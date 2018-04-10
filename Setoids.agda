{- Definitions and properties about Setoids -}
module Setoids where

open import Relation.Binary hiding (Total)
open import Level renaming (suc to lsuc ; zero to lzero)
open import Relation.Binary.PropositionalEquality as PE hiding ( Reveal_·_is_;[_])
open import Function as F
open import Function.Equality as FE renaming (_∘_ to _∘ₛ_) hiding (setoid)

open import Data.Fin hiding (_+_)

import Relation.Binary.EqReasoning as EqR

open Setoid

{- Carrier -}
∥_∥ : ∀ {l₁ l₂} → (Setoid l₁ l₂) → Set l₁
∥ S ∥ =  Carrier S

≡to≈ : ∀ {ℓ₁ ℓ₂} → (S : Setoid ℓ₁ ℓ₂) →
         {x y : Carrier S } → x ≡ y → Setoid._≈_ S x y
≡to≈ S refl = Setoid.refl S

{- Extensional equality -}
module ExtEq {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Setoid ℓ₁ ℓ₂} {B : Setoid ℓ₃ ℓ₄} where
  private
    _≈B_ : _
    _≈B_ = _≈_ B

    _≈A_ : _
    _≈A_ = _≈_ A

  _≈→_ : Rel (A ⟶ B) _
  f ≈→ g  = ∀ (a : ∥ A ∥) → (f ⟨$⟩ a) ≈B (g ⟨$⟩ a)

  ≈→-preserves-≈ : ∀ a a' f g → f ≈→ g → a ≈A a' → (f ⟨$⟩ a) ≈B (g ⟨$⟩ a')
  ≈→-preserves-≈ a a' f g f≈g a≈a' =
                      begin
                        f ⟨$⟩ a
                          ≈⟨ Π.cong f a≈a' ⟩
                        f ⟨$⟩ a'
                          ≈⟨ f≈g a' ⟩
                        g ⟨$⟩ a'
                        ∎
     where open EqR B
    
  Equiv≈→ : IsEquivalence (_≈→_)
  Equiv≈→ = record { refl = λ {f} → isRefl {f}
                    ; sym = λ {f} {g} prf → isSym {f} {g} prf
                    ; trans = λ {f} {g} {h} p q → isTrans {f} {g} {h} p q
                    }
    where isRefl : Reflexive (_≈→_)
          isRefl {f} a = Setoid.refl B {f ⟨$⟩ a}
          isSym : Symmetric (_≈→_)
          isSym {f} {g} p a = Setoid.sym B (p a)
          isTrans : Transitive (_≈→_)
          isTrans {f} {g} {h} p q a = Setoid.trans B (p a) (q a)

{- A predicate over a setoid should be even with respect to the equality -}
open import Relation.Unary
WellDef : ∀ {ℓ₁ ℓ₂ ℓ₃} → (S : Setoid ℓ₁ ℓ₂) → Pred (Carrier S) ℓ₃ → Set _
WellDef S P = ∀ {x y : Carrier S } → _≈_ S x y → P x → P y

{- A binary relation over a setoid should be even with respect to the equality -}
open import Data.Product
WellDefRel : ∀ {ℓ₁ ℓ₂ ℓ₃} → (S : Setoid ℓ₁ ℓ₂) → Rel (Carrier S) ℓ₃ → Set _
WellDefRel S R = WellDef S² (λ {(a , b) → R a b})
  where open import Relation.Binary.Product.Pointwise
        S² = S ×-setoid S

{- A pre-congruene is a well-defined equivalence relation -}
PreCong : ∀ {ℓ₁ ℓ₂ ℓ₃} → (S : Setoid ℓ₁ ℓ₂) → Rel (Carrier S) ℓ₃ → Set _
PreCong S R = WellDefRel S R × IsEquivalence R

{-  The setoid equality is finer than a pre-congruence -}
PC-resp-~ : ∀ {ℓ₁ ℓ₂ ℓ₃} {S : Setoid ℓ₁ ℓ₂} (R : Rel (Carrier S) ℓ₃) →
  PreCong S R → {x y : Carrier S} → _≈_ S x y → R x y
PC-resp-~ {S = S} R (wd , isEq) {x} {y} eq = wd (Setoid.refl S {x} , eq)
                                                (IsEquivalence.refl isEq {x})


{- A setoid predicate is a well-defined predicate over a setoid -}
record SetoidPredicate {ℓ₁ ℓ₂ ℓ₃} (S : Setoid ℓ₁ ℓ₂) :
                           Set (lsuc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃))  where
  field
    predicate   : Pred (Carrier S) ℓ₃
    predWellDef : WellDef S predicate

open SetoidPredicate
open import Relation.Unary hiding (_⊆_)
Subset : ∀ {ℓ₁ ℓ₂} → (A : Set ℓ₁) → (Pred A ℓ₂) → Set _
Subset A P = Σ[ a ∈ A ] (P a)

{- A setoid predicate defines a setoid -}
SubSetoid : ∀ {ℓ₁ ℓ₂ ℓ₃} (S : Setoid ℓ₁ ℓ₂) → (P : Pred ∥ S ∥ ℓ₃) →
                         Setoid _ _
SubSetoid S P = record { Carrier = Subset (Carrier S) P
                       ; _≈_ = λ { (e₁ , _) (e₂ , _) → (_≈_ S) e₁ e₂ }
                       ; isEquivalence = pequiv
                       }
  where pequiv : _
        pequiv = record { refl = Setoid.refl S
                        ; sym = Setoid.sym S
                        ; trans = Setoid.trans S }


private
-- A more explicit version of well-defined relations.
  WellDefRel' : ∀ {ℓ₁ ℓ₂ ℓ₃} → (S : Setoid ℓ₁ ℓ₂) → Rel (Carrier S) ℓ₃ → Set _
  WellDefRel' S R = ∀ {a b c d} → _≈_ S a c → _≈_ S b d → R a b → R c d

  W↔W' : ∀ {ℓ₁ ℓ₂ ℓ₃} → (S : Setoid ℓ₁ ℓ₂) → (R : Rel (Carrier S) ℓ₃) → WellDefRel' S R → WellDefRel S R
  W↔W' S R wd {(a , b)} {(c , d)} (eq , eq') pa = wd eq eq' pa

  W'↔W : ∀ {ℓ₁ ℓ₂ ℓ₃} → (S : Setoid ℓ₁ ℓ₂) → (R : Rel (Carrier S) ℓ₃) → WellDefRel S R → WellDefRel' S R
  W'↔W S R wd {a} {b} {c} {d} eq  eq' pa = wd (eq , eq') pa


{- Indexed setoids are different from the standard library because
   the relation are homogeneous over the index -}
IRel : ∀ {i a} {I : Set i} →
         (I → Set a) → (ℓ : Level) → Set _
IRel A ℓ = ∀ {i} → A i → A i → Set ℓ

record ISetoid {i} (I : Set i) c ℓ : Set (lsuc (i ⊔ c ⊔ ℓ)) where
  infix 4 _I≈_
  field
    ICarrier       : I → Set c
    _I≈_           : IRel ICarrier c
    isIEquivalence : (i : I) → IsEquivalence (_I≈_ {i = i})
  



