{- Morphisms: Homomorphism, Homo composition and equality,
              Isomorphism, Initial and Final Algebras, 
              Homomorphic image, Kernel of a congruence -}
              
module Morphisms where

open import UnivAlgebra
open import HeterogeneousVec
open import Relation.Binary hiding (Total)
open import Relation.Binary.PropositionalEquality as PE
open import Relation.Unary
open import Function as F
open import Function.Equality as FE renaming (_∘_ to _∘ₛ_) hiding (setoid)
open import Setoids
open import Data.Product hiding (map)
open import Data.List hiding (map)
open import Level renaming (suc to lsuc ; zero to lzero)

import Relation.Binary.EqReasoning as EqR

open Signature
open Setoid

{- Homomorphism from A to B -}

module Hom {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
       {Σ : Signature}
       (A : Algebra {ℓ₁} {ℓ₂} Σ) 
       (B : Algebra {ℓ₃} {ℓ₄} Σ) where 

  open Algebra

  -- Function between algebras
  _⟿_ : Set _
  _⟿_ = (s : sorts Σ) → A ⟦ s ⟧ₛ ⟶ B ⟦ s ⟧ₛ

  -- Map
  map⟿ : {ar : Arity Σ} → (m : _⟿_) →
           (ts : A ⟦ ar ⟧ₛ*) → B ⟦ ar ⟧ₛ*
  map⟿ {ar = ar} m ts = map (_⟨$⟩_ ∘ m) ts


  --Homomorphism condition
  homCond : (h : _⟿_) → Set _
  homCond h = ∀ {ar s} (f : ops Σ (ar , s)) → 
            (as : A ⟦ ar ⟧ₛ*) → let _≈ₛ_ = _≈_ (B ⟦ s ⟧ₛ) in
            (h s ⟨$⟩ (A ⟦ f ⟧ₒ ⟨$⟩ as))
                             ≈ₛ 
                             (B ⟦ f ⟧ₒ ⟨$⟩ (map⟿ h as))

  ℓ' : _
  ℓ' = lsuc (ℓ₄ ⊔ ℓ₃ ⊔ ℓ₁ ⊔ ℓ₂)


  {- Homomorphism -}
  record Homo : Set ℓ' where
    field
      ′_′    : _⟿_
      cond  : homCond ′_′

  open Homo
  open ExtEq
  open IsEquivalence renaming (refl to ref;sym to symm;trans to tran)


  {- Equality of homomorphisms -}
  _≈ₕ_  : (H G : Homo) → Set _
  H ≈ₕ G = (s : sorts Σ) → (′ H ′ s) ≈→ (′ G ′ s)
                                               
  ≈A→B : (s : sorts Σ) → IsEquivalence (_≈→_ {A = A ⟦ s ⟧ₛ} {B = B ⟦ s ⟧ₛ})
  ≈A→B s = Equiv≈→ {A = A ⟦ s ⟧ₛ} {B = B ⟦ s ⟧ₛ}
  equiv≈ₕ : IsEquivalence _≈ₕ_
  equiv≈ₕ = record { refl = λ {h} s a → ref (≈A→B s)  {′ h ′ s} a
                   ; sym = λ {h} {g} eq s a → symm (≈A→B s)
                                              {′ h ′ s} {′ g ′ s} (eq s) a
                   ; trans = λ {f} {g} {h} eq eq' s a →
                                   tran (≈A→B s) {′ f ′ s} {′ g ′ s}
                                        {′ h ′ s} (eq s) (eq' s) a
                   }

{- Homomorphism composition -}
module HomComp {ℓ₁ ℓ₂ ℓ₃ ℓ₄ l₅ l₆}
       {Σ : Signature}
       {A₀ : Algebra {ℓ₁} {ℓ₂} Σ}
       {A₁ : Algebra {ℓ₃} {ℓ₄} Σ}
       {A₂ : Algebra {l₅} {l₆} Σ} where

  open Algebra
  
  open Hom
  open Homo
  
  _∘ₕ_ : (H : Homo A₁ A₂) → (H₀ : Homo A₀ A₁) →
         Homo A₀ A₂
  _∘ₕ_  H₁ H₀ = record { ′_′   = comp
                       ; cond  = ∘ₕcond
                       }
        where comp : A₀ ⟿ A₂
              comp s = ′ H₁ ′ s ∘ₛ ′ H₀ ′ s
  
              ∘ₕcond : homCond A₀ A₂ comp 
              ∘ₕcond {ar} {s} f as = 
                begin
                  comp s ⟨$⟩ (A₀ ⟦ f ⟧ₒ ⟨$⟩ as)
                    ≈⟨ Π.cong (′ H₁ ′ s) (p₀ as) ⟩
                  ′ H₁ ′ s ⟨$⟩ (A₁ ⟦ f ⟧ₒ ⟨$⟩ (map⟿ A₀ A₁ ′ H₀ ′ as))
                    ≈⟨ p₁ (map⟿ A₀ A₁ ′ H₀ ′ as) ⟩
                  A₂ ⟦ f ⟧ₒ ⟨$⟩ (map⟿  A₁ A₂ ′ H₁ ′ (map⟿ A₀ A₁ ′ H₀ ′ as))
                    ≈⟨ propMapMorph ⟩
                  A₂ ⟦ f ⟧ₒ ⟨$⟩ map⟿ A₀ A₂ comp as
                ∎
                where open EqR (A₂ ⟦ s ⟧ₛ)
                      ty = (ar , s)
                      p₁ = cond H₁ f
                      p₀ = cond H₀ f
                      propMapMorph :  _
                      propMapMorph = 
                        begin
                          A₂ ⟦ f ⟧ₒ ⟨$⟩ (map⟿ A₁ A₂ (′ H₁ ′) $
                                              map⟿ A₀ A₁ (′ H₀ ′ ) as )
                            ≈⟨ ≡to≈ (A₂ ⟦ s ⟧ₛ) $ PE.cong (A₂ ⟦ f ⟧ₒ ⟨$⟩_ )
                                              (propMapV∘ as (_⟨$⟩_ ∘ ′ H₀ ′)
                                              (_⟨$⟩_ ∘ ′ H₁ ′)) ⟩
                          A₂ ⟦ f ⟧ₒ ⟨$⟩ (map⟿ A₀ A₂ comp as)
                        ∎




{- Homomorphism identity -}
HomId : ∀ {ℓ₁ ℓ₂} {Σ} {A : Algebra {ℓ₁} {ℓ₂} Σ} →
          Hom.Homo A A
HomId {A = A} = record { ′_′ = λ s → FE.id
                       ; cond = λ { {ar} {s} f as →
                                    Π.cong (A ⟦ f ⟧ₒ)
                                    (≡to∼v (λ i → Setoid.isEquivalence (A ⟦ i ⟧ₛ))
                                    (PE.sym (mapId as))) }
                       }
      where open Hom
            open Homo
            open Algebra


{- Isomorphism -}
open import Function.Bijection renaming (_∘_ to _∘b_) 
open import Function.Surjection hiding (_∘_)

open Bijective

open Hom
open Homo
open Algebra

{- Homomorphism inverse -}
invHomo : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {Σ : Signature} → 
          (A : Algebra {ℓ₁} {ℓ₂} Σ) → (A' : Algebra {ℓ₃} {ℓ₄} Σ) →
          (h : Homo A A') → (bj : (s : sorts Σ) → Bijective (′ h ′ s)) →
          Homo A' A
invHomo {Σ = Σ} A A' h bj = record { ′_′ = h⁻¹
                                   ; cond = cond⁻¹
                                   }
  where h⁻¹ : A' ⟿ A
        h⁻¹ s =  from (bj s)
        cond⁻¹ : homCond A' A h⁻¹ 
        cond⁻¹ {ar} {s} f as = 
               begin
                 h⁻¹ s ⟨$⟩ ((A' ⟦ f ⟧ₒ) ⟨$⟩ as)
               ≈⟨ Π.cong (h⁻¹ s) (Π.cong (A' ⟦ f ⟧ₒ)
                         (∼↑v (λ i a' → Setoid.sym (A' ⟦ i ⟧ₛ) (right-inverse-of (bj i) a'))
                         as)) ⟩
                 h⁻¹ s ⟨$⟩ ((A' ⟦ f ⟧ₒ) ⟨$⟩ map (λ i a' → ′ h ′ i ⟨$⟩ (h⁻¹ i ⟨$⟩ a')) as)
               ≈⟨ Π.cong (h⁻¹ s) (Π.cong (A' ⟦ f ⟧ₒ)
                 (Setoid.sym (_⟦_⟧ₛ A' ✳ ar) (≡to≈ (_⟦_⟧ₛ A' ✳ ar) (propMapV∘ as (λ i → _⟨$⟩_ (h⁻¹ i))
                                                                               (λ i → _⟨$⟩_ (′ h ′ i)))))) ⟩
                 h⁻¹ s ⟨$⟩ ((A' ⟦ f ⟧ₒ) ⟨$⟩ map (λ i → _⟨$⟩_ (′ h ′ i)) (map (λ i → _⟨$⟩_ (h⁻¹ i)) as))
               ≈⟨ Π.cong (h⁻¹ s) (Setoid.sym (A' ⟦ s ⟧ₛ) (cond h f (map (λ i → _⟨$⟩_ (h⁻¹ i)) as))) ⟩
                 h⁻¹ s ⟨$⟩ (′ h ′ s ⟨$⟩ (A ⟦ f ⟧ₒ ⟨$⟩ (map (λ i → _⟨$⟩_ (h⁻¹ i)) as)))
               ≈⟨ left-inverse-of (bj s) (A ⟦ f ⟧ₒ ⟨$⟩ (map (λ i → _⟨$⟩_ (h⁻¹ i)) as)) ⟩
                 A ⟦ f ⟧ₒ ⟨$⟩ map⟿ A' A h⁻¹ as
               ∎
          where open EqR (A ⟦ s ⟧ₛ)


{- Isomorphism -}
record Isomorphism {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {Σ : Signature}
                   (A : Algebra {ℓ₁} {ℓ₂} Σ) (A' : Algebra {ℓ₃} {ℓ₄} Σ) : 
                                    Set (lsuc (ℓ₄ ⊔ ℓ₃ ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    hom : Homo A A'
    bij : (s : sorts Σ) → Bijective (′ hom ′ s)

open Isomorphism

{- Isomorphic algebras -}
record _≅_ {Σ} {ℓ₁ ℓ₂ ℓ₃ ℓ₄} (A : Algebra {ℓ₁} {ℓ₂} Σ)
               (B : Algebra {ℓ₃} {ℓ₄} Σ) : Set (lsuc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)) where
  field
    iso : Isomorphism A B


{- The relation of isomorphism between algebras is an equivalence relation -}
reflIso : ∀ {ℓ₁ ℓ₂ Σ} → Reflexive (Isomorphism {ℓ₁} {ℓ₂} {ℓ₁} {ℓ₂} {Σ})
reflIso {Σ = Σ} {A} = record { hom = HomId
                              ; bij = λ s → record { injective = F.id
                                                    ; surjective = surj s } }
  where surj : (s : sorts Σ) → Surjective (′ HomId {A = A} ′ s)
        surj s = record { from = FE.id
                        ; right-inverse-of = λ x → Setoid.refl (A ⟦ s ⟧ₛ) }

symIso : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {Σ : Signature} → 
          (A : Algebra {ℓ₁} {ℓ₂} Σ) → (A' : Algebra {ℓ₃} {ℓ₄} Σ) →
          Isomorphism A A' → Isomorphism A' A
symIso {Σ = Σ} A A' i = record { hom = h⁻¹
                               ; bij = bij⁻¹ }
  where h⁻¹ : Homo A' A
        h⁻¹ = invHomo A A' (hom i) (bij i)
        surj⁻¹ : (s : sorts Σ) → Surjective (′ h⁻¹ ′ s)
        surj⁻¹ s = record { from = ′ hom i ′ s
                          ; right-inverse-of = left-inverse-of (bij i s)
                          }
        bij⁻¹ : (s : sorts Σ) → Bijective (′ h⁻¹ ′ s)
        bij⁻¹ s = record { injective = λ {x} {y} h⁻¹x≈h⁻¹y →
                             begin
                               x
                             ≈⟨ Setoid.sym (A' ⟦ s ⟧ₛ) (right-inverse-of (bij i s) x) ⟩
                               ′ hom i ′ s ⟨$⟩ (′ h⁻¹ ′ s ⟨$⟩ x)
                             ≈⟨ Π.cong (′ hom i ′ s) h⁻¹x≈h⁻¹y ⟩
                               ′ hom i ′ s ⟨$⟩ (′ h⁻¹ ′ s ⟨$⟩ y)
                             ≈⟨ right-inverse-of (bij i s) y ⟩
                               y
                             ∎
                         ; surjective = surj⁻¹ s }
              where open EqR (A' ⟦ s ⟧ₛ)

transIso : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆} {Σ : Signature} → 
             (A₀ : Algebra {ℓ₁} {ℓ₂} Σ) → (A₁ : Algebra {ℓ₃} {ℓ₄} Σ) →
             (A₂ : Algebra {ℓ₅} {ℓ₆} Σ) →
             Isomorphism A₀ A₁ → Isomorphism A₁ A₂ → Isomorphism A₀ A₂
transIso {Σ = Σ} A₀ A₁ A₂ iso₀ iso₁ =
            record { hom = hom iso₁ ∘ₕ hom iso₀
                   ; bij = λ s → bijective (bj₁ s ∘b bj₀ s) }
  where open HomComp
        open Bijection
        bj₀ : (s : sorts Σ) → Bijection (A₀ ⟦ s ⟧ₛ) (A₁ ⟦ s ⟧ₛ)
        bj₀ s = record { to = ′ hom iso₀ ′ s
                       ; bijective = bij iso₀ s }
        bj₁ : (s : sorts Σ) → Bijection (A₁ ⟦ s ⟧ₛ) (A₂ ⟦ s ⟧ₛ)
        bj₁ s = record { to = ′ hom iso₁ ′ s
                       ; bijective = bij iso₁ s }
        

isoEquiv : ∀ {ℓ₁ ℓ₂} {Σ} → IsEquivalence (Isomorphism {ℓ₁} {ℓ₂} {ℓ₁} {ℓ₂} {Σ})
isoEquiv {Σ = Σ} = record { refl = reflIso
                          ; sym = λ {A} {A'} i → symIso A A' i
                          ; trans = λ {A₀} {A₁} {A₂} i₀ i₁ →
                                           transIso A₀ A₁ A₂ i₀ i₁
                          }


{- Total relation -}
Total : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} → Rel A ℓ₂ → Set _ 
Total _≈_ = ∀ a a' → a ≈ a'


Unique : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} → Rel A ℓ₂ → Set _
Unique {A = A} _≈_ = A × Total _≈_

{- An alternative definition for Unique -}
Unique' : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} → (_≈_ : Rel A ℓ₂) →
            IsEquivalence _≈_ → Set _
Unique' {A = A} _≈_ _ = ∀ a a' → a ≈ a'


{- Initial Algebra -}
module Initial (Σ : Signature)
               {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level} where

  open Hom
  open Algebra

  record Initial  : Set (lsuc (ℓ₄ ⊔ ℓ₃ ⊔ ℓ₁ ⊔ ℓ₂)) where
    field
      alg   : Algebra {ℓ₁} {ℓ₂} Σ
      init  : (A : Algebra {ℓ₃} {ℓ₄} Σ) → Unique (_≈ₕ_ alg A)

  private
    Initial' : ∀ {ℓ₁ ℓ₂} (A : Algebra {ℓ₁} {ℓ₂} Σ) →  {ℓ₃ ℓ₄ : Level} → Set _
    Initial' A {ℓ₃} {ℓ₄} = ∀ (B : Algebra {ℓ₃} {ℓ₄} Σ) → Unique (_≈ₕ_ A B)

  record InitialCond {ℓ : Level} (P : ∀ {ℓ₅ ℓ₆} → Algebra {ℓ₅} {ℓ₆} Σ → Set ℓ) :
                                 Set (lsuc (ℓ₄ ⊔ ℓ₃ ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ)) where
    field
      alg  : Algebra {ℓ₁} {ℓ₂} Σ
      palg : P alg
      init : (A : Algebra {ℓ₃} {ℓ₄} Σ) → P A → Unique (_≈ₕ_ alg A)

{- Final Algebra -}
module Final (Σ : Signature)
             {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level} where
  open Hom
  open Algebra

  record Final  : Set (lsuc (ℓ₄ ⊔ ℓ₃ ⊔ ℓ₁ ⊔ ℓ₂)) where
    field
      alg   : Algebra {ℓ₁} {ℓ₂} Σ
      init  : (A : Algebra {ℓ₃} {ℓ₄} Σ) → Unique (_≈ₕ_ A alg)

open SetoidPredicate

{- Homomorphic image is a SubAlgebra of B -}
SubImg : ∀ {Σ} {ℓ₁ ℓ₂ ℓ₃ ℓ₄} (A : Algebra {ℓ₁} {ℓ₂} Σ) →
                              (B : Algebra {ℓ₃} {ℓ₄} Σ) →
                              (h : Homo A B) → SubAlg B
SubImg {Σ} A B h = record { pr = subipr ; opClosed = subicond }
  where subiwdef : ∀ {s} {b₀ b₁} → _≈_ (B ⟦ s ⟧ₛ) b₀ b₁ →
                     ∃ (λ a → _≈_ (B ⟦ s ⟧ₛ) (′ h ′ s ⟨$⟩ a ) b₀) →
                     ∃ (λ a → _≈_ (B ⟦ s ⟧ₛ) (′ h ′ s ⟨$⟩ a ) b₁)
        subiwdef {s} {b₀} {b₁} eq (a , eq') = a ,
                     (begin
                            ′ h ′ s ⟨$⟩ a
                              ≈⟨ eq' ⟩
                            b₀
                              ≈⟨ eq ⟩
                            b₁
                          ∎
                     )
          where open EqR (B ⟦ s ⟧ₛ)
        subipr : (s : sorts Σ) → SetoidPredicate (B ⟦ s ⟧ₛ)
        subipr s = record { predicate = λ b → ∃ (λ a → _≈_ (B ⟦ s ⟧ₛ) (′ h ′ s ⟨$⟩ a ) b)
                          ; predWellDef = subiwdef }
        subicond : ∀ {ar} {s} → (f : ops Σ (ar , s)) →
                     (_⇨v_ (predicate ∘ subipr) ⟨→⟩ predicate (subipr s))
                     (_⟨$⟩_ (B ⟦ f ⟧ₒ))
        subicond {ar} {s} f v = (A ⟦ f ⟧ₒ ⟨$⟩ va) ,
                                (begin
                                  ′ h ′ s ⟨$⟩ (A ⟦ f ⟧ₒ ⟨$⟩ va)
                                ≈⟨ cond h f va ⟩
                                  B ⟦ f ⟧ₒ ⟨$⟩ (map⟿ A B ′ h ′ va)
                                ≈⟨ Π.cong (B ⟦ f ⟧ₒ) (p≈ v) ⟩
                                  B ⟦ f ⟧ₒ ⟨$⟩ proj₁⇨v v
                                ∎
                               )
          where open EqR (B ⟦ s ⟧ₛ)
                ⇨vΣ : HVec (λ sᵢ → Σ[ b ∈ Carrier (B ⟦ sᵢ ⟧ₛ) ] (predicate ∘ subipr) sᵢ b) ar
                ⇨vΣ  = ⇨vtoΣ v
                va : HVec (Carrier ∘ _⟦_⟧ₛ A) ar
                va = map (λ { i (b , a , ha≈b) → a }) ⇨vΣ
                p≈ : ∀ {ar'} {vs : HVec (Carrier ∘ _⟦_⟧ₛ B) ar'} → (pvs : (predicate ∘ subipr) ⇨v vs) → 
                     ((_⟦_⟧ₛ B ✳ ar') ≈
                     map⟿ A B ′ h ′ (map (λ { i (b , a , ha≈b) → a }) (⇨vtoΣ pvs)))
                     vs
                p≈ ⇨v⟨⟩ = ∼⟨⟩
                p≈ (⇨v▹ pv pvs) = ∼▹ (proj₂ pv) (p≈ pvs)



homImg : ∀ {Σ} {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {B : Algebra {ℓ₃} {ℓ₄} Σ} →
               (A : Algebra {ℓ₁} {ℓ₂} Σ) → (h : Homo A B) → Algebra Σ
homImg {Σ} {B = B} A h = SubAlgebra (SubImg A B h)


Kernel : ∀ {Σ} {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Algebra {ℓ₁} {ℓ₂} Σ} {B : Algebra {ℓ₃} {ℓ₄} Σ}
                             (h : Homo A B) →
                             Congruence {ℓ₃ = ℓ₄} A
Kernel {Σ} {ℓ₄ = ℓ₄} {A = A} {B} h =
       record { rel = krel
              ; welldef = λ {s {(x , y)} {(w , z)} eq p → krelWdef s (proj₁ eq) (proj₂ eq) p }
              ; cequiv = krelEquiv
              ; csubst = krsubst
              }
  where krel : (s : sorts Σ) → Rel (Carrier (A ⟦ s ⟧ₛ)) ℓ₄
        krel s = λ a₁ a₂ → _≈_ (B ⟦ s ⟧ₛ) (′ h ′ s ⟨$⟩ a₁ ) (′ h ′ s ⟨$⟩ a₂)
        krelWdef : ∀ s {x₁ x₂ y₁ y₂ : Carrier (A ⟦ s ⟧ₛ)} →
                   _≈_ (A ⟦ s ⟧ₛ) x₁ x₂ → _≈_ (A ⟦ s ⟧ₛ) y₁ y₂ →
                   krel s x₁ y₁ → krel s x₂ y₂
        krelWdef s {x₁} {x₂} {y₁} {y₂} eqx eqy x₁ry₁ =
                        begin
                          ′ h ′ s ⟨$⟩ x₂
                          ≈⟨ Setoid.sym (B ⟦ s ⟧ₛ) (Π.cong (′ h ′ s) eqx) ⟩
                          ′ h ′ s ⟨$⟩ x₁
                          ≈⟨ x₁ry₁ ⟩
                          ′ h ′ s ⟨$⟩ y₁
                          ≈⟨ Π.cong (′ h ′ s) eqy ⟩
                          ′ h ′ s ⟨$⟩ y₂
                         ∎
          where open EqR (B ⟦ s ⟧ₛ)
        krelEquiv : (s : sorts  Σ) → IsEquivalence (krel s)
        krelEquiv s = record { refl = Setoid.refl (B ⟦ s ⟧ₛ)
                             ; sym = Setoid.sym (B ⟦ s ⟧ₛ)
                             ; trans = Setoid.trans (B ⟦ s ⟧ₛ) }
        krsubst : {ar : List (sorts Σ)} {s : sorts Σ} (f : ops Σ (ar , s)) →
                  _∼v_ {R = krel} =[ _⟨$⟩_ (A ⟦ f ⟧ₒ) ]⇒ krel s
        krsubst {s = s} f {vs₁} {vs₂} eq =
                begin
                   ′ h ′ s ⟨$⟩ ((A ⟦ f ⟧ₒ) ⟨$⟩ vs₁)
                   ≈⟨ cond h f vs₁ ⟩
                   (B ⟦ f ⟧ₒ ⟨$⟩ (map⟿ A B ′ h ′ vs₁))
                   ≈⟨ Π.cong (B ⟦ f ⟧ₒ) (p eq) ⟩
                   (B ⟦ f ⟧ₒ ⟨$⟩ (map⟿ A B ′ h ′ vs₂))
                   ≈⟨ Setoid.sym (B ⟦ s ⟧ₛ) (cond h f vs₂) ⟩
                   ′ h ′ s ⟨$⟩ ((A ⟦ f ⟧ₒ) ⟨$⟩ vs₂)
                 ∎
          where open EqR (B ⟦ s ⟧ₛ)
                p : ∀ {is} {v w} → _∼v_ {R = krel} {is = is} v w →
                      _∼v_ {R = λ s' → _≈_ (B ⟦ s' ⟧ₛ)} {is = is}
                           (map⟿ A B ′ h ′ v)
                           (map⟿ A B ′ h ′ w)
                p {[]} ∼⟨⟩ = ∼⟨⟩
                p {i ∷ is} (∼▹ x eq₁) = ∼▹ x (p eq₁)

open Congruence
open import Relation.Binary.Product.Pointwise using (_×-setoid_)

QuotHom : ∀ {Σ} {ℓ₁ ℓ₂ ℓ₃} (A : Algebra {ℓ₁} {ℓ₂} Σ) →
                        (Q : Congruence {ℓ₃} A) → Homo A (A / Q)
QuotHom {Σ} A Q = record { ′_′ = fₕ
                         ; cond = condₕ }
  where fₕ : A ⟿ (A / Q)
        fₕ s = record { _⟨$⟩_ = F.id
                      ; cong = PC-resp-~ {S = A ⟦ s ⟧ₛ} (rel Q s) (welldef Q s , (cequiv Q s)) }
          where open IsEquivalence
        condₕ : homCond A (A / Q) fₕ
        condₕ {ar} {s} f as = subst ((rel Q s) (A ⟦ f ⟧ₒ ⟨$⟩ as))
                                    (PE.cong (_⟨$⟩_ (A ⟦ f ⟧ₒ)) mapid≡)
                                    (IsEquivalence.refl (cequiv Q s))
          where open IsEquivalence
                mapid≡ : ∀ {ar'} {as' : Carrier (_⟦_⟧ₛ A ✳ ar')} →
                         as' ≡ map (λ _ a → a) as'
                mapid≡ {as' = ⟨⟩} = PE.refl
                mapid≡ {as' = v ▹ as'} = PE.cong (λ as'' → v ▹ as'') mapid≡
                
