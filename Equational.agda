{- (conditional) equational logic: Signature with variables, environments,
   equations, equational theories, proofs, models, Birkhoff soundness and 
   completeness. -}

module Equational where

open import UnivAlgebra
open import Morphisms
open import Data.List
open import Data.Nat hiding (_⊔_)
open import Data.Product
open import Data.Sum
open import Level renaming (zero to lzero ; suc to lsuc)
open import Relation.Binary hiding (Total)
open import Relation.Binary.PropositionalEquality as PE
open import Function as F
open import Function.Equality as FE renaming (_∘_ to _∘e_)
open import HeterogeneousVec renaming (map to mapV)

import TermAlgebra
import Relation.Binary.EqReasoning as EqR

open Signature

{- Variables symbols of a signature. In the bibliography is presented too
   as Ground Signature (signature with only constant symbols) -}
Vars : (Σ : Signature) → Set₁
Vars Σ = (s : sorts Σ) → Set

{- Signature extension with variables -}
_〔_〕 : (Σ : Signature) → (X : Vars Σ) → Signature
Σ 〔 X 〕 = record { sorts = sorts Σ
                   ; ops = λ { ([] , s) → ops Σ ([] , s) ⊎ X s
                             ; ty → ops Σ ty
                             }
                   }

open Algebra

{- Term Algebra of Σ (X) as Σ-Algebra -}
T_〔_〕 : (Σ : Signature) → (X : Vars Σ) →
          Algebra Σ
T Σ 〔 X 〕 = (λ s → ∣T∣ ⟦ s ⟧ₛ)
            ∥ (λ { {[]} {s} f → ∣T∣ ⟦ inj₁ f ⟧ₒ
                 ; {s₀ ∷ ar} {s} f → ∣T∣ ⟦ f ⟧ₒ })
  where open TermAlgebra (Σ 〔 X 〕)

open import Setoids
{- Environments -}
Env : ∀ {Σ} {ℓ₁ ℓ₂} → (X : Vars Σ) → (A : Algebra {ℓ₁} {ℓ₂} Σ) → Set ℓ₁
Env {Σ} X A = ∀ {s} → X s → ∥ A ⟦ s ⟧ₛ ∥


{- Extension of environments to terms -}
module EnvExt {ℓ₁ ℓ₂ : Level} {Σ} (X : Vars Σ)
              (A : Algebra {ℓ₁} {ℓ₂} Σ) where

  open TermAlgebra (Σ 〔 X 〕)

  mutual
    _↪ : (a : Env X A) → {s : sorts Σ} → ∥ ∣T∣ ⟦ s ⟧ₛ ∥ → ∥ A ⟦ s ⟧ₛ ∥
    (a ↪) (term {[]} (inj₁ k) ⟨⟩) = A ⟦ k ⟧ₒ ⟨$⟩ ⟨⟩
    (a ↪) (term {[]} (inj₂ x) ⟨⟩) = a x
    (a ↪) (term {s₀ ∷ ar'} f (t ▹ ts)) = A ⟦ f ⟧ₒ ⟨$⟩ (a ↪) t ▹ (map↪ a ts)
    
    map↪ : ∀ {ar} → (a : Env X A) → ∣T∣ ⟦ ar ⟧ₛ* → A ⟦ ar ⟧ₛ*
    map↪ a ⟨⟩ = ⟨⟩
    map↪ {s₀ ∷ ar'} a (t ▹ ts) = ((a ↪) t) ▹ map↪ a ts

  open Setoid
  map↪≈mapV : ∀ {ar} → (a : Env X A) → (ts : ∣T∣ ⟦ ar ⟧ₛ*) →
                         (_≈_ (_⟦_⟧ₛ A ✳ ar))
                         (map↪ a ts) (mapV (λ _ → (a ↪)) ts)
  map↪≈mapV {[]} a ⟨⟩ = ∼⟨⟩
  map↪≈mapV {s₀ ∷ ar'} a (t₀ ▹ ts') = ∼▹ (Setoid.refl (A ⟦ s₀ ⟧ₛ)) (map↪≈mapV a ts')

module Subst {Σ} {X : Vars Σ} where

  Subst : Set
  Subst = Env X (T Σ 〔 X 〕)

  open TermAlgebra (Σ 〔 X 〕)

  idSubst : Subst
  idSubst = λ x → term (inj₂ x) ⟨⟩

  open EnvExt X (T Σ 〔 X 〕)

  _↪s : Subst → {s : sorts Σ} →
                  ∥ ∣T∣ ⟦ s ⟧ₛ ∥ → ∥ ∣T∣ ⟦ s ⟧ₛ ∥
  _↪s θ {s} t = (θ ↪) t
  

open Hom
open Setoid



{- Extension of the initial homomorphism to signatures with variables -}
module InitHomoExt {ℓ₁ ℓ₂ : Level}
                {Σ : Signature} {X : Vars Σ}
                (A : Algebra {ℓ₁} {ℓ₂} Σ)
                (a : Env X A) where

  open TermAlgebra (Σ 〔 X 〕) renaming (∣T∣ to ∣T∣x)
  open EnvExt X A
  open ExtEq
  open Homo

  conga↪ : ∀ {s} {t₁ t₂ : ∥ ∣T∣x ⟦ s ⟧ₛ ∥} →
                   t₁ ≡ t₂ → _≈_ (A ⟦ s ⟧ₛ) ((a ↪) t₁) ((a ↪) t₂)
  conga↪ {s} {t₁} eq = ≡to≈ (A ⟦ s ⟧ₛ) (PE.cong (a ↪) eq)

  map↪≡map : ∀ {ar} {ts : ∣T∣x ⟦ ar ⟧ₛ*} →
                   map↪ a ts ≡ mapV (λ s → (a ↪) {s}) ts
  map↪≡map {ar = []} {⟨⟩} = PE.refl
  map↪≡map {ar = s ∷ ar} {t ▹ ts} = PE.cong (λ ts' → (a ↪) t ▹ ts')
                                                 map↪≡map

  TΣX⇝A : T Σ 〔 X 〕 ⟿ A
  TΣX⇝A s = record { _⟨$⟩_ = (a ↪)
                    ; cong = conga↪ }

  ⟦_⟧ : ∀ {s} → ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥ → ∥ A ⟦ s ⟧ₛ ∥
  ⟦_⟧ {s} = _⟨$⟩_ (TΣX⇝A s)

  {- Homomorphism condition of TΣX⇝A -}
  TΣXcond : (homCond (T Σ 〔 X 〕) A) TΣX⇝A
  TΣXcond {.[]} {s} f ⟨⟩ = Setoid.refl (A ⟦ s ⟧ₛ)
  TΣXcond {s₀ ∷ ar'} {s} f (t ▹ ts) =
                ≡to≈ (A ⟦ s ⟧ₛ) (PE.cong (λ ts' → A ⟦ f ⟧ₒ ⟨$⟩
                                            (TΣX⇝A s₀ ⟨$⟩ t) ▹ ts')
                               map↪≡map)

  TΣXHom : Homo (T Σ 〔 X 〕) A
  TΣXHom = record { ′_′ = TΣX⇝A ; cond = TΣXcond }

  HomEnv : Homo (T Σ 〔 X 〕) A → Set _
  HomEnv h = (s : sorts Σ) → (x : X s) → _≈_ (A ⟦ s ⟧ₛ) ( ′ h ′ s ⟨$⟩ term (inj₂ x) ⟨⟩ ) (a x)


 
  tot : (H H' : Homo (T Σ 〔 X 〕) A) → HomEnv H → HomEnv H' → _≈ₕ_ (T Σ 〔 X 〕) A H  H'
  tot H H' he he' s (TermAlgebra.term {[]} (inj₂ v) ⟨⟩) = begin (′ H ′ s ⟨$⟩ term (inj₂ v) ⟨⟩)
                                                          ≈⟨ he s v  ⟩
                                                          a v
                                                          ≈⟨ Setoid.sym (A ⟦ s ⟧ₛ) (he' s v) ⟩
                                                          ′ H' ′ s ⟨$⟩ term (inj₂ v) ⟨⟩
                                                          ∎
    where open EqR (A ⟦ s ⟧ₛ)
  tot H H' he he' s (TermAlgebra.term {[]} (inj₁ k) ⟨⟩) =
                  begin
                    ′ H ′ s ⟨$⟩ term (inj₁ k) ⟨⟩
                   ≈⟨ cond H k ⟨⟩ ⟩
                    A ⟦ k ⟧ₒ ⟨$⟩ ⟨⟩
                   ≈⟨ Setoid.sym (A ⟦ s ⟧ₛ) (cond H' k ⟨⟩) ⟩
                    ′ H' ′ s ⟨$⟩ term (inj₁ k) ⟨⟩
                   ∎
    where open EqR (A ⟦ s ⟧ₛ)
  tot H H' he he' s (TermAlgebra.term {x ∷ ar} f ts) =
                  begin
                    ′ H ′ s ⟨$⟩ term f ts
                  ≈⟨ cond H f ts ⟩
                    A ⟦ f ⟧ₒ ⟨$⟩ (map⟿ (T Σ 〔 X 〕) A ′ H ′ ts)
                  ≈⟨ Π.cong (A ⟦ f ⟧ₒ) (map≈ (x ∷ ar) ts) ⟩
                    A ⟦ f ⟧ₒ ⟨$⟩ (map⟿ (T Σ 〔 X 〕) A ′ H' ′ ts)
                  ≈⟨ Setoid.sym (A ⟦ s ⟧ₛ) (cond H' f ts) ⟩ 
                    ′ H' ′ s ⟨$⟩ term f ts
                  ∎
    where open EqR (A ⟦ s ⟧ₛ)
          map≈ : (ar : Arity Σ) → (ts : HVec (HU) ar) →
                 _∼v_ {R = _≈_ ∘ (_⟦_⟧ₛ A)} (mapV (_⟨$⟩_ ∘ ′ H ′) ts) (mapV (_⟨$⟩_ ∘ ′ H' ′) ts)
          map≈ [] ⟨⟩ = ∼⟨⟩
          map≈ (s ∷ ar) (t ▹ ts) = ∼▹ (tot H H' he he' s t)
                                      (map≈ ar ts)



open TermAlgebra


{- Equations -}
record Equation (Σ : Signature) (X : Vars Σ) (s : sorts Σ) : Set where
  constructor ⋀_≈_if「_」_
  field
    left  : ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥
    right : ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥
    carty : Arity Σ
    cond : HVec (λ s' → ∥ ∣T∣ (Σ 〔 X 〕) ⟦ s' ⟧ₛ ∥) carty ×
           HVec (λ s' → ∥ ∣T∣ (Σ 〔 X 〕) ⟦ s' ⟧ₛ ∥) carty


{- Unconditional equation -}
⋀_≈_ : ∀ {Σ X s} → (t t' : ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥) → Equation Σ X s
⋀ t ≈ t' = ⋀ t ≈ t' if「 [] 」 (⟨⟩ , ⟨⟩)

Theory : (Σ : Signature) → (X : Vars Σ) → (ar : Arity Σ) → Set
Theory Σ X ar = HVec (Equation Σ X) ar


{- Satisfactibility -}
_⊨_ : ∀ {ℓ₁ ℓ₂ Σ X} {s : sorts Σ} →
        (A : Algebra {ℓ₁} {ℓ₂} Σ) → Equation Σ X s → Set (ℓ₂ Level.⊔ ℓ₁)
_⊨_ {X = X} {s} A (⋀ t ≈ t' if「 _ 」 (us , us')) =
    (θ : Env X A) →
    _∼v_ {R = λ sᵢ uᵢ uᵢ' → _≈_ (A ⟦ sᵢ ⟧ₛ) ((θ ↪) uᵢ) ((θ ↪) uᵢ')} us us' →
    (_≈_ (A ⟦ s ⟧ₛ)) ((θ ↪) t) ((θ ↪) t')
    
  where open EnvExt X A


{- A is model -}
_⊨T_ : ∀ {ℓ₁ ℓ₂ Σ X ar} → (A : Algebra {ℓ₁} {ℓ₂} Σ) →
             (E : Theory Σ X ar) → Set _
A ⊨T E = ∀ {s e} → _∈_ {i = s} e E → A ⊨ e
       

⊨All : ∀ {ℓ₁ ℓ₂ Σ X} {ar : Arity Σ} {s : sorts Σ} → (E : Theory Σ X ar) →
               (e : Equation Σ X s) → Set (lsuc ℓ₂ Level.⊔ lsuc ℓ₁)
⊨All {ℓ₁} {ℓ₂} {Σ} E e = (A : Algebra {ℓ₁} {ℓ₂} Σ) → A ⊨T E → A ⊨ e


open Subst

{- Provability -}
data _⊢_ {Σ X}
            {ar : Arity Σ} (E : Theory Σ X ar) :
          {s : sorts Σ} → Equation Σ X s → Set where
  prefl : ∀ {s} {t : ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥} → E ⊢ (⋀ t ≈ t)
  psym : ∀ {s} {t t' : ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥} → E ⊢ (⋀ t ≈ t') →
                                                  E ⊢ (⋀ t' ≈ t)
  ptrans : ∀ {s} {t₀ t₁ t₂ : ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥} →
                 E ⊢ (⋀ t₀ ≈ t₁) → E ⊢ (⋀ t₁ ≈ t₂) → E ⊢ (⋀ t₀ ≈ t₂)
  psubst : ∀ {s} {ar'} {us us' : HVec (λ s' → ∥ T Σ 〔 X 〕 ⟦ s' ⟧ₛ ∥) ar'}
           {t t' : ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥} →
           (⋀ t ≈ t' if「 ar' 」 (us , us')) ∈ E →
           (σ : Subst) →
           _∼v_ {R = λ sᵢ uᵢ uᵢ' → E ⊢ (⋀ (σ ↪s) uᵢ ≈ (σ ↪s) uᵢ')} us us' →
           E ⊢ (⋀ (σ ↪s) t ≈ (σ ↪s) t')
  preemp : ∀ {ar'} {s} {ts ts' : HVec (λ s' → ∥ T Σ 〔 X 〕 ⟦ s' ⟧ₛ ∥) ar'} →
             _∼v_ {R = λ sᵢ tᵢ tᵢ' → E ⊢ (⋀ tᵢ ≈ tᵢ')} ts ts' →
             {f : ops (Σ 〔 X 〕) (ar' , s)} → E ⊢ (⋀ term f ts ≈ term f ts') 


-- Syntactic sugar
_∣_ : ∀ {Σ X} {ar : Arity Σ} {E : Theory Σ X ar} {s}
           {t t' : ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥} →
           (⋀ t ≈ t') ∈ E → (σ : Subst) →
           E ⊢ (⋀ (σ ↪s) t ≈ (σ ↪s) t')
ax ∣ σ = psubst ax σ ∼⟨⟩


module EnvSubst {Σ ℓ₁ ℓ₂ X} {A : Algebra {ℓ₁} {ℓ₂} Σ}
                (σ : Subst {Σ} {X}) (θ : Env X A) where

  open EnvExt X A
  open EnvExt X (T Σ 〔 X 〕) hiding (_↪) renaming (map↪ to map↪ₜ)

  EnvSubst : Env X A
  EnvSubst x = (θ ↪)(σ x)
  

  mutual
    ∘subst : ∀ {s} → (t₀ : ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥) →
             _≈_ (A ⟦ s ⟧ₛ) ((EnvSubst ↪) t₀) ((θ ↪) ((σ ↪s) t₀))
    ∘subst (term {[]} {s} (inj₁ x) ⟨⟩) = Setoid.refl (A ⟦ s ⟧ₛ)
    ∘subst (term {[]} {s} (inj₂ y) ⟨⟩) = Setoid.refl (A ⟦ s ⟧ₛ)
    ∘subst (term {s₀ ∷ ar} {s} f (t₀ ▹ ts)) =
                                 Π.cong (A ⟦ f ⟧ₒ) (∼▹ (∘subst t₀)
                                                  (map∘subst ts))

    map∘subst : ∀ {ar} → (ts : HVec (λ s' → ∥ T Σ 〔 X 〕 ⟦ s' ⟧ₛ ∥) ar) →
                _∼v_ {R = _≈_ ∘ _⟦_⟧ₛ A} (map↪ EnvSubst ts)
                                        (map↪ θ (map↪ₜ σ ts))
    map∘subst ⟨⟩ = ∼⟨⟩
    map∘subst (t ▹ ts) = ∼▹ (∘subst t) (map∘subst ts)



{- Birkhoff soundness and completeness -}
soundness : ∀ {ℓ₁ ℓ₂ Σ X} {ar : Arity Σ} {s : sorts Σ} {E : Theory Σ X ar}
                {e : Equation Σ X s} → E ⊢ e → ⊨All {ℓ₁} {ℓ₂} E e
soundness {X = X} {ar} {s} prefl = λ A _ _ _ → Setoid.refl (A ⟦ s ⟧ₛ)
soundness {X = X} {ar} {s} {E} (psym pe) = 
                 λ { A sall θ ∼⟨⟩ → Setoid.sym (A ⟦ s ⟧ₛ)
                                    (soundness pe A sall θ ∼⟨⟩) }
soundness {X = X} {ar} {s} {E} (ptrans pe₀ pe₁) =
                 λ { A x θ ∼⟨⟩ → Setoid.trans (A ⟦ s ⟧ₛ)
                                 (soundness pe₀ A x θ ∼⟨⟩)
                                 (soundness pe₁ A x θ ∼⟨⟩) }
soundness {Σ = Σ} {X} {ar} {s} {E}
            (psubst {us = us} {us'} {t} {t'} econd σ ⊢us≈us') A sall θ ∼⟨⟩ = A⊨econd
  where open EnvSubst {A = A} σ θ
        open EnvExt X A 
        θσ : Env X A
        θσ = EnvSubst
        iHus : ∀ {ar₀} {us₀ us₀' : HVec (λ s' → ∥ T Σ 〔 X 〕 ⟦ s' ⟧ₛ ∥) ar₀} →
               (θ' : Env X A) → 
               _∼v_ {R = λ sᵢ uᵢ uᵢ' → E ⊢ (⋀ (σ ↪s) uᵢ ≈ (σ ↪s) uᵢ')} us₀ us₀' →
               _∼v_ {R = λ sᵢ uᵢ uᵢ' → (A ⟦ sᵢ ⟧ₛ ≈ (θ' ↪) ((σ ↪s) uᵢ))
                                                 ((θ' ↪) ((σ ↪s) uᵢ'))} us₀ us₀'
        iHus θ' ∼⟨⟩ = ∼⟨⟩
        iHus θ' (∼▹ {s₀} {ar₀} {u₁} {u₂} ⊢u₁≈u₂ p) = ∼▹ (soundness ⊢u₁≈u₂ A sall θ' ∼⟨⟩)
                                                       (iHus θ' p)
        A⊨econd : ((A ⟦ s ⟧ₛ) ≈ (θ ↪) ((σ ↪s) t))
                               ((θ ↪) ((σ ↪s) t'))
        A⊨econd = begin
                   (θ ↪) ((σ ↪s) t)
                     ≈⟨ Setoid.sym (A ⟦ s ⟧ₛ) (∘subst t)⟩
                   (θσ ↪) t
                     ≈⟨ sall econd θσ (map∼v (λ {s₀} {uᵢ} {uᵢ'} x →
                                             Setoid.trans (A ⟦ s₀ ⟧ₛ) (∘subst uᵢ)
                                             (Setoid.trans (A ⟦ s₀ ⟧ₛ) x (Setoid.sym (A ⟦ s₀ ⟧ₛ) (∘subst uᵢ'))))
                                             (iHus θ ⊢us≈us')) ⟩
                   (θσ ↪) t'
                     ≈⟨ ∘subst t' ⟩
                   (θ ↪) ((σ ↪s) t')
                   ∎
          where open EqR (A ⟦ s ⟧ₛ)
soundness {s = s} {E} (preemp {[]} ∼⟨⟩ {f}) = λ { A x θ ∼⟨⟩ → Setoid.refl (A ⟦ s ⟧ₛ) }
soundness {ℓ₁} {ℓ₂} {Σ} {X} {ar} {s} {E}
            (preemp {x ∷ ar'} {.s} {ts} {ts'} ⊢ts≈ts' {f}) A sall θ ∼⟨⟩ =
                begin
                   (θ ↪) (term f ts)
                 ≈⟨ TΣXcond f ts ⟩
                   A ⟦ f ⟧ₒ ⟨$⟩ map⟿ (T Σ 〔 X 〕) A TΣX⇝A ts
                 ≈⟨ Π.cong (A ⟦ f ⟧ₒ) (map≈ (iHts ⊢ts≈ts')) ⟩
                   A ⟦ f ⟧ₒ ⟨$⟩ map⟿ (T Σ 〔 X 〕) A TΣX⇝A ts'
                 ≈⟨ Setoid.sym (A ⟦ s ⟧ₛ) (TΣXcond f ts') ⟩
                   (θ ↪) (term f ts')
                ∎
                
  where open EqR (A ⟦ s ⟧ₛ)
        open InitHomoExt A θ
        open EnvExt X A 
        iHts : ∀ {ar₀} {ts₀ ts₀' : HVec (λ s' → ∥ T Σ 〔 X 〕 ⟦ s' ⟧ₛ ∥) ar₀} →
               _∼v_ {R = λ sᵢ tᵢ tᵢ' → E ⊢ (⋀ tᵢ ≈ tᵢ')} ts₀ ts₀' →
               _∼v_ {R = λ sᵢ tᵢ tᵢ' → (A ⟦ sᵢ ⟧ₛ ≈ (θ ↪) tᵢ)
                                                 ((θ ↪) tᵢ')} ts₀ ts₀'
        iHts {[]} {⟨⟩} ∼⟨⟩ = ∼⟨⟩
        iHts {s₀ ∷ ar₀} {t₀ ▹ ts₀} {t₀' ▹ ts₀'} (∼▹ ⊢t₀≈t₀' ⊢ts₀≈ts₀') =
                                    ∼▹ (ih ⊢t₀≈t₀' A sall θ ∼⟨⟩) (iHts ⊢ts₀≈ts₀')
          where ih : ∀ {s' : sorts Σ} {tᵢ tᵢ' : ∥ T Σ 〔 X 〕 ⟦ s' ⟧ₛ ∥} →
                       E ⊢ (⋀ tᵢ ≈ tᵢ') → ⊨All E (⋀ tᵢ ≈ tᵢ')
                ih {s'} {tᵢ} {tᵢ'} peq = soundness peq
        map≈ : ∀ {ar'} {ts₀ ts₀' : HVec (λ s' → ∥ T Σ 〔 X 〕 ⟦ s' ⟧ₛ ∥) ar'} →
               (p : _∼v_ {R = λ sᵢ tᵢ tᵢ' → (A ⟦ sᵢ ⟧ₛ ≈ (θ ↪) tᵢ)
                                                 ((θ ↪) tᵢ')} ts₀ ts₀') →
               _∼v_ {R = λ s₀ → _≈_ (A ⟦ s₀ ⟧ₛ)}
               (map⟿ (T Σ 〔 X 〕) A TΣX⇝A ts₀) (map⟿ (T Σ 〔 X 〕) A TΣX⇝A ts₀')
        map≈ {[]} ∼⟨⟩ = ∼⟨⟩
        map≈ {i ∷ is} {t₀ ▹ ts₀} {t₀' ▹ ts₀'} (∼▹ p₀ p) = ∼▹ p₀ (map≈ p)


-- Completeness
⊢R : ∀ {Σ X ar} → (E : Theory Σ X ar) → (s : sorts Σ) →
       Rel (∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥) (Level.zero)
⊢R E s t t' = E ⊢ (⋀ t ≈ t') 

⊢REquiv : ∀ {Σ X ar} → (E : Theory Σ X ar) → (s : sorts Σ) →
          IsEquivalence (⊢R E s)
⊢REquiv E s = record { refl = prefl
                     ; sym = psym
                     ; trans = ptrans
                     }

⊢RSetoid : ∀ {Σ X ar} → (E : Theory Σ X ar) → (s : sorts Σ) → Setoid (Level.zero) (Level.zero)
⊢RSetoid {Σ} {X} {ar} E s = record { Carrier = ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥
                                   ; _≈_ = ⊢R E s
                                   ; isEquivalence = ⊢REquiv E s
                                   }

⊢Cong : ∀ {Σ X ar} → (E : Theory Σ X ar) → Congruence (T Σ 〔 X 〕)
⊢Cong {Σ} {X} E = record { rel = ⊢R E
               ; welldef = pwdef
               ; cequiv = ⊢REquiv E
               ; csubst = pcsubst }
  where pwdef : ∀ s → WellDefRel (T Σ 〔 X 〕 ⟦ s ⟧ₛ) (⊢R E s)
        pwdef s {(t , t')} {(.t , .t')} (PE.refl , PE.refl) ⊢t₀≈t₁ = ⊢t₀≈t₁
        pcsubst : ∀ {ar} {s} → (f : ops Σ (ar , s)) →
                    _∼v_ =[ _⟨$⟩_ (T Σ 〔 X 〕 ⟦ f ⟧ₒ) ]⇒ ⊢R E s
        pcsubst {[]} f ∼⟨⟩ = prefl
        pcsubst {s₀ ∷ ar} {s} f {ts} {ts'} ⊢ts≈ts' = preemp ⊢ts≈ts' {f}
        
⊢Quot : ∀ {Σ X ar} → (E : Theory Σ X ar) → Algebra {Level.zero} {Level.zero} Σ
⊢Quot {Σ} {X} E = T Σ 〔 X 〕 / (⊢Cong E)

⊢Quot⊨E : ∀ {Σ X ar} → (E : Theory Σ X ar) → (⊢Quot E) ⊨T E
⊢Quot⊨E {Σ} {X} {ar} E = sall
  where
    open EnvExt X (⊢Quot E)
    open EnvExt X (T Σ 〔 X 〕) hiding (_↪) renaming (map↪ to map↪ₜ)
    mutual
        thm : ∀ {s} {t} {θ : Subst} → ((T Σ 〔 X 〕 ⟦ s ⟧ₛ) ≈ (θ ↪s) t) ((θ ↪) t)
        thm {t = term (inj₁ x) ⟨⟩} {θ} = _≡_.refl
        thm {t = term (inj₂ y) ⟨⟩} {θ} = _≡_.refl
        thm {t = term f (t ▹ ts)} {θ} = PE.cong (term f) (thm' {ts = t ▹ ts} {θ} )

        thm' : ∀ {ar'} {ts : HVec (HU (Σ 〔 X 〕)) ar' } {θ : Subst} → map↪ₜ θ ts ≡ map↪ θ ts
        thm' {ts = ⟨⟩} {θ} = _≡_.refl
        thm' {ts = v ▹ ts} {θ} = cong₂ _▹_ (thm {t = v} {θ}) (thm' {ts = ts} {θ})


    sall : ∀ {s} {e : Equation Σ X s} → _∈_ {is = ar} e E → (⊢Quot E) ⊨ e
    sall {s} {e = ⋀ t ≈ t' if「 ar' 」 ( us , us') } e∈E θ us~us' =
                Congruence.welldef (⊢Cong E) s (thm {s} {t} {θ} , thm {s} {t'} {θ}) equi 
          where open EqR (⊢RSetoid E s)
                equi : E ⊢ (⋀ (θ ↪s) t ≈ (θ ↪s) t')
                equi = psubst {Σ} {X} {ar} {E} {s} {ar'} {us} {us'} {t} {t'} e∈E θ
                                (map∼v (λ {i} {ua} {ub} → Congruence.welldef (⊢Cong E) i
                                ((Setoid.sym (_⟦_⟧ₛ T Σ 〔 X 〕 i) (thm {t = ua} {θ})) ,
                                  (Setoid.sym (_⟦_⟧ₛ T Σ 〔 X 〕 i) (thm {t = ub} {θ})))) us~us')


module InitialModel (Σ : Signature)
                    {X : Vars Σ}
                    {ar : Arity Σ}
                    (E : Theory Σ X ar)
                    {ℓ₃ ℓ₄ : Level} where
  open Hom
  open Homo

  record InitModel : Set (lsuc (ℓ₄ ⊔ ℓ₃)) where
    field
      alg     : Algebra {lzero} {lzero} Σ
      ismodel : alg ⊨T E
      init    : (A : Algebra {ℓ₃} {ℓ₄} Σ) → A ⊨T E →
                Env X A → Unique (_≈ₕ_ alg A)


  ⊢Quot⟿ : (A : Algebra {ℓ₃} {ℓ₄} Σ) → A ⊨T E → (θ : Env X A) → (⊢Quot E) ⟿ A
  ⊢Quot⟿ A Amodel θ = λ s → record { _⟨$⟩_ = (θ ↪)
                                         ; cong = λ {t} {t'} ⊢t≈t' →
                                                    soundness ⊢t≈t' A Amodel θ ∼⟨⟩ }
    where open EnvExt X A

  ⊢Quot⟿cond : (A : Algebra {ℓ₃} {ℓ₄} Σ) → (Amodel : A ⊨T E) → (θ : Env X A) →
                 homCond (⊢Quot E) A (⊢Quot⟿ A Amodel θ)
  ⊢Quot⟿cond A Amodel θ {[]} {s} f ⟨⟩ = Setoid.refl (A ⟦ s ⟧ₛ)
  ⊢Quot⟿cond A Amodel θ {s₀ ∷ ar'} {s} f (t₀ ▹ ts') =
               Π.cong (A ⟦ f ⟧ₒ) (∼▹ (Setoid.refl (A ⟦ s₀ ⟧ₛ)) (map↪≈mapV θ ts'))
    where open EnvExt X A
          open EqR (A ⟦ s ⟧ₛ)

  hom⊢Quot : (A : Algebra {ℓ₃} {ℓ₄} Σ) → A ⊨T E → (θ : Env X A) → Homo (⊢Quot E) A
  hom⊢Quot A Amodel θ =
           record { ′_′   = ⊢Quot⟿ A Amodel θ
                  ; cond = ⊢Quot⟿cond A Amodel θ }
    where open EnvExt X A 

  total⊢Quot : (A : Algebra {ℓ₃} {ℓ₄} Σ) → A ⊨T E → (θ : Env X A) →
               Total (_≈ₕ_ (⊢Quot E) A)
  total⊢Quot A Amodel θ H G s (term f ts) =
          begin
            ′ H ′ s ⟨$⟩ (term f ts)
              ≈⟨ {!!} ⟩
            ′ G ′ s ⟨$⟩ (term f ts)
          ∎
    where open EqR (A ⟦ s ⟧ₛ)


  ⊢QuotInit : InitModel
  ⊢QuotInit = record { alg = ⊢Quot E
                     ; ismodel = ⊢Quot⊨E E
                     ; init = λ A Amodel θ → hom⊢Quot A Amodel θ
                                             , total⊢Quot A Amodel θ }


complete : ∀ {Σ X} {ar : Arity Σ} {s : sorts Σ} {E : Theory Σ X ar}
             {t t' : ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥ } →
             ⊨All {Level.zero} {Level.zero} E (⋀ t ≈ t') → E ⊢ (⋀ t ≈ t')
complete {Σ} {X} {ar} {s} {E} {t} {t'} sall = begin t
                  ≈⟨ ≡to≈ (⊢RSetoid E s) (PE.sym (idSubst≡ t)) ⟩
                  ((λ x → term (inj₂ x) ⟨⟩) ↪s) t
                  ≈⟨ Congruence.welldef (⊢Cong E ) s
                    ((Setoid.sym ((_⟦_⟧ₛ T Σ 〔 X 〕 s)) (thm {t = t} {λ x → term (inj₂ x) ⟨⟩})) ,
                    ((Setoid.sym ((_⟦_⟧ₛ T Σ 〔 X 〕 s)) (thm {t = t'} {λ x → term (inj₂ x) ⟨⟩}))))
                      (sall (⊢Quot E) (⊢Quot⊨E E) (λ x → term (inj₂ x) ⟨⟩) ∼⟨⟩) ⟩
                  ((λ x → term (inj₂ x) ⟨⟩) ↪s) t'
                  ≈⟨ ≡to≈ (⊢RSetoid E s) ((idSubst≡ t')) ⟩
                  t' ∎
  where
   open EqR (⊢RSetoid E s)
   open EnvExt X (⊢Quot E)
   open EnvExt X (T Σ 〔 X 〕) hiding (_↪) renaming (map↪ to map↪ₜ)
   mutual
        thm : ∀ {s} {t} {θ : Subst} → ((T Σ 〔 X 〕 ⟦ s ⟧ₛ) ≈ (θ ↪s) t) ((θ ↪) t)
        thm {t = term (inj₁ x) ⟨⟩} {θ} = _≡_.refl
        thm {t = term (inj₂ y) ⟨⟩} {θ} = _≡_.refl
        thm {t = term f (t ▹ ts)} {θ} = PE.cong (term f) (thm' {ts = t ▹ ts} {θ} )

        thm' : ∀ {ar'} {ts : HVec (HU (Σ 〔 X 〕)) ar' } {θ : Subst} → map↪ₜ θ ts ≡ map↪ θ ts
        thm' {ts = ⟨⟩} {θ} = _≡_.refl
        thm' {ts = v ▹ ts} {θ} = cong₂ _▹_ (thm {t = v} {θ}) (thm' {ts = ts} {θ})

   mutual
    idSubst≡ : ∀ {s} → (t : ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥) →
                 ((λ x → term (inj₂ x) ⟨⟩) ↪s) t ≡ t
    idSubst≡ (term {[]} (inj₁ x) ⟨⟩) = _≡_.refl
    idSubst≡ (term {[]} (inj₂ y) ⟨⟩) = _≡_.refl
    idSubst≡ (term {s₀ ∷ ar'} f (t ▹ ts)) = cong₂ (λ t₀ ts₀ → term f (t₀ ▹ ts₀))
                                                  (idSubst≡ t) (map↪id ts)

    map↪id : ∀ {ar'} → (ts : HVec (λ s' → ∥ T Σ 〔 X 〕 ⟦ s' ⟧ₛ ∥) ar') → (map↪ₜ idSubst ts) ≡ ts
    map↪id ⟨⟩ = _≡_.refl
    map↪id (t ▹ ts) = cong₂ (λ t₀ ts₀ → t₀ ▹ ts₀)
                            (idSubst≡ t) (map↪id ts)

module ProvSetoid {Σ : Signature} {X : Vars Σ}
                  {ar : Arity Σ} 
                  (Th : Theory Σ X ar) where


  ProvSetoid : (s : sorts Σ) → Setoid _ _
  ProvSetoid s = record { Carrier = ∥ T Σ 〔 X 〕 ⟦ s ⟧ₛ ∥
                        ; _≈_ = λ t t' → Th ⊢ (⋀ t ≈ t')
                        ; isEquivalence = record { refl = prefl
                                                 ; sym = psym
                                                 ; trans = ptrans } }

  

{- Theory implication -}
_⇒T_ : ∀ {Σ X ar ar'} → Theory Σ X ar → Theory Σ X ar' → Set
_⇒T_ {Σ} {X} T₁ T₂ = ∀ {s} {ax : Equation Σ X s} → ax ∈ T₂ → T₁ ⊢ ax


⊨T⇒ : ∀ {ℓ₁ ℓ₂ Σ X ar ar'} → (T₁ : Theory Σ X ar) (T₂ : Theory Σ X ar')
        (p⇒ : T₁ ⇒T T₂) → (A : Algebra {ℓ₁} {ℓ₂} Σ) → A ⊨T T₁ → A ⊨T T₂
⊨T⇒ T₁ T₂ p⇒ A satAll = λ ax → soundness (p⇒ ax) A satAll


