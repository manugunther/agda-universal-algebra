open import UnivAlgebra

module TermAlgebra (Σ : Signature) where

open import Morphisms
open import HeterogeneousVec
open import Relation.Binary hiding (Total)
open import Relation.Binary.PropositionalEquality as PE
open import Function as F
open import Function.Equality as FE renaming (_∘_ to _∘ₛ_) hiding (setoid)
open import Setoids
open import Data.List hiding (map)
open import Data.Product hiding (map ; Σ)

import Relation.Binary.EqReasoning as EqR

open Hom
open Algebra
open Signature

data HU : (s : sorts Σ) → Set where
  term : ∀  {ar s} →  (f : ops Σ (ar ↦ s)) → (HVec HU ar) → HU s

∣T∣ : Algebra Σ
∣T∣ = record  { _⟦_⟧ₛ = setoid ∘ HU
             ; _⟦_⟧ₒ  = ∣_|ₒ
             }
  where ≡vec : ∀ {ar}  → (ts₁ ts₂ : HVec HU ar) →
                          _∼v_ {R = λ _ → _≡_} ts₁ ts₂ →
                          ts₁ ≡ ts₂
        ≡vec ⟨⟩ ⟨⟩ ≈⟨⟩ = PE.refl
        ≡vec (t ▹ ts₁) (.t ▹ ts₂) (∼▹ PE.refl ts₁≈ts₂) =
                                  PE.cong (λ ts → t ▹ ts)
                                          (≡vec ts₁ ts₂ ts₁≈ts₂)
        fcong : ∀ {ar s} {f : ops Σ (ar ↦ s)} → (ts₁ ts₂ : HVec HU ar) →
                         _∼v_ {R = λ s₀ → _≡_} ts₁ ts₂ → term f ts₁ ≡ term f ts₂
        fcong {f = f} ts₁ ts₂ ts₁≈ts₂ = PE.cong (term f) (≡vec ts₁ ts₂ ts₁≈ts₂)
        ∣_|ₒ  : ∀ {ar s} → ops Σ (ar ↦ s) → (setoid ∘ HU) ✳ ar ⟶ (setoid ∘ HU) s
        ∣ f |ₒ = record { _⟨$⟩_ = term f
                       ; cong = λ {ts₁} {ts₂} ts₁≈ts₂ → fcong ts₁ ts₂ ts₁≈ts₂
                       }


open Hom
open Homo
open Setoid

mutual
  ∣h∣→A : ∀ {ℓ₁ ℓ₂ s} → (A : Algebra {ℓ₁} {ℓ₂} Σ) → HU s → ∥ A ⟦ s ⟧ₛ ∥
  ∣h∣→A A (term f ⟨⟩)         =   A ⟦ f ⟧ₒ ⟨$⟩ ⟨⟩
  ∣h∣→A A (term f (t ▹ ts))  =   A ⟦ f ⟧ₒ ⟨$⟩ (∣h∣→A A t ▹ map|h|→A A ts)
  
  map|h|→A : ∀ {ℓ₁ ℓ₂ ar} → (A : Algebra {ℓ₁} {ℓ₂} Σ)
                            → ∣T∣ ⟦ ar ⟧ₛ* → A ⟦ ar ⟧ₛ*
  map|h|→A A ⟨⟩ = ⟨⟩
  map|h|→A A (t ▹ ts) = ∣h∣→A A t ▹ map|h|→A A ts


map|T|→A≡map : ∀ {ℓ₁ ℓ₂ ar} {ts : ∣T∣ ⟦ ar ⟧ₛ*} {A : Algebra {ℓ₁} {ℓ₂} Σ} →
                 map|h|→A A ts ≡ map (λ s → ∣h∣→A A) ts
map|T|→A≡map {ar = []} {⟨⟩} {A} = PE.refl
map|T|→A≡map {ar = s ∷ ar} {t ▹ ts} {A} =
             PE.cong (λ ts' → ∣h∣→A A t ▹ ts') map|T|→A≡map

∣H∣ : ∀ {ℓ₁ ℓ₂} → (A : Algebra {ℓ₁} {ℓ₂} Σ) → Homo ∣T∣ A
∣H∣ A = record { ′_′  = fun|T|ₕ
              ; cond = |T|ₕcond
              }
  where congfun : ∀ {s} {t₁ t₂ : HU s} → t₁ ≡ t₂ → _≈_ (A ⟦ s ⟧ₛ) (∣h∣→A A t₁) (∣h∣→A A t₂)
        congfun {s} t₁≡t₂ = ≡to≈ (A ⟦ s ⟧ₛ) (PE.cong (∣h∣→A A) t₁≡t₂)
        fun|T|ₕ : ∣T∣ ⟿ A
        fun|T|ₕ s = record { _⟨$⟩_ = ∣h∣→A {s = s} A
                           ; cong  = congfun {s}
                           }
        |T|ₕcond : (homCond ∣T∣ A) fun|T|ₕ
        |T|ₕcond {_} {s} f ⟨⟩ = ≡to≈ (A ⟦ s ⟧ₛ) PE.refl
        |T|ₕcond {_} {s} f (t ▹ ts) =
                 ≡to≈ (A ⟦ s ⟧ₛ) (PE.cong (λ ts' → A ⟦ f ⟧ₒ ⟨$⟩
                                 (∣h∣→A A t ▹ ts')) map|T|→A≡map)


total : ∀ {ℓ₁ ℓ₂} → (A : Algebra {ℓ₁} {ℓ₂} Σ) → Total (_≈ₕ_ ∣T∣ A)
total A H G s (term {ar = ar} f ts) = 
          begin
            ′ H ′ s ⟨$⟩ term f ts
              ≈⟨ cond H f ts ⟩
            A ⟦ f ⟧ₒ ⟨$⟩ (map⟿ ∣T∣ A ′ H ′ ts)
              ≈⟨ Π.cong (A ⟦ f ⟧ₒ) (map≈ ar ts) ⟩
            A ⟦ f ⟧ₒ ⟨$⟩ (map⟿ ∣T∣ A ′ G ′ ts)
              ≈⟨ Setoid.sym (A ⟦ s ⟧ₛ) (cond G f ts) ⟩ 
            ′ G ′ s ⟨$⟩ term f ts
          ∎
  where open EqR (A ⟦ s ⟧ₛ)
        map≈ : (ar : Arity Σ) → (ts : HVec (HU) ar) →
               (map (_⟨$⟩_ ∘ ′ H ′) ts) ∼v (map (_⟨$⟩_ ∘ ′ G ′) ts)
        map≈ [] ⟨⟩ = ∼⟨⟩
        map≈ (s ∷ ar) (t ▹ ts) = ∼▹ (total A H G s t)
                                    (map≈ ar ts)


open Initial Σ

∣T∣isInitial : ∀ {ℓ₁ ℓ₂} → Initial {ℓ₃ = ℓ₁} {ℓ₄ = ℓ₂}
∣T∣isInitial = record  { alg = ∣T∣
                      ; init = λ A → ∣H∣ A , total A }
