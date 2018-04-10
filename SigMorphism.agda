{- Signature morphisms: 
   Derived signature morphism, reduct algebra, reduct homomorphism, 
   translation of terms and translation of equational theories. -}

module SigMorphism where

open import Setoids
open import UnivAlgebra
open import Morphisms

open import Relation.Binary
open import Level renaming (suc to lsuc ; zero to lzero)
open import Data.Nat renaming (_⊔_ to _⊔ₙ_)
open import Data.Product renaming (map to pmap)
open import Function
open import Function.Equality renaming (_∘_ to _∘ₛ_) hiding (id)
open import Data.Bool hiding (T)
open import Data.List renaming (map to lmap)
open import Relation.Binary.PropositionalEquality as PE
open import Induction.WellFounded
open import Data.String
open import Data.Fin hiding (#_)
open import HeterogeneousVec 
import TermAlgebra

open Signature
open Algebra

module FormalTerm (Σ : Signature) where

 data _⊩_  (ar' : Arity Σ) : (sorts Σ) → Set where
   #   : (n : Fin (length ar')) → ar' ⊩ (ar' ‼ n)
   _∣$∣_ : ∀ {ar s} → ops Σ (ar , s) → 
               HVec (ar' ⊩_) ar → ar' ⊩ s


module FormalTermInt {ℓ₁ ℓ₂} {Σ : Signature} (A : Algebra {ℓ₁} {ℓ₂} Σ) where
  open FormalTerm Σ
  mutual

    ⟦_⟧⊩ : ∀ {ar s} → ar ⊩ s → A ⟦ ar ⟧ₛ* → ∥ A ⟦ s ⟧ₛ ∥
    ⟦ # n ⟧⊩    as =  as ‼v n
    ⟦ f ∣$∣ ts ⟧⊩  as = A ⟦ f ⟧ₒ ⟨$⟩ ⟦ ts ⟧⊩* as


    ⟦_⟧⊩* : ∀ {ar ar'} → HVec (ar ⊩_) ar' → A ⟦ ar ⟧ₛ* → A ⟦ ar' ⟧ₛ*
    ⟦ ⟨⟩ ⟧⊩*      as = ⟨⟩
    ⟦ t ▹ ts ⟧⊩*  as = ⟦ t ⟧⊩ as ▹ ⟦ ts ⟧⊩* as 


  cong⟦⟧⊩ : ∀ {ar s} {vs vs' : A ⟦ ar ⟧ₛ* } →
            (t : ar ⊩ s) →
            _∼v_  {R = Setoid._≈_ ∘ _⟦_⟧ₛ A} vs vs' →
            Setoid._≈_ (A ⟦ s ⟧ₛ) (⟦ t ⟧⊩ vs) (⟦ t ⟧⊩ vs')
  cong⟦⟧⊩ {vs = vs} {vs'} (# n) eq = ~v-pointwise vs vs' eq n
  cong⟦⟧⊩ {ar} {_} {vs} {vs'} (f ∣$∣ ts) eq = Π.cong (A ⟦ f ⟧ₒ) (cong⟦⟧⊩* ts)
    where  cong⟦⟧⊩* : ∀ {ar'} →
                   (ts : HVec (ar ⊩_) ar') →
                   (⟦ ts ⟧⊩* vs ) ∼v (⟦ ts ⟧⊩* vs' )
           cong⟦⟧⊩* ⟨⟩ = ∼⟨⟩
           cong⟦⟧⊩* (t ▹ ts) = ∼▹ (cong⟦⟧⊩ t eq) (cong⟦⟧⊩* ts)


{- (derived) signature morphism -}
record _↝_ (Σₛ Σₜ : Signature) : Set where
 open FormalTerm Σₜ
 field
  ↝ₛ : sorts Σₛ → sorts Σₜ
  ↝ₒ : ∀ {ar s}  → ops Σₛ (ar , s) → lmap ↝ₛ ar ⊩ ↝ₛ s

-- module SigMorCat where

--   module Id-mor (Σ : Signature) where
--     open FormalTerm Σ
--     id-π : (ar : Arity Σ) → HVec (λ _ → Fin (length ar)) ar
--     id-π [] = ⟨⟩
--     id-π (_ ∷ ar) = zero ▹ (map (λ _ x → suc x) (id-π ar))

--     id-mor : Σ ↝ Σ
--     id-mor = record { ↝ₛ = id
--                     ; ↝ₒ = λ {ar} {s} f → f ∣$∣ {!!} -- (map (λ i x → {!# x!}) (id-π ar))
--                     }
          
--   module ∘-mor (Σ₁ Σ₂ Σ₃ : Signature) where
--     open FormalTerm
--     open _↝_
--     _∘↝_ : (m : Σ₁ ↝ Σ₂) (m' : Σ₂ ↝ Σ₃) → Σ₁ ↝ Σ₃
--     m ∘↝ m' = record { ↝ₛ = λ s → ↝ₛ m' (↝ₛ m s)
--                      ; ↝ₒ = {!!}
--                      }

{- Reduct algebras -}
module ReductAlgebra {Σₛ Σₜ} (t : Σₛ ↝ Σₜ) where

  open _↝_
  open FormalTerm Σₜ

  _⟨_⟩ₛ : ∀  {ℓ₀ ℓ₁} → (A : Algebra {ℓ₀} {ℓ₁} Σₜ) →
             (s : sorts Σₛ) → Setoid _ _
  A ⟨ s ⟩ₛ = A ⟦ ↝ₛ t s ⟧ₛ

  _⟨_⟩ₒ :  ∀  {ℓ₀ ℓ₁ ar s} → (A : Algebra {ℓ₀} {ℓ₁} Σₜ) →
              ops Σₛ (ar , s) →
              (A ⟨_⟩ₛ) ✳ ar ⟶  A ⟨ s ⟩ₛ
  A ⟨ f ⟩ₒ = record  {  _⟨$⟩_ = ⟦ ↝ₒ t f ⟧⊩ ∘ reindex (↝ₛ t) 
                    ;  cong =  cong⟦⟧⊩ (↝ₒ t f) ∘ ∼v-reindex (↝ₛ t)
                    }
    where open FormalTermInt A

  〈_〉 : ∀ {ℓ₀ ℓ₁} → Algebra {ℓ₀} {ℓ₁} Σₜ → Algebra Σₛ
  〈 A 〉 =  (A ⟨_⟩ₛ) ∥ ((A ⟨_⟩ₒ))


{- Reduct homomorphism -}
module ReductHomo {Σₛ Σₜ}  {ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level}
                 (t : Σₛ ↝ Σₜ)
                 (A : Algebra {ℓ₁} {ℓ₂} Σₜ)
                 (A' : Algebra {ℓ₃} {ℓ₄} Σₜ) where 

  open Hom
  open Homo
  open FormalTerm Σₜ
  open ReductAlgebra t
  open _↝_
  
  hcond↝ : ∀ {l₀ l₁ l₂ l₃}
             {A : Algebra {l₀} {l₁} Σₜ}
             {A' : Algebra {l₂} {l₃} Σₜ}
             (h : Homo A A') → 
             homCond 〈 A 〉 〈 A' 〉 (′ h ′ ∘ ↝ₛ t) 
  hcond↝  {A = A} {A'} h {ar} {s} f as = 
                       subst (λ vec → Setoid._≈_ (A' ⟦ ↝ₛ t s ⟧ₛ)
                                    (′ h ′ (↝ₛ t s) ⟨$⟩
                                           ⟦_⟧⊩ A (↝ₒ t f) (reindex (↝ₛ t) as))
                                    (⟦_⟧⊩ A' (↝ₒ t f) vec) 
                                    )
                       (mapReindex (↝ₛ t) 
                                   (_⟨$⟩_ ∘ ′ h ′)  as)
                       (homCond↝' (lmap (↝ₛ t) ar) (↝ₛ t s) (↝ₒ t f)
                                  (reindex (↝ₛ t) as))

    where open FormalTermInt
          homCond↝' : (ar' : Arity Σₜ) → (s' : sorts Σₜ) → (e : ar' ⊩ s') →
                      (vs : A ⟦ ar' ⟧ₛ* ) →                   
                      Setoid._≈_ (_⟦_⟧ₛ A' s')
                                 (′ h ′ s' ⟨$⟩ ⟦_⟧⊩ A e vs)
                                 (⟦ A' ⟧⊩ e (map⟿ A A' ′ h ′ vs))
          homCond↝' [] _ (# ()) ⟨⟩                           
          homCond↝' (s ∷ ar) .s (# zero) (v ▹ vs) = Setoid.refl (A' ⟦ s ⟧ₛ)
          homCond↝' (s ∷ ar) .(ar ‼ n) (# (suc n)) (v ▹ vs) =
                                                 homCond↝' ar (ar ‼ n) (# n) vs
          homCond↝' ar s (_∣$∣_ {ar₁} f₁ es) vs =
                    Setoid.trans (A' ⟦ s ⟧ₛ) (cond h f₁ (⟦_⟧⊩* A es vs))
                                             (Π.cong (A' ⟦ f₁ ⟧ₒ)
                                                     (homCond↝'vec ar₁ es))
            where homCond↝'vec : (ar₁ : Arity Σₜ) → 
                                  (es : HVec (_⊩_ ar) ar₁) → 
                                    _∼v_ {R = Setoid._≈_ ∘ (A' ⟦_⟧ₛ) }
                                      (map (λ x → _⟨$⟩_ (′ h ′ x)) (⟦_⟧⊩* A es vs))
                                      (⟦_⟧⊩* A' es (map (λ x → _⟨$⟩_ (′ h ′ x)) vs))
                  homCond↝'vec .[] ⟨⟩ = ∼⟨⟩
                  homCond↝'vec (s₁ ∷ ar₁) (e ▹ es) = ∼▹ (homCond↝' ar s₁ e vs)
                                                        (homCond↝'vec ar₁ es)
  〈_〉ₕ : Homo A A' → Homo 〈 A 〉 〈 A' 〉
  〈 h 〉ₕ = record  { ′_′ = ′ h ′ ∘ ↝ₛ t
                   ; cond = hcond↝ h
                   }

import Relation.Binary.EqReasoning as EqR


{- Signature morphisms and Equational logic -}
open import Equational
open _↝_

Img⁻¹ : ∀ {A B : Set} → (f : A → B) → (b : B) → Set
Img⁻¹ {A} f b = Σ[ a ∈ A ] (f a ≡ b)


module TermTrans {Σₛ Σₜ : Signature} (Σ↝ : Σₛ ↝ Σₜ) where

  -- Variable translation
  _↝̬ : Vars Σₛ → Vars Σₜ
  (X ↝̬) s' = Σ[ p ∈ Img⁻¹ (↝ₛ Σ↝) s' ] X (proj₁ p) 

  open Hom
  open ReductAlgebra Σ↝
  open import Data.Sum hiding (map)
  open import Data.Product renaming (map to pmap)

  term↝ : (Xₛ : Vars Σₛ) → Homo (T Σₛ 〔 Xₛ 〕) (〈 T Σₜ 〔 Xₛ ↝̬ 〕 〉)
  term↝ Xₛ = TΣXHom
    where open TermAlgebra (Σₜ 〔 Xₛ ↝̬ 〕)
          θv : Env Xₛ 〈 T Σₜ 〔 Xₛ ↝̬ 〕 〉
          θv {s} v = term (inj₂ ((s , refl) , v)) ⟨⟩
          open InitHomoExt 〈 T Σₜ 〔 Xₛ ↝̬ 〕 〉 θv

  -- Environment translation: We have a bijection
  〈_〉ₑ : ∀ {ℓ₁ ℓ₂} {Aₜ : Algebra {ℓ₁} {ℓ₂} Σₜ} {Xₛ : Vars Σₛ} →
          (θ : Env (Xₛ ↝̬) Aₜ) → Env Xₛ 〈 Aₜ 〉
  〈 θ 〉ₑ {s} = λ v → θ ((s , refl) , v)

  _↝ₑ : ∀ {ℓ₁ ℓ₂} {Aₜ : Algebra {ℓ₁} {ℓ₂} Σₜ} {Xₛ : Vars Σₛ} →
          (θ : Env Xₛ 〈 Aₜ 〉) → Env (Xₛ ↝̬) Aₜ
  _↝ₑ {Aₜ = Aₜ} {Xₛ} θ {s} ((s' , eq) , v) = subst (λ s₀ → ∥ Aₜ ⟦ s₀ ⟧ₛ ∥) eq (θ v)


{- Theory translation and preservation of models -}
module TheoryTrans {Σₛ Σₜ : Signature} (Σ↝ : Σₛ ↝ Σₜ)
                   (Xₛ : Vars Σₛ) where

  open TermTrans Σ↝
  open ReductAlgebra Σ↝
  open Hom
  open Setoid

  private Xₜ : Vars Σₜ
  Xₜ = Xₛ ↝̬

  private _∼ : (s : sorts Σₛ) → sorts Σₜ
  s ∼ = ↝ₛ Σ↝ s

  open Homo

  private _∼ₜ : ∀ {s} → ∥ T Σₛ 〔 Xₛ 〕 ⟦ s ⟧ₛ ∥ → ∥ T Σₜ 〔 Xₛ ↝̬ 〕 ⟦ s ∼ ⟧ₛ ∥
  _∼ₜ {s} t = ′ term↝ Xₛ ′ s ⟨$⟩ t

  open import Data.Product renaming (map to pmap)


  module ReductTheorem {ℓ₁ ℓ₂}
                       (Aₜ : Algebra {ℓ₁} {ℓ₂} Σₜ)
                       (θ : Env (Xₛ ↝̬) Aₜ) where

    open InitHomoExt Aₜ θ renaming (⟦_⟧ to ⟦_⟧Σₜ ; TΣXHom to ∣H∣ₜ)
    open InitHomoExt 〈 Aₜ 〉 (〈_〉ₑ {Aₜ = Aₜ} θ)  renaming
                       (⟦_⟧ to ⟦_⟧Σₛ ; tot to totΣₛ ; TΣXHom to ∣H∣ₛ ; HomEnv to HomEnvₛ)
    open Homo
    open ReductHomo Σ↝ (T Σₜ 〔 Xₛ ↝̬ 〕) Aₜ
    open HomComp
    
    reductTh : ∀ {s} → (t : ∥ T Σₛ 〔 Xₛ 〕 ⟦ s ⟧ₛ ∥) →
                 _≈_ (〈 Aₜ 〉 ⟦ s ⟧ₛ) ⟦ t ⟧Σₛ ⟦ t ∼ₜ ⟧Σₜ
    reductTh {s} t = totΣₛ ∣H∣ₛ (〈 ∣H∣ₜ 〉ₕ ∘ₕ term↝ Xₛ) he₁ he₂ s t
      where he₂ : HomEnvₛ (〈 ∣H∣ₜ 〉ₕ ∘ₕ term↝ Xₛ)
            he₂ s x = Setoid.refl (Aₜ ⟦ s ∼ ⟧ₛ)
            he₁ : HomEnvₛ ∣H∣ₛ
            he₁ s x = Setoid.refl (Aₜ ⟦ s ∼ ⟧ₛ)


  -- Equation translation
  eq↝ : ∀ {s} → Equation Σₛ Xₛ s → Equation Σₜ Xₜ (↝ₛ Σ↝ s)
  eq↝ {s} (⋀ t ≈ t' if「 carty 」 cond) =
           ⋀ t ∼ₜ ≈ t' ∼ₜ
                     if「 lmap (↝ₛ Σ↝) carty 」 pmap fcond fcond cond
    where fcond : _
          fcond = (reindex (↝ₛ Σ↝) ∘ map (_⟨$⟩_ ∘ ′ term↝ Xₛ ′))


  module SatProp {ℓ₁ ℓ₂}
                    (Aₜ : Algebra {ℓ₁} {ℓ₂} Σₜ) where


    -- This theorem is usually called "satisfaction property" and
    -- "satisfaction condition" in the handbook (Definition 6.1)
    satProp : ∀ {s} → (e : Equation Σₛ Xₛ s) → Aₜ ⊨ (eq↝ e) → 〈 Aₜ 〉 ⊨ e
    satProp {s} (⋀ t ≈ t' if「 ar 」 (us , us')) sat θ us≈us' =
                   begin
                     ⟦ t ⟧Σₛ
                   ≈⟨ reductTh t ⟩
                     ⟦ t ∼ₜ ⟧Σₜ
                   ≈⟨ sat θₜ (∼v-reindex _∼ (reductTh* us≈us')) ⟩
                     ⟦ t' ∼ₜ ⟧Σₜ
                   ≈⟨ Setoid.sym (〈 Aₜ 〉 ⟦ s ⟧ₛ) (reductTh t') ⟩ 
                     ⟦ t' ⟧Σₛ
                   ∎
      where open InitHomoExt 〈 Aₜ 〉 θ renaming
                             (⟦_⟧ to ⟦_⟧Σₛ ; tot to totΣₛ ; TΣXHom to ∣H∣ₛ ; HomEnv to HomEnvₛ)
            θₜ : Env Xₜ Aₜ
            θₜ = _↝ₑ {Aₜ = Aₜ} θ
            open InitHomoExt Aₜ θₜ renaming (⟦_⟧ to ⟦_⟧Σₜ ; TΣXHom to ∣H∣ₜ)
            open ReductTheorem Aₜ θₜ
            reductTh* : ∀ {ar₀}
                        {us₀ us₀' : HVec (λ s' → ∥ T Σₛ 〔 Xₛ 〕 ⟦ s' ⟧ₛ ∥) ar₀} →
                        _∼v_ {R = λ sᵢ uᵢ uᵢ' → _≈_ (〈 Aₜ 〉 ⟦ sᵢ ⟧ₛ) ⟦ uᵢ ⟧Σₛ ⟦ uᵢ' ⟧Σₛ} us₀ us₀' →
                        _∼v_ {R = λ sᵢ uᵢ∼ uᵢ∼' → _≈_ (Aₜ ⟦ sᵢ ∼ ⟧ₛ) ⟦ uᵢ∼ ⟧Σₜ ⟦ uᵢ∼' ⟧Σₜ}
                             (map (λ s₀ → _∼ₜ {s₀}) us₀)
                             (map (λ s₀ → _∼ₜ {s₀}) us₀')
            reductTh* {[]} ∼⟨⟩ = ∼⟨⟩
            reductTh* {s₀ ∷ ar₀} (∼▹ {t₁ = u₀} {u₀'} u₀≈u₀' eq) =
                      ∼▹ (begin
                           ⟦ u₀ ∼ₜ ⟧Σₜ
                          ≈⟨ Setoid.sym (Aₜ ⟦ s₀ ∼ ⟧ₛ) (reductTh u₀) ⟩
                           ⟦ u₀ ⟧Σₛ
                          ≈⟨ u₀≈u₀' ⟩
                           ⟦ u₀' ⟧Σₛ
                          ≈⟨ reductTh u₀' ⟩
                           ⟦ u₀' ∼ₜ ⟧Σₜ
                          ∎)
                          (reductTh* eq)
              where open EqR (Aₜ ⟦ s₀ ∼ ⟧ₛ)
            open EqR (〈 Aₜ 〉 ⟦ s ⟧ₛ)



  -- Translation of theories
  _↝T : ∀ {ar} → (Thₛ : Theory Σₛ Xₛ ar) → Theory Σₜ Xₜ (lmap (↝ₛ Σ↝) ar)
  Thₛ ↝T = reindex _∼ (map (λ s → eq↝ {s}) Thₛ)

  ∈↝T : ∀ {ar} {s} {e : Equation Σₛ Xₛ s} → (Thₛ : Theory Σₛ Xₛ ar) →
                    e ∈ Thₛ → (eq↝ e) ∈ (Thₛ ↝T)
  ∈↝T {[]} ⟨⟩ ()
  ∈↝T {s ∷ ar} (e ▹ Thₛ) here = here
  ∈↝T {s₀ ∷ ar} (e ▹ Thₛ) (there e∈Thₛ) = there (∈↝T Thₛ e∈Thₛ)

  -- Implication of theories
  _⇒T~_ : ∀ {ar ar'} → Theory Σₜ Xₜ ar → Theory Σₛ Xₛ ar' → Set
  Tₜ ⇒T~ Tₛ = ∀ {s} {ax : Equation Σₛ Xₛ s} → ax ∈ Tₛ → Tₜ ⊢ eq↝ ax

  

  module ModelPreserv {ar} (Thₛ : Theory Σₛ Xₛ ar) where

    -- Model preservation from a translated theory
    ⊨T↝ : ∀ {ℓ₁ ℓ₂} → (Aₜ : Algebra {ℓ₁} {ℓ₂} Σₜ) → Aₜ ⊨T (Thₛ ↝T) → 〈 Aₜ 〉 ⊨T Thₛ
    ⊨T↝ Aₜ sat {s} {e} = λ ax θ ceq → satProp e (sat (∈↝T Thₛ ax)) θ ceq
      where open SatProp Aₜ

    -- Model preservation from a implicated theory
    ⊨T⇒↝ : ∀ {ℓ₁ ℓ₂} {ar'} →
             (Thₜ : Theory Σₜ Xₜ ar') → (p⇒ : Thₜ ⇒T~ Thₛ) →
             (Aₜ : Algebra {ℓ₁} {ℓ₂} Σₜ) → Aₜ ⊨T Thₜ → 〈 Aₜ 〉 ⊨T Thₛ 
    ⊨T⇒↝ Thₜ p⇒ Aₜ satAll {s} {e} = λ ax θ ceq → satProp e
                                          (soundness (p⇒ ax) Aₜ satAll) θ ceq
      where open SatProp Aₜ
