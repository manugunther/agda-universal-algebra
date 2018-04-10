{- Proofs of the three isomorphism theorems -}

module IsoTheorems where

open import UnivAlgebra
open import Morphisms
open import HeterogeneousVec
open import Setoids
open import Function as F
open import Function.Equality as FE renaming (_∘_ to _∘ₛ_) hiding (setoid)
open import Relation.Binary.PropositionalEquality as PE
open import Data.Product hiding (map)
open import Relation.Binary
open import Relation.Unary hiding (_⊆_;_⇒_)
open import Data.List hiding (map)


open Signature
open Hom
open Homo
open import Function.Bijection renaming (_∘_ to _∘b_) 
open import Function.Surjection hiding (_∘_)

{- Isomorphism Theorems -}
module FirstIsoTheo {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {Σ : Signature}
                     (A : Algebra {ℓ₁} {ℓ₂} Σ)
                     (B : Algebra {ℓ₃} {ℓ₄} Σ)
                     (h : Homo A B) where

 firstIsoTheo : (surj : (s : sorts Σ) → Surjective (′ h ′ s)) → Isomorphism (A / Kernel h) B
 firstIsoTheo surj =
             record { hom = homo₁
                    ; bij = bij₁
                    }
  where homo₁ : Homo (A / Kernel h) B
        homo₁ = record { ′_′ = λ s → record { _⟨$⟩_ = λ a → ′ h ′ s ⟨$⟩ a
                                            ; cong = F.id }
                       ; cond = λ { f as → cond h f as }
                       }
        surj₁ : (s : sorts Σ) → Surjective (′ homo₁ ′ s)
        surj₁ s = record { from = record { _⟨$⟩_ = λ b → Surjective.from
                                                                 (surj s) ⟨$⟩ b
                                         ; cong = λ {b} {b'} b≈b' → Π.cong (′ h ′ s)
                                                                    (Π.cong (Surjective.from (surj s)) b≈b') }
                         ; right-inverse-of = λ b → Surjective.right-inverse-of (surj s) b
                         }
        bij₁ : (s : sorts Σ) → Bijective (′ homo₁ ′ s)
        bij₁ s = record { injective = F.id
                        ; surjective = surj₁ s }


open Congruence
open Setoid
open Algebra

module SecondIsoTheo {ℓ₁ ℓ₂ ℓ₃} {Σ : Signature}
                    (A : Algebra {ℓ₁} {ℓ₂} Σ)
                    (Φ Ψ : Congruence {ℓ₃} A)
                    (Ψ⊆Φ : Ψ ⊆ Φ )
                    where

  open IsEquivalence renaming (trans to tr ; sym to sy ; refl to re) 
  -- Φ/Ψ is a congruence on A/Ψ
  theo₁ : Congruence (A / Ψ)
  theo₁ = record { rel = λ {s x x₁ → rel Φ s x x₁ } 
                 ; welldef = λ { s {a , b} {c , d} (a~c , b~d) a~b →
                        tr (cequiv Φ s) (sy (cequiv Φ s) (Ψ⊆Φ s a~c))
                       (tr (cequiv Φ s) a~b ((Ψ⊆Φ s b~d))) }
                 ; cequiv = λ s → cequiv Φ s
                 ; csubst = csubst Φ
                 }

                 
  -- A/Φ is isomorphic to (A/Ψ)/(Φ/Ψ)
  secondIsoTheo : Isomorphism (A / Φ) ((A / Ψ) / theo₁)
  secondIsoTheo =
          record { hom = ho
                 ; bij = λ s → record { injective = λ x₁ → x₁
                                      ; surjective = record { from = act s
                                        ; right-inverse-of = λ x → re (cequiv Φ s) {x} }
                                      }
                 }
        where
              act : (A / Φ) ⟿ ((A / Ψ) / theo₁)
              act s = record { _⟨$⟩_ = F.id ; cong = λ x → x }
              condₕ : homCond (A / Φ) ((A / Ψ) / theo₁) act
              condₕ {ar} {s} f as = subst ((rel Φ s) (A ⟦ f ⟧ₒ ⟨$⟩ as))
                                    (PE.cong (_⟨$⟩_ (A ⟦ f ⟧ₒ)) mapid≡)
                                    (IsEquivalence.refl (cequiv Φ s))
                where open IsEquivalence
                      mapid≡ : ∀ {ar'} {as' : Carrier (_⟦_⟧ₛ A ✳ ar')} →
                               as' ≡ map (λ _ a → a) as'
                      mapid≡ {as' = ⟨⟩} = PE.refl
                      mapid≡ {as' = v ▹ as'} = PE.cong (λ as'' → v ▹ as'') mapid≡ 

              ho : Homo (A / Φ) ((A / Ψ) / theo₁)
              ho = record { ′_′ = act
                          ; cond = condₕ
                          }

open SetoidPredicate

module ThirdIsoTheo {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {Σ : Signature}
                     (A : Algebra {ℓ₁} {ℓ₂} Σ)
                     (B : SubAlg {ℓ₃} A)
                     (Φ : Congruence {ℓ₄} A) where

  -- Trace of a congruence in a subalgebra.
  trace : (s : sorts Σ) → Rel ∥ (SubAlgebra B) ⟦ s ⟧ₛ ∥ _
  trace s (b , _) (b' , _) = rel Φ s b b' 

  -- Collection of equivalence classes that intersect B
  A/Φ∩B : (s : sorts Σ) → Pred ∥ (A / Φ) ⟦ s ⟧ₛ ∥ _
  A/Φ∩B s = λ a → Σ[ b ∈ ∥ (SubAlgebra B) ⟦ s ⟧ₛ ∥ ] (rel Φ s) a (proj₁ b)

  -- Item 1 of theorem. The trace of Φ in B is a congruence on B.
  theo₁ : Congruence (SubAlgebra B)
  theo₁ = record { rel = trace
                 ; welldef = wellDef
                 ; cequiv = cEquiv
                 ; csubst = λ f x → csubst Φ f (relπ₁ x)
                 }
        where wellDef : (s : sorts Σ) → WellDefRel (SubAlgebra B ⟦ s ⟧ₛ) (trace s)
              wellDef s (eq₁ , eq₂) a₁~a₂ = welldef Φ s (eq₁ , eq₂) a₁~a₂
              cEquiv :  (s : sorts Σ) → IsEquivalence (trace s)
              cEquiv s = record { refl = λ {x} → IsEquivalence.refl (cequiv Φ s) {proj₁ x}
                                ; sym = λ x → IsEquivalence.sym (cequiv Φ s) x
                                ; trans = λ x x₁ → IsEquivalence.trans (cequiv Φ s) x x₁ }
              relπ₁ : {ar : List (sorts Σ)} {i j : HVec (λ z → Carrier (SubAlgebra B ⟦ z ⟧ₛ)) ar} →
                         (eq : _∼v_ {R = trace } i j) → map (λ _ → proj₁) i ∼v map (λ _ → proj₁) j
              relπ₁ ∼⟨⟩ = ∼⟨⟩
              relπ₁ (∼▹ x eq) = ∼▹ x (relπ₁ eq)
  open SubAlg
  isor : (s : sorts Σ) → SetoidPredicate ((A / Φ) ⟦ s ⟧ₛ)
  isor s = record { predicate = A/Φ∩B s
                  ; predWellDef = λ { {x} {y} x~y ((a , pa) , eq) → (a , pa) ,
                                          tr (sy x~y) eq }
                  }
                where open IsEquivalence (cequiv Φ s) renaming (trans to tr ; sym to sy)

  bs : ∀ ar → (vs : HVec (λ z → Carrier ((A / Φ) ⟦ z ⟧ₛ)) ar) → 
            (as : vs Relation.Unary.∈ _⇨v_ ((predicate) ∘ isor)) → 
          HVec (λ i → Σ[ a ∈ (Carrier (A ⟦ i ⟧ₛ)) ] (predicate (pr B i) a)) ar
  bs [] ⟨⟩ ⇨v⟨⟩ = ⟨⟩
  bs (i ∷ is) (v ▹ vs₁) (⇨v▹ ((b , pv) , bv) as₁) = (  (b , pv)) ▹ bs is vs₁ as₁
     where open IsEquivalence (cequiv Φ i) renaming (trans to tr ; sym to sy)
  bseq :  ∀ {ar} 
          (vs : HVec (λ z → Carrier ((A / Φ) ⟦ z ⟧ₛ)) ar) → 
          (as : vs Relation.Unary.∈ _⇨v_ ((predicate) ∘ isor)) →
          _∼v_ {R = rel Φ} vs (map (λ _ → proj₁) (bs ar vs as))
  bseq {[]} ⟨⟩ ⇨v⟨⟩ = ∼⟨⟩
  bseq {i ∷ is} (v ▹ vs) (⇨v▹ pv as₁) = ∼▹ (proj₂ pv)
                                                  (bseq {is} vs as₁)


-- A/Φ∩B is a subalgebra of A/Φ
  theo₂ : SubAlg (A / Φ)
  theo₂ = record { pr = isor ; opClosed = io } 
          where
            io : ∀ {ar s} → (f : ops Σ (ar , s)) →
              (_⇨v_ (( predicate) ∘ isor) ⟨→⟩ predicate (isor s)) (_⟨$⟩_ ((A / Φ) ⟦ f ⟧ₒ))
            io {ar} {s} f {vs} as = SubAlgebra B ⟦ f ⟧ₒ ⟨$⟩ bs ar vs as
                                  , csubst Φ f (bseq vs as)

  open IsEquivalence  renaming (refl to ref;sym to symm;trans to tran)

  -- A/Φ∩B is isomorphic to B/(the trace of Φ in B)
  theo₃ : Isomorphism (SubAlgebra theo₂) (SubAlgebra B / theo₁)
  theo₃ = record {
        hom = record {
            ′_′ = ⇉
        ; cond = cond⇉ }
      ; bij = λ s → record
            { injective = λ { {a , (b , pb) , a~b}
                              {c , (d , pd) , c~d} x₁ →
                                tran (cequiv Φ s) a~b
                                (tran (cequiv Φ s) x₁
                                  (symm (cequiv Φ s) c~d)) }
            ; surjective = record {
                           from = record { _⟨$⟩_ = λ { (a , pa) → a , ((a , pa) , (ref (cequiv Φ s) {a})) }
                                         ; cong = λ { {a , pa} {b , pb} x → x }}
                         ; right-inverse-of = λ x → ref (cequiv Φ s)
                         }
            }
      }
      where ⇉ : SubAlgebra theo₂ ⟿ (SubAlgebra B / theo₁)
            ⇉ s = record { _⟨$⟩_ = λ x → proj₁ (proj₂ x)
                                     ; cong = λ { {a , (b , pb) , a~b}
                                            {c , (d , pd) , c~d} x →
                                            tran (cequiv Φ s) (symm (cequiv Φ s) a~b)
                                            (tran (cequiv Φ s) x c~d)}
                                     }
            mutual 

              cond⇉ : homCond (SubAlgebra theo₂) (SubAlgebra B / theo₁) ⇉
              cond⇉  f as = csubst Φ f  (cond⇉* as)
              cond⇉* : ∀ {ar} as →  map (λ _ → proj₁) (bs ar (map (λ _ → proj₁) as)
                                                         (⇨₂ as))
                                    ∼v
                                 map (λ _ → proj₁) (map (( _⟨$⟩_) ∘ ⇉) as)
              cond⇉* {[]} ⟨⟩ = ∼⟨⟩
              cond⇉* {i ∷ is} (v ▹ as) = ∼▹ (ref (cequiv Φ i)) (cond⇉* as)



