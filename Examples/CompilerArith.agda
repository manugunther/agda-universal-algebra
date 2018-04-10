{- A compiler of an arithmetic language to a stack-based
   machine, proved correct via Universal Algebra -}
module Examples.CompilerArith where

open import UnivAlgebra
open import Setoids
open import Morphisms
import TermAlgebra
open import SigMorphism
open import Data.List renaming (map to lmap)
open import Data.String
open import Data.Product
open import Function
open import Function.Equality renaming (_∘_ to _∘ₛ_ ; cong to Πcong)
open import Data.Nat
open import Data.Fin hiding (_+_ ; #_)
open import Relation.Binary
open import HeterogeneousVec
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Maybe hiding (map)
open import Category.Monad
open import Category.Monad.Identity 

{- An example of use of signature morphisms:
   A correct compiler for arithmetic expressions -}

open Signature
open Algebra
open Setoid
open Hom

Var : Set
Var = String

{- High Level Language -}

-- Syntax

data Sortsₑ : Set where E : Sortsₑ

data Opsₑ : List Sortsₑ × Sortsₑ → Set where
  val   : (n : ℕ)   → Opsₑ ([] , E)
  var   : (v : Var) → Opsₑ ([] , E)
  plus  : Opsₑ ( E ∷ [ E ] , E )

Σₑ : Signature
Σₑ = record { sorts = Sortsₑ ; ops = Opsₑ }

-- Semantics: A Σₑ-algebra

State : Set
State = Var → ℕ

⟦_⟧ₑ : sorts Σₑ → Setoid _ _
⟦ E ⟧ₑ = State →-setoid ℕ


iopsₑ : ∀ {ar s} → (f : ops Σₑ (ar , s)) → ∥ ⟦_⟧ₑ ✳ ar ∥ → ∥ ⟦ s ⟧ₑ ∥
iopsₑ (val n) ⟨⟩ = λ σ → n
iopsₑ (plus) (v₀ ▹ (v₁ ▹ ⟨⟩)) = λ σ → v₀ σ + v₁ σ
iopsₑ (var x) ⟨⟩ = λ σ → σ x

icongₑ : ∀ {ar} {s} → (f : ops Σₑ (ar , s)) →
          {vs vs' : ∥ ⟦_⟧ₑ ✳ ar ∥ } →
         _∼v_ {R = _≈_ ∘ ⟦_⟧ₑ} vs vs' →
         _≈_ (⟦ s ⟧ₑ) (iopsₑ f vs) (iopsₑ f vs')
icongₑ (val n) {⟨⟩} ∼⟨⟩ = λ σ → _≡_.refl
icongₑ plus {v₀ ▹ (v₀' ▹ ⟨⟩)} {v₁ ▹ (v₁' ▹ ⟨⟩)} (∼▹ v₀≈v₁ (∼▹ v₀'≈v₁' ∼⟨⟩)) =
                          λ σ → cong₂ _+_ (v₀≈v₁ σ) (v₀'≈v₁' σ)
icongₑ (var v) {⟨⟩} ∼⟨⟩ = λ σ → _≡_.refl

iₑ : ∀ {ar s} → ops Σₑ (ar , s) → ⟦_⟧ₑ ✳ ar ⟶ ⟦ s ⟧ₑ
iₑ f = record  { _⟨$⟩_ = iopsₑ f ; cong = icongₑ f }

Semₑ : Algebra Σₑ
Semₑ =  ⟦_⟧ₑ ∥ iₑ

open TermAlgebra Σₑ renaming (∣T∣ to ∣T∣ₑ ; ∣H∣ to ∣H∣ₑ ; ∣T∣isInitial to ∣T∣ₑInit)

hsem : Homo ∣T∣ₑ Semₑ
hsem = ∣H∣ₑ Semₑ


{- Low Level Language -}

-- Syntax

data Sortsₘ : Set where C : Sortsₘ

data Opsₘ : List Sortsₘ × Sortsₘ → Set where
  pushₘ  : (n : ℕ) → Opsₘ ([] , C)
  loadₘ  : (v : Var) → Opsₘ ([] , C)
  addₘ   : Opsₘ ([] , C)
  seqₘ   : Opsₘ (C ∷ [ C ] , C)

Σₘ : Signature
Σₘ = record { sorts = Sortsₘ ; ops = Opsₘ }

-- Semantics: A Σₘ-algebra

Stack : Set
Stack = List ℕ

Conf : Set
Conf = Stack × State

⟦_⟧ₘ : sorts Σₘ → Setoid _ _
⟦ C ⟧ₘ = Conf →-setoid Maybe Stack

iopsₘ : ∀ {ar s} →  ops Σₘ (ar , s) →
                  ∥ ⟦_⟧ₘ ✳ ar ∥ → ∥ ⟦ s ⟧ₘ ∥
iopsₘ (pushₘ n) ⟨⟩ (s , σ) = just (n ∷ s)
iopsₘ (loadₘ v) ⟨⟩ (s , σ) = just (σ v ∷ s)
iopsₘ addₘ ⟨⟩ (m ∷ n ∷ s , σ) = just (m + n ∷ s)
iopsₘ addₘ ⟨⟩ (s , σ) = nothing
iopsₘ seqₘ ⟨⟨ f , g ⟩⟩ (s , σ) =  f (s , σ) >>= (λ s' → g (s' , σ))
  where open RawMonad Data.Maybe.monad

icongₘ : ∀ {ar} {s} → (f : ops Σₘ (ar , s)) →
           {vs vs' : ∥ ⟦_⟧ₘ ✳ ar ∥ } →
           _∼v_ {R = Setoid._≈_ ∘ ⟦_⟧ₘ} vs vs' →
           Setoid._≈_ (⟦ s ⟧ₘ) (iopsₘ f vs) (iopsₘ f vs')
icongₘ (pushₘ n) ∼⟨⟩ = Setoid.refl ⟦ C ⟧ₘ
icongₘ (loadₘ v) ∼⟨⟩ = Setoid.refl ⟦ C ⟧ₘ
icongₘ addₘ ∼⟨⟩ = Setoid.refl ⟦ C ⟧ₘ
icongₘ seqₘ {⟨⟨ t₁ , t₃ ⟩⟩} {⟨⟨ t₂ , t₄ ⟩⟩}
         (∼▹ t₁≈t₂ (∼▹ t₃≈t₄ ∼⟨⟩)) (s , σ) = begin
                                             ((t₁ (s , σ)) >>= (λ s' → t₃ (s' , σ)))
                                             ≡⟨ cong (_>>= λ s' → t₃ (s' , σ)) (t₁≈t₂ (s , σ)) ⟩
                                             ((t₂ (s , σ)) >>= (λ s' → t₃ (s' , σ)))
                                             ≡⟨ congSeq ⟩
                                             ((t₂ (s , σ)) >>= (λ s' → t₄ (s' , σ)))
                                             ∎
    where open RawMonad Data.Maybe.monad
          import Relation.Binary.PropositionalEquality
          open ≡-Reasoning
          congSeq : (t₂ (s , σ) >>= (λ s' → t₃ (s' , σ)))
                    ≡
                    (t₂ (s , σ) >>= (λ s' → t₄ (s' , σ)))
          congSeq with t₂ (s , σ)
          ... | nothing = _≡_.refl
          ... | just s' = t₃≈t₄ (s' , σ)        

iₘ :  ∀ {ar s} →  ops Σₘ (ar , s) →
                  ⟦_⟧ₘ ✳ ar ⟶ ⟦ s ⟧ₘ
iₘ f = record  { _⟨$⟩_ = iopsₘ f
               ; cong = icongₘ f }

Exec : Algebra Σₘ
Exec = ⟦_⟧ₘ ∥ iₘ

open TermAlgebra Σₘ renaming (∣T∣ to ∣T∣ₘ ; ∣H∣ to ∣H∣ₘ)

hexec : Homo ∣T∣ₘ Exec
hexec = ∣H∣ₘ Exec

{- Translation: A signature morphism from Σₑ to Σₘ -}

open FormalTerm Σₘ

s↝ : sorts Σₑ → sorts Σₘ
s↝ E = C

op↝ : ∀ {ar s} → ops Σₑ (ar , s) → lmap s↝ ar ⊩ s↝ s
op↝ (val n) = (pushₘ n) ∣$∣ ⟨⟩
op↝ (var v) = (loadₘ v) ∣$∣ ⟨⟩
op↝ plus = seqₘ  ∣$∣ ⟨⟨  # (suc zero)
                     ,  seqₘ ∣$∣ ⟨⟨ # zero , addₘ ∣$∣ ⟨⟩ ⟩⟩
                     ⟩⟩

e↝m : Σₑ ↝ Σₘ
e↝m = record  { ↝ₛ = s↝ ; ↝ₒ = op↝ }

open ReductAlgebra e↝m

-- Transformation of Σₘ-algebras into Σₑ-algebras
Tmₑ : Algebra Σₑ
Tmₑ = 〈 ∣T∣ₘ 〉

Execₑ : Algebra Σₑ
Execₑ = 〈 Exec 〉

hexecₑ : Homo Tmₑ Execₑ
hexecₑ = 〈 hexec 〉ₕ
  where open ReductHomo e↝m ∣T∣ₘ Exec

-- Compiler: Defined by the unique homomorphism from term
-- algebra of Σₑ to the term algebra of Σₘ viewed as a Σₑ-algebra.
hcomp : Homo ∣T∣ₑ Tmₑ
hcomp = ∣H∣ₑ Tmₑ


{- Homomorphism between semantics -}
enc : Semₑ ⟿ Execₑ
enc E = record  {
    _⟨$⟩_ = λ {f (s , σ) → just (f σ ∷ s) }
  ; cong =  λ { f≈g (s , σ) → cong  (λ n → just (n ∷ s))
                                    (f≈g σ) }
  }

condEnc : homCond Semₑ Execₑ enc
condEnc (val n)   ⟨⟩           (s , σ) = _≡_.refl
condEnc (var v)   ⟨⟩           (s , σ) = _≡_.refl
condEnc plus       ⟨⟨ f , g ⟩⟩  (s , σ) = _≡_.refl

encH : Homo Semₑ Execₑ
encH = record { ′_′ = enc ; cond = condEnc }

open HomComp
open Hom ∣T∣ₑ Execₑ renaming (_≈ₕ_ to _≈ₑₕ_)
open Initial Σₑ

open Initial.Initial

{- Proof of correctness -}

eqH : (hexecₑ ∘ₕ hcomp) ≈ₑₕ (encH ∘ₕ hsem)
eqH = proj₂ (init ∣T∣ₑInit Execₑ) h₁ h₂
  where h₁ = hexecₑ ∘ₕ hcomp
        h₂ = encH ∘ₕ hsem

{- Externalist proof from algebraic approach: We extract the
   proof from the algebraic development. -}

{- High level language is the carrier of term algebra ∣T∣ₑ -}
Expr : Set
Expr = ∥ ∣T∣ₑ ⟦ E ⟧ₛ ∥

open Hom.Homo

{- Semantics of Expr is the homomorphism between ∣T∣ₑ and Semₑ -}
⟦_⟧_ : Expr → State → ℕ
⟦ e ⟧ σ = (′ hsem ′ E ⟨$⟩ e) σ

{- Low level language is the carrier of term algebra ∣T∣ₘ -}
Code : Set
Code = ∥ ∣T∣ₘ ⟦ C ⟧ₛ ∥

{- Semantics of Code is the homomorphism between ∣T∣ₘ and Exec -}
⟪∣_∣⟫ : Code → Conf → Maybe Stack
⟪∣ c ∣⟫ = ′ hexec ′ C ⟨$⟩ c

{- Compiler is the homomorphism resulting of translation -}
compₑ : Expr → Code
compₑ e = ′ hcomp ′ E ⟨$⟩ e


{- Correctness -}
correct : ∀  e s σ →
             ⟪∣ compₑ  e ∣⟫ (s , σ) ≡ just ((⟦ e ⟧ σ ) ∷ s) 
correct e s σ = eqH E e (s , σ)

