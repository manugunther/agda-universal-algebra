{- Definition of two boolean theories and a translation
   from one of them to the another. The theories are
   T_Bool and T_DS from the article "Theorem Proving Modulo
   Based on Boolean Equational Procedures", Camilo Rocha
   and José Meseguer. -}
module Examples.EqBool where

open import UnivAlgebra
open import Morphisms
open import Equational
open import SigMorphism
import TermAlgebra
open import Data.Unit hiding (setoid)
open import Data.List
open import Data.Product
open import Data.Nat
open import Data.Sum
open import HeterogeneousVec
open import Relation.Binary.PropositionalEquality using (refl)


{- Example of equational logic: Theories for boolean algebras -}

{- Theory 1: The traditional Boolean theory -}
data Σops₁ : List ⊤ × ⊤ → Set where
  t₁   : Σops₁ ([] ↦ tt)
  f₁   : Σops₁ ([] ↦ tt)
  neg₁ : Σops₁ ([ tt ] ↦ tt)
  and₁ : Σops₁ ((tt ∷ [ tt ]) ↦ tt)
  or₁  : Σops₁ ((tt ∷ [ tt ]) ↦ tt)

-- The signature is monosorted, so we have an unique sort tt : ⊤ (the unit type)

Σbool₁ : Signature
Σbool₁ = record { sorts = ⊤ ; ops = Σops₁ }

open Signature

{- Definition of the equational theory -}
module Theory₁ where

  {- We use natural number as variables -}
  Vars₁ : Vars Σbool₁
  Vars₁ s = ℕ

  Eq₁ : Set
  Eq₁ = Equation Σbool₁ Vars₁ tt

  open TermAlgebra

  -- Formulas are terms of the Term Algebra
  Form₁ : Set
  Form₁ = HU (Σbool₁ 〔 Vars₁ 〕) tt

  module Smartcons where
    {- We define smart constructors to define axioms more easily -}
    _∧_ : Form₁ → Form₁ → Form₁
    φ ∧ ψ = term and₁ ⟨⟨ φ , ψ ⟩⟩

    _∨_ : Form₁ → Form₁ → Form₁
    φ ∨ ψ = term or₁ ⟨⟨ φ , ψ ⟩⟩
  
    ¬ : Form₁ → Form₁
    ¬ φ = term neg₁ ⟪ φ ⟫
  
    p : Form₁
    p = term (inj₂ 0) ⟨⟩
    
    q : Form₁
    q = term (inj₂ 1) ⟨⟩

    r : Form₁
    r = term (inj₂ 2) ⟨⟩

    true : Form₁
    true = term (inj₁ t₁) ⟨⟩

    false : Form₁
    false = term (inj₁ f₁) ⟨⟩

  open Smartcons

  -- Equations for each axiom of the theory
  assocAnd : Eq₁
  assocAnd = ⋀ p ∧ (q ∧ r) ≈ ((p ∧ q) ∧ r)

  commAnd : Eq₁
  commAnd = ⋀ p ∧ q ≈ (q ∧ p)

  assocOr₁ : Eq₁
  assocOr₁ = ⋀ p ∨ (q ∨ r) ≈ ((p ∨ q) ∨ r)

  commOr₁ : Eq₁
  commOr₁ = ⋀ p ∨ q ≈ (q ∨ p)

  idemAnd : Eq₁
  idemAnd = ⋀ p ∧ p ≈ p

  idemOr₁ : Eq₁
  idemOr₁ = ⋀ p ∨ p ≈ p

  distAndOr : Eq₁
  distAndOr = ⋀ p ∧ (q ∨ r) ≈ ((p ∧ q) ∨ (p ∧ r))

  distOrAnd : Eq₁
  distOrAnd = ⋀ p ∨ (q ∧ r) ≈ ((p ∨ q) ∧ (p ∨ r))

  abs₁ : Eq₁
  abs₁ = ⋀ p ∧ (p ∨ q) ≈ p

  abs₂ : Eq₁
  abs₂ = ⋀ p ∨ (p ∧ q) ≈ p

  defF : Eq₁
  defF = ⋀ p ∧ (¬ p) ≈ false

  3excl : Eq₁
  3excl = ⋀ p ∨ (¬ p) ≈ true


  {- The theory is a vector with the 12 axioms -}
  Tbool₁ : Theory Σbool₁ Vars₁ (replicate 12 tt)
  Tbool₁ = assocAnd ▹ commAnd ▹ assocOr₁ ▹
           commOr₁ ▹ idemAnd ▹ idemOr₁ ▹
           distAndOr ▹ distOrAnd ▹ abs₁ ▹
           abs₂ ▹ defF ▹ 3excl ▹ ⟨⟩

  {- An axiom of Tbool₁ is an element of the vector, so we need 
     to say where is each one in it. In order to have a more compact
     syntax, we define patterns. -}
  pattern axAssoc∧ = here
  pattern axComm∧ = there here
  pattern axAssoc∨₁ = there (there here)
  pattern axComm∨₁ = there (there (there here))
  pattern axIdem∧ = there (there (there (there here)))
  pattern axIdem∨₁ = there (there (there (there (there here))))
  pattern axDist∧∨ = there (there (there (there (there (there here)))))
  pattern axDist∨∧ = there (there (there (there (there (there (there here))))))
  pattern axAbs₁ = there (there (there (there (there (there (there (there here)))))))
  pattern axAbs₂ = there (there (there (there (there (there (there
                                                          (there (there here))))))))
  pattern axDefF = there (there (there (there (there (there (there
                                                          (there (there (there here)))))))))
  pattern ax3excl = there (there (there (there (there (there (there
                                                          (there (there (there (there here))))))))))
  pattern noax₁ = there (there (there (there (there (there (there
                                                          (there (there (there (there (there ())))))))))))


{- Theory 2: Axiomatization of the propositional logic of Dijkstra-Scholten.
   We define the signature and a signature morphism from Σbool₁ to Σbool₂. 
   Then we define the axioms of Σbool₂ using variables coming from Σbool₁ (so
   we can transform a model of Σbool₂ in a model of Σbool₁ directly). -}
data Σops₂ : List ⊤ × ⊤ → Set where
  t₂     : Σops₂ ([] ↦ tt)
  f₂     : Σops₂ ([] ↦ tt)
  or₂    : Σops₂ ((tt ∷ [ tt ]) ↦ tt)
  equiv₂ : Σops₂ ((tt ∷ [ tt ]) ↦ tt)


Σbool₂ : Signature
Σbool₂ = record { sorts = ⊤ ; ops = Σops₂ }


{- We define signature morphism from Σbool₁ to Σbool₂ -}
module Translation where
  open import Function
  open import Data.Fin hiding (#_)
  open import Data.List renaming (map to lmap)

  open TermAlgebra
  open Algebra
  open FormalTerm Σbool₂

  {- For each operation of Σbool₁, we define a
     formal term in Σbool₂ -}
  ops↝ : ∀ {ar s} → (f : Σops₁ (ar ↦ s)) →
           lmap id ar ⊩ s
  ops↝ t₁ = t₂ ∣$∣ ⟨⟩
  ops↝ f₁ = f₂ ∣$∣ ⟨⟩
  ops↝ or₁ = or₂ ∣$∣ ⟨⟨ p , q ⟩⟩ 
    where p = # zero
          q = # (suc zero)
  -- ¬ p is translated to p ≡ false
  ops↝ neg₁ = equiv₂ ∣$∣ ⟨⟨ p , false ⟩⟩
    where p = # zero
          false = f₂ ∣$∣ ⟨⟩
  -- p ∧ q is translated to  (p ≡ q) ≡ p ∨ q
  ops↝ and₁ = equiv₂ ∣$∣ ⟨⟨ equiv₂ ∣$∣ ⟨⟨ p , q ⟩⟩
                         , or₂ ∣$∣ ⟨⟨ p , q ⟩⟩ ⟩⟩
    where p = # zero
          q = # (suc zero)

  Σtrans : Σbool₁ ↝ Σbool₂
  Σtrans = record { ↝ₛ = id
                  ; ↝ₒ = ops↝
                  }

open Translation

{- We define now a Σbool₂-theory using variables from Σbool₁ -}
module Theory₂ where
  open TermAlgebra
  open Theory₁ using (Vars₁)
  open TermTrans Σtrans

  Vars₂ : Vars Σbool₂
  Vars₂ = Vars₁ ↝̬

  Eq₂ : Set
  Eq₂ = Equation Σbool₂ Vars₂ tt

  Form₂ : Set
  Form₂ = HU (Σbool₂ 〔 Vars₂ 〕) tt

  var : Vars₁ tt → Vars₂ tt
  var n = (tt , refl) , n

  varp : Vars₂ tt
  varp = var 0

  varq : Vars₂ tt
  varq = var 1

  varr : Vars₂ tt
  varr = var 2

  module Smartcons where
  
    _∨_ : Form₂ → Form₂ → Form₂
    φ ∨ ψ = term or₂ ⟨⟨ φ , ψ ⟩⟩

    _≡_ : Form₂ → Form₂ → Form₂
    φ ≡ ψ = term equiv₂ ⟨⟨ φ , ψ ⟩⟩

    p : Form₂
    p = term (inj₂ varp) ⟨⟩

    q : Form₂
    q = term (inj₂ varq) ⟨⟩

    r : Form₂
    r = term (inj₂ varr) ⟨⟩

    true₂ : Form₂
    true₂ = term (inj₁ t₂) ⟨⟩

    false₂ : Form₂
    false₂ = term (inj₁ f₂) ⟨⟩


  open Smartcons
  -- Equations for each axiom
  assocEquiv : Eq₂
  assocEquiv = ⋀ p ≡ (q ≡ r) ≈ ((p ≡ q) ≡ r)

  commEquiv : Eq₂
  commEquiv = ⋀ p ≡ q ≈ (q ≡ p)

  assocOr : Eq₂
  assocOr = ⋀ p ∨ (q ∨ r) ≈ ((p ∨ q) ∨ r)

  commOr : Eq₂
  commOr = ⋀ p ∨ q ≈ (q ∨ p)

  neuEquiv : Eq₂
  neuEquiv = ⋀ p ≡ true₂ ≈ p

  reflEquiv : Eq₂
  reflEquiv = ⋀ p ≡ p ≈ true₂

  absOr : Eq₂
  absOr = ⋀ p ∨ true₂ ≈ true₂

  neuOr : Eq₂
  neuOr = ⋀ p ∨ false₂ ≈ p

  idemOr : Eq₂
  idemOr = ⋀ p ∨ p ≈ p

  distOrEquiv : Eq₂
  distOrEquiv = ⋀ p ∨ (q ≡ r) ≈ ((p ∨ q) ≡ (p ∨ r)) 

  Tbool₂ : Theory Σbool₂ Vars₂ (replicate 10 tt)
  Tbool₂ = assocEquiv ▹ commEquiv ▹ assocOr ▹
           commOr ▹ neuEquiv ▹ reflEquiv ▹
           absOr ▹ neuOr ▹ idemOr ▹
           distOrEquiv ▹ ⟨⟩


  {- Patterns for each axiom in Tbool₂ -}

  pattern axAssoc≡ = here
  pattern axComm≡ = there here
  pattern axAssoc∨ = there (there here)
  pattern axComm∨ = there (there (there here))
  pattern axNeu≡ = there (there (there (there here)))
  pattern axRefl≡ = there (there (there (there (there here))))
  pattern axAbs∨ = there (there (there (there (there (there here)))))
  pattern axNeu∨ = there (there (there (there (there (there (there here))))))
  pattern axIdem∨ = there (there (there (there (there (there (there (there here)))))))
  pattern axDist∨≡ = there (there (there (there (there (there (there
                                                          (there (there here))))))))
  pattern noax = there (there (there (there (there (there (there
                                                          (there (there (there ())))))))))



  {- Tbool₂ implies Tbool₁ -}
  module Tbool₂⇒Tbool₁ where
    open Theory₁
    open TheoryTrans Σtrans Vars₁
    open ProvSetoid
    open import Relation.Binary.EqReasoning (ProvSetoid Tbool₂ tt)

  
    {- We have to prove each axiom of
      Tbool₁ in theory Tbool₂ -}

    open Subst

    T₂⊢idem∨ : Tbool₂ ⊢ eq↝ idemOr₁
    T₂⊢idem∨ =
      begin
        p ∨ p
      ≈⟨ axIdem∨ ∣ idSubst ⟩
        p
      ∎

    T₂⊢idem∧ : Tbool₂ ⊢ eq↝ idemAnd
    T₂⊢idem∧ =
      begin
        ((p ≡ p) ≡ (p ∨ p))
      ≈⟨ preemp ∼⟨⟨ axRefl≡ ∣ idSubst , prefl ⟩⟩∼ ⟩
        (true₂ ≡ (p ∨ p))
      ≈⟨ preemp ∼⟨⟨ prefl , axIdem∨ ∣ idSubst ⟩⟩∼ ⟩
        (true₂ ≡ p)
      ≈⟨ axComm≡ ∣ σ ⟩
        (p ≡ true₂)
      ≈⟨ axNeu≡ ∣ idSubst ⟩
        p
      ∎
      where σ : Subst
            σ ( _ , 0 ) = true₂
            σ ( _ , 1 ) = p
            σ n = term (inj₂ n) ⟨⟩



    T₂⊢assoc∨₁ : Tbool₂ ⊢ eq↝ assocOr₁
    T₂⊢assoc∨₁ =
     begin
        p ∨ (q ∨ r)
      ≈⟨ axAssoc∨ ∣ idSubst ⟩
        (p ∨ q) ∨ r
      ∎


    T₂⊢comm∨₁ : Tbool₂ ⊢ eq↝ commOr₁
    T₂⊢comm∨₁ =
     begin
        p ∨ q
      ≈⟨ axComm∨ ∣ idSubst ⟩
        q ∨ p
      ∎


    --p ∧ (p ∨ q) ≈ p
    T₂⊢abs₁ : Tbool₂ ⊢ eq↝ abs₁
    T₂⊢abs₁ =
      begin
        (p ≡ (p ∨ q)) ≡ (p ∨ (p ∨ q))
      ≈⟨ preemp ∼⟨⟨ prefl , axAssoc∨ ∣ σ₁ ⟩⟩∼ ⟩
        ((p ≡ (p ∨ q)) ≡ ((p ∨ p) ∨ q))
      ≈⟨ preemp ∼⟨⟨ prefl , preemp ∼⟨⟨ axIdem∨ ∣ idSubst , prefl ⟩⟩∼ ⟩⟩∼ ⟩
        (p ≡ (p ∨ q)) ≡ (p ∨ q)
      ≈⟨ psym (axAssoc≡ ∣ σ₂) ⟩
        p ≡ ((p ∨ q) ≡ (p ∨ q))
      ≈⟨ preemp ∼⟨⟨ prefl , axRefl≡ ∣ σ₃ ⟩⟩∼ ⟩
        (p ≡ true₂)
      ≈⟨ axNeu≡ ∣ idSubst ⟩
        p
      ∎
      where σ₁ : Subst
            σ₁ (_ , 1) = p
            σ₁ (_ , 2) = q
            σ₁ x = term (inj₂ x) ⟨⟩
            σ₂ : Subst
            σ₂ (_ , 1) = p ∨ q
            σ₂ (_ , 2) = p ∨ q
            σ₂ x = term (inj₂ x) ⟨⟩
            σ₃ : Subst
            σ₃ (_ , 0) = p ∨ q
            σ₃ x = term (inj₂ x) ⟨⟩

    T₂⊢abs₂ : Tbool₂ ⊢ eq↝ abs₂
    T₂⊢abs₂ =
      begin
        p ∨ ((p ≡ q) ≡ (p ∨ q))
      ≈⟨ axDist∨≡ ∣ σ₁ ⟩
        (p ∨ (p ≡ q)) ≡ (p ∨ (p ∨ q))
      ≈⟨ preemp ∼⟨⟨ axDist∨≡ ∣ σ₂ , axAssoc∨ ∣ σ₂ ⟩⟩∼ ⟩
        (((p ∨ p) ≡ (p ∨ q)) ≡ ((p ∨ p) ∨ q))
      ≈⟨ preemp ∼⟨⟨ preemp ∼⟨⟨ axIdem∨ ∣ idSubst , prefl ⟩⟩∼
                 , preemp ∼⟨⟨ axIdem∨ ∣ idSubst , prefl ⟩⟩∼ ⟩⟩∼ ⟩
        (p ≡ (p ∨ q)) ≡ (p ∨ q)
      ≈⟨ psym (axAssoc≡ ∣ σ₃) ⟩
        p ≡ ((p ∨ q) ≡ (p ∨ q))
      ≈⟨ preemp ∼⟨⟨ prefl , axRefl≡ ∣ σ₄ ⟩⟩∼ ⟩
        p ≡ true₂
      ≈⟨ axNeu≡ ∣ idSubst ⟩
        p
      ∎
      where σ₁ : Subst
            σ₁ (_ , 1) = p ≡ q
            σ₁ (_ , 2) = p ∨ q
            σ₁ x = term (inj₂ x) ⟨⟩
            σ₂ : Subst
            σ₂ (_ , 1) = p
            σ₂ (_ , 2) = q
            σ₂ x = term (inj₂ x) ⟨⟩
            σ₃ : Subst
            σ₃ (_ , 1) = p ∨ q
            σ₃ (_ , 2) = p ∨ q
            σ₃ x = term (inj₂ x) ⟨⟩
            σ₄ : Subst
            σ₄ (_ , 0) = p ∨ q
            σ₄ x = term (inj₂ x) ⟨⟩
            

    T₂⊢defF : Tbool₂ ⊢ eq↝ defF
    T₂⊢defF =
      begin
         (p ≡ (p ≡ false₂)) ≡ (p ∨ (p ≡ false₂))
       ≈⟨ preemp (∼⟨⟨ axAssoc≡ ∣ σ₁ , axDist∨≡ ∣ σ₁ ⟩⟩∼) ⟩
         ((p ≡ p) ≡ false₂) ≡ ((p ∨ p) ≡ (p ∨ false₂))
       ≈⟨ preemp ∼⟨⟨ preemp ∼⟨⟨ axRefl≡ ∣ idSubst , prefl ⟩⟩∼ ,
                    preemp ∼⟨⟨ axIdem∨ ∣ idSubst , axNeu∨ ∣ idSubst ⟩⟩∼ ⟩⟩∼ ⟩
         (true₂ ≡ false₂) ≡ (p ≡ p)
       ≈⟨ preemp ∼⟨⟨ axComm≡ ∣ σ₂ , axRefl≡ ∣ idSubst ⟩⟩∼ ⟩
         (false₂ ≡ true₂) ≡ true₂
       ≈⟨ preemp (∼⟨⟨ axNeu≡ ∣ σ₃ , prefl ⟩⟩∼) ⟩
         false₂ ≡ true₂
       ≈⟨ axNeu≡ ∣ σ₃ ⟩
         false₂
       ∎
      where σ₁ : Subst
            -- q ⟶ p ; r ⟶ false ; x ⟶ x
            σ₁ (_ , 1) = p
            σ₁ (_ , 2) = false₂
            σ₁ x = term (inj₂ x) ⟨⟩
            -- p ⟶ true ; q ⟶ false ; x ⟶ x
            σ₂ : Subst
            σ₂ (_ , 0) = true₂
            σ₂ (_ , 1) = false₂
            σ₂ x = term (inj₂ x) ⟨⟩
            -- p ⟶ false ; x ⟶ x
            σ₃ : Subst
            σ₃ (_ , 0) = false₂
            σ₃ x = term (inj₂ x) ⟨⟩
            

    
    T₂⊢3excl : Tbool₂ ⊢ eq↝ 3excl
    T₂⊢3excl =
      begin
        p ∨ (p ≡ false₂)
      ≈⟨ axDist∨≡ ∣ σ₁ ⟩
        (p ∨ p) ≡ (p ∨ false₂)
      ≈⟨ preemp (∼⟨⟨ axIdem∨ ∣ idSubst , axNeu∨ ∣ idSubst ⟩⟩∼) ⟩
        p ≡ p
      ≈⟨ axRefl≡ ∣ idSubst ⟩
        true₂
      ∎
      where σ₁ : Subst
            -- q ⟶ p
            σ₁ (_ , 1) = p
            -- r ⟶ false
            σ₁ (_ , 2) = false₂
            -- x ⟶ x
            σ₁ x = term (inj₂ x) ⟨⟩

    -- These proofs are tedious, so we postulate them.
    postulate T₂⊢assoc∧ : Tbool₂ ⊢ eq↝ assocAnd
    postulate T₂⊢comm∧ : Tbool₂ ⊢ eq↝ commAnd
    postulate T₂⊢dist∧∨ : Tbool₂ ⊢ eq↝ distAndOr
    postulate T₂⊢dist∨∧ : Tbool₂ ⊢ eq↝ distOrAnd

    T₂⇒T₁ : Tbool₂ ⇒T~ Tbool₁
    T₂⇒T₁ axAssoc∧ = T₂⊢assoc∧
    T₂⇒T₁ axComm∧ = T₂⊢comm∧
    T₂⇒T₁ axAssoc∨₁ = T₂⊢assoc∨₁
    T₂⇒T₁ axComm∨₁ = T₂⊢comm∨₁
    T₂⇒T₁ axIdem∧ = T₂⊢idem∧
    T₂⇒T₁ axIdem∨₁ = T₂⊢idem∨
    T₂⇒T₁ axDist∧∨ = T₂⊢dist∧∨
    T₂⇒T₁ axDist∨∧ = T₂⊢dist∨∧
    T₂⇒T₁ axAbs₁ = T₂⊢abs₁
    T₂⇒T₁ axAbs₂ = T₂⊢abs₂
    T₂⇒T₁ axDefF = T₂⊢defF
    T₂⇒T₁ ax3excl = T₂⊢3excl
    T₂⇒T₁ noax₁

-- Bool is model of Tbool₂
module BoolModel₂ where

  open import Data.Bool
  open import Relation.Binary.PropositionalEquality as PE
  open import Relation.Binary
  open import Function.Equality hiding (setoid)

  BCarrier : sorts Σbool₁ → Setoid _ _
  BCarrier _ = setoid Bool

  _=b_ : Bool → Bool → Bool
  false =b b₂ = not b₂
  true  =b b₂ = b₂

  Bops : ∀ {ar s} → (f : ops Σbool₂ (ar , s)) →
           BCarrier ✳ ar ⟶ BCarrier s
  Bops t₂ = record { _⟨$⟩_ = λ _ → true ; cong = λ _ → refl }
  Bops f₂ = record { _⟨$⟩_ = λ _ → false ; cong = λ _ → refl }
  Bops or₂ = record { _⟨$⟩_ = λ { ⟨⟨ b , b' ⟩⟩ → b ∨ b' } ;
                      cong = λ { {⟨⟨ b₀ , b₀' ⟩⟩} {⟨⟨ b₁ , b₁' ⟩⟩}
                                 (∼▹ b₀≡b₁ (∼▹ b₀'≡b₁' ∼⟨⟩)) →
                                                     cong₂ _∨_ b₀≡b₁ b₀'≡b₁' } }
  Bops equiv₂ = record { _⟨$⟩_ = λ { ⟨⟨ b , b' ⟩⟩ → b =b b' } ;
                      cong = λ { {⟨⟨ b₀ , b₀' ⟩⟩} {⟨⟨ b₁ , b₁' ⟩⟩}
                                 (∼▹ b₀≡b₁ (∼▹ b₀'≡b₁' ∼⟨⟩)) →
                                                    cong₂ _=b_ b₀≡b₁ b₀'≡b₁' } }


  B₂ : Algebra Σbool₂
  B₂ = BCarrier ∥ Bops

  open Theory₂

  B₂⊨assoc≡ : B₂ ⊨ assocEquiv
  B₂⊨assoc≡ θ ∼⟨⟩ with θ varp | θ varq | θ varr
  B₂⊨assoc≡ θ ∼⟨⟩ | true | b | c = refl
  B₂⊨assoc≡ θ ∼⟨⟩ | false | true | c = refl
  B₂⊨assoc≡ θ ∼⟨⟩ | false | false | false = refl
  B₂⊨assoc≡ θ ∼⟨⟩ | false | false | true = refl


  B₂⊨comm≡ : B₂ ⊨ commEquiv
  B₂⊨comm≡ θ ∼⟨⟩ with θ varp | θ varq
  B₂⊨comm≡ θ ∼⟨⟩ | false | false = refl
  B₂⊨comm≡ θ ∼⟨⟩ | false | true = refl
  B₂⊨comm≡ θ ∼⟨⟩ | true | false = refl
  B₂⊨comm≡ θ ∼⟨⟩ | true | true = refl


  B₂⊨assoc∨ : B₂ ⊨ assocOr
  B₂⊨assoc∨ θ ∼⟨⟩ with θ varp | θ varq | θ varr
  B₂⊨assoc∨ θ ∼⟨⟩ | false | b | c = refl
  B₂⊨assoc∨ θ ∼⟨⟩ | true | b | c = refl

  B₂⊨comm∨ : B₂ ⊨ commOr
  B₂⊨comm∨ θ ∼⟨⟩ with θ varp | θ varq
  B₂⊨comm∨ θ ∼⟨⟩ | false | false = refl
  B₂⊨comm∨ θ ∼⟨⟩ | false | true = refl
  B₂⊨comm∨ θ ∼⟨⟩ | true | false = refl
  B₂⊨comm∨ θ ∼⟨⟩ | true | true = refl

  B₂⊨neu≡ : B₂ ⊨ neuEquiv
  B₂⊨neu≡ θ ∼⟨⟩ with θ varp
  B₂⊨neu≡ θ ∼⟨⟩ | false = refl
  B₂⊨neu≡ θ ∼⟨⟩ | true = refl

  B₂⊨refl≡ : B₂ ⊨ reflEquiv
  B₂⊨refl≡ θ ∼⟨⟩ with θ varp
  B₂⊨refl≡ θ ∼⟨⟩ | false = refl
  B₂⊨refl≡ θ ∼⟨⟩ | true = refl

  B₂⊨abs∨ : B₂ ⊨ absOr
  B₂⊨abs∨ θ ∼⟨⟩ with θ varp
  B₂⊨abs∨ θ ∼⟨⟩ | false = refl
  B₂⊨abs∨ θ ∼⟨⟩ | true = refl

  B₂⊨neu∨ : B₂ ⊨ neuOr
  B₂⊨neu∨ θ ∼⟨⟩ with θ varp
  B₂⊨neu∨ θ ∼⟨⟩ | false = refl
  B₂⊨neu∨ θ ∼⟨⟩ | true = refl

  B₂⊨idem∨ : B₂ ⊨ idemOr
  B₂⊨idem∨ θ ∼⟨⟩ with θ varp
  B₂⊨idem∨ θ ∼⟨⟩ | false = refl
  B₂⊨idem∨ θ ∼⟨⟩ | true = refl

  B₂⊨dist∨≡ : B₂ ⊨ distOrEquiv
  B₂⊨dist∨≡ θ ∼⟨⟩ with θ varp | θ varq | θ varr
  B₂⊨dist∨≡ θ ∼⟨⟩ | false | b | c = refl
  B₂⊨dist∨≡ θ ∼⟨⟩ | true | b | c = refl

  B₂model : B₂ ⊨T Tbool₂
  B₂model axAssoc≡ = B₂⊨assoc≡
  B₂model axComm≡ = B₂⊨comm≡
  B₂model axAssoc∨ = B₂⊨assoc∨
  B₂model axComm∨ = B₂⊨comm∨
  B₂model axNeu≡ = B₂⊨neu≡
  B₂model axRefl≡ = B₂⊨refl≡
  B₂model axAbs∨ = B₂⊨abs∨
  B₂model axNeu∨ = B₂⊨neu∨
  B₂model axIdem∨ = B₂⊨idem∨
  B₂model axDist∨≡ = B₂⊨dist∨≡
  B₂model noax




-- Bool is model Tbool₁
module BoolModel₁ where
  open import Data.Bool
  open ReductAlgebra Σtrans
  open BoolModel₂

  {- Instead of prove that Bool is model of Tbool₁ (i.e., 
     it satisfies each axiom) we obtain this model from
     B₂ via the reduct theorem -}
  
  B₁ : Algebra Σbool₁
  B₁ = 〈 B₂ 〉

  open Theory₁
  open Theory₂
  open Theory₂.Tbool₂⇒Tbool₁
  open TheoryTrans.ModelPreserv Σtrans Vars₁ Tbool₁

  B₁model : B₁ ⊨T Tbool₁
  B₁model = ⊨T⇒↝ Tbool₂ T₂⇒T₁ B₂ B₂model
