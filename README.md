*** Formalization of Universal Algebra in Agda ***

This development corresponds to the formalization of 
Universal Algebra in Agda, accepted for presentation in LSFA 2017.

This README file contains instructions to install agda and compile
the library, and a description of the modules.

** Installation **

The formalization was tested on Ubuntu with Agda 2.5.2 installed and
the standard library version 0.13.

* How to install agda (using cabal) with emacs, and the standard
library in Ubuntu:

- Install emacs.
- Install 'Haskell platform' using apt-get:
  	  $ apt-get install haskell-platform
- Install 'cpphs' using cabal:
  	  $ cabal install cpphs
- Install 'agda' using cabal:
  	  $ cabal install agda
- Download the standard library version 0.13 from
  https://github.com/agda/agda-stdlib/archive/v0.13.tar.gz
- Unpack the tar.gz file to somewhere, say '~/.agda/agda-stdlib-0.13'.
- Create the file '~/.agda/libraries' and put the text:
  	 ~/.agda/agda-stdlib-0.13/standard-library.agda-lib
(replace folder '~/.agda/agda-stdlib-0.13' if it corresponds).
- Create the file '~/.agda/defaults' with the line:
  	 standard-library
- Edit file .emacs. Put the following text:
       	 (load-file (let ((coding-system-for-read 'utf-8))
                (shell-command-to-string "agda-mode locate")))

** Modules **

The formalization is modularized in these files:

- Setoids.agda
	Definitions and properties about setoids.
- HeterogeneousVec.agda
	Definition, operations, and properties of heterogeneous vectors.
- UnivAlgebra.agda
	Basic definitions of Heterogeneous Universal Algebra:
   	Signature, Algebra, Homomorphism, Congruence, Quotient, Subalgebra.
- Morphisms.agda
	Definitions of Homomorphism, Homo composition and equality,
        Isomorphism, Initial and Final Algebras, Homomorphic image and
	Kernel of a congruence.
- IsoTheorems.agda
	Proofs of the three isomorphism theorems.
- TermAlgebra.agda
	Definition of the term algebra of a signature and proof of initiality.
- SigMorphism.agda
	Definition of derived signature morphisms and reduct algebras.
	Translation of terms and theories.
- Equational.agda
	Formalization of conditional equational logic: Signature with variables,
	equations, environments, proofs, models, proof of Birkhoff soundness and
	completeness.
- Examples
  -- EqBool.agda
	  Definition of two theories of Boolean algebras; translation between them,
	  and preservation of models.
  -- Monoid.agda
          Definition of the theory of Monoids. Examples of monoids (as algebras)
	  and a homomorphism between them. 
	  Bijection between the standard library definition of monoids
	  and the universal algebra approach.	  
  -- Group.agda
	  Definition of the theory of Groups, as an extension for the theory of Monoids.
  -- CompilerArith.agda
	  McCarthy and Painter compiler correct by construction by framing it
	  as a translation of signatures.
  -- GoguenMeseguer.agda
	  Example taken from the paper “Completeness of many-sorted
	  equational logic” by Goguen and Meseguer. Its first example
	  shows that when defining satisfiablity naively, the
	  deduction system is not sound. As can be seen in this module,
	  our formalization prevents that their example can be completed.

** Using the library **

You can load a file in emacs and type-check it with the command "C-c C-l".
Alternatively one uses the type-checker from the command line:
  $ agda Examples/Monoid.agda
  
A reference with commands to edit, type check and compile Agda code in emacs is
available online: http://agda.readthedocs.io/en/latest/tools/emacs-mode.html
