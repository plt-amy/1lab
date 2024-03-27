-- This module doesn't have any text! That's because it's simply a bunch
-- of convenient re-exports for working in the Cat namespace.

module Cat.Prelude where

open import 1Lab.Prelude
  renaming ( _↪_ to _↣_
           ; _∘_ to _⊙_ -- \o.
           ; _⟩∘⟨_ to _⟩⊙⟨_
           ; refl⟩∘⟨_ to refl⟩⊙⟨_
           ; _⟩∘⟨refl to _⟩⊙⟨refl
           ; _∘⟨_ to _⊙⟨_
           ; _⟩∘_ to _⟩⊙_
           )
  hiding (id ; map ; _↠_)
  public

open import Data.Set.Truncation public
open import Data.Set.Coequaliser public

open import Cat.Base public
open import Cat.Solver hiding (module NbE; module Reflection) public
open import Cat.Univalent
  using ( is-category ; path→iso ; Hom-pathp
        ; Hom-transport ; Hom-pathp-refll ; Hom-pathp-reflr
        ; module Univalent )
  public
