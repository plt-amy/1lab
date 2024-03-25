open import Cat.Prelude

import Cat.Functor.Reasoning as Func
import Cat.Reasoning as Cat

module Cat.Functor.Reasoning.Presheaf
  {o ℓ s} {C : Precategory o ℓ} (P : Functor C (Sets s))
  where

private
  module C = Cat C
  module Pf = Func P
  open Precategory C

open Functor P using (F₀ ; F₁ ; ₀ ; ₁) public

private variable
  U V W : ⌞ C ⌟
  f g h i f' g' h' i' : C.Hom U V
  x y z : ∣ F₀ U ∣

F-id : ∀ {U : ⌞ C ⌟} {x} → F₁ {U} id x ≡ x
F-id = happly Pf.F-id _

F-∘
  : ∀ {U V W} (f : Hom V U) (g : Hom W V) {x}
  → F₁ (f ∘ g) x ≡ F₁ f (F₁ g x)
F-∘ f g = happly (Pf.F-∘ f g) _

elim : f ≡ id → F₁ f x ≡ x
elim p = happly (Pf.elim p) _

intro : id ≡ f → x ≡ F₁ f x
intro p = sym (elim (sym p))

collapse : f ∘ g ≡ h → F₁ f (F₁ g x) ≡ F₁ h x
collapse p = happly (Pf.collapse p) _

expand : h ≡ f ∘ g → F₁ h x ≡ F₁ f (F₁ g x)
expand p = happly (Pf.expand p) _

weave : f ∘ g ≡ h ∘ i → F₁ f (F₁ g x) ≡ F₁ h (F₁ i x)
weave p = happly (Pf.weave p) _

annihilate : f ∘ g ≡ id → F₁ f (F₁ g x) ≡ x
annihilate p = happly (Pf.annihilate p) _

conjure : id ≡ f ∘ g → x ≡ F₁ f (F₁ g x)
conjure p = sym (annihilate (sym p))
