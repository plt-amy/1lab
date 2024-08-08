open import Cat.Instances.Functor.Limits
open import Cat.Instances.Sets.Complete
open import Cat.Diagram.Exponential
open import Cat.Diagram.Everything
open import Cat.Instances.Functor
open import Cat.Functor.Adjoint
open import Cat.Instances.Sets
open import Cat.Functor.Hom
open import Cat.Prelude

open import Data.Sum

import Cat.Functor.Bifunctor as Bifunctor
import Cat.Reasoning

module Cat.CartesianClosed.Instances.PSh where

open Functor
open _=>_
open _⊣_

-- This module has explicit computational representations of a bunch of
-- stuff we know exists by abstract nonsense.

module _ {o ℓ κ} {C : Precategory o ℓ} where
  private
    module C = Cat.Reasoning C
    module PSh = Cat.Reasoning (PSh κ C)

  PSh-terminal : Terminal (PSh κ C)
  PSh-terminal = record { top = top ; has⊤ = uniq } where
    top : Functor (C ^op) (Sets κ)
    top .F₀ x = el! (Lift κ ⊤)
    top .F₁ _ _ = lift tt
    top .F-id = refl
    top .F-∘ _ _ = refl

    uniq : is-terminal (PSh κ C) top
    uniq x .centre .η _ _ = lift tt
    uniq x .centre .is-natural _ _ _ = refl
    uniq x .paths f = trivial!

  PSh-pullbacks
    : ∀ {X Y Z} (f : PSh.Hom X Z) (g : PSh.Hom Y Z)
    → Pullback (PSh κ C) f g
  PSh-pullbacks {X} {Y} {Z} f g = pb where
    module X = Functor X
    module Y = Functor Y
    module Z = Functor Z
    module f = _=>_ f
    module g = _=>_ g
    open Pullback
    open is-pullback

    pb-path
      : ∀ {i} {x y : Σ[ x ∈ X.₀ i ] Σ[ y ∈ Y.₀ i ] f.η i x ≡ g.η i y}
      → x .fst ≡ y .fst
      → x .snd .fst ≡ y .snd .fst
      → x ≡ y
    pb-path p q i .fst = p i
    pb-path p q i .snd .fst = q i
    pb-path {idx} {x} {y} p q i .snd .snd j =
      is-set→squarep (λ _ _ → Z.₀ idx .is-tr)
        (ap (f .η idx) p) (x .snd .snd) (y .snd .snd) (ap (g .η idx) q)
        i j

    pb : Pullback (PSh κ C) f g
    pb .apex .F₀ i = el! (Σ[ x ∈ X.₀ i ] Σ[ y ∈ Y.₀ i ] f.η i x ≡ g.η i y)
    pb .apex .F₁ {x} {y} h (a , b , p) = X.₁ h a , Y.₁ h b , path where abstract
      path : f.η y (X.₁ h a) ≡ g.η y (Y.₁ h b)
      path = happly (f.is-natural _ _ _) _
          ·· (λ i → Z.₁ h (p i))
          ·· sym (happly (g.is-natural _ _ _) _)
    pb .apex .F-id = funext λ (a , b , _) → pb-path (X.F-id $ₚ a) (Y.F-id $ₚ b)
    pb .apex .F-∘ f g = funext λ (a , b , _) → pb-path (X.F-∘ f g $ₚ a) (Y.F-∘ f g $ₚ b)
    pb .p₁ .η idx (a , b , _) = a
    pb .p₁ .is-natural _ _ _ = refl
    pb .p₂ .η x (a , b , _) = b
    pb .p₂ .is-natural _ _ _ = refl
    pb .has-is-pb .square = ext λ _ _ _ p → p
    pb .has-is-pb .universal path .η idx arg = _ , _ , unext path _ _
    pb .has-is-pb .universal {p₁' = p₁'} {p₂'} path .is-natural x y f = funext λ x →
      pb-path (happly (p₁' .is-natural _ _ _) _) (happly (p₂' .is-natural _ _ _) _)
    pb .has-is-pb .p₁∘universal = trivial!
    pb .has-is-pb .p₂∘universal = trivial!
    pb .has-is-pb .unique p q = ext λ _ _ →
      pb-path (unext p _ _) (unext q _ _)

  PSh-products : (A B : PSh.Ob) → Product (PSh κ C) A B
  PSh-products A B = prod where
    open Product
    open is-product
    module A = Functor A
    module B = Functor B

    prod : Product (PSh _ C) A B
    prod .apex .F₀ x = el! (∣ A.₀ x ∣ × ∣ B.₀ x ∣)
    prod .apex .F₁ f (x , y) = A.₁ f x , B.₁ f y
    prod .apex .F-id i (x , y) = A.F-id i x , B.F-id i y
    prod .apex .F-∘ f g i (x , y) = A.F-∘ f g i x , B.F-∘ f g i y
    prod .π₁ = NT (λ x → fst) (λ _ _ _ → refl)
    prod .π₂ = NT (λ x → snd) (λ _ _ _ → refl)
    prod .has-is-product .⟨_,_⟩ f g =
      NT (λ i x → f .η i x , g .η i x) λ x y h i a →
        f .is-natural x y h i a , g .is-natural x y h i a
    prod .has-is-product .π₁∘⟨⟩ = trivial!
    prod .has-is-product .π₂∘⟨⟩ = trivial!
    prod .has-is-product .unique p q = ext λ i x → unext p i x , unext q i x

  {-# TERMINATING #-}
  PSh-coproducts : (A B : PSh.Ob) → Coproduct (PSh κ C) A B
  PSh-coproducts A B = coprod where
    open Coproduct
    open is-coproduct
    module A = Functor A
    module B = Functor B

    coprod : Coproduct (PSh _ C) A B
    coprod .coapex .F₀ i = el! (∣ A.₀ i ∣ ⊎ ∣ B.₀ i ∣)
    coprod .coapex .F₁ h (inl x) = inl (A.₁ h x)
    coprod .coapex .F₁ h (inr x) = inr (B.₁ h x)
    coprod .coapex .F-id = funext λ where
      (inl x) → ap inl (happly A.F-id x)
      (inr x) → ap inr (happly B.F-id x)
    coprod .coapex .F-∘ f g = funext λ where
      (inl x) → ap inl (happly (A.F-∘ f g) x)
      (inr x) → ap inr (happly (B.F-∘ f g) x)
    coprod .ι₁ .η _ x = inl x
    coprod .ι₁ .is-natural x y f i a = inl (A.₁ f a)
    coprod .ι₂ .η _ x = inr x
    coprod .ι₂ .is-natural x y f i b = inr (B.₁ f b)
    coprod .has-is-coproduct .is-coproduct.[_,_] f g .η _ (inl x) = f .η _ x
    coprod .has-is-coproduct .is-coproduct.[_,_] f g .η _ (inr x) = g .η _ x
    coprod .has-is-coproduct .is-coproduct.[_,_] f g .is-natural x y h = funext λ where
      (inl x) → f .is-natural _ _ _ $ₚ _
      (inr x) → g .is-natural _ _ _ $ₚ _
    coprod .has-is-coproduct .[]∘ι₁ = trivial!
    coprod .has-is-coproduct .[]∘ι₂ = trivial!
    coprod .has-is-coproduct .unique p q = ext λ where
      a (inl x) → unext p a x
      a (inr x) → unext q a x

  PSh-coequaliser
    : ∀ {X Y} (f g : PSh.Hom X Y)
    → Coequaliser (PSh κ C) f g
  PSh-coequaliser {X = X} {Y = Y} f g = coequ where
    open Coequaliser
    open is-coequaliser
    module X = Functor X
    module Y = Functor Y

    incq : ∀ {i} → _ → Coeq (f .η i) (g .η i)
    incq = inc

    coequ : Coequaliser (PSh _ C) f g
    coequ .coapex .F₀ i = el (Coeq (f .η i) (g .η i)) squash
    coequ .coapex .F₁ h = Coeq-rec (λ g → inc (Y.₁ h g)) λ x →
      inc (Y.₁ h (f .η _ x)) ≡˘⟨ ap incq (happly (f .is-natural _ _ h) x) ⟩
      inc (f .η _ _)         ≡⟨ glue (X.₁ h x) ⟩
      inc (g .η _ _)         ≡⟨ ap incq (happly (g .is-natural _ _ h) x) ⟩
      inc (Y.₁ h (g .η _ x)) ∎
    coequ .coapex .F-id = ext λ _ → ap incq (happly Y.F-id _)
    coequ .coapex .F-∘ f g = ext λ _ → ap incq (happly (Y.F-∘ f g) _)
    coequ .coeq .η i = incq
    coequ .coeq .is-natural x y f = refl
    coequ .has-is-coeq .coequal = ext λ i x → glue x
    coequ .has-is-coeq .universal {F = F} {e' = e'} p .η x =
      Coeq-rec (e' .η x) (p ηₚ x $ₚ_)
    coequ .has-is-coeq .universal {F = F} {e' = e'} p .is-natural x y f = ext λ x →
      e' .is-natural _ _ _ $ₚ _
    coequ .has-is-coeq .factors = trivial!
    coequ .has-is-coeq .unique {F = F} p = reext! p

module _ {κ} {C : Precategory κ κ} where
  private
    module C = Cat.Reasoning C
    module PSh = Cat.Reasoning (PSh κ C)

  open Binary-products (PSh κ C) (PSh-products {C = C})

  PSh[_,_] : PSh.Ob → PSh.Ob → PSh.Ob
  PSh[ A , B ] = F module psh-exp where
    module A = Functor A
    module B = Functor B

    F : PSh.Ob
    F .F₀ c = el ((よ₀ C c ⊗₀ A) => B) Nat-is-set
    F .F₁ f nt .η i (g , x) = nt .η i (f C.∘ g , x)
    F .F₁ f nt .is-natural x y g = funext λ o →
      ap (nt .η y) (Σ-pathp (C.assoc _ _ _) refl) ∙ happly (nt .is-natural _ _ _) _
    F .F-id = ext λ f i g x →
      ap (f .η i) (Σ-pathp (C.idl _) refl)
    F .F-∘ f g = ext λ h i j x →
      ap (h .η i) (Σ-pathp (sym (C.assoc _ _ _)) refl)

  {-# DISPLAY psh-exp.F A B = PSh[ A , B ] #-}

  PSh-closed : Cartesian-closed (PSh κ C) (PSh-products {C = C}) (PSh-terminal {C = C})
  PSh-closed = cc where
    cat = PSh κ C

    module _ (A : PSh.Ob) where
      func : Functor (PSh κ C) (PSh κ C)
      func .F₀ = PSh[ A ,_]
      func .F₁ f .η i g .η j (h , x) = f .η _ (g .η _ (h , x))
      func .F₁ f .η i g .is-natural x y h = funext λ x →
        ap (f .η _) (happly (g .is-natural _ _ _) _) ∙ happly (f .is-natural _ _ _) _
      func .F₁ nt .is-natural x y f = trivial!
      func .F-id = trivial!
      func .F-∘ f g = trivial!

      adj : Bifunctor.Left ×-functor A ⊣ func
      adj .unit .η x .η i a =
        NT (λ j (h , b) → x .F₁ h a , b) λ _ _ _ → funext λ _ →
          Σ-pathp (happly (x .F-∘ _ _) _) refl
      adj .unit .η x .is-natural _ _ _ = ext λ _ _ _ _ → sym (x .F-∘ _ _ # _) , refl
      adj .unit .is-natural x y f = ext λ _ _ _ _ _ → sym (f .is-natural _ _ _ $ₚ _) , refl
      adj .counit .η _ .η _ x = x .fst .η _ (C.id , x .snd)
      adj .counit .η _ .is-natural x y f = funext λ h →
        ap (h .fst .η _) (Σ-pathp C.id-comm refl) ∙ happly (h .fst .is-natural _ _ _) _
      adj .counit .is-natural x y f = trivial!
      adj .zig {A} = ext λ x _ _ → happly (F-id A) _ , refl
      adj .zag {A} = ext λ _ x i f g j → x .η i (C.idr f j , g)

    cc : Cartesian-closed (PSh κ C) (PSh-products {C = C}) (PSh-terminal {C = C})
    cc = product-adjoint→cartesian-closed (PSh κ C)
      (PSh-products {C = C}) (PSh-terminal {C = C}) func adj
