<!--
```agda
{-# OPTIONS -vtc.decl:5 #-}
open import Cat.Functor.Equivalence.Path
open import Cat.Functor.Equivalence
open import Cat.Prelude

import Cat.Instances.Elements as Contra
```
-->

```agda
module Cat.Instances.Elements.Covariant where
```

<!--
```agda
module _ {o ℓ s} {C : Precategory o ℓ} (P : Functor C (Sets s)) where
  private module P = Functor P

  open Precategory C
  open Functor
```
-->

# The covariant category of elements {defines="covariant-category-of-elements"}

While the [[category of elements]] comes up most often in the context of presheaves
(i.e., contravariant functors into $\Sets$), the construction makes sense for
covariant functors as well.

Sadly, we cannot simply reuse the contravariant construction,
instantiating $\cC$ as $\cC\op$: the resulting category would be the
[[opposite|opposite category]] of what we want. Indeed, in both the covariant and
contravariant cases, we want the projection $\pi : \int F \to \cC$ to be covariant.

Thus we proceed to dualise the whole construction.

```agda
  record Element : Type (o ⊔ s) where
    constructor elem
    field
      ob : Ob
      section : P ʻ ob

  open Element

  record Element-hom (x y : Element) : Type (ℓ ⊔ s) where
    constructor elem-hom
    no-eta-equality
    field
      hom     : Hom (x .ob) (y .ob)
      commute : P.₁ hom (x .section) ≡ y .section

  open Element-hom
```

<!--
```agda
  private unquoteDecl eqv = declare-record-iso eqv (quote Element-hom)
  Element-hom-is-set : ∀ (x y : Element) → is-set (Element-hom x y)
  Element-hom-is-set x y = Iso→is-hlevel 2 eqv T-is-set where
    T-is-set : is-set _
    T-is-set = hlevel!

  Element-hom-path : {x y : Element} {f g : Element-hom x y} → f .hom ≡ g .hom → f ≡ g
  Element-hom-path p i .hom = p i
  Element-hom-path {x = x} {y = y} {f = f} {g = g} p i .commute =
    is-prop→pathp (λ j → P.₀ (y .ob) .is-tr (P.₁ (p j) (x .section)) (y .section))
      (f .commute)
      (g .commute) i

module _ {o ℓ s} {C : Precategory o ℓ} {P : Functor C (Sets s)} where instance
  Extensional-element-hom
    : ∀ {x y : Element P} {ℓr}
    → ⦃ ext : Extensional (C .Precategory.Hom (x .Element.ob) (y .Element.ob)) ℓr ⦄
    → Extensional (Element-hom P x y) ℓr
  Extensional-element-hom ⦃ ext ⦄ = injection→extensional
    (C .Precategory.Hom-set _ _) (Element-hom-path P) ext

  open Precategory C

  H-Level-element-hom : ∀ {x y : Element P} {n} → H-Level (Element-hom P x y) (2 + n)
  H-Level-element-hom = basic-instance 2 $ Iso→is-hlevel 2 eqv hlevel!
    where unquoteDecl eqv = declare-record-iso eqv (quote Element-hom)

module _ {o ℓ s} {C : Precategory o ℓ} (P : Functor C (Sets s)) where
  private module P = Functor P

  open Precategory C
  open Element-hom
  open Element
  open Functor
```
-->

```agda
  ∫ : Precategory (o ⊔ s) (ℓ ⊔ s)
  ∫ .Precategory.Ob = Element P
  ∫ .Precategory.Hom = Element-hom P
  ∫ .Precategory.Hom-set _ _ = hlevel 2
  ∫ .Precategory.id {x = x} = elem-hom id λ i → P.F-id i (x .section)
  ∫ .Precategory._∘_ {x = x} {y = y} {z = z} f g = elem-hom (f .hom ∘ g .hom) comm where abstract
    comm : P.₁ (f .hom ∘ g .hom) (x .section) ≡ z .section
    comm =
      P.₁ (f .hom ∘ g .hom) (x .section)       ≡⟨ happly (P.F-∘ (f .hom) (g .hom)) (x .section) ⟩
      P.₁ (f .hom) (P.₁ (g .hom) (x .section)) ≡⟨ ap (P.F₁ (f .hom)) (g .commute)  ⟩
      P.₁ (f .hom) (y .section)                ≡⟨ f .commute ⟩
      z .section ∎
  ∫ .Precategory.idr f = ext (idr (f .hom))
  ∫ .Precategory.idl f = ext (idl (f .hom))
  ∫ .Precategory.assoc f g h = ext (assoc (f .hom) (g .hom) (h .hom))

  πₚ : Functor ∫ C
  πₚ .F₀ x = x .ob
  πₚ .F₁ f = f .hom
  πₚ .F-id = refl
  πₚ .F-∘ f g = refl
  ```

  We can now relate the two constructions: the covariant category of elements of $P$
  is the opposite of the contravariant category of elements of $P$ seen as a
  contravariant functor on $\cC\op$ (thus a functor $(\cC\op)\op = \cC \to \Sets$).

  ```agda
  co-∫ : ∫ ≡ Contra.∫ (C ^op) P ^op
  co-∫ = Precategory-path F F-is-precat-iso where
    F : Functor ∫ (Contra.∫ (C ^op) P ^op)
    F .F₀ e = Contra.elem (e .ob) (e .section)
    F .F₁ h = Contra.elem-hom (h .hom) (h .commute)
    F .F-id = refl
    F .F-∘ _ _ = ext refl

    F-is-precat-iso : is-precat-iso F
    F-is-precat-iso .is-precat-iso.has-is-iso = is-iso→is-equiv λ where
      .is-iso.inv e → elem (e .Contra.Element.ob) (e .Contra.Element.section)
      .is-iso.rinv e → refl
      .is-iso.linv e → refl
    F-is-precat-iso .is-precat-iso.has-is-ff = is-iso→is-equiv λ where
      .is-iso.inv h → elem-hom (h .Contra.Element-hom.hom) (h .Contra.Element-hom.commute)
      .is-iso.rinv h → ext refl
      .is-iso.linv h → ext refl
```
