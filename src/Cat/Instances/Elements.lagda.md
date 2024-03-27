<!--
```agda
open import Cat.Prelude
```
-->

```agda
module Cat.Instances.Elements where
```

<!--
```agda
module _ {o ℓ s} (C : Precategory o ℓ) (P : Functor (C ^op) (Sets s)) where
  open Precategory C
  open Functor
  private module P = Functor P
```
-->

# The category of elements {defines="category-of-elements contravariant-category-of-elements"}

The (contravariant^[there is a separate [[covariant category of elements]] for
covariant functors]) category of elements of a presheaf $P : \cC\op \to \Sets$
is a means of unpacking the data of the presheaf. Its objects are pairs of an
object $x$, and a section $s : P x$.

```agda
  record Element : Type (o ⊔ s) where
    constructor elem
    field
      ob : Ob
      section : P ʻ ob

  open Element
```

We can think of this as taking an eraser to the data of $P$. If $P(x) =
\{x_0, x_1, x_2\}$, then the category of elements of $P$ will have three
objects in place of the one: $(x, x_0)$, $(x, x_1)$, and $(x, x_2)$.
We've erased all the boundaries of each of the sets associated with $P$,
and are left with a big soup of points.

We do something similar for morphisms, and turn functions $P(f) : P(Y)
\to P(X)$ into a huge collection of morphisms between points. We do this
by defining a morphism $(x, x_0) \to (y, y_0)$ to be a morphism $f : X
\to Y$ in $\cC$, as well as a proof that $P(f)(y_0) = x_0$ This too
can be seen as erasing boundaries, just this time with the data
associated with a function. Instead of having a bunch of data bundled
together that describes the action of $P(f)$ on each point of $P(Y)$, we
have a bunch of tiny bits of data that only describe the action of
$P(f)$ on a single point.

```agda
  record Element-hom (x y : Element) : Type (ℓ ⊔ s) where
    constructor elem-hom
    no-eta-equality
    field
      hom : Hom (x .ob) (y .ob)
      commute : P.₁ hom (y .section) ≡ x .section

  open Element-hom
```

As per usual, we need to prove some helper lemmas that describe the path
space of `Element-hom`{.Agda}.

```agda
  Element-hom-path : {x y : Element} {f g : Element-hom x y} → f .hom ≡ g .hom → f ≡ g
  Element-hom-path p i .hom = p i
  Element-hom-path {x = x} {y = y} {f = f} {g = g} p i .commute =
    is-prop→pathp (λ j → P.₀ (x .ob) .is-tr (P.₁ (p j) (y .section)) (x .section))
      (f .commute)
      (g .commute) i
```

<!--
```agda

module _ {o ℓ s} {C : Precategory o ℓ} {P : Functor (C ^op) (Sets s)} where instance
  open Element

  Extensional-element-hom
    : ∀ {x y : Element C P} {ℓr}
    → ⦃ ext : Extensional (C .Precategory.Hom (x .ob) (y .ob)) ℓr ⦄
    → Extensional (Element-hom C P x y) ℓr
  Extensional-element-hom ⦃ ext ⦄ = injection→extensional
    (C .Precategory.Hom-set _ _) (Element-hom-path C P) ext

  open Precategory C

  H-Level-Element-hom
    : ∀ {x y : Element C P} {n}
    → H-Level (Element-hom C P x y) (2 + n)
  H-Level-Element-hom = basic-instance 2 $ Iso→is-hlevel 2 eqv hlevel!
    where unquoteDecl eqv = declare-record-iso eqv (quote Element-hom)

module _ {o ℓ s} (C : Precategory o ℓ) (P : Functor (C ^op) (Sets s)) where
  private module P = Functor P
  open Precategory C
  open Functor
  open Element-hom
  open Element
```
-->

One interesting fact is that morphisms $f : X \to Y$ in $C$ induce
morphisms in the category of elements for each $py : P(y)$.

```agda
  induce : ∀ {x y} (f : Hom x y) (py : P ʻ y)
        → Element-hom C P (elem x (P.₁ f py)) (elem y py)
  induce f _ = elem-hom f refl
```

Using all this machinery, we can now define the category of elements of
$P$!

```agda
  ∫ : Precategory (o ⊔ s) (ℓ ⊔ s)
  ∫ .Precategory.Ob = Element C P
  ∫ .Precategory.Hom = Element-hom C P
  ∫ .Precategory.Hom-set _ _ = hlevel 2
  ∫ .Precategory.id {x = x} = elem-hom id λ i → P.F-id i (x .section)
  ∫ .Precategory._∘_ {x = x} {y = y} {z = z} f g = elem-hom (f .hom ∘ g .hom) comm where abstract
    comm : P.₁ (f .hom ∘ g .hom) (z .section) ≡ x .section
    comm =
      P.₁ (f .hom ∘ g .hom) (z .section)       ≡⟨ happly (P.F-∘ (g .hom) (f .hom)) (z .section) ⟩
      P.₁ (g .hom) (P.₁ (f .hom) (z .section)) ≡⟨ ap (P.F₁ (g .hom)) (f .commute)  ⟩
      P.₁ (g .hom) (y .section)                ≡⟨ g .commute ⟩
      x .section ∎
  ∫ .Precategory.idr f = ext (idr _)
  ∫ .Precategory.idl f = ext (idl _)
  ∫ .Precategory.assoc f g h = ext (assoc _ _ _)
```

## Projection

The category of elements is equipped with a canonical projection functor
$\pi_p : \int P \to C$, which just forgets all of the points and
morphism actions.

```agda
  πₚ : Functor ∫ C
  πₚ .F₀ x = x .ob
  πₚ .F₁ f = f .hom
  πₚ .F-id = refl
  πₚ .F-∘ f g = refl
```

This functor makes it clear that we ought to think of the category of
elements as something defined _over_ $\cC$. For instance, if we look
at the fibre over each $X : \cC$, we get back the set $P(X)$!
