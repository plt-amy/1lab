<!--
```agda
open import Cat.Morphism.Duality
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Groupoid where
```

# Groupoids {defines="pregroupoid"}

A category $\cC$ is a (pre)**groupoid** if every morphism of $\cC$ is
invertible.

```agda
is-pregroupoid : ∀ {o ℓ} → Precategory o ℓ → Type (o ⊔ ℓ)
is-pregroupoid C = ∀ {x y} (f : Hom x y) → is-invertible f
  where open Cat.Reasoning C
```

<!--
```agda
module _ {o ℓ} (C : Precategory o ℓ) (gpd : is-pregroupoid C) where
```
-->

Of course, the [[opposite]] of a groupoid is a groupoid.

```agda
  ^op-pregroupoid : is-pregroupoid (C ^op)
  ^op-pregroupoid f = invertible→co-invertible C (gpd f)
```

If $\cC$ is a pregroupoid, then the map $x \iso y \to \cC(x,y)$ that
forgets the inverse is an [[equivalence]].

```agda
module is-pregroupoid {o ℓ} (C : Precategory o ℓ) (gpd : is-pregroupoid C) where
  open Cat.Reasoning C

  forget-iso-is-equiv : ∀ {x y} → is-equiv (λ (f : x ≅ y) → f .to)
```

First, recall that being invertible is a [[property]] of morphisms.
This means that the first projection `Σ[ f ∈ Hom x y ] is-invertible f`
out of must be an equivalence, as all of the fibres are prop-valued
and inhabited. Moreover, the type of isomorphisms $x \iso y$ is equivalent
to the above sigma type, so 2-out-of-3 for equivalences gives us our desired
result.

```agda
  forget-iso-is-equiv {x} {y} =
    equiv-cancelr
      (inverse-is-equiv (iso≃is-invertible .snd))
      proj-is-equiv
    where
      proj-is-equiv : is-equiv {A = Σ[ f ∈ Hom x y ] is-invertible f} fst
      proj-is-equiv = Subtype-proj-is-equiv (λ _ → hlevel 1) gpd
```

<!--
```agda
  hom→iso : ∀ {x y} → Hom x y → x ≅ y
  hom→iso f = invertible→iso f (gpd f)

  hom≃iso : ∀ {x y} → Hom x y ≃ (x ≅ y)
  hom≃iso .fst = hom→iso
  hom≃iso .snd = inverse-is-equiv forget-iso-is-equiv
```
-->

## Univalent groupoids

:::{.definition #univalent-groupoid}
A precategory $\cC$ is a **univalent groupoid** or **groupoid** if
the type of morphisms of $\cC$ forms an [[identity system]] on $\cC$.
:::


```agda
is-univalent-groupoid : ∀ {o ℓ} → Precategory o ℓ → Type _
is-univalent-groupoid C = is-identity-system Hom λ x → id {x}
  where open Precategory C
```

As the name suggests, every univalent groupoid is both [[univalent category]] and aunivalent-categoryun pregroupoid.

```agda
module is-univalent-groupoid {o ℓ} (C : Precategory o ℓ) (C-gpd : is-univalent-groupoid C) where
  open Cat.Reasoning C

  univalent : is-category C
  pregroupoid : is-pregroupoid C
```

We shall start by showing that $\cC$ is a pregroupoid. Let
$f : \cC(X,Y)$ be a morphism of $\cC$: our goal is to show
that it is invertible. However, $\cC(x,y)$ is an identity
system, so we can contract $f$ down to $\id$, which is obviously
invertible!

```agda
  pregroupoid = IdsJ C-gpd (λ y f → is-invertible f) id-invertible
```

By our previous result, we now know that the type of morphisms $\cC(x,y)$ is
equivalent to type of isomorphisms $x \iso y$. Moreover, this equivalence
sends the identity morphism to the identity isomorphism. This means that
we can prove that $\cC$ is univalent by transferring the identity system on
morphisms along this equivalence.

```agda
  open is-pregroupoid C pregroupoid public

  univalent = transfer-identity-system C-gpd (λ x y → hom≃iso) λ x → ext refl
```

We can use a similar argument to establish that every univalent pregroupoid
is a univalent groupoid.

```agda
is-univalent-pregroupoid→is-univalent-groupoid
  : ∀ {o ℓ} {C : Precategory o ℓ}
  → is-category C
  → is-pregroupoid C
  → is-univalent-groupoid C
is-univalent-pregroupoid→is-univalent-groupoid {C = C} C-cat C-gpd =
  transfer-identity-system C-cat (λ x y → hom≃iso e⁻¹) λ _ → refl
  where
    open is-pregroupoid C C-gpd
```
