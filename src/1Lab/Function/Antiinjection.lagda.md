---
description: |
  Antiinjective functions.
---
<!--
```agda
open import 1Lab.Function.Surjection
open import 1Lab.Function.Embedding
open import 1Lab.HLevel.Universe
open import 1Lab.HIT.Truncation
open import 1Lab.HLevel.Closure
open import 1Lab.Inductive
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

open import Meta.Idiom
open import Meta.Bind
```
-->
```agda
module 1Lab.Function.Antiinjection where
```

<!--
```
private variable
  ℓ ℓ₁ : Level
  A B C : Type ℓ
  w x : A
```
-->

# Antiinjective functions {defines="split-antiinjective antiinjective"}

A function is **split antiinjective** if it comes equipped with a choice
of fibre that contains 2 distinct elements. Likewise, a function is
**antiinjective** if it is merely split injective. This is constructively
stronger than non-injective, as we actually know at least one obstruction
to injectivity! Moreover, note that split antiinjectivity is a structure
on a function, not a property; there may be obstructions to injectivity.

```agda
record split-antiinjective (f : A → B) : Type (level-of A ⊔ level-of B) where
  no-eta-equality
  field
    pt : B
    x₀ : A
    x₁ : A
    map-to₀ : f x₀ ≡ pt
    map-to₁ : f x₁ ≡ pt
    distinct : ¬ (x₀ ≡ x₁)

is-antiinjective : (A → B) → Type _
is-antiinjective f = ∥ split-antiinjective f ∥
```

<!--
```agda
open split-antiinjective
```
-->

As the name suggests, antiinjective functions are not injective.

```agda
split-antiinj→not-injective
  : {f : A → B}
  → split-antiinjective f
  → ¬ (injective f)
split-antiinj→not-injective f-antiinj f-inj =
  f-antiinj .distinct (f-inj (f-antiinj .map-to₀ ∙ sym (f-antiinj .map-to₁)))

is-antiinj→not-injective
  : {f : A → B}
  → is-antiinjective f
  → ¬ (injective f)
is-antiinj→not-injective f-antiinj =
  rec! split-antiinj→not-injective f-antiinj
```

<!--
```agda
split-antiinj→not-equiv
  : {f : A → B}
  → split-antiinjective f
  → ¬ (is-equiv f)
split-antiinj→not-equiv f-ai f-eqv =
  split-antiinj→not-injective f-ai (Equiv.injective (_ , f-eqv))

is-antiinj→not-equiv
  : {f : A → B}
  → is-antiinjective f
  → ¬ (is-equiv f)
is-antiinj→not-equiv f-ai f-eqv =
  is-antiinj→not-injective f-ai (Equiv.injective (_ , f-eqv))
```
-->

Precomposition by an (split) antinjective function always yields a
(split) antiinjective function.

```agda
split-antiinj-∘r
  : {f : B → C} {g : A → B}
  → split-antiinjective g
  → split-antiinjective (f ∘ g)
split-antiinj-∘r {f = f} g-antiinj .pt = f (g-antiinj .pt)
split-antiinj-∘r {f = f} g-antiinj .x₀ = g-antiinj .x₀
split-antiinj-∘r {f = f} g-antiinj .x₁ = g-antiinj .x₁
split-antiinj-∘r {f = f} g-antiinj .map-to₀ = ap f (g-antiinj .map-to₀)
split-antiinj-∘r {f = f} g-antiinj .map-to₁ = ap f (g-antiinj .map-to₁)
split-antiinj-∘r {f = f} g-antiinj .distinct = g-antiinj .distinct

is-antiinj-∘r
  : {f : B → C} {g : A → B}
  → is-antiinjective g
  → is-antiinjective (f ∘ g)
is-antiinj-∘r {f = f} = ∥-∥-map (split-antiinj-∘r {f = f})
```

If $f : B \to C$ is split antiinjective and $g : A \to B$ can be equipped with a choice
of fibres at the obstruction to injectivity, then $f \circ g$ is also antiinjective.

```agda
split-antiinj+in-image→split-antiinj
  : {f : B → C} {g : A → B}
  → (f-ai : split-antiinjective f)
  → fibre g (f-ai .x₀) → fibre g (f-ai .x₁)
  → split-antiinjective (f ∘ g)
split-antiinj+in-image→split-antiinj {f = f} {g = g} f-ai (a₀ , p₀) (a₁ , p₁) = fg-ai
  where
    fg-ai : split-antiinjective (f ∘ g)
    fg-ai .pt = f-ai .pt
    fg-ai .x₀ = a₀
    fg-ai .x₁ = a₁
    fg-ai .map-to₀ = ap f p₀ ∙ f-ai .map-to₀
    fg-ai .map-to₁ = ap f p₁ ∙ f-ai .map-to₁
    fg-ai .distinct a₀=a₁ = f-ai .distinct (sym p₀ ·· ap g a₀=a₁ ·· p₁)
```

In particular, this means that composing a (split) antiinjection with a (split)
surjection yields a (split) antiinjection.

```agda
split-antiinj+split-surj→split-antiinj
  : {f : B → C} {g : A → B}
  → split-antiinjective f
  → split-surjective g
  → split-antiinjective (f ∘ g)
split-antiinj+split-surj→split-antiinj f-ai g-s =
  split-antiinj+in-image→split-antiinj f-ai (g-s (f-ai .x₀)) (g-s (f-ai .x₁))

is-antiinj+is-surj→is-antiinj
  : {f : B → C} {g : A → B}
  → is-antiinjective f
  → is-surjective g
  → is-antiinjective (f ∘ g)
is-antiinj+is-surj→is-antiinj ∥f-ai∥ g-s = do
  f-ai ← ∥f-ai∥
  fib₀ ← g-s (f-ai .x₀)
  fib₁ ← g-s (f-ai .x₁)
  pure (split-antiinj+in-image→split-antiinj f-ai fib₀ fib₁)
```

```agda
split-antiinj-cancell
  : {f : B → C} {g : A → B}
  → injective f
  → split-antiinjective (f ∘ g)
  → split-antiinjective g
split-antiinj-cancell {f = f} {g = g} f-inj fg-ai .pt =
  g (fg-ai .x₀)
split-antiinj-cancell {f = f} {g = g} f-inj fg-ai .x₀ =
  fg-ai .x₀
split-antiinj-cancell {f = f} {g = g} f-inj fg-ai .x₁ =
  fg-ai .x₁
split-antiinj-cancell {f = f} {g = g} f-inj fg-ai .map-to₀ =
 refl
split-antiinj-cancell {f = f} {g = g} f-inj fg-ai .map-to₁ =
  f-inj (fg-ai .map-to₁ ∙ sym (fg-ai .map-to₀))
split-antiinj-cancell {f = f} {g = g} f-inj fg-ai .distinct =
  fg-ai .distinct

is-antiinj-cancell
  : {f : B → C} {g : A → B}
  → injective f
  → is-antiinjective (f ∘ g)
  → is-antiinjective g
is-antiinj-cancell f-inj = ∥-∥-map (split-antiinj-cancell f-inj)
```
