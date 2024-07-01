---
description: |
  Antisurjective functions.
---
<!--
```agda
open import 1Lab.Function.Surjection
open import 1Lab.Function.Embedding
open import 1Lab.HLevel.Universe
open import 1Lab.HIT.Truncation
open import 1Lab.HLevel.Closure
open import 1Lab.Type.Sigma
open import 1Lab.Inductive
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

open import Meta.Idiom
open import Meta.Bind
```
-->
```agda
module 1Lab.Function.Antisurjection where
```

<!--
```
private variable
  ℓ ℓ₁ : Level
  A B C : Type ℓ
  w x : A
```
-->

## Antisurjective functions {defines="antisurjective split-antisurjective"}

A function is **antisurjective** if there merely exists some $b : B$
with an empty fibre. This is constructively stronger than being
non-surjective, which states that it is not the case that all fibres
are (merely) inhabited.

```agda
is-antisurjective : (A → B) → Type _
is-antisurjective {B = B} f = ∃[ b ∈ B ] (¬ (fibre f b))
```

Likewise, a function is **split antisurjective** if there is some
$b : B$ with an empty fibre. Note that this is a structure on a function,
not a property, as there may be many ways a function fails to be surjective!

```agda
split-antisurjective : (A → B) → Type _
split-antisurjective {B = B} f = Σ[ b ∈ B ] (¬ (fibre f b))
```

As the name suggests, antisurjective functions are not surjective.

```agda
split-antisurj→not-surjective
  : {f : A → B}
  → split-antisurjective f
  → ¬ (is-surjective f)
split-antisurj→not-surjective (b , ¬fib) f-s =
  rec! (λ a p → ¬fib (a , p)) (f-s b)

is-antisurj→not-surjective
  : {f : A → B}
  → is-antisurjective f
  → ¬ (is-surjective f)
is-antisurj→not-surjective f-as =
  rec! (λ b ¬fib → split-antisurj→not-surjective (b , ¬fib)) f-as
```

<!--
```agda
is-antisurj→not-equiv
  : {f : A → B}
  → is-antisurjective f
  → ¬ (is-equiv f)
is-antisurj→not-equiv f-as f-eqv =
  is-antisurj→not-surjective f-as (λ b → inc (f-eqv .is-eqv b .centre))

split-antisurj→not-equiv
  : {f : A → B}
  → split-antisurjective f
  → ¬ (is-equiv f)
split-antisurj→not-equiv f-as = is-antisurj→not-equiv (inc f-as)
```
-->

If $f$ is antisurjective and $g$ is an arbitrary function, then $f \circ g$
is also antisurjective.

```agda
split-antisurj-∘l
  : {f : B → C} {g : A → B}
  → split-antisurjective f
  → split-antisurjective (f ∘ g)
split-antisurj-∘l {g = g} (c , ¬fib) = c , ¬fib ∘ Σ-map g (λ p → p)

is-antisurj-∘l
  : {f : B → C} {g : A → B}
  → is-antisurjective f
  → is-antisurjective (f ∘ g)
is-antisurj-∘l {f = f} {g = g} = ∥-∥-map split-antisurj-∘l
```

If $f$ is injective and $g$ is antisurjective, then $f \circ g$ is
also antisurjective.

```agda
inj+split-antisurj→split-antisurj
  : {f : B → C} {g : A → B}
  → injective f
  → split-antisurjective g
  → split-antisurjective (f ∘ g)
inj+split-antisurj→split-antisurj {f = f} f-inj (b , ¬fib) =
  f b , ¬fib ∘ Σ-map₂ f-inj

inj+is-antisurj→is-antisurj
  : {f : B → C} {g : A → B}
  → injective f
  → is-antisurjective g
  → is-antisurjective (f ∘ g)
inj+is-antisurj→is-antisurj f-inj =
  ∥-∥-map (inj+split-antisurj→split-antisurj f-inj)
```

```agda
split-antisurj-cancelr
  : {f : B → C} {g : A → B}
  → is-surjective g
  → split-antisurjective (f ∘ g)
  → split-antisurjective f
split-antisurj-cancelr {f = f} {g = g} surj (c , ¬fib) =
  c , rec! λ b p → rec! (λ a q → ¬fib (a , ap f q ∙ p)) (surj b)

is-antisurj-cancelr
  : {f : B → C} {g : A → B}
  → is-surjective g
  → is-antisurjective (f ∘ g)
  → is-antisurjective f
is-antisurj-cancelr surj = ∥-∥-map (split-antisurj-cancelr surj) 
```
