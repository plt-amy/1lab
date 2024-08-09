---
description: |
  Basic facts about the category of topological spaces.
---
<!--
```agda
open import Cat.Functor.Morphism
open import Cat.Displayed.Total
open import Cat.Prelude

open import Data.Set.Surjection
open import Data.Power

open import Topology.Instances.Codiscrete
open import Topology.Instances.Discrete
open import Topology.Base
```
-->
```agda
module Topology.Cat where
```

<!--
```agda
open Total-hom
```
-->

# Basic facts about the category of topological spaces

This file collects a bunch of basic facts about the category of
topological spaces into a single place.

## Morphisms

If $f : X \to Y$ is an injective [[continuous function]], then $f$
is [[monic]].

```agda
continuous-injection→monic
  : ∀ {ℓ} {X Y : Topological-space ℓ}
  → (f : Topologies.Hom X Y)
  → injective (f .hom)
  → Topologies.is-monic f
```

To see this, note that the forgetful functor $U : \Top \to \Sets$ is
[[faithful]], and recall that faithful functors reflect monos.

```agda
continuous-injection→monic f f-inj =
  faithful→reflects-mono Topologies↪Sets Topologies↪Sets-faithful $ λ {Z} →
  injective→monic (hlevel 2) f-inj {Z}
```

Moreover, continuous injections are *precisely* the monos in $\Top$.

```agda
monic→continuous-injection
  : ∀ {ℓ} {X Y : Topological-space ℓ}
  → (f : Topologies.Hom X Y)
  → Topologies.is-monic f
  → injective (f .hom)
```

This follows via some general abstract nonsense: the forgetful
functor $U : \Top \to \Sets$ is [[right adjoint]] to the functor
that sends every set $X$ to the [[discrete topology]] on $X$, and
[[right adjoints preserve monos]].

```agda
monic→continuous-injection f f-monic =
  monic→injective (hlevel 2) $ λ {C} →
  right-adjoint→preserves-monos
    Topologies↪Sets
    Discrete-topologies⊣Topologies↪Sets
    f-monic {C}
```

Similarly characterise the [[epis]] in $\Top$ as continuous surjections.

```agda
continuous-surjection→epic
  : ∀ {ℓ} {X Y : Topological-space ℓ}
  → (f : Topologies.Hom X Y)
  → is-surjective (f .hom)
  → Topologies.is-epic f

epic→continuous-surjection
  : ∀ {ℓ} {X Y : Topological-space ℓ}
  → (f : Topologies.Hom X Y)
  → Topologies.is-epic f
  → is-surjective (f .hom)
```

The proof is essentially dual to the one for monos: faithful functors
reflect epis, and the forgetful functor $U : \Top \to \Sets$ is [[left adjoint]]
to the [[codiscrete topology]] functor.

```agda
continuous-surjection→epic {X = X} {Y = Y} f f-surj =
  faithful→reflects-epi Topologies↪Sets Topologies↪Sets-faithful $ λ {Z} →
  surjective→epi (el! ⌞ X ⌟) (el! ⌞ Y ⌟) (f .hom) f-surj {Z}

epic→continuous-surjection {X = X} {Y = Y} f f-epic =
  epi→surjective (X .fst) (Y .fst) (f .hom) $ λ {C} →
  left-adjoint→preserves-epis
    Topologies↪Sets
    Topologies↪Sets⊣Codiscrete-topologies
    f-epic {C}
```
