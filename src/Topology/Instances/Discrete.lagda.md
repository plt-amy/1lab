---
description: |
  The discrete topology on a type.
---
<!--
```agda
open import Cat.Displayed.Total
open import Cat.Functor.Adjoint
open import Cat.Prelude

open import Data.Power

open import Topology.Base
```
-->

```agda
module Topology.Instances.Discrete where
```

# The discrete topology

:::{.definition #discrete-topology}
The **discrete topology** on a type $X$ is the topology where every
subset $U : \power{\power{X}}$ is open.
:::


<!--
```agda
private variable
  ℓ ℓ' : Level
  X Y : Type ℓ

open Free-object
open is-continuous
open Topology-on
open Total-hom
```
-->

```agda
Discrete-topology : (X : Type ℓ) → Topology-on X
Discrete-topology X .Opens = maximal
Discrete-topology X .maximal-open = tt
Discrete-topology X .∩-open _ _ = tt
Discrete-topology X .⋃ˢ-open _ _ = tt
```

Note that every function out of the discrete topology on $X$ is continuous.

```agda
discrete-continuous
  : ∀ {T : Topology-on Y}
  → {f : X → Y}
  → is-continuous f (Discrete-topology X) T
discrete-continuous .reflect-open _ = tt
```

This means that discrete topologies are [[free objects]] relative to
the forgetful functor $\Top \to \Sets$.

```agda
Discrete-topology-free : ∀ (X : Set ℓ) → Free-object Topologies↪Sets X
Discrete-topology-free X .free = X , Discrete-topology ⌞ X ⌟
Discrete-topology-free X .unit x = x
Discrete-topology-free X .fold f .hom = f
Discrete-topology-free X .fold f .preserves = discrete-continuous
Discrete-topology-free X .commute = refl
Discrete-topology-free X .unique g p = ext (apply p)
```

We can assemble these free objects together to form a left adjoint
to the aforementioned forgetful functor.

```agda
Discrete-topologies : Functor (Sets ℓ) (Topologies ℓ)
Discrete-topologies = free-objects→functor Discrete-topology-free

Discrete-topologies⊣Topologies↪Sets : Discrete-topologies {ℓ} ⊣ Topologies↪Sets
Discrete-topologies⊣Topologies↪Sets = free-objects→left-adjoint Discrete-topology-free
```
