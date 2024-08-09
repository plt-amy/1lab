---
description: |
  The union of topologies.
---
<!--
```agda
open import Cat.Prelude

open import Data.Power
open import Data.Sum

open import Topology.Instances.Cofree
open import Topology.Base
```
-->
```agda
module Topology.Instances.Union where
```

# Unions of topologies

<!--
```agda
private variable
  ℓ : Level
  X Y : Type ℓ

open is-continuous
open Topology-on
```
-->

```agda
_∪ᵗ_ : Topology-on X → Topology-on X → Topology-on X
S ∪ᵗ T = Cofree-topology (S .Opens ∪ T .Opens)

∪-continuousl
  : {S S' : Topology-on X} {T : Topology-on Y}
  → {f : X → Y}
  → is-continuous f S T
  → is-continuous f (S ∪ᵗ S') T
∪-continuousl {f = f} f-cont .reflect-open {U} U∈T =
  pure (basic (Preimage f U) (pure (inl (f-cont .reflect-open U∈T))))

∪-continuousr
  : {S S' : Topology-on X} {T : Topology-on Y}
  → {f : X → Y}
  → is-continuous f S' T
  → is-continuous f (S ∪ᵗ S') T
∪-continuousr {f = f} f-cont .reflect-open {U} U∈T =
  pure (basic (Preimage f U) (pure (inr (f-cont .reflect-open U∈T))))

∪-continuous
  : ∀ {S : Topology-on X} {T T' : Topology-on Y}
  → {f : X → Y}
  → is-continuous f S T
  → is-continuous f S T'
  → is-continuous f S (T ∪ᵗ T')
∪-continuous T-cont T'-cont =
  cofree-continuous λ U → rec! λ where
    (inl U∈T) → T-cont .reflect-open U∈T
    (inr U∈T') → T'-cont .reflect-open U∈T'

```

```agda
⋃ᵗ : ∀ {κ} {I : Type κ} → (I → Topology-on X) → Topology-on X
⋃ᵗ Tᵢ = Cofree-topology (⋃ (λ i → Tᵢ i .Opens))

⋃-continuous
  : ∀ {κ} {I : Type κ}
  → {Sᵢ : I → Topology-on X} {T : Topology-on Y}
  → {f : X → Y}
  → (i : I) → is-continuous f (Sᵢ i) T
  → is-continuous f (⋃ᵗ Sᵢ) T
⋃-continuous {f = f} i f-cont .reflect-open {U} U∈T =
  pure (basic (Preimage f U) (pure (i , f-cont .reflect-open U∈T)))

⋃-universal
  : ∀ {κ} {I : Type κ}
  → {S : Topology-on X} {Tᵢ : I → Topology-on Y}
  → {f : X → Y}
  → (∀ i → is-continuous f S (Tᵢ i))
  → is-continuous f S (⋃ᵗ Tᵢ)
⋃-universal f-cont =
  cofree-continuous λ U → rec! λ i U∈Tᵢ →
    f-cont i .reflect-open U∈Tᵢ
```
