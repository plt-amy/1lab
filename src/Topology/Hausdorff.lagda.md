---
description: |
  Hausdorff spaces.
---
<!--
```agda
open import Cat.Prelude

open import Topology.Base
```
-->
```agda
module Topology.Hausdorff where
```

```agda
record is-hausdorff {o ℓ} (X : Topological-space o ℓ) : Type (o ⊔ ℓ) where
  open Topological-space X
  field
    cool
      : ∀ (x y : ⌞ X ⌟)
      → (∀ (U V : ⌞ X ⌟ → Ω) → is-neighborhood x U → is-neighborhood y V → ∃[ z ∈ ⌞ X ⌟ ] (z ∈ U × z ∈ V))
      → x ≡ y
```
