---
description: |
  Products of topological spaces.
---
<!--
```agda
open import Cat.Diagram.Product.Indexed
open import Cat.Displayed.Total
open import Cat.Diagram.Product
open import Cat.Prelude

open import Topology.Instances.Induced
open import Topology.Instances.Union
open import Topology.Base
```
-->
```agda
module Topology.Instances.Product where
```

# Products of topological spaces

<!--
```agda
private variable
  ℓ ℓ' : Level
  X Y : Type ℓ
  S T : Topology-on X

open Topology-on
open Total-hom
open is-continuous
open Product
open Indexed-product
```
-->

```agda
_×ᵗ_
  : ∀ {X : Type ℓ} {Y : Type ℓ'}
  → Topology-on X → Topology-on Y
  → Topology-on (X × Y)
S ×ᵗ T = Induced fst S ∪ᵗ Induced snd T
```

```agda
fst-continuous : is-continuous fst (S ×ᵗ T) S
fst-continuous {T = T} =
  ∪-continuousl {S' = Induced snd T} induced-continuous

snd-continuous : is-continuous snd (S ×ᵗ T) T
snd-continuous {S = S} =
  ∪-continuousr {S = Induced fst S} induced-continuous
```

```agda
Topologies-product
  : ∀ (X Y : Topological-space ℓ)
  → Product (Topologies ℓ) X Y
Topologies-product X Y .apex =
  el! (⌞ X ⌟ × ⌞ Y ⌟) , X .snd ×ᵗ Y .snd
Topologies-product X Y .π₁ .hom = fst
Topologies-product X Y .π₁ .preserves = fst-continuous {T = Y .snd}
Topologies-product X Y .π₂ .hom = snd
Topologies-product X Y .π₂ .preserves = snd-continuous {S = X .snd}
Topologies-product X Y .has-is-product .is-product.⟨_,_⟩ f g .hom x = f # x , g # x
Topologies-product X Y .has-is-product .is-product.⟨_,_⟩ f g .preserves =
  ∪-continuous {T = Induced fst (X .snd)} {T' = Induced snd (Y .snd)}
    (induced-universal (f .preserves))
    (induced-universal (g .preserves))
Topologies-product X Y .has-is-product .is-product.π₁∘⟨⟩ = trivial!
Topologies-product X Y .has-is-product .is-product.π₂∘⟨⟩ = trivial!
Topologies-product X Y .has-is-product .is-product.unique p q =
  ext λ x → p #ₚ x , q #ₚ x
```

# Indexed products

```agda
Πᵗ
  : ∀ {κ} {I : Type κ} {Xᵢ : I → Type ℓ}
  → (∀ i → Topology-on (Xᵢ i)) → Topology-on (∀ i → Xᵢ i)
Πᵗ Tᵢ = ⋃ᵗ λ i → Induced (_$ i) (Tᵢ i)

proj-continuous
  : ∀ {κ} {I : Type κ} {Xᵢ : I → Type ℓ}
  → (Tᵢ : ∀ i → Topology-on (Xᵢ i))
  → ∀ (i : I) → is-continuous (_$ i) (Πᵗ Tᵢ) (Tᵢ i)
proj-continuous Tᵢ i =
  ⋃-continuous {Sᵢ = λ i → Induced (_$ i) (Tᵢ i)} i induced-continuous

Topologies-indexed-product
  : ∀ {I : Type ℓ}
  → (Xᵢ : I → Topological-space ℓ)
  → Indexed-product (Topologies ℓ) Xᵢ
Topologies-indexed-product {I = I} Xᵢ .ΠF =
  el! (∀ (i : I) → ⌞ Xᵢ i ⌟) , Πᵗ (λ i → Xᵢ i .snd)
Topologies-indexed-product {I = I} Xᵢ .π i .hom f = f i
Topologies-indexed-product {I = I} Xᵢ .π i .preserves =
  proj-continuous (λ i → Xᵢ i .snd) i
Topologies-indexed-product {I = I} Xᵢ .has-is-ip .is-indexed-product.tuple fᵢ .hom y i = fᵢ i # y
Topologies-indexed-product {I = I} Xᵢ .has-is-ip .is-indexed-product.tuple fᵢ .preserves =
  ⋃-universal λ i → induced-universal (fᵢ i .preserves)
Topologies-indexed-product {I = I} Xᵢ .has-is-ip .is-indexed-product.commute =
  trivial!
Topologies-indexed-product {I = I} Xᵢ .has-is-ip .is-indexed-product.unique fᵢ p =
  ext (λ y i → p i #ₚ y)
```
