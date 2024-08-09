---
description: |
  The basic theory of topological spaces.
---
<!--
```agda
open import Cat.Displayed.Univalence.Thin
open import Cat.Functor.Properties
open import Cat.Prelude

open import Data.Set.Surjection
open import Data.Sum
open import Data.Power

import Cat.Reasoning

open import 1Lab.Reflection hiding (absurd; [_])
```
-->
```agda
module Topology.Base where
```

# Topological spaces {defines="topology topological-space open-set"}

A **topology** on a type $X$ consists of a subset $\mathcal{O}$ of the [[power set]]
of $X$ that is closed under finite intersections and infinitary unions.
The elements of $\mathcal{O}$ are known as **open sets**,
and a set equipped with a topology is called a **topological space**

Topological spaces allow us to study geometric ideas like continuity,
convergence, etc. within a relatively abstract framework, and are a
pillar of modern classical mathematics. However, they tend to be rather
ill-behaved constructively, and provide a rich source of constructive
taboos.

With that small bit of motivation out of the way, we can proceed to
give a formal definition of a topology.

```agda
record Topology-on {ℓ} (X : Type ℓ) : Type ℓ where
  no-eta-equality
  field
    Opens : ℙ (ℙ X)
```

We ensure that the set of opens is closed under finite intersections
by requiring that the entirety of $X$ is open, along with closure
under binary intersections.

```agda
    maximal-open : maximal ∈ Opens
    ∩-open : ∀ {U V : ℙ X} → U ∈ Opens → V ∈ Opens → (U ∩ V) ∈ Opens
```

Instead of closure under infinitary unions $\bigcup_{i : I} U_i$, we
require that the set of opens is closed under unions of subsets. This
allows us to avoid a bump in universe level, as we do not need to quantify
over any types!

```agda
    ⋃ˢ-open : ∀ (S : ℙ (ℙ X)) → S ⊆ Opens → ⋃ˢ S ∈ Opens
```

<!--
```agda
  is-open : ℙ X → Type
  is-open X = ∣ Opens X ∣

  open-ext
    : ∀ {U V : ℙ X}
    → (∀ (x : X) → x ∈ U → x ∈ V)
    → (∀ (x : X) → x ∈ V → x ∈ U)
    → U ∈ Opens
    → V ∈ Opens
  open-ext to from U-open =
    subst is-open (ext λ x → Ω-ua (to x) (from x)) U-open
```
-->

Next, we will show that open sets are closed under indexed unions.
Let $U_i$ be a family of open sets indexed by an arbitrary type $I$.
Note that if $U$ is in the fibre of $U_i$, then $U$ is open. Moreover,
the set of fibres of $U_i$ forms a subset of the powerset, so its
union is also open. Finally, the union of the fibres of $U_i$ is equal
to the union of $U_i$, so $\bigcup_{I} U_i$ is open.

```agda
  fibre-open
    : ∀ {κ} {I : Type κ}
    → (Uᵢ : I → ℙ X) → (∀ i → Uᵢ i ∈ Opens)
    → ∀ (U : ℙ X) → □ (fibre Uᵢ U) → U ∈ Opens
  fibre-open Uᵢ Uᵢ-open U = rec! λ i Uᵢ=U →
    subst is-open Uᵢ=U (Uᵢ-open i)

  ⋃-open
    : ∀ {κ} {I : Type κ}
    → (Uᵢ : I → ℙ X) → (∀ i → Uᵢ i ∈ Opens)
    → ⋃ Uᵢ ∈ Opens
  ⋃-open {I = I} Uᵢ Uᵢ-open =
    subst is-open
      (⋃-fibre Uᵢ)
      (⋃ˢ-open (λ U → elΩ (fibre Uᵢ U)) (fibre-open Uᵢ Uᵢ-open))
```

As an easy corollary, the empty set is also open.

```agda
  minimal-open : minimal ∈ Opens
  minimal-open =
    subst is-open
      (⋃-minimal (λ _ → maximal))
      (⋃-open (λ _ → maximal) (λ _ → maximal-open))
```

We pause to note that paths between topologies are relatively easy to
characterise: if two topologies on $X$ have the same sets of opens, then
the two topologies are equal!

```agda
Topology-on-path
  : ∀ {ℓ} {X : Type ℓ}
  → {S T : Topology-on X}
  → (Topology-on.Opens S ⊆ Topology-on.Opens T)
  → (Topology-on.Opens T ⊆ Topology-on.Opens S)
  → S ≡ T
```

<details>
<summary>The proof is somewhat tedious, but the key observation is that
the sets of opens are the only non-propositional piece of data in a
topology.
</summary>
```agda
Topology-on-path {X = X} {S = S} {T = T} to from = path where
  module S = Topology-on S
  module T = Topology-on T


  opens : S.Opens ≡ T.Opens
  opens = funext λ U → Ω-ua (to U) (from U)

  path : S ≡ T
  path i .Topology-on.Opens = opens i
  path i .Topology-on.maximal-open =
    is-prop→pathp (λ i → opens i maximal .is-tr)
      S.maximal-open
      T.maximal-open i
  path i .Topology-on.∩-open {U} {V} =
    is-prop→pathp
      (λ i →
        Π-is-hlevel² {A = U ∈ opens i} {B = λ _ → V ∈ opens i} 1 λ _ _ →
        opens i (U ∩ V) .is-tr)
      S.∩-open
      T.∩-open i
  path i .Topology-on.⋃ˢ-open S =
    is-prop→pathp
      (λ i →
        Π-is-hlevel {A = S ⊆ opens i} 1 λ _ →
        opens i (⋃ˢ S) .is-tr)
      (S.⋃ˢ-open S)
      (T.⋃ˢ-open S) i
```
</details>


# Continuous functions {defines="continuous-function"}

A function $f : X \to Y$ between two topological spaces is **continuous**
if it reflects open sets. Explicitly, $f$ is continuous if for every
open set $U : \power{Y}$, the [[preimage]] $f^{-1}(U) : \power{X}$ is open
in $X$.

```agda
record is-continuous
  {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'}
  (f : X → Y)
  (X-top : Topology-on X) (Y-top : Topology-on Y)
  : Type ℓ'
  where
  no-eta-equality
  private
    module X = Topology-on X-top
    module Y = Topology-on Y-top
  field
    reflect-open : ∀ {U : ℙ Y} → U ∈ Y.Opens → Preimage f U ∈ X.Opens
```

<!--
```agda
open is-continuous

unquoteDecl H-Level-is-continuous = declare-record-hlevel 1 H-Level-is-continuous (quote is-continuous)
```
-->

# The category of topological spaces

Topological spaces and continuous maps form a category, which we will
denote $\Top$.

```agda
Topology-structure : ∀ ℓ → Thin-structure ℓ (Topology-on {ℓ})
Topology-structure ℓ .is-hom f X-top Y-top =
  el! (is-continuous f X-top Y-top)
Topology-structure ℓ .id-is-hom .reflect-open U-open = U-open
Topology-structure ℓ .∘-is-hom f g f-cont g-cont .reflect-open =
  g-cont .reflect-open ⊙ f-cont .reflect-open
Topology-structure ℓ .id-hom-unique p q =
  Topology-on-path (λ U → q .reflect-open) (λ U → p .reflect-open)

Topologies : ∀ ℓ → Precategory (lsuc ℓ) (ℓ ⊔ ℓ)
Topologies ℓ = Structured-objects (Topology-structure ℓ)
```

<!--
```agda
module Topologies {ℓ} = Cat.Reasoning (Topologies ℓ)

Topological-space : ∀ ℓ → Type (lsuc ℓ)
Topological-space ℓ = Topologies.Ob {ℓ}
```
-->

As $\Top$ is a category of [[thin structures]], it comes equipped with
a forgetful functor into sets.

```agda
Topologies↪Sets : ∀ {ℓ} → Functor (Topologies ℓ) (Sets ℓ)
Topologies↪Sets = Forget-structure (Topology-structure _)

Topologies↪Sets-faithful : ∀ {ℓ} → is-faithful (Topologies↪Sets {ℓ})
Topologies↪Sets-faithful = Structured-hom-path (Topology-structure _)
```

Additionally, $\Top$ is a [[univalent category]].

```agda
Topologies-is-category : ∀ {ℓ} → is-category (Topologies ℓ)
Topologies-is-category = Structured-objects-is-category (Topology-structure _)
```

<!--
```agda
instance
  Extensional-Topology-hom
    : ∀ {ℓ} {X Y : Topological-space ℓ} {ℓr}
    → ⦃ _ : Extensional (⌞ X ⌟ → ⌞ Y ⌟) ℓr ⦄
    → Extensional (Topologies.Hom X Y) ℓr
  Extensional-Topology-hom ⦃ e ⦄ =
    injection→extensional! (λ p → total-hom-path _ p prop!) e
```
-->

# As a displayed category

```agda
Topologies-on : ∀ ℓ → Displayed (Sets ℓ) ℓ ℓ
Topologies-on ℓ = Thin-structure-over (Topology-structure ℓ)
```
