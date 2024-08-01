---
description: |
  The category of graphs with commutativity conditions.
---
<!--
```agda
open import Cat.Instances.StrictCat
open import Cat.Functor.Properties
open import Cat.Instances.Graphs
open import Cat.Instances.Free
open import Cat.Functor.Base
open import Cat.Prelude
open import Cat.Strict

import Cat.Functor.Reasoning
import Cat.Reasoning
```
-->
```agda
module Cat.Instances.CommGraphs where
```

# Graphs with commutativity conditions

Recall that every [[graph]] $G$ gives rise to a [[free category]]
$\rm{Path}(G)$. Though useful, this construction is rather limiting;
if we want to construct (strict) categories via combinatorial methods,
then we really do need a way to add non-trivial equalities. In other words,
we need to be able to construct categories freely from a set of generators
*and* relations! This leads us to the following notion:

:::{.definition #graph-with-commutativity-conditions alias="commutative graph"}
A **graph with commutativity conditions** or **commutative graph**
consists of a [[graph]] $G$ along with a set of distinguished paths in $G$,
referred to as **commutativities**.
:::


```agda
record Comm-graph (o ℓ : Level) : Type (lsuc o ⊔ lsuc ℓ) where
  no-eta-equality
  field
    graph : Graph o ℓ

  open Graph graph public

  field
    Comm : ∀ {x y} → Path-in graph x y → Path-in graph x y → Ω
```

<!--
```agda
private variable
  o ℓ o' ℓ' : Level
  G H K : Comm-graph o ℓ

open Comm-graph
open hlevel-projection

instance
  Underlying-Comm-graph : Underlying (Comm-graph o ℓ)
  Underlying-Comm-graph = record { ⌞_⌟ = Vertex }
```
-->

:::{.definition #commutative-graph-homomorphism}
A **homomorphism of commutative graphs** $f : G \to H$ is a [[graph homomorphism]]
that takes a commutative pair $p, q : G^*$ in $G$ to a commutative pair
$f(p), g(p) : H^*$ in $H$.
:::


```agda
record Comm-graph-hom (G : Comm-graph o ℓ) (H : Comm-graph o' ℓ') : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ') where
  no-eta-equality
  field
    hom : Graph-hom (G .graph) (H .graph)
    pres-comm
      : ∀ {x y} {p q : Path-in (G .graph) x y}
      → ∣ G .Comm p q ∣
      → ∣ H .Comm (path-map hom p) (path-map hom q) ∣
  open Graph-hom hom public
```

<!--
```agda
open Comm-graph-hom

unquoteDecl H-Level-Comm-graph-hom = declare-record-hlevel 2 H-Level-Comm-graph-hom (quote Comm-graph-hom)

instance
  Funlike-Comm-graph-hom : Funlike (Comm-graph-hom G H) ⌞ G ⌟ λ _ → ⌞ H ⌟
  Funlike-Comm-graph-hom .Funlike._#_ = vertex

Comm-graph-hom-pathp
  : {G : I → Comm-graph o ℓ} {H : I → Comm-graph o' ℓ'}
  → {f : Comm-graph-hom (G i0) (H i0)} {g : Comm-graph-hom (G i1) (H i1)}
  → (p0 : ∀ (x : ∀ i → G i .Vertex)
          → PathP (λ i → H i .Vertex)
              (f .vertex (x i0)) (g .vertex (x i1)))
  → (p1 : ∀ {x y : ∀ i → G i .Vertex}
          → (e : ∀ i → G i .Edge (x i) (y i))
          → PathP (λ i → H i .Edge (p0 x i) (p0 y i))
              (f .edge (e i0)) (g .edge (e i1)))
  → PathP (λ i → Comm-graph-hom (G i) (H i)) f g
Comm-graph-hom-pathp {G = G} {H = H} {f = f} {g = g} p0 p1 = comm-path where
  hom-path : PathP (λ i → Graph-hom (G i .graph) (H i .graph)) (f .hom) (g .hom)
  hom-path =
    Graph-hom-pathp {G = λ i → G i .graph} {H = λ i → H i .graph}
      {f = f .hom} {g .hom}
      p0 p1

  comm-path : PathP (λ i → Comm-graph-hom (G i) (H i)) f g
  comm-path i .hom = hom-path i
  comm-path i .pres-comm {x} {y} {p} {q} =
    is-prop→pathp (λ i →
        Π-is-hlevel {A = G i .Vertex} 1 λ x →
        Π-is-hlevel {A = G i .Vertex} 1 λ y →
        Π-is-hlevel {A = Path-in (G i .graph) x y} 1 λ p →
        Π-is-hlevel {A = Path-in (G i .graph) x y} 1 λ q →
        Π-is-hlevel {A = ∣ G i .Comm p q ∣} 1 λ _ →
        H i .Comm (path-map (hom-path i) p) (path-map (hom-path i) q) .is-tr)
      (λ _ _ _ _ → f .pres-comm)
      (λ _ _ _ _ → g .pres-comm)
      i x y p q

Comm-graph-hom-path
  : {f g : Comm-graph-hom G H}
  → (p0 : ∀ x → f .vertex x ≡ g .vertex x)
  → (p1 : ∀ {x y} → (e : G .Edge x y) → PathP (λ i → H .Edge (p0 x i) (p0 y i)) (f .edge e) (g .edge e))
  → f ≡ g
Comm-graph-hom-path {G = G} {H = H} p0 p1 =
  Comm-graph-hom-pathp {G = λ _ → G} {H = λ _ → H}
    (λ x i → p0 (x i) i)
    (λ e i → p1 (e i) i)
```
-->

We can organize commutative graphs and commutative graph homomorphisms
into a category $\CommGraphs$.

```agda
Comm-graphs : ∀ o ℓ → Precategory (lsuc o ⊔ lsuc ℓ) (o ⊔ ℓ)
Comm-graphs o ℓ .Precategory.Ob = Comm-graph o ℓ
Comm-graphs o ℓ .Precategory.Hom = Comm-graph-hom
Comm-graphs o ℓ .Precategory.Hom-set _ _ = hlevel 2
Comm-graphs o ℓ .Precategory.id {G} .hom = Graphs.id
Comm-graphs o ℓ .Precategory.id {G} .pres-comm p~q =
  subst₂ (λ p q → ∣ G .Comm p q ∣)
    (sym (path-map-id _))
    (sym (path-map-id _))
    p~q
Comm-graphs o ℓ .Precategory._∘_ f g .hom = (f .hom) Graphs.∘ (g .hom)
Comm-graphs o ℓ .Precategory._∘_ {G} {H} {K} f g .pres-comm p~q =
  subst₂ (λ p q → ∣ K .Comm p q ∣)
    (sym (path-map-∘ _))
    (sym (path-map-∘ _))
    (f .pres-comm (g .pres-comm p~q))
Comm-graphs o ℓ .Precategory.idr _ =
  Comm-graph-hom-path (λ _ → refl) (λ _ → refl)
Comm-graphs o ℓ .Precategory.idl _ =
  Comm-graph-hom-path (λ _ → refl) (λ _ → refl)
Comm-graphs o ℓ .Precategory.assoc _ _ _ =
  Comm-graph-hom-path (λ _ → refl) (λ _ → refl)
```

<!--
```agda
open Functor
```
-->

Moreover, there is a faithful functor from the [[category of strict categories]]
to the category of commutative graphs.

```agda
Strict-cats↪Comm-graphs : Functor (Strict-cats o ℓ) (Comm-graphs o ℓ)
```

The action on objects takes a strict category $\cC$ to its underlying
graph, and adds a commutativity condition between $p, q : \cC^*$ whenever
$p$ and $q$ are equal as morphisms in $\cC$.

```agda
Strict-cats↪Comm-graphs .F₀ C .graph =
  Strict-cats↪Graphs .F₀ C
Strict-cats↪Comm-graphs .F₀ C .Comm p q =
  elΩ (path-reduce C p ≡ path-reduce C q)
```

Functoriality follows from the fact that functors take equal paths in $\cC$
to equal paths in $\cD$.

```agda
Strict-cats↪Comm-graphs .F₁ F .hom =
  Strict-cats↪Graphs .F₁ F
Strict-cats↪Comm-graphs .F₁ F .pres-comm {p = p} {q = q} =
  □-map λ p~q → path-reduce-map F p ∙ ap (F .F₁) p~q ∙ sym (path-reduce-map F q)
Strict-cats↪Comm-graphs .F-id =
  Comm-graph-hom-path (λ _ → refl) (λ _ → refl)
Strict-cats↪Comm-graphs .F-∘ F G =
  Comm-graph-hom-path (λ _ → refl) (λ _ → refl)
```
