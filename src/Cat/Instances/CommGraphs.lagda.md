---
description: |
  The category of graphs with commutativity conditions.
---
<!--
```agda
open import 1Lab.Reflection.Induction

open import Cat.Functor.Adjoint.Reflective
open import Cat.Instances.StrictCat
open import Cat.Functor.Properties
open import Cat.Instances.Graphs
open import Cat.Functor.Adjoint
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

:::{.definition #graph-with-commutativity-conditions alias="commutative-graph"}
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
  □-map λ p~q → path-reduce-natural F p ∙ ap (F .F₁) p~q ∙ sym (path-reduce-natural F q)
Strict-cats↪Comm-graphs .F-id =
  Comm-graph-hom-path (λ _ → refl) (λ _ → refl)
Strict-cats↪Comm-graphs .F-∘ F G =
  Comm-graph-hom-path (λ _ → refl) (λ _ → refl)
```

This functor is clearly [[faithful]]; the proof is essentially just
relabeling data.

```agda
Strict-cats↪Comm-graphs-faithful
  : is-faithful (Strict-cats↪Comm-graphs {o} {ℓ})
Strict-cats↪Comm-graphs-faithful p =
  Functor-path (λ x i → p i .vertex x) (λ f i → p i .edge f)
```

More surprisingly this functor is also [[full]]!


```agda
Strict-cats↪Comm-graphs-full
  : is-full (Strict-cats↪Comm-graphs {o} {ℓ})
```

To see why, suppose that $f : \cC \to \cD$ is a commutative
graph homomorphism between strict categories. By definition, $f$
already contains the data of a functor; the tricky part is showing
the properties.

```agda
Strict-cats↪Comm-graphs-full {x = C} {y = D} f =
  pure (functor , Comm-graph-hom-path (λ _ → refl) (λ _ → refl))
  where
    module C = Precategory (C .fst)
    module D = Precategory (D .fst)

    functor : Functor (C .fst) (D .fst)
    functor .F₀ = f .vertex
    functor .F₁ = f .edge
```

The trick is that commutative graph homomorphisms between categories cannot observe
the intensional structure of paths, as they must preserve all commutativities.
In particular, $f$ will preserve the commutativity in $\cC$ between the singleton path
containing $id$ is equal to the empty path; so $f(\id) = \id$

```agda
    functor .F-id =
      f .edge C.id          ≡˘⟨ D.idl _ ⟩
      D.id D.∘ f .edge C.id ≡⟨ □-out! (f .pres-comm {p = cons C.id nil} {q = nil} (inc (C.idl _))) ⟩
      D.id                  ∎
```

Additionally, $f$ will preserve the commutativity between the singleton
path $g \circ h$ and the path $h, g$, so $f(g \circ h) = f g \circ f h$.

```agda
    functor .F-∘ g h =
      f .edge (g C.∘ h)                  ≡˘⟨ D.idl _ ⟩
      D.id D.∘ f .edge (g C.∘ h)         ≡˘⟨ □-out! (f .pres-comm {p = cons h (cons g nil)} {q = cons (g C.∘ h) nil} (pure (sym (C.assoc _ _ _)))) ⟩
      (D.id D.∘ f .edge g) D.∘ f .edge h ≡⟨ ap₂ D._∘_ (D.idl _) refl ⟩
      f .edge g D.∘ f .edge h ∎
```


## Categories from generators and relations

<!--
```agda
module _ (G : Comm-graph o ℓ) where
  private module G = Comm-graph G
```
-->

In this section, we will detail how to freely construct a category
from a commutative graph $G$. Intuitvely, this works by freely generating
a category from $G$, and then quotienting by the commutativities.
However, there is a slight subtlety here: the commutativities of $G$
may not respect path concatenation, and may not even form an equivalence
relation!

Luckily, there is an easy (though tedious) solution to this problem:
we can instead quotient by the reflexive-transitive-congruent closure
instead, which we encode in Agda via the following higher-inductive type.

```agda
  data Commutativity
    : ∀ {x y} → Path-in G.graph x y → Path-in G.graph x y
    → Type (o ⊔ ℓ)
    where
    commutative
      : ∀ {x y} {p q : Path-in G.graph x y}
      → ∣ G.Comm p q ∣
      → Commutativity p q
    reflexive
      : ∀ {x y} {p : Path-in G.graph x y}
      → Commutativity p p
    symmetric
      : ∀ {x y} {p q : Path-in G.graph x y}
      → Commutativity q p
      → Commutativity p q
    transitive
      : ∀ {x y} {p q r : Path-in G.graph x y}
      → Commutativity p q → Commutativity q r
      → Commutativity p r
    congruent
      : ∀ {x y z} {p q : Path-in G.graph x y} {r s : Path-in G.graph y z}
      → Commutativity p q → Commutativity r s
      → Commutativity (p ++ r) (q ++ s)
    trunc : ∀ {x y} {p q : Path-in G.graph x y} → is-prop (Commutativity p q)
  ```

<!--
```agda
  unquoteDecl Commutativity-elim-prop = make-elim-n 1 Commutativity-elim-prop (quote Commutativity)
```
-->

The resulting category is not too difficult to construct:
the objects are the vertices of $G$, and the morphisms are paths in
$G$ quotiented by our closure from before.

```agda
  Comm-path-category : Precategory o (o ⊔ ℓ)
  Comm-path-category .Precategory.Ob = G.Vertex
  Comm-path-category .Precategory.Hom x y =
    Path-in G.graph x y / Commutativity
  Comm-path-category .Precategory.Hom-set _ _ = hlevel 2
  Comm-path-category .Precategory.id = inc nil
  Comm-path-category .Precategory._∘_ =
    Quot-op₂
      (λ _ → reflexive) (λ _ → reflexive)
      (flip _++_)
      (λ p q r s p~q r~s → congruent r~s p~q)
  Comm-path-category .Precategory.idr =
    elim! λ p → refl
  Comm-path-category .Precategory.idl =
    elim! λ p → ap inc (++-idr p)
  Comm-path-category .Precategory.assoc =
    elim! λ p q r → ap inc (++-assoc r q p)
```

Proving that this construction is free involves a bit more work.

We start with a useful lemma. Let $\cC$ be an arbitrary strict category,
$G$ a commutative graph, and $f : G \to \cC$ a commutative graph homomorphism.
If $p, q$ are related by the commutative closure of $G$, then folding $f$
over $p$ and $q$ results in the same morphism.

```agda
module _ (C : Σ (Precategory o ℓ) is-strict) where
  private
    module C = Cat.Reasoning (C .fst)
    ∣C∣ : Comm-graph o ℓ
    ∣C∣ = Strict-cats↪Comm-graphs .F₀ C

  path-fold-commutativity
    : (f : Comm-graph-hom G ∣C∣)
    → ∀ {x y} (p q : Path-in (G .graph) x y)
    → Commutativity G p q
    → path-fold C (f .hom) p ≡ path-fold C (f .hom) q
```

The proof is an easy but tedious application of the elimination principe
of `Commutative`{.Agda}.

```agda
  path-fold-commutativity {G = G} f p q =
    Commutativity-elim-prop G
      {P = λ {x} {y} {p} {q} _ →
        path-fold C (f .hom) p ≡ path-fold C (f .hom) q}
      (λ _ → hlevel 1)
      (λ {_} {_} {p} {q} p~q →
        sym (path-reduce-map p)
        ∙ □-out! (f .pres-comm p~q)
        ∙ path-reduce-map q)
      refl (λ _ → sym) (λ _ p=q _ q=r → p=q ∙ q=r)
      (λ {_} {_} {_} {p} {q} {r} {s} _ p=q _ r=s →
        path-fold-++ C p r
        ∙ ap₂ C._∘_ r=s p=q
        ∙ sym (path-fold-++ C q s))
```

This lemma lets us extend folds over paths to folds over quotiented
paths.

```agda
  comm-path-fold
    : (f : Comm-graph-hom G ∣C∣)
    → ∀ {x y} → Path-in (G .graph) x y / Commutativity G
    → C.Hom (f .vertex x) (f .vertex y)
  comm-path-fold f =
    Quot-elim (λ _ → hlevel 2)
      (path-fold C (f .hom))
      (path-fold-commutativity f)
```

Moreover, this extends to a functor from the free category over $G$
to $\cC$.

```agda
  CommF
    : Comm-graph-hom G ∣C∣
    → Functor (Comm-path-category G) (C .fst)
  CommF f .F₀ = f .vertex
  CommF f .F₁ = comm-path-fold f
  CommF f .F-id = refl
  CommF f .F-∘ = elim! λ p q → path-fold-++ C q p
```

Like path categories, functors out of commutative path categories
are purely characterized by their behaviour on edges.

<!--
```agda
module _ {C : Precategory o ℓ} where
  private module C = Cat.Reasoning C
```
-->

```agda
  Comm-path-category-functor-path
    : {F F' : Functor (Comm-path-category G) C}
    → (p0 : ∀ x → F .F₀ x ≡ F' .F₀ x)
    → (p1 : ∀ {x y} (e : G .Edge x y)
            → PathP (λ i → C.Hom (p0 x i) (p0 y i))
                (F .F₁ (inc (cons e nil)))
                (F' .F₁ (inc (cons e nil))))
    → F ≡ F'
```
<details>
<summary>Like the analogous result for path categories, this proof involves
some cubical yoga which we will hide from the innocent reader.
</summary>

```agda
  Comm-path-category-functor-path {G = G} {F = F} {F' = F'} p0 p1 =
    Functor-path p0 (elim! p1-paths)
    where
      p1-paths
        : ∀ {x y}
        → (p : Path-in (G .graph) x y)
        → PathP (λ i → C.Hom (p0 x i) (p0 y i)) (F .F₁ (inc p)) (F' .F₁ (inc p))
      p1-paths {x = x} nil i =
        hcomp (∂ i) λ where
          j (i = i0) → F .F-id (~ j)
          j (i = i1) → F' .F-id (~ j)
          j (j = i0) → C.id
      p1-paths (cons e p) i =
        hcomp (∂ i) λ where
          j (i = i0) → F .F-∘ (inc p) (inc (cons e nil)) (~ j)
          j (i = i1) → F' .F-∘ (inc p) (inc (cons e nil)) (~ j)
          j (j = i0) → p1-paths p i C.∘ p1 e i
```
</details>

With these results in hand, we can return to our original goal of showing
that the commutative path category on $G$ is a [[free object]] relative
to the underlying commutative graph functor.

```agda
Comm-free-category
  : ∀ (G : Comm-graph ℓ ℓ)
  → Free-object Strict-cats↪Comm-graphs G
Comm-free-category G .Free-object.free = Comm-path-category G , hlevel 2
```

The unit of the free object takes vertices to themselves, and edges
to singleton paths. We need to do a bit of work to show that this construction
preserves commutativities, but it's not too difficult.

```agda
Comm-free-category G .Free-object.unit = unit-comm where
  G* : Σ (Precategory _ _) is-strict
  G* = Comm-path-category G , hlevel 2

  ∣G*∣ : Graph _ _
  ∣G*∣ = Strict-cats↪Graphs .F₀ G*

  unit : Graph-hom (G .graph) ∣G*∣
  unit .Graph-hom.vertex x = x
  unit .Graph-hom.edge e = inc (cons e nil)

  unit-comm : Comm-graph-hom G (Strict-cats↪Comm-graphs .F₀ G*)
  unit-comm .hom = unit
  unit-comm .pres-comm {p = p} {q = q} p~q =
    pure $
      path-reduce G* (path-map unit p) ≡⟨ path-reduce-map p ⟩
      path-fold G* unit p              ≡˘⟨ path-fold-unique G* inc refl (λ _ _ → refl) p ⟩
      inc p                            ≡⟨ quot (commutative p~q) ⟩
      inc q                            ≡⟨ path-fold-unique G* inc refl (λ _ _ → refl) q ⟩
      path-fold G* unit q              ≡˘⟨ path-reduce-map q ⟩
      path-reduce G* (path-map unit q) ∎
```

On the other hand, the we've already put in the work for the universal
property: all that we need to do is assmeble previous results!

```agda
Comm-free-category G .Free-object.fold {Y = C} f = CommF C f
Comm-free-category G .Free-object.commute {Y = C} =
  Comm-graph-hom-path (λ _ → refl) (λ _ → idl _)
  where open Precategory (C .fst)
Comm-free-category G .Free-object.unique {Y = C} F p =
  Comm-path-category-functor-path
    (λ x i → p i .vertex x)
    (λ e → to-pathp (from-pathp (λ i → p i .edge e) ∙ sym (idl _)))
  where open Precategory (C .fst)
```

<!--
```agda
Comm-free-categories : Functor (Comm-graphs ℓ ℓ) (Strict-cats ℓ ℓ)
Comm-free-categories =
  free-objects→functor Comm-free-category

Comm-free-categories⊣Underlying-comm-graph
  : Comm-free-categories {ℓ} ⊣ Strict-cats↪Comm-graphs
Comm-free-categories⊣Underlying-comm-graph =
  free-objects→left-adjoint Comm-free-category
```
-->

This means that the category of strict categories is a [[reflective subcategory]]
of the category of commutative graphs. In more intuitive terms, this means
that we can think about strict categories as algebraic structure placed
atop a commutative graph, as inclusions from reflective subcategories
are [[monadic]]!

```agda
Comm-free-categories⊣Underlying-comm-graph-reflective
  : is-reflective (Comm-free-categories⊣Underlying-comm-graph {ℓ})
Comm-free-categories⊣Underlying-comm-graph-reflective =
  full+faithful→ff Strict-cats↪Comm-graphs
    Strict-cats↪Comm-graphs-full
    Strict-cats↪Comm-graphs-faithful
```
