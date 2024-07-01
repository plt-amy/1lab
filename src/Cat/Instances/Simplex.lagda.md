---
description: |
  The simplex category.
---
<!--
```agda
open import 1Lab.Function.Antisurjection
open import 1Lab.Function.Antiinjection

open import Cat.Diagram.Terminal
open import Cat.Functor.Concrete
open import Cat.Diagram.Initial
open import Cat.Prelude
open import Cat.Gaunt

open import Data.Dec
open import Data.Fin

open import Meta.Brackets

open import Order.Instances.Nat

import Cat.Reasoning

import Data.Fin as Fin
import Data.Nat as Nat

import Order.Reasoning
```
-->

```agda
module Cat.Instances.Simplex where
```

<!--
```agda
open Precategory
open split-antiinjective
```
-->

# The simplex category {defines="simplex-category semisimplex-category demisimplex-category"}

The simplex category, $\Delta$, is generally introduced as the category
of non-empty finite ordinals and order-preserving maps. Though
conceptually simple, this definition is difficult to work with, as
diagrams over $\Delta$ are extremely hard to form. This is why mathematicians
prefer to work with a particular presentation of $\Delta$ as a free category
generated from 2 classes of maps:

* Face maps $\delta^{n}_{i} : [n] \to [n + 1]$ for $0 \leq i \leq n$, $0 < n$
* Degeneracy maps $\sigma^{n}_{i} : [n + 1] \to [n]$ for $0 \leq i < n$, $0 < n$

Face maps $\delta^{n}_{i}$ are meant to be interpreted as injections that skip
the $i$th element of $[n + 1]$, and degeneracies as surjections that
take both $i$th and $i+1$-th element of $[n + 1]$ to $i$.

Unfortunately, we need to quotient these generators to get the correct
category; these equations are known as the **simplicial identities**, and
are quite involved.

* For all $i \leq j$, $\delta^{n + 1}_i \circ \delta^{n}_j = \delta^{n+1}_{j+1} \circ \delta^{n}_{i}$; and
* For all $i \leq j$, $\sigma^{n}_j \circ \sigma^{n+1}_i = \sigma^{n}_i \circ \sigma^{n+1}_{j + 1}$; and
* For all $i \leq j$, $\sigma^{n+1}_{j+1} \circ \delta^{n+2}_i = \delta^{n+1}_i \circ \sigma^{n}_{j}$; and
* For all $i, j$ with $i = j$ or $i = j + 1$, $\sigma{n}_j \circ \delta^{n+1}_i = id$; and
* For all $j < i$, $\sigma^{n+1}_j \circ \delta^{n+2}_{i+1} = \delta^{n+1}_{i} \circ \sigma^{n}_{j}$

These identities are extremely painful to work with, and we would need
to deal with them *every* time we construct a simplicial diagram.
This is a complete non-starter, so we will need to figure out a better approach.

Typically, the way to avoid dealing with quotients by some set of equations
is to find some sort of normal form. Luckily, the simplex category has a
particularly simple normal form: every map can be expressed uniquely as
$$
\delta_{i_1} \circ \cdots \circ \delta_{i_k} \circ \sigma_{j_1} \circ \cdots \sigma_{j_l}
$$
where $0 \leq i_k < \cdots < i_1$ and $0 \leq j_1 < \cdots < j_l$. In simpler
terms, every map can be uniquely factored as a composite of a strictly
increasing sequence of face maps, followed by a decreasing sequence of
degeneracies.

<!--
```agda
private variable
  k l m n o l' m' n' o' : Nat
```
-->

These normal forms are relatively straightforward to encode in Agda:
ascending chains of face maps can be defined via an indexed inductive,
where `shift⁺`{.Agda} postcomposes the 0th face map, and `keep⁺`{.Agda}
shifts up the index of every face map by 1. We call these maps **semisimplicial**,
and the resulting category will be denoted $\Delta_{a}^{+}$

```agda
data Δ-Hom⁺ : Nat → Nat → Type where
  done⁺ : Δ-Hom⁺ 0 0
  shift⁺ : ∀ {m n} → Δ-Hom⁺ m n → Δ-Hom⁺ m (suc n)
  keep⁺ : ∀ {m n} → Δ-Hom⁺ m n → Δ-Hom⁺ (suc m) (suc n)
```

For instance, the map $\delta_{0} \circ \delta_{2} : [2] \to [4]$
would be written as:

```agda
private
  δ₀∘δ₂ : Δ-Hom⁺ 2 4
  δ₀∘δ₂ = shift⁺ (keep⁺ (keep⁺ (shift⁺ done⁺)))
```

The first `shift⁺`{.Agda} denotes the postcomposition of the 0th face maps,
and the 2 `keep⁺`{.Agda} constructors bump up the index of the next
face map by 2. This means that the final `shift⁺`{.Agda} denotes the 4th
face map!

Descending chains of degeneracies are defined in a similar fashion, where
where `crush⁻`{.Agda} precomposes the 0th degeneracy map. We will call
these maps **demisimplicial**, and the category they form will be denoted
$\Delta_{a}^{-}$.

```agda
data Δ-Hom⁻ : Nat → Nat → Type where
  done⁻ : Δ-Hom⁻ 0 0
  crush⁻ : ∀ {m n} → Δ-Hom⁻ (suc m) n → Δ-Hom⁻ (suc (suc m)) n
  keep⁻ : ∀ {m n} → Δ-Hom⁻ m n → Δ-Hom⁻ (suc m) (suc n)
```

As an example, the map $\sigma_{2} \circ \sigma_{0} : [5] \to [3]$ would
be written as:

```agda
private
  σ₂∘σ₀ : Δ-Hom⁻ 5 3
  σ₂∘σ₀ = crush⁻ (keep⁻ (keep⁻ (crush⁻ (keep⁻ done⁻))))
```

Here, the outermost `crush⁻` constructor denotes the precomposition by $\sigma_{0}$.
Next, the two `keep⁻`{.Agda} constructors bump the index of the next face
map we encounter up by 2, so the final `crush⁻` constructor denotes the
2nd degeneracy map.

Finally, a **simplicial map** consist of an ascending chain of face maps
and a descending chain of degeneracies that factor through the same object.
We will refer to this object as the *image* of the map. These maps will form
the **augmented simplicial category**, which is denoted via $\Delta_{a}$.

```agda
record Δ-Hom (m n : Nat) : Type where
  no-eta-equality
  constructor Δ-factor
  field
    {im} : Nat
    hom⁺ : Δ-Hom⁺ im n
    hom⁻ : Δ-Hom⁻ m im

open Δ-Hom
```

Note that we allow $m$ and $n$ to be 0 for all of our classes of maps;
this is useful for algebraic applications, as $0$ plays the role of the
empty context. However, $0$ can be problematic for homotopical applications,
so it is useful to consider categories of simplicial maps between non-zero
naturals. This category is known as the **simplex category**, and is denoted
by $\Delta$. Moreover, there are also non-augmented versions of semi and
demisimplex categories, which are denoted by $\Delta^{+}$ and $\Delta^{-}$, resp.

<!--
```agda
done : Δ-Hom 0 0
done .im = 0
done .hom⁺ = done⁺
done .hom⁻ = done⁻

crush : Δ-Hom (suc m) n → Δ-Hom (suc (suc m)) n
crush f .im = f .im
crush f .hom⁺ = f .hom⁺
crush f .hom⁻ = crush⁻ (f .hom⁻)

shift : Δ-Hom m n → Δ-Hom m (suc n)
shift f .im = f .im
shift f .hom⁺ = shift⁺ (f .hom⁺)
shift f .hom⁻ = f .hom⁻
```
-->

<!--
```agda
Δ-Hom-pathp
  : {f : Δ-Hom m n} {g : Δ-Hom m' n'}
  → (p : m ≡ m') (q : f .im ≡ g .im) (r : n ≡ n')
  → PathP (λ i → Δ-Hom⁺ (q i) (r i)) (f .hom⁺) (g .hom⁺)
  → PathP (λ i → Δ-Hom⁻ (p i) (q i)) (f .hom⁻) (g .hom⁻)
  → PathP (λ i → Δ-Hom (p i) (r i)) f g
Δ-Hom-pathp p q r s t i .im = q i
Δ-Hom-pathp p q r s t i .hom⁺ = s i
Δ-Hom-pathp p q r s t i .hom⁻ = t i

Δ-Hom-path
  : {f g : Δ-Hom m n}
  → (p : f .im ≡ g .im)
  → PathP (λ i → Δ-Hom⁺ (p i) n) (f .hom⁺) (g .hom⁺)
  → PathP (λ i → Δ-Hom⁻ m (p i)) (f .hom⁻) (g .hom⁻)
  → f ≡ g
Δ-Hom-path p q r = Δ-Hom-pathp refl p refl q r

Δ-Hom-η
  : {f g : Δ-Hom m n}
  → Δ-factor (f .hom⁺) (f .hom⁻) ≡ Δ-factor (g .hom⁺) (g .hom⁻)
  → f ≡ g
Δ-Hom-η p i .im = p i .im
Δ-Hom-η p i .hom⁺ = p i .hom⁺
Δ-Hom-η p i .hom⁻ = p i .hom⁻
```
-->

## Identities and composites

Identity morphisms $[n] \to [n]$ in $\Delta^{+}$ and $\Delta^{-}$ are defined
via induction on $n$, and do not contain any face or degeneracy maps.

```agda
id⁺ : ∀ {n} → Δ-Hom⁺ n n
id⁺ {zero} = done⁺
id⁺ {suc n} = keep⁺ id⁺

id⁻ : ∀ {n} → Δ-Hom⁻ n n
id⁻ {zero} = done⁻
id⁻ {suc n} = keep⁻ id⁻
```

Identity morphisms in $\Delta$ factorize as the identities in $\Delta^{+}$
and $\Delta^{-}$.

```agda
idΔ : Δ-Hom n n
idΔ .im = _
idΔ .hom⁺ = id⁺
idΔ .hom⁻ = id⁻
```

Composing semisimplicial maps is somewhat tricky, as we need to preserve
the invariant that they form an ascending chain of face maps. To ensure
this, we will need to judiciously apply the simplicial identities to
commute face maps past one another.

```agda
_∘⁺_ : Δ-Hom⁺ n o → Δ-Hom⁺ m n → Δ-Hom⁺ m o
```

First, the base case: composing a semisimplicial map $f$ with the identity
map $[0] \to [0]$ should clearly yield $f$.

```agda
f ∘⁺ done⁺ = f
```

Next, the composite $(\delta_0 \circ f) \circ (\delta_0 \circ g)$
can be written in normal form by reassociating as
$$
\delta_0 \circ (f \circ (\delta_0 \circ g))
$$
and then recursively normalizing the right-hand side.

```agda
shift⁺ f ∘⁺ shift⁺ g = shift⁺ (f ∘⁺ shift⁺ g)
```

Now for the tricky case: consider the composite $\uparrow f \circ (\delta_0 \circ g)$,
where $\uparrow f$ shifts the index of every face map in $f$ by 1.
This means that we can repeatedly apply the 1st simplicial identity to
commute $\delta_{0}$ past every single face map in $f$ by lowering their
indices by one. This yields the following equality
$$
\uparrow f \circ (\delta_0 \circ g) = \delta_0 \circ (f \circ g)
$$
and the right-hand side can be placed into normal form by normalizing
$f \circ g$.

```agda
keep⁺ f ∘⁺ shift⁺ g = shift⁺ (f ∘⁺ g)
```

Luckily, the dual case is much easier: the composite $(\delta_0 \circ f) \circ \uparrow g$
can directly be reassociated as
$$
\delta_0 \circ (f \circ \uparrow g)
$$
We can then recursively normalize the right hand side to obtain a normal form.

```agda
shift⁺ f ∘⁺ keep⁺ g = shift⁺ (f ∘⁺ keep⁺ g)
```

Finally, $\uparrow f \circ \uparrow g = \uparrow (f \circ g)$.

```agda
keep⁺ f ∘⁺ keep⁺ g = keep⁺ (f ∘⁺ g)
```

Composing demisimplicial maps follows a similar process, though it is
slightly trickier.

```agda
_∘⁻_ : Δ-Hom⁻ n o → Δ-Hom⁻ m n → Δ-Hom⁻ m o
```

As before, precomposing $g$ with the identity map $[0] \to [0]$ just yields $g$.

```agda
done⁻ ∘⁻ g = g
```

Next, $(f \circ \sigma_0) \circ (g \circ \sigma_0)$ can be written
in our normal form by reassociating it as
$$
(f \circ \sigma_0) \circ g) \circ \sigma_0
$$
and then recursively normalizing the left-hand side.

```agda
crush⁻ f ∘⁻ crush⁻ g = crush⁻ (crush⁻ f ∘⁻ g)
```

Our first tricky case is when we encounter a composite of the form
$(f \circ \sigma_0) \circ (\uparrow g \circ \sigma_1)$. Every degeneracy
in $\uparrow g$ must have an index of at least $1$, so we can apply
the 2nd simplicial identity to commute the 0th face map past them
by lowering all indices by 1. This yields the following equation
$$
(f \circ \sigma_0) \circ (\uparrow g \circ \sigma_1) = (f \circ g) \circ \sigma_0 \circ \sigma_0
$$
If we recursively normalize $f \circ g$, then the RHS of this equation will
be in normal form!

```agda
crush⁻ f ∘⁻ keep⁻ (crush⁻ g) = crush⁻ (crush⁻ (f ∘⁻ g))
```

The next tricky case is when we encounter a composite of the form
$(f \circ \sigma_0) \circ (\uparrow \uparrow g)$. We can use a similar
line of reasoning as the previous case to commute $\sigma_0$ past $\uparrow \uparrow g$
by decrementing all indices by one, yielding the following equation:
$$
(f \circ \sigma_0) \circ (\uparrow \uparrow g) = (f \circ \uparrow g) \circ \sigma_0
$$

We will take this equation as definitional, and then proceed to recursively
normalize the left-hand side.

```agda
crush⁻ f ∘⁻ keep⁻ (keep⁻ g) = crush⁻ (f ∘⁻ (keep⁻ g))
```

Mercifully, the final 2 cases are easy. For the first, note that
composites of the form $\uparrow f \circ (g \circ \sigma_0)$ can
be placed into normal form by reassociating and recursively normalizing.
The second case is even easier, as we can rewrite $\uparrow f \circ \uparrow g$
into $\uparrow (f \circ g)$.

```agda
keep⁻ f ∘⁻ crush⁻ g = crush⁻ (keep⁻ f ∘⁻ g)
keep⁻ f ∘⁻ keep⁻ g = keep⁻ (f ∘⁻ g)
```

Composites of simplicial maps are even more tricky, as we
need to somehow normalize a string of maps $f^{+} \circ f^{-} \circ g^{+} \circ g^{-}$
into a pair of a semisimplicial and demisimplicial maps. The crux of
the problem is that we need to factor the composite of $f^{-} \circ g^{+}$
$h^{+} \circ h^{-}$, where $h^{+}$ is semisimplicial and $h^{-}$ is
demisimplicial. Once this is done, we can obtain our final factorization
by pre and post-composing with $g^{-}$ and $f^{+}$, resp.

For pedagogic purposes, we will define the image and semi/demisimplicial
components of our factorization simultaneously.

```agda
interleaved mutual
  imΔ : Δ-Hom⁻ n o → Δ-Hom⁺ m n → Nat
  _∘Δ⁺_ : (f⁻ : Δ-Hom⁻ n o) → (f⁺ : Δ-Hom⁺ m n) → Δ-Hom⁺ (imΔ f⁻ f⁺) o
  _∘Δ⁻_ : (f⁻ : Δ-Hom⁻ n o) → (f⁺ : Δ-Hom⁺ m n) → Δ-Hom⁻ m (imΔ f⁻ f⁺)
```

If both maps are the identity $[0] \to [0]$, then we can clearly factor
them as identity maps.

```agda
  imΔ done⁻ done⁺ = 0
  done⁻ ∘Δ⁺ done⁺ = done⁺
  done⁻ ∘Δ⁻ done⁺ = done⁻
```

Next, a composite of the form $(f^{-} \circ \sigma_0) \circ (\delta_0 \circ g^{+})$
is equal to $f^{-} \circ g^{+}$ by the 4th simplicial identity.

```agda
  imΔ (crush⁻ f⁻) (shift⁺ g⁺) = imΔ f⁻ g⁺
  (crush⁻ f⁻) ∘Δ⁺ (shift⁺ g⁺) = f⁻ ∘Δ⁺ g⁺
  (crush⁻ f⁻) ∘Δ⁻ (shift⁺ g⁺) = f⁻ ∘Δ⁻ g⁺
```

We can also apply the 4th simplicial identity to composites of the form
$(f^{-} \circ \sigma_0) \circ (\delta_1 \circ \uparrow g^{+})$.


```agda
  imΔ (crush⁻ f⁻) (keep⁺ (shift⁺ g⁺)) = imΔ f⁻ (keep⁺ g⁺)
  (crush⁻ f⁻) ∘Δ⁺ (keep⁺ (shift⁺ g⁺)) = f⁻ ∘Δ⁺ (keep⁺ g⁺)
  (crush⁻ f⁻) ∘Δ⁻ (keep⁺ (shift⁺ g⁺)) = f⁻ ∘Δ⁻ (keep⁺ g⁺)
```

The 5th simplicial identity can be applied to composites of the form
$(f^{-} \circ \sigma_0) \circ (\uparrow \uparrow g^{+})$, which allows
us to commute the $\sigma_0$ past $\uparrow \uparrow g^{+}$ by decrementing
the index of every face map in $\uparrow \uparrow g^{+}$.

```agda
  imΔ (crush⁻ f⁻) (keep⁺ (keep⁺ g⁺)) = imΔ f⁻ (keep⁺ g⁺)
  (crush⁻ f⁻) ∘Δ⁺ (keep⁺ (keep⁺ g⁺)) = f⁻ ∘Δ⁺ (keep⁺ g⁺)
  (crush⁻ f⁻) ∘Δ⁻ (keep⁺ (keep⁺ g⁺)) = crush⁻ (f⁻ ∘Δ⁻ (keep⁺ g⁺))
```

Likewise, the 3rd simplicial identity can be applied to composites
of the form $(\uparrow f^{-}) \circ (\delta_0 \circ g^{+})$. This
Like the other laws, this lets us commute $\delta_0$ past $\uparrow f^{-}$
by decrementing the index of every face map.

```agda
  imΔ (keep⁻ f) (shift⁺ g⁺) = imΔ f g⁺
  (keep⁻ f⁻) ∘Δ⁺ (shift⁺ g⁺) = shift⁺ (f⁻ ∘Δ⁺ g⁺)
  (keep⁻ f⁻) ∘Δ⁻ (shift⁺ g⁺) = f⁻ ∘Δ⁻ g⁺
```

Finally, we can reduce $\uparrow f^{-} \circ \uparrow g{+}$ to $\uparrow (f^{-} \circ g^{+})$.

```agda
  imΔ (keep⁻ f) (keep⁺ g) = suc (imΔ f g)
  _∘Δ⁺_ (keep⁻ f⁻) (keep⁺ f⁺) = keep⁺ (f⁻ ∘Δ⁺ f⁺)
  _∘Δ⁻_ (keep⁻ f⁻) (keep⁺ f⁺) = keep⁻ (f⁻ ∘Δ⁻ f⁺)
```

With that hard work out of the way, constructing the composite of
simplicial maps just requires us to pre and post-compose with $g^{-}$
and $f^{+}$, resp.

```agda
_∘Δ_ : Δ-Hom n o → Δ-Hom m n → Δ-Hom m o
(f ∘Δ g) .im = imΔ (f .hom⁻) (g .hom⁺)
(f ∘Δ g) .hom⁺ = f .hom⁺ ∘⁺ (f .hom⁻ ∘Δ⁺ g .hom⁺)
(f ∘Δ g) .hom⁻ = (f .hom⁻ ∘Δ⁻ g .hom⁺) ∘⁻ g .hom⁻
```

## As maps between finite sets

At this point, we could prove the associativity/unitality laws for
$\Delta^{+}, \Delta^{-}$, and $\Delta$ by a series of brutal inductions.
Luckily for us, there is a more elegant approach: all of these maps
have interpretations as maps `Fin m → Fin n`. This interpretation is
has 2 key properties:

1. The interpretation is functorial: both $\llbracket id \rrbracket = id$,
  and $\llbracket f \circ g \rrbracket = \llbracket f \rrbracket \circ \llbracket g \rrbracket$.
2. The interpretation is injective: if $\llbracket f \rrbracket = \llbracket g \rrbracket$, then $f = g$.

Together, this ensures that our interpretations form a series [[faithful functors]],
which allows us to lift equations from functions back to equations on their
syntactic presentations. In particular, composition of functions is associative
and unital, so constructing these interpretations gives us associativity
and unitality "for free".

With that plan outlined, we begin by constructing interpretations of (semi/demi)
simplicial maps as functions.

```agda
Δ-hom⁺ : ∀ {m n} → Δ-Hom⁺ m n → Fin m → Fin n
Δ-hom⁺ (shift⁺ f) = fsuc ⊙ Δ-hom⁺ f
Δ-hom⁺ (keep⁺ f) = fkeep (Δ-hom⁺ f)

Δ-hom⁻ : ∀ {m n} → Δ-Hom⁻ m n → Fin m → Fin n
Δ-hom⁻ (crush⁻ f) = Δ-hom⁻ f ⊙ fpred
Δ-hom⁻ (keep⁻ f) = fkeep (Δ-hom⁻ f)

Δ-hom : ∀ {m n} → Δ-Hom m n → Fin m → Fin n
Δ-hom f = Δ-hom⁺ (f .hom⁺) ⊙ Δ-hom⁻ (f .hom⁻)
```

<!--
```agda
{-# DISPLAY Δ-hom⁺ f = ⟦ f ⟧ #-}
{-# DISPLAY Δ-hom⁻ f = ⟦ f ⟧ #-}
{-# DISPLAY Δ-hom  f = ⟦ f ⟧ #-}
```
-->

We will denote each of these interpretations as `⟦ f ⟧ i` to avoid
too much syntactic overhead.

<!--
```agda
instance
  Δ-Hom⁺-⟦⟧-notation
    : ∀ {m n} → ⟦⟧-notation (Δ-Hom⁺ m n)
  Δ-Hom⁺-⟦⟧-notation {m = m} {n = n} .⟦⟧-notation.lvl = lzero
  Δ-Hom⁺-⟦⟧-notation {m = m} {n = n} .⟦⟧-notation.Sem = Fin m → Fin n
  Δ-Hom⁺-⟦⟧-notation {m = m} {n = n} .⟦⟧-notation.⟦_⟧ = Δ-hom⁺

  Δ-Hom⁻-⟦⟧-notation
    : ∀ {m n} → ⟦⟧-notation (Δ-Hom⁻ m n)
  Δ-Hom⁻-⟦⟧-notation {m = m} {n = n} .⟦⟧-notation.lvl = lzero
  Δ-Hom⁻-⟦⟧-notation {m = m} {n = n} .⟦⟧-notation.Sem = Fin m → Fin n
  Δ-Hom⁻-⟦⟧-notation {m = m} {n = n} .⟦⟧-notation.⟦_⟧ = Δ-hom⁻

  Δ-Hom-⟦⟧-notation
    : ∀ {m n} → ⟦⟧-notation (Δ-Hom m n)
  Δ-Hom-⟦⟧-notation {m = m} {n = n} .⟦⟧-notation.lvl = lzero
  Δ-Hom-⟦⟧-notation {m = m} {n = n} .⟦⟧-notation.Sem = Fin m → Fin n
  Δ-Hom-⟦⟧-notation {m = m} {n = n} .⟦⟧-notation.⟦_⟧ = Δ-hom
```
-->

Now that we have our interpretations, we can start to charaterize their
behaviour. First, note that semisimplicial maps always encode inflationary
functions.

```agda
Δ-hom⁺-incr
  : ∀ (f⁺ : Δ-Hom⁺ m n)
  → ∀ i → to-nat i Nat.≤ to-nat (⟦ f⁺ ⟧ i)
Δ-hom⁺-incr (shift⁺ f) i = Nat.≤-sucr (Δ-hom⁺-incr f i)
Δ-hom⁺-incr (keep⁺ f) fzero = Nat.0≤x
Δ-hom⁺-incr (keep⁺ f) (fsuc i) = Nat.s≤s (Δ-hom⁺-incr f i)
```

Likewise, demisimplicial maps always encode deflationary functions.

```agda
Δ-hom⁻-decr
  : ∀ (f⁻ : Δ-Hom⁻ m n)
  → ∀ i → to-nat (⟦ f⁻ ⟧ i) Nat.≤ to-nat i
Δ-hom⁻-decr (crush⁻ f) fzero = Δ-hom⁻-decr f fzero
Δ-hom⁻-decr (crush⁻ f) (fsuc i) = Nat.≤-sucr (Δ-hom⁻-decr f i)
Δ-hom⁻-decr (keep⁻ f) fzero = Nat.0≤x
Δ-hom⁻-decr (keep⁻ f) (fsuc i) = Nat.s≤s (Δ-hom⁻-decr f i)
```

A useful corollary of this is that demisimplicial maps always map 0 to 0.

```agda
Δ-hom⁻-zero
  : ∀ {m n} (f⁻ : Δ-Hom⁻ (suc m) (suc n))
  → ⟦ f⁻ ⟧ fzero ≡ fzero
Δ-hom⁻-zero f⁻ = to-nat-inj (Nat.≤-antisym (Δ-hom⁻-decr f⁻ fzero) Nat.0≤x)
```

Moreover, semisimplicial maps always encode injective functions, and
demisimplicial maps encode *split* surjections.

```agda
Δ-hom⁺-to-inj
  : ∀ {m n}
  → (f : Δ-Hom⁺ m n)
  → injective ⟦ f ⟧

Δ-hom⁻-to-split-surj
  : ∀ {m n}
  → (f : Δ-Hom⁻ m n)
  → split-surjective ⟦ f ⟧
```

<details>
<summary>These both follow directly via induction, so we omit the proofs.
</summary>

```agda
Δ-hom⁺-to-inj (shift⁺ f) p =
  Δ-hom⁺-to-inj f (fsuc-inj p)
Δ-hom⁺-to-inj (keep⁺ f) {fzero} {fzero} p =
  refl
Δ-hom⁺-to-inj (keep⁺ f) {fzero} {fsuc y} p =
  absurd (fzero≠fsuc p)
Δ-hom⁺-to-inj (keep⁺ f) {fsuc x} {fzero} p =
  absurd (fsuc≠fzero p)
Δ-hom⁺-to-inj (keep⁺ f) {fsuc x} {fsuc y} p =
  ap fsuc (Δ-hom⁺-to-inj f (fsuc-inj p))

Δ-hom⁻-to-split-surj {m = suc m} f fzero =
  fzero , Δ-hom⁻-zero f
Δ-hom⁻-to-split-surj (crush⁻ f) (fsuc i) =
  Σ-map fsuc (λ p → p) (Δ-hom⁻-to-split-surj f (fsuc i))
Δ-hom⁻-to-split-surj {m = suc m} (keep⁻ f) (fsuc i) =
  Σ-map fsuc (ap fsuc) (Δ-hom⁻-to-split-surj f i)
```
</details>

<!--
```agda
Δ-hom⁻-to-surj
  : ∀ {m n}
  → (f : Δ-Hom⁻ m n)
  → is-surjective ⟦ f ⟧
Δ-hom⁻-to-surj f i = inc (Δ-hom⁻-to-split-surj f i)
```
-->

We also remark that semi and demisimplicial maps always encode monotonic functions.

```agda
Δ-hom⁺-pres-≤
  : ∀ (f⁺ : Δ-Hom⁺ m n)
  → ∀ {i j} → i ≤ j → ⟦ f⁺ ⟧ i ≤ ⟦ f⁺ ⟧ j
Δ-hom⁺-pres-≤ (shift⁺ f) {i} {j} i≤j = Nat.s≤s (Δ-hom⁺-pres-≤ f i≤j)
Δ-hom⁺-pres-≤ (keep⁺ f) {fzero} {j} i≤j = Nat.0≤x
Δ-hom⁺-pres-≤ (keep⁺ f) {fsuc i} {fsuc j} i≤j = Nat.s≤s (Δ-hom⁺-pres-≤ f (Nat.≤-peel i≤j))

Δ-hom⁻-pres-≤
  : ∀ (f⁻ : Δ-Hom⁻ m n)
  → ∀ {i j} → i ≤ j → ⟦ f⁻ ⟧ i ≤ ⟦ f⁻ ⟧ j
Δ-hom⁻-pres-≤ (crush⁻ f) {fzero} {j} i≤j = Nat.≤-trans (Δ-hom⁻-decr f fzero) Nat.0≤x
Δ-hom⁻-pres-≤ (crush⁻ f) {fsuc i} {fsuc j} i≤j = Δ-hom⁻-pres-≤ f (Nat.≤-peel i≤j)
Δ-hom⁻-pres-≤ (keep⁻ f) {fzero} {j} i≤j = Nat.0≤x
Δ-hom⁻-pres-≤ (keep⁻ f) {fsuc i} {fsuc j} i≤j = Nat.s≤s (Δ-hom⁻-pres-≤ f (Nat.≤-peel i≤j))
```

This in turn implies that simplicial maps also encode monotonic functions.

```agda
Δ-hom-pres-≤
  : ∀ (f : Δ-Hom m n)
  → ∀ {i j} → i ≤ j → ⟦ f ⟧ i ≤ ⟦ f ⟧ j
Δ-hom-pres-≤ f i≤j = Δ-hom⁺-pres-≤ (f .hom⁺) (Δ-hom⁻-pres-≤ (f .hom⁻) i≤j)
```

Semisimplicial maps are not just monotonic; they are *strictly* monotonic!

```agda
Δ-hom⁺-pres-<
  : ∀ (f⁺ : Δ-Hom⁺ m n)
  → ∀ {i j} → i < j → ⟦ f⁺ ⟧ i < ⟦ f⁺ ⟧ j
Δ-hom⁺-pres-< (shift⁺ f⁺) {i} {j} i<j =
  Nat.s≤s (Δ-hom⁺-pres-< f⁺ i<j)
Δ-hom⁺-pres-< (keep⁺ f⁺) {fzero} {fsuc j} i<j =
  Nat.s≤s Nat.0≤x
Δ-hom⁺-pres-< (keep⁺ f⁺) {fsuc i} {fsuc j} i<j =
  Nat.s≤s (Δ-hom⁺-pres-< f⁺ (Nat.≤-peel i<j))
```

Likewise, demisimplicial maps reflect the strict order on `Fin`{.Agda}.

```agda
Δ-hom⁻-reflect-<
  : ∀ (f⁻ : Δ-Hom⁻ m n)
  → ∀ {i j} → ⟦ f⁻ ⟧ i < ⟦ f⁻ ⟧ j → i < j
Δ-hom⁻-reflect-< (crush⁻ f⁻) {i} {fzero} fi<fj =
  absurd (Nat.¬sucx≤0 _ (Nat.≤-trans fi<fj (Δ-hom⁻-decr f⁻ fzero)))
Δ-hom⁻-reflect-< (crush⁻ f⁻) {fzero} {fsuc j} fi<fj =
  Nat.s≤s Nat.0≤x
Δ-hom⁻-reflect-< (crush⁻ f⁻) {fsuc i} {fsuc j} fi<fj =
  Nat.s≤s (Δ-hom⁻-reflect-< f⁻ fi<fj)
Δ-hom⁻-reflect-< (keep⁻ f⁻) {fzero} {fsuc j} fi<fj =
  Nat.s≤s Nat.0≤x
Δ-hom⁻-reflect-< (keep⁻ f⁻) {fsuc i} {fsuc j} fi<fj =
  Nat.s≤s (Δ-hom⁻-reflect-< f⁻ (Nat.≤-peel fi<fj))
```

### Injectivity of interpretations

As noted earlier, each map in $\Delta^{+}, \Delta^{-}$ and $\Delta$ resp.
encodes a unique function between finite sets. Proving this for $\Delta^{+}$
and $\Delta^{-}$ is tedious, but straightforward. However, $\Delta$ presents
a more difficult challenge, as we *also* need to show that two factorizations
that are semantically equal factor through the same image.

```agda
Δ-hom-im-unique
  : ∀ {m n n' o}
  → (f⁺ : Δ-Hom⁺ n o) (g⁺ : Δ-Hom⁺ n' o) (f⁻ : Δ-Hom⁻ m n) (g⁻ : Δ-Hom⁻ m n')
  → (∀ i → Δ-hom⁺ f⁺ (Δ-hom⁻ f⁻ i) ≡ Δ-hom⁺ g⁺ (Δ-hom⁻ g⁻ i))
  → n ≡ n'
```

<details>
<summary>We can show this with a rather brutal induction.
</summary>

```agda
Δ-hom-im-unique done⁺ done⁺ f⁻ g⁻ p = refl
Δ-hom-im-unique (shift⁺ f⁺) (shift⁺ g⁺) f⁻ g⁻ p =
  Δ-hom-im-unique f⁺ g⁺ f⁻ g⁻ (fsuc-inj ⊙ p)
Δ-hom-im-unique {m = suc m} (shift⁺ f⁺) (keep⁺ g⁺) f⁻ g⁻ p =
  absurd (fsuc≠fzero (p 0 ∙ ap₂ fkeep refl (Δ-hom⁻-zero g⁻)))
Δ-hom-im-unique {m = suc m} (keep⁺ f⁺) (shift⁺ g⁺) f⁻ g⁻ p =
  absurd (fzero≠fsuc (ap₂ fkeep refl (sym (Δ-hom⁻-zero f⁻)) ∙ p 0))
Δ-hom-im-unique (keep⁺ f⁺) (keep⁺ g⁺) (crush⁻ f⁻) (crush⁻ g⁻) p =
  Δ-hom-im-unique (keep⁺ f⁺) (keep⁺ g⁺) f⁻ g⁻ (p ⊙ fsuc)
Δ-hom-im-unique (keep⁺ f⁺) (keep⁺ g⁺) (crush⁻ f⁻) (keep⁻ g⁻) p =
  absurd (fzero≠fsuc (ap₂ fkeep refl (sym (Δ-hom⁻-zero f⁻)) ∙ p 1))
Δ-hom-im-unique (keep⁺ f⁺) (keep⁺ g⁺) (keep⁻ f⁻) (crush⁻ g⁻) p =
  absurd (fsuc≠fzero (p 1 ∙ ap₂ fkeep refl (Δ-hom⁻-zero g⁻)))
Δ-hom-im-unique (keep⁺ f⁺) (keep⁺ g⁺) (keep⁻ f⁻) (keep⁻ g⁻) p =
  ap suc (Δ-hom-im-unique f⁺ g⁺ f⁻ g⁻ (fsuc-inj ⊙ p ⊙ fsuc))
```
</details>

We also need to show that if a pair of factorizations is semantically
equal, then the semi and demisimplicial components are syntactically equal.

```agda
Δ-hom-unique⁺
  : ∀ {m n o}
  → (f⁺ g⁺ : Δ-Hom⁺ n o) (f⁻ g⁻ : Δ-Hom⁻ m n)
  → (∀ (i : Fin m) → ⟦ f⁺ ⟧ (⟦ f⁻ ⟧ i) ≡ ⟦ g⁺ ⟧ (⟦ g⁻ ⟧ i))
  → f⁺ ≡ g⁺
Δ-hom-unique⁻
  : ∀ {m n o}
  → (f⁺ g⁺ : Δ-Hom⁺ n o) (f⁻ g⁻ : Δ-Hom⁻ m n)
  → (∀ (i : Fin m) → ⟦ f⁺ ⟧ (⟦ f⁻ ⟧ i) ≡ ⟦ g⁺ ⟧ (⟦ g⁻ ⟧ i))
  → f⁻ ≡ g⁻
```

<details>
<summary>These follow by some more brutal inductions.
</summary>

```agda
Δ-hom-unique⁺ done⁺ done⁺ f⁻ g⁻ p =
  refl
Δ-hom-unique⁺ (shift⁺ f⁺) (shift⁺ g⁺) f⁻ g⁻ p =
  ap shift⁺ (Δ-hom-unique⁺ f⁺ g⁺ f⁻ g⁻ (fsuc-inj ⊙ p))
Δ-hom-unique⁺ {m = suc m} (shift⁺ f⁺) (keep⁺ g⁺) f⁻ g⁻ p =
  absurd (fsuc≠fzero (p 0 ∙ ap₂ fkeep refl (Δ-hom⁻-zero g⁻)))
Δ-hom-unique⁺ {m = suc m} (keep⁺ f⁺) (shift⁺ g⁺) f⁻ g⁻ p =
  absurd (fzero≠fsuc (sym (ap₂ fkeep refl (Δ-hom⁻-zero f⁻)) ∙ p 0))
Δ-hom-unique⁺ (keep⁺ f⁺) (keep⁺ g⁺) (crush⁻ f⁻) (crush⁻ g⁻) p =
  Δ-hom-unique⁺ (keep⁺ f⁺) (keep⁺ g⁺) f⁻ g⁻ (p ⊙ fsuc)
Δ-hom-unique⁺ (keep⁺ f⁺) (keep⁺ g⁺) (crush⁻ f⁻) (keep⁻ g⁻) p =
  absurd (fzero≠fsuc (sym (ap₂ fkeep refl (Δ-hom⁻-zero f⁻)) ∙ p 1))
Δ-hom-unique⁺ (keep⁺ f⁺) (keep⁺ g⁺) (keep⁻ f⁻) (crush⁻ g⁻) p =
  absurd (fsuc≠fzero (p 1 ∙ ap₂ fkeep refl (Δ-hom⁻-zero g⁻)))
Δ-hom-unique⁺ (keep⁺ f⁺) (keep⁺ g⁺) (keep⁻ f⁻) (keep⁻ g⁻) p =
  ap keep⁺ (Δ-hom-unique⁺ f⁺ g⁺ f⁻ g⁻ (fsuc-inj ⊙ p ⊙ fsuc))

Δ-hom-unique⁻ f⁺ g⁺ done⁻ done⁻ p =
  refl
Δ-hom-unique⁻ f⁺ g⁺ (crush⁻ f⁻) (crush⁻ g⁻) p =
  ap crush⁻ (Δ-hom-unique⁻ f⁺ g⁺ f⁻ g⁻ (p ⊙ fsuc))
Δ-hom-unique⁻ f⁺ g⁺ (crush⁻ f⁻) (keep⁻ g⁻) p =
  absurd (fzero≠fsuc (Δ-hom⁺-to-inj g⁺ (sym (p 0) ∙ p 1)))
Δ-hom-unique⁻ f⁺ g⁺ (keep⁻ f⁻) (crush⁻ g⁻) p =
  absurd (fzero≠fsuc (Δ-hom⁺-to-inj f⁺ (p 0 ∙ sym (p 1))))
Δ-hom-unique⁻ (shift⁺ f⁺) (shift⁺ g⁺) (keep⁻ f⁻) (keep⁻ g⁻) p =
  Δ-hom-unique⁻ f⁺ g⁺ (keep⁻ f⁻) (keep⁻ g⁻) (fsuc-inj ⊙ p)
Δ-hom-unique⁻ (shift⁺ f⁺) (keep⁺ g⁺) (keep⁻ f⁻) (keep⁻ g⁻) p =
  absurd (fsuc≠fzero (p 0))
Δ-hom-unique⁻ (keep⁺ f⁺) (shift⁺ g⁺) (keep⁻ f⁻) (keep⁻ g⁻) p =
  absurd (fzero≠fsuc (p 0))
Δ-hom-unique⁻ (keep⁺ f⁺) (keep⁺ g⁺) (keep⁻ f⁻) (keep⁻ g⁻) p =
  ap keep⁻ (Δ-hom-unique⁻ f⁺ g⁺ f⁻ g⁻ (fsuc-inj ⊙ p ⊙ fsuc))
```
</details>

<!--
```agda
Δ-hom-uniquep⁺
  : ∀ {m n' n o}
  → {p : n ≡ n'}
  → (f⁺ : Δ-Hom⁺ n o) (g⁺ : Δ-Hom⁺ n' o) (f⁻ : Δ-Hom⁻ m n) (g⁻ : Δ-Hom⁻ m n')
  → (∀ (i : Fin m) → ⟦ f⁺ ⟧ (⟦ f⁻ ⟧ i) ≡ ⟦ g⁺ ⟧ (⟦ g⁻ ⟧ i))
  → PathP (λ i → Δ-Hom⁺ (p i) o) f⁺ g⁺
Δ-hom-uniquep⁺ {m = m} {o = o} {p = p} =
  J' (λ n n' p →
    ∀ (f⁺ : Δ-Hom⁺ n o) (g⁺ : Δ-Hom⁺ n' o) (f⁻ : Δ-Hom⁻ m n) (g⁻ : Δ-Hom⁻ m n')
    → (∀ i → Δ-hom⁺ f⁺ (Δ-hom⁻ f⁻ i) ≡ Δ-hom⁺ g⁺ (Δ-hom⁻ g⁻ i))
    → PathP (λ i → Δ-Hom⁺ (p i) o) f⁺ g⁺)
    (λ _ → Δ-hom-unique⁺)
    p

Δ-hom-uniquep⁻
  : ∀ {m n' n o}
  → {p : n ≡ n'}
  → (f⁺ : Δ-Hom⁺ n o) (g⁺ : Δ-Hom⁺ n' o) (f⁻ : Δ-Hom⁻ m n) (g⁻ : Δ-Hom⁻ m n')
  → (∀ (i : Fin m) → ⟦ f⁺ ⟧ (⟦ f⁻ ⟧ i) ≡ ⟦ g⁺ ⟧ (⟦ g⁻ ⟧ i))
  → PathP (λ i → Δ-Hom⁻ m (p i)) f⁻ g⁻
Δ-hom-uniquep⁻ {m = m} {o = o} {p = p} =
  J' (λ n n' p →
    ∀ (f⁺ : Δ-Hom⁺ n o) (g⁺ : Δ-Hom⁺ n' o) (f⁻ : Δ-Hom⁻ m n) (g⁻ : Δ-Hom⁻ m n')
    → (∀ i → Δ-hom⁺ f⁺ (Δ-hom⁻ f⁻ i) ≡ Δ-hom⁺ g⁺ (Δ-hom⁻ g⁻ i))
    → PathP (λ i → Δ-Hom⁻ m (p i)) f⁻ g⁻)
    (λ _ → Δ-hom-unique⁻)
    p
```
-->

Injectivity of the interpretation of simplicial maps follows
directly from these lemmas.

```agda
Δ-hom-inj
  : ∀ (f g : Δ-Hom m n)
  → (∀ i → ⟦ f ⟧ i ≡ ⟦ g ⟧ i)
  → f ≡ g
Δ-hom-inj {m} {n} f g p =
  Δ-Hom-path (Δ-hom-im-unique (f .hom⁺) (g .hom⁺) (f .hom⁻) (g .hom⁻) p)
    (Δ-hom-uniquep⁺ (f .hom⁺) (g .hom⁺) (f .hom⁻) (g .hom⁻) p)
    (Δ-hom-uniquep⁻ (f .hom⁺) (g .hom⁺) (f .hom⁻) (g .hom⁻) p)
```

Injectivity the interpretation of semi and demisimplicial maps follow
neatly as corollaries.

```agda
Δ-hom⁺-inj
  : ∀ (f⁺ g⁺ : Δ-Hom⁺ m n)
  → (∀ i → ⟦ f⁺ ⟧ i ≡ ⟦ g⁺ ⟧ i)
  → f⁺ ≡ g⁺
Δ-hom⁺-inj f⁺ g⁺ p = Δ-hom-unique⁺ f⁺ g⁺ id⁻ id⁻ (p ⊙ Δ-hom⁻ id⁻)

Δ-hom⁻-inj
  : ∀ (f⁻ g⁻ : Δ-Hom⁻ m n)
  → (∀ i → ⟦ f⁻ ⟧ i ≡ ⟦ g⁻ ⟧ i)
  → f⁻ ≡ g⁻
Δ-hom⁻-inj f⁻ g⁻ p = Δ-hom-unique⁻ id⁺ id⁺ f⁻ g⁻ (ap (Δ-hom⁺ id⁺) ⊙ p)
```

<!--
```agda
instance
  Extensional-Δ-Hom⁺
    : ∀ {m n ℓr}
    → ⦃ e : Extensional (Fin m → Fin n) ℓr ⦄
    → Extensional (Δ-Hom⁺ m n) ℓr
  Extensional-Δ-Hom⁺ ⦃ e ⦄ =
    injection→extensional! {f = Δ-hom⁺}
      (λ {f} {g} p → Δ-hom⁺-inj f g (happly p)) e

  Extensional-Δ-Hom⁻
    : ∀ {m n ℓr}
    → ⦃ e : Extensional (Fin m → Fin n) ℓr ⦄
    → Extensional (Δ-Hom⁻ m n) ℓr
  Extensional-Δ-Hom⁻ ⦃ e ⦄ =
    injection→extensional! {f = Δ-hom⁻}
      (λ {f} {g} p → Δ-hom⁻-inj f g (happly p)) e

  Extensional-Δ-Hom
    : ∀ {m n ℓr}
    → ⦃ e : Extensional (Fin m → Fin n) ℓr ⦄
    → Extensional (Δ-Hom m n) ℓr
  Extensional-Δ-Hom ⦃ e ⦄ =
    injection→extensional! {f = Δ-hom}
      (λ {f} {g} p → Δ-hom-inj f g (happly p)) e
```
-->

### Functoriality of interpretations

Finally, we shall prove functoriality of all of our interpretations.

Identities are mercifully simple.

```agda
Δ-hom⁺-id : ∀ (i : Fin m) → ⟦ id⁺ ⟧ i ≡ i
Δ-hom⁺-id fzero = refl
Δ-hom⁺-id (fsuc i) = ap fsuc (Δ-hom⁺-id i)

Δ-hom⁻-id : ∀ (i : Fin m) → ⟦ id⁻ ⟧ i ≡ i
Δ-hom⁻-id fzero = refl
Δ-hom⁻-id (fsuc i) = ap fsuc (Δ-hom⁻-id i)

Δ-hom-id : ∀ (i : Fin m) → ⟦ idΔ ⟧ i ≡ i
Δ-hom-id i = ap ⟦ id⁺ ⟧ (Δ-hom⁻-id i) ∙ Δ-hom⁺-id i
```

Composites of semi and demisimplicial maps are decidedly less easy.

```agda
Δ-hom⁺-∘
  : (f : Δ-Hom⁺ n o) (g : Δ-Hom⁺ m n)
  → ∀ (i : Fin m) → ⟦ f ∘⁺ g ⟧ i ≡ ⟦ f ⟧ (⟦ g ⟧ i)
Δ-hom⁻-∘
  : (f : Δ-Hom⁻ n o) (g : Δ-Hom⁻ m n)
  → ∀ (i : Fin m) → ⟦ f ∘⁻ g ⟧ i ≡ ⟦ f ⟧ (⟦ g ⟧ i)
```

<details>
<summary>The proofs are not particularly difficult; they both
consist of some (rather large) case bashes.
</summary>

```agda
Δ-hom⁺-∘ done⁺ done⁺ i = fabsurd i
Δ-hom⁺-∘ (shift⁺ f) (shift⁺ g) i = ap fsuc (Δ-hom⁺-∘ f (shift⁺ g) i)
Δ-hom⁺-∘ (shift⁺ f) (keep⁺ g) i = ap fsuc (Δ-hom⁺-∘ f (keep⁺ g) i)
Δ-hom⁺-∘ (keep⁺ f) (shift⁺ g) i = ap fsuc (Δ-hom⁺-∘ f g i)
Δ-hom⁺-∘ (keep⁺ f) (keep⁺ g) fzero = refl
Δ-hom⁺-∘ (keep⁺ f) (keep⁺ g) (fsuc i) = ap fsuc (Δ-hom⁺-∘ f g i)

Δ-hom⁻-∘ done⁻ (crush⁻ g) i = sym (Δ-hom⁻-id (Δ-hom⁻ (crush⁻ g) i))
Δ-hom⁻-∘ (crush⁻ f) (crush⁻ g) i = Δ-hom⁻-∘ (crush⁻ f) g (fpred i)
Δ-hom⁻-∘ (crush⁻ f) (keep⁻ (crush⁻ g)) fzero =
  Δ-hom⁻ (f ∘⁻ g) fzero     ≡⟨ Δ-hom⁻-∘ f g fzero ⟩
  Δ-hom⁻ f (Δ-hom⁻ g fzero) ≡⟨ ap (Δ-hom⁻ f) (Δ-hom⁻-zero g) ⟩
  Δ-hom⁻ f fzero ∎
Δ-hom⁻-∘ (crush⁻ f) (keep⁻ (crush⁻ g)) (fsuc i) = Δ-hom⁻-∘ f g (fpred i)
Δ-hom⁻-∘ (crush⁻ f) (keep⁻ (keep⁻ g)) fzero =
  Δ-hom⁻ (f ∘⁻ keep⁻ g) fzero     ≡⟨ Δ-hom⁻-∘ f (keep⁻ g) fzero ⟩
  Δ-hom⁻ f fzero ∎
Δ-hom⁻-∘ (crush⁻ f) (keep⁻ (keep⁻ g)) (fsuc i) = Δ-hom⁻-∘ f (keep⁻ g) i
Δ-hom⁻-∘ (keep⁻ f) (crush⁻ g) i = Δ-hom⁻-∘ (keep⁻ f) g (fpred i)
Δ-hom⁻-∘ (keep⁻ f) (keep⁻ g) fzero = refl
Δ-hom⁻-∘ (keep⁻ f) (keep⁻ g) (fsuc i) = ap fsuc (Δ-hom⁻-∘ f g i)
```
</details>

Composites of simplicial maps are the most difficult of the bunch. The key lemma
is that the interpretation of the of $f^{-} \circ g^{+}$ is functorial, which
follows from yet another painful induction.

```agda
Δ-hom⁺⁻-comm
  : ∀ (f⁻ : Δ-Hom⁻ n o) (f⁺ : Δ-Hom⁺ m n)
  → ∀ (i : Fin m) → ⟦ f⁻ ∘Δ⁺ f⁺ ⟧ (⟦ f⁻ ∘Δ⁻ f⁺ ⟧ i) ≡ ⟦ f⁻ ⟧ (⟦ f⁺ ⟧ i)
```

<details>
<summary>There really is no intuition to be gained from the proof, so we omit it.
</summary>
```agda
Δ-hom⁺⁻-comm done⁻ done⁺ i = fabsurd i
Δ-hom⁺⁻-comm (crush⁻ f⁻) (shift⁺ f⁺) i = Δ-hom⁺⁻-comm f⁻ f⁺ i
Δ-hom⁺⁻-comm (crush⁻ f⁻) (keep⁺ (shift⁺ f⁺)) fzero = Δ-hom⁺⁻-comm f⁻ (keep⁺ f⁺) fzero
Δ-hom⁺⁻-comm (crush⁻ f⁻) (keep⁺ (shift⁺ f⁺)) (fsuc i) = Δ-hom⁺⁻-comm f⁻ (keep⁺ f⁺) (fsuc i)
Δ-hom⁺⁻-comm (crush⁻ f⁻) (keep⁺ (keep⁺ f⁺)) fzero = Δ-hom⁺⁻-comm f⁻ (keep⁺ f⁺) fzero
Δ-hom⁺⁻-comm (crush⁻ f⁻) (keep⁺ (keep⁺ f⁺)) (fsuc fzero) = Δ-hom⁺⁻-comm f⁻ (keep⁺ f⁺) fzero
Δ-hom⁺⁻-comm (crush⁻ f⁻) (keep⁺ (keep⁺ f⁺)) (fsuc (fsuc i)) = Δ-hom⁺⁻-comm f⁻ (keep⁺ f⁺) (fsuc i)
Δ-hom⁺⁻-comm (keep⁻ f⁻) (shift⁺ f⁺) i = ap fsuc (Δ-hom⁺⁻-comm f⁻ f⁺ i)
Δ-hom⁺⁻-comm (keep⁻ f⁻) (keep⁺ f⁺) fzero = refl
Δ-hom⁺⁻-comm (keep⁻ f⁻) (keep⁺ f⁺) (fsuc i) = ap fsuc (Δ-hom⁺⁻-comm f⁻ f⁺ i)
```
</details>

Luckily, that was our last big induction, and we can get our final functoriality
lemma by piecing together previous results!

```agda
Δ-hom-∘
  : (f : Δ-Hom n o) (g : Δ-Hom m n)
  → ∀ (i : Fin m) → ⟦ (f ∘Δ g) ⟧ i ≡ ⟦ f ⟧ (⟦ g ⟧ i)
Δ-hom-∘ f g i =
  ⟦ f .hom⁺ ∘⁺ (f .hom⁻ ∘Δ⁺ g .hom⁺) ⟧ (⟦ (f .hom⁻ ∘Δ⁻ g .hom⁺) ∘⁻ g .hom⁻ ⟧ i)     ≡⟨ Δ-hom⁺-∘ (f .hom⁺) (f .hom⁻ ∘Δ⁺ g .hom⁺) (⟦ (f .hom⁻ ∘Δ⁻ g .hom⁺) ∘⁻ g .hom⁻ ⟧ i) ⟩
  ⟦ f .hom⁺ ⟧ (⟦ f .hom⁻ ∘Δ⁺ g .hom⁺ ⟧ (⟦ (f .hom⁻ ∘Δ⁻ g .hom⁺) ∘⁻ g .hom⁻ ⟧ i))    ≡⟨ ap (⟦ f .hom⁺ ⟧ ⊙ ⟦ f .hom⁻ ∘Δ⁺ g .hom⁺ ⟧) (Δ-hom⁻-∘ (f .hom⁻ ∘Δ⁻ g .hom⁺) (g .hom⁻) i) ⟩
  ⟦ f .hom⁺ ⟧ (⟦ f .hom⁻ ∘Δ⁺ g .hom⁺ ⟧ (⟦ (f .hom⁻ ∘Δ⁻ g .hom⁺) ⟧ (⟦ g .hom⁻ ⟧ i))) ≡⟨ ap ⟦ f .hom⁺ ⟧ ( Δ-hom⁺⁻-comm (f .hom⁻) (g .hom⁺) (⟦ g .hom⁻ ⟧ i)) ⟩
  ⟦ f .hom⁺ ⟧ (⟦ f .hom⁻ ⟧ (⟦ g .hom⁺ ⟧ (⟦ g .hom⁻ ⟧ i))) ∎
```

## Categories

With all that hard work behind us, it is time to enjoy the fruit
of our labor. All of our putative categories
(both augmented and non-augmented) are equipped with injective functorial
interpretations into functions between sets, which means that they are
bona-fide [[concrete categories]].

```agda
Δₐ⁺-concrete : make-concrete Nat Δ-Hom⁺
Δₐ⁻-concrete : make-concrete Nat Δ-Hom⁻
Δₐ-concrete : make-concrete Nat Δ-Hom

Δ⁺-concrete : make-concrete Nat (λ m n → Δ-Hom⁺ (suc m) (suc n))
Δ⁻-concrete : make-concrete Nat (λ m n → Δ-Hom⁻ (suc m) (suc n))
Δ-concrete : make-concrete Nat (λ m n → Δ-Hom (suc m) (suc n))
```

<details>
<summary>We already have all the results we need, so proving that they
are concrete is just an exercise in building records.
</summary>
```agda
Δₐ⁺-concrete .make-concrete.id = id⁺
Δₐ⁺-concrete .make-concrete._∘_ = _∘⁺_
Δₐ⁺-concrete .make-concrete.lvl = lzero
Δₐ⁺-concrete .make-concrete.F₀ = Fin
Δₐ⁺-concrete .make-concrete.F₀-is-set = hlevel 2
Δₐ⁺-concrete .make-concrete.F₁ = Δ-hom⁺
Δₐ⁺-concrete .make-concrete.F₁-inj = Δ-hom⁺-inj _ _
Δₐ⁺-concrete .make-concrete.F-id = Δ-hom⁺-id
Δₐ⁺-concrete .make-concrete.F-∘ = Δ-hom⁺-∘

Δₐ⁻-concrete .make-concrete.id = id⁻
Δₐ⁻-concrete .make-concrete._∘_ = _∘⁻_
Δₐ⁻-concrete .make-concrete.lvl = lzero
Δₐ⁻-concrete .make-concrete.F₀ = Fin
Δₐ⁻-concrete .make-concrete.F₀-is-set = hlevel 2
Δₐ⁻-concrete .make-concrete.F₁ = Δ-hom⁻
Δₐ⁻-concrete .make-concrete.F₁-inj = Δ-hom⁻-inj _ _
Δₐ⁻-concrete .make-concrete.F-id = Δ-hom⁻-id
Δₐ⁻-concrete .make-concrete.F-∘ = Δ-hom⁻-∘

Δₐ-concrete .make-concrete.id = idΔ
Δₐ-concrete .make-concrete._∘_ = _∘Δ_
Δₐ-concrete .make-concrete.lvl = lzero
Δₐ-concrete .make-concrete.F₀ = Fin
Δₐ-concrete .make-concrete.F₀-is-set = hlevel 2
Δₐ-concrete .make-concrete.F₁ = Δ-hom
Δₐ-concrete .make-concrete.F₁-inj = Δ-hom-inj _ _
Δₐ-concrete .make-concrete.F-id = Δ-hom-id
Δₐ-concrete .make-concrete.F-∘ = Δ-hom-∘

Δ⁺-concrete .make-concrete.id = id⁺
Δ⁺-concrete .make-concrete._∘_ = _∘⁺_
Δ⁺-concrete .make-concrete.lvl = lzero
Δ⁺-concrete .make-concrete.F₀ n = Fin (suc n)
Δ⁺-concrete .make-concrete.F₀-is-set = hlevel 2
Δ⁺-concrete .make-concrete.F₁ = Δ-hom⁺
Δ⁺-concrete .make-concrete.F₁-inj = Δ-hom⁺-inj _ _
Δ⁺-concrete .make-concrete.F-id = Δ-hom⁺-id
Δ⁺-concrete .make-concrete.F-∘ = Δ-hom⁺-∘

Δ⁻-concrete .make-concrete.id = id⁻
Δ⁻-concrete .make-concrete._∘_ = _∘⁻_
Δ⁻-concrete .make-concrete.lvl = lzero
Δ⁻-concrete .make-concrete.F₀ n = Fin (suc n)
Δ⁻-concrete .make-concrete.F₀-is-set = hlevel 2
Δ⁻-concrete .make-concrete.F₁ = Δ-hom⁻
Δ⁻-concrete .make-concrete.F₁-inj = Δ-hom⁻-inj _ _
Δ⁻-concrete .make-concrete.F-id = Δ-hom⁻-id
Δ⁻-concrete .make-concrete.F-∘ = Δ-hom⁻-∘

Δ-concrete .make-concrete.id = idΔ
Δ-concrete .make-concrete._∘_ = _∘Δ_
Δ-concrete .make-concrete.lvl = lzero
Δ-concrete .make-concrete.F₀ n = Fin (suc n)
Δ-concrete .make-concrete.F₀-is-set = hlevel 2
Δ-concrete .make-concrete.F₁ = Δ-hom
Δ-concrete .make-concrete.F₁-inj = Δ-hom-inj _ _
Δ-concrete .make-concrete.F-id = Δ-hom-id
Δ-concrete .make-concrete.F-∘ = Δ-hom-∘
```
</details>

A bit of metaprogramming gives a definition of the
(augmented (demi/semi)) simplex category that will result in pretty
goals.

```agda
Δₐ⁺ : Precategory lzero lzero
Δₐ⁻ : Precategory lzero lzero
Δₐ : Precategory lzero lzero

unquoteDef Δₐ⁺ = define-concrete-category Δₐ⁺ Δₐ⁺-concrete
unquoteDef Δₐ⁻ = define-concrete-category Δₐ⁻ Δₐ⁻-concrete
unquoteDef Δₐ = define-concrete-category Δₐ Δₐ-concrete

Δ⁺ : Precategory lzero lzero
Δ⁻ : Precategory lzero lzero
Δ : Precategory lzero lzero

unquoteDef Δ⁺ = define-concrete-category Δ⁺ Δ⁺-concrete
unquoteDef Δ⁻ = define-concrete-category Δ⁻ Δ⁻-concrete
unquoteDef Δ = define-concrete-category Δ Δ-concrete

module Δₐ⁺ = Cat.Reasoning Δₐ⁺
module Δₐ⁻ = Cat.Reasoning Δₐ⁻
module Δₐ = Cat.Reasoning Δₐ

module Δ⁺ = Cat.Reasoning Δ⁺
module Δ⁻ = Cat.Reasoning Δ⁻
module Δ = Cat.Reasoning Δ
```

## Univalence

All of the various semi/demi/augmented simplex categories are univalent,
though this is somewhat non-trivial to show. The proof will consist of 3
major steps:
1. Every map that does not contain a `shift⁺`{.Agda} or a `crush⁻`{.Agda} constructor
  preserves dimension.
2. Every semi/demisimplicial endomap is an identity.
3. A map is is interpreted as an equivalence if and only if it does not
  contain any `shift⁺`{.Agda} or a `crush⁻`{.Agda} constructors.

Once we have these 3 pieces, we can show that every isomorphism is an
equivalence, so it cannot contain `shift⁺`{.Agda} or a `crush⁻`{.Agda}
constructors. This means that the image of every factorization of an
isomorphism must have the same dimension as both endpoints, so both
the semi/demisimplicial components of the factorization are endomaps,
and thus identities.

Filling out this proof sketch will involve quite a bit of work, so
let's get to it!

### Dimension

First, note that every semisimplicial map raises the dimension, and
every demisimplicial map lowers it.

```agda
Δ-dim⁺-≤ : ∀ {m n} → (f : Δ-Hom⁺ m n) → m Nat.≤ n
Δ-dim⁺-≤ done⁺ = Nat.0≤x
Δ-dim⁺-≤ (shift⁺ f) = Nat.≤-sucr (Δ-dim⁺-≤ f)
Δ-dim⁺-≤ (keep⁺ f) = Nat.s≤s (Δ-dim⁺-≤ f)

Δ-dim⁻-≤ : ∀ {m n} → (f : Δ-Hom⁻ m n) → n Nat.≤ m
Δ-dim⁻-≤ done⁻ = Nat.0≤x
Δ-dim⁻-≤ (crush⁻ f) = Nat.≤-sucr (Δ-dim⁻-≤ f)
Δ-dim⁻-≤ (keep⁻ f) = Nat.s≤s (Δ-dim⁻-≤ f)
```

We can tighten these bounds if $f$ contains a `shift⁺`{.Agda} or a
`crush⁻`{.Agda} constructor.

```agda
has-shift⁺ : ∀ {m n} → Δ-Hom⁺ m n → Type
has-shift⁺ done⁺ = ⊥
has-shift⁺ (shift⁺ f) = ⊤
has-shift⁺ (keep⁺ f) = has-shift⁺ f

has-crush⁻ : ∀ {m n} → Δ-Hom⁻ m n → Type
has-crush⁻ done⁻ = ⊥
has-crush⁻ (crush⁻ f) = ⊤
has-crush⁻ (keep⁻ f) = has-crush⁻ f

has-shift : ∀ {m n} → Δ-Hom m n → Type
has-shift f = has-shift⁺ (f .hom⁺)

has-crush : ∀ {m n} → Δ-Hom m n → Type
has-crush f = has-crush⁻ (f .hom⁻)

Δ-dim⁺-< : ∀ {m n} → (f : Δ-Hom⁺ m n) → has-shift⁺ f → m Nat.< n
Δ-dim⁺-< (shift⁺ f) p = Nat.s≤s (Δ-dim⁺-≤ f)
Δ-dim⁺-< (keep⁺ f) p = Nat.s≤s (Δ-dim⁺-< f p)

Δ-dim⁻-< : ∀ {m n} → (f : Δ-Hom⁻ m n) → has-crush⁻ f → n Nat.< m
Δ-dim⁻-< (crush⁻ f) p = Nat.s≤s (Δ-dim⁻-≤ f)
Δ-dim⁻-< (keep⁻ f) p = Nat.s≤s (Δ-dim⁻-< f p)
```

The converse is also true; if $f$ strictly raises or lowers the dimension
then contains a `shift⁺`{.Agda} or a `crush⁻`{.Agda} constructor.

```agda
Δ-dim⁺-<-has-shift⁺
  : ∀ (f⁺ : Δ-Hom⁺ m n)
  → m Nat.< n
  → has-shift⁺ f⁺
Δ-dim⁺-<-has-shift⁺ (shift⁺ f⁺) m<n = tt
Δ-dim⁺-<-has-shift⁺ (keep⁺ f⁺) m<n = Δ-dim⁺-<-has-shift⁺ f⁺ (Nat.≤-peel m<n)

Δ-dim⁻-<-has-crush⁻
  : ∀ (f⁻ : Δ-Hom⁻ m n)
  → n Nat.< m
  → has-crush⁻ f⁻
Δ-dim⁻-<-has-crush⁻ (crush⁻ f) n<m = tt
Δ-dim⁻-<-has-crush⁻ (keep⁻ f) n<m = Δ-dim⁻-<-has-crush⁻ f (Nat.≤-peel n<m)
```

Additionally, if $f$ does not contain any `shift⁺`{.Agda} or `crush⁻`{.Agda}
constructors, then it must preserve the dimension. This concludes step 1!

```agda
no-shift⁺→dim-stable
  : ∀ (f⁺ : Δ-Hom⁺ m n)
  → ¬ (has-shift⁺ f⁺)
  → m ≡ n
no-shift⁺→dim-stable done⁺ no-shift = refl
no-shift⁺→dim-stable (shift⁺ f⁺) no-shift = absurd (no-shift tt)
no-shift⁺→dim-stable (keep⁺ f⁺) no-shift = ap suc (no-shift⁺→dim-stable f⁺ no-shift)

no-crush⁻→dim-stable
  : ∀ (f⁻ : Δ-Hom⁻ m n)
  → ¬ (has-crush⁻ f⁻)
  → m ≡ n
no-crush⁻→dim-stable done⁻ no-crush = refl
no-crush⁻→dim-stable (crush⁻ f⁻) no-crush = absurd (no-crush tt)
no-crush⁻→dim-stable (keep⁻ f⁻) no-crush = ap suc (no-crush⁻→dim-stable f⁻ no-crush)

no-shift+no-crush→dim-stable
  : ∀ (f : Δ-Hom m n)
  → ¬ (has-shift f) → ¬ (has-crush f)
  → m ≡ n
no-shift+no-crush→dim-stable f no-shift no-crush =
  no-crush⁻→dim-stable (f .hom⁻) no-crush
  ∙ no-shift⁺→dim-stable (f .hom⁺) no-shift
```

Luckily, the second step of the proof is much easier: an semi/demisimplicial
endomap cannot have `shift⁺`{.Agda} or `crush⁻`{.Agda} constructors, as
they would raise/lower the dimension!

```agda
Δ-endo⁺-id : ∀ (f : Δ-Hom⁺ n n) → f ≡ id⁺
Δ-endo⁺-id done⁺ = refl
Δ-endo⁺-id (shift⁺ f) = absurd (Nat.¬sucx≤x _ (Δ-dim⁺-≤ f))
Δ-endo⁺-id (keep⁺ f) = ap keep⁺ (Δ-endo⁺-id f)

Δ-endo⁻-id : ∀ (f : Δ-Hom⁻ n n) → f ≡ id⁻
Δ-endo⁻-id done⁻ = refl
Δ-endo⁻-id (crush⁻ f) = absurd (Nat.¬sucx≤x _ (Δ-dim⁻-≤ f))
Δ-endo⁻-id (keep⁻ f) = ap keep⁻ (Δ-endo⁻-id f)
```

<!--
```agda
Δ-endo⁺-idp
  : ∀ {p : m ≡ n} (f⁺ : Δ-Hom⁺ m n)
  → PathP (λ i → Δ-Hom⁺ (p i) n) f⁺ id⁺
Δ-endo⁺-idp {m = m} {p = p} f⁺ =
  J (λ n p → ∀ (f⁺ : Δ-Hom⁺ m n) → PathP (λ i → Δ-Hom⁺ (p i) n) f⁺ id⁺)
    Δ-endo⁺-id p
    f⁺

Δ-endo⁻-idp
  : ∀ {p : n ≡ m} (f⁻ : Δ-Hom⁻ m n)
  → PathP (λ i → Δ-Hom⁻ m (p i)) f⁻ id⁻
Δ-endo⁻-idp {n = n} {p = p} f⁻ =
  J (λ m p → ∀ (f⁻ : Δ-Hom⁻ m n) → PathP (λ i → Δ-Hom⁻ m (p i)) f⁻ id⁻)
    Δ-endo⁻-id p
    f⁻
```
-->

At this point, we already have enough results to show that the
(augmented) semi and demisimplex categories are univalent! We
will only focus on the augmented semisimplex category, as all the
other cases are more are less identical.

The key insight is that we can get a path $m = n$ from a pair of
semisimplicial maps $[m] \to [n], [n] \to [m]$ by appealing to
our antisymmetry.

```agda
Δ-hom⁺-pair-dim
  : ∀ (f : Δ-Hom⁺ m n) (f⁻¹ : Δ-Hom⁺ n m)
  → m ≡ n
Δ-hom⁺-pair-dim f f⁻¹ = Nat.≤-antisym (Δ-dim⁺-≤ f) (Δ-dim⁺-≤ f⁻¹)
```

This gives us a way to turn isomorphisms in $\Delta_{a}^{+}$ into
paths, and there is a unique automorphism, so $\Delta_{a}^{+}$ must
be univalent.

```agda
Δₐ⁺-is-category : is-category Δₐ⁺
Δₐ⁺-is-category =
  set-identity-system-K
    (λ n f → Δₐ⁺.≅-path (Δ-endo⁺-id (Δₐ⁺.to f)))
    (λ f →  Δ-hom⁺-pair-dim (Δₐ⁺.to f) (Δₐ⁺.from f))
```

<!--
```agda
Δ-hom⁻-pair-dim
  : ∀ (f : Δ-Hom⁻ m n) (f⁻¹ : Δ-Hom⁻ n m)
  → m ≡ n
Δ-hom⁻-pair-dim f f⁻¹ = Nat.≤-antisym (Δ-dim⁻-≤ f⁻¹) (Δ-dim⁻-≤ f)

Δₐ⁻-is-category : is-category Δₐ⁻
Δₐ⁻-is-category =
  set-identity-system-K
    (λ n f → Δₐ⁻.≅-path (Δ-endo⁻-id (Δₐ⁻.to f)))
    (λ f →  Δ-hom⁻-pair-dim (Δₐ⁻.to f) (Δₐ⁻.from f))

Δ⁺-is-category : is-category Δ⁺
Δ⁺-is-category =
  set-identity-system-K
    (λ n f → Δ⁺.≅-path (Δ-endo⁺-id (Δ⁺.to f)))
    (λ f → Nat.suc-inj (Δ-hom⁺-pair-dim (Δ⁺.to f) (Δ⁺.from f)))

Δ⁻-is-category : is-category Δ⁻
Δ⁻-is-category =
  set-identity-system-K
    (λ n f → Δ⁻.≅-path (Δ-endo⁻-id (Δ⁻.to f)))
    (λ f → Nat.suc-inj (Δ-hom⁻-pair-dim (Δ⁻.to f) (Δ⁻.from f)))
```
-->

Unfortunately, simplicial maps require an additional step. Our goal is to
characterise the morphisms that get interpreted as equivalence, but we will
do this in a somewhat roundabout way: instead of characterizing equivalences, we
will characterize everything that is *not* an equivalence!

In particular, we our goal is to show that a morphism is an equivalence if
and only if it does not contain any `shift⁺`{.Agda} or a `crush⁻`{.Agda}
constructor. However, doing so will require characterizing morphisms that *do*
contain these constructors. First, note that if a semisimplicial map $f$
contains a `shift⁺`{.Agda}, then it is [[split antisurjective]], as we can
find an element in the codomain that is not in the image of $f$.

```agda
shift⁺-split-antisurj
  : ∀ (f⁺ : Δ-Hom⁺ m n)
  → split-antisurjective ⟦ shift⁺ f⁺ ⟧
shift⁺-split-antisurj f⁺ = fzero , fsuc≠fzero ⊙ snd

has-shift⁺→split-antisurj
  : ∀ (f⁺ : Δ-Hom⁺ m n)
  → has-shift⁺ f⁺
  → split-antisurjective ⟦ f⁺ ⟧
has-shift⁺→split-antisurj (shift⁺ f⁺) shift =
  shift⁺-split-antisurj f⁺
has-shift⁺→split-antisurj (keep⁺ f⁺) shift =
  fkeep-split-antisurj (has-shift⁺→split-antisurj f⁺ shift)
```

Similarly, if a demisimplicial map $f$ contains a `crush⁻`, then it
is [[split antiinjective]], as we can find a fibre that contains at
least 2 distinct elements. The proof of this is a bit tricky though:
we need to observe that there are no demisimplicial maps $[1 + n] \to [0]$.

<!--
```agda
Δ-hom⁺-zero-strict : ¬ (Δ-Hom⁺ (suc n) 0)
Δ-hom⁺-zero-strict ()

Δ-hom⁻-no-initial : ¬ (Δ-Hom⁻ 0 (suc n))
Δ-hom⁻-no-initial ()
```
-->

```agda
Δ-hom⁻-zero-strict : ¬ (Δ-Hom⁻ (suc n) 0)
Δ-hom⁻-zero-strict (crush⁻ f⁻) = Δ-hom⁻-zero-strict f⁻

crush⁻-split-antiinj
  : ∀ (f⁻ : Δ-Hom⁻ (suc m) n)
  → split-antiinjective ⟦ crush⁻ f⁻ ⟧
crush⁻-split-antiinj {n = zero} f⁻ = absurd (Δ-hom⁻-zero-strict f⁻)
crush⁻-split-antiinj {n = suc n} f⁻ = antiinj where
  open split-antiinjective

  antiinj : split-antiinjective (⟦ f⁻ ⟧ ⊙ fpred)
  antiinj .pt = 0
  antiinj .x₀ = 0
  antiinj .x₁ = 1
  antiinj .map-to₀ = Δ-hom⁻-zero f⁻
  antiinj .map-to₁ = Δ-hom⁻-zero f⁻
  antiinj .distinct = fzero≠fsuc

has-crush⁻→split-antiinj
  : ∀ (f⁻ : Δ-Hom⁻ m n)
  → has-crush⁻ f⁻
  → split-antiinjective ⟦ f⁻ ⟧
has-crush⁻→split-antiinj (crush⁻ f⁻) degen = crush⁻-split-antiinj f⁻
has-crush⁻→split-antiinj (keep⁻ f⁻) degen =
  fkeep-split-antiinj (has-crush⁻→split-antiinj f⁻ degen)
```

The converse also holds: if $f$ is split antisurjective or antiinjective,
then $f$ has a `shift⁺`{.Agda} or a `crush⁻`{.Agda}.

```agda
split-antisurj→has-shift⁺
  : ∀ (f⁺ : Δ-Hom⁺ m n)
  → split-antisurjective ⟦ f⁺ ⟧
  → has-shift⁺ f⁺
split-antisurj→has-shift⁺ (shift⁺ f⁺) antisurj = tt
split-antisurj→has-shift⁺ (keep⁺ f⁺) antisurj =
  split-antisurj→has-shift⁺ f⁺ (fkeep-reflect-split-antisurj antisurj)

split-antiinj→has-crush⁻
  : ∀ (f⁻ : Δ-Hom⁻ m n)
  → split-antiinjective ⟦ f⁻ ⟧
  → has-crush⁻ f⁻
split-antiinj→has-crush⁻ done⁻ antiinj = fabsurd (antiinj .pt)
split-antiinj→has-crush⁻ (crush⁻ f⁻) antiinj = tt
split-antiinj→has-crush⁻ (keep⁻ f⁻) antiinj =
  split-antiinj→has-crush⁻ f⁻ (fkeep-reflect-split-antiinj antiinj)
```

Split antiinjective and antisurjective functions are stable under post
and precomposition respectively, so simplicial maps that contain
`shift⁺`{.Agda} or `crush⁻`{.Agda} are also split antiinjective/antisurjective.

```agda
has-shift→split-antisurj
  : (f : Δ-Hom m n)
  → has-shift f
  → split-antisurjective ⟦ f ⟧
has-shift→split-antisurj f shift =
  split-antisurj-∘l {f = ⟦ f .hom⁺ ⟧} {g = ⟦ f .hom⁻ ⟧} $
  has-shift⁺→split-antisurj (f .hom⁺) shift

has-crush→split-antiinj
  : (f : Δ-Hom m n)
  → has-crush f
  → split-antiinjective ⟦ f ⟧
has-crush→split-antiinj f crush =
  split-antiinj-∘r {f = ⟦ f .hom⁺ ⟧} {g = ⟦ f .hom⁻ ⟧} $
  has-crush⁻→split-antiinj (f .hom⁻) crush
```

Conversely, if a simplicial map is split antiinjective or antisurjective,
then it contains a `shift⁺`{.Agda} or a `crush⁻`{.Agda}, respectively.
We shall focus on the antisurjective case, as the antiinjective one
follows a similar argument. Recall that if $f \circ g$ is antisurjective
and $g$ is surjective, then $f$ must be antisurjective. This means that
the semisimplicial portion of the factorization must be antisurjective,
and thus must contain a shift.

```agda
split-antisurj→has-shift
  : (f : Δ-Hom m n)
  → split-antisurjective ⟦ f ⟧
  → has-shift f
split-antisurj→has-shift f antisurj =
  split-antisurj→has-shift⁺ (f .hom⁺) $
  split-antisurj-cancelr (Δ-hom⁻-to-surj (f .hom⁻)) antisurj
```

<details>
<summary>As noted above, antiinjectivity follows an identical argument.
</summary>
```agda
split-antiinj→has-crush
  : (f : Δ-Hom m n)
  → split-antiinjective ⟦ f ⟧
  → has-crush f
split-antiinj→has-crush f antiinj =
  split-antiinj→has-crush⁻ (f .hom⁻) $
  split-antiinj-cancell (Δ-hom⁺-to-inj (f .hom⁺)) antiinj
```
</details>

We also remark that $f$ does not contain a `shift⁺`{.Agda} or a
`crush⁻`{.Agda}, then $f$ is an equivalence.

```agda
no-shift⁺→is-equiv
  : ∀ (f⁺ : Δ-Hom⁺ m n)
  → ¬ (has-shift⁺ f⁺)
  → is-equiv ⟦ f⁺ ⟧
no-shift⁺→is-equiv done⁺ no-shift .is-eqv i = fabsurd i
no-shift⁺→is-equiv (shift⁺ f⁺) no-shift = absurd (no-shift tt)
no-shift⁺→is-equiv (keep⁺ f⁺) no-shift = fkeep-equiv (no-shift⁺→is-equiv f⁺ no-shift)

no-crush⁻→is-equiv
  : ∀ (f⁻ : Δ-Hom⁻ m n)
  → ¬ (has-crush⁻ f⁻)
  → is-equiv ⟦ f⁻ ⟧
no-crush⁻→is-equiv done⁻ no-crush .is-eqv i = fabsurd i
no-crush⁻→is-equiv (crush⁻ f⁻) no-crush = absurd (no-crush tt)
no-crush⁻→is-equiv (keep⁻ f⁻) no-crush = fkeep-equiv (no-crush⁻→is-equiv f⁻ no-crush)

no-shift+no-crush→is-equiv
  : ∀ (f : Δ-Hom m n)
  → ¬ (has-shift f) → ¬ (has-crush f)
  → is-equiv ⟦ f ⟧
no-shift+no-crush→is-equiv f no-shift no-crush =
  ∙-is-equiv
    (no-crush⁻→is-equiv (f .hom⁻) no-crush)
    (no-shift⁺→is-equiv (f .hom⁺) no-shift)
```

Additionally, antisurjective and antiinjective functions are never
equivalences, so $f$ is an equivalence *if and only if* it does not
contain `shift⁺`{.Agda} or `crush⁻`{.Agda}.

```agda
is-equiv→no-shift⁺
  : ∀ (f⁺ : Δ-Hom⁺ m n)
  → is-equiv ⟦ f⁺ ⟧
  → ¬ (has-shift⁺ f⁺)

is-equiv→no-crush⁻
  : ∀ (f⁻ : Δ-Hom⁻ m n)
  → is-equiv ⟦ f⁻ ⟧
  → ¬ (has-crush⁻ f⁻)

is-equiv→no-shift
  : ∀ (f : Δ-Hom m n)
  → is-equiv ⟦ f ⟧
  → ¬ (has-shift f)

is-equiv→no-crush
  : ∀ (f : Δ-Hom m n)
  → is-equiv ⟦ f ⟧
  → ¬ (has-crush f)
```

<details>
<summary>The proofs all follow from general results about antiinjective
and antisurjective functions, so they are not particularly enlightening.
</summary>
```agda
is-equiv→no-shift⁺ f⁺ f-eqv shift =
 split-antisurj→not-equiv (has-shift⁺→split-antisurj f⁺ shift) f-eqv

is-equiv→no-crush⁻ f⁻ f-eqv crush =
 split-antiinj→not-equiv (has-crush⁻→split-antiinj f⁻ crush) f-eqv

is-equiv→no-shift f f-eqv shift =
 split-antisurj→not-equiv (has-shift→split-antisurj f shift) f-eqv

is-equiv→no-crush f f-eqv crush =
 split-antiinj→not-equiv (has-crush→split-antiinj f crush) f-eqv
```
</details>

<!--
```agda
is-equiv→no-shift+no-crush
  : ∀ (f : Δ-Hom m n)
  → is-equiv ⟦ f ⟧
  → (¬ (has-shift f)) × (¬ (has-crush f))
is-equiv→no-shift+no-crush f f-eqv =
  (is-equiv→no-shift f f-eqv , is-equiv→no-crush f f-eqv)
```
-->

This concludes step 3, so all we need to do is put the pieces together!
We will only show the proof for the augmented simplex category, as the
non-augmented case is identical.

Invertible simplicial maps are equivalences; so isomorphisms do not contain
any `shift⁺`{.Agda} or `crush⁻`{.Agda} constructors.

```agda
Δₐ-iso→is-equiv
  : ∀ (f : m Δₐ.≅ n)
  → is-equiv ⟦ Δₐ.to f ⟧
Δₐ-iso→is-equiv f =
  is-iso→is-equiv $
    iso ⟦ from ⟧
      (λ i → sym (Δ-hom-∘ to from i) ∙ unext invl i ∙ Δ-hom-id i)
      (λ i → sym (Δ-hom-∘ from to i) ∙ unext invr i ∙ Δ-hom-id i)
  where open Δₐ._≅_ f
```

<!--
```agda
Δ-iso→is-equiv
  : ∀ (f : m Δ.≅ n)
  → is-equiv ⟦ Δ.to f ⟧
Δ-iso→is-equiv f =
  is-iso→is-equiv $
    iso ⟦ from ⟧
      (λ i → sym (Δ-hom-∘ to from i) ∙ unext invl i ∙ Δ-hom-id i)
      (λ i → sym (Δ-hom-∘ from to i) ∙ unext invr i ∙ Δ-hom-id i)
  where open Δ._≅_ f
```
-->

We can put steps 1, and 3 together to show that equivalences, and
thus isomorphisms, have images that are the same dimension as
both endpoints.

```agda
is-equiv→im-stablel
  : ∀ (f : Δ-Hom m n)
  → is-equiv ⟦ f ⟧
  → m ≡ f .im
is-equiv→im-stablel f eqv =
  no-crush⁻→dim-stable (f .hom⁻) $
  is-equiv→no-crush f eqv

is-equiv→im-stabler
  : ∀ (f : Δ-Hom m n)
  → is-equiv ⟦ f ⟧
  → f .im ≡ n
is-equiv→im-stabler f eqv =
  no-shift⁺→dim-stable (f .hom⁺) $
  is-equiv→no-shift f eqv
```

If we combine with with step 2, then we can show that every automorphism
is trivial.

```agda
Δₐ-auto-id
  : ∀ (f : n Δₐ.≅ n)
  → f ≡ Δₐ.id-iso
Δₐ-auto-id f =
  Δₐ.≅-path $
  Δ-Hom-path
    (is-equiv→im-stabler f.to (Δₐ-iso→is-equiv f))
    (Δ-endo⁺-idp (f.to .hom⁺))
    (Δ-endo⁻-idp (f.to .hom⁻))
  where module f = Δₐ._≅_ f
```

<!--
```agda
Δ-auto-id
  : ∀ (f : n Δ.≅ n)
  → f ≡ Δ.id-iso
Δ-auto-id f =
  Δ.≅-path $
  Δ-Hom-path
    (is-equiv→im-stabler f.to (Δ-iso→is-equiv f))
    (Δ-endo⁺-idp (f.to .hom⁺))
    (Δ-endo⁻-idp (f.to .hom⁻))
  where module f = Δ._≅_ f
```
-->

Finally, equivalences (and thus isomorphisms) must preserve dimension:
this gives us a way of turning isomorphisms into paths.

```agda
is-equiv→dim-stable
  : ∀ (f : Δ-Hom m n)
  → is-equiv ⟦ f ⟧
  → m ≡ n
is-equiv→dim-stable f eqv =
  no-shift+no-crush→dim-stable f
    (is-equiv→no-shift f eqv)
    (is-equiv→no-crush f eqv)
```

And just like that, the proof is done!

```agda
Δₐ-is-category : is-category Δₐ
Δₐ-is-category =
  set-identity-system-K
    (λ _ → Δₐ-auto-id)
    (λ f → is-equiv→dim-stable (Δₐ.to f) (Δₐ-iso→is-equiv f))
```

<!--
```agda
Δ-is-category : is-category Δ
Δ-is-category =
  set-identity-system-K
    (λ _ → Δ-auto-id)
    (λ f → Nat.suc-inj (is-equiv→dim-stable (Δ.to f) (Δ-iso→is-equiv f)))
```
-->


Moreover, the all of the variations of the simplex are all strict, and thus
gaunt.

```agda
Δₐ-is-gaunt : is-gaunt Δₐ
Δₐ⁺-is-gaunt : is-gaunt Δₐ⁺
Δₐ⁻-is-gaunt : is-gaunt Δₐ⁻

Δ-is-gaunt : is-gaunt Δ
Δ⁺-is-gaunt : is-gaunt Δ⁺
Δ⁻-is-gaunt : is-gaunt Δ⁻
```

<details>
<summary>The proofs are just packaging up results we have already shown,
so they aren't very interesting.
</summary>
```agda
Δₐ-is-gaunt .is-gaunt.has-category = Δₐ-is-category
Δₐ-is-gaunt .is-gaunt.has-strict = hlevel 2

Δₐ⁺-is-gaunt .is-gaunt.has-category = Δₐ⁺-is-category
Δₐ⁺-is-gaunt .is-gaunt.has-strict = hlevel 2

Δₐ⁻-is-gaunt .is-gaunt.has-category = Δₐ⁻-is-category
Δₐ⁻-is-gaunt .is-gaunt.has-strict = hlevel 2

Δ-is-gaunt .is-gaunt.has-category = Δ-is-category
Δ-is-gaunt .is-gaunt.has-strict = hlevel 2

Δ⁺-is-gaunt .is-gaunt.has-category = Δ⁺-is-category
Δ⁺-is-gaunt .is-gaunt.has-strict = hlevel 2

Δ⁻-is-gaunt .is-gaunt.has-category = Δ⁻-is-category
Δ⁻-is-gaunt .is-gaunt.has-strict = hlevel 2
```
</details>


## Categorical structure

Now that we actually have categories, we can start to construct some
interesting maps. We begin by constructing more familiar versions of
face and degeneracy map that are parameterized by some $i$.

```agda
δ⁺ : Fin (suc n) → Δ-Hom⁺ n (suc n)
δ⁺ {n = _} fzero = shift⁺ id⁺
δ⁺ {n = suc _} (fsuc i) = keep⁺ (δ⁺ i)


σ⁻ : Fin n → Δ-Hom⁻ (suc n) n
σ⁻ fzero = crush⁻ id⁻
σ⁻ (fsuc i) = keep⁻ (σ⁻ i)
```

We can extend `δ⁺`{.Agda} and `σ⁻`{.Agda} to simplicial maps by
taking the other component to be the corresponding identity map.

```agda
δ : Fin (suc n) → Δ-Hom n (suc n)
δ i .im = _
δ i .hom⁺ = δ⁺ i
δ i .hom⁻ = id⁻

σ : Fin n → Δ-Hom (suc n) n
σ i .im = _
σ i .hom⁺ = id⁺
σ i .hom⁻ = σ⁻ i
```

The semantic interpretations of `δ i`{.Agda} and `σ i`{.Agda} are the
corresponding face and degenearcy maps between finite sets.

```agda
Δ-hom⁺-δ
  : ∀ (i : Fin (suc n))
  → ∀ (x : Fin n) → ⟦ δ⁺ i ⟧ x ≡ skip i x
Δ-hom-δ
  : ∀ (i : Fin (suc n))
  → ∀ (x : Fin n) → ⟦ δ i ⟧ x ≡ skip i x

Δ-hom⁻-σ
  : ∀ (i : Fin n)
  → ∀ (x : Fin (suc n)) → ⟦ σ⁻ i ⟧ x ≡ squish i x
Δ-hom-σ
  : ∀ (i : Fin n)
  → ∀ (x : Fin (suc n)) → ⟦ σ i ⟧ x ≡ squish i x
```

<details>
<summary>The proofs are straighforward, so we omit them.
</summary>

```agda
Δ-hom⁺-δ fzero x = ap fsuc (Δ-hom⁺-id x)
Δ-hom⁺-δ (fsuc i) fzero = refl
Δ-hom⁺-δ (fsuc i) (fsuc x) = ap fsuc (Δ-hom⁺-δ i x)

Δ-hom-δ i x = ap ⟦ δ⁺ i ⟧ (Δ-hom⁻-id x) ∙ Δ-hom⁺-δ i x

Δ-hom⁻-σ fzero fzero = refl
Δ-hom⁻-σ fzero (fsuc x) =
  ap₂ fkeep (funext Δ-hom⁻-id) refl
  ∙ fkeep-id x
Δ-hom⁻-σ (fsuc i) fzero = refl
Δ-hom⁻-σ (fsuc i) (fsuc x) = ap fsuc (Δ-hom⁻-σ i x)

Δ-hom-σ i x = Δ-hom⁺-id (⟦ σ⁻ i ⟧ x) ∙ Δ-hom⁻-σ i x
```
</details>

Next, note that $0$ is an initial object in the augmented (semi) simplex
category.

```agda
¡⁺ : Δ-Hom⁺ 0 n
¡⁺ {n = zero} = done⁺
¡⁺ {n = suc n} = shift⁺ ¡⁺

¡Δ : Δ-Hom 0 n
¡Δ .im = 0
¡Δ .hom⁺ = ¡⁺
¡Δ .hom⁻ = done⁻
```

There are many ways to prove that these maps are unique, but the most
straightforward approach is to use our semantic interpretations: these
yield functions `Fin 0 → Fin n`, which are extremely easy to prove unique.

```agda
¡⁺-unique : (f : Δ-Hom⁺ 0 n) → f ≡ ¡⁺
¡⁺-unique f = ext λ i → fabsurd i

¡Δ-unique : (f : Δ-Hom 0 n) → f ≡ ¡Δ
¡Δ-unique f = ext λ i → fabsurd i
```

<!--
```agda
Δₐ⁺-initial : Initial Δₐ⁺
Δₐ⁺-initial .Initial.bot = 0
Δₐ⁺-initial .Initial.has⊥ _ .centre = ¡⁺
Δₐ⁺-initial .Initial.has⊥ _ .paths f = sym (¡⁺-unique f)

Δₐ-initial : Initial Δₐ
Δₐ-initial .Initial.bot = 0
Δₐ-initial .Initial.has⊥ _ .centre = ¡Δ
Δₐ-initial .Initial.has⊥ _ .paths f = sym (¡Δ-unique f)
```
-->

Likewise, $1$ is a terminal object in the (demi) simplex category.

```agda
!⁻ : Δ-Hom⁻ (suc n) 1
!⁻ {n = zero} = id⁻
!⁻ {n = suc n} = crush⁻ !⁻

!Δ : Δ-Hom (suc n) 1
!Δ .im = 1
!Δ .hom⁺ = id⁺
!Δ .hom⁻ = !⁻
```

It is also a terminal object in the augmented simplex category, as
we always have a map $0 \to 1$. However, note that it is *not* terminal
in the augmented demi-simplex category, as there is no surjective map
$0 \to 1$!

```agda
!Δₐ : Δ-Hom n 1
!Δₐ {n = zero} = ¡Δ
!Δₐ {n = suc n} = !Δ
```

We can use the same semantic strategy to prove that these maps are
unique.

```agda
!⁻-unique : (f : Δ-Hom⁻ (suc n) 1) → f ≡ !⁻
!⁻-unique f = ext λ i → Finite-one-is-prop (⟦ f ⟧ i) (⟦ !⁻ ⟧ i)

!Δ-unique : (f : Δ-Hom (suc n) 1) → f ≡ !Δ
!Δ-unique f = ext λ i → Finite-one-is-prop (⟦ f ⟧ i) (⟦ !Δ ⟧ i)

!Δₐ-unique : (f : Δ-Hom n 1) → f ≡ !Δₐ
!Δₐ-unique {n = zero} = ¡Δ-unique
!Δₐ-unique {n = suc n} = !Δ-unique
```

<!--
```agda
Δ⁻-terminal : Terminal Δ⁻
Δ⁻-terminal .Terminal.top = 0
Δ⁻-terminal .Terminal.has⊤ _ .centre = !⁻
Δ⁻-terminal .Terminal.has⊤ _ .paths f = sym (!⁻-unique f)

Δ-terminal : Terminal Δ
Δ-terminal .Terminal.top = 0
Δ-terminal .Terminal.has⊤ _ .centre = !Δ
Δ-terminal .Terminal.has⊤ _ .paths f = sym (!Δ-unique f)

Δₐ-terminal : Terminal Δₐ
Δₐ-terminal .Terminal.top = 1
Δₐ-terminal .Terminal.has⊤ _ .centre = !Δₐ
Δₐ-terminal .Terminal.has⊤ _ .paths f = sym (!Δₐ-unique f)
```
-->

## Decidable equality

<!--
```agda
-- Casts that compute on indices + constructors.
-- Makes decidable equality a bit more well behaved.
cast⁺ : ∀ {n' m' m n} → m ≡ m' → n ≡ n' → Δ-Hom⁺ m n → Δ-Hom⁺ m' n'
cast⁻ : ∀ {m' n' m n} → m ≡ m' → n ≡ n' → Δ-Hom⁻ m n → Δ-Hom⁻ m' n'
castΔ : m ≡ m' → n ≡ n' → Δ-Hom m n → Δ-Hom m' n'

cast⁺ {zero}   {zero}   p q f          = done⁺
cast⁺ {zero}   {suc m'} p q f          = absurd (Δ-hom⁺-zero-strict (subst₂ Δ-Hom⁺ p q f))
cast⁺ {suc n'} {m'}     p q done⁺      = absurd (Nat.zero≠suc q)
cast⁺ {suc n'} {m'}     p q (shift⁺ f) = shift⁺ (cast⁺ p (Nat.suc-inj q) f)
cast⁺ {suc n'} {zero}   p q (keep⁺ f)  = absurd (Nat.suc≠zero p)
cast⁺ {suc n'} {suc m'} p q (keep⁺ f)  = keep⁺ (cast⁺ (Nat.suc-inj p) (Nat.suc-inj q) f)

cast⁻ {zero}         {zero}   p q f          = done⁻
cast⁻ {zero}         {suc n'} p q f          = absurd (Δ-hom⁻-no-initial (subst₂ Δ-Hom⁻ p q f))
cast⁻ {suc m'}       {n'}     p q done⁻      = absurd (Nat.zero≠suc p)
cast⁻ {suc zero}     {n'}     p q (crush⁻ f) = absurd (Nat.suc≠zero (Nat.suc-inj p))
cast⁻ {suc (suc m')} {n'}     p q (crush⁻ f) = crush⁻ (cast⁻ (Nat.suc-inj p) q f)
cast⁻ {suc m'}       {zero}   p q (keep⁻ f)  = absurd (Nat.suc≠zero q)
cast⁻ {suc m'}       {suc n'} p q (keep⁻ f)  = keep⁻ (cast⁻ (Nat.suc-inj p) (Nat.suc-inj q) f)

castΔ p q f .im = f .im
castΔ p q f .hom⁺ = cast⁺ refl q (f .hom⁺)
castΔ p q f .hom⁻ = cast⁻ p refl (f .hom⁻)

cast⁺-refl : ∀ (f : Δ-Hom⁺ m n) → cast⁺ refl refl f ≡ f
cast⁺-refl done⁺ = refl
cast⁺-refl (shift⁺ f) = ap shift⁺ (cast⁺-refl f)
cast⁺-refl (keep⁺ f) = ap keep⁺ (cast⁺-refl f)

cast⁻-refl : ∀ (f : Δ-Hom⁻ m n) → cast⁻ refl refl f ≡ f
cast⁻-refl done⁻ = refl
cast⁻-refl (crush⁻ f) = ap crush⁻ (cast⁻-refl f)
cast⁻-refl (keep⁻ f) = ap keep⁻ (cast⁻-refl f)

castΔ-refl : ∀ (f : Δ-Hom m n) → castΔ refl refl f ≡ f
castΔ-refl f = Δ-Hom-path refl (cast⁺-refl (f .hom⁺)) (cast⁻-refl (f .hom⁻))

cast⁺≃pathp
  : {f : Δ-Hom⁺ m n} {g : Δ-Hom⁺ m' n'}
  → (p : m ≡ m') (q : n ≡ n')
  → (cast⁺ p q f ≡ g) ≃ PathP (λ i → Δ-Hom⁺ (p i) (q i)) f g
cast⁺≃pathp {m = m} {n = n} {f = f} {g = g} p q =
  J₂ mot (λ f g → ∙-pre-equiv (sym (cast⁺-refl f))) p q f g
  where
    mot : ∀ (m' n' : Nat) → m ≡ m' → n ≡ n' → Type _
    mot m' n' p q =
      ∀ (f : Δ-Hom⁺ m n) (g : Δ-Hom⁺ m' n')
      → (cast⁺ p q f ≡ g) ≃ PathP (λ i → Δ-Hom⁺ (p i) (q i)) f g

cast⁻≃pathp
  : {f : Δ-Hom⁻ m n} {g : Δ-Hom⁻ m' n'}
  → (p : m ≡ m') (q : n ≡ n')
  → (cast⁻ p q f ≡ g) ≃ PathP (λ i → Δ-Hom⁻ (p i) (q i)) f g
cast⁻≃pathp {m = m} {n = n} {f = f} {g = g} p q =
  J₂ mot (λ f g → ∙-pre-equiv (sym (cast⁻-refl f))) p q f g
  where
    mot : ∀ (m' n' : Nat) → m ≡ m' → n ≡ n' → Type _
    mot m' n' p q =
      ∀ (f : Δ-Hom⁻ m n) (g : Δ-Hom⁻ m' n')
      → (cast⁻ p q f ≡ g) ≃ PathP (λ i → Δ-Hom⁻ (p i) (q i)) f g

shift⁺-inj
  : ∀ {f g : Δ-Hom⁺ m n}
  → shift⁺ f ≡ shift⁺ g
  → f ≡ g
shift⁺-inj {m} {n} {f} {g} = ap unshift where
  unshift : Δ-Hom⁺ m (suc n) → Δ-Hom⁺ m n
  unshift (shift⁺ h) = h
  unshift (keep⁺ h) = f

keep⁺-inj
  : ∀ {f g : Δ-Hom⁺ m n}
  → keep⁺ f ≡ keep⁺ g
  → f ≡ g
keep⁺-inj {m} {n} {f} {g} = ap unkeep where
  unkeep : Δ-Hom⁺ (suc m) (suc n) → Δ-Hom⁺ m n
  unkeep (keep⁺ h) = h
  unkeep (shift⁺ h) = f

crush⁻-inj
  : ∀ {f g : Δ-Hom⁻ (suc m) n}
  → crush⁻ f ≡ crush⁻ g
  → f ≡ g
crush⁻-inj {m} {n} {f} {g} = ap uncrush where
  uncrush : Δ-Hom⁻ (suc (suc m)) n → Δ-Hom⁻ (suc m) n
  uncrush (crush⁻ h) = h
  uncrush (keep⁻ h) = f

keep⁻-inj
  : ∀ {f g : Δ-Hom⁻ m n}
  → keep⁻ f ≡ keep⁻ g
  → f ≡ g
keep⁻-inj {m} {n} {f} {g} = ap unkeep where
  unkeep : Δ-Hom⁻ (suc m) (suc n) → Δ-Hom⁻ m n
  unkeep (keep⁻ h) = h
  unkeep (crush⁻ h) = f

is-shift⁺ : Δ-Hom⁺ m n → Type
is-shift⁺ done⁺ = ⊥
is-shift⁺ (shift⁺ _) = ⊤
is-shift⁺ (keep⁺ _) = ⊥

is-keep⁺ : Δ-Hom⁺ m n → Type
is-keep⁺ done⁺ = ⊥
is-keep⁺ (shift⁺ _) = ⊥
is-keep⁺ (keep⁺ _) = ⊤

is-crush⁻ : Δ-Hom⁻ m n → Type
is-crush⁻ done⁻ = ⊥
is-crush⁻ (crush⁻ f) = ⊤
is-crush⁻ (keep⁻ f) = ⊥

is-keep⁻ : Δ-Hom⁻ m n → Type
is-keep⁻ done⁻ = ⊥
is-keep⁻ (crush⁻ f) = ⊥
is-keep⁻ (keep⁻ f) = ⊤

shift⁺≠keep⁺
  : ∀ {f : Δ-Hom⁺ (suc m) n} {g : Δ-Hom⁺ m n}
  → ¬ (shift⁺ f ≡ keep⁺ g)
shift⁺≠keep⁺ p = subst is-shift⁺ p tt

keep⁺≠shift⁺
  : ∀ {f : Δ-Hom⁺ m n} {g : Δ-Hom⁺ (suc m) n}
  → ¬ (keep⁺ f ≡ shift⁺ g)
keep⁺≠shift⁺ p = subst is-keep⁺ p tt

crush⁻≠keep⁻
  : ∀ {f : Δ-Hom⁻ (suc m) (suc n)} {g : Δ-Hom⁻ (suc m) n}
  → ¬ (crush⁻ f ≡ keep⁻ g)
crush⁻≠keep⁻ p = subst is-crush⁻ p tt

keep⁻≠crush⁻
  : ∀ {f : Δ-Hom⁻ (suc m) n} {g : Δ-Hom⁻ (suc m) (suc n)}
  → ¬ (keep⁻ f ≡ crush⁻ g)
keep⁻≠crush⁻ p = subst is-keep⁻ p tt
```
-->

All three classes of maps have decidable equality.

```agda
instance
  Discrete-Δ-Hom⁺ : Discrete (Δ-Hom⁺ m n)
  Discrete-Δ-Hom⁻ : Discrete (Δ-Hom⁻ m n)
  Discrete-Δ-Hom  : Discrete (Δ-Hom m n)
```

<details>
<summary>Proving this is pretty tedious though, especially for
general morphisms.
</summary>

```agda
  Discrete-Δ-Hom⁺ {x = done⁺} {y = done⁺} =
    yes refl
  Discrete-Δ-Hom⁺ {x = shift⁺ x} {y = shift⁺ y} =
    Dec-map (ap shift⁺) shift⁺-inj Discrete-Δ-Hom⁺
  Discrete-Δ-Hom⁺ {x = shift⁺ x} {y = keep⁺ y} =
    no shift⁺≠keep⁺
  Discrete-Δ-Hom⁺ {x = keep⁺ x} {y = shift⁺ y} =
    no keep⁺≠shift⁺
  Discrete-Δ-Hom⁺ {x = keep⁺ x} {y = keep⁺ y} =
    Dec-map (ap keep⁺) keep⁺-inj Discrete-Δ-Hom⁺

  Discrete-Δ-Hom⁻ {x = done⁻} {y = done⁻} =
    yes refl
  Discrete-Δ-Hom⁻ {x = crush⁻ x} {y = crush⁻ y} =
    Dec-map (ap crush⁻) crush⁻-inj Discrete-Δ-Hom⁻
  Discrete-Δ-Hom⁻ {x = crush⁻ x} {y = keep⁻ y} =
    no crush⁻≠keep⁻
  Discrete-Δ-Hom⁻ {x = keep⁻ x} {y = crush⁻ y} =
    no keep⁻≠crush⁻
  Discrete-Δ-Hom⁻ {x = keep⁻ x} {y = keep⁻ y} =
    Dec-map (ap keep⁻) keep⁻-inj Discrete-Δ-Hom⁻

  Discrete-Δ-Hom {x = x} {y = y} with x .im ≡? y .im
  ... | yes p with cast⁺ p refl (x .hom⁺) ≡? (y .hom⁺) | cast⁻ refl p (x .hom⁻) ≡? y .hom⁻
  ... | yes q | yes r =
    yes (Δ-Hom-path p (Equiv.to (cast⁺≃pathp p refl) q) (Equiv.to (cast⁻≃pathp refl p) r))
  ... | yes q | no ¬r =
    no λ s → ¬r $
      subst (λ e → cast⁻ refl e (x .hom⁻) ≡ y .hom⁻)
        (Nat.Nat-is-set _ _ _ _)
        (Equiv.from (cast⁻≃pathp refl (ap im s)) $ ap hom⁻ s)
  ... | no ¬q | r =
    no λ s → ¬q $
      subst (λ e → cast⁺ e refl (x .hom⁺) ≡ y .hom⁺)
        (Nat.Nat-is-set _ _ _ _)
        (Equiv.from (cast⁺≃pathp (ap im s) refl) $ ap hom⁺ s)
  Discrete-Δ-Hom {x = x} {y = y} | no ¬p = no (¬p ⊙ ap im)
```
</details>

Equality is not the only thing we can decide: recall that
a map $f$ is an equivalence if and only if it does not contain
any `shift⁺`{.Agda} or `crush⁻`{.Agda} constructors. The latter is
a purely syntactic condition, which makes it easily decidable!

```agda
has-shift?⁺
  : ∀ (f⁺ : Δ-Hom⁺ m n)
  → Dec (has-shift⁺ f⁺)
has-shift?⁺ done⁺ = no λ ff → ff
has-shift?⁺ (shift⁺ f⁺) = yes tt
has-shift?⁺ (keep⁺ f⁺) = has-shift?⁺ f⁺

has-crush?⁻
  : ∀ (f⁻ : Δ-Hom⁻ m n)
  → Dec (has-crush⁻ f⁻)
has-crush?⁻ done⁻ = no λ ff → ff
has-crush?⁻ (crush⁻ f⁻) = yes tt
has-crush?⁻ (keep⁻ f⁻) = has-crush?⁻ f⁻
```

This gives us an efficient way to check if a (semi/demi) simplicial
map is an equivalence.

```agda
Δ-hom⁺-equiv?
  : ∀ (f⁺ : Δ-Hom⁺ m n)
  → Dec (is-equiv ⟦ f⁺ ⟧)

Δ-hom⁻-equiv?
  : ∀ (f⁻ : Δ-Hom⁻ m n)
  → Dec (is-equiv ⟦ f⁻ ⟧)

Δ-hom-equiv?
  : ∀ (f : Δ-Hom m n)
  → Dec (is-equiv ⟦ f ⟧)
```

<details>
<summary>The actual decidability proofs are just stitching together
previous results, and are not particularly interesting.
</summary>
```agda
Δ-hom⁺-equiv? f⁺ =
  Dec-map
    (no-shift⁺→is-equiv f⁺)
    (is-equiv→no-shift⁺ f⁺)
    (not? (has-shift?⁺ f⁺))

Δ-hom⁻-equiv? f⁻ =
  Dec-map
    (no-crush⁻→is-equiv f⁻)
    (is-equiv→no-crush⁻ f⁻)
    (not? (has-crush?⁻ f⁻))

Δ-hom-equiv? f =
  Dec-map
    (rec! (no-shift+no-crush→is-equiv f))
    (is-equiv→no-shift+no-crush f)
    (Dec-× ⦃ not? (has-shift?⁺ (f .hom⁺)) ⦄ ⦃ not? (has-crush?⁻ (f .hom⁻)) ⦄)
```
</details>
