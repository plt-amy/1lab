<!--
```agda
open import 1Lab.Path
open import 1Lab.Type
```
-->

```agda
module 1Lab.HLevel where
```

<!--
```agda
private variable
  ℓ : Level
  A : Type ℓ
```
-->

# h-Levels {defines="h-level homotopy-n-type n-type truncated truncatedness"}

When working in type theory, the mathematical activities of *proving*
and *constructing* become intermingled, in a way that sometimes poses
serious complications: The *method* by which a given statement $P$ was
proven may be relevant in the future, since it is, at heart, a
*construction* --- of a term of type $P$. To tame this annoyance, an
important pursuit in type theory is identifying the statements $P$ for
which the construction *can not* matter. A simple example is equality
between natural numbers: there is no further construction that could
tell *proofs of $4 = 4$* apart.

In a homotopy type theory, where a general type might have non-trivial
[[identifications|path]] *all the way up*, it becomes very useful to
state that, at some point, a given type stops having distinguishable
*constructions*, and instead has a unique *proof* --- for which we could
substitute any *other* potential proof. We have already mentioned the
example of the natural numbers: there are a lot of different natural
numbers, but as soon as we have a pair $x, y : \bN$, if we have any $p :
x \equiv y$, then it's as good as *any other* $q : x \equiv y$.

:::{.definition #proposition alias="property"}
At this point, we should introduce the proper terminology, rather than
speaking of "proving" types and "constructing" types. We say that a type
$T$ is a **proposition**, written `is-prop`{.Agda} below, if any two of
its inhabitants are identified. Since every construction is invariant
under identifications (by definition), this means that any two putative
constructions $x, y : T$ are indistinguishable --- they're really the
same **proof**.

```agda
is-prop : ∀ {ℓ} → Type ℓ → Type ℓ
is-prop T = (x y : T) → x ≡ y
```
:::

The information that a type is a proposition can also be seen as a form
of *induction principle*: If $A$ is a proposition, and $P(x)$ is a type
family over $A$, then constructing a section $\forall_{b : A} P(b)$ can
be done by showing $P(a)$ for any $a$ at all. If we had this induction
principle, then we could recover the notion of propositionality above by
taking $P(x)$ to be the family $a \equiv x$.

```agda
subst-prop : ∀ {ℓ ℓ'} {A : Type ℓ} {P : A → Type ℓ'} → is-prop A → ∀ a → P a → ∀ b → P b
subst-prop {P = P} prop a pa b = subst P (prop a b) pa
```

Keep in mind that, *even if* a type $T$ is a proposition, it might still
be possible to project interesting data *from* a proof $t : T$ --- but,
were we to project this data from $s : T$ instead, we would get
something identical. Propositions abound: the statement that $T$ is a
proposition turns out to be one, for example, as is the statement that a
function $f : A \to B$ is an [[equivalence]]. Even though any two proofs
that $f$ is an equivalence are interchangeable, if we're given such a
proof, we can project out the inverse $B \to A$ --- and there might be a
lot of functions $B \to A$ laying around!

:::{.definition #set}
Knowing about propositions, we can now rephrase our earlier statement
about the natural numbers: each identity type $x \equiv_\bN y$ is a
proposition. Types for which this statement holds are called **sets**. A
proof that a type $T$ is a set is a licence to stop caring about *how*
we show that $x, y : T$ are identified --- we even say that they're just
**equal**.

```agda
is-set : ∀ {ℓ} → Type ℓ → Type ℓ
is-set A = (x y : A) → is-prop (x ≡ y)
```
:::

While it may seem unusual to ever explicitly *ask* whether a pair of
proofs $p, q : x \equiv_T y$ are identical, we might certainly end up in
such a situation if we're comparing larger structures! For example, if
$G$ and $H$ are [[groups]], then it makes perfect sense to ask whether
homomorphisms $f, g : G \to H$ are identical. But the data of a group
homomorphism consists of a function $f : G \to H$ between the types
underlying each group, *and* a value in the type $\forall_{x, y : G}
f(xy) = f(x)f(y)$. Knowing that a group has an underlying set means that
this type is a proposition --- this value is really a *proof* that $f$
preserves multiplication, and we do not have to care about it.

Since a set is defined to be a type whose identity types are
propositions, it's natural to ask: is there a name for a type $T$ whose
identity types are *sets*? The answer is yes! These are called
**groupoids**. We can extend this process recursively to ask about any
natural number of iterated identity types. This is called the type's
**h-level**. If we're thinking of a type $T$ as a space, and of the
identifications $x \equiv_T y$ as paths, then the statement "$T$ has
h-level $n$" tells you that the [[homotopy groups]] $\pi_k(T)$ for $k >
n$ are all zero.

:::{.definition #contractible}
Thinking about how much information $T$ carries, we could say that a
proposition carries the information of whether it is true or false; a
set carries the information of which inhabitant we're looking at; a
groupoid carries that, and, additionally, the set of symmetries of that
inhabitant, and so on. From this perspective, there are types which are
even *less* interesting --- those that carry no information at all: the
propositions *we know* are inhabited. In traditional foundations, we
might call this a *singleton*; in homotopy type theory, we call them
**contractible**.

Making the notion concrete, to say that $T$ is contractible means giving
a point $t : T$, called the **centre of contraction**, and an operation
that, given a point $s : T$, yields a path $t \equiv s$. We will show
below that every proposition is a set, which means that, since the
identity types of a proposition are all pointed, they are all
*contractible*. Thus, the contractible types naturally fit into the
hierarchy of h-levels.
:::

```agda
record is-contr {ℓ} (A : Type ℓ) : Type ℓ where
  constructor contr
  field
    centre : A
    paths  : (x : A) → centre ≡ x

open is-contr public
```

We can now write down the definition of `is-hlevel`{.Agda}, as a
function of the type *and* the specific level. Note that, even though
that being a proposition is equivalent to having contractible identity
types, we'll define `is-hlevel`{.Agda} so that it agrees with our
previous definition.

```agda
is-hlevel : ∀ {ℓ} → Type ℓ → Nat → Type _
is-hlevel A 0       = is-contr A
is-hlevel A 1       = is-prop A
is-hlevel A (suc n) = (x y : A) → is-hlevel (Path A x y) n
```

:::{.definition #groupoid}
The recursive definition above agrees with `is-set`{.Agda} at level 2.
We can also take this opportunity to define the groupoids as the types
for which `is-hlevel`{.Agda} holds at level 3.
:::

```agda
_ : is-set A ≡ is-hlevel A 2
_ = refl

is-groupoid : ∀ {ℓ} → Type ℓ → Type ℓ
is-groupoid A = is-hlevel A 3
```

::: warning
The traditional numbering for h-levels says that the *sets* are at level
zero, and that the propositions and contractible types are at negative
levels (-1 and -2, respectively). While there is no *mathematical*
benefit to using this numbering over starting at zero, there are
*social* benefits. For example, the groupoids (at level 3) turn out to
be the types underlying ([[univalent|univalent category]])
1-[[categories]].

We will, therefore, sometimes use the historical numbering in prose. To
clarify the distinction, we will say that a type $T$ is **of h-level
$n$** if `is-hlevel T n`{.Agda ident=is-hlevel} holds and, when using
the traditional numbering, we will say that $T$ is an **$(n-2)$-type**,
or is **$(n-2)$-truncated**. For example, sets are *of h-level $2$,* but
are $0$-types, or $0$-truncated.
:::

## Examples

We can now mention some examples of types at the various h-levels, to
show that the notion is not vacuous. Starting at the contractible types,
the most obvious example is the *literal* singleton --- or rather, unit
--- type.

```agda
⊤-is-contr : is-contr ⊤
⊤-is-contr .centre  = tt
⊤-is-contr .paths _ = refl
```

We have previously mentioned that [[path induction]] says that the
*singletons*, in the sense of *the subtype of $A$ identical to a given
$a : A$*, are also contractible. Even though we have a shorter cubical
proof (used in the *definition* of path induction), we can demonstrate
the application of path induction:

```agda
_ : (a : A) → is-contr (Σ[ b ∈ A ] b ≡ a)
_ = λ t → record
  { centre = (t , refl)
  ; paths  = λ (s , p) → J' (λ s t p → (t , refl) ≡ (s , p)) (λ t → refl) p
  }
```

This provides an example of a type that is not literally *defined* to be
of a certain h-level, but there are also geometric examples. One is the
unit interval, defined as a higher inductive type, which has *two*
points and a path between them.

```agda
data [0,1] : Type where
  ii0 : [0,1]
  ii1 : [0,1]
  seg : ii0 ≡ ii1
```

Thinking geometrically, the construction of the contraction "fixes" the
endpoint at zero, and "pulls in" the other endpoint; in the process, the
path between them becomes trivial. We also have a direct cubical proof
that this results in a contractible type:

```agda
interval-contractible : is-contr [0,1]
interval-contractible .centre = ii0
interval-contractible .paths ii0     i = ii0
interval-contractible .paths ii1     i = seg i
interval-contractible .paths (seg i) j = seg (i ∧ j)
```

## Propositions are sets

We have previously mentioned that *being a proposition* is a
proposition, when applied to a specific type. We will show this by
showing that every proposition is a set: since `is-prop`{.Agda} is then
a (dependent) function valued in propositions, it's also a proposition.
Showing this in axiomatic homotopy type theory is slightly tricky, but
showing it in cubical type theory is a remarkable application of lifting
properties.

First, we'll make the geometry of the problem clear: we're given points
$x, y : A$ and paths $p, q : x \equiv y$. What we want to show, that $p
\equiv q$, is visualised as a *square*. In one dimension, say $j$, we
have $p(j)$ and $q(j)$, and these are opposite faces in another
dimension, say $i$.

~~~{.quiver}
\[\begin{tikzcd}[ampersand replacement=\&]
  x \&\& x \\
  \\
  y \&\& y
  \arrow[dashed, "{p(j)}"', from=1-1, to=3-1]
  \arrow[dashed, "{q(j)}", from=1-3, to=3-3]
  \arrow[dashed, "x", from=1-1, to=1-3]
  \arrow[dashed, "y"', from=3-1, to=3-3]
\end{tikzcd}\]
~~~

Recall that, by [[fibrancy]] of $A$, we can obtain such a square by
displaying it as the missing higher-dimensional face in some higher
cube, then appealing to `hcomp`{.Agda}. As the *base face*, opposite to
what we want in some new direction $k$, we choose the square that is
constantly $x$. We then have to give terms filling the four boundary
squares --- these will turn out to be very similar. Let's focus on the
$i = i0$ square.

The diagram below illustrates the setup: in addition to $i$ varying
horizontally and $j$ varying vertically, we now have $k$ varying "front
to back". At the $k = i0$ face, we have the constantly $x$ square; at $k
= i1$, the boundary is the dashed square we're looking for. The $i = i0$
square is on the left, in red.

~~~{.quiver}
\[\begin{tikzcd}[ampersand replacement=\&]
  \textcolor{rgb,255:red,214;green,92;blue,92}{x} \&\&\&\& x \\
  \& \textcolor{rgb,255:red,214;green,92;blue,92}{x} \&\& x \\
  \\
  \& \textcolor{rgb,255:red,214;green,92;blue,92}{y} \&\& y \\
  \textcolor{rgb,255:red,214;green,92;blue,92}{x} \&\&\&\& x
  \arrow[color={rgb,255:red,214;green,92;blue,92}, from=1-1, to=2-2]
  \arrow["{p(j)}", color={rgb,255:red,214;green,92;blue,92}, dashed, from=2-2, to=4-2]
  \arrow[color={rgb,255:red,214;green,92;blue,92}, from=5-1, to=4-2]
  \arrow["x"', color={rgb,255:red,214;green,92;blue,92}, from=1-1, to=5-1]
  \arrow["y", dashed, from=4-2, to=4-4]
  \arrow["x"', dashed, from=2-2, to=2-4]
  \arrow["{q(j)}"', dashed, from=2-4, to=4-4]
  \arrow["x"', from=5-1, to=5-5]
  \arrow["x", from=1-1, to=1-5]
  \arrow["x", from=1-5, to=5-5]
\end{tikzcd}\]
~~~

By abstracting over the $k$ dimension, we can think of the boundary of
the red square as giving a path type --- we're looking to construct a
path between $x : A$ and $p(j) : A$. But since $A$ is a proposition, we
*have* such a path! If we write $\alpha$ for the witness that `is-prop
A`, we find that we can fill the $i = i0$ square by $\alpha(x,p(j),k)$.
All of the other squares follow this same reasoning. You can see them in
the code below.

```agda
is-prop→is-set : is-prop A → is-set A
is-prop→is-set h x y p q i j = hcomp (∂ i ∨ ∂ j) λ where
  k (k = i0) → x
  k (j = i0) → h x x k
  k (j = i1) → h x y k
  k (i = i0) → h x (p j) k
  k (i = i1) → h x (q j) k
```

<details>
<summary>For completeness, we can also diagram the solution above.</summary>

A minor snag, which is not relevant to the overall idea, is the boundary
*of the* $\alpha(x, p(j), k)$ square we used for $i = i0$. At $j = i0$,
we're left with $\alpha(x, x, k)$, and not just $x$. Practically, this
means that the filler of the top face can't be $x$, since that wouldn't
agree with the left face on their shared edge; It has to be the
odd-looking $\alpha(x, x, k)$ instead.

~~~{.quiver}
\[\begin{tikzcd}[ampersand replacement=\&]
  x \&\&\&\&\&\& x \\
  \\
  \&\& x \&\& x \\
  \\
  \&\& y \&\& y \\
  \\
  x \&\&\&\&\&\& x
  \arrow[from=1-1, to=3-3]
  \arrow[""{name=0, anchor=center, inner sep=0}, "pj", dashed, from=3-3, to=5-3]
  \arrow[from=7-1, to=5-3]
  \arrow[""{name=1, anchor=center, inner sep=0}, "x"', from=1-1, to=7-1]
  \arrow[""{name=2, anchor=center, inner sep=0}, "y", dashed, from=5-3, to=5-5]
  \arrow[""{name=3, anchor=center, inner sep=0}, "x"', dashed, from=3-3, to=3-5]
  \arrow[""{name=4, anchor=center, inner sep=0}, "{q(j)}"', dashed, from=3-5, to=5-5]
  \arrow[""{name=5, anchor=center, inner sep=0}, "x"', from=7-1, to=7-7]
  \arrow[""{name=6, anchor=center, inner sep=0}, "x", from=1-1, to=1-7]
  \arrow[""{name=7, anchor=center, inner sep=0}, "x", from=1-7, to=7-7]
  \arrow[from=1-7, to=3-5]
  \arrow[from=7-7, to=5-5]
  \arrow["{\alpha(x,x,k)}"{description}, draw=none, from=6, to=3]
  \arrow["{\alpha(x,p(j),k)}"{marking, allow upside down}, draw=none, from=1, to=0]
  \arrow["{\alpha(x,q(j),k)}"{marking, allow upside down}, draw=none, from=4, to=7]
  \arrow["{\alpha(x,y,k)}"{description}, draw=none, from=5, to=2]
\end{tikzcd}\]
~~~

</details>

As an immediate application, we can show that defining the types of
h-level to be the propositions, rather than asking for
*contractible* identity types, does not make a difference in the setup:

```agda
Path-is-hlevel' : (n : Nat) → is-hlevel A (suc n) → (x y : A) → is-hlevel (x ≡ y) n
Path-is-hlevel' 0 ahl x y = record
  { centre = ahl x y
  ; paths  = is-prop→is-set ahl _ _ _
  }
Path-is-hlevel' (suc n) h x y = h x y
```

<!--
```agda
PathP-is-hlevel'
  : ∀ {ℓ} {A : I → Type ℓ} (n : Nat)
  → is-hlevel (A i1) (suc n)
  → (x : A i0) (y : A i1)
  → is-hlevel (PathP A x y) n
PathP-is-hlevel' {A = A} n ahl x y =
  subst (λ e → is-hlevel e n) (sym (PathP≡Path A x y)) (Path-is-hlevel' n ahl _ _)

Path-is-hlevel→is-hlevel
  : ∀ {ℓ} {A : Type ℓ} n
  → (p : (x y : A) → is-hlevel (x ≡ y) n)
  → is-hlevel A (suc n)
Path-is-hlevel→is-hlevel zero wit x y = wit x y .centre
Path-is-hlevel→is-hlevel (suc n) wit = wit
```
-->

### Upwards closure

The proof that propositions are sets extends by induction to a proof
that any $n$-type is an $(n+1)$-type. However, recall we started the
hierarchy with the contractible types, so that the propositions are not
*literally* the base case. We're still missing a proof that being
contractible implies being a proposition. Since we have some cubical
momentum going, it's not hard to construct a [[homogeneous composition]]
that expresses that contractible types are propositions:

```agda
is-contr→is-prop : is-contr A → is-prop A
is-contr→is-prop C x y i = hcomp (∂ i) λ where
  j (i = i0) → C .paths x j
  j (i = i1) → C .paths y j
  j (j = i0) → C .centre
```

Reading the code above as a diagram, we can see that this is precisely
the composition of `sym (C .paths x)` with `C .paths y`. It would not
have made any difference whether we used the pre-existing definition of
*path* composition, but it's always a good idea to practice writing
`hcomp`{.Agda}s.

~~~{.quiver}
\[\begin{tikzcd}
  x && y \\
  \\
  {C \rm{.centre}} && {C .\rm{centre}}
  \arrow[dashed, from=1-1, to=1-3]
  \arrow["{C \rm{.paths}\ x\ j}", from=3-1, to=1-1]
  \arrow["{C \rm{.paths}\ y\ j}"', from=3-3, to=1-3]
  \arrow["{C \rm{.centre}}"', from=3-1, to=3-3]
\end{tikzcd}\]
~~~

With that base case, we can actually perform the inductive argument. A
similar argument extends this to showing that any $n$-type is a
$(k+n)$-type, for any offset $k$.

```agda
is-hlevel-suc : ∀ {ℓ} {A : Type ℓ} (n : Nat) → is-hlevel A n → is-hlevel A (suc n)
is-hlevel-suc 0 x = is-contr→is-prop x
is-hlevel-suc 1 x = is-prop→is-set x
is-hlevel-suc (suc (suc n)) h x y = is-hlevel-suc (suc n) (h x y)

is-hlevel-+ : ∀ {ℓ} {A : Type ℓ} (n k : Nat) → is-hlevel A n → is-hlevel A (k + n)
is-hlevel-+ n zero x    = x
is-hlevel-+ n (suc k) x = is-hlevel-suc _ (is-hlevel-+ n k x)
```

A very convenient specialisation of these arguments will allow us to
lift a proof that $A$ is a proposition to a proof that it has any
positive h-level.

```agda
is-prop→is-hlevel-suc
  : ∀ {ℓ} {A : Type ℓ} {n : Nat} → is-prop A → is-hlevel A (suc n)
is-prop→is-hlevel-suc {n = zero} aprop = aprop
is-prop→is-hlevel-suc {n = suc n} aprop =
  is-hlevel-suc (suc n) (is-prop→is-hlevel-suc aprop)
```

<!--
```agda
is-contr→is-hlevel : ∀ {ℓ} {A : Type ℓ} n → is-contr A → is-hlevel A n
is-contr→is-hlevel zero c = c
is-contr→is-hlevel (suc n) c = is-prop→is-hlevel-suc (is-contr→is-prop c)

is-set→is-hlevel+2
  : ∀ {ℓ} {A : Type ℓ} {n : Nat} → is-set A → is-hlevel A (2 + n)
is-set→is-hlevel+2 aset x y = is-prop→is-hlevel-suc (aset x y)
```
-->

Finally, we'll bootstrap some results about the closure of $n$-types
under various operations. Here, we can immediately show that the
identity types of an $n$-type are again $n$-types.

```agda
Path-is-hlevel
  : (n : Nat) → is-hlevel A n
  → {x y : A} → is-hlevel (x ≡ y) n
Path-is-hlevel zero ahl = record
  { centre = is-contr→is-prop ahl _ _
  ; paths  = is-prop→is-set (is-contr→is-prop ahl) _ _ _
  }
Path-is-hlevel (suc n) ahl = is-hlevel-suc (suc n) ahl _ _

PathP-is-hlevel
  : ∀ {A : I → Type ℓ} (n : Nat)
  → is-hlevel (A i1) n
  → ∀ {x y} → is-hlevel (PathP A x y) n
PathP-is-hlevel {A = A} n ahl {x} {y} =
  subst (λ e → is-hlevel e n) (sym (PathP≡Path A x y)) (Path-is-hlevel n ahl)
```

Note that, while a contractible type is not *literally* defined to be a
pointed proposition, these notions are equivalent. Indeed, if a type is
contractible *assuming* it is pointed, it is a proposition, as the two
arguments below show. This explains why propositions are sometimes
referred to as *contractible-if-inhabited*, but we will not use this
terminology.

```agda
is-contr-if-inhabited→is-prop : ∀ {ℓ} {A : Type ℓ} → (A → is-contr A) → is-prop A
is-contr-if-inhabited→is-prop cont x y = is-contr→is-prop (cont x) x y

is-prop∙→is-contr : ∀ {ℓ} {A : Type ℓ} → is-prop A → A → is-contr A
is-prop∙→is-contr prop x .centre = x
is-prop∙→is-contr prop x .paths y = prop x y
```

### Propositionality of truncatedness

With upwards closure out of the way, we can show that being a
proposition is a proposition. We have already mentioned it, and gestured
towards the proof: since every proposition is a set, any two functions
$\alpha, \beta : \forall_{x, y : A} x \equiv y$ must agree, pointwise,
on any $x, y : A$. The code is similarly simple:

```agda
is-prop-is-prop : is-prop (is-prop A)
is-prop-is-prop α β i x y = is-prop→is-set α x y (α x y) (β x y) i
```

To show that being contractible is a proposition, we'll use a similar
argument. It will suffice to show that the centres of contraction are
identical, and that, over this, we have an identification between the
contractions. This has a delightfully short proof also:

```agda
is-contr-is-prop : is-prop (is-contr A)
is-contr-is-prop c₁ c₂ i .centre = c₁ .paths (c₂ .centre) i
is-contr-is-prop c₁ c₂ i .paths x j = hcomp (∂ i ∨ ∂ j) λ where
  k (i = i0) → c₁ .paths (c₁ .paths x j) k
  k (i = i1) → c₁ .paths (c₂ .paths x j) k
  k (j = i0) → c₁ .paths (c₁ .paths (c₂ .centre) i) k
  k (j = i1) → c₁ .paths x k
  k (k = i0) → c₁ .centre
```

Once again, we can extend this pair of base cases to the entire
hierarchy, by an inductive argument of the same shape as the one we used
for upwards closure.

```agda
is-hlevel-is-prop : ∀ {ℓ} {A : Type ℓ} (n : Nat) → is-prop (is-hlevel A n)
is-hlevel-is-prop 0 = is-contr-is-prop
is-hlevel-is-prop 1 = is-prop-is-prop
is-hlevel-is-prop (suc (suc n)) x y i a b =
  is-hlevel-is-prop (suc n) (x a b) (y a b) i
```

<!--
```agda
is-hlevel-is-hlevel-suc : ∀ {ℓ} {A : Type ℓ} (k n : Nat) → is-hlevel (is-hlevel A n) (suc k)
is-hlevel-is-hlevel-suc k n = is-prop→is-hlevel-suc (is-hlevel-is-prop n)
```
-->

## Dependent h-levels

When working in a homotopy type theory, we often have to consider, in
addition to identity types, *dependent* identity types; in cubical type
theory, these are the primitive notion, implemented by `PathP`{.Agda}s.
Regardless, it makes sense to extend the notion of h-level to talk not
only about identifications in a type, but about arbitrary *dependent*
identifications in a *family* of types.

Rather than novelty, this notion of **dependent h-level** does turn out
to have practical applications --- except for the dependent analogue to
*contractibility*. Therefore, we bootstrap this notion with the
_dependent propositions_: A family $P(x)$ over $X$ is a dependent
proposition if any pair of elements are identified, over an arbitrary
path in the base:

```agda
is-hlevel-dep : ∀ {ℓ ℓ'} {A : Type ℓ} → (A → Type ℓ') → Nat → Type _
is-hlevel-dep B zero =
  ∀ {x y} (α : B x) (β : B y) (p : x ≡ y)
  → PathP (λ i → B (p i)) α β

is-hlevel-dep B (suc n) =
  ∀ {a0 a1} (b0 : B a0) (b1 : B a1)
  → is-hlevel-dep {A = a0 ≡ a1} (λ p → PathP (λ i → B (p i)) b0 b1) n
```

However, there is an *emergent* notion of h-level for families, namely,
the pointwise lifting of the ordinary, non-dependent h-levels. While the
notion we've just defined is more convenient to work with cubically,
we're led to wonder how it compares to the pointwise notion.
Fortunately, they are equivalent.

```agda
is-prop→pathp
  : ∀ {B : I → Type ℓ} → ((i : I) → is-prop (B i))
  → ∀ b0 b1 → PathP (λ i → B i) b0 b1
is-prop→pathp {B = B} hB b0 b1 = to-pathp (hB _ _ _)
```

The base case is usefully phrased as the helper lemma
`is-prop→pathp`{.Agda} above: if we have a *line of types* $B(i)$ over
$i : \bI$ which is a proposition everywhere, then we can construct a
`PathP`{.Agda} over $B$ between any points in the two fibres. The
inductive case uses path induction to focus on a single fibre:

```agda
is-hlevel→is-hlevel-dep
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
  → (n : Nat) → ((x : A) → is-hlevel (B x) (suc n))
  → is-hlevel-dep B n
is-hlevel→is-hlevel-dep zero hl α β p = is-prop→pathp (λ i → hl (p i)) α β
is-hlevel→is-hlevel-dep {A = A} {B = B} (suc n) hl {a0} {a1} b0 b1 =
  is-hlevel→is-hlevel-dep n (λ p → helper a1 p b1)
  where
    helper : (a1 : A) (p : a0 ≡ a1) (b1 : B a1)
           → is-hlevel (PathP (λ i → B (p i)) b0 b1) (suc n)
    helper a1 p b1 =
      J (λ a1 p → ∀ b1 → is-hlevel (PathP (λ i → B (p i)) b0 b1) (suc n))
        (λ _ → hl _ _ _) p b1
```

## Contractibility, geometrically

In cubical type theory, rather than reasoning algebraically about
iterated identity types, we often prefer the more direct option of
reasoning in a higher-dimensional context, using lifting problems.
However, the notions of h-level we have defined all talk about these
iterated identity types. There is a more *natively cubical* phrasing of
contractiblity, which we now introduce, in terms of [[extensibility]].

Suppose we have a partial element $\phi \vdash p : A$ defined on some
cofibration $\phi$. Does $p$ extend to a total element? If $A$ is
contractible, yes! We have a base point $c : A$, the centre of
contraction, and, taking $\phi$ as the shape of a lifting problem, we
can certainly find a system of partial paths $\phi \vdash c \equiv p$
--- $A$ is a proposition, after all!

```agda
is-contr→extend : is-contr A → (φ : I) (p : Partial φ A) → A [ φ ↦ p ]
is-contr→extend C φ p = inS do hcomp (φ ∨ ~ φ) λ where
  j (j = i0) → C .centre
  j (φ = i0) → C .centre
  j (φ = i1) → C .paths (p 1=1) j
```

Conversely, if we know that every partial element $A$ (with our choice
of shape $\phi$) is extensible, we can prove that $A$ is contractible.
The centre is given by extending the *empty* partial element, taking
$\phi = i0$:

```agda
extend→is-contr : (∀ φ (p : Partial φ A) → A [ φ ↦ p ]) → is-contr A
extend→is-contr ext .centre = outS (ext i0 λ ())
```

To come up with a path connecting this empty extension and an $x : A$,
we can extend the partial element that is $x$ when $i = i1$, and
undefined everywhere. On the left endpoint, when $i = i0$, this is
exactly the empty system we used above!

```agda
extend→is-contr ext .paths x i = outS (ext i λ _ → x)
```

We can use this to write a more direct proof that contractible types are
sets, eliminating the passage through the proof that they are
propositions.

```agda
is-contr→is-set : is-contr A → is-set A
is-contr→is-set C x y p q i j = outS do
  is-contr→extend C (∂ i ∨ ∂ j) λ where
    (i = i0) → p j
    (i = i1) → q j
    (j = i0) → x
    (j = i1) → y
```

<!--
```agda
is-contr→pathp : ∀ {B : I → Type ℓ} → ((i : I) → is-contr (B i))
              → (b0 : B i0) (b1 : B i1)
              → PathP (λ i → B i) b0 b1
is-contr→pathp hB b0 b1 = is-prop→pathp (λ i → is-contr→is-prop (hB i)) b0 b1

SingletonP : ∀ {ℓ} (A : I → Type ℓ) (a : A i0) → Type _
SingletonP A a = Σ[ x ∈ A i1 ] PathP A a x

SinglP-is-contr : ∀ {ℓ} (A : I → Type ℓ) (a : A i0) → is-contr (SingletonP A a)
SinglP-is-contr A a .centre = _ , transport-filler (λ i → A i) a
SinglP-is-contr A a .paths (x , p) i = _ , λ j → fill A (∂ i) j λ where
  j (i = i0) → coe0→i A j a
  j (i = i1) → p j
  j (j = i0) → a

SinglP-is-prop : ∀ {ℓ} {A : I → Type ℓ} {a : A i0} → is-prop (SingletonP A a)
SinglP-is-prop = is-contr→is-prop (SinglP-is-contr _ _)


is-prop→squarep
  : ∀ {B : I → I → Type ℓ} → ((i j : I) → is-prop (B i j))
  → {a : B i0 i0} {b : B i0 i1} {c : B i1 i0} {d : B i1 i1}
  → (p : PathP (λ j → B j i0) a c)
  → (q : PathP (λ j → B i0 j) a b)
  → (s : PathP (λ j → B i1 j) c d)
  → (r : PathP (λ j → B j i1) b d)
  → SquareP B p q s r
is-prop→squarep {B = B} is-propB {a = a} p q s r i j =
  hcomp (∂ j ∨ ∂ i) λ where
    k (j = i0) → is-propB i j (base i j) (p i) k
    k (j = i1) → is-propB i j (base i j) (r i) k
    k (i = i0) → is-propB i j (base i j) (q j) k
    k (i = i1) → is-propB i j (base i j) (s j) k
    k (k = i0) → base i j
  where
    base : (i j : I) → B i j
    base i j = transport (λ k → B (i ∧ k) (j ∧ k)) a

is-prop→pathp-is-contr
  : {A : I → Type ℓ} → ((i : I) → is-prop (A i))
  → (x : A i0) (y : A i1) → is-contr (PathP A x y)
is-prop→pathp-is-contr ap x y .centre = is-prop→pathp ap x y
is-prop→pathp-is-contr ap x y .paths p =
  is-prop→squarep (λ i j → ap j) refl _ _ refl

abstract
  is-set→squarep :
    {A : I → I → Type ℓ}
    (is-set : (i j : I) → is-set (A i j))
    → {a : A i0 i0} {b : A i0 i1} {c : A i1 i0} {d : A i1 i1}
    → (p : PathP (λ j → A j i0) a c)
    → (q : PathP (λ j → A i0 j) a b)
    → (s : PathP (λ j → A i1 j) c d)
    → (r : PathP (λ j → A j i1) b d)
    → SquareP A p q s r
  is-set→squarep isset a₀₋ a₁₋ a₋₀ a₋₁ =
    transport (sym (PathP≡Path _ _ _))
              (PathP-is-hlevel' 1 (isset _ _) _ _ _ _)

-- Has to go through:
_ : ∀ {A : Type} {a b c d : A} (p : a ≡ c) (q : a ≡ b) (s : c ≡ d) (r : b ≡ d)
  → Square p q s r ≡ SquareP (λ _ _ → A) p q s r
_ = λ _ _ _ _ → refl

is-set→cast-pathp
  : ∀ {ℓ ℓ'} {A : Type ℓ} {x y : A} {p q : x ≡ y} (P : A → Type ℓ') {px : P x} {py : P y}
  → is-set A
  → PathP (λ i → P (p i)) px py
  → PathP (λ i → P (q i)) px py
is-set→cast-pathp {p = p} {q = q} P {px} {py} set  r =
  coe0→1 (λ i → PathP (λ j → P (set _ _ p q i j)) px py) r

is-set→subst-refl
  : ∀ {ℓ ℓ'} {A : Type ℓ} {x : A}
  → (P : A → Type ℓ')
  → is-set A
  → (p : x ≡ x)
  → (px : P x)
  → subst P p px ≡ px
is-set→subst-refl {x = x} P set p px i =
  transp (λ j → P (set x x p refl i j)) i px
```
-->
