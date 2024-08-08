<!--
```agda
open import 1Lab.Type

open import Prim.Data.Bool
open import Prim.Extension
open import Prim.Interval
open import Prim.Kan
```
-->

```agda
module 1Lab.Path where
```

<!--
```agda
open Prim.Extension public
open Prim.Interval public
open Prim.Kan public

-- Slightly ugly type to demonstrate the algebraic properties of the
-- interval.
private
  data _≡ⁱ_ (i : I) : (j : I) → SSet where
    reflⁱ : i ≡ⁱ i

  infix 10 _≡ⁱ_

  variable
    ℓ : Level
    A B : Type ℓ
    f g : A → B
    x y : A
```
-->

# Paths and the interval

One of the key observations behind HoTT is that [[the inductive
*identity type*|inductive identity]] can be given a *spatial*
interpretation: if we interpret a type $A$ as a space, then for a pair
of points $a, b : A$, the identity type $a \is b$ behaves like the space
of *paths* from $a$ to $b$ in $A$.  There is a constant path $\refl : a
\is a$ at each point; every path $p : a \is b$ has an inverse $p\inv : b
\is a$; paths $p : a \is b$ and $q : b \is c$ can be laid end-to-end,
giving the composite $p\cdot q : a \is c$. Even further, these
operations can be shown to satisfy algebraic laws, like the inverse law
$p\inv \cdot p \is \refl$, but only up to paths-between-paths:
*homotopies*.

In the homotopy theory of topological spaces, paths in a space $A$ are
defined to be continuous mappings $f : [0,1] \to A$ from the *interval*
to our space. The key idea behind cubical type theory, and thus our
implementation Cubical Agda, is that by axiomatizing the important
properties of $[0,1]$ as an **interval type** $\bI$, we could similarly
define *paths* to be functions $\bI \to A$. We don't have to cut down to
a type of "continuous" functions; instead, we arrange for the interval
*type* to be so that all functions from it are continuous.

<details>
<summary>
A brief comment on the meanings of "equal", "identical" and
"identified", and how we refer to inhabitants of path types.
</summary>

Before getting started, it's worth taking a second to point out the
terminology that will be used in this module (and most of the other
pages). In intensional type theory, there is both an external notion of
"sameness" (definitional equality), and an internal notion of
"sameness", which goes by many names: identity type, equality type,
propositional equality, path type, etc.

In this module, we refer to the type `A ≡ B` as either (the type of)
_paths from A to B_ or (the type of) _identifications between A and B_,
but **never** as "equalities between A and B". In particular, the HoTT
book comments that we may say "$a$ and $b$ are equal" when the type $a
\is b$ is inhabited, but in this development we reserve this terminology
for the case where $a$ and $b$ inhabit a [[set]], i.e. when there can be
at most one $p : a \is b$.

Instead, for general types, we use "$a$ and $b$ are **identical**" or
"$a$ and $b$ are **identified**" (or even the wordier, and rather more
literal, "there is a path between $a$ and $b$"). Depending on the type,
we might use more specific words: Paths are said to be **homotopic**
when they're connected by a path-of-paths, and types are said to be
**equivalent** when they are connected by a path.

</details>

While the type $\bI$ is meant to represent the unit interval $[0,1]$, we
don't have to bake an axiomatization of the real numbers into our type
theory. For the purposes of representing identifications, we can get
away with treating the interval as mostly featureless. To start with,
we'll see that the interval is equipped with **endpoints**, the values
$\iZ, \iO : \bI$, its start and end. If we have an arbitrary $f : \bI \to
A$, we say that it is a path *from* $f(\iZ)$ *to* $f(\iO)$. Of course,
most of the time, we're interested in identifying elements we already
know about: we talk not about paths, but about **paths from $a$ to
$b$**.

:::{.definition #path}
However, we can not internally *define* the type of "functions $f : \bI
\to A$ which satisfy $f(\iZ) = a$ and $f(\iO) = b$"; not only can we not
internally talk of definitional equality, but we don't even have a
notion of sameness yet: that's what we're trying to define! Instead,
cubical type theory is equipped with a *primitive* type of **paths from
$a$ to $b$**.
:::

This type, like any other, has formation and elimination rules.
Informally, the formation rule says that any function $f : \bI \to A$
can be made into a path $f(\iZ) \is f(\iO)$, and the elimination rule
says that if we have $i : \bI$, and a path $p : a \is b$, we can apply
$p(i)$ and get out a value of $A$. In formal presentations of cubical
type theory (e.g.  CCHM [-@CCHM]), paths are introduced and eliminated
with their own syntax. In Agda, we instead *overload* the lambda
notation, and function application, so that it can be used for both
functions *and* paths.

Therefore, while we can define a helper that upgrades any function to a
path, it looks a lot like the identity function; we do not *require*
this helper, since we can always write paths using the same syntax as
for functions.

When we can infer the type $A$ from the points $a, b : A$, we write the
type of paths as $a \is b$, both in the formalisation and the prose.
This is traditional in Agda, but slightly breaks with the convention of
type theory *literature*, which traditionally uses $a \is b$ to mean
definitional equality.

```agda
private
  to-path : ∀ {ℓ} {A : Type ℓ} (f : I → A) → f i0 ≡ f i1
  to-path f = λ i → f i
```

The easiest path to construct is *reflexivity*, called `refl`{.Agda} for
short: Given a point $a : A$, there is a distinguished path $\refl_a : a
\is a$, which goes from $a$ to $a$ by ignoring the interval variable $i$
entirely.

```agda
refl : ∀ {ℓ} {A : Type ℓ} {x : A} → x ≡ x
refl {x = x} i = x
```

Before we move on, we can also demonstrate the elimination rule for
paths *as functions from the interval*, that is, application. Note that,
when we apply $p : a \is b$ to one of the endpoints of the interval, we
*definitionally* get back the endpoints of the path. Other than the
circularity (needing sameness to define paths, which are our notion of
sameness), these definitional equalities are the reason that paths are a
primitive type former.

```agda
module _ {ℓ} {A : Type ℓ} {a b : A} {p : a ≡ b} where private
  apply-path : (i : I) → A
  apply-path i = p i

  left-endpoint : p i0 ≡ a
  left-endpoint = refl

  right-endpoint : p i1 ≡ b
  right-endpoint = refl
```

## Dependent paths {defines="dependent-path path-over"}

Since we're working in dependent type theory, a sensible question to ask
is whether we can extend the idea that paths are functions $\bI \to A$
to *dependent* functions $(i : \bI) \to A(i)$. Indeed we can, and these
turn out to be very useful: they're **dependent paths**. We'll have
[more to say on these later](#dependent-paths-continued), to connect
them with another emergent notion of dependent path, but it's important
to mention the primitive notion now.

If we have a *line* of types $A : \bI \to \ty$, and inhabitants $a :
A(\iZ)$ and $b : A(\iO)$, we can form the **dependent** path space
between them: the type $\PathP{A}{a}{b}$, which in the code is written
`PathP A a b`. Here, inferring the line $A$ is basically always
impossible, so we'll always write it explicitly. As before, these
correspond 1-1 to dependent functions which map the endpoints to $a$ and
$b$. To avoid repetition, we'll take this opportunity to write out the
typing rules, if that helps.

::: mathpar

$$
\frac{
  \Gamma, i : \bI \vdash e : A \quad
  \Gamma \vdash e(\iZ) = a : A(\iZ) \quad
  \Gamma \vdash e(\iO) = b : A(\iO) \quad
}{
  \Gamma \vdash (\lam{i}{e}) : \PathP{A}{a}{b}
}
$$

$$
\frac{
  \Gamma \vdash p : \PathP{A}{a}{b} \quad
  \Gamma \vdash i : \bI
}{
  \Gamma \vdash p(i) : A(i)
}
$$

$$
\frac{
  \Gamma \vdash p : \PathP{A}{a}{b}
}{
  \Gamma \vdash p(\iZ) = a : A(\iZ)
}
$$

$$
\frac{
  \Gamma \vdash p : \PathP{A}{a}{b}
}{
  \Gamma \vdash p(\iO) = b : A(\iO)
}
$$

:::

Colloquially, we speak of a value $p : \PathP{A}{a}{b}$ as a path
between $a$ and $b$ **over $A$**. Formally, the idea is that, while $a$
and $b$ may live in different types, $A$ is an identification between
them; and, *over* this identification, $a$ and $b$ are identical. The
generic situation for a path over a path is pictured in the diagram
below.

~~~{.quiver}
\begin{tikzpicture}

\node (baseA0) at (-2.25, -0.5) {$A(\iZ)$};
\node (baseA1) at (2.5,   0.5)  {$A(\iO)$};

% Control points for the Bézier path in the base space
\node (C1) at (-0.75, -1.5) {};
\node (C2) at (0.75, 0.9)   {};
\draw[->] (baseA0) .. controls (C1) and (C2) .. (baseA1);

% Draw the base space itself (a potato, like any space, but more like a
% smoothed out triangle)
\draw plot[smooth cycle] coordinates
  {(0, -1.5) (-3, -0.75) (-2.5, 0.25) (3, 1.25) (3.5, 0.25)};

\node at (2.75, -1) {$\ty$};

\node (A) at (0.275, -0.375) {$A$};

\node (a) at (-2.25, 1.5) {$a$};
\node (b) at (2.5,   2.5) {$b$};

\draw[->] (a) -- node[above] {$p$} (b);
\draw[lies over] (a) -- (baseA0);
\draw[lies over] (b) -- (baseA1);

\end{tikzpicture}
~~~

Above, we have a blob representing the type of types, `Type`{.Agda},
which is on the bottom of the image. The line of types $A$ is drawn as a
literal path between the points $A(\iZ)$ and $A(\iO)$ in this space. On
top, we have the points $a$ and $b$, which "lie over" their respective
types. And finally, our $p : \PathP{A}{a}{b}$ is path from $a$ to $b$
*over* the path $A$.

Even though we introduced `Path`{.Agda} first, the `PathP`{.Agda}
connective, being more general, is the actual *primitive* provided by
Agda. The path type $a \is b$, and its longhand $\Path{A}{a}{b}$, are
defined in terms of `PathP`{.Agda}.

```agda
Path : ∀ {ℓ} (A : Type ℓ) (x y : A) → Type ℓ
Path A x y = PathP (λ i → A) x y
```

## Symmetry

Now that we have the notion of paths, we'll spend the rest of this
module setting up the structure *around* them that makes them useful. A
good place to start with are the **inverses**: there should be an
operation mapping paths $p : a \is b$ to paths $p\inv : b \is a$. In
Cubical Agda, we work in *de Morgan* cubical type theory. This means
that, in addition to the endpoints $\iZ, \iO$, the interval is equipped
with a few extra bits of algebraic structure, to make working with paths
more convenient.

The relevant operation here is the de Morgan **negation**, written
$\ineg i$ in the prose and `~_`{.Agda} in the formalisation. In addition
to interacting with the other operations, the negation satisfies $\ineg
\iZ = \iO$ and $\ineg \iO = \iZ$, and $\ineg (\ineg i) = i$. The first
two imply that we can use it to implement inverses: for if we have $p :
a \equiv b$, then $q = \lam{i}{p\ (\ineg i)}$ satisfies $q(\iZ) = p(\iO)
= b$ and $q(\iZ) = p(\iO) = a$.

```agda
sym : ∀ {ℓ} {A : Type ℓ} {x y : A} → x ≡ y → y ≡ x
sym p i = p (~ i)
```

We can also invert *dependent* paths: if $a : A(\iZ)$ and $b : A(\iO)$
are identified over a line $A$, then $b$ and $a$ are identified over the
inverse of $A$.

```agda
symP : ∀ {ℓ} {A : I → Type ℓ} {x : A i0} {y : A i1}
     → PathP A x y → PathP (λ i → A (~ i)) y x
symP p i = p (~ i)
```

Since we have $\ineg \ineg i = i$, these operations are both
*definitional* involutions. Once we implement path *composition*, we'll
be able to show that $p\inv$ is legitimately the inverse to $p$.

<!--
```agda
module _ {ℓ} {A : I → Type ℓ} {x : A i0} {y : A i1} (p : PathP A x y) where
```
-->

```agda
  _ : symP (symP p) ≡ p
  _ = refl
```

## Raising dimension

To recap, in cubical type theory, a term in a context with $n$ interval
variables expresses a way of mapping the $n$-cube into that type. So
far, we have been talking about mapping the $1$-cube, i.e. the line,
into types, producing identifications. But the type of paths $a \is b$
is itself a type, so if we have $p, q : a \is b$, we can form the
iterated path type $p \is q$. Cubically, we're now talking about
functions $\bI \to \bI \to A$, with *two* dimensions: a way of mapping
the *square* into a type.

If we consider a path $p : a \is b$ as an object in its own right, we
can consider the reflexivity path $\refl_p : p \is p$, which by the
paragraph above lives one dimension higher. In this section, we'll
explore the *other* ways in which we can lift $n$-cubes to $n+1$ cubes,
and to higher dimensions from there.

<!--
```agda
module _ {ℓ} {A : Type ℓ} {a b : A} {p : Path A a b} where private
```
-->

In a context with two interval variables, we can move in two dimensions
(call them $i$ and $j$): to use our path $p$, which only varies along
*one* dimension, we must either *discard* one of $i$ or $j$, or find a
way to *combine* them. Discarding is the easier option. Depending on
what dimension we ignore, we get one of two squares, both of which have
two $p$ faces *across* from eachother. Note that the square
`drop-i`{.Agda} is just the reflexivity path `refl`{.Agda}.

```agda
  drop-i : PathP (λ i → a ≡ b) p p
  drop-i i j = p j

  _ : drop-i ≡ refl
  _ = refl

  drop-j : PathP (λ i → p i ≡ p i) refl refl
  drop-j i j = p i
```

Let's look at how to visualise these squares. First, we should note the
direction our axes go in: $i$ varies from the left to the right, and $j$
varies top-to-bottom. The `drop-i`{.Agda} square is *constant* in the
$i$ direction, but in the $j$ direction, it's $p$. This manifests in the
diagram as having $\refl$ for both of its vertical faces: on the left,
we're looking at $p(\iZ) = a$ *not* varying along the vertical axis, and
respectively for $p(\iO) = b$ on the right. For the `drop-j`{.Agda}
square, the situation is flipped, since we're now ignoring the
horizontal direction.

<div class="mathpar">

~~~{.quiver}
\indicatortwod{i}{j}
~~~

~~~{.quiver}
\[\begin{tikzcd}
  a && a \\
  & {\footnotesize \text{drop-i}} \\
  b && b
  \arrow["{p(\iZ)~ =~ a}", from=1-1, to=1-3]
  \arrow["{p(\iO)~ =~ b}"', from=3-1, to=3-3]
  \arrow["p(j)"{description}, from=1-1, to=3-1]
  \arrow["p(j)"{description}, from=1-3, to=3-3]
\end{tikzcd}\]
~~~

~~~{.quiver}
\[\begin{tikzcd}
  a && b \\
	& {\footnotesize \text{drop-j}} \\
  a && b
  \arrow["p(i)", from=1-1, to=1-3]
  \arrow["p(i)"', from=3-1, to=3-3]
  \arrow["{p(\iZ)~ =~ a}"{description}, from=1-1, to=3-1]
  \arrow["{p(\iO)~ =~ b}"{description}, from=1-3, to=3-3]
\end{tikzcd}\]
~~~

</div>

:::{.definition #connection}
We can now introduce the two operators that go into making the interval
a de Morgan algebra: minimum, written $i \imin j$, and maximum, $i \imax
j$. As we'll see [below](#summary-of-interval-algebra), these satisfy
the familiar rules for conjunctions and disjunctions in logic, hence the
notation. But keep in mind that $\bI$ is not like $\{0,1\}$, but rather
more like $[0,1]$: we do not have $(i \imin \ineg i) = \iZ$, because
there are points along the interval where the "minimum" of $i$ and "$1 -
i$" is not zero.
:::

```agda
  ∧-conn : PathP (λ i → a ≡ p i) refl p
  ∧-conn i j = p (i ∧ j)

  ∨-conn : PathP (λ i → p i ≡ b) p refl
  ∨-conn i j = p (i ∨ j)
```

These correspond to the following two squares, called **connections**.
In the diagrams below, we do not have the space to include the
computation for the faces that vary along $j$, but we did include them
for the faces varying along $i$, e.g., in the $p(i\imin j)$ square, the
left face (varying along $j$, with $i = \iZ$) is
$$
p(\iZ\imin j) = p(\iZ) = a
$$,
while the right face in $p(i\imax j)$ is $$p(\iO\imax j) = p(\iO) = b$$.

<div class="mathpar">

~~~{.quiver}
\indicatortwod{i}{j}
~~~

~~~{.quiver}
\[\begin{tikzcd}[ampersand replacement=\&]
  a \&\& a \\
  \& {p(i\imin j)} \\
  a \&\& b
  \arrow["{p(i \imin \iZ)~ =~ p(\iZ)~ =~ a}", from=1-1, to=1-3]
  \arrow["{a}"{description}, from=1-1, to=3-1]
  \arrow["{p(j)}"{description}, from=1-3, to=3-3]
  \arrow["p(i \imin \iO)~ =~ p(i)"', from=3-1, to=3-3]
\end{tikzcd}\]
~~~

~~~{.quiver}
\[\begin{tikzcd}
  a && b \\
  & {p(i\imax j)} \\
  b && b
  \arrow["{p(i \imax \iZ)~ =~ p(i)}", from=1-1, to=1-3]
  \arrow["{p(i \imax \iO)~ =~ p(\iO)~ =~ b}"', from=3-1, to=3-3]
  \arrow["p(j)"{description}, from=1-1, to=3-1]
  \arrow["{b}"{description}, from=1-3, to=3-3]
\end{tikzcd}\]
~~~

</div>

Iterated paths are used a *lot* in homotopy type theory, but in cubical
type theory, it's best to have a type that lets us specify the boundary
of a complete 2-dimensional *square*. Pictorially, we lay out a square
with faces $p$, $q$, $r$, and $s$, as in the diagram below.

::: mathpar
~~~{.quiver}
\indicatortwod{i}{j}
~~~

~~~{.quiver}
\[\begin{tikzcd}
  {a_{00}} && {a_{10}} \\
  \\
  {a_{01}} && {a_{11}}
  \arrow["q(i)"', from=1-1, to=3-1]
  \arrow["p(j)", from=1-1, to=1-3]
  \arrow["s(i)", from=1-3, to=3-3]
  \arrow["r(j)"', from=3-1, to=3-3]
\end{tikzcd}\]
~~~
:::

Intuitively, we may read this square as saying that the *composites* $q
\cdot r$ and $p \cdot s$ are identified.[^comm-to-square] In the 1Lab,
we define the type `Square`{.Agda} so that the arguments are given in
the order $p$-$q$-$s$-$r$, i.e. top-left-right-bottom. This choice is
basically arbitrary, but it matters when reading out the (graphical)
boundary from the type of a term.

[^comm-to-square]:
    At this point in the formalisation, we have not yet introduced the
    machinery necessary to define composition of paths, let alone prove
    that squares correspond to identities between composites.

    However, it's instructive to keep this intuition in mind for when we
    *do* define composition, and for when we can [prove this
    correspondence](1Lab.Path.Groupoid.html#convenient-helpers).

```agda
Square
  : ∀ {ℓ} {A : Type ℓ} {a00 a01 a10 a11 : A}
  → (p : a00 ≡ a01) (q : a00 ≡ a10) (s : a01 ≡ a11) (r : a10 ≡ a11)
  → Type ℓ
Square p q s r = PathP (λ i → p i ≡ r i) q s
```

To start building some intuition, we can rewrite the dimension-raising
operations we named above so that their types are given in terms of
`Square`{.Agda}. We also ask Agda to check that a square with top/bottom
faces `refl`{.Agda}, but left/right faces $p$, is the same thing as a
path between paths.

<!--
```agda
module _ {ℓ} {A : Type ℓ} {a b : A} {p : Path A a b} where private
```
-->

```agda
  drop-i : Square refl p p refl
  drop-i i j = p j

  drop-j : Square p refl refl p
  drop-j i j = p i

  ∧-conn : Square refl refl p p
  ∧-conn i j = p (i ∧ j)

  ∨-conn : Square p p refl refl
  ∨-conn i j = p (i ∨ j)
```


<!--
```agda
module _ {ℓ} {A : Type ℓ} {a b : A} {p q : Path A a b} where private
```
-->

```agda
  _ : Square refl p q refl ≡ (p ≡ q)
  _ = refl
```

<!--
```
SquareP : ∀ {ℓ}
  (A : I → I → Type ℓ)
  {a₀₀ : A i0 i0} {a₀₁ : A i0 i1}
  {a₁₀ : A i1 i0} {a₁₁ : A i1 i1}
  (p : PathP (λ i → A i i0) a₀₀ a₁₀)
  (q : PathP (λ j → A i0 j) a₀₀ a₀₁)
  (s : PathP (λ j → A i1 j) a₁₀ a₁₁)
  (r : PathP (λ i → A i i1) a₀₁ a₁₁)
  → Type ℓ
SquareP A p q s r = PathP (λ i → PathP (λ j → A i j) (p i) (r i)) q s
```
-->

<!--
```agda
module
  _ {ℓ} {A : Type ℓ} {a00 a01 a10 a11 : A}
    {p : a00 ≡ a01} {q : a00 ≡ a10}
    {s : a01 ≡ a11} {r : a10 ≡ a11}
  where
```
-->

The last operations we consider *preserve* dimension, rather than
altering it. If we have a square $\alpha : \Square{p}{q}{s}{r}$, there
are a few symmetry-like operations we can apply to it, which correspond
to inverting either axis, or swapping them.

```agda
  flip₁ : Square p q s r → Square (sym p) s q (sym r)
  flip₁ α i j = α (~ i) j

  flip₂ : Square p q s r → Square r (sym q) (sym s) p
  flip₂ α i j = α i (~ j)

  transpose : Square p q s r → Square q p r s
  transpose α i j = α j i
```

### Summary of interval algebra

We'll conclude this section with a complete listing of the rules that
the algebraic operations on the interval satisfy. These all hold
definitionally, so we'll omit the proofs.

<!--
```agda
module _ where private
  variable
    i j : I
```
-->

```agda
  -- Laws governing _∧_
  ∧-comm  : i ∧ j ≡ⁱ j ∧ i
  ∧-idem  : i ∧ i ≡ⁱ i
  ∧-zero  : i ∧ i0 ≡ⁱ i0
  ∧-one   : i ∧ i1 ≡ⁱ i
  ∧-abs-∨ : i ∧ (i ∨ j) ≡ⁱ i

  -- Laws governing _∨_
  ∨-comm  : i ∨ j ≡ⁱ j ∨ i
  ∨-idem  : i ∨ i ≡ⁱ i
  ∨-zero  : i ∨ i0 ≡ⁱ i
  ∨-one   : i ∨ i1 ≡ⁱ i1
  ∨-abs-∧ : i ∨ (i ∧ j) ≡ⁱ i

  -- Laws governing ~_
  ~-invol  : ~ (~ i) ≡ⁱ i
  demorgan : ~ (i ∧ j) ≡ⁱ ~ i ∨ ~ j
  ~-zero   : ~ i0 ≡ⁱ i1
  ~-one    : ~ i1 ≡ⁱ i0
```

<!--
```agda
  ∨-idem    = reflⁱ
  ∧-one     = reflⁱ
  ∧-comm    = reflⁱ
  ∧-zero    = reflⁱ
  ∧-idem    = reflⁱ
  ∨-comm    = reflⁱ
  ∨-zero    = reflⁱ
  ∨-one     = reflⁱ
  ~-invol   = reflⁱ
  demorgan  = reflⁱ
  ~-zero    = reflⁱ
  ~-one     = reflⁱ
  ∧-abs-∨   = reflⁱ
  ∨-abs-∧   = reflⁱ
```
-->

# Paths as "sameness"

One of the fundamental features of equality is that it is respected by
all functions: if we have $f : A \to B$, and $x = y : A$, then also
$f(x) = f(y)$. In our homotopical setting, we must generalise this to
talking about *paths* $p : x \is y$, and we must also name the resulting
$f(x) \is f(y)$. In cubical type theory, our homotopical intuition for
paths provides the both the interpretation *and* implementation of this
principle: it is the *composition* of a path $p : x \is y$ with a
*continuous* function $f : A \to B$.

```agda
ap : ∀ {a b} {A : Type a} {B : A → Type b}
   → (f : ∀ x → B x) {x y : A} (p : x ≡ y)
   → PathP (λ i → B (p i)) (f x) (f y)
ap f p i = f (p i)

{-# NOINLINE ap #-}
```

The type of the function above is perhaps a bit more general than
initially expected: we talk not about types $A, B$ and a function $f : A
\to B$, but instead about a type $A$, a type family $B(-)$ over $A$, and
a *dependent* function $(x : A) \to B(x)$. While the values $f(x)$ and
$f(y)$ live in different points of the family $B$, if we have a $p : x
\is y$, the types $B(x)$ and $B(y)$ are *themselves* identical.
Therefore, we can define the composition of a *dependent* function with
a path, producing a *dependent* path in the codomain.

We can also define a corresponding operation for *dependent* paths in
the domain, as long as we're given a *line* of functions.

```agda
apd : ∀ {a b} {A : I → Type a} {B : (i : I) → A i → Type b}
    → (f : ∀ i (a : A i) → B i a) {x : A i0} {y : A i1}
    → (p : PathP A x y)
    → PathP (λ i → B i (p i)) (f i0 x) (f i1 y)
apd f p i = f i (p i)
```

The type of `apd`{.Agda} is another doozy, but it makes a *bit* more
sense when we write out the lines as paths. It says that if we have
(dependently) identical dependent functions, and we apply them to
identical arguments, we get identical results. It's a natural principle,
apart from the ludicrous amount of quantification.

```agda
_
  : ∀ {a b} {A A' : Type a} {B : A → Type b} {B' : A' → Type b}
      {f : ∀ x → B x} {g : ∀ x → B' x} {x : A} {y : A'}
  → {pa : A ≡ A'} {pb : PathP (λ i → pa i → Type b) B B'}
  → (pf : PathP (λ i → ∀ x → pb i x) f g)
  → (px : PathP (λ i → pa i) x y)
  → PathP (λ i → pb i (px i)) (f x) (g y)
_ = λ pf px → apd (λ i → pf i) px
```

<!--
```agda
ap₂
  : ∀ {a b c} {A : Type a} {B : A → Type b} {C : (x : A) → B x → Type c}
      (f : (x : A) (y : B x) → C x y) {x y : A} {α : B x} {β : B y}
  → (p : x ≡ y) (q : PathP (λ i → B (p i)) α β)
  → PathP (λ i → C (p i) (q i)) (f x α) (f y β)
ap₂ f p q i = f (p i) (q i)
```
-->

Under the correspondence between homotopy theory and higher category
theory, we would say that `ap`{.Agda} expresses that functions are
*functors* from their domain to their codomain. Accordingly, we would
expect that `ap`{.Agda} preserves identities (i.e. $\refl$) and
commutes with taking inverses. Since paths are implemented as
functions, these preservation laws are *definitional*, instead of
needing proof. We'll revisit these functoriality laws later, when we
have defined composition.

<!--
```agda
private
```
-->

```agda
  ap-sym : {p : x ≡ y} → sym (ap f p) ≡ ap f (sym p)
  ap-sym = refl

  ap-refl : ap f (refl {x = x}) ≡ refl
  ap-refl = refl
```

The `ap`{.Agda} operation is also functorial in its *first* argument: it
preserves identity and composition of *functions*, too.

```agda
  ap-∘ : {p : x ≡ y} → ap (λ x → g (f x)) p ≡ ap g (ap f p)
  ap-∘ = refl

  ap-id : {p : x ≡ y} → ap (λ x → x) p ≡ p
  ap-id = refl
```

## Transport

We've established that every function preserves paths, but this is not
*quite* enough for a notion of sameness. The key principle that
characterises identity among the relations is **indiscernibility of
identicals**: at the logical level, this says that if $P(x)$ and $x =
y$, then also $P(y)$. In type theory, this is generalised: we're not
only talking about *predicates* $P(-)$, but rather *type families*
$P(-)$, which have values; and we do not simply have $x = y$, but rather
a specific *path* $p : a \is b$.

In Cubical Agda, the relevant *primitive* is the function
`transp`{.Agda}, whose type is a slight generalisation of the
`transport`{.Agda} operation below. We'll focus on `transport`{.Agda}
for now. To start with, this is where paths show their difference from
the notion of equality in set-level type theories: it says that we have
a function from paths $p : A \is B$ to functions $A \to B$. However,
it's *not* the case that every $p, q : A \is B$ gives back the *same*
function $A \to B$. Which function you get depends on (and determines) the
path you put in!

```agda
transport : ∀ {ℓ} {A B : Type ℓ} → A ≡ B → A → B
transport p = transp (λ i → p i) i0
```

As a concrete example, it can be shown that the type `Bool ≡ Bool` has
exactly two inhabitants ([see here]), which would be traditionally be
read as saying something like "the set of booleans is equal to itself in
two ways". As mentioned before, we reserve the terminology "$a$ and $b$
are equal" for when there is *at most one* $a \is b$; instead, the
situation with `Bool`{.Agda} should be read as "there are two
*identifications* of `Bool`{.Agda} with itself."

By composing our new `transport`{.Agda} with the `ap`{.Agda} from the
last section, we can derive the promised indiscernibility of identicals,
which we call `subst`{.Agda}. Here, we'll note that the function $P(x)
\to P(y)$ you get depends on both the path $p : a \is b$ *and* the type
family $P(-)$.

```agda
subst : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} (P : A → Type ℓ₂) {x y : A}
      → x ≡ y → P x → P y
subst P p x = transport (ap P p) x
```

<!--
```agda
subst₂ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : A → Type ℓ₂} (P : (x : A) → B x → Type ℓ₃) {a a' : A} {b : B a} {b' : B a'}
       → (p : a ≡ a') (q : PathP (λ i → B (p i)) b b') → P a b → P a' b'
subst₂ P p q x = transp (λ i → P (p i) (q i)) i0 x
```
-->

[see here]: Data.Bool.html#Bool-aut≡2

As we mentioned above, the primitive `transp`{.Agda} slightly
generalises the `transport`{.Agda} operation: we'll now see how this
generality is useful. In addition to letting us specify the line (read:
identification between types) to transport over, and the thing to
transport, it has an additional argument $\phi : \bI$. This is the first
instance of the interval naming **formulas**: rather than being an
*endpoint*, the argument $\phi$ specifies *where the path is constant*.
When an element $\phi : \bI$ is taken to be a *formula*, we interpret it
to be the proposition $\phi = \iO$.

The constancy of the path is a side-condition in the type of `transp`
that is enforced by the type checker, but which we do not (yet) have the
tools to express. However, the function it serves is simple: when $\phi
= \iO$ says the path is constant, transporting is definitionally the
identity:

```agda
_ : ∀ {ℓ} {A : Type ℓ} → transp (λ i → A) i1 ≡ id
_ = refl
```

To define the high-level `transport`{.Agda}, we had to set $\phi = \iZ$,
expressing that the path is *nowhere* constant. This constancy
information is simply not tracked in the type of paths, so it's our only
choice. However, we know that transporting along a reflexivity path
should be the identity. We can use the $\phi$ argument to prove this!

```agda
transport-refl
  : ∀ {ℓ} {A : Type ℓ} (x : A) → transport refl x ≡ x
transport-refl {A = A} x i = transp (λ i → A) i x
```

In the definition above, $\lam{i}{A}$ is always a constant function, so
the side-condition is satisfied. Therefore, we can compute the endpoints
of the path. When $i = \iZ$, we have exactly `transport refl x`; but
when $i = \iO$, the entire `transp`{.Agda} computes away, and we're left
with just $x$. In fact, the proof of `transport-refl`{.Agda} generalises
to a natural operation computing a dependent path: we call it the
*filler* of the transport, since it *fills* a line $\PathP{p}{x}{\transport{p}{x}}$.

```agda
transport-filler
  : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) (x : A)
  → PathP (λ i → p i) x (transport p x)
transport-filler p x i = transp (λ j → p (i ∧ j)) (~ i) x
```

This definition is well-formed because, when $\ineg i = \iO$ (i.e. $i =
\iZ$), the line is $\lam{j}{p\ (\iZ\imin j)} = \lam{j}{A}$, which is
constant. Moreover, its body computes to $\transp{\lam{j}{A}}{\iO}{x} =
x$ on $\iZ$ and to $\transp{p}{\iZ}{x} = \transport{p}{x}$ on the right,
so the endpoints are correct.

<details>
<summary>
We also have some special cases of `transport-filler`{.Agda} which are
very convenient when working with iterated transports.
</summary>

```agda
transport-filler-ext
  : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B)
  → PathP (λ i → A → p i) (λ x → x) (transport p)
transport-filler-ext p i x = transport-filler p x i

transport⁻-filler-ext
  : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B)
  → PathP (λ i → p i → A) (λ x → x) (transport (sym p))
transport⁻-filler-ext p i x = transp (λ j → p (i ∧ ~ j)) (~ i) x

transport⁻transport
  : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) (a : A)
  → transport (sym p) (transport p a) ≡ a
transport⁻transport p a i =
  transport⁻-filler-ext p (~ i) (transport-filler-ext p (~ i) a)
```
</details>

### Computation

In book HoTT, `transport`{.Agda} is defined using [[path induction]],
and it computes definitionally only when the path is `refl`{.Agda}. By
contrast, in cubical type theory, the `transp`{.Agda} primitive computes
in terms of the line of types. For the natural numbers, and other
inductive types without parameters, `transport`{.Agda} is always the
identity function. This is justified because a type like `Nat`{.Agda} is
completely insensitive to the interval:

```agda
_ : {x : Nat} → transport (λ i → Nat) x ≡ x
_ = refl

_ : {X : Type} → transport (λ i → Type) X ≡ X
_ = refl
```

For other type formers, the definition is a bit more involved. Let's
assume that we have two lines of types, `A` and `B`, to see how
transport reduces in types built out of `A` and `B`:

```agda
module _ {A0 A1 B0 B1 : Type} {A : A0 ≡ A1} {B : B0 ≡ B1} where private
```

<!--
```agda
  variable
    a a' : A i0
    b b' : B i0
```
-->

If we have $A(i)$ and $B(i)$, we can form the product type $A(i) \times
B(i)$. The transport operation, in this case, is componentwise. There
isn't much else we could do!

```agda
  _ : transport (λ i → A i × B i) (a , b) ≡ (transport A a , transport B b)
  _ = refl
```

For non-dependent functions, the situation is similarly intuitive, but
slightly more complicated. We want to produce an $A(\iO) \to B(\iO)$,
but the only way we have to get a $B(-)$ is by applying $f$. We first
transport $x : A(\iO)$ along $A\inv$ to get $\transport{A\inv}{x} :
A(\iZ)$, then apply $f$ to get something in $B(\iZ)$, and finally
transport along $B$ to get something in $B(\iO)$. Check it out:

```agda
  _ : {f : A i0 → B i0}
    → transport (λ i → A i → B i) f
    ≡ λ x → transport B (f (transport (sym A) x))
  _ = refl

module _ {A : I → Type} {B : (i : I) → A i → Type} where private
```

It's also illustrative to consider the case of a dependent function. We
start with a line of types $A(i)$ and a line of type *families* $B(i,-)$
over $A(i)$. If we have $f : (x : A(\iZ)) \to B(\iZ, x)$, how do we send
an $x : A(\iO)$ to something in $B(\iO, x)$?

As before, we can start by producing something in $A(\iZ)$ by
transporting $x$ backwards, and applying $f$. This gives us the values

$$
\begin{align*}
x_0 &= \transport{A\inv}{x}&&: A(\iZ) \\
y_0 &= f(x_0)              &&: B(\iZ, x_0)\text{.}
\end{align*}
$$

We're now faced with the conundrum of transporting $y_0$ along $B$. But
we can't take the line to be $\lam{i}{B(i,x_0)}$ since $x_0 : A(\iZ)$,
while the argument to $B(i,-)$ should be in $A(i)$! The solution is to
*generalise* $x_0$ to a line

$$
x_i = \transp{(\lam{j}{A\ (i \imax \ineg j)})}{i}{x} : A(i)
$$

so that we may form $\lam{i}{B(i,x_i)}$ connecting $B(\iZ, x_0)$ and
$B(\iO, x)$. While this construction seems to have come out of nowhere,
note that $x_i$ is the inverse of `transport-filler`{.Agda} along
$A\inv$! We can then obtain our return value by transporting $y_0$ along
this line.

```agda
  _ : {f : (x : A i0) → B i0 x} → transport (λ i → (x : A i) → B i x) f ≡
    λ (x : A i1) →
      let
        xi : ∀ i → A i
        xi i = transport-filler (λ i → A (~ i)) x (~ i)

        y0 = f (xi i0)
      in transport (λ i → B i (xi i)) y0
  _ = refl
```

The case for dependent sums (i.e. general `Σ`{.Agda} types) also
involves a filler, but no negations.

```agda
  _ : {x : A i0} {y : B i0 x} → transport (λ i → Σ (A i) (B i)) (x , y) ≡
    let
      xi : ∀ i → A i
      xi i = transp (λ j → A (j ∧ i)) (~ i) x
    in xi i1 , transport (λ i → B i (xi i)) y
  _ = refl
```

## Path induction {defines="path-induction contractibility-of-singletons"}

In Martin-Löf type theory, the identity type is not characterised by
indiscernibility of identicals (its *recursion* principle), but rather
by its *induction* principle, known simply as "J". Internalised, the J
rule has the following type:

```agda
J : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {x : A}
  → (P : (y : A) → x ≡ y → Type ℓ₂)
  → P x refl → ∀ {y} p → P y p
```

Seen one way, this is a generalised version of `subst`{.Agda}, where the
type family may also depend on the path --- to the syntactically-minded,
this is exactly the induction principle for identity *qua* inductive
family; it says that the total space of the identity family $\Sigma_{y :
A} (x \is y)$ is generated by the point $(x, \refl)$. This rule is not
purely syntactically motivated: it has a natural homotopical
interpretation, which leads to a nice *visual* explanation.

In this analogy, the total space $\Sigma_{y : A} (x \is y)$ is the space of
paths from $x$ *with an endpoint free*, the *free* endpoint being the
first coordinate of the pair. Elements in this type are allowed to have
whatever right endpoint, and we're allowed to identify paths
with different endpoints. The J rule says that every $(y, p)$ in this
type is identical to $(x, \refl)$. How can that be? If we think of paths
as *ropes* that can shrink, and of identifications between them as
deformations over time, then this rule states that, as long as one
endpoint is *free*, we're allowed to *coil in* the rope, reducing its
length until it is trivial. In this analogy, we can see why one endpoint
has to be free: if it weren't, our path might get snagged on something!

This identification comes up very often when working in homotopy type
theory, so it has its own name: **contractibility of singletons**. A
type of singletons is something like $\Sigma_{y : A} (x \is y)$: the
type of elements of $A$ which are identical to $y$. Read
set-theoretically, it makes sense that this would only have one
inhabitant!

```agda
Singleton : ∀ {ℓ} {A : Type ℓ} → A → Type _
Singleton x = Σ[ y ∈ _ ] x ≡ y
```

We're given an inhabitant $y : A$ and a path $p : x \is y$. To identify
$(x, \refl) \is (y, p)$, we have to produce an identification $x \is y$
(we can use $p$), and, over this, an identification of $\refl$ and $p$.

```agda
Singleton-is-contr : ∀ {ℓ} {A : Type ℓ} {x : A} (y : Singleton x)
                   → Path (Singleton x) (x , refl) y
Singleton-is-contr {x = x} (y , p) =
```

Writing out the dependency explicitly, we see that the second component
should inhabit the dependent path type $$\PathP{(\lam{i}{x \is
p(i)})}{\refl}{p}$$, which we've already seen: not only can it be
expressed as a `Square`, but it is precisely the type of the
[[connection]] square $p(i \imin j)$:

```agda
  let
    q : Square refl refl p p
    q = λ i j → p (i ∧ j)
  in λ i → p i , q i
```

We then obtain the definition of J: If we have $\rm{prefl} : P(x,
\refl)$ but we want $P(y, p)$, we can first identify $(x, \refl) \is (y,
p)$, then transport our assumption over that.

```agda
J {x = x} P prefl {y} p =
  let
    pull : (x , refl) ≡ (y , p)
    pull = Singleton-is-contr (y , p)
  in subst₂ P (ap fst pull) (ap snd pull) prefl
```

This eliminator _doesn't_ definitionally compute to `prefl` when `p` is
`refl`, again since `transport (λ i → A)` isn't definitionally the
identity. However, since it _is_ a transport, we can use the
`transport-filler`{.Agda} to get a *path* expressing the computation
rule.

```agda
J-refl : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {x : A}
           (P : (y : A) → x ≡ y → Type ℓ₂)
       → (pxr : P x refl)
       → J P pxr refl ≡ pxr
J-refl {x = x} P prefl i = transport-filler (λ i → P _ (λ j → x)) prefl (~ i)
```

<!--
```agda
inspect : ∀ {a} {A : Type a} (x : A) → Singleton x
inspect x = x , refl
```
-->

# Composition

In "Book HoTT", the primitive operation from which the
higher-dimensional structure of types is derived is the `J`{.Agda}
eliminator, with `J-refl`{.Agda} as a _definitional_ computation rule.
This has the benefit of being very elegant: This one elimination rule
generates an infinite amount of coherent data. However, it's very hard
to make this rule work in the presence of higher inductive types and
univalence, so much so that, in the book, univalence and HITs only
compute up to paths.

In Cubical Agda, we trade off the computation rule `J-refl`{.Agda} for a
smooth implementation of these higher-dimensional principles. The result
is, undeniably, a more complicated type theory: we now have to explain
how to reduce `transp`{.Agda} in arbitrary lines of types. We've made
some progress, considering things like universes, inductive data types,
dependent products, and dependent sums. However, we have not yet
explained how to compute `transp`{.Agda} in path types, much less in
`PathP`{.Agda}. To have a functioning type theory, we'll need
computation rules to handle these; but for that, we first need to
introduce the higher-dimensional generalisation of path types: **partial
elements** and **extensibility**.

## Partial elements {defines="partial-cube"}

In [our discussion of the interval](#paths-and-the-interval), we became
acquainted with the idea that a value $e : A$ in a context with $n$
interval variables can be pictured as an $n$-cube drawn on the type $A$.
We're also familiar with the idea that we can place *constraints* on the
values that these cubes take at certain points along the interval: this
is what `PathP`{.Agda} specifies. A value $p : \PathP{A}{x}{y}$ is a
line $\lam{i}{p(i)}$ in $A$, which is $x$ when $i = \iZ$ and $y$ when $i
= \iO$.

But what if we want to specify constraints on a cube in higher
dimensions? We could iterate `PathP`{.Agda} types, as done in the
definition of `Square`{.Agda}, but that forces us to specify values at
*every* endpoint. What if we only particularly care about the value at
*one* of the endpoints, or some more complicated sub-shape of an
$n$-cube? Enter the `Partial`{.Agda} type former.

When $A$ is a type and $\phi : \bI$ is some interval expression, we can
form the type $\Partial{\phi}{A}$ of **partial elements** of $A$ with
**extent** $\phi$: an element of $A$, but which is only defined when
$\phi = \iO$. You can think of a partial element as a function: if you
have $p : \Partial{\phi}{A}$, and you can come up with some evidence $v$
that $\phi = \iO$, then $p(v) : A$. Conversely, if you *have* some $x :
A$, you can pretend it is a partial element by *ignoring* the evidence.
In Agda, we write `IsOne`{.Agda} for the type of such evidence, and we
write `1=1`{.Agda} for the proof that $\iO = \iO$.

The key feature of partial elements is that we can introduce them by
giving **systems**: If you want to define an $f : \Partial{(\phi \imax
\psi)}{A}$, it suffices to give $x : \Partial{\phi}{A}$ and $y :
\Partial{\psi}{A}$, *as long as they agree when $(\phi = \iO) \land
(\psi = \iO)$.*

For instance, if we have a dimension $i : \bI$, then the type
$\Partial{(i \imax \ineg i)}{A}$ represents the *endpoints* of a line in
$A$. We do not have a *complete* line, just the endpoints! As an
example, we can define a value of `Bool`{.Agda} which is `true`{.Agda}
on the left endpoint of the interval, and `false`{.Agda} on the right
endpoint.

```agda
private
  not-a-path : (i : I) → Partial (~ i ∨ i) Bool
  not-a-path i (i = i0) = true
  not-a-path i (i = i1) = false
```

Graphically, our `not-a-path`{.Agda} is represented by the following
rather boring shape: two disconnected points, with completely unrelated
values at each endpoint of the interval.

~~~{.quiver}
\[\begin{tikzcd}
  {\rm{true}} && {\rm{false}}
\end{tikzcd}\]
~~~

As a further example, we could imagine piecing together *three* paths
into a partial element that is defined on three faces, resulting in
something like an upside-down drinking glass. Note that each of the
faces in the system below only constrains *one* of the dimensions, as
written between parentheses on the left-hand-side. This means the
right-hand-side can, and does, still vary along the *other* dimension.
This is in contrast to our `not-a-path`{.Agda} example above, in which
the *only* dimension is constrained, so there can be no variation.

```agda
module _ {A : Type} {w x y z : A} {p : w ≡ x} {q : x ≡ y} {r : y ≡ z} where private
  shape : (i j : I) → Partial (~ i ∨ i ∨ ~ j) A
  shape i j (i = i0) = p (~ j)
  shape i j (i = i1) = r j
  shape i j (j = i0) = q i
```

::: mathpar
~~~{.quiver}
\indicatortwod{i}{j}
~~~

~~~{.quiver}
\[\begin{tikzcd}
  x && y \\
  \\
  w && z
  \arrow["{p(\ineg j)}"', from=1-1, to=3-1]
  \arrow["q(i)", from=1-1, to=1-3]
  \arrow["r(j)", from=1-3, to=3-3]
\end{tikzcd}\]
~~~
:::

Note that this element is valid *only because* we laid out the paths
with their common vertices are aligned. This is the side condition we
have to fulfill when defining a system: on common edges, the faces of
the partial element *must* agree.

## Extensibility {defines="extensibility extension-type"}

The next type former we'll introduce lets us turn a partial element into
a *constraint*. Much like the `Path`{.Agda} type constrains its
inhabitants to have matching endpoints definitionally, the **extension
types** let us carve out the subtype of $A$ which *definitionally* agree
with a given partial element. If we have a $p : \Partial{\phi}{A}$, then
we can form the type $\Extn{A}{\phi \mapsto p}$.

The introduction rule, internalized as the constructor `inS`{.Agda},
says that, if we have a totally-defined element $e : A$ which satisfies
$\phi \vdash e = p$ (i.e. which agrees with $p$ wherever it is defined),
then we can form $\inS{e} : \Extn{A}{\phi \mapsto p}$. The elimination
rule says that, if $e : \Extn{A}{\phi \mapsto p}$, then we can obtain an
element $\outS{e} : A$; and moreover, $\phi \vdash \outS{e} = p$.

With the type theory aside, let's get to examples. Suppose we have a
partial element of `Bool`{.Agda} which is `true`{.Agda} on the left
endpoint of the interval, and undefined elsewhere. This is a partial
element with one interval variable, so it would be extended by a _path_
--- a 1-dimensional cube. The reflexivity path is a line in `Bool`,
which is `true`{.Agda} on the left endpoint of the interval (in fact, it
is `true`{.Agda} everywhere), so we say that `refl`{.Agda} _extends_ this
partial element.

~~~{.quiver}
\[\begin{tikzcd}
  \textcolor{rgb,255:red,214;green,92;blue,92}{\rm{true}} && {\rm{true}}
  \arrow["{\refl}", from=1-1, to=1-3]
\end{tikzcd}\]
~~~

Diagramatically, we'll depict extensions by drawing the relevant partial
element in red, and the total element in black. In Agda, we write
extension types using the type former `_[_↦_]`{.Agda}, which is written
mixfix as `A [ φ ↦ p ]`. We can formalise the red-black extensibility
diagram above by defining the partial element `left-true`{.Agda}, and
giving `refl`{.Agda} to `inS`{.Agda}, the constructor for
`_[_↦_]`{.Agda}.

```agda
private
  left-true : (i : I) → Partial (~ i) Bool
  left-true i (i = i0) = true

  refl-extends : (i : I) → Bool [ (~ i) ↦ left-true i ]
  refl-extends i = inS (refl {x = true} i)
```

Slightly more preicsely, the constructor `inS` expresses that _any_
totally-defined cube $u$ can be seen as a partial cube, which simply
agrees with $u$ for any choice of formula $\phi$. To introduce elements
of *specific* extensions, we use the fact that partial elements are
definitionally equal as long as they are definitionally equal on their
intersections. This might be a bit abstract, so let's diagram the case
where we have some square $a$, and the partial element has formula $i
\lor j$. This extension can be drawn as in the diagram below: The red
wedge shape is the partial element, which is "extended by" the black
lines to make a complete square.

~~~{.quiver}
\[\begin{tikzcd}
  {a_{\iZ, \iZ}} && \textcolor{rgb,255:red,214;green,92;blue,92}{a_{\iO, \iZ}} \\
  & {a_{i, j}} \\
  \textcolor{rgb,255:red,214;green,92;blue,92}{a_{\iZ, \iO}} && \textcolor{rgb,255:red,214;green,92;blue,92}{a_{\iO, \iO}}
  \arrow["{a_{i, \iZ}}", from=1-1, to=1-3]
  \arrow["{a_{\iO, j}}", color={rgb,255:red,214;green,92;blue,92}, from=1-3, to=3-3]
  \arrow["{a_{\iZ, j}}"', from=1-1, to=3-1]
  \arrow["{a_{i, \iO}}"', color={rgb,255:red,214;green,92;blue,92}, from=3-1, to=3-3]
\end{tikzcd}\]
~~~

```agda
  _ : ∀ {ℓ} {A : Type ℓ} {φ : I} (u : A) → A [ φ ↦ (λ _ → u) ]
  _ = inS
```

Note that since an extension must agree with the partial element
_everywhere_, there are many partial elements that can not be extended
at all. Take `not-a-path`{.Agda} from before --- since there is no line
that is `true`{.Agda} at `i0`{.Agda} and `false`{.Agda} at `i1`{.Agda},
this element is not extensible. If it *were* extensible, we would have
`true ≡ false` --- a contradiction.[^truenotfalse]

[^truenotfalse]: Although it is not proven to be a contradiction in
_this_ module, see [Data.Bool](Data.Bool.html) for that construction.

```agda
  not-extensible
    : ((i : I) → Bool [ (~ i ∨ i) ↦ not-a-path i ])
    → true ≡ false
  not-extensible ext i = outS (ext i)
```

This counterexample demonstrates the eliminator for `_[_↦_]`{.Agda},
`outS`{.Agda}, which we have already mentioned. However, we can also
demonstrate its *computation* rule. In the code below, even though `x`
is abstract, we know that `outS` agrees with the partial element `u`.

```agda
  _ : ∀ {A : Type} {u : Partial i1 A} {x : A [ i1 ↦ u ]}
    → outS x ≡ u 1=1
  _ = refl
```

## Box filling {defines="hcomp fibrant fibrancy homogeneous-composition"}

Using the notions of partial elements and extensibility, we can define a
higher-dimensional generalisation of the notion of binary path
composition: the **homogeneous composition** operation, `hcomp`{.Agda}.
This is one of the fundamental tools for working with higher-dimensional
types in cubical type theory: it lets us reduce many problems of path
algebra to formulating partial elements expressing their solutions.

Since this is the second hardest construction to grok in cubical type
theory, we'll start with a very concrete example. Recall the partial
element we drew by gluing three paths together, and its formalisation:

::: mathpar
~~~{.quiver}
\indicatortwod{i}{j}
~~~

~~~{.quiver}
\[\begin{tikzcd}
  x && y \\
  \\
  w && z
  \arrow["{p(\ineg j)}"', from=1-1, to=3-1]
  \arrow["q(i)", from=1-1, to=1-3]
  \arrow["r(j)", from=1-3, to=3-3]
\end{tikzcd}\]
~~~
:::

```agda
module _ {A : Type} {w x y z : A} {p : w ≡ x} {q : x ≡ y} {r : y ≡ z} where private
  shape : (i j : I) → Partial (~ j ∨ i ∨ ~ i) A
  shape i j (i = i0) = p (~ j)
  shape i j (i = i1) = r j
  shape i j (j = i0) = q i
```

If we consider this open square as a sequence of three paths to follow,
then our intuition that types are spaces (or groupoids) says that there
should be a *fourth* path, the composite, whose "effect" is to follow
each of the paths in turn. We don't yet know how to compute such a path,
but it should very well exist! This is one of the many things that
`hcomp`{.Agda} can do for us:

```agda
  composite : w ≡ z
  composite i = hcomp (i ∨ ~ i) (shape i)
```

In this situation, we picture `hcomp`{.Agda} as filling the face
opposite $j = \iZ$.

~~~{.quiver}
\[\begin{tikzcd}
	x && y \\
	\\
	w && z
	\arrow["{q(i)}", from=1-1, to=1-3]
	\arrow["{{p(\ineg j)}}"', from=1-1, to=3-1]
	\arrow["{r(j)}", from=1-3, to=3-3]
	\arrow["{\operatorname{hcomp} \dots}"', dashed, from=3-1, to=3-3]
\end{tikzcd}\]
~~~

In general, `hcomp`{.Agda} allows us to build an $n$-dimensional cube,
with a boundary of our choice, by expressing it as the missing face in
some $(n+1)$-dimensional shape. Its actual interface says that, if we
have some shape $\phi : I$, and a partial element

$$
i : \bI \vdash e : \Partial{(\ineg i \imax \phi)}{A}
$$,

then we can obtain an extension $\Extn{A}{\phi \mapsto e(\iO)}$. The
idea of the extra $i$ dimension is that we're forced to give a
*connected* shape: $i$ is disjoint from any of the variables in $\phi$,
so we have to give at least *something* (the value $e(\iZ)$). This means
that we can't use `hcomp`{.Agda} to produce an extension of our
`not-a-path`{.Agda} system, for example, since it would be impossible to
make it connected in the first place!

Note that `hcomp`{.Agda} gives us the missing $(n-1)$-dimensional face
of the open $n$-box, but the semantics guarantees the existence of the
$n$-box *itself*. Using the De Morgan structure on the interval, we can
*define* this "filling" operation in terms of composition: we express
the *entire* original shape as the "missing face" of an
$(n+1)$-dimensional problem.

```agda
hfill : ∀ {ℓ} {A : Type ℓ} (φ : I) → I
      → ((i : I) → Partial (φ ∨ ~ i) A)
      → A
hfill φ i u = hcomp (φ ∨ ~ i) λ where
  j (φ = i1) → u (i ∧ j) 1=1
  j (i = i0) → u i0 1=1
  j (j = i0) → u i0 1=1
```

:::{.note}
While every inhabitant of `Type`{.Agda} has a composition operation, not
every _type_ (something that can be on the right of a type signature `e
: T`) does. We call the types that _do_ have a composition operation
“fibrant”, since these are semantically the cubical sets which are Kan
complices. Examples of types which are _not_ fibrant include the
interval `I`{.Agda}, the partial elements `Partial`{.Agda}, and the
extensions `_[_↦_]`.
:::

Agda also provides a _heterogeneous_ version of composition (which we
sometimes call "CCHM composition"), called `comp`{.Agda}. It too has a
corresponding filling operation, called `fill`{.Agda}. The idea behind
CCHM composition is --- by analogy with `hcomp`{.Agda} expressing that
"paths preserve extensibility" --- that `PathP`{.Agda}s preserve
extensibility. Thus we have:

```agda
fill : ∀ {ℓ : I → Level} (A : ∀ i → Type (ℓ i)) (φ : I) (i : I)
     → (u : ∀ i → Partial (φ ∨ ~ i) (A i))
     → A i
fill A φ i u = comp (λ j → A (i ∧ j)) (φ ∨ ~ i) λ where
  j (φ = i1) → u (i ∧ j) 1=1
  j (i = i0) → u i0 1=1
  j (j = i0) → u i0 1=1
```

Given the inputs to a composition --- a family of partial paths `u` and
a base `u0` --- `hfill`{.Agda} connects the input of the composition
(`u0`) and the output. The cubical shape of iterated identifications
causes a slight oddity: The only unbiased definition of path composition
we can give is _double composition_, which corresponds to the missing
face for the [square] at the start of this section.

[square]: 1Lab.Path.html#composition

```agda
_··_··_ : ∀ {ℓ} {A : Type ℓ} {w x y z : A}
        → w ≡ x → x ≡ y → y ≡ z
        → w ≡ z
(p ·· q ·· r) i = hcomp (∂ i) λ where
  j (i = i0) → p (~ j)
  j (i = i1) → r j
  j (j = i0) → q i
```

Since it will be useful later, we also give an explicit name for the
*filler* of the double composition square. Since `Square`{.Agda}
expresses an equation between paths, we can read the type of
`··-filler`{.Agda} as saying that $p\inv \cdot (p \dcomp q \dcomp r) = q
\cdot r$.

```agda
··-filler : ∀ {ℓ} {A : Type ℓ} {w x y z : A}
          → (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
          → Square (sym p) q (p ·· q ·· r) r
··-filler p q r i j = hfill (∂ j) i λ where
  k (j = i0) → p (~ k)
  k (j = i1) → r k
  k (k = i0) → q j
```

We can define the ordinary, single composition by taking `p = refl`, as
is done below. Any of paths would have led to the same definition, but
for definiteness we choose `p`. Note that we can also define a filler
for the single composition, whose type we read as saying that $\refl
\cdot (p \cdot q) = p \cdot q$.

::: mathpar

~~~{.quiver}
\indicatortwod{i}{j}
~~~

~~~{.quiver}
\[\begin{tikzcd}
  x && y \\
  & {\bullet\text{-filler}~ p~ q}      \\
  x && z
  \arrow["{\refl}", from=1-1, to=1-3]
  \arrow["{p}"', from=1-1, to=3-1]
  \arrow["{p \bullet q}", dashed, from=1-3, to=3-3]
  \arrow["{q}"', from=3-1, to=3-3]
\end{tikzcd}\]
~~~

:::

```agda
_∙_
  : ∀ {ℓ} {A : Type ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
p ∙ q = refl ·· p ·· q

∙-filler
  : ∀ {ℓ} {A : Type ℓ} {x y z : A}
  → (p : x ≡ y) (q : y ≡ z) → Square refl p (p ∙ q) q
∙-filler {x = x} {y} {z} p q = ··-filler refl p q

infixr 30 _∙_
```

We'll leave this section with a composition operation that works for
*dependent* paths. This is a nice combination of fillers and CCHM
composition: it takes proofs that $x \is y$ over $p$ and $y \is z$ over
$q$, and produces a path witnessing that $x \is z$ over $p \cdot q$. The
definition is exactly analogous to that of single composition, but with
extreme amounts of extra quantification.

```agda
_∙P_ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
         {x y z : A} {x' : B x} {y' : B y} {z' : B z}
         {p : x ≡ y} {q : y ≡ z}
     → PathP (λ i → B (p i)) x' y'
     → PathP (λ i → B (q i)) y' z'
     → PathP (λ i → B ((p ∙ q) i)) x' z'
_∙P_ {B = B} {x' = x'} {p = p} {q = q} p' q' i =
  comp (λ j → B (∙-filler p q j i)) (∂ i) λ where
    j (i = i0) → x'
    j (i = i1) → q' j
    j (j = i0) → p' i
```

<!--
```agda
∙-filler' : ∀ {ℓ} {A : Type ℓ} {x y z : A}
          → (p : x ≡ y) (q : y ≡ z)
          → Square (sym p) q (p ∙ q) refl
∙-filler' {x = x} {y} {z} p q j i =
  hcomp (∂ i ∨ ~ j) λ where
    k (i = i0) → p (~ j)
    k (i = i1) → q k
    k (j = i0) → q (i ∧ k)
    k (k = i0) → p (i ∨ ~ j)

_∙₂_ : ∀ {ℓ} {A : Type ℓ} {a00 a01 a02 a10 a11 a12 : A}
       {p : a00 ≡ a01} {p' : a01 ≡ a02}
       {q : a00 ≡ a10} {s : a01 ≡ a11} {t : a02 ≡ a12}
       {r : a10 ≡ a11} {r' : a11 ≡ a12}
     → Square p q s r
     → Square p' s t r'
     → Square (p ∙ p') q t (r ∙ r')
(α ∙₂ β) i j = ((λ i → α i j) ∙ (λ i → β i j)) i

infixr 30 _∙P_ _∙₂_
```
-->

## The need for hcomp

At the start of this section, our goal was to explain how to compute
`transp`{.Agda} in a line of *paths* (or `PathP`{.Agda}s). Towards this,
we introduced the higher-dimensional composition operation,
`hcomp`{.Agda}, and we've shown that it can be used to recover ordinary
path composition --- but we have not explained how that connects to
reduction of `transp`{.Agda} in path types. Let us do so now. Readers
familiar with MLTT will know that composition of paths can be defined in
terms of path induction, or, more clearly, `transport`{.Agda}:

```agda
_∙'_ : {x y z : A} (p : x ≡ y) (q : y ≡ z) → x ≡ z
_∙'_ {x = x} p q = transport (λ i → x ≡ q i) p
```

Since we know that `transport`{.Agda} reduces when applied to type
formers, the definition above is *not* neutral, even when $p$ and $q$
are variables. But what does it reduce *to*? A natural attempt would be
to say that, at a point $i : \bI$, the path $\transport{(\lam{i}. x \is
q(i))}{p}$ is $t = \transport{(\lam{i}. A)}{p(i)}$ --- i.e., transport
of paths is, pointwise, transport along the base. But this can't be the
case, since $t$ has endpoints

~~~{.quiver}
\[\begin{tikzcd}[ampersand replacement=\&]
  {\transport{(\lam{i}{A})}{x}} \&\& {\transport{(\lam{i}{A})}{y}}
	\arrow["t", from=1-1, to=1-3]
\end{tikzcd}\]
~~~

which are *both* wrong! More saliently, this attempt makes no use of the
path $q$ at all, so there's no way it can be right. However, the
endpoints are *propositionally* correct. What we need is a way to
correct the endpoints after transporting the base, using an arbitrary
path. But this is exactly what `hcomp`{.Agda} lets us do! The *real*
normal form of our transport is the dashed path in the diagram below,
where we abbreviate $\transp{(\lam{i}{A})}{\phi}{x}$ as
$\rm{tr}~{\phi}~{x}$:

~~~{.quiver}
\[\begin{tikzcd}[ampersand replacement=\&]
	{\rm{tr}~\iZ~x} \&\&\&\& {\rm{tr}~\iZ~y} \\
	\\
	x \&\&\&\& z
	\arrow["{{\rm{tr}~\iZ~p(i)}}", from=1-1, to=1-5]
	\arrow["{{\rm{tr}~j~x}}"', from=1-1, to=3-1]
	\arrow["{{\rm{tr}~j~q(j)}}", from=1-5, to=3-5]
	\arrow["{{\transport{(\lam{i}{x \is q(i)})}{p(i)}}}"', dashed, from=3-1, to=3-5]
\end{tikzcd}\]
~~~

We can ask Agda to verify this, by writing out the diagram as an `hcomp`{.Agda}:

```agda
_ : {x y z : A} {p : x ≡ y} {q : y ≡ z} →
  let
    tr : (φ : I) (a : A) → A
    tr φ a = transp (λ i → A) φ a

    the-hcomp : x ≡ z
    the-hcomp i = hcomp (∂ i) λ where
      j (j = i0) → tr i0 (p i)
      j (i = i0) → tr j x
      j (i = i1) → tr j (q j)
  in (p ∙' q) ≡ the-hcomp
_ = refl
```

More generally, we can demonstrate the computation rule in an arbitrary
`PathP`{.Agda}. It's a straightforward generalisation of the
construction above: We have a *square* of types $A(i,j)$, and lines of
endpoints $x(i) : A(i,\iZ)$ and $y(i) : A(i, \iO)$. Writing

$$
C(j) = \PathP{(\lam{i}{A(j,i)})}{x(j)}{y(j)}\text{,}
$$

we can ask Agda to check that transporting a $p : C(\iZ)$ to something
in $C(\iO)$ is done by computing the composition below:

<!--
```agda
private module _ {A : I → I → Type} {x : ∀ i → A i i0} {y : ∀ i → A i i1} where private
```
-->

```agda
  C : I → Type
  C j = PathP (λ i → A j i) (x j) (y j)

  the-hcomp : C i0 → C i1
  the-hcomp p i = hcomp (∂ i) λ where
    j (j = i0) → transp (λ j → A j i) i0 (p i)
    j (i = i0) → transp (λ i → A (j ∨ i) i0) j (x j)
    j (i = i1) → transp (λ i → A (j ∨ i) i1) j (y j)

  _ : {p : C i0} → transp C i0 p ≡ the-hcomp p
  _ = refl
```

## Uniqueness of compositions

Since we're defining composition of paths as the missing face in a
particular square, we have to wonder: can paths have *multiple*
composites, i.e. multiple faces that fit into the same square? The
answer, fortunately, is no: we can show that any triple of paths has a
*unique* double composite, by drawing a *cube* whose missing face is a
*square* whose boundary includes the two *lines* we're comparing.

```agda
··-unique
  : ∀ {ℓ} {A : Type ℓ} {w x y z : A}
  → (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
  → (α β : Σ[ s ∈ (w ≡ z) ] Square (sym p) q s r)
  → α ≡ β
```

Note that the type of `α` and `β` asks for a path `w ≡ z` which
_specifically_ completes the open box for double composition. We would
not in general expect that `w ≡ z` is contractible for an arbitrary `a`!
Note that the proof of this involves filling a cube in a context that
*already* has an interval variable in scope - a hypercube!

```agda
··-unique {w = w} {x} {y} {z} p q r (α , α-fill) (β , β-fill) =
  λ i → (λ j → square i j) , (λ j k → cube i j k)
  where
    cube : (i j : I) → p (~ j) ≡ r j
    cube i j k = hfill (∂ i ∨ ∂ k) j λ where
      l (i = i0) → α-fill l k
      l (i = i1) → β-fill l k
      l (k = i0) → p (~ l)
      l (k = i1) → r l
      l (l = i0) → q k

    square : α ≡ β
    square i j = cube i i1 j
```

The term `cube` above has the following cube as a boundary. Since it is
a filler, there is a missing face at the bottom which has no name, so we
denote it by `hcomp...` in the diagram.

~~~{.quiver}
\[\begin{tikzcd}
  \textcolor{rgb,255:red,153;green,92;blue,214}{x} &&&& \textcolor{rgb,255:red,153;green,92;blue,214}{x} \\
  & \textcolor{rgb,255:red,214;green,92;blue,92}{y} && \textcolor{rgb,255:red,214;green,92;blue,92}{y} \\
  \\
  & \textcolor{rgb,255:red,214;green,92;blue,92}{z} && \textcolor{rgb,255:red,214;green,92;blue,92}{z} & {} \\
  \textcolor{rgb,255:red,153;green,92;blue,214}{w} &&&& \textcolor{rgb,255:red,153;green,92;blue,214}{w}
  \arrow[""{name=0, anchor=center, inner sep=0}, color={rgb,255:red,214;green,92;blue,92}, from=4-2, to=4-4]
  \arrow[""{name=1, anchor=center, inner sep=0}, color={rgb,255:red,214;green,92;blue,92}, from=2-4, to=4-4]
  \arrow[""{name=2, anchor=center, inner sep=0}, color={rgb,255:red,214;green,92;blue,92}, from=2-2, to=2-4]
  \arrow[""{name=3, anchor=center, inner sep=0}, color={rgb,255:red,214;green,92;blue,92}, from=2-2, to=4-2]
  \arrow[""{name=4, anchor=center, inner sep=0}, color={rgb,255:red,153;green,92;blue,214}, from=1-5, to=5-5]
  \arrow[""{name=5, anchor=center, inner sep=0}, color={rgb,255:red,153;green,92;blue,214}, from=1-1, to=5-1]
  \arrow[""{name=6, anchor=center, inner sep=0}, color={rgb,255:red,153;green,92;blue,214}, from=5-1, to=5-5]
  \arrow[""{name=7, anchor=center, inner sep=0}, color={rgb,255:red,153;green,92;blue,214}, from=1-1, to=1-5]
  \arrow[from=1-5, to=2-4]
  \arrow[from=1-1, to=2-2]
  \arrow["{\alpha\ k}"', from=5-1, to=4-2]
  \arrow["{\beta\ k}", from=5-5, to=4-4]
  \arrow["{\alpha\text{-filler}\ j\ k}"{description}, shorten >=6pt, Rightarrow, from=5, to=3]
  \arrow["{\beta\text{-filler}\ j\ k}"{description}, Rightarrow, draw=none, from=4, to=1]
  \arrow[""{name=8, anchor=center, inner sep=0}, "{\rm{hcomp}\dots}"{description}, Rightarrow, draw=none, from=6, to=0]
  \arrow["{r\ j}"{description}, color={rgb,255:red,214;green,92;blue,92}, Rightarrow, draw=none, from=0, to=2]
  \arrow["{q\ k}"{description}, Rightarrow, draw=none, from=2, to=7]
  \arrow["{p\ \neg j}"{description}, shift left=2, color={rgb,255:red,153;green,92;blue,214}, Rightarrow, draw=none, from=8, to=7]
\end{tikzcd}\]
~~~

This diagram is quite busy because it is a 3D commutative diagram, but
it could be busier: all of the unimportant edges were not annotated. By
the way, the lavender face (including the lavender $p\ \neg j$) is the
$k = \rm{i0}$ face, and the red face is the $k = \rm{i1}$ face.

However, even though the diagram is very busy, most of the detail it
contains can be ignored. Reading it in the left-right direction, it
expresses an identification between `α-filler j k` and `β-filler j k`,
lying over a homotopy `α = β`. That homotopy is what you get when you
read the bottom square of the diagram in the left-right direction.
Explicitly, here is that bottom square:

~~~{.quiver}
\[\begin{tikzcd}
  \textcolor{rgb,255:red,214;green,92;blue,92}{z} && \textcolor{rgb,255:red,214;green,92;blue,92}{z} \\
  \\
  \textcolor{rgb,255:red,153;green,92;blue,214}{w} && \textcolor{rgb,255:red,153;green,92;blue,214}{w}
  \arrow["\alpha", from=3-1, to=1-1]
  \arrow["\beta"', from=3-3, to=1-3]
  \arrow[""{name=0, anchor=center, inner sep=0}, "w", color={rgb,255:red,153;green,92;blue,214}, from=3-1, to=3-3]
  \arrow[""{name=1, anchor=center, inner sep=0}, "z"', color={rgb,255:red,214;green,92;blue,92}, from=1-1, to=1-3]
  \arrow["{\rm{hcomp}\dots}"{description}, Rightarrow, draw=none, from=0, to=1]
\end{tikzcd}\]
~~~

Note that, exceptionally, this diagram is drawn with the left/right
edges going up rather than down. This is to match the direction of the
3D diagram above. The colours are also matching.

Readers who are already familiar with the notion of h-level will have
noticed that the proof `··-unique`{.Agda} expresses that the type of
double composites `p ·· q ·· r` is a _proposition_, not that it is
contractible. However, since it is inhabited (by `_··_··_`{.Agda} and
its filler), it is contractible:

```agda
··-contract : ∀ {ℓ} {A : Type ℓ} {w x y z : A}
            → (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
            → (β : Σ[ s ∈ (w ≡ z) ] Square (sym p) q s r)
            → (p ·· q ·· r , ··-filler p q r) ≡ β
··-contract p q r β = ··-unique p q r _ β
```

<!--
```agda
∙-unique
  : ∀ {ℓ} {A : Type ℓ} {x y z : A} {p : x ≡ y} {q : y ≡ z}
  → (r : x ≡ z)
  → Square refl p r q
  → r ≡ p ∙ q
∙-unique {p = p} {q} r square i =
  ··-unique refl p q (_ , square) (_ , (∙-filler p q)) i .fst

··-unique' : ∀ {ℓ} {A : Type ℓ} {w x y z : A}
           → {p : w ≡ x} {q : x ≡ y} {r : y ≡ z} {s : w ≡ z}
           → (β : Square (sym p) q s r)
           → s ≡ p ·· q ·· r
··-unique' β i = ··-contract _ _ _ (_ , β) (~ i) .fst
```
-->

Finally, we note that the uniqueness results from this section let us
prove that path composition as defined directly through `hcomp`{.Agda}
agrees with path composition as defined through transport. The key
observation is that the `transport-filler`{.Agda} along $\lam{i}{x \is
q(i)}$ is *precisely* the square analogous to `∙-filler`{.Agda}:

```agda
_ : (x : A) {y z : A} (p : x ≡ y) (q : y ≡ z) → p ∙' q ≡ p ∙ q
_ = λ x p q →
  let
    filler : Square refl p (p ∙' q) q
    filler = transport-filler (λ i → x ≡ q i) p
  in ∙-unique (p ∙' q) filler
```

### Functoriality of ap

This is a very short section: when we [introduced
`ap`](#paths-as-sameness), we promised to show that it also preserves
path composition, to complete the requirements of functoriality. Using
the uniqueness result from the previous section, this becomes mostly
straightforward. First, we introduce the operation `ap-square`{.Agda},
which, as the name implies, shows that every function preserves squares:

```agda
ap-square
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {a00 a01 a10 a11 : A}
      {p : a00 ≡ a01} {q : a00 ≡ a10} {s : a01 ≡ a11} {r : a10 ≡ a11}
  → (f : (a : A) → B a)
  → (α : Square p q s r)
  → SquareP (λ i j → B (α i j)) (ap f p) (ap f q) (ap f s) (ap f r)
ap-square f α i j = f (α i j)
```

Despite the nightmare type (to allow `f` to be a dependent function),
the definition is just as straightforward as that of `ap`{.Agda}. Using
this with `··filler`{.Agda}, we get a square with boundary

~~~{.quiver}
\[\begin{tikzcd}[ampersand replacement=\&]
  fy \&\& \textcolor{rgb,255:red,214;green,92;blue,92}{fx} \\
  \\
  fz \&\& \textcolor{rgb,255:red,214;green,92;blue,92}{fw}
  \arrow["{\ap{f}{p\inv}}", from=1-1, to=1-3]
  \arrow["{\ap{f}{q}}"', from=1-1, to=3-1]
  \arrow["{\ap{f}{(p \dcomp q \dcomp r)}}", color={rgb,255:red,214;green,92;blue,92}, from=1-3, to=3-3]
  \arrow["{\ap{f}{r}}"', from=3-1, to=3-3]
\end{tikzcd}\]
~~~

but note that our lemma `··-unique'`{.Agda} says precisely that, for
every square with this boundary, we can get a square connecting the red
path $\ap{f}{(p \dcomp q \dcomp r)}$ and the composition $\ap{f}{p} \dcomp
\ap{f}{q} \dcomp \ap{f}{r}$.

```agda
ap-·· : (f : A → B) {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
      → ap f (p ·· q ·· r) ≡ ap f p ·· ap f q ·· ap f r
ap-·· f p q r = ··-unique' (ap-square f (··-filler p q r))

ap-∙ : (f : A → B) {x y z : A} (p : x ≡ y) (q : y ≡ z)
      → ap f (p ∙ q) ≡ ap f p ∙ ap f q
ap-∙ f p q = ap-·· f refl p q
```

## Dependent paths, continued

Armed with the transport and composition operations, we can continue the
development of the notion of [dependent path](#dependent-paths). The
`transport`{.Agda} operation gives rise to an *emergent* notion of
dependent path, in addition to the primitive `PathP`{.Agda}. If we have
a line of types $P(i)$, and points $x : P(\iZ), y : P(\iO)$, then we can
say that they are "identified over $P$" to mean either $\PathP{P}{x}{y}$
*or* $\transport{P}{x} \is y$.

It's possible to directly construct paths in the universe that witness
the agreement between these:

```agda
PathP≡Path : ∀ {ℓ} (P : I → Type ℓ) (p : P i0) (q : P i1)
           → PathP P p q ≡ Path (P i1) (transport (λ i → P i) p) q
PathP≡Path P p q i = PathP (λ j → P (i ∨ j)) (transport-filler (λ j → P j) p i) q

PathP≡Path⁻ : ∀ {ℓ} (P : I → Type ℓ) (p : P i0) (q : P i1)
            → PathP P p q ≡ Path (P i0) p (transport (λ i → P (~ i)) q)
PathP≡Path⁻ P p q i = PathP (λ j → P (~ i ∧ j)) p (transport-filler (λ j → P (~ j)) q i)
```

We can see that the first definition is well-formed by substituting
either `i0` or `i1` for the variable `i`.

* When `i = i0`, we have `PathP (λ j → P j) p q`, by the endpoint rule
for `transport-filler`{.Agda}.

* When `i = i1`, we have `PathP (λ j → P i1) (transport P p) q`, again
by the endpoint rule for `transport-filler`{.Agda}.

The connection between dependent paths and transport gives another
"counterexample" to thinking of paths as _equality_. For instance, it's
hard to imagine a world in which `true` and `false` can be equal in any
interesting sense of the word _equal_ --- but *over* the identification
$\rm{Bool} \equiv \rm{Bool}$ that switches the points around, `true` and
`false` can be identified!

## Squeezing and spreading

Using the De Morgan algebra structure on the interval, together with the
"$\phi$" argument to `transp`{.Agda}, we can implement operations that
move a point between the concrete endpoints (i0, i1) and arbitrary
points on the interval, represented as variables. First, we introduce
the following names for transporting forwards and backwards along a
path.

```agda
coe0→1 : ∀ {ℓ} (A : I → Type ℓ) → A i0 → A i1
coe0→1 A a = transp (λ i → A i) i0 a

coe1→0 : ∀ {ℓ} (A : I → Type ℓ) → A i1 → A i0
coe1→0 A a = transp (λ i → A (~ i)) i0 a
```

These two operations will "spread" a value which is concentrated at one
of the endpoints to cover the entire path. They are named after their
type: they move a value from $\iZ/\iO$ to an arbitrary $i$.

```agda
coe0→i : ∀ {ℓ : I → Level} (A : ∀ i → Type (ℓ i)) (i : I) → A i0 → A i
coe0→i A i a = transp (λ j → A (i ∧ j)) (~ i) a

coe1→i : ∀ {ℓ : I → Level} (A : ∀ i → Type (ℓ i)) (i : I) → A i1 → A i
coe1→i A i a = transp (λ j → A (i ∨ ~ j)) i a
```

In the converse direction, we have "squeeze" operations, which take a
value from $A(i)$ to $A(\iZ)$ or $A(\iO)$.

```agda
coei→0 : ∀ {ℓ : I → Level} (A : ∀ i → Type (ℓ i)) (i : I) → A i → A i0
coei→0 A i a = transp (λ j → A (i ∧ ~ j)) (~ i) a

coei→1 : ∀ {ℓ : I → Level} (A : ∀ i → Type (ℓ i)) (i : I) → A i → A i1
coei→1 A i a = transp (λ l → A (i ∨ l)) i a
```

Using these operations, we can define maps that convert between
`PathP`{.Agda}s and "book-style" dependent paths, which are more
efficient than transporting along `PathP≡Path`{.Agda}.

```agda
module _ {ℓ} {A : I → Type ℓ} {x : A i0} {y : A i1} where
  to-pathp : coe0→1 A x ≡ y → PathP A x y
  to-pathp p i = hcomp (∂ i) λ where
    j (j = i0) → coe0→i A i x
    j (i = i0) → x
    j (i = i1) → p j

  from-pathp : PathP A x y → coe0→1 A x ≡ y
  from-pathp p i = transp (λ j → A (i ∨ j)) i (p i)
```

Note that by composing the functions `to-pathp`{.Agda} and
`to-pathp`{.Agda} with the reversal on the interval, we obtain a
correspondence `PathP`{.Agda} and paths with a backwards transport on
the right-hand side.

```agda
module _ {ℓ} {A : I → Type ℓ} {x : A i0} {y : A i1} where
  to-pathp⁻ : x ≡ coe1→0 A y → PathP A x y
  to-pathp⁻ p = symP $ to-pathp {A = λ j → A (~ j)} (λ i → p (~ i))

  from-pathp⁻ : PathP A x y → x ≡ coe1→0 A y
  from-pathp⁻ p = sym $ from-pathp (λ i → p (~ i))
```

It's actually fairly complicated to show that the functions
`to-pathp`{.Agda} and `from-pathp`{.Agda} are inverses. The statements
of the theorems are simple:

```agda
to-from-pathp
  : ∀ {ℓ} {A : I → Type ℓ} {x y} (p : PathP A x y) → to-pathp (from-pathp p) ≡ p

from-to-pathp
  : ∀ {ℓ} {A : I → Type ℓ} {x y} (p : coe0→1 A x ≡ y)
  → from-pathp {A = A} (to-pathp p) ≡ p
```

<!--
```agda
hcomp-unique : ∀ {ℓ} {A : Type ℓ} φ
               (u : ∀ i → Partial (φ ∨ ~ i) A)
             → (h2 : ∀ i → A [ _ ↦ (λ { (i = i0) → u i0 1=1
                                      ; (φ = i1) → u i 1=1 }) ])
             → hcomp φ u ≡ outS (h2 i1)
hcomp-unique φ u h2 i =
  hcomp (φ ∨ i) λ where
    k (k = i0) → u i0 1=1
    k (i = i1) → outS (h2 k)
    k (φ = i1) → u k 1=1
```
-->

<details>
<summary>
The proof is a bit hairy, since it involves very high-dimensional
hcomps. We leave it under this fold for the curious reader, but we
encourage you to take `to-from-pathp`{.Agda} and `from-to-pathp`{.Agda}
on faith otherwise.
</summary>

```agda
to-from-pathp {A = A} {x} {y} p i j = hcomp-unique (∂ j)
  (λ { k (k = i0) → coe0→i A j x
     ; k (j = i0) → x
     ; k (j = i1) → coei→1 A k (p k)
     })
  (λ k → inS (transp (λ l → A (j ∧ (k ∨ l))) (~ j ∨ k) (p (j ∧ k))))
  i

from-to-pathp {A = A} {x} {y} p i j =
  hcomp (∂ i ∨ ∂ j) λ where
    k (k = i0) →
      coei→1 A (j ∨ ~ i) $
        transp (λ l → A (j ∨ (~ i ∧ l))) (i ∨ j) $
          coe0→i A j x

    k (j = i0) → slide (k ∨ ~ i)
    k (j = i1) → p k

    k (i = i0) → coei→1 A j $ hfill (∂ j) k λ where
      k (k = i0) → coe0→i A j x
      k (j = i0) → x
      k (j = i1) → p k

    k (i = i1) → hcomp (∂ k ∨ ∂ j) λ where
      l (l = i0) → slide (k ∨ j)
      l (k = i0) → slide j
      l (k = i1) → p (j ∧ l)
      l (j = i0) → slide k
      l (j = i1) → p (k ∧ l)
  where
    slide : coe0→1 A x ≡ coe0→1 A x
    slide i = coei→1 A i (coe0→i A i x)
```

</details>


# Syntax sugar

When constructing long chains of identifications, it's rather helpful to
be able to visualise _what_ is being identified with more "priority"
than _how_ it is being identified. For this, a handful of combinators
with weird names are defined:

```agda
≡⟨⟩-syntax : ∀ {ℓ} {A : Type ℓ} (x : A) {y z} → y ≡ z → x ≡ y → x ≡ z
≡⟨⟩-syntax x q p = p ∙ q

≡⟨⟩≡⟨⟩-syntax
  : ∀ {ℓ} {A : Type ℓ} (w x : A) {y z}
  → (p : w ≡ x)
  → (q : x ≡ y)
  → (r : y ≡ z)
  → w ≡ z
≡⟨⟩≡⟨⟩-syntax w x p q r = p ·· q ·· r

infixr 2 ≡⟨⟩-syntax
syntax ≡⟨⟩-syntax x q p = x ≡⟨ p ⟩ q

_≡˘⟨_⟩_ : ∀ {ℓ} {A : Type ℓ} (x : A) {y z : A} → y ≡ x → y ≡ z → x ≡ z
x ≡˘⟨ p ⟩ q = (sym p) ∙ q

_≡⟨⟩_ : ∀ {ℓ} {A : Type ℓ} (x : A) {y : A} → x ≡ y → x ≡ y
x ≡⟨⟩ x≡y = x≡y

_∎ : ∀ {ℓ} {A : Type ℓ} (x : A) → x ≡ x
x ∎ = refl

infixr 2 _≡⟨⟩_ _≡˘⟨_⟩_
infix  3 _∎

along : ∀ {ℓ} {A : I → Type ℓ} {x : A i0} {y : A i1} → (i : I) → PathP A x y → A i
along i p = p i
```

These functions are used to make _equational reasoning chains_. For
instance, the following proof that addition of naturals is associative
is done in equational reasoning style:

```agda
private
  +-associative : (x y z : Nat) → x + (y + z) ≡ (x + y) + z
  +-associative zero y z = refl
  +-associative (suc x) y z =
    suc (x + (y + z)) ≡⟨ ap suc (+-associative x y z) ⟩
    suc ((x + y) + z) ∎
```

<div class="equations">

If your browser runs JavaScript, these equational reasoning chains, by
default, render with the _justifications_ (the argument written between
`⟨ ⟩`) hidden; There is a checkbox to display them, either on the
sidebar or on the top bar depending on how narrow your screen is. For
your convenience, it's here too:

<div style="display: flex; flex-direction: column; align-items: center;">
  <span class="equations" style="display: flex; gap: 0.25em; flex-wrap: nowrap;">
    <input name=body-eqns type="checkbox" class="equations" id=body-eqns>
    <label for=body-eqns>Equations</label>
  </span>
</div>

Try pressing it!

</div>

# Basics of groupoid structure

A large part of the study of HoTT is the _characterisation of path
spaces_. Given a type `A`, what does `Path A x y` look like? [Hedberg's
theorem] says that for types with decidable equality, it's boring. For
[the circle], we can prove its loop space is the integers --- we have
`Path S¹ base base ≡ Int`.

[Hedberg's theorem]: 1Lab.Path.IdentitySystem.html
[the circle]: Homotopy.Space.Circle.html

Most of these characterisations need machinery that is not in this
module to be properly stated. Even then, we can begin to outline a few
simple cases:

## Σ types

For `Σ`{.Agda} types, a path between `(a , b) ≡ (x , y)` consists of a
path `p : a ≡ x`, and a path between `b` and `y` laying over `p`.

```agda
Σ-pathp
  : ∀ {ℓ ℓ'} {A : I → Type ℓ} {B : ∀ i → A i → Type ℓ'}
  → {x : Σ _ (B i0)} {y : Σ _ (B i1)}
  → (p : PathP A (x .fst) (y .fst))
  → PathP (λ i → B i (p i)) (x .snd) (y .snd)
  → PathP (λ i → Σ (A i) (B i)) x y
Σ-pathp p q i = p i , q i
```

We can also use the book characterisation of dependent paths, which is
simpler in the case where the `Σ`{.Agda} represents a subset --- i.e.,
`B` is a family of propositions.

```agda
Σ-path : ∀ {a b} {A : Type a} {B : A → Type b}
       → {x y : Σ A B}
       → (p : x .fst ≡ y .fst)
       → subst B p (x .snd) ≡ (y .snd)
       → x ≡ y
Σ-path {A = A} {B} {x} {y} p q = Σ-pathp p (to-pathp q)
```

## Π types {defines="funext function-extensionality homotopy"}

For dependent functions, the paths are _homotopies_, in the topological
sense: `Path ((x : A) → B x) f g` is the same thing as a function `I →
(x : A) → B x` --- which we could turn into a product if we really wanted
to.

```agda
happly : ∀ {a b} {A : Type a} {B : A → Type b}
         {f g : (x : A) → B x}
       → f ≡ g → (x : A) → f x ≡ g x
happly p x i = p i x
```

With this, we have made definitional yet another principle which is
propositional in the HoTT book: _function extensionality_. Functions are
identical precisely if they assign the same outputs to every input.

```agda
funext : ∀ {a b} {A : Type a} {B : A → Type b}
         {f g : (x : A) → B x}
       → ((x : A) → f x ≡ g x) → f ≡ g
funext p i x = p x i
```

Furthermore, we know (since types are groupoids, and functions are
functors) that, by analogy with 1-category theory, paths in a function
type should behave like natural transformations (because they are arrows
in a functor category). This is indeed the case:

```agda
homotopy-natural : ∀ {a b} {A : Type a} {B : Type b}
                 → {f g : A → B}
                 → (H : (x : A) → f x ≡ g x)
                 → {x y : A} (p : x ≡ y)
                 → H x ∙ ap g p ≡ ap f p ∙ H y
homotopy-natural {f = f} {g = g} H {x} {y} p = ∙-unique _ λ i j →
  hcomp (~ i ∨ ∂ j) λ where
    k (k = i0) → H x (j ∧ i)
    k (i = i0) → f (p (j ∧ k))
    k (j = i0) → f x
    k (j = i1) → H (p k) i
```

## Paths

The groupoid structure of _paths_ is also interesting. While the
characterisation of `Path (Path A x y) p q` is fundamentally tied to the
characterisation of `A`, there are general theorems that can be proven
about _transport_ in path spaces. For example, transporting both
endpoints of a path is equivalent to a ternary composition:

<!--
```agda
double-composite
  : ∀ {ℓ} {A : Type ℓ}
  → {x y z w : A}
  → (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
  → p ·· q ·· r ≡ p ∙ q ∙ r
double-composite p q r i j =
  hcomp (i ∨ ∂ j) λ where
    k (i = i1) → ∙-filler' p (q ∙ r) k j
    k (j = i0) → p (~ k)
    k (j = i1) → r (i ∨ k)
    k (k = i0) → ∙-filler q r i j
```
-->

```agda
transport-path : ∀ {ℓ} {A : Type ℓ} {x y x' y' : A}
                → (p : x ≡ y)
                → (left : x ≡ x') → (right : y ≡ y')
                → transport (λ i → left i ≡ right i) p ≡ sym left ∙ p ∙ right
transport-path {A = A} {x} {y} {x'} {y'} p left right =
  lemma ∙ double-composite _ _ _
```

The argument is slightly indirect. First, we have a proof (omitted for
space) that composing three paths using binary composition (twice) is
the same path as composing them in one go, using the (ternary) double
composition operation. This is used in a second step, as a slight
endpoint correction.

The first step, the lemma below, characterises transport in path spaces
in terms of the double composite: This is _almost_ definitional, but
since Cubical Agda implements only composition **for `PathP`**, we need
to adjust the path by a bunch of transports:

```agda
  where
    lemma : _ ≡ (sym left ·· p ·· right)
    lemma i j = hcomp (~ i ∨ ∂ j) λ where
      k (k = i0) → transp (λ j → A) i (p j)
      k (i = i0) → hfill (∂ j) k λ where
        k (k = i0) → transp (λ i → A) i0 (p j)
        k (j = i0) → transp (λ j → A) k (left k)
        k (j = i1) → transp (λ j → A) k (right k)
      k (j = i0) → transp (λ j → A) (k ∨ i) (left k)
      k (j = i1) → transp (λ j → A) (k ∨ i) (right k)
```

Special cases can be proven about substitution. For example, if we hold
the right endpoint constant, we get something homotopic to
composing with the inverse of the adjustment path:

```agda
subst-path-left : ∀ {ℓ} {A : Type ℓ} {x y x' : A}
                → (p : x ≡ y)
                → (left : x ≡ x')
                → subst (λ e → e ≡ y) left p ≡ sym left ∙ p
subst-path-left {y = y} p left =
  subst (λ e → e ≡ y) left p     ≡⟨⟩
  transport (λ i → left i ≡ y) p ≡⟨ transport-path p left refl ⟩
  sym left ∙ p ∙ refl            ≡⟨ ap (sym left ∙_) (sym (∙-filler _ _)) ⟩
  sym left ∙ p                   ∎
```

If we hold the left endpoint constant instead, we get a respelling of composition:

```agda
subst-path-right : ∀ {ℓ} {A : Type ℓ} {x y y' : A}
                 → (p : x ≡ y)
                 → (right : y ≡ y')
                 → subst (λ e → x ≡ e) right p ≡ p ∙ right
subst-path-right {x = x} p right =
  subst (λ e → x ≡ e) right p     ≡⟨⟩
  transport (λ i → x ≡ right i) p ≡⟨ transport-path p refl right ⟩
  sym refl ∙ p ∙ right            ≡⟨⟩
  refl ∙ p ∙ right                ≡⟨ sym (∙-filler' _ _) ⟩
  p ∙ right                       ∎
```

Finally, we can apply the same path to both endpoints:

```agda
subst-path-both : ∀ {ℓ} {A : Type ℓ} {x x' : A}
                → (p : x ≡ x)
                → (adj : x ≡ x')
                → subst (λ x → x ≡ x) adj p ≡ sym adj ∙ p ∙ adj
subst-path-both p adj = transport-path p adj adj
```

<!--
TODO: Explain these whiskerings

```agda
_◁_ : ∀ {ℓ} {A : I → Type ℓ} {a₀ a₀' : A i0} {a₁ : A i1}
  → a₀ ≡ a₀' → PathP A a₀' a₁ → PathP A a₀ a₁
(p ◁ q) i = hcomp (∂ i) λ where
  j (i = i0) → p (~ j)
  j (i = i1) → q i1
  j (j = i0) → q i

_▷_ : ∀ {ℓ} {A : I → Type ℓ} {a₀ : A i0} {a₁ a₁' : A i1}
  → PathP A a₀ a₁ → a₁ ≡ a₁' → PathP A a₀ a₁'
(p ▷ q) i = hcomp (∂ i) λ where
  j (i = i0) → p i0
  j (i = i1) → q j
  j (j = i0) → p i

infixr 31 _◁_
infixl 32 _▷_

Square≡double-composite-path : ∀ {ℓ} {A : Type ℓ}
          → {w x y z : A}
          → {p : x ≡ w} {q : x ≡ y} {s : w ≡ z} {r : y ≡ z}
          → Square p q s r ≡ (sym p ·· q ·· r ≡ s)
Square≡double-composite-path {p = p} {q} {s} {r} k =
  PathP (λ i → p (i ∨ k) ≡ r (i ∨ k))
    (··-filler (sym p) q r k) s

J' : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁}
     (P : (x y : A) → x ≡ y → Type ℓ₂)
   → (∀ x → P x x refl)
   → {x y : A} (p : x ≡ y)
   → P x y p
J' P prefl {x} p = transport (λ i → P x (p i) λ j → p (i ∧ j)) (prefl x)

J₂
  : ∀ {ℓa ℓb ℓp} {A : Type ℓa} {B : Type ℓb} {xa : A} {xb : B}
  → (P : ∀ ya yb → xa ≡ ya → xb ≡ yb → Type ℓp)
  → P xa xb refl refl
  → ∀ {ya yb} p q → P ya yb p q
J₂ P prr p q = transport (λ i → P (p i) (q i) (λ j → p (i ∧ j)) (λ j → q (i ∧ j))) prr

invert-sides : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : x ≡ z)
             → Square q p (sym q) (sym p)
invert-sides {x = x} p q i j = hcomp (∂ i ∨ ∂ j) λ where
  k (i = i0) → p (k ∧ j)
  k (i = i1) → q (~ j ∧ k)
  k (j = i0) → q (i ∧ k)
  k (j = i1) → p (~ i ∧ k)
  k (k = i0) → x

sym-∙-filler : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) → I → I → I → A
sym-∙-filler {A = A} {z = z} p q i j k =
  hfill (∂ i) k λ where
    l (i = i0) → q (l ∨ j)
    l (i = i1) → p (~ l ∧ j)
    l (l = i0) → invert-sides q (sym p) i j

sym-∙ : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y) (q : y ≡ z) → sym (p ∙ q) ≡ sym q ∙ sym p
sym-∙ p q i j = sym-∙-filler p q j i i1

infixl 45 _$ₚ_

_$ₚ_ : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : A → Type ℓ₂} {f g : ∀ x → B x}
     → f ≡ g → ∀ x → f x ≡ g x
(f $ₚ x) i = f i x
{-# INLINE _$ₚ_ #-}

_≠_ : ∀ {ℓ} {A : Type ℓ} → A → A → Type ℓ
x ≠ y = ¬ x ≡ y
```
-->
