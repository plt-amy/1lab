```agda
open import Algebra.Prelude

open import Cat.Instances.Sets.Cocomplete
open import Cat.Instances.Functor.Limits
open import Cat.Instances.Slice.Presheaf
open import Cat.Instances.Sets.Complete
open import Cat.Diagram.Everything
open import Cat.Functor.Everything
open import Cat.Instances.Elements
open import Cat.Instances.Slice
open import Cat.Instances.Lift

import Cat.Functor.Bifunctor as Bifunctor
import Cat.Reasoning

module Topoi.Base where
```

<!--
```agda
open _=>_
```
-->

# Grothendieck topoi

Topoi are an abstraction introduced by Alexander Grothendieck in the
1960s as a generalisation of [topological spaces], suitable for his work
in algebraic geometry. Later (in the work of William Lawvere, and even
later Myles Tierney), topoi found a new life as "categories with a nice
internal logic", which mirrors that of the category $\sets$. Perhaps
surprisingly, every Grothendieck topos is also a topos in their logical
conception (called **elementary**); Since elementary topoi are very hard
to come by predicatively, we formalise a particular incarnation of
Grothendieck's notion here.

[topological spaces]: https://ncatlab.org/nlab/show/topological+space

Grothendieck described his topoi by first defining a notion of _site_,
which generalises the (poset of) open subsets of a topological space,
and then describing what "sheaves on a site" should be, the
corresponding generalisation of sheaves on a space. Instead of directly
defining the notion of site, we will leave it implicitly, and define a
**topos** as follows:

A **topos** $\ca{T}$ is a [full subcategory] of a [presheaf category]
$[\ca{C}\op,\sets]$ (the category $\ca{C}$ is part of the definition)
such that the inclusion functor $\iota : \ca{T} \mono [\ca{C}\op,\sets]$
admits a [left adjoint], and this left adjoint preserves [finite
limits]. We summarise this situation in the diagram below, where "lex"
(standing for "**l**eft **ex**act") is old-timey speak for "finite limit
preserving".

~~~{.quiver .short-15}
\[\begin{tikzcd}
  {\mathcal{T}} & {[\mathcal{C}^{\mathrm{op}},\mathbf{Sets}]}
  \arrow[shift right=2, hook, from=1-1, to=1-2]
  \arrow["{\mathrm{lex}}"', shift right=2, from=1-2, to=1-1]
\end{tikzcd}\]
~~~

[full subcategory]: Cat.Functor.FullSubcategory.html
[presheaf category]: Cat.Functor.Hom.html#the-yoneda-embedding
[left adjoint]: Cat.Functor.Adjoint.html
[finite limits]: Cat.Diagram.Limit.Finite.html

In type theory, we must take care about the specific [universes] in
which everything lives. Now, much of Grothendieck topos theory
generalises to arbitrary "base" topoi, via the use of bounded geometric
morphisms, but the "main" definition talks about $\sets$-topoi. In
particular, every universe $\kappa$ generates a theory of
$\sets_\kappa$-topoi, the categories of [$\kappa$-small] sheaves on
$\kappa$-small sites.

[$\kappa$-small]: 1Lab.intro.html#universes-and-size-issues

Fix a universe level $\kappa$, and consider the category $\sets_\kappa$:
A topos $\ca{T}$ might be a large category (i.e. it might have a space
of objects $o$ with $o > \kappa$), but it is _essentially locally
small_, since it admits a fully-faithful functor into
$[\ca{C}\op,\sets_\kappa]$, which have homs at level $\kappa$. Hence,
even if we allowed the category $\ca{T}$ to have $\hom$s at a level
$\ell$, we would have no more information there than fits in $\kappa$.

For this reason, a topos $\ca{C}$ only has two levels: The level $o$ of
its objects, and the level $\kappa$ of the category of Sets relative to
which $\ca{C}$ is a topos.

[universes]: 1Lab.Type.html

```agda
record Topos {o} ?? (???? : Precategory o ??) : Type (lsuc (o ??? ??)) where
  field
    site : Precategory ?? ??

    ?? : Functor ???? (PSh ?? site)
    has-ff : is-fully-faithful ??

    L : Functor (PSh ?? site) ????
    L-lex : is-lex L

    L????? : L ??? ??

  module ?? = Functor ??
  module L = Functor L
  module L????? = _???_ L?????
```

## As generalised spaces

I'll echo here the standard definition of topological space, but due to
personal failings I can't motivate it. A **topological space** $(X,
\tau)$ consists of a set of _points_ $X$, and a _topology_ $\tau$, a
subset of its [powerset] which is closed under arbitrary unions and
finite intersections.

Let's reword that using category-theoretic language: Recall that the
powerset of $X$ is the poset $[X,\props]$. It is --- being a functor
category into a complete and cocomplete (thin) category --- _also_
complete and cocomplete, so all joins and finite meets (unions and
intersections) exist; Furthermore, the distributive law

$$
S \cap \left(\bigcup_i F_i\right) = \bigcup_i (S \cap F_i)
$$

holds for any subset $S$ and family of subsets $F$. A [lattice]
satisfying these properties (finite meets, arbitrary joins, the
distributive law) is called a **frame**. A map of frames $f : A \to B$
is defined to be a map of their underlying sets preserving finite meets
and arbitrary joins --- by abstract nonsense, this is the same as a
function $f^* : B \to A$ which preserves finite meets and has a right
adjoint $f_* : A \to B$[^aft].

[^aft]: By the adjoint functor theorem, any map between posets which
preserves arbitrary joins has a right adjoint; Conversely, every map
which has a right adjoint preserves arbitrary joins.

[powerset]: Data.Power.html
[lattice]: Algebra.Lattice.html

We can prove that a topology $\tau$ on $X$ is the same thing as a
subframe of its powerset $[X,\props]$ --- a collection of subsets of
$X$, closed under finite meets and arbitrary joins.

Now, the notion of "topos" as a generalisation of that of "topological
space" is essentially self-evident: A topos $\ca{T}$ is a sub-topos of a
presheaf category $[\ca{C}\op,\sets]$. We have essentially categorified
"subframe" into "subtopos", and $\props$ into $\sets$. Note that, while
this seems circular ("a topos is a sub-topos of..."), the notion of
subtopos --- or rather, of **geometric embedding** --- makes no mention
of actual topoi, and makes sense for any pair of categories.

## As categories of spaces

Another perspective on topoi is that they are _categories of_ spaces,
rather than spaces themselves. We start by looking at presheaf topoi,
$[\ca{C}\op,\sets]$. The [coyoneda lemma] tells us that every presheaf
is a colimit of representables, which can be restated in less abstract
terms by saying that _presheaves are instructions for gluing together
objects of $\ca{C}$._ The objects of $\ca{C}$ are then interpreted as
"primitive shapes", and the maps in $\ca{C}$ are interpreted as "maps to
glue against".

[coyoneda lemma]: Cat.Functor.Hom.html#the-coyoneda-lemma

Let's make this more concrete by considering an example: Take $\ca{C} =
\bull \tto \bull$, the category with two points --- let's
call them $V$ and $E$ --- and two arrows $s, t : V \to E$. A presheaf
$F$ on this category is given by a set $F_0(V)$, a set $F_0(E)$, and two
functions $F_1(s), F_1(t) : F_0(E) \to F_0(V)$. We call $F_0(V)$ the
vertex set, and $F_0(E)$ the edge set. Indeed, a presheaf on this
category is a _directed multigraph_, and maps between presheaves
_preserve adjacency_.

Our statement about "gluing primitive shapes" now becomes the rather
pedestrian statement "graphs are made up of vertices and edges". For
instance, the graph $\bull \to \bull \to \bull$ can be considered as a
disjoint union of two edges, which is then glued together in a way such
that the target of the first is the source of the second. The maps $s, t
: V \to E$ exhibit the two ways that a vertex can be considered "part
of" an edge.

## As "logically nice" categories

The definition of topos implies that any topos $\ca{T}$ enjoys many of
the same categorical properties of the category $\sets$ (see
[below](#properties)). Topoi are [complete] and [cocomplete], [cartesian
closed] (even [locally so]) --- colimits are stable under pullback,
coproducts are [disjoint], and [equivalence relations are effective].

[complete]: Cat.Diagram.Limit.Base.html#completeness
[cocomplete]: Cat.Diagram.Colimit.Base.html#cocompleteness
[cartesian closed]: Cat.CartesianClosed.Base.html
[locally so]: Cat.CartesianClosed.Locally.html
[disjoint]: Cat.Diagram.Coproduct.Indexed.html#disjoint-coproducts
[equivalence relations are effective]: Cat.Diagram.Congruence.html#effective-congruences

These properties, but _especially_ local cartesian closure, imply that
the internal logic of a topos is an incredibly nice form of type theory.
Dependent sums and products exist, there is an object of natural
numbers, the [poset of subobjects] is a complete [lattice] (even a
Heyting algebra), including existential and universal quantification.
Effectivity of congruences means that two points in a quotient are
identified if, and only if, they are related by the congruence.

[lattice]: Algebra.Lattice.html
[poset of subobjects]: Cat.Thin.Instances.Sub.html

In fact, this is essentially the _definition of_ a topos. The actual
definition, as a lex [reflective subcategory] of a presheaf category,
essentially ensures that the category $\ca{T}$ inherits the nice logical
properties of $\sets$ (through the presheaf category, which is _also_
very nice logically).

[reflective subcategory]: Cat.Functor.Adjoint.Reflective.html

**Terminology**: As was implicitly mentioned above, for a topos $L :
\ca{T} \xadj{}{} \psh(\ca{C})$, we call the category $\ca{C}$ the **site
of definition**. Objects in $\ca{T}$ are called **sheaves**, and the
functor $L$ is called **sheafification**. Maps between topoi are called
**geometric morphisms**, and will be defined below. We denote the
2-category of topoi, geometric morphisms and natural transformations by
$\topos$, following Johnstone. When $\psh(\ca{C})$ is regarded as a topos
unto itself, rather than an indirection in the definition of a sheaf
topos, we call it the **topos of $\ca{C}$-sets**.

# Examples

The "trivial" example of topoi is the category $\sets$, which is
equivalently the category $[*\op,\sets]$ of presheaves on the [terminal
category]. This is, in fact, the [terminal object] in the 2-category
$\topos$ of topoi (morphisms are described
[below](#geometric-morphisms)), so we denote it by `????`.

[terminal category]: Cat.Instances.Shape.Terminal.html
[terminal object]: Cat.Diagram.Terminal.html

```agda
???? : ??? {??} ??? Topos ?? (Sets ??)
???? {??} = sets where
  open Topos
  open Functor
  open _???_
  open is-lex
```

The inclusion functor $\sets \mono \psh(*)$ is given by the "constant
presheaf" functor, which sends each set $X$ to the constant functor with
value $X$.

```agda
  incl : Functor (Sets ??) (PSh ?? (Lift-cat ?? ?? ???Cat))
  incl .F??? x .F??? _    = x
  incl .F??? x .F??? _ f  = f
  incl .F??? x .F-id    = refl
  incl .F??? x .F-??? f g = refl

  incl .F??? f = NT (?? _ ??? f) (?? _ _ _ ??? refl)

  incl .F-id    = Nat-path ?? _ ??? refl
  incl .F-??? f g = Nat-path ?? _ ??? refl

  sets : Topos ?? (Sets ??)
  sets .site = Lift-cat ?? ?? ???Cat

  sets .?? = incl
```

This functor is fully faithful since a natural transformation between
presheaves on the point is entirely determined by its component at..
well, the point. Hence, the map $\eta \mapsto \eta_*$ exhibits an
inverse to the inclusion functor's action on morphisms, which is
sufficient (and necessary) to conclude fully-faithfulness.

```agda
  sets .has-ff {x} {y} = is-iso???is-equiv isic where
    open is-iso
    isic : is-iso (incl .F??? {x} {y})
    isic .inv nt         = ?? nt _

    isic .rinv nt i .?? _ = ?? nt _
    isic .rinv nt i .is-natural _ _ f j x =
      y .is-tr _ _ (?? j ??? nt .?? _ x) (?? j ??? nt .is-natural _ _ f j x) i j

    isic .linv x i = x
```

The "sheafification" left adjoint is given by evaluating a presheaf $F$
at its sole section $F(*)$, and similarly by evaluating a natural
transformation $\eta : F \To G$ at its one component $\eta_* : F(*) \to
G(*)$.

```agda
  sets .L .F??? F    = F??? F _
  sets .L .F??? nt   = ?? nt _
  sets .L .F-id    = refl
  sets .L .F-??? f g = refl
```

<details>

<summary> These functors actually define an [adjoint equivalence] of
categories, $L$ is continuous and, in particular, lex. Rather than
appealing to that theorem, though, we define the preservation of finite
limits directly for efficiency concerns. </summary>

[adjoint equivalence]: Cat.Functor.Equivalence.html

```agda
  sets .L-lex .pres-??? {T} psh-terminal set = contr (cent .?? _) uniq where
    func = incl .F??? set
    cent = psh-terminal func .centre
    uniq : ??? f ??? cent .?? _ ??? f
    uniq f = ap (?? e ??? e .?? _) (psh-terminal func .paths f???) where
      f??? : _ => _
      f??? .?? _ = f
      f??? .is-natural _ _ _ = funext ?? x ??? happly (sym (F-id T)) _

  sets .L-lex .pres-pullback {P} {X} {Y} {Z} pb = pb??? where
    open is-pullback
    pb??? : is-pullback (Sets ??) _ _ _ _
    pb??? .square = ap (?? e ??? ?? e _) (pb .square)
    pb??? .limiting {P'} {p???' = p???'} {p???' = p???'} p =
      ?? (pb .limiting {P??? = incl .F??? P'} {p???' = p1'} {p???' = p2'}
          (Nat-path ?? _ ??? p)) _
      where
        p1' : _ => _
        p1' .?? _ = p???'
        p1' .is-natural x y f i o = F-id X (~ i) (p???' o)
        p2' : _ => _
        p2' .?? _ = p???'
        p2' .is-natural x y f i o = F-id Y (~ i) (p???' o)
    pb??? .p??????limiting = ap (?? e ??? ?? e _) (pb .p??????limiting)
    pb??? .p??????limiting = ap (?? e ??? ?? e _) (pb .p??????limiting)
    pb??? .unique {P???} {lim' = lim'} p1 p2 =
      ap (?? e ??? ?? e _) (pb .unique {lim' = l???}
        (Nat-path ?? _ ??? p1) (Nat-path ?? _ ??? p2))
      where
        l??? : incl .F??? P??? => P
        l??? .?? _ = lim'
        l??? .is-natural x y f i o = F-id P (~ i) (lim' o)
```
</details>

Similarly, we can construct the adjunction unit and counit by looking at
components and constructing identity natural transformations.

```agda
  sets .L????? .unit .?? _ .?? _ f            = f
  sets .L????? .unit .?? F .is-natural _ _ _ = F-id F
  sets .L????? .unit .is-natural _ _ _      = Nat-path ?? _ ??? refl

  sets .L????? .counit .?? _ x            = x
  sets .L????? .counit .is-natural _ _ _ = refl

  sets .L????? .zig = refl
  sets .L????? .zag = Nat-path ?? _ ??? refl
```

More canonical examples are given by any presheaf category, where both
the inclusion and sheafification functors are the identity.  Examples of
presheaf topoi are abundant in abstract homotopy theory (the categories
of cubical and simplicial sets) --- which also play an important role in
modelling homotopy _type_ theory; Another example of a presheaf topos is
the category of _quivers_ (directed multigraphs).

```agda
Presheaf : ??? {??} (C : Precategory ?? ??) ??? Topos ?? (PSh ?? C)
Presheaf {??} C = psh where
  open Functor
  open Topos
  psh : Topos _ _
  psh .site = C
  psh .?? = Id
  psh .has-ff = id-equiv
  psh .L = Id
  psh .L-lex .is-lex.pres-??? c = c
  psh .L-lex .is-lex.pres-pullback pb = pb
  psh .L????? = adj where
    open _???_
    adj : Id ??? Id
    adj .unit = NT (?? _ ??? idnt) ?? x y f ??? Nat-path ?? _ ??? refl
    adj .counit = NT (?? _ ??? idnt) (?? x y f ??? Nat-path ?? _ ??? refl)
    adj .zig = Nat-path ?? _ ??? refl
    adj .zag = Nat-path ?? _ ??? refl
```

# Properties of topoi

The defining property of a topos $\ca{T}$ is that it admits a
geometric embedding into a presheaf category, meaning the adjunction
$L : \ca{T} \xadj{}{} \psh(\ca{C}) : \iota$ is very special indeed: Since
the right adjoint is fully faithful, the adjunction is [monadic],
meaning that it exhibits $\ca{T}$ as the category of [algebras] for
a (lex, idempotent) monad: the "sheafification monad". This gives us
completeness in $\ca{T}$ for "free" (really, it's because presheaf
categories are complete, and those are complete because $\sets$ is.)

```agda
module _ {o ??} {???? : Precategory o ??} (T : Topos ?? ????) where
  open Topos T

  Sheafify : Monad (PSh ?? site)
  Sheafify = Adjunction???Monad L?????

  Sheafify-monadic : is-monadic L?????
  Sheafify-monadic = is-reflective???is-monadic L????? has-ff

  Topos-is-complete : is-complete ?? ?? ????
  Topos-is-complete = equivalence???complete
    (is-equivalence.inverse-equivalence Sheafify-monadic)
    (Eilenberg-Moore-is-complete
      (Functor-cat-is-complete (Sets-is-complete {?? = ??} {??} {??})))
```

[monadic]: Cat.Functor.Adjoint.Monadic.html
[algebras]: Cat.Diagram.Monad.html#algebras-over-a-monad

Furthermore, since $L$ preserves colimits (it is a left adjoint), then
we can compute the colimit of some diagram $F : J \to \ca{T}$ as the
colimit (in $\psh(\ca{C})$) of $\iota F$ --- which exists because
$\sets$ is cocomplete --- then apply $L$ to get a colimiting cocone for
$L \iota F$. But the counit of the adjunction $\eps : L \iota \To
\id{Id}$ is a natural isomorphism, so we have a colimiting cocone for
$F$.

```agda
  Topos-is-cocomplete : is-cocomplete ?? ?? ????
  Topos-is-cocomplete F =
    Colimit-ap-iso _
      (F???-iso-id-l (is-reflective???counit-iso L????? has-ff))
      sheafified
      where
      psh-colim : Colimit (?? F??? F)
      psh-colim = Functor-cat-is-cocomplete (Sets-is-cocomplete {?? = ??} {??} {??}) _

      sheafified : Colimit ((L F??? ??) F??? F)
      sheafified = subst Colimit F???-assoc $
        left-adjoint-colimit L????? psh-colim
```

Since the reflector is left exact, and thus in particular preserves
finite products, a theorem of Johnstone (Elephant A4.3.1) implies the
topos $\ca{T}$ is an _exponential ideal_ in $\psh(\ca{C})$: If $Y$ is a
sheaf, and $X$ is any presheaf, then the internal hom $[X,Y]$ is a
sheaf: topoi are [cartesian closed].

[cartesian closed]: Cat.CartesianClosed.Base.html

<!-- TODO [Amy 2022-04-02]
prove all of the above lmao
-->

Since topoi are defined as embedding faithfully into a category of
presheaves, it follows that they have a small **generating set**, in the
same sense that representables generate presheaves: In fact, the
generating set of a Grothendieck topos is exactly the set of
representables of its site!

Elaborating, letting $\ca{T}$ be a topos, two maps $f, g : X \to Y \in
\ca{T}$ are equal if and only if they are equal under $\iota$, i.e. as
maps of presheaves. But it follows from the [coyoneda lemma] that maps
of presheaves are equal if and only if they are equal on all
representables. Consequently, two maps in a $\ca{T}$ are equal if and
only if they agree on all generalised elements with domain the
sheafification of a representable:

[coyoneda lemma]: Cat.Functor.Hom.html#the-coyoneda-lemma

<!--
```agda
module _ {o ???} {C : Precategory o ???} (ct : Topos ??? C) where
  private
    module C = Cat.Reasoning C
    module ct = Topos ct
    module Site = Cat.Reasoning (ct.site)
    module PSh = Cat.Reasoning (PSh ??? ct.site)
    module ?? = Functor (ct.??)
    module L = Functor (ct.L)
    open _???_ (ct.L?????)

  open Functor
  open _=>_
```
-->

```agda
  Representables-generate
    : ??? {X Y} {f g : C.Hom X Y}
    ??? ( ??? {A} (h : C.Hom (L.??? (?????? ct.site A)) X)
      ??? f C.??? h ??? g C.??? h )
    ??? f ??? g
  Representables-generate {f = f} {g} sep =
    fully-faithful???faithful {F = ct.??} ct.has-ff $
      Representables-generate-presheaf ct.site ?? h ???
        ??.??? f PSh.??? h                                    ?????? mangle ???
        ??.??? (f C.??? counit.?? _ C.??? L.??? h) PSh.??? unit.?? _  ?????? ap (PSh._??? _) (ap ??.??? (sep _)) ???
        ??.??? (g C.??? counit.?? _ C.??? L.??? h) PSh.??? unit.?? _  ???????? mangle ???
        ??.??? g PSh.??? h                                    ???
```

<!--
```agda
    where
      mangle
        : ??? {X Y} {f : C.Hom X Y} {Z} {h : PSh.Hom Z _}
        ??? ??.??? f PSh.??? h ??? ??.??? (f C.??? counit.?? _ C.??? L.??? h) PSh.??? unit.?? _
      mangle {f = f} {h = h} =
        ??.??? f PSh.??? h                                                              ?????? PSh.insertl zag ???
        ??.??? (counit.?? _) PSh.??? unit.?? _ PSh.??? ??.??? f PSh.??? h                        ?????? ap??? PSh._???_ refl (PSh.extendl (unit.is-natural _ _ _)) ???
        ??.??? (counit.?? _) PSh.??? ??.??? (L.??? (??.??? f)) PSh.??? unit.?? _ PSh.??? h            ?????? ap??? PSh._???_ refl (ap (??.??? (L.??? (??.??? f)) PSh.???_) (unit.is-natural _ _ _)) ???
        ??.??? (counit.?? _) PSh.??? ??.??? (L.??? (??.??? f)) PSh.??? ??.??? (L.??? h) PSh.??? unit.?? _  ?????? ap (??.??? (counit.?? _) PSh.???_) (PSh.pulll (sym (??.F-??? _ _))) ???
        ??.??? (counit.?? _) PSh.??? ??.??? (L.??? (??.??? f) C.??? L.??? h) PSh.??? unit.?? _          ?????? PSh.pulll (sym (??.F-??? _ _)) ???
        ??.??? (counit.?? _ C.??? L.??? (??.??? f) C.??? L.??? h) PSh.??? unit.?? _                  ?????? ap (PSh._??? _) (ap ??.??? (C.extendl (counit.is-natural _ _ _))) ???
        ??.??? (f C.??? counit.?? _ C.??? L.??? h) PSh.??? unit.?? _                            ???
```
-->

Finally, the property of "being a topos" is invariant under slicing.
More specifically, since a given topos can be presented by different
sites, a presentation $\ca{T} \xadj{}{} \psh(\ca{C})$ can be sliced
under an object $X \in \ca{T}$ to present $\ca{T}/X$ as a sheaf topos,
with site of definition $\psh(\int \iota(X))$. This follows from a
wealth of pre-existing theorems:

- A pair $L \dashv R$ of adjoint functors can be [sliced] under an
object $X$, giving an adjunction $\Sigma \epsilon L/R(X) \dashv R/X$; Slicing a
functor preserves full-faithfulness and left exactness, hence slicing a
geometric embedding gives a geometric embedding.

[sliced]: Cat.Functor.Slice.html

- The category $\psh(\ca{C})/\iota(X)$ [is equivalent to] the category
$\psh(\int \iota(X))$, hence "being a presheaf topos is stable under
slicing". Furthermore, this equivalence is part of an ambidextrous
adjunction, hence both functors preserve limits.

[is equivalent to]: Cat.Instances.Slice.Presheaf.html

- Dependent sum $\Sigma f$ along an isomorphism is an equivalence of
categories; But since a topos is presented by a _reflective_ subcategory
inclusion, the counit is an isomorphism.

<!--
```agda
module _ {o ???} {C : Precategory o ???} (T : Topos ??? C) (X : Precategory.Ob C) where
  private
    module C = Cat.Reasoning C
    module Co = Cat.Reasoning (Slice C X)
    module T = Topos T

  open Topos
  open Functor
```
-->

We build the geometric embedding presenting $\ca{T}/X$ as a topos by
composing the adjunctions $\epsilon_!(L/\iota(X)) \dashv \iota/X$
and $F \dashv F^{-1}$ --- where $F$ is the equivalence $\psh(\ca{C})/X
\to \psh(\int X)$. The right adjoint is fully faithful because it
composes two fully faithful functors (a slice of $\iota$ and an
equivalence), the left adjoint preserves finite limits because it is a
composite of two equivalences (hence two right adjoints) and a lex
functor.

```agda
  Slice-topos : Topos ??? (Slice C X)
  Slice-topos .site = ??? T.site (T.??.F??? X)
  Slice-topos .?? = slice???total F??? Sliced (T.??) X
  Slice-topos .has-ff = ???-is-equiv (Sliced-ff {F = T.??} (T.has-ff)) slice???total-is-ff
  Slice-topos .L = (??f (T .L?????.counit.?? _) F??? Sliced (T.L) (T.??.F??? X)) F??? total???slice

  Slice-topos .L-lex = F???-is-lex
    (F???-is-lex
      (right-adjoint???lex
        (is-equivalence.F????????F
          (??-iso-equiv (C.iso???invertible
            (is-reflective???counit-is-iso T.L????? T.has-ff)))))
      (Sliced-lex T.L-lex))
    (right-adjoint???lex (slice???total-is-equiv .is-equivalence.F???F?????))

  Slice-topos .L????? = LF???GR (is-equivalence.F????????F slice???total-is-equiv)
                           (Sliced-adjoints T.L?????)
```

# Geometric morphisms

The definition of a topos as a generalisation of topological space leads
us to look for a categorification of "continuous map" to functors
between topoi. In the same way that a continuous function $f : X \to Y$
may be seen as a homomorphism of frames $f^* : O(Y) \to O(X)$, with
defining feature the preservation of finite meets and arbitrary joins,
we shall define a **geometric morphism** $\topos(X,Y)$ to be a functor
$f^* : Y \to X$ which is left exact and admits a right adjoint.

Why the right adjoint? Well, [right adjoints preserve limits], but by
duality, _left adjoints preserve colimits_. This embodies the "arbitrary
joins" part of a map of frames, whereas the "finite meets" come from
left exactness.

[right adjoints preserve limits]: Cat.Functor.Adjoint.Continuous.html

<!--
```agda
private
  variable
    o ??? o??? ?????? ?? ????? ???????? s s??? : Level
    E F G : Precategory o ???
  lvl : ??? {o ??? o??? ??????} ??? Precategory o ??? ??? Precategory o??? ?????? ??? Level
  lvl {o} {???} {o???} {??????} _ _ = o ??? ??? ??? ?????? ??? o???
```
-->

```agda
record Geom[_,_] (E : Precategory o ???) (F : Precategory o??? ??????) : Type (lvl E F) where
  no-eta-equality
  field
    Inv[_]  : Functor F E
    Dir[_]  : Functor E F
    Inv-lex : is-lex Inv[_]
    Inv???Dir : Inv[_] ??? Dir[_]

open Geom[_,_] public
```

Computation establishes that the identity functor is left exact, and
self adjoint, so it is in particular both the direct and inverse image
parts of a geometric morphism $\ca{T} \to \ca{T}$.

```agda
Idg : Geom[ E , E ]
Idg {E = E} = record { Inv[_] = Id ; Dir[_] = Id
                     ; Inv-lex = lex ; Inv???Dir = adj }
```

<!--
```
  where
    module E = Cat.Reasoning E

    lex : is-lex Id
    lex .is-lex.pres-??? f = f
    lex .is-lex.pres-pullback p = p

    adj : Id ??? Id
    adj ._???_.unit .?? _ = E.id
    adj ._???_.unit .is-natural x y f = sym E.id-comm
    adj ._???_.counit .?? _ = E.id
    adj ._???_.counit .is-natural x y f = sym E.id-comm
    adj ._???_.zig = E.idl _
    adj ._???_.zag = E.idl _
```
-->

Since [adjunctions compose], geometric morphisms do, too. Observe that
the composite of inverse images and the composite of direct images go in
different directions! Fortunately, this matches the convention for
composing adjunctions, where the functors "swap sides": $LF \dashv GR$.

[adjunctions compose]: Cat.Functor.Adjoint.Compose.html

```agda
_G???_ : Geom[ F , G ] ??? Geom[ E , F ] ??? Geom[ E , G ]
f G??? g = mk where
  module f = Geom[_,_] f
  module g = Geom[_,_] g
  open is-lex

  mk : Geom[ _ , _ ]
  Inv[ mk ] = Inv[ g ] F??? Inv[ f ]
  Dir[ mk ] = Dir[ f ] F??? Dir[ g ]
  mk .Inv???Dir = LF???GR f.Inv???Dir g.Inv???Dir
```

The composition of two left-exact functors is again left-exact, so
there's no impediment to composition there, either.

```agda
  mk .Inv-lex .pres-??? term ob = g.Inv-lex .pres-??? (f.Inv-lex .pres-??? term) _
  mk .Inv-lex .pres-pullback pb = g.Inv-lex .pres-pullback (f.Inv-lex .pres-pullback pb)
```

An important class of geometric morphism is the **geometric embedding**,
which we've already met as the very definition of `Topos`{.Agda}. These
are the geometric morphisms with fully faithful direct image. These are
_again_ closed under composition, so if we want to exhibit that a
certain category $\ca{C}$ is a topos, it suffices to give a geometric
embedding $\ca{C} \to \ca{T}$, where $\ca{T}$ is some topos which is
convenient for this application.

```agda
record Geom[_???_] (E : Precategory o ???) (F : Precategory o??? ??????) : Type (lvl E F) where
  field
    morphism : Geom[ E , F ]
    has-ff : is-fully-faithful Dir[ morphism ]

Geometric-embeddings-compose : Geom[ F ??? G ] ??? Geom[ E ??? F ] ??? Geom[ E ??? G ]
Geometric-embeddings-compose f g =
  record { morphism = f .morphism G??? g .morphism
         ; has-ff = ???-is-equiv (g .has-ff) (f .has-ff) }
  where open Geom[_???_]

Topos???geometric-embedding : (T : Topos ?? E) ??? Geom[ E ??? PSh ?? (T .Topos.site) ]
Topos???geometric-embedding T = emb where
  emb : Geom[ _ ??? _ ]
  Inv[ emb .Geom[_???_].morphism ] = T .Topos.L
  Dir[ emb .Geom[_???_].morphism ] = T .Topos.??
  emb .Geom[_???_].morphism .Inv-lex = T .Topos.L-lex
  emb .Geom[_???_].morphism .Inv???Dir = T .Topos.L?????
  emb .Geom[_???_].has-ff = T .Topos.has-ff
```

<!-- TODO [Amy 2022-04-02]
talk about geometric logic?
-->
