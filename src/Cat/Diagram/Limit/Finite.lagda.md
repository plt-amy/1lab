<!--
```agda
open import Cat.Diagram.Pullback.Properties
open import Cat.Instances.Shape.Parallel
open import Cat.Diagram.Limit.Equaliser
open import Cat.Diagram.Limit.Pullback
open import Cat.Diagram.Limit.Terminal
open import Cat.Diagram.Product.Finite
open import Cat.Instances.Shape.Cospan
open import Cat.Diagram.Limit.Product
open import Cat.Diagram.Limit.Base
open import Cat.Diagram.Limit.Cone
open import Cat.Instances.Discrete
open import Cat.Diagram.Equaliser
open import Cat.Diagram.Pullback
open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
open import Cat.Instances.Lift
open import Cat.Prelude
open import Cat.Finite

open import Data.Fin.Finite
open import Data.Bool

import Cat.Reasoning as Cat

open is-finite-precategory
```
-->

```agda
module Cat.Diagram.Limit.Finite where
```

<!--
```agda
module _ {ℓ ℓ'} (C : Precategory ℓ ℓ') where
  open Cat C
```
-->

# Finitely complete categories {defines="finite-limit finitely-complete finitely-complete-category"}

A category is said to be **finitely complete** if it admits limits for
every diagram with a [[finite|finite category]] shape.

```agda
  is-finitely-complete : Typeω
  is-finitely-complete = ∀ {o ℓ} {D : Precategory o ℓ} → is-finite-precategory D
                       → (F : Functor D C) → Limit F
```

Similarly to the case with [[arbitrary limits|complete category]], we can get away with
only the following common shapes of limits:

* A [[terminal object]] (limit over the empty diagram)
* Binary [[products]] (limits over diagrams of the form $\bullet\quad\bullet$, that is, two points)
* Binary [[equalisers]] (limits over diagrams of the form $\bullet\tto\bullet$)
* Binary [[pullbacks]] (limits over diagrams of the form $\bullet\to\bullet\ot\bullet$)

In reality, the list above has some redundancy. Since we can build
products out of pullbacks and a terminal object, and conversely we can
build pullbacks out of products and equalisers, either of the following
subsets suffices:

* A terminal object, binary products, binary equalisers;
* A terminal object and binary pullbacks.

For proving that a [thin category] is finitely complete, given that
equalisers are trivial and pullbacks coincide with products, it suffices
to give a terminal object and binary products.

[thin category]: Order.Base.html

```agda
  record Finitely-complete : Type (ℓ ⊔ ℓ') where
    field
      terminal   : Terminal C
      products   : Binary-products C
      equalisers : Equalisers C
      pullbacks  : Pullbacks C

  open Finitely-complete
```

As promised, the two definitions imply each other, assuming that $\cC$ is a
[[univalent category]] (which is required to go from binary products to *finite*
products).

```agda
  Finitely-complete→is-finitely-complete
    : is-category C
    → Finitely-complete → is-finitely-complete
  Finitely-complete→is-finitely-complete cat Flim finite =
    limit-as-equaliser-of-product
      (Cartesian→finite-products (Flim .terminal) (Flim .products) cat (finite .has-finite-Ob))
      (Cartesian→finite-products (Flim .terminal) (Flim .products) cat (finite .has-finite-Arrows))
      (Flim .equalisers)

  is-finitely-complete→Finitely-complete
    : is-finitely-complete → Finitely-complete
  is-finitely-complete→Finitely-complete flim = Flim where
    Flim : Finitely-complete
    Flim .terminal = Limit→Terminal C (flim finite-cat _)
    Flim .products = to-binary-products λ a b → Limit→Product C (flim Disc-finite _)
    Flim .equalisers = to-equalisers λ f g → Limit→Equaliser C (flim ·⇉·-finite _)
    Flim .pullbacks = to-pullbacks λ f g → Limit→Pullback C {lzero} {lzero} (flim ·→·←·-finite _)
```

## With equalisers

We now prove that having products and equalisers suffices to have all
pullbacks; Thus a terminal object, binary products and binary equalisers
suffice for finite completeness.

The main result is as follows: Let $P$ be a (the) product of $X$ and
$Y$, with its projections called $p_1$ and $p_2$. Letting $X \xto{f} Z
\xot{g} Y$ be a cospan, if the composites $fp_1$ and $gp_2$ have an
equaliser $e : E \to P$, then the square

~~~{.quiver}
\[\begin{tikzcd}
  E && X \\
  \\
  Y && Z
  \arrow["{fp_1}", from=1-1, to=1-3]
  \arrow["{fp_2}"', from=1-1, to=3-1]
  \arrow["g"', from=3-1, to=3-3]
  \arrow["f", from=1-3, to=3-3]
  \arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=1-1, to=3-3]
\end{tikzcd}\]
~~~

is a pullback. Now, that description is almost entirely
abstract-nonsensical, because (for generality) we do not use any
"canonical" products $X \times Y$ or equalisers $\mathrm{equ}(f,g)$. If
we work slightly more concretely, then this can be read as building the
pullback $X \times_Z Y$ as the largest subobject of $X \times Y$ where
$f, g$ agree. In particular, the pullback we want is the object $X
\times_Z Y$ in the commutative diagram below.

~~~{.quiver}
\[\begin{tikzcd}
  {X\times_ZY} & {X\times Y} & Z
  \arrow[from=1-1, to=1-2]
  \arrow["{f\pi_1}", shift left=1, from=1-2, to=1-3]
  \arrow["{g\pi_2}"', shift right=1, from=1-2, to=1-3]
\end{tikzcd}\]
~~~

```agda
  product+equaliser→pullback
    : ∀ {E P X Y Z} {p1 : Hom P X} {p2 : Hom P Y} {f : Hom X Z}
        {g : Hom Y Z} {e : Hom E P}
    → is-product C p1 p2
    → is-equaliser C (f ∘ p1) (g ∘ p2) e
    → is-pullback C (p1 ∘ e) f (p2 ∘ e) g
  product+equaliser→pullback {p1 = p1} {p2} {f} {g} {e} prod eq = pb where
    open is-pullback
    module eq = is-equaliser eq
    module pr = is-product prod

    pb : is-pullback C _ _ _ _
    pb .square = assoc _ _ _ ∙ eq.equal ∙ sym (assoc _ _ _)
```

To show that this object really _is_ a pullback of $f$ and $g$, note
that we can factor any pair of arrows $P' \to X$ and $P' \to Y$ through
the Cartesian product $X \times Y$, and use the universal property of
equalisers to factor _that_ as a unique arrow $P' \to X \times_Z Y$.

~~~{.quiver}
\[\begin{tikzcd}
  {X\times_ZY} & {X\times Y} & Z \\
  {P'}
  \arrow[from=1-1, to=1-2]
  \arrow["{f\pi_1}", shift left=1, from=1-2, to=1-3]
  \arrow["{g\pi_2}"', shift right=1, from=1-2, to=1-3]
  \arrow["{\exists!}", dashed, from=2-1, to=1-1]
  \arrow["{\langle p_1',p_2' \rangle}"', from=2-1, to=1-2]
\end{tikzcd}\]
~~~

```agda
    pb .universal {p₁' = p₁'} {p₂' = p₂'} p =
      eq.universal {e' = pr.⟨ p₁' , p₂' ⟩} (
        (f ∘ p1) ∘ pr.⟨ p₁' , p₂' ⟩ ≡⟨ pullr pr.π₁∘⟨⟩ ⟩
        f ∘ p₁'                     ≡⟨ p ⟩
        g ∘ p₂'                     ≡˘⟨ pullr pr.π₂∘⟨⟩ ⟩
        (g ∘ p2) ∘ pr.⟨ p₁' , p₂' ⟩ ∎
      )
    pb .p₁∘universal = pullr eq.factors ∙ pr.π₁∘⟨⟩
    pb .p₂∘universal = pullr eq.factors ∙ pr.π₂∘⟨⟩
    pb .unique p q =
      eq.unique (pr.unique (assoc _ _ _ ∙ p) (assoc _ _ _ ∙ q))
```

<!--
```agda
  products+equalisers→pullbacks
    : Binary-products C
    → Equalisers C
    → Pullbacks C
  products+equalisers→pullbacks prods eqs = pbs where
    open Binary-products prods
    open Equalisers eqs

    pbs : Pullbacks C
    pbs = to-pullbacks λ f g → record {
       has-is-pb = product+equaliser→pullback has-is-product has-is-eq
     }
```
-->

Hence, assuming that a category has a terminal object, binary products
and binary equalisers means it also admits pullbacks.

```agda
  with-equalisers
    : Terminal C
    → Binary-products C
    → Equalisers C
    → Finitely-complete
  with-equalisers top prods eqs .terminal = top
  with-equalisers top prods eqs .products = prods
  with-equalisers top prods eqs .equalisers = eqs
  with-equalisers top prods eqs .pullbacks = products+equalisers→pullbacks prods eqs
```


## With pullbacks

We'll now prove the converse: That a terminal object and pullbacks
implies having all products, and all equalisers.  We'll start with the
products, since those are simpler. Observe that we can complete a
product diagram (like the one on the left) to a pullback diagram (like
the one on the right) by adding in the unique arrows into the terminal
object $*$.

```agda
  terminal+pullback→product
    : ∀ {P X Y T} {p1 : Hom P X} {p2 : Hom P Y} {f : Hom X T} {g : Hom Y T}
    → is-terminal C T → is-pullback C p1 f p2 g → is-product C p1 p2
  terminal+pullback→product {p1 = p1} {p2} {f} {g} term pb = prod where
```

<div class=mathpar>

~~~{.quiver}
\[\begin{tikzcd}
  {P'} \\
  & {A\times B} && B \\
  \\
  & A
  \arrow["g", from=2-2, to=2-4]
  \arrow["f"', from=2-2, to=4-2]
  \arrow["{\langle f,g\rangle}", dashed, from=1-1, to=2-2]
  \arrow[curve={height=-12pt}, from=1-1, to=2-4]
  \arrow[curve={height=12pt}, from=1-1, to=4-2]
\end{tikzcd}\]
~~~

~~~{.quiver}
\[\begin{tikzcd}
  {P'} \\
  & {A\times B} && B \\
  \\
  & A && {*}
  \arrow["g", from=2-2, to=2-4]
  \arrow["f"', from=2-2, to=4-2]
  \arrow["{\langle f,g\rangle}", dashed, from=1-1, to=2-2]
  \arrow[curve={height=-12pt}, from=1-1, to=2-4]
  \arrow[curve={height=12pt}, from=1-1, to=4-2]
  \arrow["{!}", from=2-4, to=4-4]
  \arrow["{!}"', from=4-2, to=4-4]
\end{tikzcd}\]
~~~

</div>

```agda
    module Pb = is-pullback pb

    prod : is-product C p1 p2
    prod .is-product.⟨_,_⟩ p1' p2' =
      Pb.universal {p₁' = p1'} {p₂' = p2'} (is-contr→is-prop (term _) _ _)
    prod .is-product.π₁∘⟨⟩ = Pb.p₁∘universal
    prod .is-product.π₂∘⟨⟩ = Pb.p₂∘universal
    prod .is-product.unique p q = Pb.unique p q
```

For equalisers, the situation is a bit more complicated. Recall that, by
analogy with the case in Set, we can consider the equaliser to be the
solution set of $f(x) = g(x)$, for some $f, g : A \to B$. We can
consider the two sides of this equation as a _single_ map $\langle f, g
\rangle : A \to B \times B$; The equation is solved where _this_ pairing
map equals some $(x,x)$. We can thus build equalisers by pulling back
along the diagonal map:

~~~{.quiver}
\[\begin{tikzcd}
  {\rm{eq}(f,g)} && A \\
  \\
  B && {B \times B}
  \arrow["{\rm{equ}}", from=1-1, to=1-3]
  \arrow[from=1-1, to=3-1]
  \arrow["{\langle f,g\rangle}", from=1-3, to=3-3]
  \arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=1-1, to=3-3]
  \arrow["{\langle \id, \id\rangle}"', from=3-1, to=3-3]
\end{tikzcd}\]
~~~

```agda
  product+pullback→equaliser
    : ∀ {E X Y Y²}
    → {f g : Hom X Y} {e : Hom E X} {π₁ π₂ : Hom Y² Y} {p₁ : Hom E Y}
    → (is-prod : is-product C π₁ π₂) (let open is-product is-prod)
    → (is-pb : is-pullback C p₁ ⟨ id , id ⟩ e ⟨ f , g ⟩)
    → is-equaliser C f g e
  product+pullback→equaliser {f = f} {g} {e} {π₁} {π₂} {p₁} is-prod is-pb = is-eq where
    open is-product is-prod renaming (unique₂ to ⟨⟩-unique₂)
    open is-pullback is-pb renaming (unique to pb-unique)
```

The actual equaliser map is the top, horizontal face (what the code
calls `e`, so we must show that, composed with this map, $f$
and $g$ become equal. Here's where we use the fact that pullback
squares, well, commute: We know that $f$ is $\pi_1 \circ \langle f , g
\rangle$, and that $\langle f , g \rangle \circ \rm{equ} = \langle
\id, \id \rangle$ (since the square above is a pullback).

But both projections out of $\langle \id, \id \rangle$
are equal, so we can apply commutativity of the square above _again_ to
conclude that $f \circ \rm{equ} = g \circ \rm{equ}$.


```agda
    is-eq : is-equaliser C f g e
    is-eq .is-equaliser.equal =
      f ∘ e                 ≡˘⟨ pulll π₁∘⟨⟩ ⟩
      π₁ ∘ ⟨ f , g ⟩ ∘ e    ≡˘⟨ ap₂ _∘_ refl square ⟩
      π₁ ∘ ⟨ id , id ⟩ ∘ p₁ ≡⟨ extendl (π₁∘⟨⟩ ∙ sym (π₂∘⟨⟩)) ⟩
      π₂ ∘ ⟨ id , id ⟩ ∘ p₁ ≡⟨ ap₂ _∘_ refl square ⟩
      π₂ ∘ ⟨ f , g ⟩ ∘ e    ≡⟨ pulll π₂∘⟨⟩ ⟩
      g ∘ e ∎
```

We must now show that if $e'$ is another map which equalises $f$ and
$g$, then it fits into a commutative diagram like the one below, so that
we may conclude the dashed arrow $E' \to \rm{eq}(f,g)$ exists and is
unique.

~~~{.quiver}
\[\begin{tikzcd}
  {E'} \\
  & {\rm{eq}(f,g)} && A \\
  \\
  & B && {B \times B}
  \arrow["{\rm{equ}}", from=2-2, to=2-4]
  \arrow["{\langle f, g \rangle}", from=2-4, to=4-4]
  \arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=2-2, to=4-4]
  \arrow[from=2-2, to=4-2]
  \arrow["{\langle \id, \id \rangle}"', from=4-2, to=4-4]
  \arrow["{e'}", curve={height=-6pt}, from=1-1, to=2-4]
  \arrow["{\exists!}"', dashed, from=1-1, to=2-2]
\end{tikzcd}\]
~~~

A bit of boring limit-chasing lets us conclude that this diagram _does_
commute, hence the dashed arrow _does_ exist (uniquely!), so that the
top face $\rm{equ} : \rm{eq}(f,g) \to A$ in our pullback diagram
is indeed the equaliser of $f$ and $g$.

```agda
    is-eq .is-equaliser.universal {e' = e'} p =
      universal {p₁' = f ∘ e'} {p₂' = e'} comm
      where abstract
        comm : ⟨ id , id ⟩ ∘ f ∘ e' ≡ (⟨ f , g ⟩ ∘ e')
        comm =
          ⟨⟩-unique₂
            (cancell π₁∘⟨⟩) (cancell π₂∘⟨⟩)
            (pulll π₁∘⟨⟩) (pulll π₂∘⟨⟩ ∙ sym p)
    is-eq .is-equaliser.factors = p₂∘universal
    is-eq .is-equaliser.unique {e' = e'} {p = p} {other = other} e∘other=e' =
      pb-unique
        p₁∘other=f∘e'
        e∘other=e'
      where
        p₁∘other=f∘e' : p₁ ∘ other ≡ f ∘ e'
        p₁∘other=f∘e' =
          p₁ ∘ other                    ≡⟨ insertl π₁∘⟨⟩ ⟩
          π₁ ∘ ⟨ id , id ⟩ ∘ p₁ ∘ other ≡⟨ ap₂ _∘_ refl (extendl square) ⟩
          π₁ ∘ ⟨ f , g ⟩ ∘ e ∘ other    ≡⟨ pulll π₁∘⟨⟩ ⟩
          f ∘ e ∘ other                 ≡⟨ ap₂ _∘_ refl e∘other=e' ⟩
          f ∘ e' ∎
```


<!--
```agda
  terminal+pullbacks→products
    : Terminal C
    → Pullbacks C
    → Binary-products C
  terminal+pullbacks→products top pullbacks =
    to-binary-products λ A B → record {
       has-is-product = terminal+pullback→product {f = !} {g = !} has⊤ has-is-pb
    }
    where
      open Terminal top
      open Pullbacks pullbacks

  products+pullbacks→equalisers
    : Binary-products C
    → Pullbacks C
    → Equalisers C
  products+pullbacks→equalisers products pullbacks =
    to-equalisers λ f g → record {
      has-is-eq = product+pullback→equaliser has-is-product has-is-pb
    }
    where
      open Binary-products products
      open Pullbacks pullbacks
```
-->

Putting it all together into a record we get our proof of finite completeness:

```agda
  with-pullbacks
    : Terminal C
    → Pullbacks C
    → Finitely-complete
  with-pullbacks top pbs = fc where
    prods : Binary-products C
    prods = terminal+pullbacks→products top pbs

    fc : Finitely-complete
    fc .terminal = top
    fc .products = prods
    fc .equalisers = products+pullbacks→equalisers prods pbs
    fc .pullbacks = pbs
```

-- <!--
```agda
  product→terminal-pullback
    : ∀ {P X Y T} {p1 : Hom P X} {p2 : Hom P Y} {f : Hom X T} {g : Hom Y T}
    → is-terminal C T → is-product C p1 p2 → is-pullback C p1 f p2 g
  product→terminal-pullback t r = pb where
    open is-pullback
    pb : is-pullback C _ _ _ _
    pb .square = is-contr→is-prop (t _) _ _
    pb .universal _ = r .is-product.⟨_,_⟩ _ _
    pb .p₁∘universal = r .is-product.π₁∘⟨⟩
    pb .p₂∘universal = r .is-product.π₂∘⟨⟩
    pb .unique p q = r .is-product.unique p q

  is-complete→finitely
    : ∀ {a b} → is-complete a b C → Finitely-complete
  is-complete→finitely {a} {b} compl = with-pullbacks term' pb
    where
      pb : Pullbacks C
      pb = to-pullbacks λ f g →
        Limit→Pullback C (compl (cospan→cospan-diagram _ _ f g))

      idx : Precategory a b
      idx = Lift-cat a b (Disc ⊥ λ x → absurd x)

      F : Functor idx C
      F .Functor.F₀ ()
      F .Functor.F₁ {()}
      F .Functor.F-id {()}
      F .Functor.F-∘ {()}

      limF : Limit F
      limF = compl F
      open Terminal
      open Cone-hom
      open Cone

      term' : Terminal C
      term' = record { top = Limit.apex limF ; has⊤ = limiting } where
        limiting : ∀ x → is-contr _
        limiting x =
          contr (Limit.universal limF (λ { () }) (λ { {()} })) λ h →
            sym (Limit.unique limF _ _ h λ { () })
```
-->

# Lex functors {defines="left-exact-functor lex-functor"}

A functor is said to be **left exact**, abbreviated **lex**, when it
preserves finite limits. These functors aren't called
"finite-limit-preserving functors" by historical accident, and for
brevity. By the characterisations above, it suffices for a functor to
preserve the terminal object and pullbacks.

<!--
```agda
module _ {o ℓ o' ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'} where
  private module C = Cat C
  private module D = Cat D
```
-->

```agda
  record is-lex (F : Functor C D) : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ') where
    private module F = Functor F

    field
      pres-⊤ : ∀ {T} → is-terminal C T → is-terminal D (F.₀ T)
      pres-pullback
        : ∀ {P X Y Z} {p1 : C.Hom P X} {p2 : C.Hom P Y}
            {f : C.Hom X Z} {g : C.Hom Y Z}
        → is-pullback C p1 f p2 g
        → is-pullback D (F.₁ p1) (F.₁ f) (F.₁ p2) (F.₁ g)
```

Since (if a terminal object exists), products $A \times B$ can be
identified with pullbacks $A \times_\top B$, if $\cC$ has a terminal
object, then a lex functor $F : \cC \to \cD$ also preserves
products.

```agda
    pres-product
      : ∀ {P A B T} {p1 : C.Hom P A} {p2 : C.Hom P B}
      → is-terminal C T
      → is-product C p1 p2
      → is-product D (F.₁ p1) (F.₁ p2)
    pres-product term pr = terminal+pullback→product D (pres-⊤ term)
      (pres-pullback {f = term _ .centre} {g = term _ .centre}
        (product→terminal-pullback C term pr))
```

Since $f : A \to B$ being a monomorphism is equivalent to certain squares
being pullbacks, a lex functor $F : \cC \to \cD$ preserves monomorphisms.

```agda
    pres-monos : ∀ {A B} {f : C.Hom A B} → C.is-monic f → D.is-monic (F.₁ f)
    pres-monos {f = f} mono = is-pullback→is-monic
      (subst (λ x → is-pullback D x _ x _) F.F-id
        (pres-pullback
          (is-monic→is-pullback mono)))
```

<!--
```agda
module _ {o ℓ o' ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'} where
  open is-lex

  F∘-is-lex
    : ∀ {o'' ℓ''} {E : Precategory o'' ℓ''}
        {F : Functor D E} {G : Functor C D}
    → is-lex F → is-lex G → is-lex (F F∘ G)
  F∘-is-lex f g .pres-⊤ = f .pres-⊤ ⊙ g .pres-⊤
  F∘-is-lex f g .pres-pullback = f .pres-pullback ⊙ g .pres-pullback
```
-->
