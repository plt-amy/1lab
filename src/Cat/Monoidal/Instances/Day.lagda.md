<!--
```agda
open import Cat.Diagram.Coend.Sets
open import Cat.Functor.Naturality
open import Cat.Instances.Product
open import Cat.Diagram.Coend
open import Cat.Monoidal.Base
open import Cat.Functor.Base
open import Cat.Functor.Hom
open import Cat.Prelude

import Cat.Functor.Reasoning as Fr
import Cat.Reasoning as Cat
```
-->

```agda
module Cat.Monoidal.Instances.Day
  {ℓ} {C : Precategory ℓ ℓ} (cmon : Monoidal-category C)
  where
```

<!--
```agda
open Monoidal-category cmon

open make-natural-iso
open Cowedge
open Functor
open Cat C
open _=>_
```
-->

# The Day convolution product

The **Day convolution** $F \otimes^D G$ [[monoidal structure|monoidal
category]] on $\psh(\cC)$ is the [[free cocompletion]] of a small
monoidal category $\cC$ *within the context of monoidal categories*: its
**monoidal cocompletion**. This uniquely determines the construction of
$\otimes^D$, which is perhaps sufficient motivation to a category
theorist. However, it's worth pointing out that the Day convolution
comes up in practice *surprisingly often*, so that the motivation for
this page does not rest entirely on abstract nonsense. Here are a few
examples, before we get started:

- **Automata theory**: If we have a [[set]] $\Sigma$, which we call the
  *alphabet*, then, as usual, we call a subset $S \sube \List{\Sigma}$ a
  *language* on $\Sigma$. Languages are closed under the generic
  operations of intersection and union of subsets, but we also have an
  operation specific to this domain: *concatenation*, which arises from
  the free [[monoid]] structure on $\List{\Sigma}$.

  More concretely, the concatenation $LM$ is the subset which,
  expressed as a predicate, has value

  $$
  (L \cdot M)(x) = \exists l,\ \exists m,\ (x = l \cdot m) \land L(l) \land M(m)
  $$.

  That is, the words belonging to $L_1 \cdot L_2$ are precisely those
  which decompose as a concatenation of a word from $L_1$ followed by a
  word from $L_2$. The operation of concatenation *preserves [[joins]]
  in each variable*: We can calculate

  $$
  \begin{align*}
  (\textstyle\bigcup_{i}L_i \cdot M)(x)
    & = \exists l,\ \exists m,\ (\exists i,\ L_i(l)) \land M(m) \land (x = l \cdot m) \\
    & = \exists l,\ \exists m,\ \exists i,\ L_i(l) \land M(m) \land (x = l \cdot m) \\
    & = \exists i,\ \exists l,\ \exists m,\ L_i(l) \land M(m) \land (x = l \cdot m) \\
    & = (\textstyle\bigcup_{i} (L_i \cdot M))(x)\text{,}
  \end{align*}
  $$

  and the other variable is symmetric. To give a concrete example, we
  can define the *Kleene star* $A^* = \bigcup_{n : \bN} A^n$, where
  $A^n$ denotes the $n$-fold composition. Then our cocontinuity result
  says that we can compute concatenation with a star as a union of
  simpler concatenations. For example, an enumeration of $x^*y$ starts

  $$
  y, xy, xxy, xxxy, xxxxy, \dots
  $$

* **Algebra**: if we have a [[group]] $G$ and a [[ring]] $R$, there is a
  universal way to equip the [[free module]] $R[G]$ with a multiplication
  that makes it into a ring, and where this multiplication is also
  $R$-linear in each variable: the **group $R$-algebra**, which we also
  refer to as $R[G]$. For simplicity, let us assume that $G$ is a finite
  group.

  Note that, since $G$ is finite, we can take the elements of $R[G]$ to
  simply be arbitrary functions $f : G \to R$. If we think of $r : R[G]$
  as a polynomial, then we associate to it the function that sends each
  $g : G$ to the element $r_g : R$ which appears as its coefficient. In
  the other direction, an assignment of coefficients determines the
  polynomial $\sum_{g : G} f(g) g$.

  The multiplication on $R[G]$ is determined uniquely by the requirement
  that it extends the multiplication on $G$ in an $R$-linear way: for
  polynomials $r, s$, we should have

  $$
  \left(\sum_{g : G} r(g) g\right)\left(\sum_{g' : G} s(g) g'\right)
    = \sum_{g : G} \sum_{g' : G} r(g)s(g') gg'
  $$

  It is not immediately obvious that we can rewrite this double
  summation in "coefficient form". But if we recall the diagonal
  function $\delta(g, g') : G \times G \to R$, defined so that
  $\delta(x, y) = 1$ if $x = y$ (and $0$ otherwise), then we can express
  this as

  $$
  \sum_{h : G} \left(\sum_{g : G} \sum_{g' : G} r(g)s(g') \delta(h, gg')\right) h
  $$

  since, intuitively, we have $\sum_{h : G} A\delta(h, gg')h$ = $Agg'$,
  since, for each value of $h$, if we do not have $h = gg'$, then the
  summand is equal to zero.

Drawing a generalisation from the cases above, we can equip the
collection of functions $X \to Y$ with a monoid structure whenever $X$
and $Y$ are monoids, and $Y$ admits an operation for _aggregation over
$x : X$_, to play the role of the existential quantifier and summation.
Writing $\int^x f(x)$ for this aggregation operation, the product $f
\star g$ is given pointwise by

$$
(f \star g)(x) = \int^{x_1, x_2} (x = x_1 \cdot x_2) \diamond f(x_1) \diamond g(x_2)
$$.

This operation is generally referred to as the **convolution product**
of $f$ and $g$, and it can be seen as the special case of the Day
convolution where the domain is a discrete category.

<details>
<summary>
For those curious but unfamiliar with the abstract nonsense, we should
explain what, exactly, is meant by *monoidal cocompletion*: in addition
to showing that $\psh(\cC)$ is cocomplete, and equipping it with a
monoidal structure $F \otimes^D G$, we must show that these behave
nicely together:
</summary>

- The tensor product we construct must be *[[cocontinuous]] in each variable*;

- Our chosen cocompletion $\cC \to \psh(\cC)$, which in this case is the
  [[Yoneda embedding]] $\yo$, must be a strong monoidal functor: We
  should have $\yo(x \times y) \cong \yo(x) \times^D \yo(y)$.^[This is
  actually a slight under-approximation of strong monoidal functors: the
  unit must also be preserved, of course, and the preservation
  isomorphisms need to be compatible with the structural morphisms ---
  the unitors and associator.]

As usual when we have an object defined by a universal property, the Day
convolution monoidal structure is *unique*: making this particular case
explicit, given any other monoidal cocompletion $(\cC,\otimes) \to
(\hat{\cC},\hat{\otimes})$, we have a *unique* [[equivalence of monoidal
categories|equivalence of categories]] $(\hat{\cC},\hat{\otimes}) \cong
(\psh(\cC),\otimes^D)$. Among the [[*univalent* monoidal
categories|univalent category]], we may sharpen this result to saying
that $(\cC, \otimes)$ has a [[contractible space|contractible]] of
monoidal cocompletions.

</details>

## The construction

We will interpret the formula above literally, relying on the fact that
[[coends]] are also written with an integral sign. To generalise away
from a discrete domain, we must express the idea of decomposing an
object into parts without the use of equality. An obvious idea would be
isomorphism, but this turns out to be too strong: we can simply take the
product with the $\hom$-set into the product:

$$
(F \otimes^D G)(x) = \int^{c_1, c_2 : \cC} \hom_{\cC}(c, c_1 \otimes c_2) \times X(c_1) \times Y(c_2)
$$

::: warning
It's worth taking a second to read the formalised definition, below, if
you are unfamiliar with coends. We must express the "integrand" as a
functor $(C \times C)\op \times C \times C$. This provides us with
"polarised" versions of the variables $c_1, c_2$, which we write
$c_1^-/c_1^+$ and $c_2^-/c_2^+$.

We then distribute these variables according to the polarities of each
functor. Since $\hom$ is covariant in its second argument, it sees
$c_1^+ \otimes c_2^+$; but the presheaves are contravariant, so we have
factors $X(c_1^-)$ and $Y(c_2^-)$.
:::

```agda
module Day (X Y : ⌞ PSh ℓ C ⌟) where
  Day-diagram : Ob → Functor ((C ×ᶜ C) ^op ×ᶜ (C ×ᶜ C)) (Sets ℓ)
  ∣ Day-diagram c .F₀ ((c₁⁻ , c₂⁻) , c₁⁺ , c₂⁺) ∣ = Hom c (c₁⁺ ⊗ c₂⁺) × (X ʻ c₁⁻) × (Y ʻ c₂⁻)
```

<!--
```agda
  Day-diagram c .F₀ ((c₁⁻ , c₂⁻) , c₁⁺ , c₂⁺) .is-tr =
    ×-is-hlevel 2 (Hom-set _ _) (×-is-hlevel 2 (X .F₀ _ .is-tr) (Y .F₀ _ .is-tr))

  Day-diagram c .F₁ ((f⁻ , g⁻) , f⁺ , g⁺) (h , x , y) = (f⁺ ⊗₁ g⁺) ∘ h , X .F₁ f⁻ x , Y .F₁ g⁻ y

  Day-diagram c .F-id    = ext λ h x y → eliml (-⊗- .F-id) , X .F-id #ₚ x , Y .F-id #ₚ y
  Day-diagram c .F-∘ f g = ext λ h x y → pushl (-⊗- .F-∘ _ _) , X .F-∘ _ _ #ₚ _ , Y .F-∘ _ _ #ₚ _
```
-->

```agda
  opaque
    Day-coend : (c : Ob) → Coend (Day-diagram c)
    Day-coend c = Set-coend (Day-diagram c)
```

<!--
```agda
  private module Day c = Coend (Day-coend c)
  open Day using (nadir) public

  opaque
    unfolding Day-coend
```
-->

We shall now repeat some of our knowledge about [[coends valued in
sets|coends in sets]], but specialised to the case of the Day
convolution. First, we note that we can write the elements of the coend
(at $i : \cC$) as triples $\day{h, x, y}$, where $h : \hom(i, a \otimes
b)$, $x : X(a)$, and $y : Y(b)$.

```agda
    day : {i a b : Ob} (h : Hom i (a ⊗ b)) (x : X ʻ a) (y : Y ʻ b) → Day.nadir ʻ i
    day h x y = inc ((_ , _) , h , x , y)
```

<!--
```agda
    day-ap
      : {i a b : Ob} {h h' : Hom i (a ⊗ b)} {x x' : X ʻ a} {y y' : Y ʻ b}
      → h ≡ h' → x ≡ x' → y ≡ y' → day h x y ≡ day h' x' y'
    day-ap {a = a} {b} p q r i = inc ((a , b) , p i , q i , r i)

    day-apₘ : ∀ {i a b} {h h' : Hom i (a ⊗ b)} {x y} → h ≡ h' → day h x y ≡ day h' x y
    day-apₘ p = day-ap p refl refl
```
-->

Moreover, these triples have identifications generated by letting
$\day{(f \otimes g) \circ h, x , y}$ be $\day{h, Xf(x), Yf(y)}$,
whenever these both make sense. More generally, we have $\day{h, Xf(x),
Yg(y)}$ equal to $\day{h', Xf'(x), Yg'(y)}$ whenever $(f \otimes g)
\circ h = (f' \otimes g') \circ h'$.

```agda
    day-glue
      : {i a b a' b' : Ob} {f : Hom a' a} {g : Hom b' b} {h : Hom i (a' ⊗ b')} {x : X ʻ a} {y : Y ʻ b}
      → {fgh : Hom i (a ⊗ b)} (p : fgh ≡ (f ⊗₁ g) ∘ h)
      → day fgh x y ≡ day h (X .F₁ f x) (Y .F₁ g y)
    day-glue {i} {a} {b} {a'} {b'} {f} {g} {h} {x} {y} {fgh} p =
      day fgh x y                                  ≡⟨ day-ap p (sym (X .F-id) #ₚ x) (sym (Y .F-id) #ₚ y) ⟩
      day ((f ⊗₁ g) ∘ h) (X .F₁ id x) (Y .F₁ id y) ≡⟨ Coeq.glue {f = dimapl (Day-diagram i)} {g = dimapr (Day-diagram i)} ((a , b) , (a' , b') , (f , g) , h , x , y) ⟩
      day ((id ⊗₁ id) ∘ h) (X .F₁ f x) (Y .F₁ g y) ≡⟨ day-apₘ (eliml ⊗.F-id) ⟩
      day h (X .F₁ f x) (Y .F₁ g y)                ∎
```

Finally, we will use the formalism of [[cowedges]] to define functions
out of $(F \otimes^D G)(i)$. Essentially, this says that we can define a
function $f : (F \otimes^D G)(i) \to W$ whenever we can define
$f(\day{h,x,y})$, in a way compatible with the relation above.

```agda
    factor : ∀ {i} (W : Cowedge (Day-diagram i)) → Day.nadir ʻ i → ⌞ W .nadir ⌟
    factor W = Day.factor _ W
```

<!--
```agda
    factor-day
      : ∀ {i a b} {W : Cowedge (Day-diagram i)} {h : Hom i (a ⊗ b)} {x : X ʻ a} {y : Y ʻ b}
      → factor W (day h x y) ≡ W .ψ (a , b) (h , x , y)
    factor-day = refl

  {-# REWRITE factor-day #-}

  -- To have better type inference we define the Day-coend and its
  -- associated projections as opaque symbols. Agda will treat them as
  -- injective so e.g. an equation between `Day.nadir F G i = Day.nadir
  -- ? ? ?` will actually solve those three metas.
  --
  -- But, of course, opaque symbols don't compute, and we'd really
  -- really like to have `factor W (day h x y) = W .ψ h x y`. One
  -- approach would be to lift everything that needs this definitional
  -- equality into an opaque block, but that would massively bloat the
  -- file with mandatory type signatures.
  --
  -- Rewrite rules to the rescue: `factor-day` allows us to "export" the
  -- computation rule for `factor W (day ...)` without exposing the
  -- computational behaviour of any other of the symbols here.

  private
    extensional-work
      : ∀ {i ℓ' ℓr} {C : Type ℓ'} ⦃ _ : H-Level C 2 ⦄
      → ⦃ sf : ∀ {a b} → Extensional ((h : Hom i (a ⊗ b)) (x : X ʻ a) (y : Y ʻ b) → C) ℓr ⦄
      → Extensional (⌞ Day.nadir i ⌟ → C) (ℓ ⊔ ℓr)
    extensional-work {i} {C = C} ⦃ sf ⦄ = done where
      T : Type _
      T = {a b : Ob} (h : Hom i (a ⊗ b)) (x : X ʻ a) (y : Y ʻ b) → C

      unday : (⌞ Day.nadir i ⌟ → C) → T
      unday f h x y = f (day h x y)

      opaque
        unfolding Day-coend day

        -- Note: Extensional-day-map and Extensional-coeq-map well and
        -- truly overlap whenever Day.nadir is unfoldable (which it is
        -- in the definition of to-p). So we can't let to-p see
        -- Extensional-day-map as an instance.

        to-p : ∀ {f g} → Path T (unday f) (unday g) → f ≡ g
        to-p p = ext λ a b h x y i → p i {a} {b} h x y

      done : Extensional (⌞ Day.nadir i ⌟ → C) _
      done = injection→extensional (hlevel 2) to-p auto

  instance
    Extensional-day-map
      : ∀ {i ℓ' ℓr} {C : Type ℓ'} ⦃ _ : H-Level C 2 ⦄
      → ⦃ sf : ∀ {a b} → Extensional ((h : Hom i (a ⊗ b)) (x : X ʻ a) (y : Y ʻ b) → C) ℓr ⦄
      → Extensional (⌞ Day.nadir i ⌟ → C) (ℓ ⊔ ℓr)
    Extensional-day-map = extensional-work

  day-swap
    : ∀ {i a b a' b'} {f : Hom a' a} {g : Hom b' b} {h : Hom i (a' ⊗ b')}
        {a'' b''} {f' : Hom a'' a} {g' : Hom b'' b} {h' : Hom i (a'' ⊗ b'')}
        {x : X ʻ a} {y : Y ʻ b}
    → (f ⊗₁ g) ∘ h ≡ (f' ⊗₁ g') ∘ h'
    → day h (X .F₁ f x) (Y .F₁ g y) ≡ day h' (X .F₁ f' x) (Y .F₁ g' y)
  day-swap p = sym (day-glue refl) ·· day-apₘ p ·· day-glue refl
```
-->

As an example of constructing a map using cowedges, we can construct the
restriction $(F \otimes^D G)(x) \to (F \otimes^D G)(y)$, given $h :
\hom(y, x)$. Pointwise, this sends $\day{f, x, y}$ to $\day{f \circ h,
x, y}$. It's a straightforward-but-annoying calculation to show that
this extends to the quotient.

```agda
  Day-cowedge : ∀ {x} {y} → Hom y x → Cowedge (Day-diagram x)
  Day-cowedge {y = y} h .nadir = Day.nadir y
  Day-cowedge h .ψ (a , b) (f , x , y) = day (f ∘ h) x y
  Day-cowedge h .extranatural {a , b} {a' , b'} (f , g) = funext λ (i , x , y) →
    day (((f ⊗₁ g) ∘ i) ∘ h) (X .F₁ id x) (Y .F₁ id y) ≡⟨ day-ap refl (X .F-id #ₚ x) (Y .F-id #ₚ y) ⟩
    day (((f ⊗₁ g) ∘ i) ∘ h) x y                       ≡⟨ day-glue (sym (assoc _ _ _)) ⟩
    day (i ∘ h) (X .F₁ f x) (Y .F₁ g y)                ≡⟨ day-apₘ (introl ⊗.F-id ∙ assoc _ _ _) ⟩
    day (((id ⊗₁ id) ∘ i) ∘ h) (X .F₁ f x) (Y .F₁ g y) ∎

  _⊗ᴰ_ : ⌞ PSh ℓ C ⌟
  _⊗ᴰ_ .F₀ c = Day.nadir c
  _⊗ᴰ_ .F₁ {x} {y} h v = factor (Day-cowedge h) v
  _⊗ᴰ_ .F-id    = ext λ h x y → day-apₘ (idr h)
  _⊗ᴰ_ .F-∘ f g = ext λ h x y → day-apₘ (assoc h g f)
```

<!--
```agda
  infix 25 _⊗ᴰ_

module _ {X Y} where
  open Day X Y
    using    (day ; day-ap ; day-apₘ ; day-swap ; Extensional-day-map ; day-glue)
    renaming (factor to Day-rec)
    public

open Day using (_⊗ᴰ_ ; Day-diagram)
```
-->

<details>
<summary>
Together with some quick functoriality proofs, we have shown above that
the Day convolution is a presheaf. If we have natural transformations $X
\to X'$ and $Y \to Y'$, then we can extend these to a $X \otimes^D Y \to
X' \otimes^D Y'$, so that we actually have a functor $\psh(\cC) \times
\psh(\cC) \to \psh(\cC)$. This is but another annoying calculation.
</summary>

```agda
Day-bifunctor-cowedge
  : ∀ {X Y X' Y' : ⌞ PSh ℓ C ⌟} {i}
  → X => X'
  → Y => Y'
  → Cowedge (Day-diagram X Y i)
Day-bifunctor-cowedge {X} {Y} {X'} {Y'} {i} F G = go where
  private module D = Day X' Y'
  go : Cowedge (Day-diagram X Y i)
  go .nadir           = D.nadir i
  go .ψ c (h , x , y) = D.day h (F .η _ x) (G .η _ y)
  go .extranatural (f , g) = ext λ h x y →
    D.day ((f ⊗₁ g) ∘ h)   (F .η _ (X .F₁ id x))   (G .η _ (Y .F₁ id y))   ≡⟨ D.day-ap refl (F .is-natural _ _ id #ₚ _) (G .is-natural _ _ id #ₚ _) ⟩
    D.day ((f ⊗₁ g) ∘ h)   (X' .F₁ id (F .η _ x))  (Y' .F₁ id (G .η _ y))  ≡⟨ D.day-swap (extendl (eliml ⊗.F-id ∙ intror ⊗.F-id)) ⟩
    D.day ((id ⊗₁ id) ∘ h) (X' .F₁ f (F .η _ x))   (Y' .F₁ g (G .η _ y))   ≡˘⟨ D.day-ap refl (F .is-natural _ _ f #ₚ _) (G .is-natural _ _ g #ₚ _) ⟩
    D.day ((id ⊗₁ id) ∘ h) (F .η _ (X .F₁ f x))    (G .η _ (Y .F₁ g y))    ∎

Day-map : ∀ {X X' Y Y'} (F : X => X') (G : Y => Y') → X ⊗ᴰ Y => X' ⊗ᴰ Y'
Day-map F G .η i = Day-rec (Day-bifunctor-cowedge F G)
Day-map F G .is-natural x y f = trivial!

Day-bifunctor : Functor (PSh ℓ C ×ᶜ PSh ℓ C) (PSh ℓ C)
Day-bifunctor .F₀ (X , Y) = X ⊗ᴰ Y
Day-bifunctor .F₁ (F , G) = Day-map F G
Day-bifunctor .F-id    = trivial!
Day-bifunctor .F-∘ f g = trivial!
```

</details>

## The monoidal structure

The rest of this module is devoted to showing that the Day convolution
is actually a monoidal structure: that is, we have unitors and an
associator, which satisfy the triangle and pentagon identities. We will
give an overview of the constructor of the right unitor, $\rho : X
\otimes^D \yo(I) \cong X$; It's a representative example of the nasty
calculations to come.

Fixing a presheaf $X$ and coordinate $c : \cC$, we want to show that

$$
\int^{c_1, c_2 : \cC} \hom(c, c_1 \otimes c_2) \times X(c_1) \times \hom(c_2, I)
$$

is isomorphic to $X$. Were we not working in a proof assistant, we could
do this by coend calculus: it's an instance of the Yoneda lemma.
However, it will be much easier in the long run to bang out an explicit
isomorphism. At the level of points, we are given $h : \hom(c, c_1
\otimes c_2)$, $y : \hom(c_2, I)$, and $x : X(c_1)$. We must produce an
element of $X(c)$. The composite

$$
c \xto{h} c_1 \otimes c_2 \xto{\id \otimes y} c_1 \otimes I \xto{\rho} c_1
$$

acts on $x : X$ to give us precisely the element we want. In the other
direction, we can send $x : X(c)$ to $\day{\rho\inv, x, \id}$. We can
then perform the extremely annoying calculations to show that (a) this
map extends to the coend, (b) the resulting map is a natural
transformation, and (c) the inverse construction we sketched is actually
an inverse.

```agda
module _ (X : ⌞ PSh ℓ C ⌟) where
  idr-to-cowedge : ∀ x → Cowedge (Day-diagram X (よ₀ C Unit) x)
  idr-to-cowedge i .nadir = X # i
  idr-to-cowedge i .ψ (a , b) (h , x , y) = X .F₁ (ρ← ∘ (id ⊗₁ y) ∘ h) x
  idr-to-cowedge i .extranatural {a , b} {a' , b'} (f , g) = ext λ h x y →
    X .F₁ (ρ← ∘ (id ⊗₁ y ∘ id) ∘ (f ⊗₁ g) ∘ h) (X .F₁ id x) ≡⟨ ap₂ (X .F₁) (ap (ρ← ∘_) (⊗.pulll (ap₂ _,_ (idl f) (ap (_∘ g) (idr y))))) refl ⟩
    X .F₁ (ρ← ∘ (f ⊗₁ y ∘ g) ∘ h) (X .F₁ id x)              ≡⟨ ap₂ (X .F₁) (ap (ρ← ∘_) (⊗.pushl (ap₂ _,_ (intror refl) (introl refl)))) refl ⟩
    X .F₁ (ρ← ∘ (f ⊗₁ id) ∘ (id ⊗₁ y ∘ g) ∘ h) (X .F₁ id x) ≡⟨ ap₂ (X .F₁) (extendl (unitor-r .Isoⁿ.from .is-natural a a' f)) refl ⟩
    X .F₁ (f ∘ ρ← ∘ (id ⊗₁ y ∘ g) ∘ h) (X .F₁ id x)         ≡⟨ X .F-∘ _ _ #ₚ _ ⟩
    X .F₁ (ρ← ∘ (id ⊗₁ y ∘ g) ∘ h) (X .F₁ f (X .F₁ id x))   ≡⟨ ap₂ (X .F₁) (ap (ρ← ∘_) (ap₂ _∘_ refl (introl ⊗.F-id))) (ap (X .F₁ f) (X .F-id #ₚ x)) ⟩
    X .F₁ (ρ← ∘ (id ⊗₁ y ∘ g) ∘ (id ⊗₁ id) ∘ h) (X .F₁ f x) ∎

  Day-idr : X ⊗ᴰ よ₀ C Unit ≅ⁿ X
  Day-idr = to-natural-iso mk-idr where
    mk-idr : make-natural-iso (X ⊗ᴰ よ₀ C Unit) X
    mk-idr .eta x   = Day-rec (idr-to-cowedge x)
    mk-idr .inv x a = day ρ→ a id
    mk-idr .eta∘inv x = ext λ a → ap₂ (X .F₁) (ap (ρ← ∘_) (eliml ⊗.F-id) ∙ unitor-r .Isoⁿ.invr ηₚ _) refl ∙ (X .F-id #ₚ a)
    mk-idr .inv∘eta i = ext λ h x y →
      day ρ→ (X .F₁ (ρ← ∘ (id ⊗₁ y) ∘ h) x) id          ≡⟨ day-ap refl refl (introl refl) ⟩
      day ρ→ (X .F₁ (ρ← ∘ (id ⊗₁ y) ∘ h) x) (id ∘ id)   ≡⟨ day-swap (sym (unitor-r .Isoⁿ.to .is-natural _ _ _) ∙ cancell (unitor-r .Isoⁿ.invl ηₚ _)) ⟩
      day h (X .F₁ id x) (id ∘ y)                       ≡⟨ day-ap refl (X .F-id #ₚ x) (idl y) ⟩
      day h x y                                         ∎
    mk-idr .natural x y f = ext λ h x y →
      X .F₁ f (X .F₁ (ρ← ∘ (id ⊗₁ y) ∘ h) x) ≡⟨ sym (X .F-∘ _ _) #ₚ _ ⟩
      X .F₁ ((ρ← ∘ (id ⊗₁ y) ∘ h) ∘ f) x     ≡⟨ ap₂ (X .F₁) (pullr (pullr refl)) refl ⟩
      X .F₁ (ρ← ∘ (id ⊗₁ y) ∘ h ∘ f) x       ∎
```

This completes the construction of the right unitor. It also completes the
commentary on this module: the construction of the left unitor,
$\lambda$, is analogous: just flip everything. The construction of the
associator must be done in steps. However, at the level of points, these
are all trivial operations, and the vast majority of this module is
dedicated to (extra)naturality conditions and proofs of isomorphy.

```agda
module _ (Y : ⌞ PSh ℓ C ⌟) where
  idl-to-cowedge : ∀ x → Cowedge (Day-diagram (よ₀ C Unit) Y x)
  idl-to-cowedge i .nadir = Y # i
  idl-to-cowedge i .ψ (a , b) (h , x , y) = Y .F₁ (λ← ∘ (x ⊗₁ id) ∘ h) y
  idl-to-cowedge i .extranatural {a , b} {a' , b'} (f , g) = ext λ h x y →
       ap₂ (Y .F₁) (ap (λ← ∘_) (⊗.extendl (ap₂ _,_ (ap (_∘ f) (idr x) ∙ introl refl) id-comm-sym)) ∙ extendl (unitor-l .Isoⁿ.from .is-natural _ _ _)) (Y .F-id #ₚ y)
    ·· (Y .F-∘ _ _ #ₚ y)
    ·· ap₂ (Y .F₁) (ap (λ← ∘_) (ap₂ _∘_ refl (introl ⊗.F-id))) refl

  Day-idl : よ₀ C Unit ⊗ᴰ Y ≅ⁿ Y
  Day-idl = to-natural-iso mk-idl where
    mk-idl : make-natural-iso (よ₀ C Unit ⊗ᴰ Y) Y
    mk-idl .eta x = Day-rec (idl-to-cowedge x)
    mk-idl .inv x a = day λ→ id a
    mk-idl .eta∘inv x = ext λ a → ap₂ (Y .F₁) (ap (λ← ∘_) (eliml ⊗.F-id) ∙ unitor-l .Isoⁿ.invr ηₚ _) refl ∙ (Y .F-id #ₚ a)
    mk-idl .inv∘eta i = ext λ h x y →
      day λ→ id (Y .F₁ (λ← ∘ (x ⊗₁ id) ∘ h) y)        ≡⟨ day-ap refl (introl refl) refl ⟩
      day λ→ (id ∘ id) (Y .F₁ (λ← ∘ (x ⊗₁ id) ∘ h) y) ≡⟨ day-swap (sym (unitor-l .Isoⁿ.to .is-natural _ _ _) ∙ cancell (unitor-l .Isoⁿ.invl ηₚ _)) ⟩
      day h (id ∘ x) (Y .F₁ id y)                     ≡⟨ day-ap refl (idl x) (Y .F-id #ₚ y) ⟩
      day h x y                                       ∎
    mk-idl .natural = λ x y f → ext λ h x y →
      Y .F₁ f (Y .F₁ (λ← ∘ (x ⊗₁ id) ∘ h) y) ≡˘⟨ Y .F-∘ _ _ #ₚ _ ⟩
      Y .F₁ ((λ← ∘ (x ⊗₁ id) ∘ h) ∘ f) y     ≡⟨ ap₂ (Y .F₁) (pullr (pullr refl)) refl ⟩
      Y .F₁ (λ← ∘ (x ⊗₁ id) ∘ h ∘ f) y       ∎

module _ (X Y Z : ⌞ PSh ℓ C ⌟) where
  assoc-to₀ : ∀ i {a b} (h : Hom i (a ⊗ b)) (z : Z ʻ b) → Cowedge (Day-diagram X Y a)
  assoc-to₀ i h z .nadir = Day.nadir X (Y ⊗ᴰ Z) i
  assoc-to₀ i h z .ψ (a' , b') (h' , x , y) = day (α→ _ _ _ ∘ (h' ⊗₁ id) ∘ h) x (day id y z)
  assoc-to₀ i h z .extranatural (f , g) = ext λ h' x y →
    day (α→ _ _ _ ∘ ((f ⊗₁ g) ∘ h' ⊗₁ id) ∘ h) (X .F₁ id x) (day id (Y .F₁ id y) z)  ≡⟨ day-ap (ap (α→ _ _ _ ∘_) (⊗.pushl (ap₂ _,_ refl (introl refl)))) (X .F-id #ₚ x) (day-ap refl (Y .F-id #ₚ y) refl) ⟩
    day (α→ _ _ _ ∘ ((f ⊗₁ g) ⊗₁ id) ∘ (h' ⊗₁ id) ∘ h) x (day id y z)                ≡⟨ day-apₘ (extendl (associator .Isoⁿ.to .is-natural _ _ _)) ⟩
    day ((f ⊗₁ (g ⊗₁ id)) ∘ α→ _ _ _ ∘ (h' ⊗₁ id) ∘ h) x (day id y z)                ≡⟨ day-glue refl ⟩
    day (α→ _ _ _ ∘ (h' ⊗₁ id) ∘ h) (X .F₁ f x) (day (id ∘ (g ⊗₁ id)) y z)           ≡⟨ day-ap (ap (α→ _ _ _ ∘_) (ap (_∘ h) (ap₂ _⊗₁_ (introl ⊗.F-id) refl))) refl (day-apₘ id-comm-sym ·· day-glue refl ·· day-ap refl refl (Z .F-id #ₚ z)) ⟩
    day (α→ _ _ _ ∘ ((id ⊗₁ id) ∘ h' ⊗₁ id) ∘ h) (X .F₁ f x) (day id (Y .F₁ g y) z)  ∎

  assoc-to-cowedge : ∀ i → Cowedge (Day-diagram (X ⊗ᴰ Y) Z i)
  assoc-to-cowedge i .nadir = Day.nadir X (Y ⊗ᴰ Z) i
  assoc-to-cowedge i .ψ (a , b) (h , x , y) = Day-rec (assoc-to₀ i h y) x
  assoc-to-cowedge i .extranatural (f , g) = ext λ h h' x y z →
    day (α→ _ _ _ ∘ (h' ∘ id ⊗₁ id) ∘ (f ⊗₁ g) ∘ h) x (day id y (Z .F₁ id z))   ≡⟨ day-ap (ap (α→ _ _ _ ∘_) (⊗.extendl (ap₂ _,_ (ap (_∘ f) (idr h') ∙ introl ⊗.F-id) id-comm-sym))) refl (day-ap refl refl (Z .F-id #ₚ z)) ⟩
    day (α→ _ _ _ ∘ ((id ⊗₁ id) ⊗₁ g) ∘ (h' ∘ f ⊗₁ id) ∘ h) x (day id y z)      ≡⟨ day-apₘ (extendl (associator .Isoⁿ.to .is-natural _ _ _)) ⟩
    day ((id ⊗₁ (id ⊗₁ g)) ∘ α→ _ _ _ ∘ (h' ∘ f ⊗₁ id) ∘ h) x (day id y z)      ≡⟨ day-glue refl ⟩
    day (α→ _ _ _ ∘ (h' ∘ f ⊗₁ id) ∘ h) (X .F₁ id x) (day (id ∘ (id ⊗₁ g)) y z) ≡⟨ day-ap (ap (α→ _ _ _ ∘_) (ap₂ _∘_ refl (introl ⊗.F-id))) (X .F-id #ₚ x) (day-glue id-comm-sym ∙ day-ap refl (Y .F-id #ₚ y) refl) ⟩
    day (α→ _ _ _ ∘ (h' ∘ f ⊗₁ id) ∘ (id ⊗₁ id) ∘ h) x (day id y (Z .F₁ g z))   ∎

  assoc-from₀ : ∀ i {a b} (h : Hom i (a ⊗ b)) (x : X ʻ a) → Cowedge (Day-diagram Y Z b)
  assoc-from₀ i h x .nadir = Day.nadir (X ⊗ᴰ Y) Z i
  assoc-from₀ i h x .ψ (a' , b') (h' , y , z) = day (α← _ _ _ ∘ (id ⊗₁ h') ∘ h) (day id x y) z
  assoc-from₀ i h x .extranatural (f , g) = ext λ h' y z →
    day (α← _ _ _ ∘ (id ⊗₁ ((f ⊗₁ g) ∘ h')) ∘ h) (day id x (Y .F₁ id y)) (Z .F₁ id z) ≡⟨ day-ap (extendl (pushr (ap₂ _⊗₁_ (introl refl) refl ∙ ⊗.F-∘ _ _) ·· pullr refl ·· extendl (associator .Isoⁿ.from .is-natural _ _ _))) (day-ap refl refl (Y .F-id #ₚ y)) (Z .F-id #ₚ z) ⟩
    day (((id ⊗₁ f) ⊗₁ g) ∘ (α← _ _ _ ∘ (id ⊗₁ h')) ∘ h) (day id x y) z               ≡⟨ day-glue refl ⟩
    day ((α← _ _ _ ∘ (id ⊗₁ h')) ∘ h) (day (id ∘ (id ⊗₁ f)) x y) (Z .F₁ g z)          ≡⟨ day-ap (pullr (ap (_∘ h) (ap₂ _⊗₁_ refl (introl ⊗.F-id)))) (day-glue id-comm-sym ∙ day-ap refl (X .F-id #ₚ x) refl) refl ⟩
    day (α← _ _ _ ∘ (id ⊗₁ ((id ⊗₁ id) ∘ h')) ∘ h) (day id x (Y .F₁ f y)) (Z .F₁ g z) ∎

  assoc-from-cowedge : ∀ i → Cowedge (Day-diagram X (Y ⊗ᴰ Z) i)
  assoc-from-cowedge i .nadir = Day.nadir (X ⊗ᴰ Y) Z i
  assoc-from-cowedge i .ψ (a , b) (h , x , y) = Day-rec (assoc-from₀ i h x) y
  assoc-from-cowedge i .extranatural (f , g) = ext λ h x h' y z →
    day (α← _ _ _ ∘ (id ⊗₁ h' ∘ id) ∘ (f ⊗₁ g) ∘ h) (day id (X .F₁ id x) y) z   ≡⟨ day-ap (ap (α← _ _ _ ∘_) (⊗.extendl (ap₂ _,_ id-comm-sym (ap (_∘ g) (idr h') ∙ introl ⊗.F-id)))) (day-ap refl (X .F-id #ₚ _) refl) refl ⟩
    day (α← _ _ _ ∘ (f ⊗₁ (id ⊗₁ id)) ∘ (id ⊗₁ h' ∘ g) ∘ h) (day id x y) z      ≡⟨ day-apₘ (extendl (associator .Isoⁿ.from .is-natural _ _ _)) ⟩
    day (((f ⊗₁ id) ⊗₁ id) ∘ α← _ _ _ ∘ (id ⊗₁ h' ∘ g) ∘ h) (day id x y) z      ≡⟨ day-glue refl ⟩
    day (α← _ _ _ ∘ (id ⊗₁ h' ∘ g) ∘ h) (day (id ∘ (f ⊗₁ id)) x y) (Z .F₁ id z) ≡⟨ day-ap (ap (α← _ _ _ ∘_) (ap₂ _∘_ refl (introl ⊗.F-id))) (day-glue id-comm-sym ∙ day-ap refl refl (Y .F-id #ₚ y)) (Z .F-id #ₚ z) ⟩
    day (α← _ _ _ ∘ (id ⊗₁ h' ∘ g) ∘ (id ⊗₁ id) ∘ h) (day id (X .F₁ f x) y) z   ∎

  Day-assoc : (X ⊗ᴰ Y) ⊗ᴰ Z ≅ⁿ X ⊗ᴰ (Y ⊗ᴰ Z)
  Day-assoc = to-natural-iso mk-assoc where
    mk-assoc : make-natural-iso ((X ⊗ᴰ Y) ⊗ᴰ Z) (X ⊗ᴰ (Y ⊗ᴰ Z))
    mk-assoc .eta x = Day-rec (assoc-to-cowedge x)
    mk-assoc .inv x = Day-rec (assoc-from-cowedge x)
    mk-assoc .eta∘inv x = ext λ h x h' y z →
      day (α→ _ _ _ ∘ (id ⊗₁ id) ∘ α← _ _ _ ∘ (id ⊗₁ h') ∘ h) x (day id y z) ≡⟨ day-apₘ (pulll (elimr ⊗.F-id) ∙ cancell (associator .Isoⁿ.invl ηₚ _)) ⟩
      day ((id ⊗₁ h') ∘ h) x (day id y z)                                    ≡⟨ day-glue refl ⟩
      day h (X .F₁ id x) (day (id ∘ h') y z)                                 ≡⟨ day-ap refl (X .F-id #ₚ x) (day-apₘ (idl h')) ⟩
      day h x (day h' y z)                                                   ∎
    mk-assoc .inv∘eta x = ext λ h h' x y z →
      day (α← _ _ _ ∘ (id ⊗₁ id) ∘ α→ _ _ _ ∘ (h' ⊗₁ id) ∘ h) (day id x y) z ≡⟨ day-apₘ (pulll (elimr ⊗.F-id) ∙ cancell (associator .Isoⁿ.invr ηₚ _)) ⟩
      day ((h' ⊗₁ id) ∘ h) (day id x y) z                                    ≡⟨ day-glue refl ⟩
      day h (day (id ∘ h') x y) (Z .F₁ id z)                                 ≡⟨ day-ap refl (day-apₘ (idl h')) (Z .F-id #ₚ z) ⟩
      day h (day h' x y) z                                                   ∎
    mk-assoc .natural x y f = ext λ h h' x y z →
      day ((α→ _ _ _ ∘ (h' ⊗₁ id) ∘ h) ∘ f) x (day id y z) ≡⟨ day-ap (pullr (pullr refl)) refl refl ⟩
      day (α→ _ _ _ ∘ (h' ⊗₁ id) ∘ h ∘ f) x (day id y z)   ∎

private module M = Monoidal-category

abstract
  day-triangle : ∀ {A B : ⌞ PSh ℓ C ⌟} → Day-map (Day-idr A .Isoⁿ.to) idnt ∘nt Day-assoc A (よ₀ C Unit) B .Isoⁿ.from ≡ Day-map idnt (Day-idl B .Isoⁿ.to)
  day-triangle {A} {B} = ext λ i h x h' y z →
    day (α← _ _ _ ∘ (id ⊗₁ h') ∘ h) (A .F₁ (ρ← ∘ (id ⊗₁ y) ∘ id) x) z         ≡⟨ day-ap refl (ap₂ (A .F₁) (ap (ρ← ∘_) (idr _)) refl) (sym (B .F-id #ₚ z)) ⟩
    day (α← _ _ _ ∘ (id ⊗₁ h') ∘ h) (A .F₁ (ρ← ∘ (id ⊗₁ y)) x) (B .F₁ id z)   ≡⟨ sym (day-glue refl) ⟩
    day ((ρ← ∘ (id ⊗₁ y) ⊗₁ id) ∘ α← _ _ _ ∘ (id ⊗₁ h') ∘ h) x z              ≡⟨ day-apₘ (⊗.pushl (ap₂ _,_ refl (introl refl))) ⟩
    day ((ρ← ⊗₁ id) ∘ ((id ⊗₁ y) ⊗₁ id) ∘ α← _ _ _ ∘ (id ⊗₁ h') ∘ h) x z      ≡⟨ day-apₘ (ap₂ _∘_ refl (extendl (sym (associator .Isoⁿ.from .is-natural _ _ _)))) ⟩
    day ((ρ← ⊗₁ id) ∘ α← _ _ _ ∘ (id ⊗₁ (y ⊗₁ id)) ∘ (id ⊗₁ h') ∘ h) x z      ≡⟨ day-apₘ (pulll triangle) ⟩
    day ((id ⊗₁ λ←) ∘ (id ⊗₁ (y ⊗₁ id)) ∘ (id ⊗₁ h') ∘ h) x z                 ≡⟨ day-apₘ (pulll (sym (⊗.F-∘ _ _)) ∙ pulll (sym (⊗.F-∘ _ _)) ∙ ap (_∘ h) (ap₂ _⊗₁_ (eliml (eliml refl)) (pullr refl))) ⟩
    day ((id ⊗₁ (λ← ∘ (y ⊗₁ id) ∘ h')) ∘ h) x z                               ≡⟨ day-glue refl ⟩
    day h (A .F₁ id x) (B .F₁ (λ← ∘ (y ⊗₁ id) ∘ h') z)                        ≡⟨ day-ap refl (A .F-id #ₚ x) refl ⟩
    day h x (B .F₁ (λ← ∘ (y ⊗₁ id) ∘ h') z)                                   ∎

  day-pentagon
    : ∀ {A B C D : ⌞ PSh ℓ C ⌟}
    → Day-map (Day-assoc A B C .Isoⁿ.from) idnt
      ∘nt Day-assoc A (B ⊗ᴰ C) D .Isoⁿ.from
      ∘nt Day-map idnt (Day-assoc B C D .Isoⁿ.from)
    ≡ Day-assoc (A ⊗ᴰ B) C D .Isoⁿ.from
      ∘nt Day-assoc A B (C ⊗ᴰ D) .Isoⁿ.from
  day-pentagon {D = D} = ext λ i h a h' b h'' c d →
    let
      it =
        (α← _ _ _ ⊗₁ id) ∘ α← _ _ _ ∘ (id ⊗₁ α← _ _ _ ∘ (id ⊗₁ h'') ∘ h') ∘ h         ≡⟨ ap₂ _∘_ refl (ap₂ _∘_ refl (⊗.pushl (ap₂ _,_ (intror refl) refl))) ⟩
        (α← _ _ _ ⊗₁ id) ∘ α← _ _ _ ∘ (id ⊗₁ α← _ _ _) ∘ (id ⊗₁ (id ⊗₁ h'') ∘ h') ∘ h ≡⟨ pulll refl ∙ extendl (pullr refl ∙ pentagon) ⟩
        α← _ _ _ ∘ α← _ _ _ ∘ (id ⊗₁ (id ⊗₁ h'') ∘ h') ∘ h                            ≡⟨ ap₂ _∘_ refl (ap₂ _∘_ refl (⊗.pushl (ap₂ _,_ (intror refl) refl))) ⟩
        α← _ _ _ ∘ α← _ _ _ ∘ (id ⊗₁ (id ⊗₁ h'')) ∘ (id ⊗₁ h') ∘ h                    ≡⟨ ap₂ _∘_ refl (extendl (associator .Isoⁿ.from .is-natural _ _ _)) ⟩
        α← _ _ _ ∘ ((id ⊗₁ id) ⊗₁ h'') ∘ α← _ _ _ ∘ (id ⊗₁ h') ∘ h                    ≡⟨ ap₂ _∘_ refl (ap₂ _∘_ (ap (_⊗₁ h'') ⊗.F-id) refl) ⟩
        (α← _ _ _ ∘ (id ⊗₁ h'') ∘ α← _ _ _ ∘ (id ⊗₁ h') ∘ h)                          ∎
    in
      day (α← _ _ _ ∘ (id ⊗₁ (α← _ _ _) ∘ (id ⊗₁ h'') ∘ h') ∘ h) (day (α← _ _ _ ∘ (id ⊗₁ id) ∘ id) (day id a b) c) d  ≡⟨ day-ap refl (day-ap (elimr (eliml ⊗.F-id) ∙ introl refl) refl refl) (sym (D .F-id #ₚ d)) ⟩
      day (α← _ _ _ ∘ (id ⊗₁ (α← _ _ _) ∘ (id ⊗₁ h'') ∘ h') ∘ h) (day (id ∘ α← _ _ _) (day id a b) c) (D .F₁ id d)    ≡⟨ sym (day-glue refl) ⟩
      day ((α← _ _ _ ⊗₁ id) ∘ α← _ _ _ ∘ (id ⊗₁ (α← _ _ _) ∘ (id ⊗₁ h'') ∘ h') ∘ h) (day id (day id a b) c) d         ≡⟨ day-apₘ it ⟩
      day (α← _ _ _ ∘ (id ⊗₁ h'') ∘ α← _ _ _ ∘ (id ⊗₁ h') ∘ h) (day id (day id a b) c) d                              ∎

Day-monoidal : Monoidal-category (PSh ℓ C)
Day-monoidal .M.-⊗-      = Day-bifunctor
Day-monoidal .M.Unit     = よ₀ C Unit
Day-monoidal .M.unitor-l = to-natural-iso mk-λ where
  mk-λ : make-natural-iso _ _
  mk-λ .eta x = Day-idl x .Isoⁿ.from
  mk-λ .inv x = Day-idl x .Isoⁿ.to
  mk-λ .eta∘inv x = Day-idl x .Isoⁿ.invr
  mk-λ .inv∘eta x = Day-idl x .Isoⁿ.invl
  mk-λ .natural x y f = trivial!
Day-monoidal .M.unitor-r = to-natural-iso mk-ρ where
  mk-ρ : make-natural-iso _ _
  mk-ρ .eta x = Day-idr x .Isoⁿ.from
  mk-ρ .inv x = Day-idr x .Isoⁿ.to
  mk-ρ .eta∘inv x = Day-idr x .Isoⁿ.invr
  mk-ρ .inv∘eta x = Day-idr x .Isoⁿ.invl
  mk-ρ .natural x y f = trivial!
Day-monoidal .M.associator = to-natural-iso mk-α where
  mk-α : make-natural-iso _ _
  mk-α .eta (x , y , z) = Day-assoc x y z .Isoⁿ.to
  mk-α .inv (x , y , z) = Day-assoc x y z .Isoⁿ.from
  mk-α .eta∘inv (x , y , z) = Day-assoc x y z .Isoⁿ.invl
  mk-α .inv∘eta (x , y , z) = Day-assoc x y z .Isoⁿ.invr
  mk-α .natural x y f = trivial!
Day-monoidal .M.triangle {A} {B} = day-triangle
Day-monoidal .M.pentagon {A} {B} {C} {D} = day-pentagon
```
