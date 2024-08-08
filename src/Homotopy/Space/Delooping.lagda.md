<!--
```agda
open import 1Lab.Reflection.Induction
open import 1Lab.Prelude

open import Algebra.Group.Cat.Base
open import Algebra.Group.Homotopy
open import Algebra.Group.Ab
open import Algebra.Group

open import Cat.Base

open import Data.Set.Truncation

open import Homotopy.Connectedness
open import Homotopy.Conjugation
```
-->

```agda
module Homotopy.Space.Delooping where
```

# Deloopings {defines="delooping"}

A natural question to ask, given that all pointed types have a
fundamental group, is whether every group arises as the fundamental
group of some type. The answer to this question is "yes", but in the
annoying way that questions like these tend to be answered: Given any
group $G$, we construct a type $\B{G}$ with $\pi_1(\B{G}) \equiv G$. We
call $\B{G}$ the **delooping** of $G$.

<!--
```agda
module _ {ℓ} (G : Group ℓ) where
  module G = Group-on (G .snd)
  open G
```
-->

```agda
  data Deloop : Type ℓ where
    base    : Deloop
    path    : ⌞ G ⌟ → base ≡ base
    path-sq : (x y : ⌞ G ⌟) → Square refl (path x) (path (x ⋆ y)) (path y)
    squash  : is-groupoid Deloop

  Deloop∙ : Type∙ ℓ
  Deloop∙ = Deloop , base
```

<!--
```
  private instance
    H-Level-Deloop : ∀ {n} → H-Level Deloop (3 + n)
    H-Level-Deloop = basic-instance 3 squash
```
-->

The delooping is constructed as a higher inductive type. We have a
generic `base`{.Agda} point, and a constructor expressing that
`Deloop`{.Agda} is a groupoid; Since it is a groupoid, it has a set of
loops `point ≡ point`: this is necessary, since otherwise we would not
be able to prove that $\pi_1(\B{G}) \equiv G$. We then have the
"interesting" higher constructors: `path`{.Agda} lets us turn any
element of $G$ to a path `point ≡ point`, and `path-sq`{.Agda} expresses
that `path`{.Agda} is a group homomorphism. More specifically,
`path-sq`{.Agda} fills the square below:

~~~{.quiver}
\[\begin{tikzcd}
  \bullet && \bullet \\
  \\
  \bullet && \bullet
  \arrow["{\refl}"', from=1-1, to=3-1]
  \arrow["{\rm{path}(x)}", from=1-1, to=1-3]
  \arrow["{\rm{path}(y)}", from=1-3, to=3-3]
  \arrow["{\rm{path}(x \star y)}"', from=3-1, to=3-3]
\end{tikzcd}\]
~~~

Using the `uniqueness result for double composition`{.Agda
ident=··-unique}, we derive that `path`{.Agda} is a homomorphism in the
traditional sense:

```agda
  abstract
    path-∙ : ∀ x y → path (x ⋆ y) ≡ path x ∙ path y
    path-∙ x y i j =
      ··-unique refl (path x) (path y)
        (path (x ⋆ y)    , path-sq x y)
        (path x ∙ path y , ∙-filler _ _)
        i .fst j
```

<details>
<summary>
And the standard argument shows that `path`{.Agda}, being a group
homomorphism, preserves the group identity.
</summary>

```agda
    path-unit : path unit ≡ refl
    path-unit =
      path unit                               ≡⟨ sym (∙-idr _) ⟩
      path unit ∙ ⌜ refl ⌝                    ≡˘⟨ ap¡ (∙-invr _)  ⟩
      path unit ∙ path unit ∙ sym (path unit) ≡⟨ ∙-assoc _ _ _ ∙ ap₂ _∙_ (sym (path-∙ _ _)) refl ⟩
      path ⌜ unit ⋆ unit ⌝ ∙ sym (path unit)  ≡⟨ ap! G.idr ⟩
      path unit ∙ sym (path unit)             ≡⟨ ∙-invr _  ⟩
      refl                                    ∎
```
</details>

We define an elimination principle for `Deloop`{.Agda}, which has the
following monstruous type since it works for mapping into arbitrary
groupoids. As usual, if we're mapping into a family of types that's more
truncated (i.e. a family of sets or propositions), some of the higher
cases become automatic.

```agda
  Deloop-elim
    : ∀ {ℓ'} (P : Deloop → Type ℓ')
    → (∀ x → is-groupoid (P x))
    → (p : P base)
    → (ploop : ∀ x → PathP (λ i → P (path x i)) p p)
    → ( ∀ x y
        → SquareP (λ i j → P (path-sq x y i j))
                  (λ _ → p) (ploop x) (ploop (x ⋆ y)) (ploop y))
    → ∀ x → P x
```

<!--
```agda
  unquoteDef Deloop-elim = make-elim-with (default-elim-visible into 3)
    Deloop-elim (quote Deloop)

  unquoteDecl Deloop-elim-set = make-elim-with (default-elim-visible into 2)
    Deloop-elim-set (quote Deloop)

  unquoteDecl Deloop-elim-prop = make-elim-with (default-elim-visible into 1)
    Deloop-elim-prop (quote Deloop)
```
-->

We can then proceed to characterise the type `point ≡ x` by an
encode-decode argument. We define a family `Code`{.Agda}, where the
fibre over `base`{.Agda} is definitionally `G`; Then we exhibit inverse
equivalences `base ≡ x → Code x` and `Code x → base ≡ x`, which fit
together to establish `G ≡ (base ≡ base)`.

We'll want to define the family `Code` by induction on `Deloop`. First,
since we have to map into a [[groupoid]], we'll map into the type
$\set$, rather than $\ty$. This takes care of the truncation
constructor (which is hidden from the page since it is entirely
formulaic): let's tackle the rest in order. We can also handle the
`base`{.Agda} case, since `Code base = G` was already a part of our
specification.

```agda
  Code : Deloop → Set ℓ
  Code = go module Code where
    open is-iso

    base-case : Set ℓ
    ∣ base-case ∣    = ⌞ G ⌟
    base-case .is-tr = hlevel 2
```

To handle the path case, we'll have to produce, given an element $x :
G$, an equivalence $G \simeq G$: by univalence, we can then lift this
equivalence to a path $G \equiv G$, which we can use as the
`path-case`{.Agda}. While there might be many maps $G \to (G \simeq G)$,
one is canonical: the [[Yoneda embedding]] map, sending $x$ to $y
\mapsto xy$.

```agda
    path-case : ⌞ G ⌟ → base-case ≡ base-case
    path-case x = n-ua eqv module path-case where
      rem₁ : is-iso (_⋆ x)
      rem₁ .inv = _⋆ x ⁻¹
      rem₁ .rinv x = cancelr inversel
      rem₁ .linv x = cancelr inverser

      eqv : ⌞ G ⌟ ≃ ⌞ G ⌟
      eqv .fst = _
      eqv .snd = is-iso→is-equiv rem₁

    open path-case
```

Finally, we can satisfy the coherence case `path-sq`{.Agda} by an
algebraic calculation on paths:

```agda
    coh : ∀ x y → Square refl (path-case x) (path-case (x ⋆ y)) (path-case y)
    coh x y = n-Type-square $ transport (sym Square≡double-composite-path) $
      ua (eqv x) ∙ ua (eqv y) ≡˘⟨ ua∙ ⟩
      ua (eqv x ∙e eqv y)     ≡⟨ ap ua (Σ-prop-path! (funext λ _ → sym associative)) ⟩
      ua (eqv (x ⋆ y))        ∎
```

<!--
```agda
    go : Deloop → Set ℓ
    go base = base-case
    go (path x i) = path-case x i
    go (path-sq x y i j) = coh x y i j
    go (squash x y p q α β i j k) =
      n-Type-is-hlevel 2 (Code x) (Code y)
        (λ i → Code (p i))     (λ i → Code (q i))
        (λ i j → Code (α i j)) (λ i j → Code (β i j))
        i j k
```
-->

We can then define the encoding and decoding functions. The encoding
function `encode`{.Agda} is given by lifting a path from `Deloop`{.Agda}
to `Code`{.Agda}. For decoding, we do induction on `Deloop`{.Agda} with
`Code x .fst → base ≡ x` as the motive.

```agda
  opaque
    encode : ∀ x → base ≡ x → Code ʻ x
    encode x p = subst (Code ʻ_) p unit

  decode : ∀ x → Code ʻ x → base ≡ x
  decode = go where
    coh : ∀ x → PathP (λ i → Code ʻ path x i → base ≡ path x i) path path
    coh x i c j = hcomp (∂ i ∨ ∂ j) λ where
      k (k = i0) → path (ua-unglue (Code.path-case.eqv x) i c) j
      k (i = i0) → path-sq c x (~ k) j
      k (i = i1) → path c j
      k (j = i0) → base
      k (j = i1) → path x (i ∨ ~ k)

    go : ∀ x → Code ʻ x → base ≡ x
    go base c = path c
    go (path x i) c = coh x i c
    go (path-sq x y i j) = is-set→squarep
      (λ i j → fun-is-hlevel {A = Code ʻ path-sq x y i j} 2 (Deloop.squash base (path-sq x y i j)) )
      (λ i → path) (coh x) (coh (x ⋆ y)) (coh y) i j
    go (squash x y p q α β i j k) =
      is-hlevel→is-hlevel-dep {B = λ x → Code ʻ x → base ≡ x} 2 (λ x → hlevel 3)
        (go x) (go y) (λ i → go (p i)) (λ i → go (q i))
        (λ i j → go (α i j)) (λ i j → go (β i j)) (squash x y p q α β) i j k
```

Proving that these are inverses finishes the proof. For one direction,
we use path induction to reduce to the case `decode base (encode base
refl) ≡ refl`; A quick argument tells us that `encode base refl`{.Agda}
is the group identity, and since `path`{.Agda} is a group homomorphism,
we have `path unit = refl`, as required.

```agda
  opaque
    unfolding encode

    encode→decode : ∀ {x} (p : base ≡ x) → decode x (encode x p) ≡ p
    encode→decode p =
      J (λ y p → decode y (encode y p) ≡ p)
        (ap path (transport-refl _) ∙ path-unit)
        p
```

In the other direction, we do induction on deloopings; Since the motive
is a family of propositions, we can use `Deloop-elim-prop`{.Agda} instead
of the full `Deloop-elim`{.Agda}, which reduces the goal to proving $1
\star 1 = 1$.

```agda
    decode→encode : ∀ x (c : Code ʻ x) → encode x (decode x c) ≡ c
    decode→encode =
      Deloop-elim-prop
        (λ x → (c : Code ʻ x) → encode x (decode x c) ≡ c)
        (λ x → Π-is-hlevel 1 λ _ → Code x .is-tr _ _)
        λ c → transport-refl _ ∙ G.idl
```

This completes the proof, and lets us establish that the fundamental
group of `Deloop`{.Agda} is `G`, which is what we wanted.

```agda
  G≃ΩB : ⌞ G ⌟ ≃ (base ≡ base)
  G≃ΩB = Iso→Equiv (decode base , iso (encode base) encode→decode (decode→encode base))

  G≡π₁B : G ≡ πₙ₊₁ 0 (Deloop , base)
  G≡π₁B = ∫-Path Groups-equational
    (total-hom (λ x → inc (path x))
      record { pres-⋆ = λ x y → ap ∥_∥₀.inc (path-∙ _ _) })
    (∙-is-equiv (G≃ΩB .snd) (∥-∥₀-idempotent (squash base base)))
```

Since `Deloop`{.Agda} is a groupoid, each of its loop spaces is
automatically a set, so we do not _necessarily_ need the truncation when
taking its fundamental group. This alternative construction is worth
mentioning since it allows us to trade a proof that `encode`{.Agda}
preserves multiplication for proofs that it also preserves the identity,
inverses, differences, etc.

```agda
  encode-is-group-hom
    : is-group-hom (π₁Groupoid.on-Ω Deloop∙ squash) (G .snd) (encode base)
  encode-is-group-hom .is-group-hom.pres-⋆ x y = eqv.injective₂ (eqv.ε _) $
    path (encode base x ⋆ encode base y)          ≡⟨ path-∙ (encode base x) (encode base y) ⟩
    path (encode base x) ∙ path (encode base y)   ≡⟨ ap₂ _∙_ (eqv.ε _) (eqv.ε _) ⟩
    x ∙ y                                         ∎
    where module eqv = Equiv G≃ΩB
```

<!--
```agda
  module encode where
    open is-group-hom encode-is-group-hom public
    open Equiv (Equiv.inverse G≃ΩB) public

instance
  H-Level-Deloop : ∀ {n} {ℓ} {G : Group ℓ} → H-Level (Deloop G) (3 + n)
  H-Level-Deloop {n} = basic-instance 3 squash
```
-->


## For abelian groups

<!--
```agda
module _ {ℓ} (G : Group ℓ) (ab : is-commutative-group G) where
  open Group-on (G .snd)
  open is-group-hom

  opaque
```
-->

If $G$ is an abelian group, then we can characterise the loop spaces of
$\B G$ based at totally arbitrary points, rather than the above
characterisation which only applies for the loop space at `base`{.Agda}.
Our proof starts with the following immediate observation:
multiplication in $\pi_1(\B G)$ is commutative as well.

```agda
    ∙-comm : (p q : Path (Deloop G) base base) → p ∙ q ≡ q ∙ p
    ∙-comm p q = encode.injective G
      (encode.pres-⋆ G _ _ ·· ab _ _ ·· sym (encode.pres-⋆ G _ _))
```

We'll construct a function that computes the "`winding`{.Agda} number"
of a loop with arbitrary base.

```agda
  winding : {x : Deloop G} → x ≡ x → ⌞ G ⌟
  winding {x = x} = go x module windingⁱ where
```

<!--
```agda
    hl : (x : Deloop G) → is-set (x ≡ x → ⌞ G ⌟)
    hl _ = hlevel 2

    interleaved mutual
      go   : (x : Deloop G) → x ≡ x → ⌞ G ⌟

      coherence : Type _ [ i1 ↦ (λ ._ → (x : ⌞ G ⌟) → PathP (λ i → path {G = G} x i ≡ path x i → ⌞ G ⌟) (encode G base) (encode G base)) ]
      coh : outS coherence
```
-->

```agda
      deg : base ≡ base → ⌞ G ⌟
      deg = encode G base

      go base loop = deg loop
```

If the loop is indeed based at the `base`{.Agda}point constructor, then
we can appeal to the existing construction; We'll abbreviate it as
`deg`{.Agda} for this construction.

Since our codomain is a set, the higher cases are both handled
mechanically; We omit them from the page in the interest of parsimony.
We're left with tackling the `path`{.Agda} case, which means
constructing a term exhibiting the `coherence`{.Agda} below:

```agda
      coherence = inS ( ∀ b →
        PathP (λ i → path b i ≡ path b i → ⌞ G ⌟) deg deg)
```

This condition is a bit funky, since at first glance it looks like all
we must do is equate `deg` with itself. However, we're doing this over a
non-trivial identification in the domain. By extensionality for
dependent functions, the above is equivalent to showing that
`deg`{.Agda} produces identical results given an element $b : G$ and
loops $x_0$, $x_1$ fiting into a commutative square

~~~{.quiver}
\[\begin{tikzcd}[ampersand replacement=\&]
  {\rm{base}} \&\& {\rm{base}} \\
  \\
  {\rm{base}} \&\& {\rm{base}}
  \arrow["{x_1}", from=1-1, to=1-3]
  \arrow["{\rm{path}(b)}"', from=1-1, to=3-1]
  \arrow["{x_0}"', from=3-1, to=3-3]
  \arrow["{\rm{path}(b)}", from=1-3, to=3-3]
\end{tikzcd}\]
~~~

Since commutativity of the diagram above says precisely that $x_1$ is
the [[conjugate|conjugation of paths]] of $x_0$ by $\rm{path}(b)$, we
can reason about conjugation instead; And since we've shown that
$x_0\rm{path}(b) = \rm{path}(b)x_0$, this conjugation is just $x_1$
again. That finishes the construction:

```agda
      abstract
        coh b = funext-dep λ {x₀} {x₁} p → ap deg $ sym $
          x₁               ≡˘⟨ pathp→conj p ⟩
          conj (path b) x₀ ≡⟨ conj-commutative (∙-comm x₀ (path b)) ⟩
          x₀               ∎

      go (path x i) loop = coh x i loop
```

<!--
```agda
      go (path-sq x y i j) = is-set→squarep (λ i j → hl (path-sq x y i j))
        (λ j → encode G base) (coh x) (coh (x ⋆ y)) (coh y)
        i j
      go (squash x y p q α β i j k) =
        is-hlevel→is-hlevel-dep 2 (λ x → is-hlevel-suc 2 (hl x))
          (go x) (go y) (λ i → go (p i)) (λ j → go (q j))
          (λ i j → go (α i j)) (λ i j → go (β i j))
          (squash x y p q α β) i j k

  {-# DISPLAY windingⁱ.go x p = winding p #-}
```
-->

We could go on to define the inverse to `winding`{.Agda} similar to how
we constructed `decode`{.Agda}, but there's a trick: since being an
equivalence is a proposition, if we want to show $\rm{winding}_x$ is an
equivalence for arbitrary $x$, it suffices to do so for
$\rm{winding}_{\rm{base}} = \rm{encode}$; but we've already shown
_that's_ an equivalence! A similar remark allows us to conclude that
$\rm{winding}_x$ is a group homomorphism $\Omega (\B G, x) \to G$.

```agda
  opaque
    winding-is-equiv : ∀ x → is-equiv (winding {x})
    winding-is-equiv = Deloop-elim-prop G _ (λ _ → hlevel 1) $
      Equiv.inverse (G≃ΩB G) .snd

    winding-is-group-hom : ∀ x →
      is-group-hom (π₁Groupoid.on-Ω (Deloop G , x) (hlevel 3))
        (G .snd) (winding {x})
    winding-is-group-hom = Deloop-elim-prop G _ (λ x → hlevel 1) λ where
      .pres-⋆ x y → encode.pres-⋆ G x y
```

We can then obtain a nice interface for working with `winding`{.Agda}.

```agda
  module winding {x} where
    open Equiv (winding , winding-is-equiv x) public
    open is-group-hom (winding-is-group-hom x) public

  pathᵇ : (x : Deloop G) → ⌞ G ⌟ → x ≡ x
  pathᵇ _ = winding.from
```

<!--
```agda
  -- Want: pathᵇ base ≡ path, definitionally
  -- Have: pathᵇ base is a projection from some opaque record
  -- Soln: Evil hack!
  opaque
    unfolding winding-is-equiv

    winding-is-equiv-base : winding-is-equiv base ≡ Equiv.inverse (G≃ΩB G) .snd
    winding-is-equiv-base = prop!

  {-# REWRITE winding-is-equiv-base #-}

  _ : pathᵇ base ≡ path
  _ = refl -- MUST check!

  pathᵇ-sq : ∀ (x : Deloop G) g h → Square refl (pathᵇ x g) (pathᵇ x (g ⋆ h)) (pathᵇ x h)
  pathᵇ-sq = Deloop-elim-prop G _ (λ x → hlevel 1) λ g h → path-sq g h

Deloop-is-connected : ∀ {ℓ} {G : Group ℓ} → is-connected∙ (Deloop G , base)
Deloop-is-connected = Deloop-elim-prop _ _ (λ _ → hlevel 1) (inc refl)
```
-->
