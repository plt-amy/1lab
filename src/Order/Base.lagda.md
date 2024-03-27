<!--
```agda
open import 1Lab.Reflection

open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Order.Base where
```

# Partially ordered sets {defines="poset partial-order partially-ordered-set thin-category"}

A **poset** is a [[set]] equipped with a relation $x \le y$, called a
**partial order**, which is reflexive, transitive, and _antisymmetric_.
Put another way, a poset is a [[univalent category]] which has _at most
one_ morphism between each pair of its objects: a **thin** category.

Posets are a simultaneous generalisation of many naturally occurring
notions of "order" in mathematics:

- The "usual" ordering relations $x \le y$ on familiar number systems
  like [the natural numbers], [the integers], the rationals, or the
  reals.

  When ordering the naturals, the integers, and the rationals, we can
  say more: they are _linear_ orders. That is, in addition to the
  properties of $\le$ required to be a poset, we have, for any pair of
  elements $x$ and $y$,

  $$(x \le y) \lor (y \le x)\text{.}$$

[the natural numbers]: Data.Nat.Order.html
[the integers]: Data.Int.Order.html

- The [[divisibility order|divisibility]] on the natural numbers is also
  a poset, as detailed in that page. More than just a poset, it's
  actually a [[lattice]]: the [[meet]] of a pair of numbers is their
  [[_greatest common divisor_]], and the [[join]] is their _least common
  multiple_.

  The divisibility ordering is also interesting as a counterexample:
  even though it is [[decidable]], it fails to be a linear order: any
  pair of _coprime_ numbers is unrelated by the divisibility order.

- Moving away from numbers, partial orders are also intimately connected
  with the study of logic.

  To each theory $\bT$ in a given fragment of propositional logic, we
  can build a set $\cL(\bT)$ of *sentences* in the language of $\bT$;
  The entailment (or provability) relation $\phi \vdash \psi$ is
  _almost_ a partial order: we certainly have $\phi \vdash \phi$, and
  the transitivity requirement is the "cut" rule,

  $$
  \frac
    {\phi \vdash \psi \quad \psi \vdash \theta}
    {\phi \vdash \theta\text{.}}
  $$

  However, this fails to be a poset, because inter-provable formulas
  $\phi \vdash \psi$ and $\psi \vdash \phi$ need not be syntactically
  equal. However, if we [[_quotient_]] the set $\cL(\bT)$ by the
  inter-provability relation, then we do obtain a poset: the
  *Lindenbaum-Tarski algebra* of $\bT$.

  This poset will inherit order-theoretic structure from the logical
  structure of $\bT$: For example, if $\bT$ is expressed in a fragment
  of logic which has conjunction, then $\cL(\bT)$ will be a
  [[meet-semilattice]]; if it also has infinitary disjunction, then its
  Lindenbaum-Tarski algebra is a [[frame]].

- As mentioned in the opening paragraph, the notion of poset
  _specialises_ that of [[univalent category]].

  In particular, to every univalent category $\cC$, we can universally
  associate a poset: Its set of elements is the [[set truncation]] of
  $\cC$'s groupoid of objects, and the relation $x \le y$ is the
  [[propositional truncation]] $\| \hom(x,y) \|$.

  This process can actually be extended to any precategory: however,
  instead of merely truncating the space of objects, we must instead
  take its set-quotient by the relation $x \le y \land y \le x$.

With the motivating examples out of the way, we can finally move onto
the formalised definition of poset, which is a straightforward
translation.

```agda
record Poset o ℓ : Type (lsuc (o ⊔ ℓ)) where
  no-eta-equality
  field
    Ob        : Type o
    _≤_       : Ob → Ob → Type ℓ
    ≤-thin    : ∀ {x y} → is-prop (x ≤ y)
```

We note, as usual, that each fibre $x \le y$ of the order relation
should be a [[proposition]]: this is precisely the formalisation of
having _at most one_ element. The reflexivity, transitivity, and
antisymmetry properties are literal:

```agda
    ≤-refl    : ∀ {x}     → x ≤ x
    ≤-trans   : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
    ≤-antisym : ∀ {x y}   → x ≤ y → y ≤ x → x ≡ y
```

Note that the type of `≤-antisym`{.Agda} ends in a path in `Ob`{.Agda},
which, _a priori_, might not be a proposition: we have not included the
assumption that `Ob`{.Agda} is actually a set. Therefore, it might be
the case that an identification between posets does _not_ correspond to
an identification of the underlying types and one of the relation.
However, since the "symmetric part" of $\le$, the relation
iff.

$$
x \sim y = (x \le y) \land (y \le x)
$$,

is a reflexive mere relation which implies identity, the type of objects
is automatically a set.

```agda
  abstract
    Ob-is-set : is-set Ob
    Ob-is-set =
      identity-system→hlevel 1
        {r = λ _ → ≤-refl , ≤-refl}
        (set-identity-system
          (λ a b → ×-is-hlevel 1 ≤-thin ≤-thin)
          (λ {a} {b} (p , q) → ≤-antisym {a} {b} p q))
        (λ a b → ×-is-hlevel 1 ≤-thin ≤-thin)
```

<!--
```agda
  abstract
    ≤-refl' : ∀ {x y} → x ≡ y → x ≤ y
    ≤-refl' {x = x} p = subst (x ≤_) p ≤-refl

instance
  Underlying-Poset : ∀ {o ℓ} → Underlying (Poset o ℓ)
  Underlying-Poset .Underlying.ℓ-underlying = _
  Underlying-Poset .Underlying.⌞_⌟ = Poset.Ob

  open hlevel-projection

  Poset-ob-hlevel-proj : hlevel-projection (quote Poset.Ob)
  Poset-ob-hlevel-proj .has-level   = quote Poset.Ob-is-set
  Poset-ob-hlevel-proj .get-level _ = pure (lit (nat 2))
  Poset-ob-hlevel-proj .get-argument (_ ∷ _ ∷ arg _ t ∷ _) = pure t
  Poset-ob-hlevel-proj .get-argument _                     = typeError []

  Poset-≤-hlevel-proj : hlevel-projection (quote Poset._≤_)
  Poset-≤-hlevel-proj .has-level   = quote Poset.≤-thin
  Poset-≤-hlevel-proj .get-level _ = pure (lit (nat 1))
  Poset-≤-hlevel-proj .get-argument (_ ∷ _ ∷ arg _ t ∷ _) = pure t
  Poset-≤-hlevel-proj .get-argument _                     = typeError []
```
-->

## Monotone maps {defines="monotone-map monotone-function monotonicity"}

Since we are considering posets to be categories satisfying a property,
it follows that the _category_ of posets should be a full subcategory of
$\thecat{Cat}$; i.e., the maps $P \to Q$ should be precisely the
_functors_ $P \to Q$. However, since there is at most one inhabitant of
each $f(x) \le f(y)$, we are free to drop the functoriality assumptions,
and consider instead the **monotone maps**:

```agda
record
  Monotone {o o' ℓ ℓ'} (P : Poset o ℓ) (Q : Poset o' ℓ')
    : Type (o ⊔ o' ⊔ ℓ ⊔ ℓ') where
  no-eta-equality
```

<!--
```agda
  private
    module P = Poset P
    module Q = Poset Q
```
-->

```agda
  field
    hom    : P.Ob → Q.Ob
    pres-≤ : ∀ {x y} → x P.≤ y → hom x Q.≤ hom y
```

A monotone map between posets is a map between their underlying sets
which *preserves* the order relation. This is the most natural choice:
for example, the monotone functions $(\bN, \le) \to P$ are precisely
nondecreasing sequences of elements in $P$.

<!--
```agda
open Monotone public

private
  variable
    o ℓ o' ℓ' o'' ℓ'' : Level
    P Q R : Poset o ℓ

Monotone-is-hlevel : ∀ n → is-hlevel (Monotone P Q) (2 + n)
Monotone-is-hlevel {Q = Q} n =
  Iso→is-hlevel (2 + n) eqv $ is-set→is-hlevel+2 $ hlevel!
  where unquoteDecl eqv = declare-record-iso eqv (quote Monotone)

instance
  H-Level-Monotone : ∀ {n} → H-Level (Monotone P Q) (2 + n)
  H-Level-Monotone = basic-instance 2 (Monotone-is-hlevel 0)

  Funlike-Monotone : Funlike (Monotone P Q) ⌞ P ⌟ λ _ → ⌞ Q ⌟
  Funlike-Monotone = record { _#_ = hom }

  Membership-Monotone : ⦃ _ : Underlying ⌞ Q ⌟ ⦄ → Membership ⌞ P ⌟ (Monotone P Q) _
  Membership-Monotone = record { _∈_ = λ x S → ⌞ S # x ⌟ }

Monotone-pathp
  : ∀ {o ℓ o' ℓ'} {P : I → Poset o ℓ} {Q : I → Poset o' ℓ'}
  → {f : Monotone (P i0) (Q i0)} {g : Monotone (P i1) (Q i1)}
  → PathP (λ i → ⌞ P i ⌟ → ⌞ Q i ⌟) (apply f) (apply g)
  → PathP (λ i → Monotone (P i) (Q i)) f g
Monotone-pathp q i .hom a = q i a
Monotone-pathp {P = P} {Q} {f} {g} q i .Monotone.pres-≤ {x} {y} α =
  is-prop→pathp
    (λ i → Π-is-hlevel³ {A = ⌞ P i ⌟} {B = λ _ → ⌞ P i ⌟} {C = λ x y → P i .Poset._≤_ x y} 1
      λ x y _ → Q i .Poset.≤-thin {q i x} {q i y})
    (λ _ _ α → f .Monotone.pres-≤ α)
    (λ _ _ α → g .Monotone.pres-≤ α) i x y α

instance
  Extensional-Monotone
    : ∀ {o ℓ o' ℓ' ℓr} {P : Poset o ℓ} {Q : Poset o' ℓ'}
    → ⦃ sa : Extensional (⌞ P ⌟ → ⌞ Q ⌟) ℓr ⦄
    → Extensional (Monotone P Q) ℓr
  Extensional-Monotone {Q = Q} ⦃ sa ⦄ =
    injection→extensional! Monotone-pathp sa
```
-->

It's immediate to see that the identity function is monotone, and that
monotone maps are closed under composition. Since identity of monotone
maps is given by identity of the underlying functions, there is a set of
monotone maps $P \to Q$, and the laws of a category are trivial.

```agda
idₘ : Monotone P P
idₘ .hom    x   = x
idₘ .pres-≤ x≤y = x≤y

_∘ₘ_ : Monotone Q R → Monotone P Q → Monotone P R
(f ∘ₘ g) .hom    x   = f # (g # x)
(f ∘ₘ g) .pres-≤ x≤y = f .pres-≤ (g .pres-≤ x≤y)

Posets : ∀ (o ℓ : Level) → Precategory (lsuc o ⊔ lsuc ℓ) (o ⊔ ℓ)
Posets o ℓ .Precategory.Ob      = Poset o ℓ
Posets o ℓ .Precategory.Hom     = Monotone
Posets o ℓ .Precategory.Hom-set = hlevel!

Posets o ℓ .Precategory.id  = idₘ
Posets o ℓ .Precategory._∘_ = _∘ₘ_

Posets o ℓ .Precategory.idr f       = trivial!
Posets o ℓ .Precategory.idl f       = trivial!
Posets o ℓ .Precategory.assoc f g h = trivial!
```

<!--
```agda
module Posets {o ℓ} = Cat.Reasoning (Posets o ℓ)
```
-->

## Simple constructions

The simplest thing we can do _to_ a poset is to forget the order. This
evidently extends to a faithful functor $\Pos \to \Sets$.

```agda
Forget-poset : ∀ {o ℓ} → Functor (Posets o ℓ) (Sets o)
∣ Forget-poset .Functor.F₀ P ∣    = ⌞ P ⌟
Forget-poset .Functor.F₀ P .is-tr = hlevel!

Forget-poset .Functor.F₁ = hom

Forget-poset .Functor.F-id    = refl
Forget-poset .Functor.F-∘ _ _ = refl
```

Slightly less trivial, we can extend the opposite category construction
to posets as well, by transposing the order relation and making sure to
flip the direction of transitivity:

```agda
_^opp : ∀ {ℓ ℓ'} → Poset ℓ ℓ' → Poset ℓ ℓ'
(P ^opp) .Poset.Ob      = Poset.Ob P
(P ^opp) .Poset._≤_ x y = Poset._≤_ P y x

(P ^opp) .Poset.≤-thin = Poset.≤-thin P
(P ^opp) .Poset.≤-refl = Poset.≤-refl P
(P ^opp) .Poset.≤-trans   x≥y y≥z = Poset.≤-trans P y≥z x≥y
(P ^opp) .Poset.≤-antisym x≥y y≥x = Poset.≤-antisym P y≥x x≥y
```

We can construct the trivial posets with one and zero (object(s), ordering(s)) respectively

```agda

𝟙ᵖ : ∀ {o ℓ} → Poset o ℓ
𝟙ᵖ .Poset.Ob = Lift _ ⊤
𝟙ᵖ .Poset._≤_ _ _ = Lift _ ⊤
𝟙ᵖ .Poset.≤-thin = hlevel!
𝟙ᵖ .Poset.≤-refl = lift tt
𝟙ᵖ .Poset.≤-trans = λ _ _ → lift tt
𝟙ᵖ .Poset.≤-antisym = λ _ _ → refl

𝟘ᵖ : ∀ {o ℓ} → Poset o ℓ
𝟘ᵖ .Poset.Ob = Lift _ ⊥
𝟘ᵖ .Poset._≤_ _ _ = Lift _ ⊥
𝟘ᵖ .Poset.≤-thin ()
𝟘ᵖ .Poset.≤-refl {()}
𝟘ᵖ .Poset.≤-trans ()
𝟘ᵖ .Poset.≤-antisym ()
```
