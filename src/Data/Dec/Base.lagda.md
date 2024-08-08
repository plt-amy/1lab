<!--
```agda
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

open import Data.Sum.Base

open import Meta.Invariant
open import Meta.Idiom
```
-->

```agda
module Data.Dec.Base where
```

# Decidable types {defines="decidable type-of-decisions discrete"}

The type `Dec`{.Agda}, of **decisions** for a type `A`, is a renaming of
the coproduct `A ⊎ ¬ A`. A value of `Dec A` witnesses not that `A`
is decidable, but that it _has been decided_; A witness of decidability,
then, is a proof assigning decisions to values of a certain type.

```agda
data Dec {ℓ} (A : Type ℓ) : Type ℓ where
  yes : (a  :   A) → Dec A
  no  : (¬a : ¬ A) → Dec A

Dec-elim
  : ∀ {ℓ ℓ'} {A : Type ℓ} (P : Dec A → Type ℓ')
  → (∀ y → P (yes y))
  → (∀ y → P (no y))
  → ∀ x → P x
Dec-elim P f g (yes x) = f x
Dec-elim P f g (no x)  = g x

Dec-rec
  : ∀ {ℓ ℓ'} {A : Type ℓ} {X : Type ℓ'}
  → (A → X)
  → (¬ A → X)
  → Dec A → X
Dec-rec = Dec-elim _
```

<!--
```agda
recover : ∀ {ℓ} {A : Type ℓ} ⦃ d : Dec A ⦄ → .A → A
recover ⦃ yes x ⦄ _ = x
recover ⦃ no ¬x ⦄ x = absurd (¬x x)

dec→dne : ∀ {ℓ} {A : Type ℓ} ⦃ d : Dec A ⦄ → ¬ ¬ A → A
dec→dne ⦃ yes x ⦄ _   = x
dec→dne ⦃ no ¬x ⦄ ¬¬x = absurd (¬¬x ¬x)
```
-->

A type is _discrete_ if it has decidable equality.

```agda
Discrete : ∀ {ℓ} → Type ℓ → Type ℓ
Discrete A = {x y : A} → Dec (x ≡ y)
```

<!--
```agda
private variable
  ℓ ℓ' : Level
  A B : Type ℓ
```
-->

If we can construct a pair of maps $A \to B$ and $B \to A$,
then we can deduce decidability of $B$ from decidability of $A$:
that is, `Dec`{.Agda} is an `Invariant`{.Agda} functor.

```agda
instance
  Invariant-Dec : Invariant (eff Dec)
  Invariant-Dec .Invariant.invmap f g (yes a) = yes (f a)
  Invariant-Dec .Invariant.invmap f g (no ¬a) = no (¬a ∘ g)
```

This lets us show the following useful lemma: if $A$ injects into a
discrete type, then $A$ is also discrete.

```agda
Discrete-inj
  : (f : A → B)
  → (∀ {x y} → f x ≡ f y → x ≡ y)
  → Discrete B → Discrete A
Discrete-inj f inj eq? {x} {y} =
  invmap inj (ap f) (eq? {f x} {f y})
```

## Programming with decisions

Despite the failure of `Dec A` to be a [[proposition]] for general `A`,
in the 1Lab, we like to work with decisions through instance search.
This is facilitated by the following functions, which perform instance
search:

```agda
-- Searches for a type given explicitly.
holds? : ∀ {ℓ} (A : Type ℓ) ⦃ d : Dec A ⦄ → Dec A
holds? A ⦃ d ⦄ = d

-- Searches for equality of inhabitants of a discrete type.
_≡?_ : ⦃ d : Discrete A ⦄ (x y : A) → Dec (x ≡ y)
x ≡? y = holds? (x ≡ y)

infix 3 _≡?_
```

And the following operators, which combine instance search with case
analysis:

```agda
caseᵈ_of_ : ∀ {ℓ ℓ'} (A : Type ℓ) ⦃ d : Dec A ⦄ {B : Type ℓ'} → (Dec A → B) → B
caseᵈ A of f = f (holds? A)

caseᵈ_return_of_ : ∀ {ℓ ℓ'} (A : Type ℓ) ⦃ d : Dec A ⦄ (B : Dec A → Type ℓ') → (∀ x → B x) → B d
caseᵈ A return P of f = f (holds? A)

{-# INLINE caseᵈ_of_        #-}
{-# INLINE caseᵈ_return_of_ #-}
```

<!--
```agda
private variable
  P Q : Type ℓ
```
-->

We then have the following basic instances for combining decisions,
expressing that the class of decidable types is closed under sums, products
and functions, and contains the unit type and the empty type.

```agda
instance
  Dec-⊎ : ⦃ _ : Dec A ⦄ ⦃ _ : Dec B ⦄ → Dec (A ⊎ B)
  Dec-⊎ ⦃ yes A ⦄ ⦃ _ ⦄ = yes (inl A)
  Dec-⊎ ⦃ no ¬A ⦄ ⦃ yes B ⦄ = yes (inr B)
  Dec-⊎ ⦃ no ¬A ⦄ ⦃ no ¬B ⦄ = no [ ¬A , ¬B ]

  Dec-× : ⦃ _ : Dec P ⦄ ⦃ _ : Dec Q ⦄ → Dec (P × Q)
  Dec-× {Q = _} ⦃ yes p ⦄ ⦃ yes q ⦄ = yes (p , q)
  Dec-× {Q = _} ⦃ yes p ⦄ ⦃ no ¬q ⦄ = no λ z → ¬q (snd z)
  Dec-× {Q = _} ⦃ no ¬p ⦄ ⦃ _ ⦄     = no λ z → ¬p (fst z)

  Dec-→ : ⦃ _ : Dec P ⦄ ⦃ _ : Dec Q ⦄ → Dec (P → Q)
  Dec-→ {Q = _} ⦃ yes p ⦄ ⦃ yes q ⦄ = yes λ _ → q
  Dec-→ {Q = _} ⦃ yes p ⦄ ⦃ no ¬q ⦄ = no λ pq → ¬q (pq p)
  Dec-→ {Q = _} ⦃ no ¬p ⦄ ⦃ q ⦄ = yes λ p → absurd (¬p p)

  Dec-⊤ : Dec ⊤
  Dec-⊤ = yes tt

  Dec-⊥ : Dec ⊥
  Dec-⊥ = no id

  Dec-Lift : ∀ {ℓ ℓ'} {A : Type ℓ} → ⦃ Dec A ⦄ → Dec (Lift ℓ' A)
  Dec-Lift ⦃ d ⦄ = Lift-≃ e⁻¹ <≃> d
```

These closure properties make `Dec`{.Agda} a `Monoidal`{.Agda} and
`Alternative`{.Agda} functor.

```agda
instance
  Monoidal-Dec : Monoidal (eff Dec)
  Monoidal-Dec .Monoidal.munit = Dec-⊤
  Monoidal-Dec .Monoidal._<,>_ a b = Dec-× ⦃ a ⦄ ⦃ b ⦄

  Alternative-Dec : Alternative (eff Dec)
  Alternative-Dec .Alternative.empty = Dec-⊥
  Alternative-Dec .Alternative._<+>_ a b = Dec-⊎ ⦃ a ⦄ ⦃ b ⦄
```

<!--
```agda
infix 0 ifᵈ_then_else_

ifᵈ_then_else_ : Dec A → B → B → B
ifᵈ yes a then y else n = y
ifᵈ no ¬a then y else n = n

is-yes : ∀ {ℓ} {A : Type ℓ} → Dec A → Type
is-yes (yes x) = ⊤
is-yes (no _)  = ⊥

decide! : ∀ {ℓ} {A : Type ℓ} ⦃ d : Dec A ⦄ {_ : is-yes d} → A
decide! ⦃ yes x ⦄ = x
```
-->

## Relation to sums

The decidability of $A$ can also be phrased as $A + \neg A$, so we
provide helpers to convert between the two.

```agda
from-dec : Dec A → A ⊎ ¬ A
from-dec (yes a) = inl a
from-dec (no ¬a) = inr ¬a

to-dec : A ⊎ ¬ A → Dec A
to-dec (inl  a) = yes a
to-dec (inr ¬a) = no ¬a
```

The proof that these functions are inverses is automatic by computation,
and thus it can be shown they are equivalences:

```agda
from-dec-is-equiv : {A : Type ℓ} → is-equiv (from-dec {A = A})
from-dec-is-equiv = is-iso→is-equiv (iso to-dec p q) where
  p : _
  p (inl x)  = refl
  p (inr ¬x) = refl

  q : _
  q (yes x) = refl
  q (no x)  = refl
```
