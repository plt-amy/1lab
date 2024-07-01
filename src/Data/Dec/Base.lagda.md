<!--
```agda
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type
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
recover {A = A} ⦃ no ¬x ⦄ x = go (¬x x) where
  go : .⊥ → A
  go ()
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
then we can deduce decidability of $B$ from decidability of $A$.

```agda
Dec-map
  : (A → B) → (B → A)
  → Dec A → Dec B
Dec-map to from (yes a) = yes (to a)
Dec-map to from (no ¬a) = no (¬a ∘ from)

Dec-≃ : A ≃ B → Dec A → Dec B
Dec-≃ e = Dec-map (Equiv.to e) (Equiv.from e)
```

This lets us show the following useful lemma: if $A$ injects into a
discrete type, then $A$ is also discrete.

```agda
Discrete-inj
  : (f : A → B)
  → (∀ {x y} → f x ≡ f y → x ≡ y)
  → Discrete B → Discrete A
Discrete-inj f inj eq? {x} {y} =
  Dec-map inj (ap f) (eq? {f x} {f y})
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
expressing that the class of decidable types is closed under products
and functions, and contains the unit type and the empty type.

```agda
instance
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

not? : ∀ {ℓ} {A : Type ℓ} → Dec A → Dec (¬ A)
not? (yes p) = no (_$ p)
not? (no ¬p) = yes ¬p

decide! : ∀ {ℓ} {A : Type ℓ} ⦃ d : Dec A ⦄ {_ : is-yes d} → A
decide! ⦃ yes x ⦄ = x
```
-->
