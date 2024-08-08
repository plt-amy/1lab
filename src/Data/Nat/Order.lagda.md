<!--
```agda
open import 1Lab.Prelude

open import Data.Bool.Base
open import Data.Dec.Base
open import Data.Nat.Base
open import Data.Sum

import Prim.Data.Nat as Prim
```
-->

```agda
module Data.Nat.Order where
```

# Properties of ordering on ℕ

We establish the basic properties of ordering on the natural numbers.
These are properties of the order itself, and not how it interacts with
the semiring structure. For that, see
[`Data.Nat.Properties`](Data.Nat.Properties.html). The first thing we
establish is that $x \le y$ is a [[partial order]], so it deserves the
name $\le$: It is reflexive, transitive, antisymmetric, and takes values
in propositions. In all cases, save for reflexivity, the induction
happens on the witnesses of ordering, and Agda handles inducting on the
naturals automatically.

```agda
≤-refl : ∀ {x : Nat} → x ≤ x
≤-refl {zero}  = 0≤x
≤-refl {suc x} = s≤s ≤-refl
```

<!--
```agda
≤-refl' : ∀ {x y} → x ≡ y → x ≤ y
≤-refl' {zero} {zero} p = 0≤x
≤-refl' {zero} {suc y} p = absurd (zero≠suc p)
≤-refl' {suc x} {zero} p = absurd (suc≠zero p)
≤-refl' {suc x} {suc y} p = s≤s (≤-refl' (suc-inj p))
```
-->

```agda
≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
≤-trans 0≤x     0≤x     = 0≤x
≤-trans 0≤x     (s≤s q) = 0≤x
≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)

≤-antisym : ∀ {x y : Nat} → x ≤ y → y ≤ x → x ≡ y
≤-antisym 0≤x     0≤x     = refl
≤-antisym (s≤s p) (s≤s q) = ap suc (≤-antisym p q)

≤-is-prop : {x y : Nat} → is-prop (x ≤ y)
≤-is-prop 0≤x     0≤x     = refl
≤-is-prop (s≤s p) (s≤s q) = ap s≤s (≤-is-prop p q)
```

As a minor convenience, we prove that the constructor `s≤s`{.Agda} is an
equivalence between $x \le y$ and $(1 + x) \le (1 + y)$.

```agda
≤-peel : ∀ {x y : Nat} → suc x ≤ suc y → x ≤ y
≤-peel (s≤s p) = p

≤-sucr : ∀ {x y : Nat} → x ≤ y → x ≤ suc y
≤-sucr 0≤x = 0≤x
≤-sucr (s≤s p) = s≤s (≤-sucr p)

≤-ascend : ∀ {x} → x ≤ suc x
≤-ascend = ≤-sucr ≤-refl
```

<!--
```agda
private
  from-prim-< : ∀ x y → ⌞ x Prim.< y ⌟ → x < y
  from-prim-< zero (suc y) o = s≤s 0≤x
  from-prim-< (suc x) (suc y) o = s≤s (from-prim-< x y o)

  to-prim-< : ∀ x y → x < y → ⌞ x Prim.< y ⌟
  to-prim-< zero (suc y) o = oh
  to-prim-< (suc x) (suc y) o = to-prim-< x y (≤-peel o)

instance
  H-Level-≤ : ∀ {n x y} → H-Level (x ≤ y) (suc n)
  H-Level-≤ = prop-instance ≤-is-prop
```
-->

### Properties of the strict order

```agda
<-≤-asym : ∀ {x y} → x < y → ¬ (y ≤ x)
<-≤-asym {.(suc _)} {.(suc _)} (s≤s p) (s≤s q) = <-≤-asym p q

<-asym : ∀ {x y} → x < y → ¬ (y < x)
<-asym {.(suc _)} {.(suc _)} (s≤s p) (s≤s q) = <-asym p q

<-not-equal : ∀ {x y} → x < y → x ≠ y
<-not-equal {zero} (s≤s p) q = absurd (zero≠suc q)
<-not-equal {suc x} (s≤s p) q = <-not-equal p (suc-inj q)

<-irrefl : ∀ {x y} → x ≡ y → ¬ (x < y)
<-irrefl {suc x} {zero}  p      q  = absurd (suc≠zero p)
<-irrefl {zero}  {suc y} p      _  = absurd (zero≠suc p)
<-irrefl {suc x} {suc y} p (s≤s q) = <-irrefl (suc-inj p) q

<-weaken : ∀ {x y} → x < y → x ≤ y
<-weaken {x} {suc y} p = ≤-sucr (≤-peel p)

≤-strengthen : ∀ {x y} → x ≤ y → (x ≡ y) ⊎ (x < y)
≤-strengthen {zero} {zero} 0≤x = inl refl
≤-strengthen {zero} {suc y} 0≤x = inr (s≤s 0≤x)
≤-strengthen {suc x} {suc y} (s≤s p) with ≤-strengthen p
... | inl eq = inl (ap suc eq)
... | inr le = inr (s≤s le)

<-from-≤ : ∀ {x y} → x ≠ y → x ≤ y → x < y
<-from-≤ x≠y x≤y with ≤-strengthen x≤y
... | inl x=y = absurd (x≠y x=y)
... | inr x<y = x<y
```

### Linearity

Furthermore, `_≤_`{.Agda} is decidable, and weakly total:

<!--
```agda
module _ where private
```
-->

```agda
  ≤-dec : (x y : Nat) → Dec (x ≤ y)
  ≤-dec zero zero = yes 0≤x
  ≤-dec zero (suc y) = yes 0≤x
  ≤-dec (suc x) zero = no λ { () }
  ≤-dec (suc x) (suc y) with ≤-dec x y
  ... | yes x≤y = yes (s≤s x≤y)
  ... | no ¬x≤y = no (λ { (s≤s x≤y) → ¬x≤y x≤y })

≤-is-weakly-total : ∀ x y → ¬ (x ≤ y) → y ≤ x
≤-is-weakly-total zero    zero    _    = 0≤x
≤-is-weakly-total zero    (suc y) ¬0≤s = absurd (¬0≤s 0≤x)
≤-is-weakly-total (suc x) zero    _    = 0≤x
≤-is-weakly-total (suc x) (suc y) ¬s≤s = s≤s $
  ≤-is-weakly-total x y λ z → ¬s≤s (s≤s z)
```

<!--
```agda
<-from-not-≤ : ∀ x y → ¬ (x ≤ y) → y < x
<-from-not-≤ zero    zero    x    = absurd (x 0≤x)
<-from-not-≤ zero    (suc y) ¬0≤s = absurd (¬0≤s 0≤x)
<-from-not-≤ (suc x) zero    _    = s≤s 0≤x
<-from-not-≤ (suc x) (suc y) ¬s≤s = s≤s $
  <-from-not-≤ x y λ z → ¬s≤s (s≤s z)

≤-uncap : ∀ m n → m ≠ suc n → m ≤ suc n → m ≤ n
≤-uncap m n p 0≤x = 0≤x
≤-uncap (suc x) zero p (s≤s 0≤x) = absurd (p refl)
≤-uncap (suc x) (suc n) p (s≤s q) = s≤s (≤-uncap x n (p ∘ ap suc) q)
```
-->

<!--
```agda
≤-dec : (x y : Nat) → Dec (x ≤ y)
≤-dec x y with x ≡? y
... | yes x=y = yes (≤-refl' x=y)
... | no ¬x=y with oh? (x Prim.< y)
... | yes x<y = yes (<-weaken (from-prim-< x y x<y))
... | no ¬x<y  = no not-both where
  not-both : ¬ (x ≤ y)
  not-both p with ≤-strengthen p
  ... | inl x=y = ¬x=y x=y
  ... | inr x<y = ¬x<y (to-prim-< x y x<y)

instance
  Dec-≤ : ∀ {x y} → Dec (x ≤ y)
  Dec-≤ = ≤-dec _ _
```
-->

We also have that a successor is never smaller than the number it
succeeds:

```agda
¬sucx≤x : (x : Nat) → ¬ (suc x ≤ x)
¬sucx≤x (suc x) (s≤s ord) = ¬sucx≤x x ord
```

We can do proofs on pairs of natural numbers by splitting into cases of
their strict ordering:

```agda
≤-split : ∀ (x y : Nat) → (x < y) ⊎ (y < x) ⊎ (x ≡ y)
≤-split x y with ≤-dec (suc x) y
≤-split x y | yes x<y = inl x<y
≤-split x y | no x≥y with ≤-dec (suc y) x
≤-split x y | no x≥y | yes y<x = inr (inl y<x)
≤-split x y | no x≥y | no y≥x  = inr (inr (go x y x≥y y≥x)) where
  go : ∀ x y → ¬ (suc x ≤ y) → ¬ (suc y ≤ x) → x ≡ y
  go zero zero p q          = refl
  go zero (suc zero) p q    = absurd (p (s≤s 0≤x))
  go zero (suc (suc y)) p q = absurd (p (s≤s 0≤x))
  go (suc zero) zero p q    = absurd (q (s≤s 0≤x))
  go (suc (suc x)) zero p q = absurd (q (s≤s 0≤x))
  go (suc x) (suc y) p q    = ap suc (go x y (λ { a → p (s≤s a) }) λ { a → q (s≤s a) })
```

## Nat is a lattice

An interesting tidbit about the ordering on $\NN$ is that it is, in some
sense, generated by the max operator: We have $x \le y$ iff $max(x,y) =
y$. It can also be generated by the min operator, but we don't establish
that here (it is a more general fact about
[lattices](Order.Lattice.html)).

```agda
≤-iff-max : ∀ {x y} → (x ≤ y) ≃ (y ≡ max x y)
≤-iff-max = prop-ext! to from where
  to : ∀ {x y} → x ≤ y → y ≡ max x y
  to {.0} {zero} 0≤x = refl
  to {.0} {suc y} 0≤x = refl
  to {x} {y} (s≤s p) = ap suc (to p)

  from : ∀ {x y} → y ≡ max x y → x ≤ y
  from {zero} p = 0≤x
  from {suc x} {zero} p = absurd (zero≠suc p)
  from {suc x} {suc y} p = s≤s (from (suc-inj p))
```

## Well-ordering

In classical mathematics, the well-ordering principle states that every
nonempty subset of the natural numbers has a minimal element. In
constructive mathematics, there are subsets of $\bb{N}$ which only have
a minimal elements if excluded middle holds. The LEM-agnostic statement
is that every [[inhabited|propositional truncation]] [_complemented_]
subset of the natural numbers has a minimal element. Note that for a
complemented subset, inhabitation is the same as nonemptiness, but we
prefer the stronger phrasing since it makes the proof one step shorter.

[_complemented_]: Data.Power.Complemented.html

The "subset" part only comes in at the start: To get out from under the
truncation, we need the fact that minimal solutions are unique. Given a
minimal solution $(n, p)$ and one $(k, q')$, we have that $n = k$ since
both are minimal (so $k \le n$ and $n \le k$), but we do not^[We're
implicitly appealing to path induction to reduce this to the case where
$p, q : P(n)$] automatically have that $p = q$.

```agda
module _ {ℓ} {P : Nat → Prop ℓ} where
  private
    minimal-solution : ∀ {ℓ} (P : Nat → Type ℓ) → Type _
    minimal-solution P = Σ[ n ∈ Nat ] (P n × (∀ k → P k → n ≤ k))

    minimal-solution-unique : is-prop (minimal-solution λ x → ∣ P x ∣)
    minimal-solution-unique (n , pn , n-min) (k , pk , k-min) =
      Σ-prop-path! (≤-antisym (n-min _ pk) (k-min _ pn))
```

The step of the code that actually finds a minimal solution does not
need $P$ to be a predicate: we only need that for actually searching for
an inhabited subset.

```agda
    min-suc
      : ∀ {P : Nat → Type ℓ} → ∀ n → ¬ P 0
      → (∀ k → P (suc k) → n ≤ k)
      → ∀ k → P k → suc n ≤ k
    min-suc n ¬p0 nmins zero pk           = absurd (¬p0 pk)
    min-suc zero ¬p0 nmins (suc k) psk    = s≤s 0≤x
    min-suc (suc n) ¬p0 nmins (suc k) psk = s≤s (nmins k psk)

  ℕ-minimal-solution
    : ∀ (P : Nat → Type ℓ)
    → (∀ n → Dec (P n))
    → (n : Nat) → P n
    → minimal-solution P
  ℕ-minimal-solution P decp zero p = 0 , p , λ k _ → 0≤x
  ℕ-minimal-solution P decp (suc n) p = case decp zero of λ where
    (yes p0) → 0 , p0 , λ k _ → 0≤x
    (no ¬p0) →
      let (a , pa , x) = ℕ-minimal-solution (P ∘ suc) (decp ∘ suc) n p
       in suc a , pa , min-suc {P} a ¬p0 x

  ℕ-well-ordered
    : (∀ n → Dec ∣ P n ∣)
    → ∃[ n ∈ Nat ] ∣ P n ∣
    → Σ[ n ∈ Nat ] (∣ P n ∣ × (∀ k → ∣ P k ∣ → n ≤ k))
  ℕ-well-ordered P-dec wit = ∥-∥-rec minimal-solution-unique
    (λ { (n , p) → ℕ-minimal-solution _ P-dec n p }) wit
```
