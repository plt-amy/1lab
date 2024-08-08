<!--
```agda
open import 1Lab.Prelude

open import Data.Wellfounded.Properties
open import Data.Wellfounded.Base
open import Data.Nat.Properties
open import Data.Nat.Divisible
open import Data.Nat.DivMod
open import Data.Nat.Order
open import Data.Dec.Base
open import Data.Nat.Base
open import Data.Sum.Base
```
-->

```agda
module Data.Nat.Divisible.GCD where
```

# Greatest common divisors {defines="greatest-common-divisor gcd"}

The **greatest common divisor** $\gcd(a,b)$ of a pair of natural numbers
is the largest number which [divides] them both. The definition we use
is _slightly_ unorthodox, since it requires only that the GCD be the
greatest _in the divisibility ordering_, but the divisibility ordering
is finer than the usual ordering, so this will turn out to imply they
are greatest in magnitude, as well.

[divides]: Data.Nat.Divisible.html

We start by defining what it means for a number to be a GCD --- that is,
we start by defining the *graph* of the function $\gcd$. Only after will
we show that such a function exists.

```agda
record is-gcd (x y : Nat) (gcd : Nat) : Type where
  field
    gcd-∣l : gcd ∣ x
    gcd-∣r : gcd ∣ y
    greatest : ∀ {g'} → g' ∣ x → g' ∣ y → g' ∣ gcd

open is-gcd

is-gcd-is-prop : ∀ {x y z} → is-prop (is-gcd x y z)
is-gcd-is-prop p q i .gcd-∣l = ∣-is-prop _ _ (p .gcd-∣l) (q .gcd-∣l) i
is-gcd-is-prop p q i .gcd-∣r = ∣-is-prop _ _ (p .gcd-∣r) (q .gcd-∣r) i
is-gcd-is-prop p q i .greatest a b = ∣-is-prop _ _ (p .greatest a b) (q .greatest a b) i

instance
  H-Level-is-gcd : ∀ {x y z n} → H-Level (is-gcd x y z) (suc n)
  H-Level-is-gcd = prop-instance is-gcd-is-prop

GCD : Nat → Nat → Type
GCD a b = Σ _ (is-gcd a b)

GCD-is-prop : ∀ {a b} → is-prop (GCD a b)
GCD-is-prop (_ , p) (_ , q) = Σ-prop-path! $
  ∣-antisym (q .greatest (p .gcd-∣l) (p .gcd-∣r)) (p .greatest (gcd-∣l q) (gcd-∣r q))

GCD-magnitude
  : ∀ {x y g : Nat}
  → is-gcd x y (suc g)
  → ∀ {g'} → g' ∣ x → g' ∣ y
  → g' ≤ suc g
GCD-magnitude gcd α β = m∣sn→m≤sn (gcd .greatest α β)
```

The following observations may seem trivial, but it will come in _super_
handy later: If $x | y$, then the GCD of $x$ and $y$ is $x$; Similarly,
the GCD function is "symmetric", meaning $\gcd(a,b) = \gcd(b,a)$.

```agda
divides→GCD : ∀ {x y} → x ∣ y → GCD x y
divides→GCD {x} {y} w = x , gcd where
  gcd : is-gcd x y x
  gcd .gcd-∣l = ∣-refl
  gcd .gcd-∣r = w
  gcd .greatest g'∣x g'∣y = g'∣x

GCD-sym : ∀ {x y} → GCD x y → GCD y x
GCD-sym w .fst = w .fst
GCD-sym w .snd .gcd-∣l = w .snd .gcd-∣r
GCD-sym w .snd .gcd-∣r = w .snd .gcd-∣l
GCD-sym w .snd .greatest g'∣y g'∣x = w .snd .greatest g'∣x g'∣y
```

## Euclid's algorithm

To compute greatest common divisors, we use the familiar (recursive)
Euclidean algorithm: $\gcd(a,0) = a$ and $\gcd(a, b) = \gcd(b, a \% b)$
otherwise. The difficulty comes in when we want not only to compute the
_numbers_ (in which case the definition above is perfectly cromulent),
but also to show that they are greatest common divisors.

```agda
module Euclid where
  private variable
    n m k d d' : Nat
```

The base case can be established using our existing functions:

```agda
  is-gcd-0 : is-gcd n 0 n
  is-gcd-0 .gcd-∣l = ∣-refl
  is-gcd-0 .gcd-∣r = ∣-zero
  is-gcd-0 .greatest g'∣n g∣n = g'∣n
```

The inductive step is a bit more complicated. We first have to establish
(using the most tedious of arithmetic properties) the following
properties of the divisibility relation:

- If $n$ is nonzero, $d|n$, and $d|(m \% n)$, then $d|m$;
- If $n$ is nonzero, $d|n$, and $d|m$, then $d|(m \% n)$.

These two facts, incarnated in the following helper lemmas `lem₁`{.Agda}
and `lem₂`{.Agda}, will allow us to compute the inductive step for GCD.

```agda
  private
    lem₁ : fibre (_* d) (suc n) → fibre (_* d) (m % suc n) → fibre (_* d) m
    lem₁ {d = d} {n} {m} (c₁ , p) (c₂ , q) = dm.q * c₁ + c₂ , r where
      module dm = DivMod (divide-pos m (suc n)) renaming (quot to q ; rem to r)
      r =
        (dm.q * c₁ + c₂) * d   ≡⟨ *-distrib-+r (dm.q * c₁) _ _ ⟩
        dm.q * c₁ * d + ⌜ c₂ * d ⌝ ≡⟨ ap! q ⟩
        ⌜ dm.q * c₁ * d ⌝ + dm.r   ≡⟨ ap! (*-associative dm.q c₁ d) ⟩
        dm.q * ⌜ c₁ * d ⌝ + dm.r   ≡⟨ ap! p ⟩
        dm.q * suc n + dm.r        ≡˘⟨ is-divmod m (suc n) ⟩
        m                          ∎

    lem₂ : fibre (_* d) (suc n) → fibre (_* d) m → fibre (_* d) (m % suc n)
    lem₂ {d = d} {n} {m} (c₁ , p) (c₂ , q) = c₂ - dm.q * c₁ , r where
      module dm = DivMod (divide-pos m (suc n)) renaming (quot to q ; rem to r)
      r = (c₂ - dm.q * c₁) * d                   ≡⟨ monus-distribr c₂ (dm.q * c₁) d ⟩
          c₂ * d - ⌜ dm.q * c₁ * d ⌝             ≡⟨ ap! (*-associative dm.q c₁ d ∙ ap (dm.q *_) p) ⟩
          ⌜ c₂ * d ⌝ - dm.q * suc n              ≡⟨ ap! (q ∙ is-divmod m (suc n)) ⟩
          ⌜ dm.q * suc n + dm.r ⌝ - dm.q * suc n ≡⟨ ap! (+-commutative (dm.q * suc n) dm.r) ⟩
          (dm.r + dm.q * suc n) - dm.q * suc n   ≡⟨ monus-cancelr dm.r 0 (dm.q * suc n) ⟩
          dm.r                                   ∎
```

That step is put together here: It says that, if ($n$ is nonzero and)
$\gcd(n, m \% n) = d$, then $\gcd(m, n) = d$, too --- so that it will
suffice to compute the former if we want the latter.

```agda
  is-gcd-step : is-gcd (suc n) (m % suc n) d → is-gcd m (suc n) d
  is-gcd-step x .gcd-∣l = fibre→∣ (lem₁ (∣→fibre (x .gcd-∣l)) (∣→fibre (x .gcd-∣r)))
  is-gcd-step x .gcd-∣r = x .gcd-∣l
  is-gcd-step x .greatest g'∣m g'∣sucn =
    x .greatest g'∣sucn (fibre→∣ (lem₂ (∣→fibre g'∣sucn) (∣→fibre g'∣m)))
```

Actually putting this together is a bit indirect, since we are not
performing structural induction: Agda can't see that the argument $m \%
n$ is less than $n$. We can, however, turn this into [well-founded
recursion], which demands only that the recursive call be _less_ (in the
sense of $<$) than the original input.

[well-founded recursion]: Data.Wellfounded.Base.html

```agda
  euclid-< : ∀ y x → x < y → GCD y x
  euclid-< = Wf-induction _ <-wf _ λ where
     x rec zero p    → x , is-gcd-0
     x rec (suc y) p →
      let (d , step) = rec (suc y) p (x % suc y) (x%y<y x (suc y))
       in d , is-gcd-step step

```

With a handy wrapper to put the arguments in the order our induction
worker `euclid-<`{.Agda} expects, we can create the `euclid`{.Agda}
function, together with its numerical component `gcd`{.Agda}, and a
proof that the graph of `gcd`{.Agda} is indeed `is-gcd`{.Agda}.

```agda
  euclid : ∀ x y → GCD x y
  euclid x y with ≤-split y x
  ... | inl y<x       = euclid-< x y y<x
  ... | inr (inl x<y) = GCD-sym (euclid-< y x x<y)
  ... | inr (inr y=x) = divides→GCD (subst (x ∣_) (sym y=x) ∣-refl)

gcd : Nat → Nat → Nat
gcd x y = Euclid.euclid x y .fst

is-gcd-graphs-gcd : ∀ {m n d} → is-gcd m n d ≃ (gcd m n ≡ d)
is-gcd-graphs-gcd {m = m} {n} {d} = prop-ext!
  (λ x → ap fst $ GCD-is-prop (gcd m n , Euclid.euclid m n .snd) (d , x))
  (λ p → subst (is-gcd m n) p (Euclid.euclid m n .snd))
```

## Euclid's lemma

```agda
|-*-coprime-cancel
  : ∀ n a b .⦃ _ : Positive n ⦄ .⦃ _ : Positive a ⦄
  → n ∣ a * b → is-gcd n a 1 → n ∣ b
|-*-coprime-cancel n a b div coprime = done where
  E : Nat → Prop lzero
  E x = el! (0 < x × n ∣ x * b)

  has : Σ[ x ∈ Nat ] ((x ∈ E) × (∀ y → (0 < y) × (n ∣ y * b) → x ≤ y))
  has = ℕ-well-ordered {P = E} (λ _ → auto) (inc (a , recover auto , div))

  instance
    _ : Positive (has .fst)
    _ = has .snd .fst .fst

  step : ∀ x → x ∈ E → has .fst ∣ x
  step x (xe , d) with divmod q r α β ← divide-pos x (has .fst) =
    let
      d' : n ∣ (q * has .fst * b + r * b)
      d' = subst (n ∣_) (ap (_* b) (recover α) ∙ *-distrib-+r (q * has .fst) r b) d

      d'' : n ∣ r * b
      d'' = ∣-+-cancel {n} {q * has .fst * b} {r * b} (subst (n ∣_) (sym (*-associative q (has .fst) b)) (|-*l-pres {a = q} (has .snd .fst .snd))) d'
    in case r ≡? 0 of λ where
      (yes p) → fibre→∣ (q , sym (recover α ∙ ap (q * has .fst +_) p ∙ +-zeror (q * has .fst)))
      (no ¬p) → absurd (<-irrefl
        (≤-antisym (≤-trans ≤-ascend (recover β)) (has .snd .snd r (nonzero→positive ¬p , d'')))
        (recover β))

  almost : has .fst ≡ 1
  almost = ∣-1 $ coprime .greatest {has .fst}
    (step n (recover auto , ∣-*l))
    (step a (recover auto , div))

  done : n ∣ b
  done = subst (n ∣_) (ap (_* b) almost ∙ *-onel b) (has .snd .fst .snd)
```
