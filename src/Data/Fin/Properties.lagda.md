<!--
```agda
open import 1Lab.Function.Antisurjection
open import 1Lab.Function.Antiinjection
open import 1Lab.Prelude

open import Data.Dec.Base
open import Data.Fin.Base

import Data.Nat.Order as Nat
import Data.Nat.Base as Nat
```
-->

```agda
module Data.Fin.Properties where
```

# Finite sets - properties

## Ordering

As noted in [`Data.Fin.Base`], we've set up the ordering on `Fin` so that
we can re-use all the proofs about the ordering on `Nat`{.Agda}.

[`Data.Fin.Base`]: Data.Fin.Base.html

However, there are still quite a few interesting things one can say about
`skip`{.Agda} and `squish`{.Agda}. In particular, we can prove the
*simplicial identities*, which characterize the interactions between
these two functions.

These lemmas might seem somewhat arbitrary and complicated, which
is true! However, they are enough to describe all the possible
interactions of `skip`{.Agda} and `squish`{.Agda}, which in turn
are the building blocks for _every_ monotone function between
`Fin`{.Agda}, so it's not that surprising that they would be a bit
of a mess!

<!-- [TODO: Reed M, 23/02/2022] Link to Simplicial Sets Stuff -->

```agda
skip-comm : ∀ {n} (i j : Fin (suc n)) → i ≤ j
          → ∀ x → skip (weaken i) (skip j x) ≡ skip (fsuc j) (skip i x)
skip-comm fzero    j        le x        = refl
skip-comm (fsuc i) (fsuc j) le fzero    = refl
skip-comm (fsuc i) (fsuc j) (Nat.s≤s le) (fsuc x) = ap fsuc (skip-comm i j le x)

drop-comm : ∀ {n} (i j : Fin n) → i ≤ j
          → ∀ x → squish j (squish (weaken i) x) ≡ squish i (squish (fsuc j) x)
drop-comm fzero    fzero    le fzero = refl
drop-comm fzero    fzero    le (fsuc x) = refl
drop-comm fzero    (fsuc j) le fzero = refl
drop-comm fzero    (fsuc j) le (fsuc x) = refl
drop-comm (fsuc i) (fsuc j) le fzero = refl
drop-comm (fsuc i) (fsuc j) (Nat.s≤s le) (fsuc x) = ap fsuc (drop-comm i j le x)

squish-skip-comm : ∀ {n} (i : Fin (suc n)) (j : Fin n) → i < fsuc j
                 → ∀ x → squish (fsuc j) (skip (weaken i) x) ≡ skip i (squish j x)
squish-skip-comm fzero j (Nat.s≤s p) x = refl
squish-skip-comm (fsuc i) (fsuc j) (Nat.s≤s p) fzero = refl
squish-skip-comm (fsuc i) (fsuc j) (Nat.s≤s p) (fsuc x) =
  ap fsuc (squish-skip-comm i j p x)

squish-skip : ∀ {n} (i j : Fin n) → i ≡ j
            → ∀ x → squish j (skip (weaken j) x) ≡ x
squish-skip fzero fzero p x = refl
squish-skip fzero (fsuc j) p x = absurd (fzero≠fsuc p)
squish-skip (fsuc i) fzero p x = refl
squish-skip (fsuc i) (fsuc j) p fzero = refl
squish-skip (fsuc i) (fsuc j) p (fsuc x) = ap fsuc (squish-skip i j (fsuc-inj p) x)

squish-skip-fsuc : ∀ {n} (i : Fin (suc n)) (j : Fin n) → i ≡ fsuc j
                 → ∀ x → squish j (skip i x) ≡ x
squish-skip-fsuc fzero fzero p x = refl
squish-skip-fsuc fzero (fsuc j) p x = absurd (fzero≠fsuc p)
squish-skip-fsuc (fsuc i) fzero p fzero = refl
squish-skip-fsuc (fsuc fzero) fzero p (fsuc x) = refl
squish-skip-fsuc (fsuc (fsuc i)) fzero p (fsuc x) =
  absurd (fzero≠fsuc (fsuc-inj (sym p)))
squish-skip-fsuc (fsuc i) (fsuc j) p fzero = refl
squish-skip-fsuc (fsuc i) (fsuc j) p (fsuc x) =
  ap fsuc (squish-skip-fsuc i j (fsuc-inj p) x)

Fin-peel : ∀ {l k} → Fin (suc l) ≃ Fin (suc k) → Fin l ≃ Fin k
Fin-peel {l} {k} sl≃sk = (Iso→Equiv (l→k , (iso k→l b→a→b a→b→a))) where
  sk≃sl : Fin (suc k) ≃ Fin (suc l)
  sk≃sl = sl≃sk e⁻¹
  module sl≃sk = Equiv sl≃sk
  module sk≃sl = Equiv sk≃sl

  l→k : Fin l → Fin k
  l→k x with inspect (sl≃sk.to (fsuc x))
  ... | fsuc y , _ = y
  ... | fzero , p with inspect (sl≃sk.to fzero)
  ... | fsuc y , _ = y
  ... | fzero , q = absurd (fzero≠fsuc (sl≃sk.injective₂ q p))

  k→l : Fin k → Fin l
  k→l x with inspect (sk≃sl.to (fsuc x))
  ... | fsuc x , _ = x
  ... | fzero , p with inspect (sk≃sl.to fzero)
  ... | fsuc y , _ = y
  ... | fzero , q = absurd (fzero≠fsuc (sk≃sl.injective₂ q p))

  absurd-path : ∀ {ℓ} {A : Type ℓ} {y : A} .{x : ⊥} → absurd x ≡ y
  absurd-path {x = ()}

  a→b→a : ∀ a → k→l (l→k a) ≡ a
  a→b→a a with inspect (sl≃sk.to (fsuc a))
  a→b→a a | fsuc x , p' with inspect (sk≃sl.to (fsuc x))
  a→b→a a | fsuc x , p' | fsuc y , q' = fsuc-inj (
    sym q' ∙ ap (sk≃sl.to) (sym p') ∙ sl≃sk.η _)
  a→b→a a | fsuc x , p' | fzero , q' = absurd contra where
    r = sl≃sk.injective₂ p' (sl≃sk.ε (fsuc x))
    contra = fzero≠fsuc (sym (r ∙ q'))
  a→b→a a | fzero , p' with inspect (sl≃sk.to fzero)
  a→b→a a | fzero , p' | fsuc x , q' with inspect (sk≃sl.to (fsuc x))
  a→b→a a | fzero , p' | fsuc x , q' | fsuc y , r' = absurd do
    fzero≠fsuc (sym (sym r' ∙ ap sk≃sl.to (sym q') ∙ sl≃sk.η fzero))
  a→b→a a | fzero , p' | fsuc x , q' | fzero , r' with inspect (sk≃sl.to fzero)
  a→b→a a | fzero , p' | fsuc x , q' | fzero , r' | fsuc z , s = fsuc-inj $
    sym s ∙ ap sk≃sl.to (sym p') ∙ sl≃sk.η (fsuc a)
  a→b→a a | fzero , p' | fsuc x , q' | fzero , r' | fzero , s = absurd-path
  a→b→a a | fzero , p' | fzero , q' = absurd (fzero≠fsuc $
    sl≃sk.injective₂ q' p')

  b→a→b : ∀ b → l→k (k→l b) ≡ b
  b→a→b b with inspect (sk≃sl.to (fsuc b))
  b→a→b b | fsuc x , p' with inspect (sl≃sk.to (fsuc x))
  b→a→b b | fsuc x , p' | fsuc y , q' = fsuc-inj $
    sym q' ∙ ap (sl≃sk.to) (sym p') ∙ sk≃sl.η _
  b→a→b b | fsuc x , p' | fzero , q' = absurd contra where
    r = sk≃sl.injective₂ p' (sk≃sl.ε (fsuc x))
    contra = fzero≠fsuc (sym (r ∙ q'))
  b→a→b b | fzero , p' with inspect (sk≃sl.to fzero)
  b→a→b b | fzero , p' | fsuc x , q' with inspect (sl≃sk.to (fsuc x))
  b→a→b b | fzero , p' | fsuc x , q' | fsuc y , r'  = absurd (fzero≠fsuc $
    sym (sym r' ∙ ap (sl≃sk.to) (sym q') ∙ sk≃sl.η _))
  b→a→b b | fzero , p' | fsuc x , q' | fzero , r' with inspect (sl≃sk.to fzero)
  b→a→b a | fzero , p' | fsuc x , q' | fzero , r' | fsuc z , s = fsuc-inj $
    sym s ∙ ap (sl≃sk.to) (sym p') ∙ sk≃sl.η (fsuc a)
  b→a→b a | fzero , p' | fsuc x , q' | fzero , r' | fzero , s = absurd-path
  b→a→b b | fzero , p' | fzero , q' = absurd (fzero≠fsuc $
    sk≃sl.injective₂ q' p')

Fin-injective : ∀ {l k} → Fin l ≃ Fin k → l ≡ k
Fin-injective {zero} {zero} l≃k = refl
Fin-injective {zero} {suc k} l≃k with equiv→inverse (l≃k .snd) fzero
... | ()
Fin-injective {suc l} {zero} l≃k with l≃k .fst fzero
... | ()
Fin-injective {suc l} {suc k} sl≃sk = ap suc $ Fin-injective (Fin-peel sl≃sk)

to-from-ℕ< : ∀ {n} (x : ℕ< n) → to-ℕ< {n = n} (from-ℕ< x) ≡ x
to-from-ℕ< {n = suc n} x = Σ-prop-path! (to-from-ℕ {n = suc n} x) where
  to-from-ℕ : ∀ {n} x → to-nat {n = n} (from-ℕ< x) ≡ x .fst
  to-from-ℕ {n = suc n} (zero , p) = refl
  to-from-ℕ {n = suc n} (suc x , Nat.s≤s p) = ap suc (to-from-ℕ {n = n} (x , p))

from-to-ℕ< : ∀ {n} (x : Fin n) → from-ℕ< (to-ℕ< x) ≡ x
from-to-ℕ< fzero = refl
from-to-ℕ< (fsuc x) = ap fsuc (from-to-ℕ< x)

Fin≃ℕ< : ∀ {n} → Fin n ≃ ℕ< n
Fin≃ℕ< {n} = to-ℕ< , is-iso→is-equiv (iso from-ℕ< (to-from-ℕ< {n}) from-to-ℕ<)

avoid-injective
  : ∀ {n} (i : Fin (suc n)) {j k : Fin (suc n)} {i≠j : ¬ i ≡ j} {i≠k : ¬ i ≡ k}
  → avoid i j i≠j ≡ avoid i k i≠k → j ≡ k
avoid-injective fzero {fzero} {k} {i≠j} p = absurd (i≠j refl)
avoid-injective fzero {fsuc j} {fzero} {i≠k = i≠k} p = absurd (i≠k refl)
avoid-injective {suc n} fzero {fsuc j} {fsuc k} p = ap fsuc p
avoid-injective {suc n} (fsuc i) {fzero} {fzero} p = refl
avoid-injective {suc n} (fsuc i) {fzero} {fsuc k} p = absurd (fzero≠fsuc p)
avoid-injective {suc n} (fsuc i) {fsuc j} {fzero} p = absurd (fzero≠fsuc (sym p))
avoid-injective {suc n} (fsuc i) {fsuc j} {fsuc k} p =
  ap fsuc (avoid-injective {n} i {j} {k} (fsuc-inj p))
```

## Finite choice {defines="finite-choice"}

An important fact about the [[(standard) finite sets|standard finite
sets]] in constructive mathematics is that they _always_ support choice,
which we phrase below as a "search" operator: If $M$ is any extension
system (for example, the [[propositional truncation]] monad), then $M$
commutes with finite products:

```agda
finite-choice
  : ∀ {ℓ} n {A : Fin n → Type ℓ} {M}
      (let module M = Effect M)
  → ⦃ Idiom M ⦄
  → (∀ x → M.₀ (A x)) → M.₀ (∀ x → A x)
finite-choice zero _        = pure λ ()
finite-choice (suc n) {A} k = ⦇ elim (k fzero) (finite-choice n (k ∘ fsuc)) ⦈
  where
    elim : A fzero → (∀ x → A (fsuc x)) → ∀ x → A x
    elim azero asuc fzero = azero
    elim azero asuc (fsuc x) = asuc x
```

An immediate consequence is that surjections into a finite set (thus,
_between_ finite sets) [[merely]] split:

```agda
finite-surjection-split
  : ∀ {ℓ} {n} {B : Type ℓ}
  → (f : B → Fin n) → is-surjective f
  → ∥ (∀ x → fibre f x) ∥
finite-surjection-split f = finite-choice _
```

## Injections and surjections

The standard finite sets are **Dedekind-finite**, which means that every
injection $[n] \mono [n]$ is a bijection. We prove this by a straightforward
but annoying induction on $n$.

```agda
Fin-injection→equiv
  : ∀ {n} (f : Fin n → Fin n)
  → injective f → is-equiv f
Fin-injection→equiv {zero} f inj .is-eqv ()
Fin-injection→equiv {suc n} f inj .is-eqv i with f 0 ≡? i
... | yes p = contr (0 , p) λ (j , p') → Σ-prop-path! (inj (p ∙ sym p'))
... | no ¬p = contr
  (fsuc (rec .centre .fst) , avoid-injective (f 0) (rec .centre .snd))
  λ where
    (fzero , p) → absurd (¬p p)
    (fsuc j , p) → Σ-prop-path! (ap (fsuc ∘ fst)
      (rec .paths (j , ap₂ (avoid (f 0)) p prop!)))
  where
    rec = Fin-injection→equiv {n}
      (λ x → avoid (f 0) (f (fsuc x)) (fzero≠fsuc ∘ inj))
      (λ p → fsuc-inj (inj (avoid-injective (f 0) p)))
      .is-eqv (avoid (f 0) i ¬p)
```

Since [[every surjection between finite sets splits|finite choice]], any
surjection $f : [n] \epi [n]$ has an injective right inverse, which is thus
a bijection; by general properties of equivalences, this implies that $f$ is
also a bijection.

```agda
Fin-surjection→equiv
  : ∀ {n} (f : Fin n → Fin n)
  → is-surjective f → is-equiv f
Fin-surjection→equiv f surj = case finite-surjection-split f surj of λ split →
  left-inverse→equiv (snd ∘ split)
    (Fin-injection→equiv (fst ∘ split)
      (right-inverse→injective f (snd ∘ split)))
```

## Vector operations

```agda
avoid-insert
  : ∀ {n} {ℓ} {A : Type ℓ}
  → (ρ : Fin n → A)
  → (i : Fin (suc n)) (a : A)
  → (j : Fin (suc n))
  → (i≠j : ¬ i ≡ j)
  → (ρ [ i ≔ a ]) j ≡ ρ (avoid i j i≠j)
avoid-insert {n = n} ρ fzero a fzero i≠j = absurd (i≠j refl)
avoid-insert {n = suc n} ρ fzero a (fsuc j) i≠j = refl
avoid-insert {n = suc n} ρ (fsuc i) a fzero i≠j = refl
avoid-insert {n = suc n} ρ (fsuc i) a (fsuc j) i≠j =
  avoid-insert (ρ ∘ fsuc) i a j (i≠j ∘ ap fsuc)

insert-lookup
  : ∀ {n} {ℓ} {A : Type ℓ}
  → (ρ : Fin n → A)
  → (i : Fin (suc n)) (a : A)
  → (ρ [ i ≔ a ]) i ≡ a
insert-lookup {n = n} ρ fzero a = refl
insert-lookup {n = suc n} ρ (fsuc i) a = insert-lookup (ρ ∘ fsuc) i a

delete-insert
  : ∀ {n} {ℓ} {A : Type ℓ}
  → (ρ : Fin n → A)
  → (i : Fin (suc n)) (a : A)
  → ∀ j → delete (ρ [ i ≔ a ]) i j ≡ ρ j
delete-insert ρ fzero a j = refl
delete-insert ρ (fsuc i) a fzero = refl
delete-insert ρ (fsuc i) a (fsuc j) = delete-insert (ρ ∘ fsuc) i a j

insert-delete
  : ∀ {n} {ℓ} {A : Type ℓ}
  → (ρ : Fin (suc n) → A)
  → (i : Fin (suc n)) (a : A)
  → ρ i ≡ a
  → ∀ j → ((delete ρ i) [ i ≔ a ]) j ≡ ρ j
insert-delete {n = n} ρ fzero a p fzero = sym p
insert-delete {n = n} ρ fzero a p (fsuc j) = refl
insert-delete {n = suc n} ρ (fsuc i) a p fzero = refl
insert-delete {n = suc n} ρ (fsuc i) a p (fsuc j) = insert-delete (ρ ∘ fsuc) i a p j
```

<!--
```agda
to-nat-inj
  : ∀ {n} {i j : Fin n}
  → to-nat i ≡ to-nat j
  → i ≡ j
to-nat-inj {i = fzero} {j = fzero} p = refl
to-nat-inj {i = fzero} {j = fsuc j} p = absurd (Nat.zero≠suc p)
to-nat-inj {i = fsuc i} {j = fzero} p = absurd (Nat.suc≠zero p)
to-nat-inj {i = fsuc i} {j = fsuc j} p = ap fsuc (to-nat-inj (Nat.suc-inj p))

to-from-nat : ∀ n → to-nat (from-nat n) ≡ n
to-from-nat zero = refl
to-from-nat (suc n) = ap suc (to-from-nat n)

from-nat-pres-≤
  : ∀ {m n}
  → m Nat.≤ n
  → to-nat (from-nat m) Nat.≤ to-nat (from-nat n)
from-nat-pres-≤ {m} {n} p = Nat.cast-≤ (sym (to-from-nat m)) (sym (to-from-nat n)) p

from-nat-top
  : ∀ {n}
  → (i : Fin (suc n))
  → i ≤ from-nat n
from-nat-top {n = n} fzero = Nat.0≤x
from-nat-top {n = suc n} (fsuc i) = Nat.s≤s (from-nat-top i)

to-nat-weaken-≤
  : ∀ {m n n'}
  → (p : m Nat.≤ n) (q : m Nat.≤ n') (i : Fin m)
  → to-nat (weaken-≤ p i) ≡ to-nat (weaken-≤ q i)
to-nat-weaken-≤ (Nat.s≤s p) (Nat.s≤s q) fzero = refl
to-nat-weaken-≤ (Nat.s≤s p) (Nat.s≤s q) (fsuc i) = ap suc (to-nat-weaken-≤ p q i)
```
-->

<!--
```agda
Finite-one-is-prop : is-prop (Fin 1)
Finite-one-is-prop fzero fzero = refl
```
-->

<!--
```agda
fkeep-id : ∀ {n} → ∀ (i : Fin (suc n)) → fkeep (λ x → x) i ≡ i
fkeep-id fzero = refl
fkeep-id (fsuc i) = refl

fkeep-∘
  : ∀ {m n o}
  → {f : Fin n → Fin o} {g : Fin m → Fin n}
  → ∀ i → fkeep (f ∘ g) i ≡ fkeep f (fkeep g i)
fkeep-∘ fzero = refl
fkeep-∘ (fsuc i) = refl

fkeep-inj : ∀ {m n} → injective (fkeep {m} {n})
fkeep-inj p = ext λ i → fsuc-inj (p $ₚ fsuc i)

fkeep-split-antisurj
  : ∀ {m n} {f : Fin m → Fin n}
  → split-antisurjective f
  → split-antisurjective (fkeep f)
fkeep-split-antisurj (i , ¬fib) = fsuc i , λ where
  (fzero , p) → fzero≠fsuc p
  (fsuc i , p) → ¬fib (i , fsuc-inj p)

fkeep-split-antiinj
  : ∀ {m n} {f : Fin m → Fin n}
  → split-antiinjective f
  → split-antiinjective (fkeep f)
fkeep-split-antiinj {f = f} f-ai = fkeep-antiinj where
  open split-antiinjective

  fkeep-antiinj : split-antiinjective (fkeep f)
  fkeep-antiinj .pt = fsuc (f-ai .pt)
  fkeep-antiinj .x₀ = fsuc (f-ai .x₀)
  fkeep-antiinj .x₁ = fsuc (f-ai .x₁)
  fkeep-antiinj .map-to₀ = ap fsuc (f-ai .map-to₀)
  fkeep-antiinj .map-to₁ = ap fsuc (f-ai .map-to₁)
  fkeep-antiinj .distinct = f-ai .distinct ∘ fsuc-inj

fkeep-fzero
  : ∀ {m n} {f : Fin m → Fin n}
  → ∀ i → fkeep f i ≡ fzero → i ≡ fzero
fkeep-fzero fzero p = refl
fkeep-fzero (fsuc i) p = absurd (fsuc≠fzero p)

fkeep-fpred
  : ∀ {m n} {f : Fin (suc m) → Fin (suc n)}
  → ∀ i → ¬ (i ≡ 0) → fpred (fkeep f i) ≡ f (fpred i)
fkeep-fpred fzero i≠0 = absurd (i≠0 refl)
fkeep-fpred (fsuc i) i≠0 = refl

fpred-nonzero-inj
  : ∀ {n} {i j : Fin (suc (suc n))}
  → ¬ (i ≡ 0) → ¬ (j ≡ 0)
  → fpred i ≡ fpred j
  → i ≡ j
fpred-nonzero-inj {i = fzero} {j = j} i≠0 j≠0 p = absurd (i≠0 refl)
fpred-nonzero-inj {i = fsuc i} {j = fzero} i≠0 j≠0 p = absurd (j≠0 refl)
fpred-nonzero-inj {i = fsuc i} {j = fsuc j} i≠0 j≠0 p = ap fsuc p

open split-antiinjective

fkeep-reflect-split-antiinj-suc
  : ∀ {m n} {f : Fin (suc m) → Fin (suc n)}
  → split-antiinjective (fkeep f)
  → split-antiinjective f
fkeep-reflect-split-antiinj-suc {f = f} fkeep-antiinj = antiinj where
  abstract
    pt≠0 : ¬ (fkeep-antiinj .pt ≡ 0)
    pt≠0 p =
      fkeep-antiinj .distinct $
      fkeep-fzero _ (fkeep-antiinj .map-to₀ ∙ p)
      ∙ sym (fkeep-fzero _ (fkeep-antiinj .map-to₁ ∙ p))

    x₀≠0 : ¬ (fkeep-antiinj .x₀ ≡ 0)
    x₀≠0 p = pt≠0 $ sym (ap (fkeep f) (sym p) ∙ fkeep-antiinj .map-to₀)

    x₁≠0 : ¬ (fkeep-antiinj .x₁ ≡ 0)
    x₁≠0 p = pt≠0 $ sym (ap (fkeep f) (sym p) ∙ fkeep-antiinj .map-to₁)

  antiinj : split-antiinjective f
  antiinj .pt = fpred (fkeep-antiinj .pt)
  antiinj .x₀ = fpred (fkeep-antiinj .x₀)
  antiinj .x₁ = fpred (fkeep-antiinj .x₁)
  antiinj .map-to₀ =
    sym (fkeep-fpred {f = f} (fkeep-antiinj .x₀) x₀≠0)
    ∙ ap fpred (fkeep-antiinj .map-to₀)
  antiinj .map-to₁ =
    sym (fkeep-fpred {f = f} (fkeep-antiinj .x₁) x₁≠0)
    ∙ ap fpred (fkeep-antiinj .map-to₁)
  antiinj .distinct = fkeep-antiinj .distinct ∘ fpred-nonzero-inj x₀≠0 x₁≠0

fkeep-reflect-split-antiinj
  : ∀ {m n} {f : Fin m → Fin n}
  → split-antiinjective (fkeep f)
  → split-antiinjective f
fkeep-reflect-split-antiinj {m = zero} {n = n} {f = f} fkeep-antiinj =
  absurd (fkeep-antiinj .distinct (Finite-one-is-prop _ _))
fkeep-reflect-split-antiinj {m = suc m} {n = zero} {f = f} fkeep-antiinj =
  fabsurd (f 0)
fkeep-reflect-split-antiinj {m = suc m} {n = suc n} {f = f} fkeep-antiinj =
  fkeep-reflect-split-antiinj-suc fkeep-antiinj

fkeep-reflect-split-antisurj
  : ∀ {m n} {f : Fin m → Fin n}
  → split-antisurjective (fkeep f)
  → split-antisurjective f
fkeep-reflect-split-antisurj (fzero , ¬fib) = absurd (¬fib (0 , refl))
fkeep-reflect-split-antisurj (fsuc b , ¬fib) = b , ¬fib ∘ Σ-map fsuc (ap fsuc)

fkeep-equiv
  : ∀ {m n} {f : Fin m → Fin n}
  → is-equiv f
  → is-equiv (fkeep f)
fkeep-equiv {m} {n} {f} f-eqv = is-iso→is-equiv (iso f⁻¹ f⁻¹→fkeep fkeep→f⁻¹)
  where
    f⁻¹ : Fin (suc n) → Fin (suc m)
    f⁻¹ fzero = fzero
    f⁻¹ (fsuc i) = fsuc (equiv→inverse f-eqv i)

    f⁻¹→fkeep : ∀ i → fkeep f (f⁻¹ i) ≡ i
    f⁻¹→fkeep fzero = refl
    f⁻¹→fkeep (fsuc i) = ap fsuc (equiv→counit f-eqv i)

    fkeep→f⁻¹ : ∀ i → f⁻¹ (fkeep f i) ≡ i
    fkeep→f⁻¹ fzero = refl
    fkeep→f⁻¹ (fsuc i) = ap fsuc (equiv→unit f-eqv i)
```
-->
