<!--
```agda
open import Prim.Extension
open import Prim.Interval
open import Prim.Type
```
-->

```agda
module Prim.Kan where
```

# Primitive: Kan operations

Using the machinery from the other `Prim` modules, we can define the Kan
operations: [transport] and [composition].

[transport]: 1Lab.Path.html#transport
[composition]: 1Lab.Path.html#composition

```agda
private module X where primitive
  primTransp : ∀ {ℓ} (A : (i : I) → Type (ℓ i)) (φ : I) (a : A i0) → A i1
  primHComp  : ∀ {ℓ} {A : Type ℓ} {φ : I} (u : ∀ i → Partial φ A) (a : A) → A
  primComp : ∀ {ℓ} (A : (i : I) → Type (ℓ i)) {φ : I} (u : ∀ i → Partial φ (A i)) (a : A i0) → A i1

open X public renaming (primTransp to transp)

hcomp
  : ∀ {ℓ} {A : Type ℓ} (φ : I)
  → (u : (i : I) → Partial (φ ∨ ~ i) A)
  → A
hcomp φ u = X.primHComp (λ j .o → u j (leftIs1 φ (~ j) o)) (u i0 1=1)

∂ : I → I
∂ i = i ∨ ~ i

comp
  : ∀ {ℓ : I → Level} (A : (i : I) → Type (ℓ i)) (φ : I)
  → (u : (i : I) → Partial (φ ∨ ~ i) (A i))
  → A i1
comp A φ u = X.primComp A (λ j .o → u j (leftIs1 φ (~ j) o)) (u i0 1=1)
```

We also define the type of dependent paths, and of non-dependent paths.

```agda
postulate
  PathP : ∀ {ℓ} (A : I → Type ℓ) → A i0 → A i1 → Type ℓ

{-# BUILTIN PATHP PathP #-}

infix 7 _≡_

_≡_ : ∀ {ℓ} {A : Type ℓ} → A → A → Type ℓ
_≡_ {A = A} = PathP (λ i → A)

{-# BUILTIN PATH _≡_ #-}
```

<!--
```agda
{-# BUILTIN REWRITE _≡_ #-}

caseⁱ_of_ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (x : A) → ((y : A) → x ≡ y → B) → B
caseⁱ x of f = f x (λ i → x)

caseⁱ_return_of_ : ∀ {ℓ ℓ'} {A : Type ℓ} (x : A) (P : A → Type ℓ') → ((y : A) → x ≡ y → P y) → P x
caseⁱ x return P of f = f x (λ i → x)

{-# INLINE caseⁱ_of_ #-}
{-# INLINE caseⁱ_return_of_ #-}
```
-->
