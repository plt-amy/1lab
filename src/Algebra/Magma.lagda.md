<!--
```agda
open import 1Lab.Prelude
```
-->

```agda
module Algebra.Magma where
```

<!--
```agda
private variable
  ℓ ℓ₁ : Level
  A : Type ℓ
```
-->

# ∞-Magmas {defines="magma ∞-magma"}

In common mathematical parlance, a **magma** is a set equipped with a
binary operation. In HoTT, we free ourselves from considering sets as a
primitive, and generalise to ∞-groupoids: An **∞-magma** is a _type_
equipped with a binary operation.

```agda
is∞Magma : Type ℓ → Type ℓ
is∞Magma X = X → X → X
```

Since we can canonically identify the predicate `is∞Magma`{.Agda} with a
`Structure`{.Agda} built with the structure language, we automatically
get a notion of ∞-Magma homomorphism, and a proof that
`∞MagmaStr`{.Agda} is a `univalent structure`{.Agda ident=is-univalent}.

```agda
∞MagmaStr : Structure ℓ is∞Magma
∞MagmaStr = Term→structure (s∙ s→ (s∙ s→ s∙))

∞MagmaStr-univ : is-univalent (∞MagmaStr {ℓ = ℓ})
∞MagmaStr-univ = Term→structure-univalent (s∙ s→ (s∙ s→ s∙))
```

∞-magmas form a viable structure because magmas (and therefore their
higher version) do not axiomatize any _paths_ that would require
further coherence conditions. However, when considering structures with
equalities, like semigroups or loops, we must restrict ourselves to sets
to get a reasonable object, hence the field `has-is-set`{.Agda}.
To be able to properly generalize over these notions, we define magmas
as ∞-magmas whose carrier type is a set.

# Magmas
```agda
record is-magma {A : Type ℓ} (_⋆_ : A → A → A) : Type ℓ where
```

A **magma** is a `set`{.Agda ident=is-set} equipped with an arbitrary
binary operation `⋆`, on which no further laws are imposed.

```agda
  field
    has-is-set : is-set A

  underlying-set : Set ℓ
  underlying-set = el _ has-is-set

  instance
    magma-hlevel : ∀ {n} → H-Level A (2 + n)
    magma-hlevel = basic-instance 2 has-is-set

open is-magma public
```

Note that we do not generally benefit from the [[set truncation]] of
arbitrary magmas - however, practically all structures built upon
`is-magma`{.Agda} do, since they contain paths which would require
complicated, if not outright undefinable, coherence conditions.

It also allows us to show that being a magma is a _property_:

```agda
is-magma-is-prop : {_⋆_ : A → A → A} → is-prop (is-magma _⋆_)
is-magma-is-prop x y i .has-is-set =
  is-hlevel-is-prop 2 (x .has-is-set) (y .has-is-set) i
```

By turning the operation parameter into an additional piece of data, we
get the notion of a **magma structure** on a type, as well as the
notion of a magma in general by doing the same to the carrier type.

```agda
record Magma-on (A : Type ℓ) : Type ℓ where
  field
    _⋆_ : A → A → A

    has-is-magma : is-magma _⋆_

  open is-magma has-is-magma public

Magma : (ℓ : Level) → Type (lsuc ℓ)
Magma ℓ = Σ (Type ℓ) Magma-on
```

We then define what it means for an equivalence between the carrier
types of two given magmas to be an **equivalence of magmas**: it has to
preserve the magma operation.

```agda
record
  Magma≃ (A B : Magma ℓ) (e : A .fst ≃ B .fst) : Type ℓ where
  private
    module A = Magma-on (A .snd)
    module B = Magma-on (B .snd)

  field
    pres-⋆ : (x y : A .fst) → e .fst (x A.⋆ y) ≡ e .fst x B.⋆ e .fst y

open Magma≃
```

<!--
```agda
_ = Str-desc
```
-->

## The boolean implication magma

```agda
open import Data.Bool
```

To give a somewhat natural example for a magma that is neither
associative, commutative, nor has a two-sided identity element,
consider `boolean implication`{.Agda imp}. Since the booleans form a
set, this obviously defines a magma:

```agda
private
  is-magma-imp : is-magma imp
  is-magma-imp .has-is-set = hlevel 2
```

We show it is not commutative or associative by giving counterexamples:

```agda
  imp-not-commutative : ¬ ((x y : Bool) → imp x y ≡ imp y x)
  imp-not-commutative commutative = true≠false (commutative false true)

  imp-not-associative : ¬ ((x y z : Bool) → imp x (imp y z) ≡ imp (imp x y) z)
  imp-not-associative associative = true≠false (associative false false false)
```

It also has no two-sided unit, as can be shown by case-splitting
on the candidates:

```agda
  imp-not-unital
    : (x : Bool) → ((y : Bool) → imp x y ≡ y) → ¬ ((y : Bool) → imp y x ≡ y)
  imp-not-unital false left-unital right-unital = true≠false (right-unital false)
  imp-not-unital true left-unital right-unital = true≠false (right-unital false)
```
