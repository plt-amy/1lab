---
description: |
  Concrete categories
---
<!--
```agda
open import 1Lab.Reflection

open import Cat.Functor.Properties
open import Cat.Prelude

open import Data.Nat.Base

open import Meta.Foldable

import Cat.Reasoning
```
-->
```agda
module Cat.Functor.Concrete where
```

# Concrete categories {defines="concrete-category"}

A category $\cC$ is **concrete** if it comes equipped with a faithful
functor into $\Sets$.

```agda
module _ {o ℓ} (C : Precategory o ℓ) where
  open Cat.Reasoning C

  record Concrete (κ : Level) : Type (o ⊔ ℓ ⊔ lsuc κ) where
    no-eta-equality
    field
      Forget : Functor C (Sets κ)
      has-faithful : is-faithful Forget
```

## Constructing concrete categories

When we construct a category, we typically prove the associativity/unitality
conditions "by hand". However, this can be quite tedious for syntactic
presentations of categories, as it involves a large amount of induction.
However, these presentations are often meant to present some
category of structured functions between sets: if the presentation is
injective, then we can derive the category laws by simply lifting the
good definitional behaviour of functions along the presentation function.

The following record contains the data required to perform this trick.

```agda
record make-concrete
  {o ℓ : Level}
  (Ob : Type o) (Hom : Ob → Ob → Type ℓ)
  : Typeω
  where
  no-eta-equality
  field
    id : ∀ {x} → Hom x x
    _∘_ : ∀ {x y z} → Hom y z → Hom x y → Hom x z

    {lvl} : Level
    F₀ : Ob → Type lvl
    F₀-is-set : ∀ {x} → is-set (F₀ x)

    F₁ : ∀ {x y} → Hom x y → F₀ x → F₀ y
    F₁-inj : ∀ {x y} {f g : Hom x y} → (∀ a → F₁ f a ≡ F₁ g a) → f ≡ g
    F-id : ∀ {x} → (a : F₀ x) → F₁ id a ≡ a
    F-∘ : ∀ {x y z} (f : Hom y z) (g : Hom x y) (a : F₀ x) → F₁ (f ∘ g) a ≡ F₁ f (F₁ g a)
```

We can show that our putative hom sets are actually sets by lifting
the hlevel proof along the injection.

```agda
  abstract
    make-is-set
      : ∀ x y → is-set (Hom x y)
    make-is-set x y = injective→is-set (F₁-inj ⊙ happly) (fun-is-hlevel 2 F₀-is-set)
```

Likewise, all equations can be lifted as well.

```agda
    make-idl
      : ∀ {x y} (f : Hom x y)
      → id ∘ f ≡ f
    make-idl f = F₁-inj λ a →
      F₁ (id ∘ f) a  ≡⟨ F-∘ id f a ⟩
      F₁ id (F₁ f a) ≡⟨ F-id (F₁ f a) ⟩
      F₁ f a ∎

    make-idr
      : ∀ {x y} (f : Hom x y)
      → f ∘ id ≡ f
    make-idr f = F₁-inj λ a →
      F₁ (f ∘ id) a  ≡⟨ F-∘ f id a ⟩
      F₁ f (F₁ id a) ≡⟨ ap (F₁ f) (F-id a) ⟩
      F₁ f a         ∎

    make-assoc
      : ∀ {w x y z} (f : Hom y z) (g : Hom x y) (h : Hom w x)
      → f ∘ (g ∘ h) ≡ (f ∘ g) ∘ h
    make-assoc f g h = F₁-inj λ a →
      F₁ (f ∘ (g ∘ h)) a   ≡⟨ F-∘ f (g ∘ h) a ∙ ap (F₁ f) (F-∘ g h a) ⟩
      F₁ f (F₁ g (F₁ h a)) ≡˘⟨ F-∘ (f ∘ g) h a ∙ F-∘ f g (F₁ h a) ⟩
      F₁ ((f ∘ g) ∘ h) a   ∎
```

Used naively, `make-concrete`{.Agda} would result in unreadable goals. To avoid
this, we provide macros that expand out the proofs in `make-concrete`{.Agda}
into a top-level definition implemented via copattern matching.

```agda
define-concrete-category
  : ∀ {o ℓ} {Ob : Type o} {Hom : Ob → Ob → Type ℓ}
  → Name → make-concrete Ob Hom → TC ⊤

declare-concrete-category
  : ∀ {o ℓ} {Ob : Type o} {Hom : Ob → Ob → Type ℓ}
  → Name → make-concrete Ob Hom → TC ⊤
```

<details>
<summary>The details of the macro are omitted to spare the innocent reader.
</summary>

```agda
make-concrete-category
  : ∀ {o ℓ} {Ob : Type o} {Hom : Ob → Ob → Type ℓ}
  → Bool → Name → make-concrete Ob Hom → TC Name
make-concrete-category {o} {ℓ} {Ob} {Hom} declare? nm mk = do
  `mk ← quoteωTC mk
  `O ← quoteTC Ob
  `H ← quoteTC Hom

  ty ← quoteTC (Precategory o ℓ)
  case declare? of λ where
    true → declare (argN nm) ty
    false → pure tt

  -- Need to use field projections to avoid issues with implicit instantiation.
  define-function nm $
    clause [] [ argN (proj (quote Precategory.Ob)) ] `O ∷
    clause [] [ argN (proj (quote Precategory.Hom)) ] `H ∷
    clause
      []
      [ argN (proj (quote Precategory.Hom-set)) ]
      (def (quote make-is-set) [ argN `mk ]) ∷
    clause
      (implicits `O ["x"])
      (argN (proj (quote Precategory.id)) ∷ implicit-patterns 1)
      (def (quote id) [ argN `mk , argH (var 0 []) ]) ∷
    clause
      (implicits `O ["x", "y", "z"])
      (argN (proj (quote Precategory._∘_)) ∷ implicit-patterns 3)
      (def (quote _∘_) [ argN `mk , argH (var 2 []) , argH (var 1 []) , argH (var 0 []) ]) ∷
    clause
      (implicits `O ["x", "y"])
      (argN (proj (quote Precategory.idr)) ∷ implicit-patterns 2)
      (def (quote make-idr) [ argN `mk ,  argH (var 1 []) , argH (var 0 []) ]) ∷
    clause
      (implicits `O ["x", "y"])
      (argN (proj (quote Precategory.idl)) ∷ implicit-patterns 2)
      (def (quote make-idl) [ argN `mk ,  argH (var 1 []) , argH (var 0 []) ]) ∷
    clause
      (implicits `O ["w", "x", "y", "z"])
      (argN (proj (quote Precategory.assoc)) ∷ implicit-patterns 4)
      (def (quote make-assoc) [ argN `mk , argH (var 3 []) , argH (var 2 []) , argH (var 1 []) , argH (var 0 []) ]) ∷
    []
  pure nm
  where
    open make-concrete

    implicits : Term → List String → Telescope
    implicits ty = map (_, argH ty)

    implicit-patterns : Nat → List (Arg Pattern)
    implicit-patterns 0 = []
    implicit-patterns (suc n) = argH (var n) ∷ implicit-patterns n

    implicit-args : Nat → List (Arg Term)
    implicit-args 0 = []
    implicit-args (suc n) = argH (var n []) ∷ implicit-args n

declare-concrete-category nm mk = do
  make-concrete-category true nm mk
  pure tt

define-concrete-category nm mk = do
  make-concrete-category false nm mk
  pure tt
```
</details>
