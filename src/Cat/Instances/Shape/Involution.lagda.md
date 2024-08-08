<!--
```agda
open import Cat.Skeletal
open import Cat.Prelude

open import Data.Bool

import Cat.Reasoning
```
-->

```agda
module Cat.Instances.Shape.Involution where
```

# The walking involution

The **walking involution** is the category with a single non-trivial
morphism $i : x \to x$, satisfying $i \circ i = \id$.  We can encode
this by defining morphisms as booleans, and using `xor`{.Agda} as our
composition operation.

```agda
∙⤮∙ : Precategory lzero lzero
∙⤮∙ .Precategory.Ob = ⊤
∙⤮∙ .Precategory.Hom _ _ = Bool
∙⤮∙ .Precategory.Hom-set _ _ = hlevel 2
∙⤮∙ .Precategory.id = false
∙⤮∙ .Precategory._∘_ = xor
∙⤮∙ .Precategory.idr f = xor-falser f
∙⤮∙ .Precategory.idl f = refl
∙⤮∙ .Precategory.assoc f g h = xor-associative f g h

open Cat.Reasoning ∙⤮∙
```

This is the smallest precategory with a non-trivial isomorphism.

```agda
Bool≃∙⤮∙-isos : Bool ≃ (tt ≅ tt)
Bool≃∙⤮∙-isos =
  Iso→Equiv (Bool→Iso , iso Iso→Bool right-inv left-inv)
  where
    Bool→Iso : Bool → tt ≅ tt
    Bool→Iso true = make-iso true true refl refl
    Bool→Iso false = id-iso

    Iso→Bool : tt ≅ tt → Bool
    Iso→Bool i = i .to

    right-inv : is-right-inverse Iso→Bool Bool→Iso
    right-inv f = Bool-elim (λ b → b ≡ f .to → Bool→Iso b ≡ f) ext ext (f .to) refl

    left-inv : is-left-inverse Iso→Bool Bool→Iso
    left-inv true = refl
    left-inv false = refl
```

## Skeletality and (non)-univalence

As the walking involution only has one object, it is trivially [skeletal].

[skeletal]: Cat.Skeletal.html

```agda
∙⤮∙-skeletal : is-skeletal ∙⤮∙
∙⤮∙-skeletal .to-path _ = refl
∙⤮∙-skeletal .to-path-over _ =
  is-prop→pathp (λ _ → squash) (inc id-iso) _
```

However, it is *not* univalent, since its only object has more internal
automorphisms than it has loops. By definition, univalence for the
walking involution would mean that there are two paths $\tt{tt} \equiv
\tt{tt}$ in the unit type: but this contradicts the unit type being a set.

```agda
∙⤮∙-not-univalent : ¬ is-category ∙⤮∙
∙⤮∙-not-univalent is-cat = true≠false (Bool-is-prop true false) where

  Bool≃Ob-path : Bool ≃ (tt ≡ tt)
  Bool≃Ob-path = Bool≃∙⤮∙-isos ∙e identity-system-gives-path is-cat

  Bool-is-prop : is-prop Bool
  Bool-is-prop = Equiv→is-hlevel 1 Bool≃Ob-path (hlevel 1)
```
