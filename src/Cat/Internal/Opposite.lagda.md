<!--
```agda
open import Cat.Prelude

import Cat.Internal.Base
```
-->

```agda
module Cat.Internal.Opposite {o ℓ} {C : Precategory o ℓ} where
```

<!--
```agda
open Precategory C
open Cat.Internal.Base C
open Internal-hom
```
-->

# Opposites of internal categories

We can take the opposite of an [internal category], by flipping the
source and target morphisms. We begin by defining a little helper
function that flips internal morphisms.

[internal category]: Cat.Internal.Base.html

```agda
op-ihom
  : ∀ {C₀ C₁ Γ} {src tgt : Hom C₁ C₀} {x y : Hom Γ C₀}
  → Internal-hom src tgt x y
  → Internal-hom tgt src y x
op-ihom f .ihom = f .ihom
op-ihom f .has-src = f .has-tgt
op-ihom f .has-tgt = f .has-src

op-ihom-nat
  : ∀ {C₀ C₁ Γ Δ} {src tgt : Hom C₁ C₀} {x y : Hom Δ C₀}
  → (f : Internal-hom src tgt x y)
  → (σ : Hom Γ Δ)
  → op-ihom f [ σ ] ≡ op-ihom (f [ σ ])
op-ihom-nat f _ = Internal-hom-path refl
```

<!--
```agda
private
  op-ihom-involutive
    : ∀ {C₀ C₁ Γ} {src tgt : Hom C₁ C₀} {x y : Hom Γ C₀}
    → {f : Internal-hom src tgt x y}
    → op-ihom (op-ihom f) ≡ f
  op-ihom-involutive = Internal-hom-path refl
{-# REWRITE op-ihom-involutive #-}
```
-->

Showing that this operation yields an internal category is a routine
calculation.

```agda
Internal-cat-on-opi
  : ∀ {C₀ C₁} {src tgt : Hom C₁ C₀}
  → Internal-cat-on src tgt →  Internal-cat-on tgt src
Internal-cat-on-opi ℂ = icat-opi-on  where
  open Internal-cat-on
  module ℂ = Internal-cat-on ℂ

  icat-opi-on : Internal-cat-on _ _
  icat-opi-on .idi x = op-ihom (ℂ.idi x)
  icat-opi-on ._∘i_ f g = op-ihom (op-ihom g ℂ.∘i op-ihom f)
  icat-opi-on .idli f = ap op-ihom (ℂ.idri _)
  icat-opi-on .idri f = ap op-ihom (ℂ.idli _)
  icat-opi-on .associ f g h = ap op-ihom (sym (ℂ.associ _ _ _))
  icat-opi-on .idi-nat σ =
    op-ihom-nat (ℂ.idi _) σ ∙ ap op-ihom (ℂ.idi-nat σ)
  icat-opi-on .∘i-nat f g σ =
    op-ihom-nat (op-ihom g ℂ.∘i op-ihom f) σ
    ∙ ap op-ihom ((ℂ.∘i-nat (op-ihom g) (op-ihom f) σ)
      ∙ ap₂ ℂ._∘i_ (op-ihom-nat g σ) (op-ihom-nat f σ))

_^opi : Internal-cat → Internal-cat
ℂ ^opi = op-icat where
  open Internal-cat

  op-icat : Internal-cat
  op-icat .C₀ = ℂ .C₀
  op-icat .C₁ = ℂ .C₁
  op-icat .src = ℂ .tgt
  op-icat .tgt = ℂ .src
  op-icat .has-internal-cat = Internal-cat-on-opi (ℂ .has-internal-cat)

infixl 60 _^opi
```
