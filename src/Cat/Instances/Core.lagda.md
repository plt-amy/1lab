<!--
```agda
open import Cat.Functor.WideSubcategory
open import Cat.Instances.Functor
open import Cat.Groupoid
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Instances.Core where
```

<!--
```agda
open Functor
```
-->

# The core of a category {defines="core"}

The **core** of a category $\cC$ is the maximal sub-[groupoid] of $\cC$:
the category $\rm{Core}(\cC)$ constructed by keeping only the invertible
morphisms. Since the identity is invertible, and invertibility is closed
under composition, we can construct this as a [wide subcategory] of $\cC$.

[groupoid]: Cat.Groupoid.html
[wide subcategory]: Cat.Functor.WideSubcategory.html

```agda
Core : ∀ {o ℓ} → Precategory o ℓ → Precategory o ℓ
Core C = Wide sub where
  open Cat.Reasoning C

  sub : Wide-subcat C _
  sub .Wide-subcat.P        = is-invertible
  sub .Wide-subcat.P-prop _ = is-invertible-is-prop
  sub .Wide-subcat.P-id     = id-invertible
  sub .Wide-subcat.P-∘      = invertible-∘
```

<!--
```agda
private module Core {o ℓ} (C : Precategory o ℓ) = Cat.Reasoning (Core C)
```
-->

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} where
  private
    module C = Cat.Reasoning C
```
-->

```agda
  Core-is-groupoid : is-pregroupoid (Core C)
  Core-is-groupoid f =
    Core.make-invertible _ (wide f-inv.inv ((f .witness) C.invertible⁻¹))
      (Wide-hom-path f-inv.invl)
      (Wide-hom-path f-inv.invr)
    where
      module f-inv = C.is-invertible (f .witness)
```

Note that isomorphisms in $\cC$ are equivalent to morphisms in the core
of $\cC$. This means that if $\cC$ is [[univalent|univalent-category]],
then we can transfer the associated identity system on isomorphisms to
an identity system on morphisms of the core, and thus the core
must be a [[univalent groupoid]].

```agda
  iso≃Core-hom : ∀ {x y} → (x C.≅ y) ≃ Core.Hom C x y
  iso≃Core-hom {x} {y} =
    x C.≅ y                              ≃⟨ C.iso≃is-invertible ⟩
    Σ[ f ∈ C.Hom x y ] C.is-invertible f ≃˘⟨ Wide-hom≃witness ⟩
    Core.Hom C x y                       ≃∎

  Core-is-univalent-groupoid : is-category C → is-univalent-groupoid (Core C)
  Core-is-univalent-groupoid C-cat =
    transfer-identity-system C-cat (λ _ _ → iso≃Core-hom) λ _ → ext refl
```

We have mentioned that the core is the _maximal_ sub-groupoid of $\cC$:
we can regard it as the _cofree_ groupoid on a category, summarised by
the following universal property. Suppose $\cC$ is a groupoid and $\cD$
is some category. Any functor $F : \cC \to \cD$ must factor through the
core of $\cD$.

```agda
module _
  {oc ℓc od ℓd} {C : Precategory oc ℓc} {D : Precategory od ℓd}
  (grpd : is-pregroupoid C)
  where

  Core-universal : (F : Functor C D) → Functor C (Core D)
  Core-universal F .F₀ x = F .F₀ x
  Core-universal F .F₁ f .hom = F .F₁ f
  Core-universal F .F₁ f .witness = F-map-invertible F (grpd f)
  Core-universal F .F-id = Wide-hom-path (F .F-id)
  Core-universal F .F-∘ f g = Wide-hom-path (F .F-∘ f g)

  Core-factor : (F : Functor C D) → F ≡ Forget-wide-subcat F∘ Core-universal F
  Core-factor F = Functor-path (λ _ → refl) λ _ → refl
```

This is dual to the [[free groupoid]] on a category, in the sense that
there is a biadjoint triple $\rm{Free} \dashv U \dashv \rm{Core}$,
where $U$ is the forgetful functor from the bicategory of groupoids to the
bicategory of categories.

<!-- [TODO: Reed M, 05/05/2023] This is really part of a biadjunction
between Cat and Grpd (in particular it's the right biadjoint to the
inclusion Grpd ↪ Cat).
-->
