<!--
```agda
open import Cat.Instances.Discrete
open import Cat.Instances.Functor
open import Cat.Morphism
open import Cat.Bi.Base
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Bi.Instances.Discrete {o ℓ} (C : Precategory o ℓ) where
```

<!--
```agda
private module C = Cat.Reasoning C
open Prebicategory
open Functor
```
-->

# Locally discrete bicategories {defines="locally-discrete-bicategory"}

Let $\cC$ be a precategory. We can define a prebicategory $\bf{C}$ by
letting the hom-1-categories of $\bf{C}$ be the [discrete categories] on
the Hom-sets of $\cC$.

[discrete categories]: Cat.Instances.Discrete.html

```agda
{-# TERMINATING #-}
Locally-discrete : Prebicategory o ℓ ℓ
Locally-discrete .Ob = C.Ob
Locally-discrete .Hom x y = Disc! $ C.Hom x y
Locally-discrete .id = C.id
Locally-discrete .compose .F₀ (f , g) = f C.∘ g
Locally-discrete .compose .F₁ (p , q) = ap₂ C._∘_ p q
Locally-discrete .compose .F-id = refl
Locally-discrete .compose .F-∘ f g = C.Hom-set _ _ _ _ _ _
Locally-discrete .unitor-l = to-natural-iso ni where
  ni : make-natural-iso _ _
  ni .make-natural-iso.eta x = sym (C.idl x)
  ni .make-natural-iso.inv x = C.idl x
  ni .make-natural-iso.eta∘inv x = ∙-invr (C.idl x)
  ni .make-natural-iso.inv∘eta x = ∙-invl (C.idl x)
  ni .make-natural-iso.natural x y f = C.Hom-set _ _ _ _ _ _
Locally-discrete .unitor-r = to-natural-iso ni where
  ni : make-natural-iso _ _
  ni .make-natural-iso.eta x = sym (C.idr x)
  ni .make-natural-iso.inv x = C.idr x
  ni .make-natural-iso.eta∘inv x = ∙-invr (C.idr x)
  ni .make-natural-iso.inv∘eta x = ∙-invl (C.idr x)
  ni .make-natural-iso.natural x y f = C.Hom-set _ _ _ _ _ _
Locally-discrete .associator = to-natural-iso ni where
  ni : make-natural-iso _ _
  ni .make-natural-iso.eta x = sym (C.assoc _ _ _)
  ni .make-natural-iso.inv x = C.assoc _ _ _
  ni .make-natural-iso.eta∘inv x = ∙-invr (C.assoc _ _ _)
  ni .make-natural-iso.inv∘eta x = ∙-invl (C.assoc _ _ _)
  ni .make-natural-iso.natural x y f = C.Hom-set _ _ _ _ _ _
Locally-discrete .triangle f g = C.Hom-set _ _ _ _ _ _
Locally-discrete .pentagon f g h i = C.Hom-set _ _ _ _ _ _
```
