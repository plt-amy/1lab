<!--
```agda
open import Cat.Functor.Base
open import Cat.Groupoid
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Instances.Product where
```

<!--
```agda
open Precategory
open Functor
open _=>_
private variable
  o₁ h₁ o₂ h₂ : Level
  B C D E : Precategory o₁ h₁
```
-->

# Product categories {defines="product-category"}

Let $\cC$ and $\cD$ be two precategories; we put no restrictions
on their relative sizes. Their _product category_ $\cC \times^c
\cD$ is the category having as object _pairs_ $(x, y)$ of an object
$x : \cC$ and $y : \cD$, and the morphisms are pairs $(f, g)$ of a
morphism in $\cC$ and a morphism in $\cD$. The product category
admits two projection functors

$$
\cC \xot{\pi_1} (\cC \times^c \cD) \xto{\pi_2} \cD
$$,

satisfying a universal property analogous to those of [[product
diagrams|product]] _in_ categories. Namely, given a setup like in the
diagram below, there is a unique^[When $\cC$ and $\cD$ are
precategories, this functor is only unique up to a natural isomorphism]
functor which fits into the dashed line and makes the whole diagram
commute.

[product diagrams]: Cat.Diagram.Product.html

~~~{.quiver}
\[\begin{tikzcd}
  & {\mathcal{A}} \\
  {\mathcal{C}} & {\mathcal{C} \times^c \mathcal{D}} & {\mathcal{D}}
  \arrow["{\exists!}", dashed, from=1-2, to=2-2]
  \arrow[from=1-2, to=2-1]
  \arrow[from=1-2, to=2-3]
  \arrow[from=2-2, to=2-3]
  \arrow[from=2-2, to=2-1]
\end{tikzcd}\]
~~~

Formulating this universal property properly would take us further
afield into 2-category theory than is appropriate here.

```agda
_×ᶜ_ : Precategory o₁ h₁ → Precategory o₂ h₂ → Precategory _ _
C ×ᶜ D = prodcat module ×ᶜ where
  module C = Precategory C
  module D = Precategory D

  prodcat : Precategory _ _
  prodcat .Ob = Ob C × Ob D
  prodcat .Hom (a , a') (b , b') = Hom C a b × Hom D a' b'
  prodcat .Hom-set (a , a') (b , b') = hlevel 2
  prodcat .id = id C , id D
  prodcat ._∘_ (f , f') (g , g') = f C.∘ g , f' D.∘ g'
  prodcat .idr (f , f') i = C.idr f i , D.idr f' i
  prodcat .idl (f , f') i = C.idl f i , D.idl f' i
  prodcat .assoc (f , f') (g , g') (h , h') i =
    C.assoc f g h i , D.assoc f' g' h' i

{-# DISPLAY ×ᶜ.prodcat a b = a ×ᶜ b #-}
infixr 20 _×ᶜ_
```

We define the two projection functors $\cC \times \cD \to \cC$ (resp
$\to \cD$) as the evident liftings of the `fst`{.Agda} and `snd`{.Agda}
operations from the product _type_. Functoriality is automatic because
composites (and identities) are defined componentwise in the product
category.

```agda
Fst : Functor (C ×ᶜ D) C
Fst .F₀ = fst
Fst .F₁ = fst
Fst .F-id = refl
Fst .F-∘ _ _ = refl

Snd : Functor (C ×ᶜ D) D
Snd .F₀ = snd
Snd .F₁ = snd
Snd .F-id = refl
Snd .F-∘ _ _ = refl

Cat⟨_,_⟩ : Functor E C → Functor E D → Functor E (C ×ᶜ D)
Cat⟨ F , G ⟩ = f where
  f : Functor _ _
  f .F₀ x = F .F₀ x , G .F₀ x
  f .F₁ f = F .F₁ f , G .F₁ f
  f .F-id i = F .F-id i , G .F-id i
  f .F-∘ f g i = F .F-∘ f g i , G .F-∘ f g i

Swap : Functor (C ×ᶜ D) (D ×ᶜ C)
Swap = Cat⟨ Snd , Fst ⟩

_F×_ : Functor B D → Functor C E → Functor (B ×ᶜ C) (D ×ᶜ E)
_F×_ {B = B} {D = D} {C = C} {E = E} G H = func
  module F× where

  func : Functor (B ×ᶜ C) (D ×ᶜ E)
  func .F₀ (x , y) = G .F₀ x , H .F₀ y
  func .F₁ (f , g) = G .F₁ f , H .F₁ g
  func .F-id = G .F-id ,ₚ H .F-id
  func .F-∘ (f , g) (f' , g') = G .F-∘ f f' ,ₚ H .F-∘ g g'

_nt,_
  : {F G : Functor B C} {H K : Functor B D}
  → F => G → H => K → Cat⟨ F , H ⟩ => Cat⟨ G , K ⟩
_nt,_ α β .η c              = α .η c , β .η c
_nt,_ α β .is-natural _ _ f = α .is-natural _ _ f ,ₚ β .is-natural _ _ f

_nt×_
  : {F G : Functor B D} {H K : Functor C E}
  → F => G → H => K → (F F× H) => (G F× K)
_nt×_ α β .η (c , d) = α .η c , β .η d
_nt×_ α β .is-natural (c , d) (c' , d') (f , g) = Σ-pathp
  (α .is-natural c c' f)
  (β .is-natural d d' g)
```

<!--
```agda
{-# DISPLAY F×.func F G = F F× G #-}
```
-->

## Univalence

Isomorphisms in functor categories admit a short description, too: They
are maps which are componentwise isomorphisms. It follows, since paths
in product types are products of paths in the component types, that the
product of [[univalent categories]] is itself a univalent category.

<!--
```agda
module
  _ {o ℓ o' ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'}
    (c-cat : is-category C) (d-cat : is-category D) where
    private
      module C   = Univalent c-cat
      module D   = Univalent d-cat
      module C*D = Cat.Reasoning (C ×ᶜ D)
```
-->

```agda
    ×ᶜ-is-category : is-category (C ×ᶜ D)
    ×ᶜ-is-category .to-path im =
      Σ-pathp (C.iso→path (F-map-iso Fst im)) (D.iso→path (F-map-iso Snd im))
    ×ᶜ-is-category .to-path-over p = C*D.≅-pathp _ _ $
      Σ-pathp (Univalent.Hom-pathp-reflr-iso c-cat (C.idr _))
              (Univalent.Hom-pathp-reflr-iso d-cat (D.idr _))
```

<!--
```agda
module _
  {o ℓ o' ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'}
  (c-gpd : is-univalent-groupoid C) (d-gpd : is-univalent-groupoid D)
  where

  ×ᶜ-is-univalent-groupoid : is-univalent-groupoid (C ×ᶜ D)
  ×ᶜ-is-univalent-groupoid = ×-identity-system c-gpd d-gpd
```
-->
