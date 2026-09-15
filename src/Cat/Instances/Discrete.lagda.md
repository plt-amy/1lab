<!--
```agda
open import 1Lab.HLevel.Closure

open import Cat.Functor.Naturality
open import Cat.Instances.Product
open import Cat.Groupoid
open import Cat.Morphism
open import Cat.Prelude

open import Data.Id.Properties
open import Data.Id.Base
open import Data.Dec

import Cat.Reasoning
```
-->

```agda
module Cat.Instances.Discrete where
```

<!--
```agda
private variable
  ℓ ℓ' : Level
  X : Type ℓ
  C : Precategory ℓ ℓ'

open Precategory
open Functor
open _=>_
```
-->

# Discrete categories {defines="discrete-category"}

Given a [[groupoid]] $A$, we can see $A$ as a [[category]] with
space of objects $A$ and path types $x \equiv y$ as $\hom$-sets $x \to
y$. When $A$ is a [[set]], we call this the **discrete category** on $A$.
For technical reasons, we prefer to define this category using the
[[inductive identity]] type instead of the path type.

```agda
Disc : (A : Type ℓ) → is-groupoid A → Precategory ℓ ℓ
Disc A A-grpd = record where
  Ob          = A
  Hom         = _≡ᵢ_
  Hom-set     = ≡ᵢ-is-hlevel' {n = 2} A-grpd
  id          = reflᵢ
  _∘_ p q     = q ∙ᵢ p
  idr _       = refl
  idl _       = ∙ᵢ-idr _
  assoc p q r = sym (∙ᵢ-assoc r q p)
```

<!--
```agda
Disc! : ∀ {ℓ} {U : Type ℓ} ⦃ _ : Underlying U ⦄ (T : U) ⦃ _ : H-Level ⌞ T ⌟ 3 ⦄ → Precategory _ _
Disc! A = Disc ⌞ A ⌟ h module Disc! where abstract
  h : is-groupoid ⌞ A ⌟
  h = hlevel 3

{-# DISPLAY Disc {ℓ} A (Disc!.h {_} _ ⦃ i ⦄) = Disc! {ℓ} A ⦃ i ⦄ #-}
```
-->

By construction, this is a [[univalent|univalent category]]
[[groupoid|pregroupoid]]:

```agda
Disc-is-category : ∀ {A : Type ℓ} {A-grpd} → is-category (Disc A A-grpd)
Disc-is-category .to-path is = Id≃path.to (is .to)
Disc-is-category .to-path-over {a = a} is with is .to in w
... | reflᵢ = ≅-pathp _ _ _ (Id≃path.to (symᵢ w))

Disc-is-groupoid : ∀ {A : Type ℓ} {A-grpd} → is-pregroupoid (Disc A A-grpd)
Disc-is-groupoid p = make-invertible _ (symᵢ p) (∙ᵢ-invl p) (∙ᵢ-invr p)

Disc-is-univalent-groupoid : ∀ {A : Type ℓ} {A-grpd} → is-univalent-groupoid (Disc A A-grpd)
Disc-is-univalent-groupoid = Id-identity-system
```

<!--
```agda
Codisc' : ∀ {ℓ'} → Type ℓ → Precategory ℓ ℓ'
Codisc' x .Ob = x
Codisc' x .Hom _ _ = Lift _ ⊤
Codisc' x .Hom-set _ _ = is-prop→is-set (λ _ _ i → lift tt)
Codisc' x .id = lift tt
Codisc' x ._∘_ _ _ = lift tt
Codisc' x .idr _ = refl
Codisc' x .idl _ = refl
Codisc' x .assoc _ _ _ = refl
```
-->

## Diagrams in Disc(X)

Because the morphisms in a discrete category are identifications, and
functions respect equality, any function on objects out of a discrete
category induces a functor.

```agda
Disc-diagram
  : ∀ {X : Type ℓ} {xh}
  → (X → Ob C)
  → Functor (Disc X xh) C
Disc-diagram {C = C} f .F₀       = f
Disc-diagram {C = C} f .F₁ reflᵢ = C .id
Disc-diagram {C = C} f .F-id = refl
Disc-diagram {C = C} f .F-∘ reflᵢ reflᵢ = sym (C .idl _)
```

As a corollary, we can lift any function between underlying types to a
functor between discrete categories.

```agda
lift-disc
  : ∀ {A : Type ℓ} {B : Type ℓ'} {ah bh} (f : A → B)
  → Functor (Disc A ah) (Disc B bh)
lift-disc {A = A} f = Disc-diagram f
```

<!--
```agda
Disc-into
  : ∀ {ℓ} {X : Type ℓ} {xh} ⦃ _ : H-Level X 2 ⦄
  → (F : C .Ob → ⌞ X ⌟)
  → (F₁ : ∀ {x y} → C .Hom x y → F x ≡ᵢ F y)
  → Functor C (Disc X xh)
Disc-into F F₁ .F₀      = F
Disc-into F F₁ .F₁      = F₁
Disc-into F F₁ .F-id    = hlevel!
Disc-into F F₁ .F-∘ _ _ = hlevel!

Disc-natural
  : ∀ {X : Type ℓ} {xh}
  → {F G : Functor (Disc X xh) C}
  → (∀ x → C .Hom (F .F₀ x) (G .F₀ x))
  → F => G
Disc-natural fam .η = fam
Disc-natural {C = C} {F = F} {G = G} fam .is-natural x y reflᵢ =
  C.elimr (F .F-id) ∙ C.introl (G .F-id) where module C = Cat.Reasoning C

Disc-natural₂
  : ∀ {X : Type ℓ} {Y : Type ℓ'}
  → {issx : is-groupoid X} {issy : is-groupoid Y}
  → {F G : Functor (Disc X issx ×ᶜ Disc Y issy) C}
  → ((x : X × Y) → C .Hom (F .F₀ x) (G .F₀ x))
  → F => G
Disc-natural₂ fam .η = fam
Disc-natural₂ {C = C} {F = F} {G = G} fam .is-natural x y (reflᵢ , reflᵢ) =
  C.elimr (F .F-id) ∙ C.introl (G .F-id) where module C = Cat.Reasoning C

open _≅_
open Inverses

Disc-natural-iso
  : ∀ {X : Type ℓ} {xh}
  → {F G : Functor (Disc X xh) C}
  → (∀ x → Isomorphism C (F .F₀ x) (G .F₀ x))
  → F ≅ⁿ G
Disc-natural-iso isos .to       = Disc-natural λ x → isos x .to
Disc-natural-iso isos .from     = Disc-natural λ x → isos x .from
Disc-natural-iso isos .inverses =
  to-inversesⁿ (λ x → isos x .inverses .invl) (λ x → isos x .inverses .invr)
```
-->
