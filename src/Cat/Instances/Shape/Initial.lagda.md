<!--
```agda
open import 1Lab.Prelude

open import Cat.Groupoid
open import Cat.Base
```
-->

```agda
module Cat.Instances.Shape.Initial where
```

<!--
```agda
open Precategory
```
-->

:::{.definition #initial-category}
The **initial category** is the category with no objects.
:::

```agda
⊥Cat : Precategory lzero lzero
⊥Cat .Ob = ⊥
⊥Cat .Hom _ _ = ⊥
```

This category is notable for the existence of a unique functor from
it to any other category.

```agda
module _ {o h} {A : Precategory o h} where
  private module A = Precategory A
  open Functor


  ¡F : Functor ⊥Cat A
  ¡F .F₀ ()

  ¡F-unique : ∀ (F G : Functor ⊥Cat A) → F ≡ G
  ¡F-unique F G i .F₀ ()

  ¡nt : ∀ {F G : Functor ⊥Cat A} → F => G
  ¡nt ._=>_.η ()
  ¡nt ._=>_.is-natural ()
```

The initial category is a [[univalent groupoid]].

```agda
⊥Cat-is-univalent-groupoid : is-univalent-groupoid ⊥Cat
⊥Cat-is-univalent-groupoid = set-identity-system absurd absurd
```
