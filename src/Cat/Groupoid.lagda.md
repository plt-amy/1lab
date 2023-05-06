<!--
```agda
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Groupoid where
```

# Groupoids

A precategory $\cC$ is a **pregroupoid** if every morphism of $\cC$ is
invertible.

```agda
is-pregroupoid : ∀ {o ℓ} → Precategory o ℓ → Type (o ⊔ ℓ)
is-pregroupoid C = ∀ {x y} (f : Hom x y) → is-invertible f
  where open Cat.Reasoning C
```
