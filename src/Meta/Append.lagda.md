<!--
```agda
open import 1Lab.Type
```
-->

```agda
module Meta.Append where
```

# Types with concatenation

```agda
record Append {ℓ} (A : Type ℓ) : Type ℓ where
  infixr 8 _<>_

  field
    mempty : A
    _<>_   : A → A → A

open Append ⦃ ... ⦄ public
```
