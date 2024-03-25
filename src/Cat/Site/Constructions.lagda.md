<!--
```agda
open import Cat.Diagram.Sieve
open import Cat.Site.Base
open import Cat.Prelude
```
-->

```agda
module Cat.Site.Constructions where
```

# Constructing sites

```agda
from-stable-property
  : ∀ {o ℓ ℓj} {C : Precategory o ℓ}
  → (P : ∀ {U} → Sieve C U → Type ℓj)
  → (∀ {U V} (f : C .Precategory.Hom V U) (s : Sieve C U) → P s → P (pullback f s))
  → Coverage C (o ⊔ ℓ ⊔ ℓj)
from-stable-property P stab .covers U = Σ[ s ∈ Sieve _ U ] P s
from-stable-property P stab .cover = fst
from-stable-property P stab .stable (S , ps) f = pure
  ((pullback f S , stab f S ps) , λ g hf → hf)
```
