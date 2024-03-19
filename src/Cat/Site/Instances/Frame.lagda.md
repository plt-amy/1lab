<!--
```agda
open import Cat.Diagram.Sieve
open import Cat.Site.Base
open import Cat.Prelude

open import Order.Diagram.Meet
open import Order.Frame
open import Order.Base
open import Order.Cat

import Order.Frame.Reasoning as Frame
```
-->

```agda
module Cat.Site.Instances.Frame {o ℓ} (P : Poset o ℓ) (isf : is-frame P) where
```

<!--
```agda
open Frame isf
```
-->

# Frames as sites

```agda
frame-coverage : Coverage (poset→category P) (lsuc o)
frame-coverage .covers U = Σ[ I ∈ Type o ] Σ[ f ∈ (I → ⌞ P ⌟) ] (⋃ f ≡ U)
frame-coverage .cover (I , f , _) .arrows {V} V≤U = elΩ (Σ[ i ∈ I ] (V ≤ f i))
frame-coverage .cover (I , f , _) .closed hf g = □-map (λ (i , q) → i , (≤-trans g q)) hf
frame-coverage .stable {U} {V} (I , f , p) g =
  let
    covers : ⋃ (λ i → f i ∩ V) ≡ V
    covers =
      ⋃ (λ i → f i ∩ V) ≡˘⟨ ⋃-distribr f V ⟩
      ⋃ f ∩ V           ≡⟨ ap₂ _∩_ p refl ⟩
      U ∩ V             ≡˘⟨ le-meet {P = P} g (subst (is-meet P V U) ∩-comm has-meet) ⟩
      V                 ∎

    incl : ∀ {W} → W ≤ V → □ (Σ[ i ∈ I ] (W ≤ f i ∩ V)) → □ (Σ[ i ∈ I ] (W ≤ f i))
    incl W≤V = □-map λ (i , W≤fiV) → i , ≤-trans W≤fiV ∩≤l
  in inc ((_ , _ , covers) , incl)
```
