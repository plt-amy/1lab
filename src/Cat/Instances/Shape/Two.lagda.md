<!--
```agda
open import Cat.Instances.Discrete
open import Cat.Functor.Base
open import Cat.Prelude

open import Data.Bool

open Functor
```
-->

```agda
module Cat.Instances.Shape.Two where
```

# The two-object category {defines="two-object-category"}

We define the [[discrete category]] $\twocat$ on two objects, which is
useful for expressing binary [[products]] and [[coproducts]] as
[[limits]] and [[colimits]], respectively.

```agda
2-object-category : Precategory _ _
2-object-category = Disc' (el! Bool)
```

A diagram of shape $\twocat$ in $\cC$ simply consists of two objects of
$\cC$.

```agda
module _ {o h} {C : Precategory o h} where
  open Precategory C

  2-object-diagram : Ob → Ob → Functor 2-object-category C
  2-object-diagram a b = Disc-diagram λ where
    true  → a
    false → b
```

Similarly, a natural transformation between two such diagrams consists
of two morphisms in $\cC$.

```agda
  2-object-nat-trans
    : ∀ {F G : Functor 2-object-category C}
    → Hom (F # true) (G # true) → Hom (F # false) (G # false)
    → F => G
  2-object-nat-trans f g = Disc-natural λ where
    true  → f
    false → g
```

We note that _any_ functor $F : \twocat \to \cC$ is
canonically _equal_, not just naturally isomorphic, to the one we
defined above.

```agda
  canonical-functors
    : ∀ (F : Functor 2-object-category C)
    → F ≡ 2-object-diagram (F # true) (F # false)
  canonical-functors F = Functor-path p q where
    p : ∀ x → _
    p false = refl
    p true  = refl

    q : ∀ {x y} (f : x ≡ y) → _
    q {false} {false} p =
      F .F₁ p           ≡⟨ ap (F .F₁) prop! ⟩
      F .F₁ refl        ≡⟨ F .F-id ⟩
      id                ∎
    q {true} {true} p =
      F .F₁ p           ≡⟨ ap (F .F₁) prop! ⟩
      F .F₁ refl        ≡⟨ F .F-id ⟩
      id                ∎
    q {false} {true} p = absurd (true≠false (sym p))
    q {true} {false} p = absurd (true≠false p)
```
