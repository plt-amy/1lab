<!--
```agda
open import Cat.Instances.Product
open import Cat.Groupoid
open import Cat.Morphism
open import Cat.Prelude

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

Given a groupoid $A$, we can build the category $\rm{Disc}(A)$ with
space of objects $A$ and a single morphism $x \to y$ whenever $x \equiv
y$.

```agda
Disc : (A : Type ℓ) → is-groupoid A → Precategory ℓ ℓ
Disc A A-grpd .Ob = A
Disc A A-grpd .Hom = _≡_
Disc A A-grpd .Hom-set = A-grpd
Disc A A-grpd .id = refl
Disc A A-grpd ._∘_ p q = q ∙ p
Disc A A-grpd .idr _ = ∙-idl _
Disc A A-grpd .idl _ = ∙-idr _
Disc A A-grpd .assoc _ _ _ = sym (∙-assoc _ _ _)

Disc! : {T : Type ℓ} ⦃ u : Underlying T ⦄ (A : T) {@(tactic hlevel-tactic-worker) is-grpd : is-groupoid ⌞ A ⌟} → Precategory (u .Underlying.ℓ-underlying) (u .Underlying.ℓ-underlying)
Disc! A {is-grpd} = Disc ⌞ A ⌟ is-grpd
```

Clearly this is a [[univalent|univalent category]] [[groupoid|pregroupoid]]:

```agda
Disc-is-category : ∀ {A : Type ℓ} {A-grpd} → is-category (Disc A A-grpd)
Disc-is-category .to-path is = is .to
Disc-is-category .to-path-over is = ≅-pathp _ _ _ λ i j → is .to (i ∧ j)

Disc-is-groupoid : ∀ {A : Type ℓ} {A-grpd} → is-pregroupoid (Disc A A-grpd)
Disc-is-groupoid p = make-invertible _ (sym p) (∙-invl p) (∙-invr p)
```

We can lift any function between the underlying types to a functor
between discrete categories. This is because every function
automatically respects equality in a functorial way.

```agda
lift-disc
  : {A : Type ℓ} {@(tactic hlevel-tactic-worker) is-grpd₁ : is-groupoid A} 
    {B : Type ℓ'} {@(tactic hlevel-tactic-worker) is-grpd₂ : is-groupoid B}
    → (A → B) 
    → Functor (Disc! A) (Disc! B)
lift-disc f .F₀ = f
lift-disc f .F₁ = ap f
lift-disc f .F-id = refl
lift-disc f .F-∘ p q = ap-∙ f q p
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

If $X$ is a `discrete type`{.Agda ident=Discrete}, then it is in
particular in `Set`{.Agda}, and we can make diagrams of shape
$\rm{Disc}(X)$ in some category $\cC$, using the decidable
equality on $X$. We note that the decidable equality is _redundant_
information: The construction `Disc!`{.Agda} above extends into a [[left
adjoint]] to the `Ob`{.Agda} functor.

```agda
Disc-diagram
  : {X : Type ℓ} ⦃ d : Discrete X ⦄ {@(tactic hlevel-tactic-worker) h : is-groupoid X} 
  → (X → Ob C)
  → Functor (Disc! X) C
Disc-diagram {C = C} {X = X} ⦃ d = d ⦄ f = F where
  module C = Precategory C

  P : X → X → Type _
  P x y = C.Hom (f x) (f y)

  go : ∀ {x y : X} → x ≡ y → Dec (x ≡ᵢ y) → P x y
  go {x} {.x} p (yes reflᵢ) = C.id
  go {x} {y}  p (no ¬p)     = absurd (¬p (Id≃path.from p))
```

The object part of the functor is the provided $f : X \to
\rm{Ob}(\cC)$, and the decidable equality is used to prove that
$f$ respects equality. This is why it's redundant: $f$ automatically
respects equality, because it's a function! However, by using the
decision procedure, we get better computational behaviour: Very often,
$\rm{disc}(x,x)$ will be $\rm{yes}(\refl)$, and
substitution along $\refl$ is easy to deal with.

```agda
  F : Functor _ _
  F .F₀ = f
  F .F₁ {x} {y} p = go p (x ≡ᵢ? y)
```

Proving that our our $F_1$ is functorial involves a bunch of tedious
computations with equalities and a whole waterfall of absurd cases:

```agda
  F .F-id {x} = refl
  F .F-∘  {x} {y} {z} f g =
    J (λ y g → ∀ {z} (f : y ≡ z) → go (g ∙ f) (x ≡ᵢ? z) ≡ go f (y ≡ᵢ? z) C.∘ go g (x ≡ᵢ? y))
      (λ f → J (λ z f → go (refl ∙ f) (x ≡ᵢ? z) ≡ go f (x ≡ᵢ? z) C.∘ C.id) (sym (C.idr _)) f)
      g f
```

<!--
```
Disc-adjunct
  : {X : Type ℓ} {@(tactic hlevel-tactic-worker) h : is-groupoid X}
  → (X → Ob C)
  → Functor (Disc! X) C
Disc-adjunct {C = C} F .F₀ = F
Disc-adjunct {C = C} F .F₁ p = subst (C .Hom (F _) ⊙ F) p (C .id)
Disc-adjunct {C = C} F .F-id = transport-refl _
Disc-adjunct {C = C} F .F-∘ {x} {y} {z} f g = path where
  import Cat.Reasoning C as C
  go = Disc-adjunct {C = C} F .F₁
  abstract
    path : go (g ∙ f) ≡ C ._∘_ (go f) (go g)
    path =
      J' (λ y z f → ∀ {x} (g : x ≡ y) → go (g ∙ f) ≡ go f C.∘ go g)
        (λ x g → subst-∙ (C .Hom (F _) ⊙ F) _ _ _
              ·· transport-refl _
              ·· C.introl (transport-refl _))
        f {x} g

Disc-into
  : ∀ {ℓ} (X : Set ℓ)
  → (F : C .Ob → ∣ X ∣)
  → (F₁ : ∀ {x y} → C .Hom x y → F x ≡ F y)
  → Functor C (Disc' X)
Disc-into X F F₁ .F₀ = F
Disc-into X F F₁ .F₁ = F₁
Disc-into X F F₁ .F-id = X .is-tr _ _ _ _
Disc-into X F F₁ .F-∘ _ _ = X .is-tr _ _ _ _
```
-->

<!--
```agda
Disc-natural
  : {X : Type ℓ} {h : is-groupoid X}
  → {F G : Functor (Disc! X) C}
  → (∀ x → C .Hom (F .F₀ x) (G .F₀ x))
  → F => G
Disc-natural fam .η = fam
Disc-natural {C = C} {F = F} {G = G} fam .is-natural x y f =
  J (λ y p → fam y C.∘ F .F₁ p ≡ G .F₁ p C.∘ fam x)
    (C.elimr (F .F-id) ∙ C.introl (G .F-id))
    f
  where module C = Cat.Reasoning C

Disc-natural₂
  : ∀ {X : Type ℓ} {Y : Type ℓ'}
  → {issx : is-groupoid X} {issy : is-groupoid Y}
  → {F G : Functor (Disc X issx ×ᶜ Disc Y issy) C}
  → ((x : X × Y) → C .Hom (F .F₀ x) (G .F₀ x))
  → F => G
Disc-natural₂ fam .η = fam
Disc-natural₂ {C = C} {F = F} {G = G} fam .is-natural x y (p , q) =
  J (λ y' p' → fam y' C.∘ F .F₁ (ap fst p' , ap snd p')
             ≡ G .F₁ (ap fst p' , ap snd p') C.∘ fam x)
    (C.elimr (F .F-id) ∙ C.introl (G .F-id))
    (Σ-pathp p q)
  where module C = Cat.Reasoning C
```
-->
