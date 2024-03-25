<!--
```agda
{-# OPTIONS -vtactic.hlevel:30 #-}
open import Cat.Instances.Functor
open import Cat.Functor.Hom
open import Cat.Prelude

open import Data.Power

import Cat.Reasoning
```
-->

```agda
module Cat.Diagram.Sieve where
```

<!--
```agda
module _ {o κ : _} (C : Precategory o κ) (c : ⌞ C ⌟) where
  private module C = Precategory C
```
-->

# Sieves {defines="sieve"}

Given a category $\cC$, a **sieve** on an object $c$ Is a subset of
the maps $a \to c$ closed under composition: If $f \in S$, then $(f
\circ g) \in S$. The data of a sieve on $c$ corresponds to the data of a
subobject of $\yo(c)$, considered as an object of $\psh(\cC)$.

Here, the subset is represented as the function `arrows`{.agda}, which,
given an arrow $f : a \to c$ (and its domain), yields a proposition
representing inclusion in the subset.

```agda
  record Sieve : Type (o ⊔ κ) where
    no-eta-equality
    field
      arrows : ∀ {y} → ℙ (C.Hom y c)
      closed : ∀ {y z f} (hf : f ∈ arrows) (g : C.Hom y z) → (f C.∘ g) ∈ arrows
  open Sieve public
```

<!--
```agda
```
-->

The `maximal`{.agda} sieve on an object is the collection of _all_ maps
$a \to c$; It represents the identity map $\yo(c) \to \yo(c)$ as a
subfunctor. A [$\kappa$-small] family of sieves can be intersected (the
underlying predicate is the "$\kappa$-ary conjunction" $\Pi$ --- the
universal quantifier), and this represents a wide pullback of
subobjects.

[$\kappa$-small]: 1Lab.intro.html#universes-and-size-issues

<!--
```agda
module _ {o ℓ : _} {C : Precategory o ℓ} where
  private
    module C   = Cat.Reasoning C
    module PSh = Cat.Reasoning (PSh ℓ C)

  Sieve-path : ∀ {c} {x y : Sieve C c} → Path (∀ {y} → ℙ (C.Hom y c)) (x .arrows) (y .arrows) → x ≡ y
  Sieve-path {x = x} {y} p i .arrows = p i
  Sieve-path {x = x} {y} p i .closed {f = f} hf g =
    is-prop→pathp (λ i → fun-is-hlevel {A = ⌞ p i f ⌟} 1 (p i (f C.∘ g) .is-tr)) (λ w → x .closed w g) (λ w → y .closed w g) i hf

  Extensional-sieve : ∀ {ℓr c} ⦃ _ : Extensional (∀ {y} → C.Hom y c → Ω) ℓr ⦄ → Extensional (Sieve C c) ℓr
  Extensional-sieve ⦃ e ⦄ = injection→extensional! Sieve-path e

  instance
    Membership-Sieve : ∀ {c d} → Membership (C.Hom d c) (Sieve C c) _
    Membership-Sieve = record { _∈_ = λ x S → x ∈ S .Sieve.arrows }

    Extensionality-sieve : ∀ {c} → Extensionality (Sieve C c)
    Extensionality-sieve = record { lemma = quote Extensional-sieve }

    H-Level-Sieve : ∀ {c n} → H-Level (Sieve C c) (2 + n)
    H-Level-Sieve = basic-instance 2 $
      embedding→is-hlevel 1 (injective→is-embedding! Sieve-path) (hlevel 2)

  open PSh._↪_
  open _=>_
  open Functor
```
-->

```agda
  maximal' : ∀ {c} → Sieve C c
  maximal' .arrows x = ⊤Ω
  maximal' .closed g x = tt

  intersect : ∀ {c} {I : Type ℓ} (F : I → Sieve C c) → Sieve C c
  intersect {I = I} F .arrows h = elΩ ((x : I) → h ∈ F x)
  intersect {I = I} F .closed x g = inc λ i → F i .closed (out! x i) g
```

## Representing subfunctors {defines="sieves-as-presheaves"}

Let $S$ be a sieve on $\cC$. We show that it determines a presheaf
$S'$, and that this presheaf admits a monic natural transformation $S'
\mono \yo(c)$. The functor determined by a sieve $S$ sends each object
$d$ to the set of arrows $d \xto{f} c$ s.t. $f \in S$; The functorial
action is given by composition, as with the $\hom$ functor.

```agda
  to-presheaf : ∀ {c} → Sieve C c → PSh.Ob
  to-presheaf {c} sieve .F₀ d = el! (Σ[ f ∈ C.Hom d c ] (f ∈ sieve))
  to-presheaf sieve .F₁ f (g , s) = g C.∘ f , sieve .closed s _
```

<!--
```agda
  to-presheaf sieve .F-id    = funext λ _ → Σ-prop-path! (C.idr _)
  to-presheaf sieve .F-∘ f g = funext λ _ → Σ-prop-path! (C.assoc _ _ _)
```
-->

That this functor is a subobject of $\yo$ follows straightforwardly: The
injection map $S' \mono \yo(c)$ is given by projecting out the first
component, which is an embedding (since "being in a sieve" is a
proposition). Since natural transformations are monic if they are
componentwise monic, and embeddings are monic, the result follows.

```agda
  to-presheaf↪よ : ∀ {c} {S : Sieve C c} → to-presheaf S PSh.↪ よ₀ C c
  to-presheaf↪よ {S} .mor .η x (f , _) = f
  to-presheaf↪よ {S} .mor .is-natural x y f = refl
  to-presheaf↪よ {S} .monic g h path = ext λ i x → Σ-prop-path! (unext path i x)
```

## Pullback of sieves

```agda
  pullback : ∀ {u v} → C.Hom v u → Sieve C u → Sieve C v
  pullback f s .arrows h = el (f C.∘ h ∈ s) hlevel!
  pullback f s .closed hf g = subst (_∈ s) (sym (C.assoc f _ g)) (s .closed hf g)

  pullback-id : ∀ {c} {s : Sieve C c} → pullback C.id s ≡ s
  pullback-id {s = s} = ext λ h → Ω-ua (subst (_∈ s) (C.idl h)) (subst (_∈ s) (sym (C.idl h)))

  pullback-∘
    : ∀ {u v w} {f : C.Hom w v} {g : C.Hom v u} {R : Sieve C u}
    → pullback (g C.∘ f) R ≡ pullback f (pullback g R)
  pullback-∘ {f = f} {g} {R = R} = ext λ h →
    Ω-ua (subst (_∈ R) (sym (C.assoc g f h))) (subst (_∈ R) (C.assoc g f h))

  Sieves : Functor (C ^op) (Sets (o ⊔ ℓ))
  Sieves .F₀ U .∣_∣ = Sieve C U
  Sieves .F₀ U .is-tr = hlevel 2
  Sieves .F₁ = pullback
  Sieves .F-id    = funext λ x → pullback-id
  Sieves .F-∘ f g = funext λ x → pullback-∘
```
