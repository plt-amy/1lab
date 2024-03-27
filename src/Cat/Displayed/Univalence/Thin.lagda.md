<!--
```agda
{-# OPTIONS --lossy-unification -vtc.decl:5 #-}
open import 1Lab.Function.Embedding

open import Cat.Displayed.Univalence
open import Cat.Functor.Properties
open import Cat.Displayed.Total
open import Cat.Displayed.Base
open import Cat.Instances.Sets
open import Cat.Prelude

import Cat.Displayed.Morphism
import Cat.Morphism
```
-->

```agda
module Cat.Displayed.Univalence.Thin where

```

<!--
```agda
open Cat.Displayed.Total public
open Cat.Displayed.Base public
open Total-hom public
open Precategory
open Displayed
open Cat.Displayed.Morphism
open _≅[_]_
```
-->

# Thinly displayed structures

The HoTT Book's version of the structure identity principle can be seen
as a very early example of [[displayed category]] theory. Their
_standard notion of structure_ corresponds exactly to a displayed
category, all of whose fibres are posets. Note that this is not a
category _fibred in_ posets, since the displayed category will not
necessarily be a [[Cartesian fibration]].

Here, we restrict our attention to an important special case: Categories
of structures over the category of sets (for a given universe level).
Since these all have thin fibres (by assumption), we refer to them as
_thinly displayed structures_, or _thin structures_ for short. These are
of note not only because they intersect the categorical SIP defined
above with the [typal SIP] established in the prelude modules, but also
because we can work with them very directly.

[typal SIP]: 1Lab.Univalence.SIP.html

```agda
record
  Thin-structure {ℓ o'} ℓ' (S : Type ℓ → Type o')
    : Type (lsuc ℓ ⊔ o' ⊔ lsuc ℓ') where
  no-eta-equality
  field
    is-hom    : ∀ {x y} → (x → y) → S x → S y → Prop ℓ'
    id-is-hom : ∀ {x} {s : S x} → ∣ is-hom (λ x → x) s s ∣

    ∘-is-hom  :
      ∀ {x y z} {s t u} (f : y → z) (g : x → y)
      → (α : ∣ is-hom f t u ∣) (β : ∣ is-hom g s t ∣)
      → ∣ is-hom (λ x → f (g x)) s u ∣

    id-hom-unique
      : ∀ {x} {s t : S x}
      → ∣ is-hom (λ x → x) s t ∣ → ∣ is-hom (λ x → x) t s ∣ → s ≡ t

open Thin-structure public

module _
  {ℓ o' ℓ'} {S : Type ℓ → Type o'}
  (spec : Thin-structure ℓ' S) where
```

The data above conspires to make a category displayed over $\cB$. The
laws are trivial since $H$ is valued in propositions.

```agda
  Thin-structure-over : Displayed (Sets ℓ) o' ℓ'
  Thin-structure-over .Ob[_] x = S ∣ x ∣
  Thin-structure-over .Hom[_] f x y = ∣ spec .is-hom f x y ∣
  Thin-structure-over .Hom[_]-set f a b = is-prop→is-set hlevel!
  Thin-structure-over .id' = spec .id-is-hom
  Thin-structure-over ._∘'_ f g = spec .∘-is-hom _ _ f g
  Thin-structure-over .idr' f' = is-prop→pathp (λ _ → hlevel!) _ _
  Thin-structure-over .idl' f' = is-prop→pathp (λ _ → hlevel!) _ _
  Thin-structure-over .assoc' f' g' h' = is-prop→pathp (λ _ → hlevel!) _ _

  Structured-objects : Precategory _ _
  Structured-objects = ∫ Thin-structure-over
```

We recall that the $S$-structures can be made into a preorder by setting
$\alpha \le \beta$ iff. the identity morphism is an $H$-homomorphism
from $\alpha$ to $\beta$. And, if this preorder is in fact a [[partial
order]], then the [[total category]] of structures is univalent --- the
type of identities between $S$-structured $\cB$-objects is equivalent to
the type of $H$-homomorphic $\cB$-isomorphisms.

```agda
  Structured-objects-is-category : is-category Structured-objects
  Structured-objects-is-category =
    is-category-total Thin-structure-over Sets-is-category $
      is-category-fibrewise _ Sets-is-category λ A x y →
      Σ-prop-path
        (λ _ _ _ → ≅[]-path _ (spec .is-hom _ _ _ .is-tr _ _))
        ( spec .id-hom-unique (x .snd .from') (x .snd .to')
        ∙ spec .id-hom-unique (y .snd .to') (y .snd .from'))
```

By construction, such a category of structured objects admits a
[[faithful functor]] into the category of sets.

```agda
  Forget-structure : Functor Structured-objects (Sets ℓ)
  Forget-structure = πᶠ Thin-structure-over

  Structured-hom-path : is-faithful Forget-structure
  Structured-hom-path p =
    total-hom-path Thin-structure-over p (is-prop→pathp (λ _ → hlevel!) _ _)

module _ {ℓ o' ℓ'} {S : Type ℓ → Type o'} {spec : Thin-structure ℓ' S} where
  private
    module So = Precategory (Structured-objects spec)
    module Som = Cat.Morphism (Structured-objects spec)

  instance
    Extensional-Hom
      : ∀ {a b ℓr} ⦃ sa : Extensional (⌞ a ⌟ → ⌞ b ⌟) ℓr ⦄
      → Extensional (So.Hom a b) ℓr
    Extensional-Hom ⦃ sa ⦄ = injection→extensional!
      (Structured-hom-path spec) sa

    Funlike-Hom : ∀ {x y} → Funlike (So.Hom x y) ⌞ x ⌟ λ _ → ⌞ y ⌟
    Funlike-Hom = record
      { _#_ = Total-hom.hom
      }

  Homomorphism-monic
    : ∀ {x y : So.Ob} (f : So.Hom x y)
    → (∀ {x y} (p : f # x ≡ f # y) → x ≡ y)
    → Som.is-monic f
  Homomorphism-monic f wit g h p = ext λ x → wit (ap hom p $ₚ x)

record is-equational {ℓ o' ℓ'} {S : Type ℓ → Type o'} (spec : Thin-structure ℓ' S) : Type (lsuc ℓ ⊔ o' ⊔ ℓ') where
  field
    invert-id-hom : ∀ {x} {s t : S x} → ∣ spec .is-hom (λ x → x) s t ∣ → ∣ spec .is-hom (λ x → x) t s ∣

  private
    module So = Precategory (Structured-objects spec)
    module Som = Cat.Morphism (Structured-objects spec)

  equiv-hom→inverse-hom
    : ∀ {a b : So.Ob}
    → (f : ⌞ a ⌟ ≃ ⌞ b ⌟)
    → ∣ spec .is-hom (Equiv.to f) (a .snd) (b .snd) ∣
    → ∣ spec .is-hom (Equiv.from f) (b .snd) (a .snd) ∣
  equiv-hom→inverse-hom {a = a} {b = b} f e =
    EquivJ (λ B e → ∀ st → ∣ spec .is-hom (e .fst) (a .snd) st ∣ → ∣ spec .is-hom (Equiv.from e) st (a .snd) ∣)
      (λ _ → invert-id-hom) f (b .snd) e

  ∫-Path
    : ∀ {a b : So.Ob}
    → (f : So.Hom a b)
    → is-equiv (f #_)
    → a ≡ b
  ∫-Path {a = a} {b = b} f eqv =
    Σ-pathp (n-ua (f .hom , eqv)) $
      EquivJ (λ B e → ∀ st → ∣ spec .is-hom (e .fst) (a .snd) st ∣ → PathP (λ i → S (ua e i)) (a .snd) st)
        (λ st pres → to-pathp (ap (λ e → subst S e (a .snd)) ua-id-equiv
                  ·· transport-refl _
                  ·· spec .id-hom-unique pres (invert-id-hom pres)))
        (f .hom , eqv) (b .snd) (f .preserves)

open is-equational public
```

<!--
```agda
Full-substructure
  : ∀ {ℓ o'} ℓ' (R S : Type ℓ → Type o')
  → (∀ X → R X ↪ S X)
  → Thin-structure ℓ' S
  → Thin-structure ℓ' R
Full-substructure _ R S embed Sst .is-hom f x y =
  Sst .is-hom f (embed _ .fst x) (embed _ .fst y)
Full-substructure _ R S embed Sst .id-is-hom = Sst .id-is-hom
Full-substructure _ R S embed Sst .∘-is-hom = Sst .∘-is-hom
Full-substructure _ R S embed Sst .id-hom-unique α β =
  has-prop-fibres→injective (embed _ .fst) (embed _ .snd)
    (Sst .id-hom-unique α β)
```
-->
