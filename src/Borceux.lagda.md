---
description: |
  Lemmas and theorems from Francis Borceux's "Handbook of Categorical Algebra".
---
<!--
```agda
open import Algebra.Group.Cat.FinitelyComplete
open import Algebra.Monoid.Category
open import Algebra.Group.Cat.Base
open import Algebra.Group.Free hiding (_◆_)
open import Algebra.Group.Ab

open import Cat.Bi.Base
open import Cat.Bi.Diagram.Adjunction renaming (_⊣_ to _⊣ᵇ_)
open import Cat.Bi.Instances.Spans

open import Cat.Internal.Base
open import Cat.Internal.Instances.Discrete
open import Cat.Internal.Opposite
open import Cat.Internal.Functor.Outer

open import Cat.CartesianClosed.Locally
open import Cat.Instances.OuterFunctor
open import Cat.Diagram.Coequaliser.RegularEpi
open import Cat.Functor.Adjoint.Representable
open import Cat.Instances.Elements.Covariant renaming (∫ to ∫cov)
open import Cat.Instances.StrictCat.Cohesive hiding (Disc)
open import Cat.Monoidal.Instances.Cartesian
open import Cat.Diagram.Pullback.Properties
open import Cat.Functor.Adjoint.Continuous
open import Cat.Functor.Adjoint.Reflective
open import Cat.Diagram.Colimit.Universal
open import Cat.Diagram.Coproduct.Indexed
open import Cat.Functor.Hom.Representable
open import Cat.Instances.Sets.Cocomplete
open import Cat.Instances.Functor.Limits
open import Cat.Diagram.Limit.Equaliser
open import Cat.Diagram.Product.Indexed
open import Cat.Functor.Adjoint.Compose
open import Cat.Functor.FullSubcategory
open import Cat.Instances.Sets.Complete
open import Cat.Diagram.Colimit.Cocone
open import Cat.Diagram.Limit.Pullback
open import Cat.Functor.Hom.Properties
open import Cat.Instances.Localisation
open import Cat.Morphism.Factorisation
open import Cat.Diagram.Monad.Kleisli
open import Cat.Functor.Adjoint.Monad
open import Cat.Functor.Kan.Pointwise
open import Cat.Diagram.Colimit.Base
open import Cat.Diagram.Limit.Finite
open import Cat.Functor.Conservative
open import Cat.Functor.Hom.Coyoneda
open import Cat.Diagram.Coequaliser
open import Cat.Functor.Adjoint.Hom
open import Cat.Functor.Adjoint.Kan
open import Cat.Functor.Equivalence
open import Cat.Functor.Kan.Adjoint
open import Cat.Functor.Subcategory
open import Cat.Instances.Delooping
open import Cat.Instances.StrictCat
open import Cat.Morphism.Orthogonal
open import Cat.Diagram.Limit.Base
open import Cat.Diagram.Limit.Cone
open import Cat.Functor.Hom.Yoneda
open import Cat.Functor.Properties
open import Cat.Instances.Discrete
open import Cat.Morphism.StrongEpi
open import Cat.Diagram.Equaliser
open import Cat.Instances.Functor
open import Cat.Instances.Karoubi
open import Cat.Instances.Product
open import Cat.Diagram.Pullback
open import Cat.Diagram.Terminal
open import Cat.Functor.Kan.Base
open import Cat.Functor.Morphism
open import Cat.Diagram.Initial
open import Cat.Diagram.Product
open import Cat.Diagram.Pushout
open import Cat.Functor.Adjoint
open import Cat.Functor.Compose
open import Cat.Instances.Comma
open import Cat.Instances.Slice
open import Cat.Functor.Closed
open import Cat.Instances.Free
open import Cat.Instances.Sets
open import Cat.Diagram.Monad
open import Cat.Functor.Final
open import Cat.Functor.Base
open import Cat.Functor.Hom
open import Cat.Morphism
open import Cat.Prelude
open import Cat.Strict
open import Cat.Diagram.Idempotent

open import Data.Set.Surjection

open import Order.Cat
```
-->
```agda
module Borceux where
```

Though the 1Lab is not purely a formalization of category theory, it does
aim to be a useful reference on the subject. However, the 1Lab organizes
content in a highly non-linear fashion; this can make it somewhat difficult
to use as a companion to more traditional resources.

This page attempts to (somewhat) rectify this situation by gathering all
of the results from Francis Borceux's "Handbook of Categorical Algebra"
[@Borceux:vol1] in a single place.^[It also serves as an excellent place to
find possible contributions!]

# Volume 1

## 1 The language of categories

### 1.1 Logical foundations of the theory

* Proposition 1.1: [Russell's paradox]
* Definition 1.1.2: ❌
* Proposition 1.1.3: ❌
* Proposition 1.1.6: ❌

[Russell's paradox]: 1Lab.Counterexamples.Russell.html

## 1.2 Categories and functors

<!--
```agda
_ = Precategory
_ = Functor
_ = is-strict
_ = Strict-cats
_ = Sets
_ = Groups
_ = poset→category
_ = Disc
_ = B
_ = Slice
_ = Ab↪Sets
_ = Hom[_,-]
_ = Const
```
-->

* Definition 1.2.1: `Precategory`{.Agda}
* Definition 1.2.2: `Functor`{.Agda}
* Definition 1.2.3: `is-strict`{.Agda}
* Proposition 1.2.4: `Strict-cats`{.Agda}
* Examples 1.2.5:
  * a. `Sets`{.Agda}
  * b. ❌
  * c. `Groups`{.Agda}
  * d. ❌
  * e. ❌
  * f. ❌
  * g. ❌
  * h. ❌
* Examples 1.2.6:
  * a. ❌
  * b. `poset→category`{.Agda}
  * c. `Disc`{.Agda}
  * d. `B`{.Agda}
* Examples 1.2.7:
  * a. `Slice`{.Agda}
  * b. ❌
  * c. ❌
* Examples 1.2.8:
  * a. `Ab↪Sets`{.Agda}
  * b. ❌
  * c. ❌
  * d. `Hom[_,-]`{.Agda}
  * e. `Const`{.Agda}

### 1.3 Natural transformations

<!--
```agda
_ = _=>_
_ = Cat[_,_]
_ = _◆_
_ = よcov₁
_ = yo-is-equiv
_ = yo-naturalr
_ = yo-naturall
```
-->

* Definition 1.3.1: `_=>_`{.Agda}
* Proposition 1.3.2: `Cat[_,_]`{.Agda}
* Theorem 1.3.3:
  * 1. `yo-is-equiv`{.Agda}
  * 2. `yo-naturalr`{.Agda}
  * 3. `yo-naturall`{.Agda}
* Proposition 1.3.4: `_◆_`{.Agda}
* Proposition 1.3.5: ❌
* Examples 1.3.6:
  * a. ❌
  * b. ❌
  * c. `よcov₁`{.Agda}
  * d. `const-nt`{.Agda}

### 1.4 Contravariant functors

Borceux defines contravariant functors as a distinct object rather than
functors from $\cC\op$; this makes it somewhat difficult to map
definitions on a 1-1 basis.

<!--
```agda
_ = _^op
_ = よcov
_ = よ₀
_ = よ₁
_ = よ
```
-->

* Definition 1.4.1: `_^op`{.Agda}
* Definition 1.4.2: `_^op`{.Agda}
* Examples 1.4.3:
  * a. `よcov`{.Agda}
  * b. `よ₀`{.Agda}
  * c. `よ₁`{.Agda}
  * d. `よ`{.Agda}
  * e. ❌
  * f. ❌

### 1.5 Full and faithful functors

<!--
```agda
_ = is-faithful
_ = is-full
_ = is-fully-faithful
_ = is-precat-iso
_ = よ-is-fully-faithful
_ = よcov-is-fully-faithful
_ = Subcat
_ = Restrict
```
-->

* Definition 1.5.1:
  * 1. `is-faithful`{.Agda}
  * 2. `is-full`{.Agda}
  * 3. `is-fully-faithful`{.Agda}
  * 4. `is-precat-iso`{.Agda}
* Proposition 1.5.2:
  * 1. `よ-is-fully-faithful`{.Agda}
  * 2. `よcov-is-fully-faithful`{.Agda}
* Definition 1.5.3: `Subcat`{.Agda}
* Definition 1.5.4: `Restrict`{.Agda}

### 1.6 Comma categories

<!--
```agda
_ = _↓_
_ = Dom
_ = Cod
_ = θ
_ = ∫cov
_ = _×ᶜ_
_ = Cat⟨_,_⟩
```
-->

* Definition 1.6.1: `_↓_`{.Agda}
* Proposition 1.6.2:
  * 1. `Dom`{.Agda}
  * 2. `Cod`{.Agda}
  * 3. `θ`{.Agda}
* Proposition 1.6.3: ❌
* Definition 1.6.4: `∫cov`{.Agda}
* Definition 1.6.5: `_×ᶜ_`{.Agda}
* Proposition 1.6.6: `Cat⟨_,_⟩`{.Agda}

### 1.7 Monomorphisms

<!--
```agda
_ = is-monic
_ = id-monic
_ = monic-∘
_ = monic-cancell
_ = has-section
_ = has-retract
_ = has-retract→monic
_ = faithful→reflects-mono
_ = embedding→monic
_ = monic→is-embedding
```
-->

* Definition 1.7.1: `is-monic`{.Agda}
* Proposition 1.7.2:
  * 1. `id-monic`{.Agda}
  * 2. `monic-∘`{.Agda}
  * 3. `monic-cancell`{.Agda}
* Definition 1.7.3:
  * 1. `has-section`{.Agda}
  * 2. `has-retract`{.Agda}
* Proposition 1.7.4: `has-retract→monic`{.Agda}
* Definition 1.7.5: ❌
* Proposition 1.7.6: `faithful→reflects-mono`{.Agda}
* Examples 1.7.7:
  * a. `embedding→monic`{.Agda}, `monic→is-embedding`{.Agda}
  * b. ❌
  * c. ❌
  * d. ❌
  * e. ❌
  * f. ❌
  * g. ❌
  * h. ❌

### 1.8 Epimorphisms

<!--
```agda
_ = is-epic
_ = id-epic
_ = epic-∘
_ = epic-cancelr
_ = has-section→epic
_ = faithful→reflects-epi
_ = surjective→regular-epi
_ = epi→surjective
```
-->

* Definition 1.8.1: `is-epic`{.Agda}
* Proposition 1.8.2:
  * 1. `id-epic`{.Agda}
  * 2. `epic-∘`{.Agda}
  * 3. `epic-cancelr`{.Agda}
* Proposition 1.8.3: `has-section→epic`{.Agda}
* Proposition 1.8.4: `faithful→reflects-epi`{.Agda}
* Examples 1.8.5:
  * a. `surjective→regular-epi`{.Agda}, `epi→surjective`{.Agda}
  * b. ❌
  * c. ❌
  * d. ❌
  * e. ❌
  * f. ❌
  * g. ❌

### 1.9 Isomorphisms

<!--
```agda
_ = is-invertible
_ = id-invertible
_ = invertible-∘
_ = invertible→monic
_ = invertible→epic
_ = has-retract+epic→invertible
_ = F-iso.F-map-invertible
_ = is-ff→is-conservative
_ = equiv≃iso
```
-->

* Definition 1.9.1: `is-invertible`{.Agda}
* Proposition 1.9.2:
  * 1. `id-invertible`{.Agda}
  * 2. `invertible-∘`{.Agda}
  * 3. `invertible→monic`{.Agda}, `invertible→epic`{.Agda}
* Proposition 1.9.3: `has-retract+epic→invertible`{.Agda}
* Proposition 1.9.4: `F-iso.F-map-invertible`{.Agda}
* Proposition 1.9.5: `is-ff→is-conservative`{.Agda}
* Examples 1.9.6:
  * a. `equiv≃iso`{.Agda}
  * b. ❌
  * c. ❌
  * d. ❌
  * e. ❌
  * f. ❌
  * g. ❌
  * h. ❌

### 1.10 The duality principle

<!--
```agda
_ = Hom[-,-]
```
-->

* Definition 1.10.1: `_^op`{.Agda}
* Examples 1.10.3:
  * a. `Hom[-,-]`
  * b. ❌
  * c. ❌
  * d. ❌

### 1.11 Exercises

<!--
```agda
_ = よ-preserves-mono
_ = よcov-reverses-epi
_ = has-section+monic→invertible
```
-->

* Exercise 1.11.1: 🚧 `thin-functor`{.Agda}
* Exercise 1.11.2: ❌
* Exercise 1.11.3: ❌
* Exercise 1.11.4: ❌
* Exercise 1.11.5: `よ-preserves-mono`{.Agda}
* Exercise 1.11.6: `よcov-reverses-epi`{.Agda}
* Exercise 1.11.7: ❌
* Exercise 1.11.8: 🚧 `Curry`{.Agda}, `Uncurry`{.Agda}
* Exercise 1.11.9: `has-section+monic→invertible`{.Agda}
* Exercise 1.11.10: ❌
* Exercise 1.11.12: ❌
* Exercise 1.11.13: ❌

## 2 Limits

## 2.1 Products

<!--
```agda
_ = is-product
_ = ×-Unique
_ = Binary-products.swap-is-iso
_ = Cartesian-monoidal
_ = is-indexed-product
_ = Indexed-product-unique
```
-->

* Definition 2.1.1: `is-product`{.Agda}
* Proposition 2.1.2: `×-Unique`{.Agda}
* Proposition 2.1.3:
  * 1. `Binary-products.swap-is-iso`{.Agda}
  * 2. `Cartesian-monoidal`{.Agda}
* Definition 2.1.4: `is-indexed-product`{.Agda}
* Proposition 2.1.5: `Indexed-product-unique`{.Agda}
* Proposition 2.1.6: ❌
* Examples 2.1.7:
  * a. ❌
  * b. ❌
  * c. ❌
  * d. ❌
  * e. ❌
  * f. ❌
  * g. ❌
  * h. ❌
  * i. ❌

## 2.2 Coproducts

<!--
```agda
_ = is-indexed-coproduct
```
-->

* Definition 2.2.1: `is-indexed-coproduct`{.Agda}
* Proposition 2.2.2: ❌
* Proposition 2.2.3: ❌
* Examples 2.2.4:
  * a. ❌
  * b. ❌
  * c. ❌
  * d. ❌
  * e. ❌
  * f. ❌
  * g. ❌
  * h. ❌
  * i. ❌

## 2.3 Initial and terminal objects

<!--
```agda
_ = is-initial
_ = is-terminal
_ = Sets-initial
_ = Sets-terminal
_ = Zero-group-is-zero
```
-->

* Definition 2.3.1:
  * 1. `is-terminal`{.Agda}
  * 2. `is-initial`{.Agda}
* Examples 2.3.2:
  * a. `Sets-initial`{.Agda}, `Sets-terminal`{.Agda}
  * b. 🚧 `Zero-group-is-zero`{.Agda}
  * c. ❌

## 2.4 Equalizers, coequalizers

<!--
```agda
_ = is-equaliser
_ = is-equaliser→is-monic
```
-->

* Definition 2.4.1: `is-equaliser`{.Agda}
* Proposition 2.4.2: ❌
* Proposition 2.4.3: `is-equaliser→is-monic`{.Agda}
* Proposition 2.4.4: ❌
* Proposition 2.4.5: ❌
* Examples 2.4.6:
  * a. ❌
  * b. ❌
  * c. ❌
  * d. ❌
  * e. ❌
  * f. ❌
  * g. ❌

## 2.5 Pullbacks, pushouts

<!--
```agda
_ = is-pullback
_ = Pullback-unique
_ = is-monic→pullback-is-monic
_ = is-effective-epi.is-effective-epi→is-regular-epi
_ = is-regular-epi→is-effective-epi
```
-->

* Definition 2.5.1: `is-pullback`{.Agda}
* Proposition 2.5.2: `Pullback-unique`{.Agda}
* Proposition 2.5.3:
  * 1. `is-monic→pullback-is-monic`{.Agda}
  * 2. ❌
* Definition 2.5.4: ❌
* Proposition 2.5.5: ❌
* Proposition 2.5.6: ❌
* Proposition 2.5.7: `is-effective-epi.is-effective-epi→is-regular-epi`{.Agda}
* Proposition 2.5.8: `is-regular-epi→is-effective-epi`{.Agda}
* Proposition 2.5.9:
  * 1. `pasting-left→outer-is-pullback`{.Agda}
  * 2. ❌
* Examples 2.5.10
  * a. `Sets-pullbacks`{.Agda}
  * b. ❌
  * c. ❌
  * d. ❌

### 2.6 Limits and colimits

<!--
```agda
_ = Cone
_ = is-limit
_ = limits-unique
_ = is-limit.unique₂
_ = Cocone
_ = is-colimit
_ = Limit→Equaliser
_ = Equaliser→Limit
_ = Limit→Pullback
_ = Pullback→Limit
```
-->

* Definition 2.6.1: `Cone`{.Agda}
* Definition 2.6.2: `is-limit`{.Agda}
* Proposition 2.6.3: `limits-unique`{.Agda}
* Proposition 2.6.4: `is-limit.unique₂`{.Agda}
* Definition 2.6.5: `Cocone`{.Agda}
* Definition 2.6.6: `is-colimit`{.Agda}
* Examples 2.6.7:
  * a. ❌
  * b. `Limit→Equaliser`{.Agda}, `Equaliser→Limit`{.Agda}
  * c. `Limit→Pullback`{.Agda}, `Pullback→Limit`{.Agda}
  * d. ❌
  * e. ❌
  * f. ❌

### 2.7 Complete categories

<!--
```agda
_ = is-complete
```
-->

* Proposition 2.7.1: ❌
* Definition 2.7.2: `is-complete`{.Agda}

### 2.8 Existence theorem for limits

<!--
```agda
_ = with-equalisers
_ = with-pullbacks
```
-->

* Proposition 2.8.1: ❌
* Proposition 2.8.2:
  * 1. ❌
  * 2. `with-equalisers`{.Agda}
  * 3. `with-pullbacks`{.Agda}

* Proposition 2.8.3: ❌
* Definition 2.8.4: ❌
* Proposition 2.8.5: ❌
* Example 2.8.6: ❌

### 2.9 Limit preserving functors

<!--
```agda
_ = preserves-limit
_ = is-lex.pres-monos
_ = corepresentable-preserves-limits
_ = representable-reverses-colimits
_ = reflects-limit
_ = conservative-reflects-limits
```
-->

* Definition 2.9.1: `preserves-limit`{.Agda}
* Proposition 2.9.2: ❌
* Proposition 2.9.3: `is-lex.pres-monos`{.Agda}
* Proposition 2.9.4: `corepresentable-preserves-limits`{.Agda}
* Proposition 2.9.5: `representable-reverses-colimits`{.Agda}
* Definition 2.9.6: `reflects-limit`{.Agda}
* Proposition 2.9.7: `conservative-reflects-limits`{.Agda}
* Proposition 2.9.8: ❌
* Proposition 2.9.9: ❌
* Examples 2.9.10:
  * a. ❌
  * b. ❌
  * c. ❌
  * d. ❌
  * e. ❌

### 2.10 Absolute colimits

* Definition 2.10.1: ❌
* Proposition 2.10.2: ❌
* Examples 2.10.3:
  * a. ❌
  * b. ❌
  * c. ❌
  * d. ❌

### 2.11 Final functors

::: warning
Borceux uses some outdated terminology here , and also uses a condition
that is overly powerful. We opt to stick with the terminology from the
nLab instead.
:::

<!--
```agda
_ = is-final
_ = extend-is-colimit
_ = is-colimit-restrict
```
-->

* Definition 2.11.1: `is-final`{.Agda}
* Proposition 2.11.2: `extend-is-colimit`{.Agda}, `is-colimit-restrict`{.Agda}
* Propositon 2.11.3: ❌
* Proposition 2.11.4: ❌
* Corollary 2.11.5: ❌

### 2.12 Interchange of limits

* Proposition 2.12.1: ❌
* Examples 2.12.2
  * a. ❌
  * b. ❌

### 2.13 Filtered colimits

* Definition 2.13.1: ❌
* Lemma 2.13.2: ❌
* Proposition 2.13.3: ❌
* Theorem 2.13.4: ❌
* Proposition 2.13.5: ❌
* Corollary 2.11.6: ❌
* Proposition 2.13.7: ❌
* Examples 2.13.8:
  * a. ❌
  * b. ❌
  * c. ❌
  * d ❌
* Counterexample 2.13.9: ❌

### 2.14 Universality of colimits


<!--
```agda
_ = has-stable-colimits
```
-->

* Definition 2.14.1: `has-stable-colimits`{.Agda}
* Theorem 2.14.2: ❌

### 2.15 Limits in categories of functors

<!--
```agda
_ = functor-limit
_ = Functor-cat-is-complete
_ = coyoneda
```
-->

* Proposition 2.15.1: `functor-limit`{.Agda}
* Theorem 2.15.2: `Functor-cat-is-complete`{.Agda}
* Proposition 2.15.3: ❌
* Corollary 2.15.4: ❌
* Proposition 2.15.5: ❌
* Proposition 2.15.6: `coyoneda`{.Agda}
* Examples 2.15.7:
  * a. ❌
  * b. ❌

### 2.16 Limits in comma categories

* Proposition 2.16.1: ❌
* Corollary 2.16.2: ❌
* Proposition 2.16.3: ❌

### 2.17 Exercises

<!--
```agda
_ = Cone→cone
```
-->

* Exercise 2.17.1: ❌
* Exercise 2.17.2: ❌
* Exercise 2.17.3: 🚧 `Cone→cone`{.Agda}
* Exercises 2.17.4: ❌
* Exercises 2.17.5: ❌
* Exercises 2.17.6: ❌
* Exercises 2.17.7: ❌
* Exercises 2.17.8: `extend-is-colimit`{.Adga}, `is-colimit-restrict`{.Agda}
* Exercises 2.17.9: ❌
* Exercises 2.17.10: ❌

## 3 Adjoint functors

### 3.1 Reflection along a functor

<!--
```agda
_ = Free-object
_ = free-object-unique
_ = free-objects→left-adjoint
_ = _⊣_
_ = free-objects≃left-adjoint
_ = hom-iso→adjoints
_ = make-free-group
_ = Free-monoid⊣Forget
_ = Disc⊣Γ
_ = Γ⊣Codisc
```
-->

* Definition 3.1.1: `Free-object`{.Agda}
* Proposition 3.1.2: `free-object-unique`{.Agda}
* Proposition 3.1.3: `free-objects→left-adjoint`{.Agda}
* Definition 3.1.4: `_⊣_`
* Theorem 3.1.5: `free-objects≃left-adjoint`{.Agda}, `hom-iso→adjoints`{.Agda}
* Examples 3.1.6:
  * a. `Free-monoid⊣Forget`{.Agda}
  * b. `make-free-group`{.Agda}
  * c. ❌
  * d. ❌
  * e. ❌
  * f. ❌
  * g. ❌
  * h. ❌
  * i. ❌
  * j. ❌
  * k. `Disc⊣Γ`{.Agda}, `Γ⊣Codisc`{.Agda}
  * l. ❌
  * m. ❌

### 3.2 Properties of adjoint functors

<!--
```agda
_ = LF⊣GR
_ = right-adjoint-is-continuous
```
-->

* Proposition 3.2.1: `LF⊣GR`{.Agda}
* Proposition 3.2.2: `right-adjoint-is-continuous`{.Agda}
* Proposition 3.2.3: ❌
* Proposition 3.2.4: ❌

### 3.3 The adjoint functor theorem

* Proposition 3.3.1: ❌
* Definition 3.3.2: ❌
* Theorem 3.3.3: ❌
* Theorem 3.3.4: ❌
* Corollary 3.3.5: ❌
* Corollary 3.3.6: ❌
* Corollary 3.3.7: ❌
* Proposition 3.3.8: ❌
* Examples 3.3.9:
  * a. ❌
  * b. ❌
  * c. ❌
  * d. ❌
  * e. ❌

### 3.4 Fully faithful adjoint functors

<!--
```agda
_ = is-reflective→counit-is-iso
_ = is-counit-iso→is-reflective
_ = is-equivalence
```
-->

* Proposition 3.4.1:
  (⇒). `is-reflective→counit-is-iso`{.Agda}
  (⇐). `is-counit-iso→is-reflective`{.Agda}

* Proposition 3.4.2: ❌
* Proposition 3.4.3: ❌
* Definition 3.4.4: `is-equivalence`{.Adga}
* Propositino 3.4.5: ❌

### 3.5 Reflective subcategories

<!--
```agda
_ = is-reflective
```
-->

* Definition 3.5.1: ❌
* Definition 3.5.2: `is-reflective`{.Agda}
* Proposition 3.5.3: ❌
* Proposition 3.5.4: ❌
* Definition 3.5.5: ❌
* Definition 3.5.6: ❌
* Proposition 3.5.7: ❌

### 3.6 Epireflective subcategories

* Definition 3.6.1: ❌
* Proposition 3.6.2: ❌
* Definition 3.6.3: ❌
* Proposition 3.6.4: ❌

### 3.7 Kan extensions

<!--
```agda
_ = is-lan
_ = is-ran
_ = cocomplete→lan
_ = ff→pointwise-lan-ext
_ = left-adjoint→left-extension
_ = is-initial-cocone→is-colimit
_ = is-colimit→is-initial-cocone
_ = is-colimit→is-initial-cocone
_ = adjoint→is-absolute-lan
```
-->

* Definition 3.7.1: `is-lan`{.Agda}
* Theorem 3.7.2: `cocomplete→lan`{.Agda}
* Proposition 3.7.3: `ff→pointwise-lan-ext`{.Agda}
* Proposition 3.7.4: `left-adjoint→left-extension`{.Agda}
* Proposition 3.7.5:
  * (⇒) `is-initial-cocone→is-colimit`{.Agda}
  * (⇐) `is-colimit→is-initial-cocone`{.Agda}
* Proposition 3.7.6:
  * (1 ⇒ 2) `adjoint→is-lan-id`{.Agda}, `adjoint→is-absolute-lan`{.Agda}
  * (2 ⇒ 3) ❌
  * (3 ⇒ 1) ❌

### 3.8 Tensor products of set-valued functors

Proposition 3.8.1: ❌

### 3.9 Exercises

<!--
```agda
_ = right-adjoint→objectwise-rep
_ = corepresentable→left-adjoint
_ = Karoubi-is-completion
```
-->

* Exercise 3.9.1: ❌
* Exercise 3.9.2:
  * (⇒) `corepresentable→left-adjoint`{.Agda}
  * (⇐) `right-adjoint→objectwise-rep`
* Exercise 3.9.3: `Karoubi-is-completion`{.Agda}
* Exercise 3.9.4: ❌
* Exercise 3.9.5: ❌
* Exercise 3.9.6: ❌
* Exercise 3.9.7: ❌

## 4 Generators and Projectives

### 4.1 Well-powered categories

* Definition 4.1.1: ❌
* Definition 4.1.2: ❌

### 4.2 Intersection and union

* Definitionn 4.2.1: ❌
* Proposition 4.2.2: ❌
* Proposition 4.2.3: ❌
* Proposition 4.2.4: ❌
* Corollary 4.2.5: ❌
* Proposition 4.2.6: ❌

### 4.3 Strong epimorphisms

<!--
```agda
_ = is-regular-epi
_ = is-strong-epi
_ = strong-epi-compose
_ = strong-epi-cancel-l
_ = strong-epi-mono→is-invertible
_ = is-regular-epi→is-strong-epi
_ = is-strong-epi→is-extremal-epi
_ = equaliser-lifts→is-strong-epi
_ = is-extremal-epi→is-strong-epi
```
-->

* Definition 4.3.1: `is-regular-epi`{.Agda}
* Definition 4.3.2: ❌
* Proposition 4.3.3: ❌
* Proposition 4.3.4: ❌
* Definition 4.3.5: `is-strong-epi`{.Agda}
* Proposition 4.3.6:
  * 1. `strong-epi-compose`{.Agda}
  * 2. `strong-epi-cancel-l`{.Agda}
  * 3. `strong-epi-mono→is-invertible`{.Agda}
  * 4. `is-regular-epi→is-strong-epi`{.Agda}
  * 5. `is-strong-epi→is-extremal-epi`{.Agda}
* Proposition 4.3.7:
  * 1. `equaliser-lifts→is-strong-epi`{.Agda}
  * 2. `is-extremal-epi→is-strong-epi`{.Agda}
  * 3. ❌
* Proposition 4.3.8: ❌
* Proposition 4.3.9: ❌
* Examples 4.3.10:
  * a. ❌
  * b. ❌
  * c. ❌
  * d. ❌
  * e. ❌
  * f. ❌
  * g. ❌

### 4.4 Epi-mono factorizations

* Definition 4.4.1: ❌
* Proposition 4.4.2: ❌
* Proposition 4.4.3: ❌
* Definition 4.4.4: ❌
* Proposition 4.4.5: ❌
* Proposition 4.4.6: ❌

### 4.5 Generators

* Definition 4.5.1: ❌
* Proposition 4.5.2: ❌
* Definition 4.5.3: ❌
* Definition 4.5.4: ❌
* Proposition 4.5.5: ❌
* Proposition 4.5.6: ❌
* Definition 4.5.7: ❌
* Proposition 4.5.8: ❌
* Corollary 4.5.9: ❌
* Proposition 4.5.10: ❌
* Corollary 4.5.11: ❌
* Proposition 4.5.12: ❌
* Definition 4.5.13: ❌
* Proposition 4.5.14: ❌
* Proposition 4.5.15: ❌
* Proposition 4.5.16: ❌
* Examples 4.5.17
  * a. ❌
  * b. ❌
  * c. ❌
  * d. ❌
  * e. ❌
  * f. ❌
  * g. ❌
  * h. ❌
  * i. ❌

### 4.6 Projectives

* Definition 4.6.1: ❌
* Proposition 4.6.2: ❌
* Proposition 4.6.3: ❌
* Proposition 4.6.4: ❌
* Definition 4.6.5: ❌
* Proposition 4.6.6: ❌
* Proposition 4.6.7: ❌
* Examples 4.7.8:
  * a. ❌
  * b. ❌
  * c. ❌
  * d. ❌
  * e. ❌
  * f. ❌
  * g. ❌

### 4.7 Injective cogenerators

* Proposition 4.7.1: ❌
* Proposition 4.7.2: ❌
* Proposition 4.7.3: ❌
* Proposition 4.7.4: ❌
* Proposition 4.7.5: ❌
* Proposition 4.7.6: ❌
* Proposition 4.7.7: ❌
* Proposition 4.7.8: ❌

### 4.8 Exercises

* Exercise 4.8.1: ❌
* Exercise 4.8.2: ❌
* Exercise 4.8.3: ❌
* Exercise 4.8.4: ❌
* Exercise 4.8.5: ❌
* Exercise 4.8.6: ❌

## 5 Categories of fractions

### 5.1 Graphs and path categories

<!--
```agda
_ = Graph
_ = Path-in
_ = Path-category
```
-->

* Definition 5.1.1: `Graph`{.Agda}
* Definition 5.1.2: ❌
* Definition 5.1.3: `Path-in`{.Agda}
* Proposition 5.1.4: `Path-category`{.Agda}
* Definition 5.1.5: ❌
* Proposition 5.1.6: ❌
* Proposition 5.1.7: ❌

### 5.2 Calculus of fractions

<!--
```agda
_ = Localisation
```
-->

* Definition 5.2.1: ❌
* Proposition 5.2.2: `Localisation`{.Agda}
* Definition 5.2.3: ❌
* Proposition 5.2.4: ❌
* Proposition 5.2.5: ❌
* Definition 5.2.6: ❌

### 5.3 Reflective subcategories as categories of fractinos

* Proposition 5.3.1: ❌

### 5.4 The orthogonal subcategory problem

<!--
```agda
_ = m⊥m
_ = m⊥o
_ = o⊥m
_ = object-orthogonal-!-orthogonal
_ = in-subcategory→orthogonal-to-inverted
_ = orthogonal-to-ηs→in-subcategory
_ = in-subcategory→orthogonal-to-ηs
```
-->

* Definition 5.4.1: `m⊥m`{.Agda}
* Definition 5.4.2:
  1. `m⊥o`
  2. `o⊥m`
* Proposition 5.4.3: `object-orthogonal-!-orthogonal`{.Agda}
* Proposition 5.4.4:
  * 1.
    * (a ⇒ b) `in-subcategory→orthogonal-to-inverted`{.Agda}
    * (a ⇒ c) `in-subcategory→orthogonal-to-ηs`{.Agda}
    * (b ⇒ a) ❌
    * (b ⇒ c) ❌
  * 2. ❌
* Definition 5.4.5: ❌
* Proposition 5.4.6: ❌
* Theorem 5.4.7: ❌
* Corollary 5.4.8: ❌
* Definition 5.4.9: ❌
* Proposition 5.4.10: ❌

### 5.5 Factorisation systems

<!--
```agda
_ = is-factorisation-system
_ = factorisation-essentially-unique
_ = E-is-⊥M
```
-->

* Definition 5.5.1: `is-factorisation-system`{.Agda}
* Proposition 5.5.2: `factorisation-essentially-unique`{.Agda}
* Proposition 5.5.3: 🚧 `E-is-⊥M`{.Agda}
* Proposition 5.5.4:
  * 1. ❌
  * 2. ❌
  * 3. `in-intersection≃is-iso`{.Agda}
* Proposition 5.5.5: ❌
* Proposition 5.5.6: ❌

### 5.6 The case of localisations

* Proposition 5.6.1: ❌
* Proposition 5.6.2: ❌
* Lemma 5.6.3: ❌
* Proposition 5.6.4: ❌

### 5.7 Universal closure operations

* Definition 5.7.1: ❌
* Proposition 5.7.2: ❌
* Definition 5.7.3: ❌
* Proposition 5.7.4: ❌
* Corollary 5.7.5: ❌
* Corollary 5.7.6: ❌
* Proposition 5.7.7: ❌
* Corollary 5.7.8: ❌
* Proposition 5.7.9: ❌
* Corollary 5.7.10: ❌
* Proposition 5.7.11: ❌
* Examples 5.7.12:
  * a. ❌
  * b. ❌
  * c. ❌

### 5.8 The calculus of bidense morphisms

* Definition 5.8.1: ❌
* Proposition 5.8.2: ❌
* Proposition 5.8.3: ❌
* Proposition 5.8.4: ❌
* Proposition 5.8.5: ❌
* Proposition 5.8.6: ❌
* Corollary 5.8.7: ❌
* Proposition 5.8.8: ❌
* Lemma 5.8.9: ❌
* Corllary 5.8.10: ❌

### 5.9 Exercises

* Exercise 5.9.1: ❌
* Exercise 5.9.2: ❌
* Exercise 5.9.3: ❌
* Exercise 5.9.4: ❌
* Exercise 5.9.5: ❌
* Exercise 5.9.6: ❌

## 6 Flat functors and Cauchy completeness

### 6.1 Exact functors

<!--
```agda
_ = is-lex
```
-->

* Definition 6.1.1: `is-lex`{.Agda}
* Proposition 6.1.2: ❌
* Proposition 6.1.3: ❌
* Proposition 6.1.4: ❌

### 6.2 Left exact reflection of a functor

* Proposition 6.2.1: ❌
* Proposition 6.2.2: ❌
* Proposition 6.2.3: ❌
* Proposition 6.2.4: ❌
* Theorem 6.2.5: ❌

### 6.3 Flat functors

* Definition 6.3.1: ❌
* Proposition 6.3.2: ❌
* Proposition 6.3.3: ❌
* Proposition 6.3.4: ❌
* Proposition 6.3.5: ❌
* Proposition 6.3.6: ❌
* Proposition 6.7.7: ❌
* Proposition 6.7.8: ❌

### 6.4 The relevance of regular cardinals

* Definition 6.4.1: ❌
* Definition 6.4.2: ❌
* Definition 6.4.3: ❌
* Lemma 6.4.4: ❌
* Theorem 6.4.5: ❌
* Definition 6.4.6: ❌
* Proposition 6.4.7: ❌
* Proposition 6.4.8: ❌
* Proposition 6.4.9: ❌
* Definition 6.4.10: ❌
* Proposition 6.4.11: ❌
* Proposition 6.4.12: ❌
* Proposition 6.4.13: ❌
* Corollary 6.4.14: ❌
* Definition 6.4.15: ❌

### 6.5 The splitting of idempotents

<!--
```agda
_ = is-idempotent
_ = is-split→is-idempotent
_ = is-split
_ = is-idempotent-complete
```
-->

* Definition 6.5.1: `is-idempotent`{.Agda}
* Proposition 6.5.2: `is-split→is-idempotent`{.Agda}
* Definition 6.5.3: `is-split`{.Agda}
* Proposition 6.5.4: ❌
* Definition 6.5.5: ❌
* Proposition 6.5.6: ❌
* Proposition 6.5.7: ❌
* Definition 6.5.8: `is-idempotent-complete`{.Agda}
* Proposition 6.5.9: `Karoubi-is-completion`{.Agda}
  * 1. ❌
  * 2. ❌
  * 3. ❌
* Lemma 6.5.10: ❌
* Theorem 6.5.11: ❌

### 6.6 The more general adjoint functor theorem

* Theorem 6.6.1: ❌

### 6.7 Exercises

* Exercise 6.7.1: ❌
* Exercise 6.7.2: ❌
* Exercise 6.7.3: ❌
* Exercise 6.7.4: ❌
* Exercise 6.7.5: ❌
* Exercise 6.7.6: ❌
* Exercise 6.7.7: ❌
* Exercise 6.7.8: ❌
* Exercise 6.7.9: ❌
* Exercise 6.7.10: ❌
* Exercise 6.7.11: ❌

## 7 Bicategories and distributors

### 7.1 2-categories

* Definition 7.1.1: ❌
* Definition 7.1.2: ❌
* Definition 7.1.3: ❌
* Examples 7.1.4:
  * a. ❌
  * b. ❌
  * c. ❌
  * d. ❌

### 7.2 2-functors and 2-natural transformations

* Definition 7.2.1: ❌
* Definition 7.2.2: ❌
* Proposition 7.2.3: ❌
* Examples 7.2.4:
  * a. ❌
  * b. ❌

### 7.3 Modifications and n-categories

* Definition 7.3.1: ❌
* Definition 7.3.2: ❌
* Proposition 7.3.3: ❌

### 7.4 2-limits and bilimits

* Definition 7.4.1: ❌
* Proposition 7.4.2: ❌
* Examples 7.4.3:
  * a. ❌
  * b. ❌

* Definition 7.4.4: ❌
* Proposition 7.4.5: ❌

### 7.5 Lax functors and pseudo-functors

* Definition 7.5.1: ❌
* Definition 7.5.2: ❌
* Definition 7.5.3: ❌
* Proposition 7.5.4: ❌

### 7.6 Lax limits and pseudo-limits

* Definition 7.6.1: ❌
* Proposition 7.6.2: ❌
* Example 7.6.3: ❌

### 7.7 Bicategories

<!--
```agda
_ = Prebicategory
_ = _⊣ᵇ_
_ = Spanᵇ
```
-->

* Definition 7.7.1: `Prebicategory`{.Agda}
* Definition 7.7.2: `_⊣ᵇ_`{.Agda}
* Example 7.7.3: `Spanᵇ`{.Agda}
* Example 7.7.4: ❌

### 7.8 Distributors

* Definition 7.8.1: ❌
* Proposition 7.8.2: ❌
* Example 7.8.3: ❌
* Example 7.8.4: ❌
* Proposition 7.8.5: ❌

### 7.9 Cauchy completeness versus distributors

* Proposition 7.9.1: ❌
* Proposition 7.9.2: ❌
* Theorem 7.9.3: ❌
* Theorem 7.9.4: ❌

### 7.10 Exercises

* Exercise 7.10.1: ❌
* Exercise 7.10.2: ❌
* Exercise 7.10.3: ❌
* Exercise 7.10.4: ❌
* Exercise 7.10.5: ❌
* Exercise 7.10.6: ❌
* Exercise 7.10.7: ❌
* Exercise 7.10.9: ❌
* Exercise 7.10.10: ❌
* Exercise 7.10.11: ❌
* Exercise 7.10.12: ❌

## 8 Internal category theory

### 8.1 Internal categories and functors

<!--
```agda
_ = Internal-cat
_ = Internal-functor
_ = _=>i_
_ = Disci
_ = _^opi
```
-->

* Definition 8.1.1: `Internal-cat`{.Agda}
* Definition 8.1.2: `Internal-functor`{.Agda}
* Definition 8.1.3: `_=>i_`{.Agda}
* Proposition 8.1.4: ❌
* Proposition 8.1.5: ❌
* Examples 8.1.6:
  * a. `Disci`{.Agda}
  * b. ❌
  * c. `_^opi`{.Agda}

### 8.2 Internal base-valued functors

<!--
```agda
_ = Outer-functor
_ = _=>o_
_ = Outer-functors
_ = ConstO
```
-->

* Definition 8.2.1: `Outer-functor`{.Agda}
* Definition 8.2.2: `_=>o_`{.Agda}
* Proposition 8.2.3: `Outer-functors`{.Agda}
* Example 8.2.4: `ConstO`{.Agda}, `const-nato`{.Agda}
* Proposition 8.2.5: ❌
* Proposition 8.2.6: ❌
* Definition 8.2.7: ❌
* Definition 8.2.8: ❌

### 8.3 Internal limits and colimits

* Definition 8.3.1: ❌
* Proposition 8.3.2: ❌
* Definition 8.3.3: ❌
* Proposition 8.3.4: ❌
* Proposition 8.3.5: ❌

### 8.4 Exercises

* Exercise 8.4.1: ❌
* Exercise 8.4.2: ❌
* Exercise 8.4.3: ❌
* Exercise 8.4.4: ❌
* Exercise 8.4.5: ❌
* Exercise 8.4.6:
  * (⇒) `dependent-product→lcc`{.Agda}
  * (⇐) `lcc→dependent-product`{.Agda}
* Exercises 8.4.7: ❌
