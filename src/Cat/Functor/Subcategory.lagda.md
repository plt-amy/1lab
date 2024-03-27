<!--
```agda
open import Cat.Functor.Properties
open import Cat.Univalent
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Functor.Subcategory where
```

# Subcategories {defines="subcategory"}

A **subcategory** $\cD \mono \cC$ is specified by a [predicate]
$P : C \to \prop$ on objects, and a predicate $Q : P(x) \to P(y) \to \cC(x,y) \to \prop$
on morphisms between objects within $P$ that is closed under identities
and composites.

[predicate]: 1Lab.HLevel.html#is-prop

To start, we package up all the data required to define a subcategory up
into a record. Note that we omit the requirement that the predicate on
objects is a proposition; this tends to be ill-behaved unless the $\cC$
is univalent.

<!--
```agda
module _ {o ℓ} (C : Precategory o ℓ) where
  open Cat.Reasoning C
```
-->

```agda
  record Subcat (o' ℓ' : Level) : Type (o ⊔ ℓ ⊔ lsuc o' ⊔ lsuc ℓ') where
    no-eta-equality
    field
      is-ob : Ob → Type o'
      is-hom : ∀ {x y} (f : Hom x y) → is-ob x → is-ob y → Type ℓ'
      is-hom-prop
        : ∀ {x y} (f : Hom x y) (px : is-ob x) (py : is-ob y)
        → is-prop (is-hom f px py)
      is-hom-id : ∀ {x} → (px : is-ob x) → is-hom id px px
      is-hom-∘
        : ∀ {x y z} {f : Hom y z} {g : Hom x y}
        → {px : is-ob x} {py : is-ob y} {pz : is-ob z}
        → is-hom f py pz → is-hom g px py
        → is-hom (f ∘ g) px pz
```

Morphisms of wide subcategories are defined as morphisms in $\cC$ where
$Q$ holds.

```agda
module _ {o o' ℓ ℓ'} {C : Precategory o ℓ} (subcat : Subcat C o' ℓ') where
  open Cat.Reasoning C
  open Subcat subcat

  record Subcat-hom (x y : Σ[ ob ∈ Ob ] (is-ob ob)) : Type (ℓ ⊔ ℓ') where
    no-eta-equality
    constructor sub-hom
    field
      hom : Hom (x .fst) (y .fst)
      witness : subcat .is-hom hom (x .snd) (y .snd)

open Subcat-hom
```

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} where
  private module C = Precategory C

  instance
    Membership-subcat-ob : ∀ {o' ℓ'} → Membership C.Ob (Subcat C o' ℓ') _
    Membership-subcat-ob = record { _∈_ = λ o S → o ∈ S .Subcat.is-ob }

module _ {o o' ℓ ℓ'} {C : Precategory o ℓ} {S : Subcat C o' ℓ'} where
  open Cat.Reasoning C
  open Subcat S

  Subcat-hom-pathp
    : {x x' y y' : Σ[ ob ∈ C ] (ob ∈ S)}
    → {f : Subcat-hom S x y} {g : Subcat-hom S x' y'}
    → (p : x ≡ x') (q : y ≡ y')
    → PathP (λ i → Hom (p i .fst) (q i .fst)) (f .hom) (g .hom)
    → PathP (λ i → Subcat-hom S (p i) (q i)) f g
  Subcat-hom-pathp p q r i .hom = r i
  Subcat-hom-pathp {f = f} {g = g} p q r i .witness =
    is-prop→pathp (λ i → is-hom-prop (r i) (p i .snd) (q i .snd)) (f .witness) (g .witness) i

  instance
    Extensional-subcat-hom
      : ∀ {ℓr x y} ⦃ sa : Extensional (Hom (x .fst) (y .fst)) ℓr ⦄
      → Extensional (Subcat-hom S x y) ℓr
    Extensional-subcat-hom ⦃ sa ⦄ = injection→extensional!
      (Subcat-hom-pathp refl refl) sa

    Funlike-Subcat-hom
      : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {x y}
      → ⦃ _ : Funlike (Hom (x .fst) (y .fst)) A B ⦄ → Funlike (Subcat-hom S x y) A B
    Funlike-Subcat-hom ⦃ i ⦄ = record { _#_ = λ f x → apply (f .hom) x }

    H-Level-Subcat-hom : ∀ {x y n} → H-Level (Subcat-hom S x y) (2 + n)
    H-Level-Subcat-hom = basic-instance 2 $ Iso→is-hlevel 2 eqv $
      Σ-is-hlevel 2 (Hom-set _ _) λ _ →
      is-hlevel-suc 1 (is-hom-prop _ _ _)
      where unquoteDecl eqv = declare-record-iso eqv (quote Subcat-hom)
```
-->

We can then use this data to construct a category.

<!--
```agda
module _ {o o' ℓ ℓ'} {C : Precategory o ℓ} (subcat : Subcat C o' ℓ') where
  open Cat.Reasoning C
  open Subcat subcat
```
-->

```agda
  Subcategory : Precategory (o ⊔ o') (ℓ ⊔ ℓ')
  Subcategory .Precategory.Ob = ∫ₚ subcat
  Subcategory .Precategory.Hom = Subcat-hom subcat
  Subcategory .Precategory.Hom-set _ _ = hlevel 2
  Subcategory .Precategory.id .hom = id
  Subcategory .Precategory.id .witness = is-hom-id _
  Subcategory .Precategory._∘_ f g .hom = f .hom ∘ g .hom
  Subcategory .Precategory._∘_ f g .witness = is-hom-∘ (f .witness) (g .witness)
  Subcategory .Precategory.idr f = ext (idr _)
  Subcategory .Precategory.idl f = ext (idl _)
  Subcategory .Precategory.assoc f g h = ext (assoc _ _ _)
```

## From pseudomonic functors

There is another way of representing subcategories: By giving a
[faithful functor] $F : \cD \epi \cC$.

[faithful functor]: Cat.Functor.Properties.html

<!--
```agda
module _
  {o o' ℓ ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'}
  {F : Functor C D}
  (faithful : is-faithful F)
  where
  open Functor F
  private
    module C = Cat.Reasoning C
    module D = Cat.Reasoning D
```
-->

We construct a subcategory from a faithful functor $F$ by restricting to
the objects in the [essential image] of $F$, and restricting the morphisms
to those that lie in the image of $F$.

[essential image]: Cat.Functor.Properties.html#essential-fibres

```agda
  Faithful-subcat : Subcat D (o ⊔ ℓ') (ℓ ⊔ ℓ')
  Faithful-subcat .Subcat.is-ob x = Essential-fibre F x
  Faithful-subcat .Subcat.is-hom f (y , y-es) (z , z-es) =
    Σ[ g ∈ C.Hom y z ] (D.to z-es D.∘ F₁ g D.∘ D.from y-es ≡ f)
  Faithful-subcat .Subcat.is-hom-prop f (y , y-es) (z , z-es) (g , p) (h , q) =
    Σ-prop-path! $
    faithful $
    D.iso→epic (y-es D.Iso⁻¹) _ _ $
    D.iso→monic z-es _ _ $
    p ∙ sym q
  Faithful-subcat .Subcat.is-hom-id (y , y-es) =
    C.id , ap₂ D._∘_ refl (D.eliml F-id) ∙ D.invl y-es
  Faithful-subcat .Subcat.is-hom-∘
    {f = f} {g = g} {x , x-es} {y , y-es} {z , z-es} (h , p) (i , q) =
    (h C.∘ i) ,
    D.push-inner (F-∘ h i)
    ·· D.insert-inner (D.invr y-es)
    ·· ap₂ D._∘_ (sym (D.assoc _ _ _) ∙ p) q
```

There is an equivalence between canonical subcategory associated
with $F$ and $C$.

```agda
  Faithful-subcat-domain : Functor (Subcategory Faithful-subcat) C
  Faithful-subcat-domain .Functor.F₀ (x , x-es) = x-es .fst
  Faithful-subcat-domain .Functor.F₁ f = f .witness .fst
  Faithful-subcat-domain .Functor.F-id = refl
  Faithful-subcat-domain .Functor.F-∘ _ _ = refl

  Faithful-subcat-domain-is-ff : is-fully-faithful Faithful-subcat-domain
  Faithful-subcat-domain-is-ff {x = x , x' , x-es} {y = y , y' , y-es} =
    is-iso→is-equiv $ iso
    (λ f → sub-hom (D.to y-es D.∘ F₁ f D.∘ D.from x-es) (f , refl))
    (λ _ → refl)
    (λ f → ext (f .witness .snd))

  Faithful-subcat-domain-is-split-eso : is-split-eso Faithful-subcat-domain
  Faithful-subcat-domain-is-split-eso x =
    (F₀ x , x , D.id-iso) , C.id-iso
```

There is a faithful functor from a subcategory on $\cC$ to $\cC$.

<!--
```agda
module _ {o o' ℓ ℓ'} {C : Precategory o ℓ} {S : Subcat C o' ℓ'} where
  open Cat.Reasoning C
  private module Sub = Cat.Reasoning (Subcategory S)
  open Subcat S
```
-->

```agda
  Forget-subcat : Functor (Subcategory S) C
  Forget-subcat .Functor.F₀ (x , _) = x
  Forget-subcat .Functor.F₁ f = f .hom
  Forget-subcat .Functor.F-id = refl
  Forget-subcat .Functor.F-∘ _ _ = refl

  is-faithful-Forget-subcat : is-faithful Forget-subcat
  is-faithful-Forget-subcat = ext
```

Furthermore, if the subcategory contains all of the isomorphisms of $\cC$, then
the forgetful functor is pseudomonic.

```agda
  is-pseudomonic-Forget-subcat
    : (∀ {x y} {f : Hom x y} {px : x ∈ S} {py : y ∈ S}
       → is-invertible f → S .is-hom f px py)
    → is-pseudomonic Forget-subcat
  is-pseudomonic-Forget-subcat invert .is-pseudomonic.faithful =
    is-faithful-Forget-subcat
  is-pseudomonic-Forget-subcat invert .is-pseudomonic.isos-full f =
    pure $ Sub.make-iso
      (sub-hom (f .to)   (invert (iso→invertible f)))
      (sub-hom (f .from) (invert (iso→invertible (f Iso⁻¹))))
      (ext (f .invl))
      (ext (f .invr)) , trivial!
```

## Univalent subcategories

Let $\cC$ be a [univalent] category. A subcategory of $\cC$ is univalent
when the predicate on objects is a proposition.

[univalent]: Cat.Univalent.html

```agda
  subcat-iso→iso : ∀ {x y : Σ[ x ∈ Ob ] (x ∈ S)} → x Sub.≅ y → x .fst ≅ y .fst
  subcat-iso→iso f = make-iso (Sub.to f .hom) (Sub.from f .hom)
    (ap hom (Sub.invl f)) (ap hom (Sub.invr f))

  subcat-is-category
    : is-category C
    → (∀ x → is-prop (x ∈ S))
    → is-category (Subcategory S)
  subcat-is-category cat ob-prop .to-path {a , pa} {b , pb} f =
    Σ-prop-path ob-prop (cat .to-path (subcat-iso→iso f))
  subcat-is-category cat ob-prop .to-path-over p =
    Sub.≅-pathp refl _ $
    Subcat-hom-pathp refl _ $
    apd (λ _ → to) (cat .to-path-over (subcat-iso→iso p))
```
