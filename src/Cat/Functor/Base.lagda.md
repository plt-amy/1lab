<!--
```agda
open import 1Lab.Path.Cartesian

open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Functor.Base where
```

# Functor precategories {defines="functor-category"}

Fix a pair of (completely arbitrary!) precategories $\cC$ and $\cD$.
We'll show how to make the type of functors $\cC \to \cD$ into a
precategory on its own right, with the _natural transformations_ $F \To
G$ as the morphisms. First, given $F : \cC \to \cD$, we construct the
identity natural transformation by having every component be the
identity:

<!--
```agda
private variable
  o o₁ o₂ ℓ ℓ₁ ℓ₂ : Level
  B C D E : Precategory o ℓ
  F G : Functor C D

private module Pc = Precategory
open Functor
open _=>_

module _ {C : Precategory o ℓ} {D : Precategory o₁ ℓ₁} where
  private
    module C = Cat.Reasoning C
    module D = Cat.Reasoning D
```
-->

```agda
  idnt : {F : Functor C D} → F => F
  idnt .η _              = D.id
  idnt .is-natural _ _ _ = D.id-comm-sym
```

Moreover, if we have a pair of composable-looking natural
transformations $\alpha : G \To H$ and $\beta : F \To G$, then we can
indeed make their pointwise composite into a natural transformation:

```agda
  _∘nt_ : ∀ {F G H : Functor C D} → G => H → F => G → F => H
  (f ∘nt g) .η x = f .η x D.∘ g .η x
  _∘nt_ {F} {G} {H} f g .is-natural x y h =
    (f .η y D.∘ g .η y) D.∘ F .F₁ h ≡⟨ D.pullr (g .is-natural x y h) ⟩
    f .η y D.∘ G .F₁ h D.∘ g .η x   ≡⟨ D.extendl (f .is-natural x y h) ⟩
    H .F₁ h D.∘ f .η x D.∘ g .η x   ∎

  infixr 40 _∘nt_
```

Since we already know that identity of natural transformations is
determined by identity of the underlying family of morphisms, and the
identities and composition we've just defined are _componentwise_ just
identity and composition in $\cD$, then the category laws we have to
prove are, once again, those of $\cD$:

```agda
Cat[_,_]
  : Precategory o ℓ → Precategory o₁ ℓ₁
  → Precategory (o ⊔ ℓ ⊔ o₁ ⊔ ℓ₁) (o ⊔ ℓ ⊔ ℓ₁)
Cat[ C , D ] .Pc.Ob          = Functor C D
Cat[ C , D ] .Pc.Hom         = _=>_
Cat[ C , D ] .Pc.Hom-set F G = Nat-is-set

Cat[ C , D ] .Pc.id  = idnt
Cat[ C , D ] .Pc._∘_ = _∘nt_

Cat[ C , D ] .Pc.idr f       = ext λ x → D .Pc.idr _
Cat[ C , D ] .Pc.idl f       = ext λ x → D .Pc.idl _
Cat[ C , D ] .Pc.assoc f g h = ext λ x → D .Pc.assoc _ _ _
```

We'll also need the following foundational tool, characterising paths
between functors. It says that, given a homotopy $p_0$ between the
object-parts of functors $F, G : \cC \to \cD$, and, over this, an
identification between the actions of $F$ and $G$ on morphisms, we can
construct a path $F \equiv G$.

## Paths between functors

```agda
Functor-path
  : {F G : Functor C D}
  → (p0 : ∀ x → F .F₀ x ≡ G .F₀ x)
  → (p1 : ∀ {x y} (f : C .Pc.Hom x y)
        → PathP (λ i → D .Pc.Hom (p0 x i) (p0 y i)) (F .F₁ f) (G .F₁ f))
  → F ≡ G
```

Note that this lemma is a bit unusual: we're characterising the identity
type of the _objects_ of a precategory, rather than, as is more common,
the _morphisms_ of a precategory. However, this characterisation will
let us swiftly establish necessary conditions for [univalence of functor
categories].

[univalence of functor categories]: Cat.Functor.Univalence.html

<!--
```agda
Functor-pathp
  : {C : I → Precategory o ℓ} {D : I → Precategory o₁ ℓ₁}
    {F : Functor (C i0) (D i0)} {G : Functor (C i1) (D i1)}
  → (p0 : ∀ (p : ∀ i → C i .Pc.Ob) → PathP (λ i → D i .Pc.Ob) (F .F₀ (p i0)) (G .F₀ (p i1)))
  → (p1 : ∀ {x y : ∀ i → _}
        → (r : ∀ i → C i .Pc.Hom (x i) (y i))
        → PathP (λ i → D i .Pc.Hom (p0 x i) (p0 y i))
                (F .F₁ (r i0)) (G .F₁ (r i1)))
  → PathP (λ i → Functor (C i) (D i)) F G
Functor-pathp {C = C} {D} {F} {G} p0 p1 = fn where
  open Pc
  cob : I → Type _
  cob = λ i → C i .Ob

  exth
    : ∀ i j (x y : C i .Ob) (f : C i .Hom x y)
    → C i .Hom (coe cob i i x) (coe cob i i y)
  exth i j x y f =
    comp (λ j → C i .Hom (coei→i cob i x (~ j ∨ i)) (coei→i cob i y (~ j ∨ i)))
    ((~ i ∧ ~ j) ∨ (i ∧ j))
    λ where
      k (k = i0) → f
      k (i = i0) (j = i0) → f
      k (i = i1) (j = i1) → f

  actm
    : ∀ i (x y : C i .Ob) f
    → D i .Hom (p0 (λ j → coe cob i j x) i) (p0 (λ j → coe cob i j y) i)
  actm i x y f =
    p1 {λ j → coe cob i j x} {λ j → coe cob i j y}
      (λ j → coe (λ j → C j .Hom (coe cob i j x) (coe cob i j y)) i j (exth i j x y f))
      i

  fn : PathP (λ i → Functor (C i) (D i)) F G
  fn i .F₀ x =
    p0 (λ j → coe cob i j x)
      i
  fn i .F₁ {x} {y} f = actm i x y f
  fn i .F-id {x} =
    hcomp (∂ i) λ where
      j (i = i0) → D i .Hom-set (F .F₀ x) (F .F₀ x) (F .F₁ (C i .id)) (D i .id) base (F .F-id) j
      j (i = i1) → D i .Hom-set (G .F₀ x) (G .F₀ x) (G .F₁ (C i .id)) (D i .id) base (G .F-id) j
      j (j = i0) → base
    where
      base = coe0→i (λ i → (x : C i .Ob) → actm i x x (C i .id) ≡ D i .id) i
        (λ _ → F .F-id) x
  fn i .F-∘ {x} {y} {z} f g =
    hcomp (∂ i) λ where
      j (i = i0) → D i .Hom-set (F .F₀ x) (F .F₀ z) _ _ base (F .F-∘ f g) j
      j (i = i1) → D i .Hom-set (G .F₀ x) (G .F₀ z) _ _ base (G .F-∘ f g) j
      j (j = i0) → base
    where
      base = coe0→i (λ i → (x y z : C i .Ob) (f : C i .Hom y z) (g : C i .Hom x y)
                         → actm i x z (C i ._∘_ f g)
                         ≡ D i ._∘_ (actm i y z f) (actm i x y g)) i
        (λ _ _ _ → F .F-∘) x y z f g

Functor-path p0 p1 i .F₀ x = p0 x i
Functor-path p0 p1 i .F₁ f = p1 f i
Functor-path {C = C} {D = D} {F = F} {G = G} p0 p1 i .F-id =
  is-prop→pathp (λ j → D .Pc.Hom-set _ _ (p1 (C .Pc.id) j) (D .Pc.id))
    (F .F-id) (G .F-id) i
Functor-path {C = C} {D = D} {F = F} {G = G} p0 p1 i .F-∘ f g =
  is-prop→pathp (λ i → D .Pc.Hom-set _ _ (p1 (C .Pc._∘_ f g) i) (D .Pc._∘_ (p1 f i) (p1 g i)))
    (F .F-∘ f g) (G .F-∘ f g) i
```
-->

## Action on isomorphisms

<!--
```agda
module F-iso {C : Precategory o ℓ} {D : Precategory o₁ ℓ₁} (F : Functor C D) where
  private module _ where
    module C = Cat.Reasoning C
    module D = Cat.Reasoning D
    open Cat.Reasoning using (_≅_ ; Inverses)
    open _≅_ public
    open Inverses public
```
-->

We have also to make note of the following fact: absolutely all functors
preserve isomorphisms, and, more generally, preserve invertibility.

```agda
  F-map-iso : ∀ {x y} → x C.≅ y → F # x D.≅ F # y
  F-map-iso x .to       = F .F₁ (x .to)
  F-map-iso x .from     = F .F₁ (x .from)
  F-map-iso x .inverses =
    record { invl = sym (F .F-∘ _ _) ∙ ap (F .F₁) (x .invl) ∙ F .F-id
           ; invr = sym (F .F-∘ _ _) ∙ ap (F .F₁) (x .invr) ∙ F .F-id
           }
    where module x = C._≅_ x

  F-map-invertible : ∀ {x y} {f : C.Hom x y} → C.is-invertible f → D.is-invertible (F .F₁ f)
  F-map-invertible inv =
    D.make-invertible (F .F₁ _)
      (sym (F .F-∘ _ _) ·· ap (F .F₁) x.invl ·· F .F-id)
      (sym (F .F-∘ _ _) ·· ap (F .F₁) x.invr ·· F .F-id)
    where module x = C.is-invertible inv
```

If the categories the functor maps between are univalent, there is a
competing notion of preserving isomorphisms: the action on paths of the
object-part of the functor. We first turn the isomorphism into a path
(using univalence of the domain), run it through the functor, then turn
the resulting path back into an isomorphism. Fortunately, functors are
already coherent enough to ensure that these actions agree:

```agda
  F-map-path
    : (ccat : is-category C) (dcat : is-category D)
    → ∀ {x y} (i : x C.≅ y)
    → ap# F (Univalent.iso→path ccat i) ≡ Univalent.iso→path dcat (F-map-iso i)
  F-map-path ccat dcat {x} = Univalent.J-iso ccat P pr where
    P : (b : C.Ob) → C.Isomorphism x b → Type _
    P b im = ap# F (Univalent.iso→path ccat im)
           ≡ Univalent.iso→path dcat (F-map-iso im)

    pr : P x C.id-iso
    pr =
      ap# F (Univalent.iso→path ccat C.id-iso) ≡⟨ ap (ap# F) (Univalent.iso→path-id ccat) ⟩
      ap# F refl                               ≡˘⟨ Univalent.iso→path-id dcat ⟩
      dcat .to-path D.id-iso                   ≡⟨ ap (dcat .to-path) (ext (sym (F .F-id))) ⟩
      dcat .to-path (F-map-iso C.id-iso)     ∎
```

<!--
```agda
  ap-F₀-to-iso
    : ∀ {y z}
    → (p : y ≡ z) → path→iso (ap# F p) ≡ F-map-iso (path→iso p)
  ap-F₀-to-iso {y} =
    J (λ _ p → path→iso (ap# F p) ≡ F-map-iso (path→iso p))
      (D.≅-pathp (λ _ → F .F₀ y) (λ _ → F .F₀ y)
        (Regularity.fast! (sym (F .F-id))))

  ap-F₀-iso
    : ∀ (cc : is-category C) {y z : C.Ob}
    → (p : y C.≅ z) → path→iso (ap# F (cc .to-path p)) ≡ F-map-iso p
  ap-F₀-iso cc p = ap-F₀-to-iso (cc .to-path p)
                 ∙ ap F-map-iso (Univalent.iso→path→iso cc p)

open F-iso public
```
-->

# Presheaf precategories

Of principal importance among the functor categories are those to the
category $\Sets$: these are the _presheaf categories_.

```agda
PSh : ∀ κ {o ℓ} → Precategory o ℓ → Precategory _ _
PSh κ C = Cat[ C ^op , Sets κ ]
```
