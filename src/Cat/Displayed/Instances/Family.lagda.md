<!--
```agda
open import Cat.Displayed.GenericObject
open import Cat.Displayed.Cartesian
open import Cat.Functor.Equivalence
open import Cat.Functor.Properties
open import Cat.Instances.Discrete
open import Cat.Instances.Functor
open import Cat.Displayed.Fibre
open import Cat.Displayed.Base
open import Cat.Skeletal
open import Cat.Prelude
open import Cat.Strict
open import Cat.Gaunt

import Cat.Reasoning
```
-->

```agda
module Cat.Displayed.Instances.Family {o h} (C : Precategory o h) where
```

<!--
```agda
open Cat.Reasoning C
open Displayed
open Functor
open _=>_
```
-->

# The family fibration

We can canonically treat any `Precategory`{.Agda} $\mathcal{C}$ as being
displayed over `Sets`{.Agda}, regardless of the size of the object- and
Hom-spaces of $\mathcal{C}$.

In a neutral presentation of [[displayed category]] theory, the collection
of objects over $S$ would be given by the space of functors
$[\rm{Disc}(S),C]$, regarding $S$ as a discrete category.  This is
essentially an $S$-indexed family of objects of $C$, hence the name
"family fibration". To reduce the noise, however, in HoTT we can (ab)use
the fact that all precategories have a _space of objects_, and say that
the objects over $S$ are precisely the families $S \to \rm{Ob}_\cC$.

```agda
Family : ∀ {ℓ} → Displayed (Sets ℓ) _ _
Family .Ob[_] S = ∣ S ∣ → Ob
```

The set of maps over a function $f : A \to B$ (in $\Sets$) is the set of
families of morphisms $F(x) \to G(fx)$. Here we are abusing that, for
functors between discrete categories, naturality is automatic.

```agda
Family .Hom[_] {A} {B} f F G =
  ∀ x → Hom (F x) (G (f x))
Family .Hom[_]-set f x y = hlevel 2
```

The identity and composition operations are as for natural
transformations, but without the requirement for naturality.

```agda
Family .id' x = id
Family ._∘'_ {f = f} {g = g} f' g' x = f' (g x) ∘ g' x
Family .idr' _ = funext λ x → idr _
Family .idl' _ = funext λ x → idl _
Family .assoc' _ _ _ = funext λ _ → assoc _ _ _
```

The family fibration is a [[Cartesian fibration]], essentially by solving an
_associativity_ problem. Given a function $f : x \to y$ and a family $Y$
over $y$, we must _define_ a family $X$ over $x$ and give a universal
family of functions $X(a) \to Y(f(a))$. But we may simply take $X(a) :=
Y(f(a))$, and family is constantly the identity map.

```agda
open Cartesian-fibration
open Cartesian-lift
open is-cartesian

Family-is-cartesian : ∀ {ℓ} → Cartesian-fibration (Family {ℓ = ℓ})
Family-is-cartesian = iscart where
  cart : ∀ {x y : Set _} (f : ∣ x ∣ → ∣ y ∣)
           (y' : ∣ y ∣ → Ob)
       → is-cartesian Family f λ _ → id
  cart f y' .universal m nt = nt
  cart f y' .commutes m h' = funext λ _ → idl _
  cart f y' .unique m' p = funext λ _ → introl refl ∙ happly p _

  iscart : Cartesian-fibration Family
  iscart .has-lift f y' .x' z = y' (f z)
  iscart .has-lift f y' .lifting x = id
  iscart .has-lift {x = x} {y} f y' .cartesian = cart {x = x} {y} f y'
```

Morphisms in the family fibration are cartesian if and only if they are
pointwise isomorphisms. Showing the forward direction is a matter of
using the inverse to construct the factorisation, and then applying
the isomorphism equations to show that we've actually constructed
the unique factorisation.

```agda
pointwise-iso→cartesian
  : ∀ {ℓ} {X Y : Set ℓ} {f : ∣ X ∣ → ∣ Y ∣}
  → {P : ∣ X ∣ → Ob} {Q : ∣ Y ∣ → Ob} {fₓ : ∀ x → Hom (P x) (Q (f x))}
  → (∀ x → is-invertible (fₓ x))
  → is-cartesian Family {X} {Y} {P} {Q} f fₓ
pointwise-iso→cartesian {fₓ = fₓ} fₓ-inv = fₓ-cart where
  module fₓ-inv x = is-invertible (fₓ-inv x)

  fₓ-cart : is-cartesian Family _ fₓ
  fₓ-cart .universal m h' x =
    fₓ-inv.inv (m x) ∘ h' x
  fₓ-cart .commutes m h' =
    funext λ x → cancell (fₓ-inv.invl (m x))
  fₓ-cart .unique {m = m} m' p =
    funext λ x → introl (fₓ-inv.invr (m x)) ∙ pullr (happly p x)
```

Showing the backwards direction requires using the usual trick of
factorizing the identity morphism; this is an isomorphism due
to the fact that the factorisation is unique.

```agda
cartesian→pointwise-iso
  : ∀ {ℓ} {X Y : Set ℓ} {f : ∣ X ∣ → ∣ Y ∣}
  → {P : ∣ X ∣ → Ob} {Q : ∣ Y ∣ → Ob} {fₓ : ∀ x → Hom (P x) (Q (f x))}
  → is-cartesian Family {X} {Y} {P} {Q} f fₓ
  → (∀ x → is-invertible (fₓ x))
cartesian→pointwise-iso {X = X} {f = f} {P = P} {Q = Q} {fₓ = fₓ} fₓ-cart x =
  make-invertible
    fₓ⁻¹
    (happly (fₓ-cart.commutes _ _) x)
    (happly (fₓ-cart.unique {u = X} (λ _ → fₓ⁻¹ ∘ fₓ x) (funext λ _ → cancell (happly (fₓ-cart.commutes _ _) x))) x ∙
     sym (happly (fₓ-cart.unique (λ _ → id) (funext λ _ → idr _)) x))
  where
    module fₓ-cart = is-cartesian fₓ-cart

    fₓ⁻¹ : Hom (Q (f x)) (P x)
    fₓ⁻¹ = fₓ-cart.universal {u = X} (λ x → x) (λ _ → id) x
```

## Fibres

We now prove that the [fibres](Cat.Displayed.Fibre.html) of the family
fibration are indeed the expected functor categories. This involves a
bit of annoying calculation, but it will let us automatically prove that
the family fibration is fibrewise univalent whenever $\cC$ is.

```agda
module _ {ℓ} (X : Set ℓ) where
  private
    lift-f = Disc-adjunct {C = C} {X = ⌞ X ⌟}
    module F = Cat.Reasoning (Fibre Family X)

  Families→functors : Functor (Fibre Family X) Cat[ Disc! X , C ]
  Families→functors .F₀ = Disc-adjunct
  Families→functors .F₁ f .η = f
  Families→functors .F₁ {X} {Y} f .is-natural x y =
    J (λ y p → f y ∘ lift-f X .F₁ p ≡ lift-f Y .F₁ p ∘ f x)
      (ap (f x ∘_) (lift-f X .F-id) ·· id-comm ·· ap (_∘ f x) (sym (lift-f Y .F-id)))
  Families→functors .F-id = Nat-path λ x → refl
  Families→functors .F-∘ f g =
    ap (Families→functors .F₁) (transport-refl _) ∙ Nat-path λ x → refl

  Families→functors-is-ff : is-fully-faithful Families→functors
  Families→functors-is-ff = is-iso→is-equiv
    (iso η (λ x → Nat-path λ _ → refl) λ x → refl)

  open is-precat-iso
  Families→functors-is-iso : is-precat-iso Families→functors
  Families→functors-is-iso .has-is-ff = Families→functors-is-ff
  Families→functors-is-iso .has-is-iso =
    is-iso→is-equiv (iso F₀
      (λ x → Functor-path (λ _ → refl)
        (J (λ _ p → lift-f (x .F₀) .F₁ p ≡ x .F₁ p)
           (lift-f (x .F₀) .F-id ∙ sym (x .F-id))))
      (λ x → refl))

  Families-are-categories : is-category C → is-category (Fibre Family X)
  Families-are-categories isc .to-path im = funext λ x →
    isc .to-path $ make-iso (im .F.to x) (im .F.from x)
      (happly (sym (transport-refl (λ y → im .F.to y ∘ im .F.from y)) ∙ im .F.invl) x)
      (happly (sym (transport-refl (λ y → im .F.from y ∘ im .F.to y)) ∙ im .F.invr) x)
  Families-are-categories isc .to-path-over im = F.≅-pathp refl _ $ funextP λ a →
    Hom-pathp-reflr C (elimr refl ∙ ap to (Univalent.iso→path→iso isc _))
```

## Generic objects

The family fibration on $\cC$ has a generic object if and only if $\cC$
is equivalent to a strict, small category. We begin by showing the
forward direction.

```agda
Family-generic-object→Strict-equiv
  : Globally-small (Family {h})
  → Σ[ Strict ∈ Precategory h h ]
    (is-set (Precategory.Ob Strict) × Equivalence Strict C)
Family-generic-object→Strict-equiv small =
  Strict , hlevel! , eqv module Family-generic-object-strict where
  open Globally-small small
```

The main idea of the proof is that we can replace the type of objects
of $\cC$ with the base component of the generic object $U$, which is a
small set. The displayed component of the generic object gives us a
family of objects over $U$, which we use to define morphisms of our
strict category.

```agda
  Strict : Precategory h h
  Strict .Precategory.Ob = ∣ U ∣
  Strict .Precategory.Hom x y = Hom (Gen x) (Gen y)
  Strict .Precategory.Hom-set _ _ = Hom-set _ _
  Strict .Precategory.id = id
  Strict .Precategory._∘_ = _∘_
  Strict .Precategory.idr = idr
  Strict .Precategory.idl = idl
  Strict .Precategory.assoc = assoc
```

We can use the family of objects over $U$ to construct an embedding from
the strict category into $\cC$.

```agda
  To : Functor Strict C
  To .F₀ = Gen
  To .F₁ f = f
  To .F-id = refl
  To .F-∘ _ _ = refl

  To-ff : is-fully-faithful To
  To-ff = id-equiv
```

Moreover, this embedding is [[split essentially surjective]] on objects.
To show this, note that we can construct a map from the objects of
$\cC$ back into $U$ by classifying the constant family $_ \mapsto x$
that lies over the set of endomorphisms of $x$. This yields a map
$\cC(x,x) \to U$, to which we apply the identity morphism.

```agda
  reflect : Ob → ∣ U ∣
  reflect x = classify {x = el! (Hom x x)} (λ _ → x) id
```

Next, we note that we can construct a morphism from any object $x : \cC$
to it's it's reflection in $U$, as seen through the generic object.
Furthermore, this morphism is cartesian, and thus invertible.

```agda
  η* : (x : Ob) → Hom x (Gen (reflect x))
  η* x = classify' (λ _ → x) id

  η*-invertible : ∀ {x} → is-invertible (η* x)
  η*-invertible {x} =
    cartesian→pointwise-iso (classify-cartesian λ _ → x) id
```

This implies that the embedding from our [[strict category]] into $\cC$ is
split eso, and thus an equivalence of categories.

```agda
  To-split-eso : is-split-eso To
  To-split-eso y =
    reflect y , (invertible→iso (η* y) η*-invertible Iso⁻¹)

  eqv : Equivalence Strict C
  eqv .Equivalence.To = To
  eqv .Equivalence.To-equiv =
    ff+split-eso→is-equivalence id-equiv To-split-eso
```

On to the backwards direction! The key insight here is that we can use
the set of objects of the strict category as the base of our generic
object, and the forward direction of the equivalence as the displayed
portion.

```agda
Strict-equiv→Family-generic-object
  : ∀ (Small : Precategory h h)
  → is-strict Small
  → Equivalence Small C
  → Globally-small (Family {h})
Strict-equiv→Family-generic-object Small ob-set eqv = gsmall where
  module Small = Precategory Small
  open Equivalence eqv
  open Globally-small
  open Generic-object

  gsmall : Globally-small Family
  gsmall .U = el Small.Ob ob-set
  gsmall .Gen = To .F₀
```

Classifying objects in the family fibration is just a matter of chasing
the equivalence around.

```agda
  gsmall .has-generic-ob .classify f x = From .F₀ (f x)
  gsmall .has-generic-ob .classify' f x = counit⁻¹ .η (f x)
  gsmall .has-generic-ob .classify-cartesian f .universal m h' x =
    counit .η (f (m x)) ∘ h' x
  gsmall .has-generic-ob .classify-cartesian f .commutes m h' =
    funext λ _ → cancell (is-invertible.invr (counit-iso _))
  gsmall .has-generic-ob .classify-cartesian f .unique {m = m} {h' = h'} m' p =
    funext λ x →
      m' x                                                 ≡⟨ introl (is-invertible.invl (counit-iso _)) ⟩
      (counit .η (f (m x)) ∘ counit⁻¹ .η (f (m x))) ∘ m' x ≡⟨ pullr (p $ₚ x) ⟩
      counit .η (f (m x)) ∘ h' x ∎
```

If $\cC$ is itself strict, then the set of objects of $\cC$ forms a
generic object.

```agda
Strict→Family-generic-object
  : (ob-set : is-strict C)
  → Generic-object (Family {o}) {el Ob ob-set} (λ x → x)
Strict→Family-generic-object ob-set = gobj where
  open Generic-object

  gobj : Generic-object Family (λ x → x)
  gobj .classify f = f
  gobj .classify' _ _ = id
  gobj .classify-cartesian _ .universal _ h' = h'
  gobj .classify-cartesian _ .commutes _ h' = funext λ _ → idl _
  gobj .classify-cartesian _ .unique m' p = funext λ x →
    sym (idl _) ∙ p $ₚ x
```

### Skeletal generic objects

Let $\cC$ be a strict category, and recall that the set of objects of
$\cC$ forms a generic object. This generic object is a [skeletal
generic object] if and only if $\cC$ is a [skeletal precategory].

[skeletal generic object]: Cat.Displayed.GenericObject.html#skeletal-generic-objects
[skeletal precategory]: Cat.Skeletal.html


```agda
Family-skeletal-generic-object→Skeletal
  : (ob-set : is-strict C)
  → is-skeletal-generic-object Family (Strict→Family-generic-object ob-set)
  → is-skeletal C
Family-skeletal-generic-object→Skeletal ob-set skel-gobj = skel where
```

We shall prove the forward direction first. Let $f : a \cong b$ be an
isomorphism. From this, we can construct a pair of set maps
$src, tgt : \top \to C_0$ that pick out the source and target
of the isomorphism. We then construct a pair of [[cartesian morphisms]]
$h_0, h_1 : \{ a \} \to Ob$ that lie over $src$ and $tgt$, resp.

```agda
  src : ∀ {a b} → a ≅ b → Ob
  src {a = a} _ = a

  tgt : ∀ {a b} → a ≅ b → Ob
  tgt {b = b} _ = b

  h₀ : ∀ {a b} → a ≅ b → Hom a a
  h₀ _ = id

  h₁ : ∀ {a b} → a ≅ b → Hom a b
  h₁ f = f .to

  h₀-cartesian
    : ∀ {a b} → (f : a ≅ b)
    → is-cartesian Family {a = el! (Lift _ ⊤)} (λ _ → src f) (λ _ → h₀ f)
  h₀-cartesian f = pointwise-iso→cartesian λ _ → id-invertible

  h₁-cartesian
    : ∀ {a b} → (f : a ≅ b)
    → is-cartesian Family {a = el! (Lift _ ⊤)} (λ _ → tgt f) (λ _ → h₁ f)
  h₁-cartesian f = pointwise-iso→cartesian λ _ → iso→invertible f
```

Since $Ob$ is a skeletal generic object, any 2 cartesian morphisms into
$Ob$ must have the same underlying map. Therefore, $src$ and $tgt$ must
be equal, which in turn implies that $a = b$.

```agda
  skel : is-skeletal C
  skel = path-from-has-iso→is-skeletal C λ f →
    ∥-∥-rec (ob-set _ _)
      (λ f →
        skel-gobj (h₀-cartesian f) $ₚ _
        ∙ sym (skel-gobj (h₁-cartesian f) $ₚ _))
      f
```

The reverse direction is much simpler. Let $X_i$ be a family of objects,
and $f'_i : X_i \to Ob$ be a cartesian map lying above some $u : I \to Ob$.
cartesian map. Recall that every cartesian map in the family fibration
is a pointwise isomorphism. However, $\cC$ is skeletal, so each of these
isomorphisms must be an automorphism, yielding a path between the
classifying map of the generic object and $u$.

```agda
Skeletal→Family-skeletal-generic-object
  : (skel : is-skeletal C)
  → is-skeletal-generic-object Family
      (Strict→Family-generic-object (skeletal→strict C skel))
Skeletal→Family-skeletal-generic-object skel {f' = f'} cart =
  funext λ x →
    skel .to-path $
      inc (invertible→iso (f' x) (cartesian→pointwise-iso cart x) Iso⁻¹)
```

### Gaunt generic objects

Let $\cC$ be a strict category, and again recall that the set of objects
of $\cC$ forms a generic object. This generic object is a [gaunt generic
object] if and only if $\cC$ is a [gaunt precategory].

[gaunt generic object]: Cat.Displayed.GenericObject.html#gaunt-generic-objects
[gaunt precategory]: Cat.Gaunt.html

We begin with the forward direction. Recall that a category is gaunt
if it is skeletal and all automorphisms are trivial. Gaunt generic
objects are always skeletal, which in turn implies that $\cC$ is skeletal.

```agda
Family-gaunt-generic-object→Gaunt
  : (ob-set : is-strict C)
  → is-gaunt-generic-object Family (Strict→Family-generic-object ob-set)
  → is-gaunt C
Family-gaunt-generic-object→Gaunt ob-set gaunt-gobj =
  skeletal+trivial-automorphisms→gaunt skel trivial-automorphism where
  open is-gaunt-generic-object gaunt-gobj

  skel : is-skeletal C
  skel =
    Family-skeletal-generic-object→Skeletal ob-set
      (gaunt-generic-object→skeletal-generic-object Family gaunt-gobj)
```

To see that all automorphisms of $\cC$ are trivial, note that any automorphism
$f : x \cong x$ induces a cartesian morphism $\{ x \} \to Ob$. Furthermore, this
cartesian morphism must be unique, as $Ob$ is a gaunt generic object. However, $id$
also yields a cartesian morphism $\{ x \} \to Ob$, so $f = id$.

```agda
  trivial-automorphism : ∀ {x} → (f : x ≅ x) → f ≡ id-iso
  trivial-automorphism {x} f =
    ≅-pathp refl refl (is-set→cast-pathp (λ x' → Hom x x') ob-set p) where

   f-to-cart : is-cartesian Family {a = el! (Lift _ ⊤)} (λ _ → x) (λ _ → f .to)
   f-to-cart = pointwise-iso→cartesian (λ _ → iso→invertible f)

   p : PathP (λ i → Hom x (classify-unique f-to-cart i _)) (f .to) id
   p i = classify-unique' f-to-cart i _
```

To show the reverse direction, we can appeal to the fact that isomorphisms
form an [[identity system]] to contract down cartesian maps to the identity
morphism.

```agda
Gaunt→Family-gaunt-generic-object
  : (gaunt : is-gaunt C)
  → is-gaunt-generic-object Family
      (Strict→Family-generic-object (is-gaunt.has-strict gaunt))
Gaunt→Family-gaunt-generic-object gaunt = gaunt-gobj where
  open is-gaunt gaunt hiding (from)
  open is-gaunt-generic-object

  Ob-set : Set o
  Ob-set = el Ob has-strict

  gaunt-gobj : is-gaunt-generic-object Family _
  gaunt-gobj .classify-unique cart =
    funext λ x → has-category .to-path $
      invertible→iso _ (cartesian→pointwise-iso cart x) Iso⁻¹
  gaunt-gobj .classify-unique' {x' = x'} {u = u} {f' = f'} cart =
    funextP λ x →
      IdsJ has-category
        (λ b h → PathP (λ i → Hom b (has-category .to-path h i)) (h .from) id)
        (is-set→cast-pathp {p = refl} (λ x' → Hom (u x) x') has-strict refl)
        (invertible→iso _ (cartesian→pointwise-iso cart x) Iso⁻¹)
```
