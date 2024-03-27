<!--
```agda
open import Algebra.Group.Ab.Hom
open import Algebra.Group.Ab
open import Algebra.Group

open import Cat.Displayed.Univalence.Thin
open import Cat.Functor.Adjoint.Hom
open import Cat.Instances.Product
open import Cat.Displayed.Total
open import Cat.Functor.Adjoint
open import Cat.Prelude

import Cat.Functor.Bifunctor as Bifunctor
```
-->

```agda
module Algebra.Group.Ab.Tensor where
```

# Bilinear maps

<!--
```agda
private variable
  ℓ ℓ' ℓ'' : Level
```
-->

A function $f : F \to G \to H$, where all types involved are equipped
with [[abelian group]] structures, is called **bilinear** when it
satisfies $f(x + y, z) = f(x, z) + f(y, z)$ and $f(x, y + z) = f(x, y) +
f(x, z)$: it is a group homomorphism in each of its arguments.

```agda
record Bilinear (A : Abelian-group ℓ) (B : Abelian-group ℓ') (C : Abelian-group ℓ'') : Type (ℓ ⊔ ℓ' ⊔ ℓ'') where
  private
    module A = Abelian-group-on (A .snd)
    module B = Abelian-group-on (B .snd)
    module C = Abelian-group-on (C .snd)

  field
    map     : ⌞ A ⌟ → ⌞ B ⌟ → ⌞ C ⌟
    pres-*l : ∀ x y z → map (x A.* y) z ≡ map x z C.* map y z
    pres-*r : ∀ x y z → map x (y B.* z) ≡ map x y C.* map x z
```

<!--
```agda
  fixl-is-group-hom : ∀ a →
    is-group-hom B.Abelian→Group-on C.Abelian→Group-on (map a)
  fixl-is-group-hom a .is-group-hom.pres-⋆ x y = pres-*r a x y

  fixr-is-group-hom : ∀ b →
    is-group-hom A.Abelian→Group-on C.Abelian→Group-on (λ a → map a b)
  fixr-is-group-hom b .is-group-hom.pres-⋆ x y = pres-*l x y b

  module fixl {a} = is-group-hom (fixl-is-group-hom a)
  module fixr {a} = is-group-hom (fixr-is-group-hom a)

  open fixl
    renaming ( pres-id   to pres-idr
             ; pres-inv  to pres-invr
             ; pres-diff to pres-diffr
             )
    hiding ( pres-⋆ )
    public
  open fixr
    renaming ( pres-id   to pres-idl
             ; pres-inv  to pres-invl
             ; pres-diff to pres-diffl
             )
    hiding ( pres-⋆ )
    public

module _ {A : Abelian-group ℓ} {B : Abelian-group ℓ'} {C : Abelian-group ℓ''} where
  private
    module A = Abelian-group-on (A .snd)
    module B = Abelian-group-on (B .snd)
    module C = Abelian-group-on (C .snd)

    Bilinear-path
      : {ba bb : Bilinear A B C}
      → (∀ x y → Bilinear.map ba x y ≡ Bilinear.map bb x y)
      → ba ≡ bb
    Bilinear-path {ba = ba} {bb} p = q where
      open Bilinear

      q : ba ≡ bb
      q i .map x y = p x y i
      q i .pres-*l x y z = is-prop→pathp (λ i → C.has-is-set (p (x A.* y) z i) (p x z i C.* p y z i))
        (ba .pres-*l x y z) (bb .pres-*l x y z) i
      q i .pres-*r x y z = is-prop→pathp (λ i → C.has-is-set (p x (y B.* z) i) (p x y i C.* p x z i))
        (ba .pres-*r x y z) (bb .pres-*r x y z) i

  instance
    Extensional-bilinear
      : ∀ {ℓr} ⦃ ef : Extensional (⌞ A ⌟ → ⌞ B ⌟ → ⌞ C ⌟) ℓr ⦄ → Extensional (Bilinear A B C) ℓr
    Extensional-bilinear ⦃ ef ⦄ = injection→extensional! (λ h → Bilinear-path (λ x y → h # x # y)) ef

module _ {ℓ} (A B C : Abelian-group ℓ) where
```
-->

We have already noted that the set of group homomorphisms between a pair
of abelian groups [is an abelian group], under pointwise multiplication.
The type of bilinear maps is equivalent to the type of group
homomorphisms $A \to [B,C]$.

[is an abelian group]: Algebra.Group.Ab.Hom.html

```agda
  curry-bilinear : Bilinear A B C → Ab.Hom A Ab[ B , C ]
  curry-bilinear f .hom a .hom       = f .Bilinear.map a
  curry-bilinear f .hom a .preserves = Bilinear.fixl-is-group-hom f a
  curry-bilinear f .preserves .is-group-hom.pres-⋆ x y = ext λ z →
    f .Bilinear.pres-*l _ _ _

  curry-bilinear-is-equiv : is-equiv curry-bilinear
  curry-bilinear-is-equiv = is-iso→is-equiv morp where
    morp : is-iso curry-bilinear
    morp .is-iso.inv uc .Bilinear.map x y = uc # x # y
    morp .is-iso.inv uc .Bilinear.pres-*l x y z = ap (_# _) (uc .preserves .is-group-hom.pres-⋆ _ _)
    morp .is-iso.inv uc .Bilinear.pres-*r x y z = (uc # _) .preserves .is-group-hom.pres-⋆ _ _
    morp .is-iso.rinv uc = trivial!
    morp .is-iso.linv uc = trivial!
```

## The tensor product {defines="tensor-product-of-abelian-groups"}

Thinking about the currying isomorphism $A \to (B \to C) \simeq (A
\times B) \to C$, we set out to search for an abelian group which lets
us "associate" `Bilinear`{.Agda} in the other direction: Bilinear maps
$A \to B \to C$ are equivalent to group homomorphisms $A \to [B,C]$, but
is there a construction "$P(A, B)$", playing the role of product type,
such that $P(A, B) \to C$ is _also_ the type of bilinear maps $A \to B
\to C$?

<!--
```agda
module _ {ℓ ℓ'} (A : Abelian-group ℓ) (B : Abelian-group ℓ') where
  private
    module A = Abelian-group-on (A .snd)
    module B = Abelian-group-on (B .snd)
```
-->

The answer is yes: rather than $P$, we write this infix as $A \otimes
B$, and refer to it as the **tensor product** of abelian groups. Since
$A \otimes B$ is determined by the maps _out_ of it, we can construct it
directly as a higher inductive type. We add a constructor for every
operation we want, and for the equations these should satisfy: $A
\otimes B$ should be an Abelian group, and it should admit a bilinear
map $A \to B \to A \otimes B$.

```agda
  data Tensor : Type (ℓ ⊔ ℓ') where
    :1       : Tensor
    _:*_     : Tensor → Tensor → Tensor
    :inv     : Tensor → Tensor
    squash   : is-set Tensor
    t-invl   : ∀ {x} → :inv x :* x ≡ :1
    t-idl    : ∀ {x} → :1 :* x ≡ x
    t-assoc  : ∀ {x y z} → x :* (y :* z) ≡ (x :* y) :* z
    t-comm   : ∀ {x y} → x :* y ≡ y :* x

    _,_       : ⌞ A ⌟ → ⌞ B ⌟ → Tensor
    t-pres-*r : ∀ {x y z} → (x , y B.* z) ≡ (x , y) :* (x , z)
    t-pres-*l : ∀ {x y z} → (x A.* y , z) ≡ (x , z) :* (y , z)
```

The first 8 constructors are, by definition, exactly what we need to
make `Tensor`{.Agda} into an abelian group. The latter three are the
bilinear map $A \to B \to A \otimes B$. Since this is an inductive type,
it's the initial object equipped with these data.

```agda
  open make-abelian-group
  make-abelian-tensor : make-abelian-group Tensor
  make-abelian-tensor .ab-is-set   = squash
  make-abelian-tensor .mul         = _:*_
  make-abelian-tensor .inv         = :inv
  make-abelian-tensor .1g          = :1
  make-abelian-tensor .idl x       = t-idl
  make-abelian-tensor .assoc x y z = t-assoc
  make-abelian-tensor .invl x      = t-invl
  make-abelian-tensor .comm x y    = t-comm

  _⊗_ : Abelian-group (ℓ ⊔ ℓ')
  _⊗_ = to-ab make-abelian-tensor

  to-tensor : Bilinear A B _⊗_
  to-tensor .Bilinear.map           = _,_
  to-tensor .Bilinear.pres-*l x y z = t-pres-*l
  to-tensor .Bilinear.pres-*r x y z = t-pres-*r
```

<!--
```agda
  Tensor-elim-prop
    : ∀ {ℓ'} {P : Tensor → Type ℓ'}
    → (∀ x → is-prop (P x))
    → (∀ x y → P (x , y))
    → (∀ {x y} → P x → P y → P (x :* y))
    → (∀ {x} → P x → P (:inv x))
    → P :1
    → ∀ x → P x
  Tensor-elim-prop {P = P} pprop ppair padd pinv pz = go where
    go : ∀ x → P x
    go (x , y) = ppair x y
    go :1 = pz
    go (x :* y) = padd (go x) (go y)
    go (:inv x) = pinv (go x)
    go (squash x y p q i j) = is-prop→squarep (λ i j → pprop (squash x y p q i j))
      (λ i → go x) (λ i → go (p i)) (λ i → go (q i)) (λ i → go y) i j
    go (t-invl {x} i) = is-prop→pathp (λ i → pprop (t-invl i)) (padd (pinv (go x)) (go x)) pz i
    go (t-idl {x} i) = is-prop→pathp (λ i → pprop (t-idl i)) (padd pz (go x)) (go x) i
    go (t-assoc {x} {y} {z} i) =
      is-prop→pathp (λ i → pprop (t-assoc i))
        (padd (go x) (padd (go y) (go z)))
        (padd (padd (go x) (go y)) (go z))
        i
    go (t-comm {x} {y} i) =
      is-prop→pathp (λ i → pprop (t-comm i)) (padd (go x) (go y)) (padd (go y) (go x)) i
    go (t-pres-*r {x} {y} {z} i) = is-prop→pathp (λ i → pprop (t-pres-*r i)) (ppair x (y B.* z)) (padd (ppair x y) (ppair x z)) i
    go (t-pres-*l {x} {y} {z} i) = is-prop→pathp (λ i → pprop (t-pres-*l i)) (ppair (x A.* y) z) (padd (ppair x z) (ppair y z)) i

module _ {ℓ ℓ' ℓ''} (A : Abelian-group ℓ) (B : Abelian-group ℓ') (C : Abelian-group ℓ'') where
  private
    module A = Abelian-group-on (A .snd)
    module B = Abelian-group-on (B .snd)
    module C = Abelian-group-on (C .snd)
```
-->

If we have any bilinear map $A \to B \to C$, we can first extend it to a
function of _sets_ $A \otimes B \to C$ by recursion, then prove that
this is a group homomorphism. It turns out that this extension is
_definitionally_ a group homomorphism.

```agda
  bilinear-map→function : Bilinear A B C → Tensor A B → ⌞ C ⌟
  bilinear-map→function bilin = go module bilinear-map→function where
    go : Tensor A B → ⌞ C ⌟
    go :1       = C.1g
    go (x :* y) = go x C.* go y
    go (:inv x) = go x C.⁻¹
    go (x , y)  = Bilinear.map bilin x y

    go (squash x y p q i j)      = C.has-is-set (go x) (go y) (λ i → go (p i)) (λ i → go (q i)) i j
    go (t-invl {x} i)            = C.inversel {x = go x} i
    go (t-idl {x} i)             = C.idl {x = go x} i
    go (t-assoc {x} {y} {z} i)   = C.associative {x = go x} {go y} {go z} i
    go (t-comm {x} {y} i)        = C.commutes {x = go x} {y = go y} i
    go (t-pres-*r {a} {b} {c} i) = Bilinear.pres-*r bilin a b c i
    go (t-pres-*l {a} {b} {c} i) = Bilinear.pres-*l bilin a b c i

  {-# DISPLAY bilinear-map→function.go b = bilinear-map→function b #-}
```

<!--
```agda
module _ {ℓ} (A B C : Abelian-group ℓ) where
  private
    module A = Abelian-group-on (A .snd)
    module B = Abelian-group-on (B .snd)
    module C = Abelian-group-on (C .snd)

```
-->

```agda
  from-bilinear-map : Bilinear A B C → Ab.Hom (A ⊗ B) C
  from-bilinear-map bilin .hom = bilinear-map→function A B C bilin
  from-bilinear-map bilin .preserves .is-group-hom.pres-⋆ x y = refl
```

It's also easy to construct a function in the opposite direction,
turning group homomorphisms into bilinear maps, but proving that this is
an equivalence requires appealing to an induction principle of
`Tensor`{.Agda} which handles the equational fields:
`Tensor-elim-prop`{.Agda}.

```agda
  to-bilinear-map : Ab.Hom (A ⊗ B) C → Bilinear A B C
  to-bilinear-map gh .Bilinear.map x y = gh # (x , y)
  to-bilinear-map gh .Bilinear.pres-*l x y z =
    ap (apply gh) t-pres-*l ∙ gh .preserves .is-group-hom.pres-⋆ _ _
  to-bilinear-map gh .Bilinear.pres-*r x y z =
    ap (apply gh) t-pres-*r ∙ gh .preserves .is-group-hom.pres-⋆ _ _

  from-bilinear-map-is-equiv : is-equiv from-bilinear-map
  from-bilinear-map-is-equiv = is-iso→is-equiv morp where
    morp : is-iso from-bilinear-map
    morp .is-iso.inv = to-bilinear-map
    morp .is-iso.rinv hom = ext $ Tensor-elim-prop A B (λ x → C.has-is-set _ _)
      (λ x y → refl)
      (λ x y → ap₂ C._*_ x y ∙ sym (hom .preserves .is-group-hom.pres-⋆ _ _))
      (λ x → ap C._⁻¹ x ∙ sym (is-group-hom.pres-inv (hom .preserves)))
      (sym (is-group-hom.pres-id (hom .preserves)))
    morp .is-iso.linv x = trivial!
```

<!--
```agda
  Bilinear≃Hom : Bilinear A B C ≃ Ab.Hom (A ⊗ B) C
  Bilinear≃Hom = from-bilinear-map , from-bilinear-map-is-equiv

  Hom≃Bilinear : Ab.Hom (A ⊗ B) C ≃ Bilinear A B C
  Hom≃Bilinear = Bilinear≃Hom e⁻¹

  module Bilinear≃Hom = Equiv Bilinear≃Hom
  module Hom≃Bilinear = Equiv Hom≃Bilinear

module _ {ℓ} {A B C : Abelian-group ℓ} where instance
  Extensional-tensor-hom
    : ∀ {ℓr} ⦃ ef : Extensional (⌞ A ⌟ → ⌞ B ⌟ → ⌞ C ⌟) ℓr ⦄ → Extensional (Ab.Hom (A ⊗ B) C) ℓr
  Extensional-tensor-hom ⦃ ef ⦄ =
    injection→extensional! {B = ⌞ A ⌟ → ⌞ B ⌟ → ⌞ C ⌟}
      {f = λ f x y → f .hom (x , y)}
      (λ {x} p → Hom≃Bilinear.injective _ _ _ (ext (subst (ef .Pathᵉ _) p (ef .reflᵉ _))))
      auto
  {-# OVERLAPS Extensional-tensor-hom #-}
```
-->

## The tensor-hom adjunction

<!--
```agda
open Functor
```
-->

Since we have a construction $(A \otimes B)$ satisfying $(A \otimes B)
\to C \simeq A \to [B, C]$, we're driven, being category theorists, to
question its naturality: Is the tensor product a functor, and is this
equivalence of Hom-sets an [[adjunction]]?

The answer is yes, and the proofs are essentially plugging together
existing definitions, other than the construction of the functorial
action of $\otimes$.

```agda
Ab-tensor-functor : Functor (Ab ℓ ×ᶜ Ab ℓ) (Ab ℓ)
Ab-tensor-functor .F₀ (A , B) = A ⊗ B
Ab-tensor-functor .F₁ (f , g) = from-bilinear-map _ _ _ bilin where
  bilin : Bilinear _ _ _
  bilin .Bilinear.map x y       = f # x , g # y
  bilin .Bilinear.pres-*l x y z = ap (_, g # z) (f .preserves .is-group-hom.pres-⋆ _ _) ∙ t-pres-*l
  bilin .Bilinear.pres-*r x y z = ap (f # x ,_) (g .preserves .is-group-hom.pres-⋆ _ _) ∙ t-pres-*r
Ab-tensor-functor .F-id    = trivial!
Ab-tensor-functor .F-∘ f g = trivial!

Tensor⊣Hom : (A : Abelian-group ℓ) → Bifunctor.Left Ab-tensor-functor A ⊣ Bifunctor.Right Ab-hom-functor A
Tensor⊣Hom A = hom-iso→adjoints to to-eqv nat where
  to : ∀ {x y} → Ab.Hom (x ⊗ A) y → Ab.Hom x Ab[ A , y ]
  to f = curry-bilinear _ _ _ (to-bilinear-map _ _ _ f)

  to-eqv : ∀ {x y} → is-equiv (to {x} {y})
  to-eqv = ∙-is-equiv
    (Hom≃Bilinear _ _ _ .snd)
    (curry-bilinear-is-equiv _ _ _)

  nat : hom-iso-natural {L = Bifunctor.Left Ab-tensor-functor A} {R = Bifunctor.Right Ab-hom-functor A} to
  nat f g h = trivial!
```
