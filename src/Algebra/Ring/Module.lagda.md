<!--
```agda
open import Algebra.Group.Notation
open import Algebra.Group.Ab
open import Algebra.Group
open import Algebra.Ring

open import Cat.Displayed.Univalence.Thin
open import Cat.Prelude hiding (_+_)

import Cat.Reasoning
```
-->

```agda
module Algebra.Ring.Module where
```

<!--
```agda
private variable
  ℓm ℓn : Level
  S T : Type ℓm

private module Mod {ℓ} (R : Ring ℓ) where
  private module R = Ring-on (R .snd)
  open Displayed
  open Total-hom
  open Functor
```
-->

# Modules {defines="module"}

A **module** over a [[ring]] $R$ is an [[abelian group]] $G$ equipped
with an [action by $R$]. Modules generalise the idea of vector spaces,
which may be familiar from linear algebra, by replacing the field of
scalars by a _ring_ of scalars. More pertinently, though, modules
_specialise_ [functors]: specifically, $\Ab$-enriched functors into the
category $\Ab$.

[functors]: Cat.Abelian.Instances.Functor.html
[action by $R$]: Algebra.Ring.Module.Action.html

For silly formalisation reasons, when defining modules, we do not take
"an $\Ab$-functor into $\Ab$" as the definition: this correspondence is
a theorem we prove later. Instead, we set up $R$-modules as typical
algebraic structures, as data (and property) attached to a type.

The structure of an $R$-module on a type $T$ consists of an _addition_
$+ : T \times T \to T$ and a _scalar multiplication_ $\star : R \times T
\to T$. In prose, we generally omit the star, writing $rx$ rather than
the wordlier $r \star x$. These must satisfy the following properties:

- $+$ makes $T$ into an [abelian group]. Since we've already defined
abelian groups, we can take this entire property as "indivisible",
saving some effort.

- $·$ is a ring homomorphism of $R$ onto $(T, +)$'s endomorphism ring. In
other words, we have:

  * $1x = x$;
  * $(rs) \cdot x = r \cdot (s \cdot x)$;
  * $(r + s)x = rx + sx$; and
  * $r(x + y) = rx + ry$.

[abelian group]: Algebra.Group.Ab.html

```agda
  record is-module {ℓ'} {T : Type ℓ'} (_+_ : T → T → T) (_⋆_ : ⌞ R ⌟ → T → T) : Type (ℓ ⊔ ℓ') where
    no-eta-equality
    field
      has-is-ab  : is-abelian-group _+_
      ⋆-distribl : ∀ r x y → r ⋆ (x + y)   ≡ (r ⋆ x) + (r ⋆ y)
      ⋆-distribr : ∀ r s x → (r R.+ s) ⋆ x ≡ (r ⋆ x) + (s ⋆ x)
      ⋆-assoc    : ∀ r s x → r ⋆ (s ⋆ x)   ≡ (r R.* s) ⋆ x
      ⋆-id       : ∀ x     → R.1r ⋆ x      ≡ x
```

<!--
```agda
    private
      ug : Group-on _
      ug = record { has-is-group = is-abelian-group.has-is-group has-is-ab }

    module ab = Additive-notation ug
    private module ab' = is-abelian-group has-is-ab renaming (commutes to +-comm)

    open ab using (-_ ; 0g ; +-invr ; +-invl ; +-assoc ; +-idl ; +-idr ; neg-0 ; neg-comm ; neg-neg ; has-is-set) public
    open ab' using (+-comm) public

    abstract
      ⋆-is-group-hom : ∀ {r} → is-group-hom ug ug (r ⋆_)
      ⋆-is-group-hom .is-group-hom.pres-⋆ x y = ⋆-distribl _ x y

    private module ⋆gh {r} = is-group-hom (⋆-is-group-hom {r}) renaming (pres-id to ⋆-idr ; pres-inv to ⋆-invr)
    open ⋆gh public using (⋆-idr ; ⋆-invr)

  private unquoteDecl eqv = declare-record-iso eqv (quote is-module)
```
-->

Correspondingly, a module structure on a type packages the addition, the
scalar multiplication, and the proofs that these behave as we set above.
A module is a type equipped with a module structure.

```agda
  record Module-on {ℓ'} (T : Type ℓ') : Type (ℓ ⊔ ℓ') where
    no-eta-equality
    field
      _+_        : T → T → T
      _⋆_        : ⌞ R ⌟ → T → T
      has-is-mod : is-module _+_ _⋆_

    infixl 25 _+_
    infixr 27 _⋆_

    open is-module has-is-mod public
```

<!--
```agda
  Module-on→Group-on
    : ∀ {ℓm} {T : Type ℓm}
    → Module-on T
    → Group-on T
  Module-on→Group-on M = record { has-is-group = is-abelian-group.has-is-group (Module-on.has-is-ab M) }

  Module-on→Abelian-group-on
    : ∀ {ℓm} {T : Type ℓm}
    → Module-on T
    → Abelian-group-on T
  Module-on→Abelian-group-on M = record { has-is-ab = Module-on.has-is-ab M }

  abstract instance
    H-Level-is-module
      : ∀ {ℓ'} {T : Type ℓ'} {_+_ : T → T → T} {_⋆_ : ⌞ R ⌟ → T → T} {n}
      → H-Level (is-module _+_ _⋆_) (suc n)
    H-Level-is-module {T = T} = prop-instance $ λ x →
      let
        instance
          _ : H-Level T 2
          _ = basic-instance 2 (is-module.has-is-set x)
      in Iso→is-hlevel 1 eqv (hlevel 1) x

  open Module-on ⦃ ... ⦄ hiding (has-is-set)
```
-->

```agda
  Module : ∀ ℓm → Type (lsuc ℓm ⊔ ℓ)
  Module ℓm = Σ (Set ℓm) λ X → Module-on ∣ X ∣

  record is-linear-map (f : S → T) (M : Module-on S) (N : Module-on T)
    : Type (ℓ ⊔ level-of S ⊔ level-of T) where
```

## Linear maps

The correct notion of morphism between $R$-modules is the _linear map_;
in case we need to make the base ring $R$ clear, we shall call them
$R$-linear maps. Since the structure of $R$-modules are their additions
and their scalar multiplications, it stands to reason that these are
what homomorphisms should preserve. Rather than separately asking for
preservation of addition and of multiplication, the following single
assumption suffices:

<!--
```agda
    no-eta-equality
    private instance
      _ = M
      _ = N
```
-->

```agda
    field linear : ∀ r s t → f (r ⋆ s + t) ≡ r ⋆ f s + f t
```

Any map which satisfies this equation must preserve addition, since we
have

$$
f(a+b) = f(1a+b) = 1f(a)+f(b) = f(a)+f(b)
$$.

and standard lemmas about [group homomorphisms] ensure that $f$ will
also preserve negation, and, more importantly, zero. We can then derive
that $f$ preserves the scalar multiplication, by calculating

[group homomorphisms]: Algebra.Group.html#group-homomorphisms

$$
f(ra) = f(ra + 0) = rf(a) + f(0) = rf(a) + 0 = rf(a)
$$.

<!--
```agda
    abstract
      has-is-gh : is-group-hom (Module-on→Group-on M) (Module-on→Group-on N) f
      has-is-gh .is-group-hom.pres-⋆ x y = ap f (ap₂ _+_ (sym (⋆-id _)) refl) ∙ linear _ _ _ ∙ ap₂ _+_ (⋆-id _) refl

    open is-group-hom has-is-gh
      renaming ( pres-⋆ to pres-+ ; pres-id to pres-0 ; pres-inv to pres-neg)
      public

    abstract
      pres-⋆ : ∀ r s → f (r ⋆ s) ≡ r ⋆ f s
      pres-⋆ r s = ap f (sym +-idr) ∙ linear _ _ _ ∙ ap (r ⋆ f s +_) pres-0 ∙ +-idr

  private unquoteDecl eqv' = declare-record-iso eqv' (quote is-linear-map)
  open is-linear-map using (linear) public

  -- There are too many possible instances in scope for instance search
  -- to solve this one, but fortunately it's pretty short:

  abstract
    is-linear-map-is-prop
      : ∀ {M : Module-on T} {N : Module-on S} {f : T → S}
      → is-prop (is-linear-map f M N)
    is-linear-map-is-prop {S = S} {N = N} =
      Iso→is-hlevel 1 eqv' $
      Π-is-hlevel³ 1 λ _ _ _ →
      Module-on.ab.has-is-set N _ _

    instance
      H-Level-is-linear-map
        : ∀ {M : Module-on T} {N : Module-on S} {f : T → S} {n}
        → H-Level (is-linear-map f M N) (suc n)
      H-Level-is-linear-map = prop-instance is-linear-map-is-prop
```
-->

```agda
  record Linear-map (M : Module ℓm) (N : Module ℓn) : Type (ℓ ⊔ ℓm ⊔ ℓn) where
    no-eta-equality
    field
      map : ⌞ M ⌟ → ⌞ N ⌟
      lin : is-linear-map map (M .snd) (N .snd)
    open is-linear-map lin public
```

The collection of linear maps forms a set, whose identity type is given
by pointwise identity of the underlying maps. Therefore, we may take
these to be the morphisms of a category $\Mod[R]$. $\Mod[R]$ is a very
standard category, so very standard constructions can set up the
category, the functor witnessing its concreteness, and a proof that it
is univalent.

<!--
```agda
  private unquoteDecl eqv'' = declare-record-iso eqv'' (quote Linear-map)
  abstract
    Linear-map-is-set
      : ∀ {ℓ' ℓ''} {M : Module ℓ'} {N : Module ℓ''}
      → is-set (Linear-map M N)
    Linear-map-is-set {N = N} =
      Iso→is-hlevel 2 eqv'' $
        Σ-is-hlevel 2 (fun-is-hlevel 2 (N .fst .is-tr)) λ x → is-prop→is-set (hlevel 1)

    instance
      H-Level-Linear-map
        : ∀ {ℓ' ℓ''} {M : Module ℓ'} {N : Module ℓ''} {n}
        → H-Level (Linear-map M N) (suc (suc n))
      H-Level-Linear-map {N = N} {n = n} = basic-instance (suc (suc zero)) Linear-map-is-set

  open Linear-map public

  Linear-map-path
    : ∀ {M : Module ℓm} {N : Module ℓn} {f g : Linear-map M N}
    → (∀ x → f .map x ≡ g .map x)
    → f ≡ g
  Linear-map-path p i .map x = p x i
  Linear-map-path {M = M} {N} {f} {g} p i .lin =
    is-prop→pathp (λ i → hlevel {T = is-linear-map (λ x → p x i) (M .snd) (N .snd)} 1)
      (f .lin) (g .lin) i
```
-->

```agda
  R-Mod-structure : ∀ {ℓ} → Thin-structure _ Module-on
  R-Mod-structure {ℓ} = rms where
    rms : Thin-structure _ Module-on
    ∣ rms .is-hom f M N ∣    = is-linear-map {ℓ} {_} {ℓ} f M N
    rms .is-hom f M N .is-tr = is-linear-map-is-prop

    rms .id-is-hom        .linear r s t = refl
    rms .∘-is-hom f g α β .linear r s t =
      ap f (β .linear r s t) ∙ α .linear _ _ _

    rms .id-hom-unique {s = s} {t = t} α _ = r where
      module s = Module-on s
      module t = Module-on t

      r : s ≡ t
      r i .Module-on._+_ x y = is-linear-map.pres-+ α x y i
      r i .Module-on._⋆_ x y = is-linear-map.pres-⋆ α x y i
      r i .Module-on.has-is-mod =
        is-prop→pathp (λ i → hlevel {T = is-module
          (λ x y → is-linear-map.pres-+ α x y i)
          (λ x y → is-linear-map.pres-⋆ α x y i)} 1)
          (Module-on.has-is-mod s) (Module-on.has-is-mod t) i
```

<!--
```agda
  R-Mod : ∀ ℓm → Precategory (lsuc ℓm ⊔ ℓ) (ℓm ⊔ ℓ)
  R-Mod ℓm = Structured-objects (R-Mod-structure {ℓm})

  Forget-module : ∀ ℓm → Functor (R-Mod ℓm) (Sets ℓm)
  Forget-module _ = Forget-structure R-Mod-structure

  record make-module {ℓm} (M : Type ℓm) : Type (ℓm ⊔ ℓ) where
    field
      has-is-set : is-set M
      _+_ : M → M → M
      inv : M → M
      0g  : M

      +-assoc : ∀ x y z → x + (y + z) ≡ (x + y) + z
      +-invl  : ∀ x → inv x + x ≡ 0g
      +-idl   : ∀ x → 0g + x ≡ x
      +-comm  : ∀ x y → x + y ≡ y + x

      _⋆_ : ⌞ R ⌟ → M → M

      ⋆-distribl : ∀ r x y → r ⋆ (x + y)   ≡ (r ⋆ x) + (r ⋆ y)
      ⋆-distribr : ∀ r s x → (r R.+ s) ⋆ x ≡ (r ⋆ x) + (s ⋆ x)
      ⋆-assoc    : ∀ r s x → r ⋆ (s ⋆ x)   ≡ ((r R.* s) ⋆ x)
      ⋆-id       : ∀ x     → R.1r ⋆ x      ≡ x

  to-module-on : ∀ {ℓm} {M : Type ℓm} → make-module M → Module-on M
  to-module-on m .Module-on._+_ = make-module._+_ m
  to-module-on m .Module-on._⋆_ = make-module._⋆_ m
  to-module-on m .Module-on.has-is-mod = mod where
    gr : Group-on _
    gr = to-group-on λ where
      .make-group.group-is-set → make-module.has-is-set m
      .make-group.unit → make-module.0g m
      .make-group.mul → make-module._+_ m
      .make-group.inv → make-module.inv m
      .make-group.assoc → make-module.+-assoc m
      .make-group.invl → make-module.+-invl m
      .make-group.idl → make-module.+-idl m

    mod : is-module _ _
    mod .is-module.has-is-ab .is-abelian-group.has-is-group = gr .Group-on.has-is-group
    mod .is-module.has-is-ab .is-abelian-group.commutes = make-module.+-comm m _ _
    mod .is-module.⋆-distribl = make-module.⋆-distribl m
    mod .is-module.⋆-distribr = make-module.⋆-distribr m
    mod .is-module.⋆-assoc = make-module.⋆-assoc m
    mod .is-module.⋆-id = make-module.⋆-id m

  to-module : ∀ {ℓm} {M : Type ℓm} → make-module M → Module ℓm
  ∣ to-module m .fst ∣ = _
  to-module m .fst .is-tr = make-module.has-is-set m
  to-module m .snd = to-module-on m
```
-->

# "Representable" modules

A prototypical example of $R$-module is.. $R$ itself! A ring has an
underlying abelian group, and the multiplication operation can certainly
be considered a special kind of "scalar multiplication". If we treat $R$
as an [$\Ab$-category] with a single object, this construction
corresponds to the functor $\hom_R(-,\bull)$ --- the "Yoneda embedding"
of $R$'s unique object. Stretching the analogy, we refer to
$R$-as-an-$R$-module as the "representable" $R$-module.

[$\Ab$-category]: Cat.Abelian.Base.html

```agda
  representable-module : Module ℓ
  representable-module .fst = R .fst
  representable-module .snd = to-module-on record
    { has-is-set = R.has-is-set
    ; _+_ = R._+_
    ; inv = R.-_
    ; 0g = R.0r
    ; +-assoc = λ x y z → R.+-associative
    ; +-invl = λ x → R.+-invl
    ; +-idl = λ x → R.+-idl
    ; +-comm = λ x y → R.+-commutes
    ; _⋆_ = R._*_
    ; ⋆-distribl = λ x y z → R.*-distribl
    ; ⋆-distribr = λ x y z → R.*-distribr
    ; ⋆-assoc    = λ x y z → R.*-associative
    ; ⋆-id       = λ x → R.*-idl
    }
```

Another perspective on this construction is that we are regarding $R$ as
the space of "1-dimensional vectors" over itself. Following this line of
reasoning one can define the [module of $n$-dimensional vectors] over $R$.

[module of $n$-dimensional vectors]: Algebra.Ring.Module.Vec.html

<!--
```agda
-- Hide the constructions that take the base ring as an explicit
-- argument:
open Mod
  hiding
    ( Linear-map
    ; Linear-map-path
    ; is-linear-map
    ; to-module
    ; to-module-on
    ; Module-on→Group-on
    ; Module-on→Abelian-group-on
    ; H-Level-is-linear-map
    ; H-Level-is-module
    ; H-Level-Linear-map
    )
  public

-- And open them here where R is implicit instead:
module _ {ℓ} {R : Ring ℓ} where
  open Mod R
    using
      ( Linear-map
      ; Linear-map-path
      ; is-linear-map
      ; to-module
      ; to-module-on
      ; Module-on→Group-on
      ; Module-on→Abelian-group-on
      ; H-Level-is-linear-map
      ; H-Level-is-module
      ; H-Level-Linear-map
      )
    public

  instance
    Extensional-linear-map
      : ∀ {ℓr} {M : Module R ℓm} {N : Module R ℓn}
      → ⦃ ext : Extensional (⌞ M ⌟ → ⌞ N ⌟) ℓr ⦄
      → Extensional (Linear-map M N) ℓr
    Extensional-linear-map ⦃ ext ⦄ = injection→extensional! (λ p → Linear-map-path (happly p)) ext

module R-Mod {ℓ ℓm} {R : Ring ℓ} = Cat.Reasoning (R-Mod R ℓm)

hom→linear-map
  : ∀ {ℓ ℓm} {R : Ring ℓ} {M N : Module R ℓm}
  → R-Mod.Hom M N
  → Linear-map M N
hom→linear-map h .map = h .hom
hom→linear-map h .lin = h .preserves

linear-map→hom
  : ∀ {ℓ ℓm} {R : Ring ℓ} {M N : Module R ℓm}
  → Linear-map M N
  → R-Mod.Hom M N
linear-map→hom h .hom       = h .map
linear-map→hom h .preserves = h .lin

extensional-mod-hom
  : ∀ {ℓ ℓrel} {R : Ring ℓ} {M : Module R ℓm} {N : Module R ℓm}
  → ⦃ ext : Extensional (Linear-map M N) ℓrel ⦄
  → Extensional (R-Mod R _ .Precategory.Hom M N) ℓrel
extensional-mod-hom ⦃ ei ⦄ = injection→extensional! {f = hom→linear-map} (λ p → ext λ e → ap map p $ₚ e) ei

instance Extensional-mod-hom = extensional-mod-hom
{-# OVERLAPS Extensional-mod-hom #-}
```
-->
