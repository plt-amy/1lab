<!--
```agda
open import Algebra.Group.Notation
open import Algebra.Ring.Module
open import Algebra.Group.Ab
open import Algebra.Group
open import Algebra.Ring

open import Cat.Displayed.Univalence.Thin
open import Cat.Abelian.Base
open import Cat.Abelian.Endo
open import Cat.Prelude hiding (_+_)
```
-->

```agda
module Algebra.Ring.Module.Action where
```

# Modules as actions

While the record `Module-on`{.Agda} expresses the possible $R$-module
structures on a _type_ $T$, including the scalar multiplication _and_
the addition making $T$ into an [[abelian group]], it's sometimes
fruitful to consider the $R$-module structures on an _abelian group_
$G$, which is then regarded as an indivisible unit.

The difference is in the quantification: the latter perspective,
developed in this module, allows us to "fix" the addition, and let only
the scalar multiplication vary. The ordinary definition of $R$-module,
which is consistent with our other algebraic structures, only allows us
to vary the underlying type (and the base ring).

<!--
```agda
module _ {ℓ} (R : Ring ℓ) where
  private module R = Ring-on (R .snd)
  open Additive-notation ⦃ ... ⦄
```
-->

```agda
  record Ring-action {ℓg} {T : Type ℓg} (G : Abelian-group-on T) : Type (ℓ ⊔ ℓg) where
    instance _ = G
    field
      _⋆_        : ⌞ R ⌟ → T → T
      ⋆-distribl : ∀ r x y → r ⋆ (x + y)   ≡ (r ⋆ x) + (r ⋆ y)
      ⋆-distribr : ∀ r s x → (r R.+ s) ⋆ x ≡ (r ⋆ x) + (s ⋆ x)
      ⋆-assoc    : ∀ r s x → r ⋆ (s ⋆ x)   ≡ (r R.* s) ⋆ x
      ⋆-id       : ∀ x     → R.1r ⋆ x      ≡ x
```

We refer to an "$R$-module structure on an abelian group $G$" as a _ring
action_ of $R$ on $G$, for short. The definition is unsurprising: we
bundle the scalar multiplication together with the proofs that this is,
indeed, an $R$-module structure.

<!--
```agda
  Action→Module-on
    : ∀ {ℓg} {T : Type ℓg} {G : Abelian-group-on T}
    → Ring-action G → Module-on R T
  Action→Module : ∀ {ℓg} (G : Abelian-group ℓg)
    → Ring-action (G .snd) → Module R ℓg

  Action→Module-on {G = G} act = mod where
    instance _ = G
    mod : Module-on R _
    mod .Module-on._+_ = _
    mod .Module-on._⋆_ = act .Ring-action._⋆_
    mod .Module-on.has-is-mod = record
      { has-is-ab = G .Abelian-group-on.has-is-ab ; Ring-action act }

  Action→Module G act .fst = G .fst
  Action→Module G act .snd = Action→Module-on act
```
-->

The reason for allowing the extra dimension in quantification is the
following theorem: There is an equivalence between actions of $R$ on $G$
and ring morphisms $R \to [G,G]$ into the [endomorphism ring] of $G$.

[endomorphism ring]: Cat.Abelian.Endo.html

```agda
  Action→Hom
    : (G : Abelian-group ℓ)
    → Ring-action (G .snd) → Rings.Hom R (Endo Ab-ab-category G)

  Hom→Action
    : (G : Abelian-group ℓ)
    → Rings.Hom R (Endo Ab-ab-category G) → Ring-action (G .snd)
```

```agda
  Hom→Action G rhom .Ring-action._⋆_ x y = rhom # x # y
  Hom→Action G rhom .Ring-action.⋆-distribl r x y = (rhom # r) .preserves .is-group-hom.pres-⋆ _ _
  Hom→Action G rhom .Ring-action.⋆-distribr r s x = rhom .preserves .is-ring-hom.pres-+ r s #ₚ x
  Hom→Action G rhom .Ring-action.⋆-assoc r s x    = sym (rhom .preserves .is-ring-hom.pres-* r s #ₚ x)
  Hom→Action G rhom .Ring-action.⋆-id x           = rhom .preserves .is-ring-hom.pres-id #ₚ x

  Action→Hom G act .hom r .hom = act .Ring-action._⋆_ r
  Action→Hom G act .hom r .preserves .is-group-hom.pres-⋆ x y = act .Ring-action.⋆-distribl r x y
  Action→Hom G act .preserves .is-ring-hom.pres-id    = ext λ x → act .Ring-action.⋆-id _
  Action→Hom G act .preserves .is-ring-hom.pres-+ x y = ext λ x → act .Ring-action.⋆-distribr _ _ _
  Action→Hom G act .preserves .is-ring-hom.pres-* r s = ext λ x → sym (act .Ring-action.⋆-assoc _ _ _)

  Action≃Hom
    : (G : Abelian-group ℓ)
    → Ring-action (G .snd) ≃ Rings.Hom R (Endo Ab-ab-category G)
  Action≃Hom G =
    Iso→Equiv $ Action→Hom G , iso (Hom→Action G) (λ x → trivial!)
      (λ x → Iso.injective eqv (Σ-prop-path! refl))
    where private unquoteDecl eqv = declare-record-iso eqv (quote Ring-action)
```
