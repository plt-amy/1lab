---
description: |
  A correspondence is established between concretely-defined coproduct
  diagrams and general colimits of discrete diagrams.
---

<!--
```agda
open import Cat.Diagram.Coproduct.Indexed
open import Cat.Instances.Shape.Terminal
open import Cat.Diagram.Colimit.Base
open import Cat.Instances.Discrete
open import Cat.Functor.Kan.Base
open import Cat.Prelude
```
-->

```agda
module Cat.Diagram.Colimit.Coproduct {o h} (C : Precategory o h) where
```

<!--
```agda
open import Cat.Reasoning C

private variable
  o' ℓ' : Level
```
-->

# Coproducts are colimits

## Indexed coproducts as colimits

Similarly to the product case, when $I$ is a groupoid, indexed
coproducts correspond to colimits of discrete diagrams of shape $I$.

```agda
module _ {I : Type ℓ'} (i-is-grpd : is-groupoid I) (F : I → Ob) where
  open _=>_

  Inj→Cocone : ∀ {x} → (∀ i → Hom (F i) x)
             → Disc-adjunct {C = C} F => Const x
  Inj→Cocone inj .η i = inj i
  Inj→Cocone inj .is-natural i j p =
    J (λ j p → inj j ∘ subst (Hom (F i) ⊙ F) p id ≡ id ∘ inj i)
      (elimr (transport-refl id) ∙ sym (idl _)) p

  is-indexed-coproduct→is-colimit
    : ∀ {x} {inj : ∀ i → Hom (F i) x}
    → is-indexed-coproduct C F inj
    → is-colimit (Disc-adjunct F) x (Inj→Cocone inj)
  is-indexed-coproduct→is-colimit {x = x} {inj} ic =
    to-is-colimitp mc refl
    where
      module ic = is-indexed-coproduct ic
      open make-is-colimit

      mc : make-is-colimit (Disc-adjunct F) x
      mc .ψ i = inj i
      mc .commutes {i} {j} p =
        J (λ j p → inj j ∘ subst (Hom (F i) ⊙ F) p id ≡ inj i)
          (elimr (transport-refl id))
          p
      mc .universal eta p = ic.match eta
      mc .factors eta p = ic.commute
      mc .unique eta p other q = ic.unique eta q

  is-colimit→is-indexed-coprduct
    : ∀ {K : Functor ⊤Cat C}
    → {eps : Disc-adjunct F => K F∘ !F}
    → is-lan !F (Disc-adjunct F) K eps
    → is-indexed-coproduct C F (eps .η)
  is-colimit→is-indexed-coprduct {K = K} {eps} colim = ic where
    module colim = is-colimit colim
    open is-indexed-coproduct

    ic : is-indexed-coproduct C F (eps .η)
    ic .match k =
      colim.universal k
        (J (λ j p → k j ∘ subst (Hom (F _) ⊙ F) p id ≡ k _)
           (elimr (transport-refl _)))
    ic .commute =
      colim.factors _ _
    ic .unique k comm =
      colim.unique _ _ _ comm

  IC→Colimit
    : Indexed-coproduct C F
    → Colimit {C = C} (Disc-adjunct F)
  IC→Colimit ic =
    to-colimit (is-indexed-coproduct→is-colimit has-is-ic)
    where open Indexed-coproduct ic

  Colimit→IC
    : Colimit {C = C} (Disc-adjunct F)
    → Indexed-coproduct C F
  Colimit→IC colim .Indexed-coproduct.ΣF = _
  Colimit→IC colim .Indexed-coproduct.ι = _
  Colimit→IC colim .Indexed-coproduct.has-is-ic =
    is-colimit→is-indexed-coprduct (Colimit.has-colimit colim)
```
