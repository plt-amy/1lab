---
description: |
  Free objects, adjoints, and initiality.
---
<!--
```agda
open import Cat.Functor.Subcategory
open import Cat.Functor.Properties
open import Cat.Diagram.Initial
open import Cat.Functor.Adjoint
open import Cat.Prelude

import Cat.Functor.Reasoning
import Cat.Reasoning
```
-->
```agda
module Cat.Diagram.Free where
```

# Free objects

<!--
```agda
module _
  {oc ℓc od ℓd}
  {C : Precategory oc ℓc}
  {D : Precategory od ℓd}
  (U : Functor C D)
  where
  private
    module C = Cat.Reasoning C
    module D = Cat.Reasoning D
    module U = Cat.Functor.Reasoning U
```
-->

One common perspective on [[adjunctions]] describe free constructions:
the right adjoint forgets structure, and the left adjoint freely adds it.
These sorts of adjunctions are so common that we be tempted to *define*
free constructions as left adjoints. However, this doesn't quite capture
the whole story: there are many situations where a left adjoint does not
exist, yet we can perform a free constructions on *some* objects.
This gives rise to the following definition:

:::{.definition #free-object}

Let $\cC, \cD$ be a pair of categories, and let $U : \cC \to \cD$ be a
functor. A **free object** on $X : \cD$ is an object $A : \cC$ equipped
with a morphism $\eta : \cD(X, U(A))$, satisfying the following universal
proprety:

- For every $B : \cD$ and $f : \cD(X, U(B))$, there exists a unique
  map $\eps : \cC(A, B)$ with $U(\eps) \circ \eta = f$.
:::

```agda
  record is-free-object-on {x : D.Ob} {a : C.Ob} (eta : D.Hom x (U.₀ a)) : Type (oc ⊔ ℓc ⊔ ℓd) where
    field
      eps : ∀ {b} → D.Hom x (U.₀ b) → C.Hom a b
      commute : ∀ {b} {f : D.Hom x (U.₀ b)} → U.₁ (eps f) D.∘ eta ≡ f
      unique
        : ∀ {b} {f : D.Hom x (U.₀ b)}
        → (other : C.Hom a b)
        → U.₁ other D.∘ eta ≡ f
        → other ≡ eps f

    unique₂
      : ∀ {b} {f : D.Hom x (U.₀ b)}
      → (other₁ other₂ : C.Hom a b)
      → U.₁ other₁ D.∘ eta ≡ f
      → U.₁ other₂ D.∘ eta ≡ f
      → other₁ ≡ other₂
    unique₂ other₁ other₂ p q = unique other₁ p ∙ sym (unique other₂ q)

  record Free-object-on (x : D.Ob) : Type (oc ⊔ ℓc ⊔ ℓd) where
    field
      free : C.Ob
      eta : D.Hom x (U.₀ free)
      has-is-free : is-free-object-on eta

    open is-free-object-on has-is-free public

  open Free-object-on
```

Intuitively, a free object on $X$ is an approximation of a
(potentially non-existent) left adjoint at $X$.

A free object $A : \cC$ on $X : \cD$ induces an equivalence between
$\cD(X, U(B))$ and $\cC(A, B)$. in other words, free objects are
representing objects for the functor $\cD(X,U(-))$.

```agda
  free-object-eps-equiv
    : ∀ {x} (a : Free-object-on x)
    → ∀ b → is-equiv (a .eps {b})
  free-object-eps-equiv a b .is-eqv f .centre .fst = U.₁ f D.∘ a .eta
  free-object-eps-equiv a b .is-eqv f .centre .snd = sym $ a .unique f refl
  free-object-eps-equiv a b .is-eqv f .paths (g , p) = Σ-prop-path! $
    ap (λ ϕ → U.₁ ϕ D.∘ a .eta) (sym p)
    ∙ a .commute
```

Note that free objects are unique up to isomorphism.

```agda
  free-object-unique : ∀ {x} (a b : Free-object-on x) → a .free C.≅ b .free
  free-object-unique a b =
    C.make-iso (a .eps (b .eta)) (b .eps (a .eta))
      (unique₂ b _ _ (U.popr (b .commute) ∙ a .commute) (D.eliml U.F-id))
      (unique₂ a _ _ (U.popr (a .commute) ∙ b .commute) (D.eliml U.F-id))
```


If $U$ does in fact have a left adjoint, then every $X : \cD$ has a free object.

```agda
  module _ (F : Functor D C) (F⊣U : F ⊣ U) where
    open is-free-object-on
    open _⊣_ F⊣U

    left-adjoint→unit-is-free : ∀ x → is-free-object-on (unit.η x)
    left-adjoint→unit-is-free x .eps f = R-adjunct F⊣U f
    left-adjoint→unit-is-free x .commute = L-R-adjunct F⊣U _
    left-adjoint→unit-is-free x .unique other p =
      Equiv.injective (_ , L-adjunct-is-equiv F⊣U) (p ∙ sym (L-R-adjunct F⊣U _))

    left-adjoint→free-objects : ∀ x → Free-object-on x
    left-adjoint→free-objects x .free = Functor.F₀ F x
    left-adjoint→free-objects x .eta = unit.η x
    left-adjoint→free-objects x .has-is-free = left-adjoint→unit-is-free x
```

Conversely, if $\cD$ has all free objects, then $U$ has a left adjoint.
We begin by constructing a functor $F : \cD \to \cC$ that assigns each
object to its free counterpart; functoriality is given by the universal
property.

```agda
  module _ (free-objects : ∀ x → Free-object-on x) where
    private
      module free x = Free-object-on (free-objects x)
      open Functor
      open _=>_
      open _⊣_

    free-objects→functor : Functor D C
    free-objects→functor .F₀ = free.free
    free-objects→functor .F₁ f = free.eps _ (free.eta _ D.∘ f)
    free-objects→functor .F-id =
      sym $ free.unique _ C.id $ D.eliml U.F-id ∙ sym (D.idr _)
    free-objects→functor .F-∘ f g =
      sym $ free.unique _ _ $ U.popr (free.commute _) ∙ D.extendl (free.commute _)
```

The unit of the adjunction is given by $\eta$, and the counit by $\eps \id$.
Naturality and the zig-zag identities all follow from the universal property
of free objects.

```agda
    free-objects→left-adjoint : free-objects→functor ⊣ U
    free-objects→left-adjoint .unit .η = free.eta
    free-objects→left-adjoint .unit .is-natural x y f = sym (free.commute x)
    free-objects→left-adjoint .counit .η x = free.eps (U.₀ x) D.id
    free-objects→left-adjoint .counit .is-natural x y f =
      free.unique₂ (U.F₀ x) _ _
        (U.popr (free.commute _) ∙ D.cancell (free.commute _))
        (U.popr (free.commute _) ∙ D.idr _)
    free-objects→left-adjoint .zig =
      free.unique₂ _ _ _
        (U.popr (free.commute _) ∙ D.cancell (free.commute _))
        (D.eliml U.F-id)
    free-objects→left-adjoint .zag =
      free.commute _
```

## Free objects and initiality

In categorical semantics, syntax for a theory $\bT$ is often
presented in 2 seemingly unconnected ways:

1. Via a left adjoints to the forgetful functor that forgets the structure
  of a $\bT$-model; or
2. As an [[initial object]] in the category of $\bT$-models.

Left adjoints encode the universal property "syntax with generators":
structure-preserving maps $\cC(F(X),A)$ out of the syntax generated by $X$
are given by non-structure $\cD(X,U(A))$ on the generators. Conversely,
initial objects give us the universal property of "syntax without generators":
there is a unique structure-preserving map out of the syntax into each model.

We can somewhat reconcile these views by recalling that
[[left adjoints preserve colimits|lapc]]. The initial object is a colimit,
so the initial object in the category $\bT$-models is $F(\bot)$. In other
words: "syntax without generators" and "syntax on 0 generators" coincide.
This correspondence remains intact even when we lack a full left adjoint.

For the remainder of this section, assume that $\cD$ has an initial object
$\bot_{\cD}$. If there is a free object $A : \cC$ on $\bot_{\cD}$, then
$A$ is an initial object in $\cC$.

```agda
  module _ (initial : Initial D) where
    open Initial initial
    open is-free-object-on

    free-on-initial→initial
      : (F[⊥] : Free-object-on bot)
      → is-initial C (F[⊥] .free)
    free-on-initial→initial F[⊥] x .centre = F[⊥] .eps ¡
    free-on-initial→initial F[⊥] x .paths f =
      sym $ F[⊥] .unique f (sym (¡-unique _))
```

Conversely, if $\cC$ has an initial object $\bot_{\cC}$, then $\bot_{\cC}$
is a free object for $\bot_{\cC}$.

```agda
    is-initial→free-on-initial
      : (c-initial : Initial C)
      → is-free-object-on {a = Initial.bot c-initial} ¡ 
    is-initial→free-on-initial c-initial .eps _ =
      Initial.¡ c-initial
    is-initial→free-on-initial c-initial .commute =
      ¡-unique₂ _ _
    is-initial→free-on-initial c-initial .unique _ _ =
      sym $ Initial.¡-unique c-initial _
```

Note an initial object in $\cC$ does not guarantee an initial object in
$\cD$, regardless of how many free objects there are. Put syntactically,
a notion of "syntax without generators" does not imply that there is a
set of 0 generators!

<!-- [TODO: Reed M, 27/01/2024] Link to relative adjoints once that is written -->
