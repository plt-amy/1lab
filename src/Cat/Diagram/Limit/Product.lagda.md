---
description: |
  A correspondence is established between concretely-defined product
  diagrams and general limits of discrete diagrams.
---

<!--
```agda
open import Cat.Instances.Shape.Terminal
open import Cat.Diagram.Product.Indexed
open import Cat.Diagram.Limit.Base
open import Cat.Instances.Discrete
open import Cat.Instances.Functor
open import Cat.Functor.Kan.Base
open import Cat.Diagram.Product
open import Cat.Prelude

open import Data.Bool
```
-->

```agda
module Cat.Diagram.Limit.Product {o h} (C : Precategory o h) where
```

<!--
```agda
open import Cat.Reasoning C

open is-product
open Product
open Functor
open _=>_
```
-->

# Products are limits

We establish the correspondence between binary products $A \times B$ and
limits over the functor out of $\rm{Disc}(\{0,1\})$ which maps $0$
to $A$ and $1$ to $B$. We begin by defining the functor (reusing
existing infrastructure):

```agda
2-object-category : Precategory _ _
2-object-category = Disc! Bool

2-object-diagram : Ob → Ob → Functor 2-object-category C
2-object-diagram a b = Disc-diagram λ where
  true  → a
  false → b
```

With that out of the way, we can establish the claimed equivalence. We
start by showing that any pair of morphisms $A \ot Q \to B$ defines a
cone over the discrete diagram consisting of $A$ and $B$. This is
essentially by _definition_ of what it means to be a cone in this case,
but they're arranged in very different ways:

```agda
Pair→Cone
  : ∀ {q a b} → Hom q a → Hom q b
  → Const q => (2-object-diagram a b)
Pair→Cone f g = Disc-natural λ where
  true  → f
  false → g
```

The two-way correspondence between products and terminal cones is then
simple enough to establish by appropriately shuffling the data.

```agda
is-product→is-limit
  : ∀ {x a b} {p1 : Hom x a} {p2 : Hom x b}
  → is-product C p1 p2
  → is-limit {C = C} (2-object-diagram a b) x (Pair→Cone p1 p2)
is-product→is-limit {x = x} {a} {b} {p1} {p2} is-prod =
  to-is-limitp ml λ where
    {true} → refl
    {false} → refl
  where
    module is-prod = is-product is-prod
    open make-is-limit

    ml : make-is-limit (2-object-diagram a b) x
    ml .ψ true = p1
    ml .ψ false = p2
    ml .commutes {true}  {true}  f = idl p1
    ml .commutes {true}  {false} f = absurd (true≠false f)
    ml .commutes {false} {true}  f = absurd (true≠false $ sym f)
    ml .commutes {false} {false} f = idl p2
    ml .universal       eta _ = is-prod.⟨ eta true , eta false ⟩
    ml .factors {true}  eta _ = is-prod.π₁∘factor
    ml .factors {false} eta _ = is-prod.π₂∘factor
    ml .unique eta p other q = is-prod.unique other (q true) (q false)

is-limit→is-product
  : ∀ {a b} {K : Functor ⊤Cat C}
  → {eta : K F∘ !F => 2-object-diagram a b}
  → is-ran !F (2-object-diagram a b) K eta
  → is-product C (eta .η true) (eta .η false)
is-limit→is-product {a} {b} {K} {eta} lim = prod where
  module lim = is-limit lim

  pair
    : ∀ {y} → Hom y a → Hom y b
    → ∀ (j : Bool) → Hom y (2-object-diagram a b .F₀ j)
  pair p1 p2 true = p1
  pair p1 p2 false = p2

  pair-commutes
    : ∀ {y} {p1 : Hom y a} {p2 : Hom y b}
    → {i j : Bool}
    → (p : i ≡ j)
    → 2-object-diagram a b .F₁ p ∘ pair p1 p2 i ≡ pair p1 p2 j
  pair-commutes {p1 = p1} {p2 = p2} =
      J (λ _ p → 2-object-diagram a b .F₁ p ∘ pair p1 p2 _ ≡ pair p1 p2 _)
        (eliml (2-object-diagram a b .F-id))

  prod : is-product C (eta .η true) (eta .η false)
  prod .⟨_,_⟩ f g = lim.universal (pair f g) pair-commutes
  prod .π₁∘factor {_} {p1'} {p2'} = lim.factors (pair p1' p2') pair-commutes
  prod .π₂∘factor {_} {p1'} {p2'} = lim.factors (pair p1' p2') pair-commutes
  prod .unique other p q = lim.unique _ _ other λ where
    true → p
    false → q

Product→Limit : ∀ {a b} → Product C a b → Limit (2-object-diagram a b)
Product→Limit prod = to-limit (is-product→is-limit (has-is-product prod))

Limit→Product : ∀ {a b} → Limit (2-object-diagram a b) → Product C a b
Limit→Product lim .apex = Limit.apex lim
Limit→Product lim .π₁ = Limit.cone lim .η true
Limit→Product lim .π₂ = Limit.cone lim .η false
Limit→Product lim .has-is-product =
  is-limit→is-product (Limit.has-limit lim)
```

We note that _any_ functor $F : \rm{Disc}(\{0,1\}) \to \cC$ is
canonically _equal_, not just naturally isomorphic, to the one we
defined above.

```agda
canonical-functors
  : ∀ (F : Functor 2-object-category C)
  → F ≡ 2-object-diagram (F₀ F true) (F₀ F false)
canonical-functors F = Functor-path p q where
  p : ∀ x → _
  p false = refl
  p true  = refl

  q : ∀ {x y} (f : x ≡ y) → _
  q {false} {false} p =
    F₁ F p            ≡⟨ ap (F₁ F) (Bool-is-set _ _ _ _) ⟩
    F₁ F refl         ≡⟨ F-id F ⟩
    id                ∎
  q {true} {true} p =
    F₁ F p            ≡⟨ ap (F₁ F) (Bool-is-set _ _ _ _) ⟩
    F₁ F refl         ≡⟨ F-id F ⟩
    id                ∎
  q {false} {true} p = absurd (true≠false (sym p))
  q {true} {false} p = absurd (true≠false p)
```

## Indexed products as limits

In the particular case where $I$ is a groupoid, e.g. because it arises
as the space of objects of a [[univalent category]], an [[indexed product]] for
$F : I \to \cC$ is the same thing as a limit over $F$, considered as
a functor $\rm{Disc}{I} \to \cC$. We can not lift this restriction: If
$I$ is not a groupoid, then its path spaces $x = y$ are not necessarily
sets, and so the `Disc`{.Agda} construction does not apply to it.

```agda
module _ {ℓ} {I : Type ℓ} (i-is-grpd : is-groupoid I) (F : I → Ob) where
  open _=>_

  Proj→Cone : ∀ {x} → (∀ i → Hom x (F i))
            → Const x => Disc-adjunct {C = C} F
  Proj→Cone π .η i = π i
  Proj→Cone π .is-natural i j p =
    J (λ j p →  π j ∘ id ≡ subst (Hom (F i) ⊙ F) p id ∘ π i)
      (idr _ ∙ introl (transport-refl id))
      p

  is-indexed-product→is-limit
    : ∀ {x} {π : ∀ i → Hom x (F i)}
    → is-indexed-product C F π
    → is-limit (Disc-adjunct F) x (Proj→Cone π)
  is-indexed-product→is-limit {x = x} {π} ip =
    to-is-limitp ml refl
    where
      module ip = is-indexed-product ip
      open make-is-limit

      ml : make-is-limit (Disc-adjunct F) x
      ml .ψ j = π j
      ml .commutes {i} {j} p =
        J (λ j p → subst (Hom (F i) ⊙ F) p id ∘ π i ≡ π j)
          (eliml (transport-refl _))
          p
      ml .universal eta p = ip.tuple eta
      ml .factors eta p = ip.commute
      ml .unique eta p other q = ip.unique eta q

  is-limit→is-indexed-product
    : ∀ {K : Functor ⊤Cat C}
    → {eta : K F∘ !F => Disc-adjunct F}
    → is-ran !F (Disc-adjunct F) K eta
    → is-indexed-product C F (eta .η)
  is-limit→is-indexed-product {K = K} {eta} lim = ip where
    module lim = is-limit lim
    open is-indexed-product hiding (eta)

    ip : is-indexed-product C F (eta .η)
    ip .tuple k =
      lim.universal k
        (J (λ j p → subst (Hom (F _) ⊙ F) p id ∘ k _ ≡ k j)
           (eliml (transport-refl _)))
    ip .commute =
      lim.factors _ _
    ip .unique k comm =
      lim.unique _ _ _ comm

  IP→Limit : Indexed-product C F → Limit {C = C} (Disc-adjunct F)
  IP→Limit ip =
    to-limit (is-indexed-product→is-limit has-is-ip)
    where open Indexed-product ip

  Limit→IP : Limit {C = C} (Disc-adjunct F) → Indexed-product C F
  Limit→IP lim .Indexed-product.ΠF = _
  Limit→IP lim .Indexed-product.π = _
  Limit→IP lim .Indexed-product.has-is-ip =
    is-limit→is-indexed-product (Limit.has-limit lim)
```
