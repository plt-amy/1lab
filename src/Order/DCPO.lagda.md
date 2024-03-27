<!--
```agda
open import Cat.Displayed.Univalence.Thin
open import Cat.Functor.Subcategory
open import Cat.Displayed.Total
open import Cat.Prelude

open import Data.Bool

open import Order.Diagram.Lub
open import Order.Univalent
open import Order.Base

import Cat.Reasoning

import Order.Reasoning
```
-->

```agda
module Order.DCPO where
```

<!--
```agda
private variable
  o ℓ ℓ' : Level
  Ix A B : Type o
```
-->

# Directed-complete partial orders {defines="dcpo semidirected-family"}

Let $(P, \le)$ be a [[partial order]]. A family of elements $f : I \to P$ is
a **semi-directed family** if for every $i, j$, there merely exists
some $k$ such $f i \le f k$ and $f j \le f k$. A semidirected family
$f : I \to P$ is a **directed family** when $I$ is merely inhabited.

```agda
module _ {o ℓ} (P : Poset o ℓ) where
  open Order.Reasoning P

  is-semidirected-family : ∀ {Ix : Type o} → (Ix → Ob) → Type _
  is-semidirected-family {Ix = Ix} f = ∀ i j → ∃[ k ∈ Ix ] (f i ≤ f k × f j ≤ f k)

  record is-directed-family {Ix : Type o} (f : Ix → Ob) : Type (o ⊔ ℓ) where
    no-eta-equality
    field
      elt : ∥ Ix ∥
      semidirected : is-semidirected-family f
```

Note that any family whose indexing type is a proposition is
automatically semi-directed:

```agda
  prop-indexed→semidirected
    : ∀ {Ix : Type o} → (s : Ix → Ob) → is-prop Ix
    → is-semidirected-family s
  prop-indexed→semidirected s prop i j =
    inc (i , ≤-refl , ≤-refl' (ap s (prop j i)))
```

The poset $(P, \le)$ is a **directed-complete partial order**, or DCPO,
if it has [[least upper bounds]] of all directed families.

```agda
  record is-dcpo : Type (lsuc o ⊔ ℓ) where
    no-eta-equality
    field
      directed-lubs
        : ∀ {Ix : Type o} (f : Ix → Ob) → is-directed-family f → Lub P f

    module ⋃ {Ix : Type o} (f : Ix → Ob) (dir : is-directed-family f) =
      Lub (directed-lubs f dir)

    open ⋃ using () renaming (lub to ⋃; fam≤lub to fam≤⋃; least to ⋃-least) public
```

Since least upper bounds are unique when they exist, being a DCPO is a
[[property|proposition]] of a poset, and not structure on that poset.

<!--
```agda
module _ {o ℓ} {P : Poset o ℓ} where
  open Poset P
  open is-dcpo
```
-->

```agda
  is-dcpo-is-prop : is-prop (is-dcpo P)
  is-dcpo-is-prop = Iso→is-hlevel 1 eqv hlevel!
    where unquoteDecl eqv = declare-record-iso eqv (quote is-dcpo)
```

# Scott-continuous functions

Let $(P, \le)$ and $(Q, \lsq)$ be a pair of posets. A monotone map $f :
P \to Q$ is called **Scott-continuous** when it preserves all directed
lubs.

<!--
```agda
module _ {P Q : Poset o ℓ} where
  private
    module P = Poset P
    module Q = Poset Q

  open is-directed-family
  open Total-hom
```
-->

```agda
  is-scott-continuous : (f : Posets.Hom P Q) → Type _
  is-scott-continuous f =
    ∀ {Ix} (s : Ix → P.Ob) (fam : is-directed-family P s)
    → ∀ x → is-lub P s x → is-lub Q (f .hom ⊙ s) (f .hom x)

  is-scott-continuous-is-prop
    : ∀ (f : Posets.Hom P Q) → is-prop (is-scott-continuous f)
  is-scott-continuous-is-prop = hlevel!
```

If $(P, \le)$ is a DCPO, then any function $f : P \to Q$ which preserves
directed lubs is automatically a monotone map, and, consequently,
Scott-continuous.

To see this, suppose we're given $x, y : P$ with $x \le y$. The family
$s : \rm{Bool} \to P$ that sends $\rm{true}$ to $x$ and $\rm{false}$ to
$y$ is directed: $\rm{Bool}$ is inhabited, and $\rm{false}$ is a least
upper bound for arbitrary values of the family. Since $f$ preserves
lubs, we have

$$
f(x) \le (\sqcup f(s)) = f(\sqcup s) = f(y)
$$

```agda
  opaque
    dcpo+scott→monotone
      : is-dcpo P
      → (f : P.Ob → Q.Ob)
      → (∀ {Ix} (s : Ix → Poset.Ob P) (fam : is-directed-family P s)
         → ∀ x → is-lub P s x → is-lub Q (f ⊙ s) (f x))
      → ∀ {x y} → x P.≤ y → f x Q.≤ f y
    dcpo+scott→monotone is-dcpo f scott {x} {y} p =
      fs-lub .is-lub.fam≤lub (lift true) where
        s : Lift o Bool → P.Ob
        s (lift b) = if b then x else y

        sx≤sfalse : ∀ b → s b P.≤ s (lift false)
        sx≤sfalse (lift true) = p
        sx≤sfalse (lift false) = P.≤-refl

        s-directed : is-directed-family P s
        s-directed .elt =
          inc (lift true)
        s-directed .semidirected i j =
          inc (lift false , sx≤sfalse _ , sx≤sfalse _)

        s-lub : is-lub P s y
        s-lub .is-lub.fam≤lub = sx≤sfalse
        s-lub .is-lub.least z lt = lt (lift false)

        fs-lub : is-lub Q (f ⊙ s) (f y)
        fs-lub = scott s s-directed y s-lub
```

Moreover, if $f : P \to Q$ is an arbitrary monotone map, and $s : I \to
P$ is a directed family, then $fs : I \to Q$ is still a directed family.

```agda
  monotone∘directed
    : ∀ {Ix : Type o}
    → {s : Ix → P.Ob}
    → (f : Posets.Hom P Q)
    → is-directed-family P s
    → is-directed-family Q (f .hom ⊙ s)
  monotone∘directed f dir .elt = dir .elt
  monotone∘directed f dir .is-directed-family.semidirected i j =
    ∥-∥-map (Σ-map₂ (×-map (f .pres-≤) (f .pres-≤)))
      (dir .semidirected i j)
```

<!--
```agda
module _ where
  open Total-hom
```
-->

The identity function is Scott-continuous.

```agda
  scott-id
    : ∀ {P : Poset o ℓ}
    → is-scott-continuous (Posets.id {x = P})
  scott-id s fam x lub = lub
```

Scott-continuous functions are closed under composition.

```agda
  scott-∘
    : ∀ {P Q R : Poset o ℓ}
    → (f : Posets.Hom Q R) (g : Posets.Hom P Q)
    → is-scott-continuous f → is-scott-continuous g
    → is-scott-continuous (f Posets.∘ g)
  scott-∘ f g f-scott g-scott s dir x lub =
    f-scott (g .hom ⊙ s)
      (monotone∘directed g dir)
      (g .hom x)
      (g-scott s dir x lub)
```


# The category of DCPOs

DCPOs form a [[subcategory]] of the category of posets. Furthermore,
since being a DCPO is a property, identity of DCPOs is determined by
identity of their underlying posets: thus, the category of DCPOs is
[[univalent|univalent category]].

```agda
DCPOs-subcat : ∀ (o ℓ : Level) → Subcat (Posets o ℓ) (lsuc o ⊔ ℓ) (lsuc o ⊔ ℓ)
DCPOs-subcat o ℓ .Subcat.is-ob = is-dcpo
DCPOs-subcat o ℓ .Subcat.is-hom f _ _ = is-scott-continuous f
DCPOs-subcat o ℓ .Subcat.is-hom-prop f _ _ = is-scott-continuous-is-prop f
DCPOs-subcat o ℓ .Subcat.is-hom-id _ = scott-id
DCPOs-subcat o ℓ .Subcat.is-hom-∘ {f = f} {g = g} = scott-∘ f g

DCPOs : ∀ (o ℓ : Level) → Precategory (lsuc (o ⊔ ℓ)) (lsuc o ⊔ ℓ)
DCPOs o ℓ = Subcategory (DCPOs-subcat o ℓ)

DCPOs-is-category : ∀ {o ℓ} → is-category (DCPOs o ℓ)
DCPOs-is-category = subcat-is-category Posets-is-category (λ _ → is-dcpo-is-prop)
```

<!--
```agda
module DCPOs {o ℓ : Level} = Cat.Reasoning (DCPOs o ℓ)

DCPO : (o ℓ : Level) → Type _
DCPO o ℓ = DCPOs.Ob {o} {ℓ}

Forget-DCPO : ∀ {o ℓ} → Functor (DCPOs o ℓ) (Sets o)
Forget-DCPO = Forget-poset F∘ Forget-subcat
```
-->

# Reasoning with DCPOs

The following pair of modules re-exports facts about the underlying
posets (resp. monotone maps) of DCPOs (resp. Scott-continuous
functions). They also prove a plethora of small lemmas that are useful
in formalisation but not for informal reading.

<details>
<summary>These proofs are all quite straightforward, so we omit them.
</summary>

```agda
module DCPO {o ℓ} (D : DCPO o ℓ) where
  poset : Poset o ℓ
  poset = D .fst

  open Order.Reasoning poset public

  set : Set o
  set = el ⌞ D ⌟ Ob-is-set

  has-dcpo : is-dcpo poset
  has-dcpo = D .snd

  open is-dcpo has-dcpo public

  ⋃-pointwise
    : ∀ {Ix} {s s' : Ix → Ob}
    → {fam : is-directed-family poset s} {fam' : is-directed-family poset s'}
    → (∀ ix → s ix ≤ s' ix)
    → ⋃ s fam ≤ ⋃ s' fam'
  ⋃-pointwise p = ⋃.least _ _ (⋃ _ _) λ ix →
    ≤-trans (p ix) (⋃.fam≤lub _ _ ix)

module Scott {o ℓ} {D E : DCPO o ℓ} (f : DCPOs.Hom D E) where
  private
    module D = DCPO D
    module E = DCPO E

  mono : Posets.Hom D.poset E.poset
  mono = Subcat-hom.hom f

  monotone : ∀ {x y} → x D.≤ y → f # x E.≤ f # y
  monotone = mono .pres-≤

  opaque
    pres-directed-lub
      : ∀ {Ix} (s : Ix → D.Ob) → is-directed-family D.poset s
      → ∀ x → is-lub (D .fst) s x → is-lub (E .fst) (apply f ⊙ s) (f # x)
    pres-directed-lub = Subcat-hom.witness f

    directed
      : ∀ {Ix} {s : Ix → D.Ob} → is-directed-family D.poset s
      → is-directed-family E.poset (apply f ⊙ s)
    directed dir = monotone∘directed (Subcat-hom.hom f) dir

    pres-⋃
      : ∀ {Ix} (s : Ix → D.Ob) → (dir : is-directed-family D.poset s)
      → f # (D.⋃ s dir) ≡ E.⋃ (apply f ⊙ s) (directed dir)
    pres-⋃ s dir =
      E.≤-antisym
        (is-lub.least (pres-directed-lub s dir (D.⋃ s dir) (D.⋃.has-lub s dir))
          (E.⋃ (apply f ⊙ s) (directed dir))
          (E.⋃.fam≤lub (apply f ⊙ s) (directed dir)))
        (E.⋃.least (apply f ⊙ s) (directed dir) (apply f (D.⋃ s dir)) λ i →
          monotone (D.⋃.fam≤lub s dir i))
```
</details>

<!--
```
module _ {o ℓ} {D E : DCPO o ℓ} where
  private
    module D = DCPO D
    module E = DCPO E

  open is-directed-family
  open Total-hom
```
-->

We also provide a couple methods for constructing Scott-continuous maps.
First, we note that if a function is monotonic and commutes with some
chosen _assignment_ of least upper bounds, then it is Scott-continuous.

```agda
  to-scott
    : (f : D.Ob → E.Ob)
    → (∀ {x y} → x D.≤ y → f x E.≤ f y)
    → (∀ {Ix} (s : Ix → D.Ob) → (dir : is-directed-family D.poset s)
       → is-lub E.poset (f ⊙ s) (f (D.⋃ s dir)))
    → DCPOs.Hom D E
  to-scott f monotone pres-⋃ = sub-hom fᵐ pres-lub where
      fᵐ : Monotone D.poset E.poset
      fᵐ .hom = f
      fᵐ .pres-≤ = monotone

      pres-lub
        : ∀ {Ix} (s : Ix → D.Ob) → (dir : is-directed-family D.poset s)
        → ∀ x → is-lub D.poset s x → is-lub E.poset (f ⊙ s) (f x)
      pres-lub s dir x x-lub .is-lub.fam≤lub i =
        monotone (is-lub.fam≤lub x-lub i)
      pres-lub s dir x x-lub .is-lub.least y le =
        f x              E.≤⟨ monotone (is-lub.least x-lub _ (D.⋃.fam≤lub s dir)) ⟩
        f (D.⋃ s dir)    E.=⟨ lub-unique (pres-⋃ s dir) (E.⋃.has-lub (f ⊙ s) (monotone∘directed fᵐ dir)) ⟩
        E.⋃ (f ⊙ s) _    E.≤⟨ E.⋃.least _ _ y le ⟩
        y                E.≤∎
```

Furthermore, if $f$ preserves arbitrary least upper bounds, then it
is monotone, and thus Scott-continuous.

```agda
  to-scott-directed
    : (f : D.Ob → E.Ob)
    → (∀ {Ix} (s : Ix → D.Ob) → (dir : is-directed-family D.poset s)
       → ∀ x → is-lub D.poset s x → is-lub E.poset (f ⊙ s) (f x))
    → DCPOs.Hom D E
  to-scott-directed f pres .Subcat-hom.hom .hom = f
  to-scott-directed f pres .Subcat-hom.hom .pres-≤ =
    dcpo+scott→monotone D.has-dcpo f pres
  to-scott-directed f pres .Subcat-hom.witness = pres
```
