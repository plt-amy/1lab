<!--
```agda
open import Cat.Functor.Subcategory
open import Cat.Displayed.Total
open import Cat.Prelude

open import Data.Maybe.Base

open import Order.Diagram.Fixpoint
open import Order.Diagram.Bottom
open import Order.Diagram.Lub
open import Order.Base
open import Order.DCPO

import Cat.Reasoning

import Data.Nat as Nat
```
-->

```agda
module Order.DCPO.Pointed where
```

<!--
```agda
private variable
  o ℓ : Level
  Ix : Type o
```
-->

# Pointed DCPOs {defines="pointed-dcpo"}

A [DCPO] is **pointed** if it has a least element $\bot$. This is a
property of a DCPO, as bottom elements are unique.

[DCPO]: Order.DCPO.html

```agda
is-pointed-dcpo : DCPO o ℓ → Type _
is-pointed-dcpo D = Bottom (DCPO.poset D)

is-pointed-dcpo-is-prop : ∀ (D : DCPO o ℓ) → is-prop (is-pointed-dcpo D)
is-pointed-dcpo-is-prop D = Bottom-is-prop (DCPO.poset D)
```

A DCPO is pointed if and only if it has least upper bounds of all
semidirected families.

<!--
```agda
module _ {o ℓ} (D : DCPO o ℓ) where
  open DCPO D
  open Lub
```
-->

The forward direction is straightforward: bottom elements are equivalent
to least upper bounds of the empty family $\bot \to D$, and this family
is trivially semidirected.

```agda
  semidirected-lub→pointed
    : (∀ {Ix : Type o} (s : Ix → Ob) → is-semidirected-family poset s → Lub poset s)
    → is-pointed-dcpo D
  semidirected-lub→pointed lub =
    Lub→Bottom poset (lower-lub (lub (λ ()) (λ ())))
```

Conversely, if $D$ has a bottom element $\bot$, then we can extend any semidirected
family $I \to D$ to a directed family $\rm{Maybe}(I) \to D$ by sending `nothing`
to the bottom element.

<!--
```agda
module _ {o ℓ} (D : DCPO o ℓ) (pointed : is-pointed-dcpo D) where
  open DCPO D
  open Bottom pointed
  open is-directed-family
  open is-lub
```
-->

```agda
  extend-bottom : (Ix → Ob) → Maybe Ix → Ob
  extend-bottom s nothing = bot
  extend-bottom s (just i) = s i

  extend-bottom-directed
    : (s : Ix → Ob) → is-semidirected-family poset s
    → is-directed-family poset (extend-bottom s)
  extend-bottom-directed s semidir .elt = inc nothing
  extend-bottom-directed s semidir .semidirected (just i) (just j) = do
    (k , i≤k , j≤k) ← semidir i j
    pure (just k , i≤k , j≤k)
  extend-bottom-directed s semidir .semidirected (just x) nothing =
    pure (just x , ≤-refl , ¡)
  extend-bottom-directed s semidir .semidirected nothing (just y) =
    pure (just y , ¡ , ≤-refl)
  extend-bottom-directed s semidir .semidirected nothing nothing =
   pure (nothing , ≤-refl , ≤-refl)
```

Furthermore, $s$ has a least upper bound only if the extended family does.

```agda
  lub→extend-bottom-lub
    : ∀ {s : Ix → Ob} {x : Ob} → is-lub poset s x → is-lub poset (extend-bottom s) x
  lub→extend-bottom-lub {s = s} {x = x} x-lub .fam≤lub (just i) = x-lub .fam≤lub i
  lub→extend-bottom-lub {s = s} {x = x} x-lub .fam≤lub nothing = ¡
  lub→extend-bottom-lub {s = s} {x = x} x-lub .least y le = x-lub .least y (le ⊙ just)

  extend-bottom-lub→lub
    : ∀ {s : Ix → Ob} {x : Ob} → is-lub poset (extend-bottom s) x → is-lub poset s x
  extend-bottom-lub→lub x-lub .fam≤lub i = x-lub .fam≤lub (just i)
  extend-bottom-lub→lub x-lub .least y le = x-lub .least y λ where
    nothing → ¡
    (just i) → le i
```

If we put this all together, we see that any semidirected family has a least
upper bound in a pointed DCPO.

```agda
  pointed→semidirected-lub
    : is-pointed-dcpo D
    → ∀ {Ix : Type o} (s : Ix → Ob) → is-semidirected-family poset s → Lub poset s
  pointed→semidirected-lub pointed {Ix = Ix} s semidir .Lub.lub =
    ⋃ (extend-bottom s) (extend-bottom-directed s semidir)
  pointed→semidirected-lub pointed {Ix = Ix} s semidir .Lub.has-lub =
    extend-bottom-lub→lub (⋃.has-lub _ _)
```

## Fixpoints {defines="kleenes-fixpoint-theorem"}

Let $D$ be a pointed DCPO. Every Scott continuous function $f : D \to D$ has a
[least fixed point].

[least fixed point]: Order.Diagram.Fixpoint.html

```agda
module _ {o ℓ} {D : DCPO o ℓ} where
  open DCPO D

  pointed→least-fixpoint
    : is-pointed-dcpo D
    → (f : DCPOs.Hom D D)
    → Least-fixpoint poset (Scott.mono f)
  pointed→least-fixpoint pointed f = f-fix where
    open Bottom pointed
    module f = Scott f
```

We begin by constructing a directed family $\NN \to D$ that maps $n$ to
$f^n(\bot)$.

```agda
    fⁿ : Nat → Ob → Ob
    fⁿ zero x = x
    fⁿ (suc n) x = f # (fⁿ n x)

    fⁿ-mono : ∀ {i j} → i Nat.≤ j → fⁿ i bot ≤ fⁿ j bot
    fⁿ-mono Nat.0≤x = ¡
    fⁿ-mono (Nat.s≤s p) = f.monotone (fⁿ-mono p)

    fⁿ⊥ : Lift o Nat → Ob
    fⁿ⊥ (lift n) = fⁿ n bot

    fⁿ⊥-dir : is-directed-family poset fⁿ⊥
    fⁿ⊥-dir .is-directed-family.elt = inc (lift zero)
    fⁿ⊥-dir .is-directed-family.semidirected (lift i) (lift j) =
      inc (lift (Nat.max i j) , fⁿ-mono (Nat.max-≤l i j) , fⁿ-mono (Nat.max-≤r i j))
```

The least upper bound of this sequence shall be our least fixpoint. We
begin by proving a slightly stronger variation of the universal property;
namely for any $y$ such that $f y \le y$, $\bigcup (f^{n}(\bot)) \le y$.
This follows from som quick induction.

```agda
    fⁿ⊥≤fix : ∀ (y : Ob) → f # y ≤ y → ∀ n → fⁿ⊥ n ≤ y
    fⁿ⊥≤fix y p (lift zero) = ¡
    fⁿ⊥≤fix y p (lift (suc n)) =
      f # (fⁿ n bot)   ≤⟨ f.monotone (fⁿ⊥≤fix y p (lift n)) ⟩
      f # y            ≤⟨ p ⟩
      y                ≤∎

    least-fix : ∀ (y : Ob) → f # y ≤ y → ⋃ fⁿ⊥ fⁿ⊥-dir ≤ y
    least-fix y p = ⋃.least _ _ _ (fⁿ⊥≤fix y p)
```

Now, let's show that $\bigcup (f^{n}(\bot))$ is actuall a fixpoint.
First, the forward direction: $\bigcup (f^{n}(\bot)) \le f (\bigcup (f^{n}(\bot)))$.
This follows directly from Scott-continuity of $f$.

```agda
    roll : f # (⋃ fⁿ⊥ fⁿ⊥-dir) ≤ ⋃ fⁿ⊥ fⁿ⊥-dir
    roll =
      f # (⋃ fⁿ⊥ _)        =⟨ f.pres-⋃ fⁿ⊥ fⁿ⊥-dir ⟩
      ⋃ (apply f ⊙ fⁿ⊥) _  ≤⟨ ⋃.least _ _ _ (λ (lift n) → ⋃.fam≤lub _ _ (lift (suc n))) ⟩
      ⋃ fⁿ⊥ _              ≤∎
```

To show the converse, we use universal property we proved earlier to
re-arrange the goal to $f (f (\bigcup (f^{n}(\bot)))) \le f (\bigcup (f^{n}(\bot)))$.
We can then apply monotonicity of $f$, and then use the forward direction
to finish off the proof.

```agda
    unroll : ⋃ fⁿ⊥ fⁿ⊥-dir ≤ f # (⋃ fⁿ⊥ fⁿ⊥-dir)
    unroll = least-fix (f # (⋃ fⁿ⊥ fⁿ⊥-dir)) $
      f.monotone roll
```

All that remains is to package up the data.

```agda
    f-fix : Least-fixpoint poset f.mono
    f-fix .Least-fixpoint.fixpoint = ⋃ fⁿ⊥ fⁿ⊥-dir
    f-fix .Least-fixpoint.has-least-fixpoint .is-least-fixpoint.fixed =
      ≤-antisym roll unroll
    f-fix .Least-fixpoint.has-least-fixpoint .is-least-fixpoint.least y y-fix =
      least-fix y (≤-refl' y-fix)
```

## Strictly Scott-continuous maps

A Scott-continuous map is **strictly continuous** if it preserves bottoms.

<!--
```agda
module _ {o ℓ} {D E : DCPO o ℓ} where
  private
    module D = DCPO D
    module E = DCPO E
```
-->

```agda
  is-strictly-scott-continuous : (f : DCPOs.Hom D E) → Type _
  is-strictly-scott-continuous f =
    ∀ (x : D.Ob) → is-bottom D.poset x → is-bottom E.poset (f # x)
```

```agda
  is-strictly-scott-is-prop
    : (f : DCPOs.Hom D E) → is-prop (is-strictly-scott-continuous f)
  is-strictly-scott-is-prop f = Π-is-hlevel² 1 λ x _ →
    is-bottom-is-prop E.poset (f # x)
```


Strictly Scott-continuous functions are closed under identities
and composites.

```agda
strict-scott-id
  : ∀ {D : DCPO o ℓ}
  → is-strictly-scott-continuous (DCPOs.id {x = D})
strict-scott-id x x-bot = x-bot

strict-scott-∘
  : ∀ {D E F : DCPO o ℓ}
  → (f : DCPOs.Hom E F) (g : DCPOs.Hom D E)
  → is-strictly-scott-continuous f → is-strictly-scott-continuous g
  → is-strictly-scott-continuous (f DCPOs.∘ g)
strict-scott-∘ f g f-strict g-strict x x-bot =
  f-strict (g # x) (g-strict x x-bot)
```

Pointed DCPOs and strictly Scott-continuous functions form a subcategory
of the category of DCPOs.

```agda
Pointed-DCPOs-subcat : ∀ o ℓ → Subcat (DCPOs o ℓ) (o ⊔ ℓ) (o ⊔ ℓ)
Pointed-DCPOs-subcat o ℓ .Subcat.is-ob = is-pointed-dcpo
Pointed-DCPOs-subcat o ℓ .Subcat.is-hom f _ _ = is-strictly-scott-continuous f
Pointed-DCPOs-subcat o ℓ .Subcat.is-hom-prop f _ _ =
  is-strictly-scott-is-prop f
Pointed-DCPOs-subcat o ℓ .Subcat.is-hom-id {D} _ = strict-scott-id {D = D}
Pointed-DCPOs-subcat o ℓ .Subcat.is-hom-∘ {f = f} {g = g} f-strict g-strict =
  strict-scott-∘ f g f-strict g-strict

Pointed-DCPOs : ∀ o ℓ → Precategory (lsuc (o ⊔ ℓ)) (lsuc o ⊔ ℓ)
Pointed-DCPOs o ℓ = Subcategory (Pointed-DCPOs-subcat o ℓ)

Pointed-DCPOs-is-category : is-category (Pointed-DCPOs o ℓ)
Pointed-DCPOs-is-category =
  subcat-is-category DCPOs-is-category is-pointed-dcpo-is-prop
```

# Reasoning with pointed DCPOs

The following module re-exports facts about pointed DCPOs, and also
proves a bunch of useful lemma.s

<!--
```agda
module Pointed-DCPOs {o ℓ : Level} = Cat.Reasoning (Pointed-DCPOs o ℓ)

Pointed-dcpo : ∀ o ℓ → Type _
Pointed-dcpo o ℓ = Pointed-DCPOs.Ob {o} {ℓ}

Forget-Pointed-dcpo : Functor (Pointed-DCPOs o ℓ) (Sets o)
Forget-Pointed-dcpo = Forget-DCPO F∘ Forget-subcat
```
-->

```agda
module Pointed-dcpo {o ℓ} (D : Pointed-dcpo o ℓ) where
```

<details>
<summary>These proofs are all quite straightforward, so we omit them.
</summary>

```agda
  open is-directed-family

  dcpo : DCPO o ℓ
  dcpo = D .fst

  has-pointed : is-pointed-dcpo dcpo
  has-pointed = D .snd

  open DCPO dcpo public

  bottom : Ob
  bottom = Bottom.bot (D .snd)

  bottom≤x : ∀ x → bottom ≤ x
  bottom≤x = Bottom.has-bottom (D .snd)

  adjoin : ∀ {Ix : Type o} → (Ix → Ob) → Maybe Ix → Ob
  adjoin = extend-bottom dcpo has-pointed

  adjoin-directed
    : ∀ (s : Ix → Ob) → is-semidirected-family poset s
    → is-directed-family poset (adjoin s)
  adjoin-directed = extend-bottom-directed dcpo has-pointed

  lub→adjoin-lub : ∀ {s : Ix → Ob} {x : Ob} → is-lub poset s x → is-lub poset (adjoin s) x
  lub→adjoin-lub = lub→extend-bottom-lub dcpo has-pointed

  adjoin-lub→lub : ∀ {s : Ix → Ob} {x : Ob} → is-lub poset (adjoin s) x → is-lub poset s x
  adjoin-lub→lub = extend-bottom-lub→lub dcpo has-pointed

  -- We put these behind 'opaque' to prevent blow ups in goals.
  opaque
    ⋃-semi : (s : Ix → Ob) → is-semidirected-family poset s → Ob
    ⋃-semi s semidir = ⋃ (adjoin s) (adjoin-directed s semidir)

    ⋃-semi-lub
      : ∀ (s : Ix → Ob) (dir : is-semidirected-family poset s)
      → is-lub poset s (⋃-semi s dir)
    ⋃-semi-lub s dir = adjoin-lub→lub (⋃.has-lub (adjoin s) (adjoin-directed s dir))

    ⋃-semi-le
      : ∀ (s : Ix → Ob) (dir : is-semidirected-family poset s)
      → ∀ i → s i ≤ ⋃-semi s dir
    ⋃-semi-le s dir = is-lub.fam≤lub (⋃-semi-lub s dir)

    ⋃-semi-least
      : ∀ (s : Ix → Ob) (dir : is-semidirected-family poset s)
      → ∀ x → (∀ i → s i ≤ x) → ⋃-semi s dir ≤ x
    ⋃-semi-least s dir x le = is-lub.least (⋃-semi-lub s dir) x le

    ⋃-semi-pointwise
      : ∀ {Ix} {s s' : Ix → Ob}
      → {fam : is-semidirected-family poset s} {fam' : is-semidirected-family poset s'}
      → (∀ ix → s ix ≤ s' ix)
      → ⋃-semi s fam ≤ ⋃-semi s' fam'
    ⋃-semi-pointwise le = ⋃-pointwise λ where
      (just i) → le i
      nothing → bottom≤x _
```

</details>

However, we do call attention to one extremely useful fact: if $D$ is
a pointed DCPO, then it has least upper bounds of families indexed by
propositions.

```agda
  opaque
    ⋃-prop : ∀ {Ix : Type o} → (Ix → Ob) → is-prop Ix → Ob
    ⋃-prop s ix-prop = ⋃-semi s (prop-indexed→semidirected poset s ix-prop)

    ⋃-prop-le
      : ∀ (s : Ix → Ob) (p : is-prop Ix)
      → ∀ i → s i ≤ ⋃-prop s p
    ⋃-prop-le s p i = ⋃-semi-le _ _ i

    ⋃-prop-least
      : ∀ (s : Ix → Ob) (p : is-prop Ix)
      → ∀ x → (∀ i → s i ≤ x) → ⋃-prop s p ≤ x
    ⋃-prop-least s p = ⋃-semi-least _ _

    ⋃-prop-lub
      : ∀ (s : Ix → Ob) (p : is-prop Ix)
      → is-lub poset s (⋃-prop s p)
    ⋃-prop-lub s p = ⋃-semi-lub _ _
```

This allows us to reflect the truth value of a proposition into $D$.

```agda
  opaque
    ⋃-prop-false
      : ∀ (s : Ix → Ob) (p : is-prop Ix)
      → ¬ Ix → ⋃-prop s p ≡ bottom
    ⋃-prop-false s p ¬i =
      ≤-antisym
        (⋃-prop-least s p bottom (λ x → absurd (¬i x)))
        (bottom≤x _)

    ⋃-prop-true
      : ∀ (s : Ix → Ob) (p : is-prop Ix)
      → (i : Ix) → ⋃-prop s p ≡ s i
    ⋃-prop-true s p i =
      sym $ lub-of-const-fam (λ i j → ap s (p i j)) (⋃-prop-lub s p) i
```

We define a similar module for strictly Scott-continuous maps.

```agda
module Strict-scott {D E : Pointed-dcpo o ℓ} (f : Pointed-DCPOs.Hom D E) where
```

<details>
<summary>These proofs are all quite straightforward, so we omit them.
</summary>

```agda
  private
    module D = Pointed-dcpo D
    module E = Pointed-dcpo E

  scott : DCPOs.Hom D.dcpo E.dcpo
  scott = Subcat-hom.hom f

  open Scott scott public

  opaque
    pres-bottoms : ∀ x → is-bottom D.poset x → is-bottom E.poset (f # x)
    pres-bottoms = Subcat-hom.witness f

    pres-⊥ : f # D.bottom ≡ E.bottom
    pres-⊥ = bottom-unique E.poset (pres-bottoms D.bottom D.bottom≤x) E.bottom≤x

    pres-adjoin-lub
      : ∀ {s : Ix → D.Ob} {x : D.Ob}
      → is-semidirected-family D.poset s
      → is-lub D.poset (D.adjoin s) x → is-lub E.poset (E.adjoin (apply f ⊙ s)) (f # x)
    pres-adjoin-lub {s = s} {x = x} sdir x-lub .is-lub.fam≤lub (just i) =
      monotone (is-lub.fam≤lub x-lub (just i))
    pres-adjoin-lub {s = s} {x = x} sdir x-lub .is-lub.fam≤lub nothing =
      E.bottom≤x (f # x)
    pres-adjoin-lub {s = s} {x = x} sdir x-lub .is-lub.least y le =
      is-lub.least
        (pres-directed-lub (D.adjoin s) (D.adjoin-directed s sdir) x x-lub) y λ where
          (just i) → le (just i)
          nothing → pres-bottoms _ D.bottom≤x y

    pres-semidirected-lub
      : ∀ {Ix} (s : Ix → D.Ob) → is-semidirected-family D.poset s
      → ∀ x → is-lub D.poset s x → is-lub E.poset (apply f ⊙ s) (f # x)
    pres-semidirected-lub s sdir x x-lub =
      E.adjoin-lub→lub (pres-adjoin-lub sdir (D.lub→adjoin-lub x-lub))

    pres-⋃-prop
      : ∀ {Ix} (s : Ix → D.Ob) (p q : is-prop Ix)
      → f # (D.⋃-prop s p) ≡ E.⋃-prop (apply f ⊙ s) q
    pres-⋃-prop s p q =
      lub-unique
        (pres-semidirected-lub _
          (prop-indexed→semidirected D.poset s p) (D.⋃-prop s p) (D.⋃-prop-lub s p))
        (E.⋃-prop-lub _ _)

    bottom-bounded : ∀ {x y} → x D.≤ y → f # y ≡ E.bottom → f # x ≡ E.bottom
    bottom-bounded {x = x} {y = y} p y-bot =
      E.≤-antisym
        (f # x    E.≤⟨ monotone p ⟩
         f # y    E.=⟨ y-bot ⟩
         E.bottom E.≤∎)
        (E.bottom≤x _)
```
</details>

<!--
```agda
module _ {o ℓ} {D E : Pointed-dcpo o ℓ} where
  private
    module D = Pointed-dcpo D
    module E = Pointed-dcpo E
  open Total-hom
  open is-directed-family
```
-->

We also provide a handful of ways of constructing strictly Scott-continuous
maps. First, we note that if $f$ is monotonic and preserves the chosen
least upper bound of _semidirected_ families, then $f$ is strictly
Scott-continuous.

```agda
  to-strict-scott-⋃-semi
    : (f : D.Ob → E.Ob)
    → (∀ {x y} → x D.≤ y → f x E.≤ f y)
    → (∀ {Ix} (s : Ix → D.Ob) → (dir : is-semidirected-family D.poset s)
       → is-lub E.poset (f ⊙ s) (f (D.⋃-semi s dir)))
    → Pointed-DCPOs.Hom D E
  to-strict-scott-⋃-semi f monotone pres-⋃-semi =
    sub-hom (to-scott f monotone pres-⋃) pres-bot
    where
      pres-⋃
        : ∀ {Ix} (s : Ix → D.Ob) → (dir : is-directed-family D.poset s)
        → is-lub E.poset (f ⊙ s) (f (D.⋃ s dir))
      pres-⋃ s dir .is-lub.fam≤lub i =
        monotone $ D.⋃.fam≤lub _ _ i
      pres-⋃ s dir .is-lub.least y le =
        f (D.⋃ s dir)                      E.=⟨ ap f (lub-unique (D.⋃.has-lub _ _) (D.⋃-semi-lub s (dir .semidirected))) ⟩
        f (D.⋃-semi s (dir .semidirected)) E.≤⟨ pres-⋃-semi _ _ .is-lub.least y le ⟩
        y E.≤∎

      pres-bot : ∀ x → is-bottom D.poset x → is-bottom E.poset (f x)
      pres-bot x x-bot y =
        f x              E.≤⟨ monotone (x-bot _) ⟩
        f (D.⋃-semi _ _) E.≤⟨ is-lub.least (pres-⋃-semi (λ x → absurd (x .Lift.lower)) (λ ())) y (λ ()) ⟩
        y                E.≤∎
```

Next, if $f$ is monotonic, preserves chosen least upper bounds of directed
families, and preserves chosen bottoms, then $f$ is strictly
Scott-continuous.

```agda
  to-strict-scott-bottom
    : (f : D.Ob → E.Ob)
    → (∀ {x y} → x D.≤ y → f x E.≤ f y)
    → (∀ {Ix} (s : Ix → D.Ob) → (dir : is-directed-family D.poset s)
       → is-lub E.poset (f ⊙ s) (f (D.⋃ s dir)))
    → is-bottom E.poset (f D.bottom)
    → Pointed-DCPOs.Hom D E
  to-strict-scott-bottom f monotone pres-⋃ pres-bot =
    sub-hom (to-scott f monotone pres-⋃) λ x x-bot y →
      f x        E.≤⟨ monotone (x-bot _) ⟩
      f D.bottom E.≤⟨ pres-bot y ⟩
      y          E.≤∎
```

Finally, if $f$ preserves arbitrary least upper bounds of semidirected
families, then $f$ must be monotonic, and thus strictly Scott-continuous.

```agda
  to-strict-scott-semidirected
    : (f : D.Ob → E.Ob)
    → (∀ {Ix} (s : Ix → D.Ob) → (dir : is-semidirected-family D.poset s)
       → ∀ x → is-lub D.poset s x → is-lub E.poset (f ⊙ s) (f x))
    → Pointed-DCPOs.Hom D E
  to-strict-scott-semidirected f pres =
    sub-hom
      (to-scott-directed f
        (λ s dir x lub → pres s (is-directed-family.semidirected dir) x lub))
      (λ x x-bot y → is-lub.least
          (pres _ (λ x → absurd (x .Lift.lower)) x (lift-is-lub (is-bottom→is-lub D.poset {f = λ ()} x-bot)))
          y (λ ()))
```
