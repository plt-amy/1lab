<!--
```agda
open import Cat.Displayed.Univalence.Thin
open import Cat.Functor.Subcategory
open import Cat.Displayed.Total
open import Cat.Functor.Adjoint
open import Cat.Prelude

open import Data.Partial.Properties
open import Data.Partial.Base
open import Data.Sum

open import Order.Instances.Discrete
open import Order.Diagram.Bottom
open import Order.DCPO.Pointed
open import Order.Diagram.Lub
open import Order.Base
open import Order.DCPO
```
-->

```agda
module Order.DCPO.Free where
```

<!--
```agda
private variable
  o o' ℓ : Level
  A B C : Type ℓ

open is-directed-family
open Lub

open Functor
open _=>_
open _⊣_
```
-->

# Free DCPOs

The [discrete poset] on a set $A$ is a DCPO. To see this, note that
every semi-directed family $f : I \to A$ in a discrete poset is constant.
Furthermore, $f$ is directed, so it is merely inhabited.

[discrete poset]: Order.Instances.Discrete.html

```agda
Disc-is-dcpo : ∀ {ℓ} {A : Set ℓ} → is-dcpo (Disc A)
Disc-is-dcpo {A = A} .is-dcpo.directed-lubs {Ix = Ix} f dir =
  const-inhabited-fam→lub disc-fam-const (dir .elt)
  where
    disc-fam-const : ∀ i j → f i ≡ f j
    disc-fam-const i j =
      ∥-∥-rec! (λ (k , p , q) → p ∙ sym q)
        (dir .semidirected i j)

Disc-dcpo : (A : Set ℓ) → DCPO ℓ ℓ
Disc-dcpo A = Disc A , Disc-is-dcpo
```

This extends to a functor from $\Sets$ to the category of DCPOs.

```agda
Free-DCPO : ∀ {ℓ} → Functor (Sets ℓ) (DCPOs ℓ ℓ)
Free-DCPO .F₀ = Disc-dcpo
Free-DCPO .F₁ f =
  to-scott-directed f λ s dir x x-lub →
  const-inhabited-fam→is-lub
    (λ ix → ap f (disc-is-lub→const x-lub ix))
    (dir .elt)
Free-DCPO .F-id = trivial!
Free-DCPO .F-∘ _ _ = trivial!
```

Furthermore, this functor is left adjoint to the forgetful functor
to $\Sets$.

```agda
Free-DCPO⊣Forget-DCPO : ∀ {ℓ} → Free-DCPO {ℓ} ⊣ Forget-DCPO
Free-DCPO⊣Forget-DCPO .unit .η _ x = x
Free-DCPO⊣Forget-DCPO .unit .is-natural _ _ _ = refl
Free-DCPO⊣Forget-DCPO .counit .η D =
  to-scott-directed (λ x → x) λ s dir x x-lub → λ where
    .is-lub.fam≤lub i → ≤-refl' (disc-is-lub→const x-lub i)
    .is-lub.least y le →
      ∥-∥-rec ≤-thin
        (λ i →
          x   =˘⟨ disc-is-lub→const x-lub i ⟩
          s i ≤⟨ le i ⟩
          y   ≤∎)
        (dir .elt)
   where open DCPO D
Free-DCPO⊣Forget-DCPO .counit .is-natural x y f = trivial!
Free-DCPO⊣Forget-DCPO .zig = trivial!
Free-DCPO⊣Forget-DCPO .zag = refl
```

# Free pointed DCPOs {defines="free-pointed-DCPO"}

The purpose of this section is to establish that the free [[pointed
DCPO]] on a [[set]] $A$ is given by its [[partial elements]] $\zap A$.
We have already constructed the order we will use, the [[information
ordering]], and established some of its [basic order-theoretic
properties], so that we immediately get a [[poset]] of partial elements:

[basic order-theoretic properties]: Data.Partial.Properties.html

```agda
Parts : (A : Set ℓ) → Poset ℓ ℓ
Parts A .Poset.Ob        = ↯ ∣ A ∣
Parts A .Poset._≤_       = _⊑_
Parts A .Poset.≤-thin    = ⊑-thin (A .is-tr)
Parts A .Poset.≤-refl    = ⊑-refl
Parts A .Poset.≤-trans   = ⊑-trans
Parts A .Poset.≤-antisym = ⊑-antisym
```

Unfortunately, the hardest two parts of the construction remain:

a. We must show that $\zap A$ has [[least upper bounds]] for all
[[semidirected families]], i.e., that it is actually a [[DCPO]];

b. We must show that this construction is actually free, meaning that
every map $A \to B$ to a pointed DCPO extends uniquely to a strictly
Scott-continuous $\zap A \to B$.

We will proceed in this order.

## Directed joins of partial elements

```agda
⊑-lub
  : {Ix : Type ℓ} (aset : is-set A) (s : Ix → ↯ A)
  → (semi : ∀ i j → ∃[ k ∈ Ix ] (s i ⊑ s k × s j ⊑ s k))
  → ↯ A
```

Suppose that $s_i : \zap A$ is a semidirected family of partial elements
--- which, recall, means that for each $i, j : I$, we can [[merely]]
find $k : I$ satisfying $s_i \lsq s_k$ and $s_j \lsq s_k$. We decree
that the join $\bigsqcup_i s_i$ is defined whenever there exists $i : I$
such that $s_i$ is defined.

```agda
⊑-lub {Ix = Ix} set s dir .def = elΩ (Σ[ i ∈ Ix ] ⌞ s i ⌟)
```

Next, we need to construct an element of $A$, under the assumption that
there exists such an $i$. The obvious move is to use the value $s_i$
itself. However, we only _[[merely]]_ have such an $i$, and we're not
mapping into a proposition --- we're mapping into a [[_set_]]. But
that's not a major impediment: we're allowed to make this choice, as
long as we show that the function $s_{-}$ is _constant_.

```agda
⊑-lub {Ix = Ix} set s dir .elt =
  □-rec-set (λ (ix , def) → s ix .elt def) (λ p q i →
    is-const p q i .elt $
    is-prop→pathp (λ i → is-const p q i .def .is-tr) (p .snd) (q .snd) i) set
  where abstract
```

So imagine that we have two indices $i, j$ with $s_i$ and $s_j$ both
defined. We must show that $s_i = s_j$. Since $s$ is semidirected, and
we're showing a proposition, we may assume that there is some $s_k$
satisfying $s_i \lsq s_k$ and $s_j \lsq s_k$. We then compute:

```agda
    is-const
      : ∀ (p q : Σ[ i ∈ Ix ] ⌞ s i ⌟)
      → s (p .fst) ≡ s (q .fst)
    is-const (i , si) (j , sj) = ∥-∥-proj (↯-is-hlevel 0 set _ _) $ do
      (k , p , q) ← dir i j
      pure $ part-ext (λ _ → sj) (λ _ → si) λ si sj →
        s i .elt _   ≡˘⟨ p .refines si ⟩
        s k .elt _   ≡⟨ ↯-indep (s k) ⟩
        s k .elt _   ≡⟨ q .refines sj ⟩
        s j .elt _   ∎
```

After having constructed the element, we're still left with proving that
this is actually a least upper bound. This turns out to be pretty
straightforward, so we present the solution without further comments:

<!--
```agda
module
  _ {Ix : Type ℓ} {set : is-set A} {s : Ix → ↯ A}
    {dir : ∀ i j → ∃[ k ∈ Ix ] (s i ⊑ s k × s j ⊑ s k)}
  where
```
-->

```agda
  ⊑-lub-le : ∀ i → s i ⊑ ⊑-lub set s dir
  ⊑-lub-le i .implies si = inc (i , si)
  ⊑-lub-le i .refines si = refl

  ⊑-lub-least
    : ∀ x → (∀ i → s i ⊑ x) → ⊑-lub set s dir ⊑ x
  ⊑-lub-least x le .implies = □-rec! λ (i , si) →
    le i .implies si
  ⊑-lub-least x le .refines = □-elim (λ _ → set _ _) λ (i , si) →
    le i .refines si
```

<!--
```agda
open is-dcpo
open is-lub
open Bottom
open Lub
```
-->

```agda
Parts-is-dcpo : ∀ {A : Set ℓ} → is-dcpo (Parts A)
Parts-is-dcpo {A = A} .directed-lubs s dir .lub =
  ⊑-lub (A .is-tr) s (dir .semidirected)
Parts-is-dcpo {A = A} .directed-lubs s dir .has-lub .fam≤lub = ⊑-lub-le
Parts-is-dcpo {A = A} .directed-lubs s dir .has-lub .least = ⊑-lub-least

Parts-dcpo : (A : Set ℓ) → DCPO ℓ ℓ
Parts-dcpo A = Parts A , Parts-is-dcpo
```

Furthermore, it's a *pointed* DCPO, since we additionally have a bottom
element.

```agda
Parts-is-pointed-dcpo : ∀ {A : Set ℓ} → is-pointed-dcpo (Parts-dcpo A)
Parts-is-pointed-dcpo .bot          = never
Parts-is-pointed-dcpo .has-bottom _ = never-⊑

Parts-pointed-dcpo : ∀ (A : Set ℓ) → Pointed-dcpo ℓ ℓ
Parts-pointed-dcpo A = Parts-dcpo A , Parts-is-pointed-dcpo
```

Finally, we note that the functorial action of the partiality monad
preserves these directed joins. Since it's valued in strict
Scott-continuous maps, this action extends to a proper functor from the
category $\Sets$ to the category of pointed dcpos.

```agda
part-map-lub
  : {Ix : Type ℓ} {A : Set o} {B : Set o'} {s : Ix → ↯ ∣ A ∣}
  → {dir : ∀ i j → ∃[ k ∈ Ix ] (s i ⊑ s k × s j ⊑ s k)}
  → (f : ∣ A ∣ → ∣ B ∣)
  → is-lub (Parts B) (part-map f ⊙ s) (part-map f (⊑-lub (A .is-tr) s dir))
part-map-lub f .fam≤lub i = part-map-⊑ (⊑-lub-le i)
part-map-lub f .least y le .implies =
  □-rec! λ (i , si) → le i .implies si
part-map-lub {B = B} f .least y le .refines =
  □-elim (λ _ → B .is-tr _ _) λ (i , si) → le i .refines si

Free-Pointed-dcpo : Functor (Sets ℓ) (Pointed-DCPOs ℓ ℓ)
Free-Pointed-dcpo .F₀ A = Parts-pointed-dcpo A
Free-Pointed-dcpo .F₁ {x = A} f = to-strict-scott-bottom
  (part-map f) (part-map-⊑)
  (λ _ _ → part-map-lub {A = A} f)
  (λ _ → part-map-never)
Free-Pointed-dcpo .F-id = ext (part-map-id $_)
Free-Pointed-dcpo .F-∘ f g = ext (part-map-∘ f g $_)
```

<!--
```agda
module _ (D : Pointed-dcpo o ℓ) where
  open Pointed-dcpo D
```
-->

## The universal property

It remains to show that this functor is actually a [[left adjoint]]. We
have already constructed the adjunction unit: it is the map
`always`{.Agda} which embeds $A$ into $\zap A$. We turn to defining the
counit. Since every pointed dcpo admits joins indexed by
[[propositions]], given a $x : \zap D$, we can define $\epsilon x : D$ to be
the join

$$
\bigsqcup_{x\ \text{is defined}} x(-)
$$.

```agda
  part-counit : ↯ Ob → Ob
  part-counit x = ⋃-prop (x .elt ⊙ Lift.lower) def-prop where abstract
    def-prop : is-prop (Lift o ⌞ x ⌟)
    def-prop = hlevel!
```

We can characterise the behaviour of this definition as though it were
defined by cases: if $x$ is defined, then this simply yields its value.
And if $x$ is undefined, then this is the bottom element.

```agda
  part-counit-elt : (x : ↯ Ob) (p : ⌞ x ⌟) → part-counit x ≡ x .elt p
  part-counit-elt x p = ≤-antisym
    (⋃-prop-least _ _ _ λ (lift p') → ≤-refl' (↯-indep x))
    (⋃-prop-le _ _ (lift p))

  part-counit-¬elt : (x : ↯ Ob) → (⌞ x ⌟ → ⊥) → part-counit x ≡ bottom
  part-counit-¬elt x ¬def = ≤-antisym
    (⋃-prop-least _ _ _ (λ p → absurd (¬def (Lift.lower p))))
    (bottom≤x _)
```

The following three properties are fundamental: the counit

1. preserves the information order; and
2. preserves directed joins; and
3. preserves the bottom element.

```agda
  part-counit-⊑ : ∀ {x y} → x ⊑ y → part-counit x ≤ part-counit y
  part-counit-lub
    : ∀ {Ix} s (sdir : is-semidirected-family (Parts set) {Ix} s)
    → is-lub poset (part-counit ⊙ s) (part-counit (⊑-lub (set .is-tr) s sdir))
  part-counit-never : ∀ x → part-counit never ≤ x
```

<details>
<summary>The proofs here are simply calculations. We leave them for the
curious reader.</summary>

```agda
  part-counit-⊑ {x = x} {y = y} p = ⋃-prop-least _ _ (part-counit y) λ (lift i) →
    x .elt i                       =˘⟨ p .refines i ⟩
    y .elt (p .implies i)          ≤⟨ ⋃-prop-le _ _ (lift (p .implies i)) ⟩
    ⋃-prop (y .elt ⊙ Lift.lower) _ ≤∎

  part-counit-lub s sdir .is-lub.fam≤lub i =
    ⋃-prop-least _ _ _ λ (lift p) →
    ⋃-prop-le _ _ (lift (inc (i , p)))
  part-counit-lub {Ix = Ix} s sdir .is-lub.least y le = ⋃-prop-least _ _ _ $
    λ (lift p) → □-elim (λ p → ≤-thin {x = ⊑-lub _ s sdir .elt p}) (λ (i , si) →
      s i .elt si ≤⟨ ⋃-prop-le _ _ (lift si) ⟩
      ⋃-prop _ _  ≤⟨ le i ⟩
      y           ≤∎) p

  part-counit-never x = ⋃-prop-least _ _ x (λ ())
```

</details>

We can tie this all together to obtain the desired adjunction.

```agda
Free-Pointed-dcpo⊣Forget-Pointed-dcpo
  : ∀ {ℓ} → Free-Pointed-dcpo {ℓ} ⊣ Forget-Pointed-dcpo
Free-Pointed-dcpo⊣Forget-Pointed-dcpo .unit .η A x = always x
Free-Pointed-dcpo⊣Forget-Pointed-dcpo .unit .is-natural x y f = ext λ _ →
  sym (always-natural f)

Free-Pointed-dcpo⊣Forget-Pointed-dcpo .counit .η D = to-strict-scott-bottom
  (part-counit D)
  (part-counit-⊑ D)
  (λ s dir → part-counit-lub D s (dir .semidirected))
  (part-counit-never D)
Free-Pointed-dcpo⊣Forget-Pointed-dcpo .counit .is-natural D E f = ext λ x →
  sym $ Strict-scott.pres-⋃-prop f _ _ _

Free-Pointed-dcpo⊣Forget-Pointed-dcpo .zig {A} = ext λ x → part-ext
  (A?.⋃-prop-least _ _ x (λ p → always-⊒ (Lift.lower p , refl)) .implies)
  (λ p → A?.⋃-prop-le _ _ (lift p) .implies tt)
  (λ p q →
    sym (A?.⋃-prop-least _ _ x (λ p → always-⊒ (Lift.lower p , refl)) .refines p)
    ∙ ↯-indep x)
  where module A? = Pointed-dcpo (Parts-pointed-dcpo A)

Free-Pointed-dcpo⊣Forget-Pointed-dcpo .zag {B} = ext λ x →
  sym $ lub-of-const-fam (λ _ _ → refl) (B.⋃-prop-lub _ _ ) (lift tt)
  where module B = Pointed-dcpo B
```
