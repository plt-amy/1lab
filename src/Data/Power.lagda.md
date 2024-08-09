<!--
```agda
open import 1Lab.Prelude

open import Data.Sum
```
-->

```agda
module Data.Power where
```

<!--
```agda
private variable
  ℓ ℓ' : Level
  X Y : Type ℓ
```
-->

# Power sets {defines="power-set"}

The **power set** of a type $X$ is the collection of all maps from $X$
into the universe of `propositional types`{.Agda ident=Ω}. Since
the universe of all $n$-types is a $(n+1)$-type (by
`n-Type-is-hlevel`{.Agda}), and function types have the same h-level as
their codomain (by `fun-is-hlevel`{.Agda}), the power set of a type $X$ is
always `a set`{.Agda ident=is-set}. We denote the power set of $X$ by
$\bb{P}(X)$.

```agda
ℙ : Type ℓ → Type ℓ
ℙ X = X → Ω

ℙ-is-set : is-set (ℙ X)
ℙ-is-set = hlevel 2
```

The **membership** relation is defined by applying the predicate and
projecting the underlying type of the proposition: We say that $x$ is an
element of $P$ if $P(x)$ is inhabited.

```agda
_ : ∀ {x : X} {P : ℙ X} → x ∈ P ≡ ∣ P x ∣
_ = refl
```

The **subset** relation is defined as is done traditionally: If $x \in
X$ implies $x \in Y$, for $X, Y : \bb{P}(T)$, then $X \subseteq Y$.

```agda
_ : {X : Type ℓ} {S T : ℙ X} → (S ⊆ T) ≡ ((x : X) → x ∈ S → x ∈ T)
_ = refl
```

By function and propositional extensionality, two subsets of $X$ are
equal when they contain the same elements, i.e., they assign identical
propositions to each inhabitant of $X$.

```agda
ℙ-ext : {A B : ℙ X}
      → A ⊆ B → B ⊆ A → A ≡ B
ℙ-ext {A = A} {B = B} A⊆B B⊂A = funext λ x →
  Ω-ua (A⊆B x) (B⊂A x)
```

## Lattice structure

The type $\bb{P}(X)$ has a lattice structure, with the order given by
`subset inclusion`{.Agda ident=⊆}. We call the meets
**`intersections`{.Agda ident=_∩_}** and the joins **`unions`{.Agda
ident=_∪_}**.

```agda
maximal : ℙ X
maximal _ = ⊤Ω

minimal : ℙ X
minimal _ = ⊥Ω

_∩_ : ℙ X → ℙ X → ℙ X
(A ∩ B) x = A x ∧Ω B x
```

<!--
```agda
∩-⊆
  : ∀ {U V W : ℙ X}
  → U ⊆ V → U ⊆ W
  → U ⊆ V ∩ W
∩-⊆ U⊆V V⊆W x x∈U =
  (U⊆V x x∈U) , (V⊆W x x∈U)

∩-⊆l
  : ∀ (U V : ℙ X)
  → U ∩ V ⊆ U
∩-⊆l _ _ x (x∈U , x∈V) = x∈U

∩-⊆r
  : ∀ (U V : ℙ X)
  → U ∩ V ⊆ V
∩-⊆r _ _ x (x∈U , x∈V) = x∈V
```
-->

<!--
```agda
_ = ∥_∥
_ = _⊎_
```
-->

```agda
singleton : X → ℙ X
singleton x y = elΩ (x ≡ y)
```

Note that in the definition of `union`{.Agda ident=_∪_}, we must
`truncate`{.Agda ident=∥_∥} the `coproduct`{.Agda ident=_⊎_}, since there
is nothing which guarantees that A and B are disjoint subsets.

```agda
_∪_ : ℙ X → ℙ X → ℙ X
(A ∪ B) x = A x ∨Ω B x

infixr 32 _∩_
infixr 31 _∪_
```

We can also take unions of $I$-indexed families of sets $A_i$, as well
as unions of subsets of the power set.

```agda
⋃ : ∀ {κ : Level} {I : Type κ} → (I → ℙ X) → ℙ X
⋃ {I = I} A x = ∃Ω[ i ∈ I ] A i x

⋃ˢ : ℙ (ℙ X) → ℙ X
⋃ˢ {X = X} P = ⋃ {I = Σ[ U ∈ ℙ X ] U ∈ P} fst
```

<!--
```agda
⋃-⊆
  : ∀ {κ} {I : Type κ}
  → (Uᵢ : I → ℙ X) (V : ℙ X)
  → (∀ i → Uᵢ i ⊆ V)
  → ⋃ Uᵢ ⊆ V
⋃-⊆ Uᵢ V Uᵢ⊆V x =
  rec! (λ i → Uᵢ⊆V i x)

⋃ˢ-⊆
  : (S : ℙ (ℙ X)) (V : ℙ X)
  → (∀ (U : ℙ X) → U ∈ S → U ⊆ V)
  → ⋃ˢ S ⊆ V
⋃ˢ-⊆ S V U⊆V x =
  rec! λ U U∈S → U⊆V U U∈S x

⋃-inc
  : ∀ {κ} {I : Type κ}
  → (Uᵢ : I → ℙ X)
  → ∀ i → Uᵢ i ⊆ ⋃ Uᵢ
⋃-inc Uᵢ i x x∈Uᵢ =
  pure (i , x∈Uᵢ)

⋃ˢ-inc
  : (S : ℙ (ℙ X)) (U : ℙ X)
  → U ∈ S
  → U ⊆ ⋃ˢ S
⋃ˢ-inc S U U∈S x x∈U =
  pure ((U , U∈S) , x∈U)

⋃-Σ
  : ∀ {κ κ'} {I : Type κ} {J : I → Type κ'}
  → (Aᵢⱼ : Σ[ i ∈ I ] (J i) → ℙ X)
  → ⋃ Aᵢⱼ ≡ ⋃ λ i → ⋃ λ j → Aᵢⱼ (i , j)
⋃-Σ Aᵢⱼ =
  ℙ-ext
    (λ x → rec! λ i j x∈Aᵢⱼ → pure (i , (pure (j , x∈Aᵢⱼ))))
    (λ x → rec! λ i j x∈Aᵢⱼ → pure ((i , j) , x∈Aᵢⱼ))
```
-->

Note that the union of a family of sets $A_i$ is equal to the union
of the fibres of $A_i$.

```agda
⋃-fibre
  : ∀ {κ} {I : Type κ}
  → (Aᵢ : I → ℙ X)
  → ⋃ˢ (λ A → elΩ (fibre Aᵢ A)) ≡ ⋃ Aᵢ
⋃-fibre Aᵢ =
  ℙ-ext
    (λ x → rec! λ A i Aᵢ=A x∈A → pure (i , (subst (λ A → ∣ A x ∣) (sym Aᵢ=A) x∈A)))
    (λ x → rec! λ i x∈Aᵢ → pure ((Aᵢ i , pure (i , refl)) , x∈Aᵢ))
```

Moreover, the union of an empty family of sets is equal to the empty
set.

```agda
⋃-minimal
  : (A : ⊥ → ℙ X)
  → ⋃ {I = ⊥} A ≡ minimal
⋃-minimal _ =
  ℙ-ext (λ _ → rec! λ ff x∈A → ff) (λ _ ff → absurd ff)
```

# Images of subsets {defines="preimage direct-image"}

Let $f : X \to Y$ be a function. the **preimage** of a subset $U : \power{Y}$
is the subset $f^{-1}(U) : \power{X}$ of all $x : X$ such that $f(x) \in U$.

```agda
Preimage : (X → Y) → ℙ Y → ℙ X
Preimage f A = A ∘ f
```

Conversely, the **direct image** of a subset $U : \power{X}$ is the
subset $f(U) : \power{X}$ of all $y : Y$ such that there exists an
$x \in U$ with $f(x) = y$.

```agda
Direct-image : (X → Y) → ℙ X → ℙ Y
Direct-image {X = X} f A y = elΩ (Σ[ x ∈ X ] (x ∈ A × (f x ≡ y)))
```

We can relate preimages and direct images by observing that for every
$U : \power{X}$ and $V : \power{Y}$, $f(U) \subseteq V$ if and only if
$U \subseteq f^{-1}(V)$. In more categorical terms, preimages and
direct images form and [[adjunction]] between $\power{X}$ and $\power{Y}$.

```agda
direct-image-⊆→preimage-⊆
  : ∀ {f : X → Y}
  → (U : ℙ X) (V : ℙ Y)
  → Direct-image f U ⊆ V → U ⊆ Preimage f V
direct-image-⊆→preimage-⊆ {f = f} U V f[U]⊆V x x∈U =
  f[U]⊆V (f x) (pure (x , x∈U , refl))

preimage-⊆→direct-image-⊆
  : ∀ {f : X → Y}
  → (U : ℙ X) (V : ℙ Y)
  → U ⊆ Preimage f V → Direct-image f U ⊆ V
preimage-⊆→direct-image-⊆ U V U⊆f⁻¹[V] y =
  rec! λ x x∈U f[x]=y →
    subst (λ y → ∣ V y ∣) f[x]=y (U⊆f⁻¹[V] x x∈U)
```

<!--
```agda
⋂ : ∀ {κ : Level} {I : Type κ} → (I → ℙ X) → ℙ X
⋂ {I = I} A x = ∀Ω[ i ∈ I ] A i x

_ᶜ : ℙ X → ℙ X
(A ᶜ) x = ¬Ω (A x)

≡→⊆
  : ∀ {U V : ℙ X}
  → U ≡ V → U ⊆ V
≡→⊆ {V = V} p x x∈U =
  subst (λ U → ∣ U x ∣) p x∈U

≡→⊇
  : ∀ {U V : ℙ X}
  → U ≡ V → V ⊆ U
≡→⊇ p = ≡→⊆ (sym p)
```
-->
