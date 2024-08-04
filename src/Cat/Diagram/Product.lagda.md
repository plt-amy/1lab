<!--
```agda
open import Cat.Instances.Product
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Diagram.Product where
```

<!--
```agda
module _ {o ℓ} (C : Precategory o ℓ) where
  open Cat.Reasoning C
```
-->

# Products

:::{.definition #product}
The **product** $P$ of two objects $A$ and $B$, if it exists, is the
smallest object equipped with "projection" maps $P \to A$ and $P \to B$.
This situation can be visualised by putting the data of a product into a
commutative diagram, as the one below: To express that $P$ is the
_smallest_ object with projections to $A$ and $B$, we ask that any other
object $Q$ with projections through $A$ and $B$ factors uniquely through
$P$:
:::

~~~{.quiver}
\[\begin{tikzcd}
  & Q \\
  A & P & B
  \arrow[from=2-2, to=2-1]
  \arrow[from=2-2, to=2-3]
  \arrow[from=1-2, to=2-1]
  \arrow["{\exists!}"', dashed, from=1-2, to=2-2]
  \arrow[from=1-2, to=2-3]
\end{tikzcd}\]
~~~

In the sense that [[(univalent) categories|univalent category]]
generalise posets, the product of $A$ and $B$ --- if it exists ---
generalises the binary meet $A \wedge B$. Since products are
[unique](#uniqueness) when they exist, we may safely denote any product
of $A$ and $B$ by $A \times B$.

For a diagram $A \ot A \times B \to B$ to be a product diagram, it must
be able to cough up an arrow $Q \to P$ given the data of another span $A
\ot Q \to B$, which must not only fit into the diagram above but be
unique among the arrows that do so.

This factoring is called the **pairing** of the arrows $f : Q \to A$ and
$g : Q \to B$, since in the special case where $Q$ is the [[terminal
object]] (hence the two arrows are global elements of $A$ resp. $B$),
the pairing $\langle f, g \rangle$ is a global element of the product $A
\times B$.

[terminal object]: Cat.Diagram.Terminal.html

```agda
  record is-product {A B P} (π₁ : Hom P A) (π₂ : Hom P B) : Type (o ⊔ ℓ) where
    field
      ⟨_,_⟩ : ∀ {Q} (p1 : Hom Q A) (p2 : Hom Q B) → Hom Q P
      π₁∘⟨⟩ : ∀ {Q} {p1 : Hom Q _} {p2} → π₁ ∘ ⟨ p1 , p2 ⟩ ≡ p1
      π₂∘⟨⟩ : ∀ {Q} {p1 : Hom Q _} {p2} → π₂ ∘ ⟨ p1 , p2 ⟩ ≡ p2

      unique : ∀ {Q} {p1 : Hom Q A} {p2}
             → {other : Hom Q P}
             → π₁ ∘ other ≡ p1
             → π₂ ∘ other ≡ p2
             → other ≡ ⟨ p1 , p2 ⟩

    unique₂ : ∀ {Q} {pr1 : Hom Q A} {pr2}
            → ∀ {o1} (p1 : π₁ ∘ o1 ≡ pr1) (q1 : π₂ ∘ o1 ≡ pr2)
            → ∀ {o2} (p2 : π₁ ∘ o2 ≡ pr1) (q2 : π₂ ∘ o2 ≡ pr2)
            → o1 ≡ o2
    unique₂ p1 q1 p2 q2 = unique p1 q1 ∙ sym (unique p2 q2)

    ⟨⟩∘ : ∀ {Q R} {p1 : Hom Q A} {p2 : Hom Q B} (f : Hom R Q)
        → ⟨ p1 , p2 ⟩ ∘ f ≡ ⟨ p1 ∘ f , p2 ∘ f ⟩
    ⟨⟩∘ f = unique (pulll π₁∘⟨⟩) (pulll π₂∘⟨⟩)

    ⟨⟩-η : ⟨ π₁ , π₂ ⟩ ≡ id
    ⟨⟩-η = sym $ unique (idr _) (idr _)
```

A product of $A$ and $B$ is an explicit choice of product diagram:

```agda
  record Product (A B : Ob) : Type (o ⊔ ℓ) where
    no-eta-equality
    field
      apex : Ob
      π₁ : Hom apex A
      π₂ : Hom apex B
      has-is-product : is-product π₁ π₂

    open is-product has-is-product public
```

## Uniqueness {defines="uniqueness-of-products"}

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} where
  open Cat.Reasoning C
  open Product hiding (⟨_,_⟩ ; π₁ ; π₂ ; ⟨⟩∘)
  private variable
    A B a b c d : Ob
```
-->

Products, when they exist, are unique. It's easiest to see this with a
diagrammatic argument: If we have product diagrams $A \ot P \to B$ and
$A \ot P' \to B$, we can fit them into a "commutative diamond" like the
one below:

~~~{.quiver}
\[\begin{tikzcd}
  & P \\
  A && B \\
  & {P'}
  \arrow[from=3-2, to=2-3]
  \arrow[from=1-2, to=2-3]
  \arrow[from=1-2, to=2-1]
  \arrow[from=3-2, to=2-1]
\end{tikzcd}\]
~~~

Since both $P$ and $P'$ are products, we know that the dashed arrows in
the diagram below exist, so the overall diagram commutes: hence we have
an isomorphism $P \cong P'$.

~~~{.quiver}
\[\begin{tikzcd}
  & P \\
  A && B \\
  & {P'}
  \arrow[from=3-2, to=2-3]
  \arrow[from=1-2, to=2-3]
  \arrow[from=1-2, to=2-1]
  \arrow[from=3-2, to=2-1]
  \arrow["{\exists!}"', shift right=1, dashed, from=1-2, to=3-2]
  \arrow["{\exists!}"', shift right=1, dashed, from=3-2, to=1-2]
\end{tikzcd}\]
~~~

We construct the map $P \to P'$ as the pairing of the projections from
$P$, and symmetrically for $P' \to P$.

```agda
  ×-Unique : (p1 p2 : Product C A B) → apex p1 ≅ apex p2
  ×-Unique p1 p2 = make-iso p1→p2 p2→p1 p1→p2→p1 p2→p1→p2
    where
      module p1 = Product p1
      module p2 = Product p2

      p1→p2 : Hom (apex p1) (apex p2)
      p1→p2 = p2.⟨ p1.π₁ , p1.π₂ ⟩

      p2→p1 : Hom (apex p2) (apex p1)
      p2→p1 = p1.⟨ p2.π₁ , p2.π₂ ⟩
```

These are unique because they are maps into products which commute with
the projections.

```agda
      p1→p2→p1 : p1→p2 ∘ p2→p1 ≡ id
      p1→p2→p1 =
        p2.unique₂
          (assoc _ _ _ ·· ap (_∘ _) p2.π₁∘⟨⟩ ·· p1.π₁∘⟨⟩)
          (assoc _ _ _ ·· ap (_∘ _) p2.π₂∘⟨⟩ ·· p1.π₂∘⟨⟩)
          (idr _) (idr _)

      p2→p1→p2 : p2→p1 ∘ p1→p2 ≡ id
      p2→p1→p2 =
        p1.unique₂
          (assoc _ _ _ ·· ap (_∘ _) p1.π₁∘⟨⟩ ·· p2.π₁∘⟨⟩)
          (assoc _ _ _ ·· ap (_∘ _) p1.π₂∘⟨⟩ ·· p2.π₂∘⟨⟩)
          (idr _) (idr _)

  is-product-iso
    : ∀ {A A' B B' P} {π₁ : Hom P A} {π₂ : Hom P B}
        {f : Hom A A'} {g : Hom B B'}
    → is-invertible f
    → is-invertible g
    → is-product C π₁ π₂
    → is-product C (f ∘ π₁) (g ∘ π₂)
  is-product-iso f-iso g-iso prod = prod' where
    module fi = is-invertible f-iso
    module gi = is-invertible g-iso

    open is-product
    prod' : is-product _ _ _
    prod' .⟨_,_⟩ qa qb = prod .⟨_,_⟩ (fi.inv ∘ qa) (gi.inv ∘ qb)
    prod' .π₁∘⟨⟩ = pullr (prod .π₁∘⟨⟩) ∙ cancell fi.invl
    prod' .π₂∘⟨⟩ = pullr (prod .π₂∘⟨⟩) ∙ cancell gi.invl
    prod' .unique p q = prod .unique
      (sym (ap (_ ∘_) (sym p) ∙ pulll (cancell fi.invr)))
      (sym (ap (_ ∘_) (sym q) ∙ pulll (cancell gi.invr)))

  is-product-iso-apex
    : ∀ {A B P P'} {π₁ : Hom P A} {π₂ : Hom P B}
        {π₁' : Hom P' A} {π₂' : Hom P' B}
        {f : Hom P' P}
    → is-invertible f
    → π₁ ∘ f ≡ π₁'
    → π₂ ∘ f ≡ π₂'
    → is-product C π₁ π₂
    → is-product C π₁' π₂'
  is-product-iso-apex {f = f} f-iso f-π₁ f-π₂ prod = prod' where
    module fi = is-invertible f-iso

    open is-product
    prod' : is-product _ _ _
    prod' .⟨_,_⟩ qa qb = fi.inv ∘ prod .⟨_,_⟩ qa qb
    prod' .π₁∘⟨⟩ = pulll (rswizzle (sym f-π₁) fi.invl) ∙ prod .π₁∘⟨⟩
    prod' .π₂∘⟨⟩ = pulll (rswizzle (sym f-π₂) fi.invl) ∙ prod .π₂∘⟨⟩
    prod' .unique p q = sym $ lswizzle
      (sym (prod .unique (pulll f-π₁ ∙ p) (pulll f-π₂ ∙ q))) fi.invr
```

# Categories with all binary products

Categories with all binary products are quite common, so we provide
an API for working with them. In order to get better printing in goals,
we define an unnested record where all operations are top-level fields;
this means that goals willl print as `⟨ f , g ⟩` instead of
`is-product.⟨_,_⟩ (product A B) f g`.

```agda
record Binary-products {o ℓ} (C : Precategory o ℓ) : Type (o ⊔ ℓ) where
  no-eta-equality
  open Cat.Reasoning C
  field
    _⊗₀_ : Ob → Ob → Ob
    π₁ : ∀ {A B} → Hom (A ⊗₀ B) A
    π₂ : ∀ {A B} → Hom (A ⊗₀ B) B
    ⟨_,_⟩ : ∀ {A B X} → Hom X A → Hom X B → Hom X (A ⊗₀ B)
    π₁∘⟨⟩ : ∀ {A B X} {p1 : Hom X A} {p2 : Hom X B} → π₁ ∘ ⟨ p1 , p2 ⟩ ≡ p1
    π₂∘⟨⟩ : ∀ {A B X} {p1 : Hom X A} {p2 : Hom X B} → π₂ ∘ ⟨ p1 , p2 ⟩ ≡ p2
    ⟨⟩-unique
      : ∀ {A B X}
      → {p1 : Hom X A} {p2 : Hom X B}
      → {other : Hom X (A ⊗₀ B)}
      → π₁ ∘ other ≡ p1
      → π₂ ∘ other ≡ p2
      → other ≡ ⟨ p1 , p2 ⟩

  infixr 7 _⊗₀_
  infix 50 _⊗₁_
```

<!--
```agda
  open Functor

  product : ∀ A B → Product C A B
  product A B .Product.apex = A ⊗₀ B
  product A B .Product.π₁ = π₁
  product A B .Product.π₂ = π₂
  product A B .Product.has-is-product .is-product.⟨_,_⟩ = ⟨_,_⟩
  product A B .Product.has-is-product .is-product.π₁∘⟨⟩ = π₁∘⟨⟩
  product A B .Product.has-is-product .is-product.π₂∘⟨⟩ = π₂∘⟨⟩
  product A B .Product.has-is-product .is-product.unique = ⟨⟩-unique

  private module product {A} {B} = Product (product A B)
  open product
    using (⟨⟩∘; ⟨⟩-η; has-is-product)
    renaming (unique₂ to ⟨⟩-unique₂)
    public
```
-->

If a category has all binary products, we can define a bifunctor
$\cC \times \cC \to \cC$ that sets $A, B$ to their product.

```agda
  _⊗₁_ : ∀ {a b x y} → Hom a x → Hom b y → Hom (a ⊗₀ b) (x ⊗₀ y)
  f ⊗₁ g = ⟨ f ∘ π₁ , g ∘ π₂ ⟩

  ×-functor : Functor (C ×ᶜ C) C
  ×-functor .F₀ (a , b) = a ⊗₀ b
  ×-functor .F₁ (f , g) = f ⊗₁ g
  ×-functor .F-id = sym $ ⟨⟩-unique id-comm id-comm
  ×-functor .F-∘ (f , g) (h , i) =
    sym $ ⟨⟩-unique
      (pulll π₁∘⟨⟩ ∙ extendr π₁∘⟨⟩)
      (pulll π₂∘⟨⟩ ∙ extendr π₂∘⟨⟩)
```

We also define a handful of common morphisms.

```agda
  δ : ∀ {A} → Hom A (A ⊗₀ A)
  δ = ⟨ id , id ⟩

  swap : ∀ {A B} → Hom (A ⊗₀ B) (B ⊗₀ A)
  swap = ⟨ π₂ , π₁ ⟩

  ×-assoc : ∀ {A B C} → Hom (A ⊗₀ (B ⊗₀ C)) ((A ⊗₀ B) ⊗₀ C)
  ×-assoc = ⟨ ⟨ π₁ , π₁ ∘ π₂ ⟩ , π₂ ∘ π₂ ⟩
```

<!--
```agda
  δ-natural : is-natural-transformation Id (×-functor F∘ Cat⟨ Id , Id ⟩) λ _ → δ
  δ-natural x y f = ⟨⟩-unique₂
    (cancell π₁∘⟨⟩) (cancell π₂∘⟨⟩)
    (pulll π₁∘⟨⟩ ∙ cancelr π₁∘⟨⟩) (pulll π₂∘⟨⟩ ∙ cancelr π₂∘⟨⟩)

  swap-is-iso : ∀ {A B} → is-invertible (swap {A} {B})
  swap-is-iso = make-invertible swap
    (⟨⟩-unique₂ (pulll π₁∘⟨⟩ ∙ π₂∘⟨⟩) ((pulll π₂∘⟨⟩ ∙ π₁∘⟨⟩)) (idr _) (idr _))
    (⟨⟩-unique₂ (pulll π₁∘⟨⟩ ∙ π₂∘⟨⟩) ((pulll π₂∘⟨⟩ ∙ π₁∘⟨⟩)) (idr _) (idr _))

  swap-natural
    : ∀ {A B C D} ((f , g) : Hom A C × Hom B D)
    → (g ⊗₁ f) ∘ swap ≡ swap ∘ (f ⊗₁ g)
  swap-natural (f , g) =
    (g ⊗₁ f) ∘ swap                       ≡⟨ ⟨⟩∘ _ ⟩
    ⟨ (g ∘ π₁) ∘ swap , (f ∘ π₂) ∘ swap ⟩ ≡⟨ ap₂ ⟨_,_⟩ (pullr π₁∘⟨⟩) (pullr π₂∘⟨⟩) ⟩
    ⟨ g ∘ π₂ , f ∘ π₁ ⟩                   ≡˘⟨ ap₂ ⟨_,_⟩ π₂∘⟨⟩ π₁∘⟨⟩ ⟩
    ⟨ π₂ ∘ (f ⊗₁ g) , π₁ ∘ (f ⊗₁ g) ⟩     ≡˘⟨ ⟨⟩∘ _ ⟩
    swap ∘ (f ⊗₁ g)                       ∎

  swap-δ : ∀ {A} → swap ∘ δ ≡ δ {A}
  swap-δ = ⟨⟩-unique (pulll π₁∘⟨⟩ ∙ π₂∘⟨⟩) (pulll π₂∘⟨⟩ ∙ π₁∘⟨⟩)

  assoc-δ : ∀ {a} → ×-assoc ∘ (id ⊗₁ δ {a}) ∘ δ {a} ≡ (δ ⊗₁ id) ∘ δ
  assoc-δ = ⟨⟩-unique₂
    (pulll π₁∘⟨⟩ ∙ ⟨⟩-unique₂
      (pulll π₁∘⟨⟩ ∙ pulll π₁∘⟨⟩ ∙ pullr π₁∘⟨⟩)
      (pulll π₂∘⟨⟩ ∙ pullr (pulll π₂∘⟨⟩) ∙ pulll (pulll π₁∘⟨⟩) ∙ pullr π₂∘⟨⟩)
      (pulll (pulll π₁∘⟨⟩) ∙ pullr π₁∘⟨⟩)
      (pulll (pulll π₂∘⟨⟩) ∙ pullr π₁∘⟨⟩)
    ∙ pushl (sym π₁∘⟨⟩))
    (pulll π₂∘⟨⟩ ∙ pullr (pulll π₂∘⟨⟩) ∙ pulll (pulll π₂∘⟨⟩) ∙ pullr π₂∘⟨⟩)
    refl
    (pulll π₂∘⟨⟩ ∙ pullr π₂∘⟨⟩)

  by-π₁ : ∀ {X Y Z} {f f' : Hom X Y} {g g' : Hom X Z} → ⟨ f , g ⟩ ≡ ⟨ f' , g' ⟩ → f ≡ f'
  by-π₁ p = sym π₁∘⟨⟩ ∙ ap (π₁ ∘_) p ∙ π₁∘⟨⟩

  extend-π₁ : ∀ {X Y Z} {f : Hom X Y} {g : Hom X Z} {h} → ⟨ f , g ⟩ ≡ h → f ≡ π₁ ∘ h
  extend-π₁ p = sym π₁∘⟨⟩ ∙ ap (π₁ ∘_) p

  by-π₂ : ∀ {X Y Z} {f f' : Hom X Y} {g g' : Hom X Z} → ⟨ f , g ⟩ ≡ ⟨ f' , g' ⟩ → g ≡ g'
  by-π₂ p = sym π₂∘⟨⟩ ∙ ap (π₂ ∘_) p ∙ π₂∘⟨⟩

  extend-π₂ : ∀ {X Y Z} {f : Hom X Y} {g : Hom X Z} {h} → ⟨ f , g ⟩ ≡ h → g ≡ π₂ ∘ h
  extend-π₂ p = sym π₂∘⟨⟩ ∙ ap (π₂ ∘_) p

  π₁-inv
    : ∀ {W X Y Z}
    → {f : Hom (W ⊗₀ X) Y} {g : Hom (W ⊗₀ X) Z}
    → (⟨⟩-inv : is-invertible ⟨ f , g ⟩)
    → f ∘ is-invertible.inv ⟨⟩-inv ≡ π₁
  π₁-inv {f = f} {g = g} ⟨⟩-inv =
    pushl (sym π₁∘⟨⟩) ∙ elimr (is-invertible.invl ⟨⟩-inv)

  π₂-inv
    : ∀ {W X Y Z}
    → {f : Hom (W ⊗₀ X) Y} {g : Hom (W ⊗₀ X) Z}
    → (⟨⟩-inv : is-invertible ⟨ f , g ⟩)
    → g ∘ is-invertible.inv ⟨⟩-inv ≡ π₂
  π₂-inv {f = f} {g = g} ⟨⟩-inv =
    pushl (sym π₂∘⟨⟩) ∙ elimr (is-invertible.invl ⟨⟩-inv)
```
-->

<!--
```agda
to-binary-products
  : ∀ {o ℓ} {C : Precategory o ℓ}
  → (∀ A B → Product C A B)
  → Binary-products C
to-binary-products {C = C} products = binary-products where
  module product {A} {B} = Product (products A B)
  open Binary-products hiding (product)

  binary-products : Binary-products C
  binary-products ._⊗₀_ A B = product.apex {A} {B}
  binary-products .π₁ = product.π₁
  binary-products .π₂ = product.π₂
  binary-products .⟨_,_⟩ = product.⟨_,_⟩
  binary-products .π₁∘⟨⟩ = product.π₁∘⟨⟩
  binary-products .π₂∘⟨⟩ = product.π₂∘⟨⟩
  binary-products .⟨⟩-unique = product.unique
```
-->

# Representability of products

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} where
  open Cat.Reasoning C
```
-->

The collection of maps into a product $a \times b$ is equivalent to
the collection of pairs of maps into $a$ and $b$. The forward direction
of the equivalence is given by postcomposition of the projections, and
the reverse direction by the universal property of products.

```agda
  product-repr
    : ∀ {a b}
    → (prod : Product C a b)
    → (x : Ob)
    → Hom x (Product.apex prod) ≃ (Hom x a × Hom x b)
  product-repr prod x = Iso→Equiv λ where
      .fst f → π₁ ∘ f , π₂ ∘ f
      .snd .is-iso.inv (f , g) → ⟨ f , g ⟩
      .snd .is-iso.rinv (f , g) → π₁∘⟨⟩ ,ₚ π₂∘⟨⟩
      .snd .is-iso.linv f → sym (⟨⟩∘ f) ∙ eliml ⟨⟩-η
    where open Product prod
```
