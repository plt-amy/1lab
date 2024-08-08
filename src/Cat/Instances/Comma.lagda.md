<!--
```agda
open import Cat.Instances.Shape.Terminal
open import Cat.Functor.Constant
open import Cat.Functor.Compose
open import Cat.Functor.Base
open import Cat.Groupoid
open import Cat.Morphism
open import Cat.Prelude

import Cat.Functor.Reasoning
import Cat.Reasoning
```
-->

```agda
module Cat.Instances.Comma where
```

<!--
```agda
private variable
  o h ao ah bo bh : Level
  A B C : Precategory o h
open Precategory
open Functor
```
-->

# Comma categories {defines="comma-category"}

The **comma category** of two functors $F : \cA \to \cC$ and $G : \cB
\to \cC$ with common codomain, written $F \downarrow G$, is the
directed, bicategorical analogue of a [[pullback]] square. It consists
of maps in $\cC$ which all have their domain in the image of $F$, and
codomain in the image of $G$.

The comma category is the universal way of completing a [cospan] of
functors $A \to C \ot B$ to a square, like the one below, which commutes
_up to a natural transformation_ $\theta$. Note the similarity with a
[[pullback]] square.

[cospan]: Cat.Instances.Shape.Cospan.html

~~~{.quiver}
\[\begin{tikzcd}
  {F\downarrow G} && \mathcal{A} \\
  \\
  \mathcal{B}     && \mathcal{C}
  \arrow["F", from=1-3, to=3-3]
  \arrow["G"', from=3-1, to=3-3]
  \arrow["{\rm{dom}}", from=1-1, to=1-3]
  \arrow["{\rm{cod}}"', from=1-1, to=3-1]
  \arrow["\theta"{description}, Rightarrow, from=1-1, to=3-3]
\end{tikzcd}\]
~~~

<!--
```agda
module
  _ {A : Precategory ao ah}
    {B : Precategory bo bh}
    {C : Precategory o h}
    (F : Functor A C) (G : Functor B C) where

  private
    module A = Precategory A
    module B = Precategory B
    module C = Cat.Reasoning C
    module F = Cat.Functor.Reasoning F
    module G = Cat.Functor.Reasoning G
```
-->

The objects in $F \downarrow G$ are given by triples $(x, y, f)$ where
$x : \cA$, $y : \cB$, and $f : F(x) \to G(y)$.

```agda
  record ↓Obj : Type (h ⊔ ao ⊔ bo) where
    no-eta-equality
    constructor ↓obj
    field
      {x} : Ob A
      {y} : Ob B
      map : Hom C (F .F₀ x) (G .F₀ y)
```

A morphism from $(x_a, y_a, f_a) \to (x_b, y_b, f_b)$ is given by a pair
of maps $\alpha : x_a \to x_b$ and $\beta : y_a \to y_b$, such that the
square below commutes. Note that this is exactly the data of one
component of a [naturality square].

[naturality square]: Cat.Base.html#natural-transformations

~~~{.quiver}
\[\begin{tikzcd}
  {F(x_a)} && {G(y_a)} \\
  \\
  {F(x_b)} && {G(y_b)}
  \arrow["{f_b}"', from=3-1, to=3-3]
  \arrow["{f_a}", from=1-1, to=1-3]
  \arrow["{F(\alpha)}"', from=1-1, to=3-1]
  \arrow["{G(\beta)}", from=1-3, to=3-3]
\end{tikzcd}\]
~~~

```agda
  record ↓Hom (a b : ↓Obj) : Type (h ⊔ bh ⊔ ah) where
    no-eta-equality
    constructor ↓hom
    private
      module a = ↓Obj a
      module b = ↓Obj b

    field
      {α} : Hom A a.x b.x
      {β} : Hom B a.y b.y
      sq : b.map C.∘ F .F₁ α ≡ G .F₁ β C.∘ a.map
```

We omit routine characterisations of equality in `↓Hom`{.Agda} from the
page: `↓Hom-path`{.Agda} and `↓Hom-set`{.Agda}.

<!--
```agda
  ↓Hom-pathp : ∀ {x x' y y'} {p : x ≡ x'} {q : y ≡ y'}
             → {f : ↓Hom x y} {g : ↓Hom x' y'}
             → (PathP _ (f .↓Hom.α) (g .↓Hom.α))
             → (PathP _ (f .↓Hom.β) (g .↓Hom.β))
             → PathP (λ i → ↓Hom (p i) (q i)) f g
  ↓Hom-pathp p q i .↓Hom.α = p i
  ↓Hom-pathp p q i .↓Hom.β = q i
  ↓Hom-pathp {p = p} {q} {f} {g} r s i .↓Hom.sq =
    is-prop→pathp (λ i → C.Hom-set _ _ (↓Obj.map (q i) C.∘ F .F₁ (r i))
                                       (G .F₁ (s i) C.∘ ↓Obj.map (p i)))
      (f .↓Hom.sq) (g .↓Hom.sq) i

  ↓Hom-path : ∀ {x y} {f g : ↓Hom x y}
            → (f .↓Hom.α ≡ g .↓Hom.α)
            → (f .↓Hom.β ≡ g .↓Hom.β)
            → f ≡ g
  ↓Hom-path = ↓Hom-pathp

  ↓Obj-path : {a b : ↓Obj}
            → (p : a .↓Obj.x ≡ b .↓Obj.x) (q : a .↓Obj.y ≡ b .↓Obj.y)
            → PathP (λ i → Hom C (F .F₀ (p i)) (G .F₀ (q i))) (a .↓Obj.map) (b .↓Obj.map)
            → a ≡ b
  ↓Obj-path p q r i .↓Obj.x = p i
  ↓Obj-path p q r i .↓Obj.y = q i
  ↓Obj-path p q r i .↓Obj.map = r i

  private unquoteDecl eqv = declare-record-iso eqv (quote ↓Hom)

  ↓Hom-set : ∀ x y → is-set (↓Hom x y)
  ↓Hom-set a b = hl' where abstract
    hl' : is-set (↓Hom a b)
    hl' = Iso→is-hlevel 2 eqv (hlevel 2)

```
-->

Identities and compositions are given componentwise:

```agda
  ↓id : ∀ {a} → ↓Hom a a
  ↓id .↓Hom.α = A.id
  ↓id .↓Hom.β = B.id
  ↓id .↓Hom.sq = ap (_ C.∘_) (F .F-id) ·· C.id-comm ·· ap (C._∘ _) (sym (G .F-id))

  ↓∘ : ∀ {a b c} → ↓Hom b c → ↓Hom a b → ↓Hom a c
  ↓∘ {a} {b} {c} g f = composite where
    open ↓Hom

    module a = ↓Obj a
    module b = ↓Obj b
    module c = ↓Obj c
    module f = ↓Hom f
    module g = ↓Hom g

    composite : ↓Hom a c
    composite .α = g.α A.∘ f.α
    composite .β = g.β B.∘ f.β
    composite .sq =
      c.map C.∘ F .F₁ (g.α A.∘ f.α)      ≡⟨ ap (_ C.∘_) (F .F-∘ _ _) ⟩
      c.map C.∘ F .F₁ g.α C.∘ F .F₁ f.α  ≡⟨ C.extendl g.sq ⟩
      G .F₁ g.β C.∘ b.map C.∘ F .F₁ f.α  ≡⟨ ap (_ C.∘_) f.sq ⟩
      G .F₁ g.β C.∘ G .F₁ f.β C.∘ a.map  ≡⟨ C.pulll (sym (G .F-∘ _ _)) ⟩
      G .F₁ (g.β B.∘ f.β) C.∘ a.map      ∎
```

This assembles into a precategory.

```agda
  _↓_ : Precategory _ _
  _↓_ .Ob = ↓Obj
  _↓_ .Hom = ↓Hom
  _↓_ .Hom-set = ↓Hom-set
  _↓_ .id = ↓id
  _↓_ ._∘_ = ↓∘
  _↓_ .idr f = ↓Hom-path (A.idr _) (B.idr _)
  _↓_ .idl f = ↓Hom-path (A.idl _) (B.idl _)
  _↓_ .assoc f g h = ↓Hom-path (A.assoc _ _ _) (B.assoc _ _ _)
```

We also have the projection functors onto the factors, and the natural
transformation $\theta$ witnessing "directed commutativity" of the
square.

```agda
  Dom : Functor _↓_ A
  Dom .F₀ = ↓Obj.x
  Dom .F₁ = ↓Hom.α
  Dom .F-id = refl
  Dom .F-∘ _ _ = refl

  Cod : Functor _↓_ B
  Cod .F₀ = ↓Obj.y
  Cod .F₁ = ↓Hom.β
  Cod .F-id = refl
  Cod .F-∘ _ _ = refl

  θ : (F F∘ Dom) => (G F∘ Cod)
  θ = NT (λ x → x .↓Obj.map) λ x y f → f .↓Hom.sq
```

<!--
```agda
  module _ (A-grpd : is-pregroupoid A) (B-grpd : is-pregroupoid B) where
    open ↓Hom
    open is-invertible
    open Inverses

    ↓-is-pregroupoid : is-pregroupoid _↓_
    ↓-is-pregroupoid f .inv .α = A-grpd (f .α) .inv
    ↓-is-pregroupoid f .inv .β = B-grpd (f .β) .inv
    ↓-is-pregroupoid f .inv .sq = C.rswizzle
      (sym (C.lswizzle (f .sq) (G.annihilate (B-grpd (f .β) .invr))) ∙ C.assoc _ _ _)
      (F.annihilate (A-grpd (f .α) .invl))
    ↓-is-pregroupoid f .inverses .invl = ↓Hom-path (A-grpd (f .α) .invl) (B-grpd (f .β) .invl)
    ↓-is-pregroupoid f .inverses .invr = ↓Hom-path (A-grpd (f .α) .invr) (B-grpd (f .β) .invr)

module _ {A : Precategory ao ah} {B : Precategory bo bh} where
  private
    module A = Precategory A
    module B = Precategory B
    variable
      F : Functor A B
  open ↓Obj
  open ↓Hom

  infix 8 _↙_ _↘_
  _↙_ : A.Ob → Functor B A → Precategory _ _
  X ↙ T = !Const X ↓ T

  _↘_ : Functor B A → A.Ob → Precategory _ _
  S ↘ X = S ↓ !Const X

  θ↘ : ∀ {X} → F F∘ Dom F (!Const X) => Const X
  θ↘ ._=>_.η f = f .map
  θ↘ ._=>_.is-natural _ _ γ = γ .sq

  θ↙ : ∀ {X} → Const X => F F∘ Cod (!Const X) F
  θ↙ ._=>_.η f = f .map
  θ↙ ._=>_.is-natural _ _ γ = γ .sq


module ↙-compose
    {oc ℓc od ℓd oe ℓe}
    {𝒞 : Precategory oc ℓc} {𝒟 : Precategory od ℓd} {ℰ : Precategory oe ℓe}
    (F : Functor 𝒞 𝒟) (G : Functor 𝒟 ℰ)
  where
  private
    module 𝒟 = Precategory 𝒟
    module ℰ = Precategory ℰ
    module F = Functor F
    module G = Cat.Functor.Reasoning G
  open ↓Obj
  open ↓Hom

  _↙>_ : ∀ {d} (g : Ob (d ↙ G)) → Ob (g .y ↙ F) → Ob (d ↙ G F∘ F)
  g ↙> f = ↓obj (G.₁ (f .map) ℰ.∘ g .map)

  ↙-compose : ∀ {d} (g : Ob (d ↙ G)) → Functor (g .y ↙ F) (d ↙ G F∘ F)
  ↙-compose g .F₀ f = g ↙> f
  ↙-compose g .F₁ {f} {f'} h = ↓hom {β = h .β} $
    (G.₁ (f' .map) ℰ.∘ g .map) ℰ.∘ ℰ.id          ≡⟨ ℰ.idr _ ⟩
    G.₁ (f' .map) ℰ.∘ g .map                     ≡⟨ G.pushl (sym (𝒟.idr _) ∙ h .sq) ⟩
    G.₁ (F.₁ (h .β)) ℰ.∘ G.₁ (f .map) ℰ.∘ g .map ∎
  ↙-compose g .F-id = ↓Hom-path _ _ refl refl
  ↙-compose g .F-∘ _ _ = ↓Hom-path _ _ refl refl

  ↙>-id : ∀ {c} {f : Ob (c ↙ G F∘ F)} → ↓obj (f .map) ↙> ↓obj 𝒟.id ≡ f
  ↙>-id = ↓Obj-path _ _ refl refl (G.eliml refl)


-- Outside the main module to make instance search work.
module _ where
  open ↓Hom
  open ↓Obj
  open Precategory
  open Functor


  instance
    Extensional-↓Hom
      : ∀ {ℓr}
      → {F : Functor A C} {G : Functor B C}
      → {f g : ↓Obj F G}
      → ⦃ sab : Extensional (A .Hom (f .x) (g .x) × B .Hom (f .y) (g .y)) ℓr ⦄
      → Extensional (↓Hom F G f g) ℓr
    Extensional-↓Hom {A = A} {B = B} {F = F} {G = G} {f = f} {g = g} ⦃ sab ⦄ =
      injection→extensional! (λ p → ↓Hom-path F G (ap fst p) (ap snd p)) sab

    -- Overlapping instances for ↙ and ↘; these resolve issues where
    -- Agda cannot determine the source category A for 'Const'. We can
    -- also optimize the instance a bit to avoid a silly obligation that
    -- 'tt ≡ tt'.
    Extensional-↙Hom
      : ∀ {ℓr}
      → {X : A .Ob} {T : Functor B A}
      → {f g : ↓Obj (!Const X) T}
      → ⦃ sb : Extensional (B .Hom (f .y) (g .y)) ℓr ⦄
      → Extensional (↓Hom (!Const X) T f g) ℓr
    Extensional-↙Hom {B = B} {X = X} {T = T} {f = f} {g = g} ⦃ sb ⦄ =
      injection→extensional! {f = λ sq → sq .β} (λ p → ↓Hom-path (!Const X) T refl p) sb
    {-# OVERLAPS Extensional-↙Hom #-}

    Extensional-↘Hom
      : ∀ {ℓr}
      → {T : Functor A B} {X : B .Ob}
      → {f g : ↓Obj T (!Const X)}
      → ⦃ sa : Extensional (A .Hom (f .x) (g .x)) ℓr ⦄
      → Extensional (↓Hom T (!Const X) f g) ℓr
    Extensional-↘Hom {A = A} {T = T} {X = X} {f = f} {g = g} ⦃ sa ⦄ =
      injection→extensional! {f = λ sq → sq .α} (λ p → ↓Hom-path T (!Const X) p refl) sa
    {-# OVERLAPS Extensional-↘Hom #-}


    -- Extensionality cannot handle PathP, but we /can/ make a bit of progress
    -- by deleting 'tt ≡ tt' obligations when using ↙ and ↘.
    Extensional-↙Obj
      : ∀ {ℓr}
      → {X : A .Ob} {T : Functor B A}
      → ⦃ sb : Extensional (Σ[ Y ∈ B .Ob ] (A .Hom X (T .F₀ Y))) ℓr ⦄
      → Extensional (↓Obj (!Const X) T) ℓr
    Extensional-↙Obj {A = A} {B = B} {X = X} {T = T} ⦃ sb ⦄ =
      iso→extensional isom sb
        where
          -- Easier to just do this by hand.
          isom : Iso (↓Obj (!Const X) T) (Σ[ Y ∈ B .Ob ] (A .Hom X (T .F₀ Y)))
          isom .fst α = ↓Obj.y α , ↓Obj.map α
          isom .snd .is-iso.inv (Y , f) = ↓obj f
          isom .snd .is-iso.rinv _ = refl
          isom .snd .is-iso.linv _ = ↓Obj-path (!Const X) T refl refl refl

    Extensional-↘Obj
      : ∀ {ℓr}
      → {T : Functor A B} {Y : B .Ob}
      → ⦃ sb : Extensional (Σ[ X ∈ A .Ob ] (B .Hom (T .F₀ X) Y)) ℓr ⦄
      → Extensional (↓Obj T (!Const Y)) ℓr
    Extensional-↘Obj {A = A} {B = B} {T = T} {Y = Y} ⦃ sb ⦄ =
      iso→extensional isom sb
        where
          -- Easier to just do this by hand.
          isom : Iso (↓Obj T (!Const Y)) (Σ[ X ∈ A .Ob ] (B .Hom (T .F₀ X) Y))
          isom .fst α = ↓Obj.x α , ↓Obj.map α
          isom .snd .is-iso.inv (Y , f) = ↓obj f
          isom .snd .is-iso.rinv _ = refl
          isom .snd .is-iso.linv _ = ↓Obj-path T (!Const Y) refl refl refl
```
-->
