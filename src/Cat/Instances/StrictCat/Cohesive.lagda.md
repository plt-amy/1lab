<!--
```agda
open import Cat.Instances.StrictCat
open import Cat.Instances.Discrete hiding (Disc)
open import Cat.Instances.Functor
open import Cat.Instances.Product
open import Cat.Functor.Adjoint
open import Cat.Prelude
```
-->

```agda
module Cat.Instances.StrictCat.Cohesive where
```

<!--
```agda
private variable
  ℓ o h : Level

open Precategory
open Functor
open _=>_
open _⊣_
```
-->

# Strict-cats is "cohesive"

We prove that the category $\strcat$ admits an adjoint
quadruple

$$
\Pi_0 \dashv \rm{Disc} \dashv \Gamma \dashv \rm{Codisc}
$$

where the "central" adjoint $\Gamma$ is the functor which sends a strict
category to its underlying set of objects. This lets us treat categories
as giving a kind of "spatial" structure over $\rm{Sets}$.  The left-
and right- adjoints to $\rm{Ob}$ equip sets with the "discrete" and
"codiscrete" spatial structures, where nothing is stuck together, or
everything is stuck together.

The extra [[right adjoint]] to $\rm{Ob}$ assigns a category to its set
of connected components, which can be thought of as the "pieces" of the
category. Two objects land in the same connected component if there is a
path of morphisms connecting them, hence the name.

:::{.note}
Generally, the term "cohesive" is applied to Grothendieck
topoi, which `Strict-cats`{.Agda} is _very far_ from being. We're using it
here by analogy: There's an adjoint quadruple, where the functor
$\Gamma$ sends each category to its set of points: see [the last
section]. Strictly speaking, the [[left adjoint]] to $\Gamma$ isn't defined
by tensoring with `Sets`{.Agda}, but it _does_ have the effect of
sending $S$ to the coproduct of $S$-many copies of the point category.
:::

[the last section]: #object-set-vs-global-sections

# Disc ⊣ Γ

We begin by defining the object set functor.

```agda
Γ : Functor (Strict-cats o h) (Sets o)
Γ .F₀ (C , obset) = el (Ob C) obset
Γ .F₁ = F₀
Γ .F-id = refl
Γ .F-∘ _ _ = refl
```

We must then prove that the assignment `Disc'`{.Agda} extends to a
functor from `Sets`{.Agda}, and prove that it's left adjoint to the
functor `Γ`{.Agda} we defined above. Then we define the adjunction
`Disc⊣Γ`{.Agda}.

```agda
Disc : Functor (Sets ℓ) (Strict-cats ℓ ℓ)
Disc .F₀ S = Disc' S , S .is-tr
Disc .F₁ = lift-disc
Disc .F-id = Functor-path (λ x → refl) λ f → refl
Disc .F-∘ _ _ = Functor-path (λ x → refl) λ f → refl

Disc⊣Γ : Disc {ℓ} ⊣ Γ
Disc⊣Γ = adj where
```

<!--
```agda
  abstract
    lemma : ∀ {A : Strict-cats ℓ ℓ .Precategory.Ob}
              {x y z : A .fst .Precategory.Ob} (f : y ≡ z) (g : x ≡ y)
          → subst (A .fst .Precategory.Hom _) (g ∙ f) (A .fst .Precategory.id)
          ≡ A .fst .Precategory._∘_
            (subst (A .fst .Precategory.Hom _) f (A .fst .Precategory.id))
            (subst (A .fst .Precategory.Hom _) g (A .fst .Precategory.id))
    lemma {A = A} {x = x} =
      J' (λ y z f → (g : x ≡ y) → subst (X.Hom _) (g ∙ f) X.id
                  ≡ subst (X.Hom _) f X.id X.∘ subst (X.Hom _) g X.id)
        λ x g → (subst-∙ (X.Hom _) g refl _ ·· transport-refl _ ·· sym (X.idl _))
              ∙ ap₂ X._∘_ (sym (transport-refl _)) refl
      where module X = Precategory (A .fst)
```
-->

For the adjunction `unit`{.Agda}, we're asked to provide a natural
transformation from the identity functor to $\Gamma \circ
\rm{Disc}$; Since the object set of $\rm{Disc}(X)$ is simply
$X$, the identity map suffices:

```agda
  adj : Disc {ℓ} ⊣ Γ
  adj .unit   = NT (λ _ x → x) λ x y f i o → f o
```

The adjunction counit is slightly more complicated, as we have to give a
functor $\rm{Disc}(\Gamma(X)) \to X$, naturally in $X$. Since
morphisms in discrete categories are paths, for a map $x \equiv y$ (in
`{- 1 -}`{.Agda}), it suffices to assume $y$ really is $x$, and so the
identity map suffices.

```agda
  adj .counit = NT (λ x → F x) nat where
    F : (x : ⌞ Strict-cats ℓ ℓ ⌟)
      → Functor (Disc' (el _ (x .snd))) _
    F X .F₀ x = x
    F X .F₁ p = subst (X .fst .Hom _) p (X .fst .id) {- 1 -}
    F X .F-id = transport-refl _
    F X .F-∘ = lemma {A = X}
```

<!--
```agda
    abstract
      nat : (x y : ⌞ Strict-cats ℓ ℓ ⌟)
            (f : Strict-cats ℓ ℓ .Precategory.Hom x y)
          → (F y F∘ (Disc F∘ Γ) .F₁ f) ≡ (f F∘ F x)
      nat x y f =
        Functor-path (λ x → refl)
           (J' (λ x y p → subst (Y.Hom _) (ap (f .F₀) p) Y.id
                        ≡ f .F₁ (subst (X.Hom _) p X.id))
               λ _ → transport-refl _
                  ·· sym (f .F-id)
                  ·· ap (f .F₁) (sym (transport-refl _)))
         where
           module X = Precategory (x .fst)
           module Y = Precategory (y .fst)
```
-->

Fortunately the triangle identities are straightforwardly checked.

```agda
  adj .zig {x} = Functor-path (λ x i → x) λ f → x .is-tr _ _ _ _
  adj .zag = refl
```

# Γ ⊣ Codisc

The _codiscrete_ category on a set $X$ is the [[strict category]] with
object space $X$, and _all_ hom-spaces contractible. The assignment of
codiscrete categories extends to a functor $\Sets \to \strcat$, where we
lift functions to act on object parts and the action on morphisms is
trivial.

```agda
Codisc : Functor (Sets ℓ) (Strict-cats ℓ ℓ)
Codisc .F₀ S = Codisc' ∣ S ∣ , S .is-tr

Codisc .F₁ f .F₀ = f
Codisc .F₁ f .F₁ = λ _ → lift tt
Codisc .F₁ f .F-id = refl
Codisc .F₁ f .F-∘ = λ _ _ → refl

Codisc .F-id    = Functor-path (λ x → refl) λ f → refl
Codisc .F-∘ _ _ = Functor-path (λ x → refl) λ f → refl
```

The codiscrete category functor is right adjoint to the object set
functor $\Gamma$. The construction of the adjunction is now simple in
both directions:

```agda
Γ⊣Codisc : Γ ⊣ Codisc {ℓ}
Γ⊣Codisc = adj where
  adj : _ ⊣ _
  adj .unit =
    NT (λ x → record { F₀ = λ x → x ; F₁ = λ _ → lift tt
                     ; F-id = refl ; F-∘ = λ _ _ → refl })
       λ x y f → Functor-path (λ _ → refl) λ _ → refl
  adj .counit = NT (λ _ x → x) λ x y f i o → f o
  adj .zig = refl
  adj .zag = Functor-path (λ _ → refl) λ _ → refl
```

## Object set vs global sections

Above, we defined the functor $\Gamma$ by directly projecting the
underlying set of each category. Normally in the definition of a
cohesion structure, we use the _global sections_ functor which maps
$x \mapsto \hom(*,x)$ (where $*$ is the [[terminal object]]). Here we prove
that these functors are naturally isomorphic, so our abbreviation above
is harmless.

Below, we represent the [[terminal category]] $*$ as the codiscrete category
on the terminal set. Using the codiscrete category here is equivalent to
using the discrete category, but it is more convenient since the
$\hom$-sets are definitionally contractible.

```agda
module _ {ℓ} where
  import Cat.Morphism Cat[ Strict-cats ℓ ℓ , Sets ℓ ] as Nt

  GlobalSections : Functor (Strict-cats ℓ ℓ) (Sets ℓ)
  GlobalSections .F₀ C =
    el (Functor (Codisc' (Lift _ ⊤)) (C .fst)) (Functor-is-set (C .snd))
  GlobalSections .F₁ G F = G F∘ F
  GlobalSections .F-id = funext λ _ → Functor-path (λ _ → refl) λ _ → refl
  GlobalSections .F-∘ f g = funext λ _ → Functor-path (λ _ → refl) λ _ → refl
```

Since `GlobalSections`{.Agda} is a section of the $\hom$ functor, it
acts on maps by composition. The functor identities hold definitionally.

```agda
  GlobalSections≅Γ : Γ {ℓ} Nt.≅ GlobalSections
  GlobalSections≅Γ = Nt.make-iso f g f∘g g∘f where
    open Precategory
```

We define a natural isomorphism from `Γ`{.Agda} to the
`GlobalSections`{.Agda} functor by sending each object to the constant
functor on that object. This assignment is natural because it is
essentially independent of the coordinate.

```agda
    f : Γ => GlobalSections
    f .η x ob = record
      { F₀ = λ _ → ob
      ; F₁ = λ _ → x .fst .id
      ; F-id = refl
      ; F-∘ = λ _ _ → sym (x .fst .idl _)
      }
    f .is-natural x y f = funext λ _ → Functor-path (λ _ → refl) λ _ → sym (f .F-id)
```

In the opposite direction, the natural transformation is defined by
evaluating at the point. These natural transformations compose to the
identity almost definitionally, but Agda does need some convincing,
using our path helpers, `Functor-path`{.Agda} and `trivial!`{.Agda}.

```agda
    g : GlobalSections => Γ
    g .η x f = f # lift tt
    g .is-natural x y f = refl

    f∘g : f ∘nt g ≡ idnt
    f∘g = ext λ c x → Functor-path (λ x → refl) λ f → sym (x .F-id)

    g∘f : g ∘nt f ≡ idnt
    g∘f = trivial!
```

# Connected components {defines="connected-component"}

The set of connected components of a category is the quotient of the
object set by the "relation" generated by the `Hom`{.Agda} sets. This is
not a relation because `Hom`{.Agda} takes values in sets, not
propositions; Thus the quotient forgets precisely _how_ objects are
connected. This is intentional!

```agda
π₀ : Precategory o h → Set (o ⊔ h)
π₀ C = el (Ob C / Hom C) squash
```

The `π₀`{.Agda} construction extends to a functor `Π₀`{.Agda} (capital
pi for **P**ieces) from `Strict-cats`{.Agda} back to `Sets`{.Agda}. We
send a functor $F$ to its object part, but postcomposing with the map
`inc`{.Agda} which sends an object of $\cD$ to the connected
component it inhabits.

```agda
Π₀ : Functor (Strict-cats o h) (Sets (o ⊔ h))
Π₀ .F₀ (C , _) = π₀ C
Π₀ .F₁ F =
  Quot-elim (λ _ → squash) (λ x → inc (F .F₀ x))
    λ x y r → glue (_ , _ , F .F₁ r)
```

We must prove that this assignment respects the quotient, which is where
the morphism part of the functor comes in: Two objects $x, y : \cC$
are in the same connected component if there is a map $r : x \to y$; To
show that $F_0(x)$ and $F_0(y)$ are also in the same connected
component, we must give a map $F_0(x) \to F_0(y)$, but this can be
canonically chosen to be $F_1(r)$.

```agda
Π₀ .F-id    = funext (Coeq-elim-prop (λ _ → squash _ _) λ x → refl)
Π₀ .F-∘ f g = funext (Coeq-elim-prop (λ _ → squash _ _) λ x → refl)
```

The adjunction `unit`{.Agda} is a natural assignment of functors $\cX
\to \rm{Disc}(\Pi_0(\cX))$. We send $x$ to its connected
component, and we must send a map $r : x \to y$ to an equality between
the connected components of $x$ and $y$; But we get this from the
quotient.

```agda
Π₀⊣Disc : Π₀ ⊣ Disc {ℓ}
Π₀⊣Disc = adj where
  adj : _ ⊣ _
  adj .unit .η x = Disc-into _ inc quot
  adj .unit .is-natural x y f = Functor-path (λ x → refl) λ _ → squash _ _ _ _
```

The adjunction `counit`{.Agda} is an assignment of functions
$\Pi_0(\rm{Disc}(X)) \to X$. This is essentially a natural
isomorphism: the set of connected components of a discrete category is
the same set we started with.

```agda
  adj .counit .η X = Quot-elim (λ _ → X .is-tr) (λ x → x) λ x y r → r
  adj .counit .is-natural x y f = trivial!
```

The triangle identities are again straightforwardly checked.

```agda
  adj .zig {x} = trivial!
  adj .zag = Functor-path (λ x → refl) λ f → refl
```

Furthermore, we can prove that the connected components of a product
category are product sets of connected components.

```agda
Π₀-preserve-prods
  : ∀ {C D : Precategory o h} → π₀ ʻ (C ×ᶜ D) ≡ (π₀ ʻ C × π₀ ʻ D)
Π₀-preserve-prods {C = C} {D = D} = Iso→Path (f , isom) where
  open is-iso
```

We have a map splitting $\pi_0$ of the product category onto $\pi_0$ of
each factor. This maps respect the quotient because we can also split
the morphisms.

```agda
  f : π₀ ʻ (C ×ᶜ D) → π₀ ʻ C × π₀ ʻ D
  f = Quot-elim
    (λ _ → hlevel 2)
    (λ (a , b) → inc a , inc b)
    λ (x , x') (y , y') (f , g) i →
      glue (x , y , f) i , glue (x' , y' , g) i
```

This map has an inverse given by joining up the pairs:

```agda
  isom : is-iso f
  isom .inv (a , b) = Coeq-rec₂ squash (λ x y → inc (x , y))
    (λ a (x , y , r) i → glue ((x , a) , (y , a) , r , Precategory.id D) i)
    (λ a (x , y , r) i → glue ((a , x) , (a , y) , Precategory.id C , r) i)
    a b

  isom .rinv = elim! λ x y → refl
  isom .linv = elim! λ x y → refl
```

## Pieces have points

An important property of the cohesive quadruple defined above is that
the canonically-defined natural morphism $\Gamma(X) \to \Pi_0(X)$ is
surjective, i.e. _each piece has at least one point_.

```agda
Points→Pieces : Γ {ℓ} {ℓ} => Π₀
Points→Pieces .η _ x = inc x
Points→Pieces .is-natural x y f i o = inc (f .F₀ o)

pieces-have-points : ∀ {x} → is-surjective (Points→Pieces {ℓ} .η x)
pieces-have-points = elim! λ x → inc (x , refl)
```
