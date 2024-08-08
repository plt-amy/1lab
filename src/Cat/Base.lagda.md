<!--
```agda
open import 1Lab.Path.IdentitySystem
open import 1Lab.Reflection.HLevel
open import 1Lab.Reflection.Record
open import 1Lab.HLevel.Universe
open import 1Lab.Extensionality
open import 1Lab.HLevel.Closure
open import 1Lab.Reflection
open import 1Lab.Underlying
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type hiding (id ; _∘_)
```
-->

```agda
module Cat.Base where
```

# Precategories {defines="category precategory"}

In univalent mathematics, it makes sense to distinguish two stages in
the construction of categories: A **precategory** is the object that
directly corresponds to the definition of precategory as it is
traditionally formalised, whereas a **category** (or [[univalent
category]]) has an extra condition: Isomorphic objects must be
identified.

```agda
record Precategory (o h : Level) : Type (lsuc (o ⊔ h)) where
  no-eta-equality
```

A **precategory** is a "proof-relevant preorder". In a preordered set
$(A, \le)$, the inhabitants of a set $A$ are related by a _proposition_
$a \le b$, which is

- _reflexive_: $a \le a$
- _transitive_: $a \le b \land b \le c \to a \le c$

In a precategory, the condition that $a \le b$ be a proposition is
relaxed: A precategory has a `type of objects`{.Agda ident=Ob} and,
between each $x, y$, a **set** $\hom(x, y)$ of relations (or maps). The
name "$\hom$" is historical and it betrays the original context in which
categories where employed: algebra(ic topology), where the maps in
question are **hom**omorphisms.

```agda
  field
    Ob  : Type o
    Hom : Ob → Ob → Type h
```

Whereas reading a classical definition into a type theory where equality
is a proposition, the word **set** may be read to mean inhabitant of a
[[universe]]. But in HoTT, if we want categories to be well-behaved, we
do actually mean _set_: A type of [[h-level 2|set]]

```agda
  field
    Hom-set : (x y : Ob) → is-set (Hom x y)
```

If you are already familiar with the definition of precategory there are
two things to note here:

First is that our formalization has a _family_ of `Hom`{.Agda}-sets
rather than a single `Hom`{.Agda}-set and source/target maps. This
formulation is not unique to precategory theory done internally to type
theory, but it is the most reasonable way to formulate things in this
context.

Second is that the word "set" in the definition of Hom-set has nothing
to do with "size". Indeed, the "set"/"not a set" (alternatively
"small"/"large") distinction makes no sense in type theory (some may
argue it makes no sense in general).

Instead, the `Precategory`{.Agda} record is parametrised by two levels:
`o`, and `h`. The type of objects has to fit in the universe `Type o`,
and the family of Hom-sets is `Type h` valued. As an example, the thin
precategory corresponding to the natural numbers with their usual ordering
would live in `Precategory lzero lzero`.

This means, for instance, that there is no single "category of sets" -
there is a _family_ of categories of sets, parametrised by the level in
which its objects live.

```agda
  field
    id  : ∀ {x}     → Hom x x
    _∘_ : ∀ {x y z} → Hom y z → Hom x y → Hom x z

  infixr 40 _∘_
```

The "proof-relevant" version of the reflexivity and transitivity laws
are, respectively, the `identity morphisms`{.Agda} and `composition of
morphisms`{.Agda ident="_∘_"}. Unlike in the proof-irrelevant case, in
which an inhabitant of $x \le y$ merely witnesses that two things are
related, these operations _matter_, and thus must satisfy laws:

```agda
  field
    idr : ∀ {x y} (f : Hom x y) → f ∘ id ≡ f
    idl : ∀ {x y} (f : Hom x y) → id ∘ f ≡ f
```

The two identity laws say that the identity morphisms serve as neutral
elements for the composition operation, both on the left and on the
right. The associativity law (below) says that both ways of writing
parentheses around a composition of three morphisms are equal: $(f \circ
g) \circ h = f \circ (g \circ h)$.

```agda
    assoc : ∀ {w x y z} (f : Hom y z) (g : Hom x y) (h : Hom w x)
          → f ∘ (g ∘ h) ≡ (f ∘ g) ∘ h
```

<!--
```agda
open hlevel-projection
private
  hom-set : ∀ {o ℓ} (C : Precategory o ℓ) {x y} → is-set (C .Precategory.Hom x y)
  hom-set C = C .Precategory.Hom-set _ _

instance
  hlevel-proj-hom : hlevel-projection (quote Precategory.Hom)
  hlevel-proj-hom .has-level = quote hom-set
  hlevel-proj-hom .get-level _ = pure (quoteTerm (suc (suc zero)))
  hlevel-proj-hom .get-argument (_ ∷ _ ∷ c v∷ _) = pure c
  {-# CATCHALL #-}
  hlevel-proj-hom .get-argument _ = typeError []
```
-->

## Opposites {defines="opposite-category"}

A common theme throughout precategory theory is that of _duality_: The dual
of a categorical concept is same concept, with "all the arrows
inverted". To make this formal, we introduce the idea of _opposite
categories_: The opposite of $C$, written $C\op$, has the same
`objects`{.Agda}, but with $\hom_{C\op}(x, y) =
\hom_{C}(y, x)$.

```agda
infixl 60 _^op
_^op : ∀ {o₁ h₁} → Precategory o₁ h₁ → Precategory o₁ h₁
(C ^op) .Precategory.Ob = C .Precategory.Ob
(C ^op) .Precategory.Hom     x y = C .Precategory.Hom y x
(C ^op) .Precategory.Hom-set x y = C .Precategory.Hom-set y x
(C ^op) .Precategory.id      = C .Precategory.id
(C ^op) .Precategory._∘_ f g = C .Precategory._∘_ g f
```

Composition in the opposite precategory $C\op$ is "backwards" with
respect to $C$: $f \circ_{op} g = g \circ f$. This inversion, applied
twice, ends up equal to what we started with by the nature of
computation - An equality that arises like this, automatically from what
Agda computes, is called _definitional_.

```agda
(C ^op) .Precategory.idl x = C .Precategory.idr x
(C ^op) .Precategory.idr x = C .Precategory.idl x
```

The left and right identity laws are swapped for the construction of the
opposite precategory: For `idr`{.Agda} one has to show $f \circ_{op}
\id = f$, which computes into having to show that $\id
\circ_{op}{f} = f$. The case for `idl`{.Agda} is symmetric.

```agda
(C ^op) .Precategory.assoc f g h i = C .Precategory.assoc h g f (~ i)
```

For associativity, consider the case of `assoc`{.Agda} for the
opposite precategory $C\op$. What we have to show is - by the type of
`assoc₁`{.Agda} - $f \circ_{op} (g \circ_{op} h) = (f \circ_{op} g)
\circ_{op} h$. This computes into $(h \circ g) \circ f = h \circ (g
\circ f)$ - which is exactly what `sym (assoc C h g f)` shows!

```agda
C^op^op≡C : ∀ {o ℓ} {C : Precategory o ℓ} → C ^op ^op ≡ C
C^op^op≡C {C = C} i = precat i where
  open Precategory
  precat : C ^op ^op ≡ C
  precat i .Ob = C .Ob
  precat i .Hom = C .Hom
  precat i .Hom-set = C .Hom-set
  precat i .id = C .id
  precat i ._∘_ = C ._∘_
  precat i .idr = C .idr
  precat i .idl = C .idl
  precat i .assoc = C .assoc
```

<!--
```agda
{-# REWRITE C^op^op≡C #-}
```
-->

## The precategory of Sets {defines="category-of-sets"}

Given a [[universe level|universe]], we can consider the collection of
[[all sets|set]] of that level. This assembles into a
`precategory`{.Agda ident=Precategory} quite nicely, since _taking
function types_ is an operation that preserves h-level.

```agda
module _ where
  open Precategory

  Sets : (o : _) → Precategory (lsuc o) o
  Sets o .Ob = Set o
  Sets o .Hom A B = ∣ A ∣ → ∣ B ∣
  Sets o .Hom-set _ B f g p q i j a =
    B .is-tr (f a) (g a) (happly p a) (happly q a) i j
  Sets o .id x = x
  Sets o ._∘_ f g x = f (g x)
  Sets o .idl f = refl
  Sets o .idr f = refl
  Sets o .assoc f g h = refl
```

# Functors {defines=functor}

<!--
```agda
record
  Functor
    {o₁ h₁ o₂ h₂}
    (C : Precategory o₁ h₁)
    (D : Precategory o₂ h₂)
  : Type (o₁ ⊔ h₁ ⊔ o₂ ⊔ h₂)
  where
  no-eta-equality

  private
    module C = Precategory C
    module D = Precategory D
```
-->

Since a category is an algebraic structure, there is a natural
definition of _homomorphism of categories_ defined in the same fashion
as, for instance, a _homomorphism of groups_. Since this kind of
morphism is ubiquitous, it gets a shorter name: `Functor`{.Agda}.

Alternatively, functors can be characterised as the "proof-relevant
version" of a monotone map: A monotone map is a map $F : C \to D$ which
preserves the ordering relation, $x \le y \to F(x) \le F(y)$.
Categorifying, "preserves the ordering relation" becomes a function
between Hom-sets.

```agda
  field
    F₀ : C.Ob → D.Ob
    F₁ : ∀ {x y} → C.Hom x y → D.Hom (F₀ x) (F₀ y)
```

A Functor $F : C \to D$ consists of a `function between the object
sets`{.Agda ident="F₀"} - $F_0 : \rm{Ob}(C) \to \rm{Ob}(D)$, and
a `function between Hom-sets`{.Agda ident="F₁"} - which takes $f : x \to
y \in C$ to $F_1(f) : F_0(x) \to F_0(y) \in D$.

```agda
  field
    F-id : ∀ {x} → F₁ (C.id {x}) ≡ D.id
    F-∘ : ∀ {x y z} (f : C.Hom y z) (g : C.Hom x y)
        → F₁ (f C.∘ g) ≡ F₁ f D.∘ F₁ g
```

Furthermore, the morphism mapping $F_1$ must be homomorphic: Identity
morphisms are taken to identity morphisms (`F-id`{.Agda}) and
compositions are taken to compositions (`F-∘`{.Agda}).

<!--
```
  -- Alias for F₀ for use in Functor record modules.
  ₀ : C.Ob → D.Ob
  ₀ = F₀

  -- Alias for F₁ for use in Functor record modules.
  ₁ : ∀ {x y} → C.Hom x y → D.Hom (F₀ x) (F₀ y)
  ₁ = F₁
```
-->

Functors also have duals: The opposite of $F : C \to D$ is $F\op :
C\op \to D\op$.

```agda
  op : Functor (C ^op) (D ^op)
  op .F₀      = F₀
  op .F₁      = F₁
  op .F-id    = F-id
  op .F-∘ f g = F-∘ g f
```

<!--
```agda
F^op^op≡F : ∀ {o ℓ o' ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'} {F : Functor C D}
          → Functor.op (Functor.op F) ≡ F
F^op^op≡F {F = F} i .Functor.F₀ = F .Functor.F₀
F^op^op≡F {F = F} i .Functor.F₁ = F .Functor.F₁
F^op^op≡F {F = F} i .Functor.F-id = F .Functor.F-id
F^op^op≡F {F = F} i .Functor.F-∘ = F .Functor.F-∘

{-# REWRITE F^op^op≡F #-}
```
-->

## Composition

```agda
_F∘_ : ∀ {o₁ h₁ o₂ h₂ o₃ h₃}
         {C : Precategory o₁ h₁} {D : Precategory o₂ h₂} {E : Precategory o₃ h₃}
     → Functor D E → Functor C D → Functor C E
_F∘_ {C = C} {D} {E} F G = comps
```

Functors, being made up of functions, can themselves be composed. The
object mapping of $(F \circ G)$ is given by $F_0 \circ G_0$, and
similarly for the morphism mapping. Alternatively, composition of
functors is a categorification of the fact that monotone maps compose.

<!--
```agda
  module F∘ where
    module C = Precategory C
    module D = Precategory D
    module E = Precategory E

    module F = Functor F
    module G = Functor G
```
-->

```agda
    F₀ : C.Ob → E.Ob
    F₀ x = F.F₀ (G.F₀ x)

    F₁ : {x y : C.Ob} → C.Hom x y → E.Hom (F₀ x) (F₀ y)
    F₁ f = F.F₁ (G.F₁ f)
```

To verify that the result is functorial, equational reasoning is employed, using
the witnesses that $F$ and $G$ are functorial.

```agda
    abstract
      F-id : {x : C.Ob} → F₁ (C.id {x}) ≡ E.id {F₀ x}
      F-id {x} =
          F.F₁ (G.F₁ C.id) ≡⟨ ap F.F₁ G.F-id ⟩
          F.F₁ D.id        ≡⟨ F.F-id ⟩
          E.id             ∎

      F-∘ : {x y z : C.Ob} (f : C.Hom y z) (g : C.Hom x y)
          → F₁ (f C.∘ g) ≡ (F₁ f E.∘ F₁ g)
      F-∘ f g =
          F.F₁ (G.F₁ (f C.∘ g))     ≡⟨ ap F.F₁ (G.F-∘ f g) ⟩
          F.F₁ (G.F₁ f D.∘ G.F₁ g)  ≡⟨ F.F-∘ _ _ ⟩
          F₁ f E.∘ F₁ g             ∎

    comps : Functor _ _
    comps .Functor.F₀ = F₀
    comps .Functor.F₁ = F₁
    comps .Functor.F-id = F-id
    comps .Functor.F-∘ = F-∘
```

<!--
```agda
{-# DISPLAY F∘.comps F G = F F∘ G #-}
```
-->

The identity functor can be defined using the identity funct*ion* for
both its object and morphism mappings. That functors have an identity
and compose would seem to imply that categories form a category:
However, since there is no upper bound on the h-level of `Ob`{.Agda}, we
can not form a "category of categories". If we _do_ impose a bound,
however, we can obtain a [[category of strict categories]], those which
have a set of objects.

```agda
Id : ∀ {o₁ h₁} {C : Precategory o₁ h₁} → Functor C C
Id .Functor.F₀ x = x
Id .Functor.F₁ f = f
Id .Functor.F-id    = refl
Id .Functor.F-∘ f g = refl
```

# Natural transformations {defines="natural-transformation"}

Another common theme in category theory is that roughly _every_ concept
can be considered the objects of a category. This is the case for
functors, as well! The functors between $C$ and $D$ assemble into a
category, notated $[C, D]$ - the [[functor category]] between $C$ and $D$.

```agda
record _=>_ {o₁ h₁ o₂ h₂}
            {C : Precategory o₁ h₁}
            {D : Precategory o₂ h₂}
            (F G : Functor C D)
      : Type (o₁ ⊔ h₁ ⊔ h₂)
  where
  no-eta-equality
  constructor NT
```

The morphisms between functors are called **natural transformations**. A
natural transformation $F \To G$ can be thought of as a way of turning
$F(x)$s into $G(x)$s that doesn't involve any "arbitrary choices".

```agda
  private
    module F = Functor F
    module G = Functor G
    module D = Precategory D
    module C = Precategory C

  field
    η : (x : _) → D.Hom (F.₀ x) (G.₀ x)
```

The transformation itself is given by `η`{.Agda}, the family of
_components_, where the component at $x$ is a map $F(x) \to G(x)$. The
"without arbitrary choices" part is encoded in the field
`is-natural`{.Agda}, which encodes commutativity of the square below:

~~~{.quiver}
\[\begin{tikzcd}
  {F_0(x)} && {F_0(y)} \\
  \\
  {G_0(x)} && {G_0(y)}
  \arrow["{\eta_x}"', from=1-1, to=3-1]
  \arrow["{\eta_y}", from=1-3, to=3-3]
  \arrow["{F_1(f)}", from=1-1, to=1-3]
  \arrow["{G_1(f)}"', from=3-1, to=3-3]
\end{tikzcd}\]
~~~

```agda
    is-natural : (x y : _) (f : C.Hom x y)
               → η y D.∘ F.₁ f ≡ G.₁ f D.∘ η x
```

Natural transformations also dualise. The opposite of $\eta : F
\To G$ is $\eta\op : G\op \To F\op$.

```agda
  op : Functor.op G => Functor.op F
  op = record
    { η = η
    ; is-natural = λ x y f → sym (is-natural _ _ f)
    }
```

<!--
```agda
{-# INLINE NT #-}

is-natural-transformation
  : ∀ {o ℓ o' ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'}
  → (F G : Functor C D)
  → (η : ∀ x → D .Precategory.Hom (F .Functor.F₀ x) (G .Functor.F₀ x))
  → Type _
is-natural-transformation {C = C} {D = D} F G η =
  ∀ x y (f : C .Precategory.Hom x y) → η y D.∘ F .F₁ f ≡ G .F₁ f D.∘ η x
  where module D = Precategory D
        open Functor

infixr 30 _F∘_
infix 20 _=>_

unquoteDecl H-Level-Nat = declare-record-hlevel 2 H-Level-Nat (quote _=>_)

module _ {o₁ h₁ o₂ h₂}
         {C : Precategory o₁ h₁}
         {D : Precategory o₂ h₂}
         {F G : Functor C D} where
  private
    module F = Functor F
    module G = Functor G
    module D = Precategory D
    module C = Precategory C

  open Functor
  open _=>_
```
-->

Since the type of natural transformations is defined as a record, we can
not _a priori_ reason about its h-level in a convenient way. However,
using Agda's metaprogramming facilities (both reflection _and_ instance
search), we can automatically derive an equivalence between the type of
natural transformations and a certain $\Sigma$ type; This type can then
be shown to be a set using the standard `hlevel`{.Agda} machinery.

```agda
  opaque
    Nat-is-set : is-set (F => G)
    Nat-is-set = hlevel 2
```

Another fundamental lemma is that equality of natural transformations
depends only on equality of the family of morphisms, since being natural
is a proposition:

```agda
  Nat-pathp : {F' G' : Functor C D}
            → (p : F ≡ F') (q : G ≡ G')
            → {a : F => G} {b : F' => G'}
            → (∀ x → PathP _ (a .η x) (b .η x))
            → PathP (λ i → p i => q i) a b
  Nat-pathp p q path i .η x = path x i
  Nat-pathp p q {a} {b} path i .is-natural x y f =
    is-prop→pathp
      (λ i → D.Hom-set _ _
        (path y i D.∘ Functor.F₁ (p i) f) (Functor.F₁ (q i) f D.∘ path x i))
      (a .is-natural x y f)
      (b .is-natural x y f) i

  Nat-path : {a b : F => G}
           → ((x : _) → a .η x ≡ b .η x)
           → a ≡ b
  Nat-path = Nat-pathp refl refl

  _ηₚ_ : ∀ {a b : F => G} → a ≡ b → ∀ x → a .η x ≡ b .η x
  p ηₚ x = ap (λ e → e .η x) p

  _ηᵈ_ : ∀ {F' G' : Functor C D} {p : F ≡ F'} {q : G ≡ G'}
       → {a : F => G} {b : F' => G'}
       → PathP (λ i → p i => q i) a b
       → ∀ x → PathP (λ i → D.Hom (p i .F₀ x) (q i .F₀ x)) (a .η x) (b .η x)
  p ηᵈ x = apd (λ i e → e .η x) p

  infixl 45 _ηₚ_
```

<!--
```agda
open Precategory
open _=>_

instance
  Underlying-Precategory : ∀ {o ℓ} → Underlying (Precategory o ℓ)
  Underlying-Precategory = record { ⌞_⌟ = Precategory.Ob }

  Funlike-Functor
    : ∀ {o ℓ o' ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'}
    → Funlike (Functor C D) ⌞ C ⌟ (λ x → ⌞ D ⌟)
  Funlike-Functor = record { _#_ = Functor.F₀ }

  Funlike-natural-transformation
    : ∀ {o ℓ o' ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'} {F G : Functor C D}
    → Funlike (F => G) ⌞ C ⌟ (λ x → D .Precategory.Hom (F # x) (G # x))
  Funlike-natural-transformation = record { _#_ = _=>_.η }

  Extensional-natural-transformation
    : ∀ {o ℓ o' ℓ' ℓr} {C : Precategory o ℓ} {D : Precategory o' ℓ'}
    → {F G : Functor C D}
    → ⦃ sa : {x : ⌞ C ⌟} → Extensional (D .Hom (F # x) (G # x)) ℓr ⦄
    → Extensional (F => G) (o ⊔ ℓr)
  Extensional-natural-transformation ⦃ sa ⦄ .Pathᵉ f g = ∀ i → Pathᵉ sa (f .η i) (g .η i)
  Extensional-natural-transformation ⦃ sa ⦄ .reflᵉ x i = reflᵉ sa (x .η i)
  Extensional-natural-transformation ⦃ sa ⦄ .idsᵉ .to-path x = Nat-path λ i →
    sa .idsᵉ .to-path (x i)
  Extensional-natural-transformation {D = D} ⦃ sa ⦄ .idsᵉ .to-path-over h =
    is-prop→pathp (λ i → Π-is-hlevel 1 λ _ → Pathᵉ-is-hlevel 1 sa (hlevel 2)) _ _

_⟪_⟫_
  : ∀ {o ℓ o' ℓ'} {C : Precategory o ℓ} {D : Precategory o' ℓ'}
  → (F : Functor C D) {U V : ⌞ C ⌟}
  → C .Precategory.Hom U V
  → D .Precategory.Hom (F # U) (F # V)
_⟪_⟫_ F f = Functor.F₁ F f
```
-->
