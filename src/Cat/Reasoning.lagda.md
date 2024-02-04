<!--
```agda
open import 1Lab.Path
open import 1Lab.Type hiding (id; _∘_)

open import Cat.Base
```
-->

```agda
module Cat.Reasoning {o ℓ} (C : Precategory o ℓ) where

open import Cat.Morphism C public
```

# Reasoning combinators for categories

When doing category theory, we often have to perform many "trivial"
algebraic manipulations like reassociation, insertion of identity morphisms, etc.
On paper we can omit these steps, but Agda is a bit more picky!
We could just do these steps in our proofs one after another, but this
clutters things up. Instead, we provide a series of reasoning combinators
to make writing (and reading) proofs easier.

Most of these helpers were taken from `agda-categories`.

<!--
```agda
private variable
  u v w x y z : Ob
  a a' a'' b b' b'' c c' c'' d d' d'' : Hom x y
  f g h i : Hom x y
```
-->

## Identity morphisms

```agda
id-comm : ∀ {a b} {f : Hom a b} → f ∘ id ≡ id ∘ f
id-comm {f = f} = idr f ∙ sym (idl f)

id-comm-sym : ∀ {a b} {f : Hom a b} → id ∘ f ≡ f ∘ id
id-comm-sym {f = f} = idl f ∙ sym (idr f)

idr2 : ∀ {a b c} (f : Hom b c) (g : Hom a b) → f ∘ g ∘ id ≡ f ∘ g
idr2 f g = ap (f ∘_) (idr g)

module _ (a≡id : a ≡ id) where abstract
  eliml : a ∘ f ≡ f
  eliml {f = f} =
    a ∘ f ≡⟨ ap (_∘ f) a≡id ⟩
    id ∘ f ≡⟨ idl f ⟩
    f ∎

  elimr : f ∘ a ≡ f
  elimr {f = f} =
    f ∘ a ≡⟨ ap (f ∘_) a≡id ⟩
    f ∘ id ≡⟨ idr f ⟩
    f ∎

  elim-inner : f ∘ a ∘ h ≡ f ∘ h
  elim-inner {f = f} = ap (f ∘_) eliml

  introl : f ≡ a ∘ f
  introl = sym eliml

  intror : f ≡ f ∘ a
  intror = sym elimr

  intro-inner : f ∘ h ≡ f ∘ a ∘ h
  intro-inner {f = f} = ap (f ∘_) introl
```

## Reassocations

We often find ourselves in situations where we have an equality
involving the composition of 2 morphisms, but the association
is a bit off. These combinators aim to address that situation.

```agda
module _ (ab≡c : a ∘ b ≡ c) where abstract
  pulll : a ∘ (b ∘ f) ≡ c ∘ f
  pulll {f = f} =
    a ∘ b ∘ f   ≡⟨ assoc a b f ⟩
    (a ∘ b) ∘ f ≡⟨ ap (_∘ f) ab≡c ⟩
    c ∘ f ∎

  pullr : (f ∘ a) ∘ b ≡ f ∘ c
  pullr {f = f} =
    (f ∘ a) ∘ b ≡˘⟨ assoc f a b ⟩
    f ∘ (a ∘ b) ≡⟨ ap (f ∘_) ab≡c ⟩
    f ∘ c ∎

  pull-inner : (f ∘ a) ∘ (b ∘ g) ≡ f ∘ c ∘ g
  pull-inner {f = f} = sym (assoc _ _ _) ∙ ap (f ∘_) pulll

module _ (c≡ab : c ≡ a ∘ b) where abstract
  pushl : c ∘ f ≡ a ∘ (b ∘ f)
  pushl = sym (pulll (sym c≡ab))

  pushr : f ∘ c ≡ (f ∘ a) ∘ b
  pushr = sym (pullr (sym c≡ab))

  push-inner : f ∘ c ∘ g ≡ (f ∘ a) ∘ (b ∘ g)
  push-inner {f = f} = ap (f ∘_) pushl ∙ assoc _ _ _

module _ (p : f ∘ h ≡ g ∘ i) where abstract
  extendl : f ∘ (h ∘ b) ≡ g ∘ (i ∘ b)
  extendl {b = b} =
    f ∘ (h ∘ b) ≡⟨ assoc f h b ⟩
    (f ∘ h) ∘ b ≡⟨ ap (_∘ b) p ⟩
    (g ∘ i) ∘ b ≡˘⟨ assoc g i b ⟩
    g ∘ (i ∘ b) ∎

  extendr : (a ∘ f) ∘ h ≡ (a ∘ g) ∘ i
  extendr {a = a} =
    (a ∘ f) ∘ h ≡˘⟨ assoc a f h ⟩
    a ∘ (f ∘ h) ≡⟨ ap (a ∘_) p ⟩
    a ∘ (g ∘ i) ≡⟨ assoc a g i ⟩
    (a ∘ g) ∘ i ∎

  extend-inner : a ∘ f ∘ h ∘ b ≡ a ∘ g ∘ i ∘ b
  extend-inner {a = a} = ap (a ∘_) extendl
```

We also define some useful combinators for performing repeated pulls/pushes.

```agda
abstract
  centralize
    : f ∘ g ≡ a ∘ b
    → h ∘ i ≡ c ∘ d
    → f ∘ g ∘ h ∘ i ≡ a ∘ (b ∘ c) ∘ d
  centralize {f = f} {g = g} {a = a} {b = b} {h = h} {i = i} {c = c} {d = d} p q =
    f ∘ g ∘ h ∘ i   ≡⟨ pulll p ⟩
    (a ∘ b) ∘ h ∘ i ≡⟨ pullr (pushr q) ⟩
    a ∘ (b ∘ c) ∘ d ∎
  
  centralizel
    : f ∘ g ≡ a ∘ b
    → f ∘ g ∘ h ∘ i ≡ a ∘ (b ∘ h) ∘ i
  centralizel p = centralize p refl
  
  centralizer
    : h ∘ i ≡ c ∘ d
    → f ∘ g ∘ h ∘ i ≡ f ∘ (g ∘ c) ∘ d
  centralizer p = centralize refl p

  disperse
    : f ∘ g ≡ a ∘ b
    → h ∘ i ≡ c ∘ d
    → f ∘ (g ∘ h) ∘ i ≡ a ∘ b ∘ c ∘ d
  disperse {f = f} {g = g} {a = a} {b = b} {h = h} {i = i} {c = c} {d = d} p q =
    f ∘ (g ∘ h) ∘ i ≡⟨ pushr (pullr q) ⟩
    (f ∘ g) ∘ c ∘ d ≡⟨ pushl p ⟩
    a ∘ b ∘ c ∘ d ∎

  dispersel
    : f ∘ g ≡ a ∘ b
    → f ∘ (g ∘ h) ∘ i ≡ a ∘ b ∘ h ∘ i
  dispersel p = disperse p refl

  disperser
    : h ∘ i ≡ c ∘ d
    → f ∘ (g ∘ h) ∘ i ≡ f ∘ g ∘ c ∘ d
  disperser p = disperse refl p
```

## Cancellation

These lemmas do 2 things at once: rearrange parenthesis, and also remove
things that are equal to `id`.

```agda
module _ (inv : h ∘ i ≡ id) where abstract
  cancell : h ∘ (i ∘ f) ≡ f
  cancell {f = f} =
    h ∘ (i ∘ f) ≡⟨ pulll inv ⟩
    id ∘ f      ≡⟨ idl f ⟩
    f           ∎

  cancelr : (f ∘ h) ∘ i ≡ f
  cancelr {f = f} =
    (f ∘ h) ∘ i ≡⟨ pullr inv ⟩
    f ∘ id      ≡⟨ idr f ⟩
    f           ∎

  insertl : f ≡ h ∘ (i ∘ f)
  insertl = sym cancell

  insertr : f ≡ (f ∘ h) ∘ i
  insertr = sym cancelr

  cancel-inner : (f ∘ h) ∘ (i ∘ g) ≡ f ∘ g
  cancel-inner = pulll cancelr

  insert-inner : f ∘ g ≡ (f ∘ h) ∘ (i ∘ g)
  insert-inner = pushl insertr

  deleter : (f ∘ g ∘ h) ∘ i ≡ f ∘ g
  deleter = pullr cancelr

  deletel : h ∘ (i ∘ f) ∘ g ≡ f ∘ g
  deletel = pulll cancell
```

We also have combinators which combine expanding on one side with a
cancellation on the other side:

```agda
lswizzle : g ≡ h ∘ i → f ∘ h ≡ id → f ∘ g ≡ i
lswizzle {g = g} {h = h} {i = i} {f = f} p q =
  f ∘ g     ≡⟨ ap₂ _∘_ refl p ⟩
  f ∘ h ∘ i ≡⟨ cancell q ⟩
  i         ∎

rswizzle : g ≡ i ∘ h → h ∘ f ≡ id → g ∘ f ≡ i
rswizzle {g = g} {i = i} {h = h} {f = f} p q =
  g ∘ f       ≡⟨ ap₂ _∘_ p refl ⟩
  (i ∘ h) ∘ f ≡⟨ cancelr q ⟩
  i           ∎
```

## Isomorphisms

These lemmas are useful for proving that partial inverses to an
isomorphism are unique. There's a helper for proving uniqueness of left
inverses, of right inverses, and for proving that any left inverse must
match any right inverse.

```agda
module _ {y z} (f : y ≅ z) where abstract
  open _≅_

  left-inv-unique
    : ∀ {g h}
    → g ∘ f .to ≡ id → h ∘ f .to ≡ id
    → g ≡ h
  left-inv-unique {g = g} {h = h} p q =
    g                   ≡⟨ intror (f .invl) ⟩
    g ∘ f .to ∘ f .from ≡⟨ extendl (p ∙ sym q) ⟩
    h ∘ f .to ∘ f .from ≡⟨ elimr (f .invl) ⟩
    h                   ∎

  left-right-inv-unique
    : ∀ {g h}
    → g ∘ f .to ≡ id → f .to ∘ h ≡ id
    → g ≡ h
  left-right-inv-unique {g = g} {h = h} p q =
    g                    ≡⟨ intror (f .invl) ⟩
    g ∘ f .to ∘ f .from  ≡⟨ cancell p ⟩
    f .from              ≡⟨ intror q ⟩
    f .from ∘ f .to ∘ h  ≡⟨ cancell (f .invr) ⟩
    h                    ∎

  right-inv-unique
    : ∀ {g h}
    → f .to ∘ g ≡ id → f .to ∘ h ≡ id
    → g ≡ h
  right-inv-unique {g = g} {h} p q =
    g                     ≡⟨ introl (f .invr) ⟩
    (f .from ∘ f .to) ∘ g ≡⟨ pullr (p ∙ sym q) ⟩
    f .from ∘ f .to ∘ h   ≡⟨ cancell (f .invr) ⟩
    h                     ∎
```

If we have a commuting triangle of isomorphisms, then we
can flip one of the sides to obtain a new commuting triangle
of isomorphisms.

```agda
Iso-swapr :
  ∀ {a : x ≅ y} {b : y ≅ z} {c : x ≅ z}
  → a ∘Iso b ≡ c
  → a ≡ c ∘Iso (b Iso⁻¹)
Iso-swapr {a = a} {b = b} {c = c} p = ≅-path $
  a .to                     ≡⟨ introl (b .invr) ⟩
  (b .from ∘ b .to) ∘ a .to ≡⟨ pullr (ap to p) ⟩
  b .from ∘ c .to           ∎

Iso-swapl :
  ∀ {a : x ≅ y} {b : y ≅ z} {c : x ≅ z}
  → a ∘Iso b ≡ c
  → b ≡ (a Iso⁻¹) ∘Iso c
Iso-swapl {a = a} {b = b} {c = c} p = ≅-path $
  b .to                   ≡⟨ intror (a .invl) ⟩
  b .to ∘ a .to ∘ a .from ≡⟨ pulll (ap to p) ⟩
  c .to ∘ a .from         ∎
```

Assume we have a prism of isomorphisms, as in the following diagram:

~~~{.quiver}
\begin{tikzcd}
  & v \\
  u && w \\
  & y \\
  x && z
  \arrow["c"{description, pos=0.7}, from=2-1, to=2-3]
  \arrow["i"{description}, from=4-1, to=4-3]
  \arrow["d"{description}, from=2-1, to=4-1]
  \arrow["f"{description}, from=2-3, to=4-3]
  \arrow["a"{description}, from=2-1, to=1-2]
  \arrow["g"{description}, from=4-1, to=3-2]
  \arrow["e"{description, pos=0.7}, from=1-2, to=3-2]
  \arrow["b"{description}, from=1-2, to=2-3]
  \arrow["h"{description}, from=3-2, to=4-3]
\end{tikzcd}
~~~

If the top, front, left, and right faces all commute, then so does the
bottom face.

```agda
Iso-prism : ∀ {a : u ≅ v} {b : v ≅ w} {c : u ≅ w}
      → {d : u ≅ x} {e : v ≅ y} {f : w ≅ z}
      → {g : x ≅ y} {h : y ≅ z} {i : x ≅ z}
      → a ∘Iso b ≡ c
      → a ∘Iso e ≡ d ∘Iso g
      → b ∘Iso f ≡ e ∘Iso h
      → c ∘Iso f ≡ d ∘Iso i
      → g ∘Iso h ≡ i
Iso-prism {a = a} {b} {c} {d} {e} {f} {g} {h} {i} top left right front =
  ≅-path $
    h .to ∘ g .to                                           ≡⟨ ap₂ _∘_ (ap to (Iso-swapl (sym right))) (ap to (Iso-swapl (sym left)) ∙ sym (assoc _ _ _)) ⟩
    ((f .to ∘ b .to) ∘ e .from) ∘ (e .to ∘ a .to ∘ d .from) ≡⟨ cancel-inner (e .invr) ⟩
    (f .to ∘ b .to) ∘ (a .to ∘ d .from)                     ≡⟨ pull-inner (ap to top) ⟩
    f .to ∘ c .to ∘ d .from                                 ≡⟨ assoc _ _ _ ∙ sym (ap to (Iso-swapl (sym front))) ⟩
    i .to ∎
```


## Notation

When doing equational reasoning, it's often somewhat clumsy to have to write
`ap (f ∘_) p` when proving that `f ∘ g ≡ f ∘ h`. To fix this, we steal
some cute mixfix notation from `agda-categories` which allows us to write
`≡⟨ refl⟩∘⟨ p ⟩` instead, which is much more aesthetically pleasing!

```agda
_⟩∘⟨_ : f ≡ h → g ≡ i → f ∘ g ≡ h ∘ i
_⟩∘⟨_ = ap₂ _∘_

infixr 40 _⟩∘⟨_

refl⟩∘⟨_ : g ≡ h → f ∘ g ≡ f ∘ h
refl⟩∘⟨_ {f = f} p = ap (f ∘_) p

_⟩∘⟨refl : f ≡ h → f ∘ g ≡ h ∘ g
_⟩∘⟨refl {g = g} p = ap (_∘ g) p
```
