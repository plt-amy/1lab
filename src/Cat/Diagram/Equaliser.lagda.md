<!--
```agda
open import Cat.Prelude

import Cat.Reasoning
```
-->

```agda
module Cat.Diagram.Equaliser where
```

<!--
```agda
module _ {o ℓ} (C : Precategory o ℓ) where
  open Cat.Reasoning C
  private variable
    A B : Ob
    f g h : Hom A B
```
-->

# Equalisers {defines=equaliser}

The **equaliser** of two maps $f, g : A \to B$, when it exists,
represents the largest subobject of $A$ where $f$ and $g$ agree. In this
sense, the equaliser is the categorical generalisation of a _solution
set_: The solution set of an equation in one variable is largest subset
of the domain (i.e. what the variable ranges over) where the left- and
right-hand-sides agree.

```agda
  record is-equaliser {E} (f g : Hom A B) (equ : Hom E A) : Type (o ⊔ ℓ) where
    field
      equal     : f ∘ equ ≡ g ∘ equ
      universal : ∀ {F} {e' : Hom F A} (p : f ∘ e' ≡ g ∘ e') → Hom F E
      factors   : ∀ {F} {e' : Hom F A} {p : f ∘ e' ≡ g ∘ e'} → equ ∘ universal p ≡ e'
      unique
        : ∀ {F} {e' : Hom F A} {p : f ∘ e' ≡ g ∘ e'} {other : Hom F E}
        → equ ∘ other ≡ e'
        → other ≡ universal p

    equal-∘ : f ∘ equ ∘ h ≡ g ∘ equ ∘ h
    equal-∘ {h = h} =
      f ∘ equ ∘ h ≡⟨ extendl equal ⟩
      g ∘ equ ∘ h ∎

    unique₂
      : ∀ {F} {e' : Hom F A}  {o1 o2 : Hom F E}
      → f ∘ e' ≡ g ∘ e'
      → equ ∘ o1 ≡ e'
      → equ ∘ o2 ≡ e'
      → o1 ≡ o2
    unique₂ p q r = unique {p = p} q ∙ sym (unique r)
```

We can visualise the situation using the commutative diagram below:

~~~{.quiver}
\[\begin{tikzcd}
  E & A & B \\
  F
  \arrow["f", shift left=1, from=1-2, to=1-3]
  \arrow["g"', shift right=1, from=1-2, to=1-3]
  \arrow["{\rm{equ}}", hook, from=1-1, to=1-2]
  \arrow["{\exists!}", dashed, from=2-1, to=1-1]
  \arrow["e\prime"', from=2-1, to=1-2]
\end{tikzcd}\]
~~~

There is also a convenient bundling of an equalising arrow together with
its domain:

```agda
  record Equaliser (f g : Hom A B) : Type (o ⊔ ℓ) where
    field
      {apex}  : Ob
      equ     : Hom apex A
      has-is-eq : is-equaliser f g equ

    open is-equaliser has-is-eq public
```

## Equalisers are monic

As a small initial application, we prove that equaliser arrows are
always [[monic]]:

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} where
  open Cat.Reasoning C
  private variable
    A B : Ob
    f g h : Hom A B
```
-->

```agda
  is-equaliser→is-monic
    : ∀ {E} (equ : Hom E A)
    → is-equaliser C f g equ
    → is-monic equ
  is-equaliser→is-monic equ equalises g h p =
    unique₂ (extendl equal) p refl
    where open is-equaliser equalises
```

## Uniqueness

As universal constructions, equalisers are unique up to isomorphism.
The proof follows the usual pattern: if $E, E'$ both equalise $f, g : A \to B$,
then we can construct maps between $E$ and $E'$ via the universal property
of equalisers, and uniqueness ensures that these maps form an isomorphism.

```agda
  is-equaliser→iso
    : {E E' : Ob}
    → {e : Hom E A} {e' : Hom E' A}
    → is-equaliser C f g e
    → is-equaliser C f g e'
    → E ≅ E'
  is-equaliser→iso {e = e} {e' = e'} eq eq' =
    make-iso (eq' .universal (eq .equal)) (eq .universal (eq' .equal))
      (unique₂ eq' (eq' .equal) (pulll (eq' .factors) ∙ eq .factors) (idr _))
      (unique₂ eq (eq .equal) (pulll (eq .factors) ∙ eq' .factors) (idr _))
    where open is-equaliser
```

## Properties of equalisers

The equaliser of the pair $(f, f) : A \to B$ always exists, and is given
by the identity map $\id : A \to A$.

```agda
  id-is-equaliser : is-equaliser C f f id
  id-is-equaliser .is-equaliser.equal = refl
  id-is-equaliser .is-equaliser.universal {e' = e'} _ = e'
  id-is-equaliser .is-equaliser.factors = idl _
  id-is-equaliser .is-equaliser.unique p = sym (idl _) ∙ p
```

If $e : E \to A$ is an equaliser and an [[epimorphism]], then $e$ is
an iso.

```agda
  equaliser+epi→invertible
    : ∀ {E} {e : Hom E A}
    → is-equaliser C f g e
    → is-epic e
    → is-invertible e
```

Suppose that $e$ equalises some pair $(f, g) : A \to B$. By definition,
this means that $f \circ e = g \circ e$; however, $e$ is an epi, so
$f = g$. This in turn means that $\id : A \to A$ can be extended into
a map $A \to E$ via the universal property of $e$, and universality
ensures that this extension is an isomorphism!

```agda
  equaliser+epi→invertible {f = f} {g = g} {e = e} e-equaliser e-epi =
    make-invertible
      (universal {e' = id} (ap₂ _∘_ f≡g refl))
      factors
      (unique₂ (ap₂ _∘_ f≡g refl) (pulll factors) id-comm)
    where
      open is-equaliser e-equaliser
      f≡g : f ≡ g
      f≡g = e-epi f g equal
```


# Categories with all equalisers

We also define a helper module for working with categories that have
equalisers of all parallel pairs of morphisms.


```agda
record Equalisers {o ℓ} (C : Precategory o ℓ) : Type (o ⊔ ℓ) where
  no-eta-equality
  open Cat.Reasoning C
  field
    Eq : ∀ {X Y} → Hom X Y → Hom X Y → Ob
    equ : ∀ {X Y} → (f g : Hom X Y) → Hom (Eq f g) X
    equal : ∀ {X Y} {f g : Hom X Y} → f ∘ equ f g ≡ g ∘ equ f g
    equate
      : ∀ {E X Y} {f g : Hom X Y}
      → (e : Hom E X)
      → f ∘ e ≡ g ∘ e
      → Hom E (Eq f g)
    equ∘equate
      : ∀ {E X Y} {f g : Hom X Y}
      → {e : Hom E X} {p : f ∘ e ≡ g ∘ e}
      → equ f g ∘ equate e p ≡ e
    equate-unique
      : ∀ {E X Y} {f g : Hom X Y}
      → {e : Hom E X} {p : f ∘ e ≡ g ∘ e}
      → {other : Hom E (Eq f g)}
      → equ f g ∘ other ≡ e
      → other ≡ equate e p
```

<!--
```agda
  equaliser : ∀ {X Y} (f g : Hom X Y) → Equaliser C f g
  equaliser f g .Equaliser.apex = Eq f g
  equaliser f g .Equaliser.equ = equ f g
  equaliser f g .Equaliser.has-is-eq .is-equaliser.equal = equal
  equaliser f g .Equaliser.has-is-eq .is-equaliser.universal = equate _
  equaliser f g .Equaliser.has-is-eq .is-equaliser.factors = equ∘equate
  equaliser f g .Equaliser.has-is-eq .is-equaliser.unique = equate-unique

  private module equaliser {X Y} {f g : Hom X Y} = Equaliser (equaliser f g)
  open equaliser
    using (has-is-eq; equal-∘)
    renaming (unique₂ to equate-unique₂)
    public

to-equalisers
  : ∀ {o ℓ} {C : Precategory o ℓ}
  → (let open Precategory C)
  → (∀ {X Y} → (f g : Hom X Y) → Equaliser C f g)
  → Equalisers C
to-equalisers {C = C} has-equalisers = equalisers where
  open Precategory C
  module eq {X Y} {f g : Hom X Y} = Equaliser (has-equalisers f g)
  open Equalisers

  equalisers : Equalisers C
  equalisers .Eq f g = eq.apex {f = f} {g = g}
  equalisers .equ _ _ = eq.equ
  equalisers .equal = eq.equal
  equalisers .equate _ = eq.universal
  equalisers .equ∘equate = eq.factors
  equalisers .equate-unique = eq.unique
```
-->
