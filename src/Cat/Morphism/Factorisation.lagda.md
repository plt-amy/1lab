<!--
```agda
open import Cat.Morphism.Orthogonal
open import Cat.Prelude

open import Data.Power

import Cat.Reasoning
```
-->

```agda
module Cat.Morphism.Factorisation where
```

# Orthogonal factorisation systems {defines="orthogonal-factorisation-system"}

Suppose you have some category $\cC$ and you, inspired by the wisdom
of King Solomon, want to chop every morphism in half. A **factorisation
system** $(E, M)$ on $\cC$ will provide a tool for doing so, in a
particularly coherent way. Here, $E$ and $M$ are predicates on the space
of morphisms of $C$. First, we package the data of an $(E,
M)$-factorisation of a morphism $f : a \to b$.

<!--
```agda
module _ {o ℓ} (C : Precategory o ℓ)
         (E : ∀ {a b} → C .Precategory.Hom a b → Ω)
         (M : ∀ {a b} → C .Precategory.Hom a b → Ω) where
  private module C = Cat.Reasoning C
```
-->

Note that while the archetype for a factorisation system is the (epi,
mono)-factorisation system on the category of sets^[Or, more generally,
in every topos.], so that it's very hard _not_ to refer to these things
as images, it is _not_ the case, in general, nothing is required about
the interaction of epis and monos with the classes $E$ and $M$.
Generically, we call the $E$-morphism in the factorisation
`mediate`{.Agda}, and the $M$-morphism `forget`{.Agda}.

```agda
  record Factorisation {a b} (f : C.Hom a b) : Type (o ⊔ ℓ) where
    field
      mediating : C.Ob
      mediate   : C.Hom a mediating
      forget    : C.Hom mediating b
      mediate∈E : mediate ∈ E
      forget∈M  : forget ∈ M
      factors   : f ≡ forget C.∘ mediate
```

In addition to mandating that every map $f : a \to b$ factors as a map
$f : a \xto{e} r(f) \xto{m}$ where $e \in E$ and $m \in M$, the classes
must satisfy the following properties:

- Every isomorphism is in both $E$ and in $M$.^[We'll see, in a bit, that
the converse is true, too.]

- Both classes are stable under composition: if $f \in E$ and $g \in E$,
then $(g \circ f) \in E$ and the same for $M$

```agda
  record is-factorisation-system : Type (o ⊔ ℓ) where
    field
      factor : ∀ {a b} (f : C.Hom a b) → Factorisation f

      is-iso→in-E : ∀ {a b} (f : C.Hom a b) → C.is-invertible f → f ∈ E
      E-is-stable
        : ∀ {a b c} (g : C.Hom b c) (f : C.Hom a b) → f ∈ E → g ∈ E
        → (g C.∘ f) ∈ E

      is-iso→in-M : ∀ {a b} (f : C.Hom a b) → C.is-invertible f → f ∈ M
      M-is-stable
        : ∀ {a b c} (g : C.Hom b c) (f : C.Hom a b) → f ∈ M → g ∈ M
        → (g C.∘ f) ∈ M
```

Most importantly, the class $E$ is exactly the class of morphisms
left-orthogonal to $M$: A map satisfies $f \in E$ if, and only if, for
every $g \in M$, we have $f \ortho g$. Conversely, a map has $g \in M$
if, and only if, we have $f \ortho g$ for every $f \in E$.

```agda
      E⊥M : ∀ {a b c d} (f : C.Hom a b) (g : C.Hom c d) → f ∈ E → g ∈ M
          → m⊥m C f g
```

<!--
```agda
module
  _ {o ℓ} {C : Precategory o ℓ} {E M : ∀ {a b} → ℙ (C .Precategory.Hom a b)}
    where

  private module C = Cat.Reasoning C
  open Factorisation
```
-->

The first thing we observe is that factorisations for a morphism are
unique. Working in precategorical generality, we weaken this to
essential uniqueness: Given two factorisations of $f$ we exhibit an
isomorphism between their replacements $r(f)$, $r'(f)$ which commutes
with both the `mediate`{.Agda} morphism and the `forget`{.Agda}
morphism. We reproduce the proof from [@Borceux:vol1, §5.5].

```agda
  is-essentially-unique-factorisation
    : ∀ {a b} (f : C.Hom a b) (fa : Factorisation C E M f)
    → Type _
  is-essentially-unique-factorisation f fa =
    ∀ (fa' : Factorisation C E M f)
    → Σ[ f ∈ fa .mediating C.≅ fa' .mediating ]
        ( (f .C.to C.∘ fa .mediate ≡ fa' .mediate)
        × (fa .forget C.∘ f .C.from ≡ fa' .forget))
```

<!--
```agda
module
  _ {o ℓ} (C : Precategory o ℓ) (E M : ∀ {a b} → ℙ (C .Precategory.Hom a b))
    (fs : is-factorisation-system C E M)
    where

  private module C = Cat.Reasoning C
  open is-factorisation-system fs
  open Factorisation
```
-->

```agda
  factorisation-essentially-unique
    : ∀ {a b} (f : C.Hom a b) (fa : Factorisation C E M f)
    → is-essentially-unique-factorisation f fa
  factorisation-essentially-unique f fa1 fa2 =
    C.make-iso (upq .fst) (vp'q' .fst) vu=id uv=id , upq .snd .fst , vp'q' .snd .snd
    where
```

Suppose that $f = m \circ e$ and $f = m' \circ e'$ are both
$(E,M)$-factorisations of $f$. We use the fact that $e \ortho m'$ and
$e' \ortho m$ to get maps $u, v$ satisfying $um = m'$, $m'u = m$, $ve =
e'$, and $e'v = e$.

```agda
      module fa1 = Factorisation fa1
      module fa2 = Factorisation fa2

      upq = E⊥M fa1.mediate fa2.forget fa1.mediate∈E fa2.forget∈M
        (sym fa1.factors ∙ fa2.factors) .centre

      vp'q' = E⊥M fa2.mediate fa1.forget fa2.mediate∈E fa1.forget∈M
        (sym fa2.factors ∙ fa1.factors) .centre
```

To show that $u$ and $v$ are inverses, fit first $e$ and $m$ into a
lifting diagram like the one below. Since $e \ortho m$, we have that the
space of diagonals $r(f) \to r(f)$ is contractible, hence a proposition,
and since both $vu$ and the identity are in that diagonal, $uv =
\id$.

~~~{.quiver}
\[\begin{tikzcd}
  a && {r(f)} \\
  \\
  {r(f)} && b
  \arrow["e", from=1-1, to=1-3]
  \arrow["m"', from=3-1, to=3-3]
  \arrow["e"', from=1-1, to=3-1]
  \arrow["m", from=1-3, to=3-3]
	\arrow["{\mathrm{id}}"', shift right=1, from=1-3, to=3-1]
	\arrow["vu", shift left=1, from=1-3, to=3-1]
\end{tikzcd}\]
~~~

```agda
      vu=id : upq .fst C.∘ vp'q' .fst ≡ C.id
      vu=id = ap fst $ is-contr→is-prop
        (E⊥M fa2.mediate fa2.forget fa2.mediate∈E fa2.forget∈M refl)
        ( upq .fst C.∘ vp'q' .fst
        , C.pullr (vp'q' .snd .fst) ∙ upq .snd .fst
        , C.pulll (upq .snd .snd) ∙ vp'q' .snd .snd
        ) (C.id , C.idl _ , C.idr _)
```

A dual argument works by making a lifting square with $e'$ and $m'$ as
its faces. We omit it for brevity.  By the characterisation of path
spaces in categories, this implies that factorisations of a fixed
morphism are a proposition.

<!--
```agda
      uv=id : vp'q' .fst C.∘ upq .fst ≡ C.id
      uv=id = ap fst $ is-contr→is-prop
        (E⊥M fa1.mediate fa1.forget fa1.mediate∈E fa1.forget∈M refl)
        ( vp'q' .fst C.∘ upq .fst
        , C.pullr (upq .snd .fst) ∙ vp'q' .snd .fst
        , C.pulll (vp'q' .snd .snd) ∙ upq .snd .snd
        ) (C.id , C.idl _ , C.idr _)
```
-->

```agda
  factorisation-unique
    : ∀ {a b} (f : C.Hom a b) → is-category C → is-prop (Factorisation C E M f)
  factorisation-unique f c-cat x y = go where
    isop1p2 = factorisation-essentially-unique f x y

    p = Univalent.Hom-pathp-reflr-iso c-cat {q = isop1p2 .fst} (isop1p2 .snd .fst)
    q = Univalent.Hom-pathp-refll-iso c-cat {p = isop1p2 .fst} (isop1p2 .snd .snd)

    go : x ≡ y
    go i .mediating = c-cat .to-path (isop1p2 .fst) i
    go i .mediate = p i
    go i .forget = q i
```

<!--
```agda
    go i .mediate∈E = is-prop→pathp (λ i → E (p i) .is-tr) (x .mediate∈E) (y .mediate∈E) i
    go i .forget∈M = is-prop→pathp (λ i → M (q i) .is-tr) (x .forget∈M) (y .forget∈M) i
    go i .factors =
      is-prop→pathp (λ i → C.Hom-set _ _ f (q i C.∘ p i)) (x .factors) (y .factors) i
```
-->

As a passing observation, note that the intersection $E \cap M$ is
precisely the class of isomorphisms of $f$. Every isomorphism is in both
classes, by the definition, and if a morphism is in both classes, it is
orthogonal to itself, hence an isomorphism.

```agda
  in-intersection→is-iso
    : ∀ {a b} (f : C.Hom a b) → f ∈ E → f ∈ M → C.is-invertible f
  in-intersection→is-iso f f∈E f∈M = self-orthogonal→is-iso C f $ E⊥M f f f∈E f∈M

  in-intersection≃is-iso
    : ∀ {a b} (f : C.Hom a b) → C.is-invertible f ≃ ((f ∈ E) × (f ∈ M))
  in-intersection≃is-iso f = prop-ext!
    (λ fi → is-iso→in-E f fi , is-iso→in-M f fi)
    λ { (a , b) → in-intersection→is-iso f a b }
```

The final observation is that the class $E$ is precisely $^\bot M$, the
class of morphisms left-orthogonal to those in $M$. One direction is by
definition, and the other is rather technical. Let's focus on the
technical one.

```agda
  E-is-⊥M
    : ∀ {a b} (f : C.Hom a b)
    → (f ∈ E) ≃ (∀ {c d} (m : C.Hom c d) → m ∈ M → m⊥m C f m)
  E-is-⊥M f =
    prop-ext (E f .is-tr) (hlevel 1) (λ m f∈E m∈M → to f∈E m m∈M) from
    where
      to : ∀ {c d} (m : C.Hom c d) → f ∈ E → m ∈ M → m⊥m C f m
      to m f∈E m∈M {u} {v} square = E⊥M f m f∈E m∈M square

      from : (∀ {c d} (m : C.Hom c d) → m ∈ M → m⊥m C f m) → f ∈ E
      from ortho = subst (_∈ E) (sym fa.factors) $ E-is-stable _ _ fa.mediate∈E m∈E
        where
```

Suppose that $f$ is left-orthogonal to every $m \in M$, and write out
the $(E,M)$-factorisation $f = m \circ e$. By a syntactic limitation in
Agda, we start with the conclusion: We'll show that $m$ is in $E$, and
since $E$ is closed under composition, so is $f$.  Since $f$ is
orthogonal to $m$, we can fit it into a lifting diagram

~~~{.quiver}
\[\begin{tikzcd}
  A && B \\
  \\
  {r(f)} && {B\text{,}}
  \arrow["f", from=1-1, to=1-3]
  \arrow["g", dashed, from=1-3, to=3-1]
  \arrow["e"', from=1-1, to=3-1]
  \arrow[from=1-3, to=3-3]
  \arrow["m", from=3-1, to=3-3]
\end{tikzcd}\]
~~~

and make note of the diagonal filler $g : B \to r(f)$, and that it
satisfies $gf=e$ and $mg = \id$.

```agda
        fa = factor f
        module fa = Factorisation fa
        gpq = ortho fa.forget fa.forget∈M {v = C.id} (C.idl _ ∙ fa.factors)
```

We'll show $gm = \id$ by fitting it into a lifting diagram. But
since $e \ortho m$, the factorisation is unique, and $gm = \id$, as
needed.

~~~{.quiver}
\[\begin{tikzcd}
  A && {r(f)} \\
  \\
  {r(f)} && B
  \arrow["e", from=1-1, to=1-3]
  \arrow["m", from=1-3, to=3-3]
  \arrow["m"', from=3-1, to=3-3]
  \arrow["e"', from=1-1, to=3-1]
  \arrow["gm"', shift right=1, from=1-3, to=3-1]
  \arrow["id", shift left=1, from=1-3, to=3-1]
\end{tikzcd}\]
~~~

```agda
        gm=id : gpq .centre .fst C.∘ fa.forget ≡ C.id
        gm=id = ap fst $ is-contr→is-prop
          (E⊥M fa.mediate fa.forget fa.mediate∈E fa.forget∈M refl)
          ( _ , C.pullr (sym fa.factors) ∙ gpq .centre .snd .fst
          , C.cancell (gpq .centre .snd .snd)) (C.id , C.idl _ , C.idr _)
```

Think back to the conclusion we wanted to reach: $m$ is in $E$, so since
$f = m \circ e$ and $E$ is stable, so is $f$!

```agda
        m∈E : fa.forget ∈ E
        m∈E = is-iso→in-E fa.forget $
          C.make-invertible (gpq .centre .fst) (gpq .centre .snd .snd) gm=id
```
