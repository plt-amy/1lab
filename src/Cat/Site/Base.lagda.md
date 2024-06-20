<!--
```agda
open import Cat.Instances.Functor
open import Cat.Diagram.Sieve
open import Cat.Prelude hiding (glue)

import Cat.Functor.Reasoning.Presheaf as Psh
import Cat.Reasoning as Cat
```
-->

```agda
module Cat.Site.Base where
```

<!--
```agda
private variable
  o ℓ ℓc ℓs : Level
  C : Precategory o ℓ
```
-->

# Sites and sheaves

## Parts, patches and sections {defines="patch"}

<!--
```agda
-- Defining these notions for "non-functors" first will let us avoid
-- angering the positivity checker when defining sheafifications, see
-- that module for more details.
module pre {o ℓ ℓs} (C : Precategory o ℓ) {A₀ : ⌞ C ⌟ → Type ℓs} (A₁ : ∀ {U V} → C .Precategory.Hom U V → A₀ V → A₀ U) where
  open Precategory C
```
-->

To formally define the sheaf condition, we must first define what we
mean by "local data". Relative to a sieve $T$ on $U : \cC$, we will say
that a family of **parts** is given by a function $s(f_i) : A(V_i)$,
defined on every $f : V \to U$ in $T$. A family of parts may be
completely arbitrary: the name is just an abbreviation for the idea of
"elements of $A$, on every map of $T$". It would be unreasonable to
expect that an arbitrary collection of elements of $A$ will glue
together to give anything meaningful, so we must introduce another
auxiliary notion.

```agda
  Parts : ∀ {U} (T : Sieve C U) → Type _
  Parts {U} T = ∀ {V} (f : Hom V U) (hf : f ∈ T) → A₀ V
```

Ideally, we would like to say that the $s(-)$ *agree on intersections*,
but $\cC$ does not have [[limits]], or any other extant notion of
intersection, so we will have to find a formulation entirely in terms of
maps. This turns out not to be too hard: we can just pretend! If we have
maps $i : V_1 \to U$ and $j : V_2 \to U$, then the fundamental property
that characterises their intersection is that we have projections

~~~{.quiver}
\[\begin{tikzcd}[ampersand replacement=\&]
  \& {V_1 \cap V_2} \\
  {V_1} \&\& {V_2} \\
  \& U
  \arrow["{p_1}", from=1-2, to=2-1]
  \arrow["{p_2}"', from=1-2, to=2-3]
  \arrow["i", from=2-1, to=3-2]
  \arrow["j"', from=2-3, to=3-2]
\end{tikzcd}\]
~~~

which satisfy $ip_1 = jp_2$^[In other words, the intersection of $i :
V_1 \to U$ and $j : V_2 \to U$ is given by their [[pullback]]. We will
not need the universality of pullbacks here.]. We would say that $s(i)$
and $s(j)$ agree on $V_1 \cap V_2$ if $A(p_1)(s(i)) = A(p_2)(s(j))$.
Remember that, since $A$ is contravariant, $A(p_1) : A(V_1) \to A(V_1
\cap V_2)$. Since this notion only makes reference to the commutativity
of the square above, and no other special properties of $V_1 \cap V_2$,
we could use the definition as-is! But, given that $T$ is closed under
composition, if it includes $i : V_1 \to U$, then it also includes the
composite

$$
V_1 \cap V_2 \xto{p_1} V_1 \xto{i} U
$$,

so we have a part $s(ip_1)$ in addition to a part $s(i)$. We can then
simplify our notion of compatibility, to demand only that $A(p_1)(s(i))
= s(ip_1)$, since we would then have

$$
A(p_1)(s(i)) = s(ip_1) = s(jp_2) = A(p_2)(s(j))
$$.

We will use this simpler notion of agreement throughout, and we will say
that a family of parts that satisfies it is a **patch**. Johnstone
[-@Elephant, C2.1.1] refers to patches by the more verbose name
"compatible families of elements", which, while more technically more
descriptive, does not gesture to the geometric intuition that the $s$
*fit together*.

```agda
  is-patch : ∀ {U} (T : Sieve C U) (p : Parts T) → Type _
  is-patch {U} T part =
    ∀ {V W} (f : Hom V U) (hf : f ∈ T) (g : Hom W V) (hgf : f ∘ g ∈ T)
    → A₁ g (part f hf) ≡ part (f ∘ g) hgf
```

```agda
  is-section : ∀ {U} (T : Sieve C U) → A₀ U → Parts T → Type _
  is-section {U = U} T s p =
    ∀ {V} (f : Hom V U) (hf : f ∈ T)
    → A₁ f s ≡ p f hf
```

<!--
```agda
module _ {o ℓ ℓs} {C : Precategory o ℓ} (A : Functor (C ^op) (Sets ℓs)) where
  open Precategory C
  private module A = Psh A
  open pre C A.₁ hiding (is-section)
```
-->

```agda
  record Patch {U} (T : Sieve C U) : Type (o ⊔ ℓ ⊔ ℓs) where
    no-eta-equality
    field
      part  : Parts T
      patch : is-patch T part
```

<!--
```agda
    abstract
      app : ∀ {V} {f g : Hom V U} {hf hg} → f ≡ g → part f hf ≡ part g hg
      app p = ap₂ part p prop!

      compatible
        : ∀ {V W X} {i : Hom W U} {j : Hom X U} (g : Hom V W) (h : Hom V X)
        → {is : i ∈ T} {js : j ∈ T}
        → i ∘ g ≡ j ∘ h
        → A ⟪ g ⟫ part i is ≡ A ⟪ h ⟫ part j js
      compatible {i = i} {j} g h {is} {js} p =
        A ⟪ g ⟫ part i is ≡⟨ patch i _ g (T .closed is g) ⟩
        part (i ∘ g) _    ≡⟨ app p ⟩
        part (j ∘ h) _    ≡⟨ sym (patch j _ h (T .closed js h)) ⟩
        A ⟪ h ⟫ part j js ∎

  open Patch

  is-section : ∀ {U} {T : Sieve C U} → A ʻ U → Patch T → Type _
  is-section {T = T} p x = pre.is-section C A.₁ T p (x .part)
```
-->

```agda
  record Section {U} {T : Sieve C U} (p : Patch T) : Type (o ⊔ ℓ ⊔ ℓs) where
    no-eta-equality
    field
      {part} : A ʻ U
      patch  : is-section part p
```

<!--
```agda
module _ {o ℓ ℓs} {C : Precategory o ℓ} {A : Functor (C ^op) (Sets ℓs)} where
  open Cat C
  open Section
  open Patch
  private module A = Psh A
  open pre C A.₁ hiding (is-section) public

  instance
    Extensional-Patch
      : ∀ {U ℓr} {S : Sieve C U} ⦃ _ : Extensional (Parts S) ℓr ⦄
      → Extensional (Patch A S) ℓr
    Extensional-Patch ⦃ e ⦄ .Pathᵉ x y = e .Pathᵉ (x .part) (y .part)
    Extensional-Patch ⦃ e ⦄ .reflᵉ x = e .reflᵉ (x .part)
    Extensional-Patch ⦃ e ⦄ .idsᵉ .to-path p i .part = e .idsᵉ .to-path p i
    Extensional-Patch ⦃ e ⦄ .idsᵉ .to-path {x} {y} p i .patch {W = W} f hf g hgf =
      is-prop→pathp (λ i → A.₀ W .is-tr (A.₁ g (e .idsᵉ .to-path p i _ hf)) (e .idsᵉ .to-path p i _ hgf))
        (x .patch f hf g hgf) (y .patch f hf g hgf) i
    Extensional-Patch ⦃ e ⦄ .idsᵉ .to-path-over p = is-prop→pathp (λ i → Pathᵉ-is-hlevel 1 e (hlevel 2)) _ _

    Extensional-Section
      : ∀ {U ℓr} {S : Sieve C U} {p : Patch A S} ⦃ _ : Extensional (A ʻ U) ℓr ⦄
      → Extensional (Section A p) ℓr
    Extensional-Section ⦃ e ⦄ .Pathᵉ x y = e .Pathᵉ (x .part) (y .part)
    Extensional-Section ⦃ e ⦄ .reflᵉ x = e .reflᵉ (x .part)
    Extensional-Section ⦃ e ⦄ .idsᵉ .to-path p i .part = e .idsᵉ .to-path p i
    Extensional-Section {p = p} ⦃ e ⦄ .idsᵉ .to-path {a} {b} q i .patch {V} f hf =
      is-prop→pathp (λ i → A.₀ V .is-tr (A.₁ f (e .idsᵉ .to-path q i)) (p .part f hf))
        (a .patch f hf) (b .patch f hf) i
    Extensional-Section ⦃ e ⦄ .idsᵉ .to-path-over p = is-prop→pathp (λ i → Pathᵉ-is-hlevel 1 e (hlevel 2)) _ _

  subset→patch
    : ∀ {U} {S S' : Sieve C U}
    → (∀ {V} (f : Hom V U) → f ∈ S' → f ∈ S)
    → Patch A S
    → Patch A S'
  subset→patch incl p .part f hf = p .part f (incl f hf)
  subset→patch incl p .patch f hf g hgf = p .patch f _ g _

  pullback-patch : ∀ {U V} {S : Sieve C U} (f : Hom V U) → Patch A S → Patch A (pullback f S)
  pullback-patch {S = S} f s .part g p = s .part (f ∘ g) p
  pullback-patch {S = S} f s .patch g h hfg hfgh =
      s .patch (f ∘ g) h hfg (S .closed h hfg)
    ∙ app s (pullr refl)

  open _=>_

  map-patch
    : ∀ {B : Functor (C ^op) (Sets ℓs)} {U} {S : Sieve C U} (eta : A => B)
    → Patch A S
    → Patch B S
  map-patch eta x .part f hf = eta .η _ (x .part f hf)
  map-patch eta x .patch f hf g hgf = sym (eta .is-natural _ _ _ $ₚ _) ∙ ap (eta .η _) (x .patch f hf g hgf)
```
-->

Before moving on, we note that stealing the name "section" for the
concept of sections of a *patch* is benign: Any element $A(U)$ generates
a patch for a sieve $T$ on $U$, and it is a section of this patch.

```agda
  section→patch : ∀ {U} {T : Sieve C U} → A ʻ U → Patch A T
  section→patch x .part  f _ = A ⟪ f ⟫ x
  section→patch x .patch f hf g hgf = A.collapse refl

  section→section
    : ∀ {U} {T : Sieve C U} (u : A ʻ U)
    → Section A {T = T} (section→patch u)
  section→section u .part       = u
  section→section u .patch f hf = refl
```

## The notion of sheaf {defines="sheaf sheaves"}

Using our terminology above, we can very concisely define what it means
for a functor $A : \psh(\cC)$ to be a sheaf, at least with respect to a
sieve $T$ on $U$: any patch $p$ of $T$ has a unique section.

<!--
```agda
module _ {o ℓ ℓs} {C : Precategory o ℓ} (A : Functor (C ^op) (Sets ℓs)) where
  open Precategory C
  open Section
  open Patch
```
-->

```agda
  is-sheaf₁ : ∀ {U} (T : Sieve C U) → Type _
  is-sheaf₁ T = (p : Patch A T) → is-contr (Section A p)
```

::: {.definition #separated-presheaf}
We will also need the notion of **separated presheaf**. These are
typically defined to be the presheaves which have *at most one* section
for each patch: the type of sections for each patch is a
[[proposition]], instead of being [[contractible]]. But from a
type-theoretic perspective, it makes more sense to define separated
presheaves in the following "unfolded" form, which says that that
equality on $A(U)$ is a $T$-local property.
:::

```agda
  is-separated₁ : ∀ {U} (T : Sieve C U) → Type _
  is-separated₁ {U} T =
    ∀ {x y : A ʻ U}
    → (∀ {V} (f : Hom V U) (hf : f ∈ T) → A ⟪ f ⟫ x ≡ A ⟪ f ⟫ y)
    → x ≡ y
```

Note that every sheaf is indeed separated, even after this unfolding, by
the above mapping from elements to sections.

```agda
  is-sheaf₁→is-separated₁ : ∀ {U} (T : Sieve C U) → is-sheaf₁ T → is-separated₁ T
  is-sheaf₁→is-separated₁ T sheaf {x} {y} lp = ap part $
    is-contr→is-prop (sheaf (section→patch x)) (section→section x)
      record { patch = λ f hf → sym (lp f hf) }
```

<!--
```agda
  from-is-separated₁
    : ∀ {U} {T : Sieve C U}
    → is-separated₁ T
    → ∀ {p : Patch A T} (s : Section A p)
    → is-contr (Section A p)
  from-is-separated₁ sep sec .centre = sec
  from-is-separated₁ sep sec .paths x = ext $ sep λ f hf →
    sec .patch f hf ∙ sym (x .patch f hf)

  -- This is equal to `subst (is-sheaf₁ A)` but has better definitional
  -- behaviour for the relevant part.
  subst-is-sheaf₁ : ∀ {U} {T S : Sieve C U} (p : T ≡ S) → is-sheaf₁ T → is-sheaf₁ S
  subst-is-sheaf₁ {T = T} {S = S} p shf pa = done where
    pa' : Patch A T
    pa' .part f hf = pa .part f (subst (f ∈_) p hf)
    pa' .patch f hf g hgf = pa .patch f _ g _

    sec = shf pa'

    done : is-contr (Section A pa)
    done .centre .part = sec .centre .part
    done .centre .patch f hf = sec .centre .patch f (subst (f ∈_) (sym p) hf) ∙ app pa refl
    done .paths x = ext (ap part (sec .paths record { patch = λ f hf → x .patch f (subst (f ∈_) p hf) ∙ app pa refl }))
```
-->

# Sites, formally {defines="site coverage"}

```agda
record Coverage {o ℓ} (C : Precategory o ℓ) ℓc : Type (o ⊔ ℓ ⊔ lsuc ℓc) where
  no-eta-equality

  open Precategory C

  field
    covers : ⌞ C ⌟ → Type ℓc
    cover  : ∀ {U} → covers U → Sieve C U

    stable
      : ∀ {U V : ⌞ C ⌟} (c : covers U) (f : Hom V U)
      → ∃[ d ∈ covers V ] (∀ {W} (g : Hom W V) → g ∈ cover d → f ∘ g ∈ cover c)
```

<!--
```agda
open Coverage public

instance
  Funlike-Coverage : Funlike (Coverage C ℓc) ⌞ C ⌟ (λ _ → Type ℓc)
  Funlike-Coverage = record { _#_ = λ C U → C .covers U }

  Membership-Coverage : ∀ {U} → Membership (Coverage C ℓc) (Sieve C U) _
  Membership-Coverage = record { _∈_ = λ C S → fibre (C .cover) S }
```
-->

<!--
```agda
module _ {o ℓ ℓc ℓs} {C : Precategory o ℓ} (J : Coverage C ℓc) (A : Functor (C ^op) (Sets ℓs)) where
```
-->

```agda
  is-separated : Type _
  is-separated = ∀ {U : ⌞ C ⌟} (c : J # U) → is-separated₁ A (J .cover c)

  record is-sheaf : Type (o ⊔ ℓ ⊔ ℓs ⊔ ℓc) where
    no-eta-equality
    field
      part     : ∀ {U} (S : J .covers U) (p : Patch A (J .cover S)) → A ʻ U
      patch    : ∀ {U} (S : J .covers U) (p : Patch A (J .cover S)) → is-section A (part S p) p
      separate : ∀ {U} (S : J .covers U) → is-separated₁ A (J .cover S)

    split : ∀ {U} {S : J .covers U} (p : Patch A (J .cover S)) → Section A p
    split p .Section.part  = part _ p
    split p .Section.patch = patch _ p

  open is-sheaf using (part ; patch ; separate) public
```

<!--
```agda
module _ {o ℓ ℓc ℓs} {C : Precategory o ℓ} {J : Coverage C ℓc} {A : Functor (C ^op) (Sets ℓs)} where
  from-is-separated
    : is-separated J A
    → (∀ {U} (c : J .covers U) (s : Patch A (J .cover c)) → Section A s)
    → is-sheaf J A
  from-is-separated sep split .part S p   = split S p .Section.part
  from-is-separated sep split .patch S p  = split S p .Section.patch
  from-is-separated sep split .separate S = sep S

  from-is-sheaf₁
    : (∀ {U} (c : J .covers U) → is-sheaf₁ A (J .cover c))
    → is-sheaf J A
  from-is-sheaf₁ shf .part S p = shf _ p .centre .Section.part
  from-is-sheaf₁ shf .patch S p = shf _ p .centre .Section.patch
  from-is-sheaf₁ shf .separate S = is-sheaf₁→is-separated₁ _ _ (shf _)

  to-is-sheaf₁ : is-sheaf J A → ∀ {U} (c : J .covers U) → is-sheaf₁ A (J .cover c)
  to-is-sheaf₁ shf c p = from-is-separated₁ _ (shf .separate c) (is-sheaf.split shf p)
```
-->

<!--
```agda
open Section public
open Patch public

module _ {o ℓ ℓc ℓp} {C : Precategory o ℓ} {J : Coverage C ℓc} {A : Functor (C ^op) (Sets ℓp)} where
  private unquoteDecl eqv = declare-record-iso eqv (quote is-sheaf)
  abstract instance
    H-Level-is-sheaf : ∀ {n} → H-Level (is-sheaf J A) (suc n)
    H-Level-is-sheaf = prop-instance $ retract→is-hlevel 1 from to ft (hlevel 1) where
      T : Type (o ⊔ ℓ ⊔ ℓc ⊔ ℓp)
      T = ∀ {U} (S : J .covers U) (p : Patch A (J .cover S)) → is-contr (Section A p)

      from : T → is-sheaf J A
      from x .part  S p  = x S p .centre .part
      from x .patch S p  = x S p .centre .patch
      from x .separate S = is-sheaf₁→is-separated₁ A _ (x S)

      to : is-sheaf J A → T
      to shf S p = from-is-separated₁ _ (shf .separate S) (is-sheaf.split shf p)

      ft : ∀ x → from (to x) ≡ x
      ft x = Iso.injective eqv (Σ-prop-path! refl)
```
-->

<!--
```agda
module _ {o ℓ ℓc} {C : Precategory o ℓ} (J : Coverage C ℓc) ℓs where
  open Precategory
  open Functor
```
-->

```agda
  Sheaf : Type _
  Sheaf = Σ[ p ∈ Functor (C ^op) (Sets ℓs) ] is-sheaf J p

  Sheaves : Precategory (o ⊔ ℓ ⊔ ℓc ⊔ lsuc ℓs) (o ⊔ ℓ ⊔ ℓs)
  Sheaves .Ob = Sheaf
  Sheaves .Hom (S , _) (T , _) = S => T
  Sheaves .Hom-set _ _ = hlevel 2
  Sheaves .id = idnt
  Sheaves ._∘_ = _∘nt_
  Sheaves .idr f = trivial!
  Sheaves .idl f = trivial!
  Sheaves .assoc f g h = trivial!

  forget-sheaf : Functor Sheaves (PSh ℓs C)
  forget-sheaf .F₀ (S , _) = S
  forget-sheaf .F₁ f = f
  forget-sheaf .F-id = refl
  forget-sheaf .F-∘ f g = refl
```
