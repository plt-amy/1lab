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

## Parts, patches and sections

<!--
```agda
-- Defining these notions for "non-functors" first will let us avoid
-- angering the positivity checker when defining sheafifications, see
-- that module for more details.
module
  pre {o ℓ ℓs} (C : Precategory o ℓ)
      {P₀ : ⌞ C ⌟ → Type ℓs}
      (P₁ : ∀ {U V} → C .Precategory.Hom U V → P₀ V → P₀ U)
  where

  open Precategory C
```
-->

```agda
  Parts : ∀ {U} (T : Sieve C U) → Type _
  Parts {U} T = ∀ {V} (f : Hom V U) (hf : f ∈ T) → P₀ V

  is-patch : ∀ {U} (T : Sieve C U) (p : Parts T) → Type _
  is-patch {U} T part =
    ∀ {V W} (f : Hom V U) (hf : f ∈ T) (g : Hom W V) (hgf : f ∘ g ∈ T)
    → P₁ g (part f hf) ≡ part (f ∘ g) hgf

  is-section : ∀ {U} (T : Sieve C U) → P₀ U → Parts T → Type _
  is-section {U = U} T s p =
    ∀ {V} (f : Hom V U) (hf : f ∈ T)
    → P₁ f s ≡ p f hf
```

<!--
```agda
module _ {o ℓ ℓs} {C : Precategory o ℓ} (P : Functor (C ^op) (Sets ℓs)) where
  open Precategory C
  private module P = Psh P
  open pre C P.₁ hiding (is-section)
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
        → P ⟪ g ⟫ part i is ≡ P ⟪ h ⟫ part j js
      compatible {i = i} {j} g h {is} {js} p =
        P ⟪ g ⟫ part i is ≡⟨ patch i _ g (T .closed is g) ⟩
        part (i ∘ g) _    ≡⟨ app p ⟩
        part (j ∘ h) _    ≡⟨ sym (patch j _ h (T .closed js h)) ⟩
        P ⟪ h ⟫ part j js ∎

  open Patch public

  is-section : ∀ {U} {T : Sieve C U} → P ʻ U → Patch T → Type _
  is-section {T = T} p x = pre.is-section C P.₁ T p (x .part)
```
-->

```agda
  record Section {U} {T : Sieve C U} (p : Patch T) : Type (o ⊔ ℓ ⊔ ℓs) where
    no-eta-equality
    field
      {part} : P ʻ U
      patch  : is-section part p

  open Section public
```

<!--
```agda
module _ {o ℓ ℓs} {C : Precategory o ℓ} {P : Functor (C ^op) (Sets ℓs)} where
  open Precategory C
  private module P = Psh P
  open pre C P.₁ hiding (is-section) public

  Extensional-Patch
    : ∀ {U ℓr} {S : Sieve C U} ⦃ _ : Extensional (Parts S) ℓr ⦄
    → Extensional (Patch P S) ℓr
  Extensional-Patch ⦃ e ⦄ .Pathᵉ x y = e .Pathᵉ (x .part) (y .part)
  Extensional-Patch ⦃ e ⦄ .reflᵉ x = e .reflᵉ (x .part)
  Extensional-Patch ⦃ e ⦄ .idsᵉ .to-path p i .part = e .idsᵉ .to-path p i
  Extensional-Patch ⦃ e ⦄ .idsᵉ .to-path {x} {y} p i .patch {W = W} f hf g hgf =
    is-prop→pathp (λ i → P.₀ W .is-tr (P.₁ g (e .idsᵉ .to-path p i _ hf)) (e .idsᵉ .to-path p i _ hgf))
      (x .patch f hf g hgf) (y .patch f hf g hgf) i
  Extensional-Patch ⦃ e ⦄ .idsᵉ .to-path-over p = is-prop→pathp (λ i → Pathᵉ-is-hlevel 1 e hlevel!) _ _

  Extensional-Section
    : ∀ {U ℓr} {S : Sieve C U} {p : Patch P S} ⦃ _ : Extensional (P ʻ U) ℓr ⦄
    → Extensional (Section P p) ℓr
  Extensional-Section ⦃ e ⦄ .Pathᵉ x y = e .Pathᵉ (x .part) (y .part)
  Extensional-Section ⦃ e ⦄ .reflᵉ x = e .reflᵉ (x .part)
  Extensional-Section ⦃ e ⦄ .idsᵉ .to-path p i .part = e .idsᵉ .to-path p i
  Extensional-Section {p = p} ⦃ e ⦄ .idsᵉ .to-path {a} {b} q i .patch {V} f hf =
    is-prop→pathp (λ i → P.₀ V .is-tr (P.₁ f (e .idsᵉ .to-path q i)) (p .part f hf))
      (a .patch f hf) (b .patch f hf) i
  Extensional-Section ⦃ e ⦄ .idsᵉ .to-path-over p = is-prop→pathp (λ i → Pathᵉ-is-hlevel 1 e (P.₀ _ .is-tr)) _ _

  instance
    extensionality-section : ∀ {U} {S : Sieve C U} {p : Patch P S} → Extensionality (Section P p)
    extensionality-section = record { lemma = quote Extensional-Section }

    extensionality-patch : ∀ {U} {S : Sieve C U} → Extensionality (Patch P S)
    extensionality-patch = record { lemma = quote Extensional-Patch }

  subset→patch
    : ∀ {U} {S S' : Sieve C U}
    → (∀ {V} (f : Hom V U) → f ∈ S' → f ∈ S)
    → Patch P S
    → Patch P S'
  subset→patch incl p .part f hf = p .part f (incl f hf)
  subset→patch incl p .patch f hf g hgf = p .patch f _ g _
```
-->

```agda
  section→patch : ∀ {U} {T : Sieve C U} → P ʻ U → Patch P T
  section→patch x .part  f _ = P ⟪ f ⟫ x
  section→patch x .patch f hf g hgf = P.collapse refl

  section→section
    : ∀ {U} {T : Sieve C U} (u : P ʻ U)
    → Section P {T = T} (section→patch u)
  section→section u .part       = u
  section→section u .patch f hf = refl
```

## Separated presheaves and sheaves

<!--
```agda
module _ {o ℓ ℓs} {C : Precategory o ℓ} (P : Functor (C ^op) (Sets ℓs)) where
  open Precategory C
```
-->

```agda
  is-separated₁ : ∀ {U} (T : Sieve C U) → Type _
  is-separated₁ {U} T =
    ∀ {x y : P ʻ U}
    → (l : ∀ {V} (f : Hom V U) (hf : f ∈ T) → P ⟪ f ⟫ x ≡ P ⟪ f ⟫ y)
    → x ≡ y

  is-sheaf₁ : ∀ {U} (T : Sieve C U) → Type _
  is-sheaf₁ T = (p : Patch P T) → is-contr (Section P p)

  is-sheaf₁→is-separated₁ : ∀ {U} (T : Sieve C U) → is-sheaf₁ T → is-separated₁ T
  is-sheaf₁→is-separated₁ T sheaf {x} {y} lp = ap part $
    is-contr→is-prop (sheaf (section→patch x)) (section→section x)
      record { patch = λ f hf → sym (lp f hf) }
```

<!--
```agda
module _ {o ℓ ℓc ℓs} {C : Precategory o ℓ} (J : Coverage C ℓc) (P : Functor (C ^op) (Sets ℓs)) where
```
-->

```agda
  is-separated : Type _
  is-separated = ∀ {U : ⌞ C ⌟} (c : J # U) → is-separated₁ P (J .cover c)

  record is-sheaf : Type (o ⊔ ℓ ⊔ ℓs ⊔ ℓc) where
    field
      has-sheaf₁ : ∀ {U} (c : J .covers U) → is-sheaf₁ P (J .cover c)

    split : ∀ {U : ⌞ C ⌟} {c : J # U} (p : Patch P (J .cover c)) → Section P p
    split {c = c} p = has-sheaf₁ c p .centre

    abstract
      separate : ∀ {U : ⌞ C ⌟} (c : J # U) → is-separated₁ P (J .cover c)
      separate c l = is-sheaf₁→is-separated₁ P (J .cover c) (has-sheaf₁ c) l

  open is-sheaf using (has-sheaf₁) public

  from-is-separated
    : is-separated
    → (∀ {U} (c : J .covers U) (s : Patch P (J .cover c)) → Section P s)
    → is-sheaf
  from-is-separated sep split .has-sheaf₁ c p .centre = split c p
  from-is-separated sep split .has-sheaf₁ c p .paths x = ext $ sep c λ f hf →
    split c p .patch f hf ∙ sym (x .patch f hf)
```

<!--
```agda
module _ {o ℓ ℓc} {C : Precategory o ℓ} (J : Coverage C ℓc) ℓs where
  open Precategory
  open Functor
```
-->

```agda
  Sheaves : Precategory (o ⊔ ℓ ⊔ ℓc ⊔ lsuc ℓs) (o ⊔ ℓ ⊔ ℓs)
  Sheaves .Ob = Σ[ p ∈ Functor (C ^op) (Sets ℓs) ] is-sheaf J p
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
