<!--
```agda
open import Cat.Instances.Shape.Terminal
open import Cat.Diagram.Colimit.Base
open import Cat.Instances.Elements
open import Cat.Functor.Kan.Base
open import Cat.Diagram.Sieve
open import Cat.Functor.Hom
open import Cat.Site.Base
open import Cat.Prelude

import Cat.Functor.Reasoning.Presheaf as Psh
import Cat.Reasoning as Cat
```
-->

```agda
module Cat.Site.Closure where
```

# Closure properties of sites

<!--
```agda
module _ {o ℓ ℓs} {C : Precategory o ℓ} (P : Functor (C ^op) (Sets ℓs)) where
  open Cat C
  private module P = Psh P using (F-id)
```
-->

```agda
  is-sheaf-maximal : ∀ {U} (S : Sieve C U) → id ∈ S → is-sheaf₁ P S
  is-sheaf-maximal S id∈S p .centre .part = p .part id id∈S
  is-sheaf-maximal S id∈S p .centre .patch f hf =
      p .patch id id∈S f (subst (_∈ S) (sym (idl f)) hf)
    ∙ app p (idl f)
  is-sheaf-maximal S id∈S p .paths x = ext (sym (x .patch id id∈S) ∙ P.F-id)

  is-sheaf-iso : ∀ {V U} (S : Sieve C U) (f : V ≅ U) → f .to ∈ S → is-sheaf₁ P S
  is-sheaf-iso S f hf = is-sheaf-maximal S (subst (_∈ S) (f .invl) (S .closed hf (f .from)))
```

<!--
```agda
module
  _ {o ℓ ℓs ℓc} {C : Precategory o ℓ} (J : Coverage C ℓc)
    (P : Functor (C ^op) (Sets ℓs)) (shf : is-sheaf J P)
  where

  open Precategory C
  private
    module P = Psh P
    module shf = is-sheaf shf
```
-->

```agda
  is-sheaf-factor
    : ∀ {U} (s : Sieve C U) (c : J # U)
    → (∀ {V} (f : Hom V U) → f ∈ J .cover c → f ∈ s)
    → is-sheaf₁ P s
  is-sheaf-factor s c c⊆s ps = done where
    sec' = shf.split (subset→patch c⊆s ps)

    sec : Section P ps
    sec .part = sec' .part
    sec .patch f hf = ∥-∥-proj! do
      (c' , sub) ← J .stable c f
      pure $ shf.separate c' λ g hg →
        P ⟪ g ⟫ (P ⟪ f ⟫ sec' .part) ≡⟨ P.collapse refl ⟩
        P ⟪ f ∘ g ⟫ sec' .part       ≡⟨ sec' .patch (f ∘ g) (sub _ hg) ⟩
        ps .part (f ∘ g) _           ≡˘⟨ ps .patch f hf g (c⊆s (f ∘ g) (sub g hg)) ⟩
        P ⟪ g ⟫ ps .part f hf        ∎

    done : is-contr (Section P ps)
    done .centre = sec
    done .paths x = ext $ shf.separate c λ f hf →
      P ⟪ f ⟫ sec' .part ≡⟨ sec' .patch f hf ⟩
      ps .part f _       ≡˘⟨ x .patch f (c⊆s f hf) ⟩
      (P ⟪ f ⟫ x .part)  ∎
```

```agda
  is-sheaf-pullback
    : ∀ {V U} (c : J # U) (f : Hom V U) → is-sheaf₁ P (pullback f (J .cover c))
  is-sheaf-pullback c f p = ∥-∥-proj! do
    (c' , sub) ← J .stable c f
    pure (is-sheaf-factor (pullback f (J .cover c)) c' sub p)
```

<!--
```agda
module _ {o ℓ ℓs} {C : Precategory o ℓ} (P : Functor (C ^op) (Sets ℓs)) where
  open Precategory C
```
-->

## The canonical topology

```agda
  canonical-for : Coverage C (o ⊔ ℓ ⊔ ℓs)
  canonical-for .covers U = Σ[ S ∈ Sieve C U ] ((∀ {V} (f : Hom V U) → is-sheaf₁ P (pullback f S)))
  canonical-for .cover = fst
  canonical-for .stable (s , iss) f =
    let
      s' = pullback f s , λ g → subst (is-sheaf₁ P) pullback-∘ (iss (f ∘ g))
    in inc (s' , λ g x → x)

  is-sheaf-canonical-for : is-sheaf canonical-for P
  is-sheaf-canonical-for .has-sheaf₁ (c , is-s) = subst (is-sheaf₁ P) pullback-id (is-s id)
```

<!--
```agda
module _ {o ℓ} {C : Precategory o ℓ} where
  open Element-hom
  open Element
  open Cat C
  open _=>_
```
-->

## In general

```agda
  sieve→cocone : ∀ {U} (S : Sieve C U) → πₚ C (to-presheaf S) => Const U
  sieve→cocone S .η x = x .section .fst
  sieve→cocone S .is-natural x y f = ap fst (f .commute) ∙ introl refl

  -- C2.2.12
  is-effective-epi : ∀ {U} → Sieve C U → Type _
  is-effective-epi {U} S = is-colimit _ U (sieve→cocone S)

  is-universally-effective-epi : ∀ {U} → Sieve C U → Type _
  is-universally-effective-epi {U} S =
    ∀ {V} (f : Hom V U) → is-effective-epi (pullback f S)

  is-uee→is-sheaf₁
    : ∀ {U} (S : Sieve C U)
    → is-universally-effective-epi S
    → ∀ {V} → is-sheaf₁ (Hom-into C V) S
  is-uee→is-sheaf₁ {U} S effepi {V} p = uniq where
    module x = is-lan (effepi id)

    nt : πₚ C (to-presheaf (pullback id S)) => const! V F∘ !F
    nt .η (elem _ (f , hf)) = p .part f (subst (_∈ S) (idl _) hf)
    nt .is-natural (elem _ (f , hf)) (elem _ (g , hg)) h =
      (p .part g hg' ∘ h .hom)  ≡⟨ p .patch g _ (h .hom) (S .closed hg' (h .hom)) ⟩
      p .part (g ∘ h .hom) _    ≡⟨ app p (ap fst (h .commute)) ⟩
      p .part f _               ≡⟨ introl refl ⟩
      id ∘ p .part f _          ∎
      where hg' = subst (_∈ S) (idl g) hg

    s : Section _ p
    s .part       = x.σ nt .η tt
    s .patch f hf = x.σ-comm {α = nt} ηₚ elem _ (f , subst (_∈ S) (introl refl) hf) ∙ app p refl

    uniq : is-contr (Section _ p)
    uniq .centre  = s
    uniq .paths x = ext (x.σ-uniq {α = nt} {σ' = σ'} (ext λ i → sym (x .patch _ _)) ηₚ tt) where
      σ' : const! U => const! V
      σ' .η _ = x .part
      σ' .is-natural _ _ _ = id-comm

  Canonical-coverage : Coverage C (o ⊔ ℓ)
  Canonical-coverage .covers U = Σ[ s ∈ Sieve C U ] is-universally-effective-epi s
  Canonical-coverage .cover = fst
  Canonical-coverage .stable (c , st) f = pure $
    (pullback f c , λ g → subst is-effective-epi pullback-∘ (st (f ∘ g))) , λ g x → x

  representable-is-sheaf-canonical : ∀ {U} → is-sheaf Canonical-coverage (よ₀ C U)
  representable-is-sheaf-canonical .has-sheaf₁ (c , st) = is-uee→is-sheaf₁ c st

  is-sheaf₁→is-uee
    : ∀ {ℓc} (J : Coverage C ℓc)
    → (∀ {V} → is-sheaf J (Hom-into C V))
    → ∀ {U} {c : J .covers U} → is-universally-effective-epi (J .cover c)
  is-sheaf₁→is-uee J shf {U} {c} {V} f = to-is-colimitp mk refl where
    open make-is-colimit

    mk : make-is-colimit (πₚ C (to-presheaf (pullback f (J .cover c)))) V
    mk .ψ (elem V' (g , hg)) = g
    mk .commutes f = ap fst (f .commute)
    mk .universal {W} eps comm = sec .centre .part module univ where
      p : Patch (よ₀ C W) (pullback f (J .cover c))
      p .part {X} g hg = eps (elem X (g , hg))
      p .patch f hf g hgf = comm (elem-hom g (Σ-prop-path! refl))

      sec = is-sheaf-pullback J (よ₀ C W) shf c f p
    mk .factors {j} eps comm = univ.sec eps comm .centre .patch _ _
    mk .unique eps comm other p = sym $ ap part $ univ.sec eps comm .paths
      record { patch = λ f hf → p (elem _ (f , hf)) }
```
