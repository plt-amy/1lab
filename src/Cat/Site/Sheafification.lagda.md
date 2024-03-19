<!--
```agda
open import Cat.Functor.Adjoint
open import Cat.Diagram.Sieve
open import Cat.Site.Base
open import Cat.Prelude

import Cat.Functor.Reasoning.Presheaf as Psh
```
-->

```agda
module Cat.Site.Sheafification where
```

# Sheafification

<!--
```agda
module Sheafification {o ℓ ℓc} {C : Precategory o ℓ} (J : Coverage C ℓc) {ℓs} (A : Functor (C ^op) (Sets ℓs)) where
  open Precategory C
  open Functor

  private
    module A = Functor A
    variable
      U V W : ⌞ C ⌟
      f g h : Hom U V

  -- The constructors 'glue' and 'glues' are why we define pre.Parts and
  -- pre.is-patch for "non-functors" (freestanding actions).
  --
  -- Ideally we would like to define Sheafify and Sheafify₀ by mutual
  -- recursion so we could instead say Patch Sheafify (J .cover c) but
  -- this angers both the termination and the positivity checker (and
  -- occasionally the scope checker).
```
-->

```agda
  data Sheafify₀ : ⌞ C ⌟ → Type (o ⊔ ℓ ⊔ ℓs ⊔ ℓc) where
    inc    : A ʻ U → Sheafify₀ U

    map    : (f : Hom U V) → Sheafify₀ V → Sheafify₀ U
    map-id : ∀ x → map {U = U} id x ≡ x
    map-∘  : ∀ x → map (g ∘ f) x ≡ map f (map g x)

    inc-natural : (x : A ʻ U) → inc (A ⟪ f ⟫ x) ≡ map f (inc x)

    sep
      : ∀ {x y : Sheafify₀ U} (c : J .covers U)
      → (l : ∀ {V} (f : Hom V U) (hf : f ∈ J .cover c) → map f x ≡ map f y)
      → x ≡ y

    glue
      : (c : J .covers U) (p : pre.Parts C map (J .cover c))
      → (g : pre.is-patch C map (J .cover c) p)
      → Sheafify₀ U

    glues
      : (c : J .covers U) (p : pre.Parts C map (J .cover c))
      → (g : pre.is-patch C map (J .cover c) p)
      → pre.is-section C map (J .cover c) (glue c p g) p

    squash : is-set (Sheafify₀ U)
```

```agda
  Sheafify : Functor (C ^op) (Sets (o ⊔ ℓ ⊔ ℓs ⊔ ℓc))
  Sheafify .F₀ x .∣_∣ = Sheafify₀ x
  Sheafify .F₀ x .is-tr = squash
  Sheafify .F₁ = map
  Sheafify .F-id = funext map-id
  Sheafify .F-∘ f g = funext map-∘

  Sheafify-is-sep : is-separated J Sheafify
  Sheafify-is-sep c = sep c

  Sheafify-is-sheaf : is-sheaf J Sheafify
  Sheafify-is-sheaf = from-is-separated J Sheafify Sheafify-is-sep λ c s → record
    { part  = glue c (s .part) (s .patch)
    ; patch = glues c (s .part) (s .patch)
    }
```

## An induction principle

```agda
  Sheafify-elim-prop
    : ∀ {ℓp} (P : ∀ {U} → Sheafify₀ U → Type ℓp)
    → (pprop : ∀ {U} (x : Sheafify₀ U) → is-prop (P x))
    → (pinc : ∀ {U : ⌞ C ⌟} (x : A ʻ U) → P (inc x))
    → (plocal
        : ∀ {U : ⌞ C ⌟} (c : J .covers U) (x : Sheafify₀ U)
        → (∀ {V} (f : Hom V U) (hf : f ∈ J .cover c) → P (map f x)) → P x)
    → ∀ {U} (x : Sheafify₀ U) → P x
  Sheafify-elim-prop {ℓp} P pprop pinc plocal x = unp' (go x) where opaque
    P' : ∀ {U} (x : Sheafify₀ U) → Type (o ⊔ ℓ ⊔ ℓp)
    P' {U} x = ∀ {V} (f : Hom V U) → P (map f x)

    unp' : ∀ {U} {x : Sheafify₀ U} → P' x → P x
    unp' p' = subst P (map-id _) (p' id)

    p'prp : ∀ {U} (x : Sheafify₀ U) → is-prop (P' x)
    p'prp x = Π-is-hlevel' 1 λ V → Π-is-hlevel 1 λ f → pprop (map f x)

    p'map : ∀ {U V : ⌞ C ⌟} (f : Hom U V) (x : Sheafify₀ V) → P' x → P' (map f x)
    p'map f x p g = subst P (map-∘ _) (p (f ∘ g))

    p'inc : ∀ {U : ⌞ C ⌟} (x : A ʻ U) → P' (inc x)
    p'inc x {V} f = subst P (inc-natural x) (pinc (A ⟪ f ⟫ x))

    p'glue
      : ∀ {U : ⌞ C ⌟} (c : J .covers U) (p : pre.Parts C map (J .cover c)) (g : pre.is-patch C map (J .cover c) p)
      → (∀ {V} (f : Hom V U) (hf : f ∈ J .cover c) → P' (p f hf))
      → P' (glue c p g)
    p'glue c p compat loc f = ∥-∥-proj (pprop _) do
      (c' , sub) ← J .stable c f
      pure $ plocal c' (map f (glue c p compat)) λ g hg →
        let
          it : P (map id (p (f ∘ g) (sub g hg)))
          it = loc (f ∘ g) (sub g hg) id
          q = map id (p (f ∘ g) _)            ≡⟨ map-id _ ⟩
              p (f ∘ g) _                     ≡˘⟨ glues c p compat (f ∘ g) (sub g hg) ⟩
              map (f ∘ g) (glue c p compat)   ≡⟨ map-∘ _ ⟩
              map g (map f (glue c p compat)) ∎
        in subst P q it
```

<!--
```agda
    go : ∀ {U} (x : Sheafify₀ U) → P' x
    go (map f x) = p'map f x (go x)
    go (inc x)   = p'inc x
    go (glue c p g) = p'glue c p g λ f hf → go (p f hf)
    go (inc-natural {f = f} x i) = is-prop→pathp (λ i → p'prp (inc-natural x i)) (p'inc (A.₁ f x)) (p'map f (inc x) (p'inc x)) i
    go (sep {x = x} {y = y} c l i) = is-prop→pathp (λ i → p'prp (sep c l i)) (go x) (go y) i
    go (map-id x i) = is-prop→pathp (λ i → p'prp (map-id x i)) (p'map id x (go x)) (go x) i
    go (map-∘ {g = g} {f = f} x i) = is-prop→pathp (λ i → p'prp (map-∘ x i)) (p'map (g ∘ f) x (go x)) (p'map f (map g x) (p'map g x (go x))) i
    go (glues c p g f hf i) = is-prop→pathp (λ i → p'prp (glues c p g f hf i)) (p'map f (glue c p g) (p'glue c p g λ g hg → go (p g hg))) (go (p f hf)) i
    go (squash x y p q i j) = is-prop→squarep (λ i j → p'prp (squash x y p q i j)) (λ i → go x) (λ i → go (p i)) (λ i → go (q i)) (λ i → go y) i j
```
-->

## The universal property

<!--
```agda
module Small {ℓ} {C : Precategory ℓ ℓ} (J : Coverage C ℓ)  where
  open Sheafification J

  open _=>_

  private variable F : Functor (C ^op) (Sets ℓ)
```
-->

```agda
  unit : F => Sheafify F
  unit .η _ = inc
  unit .is-natural x y f = funext inc-natural

  univ : (G : Functor (C ^op) (Sets ℓ)) → is-sheaf J G → F => G → Sheafify F => G
  univ {F = F} G shf eta = nt where
    private module G = Psh G
    go : ∀ U → Sheafify₀ F U → G ʻ U
    go U (map f x) = G ⟪ f ⟫ (go _ x)
    go U (map-id x i) = G.F-id {x = go _ x} i
    go U (map-∘ {g = g} {f = f} x i) = G.F-∘ f g {x = go _ x} i
    go U (inc x) = eta .η U x
    go U (inc-natural {f = f} x i) = eta .is-natural _ U f i x
    go U (sep {x = x} {y = y} c l i) = is-sheaf.separate shf c {go _ x} {go _ y} (λ f hf i → go _ (l f hf i)) i
    go U (glue c p g) =
      is-sheaf.split shf {c = c}
        record { patch = λ f hf h hhf i → go _ (g f hf h hhf i) }
        .part
    go U (glues c p g f hf i) = is-sheaf.split shf {c = c} record { patch = λ f hf h hhf i → go _ (g f hf h hhf i) } .patch f hf i
    go U (squash x y p q i j) = G.₀ U .is-tr (go U x) (go U y) (λ i → go U (p i)) (λ i → go U (q i)) i j

    nt : Sheafify F => G
    nt .η = go
    nt .is-natural x y f = refl

  unique
    : (G : Functor (C ^op) (Sets ℓ)) (shf : is-sheaf J G) (eta : F => G) (eps : Sheafify F => G)
    → (∀ U (x : F ʻ U) → eps .η U (inc x) ≡ eta .η U x)
    → univ G shf eta ≡ eps
  unique {F = F} G shf eta eps comm = ext λ i → Sheafify-elim-prop F
    (λ {v} x → univ G shf eta .η v x ≡ eps .η v x)
    (λ {U} x → hlevel!)
    (λ x → sym (comm _ x))
    (λ c x l → is-sheaf.separate shf c (λ f hf → l f hf ∙ eps .is-natural _ _ _ # _))
```

<!--
```agda
  private module ml = make-left-adjoint

  make-free-sheaf : make-left-adjoint (forget-sheaf J ℓ)
  make-free-sheaf .ml.free F = Sheafify F , Sheafify-is-sheaf F
  make-free-sheaf .ml.unit x = unit
  make-free-sheaf .ml.universal {F} {G , shf} = univ G shf
  make-free-sheaf .ml.commutes f = trivial!
  make-free-sheaf .ml.unique {F} {G , shf} p = unique G shf _ _ λ U x → sym (p ηₚ U $ₚ x)
```
-->
