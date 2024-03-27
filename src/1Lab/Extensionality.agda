open import 1Lab.Reflection.Signature
open import 1Lab.Path.IdentitySystem
open import 1Lab.Function.Embedding
open import 1Lab.Reflection.HLevel
open import 1Lab.Reflection.Subst
open import 1Lab.HIT.Truncation
open import 1Lab.HLevel.Closure
open import 1Lab.Reflection
open import 1Lab.Type.Sigma
open import 1Lab.Resizing
open import 1Lab.Type.Pi
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

open import Data.Nat.Base

module 1Lab.Extensionality where

record Extensional {ℓ} (A : Type ℓ) (ℓ-rel : Level) : Type (ℓ ⊔ lsuc ℓ-rel) where
  no-eta-equality
  field
    Pathᵉ : A → A → Type ℓ-rel
    reflᵉ : ∀ x → Pathᵉ x x
    idsᵉ : is-identity-system Pathᵉ reflᵉ

open Extensional using (Pathᵉ ; reflᵉ ; idsᵉ) public

instance
  -- Default instance, uses regular paths for the relation.
  Extensional-default : ∀ {ℓ} {A : Type ℓ} → Extensional A ℓ
  Extensional-default .Pathᵉ   = _≡_
  Extensional-default .reflᵉ _ = refl
  Extensional-default .idsᵉ    = Path-identity-system

  {-# INCOHERENT Extensional-default #-}

  Extensional-Lift
    : ∀ {ℓ ℓ' ℓr} {A : Type ℓ}
    → ⦃ sa : Extensional A ℓr ⦄
    → Extensional (Lift ℓ' A) ℓr
  Extensional-Lift ⦃ sa ⦄ .Pathᵉ (lift x) (lift y) = sa .Pathᵉ x y
  Extensional-Lift ⦃ sa ⦄ .reflᵉ (lift x) = sa .reflᵉ x
  Extensional-Lift ⦃ sa ⦄ .idsᵉ .to-path p = ap lift (sa .idsᵉ .to-path p)
  Extensional-Lift ⦃ sa ⦄ .idsᵉ .to-path-over p = sa .idsᵉ .to-path-over p

  Extensional-Π
    : ∀ {ℓ ℓ' ℓr} {A : Type ℓ} {B : A → Type ℓ'}
    → ⦃ sb : ∀ {x} → Extensional (B x) ℓr ⦄
    → Extensional ((x : A) → B x) (ℓ ⊔ ℓr)
  Extensional-Π ⦃ sb ⦄ .Pathᵉ f g = ∀ x → Pathᵉ sb (f x) (g x)
  Extensional-Π ⦃ sb ⦄ .reflᵉ f x = reflᵉ sb (f x)
  Extensional-Π ⦃ sb ⦄ .idsᵉ .to-path h = funext λ i → sb .idsᵉ .to-path (h i)
  Extensional-Π ⦃ sb ⦄ .idsᵉ .to-path-over h = funextP λ i → sb .idsᵉ .to-path-over (h i)

  {-# OVERLAPPABLE Extensional-Π #-}

  Extensional-Π'
    : ∀ {ℓ ℓ' ℓr} {A : Type ℓ} {B : A → Type ℓ'}
    → ⦃ sb : ∀ {x} → Extensional (B x) ℓr ⦄
    → Extensional ({x : A} → B x) (ℓ ⊔ ℓr)
  Extensional-Π' ⦃ sb ⦄ .Pathᵉ f g = ∀ {x} → Pathᵉ (sb {x}) f g
  Extensional-Π' ⦃ sb ⦄ .reflᵉ f = reflᵉ sb f
  Extensional-Π' ⦃ sb ⦄ .idsᵉ .to-path h i = sb .idsᵉ .to-path h i
  Extensional-Π' ⦃ sb ⦄ .idsᵉ .to-path-over h i = sb .idsᵉ .to-path-over h i

  Extensional-uncurry
    : ∀ {ℓ ℓ' ℓ'' ℓr} {A : Type ℓ} {B : A → Type ℓ'} {C : Type ℓ''}
    → ⦃ sb : Extensional ((x : A) → B x → C) ℓr ⦄
    → Extensional (Σ A B → C) ℓr
  Extensional-uncurry ⦃ sb ⦄ .Pathᵉ f g = sb .Pathᵉ (curry f) (curry g)
  Extensional-uncurry ⦃ sb ⦄ .reflᵉ f = sb .reflᵉ (curry f)
  Extensional-uncurry ⦃ sb = sb ⦄ .idsᵉ .to-path h i (a , b) = sb .idsᵉ .to-path h i a b
  Extensional-uncurry ⦃ sb = sb ⦄ .idsᵉ .to-path-over h = sb .idsᵉ .to-path-over h

  Extensional-×
    : ∀ {ℓ ℓ' ℓr ℓs} {A : Type ℓ} {B : Type ℓ'}
    → ⦃ sa : Extensional A ℓr ⦄
    → ⦃ sb : Extensional B ℓs ⦄
    → Extensional (A × B) (ℓr ⊔ ℓs)
  Extensional-× ⦃ sa ⦄ ⦃ sb ⦄ .Pathᵉ (x , y) (x' , y') = Pathᵉ sa x x' × Pathᵉ sb y y'
  Extensional-× ⦃ sa ⦄ ⦃ sb ⦄ .reflᵉ (x , y) = reflᵉ sa x , reflᵉ sb y
  Extensional-× ⦃ sa ⦄ ⦃ sb ⦄ .idsᵉ .to-path (p , q) = ap₂ _,_
    (sa .idsᵉ .to-path p)
    (sb .idsᵉ .to-path q)
  Extensional-× ⦃ sa ⦄ ⦃ sb ⦄ .idsᵉ .to-path-over (p , q) = Σ-pathp
    (sa .idsᵉ .to-path-over p)
    (sb .idsᵉ .to-path-over q)

  Extensional-lift-map
    : ∀ {ℓ ℓ' ℓ'' ℓr} {A : Type ℓ} {B : Lift ℓ' A → Type ℓ''}
    → ⦃ sa : Extensional ((x : A) → B (lift x)) ℓr ⦄
    → Extensional ((x : Lift ℓ' A) → B x) ℓr
  Extensional-lift-map ⦃ sa = sa ⦄ .Pathᵉ f g = sa .Pathᵉ (f ∘ lift) (g ∘ lift)
  Extensional-lift-map ⦃ sa = sa ⦄ .reflᵉ x = sa .reflᵉ (x ∘ lift)
  Extensional-lift-map ⦃ sa = sa ⦄ .idsᵉ .to-path h i (lift x) = sa .idsᵉ .to-path h i x
  Extensional-lift-map ⦃ sa = sa ⦄ .idsᵉ .to-path-over h = sa .idsᵉ  .to-path-over h

{-
Actual user-facing entry point for the tactic: using the 'extensional'
tactic (through the blanket instance) we can find an identity system for
the type A, and turn a proof in the computed relation to an identity.
-}
ext
  : ∀ {ℓ ℓr} {A : Type ℓ} {x y : A} ⦃ r : Extensional A ℓr ⦄
  → Pathᵉ r x y → x ≡ y
ext ⦃ r ⦄ p = r .idsᵉ .to-path p

{-
Using the extensionality tactic we can define a "more general refl",
where the terms being compared are not definitionally equal, but they
inhabit a type with a good identity system for which 'r x : R x y' type
checks.

The idea is to write a function wrapping

  ext : ⦃ r : Extensional A ℓ ⦄ (p : Pathᵉ r x y) → x ≡ y

so that it gives (reflᵉ r x) as the default argument for p. We can use a
tactic argument to accomplish this.
-}

private
  trivial-worker
    : ∀ {ℓ ℓr} {A : Type ℓ}
    → (r : Extensional A ℓr)
    → (x y : A)
    → Term
    → TC ⊤
  trivial-worker r x y goal = try where
    error : ∀ {ℓ} {A : Type ℓ} → TC A

    -- We already have our r : Extensional A ℓr, and this is a macro, so
    -- we can just check that r .reflᵉ x : R x y. If that's the case
    -- then we can use that as the argument, otherwise we can give a
    -- slightly better error message than what Agda would yell.
    try : TC ⊤
    try = do
      `r ← wait-for-type =<< quoteTC r
      ty ← quoteTC (Pathᵉ r x y)
      `x ← quoteTC x
      `refl ← check-type (it reflᵉ ##ₙ `r ##ₙ `x) ty <|> error
      unify goal `refl

    error = do
      `x ← quoteTC x
      `y ← quoteTC y
      typeError
        [ "trivial! failed: the values\n  "
        , termErr `x
        , "\nand\n  "
        , termErr `y
        , "\nare not extensionally equal by refl."
        ]

{-
trivial! serves to replace proofs like

  Nat-path λ x → funext λ y → Nat-path λ z → Homomorphism-path λ a → refl

since this is

  ext λ x y z a → refl

and that argument is precisely reflexivity for the computed identity
system which 'ext' is using. By the way, this example is totally made
up.
-}

opaque
  trivial!
    : ∀ {ℓ ℓr} {A : Type ℓ} {x y : A}
    → ⦃ r : Extensional A ℓr ⦄
    → {@(tactic trivial-worker r x y) p : Pathᵉ r x y}
    → x ≡ y
  trivial! ⦃ r ⦄ {p = p} = r .idsᵉ .to-path p

abstract
  unext : ∀ {ℓ ℓr} {A : Type ℓ} ⦃ e : Extensional A ℓr ⦄ {x y : A} → x ≡ y → e .Pathᵉ x y
  unext ⦃ e ⦄ {x = x} p = transport (λ i → e .Pathᵉ x (p i)) (e .reflᵉ x)

macro
  reext!
    : ∀ {ℓ ℓr} {A : Type ℓ} ⦃ ea : Extensional A ℓr ⦄ {x y : A}
    → x ≡ y → Term → TC ⊤
  reext! p goal = do
    `p ← quoteTC p
    unify goal (def (quote ext) [ argN (def (quote unext) [ argN `p ]) ])

Pathᵉ-is-hlevel
  : ∀ {ℓ ℓr} {A : Type ℓ} n (sa : Extensional A ℓr)
  → is-hlevel A (suc n)
  → ∀ {x y}
  → is-hlevel (Pathᵉ sa x y) n
Pathᵉ-is-hlevel n sa hl =
  Equiv→is-hlevel _ (identity-system-gives-path (sa .idsᵉ)) (Path-is-hlevel' _ hl _ _)

embedding→extensional
  : ∀ {ℓ ℓ' ℓr} {A : Type ℓ} {B : Type ℓ'}
  → (f : A ↪ B)
  → Extensional B ℓr
  → Extensional A ℓr
embedding→extensional f ext .Pathᵉ x y = Pathᵉ ext (f .fst x) (f .fst y)
embedding→extensional f ext .reflᵉ x = reflᵉ ext (f .fst x)
embedding→extensional f ext .idsᵉ =
  pullback-identity-system (ext .idsᵉ) f

iso→extensional
  : ∀ {ℓ ℓ' ℓr} {A : Type ℓ} {B : Type ℓ'}
  → Iso A B
  → Extensional B ℓr
  → Extensional A ℓr
iso→extensional f ext =
  embedding→extensional (Iso→Embedding f) ext

injection→extensional
  : ∀ {ℓ ℓ' ℓr} {A : Type ℓ} {B : Type ℓ'}
  → is-set B
  → {f : A → B}
  → (∀ {x y} → f x ≡ f y → x ≡ y)
  → Extensional B ℓr
  → Extensional A ℓr
injection→extensional b-set {f} inj ext =
  embedding→extensional (f , injective→is-embedding b-set f inj) ext

injection→extensional!
  : ∀ {ℓ ℓ' ℓr} {A : Type ℓ} {B : Type ℓ'}
  → {@(tactic hlevel-tactic-worker) sb : is-set B}
  → {f : A → B}
  → (∀ {x y} → f x ≡ f y → x ≡ y)
  → Extensional B ℓr
  → Extensional A ℓr
injection→extensional! {sb = b-set} = injection→extensional b-set

Σ-prop-extensional
  : ∀ {ℓ ℓ' ℓr} {A : Type ℓ} {B : A → Type ℓ'}
  → (∀ x → is-prop (B x))
  → Extensional A ℓr
  → Extensional (Σ A B) ℓr
Σ-prop-extensional bprop = embedding→extensional (fst , Subset-proj-embedding bprop)

instance
  Extensional-Σ-trunc
    : ∀ {ℓ ℓ' ℓr} {A : Type ℓ} {B : A → Type ℓ'}
    → ⦃ ea : Extensional A ℓr ⦄ → Extensional (Σ A λ x → ∥ B x ∥) ℓr
  Extensional-Σ-trunc ⦃ ea ⦄ = Σ-prop-extensional (λ x → hlevel 1) ea

  Extensional-Σ-□
    : ∀ {ℓ ℓ' ℓr} {A : Type ℓ} {B : A → Type ℓ'}
    → ⦃ ea : Extensional A ℓr ⦄ → Extensional (Σ A λ x → □ (B x)) ℓr
  Extensional-Σ-□ ⦃ ea ⦄ = Σ-prop-extensional (λ x → hlevel 1) ea

  Extensional-equiv
    : ∀ {ℓ ℓ' ℓr} {A : Type ℓ} {B : Type ℓ'}
    → ⦃ ea : Extensional (A → B) ℓr ⦄ → Extensional (A ≃ B) ℓr
  Extensional-equiv ⦃ ea ⦄ = Σ-prop-extensional (λ x → is-equiv-is-prop _) ea

  Extensional-tr-map
    : ∀ {ℓ ℓ' ℓr} {A : Type ℓ} {B : Type ℓ'}
    → {@(tactic hlevel-tactic-worker) bset : is-set B}
    → ⦃ _ : Extensional (A → B) ℓr ⦄
    → Extensional (∥ A ∥ → B) ℓr
  Extensional-tr-map {bset = bset} ⦃ ea ⦄ =
    injection→extensional (Π-is-hlevel 2 λ _ → bset) {f = λ f → f ∘ inc}
      (λ p → funext $ ∥-∥-elim (λ _ → bset _ _) (happly p)) ea

private module test where
  variable
    ℓ ℓ' ℓ'' : Level
    A B C : Type ℓ
    P Q R : A → Type ℓ

  _ : {f g : A → B} → ((x : A) → f x ≡ g x) → f ≡ g
  _ = ext

  _ : {f g : A × B → C} → ((a : A) (b : B) → f (a , b) ≡ g (a , b)) → f ≡ g
  _ = ext

  _ : {f g : Σ A P → B} → ((a : A) (b : P a) → f (a , b) ≡ g (a , b)) → f ≡ g
  _ = ext

  open Lift

  _ : {f g : Σ (Lift ℓ' A) (λ x → Lift ℓ' (P (x .lower))) → Lift ℓ'' B}
    → ((a : A) (b : P a) → f (lift a , lift b) .lower ≡ g (lift a , lift b) .lower)
    → f ≡ g
  _ = ext

  _ : {f g : A → B ≃ C} → ((a : A) (b : B) → f a .fst b ≡ g a .fst b) → f ≡ g
  _ = ext
