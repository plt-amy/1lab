open import 1Lab.HLevel.Universe
open import 1Lab.HIT.Truncation hiding (∃-syntax)
open import 1Lab.HLevel.Closure
open import 1Lab.Resizing
open import 1Lab.HLevel
open import 1Lab.Path
open import 1Lab.Type hiding (Σ-syntax)

open import Data.Bool.Base

module 1Lab.Underlying where

-- Notation class for types which have a chosen projection into a
-- universe, i.e. a preferred "underlying type".
record Underlying {ℓ} (T : Type ℓ) : Typeω where
  field
    ℓ-underlying : Level
    ⌞_⌟          : T → Type ℓ-underlying

open Underlying ⦃ ... ⦄ using (⌞_⌟) public
open Underlying using (ℓ-underlying)

-- Workaround for Agda bug https://github.com/agda/agda/issues/6588 —
-- the principal (instance) argument is reified as visible, so we can
-- drop it using a display form.
{-# DISPLAY Underlying.⌞_⌟ f x = ⌞ x ⌟ #-}

instance
-- For universes, we use the standard notion of "underlying type".

  Underlying-Type : ∀ {ℓ} → Underlying (Type ℓ)
  Underlying-Type {ℓ} .ℓ-underlying = ℓ
  Underlying-Type .⌞_⌟ x = x

  Underlying-n-Type : ∀ {ℓ n} → Underlying (n-Type ℓ n)
  Underlying-n-Type {ℓ} .ℓ-underlying = ℓ
  Underlying-n-Type .⌞_⌟ x = ∣ x ∣

  Underlying-prop : Underlying Ω
  Underlying-prop .ℓ-underlying = lzero
  Underlying-prop .⌞_⌟ x = ∣ x ∣

  -- Lifting instances: for Σ-types, we think of (Σ A B) as "A with
  -- B-structure", so the underlying type is that of A; For Lift, there
  -- is no choice.
  Underlying-Σ
    : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
    → ⦃ ua : Underlying A ⦄
    → Underlying (Σ A B)
  Underlying-Σ ⦃ ua ⦄ .ℓ-underlying = ua .ℓ-underlying
  Underlying-Σ .⌞_⌟ x               = ⌞ x .fst ⌟

  Underlying-Lift
    : ∀ {ℓ ℓ'} {A : Type ℓ} ⦃ ua : Underlying A ⦄
    → Underlying (Lift ℓ' A)
  Underlying-Lift ⦃ ua ⦄ .ℓ-underlying = ua .ℓ-underlying
  Underlying-Lift .⌞_⌟ x = ⌞ x .Lift.lower ⌟

  Underlying-Bool : Underlying Bool
  Underlying-Bool = record { ⌞_⌟ = So }

-- The converse of to-is-true, generalised slightly. If P and Q are
-- identical inhabitants of some type of structured types, and Q's
-- underlying type is contractible, then P is inhabited. P's underlying
-- type is obviously also contractible, but adding this as an instance
-- would ruin type inference (I tried.)
from-is-true
  : ∀ {ℓ} {A : Type ℓ} ⦃ _ : Underlying A ⦄ {P Q : A} ⦃ _ : H-Level ⌞ Q ⌟ 0 ⦄
  → P ≡ Q
  → ⌞ P ⌟
from-is-true prf = subst ⌞_⌟ (sym prf) (hlevel 0 .centre)

-- Notation class for type families which are "function-like" (always
-- nondependent). Slight generalisation of the homs of concrete
-- categories.
record Funlike {ℓ ℓ' ℓ''} (A : Type ℓ) (arg : Type ℓ') (out : arg → Type ℓ'') : Type (ℓ ⊔ ℓ' ⊔ ℓ'') where
  field
    _#_ : A → (x : arg) → out x
  infixl 999 _#_

open Funlike ⦃ ... ⦄ using (_#_) public
{-# DISPLAY Funlike._#_ p f x = f # x #-}

-- Sections of the _#_ operator tend to be badly-behaved since they
-- introduce an argument x : ⌞ ?0 ⌟ whose Underlying instance meta
-- "mutually blocks" the Funlike instance meta. Use the prefix version
-- instead.
apply
  : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : A → Type ℓ'} {F : Type ℓ''}
  → ⦃ _ : Funlike F A B ⦄
  → F → (x : A) → B x
apply = _#_

-- Shortcut for ap (apply ...)
ap#
  : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : A → Type ℓ'} {F : Type ℓ''}
  → ⦃ _ : Funlike F A B ⦄
  → (f : F) {x y : A} (p : x ≡ y) → PathP (λ i → B (p i)) (f # x) (f # y)
ap# f = ap (apply f)

-- Generalised happly.
_#ₚ_
  : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : A → Type ℓ'} {F : Type ℓ''}
  → ⦃ _ : Funlike F A B ⦄
  → {f g : F} → f ≡ g → (x : A) → f # x ≡ g # x
f #ₚ x = ap₂ _#_ f refl

instance
  Funlike-Π : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} → Funlike ((x : A) → B x) A B
  Funlike-Π = record { _#_ = id }

  Funlike-Homotopy
    : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {f g : ∀ x → B x}
    → Funlike (f ≡ g) A (λ x → f x ≡ g x)
  Funlike-Homotopy = record { _#_ = happly }

-- Generalised "sections" (e.g. of a presheaf) notation.
_ʻ_
  : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : A → Type ℓ'} {F : Type ℓ''}
  → ⦃ _ : Funlike F A B ⦄
  → F → (x : A) → ⦃ _ : Underlying (B x) ⦄
  → Type _
F ʻ x = ⌞ F # x ⌟

infix 999 _ʻ_

-- Generalisations of the syntax for Σ and ∃ which allow the domain to
-- be something with an Underlying instance rather than a literal type.
-- E.g. if
--
--   C : Precategory o ℓ
--
-- then `Σ[ x ∈ C ] P x` means `Σ (C .Ob) P`.

Σ-syntax
  : ∀ {ℓ ℓ'} {A : Type ℓ} ⦃ _ : Underlying A ⦄ (X : A) (F : ⌞ X ⌟ → Type ℓ')
  → Type _
Σ-syntax X F = Σ ⌞ X ⌟ F

∃-syntax
  : ∀ {ℓ ℓ'} {A : Type ℓ} ⦃ _ : Underlying A ⦄ (X : A) (F : ⌞ X ⌟ → Type ℓ')
  → Type _
∃-syntax X F = ∥ Σ ⌞ X ⌟ F ∥

syntax Σ-syntax X (λ x → F) = Σ[ x ∈ X ] F
syntax ∃-syntax X (λ x → F) = ∃[ x ∈ X ] F
infix 5 Σ-syntax ∃-syntax
