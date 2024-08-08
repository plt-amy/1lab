open import 1Lab.Underlying
open import 1Lab.Type hiding (Σ-syntax)

module 1Lab.Membership where

-- Syntax class for the _∈_ notation. An instance
--
--   Membership A ℙA _
--
-- denotes, essentially, that ℙA has a preferred projection into
--
--   A → Type _
--
-- Note that this projection does not have to be an embedding, or even
-- injective; and x ∈ S does not necessarily need to be valued in
-- propositions, either. In practice, both of these conditions are
-- satisfied.

record Membership {ℓ ℓe} (A : Type ℓe) (ℙA : Type ℓ) ℓm : Type (ℓ ⊔ ℓe ⊔ lsuc ℓm) where
  field _∈_ : A → ℙA → Type ℓm
  infix 30 _∈_

open Membership ⦃ ... ⦄ using (_∈_) public
{-# DISPLAY Membership._∈_ i a b = a ∈ b #-}

-- The prototypical instance is given by functions into a universe:

instance
  Membership-pow
    : ∀ {ℓ ℓ'} {A : Type ℓ} {P : Type ℓ'} ⦃ u : Underlying P ⦄
    → Membership A (A → P) _
  Membership-pow = record { _∈_ = λ x S → ⌞ S x ⌟ }

-- If a type has membership, then it has a non-membership as well. Note
-- that this is a negative definition, while in some cases it might be
-- possible to implement ∉ as *positive* information.

_∉_ : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {ℙA : Type ℓ'} ⦃ m : Membership A ℙA ℓ'' ⦄
    → A → ℙA → Type ℓ''
x ∉ y = ¬ (x ∈ y)

infix 30 _∉_

-- Total space of a predicate.
∫ₚ
  : ∀ {ℓ ℓ' ℓ''} {X : Type ℓ} {ℙX : Type ℓ'} ⦃ m : Membership X ℙX ℓ'' ⦄
  → ℙX → Type _
∫ₚ {X = X} P = Σ[ x ∈ X ] x ∈ P

-- Notation typeclass for _⊆_. We could always define
--
--   S ⊆ T = ∀ x → x ∈ S → x ∈ T
--
-- but this doesn't work too well for collections where the element type
-- is more polymorphic than the collection type, e.g. sieves, where we
-- would instead like
--
--  S ⊆ T = ∀ {i} (x : F i) → x ∈ S → x ∈ T
--
-- Instead we can define _⊆_ as its own class, then write a default
-- instance in terms of _∈_.

record Inclusion {ℓ} (ℙA : Type ℓ) ℓi : Type (ℓ ⊔ lsuc (ℓi)) where
  field _⊆_ : ℙA → ℙA → Type ℓi
  infix 30 _⊆_

open Inclusion ⦃ ... ⦄ using (_⊆_) public
{-# DISPLAY Inclusion._⊆_ i a b = a ⊆ b #-}

instance
  Inclusion-default
    : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {ℙA : Type ℓ'} ⦃ m : Membership A ℙA ℓ'' ⦄
    → Inclusion ℙA (ℓ ⊔ ℓ'')
  Inclusion-default {A = A} = record { _⊆_ = λ S T → (a : A) → a ∈ S → a ∈ T }
  {-# INCOHERENT Inclusion-default #-}
