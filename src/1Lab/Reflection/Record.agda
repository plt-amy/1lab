{-# OPTIONS -v refl:20 #-}
open import 1Lab.Reflection.Signature
open import 1Lab.Reflection
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

open import Meta.Foldable
open import Meta.Append

import Prim.Data.Sigma as S
import Prim.Data.Nat as N

module 1Lab.Reflection.Record where

field-names→sigma : ∀ {ℓ} {A : Type ℓ} → List A → Term
field-names→sigma [] = def (quote ⊤) []
field-names→sigma (_ ∷ []) = unknown
field-names→sigma (_ ∷ xs) =
  def (quote Σ) (lam visible (abs "_" (field-names→sigma xs)) v∷ [])

Fields : Type
Fields = List (Name × List Name)

field-names→paths : List (Arg Name) → Fields
field-names→paths [] = []
field-names→paths (arg _ nm ∷ []) = (nm , []) ∷ []
field-names→paths (arg _ x  ∷ (y ∷ ys)) with field-names→paths (y ∷ ys)
... | fields = (x , quote fst ∷ []) ∷ map (λ (f , p) → f , quote snd ∷ p) fields

record→iso : Name → (List (Arg Term) → TC Term) → TC Term
record→iso namen unfolded = go [] =<< normalise =<< infer-type (def namen []) where
  go : List ArgInfo → Term → TC Term
  go acc (pi argu@(arg i argTy) (abs s ty)) = do
    r ← extend-context "arg" argu $ go (i ∷ acc) ty
    pure $ pi (argH argTy) (abs s r)

  go acc (agda-sort _) = do
    let rec = def namen (reverse (map-up (λ n i → arg i (var n [])) 0 acc))
    unfolded ← unfolded (reverse (map-up (λ n _ → argH (var n [])) 0 acc))
    pure $ def (quote Iso) (rec v∷ unfolded v∷ [])

  go _ _ = typeError [ "Not a record type name: " , nameErr namen ]

undo-clause : Name × List Name → Clause
undo-clause (r-field , sel-path) = clause
  (("sig" , argN unknown) ∷ [])
  [ argN (proj (quote snd))
  , argN (proj (quote is-iso.inv))
  , argN (var 0)
  , argN (proj r-field)
  ]
  (foldr (λ n t → def n (t v∷ [])) (var 0 []) (reverse sel-path))

redo-clause : Name × List Name → Clause
redo-clause (r-field , sel-path) = clause
  (("rec" , argN unknown) ∷ [])
  (argN (proj (quote fst)) ∷ argN (var 0) ∷ map (argN ∘ proj) sel-path)
  (def r-field (var 0 [] v∷ []))

undo-redo-clause : Name × List Name → Clause
undo-redo-clause ((r-field , _)) = clause
  (("sig" , argN unknown) ∷ ("i" , argN (quoteTerm I)) ∷ [])
  ( argN (proj (quote snd)) ∷ argN (proj (quote is-iso.linv))
  ∷ argN (var 1) ∷ argN (var 0) ∷ argN (proj r-field) ∷ [])
  (def r-field (var 1 [] v∷ []))

redo-undo-clause : Name × List Name → Clause
redo-undo-clause (r-field , sel-path) = clause
  (("rec" , argN unknown) ∷ ("i" , argN (quoteTerm I)) ∷ [])
  (  [ argN (proj (quote snd)) , argN (proj (quote is-iso.rinv)) , argN (var 1) , argN (var 0) ]
  <> map (argN ∘ proj) sel-path)
  (foldr (λ n t → def n (t v∷ [])) (var 1 []) (reverse sel-path))

pi-term→sigma : Term → TC Term
pi-term→sigma (pi (arg _ x) (abs n (def n' _))) = pure x
pi-term→sigma (pi (arg _ x) (abs n y)) = do
  sig ← pi-term→sigma y
  pure $ def (quote S.Σ) (x v∷ lam visible (abs n sig) v∷ [])
pi-term→sigma _ = typeError (strErr "Not a record type constructor! " ∷ [])

instantiate' : Term → Term → Term
instantiate' (pi _ (abs _ xs)) (pi _ (abs _ b)) = instantiate' xs b
instantiate' (agda-sort _) tm = tm
instantiate' _ tm = tm

make-record-iso-sigma : Bool → TC Name → Name → TC Name
make-record-iso-sigma declare? getName `R = do
  `R-con , fields ← get-record-type `R

  let fields = field-names→paths fields

  `R-ty ← get-type `R
  con-ty ← get-type `R-con
  ty ← record→iso `R λ args → do
    let con-ty = instantiate' `R-ty con-ty
    `S ← pi-term→sigma con-ty
    pure `S

  nm ← getName
  case declare? of λ where
    true → declare (argN nm) ty
    false → pure tt

  define-function nm
    ( map redo-clause fields ++
      map undo-clause fields ++
      map redo-undo-clause fields ++
      map undo-redo-clause fields)
  pure nm

{-
Usage: slap

  unquoteDecl eqv = declare-record-iso eqv (quote Your-record)

in a module! The macro *DOES NOT WORK* in where clauses (or in record
definitions!). It does work in arbitrarily nested modules, and in the
top-level module, as the example below demonstrates: we can declare the
isomorphism adjacent to the record, outside the module where the record
is defined, and in a different module altogether.

All features of non-recursive records are supported, including
no-eta-equality, implicit and instance fields, and fields with implicit
arguments as types.
-}

declare-record-iso : Name → Name → TC ⊤
declare-record-iso nm rec = do
  make-record-iso-sigma true (pure nm) rec
  pure tt

define-record-iso : Name → Name → TC ⊤
define-record-iso nm rec = do
  make-record-iso-sigma false (pure nm) rec
  pure tt

private
  module _ {ℓ} (A : Type ℓ) where
    record T : Type ℓ where
      no-eta-equality
      field
        ⦃ fp ⦄ : A
        {f} : A → A
        fixed : f fp ≡ fp

    unquoteDecl eqv = declare-record-iso eqv (quote T)

    _ : Iso T (S.Σ A (λ fp → S.Σ (A → A) (λ f → f fp ≡ fp)))
    _ = eqv

  unquoteDecl eqv-outside = declare-record-iso eqv-outside (quote T)

  _ : {ℓ : Level} {A : Type ℓ} → Iso (T A) (S.Σ A (λ fp → S.Σ (A → A) (λ f → f fp ≡ fp)))
  _ = eqv-outside

  module _ (x : Nat) where
    unquoteDecl eqv-extra = declare-record-iso eqv-extra (quote T)

  _ : Nat → {ℓ : Level} {A : Type ℓ}
    → Iso (T A) (S.Σ A (λ fp → S.Σ (A → A) (λ f → f fp ≡ fp)))
  _ = eqv-extra


  record T2 : Type where
    -- works without eta equality too
    field
      some-field : Nat

  s-eqv : Iso T2 Nat
  unquoteDef s-eqv = define-record-iso s-eqv (quote T2)
