open import 1Lab.Reflection.Signature
open import 1Lab.Function.Embedding
open import 1Lab.Reflection.Record
open import 1Lab.Reflection.Subst
open import 1Lab.HLevel.Universe
open import 1Lab.HLevel.Closure
open import 1Lab.Reflection
open import 1Lab.Type.Sigma
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

open import Data.List.Base
open import Data.Nat.Base
open import Data.Id.Base
open import Data.Bool

open import Meta.Foldable

open import Prim.Data.Nat

module 1Lab.Reflection.HLevel where

-- | How to decompose an application of a record selector into something
-- which might have an h-level.
record hlevel-projection (proj : Name) : Type where
  field
    has-level : Name
    -- ^ The name of the h-level lemma. It must be sufficient to apply
    -- this name to the argument (see get-argument below); arg specs are
    -- not supported.
    get-level : Term → TC Term
    -- ^ Given an application of underlying-type, what h-level does this
    -- type have? Necessary for computing lifts.
    get-argument : List (Arg Term) → TC Term
    -- ^ Extract the argument out from under the application.
{-
Using projections
-----------------

Projection decomposition happens as follows; suppose we have some
neutral

  n = def (quote X) as

in order, every 'hlevel-projection' instance definition will be tried;
Let us call a generic instance I. If I.underlying-type == X, then we'll
use this instance, otherwise, we fail (i.e. backtrack and try another
projection).

To use this instance, the get-level and get-argument functions are
involved; get-argument must take 'as' and return some representative
sub-expression e. get-level will receive e's inferred type and must
return the h-level of the type n. Finally, we return

  I.has-level (get-argument e),

possibly wrapped in (k - get-level (get-argument e)) applications of
is-hlevel-suc.
-}

open hlevel-projection

is-hlevel-le : ∀ {ℓ} {A : Type ℓ} n k → n ≤ k → is-hlevel A n → is-hlevel A k
is-hlevel-le 0 k 0≤x p =
  is-contr→is-hlevel k p
is-hlevel-le 1 1 (s≤s 0≤x) p = p
is-hlevel-le 1 (suc (suc k)) (s≤s 0≤x) p x y =
  is-prop→is-hlevel-suc (is-prop→is-set p x y)
is-hlevel-le (suc (suc n)) (suc (suc k)) (s≤s le) p x y =
  is-hlevel-le (suc n) (suc k) le (p x y)

hlevel-proj : ∀ {ℓ} → Type ℓ → Nat → Term → TC ⊤
hlevel-proj A want goal = do
  want ← quoteTC want

  def head args ← reduce =<< quoteTC A
    where ty → typeError [ "H-Level: I do not know how to show that\n  " , termErr ty , "\nhas h-level\n", termErr want ]
  debugPrint "tactic.hlevel" 30 [ "H-Level: trying projections for term:\n  " , termErr (def head args), "\nwith head symbol ", nameErr head ]

  projection ← resetting do
    (mv , _) ← new-meta' (def (quote hlevel-projection) (argN (lit (name head)) ∷ []))
    get-instances mv >>= λ where
      (tm ∷ []) → unquoteTC {A = hlevel-projection head} =<< normalise tm
      []        → typeError [ "H-Level: Do not know how to invert projection\n  " , termErr (def head args) ]
      _         → typeError [ "H-Level: Ambiguous inversions for projection\n  " , nameErr head ]

  it   ← projection .get-argument args
  lvl  ← projection .get-level =<< infer-type it

  let
    soln = def (quote is-hlevel-le)
      [ argN lvl
      , argN want
      , argN (def (quote auto) [])
      , argN (def (projection .has-level) [ argN it ])
      ]

  unify goal soln
open hlevel-projection

instance
  open hlevel-projection
  hlevel-proj-n-type : hlevel-projection (quote n-Type.∣_∣)
  hlevel-proj-n-type .has-level = quote n-Type.is-tr
  hlevel-proj-n-type .get-level ty = do
    def (quote n-Type) (ell v∷ lv't v∷ []) ← reduce ty
      where _ → typeError $ "Type of thing isn't n-Type, it is " ∷ termErr ty ∷ []
    normalise lv't
  hlevel-proj-n-type .get-argument (_ ∷ _ ∷ it v∷ []) = pure it
  hlevel-proj-n-type .get-argument _ = typeError []

instance
  H-Level-projection
    : ∀ {ℓ} {A : Type ℓ} {n : Nat}
    → {@(tactic hlevel-proj A n) inst : is-hlevel A n}
    → H-Level A n
  H-Level-projection {inst = inst} = hlevel-instance inst

  H-Level-n-Type : ∀ {ℓ n k} ⦃ _ : suc n ≤ k ⦄ → H-Level (n-Type ℓ n) k
  H-Level-n-Type {n = n} {k} = hlevel-instance (is-hlevel-le (suc n) k auto (n-Type-is-hlevel n))

  h-level-is-prop : ∀ {ℓ} {A : Type ℓ} {n : Nat} ⦃ _ : 1 ≤ n ⦄ → H-Level (is-prop A) n
  h-level-is-prop ⦃ s≤s _ ⦄ = hlevel-instance (is-prop→is-hlevel-suc is-prop-is-prop)

  {-# INCOHERENT H-Level-projection #-}
  {-# OVERLAPPING h-level-is-prop #-}

open Data.Nat.Base using (0≤x ; s≤s' ; x≤x ; x≤sucy) public

hlevel' : ∀ {ℓ} {T : Type ℓ} (n : Nat) → ⦃ H-Level T n ⦄ → is-hlevel T n
hlevel' n ⦃ x ⦄ = H-Level.has-hlevel x

private module _ {ℓ} {A : n-Type ℓ 2} {B : ∣ A ∣ → n-Type ℓ 3} where
  some-def = ∣ A ∣

  _ : is-hlevel (∣ A ∣ → ∣ A ∣) 2
  _ = hlevel' {T = _ → _} 2

  _ : is-hlevel (Σ some-def λ x → ∣ B x ∣) 3
  _ = hlevel 3

  _ : ∀ a → is-hlevel (∣ A ∣ × ∣ A ∣ × (Nat → ∣ B a ∣)) 5
  _ = λ a → hlevel 5

  _ : ∀ a → is-hlevel (∣ A ∣ × ∣ A ∣ × (Nat → ∣ B a ∣)) 3
  _ = λ a → hlevel 3

  _ : is-hlevel ∣ A ∣ 2
  _ = hlevel 2

  _ : ∀ n → is-hlevel (n-Type ℓ n) (suc n)
  _ = λ n → hlevel (suc n)

  _ : ∀ n (x : n-Type ℓ n) → is-hlevel ∣ x ∣ (2 + n)
  _ = λ n x → hlevel (2 + n)

  _ : ∀ k {ℓ} {A : n-Type ℓ k} → is-hlevel ∣ A ∣ (4 + k)
  _ = λ k → hlevel (4 + k)

  _ : ∀ {ℓ} {A : Type ℓ} → is-prop ((x : A) → is-prop A)
  _ = hlevel 1

  _ : ∀ {ℓ} {A : Type ℓ} → is-prop ((x y : A) → is-prop A)
  _ = hlevel 1

  _ : ∀ {ℓ} {A : Type ℓ} → is-groupoid (is-hlevel A 5)
  _ = hlevel 3

private variable
  ℓ ℓ' : Level
  A B C : Type ℓ

-- In addition to using the macro as a.. well, macro, it can be used as
-- a tactic argument, to replace instance search by the more powerful
-- decomposition-projection mechanism of the tactic. We provide only
-- some of the most common helpers:
el! : ∀ {ℓ} (A : Type ℓ) {n} ⦃ hl : H-Level A n ⦄ → n-Type ℓ n
∣ el! A ∣ = A
el! A {n} .is-tr = hlevel n

biimp-is-equiv!
  : ⦃ aprop : H-Level A 1 ⦄ ⦃ bprop : H-Level B 1 ⦄
  → (f : A → B) → (B → A)
  → is-equiv f
biimp-is-equiv! = biimp-is-equiv (hlevel 1) (hlevel 1)

prop-ext!
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → ⦃ aprop : H-Level A 1 ⦄ ⦃ bprop : H-Level B 1 ⦄
  → (A → B) → (B → A)
  → A ≃ B
prop-ext! = prop-ext (hlevel 1) (hlevel 1)

Σ-prop-path!
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
  → ⦃ bxprop : ∀ {x} → H-Level (B x) 1 ⦄
  → {x y : Σ A B}
  → x .fst ≡ y .fst
  → x ≡ y
Σ-prop-path! = Σ-prop-path (λ x → hlevel 1)

prop!
  : ∀ {ℓ} {A : I → Type ℓ} ⦃ aip : H-Level (A i0) 1 ⦄
  → {x : A i0} {y : A i1}
  → PathP (λ i → A i) x y
prop! {A = A} {x} {y} =
  is-prop→pathp (λ i → coe0→i (λ j → is-prop (A j)) i (hlevel 1)) x y

injective→is-embedding!
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} ⦃ bset : H-Level B 2 ⦄
  → ∀ {f : A → B}
  → injective f
  → is-embedding f
injective→is-embedding! {f = f} inj = injective→is-embedding (hlevel 2) f inj

private
  record-hlevel-instance
    : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (n : Nat) ⦃ _ : H-Level A n ⦄
    → Iso B A
    → ∀ {k} ⦃ p : n ≤ k ⦄
    → H-Level B k
  record-hlevel-instance n im ⦃ p ⦄ = hlevel-instance $
    Iso→is-hlevel _ im (is-hlevel-le _ _ p (hlevel _))

Iso→is-hlevel! : (n : Nat) → Iso B A → ⦃ _ : H-Level A n ⦄ → is-hlevel B n
Iso→is-hlevel! n i = Iso→is-hlevel n i (hlevel n)

declare-record-hlevel : (n : Nat) → Name → Name → TC ⊤
declare-record-hlevel lvl inst rec = do
  (rec-tele , _) ← pi-view <$> get-type rec

  eqv ← helper-function-name rec "isom"
  declare-record-iso eqv rec

  let
    args    = reverse $ map-up (λ n (_ , arg i _) → arg i (var₀ n)) 2 (reverse rec-tele)

    head-ty = it H-Level ##ₙ def rec args ##ₙ var₀ 1

    inst-ty = unpi-view (map (λ (nm , arg _ ty) → nm , argH ty) rec-tele) $
      pi (argH (it Nat)) $ abs "n" $
      pi (argI (it _≤_ ##ₙ lit (nat lvl) ##ₙ var₀ 0)) $ abs "le" $
      head-ty

  declare (argI inst) inst-ty
  define-function inst
    [ clause [] [] (it record-hlevel-instance ##ₙ lit (nat lvl) ##ₙ def₀ eqv) ]
