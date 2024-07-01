open import 1Lab.Reflection.Signature
open import 1Lab.Function.Embedding
open import 1Lab.Reflection.Record
open import 1Lab.Reflection.Subst
open import 1Lab.Equiv.Fibrewise
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

{-
Further automation of h-level proofs
------------------------------------

This module expands the setup for automation of h-level proofs that is
bootstrapped in 1Lab.HLevel.Closure with the following extra features:

* Establishing the h-level of 'is-hlevel' itself; at the base-case, this
  boils down to instances for `H-Level (is-prop A) (suc n)`.

* Support for computing h-levels of projections.

The second bullet point might seem a bit surprising: Agda has native
support for marking some projections as instances ("instance fields"),
so why not use that? The reason is twofold:

1.
  The fields would have to have type ∀ {k} → H-Level X (n + k), where n
  is the actual truncation level.

  This is not a big problem, since an n-truncated type is
  (n + k)-truncated, but it is slightly unnatural when compared to
  having is-hlevel X n.

2.
  Instance fields work by eta-expanding variables in the context. Put
  concretely, if we have

    record Set : Type₁ where
      field
        it  : Type₀
        prf : H-Level it 2

  then the following *would* work,

    module _ {X : Set} where
      _ : is-set (X .it)
      _ = hlevel 2

  but the following would not, since 'Y x' is not a variable in the
  context.

    module _ {X : Type} {Y : X → Set} where
      _ : ∀ {x} → is-hlevel (Y x .it)
      _ = hlevel 2

To handle this extended situation, we extend the graph of H-Level
instances with a very generic H-Level-projection instance which uses
tactic arguments to decompose (Y x .it) into an application of (.it) +
the argument (Y x).
-}

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
  want ← quoteTC want >>= normalise

  def head args ← reduce =<< quoteTC A
    where ty → typeError [ "H-Level: I do not know how to show that\n  " , termErr ty , "\nhas h-level\n  ", termErr want ]
  debugPrint "tactic.hlevel" 30 [ "H-Level: trying projections for term:\n  " , termErr (def head args), "\nwith head symbol ", nameErr head ]

  projection ← resetting do
    (mv , _) ← new-meta' (def (quote hlevel-projection) (argN (lit (name head)) ∷ []))
    get-instances mv >>= λ where
      [] → typeError
        [ "H-Level: There are no hints for treating the name " , nameErr head , " as a projection.\n"
        , "When showing that the type\n " , termErr (def head args)
        , "\nhas h-level " , termErr want , ".\n"
        ]

      (tm ∷ []) → unquoteTC {A = hlevel-projection head} =<< normalise tm

      insts@(_ ∷ _ ∷ _) → do
        tms ← quoteTC insts >>= normalise
        typeError
          [ "H-Level: Ambiguous inversions for projection\n  "
          , nameErr head
          , "\nAll of the following apply:\n"
          , termErr tms
          ]

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

  H-Level-Singleton : ∀ {ℓ} {A : Type ℓ} {a : A} {n : Nat} → H-Level (Singleton a) n
  H-Level-Singleton {n = n} = hlevel-instance (is-contr→is-hlevel n (contr _ Singleton-is-contr))

  {-# INCOHERENT H-Level-projection #-}
  {-# OVERLAPPING h-level-is-prop #-}
  {-# OVERLAPPING H-Level-Singleton #-}

open Data.Nat.Base using (0≤x ; s≤s' ; x≤x ; x≤sucy) public

private module _ {ℓ} {A : n-Type ℓ 2} {B : ∣ A ∣ → n-Type ℓ 3} where
  some-def = ∣ A ∣

  _ : is-hlevel (∣ A ∣ → ∣ A ∣) 2
  _ = hlevel {T = _ → _} 2

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
  P Q : A → Type ℓ

{-
In addition to the top-level 'hlevel' entry point, there are quite a few
helper functions which simplify use sites by hiding the repetitive
(hlevel n) arguments.
-}

el! : ∀ {ℓ} (A : Type ℓ) {n} ⦃ hl : H-Level A n ⦄ → n-Type ℓ n
el! A .∣_∣ = A
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

prop-over-ext!
  : (e : A ≃ B) (let module e = Equiv e)
  → ⦃ ∀ {a} → H-Level (P a) 1 ⦄
  → ⦃ ∀ {b} → H-Level (Q b) 1 ⦄
  → (∀ (a : A) → P a → Q (e.to a))
  → (∀ (b : B) → Q b → P (e.from b))
  → P ≃[ e ] Q
prop-over-ext! e = prop-over-ext e (hlevel 1) (hlevel 1)

Σ-prop-path!
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
  → ⦃ bxprop : ∀ {x} → H-Level (B x) 1 ⦄
  → {x y : Σ A B}
  → x .fst ≡ y .fst
  → x ≡ y
Σ-prop-path! = Σ-prop-path (λ x → hlevel 1)

Σ-prop-pathp!
  : ∀ {ℓ ℓ'} {A : I → Type ℓ} {B : ∀ i → A i → Type ℓ'}
  → ⦃ bxprop : ∀ {i x} → H-Level (B i x) 1 ⦄
  → {x : Σ (A i0) (B i0)} {y : Σ (A i1) (B i1)}
  → PathP A (x .fst) (y .fst)
  → PathP (λ i → Σ (A i) (B i)) x y
Σ-prop-pathp! = Σ-prop-pathp (λ _ _ → hlevel 1)

prop!
  : ∀ {ℓ} {A : I → Type ℓ} ⦃ aip : ∀ {i} → H-Level (A i) 1 ⦄ {x y}
  → PathP (λ i → A i) x y
prop! {A = A} {x} {y} = is-prop→pathp (λ i → hlevel 1) x y

injective→is-embedding!
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} ⦃ bset : H-Level B 2 ⦄ {f : A → B}
  → injective f
  → is-embedding f
injective→is-embedding! {f = f} inj = injective→is-embedding (hlevel 2) f inj

Iso→is-hlevel! : (n : Nat) → Iso B A → ⦃ _ : H-Level A n ⦄ → is-hlevel B n
Iso→is-hlevel! n i = Iso→is-hlevel n i (hlevel n)

{-
Metaprogram for defining instances of H-Level (R x) n, where R x is a
record type whose components can all immediately be seen to have h-level
n.

That is, this works for things like Cat.Morphism._↪_, since the H-Level
automation already works for showing that its representation as a Σ-type
has hlevel 2, but it does not work for Algebra.Group.is-group, since
that requires specific knowledge about is-group to work.

Can be used either for unquoteDecl or unquoteDef. In the latter case, it
is possible to give the generated instance a more specific context which
might help to automatically derive instances for more types.
-}

private
  record-hlevel-instance
    : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (n : Nat) ⦃ _ : H-Level A n ⦄
    → Iso B A
    → ∀ {k} ⦃ p : n ≤ k ⦄
    → H-Level B k
  record-hlevel-instance n im ⦃ p ⦄ = hlevel-instance $
    Iso→is-hlevel _ im (is-hlevel-le _ _ p (hlevel _))

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
