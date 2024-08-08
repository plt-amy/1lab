<!--
```agda
open import 1Lab.Prelude

open import Data.Bool
open import Data.Dec
open import Data.Sum

open import Homotopy.Space.Suspension.Properties
open import Homotopy.Space.Suspension

open import Meta.Invariant
```
-->

```agda
module 1Lab.Classical where
```

# The law of excluded middle {defines="LEM law-of-excluded-middle excluded-middle"}

While we do not assume any classical principles in the 1Lab, we can still state
them and explore their consequences.

The **law of excluded middle** (LEM) is the defining principle of classical logic,
which states that any proposition is either true or false (in other words,
[[decidable]]). Of course, assuming this as an axiom requires giving up canonicity:
we could prove that, for example, any Turing machine either halts or does not halt,
but this would not give us any computational information.

```agda
LEM : Type
LEM = ∀ (P : Ω) → Dec ∣ P ∣
```

Note that we cannot do without the assumption that $P$ is a proposition: the statement
that all types are decidable is [[inconsistent with univalence|LEM-infty]].

An equivalent statement of excluded middle is the **law of double negation
elimination** (DNE):

```agda
DNE : Type
DNE = ∀ (P : Ω) → ¬ ¬ ∣ P ∣ → ∣ P ∣
```

We show that these two statements are equivalent propositions.

```agda
LEM-is-prop : is-prop LEM
LEM-is-prop = hlevel 1

DNE-is-prop : is-prop DNE
DNE-is-prop = hlevel 1

LEM→DNE : LEM → DNE
LEM→DNE lem P = Dec-elim _ (λ p _ → p) (λ ¬p ¬¬p → absurd (¬¬p ¬p)) (lem P)

DNE→LEM : DNE → LEM
DNE→LEM dne P = dne (el (Dec ∣ P ∣) (hlevel 1)) λ k → k (no λ p → k (yes p))

LEM≃DNE : LEM ≃ DNE
LEM≃DNE = prop-ext LEM-is-prop DNE-is-prop LEM→DNE DNE→LEM
```

## Weak excluded middle {defines="weak-excluded-middle"}

The **weak law of excluded middle** (WLEM) is a slightly weaker variant
of excluded middle which asserts that every proposition is either false
or not false.

```agda
WLEM : Type
WLEM = ∀ (P : Ω) → Dec (¬ ∣ P ∣)
```

As the name suggests, the law of excluded middle implies the weak law
of excluded middle.

```agda
LEM→WLEM : LEM → WLEM
LEM→WLEM lem P = lem (P →Ω ⊥Ω)
```

The weak law of excluded middle is also a proposition.

```agda
WLEM-is-prop : is-prop WLEM
WLEM-is-prop = hlevel 1
```

## The axiom of choice {defines="axiom-of-choice"}

The **axiom of choice** is a stronger classical principle which allows us to commute
propositional truncations past Π types.

```agda
Axiom-of-choice : Typeω
Axiom-of-choice =
  ∀ {ℓ ℓ'} {B : Type ℓ} {P : B → Type ℓ'}
  → is-set B → (∀ b → is-set (P b))
  → (∀ b → ∥ P b ∥)
  → ∥ (∀ b → P b) ∥
```

Like before, the assumptions that $A$ is a set and $P$ is a family of sets are
required to avoid running afoul of univalence.

<!--
```agda
_ = Fibration-equiv
```
-->

An equivalent and sometimes useful statement is that all surjections between sets
merely have a section. This is essentially jumping to the other side of the
`fibration equivalence`{.Agda ident=Fibration-equiv}.

```agda
Surjections-split : Typeω
Surjections-split =
  ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → is-set A → is-set B
  → (f : A → B)
  → is-surjective f
  → ∥ (∀ b → fibre f b) ∥
```

We show that these two statements are logically equivalent^[they are also
propositions, but since they live in `Typeω`{.Agda} we cannot easily say that].

```agda
AC→Surjections-split : Axiom-of-choice → Surjections-split
AC→Surjections-split ac Aset Bset f =
  ac Bset (fibre-is-hlevel 2 Aset Bset f)

Surjections-split→AC : Surjections-split → Axiom-of-choice
Surjections-split→AC ss {P = P} Bset Pset h = ∥-∥-map
  (Equiv.to (Π-cod≃ (Fibre-equiv P)))
  (ss (Σ-is-hlevel 2 Bset Pset) Bset fst λ b →
    ∥-∥-map (Equiv.from (Fibre-equiv P b)) (h b))
```

We can show that the axiom of choice implies the law of excluded middle;
this is sometimes known as the Diaconescu-Goodman-Myhill theorem^[not to be confused
with [[Diaconescu's theorem]] in topos theory].

Given a proposition $P$, we consider the [[suspension]] of $P$: the type $\Sigma P$
is a set with two points and a path between them if and only if $P$ holds.

Since $\Sigma P$ admits a surjection from the booleans, the axiom of choice merely
gives us a section $\Sigma P \to 2$.

```agda
module _ (split : Surjections-split) (P : Ω) where
  section : ∥ ((x : Susp ∣ P ∣) → fibre 2→Σ x) ∥
  section = split (hlevel 2) (Susp-prop-is-set (hlevel 1)) 2→Σ 2→Σ-surjective
```

But a section is always injective, and the booleans are [[discrete]], so we can
prove that $\Sigma P$ is also discrete. Since the path type $N \equiv S$ in $\Sigma P$
is equivalent to $P$, this concludes the proof.

```agda
  Discrete-ΣP : Discrete (Susp ∣ P ∣)
  Discrete-ΣP = ∥-∥-rec (Dec-is-hlevel 1 (Susp-prop-is-set (hlevel 1) _ _))
    (λ f → Discrete-inj (fst ∘ f) (right-inverse→injective 2→Σ (snd ∘ f))
                        Discrete-Bool)
    section

  AC→LEM : Dec ∣ P ∣
  AC→LEM = Susp-prop-path (hlevel 1) <≃> Discrete-ΣP
```
