<!--
```agda
open import 1Lab.Function.Embedding
open import 1Lab.Reflection.HLevel
open import 1Lab.HIT.Truncation
open import 1Lab.HLevel.Closure
open import 1Lab.Type.Sigma
open import 1Lab.Inductive
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

open import Meta.Idiom
open import Meta.Bind
```
-->

```agda
module 1Lab.Function.Surjection where
```

<!--
```agda
private variable
  ℓ ℓ' : Level
  A B C : Type ℓ
```
-->

# Surjections {defines=surjection}

A function $f : A \to B$ is a **surjection** if, for each $b : B$, we
have $\| f^*b \|$: that is, all of its [[fibres]] are inhabited. Using
the notation for [[mere existence|merely]], we may write this as

$$
\forall (b : B),\ \exists (a : A),\ f(a) = b
$$.

which is evidently the familiar notion of surjection.

```agda
is-surjective : (A → B) → Type _
is-surjective f = ∀ b → ∥ fibre f b ∥
```

To abbreviate talking about surjections, we will use the notation $A
\epi B$, pronounced "$A$ **covers** $B$".

```agda
_↠_ : Type ℓ → Type ℓ' → Type (ℓ ⊔ ℓ')
A ↠ B = Σ[ f ∈ (A → B) ] is-surjective f
```

The notion of surjection is intimately connected with that of
[[quotient]], and in particular with the elimination principle into
[[propositions]]. We think of a surjection $A \to B$ as expressing that $B$
can be "glued together" by [[introducing paths between|path]] the
elements of $A$. Since any family of propositions respects these new
paths, we can prove a property of $B$ by showing it for the "generators"
coming from $A$:

```agda
is-surjective→elim-prop
  : (f : A ↠ B)
  → ∀ {ℓ} (P : B → Type ℓ)
  → (∀ x → is-prop (P x))
  → (∀ a → P (f .fst a))
  → ∀ x → P x
is-surjective→elim-prop (f , surj) P pprop pfa x =
  ∥-∥-rec (pprop _) (λ (x , p) → subst P p (pfa x)) (surj x)
```

When the type $B$ is a set, we can actually take this analogy all the
way to its conclusion: Given any cover $f : A \epi B$, we can produce an
equivalence between $B$ and the quotient of $A$ under the [[congruence]]
induced by $f$. See [[surjections are quotient maps]].

## Closure properties

The class of surjections contains the identity --- and thus every
equivalence --- and is closed under composition.

```agda
∘-is-surjective
  : {f : B → C} {g : A → B}
  → is-surjective f
  → is-surjective g
  → is-surjective (f ∘ g)
∘-is-surjective {f = f} fs gs x = do
  (f*x , p) ← fs x
  (g*fx , q) ← gs f*x
  pure (g*fx , ap f q ∙ p)

id-is-surjective : is-surjective {A = A} id
id-is-surjective x = inc (x , refl)

is-equiv→is-surjective : {f : A → B} → is-equiv f → is-surjective f
is-equiv→is-surjective eqv x = inc (eqv .is-eqv x .centre)
```

<!--
```agda
Equiv→Cover : A ≃ B → A ↠ B
Equiv→Cover f = f .fst , is-equiv→is-surjective (f .snd)
```
-->

## Relationship with equivalences

We have defined [[equivalences]] to be the maps with [[contractible]]
fibres; and surjections to be the maps with _inhabited_ fibres. It
follows that a surjection is an equivalence _precisely if_ its fibres
are also [[propositions]]; in other words, if it is an [[embedding]].

```agda
embedding-surjective→is-equiv
  : {f : A → B}
  → is-embedding f
  → is-surjective f
  → is-equiv f
embedding-surjective→is-equiv f-emb f-surj .is-eqv x = ∥-∥-out! do
  pt ← f-surj x
  pure $ is-prop∙→is-contr (f-emb x) pt
```

<!--
```agda
injective-surjective→is-equiv
  : {f : A → B}
  → is-set B
  → injective f
  → is-surjective f
  → is-equiv f
injective-surjective→is-equiv b-set f-inj =
  embedding-surjective→is-equiv (injective→is-embedding b-set _ f-inj)

injective-surjective→is-equiv!
  : {f : A → B} ⦃ b-set : H-Level B 2 ⦄
  → injective f
  → is-surjective f
  → is-equiv f
injective-surjective→is-equiv! =
  injective-surjective→is-equiv (hlevel 2)
```
-->

## Split surjective functions {defines="split-surjective"}

A function is **split surjective** if for each $b : B$ we have a designated
element of the fibre $f^*b$. Note that this is actually a *structure*
on $f$ instead of a property: in fact, the statement that every
surjection between sets is a split surjection is [[equivalent to the
axiom of choice|axiom-of-choice]].


```agda
split-surjective : (A → B) → Type _
split-surjective f = ∀ b → fibre f b
```
