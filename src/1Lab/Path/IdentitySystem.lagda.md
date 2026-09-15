<!--
```agda
open import 1Lab.Function.Embedding
open import 1Lab.Equiv.Fibrewise
open import 1Lab.HLevel.Closure
open import 1Lab.Type.Sigma
open import 1Lab.Univalence
open import 1Lab.Type.Pi
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

open import Data.Dec.Base
```
-->

```agda
module 1Lab.Path.IdentitySystem where
```

# Identity systems {defines=identity-system}

An **identity system** is a way of characterising the path spaces of a
particular type, without necessarily having to construct a full
encode-decode equivalence. Essentially, the data of an identity system
is precisely the data required to implement _path induction_, a.k.a. the
J eliminator. Any type with the data of an identity system satisfies its
own J, and conversely, if the type satisfies J, it is an identity
system.

We unravel the definition of being an identity system into the following
data, using a translation that takes advantage of cubical type theory's
native support for paths-over-paths:

```agda
record
  is-identity-system {ℓ ℓ'} {A : Type ℓ}
    (R : A → A → Type ℓ')
    (refl : ∀ a → R a a)
    : Type (ℓ ⊔ ℓ')
  where
  no-eta-equality
  field
    to-path      : ∀ {a b} → R a b → a ≡ b
    to-path-over
      : ∀ {a b} (p : R a b)
      → PathP (λ i → R a (to-path p i)) (refl a) p

  is-contr-ΣR : ∀ {a} → is-contr (Σ A (R a))
  is-contr-ΣR .centre    = _ , refl _
  is-contr-ΣR .paths x i = to-path (x .snd) i , to-path-over (x .snd) i

open is-identity-system public
```

As mentioned before, the data of an identity system gives us exactly
what is required to prove J for the relation $R$. This is essentially
the decomposition of J into _contractibility of singletons_, but with
singletons replaced by $R$-singletons.

```agda
IdsJ
  : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {R : A → A → Type ℓ'} {r : ∀ a → R a a} {a : A}
  → is-identity-system R r
  → (P : ∀ b → R a b → Type ℓ'')
  → P a (r a)
  → ∀ {b} s → P b s
IdsJ ids P pr s =
  transport (λ i → P (ids .to-path s i) (ids .to-path-over s i)) pr
```

<!--
```agda
IdsJ-refl
  : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {R : A → A → Type ℓ'} {r : ∀ a → R a a} {a : A}
  → (ids : is-identity-system R r)
  → (P : ∀ b → R a b → Type ℓ'')
  → (x : P a (r a))
  → IdsJ ids P x (r a) ≡ x
IdsJ-refl {R = R} {r = r} {a = a} ids P x =
  transport (λ i → P (ids .to-path (r a) i) (ids .to-path-over (r a) i)) x ≡⟨⟩
  subst P' (λ i → ids .to-path (r a) i , ids .to-path-over (r a) i) x      ≡⟨ ap (λ e → subst P' e x) lemma ⟩
  subst P' refl x                                                          ≡⟨ transport-refl x ⟩
  x                                                                        ∎
  where
    P' : Σ _ (R a) → Type _
    P' (b , r) = P b r

    lemma : Σ-pathp (ids .to-path (r a)) (ids .to-path-over (r a)) ≡ refl
    lemma = is-contr→is-set (is-contr-ΣR ids) _ _ _ _

to-path-refl-coh
  : ∀ {ℓ ℓ'} {A : Type ℓ} {R : A → A → Type ℓ'} {r : ∀ a → R a a}
  → (ids : is-identity-system R r)
  → ∀ a
  → (Σ-pathp (ids .to-path (r a)) (ids .to-path-over (r a))) ≡ refl
to-path-refl-coh {r = r} ids a =
  is-contr→is-set (is-contr-ΣR ids) _ _
    (Σ-pathp (ids .to-path (r a)) (ids .to-path-over (r a)))
    refl

to-path-refl
  : ∀ {ℓ ℓ'} {A : Type ℓ} {R : A → A → Type ℓ'} {r : ∀ a → R a a} {a : A}
  → (ids : is-identity-system R r)
  → ids .to-path (r a) ≡ refl
to-path-refl {r = r} {a = a} ids = ap (ap fst) $ to-path-refl-coh ids a

to-path-over-refl
  : ∀ {ℓ ℓ'} {A : Type ℓ} {R : A → A → Type ℓ'} {r : ∀ a → R a a} {a : A}
  → (ids : is-identity-system R r)
  → PathP (λ i → PathP (λ j → R a (to-path-refl {a = a} ids i j)) (r a) (r a))
      (ids .to-path-over (r a))
      refl
to-path-over-refl {a = a} ids = ap (ap snd) $ to-path-refl-coh ids a
```
-->

Note that for any $(R, r)$, the type of identity system data on $(R, r)$
is a [[proposition]]. This is because it is exactly equivalent to the type
$\sum_a (R a)$ being contractible for every $a$, which is a proposition
by standard results. One direction is `is-contr-ΣR`{.Agda}; we prove
the converse direction now.

```agda
contr→identity-system
  : ∀ {ℓ ℓ'} {A : Type ℓ} {R : A → A → Type ℓ'} {r : ∀ a → R a a}
  → (∀ {a} → is-contr (Σ _ (R a)))
  → is-identity-system R r
contr→identity-system {R = R} {r} c = ids where
  paths' : ∀ {a} (p : Σ _ (R a)) → (a , r a) ≡ p
  paths' _ = is-contr→is-prop c _ _

  ids : is-identity-system R r
  ids .to-path p = ap fst (paths' (_ , p))
  ids .to-path-over p = ap snd (paths' (_ , p))
```

If we have a relation $R$ together with reflexivity witness $r$, then
any equivalence $f : R(a, b) \simeq (a \equiv b)$ equips $(R, r)$ with
the structure of an identity system, by contractibility of singletons. Of
course if we do not particularly care about the specific reflexivity
witness, we can simply define $r$ as $f\inv(\refl)$.

```agda
equiv-path→identity-system
  : ∀ {ℓ ℓ'} {A : Type ℓ} {R : A → A → Type ℓ'} {r : ∀ a → R a a}
  → (∀ {a b} → R a b ≃ (a ≡ b))
  → is-identity-system R r
equiv-path→identity-system eqv = contr→identity-system $
  Equiv→is-hlevel 0 ((total (λ _ → eqv .fst) , equiv→total (eqv .snd)))
    Singleton-is-contr
```

Conversely, any identity system $(R, r)$ implies an equivalence
$R(a, b) \simeq (a \equiv b)$.

```agda
identity-system-gives-path
  : ∀ {ℓ ℓ'} {A : Type ℓ} {R : A → A → Type ℓ'} {r : ∀ a → R a a}
  → is-identity-system R r
  → ∀ {a b} → R a b ≃ (a ≡ b)
identity-system-gives-path {R = R} {r = r} ids =
  Iso→Equiv (ids .to-path , iso from ri li) where
    from : ∀ {a b} → a ≡ b → R a b
    from {a = a} p = transport (λ i → R a (p i)) (r a)

    ri : ∀ {a b} → is-right-inverse (from {a} {b}) (ids .to-path)
    ri = J (λ y p → ids .to-path (from p) ≡ p)
           ( ap (ids .to-path) (transport-refl _)
           ∙ to-path-refl ids)

    li : ∀ {a b} → is-left-inverse (from {a} {b}) (ids .to-path)
    li = IdsJ ids (λ y p → from (ids .to-path p) ≡ p)
          ( ap from (to-path-refl ids)
          ∙ transport-refl _ )
```

## Based identity systems {defines="based-identity-system unary-identity-system"}

It is sometimes useful to characterise the *based* identity type at
a point $a : A$, i.e. the family $a \is -$, instead of the whole
binary family of paths $- \equiv -$. To that end, we introduce a unary
variant of identity systems called **based identity systems**, or
**unary identity systems**.

```agda
record
  is-based-identity-system {ℓ ℓ'} {A : Type ℓ}
    (a : A)
    (C : A → Type ℓ')
    (refl : C a)
    : Type (ℓ ⊔ ℓ')
  where
  no-eta-equality
  field
    to-path : ∀ {b} → C b → a ≡ b
    to-path-over
      : ∀ {b} (p : C b)
      → PathP (λ i → C (to-path p i)) refl p

open is-based-identity-system public

is-contr-ΣC
  : ∀ {ℓ ℓ'} {A : Type ℓ} {a : A} {C : A → Type ℓ'} {r : C a}
  → is-based-identity-system a C r
  → is-contr (Σ A C)
is-contr-ΣC {r = r} ids .centre         = _ , r
is-contr-ΣC {r = r} ids .paths x i .fst = ids .to-path (x .snd) i
is-contr-ΣC {r = r} ids .paths x i .snd = ids .to-path-over (x .snd) i
```

As previously, the data of a based identity system at $a : A$ is
precisely what is required to implement *based* path induction at $a$.

```agda
IdsJ-based
  : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {a : A} {C : A → Type ℓ'} {r : C a}
  → is-based-identity-system a C r
  → (P : ∀ b → C b → Type ℓ'')
  → P a r
  → ∀ {b} s → P b s
IdsJ-based ids P pr s = transport
  (λ i → P (ids .to-path s i) (ids .to-path-over s i)) pr
```

<!--
```agda
IdsJ-based-refl
  : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {a : A} {C : A → Type ℓ'} {r : C a}
  → (ids : is-based-identity-system a C r)
  → (P : ∀ b → C b → Type ℓ'')
  → (x : P a r)
  → IdsJ-based ids P x r ≡ x
IdsJ-based-refl {C = C} {r = r} ids P x =
  transport (λ i → P (ids .to-path r i) (ids .to-path-over r i)) x ≡⟨⟩
  subst P' (λ i → ids .to-path r i , ids .to-path-over r i) x      ≡⟨ ap (λ e → subst P' e x) lemma ⟩
  subst P' refl x                                                  ≡⟨ transport-refl x ⟩
  x                                                                ∎
  where
    P' : Σ _ C → Type _
    P' (b , c) = P b c

    lemma : Σ-pathp (ids .to-path r) (ids .to-path-over r) ≡ refl
    lemma = is-contr→is-set (is-contr-ΣC ids) _ _ _ _

to-path-based-refl-coh
  : ∀ {ℓ ℓ'} {A : Type ℓ} {a : A} {C : A → Type ℓ'} {r : C a}
  → (ids : is-based-identity-system a C r)
  → (Σ-pathp (ids .to-path r) (ids .to-path-over r)) ≡ refl
to-path-based-refl-coh {r = r} ids =
  is-contr→is-set (is-contr-ΣC ids) _ _
    (Σ-pathp (ids .to-path r) (ids .to-path-over r))
    refl

to-path-based-refl
  : ∀ {ℓ ℓ'} {A : Type ℓ} {a : A} {C : A → Type ℓ'} {r : C a}
  → (ids : is-based-identity-system a C r)
  → ids .to-path r ≡ refl
to-path-based-refl ids = ap (ap fst) $ to-path-based-refl-coh ids

to-path-over-based-refl
  : ∀ {ℓ ℓ'} {A : Type ℓ} {a : A} {C : A → Type ℓ'} {r : C a}
  → (ids : is-based-identity-system a C r)
  → PathP (λ i → PathP (λ j → C (to-path-based-refl ids i j)) r r)
      (ids .to-path-over r)
      refl
to-path-over-based-refl ids = ap (ap snd) $ to-path-based-refl-coh ids

contr→based-identity-system
  : ∀ {ℓ ℓ'} {A : Type ℓ} {a : A} {C : A → Type ℓ'} {r : C a}
  → is-contr (Σ _ C)
  → is-based-identity-system a C r
contr→based-identity-system {a = a} {C = C} {r} c = ids where
  paths' : ∀ (p : Σ _ C) → (a , r) ≡ p
  paths' _ = is-contr→is-prop c _ _

  ids : is-based-identity-system a C r
  ids .to-path p = ap fst (paths' (_ , p))
  ids .to-path-over p = ap snd (paths' (_ , p))

based-identity-system-gives-path
  : ∀ {ℓ ℓ'} {A : Type ℓ} {a : A} {C : A → Type ℓ'} {r : C a}
  → is-based-identity-system a C r
  → ∀ {b} → C b ≃ (a ≡ b)
based-identity-system-gives-path {a = a} {C = C} {r = r} ids =
  Iso→Equiv (ids .to-path , iso from ri li) where
    from : ∀ {b} → a ≡ b → C b
    from p = subst C p r

    ri : ∀ {b} → is-right-inverse (from {b}) (ids .to-path)
    ri = J (λ y p → ids .to-path (from p) ≡ p)
           ( ap (ids .to-path) (transport-refl _)
           ∙ to-path-based-refl ids)

    li : ∀ {b} → is-left-inverse (from {b}) (ids .to-path)
    li = IdsJ-based ids (λ y p → from (ids .to-path p) ≡ p)
                        ( ap from (to-path-based-refl ids)
                        ∙ transport-refl _)
```
-->

## In subtypes

Let $f : A \mono B$ be an embedding. If $(R, r)$ is an identity system
on $B$, then it can be pulled back along $f$ to an identity system on
$A$.

```agda
module
  _ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'}
    {R : B → B → Type ℓ''} {r : ∀ b → R b b}
    (ids : is-identity-system R r)
    (f : A ↪ B)
  where

  pullback-identity-system
    : is-identity-system (λ x y → R (f .fst x) (f .fst y)) (λ _ → r _)
  pullback-identity-system .to-path {a} {b} x = ap fst $
    f .snd (f .fst b) (a , ids .to-path x) (b , refl)
  pullback-identity-system .to-path-over {a} {b} p i =
    comp
      (λ j → R (f .fst a) (f .snd (f .fst b) (a , ids .to-path p) (b , refl) i .snd (~ j)))
      (∂ i) λ where
      k (k = i0) → ids .to-path-over p (~ k)
      k (i = i0) → ids .to-path-over p (~ k ∨ i)
      k (i = i1) → p
```

This is actually part of an equivalence: if the equality identity
system on $B$ (thus any identity system) can be pulled back along $f$,
then $f$ is an embedding.

```agda
identity-system→embedding
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → (f : A → B)
  → is-identity-system (λ x y → f x ≡ f y) (λ _ → refl)
  → is-embedding f
identity-system→embedding f ids = cancellable→embedding
  (identity-system-gives-path ids)
```

<!--
```agda
module
  _ {ℓ ℓ'} {A : Type ℓ}
    {R S : A → A → Type ℓ'}
    {r : ∀ a → R a a} {s : ∀ a → S a a}
    (ids : is-identity-system R r)
    (eqv : ∀ x y → R x y ≃ S x y)
    (pres : ∀ x → eqv x x .fst (r x) ≡ s x)
  where

  transfer-identity-system : is-identity-system S s
  transfer-identity-system .to-path sab = ids .to-path (Equiv.from (eqv _ _) sab)
  transfer-identity-system .to-path-over {a} {b} p i = hcomp (∂ i) λ where
    j (j = i0) → Equiv.to (eqv _ _) (ids .to-path-over (Equiv.from (eqv _ _) p) i)
    j (i = i0) → pres a j
    j (i = i1) → Equiv.ε (eqv _ _) p j
```
-->

## Univalence

Note that univalence is precisely the statement that equivalences are an
identity system on the universe:

```agda
univalence-identity-system
  : ∀ {ℓ} → is-identity-system {A = Type ℓ} _≃_ λ _ → id , id-equiv
univalence-identity-system .to-path = ua
univalence-identity-system .to-path-over p =
  Σ-prop-pathp (λ _ → is-equiv-is-prop) $ funextP $ λ a → path→ua-pathp p refl
```

<!--
```agda
Path-identity-system
  : ∀ {ℓ} {A : Type ℓ} → is-identity-system (Path A) (λ _ → refl)
Path-identity-system .to-path p = p
Path-identity-system .to-path-over p i j = p (i ∧ j)

is-identity-system-is-prop
  : ∀ {ℓ ℓ'} {A : Type ℓ} {R : A → A → Type ℓ'} {r : ∀ a → R a a}
  → is-prop (is-identity-system R r)
is-identity-system-is-prop {A = A} {R} {r} =
  retract→is-hlevel 1 from to cancel λ x y i a → is-contr-is-prop (x a) (y a) i
  where
    to : is-identity-system R r → ∀ x → is-contr (Σ A (R x))
    to ids x = is-contr-ΣR ids

    from : (∀ x → is-contr (Σ A (R x))) → is-identity-system R r
    from x = contr→identity-system (x _)

    cancel'
      : ∀ (x : is-identity-system R r) {a b} (s : R a b)
      → PathP (λ i → (a , r a) ≡ (b , s))
        (is-contr-ΣR (from (to x)) .paths (b , s))
        (is-contr-ΣR x .paths (b , s))
    cancel' x s = is-prop→squarep (λ _ _ → is-contr→is-prop (is-contr-ΣR x)) _ _ _ _

    cancel : is-left-inverse from to
    cancel x i .to-path s = ap fst (cancel' x s i)
    cancel x i .to-path-over s = ap snd (cancel' x s i)

instance
  H-Level-is-identity-system
    : ∀ {ℓ ℓ'} {A : Type ℓ} {R : A → A → Type ℓ'} {r : ∀ a → R a a} {n}
    → H-Level (is-identity-system R r) (suc n)
  H-Level-is-identity-system = prop-instance is-identity-system-is-prop

identity-system→hlevel
  : ∀ {ℓ ℓ'} {A : Type ℓ} n {R : A → A → Type ℓ'} {r : ∀ x → R x x}
  → is-identity-system R r
  → (∀ x y → is-hlevel (R x y) n)
  → is-hlevel A (suc n)
identity-system→hlevel zero ids hl x y = ids .to-path (hl _ _ .centre)
identity-system→hlevel (suc n) ids hl x y =
  Equiv→is-hlevel (suc n) (identity-system-gives-path ids e⁻¹) (hl x y)
```
-->

## Sets and Hedberg's theorem {defines="hedberg's-theorem"}

We now apply the general theory of identity systems to something a lot
more mundane: recognising sets. An immediate consequence of having an
identity system $(R, r)$ on a type $A$ is that, if $R$ is pointwise an
$n$-type, then $A$ is an $(n+1)$-type. Now, if $R$ is a reflexive family
of propositions, then all we need for $(R, r)$ to be an identity system
is that $R(x, y) \to x = y$, by the previous observation, this implies
$A$ is a set.

```agda
set-identity-system
  : ∀ {ℓ ℓ'} {A : Type ℓ} {R : A → A → Type ℓ'} {r : ∀ x → R x x}
  → (∀ x y → is-prop (R x y))
  → (∀ {x y} → R x y → x ≡ y)
  → is-identity-system R r
set-identity-system rprop rpath .to-path = rpath
set-identity-system rprop rpath .to-path-over p =
  is-prop→pathp (λ i → rprop _ _) _ p
```

<!--
```agda
set-identity-system→hlevel
  : ∀ {ℓ ℓ'} {A : Type ℓ} (R : A → A → Type ℓ') (r : ∀ x → R x x)
  → (∀ x y → is-prop (R x y))
  → (∀ x y → R x y → x ≡ y)
  → is-set A
set-identity-system→hlevel R r p i = identity-system→hlevel 1 (set-identity-system {R = R} {r = r} p λ {x} {y} → i x y) p
```
-->

If $A$ is a type with ¬¬-stable equality, then by the theorem above, the
pointwise double negation of its identity types is an identity system:
and so, if a type has decidable (thus ¬¬-stable) equality, it is a set.
This is known as **Hedberg's theorem**.

```agda
¬¬-stable-identity-system
  : ∀ {ℓ} {A : Type ℓ}
  → (∀ {x y} → ¬ ¬ Path A x y → x ≡ y)
  → is-identity-system (λ x y → ¬ ¬ Path A x y) λ a k → k refl
¬¬-stable-identity-system = set-identity-system λ x y f g →
  funext λ h → absurd (g h)

opaque
  Discrete→is-set : ∀ {ℓ} {A : Type ℓ} → Discrete A → is-set A
  Discrete→is-set {A = A} dec =
    let instance _ = dec in identity-system→hlevel 1
    (¬¬-stable-identity-system dec→dne)
    λ x y f g → funext λ h → absurd (g h)
```

<!--
```agda
×-identity-system
  : ∀ {ℓa ℓb ℓr ℓs} {A : Type ℓa} {B : Type ℓb}
  → {R : A → A → Type ℓr} {S : B → B → Type ℓs}
  → {r : ∀ a → R a a} {s : ∀ b → S b b}
  → is-identity-system R r
  → is-identity-system S s
  → is-identity-system
      (λ ab ab' → R (ab .fst) (ab' .fst) × S (ab .snd) (ab' .snd))
      (λ ab → r (ab .fst) , s (snd ab))
×-identity-system R-ids S-ids .to-path (r' , s') = R-ids .to-path r' ,ₚ S-ids .to-path s'
×-identity-system R-ids S-ids .to-path-over (r' , s') = R-ids .to-path-over r' ,ₚ S-ids .to-path-over s'
```
-->
