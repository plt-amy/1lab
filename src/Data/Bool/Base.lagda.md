<!--
```agda
open import 1Lab.Path.IdentitySystem
open import 1Lab.HLevel.Closure
open import 1Lab.Path
open import 1Lab.Type

open import Data.Dec.Base
```
-->

```agda
module Data.Bool.Base where
```

<!--
```agda
open import Prim.Data.Bool public
```
-->

```agda
true≠false : ¬ true ≡ false
true≠false p = subst P p tt where
  P : Bool → Type
  P false = ⊥
  P true = ⊤
```

<!--
```agda
false≠true : ¬ false ≡ true
false≠true = true≠false ∘ sym
```
-->

```agda
not : Bool → Bool
not true = false
not false = true

and or : Bool → Bool → Bool
and false y = false
and true y = y

or false y = y
or true y = true
```

```agda
instance
  Discrete-Bool : Discrete Bool
  Discrete-Bool {false} {false} = yes refl
  Discrete-Bool {false} {true}  = no false≠true
  Discrete-Bool {true}  {false} = no true≠false
  Discrete-Bool {true}  {true}  = yes refl
```

<!--
```agda
instance
  H-Level-Bool : ∀ {n} → H-Level Bool (2 + n)
  H-Level-Bool = basic-instance 2 (Discrete→is-set auto)
```
-->

```agda
x≠true→x≡false : (x : Bool) → x ≠ true → x ≡ false
x≠true→x≡false false p = refl
x≠true→x≡false true p = absurd (p refl)

x≠false→x≡true : (x : Bool) → x ≠ false → x ≡ true
x≠false→x≡true false p = absurd (p refl)
x≠false→x≡true true p = refl
```

```agda
is-true : Bool → Type
is-true true  = ⊤
is-true false = ⊥

record So (b : Bool) : Type where
  field
    is-so : is-true b

pattern oh = record { is-so = tt }
```

<!--
```agda
¬so-false : So false → ⊥
¬so-false ()

oh? : ∀ x → Dec (So x)
oh? true = yes oh
oh? false = no λ ()

not-so : ∀ {x} → ¬ So x → So (not x)
not-so {true} ¬p = absurd (¬p oh)
not-so {false} p = oh

instance
  H-Level-So : ∀ {x n} → H-Level (So x) (suc n)
  H-Level-So {false} = prop-instance λ ()
  H-Level-So {true} = prop-instance λ where
    oh oh → refl

  Dec-So : ∀ {x} → Dec (So x)
  Dec-So = oh? _
```
-->

<!--
```agda
if : ∀ {ℓ} {A : Type ℓ} → A → A → Bool → A
if x y false = y
if x y true = x

infix 0 if_then_else_

if_then_else_ : ∀ {ℓ} {A : Type ℓ} → Bool → A → A → A
if false then t else f = f
if true then t else f = t

Bool-elim : ∀ {ℓ} (A : Bool → Type ℓ) → A true → A false → ∀ x → A x
Bool-elim A at af true = at
Bool-elim A at af false = af
```
-->
