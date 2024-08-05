<!--
```agda
open import 1Lab.Prelude

open import Homotopy.Space.Suspension
```
-->


```agda
module Homotopy.Pushout where
```

# Pushouts {defines="pushout"}

Given the following span:

~~~{.quiver}
\[\begin{tikzcd}
  C && B \\
  \\
  A
  \arrow["g", from=1-1, to=1-3]
  \arrow["f"', from=1-1, to=3-1]
\end{tikzcd}\]
~~~

The **pushout** of this span is defined as the higher inductive type
presented by:
```agda
data Pushout {ℓ} (C : Type ℓ)
                 (A : Type ℓ) (f : C → A)
                 (B : Type ℓ) (g : C → B)
                 : Type ℓ where
  inl : A → Pushout C A f B g
  inr : B → Pushout C A f B g
  commutes : ∀ c → inl (f c) ≡ inr (g c)
```

These combine to give the following:

~~~{.quiver}
\[\begin{tikzcd}
	C && B \\
	\\
	A && {\rm{Pushout}}
	\arrow["g", from=1-1, to=1-3]
	\arrow["f"', from=1-1, to=3-1]
	\arrow["{\rm{inr}}", from=1-3, to=3-3]
	\arrow["{\rm{commutes}}"{description}, shorten <=6pt, shorten >=6pt, Rightarrow, from=3-1, to=1-3]
	\arrow["{\rm{inl}}"', from=3-1, to=3-3]
\end{tikzcd}\]
~~~

## Suspensions as pushouts

The [[suspension]] of a type $A$ can be expressed as the  `Pushout`{.Agda}
of the span $\top \ot A \to \top$:

~~~{.quiver}
\[\begin{tikzcd}
	C && \top \\
	\\
	\top && {\rm{Pushout}}
	\arrow["{\rm{!}}", from=1-1, to=1-3]
	\arrow["{\rm{!}}"', from=1-1, to=3-1]
	\arrow["{\rm{inr}}", from=1-3, to=3-3]
	\arrow["{\rm{commutes}}"{description}, shorten <=6pt, shorten >=6pt, Rightarrow, from=3-1, to=1-3]
	\arrow["{\rm{inl}}"', from=3-1, to=3-3]
\end{tikzcd}\]
~~~

<!--
```agda
const : {A B : Type} → A → B → A
const t _ = t
```
-->

There is only one element of `⊤`{.Agda}, and hence only one choice
for the function projecting into `⊤`{.Agda} - `const tt`{.Agda}.

If one considers the structure we're creating, it becomes very
obvious that this is equivalent to suspension - because both of our
non-path constructors have input `⊤`{.Agda}, they're indistiguishable
from members of the pushout; therefore, we take the
`inl`{.Agda} and `inr`{.Agda} to `N`{.Agda} and
`S`{.Agda} respectively.
Likewise, we take `commutes`{.Agda} to
`merid`{.Agda}.

```agda
Susp≡Pushout-⊤←A→⊤ : ∀ {A} → Susp A ≡ Pushout A ⊤ (const tt) ⊤ (const tt)

Susp→Pushout-⊤←A→⊤ : ∀ {A} → Susp A → Pushout A ⊤ (const tt) ⊤ (const tt)
Susp→Pushout-⊤←A→⊤ N = inl tt
Susp→Pushout-⊤←A→⊤ S = inr tt
Susp→Pushout-⊤←A→⊤ (merid x i) = commutes x i

Pushout-⊤←A→⊤-to-Susp : ∀ {A} → Pushout A ⊤ (const tt) ⊤ (const tt) → Susp A
Pushout-⊤←A→⊤-to-Susp (inl x) = N
Pushout-⊤←A→⊤-to-Susp (inr x) = S
Pushout-⊤←A→⊤-to-Susp (commutes c i) = merid c i
```

So we then have:

```agda
Susp≡Pushout-⊤←A→⊤ = ua (Susp→Pushout-⊤←A→⊤ , is-iso→is-equiv iso-pf) where
```

<details><summary> We then verify that our two functions above are in fact
an equivalence. This is entirely `refl`{.Agda}, due to the noted
similarities in structure.</summary>
```agda
  open is-iso

  iso-pf : is-iso Susp→Pushout-⊤←A→⊤
  iso-pf .inv = Pushout-⊤←A→⊤-to-Susp 
  iso-pf .rinv (inl x) = refl
  iso-pf .rinv (inr x) = refl
  iso-pf .rinv (commutes c i) = refl
  iso-pf .linv N = refl
  iso-pf .linv S = refl
  iso-pf .linv (merid x i) = refl
```
</details>

## The universal property of pushouts

To formulate the universal property of a pushout, we first introduce **cocones**.
A `Cocone`{.Agda}, given a type `D`{.Agda} and a span:

~~~{.quiver}
\[\begin{tikzcd}
	A & C & B
	\arrow["f"', from=1-2, to=1-1]
	\arrow["g", from=1-2, to=1-3]
\end{tikzcd}\]
~~~

consists of functions $i : A \to D$, $j : B \to D$, and a homotopy
$h : (c : C) \to i (f c) \is j (g c)$, forming:

~~~{.quiver}
\[\begin{tikzcd}
	C && B \\
	\\
	A && D
	\arrow["g", from=1-1, to=1-3]
	\arrow["f"', from=1-1, to=3-1]
	\arrow["j", from=1-3, to=3-3]
	\arrow["h"{description}, shorten <=6pt, shorten >=6pt, Rightarrow, from=3-1, to=1-3]
	\arrow["i"', from=3-1, to=3-3]
\end{tikzcd}\]
~~~


One can then note the similarities between this definition,
and our previous `Pushout`{.Agda} definition. We denote the type of
`Cocone`{.Agda}s as:

```agda
Cocone : {C A B : Type} → (f : C → A) → (g : C → B) → (D : Type) → Type
Cocone {C} {A} {B} f g D =
  Σ[ i ∈ (A → D) ]
    Σ[ j ∈ (B → D) ]
      ((c : C) → i (f c) ≡ j (g c))
```

We can then show that the canonical `Cocone`{.Agda} consisting of a `Pushout`{.Agda}
is the universal `Cocone`{.Agda}.

```agda
Pushout-is-universal-cocone : ∀ {A B C E f g} → (Pushout C A f B g → E) ≡ (Cocone f g E)
Pushout-is-universal-cocone = ua ( Pushout→Cocone , is-iso→is-equiv iso-pc ) where
```

<details><summary> Once again we show that the above is an equivalence;
this proof is essentially a transcription of Lemma 6.8.2 in the [HoTT](HoTT.html) book,
and again mostly reduces to `refl`{.Agda}.
</summary>
```agda
  open is-iso

  Pushout→Cocone : ∀ {A B C E f g} → (Pushout C A f B g → E) → Cocone f g E
  Cocone→Pushout : ∀ {A B C E f g} → Cocone f g E → (Pushout C A f B g → E)
  iso-pc : is-iso Pushout→Cocone

  Pushout→Cocone t = (λ x → t (inl x)) ,
                     (λ x → t (inr x)) ,
                     (λ c i → ap t (commutes c) i)

  Cocone→Pushout t (inl x) = fst t x 
  Cocone→Pushout t (inr x) = fst (snd t) x
  Cocone→Pushout t (commutes c i) = snd (snd t) c i

  iso-pc .inv = Cocone→Pushout
  iso-pc .rinv _ = refl
  iso-pc .linv _ = funext (λ { (inl y) → refl;
                                (inr y) → refl;
                                (commutes c i) → refl
                           })
```
</details>
