<!--
```agda
{-# OPTIONS -vtc.def.fun:10 #-}
open import Cat.Functor.FullSubcategory
open import Cat.Functor.Properties
open import Cat.Instances.Functor
open import Cat.Instances.Sets
open import Cat.Functor.Hom
open import Cat.Prelude

open import Data.Image

import Cat.Functor.Reasoning.FullyFaithful as Ffr
import Cat.Reasoning as Cr
```
-->

```agda
module Cat.Univalent.Rezk where
```

<!--
```agda
private variable
  o h o' h' : Level
open Precategory
open Functor
```
-->

# The Rezk completion {defines="rezk-completion"}

In the same way that we can [freely] complete a proset into a poset, it
is possible to, in a universal way, replace any precategory $\cA$ by a
category $\widehat{\cA}$, such that there is a weak equivalence (a
[[fully faithful]], [[essentially surjective]] functor) $\cA \to
\widehat{\cA}$, such that any map from $\cA$ to a [[univalent category]]
$\cC$ factors uniquely through $\widehat{\cA}$.

[freely]: Cat.Functor.Adjoint.html
[fully faithful]: Cat.Functor.Properties.html#ff-functors
[essentially surjective]: Cat.Functor.Properties.html#essential-fibres
[univalent category]: Cat.Univalent.html

The construction is essentially piecing together a handful of
pre-existing results: The univalence principle for $n$-types implies
that [Sets is a univalent category][setu], and [functor categories with
univalent codomain are univalent][funcu]; The [Yoneda lemma] implies
that any precategory $\cA$ admits a [full inclusion] into
$[\cA\op, \Sets]$, and [full subcategories of univalent categories
are univalent][fullu] --- so, like Grothendieck cracking the nut, the
sea of theory has risen to the point where our result is trivial:

[setu]: Cat.Instances.Sets.html
[funcu]: Cat.Functor.Univalence.html
[Yoneda lemma]: Cat.Functor.Hom.html#the-yoneda-embedding
[full inclusion]: Cat.Functor.FullSubcategory.html#from-full-inclusions
[fullu]: Cat.Functor.FullSubcategory.html#Restrict-is-category

```agda
module Rezk-large (A : Precategory o h) where
  Rezk-completion : Precategory (o ⊔ lsuc h) (o ⊔ h)
  Rezk-completion = Full-inclusion→Full-subcat {F = よ A} (よ-is-fully-faithful A)

  Rezk-completion-is-category : is-category Rezk-completion
  Rezk-completion-is-category =
    Restrict-is-category _ (λ _ → squash)
      (Functor-is-category Sets-is-category)

  Complete : Functor A Rezk-completion
  Complete = Ff-domain→Full-subcat {F = よ A} (よ-is-fully-faithful A)

  Complete-is-ff : is-fully-faithful Complete
  Complete-is-ff = is-fully-faithful-domain→Full-subcat
      {F = よ _} (よ-is-fully-faithful _)

  Complete-is-eso : is-eso Complete
  Complete-is-eso = is-eso-domain→Full-subcat {F = よ _} (よ-is-fully-faithful _)
```

However, this construction is a bit disappointing, because we've had to
pass to a _larger_ universe than the one we started with. If originally
we had $\cA$ with objects living in a universe $o$ and homs in $h$,
we now have $\widehat{\cA}$ with objects living in $o \sqcup (1 + h)$.

It's unavoidable that the objects in $\widehat{\cA}$ will live in an
universe $\widehat{o}$ satisfying $(o \sqcup h) \le \widehat{o}$, since
we want their identity type to be equivalent to something living in $h$,
but going up a level is unfortunate. However, it's also avoidable!

Since $\psh(\cA)$ is a category, isomorphism is an [[identity system]]
on its objects, which lives at the level of its morphisms --- $o \sqcup h$
--- rather than of its objects, $o \sqcup (1 + h)$. Therefore, using the
construction of [small images], we may take $\im \yo_{\cA}$ to be a
$o \sqcup h$-type!

[small images]: Data.Image.html

```agda
module _ (A : Precategory o h) where
  private
    PSh[A] = PSh h A
    module PSh[A] = Precategory PSh[A]

    PSh[A]-is-cat : is-category PSh[A]
    PSh[A]-is-cat = Functor-is-category Sets-is-category

    module よim = Replacement PSh[A]-is-cat (よ₀ A)

  Rezk-completion : Precategory (o ⊔ h) (o ⊔ h)
  Rezk-completion .Ob          = よim.Image
  Rezk-completion .Hom x y     = よim.embed x => よim.embed y
  Rezk-completion .Hom-set _ _ = PSh[A].Hom-set _ _
  Rezk-completion .id    = PSh[A].id
  Rezk-completion ._∘_   = PSh[A]._∘_
  Rezk-completion .idr   = PSh[A].idr
  Rezk-completion .idl   = PSh[A].idl
  Rezk-completion .assoc = PSh[A].assoc
```

Our resized Rezk completion $\widehat{\cA}$ factors the Yoneda
embedding $\yo_\cA$ as a functor

$$
\cA \xto{\sim} \widehat{\cA} \mono \psh(\cA)
$$

where the first functor is a weak equivalence, and the second functor is
fully faithful. Let's first define the functors:

```agda
  complete : Functor A Rezk-completion
  complete .F₀   = よim.inc
  complete .F₁   = よ A .F₁
  complete .F-id = よ A .F-id
  complete .F-∘  = よ A .F-∘

  Rezk↪PSh : Functor Rezk-completion (PSh h A)
  Rezk↪PSh .F₀      = よim.embed
  Rezk↪PSh .F₁ f    = f
  Rezk↪PSh .F-id    = refl
  Rezk↪PSh .F-∘ _ _ = refl
```

From the existence of the second functor, we can piece together
pre-existing lemmas about the image and about identity systems in
general to show that this resized Rezk completion is also a category: We
can pull back the identity system on $\psh(\cA)$ to one on
$\widehat{\cA}$, since we know of a (type-theoretic) embedding
between their types of objects.

That gives us an identity system which is slightly off, that of
"$\psh(\cA)$-isomorphisms on the image of the functor
$\widehat{\cA} \mono \psh(\cA)$", but since we know that this
functor is fully faithful, that's equivalent to what we want.

```agda
  private module Rezk↪PSh = Ffr Rezk↪PSh id-equiv
  open Cr Rezk-completion using (Extensional-≅)

  abstract
    Rezk-completion-is-category : is-category Rezk-completion
    Rezk-completion-is-category =
      transfer-identity-system
        (pullback-identity-system
          (Functor-is-category Sets-is-category)
          (よim.embed , よim.embed-is-embedding))
        (λ x y → Rezk↪PSh.iso-equiv e⁻¹)
        λ x → trivial!
```

It remains to show that the functor $\cA \to \widehat{\cA}$ is a
weak equivalence. It's fully faithful because the Yoneda embedding is,
and it's essentially surjective because it's _literally_
surjective-on-objects.

```agda
  complete-is-ff : is-fully-faithful complete
  complete-is-ff = よ-is-fully-faithful A

  complete-is-eso : is-eso complete
  complete-is-eso x = do
    t ← よim.inc-is-surjective x
    pure (t .fst , path→iso (t .snd))
```
