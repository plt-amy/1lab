```agda
open import 1Lab.Path

open import Cat.Base

import Cat.Reasoning

module Cat.Functor.Reasoning
  {o â oâ² ââ²}
  {ð : Precategory o â} {ð : Precategory oâ² ââ²}
  (F : Functor ð ð) where

module ð = Cat.Reasoning ð
module ð = Cat.Reasoning ð
open Functor F public
```

<!--
```agda
private variable
  A B C : ð.Ob
  a b c d : ð.Hom A B
  X Y Z : ð.Ob
  f g h i : ð.Hom X Y
```
-->


# Reasoning Combinators for Functors

The combinators exposed in [category reasoning] abstract out a lot of common
algebraic manipulations, and make proofs much more concise. However, once functors
get involved, those combinators start to get unwieldy! Therefore, we have
to write some new combinators for working with functors specifically.
This module is meant to be imported qualified.

[category reasoning]: Cat.Reasoning.html

## Identity Morphisms

```agda
module _ (aâ¡id : a â¡ ð.id) where
  elim : Fâ a â¡ ð.id
  elim = ap Fâ aâ¡id â F-id

  eliml : Fâ a ð.â f â¡ f 
  eliml = ð.eliml elim

  elimr : f ð.â Fâ a â¡ f
  elimr = ð.elimr elim

  introl : f â¡ Fâ a ð.â f
  introl = ð.introl elim

  intror : f â¡ f ð.â Fâ a
  intror = ð.intror elim
```

## Reassociations

```agda
module _ (abâ¡c : a ð.â b â¡ c) where
  collapse : Fâ a ð.â Fâ b â¡ Fâ c
  collapse = sym (F-â a b) â ap Fâ abâ¡c

  pulll : Fâ a ð.â (Fâ b ð.â f) â¡ Fâ c ð.â f
  pulll = ð.pulll collapse

  pullr : (f ð.â Fâ a) ð.â Fâ b â¡ f ð.â Fâ c
  pullr = ð.pullr collapse

module _ (câ¡ab : c â¡ a ð.â b) where
  expand : Fâ c â¡ Fâ a ð.â Fâ b
  expand = sym (collapse (sym câ¡ab))

  pushl : Fâ c ð.â f â¡ Fâ a ð.â (Fâ b ð.â f)
  pushl = ð.pushl expand

  pushr : f ð.â Fâ c â¡ (f ð.â Fâ a) ð.â Fâ b
  pushr = ð.pushr expand

module _ (p : a ð.â c â¡ b ð.â d) where
  weave : Fâ a ð.â Fâ c â¡ Fâ b ð.â Fâ d
  weave = sym (F-â a c) â ap Fâ p â F-â b d

  extendl : Fâ a ð.â (Fâ c ð.â f) â¡ Fâ b ð.â (Fâ d ð.â f)
  extendl = ð.extendl weave

  extendr : (f ð.â Fâ a) ð.â Fâ c â¡ (f ð.â Fâ b) ð.â Fâ d
  extendr = ð.extendr weave

  extend-inner :
    f ð.â Fâ a ð.â Fâ c ð.â g â¡ f ð.â Fâ b ð.â Fâ d ð.â g
  extend-inner = ð.extend-inner weave
```

## Cancellation

```agda
module _ (inv : a ð.â b â¡ ð.id) where
  annihilate : Fâ a ð.â Fâ b â¡ ð.id
  annihilate = sym (F-â a b) â ap Fâ inv â F-id

  cancell : Fâ a ð.â (Fâ b ð.â f) â¡ f
  cancell = ð.cancell annihilate

  cancelr : (f ð.â Fâ a) ð.â Fâ b â¡ f
  cancelr = ð.cancelr annihilate

  insertl : f â¡ Fâ a ð.â (Fâ b ð.â f)
  insertl = ð.insertl annihilate

  insertr : f â¡ (f ð.â Fâ a) ð.â Fâ b
  insertr = ð.insertr annihilate

  cancel-inner : (f ð.â Fâ a) ð.â (Fâ b ð.â g) â¡ f ð.â g
  cancel-inner = ð.cancel-inner annihilate
```

## Notation

Writing `ap Fâ p` is somewhat clunky, so we define a bit of notation
to make it somewhat cleaner.

```agda
â¨_â© : a â¡ b â Fâ a â¡ Fâ b
â¨_â© = ap Fâ
```

