{-# OPTIONS -vtc.def.fun:10 #-}
module Cat.Displayed.Solver where

open import Data.List

open import 1Lab.Reflection
open import 1Lab.Reflection.Solver
open import 1Lab.Prelude hiding (id; _∘_)

open import Cat.Base
open import Cat.Displayed.Base
import Cat.Solver

import Cat.Displayed.Reasoning as Dr

module NbE {o′ ℓ′ o′′ ℓ′′}
           {B : Precategory o′ ℓ′}
           (E : Displayed B o′′ ℓ′′)
           where

  open Displayed E
  module B = Precategory B
  open Dr E
  open Cat.Solver.NbE

  private variable
    a b c d e : B.Ob
    f g h i j : B.Hom a b
    a′ b′ c′ d′ e′ : Ob[ a ]
    f′ g′ h′ i′ j′ : Hom[ f ] a′ b′

  data Expr[_] : ∀ {a b} (f : Expr B a b) (a′ : Ob[ a ]) (b′ : Ob[ b ]) → Type (o′ ⊔ ℓ′ ⊔ o′′ ⊔ ℓ′′) where
    `id  : {a′ : Ob[ a ]} → Expr[ `id ] a′ a′
    _`∘_ : ∀ {a′ b′ c′} {f : Expr B b c} {g : Expr B a b}
           → Expr[ f ] b′ c′ → Expr[ g ] a′ b′ → Expr[ f `∘ g ] a′ c′
    _↑ : ∀ {a′ b′} {f : Expr B a b} → Hom[ embed B f ] a′ b′ → Expr[ f ] a′ b′
    `hom[_]_ : ∀ {a b} {a′ b′} {f g : Expr B a b} → embed B f ≡ embed B g → Expr[ f ] a′ b′ → Expr[ g ] a′ b′

  unexpr[_] : (d : Expr B a b) → Expr[ d ] a′ b′ → Hom[ embed B d ] a′ b′
  unexpr[ d ] (`hom[ p ] e)   = hom[ p ] (unexpr[ _ ] e)
  unexpr[ `id ] `id           = id′
  unexpr[ d `∘ d₁ ] (e `∘ e₁) = unexpr[ d ] e ∘′ unexpr[ d₁ ] e₁
  unexpr[ _ ] (hom ↑)         = hom

  data Stack[_] : ∀ {a b} → B.Hom a b → Ob[ a ] → Ob[ b ] → Type (o′ ⊔ ℓ′ ⊔ o′′ ⊔ ℓ′′) where
    [] : ∀ {a} {a′ : Ob[ a ]} → Stack[ B.id ] a′ a′
    _∷_ : ∀ {a b c a′ b′ c′} {f : B.Hom b c} {g : B.Hom a b} → Hom[ f ] b′ c′ → Stack[ g ] a′ b′ → Stack[ f B.∘ g ] a′ c′

  record Value[_] {a b} (f : B.Hom a b) (a′ : Ob[ a ]) (b′ : Ob[ b ]) : Type (o′ ⊔ ℓ′ ⊔ o′′ ⊔ ℓ′′) where
    constructor vsubst
    field
      {mor} : B.Hom a b
      vpath : mor ≡ f
      homs  : Stack[ mor ] a′ b′

  open Value[_]

  value-path : ∀ {v₁ v₂ : Value[ f ] a′ b′} → (p : mor v₁ ≡ mor v₂) → PathP (λ i → Stack[ p i ] a′ b′) (homs v₁) (homs v₂) → v₁ ≡ v₂
  value-path p q i .mor = p i
  value-path {f = f} {v₁ = v₁} {v₂ = v₂}  p q i .vpath =
    is-prop→pathp (λ i → B.Hom-set _ _ (p i) f) (vpath v₁) (vpath v₂) i
  value-path p q i .homs = q i

  vid : Value[ B.id ] a′ a′
  vid = vsubst refl []

  vcomp′ : Hom[ f ] b′ c′ → Value[ g ] a′ b′ → Value[ f B.∘ g ] a′ c′
  vcomp′ {f = f} f′ (vsubst p homs) = vsubst (ap (f B.∘_) p) (f′ ∷ homs)

  vhom[_] : f ≡ g → Value[ f ] a′ b′ → Value[ g ] a′ b′
  vhom[_] p (vsubst q homs) = vsubst (q ∙ p) homs

  abstract
    adjust-k : ∀ {a b c} {f g : Expr B b c} {k : B.Hom a b} → embed B f ≡ embed B g → eval B f k ≡ eval B g k
    adjust-k {f = f'} {g = g'} {f} p =
      sym (ap (B._∘ _) (sym (eval-sound B f')) ∙ eval-sound-k B f' f)
      ∙ ap (B._∘ _) p
      ∙ ap (B._∘ _) (sym (eval-sound B g')) ∙ eval-sound-k B g' f

  eval′ : ∀ {e : Expr B b c} → Expr[ e ] b′ c′ → Value[ f ] a′ b′ → Value[ eval B e f ] a′ c′
  eval′ `id v′                    = v′
  eval′ (e₁′ `∘ e₂′) v′           = eval′ e₁′ (eval′ e₂′ v′)
  eval′ {e = e} (_↑ {f = f} f′) v′ =
    vhom[ ap (B._∘ _) (sym (eval-sound B e)) ∙ eval-sound-k B f _ ] (vcomp′ f′ v′)
  eval′ {f = f} (`hom[_]_ {f = f'} {g = g'} p e′) v′ =
    vhom[ adjust-k {f = f'} {g = g'} p ] (eval′ e′ v′)

  stack→map : Stack[ f ] a′ b′ → Hom[ f ] a′ b′
  stack→map [] = id′
  stack→map (x ∷ x₁) = x ∘′ stack→map x₁

  ⟦_⟧ : Value[ f ] a′ b′ → Hom[ f ] a′ b′
  ⟦ vsubst path homs ⟧ = hom[ path ] (stack→map homs)

  vid-sound : ⟦ vid {a′ = a′} ⟧ ≡ id′
  vid-sound = transport-refl _

  vcomp′-sound
    : (f′ : Hom[ f ] b′ c′) (v : Value[ g ] a′ b′)
    → ⟦ vcomp′ f′ v ⟧ ≡ f′ ∘′ ⟦ v ⟧
  vcomp′-sound f′ v = sym (whisker-r _)

  vhom-sound
    : (p : f ≡ g) (v : Value[ f ] a′ b′)
    → ⟦ vhom[ p ] v ⟧ ≡ hom[ p ] ⟦ v ⟧
  vhom-sound p v = sym (hom[]-∙ _ _)

  abstract
    eval′-sound-k
      : {e : Expr B a b} (e′ : Expr[ e ] b′ c′) (v : Value[ f ] a′ b′)
      → PathP (λ i → Hom[ eval-sound-k B e f i ] a′ c′)
        ⟦ vcomp′ ⟦ eval′ e′ vid ⟧ v ⟧ ⟦ eval′ e′ v ⟧
    eval′-sound-k `id v = to-pathp $
      hom[] ⟦ vcomp′ ⟦ eval′ `id vid ⟧ v ⟧ ≡⟨ hom[]⟩⟨ vcomp′-sound _ v ⟩
      hom[] (hom[] id′ ∘′ ⟦ v ⟧)           ≡⟨ hom[]⟩⟨ ap₂ _∘′_ (transport-refl _) refl ⟩
      hom[] (id′ ∘′ ⟦ v ⟧)                 ≡⟨ from-pathp (idl′ _) ⟩
      ⟦ v ⟧                                ∎

    eval′-sound-k {f = f} {e = d `∘ d₁} (e′ `∘ f′) v = to-pathp $
      hom[ eval-sound-k B (d `∘ d₁) _ ] ⟦ vcomp′ ⟦ eval′ e′ (eval′ f′ vid) ⟧ v ⟧         ≡⟨ hom[]⟩⟨ vcomp′-sound _ v ⟩
      hom[ eval-sound-k B (d `∘ d₁) _ ] (⟦ eval′ e′ (eval′ f′ vid) ⟧ ∘′ ⟦ v ⟧)           ≡˘⟨ smashl _ _ ⟩
      hom[] (hom[ sym (eval-sound-k B d _) ] ⟦ eval′ e′ (eval′ f′ vid) ⟧ ∘′ ⟦ v ⟧)       ≡⟨ hom[]⟩⟨ symP (eval′-sound-k e′ (eval′ f′ vid)) ⟩∘′⟨refl ⟩
      hom[] (⟦ vcomp′ ⟦ eval′ e′ vid ⟧ (eval′ f′ vid) ⟧ ∘′ ⟦ v ⟧)                        ≡⟨ hom[]⟩⟨ ap₂ _∘′_ (vcomp′-sound _ (eval′ f′ vid)) refl ⟩
      hom[] ((⟦ eval′ e′ vid ⟧ ∘′ ⟦ eval′ f′ vid ⟧) ∘′ ⟦ v ⟧)                            ≡⟨ kill₁ _ (_ ≡⟨ _ ⟩ _ ≡⟨ _ ⟩ _ ∎) (symP (assoc′ _ _ _)) ⟩
      hom[] (⟦ eval′ e′ vid ⟧ ∘′ ⟦ eval′ f′ vid ⟧ ∘′ ⟦ v ⟧)                              ≡˘⟨ smashr (eval-sound-k B d₁ _) ((_ ≡⟨ eval-sound-k B d (eval B d₁ _) ⟩ _ ∎)) ⟩
      hom[] (⟦ eval′ e′ vid ⟧ ∘′ hom[] (⟦ eval′ f′ vid ⟧ ∘′ ⟦ v ⟧))                      ≡⟨ hom[]⟩⟨ ap₂ _∘′_ refl (hom[]⟩⟨ sym (vcomp′-sound ⟦ eval′ f′ vid ⟧ v)) ⟩
      hom[] (⟦ eval′ e′ vid ⟧ ∘′ hom[] ⟦ vcomp′ ⟦ eval′ f′ vid ⟧ v ⟧)                    ≡⟨ hom[]⟩⟨ refl⟩∘′⟨ eval′-sound-k f′ v ⟩
      hom[] (⟦ eval′ e′ vid ⟧ ∘′ ⟦ eval′ f′ v ⟧)                                         ≡⟨ hom[]⟩⟨ sym (vcomp′-sound ⟦ eval′ e′ vid ⟧ (eval′ f′ v)) ⟩
      hom[] ⟦ vcomp′ ⟦ eval′ e′ vid ⟧ (eval′ f′ v) ⟧                                     ≡⟨ reindex _ _ ∙ from-pathp (eval′-sound-k e′ (eval′ f′ v)) ⟩
      ⟦ eval′ (e′ `∘ f′) v ⟧                                                             ∎

    eval′-sound-k {e = e} (_↑ {f = f} x) v = to-pathp $
      hom[] ⟦ vcomp′ ⟦ eval′ (_↑ {f = f} x) vid ⟧ v ⟧                                  ≡⟨ hom[]⟩⟨ vcomp′-sound ⟦ eval′ (_↑ {f = f} x) vid ⟧ v ⟩
      hom[] (⟦ vhom[ _ ] (vcomp′ x vid) ⟧ ∘′ ⟦ v ⟧)                                    ≡⟨ hom[]⟩⟨ ap₂ _∘′_ (vhom-sound _ (vcomp′ x vid)) refl ⟩
      hom[] (hom[] ⟦ vcomp′ x vid ⟧ ∘′ ⟦ v ⟧)                                          ≡⟨ hom[]⟩⟨ ap₂ _∘′_ (ap hom[] (vcomp′-sound x vid)) refl ⟩
      hom[] (hom[] (x ∘′ ⟦ vid ⟧ ) ∘′ ⟦ v ⟧)                                           ≡⟨ hom[]⟩⟨ ap₂ _∘′_ (ap hom[] (ap (x ∘′_) vid-sound)) refl ⟩
      hom[] (hom[] (x ∘′ id′) ∘′ ⟦ v ⟧)                                                ≡⟨ ap hom[] (whisker-l _) ·· hom[]-∙ _ _ ·· reindex _ (ap (B._∘ _) (B.idr _) ∙ ap (B._∘ _) (sym (eval-sound B e)) ∙ eval-sound-k B e _) ·· sym (hom[]-∙ _ _) ·· ap hom[] (sym (whisker-l _) ∙ ap₂ _∘′_ (from-pathp (idr′ x)) refl) ⟩
      hom[] (x ∘′ ⟦ v ⟧)                                                               ≡⟨ ap hom[] (sym (vcomp′-sound x v)) ∙ sym (vhom-sound _ (vcomp′ x v)) ⟩
      ⟦ vhom[ ap (B._∘ _) (sym (eval-sound B e)) ∙ eval-sound-k B f _ ] (vcomp′ x v) ⟧ ∎

    eval′-sound-k {f = f} {e = e} (`hom[_]_ {f = e'} x e′) v = to-pathp $
      hom[ eval-sound-k B e f ] ⟦ vcomp′ ⟦ vhom[ _ ] (eval′ e′ vid) ⟧ v ⟧  ≡⟨ hom[]⟩⟨ ap ⟦_⟧ (ap (λ e → vcomp′ e v) (vhom-sound (adjust-k {f = e'} {e} {k = B.id} x) (eval′ e′ vid))) ⟩
      hom[ eval-sound-k B e f ] ⟦ vcomp′ (hom[] ⟦ eval′ e′ vid ⟧) v ⟧      ≡⟨ hom[]⟩⟨ vcomp′-sound (hom[] ⟦ eval′ e′ vid ⟧) v ⟩
      hom[ eval-sound-k B e f ] (hom[] ⟦ eval′ e′ vid ⟧ ∘′ ⟦ v ⟧)          ≡⟨ smashl (adjust-k {f = e'} {g = e} {k = B.id} x) _ ⟩
      hom[] (⟦ eval′ e′ vid ⟧ ∘′ ⟦ v ⟧)                                    ≡⟨ hom[]⟩⟨ sym (vcomp′-sound ⟦ eval′ e′ vid ⟧ v) ⟩
      hom[] ⟦ vcomp′ ⟦ eval′ e′ vid ⟧ v ⟧                                  ≡˘⟨ reindex _ _ ⟩
      hom[] ⟦ vcomp′ ⟦ eval′ e′ vid ⟧ v ⟧                                  ≡˘⟨ hom[]-∙ _ (adjust-k {f = e'} {e} {k = f} x) ⟩
      hom[] (hom[ eval-sound-k B e' f ] ⟦ vcomp′ ⟦ eval′ e′ vid ⟧ v ⟧)     ≡⟨ hom[]⟩⟨ from-pathp (eval′-sound-k e′ v) ⟩
      hom[] ⟦ eval′ e′ v ⟧                                                 ≡˘⟨ vhom-sound (adjust-k {f = e'} {e} {k = f} x) (eval′ e′ v) ⟩
      ⟦ vhom[ _ ] (eval′ e′ v) ⟧                                           ∎

    eval′-sound
      : (e : Expr B a b) (e′ : Expr[ e ] a′ b′)
      → PathP (λ i → Hom[ eval-sound B e i ] a′ b′) ⟦ eval′ e′ vid ⟧ (unexpr[ e ] e′)
    eval′-sound .`id `id = vid-sound

    eval′-sound (fe `∘ ge) (f `∘ g) = to-pathp $
      hom[] ⟦ eval′ (f `∘ g) vid ⟧                      ≡⟨ reindex _ (sym (eval-sound-k B fe (eval B ge B.id)) ∙ ap₂ B._∘_ (eval-sound B fe) (eval-sound B ge)) ⟩
      hom[ _ ∙ _ ] ⟦ eval′ (f `∘ g) vid ⟧               ≡˘⟨ hom[]-∙ _ _ ⟩
      hom[ _ ] (hom[ _ ] ⟦ eval′ f (eval′ g vid) ⟧)     ≡⟨ hom[]⟩⟨ from-pathp (symP (eval′-sound-k f (eval′ g vid))) ⟩
      hom[ _ ] ⟦ vcomp′ ⟦ eval′ f vid ⟧ (eval′ g vid) ⟧ ≡⟨ hom[]⟩⟨ vcomp′-sound _ (eval′ g vid) ⟩
      hom[ _ ] (⟦ eval′ f vid ⟧ ∘′ ⟦ eval′ g vid ⟧)     ≡⟨ split⟩⟨ eval′-sound _ f ⟩∘′⟨ eval′-sound _ g ⟩
      unexpr[ _ ] f ∘′ unexpr[ _ ] g                    ∎

    eval′-sound e (x ↑)     = to-pathp $
         ap hom[] (vhom-sound _ (vcomp′ x vid))
      ·· hom[]-∙ _ _
      ·· ap hom[] (vcomp′-sound x vid ∙ ap₂ _∘′_ refl vid-sound)
      ·· reindex _ _
      ·· from-pathp (idr′ x)

    eval′-sound e (`hom[_]_ {f = f} {g = g} x e′) = to-pathp $
      hom[] ⟦ vhom[ adjust-k {f = f} {g} x ] (eval′ e′ vid) ⟧ ≡⟨ hom[]⟩⟨ vhom-sound _ (eval′ e′ vid) ⟩
      hom[] (hom[] ⟦ eval′ e′ vid ⟧)                          ≡⟨ hom[]-∙ (adjust-k {f = f} {g} x) (eval-sound B e) ⟩
      hom[] ⟦ eval′ e′ vid ⟧                                  ≡⟨ reindex ((adjust-k {f = f} {g} x ∙ eval-sound B e)) (eval-sound B f ∙ x) ∙ sym (hom[]-∙ _ _) ⟩
      hom[] (hom[] ⟦ eval′ e′ vid ⟧)                          ≡⟨ hom[]⟩⟨ from-pathp (eval′-sound f e′) ⟩
      hom[] (unexpr[ f ] e′)                                  ∎

  nf′ : ∀ {f : Expr B a b} → Expr[ f ] a′ b′ → Hom[ nf B f ] a′ b′
  nf′ f = ⟦ eval′ f vid ⟧

  abstract
    solve′ : ∀ {f g : Expr B a b} (f′ : Expr[ f ] a′ b′) (g′ : Expr[ g ] a′ b′)
               {q : embed B f ≡ embed B g}
              → (p : nf B f ≡ nf B g)
              → nf′ f′ ≡[ p ] nf′ g′
              → unexpr[ f ] f′ ≡[ q ] unexpr[ g ] g′
    solve′ {f = f} {g = g} f′ g′ {q = q} p p′ = to-pathp $
      hom[] (unexpr[ f ] f′) ≡⟨ revive₁ (symP (eval′-sound f f′)) ⟩
      hom[] (nf′ f′)         ≡⟨ revive₁ p′ ⟩
      hom[] (nf′ g′)         ≡⟨ cancel _ _ (eval′-sound g g′) ⟩
      unexpr[ g ] g′ ∎


module Reflection where
  module Cat = Cat.Solver.Reflection

  pattern displayed-field-args xs =
    _ h0∷ _ h0∷ -- Base Levels
    _ h0∷       -- Base Category
    _ h0∷ _ h0∷ -- Displayed Levels
    _ v∷ xs     -- Displayed Category

  pattern displayed-fn-args xs =
    _ h∷ _ h∷ _ h∷ _ h∷ _ h∷ _ v∷ xs

  pattern ob[]_ xs =
    _ h∷ _ h∷ xs

  pattern “Hom[_]” f x y =
    def (quote Displayed.Hom[_]) (displayed-field-args (ob[] (f v∷ x v∷ y v∷ [])))

  pattern “id” =
    def (quote Displayed.id′) (displayed-field-args (ob[] []))

  pattern “∘” f g f′ g′ =
    def (quote Displayed._∘′_) (displayed-field-args (ob[] ob[] ob[] (f h∷ g h∷ f′ v∷ g′ v∷ [])))

  -- This p has type 'f ≡ g', but we need 'embed (build-expr f) ≡ embed (build-expr g)'
  pattern “hom[]” f g p f′  =
    def (quote Dr.hom[_]) (displayed-fn-args (ob[] ob[] (f h∷ g h∷ p v∷ f′ v∷ [])))

  mk-displayed-fn : Term → List (Arg Term) → List (Arg Term)
  mk-displayed-fn disp args = unknown h∷ unknown h∷ unknown h∷ unknown h∷ unknown h∷ disp v∷ args

  invoke-solver : Term → Term → Term → Term
  invoke-solver disp lhs rhs =
    def (quote NbE.solve′) (mk-displayed-fn disp (infer-hidden 6 $ lhs v∷ rhs v∷ “refl” v∷ “reindex” v∷ []))
    where “reindex” = def (quote Dr.reindex) (disp v∷ unknown v∷ unknown v∷ [])

  invoke-normaliser : Term → Term → Term
  invoke-normaliser disp tm = def (quote NbE.nf′) (mk-displayed-fn disp (infer-hidden 5 $ tm v∷ []))

  build-expr : Term → TC Term
  build-expr “id” = returnTC $ con (quote NbE.`id) []
  build-expr (“∘” f g f′ g′) = do
    let f = Cat.build-expr f
    let g = Cat.build-expr g
    f′ ← build-expr f′
    g′ ← build-expr g′
    returnTC $ con (quote NbE._`∘_) (infer-hidden 12 $ f h∷ g h∷ f′ v∷ g′ v∷ [])
  build-expr (“hom[]” f g p f′) = do
    let f = Cat.build-expr f
    let g = Cat.build-expr g
    f′ ← build-expr f′
    returnTC $ con (quote NbE.`hom[_]_) (infer-hidden 10 $ f h∷ g h∷ p v∷ f′ v∷ [])
  build-expr f′ = do
    “Hom[ f ]” x y ← inferType f′ >>= reduce
      where tp → typeError $ strErr "Expected a displayed morphism: " ∷ termErr tp ∷ []
    returnTC $ con (quote NbE._↑) (infer-hidden 8 $ x h∷ y h∷ Cat.build-expr f h∷ f′ v∷ [])

  dont-reduce : List Name
  dont-reduce =
    quote Precategory.id ∷ quote Precategory._∘_ ∷
    quote Displayed.id′ ∷ quote Displayed._∘′_ ∷ quote Dr.hom[_] ∷ []

  displayed-solver : Term → SimpleSolver
  displayed-solver disp .SimpleSolver.dont-reduce = dont-reduce
  displayed-solver disp .SimpleSolver.build-expr tm = build-expr tm
  displayed-solver disp .SimpleSolver.invoke-solver = invoke-solver disp
  displayed-solver disp .SimpleSolver.invoke-normaliser = invoke-normaliser disp

  repr-macro : Term → Term → Term → TC ⊤
  repr-macro disp f _ =
    mk-simple-repr (displayed-solver disp) f

  simplify-macro : Term → Term → Term → TC ⊤
  simplify-macro disp f hole =
    mk-simple-normalise (displayed-solver disp) f hole

  solve-macro : Term → Term → TC ⊤
  solve-macro disp hole =
    mk-simple-solver (displayed-solver disp) hole

macro
  repr-disp! : Term → Term → Term → TC ⊤
  repr-disp! = Reflection.repr-macro

  simpl-disp! : Term → Term → Term → TC ⊤
  simpl-disp! = Reflection.simplify-macro

  disp! : Term → Term → TC ⊤
  disp! = Reflection.solve-macro

private module Test {o ℓ o′ ℓ′} {B : Precategory o ℓ} (E : Displayed B o′ ℓ′) where
  open Precategory B
  open Displayed E
  open Dr E

  private variable
    x y z : Ob
    x′ y′ z′ : Ob[ x ]
    f g h : Hom x y
    f′ g′ h′ : Hom[ f ] x′ y′


  test : ∀ (f′ : Hom[ f ] y′ z′) → (g′ : Hom[ g ] x′ y′) → (p : (f ∘ id) ∘ g ≡ f ∘ g) → f′ ≡ hom[ idl f ] (id′ ∘′ f′)
  test {f = f} f′ g′ p = disp! E
