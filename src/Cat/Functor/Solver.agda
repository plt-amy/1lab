module Cat.Functor.Solver where

open import 1Lab.Prelude

open import Cat.Base
import Cat.Reasoning as Cat

open import 1Lab.Reflection

module NbE {o h o′ h′} {𝒞 : Precategory o h} {𝒟 : Precategory o′ h′} (F : Functor 𝒞 𝒟) where
  private
    module 𝒞 = Cat 𝒞
    module 𝒟 = Cat 𝒟
    open Functor F

    variable
      A B C : 𝒞.Ob
      X Y Z : 𝒟.Ob

  data CExpr : 𝒞.Ob → 𝒞.Ob → Type (o ⊔ h) where
    _‶∘‶_ : CExpr B C → CExpr A B → CExpr A C
    ‶id‶  : CExpr A A
    _↑    : 𝒞.Hom A B → CExpr A B

  data DExpr : 𝒟.Ob → 𝒟.Ob → Type (o ⊔ h ⊔ o′ ⊔ h′) where
    ‶F₁‶  : CExpr A B → DExpr (F₀ A) (F₀ B)
    _‶∘‶_ : DExpr Y Z → DExpr X Y → DExpr X Z
    ‶id‶  : DExpr X X
    _↑    : 𝒟.Hom X Y → DExpr X Y

  uncexpr : CExpr A B → 𝒞.Hom A B
  uncexpr (e1 ‶∘‶ e2) = uncexpr e1 𝒞.∘ uncexpr e2
  uncexpr ‶id‶ = 𝒞.id
  uncexpr (f ↑) = f

  undexpr : DExpr X Y → 𝒟.Hom X Y
  undexpr (‶F₁‶ e) = F₁ (uncexpr e)
  undexpr (e1 ‶∘‶ e2) = undexpr e1 𝒟.∘ undexpr e2
  undexpr ‶id‶ = 𝒟.id
  undexpr (f ↑) = f

  --------------------------------------------------------------------------------
  -- Values

  data CValue : 𝒞.Ob → 𝒞.Ob → Type (o ⊔ h) where
    vid : CValue A A
    vcomp : 𝒞.Hom B C → CValue A B → CValue A C

  data Frame : 𝒟.Ob → 𝒟.Ob → Type (o ⊔ h ⊔ o′ ⊔ h′) where
    vhom : 𝒟.Hom X Y → Frame X Y
    vfmap : 𝒞.Hom A B → Frame (F₀ A) (F₀ B)

  data DValue : 𝒟.Ob → 𝒟.Ob → Type (o ⊔ h ⊔ o′ ⊔ h′) where
    vid   : DValue X X
    vcomp : Frame Y Z → DValue X Y → DValue X Z

  uncvalue : CValue A B → 𝒞.Hom A B
  uncvalue vid = 𝒞.id
  uncvalue (vcomp f v) = f 𝒞.∘ uncvalue v

  unframe : Frame X Y → 𝒟.Hom X Y
  unframe (vhom f) = f
  unframe (vfmap f) = F₁ f

  undvalue : DValue X Y → 𝒟.Hom X Y
  undvalue vid = 𝒟.id
  undvalue (vcomp f v) = unframe f 𝒟.∘ undvalue v

  --------------------------------------------------------------------------------
  -- Evaluation

  do-cvcomp : CValue B C → CValue A B → CValue A C
  do-cvcomp vid v2 = v2
  do-cvcomp (vcomp f v1) v2 = vcomp f (do-cvcomp v1 v2)

  ceval : CExpr A B → CValue A B
  ceval (e1 ‶∘‶ e2) = do-cvcomp (ceval e1) (ceval e2)
  ceval ‶id‶ = vid
  ceval (f ↑) = vcomp f vid

  do-dvcomp : DValue Y Z → DValue X Y → DValue X Z
  do-dvcomp vid v2 = v2
  do-dvcomp (vcomp f v1) v2 = vcomp f (do-dvcomp v1 v2)

  do-vfmap : CValue A B → DValue (F₀ A) (F₀ B)
  do-vfmap vid = vid
  do-vfmap (vcomp f v) = vcomp (vfmap f) (do-vfmap v)

  deval : DExpr X Y → DValue X Y
  deval (‶F₁‶ e) = do-vfmap (ceval e)
  deval (e1 ‶∘‶ e2) = do-dvcomp (deval e1) (deval e2)
  deval ‶id‶ = vid
  deval (f ↑) = vcomp (vhom f) vid

  --------------------------------------------------------------------------------
  -- Soundness

  do-cvcomp-sound : ∀ (v1 : CValue B C) → (v2 : CValue A B) → uncvalue (do-cvcomp v1 v2) ≡ uncvalue v1 𝒞.∘ uncvalue v2
  do-cvcomp-sound vid v2 = sym (𝒞.idl (uncvalue v2))
  do-cvcomp-sound (vcomp f v1) v2 = 𝒞.pushr (do-cvcomp-sound v1 v2)

  ceval-sound : ∀ (e : CExpr A B) → uncvalue (ceval e) ≡ uncexpr e
  ceval-sound (e1 ‶∘‶ e2) =
    uncvalue (do-cvcomp (ceval e1) (ceval e2))    ≡⟨ do-cvcomp-sound (ceval e1) (ceval e2) ⟩
    (uncvalue (ceval e1) 𝒞.∘ uncvalue (ceval e2)) ≡⟨ ap₂ 𝒞._∘_ (ceval-sound e1) (ceval-sound e2) ⟩
    uncexpr e1 𝒞.∘ uncexpr e2                     ∎
  ceval-sound ‶id‶ = refl
  ceval-sound (f ↑) = 𝒞.idr f

  do-vfmap-sound : ∀ (v : CValue A B) → undvalue (do-vfmap v) ≡ F₁ (uncvalue v)
  do-vfmap-sound vid = sym F-id
  do-vfmap-sound (vcomp f v) =
    F₁ f 𝒟.∘ undvalue (do-vfmap v) ≡⟨ ap (F₁ f 𝒟.∘_) (do-vfmap-sound v) ⟩
    F₁ f 𝒟.∘ F₁ (uncvalue v)       ≡˘⟨ F-∘ f (uncvalue v) ⟩
    F₁ (f 𝒞.∘ uncvalue v)          ∎

  do-dvcomp-sound : ∀ (v1 : DValue Y Z) → (v2 : DValue X Y) → undvalue (do-dvcomp v1 v2) ≡ undvalue v1 𝒟.∘ undvalue v2
  do-dvcomp-sound vid v2 = sym (𝒟.idl (undvalue v2))
  do-dvcomp-sound (vcomp f v1) v2 = 𝒟.pushr (do-dvcomp-sound v1 v2)

  deval-sound : ∀ (e : DExpr X Y) → undvalue (deval e) ≡ undexpr e
  deval-sound (‶F₁‶ e) =
    undvalue (do-vfmap (ceval e)) ≡⟨ do-vfmap-sound (ceval e) ⟩
    F₁ (uncvalue (ceval e))       ≡⟨ ap F₁ (ceval-sound e ) ⟩
    F₁ (uncexpr e)                ∎
  deval-sound (e1 ‶∘‶ e2) =
    undvalue (do-dvcomp (deval e1) (deval e2))  ≡⟨ do-dvcomp-sound (deval e1) (deval e2) ⟩
    undvalue (deval e1) 𝒟.∘ undvalue (deval e2) ≡⟨ ap₂ 𝒟._∘_ (deval-sound e1) (deval-sound e2) ⟩
    undexpr e1 𝒟.∘ undexpr e2                   ∎
  deval-sound ‶id‶ = refl
  deval-sound (f ↑) = 𝒟.idr f

  abstract
    solve : (e1 e2 : DExpr X Y) → undvalue (deval e1) ≡ undvalue (deval e2) → undexpr e1 ≡ undexpr e2
    solve e1 e2 p  = sym (deval-sound e1) ·· p ·· (deval-sound e2)

module Reflection where

  pattern category-args xs =
    _ h0∷ _ h0∷ _ v∷ xs

  pattern functor-args xs =
    _ h0∷ _ h0∷ _ h0∷ _ h0∷ _ h0∷ _ h0∷ _ v∷ xs

  pattern “id” =
    def (quote Precategory.id) (category-args (_ h∷ []))

  pattern “∘” f g =
    def (quote Precategory._∘_) (category-args (_ h∷ _ h∷ _ h∷ f v∷ g v∷ []))

  pattern “F₁” f =
    def (quote Functor.F₁) (functor-args (_ h∷ _ h∷ f v∷ []))

  mk-functor-args : Term → List (Arg Term) → List (Arg Term)
  mk-functor-args functor args = unknown h0∷ unknown h0∷ unknown h0∷ unknown h0∷ unknown h0∷ unknown h0∷ functor v∷ args

  “solve” : Term → Term → Term → Term
  “solve” functor lhs rhs =
    def (quote NbE.solve) (mk-functor-args functor $ infer-hidden 2 $ lhs v∷ rhs v∷ def (quote refl) [] v∷ [])

  build-cexpr : Term → Term
  build-cexpr “id” = con (quote NbE.CExpr.‶id‶) []
  build-cexpr (“∘” f g) = con (quote NbE.CExpr._‶∘‶_) (build-cexpr f v∷ build-cexpr g v∷ [])
  build-cexpr f = con (quote NbE.CExpr._↑) (f v∷ [])

  build-dexpr : Term → Term
  build-dexpr “id” = con (quote NbE.DExpr.‶id‶) []
  build-dexpr (“∘” f g) = con (quote NbE.DExpr._‶∘‶_) (build-dexpr f v∷ build-dexpr g v∷ [])
  build-dexpr (“F₁” f) = con (quote NbE.DExpr.‶F₁‶) (build-cexpr f v∷ [])
  build-dexpr f = con (quote NbE.DExpr._↑) (f v∷ [])

  dont-reduce : List Name
  dont-reduce = quote Precategory.id ∷ quote Precategory._∘_ ∷ quote Functor.F₁ ∷ []

  solve-macro : ∀ {o h o′ h′} {𝒞 : Precategory o h} {𝒟 : Precategory o′ h′} → Functor 𝒞 𝒟 → Term → TC ⊤
  solve-macro functor hole = 
   withNormalisation false $
   dontReduceDefs dont-reduce $ do
     functor-tm ← quoteTC functor
     goal ← inferType hole >>= reduce
     just (lhs , rhs) ← get-boundary goal
       where nothing → typeError $ strErr "Can't determine boundary: " ∷
                                   termErr goal ∷ []
     let elhs = build-dexpr lhs
     let erhs = build-dexpr rhs
     noConstraints $ unify hole (“solve” functor-tm elhs erhs)

macro
  functor! : ∀ {o h o′ h′} {𝒞 : Precategory o h} {𝒟 : Precategory o′ h′} → Functor 𝒞 𝒟 → Term → TC ⊤
  functor! functor = Reflection.solve-macro functor

private module Test {o h o′ h′} {𝒞 : Precategory o h} {𝒟 : Precategory o′ h′} (F : Functor 𝒞 𝒟) where
  module 𝒞 = Cat 𝒞
  module 𝒟 = Cat 𝒟
  open Functor F

  variable
    A B : 𝒞.Ob
    X Y : 𝒟.Ob
    a b c : 𝒞.Hom A B
    x y z : 𝒟.Hom X Y
    

  test : (x 𝒟.∘ F₁ (𝒞.id 𝒞.∘ 𝒞.id)) 𝒟.∘ F₁ a 𝒟.∘ F₁ (𝒞.id 𝒞.∘ b) ≡ 𝒟.id 𝒟.∘ x 𝒟.∘ F₁ (a 𝒞.∘ b)
  test = functor! F
