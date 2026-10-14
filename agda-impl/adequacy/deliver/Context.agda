{-# OPTIONS --guardedness --large-indices #-}

-- WHERE A DELIVERY STANDS: the witness opened at the subscription a
-- delivery has reached, as a zipper from there to the root.  A frame is
-- one kernel the delivery climbs through, with its siblings — what that
-- kernel holds beside the subscription below it.  A frame's observer is
-- the one that kernel registers for the subscription below, so the
-- delivery at a hole runs the hole's frame's observer.
--
-- A delivery grows the world and moves its siblings: a lane admitted, a
-- joiner's copy stepped, a joiner finished, a connect's held source
-- replaced.  Nothing it reaches is dropped — a lane killed by a switch
-- stays, cut — so a frame survives a delivery as itself, weakened.
module adequacy.deliver.Context where

open import Data.Bool using (Bool)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe)
open import Data.Unit using (⊤)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using ([]; _∷_)

import Tree as T
open import Tree using (Obs)
open import denotation.MonotonicList using (Timeline)
import denotation.Unfold as U
open import denotation.Unfold using (Srcs)
open import operation.AbstractObservable using (base; module Run)
open import operation.PureObservable using (Pureᴾ; World; _⊑_; Sink; wk∋)
open import adequacy.Realize using (module Realizing)

module Contexts (R : Set) where
  open Run (Pureᴾ R)
  open Kit
  open FlatKit
  open Realizing R
  open Canon

  ------------------------------------------------------------------------
  -- One kernel climbed through: the hole's `Δ A`, the parent's `Δ′ B`

  data Fr (h : World) : List Set → Set → List Set → Set → Set₁ where
    mapF    : ∀ {Δ A B} → (A → B) → Fr h Δ A Δ B
    scanF   : ∀ {Δ A B} → (B → A → B) → Ref h (base B) → Fr h Δ A Δ B
    takeF   : ∀ {Δ A} → Bool → (A → Bool) → Cut h → Sink h ⊤ → Fr h Δ A Δ A
    -- The hole is the outer: the lanes beside it.
    outerF  : ∀ {Δ A B} → T.FlatOp → (A → Obs Timeline Δ B) → Flat A h → Cut h → Sink h ⊤ → Sink h ⊤
            → List (Lane h Δ B) → Fr h Δ A Δ B
    -- The hole is a lane's inner: the outer, the lanes before it, its
    -- switch and detacher, the lanes after it.
    laneF   : ∀ {Δ A B} → T.FlatOp → (A → Obs Timeline Δ B) → Flat A h → Cut h → Sink h ⊤ → Sink h ⊤
            → Sub h Δ A → List (Lane h Δ B) → Cut h → Sink h ⊤ → List (Lane h Δ B) → Fr h Δ B Δ B
    -- The hole is a connect's source: the body beside it.
    sourceF : ∀ {Δ A B} → Subject A h → Cut h → Sink h ⊤ → U.Node A → Maybe (U.Node A) → Sub h (A ∷ Δ) B
            → Fr h Δ A Δ B
    -- The hole is a connect's body: the source beside it.
    bodyF   : ∀ {Δ A B} → Subject A h → Cut h → Sink h ⊤ → U.Node A → Maybe (U.Node A) → Sub h Δ A
            → Fr h (A ∷ Δ) B Δ B
    deferF  : ∀ {Δ A} → Sink h ⊤ → Fr h Δ A Δ A

  -- From the hole to the root.
  infixr 5 _◂_
  data Ctx (h : World) : List Set → Set → Set₁ where
    top : Ctx h [] R
    _◂_ : ∀ {Δ A Δ′ B} → Fr h Δ A Δ′ B → Ctx h Δ′ B → Ctx h Δ A

  plugF : ∀ {h Δ A Δ′ B} → Fr h Δ A Δ′ B → Sub h Δ A → Sub h Δ′ B
  plugF (mapF f)                              t = mapˢ f t
  plugF (scanF f r)                           t = scanˢ f r t
  plugF (takeF i p c u)                       t = takeWhileˢ i p c u t
  plugF (outerF op f fl oc u r ls)            t = flatMapˢ op f fl oc u r t ls
  plugF (laneF op f fl oc u r so bs c d as)   t = flatMapˢ op f fl oc u r so (bs ++ lane c d t ∷ as)
  plugF (sourceF S c u s₀ mm body)            t = connectˢ S c u s₀ mm t body
  plugF (bodyF S c u s₀ mm src)               t = connectˢ S c u s₀ mm src t
  plugF (deferF u)                            t = deferˢ u t

  plug : ∀ {h Δ A} → Ctx h Δ A → Sub h Δ A → Sub h [] R
  plug top      t = t
  plug (f ◂ k)  t = plug k (plugF f t)

  -- The subjects and sources in scope at the hole.
  envF : ∀ {h Δ A Δ′ B} → Fr h Δ A Δ′ B → Env Δ′ h → Env Δ h
  envF (bodyF S c u s₀ mm src) E = S ∷ E
  envF (mapF _)                E = E
  envF (scanF _ _)             E = E
  envF (takeF _ _ _ _)         E = E
  envF (outerF _ _ _ _ _ _ _)  E = E
  envF (laneF _ _ _ _ _ _ _ _ _ _ _) E = E
  envF (sourceF _ _ _ _ _ _)   E = E
  envF (deferF _)              E = E

  srcsF : ∀ {h Δ A Δ′ B} → Fr h Δ A Δ′ B → Srcs Δ′ → Srcs Δ
  srcsF (bodyF S c u s₀ mm src) ρ = s₀ ∷ ρ
  srcsF (mapF _)                ρ = ρ
  srcsF (scanF _ _)             ρ = ρ
  srcsF (takeF _ _ _ _)         ρ = ρ
  srcsF (outerF _ _ _ _ _ _ _)  ρ = ρ
  srcsF (laneF _ _ _ _ _ _ _ _ _ _ _) ρ = ρ
  srcsF (sourceF _ _ _ _ _ _)   ρ = ρ
  srcsF (deferF _)              ρ = ρ

  envC : ∀ {h Δ A} → Ctx h Δ A → Env Δ h
  envC top     = []
  envC (f ◂ k) = envF f (envC k)

  srcsC : ∀ {h Δ A} → Ctx h Δ A → Srcs Δ
  srcsC top     = []
  srcsC (f ◂ k) = srcsF f (srcsC k)

  -- The observer a frame's kernel registers for the subscription below.
  obsF : ∀ {h Δ A Δ′ B} → Fr h Δ A Δ′ B → Env Δ′ h → Observer B h → Observer A h
  obsF (mapF f)                            E o = mapO f o
  obsF (scanF f r)                         E o = scanO f r o
  obsF (takeF i p c u)                     E o = takeWhileO i p c o
  obsF (outerF op f fl oc u r ls)          E o = Flat′.outerO op f E o fl oc
  obsF (laneF op f fl oc u r so bs c d as) E o = Flat′.laneO op f E o fl c
  obsF (sourceF S c u s₀ mm body)          E o = feeder S
  obsF (bodyF S c u s₀ mm src)             E o = bodyO c o
  obsF (deferF u)                          E o = o

  obsC : ∀ {h Δ A} → Ctx h Δ A → Observer A h
  obsC top     = rootObs
  obsC (f ◂ k) = obsF f (envC k) (obsC k)

  wkFiring : ∀ {h v} → h ⊑ v → Firing h → Firing v
  wkFiring τ (firing s hd since at′ i b) = firing (wk∋ τ s) (wk∋ τ hd) since at′ i b

  ------------------------------------------------------------------------
  -- What a delivery does to what it does not climb through

  -- A subscription moved by a delivery, in a world grown by `τ`: its names
  -- weakened, a cold's phase where it was, a lane admitted at the front
  -- of a lane list, a joiner's count and copy moved or the joiner
  -- finished, a connect's held source replaced.
  mutual
    data Evolves {h v} (τ : h ⊑ v) : ∀ {Δ A} → Sub h Δ A → Sub v Δ A → Set₁ where
      coldᵉ    : ∀ {Δ A} {s : Sink h A} {hd ph} → Evolves τ (coldˢ {Δ = Δ} s hd ph) (coldˢ (wk∋ τ s) (wk∋ τ hd) ph)
      doneᵉ    : ∀ {Δ A} → Evolves τ (doneˢ {Δ = Δ} {A}) doneˢ
      mapᵉ     : ∀ {Δ A B} {f : A → B} {s : Sub h Δ A} {s′} → Evolves τ s s′ → Evolves τ (mapˢ f s) (mapˢ f s′)
      scanᵉ    : ∀ {Δ A B} {f : B → A → B} {r} {s : Sub h Δ A} {s′} → Evolves τ s s′ → Evolves τ (scanˢ f r s) (scanˢ f (wkR τ r) s′)
      takeᵉ    : ∀ {Δ A} {i p c u} {s : Sub h Δ A} {s′} → Evolves τ s s′
               → Evolves τ (takeWhileˢ i p c u s) (takeWhileˢ i p (wkCut τ c) (wk∋ τ u) s′)
      flatMapᵉ : ∀ {Δ A B} {op} {f : A → Obs Timeline Δ B} {fl oc u r} {so : Sub h Δ A} {so′ ls ls′}
               → Evolves τ so so′ → EvLanes τ ls ls′
               → Evolves τ (flatMapˢ op f fl oc u r so ls) (flatMapˢ op f (wkFlat τ fl) (wkCut τ oc) (wk∋ τ u) (wk∋ τ r) so′ ls′)
      connectᵉ : ∀ {Δ A B} {S : Subject A h} {c u s₀ m m′} {src : Sub h Δ A} {src′} {body : Sub h (A ∷ Δ) B} {body′}
               → Evolves τ src src′ → Evolves τ body body′
               → Evolves τ (connectˢ S c u s₀ m src body) (connectˢ (wkSubject τ S) (wkCut τ c) (wk∋ τ u) s₀ m′ src′ body′)
      joinᵉ    : ∀ {Δ A} {j i i′ sk l} {x : A ∈ Δ} {cp cp′}
               → Evolves τ (joinˢ j i sk l x cp) (joinˢ j i′ (wk∋ τ sk) (wkR τ l) x cp′)
      finishᵉ  : ∀ {Δ A} {j i sk l} {x : A ∈ Δ} {cp} → Evolves τ (joinˢ j i sk l x cp) doneˢ
      deferᵉ   : ∀ {Δ A} {u} {s : Sub h Δ A} {s′} → Evolves τ s s′ → Evolves τ (deferˢ u s) (deferˢ (wk∋ τ u) s′)

    -- Lane for lane.
    data KeepLanes {h v} (τ : h ⊑ v) : ∀ {Δ B} → List (Lane h Δ B) → List (Lane v Δ B) → Set₁ where
      []ᵏ  : ∀ {Δ B} → KeepLanes τ {Δ} {B} [] []
      _∷ᵏ_ : ∀ {Δ B} {c d} {s : Sub h Δ B} {s′ ls ls′} → Evolves τ s s′ → KeepLanes τ ls ls′
           → KeepLanes τ (lane c d s ∷ ls) (lane (wkCut τ c) (wk∋ τ d) s′ ∷ ls′)

    -- New lanes in front of the old.
    data EvLanes {h v} (τ : h ⊑ v) {Δ B} (ls : List (Lane h Δ B)) : List (Lane v Δ B) → Set₁ where
      admitted : ∀ new {ls′} → KeepLanes τ ls ls′ → EvLanes τ ls (new ++ ls′)

  -- A frame moved by a delivery that climbed through it.
  data GrownF {h v} (τ : h ⊑ v) : ∀ {Δ A Δ′ B} → Fr h Δ A Δ′ B → Fr v Δ A Δ′ B → Set₁ where
    mapᵍ    : ∀ {Δ A B} {f : A → B} → GrownF τ (mapF {Δ = Δ} f) (mapF f)
    scanᵍ   : ∀ {Δ A B} {f : B → A → B} {r} → GrownF τ (scanF {Δ = Δ} f r) (scanF f (wkR τ r))
    takeᵍ   : ∀ {Δ A} {i} {p : A → Bool} {c u} → GrownF τ (takeF {Δ = Δ} i p c u) (takeF i p (wkCut τ c) (wk∋ τ u))
    outerᵍ  : ∀ {Δ A B} {op} {f : A → Obs Timeline Δ B} {fl oc u r ls ls′} → EvLanes τ ls ls′
            → GrownF τ (outerF op f fl oc u r ls) (outerF op f (wkFlat τ fl) (wkCut τ oc) (wk∋ τ u) (wk∋ τ r) ls′)
    laneᵍ   : ∀ {Δ A B} {op} {f : A → Obs Timeline Δ B} {fl oc u r} {so : Sub h Δ A} {so′ bs bs′ c d as as′}
            → Evolves τ so so′ → EvLanes τ bs bs′ → KeepLanes τ as as′
            → GrownF τ (laneF op f fl oc u r so bs c d as)
                       (laneF op f (wkFlat τ fl) (wkCut τ oc) (wk∋ τ u) (wk∋ τ r) so′ bs′ (wkCut τ c) (wk∋ τ d) as′)
    sourceᵍ : ∀ {Δ A B} {S : Subject A h} {c u s₀ mm mm′} {body : Sub h (A ∷ Δ) B} {body′} → Evolves τ body body′
            → GrownF τ (sourceF S c u s₀ mm body) (sourceF (wkSubject τ S) (wkCut τ c) (wk∋ τ u) s₀ mm′ body′)
    bodyᵍ   : ∀ {Δ A B} {S : Subject A h} {c u s₀ mm mm′} {src : Sub h Δ A} {src′} → Evolves τ src src′
            → GrownF τ (bodyF {B = B} S c u s₀ mm src) (bodyF (wkSubject τ S) (wkCut τ c) (wk∋ τ u) s₀ mm′ src′)
    deferᵍ  : ∀ {Δ A} {u} → GrownF τ (deferF {Δ = Δ} {A} u) (deferF (wk∋ τ u))

  data Grown {h v} (τ : h ⊑ v) : ∀ {Δ A} → Ctx h Δ A → Ctx v Δ A → Set₁ where
    topᵍ : Grown τ top top
    _◂ᵍ_ : ∀ {Δ A Δ′ B} {f : Fr h Δ A Δ′ B} {f′ k k′} → GrownF τ f f′ → Grown τ k k′ → Grown τ (f ◂ k) (f′ ◂ k′)
