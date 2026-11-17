{-# OPTIONS --guardedness #-}

-- THE FLATMAP'S CASE (`flat-rel`): the plain flatMap's record against its
-- elaboration, one layer at a time.  The plain side stays the flatMap's
-- own table; the elaborated side grows outward from the lanes' flatMap
-- (`core`) through the combined scan, the closer and the share.
--
-- The source is related once, at the share's subscription, in the
-- environment the share's trigger extends; its hot is the shared table
-- the lanes' flatMap reads.  The lanes are related wherever they are
-- subscribed alike, each in the environment the flatMap's four binders
-- extend, which no lane reads.
--
-- A lane is subscribed past its creator, so its pair is aligned from its
-- creator's.  `flat-core` owes that alignment, one story per operator:
-- merge, switch and exhaust subscribe each lane under its value's row, so
-- the source's `cuts` and `linked` at the row align it; only the bounded
-- merge queues a lane under an earlier lane's end, a run-dependent row.
module simultaneous.TableFlat where

open import Data.List using (List; []; _∷_; [_])
open import Data.List.Relation.Unary.All using (All; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (refl)

open import Tree using (Obs; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ; of; flatMap; connect; connected)
open import denotation.Position using (Pos; Label; root; _≟ᵖ_; ix; sub; _⊕_)
open import denotation.Events using (Timeline; fresh)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (hotOf)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Listing using (listC; listC-ok; UncutEnv)
open import simultaneous.InstEmit using (valuesOf)
open import simultaneous.TableCorr using (Rel)
open import simultaneous.TableEnv using (Ren; wk; Tab; Tab*; _⊕ˡ_; Linked; linked-r*; Aligned; aligned-r*; Rest; Out; _⊢_; EnvR; maps; env-wk; Holds; Full)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; elab; each; laneˢ; closer; combined; trackers)

module Flat {Γ A B} n (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A)
  (ρ : ℕ → All Tb.Listed Γ) (uρ : ∀ N → UncutEnv (ρ N)) {Δ} (ρι : Ren Γ Δ) (ρ* : ℕ → All Tb.Listed Δ) (uρ* : ∀ N → UncutEnv (ρ* N))
  (env : EnvR ρ ρι ρ*) (p p* : Pos) where

  ----------------------------------------------------------------------
  -- The elaborated parts

  ρι⁴ : Ren Γ (⊤ ∷ IE B ∷ IE A ∷ ⊤ ∷ Δ)
  ρι⁴ = wk (wk (wk (wk ρι)))

  s* : Obs Timeline (⊤ ∷ Δ) (IE A)
  s* = elab (wk ρι) s

  core : FlatOp → Obs Timeline (IE B ∷ IE A ∷ ⊤ ∷ Δ) (IE B)
  core op = flatMap op (λ a → laneˢ (elab ρι⁴ (f a))) (each valuesOf (connected (there (here refl))))

  inner : FlatOp → Obs Timeline (IE B ∷ IE A ∷ ⊤ ∷ Δ) (IE B)
  inner op = connect (core op) (combined op (trackers Γ 0 (wk (wk (wk (wk ρι))))))

  body : FlatOp → Obs Timeline (IE A ∷ ⊤ ∷ Δ) (IE B)
  body op = connect closer (inner op)

  shared : Obs Timeline (⊤ ∷ Δ) (IE A)
  shared = flatMap (mergeᶠ nothing) (λ _ → s*) (connected (here refl))

  ----------------------------------------------------------------------
  -- Their subscriptions and hots

  -- The share's body, the closer's body, the combined connect, and the
  -- lanes' flatMap.
  c₃ c₂ c₁ c₀ : Pos
  c₃ = p* ⊕ [ ix 0 ] ⊕ [ ix 0 ]
  c₂ = c₃ ⊕ [ ix 0 ]
  c₁ = c₂ ⊕ [ ix 1 ]
  c₀ = c₂ ⊕ [ ix 0 ]

  -- The source's elaborated subscription: the lane of the trigger's value,
  -- read by the shared flatMap.
  sp* : Pos
  sp* = p* ⊕ˡ (ix 1 ∷ ix 0 ∷ sub (p* ⊕ [ ix 0 ] ⊕ [ ix 1 ]) ∷ ix 1 ∷ [])

  tt-tab : ℕ → Tb.Listed ⊤
  tt-tab N = hotOf (proj₁ (listC-ok (3 + N) n (of (tt ∷ [])) (uρ* N) (p* ⊕ [ ix 1 ])))

  ρ*s : ℕ → All Tb.Listed (⊤ ∷ Δ)
  ρ*s N = tt-tab N ∷ ρ* N

  uρ*s : ∀ N → UncutEnv (ρ*s N)
  uρ*s N = proj₂ (proj₂ (listC-ok (3 + N) n (of (tt ∷ [])) (uρ* N) (p* ⊕ [ ix 1 ]))) , uρ* N

  sh-tab : ℕ → Tb.Listed (IE A)
  sh-tab N = hotOf (proj₁ (listC-ok (3 + N) n shared {ρ*s N} (uρ*s N) (p* ⊕ [ ix 0 ] ⊕ [ ix 1 ])))

  ρ*h : ℕ → All Tb.Listed (IE A ∷ ⊤ ∷ Δ)
  ρ*h N = sh-tab N ∷ ρ*s N

  uρ*h : ∀ N → UncutEnv (ρ*h N)
  uρ*h N = proj₂ (proj₂ (listC-ok (3 + N) n shared {ρ*s N} (uρ*s N) (p* ⊕ [ ix 0 ] ⊕ [ ix 1 ]))) , uρ*s N

  cl-tab : ℕ → Tb.Listed (IE B)
  cl-tab N = hotOf (proj₁ (listC-ok (3 + N) n closer {ρ*h N} (uρ*h N) (c₃ ⊕ [ ix 1 ])))

  ρ*c : ℕ → All Tb.Listed (IE B ∷ IE A ∷ ⊤ ∷ Δ)
  ρ*c N = cl-tab N ∷ ρ*h N

  ----------------------------------------------------------------------
  -- The children's records

  -- The source, at the share's subscription.
  Src : Set₁
  Src = Out n s ρ (wk ρι) ρ*s (maps env) p sp*

  -- Each lane, wherever subscribed alike, whatever the four binders hold.
  Lanes : Set₁
  Lanes = ∀ a (t₁ : ℕ → Tb.Listed ⊤) (t₂ : ℕ → Tb.Listed (IE B)) (t₃ : ℕ → Tb.Listed (IE A)) (t₄ : ℕ → Tb.Listed ⊤)
        → (∀ N → UncutEnv (t₁ N ∷ t₂ N ∷ t₃ N ∷ t₄ N ∷ ρ* N))
        → Holds n (f a) ρ ρι⁴ (λ N → t₁ N ∷ t₂ N ∷ t₃ N ∷ t₄ N ∷ ρ* N) (env-wk t₁ (env-wk t₂ (env-wk t₃ (env-wk t₄ env))))

  -- The plain flatMap's tables.
  P : FlatOp → ℕ → _
  P op = Tab n (flatMap op f s) ρ p

  -- The lanes' flatMap related to the plain flatMap.
  Core : FlatOp → Set₁
  Core op = Src → Lanes → Aligned (maps env) ρ p p* → Linked p p*
          → Rel (P op) (λ N → listC (3 + N) n (core op) (ρ*c N) c₁) p c₁

  ----------------------------------------------------------------------
  -- The layers

  -- THE LANES' FLATMAP: the shared hot is the source's elaborated rows,
  -- each value read off by `each valuesOf` under its image; each value's
  -- elaborated lane is the plain lane's, run through `laneˢ`.  Its rows
  -- are the plain flatMap's values and ends, along the source's map for
  -- the source's rows and each lane's for its own.
  --
  -- A lane's record is had only from a cut: `Lanes` wants the lane's
  -- value and its pair's alignment, and both are read off the source's
  -- row `TR (Ps N) q (out a)` and `Rest.cuts` at it.  So `φ`, `Put` and
  -- the preimage lists are written per cut, each lane row through its own
  -- lane's record at that cut; `back` is what lets the erasure read them
  -- at the cut settling the image.

  postulate
    -- Every value's lane is subscribed under its row, and every lane row
    -- is shown: each lane's pair is aligned by the source's facts at its
    -- value's row and its image.
    flat-merge : Core (mergeᶠ nothing)

    -- A value's lane is subscribed under its row when fewer than `k`
    -- lanes are live there, else queued under the end of the lane whose
    -- end frees its slot: the queue's state is a run's, so the pair is
    -- aligned by the source's facts or by that earlier lane's, and the
    -- earlier lane is the same one on both sides.
    flat-concat : ∀ k → Core (mergeᶠ (just k))

    -- Every value's lane is subscribed under its row, and a lane's rows
    -- are shown only before the next value's row: the cut is the source's
    -- row, aligned by the source's facts at both rows.
    flat-switch : Core switchᶠ

    -- Every value's lane is subscribed under its row and shown only when
    -- no earlier shown lane is live at that row: whether one is live is
    -- read off the lanes' ends, aligned by the lanes' own records.
    flat-exhaust : Core exhaustᶠ

  flat-core : ∀ op → Core op
  flat-core (mergeᶠ nothing)  = flat-merge
  flat-core (mergeᶠ (just k)) = flat-concat k
  flat-core switchᶠ           = flat-switch
  flat-core exhaustᶠ          = flat-exhaust

  postulate
    -- THE COMBINED SCAN: the lanes' flatMap read through its hot by the
    -- scan over its routes and the trackers', each value re-emitted in
    -- place with its marks.
    flat-comb : ∀ op → Rel (P op) (λ N → listC (3 + N) n (core op) (ρ*c N) c₁) p c₁
              → Rel (P op) (λ N → listC (3 + N) n (inner op) (ρ*c N) c₂) p c₂

    -- THE CLOSER: the combined run past the closer's subscription, the
    -- closer's marks unshown and in the instants of the source's ends.
    flat-close : ∀ op → Rel (P op) (λ N → listC (3 + N) n (inner op) (ρ*c N) c₂) p c₂
               → Rel (P op) (λ N → listC (3 + N) n (body op) (ρ*h N) c₃) p c₃

    -- THE SHARE: the body read past the share's two connects; the
    -- trigger's and the shared hot's own rows are never shown.
    flat-share : ∀ op → Rel (P op) (λ N → listC (3 + N) n (body op) (ρ*h N) c₃) p c₃
               → Rel (P op) (Tab* n ρι (flatMap op f s) ρ* p*) p p*

  flat-tab : ∀ op → Src → Lanes → Aligned (maps env) ρ p p* → Linked p p* → Rel (P op) (Tab* n ρι (flatMap op f s) ρ* p*) p p*
  flat-tab op Os Ls al lk = flat-share op (flat-close op (flat-comb op (flat-core op Os Ls al lk)))

  postulate
    -- THE FLATMAP'S ORDER FACTS: each row is a source row or a lane row
    -- at its own position, imaged along its stream's map, so each fact is
    -- the source's or the lane's; a lane's subscription is past every
    -- earlier pair that cuts the flatMap alike.
    flatmap-order : ∀ op (Os : Src) (Ls : Lanes) (al : Aligned (maps env) ρ p p*) (lk : Linked p p*) → Rest (maps env) ρ (flat-tab op Os Ls al lk)

flat-rel : ∀ {Γ A B} n (op : FlatOp) (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A)
         → Full n s → (∀ a → Full n (f a)) → Full n (flatMap op f s)
flat-rel n op f s Fs Ff ρ uρ ρι ρ* uρ* env p p* al lk = F.flat-tab op Os Ls al lk ⊢ F.flatmap-order op Os Ls al lk
  where
    module F = Flat n f s ρ uρ ρι ρ* uρ* env p p*

    path : List Label
    path = ix 1 ∷ ix 0 ∷ sub (p* ⊕ [ ix 0 ] ⊕ [ ix 1 ]) ∷ ix 1 ∷ []

    Os : F.Src
    Os = Fs ρ uρ (wk ρι) F.ρ*s F.uρ*s (env-wk F.tt-tab env) p F.sp*
           (aligned-r* {Ψ = maps env} {ρ = ρ} al path) (linked-r* lk path)

    Ls : F.Lanes
    Ls a t₁ t₂ t₃ t₄ u = Ff a ρ uρ F.ρι⁴ (λ N → t₁ N ∷ t₂ N ∷ t₃ N ∷ t₄ N ∷ ρ* N) u (env-wk t₁ (env-wk t₂ (env-wk t₃ (env-wk t₄ env))))
