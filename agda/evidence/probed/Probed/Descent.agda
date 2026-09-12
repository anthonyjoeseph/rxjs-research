-- THE DESCENT GUARDS, INSTANTIATED — the rows that stand under
-- `rank-sufficient`, now that the statement itself is a real body and its
-- two remaining leaves are what evidence can be about.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in the
-- proof may rest on it.  Checked by `make probed`, claimed by `Probed.Main`.
-- TARGET: drain-dry-free @140a87
-- TARGET: entry-hop-fits @3a11cc
--
-- WHY THIS REGION AND NOT THE CANONICAL PROGRAMS.  `evaluate` descends on
-- a triple and three of its clauses are guarded by a comparison that can
-- FAIL; a failing guard returns a `dry` emit and the run continues, so the
-- statement is exactly `no run ever takes that branch`.  Of the three
-- guards, the μ one and the rank one are only reachable through `μᵉ` — and
-- `μᵉ` is the one constructor the generator this repo runs cannot produce,
-- so every seed ever swept has been silent about two thirds of the claim.
-- That is why these rows are hand-written and why they are recursion
-- first: the behavioural gap and the proof gap are the same region.
--
-- THE RUN SPLITS WHERE THE ASSEMBLY SPLITS IT, which is why a row here is
-- about a half rather than about a program.  `evaluate` is the root
-- subscribe followed by the drain, and dry-freedom of each half is a
-- separate obligation; the burst's is now proven outright at every shape
-- but the three flatteners, so the twelve recursive programs land on the
-- drain leaf — which is where every one of them does its recursion.
--
-- EVERY ROW IS LABELLED, because a row that could not have failed is not a
-- row.  `hasDry` is `any` over the emit stream, so it is `false` outright
-- on a run that emitted nothing — which is the vacuity available here and
-- the only one.  Each row therefore pins the EVENT COUNT of the half it is
-- about, by `refl`: the count is what `hasDry` walks, so a positive one
-- says the quantifier the row discharges was not empty, and it is free,
-- since the row forced every one of those events already.
--
-- WHAT THE COUNTS DO NOT SEPARATE, and it is a fact about rxjs rather
-- than a gap here.  Over the empty context the three flattening
-- strategies agree emit for emit, because the non-recursive inner is
-- SYNCHRONOUS and completes before the outer's next emission — so a
-- switch has nothing live to drop and an exhaust nothing live to block.
-- Separating them needs an inner that is still live when the recursive
-- one arrives, which is what the scripted slot at the end is for, and
-- there the counts do come apart.  The rows over the agreeing programs
-- stay: they reach the guard through different registry clauses, which
-- is what the statement is about, and identical output is not identical
-- descent.
module Probed.Descent where

open import Data.List using (List; []; _∷_; length; map)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing; just)
open import Data.Nat using (ℕ)
open import Data.Nat.ListAction using (sum)
open import Data.Product using (_×_; proj₁; proj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Fuel; InstEmit; cold; after_,_)
open import Rx.Exp using (Ctx; Closed; natᵗ; nat̂; strmᵗ; ofᵉ; takeᵉ;
  mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ)
open import Rx.Evaluator using (Stream; Sched; EvalSt; drain; subscribeE;
  rootWitness; root; sched-init; st-init)
open import Rx.Slots using (Slots; scripted)
open import Verify-Rank-Sufficient using (drain-dry-free; entry-hop-fits)
open import Probed.Apparatus using (Confirms; Below)

----------------------------------------------------------------------
-- The non-vacuity measure: how many EVENTS `hasDry` had to look at.  It
-- is `any dryEvent` over each emit's event list and then over the
-- stream, so this is exactly the size of the quantification a row
-- discharges — zero here and the row would be `false` by emptiness
-- rather than by the guards holding.
----------------------------------------------------------------------

evs : ∀ {A : Set} → List (InstEmit A) → ℕ
evs = sum ∘ map (length ∘ InstEmit.events)

----------------------------------------------------------------------
-- The two halves a run splits into, named once so a row can point at
-- either.  `entry` is the root subscribe the evaluator performs before
-- it drains, so `drainOf` is what `drain-dry-free` is about everywhere.
----------------------------------------------------------------------

entry : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  Stream Γ t × Sched Γ × EvalSt e
entry e ins = subscribeE (rootWitness e ins) e root 0 0 (sched-init e ins) (st-init e)

----------------------------------------------------------------------
-- The empty context: these programs are pure recursion, with no slot to
-- connect, so the ONE guard they can be silent about is the connect one —
-- which is stated over a count the entry seeds at zero here.
----------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ⱽ

ins₀ : Slots Γ₀
ins₀ = λ ()

FUEL : Fuel
FUEL = 30

drainOf : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) → Stream Γ t
drainOf e ins = drain FUEL 1 (proj₁ (proj₂ (entry e ins))) (proj₂ (proj₂ (entry e ins)))

----------------------------------------------------------------------
-- P1 — the recursive merge, which is `repeat` and the smallest program
-- that forces `unfoldμ` at all.  LOAD-BEARING: the μ guard compares
-- `syncSizeᵉ (unfoldμ body)` against `syncSizeᵉ (μᵉ body)` at every
-- unfolding, so a run that unfolds once has taken the comparison once.
----------------------------------------------------------------------

progP1 : Closed Γ₀ natᵗ
progP1 = μᵉ (mergeAllᵉ nothing
  (ofᵉ ( strmᵗ (ofᵉ (nat̂ 1 ∷ []))
       ∷ strmᵗ (deferᵉ (varᵉ (here refl)))
       ∷ [])))

descP1 : Confirms (drain-dry-free FUEL 1 0 (λ _ → 0)
  (proj₁ (proj₂ (entry progP1 ins₀))) (proj₂ (proj₂ (entry progP1 ins₀))) Below)
descP1 = refl

_ : evs (drainOf progP1 ins₀) ≡ 210      -- LOAD-BEARING
_ = refl

----------------------------------------------------------------------
-- P2 — the same recursion under a `takeᵉ`, which is the shape that
-- actually terminates in rxjs and the one a user writes.  LOAD-BEARING
-- for a different reason than P1: the cut arrives from OUTSIDE the μ, so
-- the unfolding is interrupted mid-descent rather than run out of fuel,
-- and the count below is an order of magnitude smaller for exactly that
-- reason.
----------------------------------------------------------------------

progP2 : Closed Γ₀ natᵗ
progP2 = takeᵉ (nat̂ 3) progP1

descP2 : Confirms (drain-dry-free FUEL 1 0 (λ _ → 0)
  (proj₁ (proj₂ (entry progP2 ins₀))) (proj₂ (proj₂ (entry progP2 ins₀))) Below)
descP2 = refl

_ : evs (drainOf progP2 ins₀) ≡ 16       -- LOAD-BEARING
_ = refl

----------------------------------------------------------------------
-- P3 — μ INSIDE μ.  This is the rank guard's own region: the inner
-- recursion is an observable EMITTED by the outer one, so the claim that
-- an emitted inner's nesting is strictly under its emitter's is what
-- stands between this program and a dry emit.  The one row here that no
-- flat program can buy.
----------------------------------------------------------------------

progP3 : Closed Γ₀ natᵗ
progP3 = μᵉ (mergeAllᵉ nothing
  (ofᵉ ( strmᵗ (μᵉ (mergeAllᵉ nothing
           (ofᵉ ( strmᵗ (ofᵉ (nat̂ 2 ∷ []))
                ∷ strmᵗ (deferᵉ (varᵉ (here refl)))
                ∷ []))))
       ∷ strmᵗ (deferᵉ (varᵉ (here refl)))
       ∷ [])))

descP3 : Confirms (drain-dry-free FUEL 1 0 (λ _ → 0)
  (proj₁ (proj₂ (entry progP3 ins₀))) (proj₂ (proj₂ (entry progP3 ins₀))) Below)
descP3 = refl

_ : evs (drainOf progP3 ins₀) ≡ 228      -- LOAD-BEARING
_ = refl

----------------------------------------------------------------------
-- P4 and P5 — the recursion under the two flattening strategies that are
-- not merge.  `switchAllᵉ` unsubscribes the previous inner on each new
-- one and `exhaustAllᵉ` drops new ones while an inner is live, so each
-- reaches the unfold along a different registry path — and, on a
-- synchronous inner, along a different path to the SAME stream.
----------------------------------------------------------------------

progP4 : Closed Γ₀ natᵗ
progP4 = μᵉ (switchAllᵉ
  (ofᵉ ( strmᵗ (ofᵉ (nat̂ 1 ∷ []))
       ∷ strmᵗ (deferᵉ (varᵉ (here refl)))
       ∷ [])))

descP4 : Confirms (drain-dry-free FUEL 1 0 (λ _ → 0)
  (proj₁ (proj₂ (entry progP4 ins₀))) (proj₂ (proj₂ (entry progP4 ins₀))) Below)
descP4 = refl

_ : evs (drainOf progP4 ins₀) ≡ 210      -- LOAD-BEARING
_ = refl

progP5 : Closed Γ₀ natᵗ
progP5 = μᵉ (exhaustAllᵉ
  (ofᵉ ( strmᵗ (ofᵉ (nat̂ 1 ∷ []))
       ∷ strmᵗ (deferᵉ (varᵉ (here refl)))
       ∷ [])))

descP5 : Confirms (drain-dry-free FUEL 1 0 (λ _ → 0)
  (proj₁ (proj₂ (entry progP5 ins₀))) (proj₂ (proj₂ (entry progP5 ins₀))) Below)
descP5 = refl

_ : evs (drainOf progP5 ins₀) ≡ 210      -- LOAD-BEARING
_ = refl

----------------------------------------------------------------------
-- P6 — a bounded merge, which is the limit axis: `just 1` is rxjs's
-- `concatAll`, so the recursive inner is PARKED rather than subscribed
-- and the unfold happens on a drain rather than on arrival.
----------------------------------------------------------------------

progP6 : Closed Γ₀ natᵗ
progP6 = μᵉ (mergeAllᵉ (just 1)
  (ofᵉ ( strmᵗ (ofᵉ (nat̂ 1 ∷ []))
       ∷ strmᵗ (deferᵉ (varᵉ (here refl)))
       ∷ [])))

descP6 : Confirms (drain-dry-free FUEL 1 0 (λ _ → 0)
  (proj₁ (proj₂ (entry progP6 ins₀))) (proj₂ (proj₂ (entry progP6 ins₀))) Below)
descP6 = refl

_ : evs (drainOf progP6 ins₀) ≡ 210      -- LOAD-BEARING
_ = refl

----------------------------------------------------------------------
-- THE CONNECT GUARD, which needs a context: a SHARED slot is the only
-- thing that moves the unconnected count, and the programs above are
-- stated over the empty context where that count is seeded at zero and
-- the guard is never reached.  Here the recursion sits under a share, so
-- one run takes the connect peel and the μ peel both.
----------------------------------------------------------------------

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

open import Data.Fin using (zero)
open import Rx.Exp using (input)
open import Rx.Slots using (shared)

insShared : Slots Γ₁
insShared zero = shared (ofᵉ (nat̂ 7 ∷ nat̂ 8 ∷ []))

progP7 : Closed Γ₁ natᵗ
progP7 = μᵉ (mergeAllᵉ nothing
  (ofᵉ ( strmᵗ (input zero)
       ∷ strmᵗ (deferᵉ (varᵉ (here refl)))
       ∷ [])))

descP7 : Confirms (drain-dry-free FUEL 1 0 (λ _ → 0)
  (proj₁ (proj₂ (entry progP7 insShared))) (proj₂ (proj₂ (entry progP7 insShared))) Below)
descP7 = refl

_ : evs (drainOf progP7 insShared) ≡ 180  -- LOAD-BEARING
_ = refl

----------------------------------------------------------------------
-- P8 — the same share reached TWICE in one instant (a diamond) under the
-- recursion, which is the shape whose connect count the guard is stated
-- over: two references, one connect, and the recursion re-entering both.
----------------------------------------------------------------------

progP8 : Closed Γ₁ natᵗ
progP8 = μᵉ (mergeAllᵉ nothing
  (ofᵉ ( strmᵗ (input zero)
       ∷ strmᵗ (input zero)
       ∷ strmᵗ (deferᵉ (varᵉ (here refl)))
       ∷ [])))

descP8 : Confirms (drain-dry-free FUEL 1 0 (λ _ → 0)
  (proj₁ (proj₂ (entry progP8 insShared))) (proj₂ (proj₂ (entry progP8 insShared))) Below)
descP8 = refl

_ : evs (drainOf progP8 insShared) ≡ 240  -- LOAD-BEARING
_ = refl

----------------------------------------------------------------------
-- P9 and P10 — the recursion over a slot that is still LIVE when the
-- recursive inner arrives, which is the only way the flattening
-- strategies separate at all.  A scripted cold source with an async tail
-- keeps emitting past its subscribe frame, so the switch has something
-- to drop; the two counts below differ, and that difference is the whole
-- justification for keeping the strategy axis in this file.
----------------------------------------------------------------------

insAsync : Slots Γ₁
insAsync zero = scripted (cold (1 ∷ []) (after 1 , 2 ∷ after 1 , 3 ∷ []))

progP9 : Closed Γ₁ natᵗ
progP9 = μᵉ (mergeAllᵉ nothing
  (ofᵉ ( strmᵗ (input zero)
       ∷ strmᵗ (deferᵉ (varᵉ (here refl)))
       ∷ [])))

descP9 : Confirms (drain-dry-free FUEL 1 0 (λ _ → 0)
  (proj₁ (proj₂ (entry progP9 insAsync))) (proj₂ (proj₂ (entry progP9 insAsync))) Below)
descP9 = refl

_ : evs (drainOf progP9 insAsync) ≡ 94    -- LOAD-BEARING
_ = refl

progP10 : Closed Γ₁ natᵗ
progP10 = μᵉ (switchAllᵉ
  (ofᵉ ( strmᵗ (input zero)
       ∷ strmᵗ (deferᵉ (varᵉ (here refl)))
       ∷ [])))

descP10 : Confirms (drain-dry-free FUEL 1 0 (λ _ → 0)
  (proj₁ (proj₂ (entry progP10 insAsync))) (proj₂ (proj₂ (entry progP10 insAsync))) Below)
descP10 = refl

_ : evs (drainOf progP10 insAsync) ≡ 210  -- LOAD-BEARING
_ = refl

----------------------------------------------------------------------
-- P11 and P12 — THE RANK GUARD'S SHARPEST SHAPE IN THIS FILE, and the
-- one every program above is silent about.  A slot reference is ONE
-- SYMBOL standing for a definition of any size, so a share holding a
-- RECURSION emits an inner whose nesting is fixed outside the emitter's
-- own syntax: the guard cannot read it off the term it is comparing.
-- P11 emits it from the top, P12 from inside a second recursion, which
-- is that shape and the μ-in-μ one at once.
----------------------------------------------------------------------

insMu : Slots Γ₁
insMu zero = shared (μᵉ (mergeAllᵉ nothing
  (ofᵉ ( strmᵗ (ofᵉ (nat̂ 5 ∷ []))
       ∷ strmᵗ (deferᵉ (varᵉ (here refl)))
       ∷ []))))

progP11 : Closed Γ₁ natᵗ
progP11 = μᵉ (mergeAllᵉ nothing
  (ofᵉ ( strmᵗ (input zero)
       ∷ strmᵗ (deferᵉ (varᵉ (here refl)))
       ∷ [])))

descP11 : Confirms (drain-dry-free FUEL 1 0 (λ _ → 0)
  (proj₁ (proj₂ (entry progP11 insMu))) (proj₂ (proj₂ (entry progP11 insMu))) Below)
descP11 = refl

_ : evs (drainOf progP11 insMu) ≡ 300     -- LOAD-BEARING
_ = refl

progP12 : Closed Γ₁ natᵗ
progP12 = μᵉ (mergeAllᵉ nothing
  (ofᵉ ( strmᵗ (μᵉ (mergeAllᵉ nothing
           (ofᵉ ( strmᵗ (input zero)
                ∷ strmᵗ (deferᵉ (varᵉ (here refl)))
                ∷ []))))
       ∷ strmᵗ (deferᵉ (varᵉ (here refl)))
       ∷ [])))

descP12 : Confirms (drain-dry-free FUEL 1 0 (λ _ → 0)
  (proj₁ (proj₂ (entry progP12 insMu))) (proj₂ (proj₂ (entry progP12 insMu))) Below)
descP12 = refl

_ : evs (drainOf progP12 insMu) ≡ 233     -- LOAD-BEARING
_ = refl

----------------------------------------------------------------------
-- THE FIT ITSELF, WHICH IS THE HALF THE ROWS ABOVE DISCHARGE IN PASSING.
-- Every row above hands the target a `Below`, so every one of them has
-- already shown the premise holds at its own point; these three name
-- that separately, because it is a claim about a DIFFERENT statement —
-- the leaf the assembly spends at the door — and a receipt has to sit
-- on the statement its rows instantiate.
--
-- WHAT MAKES THEM LOAD-BEARING is the witness rather than a count.
-- `Below` is the decision procedure on the comparison, so the implicit
-- it takes is inhabited exactly when the comparison is TRUE at the
-- point: a fit that failed here would leave the row unsolvable instead
-- of letting it through, which is what a `refl` pin over a hand-written
-- predicate could never promise.  The three points are the widest
-- spread this file has — plain recursion, μ directly inside μ, and a
-- share holding a recursion referenced from inside a second one.
----------------------------------------------------------------------

fitP1 : Confirms (entry-hop-fits progP1 ins₀)
fitP1 = Below

fitP3 : Confirms (entry-hop-fits progP3 ins₀)
fitP3 = Below

fitP12 : Confirms (entry-hop-fits progP12 insMu)
fitP12 = Below
