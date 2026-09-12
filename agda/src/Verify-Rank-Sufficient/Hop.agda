------------------------------------------------------------------
-- THE TIE BETWEEN A REGISTRATION'S FRAMES AND WHAT IT CAN STILL DO.
--
-- The drain leaf was refuted twice, and both witnesses turn on the
-- same absence: a chain is a `Path` typed by the context and the root
-- type alone, so nothing relates the functions its frames carry to the
-- run they belong to, and the coherence record constrains the
-- registry's counts and element types without ever mentioning a frame.
-- A `map-f` therefore hands back a tower of any depth while every
-- quantity the entry reads holds still.
--
-- What is stated here is the missing quantity rather than a new
-- hypothesis about reachability: `chainHopD` reads a chain's own
-- remaining-hop content off its frames, and `hopFits` compares that,
-- plus the depth the schedule can deliver into it, against the rank an
-- arrival's entry seeds.  Both sides are computable, so the premise is
-- instantiable at concrete registries and the statement above it is
-- refutable rather than merely unproven.
------------------------------------------------------------------

------------------------------------------------------------------
-- WHY THE CHAIN'S READING IS ADDITIVE WHERE THE MEASURE MULTIPLIES.
-- A chain is a CONTINUATION, walked once per value, so its frames
-- compose rather than nest: each contributes what its own template can
-- reach, and only a flattener contributes an edge.  The multiplier in
-- the expression measure prices a SUBSTITUTION — one template's body
-- plugged into another's — and that has already happened by the time a
-- value reaches a frame.  Pricing it twice would make the tie a bound
-- nothing satisfies.
--
-- `thru-outer` is the one frame that pays, because it is the one that
-- subscribes what it is handed, and a `from-inner` is its counterpart
-- LEAVING an inner rather than entering one — which is why the edge
-- sits on exactly one of the two.
------------------------------------------------------------------

------------------------------------------------------------------
-- WHY THE FIT READS THE STORE'S NESTING AND NOT THE ARRIVAL'S.  The
-- rank an arrival actually gets is seeded at the join of the payload's
-- own nesting with the store's, so reading the store's half alone
-- names a SMALLER rank than any arrival will see.  The premise is
-- therefore stronger than the run needs, which is the safe direction
-- for a hypothesis, and it costs no quantification over arrivals that
-- have not happened yet.
------------------------------------------------------------------
module Verify-Rank-Sufficient.Hop where

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; suc; _+_; _^_; _⊔_; _<_)
open import Data.Product using (_×_; _,_; proj₂)

open import Rx.Prim using (Source)
open import Rx.Exp using (Ctx; Closed; sizeᵉ)
open import Rx.Slots using (slotsSize)
open import Rx.Hop-Depth using (hopDᵗ; hopDᵛ)
open import Rx.Slot-Hop using (slotHop)
open import Rx.Evaluator using (Path; root; share-sink; _↠_; map-f; scan-f;
  take-f; from-inner; thru-outer; Chain; RegId; LiveSource; Sched; EvalSt;
  stNest)

------------------------------------------------------------------
-- A CHAIN'S OWN HOP CONTENT.
------------------------------------------------------------------

chainHopD : ∀ {n} {Γ : Ctx n} {s t} (V : ℕ) (η : Fin n → ℕ) →
            Path Γ s t → ℕ
chainHopD V η root                   = 0
chainHopD V η (share-sink i)         = 0
chainHopD V η (map-f fn ↠ κ)         = hopDᵗ V η fn + chainHopD V η κ
chainHopD V η (scan-f fn nid ↠ κ)    = hopDᵗ V η fn + chainHopD V η κ
chainHopD V η (take-f nid ↠ κ)       = chainHopD V η κ
chainHopD V η (from-inner op a i ↠ κ) = chainHopD V η κ
-- THE EDGE: this frame subscribes what it is handed
chainHopD V η (thru-outer op nid ↠ κ) = suc (chainHopD V η κ)

-- the worst chain the registry holds
regsHopD : ∀ {n} {Γ : Ctx n} {t} (V : ℕ) (η : Fin n → ℕ) →
           List (RegId × Source × Chain Γ t) → ℕ
regsHopD V η []                  = 0
regsHopD V η ((rid , src , c) ∷ r) =
  chainHopD V η (proj₂ c) ⊔ regsHopD V η r

------------------------------------------------------------------
-- THE DEEPEST VALUE THE SCHEDULE CAN STILL DELIVER.
------------------------------------------------------------------

pendHopD : ∀ {n} {Γ : Ctx n} (V : ℕ) (η : Fin n → ℕ) (l : LiveSource Γ) → ℕ
pendHopD V η l = go (LiveSource.pending l)
  where
  go : List _ → ℕ
  go []             = 0
  go ((tk , v) ∷ p) = hopDᵛ V η (LiveSource.elemTy l) v ⊔ go p

liveHopD : ∀ {n} {Γ : Ctx n} (V : ℕ) (η : Fin n → ℕ) →
           List (LiveSource Γ) → ℕ
liveHopD V η []       = 0
liveHopD V η (l ∷ ls) = pendHopD V η l ⊔ liveHopD V η ls

------------------------------------------------------------------
-- THE TWO SIDES ARE DENOMINATED DIFFERENTLY, AND THAT IS THE OPEN
-- QUESTION UNDER THIS STATEMENT.  The left side prices a template's
-- REUSE of its argument — a map multiplies, a scan raises to the
-- sweep — so it bounds how deep what a program EMITS can get.  The
-- right side is the evaluator's own rank, seeded off SIZE, and the
-- companion measure the seed is actually built from is the SYNTACTIC
-- nesting, which this tree proves bounded by that size.  Nothing
-- relates the two, and every refuted seeding route has the same
-- shape: the run multiplies where the seed merely doubles.
--
-- So preservation here is an obligation BETWEEN TWO CURRENCIES rather
-- than a structural fact, and the alternative is to stop comparing
-- them.  Let the hop edge's well-founded descent be the carried
-- reading of the value being subscribed: a flattener's reading is a
-- `suc` of its source's by definition, and the inner came from that
-- source, so the descent is definitional.  Then no counter exists to
-- exhaust, the guard's zero clause is unreachable and deletable, and
-- this statement is not needed at all.  What that route costs is the
-- burst walk's strengthened return type — which is owed either way,
-- and is the whole of what it would then be spent on.
------------------------------------------------------------------

------------------------------------------------------------------
-- THE FIT, AND ITS ENVIRONMENT IS PINNED RATHER THAN QUANTIFIED.  The
-- measure reads η at `input` and nowhere else, so a caller free to
-- choose η can choose the constant zero — and that reading is refuted:
-- an obs-typed shared slot's def emits values of positive hop, which a
-- subscription connecting to that slot receives.  `slotHop` is the
-- honest environment, computed off the schedule's own telescope, and
-- naming it here is what stops the premise being satisfiable by a
-- reading of the program nobody runs.
------------------------------------------------------------------

hopFits : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} →
          ℕ → Sched Γ → EvalSt e → Set
hopFits {e = e} V sched st =
  let η = slotHop V (Sched.slots sched) in
  liveHopD V η (Sched.live sched) + regsHopD V η (EvalSt.registry st)
    < 2 ^ (sizeᵉ e + slotsSize (Sched.slots sched) + stNest st)
