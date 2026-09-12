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
-- remaining-hop content off its frames, and `hopFits` compares that
-- against the reading of the program those frames belong to.  Both
-- sides are computable, so the premise is instantiable at concrete
-- registries and the statement above it is refutable rather than
-- merely unproven — which is how the fit's previous shape died.
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
-- WHY THE FIT MENTIONS NEITHER THE PAYLOAD NOR THE STORE, WHICH IS
-- WHERE ITS PREDECESSOR DIED.  The rank an arrival gets is seeded at
-- the program's reading PLUS the join of the payload's own reading
-- with the store's nesting, and the cost of delivering that arrival is
-- the payload's reading plus what the chain still has to flatten.  The
-- payload therefore appears on both sides and cancels; a fit that
-- charged it on the left while naming only the store's half on the
-- right was charging the instant that QUEUED a value for the hops the
-- instant that POPS it is separately granted.
------------------------------------------------------------------

------------------------------------------------------------------
-- AND THAT SHAPE IS REFUTED RATHER THAN MERELY LOOSE, WHICH IS WHY THE
-- CANCELLATION IS NOT AN OPTIMISATION.  The shortfall it leaves is
-- exactly one and does not move with the program: at the door, on plain
-- recursion, on μ directly inside μ, and on a share holding a
-- recursion, the pending payload read one, two and three against a
-- chain reading of one throughout.  A run whose pending payload IS the
-- recursion reads that payload at the program's own figure by
-- construction, so the two sides grow together and the gap never
-- closes — no seed, no slack and no third conjunct reaches it, because
-- the quantity is on the wrong side of the comparison rather than too
-- small.  What survives the cancellation is the statement above, which
-- names neither half: the worst chain the registry holds is walkable
-- inside the reading of the program that built it.
------------------------------------------------------------------
module Verify-Rank-Sufficient.Hop where

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; suc; _+_; _⊔_; _≤_)
open import Data.Product using (_×_; _,_; proj₂)

open import Rx.Prim using (Source)
open import Rx.Exp using (Ctx; Closed)
open import Rx.Hop-Depth using (hopDᵉ; hopDᵗ)
open import Rx.Slot-Hop using (slotHop)
open import Rx.Evaluator using (Path; root; share-sink; _↠_; map-f; scan-f;
  take-f; from-inner; thru-outer; Chain; RegId; Sched; EvalSt)

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
-- BOTH SIDES ARE NOW THE SAME QUANTITY, AND THAT IS WHAT THIS
-- STATEMENT IS FOR.  The left side prices a template's REUSE of its
-- argument — a map multiplies, a scan raises to the sweep — so it
-- bounds how deep what a program EMITS can get.  The right side used
-- to be a counter seeded off SIZE, and nothing related the two: every
-- refuted seeding route had one shape, the run multiplying where the
-- seed merely doubled.  The evaluator's rank IS a hop reading now, so
-- what is left here is a structural comparison between a chain's
-- remaining hop content and the reading of the program that built it —
-- one currency, and a statement about the machine's own registry
-- rather than a bridge between two measures.
--
-- WHAT IS STILL OWED IS THE STORE, NOT THE RANK.  The arrival re-seeds
-- at the ⊔ of the payload's reading and the store's NESTING, and only
-- the first of those is denominated in this currency; reading the
-- store's half alone names a rank no larger than the one an arrival
-- actually gets, which is the safe direction for a hypothesis.
------------------------------------------------------------------

------------------------------------------------------------------
-- THE FIT, AND ITS ENVIRONMENT IS PINNED RATHER THAN QUANTIFIED.  The
-- measure reads η at `input` and nowhere else, so a caller free to
-- choose η can choose the constant zero — and that reading is refuted:
-- an obs-typed shared slot's def emits values of positive hop, which a
-- subscription connecting to that slot receives.  `slotHop` is the
-- honest environment, computed off the schedule's own telescope, and
-- the store bound it is taken at is the schedule's own, so neither is
-- a caller's to choose: a premise satisfiable at a reading nobody runs
-- is not a premise about this run.
------------------------------------------------------------------

hopFits : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} →
          Sched Γ → EvalSt e → Set
hopFits {e = e} sched st =
  let V = Sched.storeBound sched
      η = slotHop V (Sched.slots sched) in
  regsHopD V η (EvalSt.registry st) ≤ hopDᵉ V η e
