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
-- hypothesis about reachability: `chainDepth` reads a chain's own
-- remaining-hop content off its frames, and `hopFits` compares that
-- against the reading of the program those frames belong to.  Both
-- sides are computable, so the premise is instantiable at concrete
-- registries and the statement above it is refutable rather than
-- merely unproven — which is how the fit's previous shape died.
------------------------------------------------------------------

------------------------------------------------------------------
-- THE CHAIN IS READ BY REPLAYING THE TERM READING ALONG IT, AND THAT
-- IS WHAT MAKES THE TWO SIDES ONE QUANTITY RATHER THAN TWO.  A chain
-- is a CONTINUATION, walked once per value, so its frames compose
-- rather than nest; but composing them is not the same as reading them
-- APART.  The expression measure plugs a source's reading into the
-- template it feeds, so a body that never mentions its bound variable
-- never reads it — the measure SEES a discard.  A measure that reads
-- each template in isolation cannot, and charges a discarded template
-- in full.
--
-- So the walk here carries a reading and hands each frame what the
-- frame above it produced, spending the TERM READING'S OWN step at
-- every frame rather than a second arithmetic beside it: a `map-f` and
-- a `scan-f` plug, a `thru-outer` flattens, and nothing else moves the
-- quantity.  A frame the term measure would never have produced is
-- then the only way the two can part, which is exactly the content the
-- statements below want — they are about chains a cascade has
-- lengthened, not about chains the entry built.
--
-- `thru-outer` is the one frame that pays, because it is the one that
-- subscribes what it is handed, and a `from-inner` is its counterpart
-- LEAVING an inner rather than entering one — which is why the edge
-- sits on exactly one of the two.
--
-- REFUTED: `Refuted.Hop-Sum` — the predecessor measure read every
--   frame's template at the EMPTY environment and ADDED along the
--   path.  Two maps that ignore what they are given, each returning an
--   observable one level deep, under one flattener: the sum charged
--   one, one and the edge against a term reading of two, and the fit
--   was `3 ≤ 2` at the door.  The witness states that arithmetic
--   locally, so it goes on saying which form is dead whatever is
--   carried here.
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
open import Data.Nat using (ℕ; _⊔_; _≤_)
open import Data.Product using (_×_; _,_; proj₂)

open import Rx.Prim using (Source)
open import Rx.Exp using (Ctx; Closed)
open import Rx.Hop-Depth using (Rd₃; ε; mapStep; flatten; hopOf; depthᵉ)
open import Rx.Slot-Read using (slotRd)
open import Rx.Evaluator using (Path; root; share-sink; _↠_; map-f; scan-f;
  take-f; from-inner; thru-outer; Chain; RegId; Sched; EvalSt)

------------------------------------------------------------------
-- A CHAIN'S OWN HOP CONTENT.
------------------------------------------------------------------

-- THE PAYLOAD ENTERS AT ZERO, AND ONLY THE PAYLOAD DOES.  The variable
-- the FIRST frame's template binds stands for the value about to
-- arrive, whose own reading the fit charges on the other side and which
-- therefore cancels; entering the walk at zero is what makes that
-- cancellation exact instead of leaving the payload counted twice.
-- Every frame below the first is handed what the frame above it
-- produced, which is the whole difference from the summing measure the
-- module header records.
--
-- A `scan-f` IS PLUGGED AT ITS SOURCE AND NOT AT ITS ACCUMULATOR, which
-- is a gap and is named here rather than hidden.  The term reading
-- binds a fold's step variable to the JOIN of the accumulator's reading
-- and the source's, and a frame carries no seed — the accumulator lives
-- in the store.  That is the store obligation the block below already
-- owes, arriving one level down: what is read here is one refold
-- against the arriving value, which is what the frame itself fixes.
chainRd : ∀ {n} {Γ : Ctx n} {s t} (ψ : Fin n → Rd₃) →
          Path Γ s t → Rd₃ → Rd₃
chainRd ψ root                    p = p
chainRd ψ (share-sink i)          p = p
chainRd ψ (map-f fn ↠ κ)          p = chainRd ψ κ (mapStep ψ ε p fn)
chainRd ψ (scan-f fn nid ↠ κ)     p = chainRd ψ κ (mapStep ψ ε p fn)
chainRd ψ (take-f nid ↠ κ)        p = chainRd ψ κ p
chainRd ψ (from-inner op a i ↠ κ) p = chainRd ψ κ p
-- THE EDGE: this frame subscribes what it is handed
chainRd ψ (thru-outer op nid ↠ κ) p = chainRd ψ κ (flatten p)

chainDepth : ∀ {n} {Γ : Ctx n} {s t} (ψ : Fin n → Rd₃) →
             Path Γ s t → ℕ
chainDepth ψ c = hopOf (chainRd ψ c (0 , 0 , 0))

-- the worst chain the registry holds
regsDepth : ∀ {n} {Γ : Ctx n} {t} (ψ : Fin n → Rd₃) →
            List (RegId × Source × Chain Γ t) → ℕ
regsDepth ψ []                  = 0
regsDepth ψ ((rid , src , c) ∷ r) =
  chainDepth ψ (proj₂ c) ⊔ regsDepth ψ r

------------------------------------------------------------------
-- BOTH SIDES ARE NOW THE SAME QUANTITY, AND THAT IS WHAT THIS
-- STATEMENT IS FOR.  The left side prices what a chain's frames can
-- still reach; the right the reading of the program those frames were
-- built from.  The right side used to be a counter seeded off SIZE,
-- and nothing related the two: every refuted seeding route had one
-- shape, the run growing where the seed merely doubled.  The
-- evaluator's rank IS a depth reading now, so what is left here is a
-- structural comparison in one currency — a statement about the
-- machine's own registry rather than a bridge between two measures.
--
-- WHAT IS STILL OWED IS THE STORE, NOT THE RANK.  The arrival re-seeds
-- at the ⊔ of the payload's reading and the store's own, and both are
-- denominated in this currency; what is not is the relation between a
-- stored accumulator and the term it was folded from, which is where
-- the remaining obligation sits.
------------------------------------------------------------------

------------------------------------------------------------------
-- THE FIT, AND ITS ENVIRONMENT IS PINNED RATHER THAN QUANTIFIED.  The
-- measure reads ψ at `input` and nowhere else, so a caller free to
-- choose ψ can choose the constant zero — and that reading is refuted:
-- an obs-typed shared slot's def emits values of positive hop, which a
-- subscription connecting to that slot receives.  `slotRd` is the
-- honest environment, computed off the schedule's own telescope, so it
-- is not a caller's to choose: a premise satisfiable at a reading
-- nobody runs is not a premise about this run.  There is no second
-- parameter left to pin, which is what the iterated fold clause
-- bought — the statement now depends on the schedule and the program
-- and on nothing the machine picks.
------------------------------------------------------------------

hopFits : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} →
          Sched Γ → EvalSt e → Set
hopFits {e = e} sched st =
  let ψ = slotRd (Sched.slots sched) in
  regsDepth ψ (EvalSt.registry st) ≤ depthᵉ ψ e
