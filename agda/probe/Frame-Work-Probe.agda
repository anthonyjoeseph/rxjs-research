------------------------------------------------------------------
-- THE FRAME-WORK PROBE: is a subscribe frame's work ENTRY-DETERMINED?
--
-- Gates the round-3 restatement (walk-hyps-round3 in
-- Verify-Budget-Sufficient).  Round 3 replaces walkCap's d-index with
-- an entry measure G, and round3-anchor-indexed-absurd proves G may
-- not be allowed to depend on the store anchor — so hopDᵉ's scan
-- clause, whose exponent IS the anchor,
--
--     hopDᵉ V (scanᵉ f z e) = (2 + pmᵗ V 0 f) ^ V * (…)
--
-- has to be re-indexed onto something fixed at entry.  The claim that
-- would justify re-indexing it: a scan folds at most as many times per
-- frame as emissions arrive, and per-frame emission counts are fixed
-- by the program's syntax rather than by how big the store has grown.
--
-- The sharpest known amplifier is the DEEPENING SCAN — an obs-typed
-- accumulator that re-wraps itself on every fold and is then unwrapped
-- by a *All.  Every number below is `refl`-checked against the real
-- evaluator, so they are the machine's, not an estimate.
--
-- WHAT IT FINDS.  The frame work IS entry-determined, and it is an
-- ITERATED EXPONENTIAL in the syntactic nesting depth.  Both halves
-- matter.  The first is what round 3 needs: the fold count is the
-- source's payload count, and that bottoms out in `ofᵉ` list lengths.
-- The second kills the tempting shortcut of reading Ω as a frame
-- budget — Ω is a per-NODE width, and the frame total is Ω-to-the-
-- depth.  A 2-wide program delivers 126 payloads in one frame here.
------------------------------------------------------------------
module Frame-Work-Probe where

open import Data.Nat  using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; sum; map)
open import Data.Vec  using () renaming ([] to []ᵛ)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (InstEmit; InstEvent; value; init; close; handoff;
                           complete)
open import Rx.Exp  using (Ctx; Closed; Tm; Fn; natᵗ; obs; _×ᵗ_;
                           ofᵉ; mergeAllᵉ; scanᵉ;
                           varᵗ; nat̂; fstᵗ; strmᵗ; syncSizeᵉ)
open import Rx.Evaluator using (evaluate; Slots)
open import Rx.Hop-Depth using (hopDᵉ)
open import Verify-Budget-Sufficient using (ofWᵉ)

------------------------------------------------------------------
-- counting: how many payloads did a run actually deliver
------------------------------------------------------------------

evVals : ∀ {A : Set} → List (InstEvent A) → ℕ
evVals []               = 0
evVals (value _ ∷ es)   = suc (evVals es)
evVals (init _ ∷ es)    = evVals es
evVals (close _ _ ∷ es) = evVals es
evVals (handoff _ ∷ es) = evVals es
evVals (complete ∷ es)  = evVals es

countVals : ∀ {A : Set} → List (InstEmit A) → ℕ
countVals ems = sum (map (λ em → evVals (InstEmit.events em)) ems)

------------------------------------------------------------------
-- the programs.  NO INPUTS AT ALL — every number below comes from the
-- syntax, so nothing can be blamed on a script
------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ᵛ

ins : Slots Γ₀
ins ()

-- a scan's bound variable is the PAIR (acc , x); the accumulator is
-- its first projection
accV : Tm Γ₀ [] [] (obs natᵗ ×ᵗ natᵗ ∷ []) (obs natᵗ)
accV = fstᵗ (varᵗ (here refl))

-- ONE copy: acc ↦ mergeAll (of [acc]).  Each fold adds exactly one hop
-- edge and no width, so the payload count reads the FOLD COUNT
wrap1 : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
wrap1 = strmᵗ (mergeAllᵉ (ofᵉ (accV ∷ [])))

-- TWO copies: acc ↦ mergeAll (of [acc, acc]).  Each fold adds one hop
-- edge and DOUBLES the emissions, so the payload count reads the
-- accumulator's DEPTH off the run
wrap2 : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
wrap2 = strmᵗ (mergeAllᵉ (ofᵉ (accV ∷ accV ∷ [])))

seed : Tm Γ₀ [] [] [] (obs natᵗ)
seed = strmᵗ (ofᵉ (nat̂ 7 ∷ []))

src2 : Closed Γ₀ natᵗ
src2 = ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ [])

src3 : Closed Γ₀ natᵗ
src3 = ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ [])

prog₀ : Closed Γ₀ natᵗ                    -- three folds, one payload each
prog₀ = mergeAllᵉ (scanᵉ wrap1 seed src3)

prog₁ : Closed Γ₀ natᵗ                    -- three folds, accₖ carries 2^k
prog₁ = mergeAllᵉ (scanᵉ wrap2 seed src3)

-- TWO syntactic levels: the inner run's payloads ARE the outer scan's
-- folds.  This is the amplification test — if a fold count can ever be
-- store-driven rather than syntax-driven, it shows up here
prog₂ : Closed Γ₀ natᵗ
prog₂ = mergeAllᵉ (scanᵉ wrap2 seed (mergeAllᵉ (scanᵉ wrap2 seed src2)))

------------------------------------------------------------------
-- THE MEASUREMENTS
------------------------------------------------------------------

-- (0) the fold count IS the source's payload count, and for a literal
-- source that is the ofᵉ list's LENGTH.  Three folds, one payload each
_ : countVals (evaluate 20 prog₀ ins) ≡ 3
_ = refl

-- (1) the same three folds read through a doubling wrap: 2 + 4 + 8.
-- The exponent is the fold count, and the fold count is the literal
-- list's length — syntax, with no store quantity anywhere in it
_ : countVals (evaluate 20 prog₁ ins) ≡ 14
_ = refl

-- (2) AND THE AMPLIFICATION.  A two-element literal, nested twice: the
-- inner level delivers 2 + 4 = 6, so the outer scan folds six times and
-- delivers 2 + 4 + 8 + 16 + 32 + 64.  Entry-determined — and a tower in
-- the nesting depth.  (This one is expensive to check; see the
-- frame-work-probe target's note in the Makefile.)
_ : countVals (evaluate 20 prog₂ ins) ≡ 126
_ = refl

------------------------------------------------------------------
-- Ω IS NOT A FRAME BUDGET.  prog₂'s width seed is 2 — every ofᵉ in it
-- has at most two elements — while its frame delivers 126 payloads.
-- Anything that reads `oneShotBurst events ≤ 3 + Ω` as a bound on a
-- FRAME's emissions rather than on a NODE's is off by an iterated
-- exponential.  Pinned here because round 3's work index has to be
-- built out of exactly these quantities, and this is the trap.
------------------------------------------------------------------

om-is-not-a-frame-budget : ofWᵉ prog₂ ≡ 2
om-is-not-a-frame-budget = refl

-- nor is the syntax: 32 sync nodes produced those 126 payloads.  The
-- gap is not in the program, it is in the run
_ : syncSizeᵉ prog₂ ≡ 32
_ = refl

------------------------------------------------------------------
-- AND THE POINT OF ALL OF IT: hopD's scan allowance is charged at the
-- STORE ANCHOR, and the runs above never come near it.  hopDᵉ V prog₁
-- is suc (3 ^ V) — a three-to-the-store-bound allowance for an
-- accumulator that actually reached depth 3.  V is sizeBudgetAt, a
-- tower of 2s, so this is not a loose constant but an unbounded one,
-- and round3-anchor-indexed-absurd is precisely the price of leaving
-- it there.  The charge MOVES with the anchor while the run does not:
------------------------------------------------------------------

_ : hopDᵉ 0 prog₁ ≡ 2
_ = refl

_ : hopDᵉ 1 prog₁ ≡ 4
_ = refl

_ : hopDᵉ 2 prog₁ ≡ 10
_ = refl

------------------------------------------------------------------
-- WHAT THIS PROBE DOES NOT SHOW, stated so it is not over-read: that
-- NO program anywhere has store-driven frame work.  Three structural
-- facts carry that, and all three are read off Rx/Exp.agda's datatype
-- rather than measured:
--
--   · WIDTHS ARE SYNTAX-FIXED.  `ofᵉ` takes a literal `List (Tm …)`,
--     `strmᵗ` is Tm's only obs introduction, and there is no
--     obs-concatenation constructor anywhere in Exp.  Substitution
--     plugs values INTO list elements; nothing appends elements.  So a
--     node's emission width is the width written in the program.
--
--   · A SYNC FRAME HAS NO μ FEEDBACK.  `μᵉ` binds into Δᵍ, `varᵉ`
--     needs `t ∈ Δ`, and `deferᵉ : Exp Γ [] (Δᵍ ++ Δ) Θ t → …` is the
--     only constructor moving Δᵍ into Δ — and it crosses a tick.  A
--     frame cannot re-enter its own μ, which is why the counts above
--     terminate in the syntax instead of running away.
--
--   · SHARE RE-ENTRY IS U-CAPPED.  A second arrival at a slot finds it
--     connected and does not re-walk the def (the connect descent,
--     sharedConnect-unconn).
--
-- Together those say the per-frame fold count is a function of the
-- program; the measurements say what that function looks like.
-- Neither is a proof — the proof is the re-indexed hopD's own
-- induction, which is what Step 2 writes.
------------------------------------------------------------------
