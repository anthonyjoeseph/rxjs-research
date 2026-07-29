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

open import Data.Nat  using (ℕ; zero; suc; _+_; _≤ᵇ_)
open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; sum; map)
open import Data.Vec  using () renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Fin  using (Fin) renaming (zero to fz)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (InstEmit; InstEvent; value; init; close; handoff;
                           complete; ObservableInput; hot; Timed; after_,_)
open import Rx.Exp  using (Ctx; Closed; Tm; Fn; natᵗ; obs; _×ᵗ_; input;
                           ofᵉ; mergeAllᵉ; scanᵉ; μᵉ; deferᵉ; varᵉ;
                           varᵗ; nat̂; fstᵗ; strmᵗ; syncSizeᵉ)
open import Rx.Evaluator using (evaluate; Slots; Slot; scripted; shared)
open import Rx.Hop-Depth using (hopDᵉ)
open import Rx.Frame-Width using (outWᵉ)
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
accV : ∀ {n} {Γ : Ctx n} → Tm Γ [] [] (obs natᵗ ×ᵗ natᵗ ∷ []) (obs natᵗ)
accV = fstᵗ (varᵗ (here refl))

-- ONE copy: acc ↦ mergeAll (of [acc]).  Each fold adds exactly one hop
-- edge and no width, so the payload count reads the FOLD COUNT
wrap1 : ∀ {n} {Γ : Ctx n} → Fn Γ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
wrap1 = strmᵗ (mergeAllᵉ (ofᵉ (accV ∷ [])))

-- TWO copies: acc ↦ mergeAll (of [acc, acc]).  Each fold adds one hop
-- edge and DOUBLES the emissions, so the payload count reads the
-- accumulator's DEPTH off the run
wrap2 : ∀ {n} {Γ : Ctx n} → Fn Γ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
wrap2 = strmᵗ (mergeAllᵉ (ofᵉ (accV ∷ accV ∷ [])))

-- THREE copies, to separate the tower's base from its height: k
-- accumulator occurrences must widen the base by k and leave the height
-- alone
wrap3 : ∀ {n} {Γ : Ctx n} → Fn Γ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
wrap3 = strmᵗ (mergeAllᵉ (ofᵉ (accV ∷ accV ∷ accV ∷ [])))

seed : ∀ {n} {Γ : Ctx n} → Tm Γ [] [] [] (obs natᵗ)
seed = strmᵗ (ofᵉ (nat̂ 7 ∷ []))

src2 : Closed Γ₀ natᵗ
src2 = ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ [])

src3 : Closed Γ₀ natᵗ
src3 = ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ [])

prog₀ : Closed Γ₀ natᵗ                    -- three folds, one payload each
prog₀ = mergeAllᵉ (scanᵉ wrap1 seed src3)

prog₁ : Closed Γ₀ natᵗ                    -- three folds, accₖ carries 2^k
prog₁ = mergeAllᵉ (scanᵉ wrap2 seed src3)

prog₁′ : Closed Γ₀ natᵗ                   -- three folds, accₖ carries 3^k
prog₁′ = mergeAllᵉ (scanᵉ wrap3 seed src3)

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

-- (1′) DUPLICATION WIDENS THE BASE, NOT THE HEIGHT.  Same three folds,
-- three accumulator occurrences instead of two: 3 + 9 + 27 where prog₁
-- gave 2 + 4 + 8.  The exponent — the accumulator's depth, and so the
-- tower's height — is unmoved at 3; only the base went 2 ↦ 3, by the
-- syntactic occurrence count.  This is the occs0 lesson in its
-- quantitative form, and it is what a plug MULTIPLIER has to read
_ : countVals (evaluate 20 prog₁′ ins) ≡ 39
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
-- ACROSS INSTANTS: THE HEIGHT IS FIXED BY THE SYNTAX.  This is the
-- fact reachCap needs, and it is the one that says there is room.
--
-- A scan accumulator persists, so it keeps deepening for the whole run,
-- and the obvious worry is that it towers once per instant — which is
-- what sizeBudgetAt assumes (its height is (4 + sz)·(1 + id), growing
-- with the instant).  It does not.  One scan folds once per arrival, so
-- its accumulator gains exactly ONE wrap per instant: depth linear in
-- the instant count, base of a single exponential.
--
-- What DOES tower is syntactic nesting — prog₂ above, where one extra
-- *All level takes 6 payloads to 126.  So a reachable observable's size
-- is a tower whose HEIGHT is the program's scan/*All chain depth and
-- whose BASE grows linearly in the instant count.  sizeBudgetAt's
-- height grows per instant; this does not.  That gap is the headroom
-- round 3's reset caps have to live in.
------------------------------------------------------------------

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ᵛ []ᵛ

-- three arrivals, one instant apart
ins₁ : Slots Γ₁
ins₁ fz = scripted (hot ((after 0 , 1) ∷ (after 0 , 2) ∷ (after 0 , 3) ∷ []))

progT : Closed Γ₁ natᵗ
progT = mergeAllᵉ (scanᵉ wrap2 seed (input fz))

-- 2 + 4 + 8, one fold per instant — the SAME total as prog₁'s three
-- synchronous folds.  Spreading the folds across instants buys the
-- accumulator no extra depth, so instants add linearly where syntax
-- multiplies
_ : countVals (evaluate 40 progT ins₁) ≡ 14
_ = refl

------------------------------------------------------------------
-- CROSS-TICK FEEDBACK: THE HEIGHT IS INSTANT-FREE.  The sharpest test
-- of the fixed-height shape, and the one that could have killed it.
--
-- μᵉ binds into Δᵍ and deferᵉ is the sole gate moving Δᵍ into Δ, so a
-- self-reference NECESSARILY crosses a tick.  `ticker` is that loop: it
-- emits one value now and reruns itself next tick, forever, with no
-- scripted input at all.  Feeding it to the doubling wrap makes the
-- accumulator deepen once per tick and then unwraps it, so the payload
-- count reads the depth directly.
--
-- If a defer loop could compound depth — if instant k's ACCUMULATED
-- state could drive instant k+1's fold count — the height would climb
-- per instant and reachCap as shaped would be dead.  It cannot, and the
-- reason is structural: unfoldμ substitutes the ORIGINAL closed μ for
-- the Δᵍ variable, so the deferred self-reference re-subscribes a FRESH
-- copy of the pipeline with a fresh accumulator.  State crosses a tick
-- only as VALUES through the store, and each tick applies one fixed
-- syntactic wrap.  μ recursion is syntactic re-subscription, not state
-- feedback.
--
-- Measured, over three fuels: 14, 30, 62 — that is 2^(N+1) − 2, one
-- extra wrap per tick and nothing more.  A single exponential in the
-- instant count; the tower's height never moves.
------------------------------------------------------------------

ticker : Closed Γ₀ natᵗ
ticker = μᵉ (mergeAllᵉ (ofᵉ ( strmᵗ (ofᵉ (nat̂ 1 ∷ []))
                            ∷ strmᵗ (deferᵉ (varᵉ (here refl))) ∷ [])))

feedback : Closed Γ₀ natᵗ
feedback = mergeAllᵉ (scanᵉ wrap2 seed ticker)

_ : countVals (evaluate 2 feedback ins) ≡ 14
_ = refl

_ : countVals (evaluate 3 feedback ins) ≡ 30
_ = refl

_ : countVals (evaluate 4 feedback ins) ≡ 62
_ = refl

------------------------------------------------------------------
-- A SHARE CROSSING COSTS WHAT SYNTACTIC NESTING COSTS.  The other half
-- of cross-chain composition, and the routing most likely to compound
-- if anything does: a share is the one place a chain is reached other
-- than by descending into it syntactically.
--
-- The same inner chain is written twice — once as a `shared` slot def
-- reached through `input`, once inline — under the same outer scan.
-- Both deliver 6.  A share crossing raises the height by exactly one,
-- like every other *All level, and compounds nothing.
--
-- And re-entry is free: TWO references to the same slot, merged, also
-- deliver 6, not 12 and not 36.  The second arrival finds the slot
-- connected and does not re-walk the def — sharedConnect-unconn's
-- content, measured rather than assumed.  So a share adds to neither
-- the tower's height nor its base.
------------------------------------------------------------------

src1 : ∀ {n} {Γ : Ctx n} → Closed Γ natᵗ
src1 = ofᵉ (nat̂ 1 ∷ [])

Γₛ : Ctx 1
Γₛ = natᵗ ∷ᵛ []ᵛ

insₛ : Slots Γₛ
insₛ fz = shared (mergeAllᵉ (scanᵉ wrap2 seed src1))

progₛ : Closed Γₛ natᵗ                    -- composition through a SHARE
progₛ = mergeAllᵉ (scanᵉ wrap2 seed (input fz))

progₙ : Closed Γₛ natᵗ                    -- the syntactic twin
progₙ = mergeAllᵉ (scanᵉ wrap2 seed (mergeAllᵉ (scanᵉ wrap2 seed src1)))

progₛ₂ : Closed Γₛ natᵗ                   -- TWO subscribers to one slot
progₛ₂ = mergeAllᵉ (scanᵉ wrap2 seed
           (mergeAllᵉ (ofᵉ (strmᵗ (input fz) ∷ strmᵗ (input fz) ∷ []))))

_ : countVals (evaluate 20 progₛ insₛ) ≡ 6
_ = refl

_ : countVals (evaluate 20 progₙ insₛ) ≡ 6
_ = refl

_ : countVals (evaluate 20 progₛ₂ insₛ) ≡ 6
_ = refl

------------------------------------------------------------------
-- THE GATE: Rx.Frame-Width's measures must DOMINATE every run above.
--
-- This is what keeps the measure honest.  outWᵉ is pure syntax — it
-- never looks at the store — so each of these is instant to check, and
-- a draft that under-counts any measured run is refuted on the spot.
-- The plug slopes got their shape from exactly this: a single-slope
-- draft cannot even state the *All clause, and an occurrence count
-- under-counts the duplication case.
------------------------------------------------------------------

_ : (3   ≤ᵇ outWᵉ 2 ins prog₀)  ≡ true
_ = refl

_ : (14  ≤ᵇ outWᵉ 2 ins prog₁)  ≡ true
_ = refl

_ : (39  ≤ᵇ outWᵉ 2 ins prog₁′) ≡ true
_ = refl

_ : (126 ≤ᵇ outWᵉ 2 ins prog₂)  ≡ true
_ = refl

-- and through a share, where `input` is not structural and the measure
-- spends slot fuel instead
_ : (6 ≤ᵇ outWᵉ 2 insₛ progₛ)  ≡ true
_ = refl

_ : (6 ≤ᵇ outWᵉ 2 insₛ progₙ)  ≡ true
_ = refl

_ : (6 ≤ᵇ outWᵉ 2 insₛ progₛ₂) ≡ true
_ = refl

------------------------------------------------------------------
-- REFUTATION: THE HEIGHT IS **NOT** FIXED BY THE SYNTAX.
--
-- Everything above measured step functions whose plug lands under
-- `mergeAllᵉ`/`ofᵉ`, where a width is multiplied by a constant.  Put the
-- plug in an inner scanᵉ's SOURCE and it stops being a factor and
-- becomes the FOLD COUNT — that is, the tower's EXPONENT:
--
--   deepScan  acc ↦ mergeAll (scan wrap2 seed (mergeAll (of [acc])))
--
-- Now each outer fold re-subscribes the inner scan, and the inner scan
-- folds once per payload the accumulator carries.  Writing wₖ for the
-- accumulator's width after k outer folds, the inner scan folds wₖ times
-- with doubling widths, so
--
--     w₀ = 1,   wₖ₊₁ = 2^(wₖ + 1) − 2      →   1, 2, 6, 126, 2^127 − 2
--
-- MEASURED, against the real evaluator:
--
--   two folds (literal source)    →  8  =  w₁ + w₂  =  2 + 6
--   ONE arrival, scripted         →  2
--   TWO arrivals, scripted        →  8
--
-- The last two are the ones that matter.  The fold count grows by one
-- per INSTANT — that is exactly what the defer-loop measurement above
-- established — so wₖ is a tower whose HEIGHT grows with the instant
-- count.  A shape with height fixed by the syntax and base linear in the
-- instants cannot bound it.
--
-- WHY THE EARLIER MEASUREMENTS DID NOT SEE THIS.  They are not wrong,
-- they are incomplete.  progₛ and prog₂ each cross from one chain into
-- another ONCE, and there the heights add.  Here the crossing is
-- RE-ENTERED once per fold, and per-fold re-entry compounds where a
-- single crossing adds.  "Heights add past the first crossing" — the
-- one thing this probe listed as asserted rather than measured — is
-- precisely what fails.
--
-- CONSEQUENCE, recorded and NOT patched around: Verify-Budget-Sufficient's
-- reachCap is too small as defined, and reach-covers is false as stated.
-- The fix is a shape decision, not an implementation detail.
------------------------------------------------------------------

-- Θ-generic so the same template can sit under an inner scan's binder
accVᵍ : ∀ {n} {Γ : Ctx n} {Θ} → Tm Γ [] [] (obs natᵗ ×ᵗ natᵗ ∷ Θ) (obs natᵗ)
accVᵍ = fstᵗ (varᵗ (here refl))

wrap2ᵍ : ∀ {n} {Γ : Ctx n} {Θ} → Tm Γ [] [] ((obs natᵗ ×ᵗ natᵗ) ∷ Θ) (obs natᵗ)
wrap2ᵍ = strmᵗ (mergeAllᵉ (ofᵉ (accVᵍ ∷ accVᵍ ∷ [])))

seedᵍ : ∀ {n} {Γ : Ctx n} {Θ} → Tm Γ [] [] Θ (obs natᵗ)
seedᵍ = strmᵗ (ofᵉ (nat̂ 7 ∷ []))

-- the plug lands in an inner scan's SOURCE
deepScan : ∀ {n} {Γ : Ctx n} → Fn Γ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
deepScan = strmᵗ (mergeAllᵉ (scanᵉ wrap2ᵍ seedᵍ (mergeAllᵉ (ofᵉ (accVᵍ ∷ [])))))

progD : Closed Γ₀ natᵗ
progD = mergeAllᵉ (scanᵉ deepScan seedᵍ src2)

-- 2 + 6, where a non-compounding shape predicts 2 + 4
_ : countVals (evaluate 20 progD ins) ≡ 8
_ = refl

-- AND ACROSS INSTANTS, which is the refutation proper: one more arrival
-- buys one more level of the tower, not one more wrap
insD₁ insD₂ : Slots Γ₁
insD₁ fz = scripted (hot ((after 0 , 1) ∷ []))
insD₂ fz = scripted (hot ((after 0 , 1) ∷ (after 0 , 2) ∷ []))

progDT : Closed Γ₁ natᵗ
progDT = mergeAllᵉ (scanᵉ deepScan seedᵍ (input fz))

_ : countVals (evaluate 40 progDT insD₁) ≡ 2
_ = refl

_ : countVals (evaluate 40 progDT insD₂) ≡ 8
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
--   · (This slot used to say additivity past one crossing was merely
--     unmeasured.  It is now REFUTED — see the deepScan section above.
--     Per-fold re-entry compounds where a single crossing adds.)
--
-- Together those say the per-frame fold count is a function of the
-- program; the measurements say what that function looks like.
-- Neither is a proof — the proof is the re-indexed hopD's own
-- induction, which is what Step 2 writes.
------------------------------------------------------------------
