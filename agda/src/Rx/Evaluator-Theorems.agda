module Rx.Evaluator-Theorems where

open import Data.Bool    using (Bool)
open import Data.Fin     using (Fin)
open import Data.Nat     using (ℕ; suc; _≤_)
open import Data.List    using (List; []; _∷_)
open import Data.List.Relation.Binary.Prefix.Heterogeneous using (Prefix)
open import Data.Unit    using (⊤)
open import Data.Vec     using (lookup)
open import Induction.WellFounded using (Acc)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Prim      using (Id; Tick; Fuel)
open import Rx.Exp       using (Ctx; Closed; Exp; Val; μᵉ; unfoldμ)
open import Rx.Strat-Order using (_≺_)
open import Rx.Evaluator using (Stream; evaluate; Sched; EvalSt;
  dispatchShare)
open import Rx.Slots using (Slot; Slots)




------------------------------------------------------------------
-- Evaluator-level theorems (tested against TS, proven where cheap)
------------------------------------------------------------------

-- evaluate-well-formed (the primitives' half of the sandwich) now
-- lives in Verify-Well-Formed as a real proof over postulated
-- stage lemmas.

-- Two facts worth keeping from the sweep over the evaluator's own laws:
--   * μ SELF-SUBSCRIPTION IS A TYPE ERROR, not merely unreachable — the Δᵍ/Δ
--     gate via `deferᵉ` rules it out at the type level, so no dynamic argument
--     is owed for it.
--   * across a μ unfold, a size counting the whole syntax DOUBLES while
--     `syncSizeᵉ` HOLDS.  That asymmetry is why the descent's third
--     component reads the sync size; `Rx.Exp`'s header also records the
--     refutation of the emissions-per-instant bound.
--
postulate
  -- fuel is arrivals: processing more arrivals only extends the stream
  --
  -- PROBED: the eval-laws battery instantiated this at every canonical
  --   program and found no refutation.  The probe is spent and deleted;
  --   `git show 1f1730e^:agda/probe/Battery-Eval-Laws.agda` recovers its
  --   rows.
  fuel-coherent :
    ∀ {n} {Γ : Ctx n} {t} (f₁ f₂ : Fuel) → f₁ ≤ f₂ →
    (e : Closed Γ t) (ins : Slots Γ) →
    Prefix _≡_ (evaluate f₁ e ins) (evaluate f₂ e ins)

  -- THE DISPATCH COUNTER SUFFICES.  A share boundary re-enters chain
  -- evaluation, so the fan-out is bounded by a counter the evaluator
  -- peels and the arrival seeds at the context size; the clause that
  -- fires when it runs out returns an EMPTY fan-out.  Saturation is
  -- what says that clause is unreachable: past the seed, handing the
  -- dispatch more counter changes nothing, because the recursion is
  -- bottoming out on the registry rather than on the number.
  --
  -- AND IT IS STATED HERE BECAUSE NOTHING ELSE CAN CONSUME IT, which
  -- is the finding rather than a filing choice.  Exhausting the
  -- counter mints no dry event, so every statement about dryness holds
  -- vacuously at the clamp and the rank face passes over it for free —
  -- the truncation is invisible to every obligation the tower states.
  -- The face that would see it is the one comparing this machine to
  -- the spec, and until the clamp is DELETED there is no site whose
  -- body needs this fact to reduce.  A leaf with no consumer is what a
  -- silently-correct clause leaves behind.
  --
  -- AND THE SEED IS THE CONTEXT SIZE BECAUSE THE REAL DESCENT IS THE
  -- TELESCOPE POSITION, which is a fact about the PROGRAM: a shared
  -- slot's definition may name only inputs below it, so a chain
  -- registered on a share sinks only into the root or a strictly later
  -- share.  The registry CARRIES that order in a type — a row's chain
  -- is indexed by the floor its own source dictates, and a sink
  -- constructor demands its index be at least that floor — so the lift
  -- the counter used to stand in for is discharged by construction and
  -- the run cannot mint a row that violates it.  What is left is the
  -- DESCENT: the counter falls by one per boundary while the floor
  -- rises to the sink's own position, and nothing yet ties the two, so
  -- the clamp is unreachable only once the recursion is measured on the
  -- floor rather than on the number.
  --
  -- PROBED: `Probed.Dispatch-Saturates` — a three-slot telescope whose
  --   every share reads the one below it, so a dispatch at the middle
  --   share re-enters a dispatch.  LOAD-BEARING on the half that could
  --   have made the rows vacuous: an equality between two runs of one
  --   machine goes green wherever the machine ignores the parameter, so
  --   the counter is shown to be READ — the emit lengths at one and at
  --   two come back different, the clamp demonstrably truncating when
  --   the seed is short.  NOT covered, and it is the risky half: the
  --   nest is TWO boundaries deep against a context of three, so the
  --   seed is exercised where it is slack and never where it binds.
  --   Breadth is ruled out by reading the dispatch rather than by a row
  --   — the peel is once per BOUNDARY and every admitted chain is handed
  --   the counter the fan-out itself entered at — so depth is the only
  --   axis that can outrun the seed.
  --
  -- PROBED: `Probed.Sink-Floor` — the same machine at the DEEPEST nest a
  --   context of four admits, which is the half the receipt above says it
  --   did not reach.  The staircase runs one, two, three and then three
  --   again, so the counter is read all the way down and STOPS one below
  --   the seed, and the statement holds at the seed, above it, and at the
  --   middle rung.
  --   NOT covered: one arrival, shares reading their predecessor
  --   directly, and a registry one chain wide at every rung — so nothing
  --   here reaches a cancelled registration, a completing share, or a
  --   fan-out of breadth two.
  dispatch-saturates :
    ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {τ} (ac : Acc _≺_ τ)
      (g : ℕ) → n ≤ g →
    ∀ (id : Id) (now : Tick) (i : Fin n)
      (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
      (sd : Sched Γ) (st : EvalSt e) →
    dispatchShare {e = e} ac g id now i vals fin sd st
      ≡ dispatchShare {e = e} ac (suc g) id now i vals fin sd st

  -- causality: agreeing slot prefixes (scripted arrivals before tick
  -- k; shared defs, carrying no scripts, must agree outright) give
  -- agreeing output prefixes
  truncateIn : ∀ {n} {Γ : Ctx n} {k t} → Tick → Slot Γ k t → Slot Γ k t
  emittedBefore : ∀ {n} {Γ : Ctx n} {t} → Tick → Stream Γ t → Stream Γ t

  causality :
    ∀ {n} {Γ : Ctx n} {t} (k : Tick) (fuel : Fuel)
      (e : Closed Γ t) (ins₁ ins₂ : Slots Γ) →
    (∀ i → truncateIn k (ins₁ i) ≡ truncateIn k (ins₂ i)) →
    emittedBefore k (evaluate fuel e ins₁)
      ≡ emittedBefore k (evaluate fuel e ins₂)

  -- μ laws
  --
  -- PROBED: the same battery ran this law beside the one above, at the
  --   same programs, with no refutation.  The probe is spent and
  --   deleted; `git show 1f1730e^:agda/probe/Battery-Eval-Laws.agda`
  --   recovers its rows.
  μ-unfold :
    ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel)
      (e : Exp Γ (t ∷ []) [] [] t) (ins : Slots Γ) →
    evaluate fuel (μᵉ e) ins ≡ evaluate fuel (unfoldμ e) ins

  μ-guarded :   -- k arrivals force ≤ k unfoldings (syntactic, via deferᵉ gate)
    ∀ {n} {Γ : Ctx n} {t} (k : Fuel)
      (e : Exp Γ (t ∷ []) [] [] t) (ins : Slots Γ) →
    evaluate k (μᵉ e) ins ≡ evaluate k (unfoldμ e) ins

  -- deferᵉ's temporal law — NOT YET STATABLE, honestly.  The intent
  -- ("stream of (deferᵉ e) ≈ stream of e with ticks +1") needs two
  -- pieces that do not exist as DEFINITIONS today, only as postulated
  -- abstractions or nowhere at all:
  --   (1) a tick per emission.  InstEmit's fields are events, instant,
  --       source, kind (Rx.Prim) — no Tick.  The arrival's
  --       tick is threaded through subscribeE/foldPath internally
  --       (Arrival.tick, Rx.Evaluator; consumed at foldPath's call
  --       site, Rx.Evaluator) and discarded before it reaches
  --       Stream.  So there is no way, today, to read "the tick of
  --       this emit" back off `evaluate`'s result — the same gap
  --       `causality`'s `emittedBefore` runs into below.
  --   (2) the "≈" itself.  The comment's hedge ("because the body's
  --       ids are re-minted") wants an equivalence up to id renaming,
  --       but no relation of that shape exists in the codebase.  One
  --       was postulated once (`Rx.Time-Theorems._≈ˢ_`) and deleted as
  --       an unconsumed abstract Set: borrowing such a thing relocates
  --       the vacuity rather than fixing it, so it has to be DEFINED.
  -- Stating this for real needs new machinery (a defined tick-trace or
  -- ticked-emit variant, plus a defined — not postulated — renaming
  -- equivalence), which is a design call, not a leaf-module fix. Left
  -- as ⊤ on purpose: an honest gap, not a claim.
  defer-shift :
    ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ) →
    ⊤

