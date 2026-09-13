-- THE FAN-OUT'S HOP OBLIGATION AT A SHARE — `share-chain-hop` says
-- that every chain the share admits carries no more flatteners than
-- the bound it is entered under affords, one conjunct per admitted
-- registration, each read at the state the fold threads into it.  It
-- is the arrival door's own claim moved to the share's registry, and
-- it is what the sink arm reduces to now that the dispatch's fold is a
-- body.

-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.

-- THE LOAD-BEARING ROWS instantiate at programs where `Rst = stHop ψ
-- st > 0`: `oneProg` (one observable-accumulator scan consumer) and
-- `thriceProg` (three identical ones).  Both have `Rst = 1` at the
-- subscribe state, so the join the chains are held under is genuinely
-- read off the store rather than handed in.  The `stOut` digit records
-- the store depth AFTER the dispatch, confirming the fan-out's write
-- happened and was priced, and the `nRegs` digit confirms the premise
-- recursed over a non-empty list rather than landing on its `⊤` arm —
-- which is the one way a row here could read green having asserted
-- nothing at all.

-- THE `valsHop ψ natᵗ vals` CONJUNCT IS ALWAYS ZERO here, because the
-- dispatched values are natural numbers and `rdᵛ ψ natᵗ _ = 0 , 0` by
-- definition.  So `Rin = 0` everywhere and each conjunct reads as a
-- bare flattener count against the join.  A fan-out over
-- observable-valued slots would put a positive figure on the left.

-- THE DEGENERATE CONTROL is `quietProg`, whose three consumers are
-- plain-number scans: `Rst = 0` at subscribe and `stOut = 0` after
-- dispatch, so the join is nought and a chain carrying ANY flattener
-- would refute there.  It separates the hop count from the writing.

-- WHAT IS NOT COVERED: observable-valued share slots (where `Rin > 0`);
-- completing dispatches (`fin = true`); a spent counter (the
-- `dispatchShare sf zero` clamp, which the sink's body closes by
-- reduction and which no hop premise is read at); and store writes from
-- EARLIER cascade steps — the dispatch here is at the fresh-subscribe
-- state, so `Rst` equals what the subscription left and no prior
-- instant has deepened it.

-- TARGET: share-chain-hop @0d85b2
module Probed.Sink-Dry where

open import Data.Bool using (Bool; false)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Induction.WellFounded using (Acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (cold; after_,_)
open import Rx.Exp using (Ctx; Closed; Fn; Tm; natᵗ; obs; _×ᵗ_; strmᵗ;
  ofᵉ; scanᵉ; mergeAllᵉ; input; nat̂; fstᵗ; varᵗ)
open import Rx.Slots using (Slots; scripted; shared)
open import Rx.Strat-Order using (_≺_)
open import Rx.Hop-Depth using (Rd₃)
open import Rx.Slot-Read using (slotRd)
open import Rx.Evaluator using (EvalSt; Sched; root; shareAdmit; subscribeE; rootWitness; rootTri; sched-init; st-init;
  dispatchShare; stHop)
open import Verify-Rank-Sufficient.Path-Fits using (share-chain-hop)
open import Probed.Apparatus using (Confirms; Below)

----------------------------------------------------------------------
-- THE HARNESS.  Slot zero is a cold script delivering twice after the
-- subscribe frame; slot one is a SHARE over it, so every consumer of
-- slot one registers on one source.
----------------------------------------------------------------------

Γ₂ : Ctx 2
Γ₂ = natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

ins : Slots Γ₂
ins zero       = scripted (cold [] (after 0 , 9 ∷ after 0 , 8 ∷ []))
ins (suc zero) = shared (input zero)

----------------------------------------------------------------------
-- THE WRITING CONSUMER.  A fold whose accumulator is an OBSERVABLE, so
-- the node its subscribe installs reads positive and the fan-out's
-- per-delivery write lands somewhere the store reading can see.
--
-- AND THE WRAPPING RATE IS ONE, WHICH IS NOT A WEAKENING.  What makes
-- a row here load-bearing is that the store reads POSITIVE before the
-- dispatch and that the dispatch's write lands, and the entering
-- reading comes off the SEED rather than off the fold function — so a
-- deeper fold raises only `stOut`, at a normalisation cost the
-- dispatch pays in full at every one of the admitted chains.
----------------------------------------------------------------------

deepen : Fn Γ₂ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
deepen = strmᵗ (mergeAllᵉ nothing (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ [])))

seed : Tm Γ₂ [] [] [] (obs natᵗ)
seed = strmᵗ (mergeAllᵉ nothing
         (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ [])))

cons3 : Tm Γ₂ [] [] [] (obs natᵗ)
cons3 = strmᵗ (mergeAllᵉ nothing (scanᵉ deepen seed (input (suc zero))))

-- a consumer that fans out WITHOUT WRITING: the node its subscribe
-- installs reads nought and stays there however many values arrive
flatCons : Tm Γ₂ [] [] [] (obs natᵗ)
flatCons = strmᵗ (scanᵉ (fstᵗ (varᵗ (here refl))) (nat̂ 0) (input (suc zero)))

oneProg thriceProg quietProg : Closed Γ₂ natᵗ
oneProg    = mergeAllᵉ nothing (ofᵉ (cons3 ∷ []))
thriceProg = mergeAllᵉ nothing (ofᵉ (cons3 ∷ cons3 ∷ cons3 ∷ []))
quietProg  = mergeAllᵉ nothing (ofᵉ (flatCons ∷ flatCons ∷ flatCons ∷ []))

----------------------------------------------------------------------
-- THE INSTRUMENT.  The subscribe state, where the chains have
-- registered their accumulators but no arrival has yet run.
----------------------------------------------------------------------

entry : (e : Closed Γ₂ natᵗ) → Sched Γ₂ × EvalSt e
entry e =
  let (_ , sched , st) =
        subscribeE (rootWitness e ins) e root 0 0
          (sched-init e ins) (st-init e)
  in sched , st

----------------------------------------------------------------------
-- THE DISPATCH POINT, parameterised by program and nat value.
-- The two bounds are set to the TIGHTEST values: `Rin = 0` (nat
-- payloads read nought by construction) and `Rst = stHop ψ st` (the
-- exact store depth at entry).  Gas is the context depth, which is
-- the bound the harness seeds at `chainStep`.
----------------------------------------------------------------------

module Ap (e : Closed Γ₂ natᵗ) (v : ℕ) where

  ψ : Fin 2 → Rd₃
  ψ = slotRd ins

  ac : Acc _≺_ (rootTri e ins)
  ac = rootWitness e ins

  sd : Sched Γ₂
  sd = proj₁ (entry e)

  st : EvalSt e
  st = proj₂ (entry e)

  gas : ℕ
  gas = 2

  vals : List ℕ
  vals = v ∷ []

  fin : Bool
  fin = false

  Rin : ℕ
  Rin = 0

  Rst : ℕ
  Rst = stHop ψ st

  nRegs : ℕ
  nRegs = length (shareAdmit (suc zero) (EvalSt.registry st))

  stOut : ℕ
  stOut = stHop ψ (proj₂ (proj₂ (dispatchShare ac gas 0 0 (suc zero) vals fin sd st)))

  -- radix 1000, low digit first: registration count, store in, store
  -- out — the first confirms the fan-out delivered to a non-empty
  -- list, the second and third report the store before and after the
  -- dispatch
  packed : ℕ
  packed = nRegs + 1000 * Rst + 1000000 * stOut

----------------------------------------------------------------------
-- THE THREE POINTS.  `One3` and `Three3` are LOAD-BEARING: their store
-- depth is positive at subscribe and the dispatch writes the fold
-- accumulators deeper.  `Quiet3` is the DEGENERATE CONTROL: its store
-- depth is zero at subscribe and the flat consumers never write.
----------------------------------------------------------------------

module One3   = Ap oneProg 3
module Three3 = Ap thriceProg 3
module Quiet3 = Ap quietProg 3

----------------------------------------------------------------------
-- BOTH SIDES PINNED.  These figures come from the evaluator and are
-- the probe's own non-degeneracy check: the `nRegs` digit confirms the
-- dispatch delivered to a real list, the `Rst` digit confirms the
-- store had depth before the dispatch ran, and the `stOut` digit
-- confirms the dispatch's writes landed.  A row at a point where all
-- three read nought says nothing about the fan-out.
----------------------------------------------------------------------

one3-is : One3.packed ≡ 2001001
one3-is = refl

three3-is : Three3.packed ≡ 2001003
three3-is = refl

quiet3-is : Quiet3.packed ≡ 3
quiet3-is = refl

----------------------------------------------------------------------
-- THE TARGET AT THE THREE POINTS.  The one hypothesis is decided
-- rather than assumed — `Rin ≤ Rst` is `0 ≤ Rst` — so what remains is
-- the recursion over the admitted list, one flattener count per
-- registration read against the join with that chain's own state.
----------------------------------------------------------------------

sinkOne3 : Confirms
  (share-chain-hop One3.ac One3.gas 0 0 (suc zero) One3.ψ
     One3.Rin One3.Rst Below One3.vals One3.fin One3.sd One3.st)
sinkOne3 = Below , tt

sinkThree3 : Confirms
  (share-chain-hop Three3.ac Three3.gas 0 0 (suc zero) Three3.ψ
     Three3.Rin Three3.Rst Below Three3.vals Three3.fin Three3.sd Three3.st)
sinkThree3 = Below , Below , Below , tt

sinkQuiet3 : Confirms
  (share-chain-hop Quiet3.ac Quiet3.gas 0 0 (suc zero) Quiet3.ψ
     Quiet3.Rin Quiet3.Rst Below Quiet3.vals Quiet3.fin Quiet3.sd Quiet3.st)
sinkQuiet3 = Below , Below , Below , tt
