-- THE WALK FACE AS A TYPE — every statement the collapsed walk is
-- written over, and nothing that proves anything about them.  The face
-- itself, its clause leaves and its dispatch live one module up.
--
-- WHY IT IS SEPARATE, and it is a checking-cost argument rather than a
-- taste one.  The walk's dispatch is one genuine mutual cycle, and a
-- mutual block is an indivisible checking unit: every focused check of
-- any member re-pays for whatever else shares the module.  These
-- telescopes are large, they are pure Set-valued abbreviation, and
-- nothing in the cycle needs them RE-CHECKED to check itself — an
-- import is enough.  Moving them out is therefore free to the proof and
-- takes the per-member iteration loop back under its budget, which is
-- the difference between grinding a clause in seconds and in a minute.
--
-- WHAT BELONGS HERE: a definition that mentions no lemma — the shared
-- telescopes, the record of proven edges the dispatch is narrowed over,
-- the gas peel, and the clause leaves' STATEMENTS, which name no lemma
-- and so cannot be part of any cycle by construction.  The leaves
-- THEMSELVES are real bodies and live with the arms.  Anything with a proof
-- body that the cycle consumes belongs in the shelf module beside this
-- one; anything IN the cycle belongs with the dispatch.
--
-- Consumers name what they need from here directly, so the move shows
-- up in their import lists.

module Verify-Budget-Sufficient.Walk-Level.Statement where

open import Data.Bool    using (T; true; false)
open import Data.Nat     using (ℕ; suc; _+_; _*_; _^_; _≤_; _<_)
open import Data.List    using (List; []; _∷_; _++_; map)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive)
open import Data.Bool.ListAction using (any)
open import Data.Fin     using (Fin; toℕ)
open import Data.Vec     using (lookup)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; sym)

open import Rx.Prim      using (Tick; Id; Source; init; value; close; complete; exhausted; subscribe; _at_from_as_; Gas; g0;
  gs; gasPad; towerℕ)
open import Rx.Exp       using (obs; _×ᵗ_; Ctx; Closed; Val; Exp; Tm; Fn; inputsBelowᵉ; sizeᵉ; sizeᵗ; sizeᵛ; syncSizeᵉ;
  shellSizeᵉ; innerᵉ; input; mapᵉ; scanᵉ; μᵉ; unfoldμ; applyFn; evalTm)
open import Rx.Frame-Width using (dWᵉ)
open import Rx.Hop-Depth using (hopDᵉ; hopDᵗ; hopDᵛ; pmᵗ)
open import Rx.Slot-Hop  using (slotHop)
open import Rx.Evaluator using (Sched; EvalSt; memberSource; Path; _↠_; subscribeE; sharedConnect; scan-st; scan-f;
  splitBurst; hasDry; dryEvent; opIterD; sLvlD; sIterD; sizeAt; sLvlD-suc; opIterD-suc; widAt;
  installNode; mintNode)
open import Rx.Slots using (shared; Slot; Slots; slotsSize)

-- the wet stratum: INV?, dBound, hasAtLeast, regsLen?, pathLen, the gas
-- edges, sizeCapAt, capsAt/capsH/frameStep/Caps (via .Caps), the
-- Keeps ring, and every companion the core is narrowed over
open import Verify-Budget-Sufficient.Measures using
  (_hasAtLeast_; burstB?; burstHopD?; dBound; fnCapᵉ; hopR; INV?; pathB?;
   pathLen; regsLen?; sizeBudgetAt; unconn)
open import Verify-Budget-Sufficient.Keeps-Ring using
  (Keeps)
-- the caps face: only the five predicates the statement reads there
open import Verify-Budget-Sufficient.Caps-Face.Part1 using
  (burstCaps?; burstCount?; capsOK?; pathSz?; slotsCaps?)
open import Verify-Budget-Sufficient.Caps-Nest using
  (nest)
-- the chain-charge algebra subscribeE-caps' own *All head spends
-- the transformer monotonicity/inflation family, cited directly by the
-- loop faces' ceiling conversions
open import Verify-Budget-Sufficient.Caps
  using (sLvlD-mono; opIterD-infl; fIterD-infl; Caps; frameStep)
-- proven projections and per-emit plumbing off the caps push face —
-- pieces, never the face itself (the wet twin re-walks its skeleton
-- so both halves share one witness)
open import Verify-Budget-Sufficient.Hop-Spine-Face
  using (burstHopSpnH?)
open import Verify-Budget-Sufficient.Hop-Spine-Push
  using (scanAccSpn?)
open import Verify-Budget-Sufficient.Caps-Depth
  using (depthE)

-- `input i` WITH ITS Exp INDICES PINNED.  Written bare in a top-level
-- signature the guarded/value/parked contexts are metavariables — only
-- `Closed` forces them to `[]`, and WalkStmt gets that for free from its
-- own `b : Closed Γ u`.  A signature stating the shape itself has no
-- such binder, so the six conjuncts mentioning the expression each raise
-- an unsolved meta.  Spent by every arm that narrows to the input shape
-- (`b ≡ inputᶜ i →`).
inputᶜ : ∀ {n} {Γ : Ctx n} (i : Fin n) → Exp Γ [] [] [] (lookup Γ i)
inputᶜ i = input i


-- THE WALK FACE AND ITS CORE, as types — named once so that neither
-- the face nor the assembly that consumes it has to retype the
-- statement.
--
-- WalkStmt ABSTRACTS THE STATEMENT OVER b, so that each clause of the
-- face's dispatch can state its own obligation as `WalkStmt (ctor …)`
-- in two lines instead of retyping the forty-line telescope — the arms
-- (.Parts, .Arms) are exactly those instances, and a wrong
-- specialisation is a type error rather than a drifted copy.  b
-- therefore moves to the FRONT of WalkLevel's telescope (the dispatch
-- matches on it); its two application sites pass it first.
-- THE TAIL, SHARED — everything from κ onwards, with the gas and the
-- numeric prefix as PARAMETERS.  Factored out so one statement can be read
-- two ways: with the gas INSIDE the telescope (WalkStmt, whose argument
-- order is unchanged, so its call sites are untouched) and with the gas
-- FIXED UP FRONT (WalkStmtAt).  The second is the only way to name a walk
-- face at a given fuel: WalkStmt's conclusion is gas-indexed — a Σ about
-- `subscribeE g b κ …` — so "walkFace at the peeled fuel" is not a term of
-- type WalkLevel at all, it needs a type of its own.
WalkTail : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u} →
  Gas → Closed Γ u → Caps → (Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j : ℕ) → Set
WalkTail {n} {Γ} {t} {e} {u} g b c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j =
  ∀ (κ : Path Γ u t)
    (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
    -- caps prelims, subscribeE-caps' own
    2 ≤ Caps.cSize c →
    1 ≤ Caps.cReg c →
    Caps.cReg c ≤ Caps.cSize c →
    Sched.slots sched ≡ sl →
    slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
    slotsSize sl ≤ Caps.cSize c →
    capsOK? (frameStep j c) sched st ≡ true →
    sizeᵉ b ≤ Caps.cSize (frameStep j c) →
    dWᵉ n sl b ≤ Caps.cWid (frameStep j c) →
    pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
    suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
    nest b sl (EvalSt.connectedShares st) ≤ bud →
    suc (sizeᵉ b) ≤ ops →
    depthE g b κ bid now sched st ≤ dep →
    -- the wet half, at the level (the E-into-j collapse: the wet
    -- predicate's B position IS the level's size cap)
    INV? Ψ (Caps.cSize (frameStep j c)) sched st ≡ true →
    fnCapᵉ b ≤ Ψ →
    pathB? (Caps.cSize (frameStep j c)) Ψ κ ≡ true →
    -- the reset-anchor pins: the hop measurement index
    -- and rank ARE the reset cap's (refl at the true instantiation,
    -- where F, Ŝ := sizeCapAt e sl (suc id) and R̂ := hopR Ŝ), and the
    -- CEILING — no level this walk can reach outgrows Ŝ, stated as one
    -- frameStep bound at the free ceiling L̂ plus the face's own budget
    -- under it; call edges convert budgets with the Caps-Chain
    -- descents.  This is the hypothesis GAP 2's ruling (.Wet/Part6)
    -- always intended and hop-step-needs proves NECESSARY: without a
    -- syncSize-to-Ŝ link no r-drop can fund an inner walk, and the
    -- level receipts are the only syncSize bound in the telescope.
    2 ≤ Ŝ →
    F ≡ Ŝ →
    R̂ ≡ hopR Ŝ →
    Caps.cSize (frameStep L̂ c) ≤ Ŝ →
    opIterD (Caps.cSize c) (Caps.cWid c) dep bud ops j ≤ L̂ →
    -- the dry half, unchanged: demand at the ENTRY-COMPUTABLE reset
    -- caps, never at any ledger
    dBound Ŝ R̂ (unconn sl (EvalSt.connectedShares st))
           (hopDᵉ F (slotHop F sl) b) (syncSizeᵉ b) ≤ G →
    g hasAtLeast suc G →
    -- the length ledger, ℓ FREE (wet-ell-absurd killed the Ŝ pin)
    pathLen κ + G ≤ ℓ →
    regsLen? ℓ (EvalSt.registry st) ≡ true →
    let r = subscribeE g b κ bid now sched st
    in Σ ℕ λ j′ →
       (capsOK? (frameStep (j + j′) c) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
       × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
       × (burstCount? (frameStep (j + j′) c) (proj₁ r) ≡ true)
       × (j + j′ ≤ opIterD (Caps.cSize c) (Caps.cWid c) dep bud ops j)
       × (INV? Ψ (Caps.cSize (frameStep (j + j′) c))
               (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
       × (burstB? (Caps.cSize (frameStep (j + j′) c)) Ψ (proj₁ r) ≡ true)
       -- the hop conjunct rides the HONEST environment (Rx.Slot-Hop):
       -- `slotHop F sl i` is slot i's own def's hop, so the bound at
       -- `input i` is the def's hop rather than 0 — which is what the
       -- refutation (Demand-Probe series W) showed it has to be, and
       -- slotHop-fix is the equation the input clause spends.
       × (burstHopD? F (slotHop F sl) (hopDᵉ F (slotHop F sl) b)
                     (proj₁ r) ≡ true)
       × (hasDry (proj₁ r) ≡ false)
       × (regsLen? ℓ (EvalSt.registry (proj₂ (proj₂ r))) ≡ true)

WalkStmt : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u} → Closed Γ u → Set
WalkStmt {n} {Γ} {t} {e} {u} b =
  ∀ (c : Caps) (Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j : ℕ) (g : Gas) →
  WalkTail {e = e} g b c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j

-- the same statement with the gas pinned: a walk face AT a fuel
WalkStmtAt : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u} → Gas → Closed Γ u → Set
WalkStmtAt {n} {Γ} {t} {e} {u} g b =
  ∀ (c : Caps) (Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j : ℕ) →
  WalkTail {e = e} g b c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j

-- WalkStmt WITH THE regsLen? CONJUNCT REMOVED — the shape a clause's leaf
-- takes once its length-ledger conjunct is actually proven, so that the
-- proof plugs into a real body instead of being asserted inside a bigger
-- postulate.  It exists once, here, because every clause that registers
-- splits the same way; walk-defer is the first.  The hypothesis list is
-- WalkTail's verbatim — read the comments there, they are not repeated.
WalkTail⁻ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u} →
  Gas → Closed Γ u → Caps → (Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j : ℕ) → Set
WalkTail⁻ {n} {Γ} {t} {e} {u} g b c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j =
  ∀ (κ : Path Γ u t)
    (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
    2 ≤ Caps.cSize c →
    1 ≤ Caps.cReg c →
    Caps.cReg c ≤ Caps.cSize c →
    Sched.slots sched ≡ sl →
    slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
    slotsSize sl ≤ Caps.cSize c →
    capsOK? (frameStep j c) sched st ≡ true →
    sizeᵉ b ≤ Caps.cSize (frameStep j c) →
    dWᵉ n sl b ≤ Caps.cWid (frameStep j c) →
    pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
    suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
    nest b sl (EvalSt.connectedShares st) ≤ bud →
    suc (sizeᵉ b) ≤ ops →
    depthE g b κ bid now sched st ≤ dep →
    INV? Ψ (Caps.cSize (frameStep j c)) sched st ≡ true →
    fnCapᵉ b ≤ Ψ →
    pathB? (Caps.cSize (frameStep j c)) Ψ κ ≡ true →
    2 ≤ Ŝ →
    F ≡ Ŝ →
    R̂ ≡ hopR Ŝ →
    Caps.cSize (frameStep L̂ c) ≤ Ŝ →
    opIterD (Caps.cSize c) (Caps.cWid c) dep bud ops j ≤ L̂ →
    dBound Ŝ R̂ (unconn sl (EvalSt.connectedShares st))
           (hopDᵉ F (slotHop F sl) b) (syncSizeᵉ b) ≤ G →
    g hasAtLeast suc G →
    pathLen κ + G ≤ ℓ →
    regsLen? ℓ (EvalSt.registry st) ≡ true →
    let r = subscribeE g b κ bid now sched st
    in Σ ℕ λ j′ →
       (capsOK? (frameStep (j + j′) c) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
       × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
       × (burstCount? (frameStep (j + j′) c) (proj₁ r) ≡ true)
       × (j + j′ ≤ opIterD (Caps.cSize c) (Caps.cWid c) dep bud ops j)
       × (INV? Ψ (Caps.cSize (frameStep (j + j′) c))
               (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
       × (burstB? (Caps.cSize (frameStep (j + j′) c)) Ψ (proj₁ r) ≡ true)
       × (burstHopD? F (slotHop F sl) (hopDᵉ F (slotHop F sl) b)
                     (proj₁ r) ≡ true)
       × (hasDry (proj₁ r) ≡ false)

WalkStmt⁻ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u} → Closed Γ u → Set
WalkStmt⁻ {n} {Γ} {t} {e} {u} b =
  ∀ (c : Caps) (Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j : ℕ) (g : Gas) →
  WalkTail⁻ {e = e} g b c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j


------------------------------------------------------------------
-- SPLITTING THE HOP CONJUNCT OFF THE REST.
--
-- The burstHopD? conjunct is the ONE axis on which the chain clauses
-- differ from each other, and it is the only conjunct in the Σ that
-- mentions neither `j′` nor the caps — so it detaches cleanly, and a
-- clause's remaining eight can be stated (and ground) without it.  That
-- matters because the eight are a DELEGATION to `subscribeE-caps` plus
-- the wet predicates, identical in shape across map / take / scan,
-- while the hop conjunct is where each frame's own ledger lives and
-- where scan is genuinely harder than its siblings:
--
--   · takeᵉ transforms no value, so `hopDᵉ (takeᵉ c e) = hopDᵉ e` and
--     the source's receipt IS the receipt;
--   · mapᵉ applies its fn ONCE per value, so one hopD-applyFn step
--     closes it, and hopD-map-emit (.Measures) is that step, PROVEN;
--   · scanᵉ REFOLDS the accumulator, so the fn's multiplier compounds
--     along the burst and the receipt needs an INVARIANT rather than a
--     step.  Nothing else about scan is harder — it mints no
--     subscription the other chain frames do not, and its caps half is
--     the same delegation theirs is.
--
-- So the split is not scan-specific plumbing: it is where the family's
-- one real difference lives, and `walk-scan` below is the assembly that
-- puts scan's clause back together from the two halves.
------------------------------------------------------------------

-- THE HOP CONJUNCT AT THE FOLD'S OWN EXPONENT — scan only.
--
-- `WalkTailᴴ` asks the burst to sit under ONE number, and for a scan
-- frame that number carries the exponent `F` outright.  Reaching it in
-- one step forces the fold to carry `F` in the exponent from the start,
-- which `Refuted.Hop-Drag` refutes: a step can DEEPEN the accumulator
-- while shrinking its `sizeᵛ`.  So the leaf concludes at each emitted
-- value's OWN SPINE — `spnᵛ`, size along the hop-deepest path, which
-- that step does not decrease — and `walk-scan` below raises the
-- exponent to `F` once, by `spn≤sizeᵛ` against the size receipt the
-- other half already proves.  Everything else is `WalkTailᴴ` verbatim
-- at `b := scanᵉ f z b`.
WalkTailᴴˢ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} →
  Gas → Fn Γ [] [] [] (u ×ᵗ s) u → Tm Γ [] [] [] u → Closed Γ s →
  Caps → (Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j : ℕ) → Set
WalkTailᴴˢ {n} {Γ} {t} {e} {s} {u} g f z b c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j =
  ∀ (κ : Path Γ u t)
    (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
    2 ≤ Caps.cSize c →
    1 ≤ Caps.cReg c →
    Caps.cReg c ≤ Caps.cSize c →
    Sched.slots sched ≡ sl →
    slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
    slotsSize sl ≤ Caps.cSize c →
    capsOK? (frameStep j c) sched st ≡ true →
    sizeᵉ (scanᵉ f z b) ≤ Caps.cSize (frameStep j c) →
    dWᵉ n sl (scanᵉ f z b) ≤ Caps.cWid (frameStep j c) →
    pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
    suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
    nest (scanᵉ f z b) sl (EvalSt.connectedShares st) ≤ bud →
    suc (sizeᵉ (scanᵉ f z b)) ≤ ops →
    depthE g (scanᵉ f z b) κ bid now sched st ≤ dep →
    INV? Ψ (Caps.cSize (frameStep j c)) sched st ≡ true →
    fnCapᵉ (scanᵉ f z b) ≤ Ψ →
    pathB? (Caps.cSize (frameStep j c)) Ψ κ ≡ true →
    2 ≤ Ŝ →
    F ≡ Ŝ →
    R̂ ≡ hopR Ŝ →
    Caps.cSize (frameStep L̂ c) ≤ Ŝ →
    opIterD (Caps.cSize c) (Caps.cWid c) dep bud ops j ≤ L̂ →
    dBound Ŝ R̂ (unconn sl (EvalSt.connectedShares st))
           (hopDᵉ F (slotHop F sl) (scanᵉ f z b))
           (syncSizeᵉ (scanᵉ f z b)) ≤ G →
    g hasAtLeast suc G →
    pathLen κ + G ≤ ℓ →
    regsLen? ℓ (EvalSt.registry st) ≡ true →
    burstHopSpnH? F (slotHop F sl) (pmᵗ F 0 f)
      (hopDᵗ F (slotHop F sl) f + hopDᵗ F (slotHop F sl) z
         + hopDᵉ F (slotHop F sl) b)
      (proj₁ (subscribeE g (scanᵉ f z b) κ bid now sched st)) ≡ true

------------------------------------------------------------------
-- THE SOURCE HALF OF THE SCAN HOP RECEIPT.
--
-- `subscribeE` at a `scanᵉ` does exactly two things: it subscribes the
-- SOURCE under a freshly minted `scan-f` frame, into a state where that
-- frame's node holds `evalTm z`, and then it pushes the resulting burst
-- through the frame.  The second half is now PROVEN — `.Hop-Spine-Push`
-- walks the burst, runs `scanVals` per emit, and carries the node's
-- accumulator across emits — so the leaf is this first half alone.
--
-- Two conjuncts, and the second is the one the push face cannot see:
-- the source subscription may install nodes of its own, and the scan
-- node has to still hold a bounded accumulator when the push begins.
-- `evalTm z` satisfies it by `valHopSpn?-intro` off `hopDᵗ z ≤ BND`;
-- what is owed is that subscribing `b` does not disturb it.
------------------------------------------------------------------
WalkTailᴴˢ⁰ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} →
  Gas → Fn Γ [] [] [] (u ×ᵗ s) u → Tm Γ [] [] [] u → Closed Γ s →
  Caps → (Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j : ℕ) → Set
WalkTailᴴˢ⁰ {n} {Γ} {t} {e} {s} {u} g f z b c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j =
  ∀ (κ : Path Γ u t)
    (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
    2 ≤ Caps.cSize c →
    1 ≤ Caps.cReg c →
    Caps.cReg c ≤ Caps.cSize c →
    Sched.slots sched ≡ sl →
    slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
    slotsSize sl ≤ Caps.cSize c →
    capsOK? (frameStep j c) sched st ≡ true →
    sizeᵉ (scanᵉ f z b) ≤ Caps.cSize (frameStep j c) →
    dWᵉ n sl (scanᵉ f z b) ≤ Caps.cWid (frameStep j c) →
    pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
    suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
    nest (scanᵉ f z b) sl (EvalSt.connectedShares st) ≤ bud →
    suc (sizeᵉ (scanᵉ f z b)) ≤ ops →
    depthE g (scanᵉ f z b) κ bid now sched st ≤ dep →
    INV? Ψ (Caps.cSize (frameStep j c)) sched st ≡ true →
    fnCapᵉ (scanᵉ f z b) ≤ Ψ →
    pathB? (Caps.cSize (frameStep j c)) Ψ κ ≡ true →
    2 ≤ Ŝ →
    F ≡ Ŝ →
    R̂ ≡ hopR Ŝ →
    Caps.cSize (frameStep L̂ c) ≤ Ŝ →
    opIterD (Caps.cSize c) (Caps.cWid c) dep bud ops j ≤ L̂ →
    dBound Ŝ R̂ (unconn sl (EvalSt.connectedShares st))
           (hopDᵉ F (slotHop F sl) (scanᵉ f z b))
           (syncSizeᵉ (scanᵉ f z b)) ≤ G →
    g hasAtLeast suc G →
    pathLen κ + G ≤ ℓ →
    regsLen? ℓ (EvalSt.registry st) ≡ true →
    let (nid , sched₁) = mintNode sched
        r = subscribeE g b (scan-f f nid ↠ κ) bid now sched₁
              (installNode nid (scan-st (evalTm z)) st)
        BND = hopDᵗ F (slotHop F sl) f + hopDᵗ F (slotHop F sl) z
                + hopDᵉ F (slotHop F sl) b
    in (burstHopSpnH? F (slotHop F sl) (pmᵗ F 0 f) BND (proj₁ r) ≡ true)
     × (scanAccSpn? F (slotHop F sl) (pmᵗ F 0 f) BND u nid (proj₂ (proj₂ r)) ≡ true)

------------------------------------------------------------------
-- THE SOURCE WALK'S WHOLE TAIL — the nine-conjunct walk face, taken at
-- the source, under the scan frame, after the seed's own level step.
--
-- WHY THE WHOLE TAIL AND NOT THE ONE CONJUNCT THIS USED TO BE.  Getting
-- to the source costs a fifty-line prologue: the size and the Ψ splits,
-- the seed's eval receipt, the mint, the install, both path receipts at
-- the widened cap, and a twenty-six-argument application of the walk's
-- own induction hypothesis.  That prologue was already being paid in
-- full to extract the hop conjunct ALONE, and the other eight were
-- discarded — while the scan clause's REST face needs exactly those
-- eight.  Stating the tail whole is what stops the prologue from being
-- written twice; the hop projection moves down to the consumer that
-- wants it.
--
-- READ THE CONJUNCTS AS `WalkTail`'s, INSTANTIATED.  They are that
-- statement at the source `b`, under the frame `scan-f f nid ↠ κ`, at
-- the post-install state, and at the level `suc (j + suc (sizeᵗ z))` —
-- and the seed's step is SPELLED OUT rather than existential because
-- `evalSeed-caps`' witness IS `suc (sizeᵗ z)`, definitionally.  That is
-- the same fact the caps twin spends when it hands `op-step-eval` its
-- `s≤s`, so nothing new is being assumed by writing it here.
--
-- AND THE ops COLUMN SITS AT `suc ops`, WHICH IS THE HONEST INDEX.  The
-- clause consumes one ops step before it reaches its source, so this
-- type's own `ops` is the SOURCE's budget and the frame's is one above.
-- Stating it that way is also what removes the spent-budget clause: a
-- hypothesis at `suc ops` cannot be met at zero, so there is no absurd
-- arm to write here.  The arm reappears one level up, at whichever
-- consumer holds the frame's own ops — which is where it belongs.
--
-- THE NODE-TABLE CONJUNCT USED TO SIT HERE, AND IT WAS THE WHOLE RISK.
-- It asked that subscribing `b` under `scan-f f nid ↠ κ` leave node `nid`
-- holding exactly `scan-st (evalTm z)`.  That is now DISCHARGED at the
-- consumer (`walk-scan-source`, .Parts) off `mint-install-survives`
-- (.Node-Fresh), so the statement no longer carries it — a subscribe
-- writes nothing below the `nextNode` watermark it was handed, and the
-- caller minted `nid` below it.  That watermark fact is itself PROVEN
-- there, so nothing under this conjunct is postulated any more.
--
-- WHAT IT IS NOT, kept because the alignment is what made the route look
-- mechanical: the caps face.  `capsOK?` (.Caps-Face/Part1) BOUNDS every
-- node and IDENTIFIES none, so no strengthening of it reaches a claim
-- that a particular nid holds a particular value.
--
-- Nothing about the SPINE appears here.  `walk-scan-source` converts both
-- of its conjuncts to the hereditary form by `burstHopSpnH-intro` and
-- `scanSeed-hopSpn` (.Hop-Spine-Face, both PROVEN), which cost nothing
-- because `hopDᵛ` is a `⊔` over obs-leaves and the exponent is spare
-- room.
------------------------------------------------------------------
WalkTailᴴˢˢ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} →
  Gas → Fn Γ [] [] [] (u ×ᵗ s) u → Tm Γ [] [] [] u → Closed Γ s →
  Caps → (Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j : ℕ) → Set
WalkTailᴴˢˢ {n} {Γ} {t} {e} {s} {u} g f z b c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j =
  ∀ (κ : Path Γ u t)
    (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
    2 ≤ Caps.cSize c →
    1 ≤ Caps.cReg c →
    Caps.cReg c ≤ Caps.cSize c →
    Sched.slots sched ≡ sl →
    slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
    slotsSize sl ≤ Caps.cSize c →
    capsOK? (frameStep j c) sched st ≡ true →
    sizeᵉ (scanᵉ f z b) ≤ Caps.cSize (frameStep j c) →
    dWᵉ n sl (scanᵉ f z b) ≤ Caps.cWid (frameStep j c) →
    pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
    suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
    nest (scanᵉ f z b) sl (EvalSt.connectedShares st) ≤ bud →
    suc (sizeᵉ (scanᵉ f z b)) ≤ suc ops →
    depthE g (scanᵉ f z b) κ bid now sched st ≤ dep →
    INV? Ψ (Caps.cSize (frameStep j c)) sched st ≡ true →
    fnCapᵉ (scanᵉ f z b) ≤ Ψ →
    pathB? (Caps.cSize (frameStep j c)) Ψ κ ≡ true →
    2 ≤ Ŝ →
    F ≡ Ŝ →
    R̂ ≡ hopR Ŝ →
    Caps.cSize (frameStep L̂ c) ≤ Ŝ →
    opIterD (Caps.cSize c) (Caps.cWid c) dep bud (suc ops) j ≤ L̂ →
    dBound Ŝ R̂ (unconn sl (EvalSt.connectedShares st))
           (hopDᵉ F (slotHop F sl) (scanᵉ f z b))
           (syncSizeᵉ (scanᵉ f z b)) ≤ G →
    g hasAtLeast suc G →
    pathLen κ + G ≤ ℓ →
    regsLen? ℓ (EvalSt.registry st) ≡ true →
    let (nid , sched₁) = mintNode sched
        J₀ = suc (j + suc (sizeᵗ z))
        r = subscribeE g b (scan-f f nid ↠ κ) bid now sched₁
              (installNode nid (scan-st (evalTm z)) st)
    in Σ ℕ λ j₁ →
       (capsOK? (frameStep (J₀ + j₁) c)
                (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
       × (burstCaps? (frameStep (J₀ + j₁) c) sl (proj₁ r) ≡ true)
       × (burstCount? (frameStep (J₀ + j₁) c) (proj₁ r) ≡ true)
       × (J₀ + j₁ ≤ opIterD (Caps.cSize c) (Caps.cWid c) dep bud ops J₀)
       × (INV? Ψ (Caps.cSize (frameStep (J₀ + j₁) c))
               (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
       × (burstB? (Caps.cSize (frameStep (J₀ + j₁) c)) Ψ (proj₁ r) ≡ true)
       × (burstHopD? F (slotHop F sl) (hopDᵉ F (slotHop F sl) b)
                     (proj₁ r) ≡ true)
       × (hasDry (proj₁ r) ≡ false)
       × (regsLen? ℓ (EvalSt.registry (proj₂ (proj₂ r))) ≡ true)

-- THE THREE SCAN HALVES ARE GAS-PINNED, AND THAT IS LOAD-BEARING, NOT
-- COSMETIC.  Their assembly (`walk-scan`, .Parts) receives the walk face
-- AT THE SOURCE — `walkFace b` — so the dispatch has to hand it over at
-- the clause's OWN gas: a gas-polymorphic argument can only be supplied
-- as a lambda whose gas binder is unrelated to the clause's, and the
-- termination checker then reads the recursive call's fuel as UNKNOWN and
-- rejects the whole walk group (measured; it takes walk-mu down with it).
-- Pinned, the call is `walkFace b … g …`: fuel equal, source structurally
-- smaller, which is the shape `subscribeAll-walk` already recurses at.
-- Same lesson as `WalkStmtAt` above, arriving from the other clause.
WalkStmtᴴˢˢ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} → Gas →
  Fn Γ [] [] [] (u ×ᵗ s) u → Tm Γ [] [] [] u → Closed Γ s → Set
WalkStmtᴴˢˢ {n} {Γ} {t} {e} {s} {u} g f z b =
  ∀ (c : Caps) (Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j : ℕ) →
  WalkTailᴴˢˢ {e = e} g f z b c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j

WalkStmtᴴˢ⁰ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} → Gas →
  Fn Γ [] [] [] (u ×ᵗ s) u → Tm Γ [] [] [] u → Closed Γ s → Set
WalkStmtᴴˢ⁰ {n} {Γ} {t} {e} {s} {u} g f z b =
  ∀ (c : Caps) (Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j : ℕ) →
  WalkTailᴴˢ⁰ {e = e} g f z b c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j

WalkStmtᴴˢ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} → Gas →
  Fn Γ [] [] [] (u ×ᵗ s) u → Tm Γ [] [] [] u → Closed Γ s → Set
WalkStmtᴴˢ {n} {Γ} {t} {e} {s} {u} g f z b =
  ∀ (c : Caps) (Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j : ℕ) →
  WalkTailᴴˢ {e = e} g f z b c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j

-- WalkStmt WITH THE burstHopD? CONJUNCT REMOVED — the other eight.
WalkTail⁻ᴴ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u} →
  Gas → Closed Γ u → Caps → (Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j : ℕ) → Set
WalkTail⁻ᴴ {n} {Γ} {t} {e} {u} g b c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j =
  ∀ (κ : Path Γ u t)
    (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
    2 ≤ Caps.cSize c →
    1 ≤ Caps.cReg c →
    Caps.cReg c ≤ Caps.cSize c →
    Sched.slots sched ≡ sl →
    slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
    slotsSize sl ≤ Caps.cSize c →
    capsOK? (frameStep j c) sched st ≡ true →
    sizeᵉ b ≤ Caps.cSize (frameStep j c) →
    dWᵉ n sl b ≤ Caps.cWid (frameStep j c) →
    pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
    suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
    nest b sl (EvalSt.connectedShares st) ≤ bud →
    suc (sizeᵉ b) ≤ ops →
    depthE g b κ bid now sched st ≤ dep →
    INV? Ψ (Caps.cSize (frameStep j c)) sched st ≡ true →
    fnCapᵉ b ≤ Ψ →
    pathB? (Caps.cSize (frameStep j c)) Ψ κ ≡ true →
    2 ≤ Ŝ →
    F ≡ Ŝ →
    R̂ ≡ hopR Ŝ →
    Caps.cSize (frameStep L̂ c) ≤ Ŝ →
    opIterD (Caps.cSize c) (Caps.cWid c) dep bud ops j ≤ L̂ →
    dBound Ŝ R̂ (unconn sl (EvalSt.connectedShares st))
           (hopDᵉ F (slotHop F sl) b) (syncSizeᵉ b) ≤ G →
    g hasAtLeast suc G →
    pathLen κ + G ≤ ℓ →
    regsLen? ℓ (EvalSt.registry st) ≡ true →
    let r = subscribeE g b κ bid now sched st
    in Σ ℕ λ j′ →
       (capsOK? (frameStep (j + j′) c) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
       × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
       × (burstCount? (frameStep (j + j′) c) (proj₁ r) ≡ true)
       × (j + j′ ≤ opIterD (Caps.cSize c) (Caps.cWid c) dep bud ops j)
       × (INV? Ψ (Caps.cSize (frameStep (j + j′) c))
               (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
       × (burstB? (Caps.cSize (frameStep (j + j′) c)) Ψ (proj₁ r) ≡ true)
       × (hasDry (proj₁ r) ≡ false)
       × (regsLen? ℓ (EvalSt.registry (proj₂ (proj₂ r))) ≡ true)

-- RECOVERY: `git show 62fb817` restores `WalkTailᴴ`/`WalkStmtᴴ` (the hop
--   conjunct at WalkTail's telescope, bounded by ONE number) and `walk-join`
--   (the generic re-association of the two halves).  They were scan's assembly
--   until the hop half moved to the SPINE exponent, which is scan-specific;
--   another chain clause needing the SAME split at a single bound would want
--   them back verbatim.
--   GAS-FIXED, because the one clause stated at it needs the walk's own
--   INDUCTION HYPOTHESIS beside it and that hypothesis is stated at a fixed
--   gas (`WalkStmtAt`).  The gas-POLYMORPHIC version this replaces had
--   exactly one user and could not have one that closed — all of its
--   conjuncts are assertions about a subscribe that unfolds THROUGH the
--   source's own, so without the induction hypothesis there is nothing to
--   close them with.  `walk-scan-rest` (.Parts) is that user, and it is a
--   real body now.
WalkStmtAt⁻ᴴ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u} →
  Gas → Closed Γ u → Set
WalkStmtAt⁻ᴴ {n} {Γ} {t} {e} {u} g b =
  ∀ (c : Caps) (Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j : ℕ) →
  WalkTail⁻ᴴ {e = e} g b c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j

WalkLevel : Set
WalkLevel = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (b : Closed Γ u) → WalkStmt {e = e} b

-- THE WALK FACE AT A FIXED GAS.  `walkFace` partially applied to a fuel
-- inhabits this — no lambda over the tail is needed, since WalkStmtAt is
-- WalkStmt with exactly the gas argument removed.
WalkLevelAt : Gas → Set
WalkLevelAt g = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (b : Closed Γ u) → WalkStmtAt {e = e} g b

-- one gas step down, total.  In the type of input-wet-core below this is
-- what turns the clause's own gas into the fuel its recursive walk runs at;
-- at `gs fuel` it reduces to `fuel`, which is what makes the recursive call
-- STRUCTURALLY smaller and so visible to the termination checker.
peelGas : Gas → Gas
peelGas g0       = g0
peelGas (gs fuel) = fuel

-- THE 19 ROUTE LEMMAS, RE-HOMED.  They used to hang off
-- `subscribeE-wet-core`'s hypothesis list, from the days when that
-- core walked the gas edges clause by clause.  Assembling the outer
-- face showed it needs NONE of them — it is pure instantiation and
-- lift — while the walk face, which IS the clause-by-clause gas walk,
-- is where every one of them gets spent.  Their ONLY consumer in the
-- repo was that hypothesis list, so re-homing them here is also what
-- keeps them wired.  Set₁ rather than Set: two of them quantify over
-- `{A : Set}` (splitBurst's payload), which lifts the whole core.
WalkLevelCore : Set₁
WalkLevelCore =
    -- mu-edge  (Verify-Budget-Sufficient/Wet/Part6.agda)
    (∀ {n} {Γ : Ctx n} {t} (Ŝ R̂ U : ℕ) (η : Fin n → ℕ)
      (body : Exp Γ (t ∷ []) [] [] t) →
      suc (dBound Ŝ R̂ U (hopDᵉ Ŝ η (unfoldμ body)) (syncSizeᵉ (unfoldμ body)))
        ≤ dBound Ŝ R̂ U (hopDᵉ Ŝ η (μᵉ body)) (syncSizeᵉ (μᵉ body))
     ) →
    -- hop-edge  (Verify-Budget-Sufficient/Wet/Part6.agda)
    (∀ {n} {Γ : Ctx n} {u} (Ŝ U r s : ℕ) (η : Fin n → ℕ) → 2 ≤ Ŝ →
      (o : Val Γ (obs u)) → sizeᵛ (obs u) o ≤ Ŝ → hopDᵛ Ŝ η (obs u) o < r →
      suc (dBound Ŝ (hopR Ŝ) U (hopDᵛ Ŝ η (obs u) o) (syncSizeᵉ o))
        ≤ dBound Ŝ (hopR Ŝ) U r s
     ) →
    -- connect-edge  (Verify-Budget-Sufficient/Wet/Part6.agda)
    (∀ {n} {Γ : Ctx n} (Ŝ r s : ℕ) → 2 ≤ Ŝ →
      (sl : Slots Γ) → slotsSize sl ≤ Ŝ → (cs : List Source) (i : Fin n)
      {d : Closed Γ (lookup Γ i)} {ok : T (inputsBelowᵉ (toℕ i) d)} →
      sl i ≡ shared d {ok = ok} →
      memberSource (toℕ i) cs ≡ false → sizeᵉ d ≤ Ŝ →
      suc (dBound Ŝ (hopR Ŝ) (unconn sl (toℕ i ∷ cs))
                  (hopDᵉ Ŝ (slotHop Ŝ sl) d) (syncSizeᵉ d))
        ≤ dBound Ŝ (hopR Ŝ) (unconn sl cs) r s
     ) →
    -- hop-step-gives  (Verify-Budget-Sufficient/Wet/Part6.agda)
    (∀ (V R U r s s′ : ℕ) → suc s′ ≤ s + suc V →
      suc (dBound V R U r s′) ≤ dBound V R U (suc r) s
     ) →
    -- hop-step-needs  (Verify-Budget-Sufficient/Wet/Part6.agda)
    (∀ (V R U r s s′ : ℕ) →
      suc (dBound V R U r s′) ≤ dBound V R U (suc r) s → suc s′ ≤ s + suc V
     ) →
    -- unconn-keeps  (Verify-Budget-Sufficient/Wet.agda)
    (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
      (sched : Sched Γ) (st : EvalSt e) (sched′ : Sched Γ) (st′ : EvalSt e) →
      Keeps sched st sched′ st′ →
      unconn (Sched.slots sched′) (EvalSt.connectedShares st′)
        ≤ unconn (Sched.slots sched) (EvalSt.connectedShares st)
     ) →
    -- sharedConnect-unconn  (Verify-Budget-Sufficient/Keeps-Ring.agda)
    (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
      (fuel : Gas) (i : Fin n) (d : Closed Γ (lookup Γ i))
      (κ : Path Γ (lookup Γ i) t) (id : Id) (now : Tick)
      (sched : Sched Γ) (st : EvalSt e) {dd : Closed Γ (lookup Γ i)}
      {okd : T (inputsBelowᵉ (toℕ i) dd)} →
      Sched.slots sched i ≡ shared dd {ok = okd} →
      memberSource (toℕ i) (EvalSt.connectedShares st) ≡ false →
      unconn (Sched.slots (proj₁ (proj₂ (sharedConnect (gs fuel) i d κ id now sched st))))
             (EvalSt.connectedShares
               (proj₂ (proj₂ (sharedConnect (gs fuel) i d κ id now sched st))))
      < unconn (Sched.slots sched) (EvalSt.connectedShares st)
     ) →
    -- obs-slot-shared  (Verify-Budget-Sufficient/Keeps-Ring.agda)
    (∀ {n} {Γ : Ctx n} {k u} (s : Slot Γ k (obs u)) →
      Σ (Closed Γ (obs u)) λ d → Σ (T (inputsBelowᵉ k d)) λ ok →
        s ≡ shared d {ok = ok}
     ) →
    -- share-live-novals  (Verify-Budget-Sufficient/Keeps-Ring.agda)
    (∀ {n} {Γ : Ctx n} {u} {A : Set} (s : Source) (id : Id) →
      proj₁ (splitBurst {Γ = Γ} {u = u} {A = A}
              (((init s ∷ []) at id from s as subscribe) ∷ [])) ≡ []
     ) →
    -- share-spent-novals  (Verify-Budget-Sufficient/Keeps-Ring.agda)
    (∀ {n} {Γ : Ctx n} {u} {A : Set} (s : Source) (id : Id) →
      proj₁ (splitBurst {Γ = Γ} {u = u} {A = A}
              (((init s ∷ close s exhausted ∷ complete ∷ []) at id from s as subscribe) ∷ []))
        ≡ []
     ) →
    -- hasAtLeast-pad  (Verify-Budget-Sufficient/Measures.agda)
    (∀ (m : ℕ) (g : Gas) {n} → n ≤ m → gasPad m g hasAtLeast n
     ) →
    -- hasAtLeast-peel  (Verify-Budget-Sufficient/Measures.agda)
    (∀ {g : Gas} {m : ℕ} → g hasAtLeast suc m →
      Σ Gas (λ g′ → (g ≡ gs g′) × (g′ hasAtLeast m))
     ) →
    -- seed-covers  (Verify-Budget-Sufficient/Measures.agda)
    (∀ (sz U : ℕ) → U ≤ sz →
      let V = towerℕ ((4 + sz) * 1) in
      suc (suc V * suc (hopR V) * suc U)
        ≤ 2 ^ (sz * 1 * 1) + towerℕ ((7 + sz) * 2)
     ) →
    -- budget-covers  (Verify-Budget-Sufficient/Measures.agda)
    (∀ (sz U id : ℕ) → U ≤ sz →
      let V = towerℕ ((4 + sz) * suc (suc id)) in
      suc (suc V * suc (hopR V) * suc U)
        ≤ 2 ^ (sz * suc id * suc id) + towerℕ ((7 + sz) * suc (suc id))
     ) →
    -- oneShot-tail-dry  (Verify-Budget-Sufficient/Measures.agda)
    (∀ {n} {Γ : Ctx n} {u} (vals : List (Val Γ u)) (src : Source) →
      any dryEvent (map value vals ++ close src exhausted ∷ complete ∷ []) ≡ false
     ) →
    -- connect-anchor  (Verify-Budget-Sufficient/Measures.agda)
    (∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
      (id : Id) (i : Fin n) {d : Closed Γ (lookup Γ i)}
      {ok : T (inputsBelowᵉ (toℕ i) d)} → sl i ≡ shared d {ok = ok} →
      let V = sizeBudgetAt e sl id in
      (hopDᵉ V (slotHop V sl) d ≤ hopR V) × (syncSizeᵉ d ≤ V)
     ) →
    -- hopD-map-emit  (Verify-Budget-Sufficient/Measures.agda)
    (∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s u} (V : ℕ) (η : Fin n → ℕ)
      (f : Tm Γ Δᵍ Δ (s ∷ Θ) u) (b : Exp Γ Δᵍ Δ Θ s) (v : Val Γ s) →
      (f₀ : Fn Γ [] [] [] s u) →
      hopDᵗ V η f₀ ≤ hopDᵗ V η f → pmᵗ V 0 f₀ ≤ pmᵗ V 0 f →
      hopDᵛ V η s v ≤ hopDᵉ V η b →
      hopDᵛ V η u (applyFn f₀ v) ≤ hopDᵉ V η (mapᵉ f b)
     ) →
    -- applyFn-size  (Verify-Budget-Sufficient/Measures.agda)
    (∀ {n} {Γ : Ctx n} {s t} (V : ℕ)
      (fn : Fn Γ [] [] [] s t) (v : Val Γ s) → sizeᵛ s v ≤ V →
      sizeᵛ t (applyFn fn v) ≤ (2 + 2 * V) ^ (3 ^ sizeᵗ fn)
     ) →
    -- unconn-cons-≤  (Verify-Budget-Sufficient/Measures.agda)
    (∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source)
      (s : Source) → unconn sl (s ∷ cs) ≤ unconn sl cs
     ) →
    -- shellSize-unfoldμ  (Verify-Budget-Sufficient/Measures.agda)
    (∀ {n} {Γ : Ctx n} {t} (body : Exp Γ (t ∷ []) [] [] t) →
      shellSizeᵉ (unfoldμ body) ≡ shellSizeᵉ body
     ) →
    -- inner-unfoldμ  (Verify-Budget-Sufficient/Measures.agda)
    (∀ {n} {Γ : Ctx n} {t} (body : Exp Γ (t ∷ []) [] [] t) →
      innerᵉ (unfoldμ body) ≡ innerᵉ body
     ) →
    -- walk-desc  (Verify-Budget-Sufficient/Caps-Chain.agda)
    (∀ (S W d k m j : ℕ) →
      sLvlD S W d k (suc j) ≤ sIterD S W d k (suc m) j
     ) →
    -- inner-desc  (Verify-Budget-Sufficient/Caps-Chain.agda)
    (∀ (S W d bud j m : ℕ) → 2 ≤ S →
      suc m ≤ suc (sizeAt S (suc j)) →
      opIterD S W d bud (suc m) (suc j) ≤ sLvlD S W d (suc bud) (suc j)
     ) →
  WalkLevel

-- THE COLLAPSED WALK FACE.  The face's statement: subscribeE-caps'
-- hypothesis list verbatim (caps prelims, the level-indexed size/width/
-- path bounds, the three charge indices dep/bud/ops), then the wet half
-- at the SAME level (INV? / fnCap / pathB? at cSize (frameStep j c)),
-- then the dry half (demand at the reset caps, one spare peel, the free
-- length ledger ℓ).  Conclusion: subscribeE-caps' Σ with the wet
-- conjuncts riding the same witness.

-- THE FACE IS GROUND.  `walkFace` (.Walk-Level) is a real definition on
-- every clause and this tree holds no live postulate; what follows is
-- what a reader editing the statement or the arms still needs, and
-- nothing about the grind, which is over.  The risk census, the grind
-- order and the P-series coverage rows that stood here are retired by
-- the proof of the very conjuncts they were about.  The probe that
-- carried the P-series rows expired with them and is deleted:
-- `git log --diff-filter=D -- agda/src/Verify-Budget-Sufficient/Demand-Probe.agda`.

-- WHY THE SPLIT IS EXACT, and it is the reason every arm's caps half is
-- a DELEGATION rather than a re-derivation.  Against `subscribeE-caps`
-- (.Subscribe-Face, GROUND):
--   · the caps prelims below are subscribeE-caps' OWN hypothesis list,
--     same statements, same ORDER, nothing added and nothing dropped;
--   · the capsOK?, burstCaps? and burstCount? conjuncts and the opIterD
--     level bound are its OWN Σ, verbatim — including the bound's
--     `j + j′` form.  (The `j′ ≤ …` form on the caps bridge is
--     `sub-charge` WEAKENING this one by m≤n+m, not a competing
--     statement — a mismatch there would have meant the collapse
--     silently strengthened the bound.)
-- So an arm reports the twin's witness and spends the twin's four
-- receipts; what it OWES is the wet five at its own shape.  Two arms
-- read the twin's witness through `proj₁`, which is why they split on
-- `ops` first: the twin's case tree splits on `ops` before the
-- expression, so with `ops` a variable its witness stays stuck.

-- DO NOT WEAKEN THE opIterD LEVEL BOUND.  Five of the nine conjuncts —
-- capsOK? / burstCaps? / burstCount? / INV? / burstB? — are
-- UPWARD-closed in j′ (frameStep is monotone in j and each is a
-- ≤-against-the-caps test), so each survives enlarging the witness.  The
-- level bound `j + j′ ≤ opIterD …` is the only conjunct bounding j′ from
-- ABOVE, and it is what gives those five their content: delete or weaken
-- it and the whole Σ is satisfiable by taking j′ enormous.  The
-- burstHopD? / hasDry / regsLen? conjuncts do not mention j′ at all.

-- AT THE DEGENERATE CORNER: `opIterD` is the identity at m = 0
-- (`opIterD-0`, .Rx.Evaluator) and `ops` sits in the m position, so
-- `ops = 0` would pin j′ = 0.  It is excluded by the `suc (sizeᵉ b) ≤
-- ops` hypothesis — the positivity is already threaded.  `dep = 0` and
-- `bud = 0` ARE reachable and are harmless: opIterD's `suc m` clause
-- bumps J unconditionally (J₀ = suc (J + …)) before any d/k-dependent
-- step runs.

-- THE CHAIN FRAMES DO NOT SHARE A PUSH FACE, and that is the one design
-- ruling to internalise before touching them.  A frame-generic wet push
-- face is REFUTED — the DEAD ROUTE at the hop-edge chain section below
-- (`pushBurst-walk`, generic in `f : Frame Γ s u`) — because caps
-- measures are frame-generic and THE HOP LEDGER IS NOT.  Each chain
-- frame needs its own face, at its own output index, and the index is
-- read off hopDᵉ (Rx.Hop-Depth) rather than chosen:
--   · takeᵉ  `hopDᵉ V η (takeᵉ c e) = hopDᵉ V η e` — the IDENTITY, so
--            no growth lemma is owed at all.
--   · mapᵉ   `hopDᵗ f + (pmᵗ V 0 f ⊔ 1) * hopDᵉ e`; the per-value step
--            is hopD-map-emit (.Measures), and the SIZE half rides
--            `burstB?-halves` rather than any growth theorem, which is
--            why applyFn-size never had to be fitted under the level
--            cap.
--   · scanᵉ  `(2 + pmᵗ V 0 f) ^ V * (hopDᵗ f + hopDᵗ z + hopDᵉ e)` —
--            EXPONENTIAL in V, which is the room that funds repeated
--            application.

-- THE GAS-PEEL FINDING, and it is what took the chain frames off
-- FALSITY.  In .Rx.Evaluator the mapᵉ, takeᵉ-`suc k` and scanᵉ clauses
-- each pass `fuel` UNCHANGED to both the recursive `subscribeE` and the
-- following `pushBurst`, and takeᵉ-`zero` never subscribes at all.  The
-- ONLY clauses that consume gas are μᵉ and subscribeAll/subscribeInner.
-- Series Q's mechanism IS gas exhaustion — a static sum (`sucG`) failing
-- to dominate a runtime product (d·k) — so it cannot be sited at a
-- clause that spends no gas; what a chain frame owes on the
-- hasDry/regsLen? axis is TRANSPORT across one frame at the same fuel.
-- Series Q's own region is in any case unreachable by measurement
-- (harness, 26 points: exponential in d·k with base 2.895, cheapest
-- refuting row ~2×10¹² years against a practical ceiling of d·k ≈ 21);
-- the curve was recorded in the deleted probe's series-Q header (the
-- `--diff-filter=D` line above finds it); the program family itself
-- survives in `.Demand-Programs`, which `Harness.Main` still runs.  Spell it
-- "series Q" — the receipt that first cited it wrote "Q-series", which
-- greps as nothing and cost a review cycle.

-- THE *All BODY'S PIECES — INV?-install (below, after all-setNode) and the
-- push face its assembly (below) consumes.

------------------------------------------------------------------
-- THE μ CLAUSE'S REMAINING MISSING PIECE.  Everything else walk-mu spends
-- is proven and named in its body; this is what the caps twin could NOT
-- donate (`ceil`/`lb` are wet-side reset-anchor pins; subscribeE-caps
-- carries no L̂ ledger).  fnCap-unfoldμ is now proven in .Measures.
------------------------------------------------------------------
-- THE μ LEVEL DESCENT, for the L̂ ceiling.  A μ unfolding is a FRESH
-- ENTRY, not a chain edge: it subscribes a LARGER term at a MINTED
-- index (`suc (sizeAt S (j + j₀))`) while spending one nesting level,
-- which is exactly the shape `op-step-mu` (.Caps-Chain) already opens
-- quadratic room for.  ROUTE: sLvlD-suc converts LHS to sLvlD; sLvlD-mono
-- bounds sLvlD (j+j₀) ≤ sLvlD J₀ under hJ₀; two -infl steps; opIterD-suc
-- closes.  hJ₀ at the call site is j + j₀ ≤ J₀ = suc(j + suc B * suc B)
-- with B = cSize(frameStep j c), derived from szb via quad-arith.
-- SEALED: body on the budget-sufficient spine; consumers need only the type.
abstract
  mu-lvl-desc : ∀ (c : Caps) (d bud m j j₀ : ℕ) → 2 ≤ Caps.cSize c →
    j + j₀ ≤ suc (j + suc (Caps.cSize (frameStep j c)) * suc (Caps.cSize (frameStep j c))) →
    opIterD (Caps.cSize c) (Caps.cWid c) d bud
            (suc (Caps.cSize (frameStep (j + j₀) c))) (j + j₀)
      ≤ opIterD (Caps.cSize c) (Caps.cWid c) d (suc bud) (suc m) j
  mu-lvl-desc c d bud m j j₀ 2≤S hJ₀ =
    let S  = Caps.cSize c
        W  = Caps.cWid c
        J₀ = suc (j + suc (Caps.cSize (frameStep j c)) * suc (Caps.cSize (frameStep j c)))
        J₂ = opIterD S W d (suc bud) m (sLvlD S W d (suc bud) J₀)
    in ≤-trans (≤-reflexive (sym (sLvlD-suc S W d bud (j + j₀))))
       (≤-trans (sLvlD-mono d d (suc bud) (suc bud) 2≤S ≤-refl ≤-refl hJ₀ ≤-refl ≤-refl)
       (≤-trans (opIterD-infl S W d (suc bud) m (sLvlD S W d (suc bud) J₀))
       (≤-trans (fIterD-infl S W d (suc bud) (suc (widAt S W J₂)) J₂)
                (≤-reflexive (sym (opIterD-suc S W d (suc bud) m j))))))
