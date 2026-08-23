-- GAP 4's ASSEMBLY (.Wet-4199).  THE JOINT INVARIANT BRIDGE
-- between the caps face's `capsOK?` (Caps-Face.agda) and the wet
-- family's `INV?` (Measures.agda).
--
-- capsOK? and INV? do not imply each other: capsOK? carries two WIDTH
-- conjuncts (widLive, widNode) INV? has no counterpart for, and INV?
-- carries the fn face (fnCapBounded?, the Ψ half of regsB?) and the
-- slots conjuncts (slotsSize ≤ B, slotsFnCap ≤ Ψ) capsOK? has no
-- counterpart for.  They also read registry cardinality at DIFFERENT
-- indices (INV? at cSize, capsOK? at cReg).  So this module threads a
-- JOINT invariant through one cascade, each face fed by its own tick:
-- `caps-tick` (.Caps-Face, PROVEN) supplies the boundedness half,
-- and the four postulated suppliers below (S1-S4) supply the rest.
-- `cascadeGo-caps` concludes boundedness only, no dry — dryness stays
-- on the gas axis (S3, P2's unchanged dry half).
--
-- CONSUMERS.  CORRECTED (the upside-down ruling) — the original text here said
-- "`cascade-dry` and `burst-wet` (.Wet) migrate to consume
-- `cascade-wet-via-caps`", which is IMPOSSIBLE: `.Caps-Bridge` imports
-- `.Wet` (below), so `.Wet` can never import `.Caps-Bridge` back. The
-- real fix moves the TOP of the tower UP instead: the one-cascade step,
-- `drain-dry` and `budget-sufficient` MOVED here from `.Wet`, caps-threaded,
-- consuming `cascade-wet-via-caps` directly (§ D below). `.Wet` keeps
-- `burst-dry`/`burst-bounded`/`pop-INV`/`pop-head-bounded`,
-- which this module consumes unchanged. P1's analogue
-- (`subscribeE-wet-via-caps`) is a REAL definition (§ D below), as are
-- `init-capsOK?` (every id, by ⊑ᶜ-induction) and the subscribe-side
-- caps lift.  `burst-caps` is proved as a corollary.  The module's one
-- remaining postulate on this side is `sizeCount-mono-d` (§ D).
module Verify-Budget-Sufficient.Caps-Bridge where

open import Data.Bool    using (Bool; true; false; _∧_; if_then_else_)
open import Data.Nat     using (ℕ; zero; suc; _+_; _*_; _≤_; _≤ᵇ_; _≡ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (≤ᵇ⇒≤; ≤⇒≤ᵇ; ≤-trans; ≤-refl; ≤-reflexive; m≤n+m; m≤m+n; n≤1+n; m≤m⊔n; m≤m*n; *-monoʳ-≤;
  +-monoˡ-≤; +-monoʳ-≤; *-suc; *-identityʳ)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.List    using (List; []; _∷_; length)
open import Data.Bool.ListAction using (all; any)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (inj₁; inj₂)
open import Data.Empty   using (⊥)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import Rx.Prim      using (Gas; Tick; Id; Fuel; close; exhausted)
open import Rx.Exp       using (Ctx; Closed; sizeᵉ; syncSizeᵉ; sizeᵛ)
open import Rx.Frame-Width using (dWᵉ; ceilᵉ; dW≤ceil; entryCeil; pWᵛ; pWᵉ)
open import Rx.Hop-Depth  using (hopDᵉ)
open import Rx.Slot-Hop using (slotHop)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; LiveSource; concat-st; RegId; Path; root; arrTy; arrVal; arrTick;
  arrSource; cascade; cascadeGo; cascadeLatch; cascadeFinish; chainStep; chainsOf; hasDry;
  subscribeE; budgetAt; opIterD; sizeStep; capsBase; sched-next; schedGo; schedHeadOf;
  schedEarlier; drain; evaluate; sched-init; st-init)
open import Rx.Slots using (Slots; slotsSize)

-- the whole wet family (INV?, ΨAt, sizeCapAt, sizeCapAt-mono, valB?,
-- fnCapBounded?, regsB?, slotsFnCap, INV-parts, pathLen, the Bool
-- toolkit ∧-true/∧-intro/all-impl/≤ᵇ-widen/T-to/T⇒≡true), each imported
-- below from the module that defines it
open import Verify-Budget-Sufficient.Measures using
  (_hasAtLeast_; all-impl; boundedLive; capᴱ; chainsB?-widen; dBound; finish-slots;
  fnCapBounded?; fnCapLive; fnCapᵉ; fnCapᵛ; hasDry-append; hopR; INV-parts; INV?; pathB?;
  pathLen; pop-bounded; pop-slots; pow1; regsB?; slotsFnCap; stBounded?; unconn; valB?;
  valB?-widen; V≤C; ΨAt; ∧-true; szB)
open import Verify-Budget-Sufficient.Keeps-Ring using
  (subscribeE-slots)
open import Verify-Budget-Sufficient.Wet.Part6 using
  (caps-fuel-root; cascadeFinish-INV; cascadeLatch-INV; chainsOf-B; init-INV; pop-head-bounded;
  pop-INV; sizeCapAt; sizeCapAt-mono)
open import Verify-Budget-Sufficient.Wet.Part1 using
  (INV?-widen)
open import Verify-Budget-Sufficient.Wet.Part3 using
  (cascadeGo-walk)

-- the caps face and the subscribe clique (capsOK?, capsOK?-parts,
-- capsOK?-count, caps-tick, pathSz?/regsSz?/frameSz?, slotsCaps?,
-- valCaps?, burstCaps?/burstCount?, subscribeE-caps, nest), each
-- imported below from the module that defines it
open import Verify-Budget-Sufficient.Subscribe-Face using
  (innerFinish-caps; subscribeE-caps; subscribeInner-caps)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using
  (burstCaps?; burstCount?; capsOK?; capsOK?-mono; n≤capsAt-size; pathSz?;
   regsSz?; slotsCaps?; valCaps?; widLive; widNode)
open import Verify-Budget-Sufficient.Caps-Face.Part7 using
  (caps-tick; cascade-depth-capsH; cascadeLatch-caps; chainsOf-caps;
   chainsOf-length)
open import Verify-Budget-Sufficient.Caps-Nest using
  (nest; nest≤)
open import Verify-Budget-Sufficient.Caps-Face.Part4 using
  (capsOK?-count; capsOK?-parts; capsOK?-regs; foldPath-slots;
   slotsCaps?-capsAt)

-- the depth mirror (S4's currency)
-- `depthChain` joins `depthE` here because `dry-tick`'s assembly consumes
-- `chainStep-caps`, whose statement is stated at the chain depth measure.
open import Verify-Budget-Sufficient.Caps-Depth using (depthE)
open import Rx.Nest-Depth using (nestDᵉ; nestDᵛ)
open import Verify-Budget-Sufficient.Nest-Store using
  (pathNestD; slotsNestSum; storeNestMax; nestCapAt; nestCapAt-0;
   nestOK?; nestOK?-store; nestOK?-intro; nestCapAt-suc; nest-sum-3;
   realWidAt; nestSyn)
open import Verify-Budget-Sufficient.Op-Budget using (opIterD-dominated)
open import Verify-Budget-Sufficient.Init-Caps using (baseCaps; init-capsOK?-base)
open import Verify-Budget-Sufficient.Level-Mono using (sizeCount-mono-d)
open import Verify-Budget-Sufficient.Caps
  using (2≤capsAt-size; capsAt-base-size; capsAt-base-wid; sizeCount-body; frameBlowup;
  iterSize-mono-count; 2≤sizeCount; cSize≤frameBlowup; B2-cReg≤cSize; 1≤capsAt-reg; _⊑ᶜ_; Caps;
  caps; capsAt; capsAt-suc-full; capsH; frameStep; frameStep-0; frameStep-full;
  frameStep-mono-j; sizeCount)
open import Verify-Budget-Sufficient.Burst-Walk
  using (cascadeGo-nodry)
open import Verify-Budget-Sufficient.Psi-Split using
  (pathBΨ?; pathBΨ?-of; regsB?-of-parts; regsBΨ?; regsBΨ?-of)
-- the wet contract itself, stated over the COLLAPSED walk.
-- It lives one arrow above .Wet and .Subscribe-Face because its
-- statement is the only one reading BOTH vocabularies; this module is
-- its sole consumer.
open import Verify-Budget-Sufficient.Walk-Level using (subscribeE-wet)
open import Rx.Exp using (sizeᵛ; Closed; Ctx; sizeᵉ; syncSizeᵉ)
open import Decide using (T-to; T⇒≡true; f≡t-absurd; ∧-intro; ≤ᵇ-widen)

------------------------------------------------------------------
-- (B3, EARLY) THE Ψ-ONLY HALVES, defined before the suppliers that
-- state facts about them.  `frameB? B Ψ f` bundles a size test and a
-- weight test per frame (`(sizeᵗ fn ≤ᵇ B) ∧ ((caseWᵗ fn ⊔ fnCapᵗ fn) ≤ᵇ
-- Ψ)` on map-f/scan-f, `true` elsewhere) — and `frameSz? B f` (the
-- caps side, .Caps-Face) is EXACTLY its size half, clause for
-- clause.  So the missing half is the Ψ-only one, and both it and the
-- recombination lemmas that reunite the two into the real
-- `frameB?`/`pathB?`/`regsB?` (Measures.agda) that INV? reads now live
-- in .Burst-Walk, imported above.
------------------------------------------------------------------

-- frameBΨ?/pathBΨ?/regsBΨ? RELOCATED to .Burst-Walk: the
-- burst walk's Ψ ledger consumes them there, upstream of this module.

------------------------------------------------------------------
-- (B) THE SUPPLIERS.  S2 lands first: S1's proof calls it.
------------------------------------------------------------------

-- S2 `slots-tick` : the raw `Sched.slots` equality across a cascade.
-- PROVEN.  STRONGER than the two-conjunct version first asked for,
-- and deliberately so — the two conjuncts alone cannot bridge
-- `caps-tick`'s fixed entry-time `sl` to the wet family's own
-- convention of re-reading `Sched.slots` off whatever the current
-- schedule is, and that bridge is load-bearing below (`capsOut`).
--
-- The raw equality is a genuinely STRUCTURAL fact: grepping
-- Rx.Evaluator.agda for `slots =` finds exactly ONE occurrence in the
-- whole file — `sched-init`'s own construction.  No `record sched
-- { ... }` update anywhere in the mutual delivery clique ever touches
-- the `slots` field.  Most of the clique's own slots-invariance is
-- ALREADY PROVEN one layer down:
-- `.Keeps-Ring` (`subscribeE-slots`) carries it through the
-- whole subscribe clique via the `Keeps` invariant, `Caps-Face.agda:
-- 3690+` (`foldPath-slots`/`dispatchShare-slots`/`shareGo-slots`) has
-- the delivery side, and `.Measures` (`finish-slots`) covers
-- `cascadeFinish`.  Only two thin wrappers were missing — `chainStep`
-- (one call into `foldPath`) and `cascadeGo`'s own fold over chains —
-- and both are direct compositions of what already exists.
chainStep-slots : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (id : Id) (a : Arrival Γ) (path : Path Γ (arrTy a) t) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots (proj₁ (proj₂ (chainStep id a path sched st))) ≡ Sched.slots sched
chainStep-slots {n = n} {e = e} id a path sched st =
  foldPath-slots (budgetAt e (Sched.slots sched) id) n id (arrTick a) (arrSource a) path (arrVal a ∷ [])
                 (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else [])
                 (Arrival.isLast a) sched st

cascadeGo-slots : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (id : Id) (chains : List (RegId × Path Γ (arrTy a) t))
  (sched₀ : Sched Γ) (st₀ : EvalSt e) →
  Sched.slots (proj₁ (proj₂ (cascadeGo a id chains sched₀ st₀))) ≡ Sched.slots sched₀
cascadeGo-slots a id [] sched₀ st₀ = refl
cascadeGo-slots a id ((rid , c) ∷ chains) sched₀ st₀
  with any (_≡ᵇ rid) (EvalSt.cancelled st₀)
... | true = cascadeGo-slots a id chains sched₀ st₀
... | false =
      let (emits , sched₁ , st₁) =
            chainStep id a c sched₀ (record st₀ { delivered = rid ∷ EvalSt.delivered st₀ })
      in trans (cascadeGo-slots a id chains sched₁ st₁)
               (chainStep-slots id a c sched₀ (record st₀ { delivered = rid ∷ EvalSt.delivered st₀ }))

slots-tick : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (id : Id) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots (proj₁ (proj₂ (cascade a id sched st))) ≡ Sched.slots sched
slots-tick a id sched st =
  let (emits , sched′ , st′) = cascadeGo a id (chainsOf a st) sched (cascadeLatch a st)
  in trans (finish-slots a sched′ st′)
           (cascadeGo-slots a id (chainsOf a st) sched (cascadeLatch a st))

------------------------------------------------------------------
-- S1 `fn-tick` : the fn face is preserved across a cascade.  PROVEN,
-- and NOT by the from-scratch walk over stepFrame/pushBurst/
-- subscribeInner/... this module's header once anticipated.  Ψ never
-- needs to grow (caseW is substitution-invariant, per INV?'s own
-- header at .Measures-5323), so `fn-tick`'s conclusion —
-- Ψ-indexed only, no numeric B/E reading — is satisfied by ANY witness
-- INV? holds at, regardless of the size-axis bound reached.  That
-- means the already-proven `cascadeGo-walk` (.Wet, folding
-- the WHOLE six-conjunct INV? over the chains list at a GROWING
-- ledger bound) is directly usable here: embed the caps-level input
-- bound `B` into `capᴱ B 3` (via `pow1`), widen the input facts across
-- that embedding, run cascadeLatch-INV → cascadeGo-walk →
-- cascadeFinish-INV, then project `fnCapBounded?` and the Ψ half of
-- `regsB?` out of the landed INV? at whatever bound the walk reached.
-- GAP 4's refuted size-axis composition (why the old cascade core was
-- still stuck) never enters, because nothing here needs to land back
-- at the fixed `sizeCapAt e sl (suc id)`.  The one remaining seam —
-- the conclusion is stated at `Ψ′ = ΨAt e sl′` (output slots), the
-- walk runs at `Ψ = ΨAt e sl` (input slots) — closes by S2 above.
------------------------------------------------------------------

-- embedding a fixed bound B into capᴱ form: B ≤ 2 + 2·B ≤ capᴱ B 3,
-- the second step by `pow1` (Measures.agda, already proven).  The `≤`
-- step is `V≤C` (.Measures), where the one proof lives; this module
-- must not restate it, which is what `make dup-check` is for.
b≤capᴱ-b-3 : ∀ b → b ≤ capᴱ b 3
b≤capᴱ-b-3 b = ≤-trans (V≤C b) (pow1 b {3} (s≤s z≤n))

fn-tick : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (id : Id) (sched : Sched Γ) (st : EvalSt e) →
  let sl = Sched.slots sched
      Ψ  = ΨAt e sl
      B  = sizeCapAt e sl id
  in INV? Ψ B sched st ≡ true →
     valB? B Ψ (arrTy a) (arrVal a) ≡ true →
     let r   = cascade a id sched st
         sl′ = Sched.slots (proj₁ (proj₂ r))
         Ψ′  = ΨAt e sl′
     in (fnCapBounded? Ψ′ (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
        × (regsBΨ? Ψ′ (EvalSt.registry (proj₂ (proj₂ r))) ≡ true)
fn-tick {e = e} a id sched st inv val =
  subst (λ ψ → fnCapBounded? ψ sched″ st″ ≡ true) (sym Ψ′≡Ψ) fcΨ ,
  subst (λ ψ → regsBΨ? ψ (EvalSt.registry st″) ≡ true) (sym Ψ′≡Ψ) regsBΨF
  where
  sl  = Sched.slots sched
  Ψ   = ΨAt e sl
  B   = sizeCapAt e sl id
  W   = B
  E₀  = 3

  3≤E₀ : 3 ≤ E₀
  3≤E₀ = ≤-refl

  B≤ : B ≤ capᴱ W E₀
  B≤ = b≤capᴱ-b-3 B

  inv-caps : INV? Ψ (capᴱ W E₀) sched st ≡ true
  inv-caps = INV?-widen sched st B≤ inv

  val-caps : valB? (capᴱ W E₀) Ψ (arrTy a) (arrVal a) ≡ true
  val-caps = valB?-widen (arrTy a) (arrVal a) B≤ val

  parts0 = INV-parts Ψ B sched st inv
  regsB0 : regsB? B Ψ (EvalSt.registry st) ≡ true
  regsB0 = proj₁ (proj₂ (proj₂ (proj₂ parts0)))

  chains = chainsOf a st

  chainsB : all (λ rc → pathB? B Ψ (proj₂ rc)) chains ≡ true
  chainsB = chainsOf-B B Ψ a st regsB0

  chainsB-caps : all (λ rc → pathB? (capᴱ W E₀) Ψ (proj₂ rc)) chains ≡ true
  chainsB-caps = chainsB?-widen chains B≤ chainsB

  latched = cascadeLatch a st

  inv-latch : INV? Ψ (capᴱ W E₀) sched latched ≡ true
  inv-latch = cascadeLatch-INV Ψ (capᴱ W E₀) a sched st inv-caps

  GO = cascadeGo-walk Ψ W a id chains sched latched E₀ 3≤E₀
                      inv-latch chainsB-caps val-caps

  E′ = proj₁ GO

  sched′ = proj₁ (proj₂ (cascadeGo a id chains sched latched))
  st′    = proj₂ (proj₂ (cascadeGo a id chains sched latched))

  invGo : INV? Ψ (capᴱ W E′) sched′ st′ ≡ true
  invGo = proj₁ (proj₂ (proj₂ GO))

  sched″ = proj₁ (cascadeFinish a sched′ st′)
  st″    = proj₂ (cascadeFinish a sched′ st′)

  invFinish : INV? Ψ (capᴱ W E′) sched″ st″ ≡ true
  invFinish = cascadeFinish-INV Ψ (capᴱ W E′) a sched′ st′ invGo

  partsF = INV-parts Ψ (capᴱ W E′) sched″ st″ invFinish

  fcΨ : fnCapBounded? Ψ sched″ st″ ≡ true
  fcΨ = proj₁ (proj₂ partsF)

  regsBF : regsB? (capᴱ W E′) Ψ (EvalSt.registry st″) ≡ true
  regsBF = proj₁ (proj₂ (proj₂ (proj₂ partsF)))

  regsBΨF : regsBΨ? Ψ (EvalSt.registry st″) ≡ true
  regsBΨF = regsBΨ?-of (EvalSt.registry st″) regsBF

  slotsEq : Sched.slots sched″ ≡ Sched.slots sched
  slotsEq = slots-tick a id sched st

  Ψ′≡Ψ : ΨAt e (Sched.slots sched″) ≡ Ψ
  Ψ′≡Ψ = cong (ΨAt e) slotsEq

------------------------------------------------------------------
-- S3 `dry-tick` : the cascade's dry half, on the gas-peel axis
-- (dBound-μ/hop/connect).

-- TIER 0, LAST.  Nearly all this postulate's risk is INHERITED from
-- the anchor chain — its first hypothesis is `cascadeGo-nodry`, which
-- is a REAL projection of the three-flavour walk
-- (.Burst-Walk), so the inherited risk now bottoms out in
-- `stepFrame-nodry` (§ 5a) and through it in `subscribeE-walk-level`
-- (.Walk-Level).  Given those, what is left here is latch/finish
-- bookkeeping plus the Deliveries counts.  Work it after the anchor
-- chain resolves, never first.  (An earlier version of this header
-- claimed independence from the caps/INV? bridging problem — wrong,
-- and the kind of wrong that re-orders a schedule.)

-- THE MIRROR CENSUS SWAPPED THE FIRST HYPOTHESIS.  It
-- used to be the full `cascadeGo-wet` (hasDry × INV?-landing, the old
-- two-conjunct anchor).  The INV? conjunct was never needed here — this
-- core's own conclusion is dry-only, and the mid-cascade invariant a
-- dry grind threads is the Walk's own caps-flavoured `Res.good`
-- (.Delivery-Walk), proven; the landing is `cascade-wet-via-caps`'s
-- (§ C below), also proven.  So the hypothesis is now the dry-only
-- `cascadeGo-nodry`, at the caps telescope this core's driver facts
-- already supply — the same telescope as `cascadeGo-burst-dry` below.

-- ASSEMBLY: narrowed over the cascade-level facts it was
-- written to be built from.  `cascade` IS cascadeLatch → cascadeGo →
-- cascadeFinish, so the pieces are the anchor's dry half,
-- .Subscribe-Face's per-chain caps step, and .Deliveries' four cascade
-- counts, which say the latch clears the ledger and the two walk lines
-- account for it.
--
-- ══ THAT ROUTE LIST IS WRONG ABOUT ITSELF.  Two facts, one
-- ══ pinned and one cited:
--
-- (1) THE CONCLUSION IS `cascadeGo-nodry`'s VERBATIM.  `cascadeFinish`
--     returns (Sched × EvalSt) and emits NOTHING (Rx.Evaluator), so a
--     cascade's stream IS its cascadeGo's — pinned by `refl` just above
--     `dry-tick` below.  The paragraph above reads "`cascade` IS
--     cascadeLatch → cascadeGo → cascadeFinish" and infers that all three
--     stages owe something to the DRY half; only the middle one does.
--     Nothing about the ledger survives into `hasDry`, so .Deliveries'
--     four counts (cascadeLatch-deliv, cascade-delivN, cascadeGo-skip-N,
--     cascadeGo-cons-N) cannot be ingredients HERE.  Nor can the four
--     whose conclusions are bounds rather than dryness —
--     cascadeGo-burst-dry (burstB?), subscribeInner-dry (valB? of the
--     inner burst), dry-hop (a sizeᵛ bound), chainStep-caps (a
--     capsOK?/burstCaps? Σ).  Their real home is the OTHER two conjuncts
--     of `cascade-wet-via-caps` (§ C), which is where a cascade's bound
--     and ledger obligations actually land; re-homing them there is the
--     remaining obligation: all eight are PROVEN and orphaning them is not
--     a licence to delete them.
--
-- (2) THE ONE REAL INGREDIENT CANNOT BE PAID AS `dry-tick` IS STATED.
--     `cascadeGo-nodry`'s first premise is `capsOK? (capsAt e sl id)
--     sched st ≡ true`, and dry-tick offers only `INV?` — which this
--     module's own header (top of file) and .Wet/Part6's note (b) both
--     record as INSUFFICIENT BY CONSTRUCTION: capsOK? carries two WIDTH
--     conjuncts (widLive, widNode) for which INV? has no counterpart at
--     all, so no proof can manufacture them.  The caps face is not
--     missing a lemma; the statement is missing a hypothesis.

--     AND ITS SOLE CALLER ALREADY HOLDS IT.  `cascade-wet-via-caps` (§ C)
--     takes `capsOK? (capsAt e sl id) sched st` and `valCaps? …` as its
--     own hypotheses (`pre`, `valC`) and calls `dry-tick a id sched st
--     inv val` without them — so the two premises the body needs are
--     already proven one line up.

-- WRITING THE REAL BODY IS BLOCKED ON A RESTATEMENT, NOT A PROOF:
-- dry-tick and this core gain `pre` and `valC`, threaded from the caller.
-- That is "ADDING A HYPOTHESIS IS A RESTATEMENT" (CLAUDE.md), and the
-- one sufficient justification is a REFUTATION of the unconditional
-- form — a state satisfying INV? and failing capsOK?.
--
-- ══ THAT REFUTATION IS NOW BUILT — see the anonymous pin
-- ══ below, just above `dry-tick`.  The restatement is UNBLOCKED.
-- The witness is not a width at all but the concat queue's LENGTH: INV?
-- reaches a node only through boundedNode and fnCapNode, both `all`s
-- over the queue's ELEMENTS, while capsOK?'s widNode also demands
-- `length q ≤ᵇ cWid`.  One concat node holding cWid+1 copies of a single
-- small expression therefore satisfies INV? and fails capsOK?, at
-- `capsAt e sl id` itself.  So dry-tick may not consume capsOK? from the
-- INV? it is given, and "the call site happens to supply it" — which
-- here it demonstrably does — remains not a reason.
-- ── WHAT THE DRY HALF ACTUALLY REDUCES TO ──────────────
-- `cascadeFinish` returns a (Sched × EvalSt) and NO emits (Rx.Evaluator),
-- so a cascade's stream IS its cascadeGo's, and dry-tick's conclusion is
-- `cascadeGo-nodry`'s conclusion verbatim at the latched state.  Pinned
-- rather than argued, because it is what shows that latch/finish
-- BOOKKEEPING cannot be an ingredient of the dry half — see
-- dry-tick-core's header.  Anonymous by the bug-cache idiom.
_ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
      (a : Arrival Γ) (id : Id) (sched : Sched Γ) (st : EvalSt e) →
    proj₁ (cascade a id sched st)
      ≡ proj₁ (cascadeGo a id (chainsOf a st) sched (cascadeLatch a st))
_ = λ a id sched st → refl

-- ══ INV? DOES NOT IMPLY capsOK? — MACHINE-REFUTED ═══════
-- dry-tick-core's header (above) names the restatement that blocks it:
-- dry-tick and the core gain `pre`/`valC`, threaded from
-- `cascade-wet-via-caps`.  CLAUDE.md's "ADDING A HYPOTHESIS IS A
-- RESTATEMENT" allows that only against a REFUTATION of the
-- unconditional form.  This is it.
--
-- THE GAP IS NARROWER THAN THE HEADER SAYS.  That header names the two
-- WIDTH conjuncts (widLive, widNode) as the place INV? has no
-- counterpart.  True, but the cheapest witness is not a width at all —
-- it is the concat queue's LENGTH:
--
--   boundedNode B (concat-st q _ _) = all (λ o → sizeᵉ o ≤ᵇ B) q
--   fnCapNode   Ψ (concat-st q _ _) = all (λ o → fnCapᵉ o ≤ᵇ Ψ) q
--   widNode   W sl (concat-st q _ _) = all (λ o → pWᵉ n sl o ≤ᵇ W) q
--                                      ∧ (length q ≤ᵇ W)
--
-- INV? reads a node ONLY through boundedNode (inside stBounded?) and
-- fnCapNode (inside fnCapBounded?).  Both are `all`s over the queue's
-- ELEMENTS; NEITHER bounds how many elements there are.  capsOK? does.
-- So one concat node holding W+1 copies of a single small expression
-- satisfies INV? and fails capsOK? — and it fails at `capsAt e sl id`,
-- the caps the assembly actually uses, not at caps chosen to break it.
-- No value has to be made wide, and no numeral appears: the queue is
-- built at length `suc (Caps.cWid (capsAt e sl id))` symbolically.
--
-- NOT VACUOUS, but say what that rests on.  This is an IMPLICATION, so
-- it would assert nothing if its six hypotheses were unsatisfiable.  They
-- are not exotic: the four state-side ones are literally INV?'s own
-- conjuncts at a node-free state, and the two element-side ones just ask
-- that ONE expression fit the size and fnCap caps.  If that set were
-- unsatisfiable, `dry-tick`'s own INV? hypothesis would be too, and the
-- postulate would be vacuous — a different and larger finding.  What is
-- NOT machine-witnessed here is a concrete instance discharging all six;
-- exhibiting one would close the last gap in this receipt.
--
-- SCOPE, and this is the whole caveat.  It refutes the POSTULATE AS
-- STATED, which quantifies over every `sched`/`st`.  It does NOT show
-- the evaluator can REACH such a state — per CLAUDE.md a constructed
-- state where the predicate fails is a refutation candidate whose
-- reachability is itself the finding, and that question stays open.
-- For the restatement that is already enough: dry-tick may not consume
-- what its own hypothesis does not give it, reachable or not.
private
  -- The capsOK? side is stated as `≡ true → ⊥` rather than `≡ false`.
  -- CONSTRUCTING a `≡ false` through a stuck conjunction is the blocked
  -- direction: `_∧_` is a FUNCTION, not a constructor, so Agda will not
  -- decompose `?x ∧ ?y = C₁ ∧ REST` by unification, and a collapse chain
  -- postpones forever (measured: UnsolvedConstraints, "blocked on _x").
  -- EXTRACTING from `≡ true` has no such problem — it is what ∧-true
  -- does thirty times in this file — so the refutation runs that way.
  -- (the refutation itself is `f≡t-absurd`, .Measures — strictly stronger,
  -- and imported here directly from .Measures.)

  -- widNode W sl (concat-st q _ _) = all (pWᵉ-bound) q ∧ (length q ≤ᵇ W).
  -- Peeled HERE rather than at the use site because the RESULT type pins
  -- ∧-true's second Bool, leaving only the first to solve — and because
  -- `n` is in scope here, so the pWᵉ side needs no underscore (one there
  -- sends Agda inverting `_≤ᵇ_` to depth 50).
  widNode-len : ∀ {n} {Γ : Ctx n} (W : ℕ) (sl : Slots Γ) {u}
                (q : List (Closed Γ u)) (a b : Bool) →
                widNode W sl (concat-st q a b) ≡ true →
                (length q ≤ᵇ W) ≡ true
  widNode-len {n = n} W sl q a b h =
    proj₂ (∧-true (all (λ o′ → pWᵉ n sl o′ ≤ᵇ W) q) (length q ≤ᵇ W) h)

  -- k copies of one queued expression
  repQ : ∀ {n} {Γ : Ctx n} {u} → ℕ → Closed Γ u → List (Closed Γ u)
  repQ zero    o = []
  repQ (suc k) o = o ∷ repQ k o

  repQ-len : ∀ {n} {Γ : Ctx n} {u} (k : ℕ) (o : Closed Γ u) →
             length (repQ k o) ≡ k
  repQ-len zero    o = refl
  repQ-len (suc k) o = cong suc (repQ-len k o)

  repQ-all : ∀ {n} {Γ : Ctx n} {u} (P : Closed Γ u → Bool)
             (k : ℕ) (o : Closed Γ u) → P o ≡ true →
             all P (repQ k o) ≡ true
  repQ-all P zero    o h = refl
  repQ-all P (suc k) o h rewrite h = repQ-all P k o h

  -- the one arithmetic fact: a list of length W+1 does not fit width W
  sucW≰W : (W : ℕ) → (suc W ≤ᵇ W) ≡ false
  sucW≰W zero    = refl
  sucW≰W (suc W) = sucW≰W W

-- `e` is EXPLICIT: the proof term needs it (for `capsAt e sl id`), and an
-- anonymous `_ = λ …` cannot bind the type's leading implicits — that is
-- WrongHidingInLambda, the same trap the take-cut pin hit.
--
-- The four INV? conjuncts that do NOT concern the new node are taken as
-- HYPOTHESES rather than split out of a compound `INV? … ≡ true` with
-- ∧-true: decomposing it leaves the split point as a metavariable that
-- Agda cannot solve while it is simultaneously matching the rebuilt
-- conjunction against the goal.  Basing the state on `st-init e` makes
-- the two registry conjuncts `refl`, so what remains is exactly the two
-- live halves and the two slot bounds — none of which the node edit
-- touches, which is the point being made.
_ : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) {u}
      (id : Id) (sched : Sched Γ) (o : Closed Γ u) →
    let sl  = Sched.slots sched
        Ψ   = ΨAt e sl
        B   = sizeCapAt e sl id
        c   = capsAt e sl id
        q   = repQ (suc (Caps.cWid c)) o
        st  = record (st-init e) { nodes = (0 , concat-st q false false) ∷ [] }
    in all (boundedLive B) (Sched.live sched) ≡ true →
       all (fnCapLive Ψ) (Sched.live sched) ≡ true →
       (slotsSize sl ≤ᵇ B) ≡ true →
       (slotsFnCap sl ≤ᵇ Ψ) ≡ true →
       (sizeᵉ o ≤ᵇ B) ≡ true →
       (fnCapᵉ o ≤ᵇ Ψ) ≡ true →
       (INV? Ψ B sched st ≡ true) × (capsOK? c sched st ≡ true → ⊥)
_ = λ e id sched o hLive hFnLive hSS hSF hsz hfn →
  let sl = Sched.slots sched
      Ψ  = ΨAt e sl
      B  = sizeCapAt e sl id
      c  = capsAt e sl id
      W  = Caps.cWid c
      q  = repQ (suc W) o
      st = record (st-init e) { nodes = (0 , concat-st q false false) ∷ [] }
      hNodeSz : all (λ o′ → sizeᵉ o′ ≤ᵇ B) q ≡ true
      hNodeSz = repQ-all (λ o′ → sizeᵉ o′ ≤ᵇ B) (suc W) o hsz
      hNodeFn : all (λ o′ → fnCapᵉ o′ ≤ᵇ Ψ) q ≡ true
      hNodeFn = repQ-all (λ o′ → fnCapᵉ o′ ≤ᵇ Ψ) (suc W) o hfn
      hLen : (length q ≤ᵇ W) ≡ false
      hLen = trans (cong (_≤ᵇ W) (repQ-len (suc W) o)) (sucW≰W W)
      -- capsOK?'s five conjuncts, NAMED.  ∧-true's Bool arguments must be
      -- given explicitly: `_` leaves them as metas that Agda will not
      -- solve, because decomposing `?a ∧ ?b = C ∧ REST` needs `_∧_` to be
      -- injective and it is a function.  Same lesson as the ∧-true sites
      -- in .Burst-Walk.
      A3 = all (widLive W sl) (Sched.live sched)
      A4 = all (λ kv → widNode W sl (proj₂ kv)) (EvalSt.nodes st)
      A5 = (length (EvalSt.registry st) ≤ᵇ Caps.cReg c)
      A2 = regsSz? B (EvalSt.registry st)
      A1 = stBounded? B sched st
      WD = widNode W sl (concat-st q false false)
  in ∧-intro (∧-intro hLive   (∧-intro hNodeSz refl))
             (∧-intro (∧-intro hFnLive (∧-intro hNodeFn refl))
                      (∧-intro refl (∧-intro refl (∧-intro hSS hSF))))
   -- capsOK? = stBounded? ∧ regsSz? ∧ widLive ∧ widNode ∧ regCount.
   -- Peel to the widNode conjunct, then to its queue-LENGTH half, and
   -- read `length q ≤ᵇ W ≡ true` off against hLen's `≡ false`.
   , λ hc → let t2 = proj₂ (∧-true A1 (A2 ∧ (A3 ∧ (A4 ∧ A5))) hc)
                t3 = proj₂ (∧-true A2 (A3 ∧ (A4 ∧ A5)) t2)
                t4 = proj₂ (∧-true A3 (A4 ∧ A5) t3)
                t5 = proj₁ (∧-true A4 A5 t4)
                w  = proj₁ (∧-true WD true t5)
                ln = widNode-len W sl q false false w
            in f≡t-absurd (trans (sym hLen) ln)

-- ══ MIGRATED — `dry-tick-core` IS GONE ═══════════════════
-- It was a postulate over NINE proven lemmas.  Eight were never
-- ingredients (the route list was wrong about itself, refuted by the pin
-- above: `cascadeFinish` emits nothing, so the dry half is `cascadeGo`'s
-- and no latch/finish bookkeeping or bound can enter it), and the ninth —
-- `cascadeGo-nodry` — could not be applied because its `capsOK?` premise
-- is not derivable from the `INV?` this statement offered.  Both facts are
-- now CHECKED rather than claimed: the body below applies exactly one
-- lemma, and the typechecker holds the reduction.
--
-- `pre`/`valC` ADDED, which is a RESTATEMENT with the one sufficient
-- justification: the unconditional form is REFUTED (the pin above — a
-- concat node holding cWid+1 copies satisfies INV? and fails capsOK?, at
-- `capsAt e sl id` itself).  Its sole caller `cascade-wet-via-caps` holds
-- both already, so nothing downstream had to be found; but "the call site
-- happens to supply it" is not the reason, the refutation is.
--
-- WHERE THE TWELVE PREMISES CAME FROM, and none of them needed new
-- mathematics.  `caps-tick` (.Caps-Face/Part7) already discharges the
-- caps-side eight for `cascadeGo-caps` at THIS EXACT call — same `c`,
-- same `chainsOf a st`, same `cascadeLatch a st` — and `fn-tick` (above,
-- in this file) already discharges the Ψ-side four for `cascadeGo-walk`.
-- The body below is their union.  This is CLAUDE.md's index rule paying
-- out: the answer to "at what index should this be stated?" was sitting
-- in two proven bodies whose arguments only had to be read off.
dry-tick : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (id : Id) (sched : Sched Γ) (st : EvalSt e) →
  let sl = Sched.slots sched
      Ψ  = ΨAt e sl
      B  = sizeCapAt e sl id
  in INV? Ψ B sched st ≡ true →
     valB? B Ψ (arrTy a) (arrVal a) ≡ true →
     capsOK? (capsAt e sl id) sched st ≡ true →
     nestOK? e sl id sched st ≡ true →
     nestDᵛ (arrTy a) (arrVal a) ≤ nestCapAt e sl id →
     valCaps? (capsAt e sl id) sl (arrTy a) (arrVal a) ≡ true →
     hasDry (proj₁ (cascade a id sched st)) ≡ false
dry-tick {n = n} {e = e} a id sched st inv val pre nok bnd valC =
  cascadeGo-nodry subscribeInner-caps innerFinish-caps
    id a chains sched latched
    (slotsCaps?-capsAt e sl id)
    (≤-trans (m≤n+m (slotsSize sl) (2 + sizeᵉ e)) (capsAt-base-size e sl id))
    (cascadeLatch-caps c a sched st pre)
    fnB
    valC
    (proj₂ (∧-true (sizeᵛ (arrTy a) (arrVal a) ≤ᵇ B)
                   (fnCapᵛ (arrTy a) (arrVal a) ≤ᵇ Ψ) val))
    (chainsOf-caps (Caps.cSize c) a st (capsOK?-regs c sched st pre))
    chainsΨ
    regsΨ
    (n≤capsAt-size e sl id)
    (≤-trans (chainsOf-length a st) (capsOK?-count c sched st pre))
    (cascade-depth-capsH sl id a id sched st refl pre nok bnd)
  where
  sl      = Sched.slots sched
  Ψ       = ΨAt e sl
  B       = sizeCapAt e sl id
  c       = capsAt e sl id
  chains  = chainsOf a st
  latched = cascadeLatch a st
  -- the Ψ axis rides the latch on INV?, exactly as fn-tick does it
  inv-latch : INV? Ψ B sched latched ≡ true
  inv-latch = cascadeLatch-INV Ψ B a sched st inv
  partsL    = INV-parts Ψ B sched latched inv-latch
  fnB : fnCapBounded? Ψ sched latched ≡ true
  fnB = proj₁ (proj₂ partsL)
  regsB-latch : regsB? B Ψ (EvalSt.registry latched) ≡ true
  regsB-latch = proj₁ (proj₂ (proj₂ (proj₂ partsL)))
  regsΨ : regsBΨ? Ψ (EvalSt.registry latched) ≡ true
  regsΨ = regsBΨ?-of (EvalSt.registry latched) regsB-latch
  -- and the chains' Ψ half, off the SAME regsB? the size half is read from
  chainsB : all (λ rc → pathB? B Ψ (proj₂ rc)) chains ≡ true
  chainsB = chainsOf-B B Ψ a st
              (proj₁ (proj₂ (proj₂ (proj₂ (INV-parts Ψ B sched st inv)))))
  chainsΨ : all (λ rc → pathBΨ? Ψ (proj₂ rc)) chains ≡ true
  chainsΨ = all-impl _ _ (λ rc → pathBΨ?-of (proj₂ rc)) chains chainsB

------------------------------------------------------------------
-- S4 `sub-charge` : GAP 4 (a)'s missing subscribe-level charge.  NO
-- MISALIGNMENT FOUND, and no postulate needed — `subscribeE-caps`
-- (.Subscribe-Face, GROUND) already carries the hypothesis
-- `depthE g b κ bid now sched st ≤ dep` and already concludes
-- `j + j′ ≤ opIterD (Caps.cSize c) (Caps.cWid c) dep bud ops j` as the
-- fourth component of its Σ.  `depthE`'s argument list (g, b, κ, bid,
-- now, sched, st) is LITERALLY subscribeE-caps' own argument list in
-- the same order, so instantiating `dep := depthE g b κ bid now sched
-- st` discharges that hypothesis by `≤-refl` and reports j′'s bound
-- "via the Caps-Depth mirror's family applied at the same call
-- arguments" exactly as asked.  `j′ ≤ j + j′ ≤ opIterD (...)` is the
-- one arithmetic step (`m≤n+m`) separating subscribeE-caps' own
-- receipt from the shape asked for here.
sub-charge : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (bud ops j : ℕ) (g : Gas) (b : Closed Γ u) (κ : Path Γ u t)
  (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c → 1 ≤ Caps.cReg c → Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  capsOK? (frameStep j c) sched st ≡ true →
  sizeᵉ b ≤ Caps.cSize (frameStep j c) →
  dWᵉ n sl b ≤ Caps.cWid (frameStep j c) →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  nest b sl (EvalSt.connectedShares st) ≤ bud →
  suc (sizeᵉ b) ≤ ops →
  let r = subscribeE g b κ bid now sched st in
  Σ ℕ λ j′ →
    (capsOK? (frameStep (j + j′) c) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
    × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
    × (burstCount? (frameStep (j + j′) c) (proj₁ r) ≡ true)
    × (j′ ≤ opIterD (Caps.cSize c) (Caps.cWid c)
                     (depthE g b κ bid now sched st) bud ops j)
sub-charge {n = n} c bud ops j g b κ bid now sl sched st
           2≤S 1≤R slEq slC slSz capOK szB dwB pκ pLen nB opsB =
  j′ , capOut , burC , burN , ≤-trans (m≤n+m j′ j) jj′≤
  where
  IH   = subscribeE-caps c (depthE g b κ bid now sched st) bud ops j g b κ
                          bid now sl sched st
                          2≤S 1≤R slEq slC slSz capOK szB dwB pκ pLen nB opsB
                          ≤-refl
  j′    = proj₁ IH
  capOut = proj₁ (proj₂ IH)
  burC  = proj₁ (proj₂ (proj₂ IH))
  burN  = proj₁ (proj₂ (proj₂ (proj₂ IH)))
  jj′≤  = proj₂ (proj₂ (proj₂ (proj₂ IH)))

------------------------------------------------------------------
-- (B3, CONTINUED) THE RECOMBINATION LEMMAS have MOVED to .Burst-Walk,
-- beside the Ψ predicates they consume, and arrive here through this
-- module's existing import of it.  They were never at home in this
-- module: it is downstream of all three of their ingredient families,
-- so stating them here put them out of reach of the one postulate that
-- most needs them (`subscribeE-inner-nodry-inv`).
------------------------------------------------------------------

------------------------------------------------------------------
-- (C) THE ASSEMBLY.  Mirrors what .Wet's `cascade-dry` did (that name is
-- GONE — absorbed here when the caps route landed) plus
-- a `capsOK?`/`valCaps?` hypothesis, concluding dryness, INV? at the
-- output, AND capsOK? at the output — the joint invariant a future
-- `cascade-dry`/`burst-wet` migrate to consume in place of the
-- old postulated cascade face — which the census then
-- retired outright (`cascadeGo-nodry` keeps only the dry half).
--
-- THE INV? ASSEMBLY CLOSED CONJUNCT-BY-CONJUNCT — no `inv-assemble`
-- fallback was needed.  stBounded? and the registry-length bound come
-- off `caps-tick`'s own conclusion via B1/B2 (transported across the
-- `sl ≡ Sched.slots sched′` fact S2 supplies); the fn face and the Ψ
-- half of regsB? come off S1; the size half of regsB? comes off
-- `caps-tick`'s conclusion too (capsOK?'s own `regsSz?` conjunct,
-- recombined with S1's Ψ half via `regsB?-of-parts`); the two slots
-- conjuncts widen the INPUT's own INV? hypothesis across the tick
-- (`sizeCapAt-mono`) and transport it across S2's slots equality.
------------------------------------------------------------------

-- THE NESTING INVARIANT RIDES THE TICK exactly as `capsOK?` does — in as
-- a premise at `id`, out as a conjunct at `suc id` — because that is the
-- only shape the instant loop can carry.  `nest-tick` is the
-- preservation obligation, and it is a BODY: the cap arithmetic is
-- discharged here against `nestCapAt`'s own step equation, leaving
-- `store-growth` as the single leaf.  What that split buys is that the
-- leaf mentions no cap at all — it relates the store before an instant
-- to the store after, and the bet is legible without the recurrence in
-- the way.  It also makes the fit CHECKED: the body reduces, so the day
-- the leaf is proven is the day we learn it was the right leaf.

-- THE MEASURE IS RAW AND THE INCREMENT IS REAL-DENOMINATED, and both
-- halves are forced.  The count-parametric predecessor read the store
-- at the instant's own fold count at both ends, so the step paid for a
-- store measured at a count it never charged: at a program with one
-- shared slot whose def is a scan, the cap collapsed to a square of the
-- entry count and the statement FORCED the count itself to at most
-- square per instant — while the width the count reads steps by
-- `foldStep S w = S ^ suc w` per fold, a tower.  The witness that
-- machine-refuted it: one shared slot whose def is a scan under a
-- `mergeAllᵉ`, at the first tick, with the cap computing to the square.
-- And no other count can serve, because the squeeze is not about which
-- index: any increment denominated in a cap-side quantity must fit
-- under the fuel that quantity itself defines, and the count exceeds
-- its fuel by construction.  So the increment is priced by
-- `realWidAt` — per-node folds are per-node deliveries, which are REAL
-- burst widths, exponential per instant where every cap-side currency
-- towers.  `store-growth` is exactly that bet with the arithmetic
-- lifted off it.

-- AND THE LOAD-BEARING REGION IS THE FIRST STEP ONLY, which is worth
-- knowing before anyone spends a probe on the leaf at a later one.
-- `Harness.Main`
-- Series N evaluates this currency at a small program — the compiled
-- calculator, so the seal is no obstacle there — and the cap goes 3 at
-- entry to 66 after one instant, an increment of 63.  That is a real
-- constraint a run can violate.  By the next instant the increment is
-- the width raised to the cap, ninety digits of it, so any row asking
-- whether a store fits under THAT could not have failed: later
-- instants are degenerate, and a receipt claiming them would be
-- claiming coverage nothing bought.

-- WHAT THE SWEEP FOUND, AND THE HOLE IN IT.  `Harness.Main`'s N-sweep
-- runs the scan family whose fold wraps its accumulator a level deeper
-- per value, and the store's depth after the instant comes out at
-- exactly the product of the two parameters while the allowance comes
-- out a product of `capsBase` and `nestSyn` — so the margin WIDENS in
-- both, and it widens for a structural reason rather than a numerical
-- one: the allowance multiplies two program-shaped quantities where
-- the growth is linear in each.  Nothing was refuted.

-- THE SHARED-SLOT ARM IS THE ONE THAT KILLED THE PREDECESSOR, AND IT
-- IS NOW REACHED.  The scan family's slots are EMPTY, so `slotsNestSum`
-- is zero there and the arm is never entered — while the witness that
-- machine-refuted the count-parametric currency was precisely a shared
-- slot whose def is a scan under a `mergeAllᵉ`.  `Harness.Main`'s
-- S-sweep puts a def of that shape in slot 0 and varies its depth and
-- length independently of the root's.  The arm is not merely entered
-- but LOAD-BEARING: at the deepest def the sweep reaches, the store's
-- value IS the slot's nesting, the other three arms contributing
-- nothing.  Every row still fits, and the margin widens the same way.

-- WHAT REMAINS UNCOVERED IS THE INSTANT, NOT THE ARM.  Both sweeps
-- measure the ROOT SUBSCRIBE frame, and this statement's instant is a
-- DELIVERY — so they constrain the currency where it is seeded and
-- leave the step it is stated about indicative only.  A cascade sweep
-- is what would close that, and it needs an arrival the harness can
-- build.
postulate
  store-growth : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id)
    (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl →
    capsOK? (capsAt e sl id) sched st ≡ true →
    nestOK? e sl id sched st ≡ true →
    nestDᵛ (arrTy a) (arrVal a) ≤ nestCapAt e sl id →
    let r = cascade a nextId sched st
    in storeNestMax (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
         ≤ storeNestMax sched st + realWidAt e sl id * nestSyn e sl

nest-tick : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (capsAt e sl id) sched st ≡ true →
  nestOK? e sl id sched st ≡ true →
  nestDᵛ (arrTy a) (arrVal a) ≤ nestCapAt e sl id →
  let r = cascade a nextId sched st
  in nestOK? e sl (suc id) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true
nest-tick {e = e} sl id a nextId sched st hsl hcaps hnest hval =
  nestOK?-intro e sl (suc id)
    (proj₁ (proj₂ (cascade a nextId sched st)))
    (proj₂ (proj₂ (cascade a nextId sched st)))
    (subst (storeNestMax (proj₁ (proj₂ (cascade a nextId sched st)))
                         (proj₂ (proj₂ (cascade a nextId sched st))) ≤_)
           (sym (nestCapAt-suc e sl id))
           (≤-trans
             (store-growth sl id a nextId sched st hsl hcaps hnest hval)
             (+-monoˡ-≤ (realWidAt e sl id * nestSyn e sl)
                        (nestOK?-store e sl id sched st hnest))))

cascade-wet-via-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (id : Id) (sched : Sched Γ) (st : EvalSt e) →
  let sl = Sched.slots sched
      Ψ  = ΨAt e sl
      B  = sizeCapAt e sl id
  in INV? Ψ B sched st ≡ true →
     valB? B Ψ (arrTy a) (arrVal a) ≡ true →
     capsOK? (capsAt e sl id) sched st ≡ true →
     nestOK? e sl id sched st ≡ true →
     nestDᵛ (arrTy a) (arrVal a) ≤ nestCapAt e sl id →
     valCaps? (capsAt e sl id) sl (arrTy a) (arrVal a) ≡ true →
     let r    = cascade a id sched st
         sl′  = Sched.slots (proj₁ (proj₂ r))
         Ψ′   = ΨAt e sl′
         Ŝ    = sizeCapAt e sl′ (suc id)
     in (hasDry (proj₁ r) ≡ false)
        × (INV? Ψ′ Ŝ (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
        × (capsOK? (capsAt e sl′ (suc id))
                   (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
        × (nestOK? e sl′ (suc id)
                   (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
cascade-wet-via-caps {e = e} a id sched st inv val pre nok harr valC =
  dry , invOut , capsOut , nestOut
  where
  sl     = Sched.slots sched
  Ψ      = ΨAt e sl
  B      = sizeCapAt e sl id
  r      = cascade a id sched st
  sched′ = proj₁ (proj₂ r)
  st′    = proj₂ (proj₂ r)
  sl′    = Sched.slots sched′
  Ψ′     = ΨAt e sl′
  Ŝ      = sizeCapAt e sl′ (suc id)

  dry : hasDry (proj₁ r) ≡ false
  dry = dry-tick a id sched st inv val pre nok harr valC

  -- S2, instantiated: the output's slots equal the entry's
  slEq : sl′ ≡ sl
  slEq = slots-tick a id sched st

  ŜEq : Ŝ ≡ sizeCapAt e sl (suc id)
  ŜEq = cong (λ s → sizeCapAt e s (suc id)) slEq

  ΨEq : Ψ′ ≡ Ψ
  ΨEq = cong (ΨAt e) slEq

  B≤Ŝ : B ≤ Ŝ
  B≤Ŝ = ≤-trans (sizeCapAt-mono e sl id) (≤-reflexive (sym ŜEq))

  -- caps-tick, at the entry `sl` it is stated against, then
  -- transported to `sl′` via S2 so it can feed INV? at the level INV?
  -- (which reads Sched.slots sched′ = sl′ directly) actually needs
  capsOut : capsOK? (capsAt e sl′ (suc id)) sched′ st′ ≡ true
  capsOut =
    subst (λ s → capsOK? (capsAt e s (suc id)) sched′ st′ ≡ true) (sym slEq)
          (caps-tick (λ {n′} {Γ′} {t′} {e′} {u′} →
                        subscribeInner-caps {n′} {Γ′} {t′} {e′} {u′})
                     (λ {n′} {Γ′} {t′} {e′} {s′} →
                        innerFinish-caps {n′} {Γ′} {t′} {e′} {s′})
                     sl id a id sched st refl pre nok harr valC)

  nestOut : nestOK? e sl′ (suc id) sched′ st′ ≡ true
  nestOut =
    subst (λ s′ → nestOK? e s′ (suc id) sched′ st′ ≡ true) (sym slEq)
          (nest-tick sl id a id sched st refl pre nok harr)

  capsParts = capsOK?-parts (capsAt e sl′ (suc id)) sched′ st′ capsOut

  -- conjunct 1 : stBounded?.  Definitionally at Ŝ by B1.
  stB : stBounded? Ŝ sched′ st′ ≡ true
  stB = proj₁ capsParts

  -- conjunct 2 : fnCapBounded?, from S1
  fnB : fnCapBounded? Ψ′ sched′ st′ ≡ true
  fnB = proj₁ (fn-tick a id sched st inv val)

  -- conjunct 3 : registry length ≤ B, via capsOK?'s cReg bound (B2)
  -- transported to cSize (B1)
  lenOK : (length (EvalSt.registry st′) ≤ᵇ Ŝ) ≡ true
  lenOK = T⇒≡true _
    (≤⇒≤ᵇ (≤-trans (capsOK?-count (capsAt e sl′ (suc id)) sched′ st′ capsOut)
                   (B2-cReg≤cSize e sl′ (suc id))))

  -- conjunct 4 : regsB?, the size half from capsOK?'s regsSz? (B1),
  -- the Ψ half from S1, recombined
  regSz : regsSz? Ŝ (EvalSt.registry st′) ≡ true
  regSz = proj₁ (proj₂ capsParts)

  regBΨ : regsBΨ? Ψ′ (EvalSt.registry st′) ≡ true
  regBΨ = proj₂ (fn-tick a id sched st inv val)

  regB : regsB? Ŝ Ψ′ (EvalSt.registry st′) ≡ true
  regB = regsB?-of-parts (EvalSt.registry st′) regSz regBΨ

  -- conjuncts 5, 6 : the slots bounds, widened across the tick
  -- (sizeCapAt-mono) from the INPUT's own INV? hypothesis, then
  -- transported from `sl` to `sl′` via S2
  invParts = INV-parts Ψ B sched st inv
  ss-in : (slotsSize sl ≤ᵇ B) ≡ true
  ss-in = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ invParts))))
  sf-in : (slotsFnCap sl ≤ᵇ Ψ) ≡ true
  sf-in = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ invParts))))

  ssOut : (slotsSize sl′ ≤ᵇ Ŝ) ≡ true
  ssOut = trans (cong (λ v → v ≤ᵇ Ŝ) (cong slotsSize slEq))
                (≤ᵇ-widen (slotsSize sl) B≤Ŝ ss-in)

  sfOut : (slotsFnCap sl′ ≤ᵇ Ψ′) ≡ true
  sfOut = trans (cong₂ _≤ᵇ_ (cong slotsFnCap slEq) ΨEq) sf-in

  invOut : INV? Ψ′ Ŝ sched′ st′ ≡ true
  invOut = ∧-intro stB (∧-intro fnB (∧-intro lenOK (∧-intro regB (∧-intro ssOut sfOut))))

------------------------------------------------------------------
-- (D) THE THREADED TOP OF THE TOWER.  MOVED here from .Wet
-- (the upside-down ruling) — this
-- is not a copy beside `drain-dry`/`budget-sufficient`,
-- it IS them, generalised to also carry `capsOK?` beside `INV?` through
-- the fuel loop.  `.Wet` cannot state this (it imports `.Wet`... no —
-- it cannot consume `cascade-wet-via-caps`, since `.Caps-Bridge` imports
-- `.Wet` and not the other way around), so the top of the tower had to
-- move UP to where `cascade-wet-via-caps` already lives, not down to
-- where the cascade dry face does.  `.Wet` keeps `burst-dry`/
-- `burst-bounded`/`pop-INV`/`pop-head-bounded` — this module consumes
-- all five, unchanged, as the INV?-only half of its own burst and pop.
--
-- REHEARSED in ``git show 94a5a3c^:agda/probe/Caps-Thread-Probe.agda`` as
-- `drain-dry-threaded`/`budget-sufficient-threaded`; landed here under
-- their FINAL names (`drain-dry`, `budget-sufficient`) since they
-- replace, not sit beside, `.Wet`'s versions of the same name.
------------------------------------------------------------------

-- § 1  THE HEAD, WIDTH HALF.  capsOK?'s `widLive` conjunct, extracted
-- at the popped arrival — the width sibling of GAP 3's
-- schedHeadOf-head/schedGo-head.
--
-- NOTE ON `cOK`: the first attempt named this hypothesis `caps` and
-- Agda rejected the LHS with "caps is not a constructor of the
-- datatype _≡_".  CAUSE, confirmed: `caps` IS a constructor in scope —
-- it is the `Caps` record's own constructor (.Caps,
-- `constructor caps`) — so in a pattern the name resolves to that
-- constructor instead of binding fresh.  Same family as the
-- PatternShadowsConstructor warning `make agda-all` prints for
-- CLI/Encode.agda's `dried`, except fatal here because the argument's
-- type is `_≡_` and `caps` belongs to a different datatype.  Any
-- lowercase record-constructor name is a landmine as a variable:
-- `caps`, `slots`, `sched` are all worth checking before use.

schedHeadOf-widHead : ∀ {n} {Γ : Ctx n} (W : ℕ) (sl : Slots Γ) (l : LiveSource Γ)
  {a : Arrival Γ} {l′ : LiveSource Γ} →
  schedHeadOf l ≡ inj₂ (a , l′) →
  widLive W sl l ≡ true →
  (pWᵛ n sl (arrTy a) (arrVal a) ≤ᵇ W) ≡ true
schedHeadOf-widHead W sl l eq bnd with LiveSource.pending l | eq | bnd
... | (t , v) ∷ ps | refl | bnd′ = proj₁ (∧-true _ _ bnd′)

schedGo-widHead : ∀ {n} {Γ : Ctx n} (W : ℕ) (sl : Slots Γ) (ls : List (LiveSource Γ))
  {a : Arrival Γ} {ls′ : List (LiveSource Γ)} →
  schedGo ls ≡ inj₂ (a , ls′) →
  all (widLive W sl) ls ≡ true →
  (pWᵛ n sl (arrTy a) (arrVal a) ≤ᵇ W) ≡ true
schedGo-widHead W sl (l ∷ ls) eq bs
  with ∧-true (widLive W sl l) (all (widLive W sl) ls) bs
... | bl , bls with schedHeadOf l in eqH | schedGo ls in eqR
schedGo-widHead W sl (l ∷ ls) refl bs | bl , bls | inj₁ _ | inj₂ (a′ , ls″) =
  schedGo-widHead W sl ls eqR bls
schedGo-widHead W sl (l ∷ ls) refl bs | bl , bls | inj₂ (a″ , l′) | inj₁ _ =
  schedHeadOf-widHead W sl l eqH bl
schedGo-widHead W sl (l ∷ ls) eq bs | bl , bls | inj₂ (a″ , l′) | inj₂ (a′ , ls″)
  with schedEarlier a″ a′ | eq
... | true  | refl = schedHeadOf-widHead W sl l eqH bl
... | false | refl = schedGo-widHead W sl ls eqR bls

pop-head-widCaps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (sched : Sched Γ) (st : EvalSt e)
  {a : Arrival Γ} {sched′ : Sched Γ} →
  sched-next sched ≡ inj₂ (a , sched′) →
  capsOK? c sched st ≡ true →
  (pWᵛ n (Sched.slots sched) (arrTy a) (arrVal a) ≤ᵇ Caps.cWid c) ≡ true
pop-head-widCaps c sched st eq cOK
  with capsOK?-parts c sched st cOK
... | _ , _ , wl , _ , _ with schedGo (Sched.live sched) in eqL | eq
... | inj₂ (a″ , ls) | refl =
      schedGo-widHead (Caps.cWid c) (Sched.slots sched) (Sched.live sched) eqL wl

-- the joint reader the cascade dry face wants.  The SIZE half is
-- free: `sizeCapAt e sl id` IS `Caps.cSize (capsAt e sl id)` by
-- definition (.Wet), so GAP 3's pop-head-bounded already
-- supplies it; only the width half above is new content.
pop-head-valCaps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (id : Id) (sched : Sched Γ) (st : EvalSt e)
  {a : Arrival Γ} {sched′ : Sched Γ} →
  sched-next sched ≡ inj₂ (a , sched′) →
  INV? (ΨAt e (Sched.slots sched)) (sizeCapAt e (Sched.slots sched) id) sched st ≡ true →
  capsOK? (capsAt e (Sched.slots sched) id) sched st ≡ true →
  valCaps? (capsAt e (Sched.slots sched) id) (Sched.slots sched) (arrTy a) (arrVal a) ≡ true
-- `valB? B Ψ u v = (sizeᵛ u v ≤ᵇ B) ∧ (fnCapᵛ u v ≤ᵇ Ψ)` (.Measures)
-- and `valCaps? c sl u v = (sizeᵛ u v ≤ᵇ cSize c) ∧ (pWᵛ n sl u v ≤ᵇ cWid c)`
-- (.Caps-Face).  At `B = sizeCapAt e sl id = cSize (capsAt e sl id)`
-- the two FIRST conjuncts are literally the same Bool, so the size half
-- is a projection off pop-head-bounded — via ∧-true, since valB? is a
-- Bool conjunction and not a Σ (the first attempt used proj₁ directly
-- and that is what the probe caught).
pop-head-valCaps {e = e} id sched st eq inv cOK =
  ∧-intro
    (proj₁ (∧-true _ _
      (pop-head-bounded (ΨAt e (Sched.slots sched))
                        (sizeCapAt e (Sched.slots sched) id) sched st eq inv)))
    (pop-head-widCaps (capsAt e (Sched.slots sched) id) sched st eq cOK)

------------------------------------------------------------------
-- § 2  THE TAIL.  capsOK? survives a pop — the capsOK? sibling of
-- `pop-INV`.  Four of the five conjuncts are pop-bounded /
-- untouched / pop-slots-transported exactly as pop-INV's are; only
-- widLive needs a new tail-preserving induction, the same shape as
-- `pop-fnCap`'s `schedGo-fnCap`.
------------------------------------------------------------------

schedHeadOf-widLive : ∀ {n} {Γ : Ctx n} (W : ℕ) (sl : Slots Γ) (l : LiveSource Γ)
  {a : Arrival Γ} {l′ : LiveSource Γ} →
  schedHeadOf l ≡ inj₂ (a , l′) →
  widLive W sl l ≡ true → widLive W sl l′ ≡ true
schedHeadOf-widLive W sl l eq bnd with LiveSource.pending l | eq | bnd
... | (t , v) ∷ ps | refl | bnd′ = proj₂ (∧-true _ _ bnd′)

schedGo-widLive : ∀ {n} {Γ : Ctx n} (W : ℕ) (sl : Slots Γ) (ls : List (LiveSource Γ))
  {a : Arrival Γ} {ls′ : List (LiveSource Γ)} →
  schedGo ls ≡ inj₂ (a , ls′) →
  all (widLive W sl) ls ≡ true → all (widLive W sl) ls′ ≡ true
schedGo-widLive W sl (l ∷ ls) eq bnd
  with ∧-true (widLive W sl l) (all (widLive W sl) ls) bnd
... | bl , bls with schedHeadOf l in eqH | schedGo ls in eqR
schedGo-widLive W sl (l ∷ ls) refl bnd | bl , bls | inj₁ _ | inj₂ (a′ , ls″) =
  ∧-intro bl (schedGo-widLive W sl ls eqR bls)
schedGo-widLive W sl (l ∷ ls) refl bnd | bl , bls | inj₂ (a″ , l′) | inj₁ _ =
  ∧-intro (schedHeadOf-widLive W sl l eqH bl) bls
schedGo-widLive W sl (l ∷ ls) eq bnd | bl , bls | inj₂ (a″ , l′) | inj₂ (a′ , ls″)
  with schedEarlier a″ a′ | eq
... | true  | refl = ∧-intro (schedHeadOf-widLive W sl l eqH bl) bls
... | false | refl = ∧-intro bl (schedGo-widLive W sl ls eqR bls)

pop-widLive : ∀ {n} {Γ : Ctx n} (W : ℕ) (sched : Sched Γ)
  {a : Arrival Γ} {sched′ : Sched Γ} →
  sched-next sched ≡ inj₂ (a , sched′) →
  all (widLive W (Sched.slots sched)) (Sched.live sched) ≡ true →
  all (widLive W (Sched.slots sched′)) (Sched.live sched′) ≡ true
pop-widLive W sched eq h with schedGo (Sched.live sched) in eqL | eq
... | inj₂ (a″ , ls) | refl = schedGo-widLive W (Sched.slots sched) (Sched.live sched) eqL h

pop-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (sched : Sched Γ) (st : EvalSt e)
  {a : Arrival Γ} {sched′ : Sched Γ} →
  sched-next sched ≡ inj₂ (a , sched′) →
  capsOK? c sched st ≡ true → capsOK? c sched′ st ≡ true
pop-caps c sched st eq h with capsOK?-parts c sched st h
... | sb , rg , wl , wn , rl =
  ∧-intro (pop-bounded (Caps.cSize c) sched st eq sb)
  (∧-intro rg
  (∧-intro (pop-widLive (Caps.cWid c) sched eq wl)
  (∧-intro (subst (λ sl → all (λ kv → widNode (Caps.cWid c) sl (proj₂ kv)) (EvalSt.nodes st) ≡ true)
                  (sym (pop-slots sched eq)) wn)
           rl)))

------------------------------------------------------------------
-- § 3  THE ASSEMBLY.  The fuel loop and the theorem, with `capsOK?`
-- travelling beside `INV?`.
--
-- NOTE what is NOT restated here: the one-cascade step.  The wet original
-- threaded with a caps face has EXACTLY `cascade-wet-via-caps`'s
-- conclusion, character for character (above), so that step is a
-- relocation and not a proof.  Its dryness half rests on `dry-tick`,
-- which is where the ANCHOR PROBLEM sits — the postulate this route
-- trades the cascade core for.
------------------------------------------------------------------

-- Historical note: burst-caps was previously a postulate in this block.
-- The two open problems that blocked it — (i) `capsOK?` at the initial
-- state (no analogue of init-INV existed) and (ii) opIterD vs. the
-- sizeCount/capsH recurrence — are now PROVEN below ((i) at every id,
-- (ii) modulo `sizeCount-mono-d`), and burst-caps is proved as a
-- corollary of subscribeE-wet-via-caps.

------------------------------------------------------------------
-- (2) THE SUBSCRIBE-SIDE MEASURE BRIDGE, and it is now an ASSEMBLY
-- rather than a postulate — which is what gives `depth-capped`
-- (Depth-Bound) its first real consumer.
--
-- SPEND `depth-capped` AT THE PRE-BLOWUP BASE CAPS, NOT AT
-- `capsAt e ins 0`.  This is the whole content of the arrangement and
-- it is not visible from the goal, so it is written out here, at the one
-- site that spends it.  `capsAt e sl zero` is ITSELF a `frameBlowup` (.Caps;
-- `baseCaps-is-inner` below pins that by `refl`), so its `cSize` is
-- `sizeStep` iterated `sizeCount`-many times.  Routing the depth bound
-- through THAT number demands `3 · cSize (capsAt e ins 0) ≤ capsH`,
-- i.e. that `poolCount` at `M = towerℕ capsBase` dominate an
-- EXPONENTIAL of `sizeCount` at `M = S₀` — a cross-`M` growth-rate
-- argument that exists nowhere in this repo.  The one chain relating
-- the two, `capsAt-tower` (.Caps), points the WRONG WAY: it
-- gives `cSize ≤ towerℕ capsH`, and `towerℕ h ≫ h`, so it makes the
-- goal harder.  `depth-capped` quantifies over ANY caps satisfying
-- `capsOK?`; nothing forces the blown-up one.
--
-- AND THE SMALL CAPS IS THE HONEST PLACE TO STAND, because at the ROOT
-- the state is `st-init`/`sched-init`: three of `capsOK?`'s five
-- conjuncts (.Caps-Face) are then VACUOUS — empty registry
-- kills `regsSz?` and the `length … ≤ᵇ cReg` bound, empty
-- `EvalSt.nodes` kills the `widNode` sweep — and the two that survive
-- (`stBounded?`, the `widLive` sweep) are bounded by SYNTAX-level
-- ceilings, which is exactly what `baseCaps`'s fields ARE.
------------------------------------------------------------------

-- the caps `capsAt e sl zero` blows up from, named so the depth bound
-- can be taken at it.  That it IS that blowup's inner argument holds by
-- `refl` — checked as `baseCaps-is-inner` in
-- `git show 1f1730e^:agda/probe/Depth-Wire-Probe.agda`, which is where it lives because
-- nothing in the claim graph consumes it and the wiring law admits no
-- orphans here.
-- `baseCaps` and `init-capsOK?-base` MOVED OUT to
-- `Verify-Budget-Sufficient.Init-Caps`, where the postulate
-- `init-capsOK?-base-core` is DISCHARGED.  The five
-- capsOK? conjuncts are proven directly, including the one that was
-- open: `scripted`'s own `{ok : T (isData t)}` index forces `pWᵛ ≡ 0`
-- on every pending value, so the width check reads `0 ≤ᵇ cWid`.
-- The -core's eight scaffold hypotheses were kit for a route the
-- direct proof does not take, and went with it.

-- Lifts init-capsOK?-base from the small caps (baseCaps) to the actual
-- initial caps (capsAt e ins 0 = frameBlowup (baseCaps e ins) (capsBase e ins))
-- via capsOK?-mono at the ⊑ᶜ witnessed by:
--   cSize: capsAt-base-size e ins 0
--   cWid:  capsAt-base-wid e ins 0
--   cReg:  m≤m*n — frameBlowup multiplies cReg by suc (sizeCount * cSize) ≥ 1
-- This wires init-capsOK?-base to burst-caps as a real code consumer,
-- retiring the monolithic `init-capsOK?` postulate at that call site.
init-capsOK?-0 : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  capsOK? (capsAt e ins 0) (sched-init e ins) (st-init e) ≡ true
init-capsOK?-0 {n = n} e ins =
  capsOK?-mono
    (baseCaps e ins) (capsAt e ins 0)
    (sched-init e ins) (st-init e)
    ( capsAt-base-size e ins 0
    , capsAt-base-wid  e ins 0
    , m≤m*n (Caps.cReg (baseCaps e ins)) _
    )
    (init-capsOK?-base e ins)

-- The recurrence climbs in ⊑ᶜ: level id sits at frameStep 0 of itself
-- (frameStep-0), level suc id at the FULL frameStep endpoint
-- (frameStep-full composed with capsAt's own suc clause, which is
-- definitional), and frameStep-mono-j spans the two at 0 ≤ sizeCount.
-- This is what retired the `init-capsOK?-suc` postulate:
-- its recorded blocker — `capsAt e ins id` never reduces to a numeral
-- because `sizeCount` is abstract — killed only the COMPUTATIONAL
-- route.  The monotonicity route never needs a numeral: `capsOK?` is
-- monotone in the caps (capsOK?-mono) and the caps only ever widen.
-- Built PRIVATE, exported through an ABSTRACT alias — the caps axis's
-- standing normalization contract (see sizeCount's header): these are
-- PROOFS, no consumer ever unfolds them, and an unfoldable body here
-- hands VWF's conversion the whole capsOK?-mono/frameStep-mono-j proof
-- tower — measured as an OOM, twice, and VWF is green with the
-- postulate in this spot, i.e. with exactly this opacity.  The alias pattern rather than a plain
-- abstract block because the bodies lean on untyped where-bindings,
-- which abstract refuses to infer.
private
  capsAt-⊑-suc : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ)
    (id : ℕ) → capsAt e ins id ⊑ᶜ capsAt e ins (suc id)
  capsAt-⊑-suc e ins id =
    subst₂ _⊑ᶜ_ (frameStep-0 c) (frameStep-full c (capsH e ins id)) span
    where
    c = capsAt e ins id
    -- the count is pinned by hand: iterSize/iterFold match on it, so
    -- unification cannot invert `frameStep _ c` to recover it from the
    -- ⊑ᶜ endpoints
    span : frameStep 0 c ⊑ᶜ frameStep (sizeCount c (capsH e ins id)) c
    span = frameStep-mono-j c (2≤capsAt-size e ins id)
             (z≤n {n = sizeCount c (capsH e ins id)})

  -- PROVEN AT EVERY id (was: proven at 0, postulated at suc) — the
  -- id = 0 base is init-capsOK?-0 (lifting init-capsOK?-base via
  -- capsOK?-mono), and the suc case is capsOK?-mono along capsAt-⊑-suc
  -- over the induction hypothesis: the initial state never changes,
  -- only the caps widen, so `capsOK?` at level id survives to level
  -- suc id verbatim.
  init-capsOK?-go : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ)
    (id : ℕ) →
    capsOK? (capsAt e ins id) (sched-init e ins) (st-init e) ≡ true
  init-capsOK?-go e ins zero     = init-capsOK?-0 e ins
  init-capsOK?-go e ins (suc id) =
    capsOK?-mono (capsAt e ins id) (capsAt e ins (suc id))
      (sched-init e ins) (st-init e)
      (capsAt-⊑-suc e ins id)
      (init-capsOK?-go e ins id)

abstract
  init-capsOK? : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ)
    (id : ℕ) →
    capsOK? (capsAt e ins id) (sched-init e ins) (st-init e) ≡ true
  init-capsOK? = init-capsOK?-go

-- THE ROOT DEPTH BOUND, OVER THE STATE RATHER THAN THE SYNTAX.  A depth
-- bound has to be re-establishable at an emitted payload, and that is
-- what picks the currency: a payload is a STORED value, so a state
-- predicate reaches it and a syntactic size does not.  `capsOK?` is the
-- state predicate the caps ledger already carries at every level and
-- `capsH` is that ledger's own level count, so the statement below is
-- the ledger bounding the nesting it has already paid for.  Its
-- delivery-side sibling `cascade-depth-capsH` (.Caps-Face/Part7) is the
-- same statement over `depthCascade`, and one induction should cover
-- both — neither is proven, so neither is the other's precedent.
--
-- WHY IT IS CONDITIONED.  The unconditional form is false: `capsH e sl
-- id` is fixed by `e`, `sl` and `id`, while an `EvalSt e` may carry a
-- registry of any depth at all, so a state no cap has seen breaks it.
-- The premises are `subscribeE-caps`'s own, at the same level, which is
-- what lets the two meet at a call site rather than at a coincidence.

-- THE ROUTE, AND THE CIRCULARITY IT LOOKS LIKE IS NOT ONE.  A depth
-- induction has to bound its measure at states the walk STEPS to, so it
-- needs caps preservation — and `subscribeE-caps` takes a depth bound as
-- a HYPOTHESIS, which reads as a cycle.  `sub-charge` (below) is the way
-- through: it is proven, it takes no depth premise, and it gets there by
-- instantiating that hypothesis at `depthE`'s own value with `≤-refl`.
-- What it hands back is caps at the stepped state together with a level
-- bound `j′ ≤ opIterD S W (depthE g b κ …) bud ops j` — and the depth in
-- THAT bound is the source subscribe's, one chain edge down, so the
-- structural hypothesis on the source covers it.  Each clause is then:
-- bound the source by the hypothesis, spend `sub-charge` to reach the
-- burst's state, bound the frames there.
--
-- DEAD ROUTE: bounding the nesting count by the PATH LENGTH.  The
--   invariant is true and it lands in the wrong place.  `depthE g b κ …
--   + pathLen κ ≤ sizeCapAt e sl id` propagates cleanly — each re-entry
--   pushes one `from-inner` frame, so the depth falls exactly as the
--   path grows, and `pathSz?` re-establishes at the longer path out of
--   the premises with no new leaf.  But a size cap is not a height:
--   `capsAt e sl (suc id)` is `capsAt e sl id` STEPPED `sizeCount`
--   times, one `sizeStep S s = S * suc (2 * s)` each, and that count is
--   itself under `blowH`'s own pooled summand — so the size cap sits
--   exponentially ABOVE the height it would have to fit under.
--   `blowup-tower` and `capsAt-tower` bracket it from the other side,
--   at `towerℕ` of the height, which is the wrong side.  What has to
--   bound the nesting is the LEVEL count, one nesting level per caps
--   level, and that is the one-instant growth bound the `depOK` note
--   below calls new mathematics.
--   AND DO NOT PUT THE POOLED FORMULA IN A STATEMENT to get at it.
--   `blowH` is `abstract` for a measured reason — with the body visible
--   the delivery count inlines twice and squares — so the level count
--   has to be reached through the recurrence's own name.

-- FOUR CURRENCIES HAVE DIED IN THIS ONE REGION, SO THE FIFTH THING TO
-- TRY IS NOT A CURRENCY.  A bound on `depthE` read at the ENTRY
-- subject — some syntactic measure of `b`, plus some measure of the
-- entry state — has now been refuted or priced dead four times over,
-- and the four do not share an arithmetic mistake.  They share a
-- SHAPE: the bound is read where `capsOK?` is checked and spent where
-- the sweep has already deepened, so the hypothesis holds at a level
-- the conclusion is not about.  This is the one statement of the face
-- that reads a level it does not REPORT; every other one reports
-- growth, `frameStep j ↦ frameStep (j + j′)`, with `sub-charge`
-- minting the `j′` over exactly this burst.
--
-- AND THE FUEL IS NOT THE PROBLEM, WHICH IS WHY THE REPAIR IS THE
-- MECHANISM.  `capsH e sl id` is `blowH` iterated `id` times, so it
-- towers away from anything a sweep can reach and the goal is
-- astronomically true — every crossing has been in the ROUTE.  What no
-- route can cross is that the invariant's only handle on a stored
-- observable is `sizeᵛ (obs t) e ≡ sizeᵉ e` under `cSize`, a SIZE, and
-- the size cap sits exponentially above the height cap at every level:
-- `capsAt e sl (suc id)` steps the previous caps `sizeCount` times at
-- `sizeStep S s = S * suc (2 * s)` each, while `capsH` gains that same
-- count only LINEARLY through `blowH`'s pooled summand.  So the fact
-- the conclusion needs is not in the invariant at any strength, and
-- what the restatement adds is a nesting cap of its own — `nestCapAt`
-- with `nestOK?` over it (`.Nest-Store`), a per-instant recurrence read
-- at the instant's own index, in the shape `stBounded?` already has.
--
-- NOT A FOURTH `Caps` FIELD, THOUGH THAT WAS THE FIRST DESIGN.  A field
-- would get the growth-reporting property free, since every producer
-- must supply it and every consumer re-establish it — but it perturbs
-- every declaration concluding `capsOK? … ≡ true` and all of the caps
-- arithmetic, to buy a property a separately indexed predicate already
-- has: `nestOK? e sl id` is read at `id`, so per-instant preservation is
-- its own stated obligation rather than something inherited.  The cost
-- is one extra premise threaded beside the `capsAt e sl id` arguments
-- that are already at every site.
-- DEAD ROUTE: a nesting measure read at the subject, and it died by
--   DEGREE rather than by arithmetic, which is what makes it evidence
--   about every such measure.  A gadget's depth grows QUADRATICALLY in
--   ticks while a sum of syntactic measures grows linearly, so no
--   tightening of the sum could have closed it; the same measure also
--   read its widening at the UNSUBSTITUTED source, where a bare
--   payload variable weighs nothing, so two programs differing only in
--   how many literals a map consumes shared one cap against depths of
--   4 and 8.
-- DEAD ROUTE: the three-size cap, `sizeᵉ b + pathLen κ` joined with a
--   store maximum, conditioned on `capsOK?`.  Refuted: the multiple of
--   `cSize` is a CONSTANT while the gap under it is a PRODUCT, and the
--   deeply nested value is a scan's stored accumulator — which
--   `boundedNode` bounds by `cSize` at the entry state, where the
--   nodes are empty.  Crossed at seven wraps over twenty-nine ticks,
--   204 against 201.
-- DEAD ROUTE: the WIDTH measures, and this is the one that reads alive
--   from the clause.  `innWⱽ`/`pmIⱽ` each carry an exponential at a
--   `scanᵉ`, which looks like the missing per-wrap charge — but the
--   base is `pmIᵗⱽ … 0 f ⊔ 1`, and a step function that re-wraps its
--   accumulator has that at exactly 1, so the family is blind to the
--   wrap count.  Refuted against the MAX of all four measures at once,
--   24 against a depth of 49.  Width is how many payloads travel
--   abreast; a wrap deepens ONE payload.
-- RECOVERY: `git show 555ee43^:agda/src/Verify-Budget-Sufficient/Depth-Bound.agda`
--   holds the three-size assembly and, PROVEN under it, the inversion a
--   record-carried nesting cap will want back: `storeNest-capped` reads
--   `capsOK?`'s own conjuncts, and `foldr-⊔-bounded` /
--   `node-nest-bounded` / `nodesNestMax-bounded` take a `boundedNode`
--   test to a `⊔`-measure bound.  Only its slot half broke, on a
--   measure that paid a def's nesting.
-- RECOVERY: `git show c3a51ea^:agda/src/Verify-Budget-Sufficient/Depth-Compositional.agda`
--   holds the nesting-currency face at its high-water mark — sixteen
--   real clauses over `nestDᵉ` (`Rx/Nest-Depth.agda` at the same sha),
--   the seven `emit-*` leaves and `emit-cap`, `depth-μ-bound` and
--   `depth-subst-guarded`.  The clause census transfers to any
--   successor: it traces every head of the depth family to the channel
--   that funds it, and the `*All` burst arm is where a per-wrap charge
--   has to go.

-- WHY THE PREDECESSOR IS GONE, AND WHY A SIZE PREMISE DOES NOT REPAIR
-- IT.  `depth-hop` bounded this by `hopDᵉ V η b + pathNestD κ`, and
-- every arm needed a payload's synchronous size under `V`.  `V` cannot
-- carry that: it is `hopDᵉ`'s refold EXPONENT, so a ceiling on the
-- conclusion forces it small on any program carrying a scan, while
-- substitution multiplies a payload's synchronous size by the
-- function's occurrence count at every level of re-entry.  Nor may `V`
-- grow with the level — the measure joins a payload's depth into its
-- SOURCE's bound, so the recursive call is at the OUTER `V` and a
-- level-indexed cap cannot compose.  `hopDᵉ` itself survives, as the
-- DEMAND measure the budget must cover (`caps-fuel-root`, .Wet/Part6);
-- what died is the claim that it also bounds `depthE`.
-- DEAD ROUTE: the supplier itself.  The burst face's synchronous-size
--   conjunct was where the condition at a payload was to have come
--   from, and it was machine-refuted at a map whose function names its
--   argument twice — 22 units of payload against a 21-unit budget, on
--   a step that pays ADDITIVELY for a function substitution multiplies
--   by.  Both the conjunct and its refutation are gone from the tree,
--   the refutation because `src` can no longer state it; the sha below
--   holds them.
-- DEAD ROUTE: a gas-indexed bound, dying by arithmetic rather than by
--   shape.  `budgetAt` is a `gasTower` at height `3 + capsHgo m (suc
--   id)`, a tower ABOVE the target, so a bound in the gas lands nowhere
--   near `capsH` however tight the induction behind it is.
-- RECOVERY: `git show 58f813a:agda/src/Verify-Budget-Sufficient/Depth-Compositional.agda`
--   restores the hop-currency depth face.  All ten of its mutual
--   clauses have real bodies and every one is an induction over the
--   same measure family this statement is about, so the clause skeleton
--   transfers even though the bound does not.  `Hop-Burst-Face.agda`
--   (the five arms), `hopD-le-tower`/`hop≤capsH`, and the
--   `Refuted.Depth-Hop` / `Refuted.Hop-Burst-Sync` / `Probed.Depth-Hop`
--   evidence are in the same tree at that sha.
-- RECOVERY: `git show 58f813a:agda/src/Verify-Budget-Sufficient/Caps.agda`
--   restores the TAIL of that module — the pool's growth-rate argument
--   and the nineteen lemmas under it, ending in `tower-le-blowH k m`,
--   which is the only handle anything has ever had on `blowH` and hence
--   on `capsH`.  It went out with the depth face because that face was
--   its one consumer; whatever proves the statement above will want it
--   back, or will want to know why a tower height is the wrong
--   decomposition.  The argument in the header there is the part that
--   took two passes: one level step at least exponentiates and
--   `poolBody` iterates it `towerℕ m` times, so `towerℕ k ≤ poolCount
--   (towerℕ m) m` for every `k` the width machinery can reach, not
--   merely for `k = m`.
-- RECOVERY: `git show 725296e:agda/src/Verify-Budget-Sufficient/Nest-Tower.agda`
--   restores height arithmetic that is currency-INDEPENDENT and will be
--   wanted again whatever the decomposition: `sum2H`/`sum3H`/`sucH`/
--   `hUp`/`hIn`/`1≤3x`/`payL`/`payR` for moving a bound up a tower,
--   `tower-sum-tab` for a slot telescope, and `entryCeil-slotWid`.

------------------------------------------------------------------
-- ONE LEAF, and the split is where the work now divides.  What is
-- postulated here is the whole of the depth induction and it says nothing
-- about caps: a sweep's depth is under the nesting of its subject, of the
-- path it climbs, of the store it may be handed observables from — all
-- three RAW, read at the instant's entry — plus the instant's own fresh
-- growth, `realWidAt · nestSyn`, because the walk subscribes
-- accumulators its own folds have deepened since the entry reading, and
-- no entry-state measure can see those layers.  The fresh term is
-- real-denominated by the module's law: per-node folds are per-node
-- deliveries, and deliveries are real burst widths, never a cap-side
-- count.  The `capsOK?` premise is retained because the induction's
-- fresh-mint bookkeeping is expected to spend the walk's receipts.
--
-- The arithmetic half is not here and not mirrored: `nest-sum-3`
-- (.Nest-Store) pays three quantities each under `nestCapAt`, plus the
-- fresh term, out of `capsH`, and the delivery side spends the same
-- lemma.
--
-- RECOVERY: `git show 4c4b120:agda/evidence/probed/Probed/Nest-Depth.agda`
--   restores the count-parametric predecessor's probe harness —
--   twenty-one rows pinning the measure EQUAL to `depthE` on the
--   wrap/fold family, with the running-state plumbing and the
--   duplication witness that keeps the payload-list clause a `⊔`.  The
--   rows are evidence about the RESTATED-AWAY statement; the harness
--   and the row inventory transfer.
postulate
  depth-nest-compositional : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (sl : Slots Γ) (id : ℕ) (g : Gas) (b : Closed Γ u) (κ : Path Γ u t)
    (bid : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl →
    capsOK? (capsAt e sl id) sched st ≡ true →
    depthE g b κ bid now sched st
      ≤ nestDᵉ b + pathNestD κ
        + storeNestMax sched st
        + realWidAt e sl id * nestSyn e sl

-- THE ENTRY STATE SATISFIES THE NESTING INVARIANT, which is the mirror
-- of `init-capsOK?` and owed a real proof: no node and no registration
-- exists yet, so the store's nesting is its slots' plus its scripts', and
-- a scripted slot is obs-free by construction.  What blocks it today is
-- that `isData` discharges by unification at a CONCRETE type, so a live
-- pending value at a variable type does not reduce to nesting zero
-- without an inversion the module does not yet carry.
postulate
  init-nestOK? : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ)
    (id : ℕ) → nestOK? e ins id (sched-init e ins) (st-init e) ≡ true

subscribe-depth-capsH : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sl : Slots Γ) (id : ℕ) (g : Gas) (b : Closed Γ u) (κ : Path Γ u t)
  (bid : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (capsAt e sl id) sched st ≡ true →
  nestOK? e sl id sched st ≡ true →
  nestDᵉ b ≤ nestCapAt e sl id →
  pathNestD κ ≤ nestCapAt e sl id →
  depthE g b κ bid now sched st ≤ capsH e sl id
subscribe-depth-capsH {e = e} sl id g b κ bid now sched st sleq cok nok hb hk =
  ≤-trans (depth-nest-compositional sl id g b κ bid now sched st sleq cok)
          (nest-sum-3 e sl id _ _ _ hb hk
            (nestOK?-store e sl id sched st nok))

-- AT THE ROOT both subject premises are the trivial ones: `pathNestD` of
-- `root` is zero, and the cap's base is the subject's own nesting plus
-- the slots'.
depthE≤capsH-root : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  depthE (budgetAt e ins 0) e root 0 0 (sched-init e ins) (st-init e)
    ≤ capsH e ins 0
depthE≤capsH-root e ins =
  subscribe-depth-capsH ins 0 (budgetAt e ins 0) e root 0 0
    (sched-init e ins) (st-init e)
    refl
    (init-capsOK? e ins 0)
    (init-nestOK? e ins 0)
    (subst (nestDᵉ e ≤_) (sym (nestCapAt-0 e ins))
       (≤-trans (m≤m+n (nestDᵉ e)
                       (slotsNestSum ins))
                (n≤1+n _)))
    z≤n

-- (3) SUBSCRIBEE-WET-VIA-CAPS — P1's subscribe-side mirror.
-- Mirrors cascade-wet-via-caps structurally.  Its wet hypotheses are
-- `subscribeE-wet`'s (.Walk-Level); the caps additions are `capsOK?` at
-- the entry level and `dWᵉ ≤ cWid`; `burst-caps` below is a closed
-- corollary at the root call, and it is where `depthE≤capsH-root`
-- (above) is spent — on the root instance of the depOK premise.

-- sizeCount-mono-d is a real proof in Verify-Budget-Sufficient.Level-Mono,
-- imported above.

-- THE SUBSCRIBE-SIDE CAPS LIFT, and it is PROVEN — the
-- `sub-charge-capsOK-lift-core` postulate is replaced outright.
-- What made it provable is the LAST premise, depOK: the general-id
-- depth bound `depthE … ≤ capsH e sl id`, supplied by the caller.  A
-- premise is not a weakening here — `subscribe-depth-capsH` (above) IS
-- that bound, at the same level and off the same `capsOK?` — and it is
-- what keeps this lemma independent of the depth induction: the two
-- meet at a call site, and `burst-caps` is where the root instance is
-- met.  The state-free form is false, a state being free to carry a
-- registry no cap has seen, which is why the bound reads a LEVEL and
-- not only the syntax.
--
-- ITS PRESERVATION STEP IS A ONE-INSTANT DEPTH-GROWTH BOUND: depth
-- data at ≤ h grows to ≤ blowH h in one instant, riding the recurrence
-- `capsH e sl (suc id) = blowH (capsH e sl id)` (`blowH` is BY DESIGN
-- "the worst one instant's cascades can do").  It is not stated as a
-- postulate until an induction consumes it.
-- DEAD ROUTE: charging the growth at the state's OWN caps instead.
--   That is off by "towerℕ of" at every index, and no index shift
--   closes the gap — see (2) below, where the same arithmetic is spent
--   the other way round.

-- THE CHAIN, every link named: jB puts j′ under the walk receipt
-- `opIterD S W dep k m 0`; opIterD-dominated (with nestOK/opsOK
-- supplying k ≤ S / m ≤ S, and 2≤capsAt-size / 1≤capsAt-reg free)
-- lands the receipt in `lvls S W dep 0 (cDel c dep)`, which IS
-- `sizeCount c dep` by sizeCount-body and record eta (`caps S W R`
-- with the fields read off c is definitionally c); sizeCount-mono-d
-- over depOK climbs the fuel from dep to `capsH e sl id`, i.e. to
-- `capsAt-suc-full`'s exact j-argument; frameStep-mono-j turns the
-- arithmetic into `frameStep j′ c ⊑ᶜ capsAt e sl (suc id)`; and
-- capsOK?-mono carries capOK across it.
-- Built PRIVATE, exported through an ABSTRACT alias — same
-- normalization contract as init-capsOK? above: the body reaches
-- opIterD-dominated and the lvls-mono tower, and no consumer ever
-- needs more than the type.
private
  sub-charge-capsOK-lift-go : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) (j′ : ℕ) →
    let sl = Sched.slots sched
        c  = capsAt e sl id
        r  = subscribeE g b κ id now sched st
    in capsOK? (frameStep j′ c) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true →
       j′ ≤ opIterD (Caps.cSize c) (Caps.cWid c)
                    (depthE g b κ id now sched st)
                    (nest b sl (EvalSt.connectedShares st))
                    (suc (sizeᵉ b)) 0 →
       3 + nest b sl (EvalSt.connectedShares st) ≤ Caps.cSize c → -- nestOK
       suc (sizeᵉ b) ≤ Caps.cSize c →                             -- opsOK
       depthE g b κ id now sched st ≤ capsH e sl id →             -- depOK
       capsOK? (capsAt e sl (suc id))
               (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true
  sub-charge-capsOK-lift-go {e = e} g b κ id now sched st j′
                            capOK jB nestOK opsOK depOK =
    capsOK?-mono (frameStep j′ c) (capsAt e sl (suc id))
      (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) lift-⊑ capOK
    where
    sl  = Sched.slots sched
    c   = capsAt e sl id
    r   = subscribeE g b κ id now sched st
    dep = depthE g b κ id now sched st
    S   = Caps.cSize c
    W   = Caps.cWid c
    hS  = 2≤capsAt-size e sl id

    j≤full : j′ ≤ sizeCount c (capsH e sl id)
    j≤full =
      ≤-trans jB
      (≤-trans (opIterD-dominated S W dep
                  (nest b sl (EvalSt.connectedShares st)) (suc (sizeᵉ b))
                  (Caps.cReg c)
                  hS nestOK opsOK (1≤capsAt-reg e sl id))
      (≤-trans (≤-reflexive (sym (sizeCount-body c dep)))
               (sizeCount-mono-d c hS depOK)))

    lift-⊑ : frameStep j′ c ⊑ᶜ capsAt e sl (suc id)
    lift-⊑ = subst (λ x → frameStep j′ c ⊑ᶜ x)
                   (sym (capsAt-suc-full e sl id))
                   (frameStep-mono-j c hS j≤full)

abstract
  sub-charge-capsOK-lift : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) (j′ : ℕ) →
    let sl = Sched.slots sched
        c  = capsAt e sl id
        r  = subscribeE g b κ id now sched st
    in capsOK? (frameStep j′ c) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true →
       j′ ≤ opIterD (Caps.cSize c) (Caps.cWid c)
                    (depthE g b κ id now sched st)
                    (nest b sl (EvalSt.connectedShares st))
                    (suc (sizeᵉ b)) 0 →
       3 + nest b sl (EvalSt.connectedShares st) ≤ Caps.cSize c → -- nestOK
       suc (sizeᵉ b) ≤ Caps.cSize c →                             -- opsOK
       depthE g b κ id now sched st ≤ capsH e sl id →             -- depOK
       capsOK? (capsAt e sl (suc id))
               (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true
  sub-charge-capsOK-lift = sub-charge-capsOK-lift-go

-- THE SUBSCRIBE-SIDE ASSEMBLY.  A real definition, and the reason
-- `sub-charge` (above, PROVEN) is no longer an orphan.
--
-- IT DOES NOT REPLACE P1 — IT RESTS ON IT.  `hasDry` and `INV?` come
-- straight out of `subscribeE-wet` (Wet.agda, P1); this adds only the
-- third conjunct, `capsOK?` at `suc id`.  So read the caps route's
-- subscribe side as "P1 PLUS a caps conclusion", not as an alternative
-- to P1.  An earlier plan had this mirroring P1 rather than consuming
-- it; that would need `hasDry`/`INV?` re-derived from the caps face,
-- which nothing here does.
--
-- THE TWO PATH HYPOTHESES ARE NEW, and they are load-bearing.
-- `pathB?` carries NO length conjunct
-- (`pathB? B Ψ (f ↠ p) = frameB? B Ψ f ∧ pathB? B Ψ p`) while `pathSz?`
-- requires `suc (pathLen p) ≤ᵇ B` at every suffix — so deriving the
-- latter from the former is not merely unproven, it is FALSE: take a
-- tiny `e` (small `B`), a tiny `b`, and a long chain of `map-f` frames
-- with small step functions, and every hypothesis holds while the
-- conclusion fails.  The information has to be supplied, and it is free
-- at the only call site (`κ := root`, below).
subscribeE-wet-via-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) →
  let sl = Sched.slots sched
      Ψ  = ΨAt e sl
      B  = sizeCapAt e sl id
      Ŝ  = sizeCapAt e sl (suc id)
  in INV? Ψ B sched st ≡ true →
     pathB? B Ψ κ ≡ true →
     pathSz? B κ ≡ true →
     suc (pathLen κ) ≤ B →
     sizeᵉ b ≤ B →
     fnCapᵉ b ≤ Ψ →
     g hasAtLeast
       suc (dBound Ŝ (hopR Ŝ)
                   (unconn sl (EvalSt.connectedShares st))
                   (hopDᵉ Ŝ (slotHop Ŝ sl) b) (syncSizeᵉ b)) →
     capsOK? (capsAt e sl id) sched st ≡ true →
     dWᵉ n sl b ≤ Caps.cWid (capsAt e sl id) →
     3 + nest b sl (EvalSt.connectedShares st) ≤ B →       -- nestOK
     suc (sizeᵉ b) ≤ B →                                   -- opsOK
     depthE g b κ id now sched st ≤ capsH e sl id →        -- depOK
     let r   = subscribeE g b κ id now sched st
         sl′ = Sched.slots (proj₁ (proj₂ r))
     in (hasDry (proj₁ r) ≡ false)
        × (INV? (ΨAt e sl′) (sizeCapAt e sl′ (suc id))
                (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
        × (capsOK? (capsAt e sl′ (suc id))
                   (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
subscribeE-wet-via-caps {n = n} {e = e} g b κ id now sched st
                        inv pathB pathSzκ lenκ szB fnB gas cOK dW
                        nestOK opsOK depOK =
  dry , invOut , capsOut
  where
  sl      = Sched.slots sched
  Ψ       = ΨAt e sl
  B       = sizeCapAt e sl id
  c       = capsAt e sl id
  r       = subscribeE g b κ id now sched st
  sched′  = proj₁ (proj₂ r)
  st′     = proj₂ (proj₂ r)

  sl′Eq : Sched.slots sched′ ≡ sl
  sl′Eq = subscribeE-slots g b κ id now sched st

  invP    = INV-parts Ψ B sched st inv
  ss-in   : (slotsSize sl ≤ᵇ B) ≡ true
  ss-in   = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ invP))))
  slotsOK : slotsSize sl ≤ Caps.cSize c
  slotsOK = ≤ᵇ⇒≤ (slotsSize sl) B (T-to ss-in)

  -- the wet face now carries the caps hypotheses too (the collapsed
  -- walk's outer instantiation reads them); every one is already a
  -- hypothesis of THIS definition, so they ride through unchanged.
  wet     = subscribeE-wet g b κ id now sched st
                           inv pathB pathSzκ lenκ szB fnB gas cOK dW
                           nestOK opsOK depOK
  dry     : hasDry (proj₁ r) ≡ false
  dry     = proj₁ wet
  invOut  : INV? (ΨAt e (Sched.slots sched′))
                 (sizeCapAt e (Sched.slots sched′) (suc id))
                 sched′ st′ ≡ true
  invOut  = proj₂ wet

  f0 = frameStep-0 c

  pκSz  : pathSz? (Caps.cSize (frameStep 0 c)) κ ≡ true
  pκSz  = subst (λ x → pathSz? (Caps.cSize x) κ ≡ true) (sym f0) pathSzκ

  pκLen : suc (pathLen κ) ≤ Caps.cSize (frameStep 0 c)
  pκLen = subst (λ x → suc (pathLen κ) ≤ Caps.cSize x) (sym f0) lenκ

  IH = sub-charge c
                  (nest b sl (EvalSt.connectedShares st))
                  (suc (sizeᵉ b))
                  0
                  g b κ id now sl sched st
                  (2≤capsAt-size e sl id)
                  (1≤capsAt-reg e sl id)
                  refl
                  (slotsCaps?-capsAt e sl id)
                  slotsOK
                  (subst (λ x → capsOK? x sched st ≡ true) (sym f0) cOK)
                  (subst (λ x → sizeᵉ b ≤ Caps.cSize x) (sym f0) szB)
                  (subst (λ x → dWᵉ n sl b ≤ Caps.cWid x) (sym f0) dW)
                  pκSz
                  pκLen
                  ≤-refl
                  ≤-refl

  j′      = proj₁ IH
  capOut  = proj₁ (proj₂ IH)
  jBound  = proj₂ (proj₂ (proj₂ (proj₂ IH)))

  capsOut₀ : capsOK? (capsAt e sl (suc id)) sched′ st′ ≡ true
  capsOut₀ = sub-charge-capsOK-lift g b κ id now sched st j′
               capOut jBound nestOK opsOK depOK

  capsOut : capsOK? (capsAt e (Sched.slots sched′) (suc id)) sched′ st′ ≡ true
  capsOut = subst (λ x → capsOK? (capsAt e x (suc id)) sched′ st′ ≡ true)
                  (sym sl′Eq) capsOut₀

-- ONE MORE UNIT OF SIZE SLACK AT EVERY BASE, and `opIterD-dominated`'s
-- repaired guard (`3 + k ≤ S`, Op-Budget) is what wants it.  Free:
-- capsAt's base is `frameBlowup c₀ _`, whose cSize is
-- `iterSize (cSize c₀) (sizeCount c₀ _) (cSize c₀)`, and 2≤sizeCount
-- says at least TWO sizeSteps run.  ONE is enough, because
-- sizeStep S S = S * suc (2 * S) ≥ S + S ≥ suc S.
-- SEALED (private impl + abstract alias): burst-caps is on the
-- budget-sufficient spine, and an unfoldable body here is what OOM'd
-- VWF.
private
 sucSize≤frameBlowup-go : ∀ (c : Caps) (d : ℕ) →
  2 ≤ Caps.cSize c → 1 ≤ Caps.cReg c →
  suc (Caps.cSize c) ≤ Caps.cSize (frameBlowup c d)
 sucSize≤frameBlowup-go c d 2≤S 1≤R =
  ≤-trans sucS≤step
          (iterSize-mono-count S S 1≤S
            (≤-trans (s≤s z≤n) (2≤sizeCount c d 2≤S 1≤R)))
  where
  S = Caps.cSize c

  1≤S : 1 ≤ S
  1≤S = ≤-trans (s≤s z≤n) 2≤S

  1≤2S : 1 ≤ 2 * S
  1≤2S = ≤-trans (s≤s z≤n)
                 (≤-trans (≤-reflexive (sym (*-identityʳ 2)))
                          (*-monoʳ-≤ 2 1≤S))

  S≤S2S : S ≤ S * (2 * S)
  S≤S2S = ≤-trans (≤-reflexive (sym (*-identityʳ S))) (*-monoʳ-≤ S 1≤2S)

  -- suc S = 1 + S ≤ S + S ≤ S + S * (2 * S) = S * suc (2 * S)
  sucS≤step : suc S ≤ sizeStep S S
  sucS≤step = ≤-trans (+-monoˡ-≤ S 1≤S)
              (≤-trans (+-monoʳ-≤ S S≤S2S)
                       (≤-reflexive (sym (*-suc S (2 * S)))))

private
 capsAt-base-size⁺-go : ∀ {n} {Γ : Ctx n} {t}
  (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  3 + sizeᵉ e + slotsSize sl ≤ Caps.cSize (capsAt e sl id)
 capsAt-base-size⁺-go {n = n} e sl zero =
  sucSize≤frameBlowup-go (caps (2 + sizeᵉ e + slotsSize sl)
                               (suc (entryCeil n sl e))
                               (suc (sizeᵉ e + slotsSize sl)))
    (capsBase e sl)
    (≤-trans (m≤m+n 2 (sizeᵉ e)) (m≤m+n (2 + sizeᵉ e) (slotsSize sl)))
    (s≤s z≤n)
 capsAt-base-size⁺-go e sl (suc id) =
  ≤-trans (capsAt-base-size⁺-go e sl id)
          (cSize≤frameBlowup (capsAt e sl id) (capsH e sl id)
             (≤-trans (s≤s z≤n) (2≤capsAt-size e sl id)))

abstract
  capsAt-base-size⁺ : ∀ {n} {Γ : Ctx n} {t}
    (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
    3 + sizeᵉ e + slotsSize sl ≤ Caps.cSize (capsAt e sl id)
  capsAt-base-size⁺ = capsAt-base-size⁺-go

-- helpers for burst-caps corollary

-- dWᵉ n ins e ≤ Caps.cWid (capsAt e ins 0)
-- Route: dW≤ceil → m≤m⊔n (ceilᵉ ≤ entryCeil) → n≤1+n → capsAt-base-wid
dWe≤cWid : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  dWᵉ n ins e ≤ Caps.cWid (capsAt e ins 0)
dWe≤cWid {n = n} e ins =
  ≤-trans (dW≤ceil n ins e)
  (≤-trans (m≤m⊔n (ceilᵉ n ins e) _)
  (≤-trans (n≤1+n _)
           (capsAt-base-wid e ins 0)))

-- sizeᵉ e ≤ sizeCapAt e ins 0
-- Route: sizeᵉ e ≤ 2+sizeᵉ+slotsSize ≤ cSize (capsAt-base-size)
sizeE≤cap : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  sizeᵉ e ≤ sizeCapAt e ins 0
sizeE≤cap e ins =
  ≤-trans (≤-trans (m≤n+m (sizeᵉ e) 2) (m≤m+n (2 + sizeᵉ e) (slotsSize ins)))
          (capsAt-base-size e ins 0)

-- THE ROOT INSTANTIATION — ONE call to subscribeE-wet-via-caps, with
-- burst-dry / burst-bounded / burst-caps as its three projections.
-- The first two used to be a SECOND root call in .Wet, against the wet
-- face's five-hypothesis form; the wet face was restated
-- over the collapsed walk (.Walk-Level) and gained the caps
-- hypotheses, which are exactly the ones this call site already had to
-- supply.  So the two calls merged rather than the second one growing.
--
-- pathLen root = 0, so suc (pathLen root) = 1 ≤ B (moot at the root).
-- `EvalSt.connectedShares (st-init e) = []` (Rx.Evaluator) and
-- `Sched.slots (sched-init e ins) = ins` (Rx.Evaluator), so the
-- premises reduce to the root bounds at (capsAt e ins 0).
--
-- RECOVERY: git show c87c91a restores the split form.
burst-all : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  let r   = subscribeE (budgetAt e ins 0) e root 0 0
                       (sched-init e ins) (st-init e)
      sl′ = Sched.slots (proj₁ (proj₂ r))
  in (hasDry (proj₁ r) ≡ false)
     × (INV? (ΨAt e sl′) (sizeCapAt e sl′ 1)
             (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (capsOK? (capsAt e sl′ 1) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
burst-all {n = n} e ins =
  subscribeE-wet-via-caps
    (budgetAt e ins 0) e root 0 0 (sched-init e ins) (st-init e)
    (init-INV e ins 0)
    refl
    refl                                          -- pathSz? B root
    (≤-trans (s≤s z≤n) (2≤capsAt-size e ins 0))   -- 1 ≤ B
    (sizeE≤cap e ins)
    (m≤m+n (fnCapᵉ e) _)
    (caps-fuel-root e ins)
    (init-capsOK? e ins 0)
    (dWe≤cWid e ins)
    nestOK
    opsOK
    (depthE≤capsH-root e ins)
  where
  -- the guard repair (`3 + k ≤ S`, Op-Budget) asks for ONE unit more
  -- than capsAt-base-size gives; capsAt-base-size⁺ supplies it
  nestOK : 3 + nest e ins [] ≤ Caps.cSize (capsAt e ins 0)
  nestOK = ≤-trans (+-monoʳ-≤ 3 (nest≤ e ins []))
                   (capsAt-base-size⁺ e ins 0)
  opsOK  : suc (sizeᵉ e) ≤ Caps.cSize (capsAt e ins 0)
  opsOK  = ≤-trans (s≤s (≤-trans (m≤m+n (sizeᵉ e) (slotsSize ins))
                                 (n≤1+n (sizeᵉ e + slotsSize ins))))
                   (capsAt-base-size e ins 0)

burst-dry : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  hasDry (proj₁ (subscribeE (budgetAt e ins 0) e root 0 0
                            (sched-init e ins) (st-init e))) ≡ false
burst-dry e ins = proj₁ (burst-all e ins)

burst-bounded : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  let r = subscribeE (budgetAt e ins 0) e root 0 0
                     (sched-init e ins) (st-init e)
  in INV? (ΨAt e (Sched.slots (proj₁ (proj₂ r))))
          (sizeCapAt e (Sched.slots (proj₁ (proj₂ r))) 1)
          (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true
burst-bounded e ins = proj₁ (proj₂ (burst-all e ins))

burst-caps : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  let r = subscribeE (budgetAt e ins 0) e root 0 0
                     (sched-init e ins) (st-init e)
  in capsOK? (capsAt e ins 1) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true
burst-caps e ins =
  subst (λ s → capsOK? (capsAt e s 1) sched₁ st₁ ≡ true) slEq
        (proj₂ (proj₂ (burst-all e ins)))
  where
  r      = subscribeE (budgetAt e ins 0) e root 0 0
                      (sched-init e ins) (st-init e)
  sched₁ = proj₁ (proj₂ r)
  st₁    = proj₂ (proj₂ r)
  slEq   : Sched.slots sched₁ ≡ ins
  slEq   = subscribeE-slots (budgetAt e ins 0) e root 0 0
                            (sched-init e ins) (st-init e)

-- POPPING PRESERVES THE NESTING INVARIANT AND EXPOSES THE HEAD'S, the
-- two mirrors of `pop-caps` and `pop-head-valCaps`.  The first is the
-- easy half — a pop removes a pending value, and a `⊔`-fold over a
-- shorter list is no larger.  The second is the one the loop cannot do
-- without: the arriving payload leaves the schedule as it arrives, so its
-- nesting has to be read off the state that still held it.
--
-- TWIN: `pop-caps` and `pop-head-valCaps`, both proven directly above,
--   are these two clause for clause — same pop equation, same transport,
--   the size predicate swapped for the nesting one.
postulate
  pop-nest : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (id : ℕ) (sched : Sched Γ) (st : EvalSt e) {a : Arrival Γ} {sched′ : Sched Γ} →
    sched-next sched ≡ inj₂ (a , sched′) →
    nestOK? e (Sched.slots sched) id sched st ≡ true →
    nestOK? e (Sched.slots sched) id sched′ st ≡ true

  pop-head-nest : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (id : ℕ) (sched : Sched Γ) (st : EvalSt e) {a : Arrival Γ} {sched′ : Sched Γ} →
    sched-next sched ≡ inj₂ (a , sched′) →
    nestOK? e (Sched.slots sched) id sched st ≡ true →
    nestDᵛ (arrTy a) (arrVal a)
      ≤ nestCapAt e (Sched.slots sched) id

-- THE BURST'S OWN NESTING RECEIPT, the mirror of `burst-caps`.  The
-- subscribe frame is the one place a run's nesting can jump without an
-- arrival driving it — every inner it subscribes is grafted from the
-- program's own syntax — so instant 1's cap is the base cap plus one
-- increment, which is what `nestCapAt`'s step supplies.
postulate
  burst-nest : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
    let r = subscribeE (budgetAt e ins 0) e root 0 0
                       (sched-init e ins) (st-init e)
    in nestOK? e ins 1 (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true

drain-dry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (fuel : Fuel) (id : Id) (sched : Sched Γ) (st : EvalSt e) →
  INV? (ΨAt e (Sched.slots sched)) (sizeCapAt e (Sched.slots sched) id)
       sched st ≡ true →
  capsOK? (capsAt e (Sched.slots sched) id) sched st ≡ true →
  nestOK? e (Sched.slots sched) id sched st ≡ true →
  hasDry (drain {e = e} fuel id sched st) ≡ false
drain-dry zero    id sched st inv cOK nOK = refl
drain-dry (suc k) id sched st inv cOK nOK with sched-next sched in eq
... | inj₁ _            = refl
drain-dry {e = e} (suc k) id sched st inv cOK nOK | inj₂ (a , sched′) =
  let Ψ = ΨAt e (Sched.slots sched)
      B = sizeCapAt e (Sched.slots sched) id
      C = capsAt e (Sched.slots sched) id
      inv′ : INV? (ΨAt e (Sched.slots sched′))
                  (sizeCapAt e (Sched.slots sched′) id) sched′ st ≡ true
      inv′ = subst
               (λ sl → INV? (ΨAt e sl) (sizeCapAt e sl id) sched′ st ≡ true)
               (sym (pop-slots sched eq))
               (pop-INV Ψ B sched st eq inv)
      val′ : valB? (sizeCapAt e (Sched.slots sched′) id)
                   (ΨAt e (Sched.slots sched′)) (arrTy a) (arrVal a) ≡ true
      val′ = subst
               (λ sl → valB? (sizeCapAt e sl id) (ΨAt e sl)
                             (arrTy a) (arrVal a) ≡ true)
               (sym (pop-slots sched eq))
               (pop-head-bounded Ψ B sched st eq inv)
      caps′ : capsOK? (capsAt e (Sched.slots sched′) id) sched′ st ≡ true
      caps′ = subst
               (λ sl → capsOK? (capsAt e sl id) sched′ st ≡ true)
               (sym (pop-slots sched eq))
               (pop-caps C sched st eq cOK)
      valC′ : valCaps? (capsAt e (Sched.slots sched′) id) (Sched.slots sched′)
                       (arrTy a) (arrVal a) ≡ true
      valC′ = subst
               (λ sl → valCaps? (capsAt e sl id) sl (arrTy a) (arrVal a) ≡ true)
               (sym (pop-slots sched eq))
               (pop-head-valCaps id sched st eq inv cOK)
      nest′ : nestOK? e (Sched.slots sched′) id sched′ st ≡ true
      nest′ = subst
               (λ sl → nestOK? e sl id sched′ st ≡ true)
               (sym (pop-slots sched eq))
               (pop-nest id sched st eq nOK)
      harr′ : nestDᵛ 
                     (arrTy a) (arrVal a)
                ≤ nestCapAt e (Sched.slots sched′) id
      harr′ = subst
               (λ sl → nestDᵛ (arrTy a) (arrVal a)
                          ≤ nestCapAt e sl id)
               (sym (pop-slots sched eq))
               (pop-head-nest id sched st eq nOK)
      (dry₁ , inv″ , caps″ , nest″) =
        cascade-wet-via-caps a id sched′ st inv′ val′ caps′ nest′ harr′ valC′
  in hasDry-append (proj₁ (cascade a id sched′ st)) _
       dry₁
       (drain-dry k (suc id)
         (proj₁ (proj₂ (cascade a id sched′ st)))
         (proj₂ (proj₂ (cascade a id sched′ st)))
         inv″
         caps″
         nest″)

-- THE THEOREM.  Same face as .Wet's `budget-sufficient` — it does not
-- move.  Only the interior changes: it now also seeds and carries
-- capsOK?, transported from `ins` to the post-burst sched's own slots by
-- subscribeE-slots.
budget-sufficient :
  ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ) →
  hasDry (evaluate fuel e ins) ≡ false
budget-sufficient fuel e ins =
  hasDry-append
    (proj₁ (subscribeE (budgetAt e ins 0) e root 0 0
                       (sched-init e ins) (st-init e)))
    _
    (burst-dry e ins)
    (drain-dry fuel 1 sched₁ st₁ (burst-bounded e ins) caps₁ nest₁)
  where
  sched₁ = proj₁ (proj₂ (subscribeE (budgetAt e ins 0) e root 0 0
                                    (sched-init e ins) (st-init e)))
  st₁    = proj₂ (proj₂ (subscribeE (budgetAt e ins 0) e root 0 0
                                    (sched-init e ins) (st-init e)))
  slEq : Sched.slots sched₁ ≡ ins
  slEq = subscribeE-slots (budgetAt e ins 0) e root 0 0
                          (sched-init e ins) (st-init e)
  caps₁ : capsOK? (capsAt e (Sched.slots sched₁) 1) sched₁ st₁ ≡ true
  caps₁ = subst (λ s → capsOK? (capsAt e s 1) sched₁ st₁ ≡ true)
                (sym slEq)
                (burst-caps e ins)
  nest₁ : nestOK? e (Sched.slots sched₁) 1 sched₁ st₁ ≡ true
  nest₁ = subst (λ s → nestOK? e s 1 sched₁ st₁ ≡ true)
                (sym slEq)
                (burst-nest e ins)
