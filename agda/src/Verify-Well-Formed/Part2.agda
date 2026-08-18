-- THE PROOF that the evaluator's output satisfies the protocol
-- automaton: evaluate-well-formed, the primitives' half of the
-- batching sandwich (see Verify-Batch-Simultaneous.The-Proof).
--
-- Architecture: a simulation, in three layers.
--   1. Inv (CONCRETE below) relates evaluator state to automaton
--      state between cascades.
--   2. Two frame relations — BurstInv (mid-subscribe-frame) and Mid
--      (mid-cascade, indexed by the chains still to fold) — both
--      CONCRETE records now, with entry/step/exit lemmas.  Proven:
--      burst-init, burst-final.  Postulated (all believed true and
--      properly hypothesised — no known-false placeholders): the
--      step lemmas
--      (subscribeE-wf, mid-step — the per-clause preservation
--      grind), mid-init, mid-skip, mid-final.  Budget sufficiency
--      is no longer assumed here: it is imported, proven, from
--      Verify-Budget-Sufficient.
--   3. The compositions — the subscribe frame, the chain fold, the
--      fuel loop, and the theorem — are all DEFINED, glued by
--      runProtocol's distribution over ++.
module Verify-Well-Formed.Part2 where

open import Data.Bool    using (Bool; true; false; if_then_else_; _∧_; _∨_; not; T)
open import Data.Bool.Properties using (∨-assoc; ∨-comm; ∨-identityʳ)
open import Data.Fin     using (Fin; toℕ)
open import Data.Vec     using (lookup)
open import Data.Nat     using (ℕ; zero; suc; _≤_; z≤n; s≤s; _≡ᵇ_; _<ᵇ_; _≤ᵇ_; _+_; _∸_)
open import Data.Nat.Properties using (≤-refl; ≤-reflexive; ≤-trans; ≤-pred; m≤n+m; 1+n≰n; ≤⇒≤ᵇ; ≤ᵇ⇒≤; +-suc; +-comm; +-assoc; +-identityʳ; +-cancelʳ-≡; m+n∸n≡m)
open import Data.List    using (List; []; _∷_; _++_; length; map)
open import Data.Bool.ListAction using (any)
open import Data.List.Properties using (++-identityʳ)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Unit    using (⊤; tt)
open import Data.Empty   using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Relation.Nullary using (Dec; yes; no)

-- from .Caps-Bridge, not from the top module: the top module is the
-- active caps grind, and importing it here would put this file on that
-- clock.  MOVED 2026-08-05 from .Wet (the 2026-08-05 upside-down ruling) — `budget-sufficient`'s TYPE did
-- not change, only which module proves it, so nothing else here needed
-- to move with it.
open import Verify-Budget-Sufficient.Caps-Bridge using (budget-sufficient)
open import Rx.Prim      using (Fuel; Gas; g0; gs; Tick; Id; Source; Ordinal; InstEmit;
                                hot; cold;
                                InstEvent; init; value; close; handoff; complete;
                                EmitKind; delivery; subscribe; plumbing; CloseReason; exhausted;
                                dried;
                                cut; cutPending; _at_from_as_)
open import Rx.Exp       using (Ctx; Closed; Ty; _≟ᵗ_; Val; Fn; obs; applyFn; mapᵉ;
                                unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_; Tm; scanᵉ; takeᵉ; evalTm;
                                input; ofᵉ; emptyᵉ; varᵉ; deferᵉ; mergeAllᵉ; concatAllᵉ;
                                switchAllᵉ; exhaustAllᵉ; μᵉ; unfoldμ)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; Slots; Slot; scripted; shared; Stream;
                                RegId; Chain; Path; root; share-sink; _↠_; Frame;
                                map-f; scan-f; take-f; from-inner; thru-outer; AllOp;
                                mergeᵒ; concatᵒ; switchᵒ; exhaustᵒ; aliveThroughᶠ;
                                takeVals; takeDispatch; cutThrough; setNode; pathHasNode; memberSource;
                                NodeId; NodeState; lookupNode; scan-st; take-st; merge-st;
                                concat-st; switch-st; exhaust-st;
                                sched-init; st-init; sched-next; LiveSource;
                                schedGo; schedHeadOf; schedFinish; schedEarlier;
                                arrTy; arrSource; arrVal; arrTick;
                                chainsOf; chainsGo; chainStep;
                                foldPath; dispatchShare; stepFrame;
                                cascadeLatch; cascadeGo; cascadeFinish;
                                subscribeE; cascade; drain; evaluate;
                                oneShotBurst; mintSource; register; splitEvents;
                                pushBurst; scanVals; installNode; mintNode; retagEvents;
                                sameSource; dryEvent; hasDry;
                                dropSource; sweepLive; budgetAt)
open import Rx.Protocol  using (ProtocolSt; Owed; countIn; allZero; protocol-init;
                                stepProtocol; runProtocol; paidUp; settle; hasOwed;
                                payOwed; paidOff; applyEvents; removeOne;
                                cancelOwed; bumpOwed; settleInstant;
                                checkFinal; Accepted; accepted; WellFormed;
                                hasValue; valsLast?)

------------------------------------------------------------------
-- glue: runProtocol distributes over ++, and a fully-paid final
-- state is accepted
------------------------------------------------------------------

open import Verify-Well-Formed.Part1 public

∧-trueˡ : ∀ {a b : Bool} → (a ∧ b) ≡ true → a ≡ true
∧-trueˡ {true} _ = refl

∧-trueʳ : ∀ {a b : Bool} → (a ∧ b) ≡ true → b ≡ true
∧-trueʳ {true} h = h

∧-intro : ∀ {a b : Bool} → a ≡ true → b ≡ true → (a ∧ b) ≡ true
∧-intro refl refl = refl

if-false : ∀ {A : Set} {x y : A} (b : Bool) → b ≡ false → (if b then x else y) ≡ y
if-false b eq rewrite eq = refl

if-true : ∀ {A : Set} {x y : A} (b : Bool) → b ≡ true → (if b then x else y) ≡ x
if-true b eq rewrite eq = refl

sameTy-sound : ∀ (a b : Ty) → sameTy a b ≡ true → a ≡ b
sameTy-sound a b h with a ≟ᵗ b
... | yes p = p
... | no  _ = true≢false (sym h)

sameTy-refl : ∀ (a : Ty) → sameTy a a ≡ true
sameTy-refl a with a ≟ᵗ a
... | yes _  = refl
... | no ¬p = ⊥-elim (¬p refl)

-- the arrival a live source pops carries its source and elemTy
schedHeadOf-match : ∀ {n} {Γ : Ctx n} (l : LiveSource Γ) {a : Arrival Γ} {l′} →
  schedHeadOf l ≡ inj₂ (a , l′) →
  (arrSource a ≡ LiveSource.source l) × (arrTy a ≡ LiveSource.elemTy l)
schedHeadOf-match l eq with LiveSource.pending l | eq
... | (t , v) ∷ ps | refl = refl , refl

-- a's source/type is present among the live sources sched-next drew from
liveHas : ∀ {n} {Γ : Ctx n} → Source → Ty → List (LiveSource Γ) → Bool
liveHas s τ []       = false
liveHas s τ (l ∷ ls) =
  ((LiveSource.source l ≡ᵇ s) ∧ sameTy τ (LiveSource.elemTy l)) ∨ liveHas s τ ls

∨-trueʳ : ∀ (x : Bool) → (x ∨ true) ≡ true
∨-trueʳ false = refl
∨-trueʳ true  = refl

-- the arrival schedGo pops is one of the live sources it drew from
schedGo-mem : ∀ {n} {Γ : Ctx n} (live : List (LiveSource Γ)) {a : Arrival Γ} {ls} →
  schedGo live ≡ inj₂ (a , ls) → liveHas (arrSource a) (arrTy a) live ≡ true
schedGo-mem (l ∷ ls) eq with schedHeadOf l in heq | schedGo ls in geq
... | inj₁ _        | inj₁ _         with eq
...   | ()
schedGo-mem (l ∷ ls) eq | inj₁ _ | inj₂ (a′ , ls′) with eq
...   | refl rewrite schedGo-mem ls geq = ∨-trueʳ _
schedGo-mem (l ∷ ls) eq | inj₂ (a₀ , l′) | inj₁ _ with eq
...   | refl rewrite proj₁ (schedHeadOf-match l heq)
                   | proj₂ (schedHeadOf-match l heq)
                   | ≡ᵇ-refl (LiveSource.source l)
                   | sameTy-refl (LiveSource.elemTy l) = refl
schedGo-mem (l ∷ ls) eq | inj₂ (a₀ , l′) | inj₂ (a′ , ls′) with schedEarlier a₀ a′ | eq
...   | true  | refl rewrite proj₁ (schedHeadOf-match l heq)
                           | proj₂ (schedHeadOf-match l heq)
                           | ≡ᵇ-refl (LiveSource.source l)
                           | sameTy-refl (LiveSource.elemTy l) = refl
...   | false | refl rewrite schedGo-mem ls geq = ∨-trueʳ _

-- a source-matching live source pins the registration's type via regTyped?
liveTypeOK?-extract : ∀ {n} {Γ : Ctx n} (s : Source) (u τ : Ty)
  (live : List (LiveSource Γ)) →
  liveTypeOK? s u live ≡ true → liveHas s τ live ≡ true → sameTy u τ ≡ true
liveTypeOK?-extract s u τ []       ok has = true≢false (sym has)
liveTypeOK?-extract s u τ (l ∷ ls) ok has with LiveSource.source l ≡ᵇ s
... | false = liveTypeOK?-extract s u τ ls (∧-trueʳ ok) has
... | true  with sameTy τ (LiveSource.elemTy l) in seq
...   | true  = subst (λ z → sameTy u z ≡ true)
                  (trans (sameTy-sound u (LiveSource.elemTy l) (∧-trueˡ ok))
                         (sym (sameTy-sound τ (LiveSource.elemTy l) seq)))
                  (sameTy-refl u)
...   | false = liveTypeOK?-extract s u τ ls (∧-trueʳ ok) has

-- the registry induction: every entry of a's source is a's-typed (else
-- regTyped? + the live source would contradict), so no chainsGo drop
count-eq : ∀ {n} {Γ : Ctx n} {t} (a : Arrival Γ)
  (reg : List (RegId × Source × Chain Γ t)) (live : List (LiveSource Γ)) →
  regTyped? reg live ≡ true → liveHas (arrSource a) (arrTy a) live ≡ true →
  countRegs (arrSource a) reg ≡ length (chainsGo a reg)
count-eq a []                      live rt lh = refl
count-eq a ((rid , s , (u , p)) ∷ r) live rt lh
  with sameSource (arrSource a) s in sseq
... | false = count-eq a r live (∧-trueʳ rt) lh
... | true  with u ≟ᵗ arrTy a
...   | yes refl = cong suc (count-eq a r live (∧-trueʳ rt) lh)
...   | no ¬p    = ⊥-elim (¬p (sameTy-sound u (arrTy a)
                    (liveTypeOK?-extract (arrSource a) u (arrTy a) live
                      (subst (λ z → liveTypeOK? z u live ≡ true)
                             (sym (≡ᵇ→≡ (arrSource a) s sseq)) (∧-trueˡ rt))
                      lh)))

-- THE derived fact, recovering the old one-lookahead chains-count from
-- the pointwise registry↔schedule type-consistency invariant
chains-count-derived : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (sched sched″ : Sched Γ) (st : EvalSt e) →
  regTyped? (EvalSt.registry st) (Sched.live sched) ≡ true →
  sched-next sched ≡ inj₂ (a , sched″) →
  countRegs (arrSource a) (EvalSt.registry st) ≡ length (chainsOf a st)
chains-count-derived a sched sched″ st rt eq with schedGo (Sched.live sched) in geq
... | inj₁ _ with eq
...   | ()
chains-count-derived a sched sched″ st rt eq | inj₂ (a₀ , ls) with eq
...   | refl = count-eq a₀ (EvalSt.registry st) (Sched.live sched) rt
                 (schedGo-mem (Sched.live sched) geq)

-- popping an arrival only shortens a live source's pending — source and
-- elemTy are untouched, so liveTypeOK? (hence regTyped?) is preserved
schedHeadOf-l′ : ∀ {n} {Γ : Ctx n} (l : LiveSource Γ) {a : Arrival Γ} {l′} →
  schedHeadOf l ≡ inj₂ (a , l′) →
  (LiveSource.source l′ ≡ LiveSource.source l) × (LiveSource.elemTy l′ ≡ LiveSource.elemTy l)
schedHeadOf-l′ l eq with LiveSource.pending l | eq
... | (t , v) ∷ ps | refl = refl , refl

liveTypeOK?-swap : ∀ {n} {Γ : Ctx n} (s : Source) (u : Ty)
  (l l′ : LiveSource Γ) (rest : List (LiveSource Γ)) →
  LiveSource.source l′ ≡ LiveSource.source l →
  LiveSource.elemTy l′ ≡ LiveSource.elemTy l →
  liveTypeOK? s u (l′ ∷ rest) ≡ liveTypeOK? s u (l ∷ rest)
liveTypeOK?-swap s u l l′ rest seq teq rewrite seq | teq = refl

schedGo-liveTypeOK : ∀ {n} {Γ : Ctx n} (live : List (LiveSource Γ)) {a : Arrival Γ} {ls} →
  schedGo live ≡ inj₂ (a , ls) →
  ∀ (s : Source) (u : Ty) → liveTypeOK? s u ls ≡ liveTypeOK? s u live
schedGo-liveTypeOK (l ∷ ls) eq s u with schedHeadOf l in heq | schedGo ls in geq
... | inj₁ _        | inj₁ _         with eq
...   | ()
schedGo-liveTypeOK (l ∷ ls) eq s u | inj₁ _ | inj₂ (a′ , ls′) with eq
...   | refl = cong (_∧_ (if LiveSource.source l ≡ᵇ s
                          then sameTy u (LiveSource.elemTy l) else true))
                    (schedGo-liveTypeOK ls geq s u)
schedGo-liveTypeOK (l ∷ ls) eq s u | inj₂ (a₀ , l′) | inj₁ _ with eq
...   | refl = liveTypeOK?-swap s u l l′ ls
                 (proj₁ (schedHeadOf-l′ l heq)) (proj₂ (schedHeadOf-l′ l heq))
schedGo-liveTypeOK (l ∷ ls) eq s u | inj₂ (a₀ , l′) | inj₂ (a′ , ls′)
  with schedEarlier a₀ a′ | eq
...   | true  | refl = liveTypeOK?-swap s u l l′ ls
                         (proj₁ (schedHeadOf-l′ l heq)) (proj₂ (schedHeadOf-l′ l heq))
...   | false | refl = cong (_∧_ (if LiveSource.source l ≡ᵇ s
                                  then sameTy u (LiveSource.elemTy l) else true))
                            (schedGo-liveTypeOK ls geq s u)

regTyped?-pop : ∀ {n} {Γ : Ctx n} {t} (reg : List (RegId × Source × Chain Γ t))
  (live : List (LiveSource Γ)) {a : Arrival Γ} {ls} →
  schedGo live ≡ inj₂ (a , ls) → regTyped? reg live ≡ true → regTyped? reg ls ≡ true
regTyped?-pop []                      live sgeq rt = refl
regTyped?-pop ((_ , s , (u , _)) ∷ r) live sgeq rt =
  ∧-intro (trans (schedGo-liveTypeOK live sgeq s u) (∧-trueˡ rt))
          (regTyped?-pop r live sgeq (∧-trueʳ rt))

regTyped?-pop-sched : ∀ {n} {Γ : Ctx n} {t} (sched sched′ : Sched Γ)
  (reg : List (RegId × Source × Chain Γ t)) {a : Arrival Γ} →
  sched-next sched ≡ inj₂ (a , sched′) →
  regTyped? reg (Sched.live sched) ≡ true → regTyped? reg (Sched.live sched′) ≡ true
regTyped?-pop-sched sched sched′ reg eq rt with schedGo (Sched.live sched) in geq
... | inj₁ _ with eq
...   | ()
regTyped?-pop-sched sched sched′ reg eq rt | inj₂ (a₀ , ls) with eq
...   | refl = regTyped?-pop reg (Sched.live sched) geq rt

-- cascadeFinish preserves type-consistency: dropSource only removes
-- registrations, sweepLive only removes live sources — both loosen
-- regTyped?, never tighten it
regTyped?-dropReg : ∀ {n} {Γ : Ctx n} {t} (src : Source)
  (reg : List (RegId × Source × Chain Γ t)) (live : List (LiveSource Γ)) →
  regTyped? reg live ≡ true → regTyped? (dropSource src reg) live ≡ true
regTyped?-dropReg src []                      live rt = refl
regTyped?-dropReg src ((rid , s , (u , p)) ∷ r) live rt with sameSource src s
... | true  = regTyped?-dropReg src r live (∧-trueʳ rt)
... | false = ∧-intro (∧-trueˡ rt) (regTyped?-dropReg src r live (∧-trueʳ rt))

liveTypeOK?-sweepLive : ∀ {n} {Γ : Ctx n} {t}
  (sweepReg : List (RegId × Source × Chain Γ t)) (s : Source) (u : Ty)
  (live : List (LiveSource Γ)) →
  liveTypeOK? s u live ≡ true → liveTypeOK? s u (sweepLive sweepReg live) ≡ true
liveTypeOK?-sweepLive sweepReg s u []       ok = refl
liveTypeOK?-sweepLive {n = n} sweepReg s u (l ∷ ls) ok
  with (LiveSource.source l <ᵇ n)
       ∨ any (λ p → sameSource (LiveSource.source l) (proj₁ (proj₂ p))) sweepReg
... | true  = ∧-intro (∧-trueˡ ok) (liveTypeOK?-sweepLive sweepReg s u ls (∧-trueʳ ok))
... | false = liveTypeOK?-sweepLive sweepReg s u ls (∧-trueʳ ok)

regTyped?-sweepLive : ∀ {n} {Γ : Ctx n} {t}
  (sweepReg reg : List (RegId × Source × Chain Γ t)) (live : List (LiveSource Γ)) →
  regTyped? reg live ≡ true → regTyped? reg (sweepLive sweepReg live) ≡ true
regTyped?-sweepLive sweepReg []                      live rt = refl
regTyped?-sweepLive sweepReg ((_ , s , (u , _)) ∷ r) live rt =
  ∧-intro (liveTypeOK?-sweepLive sweepReg s u live (∧-trueˡ rt))
          (regTyped?-sweepLive sweepReg r live (∧-trueʳ rt))

-- cutThrough's `kept` is a sublist of the registry (it only drops victims), so
-- registry well-typedness is preserved through it
regTyped?-cutThrough : ∀ {n} {Γ : Ctx n} {t}
  (nid : NodeId) (dlv : List RegId) (wm : RegId) (dying : List Source)
  (reg : List (RegId × Source × Chain Γ t)) (live : List (LiveSource Γ)) →
  regTyped? reg live ≡ true →
  regTyped? (proj₁ (cutThrough nid dlv wm dying reg)) live ≡ true
regTyped?-cutThrough nid dlv wm dying []                        live rt = refl
regTyped?-cutThrough nid dlv wm dying ((rid , src , (u , p)) ∷ r) live rt
  with pathHasNode nid p | cutThrough nid dlv wm dying r
     | regTyped?-cutThrough nid dlv wm dying r live (∧-trueʳ rt)
... | false | kept , closes , rids | ih = ∧-intro (∧-trueˡ rt) ih
... | true  | kept , closes , rids | ih = ih

reg-typed-finish : ∀ {n} {Γ : Ctx n} {t} (src : Source)
  (reg : List (RegId × Source × Chain Γ t)) (live : List (LiveSource Γ)) →
  regTyped? reg live ≡ true →
  regTyped? (dropSource src reg) (sweepLive (dropSource src reg) live) ≡ true
reg-typed-finish src reg live rt =
  regTyped?-sweepLive (dropSource src reg) (dropSource src reg) live
    (regTyped?-dropReg src reg live rt)

-- the open (or last) instant is strictly in the past
CurrentPast : Maybe (Id × Owed) → Id → Set
CurrentPast nothing        nextId = ⊤
CurrentPast (just (j , _)) nextId = suc j ≤ nextId

-- IS THIS SLOT A HOT SCRIPT?  A Bool rather than an equation on
-- `scripted (hot _)` so the `hot-live` field below needs no implicit
-- `ok : T (isData …)` juggling: a call site that has split with
-- `with Sched.slots sched i in eq` discharges the premise by
-- `cong hotSlot? eq`.
hotSlot? : ∀ {n} {Γ : Ctx n} {k t} → Slot Γ k t → Bool
hotSlot? (scripted (hot _)) = true
hotSlot? (scripted (cold _ _)) = false
hotSlot? (shared _) = false

-- THE SCHEDULE INVARIANT ITSELF, named once so that the `hot-live`
-- fields below, and every preservation leaf, share one spelling.
HotLive : ∀ {n} {Γ : Ctx n} → Sched Γ → Set
HotLive {Γ = Γ} sched = ∀ (i : Fin _) →
  hotSlot? (Sched.slots sched i) ≡ true →
  liveTypeOK? (toℕ i) (lookup Γ i) (Sched.live sched) ≡ true

postulate
  -- BASE.  `sched-init`'s live list is `concat (tabulate (mkHot ins))`,
  -- and `mkHot ins i` (Evaluator:110) emits exactly one LiveSource for a
  -- hot slot, with `source = toℕ i` and `elemTy = lookup Γ i`.  So the
  -- fact holds by construction; what it costs is the concat/tabulate
  -- membership argument, which is why it is a leaf rather than a proof.
  sched-init-hot-live : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
    HotLive (sched-init e ins)

  -- STEP, minting.  `mintSource` (via oneShotBurst and the cold-input
  -- arm) prepends a FRESH source and never touches `slots`, so a hot
  -- slot's own entry survives and the new head cannot collide with it.
  mintSource-hot-live : ∀ {n} {Γ : Ctx n} (sched : Sched Γ) →
    HotLive sched → HotLive (proj₂ (mintSource sched))

  -- STEP, subscribing.  A subscribe burst mints and registers but never
  -- rewrites `slots`, and it only ever PREPENDS to `live` (mintSource in
  -- the cold arm, the anchored cold tail); nothing in subscribeE removes
  -- a live source.  So a hot slot's entry is still there afterwards.
  subscribeE-hot-live : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) →
    HotLive sched →
    HotLive (proj₁ (proj₂ (subscribeE g b κ id now sched st)))

  -- STEP, cascade exit.  `cascadeFinish` is the identity unless the
  -- arrival isLast, in which case it sweeps the arrival's source out of
  -- `live` and leaves `slots` alone.  A swept source is one whose
  -- registrations are gone; a hot slot's own ordinal is only swept once
  -- that slot is exhausted, which also makes its `liveTypeOK?` vacuous.
  cascadeFinish-hot-live : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
    HotLive sched → HotLive (proj₁ (cascadeFinish a sched st))

  -- STEP, scheduler pop.  `sched-next` pops one arrival off one live
  -- source and writes back the shortened pending list; `slots` is
  -- untouched and no source's identity or elemTy changes.  Twin of the
  -- proven `regTyped?-pop-sched` (.Part13's mid-init spends that one).
  sched-next-hot-live : ∀ {n} {Γ : Ctx n} (sched sched′ : Sched Γ) {a : Arrival Γ} →
    sched-next sched ≡ inj₂ (a , sched′) →
    HotLive sched → HotLive sched′

record Inv {n} {Γ : Ctx n} {t} {e : Closed Γ t}
           (nextId : Id) (sched : Sched Γ) (st : EvalSt e)
           (S : ProtocolSt) : Set where
  field
    -- the automaton's live multiset shadows the registry: per source,
    -- one for one
    live-matches : ∀ (s : Source) →
      countIn s (ProtocolSt.live S) ≡ countRegs s (EvalSt.registry st)
    -- registry entries are well-typed for their scheduled source (each
    -- registration's type matches its live source's elemTy), so chainsOf's
    -- type check drops nothing — countRegs ≡ length chainsOf for every
    -- scheduled arrival (chains-count-derived).  A pointwise fact, unlike
    -- the old one-lookahead form, so it threads across scheduler pops
    reg-typed    : regTyped? (EvalSt.registry st) (Sched.live sched) ≡ true
    -- freshness is one comparison: ids mint from arrival position
    horizon-low  : ProtocolSt.horizon S ≤ nextId
    current-past : CurrentPast (ProtocolSt.current S) nextId
    -- after the root completes, only share plumbing survives — no
    -- registration can ever carry a value to the root again
    done-plumbed : ProtocolSt.done S ≡ true →
      allShareSunk (EvalSt.registry st) ≡ true
    -- node counters cache the registry's ground truth (see cachesValid):
    -- the between-cascades carrier of the first global coherence field
    caches       : cachesValid (EvalSt.nodes st) (EvalSt.registry st) ≡ true
    -- A HOT SLOT'S ORDINAL IS LIVE AT THE SLOT'S ELEMENT TYPE.
    -- `mkHot` (Evaluator:110) establishes this at sched-init and NOTHING
    -- carried it afterwards, so subscribeE's hot/live input arm could not
    -- pay initReg-wf's `ltok` — the finding is in subscribeE-input-wf's
    -- header (.Part3), where `BurstInv.hot-live binv i` spends it.  It is a
    -- FIELD and not a hypothesis by ruling (Anthony,
    -- 2026-08-15): `live` and `slots` are independent fields of the plain
    -- record `Sched`, so no lemma over an arbitrary sched could be true,
    -- and a hypothesis would bind only whoever calls today while making
    -- the debt invisible to `make wiring`.  See CLAUDE.md, "A POSTULATE
    -- MUST BE A LEAF".
    hot-live     : HotLive sched

------------------------------------------------------------------
-- the subscribe frame: BurstInv and its entry/step/exit lemmas
------------------------------------------------------------------

-- mid-subscribe-frame, CONCRETE: live shadows the registry exactly
-- (burst closes and registry cuts move in lockstep), and the open
-- instant — if any emit has landed — is `id` with a LITERALLY EMPTY
-- owed table: subscribe/plumbing settle to net zero, handoffs are
-- minted only by foldPath (never in a burst), and cancelOwed on []
-- is a no-op, so nothing ever writes an entry
record BurstInv {n} {Γ : Ctx n} {t} {e : Closed Γ t}
                (id : Id) (sched : Sched Γ) (st : EvalSt e)
                (S : ProtocolSt) : Set where
  field
    -- OFF THE DYING SOURCES ONLY (2026-08-18, ruling by Anthony).  The
    -- all-sources form was REFUTED at a dying source: a victim that has
    -- already delivered on a dying source carried its exhausted close on
    -- its own emit, so `cutThrough` drops it from the registry and emits
    -- no close for it (Evaluator's `delivered ∧ memberSource src dying`
    -- guard) — the registry loses an entry the live list never sees.  The
    -- refutation is the third pin in .Part3 (`cutThrough-balance` with its
    -- dying hypothesis removed: 1 ≡ 0 + 0).
    --
    -- KEYED ON `EvalSt.dying st`, NOT ON AN envSrc INDEX.  The fold branch
    -- solved the same problem by excluding envSrc (`FoldInv.shadow`,
    -- .Part8), and its take-cut clause is proven that way (.Part9's
    -- stepFrame-wf-take-cut).  Copying that here would have meant giving
    -- BurstInv an envSrc parameter it does not have and does not need:
    -- `dying` is readable off `st`, which BurstInv already takes, and the
    -- whole cut chain is ALREADY conditioned pointwise on this exact
    -- predicate — `cutThrough-balance`'s own `mem` argument (.Part7).  So
    -- the hypothesis is discharged at every source the machinery can serve,
    -- and the take-cut edge's unpayable `dyF` premise does not get re-keyed,
    -- it DISAPPEARS: what it was trying to establish is now the field's own
    -- hypothesis.  See subscribeE-takeᵉ-wf's header (.Part3) for the two
    -- refutations that forced this.
    live-matches  : ∀ (s : Source) →
      memberSource s (EvalSt.dying st) ≡ false →
      countIn s (ProtocolSt.live S) ≡ countRegs s (EvalSt.registry st)
    reg-typed     : regTyped? (EvalSt.registry st) (Sched.live sched) ≡ true
    horizon-low   : ProtocolSt.horizon S ≤ id
    current-frame : (ProtocolSt.current S ≡ nothing)
                  ⊎ (ProtocolSt.current S ≡ just (id , []))
    -- the mid-burst carrier of Inv's `hot-live` — see that field's note
    hot-live      : HotLive sched
    -- NB: no caches here either, and for a sharper reason than done-plumbed's:
    -- cachesValid is not merely inconvenient mid-burst, it is FALSE there.
    -- nodeCacheOK's only load-bearing clause is merge — while the outer is
    -- registered, activeInners must equal countLiveInners — and a subscribe
    -- burst breaks that equality in BOTH directions.  thruConsume mergeᵒ runs
    -- subscribeInner FIRST and applies mergeBump only after, so throughout an
    -- inner's burst the inner's registrations exist while activeInners has not
    -- been incremented (the count TRAILS the registry); and a take-cut strips
    -- registrations without touching activeInners (the count LEADS it).  No
    -- relation between the two survives both, so no weakening of the field
    -- would work — it has to leave.  Both directions were checked by
    -- computation before the field was dropped (2026-08-09).  Like done-plumbed
    -- it is re-established once, at the root exit, from `root-caches`.
    -- NB: no done-plumbed here.  A base burst always latches done ≡ true, but
    -- an INNER base completing amid a live async sibling makes the full-registry
    -- allShareSunk FALSE (the enclosing thru-outer frame strips that complete
    -- before emission — see the fork note on the blueprint).  done-plumbed's only
    -- consumer is burst-final (root frame-0 exit), so it is a ROOT-EXIT
    -- obligation, supplied to burst-final directly, not threaded through here.

-- the empty states are related
burst-init : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  BurstInv {e = e} 0 (sched-init e ins) (st-init e) protocol-init
burst-init e ins = record
  { live-matches  = λ s _ → refl
  ; reg-typed     = refl
  ; horizon-low   = z≤n
  ; current-frame = inj₁ refl
  ; hot-live      = sched-init-hot-live e ins
  }

-- ── base-case brick: a oneShotBurst's protocol trajectory ────────────────
-- The single emit  init src ∷ values ++ close src ∷ complete  runs against
-- any BurstInv-shaped state whose done is still false: the init/close bracket
-- is net-zero on live (values are protocol-transparent while not done), and
-- the trailing complete latches done.  Result keeps live and horizon, opens
-- instant id with an EMPTY owed table, done true — precisely the state the
-- base clauses of subscribeE-wf must exhibit.

-- a ≤ b reflected as the Bool the protocol's freshness guard tests
≤ᵇ-true : ∀ (a b : ℕ) → a ≤ b → (a ≤ᵇ b) ≡ true
≤ᵇ-true a b p with a ≤ᵇ b | ≤⇒≤ᵇ p
... | true | _ = refl

-- settleInstant on an absent instant just publishes the horizon (its
-- own current-match must be discharged separately from stepProtocol's)
settleInstant-nothing : (S : ProtocolSt) → ProtocolSt.current S ≡ nothing →
  settleInstant S ≡ just (ProtocolSt.horizon S)
settleInstant-nothing S ceq with ProtocolSt.current S | ceq
... | nothing | refl = refl

-- values carry no protocol traffic while the stream is not yet done
applyEvents-vals-through : ∀ {A : Set} (vals : List A)
  (rest : List (InstEvent A)) (live : List Source) (owed : Owed) →
  applyEvents (map value vals ++ rest) live owed false
    ≡ applyEvents rest live owed false
applyEvents-vals-through []         rest live owed = refl
applyEvents-vals-through (v ∷ vals) rest live owed =
  applyEvents-vals-through vals rest live owed

-- the whole event list folds to (live , [] , true): init enlists src, the
-- values pass through, close brackets it back out, complete latches done
oneShotBurst-apply : ∀ {n} {Γ : Ctx n} {u}
  (vals : List (Val Γ u)) (src : Source) (live : List Source) →
  applyEvents (init src ∷ map value vals ++ close src exhausted ∷ complete ∷ [])
              live [] false
    ≡ just (live , [] , true)
oneShotBurst-apply vals src live
  rewrite applyEvents-vals-through vals (close src exhausted ∷ complete ∷ [])
                             (src ∷ live) []
        | ≡ᵇ-refl src
  = refl

-- one emit steps the automaton once: opens (or re-enters) instant id and
-- settles it to the net-zero-plus-done state above
oneShotBurst-step : ∀ {n} {Γ : Ctx n} {u}
  (vals : List (Val Γ u)) (id : Id) (src : Source) (S : ProtocolSt) →
  ProtocolSt.done S ≡ false →
  (ProtocolSt.current S ≡ nothing) ⊎ (ProtocolSt.current S ≡ just (id , [])) →
  ProtocolSt.horizon S ≤ id →
  stepProtocol ((init src ∷ map value vals ++ close src exhausted ∷ complete ∷ [])
                 at id from src as subscribe) S
    ≡ just (record { live = ProtocolSt.live S ; horizon = ProtocolSt.horizon S
                   ; current = just (id , []) ; done = true })
oneShotBurst-step vals id src S deq (inj₁ ceq) hlow
  rewrite ceq | settleInstant-nothing S ceq
        | ≤ᵇ-true (ProtocolSt.horizon S) id hlow | deq
        | oneShotBurst-apply vals src (ProtocolSt.live S) = refl
oneShotBurst-step vals id src S deq (inj₂ ceq) hlow
  rewrite ceq | ≡ᵇ-refl id | deq
        | oneShotBurst-apply vals src (ProtocolSt.live S) = refl

-- lifted to the whole one-emit burst
oneShotBurst-run : ∀ {n} {Γ : Ctx n} {u}
  (vals : List (Val Γ u)) (id : Id) (sched : Sched Γ) (S : ProtocolSt) →
  ProtocolSt.done S ≡ false →
  (ProtocolSt.current S ≡ nothing) ⊎ (ProtocolSt.current S ≡ just (id , [])) →
  ProtocolSt.horizon S ≤ id →
  runProtocol S (proj₁ (oneShotBurst vals id sched))
    ≡ just (record { live = ProtocolSt.live S ; horizon = ProtocolSt.horizon S
                   ; current = just (id , []) ; done = true })
oneShotBurst-run vals id sched S deq curr hlow
  rewrite oneShotBurst-step vals id (Sched.nextSource sched) S deq curr hlow = refl

-- ── the base clause of subscribeE-wf, mechanism-complete ─────────────────
-- A oneShotBurst (ofᵉ / emptyᵉ / takeᵉ-zero) registers nothing, so it leaves
-- st untouched and mints only a source.  Given BurstInv on entry, its burst
-- runs and re-establishes BurstInv.  The mechanism (oneShotBurst-run) is fully
-- proven; the clause owes exactly ONE thing from the surrounding context, the
-- premise `deq`:
--   · deq  — `done S ≡ false` at subscribe time (you never subscribe a new
--     source after the run has completed; the protocol would reject a value
--     behind `complete`).  This is a subscribe-TIME fact, not a frame-exit
--     one (done may be true at exit), so BurstInv cannot carry it; it must
--     come from the walk order.
-- (The former `allShareSunk` premise is GONE: done-plumbed left BurstInv and
--  became a root-exit obligation, so the base clause no longer owes it.)
oneShotBurst-wf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (vals : List (Val Γ u)) (id : Id) (sched : Sched Γ) (st : EvalSt e)
  (S : ProtocolSt) →
  BurstInv id sched st S →
  ProtocolSt.done S ≡ false →
  Σ ProtocolSt λ S′ →
    runProtocol S (proj₁ (oneShotBurst vals id sched)) ≡ just S′
    × BurstInv id (proj₂ (oneShotBurst vals id sched)) st S′
oneShotBurst-wf vals id sched st S binv deq =
  _ , oneShotBurst-run vals id sched S deq (BurstInv.current-frame binv)
                       (BurstInv.horizon-low binv)
    , record
        { live-matches  = λ s h → BurstInv.live-matches binv s h
        ; reg-typed     = BurstInv.reg-typed binv
        ; horizon-low   = BurstInv.horizon-low binv
        ; current-frame = inj₂ refl
        ; hot-live      = mintSource-hot-live sched (BurstInv.hot-live binv)
        }

-- ── the register/init balance mechanism (blueprint step 2) ───────────────
-- `register` appends ONE entry to the tail of the registry; these two snoc
-- lemmas are how live-matches and reg-typed absorb that append.  Reused by
-- EVERY registering clause (input hot/cold-async, deferᵉ, share connect).

-- countRegs over a tail-append: the new entry adds 1 iff it is s's source
countRegs-snoc : ∀ {n} {Γ : Ctx n} {t}
  (s : Source) (r : List (RegId × Source × Chain Γ t))
  (rid : RegId) (x : Source) (u : Ty) (p : Path Γ u t) →
  countRegs s (r ++ (rid , x , u , p) ∷ [])
    ≡ countRegs s r + (if s ≡ᵇ x then 1 else 0)
countRegs-snoc s []                        rid x u p with s ≡ᵇ x
... | true  = refl
... | false = refl
countRegs-snoc s ((rid′ , x′ , u′ , p′) ∷ r) rid x u p with s ≡ᵇ x′
... | true  = cong suc (countRegs-snoc s r rid x u p)
... | false = countRegs-snoc s r rid x u p

-- regTyped? over a tail-append: stays true when the new entry is well-typed
