-- Verify-Budget-Sufficient.Caps-Face.Part7.Walk-Sink
-- the chain/sink walk SCC
module Verify-Budget-Sufficient.Caps-Face.Part7.Walk-Sink where

open import Data.Bool    using (Bool; true; false; _∧_; if_then_else_)
open import Data.Nat     using (ℕ; zero; suc; pred; _+_; _∸_; _⊔_; _≤_; _≤ᵇ_; _≡ᵇ_; s≤s)
open import Data.Nat.Properties using (m+[n∸m]≡n; ≤ᵇ⇒≤; ≤-trans; ≤-refl; ≤-reflexive; m≤m+n; m≤n+m; n≤1+n; +-monoʳ-≤; ⊔-lub; m≤m⊔n;
  m≤n⊔m; +-suc; ≤-pred)
open import Data.Nat.Solver     using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.List    using (List; []; _∷_; _++_; length)
open import Data.Bool.ListAction using (any)
open import Data.Fin     using (Fin)
import Data.Fin as Fin
open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []ᵃ; _∷_ to _∷ᵃ_; map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties
  using (concat⁺; tabulate⁺)
  renaming (++⁺ to all-++; ++⁻ˡ to all-++ˡ; ++⁻ʳ to all-++ʳ)
open import Data.Maybe   using (Maybe; just)
open import Data.Vec     using (Vec; lookup) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit    using (tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; sym; trans; subst)

open import Rx.Prim      using (Tick; Id; Source; _at_from_as_; Gas; after_,_; close; exhausted;
  InstEvent)
open import Rx.Exp       using (Ctx; Closed; Val; sizeᵉ)
open import Verify-Budget-Sufficient.Nest-Ceiling using
  (Ent; ent-step; reached-room)
open import Verify-Budget-Sufficient.Subscribe-Face using (stepFrame-caps)
open import Verify-Budget-Sufficient.Nest-Walk using
  (capsWalkOK; dispatchCapsOK; frameDrainOK; capsDrainOK; shareCapsOK)
open import Verify-Budget-Sufficient.Caps-Depth using
  (depthFold; depthShareGo; lub3-l; lub3-m; lub3-r)
open import Verify-Budget-Sufficient.Deliver-Measure using
  (shareAdmit-len; shareAdmit-sz; admSz?)
open import Rx.Evaluator using (Sched; EvalSt; RegId; mergeAll-st; lookupNode; NodeId; _↠_; Frame; AllOp; map-f; scan-f;
  take-f; from-inner; thru-outer; Path; stepFrame; regAt; share-sink; root; dCapᶜ; fLvlD; lvls;
  shareAdmit; shareLatch)
open import Rx.Slots using (Slots; slotsSize)

open import Verify-Budget-Sufficient.Deliveries using
  (delivN)
open import Verify-Budget-Sufficient.Caps using
  (1≤capsAt-reg; 2≤capsAt-size; Caps; capsAt; capsAt-base-size; capsAt-suc-full; capsH;
  frameStep; frameStep-mono-j; frameStep-reg-mono; iterL-infl; sucJ≤fLvlD; regAt-mono;
  lvls-infl; lvls-mono; size≤sizeCount; sizeCount)
open import Verify-Budget-Sufficient.Measures using
  (pathLen; ∧-true; all-impl)
open import Verify-Budget-Sufficient.Keeps-Ring using
  (KeepsC; stepFrame-keeps)
open import Verify-Budget-Sufficient.Caps-Depth
  using (depthFrame)

open import Verify-Budget-Sufficient.Caps-Face.Part1 using
  (capsOK?-mono; frameSz?; pathSz?; pathSz?-widen; nestClosOK?ᵛ-widen)
open import Verify-Budget-Sufficient.Caps-Face.Part5 using
  (clos-lift; valsCaps?-parts)
open import Verify-Budget-Sufficient.Caps-Face.Part4 using
  (foldPath-slots; capsOK?-count; capsOK?-delivered; capsOK?-regs; frameBud; shareLatch-caps;
  slotsCaps?-capsAt; valsCaps?-lvl)
open import Verify-Budget-Sufficient.Caps-Face.Part3 using
  (frameStep-⊑-+; valCaps?-size)
open import Decide using (T-to)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Ring-Vocabulary using
  (RingState; WalkHyps; ent-infl; floor-parts; frameStep-regAt; regs-exit; ring-room; ringFold; sink-deliv-cap; sink-entry-ladder; sink-step-caps; walk-frame-clos)

chain-walk-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sl : Slots Γ) (id : ℕ) (L : ℕ) (sf : Gas) (gas : ℕ) (nid : Id) (now : Tick)
  (src : Source) (p : Path Γ u t) (vals : List (Val Γ u))
  (evs : List (InstEvent (Val Γ t))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  WalkHyps sl id L sf gas nid now src p vals evs fin sched st →
  capsWalkOK (capsAt e sl id) (capsAt e sl (suc id)) sl (capsH e sl id) L sf gas nid now p vals fin sched st

-- ONE ADMITTED REGISTRATION'S OWN WALK, which is the first of the two
-- things the ring cannot do for itself.  The entry's path lives in the
-- REGISTRY rather than in the chain being charged, so its receipt is
-- not a sub-receipt of anything the ring holds -- but every hypothesis
-- the path induction wants of it is one the ring already carries.
-- Writing the body is what says so: the walk is entered at the ring's
-- level with the entry's own source, and the only place a `record`
-- update is visible is the `delivered` mark, which the caps receipt
-- survives and the registry does not see.
--
-- TWIN: `arr-chain-caps` -- the cascade's per-chain walk, entered from
--   its own round package by the same two rewrites.
sink-entry-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (sf : Gas) (gas : ℕ) (nid : Id) (now : Tick)
  (i : Fin n) (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
  (rid : RegId) (p : Path Γ (lookup Γ i) t) (Lv J g k : ℕ)
  (sched : Sched Γ) (st : EvalSt e) →
  RingState {t = t} sl id i vals gas Lv J g k sched st →
  pathSz? (Caps.cSize (frameStep Lv (capsAt e sl id))) p ≡ true →
  suc k ≤ regAt (Caps.cSize (capsAt e sl id)) (Caps.cReg (capsAt e sl id)) J →
  depthFold sf gas nid now (Fin.toℕ i) p vals
    (if fin then close (Fin.toℕ i) exhausted ∷ [] else []) fin sched
    (record st { delivered = rid ∷ EvalSt.delivered st })
    ≤ capsH e sl id →
  capsWalkOK (capsAt e sl id) (capsAt e sl (suc id)) sl (capsH e sl id) Lv sf gas nid now
    p vals fin sched (record st { delivered = rid ∷ EvalSt.delivered st })
sink-entry-caps {e = e} sl id sf gas nid now i vals fin rid p Lv J g k sched st
  RS@(sleq , cok , hvc , hcl , _) hpz hi hdf =
  chain-walk-caps sl id Lv sf gas nid now (Fin.toℕ i) p vals
    (if fin then close (Fin.toℕ i) exhausted ∷ [] else []) fin sched
    (record st { delivered = rid ∷ EvalSt.delivered st })
    ( sleq
    , capsOK?-delivered (frameStep Lv c) rid sched st cok
    , hvc
    , hcl
    , hpz
    , hdf
    , sink-entry-ladder sl id i vals p gas Lv J g k sched st RS hpz hi )
  where
  c = capsAt e sl id

-- THE RING, AND IT IS THE RECURSION AND NOTHING ELSE.  A cancelled
-- registration is skipped at the position it was reached at; a live one
-- spends its own walk, reports its advance, and hands the tail the state
-- its delivery left one position further on.  Both of the depth
-- premise's tails come off the SAME `⊔`, because the measure reports the
-- tail at both states rather than choosing between them -- so neither
-- branch has to re-derive a depth bound, and the skip arm needs nothing
-- beyond the head of the admitted list's pricing being dropped.
sink-ring-go : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (sf : Gas) (gas : ℕ) (nid : Id) (now : Tick)
  (i : Fin n) (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
  (ps : List (RegId × Path Γ (lookup Γ i) t)) (L₀ Lv J g k : ℕ)
  (sched : Sched Γ) (st : EvalSt e) →
  RingState {t = t} sl id i vals gas Lv J g k sched st →
  admSz? (Caps.cSize (frameStep L₀ (capsAt e sl id))) ps ≡ true →
  L₀ ≤ Lv →
  k + length ps ≤ regAt (Caps.cSize (capsAt e sl id)) (Caps.cReg (capsAt e sl id)) J →
  depthShareGo sf gas nid now i vals fin ps sched st ≤ capsH e sl id →
  shareCapsOK (capsAt e sl id) (capsAt e sl (suc id)) sl (capsH e sl id) Lv sf gas nid now
    i vals fin ps sched st
sink-ring-go sl id sf gas nid now i vals fin [] L₀ Lv J g k sched st RS hadm hL₀ hlen hdp = tt
sink-ring-go {n = n} {e = e} sl id sf gas nid now i vals fin ((rid , p) ∷ ps) L₀ Lv J g k sched st
  RS hadm hL₀ hlen hdp
  with any (_≡ᵇ rid) (EvalSt.cancelled st)
... | true =
  sink-ring-go sl id sf gas nid now i vals fin ps L₀ Lv J g k sched st RS
    (proj₂ (∧-true (pathSz? (Caps.cSize (frameStep L₀ (capsAt e sl id))) p)
                   (admSz? (Caps.cSize (frameStep L₀ (capsAt e sl id))) ps) hadm))
    hL₀
    (≤-trans (+-monoʳ-≤ k (n≤1+n (length ps))) hlen)
    (lub3-l (depthShareGo sf gas nid now i vals fin ps sched st)
            (depthFold sf gas nid now (Fin.toℕ i) p vals
              (if fin then close (Fin.toℕ i) exhausted ∷ [] else []) fin sched
              (record st { delivered = rid ∷ EvalSt.delivered st }))
            (depthShareGo sf gas nid now i vals fin ps
              (proj₁ (ringFold sf gas nid now i vals fin rid p sched st))
              (proj₂ (ringFold sf gas nid now i vals fin rid p sched st)))
            hdp)
... | false =
    sink-entry-caps sl id sf gas nid now i vals fin rid p Lv J g k sched st RS hpzL HI
      (lub3-m DA DB DC hdp)
  , L′
  , ring-room c d g J k (Lv + L′) 2≤S HI hR (proj₂ (proj₂ (proj₂ (proj₂ (proj₂
      (proj₂ RS₁))))))
  , sink-ring-go sl id sf gas nid now i vals fin ps L₀ (Lv + L′) J g (suc k) sched₁ st₁ RS₁
      (proj₂ (∧-true (pathSz? B₀ p) (admSz? B₀ ps) hadm))
      (≤-trans hL₀ (m≤m+n Lv L′))
      (subst (_≤ regAt (Caps.cSize c) (Caps.cReg c) J) (+-suc k (length ps)) hlen)
      (lub3-r DA DB DC hdp)
  where
  c   = capsAt e sl id
  d   = capsH e sl id
  2≤S = 2≤capsAt-size e sl id
  B₀  = Caps.cSize (frameStep L₀ c)
  hR  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ RS)))))
  HI : suc k ≤ regAt (Caps.cSize c) (Caps.cReg c) J
  HI = ≤-trans (subst (suc k ≤_) (sym (+-suc k (length ps)))
                      (s≤s (m≤m+n k (length ps))))
               hlen
  hpz = proj₁ (∧-true (pathSz? B₀ p) (admSz? B₀ ps) hadm)
  sched₁ = proj₁ (ringFold sf gas nid now i vals fin rid p sched st)
  st₁    = proj₂ (ringFold sf gas nid now i vals fin rid p sched st)
  st′ = record st { delivered = rid ∷ EvalSt.delivered st }
  EVS = if fin then close (Fin.toℕ i) exhausted ∷ [] else []
  DA = depthShareGo sf gas nid now i vals fin ps sched st
  DB = depthFold sf gas nid now (Fin.toℕ i) p vals EVS fin sched st′
  DC = depthShareGo sf gas nid now i vals fin ps sched₁ st₁
  sleq = proj₁ RS
  cok  = proj₁ (proj₂ RS)
  hvc  = proj₁ (proj₂ (proj₂ RS))
  hcl  = proj₁ (proj₂ (proj₂ (proj₂ RS)))
  hfl  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ RS))))
  hgas = proj₂ (proj₂ (floor-parts (4 + (sizeᵉ e + slotsSize sl)) n gas g hfl))
  hLv  = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ RS)))))
  hpzL = pathSz?-widen p (proj₁ (frameStep-mono-j c 2≤S hL₀)) hpz
  cok′ = capsOK?-delivered (frameStep Lv c) rid sched st cok
  ST  = sink-step-caps sl id sf gas nid now i vals fin rid p Lv sched st
          sleq cok′ hpzL hvc (lub3-m DA DB DC hdp)
  L′  = proj₁ ST
  D   = delivN st′ st₁
  STEP : lvls (Caps.cSize c) (Caps.cWid c) d Lv (suc D) ≤ Ent c d J g (suc k)
  STEP = ≤-trans (lvls-mono (suc D) (suc D) 2≤S ≤-refl ≤-refl hLv ≤-refl)
                 (ent-step c d J g k D 2≤S
                    (sink-deliv-cap sl id sf gas nid now i vals fin rid p Lv J g k sched st
                       sleq hgas cok′ hpzL hvc (lub3-m DA DB DC hdp) hLv))
  RS₁ = trans (foldPath-slots sf gas nid now (Fin.toℕ i) p vals EVS fin sched st′) sleq
      , proj₂ (proj₂ ST)
      , valsCaps?-lvl (frameStep Lv c) (frameStep (Lv + L′) c) sl vals
          (frameStep-⊑-+ c 2≤S Lv L′) hvc
      , all-impl _ _
          (λ v h → nestClosOK?ᵛ-widen sl _ v (frameStep-⊑-+ c 2≤S Lv L′) h) vals hcl
      , hfl , hR
      , ≤-trans (proj₁ (proj₂ ST)) STEP

-- THE SINK'S RING RUNS IN A NESTED ROUND, and the walk's own round is
-- what it is nested in.  A ring is not a path: it advances one
-- REGISTRATION at a time, and what has to survive a turn is a position
-- within a round together with the gas that round was entered with.
-- The walk carries a reachable position and a level under it, and the
-- ring opens at position zero of that same round one gas down -- which
-- is the one thing the `walk` constructor charges for.
--
-- SO THE FLOOR IS DENOMINATED IN THE GAS, which is the only quantity
-- here that counts the nestings.  The depth mirror spends one at
-- exactly this head and nowhere else, and the caps face matches the
-- same `suc`, so a floor of the form `<constants> + gas <= g`
-- reproduces itself across a nesting for free: the nested round runs at
-- one less gas AND one less ledger, and the two decrements cancel.  A
-- CONSTANT floor survives one nesting and no more, which is the whole
-- reason the walk's floor carries its gas.
--
-- AND THE REST IS READ OFF THE LEVEL BOUND.  The ring's entry level is
-- the round's own head because the walk's level sits under the position
-- and a round's head only climbs; its admitted list fits one round's
-- ledger because the registry count is the frame cap at the walk's
-- level, which is that same ledger read below the position.
walk-sink-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (L : ℕ) (sf : Gas) (gas : ℕ) (nid : Id) (now : Tick)
  (src : Source) (i : Fin n) (vals : List (Val Γ (lookup Γ i)))
  (evs : List (InstEvent (Val Γ t))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  WalkHyps {t = t} sl id L sf gas nid now src (share-sink i) vals evs fin sched st →
  dispatchCapsOK (capsAt e sl id) (capsAt e sl (suc id)) sl (capsH e sl id) L sf gas nid now i vals fin sched st
walk-sink-caps sl id L sf zero nid now src i vals evs fin sched st H = tt
walk-sink-caps sl id L sf (suc gas) nid now src i vals evs fin sched st
  (_ , _ , _ , _ , _ , _ , (zero , _ , () , _ , _))
walk-sink-caps {n = n} {Γ = Γ} {t = t} {e = e} sl id L sf (suc gas) nid now src i vals evs fin sched st
  (sleq , cok , hvc , hcl , _ , hdp , (suc g₀ , P , hfl , hlvP , hR)) =
    shareAdmit-sz i (Caps.cSize (capsAt e sl (suc id))) (EvalSt.registry st)
      (regs-exit sl id L sched st L≤TOP cok)
  , ≤-trans (shareAdmit-len i (EvalSt.registry st))
            (≤-trans (capsOK?-count (frameStep L c) sched st cok)
                     (subst (λ x → Caps.cReg (frameStep L c) ≤ Caps.cReg x)
                            (sym (capsAt-suc-full e sl id))
                            (frameStep-reg-mono c L≤)))
  , sink-ring-go sl id sf gas nid now i vals fin
      (shareAdmit i (EvalSt.registry st)) L L P g₀ 0 sched (shareLatch i fin st)
      ( sleq
      , shareLatch-caps (frameStep L c) i fin sched st cok
      , hvc
      , hcl
      , hfl₀ , hR , hL₀ )
      (shareAdmit-sz i (Caps.cSize (frameStep L c)) (EvalSt.registry st)
         (capsOK?-regs (frameStep L c) sched st cok))
      ≤-refl
      hlen₀
      hdp
  where
  c   = capsAt e sl id
  S   = Caps.cSize c
  W   = Caps.cWid c
  d   = capsH e sl id
  2≤S = 2≤capsAt-size e sl id
  hfl₀ : 4 + (sizeᵉ e + slotsSize sl) + n + gas ≤ g₀
  hfl₀ = ≤-pred (subst (_≤ suc g₀)
                   (+-suc (4 + (sizeᵉ e + slotsSize sl) + n) gas) hfl)
  L≤P : L ≤ P
  L≤P = ≤-trans (iterL-infl S W d (pathLen {Γ = Γ} {t = t} (share-sink i)) L) hlvP
  L≤TOP : L ≤ sizeCount c d ⊔ S
  L≤TOP = ≤-trans L≤P
            (≤-trans (lvls-infl S W d P (dCapᶜ S W (Caps.cReg c) d (suc g₀) P))
                     (reached-room c d P (suc g₀) 2≤S hR))
  hL₀ : L ≤ Ent c d P g₀ 0
  hL₀ = ≤-trans L≤P (ent-infl c d P g₀ 0)
  hlen₀ : 0 + length (shareAdmit i (EvalSt.registry st)) ≤ regAt S (Caps.cReg c) P
  hlen₀ = ≤-trans (shareAdmit-len i (EvalSt.registry st))
            (≤-trans (capsOK?-count (frameStep L c) sched st cok)
              (≤-trans (≤-reflexive (frameStep-regAt c L))
                 (regAt-mono {S} {S} {Caps.cReg c} {Caps.cReg c} ≤-refl ≤-refl L≤P)))
  L≤ : L ≤ sizeCount c d
  L≤ = ≤-trans L≤P
         (≤-trans (≤-trans (lvls-infl S W d P (dCapᶜ S W (Caps.cReg c) d (suc g₀) P))
                           (reached-room c d P (suc g₀) 2≤S hR))
                  (⊔-lub ≤-refl (size≤sizeCount c d 2≤S (1≤capsAt-reg e sl id))))

-- THE ONE HEAD THAT OWES, AND A CENSUS SAYS WHICH CONJUNCTS THOSE
-- ARE.  The state and slot conjuncts are the frame's own hypotheses,
-- and TWO of the per-entry readings are already recorded: the store
-- predicate carries a written-size field and a width field per NODE,
-- and the lookup hypothesis here names the very node whose queue is
-- being read, so the entry's size and its slot width come off the
-- receipt the frame arrives holding.
--
-- WHAT IS ACTUALLY OWED IS THREE THINGS, and they fail for three
-- different reasons.  The entry's CLOSURE key is recorded nowhere --
-- the store predicate's closure half ranges over the live list and
-- never over the node table -- but it does not want a field, because
-- a key read through a CAPPED telescope is at most the cap times the
-- term's plain size, and the size is recorded; one level absorbs the
-- factor, which is the ratio `clos-lift` already spends.  The ROOM
-- FLOOR comes off the store predicate's own park field, which is what
-- fixes the cap it is read at: the field is re-established one level
-- up at every park, so the floor is a statement about the walk's level
-- and the base reading is available to no queue at all.  And the
-- REACHED level is a fact about the ceiling rather than about the
-- store, so no field could hold it.
--
-- AND THE ACCOUNT THAT REPLACES ALL OF THIS CHARGES THE TERM AT
-- DELIVERY RATHER THAN AT DRAIN (Anthony's ruling).  The demand is not
-- wrong: a drained descent really does run at the global cursor and
-- really does push it.  What cannot be done is to have anyone hold
-- that fact AHEAD of time, because whether it holds is settled jointly
-- by the term's ladder and the budget remaining when the drain
-- happens.  So the store stops carrying a ceiling: what it carries is
-- the term's price at the path it was DELIVERED under, which is fixed
-- when the term is emitted and never climbs, so no level is named and
-- the invariant becomes statable at all.  The drain then derives its
-- ceiling from the parent frame's own remaining budget -- the chain
-- already hands one to every frame, and this one is not special -- and
-- the delivery price is the debit the drain's fold spends.
--
-- AND THE ITERATED FACT IS NOW PROVEN, IN THE CURRENCY THE SUBSCRIBE
-- ALREADY REPORTS IN.  One unit of the operator measure buys one
-- LEVEL, which is not what the drain climbs -- the subscribe's caps
-- lemma hands back a climb it chooses, bounded by a SWEEP rather than
-- in operator units -- and the multi-level step that would have taken
-- it wants a climb under a quadratic in the cap, which nothing
-- supplies.  The repair is that the quadratic was never the price: the
-- entry step spends its room only on lifting a sweep to the level the
-- ladder's own recursion starts a sweep at, so a climb reported
-- DIRECTLY under that sweep needs no room at all.  One operator unit
-- therefore buys a whole sweep, and a queue whose entries each climb
-- within one costs one unit each -- so the fold holds a single
-- frame-level ceiling and spends it entry by entry, and the store
-- carries an offset with a sweep bound in place of a roof.

-- AND THE REACHED LEVEL IS NOT MERELY UNSUPPLIED -- A WITNESS KILLS
-- IT, in the GAS currency, which is the same base-cap defect the
-- three readings above already suffered.  A reached gas is rooted at `suc`
-- the ENTRY size cap and every walk position spends one, so no gas the
-- relation offers exceeds that root; the nesting the ceiling entry is
-- asked for is bounded only at the cap the walk has STEPPED to, and one
-- step multiplies the size by better than the size itself.  So the
-- entry demands a fuel above the entry cap and the relation cannot
-- issue one -- and the fuel is not slack that could be found elsewhere,
-- since the delivery recurrence grows without bound in it while the
-- count it is measured against does not move.  Handing over the walk's
-- OWN ceiling entry does not help: the same reading caps that one too.
-- REFUTED: `Refuted.Drain-Reach-Gas.drain-reach-gas-absurd`, at one
--   level, with `drain-reach-gas-base` beside it proving the same
--   obligation at level zero -- where the room floor the entry already
--   carries IS the gas floor and the bottom constructor supplies the
--   level.
-- REFUTED: `Refuted.Frame-Step-Compose.frameStep-compose-absurd`;
--   `Refuted.Drain-Queue-Flat.drain-spine-flat-absurd` for the
--   conjuncts themselves being unreachable from what the walk holds;
--   and `Refuted.Arr-Cap-Step.arr-cap-step-absurd` for the raise that
--   also re-enters the arrival family one level up, which is the one
--   route the two above leave standing
-- TWIN: `subscribeE-caps` already threads a level exactly this way --
--   invariant at the stepped cap, conclusion at the sum -- and is
--   proven.
-- PROBED: `Probed.Drain-Queue-Ladder` reads the two computable halves
--   at a `mergeAll` limited to one over parked inners, at queue
--   lengths TWO and FOUR -- the queue read off the node the run
--   installed, so the entries are the ones the evaluator parked.  Both
--   dominate with room: the frame reads eighteen and eighty-seven
--   against entries at eleven, charged twenty-nine and thirty once
--   one level per entry is paid for.  Not covered, and the first is
--   the one that matters: the position is CHARGED rather than
--   measured, so nothing here reaches the sweep-currency climb the
--   subscribe actually takes; the ledger comparison the
--   readings feed, symbolic-or-nothing by the descent family's own
--   dead route; the two heads other than `mergeAllᵒ`; and a queue
--   whose entries differ from one another in size.
-- PROBED: `Probed.Drain-Queue-Length` reads the other half the fold
--   names -- the queue's LENGTH, since one unit of the frame's
--   measure is spent per entry.  A limit-one merge over a scripted
--   input parks one short of the script at three lengths, against a
--   syntax size that does not move, so no bound naming the program's
--   own size can hold; the slot vocabulary dominates at all three.
--   Not covered: a source that parks without a script, a limit other
--   than one, a merge nested in another's drain, and the cap, which
--   is a tower and is not instantiated.
postulate
  walk-frame-drain-inner : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (sl : Slots Γ) (id : ℕ) (L : ℕ) (sf : Gas) (gas : ℕ) (nid : Id) (now : Tick)
    (src : Source) (op : AllOp) (allNid : NodeId) (inst : NodeId)
    (p : Path Γ u t) (vals : List (Val Γ u))
    (evs : List (InstEvent (Val Γ t))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    WalkHyps sl id L sf gas nid now src (from-inner op allNid inst ↠ p)
      vals evs fin sched st →
    ∀ (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ u)) (od : Bool) →
      lookupNode allNid (EvalSt.nodes st) ≡ just (mergeAll-st lim act q od) →
      capsDrainOK (capsAt e sl id) sl (capsH e sl id) L sf allNid p nid now
        lim (pred act) q sched st


-- AND THE DRAIN ONE IS NOW A FRAME-LOCAL STATEMENT, which is what it
-- had to become.  Its conjunct used to charge the walk's LEVEL against
-- the BASE size cap, because the proven consumer climbed the relative
-- ceiling one operator per level from the bottom and that climb is paid
-- for only while the level fits under that cap.  The walk's ladder is
-- denominated in the COUNT instead -- the Σ it hands its tail permits a
-- level anywhere up to `sizeCount c d ⊔ Caps.cSize c`, and the arrival
-- face confirms levels genuinely reach the count -- so at level zero the
-- conjunct was `capsOK?` read through `parkRoom` and the level was the
-- whole of what it asked for and the whole of what the bundle could not
-- give.
--
-- WHAT THE CONJUNCT SAYS NOW IS THE PARKED TERM UNDER THE BASE CAP,
-- with no level term in it, which is the refuted statement minus the
-- refuted part, TOGETHER WITH THE LEVEL BEING REACHED.  A level the
-- cascade's delivery walk actually lands on carries the gas it still
-- has there, and from that its room is derived rather than assumed:
-- the walk recurrence splits so that the budget read from a reached
-- level IS the walk read from the level before it, one gas down, and
-- the bottom is the two bodies.  So the queue asks for the reaching
-- and the arithmetic follows.
--
-- AND THE GAS IS WHY THE RELATION CARRIES ONE.  At the whole cascade's
-- gas a room receipt is false everywhere above the bottom -- the
-- budget read higher is the larger one and the ladder from there is
-- longer, so both sides move the wrong way at once -- while four plus
-- a term's operator count is syntactic and fixed before any level
-- exists.  A level bound cannot say which of the two it has; the
-- reaching relation can, because it is built by spending it.
--
-- AND THE REACHING IS A `≤`, WHICH IS THE ONLY SHAPE THAT COULD BE
-- SUPPLIED.  A chain advances its level by one frame charge at a time
-- while the cascade advances by whole restarts, so the levels a chain
-- visits sit BETWEEN two positions the walk lands on and are almost
-- never positions themselves.  Room survives that gap in the useful
-- direction: the ladder from a level and the budget read at it both
-- grow with the level, so the receipt at the position ABOVE covers
-- every level under it, and what the queue asks for is a position
-- above the walk's level rather than the walk's level itself.
--
-- RECOVERY: git show b927a16 restores `Refuted.Walk-Frame-Drain-Level`,
--   which refuted the levelled conjunct at the empty context with the
--   level taken to be the base size cap, every other premise met by the
--   entry bounds and the proven node installer.  Whoever puts a level
--   back into this statement wants that witness back.

-- AND FOUR OF THE FIVE HEADS OWE NOTHING, which the match says in
-- code rather than in prose.  Only a `from-inner` names a node, so
-- only a `from-inner` can be looking at a `mergeAll` queue; the other
-- four forward what they are handed and their arm is the unit.
walk-frame-drain : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (sl : Slots Γ) (id : ℕ) (L : ℕ) (sf : Gas) (gas : ℕ) (nid : Id) (now : Tick)
  (src : Source) (f : Frame Γ s u) (p : Path Γ u t) (vals : List (Val Γ s))
  (evs : List (InstEvent (Val Γ t))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  WalkHyps sl id L sf gas nid now src (f ↠ p) vals evs fin sched st →
  frameDrainOK (capsAt e sl id) sl (capsH e sl id) L sf nid now f p vals sched st

walk-frame-drain sl id L sf gas nid now src (map-f _) p vals evs fin sched st H = tt
walk-frame-drain sl id L sf gas nid now src (scan-f _ _) p vals evs fin sched st H = tt
walk-frame-drain sl id L sf gas nid now src (take-f _) p vals evs fin sched st H = tt
walk-frame-drain sl id L sf gas nid now src (thru-outer _ _) p vals evs fin sched st H = tt
walk-frame-drain sl id L sf gas nid now src (from-inner op allNid inst) p vals evs fin sched st H =
  walk-frame-drain-inner sl id L sf gas nid now src op allNid inst p vals evs fin sched st H



-- THE WALK ITSELF, WHICH IS THE FRAME LAW ITERATED AND NOTHING ELSE.
-- Each frame spends the proven step receipt, which reports its own
-- increment and hands back the caps and the values one level up; the
-- ladder premise pays the ceiling at that frame and reproduces itself
-- for the tail, since `iterL` at a `suc` IS `iterL` at the stepped
-- level.  The path receipt splits the same way -- this frame's, the
-- tail's length, the tail's -- so nothing has to be re-established
-- from outside, which is what made the frame law's data the right
-- thing to state the walk over.
chain-walk-caps sl id L sf gas nid now src root vals evs fin sched st H =
  proj₁ (proj₂ H)
chain-walk-caps sl id L sf gas nid now src (share-sink i) vals evs fin sched st H =
  proj₁ (proj₂ H)
  , walk-sink-caps sl id L sf gas nid now src i vals evs fin sched st H
chain-walk-caps {e = e} sl id L sf gas nid now src (f ↠ p) vals evs fin sched st
  H@(sleq , cok , hvc , hcl , hpz , hdp , (g , P , hfl , hlvP , hR)) =
    cok
  , proj₁ (valsCaps?-parts (frameStep L c) sl vals hvc)
  , slSz
  , hpz
  , walk-frame-clos sl id L sf gas nid now src f p vals evs fin sched st H
  , walk-frame-drain sl id L sf gas nid now src f p vals evs fin sched st H
  , Lt ∸ L
  , subst (_≤ sizeCount c d ⊔ S) (sym hLt) Lt≤TOP
  , subst (λ x → capsWalkOK c (capsAt e sl (suc id)) sl d x sf gas nid now p
                   (proj₁ r) (proj₁ (proj₂ (proj₂ r)))
                   (proj₁ (proj₂ (proj₂ (proj₂ r))))
                   (proj₂ (proj₂ (proj₂ (proj₂ r)))))
      (sym hLt)
      (chain-walk-caps sl id Lt sf gas nid now src p
        (proj₁ r) (evs ++ proj₁ (proj₂ r)) (proj₁ (proj₂ (proj₂ r)))
        (proj₁ (proj₂ (proj₂ (proj₂ r)))) (proj₂ (proj₂ (proj₂ (proj₂ r))))
        ( trans (KeepsC.slotsEq (stepFrame-keeps sf nid now f p vals fin sched st)) sleq
        , capsOK?-mono (frameStep (L + proj₁ ST) c) (frameStep Lt c)
            (proj₁ (proj₂ (proj₂ (proj₂ r)))) (proj₂ (proj₂ (proj₂ (proj₂ r))))
            (frameStep-mono-j c 2≤S ST≤t) (proj₁ (proj₂ ST))
        , valsCaps?-lvl _ _ sl (proj₁ r)
            (frameStep-mono-j c 2≤S ST≤t) (proj₁ (proj₂ (proj₂ ST)))
        , all-impl _ _
            (λ v h → nestClosOK?ᵛ-widen sl _ v (frameStep-mono-j c 2≤S STs≤t) h)
            (proj₁ r)
            (clos-lift c (L + proj₁ ST) sl (proj₁ r) 2≤S (slotsCaps?-capsAt e sl id)
              (all-impl _ _
                 (λ v → valCaps?-size (frameStep (L + proj₁ ST) c) sl _ v)
                 (proj₁ r)
                 (proj₁ (valsCaps?-parts (frameStep (L + proj₁ ST) c) sl (proj₁ r)
                           (proj₁ (proj₂ (proj₂ ST)))))))
        , pathSz?-widen p (proj₁ (frameStep-mono-j c 2≤S L≤t)) pz2
        , ≤-trans (m≤n⊔m (depthFrame sf nid now f p vals fin sched st) _) hdp
        , (g , P , hfl , hlvP , hR) ))
  where
  c   = capsAt e sl id
  S   = Caps.cSize c
  W   = Caps.cWid c
  d   = capsH e sl id
  2≤S = 2≤capsAt-size e sl id
  slSz : slotsSize sl ≤ Caps.cSize c
  slSz = ≤-trans (m≤n+m (slotsSize sl) (2 + sizeᵉ e)) (capsAt-base-size e sl id)
  B   = Caps.cSize (frameStep L c)
  pz1 : frameSz? B f ≡ true
  pz1 = proj₁ (∧-true (frameSz? B f) ((suc (pathLen p) ≤ᵇ B) ∧ pathSz? B p) hpz)
  pzr : ((suc (pathLen p) ≤ᵇ B) ∧ pathSz? B p) ≡ true
  pzr = proj₂ (∧-true (frameSz? B f) ((suc (pathLen p) ≤ᵇ B) ∧ pathSz? B p) hpz)
  pzl : (suc (pathLen p) ≤ᵇ B) ≡ true
  pzl = proj₁ (∧-true (suc (pathLen p) ≤ᵇ B) (pathSz? B p) pzr)
  pz2 : pathSz? B p ≡ true
  pz2 = proj₂ (∧-true (suc (pathLen p) ≤ᵇ B) (pathSz? B p) pzr)
  r   = stepFrame sf nid now f p vals fin sched st
  ST  = stepFrame-caps c d (frameBud c L) L sf nid now f p vals fin sl sched st
          2≤S (1≤capsAt-reg e sl id) sleq (slotsCaps?-capsAt e sl id) slSz cok
          pz1 pz2 (≤ᵇ⇒≤ (suc (pathLen p)) B (T-to pzl))
          hvc ≤-refl
          (≤-trans (m≤m⊔n (depthFrame sf nid now f p vals fin sched st) _) hdp)
  Lt  = fLvlD S W d L
  STs≤t : suc (L + proj₁ ST) ≤ Lt
  STs≤t = proj₂ (proj₂ (proj₂ (proj₂ ST)))
  ST≤t : L + proj₁ ST ≤ Lt
  ST≤t = ≤-trans (n≤1+n (L + proj₁ ST)) STs≤t
  sucL≤t : suc L ≤ Lt
  sucL≤t = sucJ≤fLvlD S W d L
  L≤t : L ≤ Lt
  L≤t = ≤-trans (n≤1+n L) sucL≤t
  hLt : L + (Lt ∸ L) ≡ Lt
  hLt = m+[n∸m]≡n L≤t
  P≤TOP : P ≤ sizeCount c d ⊔ S
  P≤TOP = ≤-trans (lvls-infl S W d P (dCapᶜ S W (Caps.cReg c) d g P))
                  (reached-room c d P g 2≤S hR)
  Lt≤TOP : Lt ≤ sizeCount c d ⊔ S
  Lt≤TOP = ≤-trans (iterL-infl S W d (pathLen p) Lt) (≤-trans hlvP P≤TOP)

-- AND THE CHAIN'S OWN LEAF IS NOW THAT WALK AT ITS ENTRY, with the one
-- step of arithmetic between them real: the premise arrives as a
-- DELIVERY count, which is the currency the cascade fold's invariant is
-- kept in, and the walk wants a FRAME count, which is the currency the
-- level ladder climbs in.  `pathSz?` is the conversion -- a chain is at
-- most `suc (sizeAt S L)` frames, which is exactly one rung -- so the
-- two statements are the same bound read at the two granularities the
-- fold and the walk respectively speak, and neither has to know the
-- other's.
--
-- AND THE REST OF THE HYPOTHESES ARE THE FRAME LAW'S OWN, WHICH IS THE
-- ONLY CLAIM MADE FOR THEM.  A walk is the iterate of one frame's
-- receipt, so it is stated over that receipt's data: the values' caps,
-- the path's size receipt, the depth bound.  Each is what the frame law
-- takes at every frame, each propagates down a path without further
-- hypothesis -- the path receipt splits into this frame's, the tail's
-- length and the tail's -- and the sole caller holds all three already,
-- since it hands the same three to the step face next door.  What is
-- NOT claimed is that a form without them is false: nothing has
-- instantiated that, and the argument here is the twin's shape rather
-- than a witness.
