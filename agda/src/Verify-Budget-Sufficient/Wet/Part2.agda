-- STRATUM 2b of Verify-Budget-Sufficient: THE WET FAMILY, part 2 of 4.
--
-- THE WET WALK's 36-member block (genuine cycles of 14 and 3).  Isolated
-- so that an edit anywhere else in the wet family does not re-check it;
-- this is the heaviest single unit in the module.
--
-- Split from Verify-Budget-Sufficient.Wet so that a
-- multi-member block gets its own module and an edit re-checks one
-- part instead of 4.7k lines.  The family is FOUR modules numbered
-- 1, 2, 3, 6: Parts 4 and 5 were the width walk and went with it
-- .  The gap is deliberate — renaming Part6 would churn
-- every consumer's import for nothing, and .Measures carries the
-- deletion record.

module Verify-Budget-Sufficient.Wet.Part2 where


open import Data.Bool    using (Bool; true; false; not; if_then_else_)
open import Data.Nat     using (ℕ; zero; suc; pred; _+_; _*_; _^_; _≤_; _⊔_; _≤ᵇ_; _≡ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (≤ᵇ⇒≤; ≤⇒≤ᵇ; ≤-trans; ≤-refl; ≤-reflexive; m≤m+n; m≤n+m; n≤1+n; *-mono-≤; m≤m⊔n; m≤n⊔m; ⊔-lub)
open import Data.Nat.Solver     using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.List    using (List; []; _∷_; _++_; length; map)
open import Data.Bool.ListAction using (all; any)
open import Data.Nat.ListAction  using (sum)
open import Data.Fin     using (Fin; toℕ)
import Data.Fin as Fin
open import Data.List.Relation.Unary.Any using (here)
open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []ᵃ; _∷_ to _∷ᵃ_; map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties
  using (concat⁺; tabulate⁺)
  renaming (++⁺ to all-++; ++⁻ˡ to all-++ˡ; ++⁻ʳ to all-++ʳ)
open import Data.Maybe   using (Maybe; nothing; just)
open import Relation.Nullary using (yes; no)
open import Data.Vec     using (Vec; lookup) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit    using (tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst)

open import Rx.Prim      using (Tick; Id; Source; InstEmit; _at_from_as_; subscribe; InstEvent; init; value; close; complete;
  exhausted; Gas; g0; gs; Timed; after_,_; hot; cold)
open import Rx.Exp       using (Ty; obs; _≟ᵗ_; Ctx; Closed; Val; sizeᵉ; sizeᵗ; sizeᵗˢ; sizeᵛ; input; ofᵉ; emptyᵉ; mapᵉ;
  takeᵉ; scanᵉ; flattenᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ; unfoldμ;
  evalTm)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; LiveSource; resolve; arrVal; memberSource; RegId; Chain; NodeState;
  scan-st; take-st; flatten-st; switch-st; exhaust-st; installNode; lookupNode;
  NodeId; root; share-sink; _↠_; Frame; AllOp; map-f; scan-f; take-f; from-inner; thru-outer;
  Stream; dropSource; arrSource; Path; arrTy; subscribeE; stepFrame; pushBurst; subscribeInner;
  chainStep; subscribeAll; mintNode; mintSource; mintOrdinal; register; flattenᵒ; hasRoom;
  switchᵒ; exhaustᵒ; splitEvents; retagEvents; switchKill; thruConsume; thruWalk; flattenDrain;
  innerFinish; sharedPlumb; sharedConnect; subscribeSharedSlot; burstCompleted; shareLatch;
  shareAdmit; shareFinish; shareGo; foldPath; dispatchShare; arrTick; aliveThroughᶠ; hasDry;
  dryEvent; sameSource; budgetAt)
open import Rx.Slots using (scripted; shared; slotSize; slotsSize)

open import Verify-Budget-Sufficient.Measures using
  (all-++-intro; all-impl; allPathB-widen;
                                                      boundedLive; boundedNode; burstB?;
                                                      burstB?-widen; burstHopD?; capᴱ;
                                                      capᴱ-mono; caseWᵗ; dropSource-all;
                                                      dropSource-len; eventB?; E≤E*3^;
                                                      fcB-live; fcB-nodes; fnCap-elimG;
                                                      fnCap-evalWith; fnCapBounded?;
                                                      fnCapLive; fnCapNode; fnCapᵉ; fnCapᵗ;
                                                      fnCapᵛ; frameB?; frameB?-widen;
                                                      fᵢ≤sum-tab; INV-parts; INV?;
                                                      mapValue-B; pathB?; pathB?-widen;
                                                      regsB?; resolve-bounded;
                                                      resolve-measure; retag-B; slotFnCap;
                                                      splitEvents-bk-B; splitEvents-vals-B;
                                                      stB-live; stB-nodes; stBounded?;
                                                      sweepLive-bounded; valB?; valsB?-widen;
                                                      ∧-true; ∨-false; szB)
open import Verify-Budget-Sufficient.Keeps-Ring using
  (size-unfoldμ)

------------------------------------------------------------------
-- the Keeps ring and the share-boundary facts moved to
-- .Keeps-Ring: the caps face needs slotsEq too, and a shared
-- prerequisite must not sit inside one of the two faces.
------------------------------------------------------------------
------------------------------------------------------------------
-- the walk contracts, store half — the SHAPE the clause grind
-- threads (receipts E′ ≤ E · spendᴱ … attach with the cost
-- instrumentation; the landing stays in the cores below).  Stated
-- against the frozen instant base W and a ledger position E ≥ 3.
------------------------------------------------------------------


open import Verify-Budget-Sufficient.Wet.Part1 using
  (capᴱ-square; evalTm-cap; eventsB?-widen; install-INV; INV?-widen;
   lookupNode-B; map-applyFn-B; flattenBump-INV; ofVals-B; register-INV;
   splitBurst-bk-B; splitBurst-vals-B; stepFrame-scan-wet; stepFrame-take-wet;
   sweepLive-fnCap; switchKill-INV; thruWrap-wet)
open import Decide using (T-to; T⇒≡true; ∧-intro; ≤ᵇ-widen)

-- forward declarations: these join subscribeE-walkS's clique
-- (thruConsume re-enters subscribeE through subscribeInner; the input
-- clause re-enters it through a share's connect), so their definitions
-- live after the walk's own signature
subscribeE-input-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (Ψ W : ℕ) (g : Gas) (i : Fin n) (κ : Path Γ (lookup Γ i) t)
  (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  pathB? (capᴱ W E) Ψ κ ≡ true →
  let r = subscribeE g (input i) κ id now sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstB? (capᴱ W E′) Ψ (proj₁ r) ≡ true)

-- the DELIVERY clique: foldPath walks one chain sinkward, and at a
-- share boundary hands off to dispatchShare, which folds every
-- admitted registration back through foldPath.  Lexicographic on
-- (dispatch gas, path) exactly as the machine recurses: the frame
-- hops shrink the path at constant gas, the share hop peels one gas
foldPath-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (Ψ W : ℕ) (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
  (path : Path Γ u t) (vals : List (Val Γ u))
  (evs : List (InstEvent (Val Γ t))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  pathB? (capᴱ W E) Ψ path ≡ true →
  all (valB? (capᴱ W E) Ψ u) vals ≡ true →
  all (eventB? (capᴱ W E) Ψ) evs ≡ true →
  let r = foldPath sf gas id now envSrc path vals evs fin sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstB? (capᴱ W E′) Ψ (proj₁ r) ≡ true)

dispatchShare-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (Ψ W : ℕ) (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
  (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  all (valB? (capᴱ W E) Ψ (lookup Γ i)) vals ≡ true →
  let r = dispatchShare sf gas id now i vals fin sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstB? (capᴱ W E′) Ψ (proj₁ r) ≡ true)

shareGo-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (Ψ W : ℕ) (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
  (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
  (ps : List (RegId × Path Γ (lookup Γ i) t))
  (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  all (λ rp → pathB? (capᴱ W E) Ψ (proj₂ rp)) ps ≡ true →
  all (valB? (capᴱ W E) Ψ (lookup Γ i)) vals ≡ true →
  let r = shareGo sf gas id now i vals fin ps sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstB? (capᴱ W E′) Ψ (proj₁ r) ≡ true)

chainStep-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (Ψ W : ℕ) (id : Id) (a : Arrival Γ)
  (path : Path Γ (arrTy a) t)
  (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  pathB? (capᴱ W E) Ψ path ≡ true →
  valB? (capᴱ W E) Ψ (arrTy a) (arrVal a) ≡ true →
  let r = chainStep id a path sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstB? (capᴱ W E′) Ψ (proj₁ r) ≡ true)

sharedSlot-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (Ψ W : ℕ) (g : Gas) (i : Fin n) (d : Closed Γ (lookup Γ i))
  (κ : Path Γ (lookup Γ i) t)
  (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  sizeᵉ d ≤ capᴱ W E → fnCapᵉ d ≤ Ψ →
  pathB? (capᴱ W E) Ψ κ ≡ true →
  let r = subscribeSharedSlot g i d κ id now sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstB? (capᴱ W E′) Ψ (proj₁ r) ≡ true)

sharedConnect-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (Ψ W : ℕ) (g : Gas) (i : Fin n) (d : Closed Γ (lookup Γ i))
  (κ : Path Γ (lookup Γ i) t)
  (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  sizeᵉ d ≤ capᴱ W E → fnCapᵉ d ≤ Ψ →
  pathB? (capᴱ W E) Ψ κ ≡ true →
  let r = sharedConnect g i d κ id now sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstB? (capᴱ W E′) Ψ (proj₁ r) ≡ true)

subscribeInner-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (Ψ W : ℕ) (g : Gas) (op : AllOp) (allNid : NodeId) (κ : Path Γ u t)
  (id : Id) (now : Tick) (o : Val Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  valB? (capᴱ W E) Ψ (obs u) o ≡ true →
  pathB? (capᴱ W E) Ψ κ ≡ true →
  let r = subscribeInner g op allNid κ id now o sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r)))))
                           (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r))))) ≡ true)
     × (all (valB? (capᴱ W E′) Ψ u) (proj₁ (proj₂ r)) ≡ true)
     × (all (eventB? (capᴱ W E′) Ψ) (proj₁ (proj₂ (proj₂ r))) ≡ true)

thruConsume-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (Ψ W : ℕ) (g : Gas) (op : AllOp) (nid : NodeId) (κ : Path Γ u t)
  (id : Id) (now : Tick) (o : Val Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  valB? (capᴱ W E) Ψ (obs u) o ≡ true →
  pathB? (capᴱ W E) Ψ κ ≡ true →
  let r = thruConsume g op nid κ id now o sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ (proj₂ r)))
                           (proj₂ (proj₂ (proj₂ r))) ≡ true)
     × (all (valB? (capᴱ W E′) Ψ u) (proj₁ r) ≡ true)
     × (all (eventB? (capᴱ W E′) Ψ) (proj₁ (proj₂ r)) ≡ true)

thruWalk-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (Ψ W : ℕ) (g : Gas) (op : AllOp) (nid : NodeId) (κ : Path Γ u t)
  (id : Id) (now : Tick) (vals : List (Val Γ (obs u)))
  (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  pathB? (capᴱ W E) Ψ κ ≡ true →
  all (valB? (capᴱ W E) Ψ (obs u)) vals ≡ true →
  let r = thruWalk g op nid κ id now vals sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ (proj₂ r)))
                           (proj₂ (proj₂ (proj₂ r))) ≡ true)
     × (all (valB? (capᴱ W E′) Ψ u) (proj₁ r) ≡ true)
     × (all (eventB? (capᴱ W E′) Ψ) (proj₁ (proj₂ r)) ≡ true)

stepFrame-thruOuter-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (Ψ W : ℕ) (g : Gas) (id : Id) (now : Tick)
  (op : AllOp) (nid : NodeId) (κ : Path Γ u t)
  (vals : List (Val Γ (obs u))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  pathB? (capᴱ W E) Ψ κ ≡ true →
  all (valB? (capᴱ W E) Ψ (obs u)) vals ≡ true →
  let r = stepFrame g id now (thru-outer op nid) κ vals fin sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ (proj₂ (proj₂ r))))
                           (proj₂ (proj₂ (proj₂ (proj₂ r)))) ≡ true)
     × (all (valB? (capᴱ W E′) Ψ u) (proj₁ r) ≡ true)
     × (all (eventB? (capᴱ W E′) Ψ) (proj₁ (proj₂ r)) ≡ true)
flattenDrain-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (Ψ W : ℕ) (g : Gas) (allNid : NodeId) (κ : Path Γ s t)
  (id : Id) (now : Tick) (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ s))
  (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  pathB? (capᴱ W E) Ψ κ ≡ true →
  all (λ o → sizeᵉ o ≤ᵇ capᴱ W E) q ≡ true →
  all (λ o → fnCapᵉ o ≤ᵇ Ψ) q ≡ true →
  let r = flattenDrain g allNid κ id now lim act q sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r)))))
                           (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r))))) ≡ true)
     × (all (valB? (capᴱ W E′) Ψ s) (proj₁ r) ≡ true)
     × (all (eventB? (capᴱ W E′) Ψ) (proj₁ (proj₂ r)) ≡ true)
     × (all (λ o → sizeᵉ o ≤ᵇ capᴱ W E′) (proj₁ (proj₂ (proj₂ (proj₂ r)))) ≡ true)
     × (all (λ o → fnCapᵉ o ≤ᵇ Ψ) (proj₁ (proj₂ (proj₂ (proj₂ r)))) ≡ true)

innerFinish-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (Ψ W : ℕ) (g : Gas) (op : AllOp) (allNid inst : NodeId) (κ : Path Γ s t)
  (id : Id) (now : Tick) (vals : List (Val Γ s))
  (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  pathB? (capᴱ W E) Ψ κ ≡ true →
  all (valB? (capᴱ W E) Ψ s) vals ≡ true →
  let r = innerFinish g op allNid inst κ id now vals sched st
            (lookupNode allNid (EvalSt.nodes st))
  in Σ ℕ λ E′ → (E ≤ E′)
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ (proj₂ (proj₂ r))))
                           (proj₂ (proj₂ (proj₂ (proj₂ r)))) ≡ true)
     × (all (valB? (capᴱ W E′) Ψ s) (proj₁ r) ≡ true)
     × (all (eventB? (capᴱ W E′) Ψ) (proj₁ (proj₂ r)) ≡ true)

-- the inner *All frame: a fin is either absorbed (a sibling
-- registration still lives) or finishes the *All node.  Only
-- the flatten drain moves the ledger
stepFrame-fromInner-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (Ψ W : ℕ) (g : Gas) (id : Id) (now : Tick)
  (op : AllOp) (allNid inst : NodeId) (κ : Path Γ s t)
  (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  pathB? (capᴱ W E) Ψ κ ≡ true →
  all (valB? (capᴱ W E) Ψ s) vals ≡ true →
  let r = stepFrame g id now (from-inner op allNid inst) κ vals fin sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ (proj₂ (proj₂ r))))
                           (proj₂ (proj₂ (proj₂ (proj₂ r)))) ≡ true)
     × (all (valB? (capᴱ W E′) Ψ s) (proj₁ r) ≡ true)
     × (all (eventB? (capᴱ W E′) Ψ) (proj₁ (proj₂ r)) ≡ true)
stepFrame-fromInner-wet Ψ W g id now op allNid inst κ vals false sched st E
                        3≤E inv pB vB = E , ≤-refl , inv , vB , refl
stepFrame-fromInner-wet Ψ W g id now op allNid inst κ vals true sched st E
                        3≤E inv pB vB
  with any (aliveThroughᶠ inst st) (EvalSt.registry st)
... | true  = E , ≤-refl , inv , vB , refl
... | false = innerFinish-wet Ψ W g op allNid inst κ id now vals sched st E
                3≤E inv pB vB

-- the flatten queue's stored outers only ever need widening upward
allsz-widen : ∀ {n} {Γ : Ctx n} {s} {B B′ : ℕ} (q : List (Closed Γ s)) → B ≤ B′ →
  all (λ o → sizeᵉ o ≤ᵇ B) q ≡ true → all (λ o → sizeᵉ o ≤ᵇ B′) q ≡ true
allsz-widen q B≤ h = all-impl _ _ (λ o → ≤ᵇ-widen (sizeᵉ o) B≤) q h

stepFrame-thruOuter-wet Ψ W g id now op nid κ vals fin sched st E 3≤E inv pB vB =
  E′ , E≤E′ , proj₁ WR , proj₁ (proj₂ WR) , proj₂ (proj₂ WR)
  where
  WK   = thruWalk-wet Ψ W g op nid κ id now vals sched st E 3≤E inv pB vB
  E′   = proj₁ WK
  E≤E′ = proj₁ (proj₂ WK)
  wr   = thruWalk g op nid κ id now vals sched st
  WR   = thruWrap-wet Ψ (capᴱ W E′) op nid fin (proj₁ wr) (proj₁ (proj₂ wr))
           (proj₁ (proj₂ (proj₂ wr))) (proj₂ (proj₂ (proj₂ wr)))
           (proj₁ (proj₂ (proj₂ WK)))
           (proj₁ (proj₂ (proj₂ (proj₂ WK))))
           (proj₂ (proj₂ (proj₂ (proj₂ WK))))

------------------------------------------------------------------
-- stepFrame-wet, now a REAL dispatch: the map clause proven end to
-- end on the ledger rule; the other frames delegate to their named
-- cores above
------------------------------------------------------------------

stepFrame-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (Ψ W : ℕ) (g : Gas) (id : Id) (now : Tick)
  (f : Frame Γ s u) (κ : Path Γ u t)
  (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  frameB? (capᴱ W E) Ψ f ≡ true →
  pathB? (capᴱ W E) Ψ κ ≡ true →
  all (valB? (capᴱ W E) Ψ s) vals ≡ true →
  let r = stepFrame g id now f κ vals fin sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ (proj₂ (proj₂ r))))
                           (proj₂ (proj₂ (proj₂ (proj₂ r)))) ≡ true)
     × (all (valB? (capᴱ W E′) Ψ u) (proj₁ r) ≡ true)
     × (all (eventB? (capᴱ W E′) Ψ) (proj₁ (proj₂ r)) ≡ true)
stepFrame-wet Ψ W g id now (map-f fn) κ vals fin sched st E 3≤E inv fB pB vB =
  E * 3 ^ suc Ψ , E≤E*3^ E (suc Ψ) ,
  INV?-widen sched st (capᴱ-mono W (E≤E*3^ E (suc Ψ))) inv ,
  map-applyFn-B Ψ W E fn (≤-trans (n≤1+n 2) 3≤E) capsOK szOK vals vB ,
  refl
  where
  fB2   = ∧-true (sizeᵗ fn ≤ᵇ capᴱ W E) _ fB
  szOK  : sizeᵗ fn ≤ capᴱ W E
  szOK  = ≤ᵇ⇒≤ _ _ (T-to (proj₁ fB2))
  capsOK : caseWᵗ fn ⊔ fnCapᵗ fn ≤ Ψ
  capsOK = ≤ᵇ⇒≤ _ _ (T-to (proj₂ fB2))
stepFrame-wet Ψ W g id now (scan-f fn nid) κ vals fin sched st E h inv fB pB vB =
  stepFrame-scan-wet Ψ W g id now fn nid κ vals fin sched st E h inv fB pB vB
stepFrame-wet Ψ W g id now (take-f nid) κ vals fin sched st E h inv fB pB vB =
  stepFrame-take-wet Ψ W g id now nid κ vals fin sched st E h inv pB vB
stepFrame-wet Ψ W g id now (from-inner op allNid inst) κ vals fin sched st E h inv fB pB vB =
  stepFrame-fromInner-wet Ψ W g id now op allNid inst κ vals fin sched st E h inv pB vB
stepFrame-wet Ψ W g id now (thru-outer op nid) κ vals fin sched st E h inv fB pB vB =
  stepFrame-thruOuter-wet Ψ W g id now op nid κ vals fin sched st E h inv pB vB

-- the fin marker's event list is value-free either way
finList-B : ∀ {n} {Γ : Ctx n} {u} (B Ψ : ℕ) (b : Bool) →
  all (eventB? {n = n} {Γ = Γ} {u = u} B Ψ)
      (if b then complete ∷ [] else []) ≡ true
finList-B B Ψ true  = refl
finList-B B Ψ false = refl

------------------------------------------------------------------
-- pushBurst-wet, PROVEN: the burst re-entry threads the walk
-- invariant emit by emit over stepFrame-wet — the first of the
-- mutual block's contracts discharged as a real induction (list
-- induction on the burst; each emit splits, steps its frame at the
-- current ledger position, and reassembles under widened bounds)
------------------------------------------------------------------

pushBurst-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (Ψ W : ℕ) (g : Gas) (id : Id) (now : Tick)
  (f : Frame Γ s u) (κ : Path Γ u t) (ems : Stream Γ s)
  (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  frameB? (capᴱ W E) Ψ f ≡ true →
  pathB? (capᴱ W E) Ψ κ ≡ true →
  burstB? (capᴱ W E) Ψ ems ≡ true →
  let r = pushBurst g id now f κ ems sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstB? (capᴱ W E′) Ψ (proj₁ r) ≡ true)
pushBurst-wet Ψ W g id now f κ [] sched st E 3≤E inv fB pB bB =
  E , ≤-refl , inv , refl
pushBurst-wet {Γ = Γ} {s = s} {u = u} Ψ W g id now f κ (em ∷ ems)
              sched st E 3≤E inv fB pB bB =
  E₂ , ≤-trans E≤E₁ E₁≤E₂ , inv₂ , outAll
  where
  B₀    = capᴱ W E
  sp    : List (Val Γ s) × List (InstEvent (Val Γ u)) × Bool
  sp    = splitEvents (InstEmit.events em)
  vals  = proj₁ sp
  emB   = proj₁ (∧-true (all (eventB? B₀ Ψ) (InstEmit.events em)) _ bB)
  emsB  = proj₂ (∧-true (all (eventB? B₀ Ψ) (InstEmit.events em)) _ bB)

  step  = stepFrame g id now f κ vals (proj₂ (proj₂ sp)) sched st
  W1    = stepFrame-wet Ψ W g id now f κ vals (proj₂ (proj₂ sp))
            sched st E 3≤E inv fB pB
            (splitEvents-vals-B B₀ Ψ (InstEmit.events em) emB)
  E₁    = proj₁ W1
  E≤E₁  = proj₁ (proj₂ W1)
  inv₁  = proj₁ (proj₂ (proj₂ W1))
  outB  = proj₁ (proj₂ (proj₂ (proj₂ W1)))
  cap₁  = capᴱ-mono W E≤E₁

  rec   = pushBurst-wet Ψ W g id now f κ ems
            (proj₁ (proj₂ (proj₂ (proj₂ step))))
            (proj₂ (proj₂ (proj₂ (proj₂ step))))
            E₁ (≤-trans 3≤E E≤E₁) inv₁
            (frameB?-widen f cap₁ fB) (pathB?-widen κ cap₁ pB)
            (burstB?-widen ems cap₁ emsB)
  E₂    = proj₁ rec
  E₁≤E₂ = proj₁ (proj₂ rec)
  inv₂  = proj₁ (proj₂ (proj₂ rec))
  restB = proj₂ (proj₂ (proj₂ rec))
  cap₂  = capᴱ-mono W E₁≤E₂

  headOK : all (eventB? (capᴱ W E₂) Ψ)
             (proj₁ (proj₂ sp)
              ++ retagEvents (proj₁ (proj₂ step))
              ++ map value (proj₁ step)
              ++ (if proj₁ (proj₂ (proj₂ step)) then complete ∷ [] else []))
           ≡ true
  headOK =
    all-++-intro _ (proj₁ (proj₂ sp)) _
      (splitEvents-bk-B (capᴱ W E₂) Ψ (InstEmit.events em))
      (all-++-intro _ (retagEvents (proj₁ (proj₂ step))) _
        (retag-B (capᴱ W E₂) Ψ (proj₁ (proj₂ step)))
        (all-++-intro _ (map value (proj₁ step)) _
          (mapValue-B (capᴱ W E₂) Ψ u (proj₁ step)
            (valsB?-widen u (proj₁ step) cap₂ outB))
          (finList-B (capᴱ W E₂) Ψ (proj₁ (proj₂ (proj₂ step))))))

  outAll = ∧-intro headOK restB

------------------------------------------------------------------
-- (W9, deferᵉ) THE DEFER HOP, PROVEN.  deferᵉ is the one walk clause
-- that mints machinery without recursing: a node, a source and an
-- ordinal are minted, the flatten node installed, the BODY itself
-- parked as the single pending value of a fresh live source, and the
-- outer chain registered.  The only ledger cost is register-INV's ×2
-- length edge; the burst is a lone `init`, so it is bounded by refl.
------------------------------------------------------------------

-- adding a live hop: only the live conjuncts move, and both faces of
-- the new entry come from the caller
addLive-INV : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ψ B : ℕ)
  (sched : Sched Γ) (st : EvalSt e) (l : LiveSource Γ) →
  boundedLive B l ≡ true → fnCapLive Ψ l ≡ true →
  INV? Ψ B sched st ≡ true →
  INV? Ψ B (record sched { live = l ∷ Sched.live sched }) st ≡ true
addLive-INV Ψ B sched st l bl fl inv
  with ∧-true (stBounded? B sched st) _ inv
... | sb , r1 with ∧-true (fnCapBounded? Ψ sched st) _ r1
... | fc , r2 =
  ∧-intro (∧-intro (∧-intro bl (proj₁ (∧-true _ _ sb))) (proj₂ (∧-true _ _ sb)))
  (∧-intro (∧-intro (∧-intro fl (proj₁ (∧-true _ _ fc))) (proj₂ (∧-true _ _ fc)))
           r2)

------------------------------------------------------------------
-- (W9 face) THE SLOTS, READ ONE AT A TIME.  INV? carries the whole
-- slot vector's size and weight as two sums; a single slot is one
-- summand, so fᵢ≤sum-tab projects the per-slot bound the input
-- clause needs.  The slots themselves never change, so these are
-- the ONLY facts the input clause has about what it is subscribing.
------------------------------------------------------------------

slotSize-at : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ψ B : ℕ)
  (i : Fin n) (sched : Sched Γ) (st : EvalSt e) →
  INV? Ψ B sched st ≡ true → slotSize (Sched.slots sched i) ≤ B
slotSize-at {Γ = Γ} Ψ B i sched st inv
  with ∧-true (stBounded? B sched st) _ inv
... | _ , r1 with ∧-true (fnCapBounded? Ψ sched st) _ r1
... | _ , r2 with ∧-true (length (EvalSt.registry st) ≤ᵇ B) _ r2
... | _ , r3 with ∧-true (regsB? B Ψ (EvalSt.registry st)) _ r3
... | _ , r4 with ∧-true (slotsSize (Sched.slots sched) ≤ᵇ B) _ r4
... | ss , _ =
  ≤-trans (fᵢ≤sum-tab (λ j → slotSize (Sched.slots sched j)) i)
          (≤ᵇ⇒≤ _ _ (T-to ss))

slotFnCap-at : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ψ B : ℕ)
  (i : Fin n) (sched : Sched Γ) (st : EvalSt e) →
  INV? Ψ B sched st ≡ true → slotFnCap (Sched.slots sched i) ≤ Ψ
slotFnCap-at {Γ = Γ} Ψ B i sched st inv
  with ∧-true (stBounded? B sched st) _ inv
... | _ , r1 with ∧-true (fnCapBounded? Ψ sched st) _ r1
... | _ , r2 with ∧-true (length (EvalSt.registry st) ≤ᵇ B) _ r2
... | _ , r3 with ∧-true (regsB? B Ψ (EvalSt.registry st)) _ r3
... | _ , r4 with ∧-true (slotsSize (Sched.slots sched) ≤ᵇ B) _ r4
... | _ , sf =
  ≤-trans (fᵢ≤sum-tab (λ j → slotFnCap (Sched.slots sched j)) i)
          (≤ᵇ⇒≤ _ _ (T-to sf))

-- a script's sync prefix, elementwise, off the slot's two sums
sumVals-B : ∀ {n} {Γ : Ctx n} (B Ψ : ℕ) (u : Ty) (vs : List (Val Γ u)) →
  sum (map (sizeᵛ u) vs) ≤ B → sum (map (fnCapᵛ u) vs) ≤ Ψ →
  all (valB? B Ψ u) vs ≡ true
sumVals-B B Ψ u []       hsz hf = refl
sumVals-B B Ψ u (v ∷ vs) hsz hf =
  ∧-intro (∧-intro (T⇒≡true _ (≤⇒≤ᵇ (≤-trans (m≤m+n (sizeᵛ u v) _) hsz)))
                   (T⇒≡true _ (≤⇒≤ᵇ (≤-trans (m≤m+n (fnCapᵛ u v) _) hf))))
          (sumVals-B B Ψ u vs (≤-trans (m≤n+m _ (sizeᵛ u v)) hsz)
                              (≤-trans (m≤n+m _ (fnCapᵛ u v)) hf))

-- retagging an emit's kind leaves its EVENTS alone, so the share's
-- plumbing relabel is invisible to every in-flight bound
sharedPlumb-B : ∀ {n} {Γ : Ctx n} {u} (B Ψ : ℕ) (str : Stream Γ u) →
  burstB? B Ψ str ≡ true → burstB? B Ψ (sharedPlumb str) ≡ true
sharedPlumb-B B Ψ []         h = refl
sharedPlumb-B B Ψ (em ∷ ems) h =
  ∧-intro (proj₁ (∧-true _ _ h)) (sharedPlumb-B B Ψ ems (proj₂ (∧-true _ _ h)))

-- THE SAME RELABEL, FOR THE OTHER TWO FLAVOURS THE WALK CARRIES.  It is
-- one fact three times: `sharedPlumb` rewrites an emit's KIND and touches
-- nothing else, and none of the three predicates reads the kind.  They sit
-- together so the next flavour lands here too rather than growing a fourth
-- copy of the same induction somewhere downstream.
sharedPlumb-hopD : ∀ {n} {Γ : Ctx n} {u} (V : ℕ) (η : Fin n → ℕ) (r : ℕ)
  (str : Stream Γ u) →
  burstHopD? V η r str ≡ true → burstHopD? V η r (sharedPlumb str) ≡ true
sharedPlumb-hopD V η r []         h = refl
sharedPlumb-hopD V η r (em ∷ ems) h =
  ∧-intro (proj₁ (∧-true _ _ h))
          (sharedPlumb-hopD V η r ems (proj₂ (∧-true _ _ h)))

-- dryness is a DISJUNCTION rather than a conjunction, so this one peels
-- with ∨-false; the shape is otherwise identical
sharedPlumb-nodry : ∀ {n} {Γ : Ctx n} {u} (str : Stream Γ u) →
  hasDry str ≡ false → hasDry (sharedPlumb str) ≡ false
sharedPlumb-nodry []         h = refl
sharedPlumb-nodry (em ∷ ems) h
  with ∨-false (any dryEvent (InstEmit.events em)) (hasDry ems) h
... | hd , tl rewrite hd = sharedPlumb-nodry ems tl

-- the completion latch: dropping a source SHRINKS the registry on
-- both riders, and completedSources / connectedShares are read by no
-- conjunct at all
dropSource-regs : ∀ {n} {Γ : Ctx n} {t} (B Ψ : ℕ) (src : Source)
  (reg : List (RegId × Source × Chain Γ t)) →
  regsB? B Ψ reg ≡ true → regsB? B Ψ (dropSource src reg) ≡ true
dropSource-regs B Ψ = dropSource-all (λ en → pathB? B Ψ (proj₂ (proj₂ (proj₂ en))))

latch-INV : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ψ B : ℕ)
  (src : Source) (sched : Sched Γ) (st : EvalSt e) →
  INV? Ψ B sched st ≡ true →
  INV? Ψ B sched
    (record st { registry = dropSource src (EvalSt.registry st)
               ; completedSources = src ∷ EvalSt.completedSources st })
    ≡ true
latch-INV Ψ B src sched st inv
  with ∧-true (stBounded? B sched st) _ inv
... | sb , r1 with ∧-true (fnCapBounded? Ψ sched st) _ r1
... | fc , r2 with ∧-true (length (EvalSt.registry st) ≤ᵇ B) _ r2
... | rl , r3 with ∧-true (regsB? B Ψ (EvalSt.registry st)) _ r3
... | rb , r4 =
  ∧-intro sb
  (∧-intro fc
  (∧-intro (T⇒≡true _ (≤⇒≤ᵇ (≤-trans (dropSource-len src (EvalSt.registry st))
                                     (≤ᵇ⇒≤ _ _ (T-to rl)))))
  (∧-intro (dropSource-regs B Ψ src (EvalSt.registry st) rb) r4)))

-- a share's close list, the dual of finList-B
closeList-B : ∀ {n} {Γ : Ctx n} {u} (B Ψ : ℕ) (src : Source) (b : Bool) →
  all (eventB? {n = n} {Γ = Γ} {u = u} B Ψ)
      (if b then close src exhausted ∷ [] else []) ≡ true
closeList-B B Ψ src true  = refl
closeList-B B Ψ src false = refl

-- completedSources / dying / delivered are read by no conjunct
shareLatch-INV : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ψ B : ℕ)
  (i : Fin n) (b : Bool) (sched : Sched Γ) (st : EvalSt e) →
  INV? Ψ B sched st ≡ true → INV? Ψ B sched (shareLatch i b st) ≡ true
shareLatch-INV Ψ B i false sched st inv = inv
shareLatch-INV Ψ B i true  sched st inv = inv

delivered-INV : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ψ B : ℕ)
  (rid : RegId) (sched : Sched Γ) (st : EvalSt e) →
  INV? Ψ B sched st ≡ true →
  INV? Ψ B sched (record st { delivered = rid ∷ EvalSt.delivered st }) ≡ true
delivered-INV Ψ B rid sched st inv = inv

-- the admitted fan-out chains inherit their bounds from the registry
shareAdmit-B : ∀ {n} {Γ : Ctx n} {t} (B Ψ : ℕ) (i : Fin n)
  (reg : List (RegId × Source × Chain Γ t)) → regsB? B Ψ reg ≡ true →
  all (λ rp → pathB? B Ψ (proj₂ rp)) (shareAdmit i reg) ≡ true
shareAdmit-B B Ψ i []                      h = refl
shareAdmit-B {Γ = Γ} B Ψ i ((rid , src , (u , q)) ∷ r) h
  with sameSource (toℕ i) src | u ≟ᵗ lookup Γ i
... | false | _        = shareAdmit-B B Ψ i r (proj₂ (∧-true (pathB? B Ψ q) _ h))
... | true  | no  _    = shareAdmit-B B Ψ i r (proj₂ (∧-true (pathB? B Ψ q) _ h))
... | true  | yes refl =
      ∧-intro (proj₁ (∧-true (pathB? B Ψ q) _ h))
              (shareAdmit-B B Ψ i r (proj₂ (∧-true (pathB? B Ψ q) _ h)))

-- the share's completion sweep: the registry SHRINKS on both riders
-- and the live list is filtered, so every conjunct only improves
shareFinish-INV : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ψ B : ℕ)
  (i : Fin n) (b : Bool) (emits : Stream Γ t)
  (sched : Sched Γ) (st : EvalSt e) →
  INV? Ψ B sched st ≡ true →
  INV? Ψ B (proj₁ (proj₂ (shareFinish i b (emits , sched , st))))
           (proj₂ (proj₂ (shareFinish i b (emits , sched , st)))) ≡ true
shareFinish-INV Ψ B i false emits sched st inv = inv
shareFinish-INV Ψ B i true  emits sched st inv =
  ∧-intro (∧-intro (sweepLive-bounded B kept (Sched.live sched)
                     (stB-live B sched st sb))
                   (stB-nodes B sched st sb))
  (∧-intro (∧-intro (sweepLive-fnCap Ψ kept (Sched.live sched)
                      (fcB-live Ψ sched st fc))
                    (fcB-nodes Ψ sched st fc))
  (∧-intro (T⇒≡true _ (≤⇒≤ᵇ (≤-trans (dropSource-len (toℕ i) (EvalSt.registry st))
                                     (≤ᵇ⇒≤ _ _ (T-to rl)))))
  (∧-intro (dropSource-regs B Ψ (toℕ i) (EvalSt.registry st) rb)
  (∧-intro ss sf))))
  where
  kept = dropSource (toℕ i) (EvalSt.registry st)
  P    = INV-parts Ψ B sched st inv
  sb   = proj₁ P
  fc   = proj₁ (proj₂ P)
  rl   = proj₁ (proj₂ (proj₂ P))
  rb   = proj₁ (proj₂ (proj₂ (proj₂ P)))
  ss   = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ P))))
  sf   = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ P))))

-- shareFinish never touches the emits it is handed
shareFinish-burst : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (i : Fin n) (b : Bool) (emits : Stream Γ t)
  (sched : Sched Γ) (st : EvalSt e) →
  proj₁ (shareFinish i b (emits , sched , st)) ≡ emits
shareFinish-burst i false emits sched st = refl
shareFinish-burst i true  emits sched st = refl

-- connectedShares is read by no conjunct of INV?, so latching a
-- connect is invisible to the invariant (record eta does the work)
connectShare-INV : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ψ B : ℕ)
  (src : Source) (sched : Sched Γ) (st : EvalSt e) →
  INV? Ψ B sched st ≡ true →
  INV? Ψ B sched
    (record st { connectedShares = src ∷ EvalSt.connectedShares st }) ≡ true
connectShare-INV Ψ B src sched st inv = inv

-- the connect's two landings, factored out of sharedConnect's `if` so
-- the caller can keep one where-block across both
connectWrap-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (Ψ B : ℕ) (i : Fin n) (id : Id) (c : Bool)
  (burst : Stream Γ (lookup Γ i)) (sched : Sched Γ) (st : EvalSt e) →
  INV? Ψ B sched st ≡ true → burstB? B Ψ burst ≡ true →
  let r = if c
          then (((init (toℕ i) ∷ close (toℕ i) exhausted ∷ [])
                  at id from toℕ i as subscribe) ∷ sharedPlumb burst)
               , sched
               , record st { registry = dropSource (toℕ i) (EvalSt.registry st)
                           ; completedSources = toℕ i ∷ EvalSt.completedSources st }
          else ((init (toℕ i) ∷ []) at id from toℕ i as subscribe) ∷ sharedPlumb burst
               , sched , st
  in (INV? Ψ B (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstB? B Ψ (proj₁ r) ≡ true)
connectWrap-wet Ψ B i id true  burst sched st inv bB =
  latch-INV Ψ B (toℕ i) sched st inv ,
  ∧-intro refl (sharedPlumb-B B Ψ burst bB)
connectWrap-wet Ψ B i id false burst sched st inv bB =
  inv , ∧-intro refl (sharedPlumb-B B Ψ burst bB)

subscribeE-defer-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (Ψ W : ℕ) (g : Gas) (body : Closed Γ u) (κ : Path Γ u t)
  (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  sizeᵉ body ≤ capᴱ W E → fnCapᵉ body ≤ Ψ →
  pathB? (capᴱ W E) Ψ κ ≡ true →
  let r = subscribeE g (deferᵉ body) κ id now sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstB? (capᴱ W E′) Ψ (proj₁ r) ≡ true)
subscribeE-defer-wet {Γ = Γ} {u = u} Ψ W g body κ id now sched st E
                     3≤E inv szB fcB pB =
  2 * E , m≤m+n E (E + 0) ,
  register-INV Ψ W E src (thru-outer flattenᵒ nid ↠ κ) sched₄ st₀
    (≤-trans (s≤s z≤n) 3≤E) inv₂ (∧-intro refl pB) ,
  refl
  where
  nid    = proj₁ (mintNode sched)
  sched₁ = proj₂ (mintNode sched)
  src    = proj₁ (mintSource sched₁)
  sched₂ = proj₂ (mintSource sched₁)
  ord    = proj₁ (mintOrdinal sched₂)
  sched₃ = proj₂ (mintOrdinal sched₂)
  hop : LiveSource Γ
  hop = record { source = src ; ordinal = ord ; elemTy = obs u
               ; pending = (suc now , body) ∷ [] }
  sched₄ = record sched₃ { live = hop ∷ Sched.live sched₃ }
  st₀    = installNode nid (flatten-st {t = u} nothing 0 [] false) st
  inv₁   = install-INV Ψ (capᴱ W E) sched₃ st nid
             (flatten-st {t = u} nothing 0 [] false)
             refl refl inv
  inv₂   = addLive-INV Ψ (capᴱ W E) sched₃ st₀ hop
             (∧-intro (T⇒≡true _ (≤⇒≤ᵇ szB)) refl)
             (∧-intro (T⇒≡true _ (≤⇒≤ᵇ fcB)) refl)
             inv₁

------------------------------------------------------------------
-- subscribeE-walkS, THE REAL INDUCTION: the store half of the wet
-- contract ground through the machine's clauses, lexicographic on
-- (gas, expression) exactly as the machine recurses.  Eleven of the
-- thirteen clauses are proven here (of/empty one-shots pay one eval
-- edge; map/take/scan/the four *Alls thread install-INV/register
-- rings, the IH and pushBurst-wet; μ pays the ×2 copy edge against
-- size-unfoldμ with shells/caps carried by elimG-invariance; varᵉ
-- is absurd); input and deferᵉ delegate to their named W9 cores.
------------------------------------------------------------------

subscribeE-walkS : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (Ψ W : ℕ) (g : Gas) (b : Closed Γ u) (κ : Path Γ u t)
  (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  sizeᵉ b ≤ capᴱ W E → fnCapᵉ b ≤ Ψ →
  pathB? (capᴱ W E) Ψ κ ≡ true →
  let r = subscribeE g b κ id now sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstB? (capᴱ W E′) Ψ (proj₁ r) ≡ true)

-- the shared *All shape: mint, install (bounded on both faces),
-- subscribe under the thru-outer frame, push the burst — proven
-- once, consumed by all four *All clauses
subscribeAll-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (Ψ W : ℕ) (g : Gas) (op : AllOp) (ns : NodeState Γ)
  (b : Closed Γ (obs u)) (κ : Path Γ u t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  boundedNode (capᴱ W E) ns ≡ true → fnCapNode Ψ ns ≡ true →
  sizeᵉ b ≤ capᴱ W E → fnCapᵉ b ≤ Ψ →
  pathB? (capᴱ W E) Ψ κ ≡ true →
  let r = subscribeAll g op ns b κ id now sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstB? (capᴱ W E′) Ψ (proj₁ r) ≡ true)
subscribeAll-wet Ψ W g op ns b κ id now sched st E 3≤E inv bn fnn szB fcB pB =
  E₂ , ≤-trans E≤E₁ E₁≤E₂ , inv₂ , b₂
  where
  nid    = Sched.nextNode sched
  sched₁ = proj₂ (mintNode sched)
  st₀    = installNode nid ns st
  inv₀   = install-INV Ψ (capᴱ W E) sched₁ st nid ns bn fnn inv
  sE      = subscribeE g b (thru-outer op nid ↠ κ) id now sched₁ st₀
  IH     = subscribeE-walkS Ψ W g b (thru-outer op nid ↠ κ) id now
             sched₁ st₀ E 3≤E inv₀ szB fcB (∧-intro refl pB)
  E₁     = proj₁ IH
  E≤E₁   = proj₁ (proj₂ IH)
  inv₁   = proj₁ (proj₂ (proj₂ IH))
  bB₁    = proj₂ (proj₂ (proj₂ IH))
  cap₁   = capᴱ-mono W E≤E₁
  PB     = pushBurst-wet Ψ W g id now (thru-outer op nid) κ (proj₁ sE)
             (proj₁ (proj₂ sE)) (proj₂ (proj₂ sE)) E₁
             (≤-trans 3≤E E≤E₁) inv₁ refl (pathB?-widen κ cap₁ pB) bB₁
  E₂     = proj₁ PB
  E₁≤E₂  = proj₁ (proj₂ PB)
  inv₂   = proj₁ (proj₂ (proj₂ PB))
  b₂     = proj₂ (proj₂ (proj₂ PB))

subscribeE-walkS Ψ W g (input i) κ id now sched st E 3≤E inv szB fcB pB =
  subscribeE-input-wet Ψ W g i κ id now sched st E 3≤E inv pB

subscribeE-walkS {Γ = Γ} {u = u} Ψ W g (ofᵉ ts) κ id now sched st E 3≤E inv szB fcB pB =
  E * 3 ^ suc Ψ , E≤E*3^ E (suc Ψ) ,
  INV?-widen (record sched { nextSource = suc (Sched.nextSource sched) }) st
    (capᴱ-mono W (E≤E*3^ E (suc Ψ))) inv ,
  ∧-intro
    (∧-intro refl
      (all-++-intro _ (map value (map (λ tm → evalTm tm) ts)) _
        (mapValue-B (capᴱ W (E * 3 ^ suc Ψ)) Ψ u (map (λ tm → evalTm tm) ts)
          (ofVals-B Ψ W E (≤-trans (n≤1+n 2) 3≤E) ts (≤-trans (n≤1+n (sizeᵗˢ ts)) szB) fcB))
        refl))
    refl

subscribeE-walkS Ψ W g emptyᵉ κ id now sched st E 3≤E inv szB fcB pB =
  E , ≤-refl , inv , refl

subscribeE-walkS Ψ W g (mapᵉ f b) κ id now sched st E 3≤E inv szB fcB pB =
  E₂ , ≤-trans E≤E₁ E₁≤E₂ , inv₂ , b₂
  where
  szf  = ≤-trans (≤-trans (m≤m+n (sizeᵗ f) (sizeᵉ b)) (n≤1+n _)) szB
  szb  = ≤-trans (≤-trans (m≤n+m (sizeᵉ b) (sizeᵗ f)) (n≤1+n _)) szB
  capf = ≤-trans (m≤m⊔n (caseWᵗ f ⊔ fnCapᵗ f) (fnCapᵉ b)) fcB
  fcb  = ≤-trans (m≤n⊔m (caseWᵗ f ⊔ fnCapᵗ f) (fnCapᵉ b)) fcB
  fB   : frameB? (capᴱ W E) Ψ (map-f f) ≡ true
  fB   = ∧-intro (T⇒≡true _ (≤⇒≤ᵇ szf)) (T⇒≡true _ (≤⇒≤ᵇ capf))
  sE    = subscribeE g b (map-f f ↠ κ) id now sched st
  IH   = subscribeE-walkS Ψ W g b (map-f f ↠ κ) id now sched st E 3≤E inv
           szb fcb (∧-intro fB pB)
  E₁   = proj₁ IH
  E≤E₁ = proj₁ (proj₂ IH)
  inv₁ = proj₁ (proj₂ (proj₂ IH))
  bB₁  = proj₂ (proj₂ (proj₂ IH))
  cap₁ = capᴱ-mono W E≤E₁
  PB   = pushBurst-wet Ψ W g id now (map-f f) κ (proj₁ sE)
           (proj₁ (proj₂ sE)) (proj₂ (proj₂ sE)) E₁ (≤-trans 3≤E E≤E₁)
           inv₁ (frameB?-widen (map-f f) cap₁ fB) (pathB?-widen κ cap₁ pB) bB₁
  E₂   = proj₁ PB
  E₁≤E₂ = proj₁ (proj₂ PB)
  inv₂ = proj₁ (proj₂ (proj₂ PB))
  b₂   = proj₂ (proj₂ (proj₂ PB))

subscribeE-walkS Ψ W g (takeᵉ count b) κ id now sched st E 3≤E inv szB fcB pB
  with evalTm count
... | zero  = E , ≤-refl , inv , refl
... | suc k = E₂ , ≤-trans E≤E₁ E₁≤E₂ , inv₂ , b₂
  where
  nid    = Sched.nextNode sched
  sched₁ = proj₂ (mintNode sched)
  st₀    = installNode nid (take-st (suc k)) st
  szb    = ≤-trans (≤-trans (m≤n+m (sizeᵉ b) (sizeᵗ count)) (n≤1+n _)) szB
  fcb    = ≤-trans (m≤n⊔m (caseWᵗ count ⊔ fnCapᵗ count) (fnCapᵉ b)) fcB
  inv₀   = install-INV Ψ (capᴱ W E) sched₁ st nid (take-st (suc k)) refl refl inv
  sE      = subscribeE g b (take-f nid ↠ κ) id now sched₁ st₀
  IH     = subscribeE-walkS Ψ W g b (take-f nid ↠ κ) id now sched₁ st₀ E 3≤E
             inv₀ szb fcb (∧-intro refl pB)
  E₁     = proj₁ IH
  E≤E₁   = proj₁ (proj₂ IH)
  inv₁   = proj₁ (proj₂ (proj₂ IH))
  bB₁    = proj₂ (proj₂ (proj₂ IH))
  cap₁   = capᴱ-mono W E≤E₁
  PB     = pushBurst-wet Ψ W g id now (take-f nid) κ (proj₁ sE)
             (proj₁ (proj₂ sE)) (proj₂ (proj₂ sE)) E₁
             (≤-trans 3≤E E≤E₁) inv₁ refl (pathB?-widen κ cap₁ pB) bB₁
  E₂     = proj₁ PB
  E₁≤E₂  = proj₁ (proj₂ PB)
  inv₂   = proj₁ (proj₂ (proj₂ PB))
  b₂     = proj₂ (proj₂ (proj₂ PB))

subscribeE-walkS {Γ = Γ} {u = u} Ψ W g (scanᵉ f z b) κ id now sched st E 3≤E inv szB fcB pB =
  E₃ , ≤-trans E≤E₁ (≤-trans E₁≤E₂ E₂≤E₃) , inv₃ , b₃
  where
  E₁    = E * 3 ^ suc Ψ
  E≤E₁  = E≤E*3^ E (suc Ψ)
  3≤E₁  = ≤-trans 3≤E E≤E₁
  cap₁  = capᴱ-mono W E≤E₁
  nid    = Sched.nextNode sched
  sched₁ = proj₂ (mintNode sched)
  -- caps out of fnCapᵉ (scanᵉ f z b) = F ⊔ (Z ⊔ R)
  capf  = ≤-trans (m≤m⊔n (caseWᵗ f ⊔ fnCapᵗ f) _) fcB
  capz  : caseWᵗ z ⊔ fnCapᵗ z ≤ Ψ
  capz  = ≤-trans (m≤m⊔n (caseWᵗ z ⊔ fnCapᵗ z) (fnCapᵉ b))
            (≤-trans (m≤n⊔m (caseWᵗ f ⊔ fnCapᵗ f) _) fcB)
  fcb   = ≤-trans (m≤n⊔m (caseWᵗ z ⊔ fnCapᵗ z) (fnCapᵉ b))
            (≤-trans (m≤n⊔m (caseWᵗ f ⊔ fnCapᵗ f) _) fcB)
  -- sizes out of sizeᵉ (scanᵉ f z b) = suc (sizeᵗ f + sizeᵗ z + sizeᵉ b)
  szf   = ≤-trans (≤-trans (m≤m+n (sizeᵗ f) (sizeᵗ z))
                   (≤-trans (m≤m+n (sizeᵗ f + sizeᵗ z) (sizeᵉ b)) (n≤1+n _))) szB
  szz   = ≤-trans (≤-trans (m≤n+m (sizeᵗ z) (sizeᵗ f))
                   (≤-trans (m≤m+n (sizeᵗ f + sizeᵗ z) (sizeᵉ b)) (n≤1+n _))) szB
  szb   = ≤-trans (≤-trans (m≤n+m (sizeᵉ b) (sizeᵗ f + sizeᵗ z)) (n≤1+n _)) szB
  -- the seed's install pays one eval edge
  seedB = evalTm-cap Ψ W E z (≤-trans (n≤1+n 2) 3≤E)
            (≤-trans (m≤m⊔n (caseWᵗ z) (fnCapᵗ z)) capz) szz
  seedF = fnCap-evalWith Ψ z []ᵃ tt capz
  st₀   = installNode nid (scan-st (evalTm z)) st
  inv₀  = install-INV Ψ (capᴱ W E₁) sched₁ st nid (scan-st (evalTm z))
            (T⇒≡true _ (≤⇒≤ᵇ seedB)) (T⇒≡true _ (≤⇒≤ᵇ seedF))
            (INV?-widen sched₁ st cap₁ inv)
  fB₁   : frameB? (capᴱ W E₁) Ψ (scan-f f nid) ≡ true
  fB₁   = ∧-intro (T⇒≡true _ (≤⇒≤ᵇ (≤-trans szf cap₁)))
                  (T⇒≡true _ (≤⇒≤ᵇ capf))
  sE     = subscribeE g b (scan-f f nid ↠ κ) id now sched₁ st₀
  IH    = subscribeE-walkS Ψ W g b (scan-f f nid ↠ κ) id now sched₁ st₀ E₁
            3≤E₁ inv₀ (≤-trans szb cap₁) fcb
            (∧-intro fB₁ (pathB?-widen κ cap₁ pB))
  E₂    = proj₁ IH
  E₁≤E₂ = proj₁ (proj₂ IH)
  inv₂  = proj₁ (proj₂ (proj₂ IH))
  bB₂   = proj₂ (proj₂ (proj₂ IH))
  cap₂  = capᴱ-mono W E₁≤E₂
  PB    = pushBurst-wet Ψ W g id now (scan-f f nid) κ (proj₁ sE)
            (proj₁ (proj₂ sE)) (proj₂ (proj₂ sE)) E₂
            (≤-trans 3≤E₁ E₁≤E₂) inv₂ (frameB?-widen (scan-f f nid) cap₂ fB₁)
            (pathB?-widen κ (capᴱ-mono W (≤-trans E≤E₁ E₁≤E₂)) pB) bB₂
  E₃    = proj₁ PB
  E₂≤E₃ = proj₁ (proj₂ PB)
  inv₃  = proj₁ (proj₂ (proj₂ PB))
  b₃    = proj₂ (proj₂ (proj₂ PB))

subscribeE-walkS {u = u} Ψ W g (flattenᵉ lim b) κ id now sched st E 3≤E inv szB fcB pB =
  subscribeAll-wet Ψ W g flattenᵒ (flatten-st {t = u} lim 0 [] false) b κ id now sched st E
    3≤E inv refl refl (≤-trans (n≤1+n (sizeᵉ b)) szB) fcB pB
subscribeE-walkS Ψ W g (switchAllᵉ b) κ id now sched st E 3≤E inv szB fcB pB =
  subscribeAll-wet Ψ W g switchᵒ (switch-st nothing false) b κ id now sched st E
    3≤E inv refl refl (≤-trans (n≤1+n (sizeᵉ b)) szB) fcB pB
subscribeE-walkS Ψ W g (exhaustAllᵉ b) κ id now sched st E 3≤E inv szB fcB pB =
  subscribeAll-wet Ψ W g exhaustᵒ (exhaust-st false false) b κ id now sched st E
    3≤E inv refl refl (≤-trans (n≤1+n (sizeᵉ b)) szB) fcB pB

subscribeE-walkS Ψ W g0 (μᵉ body) κ id now sched st E 3≤E inv szB fcB pB =
  E , ≤-refl , inv , refl
subscribeE-walkS Ψ W (gs fuel) (μᵉ body) κ id now sched st E 3≤E inv szB fcB pB =
  proj₁ IH , ≤-trans E≤2E (proj₁ (proj₂ IH)) ,
  proj₁ (proj₂ (proj₂ IH)) , proj₂ (proj₂ (proj₂ IH))
  where
  E≤2E = m≤m+n E (E + 0)
  cap2 = capᴱ-mono W E≤2E
  szU  : sizeᵉ (unfoldμ body) ≤ capᴱ W (2 * E)
  szU  = ≤-trans (size-unfoldμ body)
         (≤-trans (*-mono-≤ szB szB) (≤-reflexive (sym (capᴱ-square W E))))
  fcU  : fnCapᵉ (unfoldμ body) ≤ Ψ
  fcU  = ≤-trans (fnCap-elimG (here refl) (μᵉ body) body) (⊔-lub fcB fcB)
  IH   = subscribeE-walkS Ψ W fuel (unfoldμ body) κ id now sched st (2 * E)
           (≤-trans 3≤E E≤2E) (INV?-widen sched st cap2 inv) szU fcU
           (pathB?-widen κ cap2 pB)

subscribeE-walkS Ψ W g (varᵉ ()) κ id now sched st E 3≤E inv szB fcB pB

subscribeE-walkS Ψ W g (deferᵉ body) κ id now sched st E 3≤E inv szB fcB pB =
  subscribeE-defer-wet Ψ W g body κ id now sched st E 3≤E inv
    (≤-trans (n≤1+n (sizeᵉ body)) szB) fcB pB

------------------------------------------------------------------
-- (W9) THE INPUT CLAUSE.  Five shapes over ONE slot.  INV? carries
-- the slot VECTOR's size and weight as two sums; slotSize-at and
-- slotFnCap-at cut out the single summand this subscription reads,
-- and that is everything the clause knows about what it subscribes.
-- Four shapes are pure state motion — a registration ring, a
-- one-shot, a fresh cold anchor.  `shared` is the one that recurses:
-- its connect walks the stored def, and THAT is the gas edge, so
-- sharedSlot/sharedConnect join the walk's clique.
------------------------------------------------------------------

sharedSlot-wet Ψ W g i d κ id now sched st E 3≤E inv szd fcd pB
  with memberSource (toℕ i) (EvalSt.completedSources st)
-- a share that already completed: completion is re-observable, values
-- are not, so a late subscriber gets close/complete and registers nothing
... | true  = E , ≤-refl , inv , refl
... | false with memberSource (toℕ i) (EvalSt.connectedShares st)
-- already connected: join mid-flight, one registration, no ledger walk
...   | true  = 2 * E , m≤m+n E (E + 0) ,
                register-INV Ψ W E (toℕ i) κ sched st
                  (≤-trans (s≤s z≤n) 3≤E) inv pB ,
                refl
...   | false = sharedConnect-wet Ψ W g i d κ id now sched st E
                  3≤E inv szd fcd pB

-- out of fuel: the dry stub carries a lone close and moves nothing
sharedConnect-wet Ψ W g0 i d κ id now sched st E 3≤E inv szd fcd pB =
  E , ≤-refl , inv , refl
sharedConnect-wet Ψ W (gs fuel) i d κ id now sched st E 3≤E inv szd fcd pB =
  E₂ , E≤E₂ , proj₁ WR , proj₂ WR
  where
  E≤2E  = m≤m+n E (E + 0)
  cap2  = capᴱ-mono W E≤2E
  -- the share owns its registration: it is planted at share-sink
  -- BEFORE the def is walked, so the def's own connect burst sees it
  st₀   = record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st }
  st₁   = register (toℕ i) κ st₀
  inv₁  = register-INV Ψ W E (toℕ i) κ sched st₀ (≤-trans (s≤s z≤n) 3≤E)
            (connectShare-INV Ψ (capᴱ W E) (toℕ i) sched st inv) pB
  -- the gas edge: d is a STORED expression, structurally unrelated to
  -- the `input i` being subscribed, so only the fuel decreases here
  IH    = subscribeE-walkS Ψ W fuel d (share-sink i) id now sched st₁ (2 * E)
            (≤-trans 3≤E E≤2E) inv₁ (≤-trans szd cap2) fcd refl
  E₂    = proj₁ IH
  E≤E₂  = ≤-trans E≤2E (proj₁ (proj₂ IH))
  inv₂  = proj₁ (proj₂ (proj₂ IH))
  bB₂   = proj₂ (proj₂ (proj₂ IH))
  SE    = subscribeE fuel d (share-sink i) id now sched st₁
  WR    = connectWrap-wet Ψ (capᴱ W E₂) i id (burstCompleted (proj₁ SE))
            (proj₁ SE) (proj₁ (proj₂ SE)) (proj₂ (proj₂ SE)) inv₂ bB₂

subscribeE-input-wet {Γ = Γ} Ψ W g i κ id now sched st E 3≤E inv pB
  with Sched.slots sched i
     | slotSize-at Ψ (capᴱ W E) i sched st inv
     | slotFnCap-at Ψ (capᴱ W E) i sched st inv

-- a shared def: connect once, ever; then join
... | shared d | szd | fcd =
      sharedSlot-wet Ψ W g i d κ id now sched st E 3≤E inv szd fcd pB

-- a cold with no async tail: born and spent inside its own burst —
-- nothing registered, nothing scheduled, one ledger-free one-shot
... | scripted (cold sy []) | szs | fcs =
      E , ≤-refl , inv ,
      ∧-intro
        (all-++-intro _ (map value sy) _
          (mapValue-B (capᴱ W E) Ψ (lookup Γ i) sy
            (sumVals-B (capᴱ W E) Ψ (lookup Γ i) sy
              (≤-trans (≤-trans (m≤m+n _ 0) (n≤1+n _)) szs)
              (≤-trans (m≤m+n _ 0) fcs)))
          refl)
        refl

-- a cold WITH a tail: per-subscription anchoring — a fresh source and
-- ordinal, the tail resolved against this subscription's tick, one
-- registration.  resolve only RETIMES, so both slot bounds ride through
... | scripted (cold sy (tv ∷ tvs)) | szs | fcs =
      2 * E , E≤2E ,
      register-INV Ψ W E src κ sched₃ st (≤-trans (s≤s z≤n) 3≤E) inv₃ pB ,
      ∧-intro
        (mapValue-B (capᴱ W (2 * E)) Ψ (lookup Γ i) sy
          (valsB?-widen (lookup Γ i) sy cap2 syB))
        refl
      where
      E≤2E   = m≤m+n E (E + 0)
      cap2   = capᴱ-mono W E≤2E
      src    = Sched.nextSource sched
      sched₁ = proj₂ (mintSource sched)
      ord    = Sched.nextOrdinal sched₁
      sched₂ = proj₂ (mintOrdinal sched₁)
      anchored : LiveSource Γ
      anchored = record { source = src ; ordinal = ord ; elemTy = lookup Γ i
                        ; pending = resolve now (tv ∷ tvs) }
      sched₃ = record sched₂ { live = anchored ∷ Sched.live sched₂ }
      -- the tail's own two sums, split off the slot's.  Both summands
      -- are given: the goal pins only the tail, and nothing can recover
      -- the sync side by inverting _+_
      syncSz = sum (map (sizeᵛ (lookup Γ i)) sy)
      tailSum = sum (map (λ p → sizeᵛ (lookup Γ i) (Timed.val p)) (tv ∷ tvs))
      syncFc = sum (map (fnCapᵛ (lookup Γ i)) sy)
      tailFcSum = sum (map (λ p → fnCapᵛ (lookup Γ i) (Timed.val p)) (tv ∷ tvs))
      tailSz = ≤-trans (m≤n+m tailSum syncSz)
                       (≤-trans (n≤1+n (syncSz + tailSum)) szs)
      tailFc = ≤-trans (m≤n+m tailFcSum syncFc) fcs
      inv₃ = addLive-INV Ψ (capᴱ W E) sched₂ st anchored
               (resolve-bounded (capᴱ W E) now (tv ∷ tvs) tailSz)
               (resolve-measure (fnCapᵛ (lookup Γ i)) Ψ now (tv ∷ tvs) tailFc)
               inv
      syB = sumVals-B (capᴱ W E) Ψ (lookup Γ i) sy
              (≤-trans (≤-trans (m≤m+n _ _) (n≤1+n _)) szs)
              (≤-trans (m≤m+n _ _) fcs)

-- a hot: already live at the slot's own source/ordinal.  Either it is
-- spent (immediate close/complete, nothing registered) or this is just
-- one more registration — fan-out IS that multiplicity
... | scripted (hot _) | szs | fcs
      with memberSource (toℕ i) (EvalSt.completedSources st)
...   | true  = E , ≤-refl , inv , refl
...   | false = 2 * E , m≤m+n E (E + 0) ,
                register-INV Ψ W E (toℕ i) κ sched st
                  (≤-trans (s≤s z≤n) 3≤E) inv pB ,
                refl

------------------------------------------------------------------
-- THE DELIVERY CLIQUE.  One arrival, one chain: fold the value list
-- sinkward through the frames (stepFrame-wet at every hop, which is
-- where the ledger actually moves), and at a share boundary hand off
-- to the fan-out — one emit per registration the share owes, each
-- folded back through foldPath.  Nothing here mints values: the
-- frames do, and they are already accounted for.
------------------------------------------------------------------

-- the root: assemble the envelope.  evs, then the values, then the
-- completion if this emit carries one
foldPath-wet {u = u} Ψ W sf gas id now envSrc root vals evs fin sched st E
             3≤E inv pB vB eB =
  E , ≤-refl , inv ,
  ∧-intro
    (all-++-intro _ evs _ eB
      (all-++-intro _ (map value vals) _
        (mapValue-B (capᴱ W E) Ψ u vals vB)
        (finList-B (capᴱ W E) Ψ fin)))
    refl

-- the share boundary: the chain's own valueless emit announces the
-- handoff, then the share fans the SAME values out to its own
-- registrations — the diamond, batched by construction
foldPath-wet Ψ W sf gas id now envSrc (share-sink i) vals evs fin sched st E
             3≤E inv pB vB eB =
  E′ , E≤E′ , inv′ ,
  ∧-intro (all-++-intro _ evs _ (eventsB?-widen evs cap′ eB) refl) bB′
  where
  DS   = dispatchShare-wet Ψ W sf gas id now i vals fin sched st E 3≤E inv vB
  E′   = proj₁ DS
  E≤E′ = proj₁ (proj₂ DS)
  inv′ = proj₁ (proj₂ (proj₂ DS))
  bB′  = proj₂ (proj₂ (proj₂ DS))
  cap′ = capᴱ-mono W E≤E′

-- a frame hop: step it, then keep folding down the shorter path
foldPath-wet Ψ W sf gas id now envSrc (f ↠ path′) vals evs fin sched st E
             3≤E inv pB vB eB =
  E₂ , ≤-trans E≤E₁ E₁≤E₂ , inv₂ , bB₂
  where
  SF   = stepFrame-wet Ψ W sf id now f path′ vals fin sched st E 3≤E inv
           (proj₁ (∧-true (frameB? (capᴱ W E) Ψ f) _ pB))
           (proj₂ (∧-true (frameB? (capᴱ W E) Ψ f) _ pB)) vB
  E₁    = proj₁ SF
  E≤E₁  = proj₁ (proj₂ SF)
  inv₁  = proj₁ (proj₂ (proj₂ SF))
  vB₁   = proj₁ (proj₂ (proj₂ (proj₂ SF)))
  eB₁   = proj₂ (proj₂ (proj₂ (proj₂ SF)))
  cap₁  = capᴱ-mono W E≤E₁
  step  = stepFrame sf id now f path′ vals fin sched st
  IH    = foldPath-wet Ψ W sf gas id now envSrc path′ (proj₁ step)
            (evs ++ proj₁ (proj₂ step)) (proj₁ (proj₂ (proj₂ step)))
            (proj₁ (proj₂ (proj₂ (proj₂ step))))
            (proj₂ (proj₂ (proj₂ (proj₂ step)))) E₁
            (≤-trans 3≤E E≤E₁) inv₁
            (pathB?-widen path′ cap₁
              (proj₂ (∧-true (frameB? (capᴱ W E) Ψ f) _ pB)))
            vB₁
            (all-++-intro _ evs _ (eventsB?-widen evs cap₁ eB) eB₁)
  E₁≤E₂ = proj₁ (proj₂ IH)
  E₂    = proj₁ IH
  inv₂  = proj₁ (proj₂ (proj₂ IH))
  bB₂   = proj₂ (proj₂ (proj₂ IH))

-- out of dispatch gas: unreachable in a real run (the telescope bound
-- is the context size), and free when it does fire
dispatchShare-wet Ψ W sf zero id now i vals fin sched st E 3≤E inv vB =
  E , ≤-refl , inv , refl
dispatchShare-wet {Γ = Γ} Ψ W sf (suc gas) id now i vals fin sched st E
                  3≤E inv vB =
  E′ , E≤E′ ,
  shareFinish-INV Ψ (capᴱ W E′) i fin (proj₁ GOr)
    (proj₁ (proj₂ GOr)) (proj₂ (proj₂ GOr)) inv′ ,
  subst (λ b → burstB? (capᴱ W E′) Ψ b ≡ true)
        (sym (shareFinish-burst i fin (proj₁ GOr)
               (proj₁ (proj₂ GOr)) (proj₂ (proj₂ GOr))))
        bB′
  where
  st₀  = shareLatch i fin st
  inv₀ = shareLatch-INV Ψ (capᴱ W E) i fin sched st inv
  adm  = shareAdmit i (EvalSt.registry st)
  admB = shareAdmit-B (capᴱ W E) Ψ i (EvalSt.registry st)
           (proj₁ (proj₂ (proj₂ (proj₂ (INV-parts Ψ (capᴱ W E) sched st inv)))))
  GO   = shareGo-wet Ψ W sf gas id now i vals fin adm sched st₀ E 3≤E inv₀ admB vB
  GOr  = shareGo sf gas id now i vals fin adm sched st₀
  E′   = proj₁ GO
  E≤E′ = proj₁ (proj₂ GO)
  inv′ = proj₁ (proj₂ (proj₂ GO))
  bB′  = proj₂ (proj₂ (proj₂ GO))

shareGo-wet Ψ W sf gas id now i vals fin [] sched st E 3≤E inv pB vB =
  E , ≤-refl , inv , refl
shareGo-wet {Γ = Γ} Ψ W sf gas id now i vals fin ((rid , q) ∷ ps) sched st E
            3≤E inv pB vB
  with any (_≡ᵇ rid) (EvalSt.cancelled st)
-- cut earlier this cascade: its close already rode the cutting emit
... | true  = shareGo-wet Ψ W sf gas id now i vals fin ps sched st E 3≤E inv
                (proj₂ (∧-true (pathB? (capᴱ W E) Ψ q) _ pB)) vB
... | false = E₂ , ≤-trans E≤E₁ E₁≤E₂ , inv₂ ,
              all-++-intro _ (proj₁ FPr) _
                (burstB?-widen (proj₁ FPr) cap₂ bB₁) bB₂
  where
  st₀  = record st { delivered = rid ∷ EvalSt.delivered st }
  FP   = foldPath-wet Ψ W sf gas id now (toℕ i) q vals
           (if fin then close (toℕ i) exhausted ∷ [] else []) fin sched st₀ E
           3≤E (delivered-INV Ψ (capᴱ W E) rid sched st inv)
           (proj₁ (∧-true (pathB? (capᴱ W E) Ψ q) _ pB)) vB
           (closeList-B (capᴱ W E) Ψ (toℕ i) fin)
  FPr  = foldPath sf gas id now (toℕ i) q vals
           (if fin then close (toℕ i) exhausted ∷ [] else []) fin sched st₀
  E₁   = proj₁ FP
  E≤E₁ = proj₁ (proj₂ FP)
  inv₁ = proj₁ (proj₂ (proj₂ FP))
  bB₁  = proj₂ (proj₂ (proj₂ FP))
  cap₁ = capᴱ-mono W E≤E₁
  IH   = shareGo-wet Ψ W sf gas id now i vals fin ps
           (proj₁ (proj₂ FPr)) (proj₂ (proj₂ FPr)) E₁
           (≤-trans 3≤E E≤E₁) inv₁
           (allPathB-widen ps cap₁
             (proj₂ (∧-true (pathB? (capᴱ W E) Ψ q) _ pB)))
           (valsB?-widen (lookup Γ i) vals cap₁ vB)
  E₂    = proj₁ IH
  E₁≤E₂ = proj₁ (proj₂ IH)
  inv₂  = proj₁ (proj₂ (proj₂ IH))
  bB₂   = proj₂ (proj₂ (proj₂ IH))
  cap₂  = capᴱ-mono W E₁≤E₂

-- one arrival seeded into one chain: chainStep is foldPath with the
-- arrival's value, its tick, and (when the source is spent) this
-- registration's own exhausted close
chainStep-wet {n = n} {e = e} Ψ W id a path sched st E 3≤E inv pB vB =
  foldPath-wet Ψ W (budgetAt e (Sched.slots sched) id) n id (arrTick a)
    (arrSource a) path (arrVal a ∷ [])
    (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else [])
    (Arrival.isLast a) sched st E 3≤E inv pB (∧-intro vB refl)
    (closeList-B (capᴱ W E) Ψ (arrSource a) (Arrival.isLast a))

------------------------------------------------------------------
-- the *All re-entry, the clique's last link: one inner subscription
-- per emitted outer value.  g0 is the dry stub (a lone close, no
-- ledger); gs peels one fuel unit and re-enters subscribeE-walkS on
-- the inner — a runtime VALUE, so the gas is what decreases.
------------------------------------------------------------------

subscribeInner-wet Ψ W g0 op allNid κ id now o sched st E 3≤E inv oB pB =
  E , ≤-refl , inv , refl , refl
subscribeInner-wet {t = t} {u = u} Ψ W (gs fuel) op allNid κ id now o sched st E
                   3≤E inv oB pB =
  E′ , E≤E′ , inv′ ,
  -- s is the burst's element type (u); the phantom A is the ROOT's
  -- (Val Γ t) — that is what subscribeInner's back-channel carries
  splitBurst-vals-B {s = u} {u = t} (capᴱ W E′) Ψ (proj₁ sE) bB ,
  splitBurst-bk-B {s = u} {u = t} (capᴱ W E′) Ψ (proj₁ sE)
  where
  inst   = Sched.nextNode sched
  sched₀ = record sched { nextNode = suc inst }
  sE     = subscribeE fuel o (from-inner op allNid inst ↠ κ) id now sched₀ st
  IH     = subscribeE-walkS Ψ W fuel o (from-inner op allNid inst ↠ κ) id now
             sched₀ st E 3≤E inv
             (≤ᵇ⇒≤ _ _ (T-to (proj₁ (∧-true _ _ oB))))
             (≤ᵇ⇒≤ _ _ (T-to (proj₂ (∧-true _ _ oB))))
             (∧-intro refl pB)
  E′     = proj₁ IH
  E≤E′   = proj₁ (proj₂ IH)
  inv′   = proj₁ (proj₂ (proj₂ IH))
  bB     = proj₂ (proj₂ (proj₂ IH))

thruConsume-wet {u = u} Ψ W g flattenᵒ nid κ id now o sched st E 3≤E inv oB pB
  with lookupNode nid (EvalSt.nodes st)
     | lookupNode-B (capᴱ W E) Ψ nid (EvalSt.nodes st)
         (stB-nodes (capᴱ W E) sched st (proj₁ (INV-parts Ψ (capᴱ W E) sched st inv)))
         (fcB-nodes Ψ sched st (proj₁ (proj₂ (INV-parts Ψ (capᴱ W E) sched st inv))))
... | just (flatten-st {w} lim act q od) | nb with w ≟ᵗ u
...   | no _ = E , ≤-refl , inv , refl , refl
...   | yes refl with hasRoom lim act
...     | false =
  E , ≤-refl ,
  install-INV Ψ (capᴱ W E) sched st nid (flatten-st lim act (q ++ o ∷ []) od)
    (all-++-intro _ q _ (proj₁ nb)
      (∧-intro (proj₁ (∧-true _ _ oB)) refl))
    (all-++-intro _ q _ (proj₂ nb)
      (∧-intro (proj₂ (∧-true _ _ oB)) refl))
    inv ,
  refl , refl
...     | true =
  E₁ , E≤E₁ , flattenBump-INV Ψ (capᴱ W E₁) nid done sched₁ st₁ inv₁ ,
  vsB , bsB
  where
  SI   = subscribeInner-wet Ψ W g flattenᵒ nid κ id now o sched st E 3≤E inv oB pB
  SI₄  = subscribeInner g flattenᵒ nid κ id now o sched st
  done = proj₁ (proj₂ (proj₂ (proj₂ SI₄)))
  sched₁ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ SI₄))))
  st₁  = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SI₄))))
  E₁   = proj₁ SI
  E≤E₁ = proj₁ (proj₂ SI)
  inv₁ = proj₁ (proj₂ (proj₂ SI))
  vsB  = proj₁ (proj₂ (proj₂ (proj₂ SI)))
  bsB  = proj₂ (proj₂ (proj₂ (proj₂ SI)))
thruConsume-wet Ψ W g flattenᵒ nid κ id now o sched st E 3≤E inv oB pB
    | nothing | _ = E , ≤-refl , inv , refl , refl
thruConsume-wet Ψ W g flattenᵒ nid κ id now o sched st E 3≤E inv oB pB
    | just (scan-st _) | _ = E , ≤-refl , inv , refl , refl
thruConsume-wet Ψ W g flattenᵒ nid κ id now o sched st E 3≤E inv oB pB
    | just (take-st _) | _ = E , ≤-refl , inv , refl , refl
thruConsume-wet Ψ W g flattenᵒ nid κ id now o sched st E 3≤E inv oB pB
    | just (switch-st _ _) | _ = E , ≤-refl , inv , refl , refl
thruConsume-wet Ψ W g flattenᵒ nid κ id now o sched st E 3≤E inv oB pB
    | just (exhaust-st _ _) | _ = E , ≤-refl , inv , refl , refl
thruConsume-wet Ψ W g switchᵒ nid κ id now o sched st E 3≤E inv oB pB
  with lookupNode nid (EvalSt.nodes st)
... | just (switch-st cur od) =
  E₁ , E≤E₁ ,
  install-INV Ψ (capᴱ W E₁) (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ SI₄))))) st₂ nid
    (switch-st (if done then nothing else just inst) od) refl refl inv₁ ,
  vsB ,
  all-++-intro _ closes _
    (eventsB?-widen closes (capᴱ-mono W E≤E₁) (proj₂ KL)) bsB
  where
  KL     = switchKill-INV Ψ W E cur sched st inv
  closes = proj₁ (switchKill cur sched st)
  sched₁ = proj₁ (proj₂ (switchKill cur sched st))
  st₁    = proj₂ (proj₂ (switchKill cur sched st))
  SI     = subscribeInner-wet Ψ W g switchᵒ nid κ id now o sched₁ st₁ E 3≤E
             (proj₁ KL) oB pB
  SI₄    = subscribeInner g switchᵒ nid κ id now o sched₁ st₁
  inst   = proj₁ SI₄
  done   = proj₁ (proj₂ (proj₂ (proj₂ SI₄)))
  st₂    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SI₄))))
  E₁     = proj₁ SI
  E≤E₁   = proj₁ (proj₂ SI)
  inv₁   = proj₁ (proj₂ (proj₂ SI))
  vsB    = proj₁ (proj₂ (proj₂ (proj₂ SI)))
  bsB    = proj₂ (proj₂ (proj₂ (proj₂ SI)))
... | nothing                = E , ≤-refl , inv , refl , refl
... | just (scan-st _)       = E , ≤-refl , inv , refl , refl
... | just (take-st _)       = E , ≤-refl , inv , refl , refl
... | just (flatten-st _ _ _ _)    = E , ≤-refl , inv , refl , refl
... | just (exhaust-st _ _)  = E , ≤-refl , inv , refl , refl
thruConsume-wet Ψ W g exhaustᵒ nid κ id now o sched st E 3≤E inv oB pB
  with lookupNode nid (EvalSt.nodes st)
... | just (exhaust-st true od)  = E , ≤-refl , inv , refl , refl
... | just (exhaust-st false od) =
  E₁ , E≤E₁ ,
  install-INV Ψ (capᴱ W E₁) (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ SI₄))))) st₁ nid
    (exhaust-st (not done) od) refl refl inv₁ ,
  vsB , bsB
  where
  SI   = subscribeInner-wet Ψ W g exhaustᵒ nid κ id now o sched st E 3≤E inv oB pB
  SI₄  = subscribeInner g exhaustᵒ nid κ id now o sched st
  done = proj₁ (proj₂ (proj₂ (proj₂ SI₄)))
  st₁  = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SI₄))))
  E₁   = proj₁ SI
  E≤E₁ = proj₁ (proj₂ SI)
  inv₁ = proj₁ (proj₂ (proj₂ SI))
  vsB  = proj₁ (proj₂ (proj₂ (proj₂ SI)))
  bsB  = proj₂ (proj₂ (proj₂ (proj₂ SI)))
... | nothing                = E , ≤-refl , inv , refl , refl
... | just (scan-st _)       = E , ≤-refl , inv , refl , refl
... | just (take-st _)       = E , ≤-refl , inv , refl , refl
... | just (flatten-st _ _ _ _)    = E , ≤-refl , inv , refl , refl
... | just (switch-st _ _)   = E , ≤-refl , inv , refl , refl

thruWalk-wet Ψ W g op nid κ id now [] sched st E 3≤E inv pB vB =
  E , ≤-refl , inv , refl , refl
thruWalk-wet {u = u} Ψ W g op nid κ id now (o ∷ os) sched st E 3≤E inv pB vB =
  E₂ , ≤-trans E≤E₁ E₁≤E₂ , inv₂ ,
  all-++-intro _ vs _ (valsB?-widen u vs cap₁₂ vsB) vs′B ,
  all-++-intro _ bs _ (eventsB?-widen bs cap₁₂ bsB) bs′B
  where
  CS   = thruConsume-wet Ψ W g op nid κ id now o sched st E 3≤E inv
           (proj₁ (∧-true _ _ vB)) pB
  cr   = thruConsume g op nid κ id now o sched st
  vs   = proj₁ cr
  bs   = proj₁ (proj₂ cr)
  E₁   = proj₁ CS
  E≤E₁ = proj₁ (proj₂ CS)
  inv₁ = proj₁ (proj₂ (proj₂ CS))
  vsB  = proj₁ (proj₂ (proj₂ (proj₂ CS)))
  bsB  = proj₂ (proj₂ (proj₂ (proj₂ CS)))
  cap₁ = capᴱ-mono W E≤E₁
  IH   = thruWalk-wet Ψ W g op nid κ id now os
           (proj₁ (proj₂ (proj₂ cr))) (proj₂ (proj₂ (proj₂ cr))) E₁
           (≤-trans 3≤E E≤E₁) inv₁ (pathB?-widen κ cap₁ pB)
           (valsB?-widen (obs u) os cap₁ (proj₂ (∧-true _ _ vB)))
  E₂    = proj₁ IH
  E₁≤E₂ = proj₁ (proj₂ IH)
  inv₂  = proj₁ (proj₂ (proj₂ IH))
  vs′B  = proj₁ (proj₂ (proj₂ (proj₂ IH)))
  bs′B  = proj₂ (proj₂ (proj₂ (proj₂ IH)))
  cap₁₂ = capᴱ-mono W E₁≤E₂

------------------------------------------------------------------
-- the inner *All frame's drain and finish.  flatten is the only
-- op whose completion does more than flip a flag: it walks its
-- parked queue, subscribing stored outers while a lane is free.
------------------------------------------------------------------

flattenDrain-wet Ψ W g allNid κ id now lim act [] sched st E 3≤E inv pB qz qf =
  E , ≤-refl , inv , refl , refl , refl , refl
flattenDrain-wet {s = s} Ψ W g allNid κ id now lim act (o ∷ q) sched st E 3≤E inv pB qz qf
  with hasRoom lim act
-- the gate is shut: nothing runs, and the residue is the input queue
... | false = E , ≤-refl , inv , refl , refl , qz , qf
... | true
  with subscribeInner g flattenᵒ allNid κ id now o sched st
     | subscribeInner-wet Ψ W g flattenᵒ allNid κ id now o sched st E 3≤E inv
         (∧-intro (proj₁ (∧-true (sizeᵉ o ≤ᵇ capᴱ W E) _ qz))
                  (proj₁ (∧-true (fnCapᵉ o ≤ᵇ Ψ) _ qf))) pB
...   | (_ , vs , bs , done , sched₁ , st₁) | (E₁ , E≤E₁ , inv₁ , vsB , bsB) =
  E₂ , ≤-trans E≤E₁ E₁≤E₂ , inv₂ ,
  all-++-intro _ vs _ (valsB?-widen s vs cap₁₂ vsB) vs′B ,
  all-++-intro _ bs _ (eventsB?-widen bs cap₁₂ bsB) bs′B ,
  q′z , q′f
  where
  IH    = flattenDrain-wet Ψ W g allNid κ id now lim (if done then act else suc act)
            q sched₁ st₁ E₁
            (≤-trans 3≤E E≤E₁) inv₁ (pathB?-widen κ (capᴱ-mono W E≤E₁) pB)
            (allsz-widen q (capᴱ-mono W E≤E₁) (proj₂ (∧-true _ _ qz)))
            (proj₂ (∧-true _ _ qf))
  E₂    = proj₁ IH
  E₁≤E₂ = proj₁ (proj₂ IH)
  inv₂  = proj₁ (proj₂ (proj₂ IH))
  vs′B  = proj₁ (proj₂ (proj₂ (proj₂ IH)))
  bs′B  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ IH))))
  q′z   = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH)))))
  q′f   = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH)))))
  cap₁₂ = capᴱ-mono W E₁≤E₂

innerFinish-wet {s = s} Ψ W g flattenᵒ allNid inst κ id now vals sched st E
                3≤E inv pB vB
  with lookupNode allNid (EvalSt.nodes st)
     | lookupNode-B (capᴱ W E) Ψ allNid (EvalSt.nodes st)
         (stB-nodes (capᴱ W E) sched st (proj₁ (INV-parts Ψ (capᴱ W E) sched st inv)))
         (fcB-nodes Ψ sched st (proj₁ (proj₂ (INV-parts Ψ (capᴱ W E) sched st inv))))
... | just (flatten-st {w} lim act q od) | nb with w ≟ᵗ s
...   | yes refl =
  E′ , E≤E′ ,
  install-INV Ψ (capᴱ W E′) sched′ st′ allNid (flatten-st lim act′ q′ od)
    q′z q′f inv′ ,
  all-++-intro _ vals _ (valsB?-widen s vals (capᴱ-mono W E≤E′) vB) vsB ,
  bsB
  where
  DR    = flattenDrain-wet Ψ W g allNid κ id now lim (pred act) q sched st E 3≤E inv pB
            (proj₁ nb) (proj₂ nb)
  dr    = flattenDrain g allNid κ id now lim (pred act) q sched st
  act′  = proj₁ (proj₂ (proj₂ dr))
  q′    = proj₁ (proj₂ (proj₂ (proj₂ dr)))
  sched′ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ dr))))
  st′   = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ dr))))
  E′    = proj₁ DR
  E≤E′  = proj₁ (proj₂ DR)
  inv′  = proj₁ (proj₂ (proj₂ DR))
  vsB   = proj₁ (proj₂ (proj₂ (proj₂ DR)))
  bsB   = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ DR))))
  q′z   = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ DR)))))
  q′f   = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ DR)))))
...   | no _ = E , ≤-refl , inv , vB , refl
innerFinish-wet Ψ W g flattenᵒ allNid inst κ id now vals sched st E 3≤E inv pB vB
    | nothing               | _ = E , ≤-refl , inv , vB , refl
innerFinish-wet Ψ W g flattenᵒ allNid inst κ id now vals sched st E 3≤E inv pB vB
    | just (scan-st _)      | _ = E , ≤-refl , inv , vB , refl
innerFinish-wet Ψ W g flattenᵒ allNid inst κ id now vals sched st E 3≤E inv pB vB
    | just (take-st _)      | _ = E , ≤-refl , inv , vB , refl
innerFinish-wet Ψ W g flattenᵒ allNid inst κ id now vals sched st E 3≤E inv pB vB
    | just (switch-st _ _)  | _ = E , ≤-refl , inv , vB , refl
innerFinish-wet Ψ W g flattenᵒ allNid inst κ id now vals sched st E 3≤E inv pB vB
    | just (exhaust-st _ _) | _ = E , ≤-refl , inv , vB , refl
innerFinish-wet Ψ W g switchᵒ allNid inst κ id now vals sched st E 3≤E inv pB vB
  with lookupNode allNid (EvalSt.nodes st)
... | just (switch-st (just c) od) with c ≡ᵇ inst
...   | true  =
  E , ≤-refl ,
  install-INV Ψ (capᴱ W E) sched st allNid (switch-st nothing od) refl refl inv ,
  vB , refl
...   | false = E , ≤-refl , inv , vB , refl
innerFinish-wet Ψ W g switchᵒ allNid inst κ id now vals sched st E 3≤E inv pB vB
    | just (switch-st nothing od) = E , ≤-refl , inv , vB , refl
innerFinish-wet Ψ W g switchᵒ allNid inst κ id now vals sched st E 3≤E inv pB vB
    | nothing                = E , ≤-refl , inv , vB , refl
innerFinish-wet Ψ W g switchᵒ allNid inst κ id now vals sched st E 3≤E inv pB vB
    | just (scan-st _)       = E , ≤-refl , inv , vB , refl
innerFinish-wet Ψ W g switchᵒ allNid inst κ id now vals sched st E 3≤E inv pB vB
    | just (take-st _)       = E , ≤-refl , inv , vB , refl
innerFinish-wet Ψ W g switchᵒ allNid inst κ id now vals sched st E 3≤E inv pB vB
    | just (flatten-st _ _ _ _) = E , ≤-refl , inv , vB , refl
innerFinish-wet Ψ W g switchᵒ allNid inst κ id now vals sched st E 3≤E inv pB vB
    | just (exhaust-st _ _)  = E , ≤-refl , inv , vB , refl
innerFinish-wet Ψ W g exhaustᵒ allNid inst κ id now vals sched st E 3≤E inv pB vB
  with lookupNode allNid (EvalSt.nodes st)
... | just (exhaust-st act od) =
  E , ≤-refl ,
  install-INV Ψ (capᴱ W E) sched st allNid (exhaust-st false od) refl refl inv ,
  vB , refl
... | nothing                = E , ≤-refl , inv , vB , refl
... | just (scan-st _)       = E , ≤-refl , inv , vB , refl
... | just (take-st _)       = E , ≤-refl , inv , vB , refl
... | just (flatten-st _ _ _ _)    = E , ≤-refl , inv , vB , refl
... | just (switch-st _ _)   = E , ≤-refl , inv , vB , refl
