-- Verify-Budget-Sufficient.Caps-Face.Part7.Ring-Vocabulary
-- frameStep-regAt … sink-entry-ladder
module Verify-Budget-Sufficient.Caps-Face.Part7.Ring-Vocabulary where

open import Data.Bool    using (Bool; true; if_then_else_)
open import Data.Nat     using (ℕ; suc; _+_; _∸_; _⊔_; _≤_)
open import Data.Nat.Properties using (m+[n∸m]≡n; ≤-trans; ≤-refl; ≤-reflexive; m≤m+n; m≤n+m; n≤1+n; ⊔-lub)
open import Data.Nat.Solver     using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.List    using (List; []; _∷_)
open import Data.Bool.ListAction using (all)
open import Data.Fin     using (Fin)
import Data.Fin as Fin
open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []ᵃ; _∷_ to _∷ᵃ_; map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties
  using (concat⁺; tabulate⁺)
  renaming (++⁺ to all-++; ++⁻ˡ to all-++ˡ; ++⁻ʳ to all-++ʳ)
open import Data.Vec     using (Vec; lookup) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit    using (tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst)

open import Rx.Prim      using (Tick; Id; Source; _at_from_as_; Gas; after_,_; close; exhausted;
  InstEvent)
open import Rx.Exp       using (Ctx; Closed; Val; sizeᵉ)
open import Verify-Budget-Sufficient.Nest-Ceiling using
  (Reached; Ent; Pos; reached-room; room-step; room-descend; walk)
open import Verify-Budget-Sufficient.Subscribe-Face using (subscribeInner-caps; innerFinish-caps)
open import Verify-Budget-Sufficient.Nest-Walk using
  (frameClosOK)
open import Verify-Budget-Sufficient.Caps-Depth using
  (depthFold)
open import Rx.Evaluator using (Sched; EvalSt; RegId; _↠_; Frame; map-f; scan-f; take-f; from-inner; thru-outer; Path; regAt;
  dCapᶜ; dWalkᶜ; lvls; iterL; foldPath)
open import Rx.Slots using (Slots; slotsSize)

open import Verify-Budget-Sufficient.Delivery-Walk using
  (module Walk)
open import Verify-Budget-Sufficient.Deliveries using
  (delivN)
open import Verify-Budget-Sufficient.Caps using
  (1≤capsAt-reg; 2≤capsAt-size; Caps; capsAt; capsAt-base-size; capsAt-suc-full; capsH; _⊑ᶜ_;
  dCapᶜ-mono; frameStep; frameStep-mono-j; iterL-mono; lvls-add; lvls-infl; lvls-mono;
  size≤sizeCount; sizeCount)
open import Verify-Budget-Sufficient.Measures using
  (pathLen)

open import Verify-Budget-Sufficient.Caps-Face.Part1 using
  (capsOK?; pathSz?; regsSz?; regsSz?-widen; nestClosOK?ᵛ)
open import Verify-Budget-Sufficient.Caps-Face.Part4 using
  (capsOK?-regs; pathSz?-len; slotsCaps?-capsAt; valsCaps?)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Cascade-Caps using
  (walkH)

frameStep-regAt : ∀ (c : Caps) (j : ℕ) →
  Caps.cReg (frameStep j c) ≡ regAt (Caps.cSize c) (Caps.cReg c) j
frameStep-regAt c j = refl

-- THE FLOOR IS ONE CONJUNCT AND ITS PARTS ARE READ OFF IT, because the
-- three facts the ladder's consumers ask for -- the constants, the slot
-- count, the gas -- are each a summand of the one sum that has to
-- survive a nesting.  Carrying them separately is what let a CONSTANT
-- floor be threaded past the sink head, where the nested round costs a
-- gas and the sum is the only form that pays for it.
-- AND A ROUND'S HEAD ONLY CLIMBS, so a level under the position is a
-- level under every entry of the round that starts there.
ent-infl : ∀ (c : Caps) (d J g i : ℕ) → J ≤ Ent c d J g i
ent-infl c d J g i =
  lvls-infl (Caps.cSize c) (Caps.cWid c) d J
    (dWalkᶜ (Caps.cSize c) (Caps.cWid c) (Caps.cReg c) d g J i)

floor-parts : ∀ (X m gas g : ℕ) → X + m + gas ≤ g → (X ≤ g) × (m ≤ g) × (gas ≤ g)
floor-parts X m gas g h =
    ≤-trans (m≤m+n X m) (≤-trans (m≤m+n (X + m) gas) h)
  , ≤-trans (m≤n+m m X) (≤-trans (m≤m+n (X + m) gas) h)
  , ≤-trans (m≤n+m gas (X + m)) h

-- AND THE REGISTRY IS NOT HERE, WHICH IS THE POINT.  The sink is the
-- one head that prices a registered path, and it used to be handed
-- that pricing as two flat conjuncts carried unstepped past every
-- frame -- a base-cap `regsSz?` and a base-cap path receipt -- because
-- the nodes face read a path at the base cap and nothing stepped could
-- reach it.  It no longer does: the walk carries its own levelled path
-- receipt, so the sink's pricing may be read at the LEVEL, and at the
-- level it is a projection out of the `capsOK?` two conjuncts up.
--
-- SO WHAT WAS A PRESERVATION FAMILY IS NOW A PROJECTION.  Re-establishing
-- a BASE-cap registry pricing across a subscribe is not merely hard, it
-- is false -- a registration's path is built from the observable being
-- subscribed, a closed expression structurally unrelated to the program
-- the base cap was computed from -- and two of the leaves that claimed
-- it died at a witness.  Reading it at the frame's own cap asks
-- nothing of a subscribe at all, since the frame face already reports
-- the level it climbed to and `capsOK?` at that level already says what
-- the registry costs there.
--
-- REFUTED: `Refuted.Subscribe-Inner-Regs-Base` -- the base-cap form,
--   killed at a subscribed inner whose path outgrows any cap the outer
--   program fixes.

WalkHyps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sl : Slots Γ) (id : ℕ) (L : ℕ) (sf : Gas) (gas : ℕ) (nid : Id) (now : Tick)
  (src : Source) (p : Path Γ u t) (vals : List (Val Γ u))
  (evs : List (InstEvent (Val Γ t))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) → Set
WalkHyps {n = n} {e = e} {u = u} sl id L sf gas nid now src p vals evs fin sched st =
  (Sched.slots sched ≡ sl)
  × (capsOK? (frameStep L (capsAt e sl id)) sched st ≡ true)
  × (valsCaps? (frameStep L (capsAt e sl id)) sl vals ≡ true)
  × (all (nestClosOK?ᵛ (frameStep L (capsAt e sl id)) sl u) vals ≡ true)
  × (pathSz? (Caps.cSize (frameStep L (capsAt e sl id))) p ≡ true)
  × (depthFold sf gas nid now src p vals evs fin sched st ≤ capsH e sl id)
  × (Σ ℕ λ g → Σ ℕ λ P →
      (4 + (sizeᵉ e + slotsSize sl) + n + gas ≤ g)
      × (iterL (Caps.cSize (capsAt e sl id)) (Caps.cWid (capsAt e sl id)) (capsH e sl id)
               (pathLen p) L
           ≤ P)
      × Reached (capsAt e sl id) (capsH e sl id) P g)

-- THE CLOSURE READING IS CARRIED BY THE WALK, NOT DERIVED AT THE
-- FRAME.  A `thru-outer` is handed an inner observable and owes its
-- size measured THROUGH the slot telescope, which is a strictly
-- stronger reading than the caps receipt beside it: `valCaps?` charges
-- the value's own syntax and nothing the slots it names expand to, and
-- the two come apart at the first shared definition.
--
-- AND IT CANNOT BE DERIVED FROM THAT RECEIPT, AT ANY CAP.  The
-- standing reading was that `capsAt`'s size is a tower and a tower
-- might simply dominate a telescope.  It cannot, and the tower's size
-- is not what decides it: the deficit is PER REFERENCE, so the value
-- the premise admits grows with the cap and carries the deficit up with
-- it.  A `map` spine whose every step is a template naming the slot
-- costs three of syntax and nine of closure per step, a fixed ratio at
-- every length, so at each cap one member of the family is admitted and
-- reads a closure above it.  So the reading is a HYPOTHESIS of the
-- walk, established where the values are admitted and preserved across
-- every frame that rebuilds them.
--
-- AND THE WIDTH CONJUNCT VERY NEARLY SUPPLIES IT, which is the half
-- worth keeping: references CAN be capped by `cWid`, since
-- `outWⱽ (ofᵉ ts)` is the list's length, so N references side by side
-- run out at the width.  The spine is where that gate is absent --
-- `outWⱽ` walks straight through a `mapᵉ` and every `dW` clause is a
-- join -- so the family sits at width one however many references it
-- names.  Width bounds how many references arrive TOGETHER; the closure
-- reading counts how many there are.
--
-- REFUTED: `Refuted.Nest-Clos-Cap-Free` -- the derivation, verbatim, at
--   `frameStep 0 (capsAt … 0)`: the spine family above, its length read
--   off the cap by a hand-rolled third, with `init-capsOK?` supplying
--   the state premise and `capsAt-base-size`/`capsAt-base-wid` the two
--   floors.  It is what closes the question `Refuted.Nest-Clos-Flat`
--   left standing.
-- REFUTED: `Refuted.Thru-Fit-Frame-Slot` -- the frame head WITHOUT a
--   resolved-size premise, at a telescope each of whose layers doubles
--   its predecessor: every term of the grant is pinned at its floor by
--   an arrival that merely NAMES the slot, so the deficit diverges
--   rather than crossing.  That is the argument for the premise existing
--   at all, and its `parent-premise-absurd` is the other half -- the
--   cap those rows are read at does not admit the telescope, so what
--   they kill is the premise-free form and not this one.
-- REFUTED: `Refuted.Nest-Clos-Flat` -- the same reading stated over an
--   ARBITRARY cap rather than `capsAt`'s.  The witness cap is the
--   value's own `sizeᵉ`, so the premise holds by construction at every
--   size the family reaches and raising the cap raises the admitted
--   value with it; three references to one slot read `4 6 8` of syntax
--   against `10 18 26` of closure.
-- REFUTED: `Refuted.Clos-Wrap-Sum` -- the subscribe-side ceiling's
--   traded sum, which is the one quantity in the tier that prices a
--   slot's own BODY rather than counting slots, and so the obvious thing
--   to transport here.  Both factors of `slotWrap` are
--   nesting-denominated and one is a bare `nestDᵉ`, so a slot whose
--   definition wears no `*All` head contributes nothing however large
--   its body is; a pure-`map` vocabulary reads the whole sum at zero
--   against a closure of ten, and the stratum SCALE cannot repair it.

-- THE FRAME-LOCAL LEAF, WHICH IS `⊤` AT FOUR OF THE FIVE HEADS AND SO
-- was never a statement about a walk at all.  Matching on the frame
-- says so in code: only a `thru-outer` carries an obligation, and what
-- it carries is the closure reading of the values it is about to
-- subscribe, one value at a time.
walk-frame-clos : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (sl : Slots Γ) (id : ℕ) (L : ℕ) (sf : Gas) (gas : ℕ) (nid : Id) (now : Tick)
  (src : Source) (f : Frame Γ s u) (p : Path Γ u t) (vals : List (Val Γ s))
  (evs : List (InstEvent (Val Γ t))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  WalkHyps sl id L sf gas nid now src (f ↠ p) vals evs fin sched st →
  frameClosOK (frameStep L (capsAt e sl id)) sl f vals
walk-frame-clos sl id L sf gas nid now src (map-f _) p vals evs fin sched st H = tt
walk-frame-clos sl id L sf gas nid now src (scan-f _ _) p vals evs fin sched st H = tt
walk-frame-clos sl id L sf gas nid now src (take-f _) p vals evs fin sched st H = tt
walk-frame-clos sl id L sf gas nid now src (from-inner _ _ _) p vals evs fin sched st H = tt
walk-frame-clos sl id L sf gas nid now src (thru-outer _ _) p vals evs fin sched st
  (_ , _ , _ , hcl , _) = hcl

-- WHAT THE REGISTRY IS PRICED AT, AND IT IS THE INSTANT'S EXIT CAP
-- rather than its entry one.  A registration's path is built from the
-- observable being subscribed, and a runtime observable is a CLOSED
-- EXPRESSION structurally unrelated to the program the entry cap was
-- computed from -- so an entry-cap pricing of the registry is not
-- preservable across a subscribe at all, at any enlargement of that
-- cap.  What IS big enough is the cap the recurrence's own step
-- reaches: `capsAt (suc id)` is `frameStep (sizeCount c d) c`, and the
-- walk's ceiling is that same count, so every level a subscribe can
-- climb to is componentwise under it.
--
-- AND AT THAT CAP THE FACT IS NOT A SEPARATE OBLIGATION, which is the
-- whole payoff.  `capsOK?` already carries `regsSz?` at whatever cap
-- it is read at, and the walk holds a levelled `capsOK?` at every
-- state it passes through -- so the registry's pricing is a
-- PROJECTION out of a receipt already in hand plus one widening, and
-- the frame-by-frame preservation family that used to thread it, two
-- of whose leaves were machine-refuted, is gone.  A subscribe's own
-- registrations are priced by the subscribe face, which reports the
-- level it climbed to; nothing here re-proves that.
RegsBase : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (st : EvalSt e) → Set
RegsBase {e = e} sl id st =
  regsSz? (Caps.cSize (capsAt e sl (suc id))) (EvalSt.registry st) ≡ true

-- THE PROJECTION, and it is the only route to a `RegsBase` there is.
-- Every level the walk reaches sits under the recurrence's step count
-- by its own ceiling, and `capsAt-suc-full` says the cap at that count
-- IS the exit cap -- so a levelled caps receipt widens into the
-- registry's pricing componentwise.
regs-exit : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (L : ℕ) (sched : Sched Γ) (st : EvalSt e) →
  L ≤ sizeCount (capsAt e sl id) (capsH e sl id) ⊔ Caps.cSize (capsAt e sl id) →
  capsOK? (frameStep L (capsAt e sl id)) sched st ≡ true →
  RegsBase sl id st
regs-exit {e = e} sl id L sched st hL cok =
  regsSz?-widen (EvalSt.registry st) (proj₁ lift⊑)
    (capsOK?-regs (frameStep L (capsAt e sl id)) sched st cok)
  where
  c   = capsAt e sl id
  d   = capsH e sl id
  2≤S = 2≤capsAt-size e sl id
  lift⊑ : frameStep L c ⊑ᶜ capsAt e sl (suc id)
  lift⊑ = subst (λ x → frameStep L c ⊑ᶜ x) (sym (capsAt-suc-full e sl id))
            (frameStep-mono-j c 2≤S
              (≤-trans hL (⊔-lub ≤-refl
                 (size≤sizeCount c d 2≤S (1≤capsAt-reg e sl id)))))

-- WHAT ONE TURN OF THE RING CARRIES, and it is a ROUND package rather
-- than a flat one.  The ring is the walk's SECOND recursion -- over
-- admitted registrations instead of over a path -- so what has to
-- reproduce itself across a turn is everything a registered chain is
-- walked UNDER: the schedule's slots, the levelled caps receipt, the
-- arriving values' pricing, and the position the round has climbed
-- to.
--
-- THE POSITION IS WHAT A FLAT CEILING CANNOT REPLACE.  A level under
-- the count says nothing about how much of the count is unspent, so a
-- turn that advances the level has no ground to stand the next turn
-- on.  `Reached … J (suc g)` plus `Lv ≤ Ent … J g k` says instead that
-- the level is the `k`-th position of a round entered with `g` to
-- spend -- from which the ceiling is derivable and the NEXT position
-- is one `ent-step` away.  The path receipt is not here: each entry
-- brings its own, off the admitted list's `admSz?`.
--
-- TWIN: `arr-chains-caps-go` -- the cascade's fold over its chains,
--   carrying exactly this package over the same round.
RingState : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (i : Fin n) (vals : List (Val Γ (lookup Γ i)))
  (gas Lv J g k : ℕ) (sched : Sched Γ) (st : EvalSt e) → Set
RingState {n = n} {Γ = Γ} {e = e} sl id i vals gas Lv J g k sched st =
  (Sched.slots sched ≡ sl)
  × (capsOK? (frameStep Lv (capsAt e sl id)) sched st ≡ true)
  × (valsCaps? (frameStep Lv (capsAt e sl id)) sl vals ≡ true)
  × (all (nestClosOK?ᵛ (frameStep Lv (capsAt e sl id)) sl (lookup Γ i)) vals ≡ true)
  × (4 + (sizeᵉ e + slotsSize sl) + n + gas ≤ g)
  × Reached (capsAt e sl id) (capsH e sl id) J (suc g)
  × (Lv ≤ Ent (capsAt e sl id) (capsH e sl id) J g k)

-- AND THE CEILING IS DERIVED FROM THE POSITION RATHER THAN CARRIED
-- BESIDE IT.  A position of the delivery walk inherits its room from
-- the base's one gas up -- which is `room-descend` -- and `room-step`
-- says the level that lands on IS the next position.  So the bound the
-- ring's Σ owes at every turn is two rewrites away from the package,
-- and carrying it as its own conjunct would oblige every producer to
-- supply a fact its other conjuncts imply.
ring-room : ∀ (c : Caps) (d g J k Lv : ℕ) → 2 ≤ Caps.cSize c →
  suc k ≤ regAt (Caps.cSize c) (Caps.cReg c) J →
  Reached c d J (suc g) →
  Lv ≤ Ent c d J g (suc k) →
  Lv ≤ sizeCount c d ⊔ Caps.cSize c
ring-room c d g J k Lv 2≤S hi hR hLv =
  ≤-trans hLv
    (≤-trans (≤-reflexive (sym (room-step (Caps.cSize c) (Caps.cWid c) (Caps.cReg c) d g J k)))
             (room-descend c d g J k 2≤S hi (reached-room c d J (suc g) 2≤S hR)))

-- THE STATE ONE TURN OF THE RING LEAVES BEHIND, named so the two leaves
-- and the recursion all read the same object.  A turn delivers into one
-- registration, and what the next turn sees is the schedule and the
-- store that delivery produced -- not the ones it started from, which is
-- the whole reason the ring cannot be a fold over a fixed state.
ringFold : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sf : Gas) (gas : ℕ) (nid : Id) (now : Tick) (i : Fin n)
  (vals : List (Val Γ (lookup Γ i))) (fin : Bool) (rid : RegId)
  (p : Path Γ (lookup Γ i) t) (sched : Sched Γ) (st : EvalSt e) →
  Sched Γ × EvalSt e
ringFold sf gas nid now i vals fin rid p sched st =
    proj₁ (proj₂ r)
  , proj₂ (proj₂ r)
  where
  r = foldPath sf gas nid now (Fin.toℕ i) p vals
        (if fin then close (Fin.toℕ i) exhausted ∷ [] else []) fin sched
        (record st { delivered = rid ∷ EvalSt.delivered st })

-- ONE TURN'S ADVANCE IS THE PATH FOLD, so the level it lands at is the
-- fold's own theorem and not a leaf.  `ringFold` IS `foldPath` at the
-- ring's gas over the entry's own source, the walk skeleton is
-- instantiated at exactly the caps hypotheses here, and its receipt
-- reports the three things the statement asks for: the level, that the
-- walk only climbed to it, and the state fact there.  The increment is
-- the difference, which is why the conclusion is stated at `Lv + L'`
-- and proven at the absolute level the walk names.
--
-- TWIN: `chainStep-caps` -- one chain's step of this same fold, with
--   the same discipline: invariant at the stepped cap, own increment
--   reported.
sink-step-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (sf : Gas) (gas : ℕ) (nid : Id) (now : Tick)
  (i : Fin n) (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
  (rid : RegId) (p : Path Γ (lookup Γ i) t) (Lv : ℕ)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (frameStep Lv (capsAt e sl id)) sched
    (record st { delivered = rid ∷ EvalSt.delivered st }) ≡ true →
  pathSz? (Caps.cSize (frameStep Lv (capsAt e sl id))) p ≡ true →
  valsCaps? (frameStep Lv (capsAt e sl id)) sl vals ≡ true →
  depthFold sf gas nid now (Fin.toℕ i) p vals
    (if fin then close (Fin.toℕ i) exhausted ∷ [] else []) fin sched
    (record st { delivered = rid ∷ EvalSt.delivered st }) ≤ capsH e sl id →
  Σ ℕ λ L′ →
    (Lv + L′
       ≤ lvls (Caps.cSize (capsAt e sl id)) (Caps.cWid (capsAt e sl id)) (capsH e sl id) Lv
           (suc (delivN (record st { delivered = rid ∷ EvalSt.delivered st })
                        (proj₂ (ringFold sf gas nid now i vals fin rid p sched st)))))
    × (capsOK? (frameStep (Lv + L′) (capsAt e sl id))
         (proj₁ (ringFold sf gas nid now i vals fin rid p sched st))
         (proj₂ (ringFold sf gas nid now i vals fin rid p sched st)) ≡ true)
sink-step-caps {e = e} sl id sf gas nid now i vals fin rid p Lv sched st sleq cok hpz hvc hdp =
    W.Res.lvl FP ∸ Lv
  , subst (_≤ CEIL) (sym EQ) (≤-trans (W.Res.hi FP) STEP)
  , subst (λ x → capsOK? (frameStep x c)
                   (proj₁ (ringFold sf gas nid now i vals fin rid p sched st))
                   (proj₂ (ringFold sf gas nid now i vals fin rid p sched st)) ≡ true)
          (sym EQ) (proj₂ (proj₁ (W.Res.good FP)))
  where
  c   = capsAt e sl id
  S   = Caps.cSize c
  Wd  = Caps.cWid c
  d   = capsH e sl id
  2≤S = 2≤capsAt-size e sl id
  st′ = record st { delivered = rid ∷ EvalSt.delivered st }
  slSz : slotsSize sl ≤ Caps.cSize c
  slSz = ≤-trans (m≤n+m (slotsSize sl) (2 + sizeᵉ e)) (capsAt-base-size e sl id)
  module W = Walk {e = e} S Wd (Caps.cReg c) d 2≤S
    (walkH (λ {n′} {Γ′} {t′} {e′} {u′} → subscribeInner-caps {n′} {Γ′} {t′} {e′} {u′})
           (λ {n′} {Γ′} {t′} {e′} {s′} → innerFinish-caps {n′} {Γ′} {t′} {e′} {s′})
           c d sl 2≤S (1≤capsAt-reg e sl id) (slotsCaps?-capsAt e sl id) slSz)
  FP = W.foldPath-go Lv sf gas nid now (Fin.toℕ i) p vals
         (if fin then close (Fin.toℕ i) exhausted ∷ [] else []) fin sched st′
         ((sleq , cok) , capsOK?-regs (frameStep Lv c) sched st′ cok)
         hpz hvc (W.eb-seed Lv (Fin.toℕ i) fin) tt tt hdp
  EQ : Lv + (W.Res.lvl FP ∸ Lv) ≡ W.Res.lvl FP
  EQ = m+[n∸m]≡n (W.Res.lo FP)
  D = delivN st′ (proj₂ (ringFold sf gas nid now i vals fin rid p sched st))
  CEIL = lvls S Wd d Lv (suc D)
  entry≤ : iterL S Wd d (pathLen p) Lv ≤ lvls S Wd d Lv 1
  entry≤ = iterL-mono (pathLen p) _ 2≤S ≤-refl ≤-refl ≤-refl
             (≤-trans (pathSz?-len (Caps.cSize (frameStep Lv c)) p hpz) (n≤1+n _))
  STEP : lvls S Wd d (iterL S Wd d (pathLen p) Lv) D ≤ CEIL
  STEP = ≤-trans (lvls-mono D D 2≤S ≤-refl ≤-refl entry≤ ≤-refl)
                 (≤-reflexive (sym (lvls-add S Wd d Lv 1 D)))

-- ONE TURN'S DELIVERIES AGAINST THE BUDGET READ AT ITS OWN POSITION,
-- which is what makes the advance land on the NEXT position rather than
-- merely somewhere higher.  The gas is the ring's own dispatch budget
-- and the round was entered with at least as much, which is the one
-- thing a level bound could never supply.
--
-- TWIN: `chain-deliv-cap` -- the same reading for a cascade's chain.
sink-deliv-cap : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (sf : Gas) (gas : ℕ) (nid : Id) (now : Tick)
  (i : Fin n) (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
  (rid : RegId) (p : Path Γ (lookup Γ i) t) (Lv J g k : ℕ)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  gas ≤ g →
  capsOK? (frameStep Lv (capsAt e sl id)) sched
    (record st { delivered = rid ∷ EvalSt.delivered st }) ≡ true →
  pathSz? (Caps.cSize (frameStep Lv (capsAt e sl id))) p ≡ true →
  valsCaps? (frameStep Lv (capsAt e sl id)) sl vals ≡ true →
  depthFold sf gas nid now (Fin.toℕ i) p vals
    (if fin then close (Fin.toℕ i) exhausted ∷ [] else []) fin sched
    (record st { delivered = rid ∷ EvalSt.delivered st }) ≤ capsH e sl id →
  Lv ≤ Ent (capsAt e sl id) (capsH e sl id) J g k →
  delivN (record st { delivered = rid ∷ EvalSt.delivered st })
         (proj₂ (ringFold sf gas nid now i vals fin rid p sched st))
    ≤ dCapᶜ (Caps.cSize (capsAt e sl id)) (Caps.cWid (capsAt e sl id))
            (Caps.cReg (capsAt e sl id)) (capsH e sl id) g
            (Pos (capsAt e sl id) (capsH e sl id) J g k)
sink-deliv-cap {e = e} sl id sf gas nid now i vals fin rid p Lv J g k sched st
  sleq hgas cok hpz hvc hdp hLv =
  ≤-trans (W.Res.cnt FP)
          (dCapᶜ-mono {S} {S} {Wd} {Wd} {R} {R} {_} {_} {d} gas g
             2≤S ≤-refl ≤-refl ≤-refl hgas CLIMB)
  where
  c   = capsAt e sl id
  S   = Caps.cSize c
  Wd  = Caps.cWid c
  R   = Caps.cReg c
  d   = capsH e sl id
  2≤S = 2≤capsAt-size e sl id
  st′ = record st { delivered = rid ∷ EvalSt.delivered st }
  slSz : slotsSize sl ≤ Caps.cSize c
  slSz = ≤-trans (m≤n+m (slotsSize sl) (2 + sizeᵉ e)) (capsAt-base-size e sl id)
  module W = Walk {e = e} S Wd R d 2≤S
    (walkH (λ {n′} {Γ′} {t′} {e′} {u′} → subscribeInner-caps {n′} {Γ′} {t′} {e′} {u′})
           (λ {n′} {Γ′} {t′} {e′} {s′} → innerFinish-caps {n′} {Γ′} {t′} {e′} {s′})
           c d sl 2≤S (1≤capsAt-reg e sl id) (slotsCaps?-capsAt e sl id) slSz)
  FP = W.foldPath-go Lv sf gas nid now (Fin.toℕ i) p vals
         (if fin then close (Fin.toℕ i) exhausted ∷ [] else []) fin sched st′
         ((sleq , cok) , capsOK?-regs (frameStep Lv c) sched st′ cok)
         hpz hvc (W.eb-seed Lv (Fin.toℕ i) fin) tt tt hdp
  CLIMB : iterL S Wd d (pathLen p) Lv ≤ Pos c d J g k
  CLIMB = ≤-trans (iterL-mono (pathLen p) _ 2≤S ≤-refl ≤-refl ≤-refl
                     (≤-trans (pathSz?-len (Caps.cSize (frameStep Lv c)) p hpz)
                              (n≤1+n _)))
                  (lvls-mono 1 1 2≤S ≤-refl ≤-refl hLv ≤-refl)

-- THE LADDER THE ENTRY'S WALK IS ENTERED WITH, and it is the round
-- package read one restart down.  A registered chain climbs at most
-- its own path length, `pathSz?` bounds that by one restart, and one
-- restart from the `k`-th position IS the position the round's `walk`
-- constructor reaches with a gas spent.  So what the entry needs is
-- what the ring already holds, at the level below.
sink-entry-ladder : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (i : Fin n) (vals : List (Val Γ (lookup Γ i)))
  (p : Path Γ (lookup Γ i) t) (gas Lv J g k : ℕ)
  (sched : Sched Γ) (st : EvalSt e) →
  RingState {t = t} sl id i vals gas Lv J g k sched st →
  pathSz? (Caps.cSize (frameStep Lv (capsAt e sl id))) p ≡ true →
  suc k ≤ regAt (Caps.cSize (capsAt e sl id)) (Caps.cReg (capsAt e sl id)) J →
  Σ ℕ λ g′ → Σ ℕ λ P →
    (4 + (sizeᵉ e + slotsSize sl) + n + gas ≤ g′)
    × (iterL (Caps.cSize (capsAt e sl id)) (Caps.cWid (capsAt e sl id))
             (capsH e sl id) (pathLen p) Lv
         ≤ P)
    × Reached (capsAt e sl id) (capsH e sl id) P g′
sink-entry-ladder {e = e} sl id i vals p gas Lv J g k sched st
  (_ , _ , _ , _ , hfl , hR , hLv) hpzL hi =
  g , Pos c d J g k , hfl , CLIMB , walk J g k hi hR
  where
  c   = capsAt e sl id
  S   = Caps.cSize c
  W   = Caps.cWid c
  d   = capsH e sl id
  2≤S = 2≤capsAt-size e sl id
  CLIMB : iterL S W d (pathLen p) Lv ≤ Pos c d J g k
  CLIMB = ≤-trans (iterL-mono (pathLen p) _ 2≤S ≤-refl ≤-refl ≤-refl
                     (≤-trans (pathSz?-len (Caps.cSize (frameStep Lv c)) p hpzL)
                              (n≤1+n _)))
                  (lvls-mono 1 1 2≤S ≤-refl ≤-refl hLv ≤-refl)
