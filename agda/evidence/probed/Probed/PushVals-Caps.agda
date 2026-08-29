-- THE BUNDLE THE BURST CARRIES, which is the half of the burst claim
-- nothing had ever instantiated.  Every earlier probe of this family
-- pins `nestCapsOK?` at the state the head is ENTERED at -- that is the
-- statement's premise.  What these leaves assert is the bundle at every
-- frame the descent LEAVES, which is a different state and a different
-- claim, and the two were being read as one because they were conjuncts
-- of a single predicate.
--
-- WHAT IS NOT COVERED, and it is a gap rather than a boundary: the
-- WIDTH conjunct the bundle now also carries -- a bound on the measure
-- under each arrival's own subscribe.  These rows read the caps side
-- only, and the measure is sealed, so instantiating it would need a
-- lower bound of the kind the arr-keyed scan probes pin.
--
-- AND THE TWO ARRIVAL BOOLEANS ARE READ AT THE *All-HEADED PATH ONLY,
-- which is a coverage boundary and named as one.  Those two targets
-- are stated over ANY subscription at ANY path; every row here enters
-- through a `thru-outer` continuation, because that is the shape the
-- consumers of those statements stand at.  The clauses no row reaches
-- are therefore the ones a bare path takes -- and the risky two of
-- those, the defer and the scripted slot, ARE reached, since the gate
-- and async bodies below put both under a `*All` head.
--
-- AND THE LEVEL IS A BOUNDARY, not a gap: the three leaves now take the
-- caps level as a parameter, and these rows are taken at the level the
-- head's own written size fixes -- the SMALLEST any arm passes, since an
-- arm hands in that size joined with its child's.  A larger level is a
-- larger cap and a weaker conjunct, so a row green here is green at
-- every level an arm actually uses.  What is NOT reached is the other
-- direction: level zero, where the step is the identity and the leaf
-- collapses to the flat statement `Refuted.PushVals-Adm-Map` kills.
--
-- EVIDENCE, not a claim: `src` cannot import this file (the library
-- layout makes the name unresolvable from there) and nothing in the
-- proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.
-- TARGET: subscribeE-burst-nest @d2c32b
-- TARGET: pushVals-caps-burstW @338e1f
module Probed.PushVals-Caps where

open import Data.Bool using (Bool; true; false)
open import Data.Unit using (tt)
open import Data.List using (List; []; _∷_; length; map; _++_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Nat.Properties using (_≤?_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (True; toWitness)

open import Rx.Prim using (Gas; g0; gs; Id; Tick; hot; InstEmit)
open import Rx.Exp
  using (Closed; Val; natᵗ; obs; ofᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; nat̂; strmᵗ; deferᵉ;
  syncSizeᵛ; mapᵉ; input; Fn; varᵗ)
open import Rx.Frame-Width using (pWᵛ)
open import Rx.Slots using (Slots; shared; scripted)
open import Rx.Evaluator
  using (subscribeE; root; sched-init; st-init; mintNode; installNode; thru-outer; _↠_; mergeAllᵒ;
  splitEvents;
  switchᵒ; exhaustᵒ; mergeAll-st; switch-st; exhaust-st; Sched; EvalSt; Stream;
  AllOp; NodeId; Path)
open import Verify-Budget-Sufficient.Caps using (arrCapAt; Caps; caps)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (burstCaps?; capsOK?; nestValOK?; slotsCaps?)
open import Verify-Budget-Sufficient.Nest-Walk using (burstNest?; nestCapsOK?; nestClosOK?; pushValsCapsOK; pushValsWidOK;
          pushValsWOK)
open import Verify-Budget-Sufficient.Nest-Burst using (innerW)
open import Verify-Budget-Sufficient.Demand-Programs using (Γ₂; insT)

slots : Slots Γ₂
slots = insT 0 0 0

gasBig : Gas
gasBig = gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs g0)))))))))))))))))))

deepV : ℕ → Val Γ₂ (obs natᵗ)
deepV zero    = ofᵉ (nat̂ 0 ∷ [])
deepV (suc k) = switchAllᵉ (ofᵉ (strmᵗ (deepV k) ∷ []))

wrapped : ℕ → Val Γ₂ (obs (obs (obs natᵗ)))
wrapped k = ofᵉ (strmᵗ (ofᵉ (strmᵗ (deepV k) ∷ [])) ∷
                 strmᵗ (ofᵉ (strmᵗ (deepV k) ∷ [])) ∷ [])

-- THE THREE HEADS, at the caps the neighbouring wrap probe uses: the
-- cap at the value's own sync size and the width at its own frame
-- width, which is the tightest reading the premises admit.
tight : ∀ {u} → Val Γ₂ u → Caps
tight {u} v = caps (syncSizeᵛ u v) (pWᵛ 2 slots u v) 0

rM : ℕ → ℕ → Closed Γ₂ (obs natᵗ)
rM lim k = mergeAllᵉ (just lim) (wrapped k)

qS : ℕ → Closed Γ₂ (obs natᵗ)
qS k = switchAllᵉ (wrapped k)

qX : ℕ → Closed Γ₂ (obs natᵗ)
qX k = exhaustAllᵉ (wrapped k)

-- MEASUREMENT PASS: the burst the descent hands back, and the split
-- each of its instants carries, so the tuple's arity is read rather
-- than guessed.
resM : (lim k : ℕ) → Stream Γ₂ (obs (obs natᵗ)) × Sched Γ₂ × EvalSt (rM lim k)
resM lim k =
  subscribeE gasBig (wrapped k)
    (thru-outer mergeAllᵒ (proj₁ (mintNode (sched-init (rM lim k) slots))) ↠ root) 0 0
    (proj₂ (mintNode (sched-init (rM lim k) slots)))
    (installNode (proj₁ (mintNode (sched-init (rM lim k) slots)))
       (mergeAll-st {t = obs natᵗ} (just lim) 0 [] false)
       (st-init (rM lim k)))

resS : (k : ℕ) → Stream Γ₂ (obs (obs natᵗ)) × Sched Γ₂ × EvalSt (qS k)
resS k =
  subscribeE gasBig (wrapped k)
    (thru-outer switchᵒ (proj₁ (mintNode (sched-init (qS k) slots))) ↠ root) 0 0
    (proj₂ (mintNode (sched-init (qS k) slots)))
    (installNode (proj₁ (mintNode (sched-init (qS k) slots)))
       (switch-st nothing false) (st-init (qS k)))

resX : (k : ℕ) → Stream Γ₂ (obs (obs natᵗ)) × Sched Γ₂ × EvalSt (qX k)
resX k =
  subscribeE gasBig (wrapped k)
    (thru-outer exhaustᵒ (proj₁ (mintNode (sched-init (qX k) slots))) ↠ root) 0 0
    (proj₂ (mintNode (sched-init (qX k) slots)))
    (installNode (proj₁ (mintNode (sched-init (qX k) slots)))
       (exhaust-st false false) (st-init (qX k)))

burstLens : ℕ × ℕ × ℕ
burstLens = length (proj₁ (resM 1 1)) , length (proj₁ (resS 1)) , length (proj₁ (resX 1))

burstLens≡ : burstLens ≡ (1 , 1 , 1)
burstLens≡ = refl

-- THE CONCLUSION, at the state the descent LEAVES, which is what
-- distinguishes these rows from every earlier probe of this family --
-- and read at the ARRIVAL CAP, one caps level above the one the head's
-- premises are pinned at.  That is where the statements put it: an
-- arrival is the head's syntax with payloads substituted in, so it
-- crosses the size key, and the level it crosses by is the head's own
-- written size.  The premises below stay at the entry cap, so a row
-- here is a reading about the gap between the two and not about a
-- single cap satisfying both.
capsM : (lim k W : ℕ) → Set
capsM lim k W =
  pushValsCapsOK (arrCapAt (Caps.cSize (tight {obs (obs natᵗ)} (rM lim k))) (tight {obs (obs natᵗ)} (rM lim k))) 0 slots W gasBig mergeAllᵒ
    (proj₁ (mintNode (sched-init (rM lim k) slots))) root 0 0
    (proj₁ (resM lim k)) (proj₁ (proj₂ (resM lim k))) (proj₂ (proj₂ (resM lim k)))

le : ∀ {x y} → True (x ≤? y) → x ≤ y
le = toWitness

-- THE WIDTH HALF, TAKEN AS A HYPOTHESIS AND NOT AS A ROW.  The measure
-- is sealed, so no numeral discharges it and no `refl` reaches it; what
-- these rows read is the CAPS half, which computes.  Stating the width
-- half as one universally quantified premise is what keeps the row
-- honest about that: it says the caps conjuncts hold at these programs
-- GIVEN the widths, and it claims nothing about the widths themselves.
Widths : ℕ → Set
Widths W = ∀ {s t} {e : Closed Γ₂ t} (fuel : Gas) (op : AllOp) (nid : NodeId)
             (κ : Path Γ₂ s t) (id : Id) (now : Tick) (o : Closed Γ₂ s)
             (sched : Sched Γ₂) (st : EvalSt e) →
             innerW fuel op nid κ id now o sched st ≤ W

capsM-1 : ∀ {W} → Widths W → capsM 1 1 W
capsM-1 hw = refl , refl , refl , refl
        , refl
        , ((le tt , hw _ _ _ _ _ _ _ _ _ , λ { cur od () })
          , (le tt , hw _ _ _ _ _ _ _ _ _ , λ { cur od () }) , tt)
        , 0 , tt

capsS : (k W : ℕ) → Set
capsS k W =
  pushValsCapsOK (arrCapAt (Caps.cSize (tight {obs (obs natᵗ)} (qS k))) (tight {obs (obs natᵗ)} (qS k))) 0 slots W gasBig switchᵒ
    (proj₁ (mintNode (sched-init (qS k) slots))) root 0 0
    (proj₁ (resS k)) (proj₁ (proj₂ (resS k))) (proj₂ (proj₂ (resS k)))

capsS-1 : ∀ {W} → Widths W → capsS 1 W
capsS-1 hw = refl , refl , refl , refl
        , refl
        , ((le tt , hw _ _ _ _ _ _ _ _ _ , λ { cur od refl → hw _ _ _ _ _ _ _ _ _ })
          , (le tt , hw _ _ _ _ _ _ _ _ _ , λ { cur od refl → hw _ _ _ _ _ _ _ _ _ }) , tt)
        , 0 , tt

capsX : (k W : ℕ) → Set
capsX k W =
  pushValsCapsOK (arrCapAt (Caps.cSize (tight {obs (obs natᵗ)} (qX k))) (tight {obs (obs natᵗ)} (qX k))) 0 slots W gasBig exhaustᵒ
    (proj₁ (mintNode (sched-init (qX k) slots))) root 0 0
    (proj₁ (resX k)) (proj₁ (proj₂ (resX k))) (proj₂ (proj₂ (resX k)))

capsX-1 : ∀ {W} → Widths W → capsX 1 W
capsX-1 hw = refl , refl , refl , refl
        , refl
        , ((le tt , hw _ _ _ _ _ _ _ _ _ , λ { cur od () })
          , (le tt , hw _ _ _ _ _ _ _ _ _ , λ { cur od () }) , tt)
        , 0 , tt

-- THE HEAD'S OWN PREMISES, pinned rather than assumed, so the rows
-- above are not evidence about a region the head grants nothing at.
heads : Bool × Bool × Bool
heads = nestValOK? (tight {obs (obs natᵗ)} (rM 1 1)) (obs (obs natᵗ)) (rM 1 1)
      , nestValOK? (tight {obs (obs natᵗ)} (qS 1)) (obs (obs natᵗ)) (qS 1)
      , nestValOK? (tight {obs (obs natᵗ)} (qX 1)) (obs (obs natᵗ)) (qX 1)

heads≡ : heads ≡ (true , true , true)
heads≡ = refl

-- read at the FULL invariant, which is what the leaves now ask for at
-- entry, and at the slot-table bundle beside it -- the two keys the
-- restatement added, pinned here rather than assumed so these rows stay
-- evidence about the statement as it now reads
entry : Bool × Bool × Bool
entry = capsOK? (tight {obs (obs natᵗ)} (rM 1 1)) (sched-init (rM 1 1) slots) (st-init (rM 1 1))
      , capsOK? (tight {obs (obs natᵗ)} (qS 1)) (sched-init (qS 1) slots) (st-init (qS 1))
      , capsOK? (tight {obs (obs natᵗ)} (qX 1)) (sched-init (qX 1) slots) (st-init (qX 1))

entry≡ : entry ≡ (true , true , true)
entry≡ = refl

entryFace : Bool × Bool × Bool
entryFace =
    slotsCaps? (Caps.cSize (tight {obs (obs natᵗ)} (rM 1 1))) (Caps.cWid (tight {obs (obs natᵗ)} (rM 1 1))) slots
  , slotsCaps? (Caps.cSize (tight {obs (obs natᵗ)} (qS 1))) (Caps.cWid (tight {obs (obs natᵗ)} (qS 1))) slots
  , slotsCaps? (Caps.cSize (tight {obs (obs natᵗ)} (qX 1))) (Caps.cWid (tight {obs (obs natᵗ)} (qX 1))) slots

entryFace≡ : entryFace ≡ (true , true , true)
entryFace≡ = refl

-- AND THE CLOSURE PREMISE THE HEADS NOW CARRY, pinned at the same three
-- arrivals.  These programs reference the telescope, so the reading is
-- not the written size by default; what it turns on is whether a slot
-- the arrival names is SCRIPTED, since a scripted slot's closure is one.
headsClos : Bool × Bool × Bool
headsClos = nestClosOK? (tight {obs (obs natᵗ)} (rM 1 1)) slots (rM 1 1)
          , nestClosOK? (tight {obs (obs natᵗ)} (qS 1)) slots (qS 1)
          , nestClosOK? (tight {obs (obs natᵗ)} (qX 1)) slots (qX 1)

headsClos≡ : headsClos ≡ (true , true , true)
headsClos≡ = refl

-- and a second nesting level, and a limit the arrivals do not fit
-- under, so the merge head is read at a limit that REFUSES as well as
-- at one that admits
capsM-2 : ∀ {W} → Widths W → capsM 1 2 W
capsM-2 hw = refl , refl , refl , refl
        , refl
        , ((le tt , hw _ _ _ _ _ _ _ _ _ , λ { cur od () })
          , (le tt , hw _ _ _ _ _ _ _ _ _ , λ { cur od () }) , tt)
        , 0 , tt

capsM-0 : ∀ {W} → Widths W → capsM 0 1 W
capsM-0 hw = refl , refl , refl , refl
        , refl
        , ((le tt , hw _ _ _ _ _ _ _ _ _ , λ { cur od () })
          , (le tt , hw _ _ _ _ _ _ _ _ _ , λ { cur od () }) , tt)
        , 0 , tt

capsS-2 : ∀ {W} → Widths W → capsS 2 W
capsS-2 hw = refl , refl , refl , refl
        , refl
        , ((le tt , hw _ _ _ _ _ _ _ _ _ , λ { cur od refl → hw _ _ _ _ _ _ _ _ _ })
          , (le tt , hw _ _ _ _ _ _ _ _ _ , λ { cur od refl → hw _ _ _ _ _ _ _ _ _ }) , tt)
        , 0 , tt

capsX-2 : ∀ {W} → Widths W → capsX 2 W
capsX-2 hw = refl , refl , refl , refl
        , refl
        , ((le tt , hw _ _ _ _ _ _ _ _ _ , λ { cur od () })
          , (le tt , hw _ _ _ _ _ _ _ _ _ , λ { cur od () }) , tt)
        , 0 , tt

-- WHICH CONJUNCTS COULD HAVE FAILED, and the answer is not all of
-- them.  Read at a cap granting nothing, the invariant at the very
-- state the descent LEAVES still reads true at all three heads -- so
-- that conjunct is REACHED here and cannot fail here, and a row above
-- is evidence for the other five.  The census below says why: the
-- left state carries one node and an empty registry and live set, so
-- four of the invariant's five conjuncts are quantified over nothing
-- and the fifth is a width reading on an empty queue.
starved : Caps
starved = caps 0 0 0

left-starved : Bool × Bool × Bool
left-starved =
    nestCapsOK? starved (proj₁ (proj₂ (resM 1 1))) (proj₂ (proj₂ (resM 1 1)))
  , nestCapsOK? starved (proj₁ (proj₂ (resS 1))) (proj₂ (proj₂ (resS 1)))
  , nestCapsOK? starved (proj₁ (proj₂ (resX 1))) (proj₂ (proj₂ (resX 1)))

left-starved≡ : left-starved ≡ (true , true , true)
left-starved≡ = refl

census : ℕ × ℕ × ℕ
census = length (EvalSt.registry (proj₂ (proj₂ (resM 1 1))))
       , length (Sched.live (proj₁ (proj₂ (resM 1 1))))
       , length (EvalSt.nodes (proj₂ (proj₂ (resM 1 1))))

census≡ : census ≡ (0 , 0 , 1)
census≡ = refl

-- THE SHARE-FREE SHAPES HAND BACK ONE INSTANT, so every row above has
-- a `⊤` tail: a two-armed synchronous source, a `deferᵉ` gate whose
-- second arm fires a tick later, and a scripted slot delivering j
-- values over j ticks, at j = 1, 2, 3, all return a single-instant
-- burst.  The ONE route to a longer subscribe-frame burst is a share
-- CONNECT -- `sharedConnect` conses its own head instant in front of
-- the def's plumbed burst -- and `pushBurst` preserves instant count,
-- so the multi-instant region of these targets is reachable exactly
-- through an inner that connects a share.  The rows below walk it:
-- the burst is pinned at length TWO, and the second instant's bundle
-- is read at the state the first instant's step leaves, which is the
-- recursive tail every other row's `⊤` never reaches.
-- the minimal connecting vocabulary: a share at index zero whose def
-- is a one-value synchronous source, so the connect burst is one
-- instant and the whole subscribe-frame burst is exactly two
insSh : Slots Γ₂
insSh fzero        = shared (ofᵉ (nat̂ 0 ∷ [])) {ok = tt}
insSh (fsuc fzero) = scripted (hot [])

liftS : Fn Γ₂ [] [] [] natᵗ (obs natᵗ)
liftS = strmᵗ (ofᵉ (varᵗ (here refl) ∷ []))

bSh : Closed Γ₂ (obs natᵗ)
bSh = mapᵉ liftS (input fzero)

rSh : Closed Γ₂ natᵗ
rSh = mergeAllᵉ nothing bSh

resSh : Stream Γ₂ (obs natᵗ) × Sched Γ₂ × EvalSt rSh
resSh =
  subscribeE gasBig bSh
    (thru-outer mergeAllᵒ (proj₁ (mintNode (sched-init rSh insSh))) ↠ root) 0 0
    (proj₂ (mintNode (sched-init rSh insSh)))
    (installNode (proj₁ (mintNode (sched-init rSh insSh)))
       (mergeAll-st {t = natᵗ} nothing 0 [] false)
       (st-init rSh))

-- LOAD-BEARING: two instants is the whole point of the row
lenSh≡ : length (proj₁ resSh) ≡ 2
lenSh≡ = refl

-- `tight` reads the module-level slot table, so the Sh row carries its
-- own cap at the same tightest recipe over `insSh`
tightSh : Caps
tightSh = caps (syncSizeᵛ (obs natᵗ) rSh) (pWᵛ 2 insSh (obs natᵗ) rSh) 0

capsSh : (W : ℕ) → Set
capsSh W =
  pushValsCapsOK tightSh 0 insSh W gasBig mergeAllᵒ
    (proj₁ (mintNode (sched-init rSh insSh))) root 0 0
    (proj₁ resSh) (proj₁ (proj₂ resSh)) (proj₂ (proj₂ resSh))

capsSh-2 : ∀ {W} → Widths W → capsSh W
capsSh-2 hw = refl , refl , refl , refl , refl , tt
        , 0 , (refl , refl , refl , refl , refl
          , ((le tt , hw _ _ _ _ _ _ _ _ _ , λ { cur od () }) , tt)
          , 0 , tt)

-- the same two-instant walk at the other two heads: the switch
-- subscribes and records the current inner, the exhaust subscribes
-- into an idle gate, and both second-instant bundles are read at the
-- state the head instant's step leaves, exactly as the merge's
qSh : Closed Γ₂ natᵗ
qSh = switchAllᵉ bSh

xSh : Closed Γ₂ natᵗ
xSh = exhaustAllᵉ bSh

tightShS : Caps
tightShS = caps (syncSizeᵛ (obs natᵗ) qSh) (pWᵛ 2 insSh (obs natᵗ) qSh) 0

tightShX : Caps
tightShX = caps (syncSizeᵛ (obs natᵗ) xSh) (pWᵛ 2 insSh (obs natᵗ) xSh) 0

resShS : Stream Γ₂ (obs natᵗ) × Sched Γ₂ × EvalSt qSh
resShS =
  subscribeE gasBig bSh
    (thru-outer switchᵒ (proj₁ (mintNode (sched-init qSh insSh))) ↠ root) 0 0
    (proj₂ (mintNode (sched-init qSh insSh)))
    (installNode (proj₁ (mintNode (sched-init qSh insSh)))
       (switch-st nothing false) (st-init qSh))

resShX : Stream Γ₂ (obs natᵗ) × Sched Γ₂ × EvalSt xSh
resShX =
  subscribeE gasBig bSh
    (thru-outer exhaustᵒ (proj₁ (mintNode (sched-init xSh insSh))) ↠ root) 0 0
    (proj₂ (mintNode (sched-init xSh insSh)))
    (installNode (proj₁ (mintNode (sched-init xSh insSh)))
       (exhaust-st false false) (st-init xSh))

lenShS≡ : length (proj₁ resShS) ≡ 2
lenShS≡ = refl

lenShX≡ : length (proj₁ resShX) ≡ 2
lenShX≡ = refl

capsShS : (W : ℕ) → Set
capsShS W =
  pushValsCapsOK tightShS 0 insSh W gasBig switchᵒ
    (proj₁ (mintNode (sched-init qSh insSh))) root 0 0
    (proj₁ resShS) (proj₁ (proj₂ resShS)) (proj₂ (proj₂ resShS))

capsShS-2 : ∀ {W} → Widths W → capsShS W
capsShS-2 hw = refl , refl , refl , refl , refl , tt
        , 0 , (refl , refl , refl , refl , refl
          , ((le tt , hw _ _ _ _ _ _ _ _ _ , λ { cur od refl → hw _ _ _ _ _ _ _ _ _ }) , tt)
          , 0 , tt)

capsShX : (W : ℕ) → Set
capsShX W =
  pushValsCapsOK tightShX 0 insSh W gasBig exhaustᵒ
    (proj₁ (mintNode (sched-init xSh insSh))) root 0 0
    (proj₁ resShX) (proj₁ (proj₂ resShX)) (proj₂ (proj₂ resShX))

capsShX-2 : ∀ {W} → Widths W → capsShX W
capsShX-2 hw = refl , refl , refl , refl , refl , tt
        , 0 , (refl , refl , refl , refl , refl
          , ((le tt , hw _ _ _ _ _ _ _ _ _ , λ { cur od () }) , tt)
          , 0 , tt)

slotsA : ℕ → Slots Γ₂
slotsA j = insT 0 0 j

lift1 : Fn Γ₂ [] [] [] natᵗ (obs (obs natᵗ))
lift1 = strmᵗ (ofᵉ (strmᵗ (ofᵉ (varᵗ (here refl) ∷ [])) ∷ []))

asyncBody : Closed Γ₂ (obs (obs natᵗ))
asyncBody = mapᵉ lift1 (input (fsuc fzero))

gateBody : Closed Γ₂ (obs (obs natᵗ))
gateBody = mergeAllᵉ nothing
  (ofᵉ (strmᵗ (ofᵉ (strmᵗ (ofᵉ (strmᵗ (deepV 1) ∷ [])) ∷ [])) ∷
        strmᵗ (deferᵉ (ofᵉ (strmᵗ (ofᵉ (strmᵗ (deepV 1) ∷ [])) ∷ []))) ∷ []))

rG : ℕ → Closed Γ₂ (obs natᵗ)
rG lim = mergeAllᵉ (just lim) gateBody

resG : (lim : ℕ) → Stream Γ₂ (obs (obs natᵗ)) × Sched Γ₂ × EvalSt (rG lim)
resG lim =
  subscribeE gasBig gateBody
    (thru-outer mergeAllᵒ (proj₁ (mintNode (sched-init (rG lim) slots))) ↠ root) 0 0
    (proj₂ (mintNode (sched-init (rG lim) slots)))
    (installNode (proj₁ (mintNode (sched-init (rG lim) slots)))
       (mergeAll-st {t = obs natᵗ} (just lim) 0 [] false)
       (st-init (rG lim)))

rA : ℕ → Closed Γ₂ (obs natᵗ)
rA lim = mergeAllᵉ (just lim) asyncBody

resA : (j lim : ℕ) → Stream Γ₂ (obs (obs natᵗ)) × Sched Γ₂ × EvalSt (rA lim)
resA j lim =
  subscribeE gasBig asyncBody
    (thru-outer mergeAllᵒ (proj₁ (mintNode (sched-init (rA lim) (slotsA j)))) ↠ root) 0 0
    (proj₂ (mintNode (sched-init (rA lim) (slotsA j))))
    (installNode (proj₁ (mintNode (sched-init (rA lim) (slotsA j))))
       (mergeAll-st {t = obs natᵗ} (just lim) 0 [] false)
       (st-init (rA lim)))

burstOne : ℕ × ℕ × ℕ × ℕ
burstOne = length (proj₁ (resG 1))
         , length (proj₁ (resA 1 1)) , length (proj₁ (resA 2 1)) , length (proj₁ (resA 3 1))

burstOne≡ : burstOne ≡ (1 , 1 , 1 , 1)
burstOne≡ = refl

-- AND THE SAME PROGRAMS AT THE TWO LEAVES THE ROOM WALK NOW STANDS
-- ON.  The bundle rows above build the room record whole; these build
-- its inputs apart, in the shapes the burst leaves state -- the
-- arrivals' width key and the frame widths -- so the rows are evidence
-- about those statements and not only about the record they compose
-- into.  The width key is the one of the two that is NEW here rather
-- than a re-cut of a conjunct the bundle rows already carried: it is a
-- `refl` on a boolean, so unlike its sibling it could have failed on
-- its own.
Leaves : ∀ {t u} {e : Closed Γ₂ t} (c : Caps) (sl : Slots Γ₂) (W : ℕ)
  (op : AllOp) (nid : NodeId) (κ : Path Γ₂ u t)
  (r : Stream Γ₂ (obs u) × Sched Γ₂ × EvalSt e) → Set
Leaves c sl W op nid κ r =
  pushValsWidOK c sl (proj₁ r)
  × pushValsWOK W gasBig op nid κ 0 0 (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

leavesM-1 : ∀ {W} → Widths W →
  Leaves (tight {obs (obs natᵗ)} (rM 1 1)) slots W mergeAllᵒ
    (proj₁ (mintNode (sched-init (rM 1 1) slots))) root (resM 1 1)
leavesM-1 hw =
  (refl , tt)
  , (((hw _ _ _ _ _ _ _ _ _ , λ { cur od () })
     , (hw _ _ _ _ _ _ _ _ _ , λ { cur od () }) , tt) , tt)

leavesM-2 : ∀ {W} → Widths W →
  Leaves (tight {obs (obs natᵗ)} (rM 1 2)) slots W mergeAllᵒ
    (proj₁ (mintNode (sched-init (rM 1 2) slots))) root (resM 1 2)
leavesM-2 hw =
  (refl , tt)
  , (((hw _ _ _ _ _ _ _ _ _ , λ { cur od () })
     , (hw _ _ _ _ _ _ _ _ _ , λ { cur od () }) , tt) , tt)

leavesM-0 : ∀ {W} → Widths W →
  Leaves (tight {obs (obs natᵗ)} (rM 0 1)) slots W mergeAllᵒ
    (proj₁ (mintNode (sched-init (rM 0 1) slots))) root (resM 0 1)
leavesM-0 hw =
  (refl , tt)
  , (((hw _ _ _ _ _ _ _ _ _ , λ { cur od () })
     , (hw _ _ _ _ _ _ _ _ _ , λ { cur od () }) , tt) , tt)

leavesS-1 : ∀ {W} → Widths W →
  Leaves (tight {obs (obs natᵗ)} (qS 1)) slots W switchᵒ
    (proj₁ (mintNode (sched-init (qS 1) slots))) root (resS 1)
leavesS-1 hw =
  (refl , tt)
  , (((hw _ _ _ _ _ _ _ _ _ , λ { cur od refl → hw _ _ _ _ _ _ _ _ _ })
     , (hw _ _ _ _ _ _ _ _ _ , λ { cur od refl → hw _ _ _ _ _ _ _ _ _ }) , tt) , tt)

leavesS-2 : ∀ {W} → Widths W →
  Leaves (tight {obs (obs natᵗ)} (qS 2)) slots W switchᵒ
    (proj₁ (mintNode (sched-init (qS 2) slots))) root (resS 2)
leavesS-2 hw =
  (refl , tt)
  , (((hw _ _ _ _ _ _ _ _ _ , λ { cur od refl → hw _ _ _ _ _ _ _ _ _ })
     , (hw _ _ _ _ _ _ _ _ _ , λ { cur od refl → hw _ _ _ _ _ _ _ _ _ }) , tt) , tt)

leavesX-1 : ∀ {W} → Widths W →
  Leaves (tight {obs (obs natᵗ)} (qX 1)) slots W exhaustᵒ
    (proj₁ (mintNode (sched-init (qX 1) slots))) root (resX 1)
leavesX-1 hw =
  (refl , tt)
  , (((hw _ _ _ _ _ _ _ _ _ , λ { cur od () })
     , (hw _ _ _ _ _ _ _ _ _ , λ { cur od () }) , tt) , tt)

leavesX-2 : ∀ {W} → Widths W →
  Leaves (tight {obs (obs natᵗ)} (qX 2)) slots W exhaustᵒ
    (proj₁ (mintNode (sched-init (qX 2) slots))) root (resX 2)
leavesX-2 hw =
  (refl , tt)
  , (((hw _ _ _ _ _ _ _ _ _ , λ { cur od () })
     , (hw _ _ _ _ _ _ _ _ _ , λ { cur od () }) , tt) , tt)

-- and the two-instant walk, where the leaves are read at the state the
-- head instant's step leaves exactly as the bundle rows read theirs
leavesSh : ∀ {W} → Widths W →
  Leaves tightSh insSh W mergeAllᵒ
    (proj₁ (mintNode (sched-init rSh insSh))) root resSh
leavesSh hw =
  (refl , refl , tt)
  , (tt , ((hw _ _ _ _ _ _ _ _ _ , λ { cur od () }) , tt) , tt)

leavesShS : ∀ {W} → Widths W →
  Leaves tightShS insSh W switchᵒ
    (proj₁ (mintNode (sched-init qSh insSh))) root resShS
leavesShS hw =
  (refl , refl , tt)
  , (tt , ((hw _ _ _ _ _ _ _ _ _
           , λ { cur od refl → hw _ _ _ _ _ _ _ _ _ }) , tt) , tt)

leavesShX : ∀ {W} → Widths W →
  Leaves tightShX insSh W exhaustᵒ
    (proj₁ (mintNode (sched-init xSh insSh))) root resShX
leavesShX hw =
  (refl , refl , tt)
  , (tt , ((hw _ _ _ _ _ _ _ _ _ , λ { cur od () }) , tt) , tt)

-- THE SUBSTITUTION'S TWO AXES READ APART, at the very program that
-- refutes the pair.  `Refuted.PushVals-Adm-Map` sets the width and
-- registry fields WIDE on purpose, so that nothing but the size half
-- can be doing the work -- which leaves open the question a split
-- design turns on: does the arrival's PENDING WIDTH stay inside the
-- head's own width, while only its SIZE crosses?  These rows put the
-- same dup-map program under a cap tight on BOTH fields and report
-- the two readings side by side.  LOAD-BEARING on the width axis, and
-- it is the axis that could have gone either way: the size crossing
-- is already known.
--
-- IT DOES NOT MOVE.  Over a flat payload the head reads (21, 16) and
-- the arrival (25, 16); over a payload that is itself pending, (22, 2)
-- against (27, 2).  The step function names its payload twice in both,
-- so the doubling is there in the size and simply absent from the
-- width -- a duplicated reference is a second mention of the SAME
-- pending observable, and the frame measure counts observables and not
-- mentions.  So the crossing is confined to the one axis a stepped cap
-- prices, and the invariant that reads the node table's widths has no
-- reason to leave the entry cap.
dupFn : Fn Γ₂ [] [] [] (obs natᵗ) (obs natᵗ)
dupFn = strmᵗ (mergeAllᵉ nothing
                 (ofᵉ (varᵗ (here refl) ∷ varᵗ (here refl) ∷ [])))

flatV : Val Γ₂ (obs natᵗ)
flatV = ofᵉ (nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷
             nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ [])

-- and the same shape over a payload that is itself PENDING, so the
-- width axis has something to double
nestV : Val Γ₂ (obs natᵗ)
nestV = deepV 2

dupBody : Val Γ₂ (obs natᵗ) → Closed Γ₂ (obs natᵗ)
dupBody v = mapᵉ dupFn (ofᵉ (strmᵗ v ∷ []))

dupHead : Val Γ₂ (obs natᵗ) → Closed Γ₂ natᵗ
dupHead v = mergeAllᵉ nothing (dupBody v)

resD : (v : Val Γ₂ (obs natᵗ)) →
  Stream Γ₂ (obs natᵗ) × Sched Γ₂ × EvalSt (dupHead v)
resD v =
  subscribeE gasBig (dupBody v)
    (thru-outer mergeAllᵒ (proj₁ (mintNode (sched-init (dupHead v) slots))) ↠ root) 0 0
    (proj₂ (mintNode (sched-init (dupHead v) slots)))
    (installNode (proj₁ (mintNode (sched-init (dupHead v) slots)))
       (mergeAll-st {t = natᵗ} nothing 0 [] false)
       (st-init (dupHead v)))

vals : Stream Γ₂ (obs natᵗ) → List (Val Γ₂ (obs natᵗ))
vals [] = []
vals (em ∷ ems) =
  proj₁ (splitEvents {A = Val Γ₂ natᵗ} (InstEmit.events em)) ++ vals ems

-- the head's own two readings, then the arrivals' -- LOAD-BEARING on
-- the width axis, which is the one that could have gone either way
axesFlat : (ℕ × ℕ) × List ℕ × List ℕ
axesFlat =
  (syncSizeᵛ (obs natᵗ) (dupHead flatV) , pWᵛ 2 slots (obs natᵗ) (dupHead flatV))
  , map (syncSizeᵛ (obs natᵗ)) (vals (proj₁ (resD flatV)))
  , map (pWᵛ 2 slots (obs natᵗ)) (vals (proj₁ (resD flatV)))

axesNest : (ℕ × ℕ) × List ℕ × List ℕ
axesNest =
  (syncSizeᵛ (obs natᵗ) (dupHead nestV) , pWᵛ 2 slots (obs natᵗ) (dupHead nestV))
  , map (syncSizeᵛ (obs natᵗ)) (vals (proj₁ (resD nestV)))
  , map (pWᵛ 2 slots (obs natᵗ)) (vals (proj₁ (resD nestV)))

axesFlat≡ : axesFlat ≡ ((21 , 16) , 25 ∷ [] , 16 ∷ [])
axesFlat≡ = refl

axesNest≡ : axesNest ≡ ((22 , 2) , 27 ∷ [] , 2 ∷ [])
axesNest≡ = refl

-- THE TWO BURST PREDICATES THE ADMISSION AND WIDTH LEAVES NOW STATE,
-- read at the same three heads and at the same arrival cap the bundle
-- rows use.  These are the rows that carry those two targets: the
-- per-emit records above are now DERIVED from these booleans, so a row
-- on a record is a consequence and not evidence about the leaf.  Both
-- are LOAD-BEARING and could have failed independently -- the width
-- boolean reads the arrival's frame width against the cap, and the
-- admission boolean reads its resolved CLOSURE, which the head's own
-- `nestClosOK?` says nothing about once a payload has been substituted.
capAt : ∀ {u} → Val Γ₂ u → Caps
capAt {u} v = arrCapAt (Caps.cSize (tight {u} v)) (tight {u} v)

burstsM burstsS burstsX : Bool × Bool
burstsM = burstCaps? (capAt {obs (obs natᵗ)} (rM 1 1)) slots (proj₁ (resM 1 1))
        , burstNest? (capAt {obs (obs natᵗ)} (rM 1 1)) slots (proj₁ (resM 1 1))
burstsS = burstCaps? (capAt {obs (obs natᵗ)} (qS 1)) slots (proj₁ (resS 1))
        , burstNest? (capAt {obs (obs natᵗ)} (qS 1)) slots (proj₁ (resS 1))
burstsX = burstCaps? (capAt {obs (obs natᵗ)} (qX 1)) slots (proj₁ (resX 1))
        , burstNest? (capAt {obs (obs natᵗ)} (qX 1)) slots (proj₁ (resX 1))

burstsM≡ : burstsM ≡ (true , true)
burstsM≡ = refl

burstsS≡ : burstsS ≡ (true , true)
burstsS≡ = refl

burstsX≡ : burstsX ≡ (true , true)
burstsX≡ = refl

-- and the two-instant walk, where the second instant's arrivals are
-- the ones no single-instant row reaches
burstsSh burstsShS burstsShX : Bool × Bool
burstsSh  = burstCaps? (arrCapAt (Caps.cSize tightSh) tightSh) insSh (proj₁ resSh)
          , burstNest? (arrCapAt (Caps.cSize tightSh) tightSh) insSh (proj₁ resSh)
burstsShS = burstCaps? (arrCapAt (Caps.cSize tightShS) tightShS) insSh (proj₁ resShS)
          , burstNest? (arrCapAt (Caps.cSize tightShS) tightShS) insSh (proj₁ resShS)
burstsShX = burstCaps? (arrCapAt (Caps.cSize tightShX) tightShX) insSh (proj₁ resShX)
          , burstNest? (arrCapAt (Caps.cSize tightShX) tightShX) insSh (proj₁ resShX)

burstsSh≡ : burstsSh ≡ (true , true)
burstsSh≡ = refl

burstsShS≡ : burstsShS ≡ (true , true)
burstsShS≡ = refl

burstsShX≡ : burstsShX ≡ (true , true)
burstsShX≡ = refl

-- AND THE TWO BOOLEANS AT THE DEFER AND THE SCRIPTED SLOT, which is
-- where the two refutations of this face's state predicate live: a
-- defer parks its body at FULL syntax size and FULL delivered width
-- while every premise here reads the defer as 1, and a scripted slot
-- delivers on a later tick.  The arrival cap steps the SIZE axis only,
-- so if the parked body ever arrives its WIDTH is priced at the entry
-- field and the width half has nowhere to move.  LOAD-BEARING on both
-- axes, and the whole reason for the rows: every other program here
-- reaches the leaf through a synchronous source.
tightG : (lim : ℕ) → Caps
tightG lim = tight {obs (obs natᵗ)} (rG lim)

tightA : (lim : ℕ) → Caps
tightA lim = tight {obs (obs natᵗ)} (rA lim)

burstsG : Bool × Bool
burstsG = burstCaps? (arrCapAt (Caps.cSize (tightG 1)) (tightG 1)) slots (proj₁ (resG 1))
        , burstNest? (arrCapAt (Caps.cSize (tightG 1)) (tightG 1)) slots (proj₁ (resG 1))

burstsG≡ : burstsG ≡ (true , true)
burstsG≡ = refl

burstsA : Bool × Bool
burstsA = burstCaps? (arrCapAt (Caps.cSize (tightA 1)) (tightA 1)) (slotsA 1) (proj₁ (resA 1 1))
        , burstNest? (arrCapAt (Caps.cSize (tightA 1)) (tightA 1)) (slotsA 1) (proj₁ (resA 1 1))

burstsA≡ : burstsA ≡ (true , true)
burstsA≡ = refl
