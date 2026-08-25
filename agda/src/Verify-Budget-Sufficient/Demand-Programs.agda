-- THE DEMAND PROGRAM FAMILIES — Q and S.  One home, and today one
-- consumer.  Q is below; S is at the foot of the file, and its own
-- section says what it reaches that Q cannot.
--
-- Q varies a scan fold's wrap DEPTH d and its source list LENGTH k
-- independently, which is what makes it the only probe family that can
-- see the walk face's live edge: the demand hypothesis supplies a SUM
-- (`sucG`, a static syntactic size) while gas demand tracks the
-- within-instant nesting depth, a PRODUCT d·k.  A sum cannot dominate a
-- product forever.
--
-- WHY IT IS A MODULE OF ITS OWN, and why that survives the probe that
-- used to share it.  The crossing region is unreachable in the
-- TYPECHECKER — `runDry` gives no
-- short-circuit in either direction (`hasDry` reads the stream
-- `subscribeE` returns, so the whole run normalises before the first dry
-- event is visible), and the cost is quadratic in k: a run normalises
-- d·k(k+1)/2 subscription levels, ~250 at the cheapest crossing point,
-- where (8,8) burned 56 min CPU without finishing.  Only the COMPILED
-- harness reaches it.  The type-level half of that pair — a probe that
-- pinned what the checker COULD reach — has since expired with its
-- targets and been deleted, so `Harness.Main` is the sole consumer; see
-- the RECOVERY pointer in `.Burst-Walk` for what those rows measured.
--
-- IMPORTS ONLY `Rx.*`, deliberately, and that is why the deletion cost
-- nothing here: `Harness.Main` is a cheap calculator, and a family that
-- reached up into the Verify tower would drag the whole thing into
-- `make harness-build`.
module Verify-Budget-Sufficient.Demand-Programs where

open import Data.List using (List; []; _∷_; replicate; _++_)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Bool using (T; true)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Unit using (tt)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (refl; _≡_; sym; subst)

open import Rx.Prim using (Timed; after_,_; cold; hot)
open import Rx.Exp using (Ctx; Closed; Ty; natᵗ; obs; _×ᵗ_; ofᵉ; mergeAllᵉ; scanᵉ; strmᵗ; fstᵗ; varᵗ; nat̂; takeᵉ; syncSizeᵉ; Tm;
  Fn; input; inputsBelowᵉ; inputsBelowᵗ; inputsBelowᵗˢ)
open import Rx.Evaluator using (root; Path; _↠_; thru-outer; mergeAllᵒ)
open import Rx.Slots using (Slots; shared; scripted)
open import Rx.Hop-Depth using (hopDᵉ)
open import Rx.Slot-Hop using (slotHop)

----------------------------------------------------------------------
-- Context and slots: empty (no inputs)
----------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ⱽ

ins₀ : Slots Γ₀
ins₀ = λ ()

----------------------------------------------------------------------
-- THE RUNNERS.  `subscribeE` at the ENTRY — root path, tick 0, and the
-- evaluator's OWN initial schedule and state, so these are states the
-- evaluator reaches by running rather than states built by hand.
----------------------------------------------------------------------
wrapD : ∀ {n} {Γ : Ctx n} {Θ} → ℕ →
  Tm Γ [] [] Θ (obs natᵗ) → Tm Γ [] [] Θ (obs natᵗ)
wrapD 0       t = t
wrapD (suc d) t = strmᵗ (mergeAllᵉ nothing (ofᵉ (wrapD d t ∷ [])))

-- the fold that wraps the accumulator d levels per value
foldD : ∀ {n} {Γ : Ctx n} → ℕ → Fn Γ [] [] [] ((obs natᵗ) ×ᵗ natᵗ) (obs natᵗ)
foldD d = wrapD d (fstᵗ (varᵗ (here refl)))

natsD : ∀ {n} {Γ : Ctx n} → ℕ → List (Tm Γ [] [] [] natᵗ)
natsD 0       = []
natsD (suc k) = nat̂ k ∷ natsD k

progD : ∀ {n} {Γ : Ctx n} → ℕ → ℕ → Closed Γ natᵗ
progD d k =
  mergeAllᵉ nothing (scanᵉ (foldD d) (strmᵗ (ofᵉ (nat̂ 0 ∷ []))) (ofᵉ (natsD k)))

-- THE GAS THE FACE'S DEMAND HYPOTHESIS SUPPLIES at the adversarial
-- (smallest) instantiation Ŝ := R̂ := F := 0 and U := 0, where dBound
-- degenerates to `syncSizeᵉ b + hopDᵉ 0 b` and `hasAtLeast-pad` makes
-- `gasPad (suc G) g0 hasAtLeast suc G` hold EXACTLY, nothing spare.
-- So `runDry (sucG p) p ≡ true` REFUTES WalkStmt at p.
sucG : Closed Γ₀ natᵗ → ℕ
sucG b = suc (syncSizeᵉ b + hopDᵉ 0 (slotHop 0 ins₀) b)

----------------------------------------------------------------------
-- THE SHARED-SLOT FAMILY.  Series Q's slots are EMPTY, so `slotNest`
-- is zero on every slot and the shared arm of the store's nesting
-- measure is never entered — while the witness that machine-refuted
-- the count-parametric currency came through exactly that arm.  S
-- reaches it: one slot, whose def is a scan under a `mergeAllᵉ`, and a
-- root that both references the slot and carries its own d and k.
----------------------------------------------------------------------
wrapD-below : ∀ {n} {Γ : Ctx n} {Θ} (j d : ℕ)
  (t : Tm Γ [] [] Θ (obs natᵗ)) →
  inputsBelowᵗ j t ≡ true → inputsBelowᵗ j (wrapD d t) ≡ true
wrapD-below j 0       t h = h
wrapD-below j (suc d) t h rewrite wrapD-below j d t h = refl

natsD-below : ∀ {n} {Γ : Ctx n} (j k : ℕ) →
  inputsBelowᵗˢ j (natsD {Γ = Γ} k) ≡ true
natsD-below j 0       = refl
natsD-below j (suc k) = natsD-below j k

progD-below : ∀ {n} {Γ : Ctx n} (j d k : ℕ) →
  inputsBelowᵉ j (progD {Γ = Γ} d k) ≡ true
progD-below {Γ = Γ} j d k
  rewrite wrapD-below {Γ = Γ} {Θ = ((obs natᵗ) ×ᵗ natᵗ) ∷ []} j d
            (fstᵗ (varᵗ (here refl))) refl =
  natsD-below {Γ = Γ} j k
Γ₂ : Ctx 2
Γ₂ = natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

-- j values, each one tick after the last
asyncNats : ℕ → List (Timed ℕ)
asyncNats 0       = []
asyncNats (suc j) = (after 0 , j) ∷ asyncNats j

insT : ℕ → ℕ → ℕ → Slots Γ₂
insT ds ks j fzero =
  shared (progD ds ks) {ok = subst T (sym (progD-below 0 ds ks)) tt}
insT ds ks j (fsuc fzero) = scripted (cold [] (asyncNats j))

progT : ℕ → ℕ → Closed Γ₂ natᵗ
progT d k =
  mergeAllᵉ nothing (scanᵉ (foldD d) (strmᵗ (ofᵉ (nat̂ 0 ∷ [])))
    (mergeAllᵉ nothing (ofᵉ (strmᵗ (input fzero)
                   ∷ strmᵗ (input (fsuc fzero))
                   ∷ strmᵗ (ofᵉ (natsD k)) ∷ []))))

sucGT : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
sucGT ds ks j d k =
  suc (syncSizeᵉ (progT d k)
       + hopDᵉ 0 (slotHop 0 (insT ds ks j)) (progT d k))

-- THE OUTER-BOUNDED FAMILY, which is `progT` with the bound moved to the
-- OUTER `*All` instead of the inner one.  Every other family here leaves
-- the outer unbounded, so every value the scan emits is subscribed on the
-- spot; here the outer fills after one and a later emission PARKS.  It
-- was built to separate two things the others always do together --
-- deepening the scan's accumulator, and minting a node instance for what
-- it emitted -- and it DOES NOT separate them: the inner flattener still
-- mints once per release, so a walk that deepens the store still mints.
-- Kept because the outer-bounded shape is the axis any further attempt on
-- that region has to drive, and because arriving at it again from nothing
-- is most of the cost.
progO : ℕ → ℕ → Closed Γ₂ natᵗ
progO d k =
  mergeAllᵉ (just 1) (scanᵉ (foldD d) (strmᵗ (ofᵉ (nat̂ 0 ∷ [])))
    (mergeAllᵉ nothing (ofᵉ (strmᵗ (input fzero)
                   ∷ strmᵗ (input (fsuc fzero))
                   ∷ strmᵗ (ofᵉ (natsD k)) ∷ []))))

sucGO : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
sucGO ds ks j d k =
  suc (syncSizeᵉ (progO d k)
       + hopDᵉ 0 (slotHop 0 (insT ds ks j)) (progO d k))

----------------------------------------------------------------------
-- THE LATE-CONNECT FAMILY.  Every other family here connects its shared
-- slot inside the ROOT SUBSCRIBE, so from the first delivery instant
-- onward the slot is spent and a re-descent of the subject reads the
-- same slot state forever.  A depth measure is state-sensitive only
-- through that read, so those families cannot move it along a run and a
-- row walked over them is degenerate on the state axis whatever it
-- reports.  U puts the shared input BEHIND a capacity-one mergeAll, whose inner
-- subscribes are deferred to arrivals: the scripted slot drains first,
-- its completion performs the connect mid-run, and the descent's value
-- before and after that instant is a genuine question.
----------------------------------------------------------------------

-- THE FAN FAMILY.  Every other family here registers each input once,
-- so one arrival drives one chain and a cascade's delivery count is
-- pinned at one — a count that cannot vary is not evidence about a
-- bound on counts, whatever the bound.  This one subscribes the SAME
-- ASYNC input `suc w` times, so the arriving slot has `suc w` registered
-- chains and the cascade delivers once per chain.  That is what makes
-- the count a free variable, and it is the only reason the family
-- exists.
-- and the slots it runs against: slot 1 HOT rather than cold, which is
-- the whole point.  A cold source is re-created per subscription, so
-- fanning one out buys separate arrival INSTANTS each carrying a single
-- chain — the count stays pinned and nothing is learned.  A hot source
-- is subscribed once and shared, so the `suc w` references land as
-- `suc w` chains on ONE arrival, which is the configuration a
-- multi-delivery cascade needs.
insF : ℕ → ℕ → ℕ → Slots Γ₂
insF ds ks j fzero =
  shared (progD ds ks) {ok = subst T (sym (progD-below 0 ds ks)) tt}
insF ds ks j (fsuc fzero) = scripted (hot (asyncNats j))

progF : ℕ → ℕ → Closed Γ₂ natᵗ
progF w k =
  mergeAllᵉ nothing (scanᵉ (foldD 1) (strmᵗ (ofᵉ (nat̂ 0 ∷ [])))
    (mergeAllᵉ nothing (ofᵉ (replicate (suc w) (strmᵗ (input (fsuc fzero)))
                     ++ (strmᵗ (input fzero) ∷ strmᵗ (ofᵉ (natsD k)) ∷ [])))))

sucGF : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
sucGF ds ks j w k =
  suc (syncSizeᵉ (progF w k)
       + hopDᵉ 0 (slotHop 0 (insF ds ks j)) (progF w k))

----------------------------------------------------------------------
-- THE CUT FAMILY.  The fan of `progF`, with a `takeᵉ 1` between the fan
-- and the root, and it exists for one reason: it is the only shape that
-- reaches `cascadeGo`'s SKIP branch.  `cascadeLatch` clears `cancelled`
-- at every cascade's entry, so a chain can only be skipped because an
-- operator CUT it during this same cascade -- and both cut sites sit
-- inside a dispatch, which runs only after the cutting chain's own
-- delivery.  So a skip is always preceded by a delivery, and a family
-- wanting skips must buy them with a take that exhausts mid-fan.
--
-- WHY THE FAN MUST BE WIDE.  Two chains put the cut on the last one and
-- leave nothing behind it, which is the degenerate case: what the skip
-- branch charges and cannot pay for is the phantom TAIL cascade after
-- the skipped chain, so the rows need at least a third chain sitting
-- past the cut.
--
-- AND THE TAKE COUNT IS THE SWEPT PARAMETER, not a constant.  A take
-- tight enough to be interesting exhausts inside the SUBSCRIBE frame,
-- on the synchronous emissions the shared slot and the seed make, and
-- then it has cut the whole registry before any arrival exists -- the
-- rows come back with no chains at all.  What is wanted is a count that
-- survives the frame and runs out partway along one arrival's fan, and
-- where that sits is a property of the program rather than something to
-- guess, so `k` IS the count and the sweep finds it.
-- AND THE FOLD DEPTH IS SWEPT TOO, because it is the axis the skip
-- branch is actually at risk on.  `foldD dd` wraps the scan's
-- accumulator `dd` levels deeper per value, so a chainStep DEEPENS THE
-- STORE -- and in the skip branch the evaluator runs no such step while
-- `depthCascade` charges one anyway, plus every phantom step stacked
-- behind it.  At depth one the charge is invisible under the base
-- terms; the question is whether it stays so as the per-value wrap
-- grows against a delivery count that does not.
--
-- AND THE TAKE SITS BELOW THE SCAN, WHICH IS THE WHOLE POINT OF THE
-- ORDER.  Above it, an exhausted take gates the scan: the phantom step
-- carries no value through, the accumulator never wraps, and the rows
-- come back flat in the fan width however deep the fold -- measured,
-- and it is what a first arrangement of this family did.  Below it, a
-- skipped chain still runs the mergeAll and the scan before meeting the
-- exhausted take, so each phantom step deepens the store and the
-- charges stack behind the cut with no delivery paying for them.
progC : ℕ → ℕ → ℕ → Closed Γ₂ natᵗ
progC dd w k =
  mergeAllᵉ nothing (takeᵉ (nat̂ (suc k))
    (scanᵉ (foldD dd) (strmᵗ (ofᵉ (nat̂ 0 ∷ [])))
      (mergeAllᵉ nothing (ofᵉ (replicate (suc w) (strmᵗ (input (fsuc fzero)))
                       ++ (strmᵗ (input fzero) ∷ []))))))

sucGC : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
sucGC ds ks j dd w k =
  suc (syncSizeᵉ (progC dd w k)
       + hopDᵉ 0 (slotHop 0 (insF ds ks j)) (progC dd w k))

-- ONE DELIVERY THAT SUBSCRIBES A WIDTH, which is the shape every other
-- family here misses.  `wrapD` merges a SINGLETON, so each accumulator
-- level costs one subscribe and a delivery never registers more than
-- one observable at a time -- and a bound charging one operator's worth
-- per delivery cannot be told apart from a bound charging a width on
-- programs like that.  `wrapW` merges the accumulator with itself `suc
-- w` times instead, so a single scan emission hands the outer *All a
-- width of inners to subscribe at one instant.
wrapW : ∀ {n} {Γ : Ctx n} {Θ} → ℕ →
  Tm Γ [] [] Θ (obs natᵗ) → Tm Γ [] [] Θ (obs natᵗ)
wrapW w t = strmᵗ (mergeAllᵉ nothing (ofᵉ (replicate (suc w) t)))

foldW : ∀ {n} {Γ : Ctx n} → ℕ → Fn Γ [] [] [] ((obs natᵗ) ×ᵗ natᵗ) (obs natᵗ)
foldW w = wrapW w (fstᵗ (varᵗ (here refl)))

progW : ℕ → ℕ → ℕ → Closed Γ₂ natᵗ
progW ww w k =
  mergeAllᵉ nothing (scanᵉ (foldW ww) (strmᵗ (ofᵉ (nat̂ 0 ∷ [])))
    (mergeAllᵉ nothing (ofᵉ (replicate (suc w) (strmᵗ (input (fsuc fzero)))
                     ++ (strmᵗ (input fzero) ∷ strmᵗ (ofᵉ (natsD k)) ∷ [])))))

sucGW : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
sucGW ds ks j ww w k =
  suc (syncSizeᵉ (progW ww w k)
       + hopDᵉ 0 (slotHop 0 (insF ds ks j)) (progW ww w k))

progU : ℕ → ℕ → Closed Γ₂ natᵗ
progU d k =
  mergeAllᵉ nothing (scanᵉ (foldD d) (strmᵗ (ofᵉ (nat̂ 0 ∷ [])))
    (mergeAllᵉ (just 1) (ofᵉ (strmᵗ (input (fsuc fzero))
                    ∷ strmᵗ (input fzero)
                    ∷ strmᵗ (ofᵉ (natsD k)) ∷ []))))

sucGU : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
sucGU ds ks j d k =
  suc (syncSizeᵉ (progU d k)
       + hopDᵉ 0 (slotHop 0 (insT ds ks j)) (progU d k))

-- THE BOUNDED-LIMIT FAMILY, which is `progU` with ONE axis moved and
-- everything else held: the inner mergeAll's limit is `suc lim` rather
-- than 1, over the same three inners.  At `lim = 0` it IS `progU`, so
-- the family contains its own control; at 1 one inner parks behind two
-- lanes and the drain must refill SEVERAL in an instant, which is the
-- only behaviour the two removed primitives could not express between
-- them and so the only region no probe of either face reached.  Holding
-- the fold depth and the source length fixed is the point: a crossing
-- that appears here and not at `lim = 0` is attributable to the gate.
progB : ℕ → ℕ → ℕ → Closed Γ₂ natᵗ
progB lim d k =
  mergeAllᵉ nothing (scanᵉ (foldD d) (strmᵗ (ofᵉ (nat̂ 0 ∷ [])))
    (mergeAllᵉ (just (suc lim)) (ofᵉ (strmᵗ (input (fsuc fzero))
                    ∷ strmᵗ (input fzero)
                    ∷ strmᵗ (ofᵉ (natsD k)) ∷ []))))

-- THE GATE IS ONLY A GATE WHEN THE SOURCE OUTRUNS IT.  `progB`'s source
-- carries exactly three inners, so a limit of three is already the
-- unbounded case and the family cannot reach a state where the drain
-- parks anything for more than one refill.  `progN` widens the source
-- alone, leaving every other axis where `progB` has it: at w inners and
-- limit l the drain must refill ⌈w/l⌉ times, which is the regime the
-- bounded argument is actually about.
progN : ℕ → ℕ → ℕ → ℕ → Closed Γ₂ natᵗ
progN lim w d k =
  mergeAllᵉ nothing (scanᵉ (foldD d) (strmᵗ (ofᵉ (nat̂ 0 ∷ [])))
    (mergeAllᵉ (just (suc lim))
      (ofᵉ (strmᵗ (input (fsuc fzero)) ∷ strmᵗ (input fzero)
            ∷ replicate (suc w) (strmᵗ (ofᵉ (natsD k)))))))

sucGN : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
sucGN ds ks j lim w d k =
  suc (syncSizeᵉ (progN lim w d k)
       + hopDᵉ 0 (slotHop 0 (insT ds ks j)) (progN lim w d k))

sucGB : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
sucGB ds ks j lim d k =
  suc (syncSizeᵉ (progB lim d k)
       + hopDᵉ 0 (slotHop 0 (insT ds ks j)) (progB lim d k))

----------------------------------------------------------------------
-- THE CLIMBED-PATH FAMILY.  A compositional depth bound is stated over
-- an arbitrary subject and an arbitrary rootward path, and the root
-- call fixes both at their smallest — subject the whole program, path
-- empty.  This varies them together: `thru-outer` is the one frame the
-- path measure charges, so a stack of j of them is a path of nesting j,
-- and the subject it demands is the program under j layers of `obs`.
-- The two must move together because the frame peels exactly one layer.
----------------------------------------------------------------------

obsN : ℕ → Ty
obsN 0       = natᵗ
obsN (suc j) = obs (obsN j)

pathN : ∀ {n} {Γ : Ctx n} (j : ℕ) → Path Γ (obsN j) natᵗ
pathN 0       = root
pathN (suc j) = thru-outer mergeAllᵒ 0 ↠ pathN j

-- THE SUBJECT MUST NEST ON ITS OWN, and two constructors in a row make
-- that easy to get wrong.  `ofᵉ` the measure sends to zero outright — a
-- one-shot list reaches no subscribe.  A scan over one is barely better:
-- the frame its burst passes is `scan-f`, which subscribes nothing, and
-- the `thru-outer` above the subject is charged by the CALLER rather
-- than by the subject's own descent.  Either way every row is
-- degenerate however deep the path is.  So the scan's source is the
-- program itself, whose `mergeAllᵉ` is what puts a level on.
subjN : ∀ {n} {Γ : Ctx n} (j d k : ℕ) → Closed Γ (obsN j)
subjN 0       d k = progD d k
subjN (suc j) d k =
  scanᵉ (fstᵗ (varᵗ (here refl))) (strmᵗ (subjN j d k)) (progD d k)
