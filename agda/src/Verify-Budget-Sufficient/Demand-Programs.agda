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
open import Data.Bool using (Bool; T; true)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Unit using (tt)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (refl; _≡_; sym; subst)

open import Rx.Prim using (g0; gasPad; Timed; after_,_; cold; hot)
open import Rx.Exp using (Ctx; Closed; Ty; natᵗ; obs; _×ᵗ_; ofᵉ; mergeAllᵉ; concatAllᵉ; scanᵉ; strmᵗ; fstᵗ; varᵗ; nat̂; syncSizeᵉ; Tm;
  Fn; input; inputsBelowᵉ; inputsBelowᵗ; inputsBelowᵗˢ)
open import Rx.Evaluator using (subscribeE; sched-init; st-init; hasDry; root;
  Path; _↠_; thru-outer; mergeᵒ)
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

runDry : ∀ {t} (h : ℕ) (e : Closed Γ₀ t) → Bool
runDry h e =
  hasDry (proj₁ (subscribeE (gasPad h g0) e root 0 0
                             (sched-init e ins₀) (st-init e)))

----------------------------------------------------------------------
-- THE FAMILY.  `progD d k` scans a k-element list with a fold that
-- wraps its accumulator d mergeAll-levels deeper per value, so accᵢ
-- carries d·i nested levels and the outer *All subscribes all of them.
----------------------------------------------------------------------

-- wrap a term d mergeAll-levels deeper
wrapD : ∀ {n} {Γ : Ctx n} {Θ} → ℕ →
  Tm Γ [] [] Θ (obs natᵗ) → Tm Γ [] [] Θ (obs natᵗ)
wrapD 0       t = t
wrapD (suc d) t = strmᵗ (mergeAllᵉ (ofᵉ (wrapD d t ∷ [])))

-- the fold that wraps the accumulator d levels per value
foldD : ∀ {n} {Γ : Ctx n} → ℕ → Fn Γ [] [] [] ((obs natᵗ) ×ᵗ natᵗ) (obs natᵗ)
foldD d = wrapD d (fstᵗ (varᵗ (here refl)))

natsD : ∀ {n} {Γ : Ctx n} → ℕ → List (Tm Γ [] [] [] natᵗ)
natsD 0       = []
natsD (suc k) = nat̂ k ∷ natsD k

progD : ∀ {n} {Γ : Ctx n} → ℕ → ℕ → Closed Γ natᵗ
progD d k =
  mergeAllᵉ (scanᵉ (foldD d) (strmᵗ (ofᵉ (nat̂ 0 ∷ []))) (ofᵉ (natsD k)))

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

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

-- STRATIFICATION HOLDS AT EVERY INDEX, INCLUDING ZERO, because the
-- family mentions no `input` at all — which is what lets slot 0 (whose
-- side condition admits nothing) hold a def of the family's full shape.
-- The three inductions are what make the def's d and k PARAMETERS: the
-- side condition is an implicit solved by unification, so without them
-- the sweep could only vary the def by literal dispatch.
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

insS : ℕ → ℕ → Slots Γ₁
insS ds ks fzero =
  shared (progD ds ks) {ok = subst T (sym (progD-below 0 ds ks)) tt}

-- the root: the same scan, over the slot's emissions MERGED with its
-- own k-element list, so d and k vary the root independently of the
-- def's ds and ks
progS : ℕ → ℕ → Closed Γ₁ natᵗ
progS d k =
  mergeAllᵉ (scanᵉ (foldD d) (strmᵗ (ofᵉ (nat̂ 0 ∷ [])))
    (mergeAllᵉ (ofᵉ (strmᵗ (input fzero) ∷ strmᵗ (ofᵉ (natsD k)) ∷ []))))

sucGS : ℕ → ℕ → ℕ → ℕ → ℕ
sucGS ds ks d k =
  suc (syncSizeᵉ (progS d k)
       + hopDᵉ 0 (slotHop 0 (insS ds ks)) (progS d k))

runDryS : ℕ → ℕ → ℕ → ℕ → Bool
runDryS ds ks d k =
  hasDry (proj₁ (subscribeE (gasPad (sucGS ds ks d k) g0) (progS d k) root 0 0
                            (sched-init (progS d k) (insS ds ks))
                            (st-init (progS d k))))

----------------------------------------------------------------------
-- THE ARRIVAL FAMILY.  Q and S are ALL-SYNCHRONOUS: every source is an
-- `ofᵉ` list, so the whole run happens in the subscribe burst and
-- `sched-next` reports an empty schedule immediately.  Neither family
-- can produce a cascade at all, which is what a delivery instant is.
-- T adds a scripted slot carrying async values, so the schedule is
-- non-empty when the burst hands over and the evaluator's own next
-- arrival is available to step.
----------------------------------------------------------------------

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
  mergeAllᵉ (scanᵉ (foldD d) (strmᵗ (ofᵉ (nat̂ 0 ∷ [])))
    (mergeAllᵉ (ofᵉ (strmᵗ (input fzero)
                   ∷ strmᵗ (input (fsuc fzero))
                   ∷ strmᵗ (ofᵉ (natsD k)) ∷ []))))

sucGT : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
sucGT ds ks j d k =
  suc (syncSizeᵉ (progT d k)
       + hopDᵉ 0 (slotHop 0 (insT ds ks j)) (progT d k))

----------------------------------------------------------------------
-- THE LATE-CONNECT FAMILY.  Every other family here connects its shared
-- slot inside the ROOT SUBSCRIBE, so from the first delivery instant
-- onward the slot is spent and a re-descent of the subject reads the
-- same slot state forever.  A depth measure is state-sensitive only
-- through that read, so those families cannot move it along a run and a
-- row walked over them is degenerate on the state axis whatever it
-- reports.  U puts the shared input BEHIND a concat, whose inner
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
  mergeAllᵉ (scanᵉ (foldD 1) (strmᵗ (ofᵉ (nat̂ 0 ∷ [])))
    (mergeAllᵉ (ofᵉ (replicate (suc w) (strmᵗ (input (fsuc fzero)))
                     ++ (strmᵗ (input fzero) ∷ strmᵗ (ofᵉ (natsD k)) ∷ [])))))

sucGF : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
sucGF ds ks j w k =
  suc (syncSizeᵉ (progF w k)
       + hopDᵉ 0 (slotHop 0 (insF ds ks j)) (progF w k))

progU : ℕ → ℕ → Closed Γ₂ natᵗ
progU d k =
  mergeAllᵉ (scanᵉ (foldD d) (strmᵗ (ofᵉ (nat̂ 0 ∷ [])))
    (concatAllᵉ (ofᵉ (strmᵗ (input (fsuc fzero))
                    ∷ strmᵗ (input fzero)
                    ∷ strmᵗ (ofᵉ (natsD k)) ∷ []))))

sucGU : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
sucGU ds ks j d k =
  suc (syncSizeᵉ (progU d k)
       + hopDᵉ 0 (slotHop 0 (insT ds ks j)) (progU d k))

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
pathN (suc j) = thru-outer mergeᵒ 0 ↠ pathN j

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
