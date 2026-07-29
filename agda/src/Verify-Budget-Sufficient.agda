-- THE PROOF (in progress) of budget sufficiency: the seeded sync
-- budget never runs dry on a canonical run — the old TERMINATING
-- pragma's claim, decomposed.
--
-- Architecture: an instant-indexed size invariant.  The only things
-- that grow across a run are the runtime values stored in the
-- machine (schedule pendings, scan accumulators, concat queues);
-- everything else is fixed program syntax.  Both fuel demand and
-- stored-value sizes TOWER (chained obs-typed scans exponentiate at
-- each story — the 2026-07-19 attack, see syncBudget's comment in
-- Rx.Evaluator), so the Gas budget is a tower and sizeBudgetAt is
-- its ℕ shadow for the ≤ᵇ-decidable store invariant.
--
--   stBounded? B          — every stored value's size ≤ B (decidable)
--   INV at instant id     — stBounded? (sizeBudgetAt … id)
--   subscribeE-wet        — THE WET CONTRACT (stated; the induction)
--   cascadeGo-wet         — the chain fold stays wet, lands bounded
--   burst-wet (PROVEN)    — the contract at the root + seed-covers
--   cascade-dry (PROVEN)  — latch + fold core + finish, composed
--   drain-dry (PROVEN)    — the fuel loop composes cascades
--   budget-sufficient     — (PROVEN from the above) the whole run
--
-- PROVEN: pop-slots/pop-bounded (inverting schedGo, hoisted for
-- exactly this), the cascade's structural ring (latch/sweep/finish/
-- mono), sync-linearity (plugs-len/occs/inner-len-subΘ), the seed
-- inequality (prod≤3pow/seed-covers — the tower dominance
-- arithmetic at instant 0, discharging the burst cores from the
-- contract), cascade-dry, drain-dry, and the theorem.
--
-- AND THE HOP MEASURE, in full (2026-07-27..29).  dBound's `r` is
-- hopD, a remaining-hop count; the emitted-value invariant the *All
-- clause consumes — every value a burst carries is no deeper than what
-- was subscribed — is proven end to end, with no postulate in its
-- chain: pm-subΘ, hopD-subΘᵉ/ᵗ/ᵗˢ (hopD is AFFINE in a substituted
-- value's depth), hopD-evalWith, hopD-applyFn, hopD-map-emit.  Getting
-- the measure's coefficient right took three machine-checked
-- refutations; see the hop-descent memo below and
-- agda/probe/Hop-Descent-Probe.agda.
--
-- READ THIS FIRST (2026-07-29).  subscribeE-walk has been refuted
-- TWICE in one day, and the second refutation is the live one.
--
--   walk-hyps-absurd    the 2026-07-24 face was VACUOUS: one V served
--                       as both the demand anchor and the store
--                       ceiling, and those two roles contradict.
--   hop-anchor-absurd   the anchor split (demand at the call's own
--                       entry bound capᴱ W E) removes the vacuity but
--                       does NOT close the hop edge: a call and its
--                       hop child then sit at DIFFERENT anchors, the
--                       child's anchor exceeds the parent's d, and the
--                       child's demand exceeds it in turn.
--
-- The split face is what stands in the file — it is strictly better
-- than the vacuous one and its store/width/ledger conjuncts are
-- unaffected — but it is NOT grind-ready.  The diagnosis, and the one
-- change that escapes both refutations (walkCap's index must become a
-- d-free measure, after which ONE shared entry-determined anchor
-- serves all three roles), is written out at hop-anchor-absurd.  That
-- is a contract change beyond the anchor split and has not been taken.
--
-- THREE POSTULATES REMAIN.  The two real cores are subscribeE-wet and
-- cascadeGo-wet — the termination content proper: fuel-accounting
-- induction over the subscription machine's clauses (the three
-- decrement edges each consume one hasAtLeast-peel against
-- dBound-μ/-hop/-connect; everything between is structural), and the
-- fold's threading invariant (see cascadeGo-wet's memo).  The third is
-- subscribeE-walk, the joint wet/dry/length face they are stated
-- against.  PROVEN 2026-07-29: hopD-size (the hop measure is now
-- derived end to end), and the walk's two bookkeeping companions
-- subscribeE-slots and subscribeE-connected-mono — one joint `Keeps`
-- induction over subscribeE's whole clique.  SPLICED: Verify-Well-Formed imports
-- budget-sufficient from here instead of postulating it.
module Verify-Budget-Sufficient where

open import Data.Bool    using (Bool; true; false; T; _∧_; _∨_; not;
                                if_then_else_)
open import Data.Nat     using (ℕ; zero; suc; pred; _+_; _*_; _^_; _≤_; _<_;
                                _⊔_; _≤ᵇ_; _<ᵇ_; _≡ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (≤ᵇ⇒≤; ≤⇒≤ᵇ; ≤-trans; ≤-refl;
                                       ≤-reflexive; <-≤-trans; ≤-pred;
                                       +-suc; +-identityʳ;
                                       +-comm; +-assoc; +-monoʳ-<;
                                       +-monoˡ-<; +-monoˡ-≤;
                                       *-monoˡ-≤; *-monoʳ-≤;
                                       m⊔n≤o⇒m≤o; m⊔n≤o⇒n≤o; ⊔-mono-≤;
                                       *-suc; m≤m+n; m≤n+m; n≤1+n;
                                       m≤n⇒m<n∨m≡n; +-mono-≤; m≤m*n;
                                       ^-monoʳ-≤; *-assoc;
                                       +-mono-<-≤; +-mono-≤-<; ≡⇒≡ᵇ;
                                       *-distribʳ-+; *-distribˡ-+; *-identityʳ; <⇒≤;
                                       ^-monoˡ-≤; ^-*-assoc;
                                       ^-distribˡ-+-*; *-mono-≤;
                                       +-monoʳ-≤; *-comm;
                                       m≤m⊔n; m≤n⊔m; ⊔-lub; *-zeroʳ; *-identityˡ;
                                       suc-injective; <-irrefl; ≡ᵇ⇒≡)
open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Nat.Induction  using (<-wellFounded)
open import Data.Nat.Solver     using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.List    using (List; []; _∷_; _++_; all; any; length;
                                sum; tabulate; concat; map)
open import Data.Fin     using (Fin; toℕ)
import Data.Fin as Fin
open import Data.Bool.Properties using (∨-zeroʳ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []ᵃ; _∷_ to _∷ᵃ_; map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties
  using (concat⁺; tabulate⁺)
  renaming (++⁺ to all-++; ++⁻ˡ to all-++ˡ; ++⁻ʳ to all-++ʳ)
open import Data.List.Properties using (length-++)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.Maybe   using (Maybe; nothing; just)
open import Relation.Nullary using (yes; no)
open import Data.Vec     using (Vec; lookup) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (inj₁; inj₂)
open import Data.Unit    using (⊤; tt)
open import Induction.WellFounded using (Acc; acc; WellFounded)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Rx.Prim      using (Fuel; Tick; Id; Source; InstEmit;
                                _at_from_as_; EmitKind; subscribe;
                                InstEvent; init; value; close; handoff;
                                complete; exhausted;
                                Gas; g0; gs; gasDouble; gasPow2; gasTower; gasPad;
                                Timed; after_,_; ObservableInput; hot; cold)
open import Rx.Exp       using (Ty; unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_; obs; _≟ᵗ_; isData;
                                Ctx; Closed; Val; sizeᵉ; sizeᵗ; sizeᵗˢ; sizeᵛ;
                                syncSizeᵉ; syncSizeᵗ; syncSizeᵗˢ;
                                shellSizeᵉ; innerᵉ; innerᵗ; innerᵗˢ;
                                shellsᵉ; shellsᵛ;
                                subΘExp; subΘTm; subΘTms;
                                plugsᵉ; plugsᵗ; plugsᵗˢ;
                                occsᵉ; occsᵗ; occsᵗˢ; varIx;
                                renExp; renTm; renTms; Ren∈; ext∈; ++Ren;
                                wkExp; wkTm; reify;
                                Exp; Tm; Fn; varᵗ; unit̂; bool̂; nat̂; pairᵗ;
                                fstᵗ; sndᵗ; inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ;
                                strmᵗ; add; sub; mul; eqᵖ; ltᵖ; notᵖ;
                                input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ;
                                mergeAllᵉ; concatAllᵉ; switchAllᵉ;
                                exhaustAllᵉ; μᵉ; varᵉ; deferᵉ;
                                elimGExp; elimGTm; elimGTms;
                                elimDExp; elimDTm; elimDTms;
                                compare∈; _⊟_; ⊟-++ˡ; ⊟-++ʳ; unfoldμ;
                                evalWith; evalTm; applyFn; lookupEnv)
open import Rx.Hop-Depth using (hopDᵉ; hopDᵗ; hopDᵗˢ; hopDᵛ; pmᵉ; pmᵗ; pmᵗˢ)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; Slots; LiveSource;
                                Slot; scripted; shared; resolve; mkHot;
                                arrVal; scanVals; memberSource;
                                slotSize; inputSize;
                                RegId; Chain;
                                NodeState; scan-st; take-st; merge-st;
                                concat-st; switch-st; exhaust-st;
                                oneShotBurst; installNode; setNode; lookupNode;
                                NodeId;
                                root; share-sink; _↠_; Frame; AllOp;
                                map-f; scan-f; take-f; from-inner;
                                thru-outer; Stream;
                                sched-init; st-init; sched-next;
                                schedHeadOf; schedGo; schedEarlier;
                                cascadeLatch; cascadeFinish; sweepLive;
                                takeVals; takeDispatch; cutThrough; pathHasNode;
                                dropSource; arrSource; chainsOf; cascadeGo;
                                Path; arrTy;
                                subscribeE; stepFrame; pushBurst;
                                subscribeInner; chainStep; subscribeAll;
                                mintNode; mintSource; mintOrdinal; register;
                                mergeᵒ; concatᵒ; switchᵒ; exhaustᵒ;
                                splitEvents; splitBurst; retagEvents;
                                mergeBump; switchKill;
                                thruConsume; thruWalk; thruWrap;
                                concatDrain; innerFinish; innerReact;
                                sharedPlumb; sharedConnect; subscribeSharedSlot;
                                burstCompleted;
                                shareLatch; shareAdmit; shareFinish; shareGo;
                                foldPath; dispatchShare; arrTick;
                                aliveThroughᶠ;
                                cascade; drain; evaluate;
                                hasDry; dryEvent; sameSource;
                                budgetAt; slotsSize)

------------------------------------------------------------------
-- dry-freeness composes over ++ (the other direction from
-- Verify-Well-Formed's hasDry-++ split)
------------------------------------------------------------------

∨-false : ∀ (a b : Bool) → a ∨ b ≡ false → (a ≡ false) × (b ≡ false)
∨-false false b h = refl , h
∨-false true  b ()

hasDry-append : ∀ {A : Set} (xs ys : List (InstEmit A)) →
  hasDry xs ≡ false → hasDry ys ≡ false → hasDry (xs ++ ys) ≡ false
hasDry-append []        ys h₁ h₂ = h₂
hasDry-append (em ∷ xs) ys h₁ h₂
  with ∨-false (any dryEvent (InstEmit.events em)) _ h₁
... | e₁ , h₁′ rewrite e₁ = hasDry-append xs ys h₁′ h₂

------------------------------------------------------------------
-- the ℕ-valued SIZE budget for the stored-value invariant: the same
-- tower shape as the Gas fuel budget (stored values tower exactly as
-- fuel demand does — the scan attack compounds both), but as a ℕ so
-- it can bound sizeᵛ via ≤ᵇ.  Proof-side only: never computed on a
-- concrete program, so strictness is irrelevant here
------------------------------------------------------------------

n<2^n : ∀ n → n < 2 ^ n
n<2^n zero    = s≤s z≤n
n<2^n (suc n) = ≤-trans step (≤-reflexive shape)
  where
  step : suc (suc n) ≤ 2 ^ n + 2 ^ n
  step = ≤-trans (+-monoˡ-≤ (suc n) (s≤s z≤n))
                 (+-mono-≤ (n<2^n n) (n<2^n n))
  shape : 2 ^ n + 2 ^ n ≡ 2 ^ suc n
  shape = cong (2 ^ n +_) (sym (+-identityʳ (2 ^ n)))

towerℕ : ℕ → ℕ
towerℕ zero    = 1
towerℕ (suc h) = 2 ^ towerℕ h

-- height (4+sz)·(1+id): the per-instant story gain (4+sz) ≥ 5 covers
-- the walk ledger's worst-case ~4-story spend against the ENTRY cap
-- (see the walk-invariant memo below) at every program size — the
-- old (1+sz) height left only 2 stories at sz = 1
sizeBudgetAt : ∀ {n} {Γ : Ctx n} {t} → Closed Γ t → Slots Γ → Id → ℕ
sizeBudgetAt e sl id = towerℕ ((4 + (sizeᵉ e + slotsSize sl)) * suc id)

towerℕ-mono : ∀ {m n} → m ≤ n → towerℕ m ≤ towerℕ n
towerℕ-mono {zero}  {zero}  h = ≤-refl
towerℕ-mono {zero}  {suc n} h =
  ≤-trans (towerℕ-mono {zero} {n} z≤n)
          (≤-trans (n≤1+n (towerℕ n)) (n<2^n (towerℕ n)))
towerℕ-mono {suc m} {suc n} (s≤s h) = ^-monoʳ-≤ 2 (towerℕ-mono h)

k≤towerℕ : ∀ k → k ≤ towerℕ k
k≤towerℕ zero    = z≤n
k≤towerℕ (suc k) =
  ≤-trans (n<2^n k) (^-monoʳ-≤ 2 (k≤towerℕ k))

-- the budget covers the syntax that seeds it, at every instant
sz≤budget : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id : Id) → sizeᵉ e + slotsSize sl ≤ sizeBudgetAt e sl id
sz≤budget e sl id =
  ≤-trans (m≤n+m (sizeᵉ e + slotsSize sl) 4)
  (≤-trans (m≤m*n (4 + (sizeᵉ e + slotsSize sl)) (suc id))
           (k≤towerℕ ((4 + (sizeᵉ e + slotsSize sl)) * suc id)))

size≤budget : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id : Id) → sizeᵉ e ≤ sizeBudgetAt e sl id
size≤budget e sl id =
  ≤-trans (m≤m+n (sizeᵉ e) (slotsSize sl)) (sz≤budget e sl id)

slots≤budget : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id : Id) → slotsSize sl ≤ sizeBudgetAt e sl id
slots≤budget e sl id =
  ≤-trans (m≤n+m (slotsSize sl) (sizeᵉ e)) (sz≤budget e sl id)

------------------------------------------------------------------
-- the Gas ordering: `g hasAtLeast n` — n peels are available.  The
-- wet-contract lemmas consume fuel through this view (an `hs` match
-- exposes the `gs` the machine's decrement edges pattern-match on),
-- and the budget lemmas below discharge it: the gasPad literal head
-- alone covers any n ≤ 2^(sz·(id+1)²), and head+tower covers the
-- tower-sized needs of chained-scan programs
------------------------------------------------------------------

data _hasAtLeast_ : Gas → ℕ → Set where
  hz : ∀ {g} → g hasAtLeast zero
  hs : ∀ {g n} → g hasAtLeast n → gs g hasAtLeast suc n

hasAtLeast-mono : ∀ {g m n} → n ≤ m → g hasAtLeast m → g hasAtLeast n
hasAtLeast-mono z≤n       _        = hz
hasAtLeast-mono (s≤s le) (hs h) = hs (hasAtLeast-mono le h)

hasAtLeast-pad : ∀ (m : ℕ) (g : Gas) {n} → n ≤ m → gasPad m g hasAtLeast n
hasAtLeast-pad m       g z≤n      = hz
hasAtLeast-pad (suc m) g (s≤s le) = hs (hasAtLeast-pad m g le)

hasAtLeast-pad-plus : ∀ (m : ℕ) {g : Gas} {n} →
  g hasAtLeast n → gasPad m g hasAtLeast (m + n)
hasAtLeast-pad-plus zero    h = h
hasAtLeast-pad-plus (suc m) h = hs (hasAtLeast-pad-plus m h)

hasAtLeast-double : ∀ {g n} → g hasAtLeast n → gasDouble g hasAtLeast (n + n)
hasAtLeast-double hz = hz
hasAtLeast-double (hs {g} {n} h) =
  hs (subst (λ k → gs (gasDouble g) hasAtLeast k) (sym (+-suc n n))
       (hs (hasAtLeast-double h)))

-- 2^g is never empty, whatever g is
pow2-min : ∀ (g : Gas) → gasPow2 g hasAtLeast 1
pow2-min g0     = hs hz
pow2-min (gs g) =
  hasAtLeast-mono (s≤s z≤n) (hasAtLeast-double (pow2-min g))

hasAtLeast-pow2 : ∀ {g n} → g hasAtLeast n → gasPow2 g hasAtLeast (2 ^ n)
hasAtLeast-pow2 {g} hz = pow2-min g
hasAtLeast-pow2 {n = suc n} (hs {g} h) =
  subst (λ k → gasDouble (gasPow2 g) hasAtLeast (2 ^ n + k))
        (sym (+-identityʳ (2 ^ n)))
        (hasAtLeast-double (hasAtLeast-pow2 h))

hasAtLeast-tower : ∀ (h : ℕ) → gasTower h hasAtLeast towerℕ h
hasAtLeast-tower zero    = hs hz
hasAtLeast-tower (suc h) = hasAtLeast-pow2 (hasAtLeast-tower h)

-- what the seeded budget guarantees: the full head plus the tower
-- (height (7+sz)·(id+2) — three-plus stories above sizeBudgetAt's
-- LANDING instant, the headroom the wet contract's rank demand,
-- anchored at the landing budget, consumes)
budget-hasAtLeast : ∀ (sz : ℕ) (id : Id) →
  gasPad (2 ^ (sz * suc id * suc id)) (gasTower ((7 + sz) * suc (suc id)))
    hasAtLeast (2 ^ (sz * suc id * suc id) + towerℕ ((7 + sz) * suc (suc id)))
budget-hasAtLeast sz id =
  hasAtLeast-pad-plus (2 ^ (sz * suc id * suc id))
                      (hasAtLeast-tower ((7 + sz) * suc (suc id)))

-- the peel every decrement-edge clause performs: enough fuel means
-- the machine's gs-match succeeds and the tail still has enough
hasAtLeast-peel : ∀ {g : Gas} {m : ℕ} → g hasAtLeast suc m →
  Σ Gas (λ g′ → (g ≡ gs g′) × (g′ hasAtLeast m))
hasAtLeast-peel (hs h) = _ , refl , h

------------------------------------------------------------------
-- the machine's value stores, bounded: schedule pendings, scan
-- accumulators, concat queues.  Registry paths and slot defs are
-- fixed syntax — no growth, no clause
------------------------------------------------------------------

boundedLive : ∀ {n} {Γ : Ctx n} → ℕ → LiveSource Γ → Bool
boundedLive B l =
  all (λ tv → sizeᵛ (LiveSource.elemTy l) (proj₂ tv) ≤ᵇ B)
      (LiveSource.pending l)

boundedNode : ∀ {n} {Γ : Ctx n} → ℕ → NodeState Γ → Bool
boundedNode B (scan-st {t} v)      = sizeᵛ t v ≤ᵇ B
boundedNode B (concat-st q _ _)    = all (λ o → sizeᵉ o ≤ᵇ B) q
boundedNode B (take-st _)          = true
boundedNode B (merge-st _ _)       = true
boundedNode B (switch-st _ _)      = true
boundedNode B (exhaust-st _ _)     = true

stBounded? : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
           → ℕ → Sched Γ → EvalSt e → Bool
stBounded? B sched st =
  all (boundedLive B) (Sched.live sched)
  ∧ all (λ kv → boundedNode B (proj₂ kv)) (EvalSt.nodes st)

------------------------------------------------------------------
-- popping the next arrival: the slots are fixed by the record
-- update, and boundedness survives because one pending list shrinks
-- and everything else is untouched — PROVEN by inverting schedGo
------------------------------------------------------------------

∧-true : ∀ (a b : Bool) → a ∧ b ≡ true → (a ≡ true) × (b ≡ true)
∧-true true  b h = refl , h
∧-true false b ()

∧-intro : ∀ {a b : Bool} → a ≡ true → b ≡ true → a ∧ b ≡ true
∧-intro refl refl = refl

schedHeadOf-bounded : ∀ {n} {Γ : Ctx n} (B : ℕ) (l : LiveSource Γ)
  {a : Arrival Γ} {l′ : LiveSource Γ} →
  schedHeadOf l ≡ inj₂ (a , l′) →
  boundedLive B l ≡ true → boundedLive B l′ ≡ true
schedHeadOf-bounded B l eq bnd with LiveSource.pending l | eq | bnd
... | (t , v) ∷ ps | refl | bnd′ = proj₂ (∧-true _ _ bnd′)

schedGo-bounded : ∀ {n} {Γ : Ctx n} (B : ℕ) (ls : List (LiveSource Γ))
  {a : Arrival Γ} {ls′ : List (LiveSource Γ)} →
  schedGo ls ≡ inj₂ (a , ls′) →
  all (boundedLive B) ls ≡ true → all (boundedLive B) ls′ ≡ true
schedGo-bounded B (l ∷ ls) eq bnd
  with ∧-true (boundedLive B l) (all (boundedLive B) ls) bnd
... | bl , bls with schedHeadOf l in eqH | schedGo ls in eqR
schedGo-bounded B (l ∷ ls) refl bnd | bl , bls | inj₁ _ | inj₂ (a′ , ls″) =
  ∧-intro bl (schedGo-bounded B ls eqR bls)
schedGo-bounded B (l ∷ ls) refl bnd | bl , bls | inj₂ (a″ , l′) | inj₁ _ =
  ∧-intro (schedHeadOf-bounded B l eqH bl) bls
schedGo-bounded B (l ∷ ls) eq bnd | bl , bls | inj₂ (a″ , l′) | inj₂ (a′ , ls″)
  with schedEarlier a″ a′ | eq
... | true  | refl = ∧-intro (schedHeadOf-bounded B l eqH bl) bls
... | false | refl = ∧-intro bl (schedGo-bounded B ls eqR bls)

pop-slots : ∀ {n} {Γ : Ctx n}
  (sched : Sched Γ) {a : Arrival Γ} {sched′ : Sched Γ} →
  sched-next sched ≡ inj₂ (a , sched′) →
  Sched.slots sched′ ≡ Sched.slots sched
pop-slots sched eq with schedGo (Sched.live sched) | eq
... | inj₂ (a″ , ls) | refl = refl

pop-bounded : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (B : ℕ) (sched : Sched Γ) (st : EvalSt e)
  {a : Arrival Γ} {sched′ : Sched Γ} →
  sched-next sched ≡ inj₂ (a , sched′) →
  stBounded? B sched st ≡ true → stBounded? B sched′ st ≡ true
pop-bounded B sched st eq bnd
  with ∧-true (all (boundedLive B) (Sched.live sched)) _ bnd
... | bls , bns with schedGo (Sched.live sched) in eqL | eq
... | inj₂ (a″ , ls) | refl =
      ∧-intro (schedGo-bounded B (Sched.live sched) eqL bls) bns

------------------------------------------------------------------
-- structural preservation around the cascade — PROVEN pieces the
-- eventual cascade-dry proof composes, whatever its core shape
------------------------------------------------------------------

T-to : ∀ {b : Bool} → b ≡ true → T b
T-to refl = tt

T⇒≡true : ∀ b → T b → b ≡ true
T⇒≡true true _ = refl

-- generic: a pointwise implication lifts through all
all-impl : ∀ {A : Set} (p q : A → Bool) →
  (∀ x → p x ≡ true → q x ≡ true) →
  ∀ (xs : List A) → all p xs ≡ true → all q xs ≡ true
all-impl p q imp []       h = refl
all-impl p q imp (x ∷ xs) h
  with ∧-true (p x) (all p xs) h
... | px , pxs = ∧-intro (imp x px) (all-impl p q imp xs pxs)

≤ᵇ-widen : ∀ (v : ℕ) {B B′ : ℕ} → B ≤ B′ → (v ≤ᵇ B) ≡ true → (v ≤ᵇ B′) ≡ true
≤ᵇ-widen v {B} {B′} le h with ≤⇒≤ᵇ (≤-trans (≤ᵇ⇒≤ v B (T-to h)) le)
... | w = T-elim w
  where
  T-elim : ∀ {b : Bool} → T b → b ≡ true
  T-elim {true} _ = refl

boundedLive-widen : ∀ {n} {Γ : Ctx n} {B B′ : ℕ} → B ≤ B′ →
  (l : LiveSource Γ) → boundedLive B l ≡ true → boundedLive B′ l ≡ true
boundedLive-widen le l =
  all-impl _ _ (λ tv → ≤ᵇ-widen (sizeᵛ (LiveSource.elemTy l) (proj₂ tv)) le)
           (LiveSource.pending l)

boundedNode-widen : ∀ {n} {Γ : Ctx n} {B B′ : ℕ} → B ≤ B′ →
  (ns : NodeState Γ) → boundedNode B ns ≡ true → boundedNode B′ ns ≡ true
boundedNode-widen le (scan-st {t} v)   h = ≤ᵇ-widen (sizeᵛ t v) le h
boundedNode-widen le (concat-st q _ _) h =
  all-impl _ _ (λ o → ≤ᵇ-widen (sizeᵉ o) le) q h
boundedNode-widen le (take-st _)       h = refl
boundedNode-widen le (merge-st _ _)    h = refl
boundedNode-widen le (switch-st _ _)   h = refl
boundedNode-widen le (exhaust-st _ _)  h = refl

-- the invariant survives raising the bound — composes cascades:
-- landing within (suc id)'s budget IS starting within (suc id)'s
stBounded-widen : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {B B′ : ℕ} →
  B ≤ B′ → (sched : Sched Γ) (st : EvalSt e) →
  stBounded? B sched st ≡ true → stBounded? B′ sched st ≡ true
stBounded-widen le sched st h
  with ∧-true _ _ h
... | hl , hn =
  ∧-intro (all-impl _ _ (λ l → boundedLive-widen le l) (Sched.live sched) hl)
          (all-impl _ _ (λ kv → boundedNode-widen le (proj₂ kv))
                    (EvalSt.nodes st) hn)

-- the latch touches only per-cascade ledger fields — the value
-- stores are untouched
latch-bounded : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (B : ℕ) (sched : Sched Γ) (a : Arrival Γ) (st : EvalSt e) →
  stBounded? B sched st ≡ true →
  stBounded? B sched (cascadeLatch a st) ≡ true
latch-bounded B sched a st bnd with Arrival.isLast a
... | true  = bnd
... | false = bnd

-- the sweep is a filter: every survivor was already bounded
sweepLive-bounded : ∀ {n} {Γ : Ctx n} {t} (B : ℕ)
  (reg : List (RegId × Source × Chain Γ t)) (ls : List (LiveSource Γ)) →
  all (boundedLive B) ls ≡ true →
  all (boundedLive B) (sweepLive reg ls) ≡ true
sweepLive-bounded B reg []       h = refl
sweepLive-bounded {n = n} B reg (l ∷ ls) h
  with ∧-true (boundedLive B l) (all (boundedLive B) ls) h
... | bl , bls
  with (LiveSource.source l <ᵇ n)
       ∨ any (λ p → sameSource (LiveSource.source l) (proj₁ (proj₂ p))) reg
... | true  = ∧-intro bl (sweepLive-bounded B reg ls bls)
... | false = sweepLive-bounded B reg ls bls

-- the finish drops registry entries (unread by stBounded?) and
-- filters the live schedule
finish-bounded : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (B : ℕ) (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
  stBounded? B sched st ≡ true →
  stBounded? B (proj₁ (cascadeFinish a sched st))
               (proj₂ (cascadeFinish a sched st)) ≡ true
finish-bounded B a sched st bnd with Arrival.isLast a
... | false = bnd
... | true  with ∧-true (all (boundedLive B) (Sched.live sched)) _ bnd
...   | bls , bns =
        ∧-intro (sweepLive-bounded B
                  (dropSource (arrSource a) (EvalSt.registry st))
                  (Sched.live sched) bls)
                bns

-- the finish never touches the slots either (record updates only)
finish-slots : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots (proj₁ (cascadeFinish a sched st)) ≡ Sched.slots sched
finish-slots a sched st with Arrival.isLast a
... | false = refl
... | true  = refl

------------------------------------------------------------------
-- THE MEASURE — edge 3's Dershowitz–Manna multiset, SYNTACTICALLY
-- (the shell reading, Rx.Exp).  A runtime obs value is a closed
-- expression; its measure is the multiset of its shells — the
-- operator-skeleton sizes of the value and of every sync-reachable
-- embedded observable (shellsᵉ).  Shells count Exp constructors
-- only: Tm material is weightless and subΘ rewrites only Tm
-- material, so INSTANTIATION PRESERVES EVERY SHELL EXACTLY
-- (shellSize-subΘ below) — an evaluated template's multiset is a
-- class-preserved copy of the template's, plus the plugged obs
-- values' own shells.  The order is count-vector lex with the HIGH
-- size class first (counts B); ≺ᵛ-wf is the semantic justification
-- and rank (below) the ℕ collapse the contract actually inducts
-- on.  Both side conditions ride on stBounded? for free: every
-- shell of e is ≤ sizeᵉ e (shells-≤) and there are ≤ sizeᵉ e of
-- them (shells-len), so a sizeᵛ cap bounds classes AND entry sum.
------------------------------------------------------------------

-- count-vector lex, high class first
data _≺ᵛ_ : ∀ {m} → Vec ℕ m → Vec ℕ m → Set where
  ≺-here  : ∀ {m x y} {xs ys : Vec ℕ m} → x < y → (x ∷ᵛ xs) ≺ᵛ (y ∷ᵛ ys)
  ≺-there : ∀ {m x} {xs ys : Vec ℕ m} → xs ≺ᵛ ys → (x ∷ᵛ xs) ≺ᵛ (x ∷ᵛ ys)

-- well-foundedness: nested induction — vector length outside, then
-- (Acc of the head, Acc of the tail) lexicographically.  accHead is
-- handed the tail relation's full well-foundedness (wfm) so a head
-- decrease can restart the tail at ANY vector.
accHead : ∀ {m} (wfm : WellFounded (_≺ᵛ_ {m})) (x : ℕ) → Acc _<_ x →
  (xs : Vec ℕ m) → Acc (_≺ᵛ_ {m}) xs → Acc _≺ᵛ_ (x ∷ᵛ xs)
accHead wfm x (acc rx) = go
  where
  go : ∀ xs → Acc _≺ᵛ_ xs → Acc _≺ᵛ_ (x ∷ᵛ xs)
  go xs (acc rxs) = acc λ where
    (≺-here  y<x) → accHead wfm _ (rx y<x) _ (wfm _)
    (≺-there ys≺) → go _ (rxs ys≺)

≺ᵛ-wf : ∀ {m} → WellFounded (_≺ᵛ_ {m})
≺ᵛ-wf {zero}  []ᵛ       = acc λ ()
≺ᵛ-wf {suc m} (x ∷ᵛ xs) = accHead ≺ᵛ-wf x (<-wellFounded x) xs (≺ᵛ-wf xs)

-- counts: the multiset → count-vector reading.  Index 0 is size
-- class B (high first); oversized elements clamp into class B — the
-- contract only ever reads it with all elements ≤ B.
zerosᵛ : ∀ {m} → Vec ℕ m
zerosᵛ {zero}  = []ᵛ
zerosᵛ {suc m} = 0 ∷ᵛ zerosᵛ

oneAt : (B x : ℕ) → Vec ℕ (suc B)     -- a single element of size x
oneAt zero    x = 1 ∷ᵛ []ᵛ
oneAt (suc B) x = if suc B ≤ᵇ x then 1 ∷ᵛ zerosᵛ else 0 ∷ᵛ oneAt B x

_⊕ᵛ_ : ∀ {m} → Vec ℕ m → Vec ℕ m → Vec ℕ m
[]ᵛ       ⊕ᵛ []ᵛ       = []ᵛ
(x ∷ᵛ xs) ⊕ᵛ (y ∷ᵛ ys) = x + y ∷ᵛ (xs ⊕ᵛ ys)

counts : (B : ℕ) → List ℕ → Vec ℕ (suc B)
counts B []      = zerosᵛ
counts B (x ∷ M) = oneAt B x ⊕ᵛ counts B M

-- the wet contract's measure of a subscribed value, end to end —
-- a pure function of the value's syntax
measureE : ∀ {n} {Γ : Ctx n} {t} (B : ℕ) → Closed Γ t → Vec ℕ (suc B)
measureE B e = counts B (shellsᵉ e)

------------------------------------------------------------------
-- the free side conditions: shells are pointwise ≤ the syntax size
-- and no more numerous than it, at every level (expression, term,
-- runtime value) — so stBounded?'s sizeᵛ cap bounds the measure's
-- classes (≤ B) and entry sum (≤ V) with no new invariant.
------------------------------------------------------------------

shellSize≤size : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (e : Exp Γ Δᵍ Δ Θ t) →
  shellSizeᵉ e ≤ sizeᵉ e
shellSize≤size (input i)       = ≤-refl
shellSize≤size (ofᵉ ts)        = s≤s z≤n
shellSize≤size emptyᵉ          = ≤-refl
shellSize≤size (mapᵉ f e)      = s≤s (≤-trans (shellSize≤size e) (m≤n+m _ _))
shellSize≤size (takeᵉ c e)     = s≤s (≤-trans (shellSize≤size e) (m≤n+m _ _))
shellSize≤size (scanᵉ f z e)   = s≤s (≤-trans (shellSize≤size e) (m≤n+m _ _))
shellSize≤size (mergeAllᵉ e)   = s≤s (shellSize≤size e)
shellSize≤size (concatAllᵉ e)  = s≤s (shellSize≤size e)
shellSize≤size (switchAllᵉ e)  = s≤s (shellSize≤size e)
shellSize≤size (exhaustAllᵉ e) = s≤s (shellSize≤size e)
shellSize≤size (μᵉ e)          = s≤s (shellSize≤size e)
shellSize≤size (varᵉ x)        = ≤-refl
shellSize≤size (deferᵉ e)      = s≤s z≤n

mutual
  inner-≤ᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (e : Exp Γ Δᵍ Δ Θ t) →
    All (_≤ sizeᵉ e) (innerᵉ e)
  inner-≤ᵉ (input i)       = []ᵃ
  inner-≤ᵉ (ofᵉ ts)        = mapᴬ (λ p → ≤-trans p (n≤1+n _)) (inner-≤ᵗˢ ts)
  inner-≤ᵉ emptyᵉ          = []ᵃ
  inner-≤ᵉ (mapᵉ f e)      = all-++
    (mapᴬ (λ p → ≤-trans p (≤-trans (m≤m+n _ _) (n≤1+n _))) (inner-≤ᵗ f))
    (mapᴬ (λ p → ≤-trans p (≤-trans (m≤n+m _ _) (n≤1+n _))) (inner-≤ᵉ e))
  inner-≤ᵉ (takeᵉ c e)     = all-++
    (mapᴬ (λ p → ≤-trans p (≤-trans (m≤m+n _ _) (n≤1+n _))) (inner-≤ᵗ c))
    (mapᴬ (λ p → ≤-trans p (≤-trans (m≤n+m _ _) (n≤1+n _))) (inner-≤ᵉ e))
  inner-≤ᵉ (scanᵉ f z e)   = all-++
    (mapᴬ (λ p → ≤-trans p
            (≤-trans (m≤m+n _ _) (≤-trans (m≤m+n _ _) (n≤1+n _))))
          (inner-≤ᵗ f))
    (all-++
      (mapᴬ (λ p → ≤-trans p
              (≤-trans (m≤n+m (sizeᵗ z) (sizeᵗ f))
                       (≤-trans (m≤m+n (sizeᵗ f + sizeᵗ z) (sizeᵉ e))
                                (n≤1+n _))))
            (inner-≤ᵗ z))
      (mapᴬ (λ p → ≤-trans p (≤-trans (m≤n+m _ _) (n≤1+n _)))
            (inner-≤ᵉ e)))
  inner-≤ᵉ (mergeAllᵉ e)   = mapᴬ (λ p → ≤-trans p (n≤1+n _)) (inner-≤ᵉ e)
  inner-≤ᵉ (concatAllᵉ e)  = mapᴬ (λ p → ≤-trans p (n≤1+n _)) (inner-≤ᵉ e)
  inner-≤ᵉ (switchAllᵉ e)  = mapᴬ (λ p → ≤-trans p (n≤1+n _)) (inner-≤ᵉ e)
  inner-≤ᵉ (exhaustAllᵉ e) = mapᴬ (λ p → ≤-trans p (n≤1+n _)) (inner-≤ᵉ e)
  inner-≤ᵉ (μᵉ e)          = mapᴬ (λ p → ≤-trans p (n≤1+n _)) (inner-≤ᵉ e)
  inner-≤ᵉ (varᵉ x)        = []ᵃ
  inner-≤ᵉ (deferᵉ e)      = []ᵃ

  inner-≤ᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (tm : Tm Γ Δᵍ Δ Θ t) →
    All (_≤ sizeᵗ tm) (innerᵗ tm)
  inner-≤ᵗ (varᵗ x)      = []ᵃ
  inner-≤ᵗ unit̂          = []ᵃ
  inner-≤ᵗ (bool̂ _)      = []ᵃ
  inner-≤ᵗ (nat̂ _)       = []ᵃ
  inner-≤ᵗ (pairᵗ a b)   = all-++
    (mapᴬ (λ p → ≤-trans p (≤-trans (m≤m+n _ _) (n≤1+n _))) (inner-≤ᵗ a))
    (mapᴬ (λ p → ≤-trans p (≤-trans (m≤n+m _ _) (n≤1+n _))) (inner-≤ᵗ b))
  inner-≤ᵗ (fstᵗ p)      = mapᴬ (λ q → ≤-trans q (n≤1+n _)) (inner-≤ᵗ p)
  inner-≤ᵗ (sndᵗ p)      = mapᴬ (λ q → ≤-trans q (n≤1+n _)) (inner-≤ᵗ p)
  inner-≤ᵗ (inlᵗ a)      = mapᴬ (λ p → ≤-trans p (n≤1+n _)) (inner-≤ᵗ a)
  inner-≤ᵗ (inrᵗ a)      = mapᴬ (λ p → ≤-trans p (n≤1+n _)) (inner-≤ᵗ a)
  inner-≤ᵗ (caseᵗ s l r) = all-++
    (mapᴬ (λ p → ≤-trans p
            (≤-trans (m≤m+n _ _) (≤-trans (m≤m+n _ _) (n≤1+n _))))
          (inner-≤ᵗ s))
    (all-++
      (mapᴬ (λ p → ≤-trans p
              (≤-trans (m≤n+m (sizeᵗ l) (sizeᵗ s))
                       (≤-trans (m≤m+n (sizeᵗ s + sizeᵗ l) (sizeᵗ r))
                                (n≤1+n _))))
            (inner-≤ᵗ l))
      (mapᴬ (λ p → ≤-trans p (≤-trans (m≤n+m _ _) (n≤1+n _)))
            (inner-≤ᵗ r)))
  inner-≤ᵗ (ifᵗ c a b)   = all-++
    (mapᴬ (λ p → ≤-trans p
            (≤-trans (m≤m+n _ _) (≤-trans (m≤m+n _ _) (n≤1+n _))))
          (inner-≤ᵗ c))
    (all-++
      (mapᴬ (λ p → ≤-trans p
              (≤-trans (m≤n+m (sizeᵗ a) (sizeᵗ c))
                       (≤-trans (m≤m+n (sizeᵗ c + sizeᵗ a) (sizeᵗ b))
                                (n≤1+n _))))
            (inner-≤ᵗ a))
      (mapᴬ (λ p → ≤-trans p (≤-trans (m≤n+m _ _) (n≤1+n _)))
            (inner-≤ᵗ b)))
  inner-≤ᵗ (primᵗ _ a)   = mapᴬ (λ p → ≤-trans p (n≤1+n _)) (inner-≤ᵗ a)
  inner-≤ᵗ (strmᵗ e)     =
    ≤-trans (shellSize≤size e) (n≤1+n _)
    ∷ᵃ mapᴬ (λ p → ≤-trans p (n≤1+n _)) (inner-≤ᵉ e)

  inner-≤ᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (ts : List (Tm Γ Δᵍ Δ Θ t)) →
    All (_≤ sizeᵗˢ ts) (innerᵗˢ ts)
  inner-≤ᵗˢ []       = []ᵃ
  inner-≤ᵗˢ (y ∷ ys) = all-++
    (mapᴬ (λ p → ≤-trans p (m≤m+n _ _)) (inner-≤ᵗ y))
    (mapᴬ (λ p → ≤-trans p (m≤n+m _ _)) (inner-≤ᵗˢ ys))

shells-≤ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (e : Exp Γ Δᵍ Δ Θ t) →
  All (_≤ sizeᵉ e) (shellsᵉ e)
shells-≤ e = shellSize≤size e ∷ᵃ inner-≤ᵉ e

shellsᵛ-≤ : ∀ {n} {Γ : Ctx n} (t : Ty) (v : Val Γ t) →
  All (_≤ sizeᵛ t v) (shellsᵛ t v)
shellsᵛ-≤ unitᵗ    v        = []ᵃ
shellsᵛ-≤ boolᵗ    v        = []ᵃ
shellsᵛ-≤ natᵗ     v        = []ᵃ
shellsᵛ-≤ (s ×ᵗ t) (a , b)  = all-++
  (mapᴬ (λ p → ≤-trans p (≤-trans (m≤m+n _ _) (n≤1+n _))) (shellsᵛ-≤ s a))
  (mapᴬ (λ p → ≤-trans p (≤-trans (m≤n+m _ _) (n≤1+n _))) (shellsᵛ-≤ t b))
shellsᵛ-≤ (s +ᵗ t) (inj₁ a) = mapᴬ (λ p → ≤-trans p (n≤1+n _)) (shellsᵛ-≤ s a)
shellsᵛ-≤ (s +ᵗ t) (inj₂ b) = mapᴬ (λ p → ≤-trans p (n≤1+n _)) (shellsᵛ-≤ t b)
shellsᵛ-≤ (obs t)  e        = shells-≤ e

mutual
  inner-lenᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (e : Exp Γ Δᵍ Δ Θ t) →
    length (innerᵉ e) < sizeᵉ e
  inner-lenᵉ (input i)       = s≤s z≤n
  inner-lenᵉ (ofᵉ ts)        = s≤s (inner-lenᵗˢ ts)
  inner-lenᵉ emptyᵉ          = s≤s z≤n
  inner-lenᵉ (mapᵉ f e)      rewrite length-++ (innerᵗ f) {innerᵉ e} =
    s≤s (≤-trans (n≤1+n _) (+-mono-≤-< (inner-lenᵗ f) (inner-lenᵉ e)))
  inner-lenᵉ (takeᵉ c e)     rewrite length-++ (innerᵗ c) {innerᵉ e} =
    s≤s (≤-trans (n≤1+n _) (+-mono-≤-< (inner-lenᵗ c) (inner-lenᵉ e)))
  inner-lenᵉ (scanᵉ f z e)
    rewrite length-++ (innerᵗ f) {innerᵗ z ++ innerᵉ e}
          | length-++ (innerᵗ z) {innerᵉ e} =
    s≤s (≤-trans (≤-reflexive (sym (+-assoc (length (innerᵗ f))
                                            (length (innerᵗ z)) _)))
        (≤-trans (n≤1+n _)
                 (+-mono-≤-< (+-mono-≤ (inner-lenᵗ f) (inner-lenᵗ z))
                             (inner-lenᵉ e))))
  inner-lenᵉ (mergeAllᵉ e)   = ≤-trans (inner-lenᵉ e) (n≤1+n _)
  inner-lenᵉ (concatAllᵉ e)  = ≤-trans (inner-lenᵉ e) (n≤1+n _)
  inner-lenᵉ (switchAllᵉ e)  = ≤-trans (inner-lenᵉ e) (n≤1+n _)
  inner-lenᵉ (exhaustAllᵉ e) = ≤-trans (inner-lenᵉ e) (n≤1+n _)
  inner-lenᵉ (μᵉ e)          = ≤-trans (inner-lenᵉ e) (n≤1+n _)
  inner-lenᵉ (varᵉ x)        = s≤s z≤n
  inner-lenᵉ (deferᵉ e)      = s≤s z≤n

  inner-lenᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (tm : Tm Γ Δᵍ Δ Θ t) →
    length (innerᵗ tm) ≤ sizeᵗ tm
  inner-lenᵗ (varᵗ x)      = z≤n
  inner-lenᵗ unit̂          = z≤n
  inner-lenᵗ (bool̂ _)      = z≤n
  inner-lenᵗ (nat̂ _)       = z≤n
  inner-lenᵗ (pairᵗ a b)   rewrite length-++ (innerᵗ a) {innerᵗ b} =
    ≤-trans (+-mono-≤ (inner-lenᵗ a) (inner-lenᵗ b)) (n≤1+n _)
  inner-lenᵗ (fstᵗ p)      = ≤-trans (inner-lenᵗ p) (n≤1+n _)
  inner-lenᵗ (sndᵗ p)      = ≤-trans (inner-lenᵗ p) (n≤1+n _)
  inner-lenᵗ (inlᵗ a)      = ≤-trans (inner-lenᵗ a) (n≤1+n _)
  inner-lenᵗ (inrᵗ a)      = ≤-trans (inner-lenᵗ a) (n≤1+n _)
  inner-lenᵗ (caseᵗ s l r)
    rewrite length-++ (innerᵗ s) {innerᵗ l ++ innerᵗ r}
          | length-++ (innerᵗ l) {innerᵗ r} =
    ≤-trans (≤-reflexive (sym (+-assoc (length (innerᵗ s))
                                       (length (innerᵗ l)) _)))
    (≤-trans (+-mono-≤ (+-mono-≤ (inner-lenᵗ s) (inner-lenᵗ l))
                       (inner-lenᵗ r))
             (n≤1+n _))
  inner-lenᵗ (ifᵗ c a b)
    rewrite length-++ (innerᵗ c) {innerᵗ a ++ innerᵗ b}
          | length-++ (innerᵗ a) {innerᵗ b} =
    ≤-trans (≤-reflexive (sym (+-assoc (length (innerᵗ c))
                                       (length (innerᵗ a)) _)))
    (≤-trans (+-mono-≤ (+-mono-≤ (inner-lenᵗ c) (inner-lenᵗ a))
                       (inner-lenᵗ b))
             (n≤1+n _))
  inner-lenᵗ (primᵗ _ a)   = ≤-trans (inner-lenᵗ a) (n≤1+n _)
  inner-lenᵗ (strmᵗ e)     = ≤-trans (inner-lenᵉ e) (n≤1+n _)

  inner-lenᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (ts : List (Tm Γ Δᵍ Δ Θ t)) →
    length (innerᵗˢ ts) ≤ sizeᵗˢ ts
  inner-lenᵗˢ []       = z≤n
  inner-lenᵗˢ (y ∷ ys) rewrite length-++ (innerᵗ y) {innerᵗˢ ys} =
    +-mono-≤ (inner-lenᵗ y) (inner-lenᵗˢ ys)

shells-len : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (e : Exp Γ Δᵍ Δ Θ t) →
  length (shellsᵉ e) ≤ sizeᵉ e
shells-len e = inner-lenᵉ e

-- the value-level shadow of shells-len: a runtime value carries no
-- more shells than its size — so a sizeᵛ cap bounds the entry sum
-- of any environment entry's contribution to a plug multiset
shellsᵛ-len : ∀ {n} {Γ : Ctx n} (t : Ty) (v : Val Γ t) →
  length (shellsᵛ t v) ≤ sizeᵛ t v
shellsᵛ-len unitᵗ    v        = z≤n
shellsᵛ-len boolᵗ    v        = z≤n
shellsᵛ-len natᵗ     v        = z≤n
shellsᵛ-len (s ×ᵗ t) (a , b)  rewrite length-++ (shellsᵛ s a) {shellsᵛ t b} =
  ≤-trans (+-mono-≤ (shellsᵛ-len s a) (shellsᵛ-len t b)) (n≤1+n _)
shellsᵛ-len (s +ᵗ t) (inj₁ a) = ≤-trans (shellsᵛ-len s a) (n≤1+n _)
shellsᵛ-len (s +ᵗ t) (inj₂ b) = ≤-trans (shellsᵛ-len t b) (n≤1+n _)
shellsᵛ-len (obs t)  e        = inner-lenᵉ e

-- the s-reset side condition, free: the synchronous walk of any
-- expression is no larger than its full syntax, so a store size cap
-- caps the contract's s component after every hop
mutual
  syncSize≤sizeᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (e : Exp Γ Δᵍ Δ Θ t) →
    syncSizeᵉ e ≤ sizeᵉ e
  syncSize≤sizeᵉ (input i)       = ≤-refl
  syncSize≤sizeᵉ (ofᵉ ts)        = s≤s (syncSize≤sizeᵗˢ ts)
  syncSize≤sizeᵉ emptyᵉ          = ≤-refl
  syncSize≤sizeᵉ (mapᵉ f e)      =
    s≤s (+-mono-≤ (syncSize≤sizeᵗ f) (syncSize≤sizeᵉ e))
  syncSize≤sizeᵉ (takeᵉ c e)     =
    s≤s (+-mono-≤ (syncSize≤sizeᵗ c) (syncSize≤sizeᵉ e))
  syncSize≤sizeᵉ (scanᵉ f z e)   =
    s≤s (+-mono-≤ (+-mono-≤ (syncSize≤sizeᵗ f) (syncSize≤sizeᵗ z))
                  (syncSize≤sizeᵉ e))
  syncSize≤sizeᵉ (mergeAllᵉ e)   = s≤s (syncSize≤sizeᵉ e)
  syncSize≤sizeᵉ (concatAllᵉ e)  = s≤s (syncSize≤sizeᵉ e)
  syncSize≤sizeᵉ (switchAllᵉ e)  = s≤s (syncSize≤sizeᵉ e)
  syncSize≤sizeᵉ (exhaustAllᵉ e) = s≤s (syncSize≤sizeᵉ e)
  syncSize≤sizeᵉ (μᵉ e)          = s≤s (syncSize≤sizeᵉ e)
  syncSize≤sizeᵉ (varᵉ x)        = ≤-refl
  syncSize≤sizeᵉ (deferᵉ e)      = s≤s z≤n

  syncSize≤sizeᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (tm : Tm Γ Δᵍ Δ Θ t) →
    syncSizeᵗ tm ≤ sizeᵗ tm
  syncSize≤sizeᵗ (varᵗ x)      = ≤-refl
  syncSize≤sizeᵗ unit̂          = ≤-refl
  syncSize≤sizeᵗ (bool̂ _)      = ≤-refl
  syncSize≤sizeᵗ (nat̂ _)       = ≤-refl
  syncSize≤sizeᵗ (pairᵗ a b)   =
    s≤s (+-mono-≤ (syncSize≤sizeᵗ a) (syncSize≤sizeᵗ b))
  syncSize≤sizeᵗ (fstᵗ p)      = s≤s (syncSize≤sizeᵗ p)
  syncSize≤sizeᵗ (sndᵗ p)      = s≤s (syncSize≤sizeᵗ p)
  syncSize≤sizeᵗ (inlᵗ a)      = s≤s (syncSize≤sizeᵗ a)
  syncSize≤sizeᵗ (inrᵗ a)      = s≤s (syncSize≤sizeᵗ a)
  syncSize≤sizeᵗ (caseᵗ s l r) =
    s≤s (+-mono-≤ (+-mono-≤ (syncSize≤sizeᵗ s) (syncSize≤sizeᵗ l))
                  (syncSize≤sizeᵗ r))
  syncSize≤sizeᵗ (ifᵗ c a b)   =
    s≤s (+-mono-≤ (+-mono-≤ (syncSize≤sizeᵗ c) (syncSize≤sizeᵗ a))
                  (syncSize≤sizeᵗ b))
  syncSize≤sizeᵗ (primᵗ _ a)   = s≤s (syncSize≤sizeᵗ a)
  syncSize≤sizeᵗ (strmᵗ e)     = s≤s (syncSize≤sizeᵉ e)

  syncSize≤sizeᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (ts : List (Tm Γ Δᵍ Δ Θ t)) →
    syncSizeᵗˢ ts ≤ sizeᵗˢ ts
  syncSize≤sizeᵗˢ []       = ≤-refl
  syncSize≤sizeᵗˢ (y ∷ ys) =
    +-mono-≤ (syncSize≤sizeᵗ y) (syncSize≤sizeᵗˢ ys)

------------------------------------------------------------------
-- THE CLOSURE, exactly: substitution preserves every shell size.
-- subΘ rewrites only Tm material — Exp constructors map 1-1 and a
-- plugged value sits behind ground literals and strmᵗ leaves, both
-- weightless — so an instantiated template's own shell is its
-- template's shell, on the nose.  This is what makes the scan hop
-- an EMBED hop: the produced value's multiset is a class-preserved
-- copy of the fn-body subtree's sub-multiset (plus plugged obs
-- values' shells, owned by the ledger).
------------------------------------------------------------------

shellSize-subΘ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (Θloc : List Ty)
  (σ : All (Val Γ) Θsub) (e : Exp Γ Δᵍ Δ (Θloc ++ Θsub) t) →
  shellSizeᵉ (subΘExp Θloc σ e) ≡ shellSizeᵉ e
shellSize-subΘ Θloc σ (input i)       = refl
shellSize-subΘ Θloc σ (ofᵉ ts)        = refl
shellSize-subΘ Θloc σ emptyᵉ          = refl
shellSize-subΘ Θloc σ (mapᵉ f e)      = cong suc (shellSize-subΘ Θloc σ e)
shellSize-subΘ Θloc σ (takeᵉ c e)     = cong suc (shellSize-subΘ Θloc σ e)
shellSize-subΘ Θloc σ (scanᵉ f z e)   = cong suc (shellSize-subΘ Θloc σ e)
shellSize-subΘ Θloc σ (mergeAllᵉ e)   = cong suc (shellSize-subΘ Θloc σ e)
shellSize-subΘ Θloc σ (concatAllᵉ e)  = cong suc (shellSize-subΘ Θloc σ e)
shellSize-subΘ Θloc σ (switchAllᵉ e)  = cong suc (shellSize-subΘ Θloc σ e)
shellSize-subΘ Θloc σ (exhaustAllᵉ e) = cong suc (shellSize-subΘ Θloc σ e)
shellSize-subΘ Θloc σ (μᵉ e)          = cong suc (shellSize-subΘ Θloc σ e)
shellSize-subΘ Θloc σ (varᵉ x)        = refl
shellSize-subΘ Θloc σ (deferᵉ e)      = refl

-- renamings never touch shells: shellSizeᵉ reads only Exp
-- constructors and renExp maps them 1-1 (weakening included —
-- wkExp/wkTm are renamings from empty contexts)
shellSize-ren : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t}
  (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′)
  (e : Exp Γ Δᵍ Δ Θ t) →
  shellSizeᵉ (renExp ρg ρd ρt e) ≡ shellSizeᵉ e
shellSize-ren ρg ρd ρt (input i)       = refl
shellSize-ren ρg ρd ρt (ofᵉ ts)        = refl
shellSize-ren ρg ρd ρt emptyᵉ          = refl
shellSize-ren ρg ρd ρt (mapᵉ f e)      = cong suc (shellSize-ren ρg ρd ρt e)
shellSize-ren ρg ρd ρt (takeᵉ c e)     = cong suc (shellSize-ren ρg ρd ρt e)
shellSize-ren ρg ρd ρt (scanᵉ f z e)   = cong suc (shellSize-ren ρg ρd ρt e)
shellSize-ren ρg ρd ρt (mergeAllᵉ e)   = cong suc (shellSize-ren ρg ρd ρt e)
shellSize-ren ρg ρd ρt (concatAllᵉ e)  = cong suc (shellSize-ren ρg ρd ρt e)
shellSize-ren ρg ρd ρt (switchAllᵉ e)  = cong suc (shellSize-ren ρg ρd ρt e)
shellSize-ren ρg ρd ρt (exhaustAllᵉ e) = cong suc (shellSize-ren ρg ρd ρt e)
shellSize-ren ρg ρd ρt (μᵉ e)          = cong suc (shellSize-ren (ext∈ ρg) ρd ρt e)
shellSize-ren ρg ρd ρt (varᵉ x)        = refl
shellSize-ren ρg ρd ρt (deferᵉ e)      = refl

mutual
  inner-renᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t}
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′)
    (e : Exp Γ Δᵍ Δ Θ t) →
    innerᵉ (renExp ρg ρd ρt e) ≡ innerᵉ e
  inner-renᵉ ρg ρd ρt (input i)       = refl
  inner-renᵉ ρg ρd ρt (ofᵉ ts)        = inner-renᵗˢ ρg ρd ρt ts
  inner-renᵉ ρg ρd ρt emptyᵉ          = refl
  inner-renᵉ ρg ρd ρt (mapᵉ f e)      =
    cong₂ _++_ (inner-renᵗ ρg ρd (ext∈ ρt) f) (inner-renᵉ ρg ρd ρt e)
  inner-renᵉ ρg ρd ρt (takeᵉ c e)     =
    cong₂ _++_ (inner-renᵗ ρg ρd ρt c) (inner-renᵉ ρg ρd ρt e)
  inner-renᵉ ρg ρd ρt (scanᵉ f z e)   =
    cong₂ _++_ (inner-renᵗ ρg ρd (ext∈ ρt) f)
               (cong₂ _++_ (inner-renᵗ ρg ρd ρt z) (inner-renᵉ ρg ρd ρt e))
  inner-renᵉ ρg ρd ρt (mergeAllᵉ e)   = inner-renᵉ ρg ρd ρt e
  inner-renᵉ ρg ρd ρt (concatAllᵉ e)  = inner-renᵉ ρg ρd ρt e
  inner-renᵉ ρg ρd ρt (switchAllᵉ e)  = inner-renᵉ ρg ρd ρt e
  inner-renᵉ ρg ρd ρt (exhaustAllᵉ e) = inner-renᵉ ρg ρd ρt e
  inner-renᵉ ρg ρd ρt (μᵉ e)          = inner-renᵉ (ext∈ ρg) ρd ρt e
  inner-renᵉ ρg ρd ρt (varᵉ x)        = refl
  inner-renᵉ ρg ρd ρt (deferᵉ e)      = refl

  inner-renᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t}
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′)
    (tm : Tm Γ Δᵍ Δ Θ t) →
    innerᵗ (renTm ρg ρd ρt tm) ≡ innerᵗ tm
  inner-renᵗ ρg ρd ρt (varᵗ x)      = refl
  inner-renᵗ ρg ρd ρt unit̂          = refl
  inner-renᵗ ρg ρd ρt (bool̂ _)      = refl
  inner-renᵗ ρg ρd ρt (nat̂ _)       = refl
  inner-renᵗ ρg ρd ρt (pairᵗ a b)   =
    cong₂ _++_ (inner-renᵗ ρg ρd ρt a) (inner-renᵗ ρg ρd ρt b)
  inner-renᵗ ρg ρd ρt (fstᵗ p)      = inner-renᵗ ρg ρd ρt p
  inner-renᵗ ρg ρd ρt (sndᵗ p)      = inner-renᵗ ρg ρd ρt p
  inner-renᵗ ρg ρd ρt (inlᵗ a)      = inner-renᵗ ρg ρd ρt a
  inner-renᵗ ρg ρd ρt (inrᵗ a)      = inner-renᵗ ρg ρd ρt a
  inner-renᵗ ρg ρd ρt (caseᵗ sc l r) =
    cong₂ _++_ (inner-renᵗ ρg ρd ρt sc)
               (cong₂ _++_ (inner-renᵗ ρg ρd (ext∈ ρt) l)
                           (inner-renᵗ ρg ρd (ext∈ ρt) r))
  inner-renᵗ ρg ρd ρt (ifᵗ c a b)   =
    cong₂ _++_ (inner-renᵗ ρg ρd ρt c)
               (cong₂ _++_ (inner-renᵗ ρg ρd ρt a) (inner-renᵗ ρg ρd ρt b))
  inner-renᵗ ρg ρd ρt (primᵗ _ a)   = inner-renᵗ ρg ρd ρt a
  inner-renᵗ ρg ρd ρt (strmᵗ e)     =
    cong₂ _∷_ (shellSize-ren ρg ρd ρt e) (inner-renᵉ ρg ρd ρt e)

  inner-renᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t}
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′)
    (ts : List (Tm Γ Δᵍ Δ Θ t)) →
    innerᵗˢ (renTms ρg ρd ρt ts) ≡ innerᵗˢ ts
  inner-renᵗˢ ρg ρd ρt []       = refl
  inner-renᵗˢ ρg ρd ρt (y ∷ ys) =
    cong₂ _++_ (inner-renᵗ ρg ρd ρt y) (inner-renᵗˢ ρg ρd ρt ys)

-- a reified value's embedded shells are exactly the value's own:
-- ground skeleton contributes nothing, obs components sit behind
-- strmᵗ verbatim
reify-inner : ∀ {n} {Γ : Ctx n} (t : Ty) (v : Val Γ t) →
  innerᵗ (reify v) ≡ shellsᵛ t v
reify-inner unitᵗ    v        = refl
reify-inner boolᵗ    v        = refl
reify-inner natᵗ     v        = refl
reify-inner (s ×ᵗ t) (a , b)  = cong₂ _++_ (reify-inner s a) (reify-inner t b)
reify-inner (s +ᵗ t) (inj₁ a) = reify-inner s a
reify-inner (s +ᵗ t) (inj₂ b) = reify-inner t b
reify-inner (obs t)  e        = refl

-- the cap closure: instantiating a capped template over a capped
-- environment yields capped shells — the substrate of invariant
-- preservation at every evalWith/applyFn site.  (The host shell is
-- covered separately and exactly by shellSize-subΘ.)
EnvCap : ∀ {n} {Γ : Ctx n} {Θ} (B : ℕ) → All (Val Γ) Θ → Set
EnvCap B []ᵃ              = ⊤
EnvCap B (_∷ᵃ_ {x = t} v σ) = All (_≤ B) (shellsᵛ t v) × EnvCap B σ

envCap-lookup : ∀ {n} {Γ : Ctx n} {Θ t} (B : ℕ) (σ : All (Val Γ) Θ) →
  EnvCap B σ → (z : t ∈ Θ) → All (_≤ B) (shellsᵛ t (lookupEnv σ z))
envCap-lookup B (v ∷ᵃ σ) (hv , hσ) (here refl) = hv
envCap-lookup B (v ∷ᵃ σ) (hv , hσ) (there z)   = envCap-lookup B σ hσ z

mutual
  subΘ-capᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (B : ℕ) (Θloc : List Ty)
    (σ : All (Val Γ) Θsub) (e : Exp Γ Δᵍ Δ (Θloc ++ Θsub) t) →
    All (_≤ B) (innerᵉ e) → EnvCap B σ →
    All (_≤ B) (innerᵉ (subΘExp Θloc σ e))
  subΘ-capᵉ B Θloc σ (input i)       h hσ = []ᵃ
  subΘ-capᵉ B Θloc σ (ofᵉ ts)        h hσ = subΘ-capᵗˢ B Θloc σ ts h hσ
  subΘ-capᵉ B Θloc σ emptyᵉ          h hσ = []ᵃ
  subΘ-capᵉ B Θloc σ (mapᵉ {s = s} f e) h hσ = all-++
    (subΘ-capᵗ B (s ∷ Θloc) σ f (all-++ˡ (innerᵗ f) h) hσ)
    (subΘ-capᵉ B Θloc σ e (all-++ʳ (innerᵗ f) h) hσ)
  subΘ-capᵉ B Θloc σ (takeᵉ c e)     h hσ = all-++
    (subΘ-capᵗ B Θloc σ c (all-++ˡ (innerᵗ c) h) hσ)
    (subΘ-capᵉ B Θloc σ e (all-++ʳ (innerᵗ c) h) hσ)
  subΘ-capᵉ B Θloc σ (scanᵉ {s = s} {t = t} f z e) h hσ = all-++
    (subΘ-capᵗ B ((t ×ᵗ s) ∷ Θloc) σ f (all-++ˡ (innerᵗ f) h) hσ)
    (all-++
      (subΘ-capᵗ B Θloc σ z
        (all-++ˡ (innerᵗ z) (all-++ʳ (innerᵗ f) h)) hσ)
      (subΘ-capᵉ B Θloc σ e
        (all-++ʳ (innerᵗ z) (all-++ʳ (innerᵗ f) h)) hσ))
  subΘ-capᵉ B Θloc σ (mergeAllᵉ e)   h hσ = subΘ-capᵉ B Θloc σ e h hσ
  subΘ-capᵉ B Θloc σ (concatAllᵉ e)  h hσ = subΘ-capᵉ B Θloc σ e h hσ
  subΘ-capᵉ B Θloc σ (switchAllᵉ e)  h hσ = subΘ-capᵉ B Θloc σ e h hσ
  subΘ-capᵉ B Θloc σ (exhaustAllᵉ e) h hσ = subΘ-capᵉ B Θloc σ e h hσ
  subΘ-capᵉ B Θloc σ (μᵉ e)          h hσ = subΘ-capᵉ B Θloc σ e h hσ
  subΘ-capᵉ B Θloc σ (varᵉ x)        h hσ = []ᵃ
  subΘ-capᵉ B Θloc σ (deferᵉ e)      h hσ = []ᵃ

  subΘ-capᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (B : ℕ) (Θloc : List Ty)
    (σ : All (Val Γ) Θsub) (tm : Tm Γ Δᵍ Δ (Θloc ++ Θsub) t) →
    All (_≤ B) (innerᵗ tm) → EnvCap B σ →
    All (_≤ B) (innerᵗ (subΘTm Θloc σ tm))
  subΘ-capᵗ B Θloc σ (varᵗ x) h hσ with ∈-++⁻ Θloc x
  ... | inj₁ y = []ᵃ
  ... | inj₂ z = subst (All (_≤ B))
      (sym (trans (inner-renᵗ (λ ()) (λ ()) (λ ())
                              (reify (lookupEnv σ z)))
                  (reify-inner _ (lookupEnv σ z))))
      (envCap-lookup B σ hσ z)
  subΘ-capᵗ B Θloc σ unit̂          h hσ = []ᵃ
  subΘ-capᵗ B Θloc σ (bool̂ _)      h hσ = []ᵃ
  subΘ-capᵗ B Θloc σ (nat̂ _)       h hσ = []ᵃ
  subΘ-capᵗ B Θloc σ (pairᵗ a b)   h hσ = all-++
    (subΘ-capᵗ B Θloc σ a (all-++ˡ (innerᵗ a) h) hσ)
    (subΘ-capᵗ B Θloc σ b (all-++ʳ (innerᵗ a) h) hσ)
  subΘ-capᵗ B Θloc σ (fstᵗ p)      h hσ = subΘ-capᵗ B Θloc σ p h hσ
  subΘ-capᵗ B Θloc σ (sndᵗ p)      h hσ = subΘ-capᵗ B Θloc σ p h hσ
  subΘ-capᵗ B Θloc σ (inlᵗ a)      h hσ = subΘ-capᵗ B Θloc σ a h hσ
  subΘ-capᵗ B Θloc σ (inrᵗ a)      h hσ = subΘ-capᵗ B Θloc σ a h hσ
  subΘ-capᵗ B Θloc σ (caseᵗ {s = s} {t = t} sc l r) h hσ = all-++
    (subΘ-capᵗ B Θloc σ sc (all-++ˡ (innerᵗ sc) h) hσ)
    (all-++
      (subΘ-capᵗ B (s ∷ Θloc) σ l
        (all-++ˡ (innerᵗ l) (all-++ʳ (innerᵗ sc) h)) hσ)
      (subΘ-capᵗ B (t ∷ Θloc) σ r
        (all-++ʳ (innerᵗ l) (all-++ʳ (innerᵗ sc) h)) hσ))
  subΘ-capᵗ B Θloc σ (ifᵗ c a b)   h hσ = all-++
    (subΘ-capᵗ B Θloc σ c (all-++ˡ (innerᵗ c) h) hσ)
    (all-++
      (subΘ-capᵗ B Θloc σ a
        (all-++ˡ (innerᵗ a) (all-++ʳ (innerᵗ c) h)) hσ)
      (subΘ-capᵗ B Θloc σ b
        (all-++ʳ (innerᵗ a) (all-++ʳ (innerᵗ c) h)) hσ))
  subΘ-capᵗ B Θloc σ (primᵗ _ a)   h hσ = subΘ-capᵗ B Θloc σ a h hσ
  subΘ-capᵗ B Θloc σ (strmᵗ e) (hd ∷ᵃ tl) hσ =
    subst (_≤ B) (sym (shellSize-subΘ Θloc σ e)) hd
    ∷ᵃ subΘ-capᵉ B Θloc σ e tl hσ

  subΘ-capᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (B : ℕ) (Θloc : List Ty)
    (σ : All (Val Γ) Θsub) (ts : List (Tm Γ Δᵍ Δ (Θloc ++ Θsub) t)) →
    All (_≤ B) (innerᵗˢ ts) → EnvCap B σ →
    All (_≤ B) (innerᵗˢ (subΘTms Θloc σ ts))
  subΘ-capᵗˢ B Θloc σ []       h hσ = []ᵃ
  subΘ-capᵗˢ B Θloc σ (y ∷ ys) h hσ = all-++
    (subΘ-capᵗ B Θloc σ y (all-++ˡ (innerᵗ y) h) hσ)
    (subΘ-capᵗˢ B Θloc σ ys (all-++ʳ (innerᵗ y) h) hσ)

------------------------------------------------------------------
-- EDGE 2, DISCHARGED: μ-unfolding preserves sync-reachable size.
-- elimG never substitutes outside a deferᵉ (the μ-var is guarded in
-- Δᵍ; only deferᵉ moves it into Δ where elimD can hit it), and
-- syncSize treats deferᵉ as a leaf — so every clause is homomorphic
-- and the deferᵉ clause is refl on both sides, subst cast and all.
-- Hence the μ-unfold decrement edge strictly shrinks syncSize:
-- the machine swaps μᵉ body (suc …) for unfoldμ body (…).
------------------------------------------------------------------

mutual
  syncSize-elimG : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
    (cl : Closed Γ t) (e : Exp Γ Δᵍ Δ Θ u) →
    syncSizeᵉ (elimGExp x cl e) ≡ syncSizeᵉ e
  syncSize-elimG x cl (input i)       = refl
  syncSize-elimG x cl (ofᵉ ts)        = cong suc (syncSize-elimGᵗˢ x cl ts)
  syncSize-elimG x cl emptyᵉ          = refl
  syncSize-elimG x cl (mapᵉ f e)      =
    cong suc (cong₂ _+_ (syncSize-elimGᵗ x cl f) (syncSize-elimG x cl e))
  syncSize-elimG x cl (takeᵉ c e)     =
    cong suc (cong₂ _+_ (syncSize-elimGᵗ x cl c) (syncSize-elimG x cl e))
  syncSize-elimG x cl (scanᵉ f z e)   =
    cong suc (cong₂ _+_ (cong₂ _+_ (syncSize-elimGᵗ x cl f)
                                   (syncSize-elimGᵗ x cl z))
                        (syncSize-elimG x cl e))
  syncSize-elimG x cl (mergeAllᵉ e)   = cong suc (syncSize-elimG x cl e)
  syncSize-elimG x cl (concatAllᵉ e)  = cong suc (syncSize-elimG x cl e)
  syncSize-elimG x cl (switchAllᵉ e)  = cong suc (syncSize-elimG x cl e)
  syncSize-elimG x cl (exhaustAllᵉ e) = cong suc (syncSize-elimG x cl e)
  syncSize-elimG x cl (μᵉ e)          = cong suc (syncSize-elimG (there x) cl e)
  syncSize-elimG x cl (varᵉ y)        = refl
  syncSize-elimG x cl (deferᵉ e)      = refl

  syncSize-elimGᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
    (cl : Closed Γ t) (f : Tm Γ Δᵍ Δ Θ u) →
    syncSizeᵗ (elimGTm x cl f) ≡ syncSizeᵗ f
  syncSize-elimGᵗ x cl (varᵗ y)      = refl
  syncSize-elimGᵗ x cl unit̂          = refl
  syncSize-elimGᵗ x cl (bool̂ b)      = refl
  syncSize-elimGᵗ x cl (nat̂ k)       = refl
  syncSize-elimGᵗ x cl (pairᵗ a b)   =
    cong suc (cong₂ _+_ (syncSize-elimGᵗ x cl a) (syncSize-elimGᵗ x cl b))
  syncSize-elimGᵗ x cl (fstᵗ p)      = cong suc (syncSize-elimGᵗ x cl p)
  syncSize-elimGᵗ x cl (sndᵗ p)      = cong suc (syncSize-elimGᵗ x cl p)
  syncSize-elimGᵗ x cl (inlᵗ a)      = cong suc (syncSize-elimGᵗ x cl a)
  syncSize-elimGᵗ x cl (inrᵗ a)      = cong suc (syncSize-elimGᵗ x cl a)
  syncSize-elimGᵗ x cl (caseᵗ s l r) =
    cong suc (cong₂ _+_ (cong₂ _+_ (syncSize-elimGᵗ x cl s)
                                   (syncSize-elimGᵗ x cl l))
                        (syncSize-elimGᵗ x cl r))
  syncSize-elimGᵗ x cl (ifᵗ c a b)   =
    cong suc (cong₂ _+_ (cong₂ _+_ (syncSize-elimGᵗ x cl c)
                                   (syncSize-elimGᵗ x cl a))
                        (syncSize-elimGᵗ x cl b))
  syncSize-elimGᵗ x cl (primᵗ op a)  = cong suc (syncSize-elimGᵗ x cl a)
  syncSize-elimGᵗ x cl (strmᵗ e)     = cong suc (syncSize-elimG x cl e)

  syncSize-elimGᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
    (cl : Closed Γ t) (ts : List (Tm Γ Δᵍ Δ Θ u)) →
    syncSizeᵗˢ (elimGTms x cl ts) ≡ syncSizeᵗˢ ts
  syncSize-elimGᵗˢ x cl []       = refl
  syncSize-elimGᵗˢ x cl (y ∷ ys) =
    cong₂ _+_ (syncSize-elimGᵗ x cl y) (syncSize-elimGᵗˢ x cl ys)

syncSize-unfoldμ : ∀ {n} {Γ : Ctx n} {t} (body : Exp Γ (t ∷ []) [] [] t) →
  syncSizeᵉ (unfoldμ body) ≡ syncSizeᵉ body
syncSize-unfoldμ body = syncSize-elimG (here refl) (μᵉ body) body

unfoldμ-shrinks : ∀ {n} {Γ : Ctx n} {t} (body : Exp Γ (t ∷ []) [] [] t) →
  syncSizeᵉ (unfoldμ body) < syncSizeᵉ (μᵉ body)
unfoldμ-shrinks body rewrite syncSize-unfoldμ body = ≤-refl

-- the SHELL mirrors: an unfold leaves the inner multiset untouched
-- (innerᵉ ignores defers entirely, and elimG substitutes only under
-- them) and shrinks the host shell by exactly the μ node — so the
-- walked expression's measure strictly DROPS across the μ edge
-- (unfoldμ-≺ below): the rank component never wobbles mid-walk.
shellSize-elimG : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
  (cl : Closed Γ t) (e : Exp Γ Δᵍ Δ Θ u) →
  shellSizeᵉ (elimGExp x cl e) ≡ shellSizeᵉ e
shellSize-elimG x cl (input i)       = refl
shellSize-elimG x cl (ofᵉ ts)        = refl
shellSize-elimG x cl emptyᵉ          = refl
shellSize-elimG x cl (mapᵉ f e)      = cong suc (shellSize-elimG x cl e)
shellSize-elimG x cl (takeᵉ c e)     = cong suc (shellSize-elimG x cl e)
shellSize-elimG x cl (scanᵉ f z e)   = cong suc (shellSize-elimG x cl e)
shellSize-elimG x cl (mergeAllᵉ e)   = cong suc (shellSize-elimG x cl e)
shellSize-elimG x cl (concatAllᵉ e)  = cong suc (shellSize-elimG x cl e)
shellSize-elimG x cl (switchAllᵉ e)  = cong suc (shellSize-elimG x cl e)
shellSize-elimG x cl (exhaustAllᵉ e) = cong suc (shellSize-elimG x cl e)
shellSize-elimG x cl (μᵉ e)          = cong suc (shellSize-elimG (there x) cl e)
shellSize-elimG x cl (varᵉ y)        = refl
shellSize-elimG x cl (deferᵉ e)      = refl

mutual
  inner-elimG : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
    (cl : Closed Γ t) (e : Exp Γ Δᵍ Δ Θ u) →
    innerᵉ (elimGExp x cl e) ≡ innerᵉ e
  inner-elimG x cl (input i)       = refl
  inner-elimG x cl (ofᵉ ts)        = inner-elimGᵗˢ x cl ts
  inner-elimG x cl emptyᵉ          = refl
  inner-elimG x cl (mapᵉ f e)      =
    cong₂ _++_ (inner-elimGᵗ x cl f) (inner-elimG x cl e)
  inner-elimG x cl (takeᵉ c e)     =
    cong₂ _++_ (inner-elimGᵗ x cl c) (inner-elimG x cl e)
  inner-elimG x cl (scanᵉ f z e)   =
    cong₂ _++_ (inner-elimGᵗ x cl f)
               (cong₂ _++_ (inner-elimGᵗ x cl z) (inner-elimG x cl e))
  inner-elimG x cl (mergeAllᵉ e)   = inner-elimG x cl e
  inner-elimG x cl (concatAllᵉ e)  = inner-elimG x cl e
  inner-elimG x cl (switchAllᵉ e)  = inner-elimG x cl e
  inner-elimG x cl (exhaustAllᵉ e) = inner-elimG x cl e
  inner-elimG x cl (μᵉ e)          = inner-elimG (there x) cl e
  inner-elimG x cl (varᵉ y)        = refl
  inner-elimG x cl (deferᵉ e)      = refl

  inner-elimGᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
    (cl : Closed Γ t) (f : Tm Γ Δᵍ Δ Θ u) →
    innerᵗ (elimGTm x cl f) ≡ innerᵗ f
  inner-elimGᵗ x cl (varᵗ y)      = refl
  inner-elimGᵗ x cl unit̂          = refl
  inner-elimGᵗ x cl (bool̂ b)      = refl
  inner-elimGᵗ x cl (nat̂ k)       = refl
  inner-elimGᵗ x cl (pairᵗ a b)   =
    cong₂ _++_ (inner-elimGᵗ x cl a) (inner-elimGᵗ x cl b)
  inner-elimGᵗ x cl (fstᵗ p)      = inner-elimGᵗ x cl p
  inner-elimGᵗ x cl (sndᵗ p)      = inner-elimGᵗ x cl p
  inner-elimGᵗ x cl (inlᵗ a)      = inner-elimGᵗ x cl a
  inner-elimGᵗ x cl (inrᵗ a)      = inner-elimGᵗ x cl a
  inner-elimGᵗ x cl (caseᵗ sc l r) =
    cong₂ _++_ (inner-elimGᵗ x cl sc)
               (cong₂ _++_ (inner-elimGᵗ x cl l) (inner-elimGᵗ x cl r))
  inner-elimGᵗ x cl (ifᵗ c a b)   =
    cong₂ _++_ (inner-elimGᵗ x cl c)
               (cong₂ _++_ (inner-elimGᵗ x cl a) (inner-elimGᵗ x cl b))
  inner-elimGᵗ x cl (primᵗ op a)  = inner-elimGᵗ x cl a
  inner-elimGᵗ x cl (strmᵗ e)     =
    cong₂ _∷_ (shellSize-elimG x cl e) (inner-elimG x cl e)

  inner-elimGᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
    (cl : Closed Γ t) (ts : List (Tm Γ Δᵍ Δ Θ u)) →
    innerᵗˢ (elimGTms x cl ts) ≡ innerᵗˢ ts
  inner-elimGᵗˢ x cl []       = refl
  inner-elimGᵗˢ x cl (y ∷ ys) =
    cong₂ _++_ (inner-elimGᵗ x cl y) (inner-elimGᵗˢ x cl ys)

shellSize-unfoldμ : ∀ {n} {Γ : Ctx n} {t} (body : Exp Γ (t ∷ []) [] [] t) →
  shellSizeᵉ (unfoldμ body) ≡ shellSizeᵉ body
shellSize-unfoldμ body = shellSize-elimG (here refl) (μᵉ body) body

inner-unfoldμ : ∀ {n} {Γ : Ctx n} {t} (body : Exp Γ (t ∷ []) [] [] t) →
  innerᵉ (unfoldμ body) ≡ innerᵉ body
inner-unfoldμ body = inner-elimG (here refl) (μᵉ body) body

------------------------------------------------------------------
-- the INIT leg: the initial machine satisfies the size invariant.
-- Provable exactly because the budget seeds from script CONTENT
-- (slotSize counts scripted values): every hot pending value is ≤
-- its slot's inputSize ≤ slotsSize ≤ the tower.
------------------------------------------------------------------

all-++-intro : ∀ {A : Set} (p : A → Bool) (xs ys : List A) →
  all p xs ≡ true → all p ys ≡ true → all p (xs ++ ys) ≡ true
all-++-intro p []       ys hx hy = hy
all-++-intro p (x ∷ xs) ys hx hy
  with ∧-true (p x) (all p xs) hx
... | px , pxs = ∧-intro px (all-++-intro p xs ys pxs hy)

all-concat-tab : ∀ {A : Set} (p : A → Bool) {m} (f : Fin m → List A) →
  (∀ i → all p (f i) ≡ true) → all p (concat (tabulate f)) ≡ true
all-concat-tab p {zero}  f h = refl
all-concat-tab p {suc m} f h =
  all-++-intro p (f Fin.zero) (concat (tabulate (λ i → f (Fin.suc i))))
               (h Fin.zero)
               (all-concat-tab p (λ i → f (Fin.suc i)) (λ i → h (Fin.suc i)))

fᵢ≤sum-tab : ∀ {m} (f : Fin m → ℕ) (i : Fin m) → f i ≤ sum (tabulate f)
fᵢ≤sum-tab {suc m} f Fin.zero    = m≤m+n (f Fin.zero) _
fᵢ≤sum-tab {suc m} f (Fin.suc i) =
  ≤-trans (fᵢ≤sum-tab (λ j → f (Fin.suc j)) i) (m≤n+m _ (f Fin.zero))

-- pending values of a resolved script stay under any bound that
-- covers the script's total content.  resolve only RETIMES, so this
-- holds for any per-value measure: the size face feeds boundedLive,
-- the fnCap face feeds fnCapLive
resolve-measure : ∀ {n} {Γ : Ctx n} {t : Ty} (f : Val Γ t → ℕ)
  (B : ℕ) (anchor : Tick) (xs : List (Timed (Val Γ t))) →
  sum (map (λ tv → f (Timed.val tv)) xs) ≤ B →
  all (λ p → f (proj₂ p) ≤ᵇ B) (resolve anchor xs) ≡ true
resolve-measure f B anchor [] h = refl
resolve-measure f B anchor ((after w , v) ∷ r) h =
  ∧-intro (T⇒≡true _ (≤⇒≤ᵇ (≤-trans (m≤m+n (f v) _) h)))
          (resolve-measure f B (anchor + suc w) r
            (≤-trans (m≤n+m _ (f v)) h))

resolve-bounded : ∀ {n} {Γ : Ctx n} {t : Ty} (B : ℕ) (anchor : Tick)
  (xs : List (Timed (Val Γ t))) →
  sum (map (λ tv → sizeᵛ t (Timed.val tv)) xs) ≤ B →
  all (λ p → sizeᵛ t (proj₂ p) ≤ᵇ B) (resolve anchor xs) ≡ true
resolve-bounded {t = t} = resolve-measure (sizeᵛ t)

mkHot-bounded : ∀ {n} {Γ : Ctx n} (ins : Slots Γ) (B : ℕ) (i : Fin n) →
  slotSize (ins i) ≤ B → all (boundedLive B) (mkHot ins i) ≡ true
mkHot-bounded ins B i h with ins i | h
... | scripted (hot async) | h′ =
      ∧-intro (resolve-bounded B 0 async (≤-trans (n≤1+n _) h′)) refl
... | scripted (cold _ _)  | _ = refl
... | shared _             | _ = refl

init-bounded : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ)
  (id : Id) → stBounded? (sizeBudgetAt e ins id) (sched-init e ins)
                         (st-init e) ≡ true
init-bounded {n = n} e ins id =
  ∧-intro (all-concat-tab (boundedLive B) (mkHot ins) perSlot) refl
  where
  B = sizeBudgetAt e ins id
  perSlot : ∀ i → all (boundedLive B) (mkHot ins i) ≡ true
  perSlot i = mkHot-bounded ins B i
                (≤-trans (fᵢ≤sum-tab (λ j → slotSize (ins j)) i)
                         (slots≤budget e ins id))

------------------------------------------------------------------
-- EDGE 1 — the connect latch, counted.  subscribeSharedSlot's
-- connect fires only behind memberSource … ≡ false and prepends to
-- connectedShares, which no machine function ever shrinks; so the
-- number of still-unconnected shared slots is the edge-1 component
-- of the demand: it strictly drops at every connect (unconn-insert)
-- and never rises (unconn-cons-≤).
------------------------------------------------------------------

unconnAt : ∀ {n} {Γ : Ctx n} → Slots Γ → List Source → Fin n → ℕ
unconnAt sl cs i with sl i
... | shared _   = if memberSource (toℕ i) cs then 0 else 1
... | scripted _ = 0

unconn : ∀ {n} {Γ : Ctx n} → Slots Γ → List Source → ℕ
unconn sl cs = sum (tabulate (unconnAt sl cs))

-- pointwise sums over Fin n
sum-tab-mono : ∀ {m} (f g : Fin m → ℕ) → (∀ i → f i ≤ g i) →
  sum (tabulate f) ≤ sum (tabulate g)
sum-tab-mono {zero}  f g h = z≤n
sum-tab-mono {suc m} f g h =
  +-mono-≤ (h Fin.zero) (sum-tab-mono _ _ (λ i → h (Fin.suc i)))

sum-tab-strict : ∀ {m} (f g : Fin m → ℕ) → (∀ j → f j ≤ g j) →
  (i : Fin m) → f i < g i → sum (tabulate f) < sum (tabulate g)
sum-tab-strict {suc m} f g h Fin.zero    fi<gi =
  +-mono-<-≤ fi<gi (sum-tab-mono _ _ (λ j → h (Fin.suc j)))
sum-tab-strict {suc m} f g h (Fin.suc i) fi<gi =
  +-mono-≤-< (h Fin.zero) (sum-tab-strict _ _ (λ j → h (Fin.suc j)) i fi<gi)

-- adding a member never raises any slot's contribution
unconnAt-cons-≤ : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source)
  (s : Source) (i : Fin n) → unconnAt sl (s ∷ cs) i ≤ unconnAt sl cs i
unconnAt-cons-≤ sl cs s i with sl i
... | scripted _ = z≤n
... | shared _ with memberSource (toℕ i) cs
...   | true  rewrite ∨-zeroʳ (sameSource (toℕ i) s) = z≤n
...   | false with sameSource (toℕ i) s ∨ false
...     | true  = z≤n
...     | false = ≤-refl

unconn-cons-≤ : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source)
  (s : Source) → unconn sl (s ∷ cs) ≤ unconn sl cs
unconn-cons-≤ sl cs s =
  sum-tab-mono _ _ (unconnAt-cons-≤ sl cs s)

f≡t-absurd : ∀ {A : Set} → false ≡ true → A
f≡t-absurd ()

-- unconn is ANTITONE in the connected set: connecting more can only
-- lower the count.  Paired with subscribeE-connected-mono this is what
-- carries unconn-insert's strict drop across the def's own walk, so the
-- connect edge's payment survives everything the def does on its way up
unconnAt-antitone : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs cs′ : List Source)
  (i : Fin n) →
  (memberSource (toℕ i) cs ≡ true → memberSource (toℕ i) cs′ ≡ true) →
  unconnAt sl cs′ i ≤ unconnAt sl cs i
unconnAt-antitone sl cs cs′ i h with sl i
... | scripted _ = z≤n
... | shared _ with memberSource (toℕ i) cs′ | memberSource (toℕ i) cs | h
...   | true  | _     | _  = z≤n
...   | false | false | _  = ≤-refl
...   | false | true  | h′ = f≡t-absurd (h′ refl)

unconn-antitone : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs cs′ : List Source) →
  (∀ s → memberSource s cs ≡ true → memberSource s cs′ ≡ true) →
  unconn sl cs′ ≤ unconn sl cs
unconn-antitone sl cs cs′ mono =
  sum-tab-mono (unconnAt sl cs′) (unconnAt sl cs)
    (λ i → unconnAt-antitone sl cs cs′ i (mono (toℕ i)))

-- connecting a fresh share strictly drops the count: its own slot
-- goes 1 → 0 and no other slot rises
unconn-insert : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source)
  (i : Fin n) {d : Closed Γ (lookup Γ i)} → sl i ≡ shared d →
  memberSource (toℕ i) cs ≡ false →
  unconn sl (toℕ i ∷ cs) < unconn sl cs
unconn-insert sl cs i eqi fresh =
  sum-tab-strict _ _ (unconnAt-cons-≤ sl cs (toℕ i)) i strict
  where
  strict : unconnAt sl (toℕ i ∷ cs) i < unconnAt sl cs i
  strict rewrite eqi | fresh
               | T⇒≡true (toℕ i ≡ᵇ toℕ i) (≡⇒≡ᵇ (toℕ i) (toℕ i) refl)
               = s≤s z≤n

-- U is syntactically owned: every unconnected slot contributes at
-- most its own slot size (a shared slot's def is nonempty syntax),
-- so the connect count sits under the program's slot content — the
-- U ≤ sz leg of the seed inequality
sizeᵉ-pos : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (e : Exp Γ Δᵍ Δ Θ t) →
  1 ≤ sizeᵉ e
sizeᵉ-pos (input i)       = s≤s z≤n
sizeᵉ-pos (ofᵉ ts)        = s≤s z≤n
sizeᵉ-pos emptyᵉ          = s≤s z≤n
sizeᵉ-pos (mapᵉ f e)      = s≤s z≤n
sizeᵉ-pos (takeᵉ c e)     = s≤s z≤n
sizeᵉ-pos (scanᵉ f z e)   = s≤s z≤n
sizeᵉ-pos (mergeAllᵉ e)   = s≤s z≤n
sizeᵉ-pos (concatAllᵉ e)  = s≤s z≤n
sizeᵉ-pos (switchAllᵉ e)  = s≤s z≤n
sizeᵉ-pos (exhaustAllᵉ e) = s≤s z≤n
sizeᵉ-pos (μᵉ e)          = s≤s z≤n
sizeᵉ-pos (varᵉ x)        = s≤s z≤n
sizeᵉ-pos (deferᵉ e)      = s≤s z≤n

unconnAt≤slot : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source)
  (i : Fin n) → unconnAt sl cs i ≤ slotSize (sl i)
unconnAt≤slot sl cs i with sl i
... | scripted s = z≤n
... | shared d with memberSource (toℕ i) cs
...   | true  = z≤n
...   | false = sizeᵉ-pos d

unconn≤slots : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source) →
  unconn sl cs ≤ slotsSize sl
unconn≤slots sl cs = sum-tab-mono _ _ (unconnAt≤slot sl cs)


------------------------------------------------------------------
-- RANK — the ≺ᵛ order collapsed to ℕ.  Sync fuel is DEPTH-consumed
-- (siblings share the remaining gas; only nested decrement edges
-- stack), so the contract needs to bound the deepest decrement
-- chain, and with the entry sum bounded by V a count vector IS a
-- base-(suc V) numeral (high class = high digit): any ≺ᵛ step
-- strictly decreases its numeric value (rank-mono-≺).  The wet
-- contract therefore inducts on this plain ℕ — no Acc plumbing —
-- converting hop decreases (≺-embed/≺-replace) via rank-mono-≺,
-- and discharging the entry-sum side condition via totᵛ-counts
-- (the sum is the shell count, ≤ sizeᵉ by shells-len — free on
-- stBounded?).
------------------------------------------------------------------

totᵛ : ∀ {m} → Vec ℕ m → ℕ
totᵛ []ᵛ       = 0
totᵛ (x ∷ᵛ xs) = x + totᵛ xs

rank : ∀ {m} (V : ℕ) → Vec ℕ m → ℕ
rank           V []ᵛ       = 0
rank {suc m}   V (x ∷ᵛ xs) = x * (suc V) ^ m + rank V xs

-- a bounded-sum vector reads below the next power (the carry bound)
rank-lt-pow : ∀ {m} (V : ℕ) (c : Vec ℕ m) →
  totᵛ c ≤ V → rank V c < (suc V) ^ m
rank-lt-pow {zero}  V []ᵛ       h = s≤s z≤n
rank-lt-pow {suc m} V (x ∷ᵛ xs) h =
  <-≤-trans (subst (x * (suc V) ^ m + rank V xs <_)
                   (+-comm (x * (suc V) ^ m) ((suc V) ^ m))
                   (+-monoʳ-< (x * (suc V) ^ m)
                      (rank-lt-pow V xs (≤-trans (m≤n+m (totᵛ xs) x) h))))
            (*-monoˡ-≤ ((suc V) ^ m)
               (s≤s (≤-trans (m≤m+n x (totᵛ xs)) h)))

-- THE BRIDGE: a ≺ᵛ step on a bounded-sum vector is a numeral decrease
rank-mono-≺ : ∀ {m} (V : ℕ) {c′ c : Vec ℕ m} →
  c′ ≺ᵛ c → totᵛ c′ ≤ V → rank V c′ < rank V c
rank-mono-≺ V (≺-here {m} {x} {y} {xs} {ys} x<y) tot≤V =
  <-≤-trans (subst (x * (suc V) ^ m + rank V xs <_)
                   (+-comm (x * (suc V) ^ m) ((suc V) ^ m))
                   (+-monoʳ-< (x * (suc V) ^ m)
                      (rank-lt-pow V xs (≤-trans (m≤n+m (totᵛ xs) x) tot≤V))))
            (≤-trans (*-monoˡ-≤ ((suc V) ^ m) x<y)
                     (m≤m+n (y * (suc V) ^ m) (rank V ys)))
rank-mono-≺ V (≺-there {m} {x} {xs} {ys} xs≺ys) tot≤V =
  +-monoʳ-< (x * (suc V) ^ m)
            (rank-mono-≺ V xs≺ys (≤-trans (m≤n+m (totᵛ xs) x) tot≤V))

-- the entry-sum of a count vector is the multiset's cardinality
totᵛ-⊕ᵛ : ∀ {m} (a b : Vec ℕ m) → totᵛ (a ⊕ᵛ b) ≡ totᵛ a + totᵛ b
totᵛ-⊕ᵛ []ᵛ       []ᵛ       = refl
totᵛ-⊕ᵛ (x ∷ᵛ xs) (y ∷ᵛ ys)
  rewrite totᵛ-⊕ᵛ xs ys
        | +-assoc x y (totᵛ xs + totᵛ ys)
        | sym (+-assoc y (totᵛ xs) (totᵛ ys))
        | +-comm y (totᵛ xs)
        | +-assoc (totᵛ xs) y (totᵛ ys)
        | sym (+-assoc x (totᵛ xs) (y + totᵛ ys)) = refl

totᵛ-zeros : ∀ {m} → totᵛ (zerosᵛ {m}) ≡ 0
totᵛ-zeros {zero}  = refl
totᵛ-zeros {suc m} = totᵛ-zeros {m}

totᵛ-oneAt : ∀ B x → totᵛ (oneAt B x) ≡ 1
totᵛ-oneAt zero    x = refl
totᵛ-oneAt (suc B) x with suc B ≤ᵇ x
... | true  = cong suc (totᵛ-zeros {suc B})
... | false = totᵛ-oneAt B x

totᵛ-counts : ∀ B (M : List ℕ) → totᵛ (counts B M) ≡ length M
totᵛ-counts B []      = totᵛ-zeros {suc B}
totᵛ-counts B (x ∷ M)
  rewrite totᵛ-⊕ᵛ (oneAt B x) (counts B M)
        | totᵛ-oneAt B x
        | totᵛ-counts B M = refl

-- a factor of at least one never shrinks
1*≤ : ∀ (x k : ℕ) → 1 ≤ k → x ≤ k * x
1*≤ x k h = ≤-trans (≤-reflexive (sym (+-identityʳ x))) (*-monoˡ-≤ x h)

1≤pow : ∀ (b k : ℕ) → 1 ≤ suc b ^ k
1≤pow b zero    = ≤-refl
1≤pow b (suc k) = ≤-trans (1≤pow b k) (m≤m+n _ _)

------------------------------------------------------------------
-- THE HOP RANK CAP — dBound's R, now that `r` is hopD.
--
-- R exists for ONE edge: dBound-connect resets r to the connected
-- def's, and demands r′ ≤ R.  A def is fixed slot content, so this
-- is a cap on hopD over STORE-SIZED expressions and nothing more.
--
-- hopD's scanᵉ clause pays (2 + pm f)^V at every node, where pm is the
-- plug MULTIPLIER (Rx.Hop-Depth) rather than an occurrence count.  A
-- count would be ≤ s and the cap would be (2+s)^(V·s), one polynomial
-- above the retired rank's (1+V)^(1+V).  A multiplier is not bounded by
-- s: pm's own scanᵉ clause is (2 + pm f)^V, so each nesting level of
-- scanᵉ multiplies the exponent by V instead of adding to it, and d
-- nested scans give V^d.  With d ≤ s the cap is (2+s)^(V′^s), and at
-- s ≤ V that is hopR V = (2+V)^((1+V)^(1+V)) — an EXPONENTIAL exponent
-- where the count gave a polynomial one.
--
-- prod≤3pow below still absorbs it inside the SAME three exponential
-- stories.  Its slack identity closes on (V+2)^(V+3) where the
-- polynomial version closed on (V+2)³, and its side condition is
-- (V+2)² ≤ 2^V (true from V ≥ 6) where that one wanted 3V ≤ 2^V (true
-- from 4).  THE BUDGET TOWER DOES NOT MOVE: V is a tower of 2s of
-- height (4+sz)(1+id) ≥ 2^65536, and a tower cannot notice the
-- difference between a polynomial and an exponential in an exponent —
-- both vanish into the first story.
------------------------------------------------------------------

hopR : ℕ → ℕ
hopR V = (2 + V) ^ (suc V ^ suc V)

-- (P1) hopD is bounded by SIZE.  The exponent is V′^s, not V′·s, and
-- that is forced: the coefficient is a MULTIPLIER (pm), not an
-- occurrence count, so it is not bounded by s.  pm's own scanᵉ clause
-- is (2 + pm f)^V, so each nesting level of scanᵉ raises the exponent
-- by a FACTOR of V rather than adding one — d nested scans give V^d.
-- With d ≤ s that is V′^s.  Under the retired occurrence count the
-- coefficient WAS ≤ s and the bound was (2+s)^(V′·s); that statement
-- is false for pm and has been retracted rather than left standing.
--
-- WHAT THE INDUCTION NEEDS, worked out 2026-07-29 and written down
-- because the shape is not the obvious one.  The statement must be
-- JOINT — the same bound for pm, since hopD's clauses read pm for
-- their coefficients — and then, with P(s) = (2+s)^(V′^s):
--
--   mapᵉ    P(s₁) + P(s₁)·P(s₂)      ≤ P(s)   via 3·V′^(s-1) ≤ V′^s
--   *Allᵉ   suc (P(s-1))             ≤ P(s)
--   ofᵉ/⊔   each child under P of the whole, by monotonicity
--   scanᵉ   (2 + P(s₁))^V · 3·P(s-1) ≤ P(s)
--
-- The scanᵉ clause is the one with a trap.  Bounding (2+B)^V by B^(2V)
-- — the obvious move — is too lossy: it wants 2V+2 ≤ V′, the induction
-- does not close, and it reads at first like the STATEMENT being
-- false.  It is not.  The slack is in the CHILD SIZES: a scanᵉ has
-- three children each of size ≥ 1, so the step function's own size is
-- s₁ ≤ s-3 and its bound's exponent is V′^(s-3) — a factor V′² below
-- the clause's budget.  That is what pays for the (2+·)^V and the
-- constant 3.  A proof that does not track WHICH child's size it is
-- using will appear to fail.
--
-- Nothing here is tight, and V is a tower, so the side conditions
-- (V ≥ 2, sizes ≥ 1) are free at every call site — hopD-cap's premise
-- sizeᵉ e ≤ V already gives V ≥ 1, since every expression has size ≥ 1.

-- the pm leaf is 0 or 1 either way
ifLe1 : ∀ (a b : ℕ) → (if a ≡ᵇ b then 1 else 0) ≤ 1
ifLe1 a b with a ≡ᵇ b
... | true  = ≤-refl
... | false = z≤n

-- OPAQUE on purpose.  Everything below states bounds in terms of szB
-- and never needs its definition; leaving it transparent makes Agda try
-- to invert `^` to solve the monotonicity lemmas' implicit sizes, which
-- costs an inversion-depth warning per clause and then fails outright.
-- Only the two places that genuinely compare szB against hopR unfold it.
opaque
  szB : ℕ → ℕ → ℕ
  szB V s = (2 + s) ^ (suc V ^ s)

  szB-mono : ∀ (V : ℕ) {s s′ : ℕ} → s ≤ s′ → szB V s ≤ szB V s′
  szB-mono V {s} {s′} h =
    ≤-trans (^-monoˡ-≤ (suc V ^ s) (+-monoʳ-≤ 2 h))
            (^-monoʳ-≤ (2 + s′) (^-monoʳ-≤ (suc V) h))

  1≤szB : ∀ (V s : ℕ) → 1 ≤ szB V s
  1≤szB V s = 1≤pow (suc s) (suc V ^ s)

-- every expression and term has at least one node
1≤sizeᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (e : Exp Γ Δᵍ Δ Θ t) → 1 ≤ sizeᵉ e
1≤sizeᵉ (input i)       = ≤-refl
1≤sizeᵉ (ofᵉ ts)        = s≤s z≤n
1≤sizeᵉ emptyᵉ          = ≤-refl
1≤sizeᵉ (mapᵉ f e)      = s≤s z≤n
1≤sizeᵉ (takeᵉ c e)     = s≤s z≤n
1≤sizeᵉ (scanᵉ f z e)   = s≤s z≤n
1≤sizeᵉ (mergeAllᵉ e)   = s≤s z≤n
1≤sizeᵉ (concatAllᵉ e)  = s≤s z≤n
1≤sizeᵉ (switchAllᵉ e)  = s≤s z≤n
1≤sizeᵉ (exhaustAllᵉ e) = s≤s z≤n
1≤sizeᵉ (μᵉ e)          = s≤s z≤n
1≤sizeᵉ (varᵉ x)        = ≤-refl
1≤sizeᵉ (deferᵉ e)      = s≤s z≤n

1≤sizeᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (tm : Tm Γ Δᵍ Δ Θ t) → 1 ≤ sizeᵗ tm
1≤sizeᵗ (varᵗ x)      = ≤-refl
1≤sizeᵗ unit̂          = ≤-refl
1≤sizeᵗ (bool̂ _)      = ≤-refl
1≤sizeᵗ (nat̂ _)       = ≤-refl
1≤sizeᵗ (pairᵗ a b)   = s≤s z≤n
1≤sizeᵗ (fstᵗ q)      = s≤s z≤n
1≤sizeᵗ (sndᵗ q)      = s≤s z≤n
1≤sizeᵗ (inlᵗ a)      = s≤s z≤n
1≤sizeᵗ (inrᵗ a)      = s≤s z≤n
1≤sizeᵗ (caseᵗ sc l r) = s≤s z≤n
1≤sizeᵗ (ifᵗ c a b)   = s≤s z≤n
1≤sizeᵗ (primᵗ _ a)   = s≤s z≤n
1≤sizeᵗ (strmᵗ e)     = s≤s z≤n

1≤sizeᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (ts : List (Tm Γ Δᵍ Δ Θ t)) →
  1 ≤ sizeᵗˢ ts
1≤sizeᵗˢ []       = ≤-refl
1≤sizeᵗˢ (y ∷ ys) = ≤-trans (1≤sizeᵗ y) (m≤m+n (sizeᵗ y) (sizeᵗˢ ys))

-- THE THREE ARITHMETIC FACTS the clauses reduce to.  Each is a
-- statement about ℕ and `^` alone — no syntax, no measure — which is
-- what leaves the induction below with no arithmetic in it at all.
opaque
  unfolding szB

  -- a base of at least 1 is under any of its powers
  x≤x^ : ∀ (x k : ℕ) → 1 ≤ k → suc x ≤ suc x ^ k
  x≤x^ x k hk =
    ≤-trans (≤-reflexive (sym (*-identityʳ (suc x)))) (^-monoʳ-≤ (suc x) hk)

  3≤szB : ∀ (V p : ℕ) → 1 ≤ p → 3 ≤ szB V p
  3≤szB V p hp =
    ≤-trans (+-monoʳ-≤ 2 hp) (x≤x^ (suc p) (suc V ^ p) (1≤pow V p))

  -- B + B ≤ B · B, the step every clause starts from
  dbl≤sq : ∀ (V p : ℕ) → 1 ≤ p → szB V p + szB V p ≤ szB V p * szB V p
  dbl≤sq V p hp =
    ≤-trans (≤-reflexive (cong (szB V p +_) (sym (+-identityʳ (szB V p)))))
            (*-monoˡ-≤ (szB V p) (≤-trans (≤ᵇ⇒≤ 2 3 tt) (3≤szB V p hp)))

  -- and the exponent side: k copies of W^p sit under W^(suc p) as soon
  -- as k ≤ W.  This is where V ≥ 2 is spent — the szB-sq clause needs
  -- three copies, so it needs 3 ≤ suc V
  pow-step : ∀ (V p k : ℕ) → k ≤ suc V → k * (suc V ^ p) ≤ suc V ^ suc p
  pow-step V p k h = *-monoˡ-≤ (suc V ^ p) h

  szB-suc : ∀ (V p : ℕ) → 2 ≤ V → 1 ≤ p →
    suc (szB V p) ≤ szB V (suc p)
  szB-suc V p hV hp =
    ≤-trans (+-monoˡ-≤ B (1≤szB V p))
    (≤-trans (dbl≤sq V p hp)
    (≤-trans (≤-reflexive (sym (^-distribˡ-+-* (2 + p) (suc V ^ p) (suc V ^ p))))
    (≤-trans (^-monoˡ-≤ (suc V ^ p + suc V ^ p) (n≤1+n (2 + p)))
             (^-monoʳ-≤ (3 + p) two))))
    where
    B : ℕ
    B = (2 + p) ^ (suc V ^ p)
    two : suc V ^ p + suc V ^ p ≤ suc V ^ suc p
    two = ≤-trans (≤-reflexive (cong (suc V ^ p +_)
                                     (sym (+-identityʳ (suc V ^ p)))))
                  (pow-step V p 2 (≤-trans (≤ᵇ⇒≤ 2 3 tt) (s≤s hV)))

  szB-sq : ∀ (V p : ℕ) → 2 ≤ V → 1 ≤ p →
    szB V p + szB V p * szB V p ≤ szB V (suc p)
  szB-sq V p hV hp =
    ≤-trans (+-monoˡ-≤ (B * B) (1*≤ B B (1≤szB V p)))
    (≤-trans (≤-trans (≤-reflexive (cong (B * B +_) (sym (+-identityʳ (B * B)))))
                      (*-monoˡ-≤ (B * B) (≤-trans (≤ᵇ⇒≤ 2 3 tt) (3≤szB V p hp))))
    (≤-trans (≤-reflexive
               (trans (cong (B *_)
                        (sym (^-distribˡ-+-* (2 + p) (suc V ^ p) (suc V ^ p))))
                      (sym (^-distribˡ-+-* (2 + p) (suc V ^ p)
                                           (suc V ^ p + suc V ^ p)))))
    (≤-trans (^-monoˡ-≤ (suc V ^ p + (suc V ^ p + suc V ^ p)) (n≤1+n (2 + p)))
             (^-monoʳ-≤ (3 + p) three))))
    where
    B : ℕ
    B = (2 + p) ^ (suc V ^ p)
    three : suc V ^ p + (suc V ^ p + suc V ^ p) ≤ suc V ^ suc p
    three = ≤-trans (≤-reflexive (cong (λ z → suc V ^ p + (suc V ^ p + z))
                                       (sym (+-identityʳ (suc V ^ p)))))
                    (pow-step V p 3 (s≤s hV))

  -- THE REFOLD, and the one place the child sizes matter.  The step
  -- function's own size is s₁, and the scanᵉ's other two children cost
  -- at least 1 each, so s₁ + 2 ≤ p.  That is a factor (suc V)² of slack
  -- in the exponent, and it is exactly what pays for the (2+·)^V and
  -- the three copies.  Bounding (2 + B₁)^V by B₁^(2V) WITHOUT it wants
  -- 2V + 2 ≤ suc V and the chain does not close.
  szB-scan : ∀ (V s₁ s₂ s₃ : ℕ) → 2 ≤ V → 1 ≤ s₁ → 1 ≤ s₂ → 1 ≤ s₃ →
    (2 + szB V s₁) ^ V
      * (szB V (s₁ + s₂ + s₃) + szB V (s₁ + s₂ + s₃) + szB V (s₁ + s₂ + s₃))
    ≤ szB V (suc (s₁ + s₂ + s₃))
  szB-scan V s₁ s₂ s₃ hV h₁ h₂ h₃ =
    ≤-trans (*-mono-≤ powBound triple)
    (≤-trans (≤-reflexive (sym (^-distribˡ-+-* (2 + p)
                                 ((suc V ^ s₁ + suc V ^ s₁) * V)
                                 (suc V ^ p + suc V ^ p))))
    (≤-trans (^-monoˡ-≤ ((suc V ^ s₁ + suc V ^ s₁) * V
                          + (suc V ^ p + suc V ^ p))
                        (n≤1+n (2 + p)))
             (^-monoʳ-≤ (3 + p) expo)))
    where
    p : ℕ
    p  = s₁ + s₂ + s₃
    1≤p : 1 ≤ p
    1≤p = ≤-trans h₁ (≤-trans (m≤m+n s₁ s₂) (m≤m+n (s₁ + s₂) s₃))
    s₁≤p : s₁ ≤ p
    s₁≤p = ≤-trans (m≤m+n s₁ s₂) (m≤m+n (s₁ + s₂) s₃)
    s₁+2≤p : s₁ + 2 ≤ p
    s₁+2≤p = ≤-trans (+-monoʳ-≤ s₁ (+-mono-≤ h₂ h₃))
                     (≤-reflexive (sym (+-assoc s₁ s₂ s₃)))
    -- (2 + B₁)^V, flattened into the shared base without ever needing
    -- (x·y)^n — the step goes through ^-*-assoc instead
    powBound : (2 + szB V s₁) ^ V
             ≤ (2 + p) ^ ((suc V ^ s₁ + suc V ^ s₁) * V)
    powBound =
      ≤-trans (^-monoˡ-≤ V
                (≤-trans (≤-trans (+-monoˡ-≤ (szB V s₁)
                            (≤-trans (≤ᵇ⇒≤ 2 3 tt) (3≤szB V s₁ h₁)))
                                  (dbl≤sq V s₁ h₁))
                         (≤-reflexive
                           (sym (^-distribˡ-+-* (2 + s₁) (suc V ^ s₁)
                                                (suc V ^ s₁))))))
      (≤-trans (≤-reflexive (^-*-assoc (2 + s₁) (suc V ^ s₁ + suc V ^ s₁) V))
               (^-monoˡ-≤ ((suc V ^ s₁ + suc V ^ s₁) * V) (+-monoʳ-≤ 2 s₁≤p)))
    mul3 : ∀ (b : ℕ) → b + b + b ≡ 3 * b
    mul3 = solve 1 (λ b → b :+ b :+ b := con 3 :* b) refl
    triple : szB V p + szB V p + szB V p ≤ (2 + p) ^ (suc V ^ p + suc V ^ p)
    triple =
      ≤-trans (≤-reflexive (mul3 (szB V p)))
      (≤-trans (*-monoˡ-≤ (szB V p) (3≤szB V p 1≤p))
               (≤-reflexive
                 (sym (^-distribˡ-+-* (2 + p) (suc V ^ p) (suc V ^ p)))))
    2V≤W² : V + V ≤ suc V * suc V
    2V≤W² = ≤-trans (+-mono-≤ (n≤1+n V) (n≤1+n V))
                    (≤-trans (≤-reflexive (cong (suc V +_)
                                            (sym (+-identityʳ (suc V)))))
                             (*-monoˡ-≤ (suc V) (≤-trans hV (n≤1+n V))))
    swap2 : ∀ (a v : ℕ) → (a + a) * v ≡ a * (v + v)
    swap2 = solve 2 (λ a v → (a :+ a) :* v := a :* (v :+ v)) refl
    -- 2V ≤ (suc V)², so the step function's exponent fits in the two
    -- extra stories that s₁ + 2 ≤ p supplies
    head≤ : (suc V ^ s₁ + suc V ^ s₁) * V ≤ suc V ^ p
    head≤ =
      ≤-trans (≤-reflexive (swap2 (suc V ^ s₁) V))
      (≤-trans (*-monoʳ-≤ (suc V ^ s₁) 2V≤W²)
      (≤-trans (≤-reflexive (cong (suc V ^ s₁ *_)
                              (cong (suc V *_) (sym (*-identityʳ (suc V))))))
      (≤-trans (≤-reflexive (sym (^-distribˡ-+-* (suc V) s₁ 2)))
               (^-monoʳ-≤ (suc V) s₁+2≤p))))
    expo : (suc V ^ s₁ + suc V ^ s₁) * V + (suc V ^ p + suc V ^ p)
         ≤ suc V ^ suc p
    expo =
      ≤-trans (+-monoˡ-≤ (suc V ^ p + suc V ^ p) head≤)
              (≤-trans (≤-reflexive (cong (λ z → suc V ^ p + (suc V ^ p + z))
                                          (sym (+-identityʳ (suc V ^ p)))))
                       (pow-step V p 3 (s≤s hV)))

-- THE INDUCTION, joint in hopD and pm because hopD's clauses read pm
-- for their coefficients.  Every clause is monotonicity plus one of the
-- three facts above.
mutual
  hopD-sizeᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (V : ℕ) (e : Exp Γ Δᵍ Δ Θ t) →
    2 ≤ V → hopDᵉ V e ≤ szB V (sizeᵉ e)
  hopD-sizeᵉ V (input i) hV = z≤n
  hopD-sizeᵉ V (ofᵉ ts)  hV =
    ≤-trans (hopD-sizeᵗˢ V ts hV) (szB-mono V (n≤1+n (sizeᵗˢ ts)))
  hopD-sizeᵉ V emptyᵉ    hV = z≤n
  hopD-sizeᵉ V (mapᵉ f e) hV =
    ≤-trans (+-mono-≤ (≤-trans (hopD-sizeᵗ V f hV)
                               (szB-mono V (m≤m+n (sizeᵗ f) (sizeᵉ e))))
                      (*-mono-≤ (⊔-lub (≤-trans (pm-sizeᵗ V 0 f hV)
                                                (szB-mono V (m≤m+n _ _)))
                                       (1≤szB V _))
                                (≤-trans (hopD-sizeᵉ V e hV)
                                         (szB-mono V (m≤n+m (sizeᵉ e) (sizeᵗ f))))))
            (szB-sq V (sizeᵗ f + sizeᵉ e) hV
              (≤-trans (1≤sizeᵗ f) (m≤m+n (sizeᵗ f) (sizeᵉ e))))
  hopD-sizeᵉ V (takeᵉ c e) hV =
    ≤-trans (hopD-sizeᵉ V e hV)
            (szB-mono V (≤-trans (m≤n+m (sizeᵉ e) (sizeᵗ c))
                                 (n≤1+n (sizeᵗ c + sizeᵉ e))))
  hopD-sizeᵉ V (scanᵉ f z e) hV =
    ≤-trans (*-mono-≤ (^-monoˡ-≤ V (+-monoʳ-≤ 2 (pm-sizeᵗ V 0 f hV)))
              (+-mono-≤ (+-mono-≤ (≤-trans (hopD-sizeᵗ V f hV) (szB-mono V lef))
                                  (≤-trans (hopD-sizeᵗ V z hV) (szB-mono V lez)))
                        (≤-trans (hopD-sizeᵉ V e hV) (szB-mono V lee))))
            (szB-scan V (sizeᵗ f) (sizeᵗ z) (sizeᵉ e) hV
                      (1≤sizeᵗ f) (1≤sizeᵗ z) (1≤sizeᵉ e))
    where
    lef : sizeᵗ f ≤ sizeᵗ f + sizeᵗ z + sizeᵉ e
    lef = ≤-trans (m≤m+n (sizeᵗ f) (sizeᵗ z)) (m≤m+n _ (sizeᵉ e))
    lez : sizeᵗ z ≤ sizeᵗ f + sizeᵗ z + sizeᵉ e
    lez = ≤-trans (m≤n+m (sizeᵗ z) (sizeᵗ f)) (m≤m+n _ (sizeᵉ e))
    lee : sizeᵉ e ≤ sizeᵗ f + sizeᵗ z + sizeᵉ e
    lee = m≤n+m (sizeᵉ e) (sizeᵗ f + sizeᵗ z)
  hopD-sizeᵉ V (mergeAllᵉ e) hV =
    ≤-trans (s≤s (hopD-sizeᵉ V e hV)) (szB-suc V (sizeᵉ e) hV (1≤sizeᵉ e))
  hopD-sizeᵉ V (concatAllᵉ e) hV =
    ≤-trans (s≤s (hopD-sizeᵉ V e hV)) (szB-suc V (sizeᵉ e) hV (1≤sizeᵉ e))
  hopD-sizeᵉ V (switchAllᵉ e) hV =
    ≤-trans (s≤s (hopD-sizeᵉ V e hV)) (szB-suc V (sizeᵉ e) hV (1≤sizeᵉ e))
  hopD-sizeᵉ V (exhaustAllᵉ e) hV =
    ≤-trans (s≤s (hopD-sizeᵉ V e hV)) (szB-suc V (sizeᵉ e) hV (1≤sizeᵉ e))
  hopD-sizeᵉ V (μᵉ e)     hV =
    ≤-trans (hopD-sizeᵉ V e hV) (szB-mono V (n≤1+n (sizeᵉ e)))
  hopD-sizeᵉ V (varᵉ x)   hV = z≤n
  hopD-sizeᵉ V (deferᵉ e) hV = z≤n

  hopD-sizeᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (V : ℕ) (tm : Tm Γ Δᵍ Δ Θ t) →
    2 ≤ V → hopDᵗ V tm ≤ szB V (sizeᵗ tm)
  hopD-sizeᵗ V (varᵗ x) hV = z≤n
  hopD-sizeᵗ V unit̂     hV = z≤n
  hopD-sizeᵗ V (bool̂ _) hV = z≤n
  hopD-sizeᵗ V (nat̂ _)  hV = z≤n
  hopD-sizeᵗ V (pairᵗ a b) hV =
    ⊔-lub (≤-trans (hopD-sizeᵗ V a hV)
             (szB-mono V (≤-trans (m≤m+n (sizeᵗ a) (sizeᵗ b))
                                  (n≤1+n (sizeᵗ a + sizeᵗ b)))))
          (≤-trans (hopD-sizeᵗ V b hV)
             (szB-mono V (≤-trans (m≤n+m (sizeᵗ b) (sizeᵗ a))
                                  (n≤1+n (sizeᵗ a + sizeᵗ b)))))
  hopD-sizeᵗ V (fstᵗ q) hV =
    ≤-trans (hopD-sizeᵗ V q hV) (szB-mono V (n≤1+n (sizeᵗ q)))
  hopD-sizeᵗ V (sndᵗ q) hV =
    ≤-trans (hopD-sizeᵗ V q hV) (szB-mono V (n≤1+n (sizeᵗ q)))
  hopD-sizeᵗ V (inlᵗ a) hV =
    ≤-trans (hopD-sizeᵗ V a hV) (szB-mono V (n≤1+n (sizeᵗ a)))
  hopD-sizeᵗ V (inrᵗ a) hV =
    ≤-trans (hopD-sizeᵗ V a hV) (szB-mono V (n≤1+n (sizeᵗ a)))
  hopD-sizeᵗ V (caseᵗ sc l r) hV =
    ≤-trans (+-mono-≤ (⊔-lub (≤-trans (hopD-sizeᵗ V l hV) (szB-mono V cl))
                             (≤-trans (hopD-sizeᵗ V r hV) (szB-mono V cr)))
                      (*-mono-≤ (⊔-lub (⊔-lub (≤-trans (pm-sizeᵗ V 0 l hV)
                                                       (szB-mono V cl))
                                              (≤-trans (pm-sizeᵗ V 0 r hV)
                                                       (szB-mono V cr)))
                                       (1≤szB V _))
                                (≤-trans (hopD-sizeᵗ V sc hV) (szB-mono V cs))))
            (szB-sq V (sizeᵗ sc + sizeᵗ l + sizeᵗ r) hV
                    (≤-trans (1≤sizeᵗ sc) cs))
    where
    cs : sizeᵗ sc ≤ sizeᵗ sc + sizeᵗ l + sizeᵗ r
    cs = ≤-trans (m≤m+n (sizeᵗ sc) (sizeᵗ l))
                 (m≤m+n (sizeᵗ sc + sizeᵗ l) (sizeᵗ r))
    cl : sizeᵗ l ≤ sizeᵗ sc + sizeᵗ l + sizeᵗ r
    cl = ≤-trans (m≤n+m (sizeᵗ l) (sizeᵗ sc))
                 (m≤m+n (sizeᵗ sc + sizeᵗ l) (sizeᵗ r))
    cr : sizeᵗ r ≤ sizeᵗ sc + sizeᵗ l + sizeᵗ r
    cr = m≤n+m (sizeᵗ r) (sizeᵗ sc + sizeᵗ l)
  hopD-sizeᵗ V (ifᵗ c a b) hV =
    ⊔-lub (≤-trans (hopD-sizeᵗ V a hV)
             (szB-mono V (≤-trans (≤-trans (m≤n+m (sizeᵗ a) (sizeᵗ c))
                                           (m≤m+n (sizeᵗ c + sizeᵗ a) (sizeᵗ b)))
                                  (n≤1+n (sizeᵗ c + sizeᵗ a + sizeᵗ b)))))
          (≤-trans (hopD-sizeᵗ V b hV)
             (szB-mono V (≤-trans (m≤n+m (sizeᵗ b) (sizeᵗ c + sizeᵗ a))
                                  (n≤1+n (sizeᵗ c + sizeᵗ a + sizeᵗ b)))))
  hopD-sizeᵗ V (primᵗ _ a) hV = z≤n
  hopD-sizeᵗ V (strmᵗ e)   hV =
    ≤-trans (hopD-sizeᵉ V e hV) (szB-mono V (n≤1+n (sizeᵉ e)))

  hopD-sizeᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (V : ℕ)
    (ts : List (Tm Γ Δᵍ Δ Θ t)) → 2 ≤ V → hopDᵗˢ V ts ≤ szB V (sizeᵗˢ ts)
  hopD-sizeᵗˢ V []       hV = z≤n
  hopD-sizeᵗˢ V (y ∷ ys) hV =
    ⊔-lub (≤-trans (hopD-sizeᵗ V y hV)
                   (szB-mono V (m≤m+n (sizeᵗ y) (sizeᵗˢ ys))))
          (≤-trans (hopD-sizeᵗˢ V ys hV)
                   (szB-mono V (m≤n+m (sizeᵗˢ ys) (sizeᵗ y))))

  pm-sizeᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (V k : ℕ) (e : Exp Γ Δᵍ Δ Θ t) →
    2 ≤ V → pmᵉ V k e ≤ szB V (sizeᵉ e)
  pm-sizeᵉ V k (input i) hV = z≤n
  pm-sizeᵉ V k (ofᵉ ts)  hV =
    ≤-trans (pm-sizeᵗˢ V k ts hV) (szB-mono V (n≤1+n (sizeᵗˢ ts)))
  pm-sizeᵉ V k emptyᵉ    hV = z≤n
  pm-sizeᵉ V k (mapᵉ f e) hV =
    ≤-trans (+-mono-≤ (≤-trans (pm-sizeᵗ V (suc k) f hV)
                               (szB-mono V (m≤m+n (sizeᵗ f) (sizeᵉ e))))
                      (*-mono-≤ (⊔-lub (≤-trans (pm-sizeᵗ V 0 f hV)
                                                (szB-mono V (m≤m+n _ _)))
                                       (1≤szB V _))
                                (≤-trans (pm-sizeᵉ V k e hV)
                                         (szB-mono V (m≤n+m (sizeᵉ e) (sizeᵗ f))))))
            (szB-sq V (sizeᵗ f + sizeᵉ e) hV
              (≤-trans (1≤sizeᵗ f) (m≤m+n (sizeᵗ f) (sizeᵉ e))))
  pm-sizeᵉ V k (takeᵉ c e) hV =
    ≤-trans (pm-sizeᵉ V k e hV)
            (szB-mono V (≤-trans (m≤n+m (sizeᵉ e) (sizeᵗ c))
                                 (n≤1+n (sizeᵗ c + sizeᵉ e))))
  pm-sizeᵉ V k (scanᵉ f z e) hV =
    ≤-trans (*-mono-≤ (^-monoˡ-≤ V (+-monoʳ-≤ 2 (pm-sizeᵗ V 0 f hV)))
              (+-mono-≤ (+-mono-≤ (≤-trans (pm-sizeᵗ V (suc k) f hV) (szB-mono V lef))
                                  (≤-trans (pm-sizeᵗ V k z hV) (szB-mono V lez)))
                        (≤-trans (pm-sizeᵉ V k e hV) (szB-mono V lee))))
            (szB-scan V (sizeᵗ f) (sizeᵗ z) (sizeᵉ e) hV
                      (1≤sizeᵗ f) (1≤sizeᵗ z) (1≤sizeᵉ e))
    where
    lef : sizeᵗ f ≤ sizeᵗ f + sizeᵗ z + sizeᵉ e
    lef = ≤-trans (m≤m+n (sizeᵗ f) (sizeᵗ z)) (m≤m+n _ (sizeᵉ e))
    lez : sizeᵗ z ≤ sizeᵗ f + sizeᵗ z + sizeᵉ e
    lez = ≤-trans (m≤n+m (sizeᵗ z) (sizeᵗ f)) (m≤m+n _ (sizeᵉ e))
    lee : sizeᵉ e ≤ sizeᵗ f + sizeᵗ z + sizeᵉ e
    lee = m≤n+m (sizeᵉ e) (sizeᵗ f + sizeᵗ z)
  pm-sizeᵉ V k (mergeAllᵉ e)   hV =
    ≤-trans (pm-sizeᵉ V k e hV) (szB-mono V (n≤1+n (sizeᵉ e)))
  pm-sizeᵉ V k (concatAllᵉ e)  hV =
    ≤-trans (pm-sizeᵉ V k e hV) (szB-mono V (n≤1+n (sizeᵉ e)))
  pm-sizeᵉ V k (switchAllᵉ e)  hV =
    ≤-trans (pm-sizeᵉ V k e hV) (szB-mono V (n≤1+n (sizeᵉ e)))
  pm-sizeᵉ V k (exhaustAllᵉ e) hV =
    ≤-trans (pm-sizeᵉ V k e hV) (szB-mono V (n≤1+n (sizeᵉ e)))
  pm-sizeᵉ V k (μᵉ e)     hV =
    ≤-trans (pm-sizeᵉ V k e hV) (szB-mono V (n≤1+n (sizeᵉ e)))
  pm-sizeᵉ V k (varᵉ x)   hV = z≤n
  pm-sizeᵉ V k (deferᵉ e) hV = z≤n

  pm-sizeᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (V k : ℕ) (tm : Tm Γ Δᵍ Δ Θ t) →
    2 ≤ V → pmᵗ V k tm ≤ szB V (sizeᵗ tm)
  pm-sizeᵗ V k (varᵗ x) hV = ≤-trans (ifLe1 (varIx x) k) (1≤szB V 1)
  pm-sizeᵗ V k unit̂     hV = z≤n
  pm-sizeᵗ V k (bool̂ _) hV = z≤n
  pm-sizeᵗ V k (nat̂ _)  hV = z≤n
  pm-sizeᵗ V k (pairᵗ a b) hV =
    ⊔-lub (≤-trans (pm-sizeᵗ V k a hV)
             (szB-mono V (≤-trans (m≤m+n (sizeᵗ a) (sizeᵗ b))
                                  (n≤1+n (sizeᵗ a + sizeᵗ b)))))
          (≤-trans (pm-sizeᵗ V k b hV)
             (szB-mono V (≤-trans (m≤n+m (sizeᵗ b) (sizeᵗ a))
                                  (n≤1+n (sizeᵗ a + sizeᵗ b)))))
  pm-sizeᵗ V k (fstᵗ q) hV =
    ≤-trans (pm-sizeᵗ V k q hV) (szB-mono V (n≤1+n (sizeᵗ q)))
  pm-sizeᵗ V k (sndᵗ q) hV =
    ≤-trans (pm-sizeᵗ V k q hV) (szB-mono V (n≤1+n (sizeᵗ q)))
  pm-sizeᵗ V k (inlᵗ a) hV =
    ≤-trans (pm-sizeᵗ V k a hV) (szB-mono V (n≤1+n (sizeᵗ a)))
  pm-sizeᵗ V k (inrᵗ a) hV =
    ≤-trans (pm-sizeᵗ V k a hV) (szB-mono V (n≤1+n (sizeᵗ a)))
  pm-sizeᵗ V k (caseᵗ sc l r) hV =
    ≤-trans (+-mono-≤ (⊔-lub (≤-trans (pm-sizeᵗ V (suc k) l hV) (szB-mono V cl))
                             (≤-trans (pm-sizeᵗ V (suc k) r hV) (szB-mono V cr)))
                      (*-mono-≤ (⊔-lub (⊔-lub (≤-trans (pm-sizeᵗ V 0 l hV)
                                                       (szB-mono V cl))
                                              (≤-trans (pm-sizeᵗ V 0 r hV)
                                                       (szB-mono V cr)))
                                       (1≤szB V _))
                                (≤-trans (pm-sizeᵗ V k sc hV) (szB-mono V cs))))
            (szB-sq V (sizeᵗ sc + sizeᵗ l + sizeᵗ r) hV
                    (≤-trans (1≤sizeᵗ sc) cs))
    where
    cs : sizeᵗ sc ≤ sizeᵗ sc + sizeᵗ l + sizeᵗ r
    cs = ≤-trans (m≤m+n (sizeᵗ sc) (sizeᵗ l))
                 (m≤m+n (sizeᵗ sc + sizeᵗ l) (sizeᵗ r))
    cl : sizeᵗ l ≤ sizeᵗ sc + sizeᵗ l + sizeᵗ r
    cl = ≤-trans (m≤n+m (sizeᵗ l) (sizeᵗ sc))
                 (m≤m+n (sizeᵗ sc + sizeᵗ l) (sizeᵗ r))
    cr : sizeᵗ r ≤ sizeᵗ sc + sizeᵗ l + sizeᵗ r
    cr = m≤n+m (sizeᵗ r) (sizeᵗ sc + sizeᵗ l)
  pm-sizeᵗ V k (ifᵗ c a b) hV =
    ⊔-lub (≤-trans (pm-sizeᵗ V k a hV)
             (szB-mono V (≤-trans (≤-trans (m≤n+m (sizeᵗ a) (sizeᵗ c))
                                           (m≤m+n (sizeᵗ c + sizeᵗ a) (sizeᵗ b)))
                                  (n≤1+n (sizeᵗ c + sizeᵗ a + sizeᵗ b)))))
          (≤-trans (pm-sizeᵗ V k b hV)
             (szB-mono V (≤-trans (m≤n+m (sizeᵗ b) (sizeᵗ c + sizeᵗ a))
                                  (n≤1+n (sizeᵗ c + sizeᵗ a + sizeᵗ b)))))
  pm-sizeᵗ V k (primᵗ _ a) hV = z≤n
  pm-sizeᵗ V k (strmᵗ e)   hV =
    ≤-trans (pm-sizeᵉ V k e hV) (szB-mono V (n≤1+n (sizeᵉ e)))

  pm-sizeᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (V k : ℕ)
    (ts : List (Tm Γ Δᵍ Δ Θ t)) → 2 ≤ V → pmᵗˢ V k ts ≤ szB V (sizeᵗˢ ts)
  pm-sizeᵗˢ V k []       hV = z≤n
  pm-sizeᵗˢ V k (y ∷ ys) hV =
    ⊔-lub (≤-trans (pm-sizeᵗ V k y hV)
                   (szB-mono V (m≤m+n (sizeᵗ y) (sizeᵗˢ ys))))
          (≤-trans (pm-sizeᵗˢ V k ys hV)
                   (szB-mono V (m≤n+m (sizeᵗˢ ys) (sizeᵗ y))))


-- the r ≤ R discharge, packaged: a stored expression's hop depth sits
-- under the store rank cap purely because its SIZE does — all through
-- stBounded?, no extra invariant
opaque
  unfolding szB

  hopD-cap : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (V : ℕ) (e : Exp Γ Δᵍ Δ Θ t) →
    2 ≤ V → sizeᵉ e ≤ V → hopDᵉ V e ≤ hopR V
  hopD-cap V e hV h =
    ≤-trans (hopD-sizeᵉ V e hV)
    (≤-trans (^-monoˡ-≤ (suc V ^ sizeᵉ e) (+-monoʳ-≤ 2 h))
             (^-monoʳ-≤ (2 + V) (^-monoʳ-≤ (suc V) (≤-trans h (n≤1+n V)))))

-- a shared slot's def is an element of the global syntactic
-- multiset {program} ⊎ {slots}: its size sits inside the budget's
-- slot summand
slotDef-size : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (i : Fin n)
  {d : Closed Γ (lookup Γ i)} → sl i ≡ shared d →
  sizeᵉ d ≤ slotsSize sl
slotDef-size sl i {d} eq =
  ≤-trans (≤-reflexive size-eq) (fᵢ≤sum-tab (λ j → slotSize (sl j)) i)
  where
  size-eq : sizeᵉ d ≡ slotSize (sl i)
  size-eq rewrite eq = refl

-- THE OWNERSHIP ANCHOR (the cascadeGo ledger's share-crossing
-- half), PROVEN: when a walked template's `input i` hits a shared
-- slot, the connect's resets re-anchor against the slot's OWN
-- element of the global syntactic multiset — its def d is fixed
-- the budget's height is at least 2 at every instant, and towerℕ 2 ≡ 4:
-- the V ≥ 2 that hopD-size wants is free wherever V is the budget
2≤sizeBudget : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id : Id) → 2 ≤ sizeBudgetAt e sl id
2≤sizeBudget e sl id =
  ≤-trans (≤ᵇ⇒≤ 2 4 tt)
          (towerℕ-mono {2} {(4 + (sizeᵉ e + slotsSize sl)) * suc id}
            (≤-trans (s≤s (s≤s z≤n))
                     (m≤m*n (4 + (sizeᵉ e + slotsSize sl)) (suc id))))

-- slot content, so its hop depth sits under the store rank cap
-- (feeding dBound-connect's r′ ≤ R) and its walk under the store bound
-- (feeding dBound-hop/-connect's s′ ≤ V), straight off the
-- budget's slot summand: no state invariant consulted
connect-anchor : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id : Id) (i : Fin n) {d : Closed Γ (lookup Γ i)} → sl i ≡ shared d →
  let V = sizeBudgetAt e sl id in
  (hopDᵉ V d ≤ hopR V) × (syncSizeᵉ d ≤ V)
connect-anchor e sl id i {d} eq =
  hopD-cap V d (2≤sizeBudget e sl id) size≤V
  , ≤-trans (syncSize≤sizeᵉ d) size≤V
  where
  V = sizeBudgetAt e sl id
  size≤V : sizeᵉ d ≤ V
  size≤V = ≤-trans (slotDef-size sl i eq) (slots≤budget e sl id)

------------------------------------------------------------------
-- THE DEMAND FUNCTION.  Fuel is depth-consumed, so the wet contract
-- carries `fuel hasAtLeast suc (dBound V R U r s)` where V bounds
-- store sizes, R bounds store ranks ((suc V)^(suc B), rank-lt-pow),
-- U = unconn, r = the current value's rank, s = the current
-- expression's syncSize.  The three decrement edges each consume
-- one gs against a strictly smaller demand — the suc V coefficient
-- absorbs the post-hop reset s′ ≤ V exactly, and suc R absorbs the
-- post-connect reset r′ ≤ R exactly; all three interface lemmas are
-- proven below, so the contract's clause proofs only ever apply
-- them, never redo arithmetic.
------------------------------------------------------------------

dBound : (V R U r s : ℕ) → ℕ
dBound V R U r s = s + suc V * (r + suc R * U)

-- edge 2 (μ-unfold): syncSize drops at fixed (U, r)
dBound-μ : ∀ {V R U r s′ s} → s′ < s →
  dBound V R U r s′ < dBound V R U r s
dBound-μ {V} {R} {U} {r} s′<s = +-monoˡ-≤ (suc V * (r + suc R * U)) s′<s

-- edge 3 (inner hop): rank drops, syncSize resets within the store
dBound-hop : ∀ {V R U r′ r s′ s} → r′ < r → s′ ≤ V →
  suc (dBound V R U r′ s′) ≤ dBound V R U r s
dBound-hop {V} {R} {U} {r′} {r} {s′} {s} r′<r s′≤V =
  ≤-trans (+-monoˡ-≤ (suc V * (r′ + suc R * U)) (s≤s s′≤V))
  (≤-trans (≤-reflexive (sym (*-suc (suc V) (r′ + suc R * U))))
  (≤-trans (*-monoʳ-≤ (suc V) (+-monoˡ-≤ (suc R * U) r′<r))
           (m≤n+m (suc V * (r + suc R * U)) s)))

-- edge 1 (connect): unconn drops, rank and syncSize reset within
-- the store bounds
dBound-connect : ∀ {V R U′ U r′ r s′ s} → U′ < U → r′ ≤ R → s′ ≤ V →
  suc (dBound V R U′ r′ s′) ≤ dBound V R U r s
dBound-connect {V} {R} {U′} {U} {r′} {r} {s′} {s} U′<U r′≤R s′≤V =
  ≤-trans (+-monoˡ-≤ (suc V * (r′ + suc R * U′)) (s≤s s′≤V))
  (≤-trans (≤-reflexive (sym (*-suc (suc V) (r′ + suc R * U′))))
  (≤-trans (*-monoʳ-≤ (suc V)
             (≤-trans (+-monoˡ-≤ (suc R * U′) (s≤s r′≤R))
             (≤-trans (≤-reflexive (sym (*-suc (suc R) U′)))
                      (*-monoʳ-≤ (suc R) U′<U))))
  (≤-trans (*-monoʳ-≤ (suc V) (m≤n+m (suc R * U) r))
           (m≤n+m (suc V * (r + suc R * U)) s))))

-- structural steps consume no fuel but shrink (or preserve) every
-- demand component — the interface every non-edge clause of the
-- contract's induction applies: the child's demand fits the
-- parent's fuel unchanged
-- the whole demand under one product — what the seed inequality
-- compares against the budget tower: dBound ≤ (1+V)(1+R)(1+U)
dBound-bound : ∀ {V R U r s} → s ≤ V → r ≤ R →
  dBound V R U r s ≤ suc V * suc R * suc U
dBound-bound {V} {R} {U} {r} {s} s≤V r≤R =
  ≤-trans (+-mono-≤ s≤V
            (*-monoʳ-≤ (suc V) (+-monoˡ-≤ (suc R * U) r≤R)))
  (≤-trans (+-monoˡ-≤ (suc V * (R + suc R * U)) (n≤1+n V))
  (≤-trans (≤-reflexive (sym (*-suc (suc V) (R + suc R * U))))
  (≤-trans (*-monoʳ-≤ (suc V) (≤-reflexive shuffle))
           (≤-reflexive (sym (*-assoc (suc V) (suc R) (suc U)))))))
  where
  -- suc (R + suc R * U) ≡ suc R * suc U, definitionally via *-suc
  shuffle : suc (R + suc R * U) ≡ suc R * suc U
  shuffle = sym (*-suc (suc R) U)

-- the two decrease lemmas the hop analysis needs (proof-design memo
-- below), PROVEN: ≺-embed (embedded-value hop — a value reified
-- into the carrier measures strictly below it, regardless of
-- relative template sizes) and ≺-replace (scan-produced hop —
-- replacing the carrier top with elements strictly below it
-- decreases; t must be a real size class).

⊕ᵛ-identityˡ : ∀ {m} (v : Vec ℕ m) → zerosᵛ ⊕ᵛ v ≡ v
⊕ᵛ-identityˡ []ᵛ       = refl
⊕ᵛ-identityˡ (x ∷ᵛ v) = cong (x ∷ᵛ_) (⊕ᵛ-identityˡ v)

⊕ᵛ-assoc : ∀ {m} (a b c : Vec ℕ m) → (a ⊕ᵛ b) ⊕ᵛ c ≡ a ⊕ᵛ (b ⊕ᵛ c)
⊕ᵛ-assoc []ᵛ       []ᵛ       []ᵛ       = refl
⊕ᵛ-assoc (x ∷ᵛ a) (y ∷ᵛ b) (z ∷ᵛ c) =
  cong₂ _∷ᵛ_ (+-assoc x y z) (⊕ᵛ-assoc a b c)

⊕ᵛ-comm : ∀ {m} (a b : Vec ℕ m) → a ⊕ᵛ b ≡ b ⊕ᵛ a
⊕ᵛ-comm []ᵛ       []ᵛ       = refl
⊕ᵛ-comm (x ∷ᵛ a) (y ∷ᵛ b) = cong₂ _∷ᵛ_ (+-comm x y) (⊕ᵛ-comm a b)

counts-++ : ∀ B (xs ys : List ℕ) →
  counts B (xs ++ ys) ≡ counts B xs ⊕ᵛ counts B ys
counts-++ B []       ys = sym (⊕ᵛ-identityˡ (counts B ys))
counts-++ B (x ∷ xs) ys rewrite counts-++ B xs ys =
  sym (⊕ᵛ-assoc (oneAt B x) (counts B xs) (counts B ys))

-- adding any vector with mass strictly grows the lex reading
≺ᵛ-grow : ∀ {m} (w v : Vec ℕ m) → 1 ≤ totᵛ w → v ≺ᵛ (w ⊕ᵛ v)
≺ᵛ-grow []ᵛ           []ᵛ       ()
≺ᵛ-grow (zero  ∷ᵛ w) (y ∷ᵛ v) h = ≺-there (≺ᵛ-grow w v h)
≺ᵛ-grow (suc x ∷ᵛ w) (y ∷ᵛ v) h = ≺-here (s≤s (m≤n+m y x))

≺-embed : ∀ B t (xs ys M : List ℕ) →
  counts B M ≺ᵛ counts B (t ∷ xs ++ M ++ ys)
≺-embed B t xs ys M =
  subst (counts B M ≺ᵛ_) (sym eq) (≺ᵛ-grow W (counts B M) tot1)
  where
  W = oneAt B t ⊕ᵛ (counts B xs ⊕ᵛ counts B ys)
  eq : counts B (t ∷ xs ++ M ++ ys) ≡ W ⊕ᵛ counts B M
  eq = trans (cong (oneAt B t ⊕ᵛ_)
               (trans (counts-++ B xs (M ++ ys))
                      (cong (counts B xs ⊕ᵛ_) (counts-++ B M ys))))
       (trans (cong (λ z → oneAt B t ⊕ᵛ (counts B xs ⊕ᵛ z))
                    (⊕ᵛ-comm (counts B M) (counts B ys)))
       (trans (cong (oneAt B t ⊕ᵛ_)
                    (sym (⊕ᵛ-assoc (counts B xs) (counts B ys) (counts B M))))
              (sym (⊕ᵛ-assoc (oneAt B t)
                             (counts B xs ⊕ᵛ counts B ys) (counts B M)))))
  tot1 : 1 ≤ totᵛ W
  tot1 = subst (1 ≤_)
           (sym (trans (totᵛ-⊕ᵛ (oneAt B t) (counts B xs ⊕ᵛ counts B ys))
                       (cong (_+ totᵛ (counts B xs ⊕ᵛ counts B ys))
                             (totᵛ-oneAt B t))))
           (s≤s z≤n)

-- lex is compatible with adding a common vector
≺ᵛ-⊕ʳ : ∀ {m} {u v : Vec ℕ m} (w : Vec ℕ m) → u ≺ᵛ v → (u ⊕ᵛ w) ≺ᵛ (v ⊕ᵛ w)
≺ᵛ-⊕ʳ (z ∷ᵛ w) (≺-here  x<y) = ≺-here (+-monoˡ-< z x<y)
≺ᵛ-⊕ʳ (z ∷ᵛ w) (≺-there u≺v) = ≺-there (≺ᵛ-⊕ʳ w u≺v)

-- (suc B ≤ᵇ y) unfolds to (B <ᵇ y), so state the false case there
≤⇒<ᵇ-false : ∀ y B → y ≤ B → (B <ᵇ y) ≡ false
≤⇒<ᵇ-false zero    B       z≤n       = refl
≤⇒<ᵇ-false (suc y) (suc B) (s≤s y≤B) = ≤⇒<ᵇ-false y B y≤B

-- every element strictly below suc B ⇒ the top class stays empty
counts-tail : ∀ B (Y : List ℕ) → All (_< suc B) Y →
  counts (suc B) Y ≡ 0 ∷ᵛ counts B Y
counts-tail B []      []ᵃ        = refl
counts-tail B (y ∷ Y) (py ∷ᵃ pY)
  rewrite ≤⇒<ᵇ-false y B (≤-pred py) | counts-tail B Y pY = refl

-- a multiset entirely below class t sits under a single t element
counts-below : ∀ B t (Y : List ℕ) → All (_< t) Y → t ≤ B →
  counts B Y ≺ᵛ oneAt B t
counts-below zero    zero    []      []ᵃ        h = ≺-here (s≤s z≤n)
counts-below zero    zero    (y ∷ Y) (() ∷ᵃ _)  h
counts-below zero    (suc t) Y       aY         ()
counts-below (suc B) t       Y       aY         t≤
  with m≤n⇒m<n∨m≡n t≤
... | inj₂ refl
  rewrite counts-tail B Y aY
        | T⇒≡true (suc B ≤ᵇ suc B) (≤⇒≤ᵇ (≤-refl {suc B})) = ≺-here (s≤s z≤n)
... | inj₁ t<sB
  rewrite counts-tail B Y
            (mapᴬ (λ py → ≤-trans py (≤-trans (≤-pred t<sB) (n≤1+n B))) aY)
        | ≤⇒<ᵇ-false t B (≤-pred t<sB)
  = ≺-there (counts-below B t Y aY (≤-pred t<sB))

≺-replace : ∀ B t (Y Z : List ℕ) → All (_< t) Y → t ≤ B →
  counts B (Y ++ Z) ≺ᵛ counts B (t ∷ Z)
≺-replace B t Y Z aY t≤B rewrite counts-++ B Y Z =
  ≺ᵛ-⊕ʳ (counts B Z) (counts-below B t Y aY t≤B)

-- the μ edge at the measure level: unfolding strictly DROPS the
-- walked expression's multiset — the μ node's host class steps
-- down by one and the inner multiset rides along (shell mirrors
-- of elimG above) — so hop anchors never wobble across unfolds
unfoldμ-≺ : ∀ {n} {Γ : Ctx n} {t} (B : ℕ)
  (body : Exp Γ (t ∷ []) [] [] t) →
  shellSizeᵉ (μᵉ body) ≤ B →
  measureE B (unfoldμ body) ≺ᵛ measureE B (μᵉ body)
unfoldμ-≺ B body h
  rewrite shellSize-unfoldμ body | inner-unfoldμ body =
  ≺-replace B (suc (shellSizeᵉ body)) (shellSizeᵉ body ∷ []) (innerᵉ body)
    (≤-refl ∷ᵃ []ᵃ) h

-- the μ clause threads SHELL caps, not sizeᵉ (unfoldμ copies the
-- closed μ, so sizeᵉ grows — but every shell is preserved or
-- stepped down, and the shell COUNT is exactly preserved).  These
-- two transfers are what keep the contract's side conditions alive
-- across the μ decrement edge
shells-unfoldμ-cap : ∀ {n} {Γ : Ctx n} {t} (B : ℕ)
  (body : Exp Γ (t ∷ []) [] [] t) →
  All (_≤ B) (shellsᵉ (μᵉ body)) → All (_≤ B) (shellsᵉ (unfoldμ body))
shells-unfoldμ-cap B body (hd ∷ᵃ tl)
  rewrite shellSize-unfoldμ body | inner-unfoldμ body =
  ≤-trans (n≤1+n _) hd ∷ᵃ tl

------------------------------------------------------------------
-- (W12-A) THE STRUCTURAL DESCENT.  The three FUEL edges (μ, inner
-- hop, connect) each have their dBound lemma above.  A STRUCTURAL
-- edge — mapᵉ/takeᵉ/scanᵉ/the four *Alls/μ, the operator walking
-- into its own source — peels no gas, so the fuel accounting is
-- indifferent to it; but the LENGTH ledger is not, because such an
-- edge adds one frame to the path.  It pays for that frame out of
-- the descent: both dBound arguments drop at once.
--
--   syncSize  drops because every structural constructor is
--             `suc (… + syncSizeᵉ e)` — a strict drop, the s side.
--   rank      drops because shellSizeᵉ steps DOWN by exactly one
--             (the operator's own node) and the child's inner
--             multiset is a sub-multiset of the parent's — so the
--             child's count vector loses a high digit and gains
--             nothing, the r side.
--
-- descent-of below is the single interface: it takes exactly the
-- two syntactic facts that distinguish the seven constructors (host
-- shell steps down one; inner multiset grows by some N) and returns
-- the strict dBound drop.  Instantiating it per clause is then just
-- naming N — [] for the *Alls and μ, innerᵗ f for map/take,
-- innerᵗ f ++ innerᵗ z for scan.
------------------------------------------------------------------

-- lex is compatible with GROWING the larger side (the mirror of
-- ≺ᵛ-⊕ʳ, which grows both): a zero digit passes the step through,
-- a positive one settles it right there
≺ᵛ-⊕ᵇ : ∀ {m} {u v : Vec ℕ m} (w : Vec ℕ m) → u ≺ᵛ v → u ≺ᵛ (v ⊕ᵛ w)
≺ᵛ-⊕ᵇ (z ∷ᵛ w) (≺-here {y = y} x<y) = ≺-here (<-≤-trans x<y (m≤m+n y z))
≺ᵛ-⊕ᵇ {u = x ∷ᵛ _} (zero ∷ᵛ w) (≺-there u≺v)
  rewrite +-identityʳ x = ≺-there (≺ᵛ-⊕ᵇ w u≺v)
≺ᵛ-⊕ᵇ {u = x ∷ᵛ _} (suc z ∷ᵛ w) (≺-there u≺v) =
  ≺-here (subst (x <_) (sym (+-suc x z)) (s≤s (m≤m+n x z)))

-- ONE class-s element under ONE class-(suc s) element, with any
-- extra multiset N riding on the larger side
shells-drop : ∀ B s (N M : List ℕ) → suc s ≤ B →
  counts B (s ∷ M) ≺ᵛ counts B (suc s ∷ (N ++ M))
shells-drop B s N M h =
  subst (counts B (s ∷ M) ≺ᵛ_) (sym eq)
    (≺ᵛ-⊕ᵇ (counts B N)
      (≺-replace B (suc s) (s ∷ []) M (≤-refl ∷ᵃ []ᵃ) h))
  where
  eq : counts B (suc s ∷ (N ++ M)) ≡ counts B (suc s ∷ M) ⊕ᵛ counts B N
  eq = trans (cong (oneAt B (suc s) ⊕ᵛ_)
               (trans (counts-++ B N M)
                      (⊕ᵛ-comm (counts B N) (counts B M))))
             (sym (⊕ᵛ-assoc (oneAt B (suc s)) (counts B M) (counts B N)))

-- the ≺ᵛ step read as a numeral drop, with the entry-sum side
-- condition discharged off sizeᵉ exactly as measureE-rank does
rank-drop : ∀ {n} {Γ : Ctx n} {s u} (V : ℕ)
  (b : Closed Γ s) (c : Closed Γ u) →
  measureE V b ≺ᵛ measureE V c → sizeᵉ b ≤ V →
  rank V (measureE V b) < rank V (measureE V c)
rank-drop V b c step h =
  rank-mono-≺ V step
    (subst (_≤ V) (sym (totᵛ-counts V (shellsᵉ b)))
           (≤-trans (shells-len b) h))

-- both dBound arguments move at once: rank weakly, syncSize
-- strictly.  V R U are EXPLICIT: dBound unfolds through _*_, which
-- matches on its first argument, so implicits here are stuck in the
-- same way ⊔-elim-help's were
dBound-struct : ∀ (V R U : ℕ) {r′ r s′ s} → r′ ≤ r → s′ < s →
  dBound V R U r′ s′ < dBound V R U r s
dBound-struct V R U r′≤r s′<s =
  +-mono-<-≤ s′<s (*-monoʳ-≤ (suc V) (+-monoˡ-≤ (suc R * U) r′≤r))

------------------------------------------------------------------
-- THE STRUCTURAL EDGE's r side, in hopD.  With `r` a remaining-hop
-- COUNT rather than a shell multiset, this stops being a sub-multiset
-- argument and becomes seven one-line clause facts: every structural
-- constructor keeps its source's hop depth, because every clause
-- either passes it through, scales it by a factor that is ≥ 1, or
-- (at a *All) adds the one hop the operator itself will take.
--
-- Note what is NOT here and does not need to be: an inequality for
-- the μ edge.  hopD (μᵉ body) is hopD body BY DEFINITION, so the
-- structural μ step is refl and the UNFOLD step — where the retired
-- measure needed unfoldμ-≺ — is an equality too (Δᵍ vars live only
-- under deferᵉ, which hopD cuts).  The μ edge pays entirely with
-- dBound-μ's s, exactly as it already did.
------------------------------------------------------------------

module _ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} (V : ℕ) where

  hopD-map : ∀ {s u} (f : Tm Γ Δᵍ Δ (s ∷ Θ) u) (b : Exp Γ Δᵍ Δ Θ s) →
    hopDᵉ V b ≤ hopDᵉ V (mapᵉ f b)
  hopD-map f b =
    ≤-trans (1*≤ (hopDᵉ V b) (pmᵗ V 0 f ⊔ 1) (m≤n⊔m (pmᵗ V 0 f) 1))
            (m≤n+m ((pmᵗ V 0 f ⊔ 1) * hopDᵉ V b) (hopDᵗ V f))

  hopD-take : ∀ {u} (c : Tm Γ Δᵍ Δ Θ natᵗ) (b : Exp Γ Δᵍ Δ Θ u) →
    hopDᵉ V b ≤ hopDᵉ V (takeᵉ c b)
  hopD-take c b = ≤-refl

  hopD-scan : ∀ {s u} (f : Tm Γ Δᵍ Δ ((u ×ᵗ s) ∷ Θ) u) (z : Tm Γ Δᵍ Δ Θ u)
    (b : Exp Γ Δᵍ Δ Θ s) → hopDᵉ V b ≤ hopDᵉ V (scanᵉ f z b)
  hopD-scan f z b =
    ≤-trans (m≤n+m (hopDᵉ V b) (hopDᵗ V f + hopDᵗ V z))
            (1*≤ _ _ (1≤pow (suc (pmᵗ V 0 f)) V))

  -- the four hop carriers: the operator's own frame is the `suc`
  hopD-all : ∀ {u} (b : Exp Γ Δᵍ Δ Θ (obs u)) →
    hopDᵉ V b ≤ suc (hopDᵉ V b)
  hopD-all b = n≤1+n (hopDᵉ V b)

------------------------------------------------------------------
-- PHASE 3, THE ASSEMBLY: the emitted-value invariant's engine.
--
-- burstHopD? (above) says every value a burst carries has hop depth at
-- most the subscribed expression's.  Every such value is produced by
-- evalWith on a SUBTERM of that expression — the mapᵉ frame's applyFn,
-- the ofᵉ frame's evalTm — and evalWith at an obs type IS subΘExp
-- (closeUnderFn is subΘExp []).  So the conjunct reduces to a bound on
-- substitution, and that bound is AFFINE in the plugged depth:
--
--     hopD (e[v]) ≤ hopD e + pm k e · hopD v
--
-- with pm the slope.  This is where pm came from — the mapᵉ clause
-- needs exactly `pmᵗ V 0 f` from its recursive calls, and no
-- occurrence count is that quantity (see the hop-descent memo).
--
-- Stated here with its three pieces postulated, per the outside-in
-- rule, so the consumer exists before any of them is proven.  The
-- consumer is hopD-map-emit at the bottom: the shape subscribeE-walk's
-- mapᵉ clause applies, with no arithmetic left in it.
------------------------------------------------------------------

-- (H0)'s TWO PIECES, proven.  A coefficient is read at a LOCAL index —
-- one of the binders between it and the root — and substitution has to
-- leave it alone, or the affine bound has a different slope on each
-- side and there is nothing to induct on.
--
-- subΘ keeps Θloc as a PREFIX, so a local variable keeps its position;
-- and a plug is Θ-CLOSED, so every variable it brings is bound inside
-- it and is compared against an index already bumped past it.  Those
-- are the two pieces, in that order.

-- a de Bruijn position survives the ∈-++⁻ left injection …
varIx-++ˡ : ∀ {t} (Θloc : List Ty) {Θsub} (x : t ∈ Θloc ++ Θsub)
  {y : t ∈ Θloc} → ∈-++⁻ Θloc x ≡ inj₁ y → varIx y ≡ varIx x
varIx-++ˡ []          x          ()
varIx-++ˡ (u ∷ Θloc) (here refl) refl = refl
varIx-++ˡ (u ∷ Θloc) (there x)   eq with ∈-++⁻ Θloc x in eq′
varIx-++ˡ (u ∷ Θloc) (there x)   refl | inj₁ y′ = cong suc (varIx-++ˡ Θloc x eq′)
varIx-++ˡ (u ∷ Θloc) (there x)   ()   | inj₂ z′

-- … and on the right injection the position is past every local binder
varIx-++ʳ : ∀ {t} (Θloc : List Ty) {Θsub} (x : t ∈ Θloc ++ Θsub)
  {z : t ∈ Θsub} → ∈-++⁻ Θloc x ≡ inj₂ z → length Θloc ≤ varIx x
varIx-++ʳ []          x          eq = z≤n
varIx-++ʳ (u ∷ Θloc) (here refl) ()
varIx-++ʳ (u ∷ Θloc) (there x)   eq with ∈-++⁻ Θloc x in eq′
varIx-++ʳ (u ∷ Θloc) (there x)   ()   | inj₁ y′
varIx-++ʳ (u ∷ Θloc) (there x)   refl | inj₂ z′ = s≤s (varIx-++ʳ Θloc x eq′)

-- the pm leaf at a position that is not the one being asked about
ifNeq : ∀ (a b : ℕ) → (a ≡ b → ⊥) → (if a ≡ᵇ b then 1 else 0) ≡ 0
ifNeq a b ne with a ≡ᵇ b in eq
... | false = refl
... | true  = ⊥-elim (ne (≡ᵇ⇒≡ a b (subst T (sym eq) tt)))

-- pm of a RENAMED term is 0 at any index no variable is renamed onto.
-- Stated over an arbitrary renaming rather than over wkTm directly, so
-- the induction can pass under binders — where the index and the
-- renaming shift together, and the hypothesis shifts with them.
ext-≢ : ∀ {Θ Θ′ s} (k : ℕ) (ρt : Ren∈ Θ Θ′) →
  (∀ {u} (x : u ∈ Θ) → varIx (ρt x) ≡ k → ⊥) →
  (∀ {u} (x : u ∈ s ∷ Θ) → varIx (ext∈ ρt x) ≡ suc k → ⊥)
ext-≢ k ρt h (here refl) ()
ext-≢ k ρt h (there y)   eq = h y (suc-injective eq)

mutual
  pm-ren0ᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (V k : ℕ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′) →
    (∀ {u} (x : u ∈ Θ) → varIx (ρt x) ≡ k → ⊥) →
    (e : Exp Γ Δᵍ Δ Θ t) → pmᵉ V k (renExp ρg ρd ρt e) ≡ 0
  pm-ren0ᵉ V k ρg ρd ρt h (input i)  = refl
  pm-ren0ᵉ V k ρg ρd ρt h (ofᵉ ts)   = pm-ren0ᵗˢ V k ρg ρd ρt h ts
  pm-ren0ᵉ V k ρg ρd ρt h emptyᵉ     = refl
  pm-ren0ᵉ V k ρg ρd ρt h (mapᵉ f e)
    rewrite pm-ren0ᵗ V (suc k) ρg ρd (ext∈ ρt) (ext-≢ k ρt h) f
          | pm-ren0ᵉ V k ρg ρd ρt h e =
    *-zeroʳ (pmᵗ V 0 (renTm ρg ρd (ext∈ ρt) f) ⊔ 1)
  pm-ren0ᵉ V k ρg ρd ρt h (takeᵉ c e) = pm-ren0ᵉ V k ρg ρd ρt h e
  pm-ren0ᵉ V k ρg ρd ρt h (scanᵉ f z e)
    rewrite pm-ren0ᵗ V (suc k) ρg ρd (ext∈ ρt) (ext-≢ k ρt h) f
          | pm-ren0ᵗ V k ρg ρd ρt h z
          | pm-ren0ᵉ V k ρg ρd ρt h e =
    *-zeroʳ (suc (suc (pmᵗ V 0 (renTm ρg ρd (ext∈ ρt) f))) ^ V)
  pm-ren0ᵉ V k ρg ρd ρt h (mergeAllᵉ e)   = pm-ren0ᵉ V k ρg ρd ρt h e
  pm-ren0ᵉ V k ρg ρd ρt h (concatAllᵉ e)  = pm-ren0ᵉ V k ρg ρd ρt h e
  pm-ren0ᵉ V k ρg ρd ρt h (switchAllᵉ e)  = pm-ren0ᵉ V k ρg ρd ρt h e
  pm-ren0ᵉ V k ρg ρd ρt h (exhaustAllᵉ e) = pm-ren0ᵉ V k ρg ρd ρt h e
  pm-ren0ᵉ V k ρg ρd ρt h (μᵉ e)     = pm-ren0ᵉ V k (ext∈ ρg) ρd ρt h e
  pm-ren0ᵉ V k ρg ρd ρt h (varᵉ x)   = refl
  pm-ren0ᵉ V k ρg ρd ρt h (deferᵉ e) = refl

  pm-ren0ᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (V k : ℕ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′) →
    (∀ {u} (x : u ∈ Θ) → varIx (ρt x) ≡ k → ⊥) →
    (tm : Tm Γ Δᵍ Δ Θ t) → pmᵗ V k (renTm ρg ρd ρt tm) ≡ 0
  pm-ren0ᵗ V k ρg ρd ρt h (varᵗ x)    = ifNeq (varIx (ρt x)) k (h x)
  pm-ren0ᵗ V k ρg ρd ρt h unit̂        = refl
  pm-ren0ᵗ V k ρg ρd ρt h (bool̂ _)    = refl
  pm-ren0ᵗ V k ρg ρd ρt h (nat̂ _)     = refl
  pm-ren0ᵗ V k ρg ρd ρt h (pairᵗ a b)
    rewrite pm-ren0ᵗ V k ρg ρd ρt h a | pm-ren0ᵗ V k ρg ρd ρt h b = refl
  pm-ren0ᵗ V k ρg ρd ρt h (fstᵗ p)    = pm-ren0ᵗ V k ρg ρd ρt h p
  pm-ren0ᵗ V k ρg ρd ρt h (sndᵗ p)    = pm-ren0ᵗ V k ρg ρd ρt h p
  pm-ren0ᵗ V k ρg ρd ρt h (inlᵗ a)    = pm-ren0ᵗ V k ρg ρd ρt h a
  pm-ren0ᵗ V k ρg ρd ρt h (inrᵗ a)    = pm-ren0ᵗ V k ρg ρd ρt h a
  pm-ren0ᵗ V k ρg ρd ρt h (caseᵗ sc l r)
    rewrite pm-ren0ᵗ V (suc k) ρg ρd (ext∈ ρt) (ext-≢ k ρt h) l
          | pm-ren0ᵗ V (suc k) ρg ρd (ext∈ ρt) (ext-≢ k ρt h) r
          | pm-ren0ᵗ V k ρg ρd ρt h sc =
    *-zeroʳ (pmᵗ V 0 (renTm ρg ρd (ext∈ ρt) l)
             ⊔ pmᵗ V 0 (renTm ρg ρd (ext∈ ρt) r) ⊔ 1)
  pm-ren0ᵗ V k ρg ρd ρt h (ifᵗ c a b)
    rewrite pm-ren0ᵗ V k ρg ρd ρt h a | pm-ren0ᵗ V k ρg ρd ρt h b = refl
  pm-ren0ᵗ V k ρg ρd ρt h (primᵗ _ a) = refl
  pm-ren0ᵗ V k ρg ρd ρt h (strmᵗ e)   = pm-ren0ᵉ V k ρg ρd ρt h e

  pm-ren0ᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (V k : ℕ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′) →
    (∀ {u} (x : u ∈ Θ) → varIx (ρt x) ≡ k → ⊥) →
    (ts : List (Tm Γ Δᵍ Δ Θ t)) → pmᵗˢ V k (renTms ρg ρd ρt ts) ≡ 0
  pm-ren0ᵗˢ V k ρg ρd ρt h []       = refl
  pm-ren0ᵗˢ V k ρg ρd ρt h (y ∷ ys)
    rewrite pm-ren0ᵗ V k ρg ρd ρt h y | pm-ren0ᵗˢ V k ρg ρd ρt h ys = refl

-- the case that matters: a Θ-closed plug, weakened in, is invisible
pm-wkTm : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (V k : ℕ) (tm : Tm Γ [] [] [] t) →
  pmᵗ V k (wkTm {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} tm) ≡ 0
pm-wkTm V k tm = pm-ren0ᵗ V k (λ ()) (λ ()) (λ ()) (λ ()) tm

-- A RENAMING THAT KEEPS EVERY POSITION keeps both measures — pm reads
-- positions, and hopD reads pm for its coefficients.  The instance that
-- matters is weakening OUT OF EMPTY contexts, whose hypothesis is
-- vacuous; the generality is only so the induction can pass under
-- binders, where ext∈ preserves positions exactly when ρt does.
ext-ix : ∀ {Θ Θ′ s} (ρt : Ren∈ Θ Θ′) →
  (∀ {u} (x : u ∈ Θ) → varIx (ρt x) ≡ varIx x) →
  (∀ {u} (x : u ∈ s ∷ Θ) → varIx (ext∈ ρt x) ≡ varIx x)
ext-ix ρt p (here refl) = refl
ext-ix ρt p (there y)   = cong suc (p y)

mutual
  pm-renᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (V k : ℕ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′) →
    (∀ {u} (x : u ∈ Θ) → varIx (ρt x) ≡ varIx x) →
    (e : Exp Γ Δᵍ Δ Θ t) → pmᵉ V k (renExp ρg ρd ρt e) ≡ pmᵉ V k e
  pm-renᵉ V k ρg ρd ρt p (input i) = refl
  pm-renᵉ V k ρg ρd ρt p (ofᵉ ts)  = pm-renᵗˢ V k ρg ρd ρt p ts
  pm-renᵉ V k ρg ρd ρt p emptyᵉ    = refl
  pm-renᵉ V k ρg ρd ρt p (mapᵉ f e)
    rewrite pm-renᵗ V (suc k) ρg ρd (ext∈ ρt) (ext-ix ρt p) f
          | pm-renᵗ V 0 ρg ρd (ext∈ ρt) (ext-ix ρt p) f
          | pm-renᵉ V k ρg ρd ρt p e = refl
  pm-renᵉ V k ρg ρd ρt p (takeᵉ c e) = pm-renᵉ V k ρg ρd ρt p e
  pm-renᵉ V k ρg ρd ρt p (scanᵉ f z e)
    rewrite pm-renᵗ V (suc k) ρg ρd (ext∈ ρt) (ext-ix ρt p) f
          | pm-renᵗ V 0 ρg ρd (ext∈ ρt) (ext-ix ρt p) f
          | pm-renᵗ V k ρg ρd ρt p z
          | pm-renᵉ V k ρg ρd ρt p e = refl
  pm-renᵉ V k ρg ρd ρt p (mergeAllᵉ e)   = pm-renᵉ V k ρg ρd ρt p e
  pm-renᵉ V k ρg ρd ρt p (concatAllᵉ e)  = pm-renᵉ V k ρg ρd ρt p e
  pm-renᵉ V k ρg ρd ρt p (switchAllᵉ e)  = pm-renᵉ V k ρg ρd ρt p e
  pm-renᵉ V k ρg ρd ρt p (exhaustAllᵉ e) = pm-renᵉ V k ρg ρd ρt p e
  pm-renᵉ V k ρg ρd ρt p (μᵉ e)     = pm-renᵉ V k (ext∈ ρg) ρd ρt p e
  pm-renᵉ V k ρg ρd ρt p (varᵉ x)   = refl
  pm-renᵉ V k ρg ρd ρt p (deferᵉ e) = refl

  pm-renᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (V k : ℕ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′) →
    (∀ {u} (x : u ∈ Θ) → varIx (ρt x) ≡ varIx x) →
    (tm : Tm Γ Δᵍ Δ Θ t) → pmᵗ V k (renTm ρg ρd ρt tm) ≡ pmᵗ V k tm
  pm-renᵗ V k ρg ρd ρt p (varᵗ x)  =
    cong (λ i → if i ≡ᵇ k then 1 else 0) (p x)
  pm-renᵗ V k ρg ρd ρt p unit̂      = refl
  pm-renᵗ V k ρg ρd ρt p (bool̂ _)  = refl
  pm-renᵗ V k ρg ρd ρt p (nat̂ _)   = refl
  pm-renᵗ V k ρg ρd ρt p (pairᵗ a b)
    rewrite pm-renᵗ V k ρg ρd ρt p a | pm-renᵗ V k ρg ρd ρt p b = refl
  pm-renᵗ V k ρg ρd ρt p (fstᵗ q)  = pm-renᵗ V k ρg ρd ρt p q
  pm-renᵗ V k ρg ρd ρt p (sndᵗ q)  = pm-renᵗ V k ρg ρd ρt p q
  pm-renᵗ V k ρg ρd ρt p (inlᵗ a)  = pm-renᵗ V k ρg ρd ρt p a
  pm-renᵗ V k ρg ρd ρt p (inrᵗ a)  = pm-renᵗ V k ρg ρd ρt p a
  pm-renᵗ V k ρg ρd ρt p (caseᵗ sc l r)
    rewrite pm-renᵗ V (suc k) ρg ρd (ext∈ ρt) (ext-ix ρt p) l
          | pm-renᵗ V (suc k) ρg ρd (ext∈ ρt) (ext-ix ρt p) r
          | pm-renᵗ V 0 ρg ρd (ext∈ ρt) (ext-ix ρt p) l
          | pm-renᵗ V 0 ρg ρd (ext∈ ρt) (ext-ix ρt p) r
          | pm-renᵗ V k ρg ρd ρt p sc = refl
  pm-renᵗ V k ρg ρd ρt p (ifᵗ c a b)
    rewrite pm-renᵗ V k ρg ρd ρt p a | pm-renᵗ V k ρg ρd ρt p b = refl
  pm-renᵗ V k ρg ρd ρt p (primᵗ _ a) = refl
  pm-renᵗ V k ρg ρd ρt p (strmᵗ e)   = pm-renᵉ V k ρg ρd ρt p e

  pm-renᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (V k : ℕ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′) →
    (∀ {u} (x : u ∈ Θ) → varIx (ρt x) ≡ varIx x) →
    (ts : List (Tm Γ Δᵍ Δ Θ t)) →
    pmᵗˢ V k (renTms ρg ρd ρt ts) ≡ pmᵗˢ V k ts
  pm-renᵗˢ V k ρg ρd ρt p []       = refl
  pm-renᵗˢ V k ρg ρd ρt p (y ∷ ys)
    rewrite pm-renᵗ V k ρg ρd ρt p y | pm-renᵗˢ V k ρg ρd ρt p ys = refl

mutual
  hopD-renᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (V : ℕ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′) →
    (∀ {u} (x : u ∈ Θ) → varIx (ρt x) ≡ varIx x) →
    (e : Exp Γ Δᵍ Δ Θ t) → hopDᵉ V (renExp ρg ρd ρt e) ≡ hopDᵉ V e
  hopD-renᵉ V ρg ρd ρt p (input i) = refl
  hopD-renᵉ V ρg ρd ρt p (ofᵉ ts)  = hopD-renᵗˢ V ρg ρd ρt p ts
  hopD-renᵉ V ρg ρd ρt p emptyᵉ    = refl
  hopD-renᵉ V ρg ρd ρt p (mapᵉ f e)
    rewrite hopD-renᵗ V ρg ρd (ext∈ ρt) (ext-ix ρt p) f
          | pm-renᵗ V 0 ρg ρd (ext∈ ρt) (ext-ix ρt p) f
          | hopD-renᵉ V ρg ρd ρt p e = refl
  hopD-renᵉ V ρg ρd ρt p (takeᵉ c e) = hopD-renᵉ V ρg ρd ρt p e
  hopD-renᵉ V ρg ρd ρt p (scanᵉ f z e)
    rewrite pm-renᵗ V 0 ρg ρd (ext∈ ρt) (ext-ix ρt p) f
          | hopD-renᵗ V ρg ρd (ext∈ ρt) (ext-ix ρt p) f
          | hopD-renᵗ V ρg ρd ρt p z
          | hopD-renᵉ V ρg ρd ρt p e = refl
  hopD-renᵉ V ρg ρd ρt p (mergeAllᵉ e)   = cong suc (hopD-renᵉ V ρg ρd ρt p e)
  hopD-renᵉ V ρg ρd ρt p (concatAllᵉ e)  = cong suc (hopD-renᵉ V ρg ρd ρt p e)
  hopD-renᵉ V ρg ρd ρt p (switchAllᵉ e)  = cong suc (hopD-renᵉ V ρg ρd ρt p e)
  hopD-renᵉ V ρg ρd ρt p (exhaustAllᵉ e) = cong suc (hopD-renᵉ V ρg ρd ρt p e)
  hopD-renᵉ V ρg ρd ρt p (μᵉ e)     = hopD-renᵉ V (ext∈ ρg) ρd ρt p e
  hopD-renᵉ V ρg ρd ρt p (varᵉ x)   = refl
  hopD-renᵉ V ρg ρd ρt p (deferᵉ e) = refl

  hopD-renᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (V : ℕ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′) →
    (∀ {u} (x : u ∈ Θ) → varIx (ρt x) ≡ varIx x) →
    (tm : Tm Γ Δᵍ Δ Θ t) → hopDᵗ V (renTm ρg ρd ρt tm) ≡ hopDᵗ V tm
  hopD-renᵗ V ρg ρd ρt p (varᵗ x)  = refl
  hopD-renᵗ V ρg ρd ρt p unit̂      = refl
  hopD-renᵗ V ρg ρd ρt p (bool̂ _)  = refl
  hopD-renᵗ V ρg ρd ρt p (nat̂ _)   = refl
  hopD-renᵗ V ρg ρd ρt p (pairᵗ a b)
    rewrite hopD-renᵗ V ρg ρd ρt p a | hopD-renᵗ V ρg ρd ρt p b = refl
  hopD-renᵗ V ρg ρd ρt p (fstᵗ q)  = hopD-renᵗ V ρg ρd ρt p q
  hopD-renᵗ V ρg ρd ρt p (sndᵗ q)  = hopD-renᵗ V ρg ρd ρt p q
  hopD-renᵗ V ρg ρd ρt p (inlᵗ a)  = hopD-renᵗ V ρg ρd ρt p a
  hopD-renᵗ V ρg ρd ρt p (inrᵗ a)  = hopD-renᵗ V ρg ρd ρt p a
  hopD-renᵗ V ρg ρd ρt p (caseᵗ sc l r)
    rewrite hopD-renᵗ V ρg ρd (ext∈ ρt) (ext-ix ρt p) l
          | hopD-renᵗ V ρg ρd (ext∈ ρt) (ext-ix ρt p) r
          | pm-renᵗ V 0 ρg ρd (ext∈ ρt) (ext-ix ρt p) l
          | pm-renᵗ V 0 ρg ρd (ext∈ ρt) (ext-ix ρt p) r
          | hopD-renᵗ V ρg ρd ρt p sc = refl
  hopD-renᵗ V ρg ρd ρt p (ifᵗ c a b)
    rewrite hopD-renᵗ V ρg ρd ρt p a | hopD-renᵗ V ρg ρd ρt p b = refl
  hopD-renᵗ V ρg ρd ρt p (primᵗ _ a) = refl
  hopD-renᵗ V ρg ρd ρt p (strmᵗ e)   = hopD-renᵉ V ρg ρd ρt p e

  hopD-renᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (V : ℕ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′) →
    (∀ {u} (x : u ∈ Θ) → varIx (ρt x) ≡ varIx x) →
    (ts : List (Tm Γ Δᵍ Δ Θ t)) →
    hopDᵗˢ V (renTms ρg ρd ρt ts) ≡ hopDᵗˢ V ts
  hopD-renᵗˢ V ρg ρd ρt p []       = refl
  hopD-renᵗˢ V ρg ρd ρt p (y ∷ ys)
    rewrite hopD-renᵗ V ρg ρd ρt p y | hopD-renᵗˢ V ρg ρd ρt p ys = refl

-- a reified value measures as the value did — the obs case is refl,
-- since reify of an observable IS strmᵗ of it — and weakening it in
-- changes nothing, since weakening out of the empty context moves no
-- position
hopD-wkReify : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ} (V : ℕ) (t : Ty) (v : Val Γ t) →
  hopDᵗ V (wkTm {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} (reify v)) ≡ hopDᵛ V t v
hopD-wkReify V unitᵗ    v        = refl
hopD-wkReify V boolᵗ    v        = refl
hopD-wkReify V natᵗ     v        = refl
hopD-wkReify V (s ×ᵗ t) (a , b) =
  cong₂ _⊔_ (hopD-wkReify V s a) (hopD-wkReify V t b)
hopD-wkReify V (s +ᵗ t) (inj₁ a) = hopD-wkReify V s a
hopD-wkReify V (s +ᵗ t) (inj₂ b) = hopD-wkReify V t b
hopD-wkReify V (obs t)  e        = hopD-renᵉ V (λ ()) (λ ()) (λ ()) (λ ()) e

-- AND THE SUM FIRES.  On the right injection the plug's depth has to be
-- paid for by the slope, so the slope must be at least 1 there — and it
-- is, because the substituted variable's position is length Θloc past
-- the local binders, which is exactly one of the indices the sum runs
-- over.  Three small facts: where the position lands, that it lands
-- inside the range, and that a sum with a hit is at least 1.
varIx-ix : ∀ {t} (Θloc : List Ty) {Θsub} (x : t ∈ Θloc ++ Θsub)
  {z : t ∈ Θsub} → ∈-++⁻ Θloc x ≡ inj₂ z → varIx x ≡ length Θloc + varIx z
varIx-ix []          x          refl = refl
varIx-ix (u ∷ Θloc) (here refl) ()
varIx-ix (u ∷ Θloc) (there x)   eq with ∈-++⁻ Θloc x in eq′
varIx-ix (u ∷ Θloc) (there x)   ()   | inj₁ y′
varIx-ix (u ∷ Θloc) (there x)   refl | inj₂ z′ = cong suc (varIx-ix Θloc x eq′)

varIx<len : ∀ {t} {Θ : List Ty} (z : t ∈ Θ) → varIx z < length Θ
varIx<len (here _)  = s≤s z≤n
varIx<len (there p) = s≤s (varIx<len p)

ifEq : ∀ (a b : ℕ) → a ≡ b → 1 ≤ (if a ≡ᵇ b then 1 else 0)
ifEq a b e with a ≡ᵇ b in q
... | true  = s≤s z≤n
... | false = ⊥-elim (subst T q (≡⇒≡ᵇ a b e))


-- (H0), PROVEN.  A coefficient is read at index 0 of the clause's own
-- binder — a LOCAL index — and this says substitution leaves every
-- local index alone.  The two pieces do the work: on the left
-- injection varIx is preserved, so a local variable reads the same;
-- on the right the plug is Θ-closed and weakened in, so pm-wkTm makes
-- it 0, and the original was 0 too because its position was past every
-- local binder.
--
-- Every binder clause needs the lemma at TWO indices: at suc k for the
-- body, and at 0 for the coefficient the clause multiplies by.  Both
-- are instances of the same statement, which is why the coefficient's
-- invariance falls out of the same induction rather than needing its
-- own.
mutual
  pm-subΘᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (V k : ℕ) (Θloc : List Ty)
    (σ : All (Val Γ) Θsub) (e : Exp Γ Δᵍ Δ (Θloc ++ Θsub) t) →
    k < length Θloc → pmᵉ V k (subΘExp Θloc σ e) ≡ pmᵉ V k e
  pm-subΘᵉ V k Θloc σ (input i)  h = refl
  pm-subΘᵉ V k Θloc σ (ofᵉ ts)   h = pm-subΘᵗˢ V k Θloc σ ts h
  pm-subΘᵉ V k Θloc σ emptyᵉ     h = refl
  pm-subΘᵉ V k Θloc σ (mapᵉ {s = s} f e) h
    rewrite pm-subΘᵗ V (suc k) (s ∷ Θloc) σ f (s≤s h)
          | pm-subΘᵗ V 0 (s ∷ Θloc) σ f (s≤s z≤n)
          | pm-subΘᵉ V k Θloc σ e h = refl
  pm-subΘᵉ V k Θloc σ (takeᵉ c e) h = pm-subΘᵉ V k Θloc σ e h
  pm-subΘᵉ V k Θloc σ (scanᵉ {s = s} {t = t} f z e) h
    rewrite pm-subΘᵗ V (suc k) ((t ×ᵗ s) ∷ Θloc) σ f (s≤s h)
          | pm-subΘᵗ V 0 ((t ×ᵗ s) ∷ Θloc) σ f (s≤s z≤n)
          | pm-subΘᵗ V k Θloc σ z h
          | pm-subΘᵉ V k Θloc σ e h = refl
  pm-subΘᵉ V k Θloc σ (mergeAllᵉ e)   h = pm-subΘᵉ V k Θloc σ e h
  pm-subΘᵉ V k Θloc σ (concatAllᵉ e)  h = pm-subΘᵉ V k Θloc σ e h
  pm-subΘᵉ V k Θloc σ (switchAllᵉ e)  h = pm-subΘᵉ V k Θloc σ e h
  pm-subΘᵉ V k Θloc σ (exhaustAllᵉ e) h = pm-subΘᵉ V k Θloc σ e h
  pm-subΘᵉ V k Θloc σ (μᵉ e)     h = pm-subΘᵉ V k Θloc σ e h
  pm-subΘᵉ V k Θloc σ (varᵉ x)   h = refl
  pm-subΘᵉ V k Θloc σ (deferᵉ e) h = refl

  pm-subΘᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (V k : ℕ) (Θloc : List Ty)
    (σ : All (Val Γ) Θsub) (tm : Tm Γ Δᵍ Δ (Θloc ++ Θsub) t) →
    k < length Θloc → pmᵗ V k (subΘTm Θloc σ tm) ≡ pmᵗ V k tm
  pm-subΘᵗ V k Θloc σ (varᵗ x) h with ∈-++⁻ Θloc x in eq
  ... | inj₁ y = cong (λ i → if i ≡ᵇ k then 1 else 0) (varIx-++ˡ Θloc x eq)
  ... | inj₂ z =
    trans (pm-wkTm V k (reify (lookupEnv σ z)))
          (sym (ifNeq (varIx x) k
                 (λ ix≡k → <-irrefl (sym ix≡k)
                             (≤-trans h (varIx-++ʳ Θloc x eq)))))
  pm-subΘᵗ V k Θloc σ unit̂       h = refl
  pm-subΘᵗ V k Θloc σ (bool̂ _)   h = refl
  pm-subΘᵗ V k Θloc σ (nat̂ _)    h = refl
  pm-subΘᵗ V k Θloc σ (pairᵗ a b) h
    rewrite pm-subΘᵗ V k Θloc σ a h | pm-subΘᵗ V k Θloc σ b h = refl
  pm-subΘᵗ V k Θloc σ (fstᵗ p) h = pm-subΘᵗ V k Θloc σ p h
  pm-subΘᵗ V k Θloc σ (sndᵗ p) h = pm-subΘᵗ V k Θloc σ p h
  pm-subΘᵗ V k Θloc σ (inlᵗ a) h = pm-subΘᵗ V k Θloc σ a h
  pm-subΘᵗ V k Θloc σ (inrᵗ a) h = pm-subΘᵗ V k Θloc σ a h
  pm-subΘᵗ V k Θloc σ (caseᵗ {s = s} {t = t} sc l r) h
    rewrite pm-subΘᵗ V (suc k) (s ∷ Θloc) σ l (s≤s h)
          | pm-subΘᵗ V (suc k) (t ∷ Θloc) σ r (s≤s h)
          | pm-subΘᵗ V 0 (s ∷ Θloc) σ l (s≤s z≤n)
          | pm-subΘᵗ V 0 (t ∷ Θloc) σ r (s≤s z≤n)
          | pm-subΘᵗ V k Θloc σ sc h = refl
  pm-subΘᵗ V k Θloc σ (ifᵗ c a b) h
    rewrite pm-subΘᵗ V k Θloc σ a h | pm-subΘᵗ V k Θloc σ b h = refl
  pm-subΘᵗ V k Θloc σ (primᵗ _ a) h = refl
  pm-subΘᵗ V k Θloc σ (strmᵗ e)   h = pm-subΘᵉ V k Θloc σ e h

  pm-subΘᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (V k : ℕ) (Θloc : List Ty)
    (σ : All (Val Γ) Θsub) (ts : List (Tm Γ Δᵍ Δ (Θloc ++ Θsub) t)) →
    k < length Θloc → pmᵗˢ V k (subΘTms Θloc σ ts) ≡ pmᵗˢ V k ts
  pm-subΘᵗˢ V k Θloc σ []       h = refl
  pm-subΘᵗˢ V k Θloc σ (y ∷ ys) h
    rewrite pm-subΘᵗ V k Θloc σ y h | pm-subΘᵗˢ V k Θloc σ ys h = refl

-- every value in an environment is bounded, POSITION BY POSITION
EnvHopDs : ∀ {n} {Γ : Ctx n} {Θ} (V : ℕ) → All (Val Γ) Θ → (ℕ → ℕ) → Set
EnvHopDs V []ᵃ                Ds = ⊤
EnvHopDs V (_∷ᵃ_ {x = t} v σ) Ds =
  (hopDᵛ V t v ≤ Ds 0) × EnvHopDs V σ (λ j → Ds (suc j))

-- the slope over a WHOLE environment: one pm per substituted variable,
-- read at the index that variable occupies once the local binders
-- between it and the root have been counted.  m is the environment's
-- length, k the offset where it starts.
-- …summed over one index range, WEIGHTED per position.  Each
-- substituted variable gets its own bound: one bound for the whole
-- environment is not enough, because evalWith's caseᵗ pushes the
-- SCRUTINEE's value onto the environment and that value can be deeper
-- than anything already in it (see (H2) below).
--
-- Slope and weight shift together at the head, which is what makes
-- pushing a value onto the environment line up on both sides at once.
sumW : (ℕ → ℕ) → (ℕ → ℕ) → ℕ → ℕ
sumW g w zero    = 0
sumW g w (suc m) = g 0 * w 0 + sumW (λ j → g (suc j)) (λ j → w (suc j)) m

-- a max of sums sits under the sum of maxes, termwise
⊔-+-split : ∀ x y u v → (x + y) ⊔ (u + v) ≤ (x ⊔ u) + (y ⊔ v)
⊔-+-split x y u v =
  ⊔-lub (+-mono-≤ (m≤m⊔n x u) (m≤m⊔n y v))
        (+-mono-≤ (m≤n⊔m x u) (m≤n⊔m y v))

-- FIVE GENERIC FACTS, and they replace the per-clause decomposition
-- lemmas entirely.  With the slope weighted, a hopD clause needs only
-- that the sum is additive, homogeneous, monotone, under a max, and
-- collects a hit; the clause's own shape then falls out by rewriting
-- pm's clause and applying these.  (An UNWEIGHTED sum needed one lemma
-- per clause, because the multiplication by D sat outside the sum where
-- it could not see the clause's structure.)
sumW-mono : ∀ (g h w : ℕ → ℕ) (m : ℕ) → (∀ j → g j ≤ h j) →
  sumW g w m ≤ sumW h w m
sumW-mono g h w zero    p = z≤n
sumW-mono g h w (suc m) p =
  +-mono-≤ (*-monoˡ-≤ (w 0) (p 0))
           (sumW-mono (λ j → g (suc j)) (λ j → h (suc j))
                      (λ j → w (suc j)) m (λ j → p (suc j)))

+-mix4 : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
+-mix4 = solve 4 (λ a b c d → (a :+ b) :+ (c :+ d) := (a :+ c) :+ (b :+ d)) refl

sumW-+ : ∀ (g h w : ℕ → ℕ) (m : ℕ) →
  sumW g w m + sumW h w m ≡ sumW (λ j → g j + h j) w m
sumW-+ g h w zero    = refl
sumW-+ g h w (suc m) =
  trans (+-mix4 (g 0 * w 0) (sumW (λ j → g (suc j)) (λ j → w (suc j)) m)
                (h 0 * w 0) (sumW (λ j → h (suc j)) (λ j → w (suc j)) m))
        (cong₂ _+_ (sym (*-distribʳ-+ (w 0) (g 0) (h 0)))
                   (sumW-+ (λ j → g (suc j)) (λ j → h (suc j))
                           (λ j → w (suc j)) m))

sumW-* : ∀ (c : ℕ) (g w : ℕ → ℕ) (m : ℕ) →
  c * sumW g w m ≡ sumW (λ j → c * g j) w m
sumW-* c g w zero    = *-zeroʳ c
sumW-* c g w (suc m) =
  trans (*-distribˡ-+ c (g 0 * w 0)
          (sumW (λ j → g (suc j)) (λ j → w (suc j)) m))
        (cong₂ _+_ (sym (*-assoc c (g 0) (w 0)))
                   (sumW-* c (λ j → g (suc j)) (λ j → w (suc j)) m))

sumW-⊔ : ∀ (g h w : ℕ → ℕ) (m : ℕ) →
  sumW g w m ⊔ sumW h w m ≤ sumW (λ j → g j ⊔ h j) w m
sumW-⊔ g h w zero    = z≤n
sumW-⊔ g h w (suc m) =
  ≤-trans (⊔-+-split (g 0 * w 0) (sumW (λ j → g (suc j)) (λ j → w (suc j)) m)
                     (h 0 * w 0) (sumW (λ j → h (suc j)) (λ j → w (suc j)) m))
          (+-mono-≤ (⊔-lub (*-monoˡ-≤ (w 0) (m≤m⊔n (g 0) (h 0)))
                           (*-monoˡ-≤ (w 0) (m≤n⊔m (g 0) (h 0))))
                    (sumW-⊔ (λ j → g (suc j)) (λ j → h (suc j))
                            (λ j → w (suc j)) m))

sumW-hit : ∀ (g w : ℕ → ℕ) (m j : ℕ) → j < m → 1 ≤ g j → w j ≤ sumW g w m
sumW-hit g w (suc m) zero    lt hit =
  ≤-trans (1*≤ (w 0) (g 0) hit)
          (m≤m+n (g 0 * w 0) (sumW (λ j → g (suc j)) (λ j → w (suc j)) m))
sumW-hit g w (suc m) (suc j) lt hit =
  ≤-trans (sumW-hit (λ i → g (suc i)) (λ i → w (suc i)) m j (≤-pred lt) hit)
          (m≤n+m (sumW (λ i → g (suc i)) (λ i → w (suc i)) m) (g 0 * w 0))

envHopDs-lookup : ∀ {n} {Γ : Ctx n} {Θ t} (V : ℕ) (Ds : ℕ → ℕ)
  (σ : All (Val Γ) Θ) → EnvHopDs V σ Ds → (z : t ∈ Θ) →
  hopDᵛ V t (lookupEnv σ z) ≤ Ds (varIx z)
envHopDs-lookup V Ds (v ∷ᵃ σ) (hv , hσ) (here refl) = hv
envHopDs-lookup V Ds (v ∷ᵃ σ) (hv , hσ) (there z)   =
  envHopDs-lookup V (λ j → Ds (suc j)) σ hσ z

-- the two regroupings the multiplying clauses need.  With the slope
-- weighted, D no longer appears — it is inside the sum
+*-mix : ∀ a s c b u → (a + s) + c * (b + u) ≡ (a + c * b) + (s + c * u)
+*-mix = solve 5
  (λ a s c b u → (a :+ s) :+ c :* (b :+ u) := (a :+ c :* b) :+ (s :+ c :* u))
  refl

*3-mix : ∀ p a s b t c u →
  p * ((a + s) + (b + t) + (c + u)) ≡ p * (a + b + c) + p * (s + t + u)
*3-mix = solve 7
  (λ p a s b t c u → p :* ((a :+ s) :+ (b :+ t) :+ (c :+ u))
                       := p :* (a :+ b :+ c) :+ p :* (s :+ t :+ u)) refl

-- a max of two bounded things is bounded by the max of the bounds with
-- the slopes maxed — the shape every `⊔` clause closes by
⊔-bound : ∀ {a b} (Ha Hb Sa Sb S : ℕ) →
  a ≤ Ha + Sa → b ≤ Hb + Sb → Sa ⊔ Sb ≤ S → a ⊔ b ≤ (Ha ⊔ Hb) + S
⊔-bound Ha Hb Sa Sb S bA bB bS =
  ≤-trans (⊔-mono-≤ bA bB)
          (≤-trans (⊔-+-split Ha Sa Hb Sb) (+-monoʳ-≤ (Ha ⊔ Hb) bS))

-- (H1), PROVEN.  hopD is affine in the substituted values' depths, with
-- pm as the slope — the statement phase 3 exists to establish, following
-- subΘ-countsᵉ/ᵗ's induction clause for clause: the same substitution
-- walked with the same multiplicity accounting, a different semiring at
-- the leaves.
--
-- Each multiplying clause rewrites its coefficient by (H0) — without
-- which the two sides would have different slopes and there would be
-- nothing to induct on — applies its IHs, and closes on one regrouping
-- plus sumW-+/sumW-*.  Each maximising clause goes through ⊔-bound and
-- sumW-⊔.  The varᵗ leaf is where the plug's own depth enters: on the
-- left injection both sides are 0; on the right the plug is bounded by
-- its position's weight, and the slope collects that weight because the
-- variable's position is exactly one of the indices the sum runs over.
mutual
  hopD-subΘᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (V : ℕ) (Ds : ℕ → ℕ)
    (Θloc : List Ty) (σ : All (Val Γ) Θsub)
    (e : Exp Γ Δᵍ Δ (Θloc ++ Θsub) t) → EnvHopDs V σ Ds →
    hopDᵉ V (subΘExp Θloc σ e)
      ≤ hopDᵉ V e
        + sumW (λ j → pmᵉ V (length Θloc + j) e) Ds (length Θsub)
  hopD-subΘᵉ V Ds Θloc σ (input i) hσ = z≤n
  hopD-subΘᵉ V Ds Θloc σ (ofᵉ ts)  hσ = hopD-subΘᵗˢ V Ds Θloc σ ts hσ
  hopD-subΘᵉ V Ds Θloc σ emptyᵉ    hσ = z≤n
  hopD-subΘᵉ {Θsub = Θsub} V Ds Θloc σ (mapᵉ {s = s} f e) hσ
    rewrite pm-subΘᵗ V 0 (s ∷ Θloc) σ f (s≤s z≤n) =
    ≤-trans (+-mono-≤ (hopD-subΘᵗ V Ds (s ∷ Θloc) σ f hσ)
                      (*-monoʳ-≤ C (hopD-subΘᵉ V Ds Θloc σ e hσ)))
    (≤-trans (≤-reflexive (+*-mix (hopDᵗ V f) Sf C (hopDᵉ V e) Se))
             (+-monoʳ-≤ (hopDᵗ V f + C * hopDᵉ V e)
               (≤-reflexive
                 (trans (cong (Sf +_) (sumW-* C (λ j → pmᵉ V (length Θloc + j) e) Ds
                                              (length Θsub)))
                        (sumW-+ (λ j → pmᵗ V (suc (length Θloc + j)) f)
                                (λ j → C * pmᵉ V (length Θloc + j) e)
                                Ds (length Θsub))))))
    where
    C  = pmᵗ V 0 f ⊔ 1
    Sf = sumW (λ j → pmᵗ V (suc (length Θloc + j)) f) Ds (length Θsub)
    Se = sumW (λ j → pmᵉ V (length Θloc + j) e) Ds (length Θsub)
  hopD-subΘᵉ V Ds Θloc σ (takeᵉ c e) hσ = hopD-subΘᵉ V Ds Θloc σ e hσ
  hopD-subΘᵉ {Θsub = Θsub} V Ds Θloc σ (scanᵉ {s = s} {t = t} f z e) hσ
    rewrite pm-subΘᵗ V 0 ((t ×ᵗ s) ∷ Θloc) σ f (s≤s z≤n) =
    ≤-trans (*-monoʳ-≤ P
              (+-mono-≤ (+-mono-≤ (hopD-subΘᵗ V Ds ((t ×ᵗ s) ∷ Θloc) σ f hσ)
                                  (hopD-subΘᵗ V Ds Θloc σ z hσ))
                        (hopD-subΘᵉ V Ds Θloc σ e hσ)))
    (≤-trans (≤-reflexive
               (*3-mix P (hopDᵗ V f) Sf (hopDᵗ V z) Sz (hopDᵉ V e) Se))
             (+-monoʳ-≤ (P * (hopDᵗ V f + hopDᵗ V z + hopDᵉ V e))
               (≤-reflexive
                 (trans (cong (P *_)
                          (trans (cong (_+ Se) (sumW-+ Gf Gz Ds (length Θsub)))
                                 (sumW-+ (λ j → Gf j + Gz j) Ge Ds (length Θsub))))
                        (sumW-* P (λ j → (Gf j + Gz j) + Ge j) Ds
                                (length Θsub))))))
    where
    P  = (2 + pmᵗ V 0 f) ^ V
    Gf = λ j → pmᵗ V (suc (length Θloc + j)) f
    Gz = λ j → pmᵗ V (length Θloc + j) z
    Ge = λ j → pmᵉ V (length Θloc + j) e
    Sf = sumW Gf Ds (length Θsub)
    Sz = sumW Gz Ds (length Θsub)
    Se = sumW Ge Ds (length Θsub)
  hopD-subΘᵉ V Ds Θloc σ (mergeAllᵉ e)   hσ = s≤s (hopD-subΘᵉ V Ds Θloc σ e hσ)
  hopD-subΘᵉ V Ds Θloc σ (concatAllᵉ e)  hσ = s≤s (hopD-subΘᵉ V Ds Θloc σ e hσ)
  hopD-subΘᵉ V Ds Θloc σ (switchAllᵉ e)  hσ = s≤s (hopD-subΘᵉ V Ds Θloc σ e hσ)
  hopD-subΘᵉ V Ds Θloc σ (exhaustAllᵉ e) hσ = s≤s (hopD-subΘᵉ V Ds Θloc σ e hσ)
  hopD-subΘᵉ V Ds Θloc σ (μᵉ e)     hσ = hopD-subΘᵉ V Ds Θloc σ e hσ
  hopD-subΘᵉ V Ds Θloc σ (varᵉ x)   hσ = z≤n
  hopD-subΘᵉ V Ds Θloc σ (deferᵉ e) hσ = z≤n

  hopD-subΘᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (V : ℕ) (Ds : ℕ → ℕ)
    (Θloc : List Ty) (σ : All (Val Γ) Θsub)
    (tm : Tm Γ Δᵍ Δ (Θloc ++ Θsub) t) → EnvHopDs V σ Ds →
    hopDᵗ V (subΘTm Θloc σ tm)
      ≤ hopDᵗ V tm
        + sumW (λ j → pmᵗ V (length Θloc + j) tm) Ds (length Θsub)
  hopD-subΘᵗ {Γ = Γ} {Δᵍ = Δᵍ} {Δ = Δ} {Θsub = Θsub}
             V Ds Θloc σ (varᵗ x) hσ with ∈-++⁻ Θloc x in eq
  ... | inj₁ y = z≤n
  ... | inj₂ z =
    ≤-trans (≤-reflexive (hopD-wkReify V _ (lookupEnv σ z)))
    (≤-trans (envHopDs-lookup V Ds σ hσ z)
             (sumW-hit (λ j → pmᵗ {Γ = Γ} {Δᵍ = Δᵍ} {Δ = Δ}
                                  V (length Θloc + j) (varᵗ x))
                       Ds (length Θsub) (varIx z) (varIx<len z)
                       (ifEq (varIx x) (length Θloc + varIx z)
                             (varIx-ix Θloc x eq))))
  hopD-subΘᵗ V Ds Θloc σ unit̂     hσ = z≤n
  hopD-subΘᵗ V Ds Θloc σ (bool̂ _) hσ = z≤n
  hopD-subΘᵗ V Ds Θloc σ (nat̂ _)  hσ = z≤n
  hopD-subΘᵗ {Θsub = Θsub} V Ds Θloc σ (pairᵗ a b) hσ =
    ⊔-bound (hopDᵗ V a) (hopDᵗ V b)
            (sumW (λ j → pmᵗ V (length Θloc + j) a) Ds (length Θsub))
            (sumW (λ j → pmᵗ V (length Θloc + j) b) Ds (length Θsub))
            (sumW (λ j → pmᵗ V (length Θloc + j) (pairᵗ a b)) Ds (length Θsub))
            (hopD-subΘᵗ V Ds Θloc σ a hσ) (hopD-subΘᵗ V Ds Θloc σ b hσ)
            (sumW-⊔ (λ j → pmᵗ V (length Θloc + j) a)
                    (λ j → pmᵗ V (length Θloc + j) b) Ds (length Θsub))
  hopD-subΘᵗ V Ds Θloc σ (fstᵗ q) hσ = hopD-subΘᵗ V Ds Θloc σ q hσ
  hopD-subΘᵗ V Ds Θloc σ (sndᵗ q) hσ = hopD-subΘᵗ V Ds Θloc σ q hσ
  hopD-subΘᵗ V Ds Θloc σ (inlᵗ a) hσ = hopD-subΘᵗ V Ds Θloc σ a hσ
  hopD-subΘᵗ V Ds Θloc σ (inrᵗ a) hσ = hopD-subΘᵗ V Ds Θloc σ a hσ
  hopD-subΘᵗ {Θsub = Θsub} V Ds Θloc σ (caseᵗ {s = s} {t = t} sc l r) hσ
    rewrite pm-subΘᵗ V 0 (s ∷ Θloc) σ l (s≤s z≤n)
          | pm-subΘᵗ V 0 (t ∷ Θloc) σ r (s≤s z≤n) =
    ≤-trans (+-mono-≤
              (⊔-bound (hopDᵗ V l) (hopDᵗ V r) SL SR (SL ⊔ SR)
                       (hopD-subΘᵗ V Ds (s ∷ Θloc) σ l hσ)
                       (hopD-subΘᵗ V Ds (t ∷ Θloc) σ r hσ) ≤-refl)
              (*-monoʳ-≤ C (hopD-subΘᵗ V Ds Θloc σ sc hσ)))
    (≤-trans (≤-reflexive
               (+*-mix (hopDᵗ V l ⊔ hopDᵗ V r) (SL ⊔ SR) C (hopDᵗ V sc) SSC))
             (+-monoʳ-≤ ((hopDᵗ V l ⊔ hopDᵗ V r) + C * hopDᵗ V sc)
               (≤-trans (+-mono-≤ (sumW-⊔ GL GR Ds (length Θsub))
                                  (≤-reflexive (sumW-* C GSC Ds (length Θsub))))
                        (≤-reflexive
                          (sumW-+ (λ j → GL j ⊔ GR j) (λ j → C * GSC j)
                                  Ds (length Θsub))))))
    where
    C   = pmᵗ V 0 l ⊔ pmᵗ V 0 r ⊔ 1
    GL  = λ j → pmᵗ V (suc (length Θloc + j)) l
    GR  = λ j → pmᵗ V (suc (length Θloc + j)) r
    GSC = λ j → pmᵗ V (length Θloc + j) sc
    SL  = sumW GL Ds (length Θsub)
    SR  = sumW GR Ds (length Θsub)
    SSC = sumW GSC Ds (length Θsub)
  hopD-subΘᵗ {Θsub = Θsub} V Ds Θloc σ (ifᵗ c a b) hσ =
    ⊔-bound (hopDᵗ V a) (hopDᵗ V b)
            (sumW (λ j → pmᵗ V (length Θloc + j) a) Ds (length Θsub))
            (sumW (λ j → pmᵗ V (length Θloc + j) b) Ds (length Θsub))
            (sumW (λ j → pmᵗ V (length Θloc + j) (ifᵗ c a b)) Ds (length Θsub))
            (hopD-subΘᵗ V Ds Θloc σ a hσ) (hopD-subΘᵗ V Ds Θloc σ b hσ)
            (sumW-⊔ (λ j → pmᵗ V (length Θloc + j) a)
                    (λ j → pmᵗ V (length Θloc + j) b) Ds (length Θsub))
  hopD-subΘᵗ V Ds Θloc σ (primᵗ _ a) hσ = z≤n
  hopD-subΘᵗ V Ds Θloc σ (strmᵗ e)   hσ = hopD-subΘᵉ V Ds Θloc σ e hσ

  hopD-subΘᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (V : ℕ) (Ds : ℕ → ℕ)
    (Θloc : List Ty) (σ : All (Val Γ) Θsub)
    (ts : List (Tm Γ Δᵍ Δ (Θloc ++ Θsub) t)) → EnvHopDs V σ Ds →
    hopDᵗˢ V (subΘTms Θloc σ ts)
      ≤ hopDᵗˢ V ts
        + sumW (λ j → pmᵗˢ V (length Θloc + j) ts) Ds (length Θsub)
  hopD-subΘᵗˢ V Ds Θloc σ []       hσ = z≤n
  hopD-subΘᵗˢ {Θsub = Θsub} V Ds Θloc σ (y ∷ ys) hσ =
    ⊔-bound (hopDᵗ V y) (hopDᵗˢ V ys)
            (sumW (λ j → pmᵗ V (length Θloc + j) y) Ds (length Θsub))
            (sumW (λ j → pmᵗˢ V (length Θloc + j) ys) Ds (length Θsub))
            (sumW (λ j → pmᵗˢ V (length Θloc + j) (y ∷ ys)) Ds (length Θsub))
            (hopD-subΘᵗ V Ds Θloc σ y hσ) (hopD-subΘᵗˢ V Ds Θloc σ ys hσ)
            (sumW-⊔ (λ j → pmᵗ V (length Θloc + j) y)
                    (λ j → pmᵗˢ V (length Θloc + j) ys) Ds (length Θsub))

-- (H2), PROVEN.  The affine bound at evalWith, which is what the walk's
-- frames actually call: a mapᵉ frame's applyFn, an ofᵉ frame's evalTm.
-- Its strmᵗ clause is (H1) at Θloc ≡ [] — closeUnderFn IS subΘExp [] —
-- and its varᵗ and projection clauses read the value off the
-- environment.
--
-- caseᵗ is the clause that EXTENDS the environment, and the reason every
-- statement in this block is weighted rather than carrying a single
-- bound.  The scrutinee's value is pushed on at index 0 and can be
-- deeper than anything already there; with one bound the branch's IH
-- would have to be taken at that depth for ALL positions, and the
-- branch's slope for the outer variables would get multiplied by the
-- scrutinee's depth — a product with no counterpart on the right,
-- because hopD's caseᵗ clause prices the scrutinee by the branch's
-- coefficient AT INDEX 0 only.  Weighted, it closes termwise: index 0's
-- slope pays for the scrutinee (a branch's pmᵗ V 0 is under the caseᵗ
-- coefficient by construction) and the shifted slopes pay for the outer
-- variables, each under the ⊔ of the two branches'.
case-shape : ∀ a b c d → a + ((b + c) + d) ≡ (a + b) + (d + c)
case-shape = solve 4
  (λ a b c d → a :+ ((b :+ c) :+ d) := (a :+ b) :+ (d :+ c)) refl

hopD-evalWith : ∀ {n} {Γ : Ctx n} {Θ u} (V : ℕ) (Ds : ℕ → ℕ)
  (tm : Tm Γ [] [] Θ u) (env : All (Val Γ) Θ) → EnvHopDs V env Ds →
  hopDᵛ V u (evalWith tm env)
    ≤ hopDᵗ V tm + sumW (λ j → pmᵗ V j tm) Ds (length Θ)
hopD-evalWith {Γ = Γ} {Θ = Θ} V Ds (varᵗ x) env hσ =
  ≤-trans (envHopDs-lookup V Ds env hσ x)
          (sumW-hit (λ j → pmᵗ {Γ = Γ} {Δᵍ = []} {Δ = []} V j (varᵗ x))
                    Ds (length Θ) (varIx x)
                    (varIx<len x) (ifEq (varIx x) (varIx x) refl))
hopD-evalWith V Ds unit̂     env hσ = z≤n
hopD-evalWith V Ds (bool̂ _) env hσ = z≤n
hopD-evalWith V Ds (nat̂ _)  env hσ = z≤n
hopD-evalWith {Θ = Θ} V Ds (pairᵗ a b) env hσ =
  ⊔-bound (hopDᵗ V a) (hopDᵗ V b)
          (sumW (λ j → pmᵗ V j a) Ds (length Θ))
          (sumW (λ j → pmᵗ V j b) Ds (length Θ))
          (sumW (λ j → pmᵗ V j (pairᵗ a b)) Ds (length Θ))
          (hopD-evalWith V Ds a env hσ) (hopD-evalWith V Ds b env hσ)
          (sumW-⊔ (λ j → pmᵗ V j a) (λ j → pmᵗ V j b) Ds (length Θ))
hopD-evalWith V Ds (fstᵗ q) env hσ =
  ≤-trans (m≤m⊔n _ _) (hopD-evalWith V Ds q env hσ)
hopD-evalWith V Ds (sndᵗ q) env hσ =
  ≤-trans (m≤n⊔m _ _) (hopD-evalWith V Ds q env hσ)
hopD-evalWith V Ds (inlᵗ a) env hσ = hopD-evalWith V Ds a env hσ
hopD-evalWith V Ds (inrᵗ a) env hσ = hopD-evalWith V Ds a env hσ
-- the scrutinee's VALUE and the bound on it are abstracted together, so
-- the branch sees the bound already specialised to its own injection
hopD-evalWith {Θ = Θ} V Ds (caseᵗ {s = s} {t = t} sc l r) env hσ
  with evalWith sc env | hopD-evalWith V Ds sc env hσ
... | inj₁ x | ihsc =
  ≤-trans (hopD-evalWith V (λ { zero → hopDᵛ V s x ; (suc j) → Ds j })
                         l (x ∷ᵃ env) (≤-refl , hσ))
  (≤-trans (+-mono-≤ (m≤m⊔n (hopDᵗ V l) (hopDᵗ V r))
             (+-mono-≤
               (≤-trans (*-monoˡ-≤ (hopDᵛ V s x) pm0l≤C)
                        (≤-trans (*-monoʳ-≤ C ihsc)
                                 (≤-reflexive (*-distribˡ-+ C (hopDᵗ V sc) SSC))))
               (sumW-mono GL (λ j → GL j ⊔ GR j) Ds (length Θ)
                          (λ j → m≤m⊔n (GL j) (GR j)))))
  (≤-trans (≤-reflexive
             (case-shape (hopDᵗ V l ⊔ hopDᵗ V r) (C * hopDᵗ V sc)
                         (C * SSC) SLR))
           (+-monoʳ-≤ ((hopDᵗ V l ⊔ hopDᵗ V r) + C * hopDᵗ V sc) fold)))
  where
  C    = pmᵗ V 0 l ⊔ pmᵗ V 0 r ⊔ 1
  GL   = λ j → pmᵗ V (suc j) l
  GR   = λ j → pmᵗ V (suc j) r
  GSC  = λ j → pmᵗ V j sc
  SSC  = sumW GSC Ds (length Θ)
  SLR  = sumW (λ j → GL j ⊔ GR j) Ds (length Θ)
  pm0l≤C : pmᵗ V 0 l ≤ C
  pm0l≤C = ≤-trans (m≤m⊔n (pmᵗ V 0 l) (pmᵗ V 0 r))
                   (m≤m⊔n (pmᵗ V 0 l ⊔ pmᵗ V 0 r) 1)
  fold : SLR + C * SSC ≤ sumW (λ j → (GL j ⊔ GR j) + C * GSC j) Ds (length Θ)
  fold = ≤-reflexive
    (trans (cong (SLR +_) (sumW-* C GSC Ds (length Θ)))
           (sumW-+ (λ j → GL j ⊔ GR j) (λ j → C * GSC j) Ds (length Θ)))
... | inj₂ y | ihsc =
  ≤-trans (hopD-evalWith V (λ { zero → hopDᵛ V t y ; (suc j) → Ds j })
                         r (y ∷ᵃ env) (≤-refl , hσ))
  (≤-trans (+-mono-≤ (m≤n⊔m (hopDᵗ V l) (hopDᵗ V r))
             (+-mono-≤
               (≤-trans (*-monoˡ-≤ (hopDᵛ V t y) pm0r≤C)
                        (≤-trans (*-monoʳ-≤ C ihsc)
                                 (≤-reflexive (*-distribˡ-+ C (hopDᵗ V sc) SSC))))
               (sumW-mono GR (λ j → GL j ⊔ GR j) Ds (length Θ)
                          (λ j → m≤n⊔m (GL j) (GR j)))))
  (≤-trans (≤-reflexive
             (case-shape (hopDᵗ V l ⊔ hopDᵗ V r) (C * hopDᵗ V sc)
                         (C * SSC) SLR))
           (+-monoʳ-≤ ((hopDᵗ V l ⊔ hopDᵗ V r) + C * hopDᵗ V sc) fold)))
  where
  C    = pmᵗ V 0 l ⊔ pmᵗ V 0 r ⊔ 1
  GL   = λ j → pmᵗ V (suc j) l
  GR   = λ j → pmᵗ V (suc j) r
  GSC  = λ j → pmᵗ V j sc
  SSC  = sumW GSC Ds (length Θ)
  SLR  = sumW (λ j → GL j ⊔ GR j) Ds (length Θ)
  pm0r≤C : pmᵗ V 0 r ≤ C
  pm0r≤C = ≤-trans (m≤n⊔m (pmᵗ V 0 l) (pmᵗ V 0 r))
                   (m≤m⊔n (pmᵗ V 0 l ⊔ pmᵗ V 0 r) 1)
  fold : SLR + C * SSC ≤ sumW (λ j → (GL j ⊔ GR j) + C * GSC j) Ds (length Θ)
  fold = ≤-reflexive
    (trans (cong (SLR +_) (sumW-* C GSC Ds (length Θ)))
           (sumW-+ (λ j → GL j ⊔ GR j) (λ j → C * GSC j) Ds (length Θ)))
hopD-evalWith {Θ = Θ} V Ds (ifᵗ c a b) env hσ with evalWith c env
... | true =
  ≤-trans (hopD-evalWith V Ds a env hσ)
          (+-mono-≤ (m≤m⊔n (hopDᵗ V a) (hopDᵗ V b))
                    (sumW-mono (λ j → pmᵗ V j a)
                               (λ j → pmᵗ V j a ⊔ pmᵗ V j b) Ds (length Θ)
                               (λ j → m≤m⊔n (pmᵗ V j a) (pmᵗ V j b))))
... | false =
  ≤-trans (hopD-evalWith V Ds b env hσ)
          (+-mono-≤ (m≤n⊔m (hopDᵗ V a) (hopDᵗ V b))
                    (sumW-mono (λ j → pmᵗ V j b)
                               (λ j → pmᵗ V j a ⊔ pmᵗ V j b) Ds (length Θ)
                               (λ j → m≤n⊔m (pmᵗ V j a) (pmᵗ V j b))))
-- every PrimOp lands in natᵗ or boolᵗ, so its value carries no hops —
-- one clause per operator, since the result type is what makes that true
hopD-evalWith V Ds (primᵗ add  a) env hσ = z≤n
hopD-evalWith V Ds (primᵗ sub  a) env hσ = z≤n
hopD-evalWith V Ds (primᵗ mul  a) env hσ = z≤n
hopD-evalWith V Ds (primᵗ eqᵖ  a) env hσ = z≤n
hopD-evalWith V Ds (primᵗ ltᵖ  a) env hσ = z≤n
hopD-evalWith V Ds (primᵗ notᵖ a) env hσ = z≤n
-- and the two strmᵗ clauses: a closed template IS its own value, and an
-- open one is closed by substitution — which is (H1) at Θloc ≡ []
hopD-evalWith V Ds (strmᵗ e) []ᵃ       hσ =
  ≤-reflexive (sym (+-identityʳ (hopDᵉ V e)))
hopD-evalWith V Ds (strmᵗ e) (v ∷ᵃ vs) hσ =
  hopD-subΘᵉ V Ds [] (v ∷ᵃ vs) e hσ

-- a one-value environment: the weighted sum collapses to exactly the pm
-- the mapᵉ clause's coefficient is built from
hopD-applyFn : ∀ {n} {Γ : Ctx n} {s u} (V : ℕ)
  (f : Fn Γ [] [] [] s u) (v : Val Γ s) →
  hopDᵛ V u (applyFn f v) ≤ hopDᵗ V f + (pmᵗ V 0 f ⊔ 1) * hopDᵛ V s v
hopD-applyFn {s = s} V f v =
  ≤-trans (hopD-evalWith V (λ _ → hopDᵛ V s v) f (v ∷ᵃ []ᵃ) (≤-refl , tt))
          (+-monoʳ-≤ (hopDᵗ V f)
            (≤-trans (≤-reflexive (+-identityʳ (pmᵗ V 0 f * hopDᵛ V s v)))
                     (*-monoˡ-≤ (hopDᵛ V s v) (m≤m⊔n (pmᵗ V 0 f) 1))))

-- THE CONSUMER, and the whole point of the block: a mapᵉ frame's
-- emission sits under the mapᵉ's OWN hop depth, given only that the
-- source's value sat under the source's.  That is burstHopD? at the
-- mapᵉ clause, with the arithmetic already done — and with hopDᵉ
-- (mergeAllᵉ c) ≡ suc (hopDᵉ c) definitional, it is also the hop
-- edge's strictness.
hopD-map-emit : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s u} (V : ℕ)
  (f : Tm Γ Δᵍ Δ (s ∷ Θ) u) (b : Exp Γ Δᵍ Δ Θ s) (v : Val Γ s) →
  (f₀ : Fn Γ [] [] [] s u) → hopDᵗ V f₀ ≤ hopDᵗ V f → pmᵗ V 0 f₀ ≤ pmᵗ V 0 f →
  hopDᵛ V s v ≤ hopDᵉ V b →
  hopDᵛ V u (applyFn f₀ v) ≤ hopDᵉ V (mapᵉ f b)
hopD-map-emit V f b v f₀ hf hp hv =
  ≤-trans (hopD-applyFn V f₀ v)
          (+-mono-≤ hf (*-mono-≤ (⊔-mono-≤ hp ≤-refl) hv))

------------------------------------------------------------------
-- THE LEDGER'S INPUT — the subΘ multiset equation, exact: the
-- instantiated inner multiset is the template's plus the plug
-- shells, class for class.  With shellSize-subΘ (host preserved)
-- this fully characterizes instantiation at the measure level.
------------------------------------------------------------------

⊕ᵛ-medial : ∀ {m} (a b c d : Vec ℕ m) →
  (a ⊕ᵛ b) ⊕ᵛ (c ⊕ᵛ d) ≡ (a ⊕ᵛ c) ⊕ᵛ (b ⊕ᵛ d)
⊕ᵛ-medial a b c d =
  trans (⊕ᵛ-assoc a b (c ⊕ᵛ d))
  (trans (cong (a ⊕ᵛ_) (trans (sym (⊕ᵛ-assoc b c d))
                       (trans (cong (_⊕ᵛ d) (⊕ᵛ-comm b c))
                              (⊕ᵛ-assoc c b d))))
         (sym (⊕ᵛ-assoc a c (b ⊕ᵛ d))))

-- the 2-way composition step, shared by every two-child clause:
-- counts (X′ ++ Y′) from recursive equations for X′ and Y′
counts-2way : ∀ B (X′ Y′ X Y P Q : List ℕ) →
  counts B X′ ≡ counts B X ⊕ᵛ counts B P →
  counts B Y′ ≡ counts B Y ⊕ᵛ counts B Q →
  counts B (X′ ++ Y′) ≡ counts B (X ++ Y) ⊕ᵛ counts B (P ++ Q)
counts-2way B X′ Y′ X Y P Q ex ey =
  trans (counts-++ B X′ Y′)
  (trans (cong₂ _⊕ᵛ_ ex ey)
  (trans (⊕ᵛ-medial (counts B X) (counts B P) (counts B Y) (counts B Q))
         (sym (cong₂ _⊕ᵛ_ (counts-++ B X Y) (counts-++ B P Q)))))

-- the 3-way step: fold the right two children first, then medial
counts-3way : ∀ B (X′ Y′ Z′ X Y Z P Q R : List ℕ) →
  counts B X′ ≡ counts B X ⊕ᵛ counts B P →
  counts B Y′ ≡ counts B Y ⊕ᵛ counts B Q →
  counts B Z′ ≡ counts B Z ⊕ᵛ counts B R →
  counts B (X′ ++ Y′ ++ Z′) ≡
    counts B (X ++ Y ++ Z) ⊕ᵛ counts B (P ++ Q ++ R)
counts-3way B X′ Y′ Z′ X Y Z P Q R ex ey ez =
  counts-2way B X′ (Y′ ++ Z′) X (Y ++ Z) P (Q ++ R) ex
    (counts-2way B Y′ Z′ Y Z Q R ey ez)

mutual
  subΘ-countsᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (B : ℕ) (Θloc : List Ty)
    (σ : All (Val Γ) Θsub) (e : Exp Γ Δᵍ Δ (Θloc ++ Θsub) t) →
    counts B (innerᵉ (subΘExp Θloc σ e)) ≡
      counts B (innerᵉ e) ⊕ᵛ counts B (plugsᵉ Θloc σ e)
  subΘ-countsᵉ B Θloc σ (input i)       = sym (⊕ᵛ-identityˡ zerosᵛ)
  subΘ-countsᵉ B Θloc σ (ofᵉ ts)        = subΘ-countsᵗˢ B Θloc σ ts
  subΘ-countsᵉ B Θloc σ emptyᵉ          = sym (⊕ᵛ-identityˡ zerosᵛ)
  subΘ-countsᵉ B Θloc σ (mapᵉ {s = s} f e) =
    counts-2way B (innerᵗ (subΘTm (s ∷ Θloc) σ f))
                  (innerᵉ (subΘExp Θloc σ e))
                  (innerᵗ f) (innerᵉ e)
                  (plugsᵗ (s ∷ Θloc) σ f) (plugsᵉ Θloc σ e)
      (subΘ-countsᵗ B (s ∷ Θloc) σ f) (subΘ-countsᵉ B Θloc σ e)
  subΘ-countsᵉ B Θloc σ (takeᵉ c e)     =
    counts-2way B (innerᵗ (subΘTm Θloc σ c))
                  (innerᵉ (subΘExp Θloc σ e))
                  (innerᵗ c) (innerᵉ e)
                  (plugsᵗ Θloc σ c) (plugsᵉ Θloc σ e)
      (subΘ-countsᵗ B Θloc σ c) (subΘ-countsᵉ B Θloc σ e)
  subΘ-countsᵉ B Θloc σ (scanᵉ {s = s} {t = t} f z e) =
    counts-3way B (innerᵗ (subΘTm ((t ×ᵗ s) ∷ Θloc) σ f))
                  (innerᵗ (subΘTm Θloc σ z))
                  (innerᵉ (subΘExp Θloc σ e))
                  (innerᵗ f) (innerᵗ z) (innerᵉ e)
                  (plugsᵗ ((t ×ᵗ s) ∷ Θloc) σ f)
                  (plugsᵗ Θloc σ z) (plugsᵉ Θloc σ e)
      (subΘ-countsᵗ B ((t ×ᵗ s) ∷ Θloc) σ f)
      (subΘ-countsᵗ B Θloc σ z) (subΘ-countsᵉ B Θloc σ e)
  subΘ-countsᵉ B Θloc σ (mergeAllᵉ e)   = subΘ-countsᵉ B Θloc σ e
  subΘ-countsᵉ B Θloc σ (concatAllᵉ e)  = subΘ-countsᵉ B Θloc σ e
  subΘ-countsᵉ B Θloc σ (switchAllᵉ e)  = subΘ-countsᵉ B Θloc σ e
  subΘ-countsᵉ B Θloc σ (exhaustAllᵉ e) = subΘ-countsᵉ B Θloc σ e
  subΘ-countsᵉ B Θloc σ (μᵉ e)          = subΘ-countsᵉ B Θloc σ e
  subΘ-countsᵉ B Θloc σ (varᵉ x)        = sym (⊕ᵛ-identityˡ zerosᵛ)
  subΘ-countsᵉ B Θloc σ (deferᵉ e)      = sym (⊕ᵛ-identityˡ zerosᵛ)

  subΘ-countsᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (B : ℕ) (Θloc : List Ty)
    (σ : All (Val Γ) Θsub) (tm : Tm Γ Δᵍ Δ (Θloc ++ Θsub) t) →
    counts B (innerᵗ (subΘTm Θloc σ tm)) ≡
      counts B (innerᵗ tm) ⊕ᵛ counts B (plugsᵗ Θloc σ tm)
  subΘ-countsᵗ B Θloc σ (varᵗ x) with ∈-++⁻ Θloc x
  ... | inj₁ y = sym (⊕ᵛ-identityˡ zerosᵛ)
  ... | inj₂ z =
    trans (cong (counts B)
            (trans (inner-renᵗ (λ ()) (λ ()) (λ ())
                               (reify (lookupEnv σ z)))
                   (reify-inner _ (lookupEnv σ z))))
          (sym (⊕ᵛ-identityˡ (counts B (shellsᵛ _ (lookupEnv σ z)))))
  subΘ-countsᵗ B Θloc σ unit̂          = sym (⊕ᵛ-identityˡ zerosᵛ)
  subΘ-countsᵗ B Θloc σ (bool̂ _)      = sym (⊕ᵛ-identityˡ zerosᵛ)
  subΘ-countsᵗ B Θloc σ (nat̂ _)       = sym (⊕ᵛ-identityˡ zerosᵛ)
  subΘ-countsᵗ B Θloc σ (pairᵗ a b)   =
    counts-2way B (innerᵗ (subΘTm Θloc σ a))
                  (innerᵗ (subΘTm Θloc σ b))
                  (innerᵗ a) (innerᵗ b)
                  (plugsᵗ Θloc σ a) (plugsᵗ Θloc σ b)
      (subΘ-countsᵗ B Θloc σ a) (subΘ-countsᵗ B Θloc σ b)
  subΘ-countsᵗ B Θloc σ (fstᵗ p)      = subΘ-countsᵗ B Θloc σ p
  subΘ-countsᵗ B Θloc σ (sndᵗ p)      = subΘ-countsᵗ B Θloc σ p
  subΘ-countsᵗ B Θloc σ (inlᵗ a)      = subΘ-countsᵗ B Θloc σ a
  subΘ-countsᵗ B Θloc σ (inrᵗ a)      = subΘ-countsᵗ B Θloc σ a
  subΘ-countsᵗ B Θloc σ (caseᵗ {s = s} {t = t} sc l r) =
    counts-3way B (innerᵗ (subΘTm Θloc σ sc))
                  (innerᵗ (subΘTm (s ∷ Θloc) σ l))
                  (innerᵗ (subΘTm (t ∷ Θloc) σ r))
                  (innerᵗ sc) (innerᵗ l) (innerᵗ r)
                  (plugsᵗ Θloc σ sc) (plugsᵗ (s ∷ Θloc) σ l)
                  (plugsᵗ (t ∷ Θloc) σ r)
      (subΘ-countsᵗ B Θloc σ sc)
      (subΘ-countsᵗ B (s ∷ Θloc) σ l) (subΘ-countsᵗ B (t ∷ Θloc) σ r)
  subΘ-countsᵗ B Θloc σ (ifᵗ c a b)   =
    counts-3way B (innerᵗ (subΘTm Θloc σ c))
                  (innerᵗ (subΘTm Θloc σ a))
                  (innerᵗ (subΘTm Θloc σ b))
                  (innerᵗ c) (innerᵗ a) (innerᵗ b)
                  (plugsᵗ Θloc σ c) (plugsᵗ Θloc σ a)
                  (plugsᵗ Θloc σ b)
      (subΘ-countsᵗ B Θloc σ c)
      (subΘ-countsᵗ B Θloc σ a) (subΘ-countsᵗ B Θloc σ b)
  subΘ-countsᵗ B Θloc σ (primᵗ _ a)   = subΘ-countsᵗ B Θloc σ a
  subΘ-countsᵗ B Θloc σ (strmᵗ e)     =
    trans (cong₂ _⊕ᵛ_ (cong (oneAt B) (shellSize-subΘ Θloc σ e))
                      (subΘ-countsᵉ B Θloc σ e))
          (sym (⊕ᵛ-assoc (oneAt B (shellSizeᵉ e))
                         (counts B (innerᵉ e))
                         (counts B (plugsᵉ Θloc σ e))))

  subΘ-countsᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (B : ℕ) (Θloc : List Ty)
    (σ : All (Val Γ) Θsub) (ts : List (Tm Γ Δᵍ Δ (Θloc ++ Θsub) t)) →
    counts B (innerᵗˢ (subΘTms Θloc σ ts)) ≡
      counts B (innerᵗˢ ts) ⊕ᵛ counts B (plugsᵗˢ Θloc σ ts)
  subΘ-countsᵗˢ B Θloc σ []       = sym (⊕ᵛ-identityˡ zerosᵛ)
  subΘ-countsᵗˢ B Θloc σ (y ∷ ys) =
    counts-2way B (innerᵗ (subΘTm Θloc σ y))
                  (innerᵗˢ (subΘTms Θloc σ ys))
                  (innerᵗ y) (innerᵗˢ ys)
                  (plugsᵗ Θloc σ y) (plugsᵗˢ Θloc σ ys)
      (subΘ-countsᵗ B Θloc σ y) (subΘ-countsᵗˢ B Θloc σ ys)

------------------------------------------------------------------
-- SYNC-LINEARITY, PROVEN: deliveries ≤ syntactic occurrences.
-- subΘ COPIES trees — one copy of the plugged value per Θ-var
-- occurrence — so an instantiation can multiply a stored value's
-- shells only by the occurrence count of the template, which is
-- itself capped by the template's sync-reachable syntax
-- (occs≤syncᵉ).  With the exact cardinality bookkeeping
-- (inner-len-subΘ, the length shadow of the subΘ multiset
-- equation), this bounds an instantiated value's entry sum BEFORE
-- the store re-caps it: length shells ≤ template size + occs · V —
-- the ledger's cardinality half at every applyFn/evalWith hop.
------------------------------------------------------------------

-- per-entry cardinality cap on an environment: each plugged value
-- delivers at most V shells per occurrence
EnvLen : ∀ {n} {Γ : Ctx n} {Θ} (V : ℕ) → All (Val Γ) Θ → Set
EnvLen V []ᵃ                = ⊤
EnvLen V (_∷ᵃ_ {x = t} v σ) = (length (shellsᵛ t v) ≤ V) × EnvLen V σ

envLen-lookup : ∀ {n} {Γ : Ctx n} {Θ t} (V : ℕ) (σ : All (Val Γ) Θ) →
  EnvLen V σ → (z : t ∈ Θ) → length (shellsᵛ t (lookupEnv σ z)) ≤ V
envLen-lookup V (v ∷ᵃ σ) (hv , hσ) (here refl) = hv
envLen-lookup V (v ∷ᵃ σ) (hv , hσ) (there z)   = envLen-lookup V σ hσ z

mutual
  plugs-lenᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (V : ℕ) (Θloc : List Ty)
    (σ : All (Val Γ) Θsub) (e : Exp Γ Δᵍ Δ (Θloc ++ Θsub) t) →
    EnvLen V σ → length (plugsᵉ Θloc σ e) ≤ occsᵉ e * V
  plugs-lenᵉ V Θloc σ (input i)       hσ = z≤n
  plugs-lenᵉ V Θloc σ (ofᵉ ts)        hσ = plugs-lenᵗˢ V Θloc σ ts hσ
  plugs-lenᵉ V Θloc σ emptyᵉ          hσ = z≤n
  plugs-lenᵉ V Θloc σ (mapᵉ {s = s} f e) hσ
    rewrite length-++ (plugsᵗ (s ∷ Θloc) σ f) {plugsᵉ Θloc σ e}
          | *-distribʳ-+ V (occsᵗ f) (occsᵉ e) =
    +-mono-≤ (plugs-lenᵗ V (s ∷ Θloc) σ f hσ) (plugs-lenᵉ V Θloc σ e hσ)
  plugs-lenᵉ V Θloc σ (takeᵉ c e)     hσ
    rewrite length-++ (plugsᵗ Θloc σ c) {plugsᵉ Θloc σ e}
          | *-distribʳ-+ V (occsᵗ c) (occsᵉ e) =
    +-mono-≤ (plugs-lenᵗ V Θloc σ c hσ) (plugs-lenᵉ V Θloc σ e hσ)
  plugs-lenᵉ V Θloc σ (scanᵉ {s = s} {t = t} f z e) hσ
    rewrite length-++ (plugsᵗ ((t ×ᵗ s) ∷ Θloc) σ f)
                      {plugsᵗ Θloc σ z ++ plugsᵉ Θloc σ e}
          | length-++ (plugsᵗ Θloc σ z) {plugsᵉ Θloc σ e}
          | *-distribʳ-+ V (occsᵗ f + occsᵗ z) (occsᵉ e)
          | *-distribʳ-+ V (occsᵗ f) (occsᵗ z) =
    ≤-trans (≤-reflexive (sym (+-assoc
              (length (plugsᵗ ((t ×ᵗ s) ∷ Θloc) σ f))
              (length (plugsᵗ Θloc σ z)) _)))
            (+-mono-≤ (+-mono-≤ (plugs-lenᵗ V ((t ×ᵗ s) ∷ Θloc) σ f hσ)
                                (plugs-lenᵗ V Θloc σ z hσ))
                      (plugs-lenᵉ V Θloc σ e hσ))
  plugs-lenᵉ V Θloc σ (mergeAllᵉ e)   hσ = plugs-lenᵉ V Θloc σ e hσ
  plugs-lenᵉ V Θloc σ (concatAllᵉ e)  hσ = plugs-lenᵉ V Θloc σ e hσ
  plugs-lenᵉ V Θloc σ (switchAllᵉ e)  hσ = plugs-lenᵉ V Θloc σ e hσ
  plugs-lenᵉ V Θloc σ (exhaustAllᵉ e) hσ = plugs-lenᵉ V Θloc σ e hσ
  plugs-lenᵉ V Θloc σ (μᵉ e)          hσ = plugs-lenᵉ V Θloc σ e hσ
  plugs-lenᵉ V Θloc σ (varᵉ x)        hσ = z≤n
  plugs-lenᵉ V Θloc σ (deferᵉ e)      hσ = z≤n

  plugs-lenᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (V : ℕ) (Θloc : List Ty)
    (σ : All (Val Γ) Θsub) (tm : Tm Γ Δᵍ Δ (Θloc ++ Θsub) t) →
    EnvLen V σ → length (plugsᵗ Θloc σ tm) ≤ occsᵗ tm * V
  plugs-lenᵗ V Θloc σ (varᵗ x) hσ with ∈-++⁻ Θloc x
  ... | inj₁ y = z≤n
  ... | inj₂ z =
    ≤-trans (envLen-lookup V σ hσ z) (≤-reflexive (sym (+-identityʳ V)))
  plugs-lenᵗ V Θloc σ unit̂          hσ = z≤n
  plugs-lenᵗ V Θloc σ (bool̂ _)      hσ = z≤n
  plugs-lenᵗ V Θloc σ (nat̂ _)       hσ = z≤n
  plugs-lenᵗ V Θloc σ (pairᵗ a b)   hσ
    rewrite length-++ (plugsᵗ Θloc σ a) {plugsᵗ Θloc σ b}
          | *-distribʳ-+ V (occsᵗ a) (occsᵗ b) =
    +-mono-≤ (plugs-lenᵗ V Θloc σ a hσ) (plugs-lenᵗ V Θloc σ b hσ)
  plugs-lenᵗ V Θloc σ (fstᵗ p)      hσ = plugs-lenᵗ V Θloc σ p hσ
  plugs-lenᵗ V Θloc σ (sndᵗ p)      hσ = plugs-lenᵗ V Θloc σ p hσ
  plugs-lenᵗ V Θloc σ (inlᵗ a)      hσ = plugs-lenᵗ V Θloc σ a hσ
  plugs-lenᵗ V Θloc σ (inrᵗ a)      hσ = plugs-lenᵗ V Θloc σ a hσ
  plugs-lenᵗ V Θloc σ (caseᵗ {s = s} {t = t} sc l r) hσ
    rewrite length-++ (plugsᵗ Θloc σ sc)
                      {plugsᵗ (s ∷ Θloc) σ l ++ plugsᵗ (t ∷ Θloc) σ r}
          | length-++ (plugsᵗ (s ∷ Θloc) σ l) {plugsᵗ (t ∷ Θloc) σ r}
          | *-distribʳ-+ V (occsᵗ sc + occsᵗ l) (occsᵗ r)
          | *-distribʳ-+ V (occsᵗ sc) (occsᵗ l) =
    ≤-trans (≤-reflexive (sym (+-assoc (length (plugsᵗ Θloc σ sc))
                                       (length (plugsᵗ (s ∷ Θloc) σ l)) _)))
            (+-mono-≤ (+-mono-≤ (plugs-lenᵗ V Θloc σ sc hσ)
                                (plugs-lenᵗ V (s ∷ Θloc) σ l hσ))
                      (plugs-lenᵗ V (t ∷ Θloc) σ r hσ))
  plugs-lenᵗ V Θloc σ (ifᵗ c a b)   hσ
    rewrite length-++ (plugsᵗ Θloc σ c) {plugsᵗ Θloc σ a ++ plugsᵗ Θloc σ b}
          | length-++ (plugsᵗ Θloc σ a) {plugsᵗ Θloc σ b}
          | *-distribʳ-+ V (occsᵗ c + occsᵗ a) (occsᵗ b)
          | *-distribʳ-+ V (occsᵗ c) (occsᵗ a) =
    ≤-trans (≤-reflexive (sym (+-assoc (length (plugsᵗ Θloc σ c))
                                       (length (plugsᵗ Θloc σ a)) _)))
            (+-mono-≤ (+-mono-≤ (plugs-lenᵗ V Θloc σ c hσ)
                                (plugs-lenᵗ V Θloc σ a hσ))
                      (plugs-lenᵗ V Θloc σ b hσ))
  plugs-lenᵗ V Θloc σ (primᵗ _ a)   hσ = plugs-lenᵗ V Θloc σ a hσ
  plugs-lenᵗ V Θloc σ (strmᵗ e)     hσ = plugs-lenᵉ V Θloc σ e hσ

  plugs-lenᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (V : ℕ) (Θloc : List Ty)
    (σ : All (Val Γ) Θsub) (ts : List (Tm Γ Δᵍ Δ (Θloc ++ Θsub) t)) →
    EnvLen V σ → length (plugsᵗˢ Θloc σ ts) ≤ occsᵗˢ ts * V
  plugs-lenᵗˢ V Θloc σ []       hσ = z≤n
  plugs-lenᵗˢ V Θloc σ (y ∷ ys) hσ
    rewrite length-++ (plugsᵗ Θloc σ y) {plugsᵗˢ Θloc σ ys}
          | *-distribʳ-+ V (occsᵗ y) (occsᵗˢ ys) =
    +-mono-≤ (plugs-lenᵗ V Θloc σ y hσ) (plugs-lenᵗˢ V Θloc σ ys hσ)

-- occurrences are syntactically counted: no template delivers more
-- copies than its sync-reachable size
mutual
  occs≤syncᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (e : Exp Γ Δᵍ Δ Θ t) →
    occsᵉ e ≤ syncSizeᵉ e
  occs≤syncᵉ (input i)       = z≤n
  occs≤syncᵉ (ofᵉ ts)        = ≤-trans (occs≤syncᵗˢ ts) (n≤1+n _)
  occs≤syncᵉ emptyᵉ          = z≤n
  occs≤syncᵉ (mapᵉ f e)      =
    ≤-trans (+-mono-≤ (occs≤syncᵗ f) (occs≤syncᵉ e)) (n≤1+n _)
  occs≤syncᵉ (takeᵉ c e)     =
    ≤-trans (+-mono-≤ (occs≤syncᵗ c) (occs≤syncᵉ e)) (n≤1+n _)
  occs≤syncᵉ (scanᵉ f z e)   =
    ≤-trans (+-mono-≤ (+-mono-≤ (occs≤syncᵗ f) (occs≤syncᵗ z))
                      (occs≤syncᵉ e))
            (n≤1+n _)
  occs≤syncᵉ (mergeAllᵉ e)   = ≤-trans (occs≤syncᵉ e) (n≤1+n _)
  occs≤syncᵉ (concatAllᵉ e)  = ≤-trans (occs≤syncᵉ e) (n≤1+n _)
  occs≤syncᵉ (switchAllᵉ e)  = ≤-trans (occs≤syncᵉ e) (n≤1+n _)
  occs≤syncᵉ (exhaustAllᵉ e) = ≤-trans (occs≤syncᵉ e) (n≤1+n _)
  occs≤syncᵉ (μᵉ e)          = ≤-trans (occs≤syncᵉ e) (n≤1+n _)
  occs≤syncᵉ (varᵉ x)        = z≤n
  occs≤syncᵉ (deferᵉ e)      = z≤n

  occs≤syncᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (tm : Tm Γ Δᵍ Δ Θ t) →
    occsᵗ tm ≤ syncSizeᵗ tm
  occs≤syncᵗ (varᵗ x)      = ≤-refl
  occs≤syncᵗ unit̂          = z≤n
  occs≤syncᵗ (bool̂ _)      = z≤n
  occs≤syncᵗ (nat̂ _)       = z≤n
  occs≤syncᵗ (pairᵗ a b)   =
    ≤-trans (+-mono-≤ (occs≤syncᵗ a) (occs≤syncᵗ b)) (n≤1+n _)
  occs≤syncᵗ (fstᵗ p)      = ≤-trans (occs≤syncᵗ p) (n≤1+n _)
  occs≤syncᵗ (sndᵗ p)      = ≤-trans (occs≤syncᵗ p) (n≤1+n _)
  occs≤syncᵗ (inlᵗ a)      = ≤-trans (occs≤syncᵗ a) (n≤1+n _)
  occs≤syncᵗ (inrᵗ a)      = ≤-trans (occs≤syncᵗ a) (n≤1+n _)
  occs≤syncᵗ (caseᵗ s l r) =
    ≤-trans (+-mono-≤ (+-mono-≤ (occs≤syncᵗ s) (occs≤syncᵗ l))
                      (occs≤syncᵗ r))
            (n≤1+n _)
  occs≤syncᵗ (ifᵗ c a b)   =
    ≤-trans (+-mono-≤ (+-mono-≤ (occs≤syncᵗ c) (occs≤syncᵗ a))
                      (occs≤syncᵗ b))
            (n≤1+n _)
  occs≤syncᵗ (primᵗ _ a)   = ≤-trans (occs≤syncᵗ a) (n≤1+n _)
  occs≤syncᵗ (strmᵗ e)     = ≤-trans (occs≤syncᵉ e) (n≤1+n _)

  occs≤syncᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (ts : List (Tm Γ Δᵍ Δ Θ t)) →
    occsᵗˢ ts ≤ syncSizeᵗˢ ts
  occs≤syncᵗˢ []       = z≤n
  occs≤syncᵗˢ (y ∷ ys) = +-mono-≤ (occs≤syncᵗ y) (occs≤syncᵗˢ ys)

-- the length shadow of the subΘ multiset equation, EXACT:
-- instantiation adds precisely the plugged shells to the inner
-- multiset's cardinality (read the equation through totᵛ at B = 0)
inner-len-subΘ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (Θloc : List Ty)
  (σ : All (Val Γ) Θsub) (e : Exp Γ Δᵍ Δ (Θloc ++ Θsub) t) →
  length (innerᵉ (subΘExp Θloc σ e)) ≡
    length (innerᵉ e) + length (plugsᵉ Θloc σ e)
inner-len-subΘ Θloc σ e =
  trans (sym (totᵛ-counts 0 (innerᵉ (subΘExp Θloc σ e))))
  (trans (cong totᵛ (subΘ-countsᵉ 0 Θloc σ e))
  (trans (totᵛ-⊕ᵛ (counts 0 (innerᵉ e)) (counts 0 (plugsᵉ Θloc σ e)))
         (cong₂ _+_ (totᵛ-counts 0 (innerᵉ e))
                    (totᵛ-counts 0 (plugsᵉ Θloc σ e)))))

-- sync-linearity, packaged for the hop: an instantiated template's
-- shell count — its entry sum, the rank bridge's side condition —
-- is the template's syntax plus occurrences · per-value cap, before
-- any store re-cap
subΘ-shells-len : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (V : ℕ) (Θloc : List Ty)
  (σ : All (Val Γ) Θsub) (e : Exp Γ Δᵍ Δ (Θloc ++ Θsub) t) →
  EnvLen V σ →
  length (shellsᵉ (subΘExp Θloc σ e)) ≤ sizeᵉ e + occsᵉ e * V
subΘ-shells-len V Θloc σ e hσ =
  ≤-trans (≤-reflexive (cong suc (inner-len-subΘ Θloc σ e)))
          (+-mono-≤ (inner-lenᵉ e) (plugs-lenᵉ V Θloc σ e hσ))

------------------------------------------------------------------
-- THE SEED INEQUALITY, PROVEN: the contract's whole demand — under
-- one product by dBound-bound — fits the seeded budget's literal
-- head plus tower at instant 0.  The engine (prod≤3pow) is generic:
-- for any store bound V ≥ 2, (1+V)(1+R)(1+U) with R = (1+V)^(1+V)
-- and U ≤ V sits within THREE exponential stories above V — exactly
-- the three stories syncBudget's tower height carries above
-- sizeBudgetAt's (the "(4+sz) vs (1+sz)" gap, now theorem-backed at
-- the burst; the id > 0 instances are cascadeGo-wet's obligation).
------------------------------------------------------------------

1≤2^ : ∀ k → 1 ≤ 2 ^ k
1≤2^ k = ≤-trans (s≤s z≤n) (n<2^n k)

suc-2^ : ∀ k → suc (2 ^ k) ≤ 2 ^ suc k
suc-2^ k = ≤-trans (+-monoˡ-≤ (2 ^ k) (1≤2^ k))
                   (≤-reflexive (cong (2 ^ k +_) (sym (+-identityʳ (2 ^ k)))))

k+2≤2^k : ∀ k → 2 ≤ k → k + 2 ≤ 2 ^ k
k+2≤2^k (suc zero)          (s≤s ())
k+2≤2^k (suc (suc zero))    _ = ≤ᵇ⇒≤ 4 4 tt
k+2≤2^k (suc (suc (suc j))) _ =
  ≤-trans (s≤s (k+2≤2^k (suc (suc j)) (s≤s (s≤s z≤n))))
          (suc-2^ (suc (suc j)))

2k≤2^k : ∀ k → 2 ≤ k → k + k ≤ 2 ^ k
2k≤2^k (suc zero)          (s≤s ())
2k≤2^k (suc (suc zero))    _ = ≤ᵇ⇒≤ 4 4 tt
2k≤2^k (suc (suc (suc j))) _ =
  ≤-trans (≤-reflexive (cong suc (+-suc (suc (suc j)) (suc (suc j)))))
  (+-mono-≤ (^-monoʳ-≤ 2 {x = 1} {y = suc (suc j)} (s≤s z≤n))
            (≤-trans (2k≤2^k (suc (suc j)) (s≤s (s≤s z≤n)))
                     (≤-reflexive (sym (+-identityʳ (2 ^ suc (suc j)))))))

-- THE SQUARE's side condition.  The retired occurrence count made
-- hopR's exponent a polynomial and this was 3k ≤ 2^k (true from 4);
-- pm's scanᵉ clause makes it an exponential, (1+V)^(1+V), so the slack
-- identity below closes on (V+2)^(V+3) and wants (V+2)² ≤ 2^V — true
-- from V ≥ 6, where at V ≡ 6 it is exactly 64 ≤ 64.  V is a tower of
-- 2s of height ≥ 5, so 6 is as free as 4 was.
--
-- The step needs no side condition of its own: (j+9)² ≤ 2·(j+8)² holds
-- at every j, with j²+14j+47 to spare.  Only the base is delicate, and
-- it is delicate by exactly zero.
sq≤2^ : ∀ k → 6 ≤ k → (2 + k) * (2 + k) ≤ 2 ^ k
sq≤2^ zero                                         ()
sq≤2^ (suc zero)                                   (s≤s ())
sq≤2^ (suc (suc zero))                             (s≤s (s≤s ()))
sq≤2^ (suc (suc (suc zero)))                       (s≤s (s≤s (s≤s ())))
sq≤2^ (suc (suc (suc (suc zero))))                 (s≤s (s≤s (s≤s (s≤s ()))))
sq≤2^ (suc (suc (suc (suc (suc zero)))))           (s≤s (s≤s (s≤s (s≤s (s≤s ())))))
sq≤2^ (suc (suc (suc (suc (suc (suc zero))))))     _ = ≤ᵇ⇒≤ 64 64 tt
-- the recursive call spells its argument out: the termination checker
-- is syntactic and would not see through a where-binding
sq≤2^ (suc (suc (suc (suc (suc (suc (suc j))))))) _ =
  ≤-trans (≤-trans (m≤m+n ((9 + j) * (9 + j)) (j * j + 14 * j + 47))
                   (≤-reflexive ident))
          (*-monoʳ-≤ 2 (sq≤2^ (suc (suc (suc (suc (suc (suc j))))))
                              (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))) 
  where
  ident : (9 + j) * (9 + j) + (j * j + 14 * j + 47)
        ≡ 2 * ((8 + j) * (8 + j))
  ident = solve 1
    (λ v → ((con 9 :+ v) :* (con 9 :+ v))
             :+ (v :* v :+ con 14 :* v :+ con 47)
             := con 2 :* ((con 8 :+ v) :* (con 8 :+ v)))
    refl j

2+k≤2^k : ∀ k → 2 ≤ k → 2 + k ≤ 2 ^ k
2+k≤2^k k h = ≤-trans (≤-reflexive (+-comm 2 k)) (k+2≤2^k k h)

prod≤3pow : ∀ (V U : ℕ) → 6 ≤ V → U ≤ V →
  suc (suc V * suc (hopR V) * suc U) ≤ 2 ^ (2 ^ (2 ^ V))
prod≤3pow V U 6≤V U≤V =
  ≤-trans (s≤s prod≤2F) (≤-trans (suc-2^ F) (^-monoʳ-≤ 2 sucF≤))
  where
  2≤V : 2 ≤ V
  2≤V = ≤-trans (≤ᵇ⇒≤ 2 6 tt) 6≤V

  Q = V * (suc V ^ suc V)
  F = V + suc Q + V
  X = (2 + V) ^ (2 + V)

  hV : suc V ≤ 2 ^ V
  hV = n<2^n V

  hB : 2 + V ≤ 2 ^ V
  hB = 2+k≤2^k V 2≤V

  hR : suc (hopR V) ≤ 2 ^ suc Q
  hR = ≤-trans (s≤s (≤-trans (^-monoˡ-≤ (suc V ^ suc V) hB)
                             (≤-reflexive (^-*-assoc 2 V (suc V ^ suc V)))))
               (suc-2^ Q)

  hU : suc U ≤ 2 ^ V
  hU = ≤-trans (s≤s U≤V) hV

  prod≤2F : suc V * suc (hopR V) * suc U ≤ 2 ^ F
  prod≤2F = ≤-trans (*-mono-≤ (*-mono-≤ hV hR) hU)
    (≤-reflexive
      (trans (cong (_* 2 ^ V) (sym (^-distribˡ-+-* 2 V (suc Q))))
             (sym (^-distribˡ-+-* 2 (V + suc Q) V))))

  -- Q sits under X: V ≤ 2+V and (1+V)^(1+V) ≤ (2+V)^(1+V), and
  -- (2+V)·(2+V)^(1+V) IS X
  Q≤ : Q ≤ X
  Q≤ = *-mono-≤ (≤-trans (n≤1+n V) (n≤1+n (suc V)))
                (^-monoˡ-≤ (suc V) (n≤1+n (suc V)))

  -- and so does the linear part, via the square
  sq≤X : (2 + V) * (2 + V) ≤ X
  sq≤X = *-monoʳ-≤ (2 + V)
           (≤-trans (≤-reflexive (sym (*-identityʳ (2 + V))))
                    (*-monoʳ-≤ (2 + V) (1≤pow (suc V) V)))

  lin≤ : 2 + (V + V) ≤ X
  lin≤ = ≤-trans (≤-trans (m≤m+n (2 + (V + V)) (2 + 2 * V + V * V))
                          (≤-reflexive linId))
                 sq≤X
    where
    linId : (2 + (V + V)) + (2 + 2 * V + V * V) ≡ (2 + V) * (2 + V)
    linId = solve 1
      (λ v → (con 2 :+ (v :+ v)) :+ (con 2 :+ con 2 :* v :+ v :* v)
               := (con 2 :+ v) :* (con 2 :+ v))
      refl V

  -- V·(V+3) ≤ (V+2)², with V+4 to spare — the exponent's own slack
  expo≤ : V * (3 + V) ≤ 2 ^ V
  expo≤ = ≤-trans (≤-trans (m≤m+n (V * (3 + V)) (V + 4))
                           (≤-reflexive expId))
                  (sq≤2^ V 6≤V)
    where
    expId : V * (3 + V) + (V + 4) ≡ (2 + V) * (2 + V)
    expId = solve 1
      (λ v → v :* (con 3 :+ v) :+ (v :+ con 4) := (con 2 :+ v) :* (con 2 :+ v))
      refl V

  reshape : suc F ≡ (2 + (V + V)) + Q
  reshape = solve 2
    (λ v q → con 1 :+ ((v :+ (con 1 :+ q)) :+ v)
               := (con 2 :+ (v :+ v)) :+ q)
    refl V Q

  -- X + X ≤ (2+V)·X, and (2+V)·X IS (2+V)^(3+V)
  twoX : X + X ≤ (2 + V) ^ (3 + V)
  twoX = ≤-trans (≤-reflexive (sym (cong (X +_) (+-identityʳ X))))
                 (*-monoˡ-≤ X (≤-trans (≤ᵇ⇒≤ 2 2 tt) (m≤m+n 2 V)))

  sucF≤ : suc F ≤ 2 ^ (2 ^ V)
  sucF≤ =
    ≤-trans (≤-reflexive reshape)
    (≤-trans (+-mono-≤ lin≤ Q≤)
    (≤-trans twoX
    (≤-trans (^-monoˡ-≤ (3 + V) hB)
    (≤-trans (≤-reflexive (^-*-assoc 2 V (3 + V)))
             (^-monoʳ-≤ 2 expo≤)))))

-- the burst's seed step: at instant 0 the demand product sits under
-- the budget's tower summand alone.  The demand anchors at the
-- ENTRY store bound here (the burst is instant 0's whole walk);
-- prod≤3pow's three stories land inside the gas tower's height
-- (7+sz)·2 with 7+sz to spare
seed-covers : ∀ (sz U : ℕ) → U ≤ sz →
  let V = towerℕ ((4 + sz) * 1) in
  suc (suc V * suc (hopR V) * suc U)
    ≤ 2 ^ (sz * 1 * 1) + towerℕ ((7 + sz) * 2)
seed-covers sz U U≤sz
  rewrite *-identityʳ sz | *-identityʳ sz | *-identityʳ (4 + sz) =
  ≤-trans (prod≤3pow (towerℕ (4 + sz)) U 6≤V U≤V)
  (≤-trans (towerℕ-mono (m≤m*n (7 + sz) 2))
           (m≤n+m (towerℕ ((7 + sz) * 2)) (2 ^ sz)))
  where
  -- towerℕ 3 ≡ 16, and the seed's height is 4 + sz
  6≤V : 6 ≤ towerℕ (4 + sz)
  6≤V = ≤-trans (≤ᵇ⇒≤ 6 16 tt) (towerℕ-mono {3} {4 + sz} (s≤s (s≤s (s≤s z≤n))))
  U≤V : U ≤ towerℕ (4 + sz)
  U≤V = ≤-trans U≤sz (≤-trans (m≤n+m sz 4) (k≤towerℕ (4 + sz)))

------------------------------------------------------------------
-- GRINDER QUEUE — mechanical waypoints with settled statements,
-- postulated for the grinder to discharge one at a time.  Each is
-- a structural induction or ≤-chain shaped exactly like a proven
-- neighbor (named per item).  None is consumed yet: the consumers
-- arrive with the subscribeE-wet clause grind (G1-G4 feed the
-- store-landing bounds at applyFn/evalWith sites — closeUnderFn IS
-- subΘExp [], so obs-typed eval results are direct subΘ instances)
-- and the cascade-side seed step (G5).  Replace postulates with
-- proofs; do NOT reshape statements.
------------------------------------------------------------------

-- the store-side cap on an environment — what stBounded? hands
-- out; the shell caps (EnvLen, EnvCap) both follow from it
EnvSize : ∀ {n} {Γ : Ctx n} {Θ} (V : ℕ) → All (Val Γ) Θ → Set
EnvSize V []ᵃ                = ⊤
EnvSize V (_∷ᵃ_ {x = t} v σ) = (sizeᵛ t v ≤ V) × EnvSize V σ

-- an env capped at V looks up values capped at V
envSize-lookup : ∀ {n} {Γ : Ctx n} {Θ t} (V : ℕ) (σ : All (Val Γ) Θ) →
  EnvSize V σ → (z : t ∈ Θ) → sizeᵛ t (lookupEnv σ z) ≤ V
envSize-lookup V (v ∷ᵃ σ) (hv , hσ) (here refl) = hv
envSize-lookup V (v ∷ᵃ σ) (hv , hσ) (there z)   = envSize-lookup V σ hσ z

-- (G2) renamings are size-invariant: renExp/renTm/renTms map every
-- constructor 1-1 (weakening included) and sizeᵉ/ᵗ/ᵗˢ count constructors
-- plus subterm sizes, so each clause is refl (leaf) or cong/cong₂ over the
-- recursive calls — the sizeᵉ analog of shellSize-ren/inner-ren.  Renaming
-- values are irrelevant to size, so the ext∈/++Ren/(λ ()) shifts pass through.
mutual
  size-renᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t}
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′)
    (e : Exp Γ Δᵍ Δ Θ t) → sizeᵉ (renExp ρg ρd ρt e) ≡ sizeᵉ e
  size-renᵉ ρg ρd ρt (input i)       = refl
  size-renᵉ ρg ρd ρt (ofᵉ ts)        = cong suc (size-renᵗˢ ρg ρd ρt ts)
  size-renᵉ ρg ρd ρt emptyᵉ          = refl
  size-renᵉ ρg ρd ρt (mapᵉ f e)      =
    cong suc (cong₂ _+_ (size-renᵗ ρg ρd (ext∈ ρt) f) (size-renᵉ ρg ρd ρt e))
  size-renᵉ ρg ρd ρt (takeᵉ c e)     =
    cong suc (cong₂ _+_ (size-renᵗ ρg ρd ρt c) (size-renᵉ ρg ρd ρt e))
  size-renᵉ ρg ρd ρt (scanᵉ f z e)   =
    cong suc (cong₂ _+_ (cong₂ _+_ (size-renᵗ ρg ρd (ext∈ ρt) f) (size-renᵗ ρg ρd ρt z))
                        (size-renᵉ ρg ρd ρt e))
  size-renᵉ ρg ρd ρt (mergeAllᵉ e)   = cong suc (size-renᵉ ρg ρd ρt e)
  size-renᵉ ρg ρd ρt (concatAllᵉ e)  = cong suc (size-renᵉ ρg ρd ρt e)
  size-renᵉ ρg ρd ρt (switchAllᵉ e)  = cong suc (size-renᵉ ρg ρd ρt e)
  size-renᵉ ρg ρd ρt (exhaustAllᵉ e) = cong suc (size-renᵉ ρg ρd ρt e)
  size-renᵉ ρg ρd ρt (μᵉ e)          = cong suc (size-renᵉ (ext∈ ρg) ρd ρt e)
  size-renᵉ ρg ρd ρt (varᵉ x)        = refl
  size-renᵉ ρg ρd ρt (deferᵉ e)      = cong suc (size-renᵉ (λ ()) (++Ren ρg ρd) ρt e)

  size-renᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t}
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′)
    (tm : Tm Γ Δᵍ Δ Θ t) → sizeᵗ (renTm ρg ρd ρt tm) ≡ sizeᵗ tm
  size-renᵗ ρg ρd ρt (varᵗ x)      = refl
  size-renᵗ ρg ρd ρt unit̂          = refl
  size-renᵗ ρg ρd ρt (bool̂ _)      = refl
  size-renᵗ ρg ρd ρt (nat̂ _)       = refl
  size-renᵗ ρg ρd ρt (pairᵗ a b)   =
    cong suc (cong₂ _+_ (size-renᵗ ρg ρd ρt a) (size-renᵗ ρg ρd ρt b))
  size-renᵗ ρg ρd ρt (fstᵗ p)      = cong suc (size-renᵗ ρg ρd ρt p)
  size-renᵗ ρg ρd ρt (sndᵗ p)      = cong suc (size-renᵗ ρg ρd ρt p)
  size-renᵗ ρg ρd ρt (inlᵗ a)      = cong suc (size-renᵗ ρg ρd ρt a)
  size-renᵗ ρg ρd ρt (inrᵗ a)      = cong suc (size-renᵗ ρg ρd ρt a)
  size-renᵗ ρg ρd ρt (caseᵗ s l r) =
    cong suc (cong₂ _+_ (cong₂ _+_ (size-renᵗ ρg ρd ρt s) (size-renᵗ ρg ρd (ext∈ ρt) l))
                        (size-renᵗ ρg ρd (ext∈ ρt) r))
  size-renᵗ ρg ρd ρt (ifᵗ c a b)   =
    cong suc (cong₂ _+_ (cong₂ _+_ (size-renᵗ ρg ρd ρt c) (size-renᵗ ρg ρd ρt a))
                        (size-renᵗ ρg ρd ρt b))
  size-renᵗ ρg ρd ρt (primᵗ _ a)   = cong suc (size-renᵗ ρg ρd ρt a)
  size-renᵗ ρg ρd ρt (strmᵗ e)     = cong suc (size-renᵉ ρg ρd ρt e)

  size-renᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t}
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′)
    (ts : List (Tm Γ Δᵍ Δ Θ t)) → sizeᵗˢ (renTms ρg ρd ρt ts) ≡ sizeᵗˢ ts
  size-renᵗˢ ρg ρd ρt []       = refl
  size-renᵗˢ ρg ρd ρt (y ∷ ys) =
    cong₂ _+_ (size-renᵗ ρg ρd ρt y) (size-renᵗˢ ρg ρd ρt ys)

-- small doubling identities (solver) and the "suc absorbs into the double" step
private
  dbl : ∀ X → 2 * X ≡ X + X
  dbl = solve 1 (λ x → con 2 :* x := x :+ x) refl
  two-distrib : ∀ a b → 2 * (a + b) ≡ 2 * a + 2 * b
  two-distrib = solve 2 (λ a b → con 2 :* (a :+ b) := con 2 :* a :+ con 2 :* b) refl

bump : ∀ X → suc (2 * X) ≤ 2 * suc X
bump X = subst (suc (2 * X) ≤_) (sym (*-suc 2 X)) (n≤1+n (suc (2 * X)))

-- (G3) reification at most doubles: pair/sum/base map 1-1 into a size-1-larger
-- term but the value grows the same suc, so `bump` absorbs it; the obs base
-- (strmᵗ e over sizeᵛ = sizeᵉ e) is the only off-by-one and sizeᵉ-pos (1 ≤
-- sizeᵉ e) covers it.  Induction on the type/value like shellsᵛ-len.
size-reify : ∀ {n} {Γ : Ctx n} (t : Ty) (v : Val Γ t) →
  sizeᵗ (reify v) ≤ 2 * sizeᵛ t v
size-reify unitᵗ   _        = s≤s z≤n
size-reify boolᵗ   _        = s≤s z≤n
size-reify natᵗ    _        = s≤s z≤n
size-reify (s ×ᵗ t) (a , b) =
  ≤-trans (s≤s (+-mono-≤ (size-reify s a) (size-reify t b)))
          (subst (λ w → suc w ≤ 2 * suc (sizeᵛ s a + sizeᵛ t b))
                 (two-distrib (sizeᵛ s a) (sizeᵛ t b))
                 (bump (sizeᵛ s a + sizeᵛ t b)))
size-reify (s +ᵗ t) (inj₁ a) = ≤-trans (s≤s (size-reify s a)) (bump (sizeᵛ s a))
size-reify (s +ᵗ t) (inj₂ b) = ≤-trans (s≤s (size-reify t b)) (bump (sizeᵛ t b))
size-reify (obs t)  e =
  subst (suc (sizeᵉ e) ≤_) (sym (dbl (sizeᵉ e)))
        (+-monoˡ-≤ (sizeᵉ e) (sizeᵉ-pos e))

-- (G4) helpers.  Each subΘ clause is a `suc (Σ subterm sizes)` over a
-- constructor that maps 1-1, so the bound composes multiplicatively:
--   suc S ≤ suc N * M   from   S ≤ N * M   and   1 ≤ M      (sucmul)
-- where the S ≤ N * M part sums the IHs and distributes M (sum2 / sum3).
sucmul : ∀ {S} (N M : ℕ) → S ≤ N * M → 1 ≤ M → suc S ≤ suc N * M
sucmul N M S≤ 1≤M = ≤-trans (s≤s S≤) (+-monoˡ-≤ (N * M) 1≤M)

sum2 : ∀ {A B} (a b M : ℕ) → A ≤ a * M → B ≤ b * M → A + B ≤ (a + b) * M
sum2 {A} {B} a b M pa pb =
  subst (A + B ≤_) (sym (*-distribʳ-+ M a b)) (+-mono-≤ pa pb)

sum3 : ∀ {A B C} (a b c M : ℕ) → A ≤ a * M → B ≤ b * M → C ≤ c * M →
  (A + B) + C ≤ ((a + b) + c) * M
sum3 a b c M pa pb pc = sum2 (a + b) c M (sum2 a b M pa pb) pc

-- (G4) substitution grows size at most linearly in the env cap: every varᵗ
-- (size 1) hitting Θsub becomes wkTm (reify value), which is size-ren-invariant
-- (G2) and ≤ 2·sizeᵛ ≤ 2V (G3 + the cap), all under 1 * suc (2V); every other
-- constructor maps 1-1 and composes via sucmul/sum.  Mutual, shaped like
-- subΘ-capᵉ.
mutual
  size-subΘᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (V : ℕ) (Θloc : List Ty)
    (σ : All (Val Γ) Θsub) (e : Exp Γ Δᵍ Δ (Θloc ++ Θsub) t) →
    EnvSize V σ → sizeᵉ (subΘExp Θloc σ e) ≤ sizeᵉ e * suc (2 * V)
  size-subΘᵉ V Θloc σ (input i)       hσ = m≤m*n 1 (suc (2 * V))
  size-subΘᵉ V Θloc σ (ofᵉ ts)        hσ =
    sucmul (sizeᵗˢ ts) (suc (2 * V)) (size-subΘᵗˢ V Θloc σ ts hσ) (s≤s z≤n)
  size-subΘᵉ V Θloc σ emptyᵉ          hσ = m≤m*n 1 (suc (2 * V))
  size-subΘᵉ V Θloc σ (mapᵉ {s = s} f e) hσ =
    sucmul (sizeᵗ f + sizeᵉ e) (suc (2 * V))
      (sum2 (sizeᵗ f) (sizeᵉ e) (suc (2 * V))
            (size-subΘᵗ V (s ∷ Θloc) σ f hσ) (size-subΘᵉ V Θloc σ e hσ))
      (s≤s z≤n)
  size-subΘᵉ V Θloc σ (takeᵉ c e)     hσ =
    sucmul (sizeᵗ c + sizeᵉ e) (suc (2 * V))
      (sum2 (sizeᵗ c) (sizeᵉ e) (suc (2 * V))
            (size-subΘᵗ V Θloc σ c hσ) (size-subΘᵉ V Θloc σ e hσ))
      (s≤s z≤n)
  size-subΘᵉ V Θloc σ (scanᵉ {s = s} {t = t} f i e) hσ =
    sucmul ((sizeᵗ f + sizeᵗ i) + sizeᵉ e) (suc (2 * V))
      (sum3 (sizeᵗ f) (sizeᵗ i) (sizeᵉ e) (suc (2 * V))
            (size-subΘᵗ V ((t ×ᵗ s) ∷ Θloc) σ f hσ)
            (size-subΘᵗ V Θloc σ i hσ) (size-subΘᵉ V Θloc σ e hσ))
      (s≤s z≤n)
  size-subΘᵉ V Θloc σ (mergeAllᵉ e)   hσ =
    sucmul (sizeᵉ e) (suc (2 * V)) (size-subΘᵉ V Θloc σ e hσ) (s≤s z≤n)
  size-subΘᵉ V Θloc σ (concatAllᵉ e)  hσ =
    sucmul (sizeᵉ e) (suc (2 * V)) (size-subΘᵉ V Θloc σ e hσ) (s≤s z≤n)
  size-subΘᵉ V Θloc σ (switchAllᵉ e)  hσ =
    sucmul (sizeᵉ e) (suc (2 * V)) (size-subΘᵉ V Θloc σ e hσ) (s≤s z≤n)
  size-subΘᵉ V Θloc σ (exhaustAllᵉ e) hσ =
    sucmul (sizeᵉ e) (suc (2 * V)) (size-subΘᵉ V Θloc σ e hσ) (s≤s z≤n)
  size-subΘᵉ V Θloc σ (μᵉ e)          hσ =
    sucmul (sizeᵉ e) (suc (2 * V)) (size-subΘᵉ V Θloc σ e hσ) (s≤s z≤n)
  size-subΘᵉ V Θloc σ (varᵉ x)        hσ = m≤m*n 1 (suc (2 * V))
  size-subΘᵉ V Θloc σ (deferᵉ e)      hσ =
    sucmul (sizeᵉ e) (suc (2 * V)) (size-subΘᵉ V Θloc σ e hσ) (s≤s z≤n)

  size-subΘᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (V : ℕ) (Θloc : List Ty)
    (σ : All (Val Γ) Θsub) (tm : Tm Γ Δᵍ Δ (Θloc ++ Θsub) t) →
    EnvSize V σ → sizeᵗ (subΘTm Θloc σ tm) ≤ sizeᵗ tm * suc (2 * V)
  size-subΘᵗ V Θloc σ (varᵗ x) hσ with ∈-++⁻ Θloc x
  ... | inj₁ y = m≤m*n 1 (suc (2 * V))
  ... | inj₂ z =
    subst (_≤ 1 * suc (2 * V))
      (sym (size-renᵗ (λ ()) (λ ()) (λ ()) (reify (lookupEnv σ z))))
      (≤-trans (size-reify _ (lookupEnv σ z))
        (≤-trans (*-monoʳ-≤ 2 (envSize-lookup V σ hσ z))
          (subst (2 * V ≤_) (sym (+-identityʳ (suc (2 * V)))) (n≤1+n (2 * V)))))
  size-subΘᵗ V Θloc σ unit̂         hσ = m≤m*n 1 (suc (2 * V))
  size-subΘᵗ V Θloc σ (bool̂ _)     hσ = m≤m*n 1 (suc (2 * V))
  size-subΘᵗ V Θloc σ (nat̂ _)      hσ = m≤m*n 1 (suc (2 * V))
  size-subΘᵗ V Θloc σ (pairᵗ a b)  hσ =
    sucmul (sizeᵗ a + sizeᵗ b) (suc (2 * V))
      (sum2 (sizeᵗ a) (sizeᵗ b) (suc (2 * V))
            (size-subΘᵗ V Θloc σ a hσ) (size-subΘᵗ V Θloc σ b hσ))
      (s≤s z≤n)
  size-subΘᵗ V Θloc σ (fstᵗ p)     hσ =
    sucmul (sizeᵗ p) (suc (2 * V)) (size-subΘᵗ V Θloc σ p hσ) (s≤s z≤n)
  size-subΘᵗ V Θloc σ (sndᵗ p)     hσ =
    sucmul (sizeᵗ p) (suc (2 * V)) (size-subΘᵗ V Θloc σ p hσ) (s≤s z≤n)
  size-subΘᵗ V Θloc σ (inlᵗ a)     hσ =
    sucmul (sizeᵗ a) (suc (2 * V)) (size-subΘᵗ V Θloc σ a hσ) (s≤s z≤n)
  size-subΘᵗ V Θloc σ (inrᵗ a)     hσ =
    sucmul (sizeᵗ a) (suc (2 * V)) (size-subΘᵗ V Θloc σ a hσ) (s≤s z≤n)
  size-subΘᵗ V Θloc σ (caseᵗ {s = s} {t = t} sc l r) hσ =
    sucmul ((sizeᵗ sc + sizeᵗ l) + sizeᵗ r) (suc (2 * V))
      (sum3 (sizeᵗ sc) (sizeᵗ l) (sizeᵗ r) (suc (2 * V))
            (size-subΘᵗ V Θloc σ sc hσ)
            (size-subΘᵗ V (s ∷ Θloc) σ l hσ) (size-subΘᵗ V (t ∷ Θloc) σ r hσ))
      (s≤s z≤n)
  size-subΘᵗ V Θloc σ (ifᵗ c a b)  hσ =
    sucmul ((sizeᵗ c + sizeᵗ a) + sizeᵗ b) (suc (2 * V))
      (sum3 (sizeᵗ c) (sizeᵗ a) (sizeᵗ b) (suc (2 * V))
            (size-subΘᵗ V Θloc σ c hσ)
            (size-subΘᵗ V Θloc σ a hσ) (size-subΘᵗ V Θloc σ b hσ))
      (s≤s z≤n)
  size-subΘᵗ V Θloc σ (primᵗ _ a)  hσ =
    sucmul (sizeᵗ a) (suc (2 * V)) (size-subΘᵗ V Θloc σ a hσ) (s≤s z≤n)
  size-subΘᵗ V Θloc σ (strmᵗ e)    hσ =
    sucmul (sizeᵉ e) (suc (2 * V)) (size-subΘᵉ V Θloc σ e hσ) (s≤s z≤n)

  size-subΘᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (V : ℕ) (Θloc : List Ty)
    (σ : All (Val Γ) Θsub) (ts : List (Tm Γ Δᵍ Δ (Θloc ++ Θsub) t)) →
    EnvSize V σ → sizeᵗˢ (subΘTms Θloc σ ts) ≤ sizeᵗˢ ts * suc (2 * V)
  size-subΘᵗˢ V Θloc σ []       hσ = m≤m*n 1 (suc (2 * V))
  size-subΘᵗˢ V Θloc σ (x ∷ xs) hσ =
    sum2 (sizeᵗ x) (sizeᵗˢ xs) (suc (2 * V))
         (size-subΘᵗ V Θloc σ x hσ) (size-subΘᵗˢ V Θloc σ xs hσ)

-- (G1) an env capped at V (EnvSize) has short shells (EnvLen) and per-entry
-- bounded shells (EnvCap): per-entry ≤-trans / mapᴬ of the proven shellsᵛ-len
-- / shellsᵛ-≤ (both ≤ sizeᵛ) against the entry's own cap.
envSize→envLen : ∀ {n} {Γ : Ctx n} {Θ} (V : ℕ) (σ : All (Val Γ) Θ) →
  EnvSize V σ → EnvLen V σ
envSize→envLen V []ᵃ _ = tt
envSize→envLen V (_∷ᵃ_ {x = t} v σ) (h , hσ) =
  ≤-trans (shellsᵛ-len t v) h , envSize→envLen V σ hσ

envSize→envCap : ∀ {n} {Γ : Ctx n} {Θ} (B : ℕ) (σ : All (Val Γ) Θ) →
  EnvSize B σ → EnvCap B σ
envSize→envCap B []ᵃ _ = tt
envSize→envCap B (_∷ᵃ_ {x = t} v σ) (h , hσ) =
  mapᴬ (λ p → ≤-trans p h) (shellsᵛ-≤ t v) , envSize→envCap B σ hσ

-- (G6) oneShotBurst emits only init / value / close-exhausted / complete —
-- never close-dried — so its single emit is dry-free.  List induction over the
-- value payload (each `value` rejects dryEvent) plus the literal heads.
oneShot-tail-dry : ∀ {n} {Γ : Ctx n} {u} (vals : List (Val Γ u)) (src : Source) →
  any dryEvent (map value vals ++ close src exhausted ∷ complete ∷ []) ≡ false
oneShot-tail-dry []         src = refl
oneShot-tail-dry (v ∷ vals) src = oneShot-tail-dry vals src

-- (G7) installing a bounded node preserves the store bound: the schedule's
-- live is untouched, and setNode either overwrites at nid (new node bounded)
-- or recurses past a survivor, so all-boundedness survives.  Shaped like
-- sweepLive-bounded.
setNode-bounded : ∀ {n} {Γ : Ctx n} (B : ℕ) (nid : NodeId) (ns : NodeState Γ)
  (nodes : List (NodeId × NodeState Γ)) →
  boundedNode B ns ≡ true →
  all (λ kv → boundedNode B (proj₂ kv)) nodes ≡ true →
  all (λ kv → boundedNode B (proj₂ kv)) (setNode nid ns nodes) ≡ true
setNode-bounded B nid ns []             bn h = ∧-intro bn refl
setNode-bounded B nid ns ((k , s′) ∷ r) bn h with k ≡ᵇ nid
... | true  = ∧-intro bn (proj₂ (∧-true _ _ h))
... | false = ∧-intro (proj₁ (∧-true _ _ h))
                      (setNode-bounded B nid ns r bn (proj₂ (∧-true _ _ h)))

install-bounded : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (B : ℕ)
  (sched : Sched Γ) (st : EvalSt e) (nid : NodeId) (ns : NodeState Γ) →
  boundedNode B ns ≡ true → stBounded? B sched st ≡ true →
  stBounded? B sched (installNode nid ns st) ≡ true
install-bounded B sched st nid ns bn h =
  ∧-intro (proj₁ (∧-true _ _ h))
          (setNode-bounded B nid ns (EvalSt.nodes st) bn (proj₂ (∧-true _ _ h)))

-- (G5) the id-general seed inequality: prod≤3pow lands the demand product
-- under 2^2^2^(towerℕ h) which is DEFINITIONALLY towerℕ (3 + h) (h = (4+sz)·
-- (id+2)); towerℕ-mono lifts 3 + h ≤ (7+sz)·(id+2) (slack 3·(id+2) ≥ 3, a
-- solver identity for the split (4+sz)k + 3k ≡ (7+sz)k), and m≤n+m pads with
-- the 2^… head.  Shaped like seed-covers.  V here is the LANDING budget.
budget-covers : ∀ (sz U id : ℕ) → U ≤ sz →
  let V = towerℕ ((4 + sz) * suc (suc id)) in
  suc (suc V * suc (hopR V) * suc U)
    ≤ 2 ^ (sz * suc id * suc id) + towerℕ ((7 + sz) * suc (suc id))
budget-covers sz U id U≤sz =
  ≤-trans (prod≤3pow (towerℕ h) U 6≤V U≤V)
  (≤-trans (towerℕ-mono slack)
           (m≤n+m (towerℕ H) (2 ^ (sz * suc id * suc id))))
  where
  h = (4 + sz) * suc (suc id)
  H = (7 + sz) * suc (suc id)

  6≤V : 6 ≤ towerℕ h
  6≤V = ≤-trans (≤ᵇ⇒≤ 6 16 tt)
          (towerℕ-mono {3} {h}
            (≤-trans (s≤s (s≤s (s≤s z≤n))) (m≤m*n (4 + sz) (suc (suc id)))))

  sz≤h : sz ≤ h
  sz≤h = ≤-trans (m≤n+m sz 4) (m≤m*n (4 + sz) (suc (suc id)))

  U≤V : U ≤ towerℕ h
  U≤V = ≤-trans U≤sz (≤-trans sz≤h (k≤towerℕ h))

  3≤3k : 3 ≤ 3 * suc (suc id)
  3≤3k = subst (3 ≤_) (sym (*-suc 3 (suc id))) (m≤m+n 3 (3 * suc id))

  Hsplit : (4 + sz) * suc (suc id) + 3 * suc (suc id) ≡ H
  Hsplit = solve 2 (λ s i → (con 4 :+ s) :* (con 2 :+ i) :+ con 3 :* (con 2 :+ i)
                              := (con 7 :+ s) :* (con 2 :+ i)) refl sz id

  slack : 3 + h ≤ H
  slack = subst (3 + h ≤_) Hsplit
            (subst (_≤ h + 3 * suc (suc id)) (+-comm h 3)
              (+-monoʳ-≤ h 3≤3k))

------------------------------------------------------------------
-- THE EVAL GROWTH BOUND, PROVEN: one evaluation grows a value at
-- most to (2+2V)^(3^|tm|) from a V-capped environment.  The naive
-- per-template LINEAR bound is FALSE — a nested caseᵗ extends the
-- environment with an already-grown scrutinee component, so caps
-- compound multiplicatively per nesting level — but the compounding
-- is exactly a base swap V ↦ (2+2V)^(3^|sc|), and the tripled
-- exponent absorbs it: 2+2·C^p ≤ C^(p+2) (grow-pow) and
-- (3^|sc|+2)·3^|branch| ≤ 3^|caseᵗ …| (case-exp).  This is the
-- store-landing substrate at every applyFn/evalWith site of the
-- wet contract's clause grind: per application the store jumps at
-- most one exponential-of-exponential above the current cap, which
-- the per-instant tower step dwarfs.  Consumes G4 (size-subΘᵉ) at
-- the strmᵗ instantiation clause.
------------------------------------------------------------------

envSize-widen : ∀ {n} {Γ : Ctx n} {Θ} {V V′ : ℕ} → V ≤ V′ →
  (σ : All (Val Γ) Θ) → EnvSize V σ → EnvSize V′ σ
envSize-widen le []ᵃ       _         = tt
envSize-widen le (v ∷ᵃ σ) (hv , hσ) =
  ≤-trans hv le , envSize-widen le σ hσ

-- base facts about the growth base C = 2+2V
2≤C : ∀ V → 2 ≤ 2 + 2 * V
2≤C V = m≤m+n 2 (2 * V)

V≤C : ∀ V → V ≤ 2 + 2 * V
V≤C V = ≤-trans (m≤m+n V (V + 0)) (m≤n+m (2 * V) 2)

one≤pow : ∀ V k → 1 ≤ (2 + 2 * V) ^ k
one≤pow V k = ≤-trans (1≤2^ k) (^-monoˡ-≤ k (2≤C V))

one≤3^ : ∀ k → 1 ≤ 3 ^ k
one≤3^ k = ≤-trans (1≤2^ k) (^-monoˡ-≤ k (s≤s (s≤s z≤n)))

E≤E*3^ : ∀ (E k : ℕ) → E ≤ E * 3 ^ k
E≤E*3^ E k = ≤-trans (≤-reflexive (sym (*-identityʳ E)))
                     (*-monoʳ-≤ E (one≤3^ k))

k≤3^k : ∀ k → k ≤ 3 ^ k
k≤3^k k = ≤-trans (≤-trans (n≤1+n k) (n<2^n k))
                  (^-monoˡ-≤ k (s≤s (s≤s z≤n)))

pow1 : ∀ V {k} → 1 ≤ k → 2 + 2 * V ≤ (2 + 2 * V) ^ k
pow1 V h = ≤-trans (≤-reflexive (sym (*-identityʳ (2 + 2 * V))))
                   (^-monoʳ-≤ (2 + 2 * V) h)

-- one growth story: suc under the bound steps the exponent once
suc-pow-C : ∀ V p → suc ((2 + 2 * V) ^ p) ≤ (2 + 2 * V) ^ suc p
suc-pow-C V p =
  ≤-trans (+-monoˡ-≤ X (one≤pow V p))
  (≤-trans (≤-reflexive (cong (X +_) (sym (+-identityʳ X))))
           (*-monoˡ-≤ X (2≤C V)))
  where X = (2 + 2 * V) ^ p

-- two grown children: sizes sum, bounds multiply, all within the
-- tripled exponent
m+n≤m*n : ∀ {m n} → 2 ≤ m → 2 ≤ n → m + n ≤ m * n
m+n≤m*n {m} {suc n′} 2≤m (s≤s 1≤n′) =
  ≤-trans (+-monoʳ-≤ m
            (≤-trans (+-mono-≤ 1≤n′ (≤-reflexive (sym (+-identityʳ n′))))
                     (*-monoˡ-≤ n′ 2≤m)))
          (≤-reflexive (sym (*-suc m n′)))

pow3-pair : ∀ V (x y sa sb : ℕ) →
  x ≤ (2 + 2 * V) ^ (3 ^ sa) → y ≤ (2 + 2 * V) ^ (3 ^ sb) →
  suc (x + y) ≤ (2 + 2 * V) ^ (3 ^ suc (sa + sb))
pow3-pair V x y sa sb hx hy =
  ≤-trans (s≤s (+-mono-≤ hx hy))
  (≤-trans (s≤s (m+n≤m*n 2≤P 2≤Q))
  (≤-trans (+-monoˡ-≤ (P * Q) (*-mono-≤ (one≤pow V (3 ^ sa)) (one≤pow V (3 ^ sb))))
  (≤-trans (≤-reflexive (cong (P * Q +_) (sym (+-identityʳ (P * Q)))))
  (≤-trans (*-monoˡ-≤ (P * Q) (2≤C V))
  (≤-trans (≤-reflexive (cong ((2 + 2 * V) *_)
             (sym (^-distribˡ-+-* (2 + 2 * V) (3 ^ sa) (3 ^ sb)))))
           (^-monoʳ-≤ (2 + 2 * V) exp-arith))))))
  where
  P = (2 + 2 * V) ^ (3 ^ sa)
  Q = (2 + 2 * V) ^ (3 ^ sb)
  X = 3 ^ (sa + sb)
  2≤P = ≤-trans (2≤C V) (pow1 V (one≤3^ sa))
  2≤Q = ≤-trans (2≤C V) (pow1 V (one≤3^ sb))
  exp-arith : suc (3 ^ sa + 3 ^ sb) ≤ 3 ^ suc (sa + sb)
  exp-arith =
    +-mono-≤ (one≤3^ (sa + sb))
      (+-mono-≤ (^-monoʳ-≤ 3 (m≤m+n sa sb))
                (≤-trans (^-monoʳ-≤ 3 (m≤n+m sb sa))
                         (≤-reflexive (sym (+-identityʳ X)))))

-- the case hop: a branch bound over the GROWN cap collapses back —
-- the base swap costs two exponent units, absorbed by the 3^ jump
grow-pow : ∀ V p → 2 + 2 * ((2 + 2 * V) ^ p) ≤ (2 + 2 * V) ^ (p + 2)
grow-pow V p =
  ≤-trans (+-monoˡ-≤ (2 * X)
            (+-mono-≤ (one≤pow V p)
              (+-mono-≤ (one≤pow V p) (z≤n {0}))))
  (≤-trans (≤-reflexive (solve 1
             (λ x → con 2 :* x :+ con 2 :* x := x :* con 4) refl X))
  (≤-trans (*-monoʳ-≤ X
             (*-mono-≤ (2≤C V)
               (≤-trans (2≤C V) (≤-reflexive (sym (*-identityʳ (2 + 2 * V)))))))
           (≤-reflexive (sym (^-distribˡ-+-* (2 + 2 * V) p 2)))))
  where X = (2 + 2 * V) ^ p

pow3-hop : ∀ V (x p q E : ℕ) →
  x ≤ (2 + 2 * ((2 + 2 * V) ^ p)) ^ q →
  (p + 2) * q ≤ E →
  x ≤ (2 + 2 * V) ^ E
pow3-hop V x p q E hx hE =
  ≤-trans hx
  (≤-trans (^-monoˡ-≤ q (grow-pow V p))
  (≤-trans (≤-reflexive (^-*-assoc (2 + 2 * V) (p + 2) q))
           (^-monoʳ-≤ (2 + 2 * V) hE)))

case-exp : ∀ ss b K → ss + b ≤ K → (3 ^ ss + 2) * 3 ^ b ≤ 3 ^ suc K
case-exp ss b K h =
  ≤-trans (*-monoˡ-≤ (3 ^ b)
            (+-monoʳ-≤ Y
              (+-mono-≤ (one≤3^ ss)
                (+-mono-≤ (one≤3^ ss) (z≤n {0})))))
  (≤-trans (≤-reflexive (trans (*-assoc 3 Y (3 ^ b))
                               (cong (3 *_) (sym (^-distribˡ-+-* 3 ss b)))))
           (^-monoʳ-≤ 3 (s≤s h)))
  where Y = 3 ^ ss

-- THE BOUND.  Induction on the term; the caseᵗ clauses re-enter at
-- the grown cap and collapse via pow3-hop
evalWith-size : ∀ {n} {Γ : Ctx n} {Θ t} (V : ℕ)
  (tm : Tm Γ [] [] Θ t) (env : All (Val Γ) Θ) → EnvSize V env →
  sizeᵛ t (evalWith tm env) ≤ (2 + 2 * V) ^ (3 ^ sizeᵗ tm)
evalWith-size V (varᵗ x) env hσ =
  ≤-trans (envSize-lookup V env hσ x)
          (≤-trans (V≤C V) (pow1 V (one≤3^ 1)))
evalWith-size V unit̂     env hσ = one≤pow V (3 ^ 1)
evalWith-size V (bool̂ _) env hσ = one≤pow V (3 ^ 1)
evalWith-size V (nat̂ _)  env hσ = one≤pow V (3 ^ 1)
evalWith-size V (pairᵗ a b) env hσ =
  pow3-pair V _ _ (sizeᵗ a) (sizeᵗ b)
    (evalWith-size V a env hσ) (evalWith-size V b env hσ)
evalWith-size {t = t} V (fstᵗ p) env hσ
  with evalWith p env | evalWith-size V p env hσ
... | (a , b) | ihp =
  ≤-trans (≤-trans (m≤m+n (sizeᵛ _ a) (sizeᵛ _ b)) (n≤1+n _))
          (≤-trans ihp
                   (^-monoʳ-≤ (2 + 2 * V) (^-monoʳ-≤ 3 (n≤1+n (sizeᵗ p)))))
evalWith-size {t = t} V (sndᵗ p) env hσ
  with evalWith p env | evalWith-size V p env hσ
... | (a , b) | ihp =
  ≤-trans (≤-trans (m≤n+m (sizeᵛ _ b) (sizeᵛ _ a)) (n≤1+n _))
          (≤-trans ihp
                   (^-monoʳ-≤ (2 + 2 * V) (^-monoʳ-≤ 3 (n≤1+n (sizeᵗ p)))))
evalWith-size V (inlᵗ a) env hσ =
  ≤-trans (s≤s (evalWith-size V a env hσ))
  (≤-trans (suc-pow-C V (3 ^ sizeᵗ a))
           (^-monoʳ-≤ (2 + 2 * V)
             (+-mono-≤ (one≤3^ (sizeᵗ a))
                       (m≤m+n (3 ^ sizeᵗ a) (3 ^ sizeᵗ a + 0)))))
evalWith-size V (inrᵗ a) env hσ =
  ≤-trans (s≤s (evalWith-size V a env hσ))
  (≤-trans (suc-pow-C V (3 ^ sizeᵗ a))
           (^-monoʳ-≤ (2 + 2 * V)
             (+-mono-≤ (one≤3^ (sizeᵗ a))
                       (m≤m+n (3 ^ sizeᵗ a) (3 ^ sizeᵗ a + 0)))))
evalWith-size V (caseᵗ {s = s} {t = t} sc l r) env hσ
  with evalWith sc env | evalWith-size V sc env hσ
... | inj₁ a | ihsc =
  pow3-hop V _ (3 ^ sizeᵗ sc) (3 ^ sizeᵗ l) _
    (evalWith-size ((2 + 2 * V) ^ (3 ^ sizeᵗ sc)) l (a ∷ᵃ env)
      ( ≤-trans (n≤1+n _) ihsc
      , envSize-widen (≤-trans (V≤C V) (pow1 V (one≤3^ (sizeᵗ sc)))) env hσ))
    (case-exp (sizeᵗ sc) (sizeᵗ l) (sizeᵗ sc + sizeᵗ l + sizeᵗ r)
      (m≤m+n (sizeᵗ sc + sizeᵗ l) (sizeᵗ r)))
... | inj₂ b | ihsc =
  pow3-hop V _ (3 ^ sizeᵗ sc) (3 ^ sizeᵗ r) _
    (evalWith-size ((2 + 2 * V) ^ (3 ^ sizeᵗ sc)) r (b ∷ᵃ env)
      ( ≤-trans (n≤1+n _) ihsc
      , envSize-widen (≤-trans (V≤C V) (pow1 V (one≤3^ (sizeᵗ sc)))) env hσ))
    (case-exp (sizeᵗ sc) (sizeᵗ r) (sizeᵗ sc + sizeᵗ l + sizeᵗ r)
      (+-monoˡ-≤ (sizeᵗ r) (m≤m+n (sizeᵗ sc) (sizeᵗ l))))
evalWith-size V (ifᵗ c a b) env hσ with evalWith c env
... | true  =
  ≤-trans (evalWith-size V a env hσ)
          (^-monoʳ-≤ (2 + 2 * V)
            (^-monoʳ-≤ 3 (≤-trans (m≤n+m (sizeᵗ a) (sizeᵗ c))
                          (≤-trans (m≤m+n (sizeᵗ c + sizeᵗ a) (sizeᵗ b))
                                   (n≤1+n _)))))
... | false =
  ≤-trans (evalWith-size V b env hσ)
          (^-monoʳ-≤ (2 + 2 * V)
            (^-monoʳ-≤ 3 (≤-trans (m≤n+m (sizeᵗ b) (sizeᵗ c + sizeᵗ a))
                                  (n≤1+n _))))
evalWith-size V (primᵗ add arg)  env hσ = one≤pow V (3 ^ suc (sizeᵗ arg))
evalWith-size V (primᵗ sub arg)  env hσ = one≤pow V (3 ^ suc (sizeᵗ arg))
evalWith-size V (primᵗ mul arg)  env hσ = one≤pow V (3 ^ suc (sizeᵗ arg))
evalWith-size V (primᵗ eqᵖ arg)  env hσ = one≤pow V (3 ^ suc (sizeᵗ arg))
evalWith-size V (primᵗ ltᵖ arg)  env hσ = one≤pow V (3 ^ suc (sizeᵗ arg))
evalWith-size V (primᵗ notᵖ arg) env hσ = one≤pow V (3 ^ suc (sizeᵗ arg))
evalWith-size V (strmᵗ e) []ᵃ hσ =
  ≤-trans (≤-trans (n≤1+n (sizeᵉ e)) (n<2^n (sizeᵉ e)))
  (≤-trans (^-monoˡ-≤ (sizeᵉ e) (2≤C V))
           (^-monoʳ-≤ (2 + 2 * V)
             (≤-trans (k≤3^k (sizeᵉ e)) (^-monoʳ-≤ 3 (n≤1+n (sizeᵉ e))))))
evalWith-size V (strmᵗ e) (v ∷ᵃ vs) hσ =
  ≤-trans (size-subΘᵉ V [] (v ∷ᵃ vs) e hσ)
  (≤-trans (*-mono-≤
             (≤-trans (≤-trans (n≤1+n (sizeᵉ e)) (n<2^n (sizeᵉ e)))
                      (^-monoˡ-≤ (sizeᵉ e) (2≤C V)))
             (n≤1+n (suc (2 * V))))
  (≤-trans (≤-reflexive (*-comm ((2 + 2 * V) ^ sizeᵉ e) (2 + 2 * V)))
           (^-monoʳ-≤ (2 + 2 * V) (k≤3^k (suc (sizeᵉ e))))))

-- the applyFn/evalTm faces the contract's clause grind consumes
applyFn-size : ∀ {n} {Γ : Ctx n} {s t} (V : ℕ)
  (fn : Fn Γ [] [] [] s t) (v : Val Γ s) → sizeᵛ s v ≤ V →
  sizeᵛ t (applyFn fn v) ≤ (2 + 2 * V) ^ (3 ^ sizeᵗ fn)
applyFn-size V fn v hv = evalWith-size V fn (v ∷ᵃ []ᵃ) (hv , tt)

------------------------------------------------------------------
-- THE WALK LEDGER (2026-07-24 — the settled per-instant invariant).
--
-- The blocking question was the closed form of the internal
-- invariant that survives subscribeE's walk: scan frames fold
-- value-list breadth with no fuel peel, so no fixed (V, R) and no
-- gas-indexed cap works.  Settled:
--
-- (1) THE SHARP EVAL BOUND.  evalWith-size's exponent 3^|tm| was
--     the lossy culprit: |tm| grows under substitution, so iterated
--     folds looked like iterated exponentials.  But the ONLY
--     constructor that compounds sizes multiplicatively under
--     evalWith is caseᵗ — its branch runs over an environment
--     extended with an already-grown scrutinee component; ifᵗ
--     branches see the unextended environment, pair components
--     multiply bounds side by side, and reify images (pairᵗ / inlᵗ
--     / inrᵗ / strmᵗ / literals) are eval-passive.  caseWᵗ counts
--     exactly that compounding structure, with strmᵗ a LEAF (an
--     embedded expression is inert during eval: evalWith (strmᵗ e)
--     σ = subΘ e, LINEAR in the plugs — size-subΘᵉ).  Then (W3):
--       sizeᵛ (evalWith tm env) ≤ sizeᵗ tm · (2+2V)^(3^caseWᵗ tm)
--     — the BASE carries the store, the EXPONENT carries only
--     template structure.  And caseW is EXACTLY substitution-
--     invariant (caseW-subΘ: plugs land behind reify images, which
--     weigh 0), so every runtime fn's caseW is its program
--     template's: ≤ Ψ FOREVER, Ψ seeded once from program+slots
--     (ΨAt).  fnCap is the max-shaped closure carrying "every
--     embedded fn's caseW ≤ Ψ" through stores, evals
--     (fnCap-evalWith), substitution and μ-unfolds.
--
-- (2) THE LEDGER.  Freeze W₀ := sizeBudgetAt id at instant entry;
--     the running cap is capᴱ W₀ E = (2+2W₀)^E with E ≥ 2 the
--     ledger position.  ONE RULE covers every growth edge: at
--     E ≥ 2, an eval/fold application multiplies E by at most
--     3^(suc Ψ) (from (W3) and grow-pow: the recurrence
--     q′ = E + (q+2)·3^Ψ ≤ q·3^(suc Ψ) for q ≥ E ≥ 2), and a
--     register / μ-copy / one-shot install multiplies E by at most
--     2.  A fold-RUN over a value list of length m costs the single
--     factor 3^(suc Ψ · m) (scanVals-sharp) — the value-list
--     lengths thread the receipts, and receipts compose
--     multiplicatively: spendᴱ Ψ r s = 2^r · 3^(suc Ψ · s),
--     spendᴱ-compose.  Receipts are LOCAL — a clause's spend is its
--     own sites plus its children's, no global count needed for
--     preservation.
--
-- (3) THE LANDING.  sizeBudgetAt now has height (4+sz)(1+id): the
--     per-instant gain of (4+sz) ≥ 5 stories dominates the walk's
--     spend measured against the ENTRY cap: the spend exponent is
--     (counts)·(suc Ψ), one story for the counts, one for the 3^·,
--     one for capᴱ, margin for the rest.  The instant's total
--     application COUNT still needs its a-priori entry-anchored
--     bound — the one remaining quantitative core: per-subscription
--     sites are template-invariant (shells, of-widths and caseW all
--     substitution-invariant), subscriptions ≤ 1 + fuel peels, and
--     peels are bounded by the lex descent (U, rank, syncSize),
--     whose ℕ collapse anchors at the LANDING budget (mid-walk
--     values outgrow the entry cap, but every hop target measures
--     strictly below its parent).  The dry-half demand therefore
--     anchors at sizeBudgetAt (suc id) — the gas tower's height
--     (7+sz)(2+id) covers it (budget-covers) — while the count cap
--     needs the descent length anchored one story sharper.  Closing
--     that gap is the remaining quantitative debt, localized in the
--     two cores below; do NOT restate their landing halves until it
--     closes.  REFINEMENT (2026-07-24, the grind session): the
--     boundary will need the RUN receipts in their sharp MIXED
--     form, not the uniform ×3^(suc Ψ) rule — for a caseW-0 fn the
--     run recurrence q′ = E + q + 2 is ADDITIVE (the exponent grows
--     linearly in the fold count, matching the attack's
--     one-story-per-instant reality), and only executed CASE-work
--     compounds multiplicatively: E_fin ≤ (E₀ + 2 + F) · 3^(Σ wᵢ)
--     with F the total fold count and Σ wᵢ the caseW actually
--     executed.  The uniform rule stays true and is what the
--     preservation grind below uses; the boundary consumes the
--     mixed form, whose F needs the a-priori anchor — CLOSED
--     2026-07-24: see (5) THE WIDTH LEDGER below.  SUPERSEDED
--     (same day, the dry-half session): the joint face's receipt
--     (E′ ≤ E·3^(suc Ψ·walkCap), subscribeE-walk) anchors the
--     whole walk's spend a priori, so the boundary consumes THAT
--     directly — no per-fold count, uniform or mixed, global or
--     per-lineage, is needed at all.
--
-- (4) THE REGISTRY (the fold-threading design block).  INV?
--     extends stBounded? with: fnCap-boundedness of every store
--     (Ψ never grows), length (registry) ≤ B (the CARDINALITY
--     invariant cascadeGo's fold needs: |chains| ≤ registry length
--     at the latch), and per-chain frame bounds (registered
--     scan/map fns are runtime material — sizes ride B, caseW
--     rides Ψ; the "registry entries are fixed syntax" assumption
--     held only for the root program's chains).  chainStep-wet is
--     stated against INV?, and cascadeGo-walk (PROVEN below) is
--     the fold decomposition: it threads INV? and the ledger
--     position chain by chain — the structure the cascadeGo-wet
--     memo demanded — leaving the per-chain core and the landing
--     arithmetic as the only leaves.
--
-- (5) THE WIDTH LEDGER (2026-07-24, the anchor session — closes
--     the count cap).  Two settled findings.
--
--     IMPOSSIBILITY: no GLOBAL-SEQUENTIAL count can land.  If the
--     boundary threads ONE exponent through every fold of the
--     instant in sequence, the total fold count N is bounded only
--     through list lengths ≤ value sizes ≤ the FINAL cap — but the
--     final cap sits a story above N (capᴱ of an N-linear
--     exponent), so the tower heights demand story(N) ≥
--     story(cap) + 1 ≥ story(N) + 2: a divergent fixpoint.  No
--     sharper counting RULE fixes this; the landing must break the
--     "lengths ≤ sizes" self-reference itself.
--
--     THE BREAK: stream WIDTH is substitution-invariant.  Widths
--     (of-list lengths) are SYNTAX: subΘ/elimG/ren map over the
--     of-list (length preserved), evalWith on strmᵗ IS subΘ, reify
--     at obs is strmᵗ, and NO operator converts a value's SIZE
--     into a stream's WIDTH — ofᵉ is the only width mint and its
--     list is template-fixed.  (PORTABILITY TRIPWIRE: a
--     fromArray-style operator — value ↦ stream of its elements —
--     would break exactly this; the modeled fragment has none, and
--     adding one re-opens this core.)  So the width cap Ω (ofW,
--     the max-shaped closure mirroring fnCap clause for clause,
--     seeded ΩAt = program + slots) NEVER GROWS: it rides the walk
--     as Ψ does, with NO ledger position at all (widthOK? below —
--     flat, no existential).
--
--     THE ANCHOR: fold counts are now entry-anchored.  A list
--     delivered to a frame is a concatenation of per-subscription
--     of-runs, each of length ≤ Ω, so run lengths ride the
--     SUBSCRIPTION COUNT S — the machine's own counter delta
--     (mintCount below): the length ledger threads counter
--     deltas.  S is NOT ≤ the descent length: fuel is
--     depth-consumed and SIBLINGS SHARE IT (syncBudget's memo —
--     mints are breadth-many; the measured attack makes 2^k
--     sibling subscriptions on k peels).
--
--     CORRECTION (2026-07-24, the dry-half session): this memo's
--     first cut claimed per-subscription fan-out ≤ Ω and hence
--     S ≤ Ω^(suc D₀).  That accounting is WRONG twice over: a
--     *All frame hops once per VALUE of its child's burst — an
--     aggregate of the whole child SUBTREE's emissions, not of
--     one subscription's of-run — and one value can hop again at
--     every later *All frame it crosses.  The honest call-tree
--     recurrence (every edge descends the dBound demand d:
--     structural edges drop s, μ drops s, hops drop r, connects
--     drop U) is QUADRATIC,
--       S(d) ≤ c + S(d-1) + burstLen(d-1)·S(d-1),
--     whose naive closure is doubly exponential in d:
--       S, burstLen ≤ walkCap Ω ℓ d = ((3+Ω)·suc ℓ)^(3^d)
--     with ℓ ≥ pathLen κ + d the frame-crossing bound (path
--     lengths join the base: each value folds/hops at most once
--     per frame crossed; `pathLen κ + d ≤ ℓ` is preserved on
--     every edge for free).  Whether dBound's rank-weighting
--     recovers a singly-exponential form (the rank component
--     self-limits nested-hop capacity) is OPEN and IRRELEVANT for
--     the landing: walkCap is frozen at instant entry, one tower
--     story above the old claim — story counts shift by one and
--     nothing else changes.  Fold counts per value lineage:
--       F ≤ 𝔉 := suc ℓ₀ · walkCap Ω ℓ₀ D₀
--     (crossings per value ≤ suc ℓ₀, values ≤ walkCap) — every
--     factor frozen at instant entry.  The wet and dry halves
--     consume the SAME descent: d bounds the hop geometry for the
--     count cap exactly where dBound bounds it for the fuel.
--     Story count, W₀ = tower h: Ω syntax-seeded, ℓ₀ ≤ tower(h+3)
--     (dBound at R₀ = (suc V)^(suc V)), 3^D₀ ≤ tower(h+4),
--     walkCap and 𝔉 ≤ tower(h+5), E_fin ≤ E₀·3^(suc Ψ·𝔉) ≤
--     tower(h+6), sizes ≤ capᴱ W₀ E_fin ≤ tower(h+7): a CONSTANT
--     story count per instant, absorbed by the height multiplier
--     (bump 4+sz if the grind's constants land above it —
--     verification-side, plus the matching gas-tower bump; both
--     behavior-preserving, Unit-Test guards).
--
--     WHAT REMAINS is grind, not design: (a) the ofW invariance /
--     preservation mirrors (W10/W11 below — literal fnCap-grind
--     repeats); (b) STATED 2026-07-24: subscribeE-walk (below the
--     W11 block) is the JOINT FACE — the wet conjuncts with their
--     receipt E′ ≤ E·3^(suc Ψ·walkCap), the dry half, and the
--     length ledger (mintCount delta, burstLen, registered path
--     lengths) in one hypothesis block under one ceiling; its
--     clause grind extends the ground walkS clauses conjunct by
--     conjunct, consuming W11 for hop targets and hasAtLeast-peel
--     against dBound-μ/-hop/-connect for the fuel; (c) RETIRED —
--     the face's receipt anchors the spend a priori, so no
--     lineage-indexed (or any per-fold) receipt is needed; (d) the
--     landing: instantiate the face at the root with V =
--     sizeBudgetAt (suc id) and discharge the ceiling by the
--     story-count arithmetic above (this WILL need the height-
--     multiplier bump and its matching gas-tower bump), the fuel
--     seed by budget-hasAtLeast, and the Ω/ℓ₀/regsLen? seeds at
--     init — replacing the two cores' landing halves.  The
--     instant-level (cascadeGo) joint face repeats this design at
--     the chain fold, but is deliberately NOT stated until (b)'s
--     grind confirms the subscribeE face survives contact.
------------------------------------------------------------------

-- the eval-compounding weight: caseᵗ nodes only; strmᵗ is a leaf
-- (embedded expressions are inert during eval); reify images weigh 0
caseWᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Tm Γ Δᵍ Δ Θ t → ℕ
caseWᵗ (varᵗ x)      = 0
caseWᵗ unit̂          = 0
caseWᵗ (bool̂ _)      = 0
caseWᵗ (nat̂ _)       = 0
caseWᵗ (pairᵗ a b)   = caseWᵗ a + caseWᵗ b
caseWᵗ (fstᵗ p)      = caseWᵗ p
caseWᵗ (sndᵗ p)      = caseWᵗ p
caseWᵗ (inlᵗ a)      = caseWᵗ a
caseWᵗ (inrᵗ a)      = caseWᵗ a
caseWᵗ (caseᵗ s l r) = 2 + (caseWᵗ s + caseWᵗ l + caseWᵗ r)
caseWᵗ (ifᵗ c a b)   = caseWᵗ c + caseWᵗ a + caseWᵗ b
caseWᵗ (primᵗ _ a)   = caseWᵗ a
caseWᵗ (strmᵗ e)     = 0

-- the fn-cap closure: the max caseW of every fn that material
-- reachable from here can EVER apply — through strmᵗ, deferᵉ, and
-- every operator's Tm positions (of-elements, fns, seeds, counts
-- are all eval sites, now or after storage)
mutual
  fnCapᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Tm Γ Δᵍ Δ Θ t → ℕ
  fnCapᵗ (varᵗ x)      = 0
  fnCapᵗ unit̂          = 0
  fnCapᵗ (bool̂ _)      = 0
  fnCapᵗ (nat̂ _)       = 0
  fnCapᵗ (pairᵗ a b)   = fnCapᵗ a ⊔ fnCapᵗ b
  fnCapᵗ (fstᵗ p)      = fnCapᵗ p
  fnCapᵗ (sndᵗ p)      = fnCapᵗ p
  fnCapᵗ (inlᵗ a)      = fnCapᵗ a
  fnCapᵗ (inrᵗ a)      = fnCapᵗ a
  fnCapᵗ (caseᵗ s l r) = fnCapᵗ s ⊔ (fnCapᵗ l ⊔ fnCapᵗ r)
  fnCapᵗ (ifᵗ c a b)   = fnCapᵗ c ⊔ (fnCapᵗ a ⊔ fnCapᵗ b)
  fnCapᵗ (primᵗ _ a)   = fnCapᵗ a
  fnCapᵗ (strmᵗ e)     = fnCapᵉ e

  fnCapᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Exp Γ Δᵍ Δ Θ t → ℕ
  fnCapᵉ (input i)       = 0
  fnCapᵉ (ofᵉ ts)        = fnCapᵗˢ ts
  fnCapᵉ emptyᵉ          = 0
  fnCapᵉ (mapᵉ f e)      = (caseWᵗ f ⊔ fnCapᵗ f) ⊔ fnCapᵉ e
  fnCapᵉ (takeᵉ c e)     = (caseWᵗ c ⊔ fnCapᵗ c) ⊔ fnCapᵉ e
  fnCapᵉ (scanᵉ f z e)   =
    (caseWᵗ f ⊔ fnCapᵗ f) ⊔ ((caseWᵗ z ⊔ fnCapᵗ z) ⊔ fnCapᵉ e)
  fnCapᵉ (mergeAllᵉ e)   = fnCapᵉ e
  fnCapᵉ (concatAllᵉ e)  = fnCapᵉ e
  fnCapᵉ (switchAllᵉ e)  = fnCapᵉ e
  fnCapᵉ (exhaustAllᵉ e) = fnCapᵉ e
  fnCapᵉ (μᵉ e)          = fnCapᵉ e
  fnCapᵉ (varᵉ x)        = 0
  fnCapᵉ (deferᵉ e)      = fnCapᵉ e

  fnCapᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → List (Tm Γ Δᵍ Δ Θ t) → ℕ
  fnCapᵗˢ []       = 0
  fnCapᵗˢ (y ∷ ys) = (caseWᵗ y ⊔ fnCapᵗ y) ⊔ fnCapᵗˢ ys

fnCapᵛ : ∀ {n} {Γ : Ctx n} (t : Ty) → Val Γ t → ℕ
fnCapᵛ unitᵗ    v        = 0
fnCapᵛ boolᵗ    v        = 0
fnCapᵛ natᵗ     v        = 0
fnCapᵛ (s ×ᵗ t) (a , b)  = fnCapᵛ s a ⊔ fnCapᵛ t b
fnCapᵛ (s +ᵗ t) (inj₁ a) = fnCapᵛ s a
fnCapᵛ (s +ᵗ t) (inj₂ b) = fnCapᵛ t b
fnCapᵛ (obs t)  e        = fnCapᵉ e

-- the fn-cap face of an environment, shaped like EnvSize
EnvFnCap : ∀ {n} {Γ : Ctx n} {Θ} (Ψ : ℕ) → All (Val Γ) Θ → Set
EnvFnCap Ψ []ᵃ                = ⊤
EnvFnCap Ψ (_∷ᵃ_ {x = t} v σ) = (fnCapᵛ t v ≤ Ψ) × EnvFnCap Ψ σ

-- (W1) caseW is renaming- and substitution-INVARIANT: reify images weigh 0
-- (they contain no caseᵗ), and subΘ rewrites only var positions — a
-- structural induction over Tm (caseWᵗ ignores the Exp under strmᵗ, so no
-- mutual recursion is needed), mirroring shellSize-ren / shellSize-subΘ.
caseW-ren : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t}
  (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′)
  (tm : Tm Γ Δᵍ Δ Θ t) → caseWᵗ (renTm ρg ρd ρt tm) ≡ caseWᵗ tm
caseW-ren ρg ρd ρt (varᵗ x)      = refl
caseW-ren ρg ρd ρt unit̂          = refl
caseW-ren ρg ρd ρt (bool̂ _)      = refl
caseW-ren ρg ρd ρt (nat̂ _)       = refl
caseW-ren ρg ρd ρt (pairᵗ a b)   = cong₂ _+_ (caseW-ren ρg ρd ρt a) (caseW-ren ρg ρd ρt b)
caseW-ren ρg ρd ρt (fstᵗ p)      = caseW-ren ρg ρd ρt p
caseW-ren ρg ρd ρt (sndᵗ p)      = caseW-ren ρg ρd ρt p
caseW-ren ρg ρd ρt (inlᵗ a)      = caseW-ren ρg ρd ρt a
caseW-ren ρg ρd ρt (inrᵗ a)      = caseW-ren ρg ρd ρt a
caseW-ren ρg ρd ρt (caseᵗ s l r) =
  cong (2 +_) (cong₂ _+_ (cong₂ _+_ (caseW-ren ρg ρd ρt s) (caseW-ren ρg ρd (ext∈ ρt) l))
                         (caseW-ren ρg ρd (ext∈ ρt) r))
caseW-ren ρg ρd ρt (ifᵗ c a b)   =
  cong₂ _+_ (cong₂ _+_ (caseW-ren ρg ρd ρt c) (caseW-ren ρg ρd ρt a)) (caseW-ren ρg ρd ρt b)
caseW-ren ρg ρd ρt (primᵗ _ a)   = caseW-ren ρg ρd ρt a
caseW-ren ρg ρd ρt (strmᵗ e)     = refl

caseW-reify : ∀ {n} {Γ : Ctx n} (t : Ty) (v : Val Γ t) →
  caseWᵗ (reify v) ≡ 0
caseW-reify unitᵗ   _        = refl
caseW-reify boolᵗ   _        = refl
caseW-reify natᵗ    _        = refl
caseW-reify (s ×ᵗ t) (a , b) = cong₂ _+_ (caseW-reify s a) (caseW-reify t b)
caseW-reify (s +ᵗ t) (inj₁ a) = caseW-reify s a
caseW-reify (s +ᵗ t) (inj₂ b) = caseW-reify t b
caseW-reify (obs t)  e       = refl

caseW-subΘ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (Θloc : List Ty)
  (σ : All (Val Γ) Θsub) (tm : Tm Γ Δᵍ Δ (Θloc ++ Θsub) t) →
  caseWᵗ (subΘTm Θloc σ tm) ≡ caseWᵗ tm
caseW-subΘ Θloc σ (varᵗ x) with ∈-++⁻ Θloc x
... | inj₁ y = refl
... | inj₂ z =
  trans (caseW-ren (λ ()) (λ ()) (λ ()) (reify (lookupEnv σ z)))
        (caseW-reify _ (lookupEnv σ z))
caseW-subΘ Θloc σ unit̂         = refl
caseW-subΘ Θloc σ (bool̂ _)     = refl
caseW-subΘ Θloc σ (nat̂ _)      = refl
caseW-subΘ Θloc σ (pairᵗ a b)  = cong₂ _+_ (caseW-subΘ Θloc σ a) (caseW-subΘ Θloc σ b)
caseW-subΘ Θloc σ (fstᵗ p)     = caseW-subΘ Θloc σ p
caseW-subΘ Θloc σ (sndᵗ p)     = caseW-subΘ Θloc σ p
caseW-subΘ Θloc σ (inlᵗ a)     = caseW-subΘ Θloc σ a
caseW-subΘ Θloc σ (inrᵗ a)     = caseW-subΘ Θloc σ a
caseW-subΘ Θloc σ (caseᵗ {s = s} {t = t} sc l r) =
  cong (2 +_) (cong₂ _+_ (cong₂ _+_ (caseW-subΘ Θloc σ sc) (caseW-subΘ (s ∷ Θloc) σ l))
                         (caseW-subΘ (t ∷ Θloc) σ r))
caseW-subΘ Θloc σ (ifᵗ c a b)  =
  cong₂ _+_ (cong₂ _+_ (caseW-subΘ Θloc σ c) (caseW-subΘ Θloc σ a)) (caseW-subΘ Θloc σ b)
caseW-subΘ Θloc σ (primᵗ _ a)  = caseW-subΘ Θloc σ a
caseW-subΘ Θloc σ (strmᵗ e)    = refl

-- split a bound on a join into its two summands (explicit summands so Agda
-- never has to invert _⊔_ — nested decomposition otherwise stalls)
⊔ˡ : ∀ a b {c} → a ⊔ b ≤ c → a ≤ c
⊔ˡ a b = m⊔n≤o⇒m≤o a b
⊔ʳ : ∀ a b {c} → a ⊔ b ≤ c → b ≤ c
⊔ʳ a b = m⊔n≤o⇒n≤o a b

-- fnCap is renaming-invariant (constructors map 1-1; strmᵗ recurses into
-- the Exp, so this is mutual over ᵉ/ᵗ/ᵗˢ, shaped like size-renᵉ but with ⊔).
mutual
  fnCap-renᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t}
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′)
    (e : Exp Γ Δᵍ Δ Θ t) → fnCapᵉ (renExp ρg ρd ρt e) ≡ fnCapᵉ e
  fnCap-renᵉ ρg ρd ρt (input i)       = refl
  fnCap-renᵉ ρg ρd ρt (ofᵉ ts)        = fnCap-renᵗˢ ρg ρd ρt ts
  fnCap-renᵉ ρg ρd ρt emptyᵉ          = refl
  fnCap-renᵉ ρg ρd ρt (mapᵉ f e)      =
    cong₂ _⊔_ (cong₂ _⊔_ (caseW-ren ρg ρd (ext∈ ρt) f) (fnCap-renᵗ ρg ρd (ext∈ ρt) f))
              (fnCap-renᵉ ρg ρd ρt e)
  fnCap-renᵉ ρg ρd ρt (takeᵉ c e)     =
    cong₂ _⊔_ (cong₂ _⊔_ (caseW-ren ρg ρd ρt c) (fnCap-renᵗ ρg ρd ρt c))
              (fnCap-renᵉ ρg ρd ρt e)
  fnCap-renᵉ ρg ρd ρt (scanᵉ f z e)   =
    cong₂ _⊔_ (cong₂ _⊔_ (caseW-ren ρg ρd (ext∈ ρt) f) (fnCap-renᵗ ρg ρd (ext∈ ρt) f))
              (cong₂ _⊔_ (cong₂ _⊔_ (caseW-ren ρg ρd ρt z) (fnCap-renᵗ ρg ρd ρt z))
                         (fnCap-renᵉ ρg ρd ρt e))
  fnCap-renᵉ ρg ρd ρt (mergeAllᵉ e)   = fnCap-renᵉ ρg ρd ρt e
  fnCap-renᵉ ρg ρd ρt (concatAllᵉ e)  = fnCap-renᵉ ρg ρd ρt e
  fnCap-renᵉ ρg ρd ρt (switchAllᵉ e)  = fnCap-renᵉ ρg ρd ρt e
  fnCap-renᵉ ρg ρd ρt (exhaustAllᵉ e) = fnCap-renᵉ ρg ρd ρt e
  fnCap-renᵉ ρg ρd ρt (μᵉ e)          = fnCap-renᵉ (ext∈ ρg) ρd ρt e
  fnCap-renᵉ ρg ρd ρt (varᵉ x)        = refl
  fnCap-renᵉ ρg ρd ρt (deferᵉ e)      = fnCap-renᵉ (λ ()) (++Ren ρg ρd) ρt e

  fnCap-renᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t}
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′)
    (tm : Tm Γ Δᵍ Δ Θ t) → fnCapᵗ (renTm ρg ρd ρt tm) ≡ fnCapᵗ tm
  fnCap-renᵗ ρg ρd ρt (varᵗ x)      = refl
  fnCap-renᵗ ρg ρd ρt unit̂          = refl
  fnCap-renᵗ ρg ρd ρt (bool̂ _)      = refl
  fnCap-renᵗ ρg ρd ρt (nat̂ _)       = refl
  fnCap-renᵗ ρg ρd ρt (pairᵗ a b)   = cong₂ _⊔_ (fnCap-renᵗ ρg ρd ρt a) (fnCap-renᵗ ρg ρd ρt b)
  fnCap-renᵗ ρg ρd ρt (fstᵗ p)      = fnCap-renᵗ ρg ρd ρt p
  fnCap-renᵗ ρg ρd ρt (sndᵗ p)      = fnCap-renᵗ ρg ρd ρt p
  fnCap-renᵗ ρg ρd ρt (inlᵗ a)      = fnCap-renᵗ ρg ρd ρt a
  fnCap-renᵗ ρg ρd ρt (inrᵗ a)      = fnCap-renᵗ ρg ρd ρt a
  fnCap-renᵗ ρg ρd ρt (caseᵗ s l r) =
    cong₂ _⊔_ (fnCap-renᵗ ρg ρd ρt s)
              (cong₂ _⊔_ (fnCap-renᵗ ρg ρd (ext∈ ρt) l) (fnCap-renᵗ ρg ρd (ext∈ ρt) r))
  fnCap-renᵗ ρg ρd ρt (ifᵗ c a b)   =
    cong₂ _⊔_ (fnCap-renᵗ ρg ρd ρt c)
              (cong₂ _⊔_ (fnCap-renᵗ ρg ρd ρt a) (fnCap-renᵗ ρg ρd ρt b))
  fnCap-renᵗ ρg ρd ρt (primᵗ _ a)   = fnCap-renᵗ ρg ρd ρt a
  fnCap-renᵗ ρg ρd ρt (strmᵗ e)     = fnCap-renᵉ ρg ρd ρt e

  fnCap-renᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t}
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′)
    (ts : List (Tm Γ Δᵍ Δ Θ t)) → fnCapᵗˢ (renTms ρg ρd ρt ts) ≡ fnCapᵗˢ ts
  fnCap-renᵗˢ ρg ρd ρt []       = refl
  fnCap-renᵗˢ ρg ρd ρt (y ∷ ys) =
    cong₂ _⊔_ (cong₂ _⊔_ (caseW-ren ρg ρd ρt y) (fnCap-renᵗ ρg ρd ρt y))
              (fnCap-renᵗˢ ρg ρd ρt ys)

-- an env with every entry's fn-weight ≤ Ψ looks up values weighing ≤ Ψ
envfncap-lookup : ∀ {n} {Γ : Ctx n} {Θ} (Ψ : ℕ) (σ : All (Val Γ) Θ) →
  EnvFnCap Ψ σ → ∀ {t} (z : t ∈ Θ) → fnCapᵛ t (lookupEnv σ z) ≤ Ψ
envfncap-lookup Ψ (v ∷ᵃ σ) (h , hσ) (here refl) = h
envfncap-lookup Ψ (v ∷ᵃ σ) (h , hσ) (there z)   = envfncap-lookup Ψ σ hσ z

-- (W2) reification reads the value's own fn-cap (strmᵗ carries the obs
-- payload's fnCapᵉ; every other node folds by ⊔).
fnCap-reify : ∀ {n} {Γ : Ctx n} (t : Ty) (v : Val Γ t) →
  fnCapᵗ (reify v) ≡ fnCapᵛ t v
fnCap-reify unitᵗ   _        = refl
fnCap-reify boolᵗ   _        = refl
fnCap-reify natᵗ    _        = refl
fnCap-reify (s ×ᵗ t) (a , b) = cong₂ _⊔_ (fnCap-reify s a) (fnCap-reify t b)
fnCap-reify (s +ᵗ t) (inj₁ a) = fnCap-reify s a
fnCap-reify (s +ᵗ t) (inj₂ b) = fnCap-reify t b
fnCap-reify (obs t)  e       = refl

-- (W2) substitution keeps every embedded fn-weight ≤ Ψ: template positions
-- stay by ⊔-decomposition of the hypothesis, plugged var positions become
-- wkTm (reify …) whose weight is the env entry's (fnCap-ren + fnCap-reify +
-- the env cap).  Mutual over ᵉ/ᵗ/ᵗˢ; caseWᵗ of substituted fns rides W1.
mutual
  fnCap-subΘᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (Ψ : ℕ) (Θloc : List Ty)
    (σ : All (Val Γ) Θsub) (e : Exp Γ Δᵍ Δ (Θloc ++ Θsub) t) →
    EnvFnCap Ψ σ → fnCapᵉ e ≤ Ψ → fnCapᵉ (subΘExp Θloc σ e) ≤ Ψ
  fnCap-subΘᵉ Ψ Θloc σ (input i)       hσ h = z≤n
  fnCap-subΘᵉ Ψ Θloc σ (ofᵉ ts)        hσ h = fnCap-subΘᵗˢ Ψ Θloc σ ts hσ h
  fnCap-subΘᵉ Ψ Θloc σ emptyᵉ          hσ h = z≤n
  fnCap-subΘᵉ Ψ Θloc σ (mapᵉ {s = s} f e) hσ h =
    let hf = ⊔ˡ (caseWᵗ f ⊔ fnCapᵗ f) (fnCapᵉ e) h
    in ⊔-lub (⊔-lub (subst (_≤ Ψ) (sym (caseW-subΘ (s ∷ Θloc) σ f)) (⊔ˡ (caseWᵗ f) (fnCapᵗ f) hf))
                    (fnCap-subΘᵗ Ψ (s ∷ Θloc) σ f hσ (⊔ʳ (caseWᵗ f) (fnCapᵗ f) hf)))
             (fnCap-subΘᵉ Ψ Θloc σ e hσ (⊔ʳ (caseWᵗ f ⊔ fnCapᵗ f) (fnCapᵉ e) h))
  fnCap-subΘᵉ Ψ Θloc σ (takeᵉ c e)     hσ h =
    let hc = ⊔ˡ (caseWᵗ c ⊔ fnCapᵗ c) (fnCapᵉ e) h
    in ⊔-lub (⊔-lub (subst (_≤ Ψ) (sym (caseW-subΘ Θloc σ c)) (⊔ˡ (caseWᵗ c) (fnCapᵗ c) hc))
                    (fnCap-subΘᵗ Ψ Θloc σ c hσ (⊔ʳ (caseWᵗ c) (fnCapᵗ c) hc)))
             (fnCap-subΘᵉ Ψ Θloc σ e hσ (⊔ʳ (caseWᵗ c ⊔ fnCapᵗ c) (fnCapᵉ e) h))
  fnCap-subΘᵉ Ψ Θloc σ (scanᵉ {s = s} {t = t} f z e) hσ h =
    let hf  = ⊔ˡ (caseWᵗ f ⊔ fnCapᵗ f) ((caseWᵗ z ⊔ fnCapᵗ z) ⊔ fnCapᵉ e) h
        hze = ⊔ʳ (caseWᵗ f ⊔ fnCapᵗ f) ((caseWᵗ z ⊔ fnCapᵗ z) ⊔ fnCapᵉ e) h
        hz  = ⊔ˡ (caseWᵗ z ⊔ fnCapᵗ z) (fnCapᵉ e) hze
    in ⊔-lub (⊔-lub (subst (_≤ Ψ) (sym (caseW-subΘ ((t ×ᵗ s) ∷ Θloc) σ f)) (⊔ˡ (caseWᵗ f) (fnCapᵗ f) hf))
                    (fnCap-subΘᵗ Ψ ((t ×ᵗ s) ∷ Θloc) σ f hσ (⊔ʳ (caseWᵗ f) (fnCapᵗ f) hf)))
             (⊔-lub (⊔-lub (subst (_≤ Ψ) (sym (caseW-subΘ Θloc σ z)) (⊔ˡ (caseWᵗ z) (fnCapᵗ z) hz))
                           (fnCap-subΘᵗ Ψ Θloc σ z hσ (⊔ʳ (caseWᵗ z) (fnCapᵗ z) hz)))
                    (fnCap-subΘᵉ Ψ Θloc σ e hσ (⊔ʳ (caseWᵗ z ⊔ fnCapᵗ z) (fnCapᵉ e) hze)))
  fnCap-subΘᵉ Ψ Θloc σ (mergeAllᵉ e)   hσ h = fnCap-subΘᵉ Ψ Θloc σ e hσ h
  fnCap-subΘᵉ Ψ Θloc σ (concatAllᵉ e)  hσ h = fnCap-subΘᵉ Ψ Θloc σ e hσ h
  fnCap-subΘᵉ Ψ Θloc σ (switchAllᵉ e)  hσ h = fnCap-subΘᵉ Ψ Θloc σ e hσ h
  fnCap-subΘᵉ Ψ Θloc σ (exhaustAllᵉ e) hσ h = fnCap-subΘᵉ Ψ Θloc σ e hσ h
  fnCap-subΘᵉ Ψ Θloc σ (μᵉ e)          hσ h = fnCap-subΘᵉ Ψ Θloc σ e hσ h
  fnCap-subΘᵉ Ψ Θloc σ (varᵉ x)        hσ h = z≤n
  fnCap-subΘᵉ Ψ Θloc σ (deferᵉ e)      hσ h = fnCap-subΘᵉ Ψ Θloc σ e hσ h

  fnCap-subΘᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (Ψ : ℕ) (Θloc : List Ty)
    (σ : All (Val Γ) Θsub) (tm : Tm Γ Δᵍ Δ (Θloc ++ Θsub) t) →
    EnvFnCap Ψ σ → fnCapᵗ tm ≤ Ψ → fnCapᵗ (subΘTm Θloc σ tm) ≤ Ψ
  fnCap-subΘᵗ Ψ Θloc σ (varᵗ x) hσ h with ∈-++⁻ Θloc x
  ... | inj₁ y = z≤n
  ... | inj₂ z =
    subst (_≤ Ψ)
      (sym (trans (fnCap-renᵗ (λ ()) (λ ()) (λ ()) (reify (lookupEnv σ z)))
                  (fnCap-reify _ (lookupEnv σ z))))
      (envfncap-lookup Ψ σ hσ z)
  fnCap-subΘᵗ Ψ Θloc σ unit̂         hσ h = z≤n
  fnCap-subΘᵗ Ψ Θloc σ (bool̂ _)     hσ h = z≤n
  fnCap-subΘᵗ Ψ Θloc σ (nat̂ _)      hσ h = z≤n
  fnCap-subΘᵗ Ψ Θloc σ (pairᵗ a b)  hσ h =
    ⊔-lub (fnCap-subΘᵗ Ψ Θloc σ a hσ (⊔ˡ (fnCapᵗ a) (fnCapᵗ b) h))
          (fnCap-subΘᵗ Ψ Θloc σ b hσ (⊔ʳ (fnCapᵗ a) (fnCapᵗ b) h))
  fnCap-subΘᵗ Ψ Θloc σ (fstᵗ p)     hσ h = fnCap-subΘᵗ Ψ Θloc σ p hσ h
  fnCap-subΘᵗ Ψ Θloc σ (sndᵗ p)     hσ h = fnCap-subΘᵗ Ψ Θloc σ p hσ h
  fnCap-subΘᵗ Ψ Θloc σ (inlᵗ a)     hσ h = fnCap-subΘᵗ Ψ Θloc σ a hσ h
  fnCap-subΘᵗ Ψ Θloc σ (inrᵗ a)     hσ h = fnCap-subΘᵗ Ψ Θloc σ a hσ h
  fnCap-subΘᵗ Ψ Θloc σ (caseᵗ {s = s} {t = t} sc l r) hσ h =
    let hlr = ⊔ʳ (fnCapᵗ sc) (fnCapᵗ l ⊔ fnCapᵗ r) h
    in ⊔-lub (fnCap-subΘᵗ Ψ Θloc σ sc hσ (⊔ˡ (fnCapᵗ sc) (fnCapᵗ l ⊔ fnCapᵗ r) h))
             (⊔-lub (fnCap-subΘᵗ Ψ (s ∷ Θloc) σ l hσ (⊔ˡ (fnCapᵗ l) (fnCapᵗ r) hlr))
                    (fnCap-subΘᵗ Ψ (t ∷ Θloc) σ r hσ (⊔ʳ (fnCapᵗ l) (fnCapᵗ r) hlr)))
  fnCap-subΘᵗ Ψ Θloc σ (ifᵗ c a b)  hσ h =
    let hab = ⊔ʳ (fnCapᵗ c) (fnCapᵗ a ⊔ fnCapᵗ b) h
    in ⊔-lub (fnCap-subΘᵗ Ψ Θloc σ c hσ (⊔ˡ (fnCapᵗ c) (fnCapᵗ a ⊔ fnCapᵗ b) h))
             (⊔-lub (fnCap-subΘᵗ Ψ Θloc σ a hσ (⊔ˡ (fnCapᵗ a) (fnCapᵗ b) hab))
                    (fnCap-subΘᵗ Ψ Θloc σ b hσ (⊔ʳ (fnCapᵗ a) (fnCapᵗ b) hab)))
  fnCap-subΘᵗ Ψ Θloc σ (primᵗ _ a)  hσ h = fnCap-subΘᵗ Ψ Θloc σ a hσ h
  fnCap-subΘᵗ Ψ Θloc σ (strmᵗ e)    hσ h = fnCap-subΘᵉ Ψ Θloc σ e hσ h

  fnCap-subΘᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (Ψ : ℕ) (Θloc : List Ty)
    (σ : All (Val Γ) Θsub) (ts : List (Tm Γ Δᵍ Δ (Θloc ++ Θsub) t)) →
    EnvFnCap Ψ σ → fnCapᵗˢ ts ≤ Ψ → fnCapᵗˢ (subΘTms Θloc σ ts) ≤ Ψ
  fnCap-subΘᵗˢ Ψ Θloc σ []       hσ h = z≤n
  fnCap-subΘᵗˢ Ψ Θloc σ (x ∷ xs) hσ h =
    let hx = ⊔ˡ (caseWᵗ x ⊔ fnCapᵗ x) (fnCapᵗˢ xs) h
    in ⊔-lub (⊔-lub (subst (_≤ Ψ) (sym (caseW-subΘ Θloc σ x)) (⊔ˡ (caseWᵗ x) (fnCapᵗ x) hx))
                    (fnCap-subΘᵗ Ψ Θloc σ x hσ (⊔ʳ (caseWᵗ x) (fnCapᵗ x) hx)))
             (fnCap-subΘᵗˢ Ψ Θloc σ xs hσ (⊔ʳ (caseWᵗ x ⊔ fnCapᵗ x) (fnCapᵗˢ xs) h))

-- caseW is invariant under global/deferred var elimination
-- (caseWᵗ(strmᵗ _) = 0 regardless; all other constructors map point-to-point)
caseW-elimGᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
  (cl : Closed Γ t) (tm : Tm Γ Δᵍ Δ Θ u) →
  caseWᵗ (elimGTm x cl tm) ≡ caseWᵗ tm
caseW-elimGᵗ x cl (varᵗ y)      = refl
caseW-elimGᵗ x cl unit̂          = refl
caseW-elimGᵗ x cl (bool̂ _)      = refl
caseW-elimGᵗ x cl (nat̂ _)       = refl
caseW-elimGᵗ x cl (pairᵗ a b)   = cong₂ _+_ (caseW-elimGᵗ x cl a) (caseW-elimGᵗ x cl b)
caseW-elimGᵗ x cl (fstᵗ p)      = caseW-elimGᵗ x cl p
caseW-elimGᵗ x cl (sndᵗ p)      = caseW-elimGᵗ x cl p
caseW-elimGᵗ x cl (inlᵗ a)      = caseW-elimGᵗ x cl a
caseW-elimGᵗ x cl (inrᵗ a)      = caseW-elimGᵗ x cl a
caseW-elimGᵗ x cl (caseᵗ s l r) =
  cong (2 +_) (cong₂ _+_ (cong₂ _+_ (caseW-elimGᵗ x cl s) (caseW-elimGᵗ x cl l))
                           (caseW-elimGᵗ x cl r))
caseW-elimGᵗ x cl (ifᵗ c a b)   =
  cong₂ _+_ (cong₂ _+_ (caseW-elimGᵗ x cl c) (caseW-elimGᵗ x cl a)) (caseW-elimGᵗ x cl b)
caseW-elimGᵗ x cl (primᵗ _ a)   = caseW-elimGᵗ x cl a
caseW-elimGᵗ x cl (strmᵗ e)     = refl

caseW-elimDᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δ)
  (cl : Closed Γ t) (tm : Tm Γ Δᵍ Δ Θ u) →
  caseWᵗ (elimDTm x cl tm) ≡ caseWᵗ tm
caseW-elimDᵗ x cl (varᵗ y)      = refl
caseW-elimDᵗ x cl unit̂          = refl
caseW-elimDᵗ x cl (bool̂ _)      = refl
caseW-elimDᵗ x cl (nat̂ _)       = refl
caseW-elimDᵗ x cl (pairᵗ a b)   = cong₂ _+_ (caseW-elimDᵗ x cl a) (caseW-elimDᵗ x cl b)
caseW-elimDᵗ x cl (fstᵗ p)      = caseW-elimDᵗ x cl p
caseW-elimDᵗ x cl (sndᵗ p)      = caseW-elimDᵗ x cl p
caseW-elimDᵗ x cl (inlᵗ a)      = caseW-elimDᵗ x cl a
caseW-elimDᵗ x cl (inrᵗ a)      = caseW-elimDᵗ x cl a
caseW-elimDᵗ x cl (caseᵗ s l r) =
  cong (2 +_) (cong₂ _+_ (cong₂ _+_ (caseW-elimDᵗ x cl s) (caseW-elimDᵗ x cl l))
                           (caseW-elimDᵗ x cl r))
caseW-elimDᵗ x cl (ifᵗ c a b)   =
  cong₂ _+_ (cong₂ _+_ (caseW-elimDᵗ x cl c) (caseW-elimDᵗ x cl a)) (caseW-elimDᵗ x cl b)
caseW-elimDᵗ x cl (primᵗ _ a)   = caseW-elimDᵗ x cl a
caseW-elimDᵗ x cl (strmᵗ e)     = refl

-- subst on the Δ-index of Exp is transparent to fnCapᵉ (J on the equality)
fnCap-substᴱ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Δ′ Θ t} (p : Δ ≡ Δ′) (e : Exp Γ Δᵍ Δ Θ t) →
  fnCapᵉ (subst (λ ζ → Exp Γ Δᵍ ζ Θ t) p e) ≡ fnCapᵉ e
fnCap-substᴱ refl e = refl

-- if a' ≤ a ⊔ c and b' ≤ b ⊔ c then a' ⊔ b' ≤ (a ⊔ b) ⊔ c
-- every ⊔ index is given by name: left to itself, these _ 's are metas
-- under a stuck ⊔ and the solver cannot pick them
⊔-elim-help : ∀ {a' b'} (a b c : ℕ) →
  a' ≤ a ⊔ c → b' ≤ b ⊔ c → a' ⊔ b' ≤ (a ⊔ b) ⊔ c
⊔-elim-help a b c ha hb =
  ⊔-lub (≤-trans ha (⊔-mono-≤ (m≤m⊔n a b) (≤-refl {c})))
        (≤-trans hb (⊔-mono-≤ (m≤n⊔m a b) (≤-refl {c})))

-- (cw ⊔ fc) pair bound after elimG/D, using caseW invariance + fnCap IH
fn-comb-G : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ) (cl : Closed Γ t)
  (tm : Tm Γ Δᵍ Δ Θ u) (C : ℕ) →
  fnCapᵗ (elimGTm x cl tm) ≤ fnCapᵗ tm ⊔ C →
  (caseWᵗ (elimGTm x cl tm) ⊔ fnCapᵗ (elimGTm x cl tm)) ≤ (caseWᵗ tm ⊔ fnCapᵗ tm) ⊔ C
fn-comb-G x cl tm C h =
  ⊔-lub (subst (_≤ (caseWᵗ tm ⊔ fnCapᵗ tm) ⊔ C) (sym (caseW-elimGᵗ x cl tm))
               (≤-trans (m≤m⊔n (caseWᵗ tm) (fnCapᵗ tm))
                        (m≤m⊔n (caseWᵗ tm ⊔ fnCapᵗ tm) C)))
        (≤-trans h (⊔-mono-≤ (m≤n⊔m (caseWᵗ tm) (fnCapᵗ tm)) (≤-refl {C})))

fn-comb-D : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δ) (cl : Closed Γ t)
  (tm : Tm Γ Δᵍ Δ Θ u) (C : ℕ) →
  fnCapᵗ (elimDTm x cl tm) ≤ fnCapᵗ tm ⊔ C →
  (caseWᵗ (elimDTm x cl tm) ⊔ fnCapᵗ (elimDTm x cl tm)) ≤ (caseWᵗ tm ⊔ fnCapᵗ tm) ⊔ C
fn-comb-D x cl tm C h =
  ⊔-lub (subst (_≤ (caseWᵗ tm ⊔ fnCapᵗ tm) ⊔ C) (sym (caseW-elimDᵗ x cl tm))
               (≤-trans (m≤m⊔n (caseWᵗ tm) (fnCapᵗ tm))
                        (m≤m⊔n (caseWᵗ tm ⊔ fnCapᵗ tm) C)))
        (≤-trans h (⊔-mono-≤ (m≤n⊔m (caseWᵗ tm) (fnCapᵗ tm)) (≤-refl {C})))

-- (W2, remaining) elimG/D keep fnCap ≤ host ⊔ closure
mutual
  fnCap-elimG : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
    (cl : Closed Γ t) (e : Exp Γ Δᵍ Δ Θ u) →
    fnCapᵉ (elimGExp x cl e) ≤ fnCapᵉ e ⊔ fnCapᵉ cl
  fnCap-elimG x cl (input i)       = z≤n
  fnCap-elimG x cl (ofᵉ ts)        = fnCap-elimGᵗˢ x cl ts
  fnCap-elimG x cl emptyᵉ          = z≤n
  fnCap-elimG x cl (mapᵉ f e)      =
    ⊔-elim-help (caseWᵗ f ⊔ fnCapᵗ f) (fnCapᵉ e) (fnCapᵉ cl)
                (fn-comb-G x cl f (fnCapᵉ cl) (fnCap-elimGᵗ x cl f))
                (fnCap-elimG x cl e)
  fnCap-elimG x cl (takeᵉ c e)     =
    ⊔-elim-help (caseWᵗ c ⊔ fnCapᵗ c) (fnCapᵉ e) (fnCapᵉ cl)
                (fn-comb-G x cl c (fnCapᵉ cl) (fnCap-elimGᵗ x cl c))
                (fnCap-elimG x cl e)
  fnCap-elimG x cl (scanᵉ f z e)   =
    ⊔-elim-help (caseWᵗ f ⊔ fnCapᵗ f)
                ((caseWᵗ z ⊔ fnCapᵗ z) ⊔ fnCapᵉ e) (fnCapᵉ cl)
                (fn-comb-G x cl f (fnCapᵉ cl) (fnCap-elimGᵗ x cl f))
                (⊔-elim-help (caseWᵗ z ⊔ fnCapᵗ z) (fnCapᵉ e) (fnCapᵉ cl)
                              (fn-comb-G x cl z (fnCapᵉ cl) (fnCap-elimGᵗ x cl z))
                              (fnCap-elimG x cl e))
  fnCap-elimG x cl (mergeAllᵉ e)   = fnCap-elimG x cl e
  fnCap-elimG x cl (concatAllᵉ e)  = fnCap-elimG x cl e
  fnCap-elimG x cl (switchAllᵉ e)  = fnCap-elimG x cl e
  fnCap-elimG x cl (exhaustAllᵉ e) = fnCap-elimG x cl e
  fnCap-elimG x cl (μᵉ e)          = fnCap-elimG (there x) cl e
  fnCap-elimG x cl (varᵉ y)        = z≤n
  fnCap-elimG x cl (deferᵉ e)      =
    ≤-trans (≤-reflexive (fnCap-substᴱ (⊟-++ˡ x) (elimDExp (∈-++⁺ˡ x) cl e)))
            (fnCap-elimD (∈-++⁺ˡ x) cl e)

  fnCap-elimD : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δ)
    (cl : Closed Γ t) (e : Exp Γ Δᵍ Δ Θ u) →
    fnCapᵉ (elimDExp x cl e) ≤ fnCapᵉ e ⊔ fnCapᵉ cl
  fnCap-elimD x cl (input i)       = z≤n
  fnCap-elimD x cl (ofᵉ ts)        = fnCap-elimDᵗˢ x cl ts
  fnCap-elimD x cl emptyᵉ          = z≤n
  fnCap-elimD x cl (mapᵉ f e)      =
    ⊔-elim-help (caseWᵗ f ⊔ fnCapᵗ f) (fnCapᵉ e) (fnCapᵉ cl)
                (fn-comb-D x cl f (fnCapᵉ cl) (fnCap-elimDᵗ x cl f))
                (fnCap-elimD x cl e)
  fnCap-elimD x cl (takeᵉ c e)     =
    ⊔-elim-help (caseWᵗ c ⊔ fnCapᵗ c) (fnCapᵉ e) (fnCapᵉ cl)
                (fn-comb-D x cl c (fnCapᵉ cl) (fnCap-elimDᵗ x cl c))
                (fnCap-elimD x cl e)
  fnCap-elimD x cl (scanᵉ f z e)   =
    ⊔-elim-help (caseWᵗ f ⊔ fnCapᵗ f)
                ((caseWᵗ z ⊔ fnCapᵗ z) ⊔ fnCapᵉ e) (fnCapᵉ cl)
                (fn-comb-D x cl f (fnCapᵉ cl) (fnCap-elimDᵗ x cl f))
                (⊔-elim-help (caseWᵗ z ⊔ fnCapᵗ z) (fnCapᵉ e) (fnCapᵉ cl)
                              (fn-comb-D x cl z (fnCapᵉ cl) (fnCap-elimDᵗ x cl z))
                              (fnCap-elimD x cl e))
  fnCap-elimD x cl (mergeAllᵉ e)   = fnCap-elimD x cl e
  fnCap-elimD x cl (concatAllᵉ e)  = fnCap-elimD x cl e
  fnCap-elimD x cl (switchAllᵉ e)  = fnCap-elimD x cl e
  fnCap-elimD x cl (exhaustAllᵉ e) = fnCap-elimD x cl e
  fnCap-elimD x cl (μᵉ e)          = fnCap-elimD x cl e
  fnCap-elimD x cl (varᵉ y)        with compare∈ x y
  ... | inj₁ refl = ≤-reflexive (fnCap-renᵉ (λ ()) (λ ()) (λ ()) cl)
  ... | inj₂ y′   = z≤n
  fnCap-elimD {Δᵍ = Δᵍ} x cl (deferᵉ e) =
    ≤-trans (≤-reflexive (fnCap-substᴱ (⊟-++ʳ {Δᵍ = Δᵍ} x)
                                    (elimDExp (∈-++⁺ʳ Δᵍ x) cl e)))
            (fnCap-elimD (∈-++⁺ʳ Δᵍ x) cl e)

  fnCap-elimGᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
    (cl : Closed Γ t) (tm : Tm Γ Δᵍ Δ Θ u) →
    fnCapᵗ (elimGTm x cl tm) ≤ fnCapᵗ tm ⊔ fnCapᵉ cl
  fnCap-elimGᵗ x cl (varᵗ y)      = z≤n
  fnCap-elimGᵗ x cl unit̂          = z≤n
  fnCap-elimGᵗ x cl (bool̂ _)      = z≤n
  fnCap-elimGᵗ x cl (nat̂ _)       = z≤n
  fnCap-elimGᵗ x cl (pairᵗ a b)   =
    ⊔-elim-help (fnCapᵗ a) (fnCapᵗ b) (fnCapᵉ cl)
                (fnCap-elimGᵗ x cl a) (fnCap-elimGᵗ x cl b)
  fnCap-elimGᵗ x cl (fstᵗ p)      = fnCap-elimGᵗ x cl p
  fnCap-elimGᵗ x cl (sndᵗ p)      = fnCap-elimGᵗ x cl p
  fnCap-elimGᵗ x cl (inlᵗ a)      = fnCap-elimGᵗ x cl a
  fnCap-elimGᵗ x cl (inrᵗ a)      = fnCap-elimGᵗ x cl a
  fnCap-elimGᵗ x cl (caseᵗ s l r) =
    ⊔-elim-help (fnCapᵗ s) ((fnCapᵗ l) ⊔ (fnCapᵗ r)) (fnCapᵉ cl)
                (fnCap-elimGᵗ x cl s)
                (⊔-elim-help (fnCapᵗ l) (fnCapᵗ r) (fnCapᵉ cl)
                             (fnCap-elimGᵗ x cl l) (fnCap-elimGᵗ x cl r))
  fnCap-elimGᵗ x cl (ifᵗ c a b)   =
    ⊔-elim-help (fnCapᵗ c) ((fnCapᵗ a) ⊔ (fnCapᵗ b)) (fnCapᵉ cl)
                (fnCap-elimGᵗ x cl c)
                (⊔-elim-help (fnCapᵗ a) (fnCapᵗ b) (fnCapᵉ cl)
                             (fnCap-elimGᵗ x cl a) (fnCap-elimGᵗ x cl b))
  fnCap-elimGᵗ x cl (primᵗ _ a)   = fnCap-elimGᵗ x cl a
  fnCap-elimGᵗ x cl (strmᵗ e)     = fnCap-elimG x cl e

  fnCap-elimDᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δ)
    (cl : Closed Γ t) (tm : Tm Γ Δᵍ Δ Θ u) →
    fnCapᵗ (elimDTm x cl tm) ≤ fnCapᵗ tm ⊔ fnCapᵉ cl
  fnCap-elimDᵗ x cl (varᵗ y)      = z≤n
  fnCap-elimDᵗ x cl unit̂          = z≤n
  fnCap-elimDᵗ x cl (bool̂ _)      = z≤n
  fnCap-elimDᵗ x cl (nat̂ _)       = z≤n
  fnCap-elimDᵗ x cl (pairᵗ a b)   =
    ⊔-elim-help (fnCapᵗ a) (fnCapᵗ b) (fnCapᵉ cl)
                (fnCap-elimDᵗ x cl a) (fnCap-elimDᵗ x cl b)
  fnCap-elimDᵗ x cl (fstᵗ p)      = fnCap-elimDᵗ x cl p
  fnCap-elimDᵗ x cl (sndᵗ p)      = fnCap-elimDᵗ x cl p
  fnCap-elimDᵗ x cl (inlᵗ a)      = fnCap-elimDᵗ x cl a
  fnCap-elimDᵗ x cl (inrᵗ a)      = fnCap-elimDᵗ x cl a
  fnCap-elimDᵗ x cl (caseᵗ s l r) =
    ⊔-elim-help (fnCapᵗ s) ((fnCapᵗ l) ⊔ (fnCapᵗ r)) (fnCapᵉ cl)
                (fnCap-elimDᵗ x cl s)
                (⊔-elim-help (fnCapᵗ l) (fnCapᵗ r) (fnCapᵉ cl)
                             (fnCap-elimDᵗ x cl l) (fnCap-elimDᵗ x cl r))
  fnCap-elimDᵗ x cl (ifᵗ c a b)   =
    ⊔-elim-help (fnCapᵗ c) ((fnCapᵗ a) ⊔ (fnCapᵗ b)) (fnCapᵉ cl)
                (fnCap-elimDᵗ x cl c)
                (⊔-elim-help (fnCapᵗ a) (fnCapᵗ b) (fnCapᵉ cl)
                             (fnCap-elimDᵗ x cl a) (fnCap-elimDᵗ x cl b))
  fnCap-elimDᵗ x cl (primᵗ _ a)   = fnCap-elimDᵗ x cl a
  fnCap-elimDᵗ x cl (strmᵗ e)     = fnCap-elimD x cl e

  fnCap-elimGᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
    (cl : Closed Γ t) (ts : List (Tm Γ Δᵍ Δ Θ u)) →
    fnCapᵗˢ (elimGTms x cl ts) ≤ fnCapᵗˢ ts ⊔ fnCapᵉ cl
  fnCap-elimGᵗˢ x cl []       = z≤n
  fnCap-elimGᵗˢ x cl (y ∷ ys) =
    ⊔-elim-help (caseWᵗ y ⊔ fnCapᵗ y) (fnCapᵗˢ ys) (fnCapᵉ cl)
                (fn-comb-G x cl y (fnCapᵉ cl) (fnCap-elimGᵗ x cl y))
                (fnCap-elimGᵗˢ x cl ys)

  fnCap-elimDᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δ)
    (cl : Closed Γ t) (ts : List (Tm Γ Δᵍ Δ Θ u)) →
    fnCapᵗˢ (elimDTms x cl ts) ≤ fnCapᵗˢ ts ⊔ fnCapᵉ cl
  fnCap-elimDᵗˢ x cl []       = z≤n
  fnCap-elimDᵗˢ x cl (y ∷ ys) =
    ⊔-elim-help (caseWᵗ y ⊔ fnCapᵗ y) (fnCapᵗˢ ys) (fnCapᵉ cl)
                (fn-comb-D x cl y (fnCapᵉ cl) (fnCap-elimDᵗ x cl y))
                (fnCap-elimDᵗˢ x cl ys)

-- every term has at least one node
sizeᵗ-pos : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (tm : Tm Γ Δᵍ Δ Θ t) → 1 ≤ sizeᵗ tm
sizeᵗ-pos (varᵗ _)      = s≤s z≤n
sizeᵗ-pos unit̂          = s≤s z≤n
sizeᵗ-pos (bool̂ _)      = s≤s z≤n
sizeᵗ-pos (nat̂ _)       = s≤s z≤n
sizeᵗ-pos (pairᵗ _ _)   = s≤s z≤n
sizeᵗ-pos (fstᵗ _)      = s≤s z≤n
sizeᵗ-pos (sndᵗ _)      = s≤s z≤n
sizeᵗ-pos (inlᵗ _)      = s≤s z≤n
sizeᵗ-pos (inrᵗ _)      = s≤s z≤n
sizeᵗ-pos (caseᵗ _ _ _) = s≤s z≤n
sizeᵗ-pos (ifᵗ _ _ _)   = s≤s z≤n
sizeᵗ-pos (primᵗ _ _)   = s≤s z≤n
sizeᵗ-pos (strmᵗ _)     = s≤s z≤n

-- a cap scaled by a positive size factor still dominates 1, and (at a
-- positive exponent) the base cap itself
one≤scaled : ∀ V N k → 1 ≤ N → 1 ≤ N * ((2 + 2 * V) ^ k)
one≤scaled V N k hN =
  ≤-trans (≤-reflexive (sym (+-identityʳ 1))) (*-mono-≤ hN (one≤pow V k))

C≤scaled : ∀ V N k → 1 ≤ N → 1 ≤ k → 2 + 2 * V ≤ N * ((2 + 2 * V) ^ k)
C≤scaled V N k hN hk =
  ≤-trans (pow1 V hk)
          (≤-trans (≤-reflexive (sym (+-identityʳ ((2 + 2 * V) ^ k))))
                   (*-monoˡ-≤ ((2 + 2 * V) ^ k) hN))

-- 3^ss + 3 ≤ 3^(2+ss):  Y + 3 ≤ 4·Y ≤ 9·Y
pow3+3 : ∀ ss → 3 ^ ss + 3 ≤ 3 ^ (2 + ss)
pow3+3 ss = ≤-trans lo hi
  where
  Y = 3 ^ ss
  -- 3 = 3 * 1 ≤ 3 * Y
  lo : 3 ^ ss + 3 ≤ Y + 3 * Y
  lo = +-monoʳ-≤ Y (*-monoʳ-≤ 3 (one≤3^ ss))
  -- 3 ^ (2 + ss) IS 3 * (3 * Y).  Everything here is given explicitly:
  -- a metavariable under _*_ would send the unifier inverting
  -- multiplication against the stuck Y
  hi : Y + 3 * Y ≤ 3 ^ (2 + ss)
  hi = +-mono-≤ (m≤m+n Y (Y + (Y + 0))) (m≤m+n (3 * Y) (3 * Y + 0))

-- the sharp case hop's exponent arithmetic: the scrutinee's exponent
-- plus the base swap's three units, times the branch's, inside 3^(2+K)
case-exp-sharp : ∀ ss b K → ss + b ≤ K → (3 ^ ss + 3) * 3 ^ b ≤ 3 ^ (2 + K)
case-exp-sharp ss b K h =
  ≤-trans (*-monoˡ-≤ (3 ^ b) (pow3+3 ss))
  (≤-trans (≤-reflexive (sym (^-distribˡ-+-* 3 (2 + ss) b)))
           (^-monoʳ-≤ 3 (s≤s (s≤s h))))

-- the base swap: a cap scaled by a size factor N ≤ C costs the
-- exponent three units — one for N, two for the 2+2· wrapper
sharp-base : ∀ V N p → N ≤ 2 + 2 * V →
  2 + 2 * (N * ((2 + 2 * V) ^ p)) ≤ (2 + 2 * V) ^ (p + 3)
sharp-base V N p hN =
  ≤-trans (+-monoʳ-≤ 2 (*-monoʳ-≤ 2 (*-monoˡ-≤ ((2 + 2 * V) ^ p) hN)))
  (≤-trans (grow-pow V (suc p))
           (≤-reflexive (cong ((2 + 2 * V) ^_) (sym (+-suc p 2)))))

pow3-hop-sharp : ∀ V (N p q E : ℕ) → N ≤ 2 + 2 * V → (p + 3) * q ≤ E →
  (2 + 2 * (N * ((2 + 2 * V) ^ p))) ^ q ≤ (2 + 2 * V) ^ E
pow3-hop-sharp V N p q E hN hE =
  ≤-trans (^-monoˡ-≤ q (sharp-base V N p hN))
  (≤-trans (≤-reflexive (^-*-assoc (2 + 2 * V) (p + 3) q))
           (^-monoʳ-≤ (2 + 2 * V) hE))

-- one caseᵗ branch: its bound over the GROWN cap (base scaled by the
-- scrutinee's size) collapses back to the host cap at 3^(2+K)
case-branch : ∀ V (X ssc sl S csc cl K : ℕ) →
  X ≤ sl * (2 + 2 * (ssc * ((2 + 2 * V) ^ (3 ^ csc)))) ^ (3 ^ cl) →
  ssc ≤ V → sl ≤ S → csc + cl ≤ K →
  X ≤ S * (2 + 2 * V) ^ (3 ^ (2 + K))
case-branch V X ssc sl S csc cl K hX hssc hsl hK =
  ≤-trans hX
    (*-mono-≤ hsl
      (pow3-hop-sharp V ssc (3 ^ csc) (3 ^ cl) (3 ^ (2 + K))
        (≤-trans hssc (V≤C V))
        (case-exp-sharp csc cl K hK)))

-- (W3) THE SHARP EVAL BOUND — the walk ledger's load-bearing fact.
-- Same induction as evalWith-size, but the sizeᵗ factor out front
-- absorbs every constructor's +1, so caseᵗ is the ONLY clause that
-- moves the exponent: it re-enters at the grown cap (base carrying
-- the scrutinee's size factor, cost three exponent units) and
-- collapses through case-branch.  Every other clause stays at V.
-- The strmᵗ clause is size-subΘᵉ (linear), exponent 3^0 = 1.
evalWith-sharp : ∀ {n} {Γ : Ctx n} {Θ t} (V : ℕ)
  (tm : Tm Γ [] [] Θ t) (env : All (Val Γ) Θ) →
  EnvSize V env → sizeᵗ tm ≤ V →
  sizeᵛ t (evalWith tm env) ≤ sizeᵗ tm * (2 + 2 * V) ^ (3 ^ caseWᵗ tm)
evalWith-sharp V (varᵗ x) env hσ hsz =
  ≤-trans (envSize-lookup V env hσ x)
          (≤-trans (V≤C V) (C≤scaled V 1 1 ≤-refl ≤-refl))
evalWith-sharp V unit̂     env hσ hsz = one≤scaled V 1 1 ≤-refl
evalWith-sharp V (bool̂ _) env hσ hsz = one≤scaled V 1 1 ≤-refl
evalWith-sharp V (nat̂ _)  env hσ hsz = one≤scaled V 1 1 ≤-refl
evalWith-sharp V (pairᵗ a b) env hσ hsz =
  sucmul (sizeᵗ a + sizeᵗ b) M
    (sum2 (sizeᵗ a) (sizeᵗ b) M
      (≤-trans (evalWith-sharp V a env hσ
                 (≤-trans (≤-trans (m≤m+n (sizeᵗ a) (sizeᵗ b)) (n≤1+n _)) hsz))
               (*-monoʳ-≤ (sizeᵗ a)
                 (^-monoʳ-≤ (2 + 2 * V)
                   (^-monoʳ-≤ 3 (m≤m+n (caseWᵗ a) (caseWᵗ b))))))
      (≤-trans (evalWith-sharp V b env hσ
                 (≤-trans (≤-trans (m≤n+m (sizeᵗ b) (sizeᵗ a)) (n≤1+n _)) hsz))
               (*-monoʳ-≤ (sizeᵗ b)
                 (^-monoʳ-≤ (2 + 2 * V)
                   (^-monoʳ-≤ 3 (m≤n+m (caseWᵗ b) (caseWᵗ a)))))))
    (one≤pow V (3 ^ (caseWᵗ a + caseWᵗ b)))
  where M = (2 + 2 * V) ^ (3 ^ (caseWᵗ a + caseWᵗ b))
evalWith-sharp V (fstᵗ p) env hσ hsz
  with evalWith p env
     | evalWith-sharp V p env hσ (≤-trans (n≤1+n (sizeᵗ p)) hsz)
... | (a , b) | ihp =
  ≤-trans (≤-trans (m≤m+n (sizeᵛ _ a) (sizeᵛ _ b)) (n≤1+n _))
          (≤-trans ihp (*-monoˡ-≤ _ (n≤1+n (sizeᵗ p))))
evalWith-sharp V (sndᵗ p) env hσ hsz
  with evalWith p env
     | evalWith-sharp V p env hσ (≤-trans (n≤1+n (sizeᵗ p)) hsz)
... | (a , b) | ihp =
  ≤-trans (≤-trans (m≤n+m (sizeᵛ _ b) (sizeᵛ _ a)) (n≤1+n _))
          (≤-trans ihp (*-monoˡ-≤ _ (n≤1+n (sizeᵗ p))))
evalWith-sharp V (inlᵗ a) env hσ hsz =
  sucmul (sizeᵗ a) ((2 + 2 * V) ^ (3 ^ caseWᵗ a))
    (evalWith-sharp V a env hσ (≤-trans (n≤1+n (sizeᵗ a)) hsz))
    (one≤pow V (3 ^ caseWᵗ a))
evalWith-sharp V (inrᵗ a) env hσ hsz =
  sucmul (sizeᵗ a) ((2 + 2 * V) ^ (3 ^ caseWᵗ a))
    (evalWith-sharp V a env hσ (≤-trans (n≤1+n (sizeᵗ a)) hsz))
    (one≤pow V (3 ^ caseWᵗ a))
evalWith-sharp V (caseᵗ {s = s} {t = t} sc l r) env hσ hsz
  with evalWith sc env
     | evalWith-sharp V sc env hσ
         (≤-trans (≤-trans (m≤m+n (sizeᵗ sc) (sizeᵗ l))
                    (≤-trans (m≤m+n (sizeᵗ sc + sizeᵗ l) (sizeᵗ r))
                             (n≤1+n _))) hsz)
... | inj₁ a | ihsc =
  case-branch V _ (sizeᵗ sc) (sizeᵗ l) _ (caseWᵗ sc) (caseWᵗ l) _
    (evalWith-sharp (sizeᵗ sc * ((2 + 2 * V) ^ (3 ^ caseWᵗ sc))) l (a ∷ᵃ env)
      (≤-trans (n≤1+n _) ihsc , envSize-widen hV env hσ)
      (≤-trans (≤-trans hbr hsz) hV))
    hsc hbr (m≤m+n (caseWᵗ sc + caseWᵗ l) (caseWᵗ r))
  where
  hsc : sizeᵗ sc ≤ V
  hsc = ≤-trans (≤-trans (m≤m+n (sizeᵗ sc) (sizeᵗ l))
                  (≤-trans (m≤m+n (sizeᵗ sc + sizeᵗ l) (sizeᵗ r))
                           (n≤1+n _))) hsz
  hbr : sizeᵗ l ≤ suc ((sizeᵗ sc + sizeᵗ l) + sizeᵗ r)
  hbr = ≤-trans (m≤n+m (sizeᵗ l) (sizeᵗ sc))
                (≤-trans (m≤m+n (sizeᵗ sc + sizeᵗ l) (sizeᵗ r)) (n≤1+n _))
  hV : V ≤ sizeᵗ sc * ((2 + 2 * V) ^ (3 ^ caseWᵗ sc))
  hV = ≤-trans (V≤C V)
         (C≤scaled V (sizeᵗ sc) (3 ^ caseWᵗ sc)
                   (sizeᵗ-pos sc) (one≤3^ (caseWᵗ sc)))
... | inj₂ b | ihsc =
  case-branch V _ (sizeᵗ sc) (sizeᵗ r) _ (caseWᵗ sc) (caseWᵗ r) _
    (evalWith-sharp (sizeᵗ sc * ((2 + 2 * V) ^ (3 ^ caseWᵗ sc))) r (b ∷ᵃ env)
      (≤-trans (n≤1+n _) ihsc , envSize-widen hV env hσ)
      (≤-trans (≤-trans hbr hsz) hV))
    hsc hbr (+-monoˡ-≤ (caseWᵗ r) (m≤m+n (caseWᵗ sc) (caseWᵗ l)))
  where
  hsc : sizeᵗ sc ≤ V
  hsc = ≤-trans (≤-trans (m≤m+n (sizeᵗ sc) (sizeᵗ l))
                  (≤-trans (m≤m+n (sizeᵗ sc + sizeᵗ l) (sizeᵗ r))
                           (n≤1+n _))) hsz
  hbr : sizeᵗ r ≤ suc ((sizeᵗ sc + sizeᵗ l) + sizeᵗ r)
  hbr = ≤-trans (m≤n+m (sizeᵗ r) (sizeᵗ sc + sizeᵗ l)) (n≤1+n _)
  hV : V ≤ sizeᵗ sc * ((2 + 2 * V) ^ (3 ^ caseWᵗ sc))
  hV = ≤-trans (V≤C V)
         (C≤scaled V (sizeᵗ sc) (3 ^ caseWᵗ sc)
                   (sizeᵗ-pos sc) (one≤3^ (caseWᵗ sc)))
evalWith-sharp V (ifᵗ c a b) env hσ hsz with evalWith c env
... | true =
  ≤-trans (evalWith-sharp V a env hσ (≤-trans hbr hsz))
          (*-mono-≤ hbr
            (^-monoʳ-≤ (2 + 2 * V)
              (^-monoʳ-≤ 3 (≤-trans (m≤n+m (caseWᵗ a) (caseWᵗ c))
                             (m≤m+n (caseWᵗ c + caseWᵗ a) (caseWᵗ b))))))
  where
  hbr : sizeᵗ a ≤ suc ((sizeᵗ c + sizeᵗ a) + sizeᵗ b)
  hbr = ≤-trans (m≤n+m (sizeᵗ a) (sizeᵗ c))
                (≤-trans (m≤m+n (sizeᵗ c + sizeᵗ a) (sizeᵗ b)) (n≤1+n _))
... | false =
  ≤-trans (evalWith-sharp V b env hσ (≤-trans hbr hsz))
          (*-mono-≤ hbr
            (^-monoʳ-≤ (2 + 2 * V)
              (^-monoʳ-≤ 3 (m≤n+m (caseWᵗ b) (caseWᵗ c + caseWᵗ a)))))
  where
  hbr : sizeᵗ b ≤ suc ((sizeᵗ c + sizeᵗ a) + sizeᵗ b)
  hbr = ≤-trans (m≤n+m (sizeᵗ b) (sizeᵗ c + sizeᵗ a)) (n≤1+n _)
evalWith-sharp V (primᵗ add arg)  env hσ hsz =
  one≤scaled V (suc (sizeᵗ arg)) (3 ^ caseWᵗ arg) (s≤s z≤n)
evalWith-sharp V (primᵗ sub arg)  env hσ hsz =
  one≤scaled V (suc (sizeᵗ arg)) (3 ^ caseWᵗ arg) (s≤s z≤n)
evalWith-sharp V (primᵗ mul arg)  env hσ hsz =
  one≤scaled V (suc (sizeᵗ arg)) (3 ^ caseWᵗ arg) (s≤s z≤n)
evalWith-sharp V (primᵗ eqᵖ arg)  env hσ hsz =
  one≤scaled V (suc (sizeᵗ arg)) (3 ^ caseWᵗ arg) (s≤s z≤n)
evalWith-sharp V (primᵗ ltᵖ arg)  env hσ hsz =
  one≤scaled V (suc (sizeᵗ arg)) (3 ^ caseWᵗ arg) (s≤s z≤n)
evalWith-sharp V (primᵗ notᵖ arg) env hσ hsz =
  one≤scaled V (suc (sizeᵗ arg)) (3 ^ caseWᵗ arg) (s≤s z≤n)
evalWith-sharp V (strmᵗ e) []ᵃ hσ hsz =
  ≤-trans (n≤1+n (sizeᵉ e))
          (≤-trans (≤-reflexive (sym (*-identityʳ (suc (sizeᵉ e)))))
                   (*-monoʳ-≤ (suc (sizeᵉ e)) (one≤pow V 1)))
evalWith-sharp V (strmᵗ e) (v ∷ᵃ vs) hσ hsz =
  ≤-trans (size-subΘᵉ V [] (v ∷ᵃ vs) e hσ)
          (*-mono-≤ (n≤1+n (sizeᵉ e))
            (≤-trans (n≤1+n (suc (2 * V)))
                     (≤-reflexive (sym (*-identityʳ (2 + 2 * V))))))

-- combine a sub-template's caseW and fnCap bounds against the host cap
cmb : ∀ {cw fw CW FW Ψ} → cw ≤ CW → fw ≤ FW → CW ⊔ FW ≤ Ψ → cw ⊔ fw ≤ Ψ
cmb hc hf h = ≤-trans (⊔-mono-≤ hc hf) h

-- (W4) eval never mints a new fn: every fn embedded in the result comes from
-- the template's strm-subtrees (subΘ'd — W2) or the environment.  Structural
-- induction shaped like evalWith-size; caseᵗ re-enters over the env extended
-- with the scrutinee component (whose weight is the scrutinee's own IH), ifᵗ
-- stays at env, strmᵗ is fnCap-subΘᵉ, literals/prims are fn-free.
fnCap-evalWith : ∀ {n} {Γ : Ctx n} {Θ t} (Ψ : ℕ)
  (tm : Tm Γ [] [] Θ t) (env : All (Val Γ) Θ) →
  EnvFnCap Ψ env → caseWᵗ tm ⊔ fnCapᵗ tm ≤ Ψ →
  fnCapᵛ t (evalWith tm env) ≤ Ψ
fnCap-evalWith Ψ (varᵗ x)  env hσ h = envfncap-lookup Ψ env hσ x
fnCap-evalWith Ψ unit̂      env hσ h = z≤n
fnCap-evalWith Ψ (bool̂ _)  env hσ h = z≤n
fnCap-evalWith Ψ (nat̂ _)   env hσ h = z≤n
fnCap-evalWith Ψ (pairᵗ a b) env hσ h =
  ⊔-lub (fnCap-evalWith Ψ a env hσ
           (cmb (m≤m+n (caseWᵗ a) (caseWᵗ b)) (m≤m⊔n (fnCapᵗ a) (fnCapᵗ b)) h))
        (fnCap-evalWith Ψ b env hσ
           (cmb (m≤n+m (caseWᵗ b) (caseWᵗ a)) (m≤n⊔m (fnCapᵗ a) (fnCapᵗ b)) h))
fnCap-evalWith Ψ (fstᵗ p) env hσ h with evalWith p env | fnCap-evalWith Ψ p env hσ h
... | (a , b) | ihp = ⊔ˡ (fnCapᵛ _ a) (fnCapᵛ _ b) ihp
fnCap-evalWith Ψ (sndᵗ p) env hσ h with evalWith p env | fnCap-evalWith Ψ p env hσ h
... | (a , b) | ihp = ⊔ʳ (fnCapᵛ _ a) (fnCapᵛ _ b) ihp
fnCap-evalWith Ψ (inlᵗ a) env hσ h = fnCap-evalWith Ψ a env hσ h
fnCap-evalWith Ψ (inrᵗ a) env hσ h = fnCap-evalWith Ψ a env hσ h
fnCap-evalWith Ψ (caseᵗ {s = s} {t = t} sc l r) env hσ h
  with evalWith sc env
     | fnCap-evalWith Ψ sc env hσ
         (cmb (≤-trans (m≤m+n (caseWᵗ sc) (caseWᵗ l))
                 (≤-trans (m≤m+n (caseWᵗ sc + caseWᵗ l) (caseWᵗ r))
                          (m≤n+m ((caseWᵗ sc + caseWᵗ l) + caseWᵗ r) 2)))
              (m≤m⊔n (fnCapᵗ sc) (fnCapᵗ l ⊔ fnCapᵗ r)) h)
... | inj₁ a | iha = fnCap-evalWith Ψ l (a ∷ᵃ env) (iha , hσ)
      (cmb (≤-trans (m≤n+m (caseWᵗ l) (caseWᵗ sc))
              (≤-trans (m≤m+n (caseWᵗ sc + caseWᵗ l) (caseWᵗ r))
                       (m≤n+m ((caseWᵗ sc + caseWᵗ l) + caseWᵗ r) 2)))
           (≤-trans (m≤m⊔n (fnCapᵗ l) (fnCapᵗ r)) (m≤n⊔m (fnCapᵗ sc) (fnCapᵗ l ⊔ fnCapᵗ r))) h)
... | inj₂ b | ihb = fnCap-evalWith Ψ r (b ∷ᵃ env) (ihb , hσ)
      (cmb (≤-trans (m≤n+m (caseWᵗ r) (caseWᵗ sc + caseWᵗ l))
                    (m≤n+m ((caseWᵗ sc + caseWᵗ l) + caseWᵗ r) 2))
           (≤-trans (m≤n⊔m (fnCapᵗ l) (fnCapᵗ r)) (m≤n⊔m (fnCapᵗ sc) (fnCapᵗ l ⊔ fnCapᵗ r))) h)
fnCap-evalWith Ψ (ifᵗ c a b) env hσ h with evalWith c env
... | true  = fnCap-evalWith Ψ a env hσ
      (cmb (≤-trans (m≤n+m (caseWᵗ a) (caseWᵗ c)) (m≤m+n (caseWᵗ c + caseWᵗ a) (caseWᵗ b)))
           (≤-trans (m≤m⊔n (fnCapᵗ a) (fnCapᵗ b)) (m≤n⊔m (fnCapᵗ c) (fnCapᵗ a ⊔ fnCapᵗ b))) h)
... | false = fnCap-evalWith Ψ b env hσ
      (cmb (m≤n+m (caseWᵗ b) (caseWᵗ c + caseWᵗ a))
           (≤-trans (m≤n⊔m (fnCapᵗ a) (fnCapᵗ b)) (m≤n⊔m (fnCapᵗ c) (fnCapᵗ a ⊔ fnCapᵗ b))) h)
fnCap-evalWith Ψ (primᵗ add arg)  env hσ h = z≤n
fnCap-evalWith Ψ (primᵗ sub arg)  env hσ h = z≤n
fnCap-evalWith Ψ (primᵗ mul arg)  env hσ h = z≤n
fnCap-evalWith Ψ (primᵗ eqᵖ arg)  env hσ h = z≤n
fnCap-evalWith Ψ (primᵗ ltᵖ arg)  env hσ h = z≤n
fnCap-evalWith Ψ (primᵗ notᵖ arg) env hσ h = z≤n
fnCap-evalWith Ψ (strmᵗ e) []ᵃ       hσ h = h
fnCap-evalWith Ψ (strmᵗ e) (v ∷ᵃ vs) hσ h = fnCap-subΘᵉ Ψ [] (v ∷ᵃ vs) e hσ h

-- the fold face of (W3), at the machine's applyFn sites
applyFn-sharp : ∀ {n} {Γ : Ctx n} {s t} (V : ℕ)
  (fn : Fn Γ [] [] [] s t) (v : Val Γ s) →
  sizeᵛ s v ≤ V → sizeᵗ fn ≤ V →
  sizeᵛ t (applyFn fn v) ≤ sizeᵗ fn * (2 + 2 * V) ^ (3 ^ caseWᵗ fn)
applyFn-sharp V fn v hv hf = evalWith-sharp V fn (v ∷ᵃ []ᵃ) (hv , tt) hf

------------------------------------------------------------------
-- the ledger: running cap capᴱ W₀ E, multiplicative receipts
------------------------------------------------------------------

capᴱ : ℕ → ℕ → ℕ
capᴱ W E = (2 + 2 * W) ^ E

spendᴱ : (Ψ r s : ℕ) → ℕ         -- r cheap edges (×2), s eval edges
spendᴱ Ψ r s = 2 ^ r * 3 ^ (suc Ψ * s)

capᴱ-mono : ∀ (W : ℕ) {E E′ : ℕ} → E ≤ E′ → capᴱ W E ≤ capᴱ W E′
capᴱ-mono W = ^-monoʳ-≤ (2 + 2 * W)

-- (W5) receipts compose multiplicatively (pure ^-arithmetic): the two
-- 2^r factors and the two 3^(κ·s) factors each merge by ^-distribˡ-+-*,
-- with the exponent split κ·s₁ + κ·s₂ = κ·(s₁+s₂) by *-distribˡ-+.  The
-- product rearrangement (a₁b₁)(a₂b₂) = (a₁a₂)(b₁b₂) is a semiring identity.
spendᴱ-compose : ∀ (Ψ r₁ s₁ r₂ s₂ : ℕ) →
  spendᴱ Ψ r₁ s₁ * spendᴱ Ψ r₂ s₂ ≡ spendᴱ Ψ (r₁ + r₂) (s₁ + s₂)
spendᴱ-compose Ψ r₁ s₁ r₂ s₂ =
  trans (rearrange (2 ^ r₁) (3 ^ (suc Ψ * s₁)) (2 ^ r₂) (3 ^ (suc Ψ * s₂)))
        (cong₂ _*_
          (sym (^-distribˡ-+-* 2 r₁ r₂))
          (trans (sym (^-distribˡ-+-* 3 (suc Ψ * s₁) (suc Ψ * s₂)))
                 (cong (3 ^_) (sym (*-distribˡ-+ (suc Ψ) s₁ s₂)))))
  where
  rearrange : ∀ (a₁ b₁ a₂ b₂ : ℕ) →
    (a₁ * b₁) * (a₂ * b₂) ≡ (a₁ * a₂) * (b₁ * b₂)
  rearrange = solve 4 (λ a₁ b₁ a₂ b₂ →
    (a₁ :* b₁) :* (a₂ :* b₂) := (a₁ :* a₂) :* (b₁ :* b₂)) refl

-- (W6) pair-size helpers: a scan fold feeds (ac,v) as a pair, so
-- the input size is 1+2C^E.  grow-pow3 handles the 3-story rebase;
-- pair-ledger-step closes the exponent recurrence at 3≤E.
grow-pow3 : ∀ W E → 4 + 4 * capᴱ W E ≤ capᴱ W (E + 3)
grow-pow3 W E =
  ≤-trans (+-monoˡ-≤ (4 * X) (*-monoʳ-≤ 4 (one≤pow W E)))
  (≤-trans (≤-reflexive (solve 1 (λ x → con 4 :* x :+ con 4 :* x := con 8 :* x) refl X))
  (≤-trans (*-monoˡ-≤ X (^-monoˡ-≤ 3 (2≤C W)))
           (≤-reflexive (trans (*-comm ((2 + 2 * W) ^ 3) X)
                               (sym (^-distribˡ-+-* (2 + 2 * W) E 3))))))
  where X = capᴱ W E

pair-ledger-step : ∀ (E w : ℕ) → 3 ≤ E → E + (E + 3) * 3 ^ w ≤ E * 3 ^ suc w
pair-ledger-step E w 3≤E =
  ≤-trans (+-mono-≤ E≤E3w (*-monoˡ-≤ (3 ^ w) E+3≤2E))
          (≤-reflexive (solve 2 (λ e x → e :* x :+ con 2 :* e :* x := e :* (con 3 :* x)) refl E (3 ^ w)))
  where
  E+3≤2E : E + 3 ≤ 2 * E
  E+3≤2E = ≤-trans (+-monoʳ-≤ E 3≤E)
                   (≤-reflexive (cong (E +_) (sym (+-identityʳ E))))
  E≤E3w : E ≤ E * 3 ^ w
  E≤E3w = ≤-trans (≤-reflexive (sym (*-identityʳ E)))
                  (*-monoʳ-≤ E (one≤3^ w))

-- (W6) the fold-run closed form: one scan run over a value list
-- of length m, everything (fn size, seed, values) within the
-- current cap at 3≤E, lands within the cap grown by 3^(suc caseW·m).
-- Recurrence: applyFn at the pair (ac,v) uses grow-pow3 + pair-ledger-step
-- in place of grow-pow + ledger-step.
scanVals-sharp : ∀ {n} {Γ : Ctx n} {s u} (W E : ℕ)
  (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (ac : Val Γ u)
  (vs : List (Val Γ s)) →
  3 ≤ E →
  sizeᵗ fn ≤ capᴱ W E → sizeᵛ u ac ≤ capᴱ W E →
  All (λ v → sizeᵛ s v ≤ capᴱ W E) vs →
  (sizeᵛ u (proj₂ (scanVals fn ac vs))
     ≤ capᴱ W (E * 3 ^ (suc (caseWᵗ fn) * length vs)))
  × All (λ o → sizeᵛ u o ≤ capᴱ W (E * 3 ^ (suc (caseWᵗ fn) * length vs)))
        (proj₁ (scanVals fn ac vs))
scanVals-sharp {s = s} {u = u} W E fn ac [] 3≤E hfn hacc _ =
  subst (λ e → sizeᵛ u ac ≤ capᴱ W e
               × All (λ o → sizeᵛ u o ≤ capᴱ W e) (proj₁ (scanVals fn ac [])))
    (sym (trans (cong (E *_) (cong (3 ^_) (trans (*-comm (suc (caseWᵗ fn)) 0) refl)))
                (*-identityʳ E)))
    (hacc , []ᵃ)
scanVals-sharp {s = s} {u = u} W E fn ac (v ∷ vs) 3≤E hfn hacc (hv ∷ᵃ hvs) =
  last-ok , acc'B₁ ∷ᵃ outs-ok
  where
  cw    = suc (caseWᵗ fn)
  m     = length vs
  C     = 2 + 2 * W
  E₁    = E * 3 ^ cw
  3≤E₁  = ≤-trans 3≤E (E≤E*3^ E cw)
  cap₁  = capᴱ-mono W (E≤E*3^ E cw)
  acc'  = applyFn fn (ac , v)

  -- pair bound: sizeᵛ (u×s) (ac,v) ≤ 1 + C^E + C^E
  pairB : sizeᵛ (u ×ᵗ s) (ac , v) ≤ 1 + capᴱ W E + capᴱ W E
  pairB = s≤s (+-mono-≤ hacc hv)

  -- 2 + 2*(1 + C^E + C^E) = 4 + 4*C^E  by ring arithmetic
  arith : 2 + 2 * (1 + capᴱ W E + capᴱ W E) ≡ 4 + 4 * capᴱ W E
  arith = solve 1 (λ x → con 2 :+ con 2 :* (con 1 :+ x :+ x) := con 4 :+ con 4 :* x)
                  refl (capᴱ W E)

  -- sizeᵗ fn ≤ 1 + C^E + C^E (widened from hfn)
  hf' : sizeᵗ fn ≤ 1 + capᴱ W E + capᴱ W E
  hf' = ≤-trans hfn (≤-trans (m≤n+m (capᴱ W E) (capᴱ W E)) (n≤1+n _))

  -- applyFn-sharp at V = 1 + C^E + C^E
  acc'sz : sizeᵛ u acc' ≤ sizeᵗ fn * (2 + 2 * (1 + capᴱ W E + capᴱ W E)) ^ 3 ^ caseWᵗ fn
  acc'sz = applyFn-sharp (1 + capᴱ W E + capᴱ W E) fn (ac , v) pairB hf'

  -- substitute arith to expose (4 + 4*C^E)^...
  acc'sz' : sizeᵛ u acc' ≤ sizeᵗ fn * (4 + 4 * capᴱ W E) ^ 3 ^ caseWᵗ fn
  acc'sz' = subst (λ b → sizeᵛ u acc' ≤ sizeᵗ fn * b ^ 3 ^ caseWᵗ fn) arith acc'sz

  -- grow-pow3: (4 + 4*C^E) ≤ C^(E+3); lift through ^
  step1 : sizeᵛ u acc' ≤ sizeᵗ fn * capᴱ W (E + 3) ^ 3 ^ caseWᵗ fn
  step1 = ≤-trans acc'sz'
            (*-monoʳ-≤ (sizeᵗ fn) (^-monoˡ-≤ (3 ^ caseWᵗ fn) (grow-pow3 W E)))

  -- *-monoˡ using hfn (sizeᵗ fn ≤ C^E)
  step2 : sizeᵛ u acc' ≤ capᴱ W E * capᴱ W (E + 3) ^ 3 ^ caseWᵗ fn
  step2 = ≤-trans step1 (*-monoˡ-≤ (capᴱ W (E + 3) ^ 3 ^ caseWᵗ fn) hfn)

  -- collapse: C^E * (C^(E+3))^(3^cw) = C^(E + (E+3)*3^cw)
  collapse : capᴱ W E * capᴱ W (E + 3) ^ 3 ^ caseWᵗ fn
           ≡ capᴱ W (E + (E + 3) * 3 ^ caseWᵗ fn)
  collapse =
    trans (cong (capᴱ W E *_) (^-*-assoc C (E + 3) (3 ^ caseWᵗ fn)))
          (sym (^-distribˡ-+-* C E ((E + 3) * 3 ^ caseWᵗ fn)))

  -- pair-ledger-step: E + (E+3)*3^cw ≤ E*3^suc cw = E₁
  acc'B : sizeᵛ u acc' ≤ capᴱ W E₁
  acc'B =
    ≤-trans step2
    (≤-trans (≤-reflexive collapse)
             (capᴱ-mono W (pair-ledger-step E (caseWᵗ fn) 3≤E)))

  -- widen fn and value bounds to E₁
  hfn₁ : sizeᵗ fn ≤ capᴱ W E₁
  hfn₁ = ≤-trans hfn cap₁
  hvs₁ : All (λ v₀ → sizeᵛ s v₀ ≤ capᴱ W E₁) vs
  hvs₁ = mapᴬ (λ h → ≤-trans h cap₁) hvs

  -- IH at position E₁
  IH     = scanVals-sharp W E₁ fn acc' vs 3≤E₁ hfn₁ acc'B hvs₁
  IH-last = proj₁ IH
  IH-outs = proj₂ IH

  -- E₁ * 3^(cw*m) = E * 3^(cw * suc m)
  expEq : E₁ * 3 ^ (cw * m) ≡ E * 3 ^ (cw * suc m)
  expEq =
    trans (*-assoc E (3 ^ cw) (3 ^ (cw * m)))
    (cong (E *_)
      (trans (sym (^-distribˡ-+-* 3 cw (cw * m)))
             (cong (3 ^_) (sym (*-suc cw m)))))

  -- transport IH results to exponent cw * suc m
  cap-eq = ≤-reflexive (cong (capᴱ W) expEq)
  last-ok : sizeᵛ u (proj₂ (scanVals fn acc' vs)) ≤ capᴱ W (E * 3 ^ (cw * suc m))
  last-ok = ≤-trans IH-last cap-eq
  outs-ok : All (λ o → sizeᵛ u o ≤ capᴱ W (E * 3 ^ (cw * suc m))) (proj₁ (scanVals fn acc' vs))
  outs-ok = mapᴬ (λ h → ≤-trans h cap-eq) IH-outs

  -- acc' itself bounded at E * 3^(cw * suc m)
  acc'B₁ : sizeᵛ u acc' ≤ capᴱ W (E * 3 ^ (cw * suc m))
  acc'B₁ = ≤-trans acc'B (≤-trans (capᴱ-mono W (E≤E*3^ E₁ (cw * m))) cap-eq)

------------------------------------------------------------------
-- the machine-side faces of the walk invariant
------------------------------------------------------------------

fnCapLive : ∀ {n} {Γ : Ctx n} → ℕ → LiveSource Γ → Bool
fnCapLive Ψ l =
  all (λ tv → fnCapᵛ (LiveSource.elemTy l) (proj₂ tv) ≤ᵇ Ψ)
      (LiveSource.pending l)

fnCapNode : ∀ {n} {Γ : Ctx n} → ℕ → NodeState Γ → Bool
fnCapNode Ψ (scan-st {t} v)   = fnCapᵛ t v ≤ᵇ Ψ
fnCapNode Ψ (concat-st q _ _) = all (λ o → fnCapᵉ o ≤ᵇ Ψ) q
fnCapNode Ψ (take-st _)       = true
fnCapNode Ψ (merge-st _ _)    = true
fnCapNode Ψ (switch-st _ _)   = true
fnCapNode Ψ (exhaust-st _ _)  = true

fnCapBounded? : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
              → ℕ → Sched Γ → EvalSt e → Bool
fnCapBounded? Ψ sched st =
  all (fnCapLive Ψ) (Sched.live sched)
  ∧ all (λ kv → fnCapNode Ψ (proj₂ kv)) (EvalSt.nodes st)

-- registered chains carry RUNTIME fns (chains registered while
-- subscribing stored values): their sizes ride the store bound,
-- their weights ride Ψ
frameB? : ∀ {n} {Γ : Ctx n} {s u} → ℕ → ℕ → Frame Γ s u → Bool
frameB? B Ψ (map-f fn)         =
  (sizeᵗ fn ≤ᵇ B) ∧ ((caseWᵗ fn ⊔ fnCapᵗ fn) ≤ᵇ Ψ)
frameB? B Ψ (scan-f fn _)      =
  (sizeᵗ fn ≤ᵇ B) ∧ ((caseWᵗ fn ⊔ fnCapᵗ fn) ≤ᵇ Ψ)
frameB? B Ψ (take-f _)         = true
frameB? B Ψ (from-inner _ _ _) = true
frameB? B Ψ (thru-outer _ _)   = true

pathB? : ∀ {n} {Γ : Ctx n} {s t} → ℕ → ℕ → Path Γ s t → Bool
pathB? B Ψ root           = true
pathB? B Ψ (share-sink i) = true
pathB? B Ψ (f ↠ p)        = frameB? B Ψ f ∧ pathB? B Ψ p

regsB? : ∀ {n} {Γ : Ctx n} {t} → ℕ → ℕ
       → List (RegId × Source × Chain Γ t) → Bool
regsB? B Ψ = all (λ en → pathB? B Ψ (proj₂ (proj₂ (proj₂ en))))

-- the Ψ seed: the program's own weight plus every slot's (script
-- values are delivered and folded like any others; shared defs are
-- subscribed at connect) — a sum, which dominates the max
inputFnCap : ∀ {n} {Γ : Ctx n} {t : Ty} → ObservableInput (Val Γ t) → ℕ
inputFnCap {t = t} (hot async) =
  sum (map (λ tv → fnCapᵛ t (Timed.val tv)) async)
inputFnCap {t = t} (cold sync async) =
  sum (map (fnCapᵛ t) sync)
  + sum (map (λ tv → fnCapᵛ t (Timed.val tv)) async)

slotFnCap : ∀ {n} {Γ : Ctx n} {t} → Slot Γ t → ℕ
slotFnCap (scripted i) = inputFnCap i
slotFnCap (shared d)   = fnCapᵉ d

slotsFnCap : ∀ {n} {Γ : Ctx n} → Slots Γ → ℕ
slotsFnCap sl = sum (tabulate λ i → slotFnCap (sl i))

ΨAt : ∀ {n} {Γ : Ctx n} {t} → Closed Γ t → Slots Γ → ℕ
ΨAt e sl = fnCapᵉ e + slotsFnCap sl

-- THE COMPOSITE WALK INVARIANT: value stores bounded (stBounded?),
-- every embedded fn's weight capped (Ψ never grows — caseW is
-- substitution-invariant), the registry CARDINALITY within the
-- store bound (the fold-threading budget: |chains| ≤ B at latch),
-- every registered chain's frames bounded, and the SLOTS bounded
-- (script values and shared defs are subscribed/delivered mid-walk;
-- slots never change, so these two conjuncts ride along and only
-- ever widen)
INV? : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
     → ℕ → ℕ → Sched Γ → EvalSt e → Bool
INV? Ψ B sched st =
  stBounded? B sched st
  ∧ fnCapBounded? Ψ sched st
  ∧ (length (EvalSt.registry st) ≤ᵇ B)
  ∧ regsB? B Ψ (EvalSt.registry st)
  ∧ (slotsSize (Sched.slots sched) ≤ᵇ B)
  ∧ (slotsFnCap (Sched.slots sched) ≤ᵇ Ψ)

-- in-flight bounds: the values a frame is fed, the events a burst
-- carries
valB? : ∀ {n} {Γ : Ctx n} → ℕ → ℕ → (u : Ty) → Val Γ u → Bool
valB? B Ψ u v = (sizeᵛ u v ≤ᵇ B) ∧ (fnCapᵛ u v ≤ᵇ Ψ)

eventB? : ∀ {n} {Γ : Ctx n} {u} → ℕ → ℕ → InstEvent (Val Γ u) → Bool
eventB? {u = u} B Ψ (value v)   = valB? B Ψ u v
eventB? B Ψ (init _)    = true
eventB? B Ψ (close _ _) = true
eventB? B Ψ (handoff _) = true
eventB? B Ψ complete    = true

burstB? : ∀ {n} {Γ : Ctx n} {u} → ℕ → ℕ → Stream Γ u → Bool
burstB? B Ψ = all (λ em → all (eventB? B Ψ) (InstEmit.events em))

-- THE EMITTED-VALUE INVARIANT, in the same shape: every value a burst
-- carries has hop depth at most `r`, the depth of the expression that
-- was subscribed.  Stated here so subscribeE-walk can carry it as a
-- conjunct, which is what makes the *All clause's hop edge STRICT with
-- no arithmetic at all: hopDᵉ (mergeAllᵉ c) is DEFINITIONALLY suc
-- (hopDᵉ c), so an inner drawn from a carrier's burst has hopD ≤
-- hopDᵉ c < hopDᵉ (mergeAllᵉ c), and dBound-hop's r′ < r is discharged
-- by the definition rather than by a lemma.
--
-- This conjunct was postulated on 2026-07-28, REFUTED the same day
-- against the index-blind coefficient, retracted, and restated here
-- once occs0 had been re-gated — see the hop-descent memo below for the
-- mechanism and the corpus numbers both ways.
hopDev? : ∀ {n} {Γ : Ctx n} {u} → ℕ → ℕ → InstEvent (Val Γ u) → Bool
hopDev? {u = u} V r (value v)   = hopDᵛ V u v ≤ᵇ r
hopDev? V r (init _)    = true
hopDev? V r (close _ _) = true
hopDev? V r (handoff _) = true
hopDev? V r complete    = true

burstHopD? : ∀ {n} {Γ : Ctx n} {u} → ℕ → ℕ → Stream Γ u → Bool
burstHopD? V r = all (λ em → all (hopDev? V r) (InstEmit.events em))

------------------------------------------------------------------
-- PROJECTING THE INVARIANT.  _∧_ matches on its FIRST argument, so
-- `∧-true _ _ inv` leaves a metavariable in stuck position and the
-- solver cannot close it — every peel has to name the Bool it is
-- splitting off.  Done once here, so no consumer has to spell out
-- the six-way chain (or get it wrong).
------------------------------------------------------------------

INV-parts : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ψ B : ℕ)
  (sched : Sched Γ) (st : EvalSt e) → INV? Ψ B sched st ≡ true →
  (stBounded? B sched st ≡ true)
  × (fnCapBounded? Ψ sched st ≡ true)
  × ((length (EvalSt.registry st) ≤ᵇ B) ≡ true)
  × (regsB? B Ψ (EvalSt.registry st) ≡ true)
  × ((slotsSize (Sched.slots sched) ≤ᵇ B) ≡ true)
  × ((slotsFnCap (Sched.slots sched) ≤ᵇ Ψ) ≡ true)
INV-parts Ψ B sched st inv
  with ∧-true (stBounded? B sched st) _ inv
... | sb , r1 with ∧-true (fnCapBounded? Ψ sched st) _ r1
... | fc , r2 with ∧-true (length (EvalSt.registry st) ≤ᵇ B) _ r2
... | rl , r3 with ∧-true (regsB? B Ψ (EvalSt.registry st)) _ r3
... | rb , r4 with ∧-true (slotsSize (Sched.slots sched) ≤ᵇ B) _ r4
... | ss , sf = sb , fc , rl , rb , ss , sf

-- the two halves of each store predicate
stB-live : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (B : ℕ)
  (sched : Sched Γ) (st : EvalSt e) → stBounded? B sched st ≡ true →
  all (boundedLive B) (Sched.live sched) ≡ true
stB-live B sched st h =
  proj₁ (∧-true (all (boundedLive B) (Sched.live sched)) _ h)

fcB-live : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ψ : ℕ)
  (sched : Sched Γ) (st : EvalSt e) → fnCapBounded? Ψ sched st ≡ true →
  all (fnCapLive Ψ) (Sched.live sched) ≡ true
fcB-live Ψ sched st h =
  proj₁ (∧-true (all (fnCapLive Ψ) (Sched.live sched)) _ h)

stB-nodes : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (B : ℕ)
  (sched : Sched Γ) (st : EvalSt e) → stBounded? B sched st ≡ true →
  all (λ kv → boundedNode B (proj₂ kv)) (EvalSt.nodes st) ≡ true
stB-nodes B sched st h =
  proj₂ (∧-true (all (boundedLive B) (Sched.live sched)) _ h)

fcB-nodes : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ψ : ℕ)
  (sched : Sched Γ) (st : EvalSt e) → fnCapBounded? Ψ sched st ≡ true →
  all (λ kv → fnCapNode Ψ (proj₂ kv)) (EvalSt.nodes st) ≡ true
fcB-nodes Ψ sched st h =
  proj₂ (∧-true (all (fnCapLive Ψ) (Sched.live sched)) _ h)

-- and the in-flight ones, same reason
valB-sz : ∀ {n} {Γ : Ctx n} (B Ψ : ℕ) (u : Ty) (v : Val Γ u) →
  valB? B Ψ u v ≡ true → sizeᵛ u v ≤ B
valB-sz B Ψ u v h = ≤ᵇ⇒≤ _ _ (T-to (proj₁ (∧-true (sizeᵛ u v ≤ᵇ B) _ h)))

valB-fc : ∀ {n} {Γ : Ctx n} (B Ψ : ℕ) (u : Ty) (v : Val Γ u) →
  valB? B Ψ u v ≡ true → fnCapᵛ u v ≤ Ψ
valB-fc B Ψ u v h = ≤ᵇ⇒≤ _ _ (T-to (proj₂ (∧-true (sizeᵛ u v ≤ᵇ B) _ h)))

allB-head : ∀ {n} {Γ : Ctx n} (B Ψ : ℕ) (u : Ty) (v : Val Γ u)
  (vs : List (Val Γ u)) →
  all (valB? B Ψ u) (v ∷ vs) ≡ true → valB? B Ψ u v ≡ true
allB-head B Ψ u v vs h = proj₁ (∧-true (valB? B Ψ u v) _ h)

allB-tail : ∀ {n} {Γ : Ctx n} (B Ψ : ℕ) (u : Ty) (v : Val Γ u)
  (vs : List (Val Γ u)) →
  all (valB? B Ψ u) (v ∷ vs) ≡ true → all (valB? B Ψ u) vs ≡ true
allB-tail B Ψ u v vs h = proj₂ (∧-true (valB? B Ψ u v) _ h)

-- (W7) all the in-flight predicates only ever need widening
-- upward (≤ᵇ-widen through all, mirror boundedLive-widen)
valB?-widen : ∀ {n} {Γ : Ctx n} {B B′ Ψ : ℕ} (u : Ty) (v : Val Γ u) →
  B ≤ B′ → valB? B Ψ u v ≡ true → valB? B′ Ψ u v ≡ true
valB?-widen u v B≤ h =
  ∧-intro (≤ᵇ-widen (sizeᵛ u v) B≤ (proj₁ (∧-true _ _ h)))
          (proj₂ (∧-true _ _ h))

valsB?-widen : ∀ {n} {Γ : Ctx n} {B B′ Ψ : ℕ} (u : Ty)
  (vs : List (Val Γ u)) → B ≤ B′ →
  all (valB? B Ψ u) vs ≡ true → all (valB? B′ Ψ u) vs ≡ true
valsB?-widen u vs B≤ h = all-impl _ _ (λ v → valB?-widen u v B≤) vs h

-- per-event widening (only `value` carries a B-sized payload)
eventB?-widen : ∀ {n} {Γ : Ctx n} {u} {B B′ Ψ : ℕ} (ev : InstEvent (Val Γ u)) →
  B ≤ B′ → eventB? B Ψ ev ≡ true → eventB? B′ Ψ ev ≡ true
eventB?-widen (value v)  B≤ h = valB?-widen _ v B≤ h
eventB?-widen (init _)   B≤ h = refl
eventB?-widen (close _ _) B≤ h = refl
eventB?-widen (handoff _) B≤ h = refl
eventB?-widen complete   B≤ h = refl

burstB?-widen : ∀ {n} {Γ : Ctx n} {u} {B B′ Ψ : ℕ} (str : Stream Γ u) →
  B ≤ B′ → burstB? B Ψ str ≡ true → burstB? B′ Ψ str ≡ true
burstB?-widen str B≤ h =
  all-impl _ _ (λ em → all-impl _ _ (λ ev → eventB?-widen ev B≤)
                                (InstEmit.events em)) str h

frameB?-widen : ∀ {n} {Γ : Ctx n} {s u} {B B′ Ψ : ℕ} (f : Frame Γ s u) →
  B ≤ B′ → frameB? B Ψ f ≡ true → frameB? B′ Ψ f ≡ true
frameB?-widen (map-f fn)         B≤ h =
  ∧-intro (≤ᵇ-widen (sizeᵗ fn) B≤ (proj₁ (∧-true _ _ h))) (proj₂ (∧-true _ _ h))
frameB?-widen (scan-f fn _)      B≤ h =
  ∧-intro (≤ᵇ-widen (sizeᵗ fn) B≤ (proj₁ (∧-true _ _ h))) (proj₂ (∧-true _ _ h))
frameB?-widen (take-f _)         B≤ h = refl
frameB?-widen (from-inner _ _ _) B≤ h = refl
frameB?-widen (thru-outer _ _)   B≤ h = refl

pathB?-widen : ∀ {n} {Γ : Ctx n} {s t} {B B′ Ψ : ℕ} (p : Path Γ s t) →
  B ≤ B′ → pathB? B Ψ p ≡ true → pathB? B′ Ψ p ≡ true
pathB?-widen root           B≤ h = refl
pathB?-widen (share-sink i) B≤ h = refl
pathB?-widen (f ↠ p)        B≤ h =
  ∧-intro (frameB?-widen f B≤ (proj₁ (∧-true _ _ h)))
          (pathB?-widen p B≤ (proj₂ (∧-true _ _ h)))

chainsB?-widen : ∀ {n} {Γ : Ctx n} {t} {B B′ Ψ : ℕ} {s : Ty}
  (chains : List (RegId × Path Γ s t)) → B ≤ B′ →
  all (λ rc → pathB? B Ψ (proj₂ rc)) chains ≡ true →
  all (λ rc → pathB? B′ Ψ (proj₂ rc)) chains ≡ true
chainsB?-widen chains B≤ h =
  all-impl _ _ (λ rc → pathB?-widen (proj₂ rc) B≤) chains h

allPathB-widen : ∀ {n} {Γ : Ctx n} {s t} {B B′ Ψ : ℕ}
  (ps : List (RegId × Path Γ s t)) → B ≤ B′ →
  all (λ rp → pathB? B Ψ (proj₂ rp)) ps ≡ true →
  all (λ rp → pathB? B′ Ψ (proj₂ rp)) ps ≡ true
allPathB-widen ps B≤ h = all-impl _ _ (λ rp → pathB?-widen (proj₂ rp) B≤) ps h

regsB?-widen : ∀ {n} {Γ : Ctx n} {t} {B B′ Ψ : ℕ}
  (reg : List (RegId × Source × Chain Γ t)) → B ≤ B′ →
  regsB? B Ψ reg ≡ true → regsB? B′ Ψ reg ≡ true
regsB?-widen reg B≤ h =
  all-impl _ _ (λ en → pathB?-widen (proj₂ (proj₂ (proj₂ en))) B≤) reg h

-- (W8) burst plumbing: splitting a bounded emit yields bounded
-- values; the bookkeeping side and retag images are value-free,
-- so any bound covers them; wrapping bounded values back into
-- events is pointwise (all list inductions)
splitEvents-vals-B : ∀ {n} {Γ : Ctx n} {s u : Ty} (B Ψ : ℕ)
  (es : List (InstEvent (Val Γ s))) →
  all (eventB? B Ψ) es ≡ true →
  all (valB? B Ψ s) (proj₁ (splitEvents {A = Val Γ u} es)) ≡ true
splitEvents-vals-B B Ψ []              h = refl
splitEvents-vals-B B Ψ (value v  ∷ es) h =
  ∧-intro (proj₁ (∧-true _ _ h)) (splitEvents-vals-B B Ψ es (proj₂ (∧-true _ _ h)))
splitEvents-vals-B B Ψ (init _   ∷ es) h = splitEvents-vals-B B Ψ es (proj₂ (∧-true _ _ h))
splitEvents-vals-B B Ψ (close _ _ ∷ es) h = splitEvents-vals-B B Ψ es (proj₂ (∧-true _ _ h))
splitEvents-vals-B B Ψ (handoff _ ∷ es) h = splitEvents-vals-B B Ψ es (proj₂ (∧-true _ _ h))
splitEvents-vals-B B Ψ (complete ∷ es) h = splitEvents-vals-B B Ψ es (proj₂ (∧-true _ _ h))

splitEvents-bk-B : ∀ {n} {Γ : Ctx n} {s u : Ty} (B Ψ : ℕ)
  (es : List (InstEvent (Val Γ s))) →
  all (eventB? B Ψ) (proj₁ (proj₂ (splitEvents {A = Val Γ u} es))) ≡ true
splitEvents-bk-B B Ψ []              = refl
splitEvents-bk-B {u = u} B Ψ (value v  ∷ es) = splitEvents-bk-B {u = u} B Ψ es
splitEvents-bk-B {u = u} B Ψ (init _   ∷ es) = ∧-intro refl (splitEvents-bk-B {u = u} B Ψ es)
splitEvents-bk-B {u = u} B Ψ (close _ _ ∷ es) = ∧-intro refl (splitEvents-bk-B {u = u} B Ψ es)
splitEvents-bk-B {u = u} B Ψ (handoff _ ∷ es) = ∧-intro refl (splitEvents-bk-B {u = u} B Ψ es)
splitEvents-bk-B {u = u} B Ψ (complete ∷ es) = splitEvents-bk-B {u = u} B Ψ es

retag-B : ∀ {n} {Γ : Ctx n} {u : Ty} {A : Set} (B Ψ : ℕ)
  (es : List (InstEvent A)) →
  all (eventB? B Ψ) (retagEvents {B = Val Γ u} es) ≡ true
retag-B B Ψ []              = refl
retag-B B Ψ (init _   ∷ es) = ∧-intro refl (retag-B B Ψ es)
retag-B B Ψ (close _ _ ∷ es) = ∧-intro refl (retag-B B Ψ es)
retag-B B Ψ (handoff _ ∷ es) = ∧-intro refl (retag-B B Ψ es)
retag-B B Ψ (complete ∷ es) = ∧-intro refl (retag-B B Ψ es)
retag-B B Ψ (value _  ∷ es) = retag-B B Ψ es

mapValue-B : ∀ {n} {Γ : Ctx n} (B Ψ : ℕ) (u : Ty) (vs : List (Val Γ u)) →
  all (valB? B Ψ u) vs ≡ true →
  all (eventB? B Ψ) (map value vs) ≡ true
mapValue-B B Ψ u []       h = refl
mapValue-B B Ψ u (v ∷ vs) h =
  ∧-intro (proj₁ (∧-true _ _ h)) (mapValue-B B Ψ u vs (proj₂ (∧-true _ _ h)))

------------------------------------------------------------------
-- THE WIDTH LEDGER (memo (5)): the width cap Ω — the largest
-- of-list LENGTH reachable from here.  Widths are syntax
-- (substitution plugs single elements), so unlike the size ledger
-- Ω needs NO running position: the machine can never mint a width
-- above the entry seed.  Mirrors fnCap clause for clause; the ONE
-- non-mirror clause is ofᵉ, the only width mint, contributing its
-- literal list length.
------------------------------------------------------------------

mutual
  ofWᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Tm Γ Δᵍ Δ Θ t → ℕ
  ofWᵗ (varᵗ x)      = 0
  ofWᵗ unit̂          = 0
  ofWᵗ (bool̂ _)      = 0
  ofWᵗ (nat̂ _)       = 0
  ofWᵗ (pairᵗ a b)   = ofWᵗ a ⊔ ofWᵗ b
  ofWᵗ (fstᵗ p)      = ofWᵗ p
  ofWᵗ (sndᵗ p)      = ofWᵗ p
  ofWᵗ (inlᵗ a)      = ofWᵗ a
  ofWᵗ (inrᵗ a)      = ofWᵗ a
  ofWᵗ (caseᵗ s l r) = ofWᵗ s ⊔ (ofWᵗ l ⊔ ofWᵗ r)
  ofWᵗ (ifᵗ c a b)   = ofWᵗ c ⊔ (ofWᵗ a ⊔ ofWᵗ b)
  ofWᵗ (primᵗ _ a)   = ofWᵗ a
  ofWᵗ (strmᵗ e)     = ofWᵉ e

  ofWᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Exp Γ Δᵍ Δ Θ t → ℕ
  ofWᵉ (input i)       = 0
  ofWᵉ (ofᵉ ts)        = length ts ⊔ ofWᵗˢ ts
  ofWᵉ emptyᵉ          = 0
  ofWᵉ (mapᵉ f e)      = ofWᵗ f ⊔ ofWᵉ e
  ofWᵉ (takeᵉ c e)     = ofWᵗ c ⊔ ofWᵉ e
  ofWᵉ (scanᵉ f z e)   = ofWᵗ f ⊔ (ofWᵗ z ⊔ ofWᵉ e)
  ofWᵉ (mergeAllᵉ e)   = ofWᵉ e
  ofWᵉ (concatAllᵉ e)  = ofWᵉ e
  ofWᵉ (switchAllᵉ e)  = ofWᵉ e
  ofWᵉ (exhaustAllᵉ e) = ofWᵉ e
  ofWᵉ (μᵉ e)          = ofWᵉ e
  ofWᵉ (varᵉ x)        = 0
  ofWᵉ (deferᵉ e)      = ofWᵉ e

  ofWᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → List (Tm Γ Δᵍ Δ Θ t) → ℕ
  ofWᵗˢ []       = 0
  ofWᵗˢ (y ∷ ys) = ofWᵗ y ⊔ ofWᵗˢ ys

ofWᵛ : ∀ {n} {Γ : Ctx n} (t : Ty) → Val Γ t → ℕ
ofWᵛ unitᵗ    v        = 0
ofWᵛ boolᵗ    v        = 0
ofWᵛ natᵗ     v        = 0
ofWᵛ (s ×ᵗ t) (a , b)  = ofWᵛ s a ⊔ ofWᵛ t b
ofWᵛ (s +ᵗ t) (inj₁ a) = ofWᵛ s a
ofWᵛ (s +ᵗ t) (inj₂ b) = ofWᵛ t b
ofWᵛ (obs t)  e        = ofWᵉ e

-- the width face of an environment, shaped like EnvFnCap
EnvOfW : ∀ {n} {Γ : Ctx n} {Θ} (Ω : ℕ) → All (Val Γ) Θ → Set
EnvOfW Ω []ᵃ                = ⊤
EnvOfW Ω (_∷ᵃ_ {x = t} v σ) = (ofWᵛ t v ≤ Ω) × EnvOfW Ω σ

envofw-lookup : ∀ {n} {Γ : Ctx n} {Θ t} (Ω : ℕ) (σ : All (Val Γ) Θ) →
  EnvOfW Ω σ → (z : t ∈ Θ) → ofWᵛ t (lookupEnv σ z) ≤ Ω
envofw-lookup Ω (v ∷ᵃ σ) (h , hσ) (here refl) = h
envofw-lookup Ω (v ∷ᵃ σ) (h , hσ) (there z)   = envofw-lookup Ω σ hσ z

------------------------------------------------------------------
-- (W10) width invariance: the ofW mirrors of W1/W2/W4.  Same
-- inductions and the same ⊔ algebra as fnCap; the only differing
-- clause is ofᵉ, whose `length` conjunct rides the fact that ren /
-- subΘ / elimG / elimD all MAP over the of-list (len-* below).
------------------------------------------------------------------

len-renTms : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t}
  (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′)
  (ts : List (Tm Γ Δᵍ Δ Θ t)) → length (renTms ρg ρd ρt ts) ≡ length ts
len-renTms ρg ρd ρt []       = refl
len-renTms ρg ρd ρt (y ∷ ys) = cong suc (len-renTms ρg ρd ρt ys)

len-subΘTms : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (Θloc : List Ty)
  (σ : All (Val Γ) Θsub) (ts : List (Tm Γ Δᵍ Δ (Θloc ++ Θsub) t)) →
  length (subΘTms Θloc σ ts) ≡ length ts
len-subΘTms Θloc σ []       = refl
len-subΘTms Θloc σ (y ∷ ys) = cong suc (len-subΘTms Θloc σ ys)

len-elimGTms : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
  (cl : Closed Γ t) (ts : List (Tm Γ Δᵍ Δ Θ u)) →
  length (elimGTms x cl ts) ≡ length ts
len-elimGTms x cl []       = refl
len-elimGTms x cl (y ∷ ys) = cong suc (len-elimGTms x cl ys)

len-elimDTms : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δ)
  (cl : Closed Γ t) (ts : List (Tm Γ Δᵍ Δ Θ u)) →
  length (elimDTms x cl ts) ≡ length ts
len-elimDTms x cl []       = refl
len-elimDTms x cl (y ∷ ys) = cong suc (len-elimDTms x cl ys)

-- ofW is renaming-invariant (mirror of fnCap-renᵉ/ᵗ/ᵗˢ)
mutual
  ofW-renᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t}
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′)
    (e : Exp Γ Δᵍ Δ Θ t) → ofWᵉ (renExp ρg ρd ρt e) ≡ ofWᵉ e
  ofW-renᵉ ρg ρd ρt (input i)       = refl
  ofW-renᵉ ρg ρd ρt (ofᵉ ts)        =
    cong₂ _⊔_ (len-renTms ρg ρd ρt ts) (ofW-renᵗˢ ρg ρd ρt ts)
  ofW-renᵉ ρg ρd ρt emptyᵉ          = refl
  ofW-renᵉ ρg ρd ρt (mapᵉ f e)      =
    cong₂ _⊔_ (ofW-renᵗ ρg ρd (ext∈ ρt) f) (ofW-renᵉ ρg ρd ρt e)
  ofW-renᵉ ρg ρd ρt (takeᵉ c e)     =
    cong₂ _⊔_ (ofW-renᵗ ρg ρd ρt c) (ofW-renᵉ ρg ρd ρt e)
  ofW-renᵉ ρg ρd ρt (scanᵉ f z e)   =
    cong₂ _⊔_ (ofW-renᵗ ρg ρd (ext∈ ρt) f)
              (cong₂ _⊔_ (ofW-renᵗ ρg ρd ρt z) (ofW-renᵉ ρg ρd ρt e))
  ofW-renᵉ ρg ρd ρt (mergeAllᵉ e)   = ofW-renᵉ ρg ρd ρt e
  ofW-renᵉ ρg ρd ρt (concatAllᵉ e)  = ofW-renᵉ ρg ρd ρt e
  ofW-renᵉ ρg ρd ρt (switchAllᵉ e)  = ofW-renᵉ ρg ρd ρt e
  ofW-renᵉ ρg ρd ρt (exhaustAllᵉ e) = ofW-renᵉ ρg ρd ρt e
  ofW-renᵉ ρg ρd ρt (μᵉ e)          = ofW-renᵉ (ext∈ ρg) ρd ρt e
  ofW-renᵉ ρg ρd ρt (varᵉ x)        = refl
  ofW-renᵉ ρg ρd ρt (deferᵉ e)      = ofW-renᵉ (λ ()) (++Ren ρg ρd) ρt e

  ofW-renᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t}
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′)
    (tm : Tm Γ Δᵍ Δ Θ t) → ofWᵗ (renTm ρg ρd ρt tm) ≡ ofWᵗ tm
  ofW-renᵗ ρg ρd ρt (varᵗ x)      = refl
  ofW-renᵗ ρg ρd ρt unit̂          = refl
  ofW-renᵗ ρg ρd ρt (bool̂ _)      = refl
  ofW-renᵗ ρg ρd ρt (nat̂ _)       = refl
  ofW-renᵗ ρg ρd ρt (pairᵗ a b)   =
    cong₂ _⊔_ (ofW-renᵗ ρg ρd ρt a) (ofW-renᵗ ρg ρd ρt b)
  ofW-renᵗ ρg ρd ρt (fstᵗ p)      = ofW-renᵗ ρg ρd ρt p
  ofW-renᵗ ρg ρd ρt (sndᵗ p)      = ofW-renᵗ ρg ρd ρt p
  ofW-renᵗ ρg ρd ρt (inlᵗ a)      = ofW-renᵗ ρg ρd ρt a
  ofW-renᵗ ρg ρd ρt (inrᵗ a)      = ofW-renᵗ ρg ρd ρt a
  ofW-renᵗ ρg ρd ρt (caseᵗ s l r) =
    cong₂ _⊔_ (ofW-renᵗ ρg ρd ρt s)
              (cong₂ _⊔_ (ofW-renᵗ ρg ρd (ext∈ ρt) l)
                         (ofW-renᵗ ρg ρd (ext∈ ρt) r))
  ofW-renᵗ ρg ρd ρt (ifᵗ c a b)   =
    cong₂ _⊔_ (ofW-renᵗ ρg ρd ρt c)
              (cong₂ _⊔_ (ofW-renᵗ ρg ρd ρt a) (ofW-renᵗ ρg ρd ρt b))
  ofW-renᵗ ρg ρd ρt (primᵗ _ a)   = ofW-renᵗ ρg ρd ρt a
  ofW-renᵗ ρg ρd ρt (strmᵗ e)     = ofW-renᵉ ρg ρd ρt e

  ofW-renᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t}
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′)
    (ts : List (Tm Γ Δᵍ Δ Θ t)) → ofWᵗˢ (renTms ρg ρd ρt ts) ≡ ofWᵗˢ ts
  ofW-renᵗˢ ρg ρd ρt []       = refl
  ofW-renᵗˢ ρg ρd ρt (y ∷ ys) =
    cong₂ _⊔_ (ofW-renᵗ ρg ρd ρt y) (ofW-renᵗˢ ρg ρd ρt ys)

ofW-reify : ∀ {n} {Γ : Ctx n} (t : Ty) (v : Val Γ t) →
  ofWᵗ (reify v) ≡ ofWᵛ t v
ofW-reify unitᵗ    _        = refl
ofW-reify boolᵗ    _        = refl
ofW-reify natᵗ     _        = refl
ofW-reify (s ×ᵗ t) (a , b)  = cong₂ _⊔_ (ofW-reify s a) (ofW-reify t b)
ofW-reify (s +ᵗ t) (inj₁ a) = ofW-reify s a
ofW-reify (s +ᵗ t) (inj₂ b) = ofW-reify t b
ofW-reify (obs t)  e        = refl

-- substitution keeps every width ≤ Ω (mirror of fnCap-subΘᵉ/ᵗ/ᵗˢ)
mutual
  ofW-subΘᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (Ω : ℕ) (Θloc : List Ty)
    (σ : All (Val Γ) Θsub) (e : Exp Γ Δᵍ Δ (Θloc ++ Θsub) t) →
    EnvOfW Ω σ → ofWᵉ e ≤ Ω → ofWᵉ (subΘExp Θloc σ e) ≤ Ω
  ofW-subΘᵉ Ω Θloc σ (input i)       hσ h = z≤n
  ofW-subΘᵉ Ω Θloc σ (ofᵉ ts)        hσ h =
    ⊔-lub (subst (_≤ Ω) (sym (len-subΘTms Θloc σ ts))
                 (⊔ˡ (length ts) (ofWᵗˢ ts) h))
          (ofW-subΘᵗˢ Ω Θloc σ ts hσ (⊔ʳ (length ts) (ofWᵗˢ ts) h))
  ofW-subΘᵉ Ω Θloc σ emptyᵉ          hσ h = z≤n
  ofW-subΘᵉ Ω Θloc σ (mapᵉ {s = s} f e) hσ h =
    ⊔-lub (ofW-subΘᵗ Ω (s ∷ Θloc) σ f hσ (⊔ˡ (ofWᵗ f) (ofWᵉ e) h))
          (ofW-subΘᵉ Ω Θloc σ e hσ (⊔ʳ (ofWᵗ f) (ofWᵉ e) h))
  ofW-subΘᵉ Ω Θloc σ (takeᵉ c e)     hσ h =
    ⊔-lub (ofW-subΘᵗ Ω Θloc σ c hσ (⊔ˡ (ofWᵗ c) (ofWᵉ e) h))
          (ofW-subΘᵉ Ω Θloc σ e hσ (⊔ʳ (ofWᵗ c) (ofWᵉ e) h))
  ofW-subΘᵉ Ω Θloc σ (scanᵉ {s = s} {t = t} f z e) hσ h =
    ⊔-lub (ofW-subΘᵗ Ω ((t ×ᵗ s) ∷ Θloc) σ f hσ
             (⊔ˡ (ofWᵗ f) (ofWᵗ z ⊔ ofWᵉ e) h))
          (⊔-lub (ofW-subΘᵗ Ω Θloc σ z hσ
                    (⊔ˡ (ofWᵗ z) (ofWᵉ e) (⊔ʳ (ofWᵗ f) (ofWᵗ z ⊔ ofWᵉ e) h)))
                 (ofW-subΘᵉ Ω Θloc σ e hσ
                    (⊔ʳ (ofWᵗ z) (ofWᵉ e) (⊔ʳ (ofWᵗ f) (ofWᵗ z ⊔ ofWᵉ e) h))))
  ofW-subΘᵉ Ω Θloc σ (mergeAllᵉ e)   hσ h = ofW-subΘᵉ Ω Θloc σ e hσ h
  ofW-subΘᵉ Ω Θloc σ (concatAllᵉ e)  hσ h = ofW-subΘᵉ Ω Θloc σ e hσ h
  ofW-subΘᵉ Ω Θloc σ (switchAllᵉ e)  hσ h = ofW-subΘᵉ Ω Θloc σ e hσ h
  ofW-subΘᵉ Ω Θloc σ (exhaustAllᵉ e) hσ h = ofW-subΘᵉ Ω Θloc σ e hσ h
  ofW-subΘᵉ Ω Θloc σ (μᵉ e)          hσ h = ofW-subΘᵉ Ω Θloc σ e hσ h
  ofW-subΘᵉ Ω Θloc σ (varᵉ x)        hσ h = z≤n
  ofW-subΘᵉ Ω Θloc σ (deferᵉ e)      hσ h = ofW-subΘᵉ Ω Θloc σ e hσ h

  ofW-subΘᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (Ω : ℕ) (Θloc : List Ty)
    (σ : All (Val Γ) Θsub) (tm : Tm Γ Δᵍ Δ (Θloc ++ Θsub) t) →
    EnvOfW Ω σ → ofWᵗ tm ≤ Ω → ofWᵗ (subΘTm Θloc σ tm) ≤ Ω
  ofW-subΘᵗ Ω Θloc σ (varᵗ x) hσ h with ∈-++⁻ Θloc x
  ... | inj₁ y = z≤n
  ... | inj₂ z =
    subst (_≤ Ω)
      (sym (trans (ofW-renᵗ (λ ()) (λ ()) (λ ()) (reify (lookupEnv σ z)))
                  (ofW-reify _ (lookupEnv σ z))))
      (envofw-lookup Ω σ hσ z)
  ofW-subΘᵗ Ω Θloc σ unit̂         hσ h = z≤n
  ofW-subΘᵗ Ω Θloc σ (bool̂ _)     hσ h = z≤n
  ofW-subΘᵗ Ω Θloc σ (nat̂ _)      hσ h = z≤n
  ofW-subΘᵗ Ω Θloc σ (pairᵗ a b)  hσ h =
    ⊔-lub (ofW-subΘᵗ Ω Θloc σ a hσ (⊔ˡ (ofWᵗ a) (ofWᵗ b) h))
          (ofW-subΘᵗ Ω Θloc σ b hσ (⊔ʳ (ofWᵗ a) (ofWᵗ b) h))
  ofW-subΘᵗ Ω Θloc σ (fstᵗ p)     hσ h = ofW-subΘᵗ Ω Θloc σ p hσ h
  ofW-subΘᵗ Ω Θloc σ (sndᵗ p)     hσ h = ofW-subΘᵗ Ω Θloc σ p hσ h
  ofW-subΘᵗ Ω Θloc σ (inlᵗ a)     hσ h = ofW-subΘᵗ Ω Θloc σ a hσ h
  ofW-subΘᵗ Ω Θloc σ (inrᵗ a)     hσ h = ofW-subΘᵗ Ω Θloc σ a hσ h
  ofW-subΘᵗ Ω Θloc σ (caseᵗ {s = s} {t = t} sc l r) hσ h =
    ⊔-lub (ofW-subΘᵗ Ω Θloc σ sc hσ (⊔ˡ (ofWᵗ sc) (ofWᵗ l ⊔ ofWᵗ r) h))
          (⊔-lub (ofW-subΘᵗ Ω (s ∷ Θloc) σ l hσ
                    (⊔ˡ (ofWᵗ l) (ofWᵗ r) (⊔ʳ (ofWᵗ sc) (ofWᵗ l ⊔ ofWᵗ r) h)))
                 (ofW-subΘᵗ Ω (t ∷ Θloc) σ r hσ
                    (⊔ʳ (ofWᵗ l) (ofWᵗ r) (⊔ʳ (ofWᵗ sc) (ofWᵗ l ⊔ ofWᵗ r) h))))
  ofW-subΘᵗ Ω Θloc σ (ifᵗ c a b)  hσ h =
    ⊔-lub (ofW-subΘᵗ Ω Θloc σ c hσ (⊔ˡ (ofWᵗ c) (ofWᵗ a ⊔ ofWᵗ b) h))
          (⊔-lub (ofW-subΘᵗ Ω Θloc σ a hσ
                    (⊔ˡ (ofWᵗ a) (ofWᵗ b) (⊔ʳ (ofWᵗ c) (ofWᵗ a ⊔ ofWᵗ b) h)))
                 (ofW-subΘᵗ Ω Θloc σ b hσ
                    (⊔ʳ (ofWᵗ a) (ofWᵗ b) (⊔ʳ (ofWᵗ c) (ofWᵗ a ⊔ ofWᵗ b) h))))
  ofW-subΘᵗ Ω Θloc σ (primᵗ _ a)  hσ h = ofW-subΘᵗ Ω Θloc σ a hσ h
  ofW-subΘᵗ Ω Θloc σ (strmᵗ e)    hσ h = ofW-subΘᵉ Ω Θloc σ e hσ h

  ofW-subΘᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (Ω : ℕ) (Θloc : List Ty)
    (σ : All (Val Γ) Θsub) (ts : List (Tm Γ Δᵍ Δ (Θloc ++ Θsub) t)) →
    EnvOfW Ω σ → ofWᵗˢ ts ≤ Ω → ofWᵗˢ (subΘTms Θloc σ ts) ≤ Ω
  ofW-subΘᵗˢ Ω Θloc σ []       hσ h = z≤n
  ofW-subΘᵗˢ Ω Θloc σ (y ∷ ys) hσ h =
    ⊔-lub (ofW-subΘᵗ Ω Θloc σ y hσ (⊔ˡ (ofWᵗ y) (ofWᵗˢ ys) h))
          (ofW-subΘᵗˢ Ω Θloc σ ys hσ (⊔ʳ (ofWᵗ y) (ofWᵗˢ ys) h))

-- subst on the Δ-index of Exp is transparent to ofWᵉ (J on the equality)
ofW-substᴱ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Δ′ Θ t} (p : Δ ≡ Δ′) (e : Exp Γ Δᵍ Δ Θ t) →
  ofWᵉ (subst (λ ζ → Exp Γ Δᵍ ζ Θ t) p e) ≡ ofWᵉ e
ofW-substᴱ refl e = refl

-- elimG/D keep every width ≤ host ⊔ closure (mirror of fnCap-elimG/D)
mutual
  ofW-elimG : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
    (cl : Closed Γ t) (e : Exp Γ Δᵍ Δ Θ u) →
    ofWᵉ (elimGExp x cl e) ≤ ofWᵉ e ⊔ ofWᵉ cl
  ofW-elimG x cl (input i)       = z≤n
  ofW-elimG x cl (ofᵉ ts)        =
    ⊔-elim-help (length ts) (ofWᵗˢ ts) (ofWᵉ cl)
                (subst (_≤ length ts ⊔ ofWᵉ cl) (sym (len-elimGTms x cl ts))
                       (m≤m⊔n (length ts) (ofWᵉ cl)))
                (ofW-elimGᵗˢ x cl ts)
  ofW-elimG x cl emptyᵉ          = z≤n
  ofW-elimG x cl (mapᵉ f e)      =
    ⊔-elim-help (ofWᵗ f) (ofWᵉ e) (ofWᵉ cl)
                (ofW-elimGᵗ x cl f) (ofW-elimG x cl e)
  ofW-elimG x cl (takeᵉ c e)     =
    ⊔-elim-help (ofWᵗ c) (ofWᵉ e) (ofWᵉ cl)
                (ofW-elimGᵗ x cl c) (ofW-elimG x cl e)
  ofW-elimG x cl (scanᵉ f z e)   =
    ⊔-elim-help (ofWᵗ f) ((ofWᵗ z) ⊔ (ofWᵉ e)) (ofWᵉ cl)
                (ofW-elimGᵗ x cl f)
                (⊔-elim-help (ofWᵗ z) (ofWᵉ e) (ofWᵉ cl)
                             (ofW-elimGᵗ x cl z) (ofW-elimG x cl e))
  ofW-elimG x cl (mergeAllᵉ e)   = ofW-elimG x cl e
  ofW-elimG x cl (concatAllᵉ e)  = ofW-elimG x cl e
  ofW-elimG x cl (switchAllᵉ e)  = ofW-elimG x cl e
  ofW-elimG x cl (exhaustAllᵉ e) = ofW-elimG x cl e
  ofW-elimG x cl (μᵉ e)          = ofW-elimG (there x) cl e
  ofW-elimG x cl (varᵉ y)        = z≤n
  ofW-elimG x cl (deferᵉ e)      =
    ≤-trans (≤-reflexive (ofW-substᴱ (⊟-++ˡ x) (elimDExp (∈-++⁺ˡ x) cl e)))
            (ofW-elimD (∈-++⁺ˡ x) cl e)

  ofW-elimD : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δ)
    (cl : Closed Γ t) (e : Exp Γ Δᵍ Δ Θ u) →
    ofWᵉ (elimDExp x cl e) ≤ ofWᵉ e ⊔ ofWᵉ cl
  ofW-elimD x cl (input i)       = z≤n
  ofW-elimD x cl (ofᵉ ts)        =
    ⊔-elim-help (length ts) (ofWᵗˢ ts) (ofWᵉ cl)
                (subst (_≤ length ts ⊔ ofWᵉ cl) (sym (len-elimDTms x cl ts))
                       (m≤m⊔n (length ts) (ofWᵉ cl)))
                (ofW-elimDᵗˢ x cl ts)
  ofW-elimD x cl emptyᵉ          = z≤n
  ofW-elimD x cl (mapᵉ f e)      =
    ⊔-elim-help (ofWᵗ f) (ofWᵉ e) (ofWᵉ cl)
                (ofW-elimDᵗ x cl f) (ofW-elimD x cl e)
  ofW-elimD x cl (takeᵉ c e)     =
    ⊔-elim-help (ofWᵗ c) (ofWᵉ e) (ofWᵉ cl)
                (ofW-elimDᵗ x cl c) (ofW-elimD x cl e)
  ofW-elimD x cl (scanᵉ f z e)   =
    ⊔-elim-help (ofWᵗ f) ((ofWᵗ z) ⊔ (ofWᵉ e)) (ofWᵉ cl)
                (ofW-elimDᵗ x cl f)
                (⊔-elim-help (ofWᵗ z) (ofWᵉ e) (ofWᵉ cl)
                             (ofW-elimDᵗ x cl z) (ofW-elimD x cl e))
  ofW-elimD x cl (mergeAllᵉ e)   = ofW-elimD x cl e
  ofW-elimD x cl (concatAllᵉ e)  = ofW-elimD x cl e
  ofW-elimD x cl (switchAllᵉ e)  = ofW-elimD x cl e
  ofW-elimD x cl (exhaustAllᵉ e) = ofW-elimD x cl e
  ofW-elimD x cl (μᵉ e)          = ofW-elimD x cl e
  ofW-elimD x cl (varᵉ y)        with compare∈ x y
  ... | inj₁ refl = ≤-reflexive (ofW-renᵉ (λ ()) (λ ()) (λ ()) cl)
  ... | inj₂ y′   = z≤n
  ofW-elimD {Δᵍ = Δᵍ} x cl (deferᵉ e) =
    ≤-trans (≤-reflexive (ofW-substᴱ (⊟-++ʳ {Δᵍ = Δᵍ} x)
                                    (elimDExp (∈-++⁺ʳ Δᵍ x) cl e)))
            (ofW-elimD (∈-++⁺ʳ Δᵍ x) cl e)

  ofW-elimGᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
    (cl : Closed Γ t) (tm : Tm Γ Δᵍ Δ Θ u) →
    ofWᵗ (elimGTm x cl tm) ≤ ofWᵗ tm ⊔ ofWᵉ cl
  ofW-elimGᵗ x cl (varᵗ y)      = z≤n
  ofW-elimGᵗ x cl unit̂          = z≤n
  ofW-elimGᵗ x cl (bool̂ _)      = z≤n
  ofW-elimGᵗ x cl (nat̂ _)       = z≤n
  ofW-elimGᵗ x cl (pairᵗ a b)   =
    ⊔-elim-help (ofWᵗ a) (ofWᵗ b) (ofWᵉ cl)
                (ofW-elimGᵗ x cl a) (ofW-elimGᵗ x cl b)
  ofW-elimGᵗ x cl (fstᵗ p)      = ofW-elimGᵗ x cl p
  ofW-elimGᵗ x cl (sndᵗ p)      = ofW-elimGᵗ x cl p
  ofW-elimGᵗ x cl (inlᵗ a)      = ofW-elimGᵗ x cl a
  ofW-elimGᵗ x cl (inrᵗ a)      = ofW-elimGᵗ x cl a
  ofW-elimGᵗ x cl (caseᵗ s l r) =
    ⊔-elim-help (ofWᵗ s) ((ofWᵗ l) ⊔ (ofWᵗ r)) (ofWᵉ cl)
                (ofW-elimGᵗ x cl s)
                (⊔-elim-help (ofWᵗ l) (ofWᵗ r) (ofWᵉ cl)
                             (ofW-elimGᵗ x cl l) (ofW-elimGᵗ x cl r))
  ofW-elimGᵗ x cl (ifᵗ c a b)   =
    ⊔-elim-help (ofWᵗ c) ((ofWᵗ a) ⊔ (ofWᵗ b)) (ofWᵉ cl)
                (ofW-elimGᵗ x cl c)
                (⊔-elim-help (ofWᵗ a) (ofWᵗ b) (ofWᵉ cl)
                             (ofW-elimGᵗ x cl a) (ofW-elimGᵗ x cl b))
  ofW-elimGᵗ x cl (primᵗ _ a)   = ofW-elimGᵗ x cl a
  ofW-elimGᵗ x cl (strmᵗ e)     = ofW-elimG x cl e

  ofW-elimDᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δ)
    (cl : Closed Γ t) (tm : Tm Γ Δᵍ Δ Θ u) →
    ofWᵗ (elimDTm x cl tm) ≤ ofWᵗ tm ⊔ ofWᵉ cl
  ofW-elimDᵗ x cl (varᵗ y)      = z≤n
  ofW-elimDᵗ x cl unit̂          = z≤n
  ofW-elimDᵗ x cl (bool̂ _)      = z≤n
  ofW-elimDᵗ x cl (nat̂ _)       = z≤n
  ofW-elimDᵗ x cl (pairᵗ a b)   =
    ⊔-elim-help (ofWᵗ a) (ofWᵗ b) (ofWᵉ cl)
                (ofW-elimDᵗ x cl a) (ofW-elimDᵗ x cl b)
  ofW-elimDᵗ x cl (fstᵗ p)      = ofW-elimDᵗ x cl p
  ofW-elimDᵗ x cl (sndᵗ p)      = ofW-elimDᵗ x cl p
  ofW-elimDᵗ x cl (inlᵗ a)      = ofW-elimDᵗ x cl a
  ofW-elimDᵗ x cl (inrᵗ a)      = ofW-elimDᵗ x cl a
  ofW-elimDᵗ x cl (caseᵗ s l r) =
    ⊔-elim-help (ofWᵗ s) ((ofWᵗ l) ⊔ (ofWᵗ r)) (ofWᵉ cl)
                (ofW-elimDᵗ x cl s)
                (⊔-elim-help (ofWᵗ l) (ofWᵗ r) (ofWᵉ cl)
                             (ofW-elimDᵗ x cl l) (ofW-elimDᵗ x cl r))
  ofW-elimDᵗ x cl (ifᵗ c a b)   =
    ⊔-elim-help (ofWᵗ c) ((ofWᵗ a) ⊔ (ofWᵗ b)) (ofWᵉ cl)
                (ofW-elimDᵗ x cl c)
                (⊔-elim-help (ofWᵗ a) (ofWᵗ b) (ofWᵉ cl)
                             (ofW-elimDᵗ x cl a) (ofW-elimDᵗ x cl b))
  ofW-elimDᵗ x cl (primᵗ _ a)   = ofW-elimDᵗ x cl a
  ofW-elimDᵗ x cl (strmᵗ e)     = ofW-elimD x cl e

  ofW-elimGᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
    (cl : Closed Γ t) (ts : List (Tm Γ Δᵍ Δ Θ u)) →
    ofWᵗˢ (elimGTms x cl ts) ≤ ofWᵗˢ ts ⊔ ofWᵉ cl
  ofW-elimGᵗˢ x cl []       = z≤n
  ofW-elimGᵗˢ x cl (y ∷ ys) =
    ⊔-elim-help (ofWᵗ y) (ofWᵗˢ ys) (ofWᵉ cl)
                (ofW-elimGᵗ x cl y) (ofW-elimGᵗˢ x cl ys)

  ofW-elimDᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δ)
    (cl : Closed Γ t) (ts : List (Tm Γ Δᵍ Δ Θ u)) →
    ofWᵗˢ (elimDTms x cl ts) ≤ ofWᵗˢ ts ⊔ ofWᵉ cl
  ofW-elimDᵗˢ x cl []       = z≤n
  ofW-elimDᵗˢ x cl (y ∷ ys) =
    ⊔-elim-help (ofWᵗ y) (ofWᵗˢ ys) (ofWᵉ cl)
                (ofW-elimDᵗ x cl y) (ofW-elimDᵗˢ x cl ys)

-- eval never widens: every of-list in the result comes from the
-- template's strm-subtrees (subΘ'd) or the environment
ofW-evalWith : ∀ {n} {Γ : Ctx n} {Θ t} (Ω : ℕ)
  (tm : Tm Γ [] [] Θ t) (env : All (Val Γ) Θ) →
  EnvOfW Ω env → ofWᵗ tm ≤ Ω →
  ofWᵛ t (evalWith tm env) ≤ Ω
ofW-evalWith Ω (varᵗ x)  env hσ h = envofw-lookup Ω env hσ x
ofW-evalWith Ω unit̂      env hσ h = z≤n
ofW-evalWith Ω (bool̂ _)  env hσ h = z≤n
ofW-evalWith Ω (nat̂ _)   env hσ h = z≤n
ofW-evalWith Ω (pairᵗ a b) env hσ h =
  ⊔-lub (ofW-evalWith Ω a env hσ (⊔ˡ (ofWᵗ a) (ofWᵗ b) h))
        (ofW-evalWith Ω b env hσ (⊔ʳ (ofWᵗ a) (ofWᵗ b) h))
ofW-evalWith Ω (fstᵗ p) env hσ h with evalWith p env | ofW-evalWith Ω p env hσ h
... | (a , b) | ihp = ⊔ˡ (ofWᵛ _ a) (ofWᵛ _ b) ihp
ofW-evalWith Ω (sndᵗ p) env hσ h with evalWith p env | ofW-evalWith Ω p env hσ h
... | (a , b) | ihp = ⊔ʳ (ofWᵛ _ a) (ofWᵛ _ b) ihp
ofW-evalWith Ω (inlᵗ a) env hσ h = ofW-evalWith Ω a env hσ h
ofW-evalWith Ω (inrᵗ a) env hσ h = ofW-evalWith Ω a env hσ h
ofW-evalWith Ω (caseᵗ {s = s} {t = t} sc l r) env hσ h
  with evalWith sc env
     | ofW-evalWith Ω sc env hσ (⊔ˡ (ofWᵗ sc) (ofWᵗ l ⊔ ofWᵗ r) h)
... | inj₁ a | iha = ofW-evalWith Ω l (a ∷ᵃ env) (iha , hσ)
      (⊔ˡ (ofWᵗ l) (ofWᵗ r) (⊔ʳ (ofWᵗ sc) (ofWᵗ l ⊔ ofWᵗ r) h))
... | inj₂ b | ihb = ofW-evalWith Ω r (b ∷ᵃ env) (ihb , hσ)
      (⊔ʳ (ofWᵗ l) (ofWᵗ r) (⊔ʳ (ofWᵗ sc) (ofWᵗ l ⊔ ofWᵗ r) h))
ofW-evalWith Ω (ifᵗ c a b) env hσ h with evalWith c env
... | true  = ofW-evalWith Ω a env hσ
      (⊔ˡ (ofWᵗ a) (ofWᵗ b) (⊔ʳ (ofWᵗ c) (ofWᵗ a ⊔ ofWᵗ b) h))
... | false = ofW-evalWith Ω b env hσ
      (⊔ʳ (ofWᵗ a) (ofWᵗ b) (⊔ʳ (ofWᵗ c) (ofWᵗ a ⊔ ofWᵗ b) h))
ofW-evalWith Ω (primᵗ add arg)  env hσ h = z≤n
ofW-evalWith Ω (primᵗ sub arg)  env hσ h = z≤n
ofW-evalWith Ω (primᵗ mul arg)  env hσ h = z≤n
ofW-evalWith Ω (primᵗ eqᵖ arg)  env hσ h = z≤n
ofW-evalWith Ω (primᵗ ltᵖ arg)  env hσ h = z≤n
ofW-evalWith Ω (primᵗ notᵖ arg) env hσ h = z≤n
ofW-evalWith Ω (strmᵗ e) []ᵃ       hσ h = h
ofW-evalWith Ω (strmᵗ e) (v ∷ᵃ vs) hσ h = ofW-subΘᵉ Ω [] (v ∷ᵃ vs) e hσ h

-- machine faces, mirroring fnCapLive / fnCapNode / frameB? /
-- pathB? / regsB? with the flat cap Ω
ofWLive : ∀ {n} {Γ : Ctx n} → ℕ → LiveSource Γ → Bool
ofWLive Ω l =
  all (λ tv → ofWᵛ (LiveSource.elemTy l) (proj₂ tv) ≤ᵇ Ω)
      (LiveSource.pending l)

ofWNode : ∀ {n} {Γ : Ctx n} → ℕ → NodeState Γ → Bool
ofWNode Ω (scan-st {t} v)   = ofWᵛ t v ≤ᵇ Ω
ofWNode Ω (concat-st q _ _) = all (λ o → ofWᵉ o ≤ᵇ Ω) q
ofWNode Ω (take-st _)       = true
ofWNode Ω (merge-st _ _)    = true
ofWNode Ω (switch-st _ _)   = true
ofWNode Ω (exhaust-st _ _)  = true

frameΩ? : ∀ {n} {Γ : Ctx n} {s u} → ℕ → Frame Γ s u → Bool
frameΩ? Ω (map-f fn)         = ofWᵗ fn ≤ᵇ Ω
frameΩ? Ω (scan-f fn _)      = ofWᵗ fn ≤ᵇ Ω
frameΩ? Ω (take-f _)         = true
frameΩ? Ω (from-inner _ _ _) = true
frameΩ? Ω (thru-outer _ _)   = true

pathΩ? : ∀ {n} {Γ : Ctx n} {s t} → ℕ → Path Γ s t → Bool
pathΩ? Ω root           = true
pathΩ? Ω (share-sink i) = true
pathΩ? Ω (f ↠ p)        = frameΩ? Ω f ∧ pathΩ? Ω p

regsΩ? : ∀ {n} {Γ : Ctx n} {t} → ℕ
       → List (RegId × Source × Chain Γ t) → Bool
regsΩ? Ω = all (λ en → pathΩ? Ω (proj₂ (proj₂ (proj₂ en))))

-- the Ω seed: program plus slots, a sum dominating the max —
-- shaped exactly like ΨAt
inputOfW : ∀ {n} {Γ : Ctx n} {t : Ty} → ObservableInput (Val Γ t) → ℕ
inputOfW {t = t} (hot async) =
  sum (map (λ tv → ofWᵛ t (Timed.val tv)) async)
inputOfW {t = t} (cold sync async) =
  sum (map (ofWᵛ t) sync)
  + sum (map (λ tv → ofWᵛ t (Timed.val tv)) async)

slotOfW : ∀ {n} {Γ : Ctx n} {t} → Slot Γ t → ℕ
slotOfW (scripted i) = inputOfW i
slotOfW (shared d)   = ofWᵉ d

slotsOfW : ∀ {n} {Γ : Ctx n} → Slots Γ → ℕ
slotsOfW sl = sum (tabulate λ i → slotOfW (sl i))

ΩAt : ∀ {n} {Γ : Ctx n} {t} → Closed Γ t → Slots Γ → ℕ
ΩAt e sl = ofWᵉ e + slotsOfW sl

-- THE FLAT WIDTH INVARIANT: every width in the machine ≤ Ω —
-- stores, node states, registered frames, and the (never-changing)
-- slots.  No ledger position: Ω is a constant of the whole run.
widthOK? : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
         → ℕ → Sched Γ → EvalSt e → Bool
widthOK? Ω sched st =
  all (ofWLive Ω) (Sched.live sched)
  ∧ all (λ kv → ofWNode Ω (proj₂ kv)) (EvalSt.nodes st)
  ∧ regsΩ? Ω (EvalSt.registry st)
  ∧ (slotsOfW (Sched.slots sched) ≤ᵇ Ω)

eventΩ? : ∀ {n} {Γ : Ctx n} {u} → ℕ → InstEvent (Val Γ u) → Bool
eventΩ? {u = u} Ω (value v) = ofWᵛ u v ≤ᵇ Ω
eventΩ? Ω (init _)    = true
eventΩ? Ω (close _ _) = true
eventΩ? Ω (handoff _) = true
eventΩ? Ω complete    = true

burstΩ? : ∀ {n} {Γ : Ctx n} {u} → ℕ → Stream Γ u → Bool
burstΩ? Ω = all (λ em → all (eventΩ? Ω) (InstEmit.events em))

------------------------------------------------------------------
-- (W11) THE WIDTH WALK — PROVEN (2026-07-25), below.  Ω is flat, so
-- every statement is pure preservation: no existential, no receipt,
-- no widening.  The clique lives at the bottom of the file:
--
--   subscribeE-width ← subscribeAll-width, pushBurst-width,
--                      subscribeE-input-width (→ sharedSlot /
--                      sharedConnect-width), subscribeE-defer-width
--   stepFrame-width  ← the five frames, as stepFrame-wet:
--                      map (map-applyFn-Ω off ofW-evalWith),
--                      scan (scanVals-ofW), take (takeVals-Ω,
--                      cutThrough-regsΩ/-closesΩ), thru-outer
--                      (thruConsume/thruWalk/thruWrap-width),
--                      from-inner (concatDrain/innerFinish-width)
--   cascadeGo-width  ← chainStep-width ← foldPath-width ←
--                      dispatchShare-width ← shareGo-width
--
-- over the flat state lemmas (W11-A) mirroring install-INV /
-- register-INV / addLive-INV / latch-INV / shareFinish-INV.
-- widthOK? has FOUR conjuncts (live, nodes, registry, slots) against
-- INV?'s six: no length rider, so register-width pays no ledger edge
-- at all where register-INV pays a ×2.  The ONE width mint in the
-- machine is ofᵉ, and it mints exactly its own list, which the entry
-- seed ΩAt already dominates — that is why the walk needs no running
-- position where the size ledger needs capᴱ.
--
-- Consumed by subscribeE-walk's joint face below (its widthOK? /
-- ofWᵉ / pathΩ? conjuncts), which is where the width bound feeds the
-- hop targets' rank drops.
--
-- WORTH TRYING, LATER: fnCapᵉ and ofWᵉ differ in only two clauses —
-- ofᵉ mints a width (`length ts ⊔ …`) where fnCap does not, and
-- fnCap pairs each fn with its caseWᵗ.  Otherwise they are the same
-- recursion, and the fnCap half of INV? has the same four-conjunct
-- shape as widthOK?.  A module parameterised over the measure would
-- collapse this walk and the proven fnCap half into one.
--
-- DECIDED 2026-07-25: NOT then — W11 was ground as a direct mirror
-- instead.  The fnCap half is not a freestanding artifact (it lives
-- as conjuncts inside subscribeE-walkS's clause induction and the
-- wet clique), the joint face also states INV?, and the two measures
-- differ per clause, so the abstraction needs hooks and is not free.
-- Restructuring INV? mid-proof would churn both at once, and an
-- abstraction that turned out unclean halfway would leave INV?
-- half-refactored — the worst outcome.  REVISIT at end-of-proof
-- cleanup, once Formal-Verification is discharged and nothing is in
-- flux: the two walks are now both proven, so the merge would be a
-- pure deduplication with no open risk.
------------------------------------------------------------------

------------------------------------------------------------------
-- THE LENGTH LEDGER's vocabulary (memo (5), corrected form)
------------------------------------------------------------------

-- path length = frames to cross.  The walk invariant
-- `pathLen κ + d ≤ ℓ` costs nothing to preserve: a structural
-- edge adds one frame and drops the descent by one, a hop edge
-- adds one frame against dBound-hop's strict drop, and a connect
-- resets to share-sink — so one entry-frozen ℓ bounds every
-- frame-crossing and every registered path for the whole walk
pathLen : ∀ {n} {Γ : Ctx n} {s t} → Path Γ s t → ℕ
pathLen root           = 0
pathLen (share-sink i) = 0
pathLen (f ↠ p)        = suc (pathLen p)

regsLen? : ∀ {n} {Γ : Ctx n} {t} → ℕ
         → List (RegId × Source × Chain Γ t) → Bool
regsLen? ℓ = all (λ en → pathLen (proj₂ (proj₂ (proj₂ en))) ≤ᵇ ℓ)

-- the machine's own allocation counter: every source / ordinal /
-- node / registration mint bumps one of these, so a walk's total
-- subscription work is a counter delta — what the ledger reads
mintCount : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
          → Sched Γ → EvalSt e → ℕ
mintCount sched st =
  Sched.nextOrdinal sched + Sched.nextSource sched
  + Sched.nextNode sched + EvalSt.nextReg st

-- one InstEmit costs suc (its event count): burstLen bounds the
-- emit count and the total event count at once
burstLen : ∀ {n} {Γ : Ctx n} {u} → Stream Γ u → ℕ
burstLen b = sum (map (λ em → suc (length (InstEmit.events em))) b)

-- THE RECURRENCE-CLOSED CAP.  Per-clause obligations (c ≤ 4 own
-- mints; oneShotBurst events ≤ 3+Ω; hops ≤ the child's burstLen,
-- each a fresh subtree at a strictly smaller descent; per-value
-- fold/hop sites ≤ frame crossings ≤ ℓ) all close under
--   walkCap(d)² · base + walkCap(d-1) + c ≤ walkCap(suc d)
-- because the exponent triples per descent step: β^(2·3^d + 2) ≤
-- β^(3^(suc d)) once 3^d ≥ 2, and the d ∈ {0,1} cases are
-- degenerate (a demand that small admits no child subtree).
walkCap : (Ω ℓ d : ℕ) → ℕ
walkCap Ω ℓ d = ((3 + Ω) * suc ℓ) ^ (3 ^ d)

------------------------------------------------------------------
-- THE JOINT WALK FACE (2026-07-24): wet half, dry half, and the
-- length ledger in ONE contract — memo (5)(b)'s "state them
-- together".  Settled design points:
--   · d is an UPPER bound on the call's dBound demand (≤, not ≡):
--     every conjunct is monotone in d, so callers weaken freely
--     and clause proofs descend by exactly one per edge.
--   · THE CEILING capᴱ W (E·3^(suc Ψ·walkCap)) ≤ V ties the
--     halves together: the receipt conjunct E′ ≤ E·3^(…) keeps
--     every mid-walk ledger position under it, so every mid-walk
--     store and emission is sized ≤ V — exactly what dBound-hop's
--     s′ ≤ V reset and the rank machinery's class caps need at
--     hop edges.  V is the caller's DESCENT ANCHOR — at the root
--     instantiation, the landing budget sizeBudgetAt (suc id),
--     where the ceiling becomes memo (5)'s story-count
--     arithmetic.  No fixed V survives as a store INVARIANT
--     (folds outgrow it) — it survives as a CEILING on the
--     receipt, which is why the receipt conjunct is load-bearing
--     and not instrumentation.
--   · the dry half consumes hasAtLeast (suc d) peels against
--     dBound-μ/-hop/-connect; hop targets get their rank drop
--     from the shell hop machinery and their width bound from W11
--     applied to the child call.
--   · subsumption: subscribeE-walkS below is this contract's
--     store-half projection — its ground clauses lift conjunct by
--     conjunct in the grind.  The two cores at the bottom stay
--     until the landing composes (𝔉 into the boundary).
------------------------------------------------------------------

postulate
  -- THE SPLIT-ANCHOR FACE (2026-07-29).  The 2026-07-24 statement was
  -- VACUOUS: a single V was at once the demand anchor and the store
  -- ceiling, and those two roles contradict each other (walk-hyps-absurd
  -- below).  Repaired here by anchoring the demand — and the emitted-hopD
  -- conjunct that feeds the *All recursion, which must sit at the SAME
  -- anchor or the recursion cannot feed itself — at the call's own ENTRY
  -- bound capᴱ W E.
  --
  -- V and the ceiling hypothesis are GONE, not renamed: once the demand
  -- and burstHopD? move off V, V occurs nowhere in the conclusion, and a
  -- hypothesis constraining a variable the statement never mentions again
  -- is dead weight.  The repaired face is strictly smaller than the old
  -- one.
  --
  -- READ hop-anchor-absurd BELOW BEFORE GRINDING THIS.  Per-call
  -- anchoring does not by itself discharge the hop edge; the probe is
  -- machine-checked and it REFUTES.
  subscribeE-walk : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (Ψ W Ω ℓ : ℕ) (g : Gas) (b : Closed Γ u) (κ : Path Γ u t)
    (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) (E d : ℕ) →
    3 ≤ E →
    INV? Ψ (capᴱ W E) sched st ≡ true →
    sizeᵉ b ≤ capᴱ W E → fnCapᵉ b ≤ Ψ →
    pathB? (capᴱ W E) Ψ κ ≡ true →
    widthOK? Ω sched st ≡ true → ofWᵉ b ≤ Ω → pathΩ? Ω κ ≡ true →
    -- demand, anchored at this call's entry store bound
    dBound (capᴱ W E) (hopR (capᴱ W E))
           (unconn (Sched.slots sched) (EvalSt.connectedShares st))
           (hopDᵉ (capᴱ W E) b) (syncSizeᵉ b) ≤ d →
    g hasAtLeast suc d →
    pathLen κ + d ≤ ℓ →
    regsLen? ℓ (EvalSt.registry st) ≡ true →
    let r = subscribeE g b κ id now sched st
    in Σ ℕ λ E′ → (E ≤ E′)
       × (E′ ≤ E * 3 ^ (suc Ψ * walkCap Ω ℓ d))
       × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
       × (burstB? (capᴱ W E′) Ψ (proj₁ r) ≡ true)
       -- the hop edge's feed: at the SAME anchor as the demand
       × (burstHopD? (capᴱ W E) (hopDᵉ (capᴱ W E) b) (proj₁ r) ≡ true)
       × (hasDry (proj₁ r) ≡ false)
       × (mintCount (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
            ≤ mintCount sched st + walkCap Ω ℓ d)
       × (burstLen (proj₁ r) ≤ walkCap Ω ℓ d)
       × (regsLen? ℓ (EvalSt.registry (proj₂ (proj₂ r))) ≡ true)

------------------------------------------------------------------
-- REFUTATION 1 (the statement): the 2026-07-24 face was vacuous.
--
--   (demand)  dBound V (hopR V) U (hopDᵉ V b) (syncSizeᵉ b) ≤ d
--   (ceiling) capᴱ W (E * 3 ^ (suc Ψ * walkCap Ω ℓ d))       ≤ V
--
-- (demand) puts d ≥ suc V as soon as the call has ONE unconnected
-- share or ONE remaining hop, since dBound V R U r s expands to
-- s + suc V * (r + suc R * U).  (ceiling) puts V above a tower in d:
-- walkCap Ω ℓ d ≥ 3^(3^d) ≥ d, and capᴱ W X ≥ 2^X > X.  d ≥ suc V and
-- V > d.  walk-hyps-absurd is the proof; walk-hyps-splitAnchor is the
-- contrast showing the split makes the same constraints satisfiable.
------------------------------------------------------------------

-- (demand) alone already puts d past V, given one share or one hop
sucV≤d : ∀ (V R U r s d : ℕ) → 1 ≤ r + suc R * U →
  dBound V R U r s ≤ d → suc V ≤ d
sucV≤d V R U r s d 1≤ h =
  ≤-trans (≤-trans (≤-reflexive (sym (*-identityʳ (suc V))))
                   (*-monoʳ-≤ (suc V) 1≤))
          (≤-trans (m≤n+m (suc V * (r + suc R * U)) s) h)

-- walkCap's base is ≥ 3 and its exponent is 3^d, so it dominates d
d≤walkCap : ∀ (Ω ℓ d : ℕ) → d ≤ walkCap Ω ℓ d
d≤walkCap Ω ℓ d =
  ≤-trans (k≤3^k d)
    (≤-trans (^-monoʳ-≤ 3 (k≤3^k d))
             (^-monoˡ-≤ (3 ^ d) 3≤β))
  where
  3≤β : 3 ≤ (3 + Ω) * suc ℓ
  3≤β = ≤-trans (m≤m+n 3 Ω)
          (≤-trans (≤-reflexive (sym (*-identityʳ (3 + Ω))))
                   (*-monoʳ-≤ (3 + Ω) (s≤s z≤n)))

-- so does the ceiling's whole exponent argument
d≤walkArg : ∀ (Ψ Ω ℓ d E : ℕ) → 3 ≤ E →
  d ≤ E * 3 ^ (suc Ψ * walkCap Ω ℓ d)
d≤walkArg Ψ Ω ℓ d E 3≤E =
  ≤-trans (d≤walkCap Ω ℓ d)
    (≤-trans (k≤3^k (walkCap Ω ℓ d))
      (≤-trans (^-monoʳ-≤ 3 w≤Ψw) E-mul))
  where
  w : ℕ
  w = walkCap Ω ℓ d
  w≤Ψw : w ≤ suc Ψ * w
  w≤Ψw = ≤-trans (≤-reflexive (sym (*-identityˡ w)))
                 (*-monoˡ-≤ w {1} {suc Ψ} (s≤s z≤n))
  E-mul : 3 ^ (suc Ψ * w) ≤ E * 3 ^ (suc Ψ * w)
  E-mul = ≤-trans (≤-reflexive (sym (*-identityˡ (3 ^ (suc Ψ * w)))))
                  (*-monoˡ-≤ (3 ^ (suc Ψ * w)) {1} {E}
                             (≤-trans (s≤s z≤n) 3≤E))

-- THE REFUTATION.  Instantiate at any real call: U = unconn of a
-- program with a shared slot (≥ 1 at the root, where connectedShares
-- is []), or r = hopDᵉ V b of any *All (≥ 1 by hopD's own suc).
walk-hyps-absurd : ∀ (Ψ W Ω V ℓ R U r s d E : ℕ) →
  3 ≤ E →
  1 ≤ r + suc R * U →
  dBound V R U r s ≤ d →
  capᴱ W (E * 3 ^ (suc Ψ * walkCap Ω ℓ d)) ≤ V →
  ⊥
walk-hyps-absurd Ψ W Ω V ℓ R U r s d E 3≤E 1≤ dem ceil =
  <-irrefl refl
    (≤-trans (≤-trans (sucV≤d V R U r s d 1≤ dem)
                      (d≤walkArg Ψ Ω ℓ d E 3≤E))
             (≤-trans (<⇒≤ (n<2^n X))
                      (≤-trans (^-monoˡ-≤ X (s≤s (s≤s z≤n))) ceil)))
  where
  X : ℕ
  X = E * 3 ^ (suc Ψ * walkCap Ω ℓ d)

-- AND THE CONTRAST, which pins the diagnosis: measure the demand at
-- the entry store bound B₀ instead of at V, change nothing else, and
-- the same constraint set is satisfiable — for every choice of the
-- other parameters, and with V and d written down explicitly.  The
-- circle was the whole problem; nothing else about the face is.
walk-hyps-splitAnchor : ∀ (Ψ W Ω ℓ E B₀ R U r s : ℕ) →
  Σ ℕ λ V → Σ ℕ λ d →
    (dBound B₀ R U r s ≤ d)
    × (capᴱ W (E * 3 ^ (suc Ψ * walkCap Ω ℓ d)) ≤ V)
walk-hyps-splitAnchor Ψ W Ω ℓ E B₀ R U r s =
  capᴱ W (E * 3 ^ (suc Ψ * walkCap Ω ℓ (dBound B₀ R U r s)))
  , dBound B₀ R U r s , ≤-refl , ≤-refl

------------------------------------------------------------------
-- REFUTATION 2 (the hop edge): THE SPLIT ANCHOR DOES NOT CLOSE
-- EITHER.  Probed 2026-07-29 BEFORE grinding any clause, per the
-- outside-in rule — the vacuity had already shown once that this face
-- can look grind-ready and be uninstantiable, so the most uncertain
-- piece goes first.  IT REFUTES.
--
-- With per-call anchoring, each call measures its demand at its OWN
-- entry bound.  The outer call sits at A = capᴱ W E with demand ≤ d.
-- It re-enters (subscribeInner) on an inner observable o drawn from
-- the carrier's burst.  By then the ledger has moved to E″, and the
-- face's own receipt conjunct permits E″ anywhere up to
-- E * 3 ^ (suc Ψ * walkCap Ω ℓ d).  So the inner call's anchor is
-- A″ = capᴱ W E″, its demand is dBound A″ (hopR A″) U″ r″ s″, and the
-- hop edge owes  suc (inner demand) ≤ d.
--
-- That is impossible at the ledger the face itself permits:
--
--   · d  ≤ E″                    (d≤walkArg — the work bound dominates d)
--   · E″ <  capᴱ W E″ ≡ A″       (n<2^n, then base 2 ≤ 2 + 2W)
--   · suc A″ ≤ inner demand      (sucV≤d — ONE inner share or ONE
--                                 remaining hop is enough)
--
-- so A″ < d ≤ E″ < A″.  Absurd.
--
-- WHAT THIS MEANS.  The split did not remove the circle; it MOVED it,
-- from between the face's two hypotheses to between a call and its own
-- hop child.  Both times the mechanism is identical: an anchor that
-- tracks the store, a demand monotone in that anchor, and a store that
-- grows super-exponentially in the demand.  Renaming the anchor cannot
-- fix a loop whose three edges are all still present.
--
-- Note the refutation needs NO facts about hopD at all — not its scan
-- clause, not its monotonicity in the anchor.  It is pure dBound /
-- capᴱ / walkCap arithmetic, so no recalibration of the hop measure
-- can escape it.  (Anchor-monotonicity of hopD would make it worse,
-- not better: hopDᵉ A″ o ≥ hopDᵉ A o, so the inner r″ is inflated too.)
--
-- WHAT WOULD ESCAPE IT, stated so the next session does not re-derive
-- it: the anchor must be SHARED across the whole walk (so the hop edge
-- never transports between two different anchors) AND
-- ENTRY-DETERMINED (so it does not depend on d).  That is exactly what
-- the ceiling was trying and failing to be — it was shared, but it was
-- indexed by walkCap Ω ℓ d, which is d-dependent, and that is the
-- edge that closed the loop.  So the change is not to the anchor at
-- all: it is to the GROWTH CAP.  walkCap's index must become a
-- d-free measure of the walk's work — the hop depth and the syntax
-- both bound it, and both are fixed at entry — after which one shared
-- anchor capᴱ W (E * 3 ^ (suc Ψ * walkCap Ω ℓ G)) with G entry-
-- determined serves as the demand anchor, the s′ reset bound, and the
-- store ceiling at once, with no circularity.
--
-- That is a contract change beyond the anchor split, so it is NOT
-- taken here.
------------------------------------------------------------------

hop-anchor-absurd : ∀ (Ψ W Ω ℓ E d U″ r″ s″ : ℕ) →
  3 ≤ E →
  -- the inner call is nontrivial: one unconnected share or one hop
  1 ≤ r″ + suc (hopR (capᴱ W (E * 3 ^ (suc Ψ * walkCap Ω ℓ d)))) * U″ →
  -- what the hop edge owes, at the largest ledger the receipt permits
  suc (dBound (capᴱ W (E * 3 ^ (suc Ψ * walkCap Ω ℓ d)))
              (hopR (capᴱ W (E * 3 ^ (suc Ψ * walkCap Ω ℓ d))))
              U″ r″ s″) ≤ d →
  ⊥
hop-anchor-absurd Ψ W Ω ℓ E d U″ r″ s″ 3≤E 1≤ owed =
  <-irrefl refl
    (≤-trans A″<d (≤-trans (d≤walkArg Ψ Ω ℓ d E 3≤E) (<⇒≤ E″<A″)))
  where
  E″ : ℕ
  E″ = E * 3 ^ (suc Ψ * walkCap Ω ℓ d)
  A″ : ℕ
  A″ = capᴱ W E″

  -- the inner demand already exceeds its own anchor, and d exceeds it
  A″<d : suc A″ ≤ d
  A″<d = ≤-trans (n≤1+n (suc A″))
           (≤-trans (s≤s (sucV≤d A″ (hopR A″) U″ r″ s″
                            (dBound A″ (hopR A″) U″ r″ s″) 1≤ ≤-refl))
                    owed)

  -- but the anchor is exponential in the ledger, which already
  -- dominates d
  E″<A″ : suc E″ ≤ A″
  E″<A″ = ≤-trans (n<2^n E″) (^-monoˡ-≤ E″ (s≤s (s≤s z≤n)))

------------------------------------------------------------------
-- HOP DESCENT, the *All clause's missing edge — AND THE OPEN HOLE.
-- subscribeInner re-enters subscribeE on an observable VALUE o
-- carried by the carrier's burst, so the clause owes a strictly
-- smaller dBound demand for o.  Two routes were stated for it.  One
-- survives; the other was REFUTED 2026-07-27 and is gone.
--
--   hop-anchored (SURVIVES)  o crossed a SHARE boundary — it came out
--             of slot i's def, whose shells are unrelated to b's.
--             This exits the per-value order entirely and pays with U:
--             the connect edge strictly drops unconn
--             (sharedConnect-unconn, proven below), and o is
--             store-sized, so connect-anchor re-anchors rank ≤ R.
--             Fed to dBound-connect.
--
--   hop-descends (FALSE)  measureE B o ≺ᵛ measureE B b — "o's shells
--             sit inside b's", fed to dBound-hop through rank-mono-≺.
--             This does not hold, at ANY of its three claimed sites.
--             agda/probe/Hop-Descent-Probe.agda refutes all three by
--             absurd pattern (make hop-descent-probe).
--
-- WHY IT IS FALSE, in one line: a hop value is a TEMPLATE
-- INSTANTIATED WITH A VALUE, and a template may use its bound
-- variable more than once.  subΘ then copies that value's shells
-- once per occurrence — precisely the plugs summand that
-- subΘ-countsᵗ makes exact — while the carrier holds them once.  So
-- duplication makes the hop's multiset strictly BIGGER and ≺ᵛ points
-- the wrong way.  The probe's witness is
--   mergeAll (map (x ↦ merge (of (x , x))) (of (strm big)))
-- whose hop grows class-4 from 1 to 2.  Note it needs no `caseᵗ` and
-- no exotic typing — an ordinary two-use lambda over an obs-typed
-- source does it.
--
-- Three things this KILLS, and it is worth being exact about each:
--
--   · the isData restriction (2026-07-27) does NOT rescue site 2a.
--     It empties the plug when the SOURCE is data, but `caseᵗ` mints
--     an obs-carrying value from a closed term — `inlᵗ (strmᵗ big)` —
--     and binds it to a Θ var the branch then uses twice.  The
--     restriction is still right for its own reason (it removes the
--     scripted-slot regress, see obs-slot-shared) but it does not
--     touch this.
--   · site 2b's guarding premise does not rescue it either.  The
--     probe DISCHARGES that premise and the conclusion still fails.
--   · subscribeE-walk's `r` had to be REPLACED, not merely proven.
--     While it was rank V (measureE V b) the walk handed the *All
--     clause a demand `d` that the clause was to peel with dBound-hop,
--     and with the hop's measure able to exceed the carrier's that
--     peel was unavailable — `d` could simply under-count the walk.
--     SETTLED 2026-07-28: `r` is now hopDᵉ V b (phase 2 below).
--
-- Site 3, μ-unfold, was unaffected and had been proven as unfoldμ-≺;
-- under hopD it is not even an inequality (hopD is EQUAL across an
-- unfold), so the shell version is retired with the rest.
--
-- WHAT `r` MUST BE INSTEAD is open.  Note first that this is the
-- SAME pattern syncBudget's memo already records as the reason the
-- budget must be a tower at all — "a scanᵉ with an obs-typed
-- accumulator whose template embeds the accumulator twice
-- (acc ↦ mergeAll(of[acc,acc]))", measured 2026-07-19.  That memo
-- read the pattern as a demand SIZE problem and towered the budget
-- for it; what went unnoticed is that the same two-use template also
-- destroys the per-hop ORDER the demand was to descend in.  The size
-- half is fine and stays.
--
-- Ruled out as `r` so far, each against the probe's witness:
--   · the shell multiset — the refutation above
--   · syncSizeᵉ — 16 ↦ 17 across the witness's first hop
--   · sizeᵉ — same, and for the same reason
--   · obs-depth of the subscribed type — CONSTANT along the
--     witness's hop chain (natᵗ, natᵗ, natᵗ), so never strict
--   · strmᵗ-nesting depth — 1, 1, 0: non-strict at the first hop
--
-- THE CANDIDATE, now stated as Rx.Hop-Depth.hopD: a REMAINING-HOP
-- count — how many *All frames a subscription can still enter.  Two
-- of its clauses were forced by witnesses rather than chosen:
--
--   · mapᵉ composes by `+`, not `⊔`.  A fn's template is applied to
--     the source's values, so the chains CONCATENATE.  Lifting the
--     probe's leaf from `big` to mergeAll (of (strm big)) reads 4 ↦ 2
--     under `+` and 2 ↦ 2 — a tie — under `⊔`.
--   · the source's depth enters scaled by occsᵗ.  A bare `+` did not
--     survive a nested map: subΘ plugs the value at EVERY Θ-var
--     occurrence, so two occurrences either side of a `+` count the
--     plugged depth twice.  Same multiplicity the proven
--     sync-linearity ledger already uses.
--
-- V enters at scanᵉ, where the accumulator is REFOLDED: hopD(accₖ)
-- grows once per folded value — the 07-19 memo's "after k folded
-- values the acc nests k deep" — so the clause pays (2 + occs)^V,
-- from solving aₖ ≤ F + c·(aₖ₋₁ ⊔ m) at k ≤ V.  hopD is therefore a
-- function of the expression AND the store bound, which is what
-- dBound already anticipates in allowing r ≤ R = suc V ^ suc V.
--
-- MEASURED (2026-07-27) before anything below took a dependency on it.
-- Static, in agda/probe/Hop-Descent-Probe.agda — all four refutation
-- witnesses descend strictly (2↦1, 2↦1, 2↦1, 4↦2); the scan
-- accumulator's depth is 0,1,2,3 after 0..3 folds, against a clause
-- paying 256 at V ≡ 4; and hopD is EQUAL across a μ unfold, since an
-- unfold substitutes for a Δᵍ variable and those sit only under
-- deferᵉ, which hopD cuts.  So the μ edge is weakly monotone in r and
-- keeps paying with dBound-μ's s — unfoldμ-≺ was NOT assumed to
-- transfer, it is a fact about the shell multiset and says nothing
-- about hopD.
--
-- Corpus-wide, via the burst probe's numeric hopLog (make
-- burst-probe), testing the emitted-value invariant hopD v ≤ hopD b
-- that the hop edge consumes — with hopD (mergeAllᵉ c) ≡ suc (hopD c),
-- that inequality is exactly what makes a hop strict:
--
--   A  generated, scripted slots     1000 progs   11010 obs   0 viol
--   B  generated, shared slots       1000 progs   17739 obs   0 viol
--   C  directed, 2 slots               19 progs     199 obs   0 viol
--   C₃ directed, 3 slots, 2 shares     36 progs     681 obs   0 viol
--   D  directed, obs into templates    14 progs     172 obs   0 viol
--   D  generated, obs into templates  700 progs   17804 obs   0 viol
--
-- Re-measured in full after the coefficient became a multiplier: the
-- coefficient sits on both sides of every one of these inequalities,
-- so none of the earlier greens carried over.
--
-- B was first run at 6 programs (three seeds deep) and REBALANCED
-- 2026-07-28 toward breadth — 40 seeds × 25 programs at depth 3 —
-- because random SHARE shapes are where a surprise would hide and
-- depth had been bought at coverage's expense.
--
-- D WAS ADDED 2026-07-28 to close a structural blind spot, and it is
-- the only one of the six with a demonstrated ability to see the bug
-- this measure was calibrated against.  A, B, C and C₃ keep every
-- observable inside `ofᵉ (strmᵗ e ∷ …)` with e Θ-CLOSED — the
-- QuickCheck generator's only Fns are natᵗ → natᵗ — so across ~25k hop
-- observations NO program ever substituted an observable into a
-- template.  That is the single mechanism both refutations live in
-- (measureE's duplicated shells; hopD-with-occsᵗ's phantom
-- coefficient), and both were found by adversarial construction rather
-- than by the corpus.  D generates obs-typed templates: an obs-typed
-- source may be wrapped in a mapᵉ whose bound variable is an
-- observable, or a scanᵉ whose accumulator is one.
--
-- D has a DIRECTED half as well, because the generated half could not
-- be trusted alone: reaching the mechanism needs several draws to line
-- up, and 500 generated programs run against the KNOWN-BUGGY occsᵗ
-- coefficient found zero violations.  The directed half forces the
-- conjunction, and measured both ways on identical programs it reads
--
--   occsᵗ (the index-blind count)   130 obs   9 VIOLATIONS
--   the multiplier                  130 obs   0 violations
--
-- Eight of those eleven programs fire under occsᵗ; the other three are
-- controls whose shapes are correct by construction.  That 9 ↦ 0 is
-- the evidence that the corpus can see the mechanism at all — a corpus
-- that cannot fail on the bug it guards is decoration.
--
-- Three further directed programs (mulG/mulG₂) carry the SECOND
-- refutation, the one the per-binder count `occs0ᵗ` also failed: an
-- outer template that mentions its observable once and duplicates
-- nothing, over an inner map whose coefficient multiplies whatever
-- lands in its source.  Their machine-checked static counterpart is
-- Hop-Descent-Probe's mul-exceeds (6 against an allowance of 4 under
-- occs0ᵗ) and mul-fits (2 ≤ 2 under the multiplier); the corpus
-- carries the runtime guard.
--
-- (Two of thirty D seeds time out on pathological programs and are
-- excluded from the count above; the self-doubling scan step is not
-- generated at all, since its syntax doubles per folded value.  Its
-- hop behaviour is refl-checked statically instead.)
--
-- selfcheck and wellFormed clean throughout, so the log does not move
-- the evaluator.  The probe's V is capped at 8 (the real V makes
-- (2+occs)^V a bignum per subscribe and OOMs a depth-4 corpus); a
-- smaller V shrinks the PARENT's allowance, so the cap can only make
-- the test harder, never hide a violation.  Sweeping it over 4/8/16
-- gives identical counts and no violations, so the cap is not deciding
-- the answer.
--
-- AND k ≤ V, the piece whose failure would have reshaped the assembly,
-- turns out to need no measurement at all — it is a CONSEQUENCE of the
-- store invariant this proof already carries, not a new premise:
--
--   · a scan accumulator is a STORED value, and boundedNode above reads
--     exactly `boundedNode B (scan-st v) = sizeᵛ v ≤ᵇ B`, so INV? at
--     instant id already gives sizeᵛ accₖ ≤ sizeBudgetAt e sl id ≡ V;
--   · a fold that DEEPENS the accumulator adds at least one syntax
--     constructor, so k ≤ sizeᵛ accₖ; a fold that does not deepen it
--     does not raise hopD either, so it costs nothing;
--   · hence k ≤ sizeᵛ accₖ ≤ V, which is the scan clause's side
--     condition, discharged from INV? rather than assumed.
--
-- The margin is not close, and that is why no corpus counter was
-- written for it: V is towerℕ ((4 + size) · suc id), so V ≥ towerℕ 5 ≡
-- 2^65536.  A counter comparing a run's fold count against a number
-- that cannot be computed would be vacuous, not evidence.  (k≤towerℕ,
-- already proven above, is the arithmetic half.)
--
-- THE GATE PASSED, and PHASE 2 (the assembly) is DONE as of
-- 2026-07-28 — everything below is now stated in terms of hopD and
-- typechecks.  What moved, and what it cost:
--
--   · `r` is hopDᵉ V b, a plain ℕ.  rank ∘ measureE is gone and
--     NOTHING replaces the rank wrapper — hopD is already the number.
--   · `R` is hopR V = (2+V)^((1+V)^(1+V)), replacing (1+V)^(1+V).
--     (Stated as (2+V)^((1+V)²) on the day, when the coefficient was
--     still a count; the exponent became exponential when it became a
--     multiplier.  See the hop-rank-cap memo above.)  hopD's
--     scan clause pays (2+occs)^V per node, so a store-sized def costs
--     one polynomial degree more in the exponent.  prod≤3pow absorbs
--     it inside the SAME three exponential stories — its slack
--     identity closes on (V+2)³ where it used to close on (V+2)², and
--     it now wants 3V ≤ 2^V (V ≥ 4) where it wanted 2V ≤ 2^V (V ≥ 2).
--     Both are free at V = towerℕ (4+sz) ≥ 2^65536.  THE BUDGET TOWER
--     DOES NOT MOVE: a tower of 2s cannot notice a polynomial in an
--     exponent.
--   · the structural edge stopped being a sub-multiset argument.
--     hopD-map/-take/-scan/-all above are one line each.
--   · the μ edge is not even an inequality — see the hopD structural
--     block's header.
--
-- AND THEN THE HOP EDGE ITSELF WAS REFUTED, same day, before anything
-- was proven — which is what phase 2 existed to find out.
--
-- The plan was that the hop edge needs no postulate: hopD's *All
-- clauses are literally suc (hopD carrier), so a walk conjunct
--
--     every value a subscription emits has hopD ≤ hopD of what was
--     subscribed                                        (burstHopD?)
--
-- would make the strictness definitional.  That conjunct is FALSE for
-- hopD as written.  agda/probe/Hop-Descent-Probe.agda (make
-- hop-descent-probe) carries the witness as refl-checked numbers plus
-- an absurd pattern: a program whose allowance is 2 and whose very
-- first emission is 3.
--
-- WHY, and it is a CALIBRATION bug in one coefficient rather than a
-- failure of the remaining-hop idea.  hopD's mapᵉ clause scales by a
-- coefficient, and the question is what that coefficient counts.
-- Three answers were tried in one day; the first two are refuted by
-- machine-checked witnesses in agda/probe/Hop-Descent-Probe.agda.
--
-- (1) occsᵗ, the index-blind count the sync-linearity ledger uses.
-- It counts EVERY varᵗ in the template.  The coefficient exists to
-- price the SOURCE's value, which is the occurrences of the map's OWN
-- bound variable — those agree on a template and come apart under
-- substitution, since subΘ replaces an OUTER Θ variable by a reified
-- observable carrying its own templates, whose own bound variables
-- occsᵗ then counts as well.  So it inflates although nothing was
-- duplicated.  `plugged` makes that stark with a value of hop depth
-- ZERO: occsᵉ 2, hopD 0, lifting an inner coefficient 2 ↦ 3, and the
-- extra unit multiplies an inner source's hop depth of 1.  The
-- template even DISCARDS the plugged observable (sndᵗ) — the mention
-- alone is enough.
--
-- (2) occs0ᵗ, the same count restricted to the binder's own index.
-- It fixes (1) and stays put under substitution — a plug is Θ-closed,
-- so every variable it brings is compared against an already-bumped
-- index.  It was gated the full way (corpora re-run, static witnesses
-- re-checked) and taken.  It is still wrong, and for a reason that
-- has nothing to do with which variables get counted: it is a COUNT.
-- hopD combines by `⊔` at ofᵉ and pairᵗ, where two mentions cost what
-- one costs; and it MULTIPLIES at mapᵉ, where a plug landing in an
-- inner map's SOURCE is scaled by that inner template's coefficient —
-- a factor no count of outer mentions can see.  `mul-exceeds` is that
-- witness: an outer template that mentions its argument exactly once
-- and duplicates nothing, emitting at hop depth 6 against an
-- allowance of 4.
--
-- Note (1) and (2) point in OPPOSITE directions: (1) over-prices
-- phantom duplication, (2) under-prices real multiplication.  That is
-- what makes the third answer determined rather than guessed — it is
-- pinned from both sides.
--
-- Neither is the two-use duplication that killed measureE.  That was
-- real duplication the measure failed to price at all.
--
-- (3) THE ANSWER, and it is what these coefficients always meant: the
-- plug MULTIPLIER, Rx.Hop-Depth.pmᵗ.  Read hopD as a function of one
-- substituted value's depth; it is affine in that depth,
--
--     hopD (e[v]) ≤ hopD e + pm k e · hopD v
--
-- and pm is the slope — the factor hopD's own arithmetic applies along
-- every path from the root to an occurrence of the variable at index
-- k.  pm is hopD's own recursion with two changes: a variable at index
-- k contributes 1 where hopD contributes 0, and the *All frames drop
-- their `suc`, an operator's hop being added to the plug's depth
-- rather than multiplied by it.  Same tree, a different semiring at
-- the leaves — which is exactly the shape phase 3 was told to look
-- for, arrived at from the induction rather than from the analogy.
--
-- pm inherits the substitution-invariance that made occs0 usable, for
-- the same reason and at the same index.  It also reads the witnesses
-- of (1) and (2) correctly in BOTH directions: 1 where occsᵗ said 3,
-- and 1 where occs0ᵗ's ×3 came from primᵗ positions hopD scores as 0.
--
-- WHAT IT COST, all inside the same three exponential stories: hopR's
-- exponent went from polynomial to exponential (see the hop-rank-cap
-- memo), hopD-size was restated at (2+s)^(V′^s) — the old (2+s)^(V′·s)
-- is FALSE for a multiplier and was retracted rather than left
-- standing — and prod≤3pow's side condition moved from 3V ≤ 2^V (V ≥ 4)
-- to (V+2)² ≤ 2^V (V ≥ 6).  The budget tower did not move.
--
-- WHAT STOOD THROUGHOUT: the structural facts, the μ edge, `r`'s slot
-- being a plain ℕ, and R being a cap on hopD over store-sized syntax
-- whatever the coefficient.  What is RESTATED: the emitted-value
-- conjunct, burstHopD? above, carried by subscribeE-walk.
--
-- PHASE 3 IS DISCHARGED (2026-07-29).  The conjunct's engine is built
-- and contains no postulate:
--
--   pm-subΘ          a coefficient does not move under substitution
--   hopD-subΘᵉ/ᵗ/ᵗˢ  hopD is AFFINE in the substituted depths, with pm
--                    as the slope — subΘ-countsᵉ/ᵗ's induction clause
--                    for clause, no clause failing to transfer
--   hopD-evalWith    the same at evalWith, which is what frames call
--   hopD-applyFn     the one-value instance
--   hopD-map-emit    the shape the walk's mapᵉ clause applies
--
-- pm is what makes the induction close, and finding it was the point:
-- the mapᵉ clause needs exactly `pm 0 f` from its recursive calls, and
-- no occurrence count is that quantity.  The one statement that had to
-- change along the way was the environment bound — evalWith's caseᵗ
-- pushes the scrutinee's value onto the environment, so the bound is
-- per-position and the slope weighted to match; see hopD-evalWith.
------------------------------------------------------------------

-- THE SHARE BOUNDARY IS THE ONLY input SITE AT AN OBSERVABLE TYPE.
-- `scripted` demands T (isData (obs u)), and isData (obs u) is false, so
-- the constructor is uninhabited here and Agda discharges it with (). This
-- is the whole content of the 2026-07-27 restriction, in one absurd pattern:
-- before it, this lemma was false and the *All input clause had a case that
-- could not be paid for.  Every hop that reaches a slot is now a connect.
obs-slot-shared : ∀ {n} {Γ : Ctx n} {u} (s : Slot Γ (obs u)) →
  Σ (Closed Γ (obs u)) λ d → s ≡ shared d
obs-slot-shared (shared d)       = d , refl
obs-slot-shared (scripted {ok = ()} _)

-- and the two NON-connecting share paths carry no values: a spent share
-- emits init/close/complete, a live one emits a bare init, both pure
-- bookkeeping.  So no hop originates there, and the input site reduces to
-- sharedConnect alone — the one path that pays with unconn
share-live-novals : ∀ {n} {Γ : Ctx n} {u} {A : Set} (s : Source) (id : Id) →
  proj₁ (splitBurst {Γ = Γ} {u = u} {A = A}
          (((init s ∷ []) at id from s as subscribe) ∷ [])) ≡ []
share-live-novals s id = refl

share-spent-novals : ∀ {n} {Γ : Ctx n} {u} {A : Set} (s : Source) (id : Id) →
  proj₁ (splitBurst {Γ = Γ} {u = u} {A = A}
          (((init s ∷ close s exhausted ∷ complete ∷ []) at id from s as subscribe) ∷ []))
    ≡ []
share-spent-novals s id = refl

------------------------------------------------------------------
-- PHASE B — the two structural bookkeeping facts, PROVEN, together.
--
-- The slot telescope is read-only and connectedShares is append-only.
-- Both are one induction over subscribeE's whole clique, so they are
-- proven jointly: `Keeps` bundles them and the clique is walked once.
--
-- What makes the grind mechanical rather than exploratory: across all
-- of Rx/Evaluator.agda, `slots =` appears exactly ONCE (sched-init) and
-- `connectedShares =` exactly TWICE (st-init, and sharedConnect, which
-- PREPENDS toℕ i and touches nothing else).  So every clause is refl,
-- the IH, or the one cons — and the one cons is `member-cons`.
--
-- The clique is subscribeE's own cone: subscribeE, subscribeInner,
-- thruConsume/-Walk/-Wrap, concatDrain, innerFinish, innerReact,
-- stepFrame, pushBurst, subscribeAll, sharedConnect,
-- subscribeSharedSlot, takeDispatch, switchKill.  (foldPath and the
-- delivery clique are NOT in it — the burst leaves subscribeE and is
-- pushed through a FRAME, never re-entered through a path.)
------------------------------------------------------------------

-- a RECORD, not a Σ: `keeps-trans` must solve its middle point by
-- unification, and `EvalSt.connectedShares` is not injective — as a Σ
-- the whole grind below blocked on metas.  And it is
-- indexed by the two FIELDS, not by the two states.  The machine
-- rebuilds a schedule as `record sched { nextNode = suc … }`, which is
-- not definitionally the schedule it came from — so a state-indexed
-- record would not accept the recursive call.  Its slots ARE
-- definitionally the same, and that is all this carries.
record KeepsC {n} {Γ : Ctx n} (sl sl′ : Slots Γ) (cs cs′ : List Source) : Set where
  constructor keeps
  field
    slotsEq  : sl′ ≡ sl
    connMono : ∀ s → memberSource s cs ≡ true → memberSource s cs′ ≡ true
open KeepsC

Keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} →
        Sched Γ → EvalSt e → Sched Γ → EvalSt e → Set
Keeps sched st sched′ st′ =
  KeepsC (Sched.slots sched) (Sched.slots sched′)
         (EvalSt.connectedShares st) (EvalSt.connectedShares st′)

keeps-refl : ∀ {n} {Γ : Ctx n} {sl : Slots Γ} {cs : List Source} → KeepsC sl sl cs cs
keeps-refl = keeps refl (λ s p → p)

keeps-trans : ∀ {n} {Γ : Ctx n} {a b c : Slots Γ} {x y z : List Source} →
  KeepsC a b x y → KeepsC b c y z → KeepsC a c x z
keeps-trans (keeps e₁ m₁) (keeps e₂ m₂) =
  keeps (trans e₂ e₁) (λ s p → m₂ s (m₁ s p))

-- the ONE fact about connectedShares the connect edge needs
member-cons : ∀ (s x : Source) (xs : List Source) →
  memberSource s xs ≡ true → memberSource s (x ∷ xs) ≡ true
member-cons s x xs p with sameSource s x
... | true  = refl
... | false = p

------------------------------------------------------------------
-- the clique, declared first (mirrors the evaluator's own block)
------------------------------------------------------------------

subscribeE-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) →
  let r = subscribeE g b κ id now sched st
  in Keeps sched st (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

subscribeInner-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (g : Gas) (op : AllOp) (allNid : NodeId) (κ : Path Γ u t)
  (id : Id) (now : Tick) (o : Val Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) →
  let r = subscribeInner g op allNid κ id now o sched st
  in Keeps sched st (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r)))))
                    (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r)))))

thruConsume-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (g : Gas) (op : AllOp) (nid : NodeId) (κ : Path Γ u t)
  (id : Id) (now : Tick) (o : Val Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) →
  let r = thruConsume g op nid κ id now o sched st
  in Keeps sched st (proj₁ (proj₂ (proj₂ r))) (proj₂ (proj₂ (proj₂ r)))

thruWalk-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (g : Gas) (op : AllOp) (nid : NodeId) (κ : Path Γ u t)
  (id : Id) (now : Tick) (os : List (Val Γ (obs u)))
  (sched : Sched Γ) (st : EvalSt e) →
  let r = thruWalk g op nid κ id now os sched st
  in Keeps sched st (proj₁ (proj₂ (proj₂ r))) (proj₂ (proj₂ (proj₂ r)))

thruWrap-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (op : AllOp) (nid : NodeId) (fin : Bool)
  (vs : List (Val Γ u)) (bs : List (InstEvent (Val Γ t)))
  (sched : Sched Γ) (st : EvalSt e) →
  let r = thruWrap op nid fin (vs , bs , sched , st)
  in Keeps sched st (proj₁ (proj₂ (proj₂ (proj₂ r))))
                    (proj₂ (proj₂ (proj₂ (proj₂ r))))

concatDrain-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (g : Gas) (allNid : NodeId) (κ : Path Γ s t) (id : Id) (now : Tick)
  (q : List (Closed Γ s)) (sched : Sched Γ) (st : EvalSt e) →
  let r = concatDrain g allNid κ id now q sched st
  in Keeps sched st (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r)))))
                    (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r)))))

innerFinish-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (g : Gas) (op : AllOp) (allNid inst : NodeId) (κ : Path Γ s t)
  (id : Id) (now : Tick) (vals : List (Val Γ s))
  (sched : Sched Γ) (st : EvalSt e) (mns : Maybe (NodeState Γ)) →
  let r = innerFinish g op allNid inst κ id now vals sched st mns
  in Keeps sched st (proj₁ (proj₂ (proj₂ (proj₂ r))))
                    (proj₂ (proj₂ (proj₂ (proj₂ r))))

innerReact-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (g : Gas) (op : AllOp) (allNid inst : NodeId) (κ : Path Γ s t)
  (id : Id) (now : Tick) (vals : List (Val Γ s))
  (sched : Sched Γ) (st : EvalSt e) (fin : Bool) →
  let r = innerReact g op allNid inst κ id now vals sched st fin
  in Keeps sched st (proj₁ (proj₂ (proj₂ (proj₂ r))))
                    (proj₂ (proj₂ (proj₂ (proj₂ r))))

takeDispatch-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (nid : NodeId) (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (mns : Maybe (NodeState Γ)) →
  let r = takeDispatch {t = t} {e = e} nid vals fin sched st mns
  in Keeps sched st (proj₁ (proj₂ (proj₂ (proj₂ r))))
                    (proj₂ (proj₂ (proj₂ (proj₂ r))))

switchKill-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (mv : Maybe NodeId) (sched : Sched Γ) (st : EvalSt e) →
  let r = switchKill {t = t} {e = e} mv sched st
  in Keeps sched st (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

stepFrame-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (g : Gas) (id : Id) (now : Tick) (f : Frame Γ s u) (κ : Path Γ u t)
  (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  let r = stepFrame g id now f κ vals fin sched st
  in Keeps sched st (proj₁ (proj₂ (proj₂ (proj₂ r))))
                    (proj₂ (proj₂ (proj₂ (proj₂ r))))

pushBurst-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (g : Gas) (id : Id) (now : Tick) (f : Frame Γ s u) (κ : Path Γ u t)
  (ems : Stream Γ s) (sched : Sched Γ) (st : EvalSt e) →
  let r = pushBurst g id now f κ ems sched st
  in Keeps sched st (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

subscribeAll-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (g : Gas) (op : AllOp) (ns : NodeState Γ) (b : Closed Γ (obs u))
  (κ : Path Γ u t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) →
  let r = subscribeAll g op ns b κ id now sched st
  in Keeps sched st (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

sharedConnect-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (g : Gas) (i : Fin n) (d : Closed Γ (lookup Γ i))
  (κ : Path Γ (lookup Γ i) t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) →
  let r = sharedConnect g i d κ id now sched st
  in Keeps sched st (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

sharedConnect-core : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (g : Gas) (i : Fin n) (d : Closed Γ (lookup Γ i))
  (κ : Path Γ (lookup Γ i) t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) →
  let st₁ = register (toℕ i) κ
              (record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st })
      r   = subscribeE g d (share-sink i) id now sched st₁
  in Keeps sched st (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

sharedSlot-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (g : Gas) (i : Fin n) (d : Closed Γ (lookup Γ i))
  (κ : Path Γ (lookup Γ i) t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) →
  let r = subscribeSharedSlot g i d κ id now sched st
  in Keeps sched st (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

------------------------------------------------------------------
-- the pure leaves: cut/sweep rewrite live, registry, cancelled and
-- nodes — none of them slots, none of them connectedShares
------------------------------------------------------------------

takeDispatch-keeps nid vals fin sched st (just (take-st k))
  with proj₂ (proj₂ (takeVals k vals))
... | true  = keeps refl (λ s p → p)
... | false = keeps refl (λ s p → p)
takeDispatch-keeps nid vals fin sched st nothing                  = keeps-refl
takeDispatch-keeps nid vals fin sched st (just (scan-st _))       = keeps-refl
takeDispatch-keeps nid vals fin sched st (just (merge-st _ _))    = keeps-refl
takeDispatch-keeps nid vals fin sched st (just (concat-st _ _ _)) = keeps-refl
takeDispatch-keeps nid vals fin sched st (just (switch-st _ _))   = keeps-refl
takeDispatch-keeps nid vals fin sched st (just (exhaust-st _ _))  = keeps-refl

switchKill-keeps nothing  sched st = keeps-refl
switchKill-keeps (just v) sched st = keeps refl (λ s p → p)

thruWrap-keeps op nid false vs bs sched st = keeps-refl
thruWrap-keeps mergeᵒ nid true vs bs sched st with lookupNode nid (EvalSt.nodes st)
... | just (merge-st k _)      = keeps refl (λ s p → p)
... | just (scan-st _)         = keeps-refl
... | just (take-st _)         = keeps-refl
... | just (concat-st _ _ _)   = keeps-refl
... | just (switch-st _ _)     = keeps-refl
... | just (exhaust-st _ _)    = keeps-refl
... | nothing                  = keeps-refl
thruWrap-keeps concatᵒ nid true vs bs sched st with lookupNode nid (EvalSt.nodes st)
... | just (concat-st q act _) = keeps refl (λ s p → p)
... | just (scan-st _)         = keeps-refl
... | just (take-st _)         = keeps-refl
... | just (merge-st _ _)      = keeps-refl
... | just (switch-st _ _)     = keeps-refl
... | just (exhaust-st _ _)    = keeps-refl
... | nothing                  = keeps-refl
thruWrap-keeps switchᵒ nid true vs bs sched st with lookupNode nid (EvalSt.nodes st)
... | just (switch-st cur _)   = keeps refl (λ s p → p)
... | just (scan-st _)         = keeps-refl
... | just (take-st _)         = keeps-refl
... | just (merge-st _ _)      = keeps-refl
... | just (concat-st _ _ _)   = keeps-refl
... | just (exhaust-st _ _)    = keeps-refl
... | nothing                  = keeps-refl
thruWrap-keeps exhaustᵒ nid true vs bs sched st with lookupNode nid (EvalSt.nodes st)
... | just (exhaust-st act _)  = keeps refl (λ s p → p)
... | just (scan-st _)         = keeps-refl
... | just (take-st _)         = keeps-refl
... | just (merge-st _ _)      = keeps-refl
... | just (concat-st _ _ _)   = keeps-refl
... | just (switch-st _ _)     = keeps-refl
... | nothing                  = keeps-refl

------------------------------------------------------------------
-- the recursive members
------------------------------------------------------------------

subscribeInner-keeps g0 op allNid κ id now o sched st = keeps-refl
subscribeInner-keeps (gs fuel) op allNid κ id now o sched st =
  subscribeE-keeps fuel o (from-inner op allNid (Sched.nextNode sched) ↠ κ) id now
    (record sched { nextNode = suc (Sched.nextNode sched) }) st

thruConsume-keeps g mergeᵒ nid κ id now o sched st =
  subscribeInner-keeps g mergeᵒ nid κ id now o sched st
thruConsume-keeps {u = u} g concatᵒ nid κ id now o sched st
  with lookupNode nid (EvalSt.nodes st)
... | just (concat-st {w} q true od) with w ≟ᵗ u
...   | yes refl = keeps-refl
...   | no _     = keeps-refl
thruConsume-keeps {u = u} g concatᵒ nid κ id now o sched st
    | just (concat-st q false od) =
      subscribeInner-keeps g concatᵒ nid κ id now o sched st
thruConsume-keeps g concatᵒ nid κ id now o sched st | nothing = keeps-refl
thruConsume-keeps g concatᵒ nid κ id now o sched st | just (scan-st _) = keeps-refl
thruConsume-keeps g concatᵒ nid κ id now o sched st | just (take-st _) = keeps-refl
thruConsume-keeps g concatᵒ nid κ id now o sched st | just (merge-st _ _) = keeps-refl
thruConsume-keeps g concatᵒ nid κ id now o sched st | just (switch-st _ _) = keeps-refl
thruConsume-keeps g concatᵒ nid κ id now o sched st | just (exhaust-st _ _) = keeps-refl
thruConsume-keeps g switchᵒ nid κ id now o sched st
  with lookupNode nid (EvalSt.nodes st)
... | just (switch-st cur od) =
      keeps-trans (switchKill-keeps cur sched st)
                  (subscribeInner-keeps g switchᵒ nid κ id now o
                     (proj₁ (proj₂ (switchKill cur sched st)))
                     (proj₂ (proj₂ (switchKill cur sched st))))
... | just (scan-st _)       = keeps-refl
... | just (take-st _)       = keeps-refl
... | just (merge-st _ _)    = keeps-refl
... | just (concat-st _ _ _) = keeps-refl
... | just (exhaust-st _ _)  = keeps-refl
... | nothing                = keeps-refl
thruConsume-keeps g exhaustᵒ nid κ id now o sched st
  with lookupNode nid (EvalSt.nodes st)
... | just (exhaust-st true od)  = keeps-refl
... | just (exhaust-st false od) =
      subscribeInner-keeps g exhaustᵒ nid κ id now o sched st
... | just (scan-st _)       = keeps-refl
... | just (take-st _)       = keeps-refl
... | just (merge-st _ _)    = keeps-refl
... | just (concat-st _ _ _) = keeps-refl
... | just (switch-st _ _)   = keeps-refl
... | nothing                = keeps-refl

thruWalk-keeps g op nid κ id now [] sched st = keeps-refl
thruWalk-keeps g op nid κ id now (o ∷ os) sched st =
  keeps-trans (thruConsume-keeps g op nid κ id now o sched st)
    (thruWalk-keeps g op nid κ id now os
      (proj₁ (proj₂ (proj₂ (thruConsume g op nid κ id now o sched st))))
      (proj₂ (proj₂ (proj₂ (thruConsume g op nid κ id now o sched st)))))

concatDrain-keeps g allNid κ id now [] sched st = keeps-refl
concatDrain-keeps g allNid κ id now (o ∷ q) sched st
  with proj₁ (proj₂ (proj₂ (proj₂
        (subscribeInner g concatᵒ allNid κ id now o sched st))))
... | true =
      keeps-trans (subscribeInner-keeps g concatᵒ allNid κ id now o sched st)
        (concatDrain-keeps g allNid κ id now q
          (proj₁ (proj₂ (proj₂ (proj₂ (proj₂
            (subscribeInner g concatᵒ allNid κ id now o sched st))))))
          (proj₂ (proj₂ (proj₂ (proj₂ (proj₂
            (subscribeInner g concatᵒ allNid κ id now o sched st)))))))
... | false = subscribeInner-keeps g concatᵒ allNid κ id now o sched st

innerFinish-keeps g mergeᵒ  allNid inst κ id now vals sched st (just (merge-st k od))   = keeps refl (λ s p → p)
innerFinish-keeps g mergeᵒ  allNid inst κ id now vals sched st nothing                  = keeps-refl
innerFinish-keeps g mergeᵒ  allNid inst κ id now vals sched st (just (scan-st _))       = keeps-refl
innerFinish-keeps g mergeᵒ  allNid inst κ id now vals sched st (just (take-st _))       = keeps-refl
innerFinish-keeps g mergeᵒ  allNid inst κ id now vals sched st (just (concat-st _ _ _)) = keeps-refl
innerFinish-keeps g mergeᵒ  allNid inst κ id now vals sched st (just (switch-st _ _))   = keeps-refl
innerFinish-keeps g mergeᵒ  allNid inst κ id now vals sched st (just (exhaust-st _ _))  = keeps-refl
innerFinish-keeps {s = s} g concatᵒ allNid inst κ id now vals sched st
                  (just (concat-st {w} q act od)) with w ≟ᵗ s
... | yes refl = concatDrain-keeps g allNid κ id now q sched st
... | no _     = keeps-refl
innerFinish-keeps g concatᵒ allNid inst κ id now vals sched st nothing                = keeps-refl
innerFinish-keeps g concatᵒ allNid inst κ id now vals sched st (just (scan-st _))     = keeps-refl
innerFinish-keeps g concatᵒ allNid inst κ id now vals sched st (just (take-st _))     = keeps-refl
innerFinish-keeps g concatᵒ allNid inst κ id now vals sched st (just (merge-st _ _))  = keeps-refl
innerFinish-keeps g concatᵒ allNid inst κ id now vals sched st (just (switch-st _ _)) = keeps-refl
innerFinish-keeps g concatᵒ allNid inst κ id now vals sched st (just (exhaust-st _ _))= keeps-refl
innerFinish-keeps g switchᵒ allNid inst κ id now vals sched st (just (switch-st (just c) od))
  with c ≡ᵇ inst
... | true  = keeps refl (λ s p → p)
... | false = keeps-refl
innerFinish-keeps g switchᵒ allNid inst κ id now vals sched st (just (switch-st nothing od)) = keeps-refl
innerFinish-keeps g switchᵒ allNid inst κ id now vals sched st nothing                 = keeps-refl
innerFinish-keeps g switchᵒ allNid inst κ id now vals sched st (just (scan-st _))      = keeps-refl
innerFinish-keeps g switchᵒ allNid inst κ id now vals sched st (just (take-st _))      = keeps-refl
innerFinish-keeps g switchᵒ allNid inst κ id now vals sched st (just (merge-st _ _))   = keeps-refl
innerFinish-keeps g switchᵒ allNid inst κ id now vals sched st (just (concat-st _ _ _))= keeps-refl
innerFinish-keeps g switchᵒ allNid inst κ id now vals sched st (just (exhaust-st _ _)) = keeps-refl
innerFinish-keeps g exhaustᵒ allNid inst κ id now vals sched st (just (exhaust-st act od)) = keeps refl (λ s p → p)
innerFinish-keeps g exhaustᵒ allNid inst κ id now vals sched st nothing                 = keeps-refl
innerFinish-keeps g exhaustᵒ allNid inst κ id now vals sched st (just (scan-st _))      = keeps-refl
innerFinish-keeps g exhaustᵒ allNid inst κ id now vals sched st (just (take-st _))      = keeps-refl
innerFinish-keeps g exhaustᵒ allNid inst κ id now vals sched st (just (merge-st _ _))   = keeps-refl
innerFinish-keeps g exhaustᵒ allNid inst κ id now vals sched st (just (concat-st _ _ _))= keeps-refl
innerFinish-keeps g exhaustᵒ allNid inst κ id now vals sched st (just (switch-st _ _))  = keeps-refl

innerReact-keeps g op allNid inst κ id now vals sched st false = keeps-refl
innerReact-keeps g op allNid inst κ id now vals sched st true
  with any (aliveThroughᶠ inst st) (EvalSt.registry st)
... | true  = keeps-refl
... | false = innerFinish-keeps g op allNid inst κ id now vals sched st
                (lookupNode allNid (EvalSt.nodes st))

stepFrame-keeps g id now (map-f fn) κ vals fin sched st = keeps-refl
stepFrame-keeps {u = u} g id now (scan-f fn nid) κ vals fin sched st
  with lookupNode nid (EvalSt.nodes st)
... | just (scan-st {w} sacc) with w ≟ᵗ u
...   | yes refl = keeps refl (λ s p → p)
...   | no _     = keeps-refl
stepFrame-keeps g id now (scan-f fn nid) κ vals fin sched st | nothing = keeps-refl
stepFrame-keeps g id now (scan-f fn nid) κ vals fin sched st | just (take-st _) = keeps-refl
stepFrame-keeps g id now (scan-f fn nid) κ vals fin sched st | just (merge-st _ _) = keeps-refl
stepFrame-keeps g id now (scan-f fn nid) κ vals fin sched st | just (concat-st _ _ _) = keeps-refl
stepFrame-keeps g id now (scan-f fn nid) κ vals fin sched st | just (switch-st _ _) = keeps-refl
stepFrame-keeps g id now (scan-f fn nid) κ vals fin sched st | just (exhaust-st _ _) = keeps-refl
stepFrame-keeps g id now (take-f nid) κ vals fin sched st =
  takeDispatch-keeps nid vals fin sched st (lookupNode nid (EvalSt.nodes st))
stepFrame-keeps g id now (from-inner op allNid inst) κ vals fin sched st =
  innerReact-keeps g op allNid inst κ id now vals sched st fin
stepFrame-keeps g id now (thru-outer op nid) κ vals fin sched st =
  keeps-trans (thruWalk-keeps g op nid κ id now vals sched st)
    (thruWrap-keeps op nid fin
      (proj₁ (thruWalk g op nid κ id now vals sched st))
      (proj₁ (proj₂ (thruWalk g op nid κ id now vals sched st)))
      (proj₁ (proj₂ (proj₂ (thruWalk g op nid κ id now vals sched st))))
      (proj₂ (proj₂ (proj₂ (thruWalk g op nid κ id now vals sched st)))))

pushBurst-keeps g id now f κ [] sched st = keeps-refl
pushBurst-keeps g id now f κ (em ∷ ems) sched st =
  keeps-trans
    (stepFrame-keeps g id now f κ (proj₁ sp) (proj₂ (proj₂ sp)) sched st)
    (pushBurst-keeps g id now f κ ems
       (proj₁ (proj₂ (proj₂ (proj₂ SF))))
       (proj₂ (proj₂ (proj₂ (proj₂ SF)))))
  where
  sp = splitEvents (InstEmit.events em)
  SF = stepFrame g id now f κ (proj₁ sp) (proj₂ (proj₂ sp)) sched st

subscribeAll-keeps g op ns b κ id now sched st =
  keeps-trans
    (subscribeE-keeps g b (thru-outer op (Sched.nextNode sched) ↠ κ) id now
       (record sched { nextNode = suc (Sched.nextNode sched) })
       (installNode (Sched.nextNode sched) ns st))
    (pushBurst-keeps g id now (thru-outer op (Sched.nextNode sched)) κ
       (proj₁ SE) (proj₁ (proj₂ SE)) (proj₂ (proj₂ SE)))
  where
  SE = subscribeE g b (thru-outer op (Sched.nextNode sched) ↠ κ) id now
         (record sched { nextNode = suc (Sched.nextNode sched) })
         (installNode (Sched.nextNode sched) ns st)

-- the connect's payment, hoisted out of the burstCompleted split: both
-- exits return sched₁ and a state whose connectedShares is st₂'s, so the
-- branch is cosmetic and the proof is shared
sharedConnect-core fuel i d κ id now sched st =
  keeps (slotsEq K0)
        (λ s p → connMono K0 s
                   (member-cons s (toℕ i) (EvalSt.connectedShares st) p))
  where
  K0 = subscribeE-keeps fuel d (share-sink i) id now sched
         (register (toℕ i) κ
           (record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st }))

sharedConnect-keeps g0 i d κ id now sched st = keeps-refl
sharedConnect-keeps (gs fuel) i d κ id now sched st
  with burstCompleted (proj₁ (subscribeE fuel d (share-sink i) id now sched
         (register (toℕ i) κ
           (record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st }))))
... | true  = sharedConnect-core fuel i d κ id now sched st
... | false = sharedConnect-core fuel i d κ id now sched st

sharedSlot-keeps g i d κ id now sched st
  with memberSource (toℕ i) (EvalSt.completedSources st)
... | true  = keeps-refl
... | false with memberSource (toℕ i) (EvalSt.connectedShares st)
...   | true  = keeps-refl
...   | false = sharedConnect-keeps g i d κ id now sched st

subscribeE-keeps {Γ = Γ} g (input i) κ id now sched st with Sched.slots sched i
... | shared d = sharedSlot-keeps g i d κ id now sched st
... | scripted (hot _) with memberSource (toℕ i) (EvalSt.completedSources st)
...   | true  = keeps-refl
...   | false = keeps-refl
subscribeE-keeps g (input i) κ id now sched st | scripted (cold sync [])       = keeps-refl
subscribeE-keeps g (input i) κ id now sched st | scripted (cold sync (x ∷ xs)) = keeps-refl
subscribeE-keeps g (ofᵉ ts)  κ id now sched st = keeps-refl
subscribeE-keeps g emptyᵉ    κ id now sched st = keeps-refl
subscribeE-keeps g (mapᵉ f b) κ id now sched st =
  keeps-trans (subscribeE-keeps g b (map-f f ↠ κ) id now sched st)
    (pushBurst-keeps g id now (map-f f) κ
      (proj₁ SE) (proj₁ (proj₂ SE)) (proj₂ (proj₂ SE)))
  where SE = subscribeE g b (map-f f ↠ κ) id now sched st
subscribeE-keeps g (takeᵉ count b) κ id now sched st with evalTm count
... | zero  = keeps-refl
... | suc k =
      keeps-trans (subscribeE-keeps g b (take-f (Sched.nextNode sched) ↠ κ) id now
                    (record sched { nextNode = suc (Sched.nextNode sched) })
                    (installNode (Sched.nextNode sched) (take-st (suc k)) st))
        (pushBurst-keeps g id now (take-f (Sched.nextNode sched)) κ
          (proj₁ SE) (proj₁ (proj₂ SE)) (proj₂ (proj₂ SE)))
      where SE = subscribeE g b (take-f (Sched.nextNode sched) ↠ κ) id now
                   (record sched { nextNode = suc (Sched.nextNode sched) })
                   (installNode (Sched.nextNode sched) (take-st (suc k)) st)
subscribeE-keeps g (scanᵉ f z b) κ id now sched st =
  keeps-trans (subscribeE-keeps g b (scan-f f (Sched.nextNode sched) ↠ κ) id now
                (record sched { nextNode = suc (Sched.nextNode sched) })
                (installNode (Sched.nextNode sched) (scan-st (evalTm z)) st))
    (pushBurst-keeps g id now (scan-f f (Sched.nextNode sched)) κ
      (proj₁ SE) (proj₁ (proj₂ SE)) (proj₂ (proj₂ SE)))
  where SE = subscribeE g b (scan-f f (Sched.nextNode sched) ↠ κ) id now
               (record sched { nextNode = suc (Sched.nextNode sched) })
               (installNode (Sched.nextNode sched) (scan-st (evalTm z)) st)
subscribeE-keeps g (mergeAllᵉ b) κ id now sched st =
  subscribeAll-keeps g mergeᵒ (merge-st 0 false) b κ id now sched st
subscribeE-keeps {u = u} g (concatAllᵉ b) κ id now sched st =
  subscribeAll-keeps g concatᵒ (concat-st {t = u} [] false false) b κ id now sched st
subscribeE-keeps g (switchAllᵉ b) κ id now sched st =
  subscribeAll-keeps g switchᵒ (switch-st nothing false) b κ id now sched st
subscribeE-keeps g (exhaustAllᵉ b) κ id now sched st =
  subscribeAll-keeps g exhaustᵒ (exhaust-st false false) b κ id now sched st
subscribeE-keeps g0 (μᵉ body) κ id now sched st = keeps-refl
subscribeE-keeps (gs fuel) (μᵉ body) κ id now sched st =
  subscribeE-keeps fuel (unfoldμ body) κ id now sched st
subscribeE-keeps g (varᵉ ()) κ id now sched st
subscribeE-keeps g (deferᵉ body) κ id now sched st = keeps-refl

------------------------------------------------------------------
-- the two faces

subscribeE-slots : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots (proj₁ (proj₂ (subscribeE g b κ id now sched st)))
    ≡ Sched.slots sched
subscribeE-slots g b κ id now sched st =
  slotsEq (subscribeE-keeps g b κ id now sched st)

subscribeE-connected-mono : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) (s : Source) →
  memberSource s (EvalSt.connectedShares st) ≡ true →
  memberSource s
    (EvalSt.connectedShares (proj₂ (proj₂ (subscribeE g b κ id now sched st))))
    ≡ true
subscribeE-connected-mono g b κ id now sched st s =
  connMono (subscribeE-keeps g b κ id now sched st) s

-- THE SHARE BOUNDARY'S PAYMENT, assembled.  sharedConnect adds i to
-- connectedShares before walking the def, so unconn-insert's strict drop is
-- taken at the connect itself; subscribeE-slots keeps the telescope fixed and
-- subscribeE-connected-mono keeps i connected, so unconn-antitone carries the
-- drop across everything the def does on its way up.  Both exit branches
-- return sched₁ and a state whose connectedShares is st₂'s (the completed
-- branch rewrites registry and completedSources only), so the split is
-- cosmetic.  This is the `hop-anchored` disjunct's payment obligation.
-- the drop, on the pieces sharedConnect threads (one clause, so the where
-- block is visible; the burstCompleted split above it is cosmetic)
sharedConnect-drop : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (fuel : Gas) (i : Fin n) (d : Closed Γ (lookup Γ i))
  (κ : Path Γ (lookup Γ i) t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) {dd : Closed Γ (lookup Γ i)} →
  Sched.slots sched i ≡ shared dd →
  memberSource (toℕ i) (EvalSt.connectedShares st) ≡ false →
  unconn (Sched.slots (proj₁ (proj₂ (subscribeE fuel d (share-sink i) id now sched
            (register (toℕ i) κ (record st
              { connectedShares = toℕ i ∷ EvalSt.connectedShares st }))))))
         (EvalSt.connectedShares (proj₂ (proj₂ (subscribeE fuel d (share-sink i) id now sched
            (register (toℕ i) κ (record st
              { connectedShares = toℕ i ∷ EvalSt.connectedShares st }))))))
  < unconn (Sched.slots sched) (EvalSt.connectedShares st)
sharedConnect-drop fuel i d κ id now sched st eqi fresh
  rewrite subscribeE-slots fuel d (share-sink i) id now sched
            (register (toℕ i) κ (record st
              { connectedShares = toℕ i ∷ EvalSt.connectedShares st }))
  = ≤-trans (s≤s step≤) step<
  where
  st₁ = register (toℕ i) κ
          (record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st })
  st₂ = proj₂ (proj₂ (subscribeE fuel d (share-sink i) id now sched st₁))
  -- i stays connected through the def's walk
  kept : ∀ s → memberSource s (toℕ i ∷ EvalSt.connectedShares st) ≡ true →
               memberSource s (EvalSt.connectedShares st₂) ≡ true
  kept s h = subscribeE-connected-mono fuel d (share-sink i) id now sched st₁ s h
  step≤ : unconn (Sched.slots sched) (EvalSt.connectedShares st₂)
        ≤ unconn (Sched.slots sched) (toℕ i ∷ EvalSt.connectedShares st)
  step≤ = unconn-antitone (Sched.slots sched)
            (toℕ i ∷ EvalSt.connectedShares st) (EvalSt.connectedShares st₂) kept
  step< : unconn (Sched.slots sched) (toℕ i ∷ EvalSt.connectedShares st)
        < unconn (Sched.slots sched) (EvalSt.connectedShares st)
  step< = unconn-insert (Sched.slots sched) (EvalSt.connectedShares st) i eqi fresh

-- and the same drop read off sharedConnect's own result: both exit branches
-- return sched₁ and a state whose connectedShares is st₂'s (the completed
-- branch rewrites registry and completedSources only)
sharedConnect-unconn : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (fuel : Gas) (i : Fin n) (d : Closed Γ (lookup Γ i))
  (κ : Path Γ (lookup Γ i) t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) {dd : Closed Γ (lookup Γ i)} →
  Sched.slots sched i ≡ shared dd →
  memberSource (toℕ i) (EvalSt.connectedShares st) ≡ false →
  unconn (Sched.slots (proj₁ (proj₂ (sharedConnect (gs fuel) i d κ id now sched st))))
         (EvalSt.connectedShares
           (proj₂ (proj₂ (sharedConnect (gs fuel) i d κ id now sched st))))
  < unconn (Sched.slots sched) (EvalSt.connectedShares st)
sharedConnect-unconn fuel i d κ id now sched st eqi fresh
  with burstCompleted (proj₁ (subscribeE fuel d (share-sink i) id now sched
         (register (toℕ i) κ
           (record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st }))))
... | true  = sharedConnect-drop fuel i d κ id now sched st eqi fresh
... | false = sharedConnect-drop fuel i d κ id now sched st eqi fresh


------------------------------------------------------------------
-- the walk contracts, store half — the SHAPE the clause grind
-- threads (receipts E′ ≤ E · spendᴱ … attach with the cost
-- instrumentation; the landing stays in the cores below).  Stated
-- against the frozen instant base W and a ledger position E ≥ 3.
------------------------------------------------------------------

-- the node-install ring's fnCap face (mirror of setNode-bounded /
-- install-bounded: setNode either replaces the hit key or recurses
-- past a survivor, and the live half is untouched)
setNode-fnCap : ∀ {n} {Γ : Ctx n} (Ψ : ℕ) (nid : NodeId) (ns : NodeState Γ)
  (nodes : List (NodeId × NodeState Γ)) →
  fnCapNode Ψ ns ≡ true →
  all (λ kv → fnCapNode Ψ (proj₂ kv)) nodes ≡ true →
  all (λ kv → fnCapNode Ψ (proj₂ kv)) (setNode nid ns nodes) ≡ true
setNode-fnCap Ψ nid ns []             bn h = ∧-intro bn refl
setNode-fnCap Ψ nid ns ((k , s′) ∷ r) bn h with k ≡ᵇ nid
... | true  = ∧-intro bn (proj₂ (∧-true _ _ h))
... | false = ∧-intro (proj₁ (∧-true _ _ h))
                      (setNode-fnCap Ψ nid ns r bn (proj₂ (∧-true _ _ h)))

install-fnCap : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ψ : ℕ)
  (sched : Sched Γ) (st : EvalSt e) (nid : NodeId) (ns : NodeState Γ) →
  fnCapNode Ψ ns ≡ true → fnCapBounded? Ψ sched st ≡ true →
  fnCapBounded? Ψ sched (installNode nid ns st) ≡ true
install-fnCap Ψ sched st nid ns bn h =
  ∧-intro (proj₁ (∧-true _ _ h))
          (setNode-fnCap Ψ nid ns (EvalSt.nodes st) bn (proj₂ (∧-true _ _ h)))


lift1 : ∀ {M} → 1 ≤ M → 1 ≤ 1 * M
lift1 {M} h = ≤-trans h (≤-reflexive (sym (+-identityʳ M)))

-- subst on the Δ-index of Exp is transparent to sizeᵉ
size-substᴱ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Δ′ Θ t} (p : Δ ≡ Δ′) (e : Exp Γ Δᵍ Δ Θ t) →
  sizeᵉ (subst (λ ζ → Exp Γ Δᵍ ζ Θ t) p e) ≡ sizeᵉ e
size-substᴱ refl e = refl

-- elimination copies the closure at ≤ one var position per node, so
-- size grows by at most the closure's own size.  Same sucmul/sum
-- skeleton as size-subΘᵉ; only elimD's hit clause plants the copy.
mutual
  size-elimGᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
    (cl : Closed Γ t) (e : Exp Γ Δᵍ Δ Θ u) →
    sizeᵉ (elimGExp x cl e) ≤ sizeᵉ e * sizeᵉ cl
  size-elimGᵉ x cl (input i)       = lift1 (sizeᵉ-pos cl)
  size-elimGᵉ x cl (ofᵉ ts)        =
    sucmul (sizeᵗˢ ts) (sizeᵉ cl) (size-elimGᵗˢ x cl ts) (sizeᵉ-pos cl)
  size-elimGᵉ x cl emptyᵉ          = lift1 (sizeᵉ-pos cl)
  size-elimGᵉ x cl (mapᵉ f e)      =
    sucmul (sizeᵗ f + sizeᵉ e) (sizeᵉ cl)
      (sum2 (sizeᵗ f) (sizeᵉ e) (sizeᵉ cl)
            (size-elimGᵗ x cl f) (size-elimGᵉ x cl e))
      (sizeᵉ-pos cl)
  size-elimGᵉ x cl (takeᵉ c e)     =
    sucmul (sizeᵗ c + sizeᵉ e) (sizeᵉ cl)
      (sum2 (sizeᵗ c) (sizeᵉ e) (sizeᵉ cl)
            (size-elimGᵗ x cl c) (size-elimGᵉ x cl e))
      (sizeᵉ-pos cl)
  size-elimGᵉ x cl (scanᵉ f z e)   =
    sucmul ((sizeᵗ f + sizeᵗ z) + sizeᵉ e) (sizeᵉ cl)
      (sum3 (sizeᵗ f) (sizeᵗ z) (sizeᵉ e) (sizeᵉ cl)
            (size-elimGᵗ x cl f) (size-elimGᵗ x cl z) (size-elimGᵉ x cl e))
      (sizeᵉ-pos cl)
  size-elimGᵉ x cl (mergeAllᵉ e)   =
    sucmul (sizeᵉ e) (sizeᵉ cl) (size-elimGᵉ x cl e) (sizeᵉ-pos cl)
  size-elimGᵉ x cl (concatAllᵉ e)  =
    sucmul (sizeᵉ e) (sizeᵉ cl) (size-elimGᵉ x cl e) (sizeᵉ-pos cl)
  size-elimGᵉ x cl (switchAllᵉ e)  =
    sucmul (sizeᵉ e) (sizeᵉ cl) (size-elimGᵉ x cl e) (sizeᵉ-pos cl)
  size-elimGᵉ x cl (exhaustAllᵉ e) =
    sucmul (sizeᵉ e) (sizeᵉ cl) (size-elimGᵉ x cl e) (sizeᵉ-pos cl)
  size-elimGᵉ x cl (μᵉ e)          =
    sucmul (sizeᵉ e) (sizeᵉ cl) (size-elimGᵉ (there x) cl e) (sizeᵉ-pos cl)
  size-elimGᵉ x cl (varᵉ y)        = lift1 (sizeᵉ-pos cl)
  size-elimGᵉ x cl (deferᵉ e)      =
    sucmul (sizeᵉ e) (sizeᵉ cl)
      (≤-trans (≤-reflexive (size-substᴱ (⊟-++ˡ x) (elimDExp (∈-++⁺ˡ x) cl e)))
               (size-elimDᵉ (∈-++⁺ˡ x) cl e))
      (sizeᵉ-pos cl)

  size-elimDᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δ)
    (cl : Closed Γ t) (e : Exp Γ Δᵍ Δ Θ u) →
    sizeᵉ (elimDExp x cl e) ≤ sizeᵉ e * sizeᵉ cl
  size-elimDᵉ x cl (input i)       = lift1 (sizeᵉ-pos cl)
  size-elimDᵉ x cl (ofᵉ ts)        =
    sucmul (sizeᵗˢ ts) (sizeᵉ cl) (size-elimDᵗˢ x cl ts) (sizeᵉ-pos cl)
  size-elimDᵉ x cl emptyᵉ          = lift1 (sizeᵉ-pos cl)
  size-elimDᵉ x cl (mapᵉ f e)      =
    sucmul (sizeᵗ f + sizeᵉ e) (sizeᵉ cl)
      (sum2 (sizeᵗ f) (sizeᵉ e) (sizeᵉ cl)
            (size-elimDᵗ x cl f) (size-elimDᵉ x cl e))
      (sizeᵉ-pos cl)
  size-elimDᵉ x cl (takeᵉ c e)     =
    sucmul (sizeᵗ c + sizeᵉ e) (sizeᵉ cl)
      (sum2 (sizeᵗ c) (sizeᵉ e) (sizeᵉ cl)
            (size-elimDᵗ x cl c) (size-elimDᵉ x cl e))
      (sizeᵉ-pos cl)
  size-elimDᵉ x cl (scanᵉ f z e)   =
    sucmul ((sizeᵗ f + sizeᵗ z) + sizeᵉ e) (sizeᵉ cl)
      (sum3 (sizeᵗ f) (sizeᵗ z) (sizeᵉ e) (sizeᵉ cl)
            (size-elimDᵗ x cl f) (size-elimDᵗ x cl z) (size-elimDᵉ x cl e))
      (sizeᵉ-pos cl)
  size-elimDᵉ x cl (mergeAllᵉ e)   =
    sucmul (sizeᵉ e) (sizeᵉ cl) (size-elimDᵉ x cl e) (sizeᵉ-pos cl)
  size-elimDᵉ x cl (concatAllᵉ e)  =
    sucmul (sizeᵉ e) (sizeᵉ cl) (size-elimDᵉ x cl e) (sizeᵉ-pos cl)
  size-elimDᵉ x cl (switchAllᵉ e)  =
    sucmul (sizeᵉ e) (sizeᵉ cl) (size-elimDᵉ x cl e) (sizeᵉ-pos cl)
  size-elimDᵉ x cl (exhaustAllᵉ e) =
    sucmul (sizeᵉ e) (sizeᵉ cl) (size-elimDᵉ x cl e) (sizeᵉ-pos cl)
  size-elimDᵉ x cl (μᵉ e)          =
    sucmul (sizeᵉ e) (sizeᵉ cl) (size-elimDᵉ x cl e) (sizeᵉ-pos cl)
  size-elimDᵉ x cl (varᵉ y)        with compare∈ x y
  ... | inj₁ refl =
    ≤-trans (≤-reflexive (size-renᵉ (λ ()) (λ ()) (λ ()) cl))
            (≤-reflexive (sym (+-identityʳ (sizeᵉ cl))))
  ... | inj₂ y′   = lift1 (sizeᵉ-pos cl)
  size-elimDᵉ x cl (deferᵉ e)      =
    sucmul (sizeᵉ e) (sizeᵉ cl)
      (≤-trans (≤-reflexive (size-substᴱ (⊟-++ʳ x) (elimDExp (∈-++⁺ʳ _ x) cl e)))
               (size-elimDᵉ (∈-++⁺ʳ _ x) cl e))
      (sizeᵉ-pos cl)

  size-elimGᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
    (cl : Closed Γ t) (tm : Tm Γ Δᵍ Δ Θ u) →
    sizeᵗ (elimGTm x cl tm) ≤ sizeᵗ tm * sizeᵉ cl
  size-elimGᵗ x cl (varᵗ y)      = lift1 (sizeᵉ-pos cl)
  size-elimGᵗ x cl unit̂          = lift1 (sizeᵉ-pos cl)
  size-elimGᵗ x cl (bool̂ _)      = lift1 (sizeᵉ-pos cl)
  size-elimGᵗ x cl (nat̂ _)       = lift1 (sizeᵉ-pos cl)
  size-elimGᵗ x cl (pairᵗ a b)   =
    sucmul (sizeᵗ a + sizeᵗ b) (sizeᵉ cl)
      (sum2 (sizeᵗ a) (sizeᵗ b) (sizeᵉ cl)
            (size-elimGᵗ x cl a) (size-elimGᵗ x cl b))
      (sizeᵉ-pos cl)
  size-elimGᵗ x cl (fstᵗ p)      =
    sucmul (sizeᵗ p) (sizeᵉ cl) (size-elimGᵗ x cl p) (sizeᵉ-pos cl)
  size-elimGᵗ x cl (sndᵗ p)      =
    sucmul (sizeᵗ p) (sizeᵉ cl) (size-elimGᵗ x cl p) (sizeᵉ-pos cl)
  size-elimGᵗ x cl (inlᵗ a)      =
    sucmul (sizeᵗ a) (sizeᵉ cl) (size-elimGᵗ x cl a) (sizeᵉ-pos cl)
  size-elimGᵗ x cl (inrᵗ a)      =
    sucmul (sizeᵗ a) (sizeᵉ cl) (size-elimGᵗ x cl a) (sizeᵉ-pos cl)
  size-elimGᵗ x cl (caseᵗ s l r) =
    sucmul ((sizeᵗ s + sizeᵗ l) + sizeᵗ r) (sizeᵉ cl)
      (sum3 (sizeᵗ s) (sizeᵗ l) (sizeᵗ r) (sizeᵉ cl)
            (size-elimGᵗ x cl s) (size-elimGᵗ x cl l) (size-elimGᵗ x cl r))
      (sizeᵉ-pos cl)
  size-elimGᵗ x cl (ifᵗ c a b)   =
    sucmul ((sizeᵗ c + sizeᵗ a) + sizeᵗ b) (sizeᵉ cl)
      (sum3 (sizeᵗ c) (sizeᵗ a) (sizeᵗ b) (sizeᵉ cl)
            (size-elimGᵗ x cl c) (size-elimGᵗ x cl a) (size-elimGᵗ x cl b))
      (sizeᵉ-pos cl)
  size-elimGᵗ x cl (primᵗ _ a)   =
    sucmul (sizeᵗ a) (sizeᵉ cl) (size-elimGᵗ x cl a) (sizeᵉ-pos cl)
  size-elimGᵗ x cl (strmᵗ e)     =
    sucmul (sizeᵉ e) (sizeᵉ cl) (size-elimGᵉ x cl e) (sizeᵉ-pos cl)

  size-elimDᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δ)
    (cl : Closed Γ t) (tm : Tm Γ Δᵍ Δ Θ u) →
    sizeᵗ (elimDTm x cl tm) ≤ sizeᵗ tm * sizeᵉ cl
  size-elimDᵗ x cl (varᵗ y)      = lift1 (sizeᵉ-pos cl)
  size-elimDᵗ x cl unit̂          = lift1 (sizeᵉ-pos cl)
  size-elimDᵗ x cl (bool̂ _)      = lift1 (sizeᵉ-pos cl)
  size-elimDᵗ x cl (nat̂ _)       = lift1 (sizeᵉ-pos cl)
  size-elimDᵗ x cl (pairᵗ a b)   =
    sucmul (sizeᵗ a + sizeᵗ b) (sizeᵉ cl)
      (sum2 (sizeᵗ a) (sizeᵗ b) (sizeᵉ cl)
            (size-elimDᵗ x cl a) (size-elimDᵗ x cl b))
      (sizeᵉ-pos cl)
  size-elimDᵗ x cl (fstᵗ p)      =
    sucmul (sizeᵗ p) (sizeᵉ cl) (size-elimDᵗ x cl p) (sizeᵉ-pos cl)
  size-elimDᵗ x cl (sndᵗ p)      =
    sucmul (sizeᵗ p) (sizeᵉ cl) (size-elimDᵗ x cl p) (sizeᵉ-pos cl)
  size-elimDᵗ x cl (inlᵗ a)      =
    sucmul (sizeᵗ a) (sizeᵉ cl) (size-elimDᵗ x cl a) (sizeᵉ-pos cl)
  size-elimDᵗ x cl (inrᵗ a)      =
    sucmul (sizeᵗ a) (sizeᵉ cl) (size-elimDᵗ x cl a) (sizeᵉ-pos cl)
  size-elimDᵗ x cl (caseᵗ s l r) =
    sucmul ((sizeᵗ s + sizeᵗ l) + sizeᵗ r) (sizeᵉ cl)
      (sum3 (sizeᵗ s) (sizeᵗ l) (sizeᵗ r) (sizeᵉ cl)
            (size-elimDᵗ x cl s) (size-elimDᵗ x cl l) (size-elimDᵗ x cl r))
      (sizeᵉ-pos cl)
  size-elimDᵗ x cl (ifᵗ c a b)   =
    sucmul ((sizeᵗ c + sizeᵗ a) + sizeᵗ b) (sizeᵉ cl)
      (sum3 (sizeᵗ c) (sizeᵗ a) (sizeᵗ b) (sizeᵉ cl)
            (size-elimDᵗ x cl c) (size-elimDᵗ x cl a) (size-elimDᵗ x cl b))
      (sizeᵉ-pos cl)
  size-elimDᵗ x cl (primᵗ _ a)   =
    sucmul (sizeᵗ a) (sizeᵉ cl) (size-elimDᵗ x cl a) (sizeᵉ-pos cl)
  size-elimDᵗ x cl (strmᵗ e)     =
    sucmul (sizeᵉ e) (sizeᵉ cl) (size-elimDᵉ x cl e) (sizeᵉ-pos cl)

  size-elimGᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
    (cl : Closed Γ t) (ts : List (Tm Γ Δᵍ Δ Θ u)) →
    sizeᵗˢ (elimGTms x cl ts) ≤ sizeᵗˢ ts * sizeᵉ cl
  size-elimGᵗˢ x cl []       = lift1 (sizeᵉ-pos cl)
  size-elimGᵗˢ x cl (y ∷ ys) =
    sum2 (sizeᵗ y) (sizeᵗˢ ys) (sizeᵉ cl)
         (size-elimGᵗ x cl y) (size-elimGᵗˢ x cl ys)

  size-elimDᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δ)
    (cl : Closed Γ t) (ts : List (Tm Γ Δᵍ Δ Θ u)) →
    sizeᵗˢ (elimDTms x cl ts) ≤ sizeᵗˢ ts * sizeᵉ cl
  size-elimDᵗˢ x cl []       = lift1 (sizeᵉ-pos cl)
  size-elimDᵗˢ x cl (y ∷ ys) =
    sum2 (sizeᵗ y) (sizeᵗˢ ys) (sizeᵉ cl)
         (size-elimDᵗ x cl y) (size-elimDᵗˢ x cl ys)

-- the μ-copy size bound: unfolding plants (μᵉ body) at the body's
-- global-var positions, so the copy is at most sizeᵉ (μᵉ body) squared
size-unfoldμ : ∀ {n} {Γ : Ctx n} {t} (body : Exp Γ (t ∷ []) [] [] t) →
  sizeᵉ (unfoldμ body) ≤ sizeᵉ (μᵉ body) * sizeᵉ (μᵉ body)
size-unfoldμ body =
  ≤-trans (size-elimGᵉ (here refl) (μᵉ body) body)
          (*-monoˡ-≤ (sizeᵉ (μᵉ body)) (n≤1+n (sizeᵉ body)))


------------------------------------------------------------------
-- THE LEDGER RULE, PROVEN — memo (2)'s one uniform step: an eval
-- edge at position E ≥ 2 lands within E · 3^(suc Ψ).  This is the
-- design's load-bearing arithmetic, machine-checked: grow-pow
-- re-bases the grown store, the exponents collapse by
-- ^-*-assoc/^-distrib, and ledger-step is the ℕ inequality
-- E + (E+2)·3^w ≤ E·3^(suc Ψ).
------------------------------------------------------------------

ledger-step : ∀ (E w Ψ : ℕ) → 2 ≤ E → w ≤ Ψ →
  E + (E + 2) * 3 ^ w ≤ E * 3 ^ suc Ψ
ledger-step E w Ψ 2≤E w≤Ψ =
  ≤-trans (+-mono-≤ E≤E3w (*-monoˡ-≤ (3 ^ w) E+2≤2E))
  (≤-trans (≤-reflexive shuffle)
           (*-monoʳ-≤ E (^-monoʳ-≤ 3 (s≤s w≤Ψ))))
  where
  E+2≤2E : E + 2 ≤ 2 * E
  E+2≤2E = ≤-trans (+-monoʳ-≤ E 2≤E)
                   (≤-reflexive (cong (E +_) (sym (+-identityʳ E))))
  E≤E3w : E ≤ E * 3 ^ w
  E≤E3w = ≤-trans (≤-reflexive (sym (*-identityʳ E)))
                  (*-monoʳ-≤ E (one≤3^ w))
  shuffle : E * 3 ^ w + 2 * E * 3 ^ w ≡ E * (3 * 3 ^ w)
  shuffle = solve 2
    (λ e x → e :* x :+ con 2 :* e :* x := e :* (con 3 :* x)) refl
    E (3 ^ w)

-- one eval edge, end to end: everything within the current cap in,
-- result within the cap at E · 3^(suc Ψ) out
evalStep-cap : ∀ {n} {Γ : Ctx n} {s t} (Ψ W E : ℕ)
  (fn : Fn Γ [] [] [] s t) (v : Val Γ s) →
  2 ≤ E → caseWᵗ fn ≤ Ψ →
  sizeᵗ fn ≤ capᴱ W E → sizeᵛ s v ≤ capᴱ W E →
  sizeᵛ t (applyFn fn v) ≤ capᴱ W (E * 3 ^ suc Ψ)
evalStep-cap Ψ W E fn v 2≤E w≤Ψ hf hv =
  ≤-trans (applyFn-sharp (capᴱ W E) fn v hv hf)
  (≤-trans (*-mono-≤ hf (^-monoˡ-≤ (3 ^ caseWᵗ fn) (grow-pow W E)))
  (≤-trans (≤-reflexive collapse)
           (capᴱ-mono W (ledger-step E (caseWᵗ fn) Ψ 2≤E w≤Ψ))))
  where
  collapse : capᴱ W E * ((2 + 2 * W) ^ (E + 2)) ^ (3 ^ caseWᵗ fn)
           ≡ capᴱ W (E + (E + 2) * 3 ^ caseWᵗ fn)
  collapse =
    trans (cong (capᴱ W E *_)
            (^-*-assoc (2 + 2 * W) (E + 2) (3 ^ caseWᵗ fn)))
          (sym (^-distribˡ-+-* (2 + 2 * W) E ((E + 2) * 3 ^ caseWᵗ fn)))

-- the fn-cap face of one eval edge
applyFn-fnCap : ∀ {n} {Γ : Ctx n} {s t} (Ψ : ℕ)
  (fn : Fn Γ [] [] [] s t) (v : Val Γ s) →
  fnCapᵛ s v ≤ Ψ → caseWᵗ fn ⊔ fnCapᵗ fn ≤ Ψ →
  fnCapᵛ t (applyFn fn v) ≤ Ψ
applyFn-fnCap Ψ fn v hv hfn = fnCap-evalWith Ψ fn (v ∷ᵃ []ᵃ) (hv , tt) hfn

-- the closed-eval face of the ledger rule (of-elements, scan seeds,
-- take counts): same collapse as evalStep-cap over the empty env
evalTm-cap : ∀ {n} {Γ : Ctx n} {t} (Ψ W E : ℕ) (tm : Tm Γ [] [] [] t) →
  2 ≤ E → caseWᵗ tm ≤ Ψ → sizeᵗ tm ≤ capᴱ W E →
  sizeᵛ t (evalTm tm) ≤ capᴱ W (E * 3 ^ suc Ψ)
evalTm-cap Ψ W E tm 2≤E w≤Ψ hsz =
  ≤-trans (evalWith-sharp (capᴱ W E) tm []ᵃ tt hsz)
  (≤-trans (*-mono-≤ hsz (^-monoˡ-≤ (3 ^ caseWᵗ tm) (grow-pow W E)))
  (≤-trans (≤-reflexive collapse)
           (capᴱ-mono W (ledger-step E (caseWᵗ tm) Ψ 2≤E w≤Ψ))))
  where
  collapse : capᴱ W E * ((2 + 2 * W) ^ (E + 2)) ^ (3 ^ caseWᵗ tm)
           ≡ capᴱ W (E + (E + 2) * 3 ^ caseWᵗ tm)
  collapse =
    trans (cong (capᴱ W E *_)
            (^-*-assoc (2 + 2 * W) (E + 2) (3 ^ caseWᵗ tm)))
          (sym (^-distribˡ-+-* (2 + 2 * W) E ((E + 2) * 3 ^ caseWᵗ tm)))

2≤capᴱ : ∀ (W : ℕ) {E : ℕ} → 1 ≤ E → 2 ≤ capᴱ W E
2≤capᴱ W h = ≤-trans (2≤C W) (pow1 W h)

capᴱ-square : ∀ (W E : ℕ) → capᴱ W (2 * E) ≡ capᴱ W E * capᴱ W E
capᴱ-square W E =
  trans (cong ((2 + 2 * W) ^_) (cong (E +_) (+-identityʳ E)))
        (^-distribˡ-+-* (2 + 2 * W) E E)

-- the invariant only ever needs widening upward in B (Ψ is fixed):
-- proven legs (stBounded-widen, ≤ᵇ-widen) + the regsB? leg (W7)
INV?-widen : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {Ψ B B′ : ℕ}
  (sched : Sched Γ) (st : EvalSt e) → B ≤ B′ →
  INV? Ψ B sched st ≡ true → INV? Ψ B′ sched st ≡ true
INV?-widen {Ψ = Ψ} {B} {B′} sched st le inv
  with ∧-true (stBounded? B sched st) _ inv
... | sb , r1 with ∧-true (fnCapBounded? Ψ sched st) _ r1
... | fc , r2 with ∧-true (length (EvalSt.registry st) ≤ᵇ B) _ r2
... | rl , r3 with ∧-true (regsB? B Ψ (EvalSt.registry st)) _ r3
... | rb , r4 with ∧-true (slotsSize (Sched.slots sched) ≤ᵇ B) _ r4
... | ss , sf =
  ∧-intro (stBounded-widen le sched st sb)
  (∧-intro fc
  (∧-intro (≤ᵇ-widen (length (EvalSt.registry st)) le rl)
  (∧-intro (regsB?-widen (EvalSt.registry st) le rb)
  (∧-intro (≤ᵇ-widen (slotsSize (Sched.slots sched)) le ss) sf))))

-- map's whole value list through one eval edge
map-applyFn-B : ∀ {n} {Γ : Ctx n} {s u} (Ψ W E : ℕ)
  (fn : Fn Γ [] [] [] s u) → 2 ≤ E →
  caseWᵗ fn ⊔ fnCapᵗ fn ≤ Ψ → sizeᵗ fn ≤ capᴱ W E →
  (vs : List (Val Γ s)) → all (valB? (capᴱ W E) Ψ s) vs ≡ true →
  all (valB? (capᴱ W (E * 3 ^ suc Ψ)) Ψ u) (map (applyFn fn) vs) ≡ true
map-applyFn-B Ψ W E fn 2≤E cap sz [] h = refl
map-applyFn-B {s = s} {u = u} Ψ W E fn 2≤E cap sz (v ∷ vs) h
  with ∧-true (valB? (capᴱ W E) Ψ s v) _ h
... | hv , hvs with ∧-true (sizeᵛ s v ≤ᵇ capᴱ W E) _ hv
... | hsz , hcap =
  ∧-intro
    (∧-intro
      (T⇒≡true _ (≤⇒≤ᵇ (evalStep-cap Ψ W E fn v 2≤E
        (≤-trans (m≤m⊔n (caseWᵗ fn) (fnCapᵗ fn)) cap) sz
        (≤ᵇ⇒≤ _ _ (T-to hsz)))))
      (T⇒≡true _ (≤⇒≤ᵇ (applyFn-fnCap Ψ fn v
        (≤ᵇ⇒≤ _ _ (T-to hcap)) cap))))
    (map-applyFn-B Ψ W E fn 2≤E cap sz vs hvs)

-- installing a node whose state is bounded on both faces preserves
-- the whole invariant (only the nodes field changes)
install-INV : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ψ B : ℕ)
  (sched : Sched Γ) (st : EvalSt e) (nid : NodeId) (ns : NodeState Γ) →
  boundedNode B ns ≡ true → fnCapNode Ψ ns ≡ true →
  INV? Ψ B sched st ≡ true → INV? Ψ B sched (installNode nid ns st) ≡ true
install-INV {Γ = Γ} Ψ B sched st nid ns bn fnn inv
  with ∧-true (stBounded? B sched st) _ inv
... | sb , r1 with ∧-true (fnCapBounded? Ψ sched st) _ r1
... | fc , r2 with ∧-true (length (EvalSt.registry st) ≤ᵇ B) _ r2
... | rl , r3 with ∧-true (regsB? B Ψ (EvalSt.registry st)) _ r3
... | rb , r4 =
  ∧-intro (install-bounded B sched st nid ns bn sb)
  (∧-intro (install-fnCap Ψ sched st nid ns fnn fc)
  (∧-intro rl (∧-intro rb r4)))

-- registering a chain: the registry grows by ONE entry — the length
-- rider pays one ×2 ledger edge (B+1 ≤ B·B = capᴱ (2E)), the new
-- path is bounded by hypothesis, everything else is untouched
register-INV : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (Ψ W E : ℕ) (src : Source) (κ : Path Γ u t)
  (sched : Sched Γ) (st : EvalSt e) → 1 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  pathB? (capᴱ W E) Ψ κ ≡ true →
  INV? Ψ (capᴱ W (2 * E)) sched (register src κ st) ≡ true
register-INV {u = u} Ψ W E src κ sched st 1≤E inv pκ
  with ∧-true (stBounded? (capᴱ W E) sched st) _ inv
... | sb , r1 with ∧-true (fnCapBounded? Ψ sched st) _ r1
... | fc , r2 with ∧-true (length (EvalSt.registry st) ≤ᵇ capᴱ W E) _ r2
... | rl , r3 with ∧-true (regsB? (capᴱ W E) Ψ (EvalSt.registry st)) _ r3
... | rb , r4 with ∧-true (slotsSize (Sched.slots sched) ≤ᵇ capᴱ W E) _ r4
... | ss , sf =
  ∧-intro (stBounded-widen cap≤ sched st sb)
  (∧-intro fc
  (∧-intro lenOK
  (∧-intro regOK
  (∧-intro (≤ᵇ-widen (slotsSize (Sched.slots sched)) cap≤ ss) sf))))
  where
  E≤2E = m≤m+n E (E + 0)
  cap≤ = capᴱ-mono W E≤2E
  1≤B  = ≤-trans (s≤s z≤n) (2≤capᴱ W 1≤E)
  lenOK : (length (EvalSt.registry st
                   ++ (EvalSt.nextReg st , src , u , κ) ∷ [])
           ≤ᵇ capᴱ W (2 * E)) ≡ true
  lenOK = T⇒≡true _ (≤⇒≤ᵇ (
    ≤-trans (≤-reflexive (length-++ (EvalSt.registry st)))
    (≤-trans (+-monoˡ-≤ 1 (≤ᵇ⇒≤ _ _ (T-to rl)))
    (≤-trans (+-monoʳ-≤ (capᴱ W E) 1≤B)
    (≤-trans (m+n≤m*n (2≤capᴱ W 1≤E) (2≤capᴱ W 1≤E))
             (≤-reflexive (sym (capᴱ-square W E))))))))
  regOK : regsB? (capᴱ W (2 * E)) Ψ
            (EvalSt.registry st
             ++ (EvalSt.nextReg st , src , u , κ) ∷ []) ≡ true
  regOK = all-++-intro _ (EvalSt.registry st) _
            (regsB?-widen (EvalSt.registry st) cap≤ rb)
            (∧-intro (pathB?-widen κ cap≤ pκ) refl)

-- of-list literals through the closed-eval ledger edge, elementwise
ofVals-B : ∀ {n} {Γ : Ctx n} {u} (Ψ W E : ℕ) → 2 ≤ E →
  (ts : List (Tm Γ [] [] [] u)) →
  sizeᵗˢ ts ≤ capᴱ W E → fnCapᵗˢ ts ≤ Ψ →
  all (valB? (capᴱ W (E * 3 ^ suc Ψ)) Ψ u) (map (λ tm → evalTm tm) ts) ≡ true
ofVals-B Ψ W E 2≤E [] hsz hfc = refl
ofVals-B {u = u} Ψ W E 2≤E (y ∷ ys) hsz hfc =
  ∧-intro
    (∧-intro
      (T⇒≡true _ (≤⇒≤ᵇ (evalTm-cap Ψ W E y 2≤E
        (≤-trans (m≤m⊔n (caseWᵗ y) (fnCapᵗ y))
                 (≤-trans (m≤m⊔n _ (fnCapᵗˢ ys)) hfc))
        (≤-trans (m≤m+n (sizeᵗ y) (sizeᵗˢ ys)) hsz))))
      (T⇒≡true _ (≤⇒≤ᵇ (fnCap-evalWith Ψ y []ᵃ tt
        (≤-trans (m≤m⊔n _ (fnCapᵗˢ ys)) hfc)))))
    (ofVals-B Ψ W E 2≤E ys
      (≤-trans (m≤n+m (sizeᵗˢ ys) (sizeᵗ y)) hsz)
      (≤-trans (m≤n⊔m _ (fnCapᵗˢ ys)) hfc))

------------------------------------------------------------------
-- (W6 face) THE SCAN FRAME, PROVEN.  A scan step is a node lookup,
-- one fold run, and a re-install: no recursion, no burst.  The size
-- side is scanVals-sharp's closed form (cap grown by
-- 3^(suc caseW · |vals|)); the fn-cap side is the pointwise
-- applyFn-fnCap run; the state side is install-INV over the widened
-- invariant.  The three stuck shapes (no node, wrong node, type
-- mismatch) emit nothing and move no ledger.
------------------------------------------------------------------

-- valB? unzips into its two faces and zips back
allB-size : ∀ {n} {Γ : Ctx n} (B Ψ : ℕ) (u : Ty) (vs : List (Val Γ u)) →
  all (valB? B Ψ u) vs ≡ true → All (λ v → sizeᵛ u v ≤ B) vs
allB-size B Ψ u []       h = []ᵃ
allB-size B Ψ u (v ∷ vs) h =
  valB-sz B Ψ u v (allB-head B Ψ u v vs h)
    ∷ᵃ allB-size B Ψ u vs (allB-tail B Ψ u v vs h)

allB-fnCap : ∀ {n} {Γ : Ctx n} (B Ψ : ℕ) (u : Ty) (vs : List (Val Γ u)) →
  all (valB? B Ψ u) vs ≡ true → All (λ v → fnCapᵛ u v ≤ Ψ) vs
allB-fnCap B Ψ u []       h = []ᵃ
allB-fnCap B Ψ u (v ∷ vs) h =
  valB-fc B Ψ u v (allB-head B Ψ u v vs h)
    ∷ᵃ allB-fnCap B Ψ u vs (allB-tail B Ψ u v vs h)

allB-zip : ∀ {n} {Γ : Ctx n} (B Ψ : ℕ) (u : Ty) (vs : List (Val Γ u)) →
  All (λ v → sizeᵛ u v ≤ B) vs → All (λ v → fnCapᵛ u v ≤ Ψ) vs →
  all (valB? B Ψ u) vs ≡ true
allB-zip B Ψ u []       _           _           = refl
allB-zip B Ψ u (v ∷ vs) (hsz ∷ᵃ hss) (hf ∷ᵃ hfs) =
  ∧-intro (∧-intro (T⇒≡true _ (≤⇒≤ᵇ hsz)) (T⇒≡true _ (≤⇒≤ᵇ hf)))
          (allB-zip B Ψ u vs hss hfs)

-- a node lookup carries both bounded faces of whatever it finds
NodeB : ∀ {n} {Γ : Ctx n} → ℕ → ℕ → Maybe (NodeState Γ) → Set
NodeB B Ψ nothing   = ⊤
NodeB B Ψ (just ns) = (boundedNode B ns ≡ true) × (fnCapNode Ψ ns ≡ true)

lookupNode-B : ∀ {n} {Γ : Ctx n} (B Ψ : ℕ) (nid : NodeId)
  (nodes : List (NodeId × NodeState Γ)) →
  all (λ kv → boundedNode B (proj₂ kv)) nodes ≡ true →
  all (λ kv → fnCapNode Ψ (proj₂ kv)) nodes ≡ true →
  NodeB B Ψ (lookupNode nid nodes)
lookupNode-B B Ψ nid []            hb hf = tt
lookupNode-B B Ψ nid ((k , s) ∷ r) hb hf with k ≡ᵇ nid
... | true  = proj₁ (∧-true _ _ hb) , proj₁ (∧-true _ _ hf)
... | false = lookupNode-B B Ψ nid r (proj₂ (∧-true _ _ hb)) (proj₂ (∧-true _ _ hf))

-- the fn-cap face of one fold run: no applyFn ever mints a new fn
scanVals-fnCap : ∀ {n} {Γ : Ctx n} {s u} (Ψ : ℕ)
  (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (ac : Val Γ u) (vs : List (Val Γ s)) →
  caseWᵗ fn ⊔ fnCapᵗ fn ≤ Ψ → fnCapᵛ u ac ≤ Ψ →
  All (λ v → fnCapᵛ s v ≤ Ψ) vs →
  (fnCapᵛ u (proj₂ (scanVals fn ac vs)) ≤ Ψ)
  × All (λ o → fnCapᵛ u o ≤ Ψ) (proj₁ (scanVals fn ac vs))
scanVals-fnCap Ψ fn ac []       hfn hacc _            = hacc , []ᵃ
scanVals-fnCap Ψ fn ac (v ∷ vs) hfn hacc (hv ∷ᵃ hvs) =
  proj₁ IH , acc′OK ∷ᵃ proj₂ IH
  where
  acc′OK = applyFn-fnCap Ψ fn (ac , v) (⊔-lub hacc hv) hfn
  IH     = scanVals-fnCap Ψ fn (applyFn fn (ac , v)) vs hfn acc′OK hvs

stepFrame-scan-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (Ψ W : ℕ) (g : Gas) (id : Id) (now : Tick)
  (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (nid : NodeId) (κ : Path Γ u t)
  (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  frameB? (capᴱ W E) Ψ (scan-f fn nid) ≡ true →
  pathB? (capᴱ W E) Ψ κ ≡ true →
  all (valB? (capᴱ W E) Ψ s) vals ≡ true →
  let r = stepFrame g id now (scan-f fn nid) κ vals fin sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ (proj₂ (proj₂ r))))
                           (proj₂ (proj₂ (proj₂ (proj₂ r)))) ≡ true)
     × (all (valB? (capᴱ W E′) Ψ u) (proj₁ r) ≡ true)
     × (all (eventB? (capᴱ W E′) Ψ) (proj₁ (proj₂ r)) ≡ true)
stepFrame-scan-wet {s = s} {u = u} Ψ W g id now fn nid κ vals fin sched st E
                   3≤E inv fB pB vB
  with lookupNode nid (EvalSt.nodes st)
     | lookupNode-B (capᴱ W E) Ψ nid (EvalSt.nodes st)
         (stB-nodes (capᴱ W E) sched st (proj₁ (INV-parts Ψ (capᴱ W E) sched st inv)))
         (fcB-nodes Ψ sched st (proj₁ (proj₂ (INV-parts Ψ (capᴱ W E) sched st inv))))
... | nothing            | _ = E , ≤-refl , inv , refl , refl
... | just (take-st _)   | _ = E , ≤-refl , inv , refl , refl
... | just (merge-st _ _)   | _ = E , ≤-refl , inv , refl , refl
... | just (concat-st _ _ _) | _ = E , ≤-refl , inv , refl , refl
... | just (switch-st _ _)  | _ = E , ≤-refl , inv , refl , refl
... | just (exhaust-st _ _) | _ = E , ≤-refl , inv , refl , refl
... | just (scan-st {w} ac) | nb with w ≟ᵗ u
...   | no _    = E , ≤-refl , inv , refl , refl
...   | yes refl =
  E′ , E≤E′ ,
  install-INV Ψ (capᴱ W E′) sched st nid (scan-st (proj₂ run))
    (T⇒≡true _ (≤⇒≤ᵇ (proj₁ szRun)))
    (T⇒≡true _ (≤⇒≤ᵇ (proj₁ fcRun)))
    (INV?-widen sched st (capᴱ-mono W E≤E′) inv) ,
  allB-zip (capᴱ W E′) Ψ u (proj₁ run) (proj₂ szRun) (proj₂ fcRun) ,
  refl
  where
  E′    = E * 3 ^ (suc (caseWᵗ fn) * length vals)
  E≤E′  = E≤E*3^ E (suc (caseWᵗ fn) * length vals)
  run   = scanVals fn ac vals
  szfn  : sizeᵗ fn ≤ capᴱ W E
  szfn  = ≤ᵇ⇒≤ _ _ (T-to (proj₁ (∧-true (sizeᵗ fn ≤ᵇ capᴱ W E) _ fB)))
  capfn : caseWᵗ fn ⊔ fnCapᵗ fn ≤ Ψ
  capfn = ≤ᵇ⇒≤ _ _ (T-to (proj₂ (∧-true (sizeᵗ fn ≤ᵇ capᴱ W E) _ fB)))
  szRun = scanVals-sharp W E fn ac vals 3≤E szfn
            (≤ᵇ⇒≤ _ _ (T-to (proj₁ nb)))
            (allB-size (capᴱ W E) Ψ s vals vB)
  fcRun = scanVals-fnCap Ψ fn ac vals capfn
            (≤ᵇ⇒≤ _ _ (T-to (proj₂ nb)))
            (allB-fnCap (capᴱ W E) Ψ s vals vB)

------------------------------------------------------------------
-- THE TAKE FRAME, PROVEN.  take emits a prefix of its input (so its
-- values ride the caller's bound), and on the cutting emit it runs
-- cutThrough: a filter on the registry whose closes are value-free
-- and whose survivors keep their frame bounds and can only shrink in
-- count.  sweepLive then filters the live schedule.  No eval edge:
-- E′ = E on both branches.
------------------------------------------------------------------

takeVals-B : ∀ {n} {Γ : Ctx n} {s} (B Ψ : ℕ) (k : ℕ) (vals : List (Val Γ s)) →
  all (valB? B Ψ s) vals ≡ true →
  all (valB? B Ψ s) (proj₁ (takeVals k vals)) ≡ true
takeVals-B B Ψ zero          _        h = refl
takeVals-B B Ψ (suc k)       []       h = refl
takeVals-B B Ψ (suc zero)    (v ∷ vs) h = ∧-intro (proj₁ (∧-true _ _ h)) refl
takeVals-B B Ψ (suc (suc k)) (v ∷ vs) h =
  ∧-intro (proj₁ (∧-true _ _ h))
          (takeVals-B B Ψ (suc k) vs (proj₂ (∧-true _ _ h)))

-- the sweep is a filter on the fn-cap face too (mirror of
-- sweepLive-bounded)
sweepLive-fnCap : ∀ {n} {Γ : Ctx n} {t} (Ψ : ℕ)
  (reg : List (RegId × Source × Chain Γ t)) (ls : List (LiveSource Γ)) →
  all (fnCapLive Ψ) ls ≡ true →
  all (fnCapLive Ψ) (sweepLive reg ls) ≡ true
sweepLive-fnCap Ψ reg []       h = refl
sweepLive-fnCap {n = n} Ψ reg (l ∷ ls) h
  with ∧-true (fnCapLive Ψ l) (all (fnCapLive Ψ) ls) h
... | bl , bls
  with (LiveSource.source l <ᵇ n)
       ∨ any (λ p → sameSource (LiveSource.source l) (proj₁ (proj₂ p))) reg
... | true  = ∧-intro bl (sweepLive-fnCap Ψ reg ls bls)
... | false = sweepLive-fnCap Ψ reg ls bls

-- the cut is a filter on the registry: the count only drops, the
-- survivors keep their frame bounds, and every close it mints is
-- value-free
cutThrough-len : ∀ {n} {Γ : Ctx n} {t} (nid : NodeId) (d : List RegId)
  (wm : RegId) (dy : List Source) (reg : List (RegId × Source × Chain Γ t)) →
  length (proj₁ (cutThrough nid d wm dy reg)) ≤ length reg
cutThrough-len nid d wm dy []                    = z≤n
cutThrough-len nid d wm dy ((rid , src , c) ∷ r)
  with pathHasNode nid (proj₂ c) | cutThrough nid d wm dy r
     | cutThrough-len nid d wm dy r
... | true  | kept , closes , rids | ih = ≤-trans ih (n≤1+n _)
... | false | kept , closes , rids | ih = s≤s ih

cutThrough-regs : ∀ {n} {Γ : Ctx n} {t} (B Ψ : ℕ) (nid : NodeId)
  (d : List RegId) (wm : RegId) (dy : List Source)
  (reg : List (RegId × Source × Chain Γ t)) →
  regsB? B Ψ reg ≡ true → regsB? B Ψ (proj₁ (cutThrough nid d wm dy reg)) ≡ true
cutThrough-regs B Ψ nid d wm dy []                    h = refl
cutThrough-regs B Ψ nid d wm dy ((rid , src , c) ∷ r) h
  with pathHasNode nid (proj₂ c) | cutThrough nid d wm dy r
     | cutThrough-regs B Ψ nid d wm dy r (proj₂ (∧-true _ _ h))
... | true  | kept , closes , rids | ih = ih
... | false | kept , closes , rids | ih = ∧-intro (proj₁ (∧-true _ _ h)) ih

cutThrough-closes : ∀ {n} {Γ : Ctx n} {t} (B Ψ : ℕ) (nid : NodeId)
  (d : List RegId) (wm : RegId) (dy : List Source)
  (reg : List (RegId × Source × Chain Γ t)) →
  all (eventB? B Ψ) (proj₁ (proj₂ (cutThrough nid d wm dy reg))) ≡ true
cutThrough-closes B Ψ nid d wm dy []                    = refl
cutThrough-closes B Ψ nid d wm dy ((rid , src , c) ∷ r)
  with pathHasNode nid (proj₂ c) | cutThrough nid d wm dy r
     | cutThrough-closes B Ψ nid d wm dy r
... | false | kept , closes , rids | ih = ih
... | true  | kept , closes , rids | ih
      with any (_≡ᵇ rid) d ∧ memberSource src dy
...   | true  = ih
...   | false = ∧-intro refl ih

stepFrame-take-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (Ψ W : ℕ) (g : Gas) (id : Id) (now : Tick)
  (nid : NodeId) (κ : Path Γ s t)
  (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  pathB? (capᴱ W E) Ψ κ ≡ true →
  all (valB? (capᴱ W E) Ψ s) vals ≡ true →
  let r = stepFrame g id now (take-f nid) κ vals fin sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ (proj₂ (proj₂ r))))
                           (proj₂ (proj₂ (proj₂ (proj₂ r)))) ≡ true)
     × (all (valB? (capᴱ W E′) Ψ s) (proj₁ r) ≡ true)
     × (all (eventB? (capᴱ W E′) Ψ) (proj₁ (proj₂ r)) ≡ true)
stepFrame-take-wet {s = s} Ψ W g id now nid κ vals fin sched st E 3≤E inv pB vB
  with lookupNode nid (EvalSt.nodes st)
... | nothing                = E , ≤-refl , inv , refl , refl
... | just (scan-st _)       = E , ≤-refl , inv , refl , refl
... | just (merge-st _ _)    = E , ≤-refl , inv , refl , refl
... | just (concat-st _ _ _) = E , ≤-refl , inv , refl , refl
... | just (switch-st _ _)   = E , ≤-refl , inv , refl , refl
... | just (exhaust-st _ _)  = E , ≤-refl , inv , refl , refl
... | just (take-st k) with proj₂ (proj₂ (takeVals k vals))
...   | false =
  E , ≤-refl ,
  install-INV Ψ (capᴱ W E) sched st nid
    (take-st (proj₁ (proj₂ (takeVals k vals)))) refl refl inv ,
  takeVals-B (capᴱ W E) Ψ k vals vB , refl
...   | true =
  E , ≤-refl ,
  ∧-intro
    (∧-intro (sweepLive-bounded B kept (Sched.live sched) bls)
             (setNode-bounded B nid (take-st zero) (EvalSt.nodes st) refl bns))
  (∧-intro
    (∧-intro (sweepLive-fnCap Ψ kept (Sched.live sched) fls)
             (setNode-fnCap Ψ nid (take-st zero) (EvalSt.nodes st) refl fns))
  (∧-intro lenOK
  (∧-intro (cutThrough-regs B Ψ nid del wm dy (EvalSt.registry st) rb) r4))) ,
  takeVals-B B Ψ k vals vB ,
  cutThrough-closes B Ψ nid del wm dy (EvalSt.registry st)
  where
  B    = capᴱ W E
  del  = EvalSt.delivered st
  wm   = EvalSt.regWatermark st
  dy   = EvalSt.dying st
  kept = proj₁ (cutThrough nid del wm dy (EvalSt.registry st))
  P    = INV-parts Ψ B sched st inv
  sb   = proj₁ P
  fc   = proj₁ (proj₂ P)
  rl   = proj₁ (proj₂ (proj₂ P))
  rb   = proj₁ (proj₂ (proj₂ (proj₂ P)))
  r4   = ∧-intro (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ P)))))
                 (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ P)))))
  bls  = stB-live B sched st sb
  bns  = stB-nodes B sched st sb
  fls  = fcB-live Ψ sched st fc
  fns  = fcB-nodes Ψ sched st fc
  lenOK : (length kept ≤ᵇ B) ≡ true
  lenOK = T⇒≡true _ (≤⇒≤ᵇ
    (≤-trans (cutThrough-len nid del wm dy (EvalSt.registry st))
             (≤ᵇ⇒≤ _ _ (T-to rl))))

------------------------------------------------------------------
-- THE OUTER *All FRAME.  thruWalk folds the emitted inners; each
-- step subscribes one inner inside the current instant and rewrites
-- the *All node.  Only the per-emit step moves the ledger (it is a
-- subscribeE re-entry); the wrap and the node rewrites are free.
------------------------------------------------------------------

eventsB?-widen : ∀ {n} {Γ : Ctx n} {u} {B B′ Ψ : ℕ}
  (es : List (InstEvent (Val Γ u))) → B ≤ B′ →
  all (eventB? B Ψ) es ≡ true → all (eventB? B′ Ψ) es ≡ true
eventsB?-widen es B≤ h = all-impl _ _ (λ ev → eventB?-widen ev B≤) es h

-- splitting a whole burst: same two faces as splitEvents, concatenated
splitBurst-vals-B : ∀ {n} {Γ : Ctx n} {s u : Ty} (B Ψ : ℕ) (str : Stream Γ s) →
  burstB? B Ψ str ≡ true →
  all (valB? B Ψ s) (proj₁ (splitBurst {A = Val Γ u} str)) ≡ true
splitBurst-vals-B B Ψ []               h = refl
splitBurst-vals-B {Γ = Γ} {u = u} B Ψ (em ∷ ems) h =
  all-++-intro _ (proj₁ (splitEvents {A = Val Γ u} (InstEmit.events em))) _
    (splitEvents-vals-B B Ψ (InstEmit.events em) (proj₁ (∧-true _ _ h)))
    (splitBurst-vals-B {u = u} B Ψ ems (proj₂ (∧-true _ _ h)))

splitBurst-bk-B : ∀ {n} {Γ : Ctx n} {s u : Ty} (B Ψ : ℕ) (str : Stream Γ s) →
  all (eventB? B Ψ) (proj₁ (proj₂ (splitBurst {A = Val Γ u} str))) ≡ true
splitBurst-bk-B B Ψ []               = refl
splitBurst-bk-B {Γ = Γ} {u = u} B Ψ (em ∷ ems) =
  all-++-intro _ (proj₁ (proj₂ (splitEvents {A = Val Γ u} (InstEmit.events em)))) _
    (splitEvents-bk-B {u = u} B Ψ (InstEmit.events em))
    (splitBurst-bk-B {u = u} B Ψ ems)

-- mergeAll's counter bump: whatever the lookup finds, the invariant
-- survives (merge-st is value-free, every other shape is a no-op)
mergeBump-INV : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ψ B : ℕ)
  (nid : NodeId) (d : Bool) (sched : Sched Γ) (st : EvalSt e) →
  INV? Ψ B sched st ≡ true →
  INV? Ψ B sched (record st { nodes = mergeBump nid d (EvalSt.nodes st) }) ≡ true
mergeBump-INV Ψ B nid d sched st inv with lookupNode nid (EvalSt.nodes st)
... | just (merge-st k od)   = install-INV Ψ B sched st nid
                                 (merge-st (if d then k else suc k) od) refl refl inv
... | nothing                = inv
... | just (scan-st _)       = inv
... | just (take-st _)       = inv
... | just (concat-st _ _ _) = inv
... | just (switch-st _ _)   = inv
... | just (exhaust-st _ _)  = inv

-- switchAll's cut: the same registry filter the take frame runs
switchKill-INV : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ψ W E : ℕ)
  (cur : Maybe NodeId) (sched : Sched Γ) (st : EvalSt e) →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  let r = switchKill cur sched st
  in (INV? Ψ (capᴱ W E) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (all (eventB? (capᴱ W E) Ψ) (proj₁ r) ≡ true)
switchKill-INV Ψ W E nothing  sched st inv = inv , refl
switchKill-INV Ψ W E (just v) sched st inv =
  ∧-intro
    (∧-intro (sweepLive-bounded B kept (Sched.live sched) bls) bns)
  (∧-intro
    (∧-intro (sweepLive-fnCap Ψ kept (Sched.live sched) fls) fns)
  (∧-intro lenOK
  (∧-intro (cutThrough-regs B Ψ v del wm dy (EvalSt.registry st) rb) r4))) ,
  cutThrough-closes B Ψ v del wm dy (EvalSt.registry st)
  where
  B    = capᴱ W E
  del  = EvalSt.delivered st
  wm   = EvalSt.regWatermark st
  dy   = EvalSt.dying st
  kept = proj₁ (cutThrough v del wm dy (EvalSt.registry st))
  P    = INV-parts Ψ B sched st inv
  sb   = proj₁ P
  fc   = proj₁ (proj₂ P)
  rl   = proj₁ (proj₂ (proj₂ P))
  rb   = proj₁ (proj₂ (proj₂ (proj₂ P)))
  r4   = ∧-intro (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ P)))))
                 (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ P)))))
  bls  = stB-live B sched st sb
  bns  = stB-nodes B sched st sb
  fls  = fcB-live Ψ sched st fc
  fns  = fcB-nodes Ψ sched st fc
  lenOK : (length kept ≤ᵇ B) ≡ true
  lenOK = T⇒≡true _ (≤⇒≤ᵇ
    (≤-trans (cutThrough-len v del wm dy (EvalSt.registry st))
             (≤ᵇ⇒≤ _ _ (T-to rl))))

-- the wrap: values and events pass through, only the *All node's
-- done-flag is written back (and concat's queue is re-installed as-is)
thruWrap-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (Ψ B : ℕ) (op : AllOp) (nid : NodeId) (fin : Bool)
  (vs : List (Val Γ u)) (bs : List (InstEvent (Val Γ t)))
  (sched : Sched Γ) (st : EvalSt e) →
  INV? Ψ B sched st ≡ true →
  all (valB? B Ψ u) vs ≡ true →
  all (eventB? B Ψ) bs ≡ true →
  let r = thruWrap op nid fin (vs , bs , sched , st)
  in (INV? Ψ B (proj₁ (proj₂ (proj₂ (proj₂ r))))
               (proj₂ (proj₂ (proj₂ (proj₂ r)))) ≡ true)
     × (all (valB? B Ψ u) (proj₁ r) ≡ true)
     × (all (eventB? B Ψ) (proj₁ (proj₂ r)) ≡ true)
thruWrap-wet Ψ B op nid false vs bs sched st inv vB bB = inv , vB , bB
thruWrap-wet Ψ B mergeᵒ nid true vs bs sched st inv vB bB
  with lookupNode nid (EvalSt.nodes st)
... | just (merge-st k _)    =
      install-INV Ψ B sched st nid (merge-st k true) refl refl inv , vB , bB
... | nothing                = inv , vB , bB
... | just (scan-st _)       = inv , vB , bB
... | just (take-st _)       = inv , vB , bB
... | just (concat-st _ _ _) = inv , vB , bB
... | just (switch-st _ _)   = inv , vB , bB
... | just (exhaust-st _ _)  = inv , vB , bB
thruWrap-wet Ψ B concatᵒ nid true vs bs sched st inv vB bB
  with lookupNode nid (EvalSt.nodes st)
     | lookupNode-B B Ψ nid (EvalSt.nodes st)
         (stB-nodes B sched st (proj₁ (INV-parts Ψ B sched st inv)))
         (fcB-nodes Ψ sched st (proj₁ (proj₂ (INV-parts Ψ B sched st inv))))
... | just (concat-st q act _) | nb =
      install-INV Ψ B sched st nid (concat-st q act true)
        (proj₁ nb) (proj₂ nb) inv , vB , bB
... | nothing                | _ = inv , vB , bB
... | just (scan-st _)       | _ = inv , vB , bB
... | just (take-st _)       | _ = inv , vB , bB
... | just (merge-st _ _)    | _ = inv , vB , bB
... | just (switch-st _ _)   | _ = inv , vB , bB
... | just (exhaust-st _ _)  | _ = inv , vB , bB
thruWrap-wet Ψ B switchᵒ nid true vs bs sched st inv vB bB
  with lookupNode nid (EvalSt.nodes st)
... | just (switch-st cur _) =
      install-INV Ψ B sched st nid (switch-st cur true) refl refl inv , vB , bB
... | nothing                = inv , vB , bB
... | just (scan-st _)       = inv , vB , bB
... | just (take-st _)       = inv , vB , bB
... | just (merge-st _ _)    = inv , vB , bB
... | just (concat-st _ _ _) = inv , vB , bB
... | just (exhaust-st _ _)  = inv , vB , bB
thruWrap-wet Ψ B exhaustᵒ nid true vs bs sched st inv vB bB
  with lookupNode nid (EvalSt.nodes st)
... | just (exhaust-st act _) =
      install-INV Ψ B sched st nid (exhaust-st act true) refl refl inv , vB , bB
... | nothing                = inv , vB , bB
... | just (scan-st _)       = inv , vB , bB
... | just (take-st _)       = inv , vB , bB
... | just (merge-st _ _)    = inv , vB , bB
... | just (concat-st _ _ _) = inv , vB , bB
... | just (switch-st _ _)   = inv , vB , bB

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
concatDrain-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (Ψ W : ℕ) (g : Gas) (allNid : NodeId) (κ : Path Γ s t)
  (id : Id) (now : Tick) (q : List (Closed Γ s))
  (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  pathB? (capᴱ W E) Ψ κ ≡ true →
  all (λ o → sizeᵉ o ≤ᵇ capᴱ W E) q ≡ true →
  all (λ o → fnCapᵉ o ≤ᵇ Ψ) q ≡ true →
  let r = concatDrain g allNid κ id now q sched st
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
-- concatAll's drain moves the ledger
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

-- the concat queue's stored outers only ever need widening upward
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
-- ordinal are minted, the merge node installed, the BODY itself
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

-- the completion latch: dropping a source SHRINKS the registry on
-- both riders, and completedSources / connectedShares are read by no
-- conjunct at all
dropSource-len : ∀ {n} {Γ : Ctx n} {t} (src : Source)
  (reg : List (RegId × Source × Chain Γ t)) →
  length (dropSource src reg) ≤ length reg
dropSource-len src []                  = z≤n
dropSource-len src ((rid , s , c) ∷ r) with sameSource src s
... | true  = ≤-trans (dropSource-len src r) (n≤1+n _)
... | false = s≤s (dropSource-len src r)

dropSource-regs : ∀ {n} {Γ : Ctx n} {t} (B Ψ : ℕ) (src : Source)
  (reg : List (RegId × Source × Chain Γ t)) →
  regsB? B Ψ reg ≡ true → regsB? B Ψ (dropSource src reg) ≡ true
dropSource-regs B Ψ src []                  h = refl
dropSource-regs B Ψ src ((rid , s , c) ∷ r) h with sameSource src s
... | true  = dropSource-regs B Ψ src r (proj₂ (∧-true _ _ h))
... | false = ∧-intro (proj₁ (∧-true _ _ h))
                      (dropSource-regs B Ψ src r (proj₂ (∧-true _ _ h)))

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
  register-INV Ψ W E src (thru-outer mergeᵒ nid ↠ κ) sched₄ st₀
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
  st₀    = installNode nid (merge-st 0 false) st
  inv₁   = install-INV Ψ (capᴱ W E) sched₃ st nid (merge-st 0 false)
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

subscribeE-walkS Ψ W g (mergeAllᵉ b) κ id now sched st E 3≤E inv szB fcB pB =
  subscribeAll-wet Ψ W g mergeᵒ (merge-st 0 false) b κ id now sched st E
    3≤E inv refl refl (≤-trans (n≤1+n (sizeᵉ b)) szB) fcB pB
subscribeE-walkS {u = u} Ψ W g (concatAllᵉ b) κ id now sched st E 3≤E inv szB fcB pB =
  subscribeAll-wet Ψ W g concatᵒ (concat-st {t = u} [] false false) b κ id now
    sched st E 3≤E inv refl refl (≤-trans (n≤1+n (sizeᵉ b)) szB) fcB pB
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

thruConsume-wet Ψ W g mergeᵒ nid κ id now o sched st E 3≤E inv oB pB =
  E₁ , E≤E₁ , mergeBump-INV Ψ (capᴱ W E₁) nid done sched₁ st₁ inv₁ ,
  vsB , bsB
  where
  SI   = subscribeInner-wet Ψ W g mergeᵒ nid κ id now o sched st E 3≤E inv oB pB
  SI₄  = subscribeInner g mergeᵒ nid κ id now o sched st
  done = proj₁ (proj₂ (proj₂ (proj₂ SI₄)))
  sched₁ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ SI₄))))
  st₁  = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SI₄))))
  E₁   = proj₁ SI
  E≤E₁ = proj₁ (proj₂ SI)
  inv₁ = proj₁ (proj₂ (proj₂ SI))
  vsB  = proj₁ (proj₂ (proj₂ (proj₂ SI)))
  bsB  = proj₂ (proj₂ (proj₂ (proj₂ SI)))
thruConsume-wet {u = u} Ψ W g concatᵒ nid κ id now o sched st E 3≤E inv oB pB
  with lookupNode nid (EvalSt.nodes st)
     | lookupNode-B (capᴱ W E) Ψ nid (EvalSt.nodes st)
         (stB-nodes (capᴱ W E) sched st (proj₁ (INV-parts Ψ (capᴱ W E) sched st inv)))
         (fcB-nodes Ψ sched st (proj₁ (proj₂ (INV-parts Ψ (capᴱ W E) sched st inv))))
... | just (concat-st {w} q true od) | nb with w ≟ᵗ u
...   | yes refl =
  E , ≤-refl ,
  install-INV Ψ (capᴱ W E) sched st nid (concat-st (q ++ o ∷ []) true od)
    (all-++-intro _ q _ (proj₁ nb)
      (∧-intro (proj₁ (∧-true _ _ oB)) refl))
    (all-++-intro _ q _ (proj₂ nb)
      (∧-intro (proj₂ (∧-true _ _ oB)) refl))
    inv ,
  refl , refl
...   | no _ = E , ≤-refl , inv , refl , refl
thruConsume-wet {u = u} Ψ W g concatᵒ nid κ id now o sched st E 3≤E inv oB pB
    | just (concat-st q false od) | nb =
  E₁ , E≤E₁ ,
  install-INV Ψ (capᴱ W E₁) (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ SI₄))))) st₁ nid
    (concat-st {t = u} [] (not done) od) refl refl inv₁ ,
  vsB , bsB
  where
  SI   = subscribeInner-wet Ψ W g concatᵒ nid κ id now o sched st E 3≤E inv oB pB
  SI₄  = subscribeInner g concatᵒ nid κ id now o sched st
  done = proj₁ (proj₂ (proj₂ (proj₂ SI₄)))
  st₁  = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SI₄))))
  E₁   = proj₁ SI
  E≤E₁ = proj₁ (proj₂ SI)
  inv₁ = proj₁ (proj₂ (proj₂ SI))
  vsB  = proj₁ (proj₂ (proj₂ (proj₂ SI)))
  bsB  = proj₂ (proj₂ (proj₂ (proj₂ SI)))
thruConsume-wet Ψ W g concatᵒ nid κ id now o sched st E 3≤E inv oB pB
    | nothing | _ = E , ≤-refl , inv , refl , refl
thruConsume-wet Ψ W g concatᵒ nid κ id now o sched st E 3≤E inv oB pB
    | just (scan-st _) | _ = E , ≤-refl , inv , refl , refl
thruConsume-wet Ψ W g concatᵒ nid κ id now o sched st E 3≤E inv oB pB
    | just (take-st _) | _ = E , ≤-refl , inv , refl , refl
thruConsume-wet Ψ W g concatᵒ nid κ id now o sched st E 3≤E inv oB pB
    | just (merge-st _ _) | _ = E , ≤-refl , inv , refl , refl
thruConsume-wet Ψ W g concatᵒ nid κ id now o sched st E 3≤E inv oB pB
    | just (switch-st _ _) | _ = E , ≤-refl , inv , refl , refl
thruConsume-wet Ψ W g concatᵒ nid κ id now o sched st E 3≤E inv oB pB
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
... | just (merge-st _ _)    = E , ≤-refl , inv , refl , refl
... | just (concat-st _ _ _) = E , ≤-refl , inv , refl , refl
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
... | just (merge-st _ _)    = E , ≤-refl , inv , refl , refl
... | just (concat-st _ _ _) = E , ≤-refl , inv , refl , refl
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
-- the inner *All frame's drain and finish.  concatAll is the only
-- op whose completion does more than flip a flag: it walks its
-- parked queue, subscribing each stored outer until one stays open.
------------------------------------------------------------------

concatDrain-wet Ψ W g allNid κ id now [] sched st E 3≤E inv pB qz qf =
  E , ≤-refl , inv , refl , refl , refl , refl
concatDrain-wet {s = s} Ψ W g allNid κ id now (o ∷ q) sched st E 3≤E inv pB qz qf
  with subscribeInner g concatᵒ allNid κ id now o sched st
     | subscribeInner-wet Ψ W g concatᵒ allNid κ id now o sched st E 3≤E inv
         (∧-intro (proj₁ (∧-true (sizeᵉ o ≤ᵇ capᴱ W E) _ qz))
                  (proj₁ (∧-true (fnCapᵉ o ≤ᵇ Ψ) _ qf))) pB
... | (_ , vs , bs , false , sched₁ , st₁) | (E₁ , E≤E₁ , inv₁ , vsB , bsB) =
  E₁ , E≤E₁ , inv₁ , vsB , bsB ,
  allsz-widen q (capᴱ-mono W E≤E₁) (proj₂ (∧-true _ _ qz)) ,
  proj₂ (∧-true _ _ qf)
... | (_ , vs , bs , true , sched₁ , st₁) | (E₁ , E≤E₁ , inv₁ , vsB , bsB) =
  E₂ , ≤-trans E≤E₁ E₁≤E₂ , inv₂ ,
  all-++-intro _ vs _ (valsB?-widen s vs cap₁₂ vsB) vs′B ,
  all-++-intro _ bs _ (eventsB?-widen bs cap₁₂ bsB) bs′B ,
  q′z , q′f
  where
  IH    = concatDrain-wet Ψ W g allNid κ id now q sched₁ st₁ E₁
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

innerFinish-wet Ψ W g mergeᵒ allNid inst κ id now vals sched st E 3≤E inv pB vB
  with lookupNode allNid (EvalSt.nodes st)
... | just (merge-st k od)   =
  E , ≤-refl ,
  install-INV Ψ (capᴱ W E) sched st allNid (merge-st (pred k) od) refl refl inv ,
  vB , refl
... | nothing                = E , ≤-refl , inv , vB , refl
... | just (scan-st _)       = E , ≤-refl , inv , vB , refl
... | just (take-st _)       = E , ≤-refl , inv , vB , refl
... | just (concat-st _ _ _) = E , ≤-refl , inv , vB , refl
... | just (switch-st _ _)   = E , ≤-refl , inv , vB , refl
... | just (exhaust-st _ _)  = E , ≤-refl , inv , vB , refl
innerFinish-wet {s = s} Ψ W g concatᵒ allNid inst κ id now vals sched st E
                3≤E inv pB vB
  with lookupNode allNid (EvalSt.nodes st)
     | lookupNode-B (capᴱ W E) Ψ allNid (EvalSt.nodes st)
         (stB-nodes (capᴱ W E) sched st (proj₁ (INV-parts Ψ (capᴱ W E) sched st inv)))
         (fcB-nodes Ψ sched st (proj₁ (proj₂ (INV-parts Ψ (capᴱ W E) sched st inv))))
... | just (concat-st {w} q act od) | nb with w ≟ᵗ s
...   | yes refl =
  E′ , E≤E′ ,
  install-INV Ψ (capᴱ W E′) sched′ st′ allNid (concat-st q′ act′ od)
    q′z q′f inv′ ,
  all-++-intro _ vals _ (valsB?-widen s vals (capᴱ-mono W E≤E′) vB) vsB ,
  bsB
  where
  DR    = concatDrain-wet Ψ W g allNid κ id now q sched st E 3≤E inv pB
            (proj₁ nb) (proj₂ nb)
  dr    = concatDrain g allNid κ id now q sched st
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
innerFinish-wet Ψ W g concatᵒ allNid inst κ id now vals sched st E 3≤E inv pB vB
    | nothing               | _ = E , ≤-refl , inv , vB , refl
innerFinish-wet Ψ W g concatᵒ allNid inst κ id now vals sched st E 3≤E inv pB vB
    | just (scan-st _)      | _ = E , ≤-refl , inv , vB , refl
innerFinish-wet Ψ W g concatᵒ allNid inst κ id now vals sched st E 3≤E inv pB vB
    | just (take-st _)      | _ = E , ≤-refl , inv , vB , refl
innerFinish-wet Ψ W g concatᵒ allNid inst κ id now vals sched st E 3≤E inv pB vB
    | just (merge-st _ _)   | _ = E , ≤-refl , inv , vB , refl
innerFinish-wet Ψ W g concatᵒ allNid inst κ id now vals sched st E 3≤E inv pB vB
    | just (switch-st _ _)  | _ = E , ≤-refl , inv , vB , refl
innerFinish-wet Ψ W g concatᵒ allNid inst κ id now vals sched st E 3≤E inv pB vB
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
    | just (merge-st _ _)    = E , ≤-refl , inv , vB , refl
innerFinish-wet Ψ W g switchᵒ allNid inst κ id now vals sched st E 3≤E inv pB vB
    | just (concat-st _ _ _) = E , ≤-refl , inv , vB , refl
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
... | just (merge-st _ _)    = E , ≤-refl , inv , vB , refl
... | just (concat-st _ _ _) = E , ≤-refl , inv , vB , refl
... | just (switch-st _ _)   = E , ≤-refl , inv , vB , refl

------------------------------------------------------------------
-- THE FOLD DECOMPOSITION, PROVEN: cascadeGo threads the walk
-- invariant chain by chain over chainStep-wet.  This is the
-- structure the cascadeGo-wet memo demanded — per-cascade growth
-- threads through the fold at a moving ledger position, with the
-- registry cardinality rider (INV?'s length conjunct) available at
-- the latch for the eventual receipt arithmetic.  Not consumed yet:
-- cascade-dry keeps riding the landing core below until the
-- quantitative debt (memo (3)) closes.
------------------------------------------------------------------

cascadeGo-walk : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (Ψ W : ℕ) (a : Arrival Γ) (id : Id)
  (chains : List (RegId × Path Γ (arrTy a) t))
  (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  all (λ rc → pathB? (capᴱ W E) Ψ (proj₂ rc)) chains ≡ true →
  valB? (capᴱ W E) Ψ (arrTy a) (arrVal a) ≡ true →
  let r = cascadeGo a id chains sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstB? (capᴱ W E′) Ψ (proj₁ r) ≡ true)
cascadeGo-walk Ψ W a id [] sched st E 3≤E inv chB vB =
  E , ≤-refl , inv , refl
cascadeGo-walk Ψ W a id ((rid , c) ∷ chains) sched st E 3≤E inv chB vB
  with ∧-true (pathB? (capᴱ W E) Ψ c) _ chB
... | pc , pchains with any (_≡ᵇ rid) (EvalSt.cancelled st)
... | true  = cascadeGo-walk Ψ W a id chains sched st E 3≤E inv pchains vB
... | false =
  let st₀ = record st { delivered = rid ∷ EvalSt.delivered st }
      (E₁ , E≤E₁ , inv₁ , em₁) =
        chainStep-wet Ψ W id a c sched st₀ E 3≤E inv pc vB
      cap≤ = capᴱ-mono W E≤E₁
      (E₂ , E₁≤E₂ , inv₂ , em₂) =
        cascadeGo-walk Ψ W a id chains
          (proj₁ (proj₂ (chainStep id a c sched st₀)))
          (proj₂ (proj₂ (chainStep id a c sched st₀)))
          E₁ (≤-trans 3≤E E≤E₁) inv₁
          (chainsB?-widen chains cap≤ pchains)
          (valB?-widen (arrTy a) (arrVal a) cap≤ vB)
  in E₂ , ≤-trans E≤E₁ E₁≤E₂ , inv₂ ,
     all-++-intro _ (proj₁ (chainStep id a c sched st₀)) _
       (burstB?-widen (proj₁ (chainStep id a c sched st₀))
                      (capᴱ-mono W E₁≤E₂) em₁)
       em₂

------------------------------------------------------------------
-- the three cores
------------------------------------------------------------------

------------------------------------------------------------------
-- THE PROOF DESIGN for the three cores (2026-07-19, after the tower
-- attack).  The wet contract for the mutual subscription block is one
-- strengthened induction, consumed through `hasAtLeast`:
--
--   fuel hasAtLeast need(args) → no dry × stores land bounded
--
-- and the induction that defines/bounds `need` is LEXICOGRAPHIC over
-- the three decrement edges:
--
--   1. share connect — decreases the UNCONNECTED-SLOT COUNT
--      (connectedShares latches; a def's walk can only shrink it).
--   2. μ-unfold — decreases SYNC-REACHABLE SIZE (syncSizeᵉ, deferᵉ
--      a leaf): unfoldμ substitutes `μᵉ body` only at var positions,
--      and vars are TYPE-GUARANTEED defer-gated (Δᵍ→Δ moves only at
--      deferᵉ), so the substituted copies are invisible to the
--      synchronous walk.  DISCHARGED above: syncSize-unfoldμ /
--      unfoldμ-shrinks, machine-checked.
--   3. subscribeInner — decreases the DERSHOWITZ–MANNA MULTISET of
--      SHELL sizes (2026-07-20: the SHELL DESIGN, adopted with
--      Anthony's approval, replacing the layer-derivation reading).
--      A runtime obs value IS a closed expression; its measure is
--      measureE = counts B ∘ shellsᵉ — the multiset of operator-
--      skeleton sizes of the value and every sync-reachable
--      embedded observable (Rx.Exp.shellsᵉ), a pure function of
--      syntax.  Shells count Exp constructors ONLY (Tm material
--      weightless, strmᵗ/deferᵉ leaves), which buys the design's
--      two load-bearing facts, both PROVEN above:
--        · substitution invariance (shellSize-subΘ): subΘ rewrites
--          only Tm material, so instantiation preserves every
--          shell size EXACTLY.  No inflation — an instantiated
--          template's multiset is a class-preserved copy of the
--          template's plus the plugged obs values' own shells
--          (reify-inner: a plug's footprint is void, its shells
--          join the inner multiset verbatim).
--        · free side conditions: every shell of e is ≤ sizeᵉ e
--          (shells-≤/shellsᵛ-≤) and shells number ≤ sizeᵉ e
--          (shells-len) — so stBounded?'s sizeᵛ cap bounds both
--          the classes (≤ B) and the entry sum (≤ V, the rank
--          bridge's side condition).  NO new invariant; the whole
--          Layered derivation apparatus is deleted (git: 1fbc59c).
--      The hops:
--        · embedded-value hop (subscribing a value that sits as a
--          strmᵗ subtree of the carrier — of-list literals under
--          closed evaluation, evalWith (strmᵗ e) []ᵃ = e): its
--          shellsᵉ is a CONTIGUOUS sublist of the carrier's inner
--          (innerᵗ (strmᵗ e) = shellsᵉ e), and the carrier's own
--          shell rides on top — strict sub-multiset, ≺-embed.
--        · eval/scan-produced hop (applyFn/evalWith instantiates a
--          template): by shellSize-subΘ the produced multiset =
--          the fn-body strmᵗ subtree's sub-multiset, classes on
--          the nose, ⊎ the plugged obs values' shells.  The first
--          part is the embed shape again; the plugged part is
--          where the LEDGER lives — the plugs are prior stored
--          values whose shells the global multiset already owns
--          (deliveries ≤ syntactic occurrences because subΘ
--          COPIES trees — SYNC-LINEARITY, PROVEN above:
--          plugs-lenᵉ bounds the plug cardinality by occsᵉ · V,
--          occs≤syncᵉ caps occurrences syntactically, and
--          inner-len-subΘ is the exact length bookkeeping).  The
--          multiset-level input is the subΘ multiset equation
--          (subΘ-countsᵉ, proven); subΘ-capᵉ is its All-cap
--          shadow and subΘ-shells-len its entry-sum package.
--        · share-crossing hop (a template's `input` hits a slot):
--          exits the per-value measure — it anchors against the
--          slot's own element of the GLOBAL multiset {program} ⊎
--          {slots}; that re-anchoring is the ownership half of the
--          ledger (cascadeGo-wet), not the per-value order.
--      (The 2026-07-19 layer-derivation design worked but carried
--      an unfixable wart: unused env entries gave layers with no
--      syntactic footprint, so the entry-sum side condition needed
--      its own invariant.  The design before THAT — lex (skeleton,
--      value size), subterm-ordered — is REFUTED: chain two
--      obs-typed scans directly, second fn λ(b,v). mergeAll(of[snd
--      x]), and the embedded-value hop lands on a first-scan ac
--      whose template is subterm-incomparable with the carrier's
--      and can dwarf it.)
--
-- THE DEMAND, closed-form and PROVEN (dBound above).  Fuel is
-- depth-consumed, so the contract carries
--
--   fuel hasAtLeast suc (dBound V R U r s)
--
-- with V the store size bound, R = (suc V)^(suc B) the store rank
-- cap (rank-lt-pow), U = unconn, r = the current value's rank, s =
-- the current expression's syncSize.  Each decrement edge consumes
-- one gs against a strictly smaller demand: dBound-μ
-- (unfoldμ-shrinks drops s), dBound-hop (rank-mono-≺ over
-- ≺-embed/≺-replace drops r, s resets ≤ V), dBound-connect
-- (unconn-insert drops U, r resets ≤ R) — all three proven, so the
-- clause proofs only apply them.  dBound < (suc V)^(B+3)·suc U:
-- one exponential story above the store bound, while the seeded
-- budget's tower gains (suc sz) stories per instant —
-- budget-hasAtLeast's tower summand dominates with room to spare,
-- and every literal-headed demand (no chained scans) is already
-- covered by the 2^(sz·(id+1)²) summand alone.
--
-- The cores below are the contract instantiated at
-- the root burst (burst-dry/-bounded) and at the chain fold
-- (cascadeGo-wet); the disjointness argument (each registration's
-- path owns its minted nodes, so per-cascade store traffic is
-- structure-bounded) supplies the store-boundedness half.
--
-- THE WALK INVARIANT (2026-07-20, the clause-grind session).  The
-- stated subscribeE-wet is the contract's OUTER FACE only — its
-- `sizeᵉ b ≤ V` hypothesis holds at both instantiation sites (root
-- program; stored values) but does NOT self-apply down the walk,
-- and the induction must generalize internally:
--   · μ edge: unfoldμ COPIES the closed μ, so sizeᵉ grows past any
--     fixed cap along iterated unfolds.  Thread the SHELL caps
--     instead — every shell preserved-or-stepped-down and the
--     count exactly preserved (shells-unfoldμ-cap/-len above);
--     sizeᵉ is only needed for STORABILITY, against the (tower)
--     landing budget, not against V.
--   · no fixed (V, R) survives the walk: a scan frame folds each
--     value with NO fuel peel (fuel is depth-consumed; breadth is
--     free), and each fold is one base swap (applyFn-size), so
--     mid-walk stores legitimately outgrow the entry cap V and
--     later inner subscriptions carry ranks past R.  A cap indexed
--     by REMAINING GAS fails for the same reason (folds do not
--     peel gas).
--   · the missing accounting is a per-instant BREADTH LEDGER: the
--     value-list lengths threading stepFrame/pushBurst.  SETTLED
--     2026-07-24 — see THE WALK LEDGER section above: the sharp
--     eval bound (caseW, substitution-invariant exponent) replaces
--     applyFn-size's self-inflating one, the ledger is the
--     multiplicative exponent capᴱ W₀ E with one uniform ×3^(suc Ψ)
--     rule per eval edge and ×2 per cheap edge, fold-runs cost
--     3^(suc Ψ · m) by scanVals-sharp, and INV? (store bounds +
--     fn caps + registry cardinality + chain frames) is the
--     invariant the walk contracts thread.  The count cap's DESIGN
--     closed 2026-07-24 (memo (5), THE WIDTH LEDGER, corrected to
--     the recurrence-closed walkCap form): widths are
--     substitution-invariant, so run lengths and the per-lineage
--     fold count 𝔉 anchor at walkCap — all entry-frozen.  The
--     JOINT FACE (subscribeE-walk above) states wet + dry + ledger
--     together; what remains is its clause grind and the landing
--     composition; until THAT lands, the landing halves live in
--     these two cores and nowhere else.
------------------------------------------------------------------

------------------------------------------------------------------
-- (W11-A) THE FLAT STATE LEMMAS.  Ω never moves, so each of these
-- is "invariant in, invariant out": the size side's ledger edges
-- (register-INV's ×2 length rider, the widening chains) all vanish,
-- and widthOK? has no length conjunct to pay them with.  Every
-- proof below is its fnCap counterpart with the arithmetic deleted.
------------------------------------------------------------------

-- widthOK? is a FLAT four-way ∧ (no nested stBounded?/fnCapBounded?
-- pair), so one projector serves the whole block — same reason
-- INV-parts exists: `∧-true _ _` alone leaves a stuck metavariable
WOK-parts : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ω : ℕ)
  (sched : Sched Γ) (st : EvalSt e) → widthOK? Ω sched st ≡ true →
  (all (ofWLive Ω) (Sched.live sched) ≡ true)
  × (all (λ kv → ofWNode Ω (proj₂ kv)) (EvalSt.nodes st) ≡ true)
  × (regsΩ? Ω (EvalSt.registry st) ≡ true)
  × ((slotsOfW (Sched.slots sched) ≤ᵇ Ω) ≡ true)
WOK-parts Ω sched st h
  with ∧-true (all (ofWLive Ω) (Sched.live sched)) _ h
... | lv , r1
  with ∧-true (all (λ kv → ofWNode Ω (proj₂ kv)) (EvalSt.nodes st)) _ r1
... | nd , r2 with ∧-true (regsΩ? Ω (EvalSt.registry st)) _ r2
... | rg , sl = lv , nd , rg , sl

-- the node-install ring (mirror of setNode-bounded / setNode-fnCap)
setNode-ofW : ∀ {n} {Γ : Ctx n} (Ω : ℕ) (nid : NodeId) (ns : NodeState Γ)
  (nodes : List (NodeId × NodeState Γ)) →
  ofWNode Ω ns ≡ true →
  all (λ kv → ofWNode Ω (proj₂ kv)) nodes ≡ true →
  all (λ kv → ofWNode Ω (proj₂ kv)) (setNode nid ns nodes) ≡ true
setNode-ofW Ω nid ns []             bn h = ∧-intro bn refl
setNode-ofW Ω nid ns ((k , s′) ∷ r) bn h with k ≡ᵇ nid
... | true  = ∧-intro bn (proj₂ (∧-true _ _ h))
... | false = ∧-intro (proj₁ (∧-true _ _ h))
                      (setNode-ofW Ω nid ns r bn (proj₂ (∧-true _ _ h)))

install-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ω : ℕ)
  (sched : Sched Γ) (st : EvalSt e) (nid : NodeId) (ns : NodeState Γ) →
  ofWNode Ω ns ≡ true → widthOK? Ω sched st ≡ true →
  widthOK? Ω sched (installNode nid ns st) ≡ true
install-width Ω sched st nid ns bn h =
  ∧-intro (proj₁ P)
  (∧-intro (setNode-ofW Ω nid ns (EvalSt.nodes st) bn (proj₁ (proj₂ P)))
  (∧-intro (proj₁ (proj₂ (proj₂ P))) (proj₂ (proj₂ (proj₂ P)))))
  where P = WOK-parts Ω sched st h

-- registering a chain: one entry appended, its frames bounded by
-- hypothesis.  No length rider means no ledger edge at all — the
-- single place where the width walk is strictly cheaper than the
-- size walk rather than merely equal
register-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (Ω : ℕ) (src : Source) (κ : Path Γ u t)
  (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true → pathΩ? Ω κ ≡ true →
  widthOK? Ω sched (register src κ st) ≡ true
register-width {u = u} Ω src κ sched st h pκ =
  ∧-intro (proj₁ P)
  (∧-intro (proj₁ (proj₂ P))
  (∧-intro (all-++-intro _ (EvalSt.registry st) _
              (proj₁ (proj₂ (proj₂ P))) (∧-intro pκ refl))
           (proj₂ (proj₂ (proj₂ P)))))
  where P = WOK-parts Ω sched st h

addLive-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ω : ℕ)
  (sched : Sched Γ) (st : EvalSt e) (l : LiveSource Γ) →
  ofWLive Ω l ≡ true → widthOK? Ω sched st ≡ true →
  widthOK? Ω (record sched { live = l ∷ Sched.live sched }) st ≡ true
addLive-width Ω sched st l bl h =
  ∧-intro (∧-intro bl (proj₁ P))
  (∧-intro (proj₁ (proj₂ P))
  (∧-intro (proj₁ (proj₂ (proj₂ P))) (proj₂ (proj₂ (proj₂ P)))))
  where P = WOK-parts Ω sched st h

-- the live sweep, width face (mirror of sweepLive-bounded/-fnCap)
sweepLive-ofW : ∀ {n} {Γ : Ctx n} {t} (Ω : ℕ)
  (reg : List (RegId × Source × Chain Γ t)) (ls : List (LiveSource Γ)) →
  all (ofWLive Ω) ls ≡ true →
  all (ofWLive Ω) (sweepLive reg ls) ≡ true
sweepLive-ofW Ω reg []       h = refl
sweepLive-ofW {n = n} Ω reg (l ∷ ls) h
  with ∧-true (ofWLive Ω l) (all (ofWLive Ω) ls) h
... | bl , bls
  with (LiveSource.source l <ᵇ n)
       ∨ any (λ p → sameSource (LiveSource.source l) (proj₁ (proj₂ p))) reg
... | true  = ∧-intro bl (sweepLive-ofW Ω reg ls bls)
... | false = sweepLive-ofW Ω reg ls bls

-- dropping a source only shrinks the registry
dropSource-regsΩ : ∀ {n} {Γ : Ctx n} {t} (Ω : ℕ) (src : Source)
  (reg : List (RegId × Source × Chain Γ t)) →
  regsΩ? Ω reg ≡ true → regsΩ? Ω (dropSource src reg) ≡ true
dropSource-regsΩ Ω src []                  h = refl
dropSource-regsΩ Ω src ((rid , s , c) ∷ r) h with sameSource src s
... | true  = dropSource-regsΩ Ω src r (proj₂ (∧-true _ _ h))
... | false = ∧-intro (proj₁ (∧-true _ _ h))
                      (dropSource-regsΩ Ω src r (proj₂ (∧-true _ _ h)))

latch-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ω : ℕ)
  (src : Source) (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true →
  widthOK? Ω sched
    (record st { registry = dropSource src (EvalSt.registry st)
               ; completedSources = src ∷ EvalSt.completedSources st })
    ≡ true
latch-width Ω src sched st h =
  ∧-intro (proj₁ P)
  (∧-intro (proj₁ (proj₂ P))
  (∧-intro (dropSource-regsΩ Ω src (EvalSt.registry st)
              (proj₁ (proj₂ (proj₂ P))))
           (proj₂ (proj₂ (proj₂ P)))))
  where P = WOK-parts Ω sched st h

-- completedSources / dying / delivered / connectedShares are read
-- by no conjunct of widthOK? either
shareLatch-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ω : ℕ)
  (i : Fin n) (b : Bool) (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true → widthOK? Ω sched (shareLatch i b st) ≡ true
shareLatch-width Ω i false sched st h = h
shareLatch-width Ω i true  sched st h = h

delivered-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ω : ℕ)
  (rid : RegId) (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true →
  widthOK? Ω sched (record st { delivered = rid ∷ EvalSt.delivered st })
    ≡ true
delivered-width Ω rid sched st h = h

connectShare-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ω : ℕ)
  (src : Source) (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true →
  widthOK? Ω sched
    (record st { connectedShares = src ∷ EvalSt.connectedShares st }) ≡ true
connectShare-width Ω src sched st h = h

-- the admitted fan-out chains inherit their frame widths
shareAdmit-Ω : ∀ {n} {Γ : Ctx n} {t} (Ω : ℕ) (i : Fin n)
  (reg : List (RegId × Source × Chain Γ t)) → regsΩ? Ω reg ≡ true →
  all (λ rp → pathΩ? Ω (proj₂ rp)) (shareAdmit i reg) ≡ true
shareAdmit-Ω Ω i []                      h = refl
shareAdmit-Ω {Γ = Γ} Ω i ((rid , src , (u , q)) ∷ r) h
  with sameSource (toℕ i) src | u ≟ᵗ lookup Γ i
... | false | _        = shareAdmit-Ω Ω i r (proj₂ (∧-true (pathΩ? Ω q) _ h))
... | true  | no  _    = shareAdmit-Ω Ω i r (proj₂ (∧-true (pathΩ? Ω q) _ h))
... | true  | yes refl =
      ∧-intro (proj₁ (∧-true (pathΩ? Ω q) _ h))
              (shareAdmit-Ω Ω i r (proj₂ (∧-true (pathΩ? Ω q) _ h)))

shareFinish-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ω : ℕ)
  (i : Fin n) (b : Bool) (emits : Stream Γ t)
  (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true →
  widthOK? Ω (proj₁ (proj₂ (shareFinish i b (emits , sched , st))))
             (proj₂ (proj₂ (shareFinish i b (emits , sched , st)))) ≡ true
shareFinish-width Ω i false emits sched st h = h
shareFinish-width Ω i true  emits sched st h =
  ∧-intro (sweepLive-ofW Ω kept (Sched.live sched) (proj₁ P))
  (∧-intro (proj₁ (proj₂ P))
  (∧-intro (dropSource-regsΩ Ω (toℕ i) (EvalSt.registry st)
              (proj₁ (proj₂ (proj₂ P))))
           (proj₂ (proj₂ (proj₂ P)))))
  where
  kept = dropSource (toℕ i) (EvalSt.registry st)
  P    = WOK-parts Ω sched st h

------------------------------------------------------------------
-- (W11-A′) THE BURST HELPERS.  eventΩ? only constrains `value`, so
-- every marker list is refl and the real content is the value lists.
------------------------------------------------------------------

mapValue-Ω : ∀ {n} {Γ : Ctx n} (Ω : ℕ) (u : Ty) (vs : List (Val Γ u)) →
  all (λ v → ofWᵛ u v ≤ᵇ Ω) vs ≡ true →
  all (eventΩ? Ω) (map value vs) ≡ true
mapValue-Ω Ω u []       h = refl
mapValue-Ω Ω u (v ∷ vs) h =
  ∧-intro (proj₁ (∧-true _ _ h)) (mapValue-Ω Ω u vs (proj₂ (∧-true _ _ h)))

finList-Ω : ∀ {n} {Γ : Ctx n} {u} (Ω : ℕ) (b : Bool) →
  all (eventΩ? {n = n} {Γ = Γ} {u = u} Ω)
      (if b then complete ∷ [] else []) ≡ true
finList-Ω Ω true  = refl
finList-Ω Ω false = refl

closeList-Ω : ∀ {n} {Γ : Ctx n} {u} (Ω : ℕ) (src : Source) (b : Bool) →
  all (eventΩ? {n = n} {Γ = Γ} {u = u} Ω)
      (if b then close src exhausted ∷ [] else []) ≡ true
closeList-Ω Ω src true  = refl
closeList-Ω Ω src false = refl

sharedPlumb-Ω : ∀ {n} {Γ : Ctx n} {u} (Ω : ℕ) (str : Stream Γ u) →
  burstΩ? Ω str ≡ true → burstΩ? Ω (sharedPlumb str) ≡ true
sharedPlumb-Ω Ω []         h = refl
sharedPlumb-Ω Ω (em ∷ ems) h =
  ∧-intro (proj₁ (∧-true _ _ h)) (sharedPlumb-Ω Ω ems (proj₂ (∧-true _ _ h)))

-- a script's sync prefix, elementwise off the slot's ofW SUM (the
-- width seed is a sum dominating the max, exactly as ΨAt is)
sumVals-Ω : ∀ {n} {Γ : Ctx n} (Ω : ℕ) (u : Ty) (vs : List (Val Γ u)) →
  sum (map (ofWᵛ u) vs) ≤ Ω → all (λ v → ofWᵛ u v ≤ᵇ Ω) vs ≡ true
sumVals-Ω Ω u []       hw = refl
sumVals-Ω Ω u (v ∷ vs) hw =
  ∧-intro (T⇒≡true _ (≤⇒≤ᵇ (≤-trans (m≤m+n (ofWᵛ u v) _) hw)))
          (sumVals-Ω Ω u vs (≤-trans (m≤n+m _ (ofWᵛ u v)) hw))

-- one slot's width, projected out of widthOK?'s slots sum
slotOfW-at : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ω : ℕ)
  (i : Fin n) (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true → slotOfW (Sched.slots sched i) ≤ Ω
slotOfW-at Ω i sched st h =
  ≤-trans (fᵢ≤sum-tab (λ j → slotOfW (Sched.slots sched j)) i)
          (≤ᵇ⇒≤ _ _ (T-to (proj₂ (proj₂ (proj₂ (WOK-parts Ω sched st h))))))

------------------------------------------------------------------
-- (W11-B) THE FRAME ANALYTICS.  Every fact the frames need about
-- values, nodes and the registry, at the flat width.  These are the
-- W2/W4 mirrors with the ledger stripped: no caseW rider (widths
-- are substitution-invariant, so eval never widens), no capᴱ, no E.
------------------------------------------------------------------

applyFn-ofW : ∀ {n} {Γ : Ctx n} {s t} (Ω : ℕ)
  (fn : Fn Γ [] [] [] s t) (v : Val Γ s) →
  ofWᵛ s v ≤ Ω → ofWᵗ fn ≤ Ω → ofWᵛ t (applyFn fn v) ≤ Ω
applyFn-ofW Ω fn v hv hfn = ofW-evalWith Ω fn (v ∷ᵃ []ᵃ) (hv , tt) hfn

map-applyFn-Ω : ∀ {n} {Γ : Ctx n} {s u} (Ω : ℕ)
  (fn : Fn Γ [] [] [] s u) → ofWᵗ fn ≤ Ω →
  (vs : List (Val Γ s)) → all (λ v → ofWᵛ s v ≤ᵇ Ω) vs ≡ true →
  all (λ v → ofWᵛ u v ≤ᵇ Ω) (map (applyFn fn) vs) ≡ true
map-applyFn-Ω Ω fn hfn []       h = refl
map-applyFn-Ω {s = s} Ω fn hfn (v ∷ vs) h =
  ∧-intro (T⇒≡true _ (≤⇒≤ᵇ (applyFn-ofW Ω fn v
            (≤ᵇ⇒≤ _ _ (T-to (proj₁ (∧-true (ofWᵛ s v ≤ᵇ Ω) _ h)))) hfn)))
          (map-applyFn-Ω Ω fn hfn vs
            (proj₂ (∧-true (ofWᵛ s v ≤ᵇ Ω) _ h)))

-- one fold run: the accumulator and every output stay under Ω,
-- because applyFn never widens (ofW-evalWith)
scanVals-ofW : ∀ {n} {Γ : Ctx n} {s u} (Ω : ℕ)
  (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (ac : Val Γ u) (vs : List (Val Γ s)) →
  ofWᵗ fn ≤ Ω → ofWᵛ u ac ≤ Ω →
  all (λ v → ofWᵛ s v ≤ᵇ Ω) vs ≡ true →
  (ofWᵛ u (proj₂ (scanVals fn ac vs)) ≤ Ω)
  × (all (λ o → ofWᵛ u o ≤ᵇ Ω) (proj₁ (scanVals fn ac vs)) ≡ true)
scanVals-ofW Ω fn ac []       hfn hacc _ = hacc , refl
scanVals-ofW {s = s} Ω fn ac (v ∷ vs) hfn hacc h =
  proj₁ IH , ∧-intro (T⇒≡true _ (≤⇒≤ᵇ acc′OK)) (proj₂ IH)
  where
  hv     = ≤ᵇ⇒≤ _ _ (T-to (proj₁ (∧-true (ofWᵛ s v ≤ᵇ Ω) _ h)))
  acc′OK = applyFn-ofW Ω fn (ac , v) (⊔-lub hacc hv) hfn
  IH     = scanVals-ofW Ω fn (applyFn fn (ac , v)) vs hfn acc′OK
             (proj₂ (∧-true (ofWᵛ s v ≤ᵇ Ω) _ h))

takeVals-Ω : ∀ {n} {Γ : Ctx n} {s} (Ω : ℕ) (k : ℕ) (vals : List (Val Γ s)) →
  all (λ v → ofWᵛ s v ≤ᵇ Ω) vals ≡ true →
  all (λ v → ofWᵛ s v ≤ᵇ Ω) (proj₁ (takeVals k vals)) ≡ true
takeVals-Ω Ω zero          _        h = refl
takeVals-Ω Ω (suc k)       []       h = refl
takeVals-Ω Ω (suc zero)    (v ∷ vs) h = ∧-intro (proj₁ (∧-true _ _ h)) refl
takeVals-Ω Ω (suc (suc k)) (v ∷ vs) h =
  ∧-intro (proj₁ (∧-true _ _ h))
          (takeVals-Ω Ω (suc k) vs (proj₂ (∧-true _ _ h)))

cutThrough-regsΩ : ∀ {n} {Γ : Ctx n} {t} (Ω : ℕ) (nid : NodeId)
  (d : List RegId) (wm : RegId) (dy : List Source)
  (reg : List (RegId × Source × Chain Γ t)) →
  regsΩ? Ω reg ≡ true → regsΩ? Ω (proj₁ (cutThrough nid d wm dy reg)) ≡ true
cutThrough-regsΩ Ω nid d wm dy []                    h = refl
cutThrough-regsΩ Ω nid d wm dy ((rid , src , c) ∷ r) h
  with pathHasNode nid (proj₂ c) | cutThrough nid d wm dy r
     | cutThrough-regsΩ Ω nid d wm dy r (proj₂ (∧-true _ _ h))
... | true  | kept , closes , rids | ih = ih
... | false | kept , closes , rids | ih = ∧-intro (proj₁ (∧-true _ _ h)) ih

cutThrough-closesΩ : ∀ {n} {Γ : Ctx n} {t} (Ω : ℕ) (nid : NodeId)
  (d : List RegId) (wm : RegId) (dy : List Source)
  (reg : List (RegId × Source × Chain Γ t)) →
  all (eventΩ? Ω) (proj₁ (proj₂ (cutThrough nid d wm dy reg))) ≡ true
cutThrough-closesΩ Ω nid d wm dy []                    = refl
cutThrough-closesΩ Ω nid d wm dy ((rid , src , c) ∷ r)
  with pathHasNode nid (proj₂ c) | cutThrough nid d wm dy r
     | cutThrough-closesΩ Ω nid d wm dy r
... | false | kept , closes , rids | ih = ih
... | true  | kept , closes , rids | ih
      with any (_≡ᵇ rid) d ∧ memberSource src dy
...   | true  = ih
...   | false = ∧-intro refl ih

-- a node lookup carries the width face of whatever it finds
NodeΩ : ∀ {n} {Γ : Ctx n} → ℕ → Maybe (NodeState Γ) → Set
NodeΩ Ω nothing   = ⊤
NodeΩ Ω (just ns) = ofWNode Ω ns ≡ true

lookupNode-Ω : ∀ {n} {Γ : Ctx n} (Ω : ℕ) (nid : NodeId)
  (nodes : List (NodeId × NodeState Γ)) →
  all (λ kv → ofWNode Ω (proj₂ kv)) nodes ≡ true →
  NodeΩ Ω (lookupNode nid nodes)
lookupNode-Ω Ω nid []            h = tt
lookupNode-Ω Ω nid ((k , s) ∷ r) h with k ≡ᵇ nid
... | true  = proj₁ (∧-true _ _ h)
... | false = lookupNode-Ω Ω nid r (proj₂ (∧-true _ _ h))

-- splitting an emit / a whole burst
splitEvents-vals-Ω : ∀ {n} {Γ : Ctx n} {s u : Ty} (Ω : ℕ)
  (es : List (InstEvent (Val Γ s))) →
  all (eventΩ? Ω) es ≡ true →
  all (λ v → ofWᵛ s v ≤ᵇ Ω) (proj₁ (splitEvents {A = Val Γ u} es)) ≡ true
splitEvents-vals-Ω Ω []              h = refl
splitEvents-vals-Ω Ω (value v  ∷ es) h =
  ∧-intro (proj₁ (∧-true _ _ h)) (splitEvents-vals-Ω Ω es (proj₂ (∧-true _ _ h)))
splitEvents-vals-Ω Ω (init _   ∷ es) h = splitEvents-vals-Ω Ω es (proj₂ (∧-true _ _ h))
splitEvents-vals-Ω Ω (close _ _ ∷ es) h = splitEvents-vals-Ω Ω es (proj₂ (∧-true _ _ h))
splitEvents-vals-Ω Ω (handoff _ ∷ es) h = splitEvents-vals-Ω Ω es (proj₂ (∧-true _ _ h))
splitEvents-vals-Ω Ω (complete ∷ es) h = splitEvents-vals-Ω Ω es (proj₂ (∧-true _ _ h))

splitEvents-bk-Ω : ∀ {n} {Γ : Ctx n} {s u : Ty} (Ω : ℕ)
  (es : List (InstEvent (Val Γ s))) →
  all (eventΩ? Ω) (proj₁ (proj₂ (splitEvents {A = Val Γ u} es))) ≡ true
splitEvents-bk-Ω Ω []              = refl
splitEvents-bk-Ω {u = u} Ω (value v  ∷ es) = splitEvents-bk-Ω {u = u} Ω es
splitEvents-bk-Ω {u = u} Ω (init _   ∷ es) = ∧-intro refl (splitEvents-bk-Ω {u = u} Ω es)
splitEvents-bk-Ω {u = u} Ω (close _ _ ∷ es) = ∧-intro refl (splitEvents-bk-Ω {u = u} Ω es)
splitEvents-bk-Ω {u = u} Ω (handoff _ ∷ es) = ∧-intro refl (splitEvents-bk-Ω {u = u} Ω es)
splitEvents-bk-Ω {u = u} Ω (complete ∷ es) = splitEvents-bk-Ω {u = u} Ω es

splitBurst-vals-Ω : ∀ {n} {Γ : Ctx n} {s u : Ty} (Ω : ℕ) (str : Stream Γ s) →
  burstΩ? Ω str ≡ true →
  all (λ v → ofWᵛ s v ≤ᵇ Ω) (proj₁ (splitBurst {A = Val Γ u} str)) ≡ true
splitBurst-vals-Ω Ω []               h = refl
splitBurst-vals-Ω {Γ = Γ} {u = u} Ω (em ∷ ems) h =
  all-++-intro _ (proj₁ (splitEvents {A = Val Γ u} (InstEmit.events em))) _
    (splitEvents-vals-Ω Ω (InstEmit.events em) (proj₁ (∧-true _ _ h)))
    (splitBurst-vals-Ω {u = u} Ω ems (proj₂ (∧-true _ _ h)))

splitBurst-bk-Ω : ∀ {n} {Γ : Ctx n} {s u : Ty} (Ω : ℕ) (str : Stream Γ s) →
  all (eventΩ? Ω) (proj₁ (proj₂ (splitBurst {A = Val Γ u} str))) ≡ true
splitBurst-bk-Ω Ω []               = refl
splitBurst-bk-Ω {Γ = Γ} {u = u} Ω (em ∷ ems) =
  all-++-intro _ (proj₁ (proj₂ (splitEvents {A = Val Γ u} (InstEmit.events em)))) _
    (splitEvents-bk-Ω {u = u} Ω (InstEmit.events em))
    (splitBurst-bk-Ω {u = u} Ω ems)

-- retagging drops values, so the result is unconditionally clean
retag-Ω : ∀ {n} {Γ : Ctx n} {s u : Ty} (Ω : ℕ)
  (es : List (InstEvent (Val Γ s))) →
  all (eventΩ? {n = n} {Γ = Γ} {u = u} Ω) (retagEvents es) ≡ true
retag-Ω Ω []              = refl
retag-Ω {u = u} Ω (init _   ∷ es) = ∧-intro refl (retag-Ω {u = u} Ω es)
retag-Ω {u = u} Ω (close _ _ ∷ es) = ∧-intro refl (retag-Ω {u = u} Ω es)
retag-Ω {u = u} Ω (handoff _ ∷ es) = ∧-intro refl (retag-Ω {u = u} Ω es)
retag-Ω {u = u} Ω (complete ∷ es) = ∧-intro refl (retag-Ω {u = u} Ω es)
retag-Ω {u = u} Ω (value _  ∷ es) = retag-Ω {u = u} Ω es

-- mergeAll's counter bump and switchAll's cut, width faces
mergeBump-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ω : ℕ)
  (nid : NodeId) (d : Bool) (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true →
  widthOK? Ω sched (record st { nodes = mergeBump nid d (EvalSt.nodes st) })
    ≡ true
mergeBump-width Ω nid d sched st inv with lookupNode nid (EvalSt.nodes st)
... | just (merge-st k od)   = install-width Ω sched st nid
                                 (merge-st (if d then k else suc k) od) refl inv
... | nothing                = inv
... | just (scan-st _)       = inv
... | just (take-st _)       = inv
... | just (concat-st _ _ _) = inv
... | just (switch-st _ _)   = inv
... | just (exhaust-st _ _)  = inv

switchKill-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ω : ℕ)
  (cur : Maybe NodeId) (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true →
  let r = switchKill cur sched st
  in (widthOK? Ω (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (all (eventΩ? Ω) (proj₁ r) ≡ true)
switchKill-width Ω nothing  sched st inv = inv , refl
switchKill-width Ω (just v) sched st inv =
  ∧-intro (sweepLive-ofW Ω kept (Sched.live sched) (proj₁ P))
  (∧-intro (proj₁ (proj₂ P))
  (∧-intro (cutThrough-regsΩ Ω v del wm dy (EvalSt.registry st)
              (proj₁ (proj₂ (proj₂ P))))
           (proj₂ (proj₂ (proj₂ P))))) ,
  cutThrough-closesΩ Ω v del wm dy (EvalSt.registry st)
  where
  del  = EvalSt.delivered st
  wm   = EvalSt.regWatermark st
  dy   = EvalSt.dying st
  kept = proj₁ (cutThrough v del wm dy (EvalSt.registry st))
  P    = WOK-parts Ω sched st inv

-- the wrap: values and events pass through, only the *All node's
-- done flag is written back
thruWrap-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (Ω : ℕ) (op : AllOp) (nid : NodeId) (fin : Bool)
  (vs : List (Val Γ u)) (bs : List (InstEvent (Val Γ t)))
  (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true →
  all (λ v → ofWᵛ u v ≤ᵇ Ω) vs ≡ true →
  all (eventΩ? Ω) bs ≡ true →
  let r = thruWrap op nid fin (vs , bs , sched , st)
  in (widthOK? Ω (proj₁ (proj₂ (proj₂ (proj₂ r))))
                 (proj₂ (proj₂ (proj₂ (proj₂ r)))) ≡ true)
     × (all (λ v → ofWᵛ u v ≤ᵇ Ω) (proj₁ r) ≡ true)
     × (all (eventΩ? Ω) (proj₁ (proj₂ r)) ≡ true)
thruWrap-width Ω op nid false vs bs sched st inv vΩ bΩ = inv , vΩ , bΩ
thruWrap-width Ω mergeᵒ nid true vs bs sched st inv vΩ bΩ
  with lookupNode nid (EvalSt.nodes st)
... | just (merge-st k _)    =
      install-width Ω sched st nid (merge-st k true) refl inv , vΩ , bΩ
... | nothing                = inv , vΩ , bΩ
... | just (scan-st _)       = inv , vΩ , bΩ
... | just (take-st _)       = inv , vΩ , bΩ
... | just (concat-st _ _ _) = inv , vΩ , bΩ
... | just (switch-st _ _)   = inv , vΩ , bΩ
... | just (exhaust-st _ _)  = inv , vΩ , bΩ
thruWrap-width Ω concatᵒ nid true vs bs sched st inv vΩ bΩ
  with lookupNode nid (EvalSt.nodes st)
     | lookupNode-Ω Ω nid (EvalSt.nodes st)
         (proj₁ (proj₂ (WOK-parts Ω sched st inv)))
... | just (concat-st q act _) | nb =
      install-width Ω sched st nid (concat-st q act true) nb inv , vΩ , bΩ
... | nothing                | _ = inv , vΩ , bΩ
... | just (scan-st _)       | _ = inv , vΩ , bΩ
... | just (take-st _)       | _ = inv , vΩ , bΩ
... | just (merge-st _ _)    | _ = inv , vΩ , bΩ
... | just (switch-st _ _)   | _ = inv , vΩ , bΩ
... | just (exhaust-st _ _)  | _ = inv , vΩ , bΩ
thruWrap-width Ω switchᵒ nid true vs bs sched st inv vΩ bΩ
  with lookupNode nid (EvalSt.nodes st)
... | just (switch-st cur _) =
      install-width Ω sched st nid (switch-st cur true) refl inv , vΩ , bΩ
... | nothing                = inv , vΩ , bΩ
... | just (scan-st _)       = inv , vΩ , bΩ
... | just (take-st _)       = inv , vΩ , bΩ
... | just (merge-st _ _)    = inv , vΩ , bΩ
... | just (concat-st _ _ _) = inv , vΩ , bΩ
... | just (exhaust-st _ _)  = inv , vΩ , bΩ
thruWrap-width Ω exhaustᵒ nid true vs bs sched st inv vΩ bΩ
  with lookupNode nid (EvalSt.nodes st)
... | just (exhaust-st act _) =
      install-width Ω sched st nid (exhaust-st act true) refl inv , vΩ , bΩ
... | nothing                = inv , vΩ , bΩ
... | just (scan-st _)       = inv , vΩ , bΩ
... | just (take-st _)       = inv , vΩ , bΩ
... | just (merge-st _ _)    = inv , vΩ , bΩ
... | just (concat-st _ _ _) = inv , vΩ , bΩ
... | just (switch-st _ _)   = inv , vΩ , bΩ

------------------------------------------------------------------
-- the two SELF-CONTAINED frames: scan folds under Ω (applyFn never
-- widens), take passes a prefix through and, on the cutting emit,
-- runs cutThrough + sweepLive.  Neither re-enters subscribeE, so
-- both live outside the clique.
------------------------------------------------------------------

stepFrame-scan-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (Ω : ℕ) (g : Gas) (id : Id) (now : Tick)
  (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (nid : NodeId) (κ : Path Γ u t)
  (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true →
  frameΩ? Ω (scan-f fn nid) ≡ true →
  all (λ v → ofWᵛ s v ≤ᵇ Ω) vals ≡ true →
  let r = stepFrame g id now (scan-f fn nid) κ vals fin sched st
  in (widthOK? Ω (proj₁ (proj₂ (proj₂ (proj₂ r))))
                 (proj₂ (proj₂ (proj₂ (proj₂ r)))) ≡ true)
     × (all (λ v → ofWᵛ u v ≤ᵇ Ω) (proj₁ r) ≡ true)
     × (all (eventΩ? Ω) (proj₁ (proj₂ r)) ≡ true)
stepFrame-scan-width {s = s} {u = u} Ω g id now fn nid κ vals fin sched st
                     inv fΩ vΩ
  with lookupNode nid (EvalSt.nodes st)
     | lookupNode-Ω Ω nid (EvalSt.nodes st)
         (proj₁ (proj₂ (WOK-parts Ω sched st inv)))
... | nothing                | _ = inv , refl , refl
... | just (take-st _)       | _ = inv , refl , refl
... | just (merge-st _ _)    | _ = inv , refl , refl
... | just (concat-st _ _ _) | _ = inv , refl , refl
... | just (switch-st _ _)   | _ = inv , refl , refl
... | just (exhaust-st _ _)  | _ = inv , refl , refl
... | just (scan-st {w} ac)  | nb with w ≟ᵗ u
...   | no _    = inv , refl , refl
...   | yes refl =
  install-width Ω sched st nid (scan-st (proj₂ run))
    (T⇒≡true _ (≤⇒≤ᵇ (proj₁ run-ok))) inv ,
  proj₂ run-ok , refl
  where
  run    = scanVals fn ac vals
  ofwfn  : ofWᵗ fn ≤ Ω
  ofwfn  = ≤ᵇ⇒≤ _ _ (T-to fΩ)
  run-ok = scanVals-ofW Ω fn ac vals ofwfn (≤ᵇ⇒≤ _ _ (T-to nb)) vΩ

stepFrame-take-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (Ω : ℕ) (g : Gas) (id : Id) (now : Tick)
  (nid : NodeId) (κ : Path Γ s t)
  (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true →
  all (λ v → ofWᵛ s v ≤ᵇ Ω) vals ≡ true →
  let r = stepFrame g id now (take-f nid) κ vals fin sched st
  in (widthOK? Ω (proj₁ (proj₂ (proj₂ (proj₂ r))))
                 (proj₂ (proj₂ (proj₂ (proj₂ r)))) ≡ true)
     × (all (λ v → ofWᵛ s v ≤ᵇ Ω) (proj₁ r) ≡ true)
     × (all (eventΩ? Ω) (proj₁ (proj₂ r)) ≡ true)
stepFrame-take-width {s = s} Ω g id now nid κ vals fin sched st inv vΩ
  with lookupNode nid (EvalSt.nodes st)
... | nothing                = inv , refl , refl
... | just (scan-st _)       = inv , refl , refl
... | just (merge-st _ _)    = inv , refl , refl
... | just (concat-st _ _ _) = inv , refl , refl
... | just (switch-st _ _)   = inv , refl , refl
... | just (exhaust-st _ _)  = inv , refl , refl
... | just (take-st k) with proj₂ (proj₂ (takeVals k vals))
...   | false =
  install-width Ω sched st nid
    (take-st (proj₁ (proj₂ (takeVals k vals)))) refl inv ,
  takeVals-Ω Ω k vals vΩ , refl
...   | true =
  ∧-intro (sweepLive-ofW Ω kept (Sched.live sched) (proj₁ P))
  (∧-intro (setNode-ofW Ω nid (take-st zero) (EvalSt.nodes st) refl
              (proj₁ (proj₂ P)))
  (∧-intro (cutThrough-regsΩ Ω nid del wm dy (EvalSt.registry st)
              (proj₁ (proj₂ (proj₂ P))))
           (proj₂ (proj₂ (proj₂ P))))) ,
  takeVals-Ω Ω k vals vΩ ,
  cutThrough-closesΩ Ω nid del wm dy (EvalSt.registry st)
  where
  del  = EvalSt.delivered st
  wm   = EvalSt.regWatermark st
  dy   = EvalSt.dying st
  kept = proj₁ (cutThrough nid del wm dy (EvalSt.registry st))
  P    = WOK-parts Ω sched st inv

-- the connect's two landings, factored out of sharedConnect's `if`
connectWrap-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (Ω : ℕ) (i : Fin n) (id : Id) (c : Bool)
  (burst : Stream Γ (lookup Γ i)) (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true → burstΩ? Ω burst ≡ true →
  let r : Stream Γ (lookup Γ i) × Sched Γ × EvalSt e
      r = if c
          then (((init (toℕ i) ∷ close (toℕ i) exhausted ∷ [])
                  at id from toℕ i as subscribe) ∷ sharedPlumb burst)
               , sched
               , record st { registry = dropSource (toℕ i) (EvalSt.registry st)
                           ; completedSources = toℕ i ∷ EvalSt.completedSources st }
          else (((init (toℕ i) ∷ []) at id from toℕ i as subscribe) ∷ sharedPlumb burst)
               , sched , st
  in (widthOK? Ω (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstΩ? Ω (proj₁ r) ≡ true)
connectWrap-width Ω i id true  burst sched st inv bΩ =
  latch-width Ω (toℕ i) sched st inv ,
  ∧-intro refl (sharedPlumb-Ω Ω burst bΩ)
connectWrap-width Ω i id false burst sched st inv bΩ =
  inv , ∧-intro refl (sharedPlumb-Ω Ω burst bΩ)

-- of-list literals: eval never widens, so each element rides the
-- list's own ofWᵗˢ max
ofVals-Ω : ∀ {n} {Γ : Ctx n} {u} (Ω : ℕ) (ts : List (Tm Γ [] [] [] u)) →
  ofWᵗˢ ts ≤ Ω →
  all (λ v → ofWᵛ u v ≤ᵇ Ω) (map (λ tm → evalTm tm) ts) ≡ true
ofVals-Ω Ω []       h = refl
ofVals-Ω Ω (y ∷ ys) h =
  ∧-intro (T⇒≡true _ (≤⇒≤ᵇ (ofW-evalWith Ω y []ᵃ tt
            (≤-trans (m≤m⊔n (ofWᵗ y) (ofWᵗˢ ys)) h))))
          (ofVals-Ω Ω ys (≤-trans (m≤n⊔m (ofWᵗ y) (ofWᵗˢ ys)) h))


------------------------------------------------------------------
-- THE WIDTH WALK's entry point.  Its clause grind and the clique it
-- re-enters follow below; the delivery clique after that.
------------------------------------------------------------------

subscribeE-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (Ω : ℕ) (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (id : Id)
  (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true → ofWᵉ b ≤ Ω → pathΩ? Ω κ ≡ true →
  let r = subscribeE g b κ id now sched st
  in (widthOK? Ω (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstΩ? Ω (proj₁ r) ≡ true)

------------------------------------------------------------------
-- (W11-D) THE SUBSCRIPTION CLIQUE, width face.  Same shape as the
-- wet clique — subscribeE re-enters through subscribeAll/pushBurst,
-- through subscribeInner under the *All frames, and through a
-- share's connect — but with Ω flat the whole thing is one
-- preservation statement per clause.  The ONE width mint in the
-- machine is ofᵉ, and it mints exactly its own list, which the
-- entry seed already dominates.
------------------------------------------------------------------

subscribeAll-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (Ω : ℕ) (g : Gas) (op : AllOp) (ns : NodeState Γ)
  (b : Closed Γ (obs u)) (κ : Path Γ u t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true → ofWNode Ω ns ≡ true →
  ofWᵉ b ≤ Ω → pathΩ? Ω κ ≡ true →
  let r = subscribeAll g op ns b κ id now sched st
  in (widthOK? Ω (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstΩ? Ω (proj₁ r) ≡ true)

pushBurst-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (Ω : ℕ) (g : Gas) (id : Id) (now : Tick)
  (f : Frame Γ s u) (κ : Path Γ u t) (str : Stream Γ s)
  (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true →
  frameΩ? Ω f ≡ true → pathΩ? Ω κ ≡ true → burstΩ? Ω str ≡ true →
  let r = pushBurst g id now f κ str sched st
  in (widthOK? Ω (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstΩ? Ω (proj₁ r) ≡ true)

stepFrame-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (Ω : ℕ) (g : Gas) (id : Id) (now : Tick)
  (f : Frame Γ s u) (κ : Path Γ u t)
  (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true →
  frameΩ? Ω f ≡ true → pathΩ? Ω κ ≡ true →
  all (λ v → ofWᵛ s v ≤ᵇ Ω) vals ≡ true →
  let r = stepFrame g id now f κ vals fin sched st
  in (widthOK? Ω (proj₁ (proj₂ (proj₂ (proj₂ r))))
                 (proj₂ (proj₂ (proj₂ (proj₂ r)))) ≡ true)
     × (all (λ v → ofWᵛ u v ≤ᵇ Ω) (proj₁ r) ≡ true)
     × (all (eventΩ? Ω) (proj₁ (proj₂ r)) ≡ true)

subscribeInner-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (Ω : ℕ) (g : Gas) (op : AllOp) (allNid : NodeId) (κ : Path Γ u t)
  (id : Id) (now : Tick) (o : Val Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true →
  (ofWᵛ (obs u) o ≤ᵇ Ω) ≡ true → pathΩ? Ω κ ≡ true →
  let r = subscribeInner g op allNid κ id now o sched st
  in (widthOK? Ω (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r)))))
                 (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r))))) ≡ true)
     × (all (λ v → ofWᵛ u v ≤ᵇ Ω) (proj₁ (proj₂ r)) ≡ true)
     × (all (eventΩ? Ω) (proj₁ (proj₂ (proj₂ r))) ≡ true)

thruConsume-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (Ω : ℕ) (g : Gas) (op : AllOp) (nid : NodeId) (κ : Path Γ u t)
  (id : Id) (now : Tick) (o : Val Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true →
  (ofWᵛ (obs u) o ≤ᵇ Ω) ≡ true → pathΩ? Ω κ ≡ true →
  let r = thruConsume g op nid κ id now o sched st
  in (widthOK? Ω (proj₁ (proj₂ (proj₂ r))) (proj₂ (proj₂ (proj₂ r))) ≡ true)
     × (all (λ v → ofWᵛ u v ≤ᵇ Ω) (proj₁ r) ≡ true)
     × (all (eventΩ? Ω) (proj₁ (proj₂ r)) ≡ true)

thruWalk-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (Ω : ℕ) (g : Gas) (op : AllOp) (nid : NodeId) (κ : Path Γ u t)
  (id : Id) (now : Tick) (vals : List (Val Γ (obs u)))
  (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true → pathΩ? Ω κ ≡ true →
  all (λ v → ofWᵛ (obs u) v ≤ᵇ Ω) vals ≡ true →
  let r = thruWalk g op nid κ id now vals sched st
  in (widthOK? Ω (proj₁ (proj₂ (proj₂ r))) (proj₂ (proj₂ (proj₂ r))) ≡ true)
     × (all (λ v → ofWᵛ u v ≤ᵇ Ω) (proj₁ r) ≡ true)
     × (all (eventΩ? Ω) (proj₁ (proj₂ r)) ≡ true)

concatDrain-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (Ω : ℕ) (g : Gas) (allNid : NodeId) (κ : Path Γ s t)
  (id : Id) (now : Tick) (q : List (Closed Γ s))
  (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true → pathΩ? Ω κ ≡ true →
  all (λ o → ofWᵉ o ≤ᵇ Ω) q ≡ true →
  let r = concatDrain g allNid κ id now q sched st
  in (widthOK? Ω (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r)))))
                 (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r))))) ≡ true)
     × (all (λ v → ofWᵛ s v ≤ᵇ Ω) (proj₁ r) ≡ true)
     × (all (eventΩ? Ω) (proj₁ (proj₂ r)) ≡ true)
     × (all (λ o → ofWᵉ o ≤ᵇ Ω) (proj₁ (proj₂ (proj₂ (proj₂ r)))) ≡ true)

innerFinish-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (Ω : ℕ) (g : Gas) (op : AllOp) (allNid inst : NodeId) (κ : Path Γ s t)
  (id : Id) (now : Tick) (vals : List (Val Γ s))
  (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true → pathΩ? Ω κ ≡ true →
  all (λ v → ofWᵛ s v ≤ᵇ Ω) vals ≡ true →
  let r = innerFinish g op allNid inst κ id now vals sched st
            (lookupNode allNid (EvalSt.nodes st))
  in (widthOK? Ω (proj₁ (proj₂ (proj₂ (proj₂ r))))
                 (proj₂ (proj₂ (proj₂ (proj₂ r)))) ≡ true)
     × (all (λ v → ofWᵛ s v ≤ᵇ Ω) (proj₁ r) ≡ true)
     × (all (eventΩ? Ω) (proj₁ (proj₂ r)) ≡ true)

subscribeE-input-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (Ω : ℕ) (g : Gas) (i : Fin n) (κ : Path Γ (lookup Γ i) t)
  (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true → pathΩ? Ω κ ≡ true →
  let r = subscribeE g (input i) κ id now sched st
  in (widthOK? Ω (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstΩ? Ω (proj₁ r) ≡ true)

sharedSlot-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (Ω : ℕ) (g : Gas) (i : Fin n) (d : Closed Γ (lookup Γ i))
  (κ : Path Γ (lookup Γ i) t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true → ofWᵉ d ≤ Ω → pathΩ? Ω κ ≡ true →
  let r = subscribeSharedSlot g i d κ id now sched st
  in (widthOK? Ω (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstΩ? Ω (proj₁ r) ≡ true)

sharedConnect-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (Ω : ℕ) (g : Gas) (i : Fin n) (d : Closed Γ (lookup Γ i))
  (κ : Path Γ (lookup Γ i) t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true → ofWᵉ d ≤ Ω → pathΩ? Ω κ ≡ true →
  let r = sharedConnect g i d κ id now sched st
  in (widthOK? Ω (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstΩ? Ω (proj₁ r) ≡ true)

------------------------------------------------------------------
-- the *All shape: mint, install, subscribe under the thru-outer
-- frame, push the burst
------------------------------------------------------------------

subscribeAll-width Ω g op ns b κ id now sched st inv nΩ bΩ pΩ =
  pushBurst-width Ω g id now (thru-outer op nid) κ (proj₁ sE)
    (proj₁ (proj₂ sE)) (proj₂ (proj₂ sE)) (proj₁ IH) refl pΩ (proj₂ IH)
  where
  nid    = Sched.nextNode sched
  sched₁ = proj₂ (mintNode sched)
  st₀    = installNode nid ns st
  sE     = subscribeE g b (thru-outer op nid ↠ κ) id now sched₁ st₀
  IH     = subscribeE-width Ω g b (thru-outer op nid ↠ κ) id now sched₁ st₀
             (install-width Ω sched₁ st nid ns nΩ inv) bΩ (∧-intro refl pΩ)

------------------------------------------------------------------
-- the burst re-entry: split each emit, step its frame, reassemble
------------------------------------------------------------------

pushBurst-width Ω g id now f κ [] sched st inv fΩ pΩ bΩ = inv , refl
pushBurst-width {Γ = Γ} {s = s} {u = u} Ω g id now f κ (em ∷ ems) sched st
                inv fΩ pΩ bΩ =
  proj₁ IH ,
  ∧-intro
    (all-++-intro _ (proj₁ (proj₂ sp)) _
      (splitEvents-bk-Ω {u = u} Ω (InstEmit.events em))
      (all-++-intro _ (retagEvents (proj₁ (proj₂ SF))) _
        (retag-Ω {u = u} Ω (proj₁ (proj₂ SF)))
        (all-++-intro _ (map value (proj₁ SF)) _
          (mapValue-Ω Ω u (proj₁ SF) (proj₁ (proj₂ SFw)))
          (finList-Ω Ω (proj₁ (proj₂ (proj₂ SF)))))))
    (proj₂ IH)
  where
  sp  = splitEvents {A = Val Γ u} (InstEmit.events em)
  SF  = stepFrame g id now f κ (proj₁ sp) (proj₂ (proj₂ sp)) sched st
  SFw = stepFrame-width Ω g id now f κ (proj₁ sp) (proj₂ (proj₂ sp)) sched st
          inv fΩ pΩ
          (splitEvents-vals-Ω {u = u} Ω (InstEmit.events em)
            (proj₁ (∧-true _ _ bΩ)))
  IH  = pushBurst-width Ω g id now f κ ems
          (proj₁ (proj₂ (proj₂ (proj₂ SF))))
          (proj₂ (proj₂ (proj₂ (proj₂ SF))))
          (proj₁ SFw) fΩ pΩ (proj₂ (∧-true _ _ bΩ))

------------------------------------------------------------------
-- the frame dispatch: map is the one real computation (and even it
-- cannot widen), scan and take are proven above, the two *All
-- frames re-enter the clique
------------------------------------------------------------------

stepFrame-width Ω g id now (map-f fn) κ vals fin sched st inv fΩ pΩ vΩ =
  inv , map-applyFn-Ω Ω fn (≤ᵇ⇒≤ _ _ (T-to fΩ)) vals vΩ , refl
stepFrame-width Ω g id now (scan-f fn nid) κ vals fin sched st inv fΩ pΩ vΩ =
  stepFrame-scan-width Ω g id now fn nid κ vals fin sched st inv fΩ vΩ
stepFrame-width Ω g id now (take-f nid) κ vals fin sched st inv fΩ pΩ vΩ =
  stepFrame-take-width Ω g id now nid κ vals fin sched st inv vΩ
stepFrame-width Ω g id now (from-inner op allNid inst) κ vals false sched st
                inv fΩ pΩ vΩ = inv , vΩ , refl
stepFrame-width Ω g id now (from-inner op allNid inst) κ vals true sched st
                inv fΩ pΩ vΩ
  with any (aliveThroughᶠ inst st) (EvalSt.registry st)
... | true  = inv , vΩ , refl
... | false = innerFinish-width Ω g op allNid inst κ id now vals sched st
                inv pΩ vΩ
stepFrame-width Ω g id now (thru-outer op nid) κ vals fin sched st
                inv fΩ pΩ vΩ =
  thruWrap-width Ω op nid fin (proj₁ wr) (proj₁ (proj₂ wr))
    (proj₁ (proj₂ (proj₂ wr))) (proj₂ (proj₂ (proj₂ wr)))
    (proj₁ WK) (proj₁ (proj₂ WK)) (proj₂ (proj₂ WK))
  where
  wr = thruWalk g op nid κ id now vals sched st
  WK = thruWalk-width Ω g op nid κ id now vals sched st inv pΩ vΩ

------------------------------------------------------------------
-- one inner subscription: g0 is the dry stub, gs re-enters
------------------------------------------------------------------

subscribeInner-width Ω g0 op allNid κ id now o sched st inv oΩ pΩ =
  inv , refl , refl
subscribeInner-width {t = t} {u = u} Ω (gs fuel) op allNid κ id now o sched st
                     inv oΩ pΩ =
  proj₁ IH ,
  splitBurst-vals-Ω {s = u} {u = t} Ω (proj₁ sE) (proj₂ IH) ,
  splitBurst-bk-Ω {s = u} {u = t} Ω (proj₁ sE)
  where
  inst   = Sched.nextNode sched
  sched₀ = record sched { nextNode = suc inst }
  sE     = subscribeE fuel o (from-inner op allNid inst ↠ κ) id now sched₀ st
  IH     = subscribeE-width Ω fuel o (from-inner op allNid inst ↠ κ) id now
             sched₀ st inv (≤ᵇ⇒≤ _ _ (T-to oΩ)) (∧-intro refl pΩ)

------------------------------------------------------------------
-- the outer *All walk, one emitted inner at a time
------------------------------------------------------------------

thruConsume-width Ω g mergeᵒ nid κ id now o sched st inv oΩ pΩ =
  mergeBump-width Ω nid done sched₁ st₁ (proj₁ SI) ,
  proj₁ (proj₂ SI) , proj₂ (proj₂ SI)
  where
  SI     = subscribeInner-width Ω g mergeᵒ nid κ id now o sched st inv oΩ pΩ
  SI₄    = subscribeInner g mergeᵒ nid κ id now o sched st
  done   = proj₁ (proj₂ (proj₂ (proj₂ SI₄)))
  sched₁ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ SI₄))))
  st₁    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SI₄))))
thruConsume-width {u = u} Ω g concatᵒ nid κ id now o sched st inv oΩ pΩ
  with lookupNode nid (EvalSt.nodes st)
     | lookupNode-Ω Ω nid (EvalSt.nodes st)
         (proj₁ (proj₂ (WOK-parts Ω sched st inv)))
... | just (concat-st {w} q true od) | nb with w ≟ᵗ u
...   | yes refl =
  install-width Ω sched st nid (concat-st (q ++ o ∷ []) true od)
    (all-++-intro _ q _ nb (∧-intro oΩ refl)) inv ,
  refl , refl
...   | no _ = inv , refl , refl
thruConsume-width {u = u} Ω g concatᵒ nid κ id now o sched st inv oΩ pΩ
    | just (concat-st q false od) | nb =
  install-width Ω (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ SI₄))))) st₁ nid
    (concat-st {t = u} [] (not done) od) refl (proj₁ SI) ,
  proj₁ (proj₂ SI) , proj₂ (proj₂ SI)
  where
  SI   = subscribeInner-width Ω g concatᵒ nid κ id now o sched st inv oΩ pΩ
  SI₄  = subscribeInner g concatᵒ nid κ id now o sched st
  done = proj₁ (proj₂ (proj₂ (proj₂ SI₄)))
  st₁  = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SI₄))))
thruConsume-width Ω g concatᵒ nid κ id now o sched st inv oΩ pΩ
    | nothing | _ = inv , refl , refl
thruConsume-width Ω g concatᵒ nid κ id now o sched st inv oΩ pΩ
    | just (scan-st _) | _ = inv , refl , refl
thruConsume-width Ω g concatᵒ nid κ id now o sched st inv oΩ pΩ
    | just (take-st _) | _ = inv , refl , refl
thruConsume-width Ω g concatᵒ nid κ id now o sched st inv oΩ pΩ
    | just (merge-st _ _) | _ = inv , refl , refl
thruConsume-width Ω g concatᵒ nid κ id now o sched st inv oΩ pΩ
    | just (switch-st _ _) | _ = inv , refl , refl
thruConsume-width Ω g concatᵒ nid κ id now o sched st inv oΩ pΩ
    | just (exhaust-st _ _) | _ = inv , refl , refl
thruConsume-width Ω g switchᵒ nid κ id now o sched st inv oΩ pΩ
  with lookupNode nid (EvalSt.nodes st)
... | just (switch-st cur od) =
  install-width Ω (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ SI₄))))) st₂ nid
    (switch-st (if done then nothing else just inst) od) refl (proj₁ SI) ,
  proj₁ (proj₂ SI) ,
  all-++-intro _ closes _ (proj₂ KL) (proj₂ (proj₂ SI))
  where
  KL     = switchKill-width Ω cur sched st inv
  closes = proj₁ (switchKill cur sched st)
  sched₁ = proj₁ (proj₂ (switchKill cur sched st))
  st₁    = proj₂ (proj₂ (switchKill cur sched st))
  SI     = subscribeInner-width Ω g switchᵒ nid κ id now o sched₁ st₁
             (proj₁ KL) oΩ pΩ
  SI₄    = subscribeInner g switchᵒ nid κ id now o sched₁ st₁
  inst   = proj₁ SI₄
  done   = proj₁ (proj₂ (proj₂ (proj₂ SI₄)))
  st₂    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SI₄))))
... | nothing                = inv , refl , refl
... | just (scan-st _)       = inv , refl , refl
... | just (take-st _)       = inv , refl , refl
... | just (merge-st _ _)    = inv , refl , refl
... | just (concat-st _ _ _) = inv , refl , refl
... | just (exhaust-st _ _)  = inv , refl , refl
thruConsume-width Ω g exhaustᵒ nid κ id now o sched st inv oΩ pΩ
  with lookupNode nid (EvalSt.nodes st)
... | just (exhaust-st true od)  = inv , refl , refl
... | just (exhaust-st false od) =
  install-width Ω (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ SI₄))))) st₁ nid
    (exhaust-st (not done) od) refl (proj₁ SI) ,
  proj₁ (proj₂ SI) , proj₂ (proj₂ SI)
  where
  SI   = subscribeInner-width Ω g exhaustᵒ nid κ id now o sched st inv oΩ pΩ
  SI₄  = subscribeInner g exhaustᵒ nid κ id now o sched st
  done = proj₁ (proj₂ (proj₂ (proj₂ SI₄)))
  st₁  = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SI₄))))
... | nothing                = inv , refl , refl
... | just (scan-st _)       = inv , refl , refl
... | just (take-st _)       = inv , refl , refl
... | just (merge-st _ _)    = inv , refl , refl
... | just (concat-st _ _ _) = inv , refl , refl
... | just (switch-st _ _)   = inv , refl , refl

thruWalk-width Ω g op nid κ id now [] sched st inv pΩ vΩ = inv , refl , refl
thruWalk-width {u = u} Ω g op nid κ id now (o ∷ os) sched st inv pΩ vΩ =
  proj₁ IH ,
  all-++-intro _ (proj₁ cr) _ (proj₁ (proj₂ CS)) (proj₁ (proj₂ IH)) ,
  all-++-intro _ (proj₁ (proj₂ cr)) _ (proj₂ (proj₂ CS)) (proj₂ (proj₂ IH))
  where
  CS = thruConsume-width Ω g op nid κ id now o sched st inv
         (proj₁ (∧-true _ _ vΩ)) pΩ
  cr = thruConsume g op nid κ id now o sched st
  IH = thruWalk-width Ω g op nid κ id now os
         (proj₁ (proj₂ (proj₂ cr))) (proj₂ (proj₂ (proj₂ cr)))
         (proj₁ CS) pΩ (proj₂ (∧-true _ _ vΩ))

------------------------------------------------------------------
-- the inner *All frame's drain and finish
------------------------------------------------------------------

concatDrain-width Ω g allNid κ id now [] sched st inv pΩ qΩ =
  inv , refl , refl , refl
concatDrain-width {s = s} Ω g allNid κ id now (o ∷ q) sched st inv pΩ qΩ
  with subscribeInner g concatᵒ allNid κ id now o sched st
     | subscribeInner-width Ω g concatᵒ allNid κ id now o sched st inv
         (proj₁ (∧-true (ofWᵉ o ≤ᵇ Ω) _ qΩ)) pΩ
... | (_ , vs , bs , false , sched₁ , st₁) | (inv₁ , vsΩ , bsΩ) =
  inv₁ , vsΩ , bsΩ , proj₂ (∧-true (ofWᵉ o ≤ᵇ Ω) _ qΩ)
... | (_ , vs , bs , true , sched₁ , st₁) | (inv₁ , vsΩ , bsΩ) =
  proj₁ IH ,
  all-++-intro _ vs _ vsΩ (proj₁ (proj₂ IH)) ,
  all-++-intro _ bs _ bsΩ (proj₁ (proj₂ (proj₂ IH))) ,
  proj₂ (proj₂ (proj₂ IH))
  where
  IH = concatDrain-width Ω g allNid κ id now q sched₁ st₁ inv₁ pΩ
         (proj₂ (∧-true (ofWᵉ o ≤ᵇ Ω) _ qΩ))

innerFinish-width Ω g mergeᵒ allNid inst κ id now vals sched st inv pΩ vΩ
  with lookupNode allNid (EvalSt.nodes st)
... | just (merge-st k od)   =
  install-width Ω sched st allNid (merge-st (pred k) od) refl inv , vΩ , refl
... | nothing                = inv , vΩ , refl
... | just (scan-st _)       = inv , vΩ , refl
... | just (take-st _)       = inv , vΩ , refl
... | just (concat-st _ _ _) = inv , vΩ , refl
... | just (switch-st _ _)   = inv , vΩ , refl
... | just (exhaust-st _ _)  = inv , vΩ , refl
innerFinish-width {s = s} Ω g concatᵒ allNid inst κ id now vals sched st
                  inv pΩ vΩ
  with lookupNode allNid (EvalSt.nodes st)
     | lookupNode-Ω Ω allNid (EvalSt.nodes st)
         (proj₁ (proj₂ (WOK-parts Ω sched st inv)))
... | just (concat-st {w} q act od) | nb with w ≟ᵗ s
...   | yes refl =
  install-width Ω sched′ st′ allNid (concat-st q′ act′ od)
    (proj₂ (proj₂ (proj₂ DR))) (proj₁ DR) ,
  all-++-intro _ vals _ vΩ (proj₁ (proj₂ DR)) ,
  proj₁ (proj₂ (proj₂ DR))
  where
  DR     = concatDrain-width Ω g allNid κ id now q sched st inv pΩ nb
  dr     = concatDrain g allNid κ id now q sched st
  act′   = proj₁ (proj₂ (proj₂ dr))
  q′     = proj₁ (proj₂ (proj₂ (proj₂ dr)))
  sched′ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ dr))))
  st′    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ dr))))
...   | no _ = inv , vΩ , refl
innerFinish-width Ω g concatᵒ allNid inst κ id now vals sched st inv pΩ vΩ
    | nothing               | _ = inv , vΩ , refl
innerFinish-width Ω g concatᵒ allNid inst κ id now vals sched st inv pΩ vΩ
    | just (scan-st _)      | _ = inv , vΩ , refl
innerFinish-width Ω g concatᵒ allNid inst κ id now vals sched st inv pΩ vΩ
    | just (take-st _)      | _ = inv , vΩ , refl
innerFinish-width Ω g concatᵒ allNid inst κ id now vals sched st inv pΩ vΩ
    | just (merge-st _ _)   | _ = inv , vΩ , refl
innerFinish-width Ω g concatᵒ allNid inst κ id now vals sched st inv pΩ vΩ
    | just (switch-st _ _)  | _ = inv , vΩ , refl
innerFinish-width Ω g concatᵒ allNid inst κ id now vals sched st inv pΩ vΩ
    | just (exhaust-st _ _) | _ = inv , vΩ , refl
innerFinish-width Ω g switchᵒ allNid inst κ id now vals sched st inv pΩ vΩ
  with lookupNode allNid (EvalSt.nodes st)
... | just (switch-st (just c) od) with c ≡ᵇ inst
...   | true  =
  install-width Ω sched st allNid (switch-st nothing od) refl inv , vΩ , refl
...   | false = inv , vΩ , refl
innerFinish-width Ω g switchᵒ allNid inst κ id now vals sched st inv pΩ vΩ
    | just (switch-st nothing od) = inv , vΩ , refl
innerFinish-width Ω g switchᵒ allNid inst κ id now vals sched st inv pΩ vΩ
    | nothing                = inv , vΩ , refl
innerFinish-width Ω g switchᵒ allNid inst κ id now vals sched st inv pΩ vΩ
    | just (scan-st _)       = inv , vΩ , refl
innerFinish-width Ω g switchᵒ allNid inst κ id now vals sched st inv pΩ vΩ
    | just (take-st _)       = inv , vΩ , refl
innerFinish-width Ω g switchᵒ allNid inst κ id now vals sched st inv pΩ vΩ
    | just (merge-st _ _)    = inv , vΩ , refl
innerFinish-width Ω g switchᵒ allNid inst κ id now vals sched st inv pΩ vΩ
    | just (concat-st _ _ _) = inv , vΩ , refl
innerFinish-width Ω g switchᵒ allNid inst κ id now vals sched st inv pΩ vΩ
    | just (exhaust-st _ _)  = inv , vΩ , refl
innerFinish-width Ω g exhaustᵒ allNid inst κ id now vals sched st inv pΩ vΩ
  with lookupNode allNid (EvalSt.nodes st)
... | just (exhaust-st act od) =
  install-width Ω sched st allNid (exhaust-st false od) refl inv , vΩ , refl
... | nothing                = inv , vΩ , refl
... | just (scan-st _)       = inv , vΩ , refl
... | just (take-st _)       = inv , vΩ , refl
... | just (merge-st _ _)    = inv , vΩ , refl
... | just (concat-st _ _ _) = inv , vΩ , refl
... | just (switch-st _ _)   = inv , vΩ , refl

------------------------------------------------------------------
-- THE INPUT CLAUSE, width face.  slotOfW-at cuts the one slot's
-- width out of widthOK?'s slots sum; that is all the clause knows.
------------------------------------------------------------------

sharedSlot-width Ω g i d κ id now sched st inv dΩ pΩ
  with memberSource (toℕ i) (EvalSt.completedSources st)
... | true  = inv , refl
... | false with memberSource (toℕ i) (EvalSt.connectedShares st)
...   | true  = register-width Ω (toℕ i) κ sched st inv pΩ , refl
...   | false = sharedConnect-width Ω g i d κ id now sched st inv dΩ pΩ

sharedConnect-width Ω g0 i d κ id now sched st inv dΩ pΩ = inv , refl
sharedConnect-width Ω (gs fuel) i d κ id now sched st inv dΩ pΩ =
  connectWrap-width Ω i id (burstCompleted (proj₁ SE))
    (proj₁ SE) (proj₁ (proj₂ SE)) (proj₂ (proj₂ SE)) (proj₁ IH) (proj₂ IH)
  where
  st₀  = record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st }
  st₁  = register (toℕ i) κ st₀
  inv₁ = register-width Ω (toℕ i) κ sched st₀
           (connectShare-width Ω (toℕ i) sched st inv) pΩ
  IH   = subscribeE-width Ω fuel d (share-sink i) id now sched st₁ inv₁ dΩ refl
  SE   = subscribeE fuel d (share-sink i) id now sched st₁

subscribeE-input-width {Γ = Γ} Ω g i κ id now sched st inv pΩ
  with Sched.slots sched i | slotOfW-at Ω i sched st inv

-- a shared def: connect once, ever; then join
... | shared d | dΩ = sharedSlot-width Ω g i d κ id now sched st inv dΩ pΩ

-- a cold with no async tail: born and spent inside its own burst
... | scripted (cold sy []) | sΩ =
      inv ,
      ∧-intro
        (all-++-intro _ (map value sy) _
          (mapValue-Ω Ω (lookup Γ i) sy
            (sumVals-Ω Ω (lookup Γ i) sy (≤-trans (m≤m+n _ 0) sΩ)))
          refl)
        refl

-- a cold WITH a tail: fresh source and ordinal, the tail resolved
-- against this subscription's tick, one registration
... | scripted (cold sy (tv ∷ tvs)) | sΩ =
      register-width Ω src κ sched₃ st inv₃ pΩ ,
      ∧-intro (mapValue-Ω Ω (lookup Γ i) sy syΩ) refl
      where
      src    = Sched.nextSource sched
      sched₁ = proj₂ (mintSource sched)
      ord    = Sched.nextOrdinal sched₁
      sched₂ = proj₂ (mintOrdinal sched₁)
      anchored : LiveSource Γ
      anchored = record { source = src ; ordinal = ord ; elemTy = lookup Γ i
                        ; pending = resolve now (tv ∷ tvs) }
      sched₃ = record sched₂ { live = anchored ∷ Sched.live sched₂ }
      -- both summands named: nothing can recover the sync side by
      -- inverting _+_
      syncW  = sum (map (ofWᵛ (lookup Γ i)) sy)
      tailW  = sum (map (λ p → ofWᵛ (lookup Γ i) (Timed.val p)) (tv ∷ tvs))
      syΩ    = sumVals-Ω Ω (lookup Γ i) sy (≤-trans (m≤m+n syncW tailW) sΩ)
      inv₃   = addLive-width Ω sched₂ st anchored
                 (resolve-measure (ofWᵛ (lookup Γ i)) Ω now (tv ∷ tvs)
                   (≤-trans (m≤n+m tailW syncW) sΩ))
                 inv

-- a hot: already live at the slot's own source/ordinal
... | scripted (hot _) | sΩ
      with memberSource (toℕ i) (EvalSt.completedSources st)
...   | true  = inv , refl
...   | false = register-width Ω (toℕ i) κ sched st inv pΩ , refl

------------------------------------------------------------------
-- deferᵉ: mint a node, a source and an ordinal, install the merge
-- node, park the BODY as the lone pending value of a fresh live
-- source, register the outer chain.  A parked obs value's width IS
-- the body's own, so the live entry needs no arithmetic.
------------------------------------------------------------------

subscribeE-defer-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (Ω : ℕ) (g : Gas) (body : Closed Γ u) (κ : Path Γ u t)
  (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true → ofWᵉ body ≤ Ω → pathΩ? Ω κ ≡ true →
  let r = subscribeE g (deferᵉ body) κ id now sched st
  in (widthOK? Ω (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstΩ? Ω (proj₁ r) ≡ true)
subscribeE-defer-width {Γ = Γ} {u = u} Ω g body κ id now sched st inv bΩ pΩ =
  register-width Ω src (thru-outer mergeᵒ nid ↠ κ) sched₄ st₀ inv₂
    (∧-intro refl pΩ) ,
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
  st₀    = installNode nid (merge-st 0 false) st
  inv₂   = addLive-width Ω sched₃ st₀ hop
             (∧-intro (T⇒≡true _ (≤⇒≤ᵇ bΩ)) refl)
             (install-width Ω sched₃ st nid (merge-st 0 false) refl inv)

------------------------------------------------------------------
-- THE WIDTH WALK ITSELF.  Thirteen clauses, each a ⊔-projection of
-- the entry bound: ofᵉ is the only width MINT and it mints exactly
-- its own list; every other clause hands its sub-bound down.
------------------------------------------------------------------

subscribeE-width Ω g (input i) κ id now sched st inv bΩ pΩ =
  subscribeE-input-width Ω g i κ id now sched st inv pΩ

subscribeE-width {Γ = Γ} {u = u} Ω g (ofᵉ ts) κ id now sched st inv bΩ pΩ =
  inv ,
  ∧-intro
    (∧-intro refl
      (all-++-intro _ (map value (map (λ tm → evalTm tm) ts)) _
        (mapValue-Ω Ω u (map (λ tm → evalTm tm) ts)
          (ofVals-Ω Ω ts (≤-trans (m≤n⊔m (length ts) (ofWᵗˢ ts)) bΩ)))
        refl))
    refl

subscribeE-width Ω g emptyᵉ κ id now sched st inv bΩ pΩ = inv , refl

subscribeE-width Ω g (mapᵉ f b) κ id now sched st inv bΩ pΩ =
  pushBurst-width Ω g id now (map-f f) κ (proj₁ sE)
    (proj₁ (proj₂ sE)) (proj₂ (proj₂ sE)) (proj₁ IH) fΩ pΩ (proj₂ IH)
  where
  ofwf = ≤-trans (m≤m⊔n (ofWᵗ f) (ofWᵉ b)) bΩ
  ofwb = ≤-trans (m≤n⊔m (ofWᵗ f) (ofWᵉ b)) bΩ
  fΩ : frameΩ? Ω (map-f f) ≡ true
  fΩ = T⇒≡true _ (≤⇒≤ᵇ ofwf)
  sE = subscribeE g b (map-f f ↠ κ) id now sched st
  IH = subscribeE-width Ω g b (map-f f ↠ κ) id now sched st inv ofwb
         (∧-intro fΩ pΩ)

subscribeE-width Ω g (takeᵉ count b) κ id now sched st inv bΩ pΩ
  with evalTm count
... | zero  = inv , refl
... | suc k =
  pushBurst-width Ω g id now (take-f nid) κ (proj₁ sE)
    (proj₁ (proj₂ sE)) (proj₂ (proj₂ sE)) (proj₁ IH) refl pΩ (proj₂ IH)
  where
  nid    = Sched.nextNode sched
  sched₁ = proj₂ (mintNode sched)
  st₀    = installNode nid (take-st (suc k)) st
  ofwb   = ≤-trans (m≤n⊔m (ofWᵗ count) (ofWᵉ b)) bΩ
  sE     = subscribeE g b (take-f nid ↠ κ) id now sched₁ st₀
  IH     = subscribeE-width Ω g b (take-f nid ↠ κ) id now sched₁ st₀
             (install-width Ω sched₁ st nid (take-st (suc k)) refl inv)
             ofwb (∧-intro refl pΩ)

subscribeE-width {Γ = Γ} {u = u} Ω g (scanᵉ f z b) κ id now sched st inv bΩ pΩ =
  pushBurst-width Ω g id now (scan-f f nid) κ (proj₁ sE)
    (proj₁ (proj₂ sE)) (proj₂ (proj₂ sE)) (proj₁ IH) fΩ pΩ (proj₂ IH)
  where
  nid    = Sched.nextNode sched
  sched₁ = proj₂ (mintNode sched)
  -- ofWᵉ (scanᵉ f z b) = ofWᵗ f ⊔ (ofWᵗ z ⊔ ofWᵉ b)
  ofwf = ≤-trans (m≤m⊔n (ofWᵗ f) (ofWᵗ z ⊔ ofWᵉ b)) bΩ
  ofwz = ≤-trans (m≤m⊔n (ofWᵗ z) (ofWᵉ b))
           (≤-trans (m≤n⊔m (ofWᵗ f) (ofWᵗ z ⊔ ofWᵉ b)) bΩ)
  ofwb = ≤-trans (m≤n⊔m (ofWᵗ z) (ofWᵉ b))
           (≤-trans (m≤n⊔m (ofWᵗ f) (ofWᵗ z ⊔ ofWᵉ b)) bΩ)
  fΩ : frameΩ? Ω (scan-f f nid) ≡ true
  fΩ = T⇒≡true _ (≤⇒≤ᵇ ofwf)
  st₀  = installNode nid (scan-st (evalTm z)) st
  seed = ofW-evalWith Ω z []ᵃ tt ofwz
  sE   = subscribeE g b (scan-f f nid ↠ κ) id now sched₁ st₀
  IH   = subscribeE-width Ω g b (scan-f f nid ↠ κ) id now sched₁ st₀
           (install-width Ω sched₁ st nid (scan-st (evalTm z))
             (T⇒≡true _ (≤⇒≤ᵇ seed)) inv)
           ofwb (∧-intro fΩ pΩ)

subscribeE-width Ω g (mergeAllᵉ b) κ id now sched st inv bΩ pΩ =
  subscribeAll-width Ω g mergeᵒ (merge-st 0 false) b κ id now sched st
    inv refl bΩ pΩ
subscribeE-width {u = u} Ω g (concatAllᵉ b) κ id now sched st inv bΩ pΩ =
  subscribeAll-width Ω g concatᵒ (concat-st {t = u} [] false false) b κ id now
    sched st inv refl bΩ pΩ
subscribeE-width Ω g (switchAllᵉ b) κ id now sched st inv bΩ pΩ =
  subscribeAll-width Ω g switchᵒ (switch-st nothing false) b κ id now sched st
    inv refl bΩ pΩ
subscribeE-width Ω g (exhaustAllᵉ b) κ id now sched st inv bΩ pΩ =
  subscribeAll-width Ω g exhaustᵒ (exhaust-st false false) b κ id now sched st
    inv refl bΩ pΩ

subscribeE-width Ω g0 (μᵉ body) κ id now sched st inv bΩ pΩ = inv , refl
subscribeE-width Ω (gs fuel) (μᵉ body) κ id now sched st inv bΩ pΩ =
  subscribeE-width Ω fuel (unfoldμ body) κ id now sched st inv ofwU pΩ
  where
  ofwU : ofWᵉ (unfoldμ body) ≤ Ω
  ofwU = ≤-trans (ofW-elimG (here refl) (μᵉ body) body) (⊔-lub bΩ bΩ)

subscribeE-width Ω g (varᵉ ()) κ id now sched st inv bΩ pΩ

subscribeE-width Ω g (deferᵉ body) κ id now sched st inv bΩ pΩ =
  subscribeE-defer-width Ω g body κ id now sched st inv bΩ pΩ

------------------------------------------------------------------
-- (W11-C) THE DELIVERY CLIQUE, width face.  Same lexicographic
-- recursion as the wet clique — (dispatch gas, path), frame hops
-- shrinking the path at constant gas and the share hop peeling one
-- gas — but with Ω flat there is no receipt to thread and no
-- widening at the joins, so each clause is its wet twin with the
-- ledger bookkeeping struck out.
------------------------------------------------------------------

foldPath-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (Ω : ℕ) (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
  (path : Path Γ u t) (vals : List (Val Γ u))
  (evs : List (InstEvent (Val Γ t))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true →
  pathΩ? Ω path ≡ true →
  all (λ v → ofWᵛ u v ≤ᵇ Ω) vals ≡ true →
  all (eventΩ? Ω) evs ≡ true →
  let r = foldPath sf gas id now envSrc path vals evs fin sched st
  in (widthOK? Ω (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstΩ? Ω (proj₁ r) ≡ true)

dispatchShare-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (Ω : ℕ) (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
  (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true →
  all (λ v → ofWᵛ (lookup Γ i) v ≤ᵇ Ω) vals ≡ true →
  let r = dispatchShare sf gas id now i vals fin sched st
  in (widthOK? Ω (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstΩ? Ω (proj₁ r) ≡ true)

shareGo-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (Ω : ℕ) (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
  (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
  (ps : List (RegId × Path Γ (lookup Γ i) t))
  (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true →
  all (λ rp → pathΩ? Ω (proj₂ rp)) ps ≡ true →
  all (λ v → ofWᵛ (lookup Γ i) v ≤ᵇ Ω) vals ≡ true →
  let r = shareGo sf gas id now i vals fin ps sched st
  in (widthOK? Ω (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstΩ? Ω (proj₁ r) ≡ true)

chainStep-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (Ω : ℕ) (id : Id) (a : Arrival Γ) (path : Path Γ (arrTy a) t)
  (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true →
  pathΩ? Ω path ≡ true →
  (ofWᵛ (arrTy a) (arrVal a) ≤ᵇ Ω) ≡ true →
  let r = chainStep id a path sched st
  in (widthOK? Ω (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstΩ? Ω (proj₁ r) ≡ true)

cascadeGo-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (Ω : ℕ) (a : Arrival Γ) (id : Id)
  (chains : List (RegId × Path Γ (arrTy a) t))
  (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true →
  (ofWᵛ (arrTy a) (arrVal a) ≤ᵇ Ω) ≡ true →
  all (λ rc → pathΩ? Ω (proj₂ rc)) chains ≡ true →
  let r = cascadeGo a id chains sched st
  in (widthOK? Ω (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstΩ? Ω (proj₁ r) ≡ true)

-- the root: assemble the envelope
foldPath-width {u = u} Ω sf gas id now envSrc root vals evs fin sched st
               inv pΩ vΩ eΩ =
  inv ,
  ∧-intro
    (all-++-intro _ evs _ eΩ
      (all-++-intro _ (map value vals) _
        (mapValue-Ω Ω u vals vΩ)
        (finList-Ω Ω fin)))
    refl

-- the share boundary: valueless handoff emit, then the fan-out
foldPath-width Ω sf gas id now envSrc (share-sink i) vals evs fin sched st
               inv pΩ vΩ eΩ =
  proj₁ DS , ∧-intro (all-++-intro _ evs _ eΩ refl) (proj₂ DS)
  where
  DS = dispatchShare-width Ω sf gas id now i vals fin sched st inv vΩ

-- a frame hop: step it, then keep folding down the shorter path
foldPath-width Ω sf gas id now envSrc (f ↠ path′) vals evs fin sched st
               inv pΩ vΩ eΩ = IH
  where
  fΩ   = proj₁ (∧-true (frameΩ? Ω f) _ pΩ)
  pΩ′  = proj₂ (∧-true (frameΩ? Ω f) _ pΩ)
  SF   = stepFrame-width Ω sf id now f path′ vals fin sched st inv fΩ pΩ′ vΩ
  step = stepFrame sf id now f path′ vals fin sched st
  IH   = foldPath-width Ω sf gas id now envSrc path′ (proj₁ step)
           (evs ++ proj₁ (proj₂ step)) (proj₁ (proj₂ (proj₂ step)))
           (proj₁ (proj₂ (proj₂ (proj₂ step))))
           (proj₂ (proj₂ (proj₂ (proj₂ step))))
           (proj₁ SF) pΩ′ (proj₁ (proj₂ SF))
           (all-++-intro _ evs _ eΩ (proj₂ (proj₂ SF)))

-- out of dispatch gas: unreachable in a real run, free when it fires
dispatchShare-width Ω sf zero id now i vals fin sched st inv vΩ = inv , refl
dispatchShare-width Ω sf (suc gas) id now i vals fin sched st inv vΩ =
  shareFinish-width Ω i fin (proj₁ GOr)
    (proj₁ (proj₂ GOr)) (proj₂ (proj₂ GOr)) (proj₁ GO) ,
  subst (λ b → burstΩ? Ω b ≡ true)
        (sym (shareFinish-burst i fin (proj₁ GOr)
               (proj₁ (proj₂ GOr)) (proj₂ (proj₂ GOr))))
        (proj₂ GO)
  where
  st₀  = shareLatch i fin st
  adm  = shareAdmit i (EvalSt.registry st)
  admΩ = shareAdmit-Ω Ω i (EvalSt.registry st)
           (proj₁ (proj₂ (proj₂ (WOK-parts Ω sched st inv))))
  GO   = shareGo-width Ω sf gas id now i vals fin adm sched st₀
           (shareLatch-width Ω i fin sched st inv) admΩ vΩ
  GOr  = shareGo sf gas id now i vals fin adm sched st₀

shareGo-width Ω sf gas id now i vals fin [] sched st inv pΩ vΩ = inv , refl
shareGo-width {Γ = Γ} Ω sf gas id now i vals fin ((rid , q) ∷ ps) sched st
              inv pΩ vΩ
  with any (_≡ᵇ rid) (EvalSt.cancelled st)
-- cut earlier this cascade: its close already rode the cutting emit
... | true  = shareGo-width Ω sf gas id now i vals fin ps sched st inv
                (proj₂ (∧-true (pathΩ? Ω q) _ pΩ)) vΩ
... | false = proj₁ IH ,
              all-++-intro _ (proj₁ FPr) _ (proj₂ FP) (proj₂ IH)
  where
  st₀ = record st { delivered = rid ∷ EvalSt.delivered st }
  FP  = foldPath-width Ω sf gas id now (toℕ i) q vals
          (if fin then close (toℕ i) exhausted ∷ [] else []) fin sched st₀
          (delivered-width Ω rid sched st inv)
          (proj₁ (∧-true (pathΩ? Ω q) _ pΩ)) vΩ
          (closeList-Ω Ω (toℕ i) fin)
  FPr = foldPath sf gas id now (toℕ i) q vals
          (if fin then close (toℕ i) exhausted ∷ [] else []) fin sched st₀
  IH  = shareGo-width Ω sf gas id now i vals fin ps
          (proj₁ (proj₂ FPr)) (proj₂ (proj₂ FPr)) (proj₁ FP)
          (proj₂ (∧-true (pathΩ? Ω q) _ pΩ)) vΩ

chainStep-width {n = n} {e = e} Ω id a path sched st inv pΩ vΩ =
  foldPath-width Ω (budgetAt e (Sched.slots sched) id) n id (arrTick a)
    (arrSource a) path (arrVal a ∷ [])
    (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else [])
    (Arrival.isLast a) sched st inv pΩ (∧-intro vΩ refl)
    (closeList-Ω Ω (arrSource a) (Arrival.isLast a))

-- the cascade fold: one emit per surviving registration, in
-- subscription order
cascadeGo-width Ω a id []                   sched st inv vΩ pΩ = inv , refl
cascadeGo-width Ω a id ((rid , c) ∷ chains) sched st inv vΩ pΩ
  with any (_≡ᵇ rid) (EvalSt.cancelled st)
... | true  = cascadeGo-width Ω a id chains sched st inv vΩ
                (proj₂ (∧-true (pathΩ? Ω c) _ pΩ))
... | false = proj₁ IH , all-++-intro _ (proj₁ CSr) _ (proj₂ CS) (proj₂ IH)
  where
  st₀ = record st { delivered = rid ∷ EvalSt.delivered st }
  CS  = chainStep-width Ω id a c sched st₀
          (delivered-width Ω rid sched st inv)
          (proj₁ (∧-true (pathΩ? Ω c) _ pΩ)) vΩ
  CSr = chainStep id a c sched st₀
  IH  = cascadeGo-width Ω a id chains
          (proj₁ (proj₂ CSr)) (proj₂ (proj₂ CSr)) (proj₁ CS) vΩ
          (proj₂ (∧-true (pathΩ? Ω c) _ pΩ))

postulate
  -- THE WET CONTRACT, stated at the mutual block's entry point:
  -- from a store-bounded machine, subscribing any store-sized value
  -- with fuel for its demand neither dries nor escapes the next
  -- instant's budget.  This is the strengthened induction of the
  -- proof design above, to be ground clause by clause through the
  -- block (subscribeE / stepFrame / pushBurst / subscribeAll /
  -- subscribeInner / subscribeSharedSlot), each decrement edge
  -- consuming one hasAtLeast-peel against dBound-μ / dBound-hop /
  -- dBound-connect.  The internal walk threads a stronger invariant
  -- (mid-walk states at the SAME instant); only this outer face is
  -- fixed here.
  subscribeE-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) →
    let V = sizeBudgetAt e (Sched.slots sched) id in
    stBounded? V sched st ≡ true →
    sizeᵉ b ≤ V →
    g hasAtLeast
      suc (dBound V (hopR V)
                  (unconn (Sched.slots sched) (EvalSt.connectedShares st))
                  (hopDᵉ V b) (syncSizeᵉ b)) →
    let r = subscribeE g b κ id now sched st
    in (hasDry (proj₁ r) ≡ false)
       × (stBounded? (sizeBudgetAt e (Sched.slots (proj₁ (proj₂ r))) (suc id))
                     (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)

  -- the chain fold at instant id, from a latched state within id's
  -- size budget, stays wet and lands within suc id's.
  --
  -- FOLD-THREADING (2026-07-20, the ledger finding): this core does
  -- NOT decompose into an end-to-end per-chainStep contract at the
  -- two fixed bounds.  After chain k lands, chain k+1 starts from a
  -- mid-cascade state that only suc id's budget bounds — and a
  -- fixed-bound "start @ suc id → land @ suc id" step statement is
  -- FALSE over its full quantification (a store value near the
  -- bound grows past it under one more applyFn), so stating it
  -- would be a forbidden false postulate.  The honest decomposition
  -- threads per-cascade growth through the fold, and its exponent
  -- budget is |chains| · demand — but |chains| (the registry's
  -- cardinality at instant id) has NO syntactic bound: it needs its
  -- own cumulative invariant (registrations accrue ≤ demand per
  -- instant) formulated and proven BEFORE a chainStep-wet can be
  -- shaped truthfully.  Until then this stays one postulate (the
  -- FoldOut precedent: no half-stated leaf).  What IS proven of the
  -- ledger: connect-anchor (share crossings re-anchor against the
  -- global syntactic multiset {program} ⊎ {slots}), and the
  -- per-cascade delivered/cancelled ledger caps deliveries at one
  -- per registration (Verify-Well-Formed's cascadeGo-skip ring).
  cascadeGo-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (a : Arrival Γ) (id : Id)
    (chains : List (RegId × Path Γ (arrTy a) t))
    (sched : Sched Γ) (st : EvalSt e) →
    stBounded? (sizeBudgetAt e (Sched.slots sched) id) sched st ≡ true →
    let r = cascadeGo a id chains sched st
    in (hasDry (proj₁ r) ≡ false)
       × (stBounded? (sizeBudgetAt e (Sched.slots (proj₁ (proj₂ r))) (suc id))
                     (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)

------------------------------------------------------------------
-- the burst cores — PROVEN: the contract instantiated at the root.
-- The root subscribes the program itself from the initial machine:
-- init-bounded seeds the store invariant, the program is its own
-- size witness, and the seeded budget covers the demand by
-- dBound-bound + seed-covers (U ≤ sz through the slot content,
-- r ≤ R through measureE-rank).
------------------------------------------------------------------

burst-wet : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  let r = subscribeE (budgetAt e ins 0) e root 0 0
                     (sched-init e ins) (st-init e)
  in (hasDry (proj₁ r) ≡ false)
     × (stBounded? (sizeBudgetAt e (Sched.slots (proj₁ (proj₂ r))) 1)
                   (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
burst-wet e ins =
  subscribeE-wet (budgetAt e ins 0) e root 0 0
                 (sched-init e ins) (st-init e)
                 (init-bounded e ins 0) size≤V fuel-ok
  where
  sz = sizeᵉ e + slotsSize ins
  V  = sizeBudgetAt e ins 0

  size≤V : sizeᵉ e ≤ V
  size≤V = size≤budget e ins 0

  U≤sz : unconn ins [] ≤ sz
  U≤sz = ≤-trans (unconn≤slots ins []) (m≤n+m (slotsSize ins) (sizeᵉ e))

  fuel-ok : budgetAt e ins 0 hasAtLeast
    suc (dBound V (hopR V) (unconn ins [])
                (hopDᵉ V e) (syncSizeᵉ e))
  fuel-ok = hasAtLeast-mono
    (≤-trans (s≤s (dBound-bound (≤-trans (syncSize≤sizeᵉ e) size≤V)
                                (hopD-cap V e (2≤sizeBudget e ins 0) size≤V)))
             (seed-covers sz (unconn ins []) U≤sz))
    (budget-hasAtLeast sz 0)

burst-dry : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  hasDry (proj₁ (subscribeE (budgetAt e ins 0) e root 0 0
                            (sched-init e ins) (st-init e))) ≡ false
burst-dry e ins = proj₁ (burst-wet e ins)

burst-bounded : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  let r = subscribeE (budgetAt e ins 0) e root 0 0
                     (sched-init e ins) (st-init e)
  in stBounded? (sizeBudgetAt e (Sched.slots (proj₁ (proj₂ r))) 1)
                (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true
burst-bounded e ins = proj₂ (burst-wet e ins)


------------------------------------------------------------------
-- one cascade — PROVEN: latch, the postulated fold core, finish
------------------------------------------------------------------

cascade-dry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (id : Id) (sched : Sched Γ) (st : EvalSt e) →
  stBounded? (sizeBudgetAt e (Sched.slots sched) id) sched st ≡ true →
  let r = cascade a id sched st
  in (hasDry (proj₁ r) ≡ false)
     × (stBounded? (sizeBudgetAt e (Sched.slots (proj₁ (proj₂ r))) (suc id))
                   (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
cascade-dry {e = e} a id sched st bnd
  with cascadeGo-wet a id (chainsOf a st) sched (cascadeLatch a st)
         (latch-bounded (sizeBudgetAt e (Sched.slots sched) id) sched a st bnd)
... | dry , bnd' = dry , final
  where
  sched' = proj₁ (proj₂ (cascadeGo a id (chainsOf a st) sched
                                   (cascadeLatch a st)))
  st'    = proj₂ (proj₂ (cascadeGo a id (chainsOf a st) sched
                                   (cascadeLatch a st)))
  final : stBounded?
            (sizeBudgetAt e (Sched.slots (proj₁ (cascadeFinish a sched' st')))
                      (suc id))
            (proj₁ (cascadeFinish a sched' st'))
            (proj₂ (cascadeFinish a sched' st')) ≡ true
  final = subst
            (λ sl → stBounded? (sizeBudgetAt e sl (suc id))
                      (proj₁ (cascadeFinish a sched' st'))
                      (proj₂ (cascadeFinish a sched' st')) ≡ true)
            (sym (finish-slots a sched' st'))
            (finish-bounded (sizeBudgetAt e (Sched.slots sched') (suc id))
                            a sched' st' bnd')

------------------------------------------------------------------
-- the fuel loop composes cascades — PROVEN
------------------------------------------------------------------

drain-dry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (fuel : Fuel) (id : Id) (sched : Sched Γ) (st : EvalSt e) →
  stBounded? (sizeBudgetAt e (Sched.slots sched) id) sched st ≡ true →
  hasDry (drain {e = e} fuel id sched st) ≡ false
drain-dry zero    id sched st bnd = refl
drain-dry (suc k) id sched st bnd with sched-next sched in eq
... | inj₁ _            = refl
drain-dry {e = e} (suc k) id sched st bnd | inj₂ (a , sched′) =
  let bnd′ : stBounded? (sizeBudgetAt e (Sched.slots sched′) id) sched′ st ≡ true
      bnd′ = subst
               (λ sl → stBounded? (sizeBudgetAt e sl id) sched′ st ≡ true)
               (sym (pop-slots sched eq))
               (pop-bounded (sizeBudgetAt e (Sched.slots sched) id) sched st eq bnd)
      (dry₁ , bnd″) = cascade-dry a id sched′ st bnd′
  in hasDry-append (proj₁ (cascade a id sched′ st)) _
       dry₁
       (drain-dry k (suc id)
         (proj₁ (proj₂ (cascade a id sched′ st)))
         (proj₂ (proj₂ (cascade a id sched′ st)))
         bnd″)

------------------------------------------------------------------
-- the theorem: same statement as Verify-Well-Formed's postulate;
-- the splice (coordinated, later) replaces that postulate with this
------------------------------------------------------------------

budget-sufficient :
  ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ) →
  hasDry (evaluate fuel e ins) ≡ false
budget-sufficient fuel e ins =
  hasDry-append
    (proj₁ (subscribeE (budgetAt e ins 0) e root 0 0
                       (sched-init e ins) (st-init e)))
    _
    (burst-dry e ins)
    (drain-dry fuel 1
      (proj₁ (proj₂ (subscribeE (budgetAt e ins 0) e root 0 0
                                (sched-init e ins) (st-init e))))
      (proj₂ (proj₂ (subscribeE (budgetAt e ins 0) e root 0 0
                                (sched-init e ins) (st-init e))))
      (burst-bounded e ins))
