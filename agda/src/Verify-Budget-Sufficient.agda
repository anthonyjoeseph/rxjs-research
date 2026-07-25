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
-- contract), cascade-dry, drain-dry, and the theorem.  Two
-- postulated cores remain — subscribeE-wet, cascadeGo-wet — the
-- real termination content: fuel-accounting induction over the
-- subscription machine's clauses (the three decrement edges each
-- consume one hasAtLeast-peel against dBound-μ/-hop/-connect;
-- everything between is structural), and the fold's threading
-- invariant (see cascadeGo-wet's memo).  Not imported by Main until
-- the splice into Verify-Well-Formed replaces its postulate.
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
                                       m≤m⊔n; m≤n⊔m; ⊔-lub)
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
open import Rx.Exp       using (Ty; unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_; obs; _≟ᵗ_;
                                Ctx; Closed; Val; sizeᵉ; sizeᵗ; sizeᵗˢ; sizeᵛ;
                                syncSizeᵉ; syncSizeᵗ; syncSizeᵗˢ;
                                shellSizeᵉ; innerᵉ; innerᵗ; innerᵗˢ;
                                shellsᵉ; shellsᵛ;
                                subΘExp; subΘTm; subΘTms;
                                plugsᵉ; plugsᵗ; plugsᵗˢ;
                                occsᵉ; occsᵗ; occsᵗˢ;
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
                                takeVals; cutThrough; pathHasNode;
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

sizeBudgetAt-mono : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t)
  (sl : Slots Γ) {id id′ : Id} → id ≤ id′ →
  sizeBudgetAt e sl id ≤ sizeBudgetAt e sl id′
sizeBudgetAt-mono e sl h =
  towerℕ-mono (*-monoʳ-≤ (4 + (sizeᵉ e + slotsSize sl)) (s≤s h))

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

-- a bound only ever needs to be respected upward: the id-level bound
-- entails the suc-id-level one (budgets grow monotonically)
bounded-mono : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  {B B′ : ℕ} → B ≤ B′ → (sched : Sched Γ) (st : EvalSt e) →
  stBounded? B sched st ≡ true → stBounded? B′ sched st ≡ true
bounded-mono {B = B} {B′} le sched st bnd
  with ∧-true (all (boundedLive B) (Sched.live sched)) _ bnd
... | bls , bns =
  ∧-intro
    (all-impl (boundedLive B) (boundedLive B′)
      (λ l → all-impl _ _ (λ tv → ≤ᵇ-widen (sizeᵛ (LiveSource.elemTy l) (proj₂ tv)) le) (LiveSource.pending l))
      (Sched.live sched) bls)
    (all-impl _ _ (λ kv → node-mono (proj₂ kv)) (EvalSt.nodes st) bns)
  where
  node-mono : ∀ nd → boundedNode B nd ≡ true → boundedNode B′ nd ≡ true
  node-mono (scan-st {t} v)   h = ≤ᵇ-widen (sizeᵛ t v) le h
  node-mono (concat-st q _ _) h = all-impl _ _ (λ o → ≤ᵇ-widen (sizeᵉ o) le) q h
  node-mono (take-st _)       h = refl
  node-mono (merge-st _ _)    h = refl
  node-mono (switch-st _ _)   h = refl
  node-mono (exhaust-st _ _)  h = refl

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

-- the r ≤ R discharge, packaged: a stored value's rank sits under
-- the store rank cap purely because its SIZE does — entry sum via
-- shells-len, all through stBounded?, no extra invariant
measureE-rank : ∀ {n} {Γ : Ctx n} {t} (B V : ℕ) (e : Closed Γ t) →
  sizeᵉ e ≤ V → rank V (measureE B e) < (suc V) ^ suc B
measureE-rank B V e h = rank-lt-pow V (counts B (shellsᵉ e))
  (subst (_≤ V) (sym (totᵛ-counts B (shellsᵉ e)))
         (≤-trans (shells-len e) h))

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
-- slot content, so its rank sits under the store rank cap (feeding
-- dBound-connect's r′ ≤ R) and its walk under the store bound
-- (feeding dBound-hop/-connect's s′ ≤ V), straight off the
-- budget's slot summand: no state invariant consulted
connect-anchor : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id : Id) (i : Fin n) {d : Closed Γ (lookup Γ i)} → sl i ≡ shared d →
  let V = sizeBudgetAt e sl id in
  (rank V (measureE V d) ≤ suc V ^ suc V) × (syncSizeᵉ d ≤ V)
connect-anchor e sl id i {d} eq =
  <⇒≤ (measureE-rank V V d size≤V) , ≤-trans (syncSize≤sizeᵉ d) size≤V
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
dBound-mono : ∀ {V R U′ U r′ r s′ s} → U′ ≤ U → r′ ≤ r → s′ ≤ s →
  dBound V R U′ r′ s′ ≤ dBound V R U r s
dBound-mono {V} {R} U′≤U r′≤r s′≤s =
  +-mono-≤ s′≤s
    (*-monoʳ-≤ (suc V) (+-mono-≤ r′≤r (*-monoʳ-≤ (suc R) U′≤U)))

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

shells-unfoldμ-len : ∀ {n} {Γ : Ctx n} {t}
  (body : Exp Γ (t ∷ []) [] [] t) →
  length (shellsᵉ (unfoldμ body)) ≡ length (shellsᵉ (μᵉ body))
shells-unfoldμ-len body rewrite inner-unfoldμ body = refl

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

prod≤3pow : ∀ (V U : ℕ) → 2 ≤ V → U ≤ V →
  suc (suc V * suc (suc V ^ suc V) * suc U) ≤ 2 ^ (2 ^ (2 ^ V))
prod≤3pow V U 2≤V U≤V =
  ≤-trans (s≤s prod≤2F) (≤-trans (suc-2^ F) (^-monoʳ-≤ 2 sucF≤))
  where
  F = V + suc (V * suc V) + V

  hV : suc V ≤ 2 ^ V
  hV = n<2^n V

  hR : suc (suc V ^ suc V) ≤ 2 ^ suc (V * suc V)
  hR = ≤-trans (s≤s (≤-trans (^-monoˡ-≤ (suc V) hV)
                             (≤-reflexive (^-*-assoc 2 V (suc V)))))
               (suc-2^ (V * suc V))

  hU : suc U ≤ 2 ^ V
  hU = ≤-trans (s≤s U≤V) hV

  prod≤2F : suc V * suc (suc V ^ suc V) * suc U ≤ 2 ^ F
  prod≤2F = ≤-trans (*-mono-≤ (*-mono-≤ hV hR) hU)
    (≤-reflexive
      (trans (cong (_* 2 ^ V) (sym (^-distribˡ-+-* 2 V (suc (V * suc V)))))
             (sym (^-distribˡ-+-* 2 (V + suc (V * suc V)) V))))

  -- suc F + slack = (V+2)², counted exactly (the ring identity)
  slack-eq : (3 + V) + F ≡ (V + 2) * (V + 2)
  slack-eq = solve 1
    (λ v → (con 3 :+ v) :+ ((v :+ (con 1 :+ v :* (con 1 :+ v))) :+ v)
             := (v :+ con 2) :* (v :+ con 2))
    refl V

  sucF≤ : suc F ≤ 2 ^ (2 ^ V)
  sucF≤ =
    ≤-trans (+-monoˡ-≤ F (s≤s (z≤n {suc (suc V)})))   -- suc F ≤ (3+V) + F
    (≤-trans (≤-reflexive slack-eq)
    (≤-trans (*-mono-≤ (k+2≤2^k V 2≤V) (k+2≤2^k V 2≤V))
    (≤-trans (≤-reflexive (sym (^-distribˡ-+-* 2 V V)))
             (^-monoʳ-≤ 2 (2k≤2^k V 2≤V)))))

-- the burst's seed step: at instant 0 the demand product sits under
-- the budget's tower summand alone.  The demand anchors at the
-- ENTRY store bound here (the burst is instant 0's whole walk);
-- prod≤3pow's three stories land inside the gas tower's height
-- (7+sz)·2 with 7+sz to spare
seed-covers : ∀ (sz U : ℕ) → U ≤ sz →
  let V = towerℕ ((4 + sz) * 1) in
  suc (suc V * suc (suc V ^ suc V) * suc U)
    ≤ 2 ^ (sz * 1 * 1) + towerℕ ((7 + sz) * 2)
seed-covers sz U U≤sz
  rewrite *-identityʳ sz | *-identityʳ sz | *-identityʳ (4 + sz) =
  ≤-trans (prod≤3pow (towerℕ (4 + sz)) U 2≤V U≤V)
  (≤-trans (towerℕ-mono (m≤m*n (7 + sz) 2))
           (m≤n+m (towerℕ ((7 + sz) * 2)) (2 ^ sz)))
  where
  2≤V : 2 ≤ towerℕ (4 + sz)
  2≤V = towerℕ-mono {1} {4 + sz} (s≤s z≤n)
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

oneShot-dry : ∀ {n} {Γ : Ctx n} {u} (vals : List (Val Γ u)) (id : Id)
  (sched : Sched Γ) →
  hasDry (proj₁ (oneShotBurst vals id sched)) ≡ false
oneShot-dry vals id sched = cong (_∨ false) (oneShot-tail-dry vals _)

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
  suc (suc V * suc (suc V ^ suc V) * suc U)
    ≤ 2 ^ (sz * suc id * suc id) + towerℕ ((7 + sz) * suc (suc id))
budget-covers sz U id U≤sz =
  ≤-trans (prod≤3pow (towerℕ h) U 2≤V U≤V)
  (≤-trans (towerℕ-mono slack)
           (m≤n+m (towerℕ H) (2 ^ (sz * suc id * suc id))))
  where
  h = (4 + sz) * suc (suc id)
  H = (7 + sz) * suc (suc id)

  2≤V : 2 ≤ towerℕ h
  2≤V = towerℕ-mono {1} {h} (s≤s z≤n)

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

evalTm-size : ∀ {n} {Γ : Ctx n} {t} (tm : Tm Γ [] [] [] t) →
  sizeᵛ t (evalTm tm) ≤ 2 ^ (3 ^ sizeᵗ tm)
evalTm-size tm = evalWith-size 0 tm []ᵃ tt

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

W≤capᴱ : ∀ (W : ℕ) {E : ℕ} → 1 ≤ E → W ≤ capᴱ W E
W≤capᴱ W h = ≤-trans (V≤C W) (pow1 W h)

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

postulate
  -- (W11) the width walk: Ω is flat, so these are pure
  -- preservation statements — no existential, no receipt.  The
  -- grind literally repeats the fnCap half of subscribeE-walkS /
  -- cascadeGo-walk with the W10 mirrors in place of W2/W4 (the
  -- slots conjunct feeds the input/defer clauses exactly as
  -- slotsFnCap did).
  subscribeE-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (Ω : ℕ) (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (id : Id)
    (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    widthOK? Ω sched st ≡ true → ofWᵉ b ≤ Ω → pathΩ? Ω κ ≡ true →
    let r = subscribeE g b κ id now sched st
    in (widthOK? Ω (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
       × (burstΩ? Ω (proj₁ r) ≡ true)

  cascadeGo-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (Ω : ℕ) (a : Arrival Γ) (id : Id)
    (chains : List (RegId × Path Γ (arrTy a) t))
    (sched : Sched Γ) (st : EvalSt e) →
    widthOK? Ω sched st ≡ true →
    ofWᵛ (arrTy a) (Arrival.payload a) ≤ Ω →
    all (λ rc → pathΩ? Ω (proj₂ rc)) chains ≡ true →
    let r = cascadeGo a id chains sched st
    in (widthOK? Ω (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
       × (burstΩ? Ω (proj₁ r) ≡ true)

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
  subscribeE-walk : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (Ψ W Ω V ℓ : ℕ) (g : Gas) (b : Closed Γ u) (κ : Path Γ u t)
    (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) (E d : ℕ) →
    3 ≤ E →
    INV? Ψ (capᴱ W E) sched st ≡ true →
    sizeᵉ b ≤ capᴱ W E → fnCapᵉ b ≤ Ψ →
    pathB? (capᴱ W E) Ψ κ ≡ true →
    widthOK? Ω sched st ≡ true → ofWᵉ b ≤ Ω → pathΩ? Ω κ ≡ true →
    dBound V (suc V ^ suc V)
           (unconn (Sched.slots sched) (EvalSt.connectedShares st))
           (rank V (measureE V b)) (syncSizeᵉ b) ≤ d →
    g hasAtLeast suc d →
    pathLen κ + d ≤ ℓ →
    regsLen? ℓ (EvalSt.registry st) ≡ true →
    capᴱ W (E * 3 ^ (suc Ψ * walkCap Ω ℓ d)) ≤ V →
    let r = subscribeE g b κ id now sched st
    in Σ ℕ λ E′ → (E ≤ E′)
       × (E′ ≤ E * 3 ^ (suc Ψ * walkCap Ω ℓ d))
       × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
       × (burstB? (capᴱ W E′) Ψ (proj₁ r) ≡ true)
       × (hasDry (proj₁ r) ≡ false)
       × (mintCount (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
            ≤ mintCount sched st + walkCap Ω ℓ d)
       × (burstLen (proj₁ r) ≤ walkCap Ω ℓ d)
       × (regsLen? ℓ (EvalSt.registry (proj₂ (proj₂ r))) ≡ true)

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
      suc (dBound V (suc V ^ suc V)
                  (unconn (Sched.slots sched) (EvalSt.connectedShares st))
                  (rank V (measureE V b)) (syncSizeᵉ b)) →
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
    suc (dBound V (suc V ^ suc V) (unconn ins [])
                (rank V (measureE V e)) (syncSizeᵉ e))
  fuel-ok = hasAtLeast-mono
    (≤-trans (s≤s (dBound-bound (≤-trans (syncSize≤sizeᵉ e) size≤V)
                                (<⇒≤ (measureE-rank V V e size≤V))))
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
