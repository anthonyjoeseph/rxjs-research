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

open import Data.Bool    using (Bool; true; false; T; _∧_; _∨_;
                                if_then_else_)
open import Data.Nat     using (ℕ; zero; suc; _+_; _*_; _^_; _≤_; _<_;
                                _⊔_; _≤ᵇ_; _<ᵇ_; _≡ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (≤ᵇ⇒≤; ≤⇒≤ᵇ; ≤-trans; ≤-refl;
                                       ≤-reflexive; <-≤-trans; ≤-pred;
                                       +-suc; +-identityʳ;
                                       +-comm; +-assoc; +-monoʳ-<;
                                       +-monoˡ-<; +-monoˡ-≤;
                                       *-monoˡ-≤; *-monoʳ-≤;
                                       *-suc; m≤m+n; m≤n+m; n≤1+n;
                                       m≤n⇒m<n∨m≡n; +-mono-≤; m≤m*n;
                                       ^-monoʳ-≤; *-assoc;
                                       +-mono-<-≤; +-mono-≤-<; ≡⇒≡ᵇ;
                                       *-distribʳ-+; *-identityʳ; <⇒≤;
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
  using (∈-++⁻; ∈-++⁺ˡ)
open import Data.Maybe   using (nothing)
open import Data.Vec     using (Vec; lookup) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (inj₁; inj₂)
open import Data.Unit    using (⊤; tt)
open import Induction.WellFounded using (Acc; acc; WellFounded)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Rx.Prim      using (Fuel; Tick; Id; Source; InstEmit;
                                InstEvent; init; value; close; handoff;
                                complete;
                                Gas; g0; gs; gasDouble; gasPow2; gasTower; gasPad;
                                Timed; after_,_; ObservableInput; hot; cold)
open import Rx.Exp       using (Ty; unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_; obs;
                                Ctx; Closed; Val; sizeᵉ; sizeᵗ; sizeᵗˢ; sizeᵛ;
                                syncSizeᵉ; syncSizeᵗ; syncSizeᵗˢ;
                                shellSizeᵉ; innerᵉ; innerᵗ; innerᵗˢ;
                                shellsᵉ; shellsᵛ;
                                subΘExp; subΘTm; subΘTms;
                                plugsᵉ; plugsᵗ; plugsᵗˢ;
                                occsᵉ; occsᵗ; occsᵗˢ;
                                renExp; renTm; renTms; Ren∈; ext∈;
                                wkExp; wkTm; reify;
                                Exp; Tm; Fn; varᵗ; unit̂; bool̂; nat̂; pairᵗ;
                                fstᵗ; sndᵗ; inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ;
                                strmᵗ; add; sub; mul; eqᵖ; ltᵖ; notᵖ;
                                input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ;
                                mergeAllᵉ; concatAllᵉ; switchAllᵉ;
                                exhaustAllᵉ; μᵉ; varᵉ; deferᵉ;
                                elimGExp; elimGTm; elimGTms; unfoldμ;
                                evalWith; evalTm; applyFn; lookupEnv)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; Slots; LiveSource;
                                Slot; scripted; shared; resolve; mkHot;
                                arrVal; scanVals; memberSource;
                                slotSize; inputSize;
                                RegId; Chain;
                                NodeState; scan-st; take-st; merge-st;
                                concat-st; switch-st; exhaust-st;
                                oneShotBurst; installNode; NodeId;
                                root; share-sink; _↠_; Frame; AllOp;
                                map-f; scan-f; take-f; from-inner;
                                thru-outer; Stream;
                                sched-init; st-init; sched-next;
                                schedHeadOf; schedGo; schedEarlier;
                                cascadeLatch; cascadeFinish; sweepLive;
                                dropSource; arrSource; chainsOf; cascadeGo;
                                Path; arrTy;
                                subscribeE; stepFrame; pushBurst;
                                subscribeInner; chainStep; subscribeAll;
                                mintNode; register;
                                mergeᵒ; concatᵒ; switchᵒ; exhaustᵒ;
                                splitEvents; retagEvents;
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
-- covers the script's total content
resolve-bounded : ∀ {n} {Γ : Ctx n} {t : Ty} (B : ℕ) (anchor : Tick)
  (xs : List (Timed (Val Γ t))) →
  sum (map (λ tv → sizeᵛ t (Timed.val tv)) xs) ≤ B →
  all (λ p → sizeᵛ t (proj₂ p) ≤ᵇ B) (resolve anchor xs) ≡ true
resolve-bounded B anchor [] h = refl
resolve-bounded {t = t} B anchor ((after w , v) ∷ r) h =
  ∧-intro (T⇒≡true _ (≤⇒≤ᵇ (≤-trans (m≤m+n (sizeᵛ t v) _) h)))
          (resolve-bounded B (anchor + suc w) r
            (≤-trans (m≤n+m _ (sizeᵛ t v)) h))

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

postulate
  -- (G1) per-entry cons of shellsᵛ-len / shellsᵛ-≤ with ≤-trans
  envSize→envLen : ∀ {n} {Γ : Ctx n} {Θ} (V : ℕ) (σ : All (Val Γ) Θ) →
    EnvSize V σ → EnvLen V σ
  envSize→envCap : ∀ {n} {Γ : Ctx n} {Θ} (B : ℕ) (σ : All (Val Γ) Θ) →
    EnvSize B σ → EnvCap B σ

  -- (G2) renamings are size-invariant (constructors map 1-1) —
  -- mirror shellSize-ren/inner-ren's mutual shape over sizeᵉ/ᵗ/ᵗˢ
  size-renᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t}
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′)
    (e : Exp Γ Δᵍ Δ Θ t) → sizeᵉ (renExp ρg ρd ρt e) ≡ sizeᵉ e
  size-renᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t}
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′)
    (tm : Tm Γ Δᵍ Δ Θ t) → sizeᵗ (renTm ρg ρd ρt tm) ≡ sizeᵗ tm
  size-renᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t}
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′)
    (ts : List (Tm Γ Δᵍ Δ Θ t)) → sizeᵗˢ (renTms ρg ρd ρt ts) ≡ sizeᵗˢ ts

  -- (G3) reification at most doubles: each obs embed adds one
  -- strmᵗ node, each pair/sum node maps 1-1 (sizeᵉ-pos covers the
  -- obs base case's off-by-one) — induction like shellsᵛ-len
  size-reify : ∀ {n} {Γ : Ctx n} (t : Ty) (v : Val Γ t) →
    sizeᵗ (reify v) ≤ 2 * sizeᵛ t v

  -- (G4) substitution grows size at most linearly in the env cap:
  -- every varᵗ (size 1) becomes a weakened reified value ≤ 2V
  -- (G2 + G3), every other constructor maps 1-1 — the multiplicative
  -- form composes clause-by-clause (1 ≤ suc (2 * V) absorbs each
  -- suc).  Mutual over ᵉ/ᵗ/ᵗˢ, shaped like subΘ-capᵉ
  size-subΘᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (V : ℕ) (Θloc : List Ty)
    (σ : All (Val Γ) Θsub) (e : Exp Γ Δᵍ Δ (Θloc ++ Θsub) t) →
    EnvSize V σ → sizeᵉ (subΘExp Θloc σ e) ≤ sizeᵉ e * suc (2 * V)
  size-subΘᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (V : ℕ) (Θloc : List Ty)
    (σ : All (Val Γ) Θsub) (tm : Tm Γ Δᵍ Δ (Θloc ++ Θsub) t) →
    EnvSize V σ → sizeᵗ (subΘTm Θloc σ tm) ≤ sizeᵗ tm * suc (2 * V)
  size-subΘᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (V : ℕ) (Θloc : List Ty)
    (σ : All (Val Γ) Θsub) (ts : List (Tm Γ Δᵍ Δ (Θloc ++ Θsub) t)) →
    EnvSize V σ → sizeᵗˢ (subΘTms Θloc σ ts) ≤ sizeᵗˢ ts * suc (2 * V)

  -- (G5) the id-general seed inequality: prod≤3pow + the
  -- definitional collapse 2^2^2^(towerℕ h) ≡ towerℕ (3 + h) +
  -- towerℕ-mono over 3 + (4 + sz) * suc (suc id) ≤ (7 + sz) *
  -- suc (suc id) (the slack is 3 * suc id — solver-friendly) +
  -- m≤n+m for the pad head.  The V here is the LANDING budget
  -- (instant suc id's store bound — the walk contract's demand
  -- anchor); seed-covers above is NOT its id-0 instance (the burst
  -- anchors at the entry bound), so both stay
  budget-covers : ∀ (sz U id : ℕ) → U ≤ sz →
    let V = towerℕ ((4 + sz) * suc (suc id)) in
    suc (suc V * suc (suc V ^ suc V) * suc U)
      ≤ 2 ^ (sz * suc id * suc id) + towerℕ ((7 + sz) * suc (suc id))

  -- (G6) the no-fuel bursts are dry-free: no machine rule emits
  -- reason `dried`, so a concrete event list rejects dryEvent
  -- pointwise — a list induction over map value plus the literal
  -- init/close/complete heads
  oneShot-dry : ∀ {n} {Γ : Ctx n} {u} (vals : List (Val Γ u)) (id : Id)
    (sched : Sched Γ) →
    hasDry (proj₁ (oneShotBurst vals id sched)) ≡ false

  -- (G7) installing a bounded node state preserves the store
  -- invariant — all-preservation through setNode (insert or
  -- overwrite), shaped like sweepLive-bounded
  install-bounded : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (B : ℕ)
    (sched : Sched Γ) (st : EvalSt e) (nid : NodeId) (ns : NodeState Γ) →
    boundedNode B ns ≡ true → stBounded? B sched st ≡ true →
    stBounded? B sched (installNode nid ns st) ≡ true

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

envSize-lookup : ∀ {n} {Γ : Ctx n} {Θ t} (V : ℕ) (σ : All (Val Γ) Θ) →
  EnvSize V σ → (z : t ∈ Θ) → sizeᵛ t (lookupEnv σ z) ≤ V
envSize-lookup V (v ∷ᵃ σ) (hv , hσ) (here refl) = hv
envSize-lookup V (v ∷ᵃ σ) (hv , hσ) (there z)   = envSize-lookup V σ hσ z

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
--     2026-07-24: see (5) THE WIDTH LEDGER below.
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
--     against dBound-μ/-hop/-connect for the fuel; (c) the
--     lineage-indexed mixed receipt composing (2)'s receipts along
--     lineages instead of globally; (d) the landing: 𝔉 into the
--     boundary, replacing the two cores' landing halves.
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

postulate
  -- (W1) caseW is renaming- and substitution-INVARIANT: reify
  -- images weigh 0 (they contain no caseᵗ), and subΘ rewrites only
  -- var positions — mirror shellSize-ren / shellSize-subΘ exactly
  caseW-ren : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t}
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′)
    (tm : Tm Γ Δᵍ Δ Θ t) → caseWᵗ (renTm ρg ρd ρt tm) ≡ caseWᵗ tm
  caseW-reify : ∀ {n} {Γ : Ctx n} (t : Ty) (v : Val Γ t) →
    caseWᵗ (reify v) ≡ 0
  caseW-subΘ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (Θloc : List Ty)
    (σ : All (Val Γ) Θsub) (tm : Tm Γ Δᵍ Δ (Θloc ++ Θsub) t) →
    caseWᵗ (subΘTm Θloc σ tm) ≡ caseWᵗ tm

  -- (W2) fnCap closures: reification reads the value's own cap;
  -- substitution and μ-unfolding stay under the max of the pieces
  -- (max-shaped inductions, all clause-homomorphic)
  fnCap-reify : ∀ {n} {Γ : Ctx n} (t : Ty) (v : Val Γ t) →
    fnCapᵗ (reify v) ≡ fnCapᵛ t v
  fnCap-subΘᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (Ψ : ℕ) (Θloc : List Ty)
    (σ : All (Val Γ) Θsub) (e : Exp Γ Δᵍ Δ (Θloc ++ Θsub) t) →
    EnvFnCap Ψ σ → fnCapᵉ e ≤ Ψ → fnCapᵉ (subΘExp Θloc σ e) ≤ Ψ
  fnCap-elimG : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
    (cl : Closed Γ t) (e : Exp Γ Δᵍ Δ Θ u) →
    fnCapᵉ (elimGExp x cl e) ≤ fnCapᵉ e ⊔ fnCapᵉ cl

  -- (W3) THE SHARP EVAL BOUND — the walk ledger's load-bearing
  -- fact.  Same induction as evalWith-size, but the caseᵗ clause is
  -- the ONLY one that re-enters at a grown cap (via grow-pow, cost
  -- two exponent units + the branch's own weight); every other
  -- clause stays at V, with the sizeᵗ factor absorbing the +1s.
  -- The strmᵗ clause is size-subΘᵉ (linear), exponent 1.
  evalWith-sharp : ∀ {n} {Γ : Ctx n} {Θ t} (V : ℕ)
    (tm : Tm Γ [] [] Θ t) (env : All (Val Γ) Θ) →
    EnvSize V env → sizeᵗ tm ≤ V →
    sizeᵛ t (evalWith tm env) ≤ sizeᵗ tm * (2 + 2 * V) ^ (3 ^ caseWᵗ tm)

  -- (W4) eval never mints a new fn: every fn embedded in the result
  -- comes from the template's strm-subtrees (subΘ'd: template fns
  -- by caseW-subΘ, plug fns from the environment) or the
  -- environment directly
  fnCap-evalWith : ∀ {n} {Γ : Ctx n} {Θ t} (Ψ : ℕ)
    (tm : Tm Γ [] [] Θ t) (env : All (Val Γ) Θ) →
    EnvFnCap Ψ env → caseWᵗ tm ⊔ fnCapᵗ tm ≤ Ψ →
    fnCapᵛ t (evalWith tm env) ≤ Ψ

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

postulate
  -- (W5) receipts compose multiplicatively (pure ^-arithmetic)
  spendᴱ-compose : ∀ (Ψ r₁ s₁ r₂ s₂ : ℕ) →
    spendᴱ Ψ r₁ s₁ * spendᴱ Ψ r₂ s₂ ≡ spendᴱ Ψ (r₁ + r₂) (s₁ + s₂)

  -- (W6) the fold-run closed form: one scan run over a value list
  -- of length m, everything (fn size, seed, values) within the
  -- current cap, lands within the cap grown by the single factor
  -- 3^(suc caseW · m).  Recurrence: at position q ≥ E ≥ 2 one fold
  -- lands at E + (q+2)·3^w ≤ q·3^(suc w) (grow-pow + applyFn-sharp)
  scanVals-sharp : ∀ {n} {Γ : Ctx n} {s u} (W E : ℕ)
    (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (acc : Val Γ u)
    (vs : List (Val Γ s)) →
    2 ≤ E →
    sizeᵗ fn ≤ capᴱ W E → sizeᵛ u acc ≤ capᴱ W E →
    All (λ v → sizeᵛ s v ≤ capᴱ W E) vs →
    (sizeᵛ u (proj₂ (scanVals fn acc vs))
       ≤ capᴱ W (E * 3 ^ (suc (caseWᵗ fn) * length vs)))
    × All (λ o → sizeᵛ u o ≤ capᴱ W (E * 3 ^ (suc (caseWᵗ fn) * length vs)))
          (proj₁ (scanVals fn acc vs))

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

postulate
  -- (W7) all the in-flight predicates only ever need widening
  -- upward (≤ᵇ-widen through all, mirror boundedLive-widen)
  valB?-widen : ∀ {n} {Γ : Ctx n} {B B′ Ψ : ℕ} (u : Ty) (v : Val Γ u) →
    B ≤ B′ → valB? B Ψ u v ≡ true → valB? B′ Ψ u v ≡ true
  valsB?-widen : ∀ {n} {Γ : Ctx n} {B B′ Ψ : ℕ} (u : Ty)
    (vs : List (Val Γ u)) → B ≤ B′ →
    all (valB? B Ψ u) vs ≡ true → all (valB? B′ Ψ u) vs ≡ true
  burstB?-widen : ∀ {n} {Γ : Ctx n} {u} {B B′ Ψ : ℕ} (str : Stream Γ u) →
    B ≤ B′ → burstB? B Ψ str ≡ true → burstB? B′ Ψ str ≡ true
  frameB?-widen : ∀ {n} {Γ : Ctx n} {s u} {B B′ Ψ : ℕ} (f : Frame Γ s u) →
    B ≤ B′ → frameB? B Ψ f ≡ true → frameB? B′ Ψ f ≡ true
  pathB?-widen : ∀ {n} {Γ : Ctx n} {s t} {B B′ Ψ : ℕ} (p : Path Γ s t) →
    B ≤ B′ → pathB? B Ψ p ≡ true → pathB? B′ Ψ p ≡ true
  chainsB?-widen : ∀ {n} {Γ : Ctx n} {t} {B B′ Ψ : ℕ} {s : Ty}
    (chains : List (RegId × Path Γ s t)) → B ≤ B′ →
    all (λ rc → pathB? B Ψ (proj₂ rc)) chains ≡ true →
    all (λ rc → pathB? B′ Ψ (proj₂ rc)) chains ≡ true
  regsB?-widen : ∀ {n} {Γ : Ctx n} {t} {B B′ Ψ : ℕ}
    (reg : List (RegId × Source × Chain Γ t)) → B ≤ B′ →
    regsB? B Ψ reg ≡ true → regsB? B′ Ψ reg ≡ true

  -- (W8) burst plumbing: splitting a bounded emit yields bounded
  -- values; the bookkeeping side and retag images are value-free,
  -- so any bound covers them; wrapping bounded values back into
  -- events is pointwise (all list inductions)
  splitEvents-vals-B : ∀ {n} {Γ : Ctx n} {s u : Ty} (B Ψ : ℕ)
    (es : List (InstEvent (Val Γ s))) →
    all (eventB? B Ψ) es ≡ true →
    all (valB? B Ψ s) (proj₁ (splitEvents {A = Val Γ u} es)) ≡ true
  splitEvents-bk-B : ∀ {n} {Γ : Ctx n} {s u : Ty} (B Ψ : ℕ)
    (es : List (InstEvent (Val Γ s))) →
    all (eventB? B Ψ) (proj₁ (proj₂ (splitEvents {A = Val Γ u} es))) ≡ true
  retag-B : ∀ {n} {Γ : Ctx n} {u : Ty} {A : Set} (B Ψ : ℕ)
    (es : List (InstEvent A)) →
    all (eventB? B Ψ) (retagEvents {B = Val Γ u} es) ≡ true
  mapValue-B : ∀ {n} {Γ : Ctx n} (B Ψ : ℕ) (u : Ty) (vs : List (Val Γ u)) →
    all (valB? B Ψ u) vs ≡ true →
    all (eventB? B Ψ) (map value vs) ≡ true

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

postulate
  -- (W10) width invariance: EXACT mirrors of W2/W4 with fnCap
  -- replaced by ofW pointwise — same inductions, same ⊔ algebra;
  -- the only differing clause (ofᵉ) is length-preserving under
  -- subΘ/elimG (they map over the of-list)
  ofW-reify : ∀ {n} {Γ : Ctx n} (t : Ty) (v : Val Γ t) →
    ofWᵗ (reify v) ≡ ofWᵛ t v
  ofW-subΘᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (Ω : ℕ) (Θloc : List Ty)
    (σ : All (Val Γ) Θsub) (e : Exp Γ Δᵍ Δ (Θloc ++ Θsub) t) →
    EnvOfW Ω σ → ofWᵉ e ≤ Ω → ofWᵉ (subΘExp Θloc σ e) ≤ Ω
  ofW-elimG : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
    (cl : Closed Γ t) (e : Exp Γ Δᵍ Δ Θ u) →
    ofWᵉ (elimGExp x cl e) ≤ ofWᵉ e ⊔ ofWᵉ cl
  ofW-evalWith : ∀ {n} {Γ : Ctx n} {Θ t} (Ω : ℕ)
    (tm : Tm Γ [] [] Θ t) (env : All (Val Γ) Θ) →
    EnvOfW Ω env → ofWᵗ tm ≤ Ω →
    ofWᵛ t (evalWith tm env) ≤ Ω

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
    2 ≤ E →
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
-- against the frozen instant base W and a ledger position E ≥ 2.
------------------------------------------------------------------

postulate
  -- (W9) the node-install ring's fnCap face (mirror G7's
  -- install-bounded), the μ-copy size bound (elimG substitutes the
  -- closed μ at ≤ sizeᵉ body var positions), and the two
  -- state-manipulation clauses of the walk (input touches
  -- slots/registry/completed-latches across five sub-shapes;
  -- deferᵉ mints a live hop carrying its body as the pending value
  -- — both consume only INV?'s slots conjuncts + the register/
  -- install ring, no recursion)
  install-fnCap : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ψ : ℕ)
    (sched : Sched Γ) (st : EvalSt e) (nid : NodeId) (ns : NodeState Γ) →
    fnCapNode Ψ ns ≡ true → fnCapBounded? Ψ sched st ≡ true →
    fnCapBounded? Ψ sched (installNode nid ns st) ≡ true
  size-unfoldμ : ∀ {n} {Γ : Ctx n} {t} (body : Exp Γ (t ∷ []) [] [] t) →
    sizeᵉ (unfoldμ body) ≤ sizeᵉ (μᵉ body) * sizeᵉ (μᵉ body)
  subscribeE-input-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (Ψ W : ℕ) (g : Gas) (i : Fin n) (κ : Path Γ (lookup Γ i) t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
    2 ≤ E →
    INV? Ψ (capᴱ W E) sched st ≡ true →
    pathB? (capᴱ W E) Ψ κ ≡ true →
    let r = subscribeE g (input i) κ id now sched st
    in Σ ℕ λ E′ → (E ≤ E′)
       × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
       × (burstB? (capᴱ W E′) Ψ (proj₁ r) ≡ true)
  subscribeE-defer-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (Ψ W : ℕ) (g : Gas) (body : Closed Γ u) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
    2 ≤ E →
    INV? Ψ (capᴱ W E) sched st ≡ true →
    sizeᵉ body ≤ capᴱ W E → fnCapᵉ body ≤ Ψ →
    pathB? (capᴱ W E) Ψ κ ≡ true →
    let r = subscribeE g (deferᵉ body) κ id now sched st
    in Σ ℕ λ E′ → (E ≤ E′)
       × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
       × (burstB? (capᴱ W E′) Ψ (proj₁ r) ≡ true)

  chainStep-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (Ψ W : ℕ) (id : Id) (a : Arrival Γ)
    (path : Path Γ (arrTy a) t)
    (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
    2 ≤ E →
    INV? Ψ (capᴱ W E) sched st ≡ true →
    pathB? (capᴱ W E) Ψ path ≡ true →
    valB? (capᴱ W E) Ψ (arrTy a) (arrVal a) ≡ true →
    let r = chainStep id a path sched st
    in Σ ℕ λ E′ → (E ≤ E′)
       × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
       × (burstB? (capᴱ W E′) Ψ (proj₁ r) ≡ true)

  -- the four remaining per-frame cores of stepFrame-wet (the map
  -- clause is PROVEN below).  scan consumes scanVals-sharp + the
  -- node-lookup/install ring; take is a prefix + cutThrough sweep;
  -- the *All frames recurse into subscribeInner (the walk's mutual
  -- knot — they discharge together with subscribeE-walkS)
  stepFrame-scan-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (Ψ W : ℕ) (g : Gas) (id : Id) (now : Tick)
    (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (nid : NodeId) (κ : Path Γ u t)
    (vals : List (Val Γ s)) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
    2 ≤ E →
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

  stepFrame-take-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (Ψ W : ℕ) (g : Gas) (id : Id) (now : Tick)
    (nid : NodeId) (κ : Path Γ s t)
    (vals : List (Val Γ s)) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
    2 ≤ E →
    INV? Ψ (capᴱ W E) sched st ≡ true →
    pathB? (capᴱ W E) Ψ κ ≡ true →
    all (valB? (capᴱ W E) Ψ s) vals ≡ true →
    let r = stepFrame g id now (take-f nid) κ vals fin sched st
    in Σ ℕ λ E′ → (E ≤ E′)
       × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ (proj₂ (proj₂ r))))
                             (proj₂ (proj₂ (proj₂ (proj₂ r)))) ≡ true)
       × (all (valB? (capᴱ W E′) Ψ s) (proj₁ r) ≡ true)
       × (all (eventB? (capᴱ W E′) Ψ) (proj₁ (proj₂ r)) ≡ true)

  stepFrame-fromInner-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (Ψ W : ℕ) (g : Gas) (id : Id) (now : Tick)
    (op : AllOp) (allNid inst : NodeId) (κ : Path Γ s t)
    (vals : List (Val Γ s)) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
    2 ≤ E →
    INV? Ψ (capᴱ W E) sched st ≡ true →
    pathB? (capᴱ W E) Ψ κ ≡ true →
    all (valB? (capᴱ W E) Ψ s) vals ≡ true →
    let r = stepFrame g id now (from-inner op allNid inst) κ vals fin sched st
    in Σ ℕ λ E′ → (E ≤ E′)
       × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ (proj₂ (proj₂ r))))
                             (proj₂ (proj₂ (proj₂ (proj₂ r)))) ≡ true)
       × (all (valB? (capᴱ W E′) Ψ s) (proj₁ r) ≡ true)
       × (all (eventB? (capᴱ W E′) Ψ) (proj₁ (proj₂ r)) ≡ true)

  stepFrame-thruOuter-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (Ψ W : ℕ) (g : Gas) (id : Id) (now : Tick)
    (op : AllOp) (nid : NodeId) (κ : Path Γ u t)
    (vals : List (Val Γ (obs u))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
    2 ≤ E →
    INV? Ψ (capᴱ W E) sched st ≡ true →
    pathB? (capᴱ W E) Ψ κ ≡ true →
    all (valB? (capᴱ W E) Ψ (obs u)) vals ≡ true →
    let r = stepFrame g id now (thru-outer op nid) κ vals fin sched st
    in Σ ℕ λ E′ → (E ≤ E′)
       × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ (proj₂ (proj₂ r))))
                             (proj₂ (proj₂ (proj₂ (proj₂ r)))) ≡ true)
       × (all (valB? (capᴱ W E′) Ψ u) (proj₁ r) ≡ true)
       × (all (eventB? (capᴱ W E′) Ψ) (proj₁ (proj₂ r)) ≡ true)

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

E≤E*3^ : ∀ (E k : ℕ) → E ≤ E * 3 ^ k
E≤E*3^ E k = ≤-trans (≤-reflexive (sym (*-identityʳ E)))
                     (*-monoʳ-≤ E (one≤3^ k))

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
-- stepFrame-wet, now a REAL dispatch: the map clause proven end to
-- end on the ledger rule; the other frames delegate to their named
-- cores above
------------------------------------------------------------------

stepFrame-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (Ψ W : ℕ) (g : Gas) (id : Id) (now : Tick)
  (f : Frame Γ s u) (κ : Path Γ u t)
  (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  2 ≤ E →
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
stepFrame-wet Ψ W g id now (map-f fn) κ vals fin sched st E 2≤E inv fB pB vB =
  E * 3 ^ suc Ψ , E≤E*3^ E (suc Ψ) ,
  INV?-widen sched st (capᴱ-mono W (E≤E*3^ E (suc Ψ))) inv ,
  map-applyFn-B Ψ W E fn 2≤E capsOK szOK vals vB ,
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
  2 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  frameB? (capᴱ W E) Ψ f ≡ true →
  pathB? (capᴱ W E) Ψ κ ≡ true →
  burstB? (capᴱ W E) Ψ ems ≡ true →
  let r = pushBurst g id now f κ ems sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstB? (capᴱ W E′) Ψ (proj₁ r) ≡ true)
pushBurst-wet Ψ W g id now f κ [] sched st E 2≤E inv fB pB bB =
  E , ≤-refl , inv , refl
pushBurst-wet {Γ = Γ} {s = s} {u = u} Ψ W g id now f κ (em ∷ ems)
              sched st E 2≤E inv fB pB bB =
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
            sched st E 2≤E inv fB pB
            (splitEvents-vals-B B₀ Ψ (InstEmit.events em) emB)
  E₁    = proj₁ W1
  E≤E₁  = proj₁ (proj₂ W1)
  inv₁  = proj₁ (proj₂ (proj₂ W1))
  outB  = proj₁ (proj₂ (proj₂ (proj₂ W1)))
  cap₁  = capᴱ-mono W E≤E₁

  rec   = pushBurst-wet Ψ W g id now f κ ems
            (proj₁ (proj₂ (proj₂ (proj₂ step))))
            (proj₂ (proj₂ (proj₂ (proj₂ step))))
            E₁ (≤-trans 2≤E E≤E₁) inv₁
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
  2 ≤ E →
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
  2 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  boundedNode (capᴱ W E) ns ≡ true → fnCapNode Ψ ns ≡ true →
  sizeᵉ b ≤ capᴱ W E → fnCapᵉ b ≤ Ψ →
  pathB? (capᴱ W E) Ψ κ ≡ true →
  let r = subscribeAll g op ns b κ id now sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstB? (capᴱ W E′) Ψ (proj₁ r) ≡ true)
subscribeAll-wet Ψ W g op ns b κ id now sched st E 2≤E inv bn fnn szB fcB pB =
  E₂ , ≤-trans E≤E₁ E₁≤E₂ , inv₂ , b₂
  where
  nid    = Sched.nextNode sched
  sched₁ = proj₂ (mintNode sched)
  st₀    = installNode nid ns st
  inv₀   = install-INV Ψ (capᴱ W E) sched₁ st nid ns bn fnn inv
  sE      = subscribeE g b (thru-outer op nid ↠ κ) id now sched₁ st₀
  IH     = subscribeE-walkS Ψ W g b (thru-outer op nid ↠ κ) id now
             sched₁ st₀ E 2≤E inv₀ szB fcB (∧-intro refl pB)
  E₁     = proj₁ IH
  E≤E₁   = proj₁ (proj₂ IH)
  inv₁   = proj₁ (proj₂ (proj₂ IH))
  bB₁    = proj₂ (proj₂ (proj₂ IH))
  cap₁   = capᴱ-mono W E≤E₁
  PB     = pushBurst-wet Ψ W g id now (thru-outer op nid) κ (proj₁ sE)
             (proj₁ (proj₂ sE)) (proj₂ (proj₂ sE)) E₁
             (≤-trans 2≤E E≤E₁) inv₁ refl (pathB?-widen κ cap₁ pB) bB₁
  E₂     = proj₁ PB
  E₁≤E₂  = proj₁ (proj₂ PB)
  inv₂   = proj₁ (proj₂ (proj₂ PB))
  b₂     = proj₂ (proj₂ (proj₂ PB))

subscribeE-walkS Ψ W g (input i) κ id now sched st E 2≤E inv szB fcB pB =
  subscribeE-input-wet Ψ W g i κ id now sched st E 2≤E inv pB

subscribeE-walkS {Γ = Γ} {u = u} Ψ W g (ofᵉ ts) κ id now sched st E 2≤E inv szB fcB pB =
  E * 3 ^ suc Ψ , E≤E*3^ E (suc Ψ) ,
  INV?-widen (record sched { nextSource = suc (Sched.nextSource sched) }) st
    (capᴱ-mono W (E≤E*3^ E (suc Ψ))) inv ,
  ∧-intro
    (∧-intro refl
      (all-++-intro _ (map value (map (λ tm → evalTm tm) ts)) _
        (mapValue-B (capᴱ W (E * 3 ^ suc Ψ)) Ψ u (map (λ tm → evalTm tm) ts)
          (ofVals-B Ψ W E 2≤E ts (≤-trans (n≤1+n (sizeᵗˢ ts)) szB) fcB))
        refl))
    refl

subscribeE-walkS Ψ W g emptyᵉ κ id now sched st E 2≤E inv szB fcB pB =
  E , ≤-refl , inv , refl

subscribeE-walkS Ψ W g (mapᵉ f b) κ id now sched st E 2≤E inv szB fcB pB =
  E₂ , ≤-trans E≤E₁ E₁≤E₂ , inv₂ , b₂
  where
  szf  = ≤-trans (≤-trans (m≤m+n (sizeᵗ f) (sizeᵉ b)) (n≤1+n _)) szB
  szb  = ≤-trans (≤-trans (m≤n+m (sizeᵉ b) (sizeᵗ f)) (n≤1+n _)) szB
  capf = ≤-trans (m≤m⊔n (caseWᵗ f ⊔ fnCapᵗ f) (fnCapᵉ b)) fcB
  fcb  = ≤-trans (m≤n⊔m (caseWᵗ f ⊔ fnCapᵗ f) (fnCapᵉ b)) fcB
  fB   : frameB? (capᴱ W E) Ψ (map-f f) ≡ true
  fB   = ∧-intro (T⇒≡true _ (≤⇒≤ᵇ szf)) (T⇒≡true _ (≤⇒≤ᵇ capf))
  sE    = subscribeE g b (map-f f ↠ κ) id now sched st
  IH   = subscribeE-walkS Ψ W g b (map-f f ↠ κ) id now sched st E 2≤E inv
           szb fcb (∧-intro fB pB)
  E₁   = proj₁ IH
  E≤E₁ = proj₁ (proj₂ IH)
  inv₁ = proj₁ (proj₂ (proj₂ IH))
  bB₁  = proj₂ (proj₂ (proj₂ IH))
  cap₁ = capᴱ-mono W E≤E₁
  PB   = pushBurst-wet Ψ W g id now (map-f f) κ (proj₁ sE)
           (proj₁ (proj₂ sE)) (proj₂ (proj₂ sE)) E₁ (≤-trans 2≤E E≤E₁)
           inv₁ (frameB?-widen (map-f f) cap₁ fB) (pathB?-widen κ cap₁ pB) bB₁
  E₂   = proj₁ PB
  E₁≤E₂ = proj₁ (proj₂ PB)
  inv₂ = proj₁ (proj₂ (proj₂ PB))
  b₂   = proj₂ (proj₂ (proj₂ PB))

subscribeE-walkS Ψ W g (takeᵉ count b) κ id now sched st E 2≤E inv szB fcB pB
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
  IH     = subscribeE-walkS Ψ W g b (take-f nid ↠ κ) id now sched₁ st₀ E 2≤E
             inv₀ szb fcb (∧-intro refl pB)
  E₁     = proj₁ IH
  E≤E₁   = proj₁ (proj₂ IH)
  inv₁   = proj₁ (proj₂ (proj₂ IH))
  bB₁    = proj₂ (proj₂ (proj₂ IH))
  cap₁   = capᴱ-mono W E≤E₁
  PB     = pushBurst-wet Ψ W g id now (take-f nid) κ (proj₁ sE)
             (proj₁ (proj₂ sE)) (proj₂ (proj₂ sE)) E₁
             (≤-trans 2≤E E≤E₁) inv₁ refl (pathB?-widen κ cap₁ pB) bB₁
  E₂     = proj₁ PB
  E₁≤E₂  = proj₁ (proj₂ PB)
  inv₂   = proj₁ (proj₂ (proj₂ PB))
  b₂     = proj₂ (proj₂ (proj₂ PB))

subscribeE-walkS {Γ = Γ} {u = u} Ψ W g (scanᵉ f z b) κ id now sched st E 2≤E inv szB fcB pB =
  E₃ , ≤-trans E≤E₁ (≤-trans E₁≤E₂ E₂≤E₃) , inv₃ , b₃
  where
  E₁    = E * 3 ^ suc Ψ
  E≤E₁  = E≤E*3^ E (suc Ψ)
  2≤E₁  = ≤-trans 2≤E E≤E₁
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
  seedB = evalTm-cap Ψ W E z 2≤E
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
            2≤E₁ inv₀ (≤-trans szb cap₁) fcb
            (∧-intro fB₁ (pathB?-widen κ cap₁ pB))
  E₂    = proj₁ IH
  E₁≤E₂ = proj₁ (proj₂ IH)
  inv₂  = proj₁ (proj₂ (proj₂ IH))
  bB₂   = proj₂ (proj₂ (proj₂ IH))
  cap₂  = capᴱ-mono W E₁≤E₂
  PB    = pushBurst-wet Ψ W g id now (scan-f f nid) κ (proj₁ sE)
            (proj₁ (proj₂ sE)) (proj₂ (proj₂ sE)) E₂
            (≤-trans 2≤E₁ E₁≤E₂) inv₂ (frameB?-widen (scan-f f nid) cap₂ fB₁)
            (pathB?-widen κ (capᴱ-mono W (≤-trans E≤E₁ E₁≤E₂)) pB) bB₂
  E₃    = proj₁ PB
  E₂≤E₃ = proj₁ (proj₂ PB)
  inv₃  = proj₁ (proj₂ (proj₂ PB))
  b₃    = proj₂ (proj₂ (proj₂ PB))

subscribeE-walkS Ψ W g (mergeAllᵉ b) κ id now sched st E 2≤E inv szB fcB pB =
  subscribeAll-wet Ψ W g mergeᵒ (merge-st 0 false) b κ id now sched st E
    2≤E inv refl refl (≤-trans (n≤1+n (sizeᵉ b)) szB) fcB pB
subscribeE-walkS {u = u} Ψ W g (concatAllᵉ b) κ id now sched st E 2≤E inv szB fcB pB =
  subscribeAll-wet Ψ W g concatᵒ (concat-st {t = u} [] false false) b κ id now
    sched st E 2≤E inv refl refl (≤-trans (n≤1+n (sizeᵉ b)) szB) fcB pB
subscribeE-walkS Ψ W g (switchAllᵉ b) κ id now sched st E 2≤E inv szB fcB pB =
  subscribeAll-wet Ψ W g switchᵒ (switch-st nothing false) b κ id now sched st E
    2≤E inv refl refl (≤-trans (n≤1+n (sizeᵉ b)) szB) fcB pB
subscribeE-walkS Ψ W g (exhaustAllᵉ b) κ id now sched st E 2≤E inv szB fcB pB =
  subscribeAll-wet Ψ W g exhaustᵒ (exhaust-st false false) b κ id now sched st E
    2≤E inv refl refl (≤-trans (n≤1+n (sizeᵉ b)) szB) fcB pB

subscribeE-walkS Ψ W g0 (μᵉ body) κ id now sched st E 2≤E inv szB fcB pB =
  E , ≤-refl , inv , refl
subscribeE-walkS Ψ W (gs fuel) (μᵉ body) κ id now sched st E 2≤E inv szB fcB pB =
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
           (≤-trans 2≤E E≤2E) (INV?-widen sched st cap2 inv) szU fcU
           (pathB?-widen κ cap2 pB)

subscribeE-walkS Ψ W g (varᵉ ()) κ id now sched st E 2≤E inv szB fcB pB

subscribeE-walkS Ψ W g (deferᵉ body) κ id now sched st E 2≤E inv szB fcB pB =
  subscribeE-defer-wet Ψ W g body κ id now sched st E 2≤E inv
    (≤-trans (n≤1+n (sizeᵉ body)) szB) fcB pB

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
  2 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  all (λ rc → pathB? (capᴱ W E) Ψ (proj₂ rc)) chains ≡ true →
  valB? (capᴱ W E) Ψ (arrTy a) (arrVal a) ≡ true →
  let r = cascadeGo a id chains sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstB? (capᴱ W E′) Ψ (proj₁ r) ≡ true)
cascadeGo-walk Ψ W a id [] sched st E 2≤E inv chB vB =
  E , ≤-refl , inv , refl
cascadeGo-walk Ψ W a id ((rid , c) ∷ chains) sched st E 2≤E inv chB vB
  with ∧-true (pathB? (capᴱ W E) Ψ c) _ chB
... | pc , pchains with any (_≡ᵇ rid) (EvalSt.cancelled st)
... | true  = cascadeGo-walk Ψ W a id chains sched st E 2≤E inv pchains vB
... | false =
  let st₀ = record st { delivered = rid ∷ EvalSt.delivered st }
      (E₁ , E≤E₁ , inv₁ , em₁) =
        chainStep-wet Ψ W id a c sched st₀ E 2≤E inv pc vB
      cap≤ = capᴱ-mono W E≤E₁
      (E₂ , E₁≤E₂ , inv₂ , em₂) =
        cascadeGo-walk Ψ W a id chains
          (proj₁ (proj₂ (chainStep id a c sched st₀)))
          (proj₂ (proj₂ (chainStep id a c sched st₀)))
          E₁ (≤-trans 2≤E E≤E₁) inv₁
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
--      x]), and the embedded-value hop lands on a first-scan acc
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
