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
--      burst-init, burst-final.  Postulated: the step lemmas
--      (subscribeE-wf, mid-step — the per-clause preservation
--      grind), mid-init, mid-skip, mid-final, and the single
--      budget-sufficient totality conjecture at the bottom.
--   3. The compositions — the subscribe frame, the chain fold, the
--      fuel loop, and the theorem — are all DEFINED, glued by
--      runProtocol's distribution over ++.
module Verify-Well-Formed where

open import Data.Bool    using (Bool; true; false; if_then_else_; _∧_; _∨_; not; T)
open import Data.Fin     using (Fin; toℕ)
open import Data.Vec     using (lookup)
open import Data.Nat     using (ℕ; zero; suc; _≤_; z≤n; s≤s; _≡ᵇ_; _<ᵇ_; _≤ᵇ_; _+_; _∸_)
open import Data.Nat.Properties using (≤-refl; 1+n≰n; ≤⇒≤ᵇ; +-suc; +-comm; +-assoc; +-identityʳ)
open import Data.List    using (List; []; _∷_; _++_; any; length; map)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Unit    using (⊤; tt)
open import Data.Empty   using (⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Relation.Nullary using (Dec; yes; no)

open import Rx.Prim      using (Fuel; Tick; Id; Source; Ordinal; InstEmit;
                                InstEvent; init; value; close; handoff; complete;
                                EmitKind; delivery; CloseReason; exhausted;
                                cut; cutPending; _at_from_as_)
open import Rx.Exp       using (Ctx; Closed; Ty; _≟ᵗ_; Val)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; Slots; Stream;
                                RegId; Chain; Path; root; share-sink; _↠_; Frame;
                                sched-init; st-init; sched-next; LiveSource;
                                schedGo; schedHeadOf; schedFinish; schedEarlier;
                                arrTy; arrSource; arrVal; arrTick;
                                chainsOf; chainsGo; chainStep;
                                foldPath; dispatchShare; stepFrame;
                                cascadeLatch; cascadeGo; cascadeFinish;
                                subscribeE; cascade; drain; evaluate;
                                sameSource; drySource; dryEvent; hasDry;
                                dropSource; sweepLive; budgetAt)
open import Rx.Protocol  using (ProtocolSt; Owed; countIn; allZero; protocol-init;
                                stepProtocol; runProtocol; paidUp; settle; hasOwed;
                                payOwed; paidOff; applyEvents; removeOne;
                                cancelOwed; bumpOwed; settleInstant;
                                checkFinal; Accepted; accepted; WellFormed)

------------------------------------------------------------------
-- glue: runProtocol distributes over ++, and a fully-paid final
-- state is accepted
------------------------------------------------------------------

_>>=ᴹ_ : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
just a  >>=ᴹ f = f a
nothing >>=ᴹ f = nothing

runProtocol-++ : ∀ {A} (S : ProtocolSt) (xs ys : List (InstEmit A)) →
  runProtocol S (xs ++ ys)
    ≡ (runProtocol S xs >>=ᴹ λ S′ → runProtocol S′ ys)
runProtocol-++ S []       ys = refl
runProtocol-++ S (x ∷ xs) ys with stepProtocol x S
... | just S′ = runProtocol-++ S′ xs ys
... | nothing = refl

run-++-just : ∀ {A} (S : ProtocolSt) (xs ys : List (InstEmit A))
              {S₁ S₂ : ProtocolSt} →
  runProtocol S xs ≡ just S₁ → runProtocol S₁ ys ≡ just S₂ →
  runProtocol S (xs ++ ys) ≡ just S₂
run-++-just S xs ys {S₁} e₁ e₂ =
  trans (runProtocol-++ S xs ys)
        (trans (cong (λ m → m >>=ᴹ (λ S′ → runProtocol S′ ys)) e₁) e₂)

acceptPaid : (S : ProtocolSt) → paidUp S ≡ true → Accepted (checkFinal (just S))
acceptPaid S eq rewrite eq = accepted

-- dry-freeness splits over ++ (the step lemmas are conditioned on it;
-- budget-sufficient below asserts it for the whole seeded run)
true≢false : {A : Set} → true ≡ false → A
true≢false ()

hasDry-++ : ∀ {A : Set} (xs ys : List (InstEmit A)) →
  hasDry (xs ++ ys) ≡ false →
  (hasDry xs ≡ false) × (hasDry ys ≡ false)
hasDry-++ []        ys h = refl , h
hasDry-++ (em ∷ xs) ys h
  with sameSource (InstEmit.source em) drySource
     | any dryEvent (InstEmit.events em)
... | true  | _     = true≢false h
... | false | true  = true≢false h
... | false | false = hasDry-++ xs ys h

------------------------------------------------------------------
-- Inv, CONCRETE: the between-cascades simulation relation
------------------------------------------------------------------

-- registrations of s, counted off the registry (the writer's ledger
-- the automaton's live multiset must shadow)
countRegs : ∀ {n} {Γ : Ctx n} {t}
          → Source → List (RegId × Source × Chain Γ t) → ℕ
countRegs s [] = zero
countRegs s ((_ , x , _) ∷ r) =
  if s ≡ᵇ x then suc (countRegs s r) else countRegs s r

-- the pending-event ledger: how many init/close for source s sit in an
-- accumulated evs (frames add registrations + init, cuts remove + close;
-- the protocol only drains these at the terminal emit, so mid-fold the
-- registry leads live by exactly initCount ∸ closeCount — the SHADOW three-way)
initCount : ∀ {A : Set} → Source → List (InstEvent A) → ℕ
initCount s []              = zero
initCount s (init x   ∷ es) = if s ≡ᵇ x then suc (initCount s es) else initCount s es
initCount s (value _  ∷ es) = initCount s es
initCount s (close _ _ ∷ es) = initCount s es
initCount s (handoff _ ∷ es) = initCount s es
initCount s (complete ∷ es) = initCount s es

closeCount : ∀ {A : Set} → Source → List (InstEvent A) → ℕ
closeCount s []              = zero
closeCount s (close x _ ∷ es) = if s ≡ᵇ x then suc (closeCount s es) else closeCount s es
closeCount s (init _   ∷ es) = closeCount s es
closeCount s (value _  ∷ es) = closeCount s es
closeCount s (handoff _ ∷ es) = closeCount s es
closeCount s (complete ∷ es) = closeCount s es

-- (registry-dropping closes — cut/cutPending, excluding the deferred
-- `exhausted` — will be counted by a cutCloseCount helper when the take-head
-- edge of reg-envSrc-out is handled; see the FoldOut blueprint above)

-- snapshot entries still obliged to fire: not yet forgiven by a
-- cutPending (the automaton's remaining owed for the arrival source)
countRemaining : ∀ {X : Set} → List (RegId × X) → List RegId → ℕ
countRemaining []               c = zero
countRemaining ((rid , _) ∷ ps) c =
  if any (_≡ᵇ rid) c then countRemaining ps c else suc (countRemaining ps c)

-- association-list reads on the automaton's owed table
lookupOwed : Source → Owed → ℕ
lookupOwed s []            = zero
lookupOwed s ((x , n) ∷ o) = if s ≡ᵇ x then n else lookupOwed s o

-- every source but s is paid to zero (bumped shares get paid back
-- down within the very chainStep that announced them)
zeroExcept : Source → Owed → Bool
zeroExcept s []            = true
zeroExcept s ((x , n) ∷ o) =
  (if s ≡ᵇ x then true else n ≡ᵇ 0) ∧ zeroExcept s o

-- the owed table's keys never repeat (bumpOwed adds to an existing
-- entry, never a second one): with `zeroExcept s` this pins down every
-- entry, so a zero at s means the whole table is zero (allZero-clean)
notKeyOwed : Source → Owed → Bool
notKeyOwed s []            = true
notKeyOwed s ((x , _) ∷ o) = not (s ≡ᵇ x) ∧ notKeyOwed s o

UniqueOwed : Owed → Bool
UniqueOwed []            = true
UniqueOwed ((x , _) ∷ o) = notKeyOwed x o ∧ UniqueOwed o

-- a path that never reaches the root delivers no values there
sinksToShare : ∀ {n} {Γ : Ctx n} {u t} → Path Γ u t → Bool
sinksToShare root           = false
sinksToShare (share-sink i) = true
sinksToShare (f ↠ p)        = sinksToShare p

allShareSunk : ∀ {n} {Γ : Ctx n} {t}
             → List (RegId × Source × Chain Γ t) → Bool
allShareSunk []                      = true
allShareSunk ((_ , _ , (u , p)) ∷ r) = sinksToShare p ∧ allShareSunk r

-- the registry↔schedule type-consistency invariant (replaces the old
-- one-lookahead chains-count): every registration's source-type matches
-- every live source of the same source.  Share-sunk registrations whose
-- source has no live entry are unconstrained — chainsOf only ever reads
-- entries of a SCHEDULED source, and those all trace to a LiveSource, so
-- this pins their type-check to pass (chains-count-derived below)
sameTy : Ty → Ty → Bool
sameTy s u with s ≟ᵗ u
... | yes _ = true
... | no  _ = false

liveTypeOK? : ∀ {n} {Γ : Ctx n} → Source → Ty → List (LiveSource Γ) → Bool
liveTypeOK? s u []       = true
liveTypeOK? s u (l ∷ ls) =
  (if LiveSource.source l ≡ᵇ s then sameTy u (LiveSource.elemTy l) else true)
    ∧ liveTypeOK? s u ls

regTyped? : ∀ {n} {Γ : Ctx n} {t} → List (RegId × Source × Chain Γ t)
          → List (LiveSource Γ) → Bool
regTyped? []                      live = true
regTyped? ((_ , s , (u , _)) ∷ r) live = liveTypeOK? s u live ∧ regTyped? r live

≡ᵇ→≡ : ∀ (m k : ℕ) → (m ≡ᵇ k) ≡ true → m ≡ k
≡ᵇ→≡ zero    zero    _ = refl
≡ᵇ→≡ (suc m) (suc k) h = cong suc (≡ᵇ→≡ m k h)

≡ᵇ-refl : ∀ (m : ℕ) → (m ≡ᵇ m) ≡ true
≡ᵇ-refl zero    = refl
≡ᵇ-refl (suc m) = ≡ᵇ-refl m

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
    live-matches  : ∀ (s : Source) →
      countIn s (ProtocolSt.live S) ≡ countRegs s (EvalSt.registry st)
    reg-typed     : regTyped? (EvalSt.registry st) (Sched.live sched) ≡ true
    horizon-low   : ProtocolSt.horizon S ≤ id
    current-frame : (ProtocolSt.current S ≡ nothing)
                  ⊎ (ProtocolSt.current S ≡ just (id , []))
    done-plumbed  : ProtocolSt.done S ≡ true →
      allShareSunk (EvalSt.registry st) ≡ true

-- the empty states are related
burst-init : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  BurstInv {e = e} 0 (sched-init e ins) (st-init e) protocol-init
burst-init e ins = record
  { live-matches  = λ s → refl
  ; reg-typed     = refl
  ; horizon-low   = z≤n
  ; current-frame = inj₁ refl
  ; done-plumbed  = λ ()
  }

postulate
  -- ONE subscription's burst preserves the frame relation.  The
  -- per-primitive preservation induction: one obligation per
  -- subscribeE clause, mirrored on its (now fuel-structural)
  -- recursion.  Conditioned on the run not going dry: a fuel-starved
  -- burst carries the dry sentinel, which the protocol rejects by
  -- design — the unconditioned statement would be false at fuel 0
  subscribeE-wf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (fuel : ℕ) (b : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
    BurstInv id sched st S →
    hasDry (proj₁ (subscribeE fuel b κ id now sched st)) ≡ false →
    Σ ProtocolSt λ S′ →
      let r = subscribeE fuel b κ id now sched st
      in (runProtocol S (proj₁ r) ≡ just S′)
         × BurstInv id (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) S′

-- an instant standing on an empty (or absent) owed table settles
≤-up : ∀ {a b : ℕ} → a ≤ b → a ≤ suc b
≤-up z≤n     = z≤n
≤-up (s≤s p) = s≤s (≤-up p)

paid-nothing : (S : ProtocolSt) → ProtocolSt.current S ≡ nothing →
               paidUp S ≡ true
paid-nothing S ceq with ProtocolSt.current S | ceq
... | nothing | refl = refl

paid-empty : (S : ProtocolSt) {j : Id} →
             ProtocolSt.current S ≡ just (j , []) → paidUp S ≡ true
paid-empty S ceq with ProtocolSt.current S | ceq
... | just (j , []) | refl = refl

-- leaving the frame: the open instant settles (owed never seeded ⇒
-- paid), landing Inv-related for the first arrival
burst-final : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
  BurstInv 0 sched st S →
  Inv 1 sched st S × (paidUp S ≡ true)
burst-final sched st S binv = inv , paid (BurstInv.current-frame binv)
  where
  past : (ProtocolSt.current S ≡ nothing)
       ⊎ (ProtocolSt.current S ≡ just (0 , [])) →
       CurrentPast (ProtocolSt.current S) 1
  past (inj₁ ceq) = subst (λ c → CurrentPast c 1) (sym ceq) tt
  past (inj₂ ceq) = subst (λ c → CurrentPast c 1) (sym ceq) (s≤s z≤n)

  paid : (ProtocolSt.current S ≡ nothing)
       ⊎ (ProtocolSt.current S ≡ just (0 , [])) →
       paidUp S ≡ true
  paid (inj₁ ceq) = paid-nothing S ceq
  paid (inj₂ ceq) = paid-empty S ceq

  inv : Inv 1 sched st S
  inv = record
    { live-matches = BurstInv.live-matches binv
    ; reg-typed    = BurstInv.reg-typed binv
    ; horizon-low  = ≤-up (BurstInv.horizon-low binv)
    ; current-past = past (BurstInv.current-frame binv)
    ; done-plumbed = BurstInv.done-plumbed binv
    }

-- the root subscription, composed (at the budget evaluate seeds)
subscribe-wf :
  ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  hasDry (proj₁ (subscribeE (budgetAt e ins 0) e root 0 0
                            (sched-init e ins) (st-init e))) ≡ false →
  Σ ProtocolSt λ S →
    let r = subscribeE (budgetAt e ins 0) e root 0 0
                       (sched-init e ins) (st-init e)
    in (runProtocol protocol-init (proj₁ r) ≡ just S)
       × Inv 1 (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) S
       × (paidUp S ≡ true)
subscribe-wf e ins nodry
  with subscribeE-wf (budgetAt e ins 0) e root 0 0
                     (sched-init e ins) (st-init e)
                     protocol-init (burst-init e ins) nodry
... | S , run , binv
  with burst-final _ _ S binv
... | inv , paid = S , run , inv , paid

------------------------------------------------------------------
-- one cascade: Mid and its entry/step/exit lemmas, the chain fold
-- composed
------------------------------------------------------------------

-- mid-cascade, CONCRETE, indexed by the chains still to fold.  Two
-- asymmetries a naive "live shadows registry" misses:
--   · for a spent (isLast) arrival the automaton runs AHEAD of the
--     registry — each delivered chain's exhausted close retires its
--     live entry on the spot, but the registry entries drop only at
--     cascadeFinish — so the arrival source's live count equals the
--     obliged remainder of the snapshot, not the registry count;
--   · the owed table exists only once the first chain emit has
--     opened the instant (seeding happens at first delivery), so the
--     ledger is a sum: not-yet-opened (the automaton still stands on
--     the previous, settled instant) or opened with owed[arrSource]
--     = the not-yet-cancelled remainder and every share paid back to
--     zero (a handoff's bump is repaid within its own chainStep).
-- fold-live carries dry-freeness for the remaining fold: Mid's
-- arguments determine every future chainStep, so the premise lives
-- here instead of infecting every step statement
record Mid {n} {Γ : Ctx n} {t} {e : Closed Γ t}
           (a : Arrival Γ) (nextId : Id)
           (ps : List (RegId × Path Γ (arrTy a) t))
           (sched : Sched Γ) (st : EvalSt e)
           (S : ProtocolSt) : Set where
  field
    live-others  : ∀ (s : Source) → sameSource s (arrSource a) ≡ false →
      countIn s (ProtocolSt.live S) ≡ countRegs s (EvalSt.registry st)
    live-source  : countIn (arrSource a) (ProtocolSt.live S)
      ≡ (if Arrival.isLast a
         then countRemaining ps (EvalSt.cancelled st)
         else countRegs (arrSource a) (EvalSt.registry st))
    reg-typed    : regTyped? (EvalSt.registry st) (Sched.live sched) ≡ true
    horizon-low  : ProtocolSt.horizon S ≤ nextId
    ledger       :
        (CurrentPast (ProtocolSt.current S) nextId × (paidUp S ≡ true))
      ⊎ (Σ Owed λ ow →
           (ProtocolSt.current S ≡ just (nextId , ow))
         × (lookupOwed (arrSource a) ow
              ≡ countRemaining ps (EvalSt.cancelled st))
         × (zeroExcept (arrSource a) ow ≡ true))
    -- after the root completes, only share plumbing survives.  Stated over
    -- the registry cascadeFinish will KEEP (drop the arrival's source iff
    -- isLast, exactly as cascadeFinish does): a completing root chain flips
    -- `done` while its own non-share-sunk registration still sits in the
    -- registry until cascadeFinish sheds it, so the full-registry form is
    -- false in that mid-cascade window.  The load-bearing evaluator fact is
    -- that at the done-flip every non-share-sunk survivor belongs to
    -- arrSource a (a completion only reaches the root once nothing else can
    -- deliver) — so dropping arrSource restores allShareSunk.  mid-final
    -- reads this off directly in both isLast branches (it mirrors
    -- cascadeFinish); mid-init establishes it from Inv's full-registry form
    -- (identity when not isLast; allShareSunk-drop when isLast).
    done-plumbed : ProtocolSt.done S ≡ true →
      allShareSunk (if Arrival.isLast a
                    then dropSource (arrSource a) (EvalSt.registry st)
                    else EvalSt.registry st) ≡ true
    fold-live    : hasDry (proj₁ (cascadeGo a nextId ps sched st)) ≡ false
    -- ADDED (owed-key uniqueness): the open instant's owed table has no
    -- repeated key, so ledger's zeroExcept + the arrival's zero remainder
    -- force allZero — the payoff mid-final reads out.  Preserved by
    -- mid-skip (same S); established by mid-init/mid-step (postulated).
    owed-unique  : ∀ (ow : Owed) →
      ProtocolSt.current S ≡ just (nextId , ow) → UniqueOwed ow ≡ true

------------------------------------------------------------------
-- Protocol foundation for foldPath-wf: a CONSTRUCTIVE stepProtocol.
-- enterInstant abstracts stepProtocol's enter/openFresh split (idle,
-- held, continue) into one Maybe (base-owed × horizon-for-go): `just`
-- means the automaton admits instant i, seeding `go` with that owed and
-- horizon.  stepProtocol-enter then rebuilds stepProtocol's result from
-- that plus the settle and applyEvents outcomes — the reverse of
-- The-Proof's stepProtocol-idle/held/cont (construction, not analysis).
------------------------------------------------------------------

openFreshᴵ : ProtocolSt → Id → Maybe (Owed × Id)
openFreshᴵ S i with settleInstant S
... | nothing = nothing
... | just hz = if hz ≤ᵇ i then just ([] , hz) else nothing

enterInstant : ProtocolSt → Id → Maybe (Owed × Id)
enterInstant S i with ProtocolSt.current S
... | nothing         = openFreshᴵ S i
... | just (j , owed) = if i ≡ᵇ j
      then (if paidOff owed then nothing else just (owed , ProtocolSt.horizon S))
      else openFreshᴵ S i

stepProtocol-enter-aux : ∀ {A : Set} (es : List (InstEvent A)) (i : Id) (s : Source)
  (k : EmitKind) (lv : List Source) (hz : Id) (dn : Bool) (cur : Maybe (Id × Owed))
  {ob hz′ ob′} {L : List Source} {O : Owed} {D : Bool} →
  enterInstant (record { live = lv ; horizon = hz ; current = cur ; done = dn }) i
    ≡ just (ob , hz′) →
  settle k s lv ob ≡ just ob′ →
  applyEvents es lv ob′ dn ≡ just (L , O , D) →
  stepProtocol (es at i from s as k)
    (record { live = lv ; horizon = hz ; current = cur ; done = dn })
    ≡ just (record { live = L ; horizon = hz′ ; current = just (i , O) ; done = D })
stepProtocol-enter-aux es i s k lv hz dn nothing entEq stEq apEq
  with hz ≤ᵇ i | entEq
... | true | refl rewrite stEq | apEq = refl
stepProtocol-enter-aux es i s k lv hz dn (just (j , owed)) entEq stEq apEq
  with i ≡ᵇ j | entEq
... | true  | e with paidOff owed | e
...   | false | refl rewrite stEq | apEq = refl
stepProtocol-enter-aux es i s k lv hz dn (just (j , owed)) entEq stEq apEq
    | false | e
  with allZero owed | e
...   | true | e′ with suc j ≤ᵇ i | e′
...     | true | refl rewrite stEq | apEq = refl

stepProtocol-enter : ∀ {A : Set} (es : List (InstEvent A)) (i : Id) (s : Source)
  (k : EmitKind) (S : ProtocolSt) {ob hz′ ob′} {L : List Source} {O : Owed} {D : Bool} →
  enterInstant S i ≡ just (ob , hz′) →
  settle k s (ProtocolSt.live S) ob ≡ just ob′ →
  applyEvents es (ProtocolSt.live S) ob′ (ProtocolSt.done S) ≡ just (L , O , D) →
  stepProtocol (es at i from s as k) S
    ≡ just (record { live = L ; horizon = hz′ ; current = just (i , O) ; done = D })
stepProtocol-enter es i s k S entEq stEq apEq =
  stepProtocol-enter-aux es i s k (ProtocolSt.live S) (ProtocolSt.horizon S)
    (ProtocolSt.done S) (ProtocolSt.current S) entEq stEq apEq

-- applyEvents plumbing for the root emit: it splits over ++, the
-- accumulated bookkeeping (init/close only — never value/complete, which
-- splitEvents routes to the value list / done flag) leaves `done`
-- untouched, and the value list + optional complete tack on cleanly.
just-injᵂ : ∀ {A : Set} {x y : A} → _≡_ {A = Maybe A} (just x) (just y) → x ≡ y
just-injᵂ refl = refl

applyEvents-++just : ∀ {A : Set} (es₁ es₂ : List (InstEvent A))
  (lv : List Source) (o : Owed) (d : Bool) {L : List Source} {O : Owed} {D : Bool} →
  applyEvents es₁ lv o d ≡ just (L , O , D) →
  applyEvents (es₁ ++ es₂) lv o d ≡ applyEvents es₂ L O D
applyEvents-++just [] es₂ lv o d eq with just-injᵂ eq
... | refl = refl
applyEvents-++just (init x ∷ es) es₂ lv o d eq =
  applyEvents-++just es es₂ (x ∷ lv) o d eq
applyEvents-++just (value v ∷ es) es₂ lv o d eq with d | eq
... | false | eq′ = applyEvents-++just es es₂ lv o false eq′
... | true  | ()
applyEvents-++just (handoff x ∷ es) es₂ lv o d eq =
  applyEvents-++just es es₂ lv (bumpOwed x (countIn x lv) o) d eq
applyEvents-++just (complete ∷ es) es₂ lv o d eq =
  applyEvents-++just es es₂ lv o true eq
applyEvents-++just (close x cutPending ∷ es) es₂ lv o d eq
  with removeOne x lv | cancelOwed x o | eq
... | just lv′ | just o′ | eq′ = applyEvents-++just es es₂ lv′ o′ d eq′
... | just lv′ | nothing | ()
... | nothing  | just o′ | ()
... | nothing  | nothing | ()
applyEvents-++just (close x cut ∷ es) es₂ lv o d eq with removeOne x lv | eq
... | just lv′ | eq′ = applyEvents-++just es es₂ lv′ o d eq′
... | nothing  | ()
applyEvents-++just (close x exhausted ∷ es) es₂ lv o d eq with removeOne x lv | eq
... | just lv′ | eq′ = applyEvents-++just es es₂ lv′ o d eq′
... | nothing  | ()

-- the value list changes nothing but must not ride behind a `complete`
-- (done-nil: a done automaton delivers no value) — so it folds to identity
applyEvents-values : ∀ {A : Set} (vals : List A) (lv : List Source) (o : Owed) (d : Bool) →
  (d ≡ true → vals ≡ []) →
  applyEvents (map value vals) lv o d ≡ just (lv , o , d)
applyEvents-values []       lv o d _    = refl
applyEvents-values (v ∷ vs) lv o d cond with d | cond
... | false | _ = applyEvents-values vs lv o false (λ ())
... | true  | c with c refl
...   | ()

-- the optional trailing complete sets done exactly when fin
applyEvents-maybeComplete : ∀ {A : Set} (fin : Bool) (lv : List Source) (o : Owed) (d : Bool) →
  applyEvents {A} (if fin then complete ∷ [] else []) lv o d
    ≡ just (lv , o , (if fin then true else d))
applyEvents-maybeComplete true  lv o d = refl
applyEvents-maybeComplete false lv o d = refl

-- the whole root tail (values then optional complete) after the evs
applyEvents-vc : ∀ {A : Set} (vals : List A) (fin : Bool)
  (lv : List Source) (o : Owed) (d : Bool) → (d ≡ true → vals ≡ []) →
  applyEvents (map value vals ++ (if fin then complete ∷ [] else [])) lv o d
    ≡ just (lv , o , (if fin then true else d))
applyEvents-vc vals fin lv o d cond =
  trans (applyEvents-++just (map value vals) (if fin then complete ∷ [] else [])
          lv o d (applyEvents-values vals lv o d cond))
        (applyEvents-maybeComplete fin lv o d)

runProtocol-one : ∀ {A : Set} (S : ProtocolSt) (x : InstEmit A) →
  runProtocol S (x ∷ []) ≡ stepProtocol x S
runProtocol-one S x with stepProtocol x S
... | just S′ = refl
... | nothing = refl

-- foldPath-wf, ROOT clause (PROVEN): a chain that reaches the root emits
-- its ONE delivery — accumulated bookkeeping evs, then the (possibly
-- empty) value list, then complete iff the source is spent.  The
-- automaton admits it (enterInstant), pays envSrc's owed (settle), folds
-- the evs (which never touch `done`), and the values ride only if not
-- already done (done-nil).  sched/st are untouched at root.
foldPath-root-wf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sf gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
  (vals : List (Val Γ t)) (evs : List (InstEvent (Val Γ t))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt)
  (ob : Owed) (hz : Id) (ob′ : Owed) (Lv : List Source) (Ov : Owed) →
  enterInstant S id ≡ just (ob , hz) →
  settle delivery envSrc (ProtocolSt.live S) ob ≡ just ob′ →
  applyEvents evs (ProtocolSt.live S) ob′ (ProtocolSt.done S)
    ≡ just (Lv , Ov , ProtocolSt.done S) →
  (ProtocolSt.done S ≡ true → vals ≡ []) →
  runProtocol S (proj₁ (foldPath sf gas id now envSrc root vals evs fin sched st))
    ≡ just (record { live = Lv ; horizon = hz ; current = just (id , Ov)
                   ; done = (if fin then true else ProtocolSt.done S) })
foldPath-root-wf sf gas id now envSrc vals evs fin sched st S ob hz ob′ Lv Ov
  entEq payEq apEq dn =
  trans (runProtocol-one S _) stepEq
  where
  target : ProtocolSt
  target = record { live = Lv ; horizon = hz ; current = just (id , Ov)
                  ; done = (if fin then true else ProtocolSt.done S) }
  apply-full :
    applyEvents (evs ++ map value vals ++ (if fin then complete ∷ [] else []))
      (ProtocolSt.live S) ob′ (ProtocolSt.done S)
      ≡ just (Lv , Ov , (if fin then true else ProtocolSt.done S))
  apply-full = trans
    (applyEvents-++just evs (map value vals ++ (if fin then complete ∷ [] else []))
      (ProtocolSt.live S) ob′ (ProtocolSt.done S) apEq)
    (applyEvents-vc vals fin Lv Ov (ProtocolSt.done S) dn)
  stepEq :
    stepProtocol
      ((evs ++ map value vals ++ (if fin then complete ∷ [] else []))
        at id from envSrc as delivery) S
      ≡ just target
  stepEq = stepProtocol-enter
    (evs ++ map value vals ++ (if fin then complete ∷ [] else []))
    id envSrc delivery S entEq payEq apply-full

------------------------------------------------------------------
-- foldPath-wf: one chain's fold, by induction on the Path (free source
-- type u — the split lives HERE, not at mid-step, see the blueprint).
-- FoldInv is the mid-fold relation: the automaton admits instant id,
-- pays envSrc, and the bookkeeping accumulated so far (evs) folds
-- cleanly, with the value list gated by done-nil.  root is PROVEN
-- (foldPath-root-wf); the frame case is IH ∘ stepFrame-wf (same emits,
-- definitionally — a frame accumulates evs, never emits); share defers
-- to dispatchShare-wf.  Acceptance only for now; the Mid-preservation
-- half (the POST) is the next layer.
------------------------------------------------------------------

record FoldInv {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
       (id : Id) (envSrc : Source) (vals : List (Val Γ u))
       (evs : List (InstEvent (Val Γ t))) (fin : Bool)
       (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) : Set where
  field
    ob   : Owed
    hz   : Id
    ob′  : Owed
    Lv   : List Source
    Ov   : Owed
    enters   : enterInstant S id ≡ just (ob , hz)
    pays     : settle delivery envSrc (ProtocolSt.live S) ob ≡ just ob′
    applies  : applyEvents evs (ProtocolSt.live S) ob′ (ProtocolSt.done S)
                 ≡ just (Lv , Ov , ProtocolSt.done S)
    -- SHADOW (three-way): mid-fold the registry LEADS the automaton's live
    -- multiset by exactly the pending evs (stepFrame mutates the registry and
    -- brackets it with init/close in evs, but never steps the protocol; the
    -- terminal emit drains evs into live).  For every source but the chain's
    -- own, live + pending inits ≡ registry + pending closes.  Collapses to
    -- Mid.live-others at the seed (evs has no init, its lone close is envSrc's)
    -- and resyncs to live-others-out once applyEvents drains evs at the root.
    shadow   : ∀ (s : Source) → sameSource s envSrc ≡ false →
      countIn s (ProtocolSt.live S) + initCount s evs
        ≡ countRegs s (EvalSt.registry st) + closeCount s evs
    -- ADJUDICATED (2026-07): an envShadow twin of SHADOW here — countIn envSrc
    -- live + initCount ≡ countRegs envSrc registry + cutCloseCount — is FALSE
    -- at the mid-seed isLast branch: it reduces to countIn ≡ countRegs, but
    -- Mid.live-source (isLast) gives countIn ≡ countRemaining, and mid-cascade
    -- countRegs ≠ countRemaining (delivered isLast chains linger in the
    -- registry until cascadeFinish).  So envSrc is NOT a seed-provable FoldInv
    -- invariant; its live-source readoff lives in FoldOut as output deltas
    -- (live-envSrc-out : live S′ ≡ live S ∸ (if fin then 1 else 0), universal;
    -- reg-envSrc-out via cutCloseCount over the emit, no-take-head first).
    -- once the root completes only share plumbing survives: every
    -- registration sinks to a share, so a share fan-out's inners are all
    -- share-bound (their own done-discipline, for dispatchShare-wf).
    -- Conditioned on `fin` exactly as Mid.done-plumbed is on isLast — the
    -- seed feeds this through unchanged (envSrc = arrSource a, fin = isLast a)
    done-plumbed : ProtocolSt.done S ≡ true →
      allShareSunk (if fin then dropSource envSrc (EvalSt.registry st)
                    else EvalSt.registry st) ≡ true

------------------------------------------------------------------
-- FoldOut — the readoff companion to FoldInv (DESIGN, worked out 2026-07;
-- not yet stated as code — see the obligations below, any one of which if
-- false would make FoldOut a false postulate, so they are discharged before
-- the record lands).  foldPath-wf will return, alongside `Σ S′ (runProtocol
-- ≡ just S′)`, a FoldOut relating the fold's OUTPUT triple (S′, st″, sched″)
-- to its inputs, from which mid-step reads Mid ps off directly.
--
-- WHY A THREE-WAY INVARIANT (the frame case is NOT a live↔registry
-- pass-through).  stepFrame mutates the registry — subscribeInner adds an
-- entry AND emits `init`; a take/switch cut removes an entry AND emits
-- `close` (Evaluator take-f, lines ~540) — but stepFrame does NOT step the
-- protocol.  live S only catches up when the ACCUMULATED evs are applied at
-- the terminal root/share emit.  So mid-fold the registry LEADS and live LAGS
-- by exactly the pending evs.  The invariant threading through frames is thus
-- three-way, per source s ≠ envSrc:
--
--   countIn s (live S) + initCount s evs ≡ countRegs s (registry st)
--                                          + closeCount s evs      … (SHADOW)
--
--   (initCount/closeCount = # of `init s` / `close s _` in the pending evs;
--    envSrc is excluded — its own delivery/close is accounted separately.)
--   • SEED: evs = if isLast then [close envSrc] else []; for s≠envSrc both
--     counts are 0, so SHADOW ⇔ Mid.live-others — provided by mid-seed.
--   • stepFrame PRESERVES SHADOW: each clause's registry delta is matched by
--     its evs′ init/close delta (bracketing) — the enriched stepFrame-wf duty.
--   • ROOT base: applyEvents drains evs into live, so countIn s Lv = countIn s
--     (live S) + initCount − closeCount = countRegs s (registry st) (registry
--     unchanged by root) ⇒ live-others-out.  SHADOW is thus added to FoldInv.
--
-- FoldOut FIELDS (postcondition at the output S′, st″, sched″), each tagged
-- with the Mid ps field it discharges and its establishing obligation:
--   1 live-others-out : ∀ s≠envSrc, countIn s (live S′) ≡ countRegs s
--       (registry st″)                                    [Mid ps.live-others]
--   2 live-src-out    : countIn envSrc (live S′) ≡
--       countIn envSrc (live S) ∸ closeCount envSrc evsᶠ  [→ live-source]
--       (evsᶠ = the accumulated evs reaching the root).  KEYED ON closeCount,
--       NOT on fin: the seed close of envSrc rides evs (isLast), and a take
--       CUT also emits `close envSrc` (cutThrough, Evaluator 253) — both must
--       count.  At the seed closeCount envSrc evs = if isLast then 1 else 0.
--       OBLIGATION: frames/shares emit no OTHER close on envSrc (inner sources
--       are fresh defs; a share node toℕ i is downstream, so envSrc ≢ toℕ i —
--       shown, not assumed).  With Mid(head∷ps).live-source (isLast branch):
--       countRemaining(head∷ps) ∸1 = countRemaining ps (head uncancelled, ceq).
--   3 reg-envSrc-fixed: countRegs envSrc (registry st″) ≡ countRegs envSrc
--       (registry st) ∸ closeCount envSrc evsᶠ — the fold removes an envSrc
--       registration exactly when it emits an envSrc close (a take cut does
--       BOTH atomically: cutThrough drops it from `kept` AND emits its close;
--       the seed isLast close is the LONE exception — it removes from live but
--       leaves the registration for cascadeFinish).  So for s = envSrc the
--       SHADOW three-way holds up to that one seed close, which is precisely
--       why the done-plumbed conditional (drop iff isLast) is correct: an
--       isLast exhaustion leaves the registration for cascadeFinish (drop
--       branch); a take completion already removed it in-band (full-registry
--       branch is clean).  The two completion routes hit the two branches.
--   4 reg-typed-out   : regTyped? (registry st″) (Sched.live sched″) ≡ true
--                                                         [Mid ps.reg-typed]
--   5 horizon-out     : ProtocolSt.horizon S′ ≡ FoldInv.hz ⇒ ≤ nextId, via
--       enters + Mid.horizon-low                          [Mid ps.horizon-low]
--   6 current-out     : current S′ ≡ just (nextId , Ov) with lookupOwed envSrc
--       Ov = (owed after the head's delivery decrement)   [ledger inj₂,
--       owed-unique] — the OUTPUT-side twin of mid-seed's owed arithmetic.
--   7 done-out        : done S′ ≡ (if finᶠ then true else done S) where finᶠ is
--       the THREADED fin at the root (a take cut flips it true even when not
--       isLast — foldPath root, Evaluator 961); done-plumbed via the
--       conditional field, correct by the field-3 self-healing argument.
--                                                         [Mid ps.done-plumbed]
--   (fold-live is NOT a FoldOut field — it names a/nextId/ps, absent from the
--    fold; mid-step peels it from Mid(head∷ps).fold-live directly.)
--
-- PER-CASE establishment of FoldOut:
--   root        : all fields concrete from foldPath-root-wf + SHADOW.
--   f ↠ path′   : foldPath frame ≡ foldPath path′ (transformed state), so the
--                 OUTPUT triple is the recursion's — the OUTPUT-ONLY fields
--                 pass THROUGH unchanged (only st″/sched″/S′, identical for
--                 outer and recursion); the frame's bookkeeping is absorbed by
--                 SHADOW (enriched stepFrame-wf re-establishes FoldInv).
--   share-sink i: handoff + fan-out (enriched dispatchShare-wf).  handoff
--                 bumps owed[i] by countIn i (live); the fan-out repays one
--                 per registration and (isLast) dropSource i at finish resyncs
--                 registry i against the fan-out's closes — the diamond.
--
-- WHICH FIELDS ARE FoldOut vs. FoldInv (traced 2026-07):
--  • OUTPUT-ONLY (clean FoldOut fields — reference only st″/sched″/S′, so they
--    pass through the frame recursion): live-others-out (s≠envSrc, from SHADOW),
--    reg-typed-out, horizon-out, current-out, done-plumbed-out.  current-out is
--      Σ Ov, current S′ ≡ just(id,Ov) × zeroExcept envSrc Ov × UniqueOwed Ov
--            × lookupOwed envSrc Ov ≡ lookupOwed envSrc ob′
--    (ob′ = FoldInv.ob′ — post-settle owed, invariant through frames).  OWED
--    TRACE: settle delivery seeds owed[envSrc]=countIn envSrc live on the first
--    delivery then pays one (later deliveries just pay); close envSrc exhausted
--    is non-cutPending so applyEvents leaves owed alone; the fan-out touches
--    only owed[toℕ i].  Hence lookupOwed envSrc Ov ≡ lookupOwed envSrc ob′,
--    uniformly.  mid-step then ties lookupOwed envSrc ob′ to countRemaining ps
--    via the ledger (inj₂ pays the entered owed once; inj₁ seeds countIn∸1).
--  • The envSrc LIVE/REGISTRY readoff is NOT a clean FoldOut field — it is
--    entangled with the cascade snapshot and belongs in FoldInv (threaded),
--    for three reasons found by tracing:
--     (1) reason-based drops: cut/cutPending drop registry+live together
--         (cutThrough); the seed exhausted is live-ONLY (registry deferred to
--         cascadeFinish).  So the envSrc analog of SHADOW must use a
--         cutCloseCount (cut+cutPending only), not closeCount.
--     (2) a take in the head path cuts the head's OWN envSrc registration
--         mid-fold, so any statement keyed on the seed evs undercounts — the
--         real count is the full accumulated evs, an internal fold quantity, so
--         it cannot be a FoldOut field parameterised by the seed evs.
--     (3) isLast vs not use DIFFERENT targets (countRemaining ps vs countRegs),
--         and mid-cascade countRegs envSrc ≠ countRemaining (delivered isLast
--         chains linger in the registry), so no single output-only envSrc
--         identity covers both.
--    DESIGN NEXT: add envShadow to FoldInv —
--      countIn envSrc live + initCount envSrc evs
--        ≡ countRegs envSrc registry + cutCloseCount envSrc evs
--    (the seed exhausted close is excluded on BOTH sides: not a cutClose, and
--    it is the lone live-drop the registry defers), threaded by stepFrame-wf/
--    dispatchShare-wf exactly like SHADOW, with the isLast/countRemaining
--    connection made at mid-step off Mid.live-source + the ledger.  The
--    take-head corner (head's own cut close + cancellation) is the one edge to
--    pin with a Unit-Test before relying on it.
------------------------------------------------------------------

-- the fold's output EvalSt (st″) and Sched (sched″)
foldSt : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sf gas : ℕ) (id : Id) (now : Tick) (envSrc : Source) (path : Path Γ u t)
  (vals : List (Val Γ u)) (evs : List (InstEvent (Val Γ t))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) → EvalSt e
foldSt sf gas id now envSrc path vals evs fin sched st =
  proj₂ (proj₂ (foldPath sf gas id now envSrc path vals evs fin sched st))

foldSched : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sf gas : ℕ) (id : Id) (now : Tick) (envSrc : Source) (path : Path Γ u t)
  (vals : List (Val Γ u)) (evs : List (InstEvent (Val Γ t))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) → Sched Γ
foldSched sf gas id now envSrc path vals evs fin sched st =
  proj₁ (proj₂ (foldPath sf gas id now envSrc path vals evs fin sched st))

-- FoldOut: the readoff companion to FoldInv (the POST of one chain's fold).
-- All fields reference only the OUTPUT triple (st″/sched″/S′) plus the input
-- live S (unchanged by frames) and ob′ — so they pass through the frame
-- recursion; envSrc live/registry are output deltas (see the blueprint above).
record FoldOut {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
       (sf gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
       (path : Path Γ u t) (vals : List (Val Γ u)) (evs : List (InstEvent (Val Γ t)))
       (fin : Bool) (sched : Sched Γ) (st : EvalSt e)
       (ob′ : Owed) (S S′ : ProtocolSt) : Set where
  field
    -- [Mid ps.live-others] SHADOW resynced by applyEvents at the terminal emit
    live-others-out : ∀ (s : Source) → sameSource s envSrc ≡ false →
      countIn s (ProtocolSt.live S′)
        ≡ countRegs s (EvalSt.registry (foldSt sf gas id now envSrc path vals evs fin sched st))
    -- [→ live-source] the chain delivers envSrc once; every close of envSrc
    -- (seed exhausted OR a take cut) drops it from live under fin ≡ true
    live-envSrc-out : countIn envSrc (ProtocolSt.live S′)
      ≡ countIn envSrc (ProtocolSt.live S) ∸ (if fin then suc zero else zero)
    -- [→ live-source, non-isLast] registry envSrc unchanged (frames touch inner
    -- sources; the seed exhausted defers to cascadeFinish).  no-take-head; the
    -- take-head cut edge (registry ∸ cutCloseCount envSrc) is deferred
    reg-envSrc-out : countRegs envSrc (EvalSt.registry (foldSt sf gas id now envSrc path vals evs fin sched st))
      ≡ countRegs envSrc (EvalSt.registry st)
    -- [Mid ps.reg-typed]
    reg-typed-out :
      regTyped? (EvalSt.registry (foldSt sf gas id now envSrc path vals evs fin sched st))
                (Sched.live (foldSched sf gas id now envSrc path vals evs fin sched st)) ≡ true
    -- [Mid ps.horizon-low]
    horizon-out : ProtocolSt.horizon S′ ≤ id
    -- [Mid ps.ledger inj₂ + owed-unique] the delivery pays owed[envSrc] once;
    -- lookupOwed envSrc Ov ≡ lookupOwed envSrc ob′ (applyEvents/fan-out leave
    -- owed[envSrc] alone); zeroExcept from the share diamond, UniqueOwed from
    -- bumpOwed.  mid-step ties lookupOwed envSrc ob′ to countRemaining ps
    current-out : Σ Owed λ Ov →
        (ProtocolSt.current S′ ≡ just (id , Ov))
      × (zeroExcept envSrc Ov ≡ true)
      × (UniqueOwed Ov ≡ true)
      × (lookupOwed envSrc Ov ≡ lookupOwed envSrc ob′)
    -- [Mid ps.done-plumbed] conditional exactly as cascadeFinish drops
    done-plumbed-out : ProtocolSt.done S′ ≡ true →
      allShareSunk (if fin
                    then dropSource envSrc (EvalSt.registry (foldSt sf gas id now envSrc path vals evs fin sched st))
                    else EvalSt.registry (foldSt sf gas id now envSrc path vals evs fin sched st)) ≡ true

postulate
  -- a frame preserves FoldInv (S untouched — frames don't step the
  -- automaton): stepFrame's bookkeeping evs′ brackets against its
  -- registry mutation, and the value transform keeps done-nil.  The
  -- delivery-side twin of subscribeE-wf's per-clause grind (map/scan/
  -- take/*All), one obligation per stepFrame clause.
  stepFrame-wf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {w u}
    (sf : ℕ) (id : Id) (now : Tick) (envSrc : Source)
    (f : Frame Γ w u) (path′ : Path Γ u t)
    (vals : List (Val Γ w)) (evs : List (InstEvent (Val Γ t))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
    FoldInv id envSrc vals evs fin sched st S →
    let (vals′ , evs′ , fin′ , sched₁ , st₁) = stepFrame sf id now f path′ vals fin sched st
    in FoldInv id envSrc vals′ (evs ++ evs′) fin′ sched₁ st₁ S

  -- the share fan-out: one handoff emit, then one delivery per share
  -- registration (each its own foldPath) — mutually recursive with
  -- foldPath-wf.  The handoff's owed bump is repaid across the fan-out.
  dispatchShare-wf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sf gas : ℕ) (id : Id) (now : Tick) (envSrc : Source) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i)))
    (evs : List (InstEvent (Val Γ t))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
    FoldInv id envSrc vals evs fin sched st S →
    Σ ProtocolSt λ S′ →
      runProtocol S (proj₁ (foldPath sf gas id now envSrc (share-sink i) vals evs fin sched st))
        ≡ just S′

-- the done-discipline, as a precondition: a done automaton (root already
-- completed) admits only share-bound folds — a chain reaching the root
-- after completion would be a value-after-complete, which the protocol
-- rejects.  At root (sinksToShare = false) this forces done S ≡ false, so
-- the value list rides; it transfers unchanged through a frame and is
-- vacuous at a share-sink.
-- a hypothesis whose codomain reduces to false forces its subject false
force-false : (b : Bool) → (b ≡ true → false ≡ true) → b ≡ false
force-false false _ = refl
force-false true  d with d refl
... | ()

foldPath-wf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sf gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
  (path : Path Γ u t) (vals : List (Val Γ u)) (evs : List (InstEvent (Val Γ t)))
  (fin : Bool) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
  FoldInv id envSrc vals evs fin sched st S →
  (ProtocolSt.done S ≡ true → sinksToShare path ≡ true) →
  Σ ProtocolSt λ S′ →
    runProtocol S (proj₁ (foldPath sf gas id now envSrc path vals evs fin sched st))
      ≡ just S′
foldPath-wf sf gas id now envSrc root vals evs fin sched st S fi ds =
  _ , foldPath-root-wf sf gas id now envSrc vals evs fin sched st S
        (FoldInv.ob fi) (FoldInv.hz fi) (FoldInv.ob′ fi) (FoldInv.Lv fi) (FoldInv.Ov fi)
        (FoldInv.enters fi) (FoldInv.pays fi) (FoldInv.applies fi) done-nil
  where
  df : ProtocolSt.done S ≡ false
  df = force-false (ProtocolSt.done S) ds
  done-nil : ProtocolSt.done S ≡ true → vals ≡ []
  done-nil deq with trans (sym df) deq
  ... | ()
foldPath-wf sf gas id now envSrc (f ↠ path′) vals evs fin sched st S fi ds =
  foldPath-wf sf gas id now envSrc path′
    (proj₁ (stepFrame sf id now f path′ vals fin sched st))
    (evs ++ proj₁ (proj₂ (stepFrame sf id now f path′ vals fin sched st)))
    (proj₁ (proj₂ (proj₂ (stepFrame sf id now f path′ vals fin sched st))))
    (proj₁ (proj₂ (proj₂ (proj₂ (stepFrame sf id now f path′ vals fin sched st)))))
    (proj₂ (proj₂ (proj₂ (proj₂ (stepFrame sf id now f path′ vals fin sched st)))))
    S (stepFrame-wf sf id now envSrc f path′ vals evs fin sched st S fi) ds
foldPath-wf sf gas id now envSrc (share-sink i) vals evs fin sched st S fi ds =
  dispatchShare-wf sf gas id now envSrc i vals evs fin sched st S fi

------------------------------------------------------------------
-- The seed: Mid (head ∷ ps) ⇒ FoldInv at the chainStep seed.  The
-- "counting machine" arithmetic — a key with a positive owed is not
-- paid-off; paying it decrements the key; a source present in `live`
-- can be removed.  These are the owed/live manipulations the enter,
-- pay, and applyEvents seed fields turn on.
------------------------------------------------------------------

lookup-pos-not-allZero : ∀ (s : Source) (ow : Owed) (k : ℕ) →
  lookupOwed s ow ≡ suc k → allZero ow ≡ false
lookup-pos-not-allZero s [] k ()
lookup-pos-not-allZero s ((x , zero)  ∷ ow) k eq with s ≡ᵇ x | eq
... | true  | ()
... | false | eq′ = lookup-pos-not-allZero s ow k eq′
lookup-pos-not-allZero s ((x , suc n) ∷ ow) k eq = refl

lookup-pos-not-paidOff : ∀ (s : Source) (ow : Owed) (k : ℕ) →
  lookupOwed s ow ≡ suc k → paidOff ow ≡ false
lookup-pos-not-paidOff s [] k ()
lookup-pos-not-paidOff s (e ∷ ow) k eq = lookup-pos-not-allZero s (e ∷ ow) k eq

T→≡ : ∀ (b : Bool) → T b → b ≡ true
T→≡ true _ = refl

≤→≤ᵇ : ∀ {m n : ℕ} → m ≤ n → (m ≤ᵇ n) ≡ true
≤→≤ᵇ {m} {n} p = T→≡ (m ≤ᵇ n) (≤⇒≤ᵇ p)

-- the automaton admits an OPEN unpaid instant: enterInstant continues it,
-- seeding go with the running owed and the standing horizon.  Fields taken
-- literally so enterInstant's `with current` reduces (enterInstant reads
-- only current/horizon, never live/done, so the dummies are harmless)
enterInstant-cont-aux : ∀ (lv : List Source) (hz i : Id) (cur : Maybe (Id × Owed))
  (dn : Bool) (ow : Owed) →
  cur ≡ just (i , ow) → paidOff ow ≡ false →
  enterInstant (record { live = lv ; horizon = hz ; current = cur ; done = dn }) i
    ≡ just (ow , hz)
enterInstant-cont-aux lv hz i .(just (i , ow)) dn ow refl pf rewrite ≡ᵇ-refl i | pf = refl

enterInstant-cont : ∀ (S : ProtocolSt) (i : Id) (ow : Owed) →
  ProtocolSt.current S ≡ just (i , ow) → paidOff ow ≡ false →
  enterInstant S i ≡ just (ow , ProtocolSt.horizon S)
enterInstant-cont S i ow cur pf =
  enterInstant-cont-aux (ProtocolSt.live S) (ProtocolSt.horizon S) i
    (ProtocolSt.current S) (ProtocolSt.done S) ow cur pf

-- a strictly-greater id is not equal (for the held instant's i ≢ j)
≢ᵇ-from-< : ∀ {j i : ℕ} → j ≤ i → (suc i ≡ᵇ j) ≡ false
≢ᵇ-from-< z≤n     = refl
≢ᵇ-from-< (s≤s q) = ≢ᵇ-from-< q

sucle→≢ᵇ : ∀ {j nextId : ℕ} → suc j ≤ nextId → (nextId ≡ᵇ j) ≡ false
sucle→≢ᵇ (s≤s q) = ≢ᵇ-from-< q

-- the automaton opens FRESH over an idle slot: settleInstant is the
-- standing horizon, admitted once horizon ≤ i
enterInstant-idle-aux : ∀ (lv : List Source) (hz i : Id) (cur : Maybe (Id × Owed))
  (dn : Bool) → cur ≡ nothing → (hz ≤ᵇ i) ≡ true →
  enterInstant (record { live = lv ; horizon = hz ; current = cur ; done = dn }) i
    ≡ just ([] , hz)
enterInstant-idle-aux lv hz i .nothing dn refl hle rewrite hle = refl

enterInstant-idle : ∀ (S : ProtocolSt) (i : Id) →
  ProtocolSt.current S ≡ nothing → (ProtocolSt.horizon S ≤ᵇ i) ≡ true →
  enterInstant S i ≡ just ([] , ProtocolSt.horizon S)
enterInstant-idle S i cn hle =
  enterInstant-idle-aux (ProtocolSt.live S) (ProtocolSt.horizon S) i
    (ProtocolSt.current S) (ProtocolSt.done S) cn hle

-- the automaton opens FRESH over a HELD paid instant j (i ≢ j): the
-- departed instant pushes the horizon to suc j, admitted once suc j ≤ i
enterInstant-held-aux : ∀ (lv : List Source) (hz i j : Id) (cur : Maybe (Id × Owed))
  (ow : Owed) (dn : Bool) → cur ≡ just (j , ow) →
  (i ≡ᵇ j) ≡ false → allZero ow ≡ true → (suc j ≤ᵇ i) ≡ true →
  enterInstant (record { live = lv ; horizon = hz ; current = cur ; done = dn }) i
    ≡ just ([] , suc j)
enterInstant-held-aux lv hz i j .(just (j , ow)) ow dn refl ieq az sle
  rewrite ieq | az | sle = refl

enterInstant-held : ∀ (S : ProtocolSt) (i j : Id) (ow : Owed) →
  ProtocolSt.current S ≡ just (j , ow) → (i ≡ᵇ j) ≡ false →
  allZero ow ≡ true → (suc j ≤ᵇ i) ≡ true →
  enterInstant S i ≡ just ([] , suc j)
enterInstant-held S i j ow cur ieq az sle =
  enterInstant-held-aux (ProtocolSt.live S) (ProtocolSt.horizon S) i j
    (ProtocolSt.current S) ow (ProtocolSt.done S) cur ieq az sle

-- a paid automaton holding instant j has that instant's owed all-zero
-- (else settleInstant would reject and paidUp be false)
paidUp-held-aux : ∀ (lv : List Source) (hz : Id) (cur : Maybe (Id × Owed))
  (dn : Bool) (j : Id) (ow : Owed) → cur ≡ just (j , ow) →
  paidUp (record { live = lv ; horizon = hz ; current = cur ; done = dn }) ≡ true →
  allZero ow ≡ true
paidUp-held-aux lv hz .(just (j , ow)) dn j ow refl pu with allZero ow | pu
... | true  | _  = refl
... | false | ()

paidUp-held : ∀ (S : ProtocolSt) (j : Id) (ow : Owed) →
  ProtocolSt.current S ≡ just (j , ow) → paidUp S ≡ true → allZero ow ≡ true
paidUp-held S j ow cur pu =
  paidUp-held-aux (ProtocolSt.live S) (ProtocolSt.horizon S) (ProtocolSt.current S)
    (ProtocolSt.done S) j ow cur pu

-- the fresh-open entry, dispatched on the (explicit) current value so
-- enterInstant reduces: idle when the slot is empty, held over a paid
-- departed instant j.  Both need only that the horizon (standing, or the
-- pushed suc j) does not exceed nextId.
enterInstant-fresh-aux : ∀ (lv : List Source) (hz i : Id) (cur : Maybe (Id × Owed))
  (dn : Bool) → CurrentPast cur i →
  paidUp (record { live = lv ; horizon = hz ; current = cur ; done = dn }) ≡ true →
  hz ≤ i →
  Σ Id λ hz′ →
    enterInstant (record { live = lv ; horizon = hz ; current = cur ; done = dn }) i
      ≡ just ([] , hz′)
enterInstant-fresh-aux lv hz i nothing dn cp pu hle =
  hz , enterInstant-idle-aux lv hz i nothing dn refl (≤→≤ᵇ hle)
enterInstant-fresh-aux lv hz i (just (j , ow)) dn cp pu hle =
  suc j , enterInstant-held-aux lv hz i j (just (j , ow)) ow dn refl
    (sucle→≢ᵇ cp) (paidUp-held-aux lv hz (just (j , ow)) dn j ow refl pu) (≤→≤ᵇ cp)

enterInstant-fresh : ∀ (S : ProtocolSt) (i : Id) →
  CurrentPast (ProtocolSt.current S) i → paidUp S ≡ true → ProtocolSt.horizon S ≤ i →
  Σ Id λ hz′ → enterInstant S i ≡ just ([] , hz′)
enterInstant-fresh S i cp pu hle =
  enterInstant-fresh-aux (ProtocolSt.live S) (ProtocolSt.horizon S) i
    (ProtocolSt.current S) (ProtocolSt.done S) cp pu hle

-- an uncancelled snapshot head is one more obligation than its tail
cr-fresh : ∀ {X : Set} (rid : RegId) (x : X) (ps : List (RegId × X)) (c : List RegId) →
  any (_≡ᵇ rid) c ≡ false → countRemaining ((rid , x) ∷ ps) c ≡ suc (countRemaining ps c)
cr-fresh rid x ps c h rewrite h = refl

-- the seed's protocol-entry field: from Mid's ledger, the automaton admits
-- instant nextId — continuing an open unpaid instant (inj₂) or opening
-- fresh over an idle/held paid slot (inj₁)
mid-enters : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {a : Arrival Γ}
  {nextId : Id} {rid : RegId} {p : Path Γ (arrTy a) t}
  {ps : List (RegId × Path Γ (arrTy a) t)} {sched : Sched Γ} {st : EvalSt e}
  {S : ProtocolSt} →
  Mid a nextId ((rid , p) ∷ ps) sched st S →
  any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ false →
  Σ Owed λ ob → Σ Id λ hz → enterInstant S nextId ≡ just (ob , hz)
mid-enters {a = a} {nextId} {rid} {p} {ps} {sched} {st} {S} mid ceq with Mid.ledger mid
... | inj₂ (ow , cur , lk , zx) =
      ow , ProtocolSt.horizon S , enterInstant-cont S nextId ow cur pf
  where
  lk-suc : lookupOwed (arrSource a) ow ≡ suc (countRemaining ps (EvalSt.cancelled st))
  lk-suc = trans lk (cr-fresh rid p ps (EvalSt.cancelled st) ceq)
  pf : paidOff ow ≡ false
  pf = lookup-pos-not-paidOff (arrSource a) ow
         (countRemaining ps (EvalSt.cancelled st)) lk-suc
mid-enters {a = a} {nextId} {rid} {p} {ps} {sched} {st} {S} mid ceq
    | inj₁ (cp , paid) = [] , enterInstant-fresh S nextId cp paid (Mid.horizon-low mid)

------------------------------------------------------------------
-- The pay/applyEvents seed fields turn on decrementing a key: paying a
-- positive owed key drops it by one; removing a present live source
-- drops its count by one.  Small hit/miss reductions feed the two.
------------------------------------------------------------------

suc-inj : ∀ {m k : ℕ} → suc m ≡ suc k → m ≡ k
suc-inj refl = refl

lookupOwed-hit : ∀ (s x : Source) (n : ℕ) (o : Owed) →
  (s ≡ᵇ x) ≡ true → lookupOwed s ((x , n) ∷ o) ≡ n
lookupOwed-hit s x n o sx with s ≡ᵇ x | sx
... | true | refl = refl

lookupOwed-miss : ∀ (s x : Source) (n : ℕ) (o : Owed) →
  (s ≡ᵇ x) ≡ false → lookupOwed s ((x , n) ∷ o) ≡ lookupOwed s o
lookupOwed-miss s x n o sx with s ≡ᵇ x | sx
... | false | refl = refl

countIn-miss : ∀ (s x : Source) (xs : List Source) →
  (s ≡ᵇ x) ≡ false → countIn s (x ∷ xs) ≡ countIn s xs
countIn-miss s x xs sx with s ≡ᵇ x | sx
... | false | refl = refl

-- removeOne drops exactly one occurrence of x: the x-count falls by one,
-- every other source's count is untouched (the two reads applyEvents-count
-- needs at a `close x` — hit for s ≡ x, miss for s ≢ x)
countIn-removeOne-hit : ∀ (x : Source) (lv lv′ : List Source) →
  removeOne x lv ≡ just lv′ → countIn x lv ≡ suc (countIn x lv′)
countIn-removeOne-hit x []       lv′ ()
countIn-removeOne-hit x (y ∷ ys) lv′ eq with x ≡ᵇ y in xy
... | true  = cong suc (cong (countIn x) (just-injᵂ eq))
... | false with removeOne x ys in ry | eq
...   | just ys′ | refl rewrite xy = countIn-removeOne-hit x ys ys′ ry
...   | nothing  | ()

countIn-removeOne-miss : ∀ (x s : Source) (lv lv′ : List Source) →
  (s ≡ᵇ x) ≡ false → removeOne x lv ≡ just lv′ → countIn s lv ≡ countIn s lv′
countIn-removeOne-miss x s []       lv′ sx ()
countIn-removeOne-miss x s (y ∷ ys) lv′ sx eq with x ≡ᵇ y in xy
... | true  = trans (countIn-miss s y ys s≢y)
                    (cong (countIn s) (just-injᵂ eq))
  where s≢y : (s ≡ᵇ y) ≡ false
        s≢y = trans (sym (cong (λ z → s ≡ᵇ z) (≡ᵇ→≡ x y xy))) sx
... | false with removeOne x ys in ry | eq
...   | nothing  | ()
...   | just ys′ | refl with s ≡ᵇ y
...     | true  = cong suc (countIn-removeOne-miss x s ys ys′ sx ry)
...     | false = countIn-removeOne-miss x s ys ys′ sx ry

-- paying the key with positive owed decrements it by one (once the `with`
-- fixes s ≡ᵇ x, payOwed/removeOne on the head reduce, so the equations are
-- refl / rewrite; the constructed tail term still needs the hit/miss read)
payOwed-key : ∀ (s : Source) (ow : Owed) (k : ℕ) →
  lookupOwed s ow ≡ suc k →
  Σ Owed λ ow′ → (payOwed s ow ≡ just ow′) × (lookupOwed s ow′ ≡ k)
payOwed-key s [] k ()
payOwed-key s ((x , n) ∷ o) k eq with s ≡ᵇ x in sx
... | true with n | eq
...   | suc m | refl = (x , m) ∷ o , refl , lookupOwed-hit s x m o sx
payOwed-key s ((x , n) ∷ o) k eq | false
  with payOwed-key s o k eq
... | o′ , po , lk rewrite po =
      (x , n) ∷ o′ , refl , trans (lookupOwed-miss s x n o′ sx) lk

-- removing a present live source decrements its count by one
countIn-removeOne : ∀ (s : Source) (lv : List Source) (k : ℕ) →
  countIn s lv ≡ suc k →
  Σ (List Source) λ lv′ → (removeOne s lv ≡ just lv′) × (countIn s lv′ ≡ k)
countIn-removeOne s [] k ()
countIn-removeOne s (x ∷ xs) k eq with s ≡ᵇ x in sx
... | true  = xs , refl , suc-inj eq
countIn-removeOne s (x ∷ xs) k eq | false
  with countIn-removeOne s xs k eq
... | xs′ , ro , ci rewrite ro = x ∷ xs′ , refl , trans (countIn-miss s x xs′ sx) ci

------------------------------------------------------------------
-- pay/applyEvents plumbing for the seed: a delivery whose source is
-- already owed pays it directly (settle-hit); a positive key is owed
-- (lookup-pos-hasOwed); the isLast close retires one live entry.
------------------------------------------------------------------

lookup-pos-hasOwed : ∀ (s : Source) (ow : Owed) (k : ℕ) →
  lookupOwed s ow ≡ suc k → hasOwed s ow ≡ true
lookup-pos-hasOwed s [] k ()
lookup-pos-hasOwed s ((x , n) ∷ o) k eq with s ≡ᵇ x in sx
... | true  = refl
... | false = lookup-pos-hasOwed s o k eq

settle-hit : ∀ (s : Source) (live : List Source) (owed : Owed) →
  hasOwed s owed ≡ true → settle delivery s live owed ≡ payOwed s owed
settle-hit s live owed h = if-true (hasOwed s owed) h

settle-miss : ∀ (s : Source) (live : List Source) (owed : Owed) →
  hasOwed s owed ≡ false →
  settle delivery s live owed ≡ payOwed s (bumpOwed s (countIn s live) owed)
settle-miss s live owed h = if-false (hasOwed s owed) h

-- an exhausted close of a present source retires its one live entry,
-- leaving owed and done untouched
applyEvents-close-exh : ∀ {A : Set} (x : Source) (live live′ : List Source)
  (owed : Owed) (done : Bool) → removeOne x live ≡ just live′ →
  applyEvents {A} (close x exhausted ∷ []) live owed done ≡ just (live′ , owed , done)
applyEvents-close-exh x live live′ owed done ro rewrite ro = refl

-- the seed's applyEvents field: fold the arrival's initial closes.  Not
-- spent (non-isLast) → no close, live untouched.  Spent (isLast) → the
-- exhausted close retires this source's one live entry (present because
-- live-source counts it: countIn = the uncancelled snapshot remainder,
-- ≥ 1 for a non-cancelled head).
seed-applies : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {a : Arrival Γ}
  {nextId : Id} {rid : RegId} {p : Path Γ (arrTy a) t}
  {ps : List (RegId × Path Γ (arrTy a) t)} {sched : Sched Γ} {st : EvalSt e}
  {S : ProtocolSt} (ob′ : Owed) →
  Mid a nextId ((rid , p) ∷ ps) sched st S →
  any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ false →
  Σ (List Source) λ Lv → Σ Owed λ Ov →
    applyEvents {Val Γ t}
      (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else [])
      (ProtocolSt.live S) ob′ (ProtocolSt.done S) ≡ just (Lv , Ov , ProtocolSt.done S)
seed-applies {a = a} {rid = rid} {p = p} {ps = ps} {st = st} {S = S} ob′ mid ceq
  with Arrival.isLast a | Mid.live-source mid
... | false | lsm = ProtocolSt.live S , ob′ , refl
... | true  | lsm =
      live′ , ob′ , applyEvents-close-exh (arrSource a) (ProtocolSt.live S) live′ ob′
                     (ProtocolSt.done S) ro
  where
  ci-eq : countIn (arrSource a) (ProtocolSt.live S)
            ≡ suc (countRemaining ps (EvalSt.cancelled st))
  ci-eq = trans lsm (cr-fresh rid p ps (EvalSt.cancelled st) ceq)
  rm = countIn-removeOne (arrSource a) (ProtocolSt.live S)
         (countRemaining ps (EvalSt.cancelled st)) ci-eq
  live′ = proj₁ rm
  ro    = proj₁ (proj₂ rm)

-- seeding a fresh instant: a first delivery from s with live count suc k
-- opens owed[s] = suc k and pays one, leaving k
payOwed-seed : ∀ (s : Source) (k : ℕ) →
  payOwed s (bumpOwed s (suc k) []) ≡ just ((s , k) ∷ [])
payOwed-seed s k rewrite ≡ᵇ-refl s = refl

postulate
  -- a non-cancelled head is a live registration of its source, so the
  -- source has ≥ 1 live entry.  For isLast this is live-source + cr-fresh;
  -- the non-isLast fresh case routes through countRegs (the snapshot↔
  -- registry link) — a TRUE positivity seeded here pending that lemma.
  seed-live-pos : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {a : Arrival Γ}
    {nextId : Id} {rid : RegId} {p : Path Γ (arrTy a) t}
    {ps : List (RegId × Path Γ (arrTy a) t)} {sched : Sched Γ} {st : EvalSt e}
    {S : ProtocolSt} →
    Mid a nextId ((rid , p) ∷ ps) sched st S →
    any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ false →
    Σ ℕ λ k → countIn (arrSource a) (ProtocolSt.live S) ≡ suc k

-- the enter/pay seed fields: the automaton admits instant nextId and the
-- delivery pays arrSource — continuing the open owed (inj₂), or opening
-- fresh and seeding owed[arrSource] from the live count (inj₁)
seed-enter-pay : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {a : Arrival Γ}
  {nextId : Id} {rid : RegId} {p : Path Γ (arrTy a) t}
  {ps : List (RegId × Path Γ (arrTy a) t)} {sched : Sched Γ} {st : EvalSt e}
  {S : ProtocolSt} →
  Mid a nextId ((rid , p) ∷ ps) sched st S →
  any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ false →
  Σ Owed λ ob → Σ Id λ hz → Σ Owed λ ob′ →
    (enterInstant S nextId ≡ just (ob , hz))
  × (settle delivery (arrSource a) (ProtocolSt.live S) ob ≡ just ob′)
seed-enter-pay {a = a} {nextId} {rid} {p} {ps} {sched} {st} {S} mid ceq
  with Mid.ledger mid
... | inj₂ (ow , cur , lk , zx) =
      ow , ProtocolSt.horizon S , proj₁ pk
      , enterInstant-cont S nextId ow cur
          (lookup-pos-not-paidOff (arrSource a) ow _ lk-suc)
      , trans (settle-hit (arrSource a) (ProtocolSt.live S) ow
                (lookup-pos-hasOwed (arrSource a) ow _ lk-suc))
              (proj₁ (proj₂ pk))
  where
  lk-suc : lookupOwed (arrSource a) ow ≡ suc (countRemaining ps (EvalSt.cancelled st))
  lk-suc = trans lk (cr-fresh rid p ps (EvalSt.cancelled st) ceq)
  pk = payOwed-key (arrSource a) ow (countRemaining ps (EvalSt.cancelled st)) lk-suc
seed-enter-pay {a = a} {nextId} {rid} {p} {ps} {sched} {st} {S} mid ceq
    | inj₁ (cp , paid) =
      [] , proj₁ ef , (arrSource a , k) ∷ []
      , proj₂ ef
      , trans (settle-miss (arrSource a) (ProtocolSt.live S) [] refl)
              (subst (λ c → payOwed (arrSource a) (bumpOwed (arrSource a) c [])
                              ≡ just ((arrSource a , k) ∷ []))
                     (sym ci-eq) (payOwed-seed (arrSource a) k))
  where
  ef = enterInstant-fresh S nextId cp paid (Mid.horizon-low mid)
  pos = seed-live-pos mid ceq
  k = proj₁ pos
  ci-eq : countIn (arrSource a) (ProtocolSt.live S) ≡ suc k
  ci-eq = proj₂ pos

-- THE seed: Mid (head ∷ ps) ⇒ FoldInv at the chainStep seed
mid-seed : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {a : Arrival Γ}
  {nextId : Id} {rid : RegId} {p : Path Γ (arrTy a) t}
  {ps : List (RegId × Path Γ (arrTy a) t)} {sched : Sched Γ} {st : EvalSt e}
  {S : ProtocolSt} →
  Mid a nextId ((rid , p) ∷ ps) sched st S →
  any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ false →
  FoldInv nextId (arrSource a) (arrVal a ∷ [])
    (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else [])
    (Arrival.isLast a) sched (record st { delivered = rid ∷ EvalSt.delivered st }) S
mid-seed {a = a} {nextId} {rid} {p} {ps} {sched} {st} {S} mid ceq = record
  { ob = ob ; hz = hz ; ob′ = ob′ ; Lv = proj₁ ap ; Ov = proj₁ (proj₂ ap)
  ; enters = enters ; pays = pays ; applies = proj₂ (proj₂ ap)
  ; shadow = shadow
  ; done-plumbed = Mid.done-plumbed mid
  }
  where
  ep = seed-enter-pay mid ceq
  ob  = proj₁ ep
  hz  = proj₁ (proj₂ ep)
  ob′ = proj₁ (proj₂ (proj₂ ep))
  enters = proj₁ (proj₂ (proj₂ (proj₂ ep)))
  pays   = proj₂ (proj₂ (proj₂ (proj₂ ep)))
  ap = seed-applies ob′ mid ceq
  -- for s ≠ arrSource the seed evs carry no init and (isLast) only an
  -- arrSource close, so initCount/closeCount vanish: SHADOW ⇔ live-others
  shadow : ∀ (s : Source) → sameSource s (arrSource a) ≡ false →
      countIn s (ProtocolSt.live S)
        + initCount s (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else [])
    ≡ countRegs s (EvalSt.registry st)
        + closeCount s (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else [])
  shadow s neq with Arrival.isLast a
  ... | false          = cong₂ _+_ (Mid.live-others mid s neq) refl
  ... | true rewrite neq = cong₂ _+_ (Mid.live-others mid s neq) refl

-- DECOMPOSITION BLUEPRINT (mid-step, the delivery-side sibling of
-- subscribeE-wf — "the per-clause preservation grind").  One surviving
-- chain's emits — its own delivery, any share fan-outs it triggers, any
-- cut closes — are accepted, paying/bumping/cancelling exactly per the
-- ledger.  The tower to grind, mirroring the evaluator's own recursion:
--
--   mid-step  ⇐  foldPath-wf  (induction on the Path)
--                ├─ root         : the chain's ONE delivery emit — the
--                │                  only place a linear path touches the
--                │                  protocol; frames merely accumulate
--                │                  evs/vals (they never step it)
--                ├─ f ↠ path′    : stepFrame-wf transforms the fold state
--                │                  (vals,evs,fin,sched,st) WITHOUT
--                │                  stepping the protocol, then the IH
--                │                  continues down path′ — the direct
--                │                  analog of subscribeE-wf's per-clause
--                │                  induction (map/scan/take/*All)
--                └─ share-sink i : one handoff emit, then dispatchShare-wf
--                                   (MUTUALLY RECURSIVE with foldPath-wf,
--                                   gas-structural) fans out to share i's
--                                   registrations — the handoff's owed
--                                   bump is repaid one-per-fan-out, so the
--                                   share subtree nets owed back to zero
--                                   (the diamond, batched by construction)
--
-- The missing piece is FoldInv — the mid-fold relation foldPath-wf is
-- stated over (BurstInv's delivery-side analog): unlike BurstInv's
-- literally-empty owed table, FoldInv carries the PARTIALLY-PAID open
-- instant (owed[envSrc] = the chain's own unpaid delivery; each pending
-- share bumped-then-being-repaid across its dispatch).  Once FoldInv is
-- pinned, mid-step is the chainStep seed (owed[arrSource] = the snapshot
-- remainder) plus reading Mid back off the FoldInv result.  Kept as ONE
-- postulate until FoldInv lands, so no half-stated (possibly-false) leaf
-- enters the development early — the whole point of the outside-in rule.
--
-- WHERE TO SPLIT (verified empirically, 2026-07): the Path-constructor
-- case split MUST live at foldPath-wf, which — like foldPath itself —
-- quantifies the chain's SOURCE type `u` FREELY (path : Path Γ u t).
-- It CANNOT live at mid-step, where the source type is pinned to the
-- stuck projection `arrTy a`: matching `share-sink i : Path Γ (lookup Γ i) t`
-- there demands `lookup Γ i ≡ arrTy a`, which Agda's unifier rejects
-- (two neutrals), so `mid-step {p = share-sink i} = …` will not even
-- typecheck (root and `f ↠ path′` do — only share-sink clashes).  With a
-- free `u`, matching share-sink cleanly sets `u := lookup Γ i`.  So:
-- mid-step invokes foldPath-wf at `u := arrTy a` with the seed; the
-- three-way induction (root / frame / share) is foldPath-wf's own.
--
-- STATE OF THE DECOMPOSITION (2026-07):
--   PRE   mid-seed : Mid (head∷ps) ⇒ FoldInv              — PROVEN
--   MID   foldPath-wf : FoldInv ⇒ Σ S′, runProtocol ≡ S′  — PROVEN
--           (modulo the two structural leaves stepFrame-wf / dispatchShare-wf,
--            postulated exactly as subscribeE-wf is on the burst side)
--   POST  readoff : … ⇒ Mid ps                            — the remaining gap
--
-- THE READOFF, precisely.  mid-step must return `Mid a nextId ps st″ sched″ S′`
-- where (·,sched″,st″) = chainStep …, and S′ is foldPath-wf's accepted state.
-- Its eight fields all reference st″/sched″/S′, so the readoff needs a
-- CHARACTERISATION of the fold's output triple, not merely `∃ S′`.  For the
-- ROOT case that characterisation is already in hand — foldPath-root-wf pins
-- S′ = record{live=Lv; horizon=hz; current=just(nextId,Ov); done= if fin then
-- true else done S}, and foldPath root leaves the EvalSt untouched, so
-- st″ = record st{delivered=…} (registry st″ ≡ registry st, sched″ ≡ sched).
-- That is the proven anchor to read the root chain's Mid ps off.
--
-- The obstruction is that the SAME `arrTy a` pinning that forces the case
-- split into foldPath-wf also forbids a standalone post-hoc readoff on `p`:
-- Mid ps must be reconstructed by the SAME path induction, so foldPath-wf's
-- CONCLUSION has to carry the readoff data — a `FoldOut` companion to FoldInv,
-- quantified over the free `u`, threaded through root (proven, above),
-- f ↠ path′ (stepFrame-wf, enriched), and share-sink (dispatchShare-wf,
-- enriched).  FoldOut is a genuinely NEW invariant: what a PARTIAL chain fold
-- preserves of the live↔registry shadow.  It is deliberately NOT yet stated —
-- an imprecise FoldOut would be a FALSE postulate (forbidden), and unlike the
-- done-plumbed window below it is not yet pinned down, so it is left as the
-- single mid-step postulate until its shape is settled with care.
--
-- done-plumbed in the readoff (RESOLVED 2026-07): a completing isLast root
-- chain flips done S′≡true while its own non-share-sunk registration is still
-- in registry st″ (dropped only at cascadeFinish).  Handled by the conditional
-- restatement of Mid/FoldInv.done-plumbed (drop arrSource iff isLast) — see
-- those fields.  The readoff's isLast-root obligation, allShareSunk(dropSource
-- arrSource registry st″), then holds BECAUSE at the flip every non-share-sunk
-- survivor belongs to arrSource (fin reaches root only once nothing else can
-- deliver).  GUARD: should a reachable flip ever leave a NON-arrival source
-- holding a root-sinking registration, that falsifies Inv.done-plumbed itself
-- (a completion emitted while something could still deliver — an evaluator
-- bug); STOP and surface the trace, do not patch around it.
postulate
  mid-step : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    {a : Arrival Γ} {nextId : Id} {rid : RegId}
    {p : Path Γ (arrTy a) t} {ps : List (RegId × Path Γ (arrTy a) t)}
    {sched : Sched Γ} {st : EvalSt e} {S : ProtocolSt} →
    Mid a nextId ((rid , p) ∷ ps) sched st S →
    any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ false →
    Σ ProtocolSt λ S′ →
      let r = chainStep nextId a p sched
                (record st { delivered = rid ∷ EvalSt.delivered st })
      in (runProtocol S (proj₁ r) ≡ just S′)
         × Mid a nextId ps (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) S′

-- a cancelled head contributes nothing to countRemaining (the `if`
-- takes the then-branch)
cr-skip : ∀ {X : Set} (rid : RegId) (x : X)
          (ps : List (RegId × X)) (c : List RegId) →
          any (_≡ᵇ rid) c ≡ true →
          countRemaining ((rid , x) ∷ ps) c ≡ countRemaining ps c
cr-skip rid x ps c h rewrite h = refl

-- and nothing to cascadeGo: its first clause skips a cancelled head
-- outright, folding the tail with the SAME state (two-column trick —
-- cascadeGo's `with` won't unfold under rewrite)
cascadeGo-skip : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (nextId : Id) (rid : RegId)
  (p : Path Γ (arrTy a) t) (ps : List (RegId × Path Γ (arrTy a) t))
  (sched : Sched Γ) (st : EvalSt e) →
  any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ true →
  cascadeGo {e = e} a nextId ((rid , p) ∷ ps) sched st
    ≡ cascadeGo {e = e} a nextId ps sched st
cascadeGo-skip a nextId rid p ps sched st ceq
  with any (_≡ᵇ rid) (EvalSt.cancelled st) | ceq
... | true | refl = refl

-- a cancelled chain folds to nothing (its close already rode the
-- cutting emit; its owed was forgiven right there): every Mid field is
-- stable when the snapshot head drops, given the head is cancelled
mid-skip : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  {a : Arrival Γ} {nextId : Id} {rid : RegId}
  {p : Path Γ (arrTy a) t} {ps : List (RegId × Path Γ (arrTy a) t)}
  {sched : Sched Γ} {st : EvalSt e} {S : ProtocolSt} →
  Mid a nextId ((rid , p) ∷ ps) sched st S →
  any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ true →
  Mid a nextId ps sched st S
mid-skip {a = a} {nextId} {rid} {p} {ps} {sched} {st} {S} mid ceq = record
  { live-others  = Mid.live-others mid
  ; live-source  = trans (Mid.live-source mid)
      (cong (λ z → if Arrival.isLast a then z
                   else countRegs (arrSource a) (EvalSt.registry st))
            (cr-skip rid p ps (EvalSt.cancelled st) ceq))
  ; reg-typed    = Mid.reg-typed mid       -- same sched, st
  ; horizon-low  = Mid.horizon-low mid
  ; ledger       = ledger′
  ; done-plumbed = Mid.done-plumbed mid
  ; fold-live    = subst (λ z → hasDry (proj₁ z) ≡ false)
      (cascadeGo-skip a nextId rid p ps sched st ceq)
      (Mid.fold-live mid)
  ; owed-unique  = Mid.owed-unique mid      -- same S, nextId
  }
  where
  ledger′ :
      (CurrentPast (ProtocolSt.current S) nextId × (paidUp S ≡ true))
    ⊎ (Σ Owed λ ow →
         (ProtocolSt.current S ≡ just (nextId , ow))
       × (lookupOwed (arrSource a) ow
            ≡ countRemaining ps (EvalSt.cancelled st))
       × (zeroExcept (arrSource a) ow ≡ true))
  ledger′ with Mid.ledger mid
  ... | inj₁ x                    = inj₁ x
  ... | inj₂ (ow , cur , lk , zx) =
        inj₂ (ow , cur
             , trans lk (cr-skip rid p ps (EvalSt.cancelled st) ceq)
             , zx)

------------------------------------------------------------------
-- mid-final: leaving the cascade.  Bool/ℕ glue first, then registry
-- lemmas for the finish sweep, then the assembly.
------------------------------------------------------------------

-- a key absent from the table reads zero
lookupOwed-absent : ∀ (s : Source) (o : Owed) →
  notKeyOwed s o ≡ true → lookupOwed s o ≡ 0
lookupOwed-absent s []            _ = refl
lookupOwed-absent s ((x , n) ∷ o) h with s ≡ᵇ x | h
... | false | h′ = lookupOwed-absent s o h′
... | true  | h′ = true≢false (sym h′)

-- with unique keys, zeroExcept + a zero at s forces the whole table
-- zero.  `with s ≡ᵇ x in seq` rewrites ze/lk in each branch: at the key
-- (true) lk reads n ≡ 0 and ze drops to the tail; off-key (false) ze's
-- head gives n ≡ᵇ 0 and lk passes to the tail
allZero-clean : ∀ (s : Source) (o : Owed) →
  UniqueOwed o ≡ true → zeroExcept s o ≡ true → lookupOwed s o ≡ 0 →
  allZero o ≡ true
allZero-clean s []            _  _  _  = refl
allZero-clean s ((x , n) ∷ o) uq ze lk with s ≡ᵇ x in seq
... | true  =
      subst (λ m → allZero ((x , m) ∷ o) ≡ true) (sym lk)
        (allZero-clean s o (∧-trueʳ uq) ze
          (lookupOwed-absent s o
            (subst (λ z → notKeyOwed z o ≡ true)
                   (sym (≡ᵇ→≡ s x seq)) (∧-trueˡ uq))))
... | false =
      subst (λ m → allZero ((x , m) ∷ o) ≡ true)
            (sym (≡ᵇ→≡ n 0 (∧-trueˡ ze)))
        (allZero-clean s o (∧-trueʳ uq) (∧-trueʳ ze) lk)

-- an all-zero owed table settles: paidUp holds
paid-allzero : (S : ProtocolSt) {j : Id} {ow : Owed} →
  ProtocolSt.current S ≡ just (j , ow) → allZero ow ≡ true → paidUp S ≡ true
paid-allzero S ceq az with ProtocolSt.current S | ceq
... | just (j , ow) | refl rewrite az = refl

-- CurrentPast only weakens as the bound grows
currentPast-up : (c : Maybe (Id × Owed)) (N : Id) →
  CurrentPast c N → CurrentPast c (suc N)
currentPast-up nothing        N cp = tt
currentPast-up (just (j , _)) N cp = ≤-up cp

-- registry sweep: dropping s zeroes s's own count and leaves others'
dropSource-self : ∀ {n} {Γ : Ctx n} {t}
  (s : Source) (reg : List (RegId × Source × Chain Γ t)) →
  countRegs s (dropSource s reg) ≡ 0
dropSource-self s []                  = refl
dropSource-self s ((rid , x , c) ∷ r) with s ≡ᵇ x in eq
... | true             = dropSource-self s r
... | false rewrite eq = dropSource-self s r

dropSource-other : ∀ {n} {Γ : Ctx n} {t}
  (s s′ : Source) (reg : List (RegId × Source × Chain Γ t)) →
  (s ≡ᵇ s′) ≡ false →
  countRegs s (dropSource s′ reg) ≡ countRegs s reg
dropSource-other s s′ []                  neq = refl
dropSource-other s s′ ((rid , x , c) ∷ r) neq with s ≡ᵇ x in sx | s′ ≡ᵇ x in s′x
... | true  | true  =
      let s≡s′ = trans (≡ᵇ→≡ s x sx) (sym (≡ᵇ→≡ s′ x s′x))
          p    = trans (sym (cong (s ≡ᵇ_) s≡s′)) (≡ᵇ-refl s)
      in true≢false (trans (sym p) neq)
... | true  | false rewrite sx = cong suc (dropSource-other s s′ r neq)
... | false | true             = dropSource-other s s′ r neq
... | false | false rewrite sx = dropSource-other s s′ r neq

-- dropping preserves "every registration is share-sunk"
allShareSunk-drop : ∀ {n} {Γ : Ctx n} {t}
  (s : Source) (reg : List (RegId × Source × Chain Γ t)) →
  allShareSunk reg ≡ true → allShareSunk (dropSource s reg) ≡ true
allShareSunk-drop s []                        h = refl
allShareSunk-drop s ((rid , x , (u , p)) ∷ r) h with s ≡ᵇ x
... | true  = allShareSunk-drop s r (∧-trueʳ h)
... | false = ∧-intro (∧-trueˡ h) (allShareSunk-drop s r (∧-trueʳ h))

-- the conditional form of done-plumbed, established from the full-registry
-- form: identity when the guard is false, allShareSunk-drop when true
allShareSunk-if : ∀ {n} {Γ : Ctx n} {t}
  (b : Bool) (s : Source) (reg : List (RegId × Source × Chain Γ t)) →
  allShareSunk reg ≡ true →
  allShareSunk (if b then dropSource s reg else reg) ≡ true
allShareSunk-if false s reg h = h
allShareSunk-if true  s reg h = allShareSunk-drop s reg h

-- cascadeFinish reduced under each isLast branch (two-column trick: the
-- `with Arrival.isLast a` won't unfold under rewrite).  isLast=false
-- leaves the state; isLast=true sweeps the spent source's registry
cascadeFinish-false : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
  Arrival.isLast a ≡ false → cascadeFinish a sched st ≡ (sched , st)
cascadeFinish-false a sched st eq with Arrival.isLast a | eq
... | false | refl = refl

finishReg-true : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
  Arrival.isLast a ≡ true →
  EvalSt.registry (proj₂ (cascadeFinish a sched st))
    ≡ dropSource (arrSource a) (EvalSt.registry st)
finishReg-true a sched st eq with Arrival.isLast a | eq
... | true | refl = refl

finishSched-true : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
  Arrival.isLast a ≡ true →
  Sched.live (proj₁ (cascadeFinish a sched st))
    ≡ sweepLive (dropSource (arrSource a) (EvalSt.registry st)) (Sched.live sched)
finishSched-true a sched st eq with Arrival.isLast a | eq
... | true | refl = refl

-- leaving: all chains folded ⇒ fully paid; finish (drop the spent
-- source, sweep) lands Inv-related at suc nextId
mid-final : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  {a : Arrival Γ} {nextId : Id}
  {sched : Sched Γ} {st : EvalSt e} {S : ProtocolSt} →
  Mid a nextId [] sched st S →
  Inv (suc nextId) (proj₁ (cascadeFinish a sched st))
                   (proj₂ (cascadeFinish a sched st)) S
  × (paidUp S ≡ true)
mid-final {a = a} {nextId} {sched} {st} {S} mid = inv , paidUp-S
  where
  paidUp-S : paidUp S ≡ true
  paidUp-S with Mid.ledger mid
  ... | inj₁ (_ , pd)             = pd
  ... | inj₂ (ow , cur , lk , zx) =
        paid-allzero S cur
          (allZero-clean (arrSource a) ow (Mid.owed-unique mid ow cur) zx lk)

  cpast : CurrentPast (ProtocolSt.current S) (suc nextId)
  cpast with Mid.ledger mid
  ... | inj₁ (cp , _)        = currentPast-up (ProtocolSt.current S) nextId cp
  ... | inj₂ (ow , cur , _ , _) =
        subst (λ c → CurrentPast c (suc nextId)) (sym cur) ≤-refl

  -- the arrival source's live count, read off Mid.live-source per isLast
  live-src-nl : Arrival.isLast a ≡ false →
    countIn (arrSource a) (ProtocolSt.live S)
      ≡ countRegs (arrSource a) (EvalSt.registry st)
  live-src-nl isL = trans (Mid.live-source mid) (if-false (Arrival.isLast a) isL)

  live-src-tl : Arrival.isLast a ≡ true →
    countIn (arrSource a) (ProtocolSt.live S) ≡ 0
  live-src-tl isL = trans (Mid.live-source mid) (if-true (Arrival.isLast a) isL)

  lm-false : Arrival.isLast a ≡ false → ∀ (s : Source) →
    countIn s (ProtocolSt.live S) ≡ countRegs s (EvalSt.registry st)
  lm-false isL s with sameSource s (arrSource a) in seq
  ... | false = Mid.live-others mid s seq
  ... | true  =
        subst (λ z → countIn z (ProtocolSt.live S)
                       ≡ countRegs z (EvalSt.registry st))
              (sym (≡ᵇ→≡ s (arrSource a) seq)) (live-src-nl isL)

  lm-true : Arrival.isLast a ≡ true → ∀ (s : Source) →
    countIn s (ProtocolSt.live S)
      ≡ countRegs s (dropSource (arrSource a) (EvalSt.registry st))
  lm-true isL s with sameSource s (arrSource a) in seq
  ... | false = trans (Mid.live-others mid s seq)
                  (sym (dropSource-other s (arrSource a) (EvalSt.registry st) seq))
  ... | true  =
        let s≡ = ≡ᵇ→≡ s (arrSource a) seq in
        trans (subst (λ z → countIn z (ProtocolSt.live S) ≡ 0) (sym s≡)
                 (live-src-tl isL))
              (sym (subst (λ z → countRegs z (dropSource (arrSource a)
                                   (EvalSt.registry st)) ≡ 0) (sym s≡)
                     (dropSource-self (arrSource a) (EvalSt.registry st))))

  inv : Inv (suc nextId) (proj₁ (cascadeFinish a sched st))
                         (proj₂ (cascadeFinish a sched st)) S
  inv = go (Arrival.isLast a) refl
    where
    go : (b : Bool) → Arrival.isLast a ≡ b →
         Inv (suc nextId) (proj₁ (cascadeFinish a sched st))
                          (proj₂ (cascadeFinish a sched st)) S
    -- isLast=false: cascadeFinish is the identity; rewrite the goal flat
    go false isL rewrite cascadeFinish-false a sched st isL = record
      { live-matches = lm-false isL
      ; reg-typed    = Mid.reg-typed mid
      ; horizon-low  = ≤-up (Mid.horizon-low mid)
      ; current-past = cpast
      ; done-plumbed = λ deq →
          subst (λ b → allShareSunk (if b then dropSource (arrSource a) (EvalSt.registry st)
                          else EvalSt.registry st) ≡ true)
                isL (Mid.done-plumbed mid deq)
      }
    -- isLast=true: keep cascadeFinish symbolic; convert registry and live
    -- field-by-field, reg-typed via the dropSource/sweepLive preservation
    go true isL = record
      { live-matches = λ s →
          subst (λ reg → countIn s (ProtocolSt.live S) ≡ countRegs s reg)
                (sym (finishReg-true a sched st isL)) (lm-true isL s)
      ; reg-typed    =
          subst (λ reg → regTyped? reg (Sched.live (proj₁ (cascadeFinish a sched st))) ≡ true)
                (sym (finishReg-true a sched st isL))
                (subst (λ lv → regTyped? (dropSource (arrSource a) (EvalSt.registry st)) lv ≡ true)
                       (sym (finishSched-true a sched st isL))
                       (reg-typed-finish (arrSource a) (EvalSt.registry st)
                          (Sched.live sched) (Mid.reg-typed mid)))
      ; horizon-low  = ≤-up (Mid.horizon-low mid)
      ; current-past = cpast
      ; done-plumbed = λ deq →
          subst (λ reg → allShareSunk reg ≡ true)
                (sym (finishReg-true a sched st isL))
                (subst (λ b → allShareSunk (if b then dropSource (arrSource a) (EvalSt.registry st)
                                else EvalSt.registry st) ≡ true)
                       isL (Mid.done-plumbed mid deq))
      }

-- the chain fold, composed (mirrors cascadeGo's own recursion —
-- structural on the snapshot, no termination debt at this level)
cascadeGo-wf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (nextId : Id)
  (chains : List (RegId × Path Γ (arrTy a) t))
  (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
  Mid a nextId chains sched st S →
  Σ ProtocolSt λ S′ →
    let r = cascadeGo {e = e} a nextId chains sched st
    in (runProtocol S (proj₁ r) ≡ just S′)
       × Mid a nextId [] (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) S′
cascadeGo-wf a nextId [] sched st S mid = S , refl , mid
cascadeGo-wf a nextId ((rid , p) ∷ ps) sched st S mid
  with any (_≡ᵇ rid) (EvalSt.cancelled st) in ceq
... | true  = cascadeGo-wf a nextId ps sched st S (mid-skip mid ceq)
... | false
  with mid-step {ps = ps} mid ceq
... | S₁ , run₁ , mid₁
  with cascadeGo-wf a nextId ps
         (proj₁ (proj₂ (chainStep nextId a p sched
                         (record st { delivered = rid ∷ EvalSt.delivered st }))))
         (proj₂ (proj₂ (chainStep nextId a p sched
                         (record st { delivered = rid ∷ EvalSt.delivered st }))))
         S₁ mid₁
... | S₂ , run₂ , mid₂ =
  S₂
  , run-++-just S
      (proj₁ (chainStep nextId a p sched
               (record st { delivered = rid ∷ EvalSt.delivered st })))
      _ run₁ run₂
  , mid₂

-- the latch leaves the registry untouched (it only resets the per-cascade
-- ledger and stamps the watermark / dying set)
latch-registry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (st : EvalSt e) →
  EvalSt.registry (cascadeLatch a st) ≡ EvalSt.registry st
latch-registry a st with Arrival.isLast a
... | true  = refl
... | false = refl

-- an all-fresh snapshot (no cancellations yet) has every entry obliged
countRemaining-[] : ∀ {X : Set} (ps : List (RegId × X)) →
  countRemaining ps [] ≡ length ps
countRemaining-[] []             = refl
countRemaining-[] ((rid , _) ∷ ps) = cong suc (countRemaining-[] ps)

-- entering: the latch opens the ledger; the automaton, Inv-related and
-- paid, stands ready to open instant nextId (still on the previous,
-- settled instant, so the ledger is the paid branch).  reg-typed threads
-- from Inv across the scheduler pop; the count fact live-source needs is
-- read off chains-count-derived
mid-init : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (nextId : Id) (sched : Sched Γ) (a : Arrival Γ) (sched′ : Sched Γ)
  (st : EvalSt e) (S : ProtocolSt) →
  sched-next sched ≡ inj₂ (a , sched′) →
  Inv nextId sched st S → paidUp S ≡ true →
  hasDry (proj₁ (cascadeGo a nextId (chainsOf a st) sched′
                           (cascadeLatch a st))) ≡ false →
  Mid a nextId (chainsOf a st) sched′ (cascadeLatch a st) S
mid-init nextId sched a sched′ st S eq inv paid nodry = record
  { live-others  = λ s _ → trans (Inv.live-matches inv s)
                     (cong (countRegs s) (sym (latch-registry a st)))
  ; live-source  = live-src
  ; reg-typed    = subst (λ reg → regTyped? reg (Sched.live sched′) ≡ true)
                     (sym (latch-registry a st))
                     (regTyped?-pop-sched sched sched′ (EvalSt.registry st) eq
                       (Inv.reg-typed inv))
  ; horizon-low  = Inv.horizon-low inv
  ; ledger       = inj₁ (Inv.current-past inv , paid)
  ; done-plumbed = λ deq →
      subst (λ reg → allShareSunk (if Arrival.isLast a
                       then dropSource (arrSource a) reg else reg) ≡ true)
            (sym (latch-registry a st))
            (allShareSunk-if (Arrival.isLast a) (arrSource a)
              (EvalSt.registry st) (Inv.done-plumbed inv deq))
  ; fold-live    = nodry
  ; owed-unique  = λ ow cur → ⊥-elim (1+n≰n
                     (subst (λ c → CurrentPast c nextId) cur (Inv.current-past inv)))
  }
  where
  live-src : countIn (arrSource a) (ProtocolSt.live S)
    ≡ (if Arrival.isLast a
       then countRemaining (chainsOf a st) (EvalSt.cancelled (cascadeLatch a st))
       else countRegs (arrSource a) (EvalSt.registry (cascadeLatch a st)))
  live-src with Arrival.isLast a
  ... | true  = trans (Inv.live-matches inv (arrSource a))
                  (trans (chains-count-derived a sched sched′ st (Inv.reg-typed inv) eq)
                         (sym (countRemaining-[] (chainsOf a st))))
  ... | false = Inv.live-matches inv (arrSource a)

-- one arrival's cascade, composed.  The dry-freeness premise is
-- stated on the cascade's own emits — definitionally the cascadeGo
-- fold's emits, which is the shape mid-init wants
cascade-wf :
  ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (nextId : Id) (sched : Sched Γ) (a : Arrival Γ) (sched′ : Sched Γ)
    (st : EvalSt e) (S : ProtocolSt) →
  sched-next sched ≡ inj₂ (a , sched′) →
  Inv nextId sched st S → paidUp S ≡ true →
  hasDry (proj₁ (cascade a nextId sched′ st)) ≡ false →
  Σ ProtocolSt λ S′ →
    let r = cascade a nextId sched′ st
    in (runProtocol S (proj₁ r) ≡ just S′)
       × Inv (suc nextId) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) S′
       × (paidUp S′ ≡ true)
cascade-wf nextId sched a sched′ st S eq inv paid nodry
  with cascadeGo-wf a nextId (chainsOf a st) sched′ (cascadeLatch a st) S
         (mid-init nextId sched a sched′ st S eq inv paid nodry)
... | S′ , run , mid
  with mid-final mid
... | inv′ , paid′ = S′ , run , inv′ , paid′

------------------------------------------------------------------
-- the composition: fuel induction over drain, then the theorem
------------------------------------------------------------------

drain-wf :
  ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (fuel : Fuel) (nextId : Id) (sched : Sched Γ) (st : EvalSt e)
    (S : ProtocolSt) →
  Inv nextId sched st S → paidUp S ≡ true →
  hasDry (drain {e = e} fuel nextId sched st) ≡ false →
  Σ ProtocolSt λ S′ →
    (runProtocol S (drain {e = e} fuel nextId sched st) ≡ just S′)
    × (paidUp S′ ≡ true)
drain-wf zero    nextId sched st S inv paid _  = S , refl , paid
drain-wf (suc k) nextId sched st S inv paid hd with sched-next sched in eq
... | inj₁ _            = S , refl , paid
... | inj₂ (a , sched′)
  -- the with-abstraction has already rewritten hd's type to the
  -- unfolded `cascade emits ++ drain k …` shape — split it there
  with hasDry-++ (proj₁ (cascade a nextId sched′ st))
         (drain k (suc nextId)
           (proj₁ (proj₂ (cascade a nextId sched′ st)))
           (proj₂ (proj₂ (cascade a nextId sched′ st))))
         hd
... | nodry₁ , nodry₂
  with cascade-wf nextId sched a sched′ st S eq inv paid nodry₁
... | S₁ , run₁ , inv₁ , paid₁
  with drain-wf k (suc nextId)
         (proj₁ (proj₂ (cascade a nextId sched′ st)))
         (proj₂ (proj₂ (cascade a nextId sched′ st)))
         S₁ inv₁ paid₁ nodry₂
... | S₂ , run₂ , paid₂ =
  S₂
  , run-++-just S (proj₁ (cascade a nextId sched′ st)) _ run₁ run₂
  , paid₂

-- the reified termination debt: the seeded sync budget never runs
-- dry on a canonical run.  This is the old TERMINATING pragma's
-- claim, now a provable statement — the evaluator is total either
-- way, and QuickCheck's WellFormed check falsifies this postulate at
-- runtime the moment any program exhausts its budget
postulate
  budget-sufficient :
    ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ) →
    hasDry (evaluate fuel e ins) ≡ false

-- the primitives' half of the sandwich: remaining debt is the frame
-- relations, their step lemmas, and budget sufficiency above
evaluate-well-formed :
  ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ) →
  WellFormed (evaluate fuel e ins)
evaluate-well-formed fuel e ins
  with hasDry-++
         (proj₁ (subscribeE (budgetAt e ins 0) e root 0 0
                            (sched-init e ins) (st-init e)))
         (drain fuel 1
           (proj₁ (proj₂ (subscribeE (budgetAt e ins 0) e root 0 0
                                     (sched-init e ins) (st-init e))))
           (proj₂ (proj₂ (subscribeE (budgetAt e ins 0) e root 0 0
                                     (sched-init e ins) (st-init e)))))
         (budget-sufficient fuel e ins)
... | nodry₀ , nodry₁
  with subscribe-wf e ins nodry₀
... | S₀ , run₀ , inv₀ , paid₀
  with drain-wf fuel 1
         (proj₁ (proj₂ (subscribeE (budgetAt e ins 0) e root 0 0
                                   (sched-init e ins) (st-init e))))
         (proj₂ (proj₂ (subscribeE (budgetAt e ins 0) e root 0 0
                                   (sched-init e ins) (st-init e))))
         S₀ inv₀ paid₀ nodry₁
... | S₁ , run₁ , paid₁
  rewrite run-++-just protocol-init
            (proj₁ (subscribeE (budgetAt e ins 0) e root 0 0
                               (sched-init e ins) (st-init e)))
            (drain fuel 1
              (proj₁ (proj₂ (subscribeE (budgetAt e ins 0) e root 0 0
                                        (sched-init e ins) (st-init e))))
              (proj₂ (proj₂ (subscribeE (budgetAt e ins 0) e root 0 0
                                        (sched-init e ins) (st-init e)))))
            run₀ run₁
  = acceptPaid S₁ paid₁
