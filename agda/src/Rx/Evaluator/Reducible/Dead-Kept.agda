------------------------------------------------------------------
-- A NODE NO LIVE CHAIN RUNS THROUGH STAYS SO.  A run only grows the
-- three marks a fan-out skips a chain on, and every row it registers
-- rides the path it was walking, lowered, or that path under frames at
-- nodes the counter hands out.  So a node below the counter and off the
-- walked path gains no row, and every row it had stays skipped.  A
-- fan-out folds only the rows it does not skip, which the registry
-- already ties off the node, so it is the same induction over their
-- own paths.
------------------------------------------------------------------

module Rx.Evaluator.Reducible.Dead-Kept where

open import Data.Bool using (Bool; true; false; T; not; _∨_; _∧_)
open import Data.Bool.Properties using (∨-zeroʳ; ∨-conicalˡ; ∨-conicalʳ)
open import Data.Bool.ListAction using (any)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _<_; _≡ᵇ_)
open import Data.Nat.Properties using (<-≤-trans; m<n⇒m<1+n)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Vec using (lookup)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; trans; cong)

open import Rx.Exp using (Ctx; Closed; Ty; FnClo; boolᵗ; _≟ᵗ_; _×ᵗ_)
open import Rx.Prim using (Source)
open import Rx.Evaluator using (Sched; EvalSt; Path; NodeId; RegId; RegSrc; RegRow; regFloor; register;
  lookupNode; frameNodes; pathHasNode; atSlot; atDyn; shareAdmit; shareDying; shareFinish; switchKill;
  skipᵇ; regSource; memberSource; sameSource; markDlv; aliveThroughᶠ; takeDispatch; takeVals; cutThrough;
  scanDispatch; batchDispatch; thruWrap; AllOp; mergeAllᵒ; switchᵒ; exhaustᵒ; lowerFloor; installNode;
  cell-st; take-st; batchSync-st; mergeAll-st; switch-st; exhaust-st)
open import Rx.Evaluator.Freshness using (nodeCt; <→≢ᵇ)
open import Rx.Evaluator.Domain using (subscribeE⇓; subscribeInner⇓; thruConsume⇓; thruWalk⇓; mergeAllDrain⇓;
  innerFinish⇓; innerReact⇓; stepFrame⇓; subscribeAll⇓; subscribeSharedSlot⇓; foldPath⇓; dispatchShare⇓;
  shareWalk⇓; shareGo⇓;
  subs-floor; subs-shared; subs-hot-done; subs-hot-live; subs-cold-sync; subs-cold-async; subs-of; subs-empty;
  subs-takeWhile; subs-batchSync; subs-map; subs-scan;
  subs-flatten; subs-μ; subs-defer; subs-mint; inner; consume-all-sub; consume-all-enqueue; consume-all-nil;
  consume-switch-sub; consume-switch-nil; consume-exhaust-sub; consume-exhaust-nil; walk-nil; walk-echo; walk-cons;
  drain-spent; drain-nil; drain-no-room; drain-room; finish-all-drain; finish-switch-clear; finish-exhaust-clear;
  finish-nil; react-false; react-alive; react-dead; step-map; step-scan; step-take; step-batchSync;
  step-from-inner; step-thru-outer; sub-all; connect; slot-spent; slot-join; slot-connect; disp; walk-end;
  walk-more; go-nil; go-cut; go-live; fold-root; fold-sink; fold-step)
open import Rx.Evaluator.Reducible.Support using (rowThrough; lower-nodes; ∈-register; kill-sub; switchKill-ct;
  wrap-reg; takeReg; scanReg; batchReg)
open import Rx.Evaluator.Reducible.Floor using (drop-sub; subscribeE-ct; subscribeInner-ct; stepFrame-ct;
  thruConsume-ct; foldPath-ct; shareGo-ct)

contra : ∀ {b} → b ≡ true → b ≡ false → ⊥
contra refl ()

off-T : ∀ {b} → (T b → ⊥) → b ≡ false
off-T {false} _ = refl
off-T {true}  h = ⊥-elim (h tt)

not-false : ∀ {b} → not b ≡ false → b ≡ true
not-false {true} _ = refl

off-∨ : ∀ {a b} → a ≡ false → b ≡ false → a ∨ b ≡ false
off-∨ refl h = h

∧-off : ∀ {a b} → T a → a ∧ b ≡ false → b ≡ false
∧-off {true} _ h = h

-- a skip test that held still holds when no mark it reads shrank
grow∨∧ : ∀ {c c′ m m′ d d′ : Bool} → (c ≡ true → c′ ≡ true) → (m ≡ true → m′ ≡ true) → (d ≡ true → d′ ≡ true)
       → c ∨ (m ∧ d) ≡ true → c′ ∨ (m′ ∧ d′) ≡ true
grow∨∧ {true}                         hc hm hd _ rewrite hc refl          = refl
grow∨∧ {false} {c′} {true} {_} {true} hc hm hd _ rewrite hm refl | hd refl = ∨-zeroʳ c′
grow∨∧ {false} {_} {true} {_} {false} _ _ _ ()
grow∨∧ {false} {_} {false}            _ _ _ ()

demorgan : ∀ c m d → not (c ∨ (m ∧ d)) ≡ not c ∧ (not m ∨ not d)
demorgan true  _     _ = refl
demorgan false true  _ = refl
demorgan false false _ = refl

any-∷ : ∀ {A : Set} (P : A → Bool) x xs → any P xs ≡ true → any P (x ∷ xs) ≡ true
any-∷ P x xs h = trans (cong (P x ∨_) h) (∨-zeroʳ (P x))

any-++ʳ : ∀ {A : Set} (P : A → Bool) xs {ys} → any P ys ≡ true → any P (xs ++ ys) ≡ true
any-++ʳ P []       h = h
any-++ʳ P (x ∷ xs) h = any-∷ P x (xs ++ _) (any-++ʳ P xs h)

any-off : ∀ {A : Set} {P : A → Bool} {xs x} → any P xs ≡ false → x ∈ xs → P x ≡ false
any-off {P = P} {xs = y ∷ ys} h (here refl) = ∨-conicalˡ (P y) _ h
any-off {P = P} {xs = y ∷ ys} h (there m)   = any-off (∨-conicalʳ (P y) _ h) m

all-off : ∀ {A : Set} {P : A → Bool} xs → (∀ {x} → x ∈ xs → P x ≡ false) → any P xs ≡ false
all-off []       h = refl
all-off (x ∷ xs) h = off-∨ (h (here refl)) (all-off xs (λ m → h (there m)))

-- the skip test as a type former, which Agda reads as injective in the state
record Skip {n} {Γ : Ctx n} {t} {e : Closed Γ t} (s : Source) (rid : RegId) (st : EvalSt e) : Set where
  constructor skip
  field unskip : skipᵇ s rid st ≡ true

module _ {n} {Γ : Ctx n} {t : Ty} {e : Closed Γ t} (j : NodeId) where

  -- THE MARKS ONLY GROW, AND THE NODE'S ROWS ARE ALL SKIPPED.
  Marks : EvalSt e → EvalSt e → Set
  Marks st st′ = ∀ s rid → Skip s rid st → Skip s rid st′

  skipOf : EvalSt e → RegRow Γ t → Bool
  skipOf st r = skipᵇ (regSource (proj₁ (proj₂ r))) (proj₁ r) st

  Dead : EvalSt e → Set
  Dead st = ∀ {r} → r ∈ EvalSt.registry st → T (rowThrough j r) → skipOf st r ≡ true

  -- the evaluator's own liveness test is the skip's complement on the node
  alive-skip : ∀ (st : EvalSt e) (r : RegRow Γ t) → aliveThroughᶠ j st r ≡ rowThrough j r ∧ not (skipOf st r)
  alive-skip st (rid , rs , (w , p)) =
    cong (pathHasNode j p ∧_) (sym (demorgan (any (_≡ᵇ rid) (EvalSt.cancelled st))
                                             (memberSource (regSource rs) (EvalSt.dying st))
                                             (any (_≡ᵇ rid) (EvalSt.delivered st))))

  dead-alive : ∀ {st : EvalSt e} → any (aliveThroughᶠ j st) (EvalSt.registry st) ≡ false → Dead st
  dead-alive {st} h {r} r∈ th =
    not-false (∧-off th (trans (sym (alive-skip st r)) (any-off h r∈)))

  row-off : ∀ (st : EvalSt e) (r : RegRow Γ t) → (T (rowThrough j r) → skipOf st r ≡ true)
          → rowThrough j r ∧ not (skipOf st r) ≡ false
  row-off st r h with rowThrough j r
  ... | false = refl
  ... | true  = cong not (h tt)

  alive-dead : ∀ {st : EvalSt e} → Dead st → any (aliveThroughᶠ j st) (EvalSt.registry st) ≡ false
  alive-dead {st} d =
    all-off (EvalSt.registry st) (λ {r} r∈ → trans (alive-skip st r) (row-off st r (d r∈)))

  _⊙_ : ∀ {st₀ st₁ st₂ : EvalSt e} → Marks st₀ st₁ → Marks st₁ st₂ → Marks st₀ st₂
  (f ⊙ g) s rid h = g s rid (f s rid h)
  infixr 5 _⊙_

  dead-sub : ∀ {st st′ : EvalSt e} → (∀ {r} → r ∈ EvalSt.registry st′ → r ∈ EvalSt.registry st)
           → Marks st st′ → Dead st → Dead st′
  dead-sub sb mk d {r} r∈ th = Skip.unskip (mk (regSource (proj₁ (proj₂ r))) (proj₁ r) (skip (d (sb r∈) th)))

  skip-grow : ∀ {s rid} {st st′ : EvalSt e}
            → (any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ true → any (_≡ᵇ rid) (EvalSt.cancelled st′) ≡ true)
            → (memberSource s (EvalSt.dying st) ≡ true → memberSource s (EvalSt.dying st′) ≡ true)
            → (any (_≡ᵇ rid) (EvalSt.delivered st) ≡ true → any (_≡ᵇ rid) (EvalSt.delivered st′) ≡ true)
            → Skip s rid st → Skip s rid st′
  skip-grow hc hm hd (skip h) = skip (grow∨∧ hc hm hd h)

  -- EVERY WRITE A RUN MAKES TO THE MARKS ADDS TO THEM
  marks-dlv : ∀ fin rid (st : EvalSt e) → Marks st (markDlv fin rid st)
  marks-dlv false rid st _ _ (skip h) = skip h
  marks-dlv true  rid st s r h = skip-grow (λ c → c) (λ m → m) (any-∷ (_≡ᵇ r) rid (EvalSt.delivered st)) h

  marks-dying : ∀ (i : Fin n) fin (st : EvalSt e) → Marks st (shareDying i fin st)
  marks-dying i false st _ _ (skip h) = skip h
  marks-dying i true  st s r h = skip-grow (λ c → c) (any-∷ (sameSource s) (toℕ i) (EvalSt.dying st)) (λ d → d) h

  marks-kill : ∀ (cur : Maybe NodeId) (sched : Sched Γ) (st : EvalSt e) → Marks st (proj₂ (switchKill cur sched st))
  marks-kill nothing  sched st _ _ (skip h) = skip h
  marks-kill (just v) sched st s r h =
    skip-grow (any-++ʳ (_≡ᵇ r) (proj₂ (cutThrough v (EvalSt.registry st)))) (λ m → m) (λ d → d) h

  marks-take : ∀ {s} (w : Maybe (FnClo Γ s boolᵗ)) nid ns vals fin (sched : Sched Γ) (st : EvalSt e)
             → Marks st (proj₂ (proj₂ (proj₂ (takeDispatch w nid vals fin sched st ns))))
  marks-take w nid (just (take-st k)) vals fin sched st with proj₂ (proj₂ (takeVals w k vals))
  ... | true  = λ s r h → skip-grow (any-++ʳ (_≡ᵇ r) (proj₂ (cutThrough nid (EvalSt.registry st)))) (λ m → m) (λ d → d) h
  ... | false = λ { _ _ (skip h) → skip h }
  marks-take w nid (just (cell-st _))           vals fin sched st _ _ (skip h) = skip h
  marks-take w nid (just (batchSync-st _ _ _))  vals fin sched st _ _ (skip h) = skip h
  marks-take w nid (just (mergeAll-st _ _ _ _)) vals fin sched st _ _ (skip h) = skip h
  marks-take w nid (just (switch-st _ _))       vals fin sched st _ _ (skip h) = skip h
  marks-take w nid (just (exhaust-st _ _))      vals fin sched st _ _ (skip h) = skip h
  marks-take w nid nothing                      vals fin sched st _ _ (skip h) = skip h

  marks-scan : ∀ {s u} (fn : FnClo Γ (u ×ᵗ s) u) nid vals fin (sched : Sched Γ) (st : EvalSt e) ns
             → Marks st (proj₂ (proj₂ (proj₂ (scanDispatch fn nid vals fin sched st ns))))
  marks-scan {u = u} fn nid vals fin sched st (just (cell-st {w} a)) with w ≟ᵗ u
  ... | no  _    = λ { _ _ (skip h) → skip h }
  ... | yes refl = λ { _ _ (skip h) → skip h }
  marks-scan fn nid vals fin sched st (just (take-st _))           _ _ (skip h) = skip h
  marks-scan fn nid vals fin sched st (just (batchSync-st _ _ _))  _ _ (skip h) = skip h
  marks-scan fn nid vals fin sched st (just (mergeAll-st _ _ _ _)) _ _ (skip h) = skip h
  marks-scan fn nid vals fin sched st (just (switch-st _ _))       _ _ (skip h) = skip h
  marks-scan fn nid vals fin sched st (just (exhaust-st _ _))      _ _ (skip h) = skip h
  marks-scan fn nid vals fin sched st nothing                      _ _ (skip h) = skip h

  marks-batch : ∀ {s} nid (vals : List _) fin (sched : Sched Γ) (st : EvalSt e) ns
              → Marks st (proj₂ (proj₂ (proj₂ (batchDispatch {s = s} nid vals fin sched st ns))))
  marks-batch {s = s} nid vals fin sched st (just (batchSync-st {w} true bur done)) with w ≟ᵗ s
  ... | no  _    = λ { _ _ (skip h) → skip h }
  ... | yes refl = λ { _ _ (skip h) → skip h }
  marks-batch {s = s} nid vals fin sched st (just (batchSync-st {w} false bur done)) with w ≟ᵗ s
  ... | no  _    = λ { _ _ (skip h) → skip h }
  ... | yes refl = λ { _ _ (skip h) → skip h }
  marks-batch nid vals fin sched st (just (cell-st _))           _ _ (skip h) = skip h
  marks-batch nid vals fin sched st (just (take-st _))           _ _ (skip h) = skip h
  marks-batch nid vals fin sched st (just (mergeAll-st _ _ _ _)) _ _ (skip h) = skip h
  marks-batch nid vals fin sched st (just (switch-st _ _))       _ _ (skip h) = skip h
  marks-batch nid vals fin sched st (just (exhaust-st _ _))      _ _ (skip h) = skip h
  marks-batch nid vals fin sched st nothing                      _ _ (skip h) = skip h

  marks-wrap : ∀ (op : AllOp) nid fin (sched : Sched Γ) (st : EvalSt e)
             → Marks st (proj₂ (proj₂ (thruWrap op nid fin (sched , st))))
  marks-wrap op nid false sched st _ _ (skip h) = skip h
  marks-wrap mergeAllᵒ nid true sched st with lookupNode nid (EvalSt.nodes st)
  ... | just (mergeAll-st _ _ _ _)  = λ { _ _ (skip h) → skip h }
  ... | just (cell-st _)            = λ { _ _ (skip h) → skip h }
  ... | just (take-st _)            = λ { _ _ (skip h) → skip h }
  ... | just (batchSync-st _ _ _)   = λ { _ _ (skip h) → skip h }
  ... | just (switch-st _ _)        = λ { _ _ (skip h) → skip h }
  ... | just (exhaust-st _ _)       = λ { _ _ (skip h) → skip h }
  ... | nothing                     = λ { _ _ (skip h) → skip h }
  marks-wrap switchᵒ nid true sched st with lookupNode nid (EvalSt.nodes st)
  ... | just (switch-st _ _)        = λ { _ _ (skip h) → skip h }
  ... | just (cell-st _)            = λ { _ _ (skip h) → skip h }
  ... | just (take-st _)            = λ { _ _ (skip h) → skip h }
  ... | just (batchSync-st _ _ _)   = λ { _ _ (skip h) → skip h }
  ... | just (mergeAll-st _ _ _ _)  = λ { _ _ (skip h) → skip h }
  ... | just (exhaust-st _ _)       = λ { _ _ (skip h) → skip h }
  ... | nothing                     = λ { _ _ (skip h) → skip h }
  marks-wrap exhaustᵒ nid true sched st with lookupNode nid (EvalSt.nodes st)
  ... | just (exhaust-st _ _)       = λ { _ _ (skip h) → skip h }
  ... | just (cell-st _)            = λ { _ _ (skip h) → skip h }
  ... | just (take-st _)            = λ { _ _ (skip h) → skip h }
  ... | just (batchSync-st _ _ _)   = λ { _ _ (skip h) → skip h }
  ... | just (mergeAll-st _ _ _ _)  = λ { _ _ (skip h) → skip h }
  ... | just (switch-st _ _)        = λ { _ _ (skip h) → skip h }
  ... | nothing                     = λ { _ _ (skip h) → skip h }

  marks-finish : ∀ (i : Fin n) fin r → Marks (proj₂ (proj₂ r)) (proj₂ (proj₂ (shareFinish {e = e} i fin r)))
  marks-finish i false r                 _ _ (skip h) = skip h
  marks-finish i true  (emits , sc , st) _ _ (skip h) = skip h

  dead-finish : ∀ (i : Fin n) fin r → Dead (proj₂ (proj₂ r)) → Dead (proj₂ (proj₂ (shareFinish {e = e} i fin r)))
  dead-finish i false r                 d = d
  dead-finish i true  (emits , sc , st) d = dead-sub {st = st} {st′ = proj₂ (proj₂ (shareFinish {e = e} i true (emits , sc , st)))} (drop-sub (toℕ i) (EvalSt.registry st)) (λ { _ _ (skip h) → skip h }) d

  dead-dying : ∀ (i : Fin n) fin {st : EvalSt e} → Dead st → Dead (shareDying i fin st)
  dead-dying i false d = d
  dead-dying i true {st} d = dead-sub {st = st} {st′ = shareDying i true st} (λ r∈ → r∈) (marks-dying i true st) d

  -- the switch's cut grows the cancelled marks and only drops rows
  kill-marks : ∀ (cur : Maybe NodeId) {sched sched₁ : Sched Γ} {st st₁ : EvalSt e}
             → switchKill cur sched st ≡ (sched₁ , st₁) → Marks st st₁
  kill-marks cur {sched} {st = st} kl = subst (λ p → Marks st (proj₂ p)) kl (marks-kill cur sched st)

  kill-dead : ∀ (cur : Maybe NodeId) {sched sched₁ : Sched Γ} {st st₁ : EvalSt e}
            → switchKill cur sched st ≡ (sched₁ , st₁) → Dead st → Dead st₁
  kill-dead cur {sched} {st = st} kl =
    subst (λ p → Dead st → Dead (proj₂ p)) kl (dead-sub (kill-sub cur sched st) (marks-kill cur sched st))

  kill-ct : ∀ (cur : Maybe NodeId) {sched sched₁ : Sched Γ} {st st₁ : EvalSt e}
          → switchKill cur sched st ≡ (sched₁ , st₁) → nodeCt sched₁ ≡ nodeCt sched
  kill-ct cur {sched} {st = st} kl = subst (λ p → nodeCt (proj₁ p) ≡ nodeCt sched) kl (switchKill-ct cur sched st)

  -- a write that leaves the three marks alone leaves the skips alone
  same : ∀ {st st′ : EvalSt e} → EvalSt.cancelled st ≡ EvalSt.cancelled st′ → EvalSt.dying st ≡ EvalSt.dying st′
       → EvalSt.delivered st ≡ EvalSt.delivered st′ → Marks st st′
  same refl refl refl s rid (skip h) = skip h

  -- a registration leaves the marks alone
  reg-marks : ∀ {u} {st : EvalSt e} (rid : RegId) (rs : RegSrc Γ) (p : Path Γ (regFloor rs) u t)
            → Marks st (register rid rs p st)
  reg-marks rid rs p _ _ (skip h) = skip h

  -- A ROW REGISTERED OFF THE NODE leaves every row through it skipped
  dead-register : ∀ {u} {st : EvalSt e} (rid : RegId) (rs : RegSrc Γ) (p : Path Γ (regFloor rs) u t)
                → pathHasNode j p ≡ false → Dead st → Dead (register rid rs p st)
  dead-register {st = st} rid rs p off d r∈ th with ∈-register {st = st} rid rs p r∈
  ... | inj₁ r∈′  = d r∈′ th
  ... | inj₂ refl = ⊥-elim (subst T off th)

  -- and a frame at the counter is not the node
  fresh-off : ∀ {c} {b} → j < c → b ≡ false → any (_≡ᵇ j) (c ∷ []) ∨ b ≡ false
  fresh-off lt off = off-∨ (off-∨ (<→≢ᵇ lt) refl) off

  -- AN ADMITTED ROW EITHER MISSES THE NODE OR IS SKIPPED
  data Gate {lo} (i : Fin n) (st : EvalSt e) (x : RegId × Path Γ lo (lookup Γ i) t) : Set where
    miss    : pathHasNode j (proj₂ x) ≡ false → Gate i st x
    skipped : skipᵇ (toℕ i) (proj₁ x) st ≡ true → Gate i st x

  gate-marks : ∀ {lo} {i : Fin n} {st st′ : EvalSt e} {x : RegId × Path Γ lo (lookup Γ i) t}
             → Marks st st′ → Gate i st x → Gate i st′ x
  gate-marks mk (miss h) = miss h
  gate-marks {i = i} {x = x} mk (skipped h) = skipped (Skip.unskip (mk (toℕ i) (proj₁ x) (skip h)))

  gate-off : ∀ {lo} {i : Fin n} {st : EvalSt e} {rid} {p : Path Γ lo (lookup Γ i) t}
           → skipᵇ (toℕ i) rid st ≡ false → Gate i st (rid , p) → pathHasNode j p ≡ false
  gate-off sk (miss h) = h
  gate-off sk (skipped h) = ⊥-elim (contra h sk)

  admit-gate : ∀ (i : Fin n) (reg : List (RegRow Γ t)) {st : EvalSt e}
             → (∀ {r} → r ∈ reg → T (rowThrough j r) → skipOf st r ≡ true)
             → ∀ {x} → x ∈ shareAdmit i reg → Gate i st x
  admit-gate i [] d ()
  admit-gate i ((rid , atDyn _ _ , _) ∷ reg) {st} d x∈ = admit-gate i reg {st} (λ m → d (there m)) x∈
  admit-gate i ((rid , atSlot k , (u , p)) ∷ reg) {st} d x∈ with i ≟ᶠ k | u ≟ᵗ lookup Γ i
  ... | no  _    | _        = admit-gate i reg {st} (λ m → d (there m)) x∈
  ... | yes _    | no  _    = admit-gate i reg {st} (λ m → d (there m)) x∈
  ... | yes refl | yes refl with x∈
  ...   | there m   = admit-gate i reg {st} (λ m′ → d (there m′)) m
  ...   | here refl with pathHasNode j p in eq
  ...     | false = miss eq
  ...     | true  = skipped (d (here refl) (subst T (sym eq) tt))

  DKb : Bool → ℕ → EvalSt e → EvalSt e → Set
  DKb b c st st′ = Marks st st′ × (b ≡ false → j < c → Dead st → Dead st′)

  -- a write that leaves the rows and the marks alone
  lead : ∀ {b} {c} {st st₁ st′ : EvalSt e}
       → EvalSt.registry st ≡ EvalSt.registry st₁ → EvalSt.cancelled st ≡ EvalSt.cancelled st₁
       → EvalSt.dying st ≡ EvalSt.dying st₁ → EvalSt.delivered st ≡ EvalSt.delivered st₁
       → DKb b c st₁ st′ → DKb b c st st′
  lead {st = st} {st₁} rg c m dl (M , D) = same c m dl ⊙ M , λ off lt d → D off lt λ {r} r∈ th →
    Skip.unskip (same {st = st} {st₁} c m dl (regSource (proj₁ (proj₂ r))) (proj₁ r) (skip (d (subst (r ∈_) (sym rg) r∈) th)))

  still : ∀ {b} {c} {st : EvalSt e} → DKb b c st st
  still = (λ { _ _ (skip h) → skip h }) , λ _ _ d → d

  -- a step that leaves the rows and the marks alone
  stay : ∀ {b} {c} {st st′ : EvalSt e}
       → EvalSt.registry st ≡ EvalSt.registry st′ → EvalSt.cancelled st ≡ EvalSt.cancelled st′
       → EvalSt.dying st ≡ EvalSt.dying st′ → EvalSt.delivered st ≡ EvalSt.delivered st′
       → DKb b c st st′
  stay {b} {c} {st} {st′} rg cc m dl = lead {b} {c} {st} {st′} {st′} rg cc m dl (still {b} {c} {st′})

  -- THE FOURTEEN-MEMBER INDUCTION, in the shape of the rule's.
  -- STRUCTURAL SCC: subscribeE-dk subscribeSharedSlot-dk subscribeAll-dk subscribeInner-dk stepFrame-dk thruWalk-dk thruConsume-dk innerReact-dk innerFinish-dk mergeAllDrain-dk foldPath-dk dispatchShare-dk shareWalk-dk shareGo-dk
  subscribeE-dk : ∀ {u lo} {b} {κ : Path Γ lo u t} {now} {sched sched′ : Sched Γ} {st st′ : EvalSt e} {out}
                → subscribeE⇓ {e = e} {u = u} b κ now sched st (out , sched′ , st′)
                → DKb (pathHasNode j κ) (nodeCt sched) st st′

  subscribeSharedSlot-dk : ∀ {lo} {i : Fin n} {d} {κ : Path Γ lo (lookup Γ i) t} {below} {now}
                             {sched sched′ : Sched Γ} {st st′ : EvalSt e} {out}
                         → subscribeSharedSlot⇓ {e = e} i d κ below now sched st (out , sched′ , st′)
                         → DKb (pathHasNode j κ) (nodeCt sched) st st′

  subscribeAll-dk : ∀ {u lo} {op} {ns} {b} {κ : Path Γ lo u t} {now}
                      {sched sched′ : Sched Γ} {st st′ : EvalSt e} {out}
                  → subscribeAll⇓ {e = e} op ns b κ now sched st (out , sched′ , st′)
                  → DKb (pathHasNode j κ) (nodeCt sched) st st′

  subscribeInner-dk : ∀ {u lo} {op a} {κ : Path Γ lo u t} {now} {o}
                        {sched sched′ : Sched Γ} {st st′ : EvalSt e} {inst out}
                    → subscribeInner⇓ {e = e} op a κ now o sched st (inst , out , sched′ , st′)
                    → DKb (any (_≡ᵇ j) (a ∷ []) ∨ pathHasNode j κ) (nodeCt sched) st st′

  stepFrame-dk : ∀ {s u lo} {f} {κ : Path Γ lo u t} {now vals fin}
                   {sched sched′ : Sched Γ} {st st′ : EvalSt e} {out vals′ fin′}
               → stepFrame⇓ {e = e} {s = s} now f κ vals fin sched st (out , vals′ , fin′ , sched′ , st′)
               → DKb (any (_≡ᵇ j) (frameNodes f) ∨ pathHasNode j κ) (nodeCt sched) st st′

  thruWalk-dk : ∀ {u lo} {op a} {κ : Path Γ lo u t} {now} {vals}
                  {sched sched′ : Sched Γ} {st st′ : EvalSt e} {out}
              → thruWalk⇓ {e = e} op a κ now vals sched st (out , sched′ , st′)
              → DKb (any (_≡ᵇ j) (a ∷ []) ∨ pathHasNode j κ) (nodeCt sched) st st′

  thruConsume-dk : ∀ {u lo} {op a} {κ : Path Γ lo u t} {now} {o}
                     {sched sched′ : Sched Γ} {st st′ : EvalSt e} {out}
                 → thruConsume⇓ {e = e} op a κ now o sched st (out , sched′ , st′)
                 → DKb (any (_≡ᵇ j) (a ∷ []) ∨ pathHasNode j κ) (nodeCt sched) st st′

  innerReact-dk : ∀ {s lo} {op a inst} {κ : Path Γ lo s t} {now} {vals}
                    {sched sched′ : Sched Γ} {st st′ : EvalSt e} {alive} {out vals′ fin}
                → innerReact⇓ {e = e} op a inst κ now vals sched st alive (out , vals′ , fin , sched′ , st′)
                → DKb (any (_≡ᵇ j) (a ∷ []) ∨ pathHasNode j κ) (nodeCt sched) st st′

  innerFinish-dk : ∀ {s lo} {op a inst} {κ : Path Γ lo s t} {now} {vals}
                     {sched sched′ : Sched Γ} {st st′ : EvalSt e} {m} {out vals′ fin}
                 → innerFinish⇓ {e = e} op a inst κ now vals sched st m (out , vals′ , fin , sched′ , st′)
                 → DKb (any (_≡ᵇ j) (a ∷ []) ∨ pathHasNode j κ) (nodeCt sched) st st′

  mergeAllDrain-dk : ∀ {s lo} {a} {κ : Path Γ lo s t} {now} {fuel lim act od q}
                       {sched sched′ : Sched Γ} {st st′ : EvalSt e} {out act′ q′}
                   → mergeAllDrain⇓ {e = e} a κ now fuel lim act od q sched st (out , act′ , q′ , sched′ , st′)
                   → DKb (any (_≡ᵇ j) (a ∷ []) ∨ pathHasNode j κ) (nodeCt sched) st st′

  foldPath-dk : ∀ {u lo} {κ : Path Γ lo u t} {now vals fin}
                  {sched sched′ : Sched Γ} {st st′ : EvalSt e} {emits}
              → foldPath⇓ {e = e} now κ vals fin sched st (emits , sched′ , st′)
              → DKb (pathHasNode j κ) (nodeCt sched) st st′

  dispatchShare-dk : ∀ {lo} {i : Fin n} {below} {now vals fin} {sched : Sched Γ} {st : EvalSt e} {r}
                   → dispatchShare⇓ {e = e} {lo = lo} now i below vals fin sched st r
                   → DKb false (nodeCt sched) st (proj₂ (proj₂ r))

  shareWalk-dk : ∀ {i : Fin n} {now vals fin} {sched : Sched Γ} {st : EvalSt e} {r}
               → shareWalk⇓ {e = e} now i vals fin sched st r
               → DKb false (nodeCt sched) st (proj₂ (proj₂ r))

  shareGo-dk : ∀ {lo} {i : Fin n} {now vals fin} {ps : List (RegId × Path Γ lo (lookup Γ i) t)}
                 {sched : Sched Γ} {st : EvalSt e} {r}
             → shareGo⇓ {e = e} {lo = lo} now i vals fin ps sched st r
             → Marks st (proj₂ (proj₂ r))
               × (j < nodeCt sched → (∀ {x} → x ∈ ps → Gate i st x) → Dead st → Dead (proj₂ (proj₂ r)))

  subscribeE-dk (subs-floor _ f)        = foldPath-dk f
  subscribeE-dk (subs-shared _ slot)    = subscribeSharedSlot-dk slot
  subscribeE-dk (subs-hot-done _ _ _ f) = foldPath-dk f
  subscribeE-dk {κ = κ} {st = st} (subs-hot-live {i = i} {rid = rid} below _ _ refl) =
    (λ { _ _ (skip h) → skip h }) , λ off lt d → dead-register {st = st} rid (atSlot i) (lowerFloor below κ) (trans (lower-nodes below κ j) off) d
  subscribeE-dk (subs-cold-sync _ _ f)  = foldPath-dk f
  subscribeE-dk {κ = κ} {st = st} (subs-cold-async {lo = lo} {src = src} {rid = rid} _ _ refl refl refl f) =
    reg-marks {st = st} rid (atDyn src lo) κ ⊙ proj₁ F , λ off lt d → proj₂ F off lt (dead-register {st = st} rid (atDyn src lo) κ off d)
    where F = foldPath-dk f
  subscribeE-dk (subs-of f)             = foldPath-dk f
  subscribeE-dk (subs-empty f)          = foldPath-dk f
  subscribeE-dk (subs-takeWhile refl sub) =
    same refl refl refl ⊙ proj₁ S , λ off lt d → proj₂ S (fresh-off lt off) (m<n⇒m<1+n lt) d
    where S = subscribeE-dk sub
  subscribeE-dk (subs-batchSync refl sub f) =
    same refl refl refl ⊙ proj₁ S ⊙ same refl refl refl ⊙ proj₁ F , λ off lt d →
      proj₂ F (fresh-off lt off) (<-≤-trans (m<n⇒m<1+n lt) (subscribeE-ct sub)) (proj₂ S (fresh-off lt off) (m<n⇒m<1+n lt) d)
    where S = subscribeE-dk sub
          F = foldPath-dk f
  subscribeE-dk (subs-map sub)          = subscribeE-dk sub
  subscribeE-dk (subs-scan refl sub) =
    same refl refl refl ⊙ proj₁ S , λ off lt d → proj₂ S (fresh-off lt off) (m<n⇒m<1+n lt) d
    where S = subscribeE-dk sub
  subscribeE-dk (subs-flatten sa)       = subscribeAll-dk sa
  subscribeE-dk (subs-μ sub)            = subscribeE-dk sub
  subscribeE-dk {u = u} {lo} {κ = κ} {st = st} (subs-defer {nid = nid} {src = src} {rid = rid} refl refl refl refl) =
    (λ { _ _ (skip h) → skip h }) , λ off lt d →
      dead-register {st = installNode nid (mergeAll-st {t = u} nothing 0 [] false) st} rid (atDyn src lo) _ (fresh-off lt off) d
  subscribeE-dk (subs-mint refl sub) =
    same refl refl refl ⊙ proj₁ S , λ off lt d → proj₂ S off lt d
    where S = subscribeE-dk sub

  subscribeSharedSlot-dk (slot-spent _ f) = foldPath-dk f
  subscribeSharedSlot-dk {i = i} {κ = κ} {below = below} {st = st} (slot-join {rid = rid} _ _ refl) =
    (λ { _ _ (skip h) → skip h }) , λ off lt d → dead-register {st = st} rid (atSlot i) (lowerFloor below κ) (trans (lower-nodes below κ j) off) d
  subscribeSharedSlot-dk {i = i} {κ = κ} {below = below} {st = st} (slot-connect _ _ (connect {rid = rid} refl sub)) =
    same refl refl refl ⊙ proj₁ S , λ off lt d → proj₂ S refl lt (dead-register
      {st = record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st }} rid (atSlot i) (lowerFloor below κ) (trans (lower-nodes below κ j) off) d)
    where S = subscribeE-dk sub

  subscribeAll-dk (sub-all refl sub) =
    same refl refl refl ⊙ proj₁ S , λ off lt d → proj₂ S (fresh-off lt off) (m<n⇒m<1+n lt) d
    where S = subscribeE-dk sub

  subscribeInner-dk {a = a} {κ = κ} (inner refl sub) =
    same refl refl refl ⊙ proj₁ S , λ off lt d →
      proj₂ S (off-∨ (off-∨ (∨-conicalˡ (a ≡ᵇ j) false (∨-conicalˡ (any (_≡ᵇ j) (a ∷ [])) (pathHasNode j κ) off))
                            (off-∨ (<→≢ᵇ lt) refl))
                     (∨-conicalʳ (any (_≡ᵇ j) (a ∷ [])) (pathHasNode j κ) off)) (m<n⇒m<1+n lt) d
    where S = subscribeE-dk sub

  stepFrame-dk step-map = stay refl refl refl refl
  stepFrame-dk (step-scan {fn = fn} {nid = c} {vals = vals} {fin} {sched} {st}) =
    marks-scan fn c vals fin sched st (lookupNode c (EvalSt.nodes st)) , λ _ _ d →
      dead-sub (λ r∈ → subst (_ ∈_) (scanReg fn c vals fin sched st (lookupNode c (EvalSt.nodes st))) r∈)
               (marks-scan fn c vals fin sched st (lookupNode c (EvalSt.nodes st))) d
  stepFrame-dk (step-take {w = w} {nid = c} {vals = vals} {fin} {sched} {st}) =
    marks-take w c (lookupNode c (EvalSt.nodes st)) vals fin sched st , λ _ _ d →
      dead-sub (takeReg w c (lookupNode c (EvalSt.nodes st)) vals fin sched st)
               (marks-take w c (lookupNode c (EvalSt.nodes st)) vals fin sched st) d
  stepFrame-dk (step-batchSync {nid = c} {vals = vals} {fin} {sched} {st}) =
    marks-batch c vals fin sched st (lookupNode c (EvalSt.nodes st)) , λ _ _ d →
      dead-sub (λ r∈ → subst (_ ∈_) (batchReg c vals fin sched st (lookupNode c (EvalSt.nodes st))) r∈)
               (marks-batch c vals fin sched st (lookupNode c (EvalSt.nodes st))) d
  stepFrame-dk {κ = κ} (step-from-inner {allNid = a} {inst = m} r) =
    proj₁ R , λ off lt d →
      proj₂ R (off-∨ (off-∨ (∨-conicalˡ (a ≡ᵇ j) ((m ≡ᵇ j) ∨ false)
                                 (∨-conicalˡ (any (_≡ᵇ j) (a ∷ m ∷ [])) (pathHasNode j κ) off)) refl)
                     (∨-conicalʳ (any (_≡ᵇ j) (a ∷ m ∷ [])) (pathHasNode j κ) off)) lt d
    where R = innerReact-dk r
  stepFrame-dk (step-thru-outer {op = op} {nid = c} {fin = fin} {sched′ = sched′} {st′ = st′} w) =
    proj₁ W ⊙ marks-wrap op c fin sched′ st′ , λ off lt d →
      dead-sub (wrap-reg op c fin sched′ st′) (marks-wrap op c fin sched′ st′) (proj₂ W off lt d)
    where W = thruWalk-dk w

  thruWalk-dk walk-nil = stay refl refl refl refl
  thruWalk-dk (walk-echo fp w) =
    same refl refl refl ⊙ proj₁ F ⊙ same refl refl refl ⊙ proj₁ W ⊙ same refl refl refl , λ off lt d → proj₂ W off (<-≤-trans lt (foldPath-ct fp)) (proj₂ F (∨-conicalʳ _ _ off) lt d)
    where F = foldPath-dk fp
          W = thruWalk-dk w
  thruWalk-dk (walk-cons c w) =
    same refl refl refl ⊙ proj₁ C ⊙ same refl refl refl ⊙ proj₁ W ⊙ same refl refl refl , λ off lt d → proj₂ W off (<-≤-trans lt (thruConsume-ct c)) (proj₂ C off lt d)
    where C = thruConsume-dk c
          W = thruWalk-dk w

  thruConsume-dk (consume-all-sub _ _ c)   = lead refl refl refl refl (subscribeInner-dk c)
  thruConsume-dk (consume-all-enqueue _ _) = stay refl refl refl refl
  thruConsume-dk (consume-all-nil _)       = stay refl refl refl refl
  thruConsume-dk (consume-switch-sub {cur = cur} _ kl _ c) =
    kill-marks cur kl ⊙ same refl refl refl ⊙ proj₁ C , λ off lt d → proj₂ C off (subst (j <_) (sym (kill-ct cur kl)) lt) (kill-dead cur kl d)
    where C = subscribeInner-dk c
  thruConsume-dk (consume-switch-nil _)    = stay refl refl refl refl
  thruConsume-dk (consume-exhaust-sub _ c) = lead refl refl refl refl (subscribeInner-dk c)
  thruConsume-dk (consume-exhaust-nil _)   = stay refl refl refl refl

  innerReact-dk react-false      = stay refl refl refl refl
  innerReact-dk (react-alive _)  = stay refl refl refl refl
  innerReact-dk (react-dead _ f) = innerFinish-dk f

  innerFinish-dk (finish-all-drain fp dr) =
    same refl refl refl ⊙ proj₁ F ⊙ same refl refl refl ⊙ proj₁ D ⊙ same refl refl refl , λ off lt d → proj₂ D off (<-≤-trans lt (foldPath-ct fp)) (proj₂ F (∨-conicalʳ _ _ off) lt d)
    where F = foldPath-dk fp
          D = mergeAllDrain-dk dr
  innerFinish-dk (finish-switch-clear _) = stay refl refl refl refl
  innerFinish-dk finish-exhaust-clear    = stay refl refl refl refl
  innerFinish-dk (finish-nil _)          = stay refl refl refl refl

  mergeAllDrain-dk drain-spent       = stay refl refl refl refl
  mergeAllDrain-dk drain-nil         = stay refl refl refl refl
  mergeAllDrain-dk (drain-no-room _) = stay refl refl refl refl
  mergeAllDrain-dk (drain-room _ c _ dr) =
    same refl refl refl ⊙ proj₁ C ⊙ same refl refl refl ⊙ proj₁ D , λ off lt d → proj₂ D off (<-≤-trans lt (subscribeInner-ct c)) (proj₂ C off lt d)
    where C = subscribeInner-dk c
          D = mergeAllDrain-dk dr

  foldPath-dk fold-root     = stay refl refl refl refl
  foldPath-dk (fold-sink d) = proj₁ D , λ _ lt dd → proj₂ D refl lt dd
    where D = dispatchShare-dk d
  foldPath-dk (fold-step sf r) =
    same refl refl refl ⊙ proj₁ S ⊙ same refl refl refl ⊙ proj₁ R ⊙ same refl refl refl , λ off lt d → proj₂ R (∨-conicalʳ _ _ off) (<-≤-trans lt (stepFrame-ct sf)) (proj₂ S off lt d)
    where S = stepFrame-dk sf
          R = foldPath-dk r

  dispatchShare-dk (disp {i = i} {fin = fin} {st = st} {r = r} w) =
    marks-dying i fin st ⊙ same refl refl refl ⊙ proj₁ W ⊙ same refl refl refl ⊙ marks-finish i fin r , λ _ lt d →
      dead-finish i fin r (proj₂ W refl lt (dead-dying i fin d))
    where W = shareWalk-dk w

  shareWalk-dk walk-nil = stay refl refl refl refl
  shareWalk-dk {st = st} (walk-end g) =
    same refl refl refl ⊙ proj₁ G ⊙ same refl refl refl , λ _ lt d → proj₂ G lt (λ m → gate-marks (same refl refl refl) (admit-gate _ (EvalSt.registry st) {st} d m)) d
    where G = shareGo-dk g
  shareWalk-dk {st = st} (walk-more g w) =
    same refl refl refl ⊙ proj₁ G ⊙ same refl refl refl ⊙ proj₁ W ⊙ same refl refl refl , λ _ lt d → proj₂ W refl (<-≤-trans lt (shareGo-ct g)) (proj₂ G lt (λ m → gate-marks (same refl refl refl) (admit-gate _ (EvalSt.registry st) {st} d m)) d)
    where G = shareGo-dk g
          W = shareWalk-dk w

  shareGo-dk go-nil       = (λ { _ _ (skip h) → skip h }) , λ _ _ d → d
  shareGo-dk (go-cut _ g) = same refl refl refl ⊙ proj₁ G ⊙ same refl refl refl , λ lt gs d → proj₂ G lt (λ m → gs (there m)) d
    where G = shareGo-dk g
  shareGo-dk (go-live {fin = fin} {rid = rid} {st₀ = st₀} sk f g) =
    M₀ ⊙ same refl refl refl ⊙ proj₁ F ⊙ same refl refl refl ⊙ proj₁ G ⊙ same refl refl refl , λ lt gs d →
      proj₂ G (<-≤-trans lt (foldPath-ct f)) (λ m → gate-marks (M₀ ⊙ same refl refl refl ⊙ proj₁ F ⊙ same refl refl refl) (gs (there m)))
        (proj₂ F (gate-off sk (gs (here refl))) lt (dead-sub (λ r∈ → r∈) M₀ d))
    where M₀ = marks-dlv fin rid st₀
          F  = foldPath-dk f
          G  = shareGo-dk g

-- A FOLD DOWN A PATH OFF A NODE BELOW THE COUNTER LEAVES THE NODE AS
-- DEAD AS IT FOUND IT, read through the evaluator's own liveness test
fold-dead : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo} {κ : Path Γ lo u t} {now vals fin}
              {sched : Sched Γ} {st : EvalSt e} {r} (j : NodeId)
          → foldPath⇓ {e = e} now κ vals fin sched st r
          → pathHasNode j κ ≡ false → j < nodeCt sched
          → any (aliveThroughᶠ j st) (EvalSt.registry st) ≡ false
          → any (aliveThroughᶠ j (proj₂ (proj₂ r))) (EvalSt.registry (proj₂ (proj₂ r))) ≡ false
fold-dead {st = st} {r} j f off lt dd = alive-dead j {proj₂ (proj₂ r)} (proj₂ (foldPath-dk j f) off lt (dead-alive j {st} dd))
