------------------------------------------------------------------
-- STRATUM DOCUMENTATION, INHERITED FROM THE DELETED `Wet` UMBRELLA.
-- That module held nothing but an `open import ... public` re-export,
-- which is now illegal — a name is imported from where it is DEFINED — so
-- the umbrella went and its prose came here, this file being the
-- stratum's bottom rung.  Consumers import the Parts directly now;
-- nothing was proven or unproven by the move.
------------------------------------------------------------------
-- STRATUM 2b of Verify-Budget-Sufficient: THE WET FAMILY.
--
-- THIS MODULE'S COST IS MEASURED, and the figures are in
-- typecheck-performance-numbers.md.  It is worth measuring because
-- Subscribe-Face's cost turned out to be 86% Agda's Positivity pass over ONE
-- mutual block, and this module is written in the same style.
--
-- The half that steps the evaluator.  The Keeps ring (slot/share
-- monotonicity), the size-elim laws, the ledger arithmetic, the wet
-- lemmas for every evaluator entry point, subscribeE-walkS and
-- subscribeAll-wet, cascadeGo-walk, the width family, and the burst
-- cores (burst-dry/burst-bounded, now in .Caps-Bridge) and pop ring (pop-INV/
-- pop-head-bounded) that compose them.
--
-- `drain-dry` and `budget-sufficient` — the theorem
-- Verify-Well-Formed consumes — MOVED to `.Caps-Bridge`
-- (the upside-down ruling): a
-- module above `.Wet` can consume `.Caps-Bridge`'s `cascade-wet-via-caps`
-- in place of the cascade wet face (whose dry half is now
-- `cascadeGo-nodry`, .Burst-Walk); `.Wet` itself
-- cannot, since `.Caps-Bridge` imports `.Wet`.
--
-- This module is a LAYER OVER .Caps: the wet cores'
-- reset caps and per-instant store bound are read off `capsAt`, the caps
-- recurrence, which is the only entry-computable reach bound in the
-- machine (round3b-ledger-reset-absurd rules out the ledger).  The
-- recurrence sits in its own prerequisite module rather than in
-- .Caps-Face — the Keeps-Ring precedent, taken the same day the layering
-- landed — so this module and the caps FACE are still siblings and a
-- caps-face grind does not re-check twenty minutes of wet clauses.

-- SPLIT INTO Wet/Part1..Part6 to bound per-edit recheck time;
-- no mutual block was broken and no content changed.  Parts 4 and 5 were
-- the width walk and went with it, so the family is now
-- Parts 1, 2, 3 and 6, imported directly — there is no umbrella.
module Verify-Budget-Sufficient.Wet.Part1 where

open import Data.Bool    using (Bool; true; false; _∧_; if_then_else_)
open import Data.Nat     using (ℕ; zero; suc; _+_; _*_; _^_; _≤_; _⊔_; _≤ᵇ_; _≡ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (≤ᵇ⇒≤; ≤⇒≤ᵇ; ≤-trans; ≤-refl; ≤-reflexive; +-identityʳ; +-monoˡ-≤; *-monoˡ-≤; *-monoʳ-≤;
  m≤m+n; m≤n+m; +-mono-≤; ^-monoʳ-≤; *-identityʳ; ^-monoˡ-≤; ^-*-assoc; ^-distribˡ-+-*;
  *-mono-≤; +-monoʳ-≤; m≤m⊔n; m≤n⊔m; ⊔-lub)
open import Data.Nat.Solver     using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.List    using (List; []; _∷_; _++_; length; map)
open import Data.Bool.ListAction using (all; any)
open import Data.Fin     using (Fin)
import Data.Fin as Fin
open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []ᵃ; _∷_ to _∷ᵃ_; map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties
  using (concat⁺; tabulate⁺)
  renaming (++⁺ to all-++; ++⁻ˡ to all-++ˡ; ++⁻ʳ to all-++ʳ)
open import Data.List.Properties using (length-++)
open import Data.Maybe   using (Maybe; nothing; just)
open import Relation.Nullary using (yes; no)
open import Data.Vec     using (Vec; lookup) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit    using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Rx.Prim      using (Tick; Id; Source; InstEmit; _at_from_as_; InstEvent; Gas; after_,_)
open import Rx.Exp       using (Ty; _×ᵗ_; _≟ᵗ_; Ctx; Closed; Val; sizeᵗ; sizeᵗˢ; sizeᵛ; Tm; Fn; evalTm; applyFn)
open import Rx.Evaluator using (Sched; EvalSt; LiveSource; scanVals; memberSource; RegId; Chain; NodeState; scan-st; take-st;
  flatten-st; switch-st; exhaust-st; installNode; setNode; lookupNode; NodeId; AllOp;
  scan-f; take-f; Stream; sweepLive; takeVals; cutThrough; pathHasNode; Path; stepFrame;
  register; flattenᵒ; switchᵒ; exhaustᵒ; splitEvents; splitBurst; flattenBump; switchKill;
  thruWrap)
open import Rx.Slots using (slotsSize)

open import Verify-Budget-Sufficient.Measures using
  (2≤C; all-++-intro; all-impl; allB-head;
                                                      allB-tail; applyFn-sharp; boundedNode;
                                                      burstB?; capᴱ; capᴱ-mono; caseWᵗ;
                                                      cutThrough-len; evalWith-sharp;
                                                      eventB?; eventB?-widen; E≤E*3^;
                                                      fcB-live; fcB-nodes; fnCap-evalWith;
                                                      fnCapBounded?; fnCapLive; fnCapNode;
                                                      fnCapᵗ; fnCapᵗˢ; fnCapᵛ; frameB?;
                                                      grow-pow; install-bounded; INV-parts;
                                                      INV?; m+n≤m*n; one≤3^; pathB?;
                                                      pathB?-widen; pow1; regsB?;
                                                      regsB?-widen; scanVals-sharp;
                                                      setNode-bounded; splitEvents-bk-B;
                                                      splitEvents-vals-B; stB-live;
                                                      stB-nodes; stBounded-widen; stBounded?;
                                                      sweepLive-all; sweepLive-bounded;
                                                      takeVals-all; valB-fc; valB-sz; valB?;
                                                      ∧-true)
open import Decide using (T-to; T⇒≡true; ∧-intro; ≤ᵇ-widen)

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
... | just (flatten-st _ _ _ _)   | _ = E , ≤-refl , inv , refl , refl
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
takeVals-B {s = s} B Ψ k vals h = takeVals-all (valB? B Ψ s) k vals h

-- the sweep is a filter on the fn-cap face too (mirror of
-- sweepLive-bounded)
sweepLive-fnCap : ∀ {n} {Γ : Ctx n} {t} (Ψ : ℕ)
  (reg : List (RegId × Source × Chain Γ t)) (ls : List (LiveSource Γ)) →
  all (fnCapLive Ψ) ls ≡ true →
  all (fnCapLive Ψ) (sweepLive reg ls) ≡ true
sweepLive-fnCap Ψ = sweepLive-all (fnCapLive Ψ)

-- the cut is a filter on the registry: the count only drops (that half
-- is cutThrough-len, in .Measures, since the caps face needs it too),
-- the survivors keep their frame bounds, and every close it mints is
-- value-free
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
... | just (flatten-st _ _ _ _)    = E , ≤-refl , inv , refl , refl
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

-- the flatten counter bump.  IT MOVES THE COUNTER AND LEAVES THE
-- QUEUE, so the node written is bounded by whatever bounded the node
-- read — which the lookup hands over, and is no longer `refl` now that
-- one constructor carries both
flattenBump-INV : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ψ B : ℕ)
  (nid : NodeId) (d : Bool) (sched : Sched Γ) (st : EvalSt e) →
  INV? Ψ B sched st ≡ true →
  INV? Ψ B sched (record st { nodes = flattenBump nid d (EvalSt.nodes st) }) ≡ true
flattenBump-INV Ψ B nid d sched st inv
  with lookupNode nid (EvalSt.nodes st)
     | lookupNode-B B Ψ nid (EvalSt.nodes st)
         (stB-nodes B sched st (proj₁ (INV-parts Ψ B sched st inv)))
         (fcB-nodes Ψ sched st (proj₁ (proj₂ (INV-parts Ψ B sched st inv))))
... | just (flatten-st lim k q od) | nb =
      install-INV Ψ B sched st nid
        (flatten-st lim (if d then k else suc k) q od)
        (proj₁ nb) (proj₂ nb) inv
... | nothing                | _ = inv
... | just (scan-st _)       | _ = inv
... | just (take-st _)       | _ = inv
... | just (switch-st _ _)   | _ = inv
... | just (exhaust-st _ _)  | _ = inv

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
-- done-flag is written back (and flatten's queue is re-installed as-is)
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
thruWrap-wet Ψ B flattenᵒ nid true vs bs sched st inv vB bB
  with lookupNode nid (EvalSt.nodes st)
     | lookupNode-B B Ψ nid (EvalSt.nodes st)
         (stB-nodes B sched st (proj₁ (INV-parts Ψ B sched st inv)))
         (fcB-nodes Ψ sched st (proj₁ (proj₂ (INV-parts Ψ B sched st inv))))
... | just (flatten-st lim act q _) | nb =
      install-INV Ψ B sched st nid (flatten-st lim act q true)
        (proj₁ nb) (proj₂ nb) inv , vB , bB
... | nothing                | _ = inv , vB , bB
... | just (scan-st _)       | _ = inv , vB , bB
... | just (take-st _)       | _ = inv , vB , bB
... | just (switch-st _ _)   | _ = inv , vB , bB
... | just (exhaust-st _ _)  | _ = inv , vB , bB
thruWrap-wet Ψ B switchᵒ nid true vs bs sched st inv vB bB
  with lookupNode nid (EvalSt.nodes st)
... | just (switch-st cur _) =
      install-INV Ψ B sched st nid (switch-st cur true) refl refl inv , vB , bB
... | nothing                = inv , vB , bB
... | just (scan-st _)       = inv , vB , bB
... | just (take-st _)       = inv , vB , bB
... | just (flatten-st _ _ _ _)    = inv , vB , bB
... | just (exhaust-st _ _)  = inv , vB , bB
thruWrap-wet Ψ B exhaustᵒ nid true vs bs sched st inv vB bB
  with lookupNode nid (EvalSt.nodes st)
... | just (exhaust-st act _) =
      install-INV Ψ B sched st nid (exhaust-st act true) refl refl inv , vB , bB
... | nothing                = inv , vB , bB
... | just (scan-st _)       = inv , vB , bB
... | just (take-st _)       = inv , vB , bB
... | just (flatten-st _ _ _ _)    = inv , vB , bB
... | just (switch-st _ _)   = inv , vB , bB
