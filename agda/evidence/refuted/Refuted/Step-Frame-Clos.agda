-- ══════════════════════════════════════════════════════════════════
-- A FRAME DOES NOT RETURN THE CLOSURE READING IT WAS GIVEN, and the
-- thing that breaks it is the frame's OWN function, which no
-- hypothesis mentions at all.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree may not import the statement it refutes: the proposition is
-- written out again here, so `src` may move its own copy freely and
-- this file goes red the day the two stop agreeing.
--
-- WHAT THE STATEMENT SAID.  Values arriving at a frame carry a closure
-- reading at the instant's cap; the values the frame passes ON carry
-- the same reading, given only that the slots match and that the state
-- satisfies the caps predicate at some level.
--
-- WHY IT LOOKED RIGHT.  Four of the five frames do not rebuild a value
-- at all -- a take filters, an inner reaction forwards, an outer walk
-- returns what it was handed -- so the statement is an identity at
-- them, and the remaining two look like they should be paid for by the
-- caps predicate the state already satisfies.
--
-- WHERE IT BREAKS.  A `map-f` carries its own function, and the
-- function is part of the FRAME, not part of the program the cap was
-- computed from and not part of the state the caps predicate is about.
-- Nothing in the hypotheses bounds it.  So the frame may apply a
-- function whose result is an observable of any size whatever, and the
-- reading on the output is a bound on exactly that.  The witness makes
-- the point in its cheapest form: a constant function returning a
-- literal stream of `suc S` elements, where `S` is the cap itself.
--
-- AND ADDING THE MISSING BOUND DOES NOT REPAIR IT, which is the part
-- worth carrying away.  Suppose the frame's function were held under
-- the cap -- by the path pricing the caller does have.  The output is
-- then the function's body with the argument substituted in, so its
-- closure is the function's plus the argument's, and both are only
-- bounded BY the cap: the sum overflows it.  A rebuilt value's reading
-- has to be taken at a HIGHER cap, which is what the size face already
-- concluded for the same frames when it made its scan law return a
-- step rather than a bound.
--
-- THE WITNESS IS SYMBOLIC, WHICH IS STRONGER THAN A ROW HERE.  `S` is
-- never computed: the counterexample is built FROM the cap, so no
-- enlargement of the cap escapes it.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Step-Frame-Clos where

open import Data.Bool using (Bool; true; false; T)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _≤_; _≤ᵇ_; s≤s; z≤n)
open import Data.Nat.Properties using (≤ᵇ⇒≤; ≤-trans; n≤1+n; 1+n≰n)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Data.Fin using (Fin) renaming (zero to fzero)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Rx.Prim using (Gas; g0; hot; Tick; Id)
open import Rx.Exp using (Ctx; Closed; Val; Tm; natᵗ; obs; Fn; Exp;
  input; ofᵉ; nat̂; strmᵗ; subΘTms)
open import Rx.Clos-Size using (closSizeᵗˢ)
open import Rx.Slots using (Slots; scripted)
open import Rx.Slot-Clos using (slotClos)
open import Rx.Evaluator using (Sched; EvalSt; mergeAllᵒ; Path; root; _↠_; Frame; map-f; thru-outer; stepFrame; sched-init;
  st-init)
open import Verify-Budget-Sufficient.Caps using (Caps; capsAt; frameStep)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (capsOK?)
open import Verify-Budget-Sufficient.Nest-Walk using (nestClosOK?ᵛ)
open import Data.Product using (proj₁)
open import Data.Bool.ListAction using (all)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)

------------------------------------------------------------------
-- the statement, restated
------------------------------------------------------------------

StepFrameClos : Set
StepFrameClos = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (sl : Slots Γ) (id : ℕ) (L : ℕ) (sf : Gas) (nid : Id) (now : Tick)
  (f : Frame Γ s u) (p : Path Γ u t) (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (frameStep L (capsAt e sl id)) sched st ≡ true →
  all (nestClosOK?ᵛ (capsAt e sl id) sl s) vals ≡ true →
  all (nestClosOK?ᵛ (capsAt e sl id) sl u)
      (proj₁ (stepFrame sf nid now f p vals fin sched st)) ≡ true

------------------------------------------------------------------
-- the witness
------------------------------------------------------------------

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

sl₁ : Slots Γ₁
sl₁ fzero = scripted (hot [])

e₁ : Closed Γ₁ natᵗ
e₁ = input fzero

S : ℕ
S = Caps.cSize (capsAt e₁ sl₁ 0)

nats : ∀ {Θ} → ℕ → List (Tm Γ₁ [] [] Θ natᵗ)
nats zero    = []
nats (suc k) = nat̂ 0 ∷ nats k

nats-clos : ∀ (σ : Fin 1 → ℕ) (v : Val Γ₁ natᵗ) (k : ℕ) →
  suc k ≤ closSizeᵗˢ σ (subΘTms {Θsub = natᵗ ∷ []} [] (v ∷ᵃ []ᵃ) (nats k))
nats-clos σ v zero    = s≤s z≤n
nats-clos σ v (suc k) = s≤s (nats-clos σ v k)

body : Exp Γ₁ [] [] (natᵗ ∷ []) natᵗ
body = ofᵉ (nats (suc S))

fn : Fn Γ₁ [] [] [] natᵗ (obs natᵗ)
fn = strmᵗ body

step-frame-clos-absurd : StepFrameClos → ⊥
step-frame-clos-absurd pr =
  1+n≰n (≤-trans (n≤1+n (suc S))
          (≤-trans (nats-clos (slotClos sl₁) 0 (suc S))
            (≤-trans (n≤1+n _)
                     (≤ᵇ⇒≤ _ S (subst T (sym conj) tt)))))
  where
  h : all (nestClosOK?ᵛ (capsAt e₁ sl₁ 0) sl₁ (obs natᵗ))
        (proj₁ (stepFrame {e = e₁} g0 0 0 (map-f fn)
                  (thru-outer mergeAllᵒ 0 ↠ root) (0 ∷ []) false
                  (sched-init e₁ sl₁) (st-init e₁))) ≡ true
  h = pr sl₁ 0 0 g0 0 0 (map-f fn) (thru-outer mergeAllᵒ 0 ↠ root) (0 ∷ []) false
         (sched-init e₁ sl₁) (st-init e₁) refl refl refl
  conj : (suc (closSizeᵗˢ (slotClos sl₁)
           (subΘTms {Θsub = natᵗ ∷ []} [] (0 ∷ᵃ []ᵃ) (nats (suc S)))) ≤ᵇ S) ≡ true
  conj with suc (closSizeᵗˢ (slotClos sl₁)
                  (subΘTms {Θsub = natᵗ ∷ []} [] (0 ∷ᵃ []ᵃ) (nats (suc S)))) ≤ᵇ S | h
  ... | true  | _  = refl
  ... | false | ()
