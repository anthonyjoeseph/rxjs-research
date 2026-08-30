-- ══════════════════════════════════════════════════════════════════
-- A SUBSCRIBE DOES NOT PRESERVE THE REGISTRY'S PRICING ON ITS OWN, and
-- what kills it is the INNER OBSERVABLE, which no hypothesis mentions.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHAT THE STATEMENT SAID.  `subscribeInner` takes a registry priced
-- under the base cap to a registry priced under the base cap, given
-- only two facts about the CONTINUATION κ: that it is one shorter than
-- the cap admits, and that its own frames are priced.
--
-- WHY IT LOOKED RIGHT.  Between a frame head and a registration there
-- is nothing but nodes updates, and the path a subscribe registers is
-- the walked path with its head swapped -- same length, different
-- frame.  Read at the IMMEDIATE registration that is exactly true, and
-- the two κ hypotheses are precisely what pays for it.
--
-- WHERE IT BREAKS.  A subscribe does not stop at the immediate
-- registration.  `Val Γ (obs u)` IS a closed expression, so the inner
-- observable is a runtime value structurally unrelated to the program
-- the cap is computed from -- and `subscribeE` pushes one frame per
-- syntax node of it before it reaches a leaf.  A `mapᵉ` whose step
-- function is larger than the whole cap registers a chain whose head
-- fails `frameSz?` outright, and nothing in the hypotheses can see the
-- inner at all.
--
-- THE WITNESS IS SYMBOLIC, WHICH IS STRONGER THAN A ROW HERE.  The cap
-- is `iterSize` at a count the caps counting family produces, a number
-- no probe can evaluate, so a numeric crossing is out of reach in both
-- directions.  Instead the counterexample is built FROM the cap: a step
-- function of size `3 · (S + 1) + 1` against a cap of `S`, for whatever
-- `S` the program fixes.  The gap is therefore unbounded and no repair
-- that merely enlarges the cap can move it.
--
-- WHAT DIES AND WHAT DOES NOT.  The form with no hypothesis on the
-- inner dies outright, and so does the drain's form, which reaches
-- `subscribeInner` on a queue element the same way.  What survives is
-- the claim about the inners a RUN presents: those are read out of a
-- state the caps invariant already bounds, and the reading is
-- `nestClosOK?` -- the closure size against the cap.  So the repair is
-- to take that reading as a premise, which is a restatement the
-- refutation licenses rather than a hypothesis the call site happens
-- to supply.  What it does NOT settle is the CAP the reading may be
-- taken at: the frame face carries it at the STEPPED cap and the
-- registry is priced at the BASE one, and widening runs the wrong way.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Subscribe-Inner-Regs-Base where

open import Data.Bool using (Bool; true; false; T)
open import Data.Empty using (⊥)
open import Data.List using ([])
open import Data.Nat using (ℕ; zero; suc; _≤_; _≤ᵇ_; s≤s; z≤n)
open import Data.Nat.Properties using (≤ᵇ⇒≤; ≤⇒≤ᵇ; ≤-trans; n≤1+n; m≤m+n; 1+n≰n)
open import Data.Product using (proj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Data.Fin using () renaming (zero to fzero)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Rx.Prim using (Gas; gs; g0; hot; Tick; Id)
open import Rx.Exp using (Ctx; Closed; Val; natᵗ; obs; Fn; input; mapᵉ; varᵗ; nat̂; pairᵗ; primᵗ; add; sizeᵗ)
open import Rx.Slots using (Slots; scripted)
open import Rx.Evaluator using (Sched; EvalSt; NodeId; AllOp; mergeAllᵒ;
  Path; root; subscribeInner; sched-init; st-init)
open import Decide using (T⇒≡true)
open import Verify-Budget-Sufficient.Measures using (pathLen)
open import Verify-Budget-Sufficient.Caps using (Caps; capsAt; 2≤capsAt-size)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (pathSz?; regsSz?)

----------------------------------------------------------------------
-- THE STATEMENT, WRITTEN OUT RATHER THAN IMPORTED.  Importing the
-- postulate would prove the tower inconsistent instead of refuting
-- anything.
----------------------------------------------------------------------
SubscribeInnerRegsBase : Set
SubscribeInnerRegsBase = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sl : Slots Γ) (id : ℕ) (fuel : Gas) (op : AllOp) (allNid : NodeId)
  (κ : Path Γ u t) (nid : Id) (now : Tick) (o : Val Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) →
  regsSz? (Caps.cSize (capsAt e sl id)) (EvalSt.registry st) ≡ true →
  (suc (pathLen κ) ≤ᵇ Caps.cSize (capsAt e sl id)) ≡ true →
  pathSz? (Caps.cSize (capsAt e sl id)) κ ≡ true →
  regsSz? (Caps.cSize (capsAt e sl id))
    (EvalSt.registry (proj₂ (proj₂ (proj₂ (proj₂ (proj₂
      (subscribeInner fuel op allNid κ nid now o sched st)))))))
    ≡ true

----------------------------------------------------------------------
-- ONE SLOT, HOT AND UNSPENT, so the leaf actually REGISTERS -- which is
-- the only thing the program has to do.  The cap is read off it and the
-- witness is then built to beat that cap.
----------------------------------------------------------------------
Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

sl₁ : Slots Γ₁
sl₁ fzero = scripted (hot [])

e₁ : Closed Γ₁ natᵗ
e₁ = input fzero

S : ℕ
S = Caps.cSize (capsAt e₁ sl₁ 0)

-- three syntax nodes per unit, so the size is linear in the parameter
-- and the parameter is the cap
big : ℕ → Fn Γ₁ [] [] [] natᵗ natᵗ
big zero    = varᵗ (here refl)
big (suc d) = primᵗ add (pairᵗ (big d) (nat̂ 0))

big-size : ∀ (d : ℕ) → suc d ≤ sizeᵗ (big d)
big-size zero    = s≤s z≤n
big-size (suc d) =
  s≤s (s≤s (≤-trans (≤-trans (n≤1+n d) (big-size d)) (m≤m+n (sizeᵗ (big d)) 1)))

o₁ : Val Γ₁ (obs natᵗ)
o₁ = mapᵉ (big (suc S)) (input fzero)

row : Bool
row = regsSz? S (EvalSt.registry (proj₂ (proj₂ (proj₂ (proj₂ (proj₂
        (subscribeInner {e = e₁} (gs (gs (gs g0))) mergeAllᵒ 0 root 0 0 o₁
                        (sched-init e₁ sl₁) (st-init e₁))))))))

subscribeInner-regs-base-absurd : SubscribeInnerRegsBase → ⊥
subscribeInner-regs-base-absurd pr =
  1+n≰n (≤-trans (n≤1+n (suc S)) (≤-trans (big-size (suc S))
                                          (≤ᵇ⇒≤ (sizeᵗ (big (suc S))) S (subst T (sym conj) tt))))
  where
  h : row ≡ true
  h = pr sl₁ 0 (gs (gs (gs g0))) mergeAllᵒ 0 root 0 0 o₁
         (sched-init e₁ sl₁) (st-init e₁)
         refl
         (T⇒≡true _ (≤⇒≤ᵇ (≤-trans (s≤s z≤n) (2≤capsAt-size e₁ sl₁ 0))))
         refl
  conj : (sizeᵗ (big (suc S)) ≤ᵇ S) ≡ true
  conj with sizeᵗ (big (suc S)) ≤ᵇ S | h
  ... | true  | _  = refl
  ... | false | ()
