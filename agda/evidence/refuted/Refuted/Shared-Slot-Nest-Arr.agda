-- ══════════════════════════════════════════════════════════════════
-- THE ARR-KEYED GRANT IS ADDITIVE AT A SLOT, AND A SHARED DEFINITION
-- CAN DOUBLE.  So the slot arm of the arrival-keyed walk is FALSE.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE`
-- notes.
--
-- WHAT THE STATEMENT SAID.  The arrival-keyed walk grants
-- `arrD U B m = 2 ^ pred m * (U + B)` at an arrival of synchronous size
-- `m`.  A slot reference has size one, so at a slot the exponent is
-- `2 ^ 0` and the whole grant collapses to `U + B` -- purely additive.
-- The reading that made that look safe: `nestUnit` charges a shared
-- slot exactly `nestDᵉ` of its definition, so a slot whose definition
-- is deep is paid for by the unit.
--
-- WHERE IT BREAKS.  It is paid for only if subscribing the definition
-- hands back what the definition MEASURES.  A substituting step does
-- not: the value it emits is BUILT, one occurrence in the step function
-- and one in the source it maps over, so a subscribe doubles per layer
-- while `nestDᵉ` -- a subterm measure -- rises by one.  Both columns are
-- pinned below, at the same four programs: delivered `1 2 4 8` against
-- a grant of `2 3 4 5`.  The third row is where they cross and the
-- fourth is where the claim is dead.
--
-- AND `B` IS NOT A WAY OUT, WHICH IS WHY THIS IS THE STATEMENT'S
-- PROBLEM AND NOT THE WITNESS'S.  `B` is bounded below by the caller's
-- own premise `nestDᵉ o ≤ B`, and `nestDᵉ (input i)` is ZERO -- by
-- definition and correctly, since the syntax of a slot reference says
-- nothing about the slot.  So `B = 0` is exactly what the head hands
-- down, and it is the instantiation below.  Raising `B` cannot be the
-- repair either: the deficit doubles with the layer count while
-- anything the caller could offer is a fixed term of the arrival.
--
-- WHAT THIS DOES NOT KILL.  The DEEP family, whose layers are
-- contained rather than substituted, reads `0 1 2 3` against the same
-- `2 3 4 5` -- inside the grant with a margin of two throughout.  So
-- the additive form is right about containment and wrong about
-- substitution, and the repair is a factor keyed on the DEFINITION's
-- synchronous size rather than on the arrival's, which at a slot is
-- one.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Shared-Slot-Nest-Arr where

open import Data.Bool using (T; true)
open import Data.Empty using (⊥)
open import Data.Fin using () renaming (zero to fzero)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_)
open import Data.Nat.Properties using (≤⇒≤ᵇ)
open import Data.Product using (proj₁)
open import Data.Unit using (tt)
open import Data.Vec using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Rx.Prim using (Gas; g0; gs)
open import Rx.Exp
  using (Ctx; Closed; Val; Fn; natᵗ; obs; ofᵉ; mapᵉ; mergeAllᵉ; nat̂;
         strmᵗ; varᵗ; caseᵗ; inlᵗ; input; inputsBelowᵉ; syncSizeᵉ)
open import Rx.Nest-Depth using (nestDᵉ)
open import Rx.Slots using (Slots; shared)
open import Rx.Evaluator
  using (subscribeE; subscribeSharedSlot; splitBurst; root; sched-init; st-init; Path; _↠_;
  thru-outer; mergeAllᵒ)
open import Verify-Budget-Sufficient.Caps using (Caps; caps)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (nestValOK?)
open import Verify-Budget-Sufficient.Nest-Cap using (arrD)
open import Verify-Budget-Sufficient.Nest-Store using (nestUnit)
open import Verify-Budget-Sufficient.Nest-Walk
  using (nestDᵛˢ; nestCapsOK?)

-- an OBSERVABLE-typed slot, which is the only kind with depth to hand
-- back: a data-typed one delivers values `nestDᵛ` reads as zero
Γₛ : Ctx 1
Γₛ = obs natᵗ ∷ []

gasBig : Gas
gasBig = gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs g0)))))))))))))))

prog : Closed Γₛ natᵗ
prog = ofᵉ (nat̂ 0 ∷ [])

----------------------------------------------------------------------
-- THE TWO DEFINITIONS A SHARED SLOT CAN HOLD
----------------------------------------------------------------------

-- CONTAINED: every layer is a subterm of the one above it
deep : ℕ → Closed Γₛ natᵗ
deep zero    = ofᵉ (nat̂ 0 ∷ [])
deep (suc k) = mergeAllᵉ nothing (ofᵉ (strmᵗ (deep k) ∷ []))

dDeep : ℕ → Closed Γₛ (obs natᵗ)
dDeep k = ofᵉ (strmᵗ (deep k) ∷ [])

-- SUBSTITUTED: the payload lands in the step function AND in the source
-- it maps over, so one application doubles what is emitted
dup : Fn Γₛ [] [] [] (obs natᵗ) (obs natᵗ)
dup = strmᵗ (mapᵉ
        (caseᵗ (inlᵗ (varᵗ (there (here refl)))) (nat̂ 0) (varᵗ (here refl)))
        (ofᵉ (varᵗ (here refl) ∷ [])))

dDup : ℕ → Closed Γₛ (obs natᵗ)
dDup zero    = ofᵉ (strmᵗ (mergeAllᵉ nothing
                 (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ []))) ∷ [])
dDup (suc k) = mapᵉ dup (mergeAllᵉ nothing (ofᵉ (strmᵗ (dDup k) ∷ [])))

----------------------------------------------------------------------
-- THE RUN, at the head's own shape
----------------------------------------------------------------------

-- `inputsBelowᵉ` does not reduce at a variable depth, so the readings
-- are taken of a DEFINITION and each row supplies its own `tt`
sl : (d : Closed Γₛ (obs natᵗ)) → T (inputsBelowᵉ 0 d) → Slots Γₛ
sl d ok fzero = shared d {ok = ok}

κ : Path Γₛ (obs natᵗ) natᵗ
κ = thru-outer mergeAllᵒ 0 ↠ root

runOf : (d : Closed Γₛ (obs natᵗ)) (ok : T (inputsBelowᵉ 0 d)) → _
runOf d ok = subscribeSharedSlot gasBig fzero d κ 0 0
               (sched-init prog (sl d ok)) (st-init prog)

burstOf : (d : Closed Γₛ (obs natᵗ)) (ok : T (inputsBelowᵉ 0 d)) → ℕ
burstOf d ok =
  nestDᵛˢ (proj₁ (splitBurst {A = Val Γₛ natᵗ} (proj₁ (runOf d ok))))

-- the grant the arm gives, at the `B` the head hands down
GOf : (d : Closed Γₛ (obs natᵗ)) (ok : T (inputsBelowᵉ 0 d)) → ℕ
GOf d ok = arrD (nestUnit prog (sl d ok)) 0 1

----------------------------------------------------------------------
-- `B = 0` IS WHAT THE HEAD SUPPLIES, so the row is not a corner
----------------------------------------------------------------------

arrTerm : Closed Γₛ (obs natᵗ)
arrTerm = input fzero

arrival≡0 : nestDᵉ arrTerm ≡ 0
arrival≡0 = refl

----------------------------------------------------------------------
-- THE PREMISE THAT COULD HAVE MADE THIS VACUOUS, discharged by `refl`
----------------------------------------------------------------------

c₀ : Caps
c₀ = caps 4096 4096 4096

capsPin : nestCapsOK? c₀ (sched-init prog (sl (dDup 3) tt)) (st-init prog)
            ≡ true
capsPin = refl

----------------------------------------------------------------------
-- THE TWO COLUMNS, packed base 100 so one row carries the shape
----------------------------------------------------------------------

-- delivered `0 1 2 3`, granted `2 3 4 5` -- containment is inside
contained : ℕ
contained = burstOf (dDeep 0) tt + 100 * burstOf (dDeep 1) tt
          + 10000 * burstOf (dDeep 2) tt + 1000000 * burstOf (dDeep 3) tt
          + 100000000 * (GOf (dDeep 0) tt + 100 * GOf (dDeep 1) tt
                       + 10000 * GOf (dDeep 2) tt + 1000000 * GOf (dDeep 3) tt)

contained≡ : contained ≡ 403020103020100
contained≡ = refl

-- delivered `1 2 4 8`, granted `2 3 4 5` -- substitution crosses
substituted : ℕ
substituted = burstOf (dDup 0) tt + 100 * burstOf (dDup 1) tt
            + 10000 * burstOf (dDup 2) tt + 1000000 * burstOf (dDup 3) tt
            + 100000000 * (GOf (dDup 0) tt + 100 * GOf (dDup 1) tt
                         + 10000 * GOf (dDup 2) tt + 1000000 * GOf (dDup 3) tt)

substituted≡ : substituted ≡ 504030208040201
substituted≡ = refl

----------------------------------------------------------------------
-- AND THE CONJUNCT ITSELF, at the fourth row
----------------------------------------------------------------------

delivered≡8 : burstOf (dDup 3) tt ≡ 8
delivered≡8 = refl

granted≡5 : GOf (dDup 3) tt ≡ 5
granted≡5 = refl

sharedSlot-nest-arr-absurd :
  burstOf (dDup 3) tt ≤ GOf (dDup 3) tt → ⊥
sharedSlot-nest-arr-absurd h =
  ≤⇒≤ᵇ (subst (λ z → burstOf (dDup 3) tt ≤ z) granted≡5 h)

----------------------------------------------------------------------
-- AND THE HEAD ABOVE IT READS THE SAME, which is what makes this a
-- finding about the WALK and not only about the arm it delegates to.
-- The slot clause is a direct call, so nothing between the two can
-- absorb the difference -- and the head's own key is the arrival's
-- synchronous size, which at a slot reference is one.
----------------------------------------------------------------------

headRun : _
headRun = subscribeE gasBig arrTerm κ 0 0
            (sched-init prog (sl (dDup 3) tt)) (st-init prog)

headBurst : ℕ
headBurst = nestDᵛˢ (proj₁ (splitBurst {A = Val Γₛ natᵗ} (proj₁ headRun)))

headValPin : nestValOK? c₀ (obs (obs natᵗ)) arrTerm ≡ true
headValPin = refl

packHead : ℕ
packHead = headBurst + 100 * syncSizeᵉ arrTerm
         + 10000 * nestUnit prog (sl (dDup 3) tt)

-- delivered 8, key 1, unit 5
packHead≡ : packHead ≡ 50108
packHead≡ = refl

headGrant : ℕ
headGrant = arrD (nestUnit prog (sl (dDup 3) tt)) 0 (syncSizeᵉ arrTerm)

headGrant≡5 : headGrant ≡ 5
headGrant≡5 = refl

nest-arr-at-slot-absurd : headBurst ≤ headGrant → ⊥
nest-arr-at-slot-absurd h =
  ≤⇒≤ᵇ (subst (λ z → headBurst ≤ z) headGrant≡5 h)
