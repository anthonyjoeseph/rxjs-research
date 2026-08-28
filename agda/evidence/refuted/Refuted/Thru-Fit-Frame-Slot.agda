-- ══════════════════════════════════════════════════════════════════
-- THE OUTER WRAP'S FIT PRICES THE ARRIVAL AND NOT THE SLOT IT NAMES,
-- so `thruFit-frame` is FALSE.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE`
-- notes.
--
-- WHAT THE STATEMENT SAID.  A `thru-outer` frame subscribes each
-- observable handed to it, and the fit grants every value the
-- subscription hands back `nestFac S W * ((nodesMax st ⊔ nestDᵛˢ vals)
-- + W)` -- a tower in the SIZE cap, times the store the frame was
-- entered at.  Every term of that is read off the arrival or off the
-- state.
--
-- WHERE IT BREAKS, AND IT IS NOT THE AXIS THE HEADER RULED OUT.  A
-- slot reference is an arrival that names its content instead of
-- carrying it: `sizeᵉ (input i) ≡ 1` and `nestDᵉ (input i) ≡ 0`, both
-- by definition and both correct, since the syntax of a reference says
-- nothing about the slot.  So EVERY term of the grant is pinned at its
-- floor by the arrival itself -- the cap `valCaps?` admits is one, the
-- store term is zero -- and the grant is the constant four whatever
-- the slot holds.  Meanwhile subscribing the slot runs its definition,
-- and a substituting step doubles per layer.  Four rows are pinned
-- below: delivered `1 2 4 8` against a grant that does not move.
--
-- WHY NO CAP CAN ABSORB IT.  `capsOK?` bounds the live pendings, the
-- node stores and the registry paths, and slot definitions are
-- deliberately none of those -- they are fixed syntax, so the
-- predicate has no clause for them.  The width cap does read the
-- telescope, but the grant does not read the width.  So the deficit
-- doubles with the layer count while every quantity the statement
-- names stands still, which is a divergence and not a crossing: no
-- row is where the two sides meet, because they never do.
--
-- WHAT THE REPAIR HAS TO CARRY.  The measure of a slot telescope
-- already exists and the rest of this face spends it -- the nest
-- walk's own grants carry a `nestU … (nestUnit e sl)` term for exactly
-- this reason.  This head is the one that does not, and a factor keyed
-- on the arrival cannot stand in for it, since at a slot that key is
-- one by construction.
--
-- WHAT THIS DOES NOT KILL.  The CONTAINED family, whose layers are
-- subterms rather than substitutions, is not what makes the reading
-- fail: a definition the arrival cannot see is unpaid whether or not
-- its depth doubles, and doubling is only what makes the gap
-- unbounded rather than merely positive.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Thru-Fit-Frame-Slot where

open import Data.Bool using (T; true; false)
open import Data.Empty using (⊥)
open import Data.Fin using () renaming (zero to fzero)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (nothing)
open import Data.Bool.ListAction using (all)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _⊔_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤⇒≤ᵇ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Vec using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)

open import Rx.Prim using (Gas; g0; gasPad)
open import Rx.Exp
  using (Ctx; Closed; Val; Fn; natᵗ; obs; ofᵉ; mapᵉ; mergeAllᵉ; nat̂;
         strmᵗ; varᵗ; caseᵗ; inlᵗ; input; inputsBelowᵉ)
open import Rx.Nest-Depth using (nestDᵉ)
open import Rx.Slots using (Slots; shared)
open import Rx.Evaluator
  using (Sched; EvalSt; Path; Frame; root; _↠_; thru-outer; mergeAllᵒ;
         mergeAll-st; thruConsume; stepFrame; installNode; sched-init; st-init)
open import Verify-Budget-Sufficient.Caps using (Caps; caps)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (capsOK?; valCaps?)
open import Verify-Budget-Sufficient.Nest-Cap using (nestFac; nestFac-def)
open import Verify-Budget-Sufficient.Nest-Store using (nestUnit)
open import Verify-Budget-Sufficient.Nest-Walk
  using (nodesMax; nestDᵛˢ; thruFitOK)

-- an OBSERVABLE-typed slot, which is the only kind with depth to hand
-- back, and necessarily a `shared` one: scripted slots carry data only
Γₛ : Ctx 1
Γₛ = obs natᵗ ∷ []

gas : Gas
gas = gasPad 400 g0

prog : Closed Γₛ natᵗ
prog = ofᵉ (nat̂ 0 ∷ [])

-- the payload lands in the step function AND in the source it maps
-- over, so one application doubles what is emitted
dup : Fn Γₛ [] [] [] (obs natᵗ) (obs natᵗ)
dup = strmᵗ (mapᵉ
        (caseᵗ (inlᵗ (varᵗ (there (here refl)))) (nat̂ 0) (varᵗ (here refl)))
        (ofᵉ (varᵗ (here refl) ∷ [])))

dDup : ℕ → Closed Γₛ (obs natᵗ)
dDup zero    = ofᵉ (strmᵗ (mergeAllᵉ nothing
                 (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ []))) ∷ [])
dDup (suc k) = mapᵉ dup (mergeAllᵉ nothing (ofᵉ (strmᵗ (dDup k) ∷ [])))

-- `inputsBelowᵉ` does not reduce at a variable depth, so the readings
-- are taken of a DEFINITION and each row supplies its own `tt`
sl : (d : Closed Γₛ (obs natᵗ)) → T (inputsBelowᵉ 0 d) → Slots Γₛ
sl d ok fzero = shared d {ok = ok}

sched : (d : Closed Γₛ (obs natᵗ)) → T (inputsBelowᵉ 0 d) → Sched Γₛ
sched d ok = sched-init prog (sl d ok)

κ : Path Γₛ (obs natᵗ) natᵗ
κ = thru-outer mergeAllᵒ 0 ↠ root

st₀ : EvalSt prog
st₀ = installNode 0 (mergeAll-st {t = obs natᵗ} nothing 0 [] false) (st-init prog)

arrTerm : Val Γₛ (obs (obs natᵗ))
arrTerm = input fzero

vals : List (Val Γₛ (obs (obs natᵗ)))
vals = arrTerm ∷ []

W : ℕ
W = 1

-- the size cap is the arrival's own, which is the smallest `valCaps?`
-- admits; the width and registry caps are given room, which only makes
-- the premises easier and the refutation stronger
cap : Caps
cap = caps 1 4096 4096

G : ℕ
G = nestFac (Caps.cSize cap) W * ((nodesMax st₀ ⊔ nestDᵛˢ vals) + W)

deliveredOf : (d : Closed Γₛ (obs natᵗ)) → T (inputsBelowᵉ 0 d) → ℕ
deliveredOf d ok =
  nestDᵛˢ (proj₁ (thruConsume gas mergeAllᵒ 0 κ 0 0 arrTerm (sched d ok) st₀))

----------------------------------------------------------------------
-- THE ARRIVAL PINS EVERY TERM OF THE GRANT AT ITS FLOOR
----------------------------------------------------------------------

arrival-nest≡0 : nestDᵉ arrTerm ≡ 0
arrival-nest≡0 = refl

store≡0 : (nodesMax st₀ ⊔ nestDᵛˢ vals) ≡ 0
store≡0 = refl

G≡4 : G ≡ 4
G≡4 = cong (λ z → z * ((nodesMax st₀ ⊔ nestDᵛˢ vals) + W))
        (nestFac-def (Caps.cSize cap) W)

----------------------------------------------------------------------
-- THE PREMISES, discharged by `refl` at the fourth row
----------------------------------------------------------------------

premises : (Sched.slots (sched (dDup 3) tt) ≡ sl (dDup 3) tt)
         × (length vals ≤ W)
         × (capsOK? cap (sched (dDup 3) tt) st₀ ≡ true)
         × (all (valCaps? cap (sl (dDup 3) tt) (obs (obs natᵗ))) vals ≡ true)
premises = refl , s≤s z≤n , refl , refl

----------------------------------------------------------------------
-- THE COLUMN: delivered `1 2 4 8` against a grant that does not move
----------------------------------------------------------------------

delivered : ℕ
delivered = deliveredOf (dDup 0) tt + 100 * deliveredOf (dDup 1) tt
          + 10000 * deliveredOf (dDup 2) tt + 1000000 * deliveredOf (dDup 3) tt

delivered≡ : delivered ≡ 8040201
delivered≡ = refl

delivered₃≡8 : deliveredOf (dDup 3) tt ≡ 8
delivered₃≡8 = refl

thruFit-frame-slot-absurd :
  thruFitOK G gas mergeAllᵒ 0 κ 0 0 vals (sched (dDup 3) tt) st₀ → ⊥
thruFit-frame-slot-absurd fit =
  ≤⇒≤ᵇ (subst (λ z → deliveredOf (dDup 3) tt ≤ z) G≡4 (proj₁ fit))

----------------------------------------------------------------------
-- THE SAME ROW KILLS THE FRAME HEAD, WHICH IS A DEFINITION
----------------------------------------------------------------------

frame : Frame Γₛ (obs (obs natᵗ)) (obs natᵗ)
frame = thru-outer mergeAllᵒ 0

runOf : (d : Closed Γₛ (obs natᵗ)) → T (inputsBelowᵉ 0 d) → _
runOf d ok = stepFrame gas 0 0 frame κ vals false (sched d ok) st₀

grownOf : (d : Closed Γₛ (obs natᵗ)) → T (inputsBelowᵉ 0 d) → ℕ
grownOf d ok =
  nodesMax (proj₂ (proj₂ (proj₂ (proj₂ (runOf d ok))))) ⊔ nestDᵛˢ (proj₁ (runOf d ok))

-- the head's own burst premise, which a refutation has to meet
lenOf : (d : Closed Γₛ (obs natᵗ)) → T (inputsBelowᵉ 0 d) → ℕ
lenOf d ok = length (proj₁ (runOf d ok))

len₃≡1 : lenOf (dDup 3) tt ≡ 1
len₃≡1 = refl

grown₃≡8 : grownOf (dDup 3) tt ≡ 8
grown₃≡8 = refl

stepFrame-nodes-thru-slot-absurd : grownOf (dDup 3) tt ≤ G → ⊥
stepFrame-nodes-thru-slot-absurd h =
  ≤⇒≤ᵇ (subst (λ z → grownOf (dDup 3) tt ≤ z) G≡4 h)

----------------------------------------------------------------------
-- AND THE UNIT ITS PARENT ADDS DOES NOT SAVE IT, one layer further on.
-- `parentGrant` is `stepFrame-nodes`'s own right-hand side at this
-- frame, with the two sealed families written out from their
-- definitions -- `nestFac S W ≡ ((2 ^ S) ^ suc W) ^ S`, which the
-- module exports, and `nestU S U ≡ suc S * U`, which it does not.  The
-- telescope term is the real `nestUnit`, so the reading is of the
-- charge and not of a model of it.
----------------------------------------------------------------------

parentGrant : ℕ
parentGrant =
  ((2 ^ Caps.cSize cap) ^ suc W) ^ Caps.cSize cap
    * (1 ^ W * ((nodesMax st₀ ⊔ nestDᵛˢ vals) + W * 1)
       + suc (Caps.cSize cap) * nestUnit prog (sl (dDup 7) tt))

unit₇≡9 : nestUnit prog (sl (dDup 7) tt) ≡ 9
unit₇≡9 = refl

parentGrant≡76 : parentGrant ≡ 76
parentGrant≡76 = refl

len₇≡1 : lenOf (dDup 7) tt ≡ 1
len₇≡1 = refl

grown₇≡128 : grownOf (dDup 7) tt ≡ 128
grown₇≡128 = refl

-- ONE LAYER SHORTER AND THE PARENT HOLDS BY FOUR, so this is a
-- crossing rather than a scale error
grown₆≡64 : grownOf (dDup 6) tt ≡ 64
grown₆≡64 = refl

parentGrant₆≡68 : ((2 ^ Caps.cSize cap) ^ suc W) ^ Caps.cSize cap
    * (1 ^ W * ((nodesMax st₀ ⊔ nestDᵛˢ vals) + W * 1)
       + suc (Caps.cSize cap) * nestUnit prog (sl (dDup 6) tt))
  ≡ 68
parentGrant₆≡68 = refl

stepFrame-nodes-slot-absurd : grownOf (dDup 7) tt ≤ parentGrant → ⊥
stepFrame-nodes-slot-absurd h =
  ≤⇒≤ᵇ (subst (λ z → grownOf (dDup 7) tt ≤ z) parentGrant≡76 h)
