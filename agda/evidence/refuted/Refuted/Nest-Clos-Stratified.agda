-- ══════════════════════════════════════════════════════════════════
-- THE TELESCOPE DOUBLES PER STAGE WHILE THE PREMISE PRICES ONE SLOT
-- AT A TIME, so a LEVELLED cap does not pay for the closure reading
-- either -- which is the escape the fixed-ratio families left open.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree may not import the statement it refutes: the proposition is
-- written out again here, so `src` may move its own copy freely and
-- this file goes red the day the two stop agreeing.
--
-- WHAT THE STATEMENT SAID.  A `defer` parks its own body, and the
-- subscribe face holds that body's WRITTEN size under the frame's cap;
-- the parked body then satisfies the closure reading one frame level
-- up, where a level multiplies the cap by the base size and doubles.
--
-- WHY IT LOOKED RIGHT.  The two families that killed the FLAT reading
-- both sit at a FIXED ratio -- three of syntax to nine of closure, a
-- constant deficit per reference -- and one frame level buys a factor
-- of twice the base size, which pays for any constant whatever.  So
-- moving the reading up a level looked like the whole repair.
--
-- WHERE IT BREAKS.  The premise prices each slot SEPARATELY: a
-- stratified telescope may hold six definitions of seven symbols each,
-- and `slotsCaps?` is satisfied at a cap of seven.  But slot `k` names
-- slot `k-1` TWICE, so the staged reading doubles at every stage while
-- the premise never moves -- six stages read two hundred and eighteen
-- against a cap of seven, and a level takes that cap only to a hundred
-- and five.  The ratio here is not a constant to be bought: it is
-- exponential in the slot count, and the slot count is not a quantity
-- any level of the frame mentions.
--
-- WHAT DIES.  Reading the closure key off a WRITTEN-SIZE receipt at
-- any FIXED number of levels, which is the last form the derivation
-- could have taken.  What survives is unchanged: a closure bound must
-- be carried, and what carries it has to be denominated in the
-- telescope rather than in the size cap.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Nest-Clos-Stratified where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.Fin using (#_) renaming (zero to fzero; suc to fsuc)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; suc; _≤_; s≤s; z≤n)
open import Data.Unit using (tt)
open import Data.Vec using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Rx.Exp
  using (Ctx; Closed; Val; natᵗ; obs; ofᵉ; strmᵗ; input; mergeAllᵉ; sizeᵉ)
open import Rx.Prim using (cold)
open import Rx.Slots using (Slots; scripted; shared)
open import Verify-Budget-Sufficient.Caps using (Caps; caps; frameStep)
open import Verify-Budget-Sufficient.Caps-Face.Part1
  using (nestClosOK?; slotsCaps?)

----------------------------------------------------------------------
-- THE TELESCOPE: six stages, each naming the one below it twice
----------------------------------------------------------------------

Γ : Ctx 6
Γ = natᵗ ∷ natᵗ ∷ natᵗ ∷ natᵗ ∷ natᵗ ∷ natᵗ ∷ []

-- seven symbols written; two references read
two : Closed Γ natᵗ → Closed Γ natᵗ
two x = mergeAllᵉ nothing (ofᵉ (strmᵗ x ∷ strmᵗ x ∷ []))

sl : Slots Γ
sl fzero                                        = scripted {ok = tt} (cold [] [])
sl (fsuc fzero)                                 = shared (two (input (# 0))) {ok = tt}
sl (fsuc (fsuc fzero))                          = shared (two (input (# 1))) {ok = tt}
sl (fsuc (fsuc (fsuc fzero)))                   = shared (two (input (# 2))) {ok = tt}
sl (fsuc (fsuc (fsuc (fsuc fzero))))            = shared (two (input (# 3))) {ok = tt}
sl (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))     = shared (two (input (# 4))) {ok = tt}

-- the parked body: one symbol of syntax, the whole telescope of closure
o : Val Γ (obs natᵗ)
o = input (# 5)

c : Caps
c = caps 7 1000 1

----------------------------------------------------------------------
-- THE NUMBERS, every one of them by computation
----------------------------------------------------------------------

slots-priced : slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true
slots-priced = refl

size≡1 : sizeᵉ o ≡ 1
size≡1 = refl

-- one level takes the cap of seven to a hundred and five
lvl≡105 : Caps.cSize (frameStep 1 c) ≡ 105
lvl≡105 = refl

-- and the six stages read two hundred and eighteen
read-fails : nestClosOK? (frameStep 1 c) sl o ≡ false
read-fails = refl

----------------------------------------------------------------------
-- THE STATEMENT, verbatim
----------------------------------------------------------------------

DeferParkClos : Set
DeferParkClos = ∀ {n} {Γ′ : Ctx n} {u} (c′ : Caps) (j : ℕ) (s : Slots Γ′)
  (v : Val Γ′ (obs u)) →
  2 ≤ Caps.cSize c′ →
  slotsCaps? (Caps.cSize c′) (Caps.cWid c′) s ≡ true →
  sizeᵉ v ≤ Caps.cSize (frameStep j c′) →
  nestClosOK? (frameStep (suc j) c′) s v ≡ true

false≢true : false ≡ true → ⊥
false≢true ()

nest-clos-stratified-absurd : DeferParkClos → ⊥
nest-clos-stratified-absurd f =
  false≢true (trans (sym read-fails)
                     (f {Γ′ = Γ} c 0 sl o (s≤s (s≤s z≤n)) slots-priced (s≤s z≤n)))
