-- ══════════════════════════════════════════════════════════════════
-- A CHAIN'S STEP DOES ADD A LIVE SOURCE DEEPER THAN THE STORE IT
-- STARTED FROM, and what mints it is `deferᵉ`.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHAT THE STATEMENT SAID.  A `chainStep` leaves the maximum nesting
-- over the schedule's live sources no larger than it found it, joined
-- with the slots' own nesting -- premise-free, over every arrival and
-- every path.
--
-- WHY IT LOOKED RIGHT, and the argument was structural rather than a
-- sweep, which is what made it convincing.  A live source was held to
-- be minted ONLY where a scripted slot is subscribed, taking its
-- element type from that slot; `Slot`'s scripted constructor carries an
-- `isData` side condition, and `isData` is FALSE at every observable
-- type.  So no live could carry an observable, `liveNest` was zero at
-- every reachable live, and the corner was said to be unreachable by
-- any corpus rather than merely unvisited by this one.
--
-- WHERE IT BREAKS.  `deferᵉ` mints a live source of its own, and it
-- never passes an `isData` test: the clause writes `elemTy = obs u`
-- outright and puts the deferred BODY in as the pending payload, which
-- is legal precisely because a `Val Γ (obs u)` IS a `Closed Γ u`.  So
-- the element type is observable by construction and `liveNest` reads
-- the body's own nesting.  The scripted-slot argument is true and
-- describes one of the two mint sites.
--
-- THE WITNESS is an arrival carrying `deferᵉ` of a payload three
-- `switchAllᵉ` layers deep, delivered through the one frame that
-- subscribes what it is handed -- `thru-outer mergeAllᵒ` -- from a
-- schedule whose own lives script plain numerals.  Three against one.
-- The left side is the deferred body's depth exactly and the right side
-- does not move with it, so the gap is unbounded: the second row takes
-- the same program to five.
--
-- WHAT DIES AND WHAT DOES NOT.  The premise-free form dies outright,
-- and so does the reason its premises were dropped -- the caps, the
-- nesting receipt and the payload bound were removed as slack on the
-- strength of the coverage argument above.  What survives is the claim
-- about lives minted at SLOTS, which is where the walk's own sources
-- come from.  The repair the numbers point at is to charge the
-- ARRIVAL's payload, since a delivered value's nesting is what the new
-- live carries and the consuming walk has that value in hand.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Chain-Step-Live-Nest where

open import Data.Bool using (false)
open import Data.Maybe using (nothing)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_; foldr)
open import Data.Nat using (ℕ; zero; suc; _≤_; _⊔_)
open import Data.Nat.Properties using (≤⇒≤ᵇ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Closed; Val; natᵗ; obs; nat̂; ofᵉ; strmᵗ; deferᵉ; switchAllᵉ)
open import Rx.Prim using (Gas; g0; gs)
open import Rx.Evaluator
  using (Sched; EvalSt; subscribeE; sched-init; st-init; root;
         chainStep; Arrival; Path; _↠_; thru-outer; mergeAllᵒ;
         installNode; mergeAll-st)
open import Rx.Slots using (Slots)
open import Verify-Budget-Sufficient.Nest-Store using (liveNest; slotsNestSum)
open import Refuted.Demand-Programs using (Γ₂; insT)

prog : Closed Γ₂ natᵗ
prog = ofᵉ (nat̂ 0 ∷ [])

slots : Slots Γ₂
slots = insT 0 0 0

gas : Gas
gas = gs (gs (gs (gs (gs (gs (gs (gs (gs (gs g0)))))))))

sub : Sched Γ₂ × EvalSt prog
sub = let r = subscribeE gas prog root 0 0 (sched-init prog slots) (st-init prog)
      in proj₁ (proj₂ r) , proj₂ (proj₂ r)

-- a payload nested `k` deep, which the arrival carries UNDER a `deferᵉ`
deepV : ℕ → Val Γ₂ (obs natᵗ)
deepV zero    = ofᵉ (nat̂ 0 ∷ [])
deepV (suc k) = switchAllᵉ (ofᵉ (strmᵗ (deepV k) ∷ []))

-- the arrival delivers an OBSERVABLE, and a `thru-outer` frame
-- subscribes what it is handed
arr : ℕ → Arrival Γ₂
arr k = record { tick = 0 ; ordinal = 0 ; source = 1 ; elemTy = obs natᵗ
               ; payload = deferᵉ (deepV k) ; isLast = false }

path : Path Γ₂ (obs natᵗ) natᵗ
path = thru-outer mergeAllᵒ 0 ↠ root

liveMax : Sched Γ₂ → ℕ
liveMax sched = foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched)

row : ℕ → ℕ × ℕ
row k =
  let sched₀ = proj₁ sub
      st₀ = installNode 0 (mergeAll-st {t = natᵗ} nothing 0 [] false) (proj₂ sub)
      r = chainStep 1 (arr k) path sched₀ st₀
  in liveMax (proj₁ (proj₂ r)) , liveMax sched₀ ⊔ slotsNestSum (Sched.slots sched₀)

figures : ℕ × ℕ
figures = proj₁ (row 3) , proj₂ (row 3)

-- THE FIGURES, PINNED, so a repair moving either side fails here naming
-- the number instead of turning the crossing into an equality
grown≡3 : proj₁ figures ≡ 3
grown≡3 = refl

charge≡1 : proj₂ figures ≡ 1
charge≡1 = refl

-- AND THE GAP IS UNBOUNDED IN THE BODY'S DEPTH: the same program at
-- five layers reads five, against the same charge
grown₅≡5 : proj₁ (row 5) ≡ 5
grown₅≡5 = refl

chainStep-nest-live-absurd : proj₁ figures ≤ proj₂ figures → ⊥
-- `3 ≤ᵇ 1` reduces to `false`, so `T` of it IS the empty type
chainStep-nest-live-absurd h = ≤⇒≤ᵇ h
