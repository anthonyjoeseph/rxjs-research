-- THE HOP-DESCENT CRUX, decided at STATEMENT time.
--
-- subscribeE-walkS's inner-hop edge (dBound-hop) demands r′ < r: the hopped-to
-- observable must rank strictly below the one being walked.  For that to be
-- discharged per emission site the walk needs, at each site where a burst value
-- reaches an *All frame,
--
--     hop-descent : … → measureE V o ≺ᵛ measureE V b
--
-- where `o` is the emitted observable and `b` the expression being walked.  At
-- the syntactic sites this is exactly ≺-embed / ≺-replace / unfoldμ-≺, already
-- proven: `o` is built out of `b`'s own syntax, so its shell multiset sits
-- strictly inside `b`'s.
--
-- At ONE site it cannot be stated, and this module is the reason.  A scripted
-- slot carries `ObservableInput (Val Γ t)`, and `Val Γ (obs u) = Closed Γ u` —
-- an observable VALUE IS A CLOSED EXPRESSION.  So slot data can carry any
-- observable at all, with no syntactic relation to the expression being walked.
-- Nothing stops it carrying the walked program ITSELF.
--
-- Below, `prog` is `mergeAllᵉ (input zero)` and slot zero is the cold script
-- that emits `prog`.  The check at the bottom is that the value handed to
-- subscribeInner IS prog, by refl.
--
-- The demanded instance at this site is therefore
--
--     measureE V prog ≺ᵛ measureE V (input zero)
--
-- while `input zero` is a strict subterm of prog, so measureE V (input zero)
-- sits at or below measureE V prog.  Chaining gives measureE V prog ≺ᵛ
-- measureE V prog, which ≺ᵛ-wf refutes.  The site does not need a harder proof;
-- it needs a different edge — the descent it is being asked for does not exist.
--
-- Note the SHARE boundary is NOT this problem.  A shared slot's def d is walked
-- (subscribeSharedSlot), so its emissions are syntactically inside d, and the
-- crossing INTO d is the connect edge, which pays with U and only needs
-- rank ≤ R — supplied already by connect-anchor off the budget's slot summand.
-- Shares are anchored; scripted inputs are not.
module Hop-Descent-Probe where

open import Data.Bool    using (Bool; true; false)
open import Data.Fin     using (Fin; zero)
open import Data.List    using (List; []; _∷_)
open import Data.Nat     using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec     using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp
open import Rx.Prim
open import Rx.Evaluator

-- one slot, carrying observables of nat
Γ₁ : Ctx 1
Γ₁ = obs natᵗ ∷ []

-- the program: subscribe the slot, and subscribe every observable it emits
prog : Closed Γ₁ natᵗ
prog = mergeAllᵉ (input zero)

-- the slot's script emits ONE value: prog itself.  Well-typed because
-- Val Γ₁ (obs natᵗ) reduces to Closed Γ₁ natᵗ, which is prog's own type.
slots₁ : Slots Γ₁
slots₁ zero = scripted (cold (prog ∷ []) [])

-- ── the emission path ────────────────────────────────────────────────────
-- subscribeAll mergeᵒ mints node 0 and subscribes the outer `input zero`
-- under a thru-outer frame; the cold script's sync list becomes the burst's
-- values; pushBurst hands each to thruConsume mergeᵒ, i.e. to subscribeInner.
outerBurst : Stream Γ₁ (obs natᵗ)
outerBurst = proj₁ (subscribeE {e = prog} (budgetAt prog slots₁ 0)
                      (input zero) (thru-outer mergeᵒ 0 ↠ root) 0 0
                      (sched-init prog slots₁) (st-init prog))

-- what pushBurst peels off and hands to subscribeInner, one `o` per element
hopTargets : List (Val Γ₁ (obs natᵗ))
hopTargets = proj₁ (splitBurst {A = Val Γ₁ natᵗ} outerBurst)

-- THE FINDING: the hop target is the whole program.  So the hop edge is asked
-- to descend from prog to prog.
_ : hopTargets ≡ prog ∷ []
_ = refl

-- ── and the regress is real, not merely undescending ─────────────────────
-- Each hop re-enters subscribeE on prog, so it re-reaches this same emission
-- site.  Gas is the only thing stopping it: at every finite gas the walk ends
-- on subscribeInner's g0 stub, which emits the dry close.  Below, one and two
-- units of gas both go dry — the recursion does not bottom out, it is cut off.
dryAt : Gas → Bool
dryAt g = hasDry (proj₁ (subscribeE {e = prog} g prog root 0 0
                           (sched-init prog slots₁) (st-init prog)))

_ : dryAt (gs g0) ≡ true
_ = refl

_ : dryAt (gs (gs g0)) ≡ true
_ = refl

_ : dryAt (gs (gs (gs g0))) ≡ true
_ = refl
