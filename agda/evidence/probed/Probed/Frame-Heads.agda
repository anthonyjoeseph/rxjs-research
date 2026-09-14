-- THE TWO BURST-REPORT HEADS THAT LEAVE THEIR MODULE, INSTANTIATED.
--
-- WHAT IS AT RISK AND WHERE IT LIVES.  Neither head rewrites a payload:
-- an `*All` frame either SUBSCRIBES one or hands on what an inner
-- subscription already produced, so the claim is that a value the frame
-- passes through is still written under the rank the frame entered at.
-- That splits cleanly in two.  Every arm of either relation that does
-- NOT run a subscription returns its own input, or returns nothing at
-- all -- so on those arms the conclusion IS the hypothesis, and what a
-- row buys is that the relation re-indexes nothing and the wrap
-- fabricates nothing.  The values that could make either head false
-- come from the other side: a value minted by `subscribeInner⇓`, which
-- is a whole subscription derivation.
--
-- COVERAGE, and it is a boundary rather than a sweep.  `inner-handed`
-- is reached at `react-false` and at `react-dead` through `finish-nil`,
-- both at a two-element payload whose side condition is inhabited.
-- `thru-handed` is reached at `walk-nil` and at `walk-cons` over each
-- of the three `*All` ops, with the input an observable whose reading
-- is strictly under the rank -- so the premise has content at the one
-- type where `ValOK` reads arithmetic at all -- and at both values of
-- the wrap's flag.  NOT reached, and this is the load-bearing region:
-- `react-alive`, which needs a registry entry alive through the
-- instance; `finish-all-drain`, whose conclusion covers values the
-- drain produced and the hypothesis never saw; and every `thruConsume⇓`
-- arm that subscribes.  All three need a state reached by RUNNING a
-- program, which this tree has no harness for -- so no row here has a
-- non-empty conclusion the hypothesis did not already carry, and the
-- receipts say only that the pass-through arms pass through.
--
-- TARGET: inner-handed @db6ebd
-- TARGET: thru-handed @fb45c1
module Probed.Frame-Heads where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; z≤n; s≤s)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Exp using (Ctx; Closed; Val; natᵗ; obs; emptyᵉ)
open import Rx.Slots using (Slots)
open import Rx.Strat-Order using (Tri)
open import Rx.Evaluator using (Path; root; Sched; EvalSt; sched-init; st-init; mergeAllᵒ; switchᵒ; exhaustᵒ)
open import Rx.Evaluator.Doorless using (HandedOK)
open import Rx.Evaluator.Domain using (react-false; react-dead; finish-nil; walk-nil; walk-cons; consume-all-nil;
  consume-switch-nil; consume-exhaust-nil)
open import Rx.Evaluator.Burst-Report using (inner-handed; thru-handed)

open import Probed.Apparatus using (Confirms)

Γ₀ : Ctx 0
Γ₀ = []ⱽ

η₀ : Fin 0 → ℕ
η₀ ()

e₀ : Closed Γ₀ natᵗ
e₀ = emptyᵉ

ins₀ : Slots Γ₀
ins₀ ()

sch₀ : Sched Γ₀
sch₀ = sched-init e₀ ins₀

st₀ : EvalSt e₀
st₀ = st-init e₀

κ₀ : Path Γ₀ 0 natᵗ natᵗ
κ₀ = root

----------------------------------------------------------------------
-- 1.  THE INNER HEAD.  `ValOK` at a data type reads no arithmetic, so
-- the side condition here is inhabited at every rank and the row's
-- content is that the relation hands the payload back unchanged.  The
-- second row is the one worth having: it goes through the completion
-- side, where a different arm could have returned a different list.
----------------------------------------------------------------------

τ₀ : Tri
τ₀ = 0 , 0 , 0

vs₂ : List (Val Γ₀ natᵗ)
vs₂ = 3 ∷ 5 ∷ []

ok₂ : HandedOK {Γ = Γ₀} {u = natᵗ} η₀ vs₂ τ₀
ok₂ = tt ∷ᵃ tt ∷ᵃ []ᵃ

-- DEGENERATE as arithmetic, LOAD-BEARING as a re-indexing test: the
-- conclusion is read off the constructor's result, so an arm handing
-- back a transformed list would leave this unclosable.
row-inner-false : Confirms
  (inner-handed {e = e₀} {τ = τ₀} η₀ ok₂
    (react-false {op = mergeAllᵒ} {allNid = 0} {inst = 0} {κ = κ₀}
                 {id = 0} {now = 0} {sched = sch₀} {st = st₀}))
row-inner-false = tt ∷ᵃ tt ∷ᵃ []ᵃ

-- the completion side, at an empty registry -- so the guard reads dead
-- and the node lookup finds nothing, which is the arm that returns
row-inner-dead : Confirms
  (inner-handed {e = e₀} {τ = τ₀} η₀ ok₂
    (react-dead {op = mergeAllᵒ} {allNid = 0} {inst = 0} {κ = κ₀}
                {id = 0} {now = 0} {sched = sch₀} {st = st₀}
                refl finish-nil))
row-inner-dead = tt ∷ᵃ tt ∷ᵃ []ᵃ

----------------------------------------------------------------------
-- 2.  THE THRU HEAD.  Its input is OBSERVABLE, which is the one type
-- at which `ValOK` reads a number -- so the premise has content here
-- and the empty walk is not the only shape available.  What no row
-- reaches is a non-empty OUTPUT: every arm that produces one
-- subscribes.
----------------------------------------------------------------------

τ₁ : Tri
τ₁ = 0 , 1 , 0

o₀ : Val Γ₀ (obs natᵗ)
o₀ = emptyᵉ

ok₁ : HandedOK {u = obs natᵗ} η₀ (o₀ ∷ []) τ₁
ok₁ = s≤s z≤n ∷ᵃ []ᵃ

-- DEGENERATE: the empty walk, here to say the wrap invents nothing.
row-thru-nil : Confirms
  (thru-handed {e = e₀} {u = natᵗ} {τ = τ₁} η₀ {op = mergeAllᵒ} {nid = 0}
    {κ = κ₀} {id = 0} {now = 0} {sched = sch₀} {st = st₀}
    false ([] , [] , sch₀ , st₀) []ᵃ walk-nil)
row-thru-nil = []ᵃ

-- LOAD-BEARING as a fabrication test at each op's wrap clause: the
-- flag is set, so the wrap selects on the op and reads the node table.
row-thru-merge : Confirms
  (thru-handed {e = e₀} {u = natᵗ} {τ = τ₁} η₀ {op = mergeAllᵒ} {nid = 0}
    {κ = κ₀} {id = 0} {now = 0} {sched = sch₀} {st = st₀}
    true ([] , [] , sch₀ , st₀) ok₁
    (walk-cons consume-all-nil walk-nil))
row-thru-merge = []ᵃ

row-thru-switch : Confirms
  (thru-handed {e = e₀} {u = natᵗ} {τ = τ₁} η₀ {op = switchᵒ} {nid = 0}
    {κ = κ₀} {id = 0} {now = 0} {sched = sch₀} {st = st₀}
    true ([] , [] , sch₀ , st₀) ok₁
    (walk-cons consume-switch-nil walk-nil))
row-thru-switch = []ᵃ

row-thru-exhaust : Confirms
  (thru-handed {e = e₀} {u = natᵗ} {τ = τ₁} η₀ {op = exhaustᵒ} {nid = 0}
    {κ = κ₀} {id = 0} {now = 0} {sched = sch₀} {st = st₀}
    true ([] , [] , sch₀ , st₀) ok₁
    (walk-cons consume-exhaust-nil walk-nil))
row-thru-exhaust = []ᵃ
