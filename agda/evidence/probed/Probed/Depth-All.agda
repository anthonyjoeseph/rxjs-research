-- TARGET: depth-all-bound
-- TARGET: depth-conn-input
--
-- THE BURST OVER SEVERAL CHAIN TOPS.  `Refuted.Depth-Chain` measured
-- what a single connect costs — one arc per link, accumulating down a
-- stratified slot chain — and forced `storeNestMax`'s slot half from a
-- max into a sum.  The question this leaves is what happens across
-- SIBLINGS: `depthAll`'s burst enters every inner observable of a
-- merge, and if those arcs add the way the chain's do, a merge over k
-- chain tops charges the sum of k chains while `suc (sizeᵉ b)` grows
-- only with the syntax that lists them.
--
-- THEY DO NOT ADD.  Measured: one chain top gives 5, two independent
-- chain tops under one burst give 5 as well, with the store at 51 in
-- both rows by construction (same slots) so the rows isolate the
-- burst.  The burst takes a MAX across siblings, which is the opposite
-- of what the chain does down a stratified descent — so the arc that
-- accumulates is the CONNECT, not the sibling entry, and
-- `suc (sizeᵉ b)` is not being asked to pay for k chains.
--
-- The rows are read against the CURRENT currency, so a green here is
-- evidence about the sum and not about the max that was refuted.
--
-- SHAPES NOT COVERED: only `mergeAllᵉ` — no concat/switch/exhaust
-- burst, whose `initSt` differs and whose queueing is what
-- `nodesNestMax` charges; no nested burst; no state the cascade has
-- run over; and the two chains here are the same length, so a burst
-- over siblings of DIFFERENT depths is untested (a max would be
-- invisible in these rows if both arms were equal — they are, at 4
-- links apiece, which is why the one-top row is carried beside them:
-- it moves the arm count without moving the arm).
module Probed.Depth-All where

open import Data.Fin  using (Fin) renaming (zero to fz; suc to fs)
open import Data.List using ([]; _∷_)
open import Data.Unit using (tt)
open import Data.Vec  using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.Nat using (_+_)
open import Rx.Prim using (Gas; g0; gs)
open import Rx.Exp  using (Ctx; Closed; natᵗ; nat̂; strmᵗ; input; ofᵉ;
  mergeAllᵉ; sizeᵉ)
open import Rx.Slots using (Slots; shared)
open import Rx.Evaluator using (EvalSt; Sched; root; sched-init; st-init)
open import Verify-Budget-Sufficient.Caps-Depth using (depthE)
open import Verify-Budget-Sufficient.Measures using (pathLen)
open import Verify-Budget-Sufficient.Depth-Compositional using (storeNestMax)

g30 : Gas
g30 = gs (gs (gs (gs (gs (gs (gs (gs (gs (gs
      (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs
      (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs g0)))))))))))))))))))))))))))))

----------------------------------------------------------------------
-- TWO INDEPENDENT CHAINS in one context: slots 0-3 and slots 4-7, each
-- a base plus three links, with slot 8 unused as the root's own.
----------------------------------------------------------------------

Γ₉ : Ctx 9
Γ₉ = natᵗ ∷ⱽ natᵗ ∷ⱽ natᵗ ∷ⱽ natᵗ ∷ⱽ natᵗ ∷ⱽ natᵗ ∷ⱽ natᵗ ∷ⱽ natᵗ ∷ⱽ
     natᵗ ∷ⱽ []ⱽ

baseᶜ : Closed Γ₉ natᵗ
baseᶜ = mergeAllᵉ (ofᵉ (strmᵗ (ofᵉ (nat̂ 7 ∷ [])) ∷ []))

l0 : Closed Γ₉ natᵗ
l0 = mergeAllᵉ (ofᵉ (strmᵗ (input fz) ∷ []))

l1 : Closed Γ₉ natᵗ
l1 = mergeAllᵉ (ofᵉ (strmᵗ (input (fs fz)) ∷ []))

l2 : Closed Γ₉ natᵗ
l2 = mergeAllᵉ (ofᵉ (strmᵗ (input (fs (fs fz))) ∷ []))

l4 : Closed Γ₉ natᵗ
l4 = mergeAllᵉ (ofᵉ (strmᵗ (input (fs (fs (fs (fs fz))))) ∷ []))

l5 : Closed Γ₉ natᵗ
l5 = mergeAllᵉ (ofᵉ (strmᵗ (input (fs (fs (fs (fs (fs fz)))))) ∷ []))

l6 : Closed Γ₉ natᵗ
l6 = mergeAllᵉ (ofᵉ (strmᵗ (input (fs (fs (fs (fs (fs (fs fz))))))) ∷ []))

slots₉ : Slots Γ₉
slots₉ fz                                         = shared baseᶜ {ok = tt}
slots₉ (fs fz)                                    = shared l0 {ok = tt}
slots₉ (fs (fs fz))                               = shared l1 {ok = tt}
slots₉ (fs (fs (fs fz)))                          = shared l2 {ok = tt}
slots₉ (fs (fs (fs (fs fz))))                     = shared baseᶜ {ok = tt}
slots₉ (fs (fs (fs (fs (fs fz)))))                = shared l4 {ok = tt}
slots₉ (fs (fs (fs (fs (fs (fs fz))))))           = shared l5 {ok = tt}
slots₉ (fs (fs (fs (fs (fs (fs (fs fz)))))))      = shared l6 {ok = tt}
slots₉ (fs (fs (fs (fs (fs (fs (fs (fs fz)))))))) = shared baseᶜ {ok = tt}

topA topB : Fin 9
topA = fs (fs (fs fz))
topB = fs (fs (fs (fs (fs (fs (fs fz))))))

-- ONE chain top, for the slope
progOne : Closed Γ₉ natᵗ
progOne = mergeAllᵉ (ofᵉ (strmᵗ (input topA) ∷ []))

-- BOTH chain tops under one burst
progTwo : Closed Γ₉ natᵗ
progTwo = mergeAllᵉ (ofᵉ (strmᵗ (input topA) ∷ strmᵗ (input topB) ∷ []))

schedO : Sched Γ₉
schedO = sched-init progOne slots₉

stO : EvalSt progOne
stO = st-init progOne

schedT : Sched Γ₉
schedT = sched-init progTwo slots₉

stT : EvalSt progTwo
stT = st-init progTwo

-- ALL SEVEN ROWS LOAD-BEARING, and the pair is the point: had the
-- burst's arcs ADDED across siblings, the two-top row would exceed the
-- one-top row by the second chain's depth while `suc (sizeᵉ b)` grew
-- by only the one `strmᵗ` that lists it.  WHAT WOULD MAKE THEM FAIL:
-- sibling accumulation outrunning the syntax that names the siblings.
-- The store rows are not decoration — they are what makes the depth
-- rows comparable, since two programs with different stores could not
-- isolate the burst.  None is vacuous: every quantity is a numeral
-- Agda computed, and the last row is the parent's own conclusion at
-- the harder program, which is the row a crossing would show up in.
_ : storeNestMax schedO stO ≡ 51
_ = refl

_ : storeNestMax schedT stT ≡ 51
_ = refl

_ : sizeᵉ progOne ≡ 5
_ = refl

_ : sizeᵉ progTwo ≡ 7
_ = refl

_ : depthE g30 progOne root 0 0 schedO stO ≡ 5
_ = refl

_ : depthE g30 progTwo root 0 0 schedT stT ≡ 5
_ = refl

-- the PARENT's conclusion at the harder of the two, spelled out so a
-- crossing is visible as a number rather than inferred
_ : sizeᵉ progTwo + pathLen (root {Γ = Γ₉} {t = natᵗ})
      + storeNestMax schedT stT ≡ 58
_ = refl
