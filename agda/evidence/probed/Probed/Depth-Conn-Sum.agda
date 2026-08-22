-- TARGET: depth-conn-input
--
-- THE STATEMENT THAT WAS REFUTED AND THEN REPAIRED WITHOUT MOVING.
-- `depth-conn-input` bounds a store read by `storeNestMax` alone, and
-- Refuted.Depth-Chain crossed it at a nine-link slot chain — against
-- the MAX the slot half used to be.  The repair changed the MEASURE to
-- a SUM and left the statement's text alone, so the statement now
-- rests entirely on the sum having margin where the max had none.
-- Nothing had instantiated it under the new measure.
--
-- SO THE QUESTION IS A RATIO, and it is a question about the CHEAPEST
-- link rather than about any particular program.  Every `suc` on the
-- subscribe side comes from a `thru-outer` frame, so depth counts
-- operator nodes; `slotNest (shared d)` is `sizeᵉ d`, so the sum counts
-- syntax.  The sum wins iff an operator node cannot be had for less
-- than one unit of size — and the adversarial program is the one that
-- buys depth as cheaply as the syntax allows.
--
-- WHAT MAKES A LINK CHEAP.  Refuted.Depth-Chain's links were
-- `mergeAllᵉ (ofᵉ (strmᵗ (input j) ∷ []))` — five units of size for one
-- of depth, because a `natᵗ`-typed chain has to re-wrap at every link
-- to feed the next `mergeAllᵉ`.  The re-wrap is avoidable: give the
-- slots DESCENDING `obs` types and each link is a bare
-- `mergeAllᵉ (input j)`, two units of size for one of depth.  That is
-- the floor, because `mergeAllᵉ` strips exactly one `obs` and so a
-- chain of length k needs `obs`-depth k at its source — the source's
-- own ladder is what the sum collects instead.
--
-- MEASURED AT TWO CHAIN LENGTHS PER SHAPE, so the reading is a slope
-- and not a point: the max was refuted precisely by a quantity that did
-- not move with the chain, and a single row cannot tell the two apart.
--
-- THE RESULT — a confidence receipt, and the cheap link turned out not
-- to be a threat at all:
--
--                             slots   depth   storeNestMax
--   obs-ladder, links size 2      6       1             28
--                                 9       1             43
--   re-wrapping, links size 5     6       6             32
--                                 9       9             47
--
-- TWO FINDINGS, and the first was the surprise.  CHEAP SYNTAX BUYS NO
-- DEPTH: the `obs`-ladder's depth is 1 at both lengths, because a bare
-- `mergeAllᵉ (input j)` recurses on the SUBSCRIBE side, where the
-- mirror charges nothing — every `suc` comes from a `thru-outer` BURST,
-- and a burst needs the link to emit synchronously at its own frame,
-- which is what the `ofᵉ`/`strmᵗ` re-wrap is doing in the accumulating
-- shape.  So the size a link spends on re-wrapping is not overhead the
-- sum is charging for gratuitously; it is the thing that generates the
-- depth.  That is a reason the ratio is bounded away from 1, not an
-- accident of the encoding.
--
-- AND THE SUM OUTRUNS THE CHAIN, which is the property the max lacked:
-- three more links cost 3 more depth and 15 more sum.  § D is the
-- refutation's own witness — nine operator nodes on one chain, 9
-- against a max of 7 — and the 47 here is the first MACHINE reading of
-- the sum at that program; Refuted.Depth-Chain computed it in prose.
--
-- NOT COVERED: a non-empty store (every row is at `st-init`, so
-- `nodesNestMax` is 0 throughout and the `⊔` in `storeNestMax` never
-- selects the node half); a `scripted` slot mixed into a chain; and any
-- shape where depth arrives from something other than a chain of
-- connects.  The rows say nothing about the proof, whose obstacle is
-- the double-count and is arithmetic rather than truth.
module Probed.Depth-Conn-Sum where

open import Data.List using ([]; _∷_)
open import Data.Unit using (tt)
open import Data.Vec  using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Data.Fin  using (Fin) renaming (zero to fz; suc to fs)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gs)
open import Rx.Exp  using (Ctx; Closed; Exp; natᵗ; obs; nat̂; ofᵉ; strmᵗ; mergeAllᵉ; input)
open import Rx.Slots using (Slots; shared)
open import Rx.Evaluator using (Sched; EvalSt; root; sched-init; st-init)
open import Verify-Budget-Sufficient.Caps-Depth using (depthE)
open import Verify-Budget-Sufficient.Depth-Compositional using (storeNestMax;
  slotNest)

g40 : Gas
g40 = gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs
      (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs
      (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs
      (g0))))))))))))))))))))))))))))))))))))))))

----------------------------------------------------------------------
-- § A — a five-link chain
----------------------------------------------------------------------

ΓA : Ctx 6
ΓA = obs (obs (obs (obs (obs natᵗ)))) ∷ⱽ obs (obs (obs (obs natᵗ))) ∷ⱽ obs (obs (obs natᵗ)) ∷ⱽ obs (obs natᵗ) ∷ⱽ obs natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

-- the source: 5 `ofᵉ`/`strmᵗ` wrapping layers over a synchronous
-- `of`, which is what makes the chain emit at subscribe at all
wrapA : ∀ {t} → Exp ΓA [] [] [] t → Exp ΓA [] [] [] (obs t)
wrapA e = ofᵉ (strmᵗ e ∷ [])

srcA : Closed ΓA (obs (obs (obs (obs (obs natᵗ)))))
srcA = wrapA (wrapA (wrapA (wrapA (wrapA (ofᵉ (nat̂ 7 ∷ []))))))

lkA1 : Closed ΓA (obs (obs (obs (obs natᵗ))))
lkA1 = mergeAllᵉ (input fz)
lkA2 : Closed ΓA (obs (obs (obs natᵗ)))
lkA2 = mergeAllᵉ (input (fs fz))
lkA3 : Closed ΓA (obs (obs natᵗ))
lkA3 = mergeAllᵉ (input (fs (fs fz)))
lkA4 : Closed ΓA (obs natᵗ)
lkA4 = mergeAllᵉ (input (fs (fs (fs fz))))
lkA5 : Closed ΓA (natᵗ)
lkA5 = mergeAllᵉ (input (fs (fs (fs (fs fz)))))

slotsA : Slots ΓA
slotsA fz                         = shared srcA {ok = tt}
slotsA (fs fz)                    = shared lkA1 {ok = tt}
slotsA (fs (fs fz))                 = shared lkA2 {ok = tt}
slotsA (fs (fs (fs fz)))              = shared lkA3 {ok = tt}
slotsA (fs (fs (fs (fs fz))))           = shared lkA4 {ok = tt}
slotsA (fs (fs (fs (fs (fs fz)))))        = shared lkA5 {ok = tt}

topA : Fin 6
topA = fs (fs (fs (fs (fs fz))))

progA : Closed ΓA natᵗ
progA = input topA

schedA : Sched ΓA
schedA = sched-init progA slotsA

stA : EvalSt progA
stA = st-init progA

-- DEGENERATE, and labelled so: the per-slot figures only show where the
-- sum's summands come from.  They cannot fail while `slotNest` is
-- `sizeᵉ`.
_ : slotNest (slotsA fz) ≡ 18
_ = refl

_ : slotNest (slotsA (fs fz)) ≡ 2
_ = refl

-- LOAD-BEARING.  The two sides of the statement at the top of the
-- chain.  WHAT WOULD MAKE THIS FAIL: a link buying a `thru-outer` arc
-- for less than one unit of `sizeᵉ`, which is what the max could not
-- survive and what the sum is being trusted to charge for.
_ : depthE g40 progA root 0 0 schedA stA ≡ 1
_ = refl

_ : storeNestMax schedA stA ≡ 28
_ = refl

----------------------------------------------------------------------
-- § B — the same construction at eight links.  Both sides must MOVE,
-- and the sum must move at least as fast; the max's defect was that it
-- did not move at all.
----------------------------------------------------------------------

ΓB : Ctx 9
ΓB = obs (obs (obs (obs (obs (obs (obs (obs natᵗ))))))) ∷ⱽ obs (obs (obs (obs (obs (obs (obs natᵗ)))))) ∷ⱽ obs (obs (obs (obs (obs (obs natᵗ))))) ∷ⱽ obs (obs (obs (obs (obs natᵗ)))) ∷ⱽ obs (obs (obs (obs natᵗ))) ∷ⱽ obs (obs (obs natᵗ)) ∷ⱽ obs (obs natᵗ) ∷ⱽ obs natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

-- the source: 8 `ofᵉ`/`strmᵗ` wrapping layers over a synchronous
-- `of`, which is what makes the chain emit at subscribe at all
wrapB : ∀ {t} → Exp ΓB [] [] [] t → Exp ΓB [] [] [] (obs t)
wrapB e = ofᵉ (strmᵗ e ∷ [])

srcB : Closed ΓB (obs (obs (obs (obs (obs (obs (obs (obs natᵗ))))))))
srcB = wrapB (wrapB (wrapB (wrapB (wrapB (wrapB (wrapB (wrapB (ofᵉ (nat̂ 7 ∷ [])))))))))

lkB1 : Closed ΓB (obs (obs (obs (obs (obs (obs (obs natᵗ)))))))
lkB1 = mergeAllᵉ (input fz)
lkB2 : Closed ΓB (obs (obs (obs (obs (obs (obs natᵗ))))))
lkB2 = mergeAllᵉ (input (fs fz))
lkB3 : Closed ΓB (obs (obs (obs (obs (obs natᵗ)))))
lkB3 = mergeAllᵉ (input (fs (fs fz)))
lkB4 : Closed ΓB (obs (obs (obs (obs natᵗ))))
lkB4 = mergeAllᵉ (input (fs (fs (fs fz))))
lkB5 : Closed ΓB (obs (obs (obs natᵗ)))
lkB5 = mergeAllᵉ (input (fs (fs (fs (fs fz)))))
lkB6 : Closed ΓB (obs (obs natᵗ))
lkB6 = mergeAllᵉ (input (fs (fs (fs (fs (fs fz))))))
lkB7 : Closed ΓB (obs natᵗ)
lkB7 = mergeAllᵉ (input (fs (fs (fs (fs (fs (fs fz)))))))
lkB8 : Closed ΓB (natᵗ)
lkB8 = mergeAllᵉ (input (fs (fs (fs (fs (fs (fs (fs fz))))))))

slotsB : Slots ΓB
slotsB fz                         = shared srcB {ok = tt}
slotsB (fs fz)                    = shared lkB1 {ok = tt}
slotsB (fs (fs fz))                 = shared lkB2 {ok = tt}
slotsB (fs (fs (fs fz)))              = shared lkB3 {ok = tt}
slotsB (fs (fs (fs (fs fz))))           = shared lkB4 {ok = tt}
slotsB (fs (fs (fs (fs (fs fz)))))        = shared lkB5 {ok = tt}
slotsB (fs (fs (fs (fs (fs (fs fz))))))     = shared lkB6 {ok = tt}
slotsB (fs (fs (fs (fs (fs (fs (fs fz)))))))  = shared lkB7 {ok = tt}
slotsB (fs (fs (fs (fs (fs (fs (fs (fs fz)))))))) = shared lkB8 {ok = tt}

topB : Fin 9
topB = fs (fs (fs (fs (fs (fs (fs (fs fz)))))))

progB : Closed ΓB natᵗ
progB = input topB

schedB : Sched ΓB
schedB = sched-init progB slotsB

stB : EvalSt progB
stB = st-init progB

_ : depthE g40 progB root 0 0 schedB stB ≡ 1
_ = refl

_ : storeNestMax schedB stB ≡ 43
_ = refl

----------------------------------------------------------------------
-- § C and § D — the shape that DOES accumulate.  § A and § B buy their
-- links cheaply and get depth 1 whatever the chain length, so they
-- cannot cross anything; the accumulating shape re-wraps at every link
-- (`mergeAllᵉ (ofᵉ (strmᵗ (input j) ∷ []))`), which is what pays for a
-- `thru-outer` burst at each link and what crossed the old max.  These
-- are the rows the repair has to survive, and Refuted.Depth-Chain never
-- measured the sum — it computed it in prose.
----------------------------------------------------------------------

ΓC : Ctx 6
ΓC = natᵗ ∷ⱽ natᵗ ∷ⱽ natᵗ ∷ⱽ natᵗ ∷ⱽ natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

srcC : Closed ΓC natᵗ
srcC = mergeAllᵉ (ofᵉ (strmᵗ (ofᵉ (nat̂ 7 ∷ [])) ∷ []))

lkC1 : Closed ΓC natᵗ
lkC1 = mergeAllᵉ (ofᵉ (strmᵗ (input (fz)) ∷ []))
lkC2 : Closed ΓC natᵗ
lkC2 = mergeAllᵉ (ofᵉ (strmᵗ (input (fs fz)) ∷ []))
lkC3 : Closed ΓC natᵗ
lkC3 = mergeAllᵉ (ofᵉ (strmᵗ (input (fs (fs fz))) ∷ []))
lkC4 : Closed ΓC natᵗ
lkC4 = mergeAllᵉ (ofᵉ (strmᵗ (input (fs (fs (fs fz)))) ∷ []))
lkC5 : Closed ΓC natᵗ
lkC5 = mergeAllᵉ (ofᵉ (strmᵗ (input (fs (fs (fs (fs fz))))) ∷ []))

slotsC : Slots ΓC
slotsC fz                             = shared srcC {ok = tt}
slotsC (fs fz)                        = shared lkC1 {ok = tt}
slotsC (fs (fs fz))                   = shared lkC2 {ok = tt}
slotsC (fs (fs (fs fz)))              = shared lkC3 {ok = tt}
slotsC (fs (fs (fs (fs fz))))         = shared lkC4 {ok = tt}
slotsC (fs (fs (fs (fs (fs fz)))))    = shared lkC5 {ok = tt}

topC : Fin 6
topC = fs (fs (fs (fs (fs fz))))

progC : Closed ΓC natᵗ
progC = input topC

schedC : Sched ΓC
schedC = sched-init progC slotsC

stC : EvalSt progC
stC = st-init progC

_ : depthE g40 progC root 0 0 schedC stC ≡ 6
_ = refl

_ : storeNestMax schedC stC ≡ 32
_ = refl

ΓD : Ctx 9
ΓD = natᵗ ∷ⱽ natᵗ ∷ⱽ natᵗ ∷ⱽ natᵗ ∷ⱽ natᵗ ∷ⱽ natᵗ ∷ⱽ natᵗ ∷ⱽ natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

srcD : Closed ΓD natᵗ
srcD = mergeAllᵉ (ofᵉ (strmᵗ (ofᵉ (nat̂ 7 ∷ [])) ∷ []))

lkD1 : Closed ΓD natᵗ
lkD1 = mergeAllᵉ (ofᵉ (strmᵗ (input (fz)) ∷ []))
lkD2 : Closed ΓD natᵗ
lkD2 = mergeAllᵉ (ofᵉ (strmᵗ (input (fs fz)) ∷ []))
lkD3 : Closed ΓD natᵗ
lkD3 = mergeAllᵉ (ofᵉ (strmᵗ (input (fs (fs fz))) ∷ []))
lkD4 : Closed ΓD natᵗ
lkD4 = mergeAllᵉ (ofᵉ (strmᵗ (input (fs (fs (fs fz)))) ∷ []))
lkD5 : Closed ΓD natᵗ
lkD5 = mergeAllᵉ (ofᵉ (strmᵗ (input (fs (fs (fs (fs fz))))) ∷ []))
lkD6 : Closed ΓD natᵗ
lkD6 = mergeAllᵉ (ofᵉ (strmᵗ (input (fs (fs (fs (fs (fs fz)))))) ∷ []))
lkD7 : Closed ΓD natᵗ
lkD7 = mergeAllᵉ (ofᵉ (strmᵗ (input (fs (fs (fs (fs (fs (fs fz))))))) ∷ []))
lkD8 : Closed ΓD natᵗ
lkD8 = mergeAllᵉ (ofᵉ (strmᵗ (input (fs (fs (fs (fs (fs (fs (fs fz)))))))) ∷ []))

slotsD : Slots ΓD
slotsD fz                             = shared srcD {ok = tt}
slotsD (fs fz)                        = shared lkD1 {ok = tt}
slotsD (fs (fs fz))                   = shared lkD2 {ok = tt}
slotsD (fs (fs (fs fz)))              = shared lkD3 {ok = tt}
slotsD (fs (fs (fs (fs fz))))         = shared lkD4 {ok = tt}
slotsD (fs (fs (fs (fs (fs fz)))))    = shared lkD5 {ok = tt}
slotsD (fs (fs (fs (fs (fs (fs fz)))))) = shared lkD6 {ok = tt}
slotsD (fs (fs (fs (fs (fs (fs (fs fz))))))) = shared lkD7 {ok = tt}
slotsD (fs (fs (fs (fs (fs (fs (fs (fs fz)))))))) = shared lkD8 {ok = tt}

topD : Fin 9
topD = fs (fs (fs (fs (fs (fs (fs (fs fz)))))))

progD : Closed ΓD natᵗ
progD = input topD

schedD : Sched ΓD
schedD = sched-init progD slotsD

stD : EvalSt progD
stD = st-init progD

-- LOAD-BEARING, and this is the row the refutation's own witness sits
-- on: nine operator nodes on one chain, the program that gave 9 against
-- a max of 7.  WHAT WOULD MAKE IT FAIL: the sum failing to grow at
-- least as fast as the chain, which is exactly how the max died.
_ : depthE g40 progD root 0 0 schedD stD ≡ 9
_ = refl

_ : storeNestMax schedD stD ≡ 47
_ = refl
