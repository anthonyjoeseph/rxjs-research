-- THE RANK'S SEED AND THE DEPTH A CASCADE REACHES GROW AT DIFFERENT
-- RATES IN THE SAME PARAMETER, AND THE RUN'S RATE IS THE LARGER.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.
--
-- WHY THIS FAMILY.  Every row ever taken against the operator leaf sat
-- at a root the leaf does not answer for, so the region carrying its
-- risk had no coverage at all.  A row there needs a FLATTENING root —
-- that is what `opShape` admits — and it is worth having only if the
-- program underneath it grows the one quantity the rank is denominated
-- in.  The family below is built to do exactly that and nothing else.
--
-- HOW A RUN DEEPENS WHAT IT SUBSCRIBES.  Two folds, and each does one
-- job.  The inner one re-wraps its accumulator THREE times per source
-- value, so flattening its output delivers a tree: one literal buys
-- three deliveries, two buy twelve, and the count triples with the
-- source.  The outer one wraps its own accumulator ONCE per delivery it
-- sees, which turns that count into a DEPTH — so the values the family
-- hands out read as deep as the inner fold delivers wide, and the root
-- flattener subscribes every one of them.

-- THE TWO RATES, WHICH IS WHAT THE ROWS BUY.  Each literal adds ONE to
-- `sizeᵉ` and so DOUBLES the rank the machine seeds, while multiplying
-- the depth by three.  Both sides are exponential in the source length
-- and the run's base is the larger, so the ratio closes by half a bit
-- per literal from wherever the machinery's own size starts it.  That
-- is a different finding from the sibling refutations, which put an
-- exponential beside a linear measure: here nothing is mis-denominated,
-- and the seed is beaten in its own currency.
--
-- WHERE THEY CROSS, AND THIS IS ARITHMETIC ON THE RATE RATHER THAN A
-- ROW.  The rows give depth `(3 ^ suc ℓ ∸ 3) / 2` against a rank
-- `2 ^ (27 + ℓ)`, and those meet at ℓ = 46 — a program of seventy-three
-- symbols whose run reads about 1.3e22 layers deep against a rank of
-- about 9.4e21.  NOTHING BELOW INSTANTIATES THAT.  It is an
-- extrapolation of the measured recurrence and is recorded as one.
--
-- AND IT CANNOT BE INSTANTIATED, WHICH IS THE COVERAGE BOUNDARY WORTH
-- RECORDING.  A crossing requires a run to build a value deeper than
-- `2 ^ sizeᵉ` of the program that built it, and no program does this
-- work in under about twenty-seven symbols — so the shallowest
-- crossing anywhere in the family is already past a hundred million
-- layers, which is a term no checker normalises.  Raising the fold's
-- branching moves the crossing to a shorter source and leaves the depth
-- there no smaller, since the bound it has to beat is the seed.  So the
-- rate is the whole of what a probe can buy here, and the rows are
-- chosen to pin the rate exactly.
--
-- THE LEAF ROW IS GREEN AND THAT IS NOT COMFORT.  It sits at the ONE
-- literal root, three layers against a rank of `2 ^ 28`, so the margin
-- there is enormous — which is precisely what the rate says it would be,
-- and precisely why no row at this end can decide the statement.  What
-- the row does buy is the first coverage the leaf has ever had at a root
-- it answers for: the run really does reach `subscribeInner`, really
-- does peel the rank, and really does come back without a dry close.
--
-- WHY ONE LITERAL, WHICH IS AN INFRASTRUCTURE LIMIT AND NOT A CHOICE.
-- MEASURING a burst and SUBSCRIBING one cost differently, and the gap is
-- not the depth.  The rate rows below run the four-literal program and
-- return, because producing a burst walks the tower once; the leaf
-- instead demands `hasDry` of a run whose root flattener SUBSCRIBES
-- every inner that burst delivers, and each of those is a tower of its
-- own.  At two literals that stalled — eleven minutes with the resident
-- set FLAT, so not a normalisation still making progress — against a
-- tree whose whole probe root checks in fourteen seconds.  So the
-- conclusion's reachable coverage stops far short of the depths the
-- rates reach, and that is the other reason the crossing above is
-- arithmetic rather than a row.
--
-- TARGET: dry-operator @27b615
module Probed.Operator-Root where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; _⊔_)
open import Data.Product using (proj₁)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (InstEvent; value; InstEmit)
open import Rx.Exp using (Ctx; Closed; Fn; Tm; natᵗ; obs; _×ᵗ_; sizeᵉ;
  ofᵉ; emptyᵉ; scanᵉ; mergeAllᵉ; strmᵗ; nat̂; fstᵗ; varᵗ)
open import Rx.Slots using (Slots)
open import Rx.Evaluator using (Stream; subscribeE; rootWitness; root;
  sched-init; st-init)
open import Rx.Nest-Depth using (nestDᵉ)
open import Verify-Rank-Sufficient.Dry using (dry-operator)
open import Verify-Rank-Sufficient.Entry using (rootTri-reads)
open import Probed.Apparatus using (Confirms)

----------------------------------------------------------------------
-- HOW DEEP THE VALUES A RUN HANDS OUT READ.  Taken verbatim from the
-- sibling probes and from `Refuted.Burst-Nesting`, so a row here is
-- comparable with a row there — and the payloads it reads are exactly
-- the ones the root flattener goes on to subscribe.
----------------------------------------------------------------------

evNest : ∀ {n} {Γ : Ctx n} {u} → List (InstEvent (Closed Γ u)) → ℕ
evNest []             = 0
evNest (value v ∷ es) = nestDᵉ v ⊔ evNest es
evNest (_ ∷ es)       = evNest es

carried : ∀ {n} {Γ : Ctx n} {u} → Stream Γ (obs u) → ℕ
carried []         = 0
carried (em ∷ ems) = evNest (InstEmit.events em) ⊔ carried ems

Γ₀ : Ctx 0
Γ₀ = []ⱽ

ins₀ : Slots Γ₀
ins₀ = λ ()

burstOf : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) → Stream Γ t
burstOf e ins =
  proj₁ (subscribeE (rootWitness e ins) e root 0 0 (sched-init e ins) (st-init e))

----------------------------------------------------------------------
-- THE TWO FOLDS.  `spread` re-wraps its accumulator three times, so its
-- output flattens to a tree that triples with the source; `deepen`
-- wraps once per delivery it sees, which is what converts that width
-- into depth.  The inner fold's seed is LIVE — one value — because a
-- tree with nothing at its leaves delivers nothing and so moves neither
-- quantity.
----------------------------------------------------------------------

spread : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
spread = strmᵗ (mergeAllᵉ nothing
                 (ofᵉ (fstᵗ (varᵗ (here refl)) ∷
                       fstᵗ (varᵗ (here refl)) ∷
                       fstᵗ (varᵗ (here refl)) ∷ [])))

deepen : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
deepen = strmᵗ (mergeAllᵉ nothing (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ [])))

liveSeed : Tm Γ₀ [] [] [] (obs natᵗ)
liveSeed = strmᵗ (ofᵉ (nat̂ 0 ∷ []))

emitter : List (Tm Γ₀ [] [] [] natᵗ) → Closed Γ₀ (obs natᵗ)
emitter src = scanᵉ deepen (strmᵗ emptyᵉ)
  (mergeAllᵉ nothing (scanᵉ spread liveSeed (ofᵉ src)))

e1 e2 e3 e4 : Closed Γ₀ (obs natᵗ)
e1 = emitter (nat̂ 0 ∷ [])
e2 = emitter (nat̂ 0 ∷ nat̂ 1 ∷ [])
e3 = emitter (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ [])
e4 = emitter (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ [])

----------------------------------------------------------------------
-- THE FIXED RATE OF THE SEED.  One literal, one symbol, one doubling of
-- the rank — pinned so that a change to `sizeᵉ` moves these rows rather
-- than silently changing what the depths below are being compared to.
----------------------------------------------------------------------

_ : sizeᵉ e1 ≡ 28                                      -- LOAD-BEARING
_ = refl

_ : sizeᵉ e2 ≡ 29                                      -- LOAD-BEARING
_ = refl

_ : sizeᵉ e3 ≡ 30                                      -- LOAD-BEARING
_ = refl

_ : sizeᵉ e4 ≡ 31                                      -- LOAD-BEARING
_ = refl

----------------------------------------------------------------------
-- THE MOVING RATE, AND IT IS THE FINDING.  Each row is LOAD-BEARING and
-- each could have failed in either direction: a depth that stalled
-- would say the outer fold does not see the flattened tree, and a depth
-- that merely added would say the inner fold's re-wrapping does not
-- multiply.  It multiplies, by three, against a seed that doubles.
----------------------------------------------------------------------

_ : carried (burstOf e1 ins₀) ≡ 3                      -- LOAD-BEARING
_ = refl

_ : carried (burstOf e2 ins₀) ≡ 12                     -- LOAD-BEARING
_ = refl

_ : carried (burstOf e3 ins₀) ≡ 39                     -- LOAD-BEARING
_ = refl

_ : carried (burstOf e4 ins₀) ≡ 120                    -- LOAD-BEARING
_ = refl

----------------------------------------------------------------------
-- THE LEAF, AT A ROOT IT ANSWERS FOR.  The flattener subscribes the
-- layers the one-literal row above measures, so the rank really is
-- peeled — and this is the first row the statement has ever had inside
-- the region `opShape` admits.
----------------------------------------------------------------------

flat1 : Closed Γ₀ natᵗ
flat1 = mergeAllᵉ nothing e1

opRoot : Confirms (dry-operator (rootWitness flat1 ins₀) flat1 root 0 0
  (sched-init flat1 ins₀) (st-init flat1) refl (rootTri-reads flat1 ins₀))
opRoot = refl
