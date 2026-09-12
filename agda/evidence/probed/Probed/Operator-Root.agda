-- THE RANK THE MACHINE ENTERS AT IS BLIND TO SOURCE LENGTH, AND THE
-- DEPTH A CASCADE REACHES MULTIPLIES WITH IT.
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

-- ONE RATE MOVES AND THE OTHER DOES NOT, WHICH IS WHAT THE ROWS BUY.
-- Each literal multiplies the depth by three while the rank the machine
-- enters at reads the SAME at every source length — four programs,
-- differing in literals alone, all reading 532899.  So this is not two
-- exponentials racing: the reading is a function of the STORE BOUND and
-- the term's templates, and source length is not among its inputs,
-- while source length is exactly what moves the deliveries a fold
-- compounds over.
--
-- WHERE THEY CROSS, AND THIS IS ARITHMETIC ON THE RATE RATHER THAN A
-- ROW.  The rows give depth `(3 ^ suc ℓ ∸ 3) / 2` against a flat
-- 532899, and those meet at TWELVE literals — a run reading about
-- 800000 layers deep at a bound of six.  NOTHING BELOW INSTANTIATES
-- THAT.  It is an extrapolation of the measured recurrence and is
-- recorded as one.
--
-- AND THIS IS THE SHAPE THE SIBLING RECEIPTS COULD NOT REACH.  A grown
-- value handed out of the ROOT is subscribed by nobody, so its depth
-- costs the guard nothing however far it passes the term's reading;
-- here the root IS a flattener, so every layer the fold builds is a
-- layer the run enters.  What the rate then says is that the store
-- bound has to cover the deliveries a cascade makes SYNCHRONOUSLY, and
-- a synchronous cascade consumes no fuel — which is where the reading's
-- `k ≤ V` premise sits, and `Refuted.Rank-Cross` since settled that it
-- is not merely unpaid but FALSE at the bound `evaluate` seeds itself
-- with.
--
-- THE COVERAGE BOUNDARY, and it is an infrastructure limit rather than
-- a choice.  MEASURING a burst and SUBSCRIBING one cost differently: at
-- two literals the leaf row stalled for eleven minutes with the
-- resident set FLAT — so not a normalisation still making progress —
-- against a whole probe root that checks in fourteen seconds.  The
-- crossing above is therefore six orders of magnitude past anything a
-- checker will normalise, and the rate is the whole of what a probe can
-- buy here.
--
-- THE LEAF ROW IS GREEN AND THAT IS NOT COMFORT.  It sits at the ONE
-- literal root, three layers against 532899, so the margin there is
-- enormous — which is precisely what the rate says it would be, and
-- precisely why no row at this end can decide the statement.  What the
-- row does buy is the first coverage the leaf has ever had at a root it
-- answers for: the run really does reach `subscribeInner`, really does
-- peel the rank, and really does come back without a dry close.
--
-- TARGET: dry-operator @474d33
module Probed.Operator-Root where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; _⊔_)
open import Data.Product using (proj₁)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (InstEvent; value; InstEmit)
open import Rx.Exp using (Ctx; Closed; Fn; Tm; natᵗ; obs; _×ᵗ_;
  ofᵉ; emptyᵉ; scanᵉ; mergeAllᵉ; strmᵗ; nat̂; fstᵗ; varᵗ)
open import Rx.Slots using (Slots)
open import Rx.Hop-Depth using (hopDᵉ)
open import Rx.Slot-Hop using (slotHop)
open import Rx.Evaluator using (Stream; subscribeE; rootWitness; root;
  sched-init; st-init)
open import Verify-Rank-Sufficient.Dry using (dry-operator)
open import Verify-Rank-Sufficient.Entry using (rootTri-reads)
open import Probed.Apparatus using (Confirms)

----------------------------------------------------------------------
-- HOW DEEP THE VALUES A RUN HANDS OUT READ, IN THE RANK'S OWN
-- CURRENCY.  The payloads it reads are exactly the ones the root
-- flattener goes on to subscribe, so a depth here is comparable with
-- the rank rows below rather than merely alongside them — which a
-- reading in NESTING was not, since the two orders disagree at the
-- `deferᵉ` gate.
----------------------------------------------------------------------

evHop : ∀ {n} {Γ : Ctx n} {u} (V : ℕ) (η : Fin n → ℕ) →
        List (InstEvent (Closed Γ u)) → ℕ
evHop V η []             = 0
evHop V η (value v ∷ es) = hopDᵉ V η v ⊔ evHop V η es
evHop V η (_ ∷ es)       = evHop V η es

carried : ∀ {n} {Γ : Ctx n} {u} (V : ℕ) (η : Fin n → ℕ) →
          Stream Γ (obs u) → ℕ
carried V η []         = 0
carried V η (em ∷ ems) = evHop V η (InstEmit.events em) ⊔ carried V η ems

Γ₀ : Ctx 0
Γ₀ = []ⱽ

ins₀ : Slots Γ₀
ins₀ = λ ()

-- THE STORE BOUND every reading here is taken at.  `evaluate` builds
-- its schedule at the fuel it then hands the drain, so a row is about a
-- RUN only when the two agree.  A row free to pick the bound separately
-- would be picking how tight the statement it instantiates is.
SB : ℕ
SB = 6

burstOf : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) → Stream Γ t
burstOf e ins =
  proj₁ (subscribeE (rootWitness SB e ins) e root 0 0 (sched-init SB e ins)
           (st-init e))

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
-- THE RANK THE MACHINE ACTUALLY ENTERS AT, AND IT DOES NOT MOVE.  The
-- entry reads `hopDᵉ` at the run's own store bound; the four programs
-- differ in source length alone and all four read the SAME.  Each row
-- is LOAD-BEARING and could have failed in either direction — a reading
-- that grew with the literals would say the rank still tracks the
-- syntax, and one that shrank would say a literal costs the measure
-- something.  It does neither, which is what makes the depths below a
-- comparison rather than two unrelated numbers.
----------------------------------------------------------------------

η₀ : Fin 0 → ℕ
η₀ = slotHop SB ins₀

_ : hopDᵉ SB η₀ e1 ≡ 532899                            -- LOAD-BEARING
_ = refl

_ : hopDᵉ SB η₀ e4 ≡ 532899                            -- LOAD-BEARING
_ = refl

----------------------------------------------------------------------
-- THE MOVING RATE, AND IT IS THE FINDING.  Each row is LOAD-BEARING and
-- each could have failed in either direction: a depth that stalled
-- would say the outer fold does not see the flattened tree, and a depth
-- that merely added would say the inner fold's re-wrapping does not
-- multiply.  It multiplies, by three, against a seed that doubles.
----------------------------------------------------------------------

_ : carried SB η₀ (burstOf e1 ins₀) ≡ 3                      -- LOAD-BEARING
_ = refl

_ : carried SB η₀ (burstOf e2 ins₀) ≡ 12                     -- LOAD-BEARING
_ = refl

_ : carried SB η₀ (burstOf e3 ins₀) ≡ 39                     -- LOAD-BEARING
_ = refl

_ : carried SB η₀ (burstOf e4 ins₀) ≡ 120                    -- LOAD-BEARING
_ = refl

----------------------------------------------------------------------
-- THE LEAF, AT A ROOT IT ANSWERS FOR.  The flattener subscribes the
-- layers the one-literal row above measures, so the rank really is
-- peeled — and this is the first row the statement has ever had inside
-- the region `opShape` admits.
----------------------------------------------------------------------

flat1 : Closed Γ₀ natᵗ
flat1 = mergeAllᵉ nothing e1

opRoot : Confirms (dry-operator (rootWitness SB flat1 ins₀) flat1 root 0 0
  (sched-init SB flat1 ins₀) (st-init flat1) refl
  (rootTri-reads SB flat1 ins₀))
opRoot = refl
