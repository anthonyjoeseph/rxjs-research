-- THE SECOND ARRIVAL, WHICH IS WHERE A SWITCH ACTUALLY CUTS.  The
-- cutting sweep put `switchAllᵉ` and `exhaustAllᵉ` on the chain and
-- both read IDENTICAL to the flatten control on every figure -- because
-- on a FIRST arrival there is no earlier inner to abandon and none
-- active to refuse, so both took the subscribing arm.  Their cut is
-- reachable only once an inner is already live, and that needs the
-- state the FIRST arrival's cascade returned.

-- AN INNER THAT OUTLIVES AN ARRIVAL MUST BE ASYNC, AND ONLY A SLOT
-- CAN BE.  Every earlier sweep innered on `ofᵉ`, which completes inside
-- the subscribe frame, so nothing was ever still live when the next
-- arrival came.  There is no async constructor in `Exp`; the one async
-- source is a scripted slot, and a `cold` with an async tail mints a
-- FRESH source on every subscribe.  So the inner here is `input` of a
-- scripted slot whose single value is timed far past the outer's, and
-- each outer emission subscribes its own live copy of it.

-- WHAT THIS BUYS THAT THE CUT SWEEP COULD NOT.  Every cutting row there
-- shrank the registry -- three entries to one, four to one -- and a
-- growth bound is satisfied by any shrinking step whatever the frames
-- did, so those rows spoke only to the length conjunct.  Here a switch
-- drops one registration and adds one, and an exhaust refuses the new
-- one and keeps the old: neither shrinks, so the size conjunct is under
-- test on these rows for the first time.

-- WHAT COULD REFUTE, and it is the registered length alone.  The
-- statement prices a registry by `pathSz?`, whose only unbounded
-- conjunct is `suc (pathLen p) ≤ B` at every frame.  A cut can only
-- refute by leaving a LONGER path registered than the subscribing frame
-- does -- an abandoned inner's entry the sweep failed to collect, say --
-- so the reading is the maximum registered length against the same
-- program built out of `mergeAllᵉ`, stepped at the same arrival.

-- WHAT THESE ROWS DO NOT BUY.  The inner is timed past the horizon so
-- that it stays live, which is what makes the cut reachable -- and it
-- means no arrival ever comes FROM an inner here.  So what an abandoned
-- inner's own arrival does, after the switch has dropped its
-- registration, is not measured by any row: the drop is read at the
-- cutting step and not at the step that would have delivered through
-- it.  `takeᵉ` is absent for the same reason it was weak in the cutting
-- sweep -- its cut shrinks the registry whichever arrival it lands on,
-- so it says nothing the size conjunct can use.

-- TARGET: chainStep-regsSz @a3d8b7
module Probed.Chain-Step-Regs-Second where

open import Data.Bool using (true; _∧_)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.List using ([]; _∷_; map; foldr; length)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; suc; _+_; _*_; _⊔_; _≤ᵇ_; _<ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx; Closed; Exp; natᵗ; ofᵉ; mapᵉ; mergeAllᵉ;
  switchAllᵉ; exhaustAllᵉ; strmᵗ; input; syncSizeᵉ)
open import Rx.Prim using (gasPad; g0; cold; after_,_)
open import Rx.Slots using (Slots; scripted; shared)
open import Rx.Evaluator using (Sched; EvalSt; subscribeE; sched-init;
  st-init; root; sched-next; cascade; cascadeLatch; chainStep; chainsOf)
open import Rx.Hop-Depth using (hopDᵉ)
open import Rx.Slot-Hop using (slotHop)
open import Verify-Budget-Sufficient.Measures using (pathLen)

Γ₃ : Ctx 3
Γ₃ = natᵗ ∷ⱽ natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

outer : Closed Γ₃ natᵗ
outer = input fzero

-- THE INNER, and it is polymorphic in the local contexts on purpose:
-- it sits under a `mapᵉ`, so it is checked in the function's own value
-- context and a `Closed` alias would pin that context to empty
inner : ∀ {Δᵍ Δ Θ} → Exp Γ₃ Δᵍ Δ Θ natᵗ
inner = input (fsuc fzero)

-- the three arms over the IDENTICAL inner, so the only thing differing
-- between the control and a cutting row is which operator flattens
mrg swi exh : Closed Γ₃ natᵗ → Closed Γ₃ natᵗ
mrg src = mergeAllᵉ nothing (mapᵉ (strmᵗ inner) src)
swi src = switchAllᵉ        (mapᵉ (strmᵗ inner) src)
exh src = exhaustAllᵉ       (mapᵉ (strmᵗ inner) src)

slots : Slots Γ₃
-- THREE outer values, so the arrival this probe steps is neither the
-- first nor the last: `cascadeFinish` drops a spent source's whole
-- registry, and a step measured there would read a sweep rather than a
-- cut.  ONE inner value, timed past every outer one (`resolve` is
-- cumulative, so the outer fires at ticks 1,2,3 and an inner subscribed
-- at tick 1 is due at 11) -- it never fires, so it is still live when
-- the second arrival lands, which is the whole point.
slots fzero               = scripted (cold [] ((after 0 , 7) ∷ (after 0 , 8) ∷ (after 0 , 9) ∷ []))
slots (fsuc fzero)        = scripted (cold [] ((after 9 , 1) ∷ []))
-- the SHARE whose def cuts, so a program rooted here meets the switch
-- BETWEEN two sinks rather than bottoming out on it
slots (fsuc (fsuc fzero)) = shared (swi outer)

sucG : Closed Γ₃ natᵗ → ℕ
sucG e = suc (syncSizeᵉ e + hopDᵉ 0 (slotHop 0 slots) e)

sub : (e : Closed Γ₃ natᵗ) → Sched Γ₃ × EvalSt e
sub e = let r = subscribeE (gasPad (sucG e) g0) e root 0 0
                           (sched-init e slots) (st-init e)
        in proj₁ (proj₂ r) , proj₂ (proj₂ r)

maxLenOf : (e : Closed Γ₃ natᵗ) → EvalSt e → ℕ
maxLenOf e st = foldr _⊔_ 0
  (map (λ en → pathLen (proj₂ (proj₂ (proj₂ en)))) (EvalSt.registry st))

-- THE FIRST ARRIVAL IS RUN, NOT CONSTRUCTED: a full `cascade`, exactly
-- as `drain` does it, so the state the second step is measured at is
-- one the evaluator actually reaches.  The second step then mirrors
-- `cascadeGo`'s own call -- `cascadeLatch`, this registration marked
-- delivered, `chainStep` -- rather than approximating it.
row : (e : Closed Γ₃ natᵗ) → ℕ × ℕ × ℕ × ℕ × ℕ
row e with sched-next (proj₁ (sub e))
... | inj₁ _         = 0 , 0 , 0 , 0 , 0
... | inj₂ (a₁ , s₁) with cascade a₁ 1 s₁ (proj₂ (sub e))
...   | (_ , s₂ , st₁) with sched-next s₂
...     | inj₁ _         = 0 , 0 , 0 , 0 , 0
...     | inj₂ (a₂ , s₃) with chainsOf a₂ st₁
...       | []            = 0 , 0 , 0 , 0 , 0
...       | (rid , c) ∷ _ =
            let st₀ = record (cascadeLatch a₂ st₁) { delivered = rid ∷ [] }
                r   = chainStep 2 a₂ c s₃ st₀
            in maxLenOf e st₀ , maxLenOf e (proj₂ (proj₂ r))
             , length (EvalSt.registry st₀)
             , length (EvalSt.registry (proj₂ (proj₂ r)))
             , length (proj₁ r)

-- HOW FAR EACH ROW GOT, so a row cannot read as covered while the
-- program never reached a SECOND `chainStep`
stage : Closed Γ₃ natᵗ → ℕ
stage e with sched-next (proj₁ (sub e))
... | inj₁ _         = 1
... | inj₂ (a₁ , s₁) with cascade a₁ 1 s₁ (proj₂ (sub e))
...   | (_ , s₂ , st₁) with sched-next s₂
...     | inj₁ _         = 2
...     | inj₂ (a₂ , _) with chainsOf a₂ st₁
...       | []          = 3
...       | _ ∷ _       = 4

lenBefore : Closed Γ₃ natᵗ → ℕ
lenBefore e = proj₁ (row e)
lenAfter : Closed Γ₃ natᵗ → ℕ
lenAfter e = proj₁ (proj₂ (row e))
regsBefore : Closed Γ₃ natᵗ → ℕ
regsBefore e = proj₁ (proj₂ (proj₂ (row e)))
regsAfter : Closed Γ₃ natᵗ → ℕ
regsAfter e = proj₁ (proj₂ (proj₂ (proj₂ (row e))))
emits : Closed Γ₃ natᵗ → ℕ
emits e = proj₂ (proj₂ (proj₂ (proj₂ (row e))))

sh₂ : Closed Γ₃ natᵗ
sh₂ = input (fsuc (fsuc fzero))

-- LEAF ROWS: the cutting frame is the root's own, so the chain bottoms
-- out on it.  `ctl` is the flatten the other two are read against.
ctl swiP exhP : Closed Γ₃ natᵗ
ctl  = mrg outer
swiP = swi outer
exhP = exh outer

-- TELESCOPE ROW: rooted at the share whose def cuts, so the fold meets
-- the switch and must still arrive at the share's own sink with
-- whatever the cut left it
deepP : Closed Γ₃ natᵗ
deepP = mergeAllᵉ nothing (ofᵉ (strmᵗ sh₂ ∷ strmᵗ sh₂ ∷ []))

packed : Closed Γ₃ natᵗ → ℕ
packed e = lenBefore e + 100 * lenAfter e + 10000 * regsBefore e
         + 1000000 * regsAfter e + 100000000 * emits e

-- EVERY ROW REACHED A SECOND `chainStep`: a plain sum, so a row that
-- stalled shows up as a wrong total rather than as a silent zero
reaches : stage ctl + stage swiP + stage exhP + stage deepP ≡ 16
reaches = refl

figuresC : packed ctl ≡ 103020202
figuresC = refl

figuresSw : packed swiP ≡ 102020202
figuresSw = refl

figuresEx : packed exhP ≡ 102020202
figuresEx = refl

figuresDp : packed deepP ≡ 304040202
figuresDp = refl

-- NO CUT LENGTHENS A REGISTERED PATH PAST ITS FLATTEN CONTROL, the
-- claim the sweep is here to test -- now read at the arrival where the
-- cut is real rather than at one where both operators subscribed.
no-longer-than-control : (lenAfter swiP ≤ᵇ lenAfter ctl)
                       ∧ (lenAfter exhP ≤ᵇ lenAfter ctl)
                       ∧ (lenAfter deepP ≤ᵇ lenAfter ctl) ≡ true
no-longer-than-control = refl

-- THE ROWS ARE NOT THE CONTROL, which is the claim the cutting sweep
-- could not make and the reason this shape exists.  There every cutting
-- operator read byte-identical to the flatten because it had taken the
-- subscribing arm; here the control registers the new inner alongside
-- the old and both cutting arms do not -- a switch dropping the
-- abandoned one as it adds, an exhaust refusing the new one outright.
-- A row that matched the control again would mean the second arrival
-- still had not reached a cut.
cut-happened : (regsAfter swiP <ᵇ regsAfter ctl)
             ∧ (regsAfter exhP <ᵇ regsAfter ctl) ≡ true
cut-happened = refl

-- AND THE SIZE CONJUNCT IS UNDER TEST, which no cutting row anywhere
-- else has managed.  Every cut in the earlier sweep SHRANK the registry
-- and a growth bound holds vacuously across a shrinking step; the
-- control here grows, and neither cutting arm shrinks below where it
-- started, so what these rows say about `regsSz?` is load-bearing.
no-shrink : (regsBefore ctl <ᵇ regsAfter ctl)
          ∧ (regsBefore swiP ≤ᵇ regsAfter swiP)
          ∧ (regsBefore exhP ≤ᵇ regsAfter exhP)
          ∧ (regsBefore deepP ≤ᵇ regsAfter deepP) ≡ true
no-shrink = refl
