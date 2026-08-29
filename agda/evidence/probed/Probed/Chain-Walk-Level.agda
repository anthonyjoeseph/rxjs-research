-- WHAT THE WALK ASSERTS AT THE STATES BETWEEN THE FRAMES, which the
-- fit rows either side of a step cannot see.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.
-- TARGET: arr-chain-caps @620ba7
--
-- WHAT IS BEING TESTED.  The target hands one chain's walk a level and
-- asserts `capsOK?` at `frameStep Lv` of the instant's cap at EVERY
-- state the walk passes through, not merely at the two ends.  Those
-- middle states are not returned by anything -- the fold consumes them
-- -- so the rows below re-walk the path with the evaluator's own
-- `stepFrame`, which is the same function the predicate recurses on,
-- and read the conjunct at each one.
--
-- AND THE LEVEL IS READ AS A CONSTANT, WHICH IS WHY THE ROWS EXIST AT
-- ALL.  The predicate lets the level GROW frame by frame; a constant
-- one that covers the whole walk therefore SATISFIES it, with every
-- increment after the first taken as zero.  Reading it that way is not
-- a simplification, it is the only reachable form: the level enters the
-- width component as an iterated exponential whose base is the size, so
-- two levels of an already small cap is a numeral of six digits and
-- three is past anything Agda will normalise.
--
-- AND THE ANSWER IS THE SAME ONE LEVEL, WITH THE FLAT READING FAILING
-- INSIDE THE WALK RATHER THAN AT ITS END.  This chain's path is three
-- frames, so the spine is four states.  Read flat, the first two hold
-- and the last two do not -- so the walk leaves the cap PART WAY, which
-- is a state the fit rows either side of a step cannot see and which no
-- end-to-end reading would have reported.  Read one level up, all four
-- hold.  Both rows are load-bearing in opposite directions: the flat
-- one could have come back all-true and does not, the levelled one
-- could have come back with a false and does not.
--
-- AND WHAT THE ROWS SAY NOTHING ABOUT IS WHERE THE LEVEL COMES FROM.
-- They read the predicate's demand at a level handed in, so they
-- measure how far a walk carries a level and not whether a caller can
-- pay for one.  The target's level premise is that account, and it is
-- stated in deliveries rather than levels; no row here instantiates it.
--
-- WHAT THESE ROWS DO NOT REACH.  The other conjuncts of the same
-- predicate -- the values' caps past the first frame, the frame's
-- closure receipt, the parked drain's two size bounds, the sink arm's
-- registry-versus-unit -- are `Set`-valued or quantified over a queue
-- and are not booleans a row can pin.  Nor is the ceiling: what a
-- constant level meets is the `⊔` branch the cap's own size supplies,
-- since `sizeCount` is sealed.  And one family, one chain, one instant.
module Probed.Chain-Walk-Level where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Closed; Ctx; Val; natᵗ)
open import Rx.Prim using (gasPad; g0; Gas; Id; Tick)
open import Rx.Evaluator
  using (Sched; EvalSt; Path; root; share-sink; _↠_; stepFrame; budgetAt; subscribeE; sched-init;
  st-init; sched-next; cascade; cascadeLatch; chainsOf; Arrival; arrVal)
open import Rx.Slots using (Slots)

open import Verify-Budget-Sufficient.Demand-Programs using (Γ₂; progU; insF; sucGU)
open import Verify-Budget-Sufficient.Caps using (Caps; caps; frameStep)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (capsOK?)

-- the predicate's own `capsOK?` spine, re-walked: one boolean per state
-- the fold passes through, read at a level held constant
walkSpine : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (Lv : ℕ) (sf : Gas) (id : Id) (now : Tick)
  (p : Path Γ u t) (vals : List (Val Γ u)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) → List Bool
walkSpine c Lv sf id now root           vals fin sched st =
  capsOK? (frameStep Lv c) sched st ∷ []
walkSpine c Lv sf id now (share-sink i) vals fin sched st =
  capsOK? (frameStep Lv c) sched st ∷ []
walkSpine c Lv sf id now (f ↠ p) vals fin sched st =
  capsOK? (frameStep Lv c) sched st ∷
  walkSpine c Lv sf id now p (proj₁ step)
    (proj₁ (proj₂ (proj₂ step)))
    (proj₁ (proj₂ (proj₂ (proj₂ step))))
    (proj₂ (proj₂ (proj₂ (proj₂ step))))
  where step = stepFrame sf id now f p vals fin sched st

pU : Closed Γ₂ natᵗ
pU = progU 2 2

slU : Slots Γ₂
slU = insF 1 2 2

entry : Sched Γ₂ × EvalSt pU
entry =
  let r = subscribeE (gasPad (sucGU 1 2 2 2 2) g0) pU root 0 0
            (sched-init pU slU) (st-init pU)
  in proj₁ (proj₂ r) , proj₂ (proj₂ r)

after1 : Sched Γ₂ × EvalSt pU
after1 with sched-next (proj₁ entry)
... | inj₁ _        = entry
... | inj₂ (a , sd) =
  let r = cascade a 1 sd (proj₂ entry)
  in proj₁ (proj₂ r) , proj₂ (proj₂ r)

capU : Caps
capU = caps 26 4 4

spineAt : ℕ → List Bool
spineAt Lv with sched-next (proj₁ after1)
... | inj₁ _        = []
... | inj₂ (a , sd) with chainsOf a (proj₂ after1)
...   | []            = []
...   | (rid , p) ∷ _ =
  let st₁ = record (cascadeLatch a (proj₂ after1))
              { delivered = rid ∷ EvalSt.delivered (cascadeLatch a (proj₂ after1)) }
  in walkSpine capU Lv (budgetAt pU slU 1) 1 (Arrival.tick a) p
       (arrVal a ∷ []) (Arrival.isLast a) sd st₁

spine0 : List Bool
spine0 = spineAt 0

spine1 : List Bool
spine1 = spineAt 1

flat-row : spine0 ≡ true ∷ true ∷ false ∷ false ∷ []
flat-row = refl

lvl1-row : spine1 ≡ true ∷ true ∷ true ∷ true ∷ []
lvl1-row = refl
