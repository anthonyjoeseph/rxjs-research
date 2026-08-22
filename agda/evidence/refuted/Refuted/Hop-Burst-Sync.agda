-- THE BURST FACE'S SYNC CONJUNCT IS FALSE AT A DUPLICATING FUNCTION.
--
-- `HopsOK`'s second conjunct asks of every value a burst carries that
-- it be an observable of `syncSizeᵉ ≤ V`, and `hops-map`
-- (.Hop-Burst-Face) asks it of a map's payloads under the hypothesis
-- `syncSizeᵉ (mapᵉ f b) ≤ V`.  Those two are in different currencies.
-- The hypothesis is ADDITIVE in the function — `syncSizeᵉ (mapᵉ f e) =
-- suc (syncSizeᵗ f + syncSizeᵉ e)` — while substitution is
-- MULTIPLICATIVE in how many times the function mentions its argument,
-- `syncSizeᵗˢ` being a sum.  A function naming its argument twice
-- therefore emits a payload of about twice the source's size out of a
-- budget that paid for the source once.
--
-- WHICH IS WHY THE HOP MEASURE CARRIES `pmᵗ` AND THE SIZE CONDITION
-- DOES NOT.  `hopDᵉ`'s map clause charges `hopDᵗ f + (pmᵗ V 0 f ⊔ 1) *
-- hopDᵉ e`, an occurrence COEFFICIENT, for exactly this reason; the
-- condition sitting beside it has no such factor.  So the repair is a
-- measure of `hopDᵉ`'s shape and not a larger `V`: the witness scales
-- with the source, so no numeral survives it.
--
-- THE WITNESS IS THE SMALLEST PROGRAM THAT SEPARATES THE TWO
-- CURRENCIES.  The function is `strmᵗ (mergeAllᵉ (ofᵉ (x ∷ x ∷ [])))`,
-- which costs 6 whatever `x` is, so the map's budget is `sE + 10` for a
-- source observable of size `sE`, while the payload it substitutes into
-- is `2 * sE + 5`.  The two cross at `sE = 5` and the figures below are
-- pinned at `sE = 12`, a ten-literal list: budget 22, payload 29.
-- Widening the list moves the gap without touching the budget's shape,
-- which is what makes it a refutation of the STATEMENT rather than of
-- one arithmetic.
--
-- ⚠ AND THIS IS WHY THE FACE'S EXISTING GREEN ROW DID NOT SEE IT.
-- `Probed.Depth-Hop` § 15 reaches the substitution region with a
-- function that wraps its argument ONCE, where the additive and
-- multiplicative readings agree, and its own receipt names "a function
-- wrapping its argument more than once" as not reached.  The receipt
-- was accurate; the untested direction was the false one.
module Refuted.Hop-Burst-Sync where

open import Data.Empty using (⊥)
open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Product using (proj₁; proj₂)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl)

open import Rx.Prim using (Gas; g0; gs; Id; Tick)
open import Rx.Exp using (Ctx; Closed; Tm; Fn; natᵗ; obs; _×ᵗ_; nat̂; strmᵗ; varᵗ;
  fstᵗ; ofᵉ; mapᵉ; scanᵉ; mergeAllᵉ; syncSizeᵉ)
open import Rx.Slots using (Slots; slotsSize)
open import Rx.Evaluator using (Sched; EvalSt; Path; AllOp; NodeState; root; sched-init;
  st-init; subscribeE; subscribeAll; mergeᵒ; merge-st)
open import Rx.Hop-Depth using (hopDᵉ)
open import Rx.Slot-Hop using (slotHop)
open import Verify-Budget-Sufficient.Hop-Burst-Face using (HopsOK; burstSync?)
open import Verify-Budget-Sufficient.Caps-Depth using (depthE)
open import Verify-Budget-Sufficient.Depth-Compositional using (pathNestD)

gN : ℕ → Gas
gN zero    = g0
gN (suc n) = gs (gN n)

Γ₀ : Ctx 0
Γ₀ = []ⱽ

slots₀ : Slots Γ₀
slots₀ ()

-- ten literals, so the source observable costs 12
litsUpto : ℕ → List (Tm Γ₀ [] [] [] natᵗ)
litsUpto zero    = []
litsUpto (suc k) = nat̂ k ∷ litsUpto k

srcE : Closed Γ₀ natᵗ
srcE = ofᵉ (litsUpto 10)

-- the function names its argument TWICE, which is the whole finding
fB : Fn Γ₀ [] [] [] (obs natᵗ) (obs natᵗ)
fB = strmᵗ (mergeAllᵉ (ofᵉ (varᵗ (here refl) ∷ varᵗ (here refl) ∷ [])))

bB : Closed Γ₀ (obs natᵗ)
bB = ofᵉ (strmᵗ srcE ∷ [])

subjB : Closed Γ₀ (obs natᵗ)
subjB = mapᵉ fB bB

schedB : Sched Γ₀
schedB = sched-init subjB slots₀

stB : EvalSt subjB
stB = st-init subjB

-- the budget the hypothesis licenses, pinned so a repair moving either
-- side fails here by naming the number rather than by quietly closing
-- the gap
syncBudget : syncSizeᵉ subjB ≡ 22
syncBudget = refl

syncRow : burstSync? 22 (proj₁ (subscribeE (gN 10) subjB (root {Γ = Γ₀} {t = obs natᵗ})
                                0 0 schedB stB))
         ≡ false
syncRow = refl

hops-map-sync-absurd :
  (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
     (V : ℕ) (g : Gas) (f : Fn Γ [] [] [] s u) (b : Closed Γ s) (κ : Path Γ u t)
     (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
     2 ≤ V → syncSizeᵉ (mapᵉ f b) ≤ V → slotsSize sl ≤ V → Sched.slots sched ≡ sl →
     HopsOK V sl (hopDᵉ V (slotHop V sl) (mapᵉ f b))
       (subscribeE g (mapᵉ f b) κ bid now sched st)) → ⊥
hops-map-sync-absurd h =
  bad (trans (sym (proj₂ (h 22 (gN 10) fB bB root 0 0 slots₀ schedB stB
                            (s≤s (s≤s z≤n)) ≤-refl z≤n refl)))
             syncRow)
  where
  bad : true ≡ false → ⊥
  bad ()

-- AND THE DISPATCHER INHERITS IT, which is the half worth stating: the
-- face's own conclusion is a real body over these leaves, so the same
-- program says the FACE is false and not merely one arm of it.
subscribeE-hops-sync-absurd :
  (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
     (V : ℕ) (g : Gas) (b : Closed Γ u) (κ : Path Γ u t)
     (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
     2 ≤ V → syncSizeᵉ b ≤ V → slotsSize sl ≤ V → Sched.slots sched ≡ sl →
     HopsOK V sl (hopDᵉ V (slotHop V sl) b)
       (subscribeE g b κ bid now sched st)) → ⊥
subscribeE-hops-sync-absurd h =
  hops-map-sync-absurd (λ V g f b κ bid now sl sched st 2≤V sz slSz slEq →
    h V g (mapᵉ f b) κ bid now sl sched st 2≤V sz slSz slEq)

-- AND THE ASSEMBLY'S OWN CONCLUSION SURVIVES THE SAME WITNESS, WHICH
-- IS WHAT LOCALISES THE FINDING.  `depth-hop` (.Depth-Compositional)
-- is a real body over this face, so the natural fear is that the depth
-- bound is false too.  It is not: at the map wrapped in a `mergeAllᵉ`,
-- so the payload is actually SUBSCRIBED, the depth comes out EQUAL to
-- the bound, and equal again when the function both duplicates its
-- argument and puts it a level deeper.  `hopDᵉ`'s occurrence
-- coefficient pays for duplication exactly; only the size condition
-- beside it does not.  So the repair is confined to that condition and
-- the hop currency is left alone.
------------------------------------------------------------------

wrapB : Closed Γ₀ natᵗ
wrapB = mergeAllᵉ subjB

schedW : Sched Γ₀
schedW = sched-init wrapB slots₀

stW : EvalSt wrapB
stW = st-init wrapB

wrapDepth : depthE (gN 20) wrapB (root {Γ = Γ₀} {t = natᵗ}) 0 0 schedW stW ≡ 2
wrapDepth = refl

wrapBound : hopDᵉ 23 (slotHop 23 slots₀) wrapB
              + pathNestD (root {Γ = Γ₀} {t = natᵗ}) ≡ 2
wrapBound = refl

-- the function now duplicates AND nests, which is the shape the map
-- arm's receipt names as unreached in both directions at once
fC : Fn Γ₀ [] [] [] (obs natᵗ) (obs natᵗ)
fC = strmᵗ (mergeAllᵉ (ofᵉ (strmᵗ (mergeAllᵉ (ofᵉ (varᵗ (here refl)
       ∷ varᵗ (here refl) ∷ []))) ∷ [])))

nestB : Closed Γ₀ natᵗ
nestB = mergeAllᵉ (mapᵉ fC bB)

schedN : Sched Γ₀
schedN = sched-init nestB slots₀

stN : EvalSt nestB
stN = st-init nestB

-- 27 is the SMALLEST budget the size condition licenses here, so the
-- row is read at the tightest instance rather than a comfortable one
nestBudget : syncSizeᵉ nestB ≡ 27
nestBudget = refl

nestDepth : depthE (gN 20) nestB (root {Γ = Γ₀} {t = natᵗ}) 0 0 schedN stN ≡ 3
nestDepth = refl

nestBound : hopDᵉ 27 (slotHop 27 slots₀) nestB
              + pathNestD (root {Γ = Γ₀} {t = natᵗ}) ≡ 3
nestBound = refl

------------------------------------------------------------------
-- AND THE SCAN ARM GOES THE SAME WAY, GEOMETRICALLY.  A step function
-- naming its ACCUMULATOR twice doubles the stored observable at every
-- emission, so two source values are already enough: the budget the
-- condition licenses is 50 and the second accumulator is 63.  The
-- doubling is the same additive-budget-against-multiplicative-
-- substitution mismatch as the map arm's, one fold deeper, which is
-- what makes it a property of the CURRENCY rather than of either
-- clause.
------------------------------------------------------------------

gS : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ obs natᵗ) (obs natᵗ)
gS = strmᵗ (mergeAllᵉ (ofᵉ (fstᵗ (varᵗ (here refl))
       ∷ fstᵗ (varᵗ (here refl)) ∷ [])))

bS : Closed Γ₀ (obs natᵗ)
bS = ofᵉ (strmᵗ srcE ∷ strmᵗ srcE ∷ [])

subjS : Closed Γ₀ (obs natᵗ)
subjS = scanᵉ gS (strmᵗ srcE) bS

schedS : Sched Γ₀
schedS = sched-init subjS slots₀

stS : EvalSt subjS
stS = st-init subjS

scanBudget : syncSizeᵉ subjS ≡ 50
scanBudget = refl

scanRow : burstSync? 50 (proj₁ (subscribeE (gN 10) subjS
                                 (root {Γ = Γ₀} {t = obs natᵗ}) 0 0 schedS stS))
          ≡ false
scanRow = refl

hops-scan-sync-absurd :
  (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
     (V : ℕ) (g : Gas) (f : Fn Γ [] [] [] (u ×ᵗ s) u) (z : Tm Γ [] [] [] u)
     (b : Closed Γ s) (κ : Path Γ u t)
     (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
     2 ≤ V → syncSizeᵉ (scanᵉ f z b) ≤ V → slotsSize sl ≤ V → Sched.slots sched ≡ sl →
     HopsOK V sl (hopDᵉ V (slotHop V sl) (scanᵉ f z b))
       (subscribeE g (scanᵉ f z b) κ bid now sched st)) → ⊥
hops-scan-sync-absurd h =
  bad (trans (sym (proj₂ (h 50 (gN 10) gS (strmᵗ srcE) bS root 0 0 slots₀ schedS stS
                            (s≤s (s≤s z≤n)) ≤-refl z≤n refl)))
             scanRow)
  where
  bad : true ≡ false → ⊥
  bad ()

------------------------------------------------------------------
-- AND THE `*All` ARM INHERITS IT WITHOUT ANY ARITHMETIC OF ITS OWN,
-- which is the reason the whole conjunct has to go rather than three of
-- its five arms.  The operator subscribes an INNER and republishes the
-- inner's values, so an inner that is itself a duplicating map hands
-- the arm a payload its own condition never sized.  Nothing about the
-- four operators enters: the outer is one literal inner and the budget
-- is the smallest the condition admits.
------------------------------------------------------------------

bA : Closed Γ₀ (obs (obs natᵗ))
bA = ofᵉ (strmᵗ subjB ∷ [])

schedA : Sched Γ₀
schedA = sched-init subjB slots₀

stA : EvalSt subjB
stA = st-init subjB

allBudget : syncSizeᵉ bA ≡ 25
allBudget = refl

allRow : burstSync? 26 (proj₁ (subscribeAll (gN 10) mergeᵒ (merge-st 0 false) bA
                                (root {Γ = Γ₀} {t = obs natᵗ}) 0 0 schedA stA))
         ≡ false
allRow = refl

hops-all-sync-absurd :
  (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
     (V : ℕ) (g : Gas) (op : AllOp) (ns : NodeState Γ)
     (b : Closed Γ (obs u)) (κ : Path Γ u t)
     (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
     2 ≤ V → suc (syncSizeᵉ b) ≤ V → slotsSize sl ≤ V → Sched.slots sched ≡ sl →
     HopsOK V sl (suc (hopDᵉ V (slotHop V sl) b))
       (subscribeAll g op ns b κ bid now sched st)) → ⊥
hops-all-sync-absurd h =
  bad (trans (sym (proj₂ (h 26 (gN 10) mergeᵒ (merge-st 0 false) bA root 0 0 slots₀ schedA stA
                            (s≤s (s≤s z≤n)) ≤-refl z≤n refl)))
             allRow)
  where
  bad : true ≡ false → ⊥
  bad ()
