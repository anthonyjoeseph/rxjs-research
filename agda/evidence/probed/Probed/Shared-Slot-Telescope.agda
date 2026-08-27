-- ══════════════════════════════════════════════════════════════════
-- THE SLOT ARM AT A TELESCOPE OF TWO, which is the one region the
-- staged key does any work in and the one its own receipt named as
-- uninstantiated.
--
-- EVIDENCE, not a claim: `src` cannot import this file (the library
-- layout makes the name unresolvable from there) and nothing in the
-- proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.
--
-- WHY ONE SLOT SAYS NOTHING ABOUT TWO.  At a single slot the staged
-- environment is never consulted: the definition references no input,
-- so every stage agrees and the key is just the definition's written
-- size.  The moment slot one's definition names slot zero, the key of
-- the ARRIVAL is read at an environment that already carries slot
-- zero's own closure -- and that substitution is the whole mechanism.
--
-- WHAT WOULD MAKE THE ROWS FAIL.  The upper definition wraps the lower
-- one in duplicating maps, so the delivered depth doubles per wrap
-- while the key gains only the wrap's own syntax.  If the exponent a
-- wrap buys were smaller than the doubling it causes, the family would
-- cross; the rows read both columns, so which way it goes is measured
-- rather than argued.  The lower slot is varied independently, so a
-- key that failed to see THROUGH the reference would be caught by the
-- rows that move only it.
--
-- NOT COVERED: the two store conjuncts, which this shape leaves at
-- `0 ≤ _`; a telescope of three; and a lower slot that is SCRIPTED
-- rather than shared, where the key reads the script instead.
-- ══════════════════════════════════════════════════════════════════
-- TARGET: subscribeSharedSlot-nest-arr @891d01
module Probed.Shared-Slot-Telescope where

open import Data.Bool using (T; true)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤ᵇ_)
open import Data.Product using (proj₁)
open import Data.Unit using (tt)
open import Data.Vec using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gs)
open import Rx.Exp
  using (Ctx; Closed; Val; Fn; natᵗ; obs; ofᵉ; mapᵉ; mergeAllᵉ; nat̂; input;
         strmᵗ; varᵗ; caseᵗ; inlᵗ; inputsBelowᵉ)
open import Rx.Clos-Size using (closSizeᵉ)
open import Rx.Slot-Clos using (slotClos)
open import Rx.Slots using (Slots; shared)
open import Rx.Evaluator
  using (subscribeSharedSlot; splitBurst; root; sched-init; st-init; Path; _↠_;
  thru-outer; mergeAllᵒ)
open import Verify-Budget-Sufficient.Nest-Cap using (arrD)
open import Verify-Budget-Sufficient.Nest-Store using (nestUnit)
open import Verify-Budget-Sufficient.Nest-Walk using (nestDᵛˢ)

Γₜ : Ctx 2
Γₜ = obs natᵗ ∷ obs natᵗ ∷ []

gasBig : Gas
gasBig = gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs g0)))))))))))))))

prog : Closed Γₜ natᵗ
prog = ofᵉ (nat̂ 0 ∷ [])

-- the duplicating step: it names its argument twice, so one wrap
-- doubles the delivered depth
dup : Fn Γₜ [] [] [] (obs natᵗ) (obs natᵗ)
dup = strmᵗ (mapᵉ
        (caseᵗ (inlᵗ (varᵗ (there (here refl)))) (nat̂ 0) (varᵗ (here refl)))
        (ofᵉ (varᵗ (here refl) ∷ [])))

-- SLOT ZERO: j doubling layers, referencing nothing
low : ℕ → Closed Γₜ (obs natᵗ)
low zero    = ofᵉ (strmᵗ (mergeAllᵉ nothing
                (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ []))) ∷ [])
low (suc j) = mapᵉ dup (mergeAllᵉ nothing (ofᵉ (strmᵗ (low j) ∷ [])))

-- SLOT ONE: k doubling layers over a REFERENCE to slot zero, which is
-- the edge the staged environment exists for
up : ℕ → Closed Γₜ (obs natᵗ)
up zero    = mapᵉ dup (input fzero)
up (suc k) = mapᵉ dup (mergeAllᵉ nothing (ofᵉ (strmᵗ (up k) ∷ [])))

sl : (j k : ℕ) → T (inputsBelowᵉ 0 (low j)) → T (inputsBelowᵉ 1 (up k)) →
     Slots Γₜ
sl j k oj ok fzero        = shared (low j) {ok = oj}
sl j k oj ok (fsuc fzero) = shared (up k)  {ok = ok}

κ : Path Γₜ (obs natᵗ) natᵗ
κ = thru-outer mergeAllᵒ 0 ↠ root

burstOf : (j k : ℕ) (oj : T (inputsBelowᵉ 0 (low j)))
          (ok : T (inputsBelowᵉ 1 (up k))) → ℕ
burstOf j k oj ok =
  nestDᵛˢ (proj₁ (splitBurst {A = Val Γₜ natᵗ}
    (proj₁ (subscribeSharedSlot gasBig (fsuc fzero) (up k) κ 0 0
              (sched-init prog (sl j k oj ok)) (st-init prog)))))

GOf : (j k : ℕ) (oj : T (inputsBelowᵉ 0 (low j)))
      (ok : T (inputsBelowᵉ 1 (up k))) → ℕ
GOf j k oj ok = arrD (nestUnit prog (sl j k oj ok)) 0
                  (suc (closSizeᵉ (slotClos (sl j k oj ok)) (up k)))

-- THE KEY SEES THROUGH THE REFERENCE, which is the reading the one-slot
-- rows could not take: holding the upper definition fixed and growing
-- the LOWER one still moves the key.
keysLow : ℕ
keysLow = suc (closSizeᵉ (slotClos (sl 0 0 tt tt)) (up 0))
        + 100 * suc (closSizeᵉ (slotClos (sl 1 0 tt tt)) (up 0))
        + 10000 * suc (closSizeᵉ (slotClos (sl 2 0 tt tt)) (up 0))

keysLow≡ : keysLow ≡ 533823
keysLow≡ = refl

-- AND IT CHARGES A LOWER LAYER EXACTLY WHAT IT CHARGES AN UPPER ONE --
-- the two readings land on the same three numbers, which is the
-- statement that the key does not DISCOUNT what it reaches through a
-- reference.  Fifteen units per doubling either way.
keysUp : ℕ
keysUp = suc (closSizeᵉ (slotClos (sl 0 0 tt tt)) (up 0))
       + 100 * suc (closSizeᵉ (slotClos (sl 0 1 tt tt)) (up 1))
       + 10000 * suc (closSizeᵉ (slotClos (sl 0 2 tt tt)) (up 2))

keysUp≡ : keysUp ≡ 533823
keysUp≡ = refl

fit00 : (burstOf 0 0 tt tt ≤ᵇ GOf 0 0 tt tt) ≡ true
fit00 = refl

fit20 : (burstOf 2 0 tt tt ≤ᵇ GOf 2 0 tt tt) ≡ true
fit20 = refl

fit02 : (burstOf 0 2 tt tt ≤ᵇ GOf 0 2 tt tt) ≡ true
fit02 = refl

fit22 : (burstOf 2 2 tt tt ≤ᵇ GOf 2 2 tt tt) ≡ true
fit22 = refl
