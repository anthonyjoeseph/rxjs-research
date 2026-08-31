-- ══════════════════════════════════════════════════════════════════
-- THE PRICE OF ONE ARRIVING INNER, at the family that killed the
-- grant's first form.  The per-value fit reads the arrival's own tower
-- plus the wrap the telescope carries; the refutation showed the first
-- summand alone is pinned at zero when the arrival is a REFERENCE, so
-- the rows here ask whether the second one pays for what substituting
-- the slot lets through.
--
-- PROBES: `refl` receipts at concrete programs.  See EVIDENCE.md.
--
-- WHAT IS LOAD-BEARING is the FLAT row, and it is the only one.  The
-- wrap is a power of two in the definition's sync size times its
-- depth, so it vanishes exactly when the definition has no `*All` in
-- it, and then the whole grant is the path's own step -- two, fixed,
-- against whatever the substitution delivers.  It reads zero, so the
-- row holds with the margin the step buys and nothing else.
--
-- THE LAYERED REFERENCE ROWS ARE DEGENERATE, and that is the
-- measurement rather than a weakness: they are the family the
-- refutation used, and the summand that repairs it does not repair it
-- marginally.  The delivery doubles per layer -- one, two, four,
-- eight -- while the grant goes a thousand and twenty-six, then
-- sixty-seven million, because the wrap is exponential in a sync size
-- that grows with the layer.  No count of layers closes that.
--
-- BLOCKED, AND THE FINDING IS THAT IT CANNOT REFUTE HERE: `deferᵉ`
-- reads depth zero whatever its body is, so a reference to a deferred
-- tower has a zero wrap and the fixed grant of two -- the shape that
-- ought to be dangerous.  It delivers nothing at all, at every layer,
-- because a consume does not unfold a defer; the subscription that
-- would is a later step.  So the hiding measure and the hidden depth
-- are invisible on the same side, and this axis is unavailable to a
-- counterexample at THIS statement rather than merely untried.
--
-- AND THE STORE CONJUNCTS ARE INSTANTIATED AND VACUOUS, which is a
-- coverage boundary rather than coverage: the store reads zero before
-- the consume and zero after it, at the flat witness and at a layered
-- one, so the two rows say only that nothing moved.  Reaching them
-- wants a consume that installs, and this harness's does not.
--
-- AND THE DUPLICATING FAMILY IS LOAD-BEARING AND SETTLES WHAT THE
-- TOWER IS FOR: over four layers the arrival's size doubles, and what
-- the consume DELIVERS reads one, two, three, four -- the arrival's
-- depth, digit for digit, with the tower contributing nothing.  So on
-- this family the grant's exponent is not standing in for the
-- delivery, which is what the entry witness saw from the other side.
--
-- NOT COVERED: a telescope of
-- more than one slot, where the sum is over slots rather than one of
-- them; and the two other operators, the arr-keyed sibling's rows
-- being what says the operator is not the axis.
--
-- TARGET: sight-thru-val @081e08
-- ══════════════════════════════════════════════════════════════════
module Probed.Sight-Thru-Val where

open import Data.Bool using (true; false; T)
open import Data.Fin using () renaming (zero to fzero)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _⊔_; _≤ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Vec using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gasPad)
open import Rx.Exp
  using (Ctx; Closed; Val; Fn; natᵗ; obs; ofᵉ; mapᵉ; mergeAllᵉ; nat̂;
         strmᵗ; varᵗ; caseᵗ; inlᵗ; input; inputsBelowᵉ; syncSizeᵛ; deferᵉ)
open import Rx.Nest-Depth using (nestDᵛ)
open import Rx.Slots using (Slots; shared)
open import Rx.Evaluator
  using (Sched; EvalSt; Path; root; _↠_; thru-outer; mergeAllᵒ;
         mergeAll-st; thruConsume; installNode; sched-init; st-init)
open import Verify-Budget-Sufficient.Nest-Store using (pathNestD; slotWrapSum)
open import Verify-Budget-Sufficient.Nest-Walk using (nestDᵛˢ; nodesMax; nodeNestAt)

Γₛ : Ctx 1
Γₛ = obs natᵗ ∷ []

gas : Gas
gas = gasPad 400 g0

prog : Closed Γₛ natᵗ
prog = ofᵉ (nat̂ 0 ∷ [])

dup : Fn Γₛ [] [] [] (obs natᵗ) (obs natᵗ)
dup = strmᵗ (mapᵉ
        (caseᵗ (inlᵗ (varᵗ (there (here refl)))) (nat̂ 0) (varᵗ (here refl)))
        (ofᵉ (varᵗ (here refl) ∷ [])))

dDup : ℕ → Closed Γₛ (obs natᵗ)
dDup zero    = ofᵉ (strmᵗ (mergeAllᵉ nothing
                 (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ []))) ∷ [])
dDup (suc k) = mapᵉ dup (mergeAllᵉ nothing (ofᵉ (strmᵗ (dDup k) ∷ [])))

sl : (d : Closed Γₛ (obs natᵗ)) → T (inputsBelowᵉ 0 d) → Slots Γₛ
sl d ok fzero = shared d {ok = ok}

sched : (d : Closed Γₛ (obs natᵗ)) → T (inputsBelowᵉ 0 d) → Sched Γₛ
sched d ok = sched-init prog (sl d ok)

κ : Path Γₛ (obs natᵗ) natᵗ
κ = thru-outer mergeAllᵒ 0 ↠ root

stM : EvalSt prog
stM = installNode 0 (mergeAll-st {t = obs natᵗ} nothing 0 [] false) (st-init prog)

-- the arrival's own tower plus the wrap the telescope carries, at the
-- one input this context has
G : Val Γₛ (obs (obs natᵗ)) → (d : Closed Γₛ (obs natᵗ)) →
    T (inputsBelowᵉ 0 d) → ℕ
G o d ok = 2 ^ syncSizeᵛ (obs (obs natᵗ)) o
             * (pathNestD κ + nestDᵛ (obs (obs natᵗ)) o)
         + 1 * slotWrapSum (sl d ok)

del : Val Γₛ (obs (obs natᵗ)) → (d : Closed Γₛ (obs natᵗ)) →
      T (inputsBelowᵉ 0 d) → ℕ
del o d ok =
  nestDᵛˢ (proj₁ (thruConsume gas mergeAllᵒ 0 κ 0 0 o (sched d ok) stM))

-- the two STORE conjuncts, at the same grant and the same consume
mx : Val Γₛ (obs (obs natᵗ)) → (d : Closed Γₛ (obs natᵗ)) →
     T (inputsBelowᵉ 0 d) → ℕ
mx o d ok =
  nodesMax (proj₂ (proj₂ (proj₂
    (thruConsume gas mergeAllᵒ 0 κ 0 0 o (sched d ok) stM))))

nAt : ℕ → Val Γₛ (obs (obs natᵗ)) → (d : Closed Γₛ (obs natᵗ)) →
      T (inputsBelowᵉ 0 d) → ℕ
nAt j o d ok =
  nodeNestAt j (proj₂ (proj₂ (proj₂
    (thruConsume gas mergeAllᵒ 0 κ 0 0 o (sched d ok) stM))))

ref : Val Γₛ (obs (obs natᵗ))
ref = input fzero

-- DEGENERATE: the reference rows, where the grant IS the wrap
fitRef : ((del ref (dDup 0) tt ≤ᵇ G ref (dDup 0) tt) ≡ true)
       × ((del ref (dDup 1) tt ≤ᵇ G ref (dDup 1) tt) ≡ true)
       × ((del ref (dDup 2) tt ≤ᵇ G ref (dDup 2) tt) ≡ true)
       × ((del ref (dDup 3) tt ≤ᵇ G ref (dDup 3) tt) ≡ true)
fitRef = refl , refl , refl , refl

-- and the two sides as numbers, so the margin is measured
sidesRef≡ : del ref (dDup 0) tt + 10 * del ref (dDup 1) tt
          + 100 * del ref (dDup 2) tt + 1000 * del ref (dDup 3) tt ≡ 8421
sidesRef≡ = refl

grantRef₀≡ : G ref (dDup 0) tt ≡ 1026
grantRef₀≡ = refl

grantRef₁≡ : G ref (dDup 1) tt ≡ 67108866
grantRef₁≡ = refl

-- the one shape where the wrap vanishes: a definition with no *All in
-- it carries depth zero, so the grant is the path's own step alone
flat : Closed Γₛ (obs natᵗ)
flat = ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ [])

grantFlat≡ : G ref flat tt ≡ 2
grantFlat≡ = refl

delFlat≡ : del ref flat tt ≡ 0
delFlat≡ = refl

-- LOAD-BEARING: the value conjunct where the grant is the step alone
fitFlat : (del ref flat tt ≤ᵇ G ref flat tt) ≡ true
fitFlat = refl

-- DEGENERATE, AND THE FIGURE BELOW IS WHY: the store does not move at
-- a consume in this family, so both conjuncts are read over a reading
-- that stood still
storeFlat : ((mx ref flat tt ≤ᵇ nodesMax stM ⊔ G ref flat tt) ≡ true)
          × ((nAt 0 ref flat tt ≤ᵇ nodeNestAt 0 stM ⊔ G ref flat tt) ≡ true)
          × ((nAt 1 ref flat tt ≤ᵇ nodeNestAt 1 stM ⊔ G ref flat tt) ≡ true)
          × ((nAt 2 ref flat tt ≤ᵇ nodeNestAt 2 stM ⊔ G ref flat tt) ≡ true)
storeFlat = refl , refl , refl , refl

storeRef : ((mx ref (dDup 1) tt ≤ᵇ nodesMax stM ⊔ G ref (dDup 1) tt) ≡ true)
         × ((nAt 0 ref (dDup 1) tt ≤ᵇ nodeNestAt 0 stM ⊔ G ref (dDup 1) tt) ≡ true)
         × ((nAt 1 ref (dDup 1) tt ≤ᵇ nodeNestAt 1 stM ⊔ G ref (dDup 1) tt) ≡ true)
storeRef = refl , refl , refl

-- and the store as a number, so the conjunct is not read over a store
-- that never moved
storeFigs≡ : nodesMax stM + 10 * mx ref flat tt
           + 100 * mx ref (dDup 1) tt ≡ 0
storeFigs≡ = refl

-- DEGENERATE: the arrival carries its own definition
fitOwn : ((del (dDup 0) (dDup 0) tt ≤ᵇ G (dDup 0) (dDup 0) tt) ≡ true)
       × ((del (dDup 1) (dDup 0) tt ≤ᵇ G (dDup 1) (dDup 0) tt) ≡ true)
       × ((del (dDup 2) (dDup 0) tt ≤ᵇ G (dDup 2) (dDup 0) tt) ≡ true)
fitOwn = refl , refl , refl

-- AND THE ONE SHAPE THAT HIDES DEPTH UNDER A ZERO WRAP: `deferᵉ` reads
-- nought whatever its body is, so the grant stays at the path's step
-- while the definition behind the reference is arbitrarily deep
hid : ℕ → Closed Γₛ (obs natᵗ)
hid k = ofᵉ (strmᵗ (deferᵉ (mergeAllᵉ nothing (dDup k))) ∷ [])

grantHid≡ : G ref (hid 3) tt ≡ 2
grantHid≡ = refl

delHid≡ : del ref (hid 0) tt + 10 * del ref (hid 1) tt
        + 100 * del ref (hid 2) tt + 1000 * del ref (hid 3) tt ≡ 0
delHid≡ = refl

-- ── the duplicating family, where the grant's exponent was outrun ───
-- The arrivals here are the ones the entry burst actually carries:
-- `Refuted.Sight-All-Stream-Dup` pins the emitted sizes and they follow
-- exactly this recurrence.  What the rows ask is which side the
-- DELIVERY tracks -- the size that doubles, or the depth that does not

vN : ℕ → Closed Γₛ natᵗ
vN zero    = mergeAllᵉ nothing (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ []))
vN (suc k) = mergeAllᵉ nothing
               (ofᵉ (strmᵗ (vN k) ∷ strmᵗ (vN k) ∷ []))

oN : ℕ → Val Γₛ (obs (obs natᵗ))
oN k = ofᵉ (strmᵗ (vN k) ∷ strmᵗ (vN k) ∷ [])

-- the three columns, packed: what is delivered, the arrival's depth,
-- and the arrival's size
dupCols : ℕ
dupCols = del (oN 0) flat tt + 100 * del (oN 1) flat tt
        + 10000 * del (oN 2) flat tt + 1000000 * del (oN 3) flat tt

dupCols≡ : dupCols ≡ 4030201
dupCols≡ = refl

dupDepth : ℕ
dupDepth = nestDᵛ (obs (obs natᵗ)) (oN 0)
         + 100 * nestDᵛ (obs (obs natᵗ)) (oN 1)
         + 10000 * nestDᵛ (obs (obs natᵗ)) (oN 2)
         + 1000000 * nestDᵛ (obs (obs natᵗ)) (oN 3)

dupDepth≡ : dupDepth ≡ 4030201
dupDepth≡ = refl
