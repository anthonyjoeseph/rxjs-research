-- ══════════════════════════════════════════════════════════════════
-- ONE CHAIN'S REGISTRY PRICE IN THE LEVEL CURRENCY THAT REPLACED THE
-- CAP, READ WHERE THE LEVEL CAN ACTUALLY BE OUTRUN.
--
-- WHAT THE STEP HAS TO COVER, and it is an arithmetic gap rather than
-- a program.  `Refuted.Chain-Step-Regs-Cap` measured the mechanism: a
-- subscribing frame swaps its head for a `from-inner` and pushes one
-- frame per operator of the inner, so the registered length is the
-- walked length plus the inner's operator count.  Both are bounded by
-- the entry cap -- one by `pathSz?`, the other by the `sizeᵛ` premise
-- -- so a single descent registers at most about `2·S`, while one
-- `sizeStep` buys `S·(1+2S)`.  So the step is not close at one
-- descent, and a row at one descent cannot fail.

-- WHICH AXIS CAN REFUTE, THEN.  Only one: whether a single
-- `chainStep` can push MORE than the inner's own operator count --
-- that is, whether the descent RECURSES.  If subscribing the payload
-- descends again through its own source and each descent pushes, the
-- registered length compounds with the stack while `sizeᵛ`, which is
-- `sizeᵉ` at an observable and so linear in the syntax, stays under
-- the cap.  Then one level is bought against a length that is not
-- linear in it, and the repair is refuted for the same reason the cap
-- was.  That is what `one-per-level` below is aimed at, and it is why
-- the stack is swept rather than instantiated once.

-- WHAT IS ALREADY KNOWN AND SO IS NOT SWEPT HERE.  Nesting inside the
-- EMITTED VALUE cannot do it: an inner subscription pushes
-- `from-inner`, which charges no length, so a payload nested however
-- deep leaves the fold where it was.  That was measured on the
-- rootward face, and it is why the stack below is built out of `*All`
-- operators whose SOURCES are each other -- the one shape that puts a
-- `thru-outer` frame rootward of the next -- rather than out of
-- observables nested inside a value.

-- AND WHAT IS NOT COVERED, WHICH IS A SECOND RE-ENTRY AND NOT A
-- SMALLER CASE OF THIS ONE.  `foldPath` recurses two ways: rootward
-- through the frames, which the stack below sweeps, and SIDEWAYS at a
-- `share-sink`, where it and `dispatchShare` are mutually recursive
-- and every chain registered on the share re-enters the fold with its
-- own continuation.  The programs here reach the SCRIPTED slot, never
-- the shared one, so nothing below puts a share-sink on a walked
-- path and no row here says anything about that route.  It is the
-- likelier of the two to compound, since its depth is the share
-- telescope rather than the syntax -- so read a green here as
-- covering the rootward stack alone.

-- THE ARRIVAL'S OWN `sizeᵛ` IS NOT THE QUANTITY THE DESCENT IS PAID
-- FOR, and that is a finding rather than a detail of this file.  The
-- arrival that opens a chain here comes off the SCRIPTED slot, so its
-- value is a bare nat and `sizeᵛ` of it is one, flat across the whole
-- stack -- while what the descent actually pushes is one frame per
-- operator of the MAPPED FUNCTION, which is the observable being
-- subscribed and not the value that triggered it.  A row comparing
-- the registered length against the arrival's `sizeᵛ` therefore fails
-- at every depth past the first for a reason that says nothing about
-- compounding, which is what the first draft of this file did.  The
-- inner's own size is measured here as `innerSz` and the rows are
-- stated against it.

-- WHAT IS LOAD-BEARING, AND IT IS THREE ROWS.  `reaches` pins that
-- the sweep is not vacuous -- that at every depth an arrival is
-- scheduled AND a chain hangs off it, so `row` is reading a real
-- `chainStep` rather than one of its two degenerate arms; without it
-- every figure below would read as a flat zero and green.
-- `one-per-level` is the sharp one: it asks that a descent add at
-- most one frame per flatten level, so ANY compounding fails it at
-- the depth it first appears.  `under-inner` is the loose reading the
-- step's arithmetic actually rests on -- registered length under the
-- walked length plus the inner's own size -- and it is kept because
-- it is the form the postulate is stated in, not because it is
-- strong.  The `figures` rows are DEGENERATE and said plainly: they
-- pin the five measured lengths at each depth so that a repair moving
-- any of them fails naming a number, and no figure row can refute
-- anything.

-- TARGET: foldPath-regsLen @d58775
module Probed.Chain-Step-Regs-Level where

open import Data.Bool using (true; _∧_)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.List using ([]; _∷_; map; foldr)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _⊔_; _≤ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ty; Closed; Exp; Tm; natᵗ; obs; sizeᵛ; sizeᵉ;
  syncSizeᵉ; ofᵉ; mapᵉ; mergeAllᵉ; deferᵉ; strmᵗ; nat̂; input)
open import Rx.Prim using (gasPad; g0)
open import Rx.Evaluator using (Sched; EvalSt; subscribeE; sched-init;
  st-init; root; sched-next; cascadeLatch; chainStep; chainsOf; arrTy; arrVal)
open import Rx.Slots using (Slots)
open import Rx.Hop-Depth using (hopDᵉ)
open import Rx.Slot-Hop using (slotHop)
open import Verify-Budget-Sufficient.Measures using (pathLen)
open import Refuted.Demand-Programs using (Γ₂; insF)

open import Verify-Budget-Sufficient.Regs-Fold-Len using (foldPath-regsLen)

open import Probed.Apparatus using (Confirms)
open import Probed.Fold-Regs-Row using (e₀; gp; pth; vls; evs₀; fin₀; sd₀; st₀;
  le1; le2; pv; pp; pr; foldRow)

slots : Slots Γ₂
slots = insF 1 1 2

----------------------------------------------------------------------
-- THE STACK.  `k` flattens whose sources are each other, so each puts
-- a `thru-outer` frame ROOTWARD of the next -- the one shape that can
-- deepen a registration, and the shape a recursing descent would have
-- to compound over.
----------------------------------------------------------------------

obsⁿ : ℕ → Ty → Ty
obsⁿ zero    t = t
obsⁿ (suc k) t = obs (obsⁿ k t)

vⁿ : ∀ {Θ} (k : ℕ) → Tm Γ₂ [] [] Θ (obsⁿ k natᵗ)
vⁿ zero    = nat̂ 0
vⁿ (suc k) = strmᵗ (ofᵉ (vⁿ k ∷ []))

flat : ∀ {Θ} (k : ℕ) → Exp Γ₂ [] [] Θ (obsⁿ k natᵗ) → Exp Γ₂ [] [] Θ natᵗ
flat zero    e = e
flat (suc k) e = flat k (mergeAllᵉ nothing e)

arriving : ∀ {Θ} (k : ℕ) → Exp Γ₂ [] [] Θ natᵗ
arriving k = flat k (deferᵉ (ofᵉ (vⁿ k ∷ [])))

progR : ℕ → Closed Γ₂ natᵗ
progR k = mergeAllᵉ nothing (mapᵉ (strmᵗ (arriving k)) (input (fsuc fzero)))

sucGR : ℕ → ℕ
sucGR k = suc (syncSizeᵉ (progR k) + hopDᵉ 0 (slotHop 0 slots) (progR k))

sub : (k : ℕ) → Sched Γ₂ × EvalSt (progR k)
sub k = let r = subscribeE (gasPad (sucGR k) g0) (progR k) root 0 0
                           (sched-init (progR k) slots) (st-init (progR k))
        in proj₁ (proj₂ r) , proj₂ (proj₂ r)

-- `k` is EXPLICIT because `progR` is not injective as far as the
-- unifier is concerned, so an implicit here has nothing to solve it
-- from and every consumer reports unsolved metas instead.
maxLen : ∀ (k : ℕ) → EvalSt (progR k) → ℕ
maxLen k st = foldr _⊔_ 0
  (map (λ en → pathLen (proj₂ (proj₂ (proj₂ en)))) (EvalSt.registry st))

-- THE INNER'S OWN SIZE, which is what the descent pushes against --
-- see the header block on why the arrival's `sizeᵛ` is not.
innerSz : ℕ → ℕ
innerSz k = sizeᵉ (arriving {[]} k)

----------------------------------------------------------------------
-- ONE CHAIN, OFF A STATE THE EVALUATOR REACHED.  The arrival, the
-- chain and the incoming state all come from RUNNING the program --
-- a hand-built state is not one `chainStep` can be asked about.
----------------------------------------------------------------------

-- (walked length, arrival payload size, registry max before, after)
row : (k : ℕ) → ℕ × ℕ × ℕ × ℕ
row k with sched-next (proj₁ (sub k))
... | inj₁ _        = 0 , 0 , 0 , 0
... | inj₂ (a , sd) with chainsOf a (proj₂ (sub k))
...   | []            = 0 , 0 , 0 , 0
...   | (rid , c) ∷ _ =
        let st₀ = cascadeLatch a (proj₂ (sub k))
            r   = chainStep 1 a c sd st₀
        in pathLen c , sizeᵛ (arrTy a) (arrVal a)
         , maxLen k st₀ , maxLen k (proj₂ (proj₂ r))

-- WHICH ARM `row` LANDED IN.  Three is the only reading that means a
-- `chainStep` was measured; one and two are the arms where nothing
-- was, and they return the same flat zeros a green would.
stage : ℕ → ℕ
stage k with sched-next (proj₁ (sub k))
... | inj₁ _        = 1
... | inj₂ (a , sd) with chainsOf a (proj₂ (sub k))
...   | []          = 2
...   | _ ∷ _       = 3

walked  : ℕ → ℕ
walked  k = proj₁ (row k)
payload : ℕ → ℕ
payload k = proj₁ (proj₂ (row k))
before  : ℕ → ℕ
before  k = proj₁ (proj₂ (proj₂ (row k)))
after   : ℕ → ℕ
after   k = proj₂ (proj₂ (proj₂ (row k)))

----------------------------------------------------------------------
-- THE ROWS.  Packed so a repair moving any figure fails naming a
-- number, and swept over the stack so the measured side moves.
----------------------------------------------------------------------

packed : ℕ → ℕ
packed k = walked k + 10 * payload k + 100 * before k
         + 1000 * after k + 100000 * innerSz k

-- NON-VACUITY, and it is the row every other one here rests on.  A
-- plain SUM and deliberately not a join: `stage` is at most three, so
-- eighteen across six depths forces every one of them to the arm that
-- measures a `chainStep`, whereas any clamp would read three back at
-- a depth that reached nothing.
reaches : stage 1 + stage 2 + stage 3
        + stage 4 + stage 6 + stage 8 ≡ 18
reaches = refl

-- one row per depth rather than one sum over all six: the same five
-- figures are pinned either way, and a failure names the depth that
-- moved instead of a difference nobody can read.  DEGENERATE.
figures₁ : packed 1 ≡ 803212
figures₁ = refl

figures₂ : packed 2 ≡ 1204212
figures₂ = refl

figures₃ : packed 3 ≡ 1605212
figures₃ = refl

figures₄ : packed 4 ≡ 2006212
figures₄ = refl

figures₆ : packed 6 ≡ 2808212
figures₆ = refl

figures₈ : packed 8 ≡ 3610212
figures₈ = refl

-- LOAD-BEARING AND SHARP.  A descent adds at most one frame per
-- flatten level, so a descent that RECURSES through the stack fails
-- this at the depth it first compounds -- which is the one axis that
-- can refute the level repair, and the reason the sweep goes to eight
-- rather than stopping where the arithmetic is obviously safe.
one-per-level : (after 1 ≤ᵇ walked 1 + suc 1)
              ∧ (after 2 ≤ᵇ walked 2 + suc 2)
              ∧ (after 3 ≤ᵇ walked 3 + suc 3)
              ∧ (after 4 ≤ᵇ walked 4 + suc 4)
              ∧ (after 6 ≤ᵇ walked 6 + suc 6)
              ∧ (after 8 ≤ᵇ walked 8 + suc 8) ≡ true
one-per-level = refl

-- LOAD-BEARING AND LOOSE, kept because it is the form the step's
-- arithmetic is stated in rather than because it is strong: the
-- measured side grows at one per level against four, so a descent
-- compounding mildly could still pass this where `one-per-level`
-- fails.  Read the sharp row first.
under-inner : (after 1 ≤ᵇ walked 1 + innerSz 1)
            ∧ (after 2 ≤ᵇ walked 2 + innerSz 2)
            ∧ (after 3 ≤ᵇ walked 3 + innerSz 3)
            ∧ (after 4 ≤ᵇ walked 4 + innerSz 4)
            ∧ (after 6 ≤ᵇ walked 6 + innerSz 6)
            ∧ (after 8 ≤ᵇ walked 8 + innerSz 8) ≡ true
under-inner = refl

-- AND THE TIE TO THE STATEMENT, held at the point this family shares.
-- The rows above are the READING; `foldTie` is what holds them to
-- `foldPath-regsLen` as it now reads, so a restatement of the target
-- breaks here rather than leaving the reading green about text that is
-- gone.  What the point covers, and what it does not, is stated where
-- it is paid for: `Probed.Fold-Regs-Row`.
foldTie : Confirms
  (foldPath-regsLen {e = e₀} gp 3 1 0 0 pth vls evs₀ fin₀ sd₀ st₀ 1 2
     le1 le2 pv pp pr)
foldTie = foldRow
