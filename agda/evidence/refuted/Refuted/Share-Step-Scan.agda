-- ══════════════════════════════════════════════════════════════════
-- A SCAN UNDER A SHARE RAISES THE CEILING THE STEP IS SUPPOSED TO
-- PRESERVE.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE`
-- notes.
--
-- WHAT THE STATEMENTS SAID.  A share's dispatch and a chain's frame
-- each carry a position ceiling forward: the ceiling read after the
-- move is at most the ceiling read before it.  The ceiling is a
-- function of the program size, the nesting of the values in hand, the
-- store measure and a unit, and of those four only the store is free to
-- move under a step -- so both statements are exactly the claim that a
-- step does not deepen the store.
--
-- WHY IT LOOKED RIGHT.  `storeSyncMax` maximises over three places, and
-- two of the frame arms cannot touch any of them: a map returns the
-- schedule and store it was handed, and a take only ever shrinks them
-- -- it drops registrations, sweeps the live set and writes a numeral.
-- The arms that a corpus of one-shot defs actually heads a chain with
-- are those two and the subscribing pair, so a family of rows can stand
-- at the statement and every one of them hold.
--
-- WHERE IT BREAKS.  A scan writes its node back carrying a fresh
-- ACCUMULATOR, and the nodes are one of the three places the store
-- measure reads.  At an accumulator typed `obs u` that value carries
-- nesting of its own, and a step function wrapping the previous
-- accumulator in one more layer per delivered value deepens it by
-- construction.  Nothing about the share is doing the work: the scan
-- would raise it anywhere, and a share is only what puts a `foldPath`
-- around it.
--
-- THE WITNESS is a two-slot vocabulary whose second slot is a share
-- over an EMPTY HOT -- a def that never fires and so never completes,
-- which is what leaves a registration alive past the connect that
-- writes it -- with a scan between that share and the root fan.  Three
-- values are delivered along the admitted chain.  The store goes two to
-- three across the fold, and the ceiling follows it up.
--
-- AND ONE WITNESS KILLS BOTH, because the two statements are denominated
-- in the same currency: the step half reads the nesting of what the
-- frame EMITS where the fold half reads what arrived, and a scan emits
-- its accumulator, so that side moves as well and by more.
--
-- WHAT THIS DOES NOT SHOW.  Nothing here says the ceiling is the wrong
-- invariant, and nothing here reaches the fold obligation stated over
-- `depthFold`, which is barred from instantiation for its own reason.
-- What dies is preservation: a scan's step has to be PRICED, the way
-- the growth statement one level up already prices a cascade -- a
-- factor times the store plus an increment, not the store.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Share-Step-Scan where

open import Data.Bool using (false)
open import Data.Empty using (⊥)
open import Data.Fin using (zero) renaming (suc to fsuc)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; suc; _+_; _*_; _≤_)
open import Data.Nat.Properties using (≤⇒≤ᵇ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Vec using (lookup)
open import Data.List renaming (length to lengthL) using ()
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; hot)
open import Rx.Exp using (Val; Closed; Fn; natᵗ; obs; _×ᵗ_;
  input; ofᵉ; mergeAllᵉ; scanᵉ; strmᵗ; fstᵗ; varᵗ; sizeᵉ)
open import Rx.Slots using (Slots; scripted; shared)
open import Rx.Evaluator
  using (Sched; EvalSt; RegId; Path; root; share-sink; _↠_;
         map-f; scan-f; take-f; from-inner; thru-outer;
         subscribeE; sched-init; st-init; shareAdmit; budgetAt;
         foldPath; stepFrame)

open import Refuted.Demand-Programs using (Γ₂)
open import Verify-Budget-Sufficient.Nest-Store
  using (storeSyncMax; sightCeil; nestUnit)
open import Verify-Budget-Sufficient.Nest-Walk using (nestDᵛˢ)

-- THE VOCABULARY.  Slot one is a share whose def is an empty hot, so
-- `sharedConnect` cannot see a completed burst and does not drop what
-- it registered; slot nought is the scripted source that def names.
slots : Slots Γ₂
slots zero              = scripted {ok = tt} (hot [])
slots (fsuc zero)       = shared (input zero) {ok = tt}
slots (fsuc (fsuc ()))

-- one more `mergeAll` layer per delivered value, in the accumulator
wrapAcc : Fn Γ₂ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
wrapAcc = strmᵗ (mergeAllᵉ nothing (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ [])))

prog : Closed Γ₂ natᵗ
prog = mergeAllᵉ nothing (scanᵉ wrapAcc (strmᵗ (ofᵉ [])) (input (fsuc zero)))

sf : Gas
sf = budgetAt prog slots 0

sub : Sched Γ₂ × EvalSt prog
sub = let r = subscribeE sf prog root 0 0 (sched-init prog slots) (st-init prog)
      in proj₁ (proj₂ r) , proj₂ (proj₂ r)

-- the registrations the share admits, at the state and schedule the
-- same subscribe returned -- not an assembled pair
adms : List (RegId × Path Γ₂ natᵗ natᵗ)
adms = shareAdmit (fsuc zero) (EvalSt.registry (proj₂ sub))

vals : List (Val Γ₂ (lookup Γ₂ (fsuc zero)))
vals = 3 ∷ 4 ∷ 5 ∷ []

-- WHICH ARM THE ROW STANDS AT, so the finding cannot be read as being
-- about some other head that happened to be admitted
pathTag : ∀ {v t} → Path Γ₂ v t → ℕ
pathTag root                   = 0
pathTag (share-sink _)         = 1
pathTag (map-f _ ↠ _)          = 2
pathTag (scan-f _ _ ↠ _)       = 3
pathTag (take-f _ ↠ _)         = 4
pathTag (from-inner _ _ _ ↠ _) = 5
pathTag (thru-outer _ _ ↠ _)   = 6

pathEnd : ∀ {v t} → Path Γ₂ v t → ℕ
pathEnd root           = 0
pathEnd (share-sink _) = 1
pathEnd (_ ↠ p)        = pathEnd p

census : ℕ
census with adms
... | []          = 0
... | (_ , p) ∷ _ = lengthL adms + 10 * suc (pathTag p) + 1000 * pathEnd p

-- one entry, scan headed, sinking at the root
census≡41 : census ≡ 41
census≡41 = refl

-- THE FIGURES, all off states the evaluator reached.  Packed into one
-- tuple because they are read at one point and a second traversal would
-- be a second point: the store either side of the fold, the ceiling
-- either side of it, and the ceiling after the frame's own step.  The
-- path indices stay general so that the two ends of a chain are cases
-- at all -- at the concrete pair the sink end does not unify.
figsAt : ∀ {v} → RegId → Path Γ₂ v natᵗ → List (Val Γ₂ v) → ℕ × ℕ × ℕ × ℕ × ℕ
figsAt _ root           _  = 0 , 0 , 0 , 0 , 0
figsAt _ (share-sink _) _  = 0 , 0 , 0 , 0 , 0
figsAt rid (f ↠ p′) vs =
  storeBefore , storeAfter , ceil storeBefore , ceil storeAfter , chainAfter
  where
  sc  = proj₁ sub
  sto = proj₂ sub

  fold = foldPath sf 8 0 0 1 (f ↠ p′) vs [] false sc
           (record sto { delivered = rid ∷ EvalSt.delivered sto })

  step = stepFrame sf 0 0 f p′ vs false sc sto

  storeBefore storeAfter : ℕ
  storeBefore = storeSyncMax sc sto
  storeAfter  = storeSyncMax (proj₁ (proj₂ fold)) (proj₂ (proj₂ fold))

  ceil : ℕ → ℕ
  ceil s = sightCeil (sizeᵉ prog) (nestDᵛˢ vs) s (nestUnit prog slots)

  chainAfter : ℕ
  chainAfter = sightCeil (sizeᵉ prog)
                 (nestDᵛˢ (proj₁ step))
                 (storeSyncMax (proj₁ (proj₂ (proj₂ (proj₂ step))))
                               (proj₂ (proj₂ (proj₂ (proj₂ step)))))
                 (nestUnit prog slots)

figs : ℕ × ℕ × ℕ × ℕ × ℕ
figs with adms
... | []            = 0 , 0 , 0 , 0 , 0
... | (rid , p) ∷ _ = figsAt rid p vals

storeBefore storeAfter ceilBefore ceilAfter chainAfter : ℕ
storeBefore = proj₁ figs
storeAfter  = proj₁ (proj₂ figs)
ceilBefore  = proj₁ (proj₂ (proj₂ figs))
ceilAfter   = proj₁ (proj₂ (proj₂ (proj₂ figs)))
chainAfter  = proj₂ (proj₂ (proj₂ (proj₂ figs)))

-- THE STORE, PINNED EITHER SIDE.  Spelled out so that a repair moving
-- either side fails here, naming the number, rather than quietly
-- turning a crossing into an equality
storeBefore≡2 : storeBefore ≡ 2
storeBefore≡2 = refl

storeAfter≡3 : storeAfter ≡ 3
storeAfter≡3 = refl

-- and the ceilings the two statements are actually about
ceilBefore≡78 : ceilBefore ≡ 78
ceilBefore≡78 = refl

ceilAfter≡91 : ceilAfter ≡ 91
ceilAfter≡91 = refl

-- the step half moves further, because the values it reads are the
-- accumulator rather than what arrived
chainAfter≡130 : chainAfter ≡ 130
chainAfter≡130 = refl

-- the fold half: one `foldPath` along an admitted chain
share-step-scan-absurd : ceilAfter ≤ ceilBefore → ⊥
share-step-scan-absurd h = ≤⇒≤ᵇ h

-- the step half: the same chain's own frame, whose emitted values carry
-- the accumulator and so move the left side twice over
chain-fit-scan-absurd : chainAfter ≤ ceilBefore → ⊥
chain-fit-scan-absurd h = ≤⇒≤ᵇ h
