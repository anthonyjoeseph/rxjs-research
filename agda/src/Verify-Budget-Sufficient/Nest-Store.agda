------------------------------------------------------------------
-- WHERE A RUN'S NESTING IS ACTUALLY HELD, and it is not in the subject.
-- Four places, each of which can hand the sweep an observable the
-- program's syntax never mentioned: a shared slot's definition, a
-- concatAll's queue, a scan's accumulator, and a live source's pending
-- list.  `storeNestMax` is their MAX, because the sweep enters them one
-- at a time and each from its own frame.
--
-- THIS IS THE FIELD THE INVARIANT DOES NOT HAVE.  `capsOK?` bounds
-- every one of these four by a SIZE — `sizeᵛ (obs t) e` is `sizeᵉ e` —
-- and a size sits exponentially above the height cap at every level, so
-- no amount of size information bounds the nesting.  So the nesting gets
-- its own per-instant cap and its own store predicate, read at the
-- instant's own index, in the shape `stBounded?` already has.

------------------------------------------------------------------
-- THE PATH MEASURE — the one arc on a path that a subscribe spends.
-- `depthFrame` returns 0 on map-f, scan-f and take-f definitionally,
-- and 0 on `from-inner`, which is the surprising one: exiting an inner
-- charges nothing, because the `thru-outer` frame that got in already
-- bought that layer, and a unit here would double charge it.  Only
-- `thru-outer` climbs.
--
-- The frames' own FUNCTIONS are charged on top, since a step function
-- reached by substitution is syntax the subject no longer contains, and
-- a scan's is charged its fold count over — same product, same reason.
module Verify-Budget-Sufficient.Nest-Store where

open import Data.Bool using (Bool; true; false; T)
open import Data.Unit using (tt)
open import Data.List using (List; foldr; tabulate)
open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _⊔_; _≤_; _≤ᵇ_)
open import Data.Nat.Properties using (≤ᵇ⇒≤; ≤-trans; ≤-reflexive; +-mono-≤; +-assoc; +-identityʳ)
open import Data.Nat.ListAction using (sum)
open import Data.Product using (_×_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Rx.Exp using (Ctx; Closed)
open import Rx.Slots using (Slot; Slots; scripted; shared)
open import Rx.Evaluator using (map-f; scan-f; take-f; from-inner; thru-outer; Path; root; share-sink; _↠_; RegId; NodeState;
  scan-st; take-st; merge-st; concat-st; switch-st; exhaust-st; LiveSource; Sched; EvalSt;
  Arrival; cascadeLatch; Chain)
open import Rx.Prim using (Source)
open import Rx.Nest-Depth using (nestDᵉ; nestDᵗ; nestDᵛ)
open import Verify-Budget-Sufficient.Caps using (capsAt; capsH; sizeCount)

pathNestD : ∀ {n} {Γ : Ctx n} {s t} (W : ℕ) → Path Γ s t → ℕ
pathNestD W root                    = 0
pathNestD W (share-sink i)          = 0
pathNestD W (map-f f ↠ p)           = nestDᵗ W f + pathNestD W p
pathNestD W (scan-f f _ ↠ p)        = W * nestDᵗ W f + pathNestD W p
pathNestD W (take-f _ ↠ p)          = pathNestD W p
pathNestD W (from-inner _ _ _ ↠ p)  = pathNestD W p
pathNestD W (thru-outer _ _ ↠ p)    = suc (pathNestD W p)

-- A CASCADE'S CHAINS ARE A MAX, not a sum: `depthCascade` folds them
-- with `⊔`, each from the same arrival.
chainsNestD : ∀ {n} {Γ : Ctx n} {s t} (W : ℕ) →
  List (RegId × Path Γ s t) → ℕ
chainsNestD W = foldr (λ rc acc → pathNestD W (proj₂ rc) ⊔ acc) 0

-- A SCRIPTED SLOT IS OBS-FREE BY CONSTRUCTION (`isData`), so no
-- observable enters a run from outside the program and the clause is 0
-- for a reason rather than as a stub.
slotNest : ∀ {n} {Γ : Ctx n} {k t} (W : ℕ) → Slot Γ k t → ℕ
slotNest W (scripted _) = 0
slotNest W (shared d)   = nestDᵉ W d

slotsNestSum : ∀ {n} {Γ : Ctx n} (W : ℕ) → Slots Γ → ℕ
slotsNestSum {n = n} W sl = sum (tabulate {n = n} (λ i → slotNest W (sl i)))

nodeNest : ∀ {n} {Γ : Ctx n} (W : ℕ) → NodeState Γ → ℕ
nodeNest W (scan-st {t} v)    = nestDᵛ W t v
nodeNest W (concat-st q _ _)  = foldr (λ o acc → nestDᵉ W o ⊔ acc) 0 q
nodeNest W (take-st _)        = 0
nodeNest W (merge-st _ _)     = 0
nodeNest W (switch-st _ _)    = 0
nodeNest W (exhaust-st _ _)   = 0

liveNest : ∀ {n} {Γ : Ctx n} (W : ℕ) → LiveSource Γ → ℕ
liveNest W l =
  foldr (λ tv acc → nestDᵛ W (LiveSource.elemTy l) (proj₂ tv) ⊔ acc) 0
        (LiveSource.pending l)

-- THE REGISTRY IS THE FOURTH PLACE, and leaving it out was a hole rather
-- than a simplification: a cascade's chains come from the registry, so a
-- statement about `chainsOf` needs the registry charged or the premise
-- has nowhere to come from.
regsNestMax : ∀ {n} {Γ : Ctx n} {t} (W : ℕ) →
  List (RegId × Source × Chain Γ t) → ℕ
regsNestMax W =
  foldr (λ r acc → pathNestD W (proj₂ (proj₂ (proj₂ r))) ⊔ acc) 0

storeNestMax : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (W : ℕ) →
  Sched Γ → EvalSt e → ℕ
storeNestMax W sched st =
  slotsNestSum W (Sched.slots sched)
  ⊔ foldr (λ l acc → liveNest W l ⊔ acc) 0 (Sched.live sched)
  ⊔ foldr (λ kv acc → nodeNest W (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st)
  ⊔ regsNestMax W (EvalSt.registry st)

-- THE LATCH MOVES NO OBSERVABLE.  `cascadeLatch` resets the per-cascade
-- bookkeeping and may add a completed source; it never touches `nodes`,
-- and the `Sched` is not its argument — so the store's nesting is
-- literally unchanged, and the cascade row can take its premise about
-- the state its caller holds rather than about the latched one.
storeNest-latch : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (W : ℕ)
  (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
  storeNestMax W sched (cascadeLatch a st) ≡ storeNestMax W sched st
storeNest-latch W a sched st with Arrival.isLast a
... | true  = refl
... | false = refl

------------------------------------------------------------------
-- THE PER-INSTANT NESTING CAP, and it is a recurrence for the same
-- reason `capsAt` is: the quantity genuinely grows per instant, so a
-- closed form would need the width cap to be monotone in the instant
-- before the preservation statement could even be stated, whereas
-- `m ≤ m + k` is free.
--
-- THE INCREMENT IS THE INSTANT'S FOLD COUNT TIMES A SYNTACTIC WRAP
-- COUNT.  Each fold re-wraps the accumulator by at most what the
-- program's syntax and its shared defs wrap by, so the growth is a
-- PRODUCT of the two — which is exactly what the refuted syntactic
-- bounds were missing, since they offered a SUM in the two variables the
-- depth multiplies.
--
-- AND THE COUNT IS `sizeCount`, NOT `cWid`, WHICH IS THE WHOLE REASON
-- THIS CAP FITS UNDER `capsH` WHERE ITS PREDECESSORS DID NOT.  `cWid`
-- steps by `foldStep S w = S ^ suc w`, iterated once per fold, so the
-- width cap is a TOWER in the fold count and sits exponentially above
-- `capsH` at every level — a cap whose increment read it could never
-- telescope.  `sizeCount c d` is the instant's own fold count, the
-- number of frame steps `frameBlowup` runs, and `blowH`'s pooled summand
-- `2 * poolCount (towerℕ m) m` exists precisely to dominate it: it is
-- `sizeCount` with every field pooled at `towerℕ`, which is above the
-- caps by `capsAt-tower`.  So each instant's increment is under half of
-- what `capsH` gains that instant, and the sum telescopes.
-- SEALED, and it is the one part of this module that must be: `foldsAt`
-- unfolds to `sizeCount (capsAt …) (capsH …)`, so a transparent cap puts
-- the whole caps recurrence inside every type that mentions the nesting
-- premises — and those premises now sit on `caps-tick`, which the
-- instant loop applies.  Transparent, one such application drove the
-- walk face past 8 GB with no error in sight.  Nothing downstream needs
-- more than the type; the two facts that ARE needed leave the block as
-- lemmas (`nestCapAt-0`, `nestOK?-latch`, `nestOK?-store`).
abstract
  foldsAt : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) → ℕ
  foldsAt e sl id = sizeCount (capsAt e sl id) (capsH e sl id)

  nestSyn : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (W : ℕ) → ℕ
  nestSyn e sl W = suc (nestDᵉ W e + slotsNestSum W sl)

  nestCapAt : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) → ℕ
  nestCapAt e sl zero    = nestSyn e sl (foldsAt e sl zero)
  nestCapAt e sl (suc id) =
    nestCapAt e sl id + foldsAt e sl id * nestSyn e sl (foldsAt e sl id)

  nestOK? : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
    Sched Γ → EvalSt e → Bool
  nestOK? e sl id sched st =
    storeNestMax (foldsAt e sl id) sched st ≤ᵇ nestCapAt e sl id

  -- the base cap, spent by the root subscribe, whose subject IS the
  -- program and whose path is `root`
  nestCapAt-0 : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) →
    nestCapAt e sl 0
      ≡ suc (nestDᵉ (foldsAt e sl 0) e + slotsNestSum (foldsAt e sl 0) sl)
  nestCapAt-0 e sl = refl

  nestOK?-latch : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
    (id : ℕ) (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
    nestOK? e sl id sched (cascadeLatch a st) ≡ nestOK? e sl id sched st
  nestOK?-latch e sl id a sched st =
    cong (_≤ᵇ nestCapAt e sl id) (storeNest-latch (foldsAt e sl id) a sched st)

  -- reading the store bound back out of the predicate
  nestOK?-store : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
    (id : ℕ) (sched : Sched Γ) (st : EvalSt e) →
    nestOK? e sl id sched st ≡ true →
    storeNestMax (foldsAt e sl id) sched st ≤ nestCapAt e sl id
  nestOK?-store e sl id sched st h =
    ≤ᵇ⇒≤ (storeNestMax (foldsAt e sl id) sched st) (nestCapAt e sl id)
         (subst T (sym h) tt)

------------------------------------------------------------------
-- THE ONE ARITHMETIC OBLIGATION THE WHOLE CURRENCY RESTS ON, and it
-- mentions no evaluator: three quantities each under `nestCapAt` sum to
-- under `capsH`.  Three because a depth statement reads a subject, a
-- path and a store, and each of the three is bounded by the same cap.
--
-- WHY THE HEADROOM IS THERE.  `capsH` gains `2 * poolCount (towerℕ m) m`
-- per instant while `nestCapAt` gains one fold count times a syntactic
-- constant, and the pooled count IS the fold count with every field
-- pooled at `towerℕ` — above the caps by `capsAt-tower`.  So each
-- instant's increment is dominated by that instant's gain, and a
-- constant multiple is absorbed by how far `poolCount` sits above the
-- count it pools.
--
-- RECOVERY: `git show 725296e:agda/src/Verify-Budget-Sufficient/Nest-Tower.agda`
--   holds height arithmetic written for exactly this shape and
--   currency-independent: `sum2H`/`sum3H`/`sucH`/`hUp`/`hIn`/`1≤3x`/
--   `payL`/`payR` for moving a bound up a tower, and `tower-sum-tab` for
--   a slot telescope.
postulate
  nestCap-3≤capsH : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
    (id : ℕ) → 3 * nestCapAt e sl id ≤ capsH e sl id

-- three parts each under the cap, summed and paid out of the height
nest-sum-3 : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id : ℕ) (x y z : ℕ) →
  x ≤ nestCapAt e sl id → y ≤ nestCapAt e sl id → z ≤ nestCapAt e sl id →
  x + y + z ≤ capsH e sl id
nest-sum-3 e sl id x y z hx hy hz =
  ≤-trans (+-mono-≤ (+-mono-≤ hx hy) hz)
          (≤-trans (≤-reflexive (3*-expand (nestCapAt e sl id)))
                   (nestCap-3≤capsH e sl id))
  where
  3*-expand : ∀ (m : ℕ) → m + m + m ≡ 3 * m
  3*-expand m =
    trans (+-assoc m m m) (cong (λ x → m + (m + x)) (sym (+-identityʳ m)))
