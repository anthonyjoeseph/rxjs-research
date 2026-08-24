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
-- THE DENOMINATION LAW, and every one of this currency's dead
-- predecessors broke it: NO CAP-SIDE NUMBER MAY ENTER A STORE MEASURE
-- OR AN INCREMENT.  A fold count, a cap width, a pooled count — each is
-- defined off the caps recurrence, whose fields step by `foldStep`'s
-- exponentiation once per budgeted fold, so every cap-side quantity
-- TOWERS past the height it would have to fit under; and a measure
-- parametrised by one moves denomination with the instant, so a
-- preservation step prices its increment in last instant's currency
-- against a store read in this instant's.  The REAL dynamics are
-- smaller by construction: an instant's actual deliveries fan out
-- through actually-installed nodes, so real widths and real layer
-- growth are EXPONENTIAL per instant in program-shaped quantities,
-- while `capsH` gains `blowH`'s pooled summand — a tower — per instant.
-- So the store is measured in RAW layers, the increment is priced by a
-- real-width recurrence, and the height's headroom is tower-vs-
-- exponential rather than the tower-vs-tower race the predecessors
-- lost.

------------------------------------------------------------------
-- THE PATH MEASURE — the one arc on a path that a subscribe spends.
-- `depthFrame` returns 0 on map-f, scan-f and take-f definitionally,
-- and 0 on `from-inner`, which is the surprising one: exiting an inner
-- charges nothing, because the `thru-outer` frame that got in already
-- bought that layer, and a unit here would double charge it.  Only
-- `thru-outer` climbs.
--
-- The frames' own FUNCTIONS are charged on top, since a step function
-- reached by substitution is syntax the subject no longer contains; on
-- any one chain each frame's function is entered once, so it is charged
-- once — what its folds pile onto the accumulator is in the store.
module Verify-Budget-Sufficient.Nest-Store where

open import Data.Bool using (Bool; true; false; T)
open import Data.Unit using (tt)
open import Data.List using (List; foldr; tabulate)
open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _^_; _⊔_; _≤_; _≤ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (≤ᵇ⇒≤; ≤-trans; ≤-reflexive; +-mono-≤; +-assoc; +-identityʳ)
open import Data.Nat.ListAction using (sum)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Rx.Exp using (Ctx; Closed)
open import Rx.Slots using (Slot; Slots; scripted; shared)
open import Rx.Evaluator using (map-f; scan-f; take-f; from-inner; thru-outer; Path; root; share-sink; _↠_; RegId; NodeState;
  scan-st; take-st; flatten-st; switch-st; exhaust-st; LiveSource; Sched; EvalSt;
  Arrival; cascadeLatch; Chain; capsBase; cascadeFinish; blowH)
open import Rx.Prim using (Source; towerℕ)
open import Rx.Nest-Depth using (nestDᵉ; nestDᵗ; nestDᵛ)
open import Decide using (≤ᵇ-true)
open import Verify-Budget-Sufficient.Caps using (capsH; 3≤capsH; tower-le-blowH)

pathNestD : ∀ {n} {Γ : Ctx n} {s t} → Path Γ s t → ℕ
pathNestD root                    = 0
pathNestD (share-sink i)          = 0
pathNestD (map-f f ↠ p)           = nestDᵗ f + pathNestD p
pathNestD (scan-f f _ ↠ p)        = nestDᵗ f + pathNestD p
pathNestD (take-f _ ↠ p)          = pathNestD p
pathNestD (from-inner _ _ _ ↠ p)  = pathNestD p
pathNestD (thru-outer _ _ ↠ p)    = suc (pathNestD p)

-- A CASCADE'S CHAINS ARE A MAX, not a sum: `depthCascade` folds them
-- with `⊔`, each from the same arrival.
chainsNestD : ∀ {n} {Γ : Ctx n} {s t} →
  List (RegId × Path Γ s t) → ℕ
chainsNestD = foldr (λ rc acc → pathNestD (proj₂ rc) ⊔ acc) 0

-- A SCRIPTED SLOT IS OBS-FREE BY CONSTRUCTION (`isData`), so no
-- observable enters a run from outside the program and the clause is 0
-- for a reason rather than as a stub.
slotNest : ∀ {n} {Γ : Ctx n} {k t} → Slot Γ k t → ℕ
slotNest (scripted _) = 0
slotNest (shared d)   = nestDᵉ d

slotsNestSum : ∀ {n} {Γ : Ctx n} → Slots Γ → ℕ
slotsNestSum {n = n} sl = sum (tabulate {n = n} (λ i → slotNest (sl i)))

nodeNest : ∀ {n} {Γ : Ctx n} → NodeState Γ → ℕ
nodeNest (scan-st {t} v)    = nestDᵛ t v
nodeNest (flatten-st _ _ q _) = foldr (λ o acc → nestDᵉ o ⊔ acc) 0 q
nodeNest (take-st _)        = 0
nodeNest (switch-st _ _)    = 0
nodeNest (exhaust-st _ _)   = 0

liveNest : ∀ {n} {Γ : Ctx n} → LiveSource Γ → ℕ
liveNest l =
  foldr (λ tv acc → nestDᵛ (LiveSource.elemTy l) (proj₂ tv) ⊔ acc) 0
        (LiveSource.pending l)

-- THE REGISTRY IS THE FOURTH PLACE, and leaving it out was a hole rather
-- than a simplification: a cascade's chains come from the registry, so a
-- statement about `chainsOf` needs the registry charged or the premise
-- has nowhere to come from.
regsNestMax : ∀ {n} {Γ : Ctx n} {t} →
  List (RegId × Source × Chain Γ t) → ℕ
regsNestMax =
  foldr (λ r acc → pathNestD (proj₂ (proj₂ (proj₂ r))) ⊔ acc) 0

storeNestMax : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} →
  Sched Γ → EvalSt e → ℕ
storeNestMax sched st =
  slotsNestSum (Sched.slots sched)
  ⊔ foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched)
  ⊔ foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st)
  ⊔ regsNestMax (EvalSt.registry st)

-- THE LATCH MOVES NO OBSERVABLE.  `cascadeLatch` resets the per-cascade
-- bookkeeping and may add a completed source; it never touches `nodes`,
-- and the `Sched` is not its argument — so the store's nesting is
-- literally unchanged, and the cascade row can take its premise about
-- the state its caller holds rather than about the latched one.
storeNest-latch : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
  storeNestMax sched (cascadeLatch a st) ≡ storeNestMax sched st
storeNest-latch a sched st with Arrival.isLast a
... | true  = refl
... | false = refl

-- AND THE FINISH ONLY DROPS.  `cascadeFinish` either returns its inputs
-- untouched or removes the spent source's registrations and sweeps the
-- live list down to what survives them; the slot sum and the node table
-- are not its arguments in either branch.  Every summand of the store
-- measure is a ⊔-fold over a list, so a step that only shortens lists
-- cannot raise it, which is why the growth statement one level up needs
-- nothing from this end of the cascade.
--
-- TWIN: `cascadeFinish-caps` — the same preservation across the same
--   two branches on the size face, proven, and its `true` arm is a
--   single lemma about exactly the two list operations this one needs.
postulate
  storeNest-finish : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
    let r = cascadeFinish a sched st
    in storeNestMax (proj₁ r) (proj₂ r) ≤ storeNestMax sched st

-- THE SYNTACTIC FACTOR: the most any single fold can wrap an
-- accumulator by, read off the program and its shared defs — a step
-- function is syntax from one of exactly those two places.
nestSyn : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) → ℕ
nestSyn e sl = suc (nestDᵉ e + slotsNestSum sl)

------------------------------------------------------------------
-- THE PER-INSTANT NESTING CAP AND THE REAL-WIDTH BUDGET, one paired
-- recurrence, because each reads the other: an instant's layer growth
-- is (per-node deliveries) × (wrap per fold), and per-node deliveries
-- are real burst widths, which next instant are at most the old widths
-- fanned through the layers a chain can now cross.
--
-- THE WIDTH BUDGET IS REAL-DENOMINATED, NOT A CAP.  `cWid` steps by
-- `foldStep S w = S ^ suc w` once per BUDGETED fold, so it towers past
-- `capsH` at every level and no increment reading it can telescope —
-- that scale mismatch, in five different currencies, is what killed
-- every predecessor of this module.  Real widths have no such step:
-- one arrival fans through actually-installed nodes, multiplying by at
-- most a stored width per layer crossed, so one instant costs at most
-- one exponential — and `capsH` gains `blowH`'s pooled summand, a
-- tower, per instant.  The bet this recurrence carries is exactly
-- that: EXPONENTIAL-PER-INSTANT COVERS THE REAL DYNAMICS.  Every
-- definition reads only program-shaped quantities (`nestSyn`,
-- `capsBase`), never the caps recurrence, so nothing can drag
-- `frameBlowup` into a type.
--
-- THE BLOCK IS SEALED BECAUSE A CAP OR A MEASURE ON THIS SPINE MUST
-- BE, and this is both.  The standing tell is met exactly: the body
-- reaches a family the tower already seals for cost, `capsBase` being
-- the base width.  A cap is worse than an ordinary body here because
-- it lands in TYPES — `nestCapAt` is named in the premise of every
-- statement carrying the nesting invariant, so a transparent one is
-- renormalised at each of their application sites, and `nestOK?`
-- additionally puts `storeNestMax` of an EVALUATOR STATE on the
-- conversion path wherever a consumer instantiates it at a cascade's
-- output.  The consumer-facing equations are proven inside the block,
-- so a probe of this bet takes its cap value through those or
-- hypothesises the growth side, as the expired probe series did.
--
-- `capsH` IS `blowH` OF SOMETHING AT EVERY INDEX, and this names that
-- something: the height the caps recurrence had reached one instant
-- earlier, which at the entry is its base.  It exists because the only
-- handle anything has ever had on `blowH` is a lemma taking that
-- argument, and the caps recurrence itself never needs to say it -- it
-- iterates, so it never looks back one step.
capsHpred : ∀ {n} {Γ : Ctx n} {t} → Closed Γ t → Slots Γ → ℕ → ℕ
capsHpred e sl zero     = capsBase e sl
capsHpred e sl (suc id) = capsH e sl id

capsH-blow : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  capsH e sl id ≡ blowH (capsHpred e sl id)
capsH-blow e sl zero     = refl
capsH-blow e sl (suc id) = refl

1≤capsHpred : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  1 ≤ capsHpred e sl id
1≤capsHpred e sl zero     = s≤s z≤n
1≤capsHpred e sl (suc id) = ≤-trans (s≤s z≤n) (3≤capsH e sl id)

-- THE BASE WIDTH IS `capsBase` BECAUSE IT CARRIES THE ENTRY CEILING —
-- the one static width reading the tower already pays for — and the
-- base cap is the program's own layers, spent by the root subscribe.
abstract
  nwAt : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) → ℕ × ℕ
  nwAt e sl zero    = nestSyn e sl , capsBase e sl
  nwAt e sl (suc id) =
    let c = proj₁ (nwAt e sl id)
        w = proj₂ (nwAt e sl id)
        c′ = c + w * nestSyn e sl
    in c′ , suc w ^ suc c′

  nestCapAt : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) → ℕ
  nestCapAt e sl id = proj₁ (nwAt e sl id)

  realWidAt : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) → ℕ
  realWidAt e sl id = proj₂ (nwAt e sl id)

  nestOK? : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
    Sched Γ → EvalSt e → Bool
  nestOK? e sl id sched st = storeNestMax sched st ≤ᵇ nestCapAt e sl id

  -- the base cap, spent by the root subscribe, whose subject IS the
  -- program and whose path is `root`
  nestCapAt-0 : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) →
    nestCapAt e sl 0 ≡ suc (nestDᵉ e + slotsNestSum sl)
  nestCapAt-0 e sl = refl

  nestOK?-latch : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
    (id : ℕ) (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
    nestOK? e sl id sched (cascadeLatch a st) ≡ nestOK? e sl id sched st
  nestOK?-latch e sl id a sched st =
    cong (_≤ᵇ nestCapAt e sl id) (storeNest-latch a sched st)

  -- reading the store bound back out of the predicate
  nestOK?-store : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
    (id : ℕ) (sched : Sched Γ) (st : EvalSt e) →
    nestOK? e sl id sched st ≡ true →
    storeNestMax sched st ≤ nestCapAt e sl id
  nestOK?-store e sl id sched st h =
    ≤ᵇ⇒≤ (storeNestMax sched st) (nestCapAt e sl id)
         (subst T (sym h) tt)

  -- and putting one back in: the seal means a consumer cannot reach the
  -- predicate's `≤ᵇ` itself, so the introduction has to be exported
  -- beside the elimination or a body proving the bound has no way to
  -- state that it did
  nestOK?-intro : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
    (id : ℕ) (sched : Sched Γ) (st : EvalSt e) →
    storeNestMax sched st ≤ nestCapAt e sl id →
    nestOK? e sl id sched st ≡ true
  nestOK?-intro e sl id sched st h =
    ≤ᵇ-true (storeNestMax sched st) (nestCapAt e sl id) h

  -- THE STEP, and it is the whole content of the currency: one instant
  -- buys exactly its real width times the wrap factor.  A consumer
  -- proving a preservation step needs this to say that what it proved
  -- IS the next cap, and outside the block nothing else can.
  nestCapAt-suc : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
    (id : ℕ) →
    nestCapAt e sl (suc id)
      ≡ nestCapAt e sl id + realWidAt e sl id * nestSyn e sl
  nestCapAt-suc e sl id = refl

  -- THE HEIGHT COMPARISON, and it is the entire bet this module carries,
  -- reduced to one number.  Both sides of the arithmetic obligation
  -- below are tower-VALUED, so the comparison between them is a
  -- comparison of HEIGHTS, and `h` is the height the nesting currency
  -- has reached at this instant.  The second conjunct is where the bet
  -- lives: the caps recurrence must have climbed strictly past it, with
  -- one story to spare, since converting a tower into `blowH` costs
  -- exactly that story.
  --
  -- IT IS STATED INSIDE THE SEAL BECAUSE ONLY IN HERE CAN IT BE PROVEN.
  -- Discharging it means unfolding `nwAt` on both axes, and the block
  -- exports equations for the cap but none for the width; stating it
  -- outside would oblige a future proof to export two more, widening
  -- the seal for no reason other than where a postulate was typed.
  --
  -- AND THE Σ HAS CONTENT: the first conjunct is upward-closed in `h`
  -- and the second downward-closed, so no witness satisfies both by
  -- being large enough.
  --
  -- RECOVERY: `git show 725296e:agda/src/Verify-Budget-Sufficient/Nest-Tower.agda`
  --   holds height arithmetic written for exactly this shape and
  --   currency-independent: `sum2H`/`sum3H`/`sucH`/`hUp`/`hIn`/`1≤3x`/
  --   `payL`/`payR` for moving a bound up a tower, and `tower-sum-tab`
  --   for a slot telescope.
  postulate
    nest-height : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
      (id : ℕ) →
      Σ ℕ λ h →
        (3 * nestCapAt e sl id + realWidAt e sl id * nestSyn e sl
           ≤ towerℕ h)
        × (suc h ≤ towerℕ (capsHpred e sl id))

------------------------------------------------------------------
-- THE ONE ARITHMETIC OBLIGATION THE WHOLE CURRENCY RESTS ON, and it
-- mentions no evaluator: three quantities each under `nestCapAt`, plus
-- the instant's own fresh growth — its real-width budget times the
-- wrap factor — sum to under `capsH`.  Three because a depth statement
-- reads a subject, a path and a store; the fourth addend because the
-- store is read at the instant's ENTRY while the walk subscribes
-- accumulators the instant's own folds have deepened since.
--
-- WHY THE HEADROOM IS THERE.  `nestCapAt` and `realWidAt` iterate one
-- exponential per instant from program-shaped bases, while `capsH`
-- iterates `blowH`, whose pooled summand `2 * poolCount (towerℕ m) m`
-- sits above `towerℕ k` for every reachable k — a tower per instant
-- against an exponential per instant, so the sum is dominated with
-- stories to spare rather than by a constant-factor squeeze.
--
-- AND THE WHOLE OF IT IS NOW A HEIGHT QUESTION.  `capsH` is `blowH` of
-- the previous height at every index, and `tower-le-blowH` turns a
-- tower one story below that height into `blowH` of it, so the sum's
-- own tower height is the only thing left to establish -- which is
-- `nest-height`, inside the seal, where the two axes unfold.
nestCap-3≤capsH : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id : ℕ) →
  3 * nestCapAt e sl id + realWidAt e sl id * nestSyn e sl
    ≤ capsH e sl id
nestCap-3≤capsH e sl id =
  ≤-trans lo (subst (towerℕ h ≤_) (sym (capsH-blow e sl id))
                (tower-le-blowH h (capsHpred e sl id)
                                (1≤capsHpred e sl id) hi))
  where
  h  = proj₁ (nest-height e sl id)
  lo = proj₁ (proj₂ (nest-height e sl id))
  hi = proj₂ (proj₂ (nest-height e sl id))

-- three parts each under the cap, the fresh term on top, paid out of
-- the height
nest-sum-3 : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id : ℕ) (x y z : ℕ) →
  x ≤ nestCapAt e sl id → y ≤ nestCapAt e sl id → z ≤ nestCapAt e sl id →
  x + y + z + realWidAt e sl id * nestSyn e sl ≤ capsH e sl id
nest-sum-3 e sl id x y z hx hy hz =
  ≤-trans (+-mono-≤ (+-mono-≤ (+-mono-≤ hx hy) hz)
                    (≤-reflexive {x = realWidAt e sl id * nestSyn e sl} refl))
          (≤-trans (≤-reflexive (cong (_+ realWidAt e sl id * nestSyn e sl)
                                      (3*-expand (nestCapAt e sl id))))
                   (nestCap-3≤capsH e sl id))
  where
  3*-expand : ∀ (m : ℕ) → m + m + m ≡ 3 * m
  3*-expand m =
    trans (+-assoc m m m) (cong (λ x → m + (m + x)) (sym (+-identityʳ m)))
