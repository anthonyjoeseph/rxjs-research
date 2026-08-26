------------------------------------------------------------------
-- WHERE A RUN'S NESTING IS ACTUALLY HELD, and it is not in the subject.
-- Four places, each of which can hand the sweep an observable the
-- program's syntax never mentioned: a shared slot's definition, a
-- mergeAll's queue, a scan's accumulator, and a live source's pending
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
open import Data.List using (List; foldr; tabulate; []; _∷_)
open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _^_; _⊔_; _≤_; _≤ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (≤ᵇ⇒≤; ≤-trans; ≤-reflexive; ⊔-lub; +-mono-≤; +-assoc; +-monoʳ-≤; +-monoˡ-≤; +-identityʳ; *-mono-≤;
  n≤1+n; *-monoˡ-≤; *-monoʳ-≤; *-assoc; *-comm; *-identityˡ; *-identityʳ; *-distribˡ-+; m^n>0; ^-distribˡ-+-*)
open import Data.Nat.ListAction using (sum)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Rx.Exp using (Ctx; Closed; sizeᵗ)
open import Rx.Slots using (Slot; Slots; scripted; shared)
open import Rx.Evaluator using (map-f; scan-f; take-f; from-inner; thru-outer; Frame; Path; root; share-sink; _↠_; RegId; NodeState;
  scan-st; take-st; mergeAll-st; switch-st; exhaust-st; LiveSource; Sched; EvalSt;
  Arrival; cascadeLatch; Chain; capsBase; cascadeFinish; blowH)
open import Rx.Prim using (Source; towerℕ)
open import Rx.Nest-Depth using (nestDᵉ; nestDᵗ; nestDᵛ)
open import Decide using (≤ᵇ-true)
open import Verify-Budget-Sufficient.Caps using (capsH; 3≤capsH; tower-le-blowH; capsAt; Caps; 1≤pow≤; 1≤capsAt-reg)
open import Verify-Budget-Sufficient.Nest-Cap using (nestU; nestU-base)

pathNestD : ∀ {n} {Γ : Ctx n} {s t} → Path Γ s t → ℕ
pathNestD root                    = 0
pathNestD (share-sink i)          = 0
pathNestD (map-f f ↠ p)           = nestDᵗ f + pathNestD p
pathNestD (scan-f f _ ↠ p)        = nestDᵗ f + pathNestD p
pathNestD (take-f _ ↠ p)          = pathNestD p
pathNestD (from-inner _ _ _ ↠ p)  = pathNestD p
pathNestD (thru-outer _ _ ↠ p)    = suc (pathNestD p)

-- THE SYNTAX A PATH CHARGES, which is the factor's exponent and the
-- currency the invariant already speaks.  `pathSz?` bounds every step
-- function on a registered path by the size cap AND the path's own
-- length by the same cap, so this sum is within the cap SQUARED -- and
-- that is a reading of a conjunct that is already carried, not a new
-- bet about the dynamics.
frameSzD : ∀ {n} {Γ : Ctx n} {s u} → Frame Γ s u → ℕ
frameSzD (map-f f)          = sizeᵗ f
frameSzD (scan-f f _)       = sizeᵗ f
frameSzD (take-f _)         = 0
frameSzD (from-inner _ _ _) = 0
frameSzD (thru-outer _ _)   = 0

pathSzSum : ∀ {n} {Γ : Ctx n} {s t} → Path Γ s t → ℕ
pathSzSum root           = 0
pathSzSum (share-sink _) = 0
pathSzSum (f ↠ p)        = frameSzD f + pathSzSum p

-- THE PER-FRAME FACTOR, AND IT IS A FACTOR BECAUSE NO SUMMAND
-- SURVIVES.  A step function may name its payload more than once, and
-- `nestDᵉ` is additive at `mapᵉ`, so the value a frame hands on is read
-- at as many copies of the payload's own nesting as the function has
-- occurrences of it.  A charge that adds the function's syntax cannot
-- see the count; a charge that MULTIPLIES by two to the size dominates
-- it, since occurrences are bounded by size and binder nesting raises
-- the power rather than the base.
--
-- THE MEASURE OVER-COUNTS AND THE DYNAMICS DO NOT, which is why the
-- repair is priced here rather than in `Rx.Nest-Depth`.  The value a
-- duplicating map really emits is exactly as deep as its payload; it is
-- the syntactic measure of the closed result that doubles.  Two
-- predecessors of that measure died of being re-designed, so the
-- doubling is paid for in the cap instead.
--
-- REFUTED: `Refuted.Apply-Fn-Nest` at the substitution itself, and
--   `Refuted.Step-Frame-Nest-Dup` at the frame that consumes it.
frameNestF : ∀ {n} {Γ : Ctx n} {s u} → Frame Γ s u → ℕ
frameNestF (map-f f)          = 2 ^ sizeᵗ f
frameNestF (scan-f f _)       = 2 ^ sizeᵗ f
frameNestF (take-f _)         = 1
frameNestF (from-inner _ _ _) = 1
frameNestF (thru-outer _ _)   = 1

1≤frameNestF : ∀ {n} {Γ : Ctx n} {s u} (f : Frame Γ s u) → 1 ≤ frameNestF f
1≤frameNestF (map-f f)          = m^n>0 2 (sizeᵗ f)
1≤frameNestF (scan-f f _)       = m^n>0 2 (sizeᵗ f)
1≤frameNestF (take-f _)         = s≤s z≤n
1≤frameNestF (from-inner _ _ _) = s≤s z≤n
1≤frameNestF (thru-outer _ _)   = s≤s z≤n

-- the walk telescopes by MULTIPLYING these, one per frame
pathNestF : ∀ {n} {Γ : Ctx n} {s t} → Path Γ s t → ℕ
pathNestF root           = 1
pathNestF (share-sink _) = 1
pathNestF (f ↠ p)        = frameNestF f * pathNestF p

1≤pathNestF : ∀ {n} {Γ : Ctx n} {s t} (p : Path Γ s t) → 1 ≤ pathNestF p
1≤pathNestF root           = s≤s z≤n
1≤pathNestF (share-sink _) = s≤s z≤n
1≤pathNestF (f ↠ p)        = *-mono-≤ (1≤frameNestF f) (1≤pathNestF p)

-- THE ARITHMETIC BOTH TELESCOPES RUN ON, and the only place a factor
-- and a summand meet: one step's factor multiplies everything the rest
-- of the walk will charge, which is sound exactly because a factor is
-- never below one.
nest-telescope : ∀ (F G B X Y : ℕ) → 1 ≤ F →
  G * (F * (B + X) + Y) ≤ F * G * (B + (X + Y))
nest-telescope F G B X Y 1≤F =
  ≤-trans (*-monoʳ-≤ G (+-monoʳ-≤ (F * (B + X)) grow)) (≤-reflexive eq)
  where
  grow : Y ≤ F * Y
  grow = ≤-trans (≤-reflexive (sym (*-identityˡ Y))) (*-monoˡ-≤ Y 1≤F)
  eq : G * (F * (B + X) + F * Y) ≡ F * G * (B + (X + Y))
  eq = trans (cong (G *_) (sym (*-distribˡ-+ F (B + X) Y)))
       (trans (sym (*-assoc G F ((B + X) + Y)))
       (trans (cong (_* ((B + X) + Y)) (*-comm G F))
              (cong (F * G *_) (+-assoc B X Y))))

-- A FACTOR RAISED TO THE BURST IS STILL A FACTOR, and it is still at
-- least the factor -- the two properties the telescope needs of the
-- burst exponent, and the only two.
pow-grow¹ : ∀ (F W : ℕ) → 1 ≤ F → 1 ≤ W → F ≤ F ^ W
pow-grow¹ F (suc W) h _ =
  ≤-trans (≤-reflexive (sym (*-identityʳ F)))
          (*-monoʳ-≤ F (1≤pow≤ F W h))

-- AND THE BASE-SIDE POWER LAW, WHICH THE STDLIB DOES NOT CARRY: it has
-- the exponent-side distribution and not this one, and the walk needs
-- this one, because the burst factor is raised over a PRODUCT of frame
-- factors and has to come apart along the path.
mul-shuffle : ∀ (a b c d : ℕ) → a * b * (c * d) ≡ a * c * (b * d)
mul-shuffle a b c d =
  trans (*-assoc a b (c * d))
  (trans (cong (a *_) (trans (sym (*-assoc b c d))
                      (trans (cong (_* d) (*-comm b c))
                             (*-assoc c b d))))
         (sym (*-assoc a c (b * d))))

pow-distrib-* : ∀ (k m n : ℕ) → (m * n) ^ k ≡ m ^ k * n ^ k
pow-distrib-* zero    m n = refl
pow-distrib-* (suc k) m n =
  trans (cong (m * n *_) (pow-distrib-* k m n))
        (mul-shuffle m n (m ^ k) (n ^ k))

frameNestF≡ : ∀ {n} {Γ : Ctx n} {s u} (f : Frame Γ s u) →
  frameNestF f ≡ 2 ^ frameSzD f
frameNestF≡ (map-f _)          = refl
frameNestF≡ (scan-f _ _)       = refl
frameNestF≡ (take-f _)         = refl
frameNestF≡ (from-inner _ _ _) = refl
frameNestF≡ (thru-outer _ _)   = refl

pathNestF≡ : ∀ {n} {Γ : Ctx n} {s t} (p : Path Γ s t) →
  pathNestF p ≡ 2 ^ pathSzSum p
pathNestF≡ root           = refl
pathNestF≡ (share-sink _) = refl
pathNestF≡ (f ↠ p)        =
  trans (cong₂ _*_ (frameNestF≡ f) (pathNestF≡ p))
        (sym (^-distribˡ-+-* 2 (frameSzD f) (pathSzSum p)))

nest-inflate : ∀ (F X : ℕ) → 1 ≤ F → X ≤ F * X
nest-inflate F X 1≤F =
  ≤-trans (≤-reflexive (sym (*-identityˡ X))) (*-monoˡ-≤ X 1≤F)

nest-scale : ∀ (F G Z : ℕ) → 1 ≤ F → G * Z ≤ F * G * Z
nest-scale F G Z 1≤F =
  ≤-trans (≤-trans (≤-reflexive (sym (*-identityˡ (G * Z))))
                   (*-monoˡ-≤ (G * Z) 1≤F))
          (≤-reflexive (sym (*-assoc F G Z)))

-- A CASCADE'S CHAINS ARE A MAX, not a sum: `depthCascade` folds them
-- with `⊔`, each from the same arrival.
chainsNestD : ∀ {n} {Γ : Ctx n} {s t} →
  List (RegId × Path Γ s t) → ℕ
chainsNestD = foldr (λ rc acc → pathNestD (proj₂ rc) ⊔ acc) 0

-- THE FACTORS ARE A PRODUCT, not a max, because the fold runs the
-- chains in sequence and each one's factor multiplies whatever the ones
-- after it will charge.
chainsNestF : ∀ {n} {Γ : Ctx n} {s t} →
  List (RegId × Path Γ s t) → ℕ
chainsNestF = foldr (λ rc acc → pathNestF (proj₂ rc) * acc) 1

chainsSzSum : ∀ {n} {Γ : Ctx n} {s t} →
  List (RegId × Path Γ s t) → ℕ
chainsSzSum = foldr (λ rc acc → pathSzSum (proj₂ rc) + acc) 0

-- the selection's factor is a product of the paths' own, so it is at
-- least one for the same reason each of them is -- and the walk needs
-- exactly this to read one chain's charge against the whole list's
1≤chainsNestF : ∀ {n} {Γ : Ctx n} {s t} (cs : List (RegId × Path Γ s t)) →
  1 ≤ chainsNestF cs
1≤chainsNestF []             = s≤s z≤n
1≤chainsNestF ((_ , p) ∷ cs) = *-mono-≤ (1≤pathNestF p) (1≤chainsNestF cs)

chainsNestF≡ : ∀ {n} {Γ : Ctx n} {s t} (cs : List (RegId × Path Γ s t)) →
  chainsNestF cs ≡ 2 ^ chainsSzSum cs
chainsNestF≡ []             = refl
chainsNestF≡ ((_ , p) ∷ cs) =
  trans (cong₂ _*_ (pathNestF≡ p) (chainsNestF≡ cs))
        (sym (^-distribˡ-+-* 2 (pathSzSum p) (chainsSzSum cs)))

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
nodeNest (mergeAll-st _ _ q _) = foldr (λ o acc → nestDᵉ o ⊔ acc) 0 q
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

-- THE STORE IS FOUR PLACES UNDER ONE `⊔`, so a bound on it IS four
-- bounds and taking it apart costs nothing.  Named here rather than
-- re-derived at each face because the four components are this
-- module's own: a caller that splits the maximum otherwise has to
-- write the folds out, and a fold written out at a call site is the
-- one thing that drifts when a fifth place is added.
storeNestMax-lub : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sched : Sched Γ) (st : EvalSt e) (F : ℕ) →
  slotsNestSum (Sched.slots sched) ≤ F →
  foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched) ≤ F →
  foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st) ≤ F →
  regsNestMax (EvalSt.registry st) ≤ F →
  storeNestMax sched st ≤ F
storeNestMax-lub sched st F hs hl hn hr =
  ⊔-lub (⊔-lub (⊔-lub hs hl) hn) hr

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
nestUnit : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) → ℕ
nestUnit e sl = suc (nestDᵉ e + slotsNestSum sl)

-- AND A CHAIN IS CHARGED TWO OF THEM, WHICH IS NOT SLACK.  A delivery
-- pays the unit once for the wraps its own walk installs, and a second
-- time for the ones the SHARE SINK installs on its behalf: the sink
-- fans the arriving values into every registration on the share, each
-- walking a path that lives in the registry rather than in the chain
-- being charged, and the path measure charges a sink zero.  A one-unit
-- charge is refuted at exactly that arm — `Refuted.Share-Sink-Nodes`,
-- three against one — and the second unit covers it because a
-- registered path's wraps are the program's wraps like any other.
--
-- THE BUDGET IS WHERE THE FACTOR HAS TO LAND, not the unit, and that
-- is why this is stated as a product here rather than by enlarging the
-- unit: the per-chain charge and the per-instant budget are compared
-- against each other, so doubling both would cancel.  Everything above
-- reads this symbolically, so the factor propagates on its own.
nestSyn : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) → ℕ
nestSyn e sl = 2 * nestUnit e sl

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

-- THE WIDTH IS THE REGISTRY CAP, AND IT IS THE ONLY QUANTITY THAT CAN
-- BE ONE.  What the width pays for is a walk deepening the store once
-- per chain it was handed, and a chain list is a SELECTION FROM THE
-- REGISTRY -- so whatever bounds the width has to bound the registry,
-- and the only thing that does is `capsOK?`'s own fifth conjunct.  Read
-- that way the comparison is definitional and the two leaves under it
-- are two lines each.
--
-- AND THE PREDECESSOR WAS A WIDTH OF THIS MODULE'S OWN INVENTION, which
-- is what made it dangerous.  It read `capsBase` at the entry and
-- squared itself each instant, a shape chosen to dominate rather than
-- to be established, so nothing anywhere related it to the quantity a
-- walk actually spends.  The leaves that had to bridge the gap were
-- stated, ranked FALSITY, and are gone with it.
--
-- THE COST IS INSTANTIABILITY, AND IT IS PAID KNOWINGLY.  `capsBase` is
-- a syntactic reading that renders, so the entry index of this currency
-- used to be reachable by a `refl`; `capsAt` sits on the caps
-- recurrence and no instantiation of it terminates, so the currency is
-- now symbolic-only at every index.  What that reach bought was the
-- refutation above -- a made-up width is cheap to evaluate and cheap to
-- be wrong about, and this trades the second for the first.
abstract
  nestCapAt : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) → ℕ

  realWidAt : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) → ℕ
  realWidAt e sl id = Caps.cReg (capsAt e sl id)

  -- THE PER-INSTANT FANOUT FACTOR.  A chain walk does not ADD its
  -- frames' charges to the store depth, it MULTIPLIES by them: a step
  -- function may name its payload twice, so one frame can double the
  -- nesting of what it emits, and a path composes those doublings.
  -- The factor is `2` per unit of step-function syntax along a path,
  -- and a cascade compounds one path's worth per chain -- so real
  -- width in the exponent, size in the base.
  -- THE BURST, WHICH IS A WIDTH READ AS A COUNT.  A frame's charge has
  -- to see how many values it was handed, because a THREADING frame --
  -- a scan -- applies its step function once per value and what the
  -- function piles onto its accumulator accrues once per application.
  -- The count of values one instant can carry is the width cap, so the
  -- burst is that cap and not a quantity of this module's own.
  --
  -- AND IT IS THE WIDTH AT THE INSTANT'S EXIT, NOT AT ITS ENTRY, which
  -- is the whole difference between a bound that survives a walk and
  -- one that does not.  A `thru` frame hands on what its inners emit,
  -- so it turns one value into as many as a burst can hold and the
  -- entry width is crossed by a PRODUCT at the first such hop -- which
  -- is why the caps face pays a square there.  `capsAt` at the next
  -- index IS the full `frameStep` endpoint for this instant, so every
  -- intermediate hop's width sits under it by monotonicity in the hop
  -- count, and one number covers the whole walk.
  --
  -- REFUTED: `Refuted.Scan-Fold-Burst` kills the burst-free reading of
  --   the walk's per-frame charge, 65 against 64, at the smallest step
  --   function that deepens its own accumulator; the gap is unbounded
  --   in the burst, so no constant repairs it and the factor below is
  --   what the numbers point at.
  nestBurstAt : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
    (id : ℕ) → ℕ
  nestBurstAt e sl id = suc (Caps.cWid (capsAt e sl id))

  1≤nestBurstAt : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
    (id : ℕ) → 1 ≤ nestBurstAt e sl id
  1≤nestBurstAt e sl id = s≤s z≤n

  -- ONE CASCADE'S WHOLE FANOUT, AND THE EXPONENT HAS TWO TENANTS.  The
  -- burst copies are the walk's own: a chain spends its wrap factor
  -- once per value it carries, and the selection's total wrap is two to
  -- its summed frame sizes, which the registry's size cap holds under
  -- the width times a square.  The other tenant pays the SUBSCRIBE
  -- factor, which is a different charge at the same frames: an `*All`
  -- frame re-enters the subscribe machinery, and what it emits is
  -- deeper than what it was handed by the number of times the
  -- substituted function names its payload.
  --
  -- AND THAT SECOND CHARGE IS PER VALUE OF THE BURST RATHER THAN PER
  -- FRAME, WHICH IS WHY THE COPIES ARE A SQUARE.  A descent hands back a
  -- whole burst, and a stored step function is refolded once per value
  -- in it, so the frame's factor is spent `suc burst` times and not
  -- once.  The frame COUNT is under the width times the size either
  -- way, so this tenant costs `suc burst` copies of the same
  -- width-times-square the first tenant costs one of -- and the square
  -- covers both sums without the two interleaving.
  -- REFUTED: `Refuted.Scan-Burst-Nest` is what rules the per-frame
  --   reading out, at a burst of fourteen against a charge that does
  --   not move with it at all.
  nestFacAt : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
    (id : ℕ) → ℕ
  nestFacAt e sl id =
    2 ^ (suc (nestBurstAt e sl id) * suc (nestBurstAt e sl id)
         * (suc (Caps.cSize (capsAt e sl id))
            * (realWidAt e sl id
               * (Caps.cSize (capsAt e sl id) * Caps.cSize (capsAt e sl id)))))

  -- ONE INSTANT'S FRESH GROWTH, NAMED, because it is what the
  -- recurrence adds and what every preservation step has to match
  -- against -- and because it now has three factors rather than two.
  nestIncAt : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
    (id : ℕ) → ℕ
  nestIncAt e sl id =
    realWidAt e sl id
      * (nestBurstAt e sl id
         * (suc (suc (realWidAt e sl id * Caps.cSize (capsAt e sl id)))
            * nestU (Caps.cSize (capsAt e sl id)) (nestUnit e sl)))

  -- THE SIZE CAP SITS UNDER ONE INSTANT'S GROWTH, which is what lets a
  -- walk charge an arrival's own size to the increment rather than to
  -- the store it arrived at.  Proven in here because every factor it
  -- reads is sealed: the width is at least one, so the doubled term
  -- already exceeds the size, and the remaining factors are each at
  -- least one.
  size≤nestIncAt : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
    (id : ℕ) → Caps.cSize (capsAt e sl id) ≤ nestIncAt e sl id
  size≤nestIncAt e sl id =
    ≤-trans S≤mid (≤-trans (≤-trans mid≤u u≤b) b≤r)
    where
    S : ℕ
    S = Caps.cSize (capsAt e sl id)

    R : ℕ
    R = realWidAt e sl id

    U : ℕ
    U = nestU S (nestUnit e sl)

    1≤U : 1 ≤ U
    1≤U = ≤-trans (s≤s z≤n) (nestU-base S (nestUnit e sl))

    S≤mid : S ≤ suc (suc (R * S))
    S≤mid =
      ≤-trans (≤-trans (≤-reflexive (sym (*-identityˡ S)))
                       (*-monoˡ-≤ S (1≤capsAt-reg e sl id)))
              (≤-trans (n≤1+n (R * S)) (n≤1+n (suc (R * S))))

    mid≤u : suc (suc (R * S)) ≤ suc (suc (R * S)) * U
    mid≤u = ≤-trans (≤-reflexive (sym (*-identityʳ (suc (suc (R * S))))))
                    (*-monoʳ-≤ (suc (suc (R * S))) 1≤U)

    u≤b : suc (suc (R * S)) * U ≤ nestBurstAt e sl id * (suc (suc (R * S)) * U)
    u≤b = ≤-trans (≤-reflexive (sym (*-identityˡ (suc (suc (R * S)) * U))))
                  (*-monoˡ-≤ (suc (suc (R * S)) * U) (1≤nestBurstAt e sl id))

    b≤r : nestBurstAt e sl id * (suc (suc (R * S)) * U)
            ≤ R * (nestBurstAt e sl id * (suc (suc (R * S)) * U))
    b≤r = ≤-trans (≤-reflexive (sym (*-identityˡ _)))
                  (*-monoˡ-≤ _ (1≤capsAt-reg e sl id))

  -- AND A BASE SITS UNDER ITS OWN BURST POWER, the burst being a
  -- successor by construction.  A consumer holding a bound on the
  -- POWER needs this to spend it on the base, and cannot see that the
  -- exponent is nonzero from outside.
  m≤m^burst : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
    (id : ℕ) (x : ℕ) → 1 ≤ x → x ≤ x ^ nestBurstAt e sl id
  m≤m^burst e sl id x hx =
    ≤-trans (≤-reflexive (sym (*-identityʳ x)))
            (*-monoʳ-≤ x (1≤pow≤ x (Caps.cWid (capsAt e sl id)) hx))

  -- READ BACK OUT OF THE SEAL for the same reason the width is: a
  -- consumer proving the fanout bound has to say what it proved.
  nestFacAt-def : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
    (id : ℕ) →
    nestFacAt e sl id
      ≡ 2 ^ (suc (nestBurstAt e sl id) * suc (nestBurstAt e sl id)
             * (suc (Caps.cSize (capsAt e sl id))
                * (realWidAt e sl id
                   * (Caps.cSize (capsAt e sl id) * Caps.cSize (capsAt e sl id)))))
  nestFacAt-def e sl id = refl

  nestIncAt-def : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
    (id : ℕ) →
    nestIncAt e sl id
      ≡ realWidAt e sl id
        * (nestBurstAt e sl id
           * (suc (suc (realWidAt e sl id * Caps.cSize (capsAt e sl id)))
              * nestU (Caps.cSize (capsAt e sl id)) (nestUnit e sl)))
  nestIncAt-def e sl id = refl

  nestCapAt e sl zero    = nestUnit e sl
  nestCapAt e sl (suc id) =
    nestFacAt e sl id * (nestCapAt e sl id + nestIncAt e sl id)

  1≤nestFacAt : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
    (id : ℕ) → 1 ≤ nestFacAt e sl id
  1≤nestFacAt e sl id =
    m^n>0 2 (suc (nestBurstAt e sl id) * suc (nestBurstAt e sl id)
             * (suc (Caps.cSize (capsAt e sl id))
                * (realWidAt e sl id
                   * (Caps.cSize (capsAt e sl id) * Caps.cSize (capsAt e sl id)))))

  nestOK? : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
    Sched Γ → EvalSt e → Bool
  nestOK? e sl id sched st = storeNestMax sched st ≤ᵇ nestCapAt e sl id

  -- the base cap, spent by the root subscribe, whose subject IS the
  -- program and whose path is `root`
  nestCapAt-0 : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) →
    nestCapAt e sl 0 ≡ suc (nestDᵉ e + slotsNestSum sl)
  nestCapAt-0 e sl = refl

  -- THE WIDTH READ BACK OUT OF THE SEAL, which is what lets a consumer
  -- spend the registry conjunct of `capsOK?` against it.  The seal is
  -- for cost and the equation costs nothing: `capsAt` is already in
  -- every type this module's consumers mention.
  realWidAt-def : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
    (id : ℕ) →
    realWidAt e sl id ≡ Caps.cReg (capsAt e sl id)
  realWidAt-def e sl id = refl

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
      ≡ nestFacAt e sl id
        * (nestCapAt e sl id + nestIncAt e sl id)
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
        (2 * nestCapAt e sl id + nestCapAt e sl (suc id) ≤ towerℕ h)
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
  2 * nestCapAt e sl id + nestCapAt e sl (suc id) ≤ capsH e sl id
nestCap-3≤capsH e sl id =
  ≤-trans lo (subst (towerℕ h ≤_) (sym (capsH-blow e sl id))
                (tower-le-blowH h (capsHpred e sl id)
                                (1≤capsHpred e sl id) hi))
  where
  h  = proj₁ (nest-height e sl id)
  lo = proj₁ (proj₂ (nest-height e sl id))
  hi = proj₂ (proj₂ (nest-height e sl id))

-- the instant's own cap sits under the next one, the factor being at
-- least one
nestCap-mono : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id : ℕ) →
  nestCapAt e sl id + nestIncAt e sl id
    ≤ nestCapAt e sl (suc id)
nestCap-mono e sl id =
  ≤-trans (nest-inflate (nestFacAt e sl id) _ (1≤nestFacAt e sl id))
          (≤-reflexive (sym (nestCapAt-suc e sl id)))

-- THE INSTANT-ONE FLOOR, STATED IN A SIGHTED CURRENCY.  The base cap
-- IS the program's own unit, and the unit is built on `nestDᵉ` -- the
-- measure that reads zero through a `deferᵉ`, so a program headed by a
-- defer carries a unit of one however deep the body its subscribe
-- frame installs.  What pays for that blindness is the increment,
-- which dominates `capsAt`'s own size, and the size reads `sizeᵉ`,
-- which DOES descend into a deferred body.  So a consumer needing the
-- instant-one cap can charge the unit plus that size and never read
-- the factor at all, which is the one quantity the seal exports no
-- equation for.
-- AND THE SUMMAND IS NOT SLACK, which `Probed.Burst-Nest-Unit`
-- measures: a defer-headed program at a body four deep leaves a store
-- of 4 against a unit of 2, so the unit alone does not carry it.
-- THE SUMMAND IS THE INCREMENT ITSELF, not the size it dominates.
-- Charging the size is available -- `size≤nestIncAt` gives it -- and
-- it is the wrong choice, because the summand here is an obligation
-- placed on whoever supplies the store bound: a SMALLER summand is a
-- HARDER leaf, and the increment is what the cap actually offers at
-- this step.  Nothing downstream wants the tighter one, and the size
-- is the sealed quantity of the two.
nestCapAt-1-floor : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) →
  nestUnit e sl + nestIncAt e sl 0 ≤ nestCapAt e sl 1
nestCapAt-1-floor e sl =
  ≤-trans (+-monoˡ-≤ (nestIncAt e sl 0)
                     (≤-reflexive (sym (nestCapAt-0 e sl))))
          (nestCap-mono e sl 0)

-- AND THE CONSUMER'S FORM, so the spine module that spends this applies
-- ONE lemma rather than re-composing the floor with the introduction at
-- a call site whose subscribe term it would have to spell out twice.
nestOK?-from-floor : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (sched : Sched Γ) (st : EvalSt e) →
  storeNestMax sched st ≤ nestUnit e sl + nestIncAt e sl 0 →
  nestOK? e sl 1 sched st ≡ true
nestOK?-from-floor e sl sched st h =
  nestOK?-intro e sl 1 sched st (≤-trans h (nestCapAt-1-floor e sl))

2*-fold : ∀ (m x y : ℕ) → x ≤ m → y ≤ m → x + y ≤ 2 * m
2*-fold m x y hx hy =
  ≤-trans (+-mono-≤ hx hy)
          (≤-reflexive (cong (m +_) (sym (+-identityʳ m))))

-- three parts each under the cap, the fresh term on top, paid out of
-- the height
nest-sum-3 : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id : ℕ) (x y z : ℕ) →
  x ≤ nestCapAt e sl id → y ≤ nestCapAt e sl id → z ≤ nestCapAt e sl id →
  x + y + z + nestIncAt e sl id ≤ capsH e sl id
nest-sum-3 e sl id x y z hx hy hz =
  ≤-trans (≤-reflexive (+-assoc (x + y) z (nestIncAt e sl id)))
    (≤-trans (+-mono-≤ (2*-fold (nestCapAt e sl id) x y hx hy)
                       (≤-trans (+-monoˡ-≤ (nestIncAt e sl id) hz)
                                (nestCap-mono e sl id)))
             (nestCap-3≤capsH e sl id))

-- THE SAME SUM, WITH THE WALK'S FANOUT FACTOR ON THE STORE TERM.  A
-- chain walk multiplies rather than adds -- a step function may name
-- its payload twice -- so the store arm of a cascade's descent arrives
-- already scaled by `nestFacAt`, and that scaled arm is exactly the
-- next instant's cap.
nest-sum-fac : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id : ℕ) (x y z : ℕ) →
  x ≤ nestCapAt e sl id → y ≤ nestCapAt e sl id → z ≤ nestCapAt e sl id →
  x + y + nestFacAt e sl id * (z + nestIncAt e sl id)
    ≤ capsH e sl id
nest-sum-fac e sl id x y z hx hy hz =
  ≤-trans (+-mono-≤ (2*-fold (nestCapAt e sl id) x y hx hy)
                    (≤-trans (*-monoʳ-≤ (nestFacAt e sl id)
                                        (+-monoˡ-≤ (nestIncAt e sl id) hz))
                             (≤-reflexive (sym (nestCapAt-suc e sl id)))))
          (nestCap-3≤capsH e sl id)
