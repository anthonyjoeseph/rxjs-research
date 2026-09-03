-- Verify-Budget-Sufficient.Caps-Face.Part7.Arrival-Ledger
-- chainsGo-sz … arr-chains-nest-fac
module Verify-Budget-Sufficient.Caps-Face.Part7.Arrival-Ledger where

open import Data.Bool    using (true; false)
open import Data.Nat     using (ℕ; suc; _+_; _*_; _^_; _≤_; z≤n)
open import Data.Nat.Properties using (*-assoc; ^-distribˡ-+-*; ^-monoʳ-≤; *-monoˡ-≤; ≤-trans; ≤-reflexive; m≤m+n; n≤1+n; *-mono-≤;
  *-monoʳ-≤; +-monoʳ-≤; +-mono-≤; *-distribˡ-+; *-distribʳ-+; m≤m*n; ^-*-assoc; *-comm)
open import Data.Nat.Solver     using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.List    using (List; []; _∷_; length)
open import Data.Bool.ListAction using (all)
open import Data.Fin     using (Fin)
import Data.Fin as Fin
open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []ᵃ; _∷_ to _∷ᵃ_; map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties
  using (concat⁺; tabulate⁺)
  renaming (++⁺ to all-++; ++⁻ˡ to all-++ˡ; ++⁻ʳ to all-++ʳ)
open import Relation.Nullary using (yes; no)
open import Data.Vec     using (Vec; lookup) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)

open import Rx.Prim      using (Id; Source; _at_from_as_; after_,_)
open import Rx.Exp       using (_≟ᵗ_; Ctx; Closed)
open import Verify-Budget-Sufficient.Nest-Cap using (nestFac; nestFac-def)
open import Verify-Budget-Sufficient.Deliver-Measure using
  (pathSzSum-cap; chainsLenSum; chainsDelLen; chainsDelNestF; chainsDelSzSum; chainsDelNestF≡;
  chainsDelLen-chains; chainsDelSzSum-chains)
open import Verify-Budget-Sufficient.Fan-Caps using
  (fanLen; fanSq; delSize; delSq; delSize-cap; delSq-cap; delSize-def; delSq-def)
open import Verify-Budget-Sufficient.Nest-Store using
  (chainsSzSum; nestOK?; nestFacAt; nestFacAt-def; realWidAt; nestBurstAt)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; RegId; Chain; cascadeLatch; arrSource; chainsOf; chainsGo; Path;
  arrTy; sameSource)
open import Rx.Slots using (Slots)

open import Verify-Budget-Sufficient.Caps using
  (1≤capsAt-reg; Caps; capsAt; capsAt-⊑-suc)
open import Verify-Budget-Sufficient.Measures using
  (∧-true)

open import Verify-Budget-Sufficient.Caps-Face.Part1 using
  (capsOK?; pathSz?; regsSz?)
open import Verify-Budget-Sufficient.Caps-Face.Part4 using
  (capsOK?-regs; pathSz?-len)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Chain-Caps-OK using
  (chainsBurstOK)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Cascade-Nodes using
  (chains-count-width)

chainsGo-sz : ∀ {n} {Γ : Ctx n} {t} (B : ℕ) (a : Arrival Γ)
  (rs : List (RegId × Source × Chain Γ t)) →
  regsSz? B rs ≡ true →
  All (λ c → pathSz? B (proj₂ c) ≡ true) (chainsGo a rs)
chainsGo-sz B a [] h = []ᵃ
chainsGo-sz B a ((rid , src , (u , p)) ∷ rs) h
  with ∧-true (pathSz? B p) (all (λ en → pathSz? B (proj₂ (proj₂ (proj₂ en)))) rs) h
... | hp , hrs with sameSource (arrSource a) src | u ≟ᵗ arrTy a
... | false | _        = chainsGo-sz B a rs hrs
... | true  | no  _    = chainsGo-sz B a rs hrs
... | true  | yes refl = hp ∷ᵃ chainsGo-sz B a rs hrs

chainsSzSum-bound : ∀ {n} {Γ : Ctx n} {s t} (B : ℕ)
  (cs : List (RegId × Path Γ s t)) →
  All (λ c → pathSz? B (proj₂ c) ≡ true) cs →
  chainsSzSum cs ≤ length cs * (B * B)
chainsSzSum-bound B []       []ᵃ         = z≤n
chainsSzSum-bound B (c ∷ cs) (hc ∷ᵃ hcs) =
  +-mono-≤ (pathSzSum-cap B (proj₂ c) hc) (chainsSzSum-bound B cs hcs)

chainsLenSum-bound : ∀ {n} {Γ : Ctx n} {s t} (B : ℕ)
  (cs : List (RegId × Path Γ s t)) →
  All (λ c → pathSz? B (proj₂ c) ≡ true) cs →
  chainsLenSum cs ≤ length cs * B
chainsLenSum-bound B []       []ᵃ         = z≤n
chainsLenSum-bound B (c ∷ cs) (hc ∷ᵃ hcs) =
  +-mono-≤ (pathSz?-len B (proj₂ c) hc) (chainsLenSum-bound B cs hcs)

-- ONE FACTOR PER FRAME IS ONE FACTOR PER UNIT OF PATH LENGTH, so the
-- selection's total frame count is what the caps rider is raised to --
-- the length half of the size bound directly below, and bounded the
-- same way, by the width the registry admits times the length one
-- chain may reach.
arr-chains-len-sum : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (capsAt e sl id) sched st ≡ true →
  chainsDelLen n (capsAt e sl (suc id)) (chainsOf a st)
    ≤ realWidAt e sl id * delSize n (capsAt e sl (suc id))
arr-chains-len-sum {n = n} {e = e} sl id a sched st hsl hcaps =
  ≤-trans (chainsDelLen-chains n C⁺ (chainsOf a st))
    (≤-trans (+-mono-≤ (≤-trans (chainsLenSum-bound B (chainsOf a st)
                                   (chainsGo-sz B a (EvalSt.registry st) regsz))
                                (*-mono-≤ wid B≤))
                       (*-monoˡ-≤ (fanLen n C⁺) wid))
             (≤-reflexive (trans (sym (*-distribˡ-+ (realWidAt e sl id)
                                        (Caps.cSize C⁺) (fanLen n C⁺)))
                                 (cong (realWidAt e sl id *_) (sym (delSize-def n C⁺))))))
  where
  C = capsAt e sl id
  C⁺ = capsAt e sl (suc id)
  B = Caps.cSize C
  B≤ = proj₁ (capsAt-⊑-suc e sl id)
  wid = chains-count-width sl id a sched st hcaps
  regsz : regsSz? B (EvalSt.registry st) ≡ true
  regsz = capsOK?-regs C sched st hcaps

arr-chains-sz-sum : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (capsAt e sl id) sched st ≡ true →
  chainsDelSzSum n (capsAt e sl (suc id)) (chainsOf a st)
    ≤ realWidAt e sl id * delSq n (capsAt e sl (suc id))
arr-chains-sz-sum {n = n} {e = e} sl id a sched st hsl hcaps =
  ≤-trans (chainsDelSzSum-chains n C⁺ (chainsOf a st))
    (≤-trans (+-mono-≤ (≤-trans (chainsSzSum-bound B (chainsOf a st)
                                   (chainsGo-sz B a (EvalSt.registry st) regsz))
                                (*-mono-≤ wid (*-mono-≤ B≤ B≤)))
                       (*-monoˡ-≤ (fanSq n C⁺) wid))
    (≤-trans (≤-reflexive (sym (*-distribˡ-+ (realWidAt e sl id)
                                 (Caps.cSize C⁺ * Caps.cSize C⁺) (fanSq n C⁺))))
             (*-monoʳ-≤ (realWidAt e sl id)
                        (delSq-cap n C⁺ (1≤capsAt-reg e sl (suc id))))))
  where
  C = capsAt e sl id
  C⁺ = capsAt e sl (suc id)
  B = Caps.cSize C
  B≤ = proj₁ (capsAt-⊑-suc e sl id)
  wid = chains-count-width sl id a sched st hcaps
  regsz : regsSz? B (EvalSt.registry st) ≡ true
  regsz = capsOK?-regs C sched st hcaps

-- AND THE SAME SELECTION AGAINST THE FANOUT CEILING, which is the half
-- the additive reading got wrong.  A frame does not ADD its function's
-- charge to what it emits: a step function may name its payload twice,
-- so one `mapᵉ` can DOUBLE the nesting of the value coming out of it,
-- and a path composes those doublings while a cascade compounds one
-- path's worth per chain.  The factor is therefore a product, `2` per
-- unit of step-function syntax, and this says the product a registered
-- chain list can reach is within the instant's own fanout ceiling --
-- real width in the exponent, the size cap in the base.
--
-- REFUTED: `Refuted.Apply-Fn-Nest` kills the additive substitution
--   reading at one frame -- a payload named on both sides of a single
--   `mapᵉ` reads 2 against a charge of 0.  `Refuted.Step-Frame-Nest-Dup`
--   carries the same witness up to the frame the walk actually steps,
--   80 against 40, unbounded in the payload's own depth.
arr-chains-nest-fac : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (capsAt e sl id) sched st ≡ true →
  nestOK? e sl id sched st ≡ true →
  nestFac (Caps.cSize (capsAt e sl (suc id))) (nestBurstAt e sl id)
      ^ chainsDelLen n (capsAt e sl (suc id)) (chainsOf a st)
    * chainsDelNestF n (capsAt e sl (suc id)) (chainsOf a st) ^ nestBurstAt e sl id
      ≤ nestFacAt e sl id
arr-chains-nest-fac {n = n} {e = e} sl id a sched st hsl hcaps hnest =
  ≤-trans (≤-reflexive
             (cong₂ _*_ (trans (cong (_^ L)
                                 (trans (nestFac-def B K)
                                   (trans (cong (_^ B) (^-*-assoc 2 B (suc K)))
                                          (^-*-assoc 2 (B * suc K) B))))
                               (^-*-assoc 2 (B * suc K * B) L))
                        (trans (cong (_^ K) (chainsDelNestF≡ n C (chainsOf a st)))
                               (^-*-assoc 2 S K))))
    (≤-trans (≤-reflexive (sym (^-distribˡ-+-* 2 (B * suc K * B * L) (S * K))))
      (≤-trans (^-monoʳ-≤ 2 expo)
               (≤-reflexive (sym (nestFacAt-def e sl id)))))
  where
  C = capsAt e sl (suc id)
  B = Caps.cSize C
  K = nestBurstAt e sl id
  L = chainsDelLen n C (chainsOf a st)
  S = chainsDelSzSum n C (chainsOf a st)
  D = delSize n C
  X = realWidAt e sl id * delSq n C
  Xʹ = suc D * X

  X≤Xʹ : X ≤ Xʹ
  X≤Xʹ = m≤m+n X (D * X)

  -- the length half lands on the fresh `suc`, the size half on the
  -- burst term the factor already had
  lenX : B * L ≤ X
  lenX =
    ≤-trans (*-mono-≤ (delSize-cap n C)
                      (arr-chains-len-sum sl id a sched st hsl hcaps))
            (≤-reflexive
              (trans (sym (*-assoc D (realWidAt e sl id) D))
                     (trans (cong (_* D) (*-comm D (realWidAt e sl id)))
                            (trans (*-assoc (realWidAt e sl id) D D)
                                   (cong (realWidAt e sl id *_) (sym (delSq-def n C)))))))

  szX : S * K ≤ K * Xʹ
  szX = ≤-trans (≤-reflexive (*-comm S K))
                (*-monoʳ-≤ K (≤-trans (arr-chains-sz-sum sl id a sched st hsl hcaps)
                                      X≤Xʹ))

  -- the subscribe half is now spent once per BURST VALUE at each frame,
  -- so the length term arrives with a `suc K` on it and the two halves
  -- together need the square the factor carries
  -- the flattened factor carries one power of the size cap per level
  -- of the term the descent walks, so the length half arrives with a
  -- second `B` on it and the ceiling gains the matching `suc B`
  lenX′ : B * suc K * B * L ≤ suc K * Xʹ
  lenX′ =
    ≤-trans (≤-reflexive
              (trans (*-assoc (B * suc K) B L)
                     (trans (cong (_* (B * L)) (*-comm B (suc K)))
                            (*-assoc (suc K) B (B * L)))))
            (*-monoʳ-≤ (suc K)
              (≤-trans (*-monoʳ-≤ B lenX)
                       (*-monoˡ-≤ X (≤-trans (delSize-cap n C) (n≤1+n D)))))

  sq : suc K + K ≤ suc K * suc K
  sq = +-monoʳ-≤ (suc K) (m≤m*n K (suc K))

  expo : B * suc K * B * L + S * K ≤ suc K * suc K * Xʹ
  expo =
    ≤-trans (+-mono-≤ lenX′ szX)
            (≤-trans (≤-reflexive (sym (*-distribʳ-+ Xʹ (suc K) K)))
                     (*-monoˡ-≤ Xʹ sq))

-- THE BURST BOUND A CASCADE'S WALKS RUN UNDER, and it is a caps fact
-- rather than a walk fact, which is why it is a leaf here and not a
-- clause up there.  A chain starts from ONE value -- the arrival's --
-- and only a `thru` frame can hand on more than it took, by however
-- many its inners emit; what caps that is the width, and the width cap
-- is `capsOK?`'s business.  So the walk takes the bound as a
-- hypothesis shaped like its own recursion and this is where the
-- hypothesis is met.
--
-- AND WHAT IS STILL OPEN IS WHETHER ONE NUMBER CAN HOLD A WHOLE WALK,
-- WHICH IS A QUESTION ABOUT COMPOUNDING AND NOT ABOUT SIZE.  A `thru`
-- frame subscribes every value it takes, so two of them in a row hand
-- on the SQUARE of what came in and a walk's burst compounds once per
-- such frame; the number the ledger reads is fixed before the first
-- hop.  So the statement holds exactly when the compounding along a
-- path -- bounded by the frames a path may carry, which the size
-- receipt is what bounds -- stays under the number, and that is an
-- inequality between two faces of the same recurrence rather than a
-- fact about any one program.  The arrival is not what widens: a nat
-- arrival and a map built at exactly the cap's width already cross the
-- entry reading, so conditioning on the payload settles nothing
-- either way.
--
-- REFUTED: `Refuted.Chains-Burst-Flat` -- four values at the root of
--   one chain against a width-two cap granting three, at the
--   evaluator's own state, arrival and registry.  It kills the ENTRY
--   width, which is what `nestBurstAt` used to name; the number it
--   names now dominates that width at every index and grants 256 at
--   the refuting shape, so the witness no longer reaches this row.
-- DEAD ROUTE: instantiating this statement, in any denomination.
--   The width it reads is `nestBurstAt`, which is sealed, and the caps
--   both sides are read at are `capsAt`'s, which does not return at the
--   smallest program the language admits.  So the mirror below is not
--   one kind of evidence among several here -- it is the only kind
--   available, and no probe can be commissioned against this row.
-- TWIN: `thruWalk-walk` propagates this conjunct ACROSS THE FEARED HOP
--   and is proven -- taking it in at one level and handing it back at
--   another, with that level's growth bounded in the same tuple.
postulate
  arr-chains-bursts : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id)
    (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl →
    capsOK? (capsAt e sl id) sched st ≡ true →
    chainsBurstOK (nestBurstAt e sl id) a nextId (chainsOf a st) sched
      (cascadeLatch a st)

-- AND THE SAME SELECTION CARRIES THE CAPS, which is a preservation
-- statement and not a selection one: the predicate asserts the store
-- bound at every state the fold passes through, so what has to be shown
-- is that a walk which starts inside the caps stays inside them.  The
-- caps face already proves exactly that, frame by frame and with its own
-- level counter, so this is that receipt re-read at a flat cap rather
-- than a fresh induction.
--
-- AND "RE-READ AT A FLAT CAP" IS THE WHOLE OBLIGATION, NOT A FORMALITY.
-- The frame-wise receipt does not conclude at the cap it was handed:
-- `stepFrame-caps` returns a level `j'` and restates the invariant at
-- `frameStep (j + j')`, and composing a walk's levels is exactly what
-- `capsAt-suc-full` identifies with the cap at the NEXT instant.  So
-- the frame-wise route delivers the successor cap, and what is owed
-- here is that one instant's whole growth already fits inside the
-- single `frameBlowup` separating this instant's cap from the last --
-- an argument about the recurrence, not another induction over frames.
--
-- AND THE FOLD OVER THE CHAINS IS A BODY, so what is asserted is ONE
-- chain's walk and ONE chain's preservation rather than a selection's
-- worth of both.  The predicate recurses on the list -- a cancelled
-- registration walks nothing and weakens by a chain, a live one owes
-- its own walk and hands the rest the state its step produced -- so the
-- induction is the list's and nothing about it is undecided.  Splitting
-- here is what makes the two obligations greppable: the walk leaf is
-- the one the flat-cap rows measure, and the step leaf is the
-- preservation half those rows report as holding outright on two of the
-- three components.
--
-- AND THE SLOTS HALF IS ALREADY PROVEN, which is why the step leaf
-- carries only the caps: `chainStep-slots` says a step does not move
-- the vocabulary, so threading the equation costs nothing.
--
-- WHAT THE WALK LEAF STILL OWES, AND IT IS NOT THE WALK.  The drain's
-- predicate prices a PARKED inner twice over -- what it nests, and what
-- a level of the walk still has to spend -- and both are stated with
-- HEADROOM: three units above the nesting, and two above the size plus
-- one per level.  Those are the shapes the domination guard wants, and
-- they are the shapes the proven entry mirror takes as hypotheses too,
-- so the conjuncts are not suspect.  What has no source is the
-- headroom itself.
--
-- DEAD ROUTE: reading the headroom off the caps hypothesis cannot
--   work.  A mergeAll queue is store content, so the caps predicate
--   does bound every parked term -- but its store conjunct bounds one
--   by the cap EXACTLY, and the size currency the wet stack measures
--   with is that same projection by definition, so there is no second,
--   smaller number to spend the difference against.  The gap is a
--   constant two and the arithmetic cannot manufacture it; the
--   headroom has to be carried by whatever states the store bound, not
--   recovered downstream of it.

-- AND THE STEP LEAF IS NOT PRESERVATION IN GENERAL, WHICH NARROWS WHAT
-- ITS PROOF MAY REST ON.  Read either side of ONE step rather than a
-- whole cascade, the smallest cap the state fits rises by better than a
-- factor of two -- a drain SUBSCRIBES the inners it releases and the
-- step retires nothing, so what pays for the growth is the cascade's
-- FINISH, one level up and outside this statement.  So a step at an
-- arbitrary cap the pre-state satisfies does NOT return inside it, and
-- no arm-by-arm argument can conclude otherwise: the frame-wise receipt
-- lands at `frameStep (j + j')` and the caps ordering only ever widens.
--
-- WHAT IS LEFT IS THE INSTANT'S OWN SLACK, and it is the whole of the
-- remaining route.  `capsAt` is not an arbitrary cap: it is a
-- `frameBlowup` of the last instant's, so the statement can still be
-- true by that gap being wide enough to swallow one instant's whole
-- growth.  That is an argument about the recurrence -- the same one the
-- block above names -- and it is now the ONLY one available, which is
-- what the finding below buys.  The alternative is to give the predicate
-- the level its consumers already speak in, as the nodes face does.
--
-- AND THE WALK LEAF IS THE SAME STATEMENT, NOT A SIBLING OF IT.  The
-- walk predicate's `root` clause IS `capsOK?` at the state the walk
-- ends on, and a chain's walk ends exactly where its step does -- the
-- path fold and the walk recurse through the same `stepFrame`, and the
-- fold returns the scheduler and state untouched at `root`.  So on any
-- sink-free path the walk leaf IMPLIES the step leaf, the crossing
-- below is a crossing of both, and the two rows are one obligation
-- read at two granularities rather than two things to grind.

-- AND THE LEVEL IS NOW IN BOTH STATEMENTS, WHICH IS WHAT THE FINDING
-- BELOW BOUGHT.  Neither leaf asserts preservation any more: the
-- walk is asserted at `frameStep Lv`, the step is handed a state inside
-- `frameStep Lv` and REPORTS the increment that carries it, and the
-- predicate under them threads that level frame by frame and chain by
-- chain.  That is the discipline the frame receipt beside them has
-- always had, and the flat form is gone from the tree.
--
-- AND THE FLAT CEILING WAS AT THE WRONG GRANULARITY, WHICH IS WHY THE
-- STEP LEAF NOW REPORTS THE WALK'S OWN.  Asking one chain, from a level
-- whose only hypothesis is that it sits under the cascade's count, to
-- land under that same count is a conclusion needing what no hypothesis
-- carries: how much of the count is UNSPENT.  The level ladder climbs
-- one delivery-charge per delivery and never returns, so a chain
-- entered at the count itself must leave above it.  The bound is true
-- of a cascade and false of a chain read alone -- a cascade-level fact
-- stated per chain.
--
-- SO THE STEP LEAF IS STATED AT THE CEILING THE WALK ACTUALLY DELIVERS:
-- one charge per delivery, at THIS chain's base rather than at zero.
-- That is the proven cascade bound's own recurrence, so the fold carries
-- the whole remaining cascade's delivery count as its invariant and the
-- two ledger lines split it chain by chain; the conversion back to the
-- count is `lvls-add` and no longer a leaf.
--
-- AND THE LEVEL PREMISE ON THE WALK LEAF IS NOT A CONVENIENCE.  Without
-- it the statement is false at EVERY program and needs no state to kill:
-- the level is a free parameter, the only hypothesis mentioning it says
-- the state fits the cap AT that level and so gets WEAKER as it rises,
-- and the predicate produced asserts at every frame that the level is
-- under the cascade's count.  A level one above the count satisfies both
-- hypotheses and contradicts the conclusion.  So the bound is a property
-- of the CALL, and the delivery-counted form is the one a caller can
-- actually supply -- this chain's own charge, out of the fold's
-- invariant.
--
-- WHICH LEAVES THE PREDICATE'S OWN FLAT CONJUNCTS AS THE GRIND.  Its
-- frame clause and its share fold each demand a level bound against the
-- cascade's count, one per frame and one per admitted chain, and the
-- premise above is what pays for them: a chain is at most one delivery's
-- charge wide, so every intermediate level sits under the same ceiling.
--
-- REFUTED: `Refuted.Chain-Level-Unbounded` -- the level-free form of
--   THIS statement, at every program at once, by arithmetic rather than
--   by a row: a level one above the count satisfies both hypotheses and
--   breaks the conclusion.  `Refuted.Chain-Step-Flat` -- one step of one
--   chain, at a concrete cap the pre-state satisfies and the post-state
--   does not.  `Refuted.Frame-Step-Compose` -- the step does not
--   compose, so the level cannot be absorbed into the cap the machinery
--   re-enters at.
--
-- DEAD ROUTE: re-entering the frame receipt with its cap parameter
--   instantiated at the STEPPED cap, so that the level needs no
--   threading.  The step's width component iterates an exponential
--   whose base is its size component, and stepping raises the size, so
--   the second step runs at the raised base -- a tower storey per
--   level against a flat count that runs every iteration at the
--   original.  One level either side already overshoots by five orders
--   of magnitude.
--
-- TWIN: `stepFrame-caps` -- the same frame, proven, with exactly the
--   discipline owed here: invariant taken at the stepped cap, own
--   increment reported, conclusion restated at the sum.
--
-- RECOVERY: git show 1281567 restores `Probed.Chain-Walk-Level`, whose
--   `walkSpine` re-walks a path with the evaluator's own `stepFrame`
--   and reads a boolean conjunct at EVERY state the fold passes
--   through, rather than at the two ends a fit row can see.  That is
--   the instrument the three leaves below want: they are exactly the
--   conjuncts it could not pin, and the harness generalises to any of
--   them that is a boolean.
--
-- RECOVERY: git show c415649 restores `Probed.Chain-Caps-Flat`, whose
--   harness reads the SMALLEST FITTING CAP either side of a whole
--   cascade over three families, one component at a time -- the way to
--   find where a cascade's growth actually lands.

-- AND THE FRAME'S REGISTRATION CAP IS THE ROUND'S LEDGER AT ITS OWN
-- LEVEL, which is true by definition and stated anyway: read at a
-- CONCRETE caps both sides unfold the tower, and read at a variable
-- neither does.
