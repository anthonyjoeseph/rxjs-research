-- Verify-Budget-Sufficient.Caps-Face.Part7.Cascade-Nest
-- cascadeGo-nest-nodes, cascadeGo-nest
module Verify-Budget-Sufficient.Caps-Face.Part7.Cascade-Nest where

open import Data.Bool    using (true)
open import Data.Nat     using (ℕ; suc; _+_; _*_; _^_; _⊔_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (*-assoc; *-identityˡ; ^-monoˡ-≤; *-monoˡ-≤; ≤-trans; ≤-refl; ≤-reflexive; m≤m+n; m≤n+m;
  *-mono-≤; *-monoʳ-≤; +-monoʳ-≤; +-monoˡ-≤; +-assoc; ⊔-lub; m≤m⊔n; m≤n⊔m; +-mono-≤)
open import Data.Nat.Solver     using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.List    using (List; length; foldr)
open import Data.Bool.ListAction using (all)
open import Data.Fin     using (Fin)
import Data.Fin as Fin
open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []ᵃ; _∷_ to _∷ᵃ_; map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties
  using (concat⁺; tabulate⁺)
  renaming (++⁺ to all-++; ++⁻ˡ to all-++ˡ; ++⁻ʳ to all-++ʳ)
open import Data.Vec     using (Vec; lookup) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Product using (_×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; sym; subst; cong)

open import Rx.Prim      using (Id; _at_from_as_)
open import Rx.Exp       using (Ctx; Closed; sizeᵛ)
open import Rx.Nest-Depth using (nestDᵛ)
open import Verify-Budget-Sufficient.Nest-Cap using (nestFac; nestFac-monoS; 1≤nestFac; nestU; nestU-mono; nestU-room)
open import Verify-Budget-Sufficient.Nest-Walk using
  (faceAt)
open import Verify-Budget-Sufficient.Caps-Depth using
  (depthCascade)
open import Verify-Budget-Sufficient.Deliver-Measure using
  (chainsDelLen; chainsDelNestD; chainsDelNestF; 1≤chainsDelNestF; chainsDelNestD-chains;
  chainsNestF≤)
open import Verify-Budget-Sufficient.Fan-Caps using
  (fanSq; delSize; delSq; delSq-monoᶜ; delSq-cap)
open import Verify-Budget-Sufficient.Nest-Store using
  (chainsNestD; chainsNestF; storeNestMax; nestCapAt; nestOK?; nestFacAt; 1≤nestFacAt;
  nest-inflate; realWidAt; nestIncAt; nestIncAt-def; m≤m^burst; nestBurstAt; 1≤nestBurstAt;
  nestUnit; slotsNestSum; liveNest; nodeNest; regsNestMax)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; arrVal; RegId; chainsOf; cascadeGo; Path; arrTy)
open import Rx.Slots using (Slots)

open import Verify-Budget-Sufficient.Caps using
  (1≤capsAt-reg; 1≤pow≤; 2≤capsAt-size; Caps; capsAt; capsAt-suc-full; capsAt-⊑-suc; capsH;
  _⊑ᶜ_; frameStep; frameStep-mono-j; size≤sizeCount)
open import Verify-Budget-Sufficient.Measures using
  (all-impl)
open import Verify-Budget-Sufficient.Caps-Depth
  using (depthCascade)

open import Verify-Budget-Sufficient.Caps-Face.Part1 using
  (capsOK?; pathSz?; pathSz?-widen)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Cascade-Caps using
  (cascadeGo-slots)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Cascade-Live using
  (cascadeGo-nest-live)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Chain-Caps-OK using
  (chainsBurstOK; chainsCapsOK)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Cascade-Nodes using
  (cascadeGo-nodes-chains)

cascadeGo-nest-nodes : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id)
  (chains : List (RegId × Path Γ (arrTy a) t))
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (capsAt e sl id) sched st ≡ true →
  nestOK? e sl id sched st ≡ true →
  nestDᵛ (arrTy a) (arrVal a) ≤ nestCapAt e sl id →
  length chains ≤ realWidAt e sl id →
  nestDᵛ (arrTy a) (arrVal a) + chainsNestD chains ≤ nestUnit e sl →
  chainsDelLen n (capsAt e sl (suc id)) chains
    ≤ realWidAt e sl id * delSize n (capsAt e sl (suc id)) →
  -- THE FACTOR IS READ AT THE NEXT INSTANT'S CAP, and that is where the
  -- walk's level dies.  A cascade reports the level its own descent
  -- reached, bounded by `sizeCount c (capsH e sl id)` -- which is
  -- exactly the count `capsAt-suc-full` steps by -- so every quantity
  -- the walk hands back sits under the successor cap and nothing
  -- existential survives into this conclusion.  Reading the premise one
  -- instant later is what buys that, and it costs nothing the caps face
  -- was not already paying: `sub-charge-capsOK-lift` (.Caps-Bridge)
  -- collapses its own level against the same cap by the same chain.
  nestFac (Caps.cSize (capsAt e sl (suc id))) (nestBurstAt e sl id)
      ^ chainsDelLen n (capsAt e sl (suc id)) chains
    * chainsDelNestF n (capsAt e sl (suc id)) chains ^ nestBurstAt e sl id
      ≤ nestFacAt e sl id →
  depthCascade a nextId chains sched st ≤ capsH e sl id →
  chainsBurstOK (nestBurstAt e sl id) a nextId chains sched st →
  chainsCapsOK (capsAt e sl id) (capsAt e sl (suc id)) sl (capsH e sl id) 0 a nextId chains sched st →
  all (λ rc → pathSz? (Caps.cSize (capsAt e sl id)) (proj₂ rc)) chains ≡ true →
  let r = cascadeGo a nextId chains sched st
  in foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes (proj₂ (proj₂ r)))
       ≤ nestFacAt e sl id
         * (storeNestMax sched st + nestIncAt e sl id)
cascadeGo-nest-nodes {n = n} {e = e} sl id a nextId chains sched st hsl hcaps hnest hval hcnt hchg hls hfac hdep hburst hcw hpz =
  ≤-trans (≤-trans (≤-trans (proj₂ (proj₂ CH)) lift)
                   (≤-reflexive
                     (sym (*-assoc (nestFac (Caps.cSize (capsAt e sl (suc id)))
                                            (nestBurstAt e sl id)
                                     ^ chainsDelLen n (capsAt e sl (suc id)) chains)
                                   (chainsDelNestF n (capsAt e sl (suc id)) chains
                                     ^ nestBurstAt e sl id) _))))
    (*-mono-≤ hfac
      (+-mono-≤ nodes≤store
        (≤-trans (*-mono-≤ hcnt
                    (*-monoʳ-≤ (nestBurstAt e sl id)
                      (≤-trans (+-monoˡ-≤ (suc (chainsDelLen n (capsAt e sl (suc id)) chains) * UU)
                                          depth≤)
                               (*-monoˡ-≤ UU (s≤s (s≤s hls))))))
                 (≤-reflexive (sym (nestIncAt-def e sl id))))))
  where

  SS = delSq n (capsAt e sl (suc id))
  UU = nestU SS (nestUnit e sl)

  CH = cascadeGo-nodes-chains (capsAt e sl id) (capsAt e sl (suc id)) (capsH e sl id) (nestBurstAt e sl id)
         sl 0 a nextId chains sched st hsl (1≤nestBurstAt e sl id)
         (≤-trans (s≤s z≤n) (2≤capsAt-size e sl id)) (capsAt-⊑-suc e sl id)
         hburst hcw hdep
         (all-impl _ _
            (λ rc h → pathSz?-widen (proj₂ rc) (proj₁ (capsAt-⊑-suc e sl id)) h)
            chains hpz)
         z≤n
         ⦃ faceAt e sl id ⦄

  -- the level's own ceiling, and the whole of the collapse: the count
  -- the cascade reports is under the one the recurrence steps by, so
  -- the stepped cap is componentwise under the next instant's
  lift-⊑ : frameStep (proj₁ CH) (capsAt e sl id) ⊑ᶜ capsAt e sl (suc id)
  lift-⊑ = subst (λ x → frameStep (proj₁ CH) (capsAt e sl id) ⊑ᶜ x)
                 (sym (capsAt-suc-full e sl id))
                 (frameStep-mono-j (capsAt e sl id) (2≤capsAt-size e sl id)
                                   (≤-trans (proj₁ (proj₂ CH))
                                      (⊔-lub ≤-refl
                                         (size≤sizeCount (capsAt e sl id) (capsH e sl id)
                                            (2≤capsAt-size e sl id) (1≤capsAt-reg e sl id)))))

  lift = *-mono-≤ (^-monoˡ-≤ (chainsDelLen n (capsAt e sl (suc id)) chains)
                     (nestFac-monoS (proj₁ lift-⊑) (nestBurstAt e sl id)))
           (*-monoʳ-≤ (chainsDelNestF n (capsAt e sl (suc id)) chains ^ nestBurstAt e sl id)
             (+-monoʳ-≤ (foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st))
               (*-monoʳ-≤ (length chains)
                 (*-monoʳ-≤ (nestBurstAt e sl id)
                   (+-monoʳ-≤ (nestDᵛ (arrTy a) (arrVal a)
                                + chainsDelNestD n (capsAt e sl (suc id)) chains)
                     (*-monoʳ-≤ (suc (chainsDelLen n (capsAt e sl (suc id)) chains))
                       (nestU-mono (delSq n (frameStep (proj₁ CH) (capsAt e sl id)))
                                   SS (nestUnit e sl)
                         (delSq-monoᶜ n (frameStep (proj₁ CH) (capsAt e sl id))
                                      (capsAt e sl (suc id))
                                      (proj₁ lift-⊑) (proj₂ (proj₂ lift-⊑))))))))))

  -- the walk charges its depth in the delivery currency and the
  -- selection bound is a path fact, so the fan allowance is what sits
  -- between them -- and the unit is priced at the delivery square
  -- precisely so it has room for one
  depth≤ : nestDᵛ (arrTy a) (arrVal a) + chainsDelNestD n (capsAt e sl (suc id)) chains ≤ UU
  depth≤ =
    ≤-trans (+-monoʳ-≤ (nestDᵛ (arrTy a) (arrVal a))
                       (chainsDelNestD-chains n (capsAt e sl (suc id)) chains))
      (≤-trans (≤-reflexive (sym (+-assoc (nestDᵛ (arrTy a) (arrVal a))
                                          (chainsNestD chains)
                                          (fanSq n (capsAt e sl (suc id))))))
        (≤-trans (+-monoˡ-≤ (fanSq n (capsAt e sl (suc id))) hchg)
                 (nestU-room SS (nestUnit e sl)
                             (fanSq n (capsAt e sl (suc id)))
                             (≤-trans (s≤s z≤n) ≤-refl)
                             (≤-trans (m≤n+m (fanSq n (capsAt e sl (suc id)))
                                             (Caps.cSize (capsAt e sl (suc id))
                                                * Caps.cSize (capsAt e sl (suc id))))
                                      (delSq-cap n (capsAt e sl (suc id))
                                                 (1≤capsAt-reg e sl (suc id)))))))


  nodes≤store : foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st) ≤ storeNestMax sched st
  nodes≤store = ≤-trans (m≤n⊔m (NA ⊔ NB) NC) (m≤m⊔n ((NA ⊔ NB) ⊔ NC) ND)
    where
    NA = slotsNestSum (Sched.slots sched)
    NB = foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched)
    NC = foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st)
    ND = regsNestMax (EvalSt.registry st)

-- THE REGISTRY COMPONENT, whose paths only ever gain frames the path
-- measure does not charge.  A walk registers the inners a release
-- subscribes, and a registration's path extends the chain's own with a
-- `from-inner` frame, which is the one frame `pathNestD` charges zero
-- for -- so the deepest registered path after the walk is expected to
-- be one the walk already had in hand.  The measurement agrees at
-- every cell of every family the harness drives.  It is stated at the
-- parent's right-hand side rather than at the tighter bound that
-- reading suggests, because the tighter form needs the chain list to
-- come FROM the registry and this statement takes it free.
--
-- PROBED: `Probed.Cascade-Store-Components` pins this component by
--   `refl` beside the store the walk started from, over three families.
--   It reads ZERO on every one -- every registration the walk touched
--   is retired by the time the cascade ends -- while the node summand
--   in the same rows goes to four times the starting store.  So the
--   increment this row carries is not being spent HERE, and the growth
--   the wider statement pays for is the node table's.  Not covered, and
--   it is the only region that could move this component: a walk that
--   leaves a registration STANDING whose path is deeper than any the
--   store held, which is what the `nestUnit` factor of the increment
--   would have to pay for.  No family reaches it, so the reading is a
--   receipt about retirement rather than about the bound.  TIED at the
--   demand family, with the three cap premises LEFT STANDING as the
--   seal forces, so the row asserts the conclusion with the caps
--   invariant unasked.  The tie is DEGENERATE on the increment for the
--   same reason the readings are: the component is under the starting
--   store before the increment is added, so `m≤m+n` carries the rest
--   and nothing here spends it.
postulate
  cascadeGo-nest-regs : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id)
    (chains : List (RegId × Path Γ (arrTy a) t))
    (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl →
    capsOK? (capsAt e sl id) sched st ≡ true →
    nestOK? e sl id sched st ≡ true →
    nestDᵛ (arrTy a) (arrVal a) ≤ nestCapAt e sl id →
    let r = cascadeGo a nextId chains sched st
    in regsNestMax (EvalSt.registry (proj₂ (proj₂ r)))
         ≤ storeNestMax sched st + nestIncAt e sl id

-- THE WALK'S STORE GROWTH, IN THE WIDTH CURRENCY, AND IT IS PRIMITIVE.
-- One arrival's chain walk leaves the store measure no deeper than it
-- found it plus one `nestSyn` per unit of REAL WIDTH.  The width factor
-- is the content rather than decoration over a narrower truth, and the
-- mechanism is one arc: mergeAll's DRAIN stores each released inner in
-- turn, and it is reached through a `from-inner` frame, which the path
-- measure charges nothing for -- so ONE delivery can store arbitrarily
-- many times, and no charge that counts what the run DID can bound it.
-- `realWidAt` is the one term in this vocabulary that moves with the
-- axis that drives the drain, which is why the width form clears the
-- rows the narrow ones cross on.
--
-- AND THE STORE MEASURE IS A `⊔` OF FOUR COMPONENTS, SO THE ROW SPLITS
-- FOUR WAYS RATHER THAN INDUCTING ONCE.  A least upper bound sits
-- below a target exactly when each of its arms does, so the walk's
-- slot store, its pending sources, its node states and its registry
-- can each be charged this same right-hand side independently.  The
-- slot arm needs no charge at all, the fold threading that store
-- untouched, and the split is worth taking because the three arms
-- that survive it are nowhere near equally hard.
cascadeGo-nest : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id)
  (chains : List (RegId × Path Γ (arrTy a) t))
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (capsAt e sl id) sched st ≡ true →
  nestOK? e sl id sched st ≡ true →
  nestDᵛ (arrTy a) (arrVal a) ≤ nestCapAt e sl id →
  length chains ≤ realWidAt e sl id →
  nestDᵛ (arrTy a) (arrVal a) + chainsNestD chains ≤ nestUnit e sl →
  chainsDelLen n (capsAt e sl (suc id)) chains
    ≤ realWidAt e sl id * delSize n (capsAt e sl (suc id)) →
  nestFac (Caps.cSize (capsAt e sl (suc id))) (nestBurstAt e sl id)
      ^ chainsDelLen n (capsAt e sl (suc id)) chains
    * chainsDelNestF n (capsAt e sl (suc id)) chains ^ nestBurstAt e sl id
      ≤ nestFacAt e sl id →
  sizeᵛ (arrTy a) (arrVal a) ≤ Caps.cSize (capsAt e sl id) →
  depthCascade a nextId chains sched st ≤ capsH e sl id →
  chainsBurstOK (nestBurstAt e sl id) a nextId chains sched st →
  chainsCapsOK (capsAt e sl id) (capsAt e sl (suc id)) sl (capsH e sl id) 0 a nextId chains sched st →
  all (λ rc → pathSz? (Caps.cSize (capsAt e sl id)) (proj₂ rc)) chains ≡ true →
  let r = cascadeGo a nextId chains sched st
  in storeNestMax (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
       ≤ nestFacAt e sl id
         * (storeNestMax sched st + nestIncAt e sl id)
cascadeGo-nest {n = n} {e = e} sl id a nextId chains sched st hsl hcaps hnest hval hcnt hchg hls hfac hsz hdep hburst hcw hpz =
  ⊔-lub (⊔-lub (⊔-lub SL LV) ND) RG
  where
  r   = cascadeGo a nextId chains sched st
  sd′ = proj₁ (proj₂ r)
  st′ = proj₂ (proj₂ r)

  RHS : ℕ
  RHS = storeNestMax sched st + nestIncAt e sl id

  up : RHS ≤ nestFacAt e sl id * RHS
  up = nest-inflate (nestFacAt e sl id) RHS (1≤nestFacAt e sl id)

  base≤ : storeNestMax sched st ≤ RHS
  base≤ = m≤m+n _ _

  SL : slotsNestSum (Sched.slots sd′) ≤ nestFacAt e sl id * RHS
  SL = ≤-trans (≤-reflexive (cong slotsNestSum (cascadeGo-slots a nextId chains sched st)))
               (≤-trans (≤-trans (≤-trans (m≤m⊔n _ _) (≤-trans (m≤m⊔n _ _) (m≤m⊔n _ _))) base≤) up)

  -- ONE CHAIN'S FACTOR OUT OF THE SELECTION'S POWER.  The fanout
  -- premise bounds the whole product raised to the burst; the burst is
  -- a successor and every factor is at least one, so the bare product
  -- comes out of it.
  chF≤fac : chainsNestF chains ≤ nestFacAt e sl id
  chF≤fac =
    ≤-trans (chainsNestF≤ n (capsAt e sl (suc id)) chains)
      (≤-trans (m≤m^burst e sl id (chainsDelNestF n (capsAt e sl (suc id)) chains)
                          (1≤chainsDelNestF n (capsAt e sl (suc id)) chains))
               (≤-trans (≤-trans (≤-reflexive (sym (*-identityˡ _)))
                                 (*-monoˡ-≤ _ (1≤pow≤ (nestFac (Caps.cSize (capsAt e sl (suc id)))
                                                               (nestBurstAt e sl id))
                                                      (chainsDelLen n (capsAt e sl (suc id)) chains)
                                                      (1≤nestFac _ _))))
                        hfac))

  LV : foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sd′) ≤ nestFacAt e sl id * RHS
  LV = cascadeGo-nest-live sl id a nextId chains sched st hsl hcaps hnest hval hsz chF≤fac

  ND : foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st′)
         ≤ nestFacAt e sl id * RHS
  ND = cascadeGo-nest-nodes sl id a nextId chains sched st hsl hcaps hnest hval hcnt hchg hls
         hfac hdep hburst hcw hpz

  RG : regsNestMax (EvalSt.registry st′) ≤ nestFacAt e sl id * RHS
  RG = ≤-trans (cascadeGo-nest-regs sl id a nextId chains sched st hsl hcaps hnest hval) up

-- ONE ARRIVAL'S WHOLE CASCADE, IN THE WIDTH CURRENCY -- and the width
-- factor is the content, not decoration over a narrower truth.  A
-- delivery walks an already-registered chain, so the tempting reading
-- is that it deepens by one operator's worth, and that the cascade is
-- one such step per delivery or per chain.  Every version of that
-- reading is false, and the mechanism is one arc: mergeAll's DRAIN
-- spends a nesting level through `depthFinC`, and it is reached
-- through a `from-inner` frame, which `pathNestD` charges nothing for.
-- Every other level this family spends is paid by a path term --
-- `pathNestD` charges the `thru-outer` frame and only that frame -- so
-- the drain's levels have nothing to come out of but the constant, and
-- a program whose folds nest spends arbitrarily many of them on ONE
-- delivery.  The width factor is what pays for them, and it pays with
-- room to spare.  So this is a primitive statement, and no
-- decomposition that charges by the run is a route to it.
--
-- REFUTED: `Refuted.Cascade-Deliv-Depth`, the per-DELIVERY half, at
--   ONE chain, ONE delivery and no cancellation -- so neither the skip
--   branch nor the phantom tail's delivery count is what kills it.
--   Across the fold parameter the descent climbs six a layer against
--   the bound's three, ties at two and crosses at three.  The BOUNDED
--   limit is the ingredient every earlier family lacked: with nothing
--   parked there is no drain to reach, and the same witness under an
--   unbounded limit clears the bound comfortably.
-- REFUTED: `Refuted.Nest-Depth-One` kills the subscribe-side sibling
--   of the same narrow reading, descent 21 against 19, which is where
--   the arc above was first read off.
-- DEAD ROUTE: a plain structural induction on the chain list, with the
--   bound stated at the entry store.  The cons clause's THIRD arm reads
--   the tail at the state the head's `chainStep` left, and that state's
--   store is strictly deeper -- measured at three before the step and
--   twelve after it, on one chain and one delivery -- so the induction
--   hypothesis is being applied at a store the conclusion does not
--   mention.  Nothing about the arm can be repaired locally: the two
--   surviving arms close against the entry store and this one cannot,
--   whatever the head-arm leaf says.  What it needs is a generalisation
--   that THREADS the store growth as a budget, and the quantity it
--   would thread is `cascadeGo-nest`'s, the row above -- so that row is
--   a genuine prerequisite of this one rather than a sibling.
-- DEAD ROUTE: the head arm without a width term, `depthChain` under the
--   payload nesting plus the path's plus the store's.  It is attractive
--   because the drain's unpaid levels come out of what is STORED, which
--   is the one term that already accounts for them.  The grid refutes it
--   without a new probe: at a single chain the whole cascade IS its head
--   arm, and the descent moves with the source length while the payload
--   nesting, the path measure and the store are each flat in it.
-- DEAD ROUTE: charging per CHAIN instead.  That clause CLOSES, which
--   the per-delivery one does not -- both tails take the hypothesis at
--   `length chains`, and the head is the one chain by which `suc`
--   exceeds it -- but the leaf under it is a single delivery within
--   one `nestSyn`, and that charge is SMALLER than the per-delivery
--   one wherever a chain is skipped, so the same witness kills it a
--   fortiori.
--
-- RECOVERY: `git show f53fff4:agda/src/Verify-Budget-Sufficient/Caps-Face/Part7.agda`
--   restores the per-chain assembly and its four leaves -- the marked-state
--   helper, the chain-step store and caps-at-the-next-index transports, and
--   the registry count under the real width.  The chain-step transports are
--   about `chainStep` alone and survive the refutation of what consumed
--   them; the assembly does not.

-- AND THE SAME SELECTION AGAINST THE SYNTACTIC CEILING, which is the
-- fact that ties a walk's charge back to the program.  A registration's
-- path is a rootward walk through `e`'s own spine, and `pathNestD`
-- charges the `thru-outer` frame and only that frame -- one per *All
-- layer, which is exactly the `suc` `nestDᵉ` spends on the same layer --
-- so the deepest registered chain is within `nestDᵉ e`.  The PAYLOAD is
-- not in the registry at all: it came from a slot, so it is within that
-- slot's own nesting and hence within `slotsNestSum`.  Adding the two
-- lands inside `nestSyn`, which is their sum plus one.
--
-- IT IS STATED OVER THE SELECTION AND NOT OVER A FREE LIST, and that is
-- the whole content: a path nobody registered may carry a `scan` frame
-- whose function wraps deeper than the program it is being charged
-- against, so the free-list form of this bound does not survive.
--
-- REFUTED: `Refuted.Chain-Step-Nodes`, the free-path form, eleven
--   against nine and unbounded in the frame's fold depth.
-- PROBED: `Probed.Cascade-Chain-Count` reads this by `refl` on five
--   families AFTER the walk has run several instants, which is the only
--   half worth having: at the ENTRY arrival the registry holds nothing
--   but what the root subscribe put there and the reading comes back at
--   2 against a whole `nestSyn`, so a sweep of first instants cannot
--   fail.  Registrations deepen when a release SUBSCRIBES an inner, so
--   the chains that could cross this sit past the first cascade.  One
--   row drives the FOLD DEPTH, which is the axis that moves both sides
--   at once -- the wrap is in the scan's own function, so it lands in
--   `pathNestD` of every chain through that frame and in `nestDᵉ` of
--   the program together.  COVERED is the conclusion; the premises
--   compute nowhere.  TIED at the entry arrival with both cap premises
--   LEFT STANDING, which the seal forces and which makes the row a
--   stronger claim than this instance rather than a weaker one: what
--   it asserts is the conclusion with the caps invariant unasked.  NOT
--   covered: `Γ₂`, and the vocabulary runs dry
--   after a handful of arrivals -- a row past the end announces itself,
--   reading its verdict false rather than passing quietly.
postulate
  arr-chains-nest-syn : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl →
    capsOK? (capsAt e sl id) sched st ≡ true →
    nestOK? e sl id sched st ≡ true →
    nestDᵛ (arrTy a) (arrVal a) + chainsNestD (chainsOf a st) ≤ nestUnit e sl

-- THE FANOUT'S EXPONENT, AND IT IS A READING OF THE SIZE INVARIANT
-- RATHER THAN A NEW BET.  `capsOK?` carries `regsSz?` over the whole
-- registry, and `pathSz?` is two conjuncts per frame: the step
-- function's own size within the cap, and the path's LENGTH within the
-- same cap.  A path therefore charges at most cap-many frames of at
-- most cap-many units each, and a cascade's chain list is a selection
-- within the real width -- so the sum is the width times the cap
-- squared, with no appeal to what the run does.
--
-- IT IS STATED IN THE SIZE CURRENCY AND NOT THE FANOUT ONE, which is
-- what keeps it provable: the exponential is peeled off by
-- `chainsNestF≡` above the leaf, so nothing under here ever multiplies.
-- the selection inherits the registry's own size predicate, filter and
-- retag alike
