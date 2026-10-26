{-# OPTIONS --guardedness #-}

-- A NODE'S RUN IN ORDER, WHAT IT LEAVES RUNNING TRAILING IT, node by
-- node, in the environment its connects give it.  A frame of one child
-- passes its child's shape as it is; a tape, an of, a joiner, a take, a
-- merge, a connect and a run read through its tail are the leaves.
--
-- A body fed the rest past a source's skips is a body of the stepped
-- tree, read in its own environment (`adequacy.Engine.FedWalk.fed-trail`).
module adequacy.Engine.Trails where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_; [_]; _ʳ++_)
import Data.List as L
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_; map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to All++⁺)
open import Data.Sum using (inj₁)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Tree using (Obs)
open import denotation.MonotonicList.Events using (Events; Timeline)
open import Data.Unit using (tt)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (lookup)

open import denotation.MonotonicList.Events using (Events∞; Pos; idle; ix; last; end; _∪_)
open import denotation.MonotonicList using (MonotonicList) renaming (cold to coldᴹ)
import denotation.MonotonicList as M′
open import denotation.Denote using (flatOp)
open import denotation.Unfold using (NEnv; Node; meaning; Source; live; ended; stateᴺ; cutᴺ; idleᶜ; restᶜ; connectᶜ; subscribe;
  states; joined; fedᴺ; put)
open import operation.PureObservable using (module Machine)
open Machine using (St; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS; Ctx; top; inMap; inScan; inCut; inLn;
  inTake; inOuter; inLanes; inSrc; inBody; plug; cs; CS; _⊕_)
open import adequacy.Engine.Meaning using (vals; endOf; gh; envAt; srcG; srcRun; srcState; subOr; lane; lanesL; liveL; holeL; flagOf)
open import adequacy.Engine.Above using (Above; states-++; live-hole)
open import adequacy.Engine.Keys using (Shape′; Shape; LaneKeys; []ᴷ; _∷ᴷ_; OuterKeys; outerOf; Fed; Joins; ConnAt; Held; Here; Keyed; KeyedL; SubKeys; EndKeys;
  keyed-at; keyedL-ʳ++)
open import adequacy.Placed.Order using (every-lookup; sorted-headed; sorted-lookup; ordered-rejoin; steady-rejoin; Alienᴱ; Disjoint;
  Ordered; Owned; Sorted; Steady; Every; Every∞; EveryT; Everyᴱ; every-monoᴱ; Headed;
  every-mono; everyT-mono; prefix-++; every-tail; everyT-burstOn; everyT-idle; everyT-∪;
  every∞-mono; headed-snoc; ordered-map; ordered-scan; steady-map; steady-scan)
open import adequacy.Placed using (ordered-sub; steady-sub; spread-subᶠ)
open import adequacy.Finite using (trunc; finite-trunc; trunc-agree)
open import adequacy.Placed.Keys using (module Merge; alienᴱ-owned; beneath-owned; prefix-refl; values-map; owned-trans; values-mono; every-beside; every-map; every-scan)
open import adequacy.Placed.Trail using (Parted; Spread; spread-lim; tick-beneath; trail-map; Trail; Trailing; trail; trailᶠ;
  trail-idle; trail-scan; trail-rejoin; sortedT-idle; flatT-idle)
open import adequacy.Placed.Burst using (module Bursting; Fresh; FreshRun; ordered-tail; steady-tail; trail-tail)
open import adequacy.Placed.Walk using (module Walk)
open import adequacy.Placed.Rising using (Rise; Rules; module Reach; apartRules; keyedRules; rise-sub; headed-sub; headedRules; ordered-take; steady-take)
open import adequacy.Placed.FlatAfter using (module FlatAfter; trail-take)
open import adequacy.Placed.FlatOrder using (module FlatOrder)
open import adequacy.Placed.Calm using (calm-steady; calm-trail)
open import operation.AbstractObservable using (free; cpAt; cutAt; overAt)
open Events∞

------------------------------------------------------------------------
-- Shapes

-- Nothing running.
shape-idle : ∀ {Γ A} (ρ : NEnv Γ) → Shape {A} (stateᴺ idleᶜ ρ)
shape-idle ρ = ((record { ordered = tt } , record { steady = tt }) , record { every = tt } , everyT-idle) , trail-idle _ tt

postulate
  -- A SUBSCRIPTION'S CUTS TRAIL ITS RUN, finite or not: a limit over
  -- `adequacy.Placed.trailing-subᶠ` once a truncation's cut agrees as its
  -- run does (`adequacy.Finite.trunc-agree`).
  trailing-sub : ∀ {Γ A} (o : Obs Timeline Γ A) p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
               → Trailing (stateᴺ (subscribe o p) ρ)
  -- WHAT A SUBSCRIPTION LEAVES RUNNING KEEPS ANY RULES ITS RUN KEEPS,
  -- finite or not: a limit over `adequacy.Placed.Rising.Reach.reachᶠ`.
  reach-cut : ∀ (Rs : Rules) {Γ A} (o : Obs Timeline Γ A) k (ρ : NEnv Γ) → Rules.S Rs k → Everyᴱ (Rules.Src Rs) ρ
            → EveryT (Rules.P Rs) (cutᴺ (subscribe o k) ρ)

-- A RUN READ THROUGH ITS TAIL: what it leaves running, in order, steady
-- and headed, trailing itself.
shape-rest : ∀ {Γ A B} (n : Node Γ A) (ρ : NEnv Γ) → Shape (stateᴺ n ρ) → Shape (stateᴺ (restᶜ {B = B} n) ρ)
shape-rest n ρ (_ , tr) with cutᴺ n ρ | trail tr | trailᶠ tr
shape-rest n ρ ((_ , _ , et) , _) | c | st , _ | ft =
  ((ordered-tail c st , steady-tail c ft) , every-tail c et , et) , trail-tail c st ft

-- A TAKEWHILE OWING ITS COMPLETION: its end, ahead of what its source
-- leaves running.
shape-ending : ∀ {Γ A} i p k (s : St Γ A) (ρ : NEnv Γ) → Here (takeS i p (cpAt k) s) ρ
             → Shape (stateᴺ (gh s) ρ) → Shape (stateᴺ (gh (takeS i p (cpAt k) s)) ρ)
shape-ending i p k s ρ hr ((_ , _ , et) , tr) =
  ((record { ordered = tt } , record { steady = tt }) , record { every = proj₁ hr } , et) , tr′
  where tr′ : Trail (end (k ⊕ (last ∷ []))) (cutᴺ (gh s) ρ)
        trail  tr′ = proj₁ (trail tr) , proj₂ hr , tt
        trailᶠ tr′ = trailᶠ tr

-- A TAKEWHILE: owing nothing, its source's run cut at the first value
-- failing; cut or over, its source's tail.
shape-take : ∀ {Γ A} i p w (s : St Γ A) (ρ : NEnv Γ) → Here (takeS i p w s) ρ
           → Shape (stateᴺ (gh s) ρ) → Shape (stateᴺ (gh (takeS i p w s)) ρ)
shape-take i p free       s ρ hr (((o , st) , ev , et) , tr) =
  ((ordered-take i p _ o , steady-take i p _ st) , Reach.every-take headedRules i p _ ev , et) , trail-take i p _ _ o st tr
shape-take i p (cpAt k)   s ρ hr sh = shape-ending i p k s ρ hr sh
shape-take i p (cutAt k)  s ρ hr sh = shape-rest (gh s) ρ sh
shape-take i p (overAt k) s ρ hr sh = shape-rest (gh s) ρ sh

-- A connect's run and cut, read off its body's state and its source's.
beside-go : ∀ {X B} p (hp : Headed p) (β : Events∞ B) (σ : Events∞ X) → Shape σ → Shape β
          → Every∞ (Owned (p ++ [ ix 0 ])) β → Every∞ (Rise (p ++ [ ix 1 ])) β → FreshRun (p ++ [ ix 0 ]) (force β)
          → Σ Pos (λ l → Owned (p ++ [ ix 0 ]) l × Bursting.Cue (p ++ [ ix 1 ]) l (force σ) × EveryT (Fresh (p ++ [ ix 0 ]) l) (cut β))
          → Every∞ (Disjoint (p ++ [ ix 0 ])) σ → Every∞ (Owned (p ++ [ ix 1 ])) σ → Walk.UB p hp β σ
          → Shape′ (M′.beside (p ++ [ ix 1 ]) β σ) (M′.burstOn (p ++ [ ix 1 ]) σ ∪ cut β)
beside-go p hp β σ (((os , ss) , hs) , ts) (((ob , sb) , hb) , tb) kb kr fr (lf , lo , lc , fc) ks rs ub =
  ((Walk.or-beside p hp β σ ts os ob , Walk.st-beside p hp β σ ts os ss sb ub)
  , every-beside (p ++ [ ix 1 ]) β σ hb (every∞-mono (λ h hh → hh , headed-snoc h hh) σ hs)
  , everyT-∪ _ (cut β) (everyT-burstOn (p ++ [ ix 1 ]) σ hs) (proj₂ hb))
  , Walk.tr-beside p hp β σ (record
      { tb = tb ; ts = ts ; os = os ; ss = ss ; kb = kb ; ks = ks ; kr = kr ; hs = hs ; rs = rs
      ; lf = lf ; lo = lo ; lc = lc ; fc = fc ; fr = fr })

-- A body beside its source, the source subscribed one past a head: in
-- order, steady, headed and trailed by what each leaves running.
beside-shape : ∀ {Γ X B} p (hp : Headed p) (n : Node (X ∷ Γ) B) (σ : Source Γ X) (ρ : NEnv Γ)
             → Shape (srcState σ ρ) → Shape (stateᴺ n (srcRun σ ρ ∷ᴬ ρ))
             → Every∞ (Owned (p ++ [ ix 0 ])) (stateᴺ n (srcRun σ ρ ∷ᴬ ρ)) → Every∞ (Rise (p ++ [ ix 1 ])) (stateᴺ n (srcRun σ ρ ∷ᴬ ρ))
             → FreshRun (p ++ [ ix 0 ]) (force (stateᴺ n (srcRun σ ρ ∷ᴬ ρ)))
             → Σ Pos (λ l → Owned (p ++ [ ix 0 ]) l × Bursting.Cue (p ++ [ ix 1 ]) l (force (srcState σ ρ))
                          × EveryT (Fresh (p ++ [ ix 0 ]) l) (cut (stateᴺ n (srcRun σ ρ ∷ᴬ ρ))))
             → Every∞ (Disjoint (p ++ [ ix 0 ])) (srcState σ ρ) → Every∞ (Owned (p ++ [ ix 1 ])) (srcState σ ρ)
             → Walk.UB p hp (stateᴺ n (srcRun σ ρ ∷ᴬ ρ)) (srcState σ ρ)
             → Shape (stateᴺ (connectᶜ (p ++ [ ix 1 ]) n σ) ρ)
beside-shape p hp n (live s)    ρ shS shB kb kr fr cu ks rs ub =
  beside-go p hp (stateᴺ n (meaning s ρ ∷ᴬ ρ)) (stateᴺ s ρ) shS shB kb kr fr cu ks rs ub
beside-shape p hp n (ended c t) ρ shS shB kb kr fr cu ks rs ub =
  beside-go p hp (stateᴺ n (end c ∷ᴬ ρ)) (stateᴺ t ρ) shS shB kb kr fr cu ks rs ub

-- A connect done with neither, at its source's mark.
conn-core : ∀ {Γ X B} k (o : St Γ X) (b : St (X ∷ Γ) B) (ρ : NEnv Γ) (m : Here (connS k o b) ρ)
     → Shape (srcState (srcG k o) ρ) → Shape (stateᴺ (gh b) (srcRun (srcG k o) ρ ∷ᴬ ρ))
     → Shape (stateᴺ (connectᶜ (CS.srcAt k) (gh b) (srcG k o)) ρ)
conn-core k o b ρ m shS shB =
  subst (λ r → Shape (stateᴺ (connectᶜ r (gh b) (srcG k o)) ρ)) (sym (ConnAt.at m))
    (beside-shape (ConnAt.mark m) (ConnAt.hm m) (gh b) (srcG k o) ρ shS shB
      (ConnAt.kb m) (ConnAt.kr m) (ConnAt.fr m) (ConnAt.cue m) (ConnAt.ks m) (ConnAt.rs m) (ConnAt.ub m))

-- A CONNECT: its body beside its source, read through its tail once it
-- owes its completion or its source has gone.
shape-conn : ∀ {Γ X B} k (o : St Γ X) (b : St (X ∷ Γ) B) (ρ : NEnv Γ) → Here (connS k o b) ρ
           → Shape (srcState (srcG k o) ρ) → Shape (stateᴺ (gh b) (srcRun (srcG k o) ρ ∷ᴬ ρ))
           → Shape (stateᴺ (gh (connS k o b)) ρ)
shape-conn k@(cs cl sl sa ba as (just q) r en) o b ρ m shS shB = shape-rest (connectᶜ r (gh b) (srcG k o)) ρ (conn-core k o b ρ m shS shB)
shape-conn k@(cs cl false sa ba as nothing r en) o b ρ m shS shB = shape-rest (connectᶜ r (gh b) (srcG k o)) ρ (conn-core k o b ρ m shS shB)
shape-conn k@(cs cl true sa ba as nothing r en) o b ρ m shS shB = conn-core k o b ρ m shS shB

------------------------------------------------------------------------
-- A merge

module FlatShape (p : Pos) where
  open module O = FlatOrder p using (K; Ok; Under; Gen; Heldᴹ; Aside; Pool; Roots; []ᴿ; _∷ᴿ_; under-k; lane-ok)
  module KM = Merge K Ok (λ h kh → owned-trans p h (h ++ [ ix 0 ]) (proj₁ kh) (inj₁ (prefix-++ h [ ix 0 ])) , headed-snoc h (proj₂ kh)) lane-ok

  roots-of : ∀ {B} {ls : List (Events∞ B)} {rs} → All Shape ls → LaneKeys p ls rs → Roots ls rs
  roots-of []ᴬ []ᴷ = []ᴿ
  roots-of ((((os , ss) , _) , tr) ∷ᴬ shs) (((kx , kc) , ok , sp) ∷ᴷ lk) = O.lane os ss tr kx kc ok sp ∷ᴿ roots-of shs lk

  roots-k : ∀ {B} {ls : List (Events∞ B)} {rs} → Roots ls rs → All (Every∞ K) ls
  roots-k []ᴿ = []ᴬ
  roots-k (_∷ᴿ_ {r = r} st R) =
    (every-mono (λ h u → under-k r h (O.Lane.ok st) u) _ (O.Lane.kx st) , everyT-mono (λ h u → under-k r h (O.Lane.ok st) u) _ (O.Lane.kc st)) ∷ᴬ roots-k R

  gen-k : ∀ {B} (m : MonotonicList B) → Gen m → KM.Lane m
  gen-k m g j ok = every∞-mono (λ h u → under-k j h ok u) (M′.enter m j) (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (g j ok))))))

  held-k : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) → Heldᴹ o → KM.Outerᴹ o
  held-k nothing  h = tt
  held-k (just e) h = KM.outer-of (force e) (O.Outer.kx h) (values-mono gen-k (force e) (O.Outer.spn h)) , O.Outer.kc h

  -- A MERGE IN FLIGHT: in order, steady, headed, trailed by what it
  -- leaves running.
  flat-shape : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t {rs} → Roots ls rs → Parted rs → All (Aside o) rs → All Gen qs
             → Heldᴹ o → Pool o rs t → Shape′ (M′.go op o ls qs t) (M′.whole o ls t)
  flat-shape op o ls qs t R pt asd gq h pl =
    ((O.ordered-go op o ls qs t R pt asd gq h pl , calm-steady _ (proj₂ c))
    , every-mono (λ _ → proj₂) _ (KM.every-go op o ls qs t ho hl hq hp)
    , everyT-mono (λ _ → proj₂) _ (KM.everyT-whole o ls t ho hl hp))
    , calm-trail _ _ (proj₁ c) (proj₂ c)
    where
      c  = FlatAfter.calm-at p op o ls qs t R pt asd gq h pl
      ho = held-k o h
      hl = roots-k R
      hq = mapᴬ (λ {m} → gen-k m) gq
      hp = everyT-mono (λ _ → proj₂) t (proj₁ (proj₂ (proj₂ pl)))

-- A SUBSCRIPTION SPREADS, finite or not.
spread-sub : ∀ {Γ A} (o : Obs Timeline Γ A) p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ → Spread (meaning (subscribe o p) ρ)
spread-sub o p ρ hp so cl =
  spread-lim (λ n → meaning (subscribe (trunc n o) p) ρ) _ (λ n → spread-subᶠ (trunc n o) (finite-trunc n o) p ρ hp so cl)
    (λ n → trunc-agree n o p ρ)

-- A subscription's run and what it leaves running, by any rules.
reach∞ : ∀ (Rs : Rules) {Γ A} (o : Obs Timeline Γ A) k (ρ : NEnv Γ) → Rules.S Rs k → Everyᴱ (Rules.Src Rs) ρ
       → Every∞ (Rules.P Rs) (stateᴺ (subscribe o k) ρ)
reach∞ Rs o k ρ sk sρ = Reach.reach Rs o k ρ sk sρ , reach-cut Rs o k ρ sk sρ

-- A MERGE'S LANE subscribed wherever a lane may fits there.
gen-sub : ∀ {Γ A C} p (f : A → Obs Timeline Γ C) (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
        → ∀ a → FlatOrder.Gen p (coldᴹ λ q → stateᴺ (lane f a q) ρ)
gen-sub p f ρ hp so cl a j (bj , hj) =
  ordered-sub (f a) j ρ hj so cj , rise-sub (f a) j ρ hj , steady-sub (f a) j ρ hj so cj , trailing-sub (f a) j ρ hj so cj
  , FlatAfter.under∞ p j L
      (every∞-mono (beneath-owned j) L (reach∞ (keyedRules j) (f a) j ρ (inj₁ (prefix-refl j)) (every-monoᴱ (λ _ _ → tt) ρ cj)))
      (reach∞ headedRules (f a) j ρ hj (sorted-headed ρ so))
      (λ R okR d → every∞-mono (λ _ → proj₁) L
         (reach∞ (apartRules R (tick-beneath p R hp (proj₁ okR))) (f a) j ρ d (alienᴱ-owned p R (beneath-owned p R (proj₁ okR)) ρ cl)))
  , spread-sub (f a) j ρ hj so cj
  where
    L  = stateᴺ (subscribe (f a) j) ρ
    cj = alienᴱ-owned p j (beneath-owned p j bj) ρ cl

-- A merge's queue, each a lane its generator fits.
gen-queue : ∀ {Γ A C} p (f : A → Obs Timeline Γ C) (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
          → ∀ qs → All (FlatOrder.Gen p) (L.map (λ a → coldᴹ λ q → stateᴺ (lane f a q) ρ) qs)
gen-queue p f ρ hp so cl []       = []ᴬ
gen-queue p f ρ hp so cl (a ∷ qs) = gen-sub p f ρ hp so cl a ∷ᴬ gen-queue p f ρ hp so cl qs

-- The live lanes of a merge, newest first.
lanes-shape : ∀ {Γ C} (ρ : NEnv Γ) (ls : List (St Γ C)) → All (λ l → Shape (stateᴺ (gh l) ρ)) ls → All Shape (states (lanesL ls) ρ)
lanes-shape ρ []       []ᴬ        = []ᴬ
lanes-shape ρ (l ∷ ls) (sh ∷ᴬ shs) =
  subst (All Shape) (sym (states-++ (lanesL ls) (liveL l) ρ))
    (All++⁺ (lanes-shape ρ ls shs) (subst (All Shape) (sym (live-hole l ρ)) (hole (flagOf l) sh)))
  where hole : ∀ b → Shape (stateᴺ (gh l) ρ) → All Shape (holeL b (stateᴺ (gh l) ρ))
        hole true  sh = sh ∷ᴬ []ᴬ
        hole false sh = []ᴬ

-- The outer of a merge, held.
held-of : ∀ {Γ A C} p (f : A → Obs Timeline Γ C) dn (s : St Γ A) (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ → Shape (stateᴺ (gh s) ρ)
        → OuterKeys p (outerOf f dn s ρ) → FlatOrder.Heldᴹ p (outerOf f dn s ρ)
held-of p f true  s ρ hp so cl sh ok = tt
held-of p f false s ρ hp so cl (((os , ss) , _) , tr) (sp , (kx , kc)) =
  FlatOrder.outer (ordered-map F _ os) (steady-map F _ ss) (trail-map F _ _ tr) sp kx kc (values-map F _ (gen-sub p f ρ hp so cl))
  where F = λ a → coldᴹ λ q → stateᴺ (lane f a q) ρ

-- A MERGE: its outer's run and its lanes', keyed under its mark.
shape-flat : ∀ {Γ A C} op (f : A → Obs Timeline Γ C) dn n qs (s : St Γ A) (ls : List (St Γ C)) (ρ : NEnv Γ)
           → Here (flatS op f dn n qs s ls) ρ → Sorted ρ
           → Shape (stateᴺ (gh s) ρ) → All (λ l → Shape (stateᴺ (gh l) ρ)) ls
           → Shape (stateᴺ (gh (flatS op f dn n qs s ls)) ρ)
shape-flat op f dn n qs s ls ρ (p , hp , cl , rs , lk , pt , asd , ok , pl) so sh shs =
  FlatShape.flat-shape p (flatOp op) _ _ _ _ (FlatShape.roots-of p (lanes-shape ρ ls shs) lk) pt asd
    (gen-queue p f ρ hp so cl qs) (held-of p f dn s ρ hp so cl sh ok) pl

------------------------------------------------------------------------
-- A joiner

-- What a joiner shows after its feed.
joined-shape : ∀ {Γ A} (i : A ∈ Γ) p c (ρ : NEnv Γ) → Sorted ρ → Joins i p c ρ → Shape′ (joined i p c ρ) idle
joined-shape i p (just c) ρ so hc =
  ((record { ordered = tt } , record { steady = tt }) , record { every = hc } , everyT-idle) , trail-idle (end c) tt
joined-shape i p nothing  ρ so (hp , al) =
  ((ordered-rejoin p E os ss , steady-rejoin p E os ss al) , Reach.every-rejoin headedRules p E hp (every-lookup Headed ρ (sorted-headed ρ so) i) , everyT-idle)
  , trail-rejoin p E
  where E = lookup ρ i
        os = proj₁ (sorted-lookup ρ so i)
        ss = proj₂ (sorted-lookup ρ so i)

-- A feed shown ahead of the rest.
fed-shape : ∀ {A} xs (x : Events A) → Fed xs x → Shape′ x idle → Shape′ (fedᴺ xs x) idle
fed-shape []                 x fd        sh = sh
fed-shape ((q , just a) ∷ xs) x ((hq , at , ps) , fd) sh with fed-shape xs x fd sh
... | ((os , ss) , ev , _) , tr = ((record { ordered = at , os } , record { steady = ps , ss }) , record { every = hq , ev , everyT-idle } , everyT-idle) , tr′
  where tr′ : Trail (put q (just a) (fedᴺ xs x)) idle
        trail  tr′ = sortedT-idle , everyT-idle , tr , everyT-idle
        trailᶠ tr′ = flatT-idle
fed-shape ((q , nothing) ∷ xs) x ((hq , at , cl) , fd) sh with fed-shape xs x fd sh
... | ((os , ss) , ev , _) , tr = ((record { ordered = at , os } , record { steady = cl , ss }) , record { every = hq , ev , everyT-idle } , everyT-idle) , tr′
  where tr′ : Trail (put q nothing (fedᴺ xs x)) idle
        trail  tr′ = sortedT-idle , everyT-idle , tr
        trailᶠ tr′ = flatT-idle

-- A JOINER: its feed, then its source's run rejoined or its told end.
shape-join : ∀ {Γ A} j g y ib (ρ : NEnv Γ) → Here {A = A} (joinS j g y ib) ρ → Sorted ρ
           → Shape (stateᴺ (gh (joinS j g y ib)) ρ)
shape-join j false y ib ρ h so = shape-idle ρ
shape-join j true  y ib ρ h so = fed-shape (vals ib) _ (proj₂ h) (joined-shape y j (endOf ib) ρ so (proj₁ h))

------------------------------------------------------------------------
-- The walk

sorted-cons : ∀ {Γ X} {e : Events X} {ρ : NEnv Γ} → (Ordered e × Steady e) × Every Headed e → Sorted ρ → Sorted (e ∷ᴬ ρ)
sorted-cons (os , ev) so = os , ev , so

-- What a connect's source has run, in order and headed: its run, else
-- an end under a head.
src-sorted : ∀ {Γ X} k (o : St Γ X) (ρ : NEnv Γ) → EndKeys k → Shape (srcState (srcG k o) ρ)
           → (Ordered (srcRun (srcG k o) ρ) × Steady (srcRun (srcG k o) ρ)) × Every Headed (srcRun (srcG k o) ρ)
src-sorted (cs cl sl sa (just p) as ow r en) o ρ ek (((o′ , st) , ev , _) , _) = (o′ , st) , ev
src-sorted (cs false sl sa nothing as ow r en) o ρ ek (((o′ , st) , ev , _) , _) = (o′ , st) , ev
src-sorted (cs true sl sa nothing as ow r en) o ρ ek sh = (record { ordered = tt } , record { steady = tt }) , record { every = ek }

-- EVERY NODE KEEPING ITS OWN IS IN SHAPE, read in an environment in order.
mutual
  shape-keyed : ∀ {Γ A} (s : St Γ A) (ρ : NEnv Γ) → Keyed s ρ → Sorted ρ → Shape (stateᴺ (gh s) ρ)
  shape-keyed (pend o)        ρ ky so = shape-idle ρ
  shape-keyed (coldS b l)     ρ ky so = proj₁ ky
  shape-keyed (ofS i p xs)    ρ ky so = proj₁ ky
  shape-keyed doneS           ρ ky so = shape-idle ρ
  shape-keyed (mapS f s)      ρ ky so with shape-keyed s ρ (proj₂ ky) so
  ... | ((o , st) , ev , et) , tr = ((ordered-map f _ o , steady-map f _ st) , every-map f _ ev , et) , trail-map f _ _ tr
  shape-keyed (scanS f z s)   ρ ky so with shape-keyed s ρ (proj₂ ky) so
  ... | ((o , st) , ev , et) , tr = ((ordered-scan f z _ o , steady-scan f z _ st) , every-scan f z _ ev , et) , trail-scan f z _ _ tr
  shape-keyed (cutS true a s)  ρ ky so = shape-keyed s ρ (proj₂ ky) so
  shape-keyed (cutS false a s) ρ ky so = shape-rest (gh s) ρ (shape-keyed s ρ (proj₂ ky) so)
  shape-keyed (lnS b s)       ρ ky so = shape-keyed s ρ (proj₂ ky) so
  shape-keyed (takeS i p w s) ρ ky so = shape-take i p w s ρ (proj₁ ky) (shape-keyed s ρ (proj₂ ky) so)
  shape-keyed (flatS op f dn n qs s ls) ρ ky so =
    shape-flat op f dn n qs s ls ρ (proj₁ ky) so (shape-keyed s ρ (proj₁ (proj₂ ky)) so) (shape-keyedL ls ρ (proj₂ (proj₂ ky)) so)
  shape-keyed (connS k o b)   ρ ky so =
    shape-conn k o b ρ (proj₁ ky) shS (shape-keyed b (srcRun (srcG k o) ρ ∷ᴬ ρ) (proj₂ (proj₂ ky)) (sorted-cons (src-sorted k o ρ (ConnAt.ends (proj₁ ky)) shS) so))
    where shS = src-shape k o b ρ (proj₁ ky) (proj₁ (proj₂ ky)) so
  shape-keyed (joinS j g y ib) ρ ky so = shape-join j g y ib ρ (proj₁ ky) so

  shape-keyedL : ∀ {Γ A} (ls : List (St Γ A)) (ρ : NEnv Γ) → KeyedL ls ρ → Sorted ρ → All (λ l → Shape (stateᴺ (gh l) ρ)) ls
  shape-keyedL []       ρ ky so = []ᴬ
  shape-keyedL (l ∷ ls) ρ ky so = shape-keyed l ρ (proj₁ ky) so ∷ᴬ shape-keyedL ls ρ (proj₂ ky) so

  -- A connect's source, subscribed at its body's mark, running, or ended.
  src-shape : ∀ {Γ X B} k (o : St Γ X) (b : St (X ∷ Γ) B) (ρ : NEnv Γ) → Here (connS k o b) ρ → Keyed o ρ → Sorted ρ
            → Shape (srcState (srcG k o) ρ)
  src-shape (cs cl sl sa (just p) as ow r en) o b ρ m ko so = shape-sub p o ρ (ConnAt.sub m) ko so
  src-shape (cs false sl sa nothing as ow r en) o b ρ m ko so = shape-keyed o ρ ko so
  src-shape (cs true sl sa nothing as ow r en) o b ρ m ko so = shape-rest (gh o) ρ (shape-keyed o ρ ko so)

  -- A source subscribed at its body's mark: fresh, by the subscription's
  -- own order; else as it runs.
  shape-sub : ∀ {Γ X} p (o : St Γ X) (ρ : NEnv Γ) → SubKeys (just p) ρ → Keyed o ρ → Sorted ρ
            → Shape (stateᴺ (subOr (p ⊕ (ix 1 ∷ [])) o) ρ)
  shape-sub p (pend o) ρ (hq , al) ko so =
    ((ordered-sub o q ρ hq so al , steady-sub o q ρ hq so al) , headed-sub o q ρ hq so , reach-cut headedRules o q ρ hq (sorted-headed ρ so))
    , trailing-sub o q ρ hq so al
    where q = p ⊕ (ix 1 ∷ [])
  shape-sub p o@(coldS _ _)   ρ sk ko so = shape-keyed o ρ ko so
  shape-sub p o@(ofS _ _ _)   ρ sk ko so = shape-keyed o ρ ko so
  shape-sub p o@doneS         ρ sk ko so = shape-keyed o ρ ko so
  shape-sub p o@(mapS _ _)    ρ sk ko so = shape-keyed o ρ ko so
  shape-sub p o@(scanS _ _ _) ρ sk ko so = shape-keyed o ρ ko so
  shape-sub p o@(cutS _ _ _)  ρ sk ko so = shape-keyed o ρ ko so
  shape-sub p o@(lnS _ _)     ρ sk ko so = shape-keyed o ρ ko so
  shape-sub p o@(takeS _ _ _ _) ρ sk ko so = shape-keyed o ρ ko so
  shape-sub p o@(flatS _ _ _ _ _ _ _) ρ sk ko so = shape-keyed o ρ ko so
  shape-sub p o@(connS _ _ _) ρ sk ko so = shape-keyed o ρ ko so
  shape-sub p o@(joinS _ _ _ _) ρ sk ko so = shape-keyed o ρ ko so

-- The environment a hole's connects give it is in order.
envAt-sorted : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) → Held (plug c s) → Sorted (envAt c)
envAt-sorted top                               s fs = tt
envAt-sorted (inMap f c)                       s fs = envAt-sorted c (mapS f s) fs
envAt-sorted (inScan f z c)                    s fs = envAt-sorted c (scanS f z s) fs
envAt-sorted (inCut l a c)                     s fs = envAt-sorted c (cutS l a s) fs
envAt-sorted (inLn b c)                        s fs = envAt-sorted c (lnS b s) fs
envAt-sorted (inTake i p w c)                  s fs = envAt-sorted c (takeS i p w s) fs
envAt-sorted (inOuter op f d n q ls c)         s fs = envAt-sorted c (flatS op f d n q s ls) fs
envAt-sorted (inLanes op f d n q o pre post c) s fs = envAt-sorted c (flatS op f d n q o (pre ʳ++ s ∷ post)) fs
envAt-sorted (inSrc k b c)                     s fs = envAt-sorted c (connS k s b) fs
envAt-sorted (inBody k o c)                    s fs =
  sorted-cons (src-sorted k o (envAt c) (ConnAt.ends (proj₁ ky)) (src-shape k o s (envAt c) (proj₁ ky) (proj₁ (proj₂ ky)) so)) so
  where so = envAt-sorted c (connS k o s) fs
        ky = keyed-at c (connS k o s) (proj₂ fs)

-- Each lane of a merge, those before it passed.
lanes-held : ∀ {R Γ A C} (e : Ctx R Γ C) op (f : A → Obs Timeline Γ C) dn n qs (s : St Γ A) (pre post : List (St Γ C))
           → Held (plug e (flatS op f dn n qs s (pre ʳ++ post))) → All (λ l → Shape (stateᴺ (gh l) (envAt e))) post
lanes-held e op f dn n qs s pre post fs =
  shape-keyedL post (envAt e) (keyedL-ʳ++ pre (proj₂ (proj₂ (keyed-at e (flatS op f dn n qs s (pre ʳ++ post)) (proj₂ fs)))))
    (envAt-sorted e (flatS op f dn n qs s (pre ʳ++ post)) fs)

-- A node, in the environment its connects give it.
shape-st : ∀ {R Γ A} (e : Ctx R Γ A) (s : St Γ A) → Held (plug e s) → Shape (stateᴺ (gh s) (envAt e))
shape-st e s fs = shape-keyed s (envAt e) (keyed-at e s (proj₂ fs)) (envAt-sorted e s fs)

-- A connect's source, likewise.
shape-src : ∀ {R Γ X B} (e : Ctx R Γ B) k (o : St Γ X) (b : St (X ∷ Γ) B) → Held (plug e (connS k o b))
           → Shape (srcState (srcG k o) (envAt e))
shape-src e k o b fs = src-shape k o b (envAt e) (proj₁ ky) (proj₁ (proj₂ ky)) (envAt-sorted e (connS k o b) fs)
  where ky = keyed-at e (connS k o b) (proj₂ fs)

-- What the frames above a hole keep, its environment in order: each
-- connect above keeps its source's shape.
above-sorted : ∀ {R Γ A} (c : Ctx R Γ A) f {h : Events∞ A} → Above c f h → Sorted (envAt c)
above-sorted top                               f ab = tt
above-sorted (inMap g c)                       f ab = above-sorted c true ab
above-sorted (inScan g z c)                    f ab = above-sorted c true ab
above-sorted (inCut l a c)                     f ab = above-sorted c true ab
above-sorted (inLn b c)                        f ab = above-sorted c b ab
above-sorted (inTake i q w c)                  f ab = above-sorted c true (proj₂ ab)
above-sorted (inOuter op g d n q ls c)         f ab = above-sorted c true (proj₂ ab)
above-sorted (inLanes op g d n q o pre post c) f ab = above-sorted c true (proj₂ ab)
above-sorted (inSrc k b c)                     f ab = above-sorted c true (proj₂ ab)
above-sorted (inBody k o c)                    f ((ca , ko , sh) , ab) =
  sorted-cons (src-sorted k o (envAt c) (ConnAt.ends ca) sh) (above-sorted c true ab)

-- A merge's live lanes, each keeping its own, in shape.
keyedL-shape : ∀ {Γ A} (ls : List (St Γ A)) (ρ : NEnv Γ) → KeyedL ls ρ → Sorted ρ → All Shape (states (lanesL ls) ρ)
keyedL-shape ls ρ kl so = lanes-shape ρ ls (shape-keyedL ls ρ kl so)
