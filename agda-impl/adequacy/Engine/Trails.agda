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
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)
open import Tree using (Obs)
open import denotation.MonotonicList.Events using (Events; Timeline)
open import Data.Unit using (⊤; tt)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (lookup)

open import denotation.MonotonicList.Events using (Events∞; Pos; Tail; idle; ix; last; end; _∪_)
open import denotation.MonotonicList using (MonotonicList) renaming (cold to coldᴹ)
import denotation.MonotonicList as M′
open import denotation.Denote using (flatOp)
open import denotation.Unfold using (NEnv; Node; meaning; Source; live; ended; stateᴺ; cutᴺ; idleᶜ; restᶜ; connectᶜ; subscribe; states; outerᴺ; joined; fedᴺ; put)
open import operation.PureObservable using (module Machine)
open Machine using (St; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS; Ctx; top; inMap; inScan; inCut; inLn;
  inTake; inOuter; inLanes; inSrc; inBody; plug; cs; CS; _⊕_)
open import adequacy.Engine.Meaning using (vals; endOf; gh; envAt; srcG; srcRun; srcState; subOr; lane; outerG; poolG; deadL; lanesL; liveL; holeL; flagOf)
open import adequacy.Engine.Kept using (states-++; live-hole)
open import adequacy.Engine.Head using (Frag)
open import adequacy.Placed.Order using (Alien; Atop; Past; Clear; every-lookup; sorted-headed; sorted-lookup; ordered-rejoin; steady-rejoin; Alienᴱ; Disjoint; Ordered; Owned; Sorted; Steady; Every; Every∞; EveryT; Headed; every-mono; everyT-mono; prefix-++; every-tail; everyT-burstOn; everyT-idle; everyT-∪; every∞-mono; headed-snoc; ordered-map; ordered-scan; steady-map; steady-scan)
open import adequacy.Placed using (ordered-sub; steady-sub)
open import adequacy.Placed.Keys using (module Merge; Values; owned-trans; values-mono; every-beside; every-map; every-scan)
open import adequacy.Placed.Trail using (Parted; Spread; trail-map; Trail; TrailE; Trailing; trail; trailᶠ; trail-idle; trail-scan; trail-rejoin; sortedT-idle; flatT-idle)
open import adequacy.Placed.Burst using (module Bursting; Fresh; FreshRun; ordered-tail; steady-tail; trail-tail)
open import adequacy.Placed.Walk using (module Walk)
open import adequacy.Placed.Rising using (Rise; module Reach; headed-sub; headedRules; ordered-take; steady-take)
open import adequacy.Placed.FlatAfter using (module FlatAfter; trail-take)
open import adequacy.Placed.FlatOrder using (module FlatOrder)
open import adequacy.Placed.Calm using (calm-steady; calm-trail)
open import operation.AbstractObservable using (free; cpAt; cutAt; overAt)
open Events∞

------------------------------------------------------------------------
-- Shapes

-- A run in order and steady, it and what it leaves running headed, the
-- latter trailing it.
Shape′ : ∀ {A} → Events A → Tail → Set
Shape′ x c = ((Ordered x × Steady x) × Every Headed x × EveryT Headed c) × Trail x c

Shape : ∀ {A} → Events∞ A → Set
Shape σ = Shape′ (force σ) (cut σ)

-- Nothing running.
shape-idle : ∀ {Γ A} (ρ : NEnv Γ) → Shape {A} (stateᴺ idleᶜ ρ)
shape-idle ρ = ((record { ordered = tt } , record { steady = tt }) , record { every = tt } , everyT-idle) , trail-idle _ tt

postulate
  -- A SOURCE SUBSCRIBED AT ITS BODY'S MARK is subscribed under a head,
  -- where no source of its environment has been.
  sub-headed : ∀ {R Γ X B} (e : Ctx R Γ B) cl sl sa p as ow r en (o : St Γ X) (b : St (X ∷ Γ) B)
             → Frag (plug e (connS (cs cl sl sa (just p) as ow r en) o b)) → Headed (p ⊕ (ix 1 ∷ []))
  sub-alien  : ∀ {R Γ X B} (e : Ctx R Γ B) cl sl sa p as ow r en (o : St Γ X) (b : St (X ∷ Γ) B)
             → Frag (plug e (connS (cs cl sl sa (just p) as ow r en) o b)) → Alienᴱ (p ⊕ (ix 1 ∷ [])) (envAt e)
  -- A SUBSCRIPTION'S CUTS TRAIL ITS RUN, finite or not: a limit over
  -- `adequacy.Placed.trailing-subᶠ` once a truncation's cut agrees as its
  -- run does (`adequacy.Finite.trunc-agree`).
  trailing-sub : ∀ {Γ A} (o : Obs Timeline Γ A) p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
               → Trailing (stateᴺ (subscribe o p) ρ)
  -- A SUBSCRIPTION LEAVES RUNNING ONLY WHAT IS HEADED, finite or not.
  headed-sub-cut : ∀ {Γ A} (o : Obs Timeline Γ A) p (ρ : NEnv Γ) → Headed p → Sorted ρ → EveryT Headed (cutᴺ (subscribe o p) ρ)
  -- AN ENDED SOURCE ended under a head.
  ended-headed : ∀ {R Γ X B} (e : Ctx R Γ B) sl sa as ow r en (o : St Γ X) (b : St (X ∷ Γ) B)
               → Frag (plug e (connS (cs true sl sa nothing as ow r en) o b)) → Headed en
  -- A TAPE MID-PLAY, an of part-way through.
  shape-cold : ∀ {R Γ A} (e : Ctx R Γ A) b l → Frag (plug e (coldS b l)) → ∀ (ρ : NEnv Γ) → Shape (stateᴺ (gh (coldS b l)) ρ)
  shape-of   : ∀ {R Γ A} (e : Ctx R Γ A) i p xs → Frag (plug e (ofS i p xs)) → ∀ (ρ : NEnv Γ) → Shape (stateᴺ (gh (ofS i p xs)) ρ)
  -- A TAKEWHILE OWING ITS COMPLETION owes it under a head, ahead of all
  -- its source leaves running.
  ending-headed : ∀ {R Γ A} (e : Ctx R Γ A) i p k (s : St Γ A) → Frag (plug e (takeS i p (cpAt k) s)) → Headed (k ⊕ (last ∷ []))
  ending-trails : ∀ {R Γ A} (e : Ctx R Γ A) i p k (s : St Γ A) → Frag (plug e (takeS i p (cpAt k) s))
                → EveryT (TrailE (end {A} (k ⊕ (last ∷ [])))) (cutᴺ (gh s) (envAt e))
  -- A CONNECT'S SOURCE SUBSCRIBED one past a head.
  conn-mark : ∀ {R Γ X B} (e : Ctx R Γ B) k (o : St Γ X) (b : St (X ∷ Γ) B) → Frag (plug e (connS k o b))
            → Σ Pos (λ p → Headed p × CS.srcAt k ≡ p ++ [ ix 1 ])

-- A RUN READ THROUGH ITS TAIL: what it leaves running, in order, steady
-- and headed, trailing itself.
shape-rest : ∀ {Γ A B} (n : Node Γ A) (ρ : NEnv Γ) → Shape (stateᴺ n ρ) → Shape (stateᴺ (restᶜ {B = B} n) ρ)
shape-rest n ρ (_ , tr) with cutᴺ n ρ | trail tr | trailᶠ tr
shape-rest n ρ ((_ , _ , et) , _) | c | st , _ | ft =
  ((ordered-tail c st , steady-tail c ft) , every-tail c et , et) , trail-tail c st ft

-- A TAKEWHILE OWING ITS COMPLETION: its end, ahead of what its source
-- leaves running.
shape-ending : ∀ {R Γ A} (e : Ctx R Γ A) i p k (s : St Γ A) → Frag (plug e (takeS i p (cpAt k) s))
             → Shape (stateᴺ (gh s) (envAt e)) → Shape (stateᴺ (gh (takeS i p (cpAt k) s)) (envAt e))
shape-ending e i p k s fs ((_ , _ , et) , tr) =
  ((record { ordered = tt } , record { steady = tt }) , record { every = ending-headed e i p k s fs } , et) , tr′
  where tr′ : Trail (end (k ⊕ (last ∷ []))) (cutᴺ (gh s) (envAt e))
        trail  tr′ = proj₁ (trail tr) , ending-trails e i p k s fs , tt
        trailᶠ tr′ = trailᶠ tr

-- A TAKEWHILE: owing nothing, its source's run cut at the first value
-- failing; cut or over, its source's tail.
shape-take : ∀ {R Γ A} (e : Ctx R Γ A) i p w (s : St Γ A) → Frag (plug e (takeS i p w s))
           → Shape (stateᴺ (gh s) (envAt e)) → Shape (stateᴺ (gh (takeS i p w s)) (envAt e))
shape-take e i p free       s fs (((o , st) , ev , et) , tr) =
  ((ordered-take i p _ o , steady-take i p _ st) , Reach.every-take headedRules i p _ ev , et) , trail-take i p _ _ o st tr
shape-take e i p (cpAt k)   s fs sh = shape-ending e i p k s fs sh
shape-take e i p (cutAt k)  s fs sh = shape-rest (gh s) (envAt e) sh
shape-take e i p (overAt k) s fs sh = shape-rest (gh s) (envAt e) sh

-- A connect's mark, its body's run and its source's.
module _ {R Γ X B} (e : Ctx R Γ B) k (o : St Γ X) (b : St (X ∷ Γ) B) (fs : Frag (plug e (connS k o b))) where
  markOf : Pos
  markOf = proj₁ (conn-mark e k o b fs)

  bodyOf : Events∞ B
  bodyOf = stateᴺ (gh b) (envAt (inBody k o e))

  srcOf′ : Events∞ X
  srcOf′ = srcState (srcG k o) (envAt e)

postulate
  -- A CONNECT'S BODY KEYED UNDER ITS MARK, rising past its source's
  -- subscription, fresh where the source cues it.
  conn-kb : ∀ {R Γ X B} (e : Ctx R Γ B) k (o : St Γ X) (b : St (X ∷ Γ) B) (fs : Frag (plug e (connS k o b)))
          → Every∞ (Owned (markOf e k o b fs ++ [ ix 0 ])) (bodyOf e k o b fs)
  conn-kr : ∀ {R Γ X B} (e : Ctx R Γ B) k (o : St Γ X) (b : St (X ∷ Γ) B) (fs : Frag (plug e (connS k o b)))
          → Every∞ (Rise (markOf e k o b fs ++ [ ix 1 ])) (bodyOf e k o b fs)
  conn-fr : ∀ {R Γ X B} (e : Ctx R Γ B) k (o : St Γ X) (b : St (X ∷ Γ) B) (fs : Frag (plug e (connS k o b)))
          → FreshRun (markOf e k o b fs ++ [ ix 0 ]) (force (bodyOf e k o b fs))
  conn-cue : ∀ {R Γ X B} (e : Ctx R Γ B) k (o : St Γ X) (b : St (X ∷ Γ) B) (fs : Frag (plug e (connS k o b)))
           → Σ Pos (λ l → Owned (markOf e k o b fs ++ [ ix 0 ]) l × Bursting.Cue (markOf e k o b fs ++ [ ix 1 ]) l (force (srcOf′ e k o b fs))
                        × EveryT (Fresh (markOf e k o b fs ++ [ ix 0 ]) l) (cut (bodyOf e k o b fs)))
  -- A CONNECT'S SOURCE KEYED UNDER ITS OWN SUBSCRIPTION, apart from its
  -- body's.
  conn-ks : ∀ {R Γ X B} (e : Ctx R Γ B) k (o : St Γ X) (b : St (X ∷ Γ) B) (fs : Frag (plug e (connS k o b)))
          → Every∞ (Disjoint (markOf e k o b fs ++ [ ix 0 ])) (srcOf′ e k o b fs)
  conn-rs : ∀ {R Γ X B} (e : Ctx R Γ B) k (o : St Γ X) (b : St (X ∷ Γ) B) (fs : Frag (plug e (connS k o b)))
          → Every∞ (Owned (markOf e k o b fs ++ [ ix 1 ])) (srcOf′ e k o b fs)
  -- NO BODY STEP UNDER WHERE A SOURCE STEP SHOWS.
  conn-ub : ∀ {R Γ X B} (e : Ctx R Γ B) k (o : St Γ X) (b : St (X ∷ Γ) B) (fs : Frag (plug e (connS k o b)))
          → Walk.UB (markOf e k o b fs) (proj₁ (proj₂ (conn-mark e k o b fs))) (bodyOf e k o b fs) (srcOf′ e k o b fs)

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
conn-core : ∀ {R Γ X B} (e : Ctx R Γ B) k (o : St Γ X) (b : St (X ∷ Γ) B) (fs : Frag (plug e (connS k o b)))
     → Shape (srcState (srcG k o) (envAt e)) → Shape (stateᴺ (gh b) (envAt (inBody k o e)))
     → Shape (stateᴺ (connectᶜ (CS.srcAt k) (gh b) (srcG k o)) (envAt e))
conn-core e k o b fs shS shB =
  subst (λ r → Shape (stateᴺ (connectᶜ r (gh b) (srcG k o)) (envAt e))) (sym (proj₂ (proj₂ m)))
    (beside-shape (proj₁ m) (proj₁ (proj₂ m)) (gh b) (srcG k o) (envAt e) shS shB
      (conn-kb e k o b fs) (conn-kr e k o b fs) (conn-fr e k o b fs) (conn-cue e k o b fs) (conn-ks e k o b fs) (conn-rs e k o b fs) (conn-ub e k o b fs))
  where m = conn-mark e k o b fs

-- A CONNECT: its body beside its source, read through its tail once it
-- owes its completion or its source has gone.
shape-conn : ∀ {R Γ X B} (e : Ctx R Γ B) k (o : St Γ X) (b : St (X ∷ Γ) B) → Frag (plug e (connS k o b))
           → Shape (srcState (srcG k o) (envAt e)) → Shape (stateᴺ (gh b) (envAt (inBody k o e)))
           → Shape (stateᴺ (gh (connS k o b)) (envAt e))
shape-conn e k@(cs cl sl sa ba as (just q) r en) o b fs shS shB = shape-rest (connectᶜ r (gh b) (srcG k o)) (envAt e) (conn-core e k o b fs shS shB)
shape-conn e k@(cs cl false sa ba as nothing r en) o b fs shS shB = shape-rest (connectᶜ r (gh b) (srcG k o)) (envAt e) (conn-core e k o b fs shS shB)
shape-conn e k@(cs cl true sa ba as nothing r en) o b fs shS shB = conn-core e k o b fs shS shB

------------------------------------------------------------------------
-- A merge

module FlatShape (p : Pos) where
  open module O = FlatOrder p using (K; Ok; Under; Gen; Heldᴹ; Aside; Pool; Roots; []ᴿ; _∷ᴿ_; under-k; lane-ok)
  module KM = Merge K Ok (λ h kh → owned-trans p h (h ++ [ ix 0 ]) (proj₁ kh) (inj₁ (prefix-++ h [ ix 0 ])) , headed-snoc h (proj₂ kh)) lane-ok

  -- A lane in flight keyed under its root, beyond its shape.
  data LaneKeys {B} : List (Events∞ B) → List Pos → Set where
    []ᴷ  : LaneKeys [] []
    _∷ᴷ_ : ∀ {r l ls rs} → Every∞ (Under r) l × Ok r × Spread (force l) → LaneKeys ls rs → LaneKeys (l ∷ ls) (r ∷ rs)

  -- The outer keyed under the merge, beyond its shape, its values lanes.
  OuterKeys : ∀ {B} → Maybe (Events∞ (MonotonicList B)) → Set
  OuterKeys nothing  = ⊤
  OuterKeys (just e) = Spread (force e) × Every∞ K e × Values Gen (force e)

  -- A merge in flight: its lanes and its outer keyed, its lanes parted
  -- and aside from the outer, its queue lanes, its pool.
  FlatKeys : ∀ {B} → Maybe (Events∞ (MonotonicList B)) → List (Events∞ B) → List (MonotonicList B) → Tail → List Pos → Set
  FlatKeys o ls qs t rs = LaneKeys ls rs × Parted rs × All (Aside o) rs × All Gen qs × OuterKeys o × Pool o rs t

  roots-of : ∀ {B} {ls : List (Events∞ B)} {rs} → All Shape ls → LaneKeys ls rs → Roots ls rs
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

-- A merge's outer, as its lanes' generator reads it.
outerOf : ∀ {Γ A C} (f : A → Obs Timeline Γ C) dn (s : St Γ A) (ρ : NEnv Γ) → Maybe (Events∞ (MonotonicList C))
outerOf f dn s ρ = outerᴺ (lane f) (outerG dn (gh s)) ρ

postulate
  -- A MERGE IN FLIGHT IS KEYED UNDER ITS MARK.
  flat-keys : ∀ {R Γ A C} (e : Ctx R Γ C) op (f : A → Obs Timeline Γ C) dn n qs (s : St Γ A) (ls : List (St Γ C))
            → Frag (plug e (flatS op f dn n qs s ls))
            → Σ Pos (λ p → Σ (List Pos) (FlatShape.FlatKeys p (outerOf f dn s (envAt e)) (states (lanesL ls) (envAt e))
                (L.map (λ a → coldᴹ λ q → stateᴺ (lane f a q) (envAt e)) qs) (cutᴺ (poolG dn (gh s) (deadL ls)) (envAt e))))

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
held-of : ∀ {Γ A C} p (f : A → Obs Timeline Γ C) dn (s : St Γ A) (ρ : NEnv Γ) → Shape (stateᴺ (gh s) ρ)
        → FlatShape.OuterKeys p (outerOf f dn s ρ) → FlatOrder.Heldᴹ p (outerOf f dn s ρ)
held-of p f true  s ρ sh ok = tt
held-of p f false s ρ (((os , ss) , _) , tr) (sp , (kx , kc) , gn) =
  FlatOrder.outer (ordered-map F _ os) (steady-map F _ ss) (trail-map F _ _ tr) sp kx kc gn
  where F = λ a → coldᴹ λ q → stateᴺ (lane f a q) ρ

-- A MERGE: its outer's run and its lanes', keyed under its mark.
shape-flat : ∀ {R Γ A C} (e : Ctx R Γ C) op (f : A → Obs Timeline Γ C) dn n qs (s : St Γ A) (ls : List (St Γ C))
           → Frag (plug e (flatS op f dn n qs s ls))
           → Shape (stateᴺ (gh s) (envAt e)) → All (λ l → Shape (stateᴺ (gh l) (envAt e))) ls
           → Shape (stateᴺ (gh (flatS op f dn n qs s ls)) (envAt e))
shape-flat e op f dn n qs s ls fs sh shs with flat-keys e op f dn n qs s ls fs
... | p , rs , lk , pt , asd , gq , ok , pl =
  FlatShape.flat-shape p (flatOp op) _ _ _ _ (FlatShape.roots-of p (lanes-shape (envAt e) ls shs) lk) pt asd gq
    (held-of p f dn s (envAt e) sh ok) pl

------------------------------------------------------------------------
-- A joiner

-- Each step fed a joiner and not yet shown, headed, at or before the
-- next and steady past it.
Steps : ∀ {A} → Pos → Maybe A → Events A → Set
Steps q (just _) x = Past q x
Steps q nothing  x = Clear q x

Fed : ∀ {A} → List (Pos × Maybe A) → Events A → Set
Fed []             x = ⊤
Fed ((q , a) ∷ xs) x = (Headed q × Atop q (fedᴺ xs x) × Steps q a (fedᴺ xs x)) × Fed xs x

-- Its end told under a head; else joined under a head where its source
-- has not been.
Joins : ∀ {Γ A} → A ∈ Γ → Pos → Maybe Pos → NEnv Γ → Set
Joins i p (just c) ρ = Headed c
Joins i p nothing  ρ = Headed p × Alien p (lookup ρ i)

postulate
  -- A JOINER'S FEED is in order ahead of its rejoined source, and it
  -- joined under a head where its source has not been.
  join-fed : ∀ {R Γ A} (e : Ctx R Γ A) j y ib → Frag (plug e (joinS j true y ib))
           → Joins y j (endOf ib) (envAt e) × Fed (vals ib) (joined y j (endOf ib) (envAt e))

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
shape-join : ∀ {R Γ A} (e : Ctx R Γ A) j g y ib → Frag (plug e (joinS j g y ib)) → Sorted (envAt e)
           → Shape (stateᴺ (gh (joinS j g y ib)) (envAt e))
shape-join e j false y ib fs so = shape-idle (envAt e)
shape-join e j true  y ib fs so =
  fed-shape (vals ib) _ (proj₂ (join-fed e j y ib fs)) (joined-shape y j (endOf ib) (envAt e) so (proj₁ (join-fed e j y ib fs)))

------------------------------------------------------------------------
-- The walk

sorted-cons : ∀ {Γ X} {e : Events X} {ρ : NEnv Γ} → (Ordered e × Steady e) × Every Headed e → Sorted ρ → Sorted (e ∷ᴬ ρ)
sorted-cons (os , ev) so = os , ev , so

-- Read in an environment in order.
private module Go where
 mutual
  shape-st : ∀ {R Γ A} (e : Ctx R Γ A) (s : St Γ A) → Frag (plug e s) → Sorted (envAt e) → Shape (stateᴺ (gh s) (envAt e))
  shape-st e (pend o)        fs so = shape-idle (envAt e)
  shape-st e (coldS b l)     fs so = shape-cold e b l fs (envAt e)
  shape-st e (ofS i p xs)    fs so = shape-of e i p xs fs (envAt e)
  shape-st e doneS           fs so = shape-idle (envAt e)
  shape-st e (mapS f s)      fs so with shape-st (inMap f e) s fs so
  ... | ((o , st) , ev , et) , tr = ((ordered-map f _ o , steady-map f _ st) , every-map f _ ev , et) , trail-map f _ _ tr
  shape-st e (scanS f z s)   fs so with shape-st (inScan f z e) s fs so
  ... | ((o , st) , ev , et) , tr = ((ordered-scan f z _ o , steady-scan f z _ st) , every-scan f z _ ev , et) , trail-scan f z _ _ tr
  shape-st e (cutS true a s)  fs so = shape-st (inCut true a e) s fs so
  shape-st e (cutS false a s) fs so = shape-rest (gh s) (envAt e) (shape-st (inCut false a e) s fs so)
  shape-st e (lnS b s)       fs so = shape-st (inLn b e) s fs so
  shape-st e (takeS i p w s) fs so = shape-take e i p w s fs (shape-st (inTake i p w e) s fs so)
  shape-st e (flatS op f dn n qs s ls) fs so =
    shape-flat e op f dn n qs s ls fs (shape-st (inOuter op f dn n qs ls e) s fs so) (shape-lanes e op f dn n qs s [] ls fs so)
  shape-st e (connS k o b)   fs so =
    shape-conn e k o b fs (shape-src e k o b fs so) (shape-st (inBody k o e) b fs (sorted-cons (src-sorted e k o b fs (shape-src e k o b fs so)) so))
  shape-st e (joinS j g y ib) fs so = shape-join e j g y ib fs so

  -- Each lane of a merge, those before it passed.
  shape-lanes : ∀ {R Γ A C} (e : Ctx R Γ C) op (f : A → _) dn n qs (s : St Γ A) (pre post : List (St Γ C))
              → Frag (plug e (flatS op f dn n qs s (pre ʳ++ post))) → Sorted (envAt e) → All (λ l → Shape (stateᴺ (gh l) (envAt e))) post
  shape-lanes e op f dn n qs s pre []         fs so = []ᴬ
  shape-lanes e op f dn n qs s pre (l ∷ post) fs so =
    shape-st (inLanes op f dn n qs s pre post e) l fs so ∷ᴬ shape-lanes e op f dn n qs s (l ∷ pre) post fs so

  -- A connect's source, subscribed at its body's mark, running, or ended.
  shape-src : ∀ {R Γ X B} (e : Ctx R Γ B) k (o : St Γ X) (b : St (X ∷ Γ) B) → Frag (plug e (connS k o b)) → Sorted (envAt e)
            → Shape (srcState (srcG k o) (envAt e))
  shape-src e (cs cl sl sa (just p) as ow r en) o b fs so = shape-sub e cl sl sa p as ow r en o b fs so
  shape-src e (cs false sl sa nothing as ow r en) o b fs so = shape-st (inSrc (cs false sl sa nothing as ow r en) b e) o fs so
  shape-src e (cs true sl sa nothing as ow r en) o b fs so =
    shape-rest (gh o) (envAt e) (shape-st (inSrc (cs true sl sa nothing as ow r en) b e) o fs so)

  -- A source subscribed at its body's mark: fresh, by the subscription's
  -- own order; else as it runs.
  shape-sub : ∀ {R Γ X B} (e : Ctx R Γ B) cl sl sa p as ow r en (o : St Γ X) (b : St (X ∷ Γ) B)
            → Frag (plug e (connS (cs cl sl sa (just p) as ow r en) o b)) → Sorted (envAt e)
            → Shape (stateᴺ (subOr (p ⊕ (ix 1 ∷ [])) o) (envAt e))
  shape-sub e cl sl sa p as ow r en (pend o) b fs so =
    ((ordered-sub o q (envAt e) hq so al , steady-sub o q (envAt e) hq so al) , headed-sub o q (envAt e) hq so , headed-sub-cut o q (envAt e) hq so)
    , trailing-sub o q (envAt e) hq so al
    where q  = p ⊕ (ix 1 ∷ [])
          hq = sub-headed e cl sl sa p as ow r en (pend o) b fs
          al = sub-alien e cl sl sa p as ow r en (pend o) b fs
  shape-sub e cl sl sa p as ow r en o@(coldS _ _)   b fs so = shape-st (inSrc (cs cl sl sa (just p) as ow r en) b e) o fs so
  shape-sub e cl sl sa p as ow r en o@(ofS _ _ _)   b fs so = shape-st (inSrc (cs cl sl sa (just p) as ow r en) b e) o fs so
  shape-sub e cl sl sa p as ow r en o@doneS         b fs so = shape-st (inSrc (cs cl sl sa (just p) as ow r en) b e) o fs so
  shape-sub e cl sl sa p as ow r en o@(mapS _ _)    b fs so = shape-st (inSrc (cs cl sl sa (just p) as ow r en) b e) o fs so
  shape-sub e cl sl sa p as ow r en o@(scanS _ _ _) b fs so = shape-st (inSrc (cs cl sl sa (just p) as ow r en) b e) o fs so
  shape-sub e cl sl sa p as ow r en o@(cutS _ _ _)  b fs so = shape-st (inSrc (cs cl sl sa (just p) as ow r en) b e) o fs so
  shape-sub e cl sl sa p as ow r en o@(lnS _ _)     b fs so = shape-st (inSrc (cs cl sl sa (just p) as ow r en) b e) o fs so
  shape-sub e cl sl sa p as ow r en o@(takeS _ _ _ _) b fs so = shape-st (inSrc (cs cl sl sa (just p) as ow r en) b e) o fs so
  shape-sub e cl sl sa p as ow r en o@(flatS _ _ _ _ _ _ _) b fs so = shape-st (inSrc (cs cl sl sa (just p) as ow r en) b e) o fs so
  shape-sub e cl sl sa p as ow r en o@(connS _ _ _) b fs so = shape-st (inSrc (cs cl sl sa (just p) as ow r en) b e) o fs so
  shape-sub e cl sl sa p as ow r en o@(joinS _ _ _ _) b fs so = shape-st (inSrc (cs cl sl sa (just p) as ow r en) b e) o fs so

  -- What a connect's source has run, in order and headed.
  src-sorted : ∀ {R Γ X B} (e : Ctx R Γ B) k (o : St Γ X) (b : St (X ∷ Γ) B) → Frag (plug e (connS k o b))
             → Shape (srcState (srcG k o) (envAt e))
             → (Ordered (srcRun (srcG k o) (envAt e)) × Steady (srcRun (srcG k o) (envAt e))) × Every Headed (srcRun (srcG k o) (envAt e))
  src-sorted e (cs cl sl sa (just p) as ow r en) o b fs (((o′ , st) , ev , _) , _) = (o′ , st) , ev
  src-sorted e (cs false sl sa nothing as ow r en) o b fs (((o′ , st) , ev , _) , _) = (o′ , st) , ev
  src-sorted e (cs true sl sa nothing as ow r en) o b fs sh =
    (record { ordered = tt } , record { steady = tt }) , record { every = ended-headed e sl sa as ow r en o b fs }

-- The environment a hole's connects give it is in order.
envAt-sorted : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) → Frag (plug c s) → Sorted (envAt c)
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
  sorted-cons (Go.src-sorted c k o s fs (Go.shape-src c k o s fs so)) so
  where so = envAt-sorted c (connS k o s) fs

-- A node, in the environment its connects give it.
shape-st : ∀ {R Γ A} (e : Ctx R Γ A) (s : St Γ A) → Frag (plug e s) → Shape (stateᴺ (gh s) (envAt e))
shape-st e s fs = Go.shape-st e s fs (envAt-sorted e s fs)

-- A connect's source, likewise.
shape-src : ∀ {R Γ X B} (e : Ctx R Γ B) k (o : St Γ X) (b : St (X ∷ Γ) B) → Frag (plug e (connS k o b))
          → Shape (srcState (srcG k o) (envAt e))
shape-src e k o b fs = Go.shape-src e k o b fs (envAt-sorted e (connS k o b) fs)
