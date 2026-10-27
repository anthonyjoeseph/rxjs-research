{-# OPTIONS --guardedness #-}

-- WHAT A STEP OWES OF ITS FLIGHT beyond what the whole tree's shape
-- gives (`adequacy.Engine.Above.Flight`): a configuration still rising or
-- subscribing carries its hole's run and every frame above's share of it.
-- A rise through a frame of one child passes the run up as the frame
-- reads it; a merge passing its lane's value, a connect its body's, an
-- outer admitting or ending, and a subscribe beginning are the leaves.
--
-- Every part of a run's shape reads a run's tail only through what it
-- forces and leaves running (`shape-out`), so a frame's run, unfolded one
-- event, is in shape as the frame's node's run is.
module adequacy.Engine.Flown where

open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _++_; _ʳ++_; [_]; reverse; length)
open import Data.List.Properties using (ʳ++-defn; reverse-involutive)
import Data.List as L
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_; map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties using (++⁻ʳ) renaming (++⁺ to All++⁺)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (zero; suc; pred; _≡ᵇ_; _<ᵇ_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import Tree using (Obs; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.MonotonicList.Events using (Events; Events∞; Pos; Timeline; out; skip; end; hush; idle; ix; _∪_)
import denotation.MonotonicList as M′
open import denotation.MonotonicList using (MonotonicList; Agreeᵀ; Agree; stop; out⁼; agree-refl; agreeᵀ-refl; agreeᵀ-trans)
open import denotation.NonExpansive using (_,ˢ_; ∪-ne; Lanes; module Agreeˢ)
open import denotation.Unfold using (NEnv; Node; Source; live; meaning; connectᶜ; restᶜ; stateᴺ; cutᴺ; states; outerᴺ; outer∞; subscribe)
open import denotation.Denote using (flatOp)
open import adequacy.Engine.Meaning using (_≋_; ≋-by; ≋-out; envAt; gh; srcG; srcRun; srcState; risen; lanesFrame; lane; lanesL; outerG; outerT;
  poolRuns; laneRuns; laneᴹ; flagOf; tailsOn; holeT; poolT; deadL; deadOne; lanes-refl; outerFrame; outerOf; poolG)
open import adequacy.Engine.Union using (∪-idleᵀ; ∪-assocᵀ; ∪-commᵀ)
open import adequacy.Engine.Keys using (Here; Shape; Shape′; module ConnAt; LaneKeys; []ᴷ; _∷ᴷ_; FlatKeys; Keyed; KeyedL)
open import adequacy.Engine.Trails using (shape-idle; body-≋; shape-≋; beside-go; module FlatShape; gen-queue; gen-sub; held-of; above-sorted; keyedL-shape)
open import adequacy.Engine.Beside using (burst-hushed)
open import adequacy.Engine.Race using (NotBefore; First; After; go-rise; go-outer; cuts-swap)
open import adequacy.Engine.Ahead using (shown; Sides) renaming (shows to showsᶜ)
open import adequacy.Engine.Above using (Above; Flight; above-≋; take-true; take-incl; toʳ; lanes-L; lanes-P; rests-++; dead-hole; lanes-runs; pool-runs; keyedL-ʳ++)
open import adequacy.Engine.Head using (Frag; Lane; len0) renaming (Lanes to Lanesᴴ)
open import adequacy.Engine.Admit using (states-length; begun-runs; begun-pool; Begins; keptLanes; running; outer-begins; outer-begins-pass;
  kill-lanes; kill-pool)
open import adequacy.Engine.Drop using (Dropsˢ; Pass; Links; pass-of; lane-admits)
open import adequacy.Engine.Passed using (above-drops)
open import adequacy.Engine.Pick using (Order; module Order; lanes-ʳsplit)
open import adequacy.Engine.Head.Within using (frag-flat; frag-parts)
open import adequacy.Placed.Order using (Ordered; Steady; Every; EveryT; Every∞; Headed; Atop; Past; Disjoint; ordered; steady; every; every∞-mono; everyT-mono;
  ordered-map; ordered-scan; steady-map; steady-scan)
open import adequacy.Placed.Keys using (every-map; every-scan; everyT-≈; values)
open import adequacy.Placed.Trail using (Trail; trail; trailᶠ; trail-map; trail-scan; trail-≈; SortedT; sortedT-idle; sortedT-∪;
  sortedT-≈; flatT-≈; parted-pick; all-pick; all-zip; Spread; spread)
open import adequacy.Placed.Rising using (module Reach; headedRules; ordered-take; steady-take; Beyond)
open import adequacy.Placed.FlatAfter using (trail-take)
open import adequacy.Placed.FlatOrder using (module FlatOrder)
open import operation.PureObservable using (module Machine; module Driver; play; ending; over)
open Machine using (St; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS; Ctx; top; inMap; inScan; inCut;
  inLn; inTake; inOuter; inLanes; inSrc; inBody; Conf; ⟨_,_,_,_⟩; subscribing; absorbed; rising; nx; cp; free; cpAt; cutAt; overAt;
  CS; cs; closed; attAt; attached; start; plug; rise; begin; admit; dequeue; settle; ended; alive; killAll; _⊕_)
open Events∞

------------------------------------------------------------------------
-- A run's shape, read one event in

-- The same event first, then tails forcing and leaving running alike.
shape-out : ∀ {A} p (a : A) {r r′ : Events∞ A} {c} → force r ≡ force r′ → cut r ≡ cut r′ → Shape′ (out p a r) c → Shape′ (out p a r′) c
shape-out p a {r} {r′} ef ec (((o , st) , ev , et) , tr) =
  ((record { ordered = subst (λ x → Atop p x × Ordered x) ef (ordered o) }
   , record { steady = subst (λ x → Past p x × Steady x) ef (steady st) })
   , record { every = proj₁ (every ev) , subst₂ (λ x t → Every Headed x × EveryT Headed t) ef ec (proj₂ (every ev)) } , et) , tr′
  where
    tr′ : Trail (out p a r′) _
    trail  tr′ = proj₁ (trail tr) , proj₁ (proj₂ (trail tr)) , subst₂ (λ x t → Trail x t × EveryT (Disjoint p) t) ef ec (proj₂ (proj₂ (trail tr)))
    trailᶠ tr′ = trailᶠ tr

-- A connect's run: its body's beside its source's, and what both leave
-- running.
-- A value risen out of runs alike.
risen-≋ : ∀ {Γ A} {n n′ : Node Γ A} {ρ : NEnv Γ} a p → stateᴺ n ρ ≋ stateᴺ n′ ρ → risen n ρ (nx a) p ≋ risen n′ ρ (nx a) p
risen-≋ a p e zero    = Agreeˢ.cutˢ (e zero) ,ˢ stop
risen-≋ a p e (suc m) = Agreeˢ.cutˢ (e (suc m)) ,ˢ out⁼ (Agreeˢ.cutˢ (e m)) (Agreeˢ.nowˢ (e m))

-- An end risen out of what runs alike leave.
risen-end-≋ : ∀ {Γ A B} {n n′ : Node Γ A} {ρ : NEnv Γ} p → stateᴺ n ρ ≋ stateᴺ n′ ρ → risen (restᶜ {B = B} n) ρ cp p ≋ risen (restᶜ n′) ρ cp p
risen-end-≋ p e m = Agreeˢ.cutˢ (e m) ,ˢ agree-refl m _

conn-run : ∀ {Γ X B} r (n : Node (X ∷ Γ) B) (σ : Source Γ X) (ρ : NEnv Γ)
         → meaning (connectᶜ r n σ) ρ ≡ M′.beside r (stateᴺ n (srcRun σ ρ ∷ᴬ ρ)) (srcState σ ρ)
         × cutᴺ (connectᶜ r n σ) ρ ≡ M′.burstOn r (srcState σ ρ) ∪ cutᴺ n (srcRun σ ρ ∷ᴬ ρ)
conn-run r n (live s)    ρ = refl , refl
conn-run r n (Source.ended c t) ρ = refl , refl

-- The body's value first, the connect's run behind it.
body-out : ∀ {X B} r (σ : Events∞ X) q {y : Events B} {p b β} → y ≡ out p b β
         → Σ (Events∞ B) λ t → M′.body r σ q y ≡ out p b t × force t ≡ M′.ahead r β σ q (M′.before q (force β)) × cut t ≡ M′.burstOn r σ ∪ cut β
body-out r σ q refl = _ , refl , refl , refl

-- What the flatMap leaves running is what it left: the lane's tail is
-- its rise's.
lanes-cut : ∀ {Γ A B} op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) pre post (s : St Γ B) (ρ : NEnv Γ) b p → flagOf s ≡ true
          → cut (lanesFrame op (lane f) d q (gh o) pre post true ρ (risen (gh s) ρ (nx b) p)) ≡ cutᴺ (gh (flatS op f d n q o (pre ++ s ∷ post))) ρ
lanes-cut op f d n q o pre post s ρ b p fl =
  trans (cong (λ z → M′.cutᴼ O ∪ z ∪ T) (cuts-swap Ls (risen (gh s) ρ (nx b) p) (stateᴺ (gh s) ρ) Rs refl))
    (cong₂ (M′.whole O) (sym (lanes-L pre s post ρ fl)) (lanes-P d o pre s post ρ fl))
  where
    O  = outerᴺ (lane f) (outerG d (gh o)) ρ
    Ls = states (lanesL post) ρ
    Rs = states (lanesL pre) ρ
    T  = outerT d (gh o) ρ (poolRuns pre post true ρ (stateᴺ (gh s) ρ))

-- A lane's value, first among its flatMap's parts, is the flatMap's: the
-- merge's run shows it, the flatMap's run behind it.
lanes-out : ∀ {Γ A B} op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) pre post (s : St Γ B) (ρ : NEnv Γ) b p → flagOf s ≡ true
          → First p (outerᴺ (lane f) (outerG d (gh o)) ρ) (states (lanesL post) ρ) (states (lanesL pre) ρ)
              (outerT d (gh o) ρ (poolRuns pre post true ρ (stateᴺ (gh s) ρ)))
          → Σ (Events∞ B) λ t → force (lanesFrame op (lane f) d q (gh o) pre post true ρ (risen (gh s) ρ (nx b) p)) ≡ out p b t
              × force t ≡ force (stateᴺ (gh (flatS op f d n q o (pre ++ s ∷ post))) ρ)
              × cut t ≡ cut (stateᴺ (gh (flatS op f d n q o (pre ++ s ∷ post))) ρ)
lanes-out op f d n q o pre post s ρ b p fl fi =
  _ , go-rise (flatOp op) O Ls (risen (gh s) ρ (nx b) p) Rs Q T refl fi
    , cong₂ (λ ls t → M′.go (flatOp op) O ls Q t) (sym L) P , cong₂ (M′.whole O) (sym L) P
  where
    O  = outerᴺ (lane f) (outerG d (gh o)) ρ
    Ls = states (lanesL post) ρ
    Rs = states (lanesL pre) ρ
    Q  = L.map (laneᴹ (lane f) ρ) q
    T  = outerT d (gh o) ρ (poolRuns pre post true ρ (stateᴺ (gh s) ρ))
    L  = lanes-L pre s post ρ fl
    P  = lanes-P d o pre s post ρ fl

lanes-rise : ∀ {Γ A B} op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) pre post (s : St Γ B) (ρ : NEnv Γ) b p → flagOf s ≡ true
           → First p (outerᴺ (lane f) (outerG d (gh o)) ρ) (states (lanesL post) ρ) (states (lanesL pre) ρ)
               (outerT d (gh o) ρ (poolRuns pre post true ρ (stateᴺ (gh s) ρ)))
           → lanesFrame op (lane f) d q (gh o) pre post true ρ (risen (gh s) ρ (nx b) p) ≋ risen (gh (flatS op f d n q o (pre ++ s ∷ post))) ρ (nx b) p
lanes-rise op f d n q o pre post s ρ b p fl fi =
  ≋-out (proj₁ (proj₂ lo)) refl (proj₁ (proj₂ (proj₂ lo))) (proj₂ (proj₂ (proj₂ lo))) (lanes-cut op f d n q o pre post s ρ b p fl)
  where lo = lanes-out op f d n q o pre post s ρ b p fl fi

-- A body's value its source is no earlier than shows first, the
-- connect's run behind it.
side-out : ∀ {X B} r (σ : Events∞ X) (x : Events X) {h β : Events∞ B} p b → force h ≡ out p b β
         → (x ≡ hush → M′.burstOn r σ ≡ idle) → NotBefore p (shown x)
         → Σ (Events∞ B) λ t → M′.side r h σ x ≡ out p b t × force t ≡ M′.side r β σ x × cut t ≡ M′.burstOn r σ ∪ cut β
side-out r σ hush        {β = β} p b e bi nb = β , e , refl , cong (_∪ cut β) (sym (bi refl))
side-out r σ (out q a l) p b e bi nb rewrite e | nb = body-out r σ _ e
side-out r σ (skip q l)  p b e bi nb rewrite e | nb = body-out r σ _ e
side-out r σ (end q)     p b e bi nb rewrite e | nb = body-out r σ _ e

-- A body's end its source is no earlier than is the connect's.
side-end : ∀ {X B} r (σ : Events∞ X) (x : Events X) {h : Events∞ B} p → force h ≡ end p → NotBefore p (shown x) → M′.side r h σ x ≡ end p
side-end r σ hush        p e nb = e
side-end r σ (out q a l) p e nb rewrite e | nb = cong (M′.body r σ _) e
side-end r σ (skip q l)  p e nb rewrite e | nb = cong (M′.body r σ _) e
side-end r σ (end q)     p e nb rewrite e | nb = cong (M′.body r σ _) e

-- An end, whatever it would have carried.
shape-end : ∀ {A B} p {c} → Shape′ {A} (end p) c → Shape′ {B} (end p) c
shape-end p (((o , st) , ev , et) , tr) = ((record { ordered = tt } , record { steady = tt }) , record { every = every ev } , et) , tr′
  where
    tr′ : Trail (end p) _
    trail  tr′ = proj₁ (trail tr) , proj₁ (proj₂ (trail tr)) , tt
    trailᶠ tr′ = trailᶠ tr

shape-mapᴱ : ∀ {A B} (f : A → B) (x : Events A) c → Shape′ x c → Shape′ (M′.mapᴱ f x) c
shape-mapᴱ f x c (((o , st) , ev , et) , tr) = ((ordered-map f x o , steady-map f x st) , every-map f x ev , et) , trail-map f x c tr

shape-scanᴱ : ∀ {A B} (f : B → A → B) z (x : Events A) c → Shape′ x c → Shape′ (M′.scanᴱ f z x) c
shape-scanᴱ f z x c (((o , st) , ev , et) , tr) = ((ordered-scan f z x o , steady-scan f z x st) , every-scan f z x ev , et) , trail-scan f z x c tr

shape-takeᴱ : ∀ {A} i (q : A → Bool) (x : Events A) c → Shape′ x c → Shape′ (M′.takeWhileᴱ i q x) c
shape-takeᴱ i q x c (((o , st) , ev , et) , tr) =
  ((ordered-take i q x o , steady-take i q x st) , Reach.every-take headedRules i q x ev , et) , trail-take i q x c o st tr

------------------------------------------------------------------------
-- A pool's tails

-- A run's shape, read through a tail alike at every depth.
shape-cut : ∀ {A} (x : Events A) c d → (∀ k → Agreeᵀ k c d) → Shape′ x c → Shape′ x d
shape-cut x c d at ((od , ev , et) , tr) = (od , ev , everyT-≈ c d at et) , trail-≈ x x c d (λ k → agree-refl k x) at tr

-- A tail joined behind a pool joins it at the pool's end.
tails-ended : ∀ {Γ B} n (ds : List (Node Γ B)) (ρ : NEnv Γ) t u → SortedT t → SortedT u → Agreeᵀ n (tailsOn ds ρ t ∪ u) (tailsOn ds ρ (u ∪ t))
tails-ended n []       ρ t u st su = ∪-commᵀ n t u st su
tails-ended n (x ∷ ds) ρ t u st su =
  agreeᵀ-trans (∪-assocᵀ n (cutᴺ x ρ) (tailsOn ds ρ t) u) (∪-ne (agreeᵀ-refl n (cutᴺ x ρ)) (tails-ended n ds ρ t u st su))

pool-ended : ∀ {Γ A B} n d (o : Node Γ A) (ds : List (Node Γ B)) (ρ : NEnv Γ) t u → SortedT t → SortedT u
           → Agreeᵀ n (outerT d o ρ (tailsOn ds ρ t) ∪ u) (outerT d o ρ (tailsOn ds ρ (u ∪ t)))
pool-ended n false o ds ρ t u st su = tails-ended n ds ρ t u st su
pool-ended n true  o ds ρ t u st su =
  agreeᵀ-trans (∪-assocᵀ n (cutᴺ o ρ) (tailsOn ds ρ t) u) (∪-ne (agreeᵀ-refl n (cutᴺ o ρ)) (tails-ended n ds ρ t u st su))

-- A pool of tails each in position order is.
hole-sorted : ∀ {B} b (h : Events∞ B) t → SortedT (cut h) → SortedT t → SortedT (holeT b h ∪ t)
hole-sorted true  h t sh st = st
hole-sorted false h t sh st = sortedT-∪ (cut h) t sh st

pool-sorted : ∀ {Γ B} (ls : List (St Γ B)) (ρ : NEnv Γ) → All (λ s → SortedT (cutᴺ (gh s) ρ)) ls → SortedT (poolT (deadL ls) ρ)
pool-sorted []       ρ []ᴬ        = sortedT-idle
pool-sorted (x ∷ ls) ρ (sx ∷ᴬ sl) =
  subst SortedT (sym (trans (rests-++ (deadOne x) (deadL ls) ρ) (dead-hole x ρ _)))
    (hole-sorted (flagOf x) (stateᴺ (gh x) ρ) _ sx (pool-sorted ls ρ sl))

-- A lane's context keeps the lanes before it nearest first.
all-at : ∀ {Γ B} {P : St Γ B → Set} pre {s post} → All P (pre ʳ++ s ∷ post) → P s × All P post
all-at pre a with ++⁻ʳ (reverse pre) (subst (All _) (ʳ++-defn pre) a)
... | x ∷ᴬ xs = x , xs

-- A flatMap of the fragment counts its live lanes.
frag-count : ∀ {Γ A B} op (f : A → Obs Timeline Γ B) d n (o : St Γ A) ls → Frag (flatS op f d n [] o ls) → n ≡ length (lanesL ls)
frag-count (mergeᶠ nothing)  f d n o ls (_ , _ , e , _) = e
frag-count (mergeᶠ (just _)) f d n o ls (_ , _ , e , _) = e
frag-count switchᶠ           f d n o ls (_ , _ , e , _) = e
frag-count exhaustᶠ          f d n o ls (_ , _ , e , _) = e

-- At most one counted, a run among its siblings: the run alone.
last-one : ∀ n → (pred n ≡ᵇ 0) ∧ true ≡ true → ∀ {X : Set} (as bs : List X) x → n ≡ length (as ++ x ∷ bs) → as ≡ [] × bs ≡ []
last-one zero          _  []          _        _ ()
last-one zero          _  (_ ∷ _)     _        _ ()
last-one (suc zero)    _  []          []       _ refl = refl , refl
last-one (suc zero)    _  []          (_ ∷ _)  _ ()
last-one (suc zero)    _  (_ ∷ [])    _        _ ()
last-one (suc zero)    _  (_ ∷ _ ∷ _) _        _ ()
last-one (suc (suc _)) () _           _        _ _

-- A lane ended stops counting and leaves its tail.
ended-flag : ∀ {Γ B} (s : St Γ B) → Lane s → flagOf (ended s) ≡ false
ended-flag (lnS true (cutS true a s))   l = refl
ended-flag (lnS false (cutS false a s)) l = refl

ended-cut : ∀ {Γ B} (s : St Γ B) (ρ : NEnv Γ) → Lane s → cutᴺ (gh (ended s)) ρ ≡ cutᴺ (gh s) ρ
ended-cut (lnS true (cutS true a s))   ρ l = refl
ended-cut (lnS false (cutS false a s)) ρ l = refl

-- A merge's last part ending, nothing queued, ends the merge.
lane-solo : ∀ {B} op (h : Events∞ B) t {Ls Rs : List (Events∞ B)} p → Ls ≡ [] → Rs ≡ [] → M′.lane op nothing Ls h Rs [] t (end p) ≡ end p
lane-solo op h t p refl refl = refl

-- A lane ended keeps its keys.
keyed-ended : ∀ {Γ B} (s : St Γ B) (ρ : NEnv Γ) → Lane s → Keyed s ρ → Keyed (ended s) ρ
keyed-ended (lnS true (cutS true a s))   ρ l k = k
keyed-ended (lnS false (cutS false a s)) ρ l k = k

postulate
  -- THE KEYS KEPT: a node whose children are unsubscribed keeps its own
  -- keys: a takeWhile its source cut, a merge its outer cut and its lanes
  -- killed, a connect both its parts; and a connect's body, unsubscribed,
  -- keeps its keys under its source unsubscribed.
  unsub-take-here : ∀ {Γ A} i q w (s : St Γ A) (ρ : NEnv Γ) → Keyed (takeS i q w s) ρ → Here (takeS i q w (proj₁ (Machine.cut s))) ρ
  unsub-flat-here : ∀ {Γ A B} op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) ls (ρ : NEnv Γ) → Keyed (flatS op f d n q o ls) ρ
                  → Here (flatS op f d 0 q (proj₁ (Machine.cut o)) (proj₁ (killAll ls))) ρ
  unsub-conn-here : ∀ {Γ X B} k (o : St Γ X) (b : St (X ∷ Γ) B) (ρ : NEnv Γ) → Keyed (connS k o b) ρ
                  → Here (connS k (proj₁ (Machine.unsub o)) (proj₁ (Machine.unsub b))) ρ
  unsub-body-keyed : ∀ {Γ X B} k (o : St Γ X) (b : St (X ∷ Γ) B) (ρ : NEnv Γ) → Keyed (connS k o b) ρ
                   → Keyed (proj₁ (Machine.unsub b)) (srcRun (srcG k (proj₁ (Machine.unsub o))) ρ ∷ᴬ ρ)

mutual
  -- A node unsubscribed keeps its keys.
  unsub-keyed : ∀ {Γ A} (s : St Γ A) (ρ : NEnv Γ) → Keyed s ρ → Keyed (proj₁ (Machine.unsub s)) ρ
  unsub-keyed (pend o)                       ρ k = k
  unsub-keyed (coldS true (play τ u i t fr)) ρ k = shape-idle ρ , tt
  unsub-keyed (coldS true (ending e))        ρ k = k
  unsub-keyed (coldS true over)              ρ k = k
  unsub-keyed (coldS false l)                ρ k = k
  unsub-keyed (ofS i p xs)                   ρ k = k
  unsub-keyed doneS                          ρ k = k
  unsub-keyed (mapS f s) ρ (_ , k) with Machine.unsub s | unsub-keyed s ρ k
  ... | s′ , u | k′ = tt , k′
  unsub-keyed (scanS f z s) ρ (_ , k) with Machine.unsub s | unsub-keyed s ρ k
  ... | s′ , u | k′ = tt , k′
  unsub-keyed (cutS l a s) ρ k = k
  unsub-keyed (lnS b s)    ρ k = k
  unsub-keyed (takeS i q w s) ρ k with Machine.cut s | unsub-take-here i q w s ρ k | cut-keyed s ρ (proj₂ k)
  ... | s′ , u | h | k′ = h , k′
  unsub-keyed (flatS op f d n q o ls) ρ k
    with Machine.cut o | killAll ls | unsub-flat-here op f d n q o ls ρ k | cut-keyed o ρ (proj₁ (proj₂ k)) | kill-keyed ls ρ (proj₂ (proj₂ k))
  ... | o′ , u | ls′ , v | h | ko | kl = h , ko , kl
  unsub-keyed (connS k o b) ρ x
    with Machine.unsub o | Machine.unsub b | unsub-conn-here k o b ρ x | unsub-keyed o ρ (proj₁ (proj₂ x)) | unsub-body-keyed k o b ρ x
  ... | o′ , u | b′ , v | h | ko | kb = h , ko , kb
  unsub-keyed (joinS j g y ib) ρ k = tt , tt

  -- A node cut keeps its keys.
  cut-keyed : ∀ {Γ A} (s : St Γ A) (ρ : NEnv Γ) → Keyed s ρ → Keyed (proj₁ (Machine.cut s)) ρ
  cut-keyed (cutS l attached s) ρ (_ , k) with Machine.unsub s | unsub-keyed s ρ k
  ... | s′ , u | k′ = tt , k′
  cut-keyed (cutS l (attAt p) s)    ρ k = k
  cut-keyed (pend o)                ρ k = k
  cut-keyed (coldS b l)             ρ k = k
  cut-keyed (ofS i p xs)            ρ k = k
  cut-keyed doneS                   ρ k = k
  cut-keyed (mapS f s)              ρ k = k
  cut-keyed (scanS f z s)           ρ k = k
  cut-keyed (lnS b s)               ρ k = k
  cut-keyed (takeS i q w s)         ρ k = k
  cut-keyed (flatS op f d n q o ls) ρ k = k
  cut-keyed (connS k o b)           ρ x = x
  cut-keyed (joinS j g y ib)        ρ k = k

  -- The lanes a switch kills keep their keys.
  kill-keyed : ∀ {Γ B} (ls : List (St Γ B)) (ρ : NEnv Γ) → KeyedL ls ρ → KeyedL (proj₁ (killAll ls)) ρ
  kill-keyed [] ρ _ = tt
  kill-keyed (lnS true s ∷ ls) ρ (k , kl) with Machine.cut s | cut-keyed s ρ (proj₂ k) | killAll ls | kill-keyed ls ρ kl
  ... | s′ , u | ks | ls′ , t | kl′ = (tt , ks) , kl′
  kill-keyed (lnS false s ∷ ls)            ρ (k , kl) = k , kill-keyed ls ρ kl
  kill-keyed (pend o ∷ ls)                 ρ (k , kl) = k , kill-keyed ls ρ kl
  kill-keyed (coldS b l ∷ ls)              ρ (k , kl) = k , kill-keyed ls ρ kl
  kill-keyed (ofS i p xs ∷ ls)             ρ (k , kl) = k , kill-keyed ls ρ kl
  kill-keyed (doneS ∷ ls)                  ρ (k , kl) = k , kill-keyed ls ρ kl
  kill-keyed (mapS f s ∷ ls)               ρ (k , kl) = k , kill-keyed ls ρ kl
  kill-keyed (scanS f z s ∷ ls)            ρ (k , kl) = k , kill-keyed ls ρ kl
  kill-keyed (cutS l a s ∷ ls)             ρ (k , kl) = k , kill-keyed ls ρ kl
  kill-keyed (takeS i q w s ∷ ls)          ρ (k , kl) = k , kill-keyed ls ρ kl
  kill-keyed (flatS op f d n q o ls′ ∷ ls) ρ (k , kl) = k , kill-keyed ls ρ kl
  kill-keyed (connS c o b ∷ ls)            ρ (k , kl) = k , kill-keyed ls ρ kl
  kill-keyed (joinS j g y ib ∷ ls)         ρ (k , kl) = k , kill-keyed ls ρ kl

kept-keyed : ∀ {Γ B} op (ls : List (St Γ B)) (ρ : NEnv Γ) → KeyedL ls ρ → KeyedL (keptLanes op ls) ρ
kept-keyed (mergeᶠ m) ls ρ k = k
kept-keyed switchᶠ    ls ρ k = kill-keyed ls ρ k
kept-keyed exhaustᶠ   ls ρ k = k

-- A run whose head is after a position lies beyond it.
after-beyond : ∀ {A} p (x : Events A) → After p (M′.head x) → Beyond p x
after-beyond p (out h _ _) a = a
after-beyond p (skip h _)  a = a
after-beyond p (end h)     a = a
after-beyond p hush        a = tt

-- A run past its first value, in shape as the run was.
shape-past : ∀ {A} p (a : A) (r : Events∞ A) → Shape′ (out p a r) (cut r) → Shape r
shape-past p a r (((o , st) , ev , et) , tr) = ((proj₂ (ordered o) , proj₂ (steady st)) , proj₂ (every ev)) , proj₁ (proj₂ (proj₂ (trail tr)))

-- The run after a value, else the default.
tailᴱ : ∀ {A} → Events A → Events∞ A → Events∞ A
tailᴱ (out _ _ r) d = r
tailᴱ (skip _ _)  d = d
tailᴱ (end _)     d = d
tailᴱ hush        d = d

------------------------------------------------------------------------
-- A merge under its mark `pk`, a queued lane begun

module _ (pk : Pos) where
  private module FO = FlatOrder pk

  -- A pool read through a tail alike at every depth.
  pool-≈ : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) rs t u → (∀ k → Agreeᵀ k t u) → FO.Pool o rs t → FO.Pool o rs u
  pool-≈ o rs t u at (st , ep , ew , ef) = sortedT-≈ t u at st , everyT-≈ t u at ep , everyT-≈ t u at ew , flatT-≈ t u at ef

  -- Lanes keyed under their roots.
  keys-of : ∀ {B} {ls : List (Events∞ B)} {rs} → FO.Roots ls rs → LaneKeys pk ls rs
  keys-of FO.[]ᴿ       = []ᴷ
  keys-of (st FO.∷ᴿ R) = ((FO.Lane.kx st , FO.Lane.kc st) , FO.Lane.ok st , FO.Lane.spr st) ∷ᴷ keys-of R

  -- A lane fitting where it is begun is in shape.
  fit-shape : ∀ {B} j (l : Events∞ B) → FO.Fit j l → Shape l
  fit-shape j l (od , _ , sd , tr , ku , _) = ((od , sd) , proj₁ ev , proj₂ ev) , tr
    where ev = every∞-mono (λ _ u → proj₁ (proj₂ u)) l ku

  -- A lane ending at `c`, one queued: the queued lane begun just past
  -- the end, ahead of the rest, fits there, the ended lane's tail joins
  -- the pool, and the merge stays keyed.
  flat-hand : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) Sp (h : Events∞ B) Sr {rs t} u c (m : MonotonicList B)
            → force h ≡ end c → (∀ k → Agreeᵀ k (t ∪ cut h) u) → All Shape (Sp ++ h ∷ Sr)
            → FlatKeys pk o (Sp ++ h ∷ Sr) t rs → FO.Heldᴹ o → FO.Gen m
            → Σ (List Pos) (FlatKeys pk o (M′.enter m (c ++ [ ix 1 ]) ∷ Sp ++ Sr) u) × Shape (M′.enter m (c ++ [ ix 1 ]))
  flat-hand o Sp h Sr {t = t} u c m fe ag shs (lk , pt , asd , ok , pl) hd gm with FO.roots-split Sp (FlatShape.roots-of pk shs lk)
  ... | FO.split {rbs} {r} {ras} rb st ra =
    ( c₁ ∷ rbs ++ ras
    , keys-of (FO.fresh c₁ (M′.enter m c₁) fit okc FO.∷ᴿ FO.roots-++ rb ra)
    , (mapᴬ (λ {r′} od → FO.hand-apart r c r′ uc (proj₁ od) (proj₂ od)) oks , proj₂ pp)
    , FO.hand-aside r c o (FO.Lane.ok st) uc ar hd ∷ᴬ proj₂ (all-pick rbs ras asd)
    , ok
    , pool-≈ o (c₁ ∷ rbs ++ ras) (t ∪ cut h) u ag (FO.pool-hand o rbs r ras t c h st′ oks ar hd pl) )
    , fit-shape c₁ (M′.enter m c₁) fit
    where
      c₁  = c ++ [ ix 1 ]
      st′ = subst (λ x → FO.Lane r x (cut h)) fe st
      uc  = every (FO.Lane.kx st′)
      okc = FO.hand-ok r c (ix 1) (FO.Lane.ok st) uc
      fit = gm c₁ okc
      pp  = parted-pick rbs r ras pt
      ar  = proj₁ (all-pick rbs ras asd)
      oks = all-zip (FO.roots-ok (FO.roots-++ rb ra)) (proj₁ pp)

  -- A merge's keys read off its outer's run and tail alone.
  keys-≡ : ∀ {B} {w w′ : Events∞ (MonotonicList B)} {ls t rs} → force w ≡ force w′ → cut w ≡ cut w′
         → FlatKeys pk (just w) ls t rs → FlatKeys pk (just w′) ls t rs
  keys-≡ ef ec (lk , pt , asd , (sp , kx , kc) , st , ep , wd) =
    lk , pt , mapᴬ (λ {r} x → subst (Every (FO.D r)) ef (proj₁ x) , subst (EveryT (FO.D r)) ec (proj₂ x)) asd
    , (subst Spread ef sp , subst (Every FO.K) ef kx , subst (EveryT FO.K) ec kc)
    , st , everyT-mono (λ k x → proj₁ x , subst₂ (λ y z → FO.FreeC y z k) ef ec (proj₂ x)) _ ep , wd

  -- A lane begun ahead of those kept, out of what the merge holds after
  -- its outer's value: the merge keyed with it.
  begun-keys : ∀ {Γ B} {w : Events∞ (MonotonicList B)} {q t d} (ls′ : List (St Γ B)) (ρ : NEnv Γ) H qs
             → Spread (force w) → Every∞ FO.K w → FO.Taken q w t (H ∷ states (lanesL ls′) ρ , qs , d)
             → (∀ k → Agreeᵀ k (t ∪ d) (poolT (deadL ls′) ρ))
             → Σ (List Pos) (FlatKeys pk (just w) (laneRuns (reverse (reverse ls′)) [] true ρ H) (poolRuns (reverse (reverse ls′)) [] true ρ H))
  begun-keys {w = w} {t = t} {d} ls′ ρ H qs sw kw (FO.taken {rs = rs} R pt asd _ _ pl _) ag =
    rs , subst₂ (λ ls u → FlatKeys pk (just w) ls u rs) (begun-runs ls′ ρ H) (begun-pool ls′ ρ H)
           (keys-of R , pt , asd , (sw , kw) , pool-≈ (just w) rs (t ∪ d) (poolT (deadL ls′) ρ) ag pl)

  -- As the flatMap admits: a merge or an idle exhaust begins the lane
  -- ahead of the rest; a switch begins it alone, its killed lanes' tails
  -- in the pool.
  admit-keys : ∀ {Γ B} op (ls : List (St Γ B)) (ρ : NEnv Γ) {w : Events∞ (MonotonicList B)} {q} H qs → Lanesᴴ ls
             → Spread (force w) → Every∞ FO.K w
             → FO.Taken q w (poolT (deadL ls) ρ) (H ∷ states (lanesL ls) ρ , qs , idle)
             → FO.Taken q w (poolT (deadL ls) ρ) ([ H ] , qs , M′.cuts (states (lanesL ls) ρ))
             → Σ (List Pos) (FlatKeys pk (just w) (laneRuns (reverse (reverse (keptLanes op ls))) [] true ρ H)
                                (poolRuns (reverse (reverse (keptLanes op ls))) [] true ρ H))
  admit-keys (mergeᶠ m) ls ρ H qs fl sw kw tn ts = begun-keys ls ρ H qs sw kw tn (λ k → ∪-idleᵀ k _)
  admit-keys exhaustᶠ   ls ρ H qs fl sw kw tn ts = begun-keys ls ρ H qs sw kw tn (λ k → ∪-idleᵀ k _)
  admit-keys switchᶠ    ls ρ {w} {q} H qs fl sw kw tn ts =
    begun-keys (proj₁ (killAll ls)) ρ H qs sw kw
      (subst (λ x → FO.Taken q w (poolT (deadL ls) ρ) (H ∷ x , qs , M′.cuts (states (lanesL ls) ρ))) (sym (cong (λ x → states x ρ) (kill-lanes ls fl))) ts)
      (kill-pool ls ρ fl)

------------------------------------------------------------------------
-- A frame of one child, the value passed up

map-flight : ∀ {R Γ A B} (c : Ctx R Γ B) (f : A → B) (s : St Γ A) e p → Flight ⟨ inMap f c , s , rising e , p ⟩
           → Flight ⟨ c , mapS f s , rising (Machine.mapEv f e) , p ⟩
map-flight c f s (nx a) p (sh , ab) =
  shape-out p (f a) refl refl (shape-mapᴱ f (out p a (stateᴺ (gh s) (envAt c))) (cutᴺ (gh s) (envAt c)) sh) , above-≋ c true (≋-out refl refl refl refl refl) ab
map-flight c f s cp     p (sh , ab) = shape-end p sh , above-≋ c true (≋-by refl refl) ab

scan-flight : ∀ {R Γ A B} (c : Ctx R Γ B) (f : B → A → B) z (s : St Γ A) a p → Flight ⟨ inScan f z c , s , rising (nx a) , p ⟩
            → Flight ⟨ c , scanS f (f z a) s , rising (nx (f z a)) , p ⟩
scan-flight c f z s a p (sh , ab) =
  shape-out p (f z a) refl refl (shape-scanᴱ f z (out p a (stateᴺ (gh s) (envAt c))) (cutᴺ (gh s) (envAt c)) sh) , above-≋ c true (≋-out refl refl refl refl refl) ab

scan-end-flight : ∀ {R Γ A B} (c : Ctx R Γ B) (f : B → A → B) z (s : St Γ A) p → Flight ⟨ inScan f z c , s , rising cp , p ⟩
                → Flight ⟨ c , scanS f z s , rising cp , p ⟩
scan-end-flight c f z s p (sh , ab) = shape-end p sh , above-≋ c true (≋-by refl refl) ab

-- A takeWhile passing a value it keeps; an inclusive one passing the
-- value it fails, under `ix 0`, owing its end.
take-flight : ∀ {R Γ A} (c : Ctx R Γ A) i (q : A → Bool) (s : St Γ A) a p → q a ≡ true → Flight ⟨ inTake i q free c , s , rising (nx a) , p ⟩
            → Flight ⟨ c , takeS i q free s , rising (nx a) , p ⟩
take-flight c i q s a p e (sh , _ , ab) =
  shape-out p a refl refl (subst (λ b → Shape′ (M′.taking i q p a b (stateᴺ (gh s) (envAt c))) (cutᴺ (gh s) (envAt c))) e
    (shape-takeᴱ i q (out p a (stateᴺ (gh s) (envAt c))) (cutᴺ (gh s) (envAt c)) sh))
  , above-≋ c true (take-true i q (gh s) (envAt c) a p e) ab

take-incl-flight : ∀ {R Γ A} (c : Ctx R Γ A) (q : A → Bool) (s : St Γ A) a p → q a ≡ false → Flight ⟨ inTake true q free c , s , rising (nx a) , p ⟩
                 → Flight ⟨ c , takeS true q (cpAt p) s , rising (nx a) , p ⊕ [ ix 0 ] ⟩
take-incl-flight c q s a p e (sh , _ , ab) =
  shape-out (p ⊕ [ ix 0 ]) a refl refl (subst (λ b → Shape′ (M′.taking true q p a b (stateᴺ (gh s) (envAt c))) (cutᴺ (gh s) (envAt c))) e
    (shape-takeᴱ true q (out p a (stateᴺ (gh s) (envAt c))) (cutᴺ (gh s) (envAt c)) sh))
  , above-≋ c true (take-incl q (gh s) (envAt c) a p e) ab

take-end-flight : ∀ {R Γ A} (c : Ctx R Γ A) i (q : A → Bool) (s : St Γ A) p → Flight ⟨ inTake i q free c , s , rising cp , p ⟩
                → Flight ⟨ c , takeS i q free s , rising cp , p ⟩
take-end-flight c i q s p (sh , _ , ab) = sh , above-≋ c true (≋-by refl refl) ab

module _ {R : Set} where
  open Driver R using (Step; silent; value; complete; drained; step; took)

  -- What a configuration owes of its flight beyond what its shape gives:
  -- a settled node's is read off the whole tree.
  Owed : Conf R → Set
  Owed ⟨ c , s , absorbed , p ⟩ = ⊤
  Owed k                        = Flight k

  NextOwed : Step → Set
  NextOwed (silent t k)    = Owed k
  NextOwed (value t p a k) = Owed k
  NextOwed (complete p)    = ⊤
  NextOwed drained         = ⊤

  postulate
    -- THE FLIGHT KEPT: an outer's value beginning its lane under an open
    -- observer, where only tails are read: every frame above the merge
    -- keeps its share of the merge's run, the lane begun.
    outer-begin-tail : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) n q ls (s : St Γ A) a p
                     → Order ⟨ inOuter op f false n q ls c , s , rising (nx a) , p ⟩ → Begins op n → closed c ≡ false
                     → showsᶜ c true ≡ false
                     → Above c true (lanesFrame op (lane f) false q (gh s) (reverse (reverse (keptLanes op ls))) [] true (envAt c)
                                       (stateᴺ (subscribe (f a) (p ⊕ [ ix 1 ])) (envAt c)))
    -- THE STILL'S SUBTREE: a lane's end under a queue, where it is shown,
    -- passes every live source above.
    lane-begin-links : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n a q (o : St Γ A) pre post (s : St Γ B) p
                     → showsᶜ c true ≡ true → Order ⟨ inLanes op f d n (a ∷ q) o pre post c , s , rising cp , p ⟩
                     → Links (_≡ p ⊕ [ ix 0 ]) c true (lanesFrame op (lane f) d (a ∷ q) (gh o) (reverse pre) post true (envAt c) (risen (gh s) (envAt c) cp p))
                             (lanesFrame op (lane f) d q (gh o) (reverse (reverse (pre ʳ++ ended s ∷ post))) [] true (envAt c)
                                (stateᴺ (subscribe (f a) (p ⊕ [ ix 1 ])) (envAt c)))
    -- THE FLIGHT KEPT: a lane's end under an open observer, a value
    -- queued, where only tails are read: every frame above the merge keeps
    -- its share of the merge's run, the queued lane begun.
    lane-begin-tail : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n a q (o : St Γ A) pre post (s : St Γ B) p
                    → Order ⟨ inLanes op f d n (a ∷ q) o pre post c , s , rising cp , p ⟩ → alive s ≡ true → closed c ≡ false
                    → showsᶜ c true ≡ false
                    → Above c true (lanesFrame op (lane f) d q (gh o) (reverse (reverse (pre ʳ++ ended s ∷ post))) [] true (envAt c)
                                      (stateᴺ (subscribe (f a) (p ⊕ [ ix 1 ])) (envAt c)))
    begin-flight : ∀ {Γ A} (c : Ctx R Γ A) (o : Obs Timeline Γ A) p → Order ⟨ c , pend o , subscribing , p ⟩
                 → NextOwed (step ⟨ c , pend o , subscribing , p ⟩)
    -- THE SORTED TAILS: every lane of a fragment's flatMap leaves its
    -- tail in position order.
    lanes-sorted : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) ls
                 → Frag (plug c (flatS op f d n q o ls)) → All (λ s → SortedT (cutᴺ (gh s) (envAt c))) ls

  -- A live lane rising: the frame above as its own lane, and the merge's
  -- run in shape, its parts in shape.
  frame-at : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) pre post (s : St Γ B) e p
           → Order ⟨ inLanes op f d n q o pre post c , s , rising e , p ⟩ → alive s ≡ true
           → Above (inLanes op f d n q o pre post c) true (risen (gh s) (envAt c) e p)
  frame-at c op f d n q o pre post s e p od a = subst (λ x → Above (inLanes op f d n q o pre post c) x (risen (gh s) (envAt c) e p)) a (proj₂ (Order.flight od))

  frame-shape : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) pre post (s : St Γ B) e p
              → Order ⟨ inLanes op f d n q o pre post c , s , rising e , p ⟩ → alive s ≡ true
              → Shape (lanesFrame op (lane f) d q (gh o) (reverse pre) post true (envAt c) (risen (gh s) (envAt c) e p))
  frame-shape c op f d n q o pre post s e p od a =
    FlatShape.flat-shape pk (flatOp op) _ _ _ _ (FlatShape.roots-of pk shs (proj₁ ks)) (proj₁ (proj₂ ks)) (proj₁ (proj₂ (proj₂ ks)))
      (gen-queue pk f ρ hp (proj₁ so′) cl q) (held-of pk f d o ρ hp (proj₁ so′) cl (proj₁ (proj₂ so′)) (proj₁ (proj₂ (proj₂ (proj₂ ks)))))
      (proj₂ (proj₂ (proj₂ (proj₂ ks))))
    where
      ρ  = envAt c
      ab = frame-at c op f d n q o pre post s e p od a
      fa = proj₁ (proj₁ ab)
      so′ = proj₂ (proj₂ (proj₂ (proj₂ (proj₁ ab))))
      pk = proj₁ fa
      hp = proj₁ (proj₂ fa)
      cl = proj₁ (proj₂ (proj₂ fa))
      ks = proj₂ (proj₂ (proj₂ (proj₂ fa)))
      shs : All Shape (laneRuns (reverse pre) post true ρ (risen (gh s) ρ e p))
      shs = All++⁺ (proj₂ (proj₂ (proj₂ so′))) (proj₁ (Order.flight od) ∷ᴬ proj₁ (proj₂ (proj₂ so′)))

  -- A lane's value rises out of its flatMap first among the merge's
  -- parts, its siblings in shape: the merge's run shows it first.
  rise-lane-flight : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) pre post (s : St Γ B) b p
                   → Order ⟨ inLanes op f d n q o pre post c , s , rising (nx b) , p ⟩ → alive s ≡ true
                   → Flight ⟨ c , flatS op f d n q o (pre ʳ++ s ∷ post) , rising (nx b) , p ⟩
  rise-lane-flight c op f d n q o pre post s b p od a =
    toʳ (λ ls → Flight ⟨ c , flatS op f d n q o ls , rising (nx b) , p ⟩) pre
      ( subst (Shape′ (out p b (stateᴺ (gh F) ρ))) (lanes-cut op f d n q o (reverse pre) post s ρ b p a)
          (shape-out p b (proj₁ (proj₂ (proj₂ lo))) (proj₂ (proj₂ (proj₂ lo))) (subst (λ x → Shape′ x (cut H)) (proj₁ (proj₂ lo)) sh))
      , above-≋ c true (lanes-rise op f d n q o (reverse pre) post s ρ b p a fi) (proj₂ (frame-at c op f d n q o pre post s (nx b) p od a)))
    where
      ρ  = envAt c
      F  = flatS op f d n q o (reverse pre ++ s ∷ post)
      H  = lanesFrame op (lane f) d q (gh o) (reverse pre) post true ρ (risen (gh s) ρ (nx b) p)
      fi = proj₁ (Order.lead od a)
      lo = lanes-out op f d n q o (reverse pre) post s ρ b p a fi
      sh : Shape′ (force H) (cut H)
      sh = frame-shape c op f d n q o pre post s (nx b) p od a

  -- The last lane's end is its merge's: the run ends there, the lane's
  -- tail joined to the pool where the lane sat.
  lane-last-flight : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n (o : St Γ A) pre post (s : St Γ B) p
                   → Order ⟨ inLanes op f d n [] o pre post c , s , rising cp , p ⟩ → alive s ≡ true → closed c ≡ false
                   → d ∧ (pred n ≡ᵇ 0) ∧ true ≡ true → Flight ⟨ c , flatS op f d (pred n) [] o (pre ʳ++ ended s ∷ post) , rising cp , p ⟩
  lane-last-flight c op f false n o pre post s p od al ce ()
  lane-last-flight c op f true  n o pre post s p od al ce de =
    toʳ (λ ls → Flight ⟨ c , flatS op f true (pred n) [] o ls , rising cp , p ⟩) pre
      ( shape-cut (end p) (cut H) (cutᴺ (gh F) ρ) ag (subst (λ x → Shape′ x (cut H)) fe (frame-shape c op f true n [] o pre post s cp p od al))
      , above-≋ c true (λ k → ag k ,ˢ subst (λ x → Agree k x (end p)) (sym fe) (agree-refl k (end p))) (proj₂ ab))
    where
      ρ  = envAt c
      h  = risen (gh s) ρ cp p
      H  = lanesFrame op (lane f) true [] (gh o) (reverse pre) post true ρ h
      F  = flatS op f true (pred n) [] o (reverse pre ++ ended s ∷ post)
      Sp = states (lanesL post) ρ
      Sr = states (lanesL (reverse pre)) ρ
      Dp = deadL (reverse pre)
      Pp = poolT (deadL post) ρ
      T  = outerT true (gh o) ρ (tailsOn Dp ρ Pp)
      ft = proj₁ (Order.shape od)
      ff = frag-flat c op f true n [] o (pre ʳ++ s ∷ post) ft
      ls = proj₁ (proj₂ (lanes-ʳsplit pre (proj₂ (frag-parts op f true n [] o (pre ʳ++ s ∷ post) ff))))
      ab = frame-at c op f true n [] o pre post s cp p od al
      ks = proj₂ (proj₂ (proj₂ (proj₂ (proj₁ (proj₁ ab)))))
      sT : SortedT T
      sT = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ ks))))
      sh : SortedT (cutᴺ (gh s) ρ)
      sh = proj₁ (trail (proj₂ (proj₁ (Order.flight od))))
      sP : SortedT Pp
      sP = pool-sorted post ρ (proj₂ (all-at pre (lanes-sorted c op f true n [] o (pre ʳ++ s ∷ post) ft)))
      cn : n ≡ length (Sp ++ stateᴺ (gh s) ρ ∷ Sr)
      cn = trans (frag-count op f true n o (pre ʳ++ s ∷ post) ff)
             (trans (cong (λ x → length (lanesL x)) (ʳ++-defn pre))
               (trans (sym (states-length (lanesL (reverse pre ++ s ∷ post)) ρ)) (cong length (lanes-L (reverse pre) s post ρ al))))
      e₁ = proj₁ (last-one n de Sp Sr (stateᴺ (gh s) ρ) cn)
      e₂ = proj₂ (last-one n de Sp Sr (stateᴺ (gh s) ρ) cn)
      fe : force H ≡ end p
      fe = trans (go-rise (flatOp op) nothing Sp h Sr [] T refl (proj₁ (proj₂ (Order.lead od)) ce)) (lane-solo (flatOp op) h T p e₁ e₂)
      L1 = trans (lanes-runs (reverse pre) (ended s) post ρ)
             (trans (cong (λ x → laneRuns (reverse pre) post x ρ (stateᴺ (gh (ended s)) ρ)) (ended-flag s ls)) (cong₂ _++_ e₁ e₂))
      P1 = trans (pool-runs (reverse pre) (ended s) post ρ)
             (trans (cong (λ x → poolRuns (reverse pre) post x ρ (stateᴺ (gh (ended s)) ρ)) (ended-flag s ls))
                    (cong (λ t → tailsOn Dp ρ (t ∪ Pp)) (ended-cut s ρ ls)))
      ag : ∀ k → Agreeᵀ k (cut H) (cutᴺ (gh F) ρ)
      ag k =
        subst (λ x → Agreeᵀ k x (cutᴺ (gh F) ρ)) (sym (cong₂ (λ a b → M′.cuts (a ++ h ∷ b) ∪ T) e₁ e₂))
          (subst (Agreeᵀ k _) (sym (cong₂ (λ ls′ t → M′.cuts ls′ ∪ (cutᴺ (gh o) ρ ∪ t)) L1 P1))
            (agreeᵀ-trans (∪-ne (∪-idleᵀ k (cutᴺ (gh s) ρ)) (agreeᵀ-refl k T))
              (agreeᵀ-trans (∪-commᵀ k (cutᴺ (gh s) ρ) T sh sT) (pool-ended k true (gh o) Dp ρ Pp (cutᴺ (gh s) ρ) sP sh))))

  -- An open outer's end, nothing running or waiting, is its merge's: the
  -- pool's pins no earlier, the outer's tail joined to the pool.
  outer-end-flight : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) ls (s : St Γ A) p
                   → Order ⟨ inOuter op f false zero [] ls c , s , rising cp , p ⟩ → closed c ≡ false
                   → Flight ⟨ c , flatS op f true zero [] s ls , rising cp , p ⟩
  outer-end-flight c op f ls s p od ce =
    ( shape-cut (end p) (cut H) (cutᴺ (gh F) ρ) ag (subst (λ x → Shape′ x (cut H)) fe sh)
    , above-≋ c true (λ k → ag k ,ˢ subst (λ x → Agree k x (end p)) (sym fe) (agree-refl k (end p))) (proj₂ (proj₂ (Order.flight od))))
    where
      ρ  = envAt c
      h  = risen (gh s) ρ cp p
      H  = outerFrame op (lane f) false [] (lanesL ls) (deadL ls) ρ h
      F  = flatS op f true zero [] s ls
      e  = outerOf (lane f) ρ h
      Ls = states (lanesL ls) ρ
      T  = poolT (deadL ls) ρ
      ff = frag-flat c op f false zero [] s ls (proj₁ (Order.shape od))
      L0 : Ls ≡ []
      L0 = len0 Ls (trans (frag-count op f false zero s ls ff) (sym (states-length (lanesL ls) ρ)))
      lt = proj₁ (Order.lead od) refl ce
      fe : force H ≡ end p
      fe = trans (go-outer (flatOp op) e Ls [] T refl (proj₁ lt) (proj₂ lt)) (cong (λ x → M′.outer (flatOp op) e x [] T (end p)) L0)
      fl = proj₁ (proj₁ (proj₂ (Order.flight od)))
      pk = proj₁ fl
      fk = proj₂ (proj₂ (proj₂ (proj₂ fl)))
      ok = proj₁ (proj₂ (proj₂ (proj₂ fk)))
      se = shape-end p (proj₁ (Order.flight od))
      hd : FlatOrder.Heldᴹ pk (just e)
      hd = FlatOrder.outer (proj₁ (proj₁ (proj₁ se))) (proj₂ (proj₁ (proj₁ se))) (proj₂ se) (proj₁ ok) (proj₁ (proj₂ ok)) (proj₂ (proj₂ ok))
             (record { values = tt })
      sh : Shape′ (force H) (cut H)
      sh = FlatShape.flat-shape pk (flatOp op) (just e) Ls [] T (FlatShape.roots-of pk (subst (All Shape) (sym L0) []ᴬ) (proj₁ fk))
             (proj₁ (proj₂ fk)) (proj₁ (proj₂ (proj₂ fk))) []ᴬ hd (proj₂ (proj₂ (proj₂ (proj₂ fk))))
      ag : ∀ k → Agreeᵀ k (cut H) (cutᴺ (gh F) ρ)
      ag k = subst (λ x → Agreeᵀ k (cutᴺ (gh s) ρ ∪ (M′.cuts x ∪ T)) (M′.cuts x ∪ cutᴺ (poolG true (gh s) (deadL ls)) ρ)) (sym L0)
               (agreeᵀ-refl k _)

  -- A lane ended under a queue: its end a skip, past it the queue's next
  -- lane begun ahead of the rest, the ended lane's tail in the pool where
  -- the lane sat.
  ended-begins : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d a q (o : St Γ A) pre post (s : St Γ B) p
               → Lane s → alive s ≡ true → SortedT (cutᴺ (gh s) (envAt c)) → SortedT (poolT (deadL post) (envAt c))
               → Sides p f d o (reverse pre) post (envAt c)
               → Dropsˢ (_≡ p ⊕ [ ix 0 ]) (lanesFrame op (lane f) d (a ∷ q) (gh o) (reverse pre) post true (envAt c) (risen (gh s) (envAt c) cp p))
                  (lanesFrame op (lane f) d q (gh o) (reverse (reverse (pre ʳ++ ended s ∷ post))) [] true (envAt c) (stateᴺ (subscribe (f a) (p ⊕ [ ix 1 ])) (envAt c)))
  ended-begins c op f d a q o pre post (lnS true (cutS true x s₀)) p fs al ss sp sd =
    lane-admits op (lane f) d a q (gh o) (reverse pre) post ρ (gh s₀) p (lanesFrame op (lane f) d q (gh o) (reverse (reverse L)) [] true ρ h) sd refl refl
      (λ m → subst (Lanes m _) (begun-runs L ρ h)
               (subst (λ z → Lanes m (h ∷ states (lanesL post) ρ ++ states (lanesL (reverse pre)) ρ) (h ∷ z)) runs
                  (lanes-refl m (h ∷ states (lanesL post) ρ ++ states (lanesL (reverse pre)) ρ))))
      (λ m → subst (λ z → Agreeᵀ m (outerT d (gh o) ρ (tailsOn (deadL (reverse pre)) ρ (poolT (deadL post) ρ)) ∪ cutᴺ (gh s₀) ρ) (outerT d (gh o) ρ z)) pool
               (pool-ended m d (gh o) (deadL (reverse pre)) ρ (poolT (deadL post) ρ) (cutᴺ (gh s₀) ρ) sp ss))
    where
      ρ = envAt c
      e = lnS false (cutS false x s₀)
      L = pre ʳ++ e ∷ post
      h = stateᴺ (subscribe (f a) (p ⊕ [ ix 1 ])) ρ
      runs : states (lanesL post) ρ ++ states (lanesL (reverse pre)) ρ ≡ states (lanesL L) ρ
      runs = trans (sym (lanes-runs (reverse pre) e post ρ)) (cong (λ z → states (lanesL z) ρ) (sym (ʳ++-defn pre)))
      pool : tailsOn (deadL (reverse pre)) ρ (cutᴺ (gh s₀) ρ ∪ poolT (deadL post) ρ) ≡ poolRuns (reverse (reverse L)) [] true ρ h
      pool = trans (sym (pool-runs (reverse pre) e post ρ)) (trans (cong (λ z → poolT (deadL z) ρ) (sym (ʳ++-defn pre))) (begun-pool L ρ h))
  ended-begins c op f d a q o pre post (lnS false (cutS false x s₀)) p fs () ss sp sd


  -- A lane's end under an open observer, a value queued, drops the skip
  -- just past the end.
  lane-begins-open : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n a q (o : St Γ A) pre post (s : St Γ B) p
                   → Order ⟨ inLanes op f d n (a ∷ q) o pre post c , s , rising cp , p ⟩ → alive s ≡ true → closed c ≡ false
                   → Dropsˢ (_≡ p ⊕ [ ix 0 ]) (lanesFrame op (lane f) d (a ∷ q) (gh o) (reverse pre) post true (envAt c) (risen (gh s) (envAt c) cp p))
                       (lanesFrame op (lane f) d q (gh o) (reverse (reverse (pre ʳ++ ended s ∷ post))) [] true (envAt c) (stateᴺ (subscribe (f a) (p ⊕ [ ix 1 ])) (envAt c)))
  lane-begins-open c op f d n a q o pre post s p od al ce =
    ended-begins c op f d a q o pre post s p (proj₁ (proj₂ (lanes-ʳsplit pre fl))) al (proj₁ ss) (pool-sorted post (envAt c) (proj₂ ss))
      (proj₁ (proj₂ (Order.lead od)) ce)
    where
      ft = proj₁ (Order.shape od)
      fl = proj₂ (frag-parts op f d n (a ∷ q) o (pre ʳ++ s ∷ post) (frag-flat c op f d n (a ∷ q) o (pre ʳ++ s ∷ post) ft))
      ss = all-at pre (lanes-sorted c op f d n (a ∷ q) o (pre ʳ++ s ∷ post) ft)

  -- And where it is shown, every frame above shows it next.
  lane-begin-pass : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n a q (o : St Γ A) pre post (s : St Γ B) p
                  → showsᶜ c true ≡ true → Order ⟨ inLanes op f d n (a ∷ q) o pre post c , s , rising cp , p ⟩
                  → Pass (_≡ p ⊕ [ ix 0 ]) c true (lanesFrame op (lane f) d (a ∷ q) (gh o) (reverse pre) post true (envAt c) (risen (gh s) (envAt c) cp p))
                      (lanesFrame op (lane f) d q (gh o) (reverse (reverse (pre ʳ++ ended s ∷ post))) [] true (envAt c) (stateᴺ (subscribe (f a) (p ⊕ [ ix 1 ])) (envAt c)))
  lane-begin-pass c op f d n a q o pre post s p sh od =
    pass-of (_≡ p ⊕ [ ix 0 ]) c true (proj₁ (proj₂ (proj₂ (proj₂ (Order.lead od))) sh)) (lane-begin-links c op f d n a q o pre post s p sh od)

  -- A lane's end under an open observer, a value queued: every frame
  -- above the merge keeps its share past the skip the merge's run drops
  -- just after the end, the queued lane begun; where only tails are read,
  -- of the merge's tail.
  lane-begin-above : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n a q (o : St Γ A) pre post (s : St Γ B) p
                   → Order ⟨ inLanes op f d n (a ∷ q) o pre post c , s , rising cp , p ⟩ → alive s ≡ true → closed c ≡ false
                   → Above c true (lanesFrame op (lane f) d q (gh o) (reverse (reverse (pre ʳ++ ended s ∷ post))) [] true (envAt c) (stateᴺ (subscribe (f a) (p ⊕ [ ix 1 ])) (envAt c)))
  lane-begin-above c op f d n a q o pre post s p od al ce with showsᶜ c true in sh
  ... | true  = above-drops (_≡ p ⊕ [ ix 0 ]) c true (lane-begins-open c op f d n a q o pre post s p od al ce)
                  (lane-begin-pass c op f d n a q o pre post s p sh od) (proj₂ (frame-at c op f d n (a ∷ q) o pre post s cp p od al))
  ... | false = lane-begin-tail c op f d n a q o pre post s p od al ce sh

  -- A lane's end under an open observer, a value queued: its lane begins
  -- just past the end, in shape, the merge keyed with it in the ended
  -- lane's place, the ended lane's tail in the pool.
  lane-begin-flight : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n a q (o : St Γ A) pre post (s : St Γ B) p
                    → Order ⟨ inLanes op f d n (a ∷ q) o pre post c , s , rising cp , p ⟩ → alive s ≡ true → closed c ≡ false
                    → Flight ⟨ inCut true (attAt (p ⊕ [ ix 1 ])) (inLn true (inLanes op f d (suc (pred n)) q o (reverse (pre ʳ++ ended s ∷ post)) [] c))
                             , pend (f a) , subscribing , p ⊕ [ ix 1 ] ⟩
  lane-begin-flight c op f d n a q o pre post s p od al ce =
    proj₂ fh
    , ( ( (pk , hp , cl , subst₂ (λ ls t → Σ (List Pos) (FlatKeys pk O ls t)) E (cong (outerT d (gh o) ρ) PU) (proj₁ fh))
        , ko , keyedL-ʳ++ L (keyedL-ʳ++ pre kpre (keyed-ended s ρ ls (proj₂ (Order.shape od)) , kpost)) tt , tt , so , sho
        , subst (All Shape) (cong (λ z → states (lanesL z) ρ) (sym (reverse-involutive L))) (subst (All Shape) RU (All++⁺ shpost shpre))
        , []ᴬ )
      , lane-begin-above c op f d n a q o pre post s p od al ce )
    where
      ρ  = envAt c
      h  = risen (gh s) ρ cp p
      L  = pre ʳ++ ended s ∷ post
      H  = stateᴺ (subscribe (f a) (p ⊕ [ ix 1 ])) ρ
      O  = outerᴺ (lane f) (outerG d (gh o)) ρ
      Sp = states (lanesL post) ρ
      Sr = states (lanesL (reverse pre)) ρ
      Dp = deadL (reverse pre)
      Pp = poolT (deadL post) ρ
      ft = proj₁ (Order.shape od)
      ff = frag-flat c op f d n (a ∷ q) o (pre ʳ++ s ∷ post) ft
      ls = proj₁ (proj₂ (lanes-ʳsplit pre (proj₂ (frag-parts op f d n (a ∷ q) o (pre ʳ++ s ∷ post) ff))))
      ab = frame-at c op f d n (a ∷ q) o pre post s cp p od al
      fa = proj₁ (proj₁ ab)
      pk = proj₁ fa
      hp = proj₁ (proj₂ fa)
      cl = proj₁ (proj₂ (proj₂ fa))
      fk = proj₂ (proj₂ (proj₂ (proj₂ fa)))
      rs = proj₂ (proj₁ ab)
      ko     = proj₁ rs
      kpre   = proj₁ (proj₂ rs)
      kpost  = proj₁ (proj₂ (proj₂ rs))
      so     = proj₁ (proj₂ (proj₂ (proj₂ rs)))
      sho    = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ rs))))
      shpre  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ rs)))))
      shpost = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ rs)))))
      sh : SortedT (cutᴺ (gh s) ρ)
      sh = proj₁ (trail (proj₂ (proj₁ (Order.flight od))))
      sP : SortedT Pp
      sP = pool-sorted post ρ (proj₂ (all-at pre (lanes-sorted c op f d n (a ∷ q) o (pre ʳ++ s ∷ post) ft)))
      fh = flat-hand pk O Sp h Sr (outerT d (gh o) ρ (tailsOn Dp ρ (cutᴺ (gh s) ρ ∪ Pp))) p (laneᴹ (lane f) ρ a) refl
             (λ k → pool-ended k d (gh o) Dp ρ Pp (cutᴺ (gh s) ρ) sP sh)
             (All++⁺ shpost (proj₁ (Order.flight od) ∷ᴬ shpre)) fk
             (held-of pk f d o ρ hp so cl sho (proj₁ (proj₂ (proj₂ (proj₂ fk))))) (gen-sub pk f ρ hp so cl a)
      RU : Sp ++ Sr ≡ states (lanesL L) ρ
      RU = sym (trans (cong (λ x → states (lanesL x) ρ) (ʳ++-defn pre))
                 (trans (lanes-runs (reverse pre) (ended s) post ρ)
                        (cong (λ x → laneRuns (reverse pre) post x ρ (stateᴺ (gh (ended s)) ρ)) (ended-flag s ls))))
      E : H ∷ Sp ++ Sr ≡ laneRuns (reverse (reverse L)) [] true ρ H
      E = trans (cong (H ∷_) RU) (begun-runs L ρ H)
      P1 = trans (pool-runs (reverse pre) (ended s) post ρ)
             (trans (cong (λ x → poolRuns (reverse pre) post x ρ (stateᴺ (gh (ended s)) ρ)) (ended-flag s ls))
                    (cong (λ t → tailsOn Dp ρ (t ∪ Pp)) (ended-cut s ρ ls)))
      PU : tailsOn Dp ρ (cutᴺ (gh s) ρ ∪ Pp) ≡ poolRuns (reverse (reverse L)) [] true ρ H
      PU = trans (sym P1) (trans (cong (λ z → poolT (deadL z) ρ) (sym (ʳ++-defn pre))) (begun-pool L ρ H))

  -- A body's value rises out of its connect only while the connect is
  -- live, its source no earlier: the connect's run shows it first, the
  -- body read unshut.
  body-flight : ∀ {Γ X B} (c : Ctx R Γ B) k (o : St Γ X) (s : St (X ∷ Γ) B) b p → Order ⟨ inBody k o c , s , rising (nx b) , p ⟩
              → CS.srcLive k ≡ true → CS.owedAt k ≡ nothing
              → Shape (risen (connectᶜ (CS.srcAt k) (gh s) (srcG k o)) (envAt c) (nx b) p) × Above c true (risen (connectᶜ (CS.srcAt k) (gh s) (srcG k o)) (envAt c) (nx b) p)
  body-flight c (cs cl true sa ba as nothing r en) o s b p od refl refl =
    subst (Shape′ (out p b (stateᴺ (connectᶜ r (gh s) (srcG k o)) ρ))) (sym (proj₂ cr))
      (shape-out p b ft ct (subst (λ x → Shape′ x (M′.burstOn r σ ∪ cut h)) (proj₁ (proj₂ so)) bs))
    , above-≋ c true (≋-out (proj₁ (proj₂ so)) refl ft ct (sym (proj₂ cr))) (proj₂ (proj₂ (Order.flight od)))
    where
      k  = cs cl true sa ba as nothing r en
      ce = Order.heard od
      ρ  = envAt c
      σ  = srcState (srcG k o) ρ
      h  = risen (gh s) (envAt (inBody k o c)) (nx b) p
      ca = proj₁ (proj₁ (proj₂ (Order.flight od)))
      sσ = proj₂ (proj₂ (proj₁ (proj₂ (Order.flight od))))
      cr = conn-run r (gh s) (srcG k o) ρ
      so = side-out r σ (force σ) {h = h} p b refl (burst-hushed r {σ = σ} (proj₂ sσ)) (proj₁ (proj₂ (Order.lead od)))
      ft = trans (proj₁ (proj₂ (proj₂ so))) (sym (proj₁ cr))
      ct = trans (proj₂ (proj₂ (proj₂ so))) (sym (proj₂ cr))
      bs = subst (λ r′ → Shape′ (M′.beside r′ h σ) (M′.burstOn r′ σ ∪ cut h)) (sym (ConnAt.at ca))
             (beside-go (ConnAt.mark ca) (ConnAt.hm ca) h σ sσ (proj₁ (Order.flight od))
                (ConnAt.kb ca) (ConnAt.kr ca) (ConnAt.fr ca) (ConnAt.cue ca) (ConnAt.ks ca) (ConnAt.rs ca) (ConnAt.ub ca))

  -- And so with the body shut once its source has ended (`bodyG`).
  rise-body-flight : ∀ {Γ X B} (c : Ctx R Γ B) k (o : St Γ X) (s : St (X ∷ Γ) B) b p → Order ⟨ inBody k o c , s , rising (nx b) , p ⟩
                   → Flight ⟨ c , connS k o s , rising (nx b) , p ⟩
  rise-body-flight c k@(cs cl true sa ba as nothing r en) o s b p od =
    shape-≋ (risen-≋ b p (body-≋ k r (gh s) o (envAt c))) (proj₁ fl) , above-≋ c true (risen-≋ b p (body-≋ k r (gh s) o (envAt c))) (proj₂ fl)
    where fl = body-flight c k o s b p od refl refl
  rise-body-flight c (cs cl true sa ba as (just _) r en) o s b p od = ⊥-elim (Order.lead od)
  rise-body-flight c (cs cl false sa ba as ow r en) o s b p od      = ⊥-elim (Order.lead od)

  -- A merge settled: an end rising, else nothing owed.
  settled : ∀ {Γ A} (c : Ctx R Γ A) (s : St Γ A) p b → (b ≡ true → Flight ⟨ c , s , rising cp , p ⟩)
          → Owed ⟨ c , s , (if b then rising cp else absorbed) , p ⟩
  settled c s p true  fl = fl refl
  settled c s p false fl = tt

  -- A lane begun under an open observer.
  begun : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) ls a p → closed c ≡ false
        → Flight ⟨ inCut true (attAt (p ⊕ [ ix 1 ])) (inLn true (inLanes op f d (suc n) q o (reverse ls) [] c)) , pend (f a) , subscribing , p ⊕ [ ix 1 ] ⟩
        → Owed (start c op f d n q o ls a p)
  begun c op f d n q o ls a p ce fl with closed c | ce
  ... | false | refl = fl

  -- A lane begun under an open observer, else the value absorbed.
  started : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) ls a p
          → (closed c ≡ false → Flight ⟨ inCut true (attAt (p ⊕ [ ix 1 ])) (inLn true (inLanes op f d (suc n) q o (reverse ls) [] c))
                                       , pend (f a) , subscribing , p ⊕ [ ix 1 ] ⟩)
          → Owed (start c op f d n q o ls a p)
  started c op f d n q o ls a p fl with closed c
  ... | true  = tt
  ... | false = fl refl

  -- An outer's value under an open observer: every frame above the merge
  -- keeps its share past the skip the merge's run drops for the value,
  -- the lane begun; where only tails are read, of the merge's tail.
  admit-above : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) n q ls (s : St Γ A) a p
              → Order ⟨ inOuter op f false n q ls c , s , rising (nx a) , p ⟩ → Begins op n → closed c ≡ false
              → Above c true (lanesFrame op (lane f) false q (gh s) (reverse (reverse (keptLanes op ls))) [] true (envAt c)
                                (stateᴺ (subscribe (f a) (p ⊕ [ ix 1 ])) (envAt c)))
  admit-above c op f n q ls s a p od b ce with showsᶜ c true in sh
  ... | true  = above-drops (_≡ p ⊕ [ ix 0 ]) c true (outer-begins b od) (outer-begins-pass sh od) (proj₂ (proj₂ (Order.flight od)))
  ... | false = outer-begin-tail c op f n q ls s a p od b ce sh

  -- An outer's value under an open observer begins its lane just past
  -- the value, in shape, the merge keyed with it ahead of the lanes kept,
  -- the lanes a switch kills in the pool.
  admit-flight : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) n q ls (s : St Γ A) a p
               → Order ⟨ inOuter op f false n q ls c , s , rising (nx a) , p ⟩ → Begins op n → closed c ≡ false
               → Flight ⟨ inCut true (attAt (p ⊕ [ ix 1 ])) (inLn true (inLanes op f false (suc (running op n)) q s (reverse (keptLanes op ls)) [] c))
                        , pend (f a) , subscribing , p ⊕ [ ix 1 ] ⟩
  admit-flight c op f n q ls s a p od b ce =
    fit-shape pk q₁ H (gm q₁ okq)
    , ( ( (pk , hp , cl , proj₁ ks , keys-≡ pk {w = tailᴱ (force (outerOf (lane f) ρ (risen (gh s) ρ (nx a) p))) w′} {w′ = w′} refl refl (proj₂ ks))
        , proj₂ (Order.shape od) , keyedL-ʳ++ Lk kL tt , tt , so , shape-past p a (stateᴺ (gh s) ρ) (proj₁ (Order.flight od))
        , keyedL-shape (reverse (reverse Lk)) ρ (keyedL-ʳ++ (reverse Lk) (keyedL-ʳ++ Lk kL tt) tt) so , []ᴬ )
      , admit-above c op f n q ls s a p od b ce )
    where
      ρ   = envAt c
      Lk  = keptLanes op ls
      w′  = outer∞ (lane f) (gh s) ρ
      Ls  = states (lanesL ls) ρ
      T   = poolT (deadL ls) ρ
      m   = laneᴹ (lane f) ρ a
      q₁  = p ⊕ [ ix 1 ]
      H   = M′.enter m q₁
      fa  = proj₁ (proj₁ (proj₂ (Order.flight od)))
      kl  = proj₂ (proj₁ (proj₂ (Order.flight od)))
      ab  = proj₂ (proj₂ (Order.flight od))
      pk  = proj₁ fa
      hp  = proj₁ (proj₂ fa)
      cl  = proj₁ (proj₂ (proj₂ fa))
      fk  = proj₂ (proj₂ (proj₂ (proj₂ fa)))
      lk  = proj₁ fk
      pt  = proj₁ (proj₂ fk)
      asd = proj₁ (proj₂ (proj₂ fk))
      ok  = proj₁ (proj₂ (proj₂ (proj₂ fk)))
      pl  = proj₂ (proj₂ (proj₂ (proj₂ fk)))
      so  = above-sorted c true ab
      fl  = proj₂ (frag-parts op f false n q s ls (frag-flat c op f false n q s ls (proj₁ (Order.shape od))))
      kL  = kept-keyed op ls ρ kl
      gm  = gen-sub pk f ρ hp so cl a
      okq = FlatOrder.lane-ok pk p (proj₁ (every (proj₁ (proj₂ ok))))
      sp  = proj₁ (spread (proj₁ ok))
      sw  = proj₂ (spread (proj₁ ok))
      kw  = proj₂ (every (proj₁ (proj₂ ok)))
      Rt  = FlatShape.roots-of pk (keyedL-shape ls ρ kl so) lk
      gq  = gen-queue pk f ρ hp so cl q
      bl  = mapᴬ (λ {l} → after-beyond p (force l)) (proj₁ (proj₂ (Order.lead od)))
      ks  = admit-keys pk op ls ρ H (L.map (laneᴹ (lane f) ρ) q) fl sw kw
              (FlatOrder.Admit.admit-new pk p m _ T (mapᴬ proj₁ asd) gm okq sp kw pl Ls _ Rt pt gq bl)
              (FlatOrder.Admit.admit-switch pk p m _ T (mapᴬ proj₁ asd) gm okq sp kw pl Ls _ Rt pt gq bl)

  -- An outer's value admitted: a lane begun under an open observer, else
  -- the value queued, dropped by a busy exhaust, or absorbed under a
  -- closed one.
  rise-admit-flight : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q ls (s : St Γ A) a p
                    → Order ⟨ inOuter op f d n q ls c , s , rising (nx a) , p ⟩ → NextOwed (took (admit c op f d n q s ls a p))
  rise-admit-flight c op f true n q ls s a p od = ⊥-elim (Order.lead od)
  rise-admit-flight c (mergeᶠ nothing) f false n q ls s a p od =
    started c (mergeᶠ nothing) f false n q s ls a p (admit-flight c (mergeᶠ nothing) f n q ls s a p od tt)
  rise-admit-flight c (mergeᶠ (just k)) f false n q ls s a p od with n <ᵇ k in b
  ... | true  = started c (mergeᶠ (just k)) f false n q s ls a p (admit-flight c (mergeᶠ (just k)) f n q ls s a p od b)
  ... | false = tt
  rise-admit-flight c switchᶠ f false n q ls s a p od with killAll ls in ek
  ... | ls′ , t = started c switchᶠ f false 0 q s ls′ a p
                    (λ ce → subst (λ x → Flight ⟨ inCut true (attAt (p ⊕ [ ix 1 ])) (inLn true (inLanes switchᶠ f false 1 q s (reverse x) [] c))
                                                , pend (f a) , subscribing , p ⊕ [ ix 1 ] ⟩)
                                  (cong proj₁ ek) (admit-flight c switchᶠ f n q ls s a p od tt ce))
  rise-admit-flight c exhaustᶠ f false n q ls s a p od with n ≡ᵇ 0 in b
  ... | true  = started c exhaustᶠ f false n q s ls a p (admit-flight c exhaustᶠ f n q ls s a p od b)
  ... | false = tt

  -- A lane's end frees its slot: the merge settles or dequeues.
  rise-lane-end-open : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) pre post (s : St Γ B) p
                     → Order ⟨ inLanes op f d n q o pre post c , s , rising cp , p ⟩ → alive s ≡ true → closed c ≡ false
                     → Owed (dequeue c op f d (pred n) q o (pre ʳ++ ended s ∷ post) p)
  rise-lane-end-open c op f d n []      o pre post s p od al ce =
    settled c _ p (d ∧ (pred n ≡ᵇ 0) ∧ true) (lane-last-flight c op f d n o pre post s p od al ce)
  rise-lane-end-open c op f d n (a ∷ q) o pre post s p od al ce =
    begun c op f d (pred n) q o (pre ʳ++ ended s ∷ post) a p ce (lane-begin-flight c op f d n a q o pre post s p od al ce)

  rise-lane-end-flight : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) pre post (s : St Γ B) p
                       → Order ⟨ inLanes op f d n q o pre post c , s , rising cp , p ⟩ → alive s ≡ true
                       → Owed (dequeue c op f d (pred n) q o (pre ʳ++ ended s ∷ post) p)
  rise-lane-end-flight c op f d n q o pre post s p od al = rise-lane-end-open c op f d n q o pre post s p od al (Order.heard od)

  -- A body's end ends its live connect, its source no earlier under an
  -- open observer: the connect's run ends there, the body read unshut.
  body-end-flight : ∀ {Γ X B} (c : Ctx R Γ B) k (o : St Γ X) (s : St (X ∷ Γ) B) p → Order ⟨ inBody k o c , s , rising cp , p ⟩
                  → CS.srcLive k ≡ true → CS.owedAt k ≡ nothing
                  → Shape (risen (restᶜ {B = B} (connectᶜ (CS.srcAt k) (gh s) (srcG k o))) (envAt c) cp p)
                  × Above c true (risen (restᶜ {B = B} (connectᶜ (CS.srcAt k) (gh s) (srcG k o))) (envAt c) cp p)
  body-end-flight c (cs cl true sa ba as nothing r en) o s p od refl refl =
    subst (Shape′ (end p)) (sym (proj₂ cr)) (subst (λ x → Shape′ x (M′.burstOn r σ ∪ cut h)) se bs)
    , above-≋ c true (≋-by se (sym (proj₂ cr))) (proj₂ (proj₂ (Order.flight od)))
    where
      k  = cs cl true sa ba as nothing r en
      ce = Order.heard od
      ρ  = envAt c
      σ  = srcState (srcG k o) ρ
      h  = risen (gh s) (envAt (inBody k o c)) cp p
      ca = proj₁ (proj₁ (proj₂ (Order.flight od)))
      sσ = proj₂ (proj₂ (proj₁ (proj₂ (Order.flight od))))
      cr = conn-run r (gh s) (srcG k o) ρ
      se = side-end r σ (force σ) {h = h} p refl (proj₂ (proj₁ (Order.lead od) ce))
      bs = subst (λ r′ → Shape′ (M′.beside r′ h σ) (M′.burstOn r′ σ ∪ cut h)) (sym (ConnAt.at ca))
             (beside-go (ConnAt.mark ca) (ConnAt.hm ca) h σ sσ (proj₁ (Order.flight od))
                (ConnAt.kb ca) (ConnAt.kr ca) (ConnAt.fr ca) (ConnAt.cue ca) (ConnAt.ks ca) (ConnAt.rs ca) (ConnAt.ub ca))

  -- And so with the body shut once its source has ended.
  rise-body-end-flight : ∀ {Γ X B} (c : Ctx R Γ B) k (o : St Γ X) (s : St (X ∷ Γ) B) p → Order ⟨ inBody k o c , s , rising cp , p ⟩
                       → Flight ⟨ c , connS (record k { owedAt = just p }) o s , rising cp , p ⟩
  rise-body-end-flight c k@(cs cl true sa ba as nothing r en) o s p od =
    shape-≋ (risen-end-≋ p E) (proj₁ fl) , above-≋ c true (risen-end-≋ p E) (proj₂ fl)
    where fl = body-end-flight c k o s p od refl refl
          E  = body-≋ (record k { owedAt = just p }) r (gh s) o (envAt c)
  rise-body-end-flight c (cs cl true sa ba as (just _) r en) o s p od = ⊥-elim (Order.lead od)
  rise-body-end-flight c (cs cl false sa ba as ow r en) o s p od      = ⊥-elim (Order.lead od)

  -- A rise through a frame of one child passes its run up; one absorbed
  -- owes nothing.
  rise-owed : ∀ {Γ A} (c : Ctx R Γ A) (s : St Γ A) e p → Order ⟨ c , s , rising e , p ⟩ → NextOwed (took (rise c s e p))
  rise-owed top                               s (nx a) p o = tt
  rise-owed top                               s cp     p o = tt
  rise-owed (inMap f c)                       s e      p o = map-flight c f s e p (Order.flight o)
  rise-owed (inScan f z c)                    s (nx a) p o = scan-flight c f z s a p (Order.flight o)
  rise-owed (inScan f z c)                    s cp     p o = scan-end-flight c f z s p (Order.flight o)
  rise-owed (inCut true a c)                  s e      p o = Order.flight o
  rise-owed (inCut false a c)                 s e      p o = tt
  rise-owed (inLn b c)                        s e      p o = Order.flight o
  rise-owed (inTake i q free c)               s (nx a) p o with q a in e | i
  ... | true  | w     = take-flight c w q s a p e (Order.flight o)
  ... | false | true  = take-incl-flight c q s a p e (Order.flight o)
  ... | false | false = tt
  rise-owed (inTake i q free c)               s cp     p o = take-end-flight c i q s p (Order.flight o)
  rise-owed (inTake i q (cpAt r) c)           s e      p o = tt
  rise-owed (inTake i q (cutAt r) c)          s e      p o = tt
  rise-owed (inTake i q (overAt r) c)         s e      p o = tt
  rise-owed (inOuter op f d n q ls c)         s (nx a) p o = rise-admit-flight c op f d n q ls s a p o
  rise-owed (inOuter op f true n q ls c)          s cp p o = tt
  rise-owed (inOuter op f false (suc n) q ls c)   s cp p o = tt
  rise-owed (inOuter op f false zero (_ ∷ _) ls c) s cp p o = tt
  rise-owed (inOuter op f false zero [] ls c)     s cp p o = outer-end-flight c op f ls s p o (Order.heard o)
  rise-owed (inLanes op f d n q o′ pre post c) s (nx b) p o with alive s in a
  ... | true  = rise-lane-flight c op f d n q o′ pre post s b p o a
  ... | false = tt
  rise-owed (inLanes op f d n q o′ pre post c) s cp     p o with alive s in a
  ... | true  = rise-lane-end-flight c op f d n q o′ pre post s p o a
  ... | false = tt
  rise-owed (inSrc k b c)                     s (nx a) p o = tt
  rise-owed (inSrc k b c)                     s cp     p o = tt
  rise-owed (inBody k o′ c)                   s (nx b) p o = rise-body-flight c k o′ s b p o
  rise-owed (inBody k o′ c)                   s cp     p o = rise-body-end-flight c k o′ s p o

  -- A subscribe of a settled node leaves the configuration as it was.
  sub-owed : ∀ {Γ A} (c : Ctx R Γ A) (s : St Γ A) p → Order ⟨ c , s , subscribing , p ⟩ → NextOwed (step ⟨ c , s , subscribing , p ⟩)
  sub-owed c (pend x)                p o = begin-flight c x p o
  sub-owed c (coldS b l)             p o = Order.flight o
  sub-owed c (ofS i q xs)            p o = Order.flight o
  sub-owed c doneS                   p o = Order.flight o
  sub-owed c (mapS f s)              p o = Order.flight o
  sub-owed c (scanS f z s)           p o = Order.flight o
  sub-owed c (cutS l a s)            p o = Order.flight o
  sub-owed c (lnS b s)               p o = Order.flight o
  sub-owed c (takeS i q w s)         p o = Order.flight o
  sub-owed c (flatS op f d n q o′ ls) p o = Order.flight o
  sub-owed c (connS k o′ b)          p o = Order.flight o
  sub-owed c (joinS j g x ib)        p o = Order.flight o
