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
open import Data.List using (List; []; _∷_; _++_; _ʳ++_; [_]; null; reverse; length)
open import Data.List.Properties using (ʳ++-defn)
import Data.List as L
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.List.Relation.Unary.All.Properties using (++⁻ʳ) renaming (++⁺ to All++⁺)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (zero; suc; pred; _≡ᵇ_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import Tree using (Obs; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.MonotonicList.Events using (Events; Events∞; Timeline; out; skip; end; hush; idle; ix; _∪_)
import denotation.MonotonicList as M′
open import denotation.MonotonicList using (Agreeᵀ; Agree; agree-refl; agreeᵀ-refl; agreeᵀ-trans)
open import denotation.NonExpansive using (_,ˢ_; ∪-ne)
open import denotation.Unfold using (NEnv; Node; Source; live; meaning; connectᶜ; stateᴺ; cutᴺ; states; outerᴺ)
open import denotation.Denote using (flatOp)
open import adequacy.Engine.Meaning using (_≋_; ≋-by; ≋-out; envAt; gh; srcG; srcRun; srcState; risen; lanesFrame; lane; lanesL; outerG; outerT;
  poolRuns; laneRuns; laneᴹ; flagOf; tailsOn; holeT; poolT; deadL; deadOne)
open import adequacy.Engine.Union using (∪-idleᵀ; ∪-assocᵀ; ∪-commᵀ)
open import adequacy.Engine.Keys using (Shape; Shape′; module ConnAt)
open import adequacy.Engine.Trails using (beside-go; module FlatShape; gen-queue; held-of)
open import adequacy.Engine.Beside using (burst-hushed)
open import adequacy.Engine.Race using (NotBefore; First; go-rise; cuts-swap)
open import adequacy.Engine.Ahead using (shown)
open import adequacy.Engine.Above using (Above; Flight; above-≋; take-true; take-incl; toʳ; lanes-L; lanes-P; rests-++; dead-hole; lanes-runs; pool-runs)
open import adequacy.Engine.Head using (Frag; Lane)
open import adequacy.Engine.Pick using (Order; module Order; frag-flat; frag-parts; lanes-ʳsplit)
open import adequacy.Placed.Order using (Ordered; Steady; Every; EveryT; Headed; Atop; Past; Disjoint; ordered; steady; every;
  ordered-map; ordered-scan; steady-map; steady-scan)
open import adequacy.Placed.Keys using (every-map; every-scan; everyT-≈)
open import adequacy.Placed.Trail using (Trail; trail; trailᶠ; trail-map; trail-scan; trail-≈; SortedT; sortedT-idle; sortedT-∪)
open import adequacy.Placed.Rising using (module Reach; headedRules; ordered-take; steady-take)
open import adequacy.Placed.FlatAfter using (trail-take)
open import operation.PureObservable using (module Machine; module Driver)
open Machine using (St; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS; Ctx; top; inMap; inScan; inCut;
  inLn; inTake; inOuter; inLanes; inSrc; inBody; Conf; ⟨_,_,_,_⟩; subscribing; absorbed; rising; nx; cp; free; cpAt; cutAt; overAt;
  CS; cs; closed; attAt; start; plug; rise; begin; admit; dequeue; settle; ended; alive; _⊕_)
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

-- The lanes a flatMap counts, the lanes its meaning holds.
states-length : ∀ {Γ B} (ls : List (Node Γ B)) (ρ : NEnv Γ) → length (states ls ρ) ≡ length ls
states-length []       ρ = refl
states-length (l ∷ ls) ρ = cong suc (states-length ls ρ)

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
    -- THE FLIGHT KEPT: a value or an end rising out of a frame that
    -- rewrites its node, or a subscribe beginning a former, leaves its
    -- hole's run in shape and every frame above keeping its share.
    rise-admit-flight : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q ls (s : St Γ A) a p
                      → Order ⟨ inOuter op f d n q ls c , s , rising (nx a) , p ⟩ → NextOwed (took (admit c op f d n q s ls a p))
    rise-outer-end-flight : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q ls (s : St Γ A) p
                          → Order ⟨ inOuter op f d n q ls c , s , rising cp , p ⟩ → Owed ⟨ c , flatS op f true n q s ls , settle true n (null q) , p ⟩
    -- A lane's end under an open observer, a value queued: its lane
    -- begins, past the skip the merge's run drops just after the end.
    lane-begin-flight : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n a q (o : St Γ A) pre post (s : St Γ B) p
                      → Order ⟨ inLanes op f d n (a ∷ q) o pre post c , s , rising cp , p ⟩ → alive s ≡ true → closed c ≡ false
                      → Flight ⟨ inCut true (attAt (p ⊕ [ ix 1 ])) (inLn true (inLanes op f d (suc (pred n)) q o (reverse (pre ʳ++ ended s ∷ post)) [] c))
                               , pend (f a) , subscribing , p ⊕ [ ix 1 ] ⟩
    -- THE CLOSED LANE: a lane's end under a closed observer.
    rise-lane-end-shut : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) pre post (s : St Γ B) p
                       → Order ⟨ inLanes op f d n q o pre post c , s , rising cp , p ⟩ → alive s ≡ true → closed c ≡ true
                       → Owed (dequeue c op f d (pred n) q o (pre ʳ++ ended s ∷ post) p)
    -- THE CLOSED LANE: a body's end under a closed observer, where the
    -- race need not have read its source's head.
    rise-body-end-shut : ∀ {Γ X B} (c : Ctx R Γ B) k (o : St Γ X) (s : St (X ∷ Γ) B) p → Order ⟨ inBody k o c , s , rising cp , p ⟩
                       → closed c ≡ true → Flight ⟨ c , connS (record k { owedAt = just p }) o s , rising cp , p ⟩
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

  -- A body's value rises out of its connect only while the connect is
  -- live, its source no earlier: the connect's run shows it first.
  rise-body-flight : ∀ {Γ X B} (c : Ctx R Γ B) k (o : St Γ X) (s : St (X ∷ Γ) B) b p → Order ⟨ inBody k o c , s , rising (nx b) , p ⟩
                   → Flight ⟨ c , connS k o s , rising (nx b) , p ⟩
  rise-body-flight c (cs cl true sa ba as nothing r en) o s b p od =
    subst (Shape′ (out p b (stateᴺ (gh (connS k o s)) ρ))) (sym (proj₂ cr))
      (shape-out p b ft ct (subst (λ x → Shape′ x (M′.burstOn r σ ∪ cut h)) (proj₁ (proj₂ so)) bs))
    , above-≋ c true (≋-out (proj₁ (proj₂ so)) refl ft ct (sym (proj₂ cr))) (proj₂ (proj₂ (Order.flight od)))
    where
      k  = cs cl true sa ba as nothing r en
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
  rise-lane-end-flight c op f d n q o pre post s p od al with closed c in ce
  ... | true  = rise-lane-end-shut c op f d n q o pre post s p od al ce
  ... | false = rise-lane-end-open c op f d n q o pre post s p od al ce

  -- A body's end ends its live connect, its source no earlier under an
  -- open observer: the connect's run ends there.
  rise-body-end-flight : ∀ {Γ X B} (c : Ctx R Γ B) k (o : St Γ X) (s : St (X ∷ Γ) B) p → Order ⟨ inBody k o c , s , rising cp , p ⟩
                       → Flight ⟨ c , connS (record k { owedAt = just p }) o s , rising cp , p ⟩
  rise-body-end-flight c (cs cl true sa ba as nothing r en) o s p od with closed c in ce
  ... | true  = rise-body-end-shut c (cs cl true sa ba as nothing r en) o s p od ce
  ... | false =
    subst (Shape′ (end p)) (sym (proj₂ cr)) (subst (λ x → Shape′ x (M′.burstOn r σ ∪ cut h)) se bs)
    , above-≋ c true (≋-by se (sym (proj₂ cr))) (proj₂ (proj₂ (Order.flight od)))
    where
      k  = cs cl true sa ba as nothing r en
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
  rise-owed (inOuter op f d n q ls c)         s cp     p o = rise-outer-end-flight c op f d n q ls s p o
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
