{-# OPTIONS --guardedness #-}

-- WHAT EVERY FRAME ABOVE A HOLE KEEPS OF ITS POSITIONS, the hole read as
-- a run: each ancestor's `adequacy.Engine.Keys.Here` with the run in its
-- child's place, frame by frame as `adequacy.Engine.Meaning.up` reads the
-- hole, and each sibling keyed (`Above`).  The whole tree's ghost has
-- already dropped an event in flight and not yet begun a pending
-- subscription; the hole's run (`Meaning.hole`) carries both, so a frame a
-- rise rewrites finds here what it owes the event (`Flight`).
--
-- A takeWhile failing a value ends one past it: the frames above saw the
-- failing value's run end there (`take-excl`, `take-incl`), and the end is
-- headed and ahead of what the source leaves running because the value
-- was (`take-here`).
module adequacy.Engine.Above where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; _ʳ++_; [_]; reverse)
open import Data.List.Properties using (++-assoc; ++-identityʳ; ʳ++-defn)
open import Data.List.Relation.Unary.All using () renaming (_∷_ to _∷ᴬ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong; trans)
open import Relation.Nullary using (¬_)

open import Tree using (Obs)
open import denotation.MonotonicList.Events using (Events; Events∞; Pos; Tail; Timeline; out; end; ix; last; _<ᵖ_; <ᵖ-split; <ᵖ-apart; _∪_)
open import denotation.MonotonicList using (MonotonicList; taking)
open import denotation.Unfold using (Node; NEnv; stateᴺ; cutᴺ; states; restsᶜ; outerᴺ; endingᶜ; takeWhileᶜ; restᶜ)
open import operation.PureObservable using (module Machine)
open Machine using (St; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS; Ev; nx; cp; Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody; plug; CS; Conf; ⟨_,_,_,_⟩; free; cpAt; cutAt; overAt; _⊕_)
open import adequacy.Engine.Meaning using (_≋_; ≋-by; ≋-out; mapped; scanned; switched; taking∞; took; rested; outerFrame; lanesFrame; srcFrame; bodyFrame;
  lane; lanesL; liveL; deadL; deadOne; holeL; holeT; tailsOn; poolG; poolT; outerT; outerG; laneRuns; poolRuns; gh; envAt; hole; flagOf; risen; endingAt)
  renaming (outerOf to outerOfᴹ)
open import adequacy.Engine.Keys using (Shape; Shape′; TakeAt; FlatAt; LaneKeys; _∷ᴷ_; ConnAt; Keyed; KeyedL; Keys; srcIn)
open import adequacy.Placed.Order using (Headed; Disjoint; Ext; Owned; Prefix; every; everyT-mono; ext; owned-ext; prefix-++)
open import adequacy.Placed.Keys using (ix-mark; last-mark; prefix-refl; prefix-plus; prefix-lane; tagged-mark)
open import adequacy.Placed.Burst using (owned-drop; freshᴿ)
open import adequacy.Placed.Trail using (trail; spread)

open Events∞

------------------------------------------------------------------------
-- The frames above a hole

-- A merge's outer, as its lanes' generator reads it, the hole its run:
-- running, else done.
outerAt : ∀ {Γ A C} → Bool → (A → Obs Timeline Γ C) → NEnv Γ → Events∞ A → Maybe (Events∞ (MonotonicList C))
outerAt false g ρ h = just (outerOfᴹ (lane g) ρ h)
outerAt true  g ρ h = nothing

-- What a merge's pool leaves running, the hole its outer: done, it
-- joins the pool.
poolAt : ∀ {Γ A B} → Bool → Events∞ A → List (Node Γ B) → NEnv Γ → Tail
poolAt false h ds ρ = poolT ds ρ
poolAt true  h ds ρ = cut h ∪ poolT ds ρ

-- What a connect's source, the hole, feeds its body: its run, else, once
-- closed, its end; and what it runs as: itself, else its rest.
fedRun : ∀ {X} → Bool → Pos → Events∞ X → Events X
fedRun false e h = force h
fedRun true  e h = end e

srcRunning : ∀ {X} → Bool → Events∞ X → Events∞ X
srcRunning false h = h
srcRunning {X} true h = rested {B = X} h

-- Every frame above the hole keeping its own, its siblings keyed and a
-- connect's source in shape, the hole's run `h` in its child's place.
Above : ∀ {R Γ A} → Ctx R Γ A → Bool → Events∞ A → Set
Above top                               f h = ⊤
Above (inMap g c)                       f h = Above c true (mapped g h)
Above (inScan g z c)                    f h = Above c true (scanned g z h)
Above (inCut l a c)                     f h = Above c true (switched l h)
Above (inLn b c)                        f h = Above c b h
Above (inTake i q w c)                  f h = TakeAt w h × Above c true (taking∞ i q w h)
Above (inOuter op g d n q ls c)         f h =
  (FlatAt (envAt c) (outerAt d g (envAt c) h) (states (lanesL ls) (envAt c)) (poolAt d h (deadL ls) (envAt c)) × KeyedL ls (envAt c))
  × Above c true (outerFrame op (lane g) d q (lanesL ls) (deadL ls) (envAt c) h)
Above (inLanes op g d n q o pre post c) f h =
  (FlatAt (envAt c) (outerᴺ (lane g) (outerG d (gh o)) (envAt c)) (laneRuns (reverse pre) post f (envAt c) h)
          (outerT d (gh o) (envAt c) (poolRuns (reverse pre) post f (envAt c) h))
   × Keyed o (envAt c) × KeyedL pre (envAt c) × KeyedL post (envAt c))
  × Above c true (lanesFrame op (lane g) d q (gh o) (reverse pre) post f (envAt c) h)
Above (inSrc k b c)                     f h =
  (ConnAt k (stateᴺ (gh b) (fedRun (CS.closed k) (CS.endAt k) h ∷ᴬ envAt c)) (srcRunning (CS.closed k) h) (envAt c)
   × Keyed b (fedRun (CS.closed k) (CS.endAt k) h ∷ᴬ envAt c))
  × Above c true (srcFrame k (gh b) (envAt c) h)
Above (inBody k o c)                    f h =
  (ConnAt k h (srcIn k o (envAt c)) (envAt c) × Keyed o (envAt c) × Shape (srcIn k o (envAt c)))
  × Above c true (bodyFrame k o (envAt c) h)

-- A configuration's hole's run in shape, and every frame above it keeping
-- its own of that run.
Flight : ∀ {R} → Conf R → Set
Flight ⟨ c , s , m , p ⟩ = Shape (hole c s m p) × Above c (flagOf s) (hole c s m p)

postulate
  -- THE KEYS KEPT: runs alike at every depth are kept alike by every frame
  -- above them.
  above-≋ : ∀ {R Γ A} (c : Ctx R Γ A) f {h h′ : Events∞ A} → h ≋ h′ → Above c f h → Above c f h′
  -- Every frame above a hole keeping its own of the run the hole's ghost
  -- gives it, and the hole its own: the whole tree keyed.
  keys-above : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) → Above c (flagOf s) (stateᴺ (gh s) (envAt c)) → Keyed s (envAt c) → Keys (plug c s)

-- A position not before a disjoint one: one past its last child is
-- after it, apart from it, and no prefix of it.
past-last : ∀ p k → k <ᵖ p ≡ false → Disjoint p k → (p ++ [ last ]) <ᵖ k ≡ true × Disjoint ((p ++ [ last ]) ++ [ ix 1 ]) k × ¬ Ext (p ++ [ last ]) k
past-last p k h (np , nk) = goal1 , (goal2-fwd , goal2-bwd) , goal3
  where
    p<k : p <ᵖ k ≡ true
    p<k with <ᵖ-split p k h
    ... | inj₁ lt   = lt
    ... | inj₂ refl = ⊥-elim (np (inj₁ (prefix-refl p)))
    ne : ∀ ys → k ≡ p ++ ys → ⊥
    ne ys e = np (inj₁ (subst (Prefix p) (sym e) (prefix-++ p ys)))
    goal1 : (p ++ [ last ]) <ᵖ k ≡ true
    goal1 = <ᵖ-apart p k [ last ] p<k ne
    goal3 : ¬ Ext (p ++ [ last ]) k
    goal3 (ext l ls) = np (owned-drop p [ last ] _ (owned-ext (ext l ls)))
    goal2-fwd : ¬ Owned ((p ++ [ last ]) ++ [ ix 1 ]) k
    goal2-fwd o = np (owned-drop p [ last ] k (owned-drop (p ++ [ last ]) [ ix 1 ] k o))
    goal2-bwd : ¬ Owned k ((p ++ [ last ]) ++ [ ix 1 ])
    goal2-bwd (inj₂ t) = nk (inj₂ (tagged-mark k p last last-mark (tagged-mark k (p ++ [ last ]) (ix 1) (ix-mark 1) t)))
    goal2-bwd (inj₁ q) with prefix-plus k ((p ++ [ last ]) ++ [ ix 1 ]) q
    ... | inj₁ refl = ne (last ∷ ix 1 ∷ []) (++-assoc p [ last ] [ ix 1 ])
    ... | inj₂ q⁺   with prefix-plus k (p ++ [ last ]) (prefix-lane k (p ++ [ last ]) (ix 1) q⁺)
    ...   | inj₁ refl = ne (last ∷ []) refl
    ...   | inj₂ q⁺'  = nk (inj₁ (prefix-lane k p last q⁺'))

------------------------------------------------------------------------
-- A takeWhile failing a value

headed-last : ∀ p → Headed p → Headed (p ++ [ last ])
headed-last (ix _ ∷ _) h = tt

-- What a failing value's run leaves running trails the end one past it.
take-here : ∀ {A} p a (h : Events∞ A) → Shape′ (out p a h) (cut h) → TakeAt (cpAt p) h
take-here p a h ((_ , hd , _) , tr) =
  headed-last p (proj₁ (every hd)) , everyT-mono (λ k t → past-last p k (proj₁ t) (proj₂ t)) (cut h) (proj₁ (proj₂ (trail tr)))

-- A takeWhile's value, taken: the value as the node runs on; failed,
-- taken under its own position before the end one past it, else not.
take-true : ∀ {Γ A} i (q : A → Bool) (n : Node Γ A) (ρ : NEnv Γ) a p → q a ≡ true
          → took i q (risen n ρ (nx a) p) ≋ risen (takeWhileᶜ i q n) ρ (nx a) p
take-true i q n ρ a p e = ≋-out (cong (λ b → taking i q p a b (stateᴺ n ρ)) e) refl refl refl refl

take-incl : ∀ {Γ A} (q : A → Bool) (n : Node Γ A) (ρ : NEnv Γ) a p → q a ≡ false
          → took true q (risen n ρ (nx a) p) ≋ risen (endingᶜ (p ⊕ [ last ]) n) ρ (nx a) (p ⊕ [ ix 0 ])
take-incl q n ρ a p e = ≋-out (cong (λ b → taking true q p a b (stateᴺ n ρ)) e) refl refl refl refl

take-excl : ∀ {Γ A} (q : A → Bool) (n : Node Γ A) (ρ : NEnv Γ) a p → q a ≡ false
          → took false q (risen n ρ (nx a) p) ≋ stateᴺ (endingᶜ (p ⊕ [ last ]) n) ρ
take-excl q n ρ a p e = ≋-by (cong (λ b → taking false q p a b (stateᴺ n ρ)) e) refl

------------------------------------------------------------------------
-- A frame already over

-- What a node leaves running, read past a value rising out of it, is
-- what it leaves running.
rested-risen : ∀ {Γ A B} (n : Node Γ A) (ρ : NEnv Γ) e p → rested {B = B} (risen n ρ e p) ≋ stateᴺ (restᶜ n) ρ
rested-risen n ρ (nx a) p = ≋-by refl refl
rested-risen n ρ cp     p = ≋-by refl refl

ending-risen : ∀ {Γ A} q (n : Node Γ A) (ρ : NEnv Γ) (e : Ev A) p → endingAt q (risen n ρ e p) ≋ stateᴺ (endingᶜ q n) ρ
ending-risen q n ρ (nx a) p = ≋-by refl refl
ending-risen q n ρ cp     p = ≋-by refl refl

-- A takeWhile's own reads only what its source leaves running.
takeAt-risen : ∀ {Γ A} w (n : Node Γ A) (ρ : NEnv Γ) e p → TakeAt w (risen n ρ e p) → TakeAt w (stateᴺ n ρ)
takeAt-risen (cpAt k)   n ρ (nx a) p t = t
takeAt-risen (cpAt k)   n ρ cp     p t = t
takeAt-risen free       n ρ e      p t = tt
takeAt-risen (cutAt k)  n ρ e      p t = tt
takeAt-risen (overAt k) n ρ e      p t = tt

------------------------------------------------------------------------
-- A body's value passed on

-- A connect keeps its own of its body's run past the value it passes on.
conn-drop : ∀ {Γ Δ X B} k (n : Node Δ B) (ρ′ : NEnv Δ) b p {σ : Events∞ X} {ρ : NEnv Γ}
          → ConnAt k (risen n ρ′ (nx b) p) σ ρ → ConnAt k (stateᴺ n ρ′) σ ρ
conn-drop k n ρ′ b p c = record
  { mark = mark ; hm = hm ; at = at
  ; kb = proj₂ (every (proj₁ kb)) ; kr = proj₂ (every (proj₁ kr))
  ; fr = proj₂ (freshᴿ fr) ; cue = cue ; ks = ks ; rs = rs
  ; ub = proj₂ (every (proj₁ ub)) ; sub = sub ; ends = ends }
  where open ConnAt c

------------------------------------------------------------------------
-- A merge's lanes, its hole among them

states-++ : ∀ {Γ A} (xs ys : List (Node Γ A)) (ρ : NEnv Γ) → states (xs ++ ys) ρ ≡ states xs ρ ++ states ys ρ
states-++ []       ys ρ = refl
states-++ (x ∷ xs) ys ρ = cong (stateᴺ x ρ ∷_) (states-++ xs ys ρ)

lanesL-++ : ∀ {Γ B} (xs ys : List (St Γ B)) → lanesL (xs ++ ys) ≡ lanesL ys ++ lanesL xs
lanesL-++ []       ys = sym (++-identityʳ (lanesL ys))
lanesL-++ (x ∷ xs) ys = trans (cong (_++ liveL x) (lanesL-++ xs ys)) (++-assoc (lanesL ys) (lanesL xs) (liveL x))

deadL-++ : ∀ {Γ B} (xs ys : List (St Γ B)) → deadL (xs ++ ys) ≡ deadL xs ++ deadL ys
deadL-++ []       ys = refl
deadL-++ (x ∷ xs) ys = trans (cong (deadOne x ++_) (deadL-++ xs ys)) (sym (++-assoc (deadOne x) (deadL xs) (deadL ys)))

rests-++ : ∀ {Γ B} (xs ys : List (Node Γ B)) (ρ : NEnv Γ) → cutᴺ (restsᶜ {B = B} (xs ++ ys)) ρ ≡ tailsOn xs ρ (cutᴺ (restsᶜ {B = B} ys) ρ)
rests-++ []       ys ρ = refl
rests-++ (x ∷ xs) ys ρ = cong (cutᴺ x ρ ∪_) (rests-++ xs ys ρ)

live-hole : ∀ {Γ B} (s : St Γ B) (ρ : NEnv Γ) → states (liveL s) ρ ≡ holeL (flagOf s) (stateᴺ (gh s) ρ)
live-hole (pend o)                ρ = refl
live-hole (coldS b l)             ρ = refl
live-hole (ofS i p xs)            ρ = refl
live-hole doneS                   ρ = refl
live-hole (mapS f s)              ρ = refl
live-hole (scanS f z s)           ρ = refl
live-hole (cutS l a s)            ρ = refl
live-hole (lnS true s)            ρ = refl
live-hole (lnS false s)           ρ = refl
live-hole (takeS i q w s)         ρ = refl
live-hole (flatS op f d n q o ls) ρ = refl
live-hole (connS k o b)           ρ = refl
live-hole (joinS j g x ib)        ρ = refl

dead-hole : ∀ {Γ B} (s : St Γ B) (ρ : NEnv Γ) t → tailsOn (deadOne s) ρ t ≡ holeT (flagOf s) (stateᴺ (gh s) ρ) ∪ t
dead-hole (pend o)                ρ t = refl
dead-hole (coldS b l)             ρ t = refl
dead-hole (ofS i p xs)            ρ t = refl
dead-hole doneS                   ρ t = refl
dead-hole (mapS f s)              ρ t = refl
dead-hole (scanS f z s)           ρ t = refl
dead-hole (cutS l a s)            ρ t = refl
dead-hole (lnS true s)            ρ t = refl
dead-hole (lnS false s)           ρ t = refl
dead-hole (takeS i q w s)         ρ t = refl
dead-hole (flatS op f d n q o ls) ρ t = refl
dead-hole (connS k o b)           ρ t = refl
dead-hole (joinS j g x ib)        ρ t = refl

lanes-runs : ∀ {Γ B} (pre : List (St Γ B)) s post (ρ : NEnv Γ) → states (lanesL (pre ++ s ∷ post)) ρ ≡ laneRuns pre post (flagOf s) ρ (stateᴺ (gh s) ρ)
lanes-runs pre s post ρ =
  trans (cong (λ l → states l ρ) (lanesL-++ pre (s ∷ post)))
  (trans (states-++ (lanesL post ++ liveL s) (lanesL pre) ρ)
  (trans (cong (_++ states (lanesL pre) ρ) (states-++ (lanesL post) (liveL s) ρ))
  (trans (++-assoc (states (lanesL post) ρ) (states (liveL s) ρ) (states (lanesL pre) ρ))
  (cong (λ z → states (lanesL post) ρ ++ (z ++ states (lanesL pre) ρ)) (live-hole s ρ)))))

pool-runs : ∀ {Γ B} (pre : List (St Γ B)) s post (ρ : NEnv Γ) → cutᴺ (restsᶜ {B = B} (deadL (pre ++ s ∷ post))) ρ ≡ poolRuns pre post (flagOf s) ρ (stateᴺ (gh s) ρ)
pool-runs {B = B} pre s post ρ =
  trans (cong (λ l → cutᴺ (restsᶜ {B = B} l) ρ) (deadL-++ pre (s ∷ post)))
  (trans (rests-++ (deadL pre) (deadOne s ++ deadL post) ρ)
  (trans (cong (tailsOn (deadL pre) ρ) (rests-++ (deadOne s) (deadL post) ρ))
  (cong (tailsOn (deadL pre) ρ) (dead-hole s ρ _))))

-- A lane's context keeps the lanes before it nearest first; the meaning
-- reads them in order.
toʳ : ∀ {ℓ Γ B} (P : List (St Γ B) → Set ℓ) pre {s : St Γ B} {post} → P (reverse pre ++ s ∷ post) → P (pre ʳ++ s ∷ post)
toʳ P pre = subst P (sym (ʳ++-defn pre))

-- A lane in the list is one of its flatMap's runs, between the lanes
-- after it and before it; its pool, the lanes ended around it.
lanes-L : ∀ {Γ B} pre (s : St Γ B) post (ρ : NEnv Γ) → flagOf s ≡ true
        → states (lanesL (pre ++ s ∷ post)) ρ ≡ states (lanesL post) ρ ++ stateᴺ (gh s) ρ ∷ states (lanesL pre) ρ
lanes-L pre s post ρ fl = trans (lanes-runs pre s post ρ) (cong (λ x → laneRuns pre post x ρ (stateᴺ (gh s) ρ)) fl)

lanes-P : ∀ {Γ A B} d (o : St Γ A) pre (s : St Γ B) post (ρ : NEnv Γ) → flagOf s ≡ true
        → outerT d (gh o) ρ (poolRuns pre post true ρ (stateᴺ (gh s) ρ)) ≡ cutᴺ (poolG d (gh o) (deadL (pre ++ s ∷ post))) ρ
lanes-P false o pre s post ρ fl = sym (trans (pool-runs pre s post ρ) (cong (λ x → poolRuns pre post x ρ (stateᴺ (gh s) ρ)) fl))
lanes-P true  o pre s post ρ fl = cong (cutᴺ (gh o) ρ ∪_) (lanes-P false o pre s post ρ fl)

-- A merge keeps its own of a lane's run past the value it passes on.
lanes-drop : ∀ {p Δ B} (Ls : List (Events∞ B)) (n : Node Δ B) (ρ′ : NEnv Δ) b q {Rs rs}
           → LaneKeys p (Ls ++ risen n ρ′ (nx b) q ∷ Rs) rs → LaneKeys p (Ls ++ stateᴺ n ρ′ ∷ Rs) rs
lanes-drop []       n ρ′ b q ((u , ok , sp) ∷ᴷ ks) = (proj₂ (every (proj₁ u)) , ok , proj₂ (spread sp)) ∷ᴷ ks
lanes-drop (L ∷ Ls) n ρ′ b q (k ∷ᴷ ks)            = k ∷ᴷ lanes-drop Ls n ρ′ b q ks

flat-drop : ∀ {Γ Δ B} {ρ : NEnv Γ} {o} (Ls : List (Events∞ B)) (n : Node Δ B) (ρ′ : NEnv Δ) b q {Rs t}
          → FlatAt ρ o (Ls ++ risen n ρ′ (nx b) q ∷ Rs) t → FlatAt ρ o (Ls ++ stateᴺ n ρ′ ∷ Rs) t
flat-drop Ls n ρ′ b q (p , hp , al , rs , lk , ks) = p , hp , al , rs , lanes-drop Ls n ρ′ b q lk , ks

-- Lanes keyed nearest first, and those after them, keyed in order.
keyedL-ʳ++ : ∀ {Γ A} (xs : List (St Γ A)) {ys} {ρ : NEnv Γ} → KeyedL xs ρ → KeyedL ys ρ → KeyedL (xs ʳ++ ys) ρ
keyedL-ʳ++ []       _          k = k
keyedL-ʳ++ (x ∷ xs) (kx , kxs) k = keyedL-ʳ++ xs kxs (kx , k)
