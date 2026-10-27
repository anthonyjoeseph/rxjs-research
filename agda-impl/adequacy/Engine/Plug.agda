{-# OPTIONS --guardedness #-}

-- EACH FRAME IS THE NODE IT IS A HOLE OF: a frame read over its hole's
-- state is the state of the node it frames (`take-plug`, `outer-plug`,
-- `lanes-plug`, `body-plug`, `src-plugⁿ`).  So what the whole tree keeps
-- of its positions (`adequacy.Engine.Keys.Keys`) is what every frame
-- above a settled node keeps of that node's run (`flight-held`), read
-- frame by frame off the node each frame plugs.
--
-- A source still to subscribe under a body already subscribed is the
-- one frame its run does not plug: the connect's state subscribes the
-- source where the hole reads it idle.  A well-formed context holds no
-- such frame (`adequacy.Engine.Fold.WfC`), so both walks read it.
module adequacy.Engine.Plug where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; _ʳ++_; reverse)
open import Data.List.Properties using (ʳ++-defn)
open import Data.List.Relation.Unary.All using () renaming (_∷_ to _∷ᴬ_)
open import Data.List.Relation.Unary.All.Properties using (++⁻ˡ)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; subst₂; sym; cong; cong₂)

open import Tree using (Obs)
open import denotation.MonotonicList.Events using (Events∞; Timeline; _∪_)
open import denotation.MonotonicList using (agreeᵀ-refl; agree-refl)
import denotation.MonotonicList as M′
open import denotation.NonExpansive using (_,ˢ_; liveᴼ; go-ne; mapᴱ-neᴹ; ∪-ne; burstOn-ne; beside-ne)
open import denotation.Unfold using (Node; NEnv; stateᴺ; cutᴺ; states; restsᶜ; outerᴺ; outer∞; restᶜ; connectᶜ)
open import denotation.Denote using (flatOp)
import Data.List
open import operation.PureObservable using (module Machine)
open Machine using (St; CS; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
  Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody; plug; cs; ⟨_,_,_,_⟩; absorbed;
  free; cpAt; cutAt; overAt)
open import adequacy.Engine.Meaning using (_≋_; ≋-by; ≋-sym; ≋-tr; ≋-trans; same; doneE-ne; doneG; doneE; envAt; flagOf; gh; lane; lanesL; deadL;
  laneᴹ; lanes-refl; queue-refl; ≈-refl; lanesFrame; outerFrame; bodyFrame; srcFrame; connSrc; outerOf; srcG; srcRun; taken; taking∞;
  poolRuns; outerT; laneRuns; poolG; outerG; rested; bodyG)
open import adequacy.Engine.Keys using (Held; Keys; Keyed; KeyedL; ConnAt; FlatAt; here-at; keyed-at; keyedL-ʳ++)
open import adequacy.Engine.Above using (Above; Flight; above-≋; lanes-runs; pool-runs; toʳ) renaming (keyedL-ʳ++ to keyedL-join)
open import adequacy.Engine.Fold using (WfC)
open import adequacy.Engine.Trails using (conn-shut; shape-st; shape-src; envAt-sorted; lanes-shape; lanes-held)

------------------------------------------------------------------------
-- Each frame is the node it is a hole of

take-plug : ∀ {Γ A} i (q : A → Bool) w (n : Node Γ A) (ρ : NEnv Γ) → taking∞ i q w (stateᴺ n ρ) ≋ stateᴺ (taken i q w n) ρ
take-plug i q free       n ρ = ≋-by refl refl
take-plug i q (cpAt p)   n ρ = ≋-by refl refl
take-plug i q (cutAt p)  n ρ = ≋-by refl refl
take-plug i q (overAt p) n ρ = ≋-by refl refl

outer-plug : ∀ {Γ A B} op (f : A → Obs Timeline Γ B) d m q ls (o : St Γ A) (ρ : NEnv Γ)
           → outerFrame op (lane f) d q (lanesL ls) (deadL ls) ρ (stateᴺ (gh o) ρ) ≋ stateᴺ (gh (flatS op f d m q o ls)) ρ
outer-plug op f true  m q ls o ρ = ≋-by refl refl
outer-plug {B = B} op f false m q ls o ρ k = agreeᵀ-refl k _ ,ˢ
  go-ne (flatOp op) (liveᴼ {e = outerOf (lane f) ρ (stateᴺ (gh o) ρ)} {outer∞ (lane f) (gh o) ρ} (agreeᵀ-refl k _) (mapᴱ-neᴹ (λ a → ≈-refl _) (agree-refl k _)))
    (lanes-refl k (states (lanesL ls) ρ)) (queue-refl k (Data.List.map (laneᴹ (lane f) ρ) q)) (agreeᵀ-refl k (cutᴺ (restsᶜ {B = B} (deadL ls)) ρ))

lanes-plug : ∀ {Γ A B} op (f : A → Obs Timeline Γ B) d m q (o : St Γ A) pre post (s : St Γ B) (ρ : NEnv Γ)
           → lanesFrame op (lane f) d q (gh o) pre post (flagOf s) ρ (stateᴺ (gh s) ρ) ≋ stateᴺ (gh (flatS op f d m q o (pre ++ s ∷ post))) ρ
lanes-plug op f d m q o pre post s ρ =
  ≋-by (cong₂ (λ ls t → M′.go (flatOp op) (outerᴺ (lane f) (outerG d (gh o)) ρ) ls (Data.List.map (laneᴹ (lane f) ρ) q) t) (sym (lanes-runs pre s post ρ)) (pool d))
       (cong₂ (M′.whole (outerᴺ (lane f) (outerG d (gh o)) ρ)) (sym (lanes-runs pre s post ρ)) (pool d))
  where
    pool : ∀ d → outerT d (gh o) ρ (poolRuns pre post (flagOf s) ρ (stateᴺ (gh s) ρ)) ≡ cutᴺ (poolG d (gh o) (deadL (pre ++ s ∷ post))) ρ
    pool false = sym (pool-runs pre s post ρ)
    pool true  = cong (cutᴺ (gh o) ρ ∪_) (sym (pool-runs pre s post ρ))

lanes-plugʳ : ∀ {Γ A B} op (f : A → Obs Timeline Γ B) d m q (o : St Γ A) pre post (s : St Γ B) (ρ : NEnv Γ)
            → lanesFrame op (lane f) d q (gh o) (reverse pre) post (flagOf s) ρ (stateᴺ (gh s) ρ) ≋ stateᴺ (gh (flatS op f d m q o (pre ʳ++ s ∷ post))) ρ
lanes-plugʳ op f d m q o pre post s ρ =
  toʳ (λ ls → lanesFrame op (lane f) d q (gh o) (reverse pre) post (flagOf s) ρ (stateᴺ (gh s) ρ) ≋ stateᴺ (gh (flatS op f d m q o ls)) ρ) pre
    (lanes-plug op f d m q o (reverse pre) post s ρ)

done-plug : ∀ {Γ A} ow sl {h : Events∞ A} (n : Node Γ A) (ρ : NEnv Γ) → h ≋ stateᴺ n ρ → doneE ow sl h ≋ stateᴺ (doneG ow sl n) ρ
done-plug (just w) l     n ρ x = ≋-tr (λ k → doneE-ne (just w) l (x k)) refl refl
done-plug nothing  false n ρ x = ≋-tr (λ k → doneE-ne nothing false (x k)) refl refl
done-plug nothing  true  n ρ x = x

body-plug : ∀ {Γ X B} k (o : St Γ X) (s : St (X ∷ Γ) B) (ρ : NEnv Γ)
          → bodyFrame k o ρ (stateᴺ (gh s) (srcRun (srcG k o) ρ ∷ᴬ ρ)) ≋ stateᴺ (gh (connS k o s)) ρ
body-plug (cs false sl sa (just p) as ow r e) o s ρ = done-plug ow sl _ ρ (≋-by refl refl)
body-plug (cs true sl sa (just p) as ow r e)  o s ρ = done-plug ow sl _ ρ (≋-by refl refl)
body-plug (cs false sl sa nothing as ow r e) o s ρ = done-plug ow sl _ ρ (≋-by refl refl)
body-plug (cs true sl sa nothing as ow r e)  o s ρ = done-plug ow sl _ ρ (≋-trans (≋-by refl refl) (conn-shut r e (gh s) (restᶜ (gh o)) ρ))


-- A source subscribed when its body was, running or ended, read through
-- its connect.
conn-plugⁿ : ∀ {Γ X B} cl sl sa as ow r e (b : St (X ∷ Γ) B) (s : St Γ X) (ρ : NEnv Γ)
           → connSrc cl r e (gh b) ρ (stateᴺ (gh s) ρ) ≋ stateᴺ (connectᶜ r (bodyG (cs cl sl sa nothing as ow r e) (gh b)) (srcG (cs cl sl sa nothing as ow r e) s)) ρ
conn-plugⁿ false sl sa as ow r e b s ρ = ≋-by refl refl
conn-plugⁿ {X = X} true sl sa as ow r e b s ρ =
  ≋-trans (λ k → ∪-ne (burstOn-ne r (R k)) (agreeᵀ-refl k _) ,ˢ beside-ne r (same k _) (R k)) (conn-shut r e (gh b) (restᶜ (gh s)) ρ)
  where
    R : rested {B = X} (stateᴺ (gh s) ρ) ≋ stateᴺ (restᶜ (gh s)) ρ
    R = ≋-by refl refl

src-plugⁿ : ∀ {Γ X B} cl sl sa as ow r e (b : St (X ∷ Γ) B) (s : St Γ X) (ρ : NEnv Γ)
          → srcFrame (cs cl sl sa nothing as ow r e) (gh b) ρ (stateᴺ (gh s) ρ) ≋ stateᴺ (gh (connS (cs cl sl sa nothing as ow r e) s b)) ρ
src-plugⁿ cl sl sa as ow r e b s ρ = done-plug ow sl _ ρ (conn-plugⁿ cl sl sa as ow r e b s ρ)

------------------------------------------------------------------------
-- What every frame above a settled node keeps of its run

-- The lanes passed, keyed.
keyedL-pre : ∀ {Γ A} (pre : List (St Γ A)) {ys} {ρ : NEnv Γ} → KeyedL (pre ʳ++ ys) ρ → KeyedL pre ρ
keyedL-pre []        k = tt
keyedL-pre (x ∷ pre) k = proj₁ (keyedL-ʳ++ pre k) , keyedL-pre pre k

-- A source run as its rest, keyed as its rest's state.
conn-rested : ∀ {Γ X B} k {β : Events∞ B} (n : Node Γ X) (ρ : NEnv Γ) → ConnAt k β (stateᴺ (restᶜ n) ρ) ρ → ConnAt k β (rested {B = X} (stateᴺ n ρ)) ρ
conn-rested k n ρ x = record { mark = mark ; hm = hm ; at = at ; kb = kb ; kr = kr ; fr = fr ; cue = cue ; ks = ks ; rs = rs ; ub = ub ; sub = sub ; ends = ends }
  where open ConnAt x

mutual
  above-held : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) → WfC c → Held (plug c s) → Above c (flagOf s) (stateᴺ (gh s) (envAt c))
  above-held top                               s v fs = tt
  above-held (inMap g c)                       s v fs = above-≋ c true (≋-by refl refl) (above-held c (mapS g s) v fs)
  above-held (inScan g z c)                    s v fs = above-≋ c true (≋-by refl refl) (above-held c (scanS g z s) v fs)
  above-held (inCut true a c)                  s v fs = above-held c (cutS true a s) v fs
  above-held (inCut false a c)                 s v fs = above-≋ c true (≋-by refl refl) (above-held c (cutS false a s) v fs)
  above-held (inLn b c)                        s v fs = above-held c (lnS b s) v fs
  above-held (inTake i q w c)                  s v fs =
    here-at c (takeS i q w s) fs , above-≋ c true (≋-sym (take-plug i q w (gh s) (envAt c))) (above-held c (takeS i q w s) v fs)
  above-held (inOuter op g true n q ls c)      s (_ , v) fs =
    (here-at c (flatS op g true n q s ls) fs , proj₂ (proj₂ (keyed-at c (flatS op g true n q s ls) (proj₂ fs))))
    , above-≋ c true (≋-sym (outer-plug op g true n q ls s (envAt c))) (above-held c (flatS op g true n q s ls) v fs)
  above-held (inOuter op g false n q ls c)     s (_ , v) fs =
    (here-at c (flatS op g false n q s ls) fs , proj₂ (proj₂ (keyed-at c (flatS op g false n q s ls) (proj₂ fs))))
    , above-≋ c true (≋-sym (outer-plug op g false n q ls s (envAt c))) (above-held c (flatS op g false n q s ls) v fs)
  above-held (inSrc k b c)                     s (e , _ , v) fs = src-above c k b s e fs (above-held c (connS k s b) v fs)
  above-held (inBody k o c)                    s (_ , _ , v) fs =
    (here-at c (connS k o s) fs , proj₁ (proj₂ (keyed-at c (connS k o s) (proj₂ fs))) , shape-src c k o s fs)
    , above-≋ c true (≋-sym (body-plug k o s (envAt c))) (above-held c (connS k o s) v fs)
  above-held (inLanes op g d n q o pre post c) s (_ , _ , _ , v) fs =
    (subst₂ (λ ls t → FlatAt′ ls t) L P (here-at c (flatS op g d n q o (pre ʳ++ s ∷ post)) fs)
     , proj₁ (proj₂ kd) , keyedL-pre pre (proj₂ (proj₂ kd)) , proj₂ (keyedL-ʳ++ pre (proj₂ (proj₂ kd)))
     , envAt-sorted c (flatS op g d n q o (pre ʳ++ s ∷ post)) fs
     , shape-st (inOuter op g d n q (pre ʳ++ s ∷ post) c) o fs
     , lanes-shape ρ (reverse pre) (++⁻ˡ (reverse pre) (lanes-held c op g d n q o [] (reverse pre ++ s ∷ post)
         (subst (λ ls → Held (plug c (flatS op g d n q o ls))) (ʳ++-defn pre) fs)))
     , lanes-shape ρ post (lanes-held c op g d n q o (s ∷ pre) post fs))
    , above-≋ c true (≋-sym (lanes-plugʳ op g d n q o pre post s ρ)) (above-held c (flatS op g d n q o (pre ʳ++ s ∷ post)) v fs)
    where
      ρ  = envAt c
      h  = stateᴺ (gh s) ρ
      kd = keyed-at c (flatS op g d n q o (pre ʳ++ s ∷ post)) (proj₂ fs)
      FlatAt′ = FlatAt ρ (outerᴺ (lane g) (outerG d (gh o)) ρ)
      L : states (lanesL (pre ʳ++ s ∷ post)) ρ ≡ laneRuns (reverse pre) post (flagOf s) ρ h
      L = toʳ (λ ls → states (lanesL ls) ρ ≡ laneRuns (reverse pre) post (flagOf s) ρ h) pre (lanes-runs (reverse pre) s post ρ)
      pool : ∀ d → cutᴺ (poolG d (gh o) (deadL (reverse pre ++ s ∷ post))) ρ ≡ outerT d (gh o) ρ (poolRuns (reverse pre) post (flagOf s) ρ h)
      pool false = pool-runs (reverse pre) s post ρ
      pool true  = cong (cutᴺ (gh o) ρ ∪_) (pool-runs (reverse pre) s post ρ)
      P : cutᴺ (poolG d (gh o) (deadL (pre ʳ++ s ∷ post))) ρ ≡ outerT d (gh o) ρ (poolRuns (reverse pre) post (flagOf s) ρ h)
      P = toʳ (λ ls → cutᴺ (poolG d (gh o) (deadL ls)) ρ ≡ outerT d (gh o) ρ (poolRuns (reverse pre) post (flagOf s) ρ h)) pre (pool d)

  -- A connect's source, its body not subscribed ahead of it: its run
  -- plugs the connect.
  src-above : ∀ {R Γ X B} (c : Ctx R Γ B) k (b : St (X ∷ Γ) B) (s : St Γ X) → CS.bodyAt k ≡ nothing → Held (plug c (connS k s b))
            → Above c true (stateᴺ (gh (connS k s b)) (envAt c)) → Above (inSrc k b c) (flagOf s) (stateᴺ (gh s) (envAt c))
  src-above c (cs false sl sa nothing as ow r e) b s _ fs up =
    (here-at c (connS (cs false sl sa nothing as ow r e) s b) fs , proj₂ (proj₂ (keyed-at c (connS (cs false sl sa nothing as ow r e) s b) (proj₂ fs))))
    , above-≋ c true (≋-sym (src-plugⁿ false sl sa as ow r e b s (envAt c))) up
  src-above c (cs true sl sa nothing as ow r e) b s _ fs up =
    (conn-rested (cs true sl sa nothing as ow r e) (gh s) (envAt c) (here-at c (connS (cs true sl sa nothing as ow r e) s b) fs)
     , proj₂ (proj₂ (keyed-at c (connS (cs true sl sa nothing as ow r e) s b) (proj₂ fs))))
    , above-≋ c true (≋-sym (src-plugⁿ true sl sa as ow r e b s (envAt c))) up
  src-above c (cs cl sl sa (just p) as ow r en) b s () fs up

-- A settled node anywhere in a tree the shape holds of: its run, and
-- every frame above, kept.
flight-held : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) p → WfC c → Held (plug c s) → Flight ⟨ c , s , absorbed , p ⟩
flight-held c s p v fs = shape-st c s fs , above-held c s v fs

------------------------------------------------------------------------
-- And back: what every frame above keeps of a hole's run, the whole tree

-- A source's rest, keyed as its run's rest.
conn-unrested : ∀ {Γ X B} k {β : Events∞ B} (n : Node Γ X) (ρ : NEnv Γ) → ConnAt k β (rested {B = X} (stateᴺ n ρ)) ρ → ConnAt k β (stateᴺ (restᶜ n) ρ) ρ
conn-unrested k n ρ x = record { mark = mark ; hm = hm ; at = at ; kb = kb ; kr = kr ; fr = fr ; cue = cue ; ks = ks ; rs = rs ; ub = ub ; sub = sub ; ends = ends }
  where open ConnAt x

-- Every frame above a hole keeping its own of the run the hole's ghost
-- gives it, and the hole its own: the whole tree keyed.  Read only where
-- each connect holding the hole in its source has its body subscribed
-- (`WfC`): a source still to subscribe is idle as its hole reads it, and
-- subscribed as the tree reads it.
keys-above : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) → WfC c → Above c (flagOf s) (stateᴺ (gh s) (envAt c)) → Keyed s (envAt c) → Keys (plug c s)
keys-above top                               s v ab k = k
keys-above (inMap g c)                       s v ab k = keys-above c (mapS g s) v (above-≋ c true (≋-by refl refl) ab) (tt , k)
keys-above (inScan g z c)                    s v ab k = keys-above c (scanS g z s) v (above-≋ c true (≋-by refl refl) ab) (tt , k)
keys-above (inCut true a c)                  s v ab k = keys-above c (cutS true a s) v ab (tt , k)
keys-above (inCut false a c)                 s v ab k = keys-above c (cutS false a s) v (above-≋ c true (≋-by refl refl) ab) (tt , k)
keys-above (inLn b c)                        s v ab k = keys-above c (lnS b s) v ab (tt , k)
keys-above (inTake i q w c)                  s v (ta , ab) k =
  keys-above c (takeS i q w s) v (above-≋ c true (take-plug i q w (gh s) (envAt c)) ab) (ta , k)
keys-above (inOuter op g true n q ls c)      s (_ , v) ((fa , kl) , ab) k =
  keys-above c (flatS op g true n q s ls) v (above-≋ c true (outer-plug op g true n q ls s (envAt c)) ab) (fa , k , kl)
keys-above (inOuter op g false n q ls c)     s (_ , v) ((fa , kl) , ab) k =
  keys-above c (flatS op g false n q s ls) v (above-≋ c true (outer-plug op g false n q ls s (envAt c)) ab) (fa , k , kl)
keys-above (inLanes op g d n q o pre post c) s (_ , _ , _ , v) ((fa , ko , kp , kq , _) , ab) k =
  keys-above c (flatS op g d n q o (pre ʳ++ s ∷ post)) v (above-≋ c true (lanes-plugʳ op g d n q o pre post s ρ) ab)
    (subst₂ (FlatAt ρ (outerᴺ (lane g) (outerG d (gh o)) ρ)) (sym L) (sym P) fa , ko , keyedL-join pre kp (k , kq))
  where
    ρ  = envAt c
    h  = stateᴺ (gh s) ρ
    L : states (lanesL (pre ʳ++ s ∷ post)) ρ ≡ laneRuns (reverse pre) post (flagOf s) ρ h
    L = toʳ (λ ls → states (lanesL ls) ρ ≡ laneRuns (reverse pre) post (flagOf s) ρ h) pre (lanes-runs (reverse pre) s post ρ)
    pool : ∀ d → cutᴺ (poolG d (gh o) (deadL (reverse pre ++ s ∷ post))) ρ ≡ outerT d (gh o) ρ (poolRuns (reverse pre) post (flagOf s) ρ h)
    pool false = pool-runs (reverse pre) s post ρ
    pool true  = cong (cutᴺ (gh o) ρ ∪_) (pool-runs (reverse pre) s post ρ)
    P : cutᴺ (poolG d (gh o) (deadL (pre ʳ++ s ∷ post))) ρ ≡ outerT d (gh o) ρ (poolRuns (reverse pre) post (flagOf s) ρ h)
    P = toʳ (λ ls → cutᴺ (poolG d (gh o) (deadL ls)) ρ ≡ outerT d (gh o) ρ (poolRuns (reverse pre) post (flagOf s) ρ h)) pre (pool d)
keys-above (inSrc (cs false sl sa nothing as ow r e) b c) s (refl , _ , v) ((ca , kb) , ab) k =
  keys-above c (connS (cs false sl sa nothing as ow r e) s b) v (above-≋ c true (src-plugⁿ false sl sa as ow r e b s (envAt c)) ab) (ca , k , kb)
keys-above (inSrc (cs true sl sa nothing as ow r e) b c) s (refl , _ , v) ((ca , kb) , ab) k =
  keys-above c (connS (cs true sl sa nothing as ow r e) s b) v (above-≋ c true (src-plugⁿ true sl sa as ow r e b s (envAt c)) ab)
    (conn-unrested (cs true sl sa nothing as ow r e) (gh s) (envAt c) ca , k , kb)
keys-above (inSrc (cs cl sl sa (just _) as ow r e) b c) s (() , _ , v) ab k
keys-above (inBody k o c)                    s (_ , _ , v) ((ca , ko , _) , ab) x =
  keys-above c (connS k o s) v (above-≋ c true (body-plug k o s (envAt c)) ab) (ca , ko , x)
