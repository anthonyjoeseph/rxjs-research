{-# OPTIONS --guardedness #-}

-- EVERY STEP OF `operation.PureObservable` KEEPS WHAT ITS CONFIGURATION
-- MEANS (`adequacy.Engine.Meaning.M`), up to what a run shows (`_≅_`): a silent
-- step means the same, a value is that value then the rest, a completion
-- ends it, and nothing owed shows nothing more.
--
-- The proof is the step's own dispatch: the mode, then the one frame a
-- rise passes, the one node a mark runs, or the one former a subscribe
-- begins.  Each clause is one frame's or one node's fact, carried to the
-- root by `lift-≅` or `closed-hides`; no clause reads any other node, and
-- the invariant (`adequacy.Engine.Inv.Inv`) is read only at the node it
-- constrains (`wf-split`).
--
-- So the obligations are per frame and per node, not per step and field.
-- What is left: the frames with siblings (a flatMap's outer and lanes, a
-- connect's source and body), whose rises interleave with what the
-- siblings run; a joiner's fed value; the two tearing folds (`unsub`, as
-- a rest); a skip dropped under a context; and the structural facts
-- about `search` and `plug`.
module adequacy.Engine.Kept where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; _ʳ++_; [_]; reverse)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (zero; suc; pred)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Unit using (tt)
open import Data.List.Properties using (++-assoc; ++-identityʳ; ʳ++-defn)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong; cong₂; trans)

open import Tree using (Obs; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.MonotonicList.Events using (Events; Events∞; Pos; Time; Frame; From; From∞; Timeline; timelineAt;
  out; skip; end; hush; idle; _∪_; ix; last; root; at; done; emit; stall; close)
  renaming (quiet to silentᶠ)
open import denotation.MonotonicList using (Agreeᵀ; agreeᵀ-refl; agree-refl; _≈[_]_)
import denotation.MonotonicList as M′
open import denotation.NonExpansive using (_,ˢ_; liveᴼ; []ᴸ; []ᑫ; go-ne; mapᴱ-neᴹ; ∪-ne; burstOn-ne; beside-ne)
open import denotation.Unfold using (Node; idleᶜ; ofᶜ; restsᶜ; states; ended; outerᴺ; restᶜ; takeWhileᶜ; endingᶜ; burstᶜ;
  connectᶜ; live; stateᴺ; cutᴺ; meaning; subscribe; outer∞; NEnv) renaming (feed to feedᵁ)
open import denotation.Denote using (flatOp)
open import operation.PureObservable using (play; ending; over; rest; module Machine; module Driver)
open Machine using (St; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
  Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody; plug; closed; closedUp;
  CS; cs; Att; attAt; attached; Owe; free; cpAt; cutAt; overAt; Ev; nx; cp; _⊕_;
  Conf; ⟨_,_,_,_⟩; subscribing; absorbed; rising; load;
  Mark; ofM; attM; bodyM; srcAttM; owedM; cpM; cutM; joinM; leafM; search; found; run; unsub; leaf; feed)
  renaming (cut to cutᴹ)
open import adequacy.Engine.Meaning using (Has; M; _≅_; _≋_; agree-≅; atOut; bodyFrame; closed-hides; connSrc; deadL; deadOne; doneE; doneE-ne;
  doneG; envAt; flagOf; gh; holeL; holeT; joinG; lane; laneRuns; lanes-dead; lanes-refl; lanesFrame; lanesL; laneᴹ; lift-≅; liveL;
  outerFrame; outerG; outerOf; outerT; pastOut; poolG; poolRuns; queue-refl; rested; risen; same; srcFrame; srcG; srcRun; subOr;
  tailsOn; taken; taking∞; tape; took; up; ≅-refl; ≅-sym; ≅-trans; ≈-refl; ≋-by; ≋-out; ≋-tr; ≋-trans)
open import adequacy.Engine.Inv using (Unpended; Opened; Wf; Base; module Base; Inv; module Inv; inv-at; wfI; wf-split; Owns; ofO;
  attO; cpO; cutO; bodyO; srcAttO; owedO; joinO; leafO; owned; search-hit)
open import adequacy.Engine.Race using (First; go-rise; cuts-swap)
open import adequacy.Engine.Head using (Frag)
open import adequacy.Engine.Pick using (module Order; Clear)

open Events∞

-- A run told now, nothing left running after it.
now : ∀ {A} → Events A → Events∞ A
now e .force = e
now e .cut   = idle

out-≅ : ∀ {A p a} {r r′ : Events∞ A} → force r ≡ force r′ → out p a r ≅ out p a r′
out-≅ {r = r} {r′} e = to e , to (sym e)
  where
    to : ∀ {x y : Events∞ _} → force x ≡ force y → ∀ {k b} → Has (out _ _ x) k b → Has (out _ _ y) k b
    to e atOut       = atOut
    to e (pastOut h) = pastOut (subst (λ z → Has z _ _) e h)

------------------------------------------------------------------------
-- Each frame is the node it is a hole of

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

private
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

  sub-settled : ∀ {Γ A} p (s : St Γ A) → Unpended s → subOr p s ≡ gh s
  sub-settled p (coldS b l)             u = refl
  sub-settled p (ofS i q xs)            u = refl
  sub-settled p doneS                   u = refl
  sub-settled p (mapS f s)              u = refl
  sub-settled p (scanS f z s)           u = refl
  sub-settled p (cutS l a s)            u = refl
  sub-settled p (lnS b s)               u = refl
  sub-settled p (takeS i q w s)         u = refl
  sub-settled p (flatS op f d n q o ls) u = refl
  sub-settled p (connS k o b)           u = refl
  sub-settled p (joinS j g x ib)        u = refl

  conn-plug : ∀ {Γ X B} k (b : St (X ∷ Γ) B) (s : St Γ X) (ρ : NEnv Γ) → Unpended s → Opened k s
            → connSrc (CS.closed k) (CS.srcAt k) (CS.endAt k) (gh b) ρ (stateᴺ (gh s) ρ) ≋ stateᴺ (connectᶜ (CS.srcAt k) (gh b) (srcG k s)) ρ
  conn-plug (cs false sl sa (just p) as ow r e) b s ρ u o rewrite sub-settled (p ⊕ [ ix 1 ]) s u = ≋-by refl refl
  conn-plug (cs true  sl sa (just p) as ow r e) b s ρ u (() , _)
  conn-plug (cs false sl sa nothing as ow r e)  b s ρ u o = ≋-by refl refl
  conn-plug {X = X} (cs true sl sa nothing as ow r e) b s ρ u o k =
    ∪-ne (burstOn-ne r (R k)) (agreeᵀ-refl k _) ,ˢ beside-ne r (same k _) (R k)
    where
      R : rested {B = X} (stateᴺ (gh s) ρ) ≋ stateᴺ (restᶜ (gh s)) ρ
      R = ≋-by refl refl

  src-plug : ∀ {Γ X B} k (b : St (X ∷ Γ) B) (s : St Γ X) (ρ : NEnv Γ) → Unpended s → Opened k s
           → srcFrame k (gh b) ρ (stateᴺ (gh s) ρ) ≋ stateᴺ (gh (connS k s b)) ρ
  src-plug k b s ρ u o = done-plug (CS.owedAt k) (CS.srcLive k) _ ρ (conn-plug k b s ρ u o)

  body-plug : ∀ {Γ X B} k (o : St Γ X) (s : St (X ∷ Γ) B) (ρ : NEnv Γ)
            → bodyFrame k o ρ (stateᴺ (gh s) (srcRun (srcG k o) ρ ∷ᴬ ρ)) ≋ stateᴺ (gh (connS k o s)) ρ
  body-plug (cs cl sl sa (just p) as ow r e)  o s ρ = done-plug ow sl _ ρ (≋-by refl refl)
  body-plug (cs false sl sa nothing as ow r e) o s ρ = done-plug ow sl _ ρ (≋-by refl refl)
  body-plug (cs true sl sa nothing as ow r e)  o s ρ = done-plug ow sl _ ρ (≋-by refl refl)

  take-true : ∀ {Γ A} i (q : A → Bool) (n : Node Γ A) (ρ : NEnv Γ) a p → q a ≡ true
            → took i q (risen n ρ (nx a) p) ≋ risen (takeWhileᶜ i q n) ρ (nx a) p
  take-true i q n ρ a p e = ≋-out (cong (λ b → M′.taking i q p a b (stateᴺ n ρ)) e) refl refl refl refl

  take-incl : ∀ {Γ A} (q : A → Bool) (n : Node Γ A) (ρ : NEnv Γ) a p → q a ≡ false
            → took true q (risen n ρ (nx a) p) ≋ risen (endingᶜ (p ⊕ [ last ]) n) ρ (nx a) (p ⊕ [ ix 0 ])
  take-incl q n ρ a p e = ≋-out (cong (λ b → M′.taking true q p a b (stateᴺ n ρ)) e) refl refl refl refl

  take-excl : ∀ {Γ A} (q : A → Bool) (n : Node Γ A) (ρ : NEnv Γ) a p → q a ≡ false
            → took false q (risen n ρ (nx a) p) ≋ stateᴺ (endingᶜ (p ⊕ [ last ]) n) ρ
  take-excl q n ρ a p e = ≋-by (cong (λ b → M′.taking false q p a b (stateᴺ n ρ)) e) refl

  -- A connect, its source subscribed now, is the source's frame read
  -- with the body over it.
  conn-src : ∀ {Γ X B} ow sl r e (b : Node (X ∷ Γ) B) (n : Node Γ X) (ρ : NEnv Γ)
           → stateᴺ (doneG ow sl (connectᶜ r b (live n))) ρ ≋ doneE ow sl (connSrc false r e b ρ (stateᴺ n ρ))
  conn-src (just _) sl    r e b n ρ = ≋-by refl refl
  conn-src nothing  false r e b n ρ = ≋-by refl refl
  conn-src nothing  true  r e b n ρ = ≋-by refl refl

  -- A cold's next frame, as the frames the denotation plays.
  rest-force : ∀ {Γ A t} τ e (m : From A t) (ρ : NEnv Γ) → M′.frames τ e m ≡ meaning (tape true (rest τ e m)) ρ
  rest-force τ e done          ρ = refl
  rest-force τ e silentᶠ       ρ = refl
  rest-force τ e (at t _ fr)   ρ = refl

  rest-cut : ∀ {Γ A t} τ e (m : From A t) (ρ : NEnv Γ) → idle ≡ cutᴺ (tape true (rest τ e m)) ρ
  rest-cut τ e done          ρ = refl
  rest-cut τ e silentᶠ       ρ = refl
  rest-cut τ e (at t _ fr)   ρ = refl

------------------------------------------------------------------------
-- What a step keeps

module _ {R : Set} where
  open Driver R using (Step; silent; value; complete; drained; step; played) renaming (took to tookᴰ)

  KeptFrom : Events R → Step → Set
  KeptFrom e (silent t k)    = e ≅ M k
  KeptFrom e (value t p a k) = e ≅ out p a (now (M k))
  KeptFrom e (complete p)    = e ≅ end p
  KeptFrom e drained         = e ≅ hush

  Kept : Conf R → Set
  Kept k = KeptFrom (M k) (step k)

  kept-pre : ∀ {e e′} x → e ≅ e′ → KeptFrom e′ x → KeptFrom e x
  kept-pre (silent t k)    q r = ≅-trans q r
  kept-pre (value t p a k) q r = ≅-trans q r
  kept-pre (complete p)    q r = ≅-trans q r
  kept-pre drained         q r = ≅-trans q r

  ----------------------------------------------------------------------
  -- The leaves: each one frame's or one node's fact

  postulate
    -- Nothing owed, nothing more shown.
    quiet-empty : ∀ {Γ A} (c : Ctx R Γ A) (s : St Γ A) p → Inv ⟨ c , s , absorbed , p ⟩ → search top (plug c s) ≡ nothing
                → M ⟨ c , s , absorbed , p ⟩ ≅ hush
    -- A skip dropped at the hole drops nothing a run shows.
    lift-skip : ∀ {Γ A} (c : Ctx R Γ A) f {h h′ : Events∞ A} {q r} → force h ≡ skip q r → r ≋ h′ → up c f h ≅ up c f h′
    -- An unsubscribe leaves a rest showing what the rest before it showed.
    -- The two rests differ only in tail pins (a connect source's burst
    -- inside `srcAt`, kept by `burstOn`, against a torn-down cold), which
    -- show only skips: a frame-by-frame congruence, false for a frame
    -- stalling forever inside `srcAt`.
    unsub-rest : ∀ {Γ A} (c : Ctx R Γ A) (s : St Γ A) {s′ t} → unsub s ≡ (s′ , t)
               → up c true (stateᴺ (restᶜ (gh s)) (envAt c)) ≅ up c true (stateᴺ (restᶜ (gh s′)) (envAt c))
    -- And a connect's rest, its source unsubscribed.
    conn-unsub : ∀ {Γ X B} (c : Ctx R Γ B) k (b : St (X ∷ Γ) B) (o : St Γ X) {o′ t} → unsub o ≡ (o′ , t)
               → up c true (stateᴺ (restᶜ (connectᶜ (CS.srcAt k) (gh b) (srcG k o))) (envAt c))
               ≅ up c true (stateᴺ (restᶜ (connectᶜ (CS.srcAt k) (gh b) (srcG k o′))) (envAt c))

    -- The frames with siblings: a rise interleaves with what they run.
    rise-outer-nx : ∀ {Γ A B} op (f : A → Obs Timeline Γ B) d n q ls (c : Ctx R Γ B) (o : St Γ A) a p
                  → Inv ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩ → Kept ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩
    rise-outer-cp : ∀ {Γ A B} op (f : A → Obs Timeline Γ B) d n q ls (c : Ctx R Γ B) (o : St Γ A) p
                  → Inv ⟨ inOuter op f d n q ls c , o , rising cp , p ⟩ → Kept ⟨ inOuter op f d n q ls c , o , rising cp , p ⟩
    -- A lane still in its flatMap's list completing frees its slot.
    rise-lanes-cp : ∀ {Γ A B} op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) pre post (c : Ctx R Γ B) (s : St Γ B) p
                  → Inv ⟨ inLanes op f d n q o pre post c , s , rising cp , p ⟩ → flagOf s ≡ true
                  → up (inLanes op f d n q o pre post c) true (risen (gh s) (envAt c) cp p) ≅ M (Machine.dequeue c op f d (pred n) q o (pre ʳ++ Machine.ended s ∷ post) p)
    -- A source's value, read by its body, is shown first as a skip just
    -- past it: the body's next event is later (the race `Clear` carries
    -- at `inSrc`), and what follows is the body fed as the meaning feeds
    -- it (`denotation.Unfold.feed`), the source past its value.  The
    -- stepper's `adequacy.Stepper.SourceFirst.fed-first` is this fact.
    src-leads : ∀ {Γ X B} k (b : St (X ∷ Γ) B) (c : Ctx R Γ B) (s : St Γ X) a p
              → Inv ⟨ inSrc k b c , s , rising (nx a) , p ⟩ → Clear p a (inSrc k b c) s
              → Σ (Events∞ B) λ r → force (srcFrame k (gh b) (envAt c) (risen (gh s) (envAt c) (nx a) p)) ≡ skip (p ⊕ [ ix 0 ]) r
                                  × r ≋ srcFrame k (feedᵁ (here refl) p (just a) (gh b)) (envAt c) (stateᴺ (gh s) (envAt c))
    -- The meaning's feed and the engine's differ only in skips.  On a
    -- live joiner joined before `p` both queue the value under it
    -- (`operation.AbstractObservable.queued`); one joined at or after `p`, and a lane
    -- or subscription not yet started, the meaning hands a skip the
    -- engine does not keep.  Each such start is past the source's
    -- position, the race won at `inSrc`, so none is handed the value.
    fed-ghost : ∀ {Γ X B} k (b : St (X ∷ Γ) B) (c : Ctx R Γ B) (s : St Γ X) a p → Inv ⟨ inSrc k b c , s , rising (nx a) , p ⟩
              → up c true (srcFrame k (feedᵁ (here refl) p (just a) (gh b)) (envAt c) (stateᴺ (gh s) (envAt c)))
              ≅ up c true (srcFrame k (gh (feed (here refl) p (nx a) b)) (envAt c) (stateᴺ (gh s) (envAt c)))
    rise-src-cp : ∀ {Γ X B} k (b : St (X ∷ Γ) B) (c : Ctx R Γ B) (s : St Γ X) p
                → Inv ⟨ inSrc k b c , s , rising cp , p ⟩ → Kept ⟨ inSrc k b c , s , rising cp , p ⟩
    rise-body-nx : ∀ {Γ X B} k (o : St Γ X) (c : Ctx R Γ B) (s : St (X ∷ Γ) B) b p
                 → Inv ⟨ inBody k o c , s , rising (nx b) , p ⟩ → Kept ⟨ inBody k o c , s , rising (nx b) , p ⟩
    rise-body-cp : ∀ {Γ X B} k (o : St Γ X) (c : Ctx R Γ B) (s : St (X ∷ Γ) B) p
                 → Inv ⟨ inBody k o c , s , rising cp , p ⟩ → Kept ⟨ inBody k o c , s , rising cp , p ⟩

    -- A joiner's next fed value, shown at its position.
    join-nx : ∀ {Γ A} (c : Ctx R Γ A) j x q (a : A) ib p → Inv ⟨ c , joinS j true x ((q , nx a) ∷ ib) , absorbed , p ⟩
            → M ⟨ c , joinS j true x ((q , nx a) ∷ ib) , absorbed , p ⟩ ≅ M ⟨ c , joinS j true x ib , rising (nx a) , q ⟩
    -- A joiner of a source already ended owes its end at its `last`.
    joined-closed : ∀ {Γ A} (c : Ctx R Γ A) (x : A ∈ Γ) p → Inv ⟨ c , pend (connected x) , subscribing , p ⟩
                  → closedUp c x ≡ true → M ⟨ c , pend (connected x) , subscribing , p ⟩ ≅ M ⟨ c , ofS 0 p [] , absorbed , p ⟩
    -- A defer is the program it defers, one level down, after a skip.
    defer-kept : ∀ {Γ A} (c : Ctx R Γ A) l p → Inv ⟨ c , pend (defer l) , subscribing , p ⟩ → Kept ⟨ c , pend (defer l) , subscribing , p ⟩

  -- THE ORDER: a lane's value rises first among its flatMap's parts.
  lanes-first : ∀ {Γ A B} op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) pre post (c : Ctx R Γ B) (s : St Γ B) b p
              → Inv ⟨ inLanes op f d n q o pre post c , s , rising (nx b) , p ⟩ → flagOf s ≡ true → closed c ≡ false
              → First p (outerᴺ (lane f) (outerG d (gh o)) (envAt c)) (states (lanesL post) (envAt c)) (states (lanesL (reverse pre)) (envAt c))
                  (outerT d (gh o) (envAt c) (poolRuns (reverse pre) post true (envAt c) (stateᴺ (gh s) (envAt c))))
  lanes-first op f d n q o pre post c s b p v fl ce = proj₁ (Order.lead (Inv.ord v) fl) ce

  ----------------------------------------------------------------------
  -- A configuration focused anywhere means what its whole tree means

  plug-up : ∀ {Γ A} (c : Ctx R Γ A) (s : St Γ A) → Unpended s → Wf (plug c s)
          → up c (flagOf s) (stateᴺ (gh s) (envAt c)) ≅ meaning (gh (plug c s)) []ᴬ
  plug-up top                               s u w = ≅-refl
  plug-up (inMap f c)                       s u w = ≅-trans (lift-≅ c true (≋-by refl refl)) (plug-up c (mapS f s) tt w)
  plug-up (inScan f z c)                    s u w = ≅-trans (lift-≅ c true (≋-by refl refl)) (plug-up c (scanS f z s) tt w)
  plug-up (inCut true a c)                  s u w = plug-up c (cutS true a s) tt w
  plug-up (inCut false a c)                 s u w = ≅-trans (lift-≅ c true (≋-by refl refl)) (plug-up c (cutS false a s) tt w)
  plug-up (inLn b c)                        s u w = plug-up c (lnS b s) tt w
  plug-up (inTake i q x c)                  s u w = ≅-trans (lift-≅ c true (take-plug i q x (gh s) (envAt c))) (plug-up c (takeS i q x s) tt w)
  plug-up (inOuter op f d n q ls c)         s u w =
    ≅-trans (lift-≅ c true (outer-plug op f d n q ls s (envAt c))) (plug-up c (flatS op f d n q s ls) tt w)
  plug-up (inLanes op f d n q o pre post c) s u w =
    ≅-trans (lift-≅ c true (lanes-plugʳ op f d n q o pre post s (envAt c))) (plug-up c (flatS op f d n q o (pre ʳ++ s ∷ post)) tt w)
  plug-up (inSrc k b c)                     s u w =
    ≅-trans (lift-≅ c true (src-plug k b s (envAt c) u (proj₁ (proj₂ (wf-split c (connS k s b) tt w))))) (plug-up c (connS k s b) tt w)
  plug-up (inBody k o c)                    s u w = ≅-trans (lift-≅ c true (body-plug k o s (envAt c))) (plug-up c (connS k o s) tt w)

  lift-plug : ∀ {Γ A} (c : Ctx R Γ A) (s : St Γ A) p → Unpended s → Wf (plug c s) → M ⟨ c , s , absorbed , p ⟩ ≅ meaning (gh (plug c s)) []ᴬ
  lift-plug c s p = plug-up c s

  ----------------------------------------------------------------------
  -- A rise, by the frame it passes

  -- A lane in the list is one of its flatMap's runs, between the lanes
  -- after it and before it; its pool, the lanes ended around it.
  lanes-L : ∀ {Γ B} pre (s : St Γ B) post (ρ : NEnv Γ) → flagOf s ≡ true
          → states (lanesL (pre ++ s ∷ post)) ρ ≡ states (lanesL post) ρ ++ stateᴺ (gh s) ρ ∷ states (lanesL pre) ρ
  lanes-L pre s post ρ fl = trans (lanes-runs pre s post ρ) (cong (λ x → laneRuns pre post x ρ (stateᴺ (gh s) ρ)) fl)

  lanes-P : ∀ {Γ A B} d (o : St Γ A) pre (s : St Γ B) post (ρ : NEnv Γ) → flagOf s ≡ true
          → outerT d (gh o) ρ (poolRuns pre post true ρ (stateᴺ (gh s) ρ)) ≡ cutᴺ (poolG d (gh o) (deadL (pre ++ s ∷ post))) ρ
  lanes-P false o pre s post ρ fl = sym (trans (pool-runs pre s post ρ) (cong (λ x → poolRuns pre post x ρ (stateᴺ (gh s) ρ)) fl))
  lanes-P true  o pre s post ρ fl = cong (cutᴺ (gh o) ρ ∪_) (lanes-P false o pre s post ρ fl)

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

  -- A lane's value, first among its flatMap's parts, is the flatMap's.
  rise-lanes-true : ∀ {Γ A B} op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) pre post (c : Ctx R Γ B) (s : St Γ B) b p
                  → flagOf s ≡ true
                  → First p (outerᴺ (lane f) (outerG d (gh o)) (envAt c)) (states (lanesL post) (envAt c)) (states (lanesL pre) (envAt c))
                      (outerT d (gh o) (envAt c) (poolRuns pre post true (envAt c) (stateᴺ (gh s) (envAt c))))
                  → up c true (lanesFrame op (lane f) d q (gh o) pre post true (envAt c) (risen (gh s) (envAt c) (nx b) p))
                  ≅ up c true (risen (gh (flatS op f d n q o (pre ++ s ∷ post))) (envAt c) (nx b) p)
  rise-lanes-true op f d n q o pre post c s b p fl fi =
    lift-≅ c true (≋-out (go-rise (flatOp op) O Ls (risen (gh s) ρ (nx b) p) Rs Q T refl fi) refl
      (cong₂ (λ ls t → M′.go (flatOp op) O ls Q t) (sym L) P)
      (cong₂ (M′.whole O) (sym L) P)
      (lanes-cut op f d n q o pre post s ρ b p fl))
    where
      ρ  = envAt c
      O  = outerᴺ (lane f) (outerG d (gh o)) ρ
      Ls = states (lanesL post) ρ
      Rs = states (lanesL pre) ρ
      Q  = Data.List.map (laneᴹ (lane f) ρ) q
      T  = outerT d (gh o) ρ (poolRuns pre post true ρ (stateᴺ (gh s) ρ))
      L  = lanes-L pre s post ρ fl
      P  = lanes-P d o pre s post ρ fl

  -- A lane's value under a closed observer: the flatMap is read through
  -- its tail alone, and the lane's tail is its rise's.
  lanes-closed : ∀ {Γ A B} op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) pre post (c : Ctx R Γ B) (s : St Γ B) b p
               → flagOf s ≡ true → closed c ≡ true
               → up c true (lanesFrame op (lane f) d q (gh o) pre post true (envAt c) (risen (gh s) (envAt c) (nx b) p))
               ≅ up c true (risen (gh (flatS op f d n q o (pre ++ s ∷ post))) (envAt c) (nx b) p)
  lanes-closed op f d n q o pre post c s b p fl ce =
    agree-≅ (closed-hides c true H (risen (gh (flatS op f d n q o (pre ++ s ∷ post))) ρ (nx b) p) ce
      (λ k → subst (Agreeᵀ k (cut H)) (lanes-cut op f d n q o pre post s ρ b p fl) (agreeᵀ-refl k (cut H))))
    where
      ρ = envAt c
      H = lanesFrame op (lane f) d q (gh o) pre post true ρ (risen (gh s) ρ (nx b) p)

  -- A lane out of its flatMap's list: what reaches it is absorbed, as
  -- the flatMap reads it through its tail alone.
  lane-dead : ∀ {Γ A B} op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) pre post (c : Ctx R Γ B) (s : St Γ B) e p → flagOf s ≡ false
            → up c true (lanesFrame op (lane f) d q (gh o) pre post false (envAt c) (risen (gh s) (envAt c) e p)) ≅ M ⟨ c , flatS op f d n q o (pre ++ s ∷ post) , absorbed , p ⟩
  lane-dead op f d n q o pre post c s e p fl =
    lift-≅ c true (≋-trans (lanes-dead op (lane f) d q (gh o) pre post (envAt c) (risen (gh s) (envAt c) e p) (stateᴺ (gh s) (envAt c)) (rc e))
      (subst (λ x → lanesFrame op (lane f) d q (gh o) pre post x (envAt c) (stateᴺ (gh s) (envAt c)) ≋ stateᴺ (gh (flatS op f d n q o (pre ++ s ∷ post))) (envAt c))
        fl (lanes-plug op f d n q o pre post s (envAt c))))
    where
      rc : ∀ e → cut (risen (gh s) (envAt c) e p) ≡ cut (stateᴺ (gh s) (envAt c))
      rc (nx b) = refl
      rc cp     = refl

  -- What a lane's rise means, with its flatMap's lanes `ls`.
  Rose : ∀ {Γ A B} op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) pre post (c : Ctx R Γ B) (s : St Γ B) b p → List (St Γ B) → Set
  Rose op f d n q o pre post c s b p ls =
    up (inLanes op f d n q o pre post c) true (risen (gh s) (envAt c) (nx b) p) ≅ up c true (risen (gh (flatS op f d n q o ls)) (envAt c) (nx b) p)

  Dead : ∀ {Γ A B} op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) pre post (c : Ctx R Γ B) (s : St Γ B) e p → List (St Γ B) → Set
  Dead op f d n q o pre post c s e p ls = up (inLanes op f d n q o pre post c) false (risen (gh s) (envAt c) e p) ≅ M ⟨ c , flatS op f d n q o ls , absorbed , p ⟩

  rise-lanes-nx : ∀ {Γ A B} op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) pre post (c : Ctx R Γ B) (s : St Γ B) b p
                → Inv ⟨ inLanes op f d n q o pre post c , s , rising (nx b) , p ⟩ → Kept ⟨ inLanes op f d n q o pre post c , s , rising (nx b) , p ⟩
  rise-lanes-nx op f d n q o pre post c s b p v with flagOf s in fl | closed c in ce
  ... | true  | true  = toʳ (Rose op f d n q o pre post c s b p) pre (lanes-closed op f d n q o (reverse pre) post c s b p fl ce)
  ... | true  | false = toʳ (Rose op f d n q o pre post c s b p) pre
                          (rise-lanes-true op f d n q o (reverse pre) post c s b p fl (lanes-first op f d n q o pre post c s b p v fl ce))
  ... | false | _     = toʳ (Dead op f d n q o pre post c s (nx b) p) pre (lane-dead op f d n q o (reverse pre) post c s (nx b) p fl)

  rise-lanes : ∀ {Γ A B} op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) pre post (c : Ctx R Γ B) (s : St Γ B) p
             → Inv ⟨ inLanes op f d n q o pre post c , s , rising cp , p ⟩ → Kept ⟨ inLanes op f d n q o pre post c , s , rising cp , p ⟩
  rise-lanes op f d n q o pre post c s p v with flagOf s in fl
  ... | true  = rise-lanes-cp op f d n q o pre post c s p v fl
  ... | false = toʳ (Dead op f d n q o pre post c s cp p) pre (lane-dead op f d n q o (reverse pre) post c s cp p fl)

  -- THE ACID TEST: takeWhile's three outcomes, each exact.
  took-nx : ∀ {Γ A} i (q : A → Bool) (c : Ctx R Γ A) (s : St Γ A) a p → Kept ⟨ inTake i q free c , s , rising (nx a) , p ⟩
  took-nx i q c s a p with q a in e
  ... | true = lift-≅ c true (take-true i q (gh s) (envAt c) a p e)
  took-nx true  q c s a p | false = lift-≅ c true (take-incl q (gh s) (envAt c) a p e)
  took-nx false q c s a p | false = lift-≅ c true (take-excl q (gh s) (envAt c) a p e)

  -- The body fed: the source's value a skip at the top, then the
  -- meaning's feed, then the engine's.
  rise-src-nx : ∀ {Γ X B} k (b : St (X ∷ Γ) B) (c : Ctx R Γ B) (s : St Γ X) a p
              → Inv ⟨ inSrc k b c , s , rising (nx a) , p ⟩ → Kept ⟨ inSrc k b c , s , rising (nx a) , p ⟩
  rise-src-nx k b c s a p v =
    ≅-trans (lift-skip c true (proj₁ (proj₂ L)) (proj₂ (proj₂ L)))
      (≅-trans (fed-ghost k b c s a p v)
        (lift-≅ c true (src-plug k (feed (here refl) p (nx a) b) s (envAt c) (Base.settled (Inv.base v))
          (proj₁ (proj₂ (wf-split c (connS k s b) tt (wfI (Inv.base v))))))))
    where
      L = src-leads k b c s a p v (Order.lead (Inv.ord v))

  rises : ∀ {Γ A} (c : Ctx R Γ A) (s : St Γ A) e p → Inv ⟨ c , s , rising e , p ⟩ → Kept ⟨ c , s , rising e , p ⟩
  rises top                               s (nx a) p v          = out-≅ refl
  rises top                               s cp     p v          = ≅-refl
  rises (inMap f c)                       s (nx a) p v          = lift-≅ c true (≋-out refl refl refl refl refl)
  rises (inMap f c)                       s cp     p v          = lift-≅ c true (≋-by refl refl)
  rises (inScan f z c)                    s (nx a) p v          = lift-≅ c true (≋-out refl refl refl refl refl)
  rises (inScan f z c)                    s cp     p v          = lift-≅ c true (≋-by refl refl)
  rises (inCut true a c)                  s e      p v          = ≅-refl
  rises (inCut false a c)                 s (nx x) p v          = lift-≅ c true (≋-by refl refl)
  rises (inCut false a c)                 s cp     p v          = lift-≅ c true (≋-by refl refl)
  rises (inLn b c)                        s e      p v          = ≅-refl
  rises (inTake i q free c)               s (nx a) p v          = took-nx i q c s a p
  rises (inTake i q free c)               s cp     p v          = lift-≅ c true (≋-by refl refl)
  rises (inTake i q (cpAt r) c)      s (nx a) p v          = lift-≅ c true (≋-by refl refl)
  rises (inTake i q (cpAt r) c)      s cp     p v          = lift-≅ c true (≋-by refl refl)
  rises (inTake i q (cutAt r) c)     s (nx a) p v          = lift-≅ c true (≋-by refl refl)
  rises (inTake i q (cutAt r) c)     s cp     p v          = lift-≅ c true (≋-by refl refl)
  rises (inTake i q (overAt r) c)    s (nx a) p v          = lift-≅ c true (≋-by refl refl)
  rises (inTake i q (overAt r) c)    s cp     p v          = lift-≅ c true (≋-by refl refl)
  rises (inOuter op f d n q ls c)         s (nx a) p v          = rise-outer-nx op f d n q ls c s a p v
  rises (inOuter op f d n q ls c)         s cp     p v          = rise-outer-cp op f d n q ls c s p v
  rises (inLanes op f d n q o pre post c) s (nx b) p v          = rise-lanes-nx op f d n q o pre post c s b p v
  rises (inLanes op f d n q o pre post c) s cp     p v          = rise-lanes op f d n q o pre post c s p v
  rises (inSrc k b c)                     s (nx a) p v          = rise-src-nx k b c s a p v
  rises (inSrc k b c)                     s cp     p v          = rise-src-cp k b c s p v
  rises (inBody k o c)                    s (nx b) p v          = rise-body-nx k o c s b p v
  rises (inBody k o c)                    s cp     p v          = rise-body-cp k o c s p v

  ----------------------------------------------------------------------
  -- A subscribe, by the former it begins

  begins : ∀ {Γ A} (c : Ctx R Γ A) (o : Obs Timeline Γ A) p → Inv ⟨ c , pend o , subscribing , p ⟩ → Kept ⟨ c , pend o , subscribing , p ⟩
  begins c (cold x) p v with timelineAt x p
  ... | at zero _ b    = ≅-refl
  ... | at (suc t) _ b = lift-≅ c true (≋-by refl refl)
  ... | done           = lift-≅ c true (≋-by refl refl)
  ... | silentᶠ        = lift-≅ c true (≋-by refl refl)
  begins c empty             p v = lift-≅ c true (≋-by refl refl)
  begins c (of xs)           p v = ≅-refl
  begins c (map f s)         p v = lift-≅ c true (≋-by refl refl)
  begins c (scan f z s)      p v = lift-≅ c true (≋-by refl refl)
  begins c (takeWhile i q s) p v = lift-≅ c true (≋-by refl refl)
  begins c (flatMap op f s)  p v = lift-≅ c true λ m →
    agreeᵀ-refl m _ ,ˢ
    go-ne (flatOp op) (liveᴼ {e = outer∞ (lane f) (subscribe s p) (envAt c)} {outerOf (lane f) (envAt c) (stateᴺ (subscribe s p) (envAt c))}
                         (agreeᵀ-refl m _) (mapᴱ-neᴹ (λ a → ≈-refl _) (agree-refl m _)))
      []ᴸ []ᑫ (agreeᵀ-refl m idle)
  begins c (connect s b)     p v = lift-≅ c true (≋-by refl refl)
  begins c (connected x)     p v with closedUp c x in ce
  ... | true  = joined-closed c x p v ce
  ... | false = ≅-refl
  begins c (defer l)         p v = defer-kept c l p v

  ----------------------------------------------------------------------
  -- A mark run, by the node that owns it

  cut-rest : ∀ {Γ A} (c : Ctx R Γ A) (s : St Γ A) {s′ t} → cutᴹ s ≡ (s′ , t)
           → up c true (stateᴺ (restᶜ (gh s)) (envAt c)) ≅ up c true (stateᴺ (restᶜ (gh s′)) (envAt c))
  cut-rest c (cutS true attached x) e with unsub x in ux
  cut-rest c (cutS true attached x) refl | x′ , t = ≅-trans (unsub-rest c x ux) (lift-≅ c true (≋-by refl refl))
  cut-rest c (cutS false attached x) e with unsub x in ux
  cut-rest c (cutS false attached x) refl | x′ , t = ≅-trans (lift-≅ c true (≋-by refl refl)) (≅-trans (unsub-rest c x ux) (lift-≅ c true (≋-by refl refl)))
  cut-rest c (cutS true (attAt p) x)  refl = lift-≅ c true (≋-by refl refl)
  cut-rest c (cutS false (attAt p) x) refl = ≅-refl
  cut-rest c (pend o)                refl = ≅-refl
  cut-rest c (coldS b l)             refl = ≅-refl
  cut-rest c (ofS i p xs)            refl = ≅-refl
  cut-rest c doneS                   refl = ≅-refl
  cut-rest c (mapS f s)              refl = ≅-refl
  cut-rest c (scanS f z s)           refl = ≅-refl
  cut-rest c (lnS b s)               refl = ≅-refl
  cut-rest c (takeS i q w s)         refl = ≅-refl
  cut-rest c (flatS op f d n q o ls) refl = ≅-refl
  cut-rest c (connS k o b)           refl = ≅-refl
  cut-rest c (joinS j g x ib)        refl = ≅-refl

  opened : ∀ {Γ X B} (c : Ctx R Γ B) k (o : St Γ X) (b : St (X ∷ Γ) B) {p} → Inv ⟨ c , connS k o b , absorbed , p ⟩ → Opened k o
  opened c k o b v = proj₁ (Base.focWf (Inv.base v))

  -- A cold's frame played on: a value shown, a stall or a close skipped.
  playing : ∀ {Γ A t} (c : Ctx R Γ A) τ u i (fr : Frame A t) p
          → KeptFrom (M ⟨ c , coldS true (play τ u i t fr) , absorbed , p ⟩)
              (played (leaf true (play τ u i t fr) false (λ e l′ b′ p′ → ⟨ c , coldS b′ l′ , rising e , p′ ⟩) (λ l′ → ⟨ c , coldS true l′ , absorbed , p ⟩)))
  playing c τ u i (emit a k)  p = lift-≅ c true (≋-out refl refl refl refl refl)
  playing c τ u i (stall k)   p = lift-skip c true refl (≋-by refl refl)
  playing c τ u i (close k)   p = lift-skip c true refl (≋-by (rest-force τ (u ++ [ last ]) (From∞.force k) (envAt c)) (rest-cut τ (u ++ [ last ]) (From∞.force k) (envAt c)))

  runs : ∀ {Γ A} (c : Ctx R Γ A) (s : St Γ A) m p → Owns s m → Inv ⟨ c , s , absorbed , p ⟩ → KeptFrom (M ⟨ c , s , absorbed , p ⟩) (tookᴰ (run c s m p))
  runs c (ofS i q xs) ofM p ofO v with closed c in ce | xs
  ... | true  | ys      = agree-≅ (closed-hides c true (stateᴺ (ofᶜ q i ys) (envAt c)) (stateᴺ idleᶜ (envAt c)) ce (λ n → agreeᵀ-refl n idle))
  ... | false | []      = lift-≅ c true (≋-by refl refl)
  ... | false | x ∷ xs′ = lift-≅ c true (≋-out refl refl refl refl refl)
  runs c (cutS true (attAt q) s)  attM p attO v = ≅-refl
  runs c (cutS false (attAt q) s) attM p attO v with unsub s in e
  ... | s′ , t = unsub-rest c s e
  runs c (takeS i x (cpAt q) s)  cpM  p cpO  v = lift-≅ c true (≋-by refl refl)
  runs c (takeS i x (cutAt q) s) cutM p cutO v with cutᴹ s in e
  ... | s′ , t = cut-rest c s e
  runs c (connS (cs cl sl sa nothing as ow r e) o b) bodyM p bodyO v = ≅-refl
  runs c (connS (cs cl sl sa (just q) as ow r e) o b) bodyM p bodyO v with proj₁ (opened c (cs cl sl sa (just q) as ow r e) o b v)
  ... | refl = lift-≅ c true (conn-src ow sl r e (gh b) (subOr (q ⊕ [ ix 1 ]) o) (envAt c))
  runs c (connS (cs cl sl sa ba nothing ow r e) o b)          srcAttM p srcAttO v = ≅-refl
  runs c (connS (cs cl true sa ba (just q) ow r e) o b)       srcAttM p srcAttO v = ≅-refl
  runs c (connS (cs cl false sa ba (just q) (just w) r e) o b) srcAttM p srcAttO v with unsub o in u
  ... | o′ , t = conn-unsub c (cs cl false sa ba (just q) (just w) r e) b o u
  runs c (connS (cs cl false sa ba (just q) nothing r e) o b)  srcAttM p srcAttO v with unsub o in u
  ... | o′ , t = conn-unsub c (cs cl false sa ba (just q) nothing r e) b o u
  runs c (connS (cs cl sl sa ba as nothing r e) o b)         owedM p owedO v = ≅-refl
  runs c (connS (cs cl sl false ba as (just w) r e) o b)     owedM p owedO v = ≅-refl
  runs c (connS (cs cl sl true ba as (just w) r e) o b)      owedM p owedO v with unsub o in u
  ... | o′ , t = conn-unsub c (cs cl sl true ba as (just w) r e) b o u
  runs c (joinS j false x ((q , nx a) ∷ ib)) joinM p joinO v = ≅-refl
  runs c (joinS j false x ((q , cp) ∷ ib))   joinM p joinO v = ≅-refl
  runs c (joinS j true  x ((q , cp) ∷ ib))   joinM p joinO v with closed c in ce
  ... | false = lift-≅ c true (≋-by refl refl)
  ... | true  = agree-≅ (closed-hides c true (stateᴺ (joinG true x j ((q , cp) ∷ ib)) (envAt c)) (stateᴺ idleᶜ (envAt c)) ce (λ n → agreeᵀ-refl n idle))
  runs c (joinS j true  x ((q , nx a) ∷ ib)) joinM p joinO v with closed c in ce
  ... | false = join-nx c j x q a ib p v
  ... | true  = agree-≅ (closed-hides c true (stateᴺ (joinG true x j ((q , nx a) ∷ ib)) (envAt c)) (stateᴺ (joinG true x j ib) (envAt c)) ce (λ n → agreeᵀ-refl n idle))
  runs c (coldS b (ending e))               leafM p leafO v = lift-≅ c true (≋-by refl refl)
  runs c (coldS false (play τ u i t fr))    leafM p leafO v = ≅-refl
  runs c (coldS false over)                 leafM p leafO v = ≅-refl
  runs c (coldS true over)                  leafM p leafO v with closed c
  ... | true  = ≅-refl
  ... | false = ≅-refl
  runs c (coldS true (play τ u i t fr))     leafM p leafO v with closed c in ce
  ... | true  = agree-≅ (closed-hides c true (stateᴺ (burstᶜ τ u i fr) (envAt c)) (stateᴺ idleᶜ (envAt c)) ce (λ n → agreeᵀ-refl n idle))
  ... | false = playing c τ u i fr p

  ----------------------------------------------------------------------
  -- THE DISPATCH

  refocus : ∀ {Γ A Γ′ A′} (c : Ctx R Γ A) (s : St Γ A) (c′ : Ctx R Γ′ A′) (s′ : St Γ′ A′) p → Unpended s → Unpended s′ → Wf (plug c s)
          → plug c′ s′ ≡ plug c s → M ⟨ c , s , absorbed , p ⟩ ≅ M ⟨ c′ , s′ , absorbed , p ⟩
  refocus c s c′ s′ p u u′ w e =
    ≅-trans (lift-plug c s p u w) (subst (λ t → meaning (gh t) []ᴬ ≅ M ⟨ c′ , s′ , absorbed , p ⟩) e (≅-sym (lift-plug c′ s′ p u′ (subst Wf (sym e) w))))

  kept : ∀ k → Inv k → Kept k
  kept ⟨ c , s , rising e , p ⟩                          v = rises c s e p v
  kept ⟨ c , pend o , subscribing , p ⟩                  v = begins c o p v
  kept ⟨ c , coldS b l , subscribing , p ⟩               v = ≅-refl
  kept ⟨ c , ofS i q xs , subscribing , p ⟩              v = ≅-refl
  kept ⟨ c , doneS , subscribing , p ⟩                   v = ≅-refl
  kept ⟨ c , mapS f s , subscribing , p ⟩                v = ≅-refl
  kept ⟨ c , scanS f z s , subscribing , p ⟩             v = ≅-refl
  kept ⟨ c , cutS l a s , subscribing , p ⟩              v = ≅-refl
  kept ⟨ c , lnS b s , subscribing , p ⟩                 v = ≅-refl
  kept ⟨ c , takeS i q w s , subscribing , p ⟩           v = ≅-refl
  kept ⟨ c , flatS op f d n q o ls , subscribing , p ⟩   v = ≅-refl
  kept ⟨ c , connS k o b , subscribing , p ⟩             v = ≅-refl
  kept ⟨ c , joinS j g x ib , subscribing , p ⟩          v = ≅-refl
  kept ⟨ c , s , absorbed , p ⟩ v with search top (plug c s) in e
  ... | nothing = quiet-empty c s p v e
  ... | just (found (_ , _ , c′ , s′) m key) with search-hit (plug c s) e
  ...   | pl , own = kept-pre (tookᴰ (run c′ s′ m p)) (refocus c s c′ s′ p (Base.settled (Inv.base v)) (owned own) (wfI (Inv.base v)) pl)
                       (runs c′ s′ m p own (inv-at c′ s′ p (owned own) (subst Wf (sym pl) (wfI (Inv.base v))) (subst Frag (sym pl) (Order.shape (Inv.ord v)))))

