{-# OPTIONS --guardedness #-}

-- A SKIP SHOWN NEXT, FROM THE PICK.  The node the search found leads
-- every race above it (`adequacy.Engine.Pick.Won`); a skip it drops at its
-- own key is then the next thing every frame above shows, so each frame
-- passes it (`adequacy.Engine.Drop.Pass`), read off the race frame by
-- frame (`won-pass`), as a rising lane's order is (`won-clear`).
--
-- A still candidate keeps its key through every retag, so each frame's
-- race is read at the skip's own position.  A frame with one child passes
-- it as it is; a flatMap's lane and outer by the race their siblings lost;
-- a connect's body by its source's candidate, which lost the tie-break
-- only by being no earlier than the body once shifted: the tree never
-- puts a body just past its source (`Untied`), so the source is no earlier
-- than the body unshifted (`shift-between`).
module adequacy.Engine.Shown where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_; [_]; reverse; _ʳ++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂; uncurry)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Tree using (Obs; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.MonotonicList.Events using (Events∞; Timeline; ix; idle; hush)
open import denotation.MonotonicList using (head; Agreeᵀ)
open import denotation.NonExpansive using (_,ˢ_; mapᴱ-ne; scanᴱ-ne; Agreeˢ)
open import denotation.Unfold using (stateᴺ; states; outerᴺ; step; headˢ; hushˢ)
open import operation.Key using (Key; at; _<ᴷ_)
open import operation.PureObservable using (play; module Machine)
open Machine using (St; mapS; scanS; cutS; lnS; takeS; flatS; connS; coldS; Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter;
  inLanes; inSrc; inBody; plug; closed; Out; still; search; found; leafM; Mark; own; cs; free; cpAt; cutAt; overAt; laneT; cutT;
  over; shift; _⊕_)
open import adequacy.Engine.Meaning using (_≋_; ≋-trans; ≋-tr; mapped; scanned; gh; lane; lanesL; deadL; poolG; outerG; outerT; poolRuns; envAt; flagOf; lanesFrame;
  outerFrame-ne; lanesFrame-ne; bodyFrame-ne; taking∞-ne; srcState; srcG; poolT)
open import adequacy.Engine.Race using (First; After; NotBefore; TailNotBefore)
open import adequacy.Engine.Head using (Frag; Lanes; cand; pool-step)
open import adequacy.Engine.Pick using (Won; KAfter; KNotBefore; SrcBehind; Untie; Untied; untied-at; Before; race-steps; after-step;
  lane-sides; frag-flat)
open import adequacy.Engine.Drop using (Dropsˢ; Pass; shows; shows-open; shown; mapped-drops; scanned-drops; took-drops; lanes-drops;
  body-drops; outer-drops)
open import adequacy.Engine.Kept using (outer-plug; lanes-plugʳ; body-plug)
open Agreeˢ

postulate
  -- The search finds a node by one of its own marks.
  found-own : ∀ {R} (t : St [] R) {Γ A} {c : Ctx R Γ A} {s m key} → search top t ≡ just (found (Γ , A , c , s) m key)
            → (m , key) ∈ own s
  -- Nothing lies strictly between a key and its `shift`.
  shift-between : ∀ h k → shift h <ᴷ k ≡ false → (shift h ≡ k → ⊥) → h <ᴷ k ≡ false
  -- An outer first: its flatMap's lanes, each after it as the race read
  -- them, are after it in the meaning; a pool the stepper hushes leaves
  -- nothing running before it.
  outer-link : ∀ {R Γ A B} (c : Ctx R Γ B) q op (f : A → Obs Timeline Γ B) n q′ (o : St Γ A) ls
             → Frag (plug c (flatS op f false n q′ o ls))
             → All (λ m → After q (headˢ (step m))) (lanesL ls) → step (poolG false (gh o) (deadL ls)) ≡ hushˢ
             → All (λ l → After q (head (Events∞.force l))) (states (lanesL ls) (envAt c)) × TailNotBefore q (poolT (deadL ls) (envAt c))
  -- A body first: the source's candidate, no earlier than it, and the
  -- connect's own marks, after it, put the source's meaning no earlier;
  -- a source hushed leaves nothing running.
  body-link : ∀ {R Γ X B} q (c : Ctx R Γ B) kk (o : St Γ X) (b : St (X ∷ Γ) B)
            → Frag (plug c (connS kk o b)) → closed c ≡ false → over kk ≡ false
            → KNotBefore (at q) (cand (inSrc kk b c) o) → Before (at q) (own (connS kk o b))
            → (Events∞.force (srcState (srcG kk o) (envAt c)) ≡ hush → ∀ d → Agreeᵀ d (Events∞.cut (srcState (srcG kk o) (envAt c))) idle)
              × NotBefore q (shown (Events∞.force (srcState (srcG kk o) (envAt c))))
  -- A SOURCE FIRST: its skips pass its connect with what the joiners
  -- saw of them, each under the skip's position, and every frame above.
  -- The race above reads the shifted key alone, while the frames above
  -- are asked of every position under the skip's.
  src-climb : ∀ {R Γ X B} q (c : Ctx R Γ B) kk (o : St Γ X) (b : St (X ∷ Γ) B) f {h h′ : Events∞ X}
            → shows (inSrc kk b c) f ≡ true → Won (at q , still) (inSrc kk b c) o
            → Frag (plug c (connS kk o b)) → Untied top (plug c (connS kk o b))
            → h ≋ stateᴺ (gh o) (envAt c) → Dropsˢ (_≡ q) h h′ → Pass (_≡ q) (inSrc kk b c) f h h′

-- A cold's key: where its frame is due.
cold-key : ∀ {R} (t : St [] R) {Γ A} {c : Ctx R Γ A} {τ u i t₀ fr key}
         → search top t ≡ just (found (Γ , A , c , coldS true (play τ u i t₀ fr)) leafM key) → key ≡ at (u ++ [ ix i ])
cold-key t e with found-own t e
... | here refl = refl
... | there ()

-- A flatMap of the fragment: its outer and its lanes are.
frag-parts : ∀ {Γ A B} op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) ls → Frag (flatS op f d n q o ls) → Frag o × Lanes ls
frag-parts (mergeᶠ nothing)  f d n []      o ls (fo , fl , _) = fo , fl
frag-parts (mergeᶠ nothing)  f d n (_ ∷ _) o ls ()
frag-parts (mergeᶠ (just m)) f d n q       o ls (fo , fl , _) = fo , fl
frag-parts switchᶠ           f d n q       o ls (fo , fl , _) = fo , fl
frag-parts exhaustᶠ          f d n q       o ls (fo , fl , _) = fo , fl

-- A live lane's still candidate passes its flatMap's retag unchanged.
lane-still : ∀ {R Γ A B} d n (q : List A) {b} k {c : Ctx R Γ B} {t} → b ≡ true
           → Won (uncurry (laneT d n q) (cutT b k still)) c t → Won (k , still) c t
lane-still d n []      k refl w = w
lane-still d n (_ ∷ _) k refl w = w

-- The source the body beat, untied from it, is no earlier.
behind : ∀ {A B} (x : Maybe (Key × Out A)) {y : Maybe (Key × Out B)} {k o′} → y ≡ just (k , o′) → Untie x y → SrcBehind false k x
       → KNotBefore k x
behind nothing         e    u sb = tt
behind (just (h , _)) refl u sb = shift-between h _ sb u

-- THE WALK: every frame above the found node passes the skip it drops
-- at its key.
won-pass : ∀ {R Γ A} q (c : Ctx R Γ A) (s : St Γ A) f {h h′ : Events∞ A}
         → Won (at q , still) c s → Frag (plug c s) → Untied top (plug c s)
         → shows c f ≡ true → flagOf s ≡ f → h ≋ stateᴺ (gh s) (envAt c) → Dropsˢ (_≡ q) h h′
         → Pass (_≡ q) c f h h′
won-pass q top s f w ft ut sh fl x d = tt
won-pass q (inMap g c) s f w ft ut sh fl x d =
  won-pass q c (mapS g s) true w ft ut sh refl (≋-tr {h′ = mapped g (stateᴺ (gh s) (envAt c))} (λ m → cutˢ (x m) ,ˢ mapᴱ-ne g (nowˢ (x m))) refl refl) (mapped-drops g d)
won-pass q (inScan g z c) s f w ft ut sh fl x d =
  won-pass q c (scanS g z s) true w ft ut sh refl (≋-tr {h′ = scanned g z (stateᴺ (gh s) (envAt c))} (λ m → cutˢ (x m) ,ˢ scanᴱ-ne g z (nowˢ (x m))) refl refl) (scanned-drops g z d)
won-pass q (inCut true a c) s f w ft ut sh fl x d = won-pass q c (cutS true a s) true w ft ut sh refl x d
won-pass q (inCut false a c) s f w ft ut () fl x d
won-pass q (inLn b c) s f w ft ut sh fl x d = won-pass q c (lnS b s) b w ft ut sh refl x d
won-pass q (inTake i p free c) s f w ft ut sh fl x d =
  won-pass q c (takeS i p free s) true w ft ut sh refl (≋-tr (λ m → taking∞-ne i p free (x m)) refl refl) (took-drops i p d)
won-pass q (inTake i p (cpAt _) c) s f w ft ut () fl x d
won-pass q (inTake i p (cutAt _) c) s f w ft ut () fl x d
won-pass q (inTake i p (overAt _) c) s f w ft ut () fl x d
won-pass q (inOuter op g true n p ls c) s f w ft ut () fl x d
won-pass q (inOuter op g false n p ls c) s f (r , w) ft ut sh fl x d =
  ol , won-pass q c (flatS op g false n p s ls) true w ft ut sh refl
         (≋-trans (λ m → outerFrame-ne op (lane g) false p (lanesL ls) (deadL ls) (envAt c) (x m)) (outer-plug op g false n p ls s (envAt c)))
         (outer-drops op (lane g) p (lanesL ls) (deadL ls) (envAt c) ol d)
  where
    parts = frag-parts op g false n p s ls (frag-flat c op g false n p s ls ft)
    ol : ∀ k → k ≡ q → All (λ l → After k (head (Events∞.force l))) (states (lanesL ls) (envAt c)) × TailNotBefore k (poolT (deadL ls) (envAt c))
    ol k refl =
      outer-link c q op g n p s ls ft
        (race-steps KAfter (After q) (at q) (after-step q) c op g false n p s [] ls [] (shows-open c true sh) (proj₂ parts) r)
        (pool-step false s ls (proj₁ parts) (proj₂ parts) (λ ()))
won-pass q (inLanes op g dd n p o pre post c) s false w ft ut () fl x d
won-pass q (inLanes op g dd n p o pre post c) s true {h} (l , w) ft ut sh fl x d =
  fi , won-pass q c (flatS op g dd n p o (pre ʳ++ s ∷ post)) true (lane-still dd n p (at q) {c} {flatS op g dd n p o (pre ʳ++ s ∷ post)} fl w) ft ut sh refl
         (≋-trans (λ m → lanesFrame-ne op (lane g) dd p (gh o) (reverse pre) post true (envAt c) (x m))
           (subst (λ b → lanesFrame op (lane g) dd p (gh o) (reverse pre) post b (envAt c) (stateᴺ (gh s) (envAt c))
                         ≋ stateᴺ (gh (flatS op g dd n p o (pre ʳ++ s ∷ post))) (envAt c))
                  fl (lanes-plugʳ op g dd n p o pre post s (envAt c))))
         (lanes-drops op (lane g) dd p (gh o) (reverse pre) post (envAt c) fi d)
  where
    fi : ∀ k → k ≡ q → First k (outerᴺ (lane g) (outerG dd (gh o)) (envAt c)) (states (lanesL post) (envAt c))
                         (states (lanesL (reverse pre)) (envAt c)) (outerT dd (gh o) (envAt c) (poolRuns (reverse pre) post true (envAt c) h))
    fi k refl = lane-sides q c op g dd n p o pre post s (shows-open c true sh) l ft (frag-flat c op g dd n p o (pre ʳ++ s ∷ post) ft)
won-pass q (inSrc kk b c) s f w ft ut sh fl x d = src-climb q c kk s b f sh w ft ut x d
won-pass q (inBody (cs cl true sa ba as nothing r en) o c) s f (ce , sb , ob , w) ft ut sh fl x d =
  proj₁ bl , (λ { k refl → proj₂ bl })
  , won-pass q c (connS kk o s) true w ft ut sh refl
      (≋-trans (λ m → bodyFrame-ne kk o (envAt c) (x m)) (body-plug kk o s (envAt c)))
      (body-drops r (srcState (srcG kk o) (envAt c)) (proj₁ bl) (λ { k refl → proj₂ bl }) d)
  where
    kk = cs cl true sa ba as nothing r en
    bl = body-link q c kk o s ft (shows-open c true sh) refl
           (behind (cand (inSrc kk s c) o) ce (proj₁ (untied-at c (connS kk o s) ut) refl) sb) ob
won-pass q (inBody (cs cl true sa ba as (just _) r en) o c) s f w ft ut () fl x d
won-pass q (inBody (cs cl false sa ba as ow r en) o c) s f w ft ut () fl x d
