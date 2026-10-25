{-# OPTIONS --guardedness #-}

-- WHAT THE FRAMES ABOVE A HOLE KEEP, PAST A SKIP THE HOLE DROPS, when
-- every frame shows the skip next (`adequacy.Engine.Drop.Pass`): each
-- frame's run drops the skip as the hole's does, so each frame's own
-- facts are read past it (`above-drops`), as `lift-drops` carries the
-- drop itself to the root.
--
-- A frame with one child keeps nothing of its own.  A merge keys its
-- outer's run or its lane's run, a connect its body fed the source's run
-- and its body's run: each of those drops the skip, and the facts the
-- frame keeps of it are read past the skip.
--
-- The leaves are suspect through `adequacy.Engine.Drop.Dropsˢ`'s last
-- conjunct: `⊒` erases at every finite depth, so an endless run of erased
-- skips under a lane's root relates to a run whose later events leave it,
-- and `Every∞ (Under r)` and `Spread` are not read across.  Below every
-- connect's source the drop is exact (`≋-⊒`); a source frame's
-- `SrcPass` is where a genuine erasure enters.  Either `⊒` erases only
-- finitely often, or the leaves keep the drop exact below the source.
module adequacy.Engine.Passed where

open import Data.Bool using (true; false)
open import Data.List using (List; _∷_; reverse)
open import Data.List.Relation.Unary.All using (All) renaming (_∷_ to _∷ᴬ_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_)

open import denotation.MonotonicList.Events using (Events∞; Pos)
open import denotation.MonotonicList using (head)
open import denotation.Unfold using (Node; NEnv; stateᴺ; states; outerᴺ)
open import operation.PureObservable using (module Machine)
open Machine using (St; CS; Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody; cs; free)
open import adequacy.Engine.Meaning using (same; srcState; srcG; envAt; gh; lane; lanesL; deadL; outerG; outerT; poolRuns; poolT;
  laneRuns; outerOf)
open import adequacy.Engine.Race using (First; After; NotBefore; TailNotBefore)
open import adequacy.Engine.Ahead using (Under; shown)
open import adequacy.Engine.Keys using (FlatAt; ConnAt; Keyed)
open import adequacy.Engine.Above using (Above)
open import adequacy.Engine.Drop using (Dropsˢ; Pass; SrcPass; mapped-drops; scanned-drops; took-drops; lanes-drops; outer-drops; src-drops;
  body-drops; ≋-⊒)
open import adequacy.Engine.Beside using (Sourced)

open Events∞

postulate
  -- THE FLIGHT KEPT: a merge's outer dropping a skip ahead of every
  -- lane's next and every tail its ended lanes left keeps its keys.
  outer-flat-drops : ∀ {Γ A B P} (g : A → Pos → Node Γ B) (ls ds : List (Node Γ B)) (ρ : NEnv Γ) {h h′ : Events∞ A}
                   → (∀ k → P k → All (λ l → After k (head (force l))) (states ls ρ) × TailNotBefore k (poolT ds ρ))
                   → Dropsˢ P h h′
                   → FlatAt ρ (just (outerOf g ρ h)) (states ls ρ) (poolT ds ρ) → FlatAt ρ (just (outerOf g ρ h′)) (states ls ρ) (poolT ds ρ)
  -- THE FLIGHT KEPT: a merge's live lane dropping a skip first among its
  -- parts keeps its keys.
  lanes-flat-drops : ∀ {Γ A B P} (g : A → Pos → Node Γ B) d (o : Node Γ A) pre post (ρ : NEnv Γ) {h h′ : Events∞ B}
                   → (∀ k → P k → First k (outerᴺ g (outerG d o) ρ) (states (lanesL post) ρ) (states (lanesL pre) ρ) (outerT d o ρ (poolRuns pre post true ρ h)))
                   → Dropsˢ P h h′
                   → FlatAt ρ (outerᴺ g (outerG d o) ρ) (laneRuns pre post true ρ h) (outerT d o ρ (poolRuns pre post true ρ h))
                   → FlatAt ρ (outerᴺ g (outerG d o) ρ) (laneRuns pre post true ρ h′) (outerT d o ρ (poolRuns pre post true ρ h′))
  -- THE FLIGHT KEPT: a live connect's source dropping a skip its body
  -- passes keeps the connect's keys, its body keyed fed the rest.
  src-at-drops : ∀ {Γ X B P} k (b : St (X ∷ Γ) B) (ρ : NEnv Γ) {h h′ : Events∞ X}
               → Sourced (CS.srcAt k) h → SrcPass P (stateᴺ (gh b) (force h ∷ᴬ ρ)) (stateᴺ (gh b) (force h′ ∷ᴬ ρ)) h′
               → Dropsˢ P h h′
               → ConnAt k (stateᴺ (gh b) (force h ∷ᴬ ρ)) h ρ × Keyed b (force h ∷ᴬ ρ)
               → ConnAt k (stateᴺ (gh b) (force h′ ∷ᴬ ρ)) h′ ρ × Keyed b (force h′ ∷ᴬ ρ)
  -- THE FLIGHT KEPT: a live connect's body dropping a skip no earlier
  -- than its source shows keeps the connect's keys.
  body-at-drops : ∀ {Γ X B P} k (σ : Events∞ X) (ρ : NEnv Γ) {h h′ : Events∞ B}
                → (∀ q → P q → NotBefore q (shown (force σ))) → Dropsˢ P h h′
                → ConnAt k h σ ρ → ConnAt k h′ σ ρ

-- THE FRAMES ABOVE, PAST THE SKIP: skips dropped at the hole, each passed
-- by every frame above, leave every frame's own facts standing.
above-drops : ∀ {R Γ A} P (c : Ctx R Γ A) f {h h′ : Events∞ A} → Dropsˢ P h h′ → Pass P c f h h′ → Above c f h → Above c f h′
above-drops P top                               f d ps       ab = ab
above-drops P (inMap g c)                       f d ps       ab = above-drops P c true (mapped-drops g d) ps ab
above-drops P (inScan g z c)                    f d ps       ab = above-drops P c true (scanned-drops g z d) ps ab
above-drops P (inCut true a c)                  f d ps       ab = above-drops P c true d ps ab
above-drops P (inLn b c)                        f d ps       ab = above-drops P c b d ps ab
above-drops P (inTake i q free c)               f d ps       (t , ab) = t , above-drops P c true (took-drops i q d) ps ab
above-drops P (inOuter op g false n q ls c)     f d (o , ps) ((fa , kl) , ab) =
  (outer-flat-drops (lane g) (lanesL ls) (deadL ls) (envAt c) o d fa , kl)
  , above-drops P c true (outer-drops op (lane g) q (lanesL ls) (deadL ls) (envAt c) o d) ps ab
above-drops P (inLanes op g d′ n q o pre post c) true d (fi , ps) ((fa , rest) , ab) =
  (lanes-flat-drops (lane g) d′ (gh o) (reverse pre) post (envAt c) fi d fa , rest)
  , above-drops P c true (lanes-drops op (lane g) d′ q (gh o) (reverse pre) post (envAt c) fi d) ps ab
above-drops P (inSrc (cs false true sa ba as nothing r en) b c) f d (so , sp , ps) (ck , ab) =
  src-at-drops (cs false true sa ba as nothing r en) b (envAt c) so sp d ck
  , above-drops (Under P) c true (src-drops r en (gh b) (envAt c) so sp d) ps ab
above-drops P (inBody (cs cl true sa ba as nothing r en) o c) f d (hc , bp , so , ps) ((ca , ko , sh) , ab) =
  (body-at-drops (cs cl true sa ba as nothing r en) (srcState (srcG (cs cl true sa ba as nothing r en) o) (envAt c)) (envAt c) bp d ca , ko , sh)
  , above-drops P c true (body-drops r hc bp so (Sourced.srcTrail so) (≋-⊒ (λ n → same n (srcState (srcG (cs cl true sa ba as nothing r en) o) (envAt c)))) d) ps ab
