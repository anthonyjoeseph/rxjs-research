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
-- Below every connect's source the drop is exact (`≋-⊒`); a source
-- frame's `SrcPass` is where a genuine erasure enters, and `⊒` erases
-- only finitely many skips between two it keeps.
module adequacy.Engine.Passed where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_; [_]; reverse)
open import Data.List.Relation.Unary.All using (All) renaming (_∷_ to _∷ᴬ_; map to mapᴬ)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl)

open import denotation.MonotonicList.Events using (Events; Events∞; Pos; Tail; out; skip; end; hush; ix; ≮-trans)
open import Data.Unit using (tt)
open import denotation.MonotonicList using (Agree; skip⁼)
open import denotation.Unfold using (Node; NEnv; stateᴺ; states; outerᴺ)
open import operation.PureObservable using (module Machine)
open Machine using (St; CS; Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody; cs; free)
open import adequacy.Engine.Meaning using (same; srcState; srcG; envAt; gh; lane; lanesL; deadL; outerG; outerT; poolRuns; poolT;
  laneRuns; outerOf; laneᴹ)
open import adequacy.Engine.Race using (NotBefore)
open import adequacy.Engine.Ahead using (Under; shown)
open import adequacy.Engine.Keys using (FlatAt; ConnAt; module ConnAt; Keyed; LaneKeys; _∷ᴷ_)
open import adequacy.Placed.FlatOrder using (module FlatOrder)
open import adequacy.Placed.Trail using (Spread)
open import adequacy.Engine.Erased using (every-drops; fresh-drops; drops-fresh; spread-drops; every-⊒; everyT-⊒; fresh-⊒)
open import adequacy.Placed.Order using (Owned; EveryT; Every∞; Disjoint; every-mono; everyT-mono)
open import Relation.Nullary using (¬_)
open import adequacy.Placed.Burst using (Fresh; FreshRun; module Bursting)
open import adequacy.Engine.Above using (Above)
open import adequacy.Engine.Drop using (Dropsˢ; dropˢ; dropsˢ; Fed; Pass; SrcPass; mapped-drops; scanned-drops; took-drops; lanes-drops; outer-drops; src-drops;
  body-drops; ≋-⊒)
open import adequacy.Engine.Beside using (Sourced)

open Events∞

postulate
  -- THE FLIGHT KEPT: a live connect's source dropping a skip its body
  -- passes keeps every key of its body, read fed the rest.
  body-keyed-drops : ∀ {Γ X B P} k (b : St (X ∷ Γ) B) (ρ : NEnv Γ) {h h′ : Events∞ X}
                   → Sourced (CS.srcAt k) h → SrcPass P (stateᴺ (gh b) (force h ∷ᴬ ρ)) (stateᴺ (gh b) (force h′ ∷ᴬ ρ)) h′
                   → Dropsˢ P h h′ → Keyed b (force h ∷ᴬ ρ) → Keyed b (force h′ ∷ᴬ ρ)

-- A merge's outer dropping skips keeps its keys: its lanes and pool are
-- untouched, and what it keeps of its outer is read past the drop.
outer-flat-drops : ∀ {Γ A B P} (g : A → Pos → Node Γ B) (ls ds : List (Node Γ B)) (ρ : NEnv Γ) {h h′ : Events∞ A}
                 → Dropsˢ P h h′
                 → FlatAt ρ (just (outerOf g ρ h)) (states ls ρ) (poolT ds ρ) → FlatAt ρ (just (outerOf g ρ h′)) (states ls ρ) (poolT ds ρ)
outer-flat-drops g ls ds ρ d (p , hp , al , rs , lk , pt , as , (sp , kk) , (st , ev , wd)) =
  p , hp , al , rs , lk , pt , mapᴬ (λ a → every-drops a d′) as , (spread-drops sp d′ , every-drops kk d′)
  , (st , everyT-mono (λ k (n , fc) → n , every-drops {P = λ y → ¬ Owned (y ++ [ ix 1 ]) k × Disjoint y k} fc d′) (poolT ds ρ) ev , wd)
  where d′ = mapped-drops (laneᴹ g ρ) d

-- What a source shows past a skip it drops is no earlier than the skip,
-- so a body cued fresh before the skip is cued fresh past it.
past-skip : ∀ {A X} r l q {x : Events A} {s} (e′ : Events X) → Agree 1 x (skip q s) → Bursting.Cue r l x
          → NotBefore (q ++ [ ix 0 ]) (shown e′) → Bursting.Cue r l e′
past-skip r l q (out k _ _) (skip⁼ _ _) c n = ≮-trans l (q ++ [ ix 0 ]) (k ++ [ ix 0 ]) c n
past-skip r l q (skip k _)  (skip⁼ _ _) c n = ≮-trans l (q ++ [ ix 0 ]) (k ++ [ ix 0 ]) c n
past-skip r l q (end k)     (skip⁼ _ _) c n = ≮-trans l (q ++ [ ix 0 ]) (k ++ [ ix 0 ]) c n
past-skip r l q hush        (skip⁼ _ _) c n = tt

drop-cue : ∀ {X P} r l {h h′ : Events∞ X} → Dropsˢ P h h′ → (∀ k → Under P k → NotBefore k (shown (force h′)))
         → Bursting.Cue r l (force h) → Bursting.Cue r l (force h′)
drop-cue r l {h′ = h′} (dropˢ {k} pk ag _)  on c = past-skip r l k (force h′) (ag 1) c (on (k ++ [ ix 0 ]) (k , pk , [ ix 0 ] , refl))
drop-cue r l {h′ = h′} (dropsˢ {k} pk ag _) on c = past-skip r l k (force h′) (ag 1) c (on (k ++ [ ix 0 ]) (k , pk , [ ix 0 ] , refl))

-- A body fed the rest keeps what it keeps of its positions.
fed-every : ∀ {B} {P Q : Pos → Set} {β β′ : Events∞ B} → Fed P β β′ → Every∞ Q β → Every∞ Q β′
fed-every (inj₁ e) q = every-⊒ q e
fed-every (inj₂ d) q = every-drops q d

fed-fresh : ∀ {B} {P : Pos → Set} {p} {β β′ : Events∞ B} → Fed P β β′ → FreshRun p (force β) → FreshRun p (force β′)
fed-fresh (inj₁ e) f = fresh-⊒ f e
fed-fresh (inj₂ d) f = fresh-drops f d

every∞-mono : ∀ {A} {P Q : Pos → Set} → (∀ y → P y → Q y) → (e : Events∞ A) → Every∞ P e → Every∞ Q e
every∞-mono f e (pe , pt) = every-mono f (force e) pe , everyT-mono f (cut e) pt

-- A merge's live lane dropping skips keeps its keys: the pool reads
-- nothing of a live lane, and the lane's own keys are read past the drop.
lanes-hole : ∀ {B} p (as : List (Events∞ B)) {h h′ : Events∞ B} {bs rs}
           → (∀ {r} → Every∞ (FlatOrder.Under p r) h × FlatOrder.Ok p r × Spread (force h) → Every∞ (FlatOrder.Under p r) h′ × FlatOrder.Ok p r × Spread (force h′))
           → LaneKeys p (as ++ h ∷ bs) rs → LaneKeys p (as ++ h′ ∷ bs) rs
lanes-hole p []       f (x ∷ᴷ k) = f x ∷ᴷ k
lanes-hole p (a ∷ as) f (x ∷ᴷ k) = x ∷ᴷ lanes-hole p as f k

lanes-flat-drops : ∀ {Γ A B P} (g : A → Pos → Node Γ B) d (o : Node Γ A) pre post (ρ : NEnv Γ) {h h′ : Events∞ B}
                 → Dropsˢ P h h′
                 → FlatAt ρ (outerᴺ g (outerG d o) ρ) (laneRuns pre post true ρ h) (outerT d o ρ (poolRuns pre post true ρ h))
                 → FlatAt ρ (outerᴺ g (outerG d o) ρ) (laneRuns pre post true ρ h′) (outerT d o ρ (poolRuns pre post true ρ h′))
lanes-flat-drops g d o pre post ρ dr (p , hp , al , rs , lk , rest) =
  p , hp , al , rs , lanes-hole p (states (lanesL post) ρ) (λ (u , ok , sp) → every-drops u dr , ok , spread-drops sp dr) lk , rest

-- A source no earlier than a skip cues a body fresh past it.
nb-cue : ∀ {A} r k (e : Events A) → NotBefore k (shown e) → Bursting.Cue r k e
nb-cue r k (out _ _ _) n = n
nb-cue r k (skip _ _)  n = n
nb-cue r k (end _)     n = n
nb-cue r k hush        n = tt

conn-cue : ∀ {A : Set} {P : Pos → Set} r p (σ : Events∞ A) {t : Tail} → (∀ q → P q → NotBefore q (shown (force σ)))
         → Σ Pos (λ l → P l × Owned p l × EveryT (Fresh p l) t) → Σ Pos (λ l → Owned p l × Bursting.Cue r l (force σ) × EveryT (Fresh p l) t)
conn-cue r p σ nb (l , q , o , f) = l , o , nb-cue r l (force σ) (nb l q) , f

-- A live connect's source dropping skips its body passes keeps the
-- connect's keys: the source's read past the drop, the body's past what
-- it is fed, the body cued fresh past the source's drop.
src-at-drops : ∀ {Γ X B P} k (b : St (X ∷ Γ) B) (ρ : NEnv Γ) {h h′ : Events∞ X}
             → Sourced (CS.srcAt k) h → SrcPass P (stateᴺ (gh b) (force h ∷ᴬ ρ)) (stateᴺ (gh b) (force h′ ∷ᴬ ρ)) h′
             → Dropsˢ P h h′
             → ConnAt k (stateᴺ (gh b) (force h ∷ᴬ ρ)) h ρ × Keyed b (force h ∷ᴬ ρ)
             → ConnAt k (stateᴺ (gh b) (force h′ ∷ᴬ ρ)) h′ ρ × Keyed b (force h′ ∷ᴬ ρ)
src-at-drops k b ρ {h} {h′} so sp d (ca , ky) = record
  { mark = mark ; hm = hm ; at = at ; kb = fed-every fd kb ; kr = fed-every fd kr ; fr = fed-fresh fd fr
  ; cue = cue′ fd cue
  ; ks = every-drops ks d ; rs = every-drops rs d
  ; ub = fed-every fd (every∞-mono (λ _ u → every-drops u d) (stateᴺ (gh b) (force h ∷ᴬ ρ)) ub) ; sub = sub ; ends = ends }
  , body-keyed-drops k b ρ so sp d ky
  where
    open ConnAt ca
    fd = SrcPass.fed sp
    cue′ : Fed _ (stateᴺ (gh b) (force h ∷ᴬ ρ)) (stateᴺ (gh b) (force h′ ∷ᴬ ρ))
         → Σ Pos (λ l → Owned (mark ++ [ ix 0 ]) l × Bursting.Cue (mark ++ [ ix 1 ]) l (force h) × EveryT (Fresh (mark ++ [ ix 0 ]) l) (cut (stateᴺ (gh b) (force h ∷ᴬ ρ))))
         → Σ Pos (λ l → Owned (mark ++ [ ix 0 ]) l × Bursting.Cue (mark ++ [ ix 1 ]) l (force h′) × EveryT (Fresh (mark ++ [ ix 0 ]) l) (cut (stateᴺ (gh b) (force h′ ∷ᴬ ρ))))
    cue′ (inj₁ e)  (l , o , c , f) = l , o , drop-cue (mark ++ [ ix 1 ]) l d (SrcPass.srcOn sp) c , everyT-⊒ f e
    cue′ (inj₂ dβ) _               = conn-cue (mark ++ [ ix 1 ]) (mark ++ [ ix 0 ]) h′ (SrcPass.srcOn sp) (drops-fresh dβ kb fr)

-- A live connect's body dropping skips no earlier than its source shows
-- keeps the connect's keys: each is read past the drop, and the body is
-- cued fresh past the last skip dropped.
body-at-drops : ∀ {Γ X B P} k (σ : Events∞ X) (ρ : NEnv Γ) {h h′ : Events∞ B}
              → (∀ q → P q → NotBefore q (shown (force σ))) → Dropsˢ P h h′
              → ConnAt k h σ ρ → ConnAt k h′ σ ρ
body-at-drops k σ ρ nb d ca = record
  { mark = mark ; hm = hm ; at = at ; kb = every-drops kb d ; kr = every-drops kr d ; fr = fresh-drops fr d
  ; cue = conn-cue (mark ++ [ ix 1 ]) (mark ++ [ ix 0 ]) σ nb (drops-fresh d kb fr)
  ; ks = ks ; rs = rs ; ub = every-drops ub d ; sub = sub ; ends = ends }
  where open ConnAt ca

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
  (outer-flat-drops (lane g) (lanesL ls) (deadL ls) (envAt c) d fa , kl)
  , above-drops P c true (outer-drops op (lane g) q (lanesL ls) (deadL ls) (envAt c) o d) ps ab
above-drops P (inLanes op g d′ n q o pre post c) true d (fi , ps) ((fa , rest) , ab) =
  (lanes-flat-drops (lane g) d′ (gh o) (reverse pre) post (envAt c) d fa , rest)
  , above-drops P c true (lanes-drops op (lane g) d′ q (gh o) (reverse pre) post (envAt c) fi d) ps ab
above-drops P (inSrc (cs false true sa ba as nothing r en) b c) f d (so , sp , ps) (ck , ab) =
  src-at-drops (cs false true sa ba as nothing r en) b (envAt c) so sp d ck
  , above-drops (Under P) c true (src-drops r en (gh b) (envAt c) so sp d) ps ab
above-drops P (inBody (cs cl true sa ba as nothing r en) o c) f d (hc , bp , so , ps) ((ca , ko , sh) , ab) =
  (body-at-drops (cs cl true sa ba as nothing r en) (srcState (srcG (cs cl true sa ba as nothing r en) o) (envAt c)) (envAt c) bp d ca , ko , sh)
  , above-drops P c true (body-drops r hc bp so (Sourced.srcTrail so) (≋-⊒ (λ n → same n (srcState (srcG (cs cl true sa ba as nothing r en) o) (envAt c)))) d) ps ab
