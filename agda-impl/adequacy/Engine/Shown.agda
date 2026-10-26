{-# OPTIONS --guardedness #-}

-- A SKIP SHOWN NEXT, FROM THE PICK.  The node the search found still
-- leads every race above it (`adequacy.Engine.Pick.Beat`); a skip it drops
-- at its own key is then the next thing every frame above shows, so each
-- frame passes it (`adequacy.Engine.Drop.Pass`), read off the race frame
-- by frame (`beat-pass`), as a rising lane's order is (`won-clear`).
--
-- A frame with one child passes the skip as it is; a flatMap's lane and
-- outer, and a connect's body, by the race their siblings lost there,
-- read at each position asked of, each no later than the race's key
-- (`cover`).  Below every live source that is the skip's own position;
-- above one, the frames are asked of every position under it (`Sought`),
-- and race past it.
module adequacy.Engine.Shown where

open import Data.Bool using (Bool; true; false)
open import Data.List using ([]; _∷_; _++_; [_]; reverse; _ʳ++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All) renaming (map to allMap; _∷_ to _∷ᴬ_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Tree using (Obs)
open import denotation.MonotonicList.Events using (Events∞; Timeline; Pos; ix; idle; hush)
open import denotation.MonotonicList using (head; Agreeᵀ)
open import denotation.NonExpansive using (_,ˢ_; mapᴱ-ne; scanᴱ-ne; Agreeˢ)
open import denotation.Unfold using (stateᴺ; states; outerᴺ)
import denotation.Unfold as U
open import operation.Key using (Key; at; after; _<ᴷ_)
open import operation.PureObservable using (play; module Machine)
open Machine using (St; mapS; scanS; cutS; lnS; takeS; flatS; connS; coldS; Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter;
  inLanes; inSrc; inBody; plug; closed; Out; search; found; leafM; own; cs; free; cpAt; cutAt; overAt; over)
open import adequacy.Engine.Meaning using (_≋_; ≋-trans; same; ≋-tr; mapped; scanned; gh; lane; lanesL; deadL; outerG; poolRuns; envAt;
  flagOf; lanesFrame; outerFrame-ne; lanesFrame-ne; bodyFrame-ne; connSrc-ne; taking∞-ne;
  srcState; srcG; poolT; outerT)
open import adequacy.Engine.Race using (First; After; NotBefore; TailNotBefore)
open import adequacy.Engine.Head using (Frag; cand; pool-step; <ᴷ-irrefl; ≮ᴷ-trans; ≮<ᴷ; ext-≮)
open import adequacy.Engine.Keys using (Held)
open import adequacy.Engine.Inv using (Unpended)
open import adequacy.Engine.Pick using (Beat; past; KAfter; KNotBefore; Lost; body-link; Before; Race; LaneWon; lane-won; race-steps; after-step;
  lane-sides; outer-link; src-floor)
open import adequacy.Engine.Head.Within using (frag-flat; frag-parts)
open import adequacy.Engine.Ahead using (Under; shows; shows-open; shown)
open import adequacy.Engine.Scope using (Scope; modes; scope-src; Gh)
open import adequacy.Engine.Drop using (Dropsˢ; Pass; SrcPass; mapped-drops; scanned-drops; took-drops; lanes-drops; body-drops;
  outer-drops; src-drops; ≋-⊒)
open import adequacy.Engine.Beside using (Sourced; sourced; sourced-≋)
open import adequacy.Placed.Order using (Atop; Ordered)
open import adequacy.Placed.Trail using (Trailing)
open import adequacy.Engine.FedWalk using (Sought; src-fed)
open import adequacy.Engine.Trails using (shape-st; shape-src)
open import adequacy.Engine.Kept using (live-plug)
open import adequacy.Engine.Plug using (outer-plug; lanes-plugʳ; body-plug)
open Agreeˢ

------------------------------------------------------------------------
-- Where a pass is asked

-- The key a skip's frames race at: its own position, or past it once a
-- source shows it to its joiners.
keyAt : Bool → Pos → Key
keyAt false q = at q
keyAt true  q = after q

postulate
  -- The search finds a node by one of its own marks.
  found-own : ∀ {R} (t : St [] R) {Γ A} {c : Ctx R Γ A} {s m key} → search top t ≡ just (found (Γ , A , c , s) m key)
            → (m , key) ∈ own s
  -- Past a position is after every position under it.
  under-after : ∀ q y → after q <ᴷ at (q ++ y) ≡ false
  -- A SOURCE PAST ITS SKIPS shows no earlier than any position under
  -- them and, hushed, leaves nothing running.
  src-next : ∀ {R Γ X B} v q {P} (c : Ctx R Γ B) sa ba as r en (o : St Γ X) (b : St (X ∷ Γ) B) {h h′ : Events∞ X}
           → Sought v q P → Frag (plug c (connS (cs false true sa ba as nothing r en) o b))
           → h ≋ stateᴺ (gh o) (envAt c) → Dropsˢ P h h′
           → (Events∞.force h′ ≡ hush → ∀ d → Agreeᵀ d (Events∞.cut h′) idle) × (∀ k → Under P k → NotBefore k (shown (Events∞.force h′)))
  -- A LIVE SOURCE, AT ITS CONNECT: its next no earlier than where it
  -- subscribed.
  src-atop : ∀ {R Γ X B} (c : Ctx R Γ B) sa ba as r en (o : St Γ X) (b : St (X ∷ Γ) B)
           → Frag (plug c (connS (cs false true sa ba as nothing r en) o b))
           → Atop r (Events∞.force (stateᴺ (gh o) (envAt c)))
  -- A SOURCE BESIDE ITS BODY, live or closed: its next no earlier than
  -- where it subscribed.
  body-src-atop : ∀ {R Γ X B} (c : Ctx R Γ B) cl sa ba as r en (o : St Γ X) (b : St (X ∷ Γ) B)
                → Frag (plug c (connS (cs cl true sa ba as nothing r en) o b))
                → Atop r (Events∞.force (srcState (srcG (cs cl true sa ba as nothing r en) o) (envAt c)))
  -- The body fed the rest comes after each source skip shows.
  src-body-on : ∀ {R Γ X B} v q {P} (c : Ctx R Γ B) sa ba as r en (o : St Γ X) (b : St (X ∷ Γ) B) {h h′ : Events∞ X}
              → Sought v q P → KAfter (after q) (cand (inBody (cs false true sa ba as nothing r en) o c) b)
              → Before (after q) (own (connS (cs false true sa ba as nothing r en) o b))
              → Frag (plug c (connS (cs false true sa ba as nothing r en) o b))
              → h ≋ stateᴺ (gh o) (envAt c) → Dropsˢ P h h′
              → ∀ k → P k → After (k ++ [ ix 0 ]) (head (Events∞.force (stateᴺ (gh b) (Events∞.force h′ ∷ᴬ envAt c))))

-- A LIVE SOURCE, AT ITS CONNECT: its run in order, what it leaves running
-- trailing it.
src-trails : ∀ {R Γ X B} (c : Ctx R Γ B) sa ba as r en (o : St Γ X) (b : St (X ∷ Γ) B)
           → Held (plug c (connS (cs false true sa ba as nothing r en) o b))
           → Ordered (Events∞.force (stateᴺ (gh o) (envAt c))) × Trailing (stateᴺ (gh o) (envAt c))
src-trails c sa ba as r en o b ft = proj₁ (proj₁ (proj₁ sh)) , proj₂ sh
  where sh = shape-st (inSrc (cs false true sa ba as nothing r en) b c) o ft

-- A SOURCE BESIDE ITS BODY, live or closed, likewise.
body-src-trails : ∀ {R Γ X B} (c : Ctx R Γ B) cl sa ba as r en (o : St Γ X) (b : St (X ∷ Γ) B)
                → Held (plug c (connS (cs cl true sa ba as nothing r en) o b))
                → Ordered (Events∞.force (srcState (srcG (cs cl true sa ba as nothing r en) o) (envAt c)))
                  × Trailing (srcState (srcG (cs cl true sa ba as nothing r en) o) (envAt c))
body-src-trails c cl sa ba as r en o b ft = proj₁ (proj₁ (proj₁ sh)) , proj₂ sh
  where sh = shape-src c (cs cl true sa ba as nothing r en) o b ft

-- A SOURCE'S OWN PASS: its body fed, its own next, the body's next,
-- and what the run it skips to leaves running trailing it.
src-pass : ∀ {R Γ X B} v q {P} (c : Ctx R Γ B) sa ba as r en (o : St Γ X) (b : St (X ∷ Γ) B) {h h′ : Events∞ X}
         → Sought v q P → KAfter (after q) (cand (inBody (cs false true sa ba as nothing r en) o c) b)
         → Before (after q) (own (connS (cs false true sa ba as nothing r en) o b))
         → Held (plug c (connS (cs false true sa ba as nothing r en) o b))
         → h ≋ stateᴺ (gh o) (envAt c) → Dropsˢ P h h′ → Trailing h′
         → (o′ : St Γ X) → Held (plug c (connS (cs false true sa ba as nothing r en) o′ b)) → Unpended o′ → h′ ≋ stateᴺ (gh o′) (envAt c)
         → SrcPass P (stateᴺ (gh b) (Events∞.force h ∷ᴬ envAt c)) (stateᴺ (gh b) (Events∞.force h′ ∷ᴬ envAt c)) h′
src-pass v q c sa ba as r en o b so ka bf ft x d t o′ ft′ u′ x′ = record
  { fed     = src-fed v q c sa ba as r en o b so ka bf ft x d o′ ft′ u′ x′
  ; srcOn   = proj₂ (src-next v q c sa ba as r en o b so (proj₁ ft) x d)
  ; srcHush = proj₁ (src-next v q c sa ba as r en o b so (proj₁ ft) x d)
  ; bodyOn  = src-body-on v q c sa ba as r en o b so ka bf (proj₁ ft) x d
  ; srcTrail = t
  }

-- A live source is subscribed where its connect is.
src-sourced : ∀ {R Γ X B} (c : Ctx R Γ B) sa ba as r en (o : St Γ X) (b : St (X ∷ Γ) B)
            → Held (plug c (connS (cs false true sa ba as nothing r en) o b)) → Sourced r (stateᴺ (gh o) (envAt c))
src-sourced c sa ba as r en o b ft = sourced (src-atop c sa ba as r en o b (proj₁ ft)) (proj₁ tr) (proj₂ tr)
  where tr = src-trails c sa ba as r en o b ft

-- So is one beside its body.
body-sourced : ∀ {R Γ X B} (c : Ctx R Γ B) cl sa ba as r en (o : St Γ X) (b : St (X ∷ Γ) B)
             → Held (plug c (connS (cs cl true sa ba as nothing r en) o b))
             → Sourced r (srcState (srcG (cs cl true sa ba as nothing r en) o) (envAt c))
body-sourced c cl sa ba as r en o b ft = sourced (body-src-atop c cl sa ba as r en o b (proj₁ ft)) (proj₁ tr) (proj₂ tr)
  where tr = body-src-trails c cl sa ba as r en o b ft

-- Every position asked of is no later than the race's key.
cover : ∀ v q {P} → Sought v q P → ∀ k → P k → keyAt v q <ᴷ at k ≡ false
cover false q so k pk with so k pk
... | refl = <ᴷ-irrefl (at q)
cover true q so k pk with so k pk
... | y , refl = under-after q y

-- Nor is the skip's own.
cover-own : ∀ v q → keyAt v q <ᴷ at q ≡ false
cover-own false q = <ᴷ-irrefl (at q)
cover-own true  q = subst (λ p → after q <ᴷ at p ≡ false) (++-identityʳ q) (under-after q [])

-- Above a live source, every position under one asked of.
sought-under : ∀ v q {P} → Sought v q P → Sought true q (Under P)
sought-under false q so _ (k , pk , y , refl) with so k pk
... | refl = y , refl
sought-under true q so _ (k , pk , y , refl) with so k pk
... | y₀ , refl = y₀ ++ y , ++-assoc q y₀ y

past-key : ∀ v q → past false (keyAt v q) ≡ after q
past-key false q = refl
past-key true  q = refl

------------------------------------------------------------------------
-- A race read at a key, read no later

kafter-≤ : ∀ {A} K k (x : Maybe (Key × Out A)) → K <ᴷ at k ≡ false → KAfter K x → KAfter (at k) x
kafter-≤ K k nothing        c w = tt
kafter-≤ K k (just (h , _)) c w = ≮<ᴷ (at k) K h c w

knot-≤ : ∀ {A} K k (x : Maybe (Key × Out A)) → K <ᴷ at k ≡ false → KNotBefore K x → KNotBefore (at k) x
knot-≤ K k nothing        c w = tt
knot-≤ K k (just (h , _)) c w = ≮ᴷ-trans h K (at k) w c

-- A candidate no earlier than a key shows no earlier than it either.
knot-lost : ∀ {A} k (x : Maybe (Key × Out A)) → KNotBefore k x → Lost false k x
knot-lost k nothing                w = tt
knot-lost k (just (at h , _))    w = ≮ᴷ-trans (at (h ++ [ ix 0 ])) (at h) k (ext-≮ h [ ix 0 ]) w
knot-lost k (just (after h , _)) w = w

before-≤ : ∀ K k ms → K <ᴷ at k ≡ false → Before K ms → Before (at k) ms
before-≤ K k ms c = allMap (λ {mk} w → ≮<ᴷ (at k) K (proj₂ mk) c w)

-- A key read past a live source's skips is no earlier than it.
past-≮ : ∀ v key k → key <ᴷ at k ≡ false → past v key <ᴷ at k ≡ false
past-≮ true  key       k c = c
past-≮ false (at p)    k c = ≮ᴷ-trans (after p) (at p) (at k) (subst (λ q → after p <ᴷ at q ≡ false) (++-identityʳ p) (under-after p [])) c
past-≮ false (after p) k c = c

-- Every connect a still find beats on its way up runs its source at or
-- past each position the find's key covers.
beat-scope : ∀ {R Γ A} key k (c : Ctx R Γ A) (s : St Γ A) → Beat key c s → key <ᴷ at k ≡ false → Frag (plug c s) → Gh top (plug c s) → Scope k c
beat-scope key k top                               s b ck ft gt = tt
beat-scope key k (inMap f c)                       s b ck ft gt = beat-scope key k c (mapS f s) b ck ft gt
beat-scope key k (inScan f z c)                    s b ck ft gt = beat-scope key k c (scanS f z s) b ck ft gt
beat-scope key k (inCut l a c)                     s b ck ft gt = beat-scope key k c (cutS l a s) b ck ft gt
beat-scope key k (inLn b′ c)                       s b ck ft gt = beat-scope key k c (lnS b′ s) b ck ft gt
beat-scope key k (inTake i q w c)                  s b ck ft gt = beat-scope key k c (takeS i q w s) b ck ft gt
beat-scope key k (inOuter op f d n q ls c)         s (_ , b) ck ft gt = beat-scope key k c (flatS op f d n q s ls) b ck ft gt
beat-scope key k (inLanes op f d n q o pre post c) s (_ , b) ck ft gt = beat-scope key k c (flatS op f d n q o (pre ʳ++ s ∷ post)) b ck ft gt
beat-scope key k (inSrc kk b′ c)                   s (_ , _ , b) ck ft gt =
  beat-scope (past (over kk) key) k c (connS kk s b′) b (past-≮ (over kk) key k ck) ft gt
beat-scope key k (inBody kk o c)                   s (nb , bf , b) ck ft gt =
  scope-src (modes c) k (srcG kk o) (envAt c)
    (src-floor k c kk o s (knot-lost (at k) (cand (inSrc kk s c) o) (knot-≤ key k (cand (inSrc kk s c) o) ck nb)) (before-≤ key k (own (connS kk o s)) ck bf) ft gt sc) sc
  where sc = beat-scope key k c (connS kk o s) b ck ft gt

race-map : ∀ {R Γ A B} {P P′ : Key → Maybe (Key × Out B) → Set} {k k′} → (∀ x → P k x → P′ k′ x)
         → ∀ (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) acc ls tl
         → Race P k c op f d n q o acc ls tl → Race P′ k′ c op f d n q o acc ls tl
race-map m c op f d n q o acc []       tl r       = tt
race-map m c op f d n q o acc (x ∷ xs) tl (w , r) = m _ w , race-map m c op f d n q o (x ∷ acc) xs tl r

lanewon-≤ : ∀ {R Γ A B} K k (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) pre post (s : St Γ B)
          → K <ᴷ at k ≡ false → LaneWon K c op f d n q o pre post s → LaneWon (at k) c op f d n q o pre post s
lanewon-≤ K k c op f d n q o pre post s le (lane-won wo wold wnew) =
  lane-won (knot-≤ K k _ le wo)
    (race-map (λ x → kafter-≤ K k x le) c op f d n q o [] (reverse pre) (s ∷ post) wold)
    (race-map (λ x → knot-≤ K k x le) c op f d n q o (s ∷ pre) post [] wnew)

------------------------------------------------------------------------
-- The walk

-- A cold's key: where its frame is due.
cold-key : ∀ {R} (t : St [] R) {Γ A} {c : Ctx R Γ A} {τ u i t₀ fr key}
         → search top t ≡ just (found (Γ , A , c , coldS true (play τ u i t₀ fr)) leafM key) → key ≡ at (u ++ [ ix i ])
cold-key t e with found-own t e
... | here refl = refl
... | there ()

-- THE WALK: every frame above the found node passes the skip it drops,
-- each position asked of read off the race there, the run it drops to
-- the meaning of the node it steps to.
beat-pass : ∀ {R Γ A} v q {P : Pos → Set} (c : Ctx R Γ A) (s : St Γ A) f {h h′ : Events∞ A}
          → Sought v q P → Beat (keyAt v q) c s → Held (plug c s) → Gh top (plug c s) → Unpended s
          → shows c f ≡ true → flagOf s ≡ f → h ≋ stateᴺ (gh s) (envAt c) → Dropsˢ P h h′
          → (s′ : St Γ A) → Held (plug c s′) → Unpended s′ → flagOf s′ ≡ f → h′ ≋ stateᴺ (gh s′) (envAt c)
          → Pass P c f h h′
beat-pass v q top s f so w ft gt u sh fl x d s′ ft′ u′ fl′ x′ = tt
beat-pass v q (inMap g c) s f so w ft gt u sh fl x d s′ ft′ u′ fl′ x′ =
  beat-pass v q c (mapS g s) true so w ft gt tt sh refl
    (≋-tr {h′ = mapped g (stateᴺ (gh s) (envAt c))} (λ m → cutˢ (x m) ,ˢ mapᴱ-ne g (nowˢ (x m))) refl refl) (mapped-drops g d)
    (mapS g s′) ft′ tt refl (≋-tr {h′ = mapped g (stateᴺ (gh s′) (envAt c))} (λ m → cutˢ (x′ m) ,ˢ mapᴱ-ne g (nowˢ (x′ m))) refl refl)
beat-pass v q (inScan g z c) s f so w ft gt u sh fl x d s′ ft′ u′ fl′ x′ =
  beat-pass v q c (scanS g z s) true so w ft gt tt sh refl
    (≋-tr {h′ = scanned g z (stateᴺ (gh s) (envAt c))} (λ m → cutˢ (x m) ,ˢ scanᴱ-ne g z (nowˢ (x m))) refl refl) (scanned-drops g z d)
    (scanS g z s′) ft′ tt refl (≋-tr {h′ = scanned g z (stateᴺ (gh s′) (envAt c))} (λ m → cutˢ (x′ m) ,ˢ scanᴱ-ne g z (nowˢ (x′ m))) refl refl)
beat-pass v q (inCut true a c) s f so w ft gt u sh fl x d s′ ft′ u′ fl′ x′ =
  beat-pass v q c (cutS true a s) true so w ft gt tt sh refl x d (cutS true a s′) ft′ tt refl x′
beat-pass v q (inCut false a c) s f so w ft gt u () fl x d s′ ft′ u′ fl′ x′
beat-pass v q (inLn b c) s f so w ft gt u sh fl x d s′ ft′ u′ fl′ x′ =
  beat-pass v q c (lnS b s) b so w ft gt tt sh refl x d (lnS b s′) ft′ tt refl x′
beat-pass v q (inTake i p free c) s f so w ft gt u sh fl x d s′ ft′ u′ fl′ x′ =
  beat-pass v q c (takeS i p free s) true so w ft gt tt sh refl (≋-tr (λ m → taking∞-ne i p free (x m)) refl refl) (took-drops i p d)
    (takeS i p free s′) ft′ tt refl (≋-tr (λ m → taking∞-ne i p free (x′ m)) refl refl)
beat-pass v q (inTake i p (cpAt _) c) s f so w ft gt u () fl x d s′ ft′ u′ fl′ x′
beat-pass v q (inTake i p (cutAt _) c) s f so w ft gt u () fl x d s′ ft′ u′ fl′ x′
beat-pass v q (inTake i p (overAt _) c) s f so w ft gt u () fl x d s′ ft′ u′ fl′ x′
beat-pass v q (inOuter op g true n p ls c) s f so w ft gt u () fl x d s′ ft′ u′ fl′ x′
beat-pass v q {P} (inOuter op g false n p ls c) s f so bw@(r , w) ft gt u sh fl x d s′ ft′ u′ fl′ x′ =
  ol , beat-pass v q c (flatS op g false n p s ls) true so w ft gt tt sh refl
         (≋-trans (λ m → outerFrame-ne op (lane g) false p (lanesL ls) (deadL ls) (envAt c) (x m)) (outer-plug op g false n p ls s (envAt c)))
         (outer-drops op (lane g) p (lanesL ls) (deadL ls) (envAt c) ol d)
         (flatS op g false n p s′ ls) ft′ tt refl
         (≋-trans (λ m → outerFrame-ne op (lane g) false p (lanesL ls) (deadL ls) (envAt c) (x′ m)) (outer-plug op g false n p ls s′ (envAt c)))
  where
    parts = frag-parts op g false n p s ls (frag-flat c op g false n p s ls (proj₁ ft))
    ol : ∀ k → P k → All (λ l → After k (head (Events∞.force l))) (states (lanesL ls) (envAt c)) × TailNotBefore k (poolT (deadL ls) (envAt c))
    ol k pk =
      outer-link c k op g n p s ls (proj₁ ft) (beat-scope (keyAt v q) k (inOuter op g false n p ls c) s bw (cover v q so k pk) (proj₁ ft) gt)
        (race-steps KAfter (After k) (keyAt v q) (λ y st a ag → after-step k y st (kafter-≤ (keyAt v q) k y (cover v q so k pk) a) ag)
           c op g false n p s [] ls [] (shows-open c true sh) (proj₂ parts) r)
        (pool-step false s ls (proj₁ parts) (proj₂ parts) (λ ()))
beat-pass v q (inLanes op g dd n p o pre post c) s false so w ft gt u () fl x d s′ ft′ u′ fl′ x′
beat-pass v q {P} (inLanes op g dd n p o pre post c) s true {h} so bw@(l , w) ft gt u sh fl x d s′ ft′ u′ fl′ x′ =
  fi , beat-pass v q c (flatS op g dd n p o (pre ʳ++ s ∷ post)) true so w ft gt tt sh refl
         (≋-trans (λ m → lanesFrame-ne op (lane g) dd p (gh o) (reverse pre) post true (envAt c) (x m))
           (subst (λ b → lanesFrame op (lane g) dd p (gh o) (reverse pre) post b (envAt c) (stateᴺ (gh s) (envAt c))
                         ≋ stateᴺ (gh (flatS op g dd n p o (pre ʳ++ s ∷ post))) (envAt c))
                  fl (lanes-plugʳ op g dd n p o pre post s (envAt c))))
         (lanes-drops op (lane g) dd p (gh o) (reverse pre) post (envAt c) fi d)
         (flatS op g dd n p o (pre ʳ++ s′ ∷ post)) ft′ tt refl
         (≋-trans (λ m → lanesFrame-ne op (lane g) dd p (gh o) (reverse pre) post true (envAt c) (x′ m))
           (subst (λ b → lanesFrame op (lane g) dd p (gh o) (reverse pre) post b (envAt c) (stateᴺ (gh s′) (envAt c))
                         ≋ stateᴺ (gh (flatS op g dd n p o (pre ʳ++ s′ ∷ post))) (envAt c))
                  fl′ (lanes-plugʳ op g dd n p o pre post s′ (envAt c))))
  where
    fi : ∀ k → P k → First k (outerᴺ (lane g) (outerG dd (gh o)) (envAt c)) (states (lanesL post) (envAt c))
                       (states (lanesL (reverse pre)) (envAt c)) (outerT dd (gh o) (envAt c) (poolRuns (reverse pre) post true (envAt c) h))
    fi k pk = lane-sides k c op g dd n p o pre post s (shows-open c true sh)
                (beat-scope (keyAt v q) k (inLanes op g dd n p o pre post c) s bw (cover v q so k pk) (proj₁ ft) gt)
                (lanewon-≤ (keyAt v q) k c op g dd n p o pre post s (cover v q so k pk) l) (proj₁ ft) (frag-flat c op g dd n p o (pre ʳ++ s ∷ post) (proj₁ ft))
beat-pass v q {P} (inSrc (cs false true sa ba as nothing r en) b c) s f so (ka , bf , bt) ft gt u sh fl x d s′ ft′ u′ fl′ x′ =
  sourced-≋ x (src-sourced c sa ba as r en s b ft) , sp , beat-pass true q c (connS kk s b) true (sought-under v q so) (subst (λ K → Beat K c (connS kk s b)) (past-key v q) bt) ft gt tt sh refl
         (≋-trans (λ m → connSrc-ne false r en (gh b) (envAt c) (x m)) (live-plug sa ba as r en b s (envAt c) u))
         (src-drops r en (gh b) (envAt c) (sourced-≋ x (src-sourced c sa ba as r en s b ft)) sp d)
         (connS kk s′ b) ft′ tt refl
         (≋-trans (λ m → connSrc-ne false r en (gh b) (envAt c) (x′ m)) (live-plug sa ba as r en b s′ (envAt c) u′))
  where
    kk = cs false true sa ba as nothing r en
    sp = src-pass v q c sa ba as r en s b so (subst (λ K → KAfter K (cand (inBody kk s c) b)) (past-key v q) ka)
           (subst (λ K → Before K (own (connS kk s b))) (past-key v q) bf) ft x d
           (Sourced.srcTrail (sourced-≋ x′ (src-sourced c sa ba as r en s′ b ft′))) s′ ft′ u′ x′
beat-pass v q (inSrc (cs false true sa ba as (just _) r en) b c) s f so w ft gt u () fl x d s′ ft′ u′ fl′ x′
beat-pass v q (inSrc (cs false false sa ba as ow r en) b c) s f so w ft gt u () fl x d s′ ft′ u′ fl′ x′
beat-pass v q (inSrc (cs true sl sa ba as ow r en) b c) s f so w ft gt u () fl x d s′ ft′ u′ fl′ x′
beat-pass v q {P} (inBody (cs cl true sa ba as nothing r en) o c) s f so (nb , ob , w) ft gt u sh fl x d s′ ft′ u′ fl′ x′ =
  hu , nbk , sd , beat-pass v q c (connS kk o s) true so w ft gt tt sh refl
               (≋-trans (λ m → bodyFrame-ne kk o (envAt c) (x m)) (body-plug kk o s (envAt c)))
               (body-drops r hu nbk sd (Sourced.srcTrail sd) (≋-⊒ (λ m → same m (srcState (srcG kk o) (envAt c)))) d)
               (connS kk o s′) ft′ tt refl
               (≋-trans (λ m → bodyFrame-ne kk o (envAt c) (x′ m)) (body-plug kk o s′ (envAt c)))
  where
    kk = cs cl true sa ba as nothing r en
    sd = body-sourced c cl sa ba as r en o s ft
    bl : ∀ k → keyAt v q <ᴷ at k ≡ false
       → (Events∞.force (srcState (srcG kk o) (envAt c)) ≡ hush → ∀ d → Agreeᵀ d (Events∞.cut (srcState (srcG kk o) (envAt c))) idle)
         × NotBefore k (shown (Events∞.force (srcState (srcG kk o) (envAt c))))
    bl k le = body-link k c kk o s (proj₁ ft) (shows-open c true sh) refl (knot-lost (at k) (cand (inSrc kk s c) o) (knot-≤ (keyAt v q) k (cand (inSrc kk s c) o) le nb))
                (before-≤ (keyAt v q) k (own (connS kk o s)) le ob)
    hu = proj₁ (bl q (cover-own v q))
    nbk : ∀ k → P k → NotBefore k (shown (Events∞.force (srcState (srcG kk o) (envAt c))))
    nbk k pk = proj₂ (bl k (cover v q so k pk))
beat-pass v q (inBody (cs cl true sa ba as (just _) r en) o c) s f so w ft gt u () fl x d s′ ft′ u′ fl′ x′
beat-pass v q (inBody (cs cl false sa ba as ow r en) o c) s f so w ft gt u () fl x d s′ ft′ u′ fl′ x′
