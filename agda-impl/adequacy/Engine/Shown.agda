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
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; [_]; reverse; _ʳ++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All) renaming (map to allMap; _∷_ to _∷ᴬ_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing; is-just)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Tree using (Obs)
open import denotation.MonotonicList.Events using (Events; Events∞; Timeline; Pos; ix; idle; hush; _<ᵖ_; out; skip; end; inside)
open import denotation.MonotonicList using (head; Agreeᵀ)
open import denotation.NonExpansive using (_,ˢ_; mapᴱ-ne; scanᴱ-ne; Agreeˢ)
open import denotation.Unfold using (stateᴺ; states; outerᴺ; NEnv)
import denotation.Unfold as U
open import operation.Key using (Key; at; after; _<ᴷ_)
open import operation.PureObservable using (play; module Machine)
open Machine using (St; mapS; scanS; cutS; lnS; takeS; flatS; connS; coldS; Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter;
  inLanes; inSrc; inBody; plug; closed; Out; search; found; leafM; own; cs; free; cpAt; cutAt; overAt; over)
open import adequacy.Engine.Meaning using (_≋_; ≋-trans; same; ≋-tr; mapped; scanned; took; outerFrame; connSrc; bodyConn; gh; lane; lanesL; deadL; outerG; poolRuns; envAt;
  flagOf; lanesFrame; outerFrame-ne; lanesFrame-ne; bodyFrame-ne; connSrc-ne; taking∞-ne;
  srcState; srcG; poolT; outerT)
open import adequacy.Engine.Race using (First; After; NotBefore; TailNotBefore)
open import adequacy.Engine.Head using (Frag; cand; pool-step; <ᴷ-irrefl; ≮ᴷ-trans; ≮<ᴷ; ext-≮)
open import adequacy.Engine.Inv using (Unpended)
open import adequacy.Engine.Pick using (Beat; past; KAfter; KNotBefore; Lost; body-link; Before; Race; LaneWon; lane-won; race-steps; after-step;
  lane-sides; frag-flat; frag-parts; outer-link)
open import adequacy.Engine.Ahead using (Ahead; Under; shows; shows-open; shown)
open import adequacy.Engine.Drop using (Dropsˢ; Pass; SrcPass; Fed; mapped-drops; scanned-drops;
  took-drops; lanes-drops; body-drops; outer-drops; src-drops; ≋-⊒)
open import adequacy.Engine.Beside using (Sourced; sourced; sourced-≋)
open import adequacy.Placed.Order using (Atop; Ordered)
open import adequacy.Placed.Trail using (Trailing)
open import adequacy.Engine.Kept using (outer-plug; lanes-plugʳ; body-plug; live-plug)
open Agreeˢ

------------------------------------------------------------------------
-- Where a pass is asked

-- The key a skip's frames race at: its own position, or past it once a
-- source shows it to its joiners.
keyAt : Bool → Pos → Key
keyAt false q = at q
keyAt true  q = after q

-- The positions a pass is asked of: the skip's own, or any under it.
Sought : Bool → Pos → (Pos → Set) → Set
Sought false q P = ∀ k → P k → k ≡ q
Sought true  q P = ∀ k → P k → Σ Pos λ y → k ≡ q ++ y

-- NOTHING OWED A SOURCE: each joiner of connect `i` in a node, not yet
-- told its end, joined before `q` and holds nothing it was fed, and no
-- defer holds a step of `i` still to be fed.  A lane not yet begun is not
-- asked.
mutual
  Caught : ∀ {Γ A B} → A ∈ Γ → Pos → U.Node Γ B → Set
  Caught i q (U.mapᶜ f n)                 = Caught i q n
  Caught i q (U.scanᶜ f z n)              = Caught i q n
  Caught i q (U.takeWhileᶜ w t n)         = Caught i q n
  Caught i q (U.flatMapᶜ op g o ls qs pl) = Caughtᴹ i q o × Caughtᴸ i q ls × Caught i q pl
  Caught i q (U.joinᶜ j p xs nothing)     = is-just (U.same? i j) ≡ false ⊎ (xs ≡ [] × p <ᵖ q ≡ true)
  Caught i q (U.connectᶜ r b s)           = Caught (there i) q b × Caughtˢ i q s
  Caught i q (U.deferᶜ l p ns)            = Unnoticed i ns
  Caught i q (U.endingᶜ p n)              = Caught i q n
  Caught i q (U.restᶜ n)                  = Caught i q n
  Caught i q (U.unionᶜ x y)               = Caught i q x × Caught i q y
  Caught i q (U.burstingᶜ r t)            = Caught i q t
  Caught i q (U.underᶜ s b)               = Caughtˢ i q s × Caught (there i) q b
  Caught i q _                            = ⊤

  Caughtᴹ : ∀ {Γ A B} → A ∈ Γ → Pos → Maybe (U.Node Γ B) → Set
  Caughtᴹ i q nothing  = ⊤
  Caughtᴹ i q (just n) = Caught i q n

  Caughtᴸ : ∀ {Γ A B} → A ∈ Γ → Pos → List (U.Node Γ B) → Set
  Caughtᴸ i q []       = ⊤
  Caughtᴸ i q (n ∷ ns) = Caught i q n × Caughtᴸ i q ns

  Caughtˢ : ∀ {Γ A B} → A ∈ Γ → Pos → U.Source Γ B → Set
  Caughtˢ i q (U.live s)    = Caught i q s
  Caughtˢ i q (U.ended c t) = Caught i q t

  Unnoticed : ∀ {Γ A} → A ∈ Γ → List (U.Notice Γ) → Set
  Unnoticed i []                   = ⊤
  Unnoticed i (U.notice j q a ∷ ns) = is-just (U.same? i j) ≡ false × Unnoticed i ns

-- A RUN NOTHING NESTS IN: no event lies under the skip just before it,
-- to `n` events.  Rejoined, an event under a skip comes before it (an
-- `ix` mark is below a `sub` one), so a skip erased before an event under
-- it is no longer erasable.
Flat : ∀ {A} → ℕ → Events A → Set
Flat zero    e           = ⊤
Flat (suc n) (out p a r) = Flat n (Events∞.force r)
Flat (suc n) (skip p r)  = Unnested p (head (Events∞.force r)) × Flat n (Events∞.force r)
  where Unnested : Pos → Maybe Pos → Set
        Unnested p nothing  = ⊤
        Unnested p (just y) = inside p y ≡ false
Flat (suc n) (end p)     = ⊤
Flat (suc n) hush        = ⊤

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
  -- Its run in order, what it leaves running trailing it.
  src-trails : ∀ {R Γ X B} (c : Ctx R Γ B) sa ba as r en (o : St Γ X) (b : St (X ∷ Γ) B)
             → Frag (plug c (connS (cs false true sa ba as nothing r en) o b))
             → Ordered (Events∞.force (stateᴺ (gh o) (envAt c))) × Trailing (stateᴺ (gh o) (envAt c))
  -- A SOURCE BESIDE ITS BODY, live or closed: its next no earlier than
  -- where it subscribed.
  body-src-atop : ∀ {R Γ X B} (c : Ctx R Γ B) cl sa ba as r en (o : St Γ X) (b : St (X ∷ Γ) B)
                → Frag (plug c (connS (cs cl true sa ba as nothing r en) o b))
                → Atop r (Events∞.force (srcState (srcG (cs cl true sa ba as nothing r en) o) (envAt c)))
  -- Its run in order, what it leaves running trailing it.
  body-src-trails : ∀ {R Γ X B} (c : Ctx R Γ B) cl sa ba as r en (o : St Γ X) (b : St (X ∷ Γ) B)
                  → Frag (plug c (connS (cs cl true sa ba as nothing r en) o b))
                  → Ordered (Events∞.force (srcState (srcG (cs cl true sa ba as nothing r en) o) (envAt c)))
                    × Trailing (srcState (srcG (cs cl true sa ba as nothing r en) o) (envAt c))
  -- NOTHING OWED A LIVE SOURCE: its body's joiners of it joined before
  -- its skip and hold nothing fed, and no defer there a step of it.
  caught : ∀ {R Γ X B} q (c : Ctx R Γ B) sa ba as r en (o : St Γ X) (b : St (X ∷ Γ) B)
         → KAfter (after q) (cand (inBody (cs false true sa ba as nothing r en) o c) b)
         → Before (after q) (own (connS (cs false true sa ba as nothing r en) o b))
         → Frag (plug c (connS (cs false true sa ba as nothing r en) o b))
         → Caught (here refl) q (gh b)
  -- A LIVE SOURCE'S RUN nests nothing.
  src-flat : ∀ {R Γ X B} (c : Ctx R Γ B) sa ba as r en (o : St Γ X) (b : St (X ∷ Γ) B) {h : Events∞ X}
           → Frag (plug c (connS (cs false true sa ba as nothing r en) o b))
           → h ≋ stateᴺ (gh o) (envAt c) → ∀ m → Flat m (Events∞.force h)
  -- A NODE FED A SOURCE'S SKIPS, owing it nothing: it drops its own
  -- leading skips, each under one of them, and erases none or more past
  -- them, to the node fed the rest.
  node-fed : ∀ {Γ X B} v q {P} (n : U.Node (X ∷ Γ) B) (ρ : NEnv Γ) {h h′ : Events∞ X}
           → Sought v q P → Caught (here refl) q n → (∀ m → Flat m (Events∞.force h)) → Dropsˢ P h h′
           → Fed P (stateᴺ n (Events∞.force h ∷ᴬ ρ)) (stateᴺ n (Events∞.force h′ ∷ᴬ ρ))
  -- The body fed the rest comes after each source skip shows.
  src-body-on : ∀ {R Γ X B} v q {P} (c : Ctx R Γ B) sa ba as r en (o : St Γ X) (b : St (X ∷ Γ) B) {h h′ : Events∞ X}
              → Sought v q P → KAfter (after q) (cand (inBody (cs false true sa ba as nothing r en) o c) b)
              → Before (after q) (own (connS (cs false true sa ba as nothing r en) o b))
              → Frag (plug c (connS (cs false true sa ba as nothing r en) o b))
              → h ≋ stateᴺ (gh o) (envAt c) → Dropsˢ P h h′
              → ∀ k → P k → After (k ++ [ ix 0 ]) (head (Events∞.force (stateᴺ (gh b) (Events∞.force h′ ∷ᴬ envAt c))))

-- A SOURCE'S SKIPS FED ITS BODY: the body fed a live source's skips
-- drops its own leading skips, each under one of them, and erases none
-- or more past them, to the body fed the rest.
src-fed : ∀ {R Γ X B} v q {P} (c : Ctx R Γ B) sa ba as r en (o : St Γ X) (b : St (X ∷ Γ) B) {h h′ : Events∞ X}
        → Sought v q P → KAfter (after q) (cand (inBody (cs false true sa ba as nothing r en) o c) b)
        → Before (after q) (own (connS (cs false true sa ba as nothing r en) o b))
        → Frag (plug c (connS (cs false true sa ba as nothing r en) o b))
        → h ≋ stateᴺ (gh o) (envAt c) → Dropsˢ P h h′
        → Fed P (stateᴺ (gh b) (Events∞.force h ∷ᴬ envAt c)) (stateᴺ (gh b) (Events∞.force h′ ∷ᴬ envAt c))
src-fed v q c sa ba as r en o b so ka bf ft x d =
  node-fed v q (gh b) (envAt c) so (caught q c sa ba as r en o b ka bf ft) (src-flat c sa ba as r en o b ft x) d

-- A SOURCE'S OWN PASS: its body fed, its own next, the body's next,
-- and what the run it skips to leaves running trailing it.
src-pass : ∀ {R Γ X B} v q {P} (c : Ctx R Γ B) sa ba as r en (o : St Γ X) (b : St (X ∷ Γ) B) {h h′ : Events∞ X}
         → Sought v q P → KAfter (after q) (cand (inBody (cs false true sa ba as nothing r en) o c) b)
         → Before (after q) (own (connS (cs false true sa ba as nothing r en) o b))
         → Frag (plug c (connS (cs false true sa ba as nothing r en) o b))
         → h ≋ stateᴺ (gh o) (envAt c) → Dropsˢ P h h′ → Trailing h′
         → SrcPass P (stateᴺ (gh b) (Events∞.force h ∷ᴬ envAt c)) (stateᴺ (gh b) (Events∞.force h′ ∷ᴬ envAt c)) h′
src-pass v q c sa ba as r en o b so ka bf ft x d t = record
  { fed     = src-fed v q c sa ba as r en o b so ka bf ft x d
  ; srcOn   = proj₂ (src-next v q c sa ba as r en o b so ft x d)
  ; srcHush = proj₁ (src-next v q c sa ba as r en o b so ft x d)
  ; bodyOn  = src-body-on v q c sa ba as r en o b so ka bf ft x d
  ; srcTrail = t
  }

-- A live source is subscribed where its connect is.
src-sourced : ∀ {R Γ X B} (c : Ctx R Γ B) sa ba as r en (o : St Γ X) (b : St (X ∷ Γ) B)
            → Frag (plug c (connS (cs false true sa ba as nothing r en) o b)) → Sourced r (stateᴺ (gh o) (envAt c))
src-sourced c sa ba as r en o b ft = sourced (src-atop c sa ba as r en o b ft) (proj₁ tr) (proj₂ tr)
  where tr = src-trails c sa ba as r en o b ft

-- So is one beside its body.
body-sourced : ∀ {R Γ X B} (c : Ctx R Γ B) cl sa ba as r en (o : St Γ X) (b : St (X ∷ Γ) B)
             → Frag (plug c (connS (cs cl true sa ba as nothing r en) o b))
             → Sourced r (srcState (srcG (cs cl true sa ba as nothing r en) o) (envAt c))
body-sourced c cl sa ba as r en o b ft = sourced (body-src-atop c cl sa ba as r en o b ft) (proj₁ tr) (proj₂ tr)
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
          → Sought v q P → Beat (keyAt v q) c s → Frag (plug c s) → Unpended s
          → shows c f ≡ true → flagOf s ≡ f → h ≋ stateᴺ (gh s) (envAt c) → Dropsˢ P h h′
          → (s′ : St Γ A) → Frag (plug c s′) → Unpended s′ → flagOf s′ ≡ f → h′ ≋ stateᴺ (gh s′) (envAt c)
          → Pass P c f h h′
beat-pass v q top s f so w ft u sh fl x d s′ ft′ u′ fl′ x′ = tt
beat-pass v q (inMap g c) s f so w ft u sh fl x d s′ ft′ u′ fl′ x′ =
  beat-pass v q c (mapS g s) true so w ft tt sh refl
    (≋-tr {h′ = mapped g (stateᴺ (gh s) (envAt c))} (λ m → cutˢ (x m) ,ˢ mapᴱ-ne g (nowˢ (x m))) refl refl) (mapped-drops g d)
    (mapS g s′) ft′ tt refl (≋-tr {h′ = mapped g (stateᴺ (gh s′) (envAt c))} (λ m → cutˢ (x′ m) ,ˢ mapᴱ-ne g (nowˢ (x′ m))) refl refl)
beat-pass v q (inScan g z c) s f so w ft u sh fl x d s′ ft′ u′ fl′ x′ =
  beat-pass v q c (scanS g z s) true so w ft tt sh refl
    (≋-tr {h′ = scanned g z (stateᴺ (gh s) (envAt c))} (λ m → cutˢ (x m) ,ˢ scanᴱ-ne g z (nowˢ (x m))) refl refl) (scanned-drops g z d)
    (scanS g z s′) ft′ tt refl (≋-tr {h′ = scanned g z (stateᴺ (gh s′) (envAt c))} (λ m → cutˢ (x′ m) ,ˢ scanᴱ-ne g z (nowˢ (x′ m))) refl refl)
beat-pass v q (inCut true a c) s f so w ft u sh fl x d s′ ft′ u′ fl′ x′ =
  beat-pass v q c (cutS true a s) true so w ft tt sh refl x d (cutS true a s′) ft′ tt refl x′
beat-pass v q (inCut false a c) s f so w ft u () fl x d s′ ft′ u′ fl′ x′
beat-pass v q (inLn b c) s f so w ft u sh fl x d s′ ft′ u′ fl′ x′ =
  beat-pass v q c (lnS b s) b so w ft tt sh refl x d (lnS b s′) ft′ tt refl x′
beat-pass v q (inTake i p free c) s f so w ft u sh fl x d s′ ft′ u′ fl′ x′ =
  beat-pass v q c (takeS i p free s) true so w ft tt sh refl (≋-tr (λ m → taking∞-ne i p free (x m)) refl refl) (took-drops i p d)
    (takeS i p free s′) ft′ tt refl (≋-tr (λ m → taking∞-ne i p free (x′ m)) refl refl)
beat-pass v q (inTake i p (cpAt _) c) s f so w ft u () fl x d s′ ft′ u′ fl′ x′
beat-pass v q (inTake i p (cutAt _) c) s f so w ft u () fl x d s′ ft′ u′ fl′ x′
beat-pass v q (inTake i p (overAt _) c) s f so w ft u () fl x d s′ ft′ u′ fl′ x′
beat-pass v q (inOuter op g true n p ls c) s f so w ft u () fl x d s′ ft′ u′ fl′ x′
beat-pass v q {P} (inOuter op g false n p ls c) s f so (r , w) ft u sh fl x d s′ ft′ u′ fl′ x′ =
  ol , beat-pass v q c (flatS op g false n p s ls) true so w ft tt sh refl
         (≋-trans (λ m → outerFrame-ne op (lane g) false p (lanesL ls) (deadL ls) (envAt c) (x m)) (outer-plug op g false n p ls s (envAt c)))
         (outer-drops op (lane g) p (lanesL ls) (deadL ls) (envAt c) ol d)
         (flatS op g false n p s′ ls) ft′ tt refl
         (≋-trans (λ m → outerFrame-ne op (lane g) false p (lanesL ls) (deadL ls) (envAt c) (x′ m)) (outer-plug op g false n p ls s′ (envAt c)))
  where
    parts = frag-parts op g false n p s ls (frag-flat c op g false n p s ls ft)
    ol : ∀ k → P k → All (λ l → After k (head (Events∞.force l))) (states (lanesL ls) (envAt c)) × TailNotBefore k (poolT (deadL ls) (envAt c))
    ol k pk =
      outer-link c k op g n p s ls ft
        (race-steps KAfter (After k) (keyAt v q) (λ y st a ag → after-step k y st (kafter-≤ (keyAt v q) k y (cover v q so k pk) a) ag)
           c op g false n p s [] ls [] (shows-open c true sh) (proj₂ parts) r)
        (pool-step false s ls (proj₁ parts) (proj₂ parts) (λ ()))
beat-pass v q (inLanes op g dd n p o pre post c) s false so w ft u () fl x d s′ ft′ u′ fl′ x′
beat-pass v q {P} (inLanes op g dd n p o pre post c) s true {h} so (l , w) ft u sh fl x d s′ ft′ u′ fl′ x′ =
  fi , beat-pass v q c (flatS op g dd n p o (pre ʳ++ s ∷ post)) true so w ft tt sh refl
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
                (lanewon-≤ (keyAt v q) k c op g dd n p o pre post s (cover v q so k pk) l) ft (frag-flat c op g dd n p o (pre ʳ++ s ∷ post) ft)
beat-pass v q {P} (inSrc (cs false true sa ba as nothing r en) b c) s f so (ka , bf , bt) ft u sh fl x d s′ ft′ u′ fl′ x′ =
  sourced-≋ x (src-sourced c sa ba as r en s b ft) , sp , beat-pass true q c (connS kk s b) true (sought-under v q so) (subst (λ K → Beat K c (connS kk s b)) (past-key v q) bt) ft tt sh refl
         (≋-trans (λ m → connSrc-ne false r en (gh b) (envAt c) (x m)) (live-plug sa ba as r en b s (envAt c) u))
         (src-drops r en (gh b) (envAt c) (sourced-≋ x (src-sourced c sa ba as r en s b ft)) sp d)
         (connS kk s′ b) ft′ tt refl
         (≋-trans (λ m → connSrc-ne false r en (gh b) (envAt c) (x′ m)) (live-plug sa ba as r en b s′ (envAt c) u′))
  where
    kk = cs false true sa ba as nothing r en
    sp = src-pass v q c sa ba as r en s b so (subst (λ K → KAfter K (cand (inBody kk s c) b)) (past-key v q) ka)
           (subst (λ K → Before K (own (connS kk s b))) (past-key v q) bf) ft x d
           (Sourced.srcTrail (sourced-≋ x′ (src-sourced c sa ba as r en s′ b ft′)))
beat-pass v q (inSrc (cs false true sa ba as (just _) r en) b c) s f so w ft u () fl x d s′ ft′ u′ fl′ x′
beat-pass v q (inSrc (cs false false sa ba as ow r en) b c) s f so w ft u () fl x d s′ ft′ u′ fl′ x′
beat-pass v q (inSrc (cs true sl sa ba as ow r en) b c) s f so w ft u () fl x d s′ ft′ u′ fl′ x′
beat-pass v q {P} (inBody (cs cl true sa ba as nothing r en) o c) s f so (nb , ob , w) ft u sh fl x d s′ ft′ u′ fl′ x′ =
  hu , nbk , sd , beat-pass v q c (connS kk o s) true so w ft tt sh refl
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
    bl k le = body-link k c kk o s ft (shows-open c true sh) refl (knot-lost (at k) (cand (inSrc kk s c) o) (knot-≤ (keyAt v q) k (cand (inSrc kk s c) o) le nb))
                (before-≤ (keyAt v q) k (own (connS kk o s)) le ob)
    hu = proj₁ (bl q (cover-own v q))
    nbk : ∀ k → P k → NotBefore k (shown (Events∞.force (srcState (srcG kk o) (envAt c))))
    nbk k pk = proj₂ (bl k (cover v q so k pk))
beat-pass v q (inBody (cs cl true sa ba as (just _) r en) o c) s f so w ft u () fl x d s′ ft′ u′ fl′ x′
beat-pass v q (inBody (cs cl false sa ba as ow r en) o c) s f so w ft u () fl x d s′ ft′ u′ fl′ x′

------------------------------------------------------------------------
-- A pass, apart from what the frames ask

-- What a pass asks of the run itself: at each live source above, that
-- the source's skips pass its connect.
Links : ∀ {R Γ A} → (Pos → Set) → Ctx R Γ A → Bool → Events∞ A → Events∞ A → Set
Links P top                                                 f h h′ = ⊤
Links P (inMap g c)                                         f h h′ = Links P c true (mapped g h) (mapped g h′)
Links P (inScan g z c)                                      f h h′ = Links P c true (scanned g z h) (scanned g z h′)
Links P (inCut l a c)                                       f h h′ = Links P c true h h′
Links P (inLn b c)                                          f h h′ = Links P c b h h′
Links P (inTake i q free c)                                 f h h′ = Links P c true (took i q h) (took i q h′)
Links P (inTake i q (cpAt _) c)                             f h h′ = ⊤
Links P (inTake i q (cutAt _) c)                            f h h′ = ⊤
Links P (inTake i q (overAt _) c)                           f h h′ = ⊤
Links P (inOuter op g d n q ls c)                           f h h′ =
  Links P c true (outerFrame op (lane g) d q (lanesL ls) (deadL ls) (envAt c) h) (outerFrame op (lane g) d q (lanesL ls) (deadL ls) (envAt c) h′)
Links P (inLanes op g d n q o pre post c)                   f h h′ =
  Links P c true (lanesFrame op (lane g) d q (gh o) (reverse pre) post f (envAt c) h) (lanesFrame op (lane g) d q (gh o) (reverse pre) post f (envAt c) h′)
Links P (inSrc (cs false true sa ba as nothing r en) b c)   f h h′ =
  Sourced r h × SrcPass P (stateᴺ (gh b) (Events∞.force h ∷ᴬ envAt c)) (stateᴺ (gh b) (Events∞.force h′ ∷ᴬ envAt c)) h′
  × Links (Under P) c true (connSrc false r en (gh b) (envAt c) h) (connSrc false r en (gh b) (envAt c) h′)
Links P (inSrc (cs false true sa ba as (just _) r en) b c)  f h h′ = ⊤
Links P (inSrc (cs false false sa ba as ow r en) b c)       f h h′ = ⊤
Links P (inSrc (cs true sl sa ba as ow r en) b c)           f h h′ = ⊤
Links P (inBody (cs cl true sa ba as nothing r en) o c)     f h h′ =
  Sourced r (srcState (srcG (cs cl true sa ba as nothing r en) o) (envAt c))
  × Links P c true (bodyConn r (srcState (srcG (cs cl true sa ba as nothing r en) o) (envAt c)) h)
                 (bodyConn r (srcState (srcG (cs cl true sa ba as nothing r en) o) (envAt c)) h′)
Links P (inBody (cs cl true sa ba as (just _) r en) o c)    f h h′ = ⊤
Links P (inBody (cs cl false sa ba as ow r en) o c)         f h h′ = ⊤

-- A pass is what the frames ask and what the run links.
pass-of : ∀ {R Γ A} P (c : Ctx R Γ A) f {h h′ : Events∞ A} → Ahead P c f → Links P c f h h′ → Pass P c f h h′
pass-of P top                                                 f a l = tt
pass-of P (inMap g c)                                         f a l = pass-of P c true a l
pass-of P (inScan g z c)                                      f a l = pass-of P c true a l
pass-of P (inCut true x c)                                    f a l = pass-of P c true a l
pass-of P (inCut false x c)                                   f () l
pass-of P (inLn b c)                                          f a l = pass-of P c b a l
pass-of P (inTake i q free c)                                 f a l = pass-of P c true a l
pass-of P (inTake i q (cpAt _) c)                             f () l
pass-of P (inTake i q (cutAt _) c)                            f () l
pass-of P (inTake i q (overAt _) c)                           f () l
pass-of P (inOuter op g true n q ls c)                        f () l
pass-of P (inOuter op g false n q ls c)                       f (o , a) l = o , pass-of P c true a l
pass-of P (inLanes op g d n q o pre post c)                   false () l
pass-of P (inLanes op g d n q o pre post c)                   true (s , a) l = s , pass-of P c true a l
pass-of P (inSrc (cs false true sa ba as nothing r en) b c)   f a (sd , sp , l) = sd , sp , pass-of (Under P) c true a l
pass-of P (inSrc (cs false true sa ba as (just _) r en) b c)  f () l
pass-of P (inSrc (cs false false sa ba as ow r en) b c)       f () l
pass-of P (inSrc (cs true sl sa ba as ow r en) b c)           f () l
pass-of P (inBody (cs cl true sa ba as nothing r en) o c)     f (hu , nb , a) (sd , l) = hu , nb , sd , pass-of P c true a l
pass-of P (inBody (cs cl true sa ba as (just _) r en) o c)    f () l
pass-of P (inBody (cs cl false sa ba as ow r en) o c)         f () l
