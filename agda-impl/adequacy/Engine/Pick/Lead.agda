{-# OPTIONS --guardedness #-}

-- WHAT THE PICK ESTABLISHES, frame by frame up from the found node: a
-- rising value's `Clear`, a completion's `Ends`, a still skip's `Ahead`,
-- each read off `Won` and the snapshot's `Caught`.  A race read at a key
-- is read at every position no earlier (`kafter-≤`, `beat-scope`), so a
-- race run past a whole subtree puts every head the frames ask of off it
-- (`beat-aloof`).
module adequacy.Engine.Pick.Lead where

open import Data.Bool using (true; false; if_then_else_; _∧_)
open import Data.Bool.Properties using (∧-identityʳ)
open import Data.List using (List; []; _∷_; _++_; _ʳ++_; [_]; reverse; null)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to either)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to allMap; head to allHead; tail to allTail)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to all-++⁺; map⁺ to all-map⁺)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (pred; _≡ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; uncurry)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans)

open import Tree using (Obs)
open import denotation.MonotonicList.Events using (Pos; Timeline; Events∞; idle; pin; ix; _<ᵖ_; <ᵖ-below; <ᵖ-asym)
open import denotation.MonotonicList using (head)
open import denotation.Unfold using (states; step)
open import operation.Key using (Key; at; after; _<ᴷ_)
open import operation.PureObservable using (module Machine)

open Machine using (St; cs; mapS; scanS; cutS; lnS; takeS; flatS; connS; Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes;
  inSrc; inBody; plug; closed; Out; still; shows; seek; search; found; Conf; ⟨_,_,_,_⟩; subscribing; absorbed; rising;
  Mark; ofM; attM; bodyM; srcAttM; owedM; cpM; cutM; joinM; leafM; pend; coldS; ofS; doneS; joinS; own; Found; Ev; nx; cp; alive; ended; free; cpAt; cutAt; overAt; _⊕_; mapT; scanT; cutT; takeT; laneT; shift; over; outOf)
  renaming (outerT to outerK)
open import adequacy.Engine.Meaning using (gh; lanesL; deadL; poolT; outerT; envAt; srcG)
open import adequacy.Engine.Race using (NotBefore; After; TailNotBefore; First; module First)
open import adequacy.Engine.Head using (Frag; cand; ≮<ᴷ; ≮ᴷ-trans; ext-≮)
open import adequacy.Engine.Head.Within using (frag-flat; frag-body; frag-parts)
open import adequacy.Engine.Keys using (Keys)
open import adequacy.Engine.Ahead using (Sides; Ahead; Under; shown; shows-open; Aloof; ahead-over; Off; OffT) renaming (shows to showsᶜ)
open import adequacy.Engine.Scope using (Scope; modes; scope-src; Gh; gh-at)
open import adequacy.Engine.Pick using (Beat; Before; Caught; Clear; Ends; EndsIf; KAfter; KNotBefore; LaneWon; Lost; Order; Race; Won; after-step; body-link; deep; lane-on; lane-sides; lane-still; lane-won; lanes-gh; open-agrees; outer-link; past; pooled-live; race-shut; src-floor;  unrisen-open; within-sub; won-beat; won-scope)

postulate
  -- Past a position is after every position under it.
  under-after : ∀ q y → after q <ᴷ at (q ++ y) ≡ false

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
beat-scope : ∀ {R Γ A} key k (c : Ctx R Γ A) (s : St Γ A) → Beat key c s → key <ᴷ at k ≡ false → Frag (plug c s) → Gh top (plug c s) → Keys (plug c s) → Scope k c
beat-scope key k top                               s b ck ft gt kt = tt
beat-scope key k (inMap f c)                       s b ck ft gt kt = beat-scope key k c (mapS f s) b ck ft gt kt
beat-scope key k (inScan f z c)                    s b ck ft gt kt = beat-scope key k c (scanS f z s) b ck ft gt kt
beat-scope key k (inCut l a c)                     s b ck ft gt kt = beat-scope key k c (cutS l a s) b ck ft gt kt
beat-scope key k (inLn b′ c)                       s b ck ft gt kt = beat-scope key k c (lnS b′ s) b ck ft gt kt
beat-scope key k (inTake i q w c)                  s b ck ft gt kt = beat-scope key k c (takeS i q w s) b ck ft gt kt
beat-scope key k (inOuter op f d n q ls c)         s (_ , b) ck ft gt kt = beat-scope key k c (flatS op f d n q s ls) b ck ft gt kt
beat-scope key k (inLanes op f d n q o pre post c) s (_ , b) ck ft gt kt = beat-scope key k c (flatS op f d n q o (pre ʳ++ s ∷ post)) b ck ft gt kt
beat-scope key k (inSrc kk b′ c)                   s (_ , _ , b) ck ft gt kt =
  beat-scope (past (over kk) key) k c (connS kk s b′) b (past-≮ (over kk) key k ck) ft gt kt
beat-scope key k (inBody kk o c)                   s (nb , bf , b) ck ft gt kt =
  scope-src (modes c) k (srcG kk o) (envAt c)
    (src-floor k c kk o s (knot-lost (at k) (cand (inSrc kk s c) o) (knot-≤ key k (cand (inSrc kk s c) o) ck nb)) (before-≤ key k (own (connS kk o s)) ck bf) ft gt kt sc) sc
  where sc = beat-scope key k c (connS kk o s) b ck ft gt kt

race-each : ∀ {R Γ A B} {P P′ : Key → Maybe (Key × Out B) → Set} {k k′} → (∀ x → P k x → P′ k′ x)
         → ∀ (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) acc ls tl
         → Race P k c op f d n q o acc ls tl → Race P′ k′ c op f d n q o acc ls tl
race-each m c op f d n q o acc []       tl r       = tt
race-each m c op f d n q o acc (x ∷ xs) tl (w , r) = m _ w , race-each m c op f d n q o (x ∷ acc) xs tl r

lanewon-≤ : ∀ {R Γ A B} K k (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) pre post (s : St Γ B)
          → K <ᴷ at k ≡ false → LaneWon K c op f d n q o pre post s → LaneWon (at k) c op f d n q o pre post s
lanewon-≤ K k c op f d n q o pre post s le (lane-won wo wold wnew) =
  lane-won (knot-≤ K k _ le wo)
    (race-each (λ x → kafter-≤ K k x le) c op f d n q o [] (reverse pre) (s ∷ post) wold)
    (race-each (λ x → knot-≤ K k x le) c op f d n q o (s ∷ pre) post [] wnew)

-- No earlier than every position under `k`: none of them.
off-under : ∀ k m → (∀ ys → NotBefore (k ++ ys) m) → Off k m
off-under k nothing  nb = tt
off-under k (just _) nb l ls refl
  with trans (sym (nb (l ∷ ls ++ [ ix 0 ]))) (subst (λ p → (k ++ l ∷ ls) <ᵖ p ≡ true) (++-assoc k (l ∷ ls) [ ix 0 ]) (<ᵖ-below (k ++ l ∷ ls) []))
... | ()

after-nb : ∀ q m → After q m → NotBefore q m
after-nb q nothing  a = tt
after-nb q (just h) a = <ᵖ-asym q h a

off-tail : ∀ k t → (∀ ys → TailNotBefore (k ++ ys) t) → OffT k t
off-tail k idle      nb = tt
off-tail k (pin h u) nb = off-under k (just h) nb

offs : ∀ {X : Set} (F : Pos → Maybe Pos → Set) → (∀ q m → F q m → NotBefore q m) → (hd : X → Maybe Pos) → ∀ k xs
     → (∀ ys → All (λ x → F (k ++ ys) (hd x)) xs) → All (λ x → Off k (hd x)) xs
offs F g hd k []       a = []
offs F g hd k (x ∷ xs) a = off-under k (hd x) (λ ys → g (k ++ ys) (hd x) (allHead (a ys))) ∷ offs F g hd k xs (λ ys → allTail (a ys))

past-after : ∀ v p → past v (after p) ≡ after p
past-after true  p = refl
past-after false p = refl

-- BEATEN PAST A SKIP IS ALOOF: where every race above a node runs past
-- `k`, every head the frames above ask of is no earlier than each
-- position under `k`, read there as `won-ahead` reads its own key, and
-- so is under none of them.
beat-aloof : ∀ {R Γ B} k (c : Ctx R Γ B) (t : St Γ B) f → Beat (after k) c t
           → Frag (plug c t) → Gh top (plug c t) → Keys (plug c t) → showsᶜ c f ≡ true → Aloof k c f
beat-aloof k top                       t f b ft gt kt sh = tt
beat-aloof k (inMap g c)               t f b ft gt kt sh = beat-aloof k c (mapS g t) true b ft gt kt sh
beat-aloof k (inScan g z c)            t f b ft gt kt sh = beat-aloof k c (scanS g z t) true b ft gt kt sh
beat-aloof k (inCut true a c)          t f b ft gt kt sh = beat-aloof k c (cutS true a t) true b ft gt kt sh
beat-aloof k (inCut false a c)         t f b ft gt kt sh = tt
beat-aloof k (inLn b′ c)               t f b ft gt kt sh = beat-aloof k c (lnS b′ t) b′ b ft gt kt sh
beat-aloof k (inTake i q free c)       t f b ft gt kt sh = beat-aloof k c (takeS i q free t) true b ft gt kt sh
beat-aloof k (inTake i q (cpAt _) c)   t f b ft gt kt sh = tt
beat-aloof k (inTake i q (cutAt _) c)  t f b ft gt kt sh = tt
beat-aloof k (inTake i q (overAt _) c) t f b ft gt kt sh = tt
beat-aloof k (inOuter op g true n q ls c) t f b ft gt kt sh = tt
beat-aloof k (inOuter op g false n q ls c) t f (r , b) ft gt kt sh =
  offs After after-nb (λ l → head (Events∞.force l)) k (states (lanesL ls) (envAt c)) (λ ys → proj₁ (ol ys))
  , off-tail k (poolT (deadL ls) (envAt c)) (λ ys → proj₂ (ol ys))
  , beat-aloof k c (flatS op g false n q t ls) true b ft gt kt sh
  where
    cl    = shows-open c true sh
    parts = frag-parts op g false n q t ls (frag-flat c op g false n q t ls ft)
    ol : ∀ ys → All (λ l → After (k ++ ys) (head (Events∞.force l))) (states (lanesL ls) (envAt c)) × TailNotBefore (k ++ ys) (poolT (deadL ls) (envAt c))
    ol ys = outer-link c (k ++ ys) op g n q t ls ft gt (beat-scope (after k) (k ++ ys) c (flatS op g false n q t ls) b (under-after k ys) ft gt kt)
              (race-shut KAfter (After (k ++ ys)) (at (k ++ ys)) (after-step (k ++ ys)) c op g false n q t [] ls [] cl (proj₂ parts) (lanes-gh c op g false n q t ls gt)
                (race-each (λ x → kafter-≤ (after k) (k ++ ys) x (under-after k ys)) c op g false n q t [] ls [] r))
beat-aloof k (inLanes op g d n q o pre post c) t false b ft gt kt sh = tt
beat-aloof k (inLanes op g d n q o pre post c) t true (l , b) ft gt kt sh =
  ( offs NotBefore (λ _ _ x → x) (λ l → head (Events∞.force l)) k (states (lanesL post) (envAt c)) (λ ys → First.before (sd ys))
  , offs After after-nb (λ l → head (Events∞.force l)) k (states (lanesL (reverse pre)) (envAt c)) (λ ys → First.after (sd ys))
  , off-under k _ (λ ys → First.outerN (sd ys))
  , off-tail k _ (λ ys → First.tailN (sd ys)) )
  , beat-aloof k c (flatS op g d n q o (pre ʳ++ t ∷ post)) true b ft gt kt sh
  where
    sd : ∀ ys → Sides (k ++ ys) g d o (reverse pre) post (envAt c)
    sd ys = lane-sides (k ++ ys) c op g d n q o pre post t (shows-open c true sh)
              (beat-scope (after k) (k ++ ys) c (flatS op g d n q o (pre ʳ++ t ∷ post)) b (under-after k ys) ft gt kt)
              (lanewon-≤ (after k) (k ++ ys) c op g d n q o pre post t (under-after k ys) l) gt (frag-flat c op g d n q o (pre ʳ++ t ∷ post) ft)
beat-aloof k (inSrc kk@(cs false true sa ba as nothing r en) b′ c) t f (_ , _ , b) ft gt kt sh =
  beat-aloof k c (connS kk t b′) true (subst (λ K → Beat K c (connS kk t b′)) (past-after (over kk) k) b) ft gt kt sh
beat-aloof k (inSrc (cs false true sa ba as (just _) r en) b′ c) t f b ft gt kt sh = tt
beat-aloof k (inSrc (cs false false sa ba as ow r en) b′ c)      t f b ft gt kt sh = tt
beat-aloof k (inSrc (cs true sl sa ba as ow r en) b′ c)          t f b ft gt kt sh = tt
beat-aloof k (inBody kk@(cs cl true sa ba as nothing r en) o c) t f (nb , bf , b) ft gt kt sh =
  off-under k _ (λ ys → proj₂ (body-link (k ++ ys) c kk o t
    (knot-lost (at (k ++ ys)) (cand (inSrc kk t c) o) (knot-≤ (after k) (k ++ ys) (cand (inSrc kk t c) o) (under-after k ys) nb))
    (before-≤ (after k) (k ++ ys) (own (connS kk o t)) (under-after k ys) bf) ft gt kt
    (beat-scope (after k) (k ++ ys) c (connS kk o t) b (under-after k ys) ft gt kt)))
  , beat-aloof k c (connS kk o t) true b ft gt kt sh
beat-aloof k (inBody (cs cl true sa ba as (just _) r en) o c) t f b ft gt kt sh = tt
beat-aloof k (inBody (cs cl false sa ba as ow r en) o c)      t f b ft gt kt sh = tt

-- A WON SKIP IS ALOOF: a skip that won just past `k`, aloft, beats every
-- race above it past `k` (`won-beat`); what lies under `k` it causes, not
-- yet run.
won-aloof : ∀ {R Γ B} k (c : Ctx R Γ B) (t : St Γ B) → Won (at (k ⊕ [ ix 0 ]) , still) c t → Caught k c t
          → Frag (plug c t) → Gh top (plug c t) → Keys (plug c t) → showsᶜ c true ≡ true → Aloof k c true
won-aloof k c t w (at p₀ , (zs , e) , af) ft gt kt sh = beat-aloof k c t true (won-beat c t (deep zs [] e) w af) ft gt kt sh
won-aloof k c t w (after _ , () , af) ft gt kt sh

-- A still candidate that won is ahead at its key in every frame above
-- it that shows it.
won-ahead : ∀ {R Γ A} k (c : Ctx R Γ A) (s : St Γ A) f → Won (at k , still) c s → Caught k c s → Frag (plug c s) → Gh top (plug c s) → Keys (plug c s) → showsᶜ c f ≡ true → Ahead (_≡ k) c f
won-ahead k top                     s f w cg ft gt kt sh = tt
won-ahead k (inMap g c)             s f w cg ft gt kt sh = won-ahead k c (mapS g s) true w cg ft gt kt sh
won-ahead k (inScan g z c)          s f w cg ft gt kt sh = won-ahead k c (scanS g z s) true w cg ft gt kt sh
won-ahead k (inCut true a c)        s f w cg ft gt kt sh = won-ahead k c (cutS true a s) true w cg ft gt kt sh
won-ahead k (inCut false a c)       s f w cg ft gt kt ()
won-ahead k (inLn b c)              s f w cg ft gt kt sh = won-ahead k c (lnS b s) b w cg ft gt kt sh
won-ahead k (inTake i q free c)     s f w cg ft gt kt sh = won-ahead k c (takeS i q free s) true w cg ft gt kt sh
won-ahead k (inTake i q (cpAt _) c)   s f w cg ft gt kt ()
won-ahead k (inTake i q (cutAt _) c)  s f w cg ft gt kt ()
won-ahead k (inTake i q (overAt _) c) s f w cg ft gt kt ()
won-ahead k (inOuter op g true n q ls c) s f w cg ft gt kt ()
won-ahead k (inOuter op g false n q ls c) s f wn@(r , w , _) (k₀ , wi , _ , af) ft gt kt sh =
  (λ { _ refl → outer-link c k op g n q s ls ft gt (won-scope k still (inOuter op g false n q ls c) s wn ft gt kt)
                  (race-shut KAfter (After k) (at k) (after-step k) c op g false n q s [] ls [] cl (proj₂ parts) (lanes-gh c op g false n q s ls gt) r) })
  , won-ahead k c (flatS op g false n q s ls) true w (k₀ , wi , af) ft gt kt sh
  where
    cl    = shows-open c true sh
    parts = frag-parts op g false n q s ls (frag-flat c op g false n q s ls ft)
won-ahead k (inLanes op g d n q o pre post c) s false w cg ft gt kt ()
won-ahead k (inLanes op g d n q o pre post c) s true wn@(l , _ , w) (k₀ , wi , _ , _ , _ , af) ft gt kt sh =
  (λ { _ refl → lane-sides k c op g d n q o pre post s (shows-open c true sh)
                  (won-scope k still (inLanes op g d n q o pre post c) s wn ft gt kt) l gt (frag-flat c op g d n q o (pre ʳ++ s ∷ post) ft) })
  , won-ahead k c (flatS op g d n q o (pre ʳ++ s ∷ post)) true (lane-still d n q (alive s) {at k} {c} w) (k₀ , wi , af) ft gt kt sh
won-ahead k (inSrc (cs false true sa ba as nothing r en) b c) s f (ka , _ , w) (k₀ , wi , _ , _ , af) ft gt kt sh =
  ahead-over k (λ j u → u) c true (won-ahead (k ⊕ [ ix 0 ]) c (connS (cs false true sa ba as nothing r en) s b) true w (k₀ , within-sub k₀ [ ix 0 ] wi , af) ft gt kt sh)
    (won-aloof k c (connS (cs false true sa ba as nothing r en) s b) w (k₀ , wi , af) ft gt kt sh)
won-ahead k (inSrc (cs false true sa ba as (just _) r en) b c) s f w cg ft gt kt ()
won-ahead k (inSrc (cs false false sa ba as ow r en) b c)      s f w cg ft gt kt ()
won-ahead k (inSrc (cs true sl sa ba as ow r en) b c)          s f w cg ft gt kt ()
won-ahead k (inBody (cs cl true sa ba as nothing r en) o c) s f (_ , lo , bf , w) (k₀ , wi , _ , _ , _ , af) ft gt kt sh =
  proj₁ bb , (λ { _ refl → proj₂ bb }) , won-ahead k c (connS (cs cl true sa ba as nothing r en) o s) true w (k₀ , wi , af) ft gt kt sh
  where bb = body-link k c (cs cl true sa ba as nothing r en) o s lo bf ft gt kt (won-scope k _ c (connS (cs cl true sa ba as nothing r en) o s) w ft gt kt)
won-ahead k (inBody (cs cl true sa ba as (just _) r en) o c) s f w cg ft gt kt ()
won-ahead k (inBody (cs cl false sa ba as ow r en) o c)      s f w cg ft gt kt ()

-- Up the found node's frames: each one the value reaches is clear there.
-- `s` is the node the search saw, `s′` the one the rise leaves.
won-clear : ∀ {R Γ A} p (a : A) (c : Ctx R Γ A) (s s′ : St Γ A) → alive s ≡ alive s′ → closed c ≡ false
          → Won (at p , shows (nx a)) c s → Caught p c s → Frag (plug c s) → Gh top (plug c s) → Keys (plug c s) → Clear p a c s′
won-clear p a top                               s s′ al ce w cg ft gt kt = tt
won-clear p a (inMap f c)                       s s′ al ce w cg ft gt kt = won-clear p (f a) c (mapS f s) (mapS f s′) refl ce w cg ft gt kt
won-clear p a (inScan f z c)                    s s′ al ce w cg ft gt kt = won-clear p (f z a) c (scanS f z s) (scanS f (f z a) s′) refl ce w cg ft gt kt
won-clear p a (inCut true x c)                  s s′ al ce w cg ft gt kt = λ _ → won-clear p a c (cutS true x s) (cutS true x s′) refl ce w cg ft gt kt
won-clear p a (inCut false x c)                 s s′ al ce w cg ft gt kt = λ ()
won-clear p a (inLn b c)                        s s′ al ce w cg ft gt kt = won-clear p a c (lnS b s) (lnS b s′) refl ce w cg ft gt kt
won-clear p a (inTake i q free c)               s s′ al ce w (k₀ , wi , af) ft gt kt with q a | i
... | true  | _     = (λ _ → won-clear p a c (takeS _ q free s) (takeS _ q free s′) refl ce w (k₀ , wi , af) ft gt kt) , (λ ())
... | false | true  = (λ ()) , (λ _ _ → won-clear (p ⊕ [ ix 0 ]) a c (takeS true q free s) (takeS true q (cpAt p) s′) refl ce w (k₀ , within-sub k₀ [ ix 0 ] wi , af) ft gt kt)
... | false | false = (λ ()) , (λ _ ())
won-clear p a (inTake i q (cpAt r) c)           s s′ al ce w cg ft gt kt = tt
won-clear p a (inTake i q (cutAt r) c)          s s′ al ce w cg ft gt kt = tt
won-clear p a (inTake i q (overAt r) c)         s s′ al ce w cg ft gt kt = tt
won-clear p a (inOuter op f true n q ls c)      s s′ al ce (_ , _ , ()) cg ft gt kt
won-clear p a (inOuter op f false n q ls c)     s s′ al ce wn@(r , w , u) (k₀ , wi , _ , af) ft gt kt =
  cl , proj₁ ol , proj₂ ol , won-ahead (p ⊕ [ ix 0 ]) c (flatS op f false n q s ls) true w (k₀ , within-sub k₀ [ ix 0 ] wi , af) ft gt kt , won-aloof p c (flatS op f false n q s ls) w (k₀ , wi , af) ft gt kt
  where
    cl    = unrisen-open (closed c) u
    parts = frag-parts op f false n q s ls (frag-flat c op f false n q s ls ft)
    ol    = outer-link c p op f n q s ls ft gt (won-scope p (shows (nx a)) (inOuter op f false n q ls c) s wn ft gt kt) (race-shut KAfter (After p) (at p) (after-step p) c op f false n q s [] ls [] cl (proj₂ parts) (lanes-gh c op f false n q s ls gt) r)
won-clear p a (inLanes op f d n q o pre post c) s s′ al ce wn@(l , _ , w) (k₀ , wi , _ , _ , _ , af) ft gt kt lv =
  lane-sides p c op f d n q o pre post s ce (won-scope p (shows (nx a)) (inLanes op f d n q o pre post c) s wn ft gt kt) l gt (frag-flat c op f d n q o (pre ʳ++ s ∷ post) ft)
  , won-clear p a c (flatS op f d n q o (pre ʳ++ s ∷ post)) (flatS op f d n q o (pre ʳ++ s′ ∷ post)) refl ce
      (lane-on d n q {alive s} {at p} a {c} {flatS op f d n q o (pre ʳ++ s ∷ post)} (trans al lv) w) (k₀ , wi , af) ft gt kt
won-clear p a (inSrc kk b c)                    s s′ al ce (w , _) cg ft gt kt with over kk
... | true  = λ ()
... | false = λ _ cl → after-step (p ⊕ [ ix 0 ]) (cand (inBody kk s c) b) (step (gh b)) w (open-agrees (inBody kk s c) b cl (frag-body c kk s b ft) (proj₂ (proj₂ (gh-at c (connS kk s b) gt))))
won-clear p a (inBody (cs cl true sa ba as nothing r en) o c) s s′ al ce (_ , lo , bf , w) (k₀ , wi , _ , _ , _ , af) ft gt kt =
  proj₁ bb , proj₂ bb , won-clear p a c (connS (cs cl true sa ba as nothing r en) o s) (connS (cs cl true sa ba as nothing r en) o s′) refl ce w (k₀ , wi , af) ft gt kt
  where bb = body-link p c (cs cl true sa ba as nothing r en) o s lo bf ft gt kt (won-scope p _ c (connS (cs cl true sa ba as nothing r en) o s) w ft gt kt)
won-clear p a (inBody (cs cl true sa ba as (just _) r en) o c)  s s′ al ce (() , _) cg ft gt kt
won-clear p a (inBody (cs cl false sa ba as (just _) r en) o c) s s′ al ce (() , _) cg ft gt kt
won-clear p a (inBody (cs cl false sa ba as nothing r en) o c)  s s′ al ce (() , _) cg ft gt kt

-- A lane's completion passes its flatMap's retag as the lane's end.
lane-off : ∀ {R Γ A B} d n (q : List A) {b} {k} {c : Ctx R Γ B} {t} → b ≡ true
         → Won (uncurry (laneT d n q) (cutT b k (shows cp))) c t → Won (laneT d n q k (shows cp)) c t
lane-off d n q refl w = w

-- A live lane's completion under a queue passes its flatMap's retag as
-- a still skip just past it.
lane-shift : ∀ {R Γ A B} d n (a : A) q {b} {k} {c : Ctx R Γ B} {t} → b ≡ true
           → Won (uncurry (laneT d n (a ∷ q)) (cutT b k (shows cp))) c t → Won (shift k , still) c t
lane-shift d n a q refl w = w

-- No end waits where a lane is queued.
ends-queued : ∀ {R Γ A} d x p (c : Ctx R Γ A) s → EndsIf (d ∧ x ∧ false) p c s
ends-queued false x     p c s = tt
ends-queued true  false p c s = tt
ends-queued true  true  p c s = tt

-- An open outer's end, won, leads its lanes and its pool.
outer-ends : ∀ {R Γ A B} p (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (s : St Γ A) ls
           → Won (at p , shows cp) (inOuter op f d n q ls c) s → Frag (plug c (flatS op f d n q s ls)) → Gh top (plug c (flatS op f d n q s ls)) → Keys (plug c (flatS op f d n q s ls)) → d ≡ false → closed c ≡ false
           → All (λ l → After p (head (Events∞.force l))) (states (lanesL ls) (envAt c)) × TailNotBefore p (poolT (deadL ls) (envAt c))
outer-ends p c op f d n q s ls wn ft gt kt refl cl =
  outer-link c p op f n q s ls ft gt (won-scope p (shows cp) (inOuter op f false n q ls c) s wn ft gt kt)
    (race-shut KAfter (After p) (at p) (after-step p) c op f false n q s [] ls [] cl (proj₂ parts) (lanes-gh c op f false n q s ls gt) (proj₁ wn))
  where parts = frag-parts op f false n q s ls (frag-flat c op f false n q s ls ft)

-- Up the found node's frames: each one the completion reaches is clear
-- there, as `won-clear` for a value.
mutual
  won-ends : ∀ {R Γ A} p (c : Ctx R Γ A) (s s′ : St Γ A) → alive s ≡ alive s′
           → Won (at p , shows cp) c s → Caught p c s → Frag (plug c s) → Gh top (plug c s) → Keys (plug c s) → Ends p c s′
  won-ends p top                               s s′ al w cg ft gt kt = tt
  won-ends p (inMap f c)                       s s′ al w cg ft gt kt = won-ends p c (mapS f s) (mapS f s′) refl w cg ft gt kt
  won-ends p (inScan f z c)                    s s′ al w cg ft gt kt = won-ends p c (scanS f z s) (scanS f z s′) refl w cg ft gt kt
  won-ends p (inCut true x c)                  s s′ al w cg ft gt kt = λ _ → won-ends p c (cutS true x s) (cutS true x s′) refl w cg ft gt kt
  won-ends p (inCut false x c)                 s s′ al w cg ft gt kt = λ ()
  won-ends p (inLn b c)                        s s′ al w cg ft gt kt = won-ends p c (lnS b s) (lnS b s′) refl w cg ft gt kt
  won-ends p (inTake i q free c)               s s′ al w cg ft gt kt = won-ends p c (takeS i q free s) (takeS i q free s′) refl w cg ft gt kt
  won-ends p (inTake i q (cpAt r) c)           s s′ al w cg ft gt kt = tt
  won-ends p (inTake i q (cutAt r) c)          s s′ al w cg ft gt kt = tt
  won-ends p (inTake i q (overAt r) c)         s s′ al w cg ft gt kt = tt
  won-ends p (inOuter op f d n q ls c)         s s′ al wn@(r , w , _) (k₀ , wi , _ , af) ft gt kt =
    outer-ends p c op f d n q s ls wn ft gt kt , ends-if p c ((n ≡ᵇ 0) ∧ null q) (flatS op f d n q s ls) (flatS op f true n q s′ ls) refl w (k₀ , wi , af) ft gt kt
  won-ends p (inLanes op f d n [] o pre post c) s s′ al wn@(l , u , w) (k₀ , wi , _ , _ , _ , af) ft gt kt =
    trans (sym al) lv , (λ cl → lane-sides p c op f d n [] o pre post s cl (won-scope p (shows cp) (inLanes op f d n [] o pre post c) s wn ft gt kt) l gt (frag-flat c op f d n [] o (pre ʳ++ s ∷ post) ft))
    , subst (λ b → EndsIf (d ∧ b) p c (flatS op f d (pred n) [] o (pre ʳ++ ended s′ ∷ post))) (sym (∧-identityʳ (pred n ≡ᵇ 0)))
        (ends-if p c (d ∧ (pred n ≡ᵇ 0)) (flatS op f d n [] o (pre ʳ++ s ∷ post)) (flatS op f d (pred n) [] o (pre ʳ++ ended s′ ∷ post)) refl
           (lane-off d n [] {alive s} {at p} {c} lv w) (k₀ , wi , af) ft gt kt)
    , tt
    where lv = pooled-live (alive s) u
  won-ends p (inLanes op f d n (a ∷ q) o pre post c) s s′ al wn@(l , u , w) (k₀ , wi , _ , _ , _ , af) ft gt kt =
    trans (sym al) lv , (λ cl → lane-sides p c op f d n (a ∷ q) o pre post s cl (won-scope p (shows cp) (inLanes op f d n (a ∷ q) o pre post c) s wn ft gt kt) l gt (frag-flat c op f d n (a ∷ q) o (pre ʳ++ s ∷ post) ft))
    , ends-queued d (pred n ≡ᵇ 0) p c (flatS op f d (pred n) (a ∷ q) o (pre ʳ++ ended s′ ∷ post))
    , λ sh → won-ahead (p ⊕ [ ix 0 ]) c (flatS op f d n (a ∷ q) o (pre ʳ++ s ∷ post)) true (lane-shift d n a q {alive s} {at p} {c} lv w) (k₀ , within-sub k₀ [ ix 0 ] wi , af) ft gt kt sh
             , won-aloof p c (flatS op f d n (a ∷ q) o (pre ʳ++ s ∷ post)) (lane-shift d n a q {alive s} {at p} {c} lv w) (k₀ , wi , af) ft gt kt sh
    where lv = pooled-live (alive s) u
  won-ends p (inSrc kk b c)                    s s′ al w cg ft gt kt = tt
  won-ends p (inBody (cs cl true sa ba as nothing r en) o c) s s′ al (_ , lo , bf , w) (k₀ , wi , _ , _ , _ , af) ft gt kt =
    (λ ce → body-link p c (cs cl true sa ba as nothing r en) o s lo bf ft gt kt (won-scope p _ c (connS (cs cl true sa ba as nothing r en) o s) w ft gt kt))
    , λ k′ → won-ends p c (connS (cs cl true sa ba as nothing r en) o s) (connS k′ o s′) refl w (k₀ , wi , af) ft gt kt
  won-ends p (inBody (cs cl true sa ba as (just _) r en) o c)  s s′ al (() , _) cg ft gt kt
  won-ends p (inBody (cs cl false sa ba as (just _) r en) o c) s s′ al (() , _) cg ft gt kt
  won-ends p (inBody (cs cl false sa ba as nothing r en) o c)  s s′ al (() , _) cg ft gt kt

  ends-if : ∀ {R Γ A} p (c : Ctx R Γ A) b (s s′ : St Γ A) → alive s ≡ alive s′
          → Won (at p , (if b then shows cp else still)) c s → Caught p c s → Frag (plug c s) → Gh top (plug c s) → Keys (plug c s) → EndsIf b p c s′
  ends-if p c true  s s′ al w cg ft gt kt = won-ends p c s s′ al w cg ft gt kt
  ends-if p c false s s′ al w cg ft gt kt = tt

-- Each frame a rising value reaches is clear there, read off the snapshot.
lead-clear : ∀ {R Γ A} {c : Ctx R Γ A} {s : St Γ A} {a p} → Order ⟨ c , s , rising (nx a) , p ⟩ → Clear p a c s
lead-clear {c = c} {s} {a} {p} o with Order.lead o
... | t , al , w , ft , gt , kt , cg = won-clear p a c t s al (Order.heard o) w cg ft gt kt

-- Each frame a rising completion reaches is clear there, likewise.
lead-ends : ∀ {R Γ A} {c : Ctx R Γ A} {s : St Γ A} {p} → Order ⟨ c , s , rising cp , p ⟩ → Ends p c s
lead-ends {c = c} {s} {p} o with Order.lead o
... | t , al , w , ft , gt , kt , cg = won-ends p c t s al w cg ft gt kt
