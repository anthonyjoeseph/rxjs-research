{-# OPTIONS --guardedness #-}

-- THE GHOST IS PLACED: every node's meaning, read where the ghost reads
-- it, comes in position order.  A connect takes its source's step ahead
-- of its body's skips tied with it, so the stepper needs the source's
-- rest atop that step.
module adequacy.Placed where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_; [_]; length)
open import Data.Nat using (ℕ; zero; suc; _<ᵇ_; _+_; _≤_; _<_; s≤s)
open import Data.Nat.Properties using (≤-refl; <⇒≢; +-monoˡ-≤; +-assoc; n≤1+n; <-≤-trans; ≤-trans; m≤n+m; m≤m+n; <-irrefl)
open import Data.List.Relation.Unary.All using (All; lookup) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_; map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to All++⁺; ++⁻ˡ to All++⁻ˡ; ++⁻ʳ to All++⁻ʳ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; cong)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; Later; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.MonotonicList.Events using (timelineAt; Events; Events∞; Pos; From; Timeline; out; skip; end; hush; ix; sub; last; tick; _<ᵖ_; root;
  <ᵖ-asym; <ᵖ-split; <ᵖ-trans; <ᵖ-irrefl; <ᵖ-below; Tail; Tail∞; pin; idle; _∪_)
open import denotation.MonotonicList using (MonotonicList; agreeᵀ; none; found)
import denotation.MonotonicList.Events as M
import denotation.MonotonicList as M′
import denotation.Unfold as U
open import denotation.Unfold using (NEnv)
open import denotation.Denote using (flatOp) renaming (⟦_⟧ to ⟦_⟧ᴰ)
open import denotation.Compositional using (env-refl)
open import adequacy.Finite using (Finite; map-f; scan-f; takeWhile-f; flatMap-f; connect-f; defer-f; trunc; finite-trunc;
  trunc-agree)
open import adequacy.Placed.Order using (Alien; Alienᴱ; Atop; Disjoint; Every; EveryT; Everyᴱ; Every∞; Headed; Ordered; Owned; Placed; Prefix; Sorted; Steady; atop-map; every; every-lookup; every-mono; every-monoᴱ; everyT-idle; everyT-mono; everyT-∪; everyᵀ; every∞-mono; headed-snoc; ordered; ordered-map; ordered-rejoin; ordered-scan; prefix-++; prefix-trans; sorted-headed; sorted-lookup; steady; steady-map; steady-rejoin; steady-scan)
open import adequacy.Placed.Keys using (Mark; Values; alienᴱ-owned; beneath-owned; earliest-all; every-map; every-reach; everyT-≈; ix-mark; last-mark; no-tick; ordered-lim; owned-tagged; owned-trans; owned-weigh; prefix-refl; prefix-weigh; sibling; snoc-inj; steady-lim; tagged-lane; tagged-mark; tagged-weigh; values; values-map; weigh; weighˡ)
open import adequacy.Placed.Rising using (Beyond; module Deferred; module Reach; Rise; alien-shown; alien-sub; apart-mark; apartRules; atop-go; below-lane; every-zip; everyT-zip; headed-lane; headed-sub; headedRules; keyedRules; next-ix; ordered-defer; ordered-of; ordered-start; ordered-take; prefix-split; rise-env; rise-owned; rise-sub; risingRules; steady-defer; steady-of; steady-start; steady-take; tagged-split)
open import adequacy.Placed.Trail using (Sp; Spread; Trail; Trailing; disjoint-swap; flatT-idle; past-beyond; shown; sortedT-idle; spread; spread-defer; spread-map; spread-scan; tick-beneath; trail; trail-idle; trail-map; trail-of; trail-rejoin; trail-scan; trailing-start)
open import adequacy.Placed.Calm using (calm-steady; calm-trail)
open import adequacy.Placed.FlatOrder using (module FlatOrder)
open import adequacy.Placed.FlatAfter using (module FlatAfter; trail-defer; trail-take)
open import adequacy.Placed.Burst using (module Bursting; Fresh; FreshRun; Fresh∞; fresh-map; fresh-of; fresh-past; fresh-rejoin; fresh-scan; fresh-start; fresh-take; fresh-under; fresh-up; fresh-widen; fresh-≈; freshᴿ; heavy; longer; mark-sub; owned-drop; snoc-ne; sub-owned; sub-tagged)
open import adequacy.Placed.Walk using (module Walk)
open import adequacy.Placed.Heads using (apart-sub; start-within)

open Events∞
open Tail∞

------------------------------------------------------------------------
-- A flatMap's merge, each part fresh against the last step it showed.

module FlatFresh (p : Pos) where
  K : Pos → Set
  K y = Owned p y × Headed y

  -- A lane in flight: what it leaves running fresh against `L`, its run
  -- fresh, keyed under `p`.
  Lanef : ∀ {B} → Pos → Events∞ B → Set
  Lanef L l = EveryT (Fresh p L) (cut l) × FreshRun p (force l) × Every K (force l)

  -- A lane admitted just past `q` is fresh against the skip the merge
  -- shows at `q`'s left.
  GenF : ∀ {B} → MonotonicList B → Set
  GenF m = ∀ q → K q → Lanef (q ++ [ ix 0 ]) (M′.enter m (q ++ [ ix 1 ]))

  Freshᴼ : ∀ {B} → Pos → Maybe (Events∞ (MonotonicList B)) → Set
  Freshᴼ L nothing  = ⊤
  Freshᴼ L (just e) = EveryT (Fresh p L) (cut e) × FreshRun p (force e) × Values GenF (force e) × Every K (force e)

  -- Fresh against a step, fresh against any after it.
  up : ∀ L L′ → L′ <ᵖ L ≡ false → (t : Tail) → EveryT (Fresh p L) t → EveryT (Fresh p L′) t
  up L L′ a = everyT-mono (λ h → fresh-past p L L′ h a)

  lane-up : ∀ {B} L L′ → L′ <ᵖ L ≡ false → (l : Events∞ B) → Lanef L l → Lanef L′ l
  lane-up L L′ a l (c , r , k) = up L L′ a (cut l) c , r , k

  lanes-up : ∀ {B} L L′ → L′ <ᵖ L ≡ false → (ls : List (Events∞ B)) → All (Lanef L) ls → All (Lanef L′) ls
  lanes-up L L′ a ls = mapᴬ (λ {l} → lane-up L L′ a l)

  outer-up : ∀ {B} L L′ → L′ <ᵖ L ≡ false → (o : Maybe (Events∞ (MonotonicList B))) → Freshᴼ L o → Freshᴼ L′ o
  outer-up L L′ a nothing  fo            = tt
  outer-up L L′ a (just e) (c , r , v , k) = up L L′ a (cut e) c , r , v , k

  cuts-fresh : ∀ {B} L (ls : List (Events∞ B)) → All (Lanef L) ls → EveryT (Fresh p L) (M′.cuts ls)
  cuts-fresh L []       []ᴬ        = everyT-idle
  cuts-fresh L (l ∷ ls) (fl ∷ᴬ al) = everyT-∪ (cut l) (M′.cuts ls) (proj₁ fl) (cuts-fresh L ls al)

  whole-fresh : ∀ {B} L (o : Maybe (Events∞ (MonotonicList B))) ls t → Freshᴼ L o → All (Lanef L) ls → EveryT (Fresh p L) t
              → EveryT (Fresh p L) (M′.whole o ls t)
  whole-fresh L nothing  ls t fo fl ft = everyT-∪ idle (M′.cuts ls ∪ t) everyT-idle (everyT-∪ (M′.cuts ls) t (cuts-fresh L ls fl) ft)
  whole-fresh L (just e) ls t fo fl ft = everyT-∪ (cut e) (M′.cuts ls ∪ t) (proj₁ fo) (everyT-∪ (M′.cuts ls) t (cuts-fresh L ls fl) ft)

  -- An admitted lane runs fresh, a queued one stays fresh where it would
  -- be admitted, and a dropped one leaves its tail.
  Admittedᶠ : ∀ {B} → Pos → List (Events∞ B) × List (MonotonicList B) × Tail → Set
  Admittedᶠ L (ls , qs , d) = All (Lanef L) ls × All GenF qs × EveryT (Fresh p L) d

  admit-fresh : ∀ {B} op q (m : MonotonicList B) ls qs L → Lanef L (M′.enter m q) → GenF m → All (Lanef L) ls → All GenF qs
              → Admittedᶠ L (M′.admit op q m ls qs)
  admit-fresh (M′.mergeᶠ nothing)  q m ls       qs L lm gm fl fq = lm ∷ᴬ fl , fq , everyT-idle
  admit-fresh (M′.mergeᶠ (just n)) q m ls       qs L lm gm fl fq with length ls <ᵇ n
  ... | true  = lm ∷ᴬ fl , fq , everyT-idle
  ... | false = fl , All++⁺ fq (gm ∷ᴬ []ᴬ) , everyT-idle
  admit-fresh M′.switchᶠ           q m ls       qs L lm gm fl fq = lm ∷ᴬ []ᴬ , fq , cuts-fresh L ls fl
  admit-fresh M′.exhaustᶠ          q m []       qs L lm gm fl fq = lm ∷ᴬ []ᴬ , fq , everyT-idle
  admit-fresh M′.exhaustᶠ          q m (l ∷ ls) qs L lm gm fl fq = fl , fq , everyT-idle

  -- Each step the merge shows is no earlier than the last, so every part
  -- fresh against the last is fresh against it; the part that showed it
  -- is fresh against it by its own run.
  mutual
    fr-go : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t L → Freshᴼ L o → All (Lanef L) ls → All GenF qs
          → EveryT (Fresh p L) t → Atop L (M′.go op o ls qs t) → Ordered (M′.go op o ls qs t) → FreshRun p (M′.go op o ls qs t)
    freshᴿ (fr-go op o ls qs idle      L fo fl fq ft at od) = freshᴿ (fr-parts op o ls qs idle L fo fl fq ft at od)
    freshᴿ (fr-go op o ls qs (pin k u) L fo fl fq ft at od) =
      freshᴿ (fr-left op o ls qs k u (M′.ahead-of k o ls) L fo fl fq ft at od)

    fr-left : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs k u b L → Freshᴼ L o → All (Lanef L) ls → All GenF qs
            → EveryT (Fresh p L) (pin k u) → Atop L (M′.left op o ls qs k u b) → Ordered (M′.left op o ls qs k u b)
            → FreshRun p (M′.left op o ls qs k u b)
    freshᴿ (fr-left op o ls qs k u true  L fo fl fq ft at od) =
      whole-fresh k o ls (later u) fo′ fl′ ft′ , fr-go op o ls qs (later u) k fo′ fl′ fq ft′ (proj₁ (ordered od)) (proj₂ (ordered od))
      where
        fo′ = outer-up L k at o fo
        fl′ = lanes-up L k at ls fl
        ft′ = up L k at (later u) (proj₂ (everyᵀ ft))
    freshᴿ (fr-left op o ls qs k u false L fo fl fq ft at od) = freshᴿ (fr-parts op o ls qs (pin k u) L fo fl fq ft at od)

    fr-parts : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t L → Freshᴼ L o → All (Lanef L) ls → All GenF qs
             → EveryT (Fresh p L) t → Atop L (M′.parts op o ls qs t) → Ordered (M′.parts op o ls qs t) → FreshRun p (M′.parts op o ls qs t)
    fr-parts op o ls qs t L fo fl fq ft at od with M′.earliest ls | earliest-all (Lanef L) ls fl
    ... | none            | _               = fr-via op o ls qs t L fo fl fq ft at od
    ... | found k bs l as | (fb , fl₁ , fa) = fr-race op o k bs l as qs t L fo fb fl₁ fa fq ft at od

    fr-via : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t L → Freshᴼ L o → All (Lanef L) ls → All GenF qs
           → EveryT (Fresh p L) t → Atop L (M′.viaOuter op o ls qs t) → Ordered (M′.viaOuter op o ls qs t)
           → FreshRun p (M′.viaOuter op o ls qs t)
    fr-via op nothing  ls qs t L fo                  fl fq ft at od = record { freshᴿ = tt }
    fr-via op (just e) ls qs t L (ce , re , ve , ke) fl fq ft at od = fr-outer op e ls qs t (force e) L ce re ve ke fl fq ft at od

    fr-race : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) k bs (l : Events∞ B) as qs t L → Freshᴼ L o
            → All (Lanef L) bs → Lanef L l → All (Lanef L) as → All GenF qs → EveryT (Fresh p L) t
            → Atop L (M′.race op o k bs l as qs t) → Ordered (M′.race op o k bs l as qs t) → FreshRun p (M′.race op o k bs l as qs t)
    fr-race op nothing  k bs l as qs t L fo fb (cl , rl , kl) fa fq ft at od =
      fr-lane op nothing bs l as qs t (force l) L fo fb cl rl kl fa fq ft at od
    fr-race op (just e) k bs l as qs t L fo fb (cl , rl , kl) fa fq ft at od with M′.head (force e)
    ... | nothing = fr-lane op (just e) bs l as qs t (force l) L fo fb cl rl kl fa fq ft at od
    ... | just k′ with k′ <ᵖ k
    ...   | true  = fr-outer op e (bs ++ l ∷ as) qs t (force e) L (proj₁ fo) (proj₁ (proj₂ fo)) (proj₁ (proj₂ (proj₂ fo)))
                      (proj₂ (proj₂ (proj₂ fo))) (All++⁺ fb ((cl , rl , kl) ∷ᴬ fa)) fq ft at od
    ...   | false = fr-lane op (just e) bs l as qs t (force l) L fo fb cl rl kl fa fq ft at od

    fr-outer : ∀ {B} op (e : Events∞ (MonotonicList B)) ls qs t (x : Events (MonotonicList B)) L → EveryT (Fresh p L) (cut e)
             → FreshRun p x → Values GenF x → Every K x → All (Lanef L) ls → All GenF qs → EveryT (Fresh p L) t
             → Atop L (M′.outer op e ls qs t x) → Ordered (M′.outer op e ls qs t x) → FreshRun p (M′.outer op e ls qs t x)
    freshᴿ (fr-outer op e ls qs t (out q m r) L ce rx vx kx fl fq ft at od) with M′.admit op (q ++ [ ix 1 ]) m ls qs in eq
    ... | ls′ , qs′ , d =
      whole-fresh Q (just r) ls′ (t ∪ d) fo′ (proj₁ ad) ft′
      , fr-go op (just r) ls′ qs′ (t ∪ d) Q fo′ (proj₁ ad) (proj₁ (proj₂ ad)) ft′ (proj₁ (ordered od)) (proj₂ (ordered od))
      where
        Q = q ++ [ ix 0 ]
        fo′ : Freshᴼ Q (just r)
        fo′ = everyT-mono (λ h → fresh-up p q Q h (inj₁ (<ᵖ-below q []))) (cut r) (proj₁ (freshᴿ rx)) , proj₂ (freshᴿ rx)
              , proj₂ (values vx) , proj₁ (proj₂ (every kx))
        ad : Admittedᶠ Q (ls′ , qs′ , d)
        ad = subst (Admittedᶠ Q) eq
               (admit-fresh op (q ++ [ ix 1 ]) m ls qs Q (proj₁ (values vx) q (proj₁ (every kx))) (proj₁ (values vx))
                  (lanes-up L Q at ls fl) fq)
        ft′ = everyT-∪ t d (up L Q at t ft) (proj₂ (proj₂ ad))
    freshᴿ (fr-outer op e ls qs t (skip q r) L ce rx vx kx fl fq ft at od) =
      whole-fresh q (just r) ls t fo′ fl′ ft′ , fr-go op (just r) ls qs t q fo′ fl′ fq ft′ (proj₁ (ordered od)) (proj₂ (ordered od))
      where
        fo′ : Freshᴼ q (just r)
        fo′ = proj₁ (freshᴿ rx) , proj₂ (freshᴿ rx) , values vx , proj₁ (proj₂ (every kx))
        fl′ = lanes-up L q at ls fl
        ft′ = up L q at t ft
    freshᴿ (fr-outer op e []       []       t (end c) L ce rx vx kx fl fq ft at od) = tt
    freshᴿ (fr-outer {B} op e []       (m ∷ qs) t (end c) L ce rx vx kx fl fq ft at od) =
      whole-fresh {B} c nothing [] (t ∪ cut e) tt []ᴬ ft′ , fr-go op nothing [] (m ∷ qs) (t ∪ cut e) c tt []ᴬ fq ft′ (proj₁ (ordered od)) (proj₂ (ordered od))
      where ft′ = everyT-∪ t (cut e) (up L c at t ft) (up L c at (cut e) ce)
    freshᴿ (fr-outer op e (l ∷ ls) qs       t (end c) L ce rx vx kx fl fq ft at od) =
      whole-fresh c nothing (l ∷ ls) (t ∪ cut e) tt fl′ ft′
      , fr-go op nothing (l ∷ ls) qs (t ∪ cut e) c tt fl′ fq ft′ (proj₁ (ordered od)) (proj₂ (ordered od))
      where
        fl′ = lanes-up L c at (l ∷ ls) fl
        ft′ = everyT-∪ t (cut e) (up L c at t ft) (up L c at (cut e) ce)
    freshᴿ (fr-outer op e ls       qs       t hush    L ce rx vx kx fl fq ft at od) = tt

    fr-lane : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) bs (l : Events∞ B) as qs t (x : Events B) L → Freshᴼ L o
            → All (Lanef L) bs → EveryT (Fresh p L) (cut l) → FreshRun p x → Every K x → All (Lanef L) as → All GenF qs
            → EveryT (Fresh p L) t → Atop L (M′.lane op o bs l as qs t x) → Ordered (M′.lane op o bs l as qs t x)
            → FreshRun p (M′.lane op o bs l as qs t x)
    freshᴿ (fr-lane op o bs l as qs t (out k b r) L fo fb cl rx kx fa fq ft at od) =
      whole-fresh k o (bs ++ r ∷ as) t fo′ fl′ ft′ , fr-go op o (bs ++ r ∷ as) qs t k fo′ fl′ fq ft′ (proj₁ (ordered od)) (proj₂ (ordered od))
      where
        fo′ = outer-up L k at o fo
        fl′ = All++⁺ (lanes-up L k at bs fb) ((proj₁ (freshᴿ rx) , proj₂ (freshᴿ rx) , proj₁ (proj₂ (every kx))) ∷ᴬ lanes-up L k at as fa)
        ft′ = up L k at t ft
    freshᴿ (fr-lane op o bs l as qs t (skip k r) L fo fb cl rx kx fa fq ft at od) =
      whole-fresh k o (bs ++ r ∷ as) t fo′ fl′ ft′ , fr-go op o (bs ++ r ∷ as) qs t k fo′ fl′ fq ft′ (proj₁ (ordered od)) (proj₂ (ordered od))
      where
        fo′ = outer-up L k at o fo
        fl′ = All++⁺ (lanes-up L k at bs fb) ((proj₁ (freshᴿ rx) , proj₂ (freshᴿ rx) , proj₁ (proj₂ (every kx))) ∷ᴬ lanes-up L k at as fa)
        ft′ = up L k at t ft
    freshᴿ (fr-lane op o bs l as (m ∷ qs) t (end c) L fo fb cl rx kx fa (gm ∷ᴬ fq) ft at od) =
      whole-fresh Q o ls′ (t ∪ cut l) fo′ fl′ ft′ , fr-go op o ls′ qs (t ∪ cut l) Q fo′ fl′ fq ft′ (proj₁ (ordered od)) (proj₂ (ordered od))
      where
        Q = c ++ [ ix 0 ]
        ls′ = M′.enter m (c ++ [ ix 1 ]) ∷ bs ++ as
        fo′ = outer-up L Q at o fo
        fl′ = gm c (every kx) ∷ᴬ All++⁺ (lanes-up L Q at bs fb) (lanes-up L Q at as fa)
        ft′ = everyT-∪ t (cut l) (up L Q at t ft) (up L Q at (cut l) cl)
    freshᴿ (fr-lane op nothing  []       l []       [] t (end c) L fo fb cl rx kx fa fq ft at od) = tt
    freshᴿ (fr-lane op nothing  []       l (a ∷ as) [] t (end c) L fo fb cl rx kx fa fq ft at od) =
      whole-fresh c nothing (a ∷ as) (t ∪ cut l) tt fl′ ft′ , fr-go op nothing (a ∷ as) [] (t ∪ cut l) c tt fl′ fq ft′ (proj₁ (ordered od)) (proj₂ (ordered od))
      where
        fl′ = lanes-up L c at (a ∷ as) fa
        ft′ = everyT-∪ t (cut l) (up L c at t ft) (up L c at (cut l) cl)
    freshᴿ (fr-lane op nothing  (b ∷ bs) l as       [] t (end c) L fo fb cl rx kx fa fq ft at od) =
      whole-fresh c nothing (b ∷ bs ++ as) (t ∪ cut l) tt fl′ ft′
      , fr-go op nothing (b ∷ bs ++ as) [] (t ∪ cut l) c tt fl′ fq ft′ (proj₁ (ordered od)) (proj₂ (ordered od))
      where
        fl′ = All++⁺ (lanes-up L c at (b ∷ bs) fb) (lanes-up L c at as fa)
        ft′ = everyT-∪ t (cut l) (up L c at t ft) (up L c at (cut l) cl)
    freshᴿ (fr-lane op (just e) bs       l as       [] t (end c) L fo fb cl rx kx fa fq ft at od) =
      whole-fresh c (just e) (bs ++ as) (t ∪ cut l) fo′ fl′ ft′
      , fr-go op (just e) (bs ++ as) [] (t ∪ cut l) c fo′ fl′ fq ft′ (proj₁ (ordered od)) (proj₂ (ordered od))
      where
        fo′ = outer-up L c at (just e) fo
        fl′ = All++⁺ (lanes-up L c at bs fb) (lanes-up L c at as fa)
        ft′ = everyT-∪ t (cut l) (up L c at t ft) (up L c at (cut l) cl)
    freshᴿ (fr-lane op o bs l as qs t hush L fo fb cl rx kx fa fq ft at od) = tt

-- Two marks under one position, neither's lane keyed by the other's,
-- nor its lane by it.
sibling-spread : ∀ p {l l′} → Mark l → Mark l′ → l ≢ l′
               → Disjoint ((p ++ [ l ]) ++ [ ix 1 ]) ((p ++ [ l′ ]) ++ [ ix 1 ]) × ¬ Owned (p ++ [ l ]) ((p ++ [ l′ ]) ++ [ ix 1 ])
sibling-spread p {l} {l′} m m′ ne = disjoint-swap _ _ d₂ , proj₁ d₁
  where
    d₁ = apart-mark (p ++ [ l ]) (p ++ [ l′ ]) (ix 1) (ix-mark 1) (sibling p m′ ne , sibling p m (λ e → ne (sym e)))
    d₂ = apart-mark ((p ++ [ l′ ]) ++ [ ix 1 ]) (p ++ [ l ]) (ix 1) (ix-mark 1) (disjoint-swap _ _ d₁)

weigh-++ : ∀ a b → weigh (a ++ b) ≡ weigh a + weigh b
weigh-++ []      b = refl
weigh-++ (l ∷ a) b = trans (cong (weighˡ l +_) (weigh-++ a b)) (sym (+-assoc (weighˡ l) (weigh a) (weigh b)))

-- A position keyed under a value's lane shares its second label: a tag
-- the value's own root holds, so smaller than it.
second-sub : ∀ r i n e z → Prefix ((r ++ [ ix i ]) ++ [ ix 1 ]) (ix n ∷ sub e ∷ z) → weigh e < weigh r
second-sub []           i n e z (_ , () , _)
second-sub (a ∷ [])     i n e z (_ , () , _)
second-sub (a ∷ b ∷ r′) i n e z (_ , refl , _) = ≤-trans (m≤m+n (suc (weigh e)) (weigh r′)) (m≤n+m _ (weighˡ a))

-- After a value at `r ++ [ ix i ]` of a cold's burst: the burst's later
-- steps its siblings, and every later frame rooted past the close, its
-- root tagging the close before it, so heavier than the value's lane.
module Apart {A : Set} (τ : ℕ) (r : Pos) (i : ℕ) where
  private
    X1 = (r ++ [ ix i ]) ++ [ ix 1 ]

  data Chain : Pos → Set where
    base : Chain (r ++ [ last ])
    step : ∀ {e} n → Chain e → Chain (ix n ∷ sub e ∷ last ∷ [])

  x1≡ : weigh X1 ≡ (weigh r + 1) + 1
  x1≡ = trans (weigh-++ (r ++ [ ix i ]) [ ix 1 ]) (cong (_+ 1) (weigh-++ r [ ix i ]))

  chain-weigh : ∀ {e} → Chain e → weigh r + 1 ≤ weigh e
  chain-weigh base         = subst (_≤ weigh (r ++ [ last ])) (weigh-++ r [ last ]) ≤-refl
  chain-weigh (step {e} n c) = ≤-trans (chain-weigh c) (≤-trans (m≤m+n (weigh e) 1) (≤-trans (n≤1+n _) (n≤1+n _)))

  nested : ∀ {e} → Chain e → weigh e < weigh r → ⊥
  nested c lt = <-irrefl refl (<-≤-trans lt (≤-trans (m≤m+n (weigh r) 1) (chain-weigh c)))

  frame-big : ∀ {e} → Chain e → ∀ n {l} → Mark l → weigh X1 < weigh (ix n ∷ sub e ∷ l ∷ [])
  frame-big {e} c n {l} (ix-mark _) = subst (_< weigh (ix n ∷ sub e ∷ l ∷ [])) (sym x1≡) (s≤s (≤-trans (+-monoˡ-≤ 1 (chain-weigh c)) (n≤1+n (weigh e + 1))))
  frame-big {e} c n {l} last-mark   = subst (_< weigh (ix n ∷ sub e ∷ l ∷ [])) (sym x1≡) (s≤s (≤-trans (+-monoˡ-≤ 1 (chain-weigh c)) (n≤1+n (weigh e + 1))))

  big : ∀ {h} → weigh X1 < weigh h → ¬ Owned h X1
  big lt o = <-irrefl refl (<-≤-trans lt (owned-weigh _ _ o))

  big-ext : ∀ {h} z → weigh X1 < weigh h → ¬ Owned (h ++ z) X1
  big-ext {h} z lt = big (<-≤-trans lt (prefix-weigh h (h ++ z) (prefix-++ h z)))

  no-own : ∀ {e} → Chain e → ¬ Owned X1 e
  no-own base o = sibling r last-mark (λ ()) (owned-trans (r ++ [ ix i ]) X1 (r ++ [ last ]) (inj₁ (prefix-++ (r ++ [ ix i ]) [ ix 1 ])) o)
  no-own (step {e} n c) (inj₁ q)        = nested c (second-sub r i n e _ q)
  no-own (step n c)     (inj₂ (inj₁ o)) = no-own c o
  no-own (step n c)     (inj₂ (inj₂ ()))

  far : ∀ {e} → Chain e → ∀ n {l} → Mark l → ¬ Owned X1 (ix n ∷ sub e ∷ l ∷ ix 1 ∷ [])
  far {e} c n m           (inj₁ q)        = nested c (second-sub r i n e _ q)
  far c n m               (inj₂ (inj₁ o)) = no-own c o
  far c n (ix-mark _)     (inj₂ (inj₂ ()))
  far c n last-mark       (inj₂ (inj₂ ()))

  frame-sp : ∀ {e} → Chain e → ∀ n {l} → Mark l → Sp (r ++ [ ix i ]) (ix n ∷ sub e ∷ l ∷ [])
  frame-sp {e} c n {l} m = (big-ext {h = ix n ∷ sub e ∷ l ∷ []} [ ix 1 ] (frame-big c n m) , far c n m) , big {h = ix n ∷ sub e ∷ l ∷ []} (frame-big c n m)

  mutual
    frames-apart : ∀ {e t} → Chain e → Sp (r ++ [ ix i ]) e → (m : From A t) → Every (Sp (r ++ [ ix i ])) (M′.frames τ e m)
    frames-apart c ok M.done       = record { every = ok }
    frames-apart c ok M.quiet      = record { every = tt }
    frames-apart c ok (M.at t _ b) = chain-burst (τ + t) c 0 b

    chain-burst : ∀ {e t} n → Chain e → ∀ j (b : M.Frame A t) → Every (Sp (r ++ [ ix i ])) (M′.burst τ (ix n ∷ sub e ∷ []) j b)
    every (chain-burst n c j (M.emit a k)) = frame-sp c n (ix-mark j) , chain-burst n c (suc j) k , everyT-idle
    every (chain-burst n c j (M.stall k))  = frame-sp c n (ix-mark j) , chain-burst n c (suc j) (M.Frame∞.force k) , everyT-idle
    every (chain-burst n c j (M.close k))  =
      frame-sp c n (ix-mark j) , frames-apart (step n c) (frame-sp c n last-mark) (M.From∞.force k) , everyT-idle

  burst-apart : ∀ {t} j → i < j → (b : M.Frame A t) → Every (Sp (r ++ [ ix i ])) (M′.burst τ r j b)
  every (burst-apart j lt (M.emit a k)) = sib j lt , burst-apart (suc j) (<-≤-trans lt (n≤1+n j)) k , everyT-idle
    where sib : ∀ j → i < j → Sp (r ++ [ ix i ]) (r ++ [ ix j ])
          sib j lt = sibling-spread r (ix-mark j) (ix-mark i) (λ { refl → <⇒≢ lt refl })
  every (burst-apart j lt (M.stall k))  = sib j lt , burst-apart (suc j) (<-≤-trans lt (n≤1+n j)) (M.Frame∞.force k) , everyT-idle
    where sib : ∀ j → i < j → Sp (r ++ [ ix i ]) (r ++ [ ix j ])
          sib j lt = sibling-spread r (ix-mark j) (ix-mark i) (λ { refl → <⇒≢ lt refl })
  every (burst-apart j lt (M.close k))  =
    sibling-spread r (ix-mark j) (ix-mark i) (λ { refl → <⇒≢ lt refl })
    , frames-apart base (sibling-spread r last-mark (ix-mark i) (λ ())) (M.From∞.force k) , everyT-idle

-- A COLD LEAF'S RUN SPREADS: each burst's steps siblings, each frame
-- tagged by the close before it.
spread-frames : ∀ {A t} τ e (m : From A t) → Spread (M′.frames τ e m)
spread-burst : ∀ {A t} τ r i (b : M.Frame A t) → Spread (M′.burst τ r i b)
spread-frames τ e M.done       = record { spread = tt }
spread-frames τ e M.quiet      = record { spread = tt }
spread-frames τ e (M.at t _ b) = spread-burst τ (ix (τ + t) ∷ sub e ∷ []) 0 b

spread (spread-burst τ r i (M.emit a k)) =
  (Apart.burst-apart τ r i (suc i) ≤-refl k , everyT-idle) , spread-burst τ r (suc i) k
spread (spread-burst τ r i (M.stall k))  = spread-burst τ r (suc i) (M.Frame∞.force k)
spread (spread-burst τ r i (M.close k))  = spread-frames τ (r ++ [ last ]) (M.From∞.force k)

spread-start : ∀ {A} p (m : From A 0) → Headed p → Spread (M′.start p m)
spread-start p (M.at zero _ b)    _ = spread-burst (tick p) p 0 b
spread-start p (M.at (suc t) l b) _ = spread-frames (tick p) (p ++ [ last ]) (M.at (suc t) l b)
spread-start p M.done             _ = spread-frames {t = 0} (tick p) (p ++ [ last ]) M.done
spread-start p M.quiet            _ = spread-frames {t = 0} (tick p) (p ++ [ last ]) M.quiet

-- A LIST'S RUN SPREADS: its values siblings, its end beside them.
of-apart : ∀ {A} p i j (xs : List A) → i < j
         → Every (λ y → Disjoint (y ++ [ ix 1 ]) ((p ++ [ ix i ]) ++ [ ix 1 ]) × ¬ Owned y ((p ++ [ ix i ]) ++ [ ix 1 ])) (M′.ofᴱ p j xs)
every (of-apart p i j []       lt) = sibling-spread p last-mark (ix-mark i) (λ ())
every (of-apart p i j (x ∷ xs) lt) =
  sibling-spread p (ix-mark j) (ix-mark i) (λ { refl → <⇒≢ lt refl }) , of-apart p i (suc j) xs (<-≤-trans lt (m≤n+m j 1)) , everyT-idle

spread-of : ∀ {A} p i (xs : List A) → Spread (M′.ofᴱ p i xs)
spread (spread-of p i [])       = tt
spread (spread-of p i (x ∷ xs)) = (of-apart p i (suc i) xs ≤-refl , everyT-idle) , spread-of p (suc i) xs

-- A cut shows its source's positions, or a step just under one.
module _ {P : Pos → Set} (d₀ : ∀ h → P h → P (h ++ [ ix 0 ])) (dₗ : ∀ h → P h → P (h ++ [ last ])) where
  mutual
    every-cut : ∀ {A} i (q : A → Bool) (e : Events A) → Every P e → Every P (M′.takeWhileᴱ i q e)
    every (every-cut i q (out k a r) pe) = every (every-cutting i q k a (q a) r pe)
    every (every-cut i q (skip k r)  pe) = proj₁ (every pe) , every-cut i q (force r) (proj₁ (proj₂ (every pe))) , proj₂ (proj₂ (every pe))
    every (every-cut i q (end k)     pe) = every pe
    every (every-cut i q hush        pe) = tt

    every-cutting : ∀ {A} i (q : A → Bool) k a b (r : Events∞ A) → Every P (out k a r) → Every P (M′.taking i q k a b r)
    every (every-cutting i     q k a true  r pe) = proj₁ (every pe) , every-cut i q (force r) (proj₁ (proj₂ (every pe))) , proj₂ (proj₂ (every pe))
    every (every-cutting true  q k a false r pe) = d₀ k (proj₁ (every pe)) , record { every = dₗ k (proj₁ (every pe)) } , proj₂ (proj₂ (every pe))
    every (every-cutting false q k a false r pe) = dₗ k (proj₁ (every pe))

-- Apart from a lane, a step just under it too.
sp-mark : ∀ x k {l} → Mark l → Sp x k → Sp x (k ++ [ l ])
sp-mark x k {l} m ((_ , b) , c) =
  ( (λ o → c (owned-drop k [ l ] _ (owned-drop (k ++ [ l ]) [ ix 1 ] _ o)))
  , proj₁ (apart-mark (x ++ [ ix 1 ]) (k ++ [ l ]) (ix 1) (ix-mark 1) (apart-mark (x ++ [ ix 1 ]) k l m (nk , c))) )
  , (λ o → c (owned-drop k [ l ] _ o))
  where
    nk : ¬ Owned (x ++ [ ix 1 ]) k
    nk o = b (owned-trans (x ++ [ ix 1 ]) k (k ++ [ ix 1 ]) o (inj₁ (prefix-++ k [ ix 1 ])))

-- What a source left running apart from a value: apart from the step
-- kept just inside it.
sp-cut : ∀ k t → Disjoint k t → Sp (k ++ [ ix 0 ]) t
sp-cut k t d =
  ( (λ o → proj₁ d₁ (owned-drop t [ ix 1 ] _ o))
  , (λ o → proj₁ (apart-mark k t (ix 1) (ix-mark 1) d) (owned-drop k [ ix 0 ] _ (owned-drop (k ++ [ ix 0 ]) [ ix 1 ] _ o))) )
  , proj₁ d₁
  where
    d₁ = apart-mark t (k ++ [ ix 0 ]) (ix 1) (ix-mark 1) (apart-mark t k (ix 0) (ix-mark 0) (disjoint-swap k t d))

-- A CUT SPREADS ITS SOURCE'S RUN: a failing value kept just inside its
-- own position, which nothing its source left running keys.
spread-take : ∀ {A} i (q : A → Bool) (e : Events A) c → Trail e c → Spread e → Spread (M′.takeWhileᴱ i q e)
spread-taking : ∀ {A} i (q : A → Bool) k a b (r : Events∞ A) c → Trail (out k a r) c → Spread (out k a r) → Spread (M′.taking i q k a b r)
spread (spread-take i q (out k a r) c t s) = spread (spread-taking i q k a (q a) r c t s)
spread (spread-take i q (skip k r)  c t s) = spread-take i q (force r) (cut r) (proj₂ (proj₂ (trail t))) (spread s)
spread (spread-take i q (end k)     c t s) = tt
spread (spread-take i q hush        c t s) = tt

spread (spread-taking i     q k a true  r c t s) =
  ( every-cut (λ h → sp-mark k h (ix-mark 0)) (λ h → sp-mark k h last-mark) i q (force r) (proj₁ (proj₁ (spread s)))
  , proj₂ (proj₁ (spread s)) )
  , spread-take i q (force r) (cut r) (proj₁ (proj₂ (proj₂ (trail t)))) (proj₂ (spread s))
spread (spread-taking true  q k a false r c t s) =
  ( record { every = sibling-spread k last-mark (ix-mark 0) (λ ()) }
  , everyT-mono (sp-cut k) (cut r) (proj₂ (proj₂ (proj₂ (trail t)))) )
  , record { spread = tt }
spread (spread-taking false q k a false r c t s) = tt

-- Two of a source's positions apart, the second alien to the joiner,
-- both tagged with it: the first keys nothing of the second's lane.
tagged-apart : ∀ p a b → ¬ Owned p b → a ≢ b → ¬ Owned (a ++ [ sub p ]) ((b ++ [ sub p ]) ++ [ ix 1 ])
tagged-apart p a b nb ne (inj₁ pr) with prefix-split (a ++ [ sub p ]) (b ++ [ sub p ]) (ix 1) pr
... | inj₂ eq = snoc-ne a (b ++ [ sub p ]) (λ ()) eq
... | inj₁ pr′ with prefix-split (a ++ [ sub p ]) b (sub p) pr′
...   | inj₁ pb = nb (sub-owned a p b (inj₁ pb))
...   | inj₂ eq = ne (proj₁ (snoc-inj a b eq))
tagged-apart p a b nb ne (inj₂ t) with tagged-split (a ++ [ sub p ]) b p (tagged-lane (a ++ [ sub p ]) (b ++ [ sub p ]) 1 t)
... | inj₁ tb = nb (inj₂ (sub-tagged a p b tb))
... | inj₂ o  = heavy a p o

-- A joiner's own step keys nothing of a tagged lane over a source alien
-- to it, and the tagged position nothing of the step's lane.
pre-apart : ∀ p q l → ¬ Owned p q → ¬ Owned (p ++ [ l ]) ((q ++ [ sub p ]) ++ [ ix 1 ])
pre-apart p q l nq (inj₂ t) with tagged-split (p ++ [ l ]) q p (tagged-lane (p ++ [ l ]) (q ++ [ sub p ]) 1 t)
... | inj₁ tq = nq (owned-drop p [ l ] q (inj₂ tq))
... | inj₂ o  = longer p l o
pre-apart p q l nq (inj₁ pr) with prefix-split p (q ++ [ sub p ]) (ix 1) (prefix-trans p (p ++ [ l ]) ((q ++ [ sub p ]) ++ [ ix 1 ]) (prefix-++ p [ l ]) pr)
... | inj₂ eq = heavy q p (inj₁ (subst (Prefix (q ++ [ sub p ])) (sym eq) (prefix-++ (q ++ [ sub p ]) [ ix 1 ])))
... | inj₁ pr′ with prefix-split p q (sub p) pr′
...   | inj₁ pq = nq (inj₁ pq)
...   | inj₂ eq = heavy q p (inj₁ (subst (Prefix (q ++ [ sub p ])) (sym eq) (prefix-refl (q ++ [ sub p ]))))

pre-apart′ : ∀ p q {l} → Mark l → ¬ Owned (q ++ [ sub p ]) ((p ++ [ l ]) ++ [ ix 1 ])
pre-apart′ p q {l} m (inj₁ pr) with prefix-split (q ++ [ sub p ]) (p ++ [ l ]) (ix 1) pr
... | inj₂ eq = snoc-ne q (p ++ [ l ]) (λ ()) eq
... | inj₁ pr′ with prefix-split (q ++ [ sub p ]) p l pr′
...   | inj₁ pp = heavy q p (inj₁ pp)
...   | inj₂ eq = snoc-ne q p (mark-sub m p) eq
pre-apart′ p q {l} m (inj₂ t) =
  heavy q p (inj₂ (tagged-mark (q ++ [ sub p ]) p l m (tagged-lane (q ++ [ sub p ]) (p ++ [ l ]) 1 t)))

sp-join : ∀ p q h → ¬ Owned p q → ¬ Owned p h → q <ᵖ h ≡ true → Sp (q ++ [ sub p ]) (h ++ [ sub p ])
sp-join p q h nq nh qh =
  ( (λ o → tagged-apart p h q nq hq (owned-drop (h ++ [ sub p ]) [ ix 1 ] _ o))
  , (λ o → tagged-apart p q h nh (λ e → hq (sym e)) (owned-drop (q ++ [ sub p ]) [ ix 1 ] _ o)) )
  , tagged-apart p h q nq hq
  where
    hq : h ≢ q
    hq e with trans (sym (subst (λ x → q <ᵖ x ≡ true) e qh)) (<ᵖ-irrefl q)
    ... | ()

sp-pre : ∀ p q {l} → Mark l → ¬ Owned p q → Sp (q ++ [ sub p ]) (p ++ [ l ])
sp-pre p q {l} m nq =
  ( (λ o → pre-apart p q l nq (owned-drop (p ++ [ l ]) [ ix 1 ] _ o))
  , (λ o → pre-apart′ p q m (owned-drop (q ++ [ sub p ]) [ ix 1 ] _ o)) )
  , pre-apart p q l nq

-- Strictly past `q`, then no earlier than that: strictly past `q`.
beyond-on : ∀ {A} q h (e : Events A) → q <ᵖ h ≡ true → Atop h e → Beyond q e
beyond-on q h (out k _ _) qh a with <ᵖ-split h k a
... | inj₁ hk   = <ᵖ-trans q h k qh hk
... | inj₂ refl = qh
beyond-on q h (skip k _)  qh a with <ᵖ-split h k a
... | inj₁ hk   = <ᵖ-trans q h k qh hk
... | inj₂ refl = qh
beyond-on q h (end k)     qh a with <ᵖ-split h k a
... | inj₁ hk   = <ᵖ-trans q h k qh hk
... | inj₂ refl = qh
beyond-on q h hush        qh a = tt

-- What a joiner shows after a value tagged from `q`, over a source past
-- it: tagged from past `q`, or its own step.
module _ (p q : Pos) (nq : ¬ Owned p q) where
  mutual
    sp-rejoin : ∀ {A} (e : Events A) → Alien p e → Ordered e → Beyond q e → Every (Sp (q ++ [ sub p ])) (M′.rejoin p e)
    every (sp-rejoin (out h a k) al o b) =
      every (sp-shown h (just a) k (p <ᵖ h) (proj₁ (every al)) (proj₁ (proj₂ (every al))) (proj₁ (ordered o)) (proj₂ (ordered o)) b)
    every (sp-rejoin (skip h k)  al o b) =
      every (sp-shown h nothing k (p <ᵖ h) (proj₁ (every al)) (proj₁ (proj₂ (every al))) (proj₁ (ordered o)) (proj₂ (ordered o)) b)
    every (sp-rejoin (end c)     al o b) with p <ᵖ c
    ... | true  = sp-join p q c nq (every al) b
    ... | false = sp-pre p q last-mark nq
    every (sp-rejoin hush        al o b) = tt

    sp-shown : ∀ {A} h (a : Maybe A) (k : Events∞ A) c → ¬ Owned p h → Alien p (force k) → Atop h (force k) → Ordered (force k)
             → q <ᵖ h ≡ true → Every (Sp (q ++ [ sub p ])) (M′.shown p h a k c)
    every (sp-shown h (just a) k true  nh al at o qh) =
      sp-join p q h nq nh qh , sp-rejoin (force k) al o (beyond-on q h (force k) qh at) , everyT-idle
    every (sp-shown h nothing  k true  nh al at o qh) =
      sp-join p q h nq nh qh , sp-rejoin (force k) al o (beyond-on q h (force k) qh at) , everyT-idle
    every (sp-shown h (just a) k false nh al at o qh) =
      sp-pre p q (ix-mark 0) nq , sp-rejoin (force k) al o (beyond-on q h (force k) qh at) , everyT-idle
    every (sp-shown h nothing  k false nh al at o qh) =
      sp-pre p q (ix-mark 0) nq , sp-rejoin (force k) al o (beyond-on q h (force k) qh at) , everyT-idle

-- A JOINER'S RUN SPREADS over a source in order, steady and alien to
-- it: each value its source's, tagged with the joiner.
spread-rejoin : ∀ {A} p (e : Events A) → Ordered e → Steady e → Alien p e → Spread (M′.rejoin p e)
spread (spread-rejoin p (out q a k) o st al) with p <ᵖ q
... | true  =
  ( sp-rejoin p q (proj₁ (every al)) (force k) (proj₁ (proj₂ (every al))) (proj₂ (ordered o)) (past-beyond q (force k) (proj₁ (steady st)))
  , everyT-idle )
  , spread-rejoin p (force k) (proj₂ (ordered o)) (proj₂ (steady st)) (proj₁ (proj₂ (every al)))
... | false = spread-rejoin p (force k) (proj₂ (ordered o)) (proj₂ (steady st)) (proj₁ (proj₂ (every al)))
spread (spread-rejoin p (skip q k) o st al) with p <ᵖ q
... | true  = spread-rejoin p (force k) (proj₂ (ordered o)) (proj₂ (steady st)) (proj₁ (proj₂ (every al)))
... | false = spread-rejoin p (force k) (proj₂ (ordered o)) (proj₂ (steady st)) (proj₁ (proj₂ (every al)))
spread (spread-rejoin p (end c) o st al) with p <ᵖ c
... | true  = tt
... | false = tt
spread (spread-rejoin p hush o st al) = tt

-- A FLATMAP'S CUTS ARE FRESH, over sorted sources alien to where it
-- subscribes: a lane inside an outer value at `q` is admitted at the skip
-- the flatMap shows just past `q`, and a lane a completion admits at the
-- skip just past that completion.
fresh-flat : ∀ {Γ A B} op (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) → (∀ a → Finite (f a)) → Finite s
           → ∀ p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
           → Fresh∞ p (U.stateᴺ (U.subscribe (flatMap op f s) p) ρ)

-- A CONNECT'S CUTS ARE FRESH, over sorted sources alien to where it
-- subscribes: its source's burst lies inside only its own subscription,
-- and its body shows nothing the connect does not.
fresh-connect : ∀ {Γ A B} (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) → Finite s → Finite b
              → ∀ p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
              → Fresh∞ p (U.stateᴺ (U.subscribe (connect s b) p) ρ)

-- A DEFER'S CUTS ARE FRESH, its program's being: what is alien to the
-- defer is alien to its program, and before the program's position only
-- if before the defer's skip.
fresh-defer : ∀ {Γ A} (l : Later Timeline Γ A) p (ρ : NEnv Γ) → Headed p → Alienᴱ p ρ
            → Fresh∞ (p ++ [ ix 1 ]) (U.stateᴺ (U.subscribe (Later.force l) (p ++ [ ix 1 ])) ρ)
            → Fresh∞ p (U.stateᴺ (U.deferᶜ l p []) ρ)
fresh-defer l p ρ hp cl (fc , fr) =
  everyT-idle
  , record { freshᴿ = everyT-≈ _ _ (λ k → agreeᵀ (U.subscribed (Later.force l) (env-refl (U.hots ρ))) P₁) (everyT-mono first _ fc)
                    , fresh-≈ p S X alike (fresh-widen p P₁ wide S fr) }
  where
    open Deferred l p ρ hp cl
    wide : ∀ k → ¬ Owned p k → ¬ Owned P₁ k
    wide k no o = no (owned-trans p P₁ k (inj₁ (prefix-++ p [ ix 1 ])) o)
    first : ∀ h → Fresh P₁ P₁ h → Fresh p (p ++ [ ix 0 ]) h
    first h f k x d with f k x (wide k d)
    ... | inj₂ t  = inj₂ t
    ... | inj₁ kl = inj₁ (below-lane p k 1 0 (λ q → d (inj₁ q)) kl)

-- A FINITE PROGRAM'S CUTS ARE FRESH, where a tick heads it, over sorted
-- sources alien to it: at every state, what it leaves running lies inside
-- nothing alien to it but a bare tick or a position before the step it
-- last showed.
fresh-subᶠ : ∀ {Γ A} (o : Obs Timeline Γ A) → Finite o → ∀ p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
           → Fresh∞ p (U.stateᴺ (U.subscribe o p) ρ)
-- A FINITE PROGRAM'S CUTS TRAIL ITS RUN, where a tick heads it, over
-- sorted sources alien to it: at every state, what a cut would leave
-- running is sorted and flat, none of it before a value coming next, nor
-- before a skip but the step that skip shows just past it; all of it past
-- an end, none keyed where that end would subscribe a lane, nor over it.
trailing-subᶠ : ∀ {Γ A} (o : Obs Timeline Γ A) → Finite o → ∀ p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
              → Trailing (U.stateᴺ (U.subscribe o p) ρ)


-- A FINITE PROGRAM'S VALUES SPREAD, where a tick heads it, over sorted
-- sources alien to it: after a value at `x`, nothing later, shown or
-- left running, keys where a lane admitted at `x` would, nor where a
-- later value's lane would key under it.
spread-subᶠ : ∀ {Γ A} (o : Obs Timeline Γ A) → Finite o → ∀ p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
            → Spread (U.meaning (U.subscribe o p) ρ)

-- A FLATMAP'S VALUES SPREAD, over sorted sources alien to where it
-- subscribes: each lane keyed apart from every other, as the outer's
-- values are.
spread-flat : ∀ {Γ A B} op (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) → (∀ a → Finite (f a)) → Finite s
            → ∀ p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
            → Spread (U.meaning (U.subscribe (flatMap op f s) p) ρ)

-- A CONNECT'S VALUES SPREAD, over sorted sources alien to where it
-- subscribes: its body's values, its source's steps only skips, each
-- past every body value shown before it.
spread-connect : ∀ {Γ A B} (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) → Finite s → Finite b
               → ∀ p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
               → Spread (U.meaning (U.subscribe (connect s b) p) ρ)

-- A CONNECT SUBSCRIBED IS IN ORDER: each source step a skip just past
-- it, ahead of the body's later events, and what the source runs on
-- with past the body's end left as the tail.
ordered-connect : ∀ {Γ A B} (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) → Finite s → Finite b
                → ∀ p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
                → Ordered (U.meaning (U.subscribe (connect s b) p) ρ)

-- A CONNECT SUBSCRIBED WHERE A TICK HEADS IS STEADY, over sources
-- sorted and alien to it: nothing the body shows lies above or below
-- where a source step shows, and the source's run past the body's end
-- steps where it would have.
steady-connect : ∀ {Γ A B} (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) → Finite s → Finite b
               → ∀ p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
               → Steady (U.meaning (U.subscribe (connect s b) p) ρ)

-- A FINITE PROGRAM SUBSCRIBED IS IN ORDER, where a tick heads, over
-- sorted sources alien to where it subscribes.
ordered-subᶠ : ∀ {Γ A} (o : Obs Timeline Γ A) → Finite o → ∀ p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
             → Ordered (U.meaning (U.subscribe o p) ρ)

-- A FLATMAP SUBSCRIBED MERGES IN ORDER AND STEADY, ITS CUTS TRAILING
-- IT: over sorted sources alien to where it subscribes.  An outer value at `q` shows as a skip
-- just past `q`, its outer steady so nothing ties there; a lane's end
-- at `c` with one queued shows a skip just past `c`, and no other lane,
-- nor the outer, ties at `c`; what an ended part left shows when it is
-- ahead of every part still running.  And no part's next lies inside
-- the event just shown.
--
-- REFUTED: 37b70651 of any outer node in order, by a joiner told a value and a skip at one position
-- REFUTED: 0d0df253 wherever no tick heads the position, a lane's timer frame sorting before the step admitting it
flat-calm : ∀ {Γ A B} op (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) → (∀ a → Finite (f a)) → Finite s
          → ∀ p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
          → Ordered (U.meaning (U.subscribe (flatMap op f s) p) ρ) × Steady (U.meaning (U.subscribe (flatMap op f s) p) ρ)
            × Trailing (U.stateᴺ (U.subscribe (flatMap op f s) p) ρ)

-- A SUBSCRIPTION OVER STEADY SOURCES IS STEADY: a joiner's skips for
-- what it missed sit just past the join, which nothing it rekeys
-- lies inside, its sources being alien to it.  Where a tick heads it,
-- as one heads every real subscription: elsewhere its frames sit at
-- bare ticks, ahead of its own steps.
--
-- REFUTED: 91953190 at the empty position, a lane's timer frame shown just inside the outer's step at its tick
-- REFUTED: 0d0df253 off the empty position where no tick heads it, that frame sorting before the step
-- REFUTED: 42e70878 over sources stepping and then emitting at one position, a takeWhile showing the value inside the step
steady-subᶠ : ∀ {Γ A} (o : Obs Timeline Γ A) → Finite o → ∀ p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
            → Steady (U.meaning (U.subscribe o p) ρ)
steady-subᶠ (cold c) _ p ρ hp so cl = subst Steady (sym (U.start-meaning p (timelineAt c p) ρ)) (steady-start p (timelineAt c p) hp)
steady-subᶠ empty _ p ρ hp so cl = record { steady = tt }
steady-subᶠ (of xs) _ p ρ hp so cl = steady-of p 0 xs
steady-subᶠ (map f s) (map-f fs) p ρ hp so cl = steady-map f _ (steady-subᶠ s fs p ρ hp so cl)
steady-subᶠ (scan f z s) (scan-f fs) p ρ hp so cl = steady-scan f z _ (steady-subᶠ s fs p ρ hp so cl)
steady-subᶠ (takeWhile i q s) (takeWhile-f fs) p ρ hp so cl = steady-take i q _ (steady-subᶠ s fs p ρ hp so cl)
steady-subᶠ (flatMap op f s) (flatMap-f ff fs) p ρ hp so cl = proj₁ (proj₂ (flat-calm op f s ff fs p ρ hp so cl))
steady-subᶠ (connect s b) (connect-f fs fb) p ρ hp so cl = steady-connect s b fs fb p ρ hp so cl
steady-subᶠ (connected i) _ p ρ hp so cl =
  steady-rejoin p _ (proj₁ (sorted-lookup ρ so i)) (proj₂ (sorted-lookup ρ so i)) (every-lookup (λ h → ¬ Owned p h) ρ cl i)
steady-subᶠ (defer l) (defer-f fl) p ρ hp so cl =
  steady-defer l p ρ hp cl (steady-subᶠ (Later.force l) fl (p ++ [ ix 1 ]) ρ (headed-snoc p hp) so
                              (alienᴱ-owned p (p ++ [ ix 1 ]) (inj₁ (prefix-++ p [ ix 1 ])) ρ cl))

-- Where a connect starts: its body and its source, each just subscribed.
-- A CONNECT'S BODY LIES UNDER NONE OF ITS SOURCE'S STEPS, over sources
-- sorted and alien to it: nothing the body shows or leaves running lies
-- under where a source step shows, its run past an end included.
--
-- RECOVERY: git show 43da74d9:agda-impl/adequacy/Placed.agda restores `alien-steps`, a subscription keying nothing just past its own events, from which this was read over a merge without tails
postulate
  under-shown-connect : ∀ {Γ A B} (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) → Finite s → Finite b
                      → ∀ p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
                      → Every∞ (λ k → Every∞ (λ q → ¬ Prefix (q ++ [ ix 0 ]) k) (U.stateᴺ (U.subscribe s (p ++ [ ix 1 ])) ρ))
                               (U.stateᴺ (U.subscribe b (p ++ [ ix 0 ])) (U.meaning (U.subscribe s (p ++ [ ix 1 ])) ρ ∷ᴬ ρ))

connect-side : ∀ {Γ A B} (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) → Finite s → Finite b → ∀ p (ρ : NEnv Γ) (hp : Headed p) → Sorted ρ
             → Alienᴱ p ρ → Walk.Side p hp (U.stateᴺ (U.subscribe b (p ++ [ ix 0 ])) (U.meaning (U.subscribe s (p ++ [ ix 1 ])) ρ ∷ᴬ ρ))
                                        (U.stateᴺ (U.subscribe s (p ++ [ ix 1 ])) ρ)
connect-side s b fs fb p ρ hp so cl = record
    { tb = trailing-subᶠ b fb P₀ ρ′ (headed-snoc p hp) so′ cl′
    ; ts = trailing-subᶠ s fs r ρ hr so cr
    ; os = ordered-subᶠ s fs r ρ hr so cr
    ; ss = steady-subᶠ s fs r ρ hr so cr
    ; kb = every∞-mono (beneath-owned P₀) Bᶜ (Reach.reachᶠ (keyedRules P₀) b fb P₀ ρ′ (inj₁ (prefix-refl P₀)) (every-monoᴱ (λ _ _ → tt) ρ′ cl′))
    ; ks = Reach.reachᶠ (apartRules P₀ (no-tick p)) s fs r ρ (sibling p (ix-mark _) (λ ()) , sibling p (ix-mark _) (λ ())) c₀
    ; kr = Reach.reachᶠ (risingRules r) b fb P₀ ρ′ rP₀ (Reach.reach (risingRules r) s r ρ rr rρ , rρ)
    ; hs = Reach.reachᶠ headedRules s fs r ρ hr (sorted-headed ρ so)
    ; rs = rS
    ; lf = P₀
    ; lo = inj₁ (prefix-refl P₀)
    ; lc = Bursting.every-cue r P₀ (force Sᶜ) (every-mono above (force Sᶜ) (every-zip (force Sᶜ) (proj₁ kS) (proj₁ rS)))
    ; fc = proj₁ fB
    ; fr = proj₂ fB
    }
  where
    r  = p ++ [ ix 1 ]
    P₀ = p ++ [ ix 0 ]
    hr = headed-snoc p hp
    cr = alienᴱ-owned p r (inj₁ (prefix-++ p [ ix 1 ])) ρ cl
    c₀ = alienᴱ-owned p P₀ (inj₁ (prefix-++ p [ ix 0 ])) ρ cl
    Sᶜ = U.stateᴺ (U.subscribe s r) ρ
    ρ′ = U.meaning (U.subscribe s r) ρ ∷ᴬ ρ
    Bᶜ = U.stateᴺ (U.subscribe b P₀) ρ′
    so′ : Sorted ρ′
    so′ = (ordered-subᶠ s fs r ρ hr so cr , steady-subᶠ s fs r ρ hr so cr) , headed-sub s r ρ hr so , so
    cl′ : Alienᴱ P₀ ρ′
    cl′ = alien-sub s p ρ cl , c₀
    rr : Rise r r
    rr = hr , λ k hk ok t → ⊥-elim (<-irrefl refl (tagged-weigh r r (owned-tagged r k r ok t)))
    rP₀ : Rise r P₀
    rP₀ = headed-snoc p hp , λ k hk ok t → ⊥-elim (sibling p (ix-mark _) (λ ()) (inj₂ (owned-tagged r k P₀ ok t)))
    rρ : Everyᴱ (Rise r) ρ
    rρ = rise-env p r (inj₁ (prefix-++ p [ ix 1 ])) ρ (sorted-headed ρ so) cl
    rS = every∞-mono (beneath-owned r) Sᶜ (Reach.reachᶠ (keyedRules r) s fs r ρ (inj₁ (prefix-refl r)) (every-monoᴱ (λ _ _ → tt) ρ cl))
    kS = Reach.reachᶠ (risingRules r) s fs r ρ rr rρ
    fB = fresh-subᶠ b fb P₀ ρ′ (headed-snoc p hp) so′ cl′
    up : ∀ h → P₀ <ᵖ h ≡ true → (h ++ [ ix 0 ]) <ᵖ P₀ ≡ false
    up h lt = <ᵖ-asym P₀ (h ++ [ ix 0 ]) (<ᵖ-trans P₀ h (h ++ [ ix 0 ]) lt (<ᵖ-below h []))
    above : ∀ h → Rise r h × Owned r h → (h ++ [ ix 0 ]) <ᵖ P₀ ≡ false
    above h (rh , oh) with rise-owned r r h rh hr (inj₁ (prefix-refl r)) oh
    ... | inj₁ e  = up h (subst (λ z → P₀ <ᵖ z ≡ true) e (proj₁ (next-ix p 0)))
    ... | inj₂ lt = up h (<ᵖ-trans P₀ r h (proj₁ (next-ix p 0)) lt)

-- A CONNECT'S CUTS TRAIL ITS RUN, where a tick heads it, over sorted
-- sources alien to it: its source's burst left running beside what its
-- body would leave trails what the connect shows next, at every state
-- the walk reaches.
trail-connect : ∀ {Γ A B} (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) → Finite s → Finite b → ∀ p (ρ : NEnv Γ) → Headed p → Sorted ρ
              → Alienᴱ p ρ → Trailing (U.stateᴺ (U.subscribe (connect s b) p) ρ)
trail-connect s b fs fb p ρ hp so cl = Walk.tr-beside p hp _ _ (connect-side s b fs fb p ρ hp so cl)

spread-connect {Γ} {A} {B} s b fs fb p ρ hp so cl =
  Walk.sp-beside {A} {B} p hp _ _ (connect-side s b fs fb p ρ hp so cl) (spread-subᶠ b fb P₀ ρ′ (headed-snoc p hp) so′ cl′)
  where
    r  = p ++ [ ix 1 ]
    P₀ = p ++ [ ix 0 ]
    hr = headed-snoc p hp
    cr = alienᴱ-owned p r (inj₁ (prefix-++ p [ ix 1 ])) ρ cl
    c₀ = alienᴱ-owned p P₀ (inj₁ (prefix-++ p [ ix 0 ])) ρ cl
    ρ′ = U.meaning (U.subscribe s r) ρ ∷ᴬ ρ
    so′ : Sorted ρ′
    so′ = (ordered-subᶠ s fs r ρ hr so cr , steady-subᶠ s fs r ρ hr so cr) , headed-sub s r ρ hr so , so
    cl′ : Alienᴱ P₀ ρ′
    cl′ = alien-sub s p ρ cl , c₀

steady-connect {Γ} {A} {B} s b fs fb p ρ hp so cl =
  W.st-beside (U.stateᴺ (U.subscribe b (p ++ [ ix 0 ])) ρ′) (U.stateᴺ (U.subscribe s r) ρ) (W.Side.ts sd) (W.Side.os sd) (W.Side.ss sd) (steady-subᶠ b fb (p ++ [ ix 0 ]) ρ′ (headed-snoc p hp) so′ cl′)
    (W.unrelated sd (under-shown-connect s b fs fb p ρ hp so cl))
  where
    module W = Walk {A} {B} p hp
    r  = p ++ [ ix 1 ]
    hr = headed-snoc p hp
    cr = alienᴱ-owned p r (inj₁ (prefix-++ p [ ix 1 ])) ρ cl
    c₀ = alienᴱ-owned p (p ++ [ ix 0 ]) (inj₁ (prefix-++ p [ ix 0 ])) ρ cl
    ρ′ = U.meaning (U.subscribe s r) ρ ∷ᴬ ρ
    so′ : Sorted ρ′
    so′ = (ordered-subᶠ s fs r ρ hr so cr , steady-subᶠ s fs r ρ hr so cr) , headed-sub s r ρ hr so , so
    cl′ : Alienᴱ (p ++ [ ix 0 ]) ρ′
    cl′ = alien-sub s p ρ cl , c₀
    sd = connect-side s b fs fb p ρ hp so cl

ordered-connect {Γ} {A} {B} s b fs fb p ρ hp so cl =
  W.or-beside (U.stateᴺ (U.subscribe b (p ++ [ ix 0 ])) ρ′) (U.stateᴺ (U.subscribe s r) ρ) (W.Side.ts sd) (W.Side.os sd) (ordered-subᶠ b fb (p ++ [ ix 0 ]) ρ′ (headed-snoc p hp) so′ cl′)
  where
    module W = Walk {A} {B} p hp
    r  = p ++ [ ix 1 ]
    hr = headed-snoc p hp
    cr = alienᴱ-owned p r (inj₁ (prefix-++ p [ ix 1 ])) ρ cl
    c₀ = alienᴱ-owned p (p ++ [ ix 0 ]) (inj₁ (prefix-++ p [ ix 0 ])) ρ cl
    ρ′ = U.meaning (U.subscribe s r) ρ ∷ᴬ ρ
    so′ : Sorted ρ′
    so′ = (ordered-subᶠ s fs r ρ hr so cr , steady-subᶠ s fs r ρ hr so cr) , headed-sub s r ρ hr so , so
    cl′ : Alienᴱ (p ++ [ ix 0 ]) ρ′
    cl′ = alien-sub s p ρ cl , c₀
    sd = connect-side s b fs fb p ρ hp so cl

fresh-connect {Γ} {A} {B} s b fs fb p ρ hp so cl = W.cuts-fresh fs₀ , W.fr-beside Bᶜ Sᶜ fs₀
  where
    module W = Walk {A} {B} p hp
    r  = p ++ [ ix 1 ]
    P₀ = p ++ [ ix 0 ]
    hr = headed-snoc p hp
    cr = alienᴱ-owned p r (inj₁ (prefix-++ p [ ix 1 ])) ρ cl
    c₀ = alienᴱ-owned p P₀ (inj₁ (prefix-++ p [ ix 0 ])) ρ cl
    Sᶜ = U.stateᴺ (U.subscribe s r) ρ
    ρ′ = U.meaning (U.subscribe s r) ρ ∷ᴬ ρ
    Bᶜ = U.stateᴺ (U.subscribe b P₀) ρ′
    so′ : Sorted ρ′
    so′ = (ordered-subᶠ s fs r ρ hr so cr , steady-subᶠ s fs r ρ hr so cr) , headed-sub s r ρ hr so , so
    cl′ : Alienᴱ P₀ ρ′
    cl′ = alien-sub s p ρ cl , c₀
    sd = connect-side s b fs fb p ρ hp so cl
    fS = fresh-subᶠ s fs r ρ hr so cr
    pP : P₀ <ᵖ p ≡ false
    pP = <ᵖ-asym p P₀ (<ᵖ-below p [])
    wide : ∀ k → ¬ Owned p k → ¬ Owned r k
    wide k no o = no (owned-trans p r k (inj₁ (prefix-++ p [ ix 1 ])) o)
    rPP : Rise P₀ P₀
    rPP = headed-snoc p hp , λ k hk ok t → ⊥-elim (<-irrefl refl (tagged-weigh P₀ P₀ (owned-tagged P₀ k P₀ ok t)))
    rPr : Rise P₀ r
    rPr = hr , λ k hk ok t → ⊥-elim (sibling p (ix-mark _) (λ ()) (inj₂ (owned-tagged P₀ k r ok t)))
    rρ : Everyᴱ (Rise P₀) ρ
    rρ = rise-env p P₀ (inj₁ (prefix-++ p [ ix 0 ])) ρ (sorted-headed ρ so) cl
    rB = Reach.reachᶠ (risingRules P₀) b fb P₀ ρ′ rPP (Reach.reach (risingRules P₀) s r ρ rPr rρ , rρ)
    past : ∀ h → Owned P₀ h × Rise P₀ h → h <ᵖ p ≡ false
    past h (oh , rh) with rise-owned P₀ P₀ h rh (headed-snoc p hp) (inj₁ (prefix-refl P₀)) oh
    ... | inj₁ e  = <ᵖ-asym p h (subst (λ z → p <ᵖ z ≡ true) e (<ᵖ-below p []))
    ... | inj₂ lt = <ᵖ-asym p h (<ᵖ-trans p P₀ h (<ᵖ-below p []) lt)
    atop : ∀ (x : Events B) → Every (λ h → h <ᵖ p ≡ false) x → Atop p x
    atop (out _ _ _) pe = proj₁ (every pe)
    atop (skip _ _)  pe = proj₁ (every pe)
    atop (end _)     pe = every pe
    atop hush        pe = tt
    fs₀ : W.FSide Bᶜ Sᶜ
    fs₀ = record
      { sd = sd
      ; ob = ordered-subᶠ b fb P₀ ρ′ (headed-snoc p hp) so′ cl′
      ; L  = p
      ; pL = <ᵖ-irrefl p
      ; cL = Bursting.cue-down r P₀ p (force Sᶜ) pP (W.Side.lc sd)
      ; bL = atop (force Bᶜ) (every-mono past (force Bᶜ) (every-zip (force Bᶜ) (proj₁ (W.Side.kb sd)) (proj₁ rB)))
      ; bc = everyT-mono (λ h f → fresh-under p [ ix 0 ] h (λ k x no → f k x (W.narrow₀ k no))) (cut Bᶜ) (W.Side.fc sd)
      ; sc = everyT-mono (λ h f → fresh-under p [ ix 1 ] h (λ k x no → f k x (wide k no))) (cut Sᶜ) (proj₁ fS)
      ; sr = fresh-widen p r wide (force Sᶜ) (proj₂ fS)
      }

fresh-subᶠ (cold c) _ p ρ hp so cl = fresh-start p (timelineAt c p) ρ
fresh-subᶠ empty _ p ρ hp so cl = everyT-idle , record { freshᴿ = tt }
fresh-subᶠ (of xs) _ p ρ hp so cl = everyT-idle , fresh-of p p 0 xs
fresh-subᶠ (map f s) (map-f fs) p ρ hp so cl =
  proj₁ (fresh-subᶠ s fs p ρ hp so cl) , fresh-map f p _ (proj₂ (fresh-subᶠ s fs p ρ hp so cl))
fresh-subᶠ (scan f z s) (scan-f fs) p ρ hp so cl =
  proj₁ (fresh-subᶠ s fs p ρ hp so cl) , fresh-scan f z p _ (proj₂ (fresh-subᶠ s fs p ρ hp so cl))
fresh-subᶠ (takeWhile i q s) (takeWhile-f fs) p ρ hp so cl =
  proj₁ (fresh-subᶠ s fs p ρ hp so cl) , fresh-take i q p _ (proj₂ (fresh-subᶠ s fs p ρ hp so cl))
fresh-subᶠ (flatMap op f s) (flatMap-f ff fs) p ρ hp so cl = fresh-flat op f s ff fs p ρ hp so cl
fresh-subᶠ (connect s b) (connect-f fs fb) p ρ hp so cl = fresh-connect s b fs fb p ρ hp so cl
fresh-subᶠ (connected i) _ p ρ hp so cl = everyT-idle , fresh-rejoin p p (lookup ρ i)
fresh-subᶠ (defer l) (defer-f fl) p ρ hp so cl =
  fresh-defer l p ρ hp cl (fresh-subᶠ (Later.force l) fl (p ++ [ ix 1 ]) ρ (headed-snoc p hp) so
                             (alienᴱ-owned p (p ++ [ ix 1 ]) (inj₁ (prefix-++ p [ ix 1 ])) ρ cl))

trailing-subᶠ (cold c) _ p ρ hp so cl = trailing-start p (timelineAt c p) ρ
trailing-subᶠ empty _ p ρ hp so cl = trail-idle _ tt
trailing-subᶠ (of xs) _ p ρ hp so cl = trail-of p 0 xs
trailing-subᶠ (map f s) (map-f fs) p ρ hp so cl = trail-map f _ _ (trailing-subᶠ s fs p ρ hp so cl)
trailing-subᶠ (scan f z s) (scan-f fs) p ρ hp so cl = trail-scan f z _ _ (trailing-subᶠ s fs p ρ hp so cl)
trailing-subᶠ (takeWhile i q s) (takeWhile-f fs) p ρ hp so cl =
  trail-take i q _ _ (ordered-subᶠ s fs p ρ hp so cl) (steady-subᶠ s fs p ρ hp so cl) (trailing-subᶠ s fs p ρ hp so cl)
trailing-subᶠ (flatMap op f s) (flatMap-f ff fs) p ρ hp so cl = proj₂ (proj₂ (flat-calm op f s ff fs p ρ hp so cl))
trailing-subᶠ (connect s b) (connect-f fs fb) p ρ hp so cl = trail-connect s b fs fb p ρ hp so cl
trailing-subᶠ (connected i) _ p ρ hp so cl = trail-rejoin p (lookup ρ i)
trailing-subᶠ (defer l) (defer-f fl) p ρ hp so cl =
  trail-defer l p ρ hp cl (trailing-subᶠ (Later.force l) fl (p ++ [ ix 1 ]) ρ (headed-snoc p hp) so
                             (alienᴱ-owned p (p ++ [ ix 1 ]) (inj₁ (prefix-++ p [ ix 1 ])) ρ cl))

-- A flatMap's outer, as its merge holds it.
flat-held : ∀ {Γ A B} (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) → (∀ a → Finite (f a)) → Finite s
          → ∀ p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
          → FlatOrder.Outer p (force (U.outer∞ (λ a q → U.subscribe (f a) q) (U.subscribe s p) ρ))
                              (cut (U.outer∞ (λ a q → U.subscribe (f a) q) (U.subscribe s p) ρ))
flat-held {Γ} {A} {B} f s ff fs p ρ hp so cl =
  O.outer (ordered-map F _ (ordered-subᶠ s fs p ρ hp so cl)) (steady-map F _ (steady-subᶠ s fs p ρ hp so cl))
    (trail-map F (force S) (cut S) (trailing-subᶠ s fs p ρ hp so cl)) (spread-map F _ (spread-subᶠ s fs p ρ hp so cl))
    (every-map F _ (proj₁ ko)) (proj₂ ko) (values-map F _ gen)
  where
    module O = FlatOrder p
    module O′ = FlatAfter p
    S = U.stateᴺ (U.subscribe s p) ρ
    F : A → MonotonicList B
    F a = M′.cold λ q → U.stateᴺ (U.subscribe (f a) q) ρ
    kp = Reach.reachᶠ (keyedRules p) s fs p ρ (inj₁ (prefix-refl p)) (every-monoᴱ (λ _ _ → tt) ρ cl)
    hd = Reach.reachᶠ headedRules s fs p ρ hp (sorted-headed ρ so)
    ko : Every∞ O.K S
    ko = every∞-mono (λ h bh → beneath-owned p h (proj₁ bh) , proj₂ bh) S
           (every-zip (force S) (proj₁ kp) (proj₁ hd) , everyT-zip (cut S) (proj₂ kp) (proj₂ hd))
    gen : ∀ a → O.Gen (F a)
    gen a j (bj , hj) =
      ordered-subᶠ (f a) (ff a) j ρ hj so cj , rise-sub (f a) j ρ hj , steady-subᶠ (f a) (ff a) j ρ hj so cj , trailing-subᶠ (f a) (ff a) j ρ hj so cj
      , O′.under∞ j L
          (every∞-mono (beneath-owned j) L (Reach.reachᶠ (keyedRules j) (f a) (ff a) j ρ (inj₁ (prefix-refl j)) (every-monoᴱ (λ _ _ → tt) ρ cj)))
          (Reach.reachᶠ headedRules (f a) (ff a) j ρ hj (sorted-headed ρ so))
          (λ R okR d → every∞-mono (λ _ → proj₁) L
             (Reach.reachᶠ (apartRules R (tick-beneath p R hp (proj₁ okR))) (f a) (ff a) j ρ d
                (alienᴱ-owned p R (beneath-owned p R (proj₁ okR)) ρ cl)))
      , spread-subᶠ (f a) (ff a) j ρ hj so cj
      where
        L  = U.stateᴺ (U.subscribe (f a) j) ρ
        cj = alienᴱ-owned p j (beneath-owned p j bj) ρ cl

flat-calm {Γ} {A} {B} op f s ff fs p ρ hp so cl =
  O.ordered-go (flatOp op) (just E) [] [] idle O.[]ᴿ tt []ᴬ []ᴬ held (sortedT-idle , everyT-idle , everyT-idle , flatT-idle)
  , calm-steady _ (proj₂ c₀) , calm-trail _ _ (proj₁ c₀) (proj₂ c₀)
  where
    module O = FlatOrder p
    module O′ = FlatAfter p
    E = U.outer∞ (λ a q → U.subscribe (f a) q) (U.subscribe s p) ρ
    held = flat-held f s ff fs p ρ hp so cl
    c₀ = O′.calm-at (flatOp op) (just E) [] [] idle O.[]ᴿ tt []ᴬ []ᴬ held (sortedT-idle , everyT-idle , everyT-idle , flatT-idle)

spread-flat {Γ} {A} {B} op f s ff fs p ρ hp so cl =
  FlatAfter.spread-go p (flatOp op) (just E) [] [] idle FlatOrder.[]ᴿ tt []ᴬ []ᴬ (flat-held f s ff fs p ρ hp so cl)
    (sortedT-idle , everyT-idle , everyT-idle , flatT-idle)
  where E = U.outer∞ (λ a q → U.subscribe (f a) q) (U.subscribe s p) ρ

fresh-flat {Γ} {A} {B} op f s ff fs p ρ hp so cl =
  W.whole-fresh p (just E) [] idle fo []ᴬ everyT-idle
  , W.fr-go (flatOp op) (just E) [] [] idle p fo []ᴬ []ᴬ everyT-idle
      (atop-go (flatOp op) (just E) [] [] idle p []ᴬ (atop-map F p _ (rise-sub s p ρ hp)) tt) (proj₁ (flat-calm op f s ff fs p ρ hp so cl))
  where
    module W = FlatFresh p
    S = U.stateᴺ (U.subscribe s p) ρ
    F : A → MonotonicList B
    F a = M′.cold λ q → U.stateᴺ (U.subscribe (f a) q) ρ
    E = U.outer∞ (λ a q → U.subscribe (f a) q) (U.subscribe s p) ρ
    kp = Reach.reachᶠ (keyedRules p) s fs p ρ (inj₁ (prefix-refl p)) (every-monoᴱ (λ _ _ → tt) ρ cl)
    hd = Reach.reachᶠ headedRules s fs p ρ hp (sorted-headed ρ so)
    ko : Every W.K (force S)
    ko = every-mono (λ h bh → beneath-owned p h (proj₁ bh) , proj₂ bh) (force S) (every-zip (force S) (proj₁ kp) (proj₁ hd))
    gen : ∀ a → W.GenF (F a)
    gen a q (oq , hq) = everyT-mono first (cut L) (proj₁ fL) , fresh-widen p j wide (force L) (proj₂ fL) , kL
      where
        j = q ++ [ ix 1 ]
        L = U.stateᴺ (U.subscribe (f a) j) ρ
        oj : Owned p j
        oj = owned-trans p q j oq (inj₁ (prefix-++ q [ ix 1 ]))
        hj = headed-snoc q hq
        cj = alienᴱ-owned p j oj ρ cl
        fL = fresh-subᶠ (f a) (ff a) j ρ hj so cj
        wide : ∀ k → ¬ Owned p k → ¬ Owned j k
        wide k no o = no (owned-trans p j k oj o)
        first : ∀ h → Fresh j j h → Fresh p (q ++ [ ix 0 ]) h
        first h fh k x no with fh k x (wide k no)
        ... | inj₂ t  = inj₂ t
        ... | inj₁ kj = inj₁ (below-lane q k 1 0 (λ pq → no (owned-trans p q k oq (inj₁ pq))) kj)
        kL : Every W.K (force L)
        kL = every-zip (force L)
               (every-mono (λ h bh → owned-trans p j h oj (beneath-owned j h bh)) (force L)
                  (proj₁ (Reach.reachᶠ (keyedRules j) (f a) (ff a) j ρ (inj₁ (prefix-refl j)) (every-monoᴱ (λ _ _ → tt) ρ cj))))
               (proj₁ (Reach.reachᶠ headedRules (f a) (ff a) j ρ hj (sorted-headed ρ so)))
    fo : W.Freshᴼ p (just E)
    fo = proj₁ fS , fresh-map F p _ (proj₂ fS) , values-map F _ gen , every-map F _ ko
      where fS = fresh-subᶠ s fs p ρ hp so cl

ordered-subᶠ (cold c) _ p ρ hp so cl = subst Ordered (sym (U.start-meaning p (timelineAt c p) ρ)) (ordered-start p (timelineAt c p) hp)
ordered-subᶠ empty _ p ρ hp so cl = record { ordered = tt }
ordered-subᶠ (of xs) _ p ρ hp so cl = ordered-of p 0 xs
ordered-subᶠ (map f s) (map-f fs) p ρ hp so cl = ordered-map f _ (ordered-subᶠ s fs p ρ hp so cl)
ordered-subᶠ (scan f z s) (scan-f fs) p ρ hp so cl = ordered-scan f z _ (ordered-subᶠ s fs p ρ hp so cl)
ordered-subᶠ (takeWhile i q s) (takeWhile-f fs) p ρ hp so cl = ordered-take i q _ (ordered-subᶠ s fs p ρ hp so cl)
ordered-subᶠ (flatMap op f s) (flatMap-f ff fs) p ρ hp so cl = proj₁ (flat-calm op f s ff fs p ρ hp so cl)
ordered-subᶠ (connect s b) (connect-f fs fb) p ρ hp so cl = ordered-connect s b fs fb p ρ hp so cl
ordered-subᶠ (connected i) _ p ρ hp so cl = ordered-rejoin p _ (proj₁ sl) (proj₂ sl)
  where sl = sorted-lookup ρ so i
ordered-subᶠ (defer l) (defer-f fl) p ρ hp so cl =
  ordered-defer l p ρ hp cl (ordered-subᶠ (Later.force l) fl (p ++ [ ix 1 ]) ρ (headed-snoc p hp) so
                               (alienᴱ-owned p (p ++ [ ix 1 ]) (inj₁ (prefix-++ p [ ix 1 ])) ρ cl))

spread-subᶠ (cold c) _ p ρ hp so cl = subst Spread (sym (U.start-meaning p (timelineAt c p) ρ)) (spread-start p (timelineAt c p) hp)
spread-subᶠ empty _ p ρ hp so cl = record { spread = tt }
spread-subᶠ (of xs) _ p ρ hp so cl = spread-of p 0 xs
spread-subᶠ (map f s) (map-f fs) p ρ hp so cl = spread-map f _ (spread-subᶠ s fs p ρ hp so cl)
spread-subᶠ (scan f z s) (scan-f fs) p ρ hp so cl = spread-scan f z _ (spread-subᶠ s fs p ρ hp so cl)
spread-subᶠ (takeWhile i q s) (takeWhile-f fs) p ρ hp so cl =
  spread-take i q _ _ (trailing-subᶠ s fs p ρ hp so cl) (spread-subᶠ s fs p ρ hp so cl)
spread-subᶠ (flatMap op f s) (flatMap-f ff fs) p ρ hp so cl = spread-flat op f s ff fs p ρ hp so cl
spread-subᶠ (connect s b) (connect-f fs fb) p ρ hp so cl = spread-connect s b fs fb p ρ hp so cl
spread-subᶠ (connected i) _ p ρ hp so cl =
  spread-rejoin p _ (proj₁ (sorted-lookup ρ so i)) (proj₂ (sorted-lookup ρ so i)) (every-lookup (λ h → ¬ Owned p h) ρ cl i)
spread-subᶠ (defer l) (defer-f fl) p ρ hp so cl =
  spread-defer l p ρ hp cl (spread-subᶠ (Later.force l) fl (p ++ [ ix 1 ]) ρ (headed-snoc p hp) so
                              (alienᴱ-owned p (p ++ [ ix 1 ]) (inj₁ (prefix-++ p [ ix 1 ])) ρ cl))

-- A PROGRAM SUBSCRIBED IS IN ORDER AND STEADY: its truncations are, and
-- it agrees with each for as many steps as it is deep.
ordered-sub : ∀ {Γ A} (o : Obs Timeline Γ A) p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ → Ordered (U.meaning (U.subscribe o p) ρ)
ordered-sub o p ρ hp so cl =
  ordered-lim (λ n → U.meaning (U.subscribe (trunc n o) p) ρ) _ (λ n → ordered-subᶠ (trunc n o) (finite-trunc n o) p ρ hp so cl)
    (λ n → trunc-agree n o p ρ)

steady-sub : ∀ {Γ A} (o : Obs Timeline Γ A) p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ → Steady (U.meaning (U.subscribe o p) ρ)
steady-sub o p ρ hp so cl =
  steady-lim (λ n → U.meaning (U.subscribe (trunc n o) p) ρ) _ (λ n → steady-subᶠ (trunc n o) (finite-trunc n o) p ρ hp so cl)
    (λ n → trunc-agree n o p ρ)

-- A program subscribed where a tick heads, over sorted sources alien to
-- where it subscribes, is placed.
placed-sub : ∀ {Γ A} (o : Obs Timeline Γ A) p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ → Placed (U.subscribe o p) ρ
placed-sub (cold c) p ρ hp so cl = ordered-sub (cold c) p ρ hp so cl , start-within p (timelineAt c p) ρ
placed-sub empty p ρ hp so cl = ordered-sub empty p ρ hp so cl , tt
placed-sub (of xs) p ρ hp so cl = ordered-sub (of xs) p ρ hp so cl , tt
placed-sub (map f s) p ρ hp so cl = ordered-sub (map f s) p ρ hp so cl , placed-sub s p ρ hp so cl
placed-sub (scan f z s) p ρ hp so cl = ordered-sub (scan f z s) p ρ hp so cl , placed-sub s p ρ hp so cl
placed-sub (takeWhile i q s) p ρ hp so cl = ordered-sub (takeWhile i q s) p ρ hp so cl , placed-sub s p ρ hp so cl
placed-sub (flatMap op f s) p ρ hp so cl =
  ordered-sub (flatMap op f s) p ρ hp so cl , placed-sub s p ρ hp so cl , tt
  , λ a x r → placed-sub (f a) (x ++ [ ix 1 ]) ρ (headed-lane x (every-reach _ (x ++ [ ix 0 ]) (headed-sub (flatMap op f s) p ρ hp so) r))
                so (alien-shown op f s p ρ cl x r)
placed-sub (connect s b) p ρ hp so cl = ordered-sub (connect s b) p ρ hp so cl , pb , ps , apart-sub s b p ρ hp cl
  where hs = headed-snoc p hp
        cs = alienᴱ-owned p (p ++ [ ix 1 ]) (inj₁ (prefix-++ p [ ix 1 ])) ρ cl
        ps = placed-sub s (p ++ [ ix 1 ]) ρ hs so cs
        pb = placed-sub b (p ++ [ ix 0 ]) (U.meaning (U.subscribe s (p ++ [ ix 1 ])) ρ ∷ᴬ ρ) (headed-snoc p hp)
               ((proj₁ ps , steady-sub s (p ++ [ ix 1 ]) ρ hs so cs) , headed-sub s (p ++ [ ix 1 ]) ρ hs so , so)
               (alien-sub s p ρ cl , alienᴱ-owned p (p ++ [ ix 0 ]) (inj₁ (prefix-++ p [ ix 0 ])) ρ cl)
placed-sub (connected i) p ρ hp so cl = ordered-sub (connected i) p ρ hp so cl , every-lookup (λ h → ¬ Owned p h) ρ cl i
placed-sub (defer l) p ρ hp so cl = ordered-sub (defer l) p ρ hp so cl , hp , so , cl

-- THE MEANING'S EVENTS ARE SORTED: a program subscribed at the root is
-- placed.
placed-subscribe : ∀ {A} (o : Obs Timeline [] A) → Placed (U.subscribe o root) []ᴬ
placed-subscribe o = placed-sub o root []ᴬ tt tt tt
