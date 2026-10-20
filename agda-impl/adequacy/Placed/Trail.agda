{-# OPTIONS --guardedness #-}

module adequacy.Placed.Trail where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List.Relation.Unary.All using (All; lookup) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_; map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to All++⁺; ++⁻ˡ to All++⁻ˡ; ++⁻ʳ to All++⁻ʳ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; cong)
open import Relation.Nullary using (¬_)

open import Tree using (Later)
open import denotation.MonotonicList.Events using (Events; Events∞; Pos; From; Timeline; out; skip; end; hush; ix; sub; last; tick; _<ᵖ_;
  <ᵖ-asym; <ᵖ-split; <ᵖ-irrefl; ≮-trans; <ᵖ-step; Tail; Tail∞; pin; idle; _∪_)
open import denotation.MonotonicList using (MonotonicList; Agree; out⁼; skip⁼; end⁼; hush⁼; Earliest; none; found; Agreeᵀ; pin⁼; idle⁼)
import denotation.MonotonicList.Events as M
import denotation.MonotonicList as M′
import denotation.Unfold as U
open import denotation.Unfold using (NEnv)
open import denotation.Denote using (flatOp) renaming (⟦_⟧ to ⟦_⟧ᴰ)
open import adequacy.Placed.Order using (Alienᴱ; Atop; Beneath; Every; EveryT; Every∞; Ext; Headed; Owned; Past; Prefix; every; everyT-idle; everyT-mono; everyT-∪; everyᵀ; ext; owned-ext; prefix-++; prefix-trans; still)
open import adequacy.Placed.Keys using (every-lim; every-map; every-scan; everyT-lim; everyT-≈; prefix-refl; rest; rest-agree; restᵀ-agree; tagged-lane)
open import adequacy.Placed.Rising using (AtopT; Atopᴹ; Beyond; module Deferred; Disjoint; atop-weaken; prefix-rest; prefix-split)

open Events∞
open Tail∞

------------------------------------------------------------------------
-- What a cut leaves running, against the run.

-- A tail's steps in order.
mutual
  SortedTs : Tail → Set
  SortedTs (pin k u) = AtopT k (later u) × SortedT (later u)
  SortedTs idle      = ⊤

  record SortedT (t : Tail) : Set where
    coinductive
    field sortedᵀ : SortedTs t

open SortedT public

sortedT-idle : SortedT idle
sortedᵀ sortedT-idle = tt

-- Two tails side by side: first whichever's first is.
atopT-∪ : ∀ h t u → AtopT h t → AtopT h u → AtopT h (t ∪ u)
atopT-∪ h idle      u at au = au
atopT-∪ h (pin k r) u at au = fst (M.sooner k u) u au
  where fst : ∀ b u → AtopT h u → AtopT h (M.first k r u b)
        fst true  u          au = at
        fst false idle       au = at
        fst false (pin k′ u) au = au

sooner-atop : ∀ k u → M.sooner k u ≡ true → AtopT k u
sooner-atop k idle       e = tt
sooner-atop k (pin k′ u) e = <ᵖ-asym k k′ e

mutual
  sortedT-∪ : ∀ t u → SortedT t → SortedT u → SortedT (t ∪ u)
  sortedT-∪ idle      u st su = su
  sortedT-∪ (pin k r) u st su = sortedT-first k r u (M.sooner k u) refl st su

  sortedT-first : ∀ k r u b → M.sooner k u ≡ b → SortedT (pin k r) → SortedT u → SortedT (M.first k r u b)
  sortedᵀ (sortedT-first k r u          true  e st su) =
    atopT-∪ k (later r) u (proj₁ (sortedᵀ st)) (sooner-atop k u e) , sortedT-∪ (later r) u (proj₂ (sortedᵀ st)) su
  sortedᵀ (sortedT-first k r idle       false e st su) = sortedᵀ st
  sortedᵀ (sortedT-first k r (pin k′ u) false e st su) =
    atopT-∪ k′ (pin k r) (later u) e (proj₁ (sortedᵀ su)) , sortedT-∪ (pin k r) (later u) st (proj₂ (sortedᵀ su))

-- A tail's steps never inside one before them.
mutual
  FlatTs : Tail → Set
  FlatTs (pin k u) = EveryT (λ h → ¬ Ext k h) (later u) × FlatT (later u)
  FlatTs idle      = ⊤

  record FlatT (t : Tail) : Set where
    coinductive
    field flatᵀ : FlatTs t

open FlatT public

flatT-idle : FlatT idle
flatᵀ flatT-idle = tt

-- Neither strictly inside the other.
Apart : Pos → Pos → Set
Apart a b = ¬ Ext a b × ¬ Ext b a

apart-of : ∀ {a b} → Disjoint a b → Apart a b
apart-of d = (λ x → proj₁ d (owned-ext x)) , (λ x → proj₂ d (owned-ext x))

-- Two flat tails side by side, no step of one inside a step of the other.
mutual
  flatT-∪ : ∀ t u → FlatT t → FlatT u → EveryT (λ a → EveryT (Apart a) u) t → FlatT (t ∪ u)
  flatT-∪ idle      u ft fu x = fu
  flatT-∪ (pin k r) u ft fu x = flatT-first k r u (M.sooner k u) ft fu x

  flatT-first : ∀ k r u b → FlatT (pin k r) → FlatT u → EveryT (λ a → EveryT (Apart a) u) (pin k r) → FlatT (M.first k r u b)
  flatᵀ (flatT-first k r u          true  ft fu x) =
    everyT-∪ (later r) u (proj₁ (flatᵀ ft)) (everyT-mono (λ h ap → proj₁ ap) u (proj₁ (everyᵀ x)))
    , flatT-∪ (later r) u (proj₂ (flatᵀ ft)) fu (proj₂ (everyᵀ x))
  flatᵀ (flatT-first k r idle       false ft fu x) = flatᵀ ft
  flatᵀ (flatT-first k r (pin k′ u) false ft fu x) =
    everyT-∪ (pin k r) (later u) (everyT-mono (λ a ap → proj₂ (proj₁ (everyᵀ ap))) (pin k r) x) (proj₁ (flatᵀ fu))
    , flatT-∪ (pin k r) (later u) ft (proj₂ (flatᵀ fu)) (everyT-mono (λ a ap → proj₂ (everyᵀ ap)) (pin k r) x)

-- A tail's first, from what every step of it satisfies.
atopT-every : ∀ h {P : Pos → Set} t → (∀ k → P k → k <ᵖ h ≡ false) → EveryT P t → AtopT h t
atopT-every h (pin k u) f pt = f k (proj₁ (everyᵀ pt))
atopT-every h idle      f pt = tt

-- `n` marks the step at `k`: just past it, or just past a mark of it, as
-- a connect re-shows a skip it did not take.
--
-- REFUTED: e295322c by a connect re-showing its lane's skip at `k ++ [ ix 0 , ix 0 ]`, `k` still pinned, while a mark was only `k ++ [ ix 0 ]`
data Marks (k : Pos) : Pos → Set where
  shown  : Marks k (k ++ [ ix 0 ])
  reshown : ∀ {n} → Marks k n → Marks k (n ++ [ ix 0 ])

marks-eq : ∀ {k n} → Marks k n → Σ Pos (λ zs → n ≡ k ++ ix 0 ∷ zs)
marks-eq         shown      = [] , refl
marks-eq {k = k} (reshown m) with marks-eq m
... | zs , refl = zs ++ [ ix 0 ] , ++-assoc k (ix 0 ∷ zs) [ ix 0 ]

-- Past `k`, and no proper extension of it: no extension of it at all.
past-apart : ∀ k h → k <ᵖ h ≡ true → ¬ Ext k h → ∀ ys → h ≡ k ++ ys → ⊥
past-apart k h kh nx []       e with () ← trans (sym (subst (λ z → k <ᵖ z ≡ true) (trans e (++-identityʳ k)) kh)) (<ᵖ-irrefl k)
past-apart k h kh nx (l ∷ ls) e = nx (subst (Ext k) (sym e) (ext l ls))

-- Past `k`'s subtree, and so is all that comes no earlier.
past-noext : ∀ k n h → k <ᵖ n ≡ true → ¬ Ext k n → h <ᵖ n ≡ false → ¬ Ext k h
past-noext k n .(k ++ l ∷ ls) kn nx hn (ext l ls) with () ← trans (sym hn) (M.<ᵖ-apart k n (l ∷ ls) kn (past-apart k n kn nx))

inside-prefix : ∀ r k h → M.inside r k ≡ true → Prefix k h → M.inside r h ≡ true
inside-prefix r k h i pr with prefix-rest k h pr
... | ys , refl = M.inside-++ r k ys i

-- Inside `r` is under it.
inside-under : ∀ r k → M.inside r k ≡ true → Prefix r k
inside-under []      k       i = tt
inside-under (a ∷ r) []      ()
inside-under (a ∷ r) (b ∷ k) i with M.inside-cons a r b k i
... | e , i′ = e , inside-under r k i′

ext-prefix : ∀ {k j n} → Ext k j → Prefix j n → Ext k n
ext-prefix {k} {n = n} (ext l ls) pr with prefix-rest (k ++ l ∷ ls) n pr
... | ys , refl = subst (Ext k) (sym (++-assoc k (l ∷ ls) ys)) (ext l (ls ++ ys))

marks-prefix : ∀ {k n} → Marks k n → Prefix k n
marks-prefix {k} shown             = prefix-++ k [ ix 0 ]
marks-prefix {k} (reshown {n} m)   = prefix-trans k n (n ++ [ ix 0 ]) (marks-prefix m) (prefix-++ n [ ix 0 ])

-- Between a step and its mark, its mark too.
marks-mid : ∀ {j n} k → Marks j n → j <ᵖ k ≡ true → n <ᵖ k ≡ false → Marks j k
marks-mid {j} k shown jk nk with <ᵖ-split (j ++ [ ix 0 ]) k (<ᵖ-step j k jk)
... | inj₁ lt with () ← trans (sym lt) nk
... | inj₂ refl = shown
marks-mid {j} k (reshown {n} m) jk nk with n <ᵖ k in e
... | false = marks-mid k m jk e
... | true with <ᵖ-split (n ++ [ ix 0 ]) k (<ᵖ-step n k e)
...   | inj₁ lt with () ← trans (sym lt) nk
...   | inj₂ refl = reshown m

-- Between a step and its mark, under the mark.
marks-under : ∀ {j n} k → Marks j n → j <ᵖ k ≡ true → n <ᵖ k ≡ false → Prefix k n
marks-under {j} k shown jk nk with <ᵖ-split (j ++ [ ix 0 ]) k (<ᵖ-step j k jk)
... | inj₁ lt with () ← trans (sym lt) nk
... | inj₂ refl = prefix-refl k
marks-under {j} k (reshown {n} m) jk nk with n <ᵖ k in e
... | false = prefix-trans k n (n ++ [ ix 0 ]) (marks-under k m jk e) (prefix-++ n [ ix 0 ])
... | true with <ᵖ-split (n ++ [ ix 0 ]) k (<ᵖ-step n k e)
...   | inj₁ lt with () ← trans (sym lt) nk
...   | inj₂ refl = prefix-refl k

-- A mark of a step keyed with none of `a` is not keyed under `a`.
marks-alien : ∀ {a k n} → Marks k n → Owned a n → Disjoint a k → ⊥
marks-alien {a} {k} shown (inj₁ pr) d with prefix-split a k (ix 0) pr
... | inj₁ q  = proj₁ d (inj₁ q)
... | inj₂ eq = proj₂ d (subst (Owned k) (sym eq) (inj₁ (prefix-++ k [ ix 0 ])))
marks-alien {a} {k} shown (inj₂ t) d = proj₁ d (inj₂ (tagged-lane a k 0 t))
marks-alien {a} {k} (reshown {n} m) (inj₁ pr) d with prefix-split a n (ix 0) pr
... | inj₁ q  = marks-alien m (inj₁ q) d
... | inj₂ eq = proj₂ d (subst (Owned k) (sym eq) (inj₁ (prefix-trans k n (n ++ [ ix 0 ]) (marks-prefix m) (prefix-++ n [ ix 0 ]))))
marks-alien {a} {k} (reshown {n} m) (inj₂ t) d = marks-alien m (inj₂ (tagged-lane a n 0 t)) d

-- Past a step and not under it: past its marks.
marks-past : ∀ {k n} h → Marks k n → k <ᵖ h ≡ true → ¬ Ext k h → n <ᵖ h ≡ true
marks-past {k} h m kh nx with marks-eq m
... | zs , refl = M.<ᵖ-apart k h (ix 0 ∷ zs) kh (past-apart k h kh nx)

-- Between a step and its mark: under the step.
marks-between : ∀ {k n} q → Marks k n → k <ᵖ q ≡ true → q <ᵖ n ≡ true → Prefix k q
marks-between {k} q m kq qn with marks-eq m
... | zs , refl with M.<ᵖ-between k q (ix 0 ∷ zs) kq qn
...   | ys , refl = prefix-++ k ys

-- What a skip at `n` lets run on: no step before it but one it marks.
Marked : Pos → Pos → Set
Marked n k = k <ᵖ n ≡ false ⊎ Marks k n

marked-cue : ∀ {j n} m → Marks j n → n <ᵖ m ≡ false → Marked m j
marked-cue {j} m mk nm with j <ᵖ m in e
... | true  = inj₂ (marks-mid m mk e nm)
... | false = inj₁ refl

-- What a cut leaves running trails the run's next event: no step before
-- a value nor keyed with it, nor before a skip but a step it marks; every step past an end, and none keyed where that end would
-- subscribe a lane, nor over it; nothing left behind silence.
TrailE : ∀ {A} → Events A → Pos → Set
TrailE (out n _ _) k = k <ᵖ n ≡ false × Disjoint n k
TrailE (skip n _)  k = Marked n k
TrailE (end n)     k = n <ᵖ k ≡ true × Disjoint (n ++ [ ix 1 ]) k × ¬ Ext n k
TrailE hush        k = ⊥

mutual
  Trailings : ∀ {A} → Events A → Set
  Trailings (out n _ r) = Trail (force r) (cut r) × EveryT (Disjoint n) (cut r)
  Trailings (skip _ r)  = Trail (force r) (cut r)
  Trailings (end _)     = ⊤
  Trailings hush        = ⊤

  -- A run `x`, leaving `c` running were it cut now, and every later
  -- state, each cut trailing its run.
  record Trail {A} (x : Events A) (c : Tail) : Set where
    coinductive
    field trail : SortedT c × EveryT (TrailE x) c × Trailings x
          trailᶠ : FlatT c

open Trail public

Trailing : ∀ {A} → Events∞ A → Set
Trailing r = Trail (force r) (cut r)

trailE-map : ∀ {A B} (f : A → B) (x : Events A) k → TrailE x k → TrailE (M′.mapᴱ f x) k
trailE-map f (out _ _ _) k t = t
trailE-map f (skip _ _)  k t = t
trailE-map f (end _)     k t = t
trailE-map f hush        k ()

mutual
  trailings-map : ∀ {A B} (f : A → B) (x : Events A) → Trailings x → Trailings (M′.mapᴱ f x)
  trailings-map f (out _ _ r) t = trail-map f (force r) (cut r) (proj₁ t) , proj₂ t
  trailings-map f (skip _ r)  t = trail-map f (force r) (cut r) t
  trailings-map f (end _)     t = tt
  trailings-map f hush        t = tt

  trail-map : ∀ {A B} (f : A → B) (x : Events A) c → Trail x c → Trail (M′.mapᴱ f x) c
  trail (trail-map f x c t) =
    proj₁ (trail t) , everyT-mono (trailE-map f x) c (proj₁ (proj₂ (trail t))) , trailings-map f x (proj₂ (proj₂ (trail t)))
  trailᶠ (trail-map f x c t) = trailᶠ t

trailE-scan : ∀ {A B} (f : B → A → B) z (x : Events A) k → TrailE x k → TrailE (M′.scanᴱ f z x) k
trailE-scan f z (out _ _ _) k t = t
trailE-scan f z (skip _ _)  k t = t
trailE-scan f z (end _)     k t = t
trailE-scan f z hush        k ()

mutual
  trailings-scan : ∀ {A B} (f : B → A → B) z (x : Events A) → Trailings x → Trailings (M′.scanᴱ f z x)
  trailings-scan f z (out _ a r) t = trail-scan f (f z a) (force r) (cut r) (proj₁ t) , proj₂ t
  trailings-scan f z (skip _ r)  t = trail-scan f z (force r) (cut r) t
  trailings-scan f z (end _)     t = tt
  trailings-scan f z hush        t = tt

  trail-scan : ∀ {A B} (f : B → A → B) z (x : Events A) c → Trail x c → Trail (M′.scanᴱ f z x) c
  trail (trail-scan f z x c t) =
    proj₁ (trail t) , everyT-mono (trailE-scan f z x) c (proj₁ (proj₂ (trail t))) , trailings-scan f z x (proj₂ (proj₂ (trail t)))
  trailᶠ (trail-scan f z x c t) = trailᶠ t

-- A run leaving nothing running, at its last state, trails it.
trail-idle : ∀ {A} (x : Events A) → Trailings x → Trail x idle
trail (trail-idle x t) = sortedT-idle , everyT-idle , t
trailᶠ (trail-idle x t) = flatT-idle

-- A TRAIL HOLDS OF WHAT AGREES WITH IT at every depth: its run and what
-- it leaves running alike.
atopT-≈ : ∀ h t u → Agreeᵀ 1 t u → AtopT h t → AtopT h u
atopT-≈ h (pin k _) (pin k _) (pin⁼ _) a = a
atopT-≈ h idle      idle      idle⁼    a = a

mutual
  sortedT-≈ : ∀ t u → (∀ k → Agreeᵀ k t u) → SortedT t → SortedT u
  sortedᵀ (sortedT-≈ t u ag st) = sortedTs-≈ t u ag (ag 1) st

  sortedTs-≈ : ∀ t u → (∀ k → Agreeᵀ k t u) → Agreeᵀ 1 t u → SortedT t → SortedTs u
  sortedTs-≈ (pin k l) (pin k r) ag (pin⁼ _) st =
    atopT-≈ k (later l) (later r) (restᵀ-agree (ag 2)) (proj₁ (sortedᵀ st))
    , sortedT-≈ (later l) (later r) (λ n → restᵀ-agree (ag (suc n))) (proj₂ (sortedᵀ st))
  sortedTs-≈ idle      idle      ag idle⁼    st = tt

mutual
  flatT-≈ : ∀ t u → (∀ k → Agreeᵀ k t u) → FlatT t → FlatT u
  flatᵀ (flatT-≈ t u ag ft) = flatTs-≈ t u ag (ag 1) ft

  flatTs-≈ : ∀ t u → (∀ k → Agreeᵀ k t u) → Agreeᵀ 1 t u → FlatT t → FlatTs u
  flatTs-≈ (pin k l) (pin k r) ag (pin⁼ _) ft =
    everyT-≈ (later l) (later r) (λ n → restᵀ-agree (ag (suc n))) (proj₁ (flatᵀ ft))
    , flatT-≈ (later l) (later r) (λ n → restᵀ-agree (ag (suc n))) (proj₂ (flatᵀ ft))
  flatTs-≈ idle      idle      ag idle⁼    ft = tt

trailE-≈ : ∀ {A} (x y : Events A) → Agree 1 x y → ∀ k → TrailE x k → TrailE y k
trailE-≈ (out _ _ _) (out _ _ _) (out⁼ _ _)  k t = t
trailE-≈ (skip _ _)  (skip _ _)  (skip⁼ _ _) k t = t
trailE-≈ (end _)     (end _)     end⁼        k t = t
trailE-≈ hush        hush        hush⁼       k t = t

mutual
  trail-≈ : ∀ {A} (x y : Events A) c d → (∀ k → Agree k x y) → (∀ k → Agreeᵀ k c d) → Trail x c → Trail y d
  trail (trail-≈ x y c d ag at tr) =
    sortedT-≈ c d at (proj₁ (trail tr))
    , everyT-≈ c d at (everyT-mono (trailE-≈ x y (ag 1)) c (proj₁ (proj₂ (trail tr))))
    , trailings-≈ x y ag (ag 1) (proj₂ (proj₂ (trail tr)))
  trailᶠ (trail-≈ x y c d ag at tr) = flatT-≈ c d at (trailᶠ tr)

  trailings-≈ : ∀ {A} (x y : Events A) → (∀ k → Agree k x y) → Agree 1 x y → Trailings x → Trailings y
  trailings-≈ (out _ _ l) (out _ _ r) ag (out⁼ _ _) (t , e) =
    trail-≈ (force l) (force r) (cut l) (cut r) (λ k → rest-agree (ag (suc k))) (λ k → M′.agree-tail (ag (suc k))) t
    , everyT-≈ (cut l) (cut r) (λ k → M′.agree-tail (ag (suc k))) e
  trailings-≈ (skip _ l)  (skip _ r)  ag (skip⁼ _ _) t =
    trail-≈ (force l) (force r) (cut l) (cut r) (λ k → rest-agree (ag (suc k))) (λ k → M′.agree-tail (ag (suc k))) t
  trailings-≈ (end _)     (end _)     ag end⁼        t = tt
  trailings-≈ hush        hush        ag hush⁼       t = tt

-- A cold leaf's run leaves nothing running at any state.
mutual
  trail-frames : ∀ {A t} τ e (m : From A t) → Trail (M′.frames τ e m) idle
  trail-frames τ e M.done        = trail-idle _ tt
  trail-frames τ e M.quiet       = trail-idle _ tt
  trail-frames τ e (M.at t _ b)  = trail-burst τ (ix (τ + t) ∷ sub e ∷ []) 0 b

  trail-burst : ∀ {A t} τ r i (b : M.Frame A t) → Trail (M′.burst τ r i b) idle
  trail (trail-burst τ r i (M.emit a k)) = sortedT-idle , everyT-idle , trail-burst τ r (suc i) (M.Frame∞.force k) , everyT-idle
  trail (trail-burst τ r i (M.stall k))  = sortedT-idle , everyT-idle , trail-burst τ r (suc i) (M.Frame∞.force k)
  trail (trail-burst τ r i (M.close k))  = sortedT-idle , everyT-idle , trail-frames τ (r ++ [ last ]) (M.From∞.force k)
  trailᶠ (trail-burst τ r i b) = flatT-idle

trailing-start : ∀ {Γ A} p (m : From A 0) (ρ : NEnv Γ) → Trailing (U.stateᴺ (U.startᶜ p m) ρ)
trailing-start p (M.at zero _ b)    ρ = trail-burst (tick p) p 0 b
trailing-start p (M.at (suc t) le b) ρ = trail-frames (tick p) (p ++ [ last ]) (M.at (suc t) le b)
trailing-start p M.done             ρ = trail-idle _ tt
trailing-start p M.quiet            ρ = trail-idle _ tt

-- A list's run leaves nothing running.
trail-of : ∀ {A} p i (xs : List A) → Trail (M′.ofᴱ p i xs) idle
trail-of p i []       = trail-idle _ tt
trail-of p i (x ∷ xs) = trail-idle _ (trail-of p (suc i) xs , everyT-idle)

-- A joiner's run leaves nothing running, whatever its source left.
mutual
  trail-rejoin : ∀ {A} p (e : Events A) → Trail (M′.rejoin p e) idle
  trail-rejoin p (out q a k) = trail-shown p q (just a) k (p <ᵖ q)
  trail-rejoin p (skip q k)  = trail-shown p q nothing k (p <ᵖ q)
  trail-rejoin p (end c) with p <ᵖ c
  ... | true  = trail-idle _ tt
  ... | false = trail-idle _ tt
  trail-rejoin p hush        = trail-idle _ tt

  trail-shown : ∀ {A} p q (a : Maybe A) (k : Events∞ A) b → Trail (M′.shown p q a k b) idle
  trail (trail-shown p q (just a) k true)  = sortedT-idle , everyT-idle , trail-rejoin p (force k) , everyT-idle
  trail (trail-shown p q nothing  k true)  = sortedT-idle , everyT-idle , trail-rejoin p (force k)
  trail (trail-shown p q (just a) k false) = sortedT-idle , everyT-idle , trail-rejoin p (force k)
  trail (trail-shown p q nothing  k false) = sortedT-idle , everyT-idle , trail-rejoin p (force k)
  trailᶠ (trail-shown p q a k b) = flatT-idle

-- Keyed apart from where a lane admitted at `x` would key, and `y`'s
-- lane too.
Sp : Pos → Pos → Set
Sp x y = Disjoint (y ++ [ ix 1 ]) (x ++ [ ix 1 ]) × ¬ Owned y (x ++ [ ix 1 ])

-- After a value at `x`, nothing later, shown or left running, lies
-- where a lane admitted then would key, nor keys where `x`'s does.
mutual
  Spreads : ∀ {A} → Events A → Set
  Spreads (out x _ r) = Every∞ (Sp x) r × Spread (force r)
  Spreads (skip _ r)  = Spread (force r)
  Spreads (end _)     = ⊤
  Spreads hush        = ⊤

  record Spread {A} (e : Events A) : Set where
    coinductive
    field spread : Spreads e

open Spread public

spread-map : ∀ {A B} (f : A → B) (e : Events A) → Spread e → Spread (M′.mapᴱ f e)
spread (spread-map f (out h a r) s) =
  (every-map f (force r) (proj₁ (proj₁ (spread s))) , proj₂ (proj₁ (spread s))) , spread-map f (force r) (proj₂ (spread s))
spread (spread-map f (skip h r)  s) = spread-map f (force r) (spread s)
spread (spread-map f (end h)     s) = tt
spread (spread-map f hush        s) = tt

spread-scan : ∀ {A B} (f : B → A → B) z (e : Events A) → Spread e → Spread (M′.scanᴱ f z e)
spread (spread-scan f z (out h a r) s) =
  (every-scan f (f z a) (force r) (proj₁ (proj₁ (spread s))) , proj₂ (proj₁ (spread s))) , spread-scan f (f z a) (force r) (proj₂ (spread s))
spread (spread-scan f z (skip h r)  s) = spread-scan f z (force r) (spread s)
spread (spread-scan f z (end h)     s) = tt
spread (spread-scan f z hush        s) = tt

rest-spread : ∀ {A} (x : Events A) → Spread x → Spread (rest x)
rest-spread (out _ _ _) s = proj₂ (spread s)
rest-spread (skip _ _)  s = spread s
rest-spread (end _)     s = record { spread = tt }
rest-spread hush        s = s

-- What follows a value at `x`, in whatever agrees with a run there.
spread-rest : ∀ {A k} x a (r : Events∞ A) (e : Events A) → Agree (suc k) e (out x a r) → Spread e
            → Every∞ (Sp x) (record { force = rest e ; cut = M′.tailOf e })
spread-rest x a r (out _ _ _) (out⁼ _ _) s = proj₁ (spread s)

-- A LIMIT SPREADS WHERE ITS APPROXIMANTS DO.
mutual
  spread-lim : ∀ {A} (xs : ℕ → Events A) (y : Events A) → (∀ n → Spread (xs n)) → (∀ n → Agree n (xs n) y) → Spread y
  spread (spread-lim xs y ps ag) = spreads-lim xs y ps ag (xs 1) (ag 1)

  spreads-lim : ∀ {A} (xs : ℕ → Events A) (y : Events A) → (∀ n → Spread (xs n)) → (∀ n → Agree n (xs n) y)
              → (x : Events A) → Agree 1 x y → Spreads y
  spreads-lim xs (out h a r) ps ag (out h _ _) (out⁼ _ _) =
    ( every-lim (λ n → rest (xs (suc n))) (force r) (λ n → proj₁ (spread-rest h a r (xs (suc n)) (ag (suc n)) (ps (suc n))))
        (λ n → rest-agree (ag (suc n)))
    , everyT-lim (λ n → M′.tailOf (xs (suc n))) (cut r) (λ n → proj₂ (spread-rest h a r (xs (suc n)) (ag (suc n)) (ps (suc n))))
        (λ n → M′.agree-tail (ag (suc n))) )
    , spread-lim (λ n → rest (xs (suc n))) (force r) (λ n → rest-spread (xs (suc n)) (ps (suc n))) (λ n → rest-agree (ag (suc n)))
  spreads-lim xs (skip h r)  ps ag (skip h _)  (skip⁼ _ _) =
    spread-lim (λ n → rest (xs (suc n))) (force r) (λ n → rest-spread (xs (suc n)) (ps (suc n))) (λ n → rest-agree (ag (suc n)))
  spreads-lim xs (end h)     ps ag (end h)     end⁼        = tt
  spreads-lim xs hush        ps ag hush        hush⁼       = tt

spread-≈ : ∀ {A} (x y : Events A) → (∀ k → Agree k x y) → Spread x → Spread y
spread-≈ x y a s = spread-lim (λ _ → x) y (λ _ → s) a

-- A DEFER SPREADS, its program's being.
spread-defer : ∀ {Γ A} (l : Later Timeline Γ A) p (ρ : NEnv Γ) → Headed p → Alienᴱ p ρ
             → Spread (U.meaning (U.subscribe (Later.force l) (p ++ [ ix 1 ])) ρ) → Spread (U.meaning (U.deferᶜ l p []) ρ)
spread (spread-defer l p ρ hp cl sp) = spread-≈ S X alike sp
  where open Deferred l p ρ hp cl

-- One fact for every index, step by step.
mutual
  everyT-∀ : ∀ {I : Set} {P : I → Pos → Set} (t : Tail) → (∀ i → EveryT (P i) t) → EveryT (λ h → ∀ i → P i h) t
  everyᵀ (everyT-∀ (pin k u) f) = (λ i → proj₁ (everyᵀ (f i))) , everyT-∀ (later u) (λ i → proj₂ (everyᵀ (f i)))
  everyᵀ (everyT-∀ idle      f) = tt

mutual
  every-∀ : ∀ {A} {I : Set} {P : I → Pos → Set} (e : Events A) → (∀ i → Every (P i) e) → Every (λ h → ∀ i → P i h) e
  every (every-∀ (out h _ r) f) = (λ i → proj₁ (every (f i))) , every-∀ (force r) (λ i → proj₁ (proj₂ (every (f i))))
                                  , everyT-∀ (cut r) (λ i → proj₂ (proj₂ (every (f i))))
  every (every-∀ (skip h r)  f) = (λ i → proj₁ (every (f i))) , every-∀ (force r) (λ i → proj₁ (proj₂ (every (f i))))
                                  , everyT-∀ (cut r) (λ i → proj₂ (proj₂ (every (f i))))
  every (every-∀ (end h)     f) = λ i → every (f i)
  every (every-∀ hush        f) = tt

-- Strictly under a position a tick heads is no timer's bare tick.
tick-beneath : ∀ p R → Headed p → Beneath p R → ∀ m → R ≢ ix (suc m) ∷ []
tick-beneath (ix _ ∷ [])    _ _  (inj₁ (_ , ())) m refl
tick-beneath (ix _ ∷ _ ∷ _) _ _  (inj₁ (_ , ())) m refl
tick-beneath p              _ _  (inj₂ ())       m refl
tick-beneath []             _ () (inj₁ _)        m refl
tick-beneath (sub _ ∷ _)    _ () (inj₁ _)        m refl
tick-beneath (last ∷ _)     _ () (inj₁ _)        m refl

-- Reading off a run's first position.
atop-nothing : ∀ {A} k (e : Events A) → M′.head e ≡ nothing → Atop k e
atop-nothing k (out _ _ _) ()
atop-nothing k (skip _ _)  ()
atop-nothing k (end _)     ()
atop-nothing k hush        h = tt

atop-just : ∀ {A} (e : Events A) {k k′} → M′.head e ≡ just k → k <ᵖ k′ ≡ false → Atop k′ e
atop-just (out _ _ _) refl a = a
atop-just (skip _ _)  refl a = a
atop-just (end _)     refl a = a
atop-just hush        ()   a

beyond-atop : ∀ {A} k (e : Events A) → Beyond k e → Atop k e
beyond-atop k (out h _ _) b = <ᵖ-asym k h b
beyond-atop k (skip h _)  b = <ᵖ-asym k h b
beyond-atop k (end h)     b = <ᵖ-asym k h b
beyond-atop k hush        b = tt

beyond-step : ∀ {A} k (e : Events A) → Beyond k e → Atop (k ++ [ ix 0 ]) e
beyond-step k (out h _ _) b = <ᵖ-step k h b
beyond-step k (skip h _)  b = <ᵖ-step k h b
beyond-step k (end h)     b = <ᵖ-step k h b
beyond-step k hush        b = tt

beyond-still : ∀ {A} k′ k (e : Events A) → k′ <ᵖ k ≡ true → Atop k e → Beyond k′ e
beyond-still k′ k (out h _ _) kk a = still k′ k h kk a
beyond-still k′ k (skip h _)  kk a = still k′ k h kk a
beyond-still k′ k (end h)     kk a = still k′ k h kk a
beyond-still k′ k hush        kk a = tt

beyond-nothing : ∀ {A} k (e : Events A) → M′.head e ≡ nothing → Beyond k e
beyond-nothing k (out _ _ _) ()
beyond-nothing k (skip _ _)  ()
beyond-nothing k (end _)     ()
beyond-nothing k hush        h = tt

beyond-just : ∀ {A} k′ (e : Events A) {k} → M′.head e ≡ just k → k′ <ᵖ k ≡ true → Beyond k′ e
beyond-just k′ (out _ _ _) refl b = b
beyond-just k′ (skip _ _)  refl b = b
beyond-just k′ (end _)     refl b = b
beyond-just k′ hush        ()   b

past-beyond : ∀ {A} k (e : Events A) → Past k e → Beyond k e
past-beyond k (out _ _ _) c = proj₁ c
past-beyond k (skip _ _)  c = proj₁ c
past-beyond k (end _)     c = proj₁ c
past-beyond k hush        c = tt

clear-beyond : ∀ {A} k (e : Events A) → M′.clear k (M′.head e) ≡ true → Beyond k e
clear-beyond k (out _ _ _) c = c
clear-beyond k (skip _ _)  c = c
clear-beyond k (end _)     c = c
clear-beyond k hush        c = tt

-- Past `q` and not `q` itself: no earlier than just past it.
step-apart : ∀ q k → k <ᵖ q ≡ false → q ≢ k → k <ᵖ (q ++ [ ix 0 ]) ≡ false
step-apart q k a ne with <ᵖ-split q k a
... | inj₁ qk   = <ᵖ-step q k qk
... | inj₂ refl = ⊥-elim (ne refl)

-- No pool step left ahead of every part is before what the parts show
-- first.
clear-atop : ∀ {B} h k (x : Events B) → Atop h x → M′.clear k (M′.head x) ≡ false → k <ᵖ h ≡ false
clear-atop h k (out k′ _ _) a c = ≮-trans h k′ k a c
clear-atop h k (skip k′ _)  a c = ≮-trans h k′ k a c
clear-atop h k (end k′)     a c = ≮-trans h k′ k a c
clear-atop h k hush         a ()

clears-atop : ∀ {B} h k (ls : List (Events∞ B)) → All (λ l → Atop h (force l)) ls → M′.clears k ls ≡ false → k <ᵖ h ≡ false
clears-atop h k []       _          ()
clears-atop h k (l ∷ ls) (a ∷ᴬ as) c with M′.clear k (M′.head (force l)) in e
... | true  = clears-atop h k ls as c
... | false = clear-atop h k (force l) a e

-- What the pool holds back, with the parts it is held behind.
Behind : ∀ {B} → Maybe (Events∞ (MonotonicList B)) → List (Events∞ B) → Tail → Set
Behind o ls idle      = ⊤
Behind o ls (pin k u) = M′.ahead-of k o ls ≡ false

behind-atop : ∀ {B} h (o : Maybe (Events∞ (MonotonicList B))) ls t → Behind o ls t → All (λ l → Atop h (force l)) ls → Atopᴹ h o
            → AtopT h t
behind-atop h o        ls idle      _ _  _  = tt
behind-atop h nothing  ls (pin k u) b al ao = clears-atop h k ls al b
behind-atop h (just e) ls (pin k u) b al ao with M′.clear k (M′.head (force e)) in c
... | true  = clears-atop h k ls al b
... | false = clear-atop h k (force e) ao c

-- A pool ahead of every part: each part's first is past its step.
ahead-atop : ∀ {B} k (o : Maybe (Events∞ (MonotonicList B))) ls → M′.ahead-of k o ls ≡ true
           → All (λ l → Atop k (force l)) ls × Atopᴹ k o
ahead-atop k o ls e = lanes ls (clears-of o e) , outer o e
  where
    one : ∀ {B} (x : Events B) → M′.clear k (M′.head x) ≡ true → Atop k x
    one (out h _ _) c = <ᵖ-asym k h c
    one (skip h _)  c = <ᵖ-asym k h c
    one (end h)     c = <ᵖ-asym k h c
    one hush        c = tt
    clears-of : ∀ o → M′.ahead-of k o ls ≡ true → M′.clears k ls ≡ true
    clears-of nothing  e = e
    clears-of (just x) e with M′.clear k (M′.head (force x))
    ... | true = e
    lanes : ∀ ls → M′.clears k ls ≡ true → All (λ l → Atop k (force l)) ls
    lanes []       c = []ᴬ
    lanes (l ∷ ls) c with M′.clear k (M′.head (force l)) in d
    ... | true  = one (force l) d ∷ᴬ lanes ls c
    outer : ∀ o → M′.ahead-of k o ls ≡ true → Atopᴹ k o
    outer nothing  e = tt
    outer (just x) e with M′.clear k (M′.head (force x)) in d
    ... | true = one (force x) d

-- The lane `earliest` picks, where it sat, and no lane's first before it.
Picks : ∀ {B} → List (Events∞ B) → Earliest B → Set
Picks ls none              = All (λ l → M′.head (force l) ≡ nothing) ls
Picks ls (found k bs l as) = ls ≡ bs ++ l ∷ as × M′.head (force l) ≡ just k × All (λ x → Atop k (force x)) bs × All (λ x → Atop k (force x)) as

earliest-picks : ∀ {B} (ls : List (Events∞ B)) → Picks ls (M′.earliest ls)
earliest-picks []       = []ᴬ
earliest-picks (l ∷ ls) with M′.head (force l) in hl | M′.earliest ls | earliest-picks ls
... | nothing | none             | hs                  = hl ∷ᴬ hs
... | nothing | found k bs c as  | (eq , hc , ab , aa) = cong (l ∷_) eq , hc , atop-nothing k (force l) hl ∷ᴬ ab , aa
... | just k  | none             | hs                  = refl , hl , []ᴬ , mapᴬ (λ {x} → atop-nothing k (force x)) hs
... | just k  | found k′ bs c as | (eq , hc , ab , aa) with k <ᵖ k′ in kk
...   | true  = refl , hl , []ᴬ
              , subst (All (λ x → Atop k (force x))) (sym eq)
                  (All++⁺ (mapᴬ (λ {x} → atop-weaken k′ k (force x) (<ᵖ-asym k k′ kk)) ab)
                          (atop-just (force c) hc (<ᵖ-asym k k′ kk) ∷ᴬ mapᴬ (λ {x} → atop-weaken k′ k (force x) (<ᵖ-asym k k′ kk)) aa))
...   | false = cong (l ∷_) eq , hc , atop-just (force l) hl kk ∷ᴬ ab , aa

all-pick : ∀ {A : Set} {P : A → Set} xs {y} ys → All P (xs ++ y ∷ ys) → P y × All P (xs ++ ys)
all-pick []       ys (py ∷ᴬ pys) = py , pys
all-pick (x ∷ xs) ys (px ∷ᴬ pxs) = proj₁ (all-pick xs ys pxs) , px ∷ᴬ proj₂ (all-pick xs ys pxs)

disjoint-swap : ∀ a h → Disjoint a h → Disjoint h a
disjoint-swap a h (na , nb) = nb , na

-- Pairwise apart.
Parted : List Pos → Set
Parted []       = ⊤
Parted (r ∷ rs) = All (Disjoint r) rs × Parted rs

parted-pick : ∀ rbs r ras → Parted (rbs ++ r ∷ ras) → All (Disjoint r) (rbs ++ ras) × Parted (rbs ++ ras)
parted-pick []        r ras pt        = pt
parted-pick (b ∷ rbs) r ras (db , pt) =
  disjoint-swap b r (proj₁ (all-pick rbs ras db)) ∷ᴬ proj₁ (parted-pick rbs r ras pt)
  , proj₂ (all-pick rbs ras db) , proj₂ (parted-pick rbs r ras pt)

all-zip : ∀ {A : Set} {P Q : A → Set} {xs} → All P xs → All Q xs → All (λ x → P x × Q x) xs
all-zip []ᴬ       []ᴬ       = []ᴬ
all-zip (p ∷ᴬ ps) (q ∷ᴬ qs) = (p , q) ∷ᴬ all-zip ps qs

t≢f : true ≡ false → ⊥
t≢f ()

behind-at : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) {ls ls′ : List (Events∞ B)} t → ls ≡ ls′ → Behind o ls t → Behind o ls′ t
behind-at o t refl b = b

-- Past `q` and not `q`: nothing a tail holds is before just past it.
pool-step : ∀ q t → AtopT q t → EveryT (λ k → q ≢ k) t → AtopT (q ++ [ ix 0 ]) t
pool-step q idle      a e = tt
pool-step q (pin k u) a e = step-apart q k a (proj₁ (everyᵀ e))

-- Each lane's tail, together.
cuts-every : ∀ {B} {P : Pos → Set} (ls : List (Events∞ B)) → All (λ l → EveryT P (cut l)) ls → EveryT P (M′.cuts ls)
cuts-every []       []ᴬ       = everyT-idle
cuts-every (l ∷ ls) (a ∷ᴬ as) = everyT-∪ (cut l) (M′.cuts ls) a (cuts-every ls as)

-- One fact per root, at every step, as every step's fact for each root.
everyT-all : ∀ {Q : Pos → Pos → Set} (rs : List Pos) (t : Tail) → All (λ r → EveryT (Q r) t) rs → EveryT (λ k → All (λ r → Q r k) rs) t
everyᵀ (everyT-all rs (pin k u) a) = mapᴬ (λ e → proj₁ (everyᵀ e)) a , everyT-all rs (later u) (mapᴬ (λ e → proj₂ (everyᵀ e)) a)
everyᵀ (everyT-all rs idle      a) = tt

self-atop : ∀ {A} (x : Events A) {k} → M′.head x ≡ just k → Atop k x
self-atop x {k} h = atop-just x h (<ᵖ-irrefl k)

-- A run's first, read off a tail.
Atopᴴ : ∀ {A} → Events A → Tail → Set
Atopᴴ (out h _ _) t = AtopT h t
Atopᴴ (skip h _)  t = AtopT h t
Atopᴴ (end h)     t = AtopT h t
Atopᴴ hush        t = ⊤

atopᴴ : ∀ {A} (x : Events A) {k} t → M′.head x ≡ just k → AtopT k t → Atopᴴ x t
atopᴴ (out _ _ _) t refl a = a
atopᴴ (skip _ _)  t refl a = a
atopᴴ (end _)     t refl a = a
atopᴴ hush        t ()   a

atopᴴ-nothing : ∀ {A} (x : Events A) t → M′.head x ≡ nothing → Atopᴴ x t
atopᴴ-nothing (out _ _ _) t ()
atopᴴ-nothing (skip _ _)  t ()
atopᴴ-nothing (end _)     t ()
atopᴴ-nothing hush        t h = tt

-- Every lane's first strictly past the outer's.
Lead : ∀ {A B} → Events A → List (Events∞ B) → Set
Lead (out h _ _) ls = All (λ l → Beyond h (force l)) ls
Lead (skip h _)  ls = All (λ l → Beyond h (force l)) ls
Lead (end h)     ls = All (λ l → Beyond h (force l)) ls
Lead hush        ls = ⊤

lead-of : ∀ {A B} (x : Events A) (ls : List (Events∞ B)) {k} → M′.head x ≡ just k → All (λ l → Beyond k (force l)) ls → Lead x ls
lead-of (out _ _ _) ls refl b = b
lead-of (skip _ _)  ls refl b = b
lead-of (end _)     ls refl b = b
lead-of hush        ls ()   b

lead-hush : ∀ {A B} (x : Events A) (ls : List (Events∞ B)) → All (λ l → M′.head (force l) ≡ nothing) ls → Lead x ls
lead-hush (out h _ _) ls hs = mapᴬ (λ {l} → beyond-nothing h (force l)) hs
lead-hush (skip h _)  ls hs = mapᴬ (λ {l} → beyond-nothing h (force l)) hs
lead-hush (end h)     ls hs = mapᴬ (λ {l} → beyond-nothing h (force l)) hs
lead-hush hush        ls hs = tt
