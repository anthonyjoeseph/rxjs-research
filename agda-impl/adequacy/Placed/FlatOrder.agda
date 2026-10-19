{-# OPTIONS --guardedness #-}

module adequacy.Placed.FlatOrder where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_; [_]; length)
open import Data.Nat using (_<ᵇ_)
open import Data.List.Relation.Unary.All using (All; lookup) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_; map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to All++⁺; ++⁻ˡ to All++⁻ˡ; ++⁻ʳ to All++⁻ʳ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Nullary using (¬_)

open import denotation.MonotonicList.Events using (Events; Events∞; Pos; out; skip; end; hush; ix; _<ᵖ_; <ᵖ-asym; <ᵖ-split; <ᵖ-trans; <ᵖ-part;
  <ᵖ-step; Tail; Tail∞; pin; idle; _∪_)
open import denotation.MonotonicList using (MonotonicList; none; found)
import denotation.MonotonicList as M′
import denotation.Unfold as U
open import denotation.Denote using (flatOp) renaming (⟦_⟧ to ⟦_⟧ᴰ)
open import adequacy.Placed.Order using (Atop; Beneath; Clear; Every; EveryT; Every∞; Ext; Headed; Ordered; Owned; Steady; every; every-mono; everyT-idle; everyT-mono; everyT-∪; everyᵀ; headed-snoc; ordered; owned-ext; prefix-++; steady; still)
open import adequacy.Placed.Keys using (Values; beneath-owned; ix-mark; owned-snoc; owned-trans; prefix-plus; prefix-refl; sibling; values)
open import adequacy.Placed.Rising using (AtopT; Atopᴹ; Beyond; Disjoint; apart-mark; atop-clear; atop-go; atop-weaken; every-zip; everyT-zip; ext-snoc)
open import adequacy.Placed.Trail using (Apart; Atopᴴ; Behind; FlatT; Lead; Parted; SortedT; Spread; Trail; TrailE; Trailing; ahead-atop; all-pick; all-zip; apart-of; atop-just; atop-nothing; atopT-every; atopT-∪; atopᴴ; atopᴴ-nothing; behind-at; behind-atop; beyond-atop; beyond-just; beyond-step; beyond-still; clear-beyond; cuts-every; disjoint-swap; earliest-picks; everyT-all; flatT-idle; flatT-∪; flatᵀ; lead-hush; lead-of; marks-between; parted-pick; past-beyond; pool-step; self-atop; sortedT-idle; sortedT-∪; sortedᵀ; spread; trail; trailᶠ)
open import adequacy.Placed.Calm using (Aloof; At; Clean; LaneAt; Obl; OuterAt; OuterAtᴹ; PoolAt; at-apart; at-beyond; away-lane; away-outer; clean-of; laneAt-map; outerAt-map; outerᴹ-map; past-at; past-step; pool-apart; poolAt-map; poolAt-∪; step-past)

open Events∞
open Tail∞

-- A FLATMAP'S MERGE IN ORDER, under `p`.  Each lane carries a ghost
-- root, where it subscribed; roots are pairwise apart, each lane keyed
-- under its own and by nothing apart from it a lane may subscribe at,
-- and the outer's events apart from each root a step past them.  What
-- ended parts left running is keyed under no root, nor where a later
-- outer value subscribes its lane, nor at that value: so no lane, nor
-- the outer, nor the pool ties with a step the merge shows just past a
-- lane's end or an outer value.
module FlatOrder (p : Pos) where

  -- Where a lane may subscribe: strictly under `p`, a tick heading it.
  Ok : Pos → Set
  Ok j = Beneath p j × Headed j

  -- Keyed under `j`, a tick heading it, keyed by nothing apart from `j`
  -- a lane may subscribe at.
  Under : Pos → Pos → Set
  Under j h = Owned j h × Headed h × (∀ R → Ok R → Disjoint R j → ¬ Owned R h)

  -- A lane subscribed at `j`.
  Fit : ∀ {B} → Pos → Events∞ B → Set
  Fit j l = Ordered (force l) × Atop j (force l) × Steady (force l) × Trailing l × Every∞ (Under j) l × Spread (force l)

  Gen : ∀ {B} → MonotonicList B → Set
  Gen m = ∀ j → Ok j → Fit j (M′.enter m j)

  -- A lane in flight under its root: its run, and what it leaves running.
  record Lane {B} (r : Pos) (x : Events B) (c : Tail) : Set where
    constructor lane
    field
      ord : Ordered x
      std : Steady x
      trl : Trail x c
      kx  : Every (Under r) x
      kc  : EveryT (Under r) c
      ok  : Ok r
      spr : Spread x

  Static : ∀ {B} → Pos → Events∞ B → Set
  Static r l = Lane r (force l) (cut l)

  fresh : ∀ {B} j (l : Events∞ B) → Fit j l → Ok j → Static j l
  fresh j l (o , _ , sd , t , (kx , kc) , sp) okj = lane o sd t kx kc okj sp

  lane-out : ∀ {B r k b c} {w : Events∞ B} → Lane r (out k b w) c → Static r w
  lane-out st = lane (proj₂ (ordered (Lane.ord st))) (proj₂ (steady (Lane.std st))) (proj₁ (proj₂ (proj₂ (trail (Lane.trl st)))))
                     (proj₁ (proj₂ (every (Lane.kx st)))) (proj₂ (proj₂ (every (Lane.kx st)))) (Lane.ok st) (proj₂ (spread (Lane.spr st)))

  lane-skip : ∀ {B r k c} {w : Events∞ B} → Lane r (skip k w) c → Static r w
  lane-skip st = lane (proj₂ (ordered (Lane.ord st))) (proj₂ (steady (Lane.std st))) (proj₂ (proj₂ (trail (Lane.trl st))))
                      (proj₁ (proj₂ (every (Lane.kx st)))) (proj₂ (proj₂ (every (Lane.kx st)))) (Lane.ok st) (spread (Lane.spr st))

  data Roots {B} : List (Events∞ B) → List Pos → Set where
    []ᴿ  : Roots [] []
    _∷ᴿ_ : ∀ {r l ls rs} → Static r l → Roots ls rs → Roots (l ∷ ls) (r ∷ rs)

  roots-++ : ∀ {B} {xs ys : List (Events∞ B)} {rs ss} → Roots xs rs → Roots ys ss → Roots (xs ++ ys) (rs ++ ss)
  roots-++ []ᴿ       S = S
  roots-++ (st ∷ᴿ R) S = st ∷ᴿ roots-++ R S

  roots-ok : ∀ {B} {ls : List (Events∞ B)} {rs} → Roots ls rs → All Ok rs
  roots-ok []ᴿ       = []ᴬ
  roots-ok (st ∷ᴿ R) = Lane.ok st ∷ᴬ roots-ok R

  data Split {B} (bs : List (Events∞ B)) (l : Events∞ B) (as : List (Events∞ B)) : List Pos → Set where
    split : ∀ {rbs r ras} → Roots bs rbs → Static r l → Roots as ras → Split bs l as (rbs ++ r ∷ ras)

  roots-split : ∀ {B} (bs : List (Events∞ B)) {l as rs} → Roots (bs ++ l ∷ as) rs → Split bs l as rs
  roots-split []       (st ∷ᴿ R) = split []ᴿ st R
  roots-split (b ∷ bs) (sb ∷ᴿ R) with roots-split bs R
  ... | split rb st ra = split (sb ∷ᴿ rb) st ra

  roots-at : ∀ {B} bs (l : Events∞ B) as {ls rs} → ls ≡ bs ++ l ∷ as → Roots ls rs → Split bs l as rs
  roots-at bs l as refl R = roots-split bs R

  -- An outer position: under `p`, a tick heading it.
  K : Pos → Set
  K y = Owned p y × Headed y

  -- The outer: in order and steady, its cuts trailing it, spread, under
  -- `p`, its values lanes.
  record Outer {B} (x : Events (MonotonicList B)) (c : Tail) : Set where
    constructor outer
    field
      ord : Ordered x
      std : Steady x
      trl : Trail x c
      spr : Spread x
      kx  : Every K x
      kc  : EveryT K c
      spn : Values Gen x

  Heldᴹ : ∀ {B} → Maybe (Events∞ (MonotonicList B)) → Set
  Heldᴹ nothing  = ⊤
  Heldᴹ (just e) = Outer (force e) (cut e)

  outer-out : ∀ {B q m c} {w : Events∞ (MonotonicList B)} → Outer (out q m w) c → Outer (force w) (cut w)
  outer-out h = outer (proj₂ (ordered (Outer.ord h))) (proj₂ (steady (Outer.std h))) (proj₁ (proj₂ (proj₂ (trail (Outer.trl h)))))
                      (proj₂ (spread (Outer.spr h))) (proj₁ (proj₂ (every (Outer.kx h)))) (proj₂ (proj₂ (every (Outer.kx h))))
                      (proj₂ (values (Outer.spn h)))

  outer-skip : ∀ {B q c} {w : Events∞ (MonotonicList B)} → Outer (skip q w) c → Outer (force w) (cut w)
  outer-skip h = outer (proj₂ (ordered (Outer.ord h))) (proj₂ (steady (Outer.std h))) (proj₂ (proj₂ (trail (Outer.trl h))))
                       (spread (Outer.spr h)) (proj₁ (proj₂ (every (Outer.kx h)))) (proj₂ (proj₂ (every (Outer.kx h))))
                       (values (Outer.spn h))

  -- Where a value at `y` subscribes its lane, apart from root `r`; and
  -- `y` itself over no root.
  D : Pos → Pos → Set
  D r y = Disjoint (y ++ [ ix 1 ]) r × ¬ Owned y r

  Aside : ∀ {B} → Maybe (Events∞ (MonotonicList B)) → Pos → Set
  Aside nothing  r = ⊤
  Aside (just e) r = Every∞ (D r) e

  aside-none : ∀ {B} rs → All (Aside {B} nothing) rs
  aside-none []       = []ᴬ
  aside-none {B} (r ∷ rs) = tt ∷ᴬ aside-none {B} rs

  -- No outer value at `k`, over it or under it, nor subscribing its
  -- lane over it.
  Free : ∀ {A} → Events A → Pos → Set
  Free x k = Every (λ y → ¬ Owned (y ++ [ ix 1 ]) k × Disjoint y k) x

  -- And none an outer at `x`, leaving `c` running, would show.
  FreeC : ∀ {A} → Events A → Tail → Pos → Set
  FreeC x c k = Free x k × EveryT (λ y → ¬ Owned (y ++ [ ix 1 ]) k × Disjoint y k) c

  FreeO : ∀ {B} → Maybe (Events∞ (MonotonicList B)) → Pos → Set
  FreeO nothing  k = ⊤
  FreeO (just e) k = FreeC (force e) (cut e) k

  -- Outer positions over no root, no one inside one before it.
  Wide : List Pos → Tail → Set
  Wide rs t = EveryT (λ k → All (λ r → ¬ Owned k r) rs × K k) t × FlatT t

  -- What ended parts left running: in order, under no root, `F` of it.
  PoolF : (Pos → Set) → List Pos → Tail → Set
  PoolF F rs t = SortedT t × EveryT (λ k → All (λ r → ¬ Owned r k) rs × F k) t × Wide rs t

  -- And free of the outer.
  Pool : ∀ {B} → Maybe (Events∞ (MonotonicList B)) → List Pos → Tail → Set
  Pool o rs t = PoolF (FreeO o) rs t

  own-lane : ∀ r y → Owned r y → Owned r (y ++ [ ix 1 ])
  own-lane r y o = owned-trans r y (y ++ [ ix 1 ]) o (inj₁ (prefix-++ y [ ix 1 ]))

  aside-not : ∀ r y → D r y → ¬ Owned r y
  aside-not r y d o = proj₂ (proj₁ d) (own-lane r y o)

  lane-ok : ∀ y → K y → Ok (y ++ [ ix 1 ])
  lane-ok y (o , h) = owned-snoc p y (ix 1) o , headed-snoc y h

  -- An outer position over no root a lane may subscribe at is one.
  ok-apart : ∀ y r → K y → Ok r → ¬ Owned y r → Ok y
  ok-apart y r (inj₂ t , hy) okr ny = inj₂ t , hy
  ok-apart y r (inj₁ q , hy) okr ny with prefix-plus p y q
  ... | inj₁ refl = ⊥-elim (ny (beneath-owned p r (proj₁ okr)))
  ... | inj₂ q⁺   = inj₁ q⁺ , hy

  -- A step under a root is free of an outer value apart from it.
  q-pin : ∀ r k y → Ok r → Under r k → D r y → K y → ¬ Owned (y ++ [ ix 1 ]) k × Disjoint y k
  q-pin r k y okr (ork , _ , shy) d ky =
    shy (y ++ [ ix 1 ]) (lane-ok y ky) (proj₁ d)
    , shy y (ok-apart y r ky okr (proj₂ d)) (proj₂ d , aside-not r y d)
    , λ o → aside-not r y d (owned-trans r k y ork o)

  free : ∀ {A} r k (x : Events A) → Ok r → Under r k → Every (D r) x → Every K x → Free x k
  free r k x okr u dx kx = every-mono (λ y dk → q-pin r k y okr u (proj₁ dk) (proj₂ dk)) x (every-zip x dx kx)

  free∞ : ∀ {A} r k (e : Events∞ A) → Ok r → Under r k → Every∞ (D r) e → Every∞ K e → FreeC (force e) (cut e) k
  free∞ r k e okr u (dx , dc) (kx , kc) =
    free r k (force e) okr u dx kx , everyT-mono (λ y dk → q-pin r k y okr u (proj₁ dk) (proj₂ dk)) (cut e) (everyT-zip (cut e) dc kc)

  freeO : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) r k → Ok r → Under r k → Aside o r → Heldᴹ o → FreeO o k
  freeO nothing  r k okr u a h = tt
  freeO (just e) r k okr u a h = free∞ r k e okr u a (Outer.kx h , Outer.kc h)

  -- A step an ended lane left: under no other root, free of the outer.
  ended : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) r k rs → Ok r → Under r k → All (λ r′ → Ok r′ × Disjoint r r′) rs → Aside o r → Heldᴹ o
        → All (λ r′ → ¬ Owned r′ k) rs × FreeO o k
  ended o r k rs okr u oks a h = mapᴬ (λ {r′} od → proj₂ (proj₂ u) r′ (proj₁ od) (disjoint-swap r r′ (proj₂ od))) oks , freeO o r k okr u a h

  -- A step under root `r`: an outer position, over no root apart from `r`.
  under-k : ∀ r k → Ok r → Under r k → K k
  under-k r k okr u = owned-trans p r k (beneath-owned p r (proj₁ okr)) (proj₁ u) , proj₁ (proj₂ u)

  under-over : ∀ r k r′ → Under r k → Disjoint r r′ → ¬ Owned k r′
  under-over r k r′ u d o = proj₁ d (owned-trans r k r′ (proj₁ u) o)

  -- An outer position apart from root `r`: keyed with no step under it.
  disjoint-under : ∀ r a b → Ok r → K a → ¬ Owned r a → ¬ Owned a r → Under r b → Disjoint a b
  disjoint-under r a b okr ka nra nar u =
    (λ o → proj₂ (proj₂ u) a (ok-apart a r ka okr nar) (nar , nra) o)
    , (λ o → nra (owned-trans r b a (proj₁ u) o))

  apart-under : ∀ r a b → Ok r → K a → ¬ Owned r a → ¬ Owned a r → Under r b → Apart a b
  apart-under r a b okr ka nra nar u = apart-of (disjoint-under r a b okr ka nra nar u)

  -- Steps under roots apart are apart.
  disjoint-roots : ∀ {B} r a → Ok r → Under r a → {ls : List (Events∞ B)} {rs : List Pos} → Roots ls rs → All (Disjoint r) rs
                 → All (λ l → EveryT (Disjoint a) (cut l)) ls
  disjoint-roots r a okr ua []ᴿ                          []ᴬ       = []ᴬ
  disjoint-roots r a okr ua (_∷ᴿ_ {r = r′} {l = l} st R) (d ∷ᴬ ds) =
    everyT-mono (λ b ub → (λ o → proj₂ (proj₂ ub) r okr d (owned-trans r a b (proj₁ ua) o))
                         , (λ o → proj₂ (proj₂ ua) r′ (Lane.ok st) (disjoint-swap r r′ d) (owned-trans r′ b a (proj₁ ub) o)))
      (cut l) (Lane.kc st)
    ∷ᴬ disjoint-roots r a okr ua R ds

  apart-roots : ∀ {B} r a → Ok r → Under r a → {ls : List (Events∞ B)} {rs : List Pos} → Roots ls rs → All (Disjoint r) rs
              → All (λ l → EveryT (Apart a) (cut l)) ls
  apart-roots r a okr ua R ds = mapᴬ (λ {l} → everyT-mono (λ b → apart-of) (cut l)) (disjoint-roots r a okr ua R ds)

  -- A pool's next steps.
  pool-later : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) rs k u → Pool o rs (pin k u) → Pool o rs (later u)
  pool-later o rs k u (st , et , ew , ef) = proj₂ (sortedᵀ st) , proj₂ (everyᵀ et) , proj₂ (everyᵀ ew) , proj₂ (flatᵀ ef)

  -- Past an outer skip.
  pool-oskip : ∀ {B} q (w : Events∞ (MonotonicList B)) c t rs → PoolF (FreeC (skip q w) c) rs t → Pool (just w) rs t
  pool-oskip q w c t rs (st , et , wd) = st , everyT-mono (λ k af → proj₁ af , proj₂ (every (proj₁ (proj₂ af)))) t et , wd

  -- A lane ending under root `r` leaves its cut to the pool.
  pool-ended : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) rbs r ras t {x : Events B} c → Lane r x c
             → All (λ r′ → Ok r′ × Disjoint r r′) (rbs ++ ras) → Aside o r → Heldᴹ o → Pool o (rbs ++ r ∷ ras) t → Pool o (rbs ++ ras) (t ∪ c)
  pool-ended o rbs r ras t c st oks a h (sp , ep , ew , ef) =
    sortedT-∪ t c sp (proj₁ (trail (Lane.trl st)))
    , everyT-∪ t c (everyT-mono (λ k af → proj₂ (all-pick rbs ras (proj₁ af)) , proj₂ af) t ep)
        (everyT-mono (λ k u → ended o r k (rbs ++ ras) (Lane.ok st) u oks a h) c (Lane.kc st))
    , everyT-∪ t c (everyT-mono (λ k w → proj₂ (all-pick rbs ras (proj₁ w)) , proj₂ w) t ew)
        (everyT-mono (λ k u → mapᴬ (λ {r′} od → under-over r k r′ u (proj₂ od)) oks , under-k r k (Lane.ok st) u) c (Lane.kc st))
    , flatT-∪ t c ef (trailᶠ (Lane.trl st))
        (everyT-mono (λ a ia → everyT-mono (λ b u → apart-under r a b (Lane.ok st) (proj₂ (proj₁ ia))
                                                      (proj₁ (all-pick rbs ras (proj₁ (proj₂ ia)))) (proj₁ (all-pick rbs ras (proj₁ (proj₁ ia)))) u)
                                    c (Lane.kc st))
          t (everyT-zip t ew ep))

  -- And with one queued, subscribes it just past its end.
  pool-hand : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) rbs r ras t c (l : Events∞ B) → Lane r (end c) (cut l)
            → All (λ r′ → Ok r′ × Disjoint r r′) (rbs ++ ras) → Aside o r → Heldᴹ o → Pool o (rbs ++ r ∷ ras) t
            → Pool o ((c ++ [ ix 1 ]) ∷ rbs ++ ras) (t ∪ cut l)
  pool-hand o rbs r ras t c l st oks a h pl with pool-ended o rbs r ras t (cut l) st oks a h pl
  ... | sp , ep , ew , ef =
    sp , everyT-mono (λ k z → proj₁ (proj₁ z) ∷ᴬ proj₁ (proj₂ z) , proj₂ (proj₂ z)) (t ∪ cut l) (everyT-zip (t ∪ cut l) c1 ep)
    , everyT-mono (λ k z → proj₂ (proj₁ z) ∷ᴬ proj₁ (proj₂ z) , proj₂ (proj₂ z)) (t ∪ cut l) (everyT-zip (t ∪ cut l) c1 ew) , ef
    where
      c₁  = c ++ [ ix 1 ]
      uc  = every (Lane.kx st)
      orc = proj₁ uc
      old : ∀ k → (All (λ r′ → ¬ Owned k r′) (rbs ++ r ∷ ras) × K k) × (All (λ r′ → ¬ Owned r′ k) (rbs ++ r ∷ ras) × FreeO o k)
          → ¬ Owned c₁ k × ¬ Owned k c₁
      old k ((nk , kk) , (nr , _)) =
        (λ o₁ → nrk (owned-trans r c₁ k (own-lane r c orc) o₁))
        , proj₁ (apart-mark k c (ix 1) (ix-mark 1) (proj₂ (proj₂ uc) k (ok-apart k r kk (Lane.ok st) nkr) (nkr , nrk) , λ o₁ → nrk (owned-trans r c k orc o₁)))
        where nrk = proj₁ (all-pick rbs ras nr)
              nkr = proj₁ (all-pick rbs ras nk)
      c1 : EveryT (λ k → ¬ Owned c₁ k × ¬ Owned k c₁) (t ∪ cut l)
      c1 = everyT-∪ t (cut l) (everyT-mono old t (everyT-zip t (proj₁ (proj₂ (proj₂ pl))) (proj₁ (proj₂ pl))))
             (everyT-mono (λ k tr → proj₁ (proj₂ tr)) (cut l) (proj₁ (proj₂ (trail (Lane.trl st)))))

  -- A lane dropped past an outer value at `q` leaves nothing before the
  -- step the value shows.
  drop-atop : ∀ {B} r q (x : Events B) c → Lane r x c → Beyond q x → D r q → AtopT (q ++ [ ix 0 ]) c
  drop-atop r q x idle      st b d = tt
  drop-atop r q x (pin k u) st b d = go x b (proj₁ (everyᵀ (proj₁ (proj₂ (trail (Lane.trl st)))))) (proj₁ (everyᵀ (Lane.kc st)))
    where
      go : ∀ x → Beyond q x → TrailE x k → Under r k → k <ᵖ (q ++ [ ix 0 ]) ≡ false
      go (out n _ _) b tr          u = <ᵖ-step q k (still q n k b (proj₁ tr))
      go (skip n _)  b (inj₁ tr)   u = <ᵖ-step q k (still q n k b tr)
      go (skip n _)  b (inj₂ m) u with k <ᵖ q in kq
      ... | true  = ⊥-elim (aside-not r q d (owned-trans r k q (proj₁ u) (inj₁ (marks-between q m kq b))))
      ... | false with <ᵖ-split q k kq
      ...   | inj₁ qk   = <ᵖ-step q k qk
      ...   | inj₂ refl = ⊥-elim (aside-not r q d (proj₁ u))
      go (end n)     b tr          u = <ᵖ-step q k (<ᵖ-trans q n k b (proj₁ tr))
      go hush        b ()          u

  drops-atop : ∀ {B} q (ls : List (Events∞ B)) {rs} → Roots ls rs → All (λ l → Beyond q (force l)) ls → All (λ r → D r q) rs
             → AtopT (q ++ [ ix 0 ]) (M′.cuts ls)
  drops-atop q []       []ᴿ       []ᴬ       []ᴬ       = tt
  drops-atop q (l ∷ ls) (st ∷ᴿ R) (b ∷ᴬ bs) (d ∷ᴬ ds) =
    atopT-∪ (q ++ [ ix 0 ]) (cut l) (M′.cuts ls) (drop-atop _ q (force l) (cut l) st b d) (drops-atop q ls R bs ds)

  drops-sorted : ∀ {B} (ls : List (Events∞ B)) {rs} → Roots ls rs → SortedT (M′.cuts ls)
  drops-sorted []       []ᴿ       = sortedT-idle
  drops-sorted (l ∷ ls) (st ∷ᴿ R) = sortedT-∪ (cut l) (M′.cuts ls) (proj₁ (trail (Lane.trl st))) (drops-sorted ls R)

  drops-free : ∀ {B} q (m : MonotonicList B) (w : Events∞ (MonotonicList B)) (ls : List (Events∞ B)) {rs} → Roots ls rs
             → All (λ r → Every (D r) (out q m w)) rs → Ok (q ++ [ ix 1 ]) → Every∞ K w
             → All (λ l → EveryT (λ k → All (λ r → ¬ Owned r k) [ q ++ [ ix 1 ] ] × FreeC (force w) (cut w) k) (cut l)) ls
  drops-free q m w []       []ᴿ       []ᴬ       okq kw = []ᴬ
  drops-free q m w (l ∷ ls) (_∷ᴿ_ {r = r} st R) (a ∷ᴬ as) okq kw =
    everyT-mono (λ k u → proj₂ (proj₂ u) (q ++ [ ix 1 ]) okq (proj₁ (proj₁ (every a))) ∷ᴬ []ᴬ , free∞ r k w (Lane.ok st) u (proj₂ (every a)) kw)
      (cut l) (Lane.kc st)
    ∷ᴬ drops-free q m w ls R as okq kw

  -- And over no root where the value subscribes its lane, outer positions.
  drops-wide : ∀ {B} q (m : MonotonicList B) (w : Events∞ (MonotonicList B)) (ls : List (Events∞ B)) {rs} → Roots ls rs
             → All (λ r → Every (D r) (out q m w)) rs
             → All (λ l → EveryT (λ k → All (λ r → ¬ Owned k r) [ q ++ [ ix 1 ] ] × K k) (cut l)) ls
  drops-wide q m w []       []ᴿ       []ᴬ       = []ᴬ
  drops-wide q m w (l ∷ ls) (_∷ᴿ_ {r = r} st R) (a ∷ᴬ as) =
    everyT-mono (λ k u → (λ o → proj₂ (proj₁ (proj₁ (every a))) (owned-trans r k (q ++ [ ix 1 ]) (proj₁ u) o)) ∷ᴬ []ᴬ , under-k r k (Lane.ok st) u)
      (cut l) (Lane.kc st)
    ∷ᴬ drops-wide q m w ls R as

  -- No step a dropped lane leaves inside another's.
  drops-flat : ∀ {B} (ls : List (Events∞ B)) {rs} → Roots ls rs → Parted rs → FlatT (M′.cuts ls)
  drops-flat []       []ᴿ       pt        = flatT-idle
  drops-flat (l ∷ ls) (_∷ᴿ_ {r = r} st R) (ds , pt) =
    flatT-∪ (cut l) (M′.cuts ls) (trailᶠ (Lane.trl st)) (drops-flat ls R pt)
      (everyT-mono (λ a u → cuts-every ls (apart-roots r a (Lane.ok st) u R ds)) (cut l) (Lane.kc st))

  -- An outer position apart from every dropped root: keyed with nothing they leave.
  drops-disjoint : ∀ {B} a (ls : List (Events∞ B)) {rs} → Roots ls rs → K a → All (λ r → ¬ Owned r a) rs → All (λ r → ¬ Owned a r) rs
                 → All (λ l → EveryT (Disjoint a) (cut l)) ls
  drops-disjoint a []       []ᴿ       ka []ᴬ       []ᴬ       = []ᴬ
  drops-disjoint a (l ∷ ls) (_∷ᴿ_ {r = r} st R) ka (n ∷ᴬ ns) (o ∷ᴬ os) =
    everyT-mono (λ b u → disjoint-under r a b (Lane.ok st) ka n o u) (cut l) (Lane.kc st) ∷ᴬ drops-disjoint a ls R ka ns os

  drops-apart : ∀ {B} a (ls : List (Events∞ B)) {rs} → Roots ls rs → K a → All (λ r → ¬ Owned r a) rs → All (λ r → ¬ Owned a r) rs
              → All (λ l → EveryT (Apart a) (cut l)) ls
  drops-apart a ls R ka ns os = mapᴬ (λ {l} → everyT-mono (λ b → apart-of) (cut l)) (drops-disjoint a ls R ka ns os)

  -- What the merge holds after an outer value's step.
  data Taken {B} (q : Pos) (w : Events∞ (MonotonicList B)) (t : Tail) : List (Events∞ B) × List (MonotonicList B) × Tail → Set where
    taken : ∀ {ls qs d rs} → Roots ls rs → Parted rs → All (Aside (just w)) rs → All (λ l → Atop (q ++ [ ix 0 ]) (force l)) ls
          → All Gen qs → Pool (just w) rs (t ∪ d) → AtopT (q ++ [ ix 0 ]) d → Taken q w t (ls , qs , d)

  module Admit {B} (q : Pos) (m : MonotonicList B) (w : Events∞ (MonotonicList B)) (t : Tail) {c : Tail} {rs : List Pos}
               (asd : All (λ r → Every (D r) (out q m w)) rs) (gm : Gen m) (okq : Ok (q ++ [ ix 1 ]))
               (sp : Aside (just w) (q ++ [ ix 1 ])) (kw : Every∞ K w)
               (pl : PoolF (FreeC (out q m w) c) rs t) where

    q₁ = q ++ [ ix 1 ]
    q₀ = q ++ [ ix 0 ]
    fit = gm q₁ okq

    top : Atop q₀ (force (M′.enter m q₁))
    top = atop-weaken q₁ q₀ _ (<ᵖ-asym q₀ q₁ (<ᵖ-part q {ix 0} {ix 1} [] [] refl)) (proj₁ (proj₂ fit))

    rest′ : All (Aside (just w)) rs
    rest′ = mapᴬ (λ a → proj₂ (every a)) asd

    -- What the pool held, each step's facts side by side.
    items : EveryT (λ k → (All (λ r → ¬ Owned k r) rs × K k) × (All (λ r → ¬ Owned r k) rs × FreeC (out q m w) c k)) t
    items = everyT-zip t (proj₁ (proj₂ (proj₂ pl))) (proj₁ (proj₂ pl))

    -- A step free of the value at `q`: over none where it subscribes its lane.
    new-over : ∀ k → Free (out q m w) k → ¬ Owned k q₁
    new-over k f = proj₁ (apart-mark k q (ix 1) (ix-mark 1) (disjoint-swap q k (proj₂ (proj₁ (every f)))))

    held : ∀ {rs′} → (∀ k → All (λ r → ¬ Owned r k) rs → Free (out q m w) k → All (λ r → ¬ Owned r k) rs′)
         → EveryT (λ k → All (λ r → ¬ Owned r k) rs′ × FreeO (just w) k) t
    held f = everyT-mono (λ k af → f k (proj₁ af) (proj₁ (proj₂ af)) , proj₂ (every (proj₁ (proj₂ af)))) t (proj₁ (proj₂ pl))

    wide : ∀ {rs′} → (∀ k → All (λ r → ¬ Owned k r) rs → Free (out q m w) k → All (λ r → ¬ Owned k r) rs′)
         → EveryT (λ k → All (λ r → ¬ Owned k r) rs′ × K k) t
    wide g = everyT-mono (λ k z → g k (proj₁ (proj₁ z)) (proj₁ (proj₂ (proj₂ z))) , proj₂ (proj₁ z)) t items

    keep : ∀ {rs′} → (∀ k → All (λ r → ¬ Owned r k) rs → Free (out q m w) k → All (λ r → ¬ Owned r k) rs′)
         → (∀ k → All (λ r → ¬ Owned k r) rs → Free (out q m w) k → All (λ r → ¬ Owned k r) rs′) → Pool (just w) rs′ (t ∪ idle)
    keep f g = sortedT-∪ t idle (proj₁ pl) sortedT-idle
             , everyT-∪ t idle (held f) everyT-idle
             , everyT-∪ t idle (wide g) everyT-idle
             , flatT-∪ t idle (proj₂ (proj₂ (proj₂ pl))) flatT-idle (everyT-mono (λ _ _ → everyT-idle) t items)

    admit-new : ∀ ls qs → Roots ls rs → Parted rs → All Gen qs → All (λ l → Beyond q (force l)) ls
              → Taken q w t (M′.enter m q₁ ∷ ls , qs , idle)
    admit-new ls qs R pt gq bl =
      taken (fresh q₁ (M′.enter m q₁) fit okq ∷ᴿ R) (mapᴬ (λ a → proj₁ (proj₁ (every a))) asd , pt) (sp ∷ᴬ rest′)
            (top ∷ᴬ mapᴬ (λ {l} → beyond-step q (force l)) bl) gq (keep (λ k a f → proj₁ (proj₁ (every f)) ∷ᴬ a) (λ k a f → new-over k f ∷ᴬ a)) tt

    admit-keep : ∀ ls qs → Roots ls rs → Parted rs → All Gen qs → All (λ l → Beyond q (force l)) ls → Taken q w t (ls , qs , idle)
    admit-keep ls qs R pt gq bl = taken R pt rest′ (mapᴬ (λ {l} → beyond-step q (force l)) bl) gq (keep (λ k a f → a) (λ k a f → a)) tt

    admit-switch : ∀ ls qs → Roots ls rs → Parted rs → All Gen qs → All (λ l → Beyond q (force l)) ls → Taken q w t ([ M′.enter m q₁ ] , qs , M′.cuts ls)
    admit-switch ls qs R pt gq bl =
      taken (fresh q₁ (M′.enter m q₁) fit okq ∷ᴿ []ᴿ) ([]ᴬ , tt) (sp ∷ᴬ []ᴬ) (top ∷ᴬ []ᴬ) gq
            ( sortedT-∪ t (M′.cuts ls) (proj₁ pl) (drops-sorted ls R)
            , everyT-∪ t (M′.cuts ls) (held (λ k a f → proj₁ (proj₁ (every f)) ∷ᴬ []ᴬ)) (cuts-every ls (drops-free q m w ls R asd okq kw))
            , everyT-∪ t (M′.cuts ls) (wide (λ k a f → new-over k f ∷ᴬ []ᴬ)) (cuts-every ls (drops-wide q m w ls R asd))
            , flatT-∪ t (M′.cuts ls) (proj₂ (proj₂ (proj₂ pl))) (drops-flat ls R pt)
                (everyT-mono (λ a z → cuts-every ls (drops-apart a ls R (proj₂ (proj₁ z)) (proj₁ (proj₂ z)) (proj₁ (proj₁ z)))) t items))
            (drops-atop q ls R bl (mapᴬ (λ a → proj₁ (every a)) asd))

  admit-ok : ∀ {B} op q (m : MonotonicList B) w t ls qs {c rs} → Roots ls rs → Parted rs → All (λ r → Every (D r) (out q m w)) rs
           → All Gen qs → Gen m → Ok (q ++ [ ix 1 ]) → Aside (just w) (q ++ [ ix 1 ]) → All (λ l → Beyond q (force l)) ls
           → Every∞ K w → PoolF (FreeC (out q m w) c) rs t
           → Taken q w t (M′.admit op (q ++ [ ix 1 ]) m ls qs)
  admit-ok (M′.mergeᶠ nothing)  q m w t ls       qs R pt asd gq gm okq sp bl kw pl = Admit.admit-new q m w t asd gm okq sp kw pl ls qs R pt gq bl
  admit-ok (M′.mergeᶠ (just n)) q m w t ls       qs R pt asd gq gm okq sp bl kw pl with length ls <ᵇ n
  ... | true  = Admit.admit-new q m w t asd gm okq sp kw pl ls qs R pt gq bl
  ... | false = Admit.admit-keep q m w t asd gm okq sp kw pl ls (qs ++ [ m ]) R pt (All++⁺ gq (gm ∷ᴬ []ᴬ)) bl
  admit-ok M′.switchᶠ           q m w t ls       qs R pt asd gq gm okq sp bl kw pl = Admit.admit-switch q m w t asd gm okq sp kw pl ls qs R pt gq bl
  admit-ok M′.exhaustᶠ          q m w t []       qs R pt asd gq gm okq sp bl kw pl = Admit.admit-new q m w t asd gm okq sp kw pl [] qs R pt gq bl
  admit-ok M′.exhaustᶠ          q m w t (l ∷ ls) qs R pt asd gq gm okq sp bl kw pl = Admit.admit-keep q m w t asd gm okq sp kw pl (l ∷ ls) qs R pt gq bl

  -- The lanes other than one ending at `c` under `r` are all past `c`.
  clear-lanes : ∀ {B} r c {ls : List (Events∞ B)} {rs} → Ok r → Owned r c → Roots ls rs → All (Disjoint r) rs
              → All (λ l → Atop c (force l)) ls → All (λ l → Atop (c ++ [ ix 0 ]) (force l)) ls
  clear-lanes r c okr oc []ᴿ                 []ᴬ       []ᴬ       = []ᴬ
  clear-lanes r c okr oc (_∷ᴿ_ {l = l} st R) (d ∷ᴬ ds) (a ∷ᴬ as) =
    beyond-step c (force l) (atop-clear r c (force l) oc a (every-mono (λ h u → proj₂ (proj₂ u) r okr d) (force l) (Lane.kx st)))
    ∷ᴬ clear-lanes r c okr oc R ds as

  -- And so is the outer.
  atop-hand : ∀ {B} r c (o : Maybe (Events∞ (MonotonicList B))) → Owned r c → Atopᴹ c o → Aside o r → Atopᴹ (c ++ [ ix 0 ]) o
  atop-hand r c nothing  oc ao a = tt
  atop-hand r c (just e) oc ao a = beyond-step c (force e) (atop-clear r c (force e) oc ao (every-mono (aside-not r) (force e) (proj₁ a)))

  -- Where a lane's end at `c` subscribes the next, apart from every
  -- other root and from where the outer subscribes its lanes.
  hand-ok : ∀ r c l → Ok r → Under r c → Ok (c ++ [ l ])
  hand-ok r c l (br , _) (orc , hc , _) = owned-snoc p c l (owned-trans p r c (beneath-owned p r br) orc) , headed-snoc c hc

  hand-apart : ∀ r c r′ → Under r c → Ok r′ → Disjoint r r′ → Disjoint (c ++ [ ix 1 ]) r′
  hand-apart r c r′ (orc , _ , shy) ok′ d =
    disjoint-swap r′ (c ++ [ ix 1 ])
      (apart-mark r′ c (ix 1) (ix-mark 1) (shy r′ ok′ (disjoint-swap r r′ d) , λ o → proj₁ d (owned-trans r c r′ orc o)))

  hand-aside : ∀ {B} r c (o : Maybe (Events∞ (MonotonicList B))) → Ok r → Under r c → Aside o r → Heldᴹ o → Aside o (c ++ [ ix 1 ])
  hand-aside r c nothing  okr u a h = tt
  hand-aside r c (just e) okr u a h =
    every-mono one (force e) (every-zip (force e) (proj₁ a) (Outer.kx h)) , everyT-mono one (cut e) (everyT-zip (cut e) (proj₂ a) (Outer.kc h))
    where
      one : ∀ y → D r y × K y → D (c ++ [ ix 1 ]) y
      one y (d , ky) = apart-mark (y ++ [ ix 1 ]) c (ix 1) (ix-mark 1)
                         (proj₂ (proj₂ u) (y ++ [ ix 1 ]) (lane-ok y ky) (proj₁ d) , λ o → proj₂ (proj₁ d) (owned-trans r c (y ++ [ ix 1 ]) (proj₁ u) o))
                       , proj₁ (apart-mark y c (ix 1) (ix-mark 1)
                           (proj₂ (proj₂ u) y (ok-apart y r ky okr (proj₂ d)) (proj₂ d , aside-not r y d) , λ o → aside-not r y d (owned-trans r c y (proj₁ u) o)))

  mutual
    ordered-go : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t {rs} → Roots ls rs → Parted rs → All (Aside o) rs → All Gen qs
               → Heldᴹ o → Pool o rs t → Ordered (M′.go op o ls qs t)
    ordered-go op o ls qs idle      R pt asd gq h pl = ordered-parts op o ls qs idle R pt asd gq h pl tt
    ordered-go op o ls qs (pin k u) R pt asd gq h pl with M′.ahead-of k o ls in e
    ... | true  = ordered-pool op o ls qs k u e R pt asd gq h pl
    ... | false = ordered-parts op o ls qs (pin k u) R pt asd gq h pl e

    ordered-pool : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs k u {rs} → M′.ahead-of k o ls ≡ true → Roots ls rs → Parted rs
                 → All (Aside o) rs → All Gen qs → Heldᴹ o → Pool o rs (pin k u) → Ordered (M′.left op o ls qs k u true)
    ordered (ordered-pool op o ls qs k u {rs} e R pt asd gq h pl) =
      atop-go op o ls qs (later u) k (proj₁ (ahead-atop k o ls e)) (proj₂ (ahead-atop k o ls e)) (proj₁ (sortedᵀ (proj₁ pl)))
      , ordered-go op o ls qs (later u) R pt asd gq h (pool-later o rs k u pl)

    ordered-parts : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t {rs} → Roots ls rs → Parted rs → All (Aside o) rs → All Gen qs
                  → Heldᴹ o → Pool o rs t → Behind o ls t → Ordered (M′.parts op o ls qs t)
    ordered-parts op o ls qs t R pt asd gq h pl bh with M′.earliest ls | earliest-picks ls
    ... | none            | hs                  = ordered-via op o ls qs t R pt asd gq h pl bh hs
    ... | found k bs l as | (eq , hk , ab , aa) with roots-at bs l as eq R
    ...   | split rb st ra = ordered-race op o k bs l as qs t rb st ra pt asd gq h pl (behind-at o t eq bh) hk ab aa

    ordered-via : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t {rs} → Roots ls rs → Parted rs → All (Aside o) rs → All Gen qs
                → Heldᴹ o → Pool o rs t → Behind o ls t → All (λ l → M′.head (force l) ≡ nothing) ls → Ordered (M′.viaOuter op o ls qs t)
    ordered-via op nothing  ls qs t R pt asd gq h pl bh hs = record { ordered = tt }
    ordered-via op (just e) ls qs t R pt asd gq h pl bh hs with M′.head (force e) in he
    ... | nothing = ordered-outer op e ls qs t (force e) R pt asd gq h pl (lead-hush (force e) ls hs) (atopᴴ-nothing (force e) t he)
    ... | just k  = ordered-outer op e ls qs t (force e) R pt asd gq h pl (lead-hush (force e) ls hs)
                      (atopᴴ (force e) t he (behind-atop k (just e) ls t bh (mapᴬ (λ {l} → atop-nothing k (force l)) hs) (self-atop (force e) he)))

    ordered-race : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) k bs (l : Events∞ B) as qs t {rbs r ras}
                 → Roots bs rbs → Static r l → Roots as ras → Parted (rbs ++ r ∷ ras) → All (Aside o) (rbs ++ r ∷ ras) → All Gen qs
                 → Heldᴹ o → Pool o (rbs ++ r ∷ ras) t → Behind o (bs ++ l ∷ as) t → M′.head (force l) ≡ just k
                 → All (λ x → Atop k (force x)) bs → All (λ x → Atop k (force x)) as → Ordered (M′.race op o k bs l as qs t)
    ordered-race op nothing  k bs l as qs t rb st ra pt asd gq h pl bh hk ab aa =
      ordered-lane op nothing bs l as qs t (force l) rb st ra pt asd gq h pl hk ab aa tt
        (behind-atop k nothing (bs ++ l ∷ as) t bh (All++⁺ ab (self-atop (force l) hk ∷ᴬ aa)) tt)
    ordered-race op (just e) k bs l as qs t rb st ra pt asd gq h pl bh hk ab aa with M′.head (force e) in he
    ... | nothing = ordered-lane op (just e) bs l as qs t (force l) rb st ra pt asd gq h pl hk ab aa (atop-nothing k (force e) he)
                      (behind-atop k (just e) (bs ++ l ∷ as) t bh (All++⁺ ab (self-atop (force l) hk ∷ᴬ aa)) (atop-nothing k (force e) he))
    ... | just k′ with k′ <ᵖ k in kk
    ...   | true  = ordered-outer op e (bs ++ l ∷ as) qs t (force e) (roots-++ rb (st ∷ᴿ ra)) pt asd gq h pl
                      (lead-of (force e) (bs ++ l ∷ as) he
                        (All++⁺ (mapᴬ (λ {x} → beyond-still k′ k (force x) kk) ab)
                                (beyond-just k′ (force l) hk kk ∷ᴬ mapᴬ (λ {x} → beyond-still k′ k (force x) kk) aa)))
                      (atopᴴ (force e) t he
                        (behind-atop k′ (just e) (bs ++ l ∷ as) t bh
                          (mapᴬ (λ {x} → atop-weaken k k′ (force x) (<ᵖ-asym k′ k kk)) (All++⁺ ab (self-atop (force l) hk ∷ᴬ aa)))
                          (self-atop (force e) he)))
    ...   | false = ordered-lane op (just e) bs l as qs t (force l) rb st ra pt asd gq h pl hk ab aa (atop-just (force e) he kk)
                      (behind-atop k (just e) (bs ++ l ∷ as) t bh (All++⁺ ab (self-atop (force l) hk ∷ᴬ aa)) (atop-just (force e) he kk))

    ordered-outer : ∀ {B} op (e : Events∞ (MonotonicList B)) ls qs t (x : Events (MonotonicList B)) {rs} → Roots ls rs → Parted rs
                  → All (λ r → Every (D r) x × EveryT (D r) (cut e)) rs → All Gen qs → Outer x (cut e)
                  → PoolF (FreeC x (cut e)) rs t → Lead x ls → Atopᴴ x t
                  → Ordered (M′.outer op e ls qs t x)
    ordered (ordered-outer op e ls qs t (out q m w) R pt asd gq h pl ld at)
      with M′.admit op (q ++ [ ix 1 ]) m ls qs
         | admit-ok op q m w t ls qs R pt (mapᴬ proj₁ asd) gq (proj₁ (values (Outer.spn h))) (lane-ok q (proj₁ (every (Outer.kx h))))
             (proj₁ (spread (Outer.spr h))) ld (proj₂ (every (Outer.kx h))) pl
    ... | ls′ , qs′ , d | taken R′ pt′ asd′ at′ gq′ pl′ ad =
      atop-go op (just w) ls′ qs′ (t ∪ d) (q ++ [ ix 0 ]) at′ (beyond-step q (force w) (past-beyond q (force w) (proj₁ (steady (Outer.std h)))))
        (atopT-∪ (q ++ [ ix 0 ]) t d (pool-step q t at (everyT-mono (λ k af eq → proj₁ (proj₂ (proj₁ (every (proj₁ (proj₂ af))))) (subst (Owned q) eq (inj₁ (prefix-refl q)))) t (proj₁ (proj₂ pl)))) ad)
      , ordered-go op (just w) ls′ qs′ (t ∪ d) R′ pt′ asd′ gq′ (outer-out h) pl′
    ordered (ordered-outer op e ls qs t (skip q w) {rs} R pt asd gq h pl ld at) =
      atop-go op (just w) ls qs t q (mapᴬ (λ {l} → beyond-atop q (force l)) ld) (proj₁ (ordered (Outer.ord h))) at
      , ordered-go op (just w) ls qs t R pt (mapᴬ (λ a → proj₂ (every (proj₁ a))) asd) gq (outer-skip h)
          (pool-oskip q w (cut e) t rs pl)
    ordered (ordered-outer op e [] [] t (end c) R pt asd gq h pl ld at) = tt
    ordered (ordered-outer op e [] (m ∷ qs) t (end c) []ᴿ pt asd gq h pl ld at) =
      atop-go op nothing [] (m ∷ qs) (t ∪ cut e) c []ᴬ tt (outer-end-atop c e t h at)
      , ordered-go op nothing [] (m ∷ qs) (t ∪ cut e) []ᴿ tt []ᴬ gq tt (outer-end-pool c e t [] h asd pl)
    ordered (ordered-outer {B} op e (l ∷ ls) qs t (end c) {rs} R pt asd gq h pl ld at) =
      atop-go op nothing (l ∷ ls) qs (t ∪ cut e) c (mapᴬ (λ {x} → beyond-atop c (force x)) ld) tt (outer-end-atop c e t h at)
      , ordered-go op nothing (l ∷ ls) qs (t ∪ cut e) R pt (aside-none {B} rs) gq tt (outer-end-pool c e t rs h asd pl)
    ordered (ordered-outer op e ls qs t hush R pt asd gq h pl ld at) = tt

    ordered-lane : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) bs (l : Events∞ B) as qs t (x : Events B) {rbs r ras}
                 → Roots bs rbs → Lane r x (cut l) → Roots as ras → Parted (rbs ++ r ∷ ras) → All (Aside o) (rbs ++ r ∷ ras) → All Gen qs
                 → Heldᴹ o → Pool o (rbs ++ r ∷ ras) t → ∀ {k} → M′.head x ≡ just k → All (λ y → Atop k (force y)) bs
                 → All (λ y → Atop k (force y)) as → Atopᴹ k o → AtopT k t → Ordered (M′.lane op o bs l as qs t x)
    ordered (ordered-lane op o bs l as qs t (out k b w) rb st ra pt asd gq h pl refl ab aa ao at) =
      atop-go op o (bs ++ w ∷ as) qs t k (All++⁺ ab (proj₁ (ordered (Lane.ord st)) ∷ᴬ aa)) ao at
      , ordered-go op o (bs ++ w ∷ as) qs t (roots-++ rb (lane-out st ∷ᴿ ra)) pt asd gq h pl
    ordered (ordered-lane op o bs l as qs t (skip k w) rb st ra pt asd gq h pl refl ab aa ao at) =
      atop-go op o (bs ++ w ∷ as) qs t k (All++⁺ ab (proj₁ (ordered (Lane.ord st)) ∷ᴬ aa)) ao at
      , ordered-go op o (bs ++ w ∷ as) qs t (roots-++ rb (lane-skip st ∷ᴿ ra)) pt asd gq h pl
    ordered (ordered-lane op o bs l as (m ∷ qs) t (end c) {rbs} {r} {ras} rb st ra pt asd (gm ∷ᴬ gq) h pl refl ab aa ao at) =
      atop-go op o (M′.enter m c₁ ∷ bs ++ as) qs (t ∪ cut l) c₀
        (top ∷ᴬ clear-lanes r c (Lane.ok st) orc (roots-++ rb ra) (proj₁ pp) (All++⁺ ab aa))
        (atop-hand r c o orc ao ar)
        (atopT-∪ c₀ t (cut l)
           (pool-step c t at (everyT-mono (λ k af eq → proj₁ (all-pick rbs ras (proj₁ af)) (subst (Owned r) eq orc)) t (proj₁ (proj₂ pl))))
           (atopT-every c₀ (cut l) (λ k tr → <ᵖ-step c k (proj₁ tr)) (proj₁ (proj₂ (trail (Lane.trl st))))))
      , ordered-go op o (M′.enter m c₁ ∷ bs ++ as) qs (t ∪ cut l) (fresh c₁ (M′.enter m c₁) fit okc ∷ᴿ roots-++ rb ra)
          (mapᴬ (λ {r′} od → hand-apart r c r′ uc (proj₁ od) (proj₂ od)) oks , proj₂ pp)
          (hand-aside r c o (Lane.ok st) uc ar h ∷ᴬ proj₂ (all-pick rbs ras asd)) gq h
          (pool-hand o rbs r ras t c l st oks ar h pl)
      where
        c₀  = c ++ [ ix 0 ]
        c₁  = c ++ [ ix 1 ]
        uc  = every (Lane.kx st)
        orc = proj₁ uc
        okc = hand-ok r c (ix 1) (Lane.ok st) uc
        fit = gm c₁ okc
        top = atop-weaken c₁ c₀ _ (<ᵖ-asym c₀ c₁ (<ᵖ-part c {ix 0} {ix 1} [] [] refl)) (proj₁ (proj₂ fit))
        pp  = parted-pick rbs r ras pt
        ar  = proj₁ (all-pick rbs ras asd)
        oks = all-zip (roots-ok (roots-++ rb ra)) (proj₁ pp)
    ordered (ordered-lane op nothing [] l [] [] t (end c) rb st ra pt asd gq h pl refl ab aa ao at) = tt
    ordered (ordered-lane op nothing [] l (a ∷ as) [] t (end c) rb st ra pt asd gq h pl refl ab aa ao at) =
      lane-ended op nothing [] l (a ∷ as) t c rb st ra pt asd h pl ab aa ao at
    ordered (ordered-lane op nothing (b ∷ bs) l as [] t (end c) rb st ra pt asd gq h pl refl ab aa ao at) =
      lane-ended op nothing (b ∷ bs) l as t c rb st ra pt asd h pl ab aa ao at
    ordered (ordered-lane op (just e) bs l as [] t (end c) rb st ra pt asd gq h pl refl ab aa ao at) =
      lane-ended op (just e) bs l as t c rb st ra pt asd h pl ab aa ao at
    ordered (ordered-lane op o bs l as qs t hush rb st ra pt asd gq h pl () ab aa ao at)

    lane-ended : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) bs (l : Events∞ B) as t c {rbs r ras}
               → Roots bs rbs → Lane {B} r (end c) (cut l) → Roots as ras → Parted (rbs ++ r ∷ ras) → All (Aside o) (rbs ++ r ∷ ras)
               → Heldᴹ o → Pool o (rbs ++ r ∷ ras) t → All (λ y → Atop c (force y)) bs → All (λ y → Atop c (force y)) as → Atopᴹ c o → AtopT c t
               → Atop c (M′.go op o (bs ++ as) [] (t ∪ cut l)) × Ordered (M′.go op o (bs ++ as) [] (t ∪ cut l))
    lane-ended op o bs l as t c {rbs} {r} {ras} rb st ra pt asd h pl ab aa ao at =
      atop-go op o (bs ++ as) [] (t ∪ cut l) c (All++⁺ ab aa) ao
        (atopT-∪ c t (cut l) at (atopT-every c (cut l) (λ k tr → <ᵖ-asym c k (proj₁ tr)) (proj₁ (proj₂ (trail (Lane.trl st))))))
      , ordered-go op o (bs ++ as) [] (t ∪ cut l) (roots-++ rb ra) (proj₂ pp) (proj₂ (all-pick rbs ras asd)) []ᴬ h
          (pool-ended o rbs r ras t (cut l) st oks (proj₁ (all-pick rbs ras asd)) h pl)
      where
        pp  = parted-pick rbs r ras pt
        oks = all-zip (roots-ok (roots-++ rb ra)) (proj₁ pp)

    outer-end-atop : ∀ {B} c (e : Events∞ (MonotonicList B)) t → Outer (end c) (cut e) → AtopT c t → AtopT c (t ∪ cut e)
    outer-end-atop c e t h at = atopT-∪ c t (cut e) at (atopT-every c (cut e) (λ k tr → <ᵖ-asym c k (proj₁ tr)) (proj₁ (proj₂ (trail (Outer.trl h)))))

    outer-end-pool : ∀ {B} c (e : Events∞ (MonotonicList B)) t rs → Outer (end c) (cut e) → All (λ r → Every (D r) (end c) × EveryT (D r) (cut e)) rs
                   → PoolF (FreeC (end c) (cut e)) rs t → Pool {B} nothing rs (t ∪ cut e)
    outer-end-pool c e t rs h asd (st , et , ew , ef) =
      sortedT-∪ t (cut e) st (proj₁ (trail (Outer.trl h)))
      , everyT-∪ t (cut e) (everyT-mono (λ k af → proj₁ af , tt) t et)
          (everyT-mono (λ k a → mapᴬ (λ {r} → aside-not r k) a , tt) (cut e) ds)
      , everyT-∪ t (cut e) ew (everyT-mono (λ k z → mapᴬ proj₂ (proj₁ z) , proj₂ z) (cut e) (everyT-zip (cut e) ds (Outer.kc h)))
      , flatT-∪ t (cut e) ef (trailᶠ (Outer.trl h))
          (everyT-mono (λ a af → everyT-mono (λ y fy → (λ x → proj₂ (proj₂ fy) (owned-ext x)) , (λ x → proj₁ (proj₂ fy) (owned-ext x))) (cut e) (proj₂ (proj₂ af))) t et)
      where ds = everyT-all rs (cut e) (mapᴬ proj₂ asd)

  -- After a pool step at `k`, nothing shows inside it: each lane's first
  -- is past it and keyed apart from it by its root, the outer's keyed
  -- clear of it, and the pool's next is not inside it, the pool flat.
  calm-pool-n : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) ls qs k u {rs} → M′.ahead-of k o ls ≡ true → Roots ls rs → Parted rs
              → All (Aside o) rs → Heldᴹ o → Pool o rs (pin k u) → Obl false k o ls qs (later u)
  calm-pool-n o ls qs k u e R pt asd h (st , et , ew , ef) =
    by-lanes ls R (proj₁ (proj₁ (everyᵀ ew))) (proj₁ (proj₁ (everyᵀ et))) (clears-of o e)
    , by-outer o e (proj₂ (proj₁ (everyᵀ et)))
    , by-pool (later u) (proj₁ (flatᵀ ef))
    where
      kk = proj₂ (proj₁ (everyᵀ ew))
      clears-of : ∀ o → M′.ahead-of k o ls ≡ true → M′.clears k ls ≡ true
      clears-of nothing  e = e
      clears-of (just x) e with M′.clear k (M′.head (force x))
      ... | true = e
      by-lanes : ∀ ls {rs} → Roots ls rs → All (λ r → ¬ Owned k r) rs → All (λ r → ¬ Owned r k) rs → M′.clears k ls ≡ true
            → All (λ y → LaneAt (Clean false k) qs (force y)) ls
      by-lanes [] []ᴿ []ᴬ []ᴬ c = []ᴬ
      by-lanes (y ∷ ls) (_∷ᴿ_ {r = r} sb R) (a ∷ᴬ as) (b ∷ᴬ bs) c with M′.clear k (M′.head (force y)) in d
      ... | true =
        laneAt-map (λ v h → clean-of false v) qs (force y)
          (away-lane k qs (force y) (at-beyond k (force y) (clear-beyond k (force y) d)
            (every-mono (λ h u → proj₂ (proj₂ u) k (ok-apart k r kk (Lane.ok sb) a) (a , b)) (force y) (Lane.kx sb))))
        ∷ᴬ by-lanes ls R as bs c
      by-apart : ∀ q → ¬ Owned k q → ¬ Ext k (q ++ [ ix 0 ])
      by-apart q nk x with ext-snoc k q (ix 0) x
      ... | inj₁ x′   = nk (owned-ext x′)
      ... | inj₂ refl = nk (inj₁ (prefix-refl k))
      by-first : ∀ {A} (x : Events A) → Beyond k x → Free x k → OuterAt (Clean false k) x
      by-first (out q _ _) b f = tt , by-apart q (proj₂ (proj₂ (proj₁ (every f))))
      by-first (skip q _)  b f = tt , λ x → proj₂ (proj₂ (proj₁ (every f))) (owned-ext x)
      by-first (end c)     b f = b , λ x → proj₂ (proj₂ (every f)) (owned-ext x)
      by-first hush        b f = tt
      by-outer : ∀ o → M′.ahead-of k o ls ≡ true → FreeO o k → OuterAtᴹ (Clean false k) o
      by-outer nothing  e f = tt
      by-outer (just x) e f with M′.clear k (M′.head (force x)) in d
      ... | true = by-first (force x) (clear-beyond k (force x) d) (proj₁ f)
      by-pool : ∀ t → EveryT (λ h → ¬ Ext k h) t → PoolAt (Clean false k) t
      by-pool (pin _ _) a = tt , proj₁ (everyᵀ a)
      by-pool idle      a = tt

  -- Every other lane's first, keyed apart from `r` and no earlier than
  -- `k` it keys: away from `k`.
  calm-apart : ∀ {B A} r k (qs : List A) {ls : List (Events∞ B)} {rs} → Ok r → Owned r k → Roots ls rs → All (Disjoint r) rs
             → All (λ y → Atop k (force y)) ls → All (λ y → LaneAt (λ _ → Aloof k) qs (force y)) ls
  calm-apart r k qs okr ok []ᴿ                  []ᴬ       []ᴬ       = []ᴬ
  calm-apart r k qs okr ok (_∷ᴿ_ {l = y} sb R) (d ∷ᴬ ds) (a ∷ᴬ as) =
    away-lane k qs (force y) (at-apart r k (force y) ok a (every-mono (λ h u → proj₂ (proj₂ u) r okr d) (force y) (Lane.kx sb)))
    ∷ᴬ calm-apart r k qs okr ok R ds as

  -- The outer's first, keyed apart from root `r`, no earlier than `k` it keys.
  outer-apart : ∀ {B} r k (o : Maybe (Events∞ (MonotonicList B))) → Owned r k → Aside o r → Atopᴹ k o → OuterAtᴹ (λ _ → Aloof k) o
  outer-apart r k nothing  ok _ _ = tt
  outer-apart r k (just e) ok a x = away-outer k (force e) (at-apart r k (force e) ok x
    (every-mono (aside-not r) (force e) (proj₁ a)))

  -- After a lane's value at `k`, every part's next is past it and not
  -- inside it: the lane's own by its steadiness, the others keyed apart
  -- from its root.
  calm-out : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) bs (l : Events∞ B) as qs t k b w {rbs r ras}
           → Roots bs rbs → Lane r (out k b w) (cut l) → Roots as ras → Parted (rbs ++ r ∷ ras) → All (Aside o) (rbs ++ r ∷ ras)
           → Heldᴹ o → Pool o (rbs ++ r ∷ ras) t → All (λ y → Atop k (force y)) bs → All (λ y → Atop k (force y)) as → Atopᴹ k o → AtopT k t
           → Obl true k o (bs ++ w ∷ as) qs t
  calm-out {B} o bs l as qs t k b w {rbs} {r} {ras} rb st ra pt asd h pl ab aa ao at =
    mapᴬ (λ {y} → laneAt-map cl qs (force y))
      (All++⁺ (calm-apart r k qs okr ok rb (All++⁻ˡ rbs ds) ab)
        (away-lane k qs (force w) (past-at k (force w) (proj₁ (steady (Lane.std st)))) ∷ᴬ calm-apart r k qs okr ok ra (All++⁻ʳ rbs ds) aa))
    , outerᴹ-map cl o (outer-apart r k o ok (proj₁ (all-pick rbs ras asd)) ao)
    , poolAt-map cl t (pool-apart r k t ok at (everyT-mono (λ h a → proj₁ (all-pick rbs ras (proj₁ a))) t (proj₁ (proj₂ pl))))
    where
      okr = Lane.ok st
      ok  = proj₁ (proj₁ (every (Lane.kx st)))
      ds  = proj₁ (parted-pick rbs r ras pt)
      cl : ∀ v h → Aloof k h → Clean true k v h
      cl v h = clean-of true v

  -- After a lane's skip at `k`, nothing shows inside it, and a value or
  -- an end past it: the lane's own by its steadiness, an end strictly
  -- past so a queued lane's step is not inside it either; the others
  -- keyed apart from its root.
  calm-skip : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) bs (l : Events∞ B) as qs t k w {rbs r ras}
            → Roots bs rbs → Lane r (skip k w) (cut l) → Roots as ras → Parted (rbs ++ r ∷ ras) → All (Aside o) (rbs ++ r ∷ ras)
            → Heldᴹ o → Pool o (rbs ++ r ∷ ras) t → All (λ y → Atop k (force y)) bs → All (λ y → Atop k (force y)) as → Atopᴹ k o → AtopT k t
            → Obl false k o (bs ++ w ∷ as) qs t
  calm-skip {B} o bs l as qs t k w {rbs} {r} {ras} rb st ra pt asd h pl ab aa ao at =
    All++⁺ (mapᴬ (λ {y} → laneAt-map cl qs (force y)) (calm-apart r k qs okr ok rb (All++⁻ˡ rbs ds) ab))
      (own qs (force w) (proj₁ (steady (Lane.std st)))
       ∷ᴬ mapᴬ (λ {y} → laneAt-map cl qs (force y)) (calm-apart r k qs okr ok ra (All++⁻ʳ rbs ds) aa))
    , outerᴹ-map cl o (outer-apart r k o ok (proj₁ (all-pick rbs ras asd)) ao)
    , poolAt-map cl t (pool-apart r k t ok at (everyT-mono (λ h a → proj₁ (all-pick rbs ras (proj₁ a))) t (proj₁ (proj₂ pl))))
    where
      okr = Lane.ok st
      ok  = proj₁ (proj₁ (every (Lane.kx st)))
      ds  = proj₁ (parted-pick rbs r ras pt)
      cl : ∀ v h → Aloof k h → Clean false k v h
      cl v h = clean-of false v
      own : ∀ {A} (qs : List A) (x : Events B) → Clear k x → LaneAt (Clean false k) qs x
      own qs      (out h _ _) c = c
      own qs      (skip h _)  c = tt , c
      own []      (end c)     a = a
      own (_ ∷ _) (end c)     a = tt , proj₂ (past-step k c a)
      own qs      hush        c = tt

  -- After a lane's end at `c`, nothing shows inside it: what it left
  -- running trails it, the other parts keyed apart from its root.
  calm-end : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) bs (l : Events∞ B) as t c {rbs r ras}
           → Roots bs rbs → Lane {B} r (end c) (cut l) → Roots as ras → Parted (rbs ++ r ∷ ras) → All (Aside o) (rbs ++ r ∷ ras)
           → Heldᴹ o → Pool o (rbs ++ r ∷ ras) t → All (λ y → Atop c (force y)) bs → All (λ y → Atop c (force y)) as → Atopᴹ c o → AtopT c t
           → Obl false c o (bs ++ as) [] (t ∪ cut l)
  calm-end {B} o bs l as t c {rbs} {r} {ras} rb st ra pt asd h pl ab aa ao at =
    mapᴬ (λ {y} → laneAt-map cl [] (force y)) (All++⁺ (calm-apart r c [] okr oc rb (All++⁻ˡ rbs ds) ab) (calm-apart r c [] okr oc ra (All++⁻ʳ rbs ds) aa))
    , outerᴹ-map cl o (outer-apart r c o oc (proj₁ (all-pick rbs ras asd)) ao)
    , poolAt-∪ (Clean false c) t (cut l)
        (poolAt-map cl t (pool-apart r c t oc at (everyT-mono (λ h a → proj₁ (all-pick rbs ras (proj₁ a))) t (proj₁ (proj₂ pl)))))
        (left (cut l) (proj₁ (proj₂ (trail (Lane.trl st)))))
    where
      okr = Lane.ok st
      oc  = proj₁ (every (Lane.kx st))
      ds  = proj₁ (parted-pick rbs r ras pt)
      cl : ∀ v h → Aloof c h → Clean false c v h
      cl v h = clean-of false v
      left : ∀ u → EveryT (TrailE {B} (end c)) u → PoolAt (Clean false c) u
      left (pin k _) e = tt , proj₂ (proj₂ (proj₁ (everyᵀ e)))
      left idle      e = tt

  -- After a lane's end at `c` hands its queue on, nothing shows inside
  -- the step just past `c`: not the lane it subscribes, keyed apart from
  -- that step, not another, not what it left running.
  calm-queue : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) bs (l : Events∞ B) as m qs t c {rbs r ras}
             → Roots bs rbs → Lane {B} r (end c) (cut l) → Roots as ras → Parted (rbs ++ r ∷ ras) → All (Aside o) (rbs ++ r ∷ ras)
             → Gen m → Heldᴹ o → Pool o (rbs ++ r ∷ ras) t → All (λ y → Atop c (force y)) bs → All (λ y → Atop c (force y)) as → Atopᴹ c o → AtopT c t
             → Obl false (c ++ [ ix 0 ]) o (M′.enter m (c ++ [ ix 1 ]) ∷ bs ++ as) qs (t ∪ cut l)
  calm-queue {B} o bs l as m qs t c {rbs} {r} {ras} rb st ra pt asd gm h pl ab aa ao at =
    laneAt-map (λ v h → clean-of false v) qs (force n) (away-lane c₀ qs (force n) first)
    ∷ᴬ mapᴬ (λ {y} → laneAt-map cl qs (force y)) (All++⁺ (calm-apart r c qs okr oc rb (All++⁻ˡ rbs ds) ab) (calm-apart r c qs okr oc ra (All++⁻ʳ rbs ds) aa))
    , outerᴹ-map cl o (outer-apart r c o oc (proj₁ (all-pick rbs ras asd)) ao)
    , poolAt-∪ (Clean false c₀) t (cut l)
        (poolAt-map cl t (pool-apart r c t oc at (everyT-mono (λ h a → proj₁ (all-pick rbs ras (proj₁ a))) t (proj₁ (proj₂ pl)))))
        (left (cut l) (proj₁ (proj₂ (trail (Lane.trl st)))))
    where
      c₀  = c ++ [ ix 0 ]
      c₁  = c ++ [ ix 1 ]
      n   = M′.enter m c₁
      okr = Lane.ok st
      uc  = every (Lane.kx st)
      oc  = proj₁ uc
      ds  = proj₁ (parted-pick rbs r ras pt)
      fit = gm c₁ (hand-ok r c (ix 1) okr uc)
      d01 : Disjoint c₀ c₁
      d01 = sibling c (ix-mark _) (λ ()) , sibling c (ix-mark _) (λ ())
      first : At (λ _ → Aloof c₀) (force n)
      first = at-beyond c₀ (force n) (beyond-still c₀ c₁ (force n) (<ᵖ-part c {ix 0} {ix 1} [] [] refl) (proj₁ (proj₂ fit)))
                (every-mono (λ h u → proj₂ (proj₂ u) c₀ (hand-ok r c (ix 0) okr uc) d01) (force n) (proj₁ (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ fit)))))))
      cl : ∀ v h → Aloof c h → Clean false c₀ v h
      cl v h a = clean-of false v (step-past c h a)
      left : ∀ u → EveryT (TrailE {B} (end c)) u → PoolAt (Clean false c₀) u
      left (pin k _) e = clean-of false false (step-past c k (proj₁ (proj₁ (everyᵀ e)) , proj₂ (proj₂ (proj₁ (everyᵀ e)))))
      left idle      e = tt

  -- The lanes past an outer step at `q`, each keyed apart from it.
  lead-aloof : ∀ {B A} q (qs : List A) {ls : List (Events∞ B)} {rs} → K q → Roots ls rs → All (λ r → D r q) rs
             → All (λ l → Beyond q (force l)) ls → All (λ l → LaneAt (λ _ → Aloof q) qs (force l)) ls
  lead-aloof q qs kq []ᴿ                         []ᴬ       []ᴬ       = []ᴬ
  lead-aloof q qs kq (_∷ᴿ_ {r = r} {l = l} st R) (d ∷ᴬ ds) (b ∷ᴬ bs) =
    away-lane q qs (force l) (at-beyond q (force l) b
      (every-mono (λ h u → proj₂ (proj₂ u) q (ok-apart q r kq (Lane.ok st) (proj₂ d)) (proj₂ d , aside-not r q d)) (force l) (Lane.kx st)))
    ∷ᴬ lead-aloof q qs kq R ds bs

  -- Steady past a skip at `q`, the outer's next shows nothing inside it.
  outer-clear : ∀ {A} q (x : Events A) → Clear q x → OuterAt (Clean false q) x
  outer-clear q (out h _ _) c = clean-of false false (past-step q h c)
  outer-clear q (skip h _)  c = tt , c
  outer-clear q (end h)     c = c
  outer-clear q hush        c = tt

  -- The lane an outer value at `q` subscribes: away from the step it shows.
  admitted : ∀ {B A} q (m : MonotonicList B) (qs : List A) → K q → Gen m
           → LaneAt (Clean false (q ++ [ ix 0 ])) qs (force (M′.enter m (q ++ [ ix 1 ])))
  admitted q m qs kq gm =
    laneAt-map (λ v h → clean-of false v) qs (force n) (away-lane q₀ qs (force n)
      (at-beyond q₀ (force n) (beyond-still q₀ q₁ (force n) (<ᵖ-part q {ix 0} {ix 1} [] [] refl) (proj₁ (proj₂ fit)))
        (every-mono (λ h u → proj₂ (proj₂ u) q₀ ok₀ d01) (force n) (proj₁ (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ fit)))))))))
    where
      q₀  = q ++ [ ix 0 ]
      q₁  = q ++ [ ix 1 ]
      n   = M′.enter m q₁
      fit = gm q₁ (lane-ok q kq)
      ok₀ : Ok q₀
      ok₀ = owned-snoc p q (ix 0) (proj₁ kq) , headed-snoc q (proj₂ kq)
      d01 : Disjoint q₀ q₁
      d01 = sibling q (ix-mark _) (λ ()) , sibling q (ix-mark _) (λ ())

  -- The lanes an outer value at `q` keeps, past the step it shows.
  kept-lanes : ∀ {B A} q (qs : List A) {ls : List (Events∞ B)} {rs} → K q → Roots ls rs → All (λ r → D r q) rs
             → All (λ l → Beyond q (force l)) ls → All (λ l → LaneAt (Clean false (q ++ [ ix 0 ])) qs (force l)) ls
  kept-lanes q qs kq R ds bs = mapᴬ (λ {l} → laneAt-map (λ v h a → clean-of false v (step-past q h a)) qs (force l)) (lead-aloof q qs kq R ds bs)

  -- What a lane dropped past an outer value at `q` leaves: under its
  -- root, so away from the step the value shows.
  drops-clean : ∀ {B} q (ls : List (Events∞ B)) {rs} → K q → Roots ls rs → All (λ r → D r q) rs
              → All (λ l → Beyond q (force l)) ls → PoolAt (Clean false (q ++ [ ix 0 ])) (M′.cuts ls)
  drops-clean q ls kq R ds bs =
    poolAt-map (λ v h → clean-of false v) (M′.cuts ls)
      (pool-apart q (q ++ [ ix 0 ]) (M′.cuts ls) (inj₁ (prefix-++ q [ ix 0 ])) (drops-atop q ls R bs ds) (cuts-every ls (go ls R ds)))
    where
      go : ∀ ls {rs} → Roots ls rs → All (λ r → D r q) rs → All (λ l → EveryT (λ h → ¬ Owned q h) (cut l)) ls
      go []       []ᴿ                  []ᴬ       = []ᴬ
      go (l ∷ ls) (_∷ᴿ_ {r = r} st R) (d ∷ᴬ ds) =
        everyT-mono (λ h u → proj₂ (proj₂ u) q (ok-apart q r kq (Lane.ok st) (proj₂ d)) (proj₂ d , aside-not r q d)) (cut l) (Lane.kc st)
        ∷ᴬ go ls R ds

  -- An outer value at `q`'s next, and what ended parts left, past the
  -- step it shows.
  step-outer : ∀ {B q m c} {w : Events∞ (MonotonicList B)} → Outer (out q m w) c → OuterAt (Clean false (q ++ [ ix 0 ])) (force w)
  step-outer {q = q} {w = w} h =
    outerAt-map (λ v h′ a → clean-of false v (step-past q h′ a)) (force w) (away-outer q (force w) (past-at q (force w) (proj₁ (steady (Outer.std h)))))

  step-pool : ∀ {B} q m (w : Events∞ (MonotonicList B)) t {c rs} → AtopT q t → EveryT (λ k → All (λ r → ¬ Owned r k) rs × FreeC (out q m w) c k) t
            → PoolAt (Clean false (q ++ [ ix 0 ])) t
  step-pool q m w t at et =
    poolAt-map (λ v h a → clean-of false v (step-past q h a)) t
      (pool-apart q q t (inj₁ (prefix-refl q)) at (everyT-mono (λ k af → proj₁ (proj₂ (proj₁ (every (proj₁ (proj₂ af)))))) t et))
