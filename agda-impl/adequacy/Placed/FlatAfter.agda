{-# OPTIONS --guardedness #-}

module adequacy.Placed.FlatAfter where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_; [_]; length)
open import Data.Nat using (_<ᵇ_)
open import Data.List.Relation.Unary.All using (All; lookup) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_; map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to All++⁺; ++⁻ˡ to All++⁻ˡ; ++⁻ʳ to All++⁻ʳ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Relation.Nullary using (¬_)

open import Tree using (Later)
open import denotation.MonotonicList.Events using (Events; Events∞; Pos; Timeline; out; skip; end; hush; ix; last; _<ᵖ_; <ᵖ-asym; <ᵖ-split;
  <ᵖ-trans; <ᵖ-irrefl; <ᵖ-part; ≮-trans; <ᵖ-step; Tail∞; pin; idle; _∪_)
open import denotation.MonotonicList using (MonotonicList; agreeᵀ; none; found)
import denotation.MonotonicList.Events as M
import denotation.MonotonicList as M′
import denotation.Unfold as U
open import denotation.Unfold using (NEnv)
open import denotation.Denote using (flatOp) renaming (⟦_⟧ to ⟦_⟧ᴰ)
open import denotation.Compositional using (env-refl)
open import adequacy.Placed.Order using (Alienᴱ; Atop; Every; EveryT; Every∞; Ext; Headed; Ordered; Owned; Past; Prefix; Steady; Tagged; every; every-mono; everyT-idle; everyT-mono; everyT-∪; everyᵀ; every∞-mono; headed-snoc; ordered; owned-ext; prefix-++; steady; still)
open import adequacy.Placed.Keys using (module Merge; ahead-quiet; last-mark; owned-trans; prefix-refl; tagged-lane; tagged-mark; values; values-mono)
open import adequacy.Placed.Rising using (AtopT; Atopᴹ; module Deferred; Disjoint; atop-weaken; every-zip; everyT-flip; everyT-zip; prefix-split)
open import adequacy.Placed.Trail using (Apart; Atopᴴ; Behind; FlatT; Lead; Marks; Parted; SortedT; Sp; Spread; Trail; TrailE; Trailing; ahead-atop; all-pick; all-zip; atop-just; atop-nothing; atopT-every; atopT-∪; atopᴴ; atopᴴ-nothing; behind-at; behind-atop; beyond-atop; beyond-just; beyond-step; beyond-still; cuts-every; disjoint-swap; earliest-picks; every-∀; everyT-all; everyT-∀; flatT-idle; flatT-∪; lead-hush; lead-of; marks-between; marks-past; parted-pick; past-beyond; pool-step; self-atop; shown; sortedT-idle; sortedT-∪; sortedᵀ; spread; trail; trail-≈; trailᶠ)
open import adequacy.Placed.Calm using (At; Calm; Clean; Here; Next; Obl; PoolAt; calms; clean-of; laneAt-map; next-go; pool-apart; poolAt-map; poolAt-∪; sp-apart; sp-step; sp-under)
open import adequacy.Placed.FlatOrder using (module FlatOrder)

open Events∞
open Tail∞

module FlatAfter (p : Pos) where
  open FlatOrder p

  -- AFTER AN OUTER VALUE'S STEP JUST PAST `q`, NOTHING SHOWS INSIDE
  -- THAT STEP: not the lane it admits, the lanes it keeps, what it drops.
  calm-admit : ∀ {B} op (e : Events∞ (MonotonicList B)) (ls : List (Events∞ B)) qs t q m (w : Events∞ (MonotonicList B)) {rs ls′ qs′ d} → M′.admit op (q ++ [ ix 1 ]) m ls qs ≡ (ls′ , qs′ , d)
             → Roots ls rs → Parted rs → All (λ r → Every (D r) (out q m w) × EveryT (D r) (cut e)) rs → All Gen qs
             → Outer (out q m w) (cut e) → PoolF (FreeC (out q m w) (cut e)) rs t
             → Lead (out q m w) ls → Atopᴴ (out q m w) t
             → Obl false (q ++ [ ix 0 ]) (just w) ls′ qs′ (t ∪ d)
  calm-admit (M′.mergeᶠ nothing) e ls qs t q m w refl R pt asd gq h (st , et , wd) ld at =
    admitted q m qs (proj₁ (every (Outer.kx h))) (proj₁ (values (Outer.spn h))) ∷ᴬ kept-lanes q qs (proj₁ (every (Outer.kx h))) R (mapᴬ (λ a → proj₁ (every (proj₁ a))) asd) ld , step-outer h , poolAt-∪ (Clean false (q ++ [ ix 0 ])) t idle (step-pool q m w t at et) tt
  calm-admit (M′.mergeᶠ (just n)) e ls qs t q m w eq R pt asd gq h (st , et , wd) ld at with length ls <ᵇ n
  calm-admit (M′.mergeᶠ (just n)) e ls qs t q m w refl R pt asd gq h (st , et , wd) ld at | true =
    admitted q m qs (proj₁ (every (Outer.kx h))) (proj₁ (values (Outer.spn h))) ∷ᴬ kept-lanes q qs (proj₁ (every (Outer.kx h))) R (mapᴬ (λ a → proj₁ (every (proj₁ a))) asd) ld , step-outer h , poolAt-∪ (Clean false (q ++ [ ix 0 ])) t idle (step-pool q m w t at et) tt
  calm-admit (M′.mergeᶠ (just n)) e ls qs t q m w refl R pt asd gq h (st , et , wd) ld at | false =
    kept-lanes q (qs ++ [ m ]) (proj₁ (every (Outer.kx h))) R (mapᴬ (λ a → proj₁ (every (proj₁ a))) asd) ld , step-outer h , poolAt-∪ (Clean false (q ++ [ ix 0 ])) t idle (step-pool q m w t at et) tt
  calm-admit M′.switchᶠ e ls qs t q m w refl R pt asd gq h (st , et , wd) ld at =
    admitted q m qs (proj₁ (every (Outer.kx h))) (proj₁ (values (Outer.spn h))) ∷ᴬ []ᴬ , step-outer h
    , poolAt-∪ (Clean false (q ++ [ ix 0 ])) t (M′.cuts ls) (step-pool q m w t at et) (drops-clean q ls (proj₁ (every (Outer.kx h))) R (mapᴬ (λ a → proj₁ (every (proj₁ a))) asd) ld)
  calm-admit M′.exhaustᶠ e [] qs t q m w refl []ᴿ pt asd gq h (st , et , wd) ld at =
    admitted q m qs (proj₁ (every (Outer.kx h))) (proj₁ (values (Outer.spn h))) ∷ᴬ []ᴬ , step-outer h , poolAt-∪ (Clean false (q ++ [ ix 0 ])) t idle (step-pool q m w t at et) tt
  calm-admit M′.exhaustᶠ e (l ∷ ls) qs t q m w refl R pt asd gq h (st , et , wd) ld at =
    kept-lanes q qs (proj₁ (every (Outer.kx h))) R (mapᴬ (λ a → proj₁ (every (proj₁ a))) asd) ld , step-outer h , poolAt-∪ (Clean false (q ++ [ ix 0 ])) t idle (step-pool q m w t at et) tt

  -- AFTER AN OUTER SKIP AT `q`, NOTHING SHOWS INSIDE IT.
  calm-oskip : ∀ {B} (e : Events∞ (MonotonicList B)) (ls : List (Events∞ B)) qs t q (w : Events∞ (MonotonicList B)) {rs}
             → Roots ls rs → Parted rs → All (λ r → Every (D r) (skip q w) × EveryT (D r) (cut e)) rs
             → Outer (skip q w) (cut e) → PoolF (FreeC (skip q w) (cut e)) rs t
             → Lead (skip q w) ls → Atopᴴ (skip q w) t
             → Obl false q (just w) ls qs t
  calm-oskip e ls qs t q w R pt asd h (st , et , wd) ld at =
    mapᴬ (λ {l} → laneAt-map (λ v h′ → clean-of false v) qs (force l)) (lead-aloof q qs kq R (mapᴬ (λ a → proj₁ (every (proj₁ a))) asd) ld)
    , outer-clear q (force w) (proj₁ (steady (Outer.std h)))
    , poolAt-map (λ v h′ → clean-of false v) t
        (pool-apart q q t (inj₁ (prefix-refl q)) at (everyT-mono (λ k af → proj₁ (proj₂ (proj₁ (every (proj₁ (proj₂ af)))))) t et))
    where kq = proj₁ (every (Outer.kx h))

  -- AFTER THE OUTER'S END AT `c`, NOTHING SHOWS INSIDE IT.
  calm-oend : ∀ {B} (e : Events∞ (MonotonicList B)) (ls : List (Events∞ B)) qs t c {rs}
            → Roots ls rs → Parted rs → All (λ r → Every {MonotonicList B} (D r) (end c) × EveryT (D r) (cut e)) rs
            → Outer {B} (end c) (cut e) → PoolF (FreeC {MonotonicList B} (end c) (cut e)) rs t
            → Lead {MonotonicList B} (end c) ls → Atopᴴ {MonotonicList B} (end c) t
            → Obl {B} false c nothing ls qs (t ∪ cut e)
  calm-oend {B} e ls qs t c R pt asd h (st , et , wd) ld at =
    mapᴬ (λ {l} → laneAt-map (λ v h′ → clean-of false v) qs (force l)) (lead-aloof c qs (every (Outer.kx h)) R (mapᴬ (λ a → every (proj₁ a)) asd) ld)
    , tt
    , poolAt-∪ (Clean false c) t (cut e)
        (poolAt-map (λ v h′ → clean-of false v) t
          (pool-apart c c t (inj₁ (prefix-refl c)) at (everyT-mono (λ k af → proj₁ (proj₂ (every (proj₁ (proj₂ af))))) t et)))
        (left (cut e) (proj₁ (proj₂ (trail (Outer.trl h)))))
    where
      left : ∀ u → EveryT (TrailE {MonotonicList B} (end c)) u → PoolAt (Clean false c) u
      left (pin k _) e = tt , proj₂ (proj₂ (proj₁ (everyᵀ e)))
      left idle      e = tt

  -- What the merge would leave running, sorted.
  sorted-whole : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) ls t {rs} → Roots ls rs → Heldᴹ o → Pool o rs t → SortedT (M′.whole o ls t)
  sorted-whole nothing  ls t R h pl = sortedT-∪ (M′.cuts ls) t (drops-sorted ls R) (proj₁ pl)
  sorted-whole (just e) ls t R h pl =
    sortedT-∪ (cut e) (M′.cuts ls ∪ t) (proj₁ (trail (Outer.trl h))) (sortedT-∪ (M′.cuts ls) t (drops-sorted ls R) (proj₁ pl))

  -- No earlier than `k`.
  Lag : Pos → Pos → Set
  Lag k h = h <ᵖ k ≡ false

  -- A pin trailing a run whose first is no earlier than `k`, and not
  -- over `k`, is no earlier than `k`.
  lags : ∀ {A} (x : Events A) k h → TrailE x h → Atop k x → ¬ Ext h k → Lag k h
  lags (out n _ _) k h tr        at nx = ≮-trans k n h at (proj₁ tr)
  lags (skip n _)  k h (inj₁ tr) at nx = ≮-trans k n h at tr
  lags (skip n _)  k h (inj₂ m) at nx with h <ᵖ k in hk
  ... | false = refl
  ... | true  with () ← trans (sym (marks-past k m hk nx)) at
  lags (end n)     k h tr        at nx with h <ᵖ k in hk
  ... | false = refl
  ... | true  with () ← trans (sym (<ᵖ-trans n h k (proj₁ tr) hk)) at
  lags hush        k h ()        at nx

  lags-on : ∀ {A} (x : Events A) c k → EveryT (TrailE x) c → Atop k x → EveryT (λ h → ¬ Ext h k) c → EveryT (Lag k) c
  lags-on x c k tr at nx = everyT-mono (λ h a → lags x k h (proj₁ a) at (proj₂ a)) c (everyT-zip c tr nx)

  atopT-lag : ∀ k h u → AtopT h u → Lag k h → AtopT k u
  atopT-lag k h idle       a l = tt
  atopT-lag k h (pin h′ _) a l = ≮-trans k h h′ l a

  -- A sorted tail, its first no earlier than `k`: all of it.
  sorted-lag : ∀ k t → SortedT t → AtopT k t → EveryT (Lag k) t
  everyᵀ (sorted-lag k (pin h u) st a) = a , sorted-lag k (later u) (proj₂ (sortedᵀ st)) (atopT-lag k h (later u) (proj₁ (sortedᵀ st)) a)
  everyᵀ (sorted-lag k idle      st a) = tt

  lag-pin : ∀ k u → SortedT (pin k u) → EveryT (Lag k) (pin k u)
  everyᵀ (lag-pin k u st) = <ᵖ-irrefl k , sorted-lag k (later u) (proj₂ (sortedᵀ st)) (proj₁ (sortedᵀ st))

  -- No earlier than `c`: past the step just under it, or that step's own.
  lag-step : ∀ c h → Lag c h → Lag (c ++ [ ix 0 ]) h ⊎ Marks h (c ++ [ ix 0 ])
  lag-step c h l with <ᵖ-split c h l
  ... | inj₁ ch   = inj₁ (<ᵖ-step c h ch)
  ... | inj₂ refl = inj₂ shown

  owned-ix : ∀ h c i → Owned h (c ++ [ ix i ]) → Owned h c ⊎ h ≡ c ++ [ ix i ]
  owned-ix h c i (inj₁ pr) with prefix-split h c (ix i) pr
  ... | inj₁ q  = inj₁ (inj₁ q)
  ... | inj₂ eq = inj₂ eq
  owned-ix h c i (inj₂ tg) = inj₁ (inj₂ (tagged-lane h c i tg))

  -- A pin no earlier than an end at `c`, apart from `c`, trails it.
  end-trail : ∀ c h → Lag c h → ¬ Owned c h → ¬ Owned h c → c <ᵖ h ≡ true × Disjoint (c ++ [ ix 1 ]) h × ¬ Ext c h
  end-trail c h l nc nh with <ᵖ-split c h l
  ... | inj₂ refl = ⊥-elim (nc (inj₁ (prefix-refl c)))
  ... | inj₁ ch   = ch , ((λ o → nc (owned-trans c (c ++ [ ix 1 ]) h (inj₁ (prefix-++ c [ ix 1 ])) o)) , no) , λ x → nc (owned-ext x)
    where no : ¬ Owned h (c ++ [ ix 1 ])
          no o with owned-ix h c 1 o
          ... | inj₁ hc = nh hc
          ... | inj₂ eq = nc (subst (Owned c) (sym eq) (inj₁ (prefix-++ c [ ix 1 ])))

  apart-ext : ∀ r k → ¬ Owned r k → ∀ h → Owned r h → ¬ Ext h k
  apart-ext r k nr h o x = nr (owned-trans r h k o (owned-ext x))

  aside-ext : ∀ r q → D r q → ∀ h → Owned r h → ¬ Ext h q
  aside-ext r q d h o x = aside-not r q d (owned-trans r h q o (owned-ext x))

  -- Each lane's cut no earlier than `k`, its first being none, and its
  -- root keying nothing over `k`.
  lag-lanes : ∀ {B} k {ls : List (Events∞ B)} {rs} → Roots ls rs → All (λ l → Atop k (force l)) ls
            → All (λ r → ∀ h → Owned r h → ¬ Ext h k) rs → All (λ l → EveryT (Lag k) (cut l)) ls
  lag-lanes k []ᴿ []ᴬ []ᴬ = []ᴬ
  lag-lanes k {l ∷ ls} (st ∷ᴿ R) (a ∷ᴬ as) (n ∷ᴬ ns) =
    lags-on (force l) (cut l) k (proj₁ (proj₂ (trail (Lane.trl st)))) a (everyT-mono (λ h u → n h (proj₁ u)) (cut l) (Lane.kc st))
    ∷ᴬ lag-lanes k R as ns

  lag-whole : ∀ {B} {P : Pos → Set} (o : Maybe (Events∞ (MonotonicList B))) ls t → EveryT P (M′.cutᴼ o) → All (λ l → EveryT P (cut l)) ls
            → EveryT P t → EveryT P (M′.whole o ls t)
  lag-whole o ls t a b c = everyT-∪ (M′.cutᴼ o) (M′.cuts ls ∪ t) a (everyT-∪ (M′.cuts ls) t (cuts-every ls b) c)

  lift-skip : ∀ k c → EveryT (Lag k) c → EveryT (λ h → h <ᵖ k ≡ false ⊎ Marks h k) c
  lift-skip k c = everyT-mono (λ _ → inj₁) c

  -- What a lane's event at `k` leaves aside: the other lanes, the outer
  -- and the pool, each no earlier than `k`.
  lag-rest : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) (bs as : List (Events∞ B)) t k {rbs r ras}
           → Roots bs rbs → Ok r → Roots as ras → Parted (rbs ++ r ∷ ras) → All (Aside o) (rbs ++ r ∷ ras) → Heldᴹ o
           → Pool o (rbs ++ r ∷ ras) t → Under r k → All (λ y → Atop k (force y)) bs → All (λ y → Atop k (force y)) as
           → Atopᴹ k o → AtopT k t
           → All (λ l → EveryT (Lag k) (cut l)) bs × All (λ l → EveryT (Lag k) (cut l)) as × EveryT (Lag k) (M′.cutᴼ o) × EveryT (Lag k) t
  lag-rest o bs as t k {rbs} {r} {ras} rb okr ra pt asd h pl u ab aa ao at =
    lag-lanes k rb ab (mapᴬ (λ {r′} n → apart-ext r′ k n) (All++⁻ˡ rbs nos))
    , lag-lanes k ra aa (mapᴬ (λ {r′} n → apart-ext r′ k n) (All++⁻ʳ rbs nos))
    , by-outer o h ao (proj₁ (all-pick rbs ras asd))
    , sorted-lag k t (proj₁ pl) at
    where
      oks = all-zip (roots-ok (roots-++ rb ra)) (proj₁ (parted-pick rbs r ras pt))
      nos : All (λ r′ → ¬ Owned r′ k) (rbs ++ ras)
      nos = mapᴬ (λ {r′} od → proj₂ (proj₂ u) r′ (proj₁ od) (disjoint-swap r r′ (proj₂ od))) oks
      by-outer : ∀ o → Heldᴹ o → Atopᴹ k o → Aside o r → EveryT (Lag k) (M′.cutᴼ o)
      by-outer nothing  h ao ar = everyT-idle
      by-outer (just e) h ao ar =
        lags-on (force e) (cut e) k (proj₁ (proj₂ (trail (Outer.trl h)))) ao
          (everyT-mono (λ y a x → proj₁ (proj₂ (q-pin r k y okr u (proj₁ a) (proj₂ a))) (owned-ext x)) (cut e) (everyT-zip (cut e) (proj₂ ar) (Outer.kc h)))

  -- What a lane's value at `k` leaves aside, the other lanes, the outer
  -- and the pool, keyed with none of it.
  keyed-rest : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) (bs as : List (Events∞ B)) t k {rbs r ras}
             → Roots bs rbs → Ok r → Roots as ras → Parted (rbs ++ r ∷ ras) → All (Aside o) (rbs ++ r ∷ ras) → Heldᴹ o
             → Pool o (rbs ++ r ∷ ras) t → Under r k
             → All (λ l → EveryT (Disjoint k) (cut l)) bs × All (λ l → EveryT (Disjoint k) (cut l)) as × EveryT (Disjoint k) (M′.cutᴼ o) × EveryT (Disjoint k) t
  keyed-rest o bs as t k {rbs} {r} {ras} rb okr ra pt asd h pl u =
    disjoint-roots r k okr u rb (All++⁻ˡ rbs ds)
    , disjoint-roots r k okr u ra (All++⁻ʳ rbs ds)
    , by-outer o h (proj₁ (all-pick rbs ras asd))
    , everyT-mono (λ b z → disjoint-swap b k (disjoint-under r b k okr (proj₂ (proj₂ z)) (proj₁ (all-pick rbs ras (proj₁ (proj₁ z)))) (proj₁ (all-pick rbs ras (proj₁ (proj₂ z)))) u))
        t (everyT-zip t (proj₁ (proj₂ pl)) (proj₁ (proj₂ (proj₂ pl))))
    where
      ds = proj₁ (parted-pick rbs r ras pt)
      by-outer : ∀ o → Heldᴹ o → Aside o r → EveryT (Disjoint k) (M′.cutᴼ o)
      by-outer nothing  h ar = everyT-idle
      by-outer (just e) h ar =
        everyT-mono (λ y z → disjoint-swap y k (disjoint-under r y k okr (proj₂ z) (aside-not r y (proj₁ z)) (proj₂ (proj₁ z)) u))
          (cut e) (everyT-zip (cut e) (proj₂ ar) (Outer.kc h))

  -- The pool's skip at `k`, ahead of every part.
  lag-pool : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) ls k u {rs} → M′.ahead-of k o ls ≡ true → Roots ls rs
           → Heldᴹ o → Pool o rs (pin k u) → EveryT (Lag k) (M′.whole o ls (pin k u))
  lag-pool o ls k u e R h (st , et , wd) =
    lag-whole o ls (pin k u) (by-outer o h (proj₂ aa) (proj₂ (proj₁ (everyᵀ et))))
      (lag-lanes k R (proj₁ aa) (mapᴬ (λ {r} n → apart-ext r k n) (proj₁ (proj₁ (everyᵀ et))))) (lag-pin k u st)
    where
      aa = ahead-atop k o ls e
      by-outer : ∀ o → Heldᴹ o → Atopᴹ k o → FreeO o k → EveryT (Lag k) (M′.cutᴼ o)
      by-outer nothing  h ao f = everyT-idle
      by-outer (just e) h ao f =
        lags-on (force e) (cut e) k (proj₁ (proj₂ (trail (Outer.trl h)))) ao (everyT-mono (λ y d x → proj₁ (proj₂ d) (owned-ext x)) (cut e) (proj₂ f))

  -- Nothing showing anywhere, nothing left running.
  quiet-one : ∀ {B} (x : Events B) c → M′.head x ≡ nothing → EveryT (TrailE x) c → EveryT (λ _ → ⊥) c
  quiet-one (out _ _ _) c () e
  quiet-one (skip _ _)  c () e
  quiet-one (end _)     c () e
  quiet-one hush        c n  e = e

  quiet-lanes : ∀ {B} {ls : List (Events∞ B)} {rs} → Roots ls rs → All (λ l → M′.head (force l) ≡ nothing) ls → All (λ l → EveryT (λ _ → ⊥) (cut l)) ls
  quiet-lanes []ᴿ []ᴬ = []ᴬ
  quiet-lanes {ls = l ∷ ls} (st ∷ᴿ R) (hl ∷ᴬ hs) = quiet-one (force l) (cut l) hl (proj₁ (proj₂ (trail (Lane.trl st)))) ∷ᴬ quiet-lanes R hs

  quiet-pool : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) ls t → M′.headᴼ o ≡ nothing → All (λ l → M′.head (force l) ≡ nothing) ls
             → Behind o ls t → EveryT (λ _ → ⊥) t
  quiet-pool o ls idle      ho hs bh = everyT-idle
  quiet-pool o ls (pin k u) ho hs bh with () ← trans (sym (ahead-quiet k o ls ho hs)) bh

  mute : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) ls t {rs} → Roots ls rs → M′.headᴼ o ≡ nothing → All (λ l → M′.head (force l) ≡ nothing) ls
       → Behind o ls t → EveryT (λ _ → ⊥) (M′.cuts ls ∪ t)
  mute o ls t R ho hs bh = everyT-∪ (M′.cuts ls) t (cuts-every ls (quiet-lanes R hs)) (quiet-pool o ls t ho hs bh)

  just≢nothing : ∀ {k : Pos} {m : Maybe Pos} → m ≡ just k → m ≡ nothing → ⊥
  just≢nothing refl ()

  -- The outer's event, the earliest: each part's cut lags it.
  trail-outer : ∀ {B} op (e : Events∞ (MonotonicList B)) ls qs t (x : Events (MonotonicList B)) {rs} → Roots ls rs
              → All (λ r → Every (D r) x × EveryT (D r) (cut e)) rs → Outer x (cut e) → PoolF (FreeC x (cut e)) rs t
              → Lead x ls → Atopᴴ x t → (M′.head x ≡ nothing → EveryT (λ _ → ⊥) (M′.cuts ls ∪ t))
              → EveryT (TrailE (M′.outer op e ls qs t x)) (M′.whole (just e) ls t)
  trail-outer op e ls qs t (out q m w) R asd h pl ld at mt with M′.admit op (q ++ [ ix 1 ]) m ls qs
  ... | ls′ , qs′ , d =
    everyT-mono (λ y → lag-step q y) (M′.whole (just e) ls t)
      (lag-whole (just e) ls t (everyT-mono (λ _ x → proj₁ x) (cut e) (proj₁ (proj₂ (trail (Outer.trl h)))))
        (lag-lanes q R (mapᴬ (λ {l} → beyond-atop q (force l)) ld) (mapᴬ (λ {r} a → aside-ext r q (proj₁ (every (proj₁ a)))) asd))
        (sorted-lag q t (proj₁ pl) at))
  trail-outer op e ls qs t (skip q w) R asd h pl ld at mt =
    lag-whole (just e) ls t (proj₁ (proj₂ (trail (Outer.trl h))))
      (mapᴬ (λ {l} → lift-skip q (cut l)) (lag-lanes q R (mapᴬ (λ {l} → beyond-atop q (force l)) ld) (mapᴬ (λ {r} a → aside-ext r q (proj₁ (every (proj₁ a)))) asd)))
      (lift-skip q t (sorted-lag q t (proj₁ pl) at))
  trail-outer op e [] [] t (end c) R asd h pl ld at mt =
    lag-whole (just e) [] t (proj₁ (proj₂ (trail (Outer.trl h)))) []ᴬ
      (everyT-mono (λ y a → end-trail c y (proj₁ a) (proj₁ (proj₂ (every (proj₁ (proj₂ (proj₂ a)))))) (proj₂ (proj₂ (every (proj₁ (proj₂ (proj₂ a)))))))
        t (everyT-zip t (sorted-lag c t (proj₁ pl) at) (proj₁ (proj₂ pl))))
  trail-outer op e [] (m ∷ qs) t (end c) R asd h pl ld at mt =
    lag-whole (just e) [] t (everyT-mono (λ y tr → inj₁ (<ᵖ-asym c y (proj₁ tr))) (cut e) (proj₁ (proj₂ (trail (Outer.trl h))))) []ᴬ
      (lift-skip c t (sorted-lag c t (proj₁ pl) at))
  trail-outer op e (l ∷ ls) qs t (end c) R asd h pl ld at mt =
    lag-whole (just e) (l ∷ ls) t (everyT-mono (λ y tr → inj₁ (<ᵖ-asym c y (proj₁ tr))) (cut e) (proj₁ (proj₂ (trail (Outer.trl h)))))
      (mapᴬ (λ {l} → lift-skip c (cut l)) (lag-lanes c R (mapᴬ (λ {l} → beyond-atop c (force l)) ld) (mapᴬ (λ {r} a → aside-ext r c (every (proj₁ a))) asd)))
      (lift-skip c t (sorted-lag c t (proj₁ pl) at))
  trail-outer op e ls qs t hush R asd h pl ld at mt = everyT-∪ (cut e) (M′.cuts ls ∪ t) (proj₁ (proj₂ (trail (Outer.trl h)))) (mt refl)

  -- A lane's end at `c`: everything left running no earlier than `c`.
  lag-ended : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) bs (l : Events∞ B) as t c {rbs r ras}
            → Roots bs rbs → Lane {B} r (end c) (cut l) → Roots as ras → Parted (rbs ++ r ∷ ras) → All (Aside o) (rbs ++ r ∷ ras)
            → Heldᴹ o → Pool o (rbs ++ r ∷ ras) t → All (λ y → Atop c (force y)) bs → All (λ y → Atop c (force y)) as → Atopᴹ c o → AtopT c t
            → EveryT (Lag c) (M′.whole o (bs ++ l ∷ as) t)
  lag-ended o bs l as t c rb st ra pt asd h pl ab aa ao at =
    lag-whole o (bs ++ l ∷ as) t (proj₁ (proj₂ (proj₂ g)))
      (All++⁺ (proj₁ g) (everyT-mono (λ y tr → <ᵖ-asym c y (proj₁ tr)) (cut l) (proj₁ (proj₂ (trail (Lane.trl st)))) ∷ᴬ proj₁ (proj₂ g)))
      (proj₂ (proj₂ (proj₂ g)))
    where g = lag-rest o bs as t c rb (Lane.ok st) ra pt asd h pl (every (Lane.kx st)) ab aa ao at

  -- A lane's event, the earliest: its own cut trails it, every other
  -- part's lags it.
  trail-lane : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) bs (l : Events∞ B) as qs t (x : Events B) {rbs r ras}
             → Roots bs rbs → Lane r x (cut l) → Roots as ras → Parted (rbs ++ r ∷ ras) → All (Aside o) (rbs ++ r ∷ ras)
             → Heldᴹ o → Pool o (rbs ++ r ∷ ras) t → ∀ {k} → M′.head x ≡ just k → All (λ y → Atop k (force y)) bs
             → All (λ y → Atop k (force y)) as → Atopᴹ k o → AtopT k t
             → EveryT (TrailE (M′.lane op o bs l as qs t x)) (M′.whole o (bs ++ l ∷ as) t)
  trail-lane op o bs l as qs t (out k b w) rb st ra pt asd h pl refl ab aa ao at =
    everyT-zip (M′.whole o (bs ++ l ∷ as) t)
      (lag-whole o (bs ++ l ∷ as) t (proj₁ (proj₂ (proj₂ g))) (All++⁺ (proj₁ g) (everyT-mono (λ _ x → proj₁ x) (cut l) own ∷ᴬ proj₁ (proj₂ g))) (proj₂ (proj₂ (proj₂ g))))
      (lag-whole o (bs ++ l ∷ as) t (proj₁ (proj₂ (proj₂ d))) (All++⁺ (proj₁ d) (everyT-mono (λ _ x → proj₂ x) (cut l) own ∷ᴬ proj₁ (proj₂ d))) (proj₂ (proj₂ (proj₂ d))))
    where g = lag-rest o bs as t k rb (Lane.ok st) ra pt asd h pl (proj₁ (every (Lane.kx st))) ab aa ao at
          d = keyed-rest o bs as t k rb (Lane.ok st) ra pt asd h pl (proj₁ (every (Lane.kx st)))
          own = proj₁ (proj₂ (trail (Lane.trl st)))
  trail-lane op o bs l as qs t (skip k w) rb st ra pt asd h pl refl ab aa ao at =
    lag-whole o (bs ++ l ∷ as) t (lift-skip k _ (proj₁ (proj₂ (proj₂ g))))
      (All++⁺ (mapᴬ (λ {y} → lift-skip k (cut y)) (proj₁ g)) (proj₁ (proj₂ (trail (Lane.trl st))) ∷ᴬ mapᴬ (λ {y} → lift-skip k (cut y)) (proj₁ (proj₂ g))))
      (lift-skip k t (proj₂ (proj₂ (proj₂ g))))
    where g = lag-rest o bs as t k rb (Lane.ok st) ra pt asd h pl (proj₁ (every (Lane.kx st))) ab aa ao at
  trail-lane op o bs l as (m ∷ qs) t (end c) rb st ra pt asd h pl refl ab aa ao at =
    everyT-mono (λ y → lag-step c y) (M′.whole o (bs ++ l ∷ as) t) (lag-ended o bs l as t c rb st ra pt asd h pl ab aa ao at)
  trail-lane op nothing [] l [] [] t (end c) {r = r} []ᴿ st []ᴿ pt asd h (sp , ep , wp , fp) refl ab aa ao at =
    lag-whole nothing (l ∷ []) t everyT-idle (proj₁ (proj₂ (trail (Lane.trl st))) ∷ᴬ []ᴬ)
      (everyT-mono (λ y a → end-trail c y (proj₁ (proj₁ a)) (nc y (proj₂ (proj₁ a))) (nh y (proj₂ (proj₁ a)) (proj₂ a))) t
        (everyT-zip t (everyT-zip t (sorted-lag c t sp at) ep) wp))
    where
      u = every (Lane.kx st)
      one : ∀ {P : Pos → Set} {y} → All P (y ∷ []) → P y
      one (a ∷ᴬ []ᴬ) = a
      nc : ∀ y → All (λ r → ¬ Owned r y) (r ∷ []) × ⊤ → ¬ Owned c y
      nc y a o = one (proj₁ a) (owned-trans r c y (proj₁ u) o)
      nh : ∀ y → All (λ r → ¬ Owned r y) (r ∷ []) × ⊤ → All (λ r → ¬ Owned y r) (r ∷ []) × K y → ¬ Owned y c
      nh y a w = proj₂ (proj₂ u) y (ok-apart y r (proj₂ w) (Lane.ok st) (one (proj₁ w))) (one (proj₁ w) , one (proj₁ a))
  trail-lane op nothing [] l (a ∷ as) [] t (end c) rb st ra pt asd h pl refl ab aa ao at =
    lift-skip c _ (lag-ended nothing [] l (a ∷ as) t c rb st ra pt asd h pl ab aa ao at)
  trail-lane op nothing (b ∷ bs) l as [] t (end c) rb st ra pt asd h pl refl ab aa ao at =
    lift-skip c _ (lag-ended nothing (b ∷ bs) l as t c rb st ra pt asd h pl ab aa ao at)
  trail-lane op (just e) bs l as [] t (end c) rb st ra pt asd h pl refl ab aa ao at =
    lift-skip c _ (lag-ended (just e) bs l as t c rb st ra pt asd h pl ab aa ao at)
  trail-lane op o bs l as qs t hush rb st ra pt asd h pl () ab aa ao at

  trail-race : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) k bs (l : Events∞ B) as qs t {rbs r ras}
             → Roots bs rbs → Static r l → Roots as ras → Parted (rbs ++ r ∷ ras) → All (Aside o) (rbs ++ r ∷ ras)
             → Heldᴹ o → Pool o (rbs ++ r ∷ ras) t → Behind o (bs ++ l ∷ as) t → M′.head (force l) ≡ just k
             → All (λ x → Atop k (force x)) bs → All (λ x → Atop k (force x)) as
             → EveryT (TrailE (M′.race op o k bs l as qs t)) (M′.whole o (bs ++ l ∷ as) t)
  trail-race op nothing  k bs l as qs t rb st ra pt asd h pl bh hk ab aa =
    trail-lane op nothing bs l as qs t (force l) rb st ra pt asd h pl hk ab aa tt
      (behind-atop k nothing (bs ++ l ∷ as) t bh (All++⁺ ab (self-atop (force l) hk ∷ᴬ aa)) tt)
  trail-race op (just e) k bs l as qs t rb st ra pt asd h pl bh hk ab aa with M′.head (force e) in he
  ... | nothing = trail-lane op (just e) bs l as qs t (force l) rb st ra pt asd h pl hk ab aa (atop-nothing k (force e) he)
                    (behind-atop k (just e) (bs ++ l ∷ as) t bh (All++⁺ ab (self-atop (force l) hk ∷ᴬ aa)) (atop-nothing k (force e) he))
  ... | just k′ with k′ <ᵖ k in kk
  ...   | true  = trail-outer op e (bs ++ l ∷ as) qs t (force e) (roots-++ rb (st ∷ᴿ ra)) asd h pl
                    (lead-of (force e) (bs ++ l ∷ as) he
                      (All++⁺ (mapᴬ (λ {x} → beyond-still k′ k (force x) kk) ab)
                              (beyond-just k′ (force l) hk kk ∷ᴬ mapᴬ (λ {x} → beyond-still k′ k (force x) kk) aa)))
                    (atopᴴ (force e) t he
                      (behind-atop k′ (just e) (bs ++ l ∷ as) t bh
                        (mapᴬ (λ {x} → atop-weaken k k′ (force x) (<ᵖ-asym k′ k kk)) (All++⁺ ab (self-atop (force l) hk ∷ᴬ aa)))
                        (self-atop (force e) he)))
                    (λ n → ⊥-elim (just≢nothing he n))
  ...   | false = trail-lane op (just e) bs l as qs t (force l) rb st ra pt asd h pl hk ab aa (atop-just (force e) he kk)
                    (behind-atop k (just e) (bs ++ l ∷ as) t bh (All++⁺ ab (self-atop (force l) hk ∷ᴬ aa)) (atop-just (force e) he kk))

  trail-via : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t {rs} → Roots ls rs → All (Aside o) rs
            → Heldᴹ o → Pool o rs t → Behind o ls t → All (λ l → M′.head (force l) ≡ nothing) ls
            → EveryT (TrailE (M′.viaOuter op o ls qs t)) (M′.whole o ls t)
  trail-via op nothing  ls qs t R asd h pl bh hs = mute nothing ls t R refl hs bh
  trail-via op (just e) ls qs t R asd h pl bh hs with M′.head (force e) in he
  ... | nothing = trail-outer op e ls qs t (force e) R asd h pl (lead-hush (force e) ls hs) (atopᴴ-nothing (force e) t he)
                    (λ _ → mute (just e) ls t R he hs bh)
  ... | just k  = trail-outer op e ls qs t (force e) R asd h pl (lead-hush (force e) ls hs)
                    (atopᴴ (force e) t he (behind-atop k (just e) ls t bh (mapᴬ (λ {l} → atop-nothing k (force l)) hs) (self-atop (force e) he)))
                    (λ n → ⊥-elim (just≢nothing he n))

  trail-parts : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t {rs} → Roots ls rs → Parted rs → All (Aside o) rs
              → Heldᴹ o → Pool o rs t → Behind o ls t → EveryT (TrailE (M′.parts op o ls qs t)) (M′.whole o ls t)
  trail-parts op o ls qs t R pt asd h pl bh with M′.earliest ls | earliest-picks ls
  ... | none            | hs                  = trail-via op o ls qs t R asd h pl bh hs
  ... | found k bs l as | (eq , hk , ab , aa) with roots-at bs l as eq R
  ...   | split rb st ra =
    subst (λ ls → EveryT (TrailE (M′.race op o k bs l as qs t)) (M′.whole o ls t)) (sym eq)
      (trail-race op o k bs l as qs t rb st ra pt asd h pl (behind-at o t eq bh) hk ab aa)

  -- WHAT THE MERGE WOULD LEAVE RUNNING TRAILS WHAT IT SHOWS NEXT: the
  -- outer's cut, every lane's and what ended parts left, against the
  -- earliest part's next or the pool's skip ahead of them all.
  trail-whole : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t {rs} → Roots ls rs → Parted rs → All (Aside o) rs
              → Heldᴹ o → Pool o rs t → EveryT (TrailE (M′.go op o ls qs t)) (M′.whole o ls t)
  trail-whole op o ls qs idle      R pt asd h pl = trail-parts op o ls qs idle R pt asd h pl tt
  trail-whole op o ls qs (pin k u) R pt asd h pl with M′.ahead-of k o ls in e
  ... | true  = lift-skip k (M′.whole o ls (pin k u)) (lag-pool o ls k u e R h pl)
  ... | false = trail-parts op o ls qs (pin k u) R pt asd h pl e

  -- What the dropped lanes and the pool leave running side by side.
  flat-rest : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) (ls : List (Events∞ B)) t {rs} → Roots ls rs → Parted rs → Pool o rs t → FlatT (M′.cuts ls ∪ t)
  flat-rest o ls t R pt pl =
    flatT-∪ (M′.cuts ls) t (drops-flat ls R pt) (proj₂ (proj₂ (proj₂ pl)))
      (everyT-mono (λ a z → everyT-mono (λ b ab → proj₂ ab , proj₁ ab) t z) (M′.cuts ls)
        (everyT-flip t (M′.cuts ls)
          (everyT-mono (λ b z → cuts-every ls (drops-apart b ls R (proj₂ (proj₂ z)) (proj₁ (proj₁ z)) (proj₁ (proj₂ z))))
            t (everyT-zip t (proj₁ (proj₂ pl)) (proj₁ (proj₂ (proj₂ pl)))))))

  -- WHAT THE MERGE WOULD LEAVE RUNNING IS FLAT: no step of the outer's
  -- cut, a lane's or the pool's inside a step of another's.
  flat-whole : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) ls t {rs} → Roots ls rs → Parted rs → All (Aside o) rs
             → Heldᴹ o → Pool o rs t → FlatT (M′.whole o ls t)
  flat-whole nothing  ls t R pt asd h pl = flatT-∪ idle (M′.cuts ls ∪ t) flatT-idle (flat-rest nothing ls t R pt pl) everyT-idle
  flat-whole (just e) ls t {rs} R pt asd h pl =
    flatT-∪ (cut e) (M′.cuts ls ∪ t) (trailᶠ (Outer.trl h)) (flat-rest (just e) ls t R pt pl)
      (everyT-mono (λ y z → everyT-∪ (M′.cuts ls) t
                     (cuts-every ls (drops-apart y ls R (proj₁ (proj₁ z)) (mapᴬ (λ {r} d → aside-not r y d) (proj₂ (proj₁ z))) (mapᴬ (λ {r} d → proj₂ d) (proj₂ (proj₁ z)))))
                     (proj₂ z))
        (cut e) (everyT-zip (cut e) (everyT-zip (cut e) (Outer.kc h) (everyT-all rs (cut e) (mapᴬ (λ {r} a → proj₂ a) asd))) op))
    where
      op : EveryT (λ y → EveryT (Apart y) t) (cut e)
      op = everyT-flip t (cut e)
             (everyT-mono (λ b af → everyT-mono (λ y fy → (λ x → proj₁ (proj₂ fy) (owned-ext x)) , (λ x → proj₂ (proj₂ fy) (owned-ext x))) (cut e) (proj₂ (proj₂ af)))
               t (proj₁ (proj₂ pl)))

  mutual
    calm-at : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t {rs} → Roots ls rs → Parted rs → All (Aside o) rs → All Gen qs
               → Heldᴹ o → Pool o rs t → Here (M′.go op o ls qs t) (M′.whole o ls t) × Calm (M′.go op o ls qs t)
    calm-at op o ls qs t R pt asd gq h pl =
      (sorted-whole o ls t R h pl , trail-whole op o ls qs t R pt asd h pl , flat-whole o ls t R pt asd h pl) , calm-go op o ls qs t R pt asd gq h pl

    calm-go : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t {rs} → Roots ls rs → Parted rs → All (Aside o) rs → All Gen qs
               → Heldᴹ o → Pool o rs t → Calm (M′.go op o ls qs t)
    calm-go op o ls qs idle      R pt asd gq h pl = calm-parts op o ls qs idle R pt asd gq h pl tt
    calm-go op o ls qs (pin k u) R pt asd gq h pl with M′.ahead-of k o ls in e
    ... | true  = calm-pool op o ls qs k u e R pt asd gq h pl
    ... | false = calm-parts op o ls qs (pin k u) R pt asd gq h pl e

    calm-pool : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs k u {rs} → M′.ahead-of k o ls ≡ true → Roots ls rs → Parted rs
                 → All (Aside o) rs → All Gen qs → Heldᴹ o → Pool o rs (pin k u) → Calm (M′.left op o ls qs k u true)
    calms (calm-pool op o ls qs k u {rs} e R pt asd gq h pl) =
      next-go false k op o ls qs (later u) (proj₁ (ahead-atop k o ls e)) (proj₂ (ahead-atop k o ls e)) (proj₁ (sortedᵀ (proj₁ pl)))
        (calm-pool-n o ls qs k u e R pt asd h pl)
      , calm-at op o ls qs (later u) R pt asd gq h (pool-later o rs k u pl)

    calm-parts : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t {rs} → Roots ls rs → Parted rs → All (Aside o) rs → All Gen qs
                  → Heldᴹ o → Pool o rs t → Behind o ls t → Calm (M′.parts op o ls qs t)
    calm-parts op o ls qs t R pt asd gq h pl bh with M′.earliest ls | earliest-picks ls
    ... | none            | hs                  = calm-via op o ls qs t R pt asd gq h pl bh hs
    ... | found k bs l as | (eq , hk , ab , aa) with roots-at bs l as eq R
    ...   | split rb st ra = calm-race op o k bs l as qs t rb st ra pt asd gq h pl (behind-at o t eq bh) hk ab aa

    calm-via : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t {rs} → Roots ls rs → Parted rs → All (Aside o) rs → All Gen qs
                → Heldᴹ o → Pool o rs t → Behind o ls t → All (λ l → M′.head (force l) ≡ nothing) ls → Calm (M′.viaOuter op o ls qs t)
    calm-via op nothing  ls qs t R pt asd gq h pl bh hs = record { calms = tt }
    calm-via op (just e) ls qs t R pt asd gq h pl bh hs with M′.head (force e) in he
    ... | nothing = calm-outer op e ls qs t (force e) R pt asd gq h pl (lead-hush (force e) ls hs) (atopᴴ-nothing (force e) t he)
    ... | just k  = calm-outer op e ls qs t (force e) R pt asd gq h pl (lead-hush (force e) ls hs)
                      (atopᴴ (force e) t he (behind-atop k (just e) ls t bh (mapᴬ (λ {l} → atop-nothing k (force l)) hs) (self-atop (force e) he)))

    calm-race : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) k bs (l : Events∞ B) as qs t {rbs r ras}
                 → Roots bs rbs → Static r l → Roots as ras → Parted (rbs ++ r ∷ ras) → All (Aside o) (rbs ++ r ∷ ras) → All Gen qs
                 → Heldᴹ o → Pool o (rbs ++ r ∷ ras) t → Behind o (bs ++ l ∷ as) t → M′.head (force l) ≡ just k
                 → All (λ x → Atop k (force x)) bs → All (λ x → Atop k (force x)) as → Calm (M′.race op o k bs l as qs t)
    calm-race op nothing  k bs l as qs t rb st ra pt asd gq h pl bh hk ab aa =
      calm-lane op nothing bs l as qs t (force l) rb st ra pt asd gq h pl hk ab aa tt
        (behind-atop k nothing (bs ++ l ∷ as) t bh (All++⁺ ab (self-atop (force l) hk ∷ᴬ aa)) tt)
    calm-race op (just e) k bs l as qs t rb st ra pt asd gq h pl bh hk ab aa with M′.head (force e) in he
    ... | nothing = calm-lane op (just e) bs l as qs t (force l) rb st ra pt asd gq h pl hk ab aa (atop-nothing k (force e) he)
                      (behind-atop k (just e) (bs ++ l ∷ as) t bh (All++⁺ ab (self-atop (force l) hk ∷ᴬ aa)) (atop-nothing k (force e) he))
    ... | just k′ with k′ <ᵖ k in kk
    ...   | true  = calm-outer op e (bs ++ l ∷ as) qs t (force e) (roots-++ rb (st ∷ᴿ ra)) pt asd gq h pl
                      (lead-of (force e) (bs ++ l ∷ as) he
                        (All++⁺ (mapᴬ (λ {x} → beyond-still k′ k (force x) kk) ab)
                                (beyond-just k′ (force l) hk kk ∷ᴬ mapᴬ (λ {x} → beyond-still k′ k (force x) kk) aa)))
                      (atopᴴ (force e) t he
                        (behind-atop k′ (just e) (bs ++ l ∷ as) t bh
                          (mapᴬ (λ {x} → atop-weaken k k′ (force x) (<ᵖ-asym k′ k kk)) (All++⁺ ab (self-atop (force l) hk ∷ᴬ aa)))
                          (self-atop (force e) he)))
    ...   | false = calm-lane op (just e) bs l as qs t (force l) rb st ra pt asd gq h pl hk ab aa (atop-just (force e) he kk)
                      (behind-atop k (just e) (bs ++ l ∷ as) t bh (All++⁺ ab (self-atop (force l) hk ∷ᴬ aa)) (atop-just (force e) he kk))

    calm-outer : ∀ {B} op (e : Events∞ (MonotonicList B)) ls qs t (x : Events (MonotonicList B)) {rs} → Roots ls rs → Parted rs
                  → All (λ r → Every (D r) x × EveryT (D r) (cut e)) rs → All Gen qs → Outer x (cut e)
                  → PoolF (FreeC x (cut e)) rs t → Lead x ls → Atopᴴ x t
                  → Calm (M′.outer op e ls qs t x)
    calms (calm-outer op e ls qs t (out q m w) R pt asd gq h pl ld at)
      with M′.admit op (q ++ [ ix 1 ]) m ls qs in eq
         | admit-ok op q m w t ls qs R pt (mapᴬ proj₁ asd) gq (proj₁ (values (Outer.spn h))) (lane-ok q (proj₁ (every (Outer.kx h))))
             (proj₁ (spread (Outer.spr h))) ld (proj₂ (every (Outer.kx h))) pl
    ... | ls′ , qs′ , d | taken R′ pt′ asd′ at′ gq′ pl′ ad =
      next-go false (q ++ [ ix 0 ]) op (just w) ls′ qs′ (t ∪ d) at′ (beyond-step q (force w) (past-beyond q (force w) (proj₁ (steady (Outer.std h)))))
        (atopT-∪ (q ++ [ ix 0 ]) t d (pool-step q t at (everyT-mono (λ k af eq → proj₁ (proj₂ (proj₁ (every (proj₁ (proj₂ af))))) (subst (Owned q) eq (inj₁ (prefix-refl q)))) t (proj₁ (proj₂ pl)))) ad)
        (calm-admit op e ls qs t q m w eq R pt asd gq h pl ld at)
      , calm-at op (just w) ls′ qs′ (t ∪ d) R′ pt′ asd′ gq′ (outer-out h) pl′
    calms (calm-outer op e ls qs t (skip q w) {rs} R pt asd gq h pl ld at) =
      next-go false q op (just w) ls qs t (mapᴬ (λ {l} → beyond-atop q (force l)) ld) (proj₁ (ordered (Outer.ord h))) at
        (calm-oskip e ls qs t q w R pt asd h pl ld at)
      , calm-at op (just w) ls qs t R pt (mapᴬ (λ a → proj₂ (every (proj₁ a))) asd) gq (outer-skip h)
          (pool-oskip q w (cut e) t rs pl)
    calms (calm-outer op e [] [] t (end c) R pt asd gq h pl ld at) = tt
    calms (calm-outer op e [] (m ∷ qs) t (end c) []ᴿ pt asd gq h pl ld at) =
      next-go false c op nothing [] (m ∷ qs) (t ∪ cut e) []ᴬ tt (outer-end-atop c e t h at) (calm-oend e [] (m ∷ qs) t c []ᴿ pt asd h pl ld at)
      , calm-at op nothing [] (m ∷ qs) (t ∪ cut e) []ᴿ tt []ᴬ gq tt (outer-end-pool c e t [] h asd pl)
    calms (calm-outer {B} op e (l ∷ ls) qs t (end c) {rs} R pt asd gq h pl ld at) =
      next-go false c op nothing (l ∷ ls) qs (t ∪ cut e) (mapᴬ (λ {x} → beyond-atop c (force x)) ld) tt (outer-end-atop c e t h at)
        (calm-oend e (l ∷ ls) qs t c R pt asd h pl ld at)
      , calm-at op nothing (l ∷ ls) qs (t ∪ cut e) R pt (aside-none {B} rs) gq tt (outer-end-pool c e t rs h asd pl)
    calms (calm-outer op e ls qs t hush R pt asd gq h pl ld at) = tt

    calm-lane : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) bs (l : Events∞ B) as qs t (x : Events B) {rbs r ras}
                 → Roots bs rbs → Lane r x (cut l) → Roots as ras → Parted (rbs ++ r ∷ ras) → All (Aside o) (rbs ++ r ∷ ras) → All Gen qs
                 → Heldᴹ o → Pool o (rbs ++ r ∷ ras) t → ∀ {k} → M′.head x ≡ just k → All (λ y → Atop k (force y)) bs
                 → All (λ y → Atop k (force y)) as → Atopᴹ k o → AtopT k t → Calm (M′.lane op o bs l as qs t x)
    calms (calm-lane op o bs l as qs t (out k b w) rb st ra pt asd gq h pl refl ab aa ao at) =
      lag-whole o (bs ++ w ∷ as) t (proj₁ (proj₂ (proj₂ d))) (All++⁺ (proj₁ d) (proj₂ (proj₂ (proj₂ (trail (Lane.trl st)))) ∷ᴬ proj₁ (proj₂ d))) (proj₂ (proj₂ (proj₂ d)))
      , next-go true k op o (bs ++ w ∷ as) qs t (All++⁺ ab (proj₁ (ordered (Lane.ord st)) ∷ᴬ aa)) ao at (calm-out o bs l as qs t k b w rb st ra pt asd h pl ab aa ao at)
      , calm-at op o (bs ++ w ∷ as) qs t (roots-++ rb (lane-out st ∷ᴿ ra)) pt asd gq h pl
      where d = keyed-rest o bs as t k rb (Lane.ok st) ra pt asd h pl (proj₁ (every (Lane.kx st)))
    calms (calm-lane op o bs l as qs t (skip k w) rb st ra pt asd gq h pl refl ab aa ao at) =
      next-go false k op o (bs ++ w ∷ as) qs t (All++⁺ ab (proj₁ (ordered (Lane.ord st)) ∷ᴬ aa)) ao at (calm-skip o bs l as qs t k w rb st ra pt asd h pl ab aa ao at)
      , calm-at op o (bs ++ w ∷ as) qs t (roots-++ rb (lane-skip st ∷ᴿ ra)) pt asd gq h pl
    calms (calm-lane op o bs l as (m ∷ qs) t (end c) {rbs} {r} {ras} rb st ra pt asd (gm ∷ᴬ gq) h pl refl ab aa ao at) =
      next-go false c₀ op o (M′.enter m c₁ ∷ bs ++ as) qs (t ∪ cut l)
        (top ∷ᴬ clear-lanes r c (Lane.ok st) orc (roots-++ rb ra) (proj₁ pp) (All++⁺ ab aa))
        (atop-hand r c o orc ao ar)
        (atopT-∪ c₀ t (cut l)
           (pool-step c t at (everyT-mono (λ k af eq → proj₁ (all-pick rbs ras (proj₁ af)) (subst (Owned r) eq orc)) t (proj₁ (proj₂ pl))))
           (atopT-every c₀ (cut l) (λ k tr → <ᵖ-step c k (proj₁ tr)) (proj₁ (proj₂ (trail (Lane.trl st))))))
        (calm-queue o bs l as m qs t c rb st ra pt asd gm h pl ab aa ao at)
      , calm-at op o (M′.enter m c₁ ∷ bs ++ as) qs (t ∪ cut l) (fresh c₁ (M′.enter m c₁) fit okc ∷ᴿ roots-++ rb ra)
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
    calms (calm-lane op nothing [] l [] [] t (end c) rb st ra pt asd gq h pl refl ab aa ao at) = tt
    calms (calm-lane op nothing [] l (a ∷ as) [] t (end c) rb st ra pt asd gq h pl refl ab aa ao at) =
      calm-ended op nothing [] l (a ∷ as) t c rb st ra pt asd h pl ab aa ao at
    calms (calm-lane op nothing (b ∷ bs) l as [] t (end c) rb st ra pt asd gq h pl refl ab aa ao at) =
      calm-ended op nothing (b ∷ bs) l as t c rb st ra pt asd h pl ab aa ao at
    calms (calm-lane op (just e) bs l as [] t (end c) rb st ra pt asd gq h pl refl ab aa ao at) =
      calm-ended op (just e) bs l as t c rb st ra pt asd h pl ab aa ao at
    calms (calm-lane op o bs l as qs t hush rb st ra pt asd gq h pl () ab aa ao at)

    calm-ended : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) bs (l : Events∞ B) as t c {rbs r ras}
               → Roots bs rbs → Lane {B} r (end c) (cut l) → Roots as ras → Parted (rbs ++ r ∷ ras) → All (Aside o) (rbs ++ r ∷ ras)
               → Heldᴹ o → Pool o (rbs ++ r ∷ ras) t → All (λ y → Atop c (force y)) bs → All (λ y → Atop c (force y)) as → Atopᴹ c o → AtopT c t
               → At (Next false c) (M′.go op o (bs ++ as) [] (t ∪ cut l)) × Here (M′.go op o (bs ++ as) [] (t ∪ cut l)) (M′.whole o (bs ++ as) (t ∪ cut l))
                 × Calm (M′.go op o (bs ++ as) [] (t ∪ cut l))
    calm-ended op o bs l as t c {rbs} {r} {ras} rb st ra pt asd h pl ab aa ao at =
      next-go false c op o (bs ++ as) [] (t ∪ cut l) (All++⁺ ab aa) ao
        (atopT-∪ c t (cut l) at (atopT-every c (cut l) (λ k tr → <ᵖ-asym c k (proj₁ tr)) (proj₁ (proj₂ (trail (Lane.trl st))))))
        (calm-end o bs l as t c rb st ra pt asd h pl ab aa ao at)
      , calm-at op o (bs ++ as) [] (t ∪ cut l) (roots-++ rb ra) (proj₂ pp) (proj₂ (all-pick rbs ras asd)) []ᴬ h
          (pool-ended o rbs r ras t (cut l) st oks (proj₁ (all-pick rbs ras asd)) h pl)
      where
        pp  = parted-pick rbs r ras pt
        oks = all-zip (roots-ok (roots-++ rb ra)) (proj₁ pp)

  -- Every step of a lane subscribed at `j`, keyed under it, headed, and
  -- keyed by nothing apart from it a lane may subscribe at.
  under∞ : ∀ {A} j (r : Events∞ A) → Every∞ (Owned j) r → Every∞ Headed r → (∀ R → Ok R → Disjoint R j → Every∞ (λ h → ¬ Owned R h) r)
         → Every∞ (Under j) r
  under∞ j r ow hh ap =
    every-mono pack (force r) (every-zip (force r) (every-zip (force r) (proj₁ ow) (proj₁ hh))
                                 (every-∀ {P = λ i h → ¬ Owned (proj₁ i) h} (force r) (λ i → proj₁ (ap (proj₁ i) (proj₁ (proj₂ i)) (proj₂ (proj₂ i))))))
    , everyT-mono pack (cut r) (everyT-zip (cut r) (everyT-zip (cut r) (proj₂ ow) (proj₂ hh))
                                  (everyT-∀ {P = λ i h → ¬ Owned (proj₁ i) h} (cut r) (λ i → proj₂ (ap (proj₁ i) (proj₁ (proj₂ i)) (proj₂ (proj₂ i))))))
    where
      pack : ∀ h → (Owned j h × Headed h) × (∀ (i : Σ Pos (λ R → Ok R × Disjoint R j)) → ¬ Owned (proj₁ i) h) → Under j h
      pack h ((o , hd) , f) = o , hd , λ R ok d → f (R , ok , d)

  -- After a lane's value at `x`: what may follow it, at an outer
  -- position; and where a lane may subscribe apart from `x`'s.
  Pk : Pos → Pos → Set
  Pk x y = Sp x y × K y

  Sk : Pos → Pos → Set
  Sk x j = Ok j × Disjoint j (x ++ [ ix 1 ])

  k-step : ∀ h → K h → K (h ++ [ ix 0 ])
  k-step h (o , hh) = owned-trans p h (h ++ [ ix 0 ]) o (inj₁ (prefix-++ h [ ix 0 ])) , headed-snoc h hh

  module After (x : Pos) = Merge (Pk x) (Sk x) (λ h ph → sp-step x h (proj₁ ph) , k-step h (proj₂ ph)) (λ h ph → lane-ok h (proj₂ ph) , proj₁ (proj₁ ph))

  -- A lane subscribed apart from `x`'s keys nothing of it.
  gen-after : ∀ {B} x (m : MonotonicList B) → K x → Gen m → After.Lane x m
  gen-after x m kx gm j (okj , d) =
    every∞-mono (λ y u → sp-under x j y (proj₁ u) d (proj₂ (proj₂ u) (x ++ [ ix 1 ]) (lane-ok x kx) (disjoint-swap j _ d)) , under-k j y okj u)
      (M′.enter m j) (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (gm j okj))))))

  -- A step under a root apart from `r` is apart from one under `r`.
  lane-apart : ∀ r r′ x y → Ok r → Ok r′ → Under r x → Disjoint r r′ → Under r′ y → Disjoint y x
  lane-apart r r′ x y okr okr′ ux d uy =
    (λ o → proj₂ (proj₂ ux) r′ okr′ (disjoint-swap r r′ d) (owned-trans r′ y x (proj₁ uy) o))
    , (λ o → proj₂ (proj₂ uy) r okr d (owned-trans r x y (proj₁ ux) o))

  roots-after : ∀ {B} r x → Ok r → Under r x → {ls : List (Events∞ B)} {rs : List Pos} → Roots ls rs → All (Disjoint r) rs
              → All (Every∞ (Pk x)) ls
  roots-after r x okr ux []ᴿ                          []ᴬ       = []ᴬ
  roots-after r x okr ux (_∷ᴿ_ {r = r′} {l = l} st R) (d ∷ᴬ ds) =
    (every-mono one (force l) (Lane.kx st) , everyT-mono one (cut l) (Lane.kc st)) ∷ᴬ roots-after r x okr ux R ds
    where
      one : ∀ y → Under r′ y → Pk x y
      one y uy = sp-apart x y (lane-apart r r′ x y okr (Lane.ok st) ux d uy) , under-k r′ y (Lane.ok st) uy

  -- The lane's own rest, spread past its value.
  own-after : ∀ {B} r x b (w : Events∞ B) c → Lane r (out x b w) c → Every∞ (Pk x) w
  own-after r x b w c st =
    every-mono one (force w) (every-zip (force w) (proj₁ (proj₁ (spread (Lane.spr st)))) (proj₁ (proj₂ (every (Lane.kx st)))))
    , everyT-mono one (cut w) (everyT-zip (cut w) (proj₂ (proj₁ (spread (Lane.spr st)))) (proj₂ (proj₂ (every (Lane.kx st)))))
    where
      one : ∀ y → Sp x y × Under r y → Pk x y
      one y (s , u) = s , under-k r y (Lane.ok st) u

  -- The outer, apart from `x`'s root a step past it.
  outer-after : ∀ {B} r x (o : Maybe (Events∞ (MonotonicList B))) → Ok r → Under r x → Aside o r → Heldᴹ o → After.Outerᴹ x o
  outer-after r x nothing  okr ux a h = tt
  outer-after r x (just e) okr ux a h =
    After.outer-of x (force e) (every-mono one (force e) (every-zip (force e) (proj₁ a) (Outer.kx h)))
      (values-mono (λ m → gen-after x m (under-k r x okr ux)) (force e) (Outer.spn h))
    , everyT-mono one (cut e) (everyT-zip (cut e) (proj₂ a) (Outer.kc h))
    where
      one : ∀ y → D r y × K y → Pk x y
      one y (d , ky) = sp-apart x y (disjoint-under r y x okr ky (aside-not r y d) (proj₂ d) ux) , ky

  -- What ended parts left, under no root.
  pool-after : ∀ {B} (o : Maybe (Events∞ (MonotonicList B))) rbs r ras t x → Ok r → Under r x → Pool o (rbs ++ r ∷ ras) t → EveryT (Pk x) t
  pool-after o rbs r ras t x okr ux pl =
    everyT-mono one t (everyT-zip t (proj₁ (proj₂ (proj₂ pl))) (proj₁ (proj₂ pl)))
    where
      one : ∀ k → (All (λ r′ → ¬ Owned k r′) (rbs ++ r ∷ ras) × K k) × (All (λ r′ → ¬ Owned r′ k) (rbs ++ r ∷ ras) × FreeO o k) → Pk x k
      one k ((nk , kk) , (nr , _)) = sp-apart x k (disjoint-under r k x okr kk (proj₁ (all-pick rbs ras nr)) (proj₁ (all-pick rbs ras nk)) ux) , kk

  -- After a lane's value at `x` under root `r`, nothing the merge shows
  -- next, nor leaves running, keys where `x`'s lane would.
  after-out : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) bs (w : Events∞ B) as qs t {rbs r ras} x b c
            → Roots bs rbs → Lane r (out x b w) c → Roots as ras → Parted (rbs ++ r ∷ ras) → All (Aside o) (rbs ++ r ∷ ras) → All Gen qs
            → Heldᴹ o → Pool o (rbs ++ r ∷ ras) t
            → Every (Sp x) (M′.go op o (bs ++ w ∷ as) qs t) × EveryT (Sp x) (M′.whole o (bs ++ w ∷ as) t)
  after-out op o bs w as qs t {rbs} {r} {ras} x b c rb st ra pt asd gq h pl =
    every-mono (λ _ → proj₁) _ (After.every-go x op o (bs ++ w ∷ as) qs t po pls pq pp)
    , everyT-mono (λ _ → proj₁) _ (After.everyT-whole x o (bs ++ w ∷ as) t po pls pp)
    where
      okr = Lane.ok st
      ux  = proj₁ (every (Lane.kx st))
      ds  = proj₁ (parted-pick rbs r ras pt)
      po  = outer-after r x o okr ux (proj₁ (all-pick rbs ras asd)) h
      pls = All++⁺ (roots-after r x okr ux rb (All++⁻ˡ rbs ds)) (own-after r x b w c st ∷ᴬ roots-after r x okr ux ra (All++⁻ʳ rbs ds))
      pq  = mapᴬ (λ {m} → gen-after x m (under-k r x okr ux)) gq
      pp  = pool-after o rbs r ras t x okr ux pl

  -- THE MERGE SPREADS: after each lane's value, the merge's next is
  -- keyed apart from where the value's lane would subscribe.
  mutual
    spread-go : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t {rs} → Roots ls rs → Parted rs → All (Aside o) rs → All Gen qs
              → Heldᴹ o → Pool o rs t → Spread (M′.go op o ls qs t)
    spread-go op o ls qs idle      R pt asd gq h pl = spread-parts op o ls qs idle R pt asd gq h pl
    spread-go op o ls qs (pin k u) R pt asd gq h pl with M′.ahead-of k o ls
    ... | true  = spread-pool op o ls qs k u R pt asd gq h pl
    ... | false = spread-parts op o ls qs (pin k u) R pt asd gq h pl

    spread-pool : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs k u {rs} → Roots ls rs → Parted rs
                → All (Aside o) rs → All Gen qs → Heldᴹ o → Pool o rs (pin k u) → Spread (M′.left op o ls qs k u true)
    spread (spread-pool op o ls qs k u {rs} R pt asd gq h pl) = spread-go op o ls qs (later u) R pt asd gq h (pool-later o rs k u pl)

    spread-parts : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t {rs} → Roots ls rs → Parted rs → All (Aside o) rs → All Gen qs
                 → Heldᴹ o → Pool o rs t → Spread (M′.parts op o ls qs t)
    spread-parts op o ls qs t R pt asd gq h pl with M′.earliest ls | earliest-picks ls
    ... | none            | hs                  = spread-via op o ls qs t R pt asd gq h pl hs
    ... | found k bs l as | (eq , hk , ab , aa) with roots-at bs l as eq R
    ...   | split rb st ra = spread-race op o k bs l as qs t rb st ra pt asd gq h pl hk ab aa

    spread-via : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t {rs} → Roots ls rs → Parted rs → All (Aside o) rs → All Gen qs
               → Heldᴹ o → Pool o rs t → All (λ l → M′.head (force l) ≡ nothing) ls → Spread (M′.viaOuter op o ls qs t)
    spread-via op nothing  ls qs t R pt asd gq h pl hs = record { spread = tt }
    spread-via op (just e) ls qs t R pt asd gq h pl hs = spread-outer op e ls qs t (force e) R pt asd gq h pl (lead-hush (force e) ls hs)

    spread-race : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) k bs (l : Events∞ B) as qs t {rbs r ras}
                → Roots bs rbs → Static r l → Roots as ras → Parted (rbs ++ r ∷ ras) → All (Aside o) (rbs ++ r ∷ ras) → All Gen qs
                → Heldᴹ o → Pool o (rbs ++ r ∷ ras) t → M′.head (force l) ≡ just k
                → All (λ x → Atop k (force x)) bs → All (λ x → Atop k (force x)) as → Spread (M′.race op o k bs l as qs t)
    spread-race op nothing  k bs l as qs t rb st ra pt asd gq h pl hk ab aa = spread-lane op nothing bs l as qs t (force l) rb st ra pt asd gq h pl hk
    spread-race op (just e) k bs l as qs t rb st ra pt asd gq h pl hk ab aa with M′.head (force e) in he
    ... | nothing = spread-lane op (just e) bs l as qs t (force l) rb st ra pt asd gq h pl hk
    ... | just k′ with k′ <ᵖ k in kk
    ...   | true  = spread-outer op e (bs ++ l ∷ as) qs t (force e) (roots-++ rb (st ∷ᴿ ra)) pt asd gq h pl
                      (lead-of (force e) (bs ++ l ∷ as) he
                        (All++⁺ (mapᴬ (λ {x} → beyond-still k′ k (force x) kk) ab)
                                (beyond-just k′ (force l) hk kk ∷ᴬ mapᴬ (λ {x} → beyond-still k′ k (force x) kk) aa)))
    ...   | false = spread-lane op (just e) bs l as qs t (force l) rb st ra pt asd gq h pl hk

    spread-outer : ∀ {B} op (e : Events∞ (MonotonicList B)) ls qs t (x : Events (MonotonicList B)) {rs} → Roots ls rs → Parted rs
                 → All (λ r → Every (D r) x × EveryT (D r) (cut e)) rs → All Gen qs → Outer x (cut e)
                 → PoolF (FreeC x (cut e)) rs t → Lead x ls → Spread (M′.outer op e ls qs t x)
    spread (spread-outer op e ls qs t (out q m w) R pt asd gq h pl ld)
      with M′.admit op (q ++ [ ix 1 ]) m ls qs
         | admit-ok op q m w t ls qs R pt (mapᴬ proj₁ asd) gq (proj₁ (values (Outer.spn h))) (lane-ok q (proj₁ (every (Outer.kx h))))
             (proj₁ (spread (Outer.spr h))) ld (proj₂ (every (Outer.kx h))) pl
    ... | ls′ , qs′ , d | taken R′ pt′ asd′ at′ gq′ pl′ ad = spread-go op (just w) ls′ qs′ (t ∪ d) R′ pt′ asd′ gq′ (outer-out h) pl′
    spread (spread-outer op e ls qs t (skip q w) {rs} R pt asd gq h pl ld) =
      spread-go op (just w) ls qs t R pt (mapᴬ (λ a → proj₂ (every (proj₁ a))) asd) gq (outer-skip h) (pool-oskip q w (cut e) t rs pl)
    spread (spread-outer op e [] [] t (end c) R pt asd gq h pl ld) = tt
    spread (spread-outer op e [] (m ∷ qs) t (end c) []ᴿ pt asd gq h pl ld) =
      spread-go op nothing [] (m ∷ qs) (t ∪ cut e) []ᴿ tt []ᴬ gq tt (outer-end-pool c e t [] h asd pl)
    spread (spread-outer {B} op e (l ∷ ls) qs t (end c) {rs} R pt asd gq h pl ld) =
      spread-go op nothing (l ∷ ls) qs (t ∪ cut e) R pt (aside-none {B} rs) gq tt (outer-end-pool c e t rs h asd pl)
    spread (spread-outer op e ls qs t hush R pt asd gq h pl ld) = tt

    spread-lane : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) bs (l : Events∞ B) as qs t (x : Events B) {rbs r ras}
                → Roots bs rbs → Lane r x (cut l) → Roots as ras → Parted (rbs ++ r ∷ ras) → All (Aside o) (rbs ++ r ∷ ras) → All Gen qs
                → Heldᴹ o → Pool o (rbs ++ r ∷ ras) t → ∀ {k} → M′.head x ≡ just k → Spread (M′.lane op o bs l as qs t x)
    spread (spread-lane op o bs l as qs t (out k b w) rb st ra pt asd gq h pl refl) =
      after-out op o bs w as qs t k b (cut l) rb st ra pt asd gq h pl
      , spread-go op o (bs ++ w ∷ as) qs t (roots-++ rb (lane-out st ∷ᴿ ra)) pt asd gq h pl
    spread (spread-lane op o bs l as qs t (skip k w) rb st ra pt asd gq h pl refl) =
      spread-go op o (bs ++ w ∷ as) qs t (roots-++ rb (lane-skip st ∷ᴿ ra)) pt asd gq h pl
    spread (spread-lane op o bs l as (m ∷ qs) t (end c) {rbs} {r} {ras} rb st ra pt asd (gm ∷ᴬ gq) h pl refl) =
      spread-go op o (M′.enter m c₁ ∷ bs ++ as) qs (t ∪ cut l) (fresh c₁ (M′.enter m c₁) (gm c₁ okc) okc ∷ᴿ roots-++ rb ra)
        (mapᴬ (λ {r′} od → hand-apart r c r′ uc (proj₁ od) (proj₂ od)) oks , proj₂ pp)
        (hand-aside r c o (Lane.ok st) uc ar h ∷ᴬ proj₂ (all-pick rbs ras asd)) gq h
        (pool-hand o rbs r ras t c l st oks ar h pl)
      where
        c₁  = c ++ [ ix 1 ]
        uc  = every (Lane.kx st)
        okc = hand-ok r c (ix 1) (Lane.ok st) uc
        pp  = parted-pick rbs r ras pt
        ar  = proj₁ (all-pick rbs ras asd)
        oks = all-zip (roots-ok (roots-++ rb ra)) (proj₁ pp)
    spread (spread-lane op nothing [] l [] [] t (end c) rb st ra pt asd gq h pl refl) = tt
    spread (spread-lane op nothing [] l (a ∷ as) [] t (end c) rb st ra pt asd gq h pl refl) =
      lane-gone op nothing [] l (a ∷ as) t c rb st ra pt asd h pl
    spread (spread-lane op nothing (b ∷ bs) l as [] t (end c) rb st ra pt asd gq h pl refl) =
      lane-gone op nothing (b ∷ bs) l as t c rb st ra pt asd h pl
    spread (spread-lane op (just e) bs l as [] t (end c) rb st ra pt asd gq h pl refl) =
      lane-gone op (just e) bs l as t c rb st ra pt asd h pl
    spread (spread-lane op o bs l as qs t hush rb st ra pt asd gq h pl ())

    lane-gone : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) bs (l : Events∞ B) as t c {rbs r ras}
              → Roots bs rbs → Lane {B} r (end c) (cut l) → Roots as ras → Parted (rbs ++ r ∷ ras) → All (Aside o) (rbs ++ r ∷ ras)
              → Heldᴹ o → Pool o (rbs ++ r ∷ ras) t → Spread (M′.go op o (bs ++ as) [] (t ∪ cut l))
    lane-gone op o bs l as t c {rbs} {r} {ras} rb st ra pt asd h pl =
      spread-go op o (bs ++ as) [] (t ∪ cut l) (roots-++ rb ra) (proj₂ pp) (proj₂ (all-pick rbs ras asd)) []ᴬ h
        (pool-ended o rbs r ras t (cut l) st oks (proj₁ (all-pick rbs ras asd)) h pl)
      where
        pp  = parted-pick rbs r ras pt
        oks = all-zip (roots-ok (roots-++ rb ra)) (proj₁ pp)

-- Keyed with no step `h` keys, so with none just under it.
disjoint-snoc : ∀ h k l → (∀ x → Tagged k (x ++ [ l ]) → Tagged k x) → Disjoint h k → Disjoint (h ++ [ l ]) k
disjoint-snoc h k l tg (nh , nk) = (λ o → nh (owned-trans h (h ++ [ l ]) k (inj₁ (prefix-++ h [ l ])) o)) , down
  where down : ¬ Owned k (h ++ [ l ])
        down (inj₁ pr) with prefix-split k h l pr
        ... | inj₁ q  = nk (inj₁ q)
        ... | inj₂ eq = nh (inj₁ (subst (Prefix h) (sym eq) (prefix-++ h [ l ])))
        down (inj₂ t) = nk (inj₂ (tg h t))

-- No earlier than `h` and keyed with none of it: strictly past it.
take-ahead : ∀ h k → k <ᵖ h ≡ false → Disjoint h k → h <ᵖ k ≡ true
take-ahead h k l d with <ᵖ-split h k l
... | inj₁ hk   = hk
... | inj₂ refl = ⊥-elim (proj₁ d (inj₁ (prefix-refl h)))

-- Past `h` and keyed with none of it: past its completion under `last`.
take-end : ∀ h k → h <ᵖ k ≡ true → Disjoint h k
         → (h ++ [ last ]) <ᵖ k ≡ true × Disjoint ((h ++ [ last ]) ++ [ ix 1 ]) k × ¬ Ext (h ++ [ last ]) k
take-end h k hk d =
  M.<ᵖ-apart h k [ last ] hk (λ ys eq → proj₁ d (inj₁ (subst (Prefix h) (sym eq) (prefix-++ h ys))))
  , disjoint-snoc (h ++ [ last ]) k (ix 1) (λ x → tagged-lane k x 1) dl
  , λ x → proj₁ dl (owned-ext x)
  where dl = disjoint-snoc h k last (λ x → tagged-mark k x last last-mark) d

-- A pin trailing what comes past a value at `h`, keyed with none of `h`:
-- past `h`.
pin-past : ∀ {A} h (x : Events A) k → Past h x → TrailE x k → Disjoint h k → h <ᵖ k ≡ true
pin-past h (out n _ _) k (hn , _) (l , _)    d = still h n k hn l
pin-past h (skip n _)  k (hn , _) (inj₁ l)   d = still h n k hn l
pin-past h (skip n _)  k (hn , _) (inj₂ m) d with k <ᵖ h in kh
... | true  = ⊥-elim (proj₂ d (inj₁ (marks-between h m kh hn)))
... | false = take-ahead h k kh d
pin-past h (end n)     k (hn , _) (nk , _)   d = <ᵖ-trans h n k hn nk
pin-past h hush        k _        ()         d

-- A TAKEWHILE KEEPS ITS SOURCE'S CUTS TRAILING, its source in order and
-- steady: what was left running before the first failing value trails
-- that value moved under `ix 0`, and the completion under `last`.
mutual
  trail-take : ∀ {A} i (q : A → Bool) (x : Events A) c → Ordered x → Steady x → Trail x c → Trail (M′.takeWhileᴱ i q x) c
  trail-take i q (out h a r) c o s tr = trail-taking i q h a (q a) r c o s tr
  trail-take i q (skip h r)  c o s tr = trail-skipping i q h r c o s tr
  trail-take i q (end h)     c o s tr = tr
  trail-take i q hush        c o s tr = tr

  trail-skipping : ∀ {A} i (q : A → Bool) h (r : Events∞ A) c → Ordered (skip h r) → Steady (skip h r) → Trail (skip h r) c
                 → Trail (M′.takeWhileᴱ i q (skip h r)) c
  trail (trail-skipping i q h r c o s tr) =
    proj₁ (trail tr) , proj₁ (proj₂ (trail tr)) , trail-take i q (force r) (cut r) (proj₂ (ordered o)) (proj₂ (steady s)) (proj₂ (proj₂ (trail tr)))
  trailᶠ (trail-skipping i q h r c o s tr) = trailᶠ tr

  trail-taking : ∀ {A} i (q : A → Bool) h a b (r : Events∞ A) c → Ordered (out h a r) → Steady (out h a r) → Trail (out h a r) c
               → Trail (M′.taking i q h a b r) c
  trail (trail-taking i q h a true r c o s tr) =
    proj₁ (trail tr) , proj₁ (proj₂ (trail tr))
    , trail-take i q (force r) (cut r) (proj₂ (ordered o)) (proj₂ (steady s)) (proj₁ (proj₂ (proj₂ (trail tr)))) , proj₂ (proj₂ (proj₂ (trail tr)))
  trail (trail-taking true q h a false r c o s tr) =
    proj₁ (trail tr)
    , everyT-mono (λ k z → <ᵖ-step h k (take-ahead h k (proj₁ z) (proj₂ z)) , disjoint-snoc h k (ix 0) (λ x → tagged-lane k x 0) (proj₂ z)) c (proj₁ (proj₂ (trail tr)))
    , ended , everyT-mono (λ k d → disjoint-snoc h k (ix 0) (λ x → tagged-lane k x 0) d) (cut r) (proj₂ nx)
    where
      nx = proj₂ (proj₂ (trail tr))
      ended : Trail (end (h ++ [ last ])) (cut r)
      trail ended = proj₁ (trail (proj₁ nx))
                  , everyT-mono (λ k z → take-end h k (pin-past h (force r) k (proj₁ (steady s)) (proj₁ z) (proj₂ z)) (proj₂ z)) (cut r)
                      (everyT-zip (cut r) (proj₁ (proj₂ (trail (proj₁ nx)))) (proj₂ nx))
                  , tt
      trailᶠ ended = trailᶠ (proj₁ nx)
  trail (trail-taking false q h a false r c o s tr) =
    proj₁ (trail tr) , everyT-mono (λ k z → take-end h k (take-ahead h k (proj₁ z) (proj₂ z)) (proj₂ z)) c (proj₁ (proj₂ (trail tr))) , tt
  trailᶠ (trail-taking i q h a b r c o s tr) = trailᶠ tr

-- A DEFER'S CUTS TRAIL ITS RUN where a tick heads it, its program's
-- subscribed just past its skip doing so: the skip leaves nothing
-- running, and past it the program's run is what it shows.
trail-defer : ∀ {Γ A} (l : Later Timeline Γ A) p (ρ : NEnv Γ) → Headed p → Alienᴱ p ρ
            → Trailing (U.stateᴺ (U.subscribe (Later.force l) (p ++ [ ix 1 ])) ρ) → Trailing (U.stateᴺ (U.deferᶜ l p []) ρ)
trail (trail-defer l p ρ hp cl tr) =
  sortedT-idle , everyT-idle
  , trail-≈ S X _ _ alike (λ k → agreeᵀ (U.subscribed (Later.force l) (env-refl (U.hots ρ))) P₁) tr
  where open Deferred l p ρ hp cl
trailᶠ (trail-defer l p ρ hp cl tr) = flatT-idle

-- `P` of where `e` next shows, if anywhere.
Head : ∀ {A} → (Pos → Set) → Events A → Set
Head P (out n _ _) = P n
Head P (skip n _)  = P n
Head P (end n)     = P n
Head P hush        = ⊤

-- A run that steps.
Going : ∀ {A} → Events A → Set
Going hush = ⊥
Going _    = ⊤
