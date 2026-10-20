{-# OPTIONS --guardedness #-}

-- A WRITE INSIDE A LIFT'S END, LEFT: the free nodes a lift carries tie
-- to their nodes' leftovers once their steps end, and an end climbs no
-- connect's source, so every leftover on the way up reads the end's
-- leftover and its siblings' cells alone.
module adequacy.Frame.Lefts where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.List.Relation.Unary.All using (_∷_) renaming (lookup to lookupᴬ)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; _∷_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; proj₁)
open import Level using (lift)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong₂; subst; subst₂)

open import denotation.MonotonicList.Events using (Timeline)
import denotation.Unfold as U
open import operation.PureObservable using (Out)
open import operation.AbstractObservable using () renaming (module Machine to Shared)
open import adequacy.Strong using (module Strongly)
open import adequacy.Strong.Against using (module StrongAgainst)
open import adequacy.Torn using (module Tearing)
open import adequacy.Moves using (module Moving)
open import adequacy.Local using (module Locality)
open import adequacy.Ghost using (module Ghosting)
open import adequacy.Frame.Repool using (module FramingRepool)
open import adequacy.Shift using (module Shifting)

module FramingLefts (R : Set) where
  open Shared Timeline (Out R) using (Heapᴹ; store)
  open Strongly R using (Sub; scanˢ; here; module At; Path; PathLanes; in-map; in-scan; in-take; in-outer; in-lanes; in-source; in-body; in-defer; this-lane; next-lane; Lane; lane; names; laneNames; cutNames; quietName; subjectNames; flatNames)
  open StrongAgainst R using (Leaves)
  open Tearing R using (Off; part-alike; names-path; lanes-path; apart-r; apart-l; look-store; fresh-path)
  open Moving R using (pairs-r; pairs-split)
  open Locality R using (module Heaps)
  open Ghosting R using (Lifts; Lefts; LeftsL; LiftsLane; OnEnd; SourceFirst; lifts-here; lifts-map; lifts-scan; lifts-take; lifts-outer; lifts-lanes; lifts-source; lifts-body; lifts-shut; lifts-defer; lifts-this; lifts-next)
  open FramingRepool R using (lifts-off; liftsL-off; module Wrote; off-store; scan-lifts)
  open Shifting R using (leftover-alike; leftoverL-alike; conn-left; sourced-heap)

  ----------------------------------------------------------------------
  -- An end climbs no source

  Skipˢ : ∀ {Γ A} → U.Step Γ A → Set
  Skipˢ (U.skipˢ _ _) = ⊤
  Skipˢ _             = ⊥

  on-end : ∀ {Γ A} (S : U.Step Γ A) {P Q : Set₁} → ((Skipˢ S → ⊥) → P → Q) → OnEnd S P → OnEnd S Q
  on-end (U.outˢ _ _ _) f p = p
  on-end (U.skipˢ _ _)  f p = p
  on-end (U.endˢ _)     f p = f (λ ()) p
  on-end U.hushˢ        f p = p

  -- Every operator a lift climbs keeps a skip a skip; a source's step
  -- under its own order is one.
  skip-map : ∀ {Γ A B} (f : A → B) (S : U.Step Γ A) → Skipˢ S → Skipˢ (U.mapˢ f S)
  skip-map f (U.skipˢ _ _) k = tt
  skip-map f (U.outˢ _ _ _) ()
  skip-map f (U.endˢ _) ()
  skip-map f U.hushˢ ()

  skip-scan : ∀ {Γ A B} (f : B → A → B) z (S : U.Step Γ A) → Skipˢ S → Skipˢ (U.scanˢ f z S)
  skip-scan f z (U.skipˢ _ _) k = tt
  skip-scan f z (U.outˢ _ _ _) ()
  skip-scan f z (U.endˢ _) ()
  skip-scan f z U.hushˢ ()

  skip-take : ∀ {Γ A} i (p : A → _) (S : U.Step Γ A) → Skipˢ S → Skipˢ (U.takeWhileˢ i p S)
  skip-take i p (U.skipˢ _ _) k = tt
  skip-take i p (U.outˢ _ _ _) ()
  skip-take i p (U.endˢ _) ()
  skip-take i p U.hushˢ ()

  skip-outer : ∀ {Γ A B} op (g : A → _ → U.Node Γ B) o (S : U.Step Γ A) ls qs p → Skipˢ S → Skipˢ (U.outerˢ op g o S ls qs p)
  skip-outer op g o (U.skipˢ _ _) ls qs p k = tt
  skip-outer op g o (U.outˢ _ _ _) ls qs p ()
  skip-outer op g o (U.endˢ _) ls qs p ()
  skip-outer op g o U.hushˢ ls qs p ()

  skip-lane : ∀ {Γ A B} op (g : A → _ → U.Node Γ B) o bs l (S : U.Step Γ B) as qs p → Skipˢ S → Skipˢ (U.laneˢ op g o bs l S as qs p)
  skip-lane op g o bs l (U.skipˢ _ _) as qs p k = tt
  skip-lane op g o bs l (U.outˢ _ _ _) as qs p ()
  skip-lane op g o bs l (U.endˢ _) as qs p ()
  skip-lane op g o bs l U.hushˢ as qs p ()

  skip-body : ∀ {Γ A B} r (s : U.Source Γ A) (S : U.Step (A ∷ Γ) B) → Skipˢ S → Skipˢ (U.bodyˢ r s S)
  skip-body r s (U.skipˢ _ _) k = tt
  skip-body r s (U.outˢ _ _ _) ()
  skip-body r s (U.endˢ _) ()
  skip-body r s U.hushˢ ()

  skip-shut : ∀ {Γ A B} r c (t : U.Node Γ A) (S : U.Step (A ∷ Γ) B) → Skipˢ S → Skipˢ (U.shutˢᵗ r c t S)
  skip-shut r c t (U.skipˢ _ _) k = tt
  skip-shut r c t (U.outˢ _ _ _) ()
  skip-shut r c t (U.endˢ _) ()
  skip-shut r c t U.hushˢ ()

  skip-source : ∀ {Γ A B} r (b : U.Node (A ∷ Γ) B) sb (s : U.Node Γ A) (S : U.Step Γ A) → SourceFirst S sb → Skipˢ (U.sourceˢ r b sb s S)
  skip-source r b sb s (U.outˢ q a s′) sf rewrite sf = tt
  skip-source r b sb s (U.skipˢ q s′)  sf rewrite sf = tt
  skip-source r b sb s (U.endˢ c)      sf rewrite sf = tt
  skip-source r b sb s U.hushˢ         ()

  mutual
    NoSource : ∀ {h Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} → Path t u → Set
    NoSource here           = ⊤
    NoSource (in-map ρ)     = NoSource ρ
    NoSource (in-scan ρ)    = NoSource ρ
    NoSource (in-take ρ)    = NoSource ρ
    NoSource (in-outer ρ)   = NoSource ρ
    NoSource (in-lanes πL)  = NoSourceL πL
    NoSource (in-source ρ)  = ⊥
    NoSource (in-body ρ)    = NoSource ρ
    NoSource (in-defer ρ)   = NoSource ρ

    NoSourceL : ∀ {h Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} → PathLanes ls u → Set
    NoSourceL (this-lane ρ)  = NoSource ρ
    NoSourceL (next-lane πL) = NoSourceL πL

  -- A lift to anything but a skip climbs no source: a source's step
  -- climbs as a skip, and a skip climbs as one.
  mutual
    sourceless : ∀ {h} {H : Heapᴹ h} {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} {ρ : Path t u} {s S} → Lifts H ρ s S → (Skipˢ S → ⊥) → NoSource ρ
    sourceless lifts-here                              ns = tt
    sourceless (lifts-map {f = f} {S = S} L)           ns = sourceless L (λ k → ns (skip-map f S k))
    sourceless (lifts-scan {S = S} L)                  ns = sourceless L (λ k → ns (skip-scan _ _ S k))
    sourceless (lifts-take {S = S} _ L)                ns = sourceless L (λ k → ns (skip-take _ _ S k))
    sourceless (lifts-outer {S = S} _ _ L)             ns = sourceless L (λ k → ns (skip-outer _ _ _ S _ _ _ k))
    sourceless (lifts-lanes {S = S} LL _ _ _)          ns = sourcelessL LL (λ k → ns (skip-lane _ _ _ _ _ S _ _ _ k))
    sourceless (lifts-source {S = S} _ sf L)           ns = ns (skip-source _ _ _ _ S sf)
    sourceless (lifts-body {S = S} _ _ L)              ns = sourceless L (λ k → ns (skip-body _ _ S k))
    sourceless (lifts-shut {S = S} _ _ _ L)            ns = sourceless L (λ k → ns (skip-shut _ _ _ S k))
    sourceless (lifts-defer L)                         ns = sourceless L ns

    sourcelessL : ∀ {h} {H : Heapᴹ h} {Δ B Δ′ C} {ls : List (Lane h Δ B)} {u : Sub h Δ′ C} {πL : PathLanes ls u} {s bs S as}
                → LiftsLane H πL s bs S as → (Skipˢ S → ⊥) → NoSourceL πL
    sourcelessL (lifts-this _ L) ns = sourceless L ns
    sourcelessL (lifts-next LL)  ns = sourcelessL LL ns

  ----------------------------------------------------------------------
  -- A leftover above a sourceless path reads the end's leftover

  mutual
    leftover-off : ∀ {h} (H H′ : Heapᴹ h) {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (ρ : Path t u) → NoSource ρ → AllPairs _≢_ (names t)
                 → Off H H′ (names u) → (∀ {B} → At.leftover H′ {B = B} u ≡ At.leftover H {B = B} u)
                 → ∀ {B} → At.leftover H′ {B = B} t ≡ At.leftover H {B = B} t
    leftover-off H H′ here ns ps off lb = lb
    leftover-off H H′ (in-map ρ) ns ps off lb = leftover-off H H′ ρ ns ps off lb
    leftover-off H H′ (in-scan ρ) ns (_ ∷ ps) off lb = leftover-off H H′ ρ ns ps off lb
    leftover-off H H′ (in-take {c = c} {k} ρ) ns ps off lb = leftover-off H H′ ρ ns (pairs-r (quietName k) (pairs-r (cutNames c) ps)) off lb
    leftover-off H H′ (in-outer {fl = fl} {oc} {k} {r} {t = so} {ls} ρ) ns ps off lb =
      cong₂ U.unionᶜ (leftover-off H H′ ρ ns (proj₁ (pairs-split (names so) P)) off lb)
                     (leftoverL-alike H H′ ls (Heaps.keeps H H′ off (names-path ρ) (apart-l (names so) P)))
      where P = pairs-r ((_ , r) ∷ []) (pairs-r (quietName k) (pairs-r (cutNames oc) (pairs-r (flatNames fl) ps)))
    leftover-off H H′ (in-lanes {fl = fl} {oc} {k} {r} {t = so} πL) ns ps off lb =
      cong₂ U.unionᶜ (leftover-alike H H′ so (Heaps.keeps H H′ off (lanes-path πL) (apart-r (names so) P)))
                     (leftoverL-off H H′ πL ns (pairs-r (names so) P) off lb)
      where P = pairs-r ((_ , r) ∷ []) (pairs-r (quietName k) (pairs-r (cutNames oc) (pairs-r (flatNames fl) ps)))
    leftover-off H H′ (in-source ρ) () ps off lb
    leftover-off H H′ (in-body {S = Sj} {c} {b} {kb} {k} {rp = rp} {t = src} ρ) ns ps off lb =
      conn-left rp (trans (sourced-heap H H′ (At.part H′ src) (At.leftover H′ src)) (cong₂ (At.sourced H) (part-alike H H′ src al) (leftover-alike H H′ src al)))
                   (leftover-off H H′ ρ ns (pairs-r (names src) Q₄) off lb)
      where
        Q₄ = pairs-r (quietName k) (pairs-r (quietName kb) (pairs-r ((_ , b) ∷ []) (pairs-r (cutNames c) (pairs-r (subjectNames Sj) ps))))
        al = Heaps.keeps H H′ off (names-path ρ) (apart-r (names src) Q₄)
    leftover-off H H′ (in-defer {k = k} ρ) ns ps off lb = leftover-off H H′ ρ ns (pairs-r (quietName k) ps) off lb

    leftoverL-off : ∀ {h} (H H′ : Heapᴹ h) {Δ B Δ′ C} {ls : List (Lane h Δ B)} {u : Sub h Δ′ C} (πL : PathLanes ls u) → NoSourceL πL → AllPairs _≢_ (laneNames ls)
                  → Off H H′ (names u) → (∀ {B′} → At.leftover H′ {B = B′} u ≡ At.leftover H {B = B′} u)
                  → ∀ {B′} → At.leftoverL H′ {B = B′} ls ≡ At.leftoverL H {B = B′} ls
    leftoverL-off H H′ (this-lane {c = c} {k} {t = s₀} {ls} ρ) ns ps off lb =
      cong₂ U.unionᶜ (leftover-off H H′ ρ ns (proj₁ (pairs-split (names s₀) P)) off lb)
                     (leftoverL-alike H H′ ls (Heaps.keeps H H′ off (names-path ρ) (apart-l (names s₀) P)))
      where P = pairs-r (quietName k) (pairs-r (cutNames c) ps)
    leftoverL-off H H′ (next-lane {l = lane c k s₀} πL) ns ps off lb =
      cong₂ U.unionᶜ (leftover-alike H H′ s₀ (Heaps.keeps H H′ off (lanes-path πL) (apart-r (names s₀) P)))
                     (leftoverL-off H H′ πL ns (pairs-r (names s₀) P) off lb)
      where P = pairs-r (quietName k) (pairs-r (cutNames c) ps)

  ----------------------------------------------------------------------
  -- The lift carried across, its free nodes left

  lefts-at : ∀ {h} {H : Heapᴹ h} {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} {ρ : Path t u} {s ℓ} {X : Set ℓ} (F : X → U.Step Δ A) {x y}
             (e : x ≡ y) {L : Lifts H ρ s (F x)} → Lefts H L → Lefts H (subst (λ z → Lifts H ρ s (F z)) e L)
  lefts-at F refl lt = lt

  lefts-at₂ : ∀ {h} {H : Heapᴹ h} {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} {ρ : Path t u} {s ℓ ℓ′} {X : Set ℓ} {Y : Set ℓ′} (F : X → Y → U.Step Δ A)
              {x₁ x₂ y₁ y₂} (e₁ : x₁ ≡ x₂) (e₂ : y₁ ≡ y₂) {L : Lifts H ρ s (F x₁ y₁)} → Lefts H L → Lefts H (subst₂ (λ x y → Lifts H ρ s (F x y)) e₁ e₂ L)
  lefts-at₂ F refl refl lt = lt

  leftsL-at : ∀ {h} {H : Heapᴹ h} {Δ B Δ′ C} {ls : List (Lane h Δ B)} {u : Sub h Δ′ C} {πL : PathLanes ls u} {s S l ℓ} {X : Set ℓ}
              (F G : X → List (U.Node Δ B)) {x y} (e : x ≡ y) {LL : LiftsLane H πL s (F x) S (G x)}
            → LeftsL H l LL → LeftsL H l (subst (λ z → LiftsLane H πL s (F z) S (G z)) e LL)
  leftsL-at F G refl lt = lt

  -- Read at an end's leftover the write leaves alike, every free node
  -- still ties to its node's.  The unconditional form, any write inside
  -- the end, is false: an ancestor's leftover reads the end's subtree,
  -- a write there moves it, and a free node the lift carried does not
  -- move with it.
  mutual
    lefts-off : ∀ {h} (H H′ : Heapᴹ h) {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (ρ : Path t u) (ps : AllPairs _≢_ (names t))
                (off : Off H H′ (names u)) → (∀ {B} → At.leftover H′ {B = B} u ≡ At.leftover H {B = B} u)
              → ∀ {s S} (L : Lifts H ρ s S) → Lefts H L → Lefts H′ (lifts-off H H′ ρ ps off L)
    lefts-off H H′ here ps off lb lifts-here lt = lt
    lefts-off H H′ (in-map ρ) ps off lb (lifts-map L) lt = lefts-off H H′ ρ ps off lb L lt
    lefts-off H H′ (in-scan {f = f} {r} ρ) (nr ∷ ps) off lb (lifts-scan {S = S} L) lt =
      lefts-at (λ z → U.scanˢ f z S) _ (lefts-off H H′ ρ ps off lb L lt)
    lefts-off H H′ (in-take {c = c} {k} ρ) ps@(nl ∷ _) off lb (lifts-take lv L) lt =
      lefts-off H H′ ρ (pairs-r (quietName k) (pairs-r (cutNames c) ps)) off lb L lt
    lefts-off H H′ (in-outer {op = op} {f} {fl} {oc} {k} {r} {pl} {t = so} {ls} ρ) ps@(_ ∷ _ ∷ aq ∷ _) off lb (lifts-outer {S = S} {o₀} of pb L) (lo , lt) =
      lefts-at₂ (λ zs qs → U.outerˢ op (λ a q → U.subscribe (f a) q) o₀ S zs qs pl) _ _
        (on-end S (λ ne → subst (λ y → Leaves o₀ y) (sym (leftover-off H H′ ρ (sourceless L ne) P₁ off lb))) lo , lefts-off H H′ ρ P₁ off lb L lt)
      where
        P  = pairs-r ((_ , r) ∷ []) (pairs-r (quietName k) (pairs-r (cutNames oc) (pairs-r (flatNames fl) ps)))
        P₁ = proj₁ (pairs-split (names so) P)
    lefts-off H H′ (in-lanes {op = op} {f} {fl} {oc} {k} {r} {pl} {t = so} {ls} πL) ps@(_ ∷ _ ∷ aq ∷ _) off lb (lifts-lanes {bs = bs} {l} {S} {as} LL ee lf pb) lt =
      lefts-at₂ (λ x qs → U.laneˢ op (λ a q → U.subscribe (f a) q) x bs l S as qs pl) _ _ (leftsL-off H H′ πL (pairs-r (names so) P) off lb LL lt)
      where P = pairs-r ((_ , r) ∷ []) (pairs-r (quietName k) (pairs-r (cutNames oc) (pairs-r (flatNames fl) ps)))
    lefts-off H H′ (in-source {S = Sj} {c} {b} {kb} {k} {t = src} {bd} ρ) ps off lb (lifts-source {S = S} {c₀} pb sf L) (lc , lt) =
      on-end S (λ ne → subst (λ y → Leaves c₀ y) (sym (leftover-off H H′ ρ (sourceless L ne) Q₁ off lb))) lc , lefts-off H H′ ρ Q₁ off lb L lt
      where
        Q₄ = pairs-r (quietName k) (pairs-r (quietName kb) (pairs-r ((_ , b) ∷ []) (pairs-r (cutNames c) (pairs-r (subjectNames Sj) ps))))
        Q₁ = proj₁ (pairs-split (names src) Q₄)
    lefts-off H H′ (in-body {S = Sj} {c} {b} {kb} {k} {t = src} {bd} ρ) ps off lb (lifts-body pt bf L) lt =
      lefts-off H H′ ρ (pairs-r (names src) Q₄) off lb L lt
      where Q₄ = pairs-r (quietName k) (pairs-r (quietName kb) (pairs-r ((_ , b) ∷ []) (pairs-r (cutNames c) (pairs-r (subjectNames Sj) ps))))
    lefts-off H H′ (in-body {S = Sj} {c} {b} {kb} {k} {t = src} {bd} ρ) ps off lb (lifts-shut pt e rb L) lt =
      lefts-off H H′ ρ (pairs-r (names src) Q₄) off lb L lt
      where Q₄ = pairs-r (quietName k) (pairs-r (quietName kb) (pairs-r ((_ , b) ∷ []) (pairs-r (cutNames c) (pairs-r (subjectNames Sj) ps))))
    lefts-off H H′ (in-defer {k = k} ρ) ps off lb (lifts-defer L) lt = lefts-off H H′ ρ (pairs-r (quietName k) ps) off lb L lt

    leftsL-off : ∀ {h} (H H′ : Heapᴹ h) {Δ B Δ′ C} {ls : List (Lane h Δ B)} {u : Sub h Δ′ C} (πL : PathLanes ls u) (ps : AllPairs _≢_ (laneNames ls))
                 (off : Off H H′ (names u)) → (∀ {B′} → At.leftover H′ {B = B′} u ≡ At.leftover H {B = B′} u)
               → ∀ {s bs S as l} (LL : LiftsLane H πL s bs S as) → LeftsL H l LL → LeftsL H′ l (liftsL-off H H′ πL ps off LL)
    leftsL-off H H′ (this-lane {c = c} {k} {t = s₀} {ls} ρ) ps@(nl ∷ _) off lb {l = l} (lifts-this {S = S} lv L) (ll , lt) =
      leftsL-at (λ _ → []) (λ zs → zs) _
        (on-end S (λ ne → subst (λ y → Leaves l y) (sym (leftover-off H H′ ρ (sourceless L ne) P₁ off lb))) ll , lefts-off H H′ ρ P₁ off lb L lt)
      where
        P  = pairs-r (quietName k) (pairs-r (cutNames c) ps)
        P₁ = proj₁ (pairs-split (names s₀) P)
    leftsL-off H H′ (next-lane {l = lane c k s₀} πL) ps@(nl ∷ _) off lb (lifts-next {bs = bs} {as = as} LL) lt =
      leftsL-at (λ zs → zs ++ bs) (λ _ → as) _ (leftsL-off H H′ πL (pairs-r (names s₀) P) off lb LL lt)
      where P = pairs-r (quietName k) (pairs-r (cutNames c) ps)

  -- A write at a scan's accumulator, left: the scan's leftover its
  -- source's, which reads no accumulator.
  scan-lefts : ∀ {h} (H : Heapᴹ h) {T : Sub h [] R} {Δ A B} {f : B → A → B} {r} {u : Sub h Δ A} (ρ : Path T (scanˢ f r u)) (fs : AllPairs _≢_ (names T))
             → ∀ {s S} z (L : Lifts H ρ s S) → Lefts H L → Lefts (store H r (lift z)) (scan-lifts H ρ fs z L)
  scan-lefts H {r = r} {u} ρ fs z with fresh-path ρ fs
  ... | nr ∷ _ = lefts-off H (store H r (lift z)) ρ fs (Wrote.offU H (store H r (lift z)) ρ (off-store H r) (here refl ∷ []) fs)
                   (leftover-alike H (store H r (lift z)) u (λ j m → look-store H r j (lookupᴬ nr m)))
