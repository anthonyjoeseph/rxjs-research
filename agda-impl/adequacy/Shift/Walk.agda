{-# OPTIONS --guardedness #-}

module adequacy.Shift.Walk where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Any.Properties using (++⁺ˡ; ++⁺ʳ; ++⁻)
open import Data.List.Relation.Unary.All using (All) renaming (lookup to lookupᴬ; _∷_ to _∷ᴬ_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; _∷_)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴸ_)
open import Level using (lower)
open import Data.Maybe using (Maybe; just; nothing; is-just; is-nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Data.Sum using ([_,_]′)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥; ⊥-elim)

open import denotation.MonotonicList.Events using (Timeline; Pos)
import denotation.Unfold as U
open import operation.PureObservable using (Out; Pureᴾ)
open import operation.AbstractObservable using (maybe; quiet; module Heap; module Run) renaming (module Machine to Shared)
open import adequacy.Strong using (module Strongly)
open import adequacy.Strong.Against using (module StrongAgainst)
open import adequacy.Strong.Held using (module StrongHeld)
open import adequacy.Torn using (module Tearing)
open import adequacy.Moves using (module Moving)
open import adequacy.Local using (module Locality)
open import adequacy.Ghost.Paths using (module GhostingPaths)
open import adequacy.Frame using (module Framing)
open import adequacy.Frame.Repool using (module FramingRepool)
open import adequacy.Kept using (module Keeping)
open import adequacy.Retag using (Retag; module Retagging) renaming (keep to keepᴿ)
open import adequacy.Shift using (module Shifting)

module ShiftWalk (R : Set) where
  open Heap using (Sink; Quiet; slot; cell)
  open Run (Pureᴾ R) using (Ref; Subject; module Kit; module FlatKit)
  open FlatKit using (Flat)
  open Shared Timeline (Out R) using (Heapᴹ; look)
  open Strongly R using (Sub; Path; PathLanes; here; in-map; in-scan; in-take; in-outer; in-lanes; in-source; in-body; in-defer; this-lane; next-lane; _⊕_; _⊕ᴸ_; pendingˢ; coldˢ; ofˢ; doneˢ; joinˢ; mapˢ; scanˢ; takeWhileˢ; flatMapˢ; connectˢ; deferˢ; Lane; lane; Taking; taking; ending; taken; names; laneNames; cutNames; quietName; subjectNames; flatNames; module At; Name; outers; outersL; Feed)
  open StrongAgainst R using (isTaking; seen; seenL; seen-join; seen-up; Each; Lingers; Leaves; Twin; Restful; tw-refl; tw-union; tw-burst; tw-shift; lv-tie; tw-tie; ∧-split; ∧-join; false≢)
  open StrongHeld R using (DoneBy; Flagged; Heads)
  open Tearing R using (Alike; Off; part-alike; partLanes-alike; seen-alike; seenL-alike; names-path; lanes-path; apart-r; apart-l; narrow; each-same)
  open Moving R using (plant; plantᴸ; planted; plantedᴸ; pairs-r; pairs-split)
  open Locality R using (module Heaps)
  open GhostingPaths R using (each-sub; each-lanes)
  open Framing R using (Tells; untold; untoldᴹ; untoldᴸ; heads-map; heads-scan; heads-take; heads-source; shut-heads; just-of; untold-shut; merged-eq; heads-flat)
  open FramingRepool R using (Untold; Ended; ended-head)
  open Keeping R using (leftover-restful)
  open Retagging R using (retag; retagᴸ)
  open Shifting R using (++-mono; module Alive; module Build; DoneByL; EachL; EndedL; module Flag; module Linger; LingersL; UntoldL; _⊆ᴾ_; conn-tw; cons-untold; each-alike; eachL-alike; eachL-head; eachL-of; eachL-tail; en-sub; enL-head; enL-of; enL-tail; filled; flags-alike; flagsL-alike; tw-if-moved; just≢; leftover-alike; leftoverL-alike; lingers-alike; lingers-sub; lingersL-alike; lingersL-head; lingersL-of; lingersL-tail; map-back; map-fwd; pairs-tl; tw-alike; pooledL-alike; seen-take; sourced-heap; untold-at; ut-sub; utL-head; utL-of; utL-tail; via-≡; ∨-l; ∨-mono; ∨-r; ≡-⊆)

  -- Below a live node the path sees, no flag held unset.
  let-go : ∀ {h} (H : Heapᴹ h) {Δ₀ A₀ Δ A} {t : Sub h Δ₀ A₀} {u : Sub h Δ A} (π : Path t u) → AllPairs _≢_ (names t) → seen H π ≡ true
         → is-just (At.part H u) ≡ true → DoneBy H t (outers π) → DoneBy H t []
  let-go H {t = t} π fs sπ ju d = Alive.release H ju {ns = []} π fs sπ (subst (DoneBy H t) (sym (++-identityʳ (outers π))) d)

  -- And back: every outer on the way down still unset.
  grip : ∀ {h} (H : Heapᴹ h) {Δ₀ A₀ Δ A} {t : Sub h Δ₀ A₀} {u : Sub h Δ A} (π : Path t u) → AllPairs _≢_ (names t) → seen H π ≡ true
       → is-just (At.part H u) ≡ true → DoneBy H t [] → DoneBy H t (outers π)
  grip H {t = t} π fs sπ ju d = subst (DoneBy H t) (++-identityʳ (outers π)) (Alive.hold H ju {ns = []} π fs sπ d)

  ----------------------------------------------------------------------
  -- THE WALK: `u` replanted to `v`, the heaps moved only at `u`'s names.
  -- Every node above `u` on the path: its own cells, and every child
  -- beside the path, read alike.

  module Walk {h} (H H′ : Heapᴹ h) {Δ₀ A₀} {u : Sub h Δ₀ A₀} (v : Sub h Δ₀ A₀) (off : Off H H′ (names u))
              (rv₀ : is-just (At.part H′ v) ≡ true → is-just (At.part H u) ≡ true) where
    open Heaps H H′ using (keep; keeps)

    -- Lanes beside the path read alike, apart from `u`'s names.
    module Beside {Δ A B} {s : Sub h Δ A} (ls : List (Lane h Δ B)) (π : Path s u) (Q : AllPairs _≢_ (names s ++ laneNames ls)) where
      apartA : Alike H H′ (laneNames ls)
      apartA = keeps off (λ m → names-path π m) (λ m → apart-l (names s) Q m)

      apartD : ∀ {n} → n ∈ᴸ laneNames ls → n ∈ᴸ names u → ⊥
      apartD m m′ = lookupᴬ (apart-l (names s) Q m) (names-path π m′) refl

      alike : At.partLanes H′ ls ≡ At.partLanes H ls
      alike = partLanes-alike H H′ ls apartA

    -- What a node on the path keeps: its own cells and its other
    -- children, apart from `u`'s names.
    module Take {Δ A} (c : Kit.Cut h) (k : Maybe (Quiet h)) {s : Sub h Δ A} (π : Path s u) (ps : AllPairs _≢_ (cutNames c ++ quietName k ++ names s)) where
      fresh : AllPairs _≢_ (names s)
      fresh = pairs-r (quietName k) (pairs-r (cutNames c) ps)

      live′ : At.val H′ (Kit.live c) ≡ At.val H (Kit.live c)
      live′ = cong lower (keep off (λ m → ++⁺ʳ (quietName k) (names-path π m)) (Kit.live c) (apart-r (cutNames c) ps (here refl)))

    module Outer {Δ A B} (fl : Flat A h) (oc : Kit.Cut h) (k : Maybe (Quiet h)) (r : Sink h ⊤) {so : Sub h Δ A} (ls : List (Lane h Δ B)) (π : Path so u)
                 (ps : AllPairs _≢_ (flatNames fl ++ cutNames oc ++ quietName k ++ (slot _ , r) ∷ names so ++ laneNames ls)) where
      private
        P′ : AllPairs _≢_ (names so ++ laneNames ls)
        P′ = pairs-tl (pairs-r (quietName k) (pairs-r (cutNames oc) (pairs-r (flatNames fl) ps)))

        rest : ∀ {n} → n ∈ᴸ names u → n ∈ᴸ (cutNames oc ++ quietName k ++ (slot _ , r) ∷ names so ++ laneNames ls)
        rest m = ++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ˡ (names-path π m))))

      fresh : AllPairs _≢_ (names so)
      fresh = proj₁ (pairs-split (names so) P′)

      open Beside ls π P′ public using () renaming (apartA to lanesA; apartD to lanesD; alike to lanes)

      queue : look H′ (Flat.queue fl) ≡ look H (Flat.queue fl)
      queue = keep off rest (Flat.queue fl) (apart-r (flatNames fl) ps (there (there (here refl))))

      done : look H′ (Flat.outerDone fl) ≡ look H (Flat.outerDone fl)
      done = keep off rest (Flat.outerDone fl) (apart-r (flatNames fl) ps (there (here refl)))

      doneD : (cell _ , Flat.outerDone fl) ∈ᴸ names u → ⊥
      doneD m = lookupᴬ (apart-r (flatNames fl) ps (there (here refl))) (rest m) refl

    module Lanes {Δ A B} (fl : Flat A h) (oc : Kit.Cut h) (k : Maybe (Quiet h)) (r : Sink h ⊤) (so : Sub h Δ A) {ls : List (Lane h Δ B)} (πL : PathLanes ls u)
                 (ps : AllPairs _≢_ (flatNames fl ++ cutNames oc ++ quietName k ++ (slot _ , r) ∷ names so ++ laneNames ls)) where
      private
        P′ : AllPairs _≢_ (names so ++ laneNames ls)
        P′ = pairs-tl (pairs-r (quietName k) (pairs-r (cutNames oc) (pairs-r (flatNames fl) ps)))

        rest : ∀ {n} → n ∈ᴸ names u → n ∈ᴸ (cutNames oc ++ quietName k ++ (slot _ , r) ∷ names so ++ laneNames ls)
        rest m = ++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ʳ (names so) (lanes-path πL m))))

      fresh : AllPairs _≢_ (laneNames ls)
      fresh = pairs-r (names so) P′

      soA : Alike H H′ (names so)
      soA = keeps off (λ m → lanes-path πL m) (λ m → apart-r (names so) P′ m)

      soD : ∀ {n} → n ∈ᴸ names so → n ∈ᴸ names u → ⊥
      soD m m′ = lookupᴬ (apart-r (names so) P′ m) (lanes-path πL m′) refl

      outer : At.part H′ so ≡ At.part H so
      outer = part-alike H H′ so soA

      queue : look H′ (Flat.queue fl) ≡ look H (Flat.queue fl)
      queue = keep off rest (Flat.queue fl) (apart-r (flatNames fl) ps (there (there (here refl))))

      done : look H′ (Flat.outerDone fl) ≡ look H (Flat.outerDone fl)
      done = keep off rest (Flat.outerDone fl) (apart-r (flatNames fl) ps (there (here refl)))

      doneD : (cell _ , Flat.outerDone fl) ∈ᴸ names u → ⊥
      doneD m = lookupᴬ (apart-r (flatNames fl) ps (there (here refl))) (rest m) refl

    module Source {Δ A B} (S : Subject A h) (c : Kit.Cut h) (b : Ref h (maybe quiet)) (kb k : Maybe (Quiet h)) {src : Sub h Δ A} (bd : Sub h (A ∷ Δ) B)
                  (π : Path src u) (ps : AllPairs _≢_ (subjectNames S ++ cutNames c ++ (cell _ , b) ∷ quietName kb ++ quietName k ++ names src ++ names bd)) where
      private
        Q : AllPairs _≢_ (names src ++ names bd)
        Q = pairs-r (quietName k) (pairs-r (quietName kb) (pairs-tl (pairs-r (cutNames c) (pairs-r (subjectNames S) ps))))

      fresh : AllPairs _≢_ (names src)
      fresh = proj₁ (pairs-split (names src) Q)

      bdA : Alike H H′ (names bd)
      bdA = keeps off (λ m → names-path π m) (λ m → apart-l (names src) Q m)

      bdD : ∀ {n} → n ∈ᴸ names bd → n ∈ᴸ names u → ⊥
      bdD m m′ = lookupᴬ (apart-l (names src) Q m) (names-path π m′) refl

      body : At.part H′ bd ≡ At.part H bd
      body = part-alike H H′ bd bdA

    module Body {Δ A B} (S : Subject A h) (c : Kit.Cut h) (b : Ref h (maybe quiet)) (kb k : Maybe (Quiet h)) (src : Sub h Δ A) {bd : Sub h (A ∷ Δ) B}
                (π : Path bd u) (ps : AllPairs _≢_ (subjectNames S ++ cutNames c ++ (cell _ , b) ∷ quietName kb ++ quietName k ++ names src ++ names bd)) where
      private
        Q : AllPairs _≢_ (names src ++ names bd)
        Q = pairs-r (quietName k) (pairs-r (quietName kb) (pairs-tl (pairs-r (cutNames c) (pairs-r (subjectNames S) ps))))

      fresh : AllPairs _≢_ (names bd)
      fresh = pairs-r (names src) Q

      srcA : Alike H H′ (names src)
      srcA = keeps off (λ m → names-path π m) (λ m → apart-r (names src) Q m)

      srcD : ∀ {n} → n ∈ᴸ names src → n ∈ᴸ names u → ⊥
      srcD m m′ = lookupᴬ (apart-r (names src) Q m) (names-path π m′) refl

      source : At.part H′ src ≡ At.part H src
      source = part-alike H H′ src srcA

    module This {Δ B} (c : Kit.Cut h) (k : Maybe (Quiet h)) {s : Sub h Δ B} (ls : List (Lane h Δ B)) (π : Path s u)
                (ps : AllPairs _≢_ (cutNames c ++ quietName k ++ names s ++ laneNames ls)) where
      private
        Q : AllPairs _≢_ (names s ++ laneNames ls)
        Q = pairs-r (quietName k) (pairs-r (cutNames c) ps)

      fresh : AllPairs _≢_ (names s)
      fresh = proj₁ (pairs-split (names s) Q)

      open Beside ls π Q public using () renaming (apartA to restA; apartD to restD; alike to rest)

      live′ : At.val H′ (Kit.live c) ≡ At.val H (Kit.live c)
      live′ = cong lower (keep off (λ m → ++⁺ʳ (quietName k) (++⁺ˡ (names-path π m))) (Kit.live c) (apart-r (cutNames c) ps (here refl)))

      on : At.val H′ (Kit.live c) ≡ true → At.val H (Kit.live c) ≡ true
      on lv = trans (sym live′) lv

    module Next {Δ B} (c : Kit.Cut h) (k : Maybe (Quiet h)) (s : Sub h Δ B) {ls : List (Lane h Δ B)} (πL : PathLanes ls u)
                (ps : AllPairs _≢_ (cutNames c ++ quietName k ++ names s ++ laneNames ls)) where
      private
        Q : AllPairs _≢_ (names s ++ laneNames ls)
        Q = pairs-r (quietName k) (pairs-r (cutNames c) ps)

      fresh : AllPairs _≢_ (laneNames ls)
      fresh = pairs-r (names s) Q

      headA : Alike H H′ (names s)
      headA = keeps off (λ m → lanes-path πL m) (λ m → apart-r (names s) Q m)

      headD : ∀ {n} → n ∈ᴸ names s → n ∈ᴸ names u → ⊥
      headD m m′ = lookupᴬ (apart-r (names s) Q m) (lanes-path πL m′) refl

      head : At.part H′ s ≡ At.part H s
      head = part-alike H H′ s headA

      live′ : At.val H′ (Kit.live c) ≡ At.val H (Kit.live c)
      live′ = cong lower (keep off (λ m → ++⁺ʳ (quietName k) (++⁺ʳ (names s) (lanes-path πL m))) (Kit.live c) (apart-r (cutNames c) ps (here refl)))

      on : At.val H′ (Kit.live c) ≡ true → At.val H (Kit.live c) ≡ true
      on lv = trans (sym live′) lv

    --------------------------------------------------------------------
    -- NO PART REVIVED: a node the write leaves held was held before.

    take-rev : ∀ {Δ A} ib (p : A → Bool) (tk : Taking Δ A) (m m′ : Maybe (U.Node Δ A)) {b b′} → b′ ≡ b → (is-just m′ ≡ true → is-just m ≡ true)
             → is-just (if b′ then At.taking? H′ ib p tk m′ else nothing) ≡ true → is-just (if b then At.taking? H ib p tk m else nothing) ≡ true
    take-rev ib p tk           m        m′       {false} refl rm ()
    take-rev ib p taking       (just _) m′       {true}  refl rm j = refl
    take-rev ib p taking       nothing  (just _) {true}  refl rm j = false≢ (rm refl)
    take-rev ib p taking       nothing  nothing  {true}  refl rm ()
    take-rev ib p (ending _ _) m        m′       {true}  refl rm j = refl
    take-rev ib p taken        m        m′       {true}  refl rm ()

    lane-rev : ∀ {Δ B} {b b′} → b′ ≡ b → (m m′ : Maybe (U.Node Δ B)) (L L′ : List (U.Node Δ B))
             → (is-just m′ ≡ true → is-just m ≡ true) → (filled L′ ≡ true → filled L ≡ true)
             → filled (if b′ then At.consᴹ H′ m′ L′ else L′) ≡ true → filled (if b then At.consᴹ H m L else L) ≡ true
    lane-rev {b = false} refl m        m′       L L′ rm rL j = rL j
    lane-rev {b = true}  refl (just _) m′       L L′ rm rL j = refl
    lane-rev {b = true}  refl nothing  (just _) L L′ rm rL j = false≢ (rm refl)
    lane-rev {b = true}  refl nothing  nothing  L L′ rm rL j = rL j

    merged-rev : ∀ {Δ A B} op (g : A → Pos → U.Node Δ B) (o o′ : Maybe (U.Node Δ A)) (L L′ : List (U.Node Δ B)) (Q Q′ : List A) pl
               → (is-just o′ ≡ true → is-just o ≡ true) → (filled L′ ≡ true → filled L ≡ true) → (filled Q′ ≡ true → filled Q ≡ true)
               → is-just (At.merged H′ op g o′ L′ Q′ pl) ≡ true → is-just (At.merged H op g o L Q pl) ≡ true
    merged-rev op g (just _) o′       L       L′      Q       Q′      pl ro rL rQ j = refl
    merged-rev op g nothing  o′       (_ ∷ _) L′      Q       Q′      pl ro rL rQ j = refl
    merged-rev op g nothing  o′       []      L′      (_ ∷ _) Q′      pl ro rL rQ j = refl
    merged-rev op g nothing  (just _) []      L′      []      Q′      pl ro rL rQ j = false≢ (ro refl)
    merged-rev op g nothing  nothing  []      (_ ∷ _) []      Q′      pl ro rL rQ j = false≢ (rL refl)
    merged-rev op g nothing  nothing  []      []      []      (_ ∷ _) pl ro rL rQ j = false≢ (rQ refl)
    merged-rev op g nothing  nothing  []      []      []      []      pl ro rL rQ ()

    conn-rev : ∀ {Δ A B} rp (e : Maybe Pos) (rt : U.Node Δ A) (s s′ : Maybe (U.Node Δ A)) (mb mb′ : Maybe (U.Node (A ∷ Δ) B))
             → (is-just s′ ≡ true → is-just s ≡ true) → (is-just mb′ ≡ true → is-just mb ≡ true)
             → is-just (At.connected H′ rp e rt s′ mb′) ≡ true → is-just (At.connected H rp e rt s mb) ≡ true
    conn-rev rp e        rt s        s′       nothing  (just _) rs rb j = false≢ (rb refl)
    conn-rev rp e        rt s        s′       nothing  nothing  rs rb ()
    conn-rev rp e        rt (just _) s′       (just _) mb′      rs rb j = refl
    conn-rev rp (just _) rt nothing  s′       (just _) mb′      rs rb j = refl
    conn-rev rp nothing  rt nothing  (just _) (just _) mb′      rs rb j = false≢ (rs refl)
    conn-rev rp nothing  rt nothing  nothing  (just _) (just _) rs rb ()
    conn-rev rp nothing  rt nothing  nothing  (just _) nothing  rs rb ()

    mutual
      revive : ∀ {Δ A} {t : Sub h Δ A} (π : Path t u) → AllPairs _≢_ (names t) → is-just (At.part H′ (plant π v)) ≡ true → is-just (At.part H t) ≡ true
      revive here ps = rv₀
      revive (in-map {f = f} {t = s} π) ps j =
        map-fwd H (U.mapᶜ f) (At.part H s) (revive π ps (map-back H′ (U.mapᶜ f) (At.part H′ (plant π v)) j))
      revive (in-scan {f = f} {r} {t = s} π) ps j =
        map-fwd H (U.scanᶜ f (At.val H r)) (At.part H s) (revive π (pairs-tl ps) (map-back H′ (U.scanᶜ f (At.val H′ r)) (At.part H′ (plant π v)) j))
      revive (in-take {i = ib} {p} {c} {k} {tk} {t = s} π) ps =
        take-rev ib p tk (At.part H s) (At.part H′ (plant π v)) Tk.live′ (revive π Tk.fresh)
        where module Tk = Take c k π ps
      revive (in-outer {op = op} {f} {fl} {oc} {k} {r} {pl} {t = so} {ls} π) ps =
        merged-rev op (λ a q → U.subscribe (f a) q) (At.part H so) (At.part H′ (plant π v)) (At.partLanes H ls) (At.partLanes H′ ls)
          (At.val H (Flat.queue fl)) (At.val H′ (Flat.queue fl)) pl (revive π O.fresh) (via-≡ filled O.lanes) (via-≡ filled (cong lower O.queue))
        where module O = Outer fl oc k r ls π ps
      revive (in-lanes {op = op} {f} {fl} {oc} {k} {r} {pl} {t = so} {ls} πL) ps =
        merged-rev op (λ a q → U.subscribe (f a) q) (At.part H so) (At.part H′ so) (At.partLanes H ls) (At.partLanes H′ (plantᴸ πL v))
          (At.val H (Flat.queue fl)) (At.val H′ (Flat.queue fl)) pl (via-≡ is-just Ln.outer) (reviveL πL Ln.fresh) (via-≡ filled (cong lower Ln.queue))
        where module Ln = Lanes fl oc k r so πL ps
      revive (in-source {S = S} {c} {b} {kb} {k} {e = e} {rp} {rt} {t = src} {bd} π) ps =
        conn-rev rp e rt (At.part H src) (At.part H′ (plant π v)) (At.part H bd) (At.part H′ bd) (revive π Sr.fresh) (via-≡ is-just Sr.body)
        where module Sr = Source S c b kb k bd π ps
      revive (in-body {S = S} {c} {b} {kb} {k} {e = e} {rp} {rt} {t = src} {bd} π) ps =
        conn-rev rp e rt (At.part H src) (At.part H′ src) (At.part H bd) (At.part H′ (plant π v)) (via-≡ is-just Bd.source) (revive π Bd.fresh)
        where module Bd = Body S c b kb k src π ps
      revive (in-defer {k = k} π) ps = revive π (pairs-r (quietName k) ps)

      reviveL : ∀ {Δ B} {ls : List (Lane h Δ B)} (πL : PathLanes ls u) → AllPairs _≢_ (laneNames ls)
              → filled (At.partLanes H′ (plantᴸ πL v)) ≡ true → filled (At.partLanes H ls) ≡ true
      reviveL (this-lane {c = c} {k} {t = s} {ls} π) ps =
        lane-rev Th.live′ (At.part H s) (At.part H′ (plant π v)) (At.partLanes H ls) (At.partLanes H′ ls) (revive π Th.fresh) (via-≡ filled Th.rest)
        where module Th = This c k ls π ps
      reviveL (next-lane {l = lane c k s} {ls} πL) ps =
        lane-rev Nx.live′ (At.part H s) (At.part H′ s) (At.partLanes H ls) (At.partLanes H′ (plantᴸ πL v)) (via-≡ is-just Nx.head) (reviveL πL Nx.fresh)
        where module Nx = Next c k s πL ps

    -- A node held after the write, read where it was held before.
    held : ∀ {ℓ} {X : Set ℓ} {Δ A} {t : Sub h Δ A} (π : Path t u) → AllPairs _≢_ (names t)
         → ∀ {n} → At.part H′ (plant π v) ≡ just n → (∀ {n₀} → At.part H t ≡ just n₀ → X) → X
    held π ps x k = k (proj₂ (just-of (revive π ps (cong is-just x))))

    --------------------------------------------------------------------
    -- DONE FLAGS, KEPT: every flag named above the write still unset, and
    -- every other reading its outer as before, the names below `u` let go.

    module Flags (X ns₀ : List (Name h)) (nu : ∀ {n} → n ∈ᴸ ns₀ → n ∈ᴸ names u) (fb₀ : DoneBy H u (X ++ ns₀) → DoneBy H′ v X) where
      module FG = Flag H′

      private
        drop : ∀ {Δ A} {x : Sub h Δ A} → (∀ {n} → n ∈ᴸ names x → n ∈ᴸ names u → ⊥) → ∀ {n} → n ∈ᴸ names x → n ∈ᴸ X ++ ns₀ → n ∈ᴸ X
        drop D m m′ = [ (λ a → a) , (λ b → ⊥-elim (D m (nu b))) ]′ (++⁻ X m′)

        dropL : ∀ {Δ B} {ls : List (Lane h Δ B)} → (∀ {n} → n ∈ᴸ laneNames ls → n ∈ᴸ names u → ⊥) → ∀ {n} → n ∈ᴸ laneNames ls → n ∈ᴸ X ++ ns₀ → n ∈ᴸ X
        dropL D m m′ = [ (λ a → a) , (λ b → ⊥-elim (D m (nu b))) ]′ (++⁻ X m′)

        beside : ∀ {Δ A} {x : Sub h Δ A} → (∀ {n} → n ∈ᴸ names x → n ∈ᴸ names u → ⊥) → Alike H H′ (names x) → DoneBy H x (X ++ ns₀) → DoneBy H′ x X
        beside {x = x} D al d = flags-alike H H′ al (Flag.relist H {t = x} (λ _ m → ++⁺ˡ m) (drop {x = x} D) d)

        besideL : ∀ {Δ B} {ls : List (Lane h Δ B)} → (∀ {n} → n ∈ᴸ laneNames ls → n ∈ᴸ names u → ⊥) → Alike H H′ (laneNames ls)
                → DoneByL H ls (X ++ ns₀) → DoneByL H′ ls X
        besideL {ls = ls} D al dL = flagsL-alike H H′ al (Flag.relistL H {ls = ls} (λ _ m → ++⁺ˡ m) (dropL {ls = ls} D) dL)

        unnamed : ∀ {n} → (n ∈ᴸ names u → ⊥) → (n ∈ᴸ X → ⊥) → n ∈ᴸ X ++ ns₀ → ⊥
        unnamed D x m = [ x , (λ b → D (nu b)) ]′ (++⁻ X m)

      mutual
        shiftF : ∀ {Δ A} {t : Sub h Δ A} (π : Path t u) → AllPairs _≢_ (names t) → (∀ {n} → n ∈ᴸ outers π → n ∈ᴸ X)
               → DoneBy H t (X ++ ns₀) → DoneBy H′ (plant π v) X
        shiftF here ps ox d = fb₀ d
        shiftF (in-map π) ps ox d = FG.db-map (shiftF π ps ox (Flag.db-sub H d (in-map here) refl))
        shiftF (in-scan π) ps ox d = FG.db-scan (shiftF π (pairs-tl ps) ox (Flag.db-sub H d (in-scan here) refl))
        shiftF (in-take {c = c} {k} {tk} π) ps ox d =
          FG.db-take (λ ok → shiftF π Tk.fresh ox (Flag.db-sub H d (in-take here) (seen-take (At.val H (Kit.live c)) (via-≡ (λ z → z ∧ isTaking tk) Tk.live′ ok))))
          where module Tk = Take c k π ps
        shiftF (in-outer {fl = fl} {oc} {k} {r} {t = so} {ls} π) ps ox d =
          FG.db-flat ((λ m → trans (cong lower O.done) (proj₁ (d here refl) (++⁺ˡ m))) , (λ m̸ → ⊥-elim (m̸ (ox (here refl)))))
                     (shiftF π O.fresh (λ m → ox (there m)) (Flag.db-sub H d (in-outer here) refl))
                     (besideL O.lanesD O.lanesA (Flag.dbL-of H d))
          where module O = Outer fl oc k r ls π ps
        shiftF (in-lanes {fl = fl} {oc} {k} {r} {t = so} πL) ps ox d =
          FG.db-flat ((λ m → trans (cong lower Ln.done) (proj₁ (d here refl) (++⁺ˡ m)))
                     , (λ m̸ → trans (cong lower Ln.done) (trans (proj₂ (d here refl) (unnamed Ln.doneD m̸)) (cong is-nothing (sym Ln.outer)))))
                     (beside Ln.soD Ln.soA (Flag.db-sub H d (in-outer here) refl))
                     (shiftFL πL Ln.fresh ox (Flag.dbL-of H d))
          where module Ln = Lanes fl oc k r so πL ps
        shiftF (in-source {S = S} {c} {b} {kb} {k} {e = e} {t = src} {bd} π) ps ox d =
          FG.db-connect (λ jb → shiftF π Sr.fresh ox (Flag.db-sub H d (in-source here) (∧-join (via-≡ is-just Sr.body jb) refl)))
                        (λ js → beside Sr.bdD Sr.bdA (Flag.db-sub H d (in-body here) (∧-join (∨-mono (is-just e) (revive π Sr.fresh) js) refl)))
          where module Sr = Source S c b kb k bd π ps
        shiftF (in-body {S = S} {c} {b} {kb} {k} {e = e} {t = src} {bd} π) ps ox d =
          FG.db-connect (λ jb → beside Bd.srcD Bd.srcA (Flag.db-sub H d (in-source here) (∧-join (revive π Bd.fresh jb) refl)))
                        (λ js → shiftF π Bd.fresh ox (Flag.db-sub H d (in-body here) (∧-join (∨-mono (is-just e) (via-≡ is-just Bd.source) js) refl)))
          where module Bd = Body S c b kb k src π ps
        shiftF (in-defer {k = k} π) ps ox d = FG.db-defer (shiftF π (pairs-r (quietName k) ps) ox (Flag.db-sub H d (in-defer here) refl))

        shiftFL : ∀ {Δ B} {ls : List (Lane h Δ B)} (πL : PathLanes ls u) → AllPairs _≢_ (laneNames ls) → (∀ {n} → n ∈ᴸ outersL πL → n ∈ᴸ X)
                → DoneByL H ls (X ++ ns₀) → DoneByL H′ (plantᴸ πL v) X
        shiftFL (this-lane {c = c} {k} {t = s} {ls} π) ps ox dL =
          FG.dbL-cons (λ lv → shiftF π Th.fresh ox (Flag.dbL-head H dL (Th.on lv))) (besideL Th.restD Th.restA (Flag.dbL-tail H dL))
          where module Th = This c k ls π ps
        shiftFL (next-lane {l = lane c k s} {ls} πL) ps ox dL =
          FG.dbL-cons (λ lv → beside Nx.headD Nx.headA (Flag.dbL-head H dL (Nx.on lv))) (shiftFL πL Nx.fresh ox (Flag.dbL-tail H dL))
          where module Nx = Next c k s πL ps

    --------------------------------------------------------------------
    -- NO JOINER NEWLY UNTOLD: what a node above leaves untold its
    -- joiners after the write, it left untold before.

    module Telling (tl₀ : ∀ {C} (i : C ∈ᴸ Δ₀) {b₀ b′} → At.part H u ≡ just b₀ → At.part H′ v ≡ just b′ → untold i b′ ⊆ᴾ untold i b₀) where
      untold-≡ : ∀ {Γ B C} (i : C ∈ᴸ Γ) {x x′ y y′ : U.Node Γ B} → x ≡ y → x′ ≡ y′ → untold i x′ ⊆ᴾ untold i x → untold i y′ ⊆ᴾ untold i y
      untold-≡ i refl refl s = s

      told-ᴹ : ∀ {Δ A B C} (i : C ∈ᴸ Δ) (g g′ : U.Node Δ A → U.Node Δ B) → (∀ c → untold i (g c) ≡ untold i c) → (∀ c → untold i (g′ c) ≡ untold i c)
             → (m m′ : Maybe (U.Node Δ A)) → ∀ {b₀ b′} → At.mapᴹ H g m ≡ just b₀ → At.mapᴹ H′ g′ m′ ≡ just b′
             → (∀ {c c′} → m ≡ just c → m′ ≡ just c′ → untold i c′ ⊆ᴾ untold i c) → untold i b′ ⊆ᴾ untold i b₀
      told-ᴹ i g g′ up up′ (just c) (just c′) refl refl sub = λ m → ≡-⊆ (sym (up c)) (sub refl refl (≡-⊆ (up′ c′) m))
      told-ᴹ i g g′ up up′ nothing  m′        ()   e′   sub
      told-ᴹ i g g′ up up′ (just c) nothing   e₀   ()   sub

      told-take : ∀ {Δ A C} (i : C ∈ᴸ Δ) ib (p : A → Bool) (tk : Taking Δ A) (m m′ : Maybe (U.Node Δ A)) {b b′} → b′ ≡ b
                → ∀ {b₀ b₁} → (if b then At.taking? H ib p tk m else nothing) ≡ just b₀ → (if b′ then At.taking? H′ ib p tk m′ else nothing) ≡ just b₁
                → (b ∧ isTaking tk ≡ true → ∀ {c c′} → m ≡ just c → m′ ≡ just c′ → untold i c′ ⊆ᴾ untold i c) → untold i b₁ ⊆ᴾ untold i b₀
      told-take i ib p tk           m m′ {b = false} refl ()   e′   sub
      told-take i ib p taking       m m′ {b = true}  refl e₀   e′   sub =
        told-ᴹ i (U.takeWhileᶜ ib p) (U.takeWhileᶜ ib p) (λ _ → refl) (λ _ → refl) m m′ e₀ e′ (sub refl)
      told-take i ib p (ending _ _) m m′ {b = true}  refl refl refl sub = λ x → x
      told-take i ib p taken        m m′ {b = true}  refl ()   e′   sub

      toldᴹ : ∀ {Δ B C} (i : C ∈ᴸ Δ) (m m′ : Maybe (U.Node Δ B)) → (∀ {c c′} → m ≡ just c → m′ ≡ just c′ → untold i c′ ⊆ᴾ untold i c)
            → (is-just m′ ≡ true → is-just m ≡ true) → untoldᴹ i m′ ⊆ᴾ untoldᴹ i m
      toldᴹ i m        nothing   sub rv = λ ()
      toldᴹ i (just c) (just c′) sub rv = sub refl refl
      toldᴹ i nothing  (just c′) sub rv = false≢ (rv refl)

      flat-told : ∀ {Δ A B C} (i : C ∈ᴸ Δ) op (g : A → Pos → U.Node Δ B) (o o′ : Maybe (U.Node Δ A)) (L L′ : List (U.Node Δ B)) (Q Q′ : List A) pl
                → untoldᴹ i o′ ⊆ᴾ untoldᴹ i o → untoldᴸ i L′ ⊆ᴾ untoldᴸ i L → Q′ ≡ Q
                → ∀ {b₀ b′} → At.merged H op g o L Q pl ≡ just b₀ → At.merged H′ op g o′ L′ Q′ pl ≡ just b′ → untold i b′ ⊆ᴾ untold i b₀
      flat-told i op g o o′ L L′ Q _ pl so sL refl e₀ e′ =
        untold-≡ i (merged-eq H op g o L Q pl e₀) (merged-eq H′ op g o′ L′ Q pl e′)
          (++-mono (untoldᴹ i o) (untoldᴹ i o′) so (++-mono (untoldᴸ i L) (untoldᴸ i L′) sL (λ m → m)))

      lane-told : ∀ {Δ B C} (i : C ∈ᴸ Δ) {b b′} → b′ ≡ b → (m m′ : Maybe (U.Node Δ B)) (L L′ : List (U.Node Δ B))
                → (b ≡ true → untoldᴹ i m′ ⊆ᴾ untoldᴹ i m) → untoldᴸ i L′ ⊆ᴾ untoldᴸ i L
                → untoldᴸ i (if b′ then At.consᴹ H′ m′ L′ else L′) ⊆ᴾ untoldᴸ i (if b then At.consᴹ H m L else L)
      lane-told i {b = false} refl m m′ L L′ fm fL = fL
      lane-told i {b = true}  refl m m′ L L′ fm fL =
        λ x → ≡-⊆ (sym (cons-untold H i m L)) (++-mono (untoldᴹ i m) (untoldᴹ i m′) (fm refl) fL (≡-⊆ (cons-untold H′ i m′ L′) x))

      -- The source replanted: a source still running past an end is
      -- refuted by the end, and one gone on both sides tells alike.
      src-told : ∀ {Δ A B C} (i : C ∈ᴸ Δ) rp (e : Maybe Pos) (rt : U.Node Δ A) (s s′ : Maybe (U.Node Δ A)) (mb : Maybe (U.Node (A ∷ Δ) B))
               → (is-just s′ ≡ true → is-just s ≡ true)
               → (is-just mb ≡ true → ∀ {c c′} → s ≡ just c → s′ ≡ just c′ → untold i c′ ⊆ᴾ untold i c)
               → (∀ {n} → At.connected H rp e rt s mb ≡ just n → ∀ {c₀} → e ≡ just c₀ → s ≡ nothing)
               → ∀ {b₀ b′} → At.connected H rp e rt s mb ≡ just b₀ → At.connected H′ rp e rt s′ mb ≡ just b′ → untold i b′ ⊆ᴾ untold i b₀
      src-told i rp e        rt s        s′        nothing  rv sub en ()   e′
      src-told i rp e        rt (just c) (just c′) (just b) rv sub en refl refl = ++-mono (untold (there i) b) (untold (there i) b) (λ m → m) (sub refl refl refl)
      src-told i rp (just x) rt (just c) nothing   (just b) rv sub en e₀   e′   = just≢ (en e₀ refl)
      src-told i rp nothing  rt (just c) nothing   (just b) rv sub en e₀   ()
      src-told i rp e        rt nothing  (just c′) (just b) rv sub en e₀   e′   = false≢ (rv refl)
      src-told i rp (just x) rt nothing  nothing   (just b) rv sub en refl refl = λ m → m
      src-told i rp nothing  rt nothing  nothing   (just b) rv sub en ()   e′

      -- The body replanted: its joiners read one frame down, through a
      -- shut when the source has ended.
      body-told : ∀ {Δ A B C} (i : C ∈ᴸ Δ) rp (e : Maybe Pos) (rt : U.Node Δ A) (s : Maybe (U.Node Δ A)) (mb mb′ : Maybe (U.Node (A ∷ Δ) B))
                → (is-just mb′ ≡ true → is-just mb ≡ true)
                → ((is-just s ∨ is-just e) ≡ true → ∀ {c c′} → mb ≡ just c → mb′ ≡ just c′ → untold (there i) c′ ⊆ᴾ untold (there i) c)
                → ∀ {b₀ b′} → At.connected H rp e rt s mb ≡ just b₀ → At.connected H′ rp e rt s mb′ ≡ just b′ → untold i b′ ⊆ᴾ untold i b₀
      body-told i rp e        rt s        mb       nothing   rv sub e₀   ()
      body-told i rp e        rt s        nothing  (just b′) rv sub e₀   e′   = false≢ (rv refl)
      body-told i rp e        rt (just c) (just b) (just b′) rv sub refl refl = ++-mono (untold (there i) b) (untold (there i) b′) (sub refl refl refl) (λ m → m)
      body-told i rp (just x) rt nothing  (just b) (just b′) rv sub refl refl =
        ++-mono (untold (there i) (U.shut (here refl) x b)) (untold (there i) (U.shut (here refl) x b′))
          (λ m → ≡-⊆ (sym (untold-shut i x b)) (sub refl refl refl (≡-⊆ (untold-shut i x b′) m))) (λ m → m)
      body-told i rp nothing  rt nothing  (just b) (just b′) rv sub ()   e′

      mutual
        told : ∀ {Δ A} {t : Sub h Δ A} (π : Path t u) → AllPairs _≢_ (names t) → Ended H t
             → ∀ {C} (i : C ∈ᴸ Δ) {b₀ b′} → At.part H t ≡ just b₀ → At.part H′ (plant π v) ≡ just b′ → untold i b′ ⊆ᴾ untold i b₀
        told here ps en i e₀ e′ = tl₀ i e₀ e′
        told (in-map {f = f} {t = s} π) ps en i e₀ e′ =
          told-ᴹ i (U.mapᶜ f) (U.mapᶜ f) (λ _ → refl) (λ _ → refl) (At.part H s) (At.part H′ (plant π v)) e₀ e′
            (told π ps (en-sub H en (in-map here) refl) i)
        told (in-scan {f = f} {r} {t = s} π) ps en i e₀ e′ =
          told-ᴹ i (U.scanᶜ f (At.val H r)) (U.scanᶜ f (At.val H′ r)) (λ _ → refl) (λ _ → refl) (At.part H s) (At.part H′ (plant π v)) e₀ e′
            (told π (pairs-tl ps) (en-sub H en (in-scan here) refl) i)
        told (in-take {i = ib} {p} {c} {k} {tk} {t = s} π) ps en i e₀ e′ =
          told-take i ib p tk (At.part H s) (At.part H′ (plant π v)) Tk.live′ e₀ e′
            (λ ok → told π Tk.fresh (en-sub H en (in-take here) (seen-take (At.val H (Kit.live c)) ok)) i)
          where module Tk = Take c k π ps
        told (in-outer {op = op} {f} {fl} {oc} {k} {r} {pl} {t = so} {ls} π) ps en i e₀ e′ =
          flat-told i op (λ a q → U.subscribe (f a) q) (At.part H so) (At.part H′ (plant π v)) (At.partLanes H ls) (At.partLanes H′ ls)
            (At.val H (Flat.queue fl)) (At.val H′ (Flat.queue fl)) pl
            (toldᴹ i (At.part H so) (At.part H′ (plant π v)) (told π O.fresh (en-sub H en (in-outer here) refl) i) (revive π O.fresh))
            (≡-⊆ (cong (untoldᴸ i) O.lanes)) (cong lower O.queue) e₀ e′
          where module O = Outer fl oc k r ls π ps
        told (in-lanes {op = op} {f} {fl} {oc} {k} {r} {pl} {t = so} {ls} πL) ps en i e₀ e′ =
          flat-told i op (λ a q → U.subscribe (f a) q) (At.part H so) (At.part H′ so) (At.partLanes H ls) (At.partLanes H′ (plantᴸ πL v))
            (At.val H (Flat.queue fl)) (At.val H′ (Flat.queue fl)) pl
            (≡-⊆ (cong (untoldᴹ i) Ln.outer)) (toldL πL Ln.fresh (enL-of H en) i) (cong lower Ln.queue) e₀ e′
          where module Ln = Lanes fl oc k r so πL ps
        told (in-source {S = S} {c} {b} {kb} {k} {e = e} {rp} {rt} {t = src} {bd} π) ps en i {b′ = b′} e₀ e′ =
          src-told i rp e rt (At.part H src) (At.part H′ (plant π v)) (At.part H bd) (revive π Sr.fresh)
            (λ jb → told π Sr.fresh (en-sub H en (in-source here) (∧-join jb refl)) i) (en here refl) e₀
            (subst (λ z → At.connected H′ rp e rt (At.part H′ (plant π v)) z ≡ just b′) Sr.body e′)
          where module Sr = Source S c b kb k bd π ps
        told (in-body {S = S} {c} {b} {kb} {k} {e = e} {rp} {rt} {t = src} {bd} π) ps en i {b′ = b′} e₀ e′ =
          body-told i rp e rt (At.part H src) (At.part H bd) (At.part H′ (plant π v)) (revive π Bd.fresh)
            (λ js → told π Bd.fresh (en-sub H en (in-body here) (∧-join js refl)) (there i)) e₀
            (subst (λ z → At.connected H′ rp e rt z (At.part H′ (plant π v)) ≡ just b′) Bd.source e′)
          where module Bd = Body S c b kb k src π ps
        told (in-defer {k = k} π) ps en i e₀ e′ = told π (pairs-r (quietName k) ps) (en-sub H en (in-defer here) refl) i e₀ e′

        toldL : ∀ {Δ B} {ls : List (Lane h Δ B)} (πL : PathLanes ls u) → AllPairs _≢_ (laneNames ls) → EndedL H ls
              → ∀ {C} (i : C ∈ᴸ Δ) → untoldᴸ i (At.partLanes H′ (plantᴸ πL v)) ⊆ᴾ untoldᴸ i (At.partLanes H ls)
        toldL (this-lane {c = c} {k} {t = s} {ls} π) ps en i =
          lane-told i Th.live′ (At.part H s) (At.part H′ (plant π v)) (At.partLanes H ls) (At.partLanes H′ ls)
            (λ lv → toldᴹ i (At.part H s) (At.part H′ (plant π v)) (told π Th.fresh (enL-head H en lv) i) (revive π Th.fresh))
            (≡-⊆ (cong (untoldᴸ i) Th.rest))
          where module Th = This c k ls π ps
        toldL (next-lane {l = lane c k s} {ls} πL) ps en i =
          lane-told i Nx.live′ (At.part H s) (At.part H′ s) (At.partLanes H ls) (At.partLanes H′ (plantᴸ πL v))
            (λ _ → ≡-⊆ (cong (untoldᴹ i) Nx.head)) (toldL πL Nx.fresh (enL-tail H en) i)
          where module Nx = Next c k s πL ps

    --------------------------------------------------------------------
    -- NO HEAD BEFORE `q`: every node above heads no sooner after the
    -- write than before.

    module Behind (tl₀ : ∀ {C} (i : C ∈ᴸ Δ₀) {b₀ b′} → At.part H u ≡ just b₀ → At.part H′ v ≡ just b′ → untold i b′ ⊆ᴾ untold i b₀)
                  (q : Pos) (bl₀ : Each H (Heads q) u → Each H′ (Heads q) v) where
      open Telling tl₀

      P : ∀ {Γ A} → U.Node Γ A → Set
      P c = Heads q c

      module BH = Build H′ P

      lift-ᴹ : ∀ {Δ A B} (G : Heapᴹ h) (g : U.Node Δ A → U.Node Δ B) (m : Maybe (U.Node Δ A)) → (∀ c → P c → P (g c))
             → (∀ {c} → m ≡ just c → P c) → ∀ {c} → At.mapᴹ G g m ≡ just c → P c
      lift-ᴹ G g (just c) up hm refl = up c (hm refl)
      lift-ᴹ G g nothing  up hm ()

      take-up : ∀ {Δ A} ib (p : A → Bool) (tk : Taking Δ A) (m m′ : Maybe (U.Node Δ A)) {b b′} → b′ ≡ b
              → (∀ {c} → (if b then At.taking? H ib p tk m else nothing) ≡ just c → P c)
              → (b ∧ isTaking tk ≡ true → ∀ {c} → m′ ≡ just c → P c)
              → ∀ {c} → (if b′ then At.taking? H′ ib p tk m′ else nothing) ≡ just c → P c
      take-up ib p tk           m m′        {b = false} refl old up ()
      take-up ib p taking       m (just c′) {b = true}  refl old up refl = heads-take ib p {c′} (up refl refl)
      take-up ib p taking       m nothing   {b = true}  refl old up ()
      take-up ib p (ending _ _) m m′        {b = true}  refl old up refl = old refl
      take-up ib p taken        m m′        {b = true}  refl old up ()

      root-flat : ∀ {Δ A B} op (g : A → Pos → U.Node Δ B) (o′ : Maybe (U.Node Δ A)) (L′ : List (U.Node Δ B)) (Q : List A) pl
                → P pl → (∀ {c} → o′ ≡ just c → P c) → All P L′
                → ∀ {c} → At.merged H′ op g o′ L′ Q pl ≡ just c → P c
      root-flat op g o′ L′ Q pl hp ho hL x = subst P (merged-eq H′ op g o′ L′ Q pl x) (heads-flat op g o′ L′ Q pl hp ho hL)

      -- The source replanted: a source running on either side heads
      -- the connect beside its body; past the end, nothing moved.
      src-up : ∀ {Δ A B} rp (e : Maybe Pos) (rt : U.Node Δ A) (s s′ : Maybe (U.Node Δ A)) (mb : Maybe (U.Node (A ∷ Δ) B))
             → (∀ {c} → At.connected H rp e rt s mb ≡ just c → P c)
             → (∀ {n} → At.connected H rp e rt s mb ≡ just n → ∀ {c₀} → e ≡ just c₀ → s ≡ nothing)
             → (is-just s′ ≡ true → is-just s ≡ true)
             → (is-just mb ≡ true → ∀ {c} → s′ ≡ just c → P c)
             → ((is-just s ∨ is-just e) ≡ true → ∀ {c} → mb ≡ just c → P c)
             → ∀ {c} → At.connected H′ rp e rt s′ mb ≡ just c → P c
      src-up rp e        rt s        s′        nothing  old en rv hs hb ()
      src-up rp e        rt s        (just c′) (just b) old en rv hs hb refl = heads-source rp {b} {c′} (hs refl refl) (hb (∨-l (rv refl)) refl)
      src-up rp (just x) rt (just c) nothing   (just b) old en rv hs hb _    = just≢ (en refl refl)
      src-up rp (just x) rt nothing  nothing   (just b) old en rv hs hb refl = old refl
      src-up rp nothing  rt s        nothing   (just b) old en rv hs hb ()

      -- The body replanted: past the source's end the new body heads
      -- through a shut, telling only what the old body left untold.
      body-up : ∀ {Δ A B} rp (e : Maybe Pos) (rt : U.Node Δ A) (s : Maybe (U.Node Δ A)) (mb mb′ : Maybe (U.Node (A ∷ Δ) B))
              → (is-just mb′ ≡ true → is-just mb ≡ true)
              → (is-just mb ≡ true → ∀ {c} → s ≡ just c → P c)
              → ((is-just s ∨ is-just e) ≡ true → ∀ {c} → mb′ ≡ just c → P c)
              → ((is-just s ∨ is-just e) ≡ true → ∀ {b₀ b′} → mb ≡ just b₀ → mb′ ≡ just b′ → untold (here refl) b′ ⊆ᴾ untold (here refl) b₀)
              → (∀ {c₀} → e ≡ just c₀ → s ≡ nothing → ∀ {b₀} → mb ≡ just b₀ → Tells q c₀ (untold (here refl) b₀))
              → (∀ {n} → At.connected H rp e rt s mb ≡ just n → s ≡ nothing → ∀ {c₀} → e ≡ just c₀ → P rt)
              → ∀ {c} → At.connected H′ rp e rt s mb′ ≡ just c → P c
      body-up rp e         rt s        mb        nothing   rv hs hb tl ut hr ()
      body-up rp e         rt (just c) mb        (just b′) rv hs hb tl ut hr refl = heads-source rp {b′} {c} (hs (rv refl) refl) (hb refl refl)
      body-up rp (just c₀) rt nothing  nothing   (just b′) rv hs hb tl ut hr _    = false≢ (rv refl)
      body-up rp (just c₀) rt nothing  (just b₀) (just b′) rv hs hb tl ut hr refl =
        ended-head rp c₀ (U.shut (here refl) c₀ b′) rt (U.step rt)
          (shut-heads (here refl) c₀ b′ (hb refl refl) (narrow (tl refl refl refl) (ut refl refl refl))) (hr refl refl refl)
      body-up rp nothing   rt nothing  mb        (just b′) rv hs hb tl ut hr ()

      mutual
        shiftE : ∀ {Δ A} {t : Sub h Δ A} (π : Path t u) → AllPairs _≢_ (names t) → Each H P t → Untold H q t → Ended H t → Each H′ P (plant π v)
        shiftE here ps ev ut en = bl₀ ev
        shiftE (in-map {f = f} {t = s} π) ps ev ut en =
          BH.each-map (lift-ᴹ H′ (U.mapᶜ f) (At.part H′ (plant π v)) (λ c → heads-map f {c}) (Each.parts es here refl)) es
          where
            es : Each H′ P (plant π v)
            es = shiftE π ps (each-sub ev (in-map here) refl) (ut-sub H ut (in-map here) refl) (en-sub H en (in-map here) refl)
        shiftE (in-scan {f = f} {r} {t = s} π) ps ev ut en =
          BH.each-scan (lift-ᴹ H′ (U.scanᶜ f (At.val H′ r)) (At.part H′ (plant π v)) (λ c → heads-scan f (At.val H′ r) {c}) (Each.parts es here refl)) es
          where
            es : Each H′ P (plant π v)
            es = shiftE π (pairs-tl ps) (each-sub ev (in-scan here) refl) (ut-sub H ut (in-scan here) refl) (en-sub H en (in-scan here) refl)
        shiftE (in-take {i = ib} {p} {c} {k} {tk} {t = s} π) ps ev ut en =
          BH.each-take root (λ ok → sh (via-≡ (λ z → z ∧ isTaking tk) Tk.live′ ok))
          where
            module Tk = Take c k π ps
            sh : At.val H (Kit.live c) ∧ isTaking tk ≡ true → Each H′ P (plant π v)
            sh ok = shiftE π Tk.fresh (each-sub ev (in-take here) sk) (ut-sub H ut (in-take here) sk) (en-sub H en (in-take here) sk)
              where
                sk : At.val H (Kit.live c) ∧ isTaking tk ∧ true ≡ true
                sk = seen-take (At.val H (Kit.live c)) ok
            root : ∀ {n} → At.part H′ (takeWhileˢ ib p c k tk (plant π v)) ≡ just n → P n
            root = take-up ib p tk (At.part H s) (At.part H′ (plant π v)) Tk.live′ (Each.parts ev here refl) (λ ok → Each.parts (sh ok) here refl)
        shiftE (in-outer {op = op} {f} {fl} {oc} {k} {r} {pl} {t = so} {ls} π) ps ev ut en =
          BH.each-flat root pool eo eL
          where
            module O = Outer fl oc k r ls π ps
            eo : Each H′ P (plant π v)
            eo = shiftE π O.fresh (each-sub ev (in-outer here) refl) (ut-sub H ut (in-outer here) refl) (en-sub H en (in-outer here) refl)
            eL : EachL H′ P ls
            eL = eachL-alike H H′ O.lanesA (eachL-of H ev)
            pool : ∀ {n} → At.part H′ (flatMapˢ op f fl oc k r pl (plant π v) ls) ≡ just n → P pl
            pool x = held (in-outer {op = op} {f = f} {fl = fl} {oc = oc} {k = k} {r = r} {pl = pl} {ls = ls} π) ps x (Each.pools ev here refl)
            root : ∀ {n} → At.part H′ (flatMapˢ op f fl oc k r pl (plant π v) ls) ≡ just n → P n
            root x = root-flat op (λ a q′ → U.subscribe (f a) q′) (At.part H′ (plant π v)) (At.partLanes H′ ls) (At.val H′ (Flat.queue fl)) pl (pool x)
                       (Each.parts eo here refl) (each-lanes {H = H′} {P = P} ls (λ πL sn e → EachL.partsL eL πL sn e)) x
        shiftE (in-lanes {op = op} {f} {fl} {oc} {k} {r} {pl} {t = so} {ls} πL) ps ev ut en =
          BH.each-flat root pool eo eL
          where
            module Ln = Lanes fl oc k r so πL ps
            eo : Each H′ P so
            eo = each-alike H H′ Ln.soA (each-sub ev (in-outer here) refl)
            eL : EachL H′ P (plantᴸ πL v)
            eL = shiftL πL Ln.fresh (eachL-of H ev) (utL-of H ut) (enL-of H en)
            pool : ∀ {n} → At.part H′ (flatMapˢ op f fl oc k r pl so (plantᴸ πL v)) ≡ just n → P pl
            pool x = held (in-lanes {op = op} {f = f} {fl = fl} {oc = oc} {k = k} {r = r} {pl = pl} {t = so} πL) ps x (Each.pools ev here refl)
            root : ∀ {n} → At.part H′ (flatMapˢ op f fl oc k r pl so (plantᴸ πL v)) ≡ just n → P n
            root x = root-flat op (λ a q′ → U.subscribe (f a) q′) (At.part H′ so) (At.partLanes H′ (plantᴸ πL v)) (At.val H′ (Flat.queue fl)) pl (pool x)
                       (Each.parts eo here refl) (each-lanes {H = H′} {P = P} (plantᴸ πL v) (λ πL′ sn e → EachL.partsL eL πL′ sn e)) x
        shiftE (in-source {S = S} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {t = src} {bd} π) ps ev ut en =
          BH.each-connect root rest es eb
          where
            module Sr = Source S c b kb k bd π ps
            es : is-just (At.part H′ bd) ≡ true → Each H′ P (plant π v)
            es jb = shiftE π Sr.fresh (each-sub ev (in-source here) s₁) (ut-sub H ut (in-source here) s₁) (en-sub H en (in-source here) s₁)
              where
                s₁ : is-just (At.part H bd) ∧ true ≡ true
                s₁ = ∧-join (via-≡ is-just Sr.body jb) refl
            eb : (is-just (At.part H′ (plant π v)) ∨ is-just e) ≡ true → Each H′ P bd
            eb js = each-alike H H′ Sr.bdA (each-sub ev (in-body here) (∧-join (∨-mono (is-just e) (revive π Sr.fresh) js) refl))
            rest : ∀ {n} → At.part H′ (connectˢ S c b kb k fd rp e rt (plant π v) bd) ≡ just n → At.part H′ (plant π v) ≡ nothing → ∀ {c₀} → e ≡ just c₀ → P rt
            rest x _ pe = held (in-source {S = S} {c = c} {b = b} {kb = kb} {k = k} {fd = fd} {e = e} {rp = rp} {rt = rt} {bd = bd} π) ps x (λ x₀ → Each.rests ev here refl x₀ (en here refl x₀ pe) pe)
            root : ∀ {n} → At.part H′ (connectˢ S c b kb k fd rp e rt (plant π v) bd) ≡ just n → P n
            root {n} x =
              src-up rp e rt (At.part H src) (At.part H′ (plant π v)) (At.part H bd) (Each.parts ev here refl) (en here refl) (revive π Sr.fresh)
                (λ jb → Each.parts (es (via-≡ is-just (sym Sr.body) jb)) here refl) (λ j → Each.parts ev (in-body here) (∧-join j refl))
                (subst (λ z → At.connected H′ rp e rt (At.part H′ (plant π v)) z ≡ just n) Sr.body x)
        shiftE (in-body {S = S} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {t = src} {bd} π) ps ev ut en =
          BH.each-connect root rest es eb
          where
            module Bd = Body S c b kb k src π ps
            sb : (is-just (At.part H src) ∨ is-just e) ≡ true → (is-just (At.part H src) ∨ is-just e) ∧ true ≡ true
            sb js = ∧-join js refl
            eb : (is-just (At.part H′ src) ∨ is-just e) ≡ true → Each H′ P (plant π v)
            eb js = shiftE π Bd.fresh (each-sub ev (in-body here) (sb js′)) (ut-sub H ut (in-body here) (sb js′)) (en-sub H en (in-body here) (sb js′))
              where
                js′ : (is-just (At.part H src) ∨ is-just e) ≡ true
                js′ = ∨-mono (is-just e) (via-≡ is-just Bd.source) js
            es : is-just (At.part H′ (plant π v)) ≡ true → Each H′ P src
            es jb = each-alike H H′ Bd.srcA (each-sub ev (in-source here) (∧-join (revive π Bd.fresh jb) refl))
            rest : ∀ {n} → At.part H′ (connectˢ S c b kb k fd rp e rt src (plant π v)) ≡ just n → At.part H′ src ≡ nothing → ∀ {c₀} → e ≡ just c₀ → P rt
            rest x pn pe = held (in-body {S = S} {c = c} {b = b} {kb = kb} {k = k} {fd = fd} {e = e} {rp = rp} {rt = rt} {t = src} π) ps x (λ x₀ → Each.rests ev here refl x₀ (trans (sym Bd.source) pn) pe)
            root : ∀ {n} → At.part H′ (connectˢ S c b kb k fd rp e rt src (plant π v)) ≡ just n → P n
            root {n} x =
              body-up rp e rt (At.part H src) (At.part H bd) (At.part H′ (plant π v)) (revive π Bd.fresh)
                (λ jb → Each.parts ev (in-source here) (∧-join jb refl))
                (λ js → Each.parts (eb (∨-mono (is-just e) (via-≡ is-just (sym Bd.source)) js)) here refl)
                (λ js → told π Bd.fresh (en-sub H en (in-body here) (sb js)) (here refl))
                (untold-at ut here refl) (Each.rests ev here refl)
                (subst (λ z → At.connected H′ rp e rt z (At.part H′ (plant π v)) ≡ just n) Bd.source x)
        shiftE (in-defer {k = k} π) ps ev ut en =
          BH.each-defer (Each.parts es here refl) es
          where
            es : Each H′ P (plant π v)
            es = shiftE π (pairs-r (quietName k) ps) (each-sub ev (in-defer here) refl) (ut-sub H ut (in-defer here) refl) (en-sub H en (in-defer here) refl)

        shiftL : ∀ {Δ B} {ls : List (Lane h Δ B)} (πL : PathLanes ls u) → AllPairs _≢_ (laneNames ls) → EachL H P ls → UntoldL H q ls → EndedL H ls
               → EachL H′ P (plantᴸ πL v)
        shiftL (this-lane {c = c} {k} {t = s} {ls} π) ps eL ut en =
          BH.eachL-cons (λ lv → shiftE π Th.fresh (eachL-head H eL (Th.on lv)) (utL-head H ut (Th.on lv)) (enL-head H en (Th.on lv)))
                        (eachL-alike H H′ Th.restA (eachL-tail H eL))
          where module Th = This c k ls π ps
        shiftL (next-lane {l = lane c k s} {ls} πL) ps eL ut en =
          BH.eachL-cons (λ lv → each-alike H H′ Nx.headA (eachL-head H eL (Nx.on lv)))
                        (shiftL πL Nx.fresh (eachL-tail H eL) (utL-tail H ut) (enL-tail H en))
          where module Nx = Next c k s πL ps

    --------------------------------------------------------------------
    -- WHAT LINGERS, TIED: every pool and every ended source's rest above
    -- the write is tied after it as before.

    module Ties (rs₀ : ∀ {C} → Twin (At.leftover H {B = C} u) (At.leftover H′ {B = C} v))
                (lb₀ : Lingers H u → Lingers H′ v) where
      module LG = Linger H′

      -- A connect's leftover over a source running on either side: the
      -- source's own leftover twinned, the body's leftover alike.

      -- SUSPECT: running, `sourced` reads the source's PART, and nothing
      -- `Ties` holds relates the part of `u` to that of `v`: `rs₀` twins
      -- leftovers only.  With `src` at `u`, a part stepping a skip under
      -- `rp` written to one that hushes, both leftovers idle, twins a
      -- skip against a hush.  A route needs the parts' burst rests
      -- twinned through the write, a parameter beside `rs₀`.
      postulate
        rest-sourced : ∀ {Δ A B} {src : Sub h Δ A} (π : Path src u) rp {x x′ : U.Node (A ∷ Δ) ⊤}
                     → (is-just (At.part H src) ∨ is-just (At.part H′ (plant π v))) ≡ true
                     → Twin (At.leftover H {B = A} src) (At.leftover H′ {B = A} (plant π v))
                     → x′ ≡ x
                     → Twin (U.unionᶜ {B = B} (U.burstingᶜ rp (At.sourced H (At.part H src) (At.leftover H src)))
                                             (U.underᶜ (U.live (At.sourced H (At.part H src) (At.leftover H src))) x))
                            (U.unionᶜ {B = B} (U.burstingᶜ rp (At.sourced H′ (At.part H′ (plant π v)) (At.leftover H′ (plant π v))))
                                             (U.underᶜ (U.live (At.sourced H′ (At.part H′ (plant π v)) (At.leftover H′ (plant π v)))) x′))

      src-rested : ∀ {Δ A B} {src : Sub h Δ A} (π : Path src u) rp {x x′ : U.Node (A ∷ Δ) ⊤}
                 → Twin (At.leftover H {B = A} src) (At.leftover H′ {B = A} (plant π v))
                 → x′ ≡ x → (s s′ : Maybe (U.Node Δ A)) → At.part H src ≡ s → At.part H′ (plant π v) ≡ s′
                 → Twin (U.unionᶜ {B = B} (U.burstingᶜ rp (At.sourced H (At.part H src) (At.leftover H src)))
                                         (U.underᶜ (U.live (At.sourced H (At.part H src) (At.leftover H src))) x))
                        (U.unionᶜ {B = B} (U.burstingᶜ rp (At.sourced H′ (At.part H′ (plant π v)) (At.leftover H′ (plant π v))))
                                         (U.underᶜ (U.live (At.sourced H′ (At.part H′ (plant π v)) (At.leftover H′ (plant π v)))) x′))
      src-rested {src = src} π rp {x = x} up lb nothing nothing p p′ rewrite p | p′ =
        tw-union (tw-burst rp (leftover-restful H src) (leftover-restful H′ (plant π v)) up)
                 (subst (λ z → Twin (U.underᶜ (U.live (At.leftover H src)) x) (U.underᶜ (U.live (At.leftover H′ (plant π v))) z)) (sym lb)
                   (tw-shift x (leftover-restful H src) (leftover-restful H′ (plant π v)) up))
      src-rested π rp up lb (just _) s′       p p′ = rest-sourced π rp (∨-l (cong is-just p)) up lb
      src-rested {src = src} π rp up lb nothing (just _) p p′ = rest-sourced π rp (∨-r (is-just (At.part H src)) (cong is-just p′)) up lb

      mutual
        restedUp : ∀ {Δ A} {t : Sub h Δ A} (π : Path t u) → AllPairs _≢_ (names t)
                 → ∀ {C} → Twin (At.leftover H {B = C} t) (At.leftover H′ {B = C} (plant π v))
        restedUp here ps = rs₀
        restedUp (in-map π) ps = restedUp π ps
        restedUp (in-scan π) ps = restedUp π (pairs-tl ps)
        restedUp (in-take {c = c} {k} π) ps = restedUp π (Take.fresh c k π ps)
        restedUp (in-outer {fl = fl} {oc} {k} {r} {ls = ls} π) ps =
          tw-union (restedUp π O.fresh) (tw-alike (leftoverL-alike H H′ ls O.lanesA))
          where module O = Outer fl oc k r ls π ps
        restedUp (in-lanes {fl = fl} {oc} {k} {r} {t = so} πL) ps =
          tw-union (tw-alike (leftover-alike H H′ so Ln.soA)) (restedUpL πL Ln.fresh)
          where module Ln = Lanes fl oc k r so πL ps
        restedUp (in-source {S = S} {c} {b} {kb} {k} {rp = rp} {t = src} {bd} π) ps =
          src-rested π rp (restedUp π Sr.fresh) (leftover-alike H H′ bd Sr.bdA) (At.part H src) (At.part H′ (plant π v)) refl refl
          where module Sr = Source S c b kb k bd π ps
        restedUp (in-body {S = S} {c} {b} {kb} {k} {rp = rp} {t = src} {bd} π) ps =
          conn-tw rp (At.sourced H (At.part H src) (At.leftover H src)) (At.sourced H′ (At.part H′ src) (At.leftover H′ src))
            (trans (sourced-heap H H′ (At.part H′ src) (At.leftover H′ src)) (cong₂ (At.sourced H) Bd.source (leftover-alike H H′ src Bd.srcA)))
            (restedUp π Bd.fresh)
          where module Bd = Body S c b kb k src π ps
        restedUp (in-defer {k = k} π) ps = restedUp π (pairs-r (quietName k) ps)

        restedUpL : ∀ {Δ B} {ls : List (Lane h Δ B)} (πL : PathLanes ls u) → AllPairs _≢_ (laneNames ls)
                  → ∀ {C} → Twin (At.leftoverL H {B = C} ls) (At.leftoverL H′ {B = C} (plantᴸ πL v))
        restedUpL (this-lane {c = c} {k} {t = s} {ls} π) ps =
          tw-union (restedUp π Th.fresh) (tw-alike (leftoverL-alike H H′ ls Th.restA))
          where module Th = This c k ls π ps
        restedUpL (next-lane {l = lane c k s} {ls} πL) ps =
          tw-union (tw-alike (leftover-alike H H′ s Nx.headA)) (restedUpL πL Nx.fresh)
          where module Nx = Next c k s πL ps

      pooledUpL : ∀ {Δ B} {ls : List (Lane h Δ B)} (πL : PathLanes ls u) → AllPairs _≢_ (laneNames ls)
                → ∀ {C} → Twin (At.pooledL H {B = C} ls) (At.pooledL H′ {B = C} (plantᴸ πL v))
      pooledUpL (this-lane {c = c} {k} {t = s} {ls} π) ps =
        tw-if-moved Th.live′ (tw-alike (pooledL-alike H H′ ls Th.restA)) (tw-union (restedUp π Th.fresh) (tw-alike (pooledL-alike H H′ ls Th.restA)))
        where module Th = This c k ls π ps
      pooledUpL (next-lane {l = lane c k s} {ls} πL) ps =
        tw-if-moved Nx.live′ (pooledUpL πL Nx.fresh) (tw-union (tw-alike (leftover-alike H H′ s Nx.headA)) (pooledUpL πL Nx.fresh))
        where module Nx = Next c k s πL ps

      mutual
        shiftLg : ∀ {Δ A} {t : Sub h Δ A} (π : Path t u) → AllPairs _≢_ (names t) → Lingers H t → Ended H t → Lingers H′ (plant π v)
        shiftLg here ps lg en = lb₀ lg
        shiftLg (in-map π) ps lg en = LG.lg-map (shiftLg π ps (lingers-sub H lg (in-map here) refl) (en-sub H en (in-map here) refl))
        shiftLg (in-scan π) ps lg en = LG.lg-scan (shiftLg π (pairs-tl ps) (lingers-sub H lg (in-scan here) refl) (en-sub H en (in-scan here) refl))
        shiftLg (in-take {c = c} {k} {tk} π) ps lg en =
          LG.lg-take (λ ok → sh (via-≡ (λ z → z ∧ isTaking tk) Tk.live′ ok))
          where
            module Tk = Take c k π ps
            sh : At.val H (Kit.live c) ∧ isTaking tk ≡ true → Lingers H′ (plant π v)
            sh ok = shiftLg π Tk.fresh (lingers-sub H lg (in-take here) sk) (en-sub H en (in-take here) sk)
              where
                sk : At.val H (Kit.live c) ∧ isTaking tk ∧ true ≡ true
                sk = seen-take (At.val H (Kit.live c)) ok
        shiftLg (in-outer {op = op} {f} {fl} {oc} {k} {r} {pl} {t = so} {ls} π) ps lg en =
          LG.lg-flat pool (shiftLg π O.fresh (lingers-sub H lg (in-outer here) refl) (en-sub H en (in-outer here) refl))
            (lingersL-alike H H′ O.lanesA (lingersL-of H lg))
          where
            module O = Outer fl oc k r ls π ps
            pool : ∀ {n} → At.part H′ (flatMapˢ op f fl oc k r pl (plant π v) ls) ≡ just n → Leaves pl (At.pooled H′ fl (plant π v) ls) × Restful pl
            pool x = held (in-outer {op = op} {f = f} {fl = fl} {oc = oc} {k = k} {r = r} {pl = pl} {ls = ls} π) ps x (λ x₀ → lv-tie (Lingers.pools lg here refl x₀)
                       (proj₁ (tw-union (tw-if-moved {y = U.idleᶜ} {y′ = U.idleᶜ} (cong lower O.done) (restedUp π O.fresh) (tw-refl U.idleᶜ)) (tw-alike (pooledL-alike H H′ ls O.lanesA)))))
        shiftLg (in-lanes {op = op} {f} {fl} {oc} {k} {r} {pl} {t = so} {ls} πL) ps lg en =
          LG.lg-flat pool (lingers-alike H H′ Ln.soA (lingers-sub H lg (in-outer here) refl)) (shiftLgL πL Ln.fresh (lingersL-of H lg) (enL-of H en))
          where
            module Ln = Lanes fl oc k r so πL ps
            pool : ∀ {n} → At.part H′ (flatMapˢ op f fl oc k r pl so (plantᴸ πL v)) ≡ just n → Leaves pl (At.pooled H′ fl so (plantᴸ πL v)) × Restful pl
            pool x = held (in-lanes {op = op} {f = f} {fl = fl} {oc = oc} {k = k} {r = r} {pl = pl} {t = so} πL) ps x (λ x₀ → lv-tie (Lingers.pools lg here refl x₀)
                       (proj₁ (tw-union (tw-if-moved {y = U.idleᶜ} {y′ = U.idleᶜ} (cong lower Ln.done) (tw-alike (leftover-alike H H′ so Ln.soA)) (tw-refl U.idleᶜ)) (pooledUpL πL Ln.fresh))))
        shiftLg (in-source {S = S} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {t = src} {bd} π) ps lg en =
          LG.lg-connect rest ls lb
          where
            module Sr = Source S c b kb k bd π ps
            ls : is-just (At.part H′ bd) ≡ true → Lingers H′ (plant π v)
            ls jb = shiftLg π Sr.fresh (lingers-sub H lg (in-source here) s₁) (en-sub H en (in-source here) s₁)
              where
                s₁ : is-just (At.part H bd) ∧ true ≡ true
                s₁ = ∧-join (via-≡ is-just Sr.body jb) refl
            lb : (is-just (At.part H′ (plant π v)) ∨ is-just e) ≡ true → Lingers H′ bd
            lb js = lingers-alike H H′ Sr.bdA (lingers-sub H lg (in-body here) (∧-join (∨-mono (is-just e) (revive π Sr.fresh) js) refl))
            rest : ∀ {n} → At.part H′ (connectˢ S c b kb k fd rp e rt (plant π v) bd) ≡ just n → At.part H′ (plant π v) ≡ nothing
                 → ∀ {c₀} → e ≡ just c₀ → Twin rt (At.leftover H′ {B = ⊤} (plant π v)) × Restful rt
            rest x _ pe = held (in-source {S = S} {c = c} {b = b} {kb = kb} {k = k} {fd = fd} {e = e} {rp = rp} {rt = rt} {bd = bd} π) ps x (λ x₀ → tw-tie (Lingers.rests lg here refl x₀ (en here refl x₀ pe) pe) (restedUp π Sr.fresh))
        shiftLg (in-body {S = S} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {t = src} {bd} π) ps lg en =
          LG.lg-connect rest ls lb
          where
            module Bd = Body S c b kb k src π ps
            ls : is-just (At.part H′ (plant π v)) ≡ true → Lingers H′ src
            ls jb = lingers-alike H H′ Bd.srcA (lingers-sub H lg (in-source here) (∧-join (revive π Bd.fresh jb) refl))
            lb : (is-just (At.part H′ src) ∨ is-just e) ≡ true → Lingers H′ (plant π v)
            lb js = shiftLg π Bd.fresh (lingers-sub H lg (in-body here) sb) (en-sub H en (in-body here) sb)
              where
                sb : (is-just (At.part H src) ∨ is-just e) ∧ true ≡ true
                sb = ∧-join (∨-mono (is-just e) (via-≡ is-just Bd.source) js) refl
            rest : ∀ {n} → At.part H′ (connectˢ S c b kb k fd rp e rt src (plant π v)) ≡ just n → At.part H′ src ≡ nothing
                 → ∀ {c₀} → e ≡ just c₀ → Twin rt (At.leftover H′ {B = ⊤} src) × Restful rt
            rest x pn pe = held (in-body {S = S} {c = c} {b = b} {kb = kb} {k = k} {fd = fd} {e = e} {rp = rp} {rt = rt} {t = src} π) ps x (λ x₀ → tw-tie (Lingers.rests lg here refl x₀ (trans (sym Bd.source) pn) pe)
                             (tw-alike (leftover-alike H H′ src Bd.srcA)))
        shiftLg (in-defer {k = k} π) ps lg en =
          LG.lg-defer (shiftLg π (pairs-r (quietName k) ps) (lingers-sub H lg (in-defer here) refl) (en-sub H en (in-defer here) refl))

        shiftLgL : ∀ {Δ B} {ls : List (Lane h Δ B)} (πL : PathLanes ls u) → AllPairs _≢_ (laneNames ls) → LingersL H ls → EndedL H ls
                 → LingersL H′ (plantᴸ πL v)
        shiftLgL (this-lane {c = c} {k} {t = s} {ls} π) ps lL en =
          LG.lgL-cons (λ lv → shiftLg π Th.fresh (lingersL-head H lL (Th.on lv)) (enL-head H en (Th.on lv)))
                      (lingersL-alike H H′ Th.restA (lingersL-tail H lL))
          where module Th = This c k ls π ps
        shiftLgL (next-lane {l = lane c k s} {ls} πL) ps lL en =
          LG.lgL-cons (λ lv → lingers-alike H H′ Nx.headA (lingersL-head H lL (Nx.on lv))) (shiftLgL πL Nx.fresh (lingersL-tail H lL) (enL-tail H en))
          where module Nx = Next c k s πL ps
