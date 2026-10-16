{-# OPTIONS --guardedness #-}

-- LOCAL: every part of the relation reads only the names its subscription
-- holds.  A heap moved only inside one node (`Off` at that node's names)
-- leaves each part reading the same above and beside it, so what a move
-- costs a part is what it does at the node it writes.
--
-- Two lemmas per part: `-alike`, the part read off two heaps alike at its
-- names; `-path`, the part at the root kept given it is kept at the node
-- the heap moved under.
module adequacy.Local where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Bool using (false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; Σ; proj₁)
open import Data.Unit using (tt)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᴬ; tabulate to tabulateᴬ; lookup to lookupᴬ)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; _∷_)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴸ_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Any.Properties using (++⁺ˡ; ++⁺ʳ)

open import denotation.MonotonicList using (Timeline)
open import operation.AbstractObservable using (module Heap; module Run) renaming (module Machine to Shared)
open import operation.PureObservable using (Pureᴾ; Out)
open import adequacy.Strong using (module Strongly)
open import adequacy.Moves using (module Moving)
open import adequacy.Torn using (module Tearing)

module Locality (R : Set) where
  open Heap using (Quiet; Sink; _∋_)
  open Shared Timeline (Out R) using (Heapᴹ; look; store)
  open Strongly R
  open Moving R using (pairs-split; pairs-r)
  open Tearing R using (Off; Alike; names-path; lanes-path; fresh-path; narrow; apart-r; apart-l; ≢-flip; look-store; torn; tornVia; thrown; thrown-off;
    Site; takeSite; bodySite; siteHeap)
  open Run (Pureᴾ R) using (Env; Observer; module Kit; module FlatKit)

  ----------------------------------------------------------------------
  -- A flatMap's lanes: their switches, those gone

  cuts : ∀ {h Δ B} → List (Lane h Δ B) → List (Kit.Cut h)
  cuts []                = []
  cuts (lane c _ _ ∷ ls) = c ∷ cuts ls

  cuts-switches : ∀ {h} (H : Heapᴹ h) {Δ B} (ls : List (Lane h Δ B)) → At.switches H ls ≡ cuts ls
  cuts-switches H []                = refl
  cuts-switches H (lane c _ _ ∷ ls) = cong (c ∷_) (cuts-switches H ls)

  cut-in : ∀ {h Δ B} (ls : List (Lane h Δ B)) {c} → c ∈ᴸ cuts ls → _∈ᴸ_ {A = Name h} (_ , Kit.live c) (laneNames ls)
  cut-in (lane c k s ∷ ls) (here refl) = here refl
  cut-in (lane c k s ∷ ls) (there m)   = ++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) (++⁺ʳ (names s) (cut-in ls m)))

  Gone : ∀ {h} → Heapᴹ h → ∀ {A Δ B} → FlatKit.Flat A h → List (Lane h Δ B) → Set
  Gone {h} H fl ls = Σ (List (Kit.Cut h)) λ gone → At.val H (FlatKit.Flat.lanes fl) ++ gone ≡ At.switches H ls
                   × All (λ c → At.val H (Kit.live c) ≡ false) gone

  -- A lane's switch apart from every name below a path into the lanes.
  live-apart : ∀ {h Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} → PathLanes ls u → AllPairs _≢_ (laneNames ls)
             → ∀ {c} → c ∈ᴸ cuts ls → All (_≢_ {A = Name h} (_ , Kit.live c)) (names u)
  live-apart (this-lane {c = c} {k} π) ps (here refl) =
    narrow (λ m → ++⁺ʳ (quietName k) (++⁺ˡ (names-path π m))) (apart-r (cutNames c) ps (here refl))
  live-apart (this-lane {c = c} {k} {t = s} {ls} π) ps (there m) =
    narrow (names-path π) (apart-l (names s) (pairs-r (quietName k) (pairs-r (cutNames c) ps)) (cut-in ls m))
  live-apart (next-lane {l = lane c k s} π) ps (here refl) =
    narrow (λ m → ++⁺ʳ (quietName k) (++⁺ʳ (names s) (lanes-path π m))) (apart-r (cutNames c) ps (here refl))
  live-apart (next-lane {l = lane c k s} π) ps (there m) = live-apart π (pairs-r (names s) (pairs-r (quietName k) (pairs-r (cutNames c) ps))) m

  ----------------------------------------------------------------------
  -- A kernel's own reads

  attached-alike : ∀ {h} {H H′ : Heapᴹ h} (c : Kit.Cut h) (k : Maybe (Quiet h)) {u}
                 → look H′ (Kit.held c) ≡ look H (Kit.held c) → Alike H H′ (quietName k) → At.Attached H c k u → At.Attached H′ c k u
  attached-alike c nothing  eh agk (lift e) = lift (trans (cong lower eh) e)
  attached-alike c (just q) eh agk (e , st) = trans (cong lower eh) e , subst (_≗ _) (sym (agk q (here refl))) st

  stashed-alike : ∀ {h} {H H′ : Heapᴹ h} (k : Maybe (Quiet h)) {u} → Alike H H′ (quietName k) → At.Stashed H k u → At.Stashed H′ k u
  stashed-alike nothing  ag st = st
  stashed-alike (just q) ag st = subst (_≗ _) (sym (ag q (here refl))) st

  -- Every subscription below a path against its kernel.
  mutual
    holds-at : ∀ {h} {H : Heapᴹ h} {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} {E o} → Path t u → At.Holds H t E o
             → Σ (Env Δ′ h) λ E′ → Σ (Observer A′ h) λ o′ → At.Holds H u E′ o′
    holds-at here          hs                          = _ , _ , hs
    holds-at (in-map π)    hs                          = holds-at π hs
    holds-at (in-scan π)   hs                          = holds-at π hs
    holds-at (in-take π)   (_ , hs)                    = holds-at π hs
    holds-at (in-outer π)  (_ , _ , _ , hso , _)       = holds-at π hso
    holds-at {t = flatMapˢ op f fl _ _ _ _ _ _} {E = E} {o = o} (in-lanes π) (_ , _ , _ , _ , _ , _ , hl) =
      holdsL-at {op = op} {f = f} {E = E} {o = o} {fl = fl} π hl
    holds-at (in-source π) (_ , _ , _ , hsrc , _)      = holds-at π hsrc
    holds-at (in-body π)   (_ , _ , _ , _ , hbd)       = holds-at π hbd
    holds-at (in-defer π)  (_ , hs)                    = holds-at π hs

    holdsL-at : ∀ {h} {H : Heapᴹ h} {Δ A B Δ′ A′ op f E o fl} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} → PathLanes ls u
              → At.HoldsLanes H {A = A} op f E o fl ls → Σ (Env Δ′ h) λ E′ → Σ (Observer A′ h) λ o′ → At.Holds H u E′ o′
    holdsL-at (this-lane π) (_ , hs , _) = holds-at π hs
    holdsL-at {op = op} {f = f} {E = E} {o = o} {fl = fl} (next-lane π) (_ , _ , hl) = holdsL-at {op = op} {f = f} {E = E} {o = o} {fl = fl} π hl

  mutual
    gated-at : ∀ {h} {H : Heapᴹ h} {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} → Path t u → At.Gated H t → At.Gated H u
    gated-at here          g             = g
    gated-at (in-map π)    g             = gated-at π g
    gated-at (in-scan π)   g             = gated-at π g
    gated-at (in-take π)   (_ , g)       = gated-at π g
    gated-at (in-outer π)  (g , _)       = gated-at π g
    gated-at (in-lanes π)  (_ , gl)      = gatedL-at π gl
    gated-at (in-source π) (_ , g , _)   = gated-at π g
    gated-at (in-body π)   (_ , _ , g)   = gated-at π g
    gated-at (in-defer π)  g             = gated-at π g

    gatedL-at : ∀ {h} {H : Heapᴹ h} {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} → PathLanes ls u → At.GatedLanes H ls → At.Gated H u
    gatedL-at (this-lane π) (_ , g , _) = gated-at π g
    gatedL-at (next-lane π) (_ , _ , gl) = gatedL-at π gl

  module Heaps {h} (H H′ : Heapᴹ h) where
    ----------------------------------------------------------------------
    -- A name apart from the moved ones reads alike

    keep : ∀ {ns ys} → Off H H′ ns → (∀ {y} → y ∈ᴸ ns → y ∈ᴸ ys)
         → ∀ {k} (j : h ∋ k) → All (_≢_ {A = Name h} (k , j)) ys → look H′ j ≡ look H j
    keep off sub j a = off j (narrow sub a)

    keeps : ∀ {ns ys ms} → Off H H′ ns → (∀ {y} → y ∈ᴸ ns → y ∈ᴸ ys)
          → (∀ {x} → x ∈ᴸ ms → All (x ≢_) ys) → Alike H H′ ms
    keeps off sub ap j m = off j (narrow sub (ap m))

    slot-alike : ∀ {A} (s : Sink h A) {cb} → look H′ s ≡ look H s → At.slotIs H s cb → At.slotIs H′ s cb
    slot-alike s {cb} e sl = subst (λ z → CbRel z cb) (sym e) sl

    ----------------------------------------------------------------------
    -- A flatMap's lanes: their live count, those gone

    Lives : ∀ {Δ B} → List (Lane h Δ B) → Set₁
    Lives ls = ∀ {c} → c ∈ᴸ cuts ls → look H′ (Kit.live c) ≡ look H (Kit.live c)

    count-lives : ∀ {Δ B} (ls : List (Lane h Δ B)) → Lives ls → At.count H′ ls ≡ At.count H ls
    count-lives [] lv = refl
    count-lives (lane c k s ∷ ls) lv rewrite lv (here refl) | count-lives ls (λ m → lv (there m)) = refl

    gone-alike : ∀ {A Δ B} (fl : FlatKit.Flat A h) (ls : List (Lane h Δ B))
               → look H′ (FlatKit.Flat.lanes fl) ≡ look H (FlatKit.Flat.lanes fl) → Lives ls → Gone H fl ls → Gone H′ fl ls
    gone-alike fl ls el lv (gone , eq , ga) =
      gone , trans (cong (λ z → lower z ++ gone) el) (trans eq (trans (cuts-switches H ls) (sym (cuts-switches H′ ls))))
      , tabulateᴬ λ {c} m → trans (cong lower (lv (subst (c ∈ᴸ_) (trans eq (cuts-switches H ls)) (++⁺ʳ (At.val H (FlatKit.Flat.lanes fl)) m))))
                                  (lookupᴬ ga m)

    ----------------------------------------------------------------------
    -- HOLDS

    mutual
      holds-alike : ∀ {Δ A} (u : Sub h Δ A) → Alike H H′ (names u) → ∀ {E o} → At.Holds H u E o → At.Holds H′ u E o
      holds-alike (pendingˢ s q)  ag hs = hs
      holds-alike (coldˢ s hd ph) ag hs = slot-alike s (ag s (here refl)) hs
      holds-alike (ofˢ p i xs)    ag hs = hs
      holds-alike doneˢ           ag hs = hs
      holds-alike (mapˢ f s)      ag hs = holds-alike s ag hs
      holds-alike (scanˢ f r s)   ag hs = holds-alike s (λ j m → ag j (there m)) hs
      holds-alike (takeWhileˢ i p c k tk s) ag (a , hs) =
        attached-alike c k (ag (Kit.held c) (there (here refl))) (λ j m → ag j (++⁺ʳ (cutNames c) (++⁺ˡ m))) a
        , holds-alike s (λ j m → ag j (++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) m))) hs
      holds-alike (flatMapˢ op f fl oc k r pl so ls) ag {E} {o} (rf , sl , a , hs , ac , gn , hl) =
        trans (cong lower (ag (FlatKit.Flat.refill fl) (there (there (there (there (here refl))))))) rf
        , slot-alike r (ag r (++⁺ʳ (flatNames fl) (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (here refl))))) sl
        , attached-alike oc k (ag (Kit.held oc) (++⁺ʳ (flatNames fl) (there (here refl))))
                              (λ j m → ag j (++⁺ʳ (flatNames fl) (++⁺ʳ (cutNames oc) (++⁺ˡ m)))) a
        , holds-alike so (λ j m → ag j (++⁺ʳ (flatNames fl) (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ˡ m)))))) hs
        , trans (cong lower (ag (FlatKit.Flat.active fl) (here refl))) (trans ac (sym (count-lives ls lv)))
        , gone-alike fl ls (ag (FlatKit.Flat.lanes fl) (there (there (there (here refl))))) lv gn
        , holdsL-alike ls (λ j m → ag j (inL m)) {op = op} {f = f} {E = E} {o = o} {fl = fl} hl
        where
          inL : ∀ {x} → x ∈ᴸ laneNames ls → x ∈ᴸ names (flatMapˢ op f fl oc k r pl so ls)
          inL m = ++⁺ʳ (flatNames fl) (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ʳ (names so) m))))
          lv : Lives ls
          lv {c} m = ag (Kit.live c) (inL (cut-in ls m))
      holds-alike (connectˢ S c b kb k fd rp e rt src bd) ag (a , be , st , hs , hb) =
        attached-alike c k (ag (Kit.held c) (++⁺ʳ (subjectNames S) (there (here refl))))
                           (λ j m → ag j (++⁺ʳ (subjectNames S) (++⁺ʳ (cutNames c) (there (++⁺ʳ (quietName kb) (++⁺ˡ m)))))) a
        , trans (cong lower (ag b (++⁺ʳ (subjectNames S) (++⁺ʳ (cutNames c) (here refl))))) be
        , stashed-alike kb (λ j m → ag j (++⁺ʳ (subjectNames S) (++⁺ʳ (cutNames c) (there (++⁺ˡ m))))) st
        , holds-alike src (λ j m → ag j (++⁺ʳ (subjectNames S) (++⁺ʳ (cutNames c) (there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ˡ m))))))) hs
        , holds-alike bd (λ j m → ag j (++⁺ʳ (subjectNames S) (++⁺ʳ (cutNames c) (there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ʳ (names src) m))))))) hb
      holds-alike (joinˢ j sk l x st) ag hs = slot-alike sk (ag sk (here refl)) hs
      holds-alike (deferˢ k s) ag (st , hs) =
        stashed-alike k (λ j m → ag j (++⁺ˡ m)) st , holds-alike s (λ j m → ag j (++⁺ʳ (quietName k) m)) hs

      holdsL-alike : ∀ {Δ B} (ls : List (Lane h Δ B)) → Alike H H′ (laneNames ls)
                   → ∀ {A : Set} {op f E o fl} → At.HoldsLanes H {A = A} op f E o fl ls → At.HoldsLanes H′ {A = A} op f E o fl ls
      holdsL-alike []                ag hl = hl
      holdsL-alike (lane c k s ∷ ls) ag {op = op} {f = f} {E = E} {o = o} {fl = fl} (a , hs , hl) =
        attached-alike c k (ag (Kit.held c) (there (here refl))) (λ j m → ag j (++⁺ʳ (cutNames c) (++⁺ˡ m))) a
        , holds-alike s (λ j m → ag j (++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) (++⁺ˡ m)))) hs
        , holdsL-alike ls (λ j m → ag j (++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) (++⁺ʳ (names s) m)))) {op = op} {f = f} {E = E} {o = o} {fl = fl} hl

    mutual
      holds-path : ∀ {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) → AllPairs _≢_ (names t)
                 → Off H H′ (names u) → (∀ {E o} → At.Holds H u E o → At.Holds H′ u E o)
                 → ∀ {E o} → At.Holds H t E o → At.Holds H′ t E o
      holds-path here         ps       off hv hs = hv hs
      holds-path (in-map π)   ps       off hv hs = holds-path π ps off hv hs
      holds-path (in-scan π)  (_ ∷ ps) off hv hs = holds-path π ps off hv hs
      holds-path (in-take {c = c} {k} π) ps off hv (a , hs) =
        attached-alike c k (keep off (λ m → ++⁺ʳ (quietName k) (names-path π m)) (Kit.held c) (apart-r (cutNames c) ps (there (here refl))))
                           (keeps off (names-path π) (apart-r (quietName k) (pairs-r (cutNames c) ps))) a
        , holds-path π (pairs-r (quietName k) (pairs-r (cutNames c) ps)) off hv hs
      holds-path {u = u} (in-outer {op = op} {f} {fl} {oc} {k} {r} {t = so} {ls} π) ps off hv {E} {o} (rf , sl , a , hs , ac , gn , hl) =
        trans (cong lower (keep off subF (FlatKit.Flat.refill fl) (apart-r (flatNames fl) ps (there (there (there (there (here refl)))))))) rf
        , slot-alike r (keep off (λ m → ++⁺ˡ (names-path π m)) r (apart-r ((_ , r) ∷ []) P₃ (here refl))) sl
        , attached-alike oc k (keep off (λ m → ++⁺ʳ (quietName k) (there (++⁺ˡ (names-path π m)))) (Kit.held oc) (apart-r (cutNames oc) P₁ (there (here refl))))
                              (keeps off (λ m → there (++⁺ˡ (names-path π m))) (apart-r (quietName k) P₂)) a
        , holds-path π (proj₁ (pairs-split (names so) P₄)) off hv hs
        , trans (cong lower (keep off subF (FlatKit.Flat.active fl) (apart-r (flatNames fl) ps (here refl)))) (trans ac (sym (count-lives ls lv)))
        , gone-alike fl ls (keep off subF (FlatKit.Flat.lanes fl) (apart-r (flatNames fl) ps (there (there (there (here refl)))))) lv gn
        , holdsL-alike ls (keeps off (names-path π) (apart-l (names so) P₄)) {op = op} {f = f} {E = E} {o = o} {fl = fl} hl
        where
          P₁ = pairs-r (flatNames fl) ps
          P₂ = pairs-r (cutNames oc) P₁
          P₃ = pairs-r (quietName k) P₂
          P₄ = pairs-r ((_ , r) ∷ []) P₃
          subF : ∀ {y} → y ∈ᴸ names u → y ∈ᴸ cutNames oc ++ quietName k ++ (_ , r) ∷ names so ++ laneNames ls
          subF m = ++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ˡ (names-path π m))))
          lv : Lives ls
          lv {c} m = keep off (names-path π) (Kit.live c) (apart-l (names so) P₄ (cut-in ls m))
      holds-path {u = u} (in-lanes {op = op} {f} {fl} {oc} {k} {r} {t = so} {ls} π) ps off hv {E} {o} (rf , sl , a , hs , ac , gn , hl) =
        trans (cong lower (keep off subF (FlatKit.Flat.refill fl) (apart-r (flatNames fl) ps (there (there (there (there (here refl)))))))) rf
        , slot-alike r (keep off (λ m → ++⁺ʳ (names so) (lanes-path π m)) r (apart-r ((_ , r) ∷ []) P₃ (here refl))) sl
        , attached-alike oc k (keep off (λ m → ++⁺ʳ (quietName k) (there (++⁺ʳ (names so) (lanes-path π m)))) (Kit.held oc) (apart-r (cutNames oc) P₁ (there (here refl))))
                              (keeps off (λ m → there (++⁺ʳ (names so) (lanes-path π m))) (apart-r (quietName k) P₂)) a
        , holds-alike so (keeps off (lanes-path π) (apart-r (names so) P₄)) hs
        , trans (cong lower (keep off subF (FlatKit.Flat.active fl) (apart-r (flatNames fl) ps (here refl)))) (trans ac (sym (count-lives ls lv)))
        , gone-alike fl ls (keep off subF (FlatKit.Flat.lanes fl) (apart-r (flatNames fl) ps (there (there (there (here refl)))))) lv gn
        , holdsL-path π (pairs-r (names so) P₄) off hv {op = op} {f = f} {E = E} {o = o} {fl = fl} hl
        where
          P₁ = pairs-r (flatNames fl) ps
          P₂ = pairs-r (cutNames oc) P₁
          P₃ = pairs-r (quietName k) P₂
          P₄ = pairs-r ((_ , r) ∷ []) P₃
          subF : ∀ {y} → y ∈ᴸ names u → y ∈ᴸ cutNames oc ++ quietName k ++ (_ , r) ∷ names so ++ laneNames ls
          subF m = ++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ʳ (names so) (lanes-path π m))))
          lv : Lives ls
          lv {c} m = off (Kit.live c) (live-apart π (pairs-r (names so) P₄) m)
      holds-path (in-source {S = S} {c} {b} {kb} {k} {t = src} {bd} π) ps off hv (a , be , st , hs , hb) =
        attached-alike c k (keep off (λ m → there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ˡ (names-path π m))))) (Kit.held c)
                                     (apart-r (cutNames c) Q₀ (there (here refl))))
                           (keeps off (λ m → ++⁺ˡ (names-path π m)) (apart-r (quietName k) Q₃)) a
        , trans (cong lower (keep off (λ m → ++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ˡ (names-path π m)))) b (apart-r ((_ , b) ∷ []) Q₁ (here refl)))) be
        , stashed-alike kb (keeps off (λ m → ++⁺ʳ (quietName k) (++⁺ˡ (names-path π m))) (apart-r (quietName kb) Q₂)) st
        , holds-path π (proj₁ (pairs-split (names src) Q₄)) off hv hs
        , holds-alike bd (keeps off (names-path π) (apart-l (names src) Q₄)) hb
        where
          Q₀ = pairs-r (subjectNames S) ps
          Q₁ = pairs-r (cutNames c) Q₀
          Q₂ = pairs-r ((_ , b) ∷ []) Q₁
          Q₃ = pairs-r (quietName kb) Q₂
          Q₄ = pairs-r (quietName k) Q₃
      holds-path (in-body {S = S} {c} {b} {kb} {k} {t = src} {bd} π) ps off hv (a , be , st , hs , hb) =
        attached-alike c k (keep off (λ m → there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ʳ (names src) (names-path π m))))) (Kit.held c)
                                     (apart-r (cutNames c) Q₀ (there (here refl))))
                           (keeps off (λ m → ++⁺ʳ (names src) (names-path π m)) (apart-r (quietName k) Q₃)) a
        , trans (cong lower (keep off (λ m → ++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ʳ (names src) (names-path π m)))) b (apart-r ((_ , b) ∷ []) Q₁ (here refl)))) be
        , stashed-alike kb (keeps off (λ m → ++⁺ʳ (quietName k) (++⁺ʳ (names src) (names-path π m))) (apart-r (quietName kb) Q₂)) st
        , holds-alike src (keeps off (names-path π) (apart-r (names src) Q₄)) hs
        , holds-path π (pairs-r (names src) Q₄) off hv hb
        where
          Q₀ = pairs-r (subjectNames S) ps
          Q₁ = pairs-r (cutNames c) Q₀
          Q₂ = pairs-r ((_ , b) ∷ []) Q₁
          Q₃ = pairs-r (quietName kb) Q₂
          Q₄ = pairs-r (quietName k) Q₃
      holds-path (in-defer {k = k} π) ps off hv (st , hs) =
        stashed-alike k (keeps off (names-path π) (apart-r (quietName k) ps)) st , holds-path π (pairs-r (quietName k) ps) off hv hs

      holdsL-path : ∀ {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (π : PathLanes ls u) → AllPairs _≢_ (laneNames ls)
                  → Off H H′ (names u) → (∀ {E o} → At.Holds H u E o → At.Holds H′ u E o)
                  → ∀ {A : Set} {op f E o fl} → At.HoldsLanes H {A = A} op f E o fl ls → At.HoldsLanes H′ {A = A} op f E o fl ls
      holdsL-path (this-lane {c = c} {k} {t = s} {ls} π) ps off hv {op = op} {f = f} {E = E} {o = o} {fl = fl} (a , hs , hl) =
        attached-alike c k (keep off (λ m → ++⁺ʳ (quietName k) (++⁺ˡ (names-path π m))) (Kit.held c) (apart-r (cutNames c) ps (there (here refl))))
                           (keeps off (λ m → ++⁺ˡ (names-path π m)) (apart-r (quietName k) (pairs-r (cutNames c) ps))) a
        , holds-path π (proj₁ (pairs-split (names s) P)) off hv hs
        , holdsL-alike ls (keeps off (names-path π) (apart-l (names s) P)) {op = op} {f = f} {E = E} {o = o} {fl = fl} hl
        where P = pairs-r (quietName k) (pairs-r (cutNames c) ps)
      holdsL-path (next-lane {l = lane c k s} π) ps off hv {op = op} {f = f} {E = E} {o = o} {fl = fl} (a , hs , hl) =
        attached-alike c k (keep off (λ m → ++⁺ʳ (quietName k) (++⁺ʳ (names s) (lanes-path π m))) (Kit.held c) (apart-r (cutNames c) ps (there (here refl))))
                           (keeps off (λ m → ++⁺ʳ (names s) (lanes-path π m)) (apart-r (quietName k) (pairs-r (cutNames c) ps))) a
        , holds-alike s (keeps off (lanes-path π) (apart-r (names s) P)) hs
        , holdsL-path π (pairs-r (names s) P) off hv {op = op} {f = f} {E = E} {o = o} {fl = fl} hl
        where P = pairs-r (quietName k) (pairs-r (cutNames c) ps)

    ----------------------------------------------------------------------
    -- SPENT

    mutual
      spent-alike : ∀ {Δ A} (u : Sub h Δ A) → Alike H H′ (names u) → At.Spent H u → At.Spent H′ u
      spent-alike (pendingˢ s q)  ag sp = sp
      spent-alike (coldˢ s hd ph) ag sp = lift (trans (cong lower (ag hd (there (here refl)))) (lower sp))
      spent-alike (ofˢ p i xs)    ag sp = sp
      spent-alike doneˢ           ag sp = sp
      spent-alike (mapˢ f s)      ag sp = spent-alike s ag sp
      spent-alike (scanˢ f r s)   ag sp = spent-alike s (λ j m → ag j (there m)) sp
      spent-alike (takeWhileˢ i p c k tk s) ag sp = cut-alike k s (λ j m → ag j (++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) m))) sp
      spent-alike (flatMapˢ op f fl oc k r pl so ls) ag (c₁ , c₂) =
        cut-alike k so (λ j m → ag j (++⁺ʳ (flatNames fl) (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ˡ m)))))) c₁
        , spentL-alike ls (λ j m → ag j (++⁺ʳ (flatNames fl) (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ʳ (names so) m)))))) c₂
      spent-alike (connectˢ S c b kb k fd rp e rt src bd) ag (c₁ , c₂) =
        cut-alike k src (λ j m → ag j (++⁺ʳ (subjectNames S) (++⁺ʳ (cutNames c) (there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ˡ m))))))) c₁
        , cut-alike kb bd (λ j m → ag j (++⁺ʳ (subjectNames S) (++⁺ʳ (cutNames c) (there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ʳ (names src) m))))))) c₂
      spent-alike (joinˢ j sk l x st) ag sp = sp
      spent-alike (deferˢ k s) ag sp = cut-alike k s (λ j m → ag j (++⁺ʳ (quietName k) m)) sp

      spentL-alike : ∀ {Δ B} (ls : List (Lane h Δ B)) → Alike H H′ (laneNames ls) → At.SpentLanes H ls → At.SpentLanes H′ ls
      spentL-alike []                ag sp = sp
      spentL-alike (lane c k s ∷ ls) ag (c₁ , c₂) =
        cut-alike k s (λ j m → ag j (++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) (++⁺ˡ m)))) c₁
        , spentL-alike ls (λ j m → ag j (++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) (++⁺ʳ (names s) m)))) c₂

      cut-alike : ∀ {Δ A} (k : Maybe (Quiet h)) (s : Sub h Δ A) → Alike H H′ (names s) → At.Cut↓ H k s → At.Cut↓ H′ k s
      cut-alike nothing  s ag sp = sp
      cut-alike (just _) s ag sp = spent-alike s ag sp

    mutual
      spent-path : ∀ {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) → AllPairs _≢_ (names t)
                 → Off H H′ (names u) → (At.Spent H u → At.Spent H′ u) → At.Spent H t → At.Spent H′ t
      spent-path here        ps       off hv sp = hv sp
      spent-path (in-map π)  ps       off hv sp = spent-path π ps off hv sp
      spent-path (in-scan π) (_ ∷ ps) off hv sp = spent-path π ps off hv sp
      spent-path (in-take {c = c} {k} π) ps off hv sp = cut-path k π (pairs-r (quietName k) (pairs-r (cutNames c) ps)) off hv sp
      spent-path (in-outer {fl = fl} {oc} {k} {r} {t = so} {ls} π) ps off hv (c₁ , c₂) =
        cut-path k π (proj₁ (pairs-split (names so) P)) off hv c₁ , spentL-alike ls (keeps off (names-path π) (apart-l (names so) P)) c₂
        where P = pairs-r ((_ , r) ∷ []) (pairs-r (quietName k) (pairs-r (cutNames oc) (pairs-r (flatNames fl) ps)))
      spent-path (in-lanes {fl = fl} {oc} {k} {r} {t = so} {ls} π) ps off hv (c₁ , c₂) =
        cut-alike k so (keeps off (lanes-path π) (apart-r (names so) P)) c₁ , spentL-path π (pairs-r (names so) P) off hv c₂
        where P = pairs-r ((_ , r) ∷ []) (pairs-r (quietName k) (pairs-r (cutNames oc) (pairs-r (flatNames fl) ps)))
      spent-path (in-source {S = S} {c} {b} {kb} {k} {t = src} {bd} π) ps off hv (c₁ , c₂) =
        cut-path k π (proj₁ (pairs-split (names src) Q)) off hv c₁ , cut-alike kb bd (keeps off (names-path π) (apart-l (names src) Q)) c₂
        where Q = pairs-r (quietName k) (pairs-r (quietName kb) (pairs-r ((_ , b) ∷ []) (pairs-r (cutNames c) (pairs-r (subjectNames S) ps))))
      spent-path (in-body {S = S} {c} {b} {kb} {k} {t = src} {bd} π) ps off hv (c₁ , c₂) =
        cut-alike k src (keeps off (names-path π) (apart-r (names src) Q)) c₁ , cut-path kb π (pairs-r (names src) Q) off hv c₂
        where Q = pairs-r (quietName k) (pairs-r (quietName kb) (pairs-r ((_ , b) ∷ []) (pairs-r (cutNames c) (pairs-r (subjectNames S) ps))))
      spent-path (in-defer {k = k} π) ps off hv sp = cut-path k π (pairs-r (quietName k) ps) off hv sp

      spentL-path : ∀ {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (π : PathLanes ls u) → AllPairs _≢_ (laneNames ls)
                  → Off H H′ (names u) → (At.Spent H u → At.Spent H′ u) → At.SpentLanes H ls → At.SpentLanes H′ ls
      spentL-path (this-lane {c = c} {k} {t = s} {ls} π) ps off hv (c₁ , c₂) =
        cut-path k π (proj₁ (pairs-split (names s) P)) off hv c₁ , spentL-alike ls (keeps off (names-path π) (apart-l (names s) P)) c₂
        where P = pairs-r (quietName k) (pairs-r (cutNames c) ps)
      spentL-path (next-lane {l = lane c k s} π) ps off hv (c₁ , c₂) =
        cut-alike k s (keeps off (lanes-path π) (apart-r (names s) P)) c₁ , spentL-path π (pairs-r (names s) P) off hv c₂
        where P = pairs-r (quietName k) (pairs-r (cutNames c) ps)

      cut-path : ∀ {Δ A Δ′ A′} (k : Maybe (Quiet h)) {s : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path s u) → AllPairs _≢_ (names s)
               → Off H H′ (names u) → (At.Spent H u → At.Spent H′ u) → At.Cut↓ H k s → At.Cut↓ H′ k s
      cut-path nothing  π ps off hv sp = sp
      cut-path (just _) π ps off hv sp = spent-path π ps off hv sp

    ----------------------------------------------------------------------
    -- GATED

    -- A switch's thrown reading, carried across a heap alike at it.
    thrown-alike : ∀ (c : Kit.Cut h) {X : Set₁} → look H′ (Kit.live c) ≡ look H (Kit.live c)
                 → (At.val H (Kit.live c) ≡ false → X) → At.val H′ (Kit.live c) ≡ false → X
    thrown-alike c e g e′ = g (trans (sym (cong lower e)) e′)

    mutual
      gated-alike : ∀ {Δ A} (u : Sub h Δ A) → Alike H H′ (names u) → At.Gated H u → At.Gated H′ u
      gated-alike (pendingˢ s q)  ag g = g
      gated-alike (coldˢ s hd ph) ag g = lift (λ e → lower g (trans (sym (cong lower (ag hd (there (here refl))))) e))
      gated-alike (ofˢ p i xs)    ag g = g
      gated-alike doneˢ           ag g = g
      gated-alike (mapˢ f s)      ag g = gated-alike s ag g
      gated-alike (scanˢ f r s)   ag g = gated-alike s (λ j m → ag j (there m)) g
      gated-alike (takeWhileˢ i p c k tk s) ag (g₁ , g₂) =
        (λ e → cut-alike k s agS (thrown-alike c (ag (Kit.live c) (here refl)) g₁ e)) , gated-alike s agS g₂
        where
          agS : Alike H H′ (names s)
          agS j m = ag j (++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) m))
      gated-alike (flatMapˢ op f fl oc k r pl so ls) ag (g₁ , g₂) =
        gated-alike so (λ j m → ag j (++⁺ʳ (flatNames fl) (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ˡ m)))))) g₁
        , gatedL-alike ls (λ j m → ag j (++⁺ʳ (flatNames fl) (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ʳ (names so) m)))))) g₂
      gated-alike (connectˢ S c b kb k fd rp e rt src bd) ag (g₁ , g₂ , g₃) =
        (λ e → cut-alike k src agS (thrown-alike c (ag (Kit.live c) (++⁺ʳ (subjectNames S) (here refl))) g₁ e))
        , gated-alike src agS g₂
        , gated-alike bd (λ j m → ag j (++⁺ʳ (subjectNames S) (++⁺ʳ (cutNames c) (there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ʳ (names src) m))))))) g₃
        where
          agS : Alike H H′ (names src)
          agS j m = ag j (++⁺ʳ (subjectNames S) (++⁺ʳ (cutNames c) (there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ˡ m))))))
      gated-alike (joinˢ j sk l x st) ag g = g
      gated-alike (deferˢ k s) ag g = gated-alike s (λ j m → ag j (++⁺ʳ (quietName k) m)) g

      gatedL-alike : ∀ {Δ B} (ls : List (Lane h Δ B)) → Alike H H′ (laneNames ls) → At.GatedLanes H ls → At.GatedLanes H′ ls
      gatedL-alike []                ag g = g
      gatedL-alike (lane c k s ∷ ls) ag (g₁ , g₂ , g₃) =
        (λ e → cut-alike k s agS (thrown-alike c (ag (Kit.live c) (here refl)) g₁ e)) , gated-alike s agS g₂
        , gatedL-alike ls (λ j m → ag j (++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) (++⁺ʳ (names s) m)))) g₃
        where
          agS : Alike H H′ (names s)
          agS j m = ag j (++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) (++⁺ˡ m)))

    mutual
      gated-path : ∀ {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) → AllPairs _≢_ (names t) → Off H H′ (names u)
                 → (At.Gated H u → At.Gated H′ u) → (At.Spent H u → At.Spent H′ u) → At.Gated H t → At.Gated H′ t
      gated-path here        ps       off hg hs g = hg g
      gated-path (in-map π)  ps       off hg hs g = gated-path π ps off hg hs g
      gated-path (in-scan π) (_ ∷ ps) off hg hs g = gated-path π ps off hg hs g
      gated-path (in-take {c = c} {k} π) ps off hg hs (g₁ , g₂) =
        (λ e → cut-path k π P off hs (thrown-alike c lc g₁ e)) , gated-path π P off hg hs g₂
        where
          P = pairs-r (quietName k) (pairs-r (cutNames c) ps)
          lc = keep off (λ m → ++⁺ʳ (quietName k) (names-path π m)) (Kit.live c) (apart-r (cutNames c) ps (here refl))
      gated-path (in-outer {fl = fl} {oc} {k} {r} {t = so} {ls} π) ps off hg hs (g₁ , g₂) =
        gated-path π (proj₁ (pairs-split (names so) P)) off hg hs g₁ , gatedL-alike ls (keeps off (names-path π) (apart-l (names so) P)) g₂
        where P = pairs-r ((_ , r) ∷ []) (pairs-r (quietName k) (pairs-r (cutNames oc) (pairs-r (flatNames fl) ps)))
      gated-path (in-lanes {fl = fl} {oc} {k} {r} {t = so} {ls} π) ps off hg hs (g₁ , g₂) =
        gated-alike so (keeps off (lanes-path π) (apart-r (names so) P)) g₁ , gatedL-path π (pairs-r (names so) P) off hg hs g₂
        where P = pairs-r ((_ , r) ∷ []) (pairs-r (quietName k) (pairs-r (cutNames oc) (pairs-r (flatNames fl) ps)))
      gated-path (in-source {S = S} {c} {b} {kb} {k} {t = src} {bd} π) ps off hg hs (g₁ , g₂ , g₃) =
        (λ e → cut-path k π Ps off hs (thrown-alike c lc g₁ e)) , gated-path π Ps off hg hs g₂
        , gated-alike bd (keeps off (names-path π) (apart-l (names src) Q₄)) g₃
        where
          Q₀ = pairs-r (subjectNames S) ps
          Q₄ = pairs-r (quietName k) (pairs-r (quietName kb) (pairs-r ((_ , b) ∷ []) (pairs-r (cutNames c) Q₀)))
          Ps = proj₁ (pairs-split (names src) Q₄)
          lc = keep off (λ m → there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ˡ (names-path π m))))) (Kit.live c) (apart-r (cutNames c) Q₀ (here refl))
      gated-path (in-body {S = S} {c} {b} {kb} {k} {t = src} {bd} π) ps off hg hs (g₁ , g₂ , g₃) =
        (λ e → cut-alike k src agS (thrown-alike c lc g₁ e)) , gated-alike src agS g₂ , gated-path π (pairs-r (names src) Q₄) off hg hs g₃
        where
          Q₀ = pairs-r (subjectNames S) ps
          Q₄ = pairs-r (quietName k) (pairs-r (quietName kb) (pairs-r ((_ , b) ∷ []) (pairs-r (cutNames c) Q₀)))
          agS = keeps off (names-path π) (apart-r (names src) Q₄)
          lc = keep off (λ m → there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ʳ (names src) (names-path π m))))) (Kit.live c) (apart-r (cutNames c) Q₀ (here refl))
      gated-path (in-defer {k = k} π) ps off hg hs g = gated-path π (pairs-r (quietName k) ps) off hg hs g

      gatedL-path : ∀ {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (π : PathLanes ls u) → AllPairs _≢_ (laneNames ls) → Off H H′ (names u)
                  → (At.Gated H u → At.Gated H′ u) → (At.Spent H u → At.Spent H′ u) → At.GatedLanes H ls → At.GatedLanes H′ ls
      gatedL-path (this-lane {c = c} {k} {t = s} {ls} π) ps off hg hs (g₁ , g₂ , g₃) =
        (λ e → cut-path k π Ps off hs (thrown-alike c lc g₁ e)) , gated-path π Ps off hg hs g₂
        , gatedL-alike ls (keeps off (names-path π) (apart-l (names s) P)) g₃
        where
          P = pairs-r (quietName k) (pairs-r (cutNames c) ps)
          Ps = proj₁ (pairs-split (names s) P)
          lc = keep off (λ m → ++⁺ʳ (quietName k) (++⁺ˡ (names-path π m))) (Kit.live c) (apart-r (cutNames c) ps (here refl))
      gatedL-path (next-lane {l = lane c k s} π) ps off hg hs (g₁ , g₂ , g₃) =
        (λ e → cut-alike k s agS (thrown-alike c lc g₁ e)) , gated-alike s agS g₂ , gatedL-path π (pairs-r (names s) P) off hg hs g₃
        where
          P = pairs-r (quietName k) (pairs-r (cutNames c) ps)
          agS = keeps off (lanes-path π) (apart-r (names s) P)
          lc = keep off (λ m → ++⁺ʳ (quietName k) (++⁺ʳ (names s) (lanes-path π m))) (Kit.live c) (apart-r (cutNames c) ps (here refl))

  ----------------------------------------------------------------------
  -- AN UNSUBSCRIBE, AT ITS OWN NODE: what it leaves of the kernel, the
  -- spent and the gates of the subscription it tears.  Elsewhere `Off`
  -- carries each part across, so these are all a cut owes the relation.

  postulate
    -- A flatMap's lanes in flight are the first so many of its lanes and
    -- the rest are cut, so `torn` throwing that many leaves none live.
    holds-torn : ∀ {h} (H : Heapᴹ h) {Δ A} (s : Sub h Δ A) → AllPairs _≢_ (names s)
               → ∀ {E o} → At.Holds H s E o → At.Holds (torn H s) s E o

    -- The lanes `torn` leaves unthrown are cut already, and their gates
    -- give their spent.
    spent-torn : ∀ {h} (H : Heapᴹ h) {Δ A} (s : Sub h Δ A) → AllPairs _≢_ (names s)
               → ∀ {E o} → At.Holds H s E o → At.Gated H s → At.Spent (torn H s) s

    gated-torn : ∀ {h} (H : Heapᴹ h) {Δ A} (s : Sub h Δ A) → AllPairs _≢_ (names s)
               → ∀ {E o} → At.Holds H s E o → At.Gated H s → At.Gated (torn H s) s

  via-holds : ∀ {h} (H : Heapᴹ h) (k : Maybe (Quiet h)) {Δ A} (s : Sub h Δ A) → AllPairs _≢_ (names s)
            → ∀ {E o} → At.Holds H s E o → At.Holds (tornVia H k s) s E o
  via-holds H nothing  s ps hs = hs
  via-holds H (just _) s ps hs = holds-torn H s ps hs

  via-cut : ∀ {h} (H : Heapᴹ h) (k : Maybe (Quiet h)) {Δ A} (s : Sub h Δ A) → AllPairs _≢_ (names s)
          → ∀ {E o} → At.Holds H s E o → At.Gated H s → At.Cut↓ (tornVia H k s) k s
  via-cut H nothing  s ps hs g = lift tt
  via-cut H (just _) s ps hs g = spent-torn H s ps hs g

  via-gated : ∀ {h} (H : Heapᴹ h) (k : Maybe (Quiet h)) {Δ A} (s : Sub h Δ A) → AllPairs _≢_ (names s)
            → ∀ {E o} → At.Holds H s E o → At.Gated H s → At.Gated (tornVia H k s) s
  via-gated H nothing  s ps hs g = g
  via-gated H (just _) s ps hs g = gated-torn H s ps hs g

  -- A thrown switch moves only the switch and what it holds.
  thrown-at : ∀ {h} (H : Heapᴹ h) (c : Kit.Cut h) (k : Maybe (Quiet h)) {Δ A} (s : Sub h Δ A) {ns}
            → (_ , Kit.live c) ∈ᴸ ns → (∀ {y} → y ∈ᴸ names s → y ∈ᴸ ns) → Off H (thrown H c k s) ns
  thrown-at H c k s ml sub j a = thrown-off H c k s j (lookupᴬ a ml) (narrow sub a)

  pair-head : ∀ {a} {X : Set a} {x : X} {xs} → AllPairs _≢_ (x ∷ xs) → All (x ≢_) xs
  pair-head (a ∷ _) = a

  -- The takeWhile a cut runs from, at the heap it leaves.
  module TakeSite {h} (H : Heapᴹ h) {Δ A i q c k} {s : Sub h Δ A} (ps : AllPairs _≢_ (names (takeWhileˢ i q c k taken s))) where
    H₁ = store H (Kit.live c) (lift false)
    H′ = thrown H c k s
    P  = pairs-r (quietName k) (pairs-r (cutNames c) ps)

    off : Off H H′ (names (takeWhileˢ i q c k taken s))
    off = thrown-at H c k s (here refl) (λ m → ++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) m))

    ag₁ : Alike H H₁ (names s)
    ag₁ j m = look-store H (Kit.live c) j (lookupᴬ (apart-r (cutNames c) ps (here refl)) (++⁺ʳ (quietName k) m))

    eh : look H′ (Kit.held c) ≡ look H (Kit.held c)
    eh = thrown-off H c k s (Kit.held c) (≢-flip (lookupᴬ (pair-head ps) (here refl)))
                    (narrow (++⁺ʳ (quietName k)) (apart-r (cutNames c) ps (there (here refl))))

    agk : Alike H H′ (quietName k)
    agk j m = thrown-off H c k s j (lookupᴬ (apart-l (cutNames c) ps (++⁺ˡ m)) (here refl)) (apart-r (quietName k) (pairs-r (cutNames c) ps) m)

    holds : ∀ {E o} → At.Holds H (takeWhileˢ i q c k taken s) E o → At.Holds H′ (takeWhileˢ i q c k taken s) E o
    holds (a , hs) = attached-alike c k eh agk a , via-holds H₁ k s P (Heaps.holds-alike H H₁ s ag₁ hs)

    module _ {E o} (hs : At.Holds H s E o) (g : At.Gated H s) where
      hs₁ = Heaps.holds-alike H H₁ s ag₁ hs
      g₁  = Heaps.gated-alike H H₁ s ag₁ g

      spent : At.Spent H′ (takeWhileˢ i q c k taken s)
      spent = via-cut H₁ k s P hs₁ g₁

      gated : At.Gated H′ (takeWhileˢ i q c k taken s)
      gated = (λ _ → spent) , via-gated H₁ k s P hs₁ g₁

  -- The connect a cut runs from, its body ended, at the heap it leaves.
  module BodySite {h} (H : Heapᴹ h) {Δ A B S c b kb k fd e rp rt} {s : Sub h Δ A} {bd : Sub h (A ∷ Δ) B}
                  (ps : AllPairs _≢_ (names (connectˢ S c b kb k fd rp e rt s bd))) where
    H₁ = store H (Kit.live c) (lift false)
    H′ = thrown H c k s
    Q₀ = pairs-r (subjectNames S) ps
    Q₁ = pairs-r (cutNames c) Q₀
    Q₂ = pairs-r ((_ , b) ∷ []) Q₁
    Q₃ = pairs-r (quietName kb) Q₂
    Q₄ = pairs-r (quietName k) Q₃
    P  = proj₁ (pairs-split (names s) Q₄)

    off : Off H H′ (names (connectˢ S c b kb k fd rp e rt s bd))
    off = thrown-at H c k s (++⁺ʳ (subjectNames S) (here refl))
                    (λ m → ++⁺ʳ (subjectNames S) (++⁺ʳ (cutNames c) (there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ˡ m))))))

    ag₁ : Alike H H₁ (names s)
    ag₁ j m = look-store H (Kit.live c) j (lookupᴬ (apart-r (cutNames c) Q₀ (here refl)) (there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ˡ m)))))

    eh : look H′ (Kit.held c) ≡ look H (Kit.held c)
    eh = thrown-off H c k s (Kit.held c) (≢-flip (lookupᴬ (pair-head Q₀) (here refl)))
                    (narrow (λ m → there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ˡ m)))) (apart-r (cutNames c) Q₀ (there (here refl))))

    agk : Alike H H′ (quietName k)
    agk j m = thrown-off H c k s j (lookupᴬ (apart-l (cutNames c) Q₀ (there (++⁺ʳ (quietName kb) (++⁺ˡ m)))) (here refl))
                         (narrow ++⁺ˡ (apart-r (quietName k) Q₃ m))

    eb : look H′ b ≡ look H b
    eb = thrown-off H c k s b (lookupᴬ (apart-l (cutNames c) Q₀ (here refl)) (here refl))
                    (narrow (λ m → ++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ˡ m))) (apart-r ((_ , b) ∷ []) Q₁ (here refl)))

    agkb : Alike H H′ (quietName kb)
    agkb j m = thrown-off H c k s j (lookupᴬ (apart-l (cutNames c) Q₀ (there (++⁺ˡ m))) (here refl))
                          (narrow (λ m′ → ++⁺ʳ (quietName k) (++⁺ˡ m′)) (apart-r (quietName kb) Q₂ m))

    agbd : Alike H H′ (names bd)
    agbd j m = thrown-off H c k s j (lookupᴬ (apart-l (cutNames c) Q₀ (there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ʳ (names s) m))))) (here refl))
                          (apart-l (names s) Q₄ m)

    holds : ∀ {E o} → At.Holds H (connectˢ S c b kb k fd rp e rt s bd) E o → At.Holds H′ (connectˢ S c b kb k fd rp e rt s bd) E o
    holds (a , be , st , hs , hb) =
      attached-alike c k eh agk a , trans (cong lower eb) be , stashed-alike kb agkb st
      , via-holds H₁ k s P (Heaps.holds-alike H H₁ s ag₁ hs) , Heaps.holds-alike H H′ bd agbd hb

    module _ {E o} (hs : At.Holds H s E o) (g : At.Gated H s) where
      hs₁ = Heaps.holds-alike H H₁ s ag₁ hs
      g₁  = Heaps.gated-alike H H₁ s ag₁ g

      spent : At.Spent H (connectˢ S c b kb k fd rp e rt s bd) → At.Spent H′ (connectˢ S c b kb k fd rp e rt s bd)
      spent (_ , c₂) = via-cut H₁ k s P hs₁ g₁ , Heaps.cut-alike H H′ kb bd agbd c₂

      gated : At.Gated H (connectˢ S c b kb k fd rp e rt s bd) → At.Gated H′ (connectˢ S c b kb k fd rp e rt s bd)
      gated (_ , _ , g₃) = (λ _ → via-cut H₁ k s P hs₁ g₁) , via-gated H₁ k s P hs₁ g₁ , Heaps.gated-alike H H′ bd agbd g₃

  -- The heap a cut leaves, against the root's kernel and gates.
  site-holds : ∀ {h} (H : Heapᴹ h) {t : Sub h [] R} → AllPairs _≢_ (names t) → (z : Site t)
             → At.Holds H t []ᴬ rootObs → At.Holds (siteHeap H z) t []ᴬ rootObs
  site-holds H ps (takeSite {i = i} {q} {c} {k} {s} π) = Heaps.holds-path H (thrown H c k s) π ps T.off (λ {E} {o} → T.holds {E} {o})
    where module T = TakeSite H {i = i} {q = q} {c = c} {k = k} {s = s} (fresh-path π ps)
  site-holds H ps (bodySite {S = S} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {s} {bd} π) = Heaps.holds-path H (thrown H c k s) π ps B.off (λ {E} {o} → B.holds {E} {o})
    where module B = BodySite H {S = S} {c = c} {b = b} {kb = kb} {k = k} {fd = fd} {e = e} {rp = rp} {rt = rt} {s = s} {bd = bd} (fresh-path π ps)

  site-gated : ∀ {h} (H : Heapᴹ h) {t : Sub h [] R} → AllPairs _≢_ (names t) → (z : Site t)
             → At.Holds H t []ᴬ rootObs → At.Gated H t → At.Gated (siteHeap H z) t
  site-gated H ps (takeSite {i = i} {q} {c} {k} {s} π) hs g with holds-at π hs | gated-at π g
  ... | _ , _ , (_ , hu) | (_ , gu) =
    Heaps.gated-path H (thrown H c k s) π ps T.off (λ _ → T.gated hu gu) (λ _ → T.spent hu gu) g
    where module T = TakeSite H {i = i} {q = q} {c = c} {k = k} {s = s} (fresh-path π ps)
  site-gated H ps (bodySite {S = S} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {s} {bd} π) hs g with holds-at π hs | gated-at π g
  ... | _ , _ , (_ , _ , _ , hu , _) | (_ , gu , _) =
    Heaps.gated-path H (thrown H c k s) π ps B.off (B.gated hu gu) (B.spent hu gu) g
    where module B = BodySite H {S = S} {c = c} {b = b} {kb = kb} {k = k} {fd = fd} {e = e} {rp = rp} {rt = rt} {s = s} {bd = bd} (fresh-path π ps)
