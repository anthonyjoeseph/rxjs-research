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

open import Data.List using (List; []; _∷_; _++_; length; drop)
open import Data.List.Properties using (∷-injectiveˡ; ∷-injectiveʳ)
open import Data.Bool using (true; false)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₂; [_,_]′) renaming (map₂ to sum-map₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Data.List.Relation.Unary.All using (All; _∷_) renaming ([] to []ᴬ; tabulate to tabulateᴬ; lookup to lookupᴬ; map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁻ to all-++⁻)
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
open import adequacy.Lowers using (module Lowering)

module Locality (R : Set) where
  open Heap using (Quiet; Sink; _∋_; same; cell; slot)
  open Shared Timeline (Out R) using (Heapᴹ; look; store; stored; Val; wkVal)
  open Strongly R
  open Moving R using (pairs-split; pairs-r; plant; plant-self; plantᴸ; planted; plantedᴸ; unsub-plant; count-plant; switches-plant)
  open Tearing R using (Off; Alike; names-path; lanes-path; fresh-path; narrow; apart-r; apart-l; ≢-flip; look-store; torn; tornVia; thrown; thrown-off;
    thrownLanes; thrownLanes-off; torn-off; tornVia-off; get-put-same; Site; takeSite; bodySite; siteHeap)
  open Run (Pureᴾ R) using (Env; Observer; module Kit; module FlatKit)
  open Lowering R using (module Lowers; via-lowers; thrown-lowers; lanes-lowers; dropped; false≢true)
  open Lowers using (lowers)

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

    gatedL-at : ∀ {h} {H : Heapᴹ h} {Δ B Δ′ A′} {X} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} → PathLanes ls u → At.GatedLanes H X ls → At.Gated H u
    gatedL-at (this-lane π) (_ , g , _) = gated-at π g
    gatedL-at (next-lane π) (_ , _ , gl) = gatedL-at π gl

  -- What a flatMap's kernel reads: its count, its lanes, its refill
  -- flag and every name under its head cells.
  flatReads : ∀ {h Δ A B} → FlatKit.Flat A h → Kit.Cut h → Maybe (Quiet h) → Sink h ⊤ → Sub h Δ A → List (Lane h Δ B) → List (Name h)
  flatReads fl oc k r so ls = (cell _ , FlatKit.Flat.active fl) ∷ (cell _ , FlatKit.Flat.lanes fl) ∷ (cell _ , FlatKit.Flat.refill fl)
                              ∷ cutNames oc ++ quietName k ++ (slot _ , r) ∷ names so ++ laneNames ls

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
      holds-alike (flatMapˢ op f fl oc k r pl so ls) ag = holds-flat {op = op} {f} {fl} {oc} {k} {r} {pl} so ls (λ j m → ag j (rd m))
        where
          rd : ∀ {x} → x ∈ᴸ flatReads fl oc k r so ls → x ∈ᴸ names (flatMapˢ op f fl oc k r pl so ls)
          rd (here e)                 = here e
          rd (there (here e))         = there (there (there (here e)))
          rd (there (there (here e))) = there (there (there (there (here e))))
          rd (there (there (there m))) = there (there (there (there (there m))))

      holds-alike (connectˢ S c b kb k fd rp e rt src bd) ag {E} {o} = holds-conn {S = S} {c} {b} {kb} {k} {fd} {rp} {e} {rt} src bd (λ j m → ag j (++⁺ʳ (subjectNames S) m)) {E} {o}
      holds-alike (joinˢ j sk l x st) ag hs = slot-alike sk (ag sk (here refl)) hs
      holds-alike (deferˢ k s) ag (st , hs) =
        stashed-alike k (λ j m → ag j (++⁺ˡ m)) st , holds-alike s (λ j m → ag j (++⁺ʳ (quietName k) m)) hs

      -- A connect's kernel reads none of its subject's cells.
      holds-conn : ∀ {Δ A B S c b kb k fd rp e rt} (src : Sub h Δ A) (bd : Sub h (A ∷ Δ) B)
                 → Alike H H′ (drop 2 (names (connectˢ S c b kb k fd rp e rt src bd)))
                 → ∀ {E o} → At.Holds H (connectˢ S c b kb k fd rp e rt src bd) E o → At.Holds H′ (connectˢ S c b kb k fd rp e rt src bd) E o
      holds-conn {c = c} {b} {kb} {k} src bd ag (a , be , st , hs , hb) =
        attached-alike c k (ag (Kit.held c) (there (here refl)))
                           (λ j m → ag j (++⁺ʳ (cutNames c) (there (++⁺ʳ (quietName kb) (++⁺ˡ m))))) a
        , trans (cong lower (ag b (++⁺ʳ (cutNames c) (here refl)))) be
        , stashed-alike kb (λ j m → ag j (++⁺ʳ (cutNames c) (there (++⁺ˡ m)))) st
        , holds-alike src (λ j m → ag j (++⁺ʳ (cutNames c) (there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ˡ m)))))) hs
        , holds-alike bd (λ j m → ag j (++⁺ʳ (cutNames c) (there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ʳ (names src) m)))))) hb

      -- A flatMap's kernel reads its count, its lanes, its refill flag
      -- and what lies under its head cells: never its done flag or its
      -- queue.
      holds-flat : ∀ {Δ A B op f fl oc k r pl} (so : Sub h Δ A) (ls : List (Lane h Δ B))
                 → Alike H H′ (flatReads fl oc k r so ls)
                 → ∀ {E o} → At.Holds H (flatMapˢ op f fl oc k r pl so ls) E o → At.Holds H′ (flatMapˢ op f fl oc k r pl so ls) E o
      holds-flat {op = op} {f} {fl} {oc} {k} {r} so ls ag {E} {o} (rf , sl , a , hs , ac , gn , hl) =
        trans (cong lower (ag (FlatKit.Flat.refill fl) (there (there (here refl))))) rf
        , slot-alike r (ag r (there (there (there (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (here refl))))))) sl
        , attached-alike oc k (ag (Kit.held oc) (there (there (there (there (here refl))))))
                              (λ j m → ag j (there (there (there (++⁺ʳ (cutNames oc) (++⁺ˡ m)))))) a
        , holds-alike so (λ j m → ag j (there (there (there (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ˡ m)))))))) hs
        , trans (cong lower (ag (FlatKit.Flat.active fl) (here refl))) (trans ac (sym (count-lives ls lv)))
        , gone-alike fl ls (ag (FlatKit.Flat.lanes fl) (there (here refl))) lv gn
        , holdsL-alike ls (λ j m → ag j (inL m)) {op = op} {f = f} {E = E} {o = o} {fl = fl} hl
        where
          inL : ∀ {x} → x ∈ᴸ laneNames ls → x ∈ᴸ flatReads fl oc k r so ls
          inL m = there (there (there (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ʳ (names so) m))))))
          lv : Lives ls
          lv {c} m = ag (Kit.live c) (inL (cut-in ls m))
      holdsL-alike : ∀ {Δ B} (ls : List (Lane h Δ B)) → Alike H H′ (laneNames ls)
                   → ∀ {A : Set} {op f E o fl} → At.HoldsLanes H {A = A} op f E o fl ls → At.HoldsLanes H′ {A = A} op f E o fl ls
      holdsL-alike []                ag hl = hl
      holdsL-alike (lane c k s ∷ ls) ag {op = op} {f = f} {E = E} {o = o} {fl = fl} (a , hs , hl) =
        attached-alike c k (ag (Kit.held c) (there (here refl))) (λ j m → ag j (++⁺ʳ (cutNames c) (++⁺ˡ m))) a
        , holds-alike s (λ j m → ag j (++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) (++⁺ˡ m)))) hs
        , holdsL-alike ls (λ j m → ag j (++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) (++⁺ʳ (names s) m)))) {op = op} {f = f} {E = E} {o = o} {fl = fl} hl

    mutual
      holds-path : ∀ {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (v : Sub h Δ′ A′) → AllPairs _≢_ (names (plant π v))
                 → Off H H′ (names v) → unsub u ≡ unsub v → (∀ {E o} → At.Holds H u E o → At.Holds H′ v E o)
                 → ∀ {E o} → At.Holds H t E o → At.Holds H′ (plant π v) E o
      holds-path here v         ps       off ue hv hs = hv hs
      holds-path (in-map π) v   ps       off ue hv hs = holds-path π v ps off ue hv hs
      holds-path (in-scan π) v  (_ ∷ ps) off ue hv hs = holds-path π v ps off ue hv hs
      holds-path (in-take {c = c} {k} π) v ps off ue hv (a , hs) =
        subst (At.Attached H′ c k) (sym (unsub-plant π v ue)) (attached-alike c k (keep off (λ m → ++⁺ʳ (quietName k) (names-path (planted π v) m)) (Kit.held c) (apart-r (cutNames c) ps (there (here refl))))
                           (keeps off (names-path (planted π v)) (apart-r (quietName k) (pairs-r (cutNames c) ps))) a)
        , holds-path π v (pairs-r (quietName k) (pairs-r (cutNames c) ps)) off ue hv hs
      holds-path (in-outer {op = op} {f} {fl} {oc} {k} {r} {t = so} {ls} π) v ps off ue hv {E} {o} (rf , sl , a , hs , ac , gn , hl) =
        trans (cong lower (keep off subF (FlatKit.Flat.refill fl) (apart-r (flatNames fl) ps (there (there (there (there (here refl)))))))) rf
        , slot-alike r (keep off (λ m → ++⁺ˡ (names-path (planted π v) m)) r (apart-r ((_ , r) ∷ []) P₃ (here refl))) sl
        , subst (At.Attached H′ oc k) (sym (unsub-plant π v ue)) (attached-alike oc k (keep off (λ m → ++⁺ʳ (quietName k) (there (++⁺ˡ (names-path (planted π v) m)))) (Kit.held oc) (apart-r (cutNames oc) P₁ (there (here refl))))
                              (keeps off (λ m → there (++⁺ˡ (names-path (planted π v) m))) (apart-r (quietName k) P₂)) a)
        , holds-path π v (proj₁ (pairs-split (names (plant π v)) P₄)) off ue hv hs
        , trans (cong lower (keep off subF (FlatKit.Flat.active fl) (apart-r (flatNames fl) ps (here refl)))) (trans ac (sym (count-lives ls lv)))
        , gone-alike fl ls (keep off subF (FlatKit.Flat.lanes fl) (apart-r (flatNames fl) ps (there (there (there (here refl)))))) lv gn
        , holdsL-alike ls (keeps off (names-path (planted π v)) (apart-l (names (plant π v)) P₄)) {op = op} {f = f} {E = E} {o = o} {fl = fl} hl
        where
          P₁ = pairs-r (flatNames fl) ps
          P₂ = pairs-r (cutNames oc) P₁
          P₃ = pairs-r (quietName k) P₂
          P₄ = pairs-r ((_ , r) ∷ []) P₃
          subF : ∀ {y} → y ∈ᴸ names v → y ∈ᴸ cutNames oc ++ quietName k ++ (_ , r) ∷ names (plant π v) ++ laneNames ls
          subF m = ++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ˡ (names-path (planted π v) m))))
          lv : Lives ls
          lv {c} m = keep off (names-path (planted π v)) (Kit.live c) (apart-l (names (plant π v)) P₄ (cut-in ls m))
      holds-path (in-lanes {op = op} {f} {fl} {oc} {k} {r} {t = so} {ls} π) v ps off ue hv {E} {o} (rf , sl , a , hs , ac , gn , hl) =
        trans (cong lower (keep off subF (FlatKit.Flat.refill fl) (apart-r (flatNames fl) ps (there (there (there (there (here refl)))))))) rf
        , slot-alike r (keep off (λ m → ++⁺ʳ (names so) (lanes-path (plantedᴸ π v) m)) r (apart-r ((_ , r) ∷ []) P₃ (here refl))) sl
        , attached-alike oc k (keep off (λ m → ++⁺ʳ (quietName k) (there (++⁺ʳ (names so) (lanes-path (plantedᴸ π v) m)))) (Kit.held oc) (apart-r (cutNames oc) P₁ (there (here refl))))
                              (keeps off (λ m → there (++⁺ʳ (names so) (lanes-path (plantedᴸ π v) m))) (apart-r (quietName k) P₂)) a
        , holds-alike so (keeps off (lanes-path (plantedᴸ π v)) (apart-r (names so) P₄)) hs
        , trans (cong lower (keep off subF (FlatKit.Flat.active fl) (apart-r (flatNames fl) ps (here refl))))
                (trans ac (trans (sym (count-plant H π v)) (sym (count-lives (plantᴸ π v) lv))))
        , gone-alike fl (plantᴸ π v) (keep off subF (FlatKit.Flat.lanes fl) (apart-r (flatNames fl) ps (there (there (there (here refl)))))) lv
                     (proj₁ gn , trans (proj₁ (proj₂ gn)) (sym (switches-plant H π v)) , proj₂ (proj₂ gn))
        , holdsL-path π v (pairs-r (names so) P₄) off ue hv {op = op} {f = f} {E = E} {o = o} {fl = fl} hl
        where
          P₁ = pairs-r (flatNames fl) ps
          P₂ = pairs-r (cutNames oc) P₁
          P₃ = pairs-r (quietName k) P₂
          P₄ = pairs-r ((_ , r) ∷ []) P₃
          subF : ∀ {y} → y ∈ᴸ names v → y ∈ᴸ cutNames oc ++ quietName k ++ (_ , r) ∷ names so ++ laneNames (plantᴸ π v)
          subF m = ++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ʳ (names so) (lanes-path (plantedᴸ π v) m))))
          lv : Lives (plantᴸ π v)
          lv {c} m = off (Kit.live c) (live-apart (plantedᴸ π v) (pairs-r (names so) P₄) m)
      holds-path (in-source {S = S} {c} {b} {kb} {k} {t = src} {bd} π) v ps off ue hv (a , be , st , hs , hb) =
        subst (At.Attached H′ c k) (sym (unsub-plant π v ue)) (attached-alike c k (keep off (λ m → there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ˡ (names-path (planted π v) m))))) (Kit.held c)
                                     (apart-r (cutNames c) Q₀ (there (here refl))))
                           (keeps off (λ m → ++⁺ˡ (names-path (planted π v) m)) (apart-r (quietName k) Q₃)) a)
        , trans (cong lower (keep off (λ m → ++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ˡ (names-path (planted π v) m)))) b (apart-r ((_ , b) ∷ []) Q₁ (here refl)))) be
        , stashed-alike kb (keeps off (λ m → ++⁺ʳ (quietName k) (++⁺ˡ (names-path (planted π v) m))) (apart-r (quietName kb) Q₂)) st
        , holds-path π v (proj₁ (pairs-split (names (plant π v)) Q₄)) off ue hv hs
        , holds-alike bd (keeps off (names-path (planted π v)) (apart-l (names (plant π v)) Q₄)) hb
        where
          Q₀ = pairs-r (subjectNames S) ps
          Q₁ = pairs-r (cutNames c) Q₀
          Q₂ = pairs-r ((_ , b) ∷ []) Q₁
          Q₃ = pairs-r (quietName kb) Q₂
          Q₄ = pairs-r (quietName k) Q₃
      holds-path (in-body {S = S} {c} {b} {kb} {k} {t = src} {bd} π) v ps off ue hv (a , be , st , hs , hb) =
        attached-alike c k (keep off (λ m → there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ʳ (names src) (names-path (planted π v) m))))) (Kit.held c)
                                     (apart-r (cutNames c) Q₀ (there (here refl))))
                           (keeps off (λ m → ++⁺ʳ (names src) (names-path (planted π v) m)) (apart-r (quietName k) Q₃)) a
        , trans (cong lower (keep off (λ m → ++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ʳ (names src) (names-path (planted π v) m)))) b (apart-r ((_ , b) ∷ []) Q₁ (here refl)))) be
        , subst (At.Stashed H′ kb) (sym (unsub-plant π v ue)) (stashed-alike kb (keeps off (λ m → ++⁺ʳ (quietName k) (++⁺ʳ (names src) (names-path (planted π v) m))) (apart-r (quietName kb) Q₂)) st)
        , holds-alike src (keeps off (names-path (planted π v)) (apart-r (names src) Q₄)) hs
        , holds-path π v (pairs-r (names src) Q₄) off ue hv hb
        where
          Q₀ = pairs-r (subjectNames S) ps
          Q₁ = pairs-r (cutNames c) Q₀
          Q₂ = pairs-r ((_ , b) ∷ []) Q₁
          Q₃ = pairs-r (quietName kb) Q₂
          Q₄ = pairs-r (quietName k) Q₃
      holds-path (in-defer {k = k} π) v ps off ue hv (st , hs) =
        subst (At.Stashed H′ k) (sym (unsub-plant π v ue)) (stashed-alike k (keeps off (names-path (planted π v)) (apart-r (quietName k) ps)) st) , holds-path π v (pairs-r (quietName k) ps) off ue hv hs

      holdsL-path : ∀ {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (π : PathLanes ls u) (v : Sub h Δ′ A′) → AllPairs _≢_ (laneNames (plantᴸ π v))
                  → Off H H′ (names v) → unsub u ≡ unsub v → (∀ {E o} → At.Holds H u E o → At.Holds H′ v E o)
                  → ∀ {A : Set} {op f E o fl} → At.HoldsLanes H {A = A} op f E o fl ls → At.HoldsLanes H′ {A = A} op f E o fl (plantᴸ π v)
      holdsL-path (this-lane {c = c} {k} {t = s} {ls} π) v ps off ue hv {op = op} {f = f} {E = E} {o = o} {fl = fl} (a , hs , hl) =
        subst (At.Attached H′ c k) (sym (unsub-plant π v ue)) (attached-alike c k (keep off (λ m → ++⁺ʳ (quietName k) (++⁺ˡ (names-path (planted π v) m))) (Kit.held c) (apart-r (cutNames c) ps (there (here refl))))
                           (keeps off (λ m → ++⁺ˡ (names-path (planted π v) m)) (apart-r (quietName k) (pairs-r (cutNames c) ps))) a)
        , holds-path π v (proj₁ (pairs-split (names (plant π v)) P)) off ue hv hs
        , holdsL-alike ls (keeps off (names-path (planted π v)) (apart-l (names (plant π v)) P)) {op = op} {f = f} {E = E} {o = o} {fl = fl} hl
        where P = pairs-r (quietName k) (pairs-r (cutNames c) ps)
      holdsL-path (next-lane {l = lane c k s} π) v ps off ue hv {op = op} {f = f} {E = E} {o = o} {fl = fl} (a , hs , hl) =
        attached-alike c k (keep off (λ m → ++⁺ʳ (quietName k) (++⁺ʳ (names s) (lanes-path (plantedᴸ π v) m))) (Kit.held c) (apart-r (cutNames c) ps (there (here refl))))
                           (keeps off (λ m → ++⁺ʳ (names s) (lanes-path (plantedᴸ π v) m)) (apart-r (quietName k) (pairs-r (cutNames c) ps))) a
        , holds-alike s (keeps off (lanes-path (plantedᴸ π v)) (apart-r (names s) P)) hs
        , holdsL-path π v (pairs-r (names s) P) off ue hv {op = op} {f = f} {E = E} {o = o} {fl = fl} hl
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
      spent-alike (connectˢ S c b kb k fd rp e rt src bd) ag = spent-conn {S = S} {c} {b} {kb} {k} {fd} {rp} {e} {rt} src bd (λ j m → ag j (++⁺ʳ (subjectNames S) m))
      spent-alike (joinˢ j sk l x st) ag sp = sp
      spent-alike (deferˢ k s) ag sp = cut-alike k s (λ j m → ag j (++⁺ʳ (quietName k) m)) sp

      spent-conn : ∀ {Δ A B S c b kb k fd rp e rt} (src : Sub h Δ A) (bd : Sub h (A ∷ Δ) B)
                 → Alike H H′ (drop 2 (names (connectˢ S c b kb k fd rp e rt src bd)))
                 → At.Spent H (connectˢ S c b kb k fd rp e rt src bd) → At.Spent H′ (connectˢ S c b kb k fd rp e rt src bd)
      spent-conn {c = c} {b} {kb} {k} src bd ag (c₁ , c₂) =
        cut-alike k src (λ j m → ag j (++⁺ʳ (cutNames c) (there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ˡ m)))))) c₁
        , cut-alike kb bd (λ j m → ag j (++⁺ʳ (cutNames c) (there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ʳ (names src) m)))))) c₂

      spentL-alike : ∀ {Δ B} (ls : List (Lane h Δ B)) → Alike H H′ (laneNames ls) → At.SpentLanes H ls → At.SpentLanes H′ ls
      spentL-alike []                ag sp = sp
      spentL-alike (lane c k s ∷ ls) ag (c₁ , c₂) =
        cut-alike k s (λ j m → ag j (++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) (++⁺ˡ m)))) c₁
        , spentL-alike ls (λ j m → ag j (++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) (++⁺ʳ (names s) m)))) c₂

      cut-alike : ∀ {Δ A} (k : Maybe (Quiet h)) (s : Sub h Δ A) → Alike H H′ (names s) → At.Cut↓ H k s → At.Cut↓ H′ k s
      cut-alike nothing  s ag sp = sp
      cut-alike (just _) s ag sp = spent-alike s ag sp

    mutual
      spent-path : ∀ {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (v : Sub h Δ′ A′) → AllPairs _≢_ (names (plant π v))
                 → Off H H′ (names v) → (At.Spent H u → At.Spent H′ v) → At.Spent H t → At.Spent H′ (plant π v)
      spent-path here v        ps       off hv sp = hv sp
      spent-path (in-map π) v  ps       off hv sp = spent-path π v ps off hv sp
      spent-path (in-scan π) v (_ ∷ ps) off hv sp = spent-path π v ps off hv sp
      spent-path (in-take {c = c} {k} π) v ps off hv sp = cut-path k π v (pairs-r (quietName k) (pairs-r (cutNames c) ps)) off hv sp
      spent-path (in-outer {fl = fl} {oc} {k} {r} {t = so} {ls} π) v ps off hv (c₁ , c₂) =
        cut-path k π v (proj₁ (pairs-split (names (plant π v)) P)) off hv c₁ , spentL-alike ls (keeps off (names-path (planted π v)) (apart-l (names (plant π v)) P)) c₂
        where P = pairs-r ((_ , r) ∷ []) (pairs-r (quietName k) (pairs-r (cutNames oc) (pairs-r (flatNames fl) ps)))
      spent-path (in-lanes {fl = fl} {oc} {k} {r} {t = so} {ls} π) v ps off hv (c₁ , c₂) =
        cut-alike k so (keeps off (lanes-path (plantedᴸ π v)) (apart-r (names so) P)) c₁ , spentL-path π v (pairs-r (names so) P) off hv c₂
        where P = pairs-r ((_ , r) ∷ []) (pairs-r (quietName k) (pairs-r (cutNames oc) (pairs-r (flatNames fl) ps)))
      spent-path (in-source {S = S} {c} {b} {kb} {k} {t = src} {bd} π) v ps off hv (c₁ , c₂) =
        cut-path k π v (proj₁ (pairs-split (names (plant π v)) Q)) off hv c₁ , cut-alike kb bd (keeps off (names-path (planted π v)) (apart-l (names (plant π v)) Q)) c₂
        where Q = pairs-r (quietName k) (pairs-r (quietName kb) (pairs-r ((_ , b) ∷ []) (pairs-r (cutNames c) (pairs-r (subjectNames S) ps))))
      spent-path (in-body {S = S} {c} {b} {kb} {k} {t = src} {bd} π) v ps off hv (c₁ , c₂) =
        cut-alike k src (keeps off (names-path (planted π v)) (apart-r (names src) Q)) c₁ , cut-path kb π v (pairs-r (names src) Q) off hv c₂
        where Q = pairs-r (quietName k) (pairs-r (quietName kb) (pairs-r ((_ , b) ∷ []) (pairs-r (cutNames c) (pairs-r (subjectNames S) ps))))
      spent-path (in-defer {k = k} π) v ps off hv sp = cut-path k π v (pairs-r (quietName k) ps) off hv sp

      spentL-path : ∀ {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (π : PathLanes ls u) (v : Sub h Δ′ A′) → AllPairs _≢_ (laneNames (plantᴸ π v))
                  → Off H H′ (names v) → (At.Spent H u → At.Spent H′ v) → At.SpentLanes H ls → At.SpentLanes H′ (plantᴸ π v)
      spentL-path (this-lane {c = c} {k} {t = s} {ls} π) v ps off hv (c₁ , c₂) =
        cut-path k π v (proj₁ (pairs-split (names (plant π v)) P)) off hv c₁ , spentL-alike ls (keeps off (names-path (planted π v)) (apart-l (names (plant π v)) P)) c₂
        where P = pairs-r (quietName k) (pairs-r (cutNames c) ps)
      spentL-path (next-lane {l = lane c k s} π) v ps off hv (c₁ , c₂) =
        cut-alike k s (keeps off (lanes-path (plantedᴸ π v)) (apart-r (names s) P)) c₁ , spentL-path π v (pairs-r (names s) P) off hv c₂
        where P = pairs-r (quietName k) (pairs-r (cutNames c) ps)

      cut-path : ∀ {Δ A Δ′ A′} (k : Maybe (Quiet h)) {s : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path s u) (v : Sub h Δ′ A′) → AllPairs _≢_ (names (plant π v))
               → Off H H′ (names v) → (At.Spent H u → At.Spent H′ v) → At.Cut↓ H k s → At.Cut↓ H′ k (plant π v)
      cut-path nothing  π v ps off hv sp = sp
      cut-path (just _) π v ps off hv sp = spent-path π v ps off hv sp

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
        , subst (λ X → At.GatedLanes H′ X ls) (cong lower (sym (ag (FlatKit.Flat.lanes fl) (there (there (there (here refl)))))))
            (gatedL-alike ls (λ j m → ag j (++⁺ʳ (flatNames fl) (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ʳ (names so) m)))))) g₂)
      gated-alike (connectˢ S c b kb k fd rp e rt src bd) ag = gated-conn {S = S} {c} {b} {kb} {k} {fd} {rp} {e} {rt} src bd (λ j m → ag j (++⁺ʳ (subjectNames S) m))
      gated-alike (joinˢ j sk l x st) ag g = g
      gated-alike (deferˢ k s) ag g = gated-alike s (λ j m → ag j (++⁺ʳ (quietName k) m)) g

      gated-conn : ∀ {Δ A B S c b kb k fd rp e rt} (src : Sub h Δ A) (bd : Sub h (A ∷ Δ) B)
                 → Alike H H′ (drop 2 (names (connectˢ S c b kb k fd rp e rt src bd)))
                 → At.Gated H (connectˢ S c b kb k fd rp e rt src bd) → At.Gated H′ (connectˢ S c b kb k fd rp e rt src bd)
      gated-conn {c = c} {b} {kb} {k} src bd ag (g₁ , g₂ , g₃) =
        (λ e → cut-alike k src agS (thrown-alike c (ag (Kit.live c) (here refl)) g₁ e))
        , gated-alike src agS g₂
        , gated-alike bd (λ j m → ag j (++⁺ʳ (cutNames c) (there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ʳ (names src) m)))))) g₃
        where
          agS : Alike H H′ (names src)
          agS j m = ag j (++⁺ʳ (cutNames c) (there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ˡ m)))))

      gatedL-alike : ∀ {Δ B X} (ls : List (Lane h Δ B)) → Alike H H′ (laneNames ls) → At.GatedLanes H X ls → At.GatedLanes H′ X ls
      gatedL-alike []                ag g = g
      gatedL-alike (lane c k s ∷ ls) ag (g₁ , g₂ , g₃) =
        (λ e → sum-map₂ (cut-alike k s agS) (thrown-alike c (ag (Kit.live c) (here refl)) g₁ e)) , gated-alike s agS g₂
        , gatedL-alike ls (λ j m → ag j (++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) (++⁺ʳ (names s) m)))) g₃
        where
          agS : Alike H H′ (names s)
          agS j m = ag j (++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) (++⁺ˡ m)))

    mutual
      gated-path : ∀ {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (v : Sub h Δ′ A′) → AllPairs _≢_ (names (plant π v)) → Off H H′ (names v)
                 → (At.Gated H u → At.Gated H′ v) → (At.Spent H u → At.Spent H′ v) → At.Gated H t → At.Gated H′ (plant π v)
      gated-path here v        ps       off hg hs g = hg g
      gated-path (in-map π) v  ps       off hg hs g = gated-path π v ps off hg hs g
      gated-path (in-scan π) v (_ ∷ ps) off hg hs g = gated-path π v ps off hg hs g
      gated-path (in-take {c = c} {k} π) v ps off hg hs (g₁ , g₂) =
        (λ e → cut-path k π v P off hs (thrown-alike c lc g₁ e)) , gated-path π v P off hg hs g₂
        where
          P = pairs-r (quietName k) (pairs-r (cutNames c) ps)
          lc = keep off (λ m → ++⁺ʳ (quietName k) (names-path (planted π v) m)) (Kit.live c) (apart-r (cutNames c) ps (here refl))
      gated-path (in-outer {fl = fl} {oc} {k} {r} {t = so} {ls} π) v ps off hg hs (g₁ , g₂) =
        gated-path π v (proj₁ (pairs-split (names (plant π v)) P)) off hg hs g₁
        , subst (λ X → At.GatedLanes H′ X ls) (cong lower (sym lc)) (gatedL-alike ls (keeps off (names-path (planted π v)) (apart-l (names (plant π v)) P)) g₂)
        where
          P = pairs-r ((_ , r) ∷ []) (pairs-r (quietName k) (pairs-r (cutNames oc) (pairs-r (flatNames fl) ps)))
          lc = keep off (λ m → ++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ˡ (names-path (planted π v) m))))) (FlatKit.Flat.lanes fl)
                 (apart-r (flatNames fl) ps (there (there (there (here refl)))))
      gated-path (in-lanes {fl = fl} {oc} {k} {r} {t = so} {ls} π) v ps off hg hs (g₁ , g₂) =
        gated-alike so (keeps off (lanes-path (plantedᴸ π v)) (apart-r (names so) P)) g₁
        , subst (λ X → At.GatedLanes H′ X (plantᴸ π v)) (cong lower (sym lc)) (gatedL-path π v (pairs-r (names so) P) off hg hs g₂)
        where
          P = pairs-r ((_ , r) ∷ []) (pairs-r (quietName k) (pairs-r (cutNames oc) (pairs-r (flatNames fl) ps)))
          lc = keep off (λ m → ++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ʳ (names so) (lanes-path (plantedᴸ π v) m))))) (FlatKit.Flat.lanes fl)
                 (apart-r (flatNames fl) ps (there (there (there (here refl)))))
      gated-path (in-source {S = S} {c} {b} {kb} {k} {t = src} {bd} π) v ps off hg hs (g₁ , g₂ , g₃) =
        (λ e → cut-path k π v Ps off hs (thrown-alike c lc g₁ e)) , gated-path π v Ps off hg hs g₂
        , gated-alike bd (keeps off (names-path (planted π v)) (apart-l (names (plant π v)) Q₄)) g₃
        where
          Q₀ = pairs-r (subjectNames S) ps
          Q₄ = pairs-r (quietName k) (pairs-r (quietName kb) (pairs-r ((_ , b) ∷ []) (pairs-r (cutNames c) Q₀)))
          Ps = proj₁ (pairs-split (names (plant π v)) Q₄)
          lc = keep off (λ m → there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ˡ (names-path (planted π v) m))))) (Kit.live c) (apart-r (cutNames c) Q₀ (here refl))
      gated-path (in-body {S = S} {c} {b} {kb} {k} {t = src} {bd} π) v ps off hg hs (g₁ , g₂ , g₃) =
        (λ e → cut-alike k src agS (thrown-alike c lc g₁ e)) , gated-alike src agS g₂ , gated-path π v (pairs-r (names src) Q₄) off hg hs g₃
        where
          Q₀ = pairs-r (subjectNames S) ps
          Q₄ = pairs-r (quietName k) (pairs-r (quietName kb) (pairs-r ((_ , b) ∷ []) (pairs-r (cutNames c) Q₀)))
          agS = keeps off (names-path (planted π v)) (apart-r (names src) Q₄)
          lc = keep off (λ m → there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ʳ (names src) (names-path (planted π v) m))))) (Kit.live c) (apart-r (cutNames c) Q₀ (here refl))
      gated-path (in-defer {k = k} π) v ps off hg hs g = gated-path π v (pairs-r (quietName k) ps) off hg hs g

      gatedL-path : ∀ {Δ B Δ′ A′ X} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (π : PathLanes ls u) (v : Sub h Δ′ A′) → AllPairs _≢_ (laneNames (plantᴸ π v)) → Off H H′ (names v)
                  → (At.Gated H u → At.Gated H′ v) → (At.Spent H u → At.Spent H′ v) → At.GatedLanes H X ls → At.GatedLanes H′ X (plantᴸ π v)
      gatedL-path (this-lane {c = c} {k} {t = s} {ls} π) v ps off hg hs (g₁ , g₂ , g₃) =
        (λ e → sum-map₂ (cut-path k π v Ps off hs) (thrown-alike c lc g₁ e)) , gated-path π v Ps off hg hs g₂
        , gatedL-alike ls (keeps off (names-path (planted π v)) (apart-l (names (plant π v)) P)) g₃
        where
          P = pairs-r (quietName k) (pairs-r (cutNames c) ps)
          Ps = proj₁ (pairs-split (names (plant π v)) P)
          lc = keep off (λ m → ++⁺ʳ (quietName k) (++⁺ˡ (names-path (planted π v) m))) (Kit.live c) (apart-r (cutNames c) ps (here refl))
      gatedL-path (next-lane {l = lane c k s} π) v ps off hg hs (g₁ , g₂ , g₃) =
        (λ e → sum-map₂ (cut-alike k s agS) (thrown-alike c lc g₁ e)) , gated-alike s agS g₂ , gatedL-path π v (pairs-r (names s) P) off hg hs g₃
        where
          P = pairs-r (quietName k) (pairs-r (cutNames c) ps)
          agS = keeps off (lanes-path (plantedᴸ π v)) (apart-r (names s) P)
          lc = keep off (λ m → ++⁺ʳ (quietName k) (++⁺ʳ (names s) (lanes-path (plantedᴸ π v) m))) (Kit.live c) (apart-r (cutNames c) ps (here refl))

    ----------------------------------------------------------------------
    -- FED

    mutual
      fed-alike : ∀ {Δ A} (u : Sub h Δ A) → Alike H H′ (names u) → ∀ ν → At.Fed H u ν → At.Fed H′ u ν
      fed-alike (pendingˢ s q)  ag ν fd = fd
      fed-alike (coldˢ s hd ph) ag ν fd = fd
      fed-alike (ofˢ p i xs)    ag ν fd = fd
      fed-alike doneˢ           ag ν fd = fd
      fed-alike (mapˢ f s)      ag ν fd = fed-alike s ag ν fd
      fed-alike (scanˢ f r s)   ag ν fd = fed-alike s (λ j m → ag j (there m)) ν fd
      fed-alike (takeWhileˢ i p c k tk s) ag ν fd = fed-alike s (λ j m → ag j (++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) m))) ν fd
      fed-alike (flatMapˢ op f fl oc k r pl so ls) ag ν (f₁ , f₂) =
        fed-alike so (λ j m → ag j (++⁺ʳ (flatNames fl) (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ˡ m)))))) ν f₁
        , fedL-alike ls (λ j m → ag j (++⁺ʳ (flatNames fl) (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ʳ (names so) m)))))) ν f₂
      fed-alike (connectˢ S c b kb k fd rp e rt src bd) ag = fed-conn {S = S} {c} {b} {kb} {k} {fd} {rp} {e} {rt} src bd (λ j m → ag j (++⁺ʳ (subjectNames S) m))
      fed-alike (joinˢ j sk l x st) ag ν (lift g) = lift (λ e → g (trans (cong lower (sym (ag l (there (here refl))))) e))
      fed-alike (deferˢ k s) ag ν fd = fed-alike s (λ j m → ag j (++⁺ʳ (quietName k) m)) ν fd

      fed-conn : ∀ {Δ A B S c b kb k fd rp e rt} (src : Sub h Δ A) (bd : Sub h (A ∷ Δ) B)
               → Alike H H′ (drop 2 (names (connectˢ S c b kb k fd rp e rt src bd)))
               → ∀ ν → At.Fed H (connectˢ S c b kb k fd rp e rt src bd) ν → At.Fed H′ (connectˢ S c b kb k fd rp e rt src bd) ν
      fed-conn {c = c} {b} {kb} {k} src bd ag ν (f₁ , f₂) =
        fed-alike src (λ j m → ag j (++⁺ʳ (cutNames c) (there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ˡ m)))))) ν f₁
        , fed-alike bd (λ j m → ag j (++⁺ʳ (cutNames c) (there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ʳ (names src) m)))))) _ f₂

      fedL-alike : ∀ {Δ B} (ls : List (Lane h Δ B)) → Alike H H′ (laneNames ls) → ∀ ν → At.FedLanes H ls ν → At.FedLanes H′ ls ν
      fedL-alike []                ag ν fl = fl
      fedL-alike (lane c k s ∷ ls) ag ν (f₁ , f₂) =
        fed-alike s (λ j m → ag j (++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) (++⁺ˡ m)))) ν f₁
        , fedL-alike ls (λ j m → ag j (++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) (++⁺ʳ (names s) m)))) ν f₂

    ----------------------------------------------------------------------
    -- A flatMap whose reads are alike: its done flag and queue free to move

    flat-so : ∀ {Δ A B fl oc k r} {so : Sub h Δ A} {ls : List (Lane h Δ B)} → Alike H H′ (flatReads fl oc k r so ls) → Alike H H′ (names so)
    flat-so {oc = oc} {k} ag j m = ag j (there (there (there (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ˡ m)))))))

    flat-ls : ∀ {Δ A B fl oc k r} {so : Sub h Δ A} {ls : List (Lane h Δ B)} → Alike H H′ (flatReads fl oc k r so ls) → Alike H H′ (laneNames ls)
    flat-ls {oc = oc} {k} {so = so} ag j m = ag j (there (there (there (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ʳ (names so) m)))))))

    gated-flat : ∀ {Δ A B op f fl oc k r pl} (so : Sub h Δ A) (ls : List (Lane h Δ B)) → Alike H H′ (flatReads fl oc k r so ls)
               → At.Gated H (flatMapˢ op f fl oc k r pl so ls) → At.Gated H′ (flatMapˢ op f fl oc k r pl so ls)
    gated-flat {fl = fl} {oc} {k} {r} so ls ag (g₁ , g₂) =
      gated-alike so (flat-so {fl = fl} {oc} {k} {r} {so} {ls} ag) g₁
      , subst (λ X → At.GatedLanes H′ X ls) (cong lower (sym (ag (FlatKit.Flat.lanes fl) (there (here refl))))) (gatedL-alike ls (flat-ls {fl = fl} {oc} {k} {r} {so} {ls} ag) g₂)

    spent-flat : ∀ {Δ A B op f fl oc k r pl} (so : Sub h Δ A) (ls : List (Lane h Δ B)) → Alike H H′ (flatReads fl oc k r so ls)
               → At.Spent H (flatMapˢ op f fl oc k r pl so ls) → At.Spent H′ (flatMapˢ op f fl oc k r pl so ls)
    spent-flat {fl = fl} {oc} {k} {r} so ls ag (c₁ , c₂) =
      cut-alike k so (flat-so {fl = fl} {oc} {k} {r} {so} {ls} ag) c₁ , spentL-alike ls (flat-ls {fl = fl} {oc} {k} {r} {so} {ls} ag) c₂

    fed-flat : ∀ {Δ A B op f fl oc k r pl} (so : Sub h Δ A) (ls : List (Lane h Δ B)) → Alike H H′ (flatReads fl oc k r so ls)
             → ∀ ν → At.Fed H (flatMapˢ op f fl oc k r pl so ls) ν → At.Fed H′ (flatMapˢ op f fl oc k r pl so ls) ν
    fed-flat {fl = fl} {oc} {k} {r} so ls ag ν (f₁ , f₂) =
      fed-alike so (flat-so {fl = fl} {oc} {k} {r} {so} {ls} ag) ν f₁ , fedL-alike ls (flat-ls {fl = fl} {oc} {k} {r} {so} {ls} ag) ν f₂

    mutual
      fed-path : ∀ {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (v : Sub h Δ′ A′) → AllPairs _≢_ (names (plant π v)) → Off H H′ (names v)
               → (∀ ν → At.Fed H u ν → At.Fed H′ v ν) → ∀ ν → At.Fed H t ν → At.Fed H′ (plant π v) ν
      fed-path here v        ps       off hv ν fd = hv ν fd
      fed-path (in-map π) v  ps       off hv ν fd = fed-path π v ps off hv ν fd
      fed-path (in-scan π) v (_ ∷ ps) off hv ν fd = fed-path π v ps off hv ν fd
      fed-path (in-take {c = c} {k} π) v ps off hv ν fd = fed-path π v (pairs-r (quietName k) (pairs-r (cutNames c) ps)) off hv ν fd
      fed-path (in-outer {fl = fl} {oc} {k} {r} {t = so} {ls} π) v ps off hv ν (f₁ , f₂) =
        fed-path π v (proj₁ (pairs-split (names (plant π v)) P)) off hv ν f₁ , fedL-alike ls (keeps off (names-path (planted π v)) (apart-l (names (plant π v)) P)) ν f₂
        where P = pairs-r ((_ , r) ∷ []) (pairs-r (quietName k) (pairs-r (cutNames oc) (pairs-r (flatNames fl) ps)))
      fed-path (in-lanes {fl = fl} {oc} {k} {r} {t = so} {ls} π) v ps off hv ν (f₁ , f₂) =
        fed-alike so (keeps off (lanes-path (plantedᴸ π v)) (apart-r (names so) P)) ν f₁ , fedL-path π v (pairs-r (names so) P) off hv ν f₂
        where P = pairs-r ((_ , r) ∷ []) (pairs-r (quietName k) (pairs-r (cutNames oc) (pairs-r (flatNames fl) ps)))
      fed-path (in-source {S = S} {c} {b} {kb} {k} {t = src} {bd} π) v ps off hv ν (f₁ , f₂) =
        fed-path π v (proj₁ (pairs-split (names (plant π v)) Q₄)) off hv ν f₁ , fed-alike bd (keeps off (names-path (planted π v)) (apart-l (names (plant π v)) Q₄)) _ f₂
        where Q₄ = pairs-r (quietName k) (pairs-r (quietName kb) (pairs-r ((_ , b) ∷ []) (pairs-r (cutNames c) (pairs-r (subjectNames S) ps))))
      fed-path (in-body {S = S} {c} {b} {kb} {k} {t = src} {bd} π) v ps off hv ν (f₁ , f₂) =
        fed-alike src (keeps off (names-path (planted π v)) (apart-r (names src) Q₄)) ν f₁ , fed-path π v (pairs-r (names src) Q₄) off hv _ f₂
        where Q₄ = pairs-r (quietName k) (pairs-r (quietName kb) (pairs-r ((_ , b) ∷ []) (pairs-r (cutNames c) (pairs-r (subjectNames S) ps))))
      fed-path (in-defer {k = k} π) v ps off hv ν fd = fed-path π v (pairs-r (quietName k) ps) off hv ν fd

      fedL-path : ∀ {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (π : PathLanes ls u) (v : Sub h Δ′ A′) → AllPairs _≢_ (laneNames (plantᴸ π v)) → Off H H′ (names v)
                → (∀ ν → At.Fed H u ν → At.Fed H′ v ν) → ∀ ν → At.FedLanes H ls ν → At.FedLanes H′ (plantᴸ π v) ν
      fedL-path (this-lane {c = c} {k} {t = s} {ls} π) v ps off hv ν (f₁ , f₂) =
        fed-path π v (proj₁ (pairs-split (names (plant π v)) P)) off hv ν f₁ , fedL-alike ls (keeps off (names-path (planted π v)) (apart-l (names (plant π v)) P)) ν f₂
        where P = pairs-r (quietName k) (pairs-r (cutNames c) ps)
      fedL-path (next-lane {l = lane c k s} π) v ps off hv ν (f₁ , f₂) =
        fed-alike s (keeps off (lanes-path (plantedᴸ π v)) (apart-r (names s) P)) ν f₁ , fedL-path π v (pairs-r (names s) P) off hv ν f₂
        where P = pairs-r (quietName k) (pairs-r (cutNames c) ps)

    -- The tree kept, only the node's names moved.
    private
      self-pairs : ∀ {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) → AllPairs _≢_ (names t) → AllPairs _≢_ (names (plant π u))
      self-pairs π = subst (λ t → AllPairs _≢_ (names t)) (sym (plant-self π))

    holds-same : ∀ {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) → AllPairs _≢_ (names t) → Off H H′ (names u)
               → (∀ {E o} → At.Holds H u E o → At.Holds H′ u E o) → ∀ {E o} → At.Holds H t E o → At.Holds H′ t E o
    holds-same {u = u} π ps off hv {E} {o} hs = subst (λ t → At.Holds H′ t E o) (plant-self π) (holds-path π u (self-pairs π ps) off refl hv hs)

    gated-same : ∀ {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) → AllPairs _≢_ (names t) → Off H H′ (names u)
               → (At.Gated H u → At.Gated H′ u) → (At.Spent H u → At.Spent H′ u) → At.Gated H t → At.Gated H′ t
    gated-same {u = u} π ps off gv sv g = subst (At.Gated H′) (plant-self π) (gated-path π u (self-pairs π ps) off gv sv g)

    fed-same : ∀ {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) → AllPairs _≢_ (names t) → Off H H′ (names u)
             → (∀ ν → At.Fed H u ν → At.Fed H′ u ν) → ∀ ν → At.Fed H t ν → At.Fed H′ t ν
    fed-same {u = u} π ps off fv ν f = subst (λ t → At.Fed H′ t ν) (plant-self π) (fed-path π u (self-pairs π ps) off fv ν f)

  ----------------------------------------------------------------------
  -- AN UNSUBSCRIBE, AT ITS OWN NODE: what it leaves of the kernel, the
  -- spent and the gates of the subscription it tears.  Elsewhere `Off`
  -- carries each part across, so these are all a cut owes the relation.

  pair-head : ∀ {a} {X : Set a} {x : X} {xs} → AllPairs _≢_ (x ∷ xs) → All (x ≢_) xs
  pair-head (a ∷ _) = a

  stored-at : ∀ {h k} (H : Heapᴹ h) (i : h ∋ k) (x : Val h k) → look (store H i x) i ≡ wkVal k same x
  stored-at H i x rewrite get-put-same H i {y = stored x same} = refl

  stored-hit : ∀ {h k} (H : Heapᴹ h) (i j : h ∋ k) {x : Val h k} → _≡_ {A = Name h} (k , i) (k , j) → look (store H i x) j ≡ wkVal k same x
  stored-hit H i .i {x} refl = stored-at H i x

  -- A switch thrown: what it holds read alike, beside the switch itself.
  module Throw {h} (H : Heapᴹ h) (c : Kit.Cut h) (k : Maybe (Quiet h)) {Δ A} (s : Sub h Δ A) {ns : List (Name h)}
               (sub : ∀ {y} → y ∈ᴸ names s → y ∈ᴸ ns) (ps : AllPairs _≢_ (cutNames c ++ quietName k ++ ns)) where
    H₀ = store H (Kit.live c) (lift false)

    ag₀ : Alike H H₀ (names s)
    ag₀ j m = look-store H (Kit.live c) j (lookupᴬ (apart-r (cutNames c) ps (here refl)) (++⁺ʳ (quietName k) (sub m)))

    eh : look (thrown H c k s) (Kit.held c) ≡ look H (Kit.held c)
    eh = thrown-off H c k s (Kit.held c) (≢-flip (lookupᴬ (pair-head ps) (here refl)))
                    (narrow (λ m → ++⁺ʳ (quietName k) (sub m)) (apart-r (cutNames c) ps (there (here refl))))

    agk : Alike H (thrown H c k s) (quietName k)
    agk j m = thrown-off H c k s j (lookupᴬ (apart-l (cutNames c) ps (++⁺ˡ m)) (here refl)) (narrow sub (apart-r (quietName k) (pairs-r (cutNames c) ps) m))

  -- The lanes a flatMap throws, and those already gone, all read thrown.
  lanes-dead : ∀ {h} (H : Heapᴹ h) (xs gone : List (Kit.Cut h)) {Δ B} (ls : List (Lane h Δ B)) → xs ++ gone ≡ cuts ls
             → All (λ c → At.val H (Kit.live c) ≡ false) gone → All (λ c → At.val (thrownLanes H (length xs) ls) (Kit.live c) ≡ false) (cuts ls)
  lanes-dead H []       gone ls eq ga = subst (All (λ c → At.val H (Kit.live c) ≡ false)) eq ga
  lanes-dead H (x ∷ xs) gone [] () ga
  lanes-dead H (x ∷ xs) gone (lane c k s ∷ ls) eq ga =
    lowers (lanes-lowers (thrown H c k s) (length xs) ls) (Kit.live c) (lowers (via-lowers _ k s) (Kit.live c) (dropped H (Kit.live c)))
    ∷ lanes-dead (thrown H c k s) xs gone ls (∷-injectiveʳ eq) (mapᴬ (λ {c′} e → lowers (thrown-lowers H c k s) (Kit.live c′) e) ga)

  count-dead : ∀ {h} (H : Heapᴹ h) {Δ B} (ls : List (Lane h Δ B)) → All (λ c → At.val H (Kit.live c) ≡ false) (cuts ls) → At.count H ls ≡ 0
  count-dead H []                d       = refl
  count-dead H (lane c k s ∷ ls) (e ∷ d) rewrite e = count-dead H ls d

  -- A gone lane is not among those its flatMap still lists.
  listed-apart : ∀ {h Δ B} (ls : List (Lane h Δ B)) → AllPairs _≢_ (laneNames ls)
               → ∀ xs {gone} → xs ++ gone ≡ cuts ls → ∀ {c} → c ∈ᴸ gone → c ∈ᴸ xs → ⊥
  listed-apart ls                ps []       eq g ()
  listed-apart []                ps (x ∷ xs) () g m
  listed-apart (lane c k s ∷ ls) ps (x ∷ xs) eq g (here refl) =
    lookupᴬ (apart-r (cutNames c) ps (here refl))
      (++⁺ʳ (quietName k) (++⁺ʳ (names s) (cut-in ls (subst (λ y → y ∈ᴸ cuts ls) (∷-injectiveˡ eq) (subst (_ ∈ᴸ_) (∷-injectiveʳ eq) (++⁺ʳ xs g)))))) refl
  listed-apart (lane c k s ∷ ls) ps (x ∷ xs) eq g (there m) =
    listed-apart ls (pairs-r (names s) (pairs-r (quietName k) (pairs-r (cutNames c) ps))) xs (∷-injectiveʳ eq) g m

  -- A lane whose switch reads thrown and that is not listed is cut, by its gate.
  spentL-dead : ∀ {h} (H : Heapᴹ h) {Δ B} (X : List (Kit.Cut h)) (ls : List (Lane h Δ B)) → All (λ c → At.val H (Kit.live c) ≡ false) (cuts ls)
              → All (λ c → c ∈ᴸ X → ⊥) (cuts ls) → At.GatedLanes H X ls → At.SpentLanes H ls
  spentL-dead H X []                d       n        g             = lift tt
  spentL-dead H X (lane c k s ∷ ls) (e ∷ d) (n ∷ ns) (g₁ , _ , g₃) = [ (λ m → ⊥-elim (n m)) , (λ x → x) ]′ (g₁ e) , spentL-dead H X ls d ns g₃

  -- Lanes spent are gated against any listing.
  gatedL-spent : ∀ {h} {H : Heapᴹ h} {Δ B} {X Y : List (Kit.Cut h)} (ls : List (Lane h Δ B)) → At.SpentLanes H ls → At.GatedLanes H X ls → At.GatedLanes H Y ls
  gatedL-spent []                sp        g             = lift tt
  gatedL-spent (lane c k s ∷ ls) (c₁ , sp) (_ , g₂ , g₃) = (λ _ → inj₂ c₁) , g₂ , gatedL-spent ls sp g₃

  cut-of : ∀ {h} {H : Heapᴹ h} (k : Maybe (Quiet h)) {Δ A} {s : Sub h Δ A} → At.Spent H s → At.Cut↓ H k s
  cut-of nothing  sp = lift tt
  cut-of (just _) sp = sp

  -- A flatMap torn: its outer thrown, its counts cleared, its lanes in
  -- flight thrown.  The lanes it holds are the first so many of its
  -- lanes and the rest are gone, so none is left live.
  module FlatTear {h} (H : Heapᴹ h) {Δ A B op f fl oc k r pl} {so : Sub h Δ A} {ls : List (Lane h Δ B)}
                  (ps : AllPairs _≢_ (names (flatMapˢ op f fl oc k r pl so ls))) where
    H′ = thrown H oc k so
    H₁ = store H′ (FlatKit.Flat.lanes fl) (lift [])
    H₂ = store H₁ (FlatKit.Flat.active fl) (lift 0)
    xs = lower (look H′ (FlatKit.Flat.lanes fl))
    Ht = thrownLanes H₂ (length xs) ls

    P₁ = pairs-r (flatNames fl) ps
    P₂ = pairs-r (cutNames oc) P₁
    P₃ = pairs-r (quietName k) P₂
    P₄ = pairs-r ((_ , r) ∷ []) P₃
    PS = proj₁ (pairs-split (names so) P₄)
    PL = pairs-r (names so) P₄

    module T = Throw H oc k so (λ m → there (++⁺ˡ m)) P₁

    aA = apart-r (flatNames fl) ps (here refl)
    aL = apart-r (flatNames fl) ps (there (there (there (here refl))))
    aR = apart-r (flatNames fl) ps (there (there (there (there (here refl)))))

    inS : ∀ {x} → x ∈ᴸ names so → x ∈ᴸ cutNames oc ++ quietName k ++ (_ , r) ∷ names so ++ laneNames ls
    inS m = ++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ˡ m)))

    inL : ∀ {x} → x ∈ᴸ laneNames ls → x ∈ᴸ cutNames oc ++ quietName k ++ (_ , r) ∷ names so ++ laneNames ls
    inL m = ++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ʳ (names so) m)))

    -- What the counts cleared and the lanes thrown leave.
    past : ∀ {k′} (j : h ∋ k′) → All (_≢_ {A = Name h} (k′ , j)) (laneNames ls)
         → _≢_ {A = Name h} (_ , FlatKit.Flat.active fl) (k′ , j) → _≢_ {A = Name h} (_ , FlatKit.Flat.lanes fl) (k′ , j) → look Ht j ≡ look H′ j
    past j a na nl = trans (thrownLanes-off H₂ (length xs) ls j a) (trans (look-store H₁ (FlatKit.Flat.active fl) j na) (look-store H′ (FlatKit.Flat.lanes fl) j nl))

    agS : Alike H′ Ht (names so)
    agS j m = past j (apart-r (names so) P₄ m) (lookupᴬ aA (inS m)) (lookupᴬ aL (inS m))

    agL : Alike H H₂ (laneNames ls)
    agL j m = trans (look-store H₁ (FlatKit.Flat.active fl) j (lookupᴬ aA (inL m)))
                (trans (look-store H′ (FlatKit.Flat.lanes fl) j (lookupᴬ aL (inL m)))
                  (thrown-off H oc k so j (lookupᴬ (apart-l (cutNames oc) P₁ (++⁺ʳ (quietName k) (there (++⁺ʳ (names so) m)))) (here refl))
                                          (apart-l (names so) P₄ m)))

    erf : look Ht (FlatKit.Flat.refill fl) ≡ look H (FlatKit.Flat.refill fl)
    erf = trans (past (FlatKit.Flat.refill fl) (narrow inL aR) (λ ()) (λ ())) (thrown-off H oc k so (FlatKit.Flat.refill fl) (lookupᴬ aR (here refl)) (narrow inS aR))

    er : look Ht r ≡ look H r
    er = trans (past r (narrow (++⁺ʳ (names so)) ar) (λ ()) (λ ())) (thrown-off H oc k so r (λ ()) (narrow ++⁺ˡ ar))
      where ar = apart-r ((_ , r) ∷ []) P₃ (here refl)

    eh : look Ht (Kit.held oc) ≡ look H (Kit.held oc)
    eh = trans (past (Kit.held oc) (narrow (λ m → ++⁺ʳ (quietName k) (there (++⁺ʳ (names so) m))) (apart-r (cutNames oc) P₁ (there (here refl))))
                     (lookupᴬ aA (there (here refl))) (lookupᴬ aL (there (here refl)))) T.eh

    agk : Alike H Ht (quietName k)
    agk j m = trans (past j (narrow (λ m′ → there (++⁺ʳ (names so) m′)) (apart-r (quietName k) P₂ m))
                            (lookupᴬ aA (++⁺ʳ (cutNames oc) (++⁺ˡ m))) (lookupᴬ aL (++⁺ʳ (cutNames oc) (++⁺ˡ m)))) (T.agk j m)

    eA : At.val Ht (FlatKit.Flat.active fl) ≡ 0
    eA = cong lower (trans (thrownLanes-off H₂ (length xs) ls (FlatKit.Flat.active fl) (narrow (λ m → there (there (there (there (inL m))))) (pair-head ps)))
                           (stored-at H₁ (FlatKit.Flat.active fl) (lift 0)))

    eL : At.val Ht (FlatKit.Flat.lanes fl) ≡ []
    eL = cong lower (trans (thrownLanes-off H₂ (length xs) ls (FlatKit.Flat.lanes fl) (narrow inL aL))
                           (trans (look-store H₁ (FlatKit.Flat.active fl) (FlatKit.Flat.lanes fl) (λ ())) (stored-at H′ (FlatKit.Flat.lanes fl) (lift []))))

    module _ (gn : Gone H fl ls) where
      split : xs ++ proj₁ gn ≡ cuts ls
      split = trans (cong (λ z → lower z ++ proj₁ gn) (thrown-off H oc k so (FlatKit.Flat.lanes fl) (lookupᴬ aL (here refl)) (narrow inS aL)))
                    (trans (proj₁ (proj₂ gn)) (cuts-switches H ls))

      gone₂ : All (λ c → At.val H₂ (Kit.live c) ≡ false) (proj₁ gn)
      gone₂ = tabulateᴬ λ {c} m → trans (cong lower (agL (Kit.live c) (cut-in ls (subst (c ∈ᴸ_) (trans (proj₁ (proj₂ gn)) (cuts-switches H ls))
                                                                                         (++⁺ʳ (At.val H (FlatKit.Flat.lanes fl)) m)))))
                                          (lookupᴬ (proj₂ (proj₂ gn)) m)

      dead : All (λ c → At.val Ht (Kit.live c) ≡ false) (cuts ls)
      dead = lanes-dead H₂ xs (proj₁ gn) ls split gone₂

      gone : Gone Ht fl ls
      gone = cuts ls , trans (cong (_++ cuts ls) eL) (sym (cuts-switches Ht ls)) , dead

  -- A connect torn: its source, then its body if attached.
  module ConnTear {h} (H : Heapᴹ h) {Δ A B S c b kb k fd e rp rt} {src : Sub h Δ A} {bd : Sub h (A ∷ Δ) B}
                  (ps : AllPairs _≢_ (names (connectˢ S c b kb k fd rp e rt src bd))) where
    H₁ = torn H src
    H₂ = tornVia H₁ kb bd
    Q₀ = pairs-r (subjectNames S) ps
    Q₁ = pairs-r (cutNames c) Q₀
    Q₂ = pairs-r ((_ , b) ∷ []) Q₁
    Q₃ = pairs-r (quietName kb) Q₂
    Q₄ = pairs-r (quietName k) Q₃
    Ps = proj₁ (pairs-split (names src) Q₄)
    Pb = pairs-r (names src) Q₄

    past : ∀ {k′} (j : h ∋ k′) → All (_≢_ {A = Name h} (k′ , j)) (names src ++ names bd) → look H₂ j ≡ look H j
    past j a = trans (tornVia-off H₁ kb bd j (proj₂ (all-++⁻ (names src) a))) (torn-off H src j (proj₁ (all-++⁻ (names src) a)))

    eh : look H₂ (Kit.held c) ≡ look H (Kit.held c)
    eh = past (Kit.held c) (narrow (λ m → there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) m))) (apart-r (cutNames c) Q₀ (there (here refl))))

    agk : Alike H H₂ (quietName k)
    agk j m = past j (apart-r (quietName k) Q₃ m)

    eb : look H₂ b ≡ look H b
    eb = past b (narrow (λ m → ++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) m)) (apart-r ((_ , b) ∷ []) Q₁ (here refl)))

    agkb : Alike H H₂ (quietName kb)
    agkb j m = past j (narrow (++⁺ʳ (quietName k)) (apart-r (quietName kb) Q₂ m))

    agS : Alike H₁ H₂ (names src)
    agS j m = tornVia-off H₁ kb bd j (apart-r (names src) Q₄ m)

    agB : Alike H H₁ (names bd)
    agB j m = torn-off H src j (apart-l (names src) Q₄ m)

  -- A lane thrown leaves the lanes after it alike.
  laneAlike : ∀ {h} (H : Heapᴹ h) (c : Kit.Cut h) (k : Maybe (Quiet h)) {Δ B} (s : Sub h Δ B) {ls : List (Lane h Δ B)}
            → AllPairs _≢_ (laneNames (lane c k s ∷ ls)) → Alike H (thrown H c k s) (laneNames ls)
  laneAlike H c k s ps j m =
    thrown-off H c k s j (lookupᴬ (apart-l (cutNames c) ps (++⁺ʳ (quietName k) (++⁺ʳ (names s) m))) (here refl))
                         (apart-l (names s) (pairs-r (quietName k) (pairs-r (cutNames c) ps)) m)

  mutual
    holds-torn : ∀ {h} (H : Heapᴹ h) {Δ A} (s : Sub h Δ A) → AllPairs _≢_ (names s)
               → ∀ {E o} → At.Holds H s E o → At.Holds (torn H s) s E o
    holds-torn H (pendingˢ s q)  ps       hs = hs
    holds-torn H (coldˢ s hd ph) ps       hs = Heaps.slot-alike H (store H hd (lift true)) s (look-store H hd s λ ()) hs
    holds-torn H (ofˢ p i xs)    ps       hs = hs
    holds-torn H doneˢ           ps       hs = hs
    holds-torn H (mapˢ f s)      ps       hs = holds-torn H s ps hs
    holds-torn H (scanˢ f r s)   (_ ∷ ps) hs = holds-torn H s ps hs
    holds-torn H (takeWhileˢ i p c k tk s) ps (a , hs) =
      attached-alike c k T.eh T.agk a , via-holds T.H₀ k s (pairs-r (quietName k) (pairs-r (cutNames c) ps)) (Heaps.holds-alike H T.H₀ s T.ag₀ hs)
      where module T = Throw H c k s (λ m → m) ps
    holds-torn H (flatMapˢ op f fl oc k r pl so ls) ps {E} {o} (rf , sl , a , hs , ac , gn , hl) =
      trans (cong lower F.erf) rf
      , Heaps.slot-alike H F.Ht r F.er sl
      , attached-alike oc k F.eh F.agk a
      , Heaps.holds-alike F.H′ F.Ht so F.agS (via-holds F.T.H₀ k so F.PS (Heaps.holds-alike H F.T.H₀ so F.T.ag₀ hs))
      , trans F.eA (sym (count-dead F.Ht ls (F.dead gn)))
      , F.gone gn
      , holdsL-torn F.H₂ (length F.xs) ls F.PL {op = op} {f = f} {E = E} {o = o} {fl = fl} (Heaps.holdsL-alike H F.H₂ ls F.agL {op = op} {f = f} {E = E} {o = o} {fl = fl} hl)
      where module F = FlatTear H {op = op} {f = f} {fl = fl} {oc = oc} {k = k} {r = r} {pl = pl} {so = so} {ls = ls} ps
    holds-torn H (connectˢ S c b kb k fd rp e rt src bd) ps (a , be , st , hs , hb) =
      attached-alike c k C.eh C.agk a , trans (cong lower C.eb) be , stashed-alike kb C.agkb st
      , Heaps.holds-alike C.H₁ C.H₂ src C.agS (holds-torn H src C.Ps hs)
      , via-holds C.H₁ kb bd C.Pb (Heaps.holds-alike H C.H₁ bd C.agB hb)
      where module C = ConnTear H {S = S} {c = c} {b = b} {kb = kb} {k = k} {fd = fd} {e = e} {rp = rp} {rt = rt} {src = src} {bd = bd} ps
    holds-torn H (joinˢ j sk l x st) ps hs = Heaps.slot-alike H (store H l (lift false)) sk (look-store H l sk λ ()) hs
    holds-torn H (deferˢ k s) ps (st , hs) =
      stashed-alike k (λ j m → tornVia-off H k s j (apart-r (quietName k) ps m)) st , via-holds H k s (pairs-r (quietName k) ps) hs

    holdsL-torn : ∀ {h} (H : Heapᴹ h) (n : ℕ) {Δ B} (ls : List (Lane h Δ B)) → AllPairs _≢_ (laneNames ls)
                → ∀ {A : Set} {op f E o fl} → At.HoldsLanes H {A = A} op f E o fl ls → At.HoldsLanes (thrownLanes H n ls) {A = A} op f E o fl ls
    holdsL-torn H zero    ls ps hl = hl
    holdsL-torn H (suc n) []  ps hl = hl
    holdsL-torn {h} H (suc n) (lane c k s ∷ ls) ps {op = op} {f} {E} {o} {fl} (a , hs , hl) =
      attached-alike c k (trans (past (Kit.held c) (narrow (λ m → ++⁺ʳ (quietName k) (++⁺ʳ (names s) m)) (apart-r (cutNames c) ps (there (here refl))))) T.eh)
                         (λ j m → trans (past j (narrow (++⁺ʳ (names s)) (apart-r (quietName k) (pairs-r (cutNames c) ps) m))) (T.agk j m)) a
      , Heaps.holds-alike H₁ (thrownLanes H₁ n ls) s (λ j m → past j (apart-r (names s) P m))
                          (via-holds T.H₀ k s (proj₁ (pairs-split (names s) P)) (Heaps.holds-alike H T.H₀ s T.ag₀ hs))
      , holdsL-torn H₁ n ls (pairs-r (names s) P) {op = op} {f = f} {E = E} {o = o} {fl = fl} (Heaps.holdsL-alike H H₁ ls (laneAlike H c k s {ls} ps) {op = op} {f = f} {E = E} {o = o} {fl = fl} hl)
      where
        module T = Throw H c k s (λ m → ++⁺ˡ m) ps
        H₁ = thrown H c k s
        P = pairs-r (quietName k) (pairs-r (cutNames c) ps)
        past : ∀ {k′} (j : h ∋ k′) → All (_≢_ {A = Name h} (k′ , j)) (laneNames ls) → look (thrownLanes H₁ n ls) j ≡ look H₁ j
        past j a = thrownLanes-off H₁ n ls j a

    via-holds : ∀ {h} (H : Heapᴹ h) (k : Maybe (Quiet h)) {Δ A} (s : Sub h Δ A) → AllPairs _≢_ (names s)
              → ∀ {E o} → At.Holds H s E o → At.Holds (tornVia H k s) s E o
    via-holds H nothing  s ps hs = hs
    via-holds H (just _) s ps hs = holds-torn H s ps hs

  mutual
    -- The lanes `torn` leaves unthrown are cut already, and their gates
    -- give their spent.
    spent-torn : ∀ {h} (H : Heapᴹ h) {Δ A} (s : Sub h Δ A) → AllPairs _≢_ (names s)
               → ∀ {E o} → At.Holds H s E o → At.Gated H s → At.Spent (torn H s) s
    spent-torn H (pendingˢ s q)  ps       hs g = lift tt
    spent-torn H (coldˢ s hd ph) ps       hs g = lift (cong lower (stored-at H hd (lift true)))
    spent-torn H (ofˢ p i xs)    ps       hs g = lift tt
    spent-torn H doneˢ           ps       hs g = lift tt
    spent-torn H (mapˢ f s)      ps       hs g = spent-torn H s ps hs g
    spent-torn H (scanˢ f r s)   (_ ∷ ps) hs g = spent-torn H s ps hs g
    spent-torn H (takeWhileˢ i p c k tk s) ps (_ , hs) (_ , g) =
      via-cut T.H₀ k s (pairs-r (quietName k) (pairs-r (cutNames c) ps)) (Heaps.holds-alike H T.H₀ s T.ag₀ hs) (Heaps.gated-alike H T.H₀ s T.ag₀ g)
      where module T = Throw H c k s (λ m → m) ps
    spent-torn H (flatMapˢ op f fl oc k r pl so ls) ps {E} {o} (_ , _ , _ , hs , _ , gn , hl) (g₁ , g₂) =
      Heaps.cut-alike F.H′ F.Ht k so F.agS (via-cut F.T.H₀ k so F.PS (Heaps.holds-alike H F.T.H₀ so F.T.ag₀ hs) (Heaps.gated-alike H F.T.H₀ so F.T.ag₀ g₁))
      , spentL-torn F.H₂ F.xs (proj₁ gn) ls (F.split gn) (F.gone₂ gn) F.PL
                    (tabulateᴬ (listed-apart ls F.PL (At.val H (FlatKit.Flat.lanes fl)) (trans (proj₁ (proj₂ gn)) (cuts-switches H ls)))) {op = op} {f = f} {E = E} {o = o} {fl = fl}
                    (Heaps.holdsL-alike H F.H₂ ls F.agL {op = op} {f = f} {E = E} {o = o} {fl = fl} hl) (Heaps.gatedL-alike H F.H₂ ls F.agL g₂)
      where module F = FlatTear H {op = op} {f = f} {fl = fl} {oc = oc} {k = k} {r = r} {pl = pl} {so = so} {ls = ls} ps
    spent-torn H (connectˢ S c b kb k fd rp e rt src bd) ps (_ , _ , _ , hs , hb) (_ , g₂ , g₃) =
      Heaps.cut-alike C.H₁ C.H₂ k src C.agS (cut-of {H = C.H₁} k {s = src} (spent-torn H src C.Ps hs g₂))
      , via-cut C.H₁ kb bd C.Pb (Heaps.holds-alike H C.H₁ bd C.agB hb) (Heaps.gated-alike H C.H₁ bd C.agB g₃)
      where module C = ConnTear H {S = S} {c = c} {b = b} {kb = kb} {k = k} {fd = fd} {e = e} {rp = rp} {rt = rt} {src = src} {bd = bd} ps
    spent-torn H (joinˢ j sk l x st) ps hs       g = lift tt
    spent-torn H (deferˢ k s)        ps (_ , hs) g = via-cut H k s (pairs-r (quietName k) ps) hs g

    spentL-torn : ∀ {h} (H : Heapᴹ h) (xs gone : List (Kit.Cut h)) {Δ B} (ls : List (Lane h Δ B)) → xs ++ gone ≡ cuts ls
                → All (λ c → At.val H (Kit.live c) ≡ false) gone → AllPairs _≢_ (laneNames ls) → ∀ {X} → All (λ c → c ∈ᴸ X → ⊥) gone
                → ∀ {A : Set} {op f E o fl} → At.HoldsLanes H {A = A} op f E o fl ls → At.GatedLanes H X ls → At.SpentLanes (thrownLanes H (length xs) ls) ls
    spentL-torn H []       gone ls eq ga ps {X} nx hl gl =
      spentL-dead H X ls (subst (All (λ c → At.val H (Kit.live c) ≡ false)) eq ga) (subst (All (λ c → c ∈ᴸ X → ⊥)) eq nx) gl
    spentL-torn H (x ∷ xs) gone [] () ga ps nx hl gl
    spentL-torn H (x ∷ xs) gone (lane c k s ∷ ls) eq ga ps nx {op = op} {f} {E} {o} {fl} (_ , hs , hl) (_ , g , gl) =
      Heaps.cut-alike H₁ (thrownLanes H₁ (length xs) ls) k s (λ j m → thrownLanes-off H₁ (length xs) ls j (apart-r (names s) P m))
        (via-cut T.H₀ k s (proj₁ (pairs-split (names s) P)) (Heaps.holds-alike H T.H₀ s T.ag₀ hs) (Heaps.gated-alike H T.H₀ s T.ag₀ g))
      , spentL-torn H₁ xs gone ls (∷-injectiveʳ eq) (mapᴬ (λ {c′} e → lowers (thrown-lowers H c k s) (Kit.live c′) e) ga) (pairs-r (names s) P) nx {op = op} {f = f} {E = E} {o = o} {fl = fl}
                    (Heaps.holdsL-alike H H₁ ls (laneAlike H c k s {ls} ps) {op = op} {f = f} {E = E} {o = o} {fl = fl} hl)
                    (Heaps.gatedL-alike H H₁ ls (laneAlike H c k s {ls} ps) gl)
      where
        module T = Throw H c k s (λ m → ++⁺ˡ m) ps
        H₁ = thrown H c k s
        P = pairs-r (quietName k) (pairs-r (cutNames c) ps)

    via-cut : ∀ {h} (H : Heapᴹ h) (k : Maybe (Quiet h)) {Δ A} (s : Sub h Δ A) → AllPairs _≢_ (names s)
            → ∀ {E o} → At.Holds H s E o → At.Gated H s → At.Cut↓ (tornVia H k s) k s
    via-cut H nothing  s ps hs g = lift tt
    via-cut H (just _) s ps hs g = spent-torn H s ps hs g

  mutual
    gated-torn : ∀ {h} (H : Heapᴹ h) {Δ A} (s : Sub h Δ A) → AllPairs _≢_ (names s)
               → ∀ {E o} → At.Holds H s E o → At.Gated H s → At.Gated (torn H s) s
    gated-torn H (pendingˢ s q)  ps       hs g = g
    gated-torn H (coldˢ s hd ph) ps       hs g = lift (λ e → ⊥-elim (false≢true (trans (sym e) (cong lower (stored-at H hd (lift true))))))
    gated-torn H (ofˢ p i xs)    ps       hs g = g
    gated-torn H doneˢ           ps       hs g = g
    gated-torn H (mapˢ f s)      ps       hs g = gated-torn H s ps hs g
    gated-torn H (scanˢ f r s)   (_ ∷ ps) hs g = gated-torn H s ps hs g
    gated-torn H (takeWhileˢ i p c k tk s) ps (a , hs) (g₁ , g) =
      (λ _ → spent-torn H (takeWhileˢ i p c k tk s) ps (a , hs) (g₁ , g))
      , via-gated T.H₀ k s (pairs-r (quietName k) (pairs-r (cutNames c) ps)) (Heaps.holds-alike H T.H₀ s T.ag₀ hs) (Heaps.gated-alike H T.H₀ s T.ag₀ g)
      where module T = Throw H c k s (λ m → m) ps
    gated-torn H (flatMapˢ op f fl oc k r pl so ls) ps {E} {o} hz@(_ , _ , _ , hs , _ , _ , hl) gz@(g₁ , g₂) =
      Heaps.gated-alike F.H′ F.Ht so F.agS (via-gated F.T.H₀ k so F.PS (Heaps.holds-alike H F.T.H₀ so F.T.ag₀ hs) (Heaps.gated-alike H F.T.H₀ so F.T.ag₀ g₁))
      , gatedL-spent ls (proj₂ (spent-torn H (flatMapˢ op f fl oc k r pl so ls) ps {E} {o} hz gz))
          (gatedL-torn F.H₂ (length F.xs) ls F.PL {op = op} {f = f} {E = E} {o = o} {fl = fl} (Heaps.holdsL-alike H F.H₂ ls F.agL {op = op} {f = f} {E = E} {o = o} {fl = fl} hl) (Heaps.gatedL-alike H F.H₂ ls F.agL g₂))
      where module F = FlatTear H {op = op} {f = f} {fl = fl} {oc = oc} {k = k} {r = r} {pl = pl} {so = so} {ls = ls} ps
    gated-torn H (connectˢ S c b kb k fd rp e rt src bd) ps {E} {o} hs@(_ , _ , _ , hsrc , hb) g@(_ , g₂ , g₃) =
      (λ _ → proj₁ (spent-torn H (connectˢ S c b kb k fd rp e rt src bd) ps {E} {o} hs g))
      , Heaps.gated-alike C.H₁ C.H₂ src C.agS (gated-torn H src C.Ps hsrc g₂)
      , via-gated C.H₁ kb bd C.Pb (Heaps.holds-alike H C.H₁ bd C.agB hb) (Heaps.gated-alike H C.H₁ bd C.agB g₃)
      where module C = ConnTear H {S = S} {c = c} {b = b} {kb = kb} {k = k} {fd = fd} {e = e} {rp = rp} {rt = rt} {src = src} {bd = bd} ps
    gated-torn H (joinˢ j sk l x st) ps hs       g = g
    gated-torn H (deferˢ k s)        ps (_ , hs) g = via-gated H k s (pairs-r (quietName k) ps) hs g

    gatedL-torn : ∀ {h} (H : Heapᴹ h) (n : ℕ) {Δ B} (ls : List (Lane h Δ B)) → AllPairs _≢_ (laneNames ls)
                → ∀ {A : Set} {op f E o fl} {X} → At.HoldsLanes H {A = A} op f E o fl ls → At.GatedLanes H X ls → At.GatedLanes (thrownLanes H n ls) X ls
    gatedL-torn H zero    ls ps hl gl = gl
    gatedL-torn H (suc n) []  ps hl gl = gl
    gatedL-torn H (suc n) (lane c k s ∷ ls) ps {op = op} {f} {E} {o} {fl} (_ , hs , hl) (_ , g , gl) =
      (λ _ → inj₂ (Heaps.cut-alike H₁ Ht k s agt (via-cut T.H₀ k s Ps hs₀ g₀)))
      , Heaps.gated-alike H₁ Ht s agt (via-gated T.H₀ k s Ps hs₀ g₀)
      , gatedL-torn H₁ n ls (pairs-r (names s) P) {op = op} {f = f} {E = E} {o = o} {fl = fl} (Heaps.holdsL-alike H H₁ ls (laneAlike H c k s {ls} ps) {op = op} {f = f} {E = E} {o = o} {fl = fl} hl)
                    (Heaps.gatedL-alike H H₁ ls (laneAlike H c k s {ls} ps) gl)
      where
        module T = Throw H c k s (λ m → ++⁺ˡ m) ps
        H₁ = thrown H c k s
        Ht = thrownLanes H₁ n ls
        P = pairs-r (quietName k) (pairs-r (cutNames c) ps)
        Ps = proj₁ (pairs-split (names s) P)
        hs₀ = Heaps.holds-alike H T.H₀ s T.ag₀ hs
        g₀ = Heaps.gated-alike H T.H₀ s T.ag₀ g
        agt : Alike H₁ Ht (names s)
        agt j m = thrownLanes-off H₁ n ls j (apart-r (names s) P m)

    via-gated : ∀ {h} (H : Heapᴹ h) (k : Maybe (Quiet h)) {Δ A} (s : Sub h Δ A) → AllPairs _≢_ (names s)
              → ∀ {E o} → At.Holds H s E o → At.Gated H s → At.Gated (tornVia H k s) s
    via-gated H nothing  s ps hs g = g
    via-gated H (just _) s ps hs g = gated-torn H s ps hs g

  -- A thrown switch moves only the switch and what it holds.
  thrown-at : ∀ {h} (H : Heapᴹ h) (c : Kit.Cut h) (k : Maybe (Quiet h)) {Δ A} (s : Sub h Δ A) {ns}
            → (_ , Kit.live c) ∈ᴸ ns → (∀ {y} → y ∈ᴸ names s → y ∈ᴸ ns) → Off H (thrown H c k s) ns
  thrown-at H c k s ml sub j a = thrown-off H c k s j (lookupᴬ a ml) (narrow sub a)

  takeOff : ∀ {h} (H : Heapᴹ h) (c : Kit.Cut h) (k : Maybe (Quiet h)) {Δ A} (s : Sub h Δ A) {i q tk}
          → Off H (thrown H c k s) (names (takeWhileˢ i q c k tk s))
  takeOff H c k s = thrown-at H c k s (here refl) (λ m → ++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) m))

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
  site-holds H ps (takeSite {i = i} {q} {c} {k} {s} π) =
    Heaps.holds-same H (thrown H c k s) π ps (takeOff H c k s {i = i} {q = q} {tk = taken}) (λ {E} {o} → holds-torn H (takeWhileˢ i q c k taken s) (fresh-path π ps) {E} {o})
  site-holds H ps (bodySite {S = S} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {s} {bd} π) = Heaps.holds-same H (thrown H c k s) π ps B.off (λ {E} {o} → B.holds {E} {o})
    where module B = BodySite H {S = S} {c = c} {b = b} {kb = kb} {k = k} {fd = fd} {e = e} {rp = rp} {rt = rt} {s = s} {bd = bd} (fresh-path π ps)

  site-gated : ∀ {h} (H : Heapᴹ h) {t : Sub h [] R} → AllPairs _≢_ (names t) → (z : Site t)
             → At.Holds H t []ᴬ rootObs → At.Gated H t → At.Gated (siteHeap H z) t
  site-gated H ps (takeSite {i = i} {q} {c} {k} {s} π) hs g with holds-at π hs | gated-at π g
  ... | _ , _ , hu | gu =
    Heaps.gated-same H (thrown H c k s) π ps (takeOff H c k s {i = i} {q = q} {tk = taken})
      (λ _ → gated-torn H (takeWhileˢ i q c k taken s) (fresh-path π ps) hu gu) (λ _ → spent-torn H (takeWhileˢ i q c k taken s) (fresh-path π ps) hu gu) g
  site-gated H ps (bodySite {S = S} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {s} {bd} π) hs g with holds-at π hs | gated-at π g
  ... | _ , _ , (_ , _ , _ , hu , _) | (_ , gu , _) =
    Heaps.gated-same H (thrown H c k s) π ps B.off (B.gated hu gu) (B.spent hu gu) g
    where module B = BodySite H {S = S} {c = c} {b = b} {kb = kb} {k = k} {fd = fd} {e = e} {rp = rp} {rt = rt} {s = s} {bd = bd} (fresh-path π ps)
