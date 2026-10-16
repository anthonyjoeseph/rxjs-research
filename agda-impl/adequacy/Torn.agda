{-# OPTIONS --guardedness #-}

-- TORN: the heap a subscription's unsubscribe leaves, and what it leaves
-- alone.  A teardown writes only names the torn subscription holds, and
-- a subscription's part reads only its own names, so with the names all
-- distinct (`Books.fresh`) the rest of the tree reads the same heap.
module adequacy.Torn where

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (tabulate to tabulateᴬ; lookup to lookupᴬ)
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

module Tearing (R : Set) where
  open Heap using (World; Kind; Quiet; _∋_; same) renaming (here to hereʰ; there to thereʰ)
  open Shared Timeline (Out R) using (Heapᴹ; store; look; get; put; stored)
  open Strongly R
  open Moving R using (pairs-split; pairs-r)
  open Run (Pureᴾ R) using (module Kit; module FlatKit)

  ----------------------------------------------------------------------
  -- The heap an unsubscribe leaves

  -- Its colds spent, its switches thrown, its joiners silenced, below a
  -- switch only once attached; a flatMap's lanes cut as `killAllᶜ` reads
  -- them, the first so many of the lanes it holds.
  mutual
    torn : ∀ {h} → Heapᴹ h → ∀ {Δ A} → Sub h Δ A → Heapᴹ h
    torn H (coldˢ s hd ph)                         = store H hd (lift true)
    torn H (mapˢ f s)                              = torn H s
    torn H (scanˢ f r s)                           = torn H s
    torn H (takeWhileˢ i p c k tk s)               = thrown H c k s
    torn H (flatMapˢ op f fl oc k r pl so ls)      = let H′ = thrown H oc k so in
      thrownLanes (store (store H′ (FlatKit.Flat.lanes fl) (lift [])) (FlatKit.Flat.active fl) (lift 0))
                  (length (lower (look H′ (FlatKit.Flat.lanes fl)))) ls
    torn H (connectˢ S c b kb k fd rp e rt src bd) = tornVia (torn H src) kb bd
    torn H (joinˢ j sk l x st)                     = store H l (lift false)
    torn H (deferˢ k s)                            = tornVia H k s
    torn H _                                       = H

    tornVia : ∀ {h} → Heapᴹ h → Maybe (Quiet h) → ∀ {Δ A} → Sub h Δ A → Heapᴹ h
    tornVia H nothing  s = H
    tornVia H (just _) s = torn H s

    -- A switch thrown, and what it holds unsubscribed.
    thrown : ∀ {h} → Heapᴹ h → Kit.Cut h → Maybe (Quiet h) → ∀ {Δ A} → Sub h Δ A → Heapᴹ h
    thrown H c k s = tornVia (store H (Kit.live c) (lift false)) k s

    thrownLanes : ∀ {h} → Heapᴹ h → ℕ → ∀ {Δ B} → List (Lane h Δ B) → Heapᴹ h
    thrownLanes H zero    ls                = H
    thrownLanes H (suc n) []                = H
    thrownLanes H (suc n) (lane c k s ∷ ls) = thrownLanes (thrown H c k s) n ls

  -- Where a cut runs from the agenda's head: a takeWhile already taken,
  -- or a connect whose body has ended.  Each holds no part, and its code
  -- throws its switch.
  data Site {h} (t : Sub h [] R) : Set₁ where
    takeSite : ∀ {Δ A i q c k} {s : Sub h Δ A} → Path t (takeWhileˢ i q c k taken s) → Site t
    bodySite : ∀ {Δ A B S c b kb k fd e rp rt} {s : Sub h Δ A} {bd : Sub h (A ∷ Δ) B}
             → Path t (connectˢ S c b kb k fd rp e rt s bd) → Site t

  siteCall : ∀ {h} {t : Sub h [] R} → Site t → Call t
  siteCall (takeSite π) = take2C π
  siteCall (bodySite π) = bodyC π

  -- The heap its cut leaves.
  siteHeap : ∀ {h} {t : Sub h [] R} → Heapᴹ h → Site t → Heapᴹ h
  siteHeap H (takeSite {c = c} {k} {s} π)         = thrown H c k s
  siteHeap H (bodySite {c = c} {k = k} {s = s} π) = thrown H c k s

  ----------------------------------------------------------------------
  -- A store reads back unchanged everywhere it did not write

  ≢-flip : ∀ {a} {X : Set a} {x y : X} → x ≢ y → y ≢ x
  ≢-flip ne e = ne (sym e)

  there-≡ : ∀ {w j k k′} {i : w ∋ k} {i′ : w ∋ k′} → _≡_ {A = Name w} (k , i) (k′ , i′)
          → _≡_ {A = Name (j ∷ w)} (k , thereʰ i) (k′ , thereʰ i′)
  there-≡ refl = refl

  get-put : ∀ {ℓ} {P : Kind → Set ℓ} {w k k′} (xs : All P w) (i : w ∋ k) (j : w ∋ k′) {y : P k}
          → _≢_ {A = Name w} (k , i) (k′ , j) → get (put xs i y) j ≡ get xs j
  get-put (x ∷ xs) hereʰ      hereʰ      ne = ⊥-elim (ne refl)
  get-put (x ∷ xs) hereʰ      (thereʰ j) ne = refl
  get-put (x ∷ xs) (thereʰ i) hereʰ      ne = refl
  get-put (x ∷ xs) (thereʰ i) (thereʰ j) ne = get-put xs i j (λ e → ne (there-≡ e))

  look-store : ∀ {h k k′} (H : Heapᴹ h) (i : h ∋ k) (j : h ∋ k′) {x} → _≢_ {A = Name h} (k , i) (k′ , j)
             → look (store H i x) j ≡ look H j
  look-store H i j {x} ne rewrite get-put H i j {y = stored x same} ne = refl

  -- A heap moved only at the names given: alike at every other.
  Off : ∀ {h} → Heapᴹ h → Heapᴹ h → List (Name h) → Set₁
  Off {h} H H′ ns = ∀ {k} (j : h ∋ k) → All (_≢_ {A = Name h} (k , j)) ns → look H′ j ≡ look H j

  -- Two heaps alike at the names given.
  Alike : ∀ {h} → Heapᴹ h → Heapᴹ h → List (Name h) → Set₁
  Alike {h} H H′ ns = ∀ {k} (j : h ∋ k) → (k , j) ∈ᴸ ns → look H′ j ≡ look H j

  ----------------------------------------------------------------------
  -- An unsubscribe writes only names its subscription holds

  mutual
    torn-off : ∀ {h} (H : Heapᴹ h) {Δ A} (u : Sub h Δ A) → Off H (torn H u) (names u)
    torn-off H (pendingˢ s q) j a                 = refl
    torn-off H (coldˢ s hd ph) j (_ ∷ nh ∷ [])    = look-store H hd j (≢-flip nh)
    torn-off H (ofˢ p i xs) j a                   = refl
    torn-off H doneˢ j a                          = refl
    torn-off H (mapˢ f s) j a                     = torn-off H s j a
    torn-off H (scanˢ f r s) j (_ ∷ a)            = torn-off H s j a
    torn-off H (takeWhileˢ i p c k tk s) j a with all-++⁻ (cutNames c) a
    ... | nl ∷ _ , b                              = thrown-off H c k s j nl (proj₂ (all-++⁻ (quietName k) b))
    torn-off H (flatMapˢ op f fl oc k r pl so ls) j a with all-++⁻ (flatNames fl) a
    ... | na ∷ _ ∷ _ ∷ nl ∷ _ ∷ [] , b with all-++⁻ (cutNames oc) b
    ... | nc ∷ _ , b₂ with all-++⁻ (quietName k) b₂
    ... | _ , _ ∷ b₃ with all-++⁻ (names so) b₃
    ... | aso , als =
      let H′ = thrown H oc k so
          H₁ = store H′ (FlatKit.Flat.lanes fl) (lift [])
          H₂ = store H₁ (FlatKit.Flat.active fl) (lift 0) in
      trans (thrownLanes-off H₂ (length (lower (look H′ (FlatKit.Flat.lanes fl)))) ls j als)
        (trans (look-store H₁ (FlatKit.Flat.active fl) j (≢-flip na))
          (trans (look-store H′ (FlatKit.Flat.lanes fl) j (≢-flip nl)) (thrown-off H oc k so j nc aso)))
    torn-off H (connectˢ S c b kb k fd rp e rt src bd) j a with all-++⁻ (subjectNames S) a
    ... | _ , b₁ with all-++⁻ (cutNames c) b₁
    ... | _ , _ ∷ b₂ with all-++⁻ (quietName kb) b₂
    ... | _ , b₃ with all-++⁻ (quietName k) b₃
    ... | _ , b₄ with all-++⁻ (names src) b₄
    ... | asrc , abd                              = trans (tornVia-off (torn H src) kb bd j abd) (torn-off H src j asrc)
    torn-off H (joinˢ x sk l y st) j (_ ∷ nl ∷ []) = look-store H l j (≢-flip nl)
    torn-off H (deferˢ k s) j a                   = tornVia-off H k s j (proj₂ (all-++⁻ (quietName k) a))

    tornVia-off : ∀ {h} (H : Heapᴹ h) (k : Maybe (Quiet h)) {Δ A} (s : Sub h Δ A) → Off H (tornVia H k s) (names s)
    tornVia-off H nothing  s j a = refl
    tornVia-off H (just _) s j a = torn-off H s j a

    thrown-off : ∀ {h} (H : Heapᴹ h) (c : Kit.Cut h) (k : Maybe (Quiet h)) {Δ A} (s : Sub h Δ A) {k′} (j : h ∋ k′)
               → _≢_ {A = Name h} (k′ , j) (_ , Kit.live c) → All (_≢_ {A = Name h} (k′ , j)) (names s)
               → look (thrown H c k s) j ≡ look H j
    thrown-off H c k s j nl a = trans (tornVia-off (store H (Kit.live c) (lift false)) k s j a) (look-store H (Kit.live c) j (≢-flip nl))

    thrownLanes-off : ∀ {h} (H : Heapᴹ h) (n : ℕ) {Δ B} (ls : List (Lane h Δ B)) → Off H (thrownLanes H n ls) (laneNames ls)
    thrownLanes-off H zero    ls                j a = refl
    thrownLanes-off H (suc n) []                j a = refl
    thrownLanes-off H (suc n) (lane c k s ∷ ls) j a with all-++⁻ (cutNames c) a
    ... | nc ∷ _ , b with all-++⁻ (quietName k) b
    ... | _ , b₂ with all-++⁻ (names s) b₂
    ... | as , al = trans (thrownLanes-off (thrown H c k s) n ls j al) (thrown-off H c k s j nc as)

  ----------------------------------------------------------------------
  -- A part reads only its own names

  mutual
    part-alike : ∀ {h} (H H′ : Heapᴹ h) {Δ A} (u : Sub h Δ A) → Alike H H′ (names u) → At.part H′ u ≡ At.part H u
    part-alike H H′ (pendingˢ s q) ag = refl
    part-alike H H′ (coldˢ s hd ph) ag rewrite ag hd (there (here refl)) = refl
    part-alike H H′ (ofˢ p i xs) ag = refl
    part-alike H H′ doneˢ ag = refl
    part-alike H H′ (mapˢ f s) ag rewrite part-alike H H′ s ag = refl
    part-alike H H′ (scanˢ f r s) ag rewrite ag r (here refl) | part-alike H H′ s (λ j m → ag j (there m)) = refl
    part-alike H H′ (takeWhileˢ i p c k tk s) ag
      rewrite ag (Kit.live c) (here refl) | part-alike H H′ s (λ j m → ag j (++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) m))) = refl
    part-alike H H′ (flatMapˢ op f fl oc k r pl so ls) ag
      rewrite ag (FlatKit.Flat.queue fl) (++⁺ˡ {xs = flatNames fl} (there (there (here refl))))
            | part-alike H H′ so (λ j m → ag j (++⁺ʳ (flatNames fl) (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ˡ m))))))
            | partLanes-alike H H′ ls (λ j m → ag j (++⁺ʳ (flatNames fl) (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ʳ (names so) m)))))) = refl
    part-alike H H′ (connectˢ S c b kb k fd rp e rt src bd) ag
      rewrite part-alike H H′ src (λ j m → ag j (++⁺ʳ (subjectNames S) (++⁺ʳ (cutNames c) (there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ˡ m)))))))
            | part-alike H H′ bd (λ j m → ag j (++⁺ʳ (subjectNames S) (++⁺ʳ (cutNames c) (there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ʳ (names src) m))))))) = refl
    part-alike H H′ (joinˢ x sk l y st) ag rewrite ag l (there (here refl)) = refl
    part-alike H H′ (deferˢ k s) ag = part-alike H H′ s (λ j m → ag j (++⁺ʳ (quietName k) m))

    partLanes-alike : ∀ {h} (H H′ : Heapᴹ h) {Δ B} (ls : List (Lane h Δ B)) → Alike H H′ (laneNames ls) → At.partLanes H′ ls ≡ At.partLanes H ls
    partLanes-alike H H′ [] ag = refl
    partLanes-alike H H′ (lane c k s ∷ ls) ag
      rewrite ag (Kit.live c) (here refl)
            | part-alike H H′ s (λ j m → ag j (++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) (++⁺ˡ m))))
            | partLanes-alike H H′ ls (λ j m → ag j (++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) (++⁺ʳ (names s) m)))) = refl

  ----------------------------------------------------------------------
  -- Names apart

  mutual
    names-path : ∀ {h Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} → Path t u → ∀ {n} → n ∈ᴸ names u → n ∈ᴸ names t
    names-path here m = m
    names-path (in-map π) m = names-path π m
    names-path (in-scan π) m = there (names-path π m)
    names-path (in-take {c = c} {k} π) m = ++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) (names-path π m))
    names-path (in-outer {fl = fl} {oc} {k} π) m =
      ++⁺ʳ (flatNames fl) (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ˡ (names-path π m)))))
    names-path (in-lanes {fl = fl} {oc} {k} {t = so} π) m =
      ++⁺ʳ (flatNames fl) (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ʳ (names so) (lanes-path π m)))))
    names-path (in-source {S = S} {c} {kb = kb} {k} π) m =
      ++⁺ʳ (subjectNames S) (++⁺ʳ (cutNames c) (there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ˡ (names-path π m))))))
    names-path (in-body {S = S} {c} {kb = kb} {k} {t = src} π) m =
      ++⁺ʳ (subjectNames S) (++⁺ʳ (cutNames c) (there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ʳ (names src) (names-path π m))))))
    names-path (in-defer {k = k} π) m = ++⁺ʳ (quietName k) (names-path π m)

    lanes-path : ∀ {h Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} → PathLanes ls u → ∀ {n} → n ∈ᴸ names u → n ∈ᴸ laneNames ls
    lanes-path (this-lane {c = c} {k} π) m = ++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) (++⁺ˡ (names-path π m)))
    lanes-path (next-lane {l = lane c k s} π) m = ++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) (++⁺ʳ (names s) (lanes-path π m)))

  -- A name left of a join apart from every name right of it, and back.
  apart-r : ∀ {a} {X : Set a} xs {ys : List X} {n} → AllPairs _≢_ (xs ++ ys) → n ∈ᴸ xs → All (n ≢_) ys
  apart-r xs ps m = lookupᴬ (proj₂ (proj₂ (pairs-split xs ps))) m

  apart-l : ∀ {a} {X : Set a} xs {ys : List X} {n} → AllPairs _≢_ (xs ++ ys) → n ∈ᴸ ys → All (n ≢_) xs
  apart-l xs ps m = tabulateᴬ λ x → ≢-flip (lookupᴬ (lookupᴬ (proj₂ (proj₂ (pairs-split xs ps))) x) m)

  narrow : ∀ {a p} {X : Set a} {P : X → Set p} {us vs : List X} → (∀ {m} → m ∈ᴸ us → m ∈ᴸ vs) → All P vs → All P us
  narrow sub a = tabulateᴬ λ m → lookupᴬ a (sub m)

  -- Below a path, the names still distinct.
  mutual
    fresh-path : ∀ {h Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} → Path t u → AllPairs _≢_ (names t) → AllPairs _≢_ (names u)
    fresh-path here ps = ps
    fresh-path (in-map π) ps = fresh-path π ps
    fresh-path (in-scan π) (_ ∷ ps) = fresh-path π ps
    fresh-path (in-take {c = c} {k} π) ps = fresh-path π (pairs-r (quietName k) (pairs-r (cutNames c) ps))
    fresh-path (in-outer {fl = fl} {oc} {k} {r} {t = so} π) ps =
      fresh-path π (proj₁ (pairs-split (names so) (pairs-r ((_ , r) ∷ []) (pairs-r (quietName k) (pairs-r (cutNames oc) (pairs-r (flatNames fl) ps))))))
    fresh-path (in-lanes {fl = fl} {oc} {k} {r} {t = so} π) ps =
      fresh-lanes π (pairs-r (names so) (pairs-r ((_ , r) ∷ []) (pairs-r (quietName k) (pairs-r (cutNames oc) (pairs-r (flatNames fl) ps)))))
    fresh-path (in-source {S = S} {c} {b} {kb} {k} {t = src} π) ps =
      fresh-path π (proj₁ (pairs-split (names src)
        (pairs-r (quietName k) (pairs-r (quietName kb) (pairs-r ((_ , b) ∷ []) (pairs-r (cutNames c) (pairs-r (subjectNames S) ps)))))))
    fresh-path (in-body {S = S} {c} {b} {kb} {k} {t = src} π) ps =
      fresh-path π (pairs-r (names src)
        (pairs-r (quietName k) (pairs-r (quietName kb) (pairs-r ((_ , b) ∷ []) (pairs-r (cutNames c) (pairs-r (subjectNames S) ps))))))
    fresh-path (in-defer {k = k} π) ps = fresh-path π (pairs-r (quietName k) ps)

    fresh-lanes : ∀ {h Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} → PathLanes ls u → AllPairs _≢_ (laneNames ls) → AllPairs _≢_ (names u)
    fresh-lanes (this-lane {c = c} {k} {t = s} π) ps = fresh-path π (proj₁ (pairs-split (names s) (pairs-r (quietName k) (pairs-r (cutNames c) ps))))
    fresh-lanes (next-lane {l = lane c k s} π) ps = fresh-lanes π (pairs-r (names s) (pairs-r (quietName k) (pairs-r (cutNames c) ps)))

  ----------------------------------------------------------------------
  -- A heap moved only within a node: the tree above reads it alike

  mutual
    part-path : ∀ {h} (H H′ : Heapᴹ h) {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) → AllPairs _≢_ (names t)
              → Off H H′ (names u) → At.part H′ u ≡ At.part H u → At.part H′ t ≡ At.part H t
    part-path H H′ here ps off eq = eq
    part-path H H′ (in-map π) ps off eq rewrite part-path H H′ π ps off eq = refl
    part-path H H′ (in-scan {r = r} π) (a ∷ ps) off eq rewrite off r (narrow (names-path π) a) | part-path H H′ π ps off eq = refl
    part-path H H′ (in-take {c = c} {k} {t = s} π) ps off eq
      rewrite off (Kit.live c) (narrow (λ m → ++⁺ʳ (quietName k) (names-path π m)) (apart-r (cutNames c) ps (here refl)))
            | part-path H H′ π (pairs-r (quietName k) (pairs-r (cutNames c) ps)) off eq = refl
    part-path H H′ (in-outer {fl = fl} {oc} {k} {r} {t = so} {ls} π) ps off eq
      rewrite off (FlatKit.Flat.queue fl)
                (narrow (λ m → ++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ˡ (names-path π m)))))
                        (apart-r (flatNames fl) ps (there (there (here refl)))))
            | part-path H H′ π (proj₁ (pairs-split (names so) (pairs-r ((_ , r) ∷ []) (pairs-r (quietName k) (pairs-r (cutNames oc) (pairs-r (flatNames fl) ps)))))) off eq
            | partLanes-alike H H′ ls (λ j m → off j (narrow (names-path π) (apart-l (names so) (pairs-r ((_ , r) ∷ []) (pairs-r (quietName k) (pairs-r (cutNames oc) (pairs-r (flatNames fl) ps)))) m))) = refl
    part-path H H′ (in-lanes {fl = fl} {oc} {k} {r} {t = so} {ls} π) ps off eq
      rewrite off (FlatKit.Flat.queue fl)
                (narrow (λ m → ++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ʳ (names so) (lanes-path π m)))))
                        (apart-r (flatNames fl) ps (there (there (here refl)))))
            | part-alike H H′ so (λ j m → off j (narrow (lanes-path π) (apart-r (names so) (pairs-r ((_ , r) ∷ []) (pairs-r (quietName k) (pairs-r (cutNames oc) (pairs-r (flatNames fl) ps)))) m)))
            | partLanes-path H H′ π (pairs-r (names so) (pairs-r ((_ , r) ∷ []) (pairs-r (quietName k) (pairs-r (cutNames oc) (pairs-r (flatNames fl) ps))))) off eq = refl
    part-path H H′ (in-source {S = S} {c} {b} {kb} {k} {t = src} {bd} π) ps off eq
      rewrite part-path H H′ π (proj₁ (pairs-split (names src) (pairs-r (quietName k) (pairs-r (quietName kb) (pairs-r ((_ , b) ∷ []) (pairs-r (cutNames c) (pairs-r (subjectNames S) ps))))))) off eq
            | part-alike H H′ bd (λ j m → off j (narrow (names-path π) (apart-l (names src) (pairs-r (quietName k) (pairs-r (quietName kb) (pairs-r ((_ , b) ∷ []) (pairs-r (cutNames c) (pairs-r (subjectNames S) ps))))) m))) = refl
    part-path H H′ (in-body {S = S} {c} {b} {kb} {k} {t = src} {bd} π) ps off eq
      rewrite part-alike H H′ src (λ j m → off j (narrow (names-path π) (apart-r (names src) (pairs-r (quietName k) (pairs-r (quietName kb) (pairs-r ((_ , b) ∷ []) (pairs-r (cutNames c) (pairs-r (subjectNames S) ps))))) m)))
            | part-path H H′ π (pairs-r (names src) (pairs-r (quietName k) (pairs-r (quietName kb) (pairs-r ((_ , b) ∷ []) (pairs-r (cutNames c) (pairs-r (subjectNames S) ps)))))) off eq = refl
    part-path H H′ (in-defer {k = k} π) ps off eq = part-path H H′ π (pairs-r (quietName k) ps) off eq

    partLanes-path : ∀ {h} (H H′ : Heapᴹ h) {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (π : PathLanes ls u)
                   → AllPairs _≢_ (laneNames ls) → Off H H′ (names u) → At.part H′ u ≡ At.part H u → At.partLanes H′ ls ≡ At.partLanes H ls
    partLanes-path H H′ (this-lane {c = c} {k} {t = s} {ls} π) ps off eq
      rewrite off (Kit.live c) (narrow (λ m → ++⁺ʳ (quietName k) (++⁺ˡ (names-path π m))) (apart-r (cutNames c) ps (here refl)))
            | part-path H H′ π (proj₁ (pairs-split (names s) (pairs-r (quietName k) (pairs-r (cutNames c) ps)))) off eq
            | partLanes-alike H H′ ls (λ j m → off j (narrow (names-path π) (apart-l (names s) (pairs-r (quietName k) (pairs-r (cutNames c) ps)) m))) = refl
    partLanes-path H H′ (next-lane {l = lane c k s} {ls} π) ps off eq
      rewrite off (Kit.live c) (narrow (λ m → ++⁺ʳ (quietName k) (++⁺ʳ (names s) (lanes-path π m))) (apart-r (cutNames c) ps (here refl)))
            | part-alike H H′ s (λ j m → off j (narrow (lanes-path π) (apart-r (names s) (pairs-r (quietName k) (pairs-r (cutNames c) ps)) m)))
            | partLanes-path H H′ π (pairs-r (names s) (pairs-r (quietName k) (pairs-r (cutNames c) ps))) off eq = refl

  ----------------------------------------------------------------------
  -- A cut's site holds no part, so the tree's part is unmoved

  if-nothing : ∀ {a} {X : Set a} (b : Bool) → (if b then nothing else nothing) ≡ nothing {A = X}
  if-nothing true  = refl
  if-nothing false = refl

  -- A takeWhile already taken holds none, whatever its switch reads.
  torn-take-part : ∀ {h} (H : Heapᴹ h) {t : Sub h [] R} {Δ A i q c k} {s : Sub h Δ A} (π : Path t (takeWhileˢ i q c k taken s))
                 → AllPairs _≢_ (names t) → At.part (thrown H c k s) t ≡ At.part H t
  torn-take-part H {c = c} {k} {s} π ps =
    part-path H (thrown H c k s) π ps off (trans (if-nothing (At.val (thrown H c k s) (Kit.live c))) (sym (if-nothing (At.val H (Kit.live c)))))
    where
      off : Off H (thrown H c k s) (cutNames c ++ quietName k ++ names s)
      off j a with all-++⁻ (cutNames c) a
      ... | nl ∷ _ , b = thrown-off H c k s j nl (proj₂ (all-++⁻ (quietName k) b))

  -- A connect whose body holds none holds none, its source torn or not.
  torn-body-part : ∀ {h} (H : Heapᴹ h) {t : Sub h [] R} {Δ A B S c b kb k fd e rp rt} {s : Sub h Δ A} {bd : Sub h (A ∷ Δ) B}
                   (π : Path t (connectˢ S c b kb k fd rp e rt s bd))
                 → AllPairs _≢_ (names t) → At.part H bd ≡ nothing → At.part (thrown H c k s) t ≡ At.part H t
  torn-body-part H {S = S} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {s = s} {bd} π ps none = part-path H (thrown H c k s) π ps off at
    where
      psᵘ = fresh-path π ps
      ps₅ = pairs-r (quietName k) (pairs-r (quietName kb) (pairs-r ((_ , b) ∷ []) (pairs-r (cutNames c) (pairs-r (subjectNames S) psᵘ))))
      off : Off H (thrown H c k s) (subjectNames S ++ cutNames c ++ (_ , b) ∷ quietName kb ++ quietName k ++ names s ++ names bd)
      off j a with all-++⁻ (subjectNames S) a
      ... | _ , a₁ with all-++⁻ (cutNames c) a₁
      ... | nl ∷ _ , _ ∷ a₂ with all-++⁻ (quietName kb) a₂
      ... | _ , a₃ with all-++⁻ (quietName k) a₃
      ... | _ , a₄ = thrown-off H c k s j nl (proj₁ (all-++⁻ (names s) a₄))
      alike : Alike H (thrown H c k s) (names bd)
      alike j m = thrown-off H c k s j
        (≢-flip (lookupᴬ (apart-r (cutNames c) (pairs-r (subjectNames S) psᵘ) (here refl))
                         (there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ʳ (names s) m))))))
        (apart-l (names s) ps₅ m)
      at : At.part (thrown H c k s) (connectˢ S c b kb k fd rp e rt s bd) ≡ At.part H (connectˢ S c b kb k fd rp e rt s bd)
      at rewrite part-alike H (thrown H c k s) bd alike | none = refl
