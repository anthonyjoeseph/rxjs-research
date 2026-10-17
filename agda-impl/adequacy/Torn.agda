{-# OPTIONS --guardedness #-}

-- TORN: the heap a subscription's unsubscribe leaves, and what it leaves
-- alone.  A teardown writes only names the torn subscription holds, and
-- a subscription's part reads only its own names, so with the names all
-- distinct (`Books.fresh`) the rest of the tree reads the same heap.
module adequacy.Torn where

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Bool using (Bool; true; false; if_then_else_; _∨_; _∧_)
open import Data.Bool.Properties using (∧-assoc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing; is-just)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (tabulate to tabulateᴬ; lookup to lookupᴬ)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁻ to all-++⁻)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; _∷_)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴸ_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Any.Properties using (++⁺ˡ; ++⁺ʳ)

open import denotation.MonotonicList using (Timeline)
import denotation.Unfold as U
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

  get-put-same : ∀ {ℓ} {P : Kind → Set ℓ} {w k} (xs : All P w) (i : w ∋ k) {y : P k} → get (put xs i y) i ≡ y
  get-put-same (x ∷ xs) hereʰ      = refl
  get-put-same (x ∷ xs) (thereʰ i) = get-put-same xs i

  -- A switch thrown reads thrown.
  cut-stored : ∀ {h} (H : Heapᴹ h) (c : Kit.Cut h) → At.val (store H (Kit.live c) (lift false)) (Kit.live c) ≡ false
  cut-stored H c rewrite get-put-same H (Kit.live c) {y = stored (lift false) same} = refl

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

  -- A takeWhile already taken holds none, whatever its switch reads;
  -- its switch thrown, nothing below it is seen.
  module _ {h} (H : Heapᴹ h) {Δ A i q c k} {s : Sub h Δ A} (ps : AllPairs _≢_ (names (takeWhileˢ i q c k taken s))) where
    private
      H′ = thrown H c k s

    take-off : Off H H′ (names (takeWhileˢ i q c k taken s))
    take-off j a with all-++⁻ (cutNames c) a
    ... | nl ∷ _ , b = thrown-off H c k s j nl (proj₂ (all-++⁻ (quietName k) b))

    take-eq : At.part H′ (takeWhileˢ i q c k taken s) ≡ At.part H (takeWhileˢ i q c k taken s)
    take-eq = trans (if-nothing (At.val H′ (Kit.live c))) (sym (if-nothing (At.val H (Kit.live c))))

    take-thrown : At.val H′ (Kit.live c) ≡ false
    take-thrown = trans (cong lower (tornVia-off (store H (Kit.live c) (lift false)) k s (Kit.live c)
                          (narrow (λ m → ++⁺ʳ (quietName k) m) (apart-r (cutNames c) ps (here refl))))) (cut-stored H c)

    take-dead : ∀ {Δ′ A′} {u : Sub h Δ′ A′} (ψ : Path (takeWhileˢ i q c k taken s) u) → seen H′ ψ ≡ true → is-just (At.part H′ u) ≡ true → ⊥
    take-dead here        _  ju = false≢ (subst (λ z → is-just z ≡ true) (if-nothing (At.val H′ (Kit.live c))) ju)
    take-dead (in-take ψ) sn _  = false≢ (trans (sym take-thrown) (proj₁ (∧-split (At.val H′ (Kit.live c)) sn)))

  -- A connect whose body holds none holds none, its source torn or not;
  -- nothing below it is seen.
  module _ {h} (H : Heapᴹ h) {Δ A B S c b kb k fd e rp rt} {s : Sub h Δ A} {bd : Sub h (A ∷ Δ) B}
           (ps : AllPairs _≢_ (names (connectˢ S c b kb k fd rp e rt s bd))) (none : At.part H bd ≡ nothing) where
    private
      H′ = thrown H c k s
      ps₅ = pairs-r (quietName k) (pairs-r (quietName kb) (pairs-r ((_ , b) ∷ []) (pairs-r (cutNames c) (pairs-r (subjectNames S) ps))))

    body-off : Off H H′ (names (connectˢ S c b kb k fd rp e rt s bd))
    body-off j a with all-++⁻ (subjectNames S) a
    ... | _ , a₁ with all-++⁻ (cutNames c) a₁
    ... | nl ∷ _ , _ ∷ a₂ with all-++⁻ (quietName kb) a₂
    ... | _ , a₃ with all-++⁻ (quietName k) a₃
    ... | _ , a₄ = thrown-off H c k s j nl (proj₁ (all-++⁻ (names s) a₄))

    body-none : At.part H′ bd ≡ nothing
    body-none = trans (part-alike H H′ bd alike) none
      where
        alike : Alike H H′ (names bd)
        alike j m = thrown-off H c k s j
          (≢-flip (lookupᴬ (apart-r (cutNames c) (pairs-r (subjectNames S) ps) (here refl))
                           (there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ʳ (names s) m))))))
          (apart-l (names s) ps₅ m)

    body-eq : At.part H′ (connectˢ S c b kb k fd rp e rt s bd) ≡ At.part H (connectˢ S c b kb k fd rp e rt s bd)
    body-eq rewrite body-none | none = refl

    body-dead : ∀ {Δ′ A′} {u : Sub h Δ′ A′} (ψ : Path (connectˢ S c b kb k fd rp e rt s bd) u) → seen H′ ψ ≡ true → is-just (At.part H′ u) ≡ true → ⊥
    body-dead here          _  ju = false≢ (subst (λ z → is-just (At.connected H′ rp e rt (At.part H′ s) z) ≡ true) body-none ju)
    body-dead (in-source ψ) sn _  = false≢ (subst (λ z → is-just z ≡ true) body-none (proj₁ (∧-split (is-just (At.part H′ bd)) sn)))
    body-dead (in-body ψ)   sn ju =
      false≢ (subst (λ z → is-just z ≡ true) body-none (seen-up H′ ψ (proj₂ (∧-split (is-just (At.part H′ s) ∨ is-just e) sn)) ju))

  torn-take-part : ∀ {h} (H : Heapᴹ h) {t : Sub h [] R} {Δ A i q c k} {s : Sub h Δ A} (π : Path t (takeWhileˢ i q c k taken s))
                 → AllPairs _≢_ (names t) → At.part (thrown H c k s) t ≡ At.part H t
  torn-take-part H {Δ = Δ} {A} {i} {q} {c} {k} {s} π ps =
    part-path H _ π ps (take-off H {Δ} {A} {i} {q} {c} {k} {s} (fresh-path π ps)) (take-eq H {Δ} {A} {i} {q} {c} {k} {s} (fresh-path π ps))

  torn-body-part : ∀ {h} (H : Heapᴹ h) {t : Sub h [] R} {Δ A B S c b kb k fd e rp rt} {s : Sub h Δ A} {bd : Sub h (A ∷ Δ) B}
                   (π : Path t (connectˢ S c b kb k fd rp e rt s bd))
                 → AllPairs _≢_ (names t) → At.part H bd ≡ nothing → At.part (thrown H c k s) t ≡ At.part H t
  torn-body-part H {Δ = Δ} {A} {B} {S} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {s} {bd} π ps none =
    part-path H _ π ps (body-off H {Δ} {A} {B} {S} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {s} {bd} (fresh-path π ps) none)
                       (body-eq H {Δ} {A} {B} {S} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {s} {bd} (fresh-path π ps) none)

  ----------------------------------------------------------------------
  -- A path seen past a teardown was seen before it, to the same part

  mutual
    seen-alike : ∀ {h} (H H′ : Heapᴹ h) {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (ψ : Path t u)
               → Alike H H′ (names t) → seen H′ ψ ≡ seen H ψ
    seen-alike H H′ here ag = refl
    seen-alike H H′ (in-map ψ) ag = seen-alike H H′ ψ ag
    seen-alike H H′ (in-scan ψ) ag = seen-alike H H′ ψ (λ j m → ag j (there m))
    seen-alike H H′ (in-take {c = c} {k} ψ) ag
      rewrite ag (Kit.live c) (here refl) | seen-alike H H′ ψ (λ j m → ag j (++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) m))) = refl
    seen-alike H H′ (in-outer {fl = fl} {oc} {k} ψ) ag =
      seen-alike H H′ ψ (λ j m → ag j (++⁺ʳ (flatNames fl) (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ˡ m))))))
    seen-alike H H′ (in-lanes {fl = fl} {oc} {k} {t = so} πL) ag =
      seenL-alike H H′ πL (λ j m → ag j (++⁺ʳ (flatNames fl) (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ʳ (names so) m))))))
    seen-alike H H′ (in-source {S = S} {c} {kb = kb} {k} {t = src} {bd} ψ) ag
      rewrite part-alike H H′ bd (λ j m → ag j (++⁺ʳ (subjectNames S) (++⁺ʳ (cutNames c) (there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ʳ (names src) m)))))))
            | seen-alike H H′ ψ (λ j m → ag j (++⁺ʳ (subjectNames S) (++⁺ʳ (cutNames c) (there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ˡ m))))))) = refl
    seen-alike H H′ (in-body {S = S} {c} {kb = kb} {k} {t = src} {bd} ψ) ag
      rewrite part-alike H H′ src (λ j m → ag j (++⁺ʳ (subjectNames S) (++⁺ʳ (cutNames c) (there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ˡ m)))))))
            | seen-alike H H′ ψ (λ j m → ag j (++⁺ʳ (subjectNames S) (++⁺ʳ (cutNames c) (there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ʳ (names src) m))))))) = refl
    seen-alike H H′ (in-defer {k = k} ψ) ag = seen-alike H H′ ψ (λ j m → ag j (++⁺ʳ (quietName k) m))

    seenL-alike : ∀ {h} (H H′ : Heapᴹ h) {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (πL : PathLanes ls u)
                → Alike H H′ (laneNames ls) → seenL H′ πL ≡ seenL H πL
    seenL-alike H H′ (this-lane {c = c} {k} ψ) ag
      rewrite ag (Kit.live c) (here refl) | seen-alike H H′ ψ (λ j m → ag j (++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) (++⁺ˡ m)))) = refl
    seenL-alike H H′ (next-lane {l = lane c k s} πL) ag =
      seenL-alike H H′ πL (λ j m → ag j (++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) (++⁺ʳ (names s) m))))

  -- A path that leaves its root.
  Deep : ∀ {h Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} → Path t u → Set
  Deep here = ⊥
  Deep _    = ⊤

  -- Against a site: a node apart from what was written there, or above
  -- it.
  Same : ∀ {h} → Heapᴹ h → Heapᴹ h → ∀ {Δ A Δ′ A′} → Sub h Δ A → Sub h Δ′ A′ → Set₁
  Same H H′ w u = Alike H H′ (names u) ⊎ Σ (Path u w) Deep

  -- A connect above a site: its source reads alike.
  src-path : ∀ {h} (H H′ : Heapᴹ h) {Δ A Δ′ A′ B′ S c b kb k fd rp e rt} {w : Sub h Δ A} {src : Sub h Δ′ A′} {bd : Sub h (A′ ∷ Δ′) B′}
           → Off H H′ (names w) → At.part H′ w ≡ At.part H w
           → AllPairs _≢_ (names (connectˢ S c b kb k fd rp e rt src bd)) → (ρ : Path (connectˢ S c b kb k fd rp e rt src bd) w) → Deep ρ
           → At.part H′ src ≡ At.part H src
  src-path H H′ off eqw ps here ()
  src-path H H′ {S = S} {c} {b} {kb} {k} {src = src} off eqw ps (in-source ρ) _ =
    part-path H H′ ρ (proj₁ (pairs-split (names src) (pairs-r (quietName k) (pairs-r (quietName kb) (pairs-r ((_ , b) ∷ []) (pairs-r (cutNames c) (pairs-r (subjectNames S) ps))))))) off eqw
  src-path H H′ {S = S} {c} {b} {kb} {k} {src = src} off eqw ps (in-body ρ) _ =
    part-alike H H′ src (λ j m → off j (narrow (names-path ρ)
      (apart-r (names src) (pairs-r (quietName k) (pairs-r (quietName kb) (pairs-r ((_ , b) ∷ []) (pairs-r (cutNames c) (pairs-r (subjectNames S) ps))))) m)))

  -- A WRITE AT A SITE, SEEN FROM THE ROOT: a path seen after it is seen
  -- before and reaches a node apart from the site or above it, or it runs
  -- inside the site, the site's own path seen before.
  module Seeing {h} (H H′ : Heapᴹ h) {Δ A} {w : Sub h Δ A} (off : Off H H′ (names w)) (eqw : At.part H′ w ≡ At.part H w) where
    Seen : ∀ {Δ₀ A₀ Δ′ A′} {t : Sub h Δ₀ A₀} {u : Sub h Δ′ A′} → Path t w → Path t u → Set₁
    Seen {u = u} π ψ = (seen H ψ ≡ true × Same H H′ w u) ⊎ (seen H π ≡ true × Σ (Path w u) λ ρ → seen H′ ρ ≡ true)

    SeenL : ∀ {Δ₀ B₀ Δ′ A′} {ls : List (Lane h Δ₀ B₀)} {u : Sub h Δ′ A′} → PathLanes ls w → PathLanes ls u → Set₁
    SeenL {u = u} πL ψL = (seenL H ψL ≡ true × Same H H′ w u) ⊎ (seenL H πL ≡ true × Σ (Path w u) λ ρ → seen H′ ρ ≡ true)

    -- A frame's own condition read before, carried over what is below it.
    under : ∀ {Δ₀ A₀ Δ₁ A₁ Δ′ A′} {t₀ : Sub h Δ₀ A₀} {t₁ : Sub h Δ₁ A₁} {u : Sub h Δ′ A′} {π : Path t₀ w} {ψ : Path t₀ u}
              {π₁ : Path t₁ w} {ψ₁ : Path t₁ u} (b : Bool) → b ≡ true
          → seen H π₁ ≡ (b ∧ seen H π) → seen H ψ₁ ≡ (b ∧ seen H ψ) → Seen π ψ → Seen π₁ ψ₁
    under b bt eπ eψ (inj₁ (s , sm))       = inj₁ (trans eψ (∧-join bt s) , sm)
    under b bt eπ eψ (inj₂ (sπ , ρ , sρ)) = inj₂ (trans eπ (∧-join bt sπ) , ρ , sρ)

    underL : ∀ {Δ₀ A₀ Δ₁ B₁ Δ′ A′} {t₀ : Sub h Δ₀ A₀} {ls : List (Lane h Δ₁ B₁)} {u : Sub h Δ′ A′} {π : Path t₀ w} {ψ : Path t₀ u}
               {π₁ : PathLanes ls w} {ψ₁ : PathLanes ls u} (b : Bool) → b ≡ true
           → seenL H π₁ ≡ (b ∧ seen H π) → seenL H ψ₁ ≡ (b ∧ seen H ψ) → Seen π ψ → SeenL π₁ ψ₁
    underL b bt eπ eψ (inj₁ (s , sm))       = inj₁ (trans eψ (∧-join bt s) , sm)
    underL b bt eπ eψ (inj₂ (sπ , ρ , sρ)) = inj₂ (trans eπ (∧-join bt sπ) , ρ , sρ)

    mutual
      vis : ∀ {Δ₀ A₀ Δ′ A′} {t : Sub h Δ₀ A₀} {u : Sub h Δ′ A′} → AllPairs _≢_ (names t) → (π : Path t w) → (ψ : Path t u)
          → seen H′ ψ ≡ true → Seen π ψ
      vis ps here ψ sn = inj₂ (refl , ψ , sn)
      vis ps π@(in-map _)    here sn = inj₁ (refl , inj₂ (π , tt))
      vis ps π@(in-scan _)   here sn = inj₁ (refl , inj₂ (π , tt))
      vis ps π@(in-take _)   here sn = inj₁ (refl , inj₂ (π , tt))
      vis ps π@(in-outer _)  here sn = inj₁ (refl , inj₂ (π , tt))
      vis ps π@(in-lanes _)  here sn = inj₁ (refl , inj₂ (π , tt))
      vis ps π@(in-source _) here sn = inj₁ (refl , inj₂ (π , tt))
      vis ps π@(in-body _)   here sn = inj₁ (refl , inj₂ (π , tt))
      vis ps π@(in-defer _)  here sn = inj₁ (refl , inj₂ (π , tt))
      vis ps (in-map π) (in-map ψ) sn = vis ps π ψ sn
      vis (_ ∷ ps) (in-scan π) (in-scan ψ) sn = vis ps π ψ sn
      vis ps π₁@(in-take {c = c} {k} {tk = tk} π) ψ₁@(in-take ψ) sn with ∧-split (At.val H′ (Kit.live c)) sn
      ... | lv , r with ∧-split (isTaking tk) r
      ... | tg , sψ =
        under {π = π} {ψ} {π₁} {ψ₁} (At.val H (Kit.live c) ∧ isTaking tk)
              (∧-join (trans (sym (cong lower (off (Kit.live c) (narrow (λ m → ++⁺ʳ (quietName k) (names-path π m)) (apart-r (cutNames c) ps (here refl)))))) lv) tg)
              (sym (∧-assoc (At.val H (Kit.live c)) (isTaking tk) (seen H π))) (sym (∧-assoc (At.val H (Kit.live c)) (isTaking tk) (seen H ψ)))
              (vis (pairs-r (quietName k) (pairs-r (cutNames c) ps)) π ψ sψ)
      vis ps (in-outer {fl = fl} {oc} {k} {r} {t = so} π) (in-outer ψ) sn =
        vis (proj₁ (pairs-split (names so) (pairs-r ((_ , r) ∷ []) (pairs-r (quietName k) (pairs-r (cutNames oc) (pairs-r (flatNames fl) ps)))))) π ψ sn
      vis ps (in-outer {fl = fl} {oc} {k} {r} {t = so} {ls} π) (in-lanes ψL) sn =
        inj₁ (trans (sym (seenL-alike H H′ ψL al)) sn , inj₁ (λ j m → al j (lanes-path ψL m)))
        where
          al : Alike H H′ (laneNames ls)
          al j m = off j (narrow (names-path π) (apart-l (names so) (pairs-r ((_ , r) ∷ []) (pairs-r (quietName k) (pairs-r (cutNames oc) (pairs-r (flatNames fl) ps)))) m))
      vis ps (in-lanes {fl = fl} {oc} {k} {r} {t = so} πL) (in-outer ψ) sn =
        inj₁ (trans (sym (seen-alike H H′ ψ al)) sn , inj₁ (λ j m → al j (names-path ψ m)))
        where
          al : Alike H H′ (names so)
          al j m = off j (narrow (lanes-path πL) (apart-r (names so) (pairs-r ((_ , r) ∷ []) (pairs-r (quietName k) (pairs-r (cutNames oc) (pairs-r (flatNames fl) ps)))) m))
      vis ps (in-lanes {fl = fl} {oc} {k} {r} {t = so} πL) (in-lanes ψL) sn =
        visL (pairs-r (names so) (pairs-r ((_ , r) ∷ []) (pairs-r (quietName k) (pairs-r (cutNames oc) (pairs-r (flatNames fl) ps))))) πL ψL sn
      vis ps π₁@(in-source {S = S} {c} {b} {kb} {k} {t = src} {bd} π) ψ₁@(in-source ψ) sn with ∧-split (is-just (At.part H′ bd)) sn
      ... | jb , sψ =
        under {π = π} {ψ} {π₁} {ψ₁} (is-just (At.part H bd)) (subst (λ z → is-just z ≡ true) (part-alike H H′ bd al) jb) refl refl
              (vis (proj₁ (pairs-split (names src) (pairs-r (quietName k) (pairs-r (quietName kb) (pairs-r ((_ , b) ∷ []) (pairs-r (cutNames c) (pairs-r (subjectNames S) ps))))))) π ψ sψ)
        where
          al : Alike H H′ (names bd)
          al j m = off j (narrow (names-path π) (apart-l (names src) (pairs-r (quietName k) (pairs-r (quietName kb) (pairs-r ((_ , b) ∷ []) (pairs-r (cutNames c) (pairs-r (subjectNames S) ps))))) m))
      vis ps (in-source {S = S} {c} {b} {kb} {k} {e = e} {t = src} {bd} π) (in-body ψ) sn with ∧-split (is-just (At.part H′ src) ∨ is-just e) sn
      ... | js , sψ =
        inj₁ (∧-join (subst (λ z → (is-just z ∨ is-just e) ≡ true)
                 (part-path H H′ π (proj₁ (pairs-split (names src) (pairs-r (quietName k) (pairs-r (quietName kb) (pairs-r ((_ , b) ∷ []) (pairs-r (cutNames c) (pairs-r (subjectNames S) ps))))))) off eqw) js)
               (trans (sym (seen-alike H H′ ψ al)) sψ) , inj₁ (λ j m → al j (names-path ψ m)))
        where
          al : Alike H H′ (names bd)
          al j m = off j (narrow (names-path π) (apart-l (names src) (pairs-r (quietName k) (pairs-r (quietName kb) (pairs-r ((_ , b) ∷ []) (pairs-r (cutNames c) (pairs-r (subjectNames S) ps))))) m))
      vis ps (in-body {S = S} {c} {b} {kb} {k} {t = src} {bd} π) (in-source ψ) sn with ∧-split (is-just (At.part H′ bd)) sn
      ... | jb , sψ =
        inj₁ (∧-join (subst (λ z → is-just z ≡ true)
                 (part-path H H′ π (pairs-r (names src) (pairs-r (quietName k) (pairs-r (quietName kb) (pairs-r ((_ , b) ∷ []) (pairs-r (cutNames c) (pairs-r (subjectNames S) ps)))))) off eqw) jb)
               (trans (sym (seen-alike H H′ ψ al)) sψ) , inj₁ (λ j m → al j (names-path ψ m)))
        where
          al : Alike H H′ (names src)
          al j m = off j (narrow (names-path π) (apart-r (names src) (pairs-r (quietName k) (pairs-r (quietName kb) (pairs-r ((_ , b) ∷ []) (pairs-r (cutNames c) (pairs-r (subjectNames S) ps))))) m))
      vis ps π₁@(in-body {S = S} {c} {b} {kb} {k} {e = e} {t = src} {bd} π) ψ₁@(in-body ψ) sn with ∧-split (is-just (At.part H′ src) ∨ is-just e) sn
      ... | js , sψ =
        under {π = π} {ψ} {π₁} {ψ₁} (is-just (At.part H src) ∨ is-just e) (subst (λ z → (is-just z ∨ is-just e) ≡ true) (part-alike H H′ src al) js) refl refl
              (vis (pairs-r (names src) (pairs-r (quietName k) (pairs-r (quietName kb) (pairs-r ((_ , b) ∷ []) (pairs-r (cutNames c) (pairs-r (subjectNames S) ps)))))) π ψ sψ)
        where
          al : Alike H H′ (names src)
          al j m = off j (narrow (names-path π) (apart-r (names src) (pairs-r (quietName k) (pairs-r (quietName kb) (pairs-r ((_ , b) ∷ []) (pairs-r (cutNames c) (pairs-r (subjectNames S) ps))))) m))
      vis ps (in-defer {k = k} π) (in-defer ψ) sn = vis (pairs-r (quietName k) ps) π ψ sn

      visL : ∀ {Δ₀ B₀ Δ′ A′} {ls : List (Lane h Δ₀ B₀)} {u : Sub h Δ′ A′} → AllPairs _≢_ (laneNames ls) → (πL : PathLanes ls w) → (ψL : PathLanes ls u)
           → seenL H′ ψL ≡ true → SeenL πL ψL
      visL ps π₁@(this-lane {c = c} {k} {t = s} π) ψ₁@(this-lane ψ) sn with ∧-split (At.val H′ (Kit.live c)) sn
      ... | lv , sψ =
        underL {π = π} {ψ} {π₁} {ψ₁} (At.val H (Kit.live c))
               (trans (sym (cong lower (off (Kit.live c) (narrow (λ m → ++⁺ʳ (quietName k) (++⁺ˡ (names-path π m))) (apart-r (cutNames c) ps (here refl)))))) lv) refl refl
               (vis (proj₁ (pairs-split (names s) (pairs-r (quietName k) (pairs-r (cutNames c) ps)))) π ψ sψ)
      visL ps (this-lane {c = c} {k} {t = s} {ls} π) (next-lane ψL) sn =
        inj₁ (trans (sym (seenL-alike H H′ ψL al)) sn , inj₁ (λ j m → al j (lanes-path ψL m)))
        where
          al : Alike H H′ (laneNames ls)
          al j m = off j (narrow (names-path π) (apart-l (names s) (pairs-r (quietName k) (pairs-r (cutNames c) ps)) m))
      visL ps (next-lane {l = lane c k s} πL) (this-lane ψ) sn with ∧-split (At.val H′ (Kit.live c)) sn
      ... | lv , sψ =
        inj₁ (∧-join (trans (sym (cong lower (off (Kit.live c) (narrow (λ m → ++⁺ʳ (quietName k) (++⁺ʳ (names s) (lanes-path πL m))) (apart-r (cutNames c) ps (here refl)))))) lv)
               (trans (sym (seen-alike H H′ ψ al)) sψ) , inj₁ (λ j m → al j (names-path ψ m)))
        where
          al : Alike H H′ (names s)
          al j m = off j (narrow (lanes-path πL) (apart-r (names s) (pairs-r (quietName k) (pairs-r (cutNames c) ps)) m))
      visL ps (next-lane {l = lane c k s} πL) (next-lane ψL) sn =
        visL (pairs-r (names s) (pairs-r (quietName k) (pairs-r (cutNames c) ps))) πL ψL sn

    same-part : ∀ {Δ′ A′} {u : Sub h Δ′ A′} → AllPairs _≢_ (names u) → Same H H′ w u → At.part H′ u ≡ At.part H u
    same-part {u = u} ps (inj₁ al)      = part-alike H H′ u al
    same-part         ps (inj₂ (ρ , _)) = part-path H H′ ρ ps off eqw

    same-src : ∀ {Δ′ A′ B′ S c b kb k fd rp e rt} {src : Sub h Δ′ A′} {bd : Sub h (A′ ∷ Δ′) B′}
             → AllPairs _≢_ (names (connectˢ S c b kb k fd rp e rt src bd)) → Same H H′ w (connectˢ S c b kb k fd rp e rt src bd)
             → At.part H′ src ≡ At.part H src
    same-src {S = S} {c} {kb = kb} {k} {src = src} ps (inj₁ al) =
      part-alike H H′ src (λ j m → al j (++⁺ʳ (subjectNames S) (++⁺ʳ (cutNames c) (there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ˡ m)))))))
    same-src ps (inj₂ (ρ , d)) = src-path H H′ off eqw ps ρ d

    -- What every node held passes, every node held after the write does,
    -- the site's own nodes by what the write leaves of them.
    each-write : ∀ {P : ∀ {Γ A} → U.Node Γ A → Set} {Δ₀ A₀} {t : Sub h Δ₀ A₀} → AllPairs _≢_ (names t) → Path t w
               → (Each H P w → Each H′ P w) → Each H P t → Each H′ P t
    each-write {P} {t = t} ps π inner ev = record { parts = pa ; pools = po ; rests = re }
      where
        sub : seen H π ≡ true → Each H P w
        sub sπ = record
          { parts = λ ρ sρ → Each.parts ev (π ⊕ ρ) (seen-join H π ρ sπ sρ)
          ; pools = λ ρ sρ → Each.pools ev (π ⊕ ρ) (seen-join H π ρ sπ sρ)
          ; rests = λ ρ sρ → Each.rests ev (π ⊕ ρ) (seen-join H π ρ sπ sρ) }

        pa : ∀ {Δ′ A′} {u : Sub h Δ′ A′} (ψ : Path t u) → seen H′ ψ ≡ true → ∀ {c} → At.part H′ u ≡ just c → P c
        pa ψ sn e with vis ps π ψ sn
        ... | inj₁ (s , sm)        = Each.parts ev ψ s (trans (sym (same-part (fresh-path ψ ps) sm)) e)
        ... | inj₂ (sπ , ρ , sρ) = Each.parts (inner (sub sπ)) ρ sρ e

        po : ∀ {Δ′ A′ B′} {op f fl oc k r pl} {so : Sub h Δ′ A′} {ls : List (Lane h Δ′ B′)}
           → (ψ : Path t (flatMapˢ op f fl oc k r pl so ls)) → seen H′ ψ ≡ true
           → ∀ {c} → At.part H′ (flatMapˢ op f fl oc k r pl so ls) ≡ just c → P pl
        po ψ sn e with vis ps π ψ sn
        ... | inj₁ (s , sm)        = Each.pools ev ψ s (trans (sym (same-part (fresh-path ψ ps) sm)) e)
        ... | inj₂ (sπ , ρ , sρ) = Each.pools (inner (sub sπ)) ρ sρ e

        re : ∀ {Δ′ A′ B′} {S c b kb k fd rp e rt} {src : Sub h Δ′ A′} {bd : Sub h (A′ ∷ Δ′) B′}
           → (ψ : Path t (connectˢ S c b kb k fd rp e rt src bd)) → seen H′ ψ ≡ true
           → ∀ {n} → At.part H′ (connectˢ S c b kb k fd rp e rt src bd) ≡ just n
           → At.part H′ src ≡ nothing → ∀ {c₀} → e ≡ just c₀ → P rt
        re ψ sn e none ej with vis ps π ψ sn
        ... | inj₁ (s , sm)        = Each.rests ev ψ s (trans (sym (same-part (fresh-path ψ ps) sm)) e)
                                       (trans (sym (same-src (fresh-path ψ ps) sm)) none) ej
        ... | inj₂ (sπ , ρ , sρ) = Each.rests (inner (sub sπ)) ρ sρ e none ej

    -- What every node held passes, every node held past a teardown does:
    -- nothing seen below the site holds a part.
    each-seen : ∀ {P : ∀ {Γ A} → U.Node Γ A → Set} {Δ₀ A₀} {t : Sub h Δ₀ A₀}
              → (∀ {Δ′ A′} {u : Sub h Δ′ A′} (ψ : Path w u) → seen H′ ψ ≡ true → is-just (At.part H′ u) ≡ true → ⊥)
              → AllPairs _≢_ (names t) → Path t w → Each H P t → Each H′ P t
    each-seen dead ps π = each-write ps π λ _ → record
      { parts = λ ρ sρ e → ⊥-elim (dead ρ sρ (cong is-just e))
      ; pools = λ ρ sρ e → ⊥-elim (dead ρ sρ (cong is-just e))
      ; rests = λ ρ sρ e _ _ → ⊥-elim (dead ρ sρ (cong is-just e)) }

  -- Every part held heads as it did: a site's teardown leaves what it
  -- reached unseen, and the rest reads alike.
  torn-take-each : ∀ {h} (H : Heapᴹ h) {P : ∀ {Γ A} → U.Node Γ A → Set} {t : Sub h [] R} {Δ A i q c k} {s : Sub h Δ A}
                   (π : Path t (takeWhileˢ i q c k taken s)) → AllPairs _≢_ (names t) → Each H P t → Each (thrown H c k s) P t
  torn-take-each H {Δ = Δ} {A} {i} {q} {c} {k} {s} π ps =
    Seeing.each-seen H _ (take-off H {Δ} {A} {i} {q} {c} {k} {s} (fresh-path π ps)) (take-eq H {Δ} {A} {i} {q} {c} {k} {s} (fresh-path π ps))
                         (take-dead H {Δ} {A} {i} {q} {c} {k} {s} (fresh-path π ps)) ps π

  torn-body-each : ∀ {h} (H : Heapᴹ h) {P : ∀ {Γ A} → U.Node Γ A → Set} {t : Sub h [] R} {Δ A B S c b kb k fd e rp rt} {s : Sub h Δ A} {bd : Sub h (A ∷ Δ) B}
                   (π : Path t (connectˢ S c b kb k fd rp e rt s bd)) → AllPairs _≢_ (names t) → At.part H bd ≡ nothing → Each H P t → Each (thrown H c k s) P t
  torn-body-each H {Δ = Δ} {A} {B} {S} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {s} {bd} π ps none =
    Seeing.each-seen H _ (body-off H {Δ} {A} {B} {S} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {s} {bd} (fresh-path π ps) none)
                         (body-eq H {Δ} {A} {B} {S} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {s} {bd} (fresh-path π ps) none)
                         (body-dead H {Δ} {A} {B} {S} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {s} {bd} (fresh-path π ps) none) ps π
