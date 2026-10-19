{-# OPTIONS --guardedness #-}

-- MOVES: the witness (`adequacy.Strong`'s `Sub`) rewritten at one node,
-- and what each part of the relation keeps across the rewrite.  A hop
-- between re-entry configurations is a chain of moves; each part of
-- `Carried` is kept by a lemma per move, so a part added to `Carried`
-- costs a lemma per move and no hop's body.
module adequacy.Moves where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Bool using (true; false)
open import Data.Nat using (ℕ; suc; _+_; _<_; s≤s; z≤n)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.List.Relation.Unary.All using (All; []; _∷_; map) renaming (tabulate to tabulateᴬ; lookup to lookupᴬ)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁻ to all-++⁻)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Unary.AllPairs.Properties using () renaming (++⁺ to pairs-++⁺)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.List.Relation.Unary.Linked using (Linked; [-]; _∷_)
open import Data.List.Relation.Unary.Linked.Properties using (Linked⇒All)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴸ_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Any.Properties using (++⁻; ++⁺ˡ; ++⁺ʳ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Data.Sum as Sum
open import Data.Maybe using (just; nothing)

open import Tree using (Obs)
import Tree as T
open import denotation.MonotonicList using (Timeline; From; Frame; at; _<ᵖ_; <ᵖ-trans; <ᵖ-irrefl) renaming (done to doneᶠ; quiet to quietᶠ)
import denotation.Unfold as U
open import operation.AbstractObservable using (module Heap; module Run) renaming (module Machine to Shared)
open import operation.PureObservable using (Pureᴾ; Out; module Pure)
open import adequacy.Strong using (module Strongly)

module Moving (R : Set) where
  open Heap using (World; Sink; Handle; _⊑_; play; slot; cell)
  open Shared Timeline (Out R) using (Heapᴹ)
  open Pure R using (Timer; cascade)
  open Strongly R
  open Run (Pureᴾ R) using (module Kit; Kont)

  true≢false : true ≢ false
  true≢false ()

  ----------------------------------------------------------------------
  -- One node rewritten

  mutual
    plant : ∀ {h Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} → Path t u → Sub h Δ′ A′ → Sub h Δ A
    plant here v                                                      = v
    plant (in-map {f = f} π) v                                         = mapˢ f (plant π v)
    plant (in-scan {f = f} {r} π) v                                    = scanˢ f r (plant π v)
    plant (in-take {i = i} {p} {c} {k} {tk} π) v                       = takeWhileˢ i p c k tk (plant π v)
    plant (in-outer {op = op} {f} {fl} {oc} {k} {r} {pl} {ls = ls} π) v     = flatMapˢ op f fl oc k r pl (plant π v) ls
    plant (in-lanes {op = op} {f} {fl} {oc} {k} {r} {pl} {t = so} π) v      = flatMapˢ op f fl oc k r pl so (plantᴸ π v)
    plant (in-source {S = S} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {bd = bd} π) v = connectˢ S c b kb k fd rp e rt (plant π v) bd
    plant (in-body {S = S} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {t = s} π) v     = connectˢ S c b kb k fd rp e rt s (plant π v)
    plant (in-defer {k = k} π) v                                       = deferˢ k (plant π v)

    plantᴸ : ∀ {h Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} → PathLanes ls u → Sub h Δ′ A′ → List (Lane h Δ B)
    plantᴸ (this-lane {c = c} {k} {ls = ls} π) v = lane c k (plant π v) ∷ ls
    plantᴸ (next-lane {l = l} π) v               = l ∷ plantᴸ π v

  -- Where the planted node now sits.
  mutual
    planted : ∀ {h Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (v : Sub h Δ′ A′) → Path (plant π v) v
    planted here v          = here
    planted (in-map π) v    = in-map (planted π v)
    planted (in-scan π) v   = in-scan (planted π v)
    planted (in-take π) v   = in-take (planted π v)
    planted (in-outer π) v  = in-outer (planted π v)
    planted (in-lanes π) v  = in-lanes (plantedᴸ π v)
    planted (in-source π) v = in-source (planted π v)
    planted (in-body π) v   = in-body (planted π v)
    planted (in-defer π) v  = in-defer (planted π v)

    plantedᴸ : ∀ {h Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (π : PathLanes ls u) (v : Sub h Δ′ A′)
             → PathLanes (plantᴸ π v) v
    plantedᴸ (this-lane π) v = this-lane (planted π v)
    plantedᴸ (next-lane π) v = next-lane (plantedᴸ π v)

  ----------------------------------------------------------------------
  -- THE WORK OWED: one for each operator reached and not begun.  A
  -- defer's body is not counted: its expansion is a skip of the
  -- meaning's.

  syn : ∀ {Δ A} → Obs Timeline Δ A → ℕ
  syn (T.cold c)          = 1
  syn T.empty             = 1
  syn (T.of xs)           = 1
  syn (T.map f s)         = suc (syn s)
  syn (T.scan f z s)      = suc (syn s)
  syn (T.takeWhile i q s) = suc (syn s)
  syn (T.flatMap op f s)  = suc (syn s)
  syn (T.connect s b)     = suc (syn s + syn b)
  syn (T.connected i)     = 1
  syn (T.defer l)         = 1

  -- Every operator reached owes at least itself.
  syn-pos : ∀ {Δ A} (s : Obs Timeline Δ A) → 0 < syn s
  syn-pos (T.cold c)          = s≤s z≤n
  syn-pos T.empty             = s≤s z≤n
  syn-pos (T.of xs)           = s≤s z≤n
  syn-pos (T.map f s)         = s≤s z≤n
  syn-pos (T.scan f z s)      = s≤s z≤n
  syn-pos (T.takeWhile i q s) = s≤s z≤n
  syn-pos (T.flatMap op f s)  = s≤s z≤n
  syn-pos (T.connect s b)     = s≤s z≤n
  syn-pos (T.connected i)     = s≤s z≤n
  syn-pos (T.defer l)         = s≤s z≤n

  mutual
    pend : ∀ {h Δ A} → Sub h Δ A → ℕ
    pend (pendingˢ s q)                    = syn s
    pend (coldˢ _ _ _)                     = 0
    pend (ofˢ _ _ _)                       = 0
    pend doneˢ                             = 0
    pend (mapˢ f s)                        = pend s
    pend (scanˢ f r s)                     = pend s
    pend (takeWhileˢ i q c k tk s)         = pend s
    pend (flatMapˢ op f fl oc k r pl s ls)    = pend s + pendᴸ ls
    pend (connectˢ S c b kb k fd rp e rt src bd) = pend src + pend bd
    pend (joinˢ _ _ _ _ _)                 = 0
    pend (deferˢ k s)                      = pend s

    pendᴸ : ∀ {h Δ B} → List (Lane h Δ B) → ℕ
    pendᴸ []                = 0
    pendᴸ (lane c k s ∷ ls) = pend s + pendᴸ ls

  -- What each takeWhile has still to do: fail, then complete.
  stage : ∀ {Δ A} → Taking Δ A → ℕ
  stage taking     = 2
  stage (ending _ _) = 1
  stage taken      = 0

  mutual
    takes : ∀ {h Δ A} → Sub h Δ A → ℕ
    takes (pendingˢ s q)                    = 0
    takes (coldˢ _ _ _)                     = 0
    takes (ofˢ _ _ _)                       = 0
    takes doneˢ                             = 0
    takes (mapˢ f s)                        = takes s
    takes (scanˢ f r s)                     = takes s
    takes (takeWhileˢ i q c k tk s)         = stage tk + takes s
    takes (flatMapˢ op f fl oc k r pl s ls)    = takes s + takesᴸ ls
    takes (connectˢ S c b kb k fd rp e rt src bd) = takes src + takes bd
    takes (joinˢ _ _ _ _ _)                 = 0
    takes (deferˢ k s)                      = takes s

    takesᴸ : ∀ {h Δ B} → List (Lane h Δ B) → ℕ
    takesᴸ []                = 0
    takesᴸ (lane c k s ∷ ls) = takes s + takesᴸ ls

  ----------------------------------------------------------------------
  -- THE POP: a waiting cold whose timer popped goes `fired`, the same
  -- meaning node with no timer owed.

  -- A frame's timer, and the cold waiting on it.
  data Waits {h Δ₀ A₀} (t : Sub h Δ₀ A₀) : Timer h → Set₁ where
    waits : ∀ {Δ A τ e v u x} {sk : Sink h A} {hd} {fr : Frame A u}
            (π : Path t (coldˢ {Δ = Δ} sk hd (waiting {u = v} τ e (at u x fr))))
          → Waits t (record { due = τ + u ; sink = sk ; handle = hd ; at′ = u ; from = e ; frame = fr })

  rewait : ∀ {h Δ A Δ′ A′} {s : Sub h Δ A} {t : Sub h Δ′ A′} {tm}
         → (∀ {Δ″ A″} {u : Sub h Δ″ A″} → Path s u → Path t u) → Waits s tm → Waits t tm
  rewait f (waits π) = waits (f π)

  -- Every queued pending frame is a waiting cold's.
  mutual
    pendings-path : ∀ {h Δ A} {t : Sub h Δ A} {tm : Timer h} → tm ∈ᴸ pendings t → Waits t tm
    pendings-path {t = coldˢ s hd (waiting τ e (at u x b))} (here refl) = waits here
    pendings-path {t = mapˢ f s} i                        = rewait in-map (pendings-path i)
    pendings-path {t = scanˢ f r s} i                     = rewait in-scan (pendings-path i)
    pendings-path {t = takeWhileˢ i p c k tk s} j         = rewait in-take (pendings-path j)
    pendings-path {t = flatMapˢ op f fl oc k r pl so ls} i with ++⁻ (pendings so) i
    ... | inj₁ j = rewait in-outer (pendings-path j)
    ... | inj₂ j = lanes-path in-lanes j
    pendings-path {t = connectˢ S c b kb k fd rp e rt src bd} i with ++⁻ (pendings src) i
    ... | inj₁ j = rewait in-source (pendings-path j)
    ... | inj₂ j = rewait in-body (pendings-path j)
    pendings-path {t = deferˢ k s} i                      = rewait in-defer (pendings-path i)

    lanes-path : ∀ {h Δ B Δ′ A′} {ls : List (Lane h Δ B)} {t : Sub h Δ′ A′} {tm : Timer h}
               → (∀ {Δ″ A″} {u : Sub h Δ″ A″} → PathLanes ls u → Path t u) → tm ∈ᴸ lanePendings ls → Waits t tm
    lanes-path {ls = lane c k s ∷ ls} f i with ++⁻ (pendings s) i
    ... | inj₁ j = rewait (λ π → f (this-lane π)) (pendings-path j)
    ... | inj₂ j = lanes-path (λ π → f (next-lane π)) j

  -- The queue past its head: each later.
  later : ∀ {h} {tm : Timer h} {ts} → Linked (λ y z → cascade y <ᵖ cascade z ≡ true) (tm ∷ ts)
        → All (λ z → cascade tm <ᵖ cascade z ≡ true) ts
  later [-]                = []
  later {tm = tm} (r ∷ lk) =
    Linked⇒All {R = λ a b → cascade a <ᵖ cascade b ≡ true} (λ {a} {b} {c} → <ᵖ-trans (cascade a) (cascade b) (cascade c)) {v = tm} r lk

  -- A list's middle entry, dropped.
  ∈-drop : ∀ {a} {X : Set a} {z y : X} xs {ys} → z ≢ y → z ∈ᴸ xs ++ y ∷ ys → z ∈ᴸ xs ++ ys
  ∈-drop []       z≢y (here e)  = ⊥-elim (z≢y e)
  ∈-drop []       z≢y (there i) = i
  ∈-drop (_ ∷ xs) z≢y (here e)  = here e
  ∈-drop (_ ∷ xs) z≢y (there i) = there (∈-drop xs z≢y i)

  all-drop : ∀ {a p} {X : Set a} {P : X → Set p} xs {y ys} → All P (xs ++ y ∷ ys) → All P (xs ++ ys)
  all-drop []       (_ ∷ ps) = ps
  all-drop (_ ∷ xs) (p ∷ ps) = p ∷ all-drop xs ps

  all-mid : ∀ {a p} {X : Set a} {P : X → Set p} xs {y ys} → All P (xs ++ y ∷ ys) → P y
  all-mid []       (p ∷ _)  = p
  all-mid (_ ∷ xs) (_ ∷ ps) = all-mid xs ps

  -- Every other entry's handle apart from the middle one's.
  others : ∀ {h} xs {y : Timer h} {ys} → AllPairs (λ a b → Timer.handle a ≢ Timer.handle b) (xs ++ y ∷ ys)
         → All (λ z → Timer.handle z ≢ Timer.handle y) (xs ++ ys)
  others []       (a ∷ _)  = map (λ d e → d (sym e)) a
  others (_ ∷ xs) (a ∷ as) = all-mid xs a ∷ others xs as

  -- One list's middle `m` replaced by `m′`, the rest kept.
  Splice : ∀ {a} {X : Set a} → List X → List X → List X → List X → Set a
  Splice {X = X} p m p′ m′ = Σ (List X) λ xs → Σ (List X) λ ys → p ≡ xs ++ m ++ ys × p′ ≡ xs ++ m′ ++ ys

  spliced-r : ∀ {a} {X : Set a} {p m p′ m′ : List X} L → Splice p m p′ m′ → Splice (p ++ L) m (p′ ++ L) m′
  spliced-r {m = m} {m′ = m′} L (xs , ys , e , e′) = xs , ys ++ L , shift m e , shift m′ e′
    where
      shift : ∀ {q} n → q ≡ xs ++ n ++ ys → q ++ L ≡ xs ++ n ++ ys ++ L
      shift n refl = trans (++-assoc xs (n ++ ys) L) (cong (xs ++_) (++-assoc n ys L))

  spliced-l : ∀ {a} {X : Set a} {p m p′ m′ : List X} P → Splice p m p′ m′ → Splice (P ++ p) m (P ++ p′) m′
  spliced-l {m = m} {m′ = m′} P (xs , ys , e , e′) = P ++ xs , ys , shift m e , shift m′ e′
    where
      shift : ∀ {q} n → q ≡ xs ++ n ++ ys → P ++ q ≡ (P ++ xs) ++ n ++ ys
      shift n refl = sym (++-assoc P xs (n ++ ys))

  -- The queue's frames: the node's own, replaced in place.
  mutual
    pendings-plant : ∀ {h Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (v : Sub h Δ′ A′)
                   → Splice (pendings t) (pendings u) (pendings (plant π v)) (pendings v)
    pendings-plant {u = u} here v = [] , [] , sym (++-identityʳ (pendings u)) , sym (++-identityʳ (pendings v))
    pendings-plant (in-map π) v                    = pendings-plant π v
    pendings-plant (in-scan π) v                   = pendings-plant π v
    pendings-plant (in-take π) v                   = pendings-plant π v
    pendings-plant (in-outer {ls = ls} π) v        = spliced-r (lanePendings ls) (pendings-plant π v)
    pendings-plant (in-lanes {t = so} π) v         = spliced-l (pendings so) (pendings-plantᴸ π v)
    pendings-plant (in-source {bd = bd} π) v       = spliced-r (pendings bd) (pendings-plant π v)
    pendings-plant (in-body {t = src} π) v         = spliced-l (pendings src) (pendings-plant π v)
    pendings-plant (in-defer π) v                  = pendings-plant π v

    pendings-plantᴸ : ∀ {h Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (π : PathLanes ls u) (v : Sub h Δ′ A′)
                    → Splice (lanePendings ls) (pendings u) (lanePendings (plantᴸ π v)) (pendings v)
    pendings-plantᴸ (this-lane {ls = ls} π) v        = spliced-r (lanePendings ls) (pendings-plant π v)
    pendings-plantᴸ (next-lane {l = lane c k s} π) v = spliced-l (pendings s) (pendings-plantᴸ π v)

  -- A list's pairs, split at a join.
  pairs-split : ∀ {a r} {X : Set a} {R : X → X → Set r} xs {ys} → AllPairs R (xs ++ ys)
              → AllPairs R xs × AllPairs R ys × All (λ x → All (R x) ys) xs
  pairs-split []       ps       = [] , ps , []
  pairs-split (x ∷ xs) (a ∷ ps) with pairs-split xs ps | all-++⁻ xs a
  ... | l , r , c | al , ar = al ∷ l , r , ar ∷ c

  pairs-r : ∀ {a r} {X : Set a} {R : X → X → Set r} xs {ys} → AllPairs R (xs ++ ys) → AllPairs R ys
  pairs-r xs ps = proj₁ (proj₂ (pairs-split xs ps))

  -- Frames named apart, handles apart.
  apart : ∀ {h} {xs ys : List (Name h)} {ps qs : List (Timer h)} → All (λ x → All (x ≢_) ys) xs
        → (∀ {a} → a ∈ᴸ ps → (play , Timer.handle a) ∈ᴸ xs) → (∀ {b} → b ∈ᴸ qs → (play , Timer.handle b) ∈ᴸ ys)
        → All (λ a → All (λ b → Timer.handle a ≢ Timer.handle b) qs) ps
  apart c f g = tabulateᴬ λ a∈ → tabulateᴬ λ b∈ eq → lookupᴬ (lookupᴬ c (f a∈)) (g b∈) (cong (play ,_) eq)

  -- A pending frame's handle is its cold's.
  mutual
    pend-named : ∀ {h Δ A} {t : Sub h Δ A} {tm : Timer h} → tm ∈ᴸ pendings t → (play , Timer.handle tm) ∈ᴸ names t
    pend-named {t = coldˢ s hd (waiting τ e (at u x b))} (here refl) = there (here refl)
    pend-named {t = mapˢ f s} i                        = pend-named {t = s} i
    pend-named {t = scanˢ f r s} i                     = there (pend-named {t = s} i)
    pend-named {t = takeWhileˢ i p c k tk s} j         = ++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) (pend-named {t = s} j))
    pend-named {t = flatMapˢ op f fl oc k r pl so ls} i with ++⁻ (pendings so) i
    ... | inj₁ j = ++⁺ʳ (flatNames fl) (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ˡ (pend-named {t = so} j)))))
    ... | inj₂ j = ++⁺ʳ (flatNames fl) (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ʳ (names so) (lane-named {ls = ls} j)))))
    pend-named {t = connectˢ S c b kb k fd rp e rt src bd} i with ++⁻ (pendings src) i
    ... | inj₁ j = ++⁺ʳ (subjectNames S) (++⁺ʳ (cutNames c) (there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ˡ (pend-named {t = src} j))))))
    ... | inj₂ j = ++⁺ʳ (subjectNames S) (++⁺ʳ (cutNames c) (there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ʳ (names src) (pend-named {t = bd} j))))))
    pend-named {t = deferˢ k s} i                      = ++⁺ʳ (quietName k) (pend-named {t = s} i)

    lane-named : ∀ {h Δ B} {ls : List (Lane h Δ B)} {tm : Timer h} → tm ∈ᴸ lanePendings ls → (play , Timer.handle tm) ∈ᴸ laneNames ls
    lane-named {ls = lane c k s ∷ ls} i with ++⁻ (pendings s) i
    ... | inj₁ j = ++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) (++⁺ˡ (pend-named {t = s} j)))
    ... | inj₂ j = ++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) (++⁺ʳ (names s) (lane-named {ls = ls} j)))

  -- Each cold's frame is its own: no two pending frames share a handle.
  mutual
    pendings-fresh : ∀ {h Δ A} {t : Sub h Δ A} → AllPairs _≢_ (names t)
                   → AllPairs (λ a b → Timer.handle a ≢ Timer.handle b) (pendings t)
    pendings-fresh {t = pendingˢ _ _}                              _ = []
    pendings-fresh {t = coldˢ s hd (waiting τ e (at u x b))}       _ = [] ∷ []
    pendings-fresh {t = coldˢ s hd (waiting τ e doneᶠ)}            _ = []
    pendings-fresh {t = coldˢ s hd (waiting τ e quietᶠ)}           _ = []
    pendings-fresh {t = coldˢ s hd (fired _ _ _)}                  _ = []
    pendings-fresh {t = coldˢ s hd (playing _ _ _ _)}              _ = []
    pendings-fresh {t = ofˢ _ _ _}                                 _ = []
    pendings-fresh {t = doneˢ}                                     _ = []
    pendings-fresh {t = mapˢ f s}                                  ps = pendings-fresh {t = s} ps
    pendings-fresh {t = scanˢ f r s}                               (_ ∷ ps) = pendings-fresh {t = s} ps
    pendings-fresh {t = takeWhileˢ i p c k tk s}                   ps =
      pendings-fresh {t = s} (pairs-r (quietName k) (pairs-r (cutNames c) ps))
    pendings-fresh {t = flatMapˢ op f fl oc k r pl so ls}             ps
      with pairs-split (names so) (pairs-r ((slot _ , r) ∷ []) (pairs-r (quietName k) (pairs-r (cutNames oc) (pairs-r (flatNames fl) ps))))
    ... | l , rs , c = pairs-++⁺ (pendings-fresh {t = so} l) (lanes-fresh {ls = ls} rs)
                         (apart c (λ {a} → pend-named {t = so} {tm = a}) (λ {b} → lane-named {ls = ls} {tm = b}))
    pendings-fresh {t = connectˢ S c b kb k fd rp e rt src bd}           ps
      with pairs-split (names src)
             (pairs-r (quietName k) (pairs-r (quietName kb) (pairs-r ((cell _ , b) ∷ []) (pairs-r (cutNames c) (pairs-r (subjectNames S) ps)))))
    ... | l , rs , cr = pairs-++⁺ (pendings-fresh {t = src} l) (pendings-fresh {t = bd} rs)
                          (apart cr (λ {a} → pend-named {t = src} {tm = a}) (λ {b′} → pend-named {t = bd} {tm = b′}))
    pendings-fresh {t = joinˢ _ _ _ _ _}                           _ = []
    pendings-fresh {t = deferˢ k s}                                ps = pendings-fresh {t = s} (pairs-r (quietName k) ps)

    lanes-fresh : ∀ {h Δ B} {ls : List (Lane h Δ B)} → AllPairs _≢_ (laneNames ls)
                → AllPairs (λ a b → Timer.handle a ≢ Timer.handle b) (lanePendings ls)
    lanes-fresh {ls = []}             _ = []
    lanes-fresh {ls = lane c k s ∷ ls} ps with pairs-split (names s) (pairs-r (quietName k) (pairs-r (cutNames c) ps))
    ... | l , rs , cr = pairs-++⁺ (pendings-fresh {t = s} l) (lanes-fresh {ls = ls} rs)
                          (apart cr (λ {a} → pend-named {t = s} {tm = a}) (λ {b} → lane-named {ls = ls} {tm = b}))

  -- The fired cold's frame leaves the queue with its timer: the queue's
  -- others are later, so not it, and the pending frames' others not
  -- its cold's.
  timed-pop : ∀ {h} (H : Heapᴹ h) {t : Sub h [] R} {ts} {Δ A τ e v u x} {sk : Sink h A} {hd} {fr : Frame A u}
              (π : Path t (coldˢ {Δ = Δ} sk hd (waiting {u = v} τ e (at u x fr))))
            → At.Timed H (record { due = τ + u ; sink = sk ; handle = hd ; at′ = u ; from = e ; frame = fr } ∷ ts) (pendings t)
            → Linked (λ y z → cascade y <ᵖ cascade z ≡ true)
                (record { due = τ + u ; sink = sk ; handle = hd ; at′ = u ; from = e ; frame = fr } ∷ ts)
            → AllPairs _≢_ (names t)
            → At.Timed H ts (pendings (plant π (coldˢ sk hd (fired τ e (at u x fr)))))
  timed-pop H {t = t} {ts = ts} {τ = τ} {e = e} {u = u} {x = x} {sk = sk} {hd = hd} {fr = fr} π (_ ∷ as , bs) lk fs
    with pendings-plant π (coldˢ sk hd (fired τ e (at u x fr)))
  ... | xs , ys , e₀ , e₁ =
    queued (later lk) as
    , subst (All _) (sym e₁) (owed (all-drop xs (subst (All _) e₀ bs)) (others xs (subst (AllPairs _) e₀ (pendings-fresh {t = t} fs))))
    where
      tm : Timer _
      tm = record { due = τ + u ; sink = sk ; handle = hd ; at′ = u ; from = e ; frame = fr }

      queued : ∀ {zs} → All (λ z → cascade tm <ᵖ cascade z ≡ true) zs
             → All (λ z → At.spentʰ H (Timer.handle z) ≡ true ⊎ z ∈ᴸ pendings t) zs
             → All (λ z → At.spentʰ H (Timer.handle z) ≡ true ⊎ z ∈ᴸ pendings (plant π (coldˢ sk hd (fired τ e (at u x fr))))) zs
      queued []       []            = []
      queued (c ∷ cs) (inj₁ d ∷ qs) = inj₁ d ∷ queued cs qs
      queued (c ∷ cs) (inj₂ i ∷ qs) =
        inj₂ (subst (_ ∈ᴸ_) (sym e₁) (∈-drop xs (λ eq → true≢false (trans (sym (subst (λ z → cascade tm <ᵖ cascade z ≡ true) eq c)) (<ᵖ-irrefl (cascade tm))))
                                         (subst (_ ∈ᴸ_) e₀ i)))
        ∷ queued cs qs

      owed : ∀ {zs} → All (λ z → At.spentʰ H (Timer.handle z) ≡ false → z ∈ᴸ tm ∷ ts) zs → All (λ z → Timer.handle z ≢ hd) zs
           → All (λ z → At.spentʰ H (Timer.handle z) ≡ false → z ∈ᴸ ts) zs
      owed []       []       = []
      owed (f ∷ fs′) (d ∷ ds) = keep f d ∷ owed fs′ ds
        where
          keep : ∀ {z} → (At.spentʰ H (Timer.handle z) ≡ false → z ∈ᴸ tm ∷ ts) → Timer.handle z ≢ hd
               → At.spentʰ H (Timer.handle z) ≡ false → z ∈ᴸ ts
          keep f′ d′ nsp with f′ nsp
          ... | here eq = ⊥-elim (d′ (cong Timer.handle eq))
          ... | there i = i

  ----------------------------------------------------------------------
  -- A path in the rewritten tree, back in the old one.

  -- Two nodes alike but for their children.
  data Same {h} : ∀ {Δ A} → Sub h Δ A → Sub h Δ A → Set₁ where
    same         : ∀ {Δ A} {s : Sub h Δ A} → Same s s
    same-map     : ∀ {Δ A B} {f : A → B} {s s′ : Sub h Δ A} → Same (mapˢ f s) (mapˢ f s′)
    same-scan    : ∀ {Δ A B} {f : B → A → B} {r} {s s′ : Sub h Δ A} → Same (scanˢ f r s) (scanˢ f r s′)
    same-take    : ∀ {Δ A} {i p c k tk} {s s′ : Sub h Δ A} → Same (takeWhileˢ i p c k tk s) (takeWhileˢ i p c k tk s′)
    same-flat    : ∀ {Δ A B} {op f fl oc k r pl} {s s′ : Sub h Δ A} {ls ls′ : List (Lane h Δ B)}
                 → Same (flatMapˢ op f fl oc k r pl s ls) (flatMapˢ op f fl oc k r pl s′ ls′)
    same-connect : ∀ {Δ A B} {S c b kb k fd e rp rt} {s s′ : Sub h Δ A} {bd bd′ : Sub h (A ∷ Δ) B}
                 → Same (connectˢ S c b kb k fd rp e rt s bd) (connectˢ S c b kb k fd rp e rt s′ bd′)
    same-defer   : ∀ {Δ A} {k} {s s′ : Sub h Δ A} → Same (deferˢ k s) (deferˢ k s′)

  -- A node of the rewritten tree: at or below the planted node, or one
  -- of the old tree's but for its children.
  Unplanted : ∀ {h Δ A Δ′ A′ Δ″ A″} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (v : Sub h Δ′ A′) {w : Sub h Δ″ A″}
            → Path (plant π v) w → Set₁
  Unplanted {t = t} π v {w} π′ = (Σ (Path v w) λ ρ → π′ ≡ planted π v ⊕ ρ) ⊎ (Σ _ λ w₀ → Path t w₀ × Same w₀ w)

  UnplantedL : ∀ {h Δ B Δ′ A′ Δ″ A″} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (π : PathLanes ls u) (v : Sub h Δ′ A′) {w : Sub h Δ″ A″}
             → PathLanes (plantᴸ π v) w → Set₁
  UnplantedL {ls = ls} π v {w} π′ = (Σ (Path v w) λ ρ → π′ ≡ plantedᴸ π v ⊕ᴸ ρ) ⊎ (Σ _ λ w₀ → PathLanes ls w₀ × Same w₀ w)

  mutual
    unplant : ∀ {h Δ A Δ′ A′ Δ″ A″} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (v : Sub h Δ′ A′) {w : Sub h Δ″ A″}
              (π′ : Path (plant π v) w) → Unplanted π v π′
    unplant here v π′ = inj₁ (π′ , refl)
    unplant (in-map π) v here = inj₂ (_ , here , same-map)
    unplant (in-map π) v (in-map π′) with unplant π v π′
    ... | inj₁ (ρ , eq)       = inj₁ (ρ , cong in-map eq)
    ... | inj₂ (_ , q , sm)   = inj₂ (_ , in-map q , sm)
    unplant (in-scan π) v here = inj₂ (_ , here , same-scan)
    unplant (in-scan π) v (in-scan π′) with unplant π v π′
    ... | inj₁ (ρ , eq)       = inj₁ (ρ , cong in-scan eq)
    ... | inj₂ (_ , q , sm)   = inj₂ (_ , in-scan q , sm)
    unplant (in-take π) v here = inj₂ (_ , here , same-take)
    unplant (in-take π) v (in-take π′) with unplant π v π′
    ... | inj₁ (ρ , eq)       = inj₁ (ρ , cong in-take eq)
    ... | inj₂ (_ , q , sm)   = inj₂ (_ , in-take q , sm)
    unplant (in-outer π) v here = inj₂ (_ , here , same-flat)
    unplant (in-outer π) v (in-outer π′) with unplant π v π′
    ... | inj₁ (ρ , eq)       = inj₁ (ρ , cong in-outer eq)
    ... | inj₂ (_ , q , sm)   = inj₂ (_ , in-outer q , sm)
    unplant (in-outer π) v (in-lanes π′) = inj₂ (_ , in-lanes π′ , same)
    unplant (in-lanes π) v here = inj₂ (_ , here , same-flat)
    unplant (in-lanes π) v (in-outer π′) = inj₂ (_ , in-outer π′ , same)
    unplant (in-lanes π) v (in-lanes π′) with unplantᴸ π v π′
    ... | inj₁ (ρ , eq)       = inj₁ (ρ , cong in-lanes eq)
    ... | inj₂ (_ , q , sm)   = inj₂ (_ , in-lanes q , sm)
    unplant (in-source π) v here = inj₂ (_ , here , same-connect)
    unplant (in-source π) v (in-source π′) with unplant π v π′
    ... | inj₁ (ρ , eq)       = inj₁ (ρ , cong in-source eq)
    ... | inj₂ (_ , q , sm)   = inj₂ (_ , in-source q , sm)
    unplant (in-source π) v (in-body π′) = inj₂ (_ , in-body π′ , same)
    unplant (in-body π) v here = inj₂ (_ , here , same-connect)
    unplant (in-body π) v (in-source π′) = inj₂ (_ , in-source π′ , same)
    unplant (in-body π) v (in-body π′) with unplant π v π′
    ... | inj₁ (ρ , eq)       = inj₁ (ρ , cong in-body eq)
    ... | inj₂ (_ , q , sm)   = inj₂ (_ , in-body q , sm)
    unplant (in-defer π) v here = inj₂ (_ , here , same-defer)
    unplant (in-defer π) v (in-defer π′) with unplant π v π′
    ... | inj₁ (ρ , eq)       = inj₁ (ρ , cong in-defer eq)
    ... | inj₂ (_ , q , sm)   = inj₂ (_ , in-defer q , sm)

    unplantᴸ : ∀ {h Δ B Δ′ A′ Δ″ A″} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (π : PathLanes ls u) (v : Sub h Δ′ A′)
               {w : Sub h Δ″ A″} (π′ : PathLanes (plantᴸ π v) w) → UnplantedL π v π′
    unplantᴸ (this-lane π) v (this-lane π′) with unplant π v π′
    ... | inj₁ (ρ , eq)       = inj₁ (ρ , cong this-lane eq)
    ... | inj₂ (_ , q , sm)   = inj₂ (_ , this-lane q , sm)
    unplantᴸ (this-lane π) v (next-lane π′) = inj₂ (_ , next-lane π′ , same)
    unplantᴸ (next-lane π) v (this-lane π′) = inj₂ (_ , this-lane π′ , same)
    unplantᴸ (next-lane π) v (next-lane π′) with unplantᴸ π v π′
    ... | inj₁ (ρ , eq)       = inj₁ (ρ , cong next-lane eq)
    ... | inj₂ (_ , q , sm)   = inj₂ (_ , next-lane q , sm)

  -- Nothing owed at the turn, and the popped cold now fired: owed only
  -- its burst.  Every other node the rewritten tree holds is the old
  -- tree's, which owed nothing.
  owned-pop : ∀ {h} (H : Heapᴹ h) {t : Sub h [] R} {p w} {σ : w ⊑ h} {Δ A τ e v u x} {sk : Sink h A} {hd} {fr : Frame A u}
              (π : Path t (coldˢ {Δ = Δ} sk hd (waiting {u = v} τ e (at u x fr))))
            → Owned H t (Against.calmAs {p = p} {σ = σ})
            → Owned H (plant π (coldˢ sk hd (fired τ e (at u x fr))))
                (Against.burstAs {p = p} {σ = σ} (Against.firesAs (planted π _)) Against.bottomᴴ Against.bottomAs)
  owned-pop {h} H {τ = τ} {e = e} {u = u} {x = x} {sk = sk} {hd = hd} {fr = fr} π ow = record
    { ofs    = λ π′ → ⊥-elim (no-of π′)
    ; plays  = λ π′ nsp → ⊥-elim (no-play π′ nsp)
    ; fires  = fires′
    ; begun  = λ π′ → ⊥-elim (no-pending π′)
    ; ends   = λ π′ l → ⊥-elim (no-end π′ l)
    ; cuts   = λ π′ l → ⊥-elim (no-cut π′ l)
    ; feeds  = λ π′ → ⊥-elim (no-feed π′)
    ; fins   = λ π′ → ⊥-elim (no-fin π′)
    ; bodies = λ π′ ()
    ; placed = [] }
    where
      fc = coldˢ sk hd (fired τ e (at u x fr))

      gone : ∀ {a} {X : Set a} {y : X} → y ∈ᴸ [] → ⊥
      gone ()

      no-of : ∀ {Δ′ A′ q i xs} → Path (plant π fc) (ofˢ {Δ = Δ′} {A′} q i xs) → ⊥
      no-of π′ with unplant π fc π′
      ... | inj₁ (() , _)
      ... | inj₂ (_ , q , same) = gone (Owned.ofs ow q)

      no-play : ∀ {Δ′ A′ s hd′ τ′ r i u′} {b : Frame A′ u′} → Path (plant π fc) (coldˢ {Δ = Δ′} s hd′ (playing τ′ r i b))
              → At.spentʰ H hd′ ≡ false → ⊥
      no-play π′ nsp with unplant π fc π′
      ... | inj₁ (() , _)
      ... | inj₂ (_ , q , same) = gone (Owned.plays ow q nsp)

      fires′ : ∀ {Δ′ A′ s hd′ τ′ e′ u′} {m : From A′ u′} (π′ : Path (plant π fc) (coldˢ {Δ = Δ′} s hd′ (fired τ′ e′ m)))
             → At.spentʰ H hd′ ≡ false → spot π′ ∈ᴸ spot (planted π fc) ∷ []
      fires′ π′ nsp with unplant π fc π′
      ... | inj₁ (here , eq)    = here (cong spot (trans eq (⊕-here (planted π fc))))
      ... | inj₂ (_ , q , same) = ⊥-elim (gone (Owned.fires ow q nsp))

      no-pending : ∀ {Δ′ A′ s q} → Path (plant π fc) (pendingˢ {Δ = Δ′} {A′} s q) → ⊥
      no-pending π′ with unplant π fc π′
      ... | inj₁ (() , _)
      ... | inj₂ (_ , q , same) = gone (Owned.begun ow q)

      no-end : ∀ {Δ′ A′ i p c k q n} {s : Sub h Δ′ A′} → Path (plant π fc) (takeWhileˢ i p c k (ending q n) s) → At.val H (Kit.live c) ≡ true → ⊥
      no-end π′ l with unplant π fc π′
      ... | inj₁ (() , _)
      ... | inj₂ (_ , q , same)      = gone (Owned.ends ow q l)
      ... | inj₂ (_ , q , same-take) = gone (Owned.ends ow q l)

      no-cut : ∀ {Δ′ A′ i p c k} {s : Sub h Δ′ A′} → Path (plant π fc) (takeWhileˢ i p c k taken s) → At.val H (Kit.live c) ≡ true → ⊥
      no-cut π′ l with unplant π fc π′
      ... | inj₁ (() , _)
      ... | inj₂ (_ , q , same)      = gone (proj₂ (Owned.cuts ow q l))
      ... | inj₂ (_ , q , same-take) = gone (proj₂ (Owned.cuts ow q l))

      no-feed : ∀ {Δ′ A B S c b kb k x q ss e′ rp rt} {s : Sub h Δ′ A} {bd : Sub h (A ∷ Δ′) B}
              → Path (plant π fc) (connectˢ S c b kb k (feeding x q ss) rp e′ rt s bd) → ⊥
      no-feed π′ with unplant π fc π′
      ... | inj₁ (() , _)
      ... | inj₂ (_ , q , same)         = gone (Owned.feeds ow q)
      ... | inj₂ (_ , q , same-connect) = gone (Owned.feeds ow q)

      no-fin : ∀ {Δ′ A B S c b kb k q ss e′ rp rt} {s : Sub h Δ′ A} {bd : Sub h (A ∷ Δ′) B}
             → Path (plant π fc) (connectˢ S c b kb k (finishing q ss) rp e′ rt s bd) → ⊥
      no-fin π′ with unplant π fc π′
      ... | inj₁ (() , _)
      ... | inj₂ (_ , q , same)         = gone (Owned.fins ow q)
      ... | inj₂ (_ , q , same-connect) = gone (Owned.fins ow q)

  ----------------------------------------------------------------------
  -- What a node rewritten keeps, each part of the relation from the
  -- same part of the node.

  mutual
    part-plant : ∀ {h} (H : Heapᴹ h) {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (v : Sub h Δ′ A′)
               → At.part H u ≡ At.part H v → At.part H (plant π v) ≡ At.part H t
    part-plant H here v eq          = sym eq
    part-plant H (in-map π) v eq    rewrite part-plant H π v eq = refl
    part-plant H (in-scan π) v eq   rewrite part-plant H π v eq = refl
    part-plant H (in-take π) v eq   rewrite part-plant H π v eq = refl
    part-plant H (in-outer π) v eq  rewrite part-plant H π v eq = refl
    part-plant H (in-lanes π) v eq  rewrite part-plantᴸ H π v eq = refl
    part-plant H (in-source π) v eq rewrite part-plant H π v eq = refl
    part-plant H (in-body π) v eq   rewrite part-plant H π v eq = refl
    part-plant H (in-defer π) v eq  = part-plant H π v eq

    part-plantᴸ : ∀ {h} (H : Heapᴹ h) {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (π : PathLanes ls u) (v : Sub h Δ′ A′)
                → At.part H u ≡ At.part H v → At.partLanes H (plantᴸ π v) ≡ At.partLanes H ls
    part-plantᴸ H (this-lane π) v eq                rewrite part-plant H π v eq = refl
    part-plantᴸ H (next-lane {l = lane c k s} π) v eq rewrite part-plantᴸ H π v eq = refl

  mutual
    pend-plant : ∀ {h Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (v : Sub h Δ′ A′)
               → pend u ≡ pend v → pend (plant π v) ≡ pend t
    pend-plant here v eq          = sym eq
    pend-plant (in-map π) v eq    = pend-plant π v eq
    pend-plant (in-scan π) v eq   = pend-plant π v eq
    pend-plant (in-take π) v eq   = pend-plant π v eq
    pend-plant (in-outer π) v eq  rewrite pend-plant π v eq = refl
    pend-plant (in-lanes π) v eq  rewrite pend-plantᴸ π v eq = refl
    pend-plant (in-source π) v eq rewrite pend-plant π v eq = refl
    pend-plant (in-body π) v eq   rewrite pend-plant π v eq = refl
    pend-plant (in-defer π) v eq  = pend-plant π v eq

    pend-plantᴸ : ∀ {h Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (π : PathLanes ls u) (v : Sub h Δ′ A′)
                → pend u ≡ pend v → pendᴸ (plantᴸ π v) ≡ pendᴸ ls
    pend-plantᴸ (this-lane π) v eq                rewrite pend-plant π v eq = refl
    pend-plantᴸ (next-lane {l = lane c k s} π) v eq rewrite pend-plantᴸ π v eq = refl

  mutual
    takes-plant : ∀ {h Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (v : Sub h Δ′ A′)
                → takes u ≡ takes v → takes (plant π v) ≡ takes t
    takes-plant here v eq          = sym eq
    takes-plant (in-map π) v eq    = takes-plant π v eq
    takes-plant (in-scan π) v eq   = takes-plant π v eq
    takes-plant (in-take π) v eq   rewrite takes-plant π v eq = refl
    takes-plant (in-outer π) v eq  rewrite takes-plant π v eq = refl
    takes-plant (in-lanes π) v eq  rewrite takes-plantᴸ π v eq = refl
    takes-plant (in-source π) v eq rewrite takes-plant π v eq = refl
    takes-plant (in-body π) v eq   rewrite takes-plant π v eq = refl
    takes-plant (in-defer π) v eq  = takes-plant π v eq

    takes-plantᴸ : ∀ {h Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (π : PathLanes ls u) (v : Sub h Δ′ A′)
                 → takes u ≡ takes v → takesᴸ (plantᴸ π v) ≡ takesᴸ ls
    takes-plantᴸ (this-lane π) v eq                rewrite takes-plant π v eq = refl
    takes-plantᴸ (next-lane {l = lane c k s} π) v eq rewrite takes-plantᴸ π v eq = refl

  mutual
    names-plant : ∀ {h Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (v : Sub h Δ′ A′)
                → names u ≡ names v → names (plant π v) ≡ names t
    names-plant here v eq          = sym eq
    names-plant (in-map π) v eq    = names-plant π v eq
    names-plant (in-scan π) v eq   rewrite names-plant π v eq = refl
    names-plant (in-take π) v eq   rewrite names-plant π v eq = refl
    names-plant (in-outer π) v eq  rewrite names-plant π v eq = refl
    names-plant (in-lanes π) v eq  rewrite names-plantᴸ π v eq = refl
    names-plant (in-source π) v eq rewrite names-plant π v eq = refl
    names-plant (in-body π) v eq   rewrite names-plant π v eq = refl
    names-plant (in-defer π) v eq  rewrite names-plant π v eq = refl

    names-plantᴸ : ∀ {h Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (π : PathLanes ls u) (v : Sub h Δ′ A′)
                 → names u ≡ names v → laneNames (plantᴸ π v) ≡ laneNames ls
    names-plantᴸ (this-lane π) v eq                rewrite names-plant π v eq = refl
    names-plantᴸ (next-lane {l = lane c k s} π) v eq rewrite names-plantᴸ π v eq = refl

  mutual
    subjects-plant : ∀ {h Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (v : Sub h Δ′ A′)
                   → subjects u ≡ subjects v → subjects (plant π v) ≡ subjects t
    subjects-plant here v eq          = sym eq
    subjects-plant (in-map π) v eq    = subjects-plant π v eq
    subjects-plant (in-scan π) v eq   = subjects-plant π v eq
    subjects-plant (in-take π) v eq   = subjects-plant π v eq
    subjects-plant (in-outer π) v eq  rewrite subjects-plant π v eq = refl
    subjects-plant (in-lanes π) v eq  rewrite subjects-plantᴸ π v eq = refl
    subjects-plant (in-source π) v eq rewrite subjects-plant π v eq = refl
    subjects-plant (in-body π) v eq   rewrite subjects-plant π v eq = refl
    subjects-plant (in-defer π) v eq  = subjects-plant π v eq

    subjects-plantᴸ : ∀ {h Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (π : PathLanes ls u) (v : Sub h Δ′ A′)
                    → subjects u ≡ subjects v → laneSubjects (plantᴸ π v) ≡ laneSubjects ls
    subjects-plantᴸ (this-lane π) v eq                rewrite subjects-plant π v eq = refl
    subjects-plantᴸ (next-lane {l = lane c k s} π) v eq rewrite subjects-plantᴸ π v eq = refl

  mutual
    joiners-plant : ∀ {h Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (v : Sub h Δ′ A′)
                  → (∀ E → joiners u E ≡ joiners v E) → ∀ E → joiners (plant π v) E ≡ joiners t E
    joiners-plant here v eq E                      = sym (eq E)
    joiners-plant (in-map π) v eq E                = joiners-plant π v eq E
    joiners-plant (in-scan π) v eq E               = joiners-plant π v eq E
    joiners-plant (in-take π) v eq E               = joiners-plant π v eq E
    joiners-plant (in-outer π) v eq E              rewrite joiners-plant π v eq E = refl
    joiners-plant (in-lanes π) v eq E              rewrite joiners-plantᴸ π v eq E = refl
    joiners-plant (in-source π) v eq E             rewrite joiners-plant π v eq E = refl
    joiners-plant (in-body {S = S} π) v eq E       rewrite joiners-plant π v eq (S ∷ E) = refl
    joiners-plant (in-defer π) v eq E              = joiners-plant π v eq E

    joiners-plantᴸ : ∀ {h Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (π : PathLanes ls u) (v : Sub h Δ′ A′)
                   → (∀ E → joiners u E ≡ joiners v E) → ∀ E → laneJoiners (plantᴸ π v) E ≡ laneJoiners ls E
    joiners-plantᴸ (this-lane π) v eq E                rewrite joiners-plant π v eq E = refl
    joiners-plantᴸ (next-lane {l = lane c k s} π) v eq E rewrite joiners-plantᴸ π v eq E = refl

  -- A lane's switch is kept: the live count and the switches.
  count-plant : ∀ {h} (H : Heapᴹ h) {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (π : PathLanes ls u) (v : Sub h Δ′ A′)
              → At.count H (plantᴸ π v) ≡ At.count H ls
  count-plant H (this-lane π) v                = refl
  count-plant H (next-lane {l = lane c k s} π) v rewrite count-plant H π v = refl

  switches-plant : ∀ {h} (H : Heapᴹ h) {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (π : PathLanes ls u) (v : Sub h Δ′ A′)
                 → At.switches H (plantᴸ π v) ≡ At.switches H ls
  switches-plant H (this-lane π) v                = refl
  switches-plant H (next-lane {l = lane c k s} π) v = cong (c ∷_) (switches-plant H π v)

  -- A path planted with the node it ends at is the tree.
  mutual
    plant-self : ∀ {h Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) → plant π u ≡ t
    plant-self here          = refl
    plant-self (in-map π)    rewrite plant-self π = refl
    plant-self (in-scan π)   rewrite plant-self π = refl
    plant-self (in-take π)   rewrite plant-self π = refl
    plant-self (in-outer π)  rewrite plant-self π = refl
    plant-self (in-lanes π)  rewrite plantᴸ-self π = refl
    plant-self (in-source π) rewrite plant-self π = refl
    plant-self (in-body π)   rewrite plant-self π = refl
    plant-self (in-defer π)  rewrite plant-self π = refl

    plantᴸ-self : ∀ {h Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (π : PathLanes ls u) → plantᴸ π u ≡ ls
    plantᴸ-self (this-lane π) rewrite plant-self π = refl
    plantᴸ-self (next-lane π) rewrite plantᴸ-self π = refl

  -- What unsubscribing does above a node still owed: as it was, or the
  -- whole still owes.
  unsub-owed : ∀ {h Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (v : Sub h Δ′ A′)
             → Owes u → unsub (plant π v) ≡ unsub t ⊎ Owes t
  unsub-owed here v ow         = inj₂ ow
  unsub-owed (in-map π) v ow   = unsub-owed π v ow
  unsub-owed (in-scan π) v ow  = unsub-owed π v ow
  unsub-owed (in-take π) v ow  = inj₁ refl
  unsub-owed (in-outer π) v ow = inj₁ refl
  unsub-owed (in-lanes π) v ow = inj₁ refl
  unsub-owed (in-source π) v ow with unsub-owed π v ow
  ... | inj₁ e rewrite e = inj₁ refl
  ... | inj₂ ow′ = inj₂ ow′
  unsub-owed (in-body π) v ow  = inj₁ refl
  unsub-owed (in-defer π) v ow = inj₁ refl

  -- A detacher is held only over what is begun, so it reads alike.
  attached-owed : ∀ {h} (H : Heapᴹ h) {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (v : Sub h Δ′ A′)
                → Owes u → ∀ c k → Begun k t → At.Attached H c k (unsub t) → At.Attached H c k (unsub (plant π v))
  attached-owed H π v ow c nothing b ak = ak
  attached-owed H π v ow c (just q) b ak with unsub-owed π v ow
  ... | inj₁ e   = subst (At.Attached H c (just q)) (sym e) ak
  ... | inj₂ ow′ = ⊥-elim (b ow′)

  stashed-owed : ∀ {h} (H : Heapᴹ h) {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (v : Sub h Δ′ A′)
               → Owes u → ∀ k → Begun k t → At.Stashed H k (unsub t) → At.Stashed H k (unsub (plant π v))
  stashed-owed H π v ow nothing b sk = sk
  stashed-owed H π v ow (just q) b sk with unsub-owed π v ow
  ... | inj₁ e   = subst (At.Stashed H (just q)) (sym e) sk
  ... | inj₂ ow′ = ⊥-elim (b ow′)

  -- A node still owed, rewritten to one whose unsubscribe differs: no
  -- detacher above reads the difference.
  mutual
    holds-owed : ∀ {h} (H : Heapᴹ h) {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (v : Sub h Δ′ A′)
               → Owes u → ∀ {E o} (k : Kont h)
               → (At.Holds H u (Here.env (walk π (ctx o k E))) (Here.obs (walk π (ctx o k E)))
                  → At.Holds H v (Here.env (walk π (ctx o k E))) (Here.obs (walk π (ctx o k E))))
               → Settled t → At.Holds H t E o → At.Holds H (plant π v) E o
    holds-owed H here v ow k hv st hs = hv hs
    holds-owed H (in-map π) v ow k hv st hs = holds-owed H π v ow k hv st hs
    holds-owed H (in-scan π) v ow k hv st hs = holds-owed H π v ow k hv st hs
    holds-owed H (in-take {c = c} {k = kc} π) v ow k hv (b , st) (ak , hs) =
      attached-owed H π v ow c kc b ak , holds-owed H π v ow _ hv st hs
    holds-owed H (in-outer {oc = oc} {k = kc} π) v ow k hv (b , st , _) (rf , sl , ak , hs , ac , gn , hl) =
      rf , sl , attached-owed H π v ow oc kc b ak , holds-owed H π v ow _ hv st hs , ac , gn , hl
    holds-owed H (in-lanes {op = op} {f = f} {fl = fl} π) v ow {E} {o} k hv (_ , _ , st) (rf , sl , ak , hs , ac , (g , ge , ga) , hl) =
      rf , sl , ak , hs , trans ac (sym (count-plant H π v)) , (g , trans ge (sym (switches-plant H π v)) , ga)
      , holds-owedᴸ H π v ow {op = op} {f = f} {E = E} {o = o} {fl = fl} k hv st hl
    holds-owed H (in-source {c = c} {k = kc} π) v ow k hv (b , _ , st , _) (ak , be , sb , hs , hb) =
      attached-owed H π v ow c kc b ak , be , sb , holds-owed H π v ow _ hv st hs , hb
    holds-owed H (in-body {kb = kb} π) v ow k hv (_ , bb , _ , st) (ak , be , sb , hs , hb) =
      ak , be , stashed-owed H π v ow kb bb sb , hs , holds-owed H π v ow _ hv st hb
    holds-owed H (in-defer {k = kc} π) v ow k hv (b , st) (sb , hs) =
      stashed-owed H π v ow kc b sb , holds-owed H π v ow _ hv st hs

    holds-owedᴸ : ∀ {h} (H : Heapᴹ h) {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (π : PathLanes ls u) (v : Sub h Δ′ A′)
                → Owes u → ∀ {A : Set} {op} {f : A → Obs Timeline Δ B} {E o fl} (k : Kont h)
                → (At.Holds H u (Here.env (walkLanes op f fl (ctx o k E) π)) (Here.obs (walkLanes op f fl (ctx o k E) π))
                   → At.Holds H v (Here.env (walkLanes op f fl (ctx o k E) π)) (Here.obs (walkLanes op f fl (ctx o k E) π)))
                → SettledLanes ls → At.HoldsLanes H op f E o fl ls → At.HoldsLanes H op f E o fl (plantᴸ π v)
    holds-owedᴸ H (this-lane {c = c} {k = kc} π) v ow k hv (b , st , _) (ak , hs , hl) =
      attached-owed H π v ow c kc b ak , holds-owed H π v ow _ hv st hs , hl
    holds-owedᴸ H (next-lane {l = lane c kc s} π) v ow {op = op} {f = f} {E = E} {o = o} {fl = fl} k hv (_ , _ , st) (ak , hs , hl) =
      ak , hs , holds-owedᴸ H π v ow {op = op} {f = f} {E = E} {o = o} {fl = fl} k hv st hl

  mutual
    fed-plant : ∀ {h} (H : Heapᴹ h) {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (v : Sub h Δ′ A′)
              → (∀ ν → At.Fed H u ν → At.Fed H v ν) → ∀ ν → At.Fed H t ν → At.Fed H (plant π v) ν
    fed-plant H here v fv ν f                             = fv ν f
    fed-plant H (in-map π) v fv ν f                       = fed-plant H π v fv ν f
    fed-plant H (in-scan π) v fv ν f                      = fed-plant H π v fv ν f
    fed-plant H (in-take π) v fv ν f                      = fed-plant H π v fv ν f
    fed-plant H (in-outer π) v fv ν (f , fl)              = fed-plant H π v fv ν f , fl
    fed-plant H (in-lanes π) v fv ν (f , fl)              = f , fed-plantᴸ H π v fv ν fl
    fed-plant H (in-source π) v fv ν (f , fb)             = fed-plant H π v fv ν f , fb
    fed-plant H (in-body {fd = fd} {e = e} π) v fv ν (f , fb) = f , fed-plant H π v fv ((fd , e) ∷ ν) fb
    fed-plant H (in-defer π) v fv ν f                     = fed-plant H π v fv ν f

    fed-plantᴸ : ∀ {h} (H : Heapᴹ h) {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (π : PathLanes ls u) (v : Sub h Δ′ A′)
               → (∀ ν → At.Fed H u ν → At.Fed H v ν) → ∀ ν → At.FedLanes H ls ν → At.FedLanes H (plantᴸ π v) ν
    fed-plantᴸ H (this-lane π) v fv ν (f , fl)                = fed-plant H π v fv ν f , fl
    fed-plantᴸ H (next-lane {l = lane c k s} π) v fv ν (f , fl) = f , fed-plantᴸ H π v fv ν fl

  -- A map's or a scan's step heads where its source's does.
  head-map : ∀ {Γ A B} (g : A → B) (s : U.Step Γ A) → U.headˢ (U.mapˢ g s) ≡ U.headˢ s
  head-map g (U.outˢ k a c) = refl
  head-map g (U.skipˢ k c)  = refl
  head-map g (U.endˢ k)     = refl
  head-map g U.hushˢ        = refl

  head-scan : ∀ {Γ A B} (g : B → A → B) z (s : U.Step Γ A) → U.headˢ (U.scanˢ g z s) ≡ U.headˢ s
  head-scan g z (U.outˢ k a c) = refl
  head-scan g z (U.skipˢ k c)  = refl
  head-scan g z (U.endˢ k)     = refl
  head-scan g z U.hushˢ        = refl
