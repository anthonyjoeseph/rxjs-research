{-# OPTIONS --guardedness #-}

-- MOVES: the witness (`adequacy.Strong`'s `Sub`) rewritten at one node,
-- and what each part of the relation keeps across the rewrite.  A hop
-- between re-entry configurations is a chain of moves; each part of
-- `Carried` is kept by a lemma per move, so a part added to `Carried`
-- costs a lemma per move and no hop's body.
module adequacy.Moves where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Bool using (true; false)
open import Data.Nat using (ℕ; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; Σ; proj₂)
open import Data.List.Relation.Unary.All using (All; []; _∷_; map)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Unary.Linked using (Linked; [-]; _∷_)
open import Data.List.Relation.Unary.Linked.Properties using (Linked⇒All)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴸ_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Any.Properties using (++⁻)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Tree using (Obs)
import Tree as T
open import denotation.MonotonicList using (Timeline; From; Frame; at; _<ᵖ_; <ᵖ-trans; <ᵖ-irrefl)
import denotation.Unfold as U
open import operation.AbstractObservable using (module Heap; module Run) renaming (module Machine to Shared)
open import operation.PureObservable using (Pureᴾ; Out; module Pure)
open import adequacy.Strong using (module Strongly)

module Moving (R : Set) where
  open Heap using (World; Sink; Handle; _⊑_)
  open Shared Timeline (Out R) using (Heapᴹ)
  open Pure R using (Timer; cascade)
  open Strongly R
  open Run (Pureᴾ R) using (module Kit)

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
    plant (in-outer {op = op} {f} {fl} {oc} {k} {r} {ls = ls} π) v     = flatMapˢ op f fl oc k r (plant π v) ls
    plant (in-lanes {op = op} {f} {fl} {oc} {k} {r} {t = so} π) v      = flatMapˢ op f fl oc k r so (plantᴸ π v)
    plant (in-source {S = S} {c} {b} {kb} {k} {fd} {e} {bd = bd} π) v = connectˢ S c b kb k fd e (plant π v) bd
    plant (in-body {S = S} {c} {b} {kb} {k} {fd} {e} {t = s} π) v     = connectˢ S c b kb k fd e s (plant π v)
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

  mutual
    pend : ∀ {h Δ A} → Sub h Δ A → ℕ
    pend (pendingˢ s q)                    = syn s
    pend (coldˢ _ _ _)                     = 0
    pend (ofˢ _ _ _)                       = 0
    pend doneˢ                             = 0
    pend (mapˢ f s)                        = pend s
    pend (scanˢ f r s)                     = pend s
    pend (takeWhileˢ i q c k tk s)         = pend s
    pend (flatMapˢ op f fl oc k r s ls)    = pend s + pendᴸ ls
    pend (connectˢ S c b kb k fd e src bd) = pend src + pend bd
    pend (joinˢ _ _ _ _ _)                 = 0
    pend (deferˢ k s)                      = pend s

    pendᴸ : ∀ {h Δ B} → List (Lane h Δ B) → ℕ
    pendᴸ []                = 0
    pendᴸ (lane c k s ∷ ls) = pend s + pendᴸ ls

  ----------------------------------------------------------------------
  -- What a node rewritten keeps, each part of the relation from the
  -- same part of the node.

  postulate
    part-plant : ∀ {h} (H : Heapᴹ h) {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (v : Sub h Δ′ A′)
               → At.part H u ≡ At.part H v → At.part H (plant π v) ≡ At.part H t

    pend-plant : ∀ {h Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (v : Sub h Δ′ A′)
               → pend u ≡ pend v → pend (plant π v) ≡ pend t

    names-plant : ∀ {h Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (v : Sub h Δ′ A′)
                → names u ≡ names v → names (plant π v) ≡ names t

    subjects-plant : ∀ {h Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (v : Sub h Δ′ A′)
                   → subjects u ≡ subjects v → subjects (plant π v) ≡ subjects t

    joiners-plant : ∀ {h Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (v : Sub h Δ′ A′)
                  → (∀ E → joiners u E ≡ joiners v E) → ∀ E → joiners (plant π v) E ≡ joiners t E

    holds-plant : ∀ {h} (H : Heapᴹ h) {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (v : Sub h Δ′ A′)
                → unsub u ≡ unsub v → (∀ {E o} → At.Holds H u E o → At.Holds H v E o)
                → ∀ {E o} → At.Holds H t E o → At.Holds H (plant π v) E o

    gated-plant : ∀ {h} (H : Heapᴹ h) {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (v : Sub h Δ′ A′)
                → At.part H u ≡ At.part H v → (At.Gated H u → At.Gated H v) → (At.Dead H u → At.Dead H v)
                → At.Gated H t → At.Gated H (plant π v)

    fed-plant : ∀ {h} (H : Heapᴹ h) {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (v : Sub h Δ′ A′)
              → (∀ ν → At.Fed H u ν → At.Fed H v ν) → ∀ ν → At.Fed H t ν → At.Fed H (plant π v) ν

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
    pendings-path {t = flatMapˢ op f fl oc k r so ls} i with ++⁻ (pendings so) i
    ... | inj₁ j = rewait in-outer (pendings-path j)
    ... | inj₂ j = lanes-path in-lanes j
    pendings-path {t = connectˢ S c b kb k fd e src bd} i with ++⁻ (pendings src) i
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

  postulate
    -- The queue's frames: the node's own, replaced in place.
    pendings-plant : ∀ {h Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (v : Sub h Δ′ A′)
                   → Σ (List (Timer h)) λ xs → Σ (List (Timer h)) λ ys
                     → pendings t ≡ xs ++ pendings u ++ ys × pendings (plant π v) ≡ xs ++ pendings v ++ ys

    -- Each cold's frame is its own: no two pending frames share a handle.
    pendings-fresh : ∀ {h Δ A} {t : Sub h Δ A} → AllPairs _≢_ (names t)
                   → AllPairs (λ a b → Timer.handle a ≢ Timer.handle b) (pendings t)

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

  mutual
    ⊕-here : ∀ {h Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) → π ⊕ here ≡ π
    ⊕-here here          = refl
    ⊕-here (in-map π)    = cong in-map (⊕-here π)
    ⊕-here (in-scan π)   = cong in-scan (⊕-here π)
    ⊕-here (in-take π)   = cong in-take (⊕-here π)
    ⊕-here (in-outer π)  = cong in-outer (⊕-here π)
    ⊕-here (in-lanes π)  = cong in-lanes (⊕-hereᴸ π)
    ⊕-here (in-source π) = cong in-source (⊕-here π)
    ⊕-here (in-body π)   = cong in-body (⊕-here π)
    ⊕-here (in-defer π)  = cong in-defer (⊕-here π)

    ⊕-hereᴸ : ∀ {h Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (π : PathLanes ls u) → π ⊕ᴸ here ≡ π
    ⊕-hereᴸ (this-lane π) = cong this-lane (⊕-here π)
    ⊕-hereᴸ (next-lane π) = cong next-lane (⊕-hereᴸ π)

  -- Two nodes alike but for their children.
  data Same {h} : ∀ {Δ A} → Sub h Δ A → Sub h Δ A → Set₁ where
    same         : ∀ {Δ A} {s : Sub h Δ A} → Same s s
    same-map     : ∀ {Δ A B} {f : A → B} {s s′ : Sub h Δ A} → Same (mapˢ f s) (mapˢ f s′)
    same-scan    : ∀ {Δ A B} {f : B → A → B} {r} {s s′ : Sub h Δ A} → Same (scanˢ f r s) (scanˢ f r s′)
    same-take    : ∀ {Δ A} {i p c k tk} {s s′ : Sub h Δ A} → Same (takeWhileˢ i p c k tk s) (takeWhileˢ i p c k tk s′)
    same-flat    : ∀ {Δ A B} {op f fl oc k r} {s s′ : Sub h Δ A} {ls ls′ : List (Lane h Δ B)}
                 → Same (flatMapˢ op f fl oc k r s ls) (flatMapˢ op f fl oc k r s′ ls′)
    same-connect : ∀ {Δ A B} {S c b kb k fd e} {s s′ : Sub h Δ A} {bd bd′ : Sub h (A ∷ Δ) B}
                 → Same (connectˢ S c b kb k fd e s bd) (connectˢ S c b kb k fd e s′ bd′)
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
                (Against.burstAs {p = p} {σ = σ} (Against.firesAs (planted π _)) Against.bottomAs)
  owned-pop {h} H {τ = τ} {e = e} {u = u} {x = x} {sk = sk} {hd = hd} {fr = fr} π ow = record
    { ofs    = λ π′ → ⊥-elim (no-of π′)
    ; plays  = λ π′ nsp → ⊥-elim (no-play π′ nsp)
    ; fires  = fires′
    ; begun  = λ π′ → ⊥-elim (no-pending π′)
    ; ends   = λ π′ l → ⊥-elim (no-end π′ l)
    ; cuts   = λ π′ l → ⊥-elim (no-cut π′ l)
    ; feeds  = λ π′ → ⊥-elim (no-feed π′)
    ; fins   = λ π′ → ⊥-elim (no-fin π′)
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

      no-end : ∀ {Δ′ A′ i p c k q} {s : Sub h Δ′ A′} → Path (plant π fc) (takeWhileˢ i p c k (ending q) s) → At.val H (Kit.live c) ≡ true → ⊥
      no-end π′ l with unplant π fc π′
      ... | inj₁ (() , _)
      ... | inj₂ (_ , q , same)      = gone (Owned.ends ow q l)
      ... | inj₂ (_ , q , same-take) = gone (Owned.ends ow q l)

      no-cut : ∀ {Δ′ A′ i p c k} {s : Sub h Δ′ A′} → Path (plant π fc) (takeWhileˢ i p c k taken s) → At.val H (Kit.live c) ≡ true → ⊥
      no-cut π′ l with unplant π fc π′
      ... | inj₁ (() , _)
      ... | inj₂ (_ , q , same)      = gone (proj₂ (Owned.cuts ow q l))
      ... | inj₂ (_ , q , same-take) = gone (proj₂ (Owned.cuts ow q l))

      no-feed : ∀ {Δ′ A B S c b kb k x q ss e′} {s : Sub h Δ′ A} {bd : Sub h (A ∷ Δ′) B}
              → Path (plant π fc) (connectˢ S c b kb k (feeding x q ss) e′ s bd) → ⊥
      no-feed π′ with unplant π fc π′
      ... | inj₁ (() , _)
      ... | inj₂ (_ , q , same)         = gone (Owned.feeds ow q)
      ... | inj₂ (_ , q , same-connect) = gone (Owned.feeds ow q)

      no-fin : ∀ {Δ′ A B S c b kb k q ss e′} {s : Sub h Δ′ A} {bd : Sub h (A ∷ Δ′) B}
             → Path (plant π fc) (connectˢ S c b kb k (finishing q ss) e′ s bd) → ⊥
      no-fin π′ with unplant π fc π′
      ... | inj₁ (() , _)
      ... | inj₂ (_ , q , same)         = gone (Owned.fins ow q)
      ... | inj₂ (_ , q , same-connect) = gone (Owned.fins ow q)
