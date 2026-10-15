{-# OPTIONS --guardedness #-}

-- MOVES: the witness (`adequacy.Strong`'s `Sub`) rewritten at one node,
-- and what each part of the relation keeps across the rewrite.  A hop
-- between re-entry configurations is a chain of moves; each part of
-- `Carried` is kept by a lemma per move, so a part added to `Carried`
-- costs a lemma per move and no hop's body.
module adequacy.Moves where

open import Data.List using (List; []; _∷_)
open import Data.Bool using (true; false)
open import Data.Nat using (ℕ; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Data.List.Relation.Unary.Linked using (Linked)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴸ_)

open import Tree using (Obs)
import Tree as T
open import denotation.MonotonicList using (Timeline; Frame; at; _<ᵖ_)
import denotation.Unfold as U
open import operation.AbstractObservable using (module Heap) renaming (module Machine to Shared)
open import operation.PureObservable using (Out; module Pure)
open import adequacy.Strong using (module Strongly)

module Moving (R : Set) where
  open Heap using (World; Sink; Handle; _⊑_)
  open Shared Timeline (Out R) using (Heapᴹ)
  open Pure R using (Timer; cascade)
  open Strongly R

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
  data Waits {h} (t : Sub h [] R) : Timer h → Set₁ where
    waits : ∀ {Δ A τ e v u x} {sk : Sink h A} {hd} {fr : Frame A u}
            (π : Path t (coldˢ {Δ = Δ} sk hd (waiting {u = v} τ e (at u x fr))))
          → Waits t (record { due = τ + u ; sink = sk ; handle = hd ; at′ = u ; from = e ; frame = fr })

  postulate
    pendings-path : ∀ {h} {t : Sub h [] R} {tm : Timer h} → tm ∈ᴸ pendings t → Waits t tm

    -- The fired cold's frame leaves the queue with its timer: each
    -- cold's frame is its own, and the queue's are strictly ordered.
    timed-pop : ∀ {h} (H : Heapᴹ h) {t : Sub h [] R} {ts} {Δ A τ e v u x} {sk : Sink h A} {hd} {fr : Frame A u}
                (π : Path t (coldˢ {Δ = Δ} sk hd (waiting {u = v} τ e (at u x fr))))
              → At.Timed H (record { due = τ + u ; sink = sk ; handle = hd ; at′ = u ; from = e ; frame = fr } ∷ ts) (pendings t)
              → Linked (λ y z → cascade y <ᵖ cascade z ≡ true)
                  (record { due = τ + u ; sink = sk ; handle = hd ; at′ = u ; from = e ; frame = fr } ∷ ts)
              → AllPairs _≢_ (names t)
              → At.Timed H ts (pendings (plant π (coldˢ sk hd (fired τ e (at u x fr)))))

    -- Nothing owed at the turn, and the popped cold now fired: owed only
    -- its burst.
    owned-pop : ∀ {h} (H : Heapᴹ h) {t : Sub h [] R} {p w} {σ : w ⊑ h} {Δ A τ e v u x} {sk : Sink h A} {hd} {fr : Frame A u}
                (π : Path t (coldˢ {Δ = Δ} sk hd (waiting {u = v} τ e (at u x fr))))
              → Owned H t (Against.calmAs {p = p} {σ = σ}) → At.spentʰ H hd ≡ false
              → Owned H (plant π (coldˢ sk hd (fired τ e (at u x fr))))
                  (Against.burstAs {p = p} {σ = σ} (Against.firesAs (planted π _)) Against.bottomAs)
