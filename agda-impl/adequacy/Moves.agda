{-# OPTIONS --guardedness #-}

-- MOVES: the witness (`adequacy.Strong`'s `Sub`) rewritten at one node.
module adequacy.Moves where

open import Data.Bool using (true)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Linked using (Linked; [-]; _∷_)
open import Data.List.Relation.Unary.Linked.Properties using (Linked⇒All)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import denotation.MonotonicList.Events using (_<ᵖ_; <ᵖ-trans)
open import operation.PureObservable using (module Driver)
open import adequacy.Strong using (module Strongly)

module Moving (R : Set) where
  open Driver R using (Timer; cascade)
  open Strongly R

  ----------------------------------------------------------------------
  -- One node rewritten

  mutual
    plant : ∀ {Γ A Δ B π} {t : Sub Γ A} {u : Sub Δ B} → Path t u π → Sub Δ B → Sub Γ A
    plant here v                                                       = v
    plant (in-map {f = f} π) v                                         = mapˢ f (plant π v)
    plant (in-scan {f = f} {z = z} π) v                                = scanˢ f z (plant π v)
    plant (in-cut {l = l} {a = a} π) v                                 = cutˢ l a (plant π v)
    plant (in-lane {r = r} π) v                                        = laneˢ r (plant π v)
    plant (in-take {i = i} {q = q} {tk = tk} π) v                     = takeWhileˢ i q tk (plant π v)
    plant (in-outer {op = op} {f = f} {d = d} {n = n} {qs = qs} {pl = pl} {ls = ls} π) v
                                                                       = flatMapˢ op f d n qs pl (plant π v) ls
    plant (in-lanes {op = op} {f = f} {d = d} {n = n} {qs = qs} {pl = pl} {o = o} π) v
                                                                       = flatMapˢ op f d n qs pl o (plantᴸ π v)
    plant (in-source {k = k} {r = r} {e = e} {rt = rt} {b = b} π) v  = connectˢ k r e rt (plant π v) b
    plant (in-body {k = k} {r = r} {e = e} {rt = rt} {s = s} π) v    = connectˢ k r e rt s (plant π v)

    plantᴸ : ∀ {Γ A Δ B i π} {ls : List (Sub Γ A)} {u : Sub Δ B} → PathLanes ls u i π → Sub Δ B → List (Sub Γ A)
    plantᴸ (this-lane {ls = ls} π) v = plant π v ∷ ls
    plantᴸ (next-lane {l = l} π) v   = l ∷ plantᴸ π v

  -- Where the planted node now sits.
  mutual
    planted : ∀ {Γ A Δ B π} {t : Sub Γ A} {u : Sub Δ B} (ψ : Path t u π) (v : Sub Δ B) → Path (plant ψ v) v π
    planted here v          = here
    planted (in-map π) v    = in-map (planted π v)
    planted (in-scan π) v   = in-scan (planted π v)
    planted (in-cut π) v    = in-cut (planted π v)
    planted (in-lane π) v   = in-lane (planted π v)
    planted (in-take π) v   = in-take (planted π v)
    planted (in-outer π) v  = in-outer (planted π v)
    planted (in-lanes π) v  = in-lanes (plantedᴸ π v)
    planted (in-source π) v = in-source (planted π v)
    planted (in-body π) v   = in-body (planted π v)

    plantedᴸ : ∀ {Γ A Δ B i π} {ls : List (Sub Γ A)} {u : Sub Δ B} (ψ : PathLanes ls u i π) (v : Sub Δ B)
             → PathLanes (plantᴸ ψ v) v i π
    plantedᴸ (this-lane π) v = this-lane (planted π v)
    plantedᴸ (next-lane π) v = next-lane (plantedᴸ π v)

  -- The old node planted back where the new one sits: the tree as it was.
  mutual
    replanted : ∀ {Γ A Δ B π} {t : Sub Γ A} {u : Sub Δ B} (ψ : Path t u π) (v : Sub Δ B) → plant (planted ψ v) u ≡ t
    replanted here v = refl
    replanted (in-map {f = f} π) v = cong (mapˢ f) (replanted π v)
    replanted (in-scan {f = f} {z = z} π) v = cong (scanˢ f z) (replanted π v)
    replanted (in-cut {l = l} {a = a} π) v = cong (cutˢ l a) (replanted π v)
    replanted (in-lane {r = r} π) v = cong (laneˢ r) (replanted π v)
    replanted (in-take {i = i} {q = q} {tk = tk} π) v = cong (takeWhileˢ i q tk) (replanted π v)
    replanted (in-outer {op = op} {f = f} {d = d} {n = n} {qs = qs} {pl = pl} {ls = ls} π) v =
      cong (λ o → flatMapˢ op f d n qs pl o ls) (replanted π v)
    replanted (in-lanes {op = op} {f = f} {d = d} {n = n} {qs = qs} {pl = pl} {o = o} π) v =
      cong (flatMapˢ op f d n qs pl o) (replantedᴸ π v)
    replanted (in-source {k = k} {r = r} {e = e} {rt = rt} {b = b} π) v = cong (λ s → connectˢ k r e rt s b) (replanted π v)
    replanted (in-body {k = k} {r = r} {e = e} {rt = rt} {s = s} π) v = cong (connectˢ k r e rt s) (replanted π v)

    replantedᴸ : ∀ {Γ A Δ B i π} {ls : List (Sub Γ A)} {u : Sub Δ B} (ψ : PathLanes ls u i π) (v : Sub Δ B)
               → plantᴸ (plantedᴸ ψ v) u ≡ ls
    replantedᴸ (this-lane {ls = ls} π) v = cong (_∷ ls) (replanted π v)
    replantedᴸ (next-lane {l = l} π) v = cong (l ∷_) (replantedᴸ π v)

  -- The queue past its head: each later.
  later : ∀ {tm : Timer} {ts} → Linked (λ y z → cascade y <ᵖ cascade z ≡ true) (tm ∷ ts)
        → All (λ z → cascade tm <ᵖ cascade z ≡ true) ts
  later [-]                = []
  later {tm = tm} (r ∷ lk) =
    Linked⇒All {R = λ a b → cascade a <ᵖ cascade b ≡ true} (λ {a} {b} {c} → <ᵖ-trans (cascade a) (cascade b) (cascade c)) {v = tm} r lk
