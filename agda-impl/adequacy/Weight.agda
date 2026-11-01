{-# OPTIONS --guardedness #-}

-- THE WEIGHT OF A SILENT RUN: what a run still has to do before its
-- clock reaches a listed position, short of `P`.  Each pending
-- subscription weighs its syntax (a defer one), by depth; each admin mark,
-- pending or owed, and each mark keyed at or before `P` at no listed
-- position, an of's every value still owed counted, its depth + 2; a
-- listed mark the clock has reached, its run: its climb and the one mark
-- it may leave, twice its depth + 4; a rise, its depth.  A mark past `P`
-- runs only once the clock has passed `P`, and a listed one ahead of the
-- clock only once the clock reaches it, so neither weighs.

-- Weighed by the clock, a still step raises no mark's weight: a listed
-- mark ahead stays ahead.
module adequacy.Weight where

open import Data.Bool using (Bool; true; false; _∧_; not; if_then_else_)
open import Data.Bool.ListAction using (any)
open import Data.List using (List; []; _∷_; _++_; [_]; length; concatMap) renaming (map to mapL)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _+_; _*_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (does)

open import Tree using (Obs; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.Events using (Pos; Timeline; ix; last; _≟ᵖ_)
open import operation.Key using (Key; at; after; _<ᴷ_)
open import operation.PureObservable using (module Machine; due)
open Machine using (St; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS; pend; CS;
                    Conf; ⟨_,_,_,_⟩; plug; dirs; subscribing; absorbed; rising;
                    attAt; attached; free; cpAt; cutAt; overAt)

-- THE RUN'S CLOCK: the least mark due once everything is absorbed; mid-run,
-- where the run is.
Clock : ∀ {R} → Conf R → Key
Clock k with Conf.mode k | Machine.next k
... | absorbed | just κ = κ
... | _        | _      = at (Conf.pos k)

-- A listed position.
listed : List Pos → Key → Bool
listed ks (at q)    = any (λ r → does (q ≟ᵖ r)) ks
listed ks (after _) = false

module Weigh (ks : List Pos) (P : Pos) (C : Key) where
  -- A mark keyed `κ`, `d` deep, the clock at `C`.
  wt : ℕ → Key → ℕ
  wt d κ = if at P <ᴷ κ then 0 else if listed ks κ then (if C <ᴷ κ then 0 else 4 + 2 * d) else 2 + d

  -- A pending subscription to `o`, `d` deep.
  syn : ∀ {Γ A} → ℕ → Obs Timeline Γ A → ℕ
  syn d (cold _)          = 3 + d
  syn d empty             = 3 + d
  syn d (of xs)           = 3 + d + length xs * (2 + d)
  syn d (map _ s)         = 1 + syn (suc d) s
  syn d (scan _ _ s)      = 1 + syn (suc d) s
  syn d (takeWhile _ _ s) = 1 + 2 * (2 + d) + (3 + d) + syn (2 + d) s
  syn d (flatMap _ _ s)   = 1 + (3 + d) + syn (2 + d) s
  syn d (connect s b)     = 1 + 3 * (2 + d) + syn (suc d) b + syn (suc d) s
  syn d (connected _)     = 3 + d
  syn d (defer _)         = 1

  private
    one : ℕ → Bool → ℕ
    one d b = if b then 2 + d else 0

    isNone : Maybe Pos → Bool
    isNone nothing  = true
    isNone (just _) = false

    bodyP : ℕ → Maybe Pos → ℕ
    bodyP d (just p) = wt d (at (p ++ [ ix 1 ])) + (2 + d)
    bodyP d nothing  = 0

  -- An of's values still owed and its end.
  ofW : ∀ {A : Set} → ℕ → ℕ → Pos → List A → ℕ
  ofW d i p []       = wt d (at (p ++ [ last ]))
  ofW d i p (_ ∷ xs) = wt d (at (p ++ [ ix i ])) + ofW d (suc i) p xs

  -- A connect's admin marks, owed and pending.
  connW : ∀ {Γ X} → ℕ → CS Γ X → ℕ
  connW d k = bodyP d (CS.bodyAt k) + one d (not (isNone (CS.attSrc k))) + one d (not (isNone (CS.owedAt k)))
            + one d (CS.srcLive k ∧ isNone (CS.owedAt k))

  mutual
    -- A tree `d` deep.
    pot : ∀ {Γ A} → ℕ → St Γ A → ℕ
    pot d (pend o q)               = syn d o
    pot d (coldS b l) with due l
    ... | just κ                   = wt d κ
    ... | nothing                  = 0
    pot d (ofS i p xs)             = ofW d i p xs
    pot d doneS                    = 0
    pot d (mapS _ s)               = pot (suc d) s
    pot d (scanS _ _ s)            = pot (suc d) s
    pot d (cutS _ (attAt _) s)     = (2 + d) + pot (suc d) s
    pot d (cutS _ attached s)      = pot (suc d) s
    pot d (lnS _ s)                = pot (suc d) s
    pot d (takeS _ _ free s)       = 2 * (2 + d) + pot (suc d) s
    pot d (takeS _ _ (cpAt p) s)   = wt d (at (p ++ [ last ])) + (2 + d) + pot (suc d) s
    pot d (takeS _ _ (cutAt _) s)  = (2 + d) + pot (suc d) s
    pot d (takeS _ _ (overAt _) s) = pot (suc d) s
    pot d (flatS _ _ _ _ _ o ls)   = pot (suc d) o + potL (suc d) ls
    pot d (connS k o b)            = connW d k + pot (suc d) o + pot (suc d) b
    pot d (joinS j g x ib)         = inbox ib
      where
        inbox : List (Pos × _) → ℕ
        inbox []             = 0
        inbox ((q , _) ∷ es) = wt d (at q) + inbox es

    potL : ∀ {Γ A} → ℕ → List (St Γ A) → ℕ
    potL d []       = 0
    potL d (s ∷ ls) = pot d s + potL d ls

-- What the mode still owes: a rise's climb.
climb : ∀ {R} → Conf R → ℕ
climb ⟨ c , s , rising _ , _ ⟩ = length (dirs c)
climb ⟨ _ , _ , _        , _ ⟩ = 0

-- THE WEIGHT, the clock at `C`.
Wᶜ : ∀ {R} → List Pos → Pos → Key → Conf R → ℕ
Wᶜ ks P C k = Weigh.pot ks P C 0 (plug (Conf.ctx k) (Conf.foc k)) + climb k

-- THE WEIGHT.
W : ∀ {R} → List Pos → Pos → Conf R → ℕ
W ks P k = Wᶜ ks P (Clock k) k

-- Each non-empty prefix of a position, itself included.
prefixes : Pos → List Pos
prefixes []      = []
prefixes (l ∷ q) = [ l ] ∷ mapL (l ∷_) (prefixes q)

-- Each listed position and its ancestors.
anc : List Pos → List Pos
anc = concatMap prefixes
