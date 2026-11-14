{-# OPTIONS --guardedness #-}

-- A READER SIMULATES ITS READER: the plain reader joins the hot's proper
-- rows past its subscription; the elaborated one joins the annotated
-- rows past its own, folds them by `joinStep` and merges each fold's
-- list.  A plain value at the hot row `k` is carried by the last value
-- of the lane of `k`'s carrier joined; an end by the elaborated end.
-- Each joined row is anchored at its hot row's carrier joined at the
-- subscription's image (`Mr`).
module simultaneous.SimReader where

open import Data.Bool using (Bool; true)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; [_]; length)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.List.Relation.Unary.All using (lookup)
open import Data.Maybe using (Maybe)
open import Data.Nat using (pred)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst₂)
open import Relation.Nullary using (¬_)

open import Tree using (connected)
open import Data.Maybe using (nothing)
open import denotation.Position using (Pos; root; _≟ᵖ_; _⊕_; sub; ix; last)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; end; EmissionSet; Den; hot; Proper; Truncate; Rejoin; _≺_; _≼_; enter; approx;
  module Scan; module Merge; module Op; DenEnv)
open import denotation.Laws.Worlds using (Hots; Ok; Lawful)
open import Tree using (mergeᶠ)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Sim using (PMap; _∪ᴹ_; Emb; Sim; Carried; Local; Fresh; NoneUnder; Joins; ListedB; BoundOk; Within;
  Shows; Shown; AShows; AShown; HotSim; EnvSim; EnvJoins; Apart; SimIH; sih)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; elab; joinStep)

------------------------------------------------------------------------
-- A reading, plain and elaborated

module Reading {X : Set} (Amb : PMap) (S : EmissionSet X) (G : EmissionSet (AIE X)) {c₀ : Maybe Pos}
               (hs : Sim AShows AShown Amb c₀ S G) (p p′ : Pos) where
  open Sim hs using () renaming (Img to Car)

  T : EmissionSet X
  T = Truncate (Rejoin p S)

  R : EmissionSet (AIE X)
  R = Truncate (Rejoin p′ G)

  z₀ : Bool × List (IE X)
  z₀ = true , []

  O : EmissionSet (Bool × List (IE X))
  O = Truncate (Scan.ScanT joinStep z₀ R)

  F : Bool × List (IE X) → Den (IE X)
  F s = Op.of (proj₂ s)

  U : EmissionSet (IE X)
  U = Truncate (Merge.JoinT F O)

  -- Each joined value or end, anchored at its hot row's carrier joined;
  -- the late end at the elaborated end.
  data Mr : PMap where
    mrow  : ∀ {k e L} → S k e → Carried e → p ≺ k → Car k L → Mr (k ⊕ [ sub p ]) (L ⊕ [ sub p′ ])
    mlate : ∀ {c l} → S c end → c ≼ p → R l end → Mr (p ⊕ [ last ]) l

  -- A joined value, carried by the last value of its carrier's lane; an
  -- end by the elaborated end.
  data ImgR : Pos → Pos → Set where
    ival  : ∀ {k a L s} → S k (out a) → p ≺ k → Car k L → Scan.Acc joinStep z₀ R (L ⊕ [ sub p′ ]) s
          → ImgR (k ⊕ [ sub p ]) (L ⊕ [ sub p′ ] ⊕ [ ix 1 ] ⊕ [ ix (pred (length (proj₂ s))) ])
    iend  : ∀ {k L} → S k end → p ≺ k → Car k L → ImgR (k ⊕ [ sub p ]) (L ⊕ [ sub p′ ])
    ilate : ∀ {c l} → S c end → c ≼ p → R l end → ImgR (p ⊕ [ last ]) l

  module Read (H H′ : Pos → Set) (c : Maybe Pos) where
    postulate
      reader-local : Local H H′ p p′ Mr
      reader-emb   : Emb (Amb ∪ᴹ Mr)
      reader-none  : NoneUnder Mr T
      reader-sim   : Sim Shows Shown (Amb ∪ᴹ Mr) c T U

------------------------------------------------------------------------
-- The former

module Leaf {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (i : A ∈ Γ) (env : DenEnv Γ) (env′ : DenEnv Δ) (Amb : PMap) (c : Maybe Pos)
            (ap : Apart env) (es : EnvSim ρ Amb c env env′) (p p′ : Pos) where
  open HotSim (es i) using (rows; rows′; sim; isP; isE)
  open Reading Amb rows rows′ sim p p′
  open Read (Hots env) (Hots env′) c

  Goal : Den A → Den (AIE A) → Set₁
  Goal d d′ = ListedB (enter d p) c → BoundOk (Hots env′) Amb (enter d p) c
    → Σ PMap λ M → Local (Hots env) (Hots env′) p p′ M × Emb (Amb ∪ᴹ M) × NoneUnder M (enter d p)
      × EnvJoins ρ env env′ es M
      × Sim Shows Shown (Amb ∪ᴹ M) c (enter d p) (enter (Op.flatMap (mergeᶠ nothing) (λ s → Op.of (proj₂ s)) (Op.scan joinStep z₀ d′)) p′)

  postulate
    reader-joins : EnvJoins ρ env env′ es Mr

  core : Goal (hot rows) (hot rows′)
  core _ _ = Mr , reader-local , reader-emb , reader-none , reader-joins , reader-sim

  leaf : Goal (lookup env i) (lookup env′ (ρ (∈-map⁺ AIE i)))
  leaf = subst₂ Goal (sym isP) (sym isE) core

sim-connected : ∀ n {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (i : A ∈ Γ) → SimIH n ρ (connected i)
sim-connected n ρ i = sih λ env env′ Amb c ge ge′ ap es em p p′ pp fr ok ok′ nh L B →
  Leaf.leaf ρ i env env′ Amb c ap es p p′ L B
