{-# OPTIONS --guardedness #-}

-- WHAT A SHUT FALLS BACK ON: the rest of every burst's source a shut
-- reaches.  A burst moved out of its range by a told end steps its
-- source's rest instead, so a shut heads no sooner than `q` only where
-- each of those rests does.
module adequacy.Calm where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to all-++⁺)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (zero; suc)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

open import Tree using (Obs; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.MonotonicList.Events using (Pos; From; Timeline; timelineAt; at; done; quiet)
import denotation.Unfold as U
open import adequacy.Sorted using (_≤ᵖ_; ≤ᵖ-trans)
open import adequacy.Leaves using (Pinned; pinned; unpinned; rest-pinned)

-- A step's next event no earlier than `q`.
NoSooner : Pos → Maybe Pos → Set
NoSooner q m = ∀ {k} → m ≡ just k → q ≤ᵖ k

-- A node's rest's next event, read at any output type.
restHead : ∀ {Γ A} → U.Node Γ A → Maybe Pos
restHead t = U.headˢ (U.restˢ {B = ⊤} t)

pinned-head : ∀ {Γ B C} {s : U.Step Γ B} {s′ : U.Step Γ C} → Pinned s s′ → U.headˢ s ≡ U.headˢ s′
pinned-head pinned   = refl
pinned-head unpinned = refl

-- A rest heads alike at every output type.
rest-heads : ∀ {Γ A B q} (t : U.Node Γ A) → NoSooner q (restHead t) → NoSooner q (U.headˢ (U.restˢ {B = B} t))
rest-heads t h e = h (trans (pinned-head (rest-pinned t)) e)

-- Every rest a shut falls back on, by the shut's own walk: a node's
-- step and its rest each read the sources of the bursts they reach.
mutual
  calms : ∀ {Γ B} → U.Node Γ B → List (Maybe Pos)
  calms (U.mapᶜ f n)                 = calms n
  calms (U.scanᶜ f z n)              = calms n
  calms (U.takeWhileᶜ b p n)         = calms n
  calms (U.flatMapᶜ op g o ls qs pl) = calmsᴹ o ++ calmsᴸ ls ++ calms pl
  calms (U.connectᶜ r b s)           = calms b ++ calmsˢ s
  calms (U.endingᶜ p n)              = calms n
  calms (U.restᶜ n)                  = calmsʳ n
  calms (U.unionᶜ x y)               = calmsʳ x ++ calmsʳ y
  calms (U.burstingᶜ r t)            = restHead t ∷ calms t ++ calmsʳ t
  calms (U.underᶜ s b)               = calmsʳ b
  calms n                            = []

  calmsʳ : ∀ {Γ B} → U.Node Γ B → List (Maybe Pos)
  calmsʳ (U.mapᶜ f n)                 = calmsʳ n
  calmsʳ (U.scanᶜ f z n)              = calmsʳ n
  calmsʳ (U.takeWhileᶜ b p n)         = calmsʳ n
  calmsʳ (U.flatMapᶜ op g o ls qs pl) = calmsʳᴹ o ++ calmsʳᴸ ls ++ calmsʳ pl
  calmsʳ (U.connectᶜ r b s)           = calmsʳ b ++ calmsᵇ s
  calmsʳ (U.endingᶜ p n)              = calmsʳ n
  calmsʳ (U.restᶜ n)                  = calmsʳ n
  calmsʳ (U.unionᶜ x y)               = calmsʳ x ++ calmsʳ y
  calmsʳ (U.burstingᶜ r t)            = restHead t ∷ calms t ++ calmsʳ t
  calmsʳ (U.underᶜ s b)               = calmsʳ b
  calmsʳ n                            = []

  calmsʳᴹ : ∀ {Γ B} → Maybe (U.Node Γ B) → List (Maybe Pos)
  calmsʳᴹ nothing  = []
  calmsʳᴹ (just n) = calmsʳ n

  calmsʳᴸ : ∀ {Γ B} → List (U.Node Γ B) → List (Maybe Pos)
  calmsʳᴸ []       = []
  calmsʳᴸ (n ∷ ns) = calmsʳ n ++ calmsʳᴸ ns

  -- A connect's source bursts in the connect's rest.
  calmsᵇ : ∀ {Γ B} → U.Source Γ B → List (Maybe Pos)
  calmsᵇ (U.live s)    = restHead s ∷ calms s ++ calmsʳ s
  calmsᵇ (U.ended e t) = restHead t ∷ calms t ++ calmsʳ t

  calmsᴹ : ∀ {Γ B} → Maybe (U.Node Γ B) → List (Maybe Pos)
  calmsᴹ nothing  = []
  calmsᴹ (just n) = calms n

  calmsᴸ : ∀ {Γ B} → List (U.Node Γ B) → List (Maybe Pos)
  calmsᴸ []       = []
  calmsᴸ (n ∷ ns) = calms n ++ calmsᴸ ns

  calmsˢ : ∀ {Γ B} → U.Source Γ B → List (Maybe Pos)
  calmsˢ (U.live s)    = calms s
  calmsˢ (U.ended e t) = calms t

-- Every rest a shut of the node falls back on heads no sooner than `q`.
Calm : ∀ {Γ B} → Pos → U.Node Γ B → Set
Calm q c = All (NoSooner q) (calms c)

-- Calm past a position, calm past any before it.
calm-below : ∀ {Γ B q′ q} {c : U.Node Γ B} → q′ ≤ᵖ q → Calm q c → Calm q′ c
calm-below le = mapᴬ (λ h {k} e → ≤ᵖ-trans le (h e))

-- A fresh subscription has no burst running, so nothing to fall back on.
calm-start : ∀ {Γ A q} p (m : From A 0) → Calm q (U.startᶜ {Γ} p m)
calm-start p (at zero _ b)    = []
calm-start p (at (suc t) _ b) = []
calm-start p done             = []
calm-start p quiet            = []

calm-subscribe : ∀ {Γ A q} (o : Obs Timeline Γ A) p → Calm q (U.subscribe o p)
calm-subscribe (cold c)          p = calm-start p (timelineAt c p)
calm-subscribe empty             p = []
calm-subscribe (of xs)           p = []
calm-subscribe (map f s)         p = calm-subscribe s p
calm-subscribe (scan f z s)      p = calm-subscribe s p
calm-subscribe (takeWhile i q s) p = calm-subscribe s p
calm-subscribe (flatMap op f s)  p = all-++⁺ (calm-subscribe s p) []
calm-subscribe (connect s b)     p = all-++⁺ (calm-subscribe b _) (calm-subscribe s _)
calm-subscribe (connected i)     p = []
calm-subscribe (defer l)         p = []

calm-just : ∀ {Γ B q} (o : Maybe (U.Node Γ B)) → (∀ {c} → o ≡ just c → Calm q c) → All (NoSooner q) (calmsᴹ o)
calm-just nothing  h = []
calm-just (just c) h = h refl

calm-all : ∀ {Γ B q} (ls : List (U.Node Γ B)) → All (Calm q) ls → All (NoSooner q) (calmsᴸ ls)
calm-all []       []       = []
calm-all (l ∷ ls) (h ∷ hs) = all-++⁺ h (calm-all ls hs)
