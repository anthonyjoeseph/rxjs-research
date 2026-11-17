{-# OPTIONS --guardedness #-}

-- THE FLATMAP'S CASE (`flat-rel`): the plain flatMap's record against its
-- elaboration, one layer at a time.  The plain side stays the flatMap's
-- own table; the elaborated side grows outward from the lanes' flatMap
-- (`core`) through the combined scan, the closer and the share.
--
-- The source is related once, at the share's subscription, in the
-- environment the share's trigger extends; its hot is the shared table
-- the lanes' flatMap reads.  The lanes are related wherever they are
-- subscribed alike, each in the environment the flatMap's four binders
-- extend, which no lane reads.
--
-- A lane is subscribed past its creator, so its pair is aligned from its
-- creator's: an unqueued lane, under the source row and that row's image,
-- by the source's `cuts` and `linked` at the row; a queued lane, under an
-- earlier lane's end and its image, by that lane's.  `flat-core` owes
-- both.
module simultaneous.TableFlat where

open import Data.List using (List; []; _∷_; [_])
open import Data.List.Relation.Unary.All using (All; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (refl)

open import Tree using (Obs; FlatOp; mergeᶠ; of; flatMap; connect; connected)
open import denotation.Position using (Pos; Label; root; _≟ᵖ_; ix; sub; _⊕_)
open import denotation.Events using (Timeline; fresh)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (hotOf)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Listing using (listC; listC-ok; UncutEnv)
open import simultaneous.InstEmit using (valuesOf)
open import simultaneous.TableCorr using (Rel)
open import simultaneous.TableEnv using (Ren; wk; Tab; Tab*; _⊕ˡ_; Linked; linked-r*; Aligned; aligned-r*; Rest; Out; _⊢_; EnvR; maps; env-wk; Holds; Full)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; elab; each; laneˢ; closer; combined; trackers)

module Flat {Γ A B} n (op : FlatOp) (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A)
  (ρ : ℕ → All Tb.Listed Γ) (uρ : ∀ N → UncutEnv (ρ N)) {Δ} (ρι : Ren Γ Δ) (ρ* : ℕ → All Tb.Listed Δ) (uρ* : ∀ N → UncutEnv (ρ* N))
  (env : EnvR ρ ρι ρ*) (p p* : Pos) where

  ----------------------------------------------------------------------
  -- The elaborated parts

  ρι⁴ : Ren Γ (⊤ ∷ IE B ∷ IE A ∷ ⊤ ∷ Δ)
  ρι⁴ = wk (wk (wk (wk ρι)))

  s* : Obs Timeline (⊤ ∷ Δ) (IE A)
  s* = elab (wk ρι) s

  core : Obs Timeline (IE B ∷ IE A ∷ ⊤ ∷ Δ) (IE B)
  core = flatMap op (λ a → laneˢ (elab ρι⁴ (f a))) (each valuesOf (connected (there (here refl))))

  inner : Obs Timeline (IE B ∷ IE A ∷ ⊤ ∷ Δ) (IE B)
  inner = connect core (combined op (trackers Γ 0 (wk (wk (wk (wk ρι))))))

  body : Obs Timeline (IE A ∷ ⊤ ∷ Δ) (IE B)
  body = connect closer inner

  shared : Obs Timeline (⊤ ∷ Δ) (IE A)
  shared = flatMap (mergeᶠ nothing) (λ _ → s*) (connected (here refl))

  ----------------------------------------------------------------------
  -- Their subscriptions and hots

  -- The share's body, the closer's body, the combined connect, and the
  -- lanes' flatMap.
  c₃ c₂ c₁ c₀ : Pos
  c₃ = p* ⊕ [ ix 0 ] ⊕ [ ix 0 ]
  c₂ = c₃ ⊕ [ ix 0 ]
  c₁ = c₂ ⊕ [ ix 1 ]
  c₀ = c₂ ⊕ [ ix 0 ]

  -- The source's elaborated subscription: the lane of the trigger's value,
  -- read by the shared flatMap.
  sp* : Pos
  sp* = p* ⊕ˡ (ix 1 ∷ ix 0 ∷ sub (p* ⊕ [ ix 0 ] ⊕ [ ix 1 ]) ∷ ix 1 ∷ [])

  tt-tab : ℕ → Tb.Listed ⊤
  tt-tab N = hotOf (proj₁ (listC-ok (3 + N) n (of (tt ∷ [])) (uρ* N) (p* ⊕ [ ix 1 ])))

  ρ*s : ℕ → All Tb.Listed (⊤ ∷ Δ)
  ρ*s N = tt-tab N ∷ ρ* N

  uρ*s : ∀ N → UncutEnv (ρ*s N)
  uρ*s N = proj₂ (proj₂ (listC-ok (3 + N) n (of (tt ∷ [])) (uρ* N) (p* ⊕ [ ix 1 ]))) , uρ* N

  sh-tab : ℕ → Tb.Listed (IE A)
  sh-tab N = hotOf (proj₁ (listC-ok (3 + N) n shared {ρ*s N} (uρ*s N) (p* ⊕ [ ix 0 ] ⊕ [ ix 1 ])))

  ρ*h : ℕ → All Tb.Listed (IE A ∷ ⊤ ∷ Δ)
  ρ*h N = sh-tab N ∷ ρ*s N

  uρ*h : ∀ N → UncutEnv (ρ*h N)
  uρ*h N = proj₂ (proj₂ (listC-ok (3 + N) n shared {ρ*s N} (uρ*s N) (p* ⊕ [ ix 0 ] ⊕ [ ix 1 ]))) , uρ*s N

  cl-tab : ℕ → Tb.Listed (IE B)
  cl-tab N = hotOf (proj₁ (listC-ok (3 + N) n closer {ρ*h N} (uρ*h N) (c₃ ⊕ [ ix 1 ])))

  ρ*c : ℕ → All Tb.Listed (IE B ∷ IE A ∷ ⊤ ∷ Δ)
  ρ*c N = cl-tab N ∷ ρ*h N

  ----------------------------------------------------------------------
  -- The children's records

  -- The source, at the share's subscription.
  Src : Set₁
  Src = Out n s ρ (wk ρι) ρ*s (maps env) p sp*

  -- Each lane, wherever subscribed alike, whatever the four binders hold.
  Lanes : Set₁
  Lanes = ∀ a (t₁ : ℕ → Tb.Listed ⊤) (t₂ : ℕ → Tb.Listed (IE B)) (t₃ : ℕ → Tb.Listed (IE A)) (t₄ : ℕ → Tb.Listed ⊤)
        → (∀ N → UncutEnv (t₁ N ∷ t₂ N ∷ t₃ N ∷ t₄ N ∷ ρ* N))
        → Holds n (f a) ρ ρι⁴ (λ N → t₁ N ∷ t₂ N ∷ t₃ N ∷ t₄ N ∷ ρ* N) (env-wk t₁ (env-wk t₂ (env-wk t₃ (env-wk t₄ env))))

  -- The plain flatMap's tables.
  P : ℕ → _
  P = Tab n (flatMap op f s) ρ p

  ----------------------------------------------------------------------
  -- The layers

  postulate
    -- THE LANES' FLATMAP: the shared hot is the source's elaborated
    -- rows, each value read off by `each valuesOf` under its image; each
    -- value's elaborated lane is the plain lane's, run through `laneˢ`.
    -- Its rows are the plain flatMap's values and ends, along the
    -- source's map for the source's rows and each lane's for its own.
    flat-core : Src → Lanes → Aligned (maps env) ρ p p* → Linked p p*
              → Rel P (λ N → listC (3 + N) n core (ρ*c N) c₁) p c₁

    -- THE COMBINED SCAN: the lanes' flatMap read through its hot by the
    -- scan over its routes and the trackers', each value re-emitted in
    -- place with its marks.
    flat-comb : Rel P (λ N → listC (3 + N) n core (ρ*c N) c₁) p c₁
              → Rel P (λ N → listC (3 + N) n inner (ρ*c N) c₂) p c₂

    -- THE CLOSER: the combined run past the closer's subscription, the
    -- closer's marks unshown and in the instants of the source's ends.
    flat-close : Rel P (λ N → listC (3 + N) n inner (ρ*c N) c₂) p c₂
               → Rel P (λ N → listC (3 + N) n body (ρ*h N) c₃) p c₃

    -- THE SHARE: the body read past the share's two connects; the
    -- trigger's and the shared hot's own rows are never shown.
    flat-share : Rel P (λ N → listC (3 + N) n body (ρ*h N) c₃) p c₃
               → Rel P (Tab* n ρι (flatMap op f s) ρ* p*) p p*

  flat-tab : Src → Lanes → Aligned (maps env) ρ p p* → Linked p p* → Rel P (Tab* n ρι (flatMap op f s) ρ* p*) p p*
  flat-tab Os Ls al lk = flat-share (flat-close (flat-comb (flat-core Os Ls al lk)))

  postulate
    -- THE FLATMAP'S ORDER FACTS: each row is a source row or a lane row
    -- at its own position, imaged along its stream's map, so each fact is
    -- the source's or the lane's; a lane's subscription is past every
    -- earlier pair that cuts the flatMap alike.
    flatmap-order : (Os : Src) (Ls : Lanes) (al : Aligned (maps env) ρ p p*) (lk : Linked p p*) → Rest (maps env) ρ (flat-tab Os Ls al lk)

flat-rel : ∀ {Γ A B} n (op : FlatOp) (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A)
         → Full n s → (∀ a → Full n (f a)) → Full n (flatMap op f s)
flat-rel n op f s Fs Ff ρ uρ ρι ρ* uρ* env p p* al lk = F.flat-tab Os Ls al lk ⊢ F.flatmap-order Os Ls al lk
  where
    module F = Flat n op f s ρ uρ ρι ρ* uρ* env p p*

    path : List Label
    path = ix 1 ∷ ix 0 ∷ sub (p* ⊕ [ ix 0 ] ⊕ [ ix 1 ]) ∷ ix 1 ∷ []

    Os : F.Src
    Os = Fs ρ uρ (wk ρι) F.ρ*s F.uρ*s (env-wk F.tt-tab env) p F.sp*
           (aligned-r* {Ψ = maps env} {ρ = ρ} al path) (linked-r* lk path)

    Ls : F.Lanes
    Ls a t₁ t₂ t₃ t₄ u = Ff a ρ uρ F.ρι⁴ (λ N → t₁ N ∷ t₂ N ∷ t₃ N ∷ t₄ N ∷ ρ* N) u (env-wk t₁ (env-wk t₂ (env-wk t₃ (env-wk t₄ env))))
