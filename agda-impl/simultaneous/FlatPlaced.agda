{-# OPTIONS --guardedness #-}

-- A FLATMAP HANGS ITS LANES ON ADMISSIBLE ROWS (`FlatPlaced.placed`): what
-- its scan shows lies below a value of the real flatMap, or where the
-- scan's source ends: under its subscription, or past a branch's end.
--
-- Each such row is a world position of its own source's world, so no
-- binder's hot row lies under it (`DeepAt.deep`), and a gap at any
-- extension of it would be a gap at it. The scan's lanes all end before
-- its source does: a lane lies under its row, and nothing follows an end.
module simultaneous.FlatPlaced where

open import Data.List using (List; []; _∷_; [_]; _++_)
import Data.List as L
open import Data.List.Relation.Unary.All using (_∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Data.Bool using (true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
import Relation.Nullary as Nl

open import Tree using (Obs; FlatOp; mergeᶠ; flatMap; of; takeWhile)
open import denotation.Position using (Pos; root; _≟ᵖ_; ix; last; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Den; enter; DenEnv; module Op; out; end; Ended; module Scan; EmissionSet; hot)
open import denotation.Laws.Modulus using (≺-irrefl; ≺-≼-≺; ≼-≺-≺; ≼-or-≻; ≼-split)
open import denotation.Laws.Count using (child)
open import denotation.Laws.Worlds using (Hots; Ok; Lawful; GoodEnv; W; step; here; ⊑-cmp; ⊑-snoc⁺; ⊑-inside; ⊑-trans; ⊑-≼; ⊕-assoc;
  ⊕-identityʳ; plain-ix; InvAt; ok-step; _⊑_)
open import denotation.Laws.Worlds.Leaves using (of-end)
open import simultaneous.SObs using (lone; module Elaborate; outerB; laneB; closeB)
open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; Input; react; combined; Routes; going; fed; closer; Out)
open import simultaneous.InstEmit using (instEmit; value; mark; laneDone)
open import simultaneous.Routed using (Held; Early; Placed; Adm; Shown; s-value; s-done; s-end)
open import simultaneous.FlatSim using (Sent; react-sent; routed; passed)
open import simultaneous.HeldComb using (ev; init)
open import simultaneous.DenRows using (merge-out; scan-out; of-mem)
open import simultaneous.HeldRead using (merge-end)
open import simultaneous.LaneLocal using (Fit; of-ix)
open import simultaneous.Layers using (pinby-vis)
open import simultaneous.CombSent using (closing-value; closer-good)
open import simultaneous.HeldBase using (EnvHeld; Fresh; Gap; IH; module FlatHots; apart-all; apart-at; gap-hot; fresh-adm)
open import simultaneous.HeldSrc using (module CombSrc; open-value)

------------------------------------------------------------------------
-- Fresh at every extension

module DeepAt {Γ Δ} {ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ} {env : DenEnv Δ} {cs} (eh : EnvHeld ρ env cs) where

  Deep : Pos → Set
  Deep x = ∀ zs → Fresh eh (x ⊕ zs)

  deep-ext : ∀ {x} → Deep x → ∀ zs → Deep (x ⊕ zs)
  deep-ext {x} d zs ws = subst (Fresh eh) (sym (⊕-assoc x zs ws)) (d (zs ++ ws))

  deep-snoc : ∀ {x l} → Deep x → Deep (x ⊕ [ l ])
  deep-snoc d = deep-ext d [ _ ]

  -- A FRESH WORLD POSITION IS FRESH ALL THE WAY DOWN: a gap below it would
  -- hang its `nothing`, a binder's hot row, under the position.
  deep : ∀ {H a x} → Ok H a → (∀ {h} → Hots env h → H h) → W H a x → Fresh eh x → Deep x
  deep {x = x} ok lift w fx zs = apart-all off , λ {c} ci → ≺-≼-≺ {c} {x} {x ⊕ zs} (proj₂ fx ci) (⊑-≼ {x} {x ⊕ zs} (zs , refl))
    where
      off : ∀ {Y} (j : Y ∈ Γ) → Nl.¬ Gap (EnvHeld.bound eh j) (x ⊕ zs)
      off j (c , r , an , h , nl) with ⊑-cmp (c ⊕ [ ix 1 ]) x h (zs , refl)
      ... | inj₂ xc = proj₂ ok (lift (gap-hot eh j an)) w (⊑-inside (⊑-trans xc (⊑-snoc⁺ _)))
      ... | inj₁ cx = apart-at (proj₁ fx) j (c , r , an , cx , λ l → nl (⊑-trans l (zs , refl)))

------------------------------------------------------------------------
-- What a flatMap's scan shows

-- A scan shows a value only where a branch's value arrives, and never a
-- lane's `laneDone`.
private
  no-done : ∀ {B} {x : Maybe (Input B)} {k n} → Sent x (instEmit (mark (laneDone k)) n) → ⊥
  no-done (routed () _)

  out≢end : ∀ {X : Set} {a : X} → out a ≡ end → ⊥
  out≢end ()

-- THE SCAN'S ROWS, over any source: each value one lane below a branch
-- value's row, each end the source's or a lane's past it.
module ScanPlaced {B : Set} (op : FlatOp) (d : Den (Maybe (Input B))) (P : Pos) (F : Pos → Set)
                  (fv : ∀ {q b v n} → enter d P q (out (just (inj₁ (b , instEmit (value v) n)))) → ∀ zs → F (q ⊕ zs))
                  (fe : ∀ {k} → enter d P k end → F k)
                  (fl : ∀ {q a} → enter d P q (out a) → Ended (enter d P) ((q ⊕ [ ix 1 ]) ⊕ [ last ]) → ⊥) where

  Sc : Den (Out B)
  Sc = Op.scan (react op) init d

  Shows : EmissionSet (IE B)
  Shows = enter (Op.flatMap (mergeᶠ nothing) (λ x → Op.of (proj₂ x)) Sc) P

  sent-at : ∀ {y v} → Shows y (out v)
          → Σ Pos λ q → Σ (Maybe (Input B)) λ x → enter d P q (out x) × Sent x v × Σ ℕ λ j → y ≡ (q ⊕ [ ix 1 ]) ⊕ [ ix j ]
  sent-at r with merge-out (λ x → Op.of (proj₂ x)) Sc P r
  ... | q , st , sq , (l , _) , _ with scan-out (react op) init d P sq
  ...   | st₀ , x , dq , refl = q , x , dq , react-sent op st₀ x (of-mem (q ⊕ [ ix 1 ]) 0 _ l) , of-ix (q ⊕ [ ix 1 ]) 0 _ l

  value-at : ∀ {y v n} → Σ Pos (λ q → Σ (Maybe (Input B)) λ x → enter d P q (out x) × Sent x (instEmit (value v) n)
                                     × Σ ℕ λ j → y ≡ (q ⊕ [ ix 1 ]) ⊕ [ ix j ]) → F y
  value-at {v = v} {n} (q , _ , dq , passed refl , j , refl) =
    subst F (sym (⊕-assoc q [ ix 1 ] [ ix j ])) (fv dq (ix 1 ∷ ix j ∷ []))

  done-at : ∀ {y k n} → Σ Pos (λ q → Σ (Maybe (Input B)) λ x → enter d P q (out x) × Sent x (instEmit (mark (laneDone k)) n)
                                    × Σ ℕ λ j → y ≡ (q ⊕ [ ix 1 ]) ⊕ [ ix j ]) → ⊥
  done-at (_ , _ , _ , s , _) = no-done s

  end-at : ∀ {k} → Shows k end → F k
  end-at r with merge-end (λ x → Op.of (proj₂ x)) Sc P r
  ... | inj₁ (Scan.send h , _) = fe h
  ... | inj₂ (q , st , sq , (l , _) , c₀ , (Scan.send h₀ , _) , c₀k) with scan-out (react op) init d P sq | of-end (q ⊕ [ ix 1 ]) 0 _ l
  ...   | _ , _ , dq , _ | refl = ⊥-elim (fl dq (c₀ , h₀ , c₀k))

  placed : Placed F Shows
  placed r s-value = value-at (sent-at r)
  placed r s-done  = ⊥-elim (done-at (sent-at r))
  placed r s-end   = end-at r

-- The scan, as the operators it is.
comb-view : ∀ m {Δ A B} op (tk : Obs Timeline (IE B ∷ IE B ∷ IE A ∷ Δ) (ℕ × Routes)) (env : DenEnv (IE B ∷ IE B ∷ IE A ∷ Δ)) P {y e}
          → enter (ev m (combined op tk) env) P y e
          → enter (Op.flatMap (mergeᶠ nothing) (λ x → Op.of (proj₂ x))
                     (Op.scan (react op) init (ev m (takeWhile false going (flatMap (mergeᶠ nothing) (fed tk) (of (true ∷ false ∷ [])))) env))) P y e
comb-view nothing  op tk env P r = r
comb-view (just n) op tk env P r = r

------------------------------------------------------------------------
-- The flatMap's own scan

module FlatPlaced (m : Maybe ℕ) {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (op : FlatOp) (f : A → Obs Timeline Γ B)
                  (s : Obs Timeline Γ A) (env : DenEnv Δ) (cs : List Pos) (gd : GoodEnv env) (eh : EnvHeld ρ env cs)
                  (hf : ∀ a {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ′) → IH m ρ′ (f a))
                  (p : Pos) (ok : Ok (Hots env) p) (fr : Fresh eh p) (ep : Early p)
                  (H₁ : Held (enter (ev m (FlatHots.trig m ρ op f s env p) (FlatHots.env₀ m ρ op f s env p)) (FlatHots.c m ρ op f s env p ⊕ [ ix 1 ]))
                             ((FlatHots.c m ρ op f s env p ⊕ [ ix 1 ]) ∷ p ∷ cs))
                  (tp : Placed (Fresh eh) (FlatHots.σ₁ m ρ op f s env p))
                  (L₁ : Lawful (FlatHots.σ₁ m ρ op f s env p)) (L₂ : Lawful (FlatHots.σ₂ m ρ op f s env p))
                  (L₃ : Lawful (FlatHots.σ₃ m ρ op f s env p))
                  (ok₁ : Ok (Hots (hot (FlatHots.σ₁ m ρ op f s env p) ∷ FlatHots.env₀ m ρ op f s env p)) (FlatHots.p₀ m ρ op f s env p))
                  (ok₂ : Ok (Hots (hot (FlatHots.σ₂ m ρ op f s env p) ∷ hot (FlatHots.σ₁ m ρ op f s env p) ∷ FlatHots.env₀ m ρ op f s env p))
                            (FlatHots.p₀₀ m ρ op f s env p))
                  (ok₃ : Ok (Hots (FlatHots.env′ m ρ op f s env p)) (FlatHots.P m ρ op f s env p))
                  (ep₃ : Early (FlatHots.P m ρ op f s env p)) where
  open FlatHots m ρ op f s env p
  open CombSrc m ρ op f s env cs gd eh hf p ok fr ep H₁ tp L₁ L₂ L₃ ok₁ ok₂ ok₃ ep₃
  open DeepAt eh

  -- The flatMap's own first step, one plain step into its world.
  deep-c : Deep c
  deep-c = deep ok (λ h → h) (step here plain-ix) (Adm.bare (fresh-adm eh) fr λ ())

  deep-P : Deep P
  deep-P = deep-snoc (deep-snoc (deep-snoc deep-c))

  -- Every shown row of the outer, the real flatMap and the closer.
  deep₁ : ∀ {y e} → σ₁ y e → Shown e → Deep y
  deep₁ r sh = deep (ok-step c ok₀′) inj₂ (InvAt.world I₁ (proj₁ r)) (tp r sh)

  deep₃ : ∀ {y e} → σ₃ y e → Shown e → Deep y
  deep₃ r sh = deep (ok-step p₀₀ ok₂) (λ h → inj₂ (inj₂ (inj₂ h))) (InvAt.world I₃ (proj₁ r)) (Fit.placed lane-fit r sh)

  deep₂ : ∀ {y} → σ₂ y end → Deep y
  deep₂ (r , _) = closer-good m σ₁ env₀ L₁ Deep deep-ext (λ y → deep₁ y s-end) (p₀ ⊕ [ ix 1 ]) (deep-snoc (deep-snoc deep-c)) r

  -- A branch's value: only the real flatMap's, one join below its row.
  fv : ∀ {q b v n} → M q (out (just (inj₁ (b , instEmit (value v) n)))) → Deep q
  fv {b = outerB} x with outer-sent x
  ... | _ , _ , _ , _ , o , _ = ⊥-elim (open-value o)
  fv {b = laneB} x with lane-sent x
  ... | _ , _ , y , refl = deep-snoc (deep₃ y s-value)
  fv {b = closeB} x with close-sent x
  ... | _ , _ , y , _ = ⊥-elim (closing-value (close-marks y))

  -- The source's end: under its subscription, or past a branch's end.
  fe : ∀ {k} → M k end → Fresh eh k
  fe x with m-ends x
  ... | inj₁ (zs , refl)                 = deep-P zs
  ... | inj₂ (_ , zs , b-outer y , refl) = deep-snoc (deep₁ y s-end) zs
  ... | inj₂ (_ , zs , b-lane y , refl)  = deep-snoc (deep₃ y s-end) zs
  ... | inj₂ (_ , zs , b-close y , refl) = deep-snoc (deep₂ y) zs

  -- Nothing of the source lies under one of its rows.
  no-under : ∀ {q a c₀} → M q (out a) → M c₀ end → q ⊑ c₀ → ⊥
  no-under {q} xq xe ([] , refl)    = out≢end (InvAt.func I-M xq (subst (λ z → M z end) (⊕-identityʳ q) xe))
  no-under xq xe (_ ∷ _ , refl)     = InvAt.flat I-M xq xe

  -- A lane of the scan ends before its source does.
  fl : ∀ {q a} → M q (out a) → Ended M ((q ⊕ [ ix 1 ]) ⊕ [ last ]) → ⊥
  fl {q} xq (c₀ , xe , c₀k) with ≼-or-≻ c₀ q
  ... | inj₁ c₀q with ≼-split {c₀} {q} c₀q
  ...   | inj₁ lt   = pinby-vis tt (InvAt.quiet I-M xe xq lt)
  ...   | inj₂ refl = out≢end (InvAt.func I-M xq xe)
  fl {q} xq (c₀ , xe , c₀k) | inj₂ qc₀ with child (ix 1) qc₀
  ... | inj₁ qc = no-under xq xe qc
  ... | inj₂ q₁c with child last q₁c
  ...   | inj₁ q₁c′ = no-under xq xe (⊑-trans (⊑-snoc⁺ q) q₁c′)
  ...   | inj₂ kc   = ≺-irrefl {c₀} (≼-≺-≺ {c₀} {(q ⊕ [ ix 1 ]) ⊕ [ last ]} {c₀} c₀k kc)

  placed : Placed (Fresh eh) scanned
  placed r sh = ScanPlaced.placed op (ev m src env′) P (Fresh eh) fv fe fl (comb-view m op tk env′ P r) sh
