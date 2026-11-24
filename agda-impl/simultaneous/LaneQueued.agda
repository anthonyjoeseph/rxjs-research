{-# OPTIONS --guardedness #-}

-- A QUEUED LANE'S BURST IS HANDED ROUTES AT A LANE'S END (`queued-hand`).
-- A queued lane subscribes at an earlier lane's end; the chain of such
-- ends runs down to one outside its own lane's burst (`Base`), whose
-- `laneDone` hands the scan the routes that lane counted.  Every row read
-- from there to the queued lane's row lies in that end's instant, each
-- lane end there finds the next lane queued, and no burst's end there
-- finds its lane running.
module simultaneous.LaneQueued where

import Data.List as L
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Relation.Unary.All using (_∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just)
open import Data.Nat using (ℕ; zero; suc; _+_)
import Data.Nat as ℕ
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; FlatOp)
open import denotation.Position using (Pos; root; _≟ᵖ_; ix; sub; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (DenEnv; out; end; enter; hot; _≺_)
open import denotation.Laws.Worlds using (Hots; GoodEnv; Ok; Lawful)
open import simultaneous.SObs using (lone; module Elaborate; Flat; isZero)
open import Data.Nat.Properties using (m+n≡0⇒n≡0)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (_∧_)
open import simultaneous.InstEmit using (instEmit; mark; laneDone; burstEnd)
open import simultaneous.Relations using (Met)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Routed using (Held; Early; Placed; Ex; Sync; Carried; nameOf)
open import simultaneous.FlatLanes using (Tg)
open import simultaneous.LaneSplit using (Ln)
open import simultaneous.HeldBase using (EnvHeld; module FlatHots; IH; Fresh)
open import simultaneous.HeldComb using (ev; init; past)
open import simultaneous.FlatHeld using (LD)
open import simultaneous.HeldSrc using (module CombSrc)
open import simultaneous.HeldLanes using (module CombLanes)
open import simultaneous.HeldLaneRoutes using (module LaneRoutes)
open import simultaneous.LaneChain using (module Chains)
open import simultaneous.LaneLocal using (inv-ev)
open import simultaneous.InstEmit using (valuesOf)
open import denotation.Laws.Worlds using (ok-step)
open import Data.List.Membership.Propositional.Properties using (∈-∃++)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Properties using (++-assoc)
open import denotation.Read using (Run; _∷_)
open import denotation.EmissionSet using (EmissionSet; Ev)
open import simultaneous.Layers using (run-after)
open import simultaneous.Instants using (btw)
open import simultaneous.TakeCut using (inst-⊕)
open import simultaneous.LaneHold using (module LaneHold)
open import simultaneous.LaneEpoch using (module Lanes)
open import simultaneous.HeldKeep using (Named; names-of; spent-on)
open import simultaneous.FlatHeld using (past-app)
open import simultaneous.Routed using (nm)
open import simultaneous.InstEmit using (laneStart)
open import simultaneous.Layers using (run-row)
open import denotation.Position using (_∙_)
open import Data.List.Properties using (∷-injective)
open import Data.Sum using ([_,_]′)
open import Data.Unit using (tt)
open import Data.List.Membership.Propositional using (find)
open import Data.List.Membership.Propositional using (lose)
open import denotation.Position using (last)
open import denotation.Laws.Worlds using (InvAt; _⊑_; ⊑-inside; inside-⊑; ⊑-snoc; ⊑-snoc⁺; ⊑-trans; world-after)
open import denotation.Laws.Modulus using (≺-irrefl)
open import denotation.Laws.BoundedInv using (end-uniq)
open import simultaneous.HeldLanes using (lane-take)
open import Relation.Nullary using (yes; no)
open import Tree using (mergeᶠ; connected)
open import simultaneous.ScanCount using (past-queue; markQue; que-cut)
open import simultaneous.LaneCount using (kStart)
open import simultaneous.InstEmit using (outerOpen; value)
open import Data.List.Relation.Unary.Any using (Any)
open import denotation.Laws.Modulus using (≺-trans; ≺-ext; ≼-≺-≺; ≺→≼)
open import denotation.Laws.Worlds using (conv; ⊑-≼; ⊑-refl; ⊑-cmp; ⊕-injˡ; W; W⁼; inW; w-up; plain-ix)
open import denotation.Laws.Modulus using (≼-or-≻; ≺-≼-≺)
open import simultaneous.HeldLanes using (bproj-mem)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (AIE; IE; Input; react; each; laneˢ; cut; ended; anyHolds; undone)

module Queued (m : Maybe ℕ) {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (op : FlatOp) (f : A → Obs Timeline Γ B)
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
  open CombSrc m ρ op f s env cs gd eh hf p ok fr ep H₁ tp L₁ L₂ L₃ ok₁ ok₂ ok₃ ep₃ using (cs′; module LS; module OS; g₂; named; met-before; lane-run)
  open CombLanes m ρ op f s env cs gd eh hf p ok fr ep H₁ tp L₁ L₂ L₃ ok₁ ok₂ ok₃ ep₃
    using (Row; RO; module RV; sub-at; fL; done-ends; no-end; Own; LaneMark; DoneMark; act; ro-row; ro-at; J≺ro; met-open; OpenMark; open-one; start-live; ro-func; lane-done-own; lane-fresh-own)
  open LaneRoutes m ρ op f s env cs gd eh hf p ok fr ep H₁ tp L₁ L₂ L₃ ok₁ ok₂ ok₃ ep₃
    using (lane-end-done; St; LaneEmit; done-told; next-idle; own-snoc; lane-rows; cnt-lane; module QL; catch-by; in-prefix; out-pin)
  open LaneHold m ρ op f s env cs gd eh hf p ok fr ep H₁ tp L₁ L₂ L₃ ok₁ ok₂ ok₃ ep₃
    using (OvBefore; Live?; lanes-at; lanes-floor; done-live)
  open Lanes {B} op Own (LaneMark laneStart) DoneMark act LaneEmit using (oc-total; OC; oc-in)

  -- ROUTES HANDED AT A LANE'S END, held to a row `z` past it: the
  -- `laneDone` read at `d` leaves routes held of `z`'s instant, and every
  -- row read after it lies in that instant, each lane end there finding a
  -- lane queued or the last lane done, each burst's end its lane done.
  record Hand (rx₁ : List Row) (z : Pos) : Set where
    field
      r₁ r₂ : List Row
      d     : Pos
      xd    : Maybe (Input B)
      split : rx₁ ≡ r₁ ++ (d , out xd) ∷ r₂
      ld    : LD xd
      held  : ¬ Flat.held (proj₁ (react op (past op init r₁) xd)) ≡ 0
      at    : Flat.at (proj₁ (react op (past op init r₁) xd)) ≡ nameOf z
      inst  : ∀ {k e} → (k , e) ∈ r₂ → instantOf k ≡ instantOf z
      dones : ∀ a {k b kd n} c → r₂ ≡ a ++ (k , out (Tg b (instEmit (mark (laneDone kd)) n))) ∷ c
            → let S = proj₁ (past op (react op (past op init r₁) xd) a) in
              ¬ Flat.queue S ≡ 0 ⊎ (Flat.finished S ≡ true × Flat.active S ℕ.∸ 1 ≡ 0)
      bursts : ∀ a {k b n} c → r₂ ≡ a ++ (k , out (Tg b (instEmit (mark burstEnd) n))) ∷ c
             → Flat.dead (proj₁ (past op (react op (past op init r₁) xd) a)) ≡ true

  -- A queued lane's row in its burst, as the scan's source reads it.
  record Target (rx₁ : List Row) : Set₁ where
    field
      {y Q} : Pos
      {v}   : IE B
      {a}   : A
      {rx₂} : List Row
      mt  : Met M (rx₁ ++ (y ⊕ [ sub LS.J ] , out (Ln v)) ∷ rx₂)
      xo  : RO Q (out a)
      l   : RV.Lane op Q a y (out v)
      nq  : ¬ sub-at xo l ≡ Q ⊕ [ ix 1 ]
      sy  : Sync (sub-at xo l) y
      car : Carried (out v)
      nx  : ¬ Ex cs′ (y ⊕ [ sub LS.J ])
      Ov  : Set
      ovf : OvBefore rx₁ (y ⊕ [ sub LS.J ]) Ov
      res : Live? rx₁ Ov

    z : Pos
    z = y ⊕ [ sub LS.J ]

    sb : Pos
    sb = sub-at xo l

  -- The real flatMap's chains of lane ends.
  module CH = Chains (ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀)) fL
    (inv-ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂) (λ a → inv-ev m (laneˢ (g a)) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂)
    (p₀₀ ⊕ [ ix 1 ]) (ok-step p₀₀ ok₂)

  -- THE CHAIN'S BASE, AS THE SCAN READS IT: at `d`, the `laneDone` of the
  -- lane ending outside its subscription that starts the chain to `sb`.
  record Base (sb d : Pos) (xd : Maybe (Input B)) : Set where
    field
      base  : CH.Base op sb
      {y₀ n₀} : Pos
      {kd}  : ℕ
      ld₀   : RV.Lane op (CH.Base.q₀ base) (CH.Base.a₀ base) y₀ (out (instEmit (mark (laneDone kd)) n₀))
      at₀   : d ≡ y₀ ⊕ [ sub LS.J ]
      xd₀   : xd ≡ Ln (instEmit (mark (laneDone kd)) n₀)
      done₀ : y₀ ≺ CH.Base.c₀ base
      inst₀ : instantOf y₀ ≡ instantOf (CH.Base.c₀ base)

  -- The scan past the base's `laneDone`.
  After : List Row → Maybe (Input B) → List Row → Flat Pos
  After r₁ xd a = proj₁ (past op (react op (past op init r₁) xd) a)

  -- NO ENVIRONMENT BURST STARTS AT A LANE'S `laneDone`: the binders list
  -- only subscriptions before the lane's, which lies before its rows.
  done-unlisted : ∀ {q a y kd n} → RO q (out a) → RV.Lane op q a y (out (instEmit (mark (laneDone kd)) n)) → y ∈ cs → ⊥
  done-unlisted {y = y} xo ld ci = ≺-irrefl {y} (≺-trans {y} {CH.subOf op xo ld} {y} (proj₂ (lane-fresh-own xo ld) ci)
    (world-after (InvAt.world (CH.sub-inv op xo ld) (CH.sub-row op xo ld ld)) (InvAt.real (CH.sub-inv op xo ld) (CH.sub-row op xo ld ld))))

  postulate
    -- A LANE END READ PAST THE BASE FINDS A LANE QUEUED: the lanes of
    -- the chain end one by one, each with the next opened and unstarted,
    -- and no other lane's row lies under the base's end.
    hand-dones : ∀ rx₁ (T : Target rx₁) r₁ {d xd} r₂ → rx₁ ≡ r₁ ++ (d , out xd) ∷ r₂ → Base (Target.sb T) d xd
               → ∀ a {k b kd n} c → r₂ ≡ a ++ (k , out (Tg b (instEmit (mark (laneDone kd)) n))) ∷ c
               → ¬ Flat.queue (After r₁ xd a) ≡ 0 ⊎ (Flat.finished (After r₁ xd a) ≡ true × Flat.active (After r₁ xd a) ℕ.∸ 1 ≡ 0)

    -- NO BURST'S END IS READ PAST THE BASE WITH ITS LANE RUNNING: the
    -- lanes of the chain end in their bursts, and the queued lane's burst
    -- holds its row.
    hand-bursts : ∀ rx₁ (T : Target rx₁) r₁ {d xd} r₂ → rx₁ ≡ r₁ ++ (d , out xd) ∷ r₂ → Base (Target.sb T) d xd
                → ∀ a {k b n} c → r₂ ≡ a ++ (k , out (Tg b (instEmit (mark burstEnd) n))) ∷ c
                → Flat.dead (After r₁ xd a) ≡ true

  -- NO VALUE LIES BETWEEN A LANE'S `laneDone` AND ITS END: the two
  -- stand beside each other at the lane's take point, in the lane's
  -- world, where no value lies.
  done-ahead : ∀ {q a y kd n c q′ a′} → RO q (out a) → RV.Lane op q a y (out (instEmit (mark (laneDone kd)) n)) → RV.Lane op q a c end
             → RO q′ (out a′) → q′ ≺ c → q′ ≺ y
  done-ahead {y = y} {c = c} {q′ = q′} x ld lc x′ qc with ≼-or-≻ y q′
  ... | inj₂ lt = lt
  ... | inj₁ le = ⊥-elim (CH.past-lane op x ld ww x′ (conv {w} {y} {q′} {c} ([ ix 0 ] , ey) le qc ([ last ] , ec)))
    where
      S : Pos
      S = CH.subOf op x ld

      tp₀ = lane-take m undone _ (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂ S (CH.sub-ok op x ld) (CH.sub-row op x ld ld) tt

      w : Pos
      w = proj₁ tp₀

      ey : y ≡ w ⊕ [ ix 0 ]
      ey = proj₁ (proj₂ tp₀)

      ec : c ≡ w ⊕ [ last ]
      ec = end-uniq (CH.sub-inv op x ld) (CH.sub-row op x ld lc) (proj₂ (proj₂ tp₀))

      wy : W (Hots (hot σ₂ ∷ hot σ₁ ∷ env₀)) S y
      wy = InvAt.world (CH.sub-inv op x ld) (CH.sub-row op x ld ld)

      ww : W⁼ (Hots (hot σ₂ ∷ hot σ₁ ∷ env₀)) S w
      ww = [ (λ e → ⊥-elim (≺-irrefl {S} (subst (S ≺_) (trans ey (sym e)) (world-after wy (InvAt.real (CH.sub-inv op x ld) (CH.sub-row op x ld ld))))))
           , (λ v → v) ]′ (w-up plain-ix (inW (subst (W (Hots (hot σ₂ ∷ hot σ₁ ∷ env₀)) S) ey wy)))

  -- THE BASE LANE'S TAKE POINT: its `laneDone` and end stand beside each
  -- other there, the `laneDone` first.
  module TakePoint {s} (B₀ : CH.Base op s) {y₀ kd n₀} (ld₀ : RV.Lane op (CH.Base.q₀ B₀) (CH.Base.a₀ B₀) y₀ (out (instEmit (mark (laneDone kd)) n₀)))
                   (yc : y₀ ≺ CH.Base.c₀ B₀) where
    x₀′ : RO (CH.Base.q₀ B₀) (out (CH.Base.a₀ B₀))
    x₀′ = CH.Base.x₀ B₀

    -- The base lane's subscription.
    S₀ : Pos
    S₀ = CH.subOf op x₀′ (CH.Base.l₀ B₀)

    -- THE `laneDone` LIES BESIDE THE END: the lane is a take, failing at
    -- its `laneDone` and ending beside it.
    sib : Σ Pos λ w → y₀ ≡ w ⊕ [ ix 0 ] × CH.Base.c₀ B₀ ≡ w ⊕ [ last ]
    sib = let (w , e , r) = lane-take m undone _ (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂ S₀ (CH.sub-ok op x₀′ (CH.Base.l₀ B₀))
                              (CH.sub-row op x₀′ (CH.Base.l₀ B₀) ld₀) tt
          in w , e , end-uniq (CH.sub-inv op x₀′ (CH.Base.l₀ B₀)) (CH.sub-row op x₀′ (CH.Base.l₀ B₀) (CH.Base.l₀ B₀)) r

    w₀ : Pos
    w₀ = proj₁ sib

    -- So the `laneDone` is not over the end.
    beside : y₀ ⊑ CH.Base.c₀ B₀ → ⊥
    beside h with ⊑-snoc w₀ (subst (y₀ ⊑_) (proj₂ (proj₂ sib)) h)
    ... | inj₁ h′ = ≺-irrefl {y₀} (≼-≺-≺ {y₀} {w₀} {y₀} (⊑-≼ h′) (subst (w₀ ≺_) (sym (proj₁ (proj₂ sib))) (≺-ext w₀ [])))
    ... | inj₂ e  = ≺-irrefl {y₀} (subst (y₀ ≺_) (sym (trans e (sym (proj₂ (proj₂ sib))))) yc)

  -- THE BASE'S `laneDone` IS MET BEFORE THE QUEUED LANE'S ROW: it lies
  -- before the base's end, below the chain's subscriptions, so before
  -- the row, and the lanes, never cut in a bounded merge, show it.
  base-read : ∀ rx₁ (T : Target rx₁) (B₀ : CH.Base op (Target.sb T)) {y₀ kd n₀}
            → RV.Lane op (CH.Base.q₀ B₀) (CH.Base.a₀ B₀) y₀ (out (instEmit (mark (laneDone kd)) n₀)) → y₀ ≺ CH.Base.c₀ B₀
            → (y₀ ⊕ [ sub LS.J ] , out (Ln (instEmit (mark (laneDone kd)) n₀))) ∈ rx₁
  base-read rx₁ T B₀ {y₀} ld₀ yc =
    let (rs , pr , run , _) = lane-run mt
        (y′ , e′ , j) = bproj-mem pr (∈-++⁺ʳ rx₁ (here refl))
        bd = proj₂ (CH.bounded op xo l nq)
    in in-prefix rx₁ mt
         (catch-by pr run (CH.Base.x₀ B₀) (CH.runs-of op bd (CH.Base.l₀ B₀)) ld₀ (CH.uncut-of op bd)
           (subst (λ w → (w , out v) ∈ rs) (sym (⊕-injˡ y y′ e′)) j) out-pin y₀y)
         jy
    where
      open Target T
      open TakePoint B₀ ld₀ yc using (beside)

      c₀y : CH.Base.c₀ B₀ ⊑ y
      c₀y = ⊑-trans (CH.chain-⊑ (CH.Base.chain B₀)) (inside-⊑ sb y (proj₁ sy))

      y₀y : y₀ ≺ y
      y₀y = ≺-≼-≺ {y₀} {CH.Base.c₀ B₀} {y} yc (⊑-≼ c₀y)

      jy : (y₀ ⊕ [ sub LS.J ]) ≺ (y ⊕ [ sub LS.J ])
      jy with ≼-or-≻ (y ⊕ [ sub LS.J ]) (y₀ ⊕ [ sub LS.J ])
      ... | inj₂ lt = lt
      ... | inj₁ le with ⊑-cmp y₀ (CH.Base.c₀ B₀)
                           (conv {y₀} {y₀} {y} {y₀ ⊕ [ sub LS.J ]} (⊑-refl y₀) (≺→≼ {y₀} {y} y₀y)
                             (≺-≼-≺ {y} {y ⊕ [ sub LS.J ]} {y₀ ⊕ [ sub LS.J ]} (≺-ext y []) le) (⊑-snoc⁺ y₀)) c₀y
      ...   | inj₁ h = ⊥-elim (beside h)
      ...   | inj₂ h = ⊥-elim (≺-irrefl {y₀} (≺-≼-≺ {y₀} {CH.Base.c₀ B₀} {y₀} yc (⊑-≼ h)))

  -- A QUEUED LANE'S CHAIN HAS A BASE, MET BEFORE ITS ROW.
  hand-base : ∀ rx₁ (T : Target rx₁) → Σ (List Row) λ r₁ → Σ Pos λ d → Σ (Maybe (Input B)) λ xd → Σ (List Row) λ r₂
            → rx₁ ≡ r₁ ++ (d , out xd) ∷ r₂ × Base (Target.sb T) d xd
  hand-base rx₁ T =
    let B₀ = CH.base op (Target.xo T) (Target.l T) (Target.nq T)
        (y₀ , kd , n₀ , ld₀ , yc) = lane-end-done (CH.Base.x₀ B₀) (CH.Base.l₀ B₀)
        (r₁ , r₂ , sp) = ∈-∃++ (base-read rx₁ T B₀ ld₀ yc)
        (c′ , l′ , ic , _) = done-ends (CH.Base.x₀ B₀) ld₀
    in r₁ , _ , _ , r₂ , sp
     , record { base = B₀ ; ld₀ = ld₀ ; at₀ = refl ; xd₀ = refl ; done₀ = yc
              ; inst₀ = trans (sym ic) (cong instantOf (CH.end-one op (CH.Base.x₀ B₀) l′ (CH.Base.l₀ B₀))) }

  -- Rows of a run between two of its rows lie between them.
  run-btw : ∀ {X} {t : EmissionSet X} {c} r₁ {d e₁} r₂ {z e₂ r₃ k e} → Run t c (r₁ ++ (d , e₁) ∷ (r₂ ++ (z , e₂) ∷ r₃)) → (k , e) ∈ r₂ → d ≺ k × k ≺ z
  run-btw (_ ∷ r₁) r₂ (_ ∷ run) i = run-btw r₁ r₂ run i
  run-btw {X} {t} []       r₂ (_ ∷ run) i = run-after run (∈-++⁺ˡ i) , below r₂ run i
    where
      below : ∀ {c′} r {z : Pos} {e₂ : Ev X} {r₃ k e} → Run t c′ (r ++ (z , e₂) ∷ r₃) → (k , e) ∈ r → k ≺ z
      below (_ ∷ r) (_ ∷ run′) (here refl) = run-after run′ (∈-++⁺ʳ r (here refl))
      below (_ ∷ r) (_ ∷ run′) (there j)   = below r run′ j

  -- THE BASE'S `laneDone` LIES IN THE ROW'S INSTANT: the base's end is
  -- in it, and the chain stays there.
  base-inst : ∀ rx₁ (T : Target rx₁) {d xd} → Base (Target.sb T) d xd → instantOf d ≡ instantOf (Target.z T)
  base-inst rx₁ T B₀ =
    let open Target T in
    trans (cong instantOf (Base.at₀ B₀)) (trans (inst-⊕ (Base.y₀ B₀) [ sub LS.J ]) (trans (Base.inst₀ B₀)
      (trans (sym (CH.chain-inst (CH.Base.chain (Base.base B₀)))) (trans (sym (cong instantOf (proj₂ sy))) (sym (inst-⊕ y [ sub LS.J ]))))))

  -- EVERY ROW READ PAST THE BASE LIES IN THE ROW'S INSTANT.
  hand-inst : ∀ rx₁ (T : Target rx₁) r₁ {d xd} r₂ → rx₁ ≡ r₁ ++ (d , out xd) ∷ r₂ → Base (Target.sb T) d xd
            → ∀ {k e} → (k , e) ∈ r₂ → instantOf k ≡ instantOf (Target.z T)
  hand-inst rx₁ T r₁ {d} {xd} r₂ refl B₀ {k} i =
    let open Target T
        (dk , kz) = run-btw r₁ r₂ (subst (Met M) (++-assoc r₁ ((d , out xd) ∷ r₂) ((z , out (Ln v)) ∷ rx₂)) mt) i
        dz = base-inst rx₁ T B₀
    in trans (btw d k z dk kz dz) dz

  -- A count not none is one at least.
  pos : ∀ {k} → ¬ k ≡ 0 → 1 ℕ.≤ k
  pos {zero}  nz = ⊥-elim (nz refl)
  pos {suc _} _  = ℕ.s≤s ℕ.z≤n

  -- THE BASE'S `laneDone`, AS THE LANES COUNTER READS IT: a lane's emit,
  -- telling a count of the row's instant that is not none.
  module AtBase (rx₁ : List Row) (T : Target rx₁) (r₁ : List Row) {d xd} (r₂ : List Row) (sp : rx₁ ≡ r₁ ++ (d , out xd) ∷ r₂)
                (B₀ : Base (Target.sb T) d xd) where
    open Target T
    open Base B₀

    mt′ : Met M (r₁ ++ (d , out xd) ∷ (r₂ ++ (z , out (Ln v)) ∷ rx₂))
    mt′ = subst (Met M) (trans (cong (_++ (z , out (Ln v)) ∷ rx₂) sp) (++-assoc r₁ ((d , out xd) ∷ r₂) ((z , out (Ln v)) ∷ rx₂))) mt

    le : LaneEmit (CH.Base.q₀ base) (d , out xd) (instEmit (mark (laneDone kd)) n₀)
    le = CH.Base.a₀ base , y₀ , CH.Base.x₀ base , cong₂, at₀ (cong out xd₀) , ld₀
      where
        cong₂, : ∀ {X Y : Set} {x x′ : X} {w w′ : Y} → x ≡ x′ → w ≡ w′ → (x , w) ≡ (x′ , w′)
        cong₂, refl refl = refl

    dz : nameOf d ≡ nameOf z
    dz = cong (λ w → nm (w ∙ [])) (base-inst rx₁ T B₀)

    open TakePoint base ld₀ done₀ public

    -- SO IT LIES OUTSIDE ITS SUBSCRIPTION'S BURST, as the end does: what
    -- leads it, past the subscription, leads the end.
    ns : ¬ Sync S₀ y₀
    ns (ins , rt) = CH.Base.out₀ base (⊑-inside (in-end (⊑-snoc w₀ (subst (S₀ ⊑_) e (inside-⊑ S₀ y₀ ins)))) , trans (cong (_∙ []) (sym inst₀)) rt)
      where
        e  = proj₁ (proj₂ sib)
        ce = proj₂ (proj₂ sib)

        before : S₀ ≺ y₀
        before = world-after (InvAt.world (CH.sub-inv op x₀′ (CH.Base.l₀ base)) (CH.sub-row op x₀′ (CH.Base.l₀ base) ld₀))
                   (InvAt.real (CH.sub-inv op x₀′ (CH.Base.l₀ base)) (CH.sub-row op x₀′ (CH.Base.l₀ base) ld₀))

        in-end : S₀ ⊑ w₀ ⊎ S₀ ≡ w₀ ⊕ [ ix 0 ] → S₀ ⊑ CH.Base.c₀ base
        in-end (inj₁ h) = subst (S₀ ⊑_) (sym ce) (⊑-trans h (⊑-snoc⁺ w₀))
        in-end (inj₂ q) = ⊥-elim (≺-irrefl {S₀} (subst (S₀ ≺_) (trans e (sym q)) before))

    -- AND IN NO ENVIRONMENT BURST: one leading the end leads the chain to
    -- the queued lane's row, which none exempts.
    free : ¬ Ex cs y₀
    free ex with find ex
    ... | c′ , ci , (ins , rt) with ⊑-snoc w₀ (subst (c′ ⊑_) (proj₁ (proj₂ sib)) (inside-⊑ c′ y₀ ins))
    ...   | inj₂ q = done-unlisted x₀′ ld₀ (subst (_∈ cs) (trans q (sym (proj₁ (proj₂ sib)))) ci)
    ...   | inj₁ h = nx (there (there (there (there (there (lose ci (⊑-inside cz , rz)))))))
      where
        cz : c′ ⊑ z
        cz = ⊑-trans (⊑-trans (⊑-trans (subst (c′ ⊑_) (sym (proj₂ (proj₂ sib))) (⊑-trans h (⊑-snoc⁺ w₀))) (CH.chain-⊑ (CH.Base.chain base)))
               (inside-⊑ _ y (proj₁ sy))) (⊑-snoc⁺ y)

        rz : (instantOf z ∙ []) ≡ (instantOf c′ ∙ [])
        rz = trans (cong (_∙ []) (trans (sym (base-inst rx₁ T B₀)) (trans (cong instantOf at₀) (inst-⊕ y₀ [ sub LS.J ])))) rt

    -- THE BASE LANE ENDS HOLDING A ROUTE: its `laneDone`, outside its
    -- burst and every exemption, is covered.
    holds : ∀ {c} (oc : OC (CH.Base.q₀ base) r₁ c) → Σ ℕ λ k → proj₂ c ≡ suc k
    holds oc =
      let (k , e) = lane-done-own x₀′ ld₀ (lane-rows oc) (own-snoc r₁ mt′ x₀′ oc le)
                      (subst (λ s′ → ¬ Sync s′ y₀) (sym (CH.sub-one op x₀′ ld₀ (CH.Base.l₀ base))) ns) free
      in k , trans (sym (cong proj₂ (cnt-lane oc))) (cong proj₂ e)

    kd≥1 : 1 ℕ.≤ kd
    kd≥1 = pos λ k0 → oc-total (CH.Base.q₀ base) r₁ λ (c , oc) →
      let (k , e) = holds oc in 0≢suc (trans (sym k0) (trans (sym (done-told rx₁ mt r₁ (d , out xd) r₂ sp le oc)) e))
      where
        0≢suc : ∀ {k} → 0 ≡ suc k → ⊥
        0≢suc ()

    -- What the lane's count tells there.
    told : ∀ {c} → OC (CH.Base.q₀ base) r₁ c → proj₁ c ≡ nameOf d × ¬ proj₂ c ≡ 0
    told {c} oc = [ (λ e → ⊥-elim (nz e)) , (λ e → e) ]′ (next-idle r₁ mt′ le oc) , nz
      where
        nz : ¬ proj₂ c ≡ 0
        nz e with holds oc
        ... | k , e′ with trans (sym e) e′
        ...   | ()

    -- The scan, past the base's `laneDone`, has read only rows of the
    -- row's instant, and begins none of another.
    inst-of : ∀ r {q x} r′ → (d , out xd) ∷ r₂ ≡ r ++ (q , out x) ∷ r′ → instantOf q ≡ instantOf z
    inst-of [] r′ eq = trans (cong instantOf (sym (cong proj₁ (proj₁ (∷-injective eq))))) (base-inst rx₁ T B₀)
    inst-of (_ ∷ r) r′ eq = hand-inst rx₁ T r₁ r₂ sp B₀ (subst (_ ∈_) (sym (proj₂ (∷-injective eq))) (∈-++⁺ʳ r (here refl)))

    named-on : Named (nameOf z) ((d , out xd) ∷ r₂)
    named-on r {q} {x} r′ eq = names-of x λ { refl → trans (named (proj₁ (run-row mt (∈-++⁺ˡ i)))) (cong (λ w → nm (w ∙ [])) (inst-of r r′ eq)) }
      where
        i : (q , out x) ∈ rx₁
        i = subst (_ ∈_) (sym sp) (∈-++⁺ʳ r₁ (subst (_ ∈_) (sym eq) (∈-++⁺ʳ r (here refl))))

  -- THE SCAN IS AT THE ROW'S INSTANT BY THE BASE'S `laneDone`: the base
  -- lane, live there, holds a route of that instant (`lanes-at`).
  base-at : ∀ rx₁ (T : Target rx₁) r₁ {d xd} r₂ → rx₁ ≡ r₁ ++ (d , out xd) ∷ r₂ → (B₀ : Base (Target.sb T) d xd)
          → Flat.at (proj₁ (past op init r₁)) ≡ nameOf (Target.z T)
  base-at rx₁ T r₁ r₂ sp B₀ with Flat.at (St r₁) ≟ᵖ nameOf (Target.z T)
  ... | yes e = e
  ... | no ne = ⊥-elim (oc-total (CH.Base.q₀ (Base.base B₀)) r₁ λ (c , oc) →
                  let (nmc , nz) = AB.told oc in ne (trans (lanes-at r₁ AB.mt′ (done-live r₁ AB.mt′ AB.le) oc nmc nz) AB.dz))
    where
      module AB = AtBase rx₁ T r₁ r₂ sp B₀

  -- THE SCAN HOLDS THE BASE LANE'S ROUTES: the lanes counter keeps the
  -- route of the row's instant the live base lane holds (`lanes-floor`),
  -- the scan not spent by an over it meets.
  base-lanes : ∀ rx₁ (T : Target rx₁) r₁ {d xd} r₂ → rx₁ ≡ r₁ ++ (d , out xd) ∷ r₂ → (B₀ : Base (Target.sb T) d xd)
             → 1 ℕ.≤ Flat.lanes (proj₁ (past op init r₁))
  base-lanes rx₁ T r₁ {d} {xd} r₂ sp B₀ with Flat.lanes (St r₁) ℕ.≟ 0
  ... | no nz = pos nz
  ... | yes z₀ = ⊥-elim (oc-total (CH.Base.q₀ (Base.base B₀)) r₁ λ (c , oc) →
                   let (nmc , nz) = AB.told oc
                   in lanes-floor r₁ (Target.Ov T) AB.mt′ (done-live r₁ AB.mt′ AB.le) oc nmc nz ovf′ res′ z₀)
    where
      module AB = AtBase rx₁ T r₁ r₂ sp B₀
      open Target T using (Ov; ovf; res; mt; z)

      ovf′ : OvBefore r₁ d Ov
      ovf′ i ik = ovf (subst (_ ∈_) (sym sp) (∈-++⁺ˡ i)) (trans ik (base-inst rx₁ T B₀))

      past≡ : past op init rx₁ ≡ past op (past op init r₁) ((d , out xd) ∷ r₂)
      past≡ = trans (cong (past op init) sp) (past-app op init r₁ (no-end rx₁ mt r₁ sp))

      t≢f : true ≡ false → ⊥
      t≢f ()

      res′ : Live? r₁ Ov
      res′ (inj₁ e) = e
      res′ (inj₂ ov) with Flat.spent (St r₁) in e
      ... | false = refl
      ... | true  = ⊥-elim (t≢f (trans (sym (subst (λ S → Flat.spent (proj₁ S) ≡ true) (sym past≡)
                      (spent-on op (nameOf z) (past op init r₁) ((d , out xd) ∷ r₂) AB.named-on (base-at rx₁ T r₁ r₂ sp B₀) e)))
                      (res (inj₂ ov))))

  -- AT THE BASE'S `laneDone` THE QUEUED LANE IS STILL WAITING: the
  -- chain's first lane is opened before it and started past its end, so
  -- the queue counter holds it.
  module AtQueue (rx₁ : List Row) (T : Target rx₁) (r₁ : List Row) {d xd} (r₂ : List Row) (sp : rx₁ ≡ r₁ ++ (d , out xd) ∷ r₂)
                 (B₀ : Base (Target.sb T) d xd) where
    open Target T using (xo; l; nq)
    open Base B₀
    open AtBase rx₁ T r₁ r₂ sp B₀ using (mt′; x₀′; beside)
    open CH.Base base using (q₁; a₁; x₁; l₁; sub₁; before₁; l₀; c₀)

    bd : op ≡ mergeᶠ (just (proj₁ (CH.bounded op xo l nq)))
    bd = proj₂ (CH.bounded op xo l nq)

    ro : Σ Pos λ r → Σ _ λ n → σ₁ r (out (instEmit (value a₁) n)) × q₁ ≡ ro-at r
    ro = ro-row x₁

    -- The first lane's value comes before the base's `laneDone`.
    jd : (proj₁ ro ⊕ [ sub OS.J ]) ≺ d
    jd = subst ((proj₁ ro ⊕ [ sub OS.J ]) ≺_) (sym at₀)
           (≺-trans {proj₁ ro ⊕ [ sub OS.J ]} {ro-at (proj₁ ro)} {y₀ ⊕ [ sub LS.J ]} (J≺ro (proj₁ ro))
             (≺-trans {ro-at (proj₁ ro)} {y₀} {y₀ ⊕ [ sub LS.J ]}
               (subst (_≺ y₀) (proj₂ (proj₂ (proj₂ ro))) (done-ahead x₀′ ld₀ l₀ x₁ before₁)) (≺-ext y₀ [])))

    -- The first lane starts past the base's end, so after its `laneDone`.
    late : ∀ {x} → x ∈ r₁ → LaneMark laneStart q₁ x → ⊥
    late i (a′ , ys , n , xo′ , refl , l′) =
      let l″ = subst (λ b → RV.Lane op q₁ b ys (out (instEmit (mark laneStart) n))) (sym (ro-func x₁ xo′)) l′
          rw = CH.sub-row op x₁ l₁ l″
          sy : (c₀ ⊕ [ ix 1 ]) ≺ ys
          sy = subst (_≺ ys) sub₁ (world-after (InvAt.world (CH.sub-inv op x₁ l₁) rw) (InvAt.real (CH.sub-inv op x₁ l₁) rw))
          yd : (ys ⊕ [ sub LS.J ]) ≺ (y₀ ⊕ [ sub LS.J ])
          yd = subst ((ys ⊕ [ sub LS.J ]) ≺_) at₀ (met-before r₁ mt′ i)
          cy : c₀ ≺ (y₀ ⊕ [ sub LS.J ])
          cy = ≺-trans {c₀} {ys} {y₀ ⊕ [ sub LS.J ]} (≺-trans {c₀} {c₀ ⊕ [ ix 1 ]} {ys} (≺-ext c₀ []) sy)
                 (≺-trans {ys} {ys ⊕ [ sub LS.J ]} {y₀ ⊕ [ sub LS.J ]} (≺-ext ys []) yd)
      in beside (conv {y₀} {y₀} {c₀} {y₀ ⊕ [ sub LS.J ]} (⊑-refl y₀) (≺→≼ {y₀} {c₀} done₀) cy (⊑-snoc⁺ y₀))

    unstarted : ¬ Any (LaneMark laneStart q₁) r₁
    unstarted st = let (_ , i , lm) = find st in late i lm

    empty : ∀ {s} (L : List Pos) → L.length L ℕ.≤ 0 → s ∈ L → ⊥
    empty (_ ∷ _) () _

    waiting : ¬ Flat.queue (proj₁ (past op init r₁)) ≡ 0
    waiting q0 = met-open r₁ mt′ (proj₁ (proj₂ (proj₂ ro))) jd λ oi →
      QL.covered r₁ (λ xs y ys eq → past-queue op init xs y (no-end r₁ mt′ xs eq))
        (λ { (_ , _ , _ , _ , _ , refl) → subst (λ o → markQue o outerOpen ≡ kStart) (sym bd) refl })
        (λ { (_ , _ , _ , _ , refl , _) → refl })
        (λ _ _ _ _ _ _ → open-one)
        (λ xs x ys eq kx κ′ → start-live r₁ mt′ xs x ys eq kx λ (q , lm , (a , xo″ , _) , rest) → κ′ (q , lm , (a , xo″) , rest))
        λ (L , le , mem) → empty L (subst (L.length L ℕ.≤_) q0 le)
          (mem ((a₁ , x₁) , subst (λ q → Any (OpenMark q) r₁) (sym (proj₂ (proj₂ (proj₂ ro)))) oi , unstarted
               , λ (_ , _ , _ , _ , cb) → let (xc , _ , kc) = find cb in que-cut op xc kc))

  base-queue : ∀ rx₁ (T : Target rx₁) r₁ {d xd} r₂ → rx₁ ≡ r₁ ++ (d , out xd) ∷ r₂ → (B₀ : Base (Target.sb T) d xd)
             → ¬ Flat.queue (proj₁ (past op init r₁)) ≡ 0
  base-queue rx₁ T r₁ r₂ sp B₀ = AtQueue.waiting rx₁ T r₁ r₂ sp B₀

  -- A cut leaves the instant where it was.
  cut-at : ∀ k n (s : Flat Pos) → Flat.at (proj₁ (cut {B} k n s)) ≡ Flat.at s
  cut-at k n s with Flat.spent s | anyHolds (Flat.at s) (Flat.live s)
  ... | true  | _     = refl
  ... | false | true  = refl
  ... | false | false = refl

  -- So does a lane's end.
  ended-at : ∀ k n (s : Flat Pos) → Flat.at (proj₁ (ended {B} k n s)) ≡ Flat.at s
  ended-at k n s with isZero (Flat.queue s)
  ... | false = refl
  ... | true with Flat.finished s ∧ isZero (Flat.active s)
  ...   | true  = refl
  ...   | false = cut-at (k + Flat.held s) n (record s { held = 0 })

  -- A lane's end with a lane queued holds its routes.
  ended-held : ∀ k n (s : Flat Pos) → ¬ Flat.queue s ≡ 0 → Flat.held (proj₁ (ended {B} k n s)) ≡ Flat.held s + k
  ended-held k n s nq with isZero (Flat.queue s) in e
  ... | false = refl
  ... | true  = ⊥-elim (nq (zero-of (Flat.queue s) e))
    where
      zero-of : ∀ k → isZero k ≡ true → k ≡ 0
      zero-of zero _ = refl

  -- THE BASE'S `laneDone` LEAVES ROUTES HELD OF THE ROW'S INSTANT: with
  -- the queued lane waiting, it holds the routes its lane ends with.
  hand-held : ∀ rx₁ (T : Target rx₁) r₁ {d xd} r₂ → rx₁ ≡ r₁ ++ (d , out xd) ∷ r₂ → Base (Target.sb T) d xd
            → ¬ Flat.held (proj₁ (react op (past op init r₁) xd)) ≡ 0 × Flat.at (proj₁ (react op (past op init r₁) xd)) ≡ nameOf (Target.z T)
  hand-held rx₁ T r₁ {d} {xd} r₂ sp B₀ = go xd (Base.xd₀ B₀)
    where
      S = proj₁ (past op init r₁)

      pos⊓ : ∀ {a b} → 1 ℕ.≤ a → 1 ℕ.≤ b → ¬ a ℕ.⊓ b ≡ 0
      pos⊓ {zero}          ()  _
      pos⊓ {suc _} {zero}  _   ()
      pos⊓ {suc _} {suc _} _   _  ()

      go : ∀ x → x ≡ Ln (instEmit (mark (laneDone (Base.kd B₀))) (Base.n₀ B₀))
         → ¬ Flat.held (proj₁ (react op (past op init r₁) x)) ≡ 0 × Flat.at (proj₁ (react op (past op init r₁) x)) ≡ nameOf (Target.z T)
      go _ refl =
        let S′ = record S { active = Flat.active S ℕ.∸ 1 ; lanes = Flat.lanes S ℕ.∸ Base.kd B₀ ; dead = true }
            k = Base.kd B₀ ℕ.⊓ Flat.lanes S
        in (λ h → pos⊓ (AtBase.kd≥1 rx₁ T r₁ r₂ sp B₀) (base-lanes rx₁ T r₁ r₂ sp B₀)
                    (m+n≡0⇒n≡0 (Flat.held S) (trans (sym (ended-held k (Base.n₀ B₀) S′ (base-queue rx₁ T r₁ r₂ sp B₀))) h)))
         , trans (ended-at k (Base.n₀ B₀) S′) (base-at rx₁ T r₁ r₂ sp B₀)

  -- IN A QUEUED LANE'S SUBSCRIBE BURST, an ended lane's routes are held
  -- to it, from the chain's base.
  queued-hand : ∀ rx₁ {y v rx₂} (Ov : Set) → Met M (rx₁ ++ (y ⊕ [ sub LS.J ] , out (Ln v)) ∷ rx₂)
              → ∀ {Q a} (xo : RO Q (out a)) (l : RV.Lane op Q a y (out v)) → ¬ sub-at xo l ≡ Q ⊕ [ ix 1 ] → Sync (sub-at xo l) y
              → Carried (out v) → OvBefore rx₁ (y ⊕ [ sub LS.J ]) Ov → Live? rx₁ Ov → ¬ Ex cs′ (y ⊕ [ sub LS.J ])
              → Hand rx₁ (y ⊕ [ sub LS.J ])
  queued-hand rx₁ Ov mt xo l nq sy car ovf res nx =
    let (r₁ , d , xd , r₂ , sp , B₀) = hand-base rx₁ T
        (hd , at) = hand-held rx₁ T r₁ r₂ sp B₀
    in record
      { r₁ = r₁ ; r₂ = r₂ ; d = d ; xd = xd ; split = sp
      ; ld = _ , Base.kd B₀ , Base.n₀ B₀ , Base.xd₀ B₀
      ; held = hd ; at = at
      ; inst = hand-inst rx₁ T r₁ r₂ sp B₀
      ; dones = hand-dones rx₁ T r₁ r₂ sp B₀
      ; bursts = hand-bursts rx₁ T r₁ r₂ sp B₀ }
    where
      T : Target rx₁
      T = record { mt = mt ; xo = xo ; l = l ; nq = nq ; sy = sy ; car = car ; nx = nx ; Ov = Ov ; ovf = ovf ; res = res }
