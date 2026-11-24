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
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
import Data.Nat as ℕ
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; FlatOp)
open import denotation.Position using (Pos; root; _≟ᵖ_; ix; sub; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (DenEnv; out; enter; hot; _≺_)
open import denotation.Laws.Worlds using (Hots; GoodEnv; Ok; Lawful)
open import simultaneous.SObs using (lone; module Elaborate; Flat; isZero)
open import Data.Nat.Properties using (m+n≡0⇒n≡0)
open import Data.Empty using (⊥-elim)
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
open import denotation.Read using (Run)
open import denotation.EmissionSet using (EmissionSet)
open import simultaneous.Layers using (run-after)
open import simultaneous.Instants using (btw)
open import simultaneous.TakeCut using (inst-⊕)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (AIE; IE; Input; react; each; connected; laneˢ; cut; ended; anyHolds)

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
  open CombSrc m ρ op f s env cs gd eh hf p ok fr ep H₁ tp L₁ L₂ L₃ ok₁ ok₂ ok₃ ep₃ using (cs′; module LS; g₂)
  open CombLanes m ρ op f s env cs gd eh hf p ok fr ep H₁ tp L₁ L₂ L₃ ok₁ ok₂ ok₃ ep₃ using (Row; RO; module RV; sub-at; fL; done-ends)
  open LaneRoutes m ρ op f s env cs gd eh hf p ok fr ep H₁ tp L₁ L₂ L₃ ok₁ ok₂ ok₃ ep₃ using (lane-end-done)

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
  record Target (rx₁ : List Row) : Set where
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

  postulate
    -- THE BASE'S `laneDone` IS MET BEFORE THE QUEUED LANE'S ROW: it lies
    -- before the base's end, below the chain's subscriptions, so before
    -- the row.
    base-read : ∀ rx₁ (T : Target rx₁) (B₀ : CH.Base op (Target.sb T)) {y₀ kd n₀}
              → RV.Lane op (CH.Base.q₀ B₀) (CH.Base.a₀ B₀) y₀ (out (instEmit (mark (laneDone kd)) n₀)) → y₀ ≺ CH.Base.c₀ B₀
              → (y₀ ⊕ [ sub LS.J ] , out (Ln (instEmit (mark (laneDone kd)) n₀))) ∈ rx₁

    -- AT THE BASE'S `laneDone` THE QUEUED LANE IS STILL WAITING: the
    -- chain's first lane is opened before it and started past its end.
    base-queue : ∀ rx₁ (T : Target rx₁) r₁ {d xd} r₂ → rx₁ ≡ r₁ ++ (d , out xd) ∷ r₂ → (B₀ : Base (Target.sb T) d xd)
               → ¬ Flat.queue (proj₁ (past op init r₁)) ≡ 0

    -- THE BASE LANE ENDS HOLDING A ROUTE: its end lies outside its
    -- subscription's burst, so its count there is covered, and its
    -- `laneDone` carries that count.
    base-kd : ∀ rx₁ (T : Target rx₁) {d xd} (B₀ : Base (Target.sb T) d xd) → 1 ℕ.≤ Base.kd B₀

    -- THE SCAN HOLDS THE BASE LANE'S ROUTES: the lanes counter counts
    -- every lane route of the instant met (`floor`).
    base-lanes : ∀ rx₁ (T : Target rx₁) r₁ {d xd} r₂ → rx₁ ≡ r₁ ++ (d , out xd) ∷ r₂ → (B₀ : Base (Target.sb T) d xd)
               → 1 ℕ.≤ Flat.lanes (proj₁ (past op init r₁))

    -- THE SCAN IS AT THE ROW'S INSTANT BY THE BASE'S `laneDone`: the base
    -- lane's route of that instant was begun before it, and every row
    -- since lies in it.
    base-at : ∀ rx₁ (T : Target rx₁) r₁ {d xd} r₂ → rx₁ ≡ r₁ ++ (d , out xd) ∷ r₂ → (B₀ : Base (Target.sb T) d xd)
            → Flat.at (proj₁ (past op init r₁)) ≡ nameOf (Target.z T)

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
  run-btw []       r₂ (_ ∷ run) i = run-after run (∈-++⁺ˡ i) , below r₂ run i
    where
      below : ∀ {c′} r {z e₂ r₃ k e} → Run _ c′ (r ++ (z , e₂) ∷ r₃) → (k , e) ∈ r → k ≺ z
      below (_ ∷ r) (_ ∷ run′) (here refl) = run-after run′ (∈-++⁺ʳ r (here refl))
      below (_ ∷ r) (_ ∷ run′) (there j)   = below r run′ j

  -- EVERY ROW READ PAST THE BASE LIES IN THE ROW'S INSTANT: the base's
  -- end is in it, and the chain stays there.
  hand-inst : ∀ rx₁ (T : Target rx₁) r₁ {d xd} r₂ → rx₁ ≡ r₁ ++ (d , out xd) ∷ r₂ → Base (Target.sb T) d xd
            → ∀ {k e} → (k , e) ∈ r₂ → instantOf k ≡ instantOf (Target.z T)
  hand-inst rx₁ T r₁ {d} {xd} r₂ refl B₀ {k} i =
    let open Target T
        (dk , kz) = run-btw r₁ r₂ (subst (Met M) (++-assoc r₁ ((d , out xd) ∷ r₂) ((z , out (Ln v)) ∷ rx₂)) mt) i
        dz : instantOf d ≡ instantOf z
        dz = trans (cong instantOf (Base.at₀ B₀)) (trans (inst-⊕ (Base.y₀ B₀) [ sub LS.J ]) (trans (Base.inst₀ B₀)
               (trans (sym (CH.chain-inst (CH.Base.chain (Base.base B₀)))) (trans (sym (cong instantOf (proj₂ sy))) (sym (inst-⊕ y [ sub LS.J ]))))))
    in trans (btw d k z dk kz dz) dz

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

      pos : ∀ {a b} → 1 ℕ.≤ a → 1 ℕ.≤ b → ¬ a ℕ.⊓ b ≡ 0
      pos {zero}          ()  _
      pos {suc _} {zero}  _   ()
      pos {suc _} {suc _} _   _  ()

      go : ∀ x → x ≡ Ln (instEmit (mark (laneDone (Base.kd B₀))) (Base.n₀ B₀))
         → ¬ Flat.held (proj₁ (react op (past op init r₁) x)) ≡ 0 × Flat.at (proj₁ (react op (past op init r₁) x)) ≡ nameOf (Target.z T)
      go _ refl =
        let S′ = record S { active = Flat.active S ℕ.∸ 1 ; lanes = Flat.lanes S ℕ.∸ Base.kd B₀ ; dead = true }
            k = Base.kd B₀ ℕ.⊓ Flat.lanes S
        in (λ h → pos (base-kd rx₁ T B₀) (base-lanes rx₁ T r₁ r₂ sp B₀)
                    (m+n≡0⇒n≡0 (Flat.held S) (trans (sym (ended-held k (Base.n₀ B₀) S′ (base-queue rx₁ T r₁ r₂ sp B₀))) h)))
         , trans (ended-at k (Base.n₀ B₀) S′) (base-at rx₁ T r₁ r₂ sp B₀)

  -- IN A QUEUED LANE'S SUBSCRIBE BURST, an ended lane's routes are held
  -- to it, from the chain's base.
  queued-hand : ∀ rx₁ {y v rx₂} → Met M (rx₁ ++ (y ⊕ [ sub LS.J ] , out (Ln v)) ∷ rx₂)
              → ∀ {Q a} (xo : RO Q (out a)) (l : RV.Lane op Q a y (out v)) → ¬ sub-at xo l ≡ Q ⊕ [ ix 1 ] → Sync (sub-at xo l) y
              → Carried (out v) → ¬ Ex cs′ (y ⊕ [ sub LS.J ]) → Hand rx₁ (y ⊕ [ sub LS.J ])
  queued-hand rx₁ mt xo l nq sy car nx =
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
      T = record { mt = mt ; xo = xo ; l = l ; nq = nq ; sy = sy ; car = car ; nx = nx }
