{-# OPTIONS --guardedness #-}

-- A LANE OF THE REAL FLATMAP STARTS ONCE (`start-once`).  Read at an
-- admissible, early subscription, its lane part's share runs the program
-- below at admissible, early subscriptions (`share-quiet`), where it is
-- held, so it shows no `laneStart`; the lane then shows its own only as
-- its frame's first mark (`lane-start-at`).
module simultaneous.LaneOnce where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; [_])
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (_∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Tree using (Obs; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ; empty; of; flatMap; connected)
open import denotation.Position using (Pos; root; _≟ᵖ_; ix; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (EmissionSet; Den; DenEnv; hot; enter; out; Proper; at-out; module Op)
open import denotation.Laws using (good-cons)
open import denotation.Laws.Connect using () renaming (lawful to src-lawful; ok₀ to body-ok)
open import denotation.Laws.Worlds using (Ok; InvD; InvAt; Lawful; Hots; GoodEnv; ok-step; ok-in)
open import denotation.Laws.Worlds.Leaves using (of-reach)
open import denotation.Laws.BoundedInv using (module BoundedI)
open import simultaneous.SObs using (lone; lanePart; burstPart; module Elaborate)
open import simultaneous.InstEmit using (instEmit; value; mark; laneStart; valuesOf)
open import simultaneous.Routed using (Held; Early)
open import simultaneous.HeldComb using (ev)
open import simultaneous.HeldConnect using (early-inst)
open import simultaneous.DenRows using (bounded-out; each-one)
open import simultaneous.LaneLocal using (inv-ev; EndsEarly; held-fit; module FlatFit; module LaneReal; each-vals; of-outer;
  empty-ends; Outer)
open import simultaneous.RealView using (module View)
open import simultaneous.Routed using (HeldD; Routing; Placed; PlacedD; Adm; adm-∪)
open import denotation.Laws.Worlds using (plain-ix)
open import denotation.EmissionSet using (end)
open import Data.Unit using (tt)
import simultaneous.LaneStart as LaneStart
open LaneStart using (laneAt)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; elab; laneˢ; each)

-- An `of`'s first value, at its first child.
of-first : ∀ m {Γ X} (y : X) ys (ρ : DenEnv Γ) p → enter (ev m (of (y ∷ ys)) ρ) p (p ⊕ [ ix 0 ]) (out y)
of-first nothing  y ys ρ p = at-out , of-reach p 0 (y ∷ ys) {p ⊕ [ ix 0 ]} {out y}
of-first (just _) y ys ρ p = at-out , of-reach p 0 (y ∷ ys) {p ⊕ [ ix 0 ]} {out y}

-- A bounded flatMap, read through its parts.
flat-at : ∀ m {Γ X Y} op (g : X → Obs Timeline Γ Y) (o : Obs Timeline Γ X) (ρ : DenEnv Γ) p {y e}
        → enter (ev m (flatMap op g o) ρ) p y e → enter (Op.flatMap op (λ c → ev m (g c) ρ) (ev m o ρ)) p y e
flat-at nothing  op g o ρ p r = r
flat-at (just _) op g o ρ p r = r

module LaneOnce (m : Maybe ℕ) {Γ Θ A B} {Fr : Pos → Set} (op : FlatOp) (f : A → Obs Timeline Γ B)
                (ρ₄ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ ⊤ ∷ IE B ∷ IE A ∷ Θ)
                (t₂ : EmissionSet (IE B)) (t₁ : EmissionSet (IE A)) (env₀ : DenEnv Θ)
                (g₂ : GoodEnv (hot t₂ ∷ hot t₁ ∷ env₀)) (L₁ : Lawful t₁)
                (tv : ∀ {r b n} → t₁ r (out (instEmit (value b) n)) → Early r) (te : EndsEarly t₁) (tp : Placed Fr t₁)
                (ad : Adm (Hots (hot t₂ ∷ hot t₁ ∷ env₀)) Fr) (cs : List Pos)
                (held : ∀ a {t} → Lawful t → HeldD (Hots (hot t ∷ hot t₂ ∷ hot t₁ ∷ env₀)) Fr (ev m (elab ρ₄ (f a)) (hot t ∷ hot t₂ ∷ hot t₁ ∷ env₀)) cs)
                (placed : ∀ a {t} → Lawful t → PlacedD (Hots (hot t ∷ hot t₂ ∷ hot t₁ ∷ env₀)) Fr (ev m (elab ρ₄ (f a)) (hot t ∷ hot t₂ ∷ hot t₁ ∷ env₀))) where

  open LaneReal m op f ρ₄ t₂ t₁ env₀ g₂ L₁ tv te tp ad (λ a L p ok fp ep → held-fit (held a L p ok fp ep) (placed a L p ok fp ep)) using (env₂; x; srcE; laneE)

  dR : Den A
  dR = ev m (each valuesOf (connected (there (here refl)))) env₂

  fL : A → Den (IE B)
  fL a = ev m (laneˢ (x a)) env₂

  Id : InvD (Hots env₂) dR
  Id = inv-ev m (each valuesOf (connected (there (here refl)))) env₂ g₂

  Il : ∀ a → InvD (Hots env₂) (fL a)
  Il a = inv-ev m (laneˢ (x a)) env₂ g₂

  -- An outer row is reachable and clear.
  ok-o : ∀ p → Ok (Hots env₂) p → ∀ {q e} → enter dR p q e → Ok (Hots env₂) q
  ok-o p ok xo = ok-in ok (InvAt.world (Id p ok) xo) (InvAt.real (Id p ok) xo)

  vals : ∀ p → Ok (Hots env₂) p → Fr p → Early p → Outer Fr (enter dR p)
  vals p ok fp ep = each-vals m t₂ t₁ env₀ g₂ L₁ ad tv te tp p ok fp ep

  -- TWO ROWS OF ONE LANE ARE ITS VALUE'S OWN, at one admissible, early
  -- subscription.
  lane-sub₂ : ∀ op′ p → Ok (Hots env₂) p → Fr p → Early p → ∀ {q a k e k′ e′} → enter dR p q (out a)
            → View.Lane fL (enter dR p) op′ q a k e → View.Lane fL (enter dR p) op′ q a k′ e′
            → Σ Pos λ s → Ok (Hots env₂) s × Fr s × Early s × enter (fL a) s k e × enter (fL a) s k′ e′
  lane-sub₂ (mergeᶠ nothing) p ok fp ep {q} xo (r , _) (r′ , _) =
    _ , ok-step q (ok-o p ok xo) , Adm.step ad (ok-o p ok xo) (proj₂ (proj₂ (vals p ok fp ep)) xo tt) plain-ix
      , early-inst [ ix 1 ] (proj₁ (vals p ok fp ep) xo) , r , r′
  lane-sub₂ switchᶠ p ok fp ep {q} xo (r , _) (r′ , _) =
    _ , ok-step q (ok-o p ok xo) , Adm.step ad (ok-o p ok xo) (proj₂ (proj₂ (vals p ok fp ep)) xo tt) plain-ix
      , early-inst [ ix 1 ] (proj₁ (vals p ok fp ep) xo) , r , r′
  lane-sub₂ exhaustᶠ p ok fp ep {q} xo (r , _) (r′ , _) =
    _ , ok-step q (ok-o p ok xo) , Adm.step ad (ok-o p ok xo) (proj₂ (proj₂ (vals p ok fp ep)) xo tt) plain-ix
      , early-inst [ ix 1 ] (proj₁ (vals p ok fp ep) xo) , r , r′
  lane-sub₂ (mergeᶠ (just n)) p ok fp ep xo (i , s , sb , r , _) (i′ , s′ , sb′ , r′ , _) with BoundedI.sub-same ok n fL Il (Id p ok) sb sb′
  ... | refl = let (es , oks , fs) = FlatFit.Bd.start-at fL dR ad Id Il laneE p ok (proj₁ V) (proj₁ (proj₂ V)) (proj₂ (proj₂ V)) n i (proj₁ sb) (proj₂ sb)
               in s , oks , fs , es , r , r′
    where V = vals p ok fp ep

  -- THE LANE PART'S SHARE SHOWS NO MARK BUT A ROUTE'S: its blocker shows
  -- nothing, and the program below is held where the bounded merge
  -- subscribes it.
  module Share (a : A) (s : Pos) (ok : Ok (Hots env₂) s) (fs : Fr s) (es : Early s) where
    P : Pos
    P = laneAt s

    tS : EmissionSet ⊤
    tS = Proper (enter (ev m (empty {A = ⊤}) env₂) (P ⊕ [ ix 1 ]))

    F : Den ⊤ → Den (IE B)
    F h = ev m (flatMap (mergeᶠ (just 1)) (x a lanePart) (of (true ∷ false ∷ []))) (h ∷ env₂)

    Is : InvD (Hots env₂) (ev m (empty {A = ⊤}) env₂)
    Is = inv-ev m (empty {A = ⊤}) env₂ g₂

    IF : ∀ {t} → Lawful t → InvD (Hots (hot t ∷ env₂)) (F (hot t))
    IF L = inv-ev m _ (hot _ ∷ env₂) (good-cons L g₂)

    ok₀ : Ok (Hots env₂) (s ⊕ [ ix 0 ])
    ok₀ = ok-in ok (InvAt.world Io xo) (InvAt.real Io xo)
      where
        Io = inv-ev m (of (lanePart ∷ burstPart ∷ [])) env₂ g₂ s ok
        xo = of-first m lanePart (burstPart ∷ []) env₂ s

    okP : Ok (Hots env₂) P
    okP = ok-step (s ⊕ [ ix 0 ]) ok₀

    fP : Fr P
    fP = Adm.step ad ok₀ (Adm.bare ad fs λ ()) plain-ix

    eP : Early P
    eP = early-inst [ ix 1 ] (early-inst [ ix 0 ] es)

    Lt : Lawful tS
    Lt = src-lawful {s = ev m (empty {A = ⊤}) env₂} {F = F} Is IF P okP

    tee : EndsEarly tS × (∀ {c} → tS c end → Fr c)
    tee = empty-ends m env₂ ad (P ⊕ [ ix 1 ]) (early-inst [ ix 1 ] eP) (Adm.step ad okP fP plain-ix)

    env′ : DenEnv (⊤ ∷ IE B ∷ IE A ∷ Θ)
    env′ = hot tS ∷ env₂

    g′ : GoodEnv env′
    g′ = good-cons Lt g₂

    Q : Pos
    Q = (P ⊕ [ ix 0 ]) ⊕ [ ix 1 ]

    ad′ : Adm (Hots env′) Fr
    ad′ = adm-∪ {t = tS} ad

    okP₀ : Ok (Hots env′) (P ⊕ [ ix 0 ])
    okP₀ = body-ok {s = ev m (empty {A = ⊤}) env₂} {F = F} Is IF P okP

    okQ : Ok (Hots env′) Q
    okQ = ok-step (P ⊕ [ ix 0 ]) okP₀

    fQ : Fr Q
    fQ = Adm.step ad′ okP₀ (Adm.bare ad′ fP λ ()) plain-ix

    eQ : Early Q
    eQ = early-inst [ ix 1 ] (early-inst [ ix 0 ] eP)

    fc : Bool → Den (IE B)
    fc c = ev m (x a lanePart c) env′

    dQ : Den Bool
    dQ = ev m (of (true ∷ false ∷ [])) env′

    blk : ∀ m′ {s′ y b} → enter (ev m′ (x a lanePart true) env′) s′ y (out b) → ⊥
    blk nothing  {s′} l with each-one (λ _ → []) (hot tS) s′ l
    ... | _ , _ , _ , ()
    blk (just _) {s′} l with each-one (λ _ → []) (hot tS) s′ l
    ... | _ , _ , _ , ()

    share-mark : ∀ {mk} → (Routing mk → ⊥) → ∀ {y n} → enter (ev m (flatMap (mergeᶠ (just 1)) (x a lanePart) (of (true ∷ false ∷ []))) env′) Q y (out (instEmit (mark mk) n)) → ⊥
    share-mark nr r with bounded-out 1 fc dQ Q (flat-at m (mergeᶠ (just 1)) (x a lanePart) (of (true ∷ false ∷ [])) env′ Q r)
    ... | _ , true  , _ , _ , _ , _ , (l , _) = blk m l
    ... | _ , false , i , s′ , _ , (N , St) , (l , _) =
      let (es′ , oks′ , fs′) = FlatFit.Bd.start-at fc dQ ad′ (inv-ev m (of (true ∷ false ∷ [])) env′ g′) (λ c → inv-ev m (x a lanePart c) env′ g′)
                           (srcE a lanePart tS Lt tee) Q okQ (proj₁ O) (proj₁ (proj₂ O)) (proj₂ (proj₂ O)) 1 i N St
      in nr (Held.routing (held a Lt s′ oks′ fs′ es′) l)
      where
        O = of-outer m _ env′ ad′ Q okQ fQ eQ

    share-quiet : ∀ {y n} → enter (ev m (flatMap (mergeᶠ (just 1)) (x a lanePart) (of (true ∷ false ∷ []))) env′) Q y (out (instEmit (mark laneStart) n)) → ⊥
    share-quiet = share-mark (λ ())

  -- A LANE STARTS ONCE: its two `laneStart`s, read at one admissible, early
  -- subscription, are where its frame shows its first mark.
  start-once : ∀ p → Ok (Hots env₂) p → Fr p → Early p → ∀ {q a y y′ n n′} → enter dR p q (out a)
             → View.Lane fL (enter dR p) op q a y (out (instEmit (mark laneStart) n)) → View.Lane fL (enter dR p) op q a y′ (out (instEmit (mark laneStart) n′))
             → y ≡ y′
  start-once p ok fp ep {a = a} xo l l′ with lane-sub₂ op p ok fp ep xo l l′
  ... | s , oks , fs , es , r , r′ = trans (at r) (sym (at r′))
    where
      open Share a s oks fs es using (share-quiet)
      at : ∀ {y n} → enter (fL a) s y (out (instEmit (mark laneStart) n)) → y ≡ LaneStart.C.startAt (λ i → ρ₄ i) (f a) env₂ m s
      at = LaneStart.lane-start-at (λ i → ρ₄ i) (f a) env₂ m s share-quiet
