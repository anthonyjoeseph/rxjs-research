{-# OPTIONS --guardedness #-}

-- WHAT THE LANES COUNTER HOLDS AT A ROW MET: a lane's stop ends a route
-- it counts, past its burst it counts a route of its row's instant, and
-- the counter keeps what each live lane holds of the instant of the row
-- met next, the scan at that instant (`simultaneous.LaneFloor`).
module simultaneous.LaneHold where

import Data.List as L
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Relation.Unary.All using (_∷_)
open import Data.List.Membership.Propositional using (_∈_; find)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ʳ; ∈-++⁺ˡ; ∈-∃++)
open import Data.List.Properties using (++-assoc)
open import Data.List.Relation.Unary.Any using (Any; here; there; any?)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_)
import Data.Nat as ℕ
import Data.Nat.Properties as ℕP
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
import Data.Sum as Sum
open import Data.Bool using (Bool; T; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Tree using (Obs; FlatOp; connected)
open import denotation.Position using (Pos; Path; root; _≟ᵖ_; ix; sub; _⊕_; inside; _∙_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (DenEnv; out; enter; hot; _≼_; _≺_)
open import denotation.Read using (Run) renaming (_∷_ to _∷ᴿ_)
open import denotation.Laws.Worlds using (Hots; GoodEnv; Ok; Lawful; ok-step; ⊑-≼; InvAt; _⊑_; inside-⊑; ⊑-snoc; ⊕-assoc; ⊕-injˡ)
open import denotation.Laws.Modulus using (≺-absurd; ≺-≼-≺; ≺-irrefl; ≺-trans; ≺-ext; ≺→≼)
open import simultaneous.Horizon using (past-sub)
open import simultaneous.Shut using (r₀)
open import simultaneous.SObs using (lone; module Elaborate; Flat; laneB; outerB; closeB)
open import simultaneous.InstEmit using (instEmit; mark; value; begin; over; stop; outerOpen; outerClose; laneStart; laneDone; burstEnd;
  outerDone; subscribed; completed; valuesOf)
open import simultaneous.Relations using (Met)
open import simultaneous.Readings using (rootOf; instantOf)
open import simultaneous.Routed using (Held; Early; Placed; Ex; Sync; Carried; cnt; c-value; c-stop; c-done; c-over; nameOf; nm; Valued; opos)
open import simultaneous.HeldConnect using (early-inst; rootOf-ext)
open import simultaneous.HeldTake using (ex-ext)
open import simultaneous.Layers using (run-tail; run-after) renaming (run-row to run-row∈)
open import simultaneous.Counts using (Counts; pre; idle-row)
open import simultaneous.Project using (run-prefix)
open import simultaneous.RealView using (lane-at)
open import simultaneous.LaneLocal using (Fit; Fine; inv-ev)
open import simultaneous.LaneEpoch using (module Lanes)
open import simultaneous.LaneFloor using (module Floor)
open import simultaneous.FlatLanes using (Tg; BProj; module BProj; keep; drop; tagged; brTag)
open import simultaneous.LaneSplit using (Ln)
open import simultaneous.HeldBase using (EnvHeld; module FlatHots; IH; Fresh)
open import simultaneous.HeldComb using (ev; init; past; from-++)
open import simultaneous.FlatSim using (tot)
open import simultaneous.HeldSrc using (module CombSrc; Opens; o-value; o-done)
open import simultaneous.HeldLanes using (module CombLanes; bproj-mem)
open import simultaneous.HeldLaneRoutes using (module LaneRoutes)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (AIE; IE; each; laneˢ; count; opening; Input; Out; react)

module LaneHold (m : Maybe ℕ) {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (op : FlatOp) (f : A → Obs Timeline Γ B)
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
  open CombLanes m ρ op f s env cs gd eh hf p ok fr ep H₁ tp L₁ L₂ L₃ ok₁ ok₂ ok₃ ep₃
  open LaneRoutes m ρ op f s env cs gd eh hf p ok fr ep H₁ tp L₁ L₂ L₃ ok₁ ok₂ ok₃ ep₃
  open Lanes {B} op Own (LaneMark laneStart) DoneMark act LaneEmit using (OC; oc-total; oc[]; oc-in; oc-out)

  -- The overs met before a row, of its instant, leave `Ov`.
  OvBefore : List Row → Pos → Set → Set
  OvBefore rx₁ q Ov = ∀ {k b n} → (k , out (Tg b (instEmit (mark over) n))) ∈ rx₁ → instantOf k ≡ instantOf q → Ov

  -- And the scan is live past them.
  Live? : List Row → Set → Set
  Live? rx₁ Ov = Flat.spent (St rx₁) ≡ false ⊎ Ov → Flat.spent (St rx₁) ≡ false

  -- A LANE'S STOP ENDS A ROUTE IT COUNTS: the lane's count is its
  -- program's, whose stops end a route it holds.
  lane-exact : ∀ {q a} → RO q (out a) → ∀ {rs} → Met (RV.Lane op q a) rs → ∀ r₁ {y n} r₂ → rs ≡ r₁ ++ (y , out (instEmit (mark stop) n)) ∷ r₂
             → Σ ℕ λ k → proj₂ (cnt r₁) ≡ suc k
  lane-exact xo mt r₁ r₂ refl = Counts.stp (lane-counts-own xo (proj₁ (run-row∈ mt (∈-++⁺ʳ r₁ (here refl))))) r₁ (pre r₁ r₂ mt)

  -- PAST ITS BURST, A VALUE A LANE CARRIES FINDS A ROUTE OF ITS INSTANT
  -- the lane counts, unless exempt: its program's rows do.
  lane-covered : ∀ {q a} (xo : RO q (out a)) → ∀ {rs} → Met (RV.Lane op q a) rs → ∀ r₁ {y v} r₂ → rs ≡ r₁ ++ (y , out v) ∷ r₂
               → (l : RV.Lane op q a y (out v)) → Carried (out v) → ¬ Sync (sub-at xo l) y → ¬ Ex cs y → Σ ℕ λ k → cnt r₁ ≡ (nameOf y , suc k)
  lane-covered xo mt r₁ r₂ refl l c ns nx = Counts.cov (lane-counts-own xo l) r₁ (pre r₁ r₂ mt) c [ ns , nx ]′

  -- A LANE COUNTS NOTHING BEFORE ITS `laneStart`: a begin of it would
  -- follow a `laneStart` of it, and it starts once.
  start-own : ∀ xs {x rest} → Met M (xs ++ x ∷ rest) → ∀ {q n c} → LaneEmit q x (instEmit (mark laneStart) n) → OC q xs c
            → proj₂ c ≡ 0
  start-own xs {rest = rest} mt {q} (a , y , xo , refl , l) oc = aux oc (λ i lu → no-begin i lu)
    where
      no-begin : ∀ {u n′} → u ∈ xs → LaneEmit q u (instEmit (mark begin) n′) → ⊥
      no-begin {u} i lu with ∈-∃++ i
      ... | a₁ , b₁ , refl with find (started a₁ (subst (Met M) (++-assoc a₁ (u ∷ b₁) _) mt) lu tt (λ ()) (λ ()))
      ...   | _ , i₀ , (a′ , y₀ , n₀ , xo₀ , refl , l₀) with ro-func xo xo₀
      ...     | refl = ≺-irrefl {y ⊕ [ sub LS.J ]}
                  (subst (_≺ (y ⊕ [ sub LS.J ])) (cong (_⊕ [ sub LS.J ]) (start-once xo l₀ l)) (met-before (a₁ ++ u ∷ b₁) mt (∈-++⁺ˡ i₀)))

      step : ∀ {c} v → proj₂ c ≡ 0 → (∀ {n′} → v ≡ instEmit (mark begin) n′ → ⊥) → proj₂ (count {B} c v) ≡ 0
      step (instEmit (mark begin) _) _ nb = ⊥-elim (nb refl)
      step (instEmit (mark stop) _)  z _  = cong (ℕ._∸ 1) z
      step (instEmit (mark over) _)  _ _  = refl
      step (instEmit (value _) _)    z _  = z
      step (instEmit (mark outerOpen) _)    z _ = z
      step (instEmit (mark outerClose) _)   z _ = z
      step (instEmit (mark laneStart) _)    z _ = z
      step (instEmit (mark (laneDone _)) _) z _ = z
      step (instEmit (mark burstEnd) _)     z _ = z
      step (instEmit (mark outerDone) _)    z _ = z
      step (instEmit (mark subscribed) _)   z _ = z
      step (instEmit (mark completed) _)    z _ = z

      aux : ∀ {pre c} → OC q pre c → (∀ {u n′} → u ∈ pre → LaneEmit q u (instEmit (mark begin) n′) → ⊥) → proj₂ c ≡ 0
      aux oc[] _ = refl
      aux (oc-out oc _) nb = aux oc (λ i → nb (∈-++⁺ˡ i))
      aux (oc-in {p₀} {_} {x₀} {v} oc l′) nb =
        step v (aux oc (λ i → nb (∈-++⁺ˡ i))) (λ e → nb (∈-++⁺ʳ p₀ (here refl)) (subst (LaneEmit q x₀) e l′))

  -- PAST ITS BURST A LANE COUNTS A ROUTE OF ITS ROW'S INSTANT.
  lane-own : ∀ rx₁ {y v rx₂} → Met M (rx₁ ++ (y ⊕ [ sub LS.J ] , out (Ln v)) ∷ rx₂)
           → ∀ {Q a} (xo : RO Q (out a)) (l : RV.Lane op Q a y (out v)) → ¬ Sync (sub-at xo l) y → Carried (out v)
           → ¬ Ex cs′ (y ⊕ [ sub LS.J ]) → ∀ {c} → OC Q rx₁ c → Σ ℕ λ k → c ≡ (nameOf y , suc k)
  lane-own rx₁ {y} {v} mt {Q} {a} xo l ns car nx oc =
    let (k , e) = lane-covered xo (own-snoc rx₁ mt xo oc (a , y , xo , refl , l)) (lane-rows oc) [] refl l car ns
                    (λ ex → nx (there (there (there (there (there (ex-ext [ sub LS.J ] ex)))))))
    in k , trans (sym (cnt-lane oc)) e

  -- A LANE'S STOP ENDS A ROUTE OF ITS OWN INSTANT THE LANE COUNTS.
  stop-own : ∀ xs {x rest} → Met M (xs ++ x ∷ rest) → ∀ {q n c} → LaneEmit q x (instEmit (mark stop) n) → OC q xs c
           → proj₁ c ≡ nameOf (proj₁ x) × ¬ proj₂ c ≡ 0
  stop-own xs mt {q} {n} le@(a , y , xo , refl , l) oc =
    trans (sym (cong proj₁ c≡)) (trans name (cong nm (sym (rootOf-ext y [ sub LS.J ])))) ,
    λ z → 0≢suc (trans (sym z) (trans (sym (cong proj₂ c≡)) (proj₂ (lane-exact xo rn (lane-rows oc) [] refl))))
    where
      rn : Met (RV.Lane op q a) (lane-rows oc ++ [ (y , out (instEmit (mark stop) n)) ])
      rn = own-snoc xs mt xo oc le

      c≡ = cnt-lane oc

      0≢suc : ∀ {k} → 0 ≡ suc k → ⊥
      0≢suc ()

      name : proj₁ (cnt (lane-rows oc)) ≡ nameOf y
      name with idle-row (lane-idle-own xo) (lane-rows oc) rn
      ... | inj₂ e = e
      ... | inj₁ z = ⊥-elim (0≢suc (trans (sym z) (proj₂ (lane-exact xo rn (lane-rows oc) [] refl))))

  done-live : ∀ xs {x rest} → Met M (xs ++ x ∷ rest) → ∀ {q kd n} → LaneEmit q x (instEmit (mark (laneDone kd)) n) → AC.Live [] xs q
  done-live xs mt le = live-of xs mt le (done-started xs mt le)

  -- THE FLOOR, read at the instant of the row met next.
  module LF (rx₁ : List Row) {z e rx₂} (mt : Met M (rx₁ ++ (z , e) ∷ rx₂)) where
    open Inst rx₁ mt using (In; row∈; begin-name; name-begin; in-after; in-root; in-name)

    private
      sm = split-met rx₁ mt

      fwd : ∀ xs x ys → rx₁ ≡ xs ++ x ∷ ys → (Σ Row λ u → u ∈ xs × In (proj₁ u)) → In (proj₁ x)
      fwd xs x ys eq (u , ua , iu) = in-after xs ys eq ua iu

    module F = Floor.Run′ {B} op Own (LaneMark laneStart) DoneMark act LaneEmit rx₁ (nameOf z) (λ x → In (proj₁ x))
      (λ {c} → end-free rx₁ mt {c})
      (λ xs k v ys eq κ → κ (lane-emit rx₁ mt (in-r₁ rx₁ xs _ ys eq)))
      (λ { (_ , y , _ , eq , _) → y ⊕ [ sub LS.J ] , eq })
      (λ {q} {q′} {x} {v} {v′} → emit-one {q} {q′} {x} {v} {v′})
      (λ { (a , y , n , xo , eq , l) → n , a , y , xo , eq , l })
      (λ { {kd = kd} {n = n} (a , y , xo , eq , l) → kd , a , y , n , xo , eq , l })
      (λ xs k b kd n ys eq → done-laneB (row∈ (in-r₁ rx₁ xs _ ys eq)))
      (λ xs x ys eq le → lane-live xs (sm xs x ys eq) le tt (λ ()) (λ ()))
      (λ xs x ys eq le → done-live xs (sm xs x ys eq) le)
      (λ xs x ys eq → done-told rx₁ mt xs x ys eq)
      (λ xs x ys eq → start-own xs (sm xs x ys eq))
      (λ xs x ys eq ik le o → let (cn , nz′) = stop-own xs (sm xs x ys eq) le o in trans cn (in-name {proj₁ x} ik) , nz′)
      (λ xs x ys eq ik le o → Sum.map₂ (λ cn → trans cn (in-name {proj₁ x} ik)) (next-idle xs (sm xs x ys eq) le o))
      (λ xs k b n ys eq → begin-name (in-r₁ rx₁ xs _ ys eq))
      (λ xs k b ys eq → name-begin (in-r₁ rx₁ xs _ ys eq))
      (λ xs x ys eq a → fwd xs x ys eq (find a))
      (λ r i → in-root r i)

  -- THE LANES COUNTER KEEPS WHAT EACH LIVE LANE HOLDS OF ITS INSTANT
  -- (`simultaneous.LaneFloor`), read at the instant of the row met next.
  lanes-floor : ∀ rx₁ {z e rx₂} (Ov : Set) → Met M (rx₁ ++ (z , e) ∷ rx₂) → ∀ {Q c} → AC.Live [] rx₁ Q → OC Q rx₁ c
              → proj₁ c ≡ nameOf z → ¬ proj₂ c ≡ 0 → OvBefore rx₁ z Ov → Live? rx₁ Ov → ¬ Flat.lanes (St rx₁) ≡ 0
  lanes-floor rx₁ {z} Ov mt lv oc nm′ nz ovf res = LF.F.floor rx₁ mt lv oc nm′ nz hov
    where
      hov : Any (LF.F.OverIn rx₁ mt) rx₁ → Flat.spent (St rx₁) ≡ false
      hov a with find a
      ... | _ , ua , iu , k , b , n , refl = res (inj₂ (ovf ua iu))

  -- AND THE SCAN IS AT THAT INSTANT.
  lanes-at : ∀ rx₁ {z e rx₂} → Met M (rx₁ ++ (z , e) ∷ rx₂) → ∀ {Q c} → AC.Live [] rx₁ Q → OC Q rx₁ c
           → proj₁ c ≡ nameOf z → ¬ proj₂ c ≡ 0 → Flat.at (St rx₁) ≡ nameOf z
  lanes-at rx₁ {z} mt lv oc nm′ nz with Flat.at (St rx₁) ≟ᵖ nameOf z
  ... | yes a = a
  ... | no na = ⊥-elim (LF.F.floor-at rx₁ mt lv oc nm′ nz na)

