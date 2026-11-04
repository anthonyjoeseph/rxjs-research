{-# OPTIONS --guardedness #-}

-- AN OUTER'S VALUE ADMITTED: a joiner's outer rises at `p`, and the
-- joiner subscribes the value's lane at `p ⊕ [ ix 1 ]`.  The frames above
-- the joiner show nothing at `p` (its row there is its outer's, in what
-- no lane's region holds), so they move past `p`; the lane, owed where
-- the cursor has not passed, is pending within its own region.
module adequacy.Admit where

open import Data.Bool using (T; true; false; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Data.Nat using (suc)
open import Data.Nat.Properties using (+-comm)
open import Data.List using ([]; _∷_; [_]; _++_; reverse)
open import Data.List.Properties using (reverse-involutive)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (tabulate) renaming (_∷_ to _∷ᴬ_; [] to []ᴬ)
open import Data.List.Relation.Unary.AllPairs using () renaming (_∷_ to _∷ᴾ_; [] to []ᴾ)
open import Data.List.Relation.Unary.AllPairs.Properties using () renaming (++⁺ to pairs-++⁺)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary using (¬_; yes; no)

open import Tree using (Obs; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Events using (ix; Timeline; _≟ᵖ_)
open import denotation.EmissionSet using (EmissionSet; _≺_; out; end; ⟦_⟧; enter; LaneOf)
open import denotation.Laws.Modulus using (≺-ext; ≺-irrefl; ≼-or-≻)
open import denotation.Laws.Worlds using (InvAt; ok-step; ok-in; world-after; ⊑-inside)
  renaming (⊑-refl to ⊑ʷ-refl)
open import operation.PureObservable using (module Machine)
open Machine using (Ctx; ⟨_,_,_,_⟩; scopeOf; closed; rise; moved; start; subscribing; rising; nx; attAt; pend;
                    inOuter; inLanes; inLn; inCut)
open import adequacy.Rows using (full; pendRows; Moves; _⇄_)
open import adequacy.Cursor using (Cur; Pol; Kill; kill-out; bef; aft; Owes; _≈_; ≈-refl; Sound; JInv; Joined; joined; Begun; none; more; JoinE; JRl; JRo; Behind; Sync; polF; JoinF; Lane; Start; Runs; Whole; OuterDone; Ahead; Asc; h-live; Queues; wait-vs)
open import adequacy.Cursor.Frame using (owes; Fr; f-outer; f-lanes; f-lane; f-lnct; d-outer)
open import adequacy.Cursor.Rise using (Inv; RT; SimC; settled; pending; flying; adrift)
open import adequacy.Enter using (module Lanes; within-sound)
open import adequacy.Walk using (dead-closed)
open import adequacy.Up using (module Past; VHot; vhot-hots; begun-out; nr-≈; nr-tr; join-nr; fr-up; After)

-- A begun lane's value, passed.
begun-nq : ∀ {Γ} {sc} {Rl C A B} {P : Pol A B} {O : EmissionSet A} {vs ls n q a}
         → Begun {Γ} sc Rl C P O vs ls n → (q , a) ∈ vs → ¬ Owes C q
begun-nq (more _ nq _ _ _) (here refl) = nq
begun-nq (more _ _ _ _ bg) (there i)   = begun-nq bg i

-- The lane subscribed where its joiner's observer is open.
start-open : ∀ {R Γ A B} {c : Ctx R Γ B} {op} {f : A → Obs Timeline Γ B} {ω d n q o ls a p} → closed c ≡ false
           → start c op f ω d n q o ls a p
             ≡ ⟨ inCut true (attAt (p ++ [ ix 1 ])) (inLn true (inLanes op f ω d (suc n) q o (reverse ls) [] c)) , pend (f a) (p ++ [ ix 1 ]) , subscribing , p ++ [ ix 1 ] ⟩
start-open cl rewrite cl = refl

module _ {R : Set} (Rt : EmissionSet R) where

  -- THE LANE OPENED: the frames above lifted past `p`, the joiner's
  -- bookkeeping with the value begun, its lane pending in its region.
  opens : ∀ {Cr Γ A B} op {f : A → Obs Timeline Γ B} {ω d n q ls} {c : Ctx R Γ B} {o a p Rg E E′}
        → Fr Rt Cr (bef p) Rg c owes E′ → (ji : JInv (scopeOf c) f E)
        → Joined (scopeOf c) (JRl (scopeOf c) Rg op f E) (bef p) (polF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) E) E d n q ls
        → JoinE (scopeOf c) op f ω E E′ → Sound (JRo (scopeOf c) Rg op f E) E → Behind (bef p) (JoinF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) E)
        → Sync (scopeOf c) (JRo (scopeOf c) Rg op f E) (aft p) o E → E p (out a)
        → Start (polF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) E) p a (p ++ [ ix 1 ])
        → pendRows (full (scopeOf c)) (f a) (p ++ [ ix 1 ]) ≈ Lane (polF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) E) p a
        → Runs (polF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) E) p → (∀ {q q′} → Kill (polF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) E) q q′ → ⊥)
        → T (not (Queues (polF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) E)))
        → Σ Cur λ Cr′ → Inv Rt Cr′ (aft p) ⟨ inCut true (attAt (p ++ [ ix 1 ])) (inLn true (inLanes op f ω d (suc n) q o (reverse ls) [] c))
                                            , pend (f a) (p ++ [ ix 1 ]) , subscribing , p ++ [ ix 1 ] ⟩
                        × Moves (RT Rt Cr) [] (RT Rt Cr′)
  opens op {f = f} {d = d} {n = n} {ls = ls} {c = c} {a = a} {p = p} {Rg = Rg} {E = E} fr ji jn@(joined {vs = vs} {ws = ws} bg wt wh od ah ao en li) m so bh sy row st ln ru nk nq =
    Cr↑ , pending (f-lnct (f-lane (f-lanes {D = aft p} fr↑ ji sy lf row (≺-irrefl {p}) ru (h-live st ln (λ k → proj₂ (proj₂ (kill-out op k)))) none (sym (+-comm n 1))
                                           (wait-vs {O = E} nq (wait-up (λ iv lc → λ { refl → nl (rl (begun-out bg iv) lc) }) ah′ wt)) wh′ od′ ah″ ao′ en li m so (λ _ → within-sound {sc = sc} (JInv.fi ji a s ok) wi) (behind-up bh) (λ ()))))
                  (≺-ext p {ix 1} [] , ok , JInv.adm ji , ≈-refl , wi)
        , moves
    where
      open Past p using (nm; owes-up; behind-up; begun-up; module Book)
      open Book {P = polF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) E} {O = E} using (ahead-up; wait-up)
      sc = scopeOf c
      P = polF op (λ a → ⟦ f a ⟧ (full sc)) E
      s = p ++ [ ix 1 ]
      io = JInv.io ji

      -- the outer's row at `p` is in what no lane's region holds
      here-o = Sound.rg so row _
      nl : ∀ {q′} → ¬ JRl sc Rg op f E q′ p
      nl r = proj₂ here-o (proj₂ r)

      rl = Lanes.lane-rows sc f ji op li

      nh : ¬ VHot (full sc) p
      nh = λ hv → proj₂ (JInv.ok ji) (vhot-hots (full sc) hv) (InvAt.world io row) (⊑-inside (⊑ʷ-refl p))

      lifted = fr-up Rt fr tt (proj₁ here-o)
                 (nr-≈ (proj₂ m) (nr-tr (join-nr op (λ a → ⟦ f a ⟧ (full sc)) rl (λ y → end-at (InvAt.func io row y)) (λ _ _ _ r → nl r)))) nh
        where
          end-at : ∀ {b} → out b ≡ end → _
          end-at ()
      Cr↑ = proj₁ lifted
      fr↑ = proj₁ (proj₂ lifted)
      moves = proj₂ (proj₂ lifted)

      ok = ok-step p (ok-in (JInv.ok ji) (InvAt.world io row) (InvAt.real io row))
      wi = Lanes.lane-within sc f ji op li row st

      lf = subst (λ l → Begun sc (JRl sc Rg op f E) (aft p) P E vs l n) (sym (reverse-involutive ls)) (begun-up (λ k → ⊥-elim (nk k)) (λ _ → nl) nh bg)

      -- no begun lane ends at `p`
      ah′ : Ahead (aft p) P vs ws
      ah′ = ahead-up (λ iv lc → λ { refl → nl (rl (begun-out bg iv) lc) }) ah
      ah″ : Ahead (aft p) P (vs ++ (p , a) ∷ []) ws
      ah″ iw st′ with ah′ iw st′
      ... | q′ , a′ , c′ , iv , rest = q′ , a′ , c′ , ∈-++⁺ˡ iv , rest

      ao′ : Asc (vs ++ (p , a) ∷ [])
      ao′ = pairs-++⁺ ao ([]ᴬ ∷ᴾ []ᴾ) (tabulate λ {x} i → before {proj₁ x} (begun-nq bg i) ∷ᴬ []ᴬ)
        where
          before : ∀ {q′} → ¬ Owes (bef p) q′ → q′ ≺ p
          before {q′} nq with ≼-or-≻ p q′
          ... | inj₁ pq = ⊥-elim (nq pq)
          ... | inj₂ qp = qp

      wh′ : Whole (aft p) P E (vs ++ (p , a) ∷ []) ws
      wh′ {q′} y nq r with p ≟ᵖ q′
      ... | yes refl with InvAt.func io row y
      ...   | refl = inj₁ (∈-++⁺ʳ vs (here refl))
      wh′ {q′} y nq r | no ne = [ (λ i → inj₁ (∈-++⁺ˡ i)) , inj₂ ]′ (wh y (λ o → nq (owes-up ne o)) r)

      od′ : OuterDone (aft p) E d
      od′ = (λ t → let (c′ , y , n′) = proj₁ od t in c′ , y , nm n′)
          , (λ y n′ → proj₂ od y (λ o → n′ (owes-up (λ { refl → end-out (InvAt.func io row y) }) o)))
        where
          end-out : ∀ {b} → out b ≡ end → _
          end-out ()

  -- A MERGE'S VALUE begins its lane at once.  In a part no live node
  -- reads, the lane is subscribed by none: it settles there, running
  -- nothing.
  merge-start : ∀ {Γ A B} {f : A → Obs Timeline Γ B} {ω d n q ls} {c : Ctx R Γ B} {o a p}
              → SimC Rt ⟨ inOuter (mergeᶠ nothing) f ω d n q ls c , o , rising (nx a) , p ⟩ [] (start c (mergeᶠ nothing) f ω d n q o ls a p)
  merge-start {f = f} {c = c} {a = a} {p = p} {Cr = Cr} (flying (f-outer fr ji jn m so bh) cl (sy , row)) =
    let (Cr′ , i , mv) = opens (mergeᶠ nothing) fr ji jn m so bh sy row refl ln tt (λ ()) tt
    in subst (After Rt Cr) (sym (start-open {c = c} {op = mergeᶠ nothing} {f = f} {a = a} {p = p} cl)) (Cr′ , aft p , i , mv)
    where
      s = p ++ [ ix 1 ]
      I = JInv.fi ji a s (ok-step p (ok-in (JInv.ok ji) (InvAt.world (JInv.io ji) row) (InvAt.real (JInv.io ji) row)))
      g : ∀ {y e} → enter (⟦ f a ⟧ (full (scopeOf c))) s y e → _
      g x = world-after (InvAt.world I x) (InvAt.real I x)
      ln : pendRows (full (scopeOf c)) (f a) s ≈ LaneOf (λ a → ⟦ f a ⟧ (full (scopeOf c))) p a
      ln = record { alike = (λ (x , v) → (x , g x) , v) ⇄ (λ ((x , _) , v) → x , v)
                  ; cov = [] , λ x → inj₁ (proj₁ x)
                  ; voc = λ x → x , g x }
  merge-start (flying (d-outer _ _ _ _) _ ())
  merge-start (adrift fr cl _) = ⊥-elim (subst T cl (dead-closed Rt fr refl))
  merge-start (settled () _ _)

  postulate
    -- A BOUNDED MERGE'S VALUE: its lane begun while a slot is free, else
    -- queued, absorbed.
    rise-outer-bounded : ∀ {Γ A B} {m} {f : A → Obs Timeline Γ B} {ω} {d n q ls} {c : Ctx R Γ B} {o a p k′ sh t}
                       → rise (inOuter (mergeᶠ (just m)) f ω d n q ls c) o (nx a) p ≡ moved k′ sh t
                       → SimC Rt ⟨ inOuter (mergeᶠ (just m)) f ω d n q ls c , o , rising (nx a) , p ⟩ sh k′
    -- A SWITCH'S VALUE: every begun lane killed, the value's begun.
    rise-outer-switch : ∀ {Γ A B} {f : A → Obs Timeline Γ B} {ω} {d n q ls} {c : Ctx R Γ B} {o a p k′ sh t}
                      → rise (inOuter switchᶠ f ω d n q ls c) o (nx a) p ≡ moved k′ sh t
                      → SimC Rt ⟨ inOuter switchᶠ f ω d n q ls c , o , rising (nx a) , p ⟩ sh k′
    -- AN EXHAUST'S VALUE: its lane begun while none runs, else dropped.
    rise-outer-exhaust : ∀ {Γ A B} {f : A → Obs Timeline Γ B} {ω} {d n q ls} {c : Ctx R Γ B} {o a p k′ sh t}
                       → rise (inOuter exhaustᶠ f ω d n q ls c) o (nx a) p ≡ moved k′ sh t
                       → SimC Rt ⟨ inOuter exhaustᶠ f ω d n q ls c , o , rising (nx a) , p ⟩ sh k′

  rise-outer-nx : ∀ {Γ A B} {op} {f : A → Obs Timeline Γ B} {ω} {d n q ls} {c : Ctx R Γ B} {o a p k′ sh t}
                → rise (inOuter op f ω d n q ls c) o (nx a) p ≡ moved k′ sh t → SimC Rt ⟨ inOuter op f ω d n q ls c , o , rising (nx a) , p ⟩ sh k′
  rise-outer-nx {op = mergeᶠ nothing}  refl = merge-start
  rise-outer-nx {op = mergeᶠ (just m)} eq   = rise-outer-bounded eq
  rise-outer-nx {op = switchᶠ}         eq   = rise-outer-switch eq
  rise-outer-nx {op = exhaustᶠ}        eq   = rise-outer-exhaust eq
