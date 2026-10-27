{-# OPTIONS --guardedness #-}

-- A SUBSCRIPTION'S ROOM, KEPT (`fresh-next`): every step keeps `Fresh`.
-- Only a step to a pending subscription has anything to show; every other
-- state's room is trivial.  A begin hands it down (`begin-fresh`); a
-- lane begun by its outer's value or by a freed slot, and a connect's
-- source subscribed once its body is, are the leaves.
module adequacy.Engine.Freshen where

open import Data.Bool using (true; false; not)
open import Data.List using ([]; _ʳ++_; _∷_; [_])
open import Data.Maybe using (just; nothing)
open import Data.Nat using (pred)
open import Data.Product using (_,_; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Tree using (Obs)
open import denotation.MonotonicList.Events using (Timeline; ix; emit; stall; close)
open import operation.PureObservable using (Tape; play; ending; over; module Machine; module Driver)
open import adequacy.Engine.Fold using (Base; Owns; attO; bodyO; cpO; cutO; joinO; leafO; ofO; owedO; srcAttO; search-hit)
open import adequacy.Engine.Pick using (Order; module Order)
open import adequacy.Engine.Fresh using (Fresh; NextFresh; begin-fresh)

open Machine using (St; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
  Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody; plug; closed;
  CS; cs; free; cpAt; cutAt; overAt; nx; cp; ⟨_,_,_,_⟩; subscribing; absorbed; rising;
  bodyM; search; found; leaf; rise; run; admit; dequeue; ended; alive; unsubIf; _⊕_)
  renaming (cut to cutᴹ)

module _ {R : Set} where
  open Driver R using (Step; step; played; took)

  postulate
    -- THE STILL'S SUBTREE, BEGUN: a lane begun where its outer's value
    -- rose, or where a freed slot dequeues the next, has room among the
    -- frames above it and the parts racing it.
    admit-fresh : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) ls a p
                → Base ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩ → Order ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩
                → NextFresh (took (admit c op f d n q o ls a p))
    dequeue-fresh : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) pre post (s : St Γ B) p
                  → Base ⟨ inLanes op f d n q o pre post c , s , rising cp , p ⟩ → Order ⟨ inLanes op f d n q o pre post c , s , rising cp , p ⟩
                  → alive s ≡ true → Fresh (dequeue c op f d (pred n) q o (pre ʳ++ ended s ∷ post) p)
    -- A connect's source, subscribed once its body is.
    src-fresh : ∀ {Γ A} (c : Ctx R Γ A) (s : St Γ A) p → Base ⟨ c , s , absorbed , p ⟩ → Order ⟨ c , s , absorbed , p ⟩
              → ∀ {Δ X B} {c′ : Ctx R Δ B} {kk} {o : St Δ X} {b : St (X ∷ Δ) B} {key q}
              → search top (plug c s) ≡ just (found (Δ , B , c′ , connS kk o b) bodyM key) → CS.bodyAt kk ≡ just q
              → Fresh ⟨ inSrc (record kk { bodyAt = nothing ; attSrc = just (q ⊕ [ ix 1 ]) }) b c′ , o , subscribing , q ⊕ [ ix 1 ] ⟩

  rise-fresh : ∀ {Γ A} (c : Ctx R Γ A) (s : St Γ A) e p → Base ⟨ c , s , rising e , p ⟩ → Order ⟨ c , s , rising e , p ⟩
             → NextFresh (took (rise c s e p))
  rise-fresh top                               s (nx a) p b o = λ ()
  rise-fresh top                               s cp     p b o = tt
  rise-fresh (inMap f c)                       s e      p b o = λ _ → tt
  rise-fresh (inScan f z c)                    s (nx a) p b o = λ _ → tt
  rise-fresh (inScan f z c)                    s cp     p b o = λ _ → tt
  rise-fresh (inCut l a c)                     s e      p b o = λ _ → tt
  rise-fresh (inLn d c)                        s e      p b o = λ _ → tt
  rise-fresh (inTake i q free c)               s (nx a) p b o with q a | i
  ... | true  | _     = λ _ → tt
  ... | false | true  = λ _ → tt
  ... | false | false = λ _ → tt
  rise-fresh (inTake i q free c)               s cp     p b o = λ _ → tt
  rise-fresh (inTake i q (cpAt r) c)           s e      p b o = λ _ → tt
  rise-fresh (inTake i q (cutAt r) c)          s e      p b o = λ _ → tt
  rise-fresh (inTake i q (overAt r) c)         s e      p b o = λ _ → tt
  rise-fresh (inOuter op f d n q ls c)         s (nx a) p b o = admit-fresh c op f d n q s ls a p b o
  rise-fresh (inOuter op f d n q ls c)         s cp     p b o = λ _ → tt
  rise-fresh (inLanes op f d n q o pre post c) s (nx a) p b v with alive s
  ... | true  = λ _ → tt
  ... | false = λ _ → tt
  rise-fresh (inLanes op f d n q o pre post c) s cp     p b v with alive s in al
  ... | true  = dequeue-fresh c op f d n q o pre post s p b v al
  ... | false = λ _ → tt
  rise-fresh (inSrc k d c)                     s (nx a) p b o = λ _ → tt
  rise-fresh (inSrc k d c)                     s cp     p b o = λ _ → tt
  rise-fresh (inBody k d c)                    s (nx a) p b o = λ _ → tt
  rise-fresh (inBody k d c)                    s cp     p b o = λ _ → tt

  played-fresh : ∀ {A} d (l : Tape A) cl dv st → (∀ e l′ b′ p′ → Fresh (dv e l′ b′ p′)) → (∀ l′ → Fresh (st l′))
               → NextFresh (played (leaf d l cl dv st))
  played-fresh d     (ending e)                  cl    dv st g s = g cp over false e
  played-fresh false (play τ u i t fr)           cl    dv st g s = s over
  played-fresh false over                        cl    dv st g s = s over
  played-fresh true  (play τ u i t fr)           true  dv st g s = s over
  played-fresh true  over                        true  dv st g s = s over
  played-fresh true  (play τ u i t (emit a k))   false dv st g s = g _ _ _ _
  played-fresh true  (play τ u i t (stall k))    false dv st g s = s _
  played-fresh true  (play τ u i t (close k))    false dv st g s = s _
  played-fresh true  over                        false dv st g s = s over

  -- A mark run subscribes nothing but a connect's source.
  run-fresh : ∀ {Γ A} (c : Ctx R Γ A) (s : St Γ A) p → Base ⟨ c , s , absorbed , p ⟩ → Order ⟨ c , s , absorbed , p ⟩
            → ∀ {Δ B} {c′ : Ctx R Δ B} {s′ : St Δ B} {m key} → search top (plug c s) ≡ just (found (Δ , B , c′ , s′) m key) → Owns s′ m
            → NextFresh (took (run c′ s′ m p))
  run-fresh c s p b v {c′ = c′} hit (ofO {xs = xs}) with closed c′ | xs
  ... | true  | _       = λ _ → tt
  ... | false | []      = λ _ → tt
  ... | false | x ∷ xs′ = λ _ → tt
  run-fresh c s p b v hit (attO {l = l} {s = t}) with unsubIf (not l) t
  ... | t′ , w = λ _ → tt
  run-fresh c s p b v hit cpO = λ _ → tt
  run-fresh c s p b v hit (cutO {s = t}) with cutᴹ t
  ... | t′ , w = λ _ → tt
  run-fresh c s p b v hit (bodyO {k = cs cl sl sa (just q) as ow r e} _) = src-fresh c s p b v hit refl
  run-fresh c s p b v hit (bodyO {k = cs cl sl sa nothing as ow r e} ())
  run-fresh c s p b v hit (srcAttO {k = cs cl sl sa ba (just q) ow r e} {o = o} _) with unsubIf (not sl) o
  ... | o′ , w = λ _ → tt
  run-fresh c s p b v hit (srcAttO {k = cs cl sl sa ba nothing ow r e} ())
  run-fresh c s p b v hit (owedO {k = cs cl sl sa ba as (just q) r e} {o = o} _) with unsubIf sa o
  ... | o′ , w = λ _ → tt
  run-fresh c s p b v hit (owedO {k = cs cl sl sa ba as nothing r e} ())
  run-fresh c s p b v hit (joinO {e = nx a}) = λ _ → tt
  run-fresh c s p b v hit (joinO {e = cp})   = λ _ → tt
  run-fresh c s p b v hit (leafO {b = d} {l = l} _) = played-fresh d l _ _ _ (λ _ _ _ _ _ → tt) (λ _ _ → tt)

  -- EVERY STEP KEEPS A SUBSCRIPTION'S ROOM.
  fresh-next : ∀ k → Base k → Order k → NextFresh (step k)
  fresh-next ⟨ c , s , rising e , p ⟩ b o = rise-fresh c s e p b o
  fresh-next ⟨ c , pend x , subscribing , p ⟩ b o = begin-fresh c x p (Order.fresh o tt)
  fresh-next ⟨ c , coldS xb xl , subscribing , p ⟩ b o = Order.fresh o
  fresh-next ⟨ c , ofS xi xp xxs , subscribing , p ⟩ b o = Order.fresh o
  fresh-next ⟨ c , doneS , subscribing , p ⟩ b o = Order.fresh o
  fresh-next ⟨ c , mapS xf xs , subscribing , p ⟩ b o = Order.fresh o
  fresh-next ⟨ c , scanS xf xz xs , subscribing , p ⟩ b o = Order.fresh o
  fresh-next ⟨ c , cutS xl xa xs , subscribing , p ⟩ b o = Order.fresh o
  fresh-next ⟨ c , lnS xb xs , subscribing , p ⟩ b o = Order.fresh o
  fresh-next ⟨ c , takeS xi xq xw xs , subscribing , p ⟩ b o = Order.fresh o
  fresh-next ⟨ c , flatS xop xf xd xn xq xo xls , subscribing , p ⟩ b o = Order.fresh o
  fresh-next ⟨ c , connS xk xo xb , subscribing , p ⟩ b o = Order.fresh o
  fresh-next ⟨ c , joinS xj xg xx xib , subscribing , p ⟩ b o = Order.fresh o
  fresh-next ⟨ c , s , absorbed , p ⟩ b o with search top (plug c s) in hit
  ... | nothing = tt
  ... | just (found (_ , _ , c′ , s′) m key) = run-fresh c s p b o hit (proj₂ (search-hit (plug c s) hit))
