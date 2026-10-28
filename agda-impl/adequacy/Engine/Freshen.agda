{-# OPTIONS --guardedness #-}

-- A SUBSCRIPTION'S ROOM, KEPT (`fresh-next`): every step keeps `Fresh`.
-- A begin hands it down (`begin-fresh`).  A rise keeps it frame by frame:
-- the rising frame's own keys are read off the aloft it held, and what a
-- rise begins (a take's completion, an outer's lane, the next queued) is
-- planted where it rose.  A mark run that rises is read off `Causal`:
-- the key it ran was aloft, so all it sows is.  The leaves are what a
-- run's node must already keep shy of where it rises, and a connect's
-- source subscribed once its body is.
module adequacy.Engine.Freshen where

open import Data.Bool using (true; false; not)
open import Data.List using (List; []; _ʳ++_; _∷_; [_]; null)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (pred; suc; _<ᵇ_; _≡ᵇ_)
open import Data.Nat.Properties using (n<1+n)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Tree using (Obs; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.MonotonicList.Events using (Timeline; ix; last; emit; stall; close)
open import operation.Key using (at)
open import operation.PureObservable using (play; ending; over; module Machine; module Driver)
open import adequacy.Engine.Causal using (Farᴷ; Every; Keys⁺; Aloft⁺; causal-own; aloft-out; far-tr; keys-map; lanes-≼; killAll-≼)
open import adequacy.Engine.Room using (Shy; aloft-hole; keys-all; lanes-all)
open import adequacy.Engine.Sown using (Proper; Plant; proper-snoc; plant-sown; plant-under)
open import adequacy.Engine.Fold using (Base; Owns; attO; bodyO; cpO; cutO; joinO; leafO; ofO; owedO; srcAttO; search-hit; found-own)
open import adequacy.Engine.Pick using (Order; module Order)
open import adequacy.Engine.Fresh using (Fresh; Risen; NextFresh; begin-fresh; past-far; sib-far; ofFut-far; shy-under; keys-ended;
  owed-to; settle-fresh; start-fresh; outer-risen; lanes-risen)

open Machine using (St; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
  Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody; plug; closed; killAll;
  CS; cs; free; cpAt; cutAt; overAt; nx; cp; ⟨_,_,_,_⟩; subscribing; absorbed; rising;
  bodyM; ofM; cpM; joinM; leafM; search; found; leaf; rise; run; admit; dequeue; ended; alive; unsubIf; _⊕_)
  renaming (cut to cutᴹ)

------------------------------------------------------------------------
-- A frame's bookkeeping risen through

module _ {R : Set} where

  -- A slot freed, its next started or the flatMap settled.
  dequeue-fresh : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) ls p
                → Risen c (flatS op f d n q o ls) p → Fresh (dequeue c op f d n q o ls p)
  dequeue-fresh c op f d n []      o ls p r = settle-fresh d n true r
  dequeue-fresh c op f d n (a ∷ q) o ls p r = start-fresh c op f d n q o ls a p r

------------------------------------------------------------------------
-- The leaves

module _ {R : Set} where
  open Driver R using (Step; step; played; took)

  postulate
    -- A connect's source, subscribed once its body is.
    src-fresh : ∀ {Γ A} (c : Ctx R Γ A) (s : St Γ A) p → Base ⟨ c , s , absorbed , p ⟩ → Order ⟨ c , s , absorbed , p ⟩
              → ∀ {Δ X B} {c′ : Ctx R Δ B} {kk} {o : St Δ X} {b : St (X ∷ Δ) B} {key q}
              → search top (plug c s) ≡ just (found (Δ , B , c′ , connS kk o b) bodyM key) → CS.bodyAt kk ≡ just q
              → Fresh ⟨ inSrc (record kk { bodyAt = nothing ; attSrc = just (q ⊕ [ ix 1 ]) }) b c′ , o , subscribing , q ⊕ [ ix 1 ] ⟩
    -- An of's place, below the run's root.
    of-proper : ∀ {Γ A} (c : Ctx R Γ A) (s : St Γ A) p → Base ⟨ c , s , absorbed , p ⟩ → Order ⟨ c , s , absorbed , p ⟩
              → ∀ {Δ B} {c′ : Ctx R Δ B} {i p₀} {xs : List B} {key}
              → search top (plug c s) ≡ just (found (Δ , B , c′ , ofS i p₀ xs) ofM key) → Proper p₀
    -- A completed takeWhile's source: shy of what its completion plants.
    take-shy : ∀ {Γ A} (c : Ctx R Γ A) (s : St Γ A) p → Base ⟨ c , s , absorbed , p ⟩ → Order ⟨ c , s , absorbed , p ⟩
             → ∀ {Δ B} {c′ : Ctx R Δ B} {i q p₀} {t : St Δ B} {key}
             → search top (plug c s) ≡ just (found (Δ , B , c′ , takeS i q (cpAt p₀) t) cpM key) → Keys⁺ (Shy (p₀ ⊕ [ last ])) t
    -- A joiner's next delivery: shy of what the one it runs plants.
    join-shy : ∀ {Γ A} (c : Ctx R Γ A) (s : St Γ A) p → Base ⟨ c , s , absorbed , p ⟩ → Order ⟨ c , s , absorbed , p ⟩
             → ∀ {Δ B} {c′ : Ctx R Δ B} {j g x q₀ e ib} {key}
             → search top (plug c s) ≡ just (found (Δ , B , c′ , joinS {A = B} j g x ((q₀ , e) ∷ ib)) joinM key)
             → Proper q₀ × Every (Shy q₀) (joinS j g x ib)
    -- A cold's completion, below the run's root.
    cold-end : ∀ {Γ A} (c : Ctx R Γ A) (s : St Γ A) p → Base ⟨ c , s , absorbed , p ⟩ → Order ⟨ c , s , absorbed , p ⟩
             → ∀ {Δ B} {c′ : Ctx R Δ B} {b e} {key}
             → search top (plug c s) ≡ just (found (Δ , B , c′ , coldS {A = B} b (ending e)) leafM key) → Proper e
    -- A cold's next frame: shy of what the value it plays plants.
    cold-shy : ∀ {Γ A} (c : Ctx R Γ A) (s : St Γ A) p → Base ⟨ c , s , absorbed , p ⟩ → Order ⟨ c , s , absorbed , p ⟩
             → ∀ {Δ B} {c′ : Ctx R Δ B} {b τ u i t a k} {key}
             → search top (plug c s) ≡ just (found (Δ , B , c′ , coldS {A = B} b (play τ u i t (emit a k))) leafM key)
             → Every (Shy (u ⊕ [ ix i ])) (coldS {Δ} true (play τ u (suc i) t k))

  -- A mark run that rises: the key it ran was aloft, so all it plants is.
  rose : ∀ {Γ A} {c : Ctx R Γ A} {s : St Γ A} {p} → Order ⟨ c , s , absorbed , p ⟩
       → ∀ {Δ B} {c′ : Ctx R Δ B} {s′ : St Δ B} {m key} → search top (plug c s) ≡ just (found (Δ , B , c′ , s′) m key)
       → (t′ : St Δ B) → ∀ {m′ x} → (m , key) ∈ [ (m′ , at x) ] → ∀ {h} → Plant x h → Aloft⁺ h c′ t′
  rose {c = c} {s} v {c′ = c′} {s′} hit t′ {m′} {x} i {h} w = go i (causal-own (Order.causal v) c′ s′ (proj₁ (search-hit (plug c s) hit)) (found-own (plug c s) hit))
    where
      go : ∀ {m key} → (m , key) ∈ [ (m′ , at x) ] → Aloft⁺ key c′ s′ → Aloft⁺ h c′ t′
      go (here refl) a = aloft-hole c′ (aloft-out c′ s′ a (plant-sown w))
      go (there ())  a

  -- An outer's value: its lane started where it rose.
  admit-fresh : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) ls a p
              → Risen (inOuter op f d n q ls c) o p → NextFresh (took (admit c op f d n q o ls a p))
  admit-fresh c (mergeᶠ nothing)  f d n q o ls a p r = start-fresh c (mergeᶠ nothing) f d n q o ls a p (outer-risen c (mergeᶠ nothing) f d n q ls d r)
  admit-fresh c (mergeᶠ (just m)) f d n q o ls a p r with n <ᵇ m
  ... | true  = start-fresh c (mergeᶠ (just m)) f d n q o ls a p (outer-risen c (mergeᶠ (just m)) f d n q ls d r)
  ... | false = tt
  admit-fresh c switchᶠ           f d n q o ls a p (pr , ks , g) with killAll ls | killAll-≼ ls
  ... | ls′ , t | kw = start-fresh c switchᶠ f d 0 q o ls′ a p {d} {n} {q}
    (pr , ((λ { (_ , ()) }) , ks , lanes-≼ (λ le sh {h} w → far-tr h le (sh w)) kw (lanes-all ls (λ w → proj₁ (g w)))) , λ w → aloft-hole c (proj₂ (g w)))
  admit-fresh c exhaustᶠ          f d n q o ls a p r with n ≡ᵇ 0
  ... | true  = start-fresh c exhaustᶠ f d n q o ls a p (outer-risen c exhaustᶠ f d n q ls d r)
  ... | false = tt

  rise-fresh : ∀ {Γ A} (c : Ctx R Γ A) (s : St Γ A) e p → Base ⟨ c , s , rising e , p ⟩ → Order ⟨ c , s , rising e , p ⟩
             → NextFresh (took (rise c s e p))
  rise-fresh top                               s (nx a) p b o = tt
  rise-fresh top                               s cp     p b o = tt
  rise-fresh (inMap f c)                       s e      p b o = let (pr , ks , a) = Order.fresh o in pr , ((λ { (_ , ()) }) , ks) , a
  rise-fresh (inScan f z c)                    s (nx x) p b o = let (pr , ks , a) = Order.fresh o in pr , ((λ { (_ , ()) }) , ks) , λ w → aloft-hole c (a w)
  rise-fresh (inScan f z c)                    s cp     p b o = let (pr , ks , a) = Order.fresh o in pr , ((λ { (_ , ()) }) , ks) , a
  rise-fresh (inCut l x c)                     s e      p b o with l
  ... | true  = let (pr , ks , a) = Order.fresh o in pr , ((λ f w → proj₁ (a w) f) , ks) , λ w → proj₂ (a w)
  ... | false = tt
  rise-fresh (inLn d c)                        s e      p b o = let (pr , ks , a) = Order.fresh o in pr , ((λ { (_ , ()) }) , ks) , a
  rise-fresh (inTake i q free c)               s (nx x) p b o with q x | i
  ... | true  | _     = let (pr , ks , a) = Order.fresh o in pr , ((λ { (_ , ()) }) , ks) , a
  ... | false | true  = let (pr , ks , a) = Order.fresh o in proper-snoc p (ix 0) ,
    ((λ { (_ , here refl) → sib-far p pr tt tt (λ ()) ; (_ , there ()) }) , keys-map (λ {k} → shy-under p (ix 0) {k}) s ks) ,
    λ w → aloft-hole c (a (plant-under p (ix 0) w))
  ... | false | false = tt
  rise-fresh (inTake i q free c)               s cp     p b o = let (pr , ks , a) = Order.fresh o in pr , ((λ { (_ , ()) }) , ks) , a
  rise-fresh (inTake i q (cpAt r) c)           s e      p b o = tt
  rise-fresh (inTake i q (cutAt r) c)          s e      p b o = tt
  rise-fresh (inTake i q (overAt r) c)         s e      p b o = tt
  rise-fresh (inOuter op f d n q ls c)         s (nx a) p b o = admit-fresh c op f d n q s ls a p (Order.fresh o)
  rise-fresh (inOuter op f d n q ls c)         s cp     p b o with d
  ... | true  = tt
  ... | false = settle-fresh true n (null q) (outer-risen c op f false n q ls true (Order.fresh o))
  rise-fresh (inLanes op f d n q o pre post c) s (nx a) p b v with alive s
  ... | true  = lanes-risen c op f d n q o pre post n s (proj₁ (proj₂ (Order.fresh v))) (Order.fresh v)
  ... | false = tt
  rise-fresh (inLanes op f d n q o pre post c) s cp     p b v with alive s
  ... | true  = dequeue-fresh c op f d (pred n) q o (pre ʳ++ ended s ∷ post) p
                  (lanes-risen c op f d n q o pre post (pred n) (ended s) (keys-ended s (proj₁ (proj₂ (Order.fresh v)))) (Order.fresh v))
  ... | false = tt
  rise-fresh (inSrc k d c)                     s (nx a) p b o = tt
  rise-fresh (inSrc k d c)                     s cp     p b o = tt
  rise-fresh (inBody k d c)                    s (nx a) p b o = let (pr , ks , a) = Order.fresh o in
    pr , ((λ f w → proj₁ (proj₂ (proj₂ (a w))) f) , keys-all d (λ w → proj₁ (a w)) , ks) , λ w → proj₂ (proj₂ (proj₂ (a w)))
  rise-fresh (inBody k d c)                    s cp     p b o = let (pr , ks , a) = Order.fresh o in
    pr , ((λ f {h} w → owed-to {P = Farᴷ h} k {d} {d} {s} {s} p (past-far p w) (proj₁ (proj₂ (proj₂ (a w)))) f) , keys-all d (λ w → proj₁ (a w)) , ks) ,
    λ w → aloft-hole c (proj₂ (proj₂ (proj₂ (a w))))

  -- A mark run rises only where its node was keyed.
  run-fresh : ∀ {Γ A} (c : Ctx R Γ A) (s : St Γ A) p → Base ⟨ c , s , absorbed , p ⟩ → (v : Order ⟨ c , s , absorbed , p ⟩)
            → ∀ {Δ B} {c′ : Ctx R Δ B} {s′ : St Δ B} {m key} → search top (plug c s) ≡ just (found (Δ , B , c′ , s′) m key) → Owns s′ m
            → NextFresh (took (run c′ s′ m p))
  run-fresh c s p b v {c′ = c′} hit (ofO {p = p₀} {xs = []}) with closed c′
  ... | true  = tt
  ... | false = proper-snoc p₀ last , ((λ { (_ , ()) }) , tt) , rose v hit doneS (found-own (plug c s) hit)
  run-fresh c s p b v {c′ = c′} hit (ofO {i = i} {p = p₀} {xs = x ∷ xs′}) with closed c′
  ... | true  = tt
  ... | false = proper-snoc p₀ (ix i) ,
    ((λ f w → ofFut-far p₀ (of-proper c s p b v hit) i (suc i) xs′ (n<1+n i) (proj₂ f) w) , tt) , rose v hit (ofS (suc i) p₀ xs′) (found-own (plug c s) hit)
  run-fresh c s p b v hit (attO {l = l} {s = t}) with unsubIf (not l) t
  ... | t′ , w = tt
  run-fresh c s p b v {c′ = c′} hit (cpO {i = i} {q = q} {p = p₀} {s = t}) with closed c′
  ... | true  = tt
  ... | false = proper-snoc p₀ last ,
    ((λ { (_ , here refl) → λ w → past-far p₀ (plant-under p₀ last w) ; (_ , there ()) }) , take-shy c s p b v hit) ,
    rose v hit (takeS i q (cutAt p₀) t) (found-own (plug c s) hit)
  run-fresh c s p b v hit (cutO {s = t}) with cutᴹ t
  ... | t′ , w = tt
  run-fresh c s p b v hit (bodyO {k = cs cl sl sa (just q) as ow r e} _) = src-fresh c s p b v hit refl
  run-fresh c s p b v hit (bodyO {k = cs cl sl sa nothing as ow r e} ())
  run-fresh c s p b v hit (srcAttO {k = cs cl sl sa ba (just q) ow r e} {o = o} _) with unsubIf (not sl) o
  ... | o′ , w = tt
  run-fresh c s p b v hit (srcAttO {k = cs cl sl sa ba nothing ow r e} ())
  run-fresh c s p b v hit (owedO {k = cs cl sl sa ba as (just q) r e} {o = o} _) with unsubIf sa o
  ... | o′ , w = tt
  run-fresh c s p b v hit (owedO {k = cs cl sl sa ba as nothing r e} ())
  run-fresh c s p b v {c′ = c′} hit (joinO {j = j} {g = g} {x = x} {e = nx a} {ib = ib}) with g | closed c′
  ... | true  | false = proj₁ (join-shy c s p b v hit) , (proj₂ (join-shy c s p b v hit) , tt) , rose v hit (joinS j true x ib) (found-own (plug c s) hit)
  ... | true  | true  = tt
  ... | false | _     = tt
  run-fresh c s p b v {c′ = c′} hit (joinO {j = j} {g = g} {x = x} {e = cp} {ib = ib}) with g | closed c′
  ... | true  | false = proj₁ (join-shy c s p b v hit) , (proj₂ (join-shy c s p b v hit) , tt) , rose v hit (joinS j false x ib) (found-own (plug c s) hit)
  ... | true  | true  = tt
  ... | false | _     = tt
  run-fresh c s p b v {c′ = c′} hit (leafO {l = ending e} refl) with closed c′
  ... | true  = tt
  ... | false = cold-end c s p b v hit , ((λ { (_ , ()) }) , tt) , rose v hit (coldS false over) (found-own (plug c s) hit)
  run-fresh c s p b v hit (leafO {b = false} {l = play τ u i t fr} refl) = tt
  run-fresh c s p b v {c′ = c′} hit (leafO {b = true} {l = play τ u i t (emit a k)} refl) with closed c′
  ... | true  = tt
  ... | false = proper-snoc u (ix i) , (cold-shy c s p b v hit , tt) , rose v hit (coldS true (play τ u (suc i) t k)) (found-own (plug c s) hit)
  run-fresh c s p b v {c′ = c′} hit (leafO {b = true} {l = play τ u i t (stall k)} refl) with closed c′
  ... | true  = tt
  ... | false = tt
  run-fresh c s p b v {c′ = c′} hit (leafO {b = true} {l = play τ u i t (close k)} refl) with closed c′
  ... | true  = tt
  ... | false = tt
  run-fresh c s p b v hit (leafO {l = over} ())

  -- EVERY STEP KEEPS A SUBSCRIPTION'S ROOM.
  fresh-next : ∀ k → Base k → Order k → NextFresh (step k)
  fresh-next ⟨ c , s , rising e , p ⟩ b o = rise-fresh c s e p b o
  fresh-next ⟨ c , pend x , subscribing , p ⟩ b o = begin-fresh c x p (Order.fresh o)
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
