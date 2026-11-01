{-# OPTIONS --guardedness #-}

-- A RISE KEEPS APART: on at its position, owing what it owed; a level
-- down inside the run, the end it now owes and its teardown inside it
-- too; a lane begun under the run; a source's feed queued under it; or
-- absorbed.
module adequacy.Apart.Rise where

open import Data.Bool using (true; false; if_then_else_)
open import Data.List using (List; []; _∷_; [_]; _++_; _ʳ++_; reverse; null)
open import Data.List.Properties using (++-assoc; ʳ++-defn; reverse-involutive)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_; ↭-refl; ↭-trans; ↭-reflexive)
open import Data.List.Relation.Binary.Sublist.Propositional using (⊆-refl; ⊆-reflexive)
open import Data.List.Relation.Binary.Sublist.Propositional.Properties using () renaming (++⁺ to ⊆-++)
open import Data.Maybe using (just)
open import Data.Nat using (suc; pred; _<ᵇ_; _≡ᵇ_)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Tree using (mergeᶠ; switchᶠ; exhaustᶠ)
open import Data.Maybe using (nothing)
open import denotation.Events using (ix; last)
open import operation.PureObservable using (PureObs; module Machine)
open Machine using (Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody; St; pend; scanS; lnS; cutS; takeS; flatS; connS;
                    CS; cs; Ev; nx; cp; attAt; free; cpAt; cutAt; overAt; closed; alive; killAll; ended; shutAt; settle; absorbed; rising;
                    start; dequeue; admit; rise)
open import adequacy.Stamped using (Ix)
open import adequacy.Apart.Cone using () renaming (pre to under)
open import adequacy.Apart.Region using (Rg; cn; pt; cl; sub-refl; sub-down; sub-pt; self)
open import adequacy.Apart.Items using (items; itemsL; itemsL-++; ended-items; killAll-⊆; csI; mI; bodyR)
open import adequacy.Apart.Kit using (W; Apart; AS; stay; quit; drop; grow; to-front; pull; cl-pt; cl-cn; cl-up; cn-up; sub-child)
open import adequacy.Apart.Feed using (feed-ap)

private
  snoc-items : ∀ {Γ A} (ls : List (St Γ A)) x → itemsL (reverse ls ʳ++ x ∷ []) ≡ itemsL ls ++ itemsL (x ∷ [])
  snoc-items ls x rewrite ʳ++-defn (reverse ls) {x ∷ []} | reverse-involutive ls = itemsL-++ ls

  mid-items : ∀ {Γ A} (pre post : List (St Γ A)) {x y} → items x ≡ items y → itemsL (pre ʳ++ x ∷ post) ≡ itemsL (pre ʳ++ y ∷ post)
  mid-items pre post {x} {y} e
    rewrite ʳ++-defn pre {x ∷ post} | ʳ++-defn pre {y ∷ post} | itemsL-++ (reverse pre) {x ∷ post} | itemsL-++ (reverse pre) {y ∷ post} | e = refl

  -- A connect's teardown owed, to the front.
  owed : ∀ (Bd As Ow Rest : List Rg) → (Bd ++ As ++ Ow) ++ Rest ↭ Ow ++ (Bd ++ As) ++ Rest
  owed Bd As Ow Rest =
    ↭-trans (↭-reflexive (trans (++-assoc Bd (As ++ Ow) Rest) (trans (cong (Bd ++_) (++-assoc As Ow Rest)) (sym (++-assoc Bd As (Ow ++ Rest))))))
      (pull (Bd ++ As) Ow Rest)

module _ {R : Set} where
  -- A lane begun a level down, its cut owed inside the run.
  start-ap : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → PureObs Γ B) d n q o ls a p → Ix p
           → W c (flatS op f d n q o ls) [ cl p ] → Apart (start c op f d n q o ls a p)
  start-ap c op f d n q o ls a p hp h with closed c
  ... | true  = stay c {t = flatS op f d n q o ls} absorbed ⊆-refl h
  ... | false = grow c {t = flatS op f d n q o ls} {t′ = flatS op f d (suc n) q o (reverse ls ʳ++ lane ∷ [])} p [ cl q′ ] [ pt q′ ] [] (items o ++ itemsL ls)
                  ↭-refl perm (sub-down (ix 1) hp ∷ sub-pt (under [ ix 1 ]) ∷ []) ((cl-pt ∷ []) ∷ [] ∷ []) h
    where
      q′ = p ++ [ ix 1 ]
      lane = lnS true (cutS true (attAt q′) (pend (f a) q′))
      perm : items o ++ itemsL (reverse ls ʳ++ lane ∷ []) ↭ pt q′ ∷ items o ++ itemsL ls
      perm rewrite snoc-items ls lane = ↭-trans (↭-reflexive (sym (++-assoc (items o) (itemsL ls) [ pt q′ ]))) (to-front (items o ++ itemsL ls) (pt q′))

  dequeue-ap : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → PureObs Γ B) d n q o ls p → Ix p
             → W c (flatS op f d n q o ls) [ cl p ] → Apart (dequeue c op f d n q o ls p)
  dequeue-ap c op f d n []      o ls p hp h = stay c {t = flatS op f d n [] o ls} (settle d n true) ⊆-refl h
  dequeue-ap c op f d n (a ∷ q) o ls p hp h =
    start-ap c op f d n q o ls a p hp (stay c {t = flatS op f d n (a ∷ q) o ls} {t′ = flatS op f d n q o ls} (rising cp) ⊆-refl h)

  admit-ap : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → PureObs Γ B) d n q o ls a p → Ix p
           → W c (flatS op f d n q o ls) [ cl p ] → AS (admit c op f d n q o ls a p)
  admit-ap c (mergeᶠ nothing)  f d n q o ls a p hp h = start-ap c _ f d n q o ls a p hp h
  admit-ap c (mergeᶠ (just m)) f d n q o ls a p hp h with n <ᵇ m
  ... | true  = start-ap c _ f d n q o ls a p hp h
  ... | false = quit c {t = flatS (mergeᶠ (just m)) f d n q o ls} {t′ = flatS (mergeᶠ (just m)) f d n (q ++ [ a ]) o ls} ⊆-refl h
  admit-ap c switchᶠ           f d n q o ls a p hp h with killAll ls | killAll-⊆ ls
  ... | ls′ , _ | kl = start-ap c switchᶠ f d 0 q o ls′ a p hp
                         (stay c {t = flatS switchᶠ f d n q o ls} {t′ = flatS switchᶠ f d 0 q o ls′} (rising cp) (⊆-++ (⊆-refl {x = items o}) kl) h)
  admit-ap c exhaustᶠ          f d n q o ls a p hp h with n ≡ᵇ 0
  ... | true  = start-ap c _ f d n q o ls a p hp h
  ... | false = drop c {t = flatS exhaustᶠ f d n q o ls} h

  rise-ap : ∀ {Γ A} (c : Ctx R Γ A) s (e : Ev A) p → Ix p → W c s [ cl p ] → AS (rise c s e p)
  rise-ap top s (nx a) p hp h = drop top {t = s} h
  rise-ap top s cp     p hp h = tt
  rise-ap (inMap f c)    s e      p hp h = h
  rise-ap (inScan f z c) s (nx a) p hp h = stay c {t = scanS f z s} {t′ = scanS f (f z a) s} (rising (nx (f z a))) ⊆-refl h
  rise-ap (inScan f z c) s cp     p hp h = h
  rise-ap (inCut l a c)  s e      p hp h = stay c {t = cutS l a s} (if l then rising e else absorbed) ⊆-refl h
  rise-ap (inLn b c)     s e      p hp h = h
  rise-ap (inTake i q free c) s (nx a) p hp h with q a | i
  ... | true  | _     = h
  ... | false | true  =
    grow c {t = takeS _ q free s} {t′ = takeS _ q (cpAt p) s} p [ cl (p ++ [ ix 0 ]) ] (cn (p ++ [ last ]) ∷ pt p ∷ []) [] (items s) ↭-refl ↭-refl
      (sub-down (ix 0) hp ∷ sub-child last hp ∷ sub-pt (self p) ∷ []) ((cl-cn hp refl ∷ cl-up ∷ []) ∷ (cn-up ∷ []) ∷ [] ∷ []) h
  ... | false | false =
    grow c {t = takeS _ q free s} {t′ = takeS _ q (cpAt p) s} p [] (cn (p ++ [ last ]) ∷ pt p ∷ []) [] (items s) ↭-refl ↭-refl
      (sub-child last hp ∷ sub-pt (self p) ∷ []) ((cn-up ∷ []) ∷ [] ∷ []) h
  rise-ap (inTake i q free c)       s cp p hp h = h
  rise-ap (inTake i q (cpAt r) c)   s e  p hp h = drop c {t = takeS i q (cpAt r) s} h
  rise-ap (inTake i q (cutAt r) c)  s e  p hp h = drop c {t = takeS i q (cutAt r) s} h
  rise-ap (inTake i q (overAt r) c) s e  p hp h = drop c {t = takeS i q (overAt r) s} h
  rise-ap (inOuter op f d n q ls c) o (nx a) p hp h = admit-ap c op f d n q o ls a p hp h
  rise-ap (inOuter op f d n q ls c) o cp     p hp h =
    stay c {t = flatS op f d n q o ls} {t′ = flatS op f true n q o ls} (if d then absorbed else settle true n (null q)) ⊆-refl h
  rise-ap (inLanes op f d n q o pre post c) s (nx b) p hp h with alive s
  ... | true  = h
  ... | false = drop c {t = flatS op f d n q o (pre ʳ++ s ∷ post)} h
  rise-ap (inLanes op f d n q o pre post c) s cp     p hp h with alive s
  ... | true  = dequeue-ap c op f d (pred n) q o (pre ʳ++ ended s ∷ post) p hp
                  (stay c {t = flatS op f d n q o (pre ʳ++ s ∷ post)} {t′ = flatS op f d (pred n) q o (pre ʳ++ ended s ∷ post)} (rising cp)
                    (⊆-reflexive (cong (items o ++_) (mid-items pre post (ended-items s)))) h)
  ... | false = drop c {t = flatS op f d n q o (pre ʳ++ s ∷ post)} h
  rise-ap (inSrc k b c) s (nx a) p hp h = feed-ap c k k s b (nx a) hp refl h
  rise-ap (inSrc k b c) s cp     p hp h = feed-ap c k (shutAt p k) s b cp hp (shut k) h
    where
      shut : ∀ k → csI (shutAt p k) ≡ csI k
      shut k with CS.srcLive k
      ... | true  = refl
      ... | false = refl
  rise-ap (inBody k o c) s (nx b) p hp h with CS.srcLive k
  ... | true  = h
  ... | false = drop c {t = connS k o s} h
  rise-ap (inBody (cs z true sa ba as ow ca ea sr sc) o c) s cp p hp h =
    grow c {t = connS (cs z true sa ba as ow ca ea sr sc) o s} {t′ = connS (cs z true sa ba as (just p) ca ea sr sc) o s} p [ cl p ] [ pt p ] Ow X
      (owed Bd As Ow Rest) (owed Bd As [ pt p ] Rest) (sub-refl (cl p) ∷ sub-pt (self p) ∷ []) ((cl-pt ∷ []) ∷ [] ∷ []) h
    where
      Bd = mI bodyR ba
      As = mI pt as
      Ow = mI pt ow
      Rest = items o ++ items s
      X = (Bd ++ As) ++ Rest
  rise-ap (inBody k@(cs z false sa ba as ow ca ea sr sc) o c) s cp p hp h = drop c {t = connS k o s} h
