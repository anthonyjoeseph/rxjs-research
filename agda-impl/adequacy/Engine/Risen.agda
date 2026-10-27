{-# OPTIONS --guardedness #-}

-- THE STILL'S SUBTREE, RISEN (`rise-causal`): a rise keeps the tree
-- causal.  Most rises move only the hole, so the tree is the one already
-- causal, or its frame's bookkeeping alone moves (a scan's seed, a flatMap
-- marked done), which owns nothing.  The leaves are the rises that key
-- something new: a takeWhile's failing value its completion, an outer's
-- value its lane, a lane's end the next queued, a source's event its
-- joiners, a body's end its owed close.
module adequacy.Engine.Risen where

open import Data.Bool using (true; false)
open import Data.List using (_ʳ++_; _∷_)
open import Data.Maybe using (just)
open import Data.Nat using (pred)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Tree using (Obs)
open import denotation.MonotonicList.Events using (Timeline)
open import operation.PureObservable using (module Machine; module Driver)
open import adequacy.Engine.Causal using (Causal; causal-run; w≼; nodeW; scan≼; flat≼; ≼-refl; lanes-refl)
open import adequacy.Engine.Fold using (Base)
open import adequacy.Engine.Pick using (Order; module Order; whole)

open Machine using (St; flatS; takeS; connS; Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody; plug;
  free; cpAt; cutAt; overAt; nx; cp; ⟨_,_,_,_⟩; rising; rise; admit; dequeue; ended; alive)

module _ {R : Set} where
  open Driver R using (Step; silent; value; complete; drained; took)

  NextCaused : Step → Set
  NextCaused (silent t k)    = Causal (whole k)
  NextCaused (value t p a k) = Causal (whole k)
  NextCaused (complete p)    = ⊤
  NextCaused drained         = ⊤

  postulate
    take-fail-causal : ∀ {Γ A} (c : Ctx R Γ A) i q (s : St Γ A) a p
                     → Base ⟨ inTake i q free c , s , rising (nx a) , p ⟩ → Order ⟨ inTake i q free c , s , rising (nx a) , p ⟩
                     → q a ≡ false → Causal (plug c (takeS i q (cpAt p) s))
    admit-causal : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) ls a p
                 → Base ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩ → Order ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩
                 → NextCaused (took (admit c op f d n q o ls a p))
    dequeue-causal : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) pre post (s : St Γ B) p
                   → Base ⟨ inLanes op f d n q o pre post c , s , rising cp , p ⟩ → Order ⟨ inLanes op f d n q o pre post c , s , rising cp , p ⟩
                   → alive s ≡ true → Causal (whole (dequeue c op f d (pred n) q o (pre ʳ++ ended s ∷ post) p))
    feed-causal : ∀ {Γ X B} (c : Ctx R Γ B) k (b : St (X ∷ Γ) B) (s : St Γ X) e p
                → Base ⟨ inSrc k b c , s , rising e , p ⟩ → Order ⟨ inSrc k b c , s , rising e , p ⟩
                → NextCaused (took (rise (inSrc k b c) s e p))
    owed-causal : ∀ {Γ X B} (c : Ctx R Γ B) k (o : St Γ X) (s : St (X ∷ Γ) B) p
                → Base ⟨ inBody k o c , s , rising cp , p ⟩ → Order ⟨ inBody k o c , s , rising cp , p ⟩
                → Causal (plug c (connS (record k { owedAt = just p }) o s))

  rise-causal : ∀ {Γ A} (c : Ctx R Γ A) (s : St Γ A) e p → Base ⟨ c , s , rising e , p ⟩ → Order ⟨ c , s , rising e , p ⟩
              → NextCaused (took (rise c s e p))
  rise-causal top                               s (nx a) p b o = Order.causal o
  rise-causal top                               s cp     p b o = tt
  rise-causal (inMap f c)                       s e      p b o = Order.causal o
  rise-causal (inScan f z c)                    s (nx a) p b o =
    causal-run c {scanS f (f z a) s} {scanS f z s} (w≼ (nodeW (λ { (_ , ()) })) (scan≼ (≼-refl s))) (Order.causal o)
    where open Machine using (scanS)
  rise-causal (inScan f z c)                    s cp     p b o = Order.causal o
  rise-causal (inCut l a c)                     s e      p b o = Order.causal o
  rise-causal (inLn d c)                        s e      p b o = Order.causal o
  rise-causal (inTake i q free c)               s (nx a) p b o with q a in qa | i
  ... | true  | _     = Order.causal o
  ... | false | true  = take-fail-causal c true q s a p b o qa
  ... | false | false = take-fail-causal c false q s a p b o qa
  rise-causal (inTake i q free c)               s cp     p b o = Order.causal o
  rise-causal (inTake i q (cpAt r) c)           s e      p b o = Order.causal o
  rise-causal (inTake i q (cutAt r) c)          s e      p b o = Order.causal o
  rise-causal (inTake i q (overAt r) c)         s e      p b o = Order.causal o
  rise-causal (inOuter op f d n q ls c)         s (nx a) p b o = admit-causal c op f d n q s ls a p b o
  rise-causal (inOuter op f d n q ls c)         s cp     p b o =
    causal-run c {flatS op f true n q s ls} {flatS op f d n q s ls} (w≼ (nodeW (λ { (_ , ()) })) (flat≼ (≼-refl s) (lanes-refl ls))) (Order.causal o)
  rise-causal (inLanes op f d n q o pre post c) s (nx a) p b v with alive s
  ... | true  = Order.causal v
  ... | false = Order.causal v
  rise-causal (inLanes op f d n q o pre post c) s cp     p b v with alive s in al
  ... | true  = dequeue-causal c op f d n q o pre post s p b v al
  ... | false = Order.causal v
  rise-causal (inSrc k d c)                     s e      p b o = feed-causal c k d s e p b o
  rise-causal (inBody k d c)                    s (nx a) p b o = Order.causal o
  rise-causal (inBody k d c)                    s cp     p b o = owed-causal c k d s p b o
