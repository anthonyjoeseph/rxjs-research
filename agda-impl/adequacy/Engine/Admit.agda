{-# OPTIONS --guardedness #-}

-- AN OUTER'S VALUE ADMITTED, read off the order alone (`Order`): as
-- `admit` decides on the count of lanes running, the value begins its
-- lane past one skip, is queued, or is dropped by a busy exhaust; each
-- drops the skip the flatMap shows the value as, and where it is shown
-- every frame above passes it.
module adequacy.Engine.Admit where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_]; length; reverse; map)
open import Data.List.Properties using (map-++; reverse-involutive; ++-identityʳ)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; suc; _<ᵇ_; _≡ᵇ_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Tree using (Obs; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.MonotonicList.Events using (Timeline; Events∞; Pos; ix; idle; _∪_)
open import denotation.MonotonicList using (MonotonicList; admit; enter; head; cuts; Agreeᵀ)
open import denotation.NonExpansive using (Lanes)
import denotation.Unfold as U
open import denotation.Unfold using (NEnv; Node; states; cutᴺ; restsᶜ)
open import denotation.Denote using (flatOp)
open import operation.PureObservable using (module Machine)
open Machine using (St; Ctx; inOuter; Conf; ⟨_,_,_,_⟩; rising; nx; flatS; killAll; lnS; cutS; _⊕_)
open import adequacy.Engine.Drop using (Dropsˢ; Pass; Links; pass-of; outer-admits)
open import adequacy.Engine.Union using (∪-idleᵀ)
open import adequacy.Engine.Meaning using (envAt; risen; gh; lane; laneᴹ; lanesL; deadL; outerFrame; lanesFrame; poolT; laneRuns;
  poolRuns; lanes-refl)
open import adequacy.Engine.Above using (rests-++)
open import adequacy.Engine.Head using (Frag) renaming (Lanes to Lanesᴴ)
open import adequacy.Engine.Pick using (Order; module Order)
open import adequacy.Engine.Head.Within using (frag-flat)
open import adequacy.Engine.Ahead using (shows) renaming (Ahead to Aheadᶠ)
open import adequacy.Engine.Race using (After; TailNotBefore)
open Events∞ using (force)

-- The lanes a flatMap counts, the lanes its meaning holds.
states-length : ∀ {Γ B} (ls : List (Node Γ B)) (ρ : NEnv Γ) → length (states ls ρ) ≡ length ls
states-length []       ρ = refl
states-length (l ∷ ls) ρ = cong suc (states-length ls ρ)

-- A lane begun ahead of those kept: the merge's lanes, newest first,
-- and the pool the kept leave.
begun-runs : ∀ {Γ B} (ls : List (St Γ B)) (ρ : NEnv Γ) h → h ∷ states (lanesL ls) ρ ≡ laneRuns (reverse (reverse ls)) [] true ρ h
begun-runs ls ρ h = cong (λ x → h ∷ states (lanesL x) ρ) (sym (reverse-involutive ls))

begun-pool : ∀ {Γ B} (ls : List (St Γ B)) (ρ : NEnv Γ) h → poolT (deadL ls) ρ ≡ poolRuns (reverse (reverse ls)) [] true ρ h
begun-pool {B = B} ls ρ h rewrite reverse-involutive ls =
  trans (cong (λ x → cutᴺ (restsᶜ {B = B} x) ρ) (sym (++-identityʳ (deadL ls)))) (rests-++ (deadL ls) [] ρ)

-- What a value admitted into a flatMap's lanes leaves running: the
-- lanes a switch kills gone, and its count from none.
keptLanes : ∀ {Γ B} → FlatOp → List (St Γ B) → List (St Γ B)
keptLanes switchᶠ    ls = proj₁ (killAll ls)
keptLanes (mergeᶠ m) ls = ls
keptLanes exhaustᶠ   ls = ls

running : FlatOp → ℕ → ℕ
running switchᶠ    n = 0
running (mergeᶠ m) n = n
running exhaustᶠ   n = n

-- As `admit` decides on the count of lanes running: an outer's value
-- begins its lane, is queued behind a full merge, or is dropped by a
-- busy exhaust.
Begins : FlatOp → ℕ → Set
Begins (mergeᶠ nothing)  n = ⊤
Begins (mergeᶠ (just k)) n = (n <ᵇ k) ≡ true
Begins switchᶠ           n = ⊤
Begins exhaustᶠ          n = (n ≡ᵇ 0) ≡ true

Queues : FlatOp → ℕ → Set
Queues (mergeᶠ (just k)) n = (n <ᵇ k) ≡ false
Queues _                 n = ⊥

Ignores : FlatOp → ℕ → Set
Ignores exhaustᶠ n = (n ≡ᵇ 0) ≡ false
Ignores _        n = ⊥

-- The outer frame with its value risen, and what each admission leaves.
outerX : ∀ {R Γ A B} → Ctx R Γ B → FlatOp → (A → Obs Timeline Γ B) → Bool → List A → List (St Γ B) → St Γ A → A → Pos → Events∞ B
outerX c op f d q ls o a p = outerFrame op (lane f) d q (lanesL ls) (deadL ls) (envAt c) (risen (gh o) (envAt c) (nx a) p)

begunY : ∀ {R Γ A B} → Ctx R Γ B → FlatOp → (A → Obs Timeline Γ B) → Bool → List A → St Γ A → List (St Γ B) → A → Pos → Events∞ B
begunY c op f d q o ls a p =
  lanesFrame op (lane f) d q (gh o) (reverse (reverse ls)) [] true (envAt c) (U.stateᴺ (U.subscribe (f a) (p ⊕ [ ix 1 ])) (envAt c))

postulate
  -- AN OUTER'S VALUE ADMITTED WHERE IT IS SHOWN PASSES EVERY LIVE SOURCE
  -- ABOVE: each source's skips pass its connect, whatever the admission
  -- left.
  outer-begins-links : ∀ {R Γ A B} {c : Ctx R Γ B} {op d n q ls} {f : A → Obs Timeline Γ B} {o : St Γ A} {a p}
                     → shows (inOuter op f d n q ls c) true ≡ true → Order ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩
                     → Links (_≡ p ⊕ [ ix 0 ]) c true (outerX c op f d q ls o a p) (begunY c op f d q o (keptLanes op ls) a p)
  outer-queues-links : ∀ {R Γ A B} {c : Ctx R Γ B} {op d n q ls} {f : A → Obs Timeline Γ B} {o : St Γ A} {a p}
                     → shows (inOuter op f d n q ls c) true ≡ true → Order ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩
                     → Links (_≡ p ⊕ [ ix 0 ]) c true (outerX c op f d q ls o a p) (U.stateᴺ (gh (flatS op f d n (q ++ [ a ]) o ls)) (envAt c))
  outer-ignores-links : ∀ {R Γ A B} {c : Ctx R Γ B} {op d n q ls} {f : A → Obs Timeline Γ B} {o : St Γ A} {a p}
                      → shows (inOuter op f d n q ls c) true ≡ true → Order ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩
                      → Links (_≡ p ⊕ [ ix 0 ]) c true (outerX c op f d q ls o a p) (U.stateᴺ (gh (flatS op f d n q o ls)) (envAt c))

-- An outer's value shown where it rises is ahead in every frame above
-- (`Clear`).
outer-ahead : ∀ {R Γ A B} {c : Ctx R Γ B} {op d n q ls} {f : A → Obs Timeline Γ B} {o : St Γ A} {a p}
            → shows (inOuter op f d n q ls c) true ≡ true → Order ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩
            → Aheadᶠ (_≡ p ⊕ [ ix 0 ]) c true
outer-ahead {d = true}  () od
outer-ahead {d = false} sh od = proj₁ (proj₂ (proj₂ (proj₂ (Order.lead od)))) sh

-- AN OUTER'S VALUE ADMITTED WHERE IT IS SHOWN IS SHOWN NEXT: every
-- frame above passes its skip, whatever the admission left.
outer-begins-pass : ∀ {R Γ A B} {c : Ctx R Γ B} {op d n q ls} {f : A → Obs Timeline Γ B} {o : St Γ A} {a p}
                  → shows (inOuter op f d n q ls c) true ≡ true → Order ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩
                  → Pass (_≡ p ⊕ [ ix 0 ]) c true (outerX c op f d q ls o a p) (begunY c op f d q o (keptLanes op ls) a p)
outer-begins-pass {c = c} {p = p} sh od = pass-of (_≡ p ⊕ [ ix 0 ]) c true (outer-ahead sh od) (outer-begins-links sh od)

outer-queues-pass : ∀ {R Γ A B} {c : Ctx R Γ B} {op d n q ls} {f : A → Obs Timeline Γ B} {o : St Γ A} {a p}
                  → shows (inOuter op f d n q ls c) true ≡ true → Order ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩
                  → Pass (_≡ p ⊕ [ ix 0 ]) c true (outerX c op f d q ls o a p) (U.stateᴺ (gh (flatS op f d n (q ++ [ a ]) o ls)) (envAt c))
outer-queues-pass {c = c} {p = p} sh od = pass-of (_≡ p ⊕ [ ix 0 ]) c true (outer-ahead sh od) (outer-queues-links sh od)

outer-ignores-pass : ∀ {R Γ A B} {c : Ctx R Γ B} {op d n q ls} {f : A → Obs Timeline Γ B} {o : St Γ A} {a p}
                   → shows (inOuter op f d n q ls c) true ≡ true → Order ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩
                   → Pass (_≡ p ⊕ [ ix 0 ]) c true (outerX c op f d q ls o a p) (U.stateᴺ (gh (flatS op f d n q o ls)) (envAt c))
outer-ignores-pass {c = c} {p = p} sh od = pass-of (_≡ p ⊕ [ ix 0 ]) c true (outer-ahead sh od) (outer-ignores-links sh od)

-- A full merge queues what arrives; a busy exhaust drops it.
queue-admits : ∀ {B} k (m : MonotonicList B) ls qs r → (length ls <ᵇ k) ≡ false → admit (flatOp (mergeᶠ (just k))) r m ls qs ≡ (ls , qs ++ [ m ] , idle)
queue-admits k m ls qs r e rewrite e = refl

ignore-admits : ∀ {B} (m : MonotonicList B) ls qs r → (length ls ≡ᵇ 0) ≡ false → admit (flatOp exhaustᶠ) r m ls qs ≡ (ls , qs , idle)
ignore-admits m (l ∷ ls) qs r e = refl

-- AN OUTER'S VALUE QUEUED, OR DROPPED BY A BUSY EXHAUST, IS ITS SKIP:
-- the outer is first among the parts (`Clear`), and its count is its
-- meaning's (`Frag`).
outer-queues : ∀ {R Γ A B} {c : Ctx R Γ B} {op d n q ls} {f : A → Obs Timeline Γ B} {o : St Γ A} {a p}
             → Queues op n → Order ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩
             → Dropsˢ (_≡ p ⊕ [ ix 0 ]) (outerX c op f d q ls o a p) (U.stateᴺ (gh (flatS op f d n (q ++ [ a ]) o ls)) (envAt c))
outer-queues {op = mergeᶠ (just k)} {true} b od = ⊥-elim (Order.lead od)
outer-queues {c = c} {mergeᶠ (just k)} {false} {n} {q} {ls} {f} {o} {a} {p} b od with Order.lead od
... | _ , al , tn , _ =
  outer-admits (mergeᶠ (just k)) (lane f) q (lanesL ls) (deadL ls) (envAt c) (gh o) a p _
    (trans (queue-admits k (laneᴹ (lane f) (envAt c) a) (U.states (lanesL ls) (envAt c)) (map (laneᴹ (lane f) (envAt c)) q) (p ⊕ [ ix 1 ])
              (subst (λ x → (x <ᵇ k) ≡ false) (trans en (sym (states-length (lanesL ls) (envAt c)))) b))
           (cong (λ x → U.states (lanesL ls) (envAt c) , x , idle) (sym (map-++ (laneᴹ (lane f) (envAt c)) q [ a ]))))
    refl refl (λ m → lanes-refl m _) (λ m → ∪-idleᵀ m _) al tn
  where en = proj₁ (proj₂ (proj₂ (frag-flat c (mergeᶠ (just k)) f false n q o ls (proj₁ (Order.shape od)))))
outer-queues {op = mergeᶠ nothing} ()
outer-queues {op = switchᶠ}        ()
outer-queues {op = exhaustᶠ}       ()

outer-ignores : ∀ {R Γ A B} {c : Ctx R Γ B} {op d n q ls} {f : A → Obs Timeline Γ B} {o : St Γ A} {a p}
              → Ignores op n → Order ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩
              → Dropsˢ (_≡ p ⊕ [ ix 0 ]) (outerX c op f d q ls o a p) (U.stateᴺ (gh (flatS op f d n q o ls)) (envAt c))
outer-ignores {op = exhaustᶠ} {true} b od = ⊥-elim (Order.lead od)
outer-ignores {c = c} {exhaustᶠ} {false} {n} {q} {ls} {f} {o} {a} {p} b od with Order.lead od
... | _ , al , tn , _ =
  outer-admits exhaustᶠ (lane f) q (lanesL ls) (deadL ls) (envAt c) (gh o) a p _
    (ignore-admits (laneᴹ (lane f) (envAt c) a) (U.states (lanesL ls) (envAt c)) (map (laneᴹ (lane f) (envAt c)) q) (p ⊕ [ ix 1 ])
       (subst (λ x → (x ≡ᵇ 0) ≡ false) (trans en (sym (states-length (lanesL ls) (envAt c)))) b))
    refl refl (λ m → lanes-refl m _) (λ m → ∪-idleᵀ m _) al tn
  where en = proj₁ (proj₂ (proj₂ (frag-flat c exhaustᶠ f false n q o ls (proj₁ (Order.shape od)))))
outer-ignores {op = mergeᶠ m} ()
outer-ignores {op = switchᶠ}  ()

-- A merge with room, or an idle exhaust, begins the lane it admits.
begin-admits : ∀ {B} k (m : MonotonicList B) ls qs r → (length ls <ᵇ k) ≡ true → admit (flatOp (mergeᶠ (just k))) r m ls qs ≡ (enter m r ∷ ls , qs , idle)
begin-admits k m ls qs r e rewrite e = refl

exhaust-admits : ∀ {B} (m : MonotonicList B) ls qs r → (length ls ≡ᵇ 0) ≡ true → admit (flatOp exhaustᶠ) r m ls qs ≡ (enter m r ∷ ls , qs , idle)
exhaust-admits m []       qs r e = refl
exhaust-admits m (l ∷ ls) qs r ()

-- A switch's kill leaves no lane live.
kill-lanes : ∀ {Γ B} (ls : List (St Γ B)) → Lanesᴴ ls → lanesL (proj₁ (killAll ls)) ≡ []
kill-lanes []                                _        = refl
kill-lanes (lnS true (cutS true a s) ∷ ls)   (_ , fl) with Machine.cut (cutS true a s) | killAll ls | kill-lanes ls fl
... | s′ , u | ls′ , t | e = cong (_++ []) e
kill-lanes (lnS false (cutS false a s) ∷ ls) (_ , fl) with killAll ls | kill-lanes ls fl
... | ls′ , t | e = cong (_++ []) e

postulate
  -- A SWITCH'S KILL POOLS WHAT IT KILLED: each lane it switches off
  -- leaves in the pool the tail the merge's `cuts` reads of it.
  kill-pool : ∀ {Γ B} (ls : List (St Γ B)) (ρ : U.NEnv Γ) → Lanesᴴ ls
            → ∀ n → Agreeᵀ n (poolT (deadL ls) ρ ∪ cuts (U.states (lanesL ls) ρ)) (poolT (deadL (proj₁ (killAll ls))) ρ)

-- An outer's value begun past its skip, as `admit` begins it.
begun-drops : ∀ {R Γ A B} (c : Ctx R Γ B) op q ls (f : A → Obs Timeline Γ B) (o : St Γ A) a p ls′ {Ls t′}
            → admit (flatOp op) (p ⊕ [ ix 1 ]) (laneᴹ (lane f) (envAt c) a) (U.states (lanesL ls) (envAt c)) (map (laneᴹ (lane f) (envAt c)) q)
                ≡ (Ls , map (laneᴹ (lane f) (envAt c)) q , t′)
            → (∀ n → Lanes n Ls (U.stateᴺ (U.subscribe (f a) (p ⊕ [ ix 1 ])) (envAt c) ∷ U.states (lanesL ls′) (envAt c)))
            → (∀ n → Agreeᵀ n (poolT (deadL ls) (envAt c) ∪ t′) (poolT (deadL ls′) (envAt c)))
            → All (λ l → After p (head (force l))) (U.states (lanesL ls) (envAt c)) → TailNotBefore p (poolT (deadL ls) (envAt c))
            → Dropsˢ (_≡ p ⊕ [ ix 0 ]) (outerX c op f false q ls o a p) (begunY c op f false q o ls′ a p)
begun-drops c op q ls f o a p ls′ ad la ta al tn =
  outer-admits op (lane f) q (lanesL ls) (deadL ls) (envAt c) (gh o) a p (begunY c op f false q o ls′ a p) ad refl refl
    (λ n → subst (Lanes n _) (begun-runs ls′ (envAt c) h) (la n)) (λ n → subst (Agreeᵀ n _) (begun-pool ls′ (envAt c) h) (ta n)) al tn
  where h = U.stateᴺ (U.subscribe (f a) (p ⊕ [ ix 1 ])) (envAt c)

-- AN OUTER'S VALUE BEGINS ITS LANE PAST ONE SKIP: the flatMap shows
-- the value as a skip, then the lane subscribed just past it.
outer-begins : ∀ {R Γ A B} {c : Ctx R Γ B} {op d n q ls} {f : A → Obs Timeline Γ B} {o : St Γ A} {a p}
             → Begins op n → Order ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩
             → Dropsˢ (_≡ p ⊕ [ ix 0 ]) (outerX c op f d q ls o a p) (begunY c op f d q o (keptLanes op ls) a p)
outer-begins {d = true} b od = ⊥-elim (Order.lead od)
outer-begins {c = c} {mergeᶠ nothing} {false} {n} {q} {ls} {f} {o} {a} {p} b od with Order.lead od
... | _ , al , tn , _ = begun-drops c (mergeᶠ nothing) q ls f o a p ls refl (λ m → lanes-refl m _) (λ m → ∪-idleᵀ m _) al tn
outer-begins {c = c} {mergeᶠ (just k)} {false} {n} {q} {ls} {f} {o} {a} {p} b od with Order.lead od
... | _ , al , tn , _ =
  begun-drops c (mergeᶠ (just k)) q ls f o a p ls
    (begin-admits k (laneᴹ (lane f) (envAt c) a) (U.states (lanesL ls) (envAt c)) (map (laneᴹ (lane f) (envAt c)) q) (p ⊕ [ ix 1 ])
       (subst (λ x → (x <ᵇ k) ≡ true) (trans en (sym (states-length (lanesL ls) (envAt c)))) b))
    (λ m → lanes-refl m _) (λ m → ∪-idleᵀ m _) al tn
  where en = proj₁ (proj₂ (proj₂ (frag-flat c (mergeᶠ (just k)) f false n q o ls (proj₁ (Order.shape od)))))
outer-begins {c = c} {exhaustᶠ} {false} {n} {q} {ls} {f} {o} {a} {p} b od with Order.lead od
... | _ , al , tn , _ =
  begun-drops c exhaustᶠ q ls f o a p ls
    (exhaust-admits (laneᴹ (lane f) (envAt c) a) (U.states (lanesL ls) (envAt c)) (map (laneᴹ (lane f) (envAt c)) q) (p ⊕ [ ix 1 ])
       (subst (λ x → (x ≡ᵇ 0) ≡ true) (trans en (sym (states-length (lanesL ls) (envAt c)))) b))
    (λ m → lanes-refl m _) (λ m → ∪-idleᵀ m _) al tn
  where en = proj₁ (proj₂ (proj₂ (frag-flat c exhaustᶠ f false n q o ls (proj₁ (Order.shape od)))))
outer-begins {c = c} {switchᶠ} {false} {n} {q} {ls} {f} {o} {a} {p} b od with Order.lead od
... | _ , al , tn , _ =
  begun-drops c switchᶠ q ls f o a p (proj₁ (killAll ls)) refl
    (λ m → subst (λ x → Lanes m (h ∷ []) (h ∷ U.states x (envAt c))) (sym (kill-lanes ls fl)) (lanes-refl m (h ∷ [])))
    (kill-pool ls (envAt c) fl) al tn
  where fl = proj₁ (proj₂ (frag-flat c switchᶠ f false n q o ls (proj₁ (Order.shape od))))
        h  = U.stateᴺ (U.subscribe (f a) (p ⊕ [ ix 1 ])) (envAt c)
