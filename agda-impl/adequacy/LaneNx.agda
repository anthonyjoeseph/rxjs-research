{-# OPTIONS --guardedness #-}

-- A LANE'S VALUE PASSES, UNLESS THE LANE IS OVER: a begun lane rising a
-- value, the joiner rises it at the same position.  The rows agree, the
-- joiner's value its lane's, and every other part lies strictly past it.
-- A lane out of its list is not open, so rises nothing.  One step for
-- every joiner, read by its policy.
module adequacy.LaneNx where

open import Data.Bool using (Bool; true; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.List.Relation.Unary.All using ([])
open import Data.List using (List; []; _∷_; _ʳ++_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (cong; subst)

open import Tree using (Obs; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Events using (Pos; Timeline)
open import denotation.EmissionSet using (out; DenEnv; Truncate)
open import denotation.Laws.Modulus using (≺→≼)
open import operation.PureObservable using (module Machine)
open Machine using (St; Ctx; ⟨_,_,_,_⟩; plug; absorbed; rising; nx; alive; Att; cutS; lnS; flatS; inLanes)
open import adequacy.Rows using (env; up; rows; rowsL; pendRows; Plus; Each; _≃_; ≃-sym; Moves; silent)
open import adequacy.Up using (up-≃; ≃-trans; vis-≃; plus-≃; trunc-≃)
open import adequacy.Bound using (Good; GLn; on; off; lane-v)
open import adequacy.Skip using (After; Since; LeadC)
open import adequacy.Policy using (JoinP; polOf)
open import adequacy.JoinEnd using (module Val)
open import adequacy.LaneVal using (val-at)
open import adequacy.LaneCp using (rows-flat; trunc-plus)
open import adequacy.Swap using (rowsL-ʳ++; ≡→≃)
open import adequacy.Inv using (Inv; inv; Sim; UpO; good-split; upo-liv)

module Nx {R Γ A B} (op : FlatOp) (f : A → Obs Timeline Γ B) (d : Bool) (n : ℕ) (q : List A) (o : St Γ A) (pre post : List (St Γ B)) (c : Ctx R Γ B)
          (a : Att) (s₀ : St Γ B) (b : B) (p : Pos)
          (g : Good [] (plug c (flatS op f d n q o (pre ʳ++ lnS true (cutS true a s₀) ∷ post))))
          (uc : UpO c) (ao : After p (rows (env c) o)) (apre : Each (After p) (rowsL (env c) pre)) (apost : Each (After p) (rowsL (env c) post))
          (lc : LeadC c p) (as : After p (rows (env c) s₀)) where

  ρ : DenEnv Γ
  ρ = env c

  L    = λ x → pendRows ρ (f x)
  O    = rows ρ o
  Pre  = rowsL ρ pre
  Post = rowsL ρ post
  s    = lnS true (cutS true a s₀)
  PX   = polOf op L O d n q (Pre ʳ++ (Plus (rows ρ s₀) p (out b) ∷ Post))
  PY   = polOf op L O d n q (Pre ʳ++ (rows ρ s₀ ∷ Post))
  node = flatS op f d n q o (pre ʳ++ s ∷ post)

  open Val (val-at L {p} {O} {d} {n} q Pre Post {rows ρ s₀} b ao apre apost as op)

  rowsY : rows ρ node ≃ Truncate (JoinP PY)
  rowsY = ≃-trans (≡→≃ (rows-flat ρ op f d n q o (pre ʳ++ s ∷ post)))
                  (trunc-≃ (≡→≃ (cong (λ Ls → JoinP (polOf op L O d n q Ls)) (rowsL-ʳ++ pre))))

  since-y : Since p (JoinP PY)
  since-y {k} r = ≺→≼ {p} {k} (after-y r)

  result : Inv ⟨ c , node , rising (nx b) , p ⟩ × Moves (up c (Truncate (JoinP PX))) [] (up c (Plus (rows ρ node) p (out b)))
  result = inv g (uc , lc , tt , (λ r → after-y (proj₁ (_≃_.to rowsY r))) , tt)
         , silent (vis-≃ (up-≃ c (≃-trans (trunc-≃ val-≃) (≃-trans (trunc-plus since-y) (plus-≃ (≃-sym rowsY))))))

-- A LANE'S VALUE PASSES, UNLESS THE LANE IS OVER.
rise-lane-nx : ∀ {R Γ A B} f d n q (o : St Γ A) pre post (c : Ctx R Γ B) s b p
             → Sim ⟨ inLanes (mergeᶠ nothing) f d n q o pre post c , s , rising (nx b) , p ⟩ []
                   (if alive s then ⟨ c , flatS (mergeᶠ nothing) f d n q o (pre ʳ++ s ∷ post) , rising (nx b) , p ⟩
                               else ⟨ c , flatS (mergeᶠ nothing) f d n q o (pre ʳ++ s ∷ post) , absorbed , p ⟩)
rise-lane-nx f d n q o pre post c s b p (inv g (u , l , op′ , as , _)) with upo-liv (inLanes (mergeᶠ nothing) f d n q o pre post c) u
... | lv with lane-v s (subst (λ v → GLn (env c) v s) lv (good-split (inLanes (mergeᶠ nothing) f d n q o pre post c) s g))
... | off a s₀ = ⊥-elim op′
... | on a s₀ _ _ with l
... | ao , apre , apost , lc = Nx.result (mergeᶠ nothing) f d n q o pre post c a s₀ b p g u ao apre apost lc as

-- A BOUNDED MERGE'S LANE VALUE.
rise-bounded-lane-nx : ∀ {R Γ A B} m f d n q (o : St Γ A) pre post (c : Ctx R Γ B) s b p
                     → Sim ⟨ inLanes (mergeᶠ (just m)) f d n q o pre post c , s , rising (nx b) , p ⟩ []
                           (if alive s then ⟨ c , flatS (mergeᶠ (just m)) f d n q o (pre ʳ++ s ∷ post) , rising (nx b) , p ⟩
                                       else ⟨ c , flatS (mergeᶠ (just m)) f d n q o (pre ʳ++ s ∷ post) , absorbed , p ⟩)
rise-bounded-lane-nx m f d n q o pre post c s b p (inv g (u , l , op′ , as , _)) with upo-liv (inLanes (mergeᶠ (just m)) f d n q o pre post c) u
... | lv with lane-v s (subst (λ v → GLn (env c) v s) lv (good-split (inLanes (mergeᶠ (just m)) f d n q o pre post c) s g))
... | off a s₀ = ⊥-elim op′
... | on a s₀ _ _ with l
... | ao , apre , apost , lc = Nx.result (mergeᶠ (just m)) f d n q o pre post c a s₀ b p g u ao apre apost lc as

-- A SWITCH'S LANE VALUE.
rise-switch-lane-nx : ∀ {R Γ A B} f d n q (o : St Γ A) pre post (c : Ctx R Γ B) s b p
                    → Sim ⟨ inLanes switchᶠ f d n q o pre post c , s , rising (nx b) , p ⟩ []
                          (if alive s then ⟨ c , flatS switchᶠ f d n q o (pre ʳ++ s ∷ post) , rising (nx b) , p ⟩
                                      else ⟨ c , flatS switchᶠ f d n q o (pre ʳ++ s ∷ post) , absorbed , p ⟩)
rise-switch-lane-nx f d n q o pre post c s b p (inv g (u , l , op′ , as , _)) with upo-liv (inLanes switchᶠ f d n q o pre post c) u
... | lv with lane-v s (subst (λ v → GLn (env c) v s) lv (good-split (inLanes switchᶠ f d n q o pre post c) s g))
... | off a s₀ = ⊥-elim op′
... | on a s₀ _ _ with l
... | ao , apre , apost , lc = Nx.result switchᶠ f d n q o pre post c a s₀ b p g u ao apre apost lc as

-- AN EXHAUST'S LANE VALUE.
rise-exhaust-lane-nx : ∀ {R Γ A B} f d n q (o : St Γ A) pre post (c : Ctx R Γ B) s b p
                     → Sim ⟨ inLanes exhaustᶠ f d n q o pre post c , s , rising (nx b) , p ⟩ []
                           (if alive s then ⟨ c , flatS exhaustᶠ f d n q o (pre ʳ++ s ∷ post) , rising (nx b) , p ⟩
                                       else ⟨ c , flatS exhaustᶠ f d n q o (pre ʳ++ s ∷ post) , absorbed , p ⟩)
rise-exhaust-lane-nx f d n q o pre post c s b p (inv g (u , l , op′ , as , _)) with upo-liv (inLanes exhaustᶠ f d n q o pre post c) u
... | lv with lane-v s (subst (λ v → GLn (env c) v s) lv (good-split (inLanes exhaustᶠ f d n q o pre post c) s g))
... | off a s₀ = ⊥-elim op′
... | on a s₀ _ _ with l
... | ao , apre , apost , lc = Nx.result exhaustᶠ f d n q o pre post c a s₀ b p g u ao apre apost lc as
