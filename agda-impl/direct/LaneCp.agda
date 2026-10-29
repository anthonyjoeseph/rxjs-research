{-# OPTIONS --guardedness #-}

-- A LANE'S END, SHOWN ONLY AS THE LAST WITH THE OUTER DONE: the lane
-- leaves its list, and the merge rises its own end exactly when the
-- outer is done and no other lane is in its list.  The rows agree but for
-- the lane's skip at the end's position, which every other part lies
-- strictly past; the merge's end there is owed exactly when every other
-- part owes nothing, which the counts read as the outer done and no
-- other lane live.
module adequacy.Direct.LaneCp where

open import Data.Bool using (Bool; true; false; T; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _ʳ++_)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; pred; _+_)
open import Data.Nat.Properties using (+-suc; m+n≡0⇒m≡0; m+n≡0⇒n≡0)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)

open import Tree using (Obs; mergeᶠ)
open import denotation.MonotonicList.Events using (Pos; Timeline)
open import denotation.EmissionSet using (end)
open import denotation.EmissionSet.Laws.Modulus using (≼-refl)
open import operation.PureObservable using (module Machine)
open Machine using (St; Ctx; ⟨_,_,_,_⟩; plug; absorbed; rising; cp; alive; ended; dequeue; settle; Att;
                    cutS; lnS; flatS; inLanes)
open import adequacy.Direct using (∅; up; here; rows; rowsL; pendRows; Plus; old; new; Lanes; Each; module Flat; _≃_; _⇄_;
  ≃-sym; Moves; silent)
open import adequacy.Direct.Up using (any-ʳ++ˡ; any-ʳ++ʳ; all-ʳ++; ≈ᴸ-refl; _∷_; flat-≃; up-≃; ≃-refl; ≃-trans; vis-≃; plus-≃)
open import adequacy.Direct.Bound using (Empty; Single; EndLast; Parts; Good; GoodL; G; GLn; shape; on; off; lane-v; live; dead-empty)
open import adequacy.Direct.Skip using (After; Since; LeadC; _≈⟨_⟩_; ≈-vis; up-≈)
open import adequacy.Direct.LaneEnd using (frame-≈; done-at; outer-owes; lanes-owe; since-x; since-y)
open import adequacy.Direct.Owes using (Owing; Owes; OwesL; UpO; Swap; owes-join; need-of; owesL-ʳ++; rowsL-ʳ++; ≡→≃; owing-≃; empty-≃;
                                        flat-owing-o; flat-owing-l; flat-empty; live-ʳ++; live-owing; goodL-ʳ++⁻; goodL-swap; lanes-≃; parts-≃; good-swap)
open import adequacy.Direct.Inv using (Inv; inv; Sim; good-split; node-good; upo-liv)

module Cp {R Γ A B} (f : A → Obs Timeline Γ B) (d : Bool) (n : ℕ) (o : St Γ A) (pre post : List (St Γ B)) (c : Ctx R Γ B)
          (a : Att) (s₀ : St Γ B) (p : Pos)
          (g : Good (plug c (flatS (mergeᶠ nothing) f d n [] o (pre ʳ++ lnS true (cutS true a s₀) ∷ post))))
          (go : Good o) (gl : GoodL (pre ʳ++ lnS true (cutS true a s₀) ∷ post)) (si : Single (rows o)) (el : EndLast (rows o)) (nl : n ≡ live (pre ʳ++ lnS true (cutS true a s₀) ∷ post))
          (ov : T d → Empty (rows o)) (pa : Parts (rows o) (rowsL (pre ʳ++ lnS true (cutS true a s₀) ∷ post))) (g₀ : Good s₀)
          (ho : ¬ T d → Owing (rows o)) (oo : Owes o) (op : OwesL pre) (oq : OwesL post) (uc : UpO c)
          (ao : After p (rows o)) (apre : Each (After p) (rowsL pre)) (apost : Each (After p) (rowsL post)) (lc : LeadC c p)
          (en : Empty (rows s₀)) where

  L    = λ x → pendRows (f x)
  O    = rows o
  Pre  = rowsL pre
  Post = rowsL post
  ln   = lnS true (cutS true a s₀)
  ed   = lnS false (cutS false a s₀)
  LX   = Pre ʳ++ (Plus (rows s₀) p end ∷ Post)
  LY   = Pre ʳ++ (∅ ∷ Post)
  Y    = Flat.FlatR L O LY

  node : ℕ → St Γ B
  node m = flatS (mergeᶠ nothing) f d m [] o (pre ʳ++ ed ∷ post)

  rowsY : ∀ {m} → rows (node m) ≃ Y
  rowsY = ≡→≃ (cong (Flat.FlatR L O) (rowsL-ʳ++ pre))

  sx′ = since-x L {p} {O} Pre Post {rows s₀} ao apre apost en
  sy′ = since-y L {p} {O} Pre Post {rows s₀} ao apre apost en
  fr  = frame-≈ L {p} {O} Pre Post {rows s₀} ao apre apost en
  da  = done-at L {p} {O} Pre Post {rows s₀} ao apre apost en

  cnt : pred n ≡ live pre + live post
  cnt = cong pred (trans nl (trans (live-ʳ++ pre) (+-suc (live pre) (live post))))

  ------------------------------------------------------------------------
  -- The tree after

  good′ : Good (plug c (node (pred n)))
  good′ = good-swap c sw g
    where
      lane≃ : rows ln ≃ rows ed
      lane≃ = (λ r → ⊥-elim (en r)) ⇄ λ ()
      gnode : ∀ v → G v (flatS (mergeᶠ nothing) f d n [] o (pre ʳ++ ln ∷ post)) → G v (node (pred n))
      gnode true  _                  = go , goodL-swap pre (λ _ → refl , shape s₀ g₀ , tt) gl , refl , si , el , trans cnt (sym (live-ʳ++ pre)) , ov , parts-≃ ≃-refl (lanes-≃ pre (lane≃ ∷ ≈ᴸ-refl Post)) pa
      gnode false (go′ , gl′ , qe , _) = go′ , goodL-swap pre (λ { (refl , g′ , _) → refl , g′ , tt }) gl′ , qe , tt
      sw : Swap (flatS (mergeᶠ nothing) f d n [] o (pre ʳ++ ln ∷ post)) (node (pred n))
      sw = record { same = flat-≃ L ≃-refl (lanes-≃ pre (lane≃ ∷ ≈ᴸ-refl Post)) ; live≡ = refl ; node = gnode ; lane = λ _ () ; body = λ _ _ () }

  owes′ : Owes (node (pred n))
  owes′ = ho , oo , owesL-ʳ++ pre op ((λ ()) , tt , oq)

  ------------------------------------------------------------------------
  -- The two outcomes

  pass : ¬ Flat.Done L O LX p → Owing Y
       → Inv ⟨ c , node (pred n) , absorbed , p ⟩ × Moves (up c (Flat.FlatR L O LX)) [] (up c (rows (node (pred n))))
  pass nd ow = inv good′ (owes-join c uc owes′ (need-of c (owing-≃ (≃-sym (rowsY {pred n})) ow)))
             , silent (≃-trans (≈-vis (up-≈ c lc (sx′) (sy′)
                                             (fr Y (λ d → ⊥-elim (nd d)) (λ r → r) inj₁)))
                               (vis-≃ (up-≃ c (≃-sym (rowsY {pred n})))))

  done : T d → pred n ≡ 0 → Inv ⟨ c , node (pred n) , rising cp , p ⟩ × Moves (up c (Flat.FlatR L O LX)) [] (up c (Plus (rows (node (pred n))) p end))
  done td pz = inv good′ (uc , lc , owes′ , tt , (λ r → ⊥-elim (empty-node r)) , empty-node)
             , silent (≃-trans (≈-vis (up-≈ c lc (sx′) since′
                                             (fr (Plus Y p end) (λ _ → new) old back)))
                               (vis-≃ (up-≃ c (plus-≃ (≃-sym (rowsY {pred n}))))))
    where
      eo = ov td
      z  = trans (sym cnt) pz
      gs = goodL-ʳ++⁻ pre gl
      ep = dead-empty pre (proj₁ gs) (m+n≡0⇒m≡0 (live pre) z)
      eq = dead-empty post (proj₂ (proj₂ gs)) (m+n≡0⇒n≡0 (live pre) z)
      D  = da eo ep eq
      empty-node : Empty (rows (node (pred n)))
      empty-node = empty-≃ (≃-sym (rowsY {pred n})) (flat-empty L eo (all-ʳ++ Pre ep ((λ {_} {_} ()) , eq)))
      back : ∀ {k e} → Plus Y p end k e → Y k e ⊎ (k ≡ p × e ≡ end × Flat.Done L O LX p)
      back (old r) = inj₁ r
      back new     = inj₂ (refl , refl , D)
      since′ : Since p (Plus Y p end)
      since′ (old r) = sy′ r
      since′ new     = ≼-refl {p}

  ------------------------------------------------------------------------
  -- Which, by the counts

  -- Some other lane still in its list owes.
  live-other : ∀ k → live pre + live post ≡ suc k → Owing (Lanes Pre) ⊎ Owing (Lanes Post)
  live-other k e with live pre in lp
  ... | suc m = inj₁ (live-owing pre op lp)
  ... | zero  = inj₂ (live-owing post oq e)

  owing-ly : Owing (Lanes Pre) ⊎ Owing (Lanes Post) → Owing (Lanes LY)
  owing-ly (inj₁ ow) em = ow λ {q} {e} x → em (any-ʳ++ˡ Pre x)
  owing-ly (inj₂ ow) em = ow λ {q} {e} x → em (any-ʳ++ʳ Pre (inj₂ x))

  Out : Machine.Mode B → Set₁
  Out m = Inv ⟨ c , node (pred n) , m , p ⟩ × Moves (up c (Flat.FlatR L O LX)) [] (up c (here (node (pred n)) m p))

  pick : ∀ b → d ≡ b → ∀ m → pred n ≡ m → Out (settle b m true)
  pick false db m em = pass (outer-owes L {p} {O} Pre Post {rows s₀} ao apre apost en ow) (flat-owing-o L {O} {LY} ow)
    where ow = ho λ t → subst T db t
  pick true db zero em = done (subst T (sym db) tt) em
  pick true db (suc k) em = pass (lanes-owe L {p} {O} Pre Post {rows s₀} ao apre apost en w) (flat-owing-l L {O} {LY} (owing-ly w))
    where w = live-other k (trans (sym cnt) em)

  result : Out (settle d (pred n) true)
  result = pick d refl (pred n) refl

-- A LANE'S END, SHOWN ONLY AS THE LAST WITH THE OUTER DONE.
rise-lane-cp : ∀ {R Γ A B} f d n q (o : St Γ A) pre post (c : Ctx R Γ B) s p
             → Sim ⟨ inLanes (mergeᶠ nothing) f d n q o pre post c , s , rising cp , p ⟩ []
                   (if alive s then dequeue c (mergeᶠ nothing) f d (pred n) q o (pre ʳ++ ended s ∷ post) p
                               else ⟨ c , flatS (mergeᶠ nothing) f d n q o (pre ʳ++ s ∷ post) , absorbed , p ⟩)
rise-lane-cp f d n q o pre post c s p (inv g (u , l , os , op′ , as , es)) with upo-liv (inLanes (mergeᶠ nothing) f d n q o pre post c) u
... | lv with lane-v s (subst (λ v → GLn v s) lv (proj₂ (good-split (inLanes (mergeᶠ nothing) f d n q o pre post c) s g)))
... | off a s₀ = ⊥-elim op′
... | on a s₀ g₀ _ with subst (λ v → G v (flatS (mergeᶠ nothing) f d n q o (pre ʳ++ lnS true (cutS true a s₀) ∷ post))) lv
                            (node-good c (flatS (mergeᶠ nothing) f d n q o (pre ʳ++ lnS true (cutS true a s₀) ∷ post)) g (λ ()))
... | go , gl , refl , si , el , nl , ov , pa with u | l
... | ho , oo , op , oq , uc | ao , apre , apost , lc =
  Cp.result f d n o pre post c a s₀ p g go gl si el nl ov pa g₀ ho oo op oq uc ao apre apost lc es
