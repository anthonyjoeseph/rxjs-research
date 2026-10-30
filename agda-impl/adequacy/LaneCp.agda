{-# OPTIONS --guardedness #-}

-- A LANE'S END, SHOWN ONLY AS THE LAST WITH THE OUTER DONE: the lane
-- leaves its list, and the merge rises its own end exactly when the
-- outer is done and no other lane is in its list.  The rows agree but for
-- the lane's skip at the end's position, which every other part lies
-- strictly past; the merge's end there is owed exactly when the outer is
-- done and the lane was the last live one.
module adequacy.LaneCp where

open import Data.Bool using (Bool; true; false; T; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.List.Relation.Unary.All using ([])
open import Data.List using (List; []; _∷_; _ʳ++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (there) renaming (here to hd)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; pred; _+_)
open import Data.Nat.Properties using (+-suc; m+n≡0⇒m≡0; m+n≡0⇒n≡0)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (tt to tt₁)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)

open import Data.List.Relation.Unary.All using () renaming (_∷_ to _∷ᴬ_)
open import Tree using (Obs; mergeᶠ)
open import denotation.Events using (Pos; Timeline)
open import denotation.EmissionSet using (EmissionSet; Ev; end; DenEnv; Truncate)
open import denotation.Laws.Modulus using (≼-refl; ≺-irrefl)
open import operation.PureObservable using (module Machine)
open Machine using (St; Ctx; CS; ⟨_,_,_,_⟩; plug; absorbed; rising; cp; alive; ended; dequeue; settle; Att;
                    cutS; lnS; flatS; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody)
open import adequacy.Rows using (env; ∅; up; here; rows; rowsL; pendRows; Plus; old; new; Each; module Flat; _≃_; _⇄_; ≃-sym;
  Moves; silent)
open import adequacy.Up using (all-ʳ++; _∷_; up-≃; ≃-trans; vis-≃; plus-≃; trunc-≃)
open import adequacy.Bound using (Empty; Good; G; GLn; on; off; lane-v; live; dead-empty; MergeG)
open import adequacy.Skip using (After; Since; LeadC; _≈⟨_⟩_; up-vis; ≈-refl; since-map; map-≈; since-scan; scan-≈; since-take; take-≈; since-row; flat-≈; after-since;
                                 since-bounded; since-switch; since-exhaust; bounded-≈; switch-≈; exhaust-≈;
                                 ≈ᴸ-hole; conn-≈; since-conn) renaming (≈ᴸ-refl to ≈ᴸ-refl⟨⟩; _∷_ to _∷≈_)
open import adequacy.LaneEnd using (frame-≈; done-at; outer-owes; lanes-owe; since-x; since-y)
open import adequacy.Swap using (rowsL-ʳ++; ≡→≃; empty-≃; flat-empty; live-ʳ++; goodL-ʳ++⁻)
open import adequacy.Inv using (Inv; inv; Sim; UpO; good-split; node-good; upo-liv)
open import adequacy.Skip using (trunc-≈)

postulate
  -- A LANE'S END TAKEN, THE TREE STILL GOOD: a rowless lane over a
  -- completed cut leaves its list and its merge's count, and every node
  -- above stays good reading the merge's rows, which may now end where
  -- the lane did.  The merge's own node is direct; open is each frame
  -- above, whose facts read those rows.
  -- RECOVERY: git show 785ca3ec:agda-impl/adequacy/LaneCp.agda restores the merge node's `G` across the swap, in `Cp.good′`.
  good-lane-end : ∀ {R Γ A B} (f : A → Obs Timeline Γ B) d n (o : St Γ A) pre post (c : Ctx R Γ B) a (s₀ : St Γ B)
                → Empty (rows (env c) s₀)
                → Good [] (plug c (flatS (mergeᶠ nothing) f d n [] o (pre ʳ++ lnS true (cutS true a s₀) ∷ post)))
                → Good [] (plug c (flatS (mergeᶠ nothing) f d (pred n) [] o (pre ʳ++ lnS false (cutS false a s₀) ∷ post)))

-- An end added past every row adds nothing before any of them.
trunc-plus : ∀ {A} {t : EmissionSet A} {p} {v : Ev A} → Since p t → Truncate (Plus t p v) ≃ Plus (Truncate t) p v
trunc-plus {t = t} {p} {v} sp = to′ ⇄ from′
  where
    to′ : ∀ {k e} → Truncate (Plus t p v) k e → Plus (Truncate t) p v k e
    to′ (old r , ks , f) = old (r , ks , λ y lt d → f (old y) lt d)
    to′ (new   , _)      = new
    from′ : ∀ {k e} → Plus (Truncate t) p v k e → Truncate (Plus t p v) k e
    from′ (old (r , ks , f)) = old r , p ∷ ks , go
      where go : ∀ {k′ e′} → Plus t p v k′ e′ → _ → _ → k′ ∈ (p ∷ ks)
            go (old y) lt d = there (f y lt d)
            go new     _  _ = hd refl
    from′ new = new , [] , λ { (old y) lt _ → ⊥-elim (sp y lt) ; new lt _ → ⊥-elim (≺-irrefl {p} lt) }

module Cp {R Γ A B} (f : A → Obs Timeline Γ B) (d : Bool) (n : ℕ) (o : St Γ A) (pre post : List (St Γ B)) (c : Ctx R Γ B)
          (a : Att) (s₀ : St Γ B) (p : Pos)
          (g : Good [] (plug c (flatS (mergeᶠ nothing) f d n [] o (pre ʳ++ lnS true (cutS true a s₀) ∷ post))))
          (mg : G (env c) true (flatS (mergeᶠ nothing) f d n [] o (pre ʳ++ lnS true (cutS true a s₀) ∷ post))) (g₀ : Good (env c) s₀)
          (uc : UpO c) (ao : After p (rows (env c) o)) (apre : Each (After p) (rowsL (env c) pre)) (apost : Each (After p) (rowsL (env c) post))
          (lc : LeadC c p) (en : Empty (rows (env c) s₀)) where

  open MergeG mg

  ρ : DenEnv Γ
  ρ = env c

  L    = λ x → pendRows ρ (f x)
  O    = rows ρ o
  Pre  = rowsL ρ pre
  Post = rowsL ρ post
  ln   = lnS true (cutS true a s₀)
  ed   = lnS false (cutS false a s₀)
  LX   = Pre ʳ++ (Plus (rows ρ s₀) p end ∷ Post)
  LY   = Pre ʳ++ (∅ ∷ Post)
  Y    = Flat.JoinT L O d (pred n) LY

  node : ℕ → St Γ B
  node m = flatS (mergeᶠ nothing) f d m [] o (pre ʳ++ ed ∷ post)

  joinY : Flat.JoinT L O d (pred n) (rowsL ρ (pre ʳ++ ed ∷ post)) ≃ Y
  joinY = ≡→≃ (cong (Flat.JoinT L O d (pred n)) (rowsL-ʳ++ pre))

  rowsY : rows ρ (node (pred n)) ≃ Truncate Y
  rowsY = trunc-≃ joinY

  sx′ = since-x L {p} {O} {d} {n} Pre Post {rows ρ s₀} ao apre apost en
  sy′ = since-y L {p} {O} {d} {n} Pre Post {rows ρ s₀} ao apre apost en
  fr  = frame-≈ L {p} {O} {d} {n} Pre Post {rows ρ s₀} ao apre apost en
  da  = done-at L {p} {O} {d} {n} Pre Post {rows ρ s₀} ao apre apost en

  cnt : pred n ≡ live pre + live post
  cnt = cong pred (trans count (trans (live-ʳ++ pre) (+-suc (live pre) (live post))))

  ------------------------------------------------------------------------
  -- The tree after

  good′ : Good [] (plug c (node (pred n)))
  good′ = good-lane-end f d n o pre post c a s₀ en g

  ------------------------------------------------------------------------
  -- The two outcomes

  pass : ¬ Flat.Done L O d n LX p
       → Inv ⟨ c , node (pred n) , absorbed , p ⟩ × Moves (up c (Flat.RowT L O d n LX)) [] (up c (rows ρ (node (pred n))))
  pass nd = inv good′ tt
          , silent (≃-trans (up-vis c lc (λ (r , _) → sx′ r) (λ (r , _) → sy′ r) skip)
                            (vis-≃ (up-≃ c (≃-sym rowsY))))
    where skip = trunc-≈ (fr Y (λ d → ⊥-elim (nd d)) (λ r → r) inj₁)

  done : T d → pred n ≡ 0 → Inv ⟨ c , node (pred n) , rising cp , p ⟩ × Moves (up c (Flat.RowT L O d n LX)) [] (up c (Plus (rows ρ (node (pred n))) p end))
  done td pz = inv good′ (uc , lc , tt , (λ r → ⊥-elim (empty-node r)) , empty-node)
             , silent (≃-trans (up-vis c lc (λ (r , _) → sx′ r) (λ (r , _) → since′ r) skip)
                               (vis-≃ (up-≃ c to-node)))
    where
      eo = spent td
      z  = trans (sym cnt) pz
      gs = goodL-ʳ++⁻ pre lanesG
      ep = dead-empty pre (proj₁ gs) (m+n≡0⇒m≡0 (live pre) z)
      eq = dead-empty post (proj₂ (proj₂ gs)) (m+n≡0⇒n≡0 (live pre) z)
      D  = da td pz
      empty-node : Empty (rows ρ (node (pred n)))
      empty-node (r , _) = empty-≃ (≃-sym joinY) (flat-empty L eo (all-ʳ++ Pre ep ((λ {_} {_} ()) , eq))) r
      back : ∀ {k e} → Plus Y p end k e → Y k e ⊎ (k ≡ p × e ≡ end × Flat.Done L O d n LX p)
      back (old r) = inj₁ r
      back new     = inj₂ (refl , refl , D)
      since′ : Since p (Plus Y p end)
      since′ (old r) = sy′ r
      since′ new     = ≼-refl {p}
      skip   = trunc-≈ (fr (Plus Y p end) (λ _ → new) old back)
      to-node = ≃-trans (trunc-plus sy′) (plus-≃ (≃-sym rowsY))

  ------------------------------------------------------------------------
  -- Which, by the counts

  Out : Machine.Mode B → Set₁
  Out m = Inv ⟨ c , node (pred n) , m , p ⟩ × Moves (up c (Flat.RowT L O d n LX)) [] (up c (here ρ (node (pred n)) m p))

  pick : ∀ b → d ≡ b → ∀ m → pred n ≡ m → Out (settle b m true)
  pick false db m em = pass (outer-owes L {p} {O} {d} {n} Pre Post {rows ρ s₀} ao apre apost en λ t → subst T db t)
  pick true db zero em = done (subst T (sym db) tt) em
  pick true db (suc k) em = pass (lanes-owe L {p} {O} {d} {n} Pre Post {rows ρ s₀} ao apre apost en em)

  result : Out (settle d (pred n) true)
  result = pick d refl (pred n) refl

-- A LANE'S END, SHOWN ONLY AS THE LAST WITH THE OUTER DONE.
rise-lane-cp : ∀ {R Γ A B} f d n q (o : St Γ A) pre post (c : Ctx R Γ B) s p
             → Sim ⟨ inLanes (mergeᶠ nothing) f d n q o pre post c , s , rising cp , p ⟩ []
                   (if alive s then dequeue c (mergeᶠ nothing) f d (pred n) q o (pre ʳ++ ended s ∷ post) p
                               else ⟨ c , flatS (mergeᶠ nothing) f d n q o (pre ʳ++ s ∷ post) , absorbed , p ⟩)
rise-lane-cp f d n q o pre post c s p (inv g (u , l , op′ , as , es)) with upo-liv (inLanes (mergeᶠ nothing) f d n q o pre post c) u
... | lv with lane-v s (subst (λ v → GLn (env c) v s) lv (good-split (inLanes (mergeᶠ nothing) f d n q o pre post c) s g))
... | off a s₀ = ⊥-elim op′
... | on a s₀ g₀ _ with subst (λ v → G (env c) v (flatS (mergeᶠ nothing) f d n q o (pre ʳ++ lnS true (cutS true a s₀) ∷ post))) lv
                            (node-good c (flatS (mergeᶠ nothing) f d n q o (pre ʳ++ lnS true (cutS true a s₀) ∷ post)) g (λ ()) (λ ()))
... | mg with MergeG.fresh mg | l
... | refl | ao , apre , apost , lc =
  Cp.result f d n o pre post c a s₀ p g mg g₀ u ao apre apost lc es
