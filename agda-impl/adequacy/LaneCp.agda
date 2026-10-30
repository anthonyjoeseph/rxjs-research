{-# OPTIONS --guardedness #-}

-- A LANE'S END, SHOWN ONLY AS THE LAST WITH THE OUTER DONE: the lane
-- leaves its list, and the merge rises its own end exactly when the
-- outer is done and no other lane is in its list.  The rows agree but for
-- the lane's skip at the end's position, which every other part lies
-- strictly past; the merge's end there is owed exactly when every other
-- part owes nothing, which the counts read as the outer done and no
-- other lane live.
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
open import Data.Maybe using (just)
open import Tree using (Obs; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Events using (Pos; Timeline)
open import denotation.EmissionSet using (EmissionSet; Ev; end; DenEnv; Truncate)
open import denotation.Laws.Modulus using (≼-refl; ≺-irrefl)
open import operation.PureObservable using (module Machine)
open Machine using (St; Ctx; CS; ⟨_,_,_,_⟩; plug; absorbed; rising; cp; alive; ended; dequeue; settle; Att;
                    cutS; lnS; flatS; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody)
open import adequacy.Rows using (env; ∅; Hot; up; here; rows; rowsL; pendRows; Plus; old; new; Lanes; Each; module Flat; _≃_; _⇄_;
  ≃-sym; Moves; silent)
open import adequacy.Up using (any-ʳ++ˡ; any-ʳ++ʳ; all-ʳ++; ≈ᴸ-refl; _∷_; up-≃; ≃-refl; ≃-trans; vis-≃; plus-≃; trunc-≃;
  row-≃)
open import adequacy.Bound using (Empty; Good; G; GLn; shape; on; off; lane-v; live; dead-empty; MergeG; mergeG-map)
open import adequacy.Skip using (After; Since; LeadC; _≈⟨_⟩_; up-vis; ≈-refl; since-map; map-≈; since-scan; scan-≈; since-row; flat-≈; after-since;
                                 ≈ᴸ-hole; conn-≈; since-conn) renaming (≈ᴸ-refl to ≈ᴸ-refl⟨⟩; _∷_ to _∷≈_)
open import adequacy.LaneEnd using (frame-≈; done-at; outer-owes; lanes-owe; since-x; since-y)
open import adequacy.Owes using (Owing; Owes; OwesL; UpO; Swap; owes-join; SrcO; srcO-≃; owesL-ʳ++; rowsL-ʳ++; ≡→≃; owing-≃; empty-≃;
                                        flat-owing-o; flat-owing-l; flat-empty; live-ʳ++; live-owing; goodL-ʳ++⁻; goodL-swap; lanes-≃; rooted-≃; good-swap)
open import adequacy.Inv using (Inv; inv; Sim; good-split; node-good; upo-liv; need-of; owing-row)
open import adequacy.Skip using (trunc-≈)
open import denotation.Laws.Modulus using (≺→≼)

postulate
  -- WHAT A SOURCE OWES IS UNMOVED BY A SKIP PAST ITS LEAD: its body,
  -- reading the source a skip apart, owes alike, and the connect above,
  -- shown a skip or a pin under it, owes alike, every other part being
  -- past `p`.
  src-owes-≈ : ∀ {R Γ X B} (k : CS) (b : St (X ∷ Γ) B) (c : Ctx R Γ B) {t u : EmissionSet X} {p}
             → After p (rows (Hot ∅ k ∷ᴬ env c) b) → LeadC c p → Since p t → Since p u → t ≈⟨ p ⟩ u
             → SrcO (inSrc k b c) t → SrcO (inSrc k b c) u

-- What is owed up a context, unmoved by a skip past its lead: `up-vis`
-- for owing.
srcO-≈ : ∀ {R Γ A} (c : Ctx R Γ A) {t u : EmissionSet A} {p} → LeadC c p → Since p t → Since p u → t ≈⟨ p ⟩ u → SrcO c t → SrcO c u
srcO-≈ top                                   ld st su eq so = tt
srcO-≈ (inMap f c)                             ld st su eq so = srcO-≈ c ld (since-map f st) (since-map f su) (map-≈ f eq) so
srcO-≈ (inScan f z c)                          ld st su eq so = srcO-≈ c ld (since-scan f z st) (since-scan f z su) (scan-≈ f z eq) so
srcO-≈ (inCut true a c)                        ld st su eq so = srcO-≈ c ld st su eq so
srcO-≈ (inCut false a c)                       ld st su eq so = tt
srcO-≈ (inLn true c)                           ld st su eq so = srcO-≈ c ld st su eq so
srcO-≈ (inLn false c)                          ld st su eq so = tt
srcO-≈ (inTake i q w c)                        ld st su eq so = tt
srcO-≈ (inOuter (mergeᶠ nothing) f d n q ls c) {t} {u} (al , ld) st su eq so =
  srcO-≈ c ld (since-row L t Ls st sl) (since-row L u Ls su sl) (trunc-≈ (flat-≈ L Ls Ls eq (≈ᴸ-refl⟨⟩ Ls) st su sl sl)) so
  where
    L  = λ a → pendRows (env c) (f a)
    Ls = rowsL (env c) ls
    sl = after-since Ls al
srcO-≈ (inOuter (mergeᶠ (just _)) f d n q ls c) ld st su eq so = tt
srcO-≈ (inOuter switchᶠ f d n q ls c)           ld st su eq so = tt
srcO-≈ (inOuter exhaustᶠ f d n q ls c)          ld st su eq so = tt
srcO-≈ (inLanes (mergeᶠ nothing) f d n q o pre post c) {t} {u} (ao , apre , apost , ld) st su eq so =
  srcO-≈ c ld (since-row L O Lt sO slt) (since-row L O Lu sO slu)
       (trunc-≈ (flat-≈ L Lt Lu ≈-refl (≈ᴸ-hole (rowsL ρ pre) (eq ∷≈ ≈ᴸ-refl⟨⟩ (rowsL ρ post))) sO sO slt slu)) so
  where
    ρ   = env c
    L   = λ a → pendRows ρ (f a)
    O   = rows ρ o
    Lt  = rowsL ρ pre ʳ++ (t ∷ rowsL ρ post)
    Lu  = rowsL ρ pre ʳ++ (u ∷ rowsL ρ post)
    sO  = λ {q} {e} r → ≺→≼ {_} {q} (ao {q} {e} r)
    slt = all-ʳ++ (rowsL ρ pre) (after-since (rowsL ρ pre) apre) (st , after-since (rowsL ρ post) apost)
    slu = all-ʳ++ (rowsL ρ pre) (after-since (rowsL ρ pre) apre) (su , after-since (rowsL ρ post) apost)
srcO-≈ (inLanes (mergeᶠ (just _)) f d n q o pre post c) ld st su eq so = tt
srcO-≈ (inLanes switchᶠ f d n q o pre post c)   ld st su eq so = tt
srcO-≈ (inLanes exhaustᶠ f d n q o pre post c)  ld st su eq so = tt
srcO-≈ (inSrc k b c)                            (ab , ld) st su eq so = src-owes-≈ k b c ab ld st su eq so
srcO-≈ (inBody k o c) {t} {u}                   (ao , ld) st su eq so =
  srcO-≈ c ld (since-conn (CS.connAt k) _ t ao st) (since-conn (CS.connAt k) _ u ao su) (conn-≈ (CS.connAt k) _ eq) so

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
          (ho : ¬ T d → Owing (rows (env c) o)) (oo : Owes (env c) o) (op : OwesL (env c) pre) (oq : OwesL (env c) post) (uc : UpO c)
          (ao : After p (rows (env c) o)) (apre : Each (After p) (rowsL (env c) pre)) (apost : Each (After p) (rowsL (env c) post)) (lc : LeadC c p)
          (en : Empty (rows (env c) s₀)) (so : SrcO (inLanes (mergeᶠ nothing) f d n [] o pre post c) (Plus (rows (env c) s₀) p end)) where

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
  Y    = Flat.JoinT L O d LY

  node : ℕ → St Γ B
  node m = flatS (mergeᶠ nothing) f d m [] o (pre ʳ++ ed ∷ post)

  joinY : Flat.JoinT L O d (rowsL ρ (pre ʳ++ ed ∷ post)) ≃ Y
  joinY = ≡→≃ (cong (Flat.JoinT L O d) (rowsL-ʳ++ pre))

  rowsY : ∀ {m} → rows ρ (node m) ≃ Truncate Y
  rowsY = trunc-≃ joinY

  sx′ = since-x L {p} {O} {d} Pre Post {rows ρ s₀} ao apre apost en
  sy′ = since-y L {p} {O} {d} Pre Post {rows ρ s₀} ao apre apost en
  fr  = frame-≈ L {p} {O} {d} Pre Post {rows ρ s₀} ao apre apost en
  da  = done-at L {p} {O} {d} Pre Post {rows ρ s₀} ao apre apost en

  cnt : pred n ≡ live pre + live post
  cnt = cong pred (trans count (trans (live-ʳ++ pre) (+-suc (live pre) (live post))))

  ------------------------------------------------------------------------
  -- The tree after

  good′ : Good [] (plug c (node (pred n)))
  good′ = good-swap c sw g
    where
      lane≃ : rows ρ ln ≃ rows ρ ed
      lane≃ = (λ r → ⊥-elim (en r)) ⇄ λ ()
      gnode : ∀ v → G ρ v (flatS (mergeᶠ nothing) f d n [] o (pre ʳ++ ln ∷ post)) → G ρ v (node (pred n))
      gnode true  _  = record { outer = outer ; lanesG = goodL-swap pre (λ _ → refl , shape s₀ g₀ , tt) lanesG ; fresh = refl
                              ; count = trans cnt (sym (live-ʳ++ pre)) ; spent = spent ; rooted = rooted-≃ ≃-refl (lanes-≃ pre (lane≃ ∷ ≈ᴸ-refl Post)) rooted }
      gnode false m′ = mergeG-map (λ x → x) (goodL-swap pre (λ { (refl , g′ , _) → refl , g′ , tt })) (λ x → x) (λ x → x) (λ x → x) m′
      sw : Swap ρ (flatS (mergeᶠ nothing) f d n [] o (pre ʳ++ ln ∷ post)) (node (pred n))
      sw = record { same = row-≃ L ≃-refl (lanes-≃ pre (lane≃ ∷ ≈ᴸ-refl Post)) ; live≡ = refl ; node = gnode ; lane = λ _ () ; body = λ _ _ () ; held = λ () }

  owes′ : Owes ρ (node (pred n))
  owes′ = ho , oo , owesL-ʳ++ pre op ((λ ()) , tt , oq)

  ------------------------------------------------------------------------
  -- The two outcomes

  pass : ¬ Flat.Done L O d LX p → Owing Y
       → Inv ⟨ c , node (pred n) , absorbed , p ⟩ × Moves (up c (Flat.RowT L O d LX)) [] (up c (rows ρ (node (pred n))))
  pass nd ow = inv good′ (owes-join c uc owes′ (need-of c uc good′ (owing-row f d (pred n) [] o (pre ʳ++ ed ∷ post) (node-good c _ good′ (λ ()) (λ ())) (owing-≃ (≃-sym joinY) ow))
                                                  (srcO-≃ c (≃-sym (rowsY {pred n})) (srcO-≈ c lc (λ (r , _) → sx′ r) (λ (r , _) → sy′ r) skip so))))
             , silent (≃-trans (up-vis c lc (λ (r , _) → sx′ r) (λ (r , _) → sy′ r) skip)
                               (vis-≃ (up-≃ c (≃-sym (rowsY {pred n})))))
    where skip = trunc-≈ (fr Y (λ d → ⊥-elim (nd d)) (λ r → r) inj₁)

  done : T d → pred n ≡ 0 → Inv ⟨ c , node (pred n) , rising cp , p ⟩ × Moves (up c (Flat.RowT L O d LX)) [] (up c (Plus (rows ρ (node (pred n))) p end))
  done td pz = inv good′ (uc , lc , owes′ , tt , (λ r → ⊥-elim (empty-node r)) , empty-node
                         , srcO-≃ c to-node (srcO-≈ c lc (λ (r , _) → sx′ r) (λ (r , _) → since′ r) skip so))
             , silent (≃-trans (up-vis c lc (λ (r , _) → sx′ r) (λ (r , _) → since′ r) skip)
                               (vis-≃ (up-≃ c to-node)))
    where
      eo = spent td
      z  = trans (sym cnt) pz
      gs = goodL-ʳ++⁻ pre lanesG
      ep = dead-empty pre (proj₁ gs) (m+n≡0⇒m≡0 (live pre) z)
      eq = dead-empty post (proj₂ (proj₂ gs)) (m+n≡0⇒n≡0 (live pre) z)
      D  = da td ep eq
      empty-node : Empty (rows ρ (node (pred n)))
      empty-node (r , _) = empty-≃ (≃-sym joinY) (flat-empty L eo (all-ʳ++ Pre ep ((λ {_} {_} ()) , eq))) r
      back : ∀ {k e} → Plus Y p end k e → Y k e ⊎ (k ≡ p × e ≡ end × Flat.Done L O d LX p)
      back (old r) = inj₁ r
      back new     = inj₂ (refl , refl , D)
      since′ : Since p (Plus Y p end)
      since′ (old r) = sy′ r
      since′ new     = ≼-refl {p}
      skip   = trunc-≈ (fr (Plus Y p end) (λ _ → new) old back)
      to-node = ≃-trans (trunc-plus sy′) (plus-≃ (≃-sym (rowsY {pred n})))

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
  Out m = Inv ⟨ c , node (pred n) , m , p ⟩ × Moves (up c (Flat.RowT L O d LX)) [] (up c (here ρ (node (pred n)) m p))

  pick : ∀ b → d ≡ b → ∀ m → pred n ≡ m → Out (settle b m true)
  pick false db m em = pass (outer-owes L {p} {O} {d} Pre Post {rows ρ s₀} ao apre apost en nd) (flat-owing-o L {O} {d} {LY} ow)
    where nd = λ t → subst T db t
          ow = ho nd
  pick true db zero em = done (subst T (sym db) tt) em
  pick true db (suc k) em = pass (lanes-owe L {p} {O} {d} Pre Post {rows ρ s₀} ao apre apost en w) (flat-owing-l L {O} {d} {LY} (owing-ly w))
    where w = live-other k (trans (sym cnt) em)

  result : Out (settle d (pred n) true)
  result = pick d refl (pred n) refl

-- A LANE'S END, SHOWN ONLY AS THE LAST WITH THE OUTER DONE.
rise-lane-cp : ∀ {R Γ A B} f d n q (o : St Γ A) pre post (c : Ctx R Γ B) s p
             → Sim ⟨ inLanes (mergeᶠ nothing) f d n q o pre post c , s , rising cp , p ⟩ []
                   (if alive s then dequeue c (mergeᶠ nothing) f d (pred n) q o (pre ʳ++ ended s ∷ post) p
                               else ⟨ c , flatS (mergeᶠ nothing) f d n q o (pre ʳ++ s ∷ post) , absorbed , p ⟩)
rise-lane-cp f d n q o pre post c s p (inv g (u , l , os , op′ , as , es , so)) with upo-liv (inLanes (mergeᶠ nothing) f d n q o pre post c) u
... | lv with lane-v s (subst (λ v → GLn (env c) v s) lv (proj₂ (good-split (inLanes (mergeᶠ nothing) f d n q o pre post c) s g)))
... | off a s₀ = ⊥-elim op′
... | on a s₀ g₀ _ with subst (λ v → G (env c) v (flatS (mergeᶠ nothing) f d n q o (pre ʳ++ lnS true (cutS true a s₀) ∷ post))) lv
                            (node-good c (flatS (mergeᶠ nothing) f d n q o (pre ʳ++ lnS true (cutS true a s₀) ∷ post)) g (λ ()) (λ ()))
... | mg with MergeG.fresh mg | u | l
... | refl | ho , oo , op , oq , uc | ao , apre , apost , lc =
  Cp.result f d n o pre post c a s₀ p g mg g₀ ho oo op oq uc ao apre apost lc es so
