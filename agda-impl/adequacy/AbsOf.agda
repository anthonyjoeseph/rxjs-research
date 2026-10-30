{-# OPTIONS --guardedness #-}

-- AN OF'S NEXT RUN, AGAINST THE ROWS: the search lands on an of inside
-- the tree, so the root's rows are the of's rows read up its frames; the
-- of's least row is then its event, risen.  Under a closed frame none of
-- the of's rows reaches the root, and its run is silent.
module adequacy.AbsOf where

open import Data.Bool using (true; false; T; if_then_else_; _∨_)
open import Data.Bool.Properties using (∧-identityʳ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Relation.Unary.All using ([])
open import Data.List using (List; []; _∷_; _ʳ++_; [_]; _++_)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapᴹ)
open import Data.Nat using (suc)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤₁; tt to tt₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)

open import Tree using (mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Events using (ix; last; <ᵖ-part; <ᵖ-ix)
open import denotation.Events using (ofᴱ)
open import denotation.EmissionSet using (EmissionSet; DenEnv; _≺_; InE; at-out; at-end; on-out; out; end)
open import denotation.Laws.Modulus using (≺-≼-≺)
open import operation.Key using (_<ᴷ_)
open import operation.PureObservable using (module Machine)
open Machine using (St; Ctx; CS; Cand; found; ⟨_,_,_,_⟩; absorbed; rising; plug; search; seek; kids; lanes; own; ownBest; first; retag; raceT; sourceT;
                    shift; over; closed; alive; cutT; mapT; scanT; takeT; run; moved; ofM; cp; nx;
                    pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
                    top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody)
open import adequacy.Rows using (env; ∅; up; rows; Plus; module BoundedF; module SwitchF; module ExhaustF; old; new;
  module Flat; _≃_; _⇄_; ≃-sym; Moves; silent)
open import adequacy.Up using (up-≃; ≃-refl; ≃-trans; vis-≃)
open import adequacy.Bound using (Good; LnBody; ofPos; of-from; ⊑→≼)
open import adequacy.Skip using (After; LeadC)
open import adequacy.Lead using (lead-found)
open import adequacy.Swap using (rowsL-ʳ++; ≡→≃)
open import adequacy.Inv using (Inv; inv; Sim; Open; UpO; good-split; unF; liv; Shut; closed-dead; dead-swap)

------------------------------------------------------------------------
-- Where the search lands

-- What a candidate found sits in the tree `t`.
Lands : ∀ {R A} → St [] R → Maybe (Cand R A) → Set₁
Lands t nothing                                  = ⊤₁
Lands t (just (found (_ , _ , c′ , s′) m κ , _)) = plug c′ s′ ≡ t

first-lands : ∀ {R A} {t : St [] R} (x y : Maybe (Cand R A)) → Lands t x → Lands t y → Lands t (first x y)
first-lands nothing             y                     _  ly = ly
first-lands (just x)            nothing               lx _  = lx
first-lands (just (f , h , o))  (just (g , h′ , o′))  lx ly with h′ <ᴷ h
... | true  = ly
... | false = lx

retag-lands : ∀ {R A B} {t : St [] R} (tr : _ → _ → _) (y : Maybe (Cand R A)) → Lands t y → Lands {A = B} t (retag tr y)
retag-lands tr nothing            _ = tt₁
retag-lands tr (just (f , h , o)) l = l

race-lands : ∀ {R A B} {t : St [] R} d n q (x : Maybe (Cand R A)) (y : Maybe (Cand R B)) → Lands t x → Lands t y → Lands t (raceT d n q x y)
race-lands d n q nothing            nothing             _  _  = tt₁
race-lands d n q nothing            (just (g , k , o′)) _  ly = ly
race-lands d n q (just (f , h , o)) nothing             lx _  = lx
race-lands d n q (just (f , h , o)) (just (g , k , o′)) lx ly with h <ᴷ k
... | true  = lx
... | false = ly

source-lands : ∀ {R A B} {t : St [] R} v (x : Maybe (Cand R A)) (y : Maybe (Cand R B)) → Lands t x → Lands t y → Lands t (sourceT v x y)
source-lands v nothing            y                   _  ly = ly
source-lands v (just (f , h , o)) nothing             lx _  = lx
source-lands v (just (f , h , o)) (just (g , k , o′)) lx ly with (if v then h else shift h) <ᴷ k
... | true  = lx
... | false = ly

own-lands : ∀ {R Γ A} {t : St [] R} (c : Ctx R Γ A) (s : St Γ A) → plug c s ≡ t → ∀ ms → Lands t (ownBest c s ms)
own-lands c s e []             = tt₁
own-lands c s e ((m , k) ∷ ms) = first-lands (just (found (_ , _ , c , s) m k , k , _)) (ownBest c s ms) e (own-lands c s e ms)

mutual
  seek-lands : ∀ {R Γ A} {t : St [] R} (c : Ctx R Γ A) (s : St Γ A) → plug c s ≡ t → Lands t (seek c s)
  seek-lands c s e = first-lands (ownBest c s (own s)) (kids c s) (own-lands c s e (own s)) (kids-lands c s e)

  kids-lands : ∀ {R Γ A} {t : St [] R} (c : Ctx R Γ A) (s : St Γ A) → plug c s ≡ t → Lands t (kids c s)
  kids-lands c (mapS f s)              e = retag-lands (mapT f) (seek (inMap f c) s) (seek-lands (inMap f c) s e)
  kids-lands c (scanS f z s)           e = retag-lands (scanT f z) (seek (inScan f z c) s) (seek-lands (inScan f z c) s e)
  kids-lands c (cutS l a s)            e = retag-lands (cutT l) (seek (inCut l a c) s) (seek-lands (inCut l a c) s e)
  kids-lands c (lnS b s)               e = seek-lands (inLn b c) s e
  kids-lands c (takeS i q w s)         e = retag-lands (takeT i q w) (seek (inTake i q w c) s) (seek-lands (inTake i q w c) s e)
  kids-lands c (flatS op f d n q o ls) e =
    race-lands d n q (seek (inOuter op f d n q ls c) o) (lanes c op f d n q o [] ls) (seek-lands (inOuter op f d n q ls c) o e) (lanes-lands c op f d n q o [] ls e)
  kids-lands c (connS k o b)           e =
    source-lands (over k) (seek (inSrc k b c) o) (seek (inBody k o c) b) (seek-lands (inSrc k b c) o e) (seek-lands (inBody k o c) b e)
  kids-lands c (pend _ _)                e = tt₁
  kids-lands c (coldS _ _)             e = tt₁
  kids-lands c (ofS _ _ _)             e = tt₁
  kids-lands c doneS                   e = tt₁
  kids-lands c (joinS _ _ _ _)         e = tt₁

  lanes-lands : ∀ {R Γ A B} {t : St [] R} (c : Ctx R Γ B) op f d n q (o : St Γ A) pre ls
              → plug c (flatS op f d n q o (pre ʳ++ ls)) ≡ t → Lands t (lanes c op f d n q o pre ls)
  lanes-lands c op f d n q o pre []         e = tt₁
  lanes-lands c op f d n q o pre (s ∷ post) e =
    first-lands (retag (cutT (alive s)) (seek (inLanes op f d n q o pre post c) s)) (lanes c op f d n q o (s ∷ pre) post)
      (retag-lands (cutT (alive s)) (seek (inLanes op f d n q o pre post c) s) (seek-lands (inLanes op f d n q o pre post c) s e))
      (lanes-lands c op f d n q o (s ∷ pre) post e)

lands-just : ∀ {R A Γ B} {t : St [] R} {c′ : Ctx R Γ B} {s′ m κ} (y : Maybe (Cand R A)) → Lands t y
           → mapᴹ proj₁ y ≡ just (found (Γ , B , c′ , s′) m κ) → plug c′ s′ ≡ t
lands-just (just (f , _)) l refl = l

-- What the search finds sits where it was found.
search-plug : ∀ {R Γ B} (t : St [] R) {c′ : Ctx R Γ B} {s′ m κ} → search top t ≡ just (found (Γ , B , c′ , s′) m κ) → plug c′ s′ ≡ t
search-plug t fd = lands-just (seek top t) (seek-lands top t refl) fd

------------------------------------------------------------------------
-- The rows, frame by frame

-- What the root owes is the hole's rows read up its frames.
up-plug : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) → up c (rows (env c) s) ≃ rows [] (plug c s)
up-plug top                s = ≃-refl
up-plug (inMap f c)        s = up-plug c (mapS f s)
up-plug (inScan f z c)     s = up-plug c (scanS f z s)
up-plug (inCut true a c)   s = up-plug c (cutS true a s)
up-plug (inCut false a c)  s = up-plug c (cutS false a s)
up-plug (inLn true c)      s = up-plug c (lnS true s)
up-plug (inLn false c)     s = up-plug c (lnS false s)
up-plug (inOuter (mergeᶠ nothing) f d n q ls c) s = up-plug c (flatS (mergeᶠ nothing) f d n q s ls)
up-plug (inLanes (mergeᶠ nothing) f d n q o pre post c) s =
  ≃-trans (up-≃ c (≡→≃ (cong (Flat.RowT _ (rows (env c) o) d n) (sym (rowsL-ʳ++ pre)))))
          (up-plug c (flatS (mergeᶠ nothing) f d n q o (pre ʳ++ s ∷ post)))
up-plug (inTake i q w c)   s = up-plug c (takeS i q w s)
up-plug (inOuter (mergeᶠ (just m)) f d n q ls c) s = up-plug c (flatS (mergeᶠ (just m)) f d n q s ls)
up-plug (inLanes (mergeᶠ (just m)) f d n q o pre post c) s =
  ≃-trans (up-≃ c (≡→≃ (cong (BoundedF.RowT m _ (rows (env c) o) d n q) (sym (rowsL-ʳ++ pre)))))
          (up-plug c (flatS (mergeᶠ (just m)) f d n q o (pre ʳ++ s ∷ post)))
up-plug (inOuter switchᶠ f d n q ls c) s = up-plug c (flatS switchᶠ f d n q s ls)
up-plug (inLanes switchᶠ f d n q o pre post c) s =
  ≃-trans (up-≃ c (≡→≃ (cong (SwitchF.RowT _ (rows (env c) o) d n) (sym (rowsL-ʳ++ pre)))))
          (up-plug c (flatS switchᶠ f d n q o (pre ʳ++ s ∷ post)))
up-plug (inOuter exhaustᶠ f d n q ls c) s = up-plug c (flatS exhaustᶠ f d n q s ls)
up-plug (inLanes exhaustᶠ f d n q o pre post c) s =
  ≃-trans (up-≃ c (≡→≃ (cong (ExhaustF.RowT _ (rows (env c) o) d n) (sym (rowsL-ʳ++ pre)))))
          (up-plug c (flatS exhaustᶠ f d n q o (pre ʳ++ s ∷ post)))
up-plug (inSrc k b c)      s = up-plug c (connS k s b)
up-plug (inBody k o c)     s = up-plug c (connS k o s)

-- Under a cut switched off, the hole reaches nothing.
off-up : ∀ {R Γ A} (c : Ctx R Γ A) {t u : EmissionSet A} → liv c ≡ false → up c t ≃ up c u
off-up top               ()
off-up (inMap f c)       d = off-up c d
off-up (inScan f z c)    d = off-up c d
off-up (inCut true a c)  d = off-up c (trans (sym (∧-identityʳ (liv c))) d)
off-up (inCut false a c) d = ≃-refl
off-up (inLn true c)     d = off-up c d
off-up (inLn false c)    d = ≃-refl
off-up (inTake i q w c)  d = off-up c d
off-up (inOuter (mergeᶠ nothing) f d n q ls c) dd = off-up c dd
off-up (inOuter (mergeᶠ (just m)) f d n q ls c) dd = off-up c dd
off-up (inOuter switchᶠ f d n q ls c) dd = off-up c dd
off-up (inOuter exhaustᶠ f d n q ls c) dd = off-up c dd
off-up (inLanes (mergeᶠ nothing) f d n q o pre post c) dd = off-up c dd
off-up (inLanes (mergeᶠ (just m)) f d n q o pre post c) dd = off-up c dd
off-up (inLanes switchᶠ f d n q o pre post c) dd = off-up c dd
off-up (inLanes exhaustᶠ f d n q o pre post c) dd = off-up c dd
off-up (inSrc k b c)     d = off-up c d
off-up (inBody k o c)    d = off-up c d

------------------------------------------------------------------------
-- What an open hole's frames owe

lnbody-open : ∀ {Γ A} {ρ : DenEnv Γ} {v} (s : St Γ A) → LnBody ρ v false s → Open s → ⊥
lnbody-open (cutS l a s) (refl , _) op = op
lnbody-open (pend _ _)              () _
lnbody-open (coldS _ _)           () _
lnbody-open (ofS _ _ _)           () _
lnbody-open doneS                 () _
lnbody-open (mapS _ _)            () _
lnbody-open (scanS _ _ _)         () _
lnbody-open (lnS _ _)             () _
lnbody-open (takeS _ _ _ _)       () _
lnbody-open (flatS _ _ _ _ _ _ _) () _
lnbody-open (connS _ _ _)         () _
lnbody-open (joinS _ _ _ _)       () _

∨-false : ∀ a {b} → (a ∨ b) ≡ false → b ≡ false
∨-false false e = e
∨-false true  ()

-- An open hole under open frames: the frames it climbs are open.
upo-split : ∀ {R Γ A} (c : Ctx R Γ A) {s : St Γ A} → closed c ≡ false → Open s → Good [] (plug c s) → UpO c
upo-split top              cl op g = tt
upo-split (inMap f c)      cl op g = upo-split c cl _ g
upo-split (inScan f z c)   cl op g = upo-split c cl _ g
upo-split (inTake i q w c) cl op g = upo-split c cl _ g
upo-split (inCut true a c) cl op g = upo-split c cl _ g
upo-split (inCut false a c) () op g
upo-split (inLn true c)    cl op g = upo-split c cl _ g
upo-split (inLn false c) {s} cl op g with unF c (lnS false s) (good-split c (lnS false s) g)
... | inj₁ ()
... | inj₂ (inj₁ lb) = ⊥-elim (lnbody-open s lb op)
... | inj₂ (inj₂ ())
upo-split (inOuter op′ f d n q ls c) cl op g = upo-split c cl _ g
upo-split (inLanes op′ f d n q o pre post c) cl op g = upo-split c cl _ g
upo-split (inSrc k b c)    cl op g = upo-split c (∨-false (CS.closed k) cl) _ g
upo-split (inBody k o c)   cl op g = upo-split c cl _ g

------------------------------------------------------------------------
-- An of's rows

of-next : ∀ {A} p i (x : A) xs → InE (ofᴱ p i (x ∷ xs)) ≃ Plus (InE (ofᴱ p (suc i) xs)) (p ++ [ ix i ]) (out x)
of-next p i x xs = to′ ⇄ from′
  where
    to′ : ∀ {q e} → InE (ofᴱ p i (x ∷ xs)) q e → Plus (InE (ofᴱ p (suc i) xs)) (p ++ [ ix i ]) (out x) q e
    to′ at-out     = new
    to′ (on-out r) = old r
    from′ : ∀ {q e} → Plus (InE (ofᴱ p (suc i) xs)) (p ++ [ ix i ]) (out x) q e → InE (ofᴱ p i (x ∷ xs)) q e
    from′ new     = at-out
    from′ (old r) = on-out r

of-last : ∀ {A} p i → InE (ofᴱ {A} p i []) ≃ Plus ∅ (p ++ [ last ]) end
of-last p i = to′ ⇄ from′
  where
    to′ : ∀ {q e} → InE (ofᴱ p i []) q e → Plus ∅ (p ++ [ last ]) end q e
    to′ at-end = new
    from′ : ∀ {q e} → Plus ∅ (p ++ [ last ]) end q e → InE (ofᴱ p i []) q e
    from′ new = at-end

-- The rest of an of lies past its next.
after-of : ∀ {A} p i (xs : List A) → After (p ++ [ ix i ]) (InE (ofᴱ p (suc i) xs))
after-of p i xs {q} r = ≺-≼-≺ {p ++ [ ix i ]} {ofPos p (suc i) xs} {q} (nxt xs) (⊑→≼ {ofPos p (suc i) xs} {q} (of-from p (suc i) xs r))
  where
    nxt : ∀ {A : Set} (ys : List A) → (p ++ [ ix i ]) ≺ ofPos p (suc i) ys
    nxt []      = subst T (sym (<ᵖ-part p [] [] refl)) tt
    nxt (_ ∷ _) = subst T (sym (<ᵖ-part p [] [] (<ᵖ-ix i))) tt

------------------------------------------------------------------------
-- The run

-- THE FOUND OF LEADS: every other part of each merge above it lies
-- strictly past its event.
found-lead : ∀ {R Γ A} (c : Ctx R Γ A) {i p₀ xs κ} → closed c ≡ false → Good [] (plug c (ofS i p₀ xs))
           → search top (plug c (ofS i p₀ xs)) ≡ just (found (Γ , A , c , ofS i p₀ xs) ofM κ) → LeadC c (ofPos p₀ i xs)
found-lead c {i} {p₀} {xs} cl g fd = lead-found {t = plug c (ofS i p₀ xs)} {c = c} {s = ofS i p₀ xs} cl refl g fd

postulate
  -- THE LEAST ROW TAKEN, THE TREE STILL GOOD.
  good-of   : ∀ {R Γ A} (c : Ctx R Γ A) {i p₀ x xs κ} → closed c ≡ false → Good [] (plug c (ofS i p₀ (x ∷ xs)))
            → search top (plug c (ofS i p₀ (x ∷ xs))) ≡ just (found (Γ , A , c , ofS i p₀ (x ∷ xs)) ofM κ) → Good [] (plug c (ofS (suc i) p₀ xs))
  good-done : ∀ {R Γ A} (c : Ctx R Γ A) {i p₀ κ} → closed c ≡ false → Good [] (plug c (ofS i p₀ []))
            → search top (plug c (ofS i p₀ [])) ≡ just (found (Γ , A , c , ofS i p₀ []) ofM κ) → Good [] (plug c doneS)

-- An of under a dead lane, dropped: checked for shape only.
good-closed : ∀ {R Γ A} (c : Ctx R Γ A) {i p₀ xs} → liv c ≡ false → Good [] (plug c (ofS i p₀ xs)) → Good [] (plug c doneS)
good-closed c d g = dead-swap c d (record { node₀ = λ _ → tt₁ ; lane₀ = λ () ; body₀ = λ _ () ; held₀ = λ () }) g

-- The root's rows, read at the of the search found.
into : ∀ {R Γ′ A′ Γ A} (c : Ctx R Γ′ A′) (s : St Γ′ A′) (c′ : Ctx R Γ A) (s′ : St Γ A) → plug c′ s′ ≡ plug c s
     → up c (rows (env c) s) ≃ up c′ (rows (env c′) s′)
into c s c′ s′ pl = ≃-trans (up-plug c s) (≃-trans (≡→≃ (cong (rows []) (sym pl))) (≃-sym (up-plug c′ s′)))

postulate
  -- AN OF IN A COMPLETED SOURCE RUNS OUT SILENTLY: the source owes nothing
  -- once its connect has seen it complete, so the of's rows reach no row
  -- above it, before or after.
  shut-of : ∀ {R Γ′ A′ Γ A} (c : Ctx R Γ′ A′) (s : St Γ′ A′) (c′ : Ctx R Γ A) {i p₀ xs} p₁ → Shut c′ → plug c′ (ofS i p₀ xs) ≡ plug c s
          → Good [] (plug c s) → Inv ⟨ c′ , doneS , absorbed , p₁ ⟩ × Moves (up c (rows (env c) s)) [] (up c′ ∅)

-- A closed of runs out silently.
closed-of : ∀ {R Γ′ A′ Γ A} (c : Ctx R Γ′ A′) (s : St Γ′ A′) (c′ : Ctx R Γ A) {i p₀ xs} p₁ → closed c′ ≡ true → plug c′ (ofS i p₀ xs) ≡ plug c s
          → Good [] (plug c s) → Inv ⟨ c′ , doneS , absorbed , p₁ ⟩ × Moves (up c (rows (env c) s)) [] (up c′ ∅)
closed-of c s c′ p₁ cl pl g with closed-dead c′ cl
... | inj₂ sh = shut-of c s c′ p₁ sh pl g
... | inj₁ d  =
  inv (good-closed c′ d (subst (Good []) (sym pl) g)) tt , silent (vis-≃ (≃-trans (into c s c′ _ pl) (off-up c′ d)))

-- AN OF'S NEXT RUN: the least row, risen.
abs-of : ∀ {R Γ′ A′ Γ A} {c : Ctx R Γ′ A′} {s} {c′ : Ctx R Γ A} {i p₀ xs κ k′ sh t} p
       → search top (plug c s) ≡ just (found (Γ , A , c′ , ofS i p₀ xs) ofM κ) → run c′ (ofS i p₀ xs) ofM p ≡ moved k′ sh t
       → Sim ⟨ c , s , absorbed , p ⟩ sh k′
abs-of {c = c} {s} {c′} {i} {p₀} {[]} p fd eq (inv g _) with closed c′ in cl
abs-of {c = c} {s} {c′} {i} {p₀} {[]} p fd refl (inv g _) | true = closed-of c s c′ p₀ cl (search-plug (plug c s) fd) g
abs-of {c = c} {s} {c′} {i} {p₀} {[]} p fd refl (inv g _) | false =
  inv (good-done c′ cl g′ fd′) (upo-split c′ cl tt g′ , found-lead c′ cl g′ fd′ , tt , (λ ()) , (λ ()))
  , silent (vis-≃ (≃-trans (into c s c′ _ pl) (up-≃ c′ (of-last p₀ i))))
  where
    pl  = search-plug (plug c s) fd
    fd′ = subst (λ u → search top u ≡ _) (sym pl) fd
    g′  = subst (Good []) (sym pl) g
abs-of {c = c} {s} {c′} {i} {p₀} {x ∷ xs} p fd eq (inv g _) with closed c′ in cl
abs-of {c = c} {s} {c′} {i} {p₀} {x ∷ xs} p fd refl (inv g _) | true = closed-of c s c′ p₀ cl (search-plug (plug c s) fd) g
abs-of {c = c} {s} {c′} {i} {p₀} {x ∷ xs} p fd refl (inv g _) | false =
  inv (good-of c′ cl g′ fd′) (upo-split c′ cl tt g′ , found-lead c′ cl g′ fd′ , tt , after-of p₀ i xs , tt)
  , silent (vis-≃ (≃-trans (into c s c′ _ pl) (up-≃ c′ (of-next p₀ i x xs))))
  where
    pl  = search-plug (plug c s) fd
    fd′ = subst (λ u → search top u ≡ _) (sym pl) fd
    g′  = subst (Good []) (sym pl) g
