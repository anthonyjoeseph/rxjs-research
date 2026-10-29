{-# OPTIONS --guardedness #-}

-- AN OF'S NEXT RUN, AGAINST THE ROWS: the search lands on an of inside
-- the tree, so the root's rows are the of's rows read up its frames; the
-- of's least row is then its event, risen.  Under a closed frame nothing
-- the of owes reaches the root, and its run is silent.
module adequacy.AbsOf where

open import Data.Bool using (true; false; T; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _ʳ++_; [_]; _++_)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapᴹ)
open import Data.Nat using (suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤₁; tt to tt₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst)

open import Tree using (mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Events using (ix; last; <ᵖ-part; <ᵖ-ix)
open import denotation.Events using (ofᴱ)
open import denotation.EmissionSet using (EmissionSet; _≺_; InE; at-out; at-end; on-out; out; end)
open import denotation.Laws.Modulus using (≺-≼-≺)
open import operation.Key using (_<ᴷ_)
open import operation.PureObservable using (module Machine)
open Machine using (St; Ctx; Cand; found; ⟨_,_,_,_⟩; absorbed; rising; plug; search; seek; kids; lanes; own; ownBest; first; retag; raceT; sourceT;
                    shift; over; closed; alive; cutT; mapT; scanT; takeT; run; moved; ofM; cp; nx;
                    pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
                    top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody)
open import adequacy.Rows using (∅; up; rows; Plus; old; new; module Flat; _≃_; _⇄_; ≃-sym; Moves; silent)
open import adequacy.Up using (up-≃; ≃-refl; ≃-trans; vis-≃)
open import adequacy.Bound using (Good; LnBody; ofPos; of-from; ⊑→≼)
open import adequacy.Skip using (After; LeadC)
open import adequacy.Lead using (lead-found)
open import adequacy.Owes using (Owes; UpO; owesL-ʳ++⁻; rowsL-ʳ++; ≡→≃)
open import adequacy.Inv using (Inv; inv; Sim; Open; good-split; unF; closed-dead; dead-swap)

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
  kids-lands c (pend _)                e = tt₁
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
up-plug : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) → up c (rows s) ≃ rows (plug c s)
up-plug top                s = ≃-refl
up-plug (inMap f c)        s = up-plug c (mapS f s)
up-plug (inScan f z c)     s = up-plug c (scanS f z s)
up-plug (inCut true a c)   s = up-plug c (cutS true a s)
up-plug (inCut false a c)  s = up-plug c (cutS false a s)
up-plug (inLn true c)      s = up-plug c (lnS true s)
up-plug (inLn false c)     s = up-plug c (lnS false s)
up-plug (inTake i q w c)   s = up-plug c (takeS i q w s)
up-plug (inOuter (mergeᶠ nothing) f d n q ls c)  s = up-plug c (flatS (mergeᶠ nothing) f d n q s ls)
up-plug (inOuter (mergeᶠ (just m)) f d n q ls c) s = up-plug c (flatS (mergeᶠ (just m)) f d n q s ls)
up-plug (inOuter switchᶠ f d n q ls c)           s = up-plug c (flatS switchᶠ f d n q s ls)
up-plug (inOuter exhaustᶠ f d n q ls c)          s = up-plug c (flatS exhaustᶠ f d n q s ls)
up-plug (inLanes (mergeᶠ nothing) f d n q o pre post c) s =
  ≃-trans (up-≃ c (≡→≃ (cong (Flat.FlatR _ (rows o)) (sym (rowsL-ʳ++ pre)))))
          (up-plug c (flatS (mergeᶠ nothing) f d n q o (pre ʳ++ s ∷ post)))
up-plug (inLanes (mergeᶠ (just m)) f d n q o pre post c) s = up-plug c (flatS (mergeᶠ (just m)) f d n q o (pre ʳ++ s ∷ post))
up-plug (inLanes switchᶠ f d n q o pre post c)           s = up-plug c (flatS switchᶠ f d n q o (pre ʳ++ s ∷ post))
up-plug (inLanes exhaustᶠ f d n q o pre post c)          s = up-plug c (flatS exhaustᶠ f d n q o (pre ʳ++ s ∷ post))
up-plug (inSrc k b c)      s = up-plug c (connS k s b)
up-plug (inBody k o c)     s = up-plug c (connS k o s)

-- Under a closed frame, the hole reaches nothing.
closed-up : ∀ {R Γ A} (c : Ctx R Γ A) {t u : EmissionSet A} → closed c ≡ true → up c t ≃ up c u
closed-up top               ()
closed-up (inMap f c)       e = closed-up c e
closed-up (inScan f z c)    e = ≃-refl
closed-up (inCut true a c)  e = closed-up c e
closed-up (inCut false a c) e = ≃-refl
closed-up (inLn true c)     e = closed-up c e
closed-up (inLn false c)    e = ≃-refl
closed-up (inTake i q w c)  e = ≃-refl
closed-up (inOuter (mergeᶠ nothing) f d n q ls c)  e = closed-up c e
closed-up (inOuter (mergeᶠ (just m)) f d n q ls c) e = ≃-refl
closed-up (inOuter switchᶠ f d n q ls c)           e = ≃-refl
closed-up (inOuter exhaustᶠ f d n q ls c)          e = ≃-refl
closed-up (inLanes (mergeᶠ nothing) f d n q o pre post c)  e = closed-up c e
closed-up (inLanes (mergeᶠ (just m)) f d n q o pre post c) e = ≃-refl
closed-up (inLanes switchᶠ f d n q o pre post c)           e = ≃-refl
closed-up (inLanes exhaustᶠ f d n q o pre post c)          e = ≃-refl
closed-up (inSrc k b c)     e = ≃-refl
closed-up (inBody k o c)    e = ≃-refl

------------------------------------------------------------------------
-- What an open hole's frames owe

lnbody-open : ∀ {Γ A} {v} (s : St Γ A) → LnBody v false s → Open s → ⊥
lnbody-open (cutS l a s) (refl , _) op = op
lnbody-open (pend _)              () _
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

-- An open hole under open frames: what the tree owes, cut there.
owes-split : ∀ {R Γ A} (c : Ctx R Γ A) {s : St Γ A} → closed c ≡ false → Open s → Good (plug c s) → Owes (plug c s) → UpO c × Owes s
owes-split top              cl op g ow = _ , ow
owes-split (inMap f c)      cl op g ow = owes-split c cl _ g ow
owes-split (inCut true a c) cl op g ow = owes-split c cl _ g ow
owes-split (inCut false a c) () op g ow
owes-split (inLn true c)    cl op g ow = owes-split c cl _ g ow
owes-split (inLn false c) {s} cl op g ow with unF c (lnS false s) (proj₂ (good-split c (lnS false s) g))
... | inj₁ ()
... | inj₂ lb = ⊥-elim (lnbody-open s lb op)
owes-split (inOuter (mergeᶠ nothing) f d n q ls c) cl op g ow with owes-split c cl _ g ow
... | u , (h , o , ol) = (ol , u) , o
owes-split (inLanes (mergeᶠ nothing) f d n q o pre post c) cl op g ow with owes-split c cl _ g ow
... | u , (h , oo , ol) with owesL-ʳ++⁻ pre ol
... | op′ , (_ , os , oq) = (h , oo , op′ , oq , u) , os
owes-split c@(inScan _ _ _)    {s} cl op g ow = ⊥-elim (proj₁ (good-split c s g))
owes-split c@(inTake _ _ _ _)  {s} cl op g ow = ⊥-elim (proj₁ (good-split c s g))
owes-split c@(inOuter (mergeᶠ (just _)) _ _ _ _ _ _) {s} cl op g ow = ⊥-elim (proj₁ (good-split c s g))
owes-split c@(inOuter switchᶠ _ _ _ _ _ _)           {s} cl op g ow = ⊥-elim (proj₁ (good-split c s g))
owes-split c@(inOuter exhaustᶠ _ _ _ _ _ _)          {s} cl op g ow = ⊥-elim (proj₁ (good-split c s g))
owes-split c@(inLanes (mergeᶠ (just _)) _ _ _ _ _ _ _ _) {s} cl op g ow = ⊥-elim (proj₁ (good-split c s g))
owes-split c@(inLanes switchᶠ _ _ _ _ _ _ _ _)           {s} cl op g ow = ⊥-elim (proj₁ (good-split c s g))
owes-split c@(inLanes exhaustᶠ _ _ _ _ _ _ _ _)          {s} cl op g ow = ⊥-elim (proj₁ (good-split c s g))
owes-split c@(inSrc _ _ _)     {s} cl op g ow = ⊥-elim (proj₁ (good-split c s g))
owes-split c@(inBody _ _ _)    {s} cl op g ow = ⊥-elim (proj₁ (good-split c s g))

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
found-lead : ∀ {R Γ A} (c : Ctx R Γ A) {i p₀ xs κ} → closed c ≡ false → Good (plug c (ofS i p₀ xs))
           → search top (plug c (ofS i p₀ xs)) ≡ just (found (Γ , A , c , ofS i p₀ xs) ofM κ) → LeadC c (ofPos p₀ i xs)
found-lead c {i} {p₀} {xs} cl g fd = lead-found {t = plug c (ofS i p₀ xs)} {c = c} {s = ofS i p₀ xs} cl refl g fd

postulate
  -- THE LEAST ROW TAKEN, THE TREE STILL GOOD.
  good-of   : ∀ {R Γ A} (c : Ctx R Γ A) {i p₀ x xs κ} → closed c ≡ false → Good (plug c (ofS i p₀ (x ∷ xs)))
            → search top (plug c (ofS i p₀ (x ∷ xs))) ≡ just (found (Γ , A , c , ofS i p₀ (x ∷ xs)) ofM κ) → Good (plug c (ofS (suc i) p₀ xs))
  good-done : ∀ {R Γ A} (c : Ctx R Γ A) {i p₀ κ} → closed c ≡ false → Good (plug c (ofS i p₀ []))
            → search top (plug c (ofS i p₀ [])) ≡ just (found (Γ , A , c , ofS i p₀ []) ofM κ) → Good (plug c doneS)
  -- A CLOSED OF, DROPPED: what is owed above the cut does not change.
  owes-closed : ∀ {R Γ A} (c : Ctx R Γ A) {i p₀ xs} → closed c ≡ true → Owes (plug c (ofS i p₀ xs)) → Owes (plug c doneS)

-- A closed of sits under a dead lane, so dropping it is checked for shape only.
good-closed : ∀ {R Γ A} (c : Ctx R Γ A) {i p₀ xs} → closed c ≡ true → Good (plug c (ofS i p₀ xs)) → Good (plug c doneS)
good-closed c cl g = dead-swap c (closed-dead c (proj₁ (good-split c _ g)) cl) (record { node₀ = λ _ → tt ; lane₀ = λ () ; body₀ = λ _ () }) g

-- The root's rows, read at the of the search found.
into : ∀ {R Γ′ A′ Γ A} (c : Ctx R Γ′ A′) (s : St Γ′ A′) (c′ : Ctx R Γ A) (s′ : St Γ A) → plug c′ s′ ≡ plug c s → up c (rows s) ≃ up c′ (rows s′)
into c s c′ s′ pl = ≃-trans (up-plug c s) (≃-trans (≡→≃ (cong rows (sym pl))) (≃-sym (up-plug c′ s′)))

-- A closed of runs out silently.
closed-of : ∀ {R Γ′ A′ Γ A} (c : Ctx R Γ′ A′) (s : St Γ′ A′) (c′ : Ctx R Γ A) {i p₀ xs} p₁ → closed c′ ≡ true → plug c′ (ofS i p₀ xs) ≡ plug c s
          → Good (plug c s) → Owes (plug c s) → Inv ⟨ c′ , doneS , absorbed , p₁ ⟩ × Moves (up c (rows s)) [] (up c′ ∅)
closed-of c s c′ p₁ cl pl g ow =
  inv (good-closed c′ cl (subst Good (sym pl) g)) (owes-closed c′ cl (subst Owes (sym pl) ow)) , silent (vis-≃ (≃-trans (into c s c′ _ pl) (closed-up c′ cl)))

-- AN OF'S NEXT RUN: the least row, risen.
abs-of : ∀ {R Γ′ A′ Γ A} {c : Ctx R Γ′ A′} {s} {c′ : Ctx R Γ A} {i p₀ xs κ k′ sh t} p
       → search top (plug c s) ≡ just (found (Γ , A , c′ , ofS i p₀ xs) ofM κ) → run c′ (ofS i p₀ xs) ofM p ≡ moved k′ sh t
       → Sim ⟨ c , s , absorbed , p ⟩ sh k′
abs-of {c = c} {s} {c′} {i} {p₀} {[]} p fd eq (inv g ow) with closed c′ in cl
abs-of {c = c} {s} {c′} {i} {p₀} {[]} p fd refl (inv g ow) | true = closed-of c s c′ p₀ cl (search-plug (plug c s) fd) g ow
abs-of {c = c} {s} {c′} {i} {p₀} {[]} p fd refl (inv g ow) | false =
  inv (good-done c′ cl g′ fd′) (proj₁ (owes-split c′ cl tt g′ ow′) , found-lead c′ cl g′ fd′ , tt , tt , (λ ()) , (λ ()))
  , silent (vis-≃ (≃-trans (into c s c′ _ pl) (up-≃ c′ (of-last p₀ i))))
  where
    pl  = search-plug (plug c s) fd
    fd′ = subst (λ u → search top u ≡ _) (sym pl) fd
    g′  = subst Good (sym pl) g
    ow′ = subst Owes (sym pl) ow
abs-of {c = c} {s} {c′} {i} {p₀} {x ∷ xs} p fd eq (inv g ow) with closed c′ in cl
abs-of {c = c} {s} {c′} {i} {p₀} {x ∷ xs} p fd refl (inv g ow) | true = closed-of c s c′ p₀ cl (search-plug (plug c s) fd) g ow
abs-of {c = c} {s} {c′} {i} {p₀} {x ∷ xs} p fd refl (inv g ow) | false =
  inv (good-of c′ cl g′ fd′) (proj₁ (owes-split c′ cl tt g′ ow′) , found-lead c′ cl g′ fd′ , tt , tt , after-of p₀ i xs , tt)
  , silent (vis-≃ (≃-trans (into c s c′ _ pl) (up-≃ c′ (of-next p₀ i x xs))))
  where
    pl  = search-plug (plug c s) fd
    fd′ = subst (λ u → search top u ≡ _) (sym pl) fd
    g′  = subst Good (sym pl) g
    ow′ = subst Owes (sym pl) ow
