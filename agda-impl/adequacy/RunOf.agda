{-# OPTIONS --guardedness #-}

-- A LEAF'S NEXT ROW.  The cursor just before an of's next row owes exactly
-- the of's rows from there; delivering that row moves the cursor past
-- it, and what is owed is the rows after it, which are the of's rest.  An
-- of with nothing left owes only its end, so once past it nothing.

-- A joiner's inbox head likewise: past a value the inbox's rest and the
-- rows still unfed are owed, none of whose source rows is the value's
-- own row, which lies above them; past an end nothing rejoined is owed.
module adequacy.RunOf where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; lookup) renaming (_∷_ to _∷ᴬ_)
open import Data.List.Relation.Unary.AllPairs using () renaming (_∷_ to _∷ᴾ_)
open import Data.List.Relation.Unary.Any using (there)
open import Data.Nat using (suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import denotation.Events using (Pos; ix; sub; last; ofᴱ)
open import denotation.EmissionSet using (EmissionSet; Den; hot; enter; Rejoin; shown; heard; ended; late; out; end; _≺_; InE; at-out; at-end; on-out)
open import denotation.Laws.Modulus using (≺-irrefl; ≺-absurd; ≺→≼; ≺-≼-≺; ≼-antisym; ≼-trans; ≼-or-≻)
open import denotation.Laws.Worlds using (Lawful)
open import operation.PureObservable using (module Machine)
open Machine using (Scope; ofS; doneS; joinS; nx; cp) renaming (Ev to Evᴹ)
open import adequacy.Rows using (_≃_; _⇄_; ≼-≢; full; Inbox; this; that)
open import adequacy.Cursor using (origin; bef; aft; Due; Unfed; Sync; s-of; s-done; s-join; s-joinx; alike; cov)
open import adequacy.Bound using (ofKey; of-lb; of-next)
open import adequacy.Up using (module Past)
open import adequacy.FeedUp using (module Walk; bare-end)
open import adequacy.SubJoin using (bind; Bind)

open _≃_

-- A value delivered: the cursor past it owes the rest.
of-nx : ∀ {Γ} {sc : Scope Γ} {Rg} {A} {i q x} {xs : List A} {E : EmissionSet A}
      → Sync sc Rg (bef (q ++ [ ix i ])) (ofS i q (x ∷ xs)) E
      → Sync sc Rg (aft (q ++ [ ix i ])) (ofS (suc i) q xs) E × E (q ++ [ ix i ]) (out x)
of-nx {A = A} {i} {q} {x} {xs} {E} (s-of du (ks , tl)) = s-of du′ (ks , tl′) , proj₁ (from du (at-out , tt , tt))
  where
    p = q ++ [ ix i ]

    past : ∀ {y e} → InE (ofᴱ q (suc i) xs) y e → p ≺ y
    past {y} r = ≺-≼-≺ {p} {ofKey q (suc i) xs} {y} (of-next q i xs) (of-lb q (suc i) xs r)

    peel : ∀ {y e} → InE (ofᴱ q i (x ∷ xs)) y e → p ≺ y → InE (ofᴱ q (suc i) xs) y e
    peel at-out     pp = ⊥-elim (≺-irrefl {p} pp)
    peel (on-out r) _  = r

    du′ : Due (aft p) E ≃ Due origin (InE (ofᴱ q (suc i) xs))
    du′ = (λ (r , v , pk) → peel (proj₁ (to du (r , v , ≺→≼ {p} pk))) pk , v , tt)
        ⇄ (λ (r , v , _) → proj₁ (from du (on-out r , v , tt)) , proj₁ (proj₂ (from du (on-out r , v , tt))) , past r)

    tl′ : ∀ {y e} → E y e → p ≺ y → InE (ofᴱ q (suc i) xs) y e ⊎ y ∈ ks
    tl′ r pk = [ (λ r′ → inj₁ (peel r′ pk)) , inj₂ ]′ (tl r (≺→≼ {p} pk))

-- Its end delivered: the cursor past it owes nothing.
of-cp : ∀ {Γ} {sc : Scope Γ} {Rg} {A} {i q} {E : EmissionSet A}
      → Sync sc Rg (bef (q ++ [ last ])) (ofS i q []) E
      → Sync sc Rg (aft (q ++ [ last ])) doneS E × E (q ++ [ last ]) end
of-cp {A = A} {i} {q} {E} (s-of du (ks , tl)) = s-done sp (ks , fn) , proj₁ (from du (at-end , tt , tt))
  where
    p = q ++ [ last ]

    gone : ∀ {y e} → InE (ofᴱ {A} q i []) y e → p ≺ y → ⊥
    gone at-end pp = ≺-irrefl {p} pp

    sp : ∀ {y e} → Due (aft p) E y e → ⊥
    sp (r , v , pk) = gone (proj₁ (to du (r , v , ≺→≼ {p} pk))) pk

    fn : ∀ {y e} → E y e → p ≺ y → y ∈ ks
    fn r pk = [ (λ r′ → ⊥-elim (gone r′ pk)) , (λ m → m) ]′ (tl r (≺→≼ {p} pk))

------------------------------------------------------------------------
-- A joiner's inbox head

-- A hot binder's rejoined row.
rj : ∀ {A} {d : Den A} {t j y e} → d ≡ hot t → enter d j y e → Rejoin j t y e
rj refl r = proj₁ r

-- A rejoined value: shown, under its source row.
shown-src : ∀ {A} {t : EmissionSet A} {j q a} → Rejoin j t q (out a) → Σ Pos λ k → t k (out a) × q ≡ k ++ [ sub j ]
shown-src (shown y _ _) = _ , y , refl

-- A row rejoined under one at or before an end is not past the end's.
under : ∀ {A} {t : EmissionSet A} {c k e j} → Lawful t → t c end → t k e → (end ≡ e → ⊥) → (c ++ [ sub j ]) ≺ (k ++ [ sub j ]) → ⊥
under {t = t} {c} {k} {e} {j} L yc yk ne qy with ≼-or-≻ c k
... | inj₁ ck = ne (Lawful.func L yc (subst (λ z → t z e) (≼-antisym {k} {c} (Lawful.proper L yc yk) ck) yk))
... | inj₂ kc = ≺-absurd {k ++ [ sub j ]} {c ++ [ sub j ]} (Walk.down k {j = j} L yk yc kc) qy

-- Nothing rejoined lies past an end.
after-end : ∀ {A} {t : EmissionSet A} {j q y e} → Lawful t → Rejoin j t q end → Rejoin j t y e → q ≺ y → ⊥
after-end L (ended yc _) (shown yk b _) qy = under L yc yk (λ w → bare-end b (sym w)) qy
after-end L (ended yc _) (heard yk _)   qy = under L yc yk (λ ()) qy
after-end {j = j} L (ended {c} yc _) (ended {c′} yc′ _) qy =
  ≺-irrefl {c′ ++ [ sub j ]} (subst (λ z → (z ++ [ sub j ]) ≺ (c′ ++ [ sub j ])) (≼-antisym {c} {c′} (Lawful.proper L yc′ yc) (Lawful.proper L yc yc′)) qy)
after-end {j = j} L (ended {c} yc jc) (late {c′} yc′ c′j) _ = ≼-trans {c} {c′} {j} (Lawful.proper L yc′ yc) c′j jc
after-end {j = j} L (late {c} yc cj) (shown {k} yk _ jk) _ = ≼-trans {k} {c} {j} (Lawful.proper L yc yk) cj jk
after-end {j = j} L (late {c} yc cj) (heard {k} yk jk)   _ = ≼-trans {k} {c} {j} (Lawful.proper L yc yk) cj jk
after-end {j = j} L (late {c} yc cj) (ended {c′} yc′ jc′) _ = ≼-trans {c′} {c} {j} (Lawful.proper L yc yc′) cj jc′
after-end {j = j} L (late _ _) (late _ _) qy = ≺-irrefl {j ++ [ last ]} qy

-- An inbox entry lies past what leads the inbox.
inb-≺ : ∀ {A} {q} {ib : List (Pos × Evᴹ A)} {y e} → All (λ u → q ≺ proj₁ u) ib → Inbox ib y e → q ≺ y
inb-≺ (h ∷ᴬ _)  this     = h
inb-≺ {q = q} (_ ∷ᴬ hs) (that m) = inb-≺ {q = q} hs m

-- A row still unfed past a value's rejoined row: its source row is not
-- the value's, which no row of a lawful source lies under.
lift : ∀ {A} {d : Den A} {t j k₀ y e a} → d ≡ hot t → Lawful t → t k₀ (out a)
     → Due (bef (k₀ ++ [ sub j ])) (Unfed (bef (k₀ ++ [ sub j ])) d j) y e → (k₀ ++ [ sub j ]) ≺ y
     → Due (aft (k₀ ++ [ sub j ])) (Unfed (aft (k₀ ++ [ sub j ])) d j) y e
lift {t = t} {j} {k₀} refl L y₀ (shown {k} (y , o) b jk , v , _) qy =
  shown (y , ≼-≢ {k₀ ++ [ sub j ]} {k} o (λ w → Lawful.flat L y₀ (subst (λ z → t z _) (sym w) y))) b jk , v , qy
lift refl L y₀ (heard _ _ , () , _) qy
lift {t = t} {j} {k₀} refl L y₀ (ended {c} (y , o) jc , v , _) qy =
  ended (y , ≼-≢ {k₀ ++ [ sub j ]} {c} o (λ w → Lawful.flat L y₀ (subst (λ z → t z end) (sym w) y))) jc , v , qy
lift {t = t} {j} {k₀} refl L y₀ (late {c} (y , o) cj , v , _) qy =
  late (y , ≼-≢ {k₀ ++ [ sub j ]} {c} o (λ w → Lawful.flat L y₀ (subst (λ z → t z end) (sym w) y))) cj , v , qy

-- A value shown: the cursor past it owes the inbox's rest and what is
-- still unfed.
join-nx : ∀ {Γ} {sc : Scope Γ} {Rg} {A} {j} {x : A ∈ Γ} {q a ib} {E : EmissionSet A}
        → Sync sc Rg (bef q) (joinS j true x ((q , nx a) ∷ ib)) E
        → Sync sc Rg (aft q) (joinS j true x ib) E × E q (out a)
join-nx {sc = sc} {j = j} {x} {q} {a} {ib} {E} (s-join en du (hd ∷ᴾ ap) bh ad) with bind sc x ad
... | t , eq , B with shown-src (rj eq (proj₁ (from (alike en) (proj₁ (from du (inj₁ this)) , tt))))
...   | k₀ , y₀ , refl = s-join en du′ ap bh′ ad , proj₁ (from du (inj₁ this))
  where
    d = lookup (full sc) x
    L = Bind.law B

    pick : ∀ {y e} → q ≺ y → Inbox ((q , nx a) ∷ ib) y e ⊎ Due (bef q) (Unfed (bef q) d j) y e → Inbox ib y e ⊎ Due (aft q) (Unfed (aft q) d j) y e
    pick o (inj₁ this)     = ⊥-elim (≺-irrefl {q} o)
    pick o (inj₁ (that m)) = inj₁ m
    pick o (inj₂ u)        = inj₂ (lift {j = j} {k₀ = k₀} eq L y₀ u o)

    du′ : Due (aft q) E ≃ (λ y e → Inbox ib y e ⊎ Due (aft q) (Unfed (aft q) d j) y e)
    du′ = (λ (r , v , o) → pick o (to du (r , v , ≺→≼ {q} o)))
        ⇄ λ { (inj₁ m) → proj₁ (from du (inj₁ (that m))) , proj₁ (proj₂ (from du (inj₁ (that m)))) , inb-≺ {q = q} hd m
            ; (inj₂ u) → proj₁ (from du (inj₂ (Past.unfed-bef q d u))) , proj₁ (proj₂ u) , proj₂ (proj₂ u) }

    bh′ : ∀ {u y e} → u ∈ ib → Due (aft q) (Unfed (aft q) d j) y e → proj₁ u ≺ y
    bh′ m u = bh (there m) (Past.unfed-bef q d u)

-- An end shown: nothing rejoined lies past it.
join-cp : ∀ {Γ} {sc : Scope Γ} {Rg} {A} {j} {x : A ∈ Γ} {q ib} {E : EmissionSet A}
        → Sync sc Rg (bef q) (joinS j true x ((q , cp) ∷ ib)) E
        → Sync sc Rg (aft q) (joinS j false x ib) E × E q end
join-cp {sc = sc} {j = j} {x} {q} {E = E} (s-join en du _ _ ad) with bind sc x ad
... | t , eq , B = s-joinx sp (proj₁ (cov en) , fn) , row
  where
    L = Bind.law B
    row = proj₁ (from du (inj₁ this))
    qr = rj eq (proj₁ (from (alike en) (row , tt)))

    sp : ∀ {y e} → Due (aft q) E y e → ⊥
    sp (r , v , o) = after-end L qr (rj eq (proj₁ (from (alike en) (r , v)))) o

    fn : ∀ {y e} → E y e → q ≺ y → y ∈ proj₁ (cov en)
    fn r o = [ (λ r′ → ⊥-elim (after-end L qr (rj eq r′) o)) , (λ m → m) ]′ (proj₂ (cov en) r)
