{-# OPTIONS --guardedness #-}

-- A CONNECT'S OWN MARKS, run over the cursor invariant: its body's run
-- subscribes its source at the connect's `ix 1`, its source's attach
-- returns from that subscribe call, and its owed teardown stops the
-- source once the body is over.  None shows a row.
module adequacy.RunCon where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥-elim)
open import Data.List using ([]; _∷_; [_]; _++_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import denotation.Events using (ix)
open import denotation.EmissionSet using (EmissionSet)
open import denotation.Laws.Modulus using (≼-refl)
open import denotation.Laws.Worlds using (ok-step)
open import operation.Key using (at; at-after-≮)
open import operation.PureObservable using (module Machine)
open Machine using (St; Ctx; Conf; Scope; ⟨_,_,_,_⟩; subscribing; absorbed; moved; plug; run; own; CS; cs; bodyM; srcAttM; owedM;
                    pend; connS; inSrc; scopeOf; binds)
open import adequacy.Rows using (Frozen; ≃-refl; Vis; _≃_; _⇄_; silent; Moves)
open _≃_
open import adequacy.Cursor using (Cur; bef; Parts; Flags; Sound; Husk; SrcH; Unread; NoIsle; _∪ᵖ_; _⊑_; ∅ᵖ; ∅-⊑; ⊑-refl; ⊑-trans;
  h-blank; h-conn; sh-dead; sh-isle; sh-islec; sh-pend; src-pend; src-on; src-shut; s-conn; Torn; un-dead; un-torn;
  owes; dead; lane; lanecut; pnd; c-abs; c-sub; ≈-refl; notT; sync-pend; subd;
  f-src; f-srcc; f-isle; f-islec; d-src)
open import adequacy.Cursor.Rise using (Inv; settled; pending; RT)
open import adequacy.Least using (Lo; k-kid; k-body)
open import adequacy.Floor.Keys using (plug-in)
open import adequacy.Bound using (behind-pend)
open import adequacy.Few using (fr-shift)
open import adequacy.Walk using (nowhere; none′)
open import adequacy.Stamped using (StOK)
open import adequacy.Isle using (G; NoAttB; att-key; noatt-noisle)

-- What the root owes, moved row for row.
vis-≃ : ∀ {A} {E E′ : EmissionSet A} → E ≃ E′ → Vis E ≃ Vis E′
vis-≃ d = (λ (x , v) → to d x , v) ⇄ (λ (x , v) → from d x , v)

-- A connect's parts read again under fields they do not read.
re-parts : ∀ {Γ X B} {sc : Scope Γ} {Rg} {k k′ : CS Γ X} {β : EmissionSet B} → Frozen k ≡ Frozen k′ → Parts sc Rg k β → Parts sc Rg k′ β
re-parts e pt = record { Rb = Parts.Rb pt ; Rs = Parts.Rs pt ; b⊆ = Parts.b⊆ pt ; s⊆ = Parts.s⊆ pt ; apart = Parts.apart pt
                       ; clear = Parts.clear pt ; sb = Parts.sb pt ; ss = subst (Sound (Parts.Rs pt)) e (Parts.ss pt) }

-- A connect's flags read again once its body has run.
re-body : ∀ {Γ X B} {C} {cl sl sa p as ow cx ea sr sc} {β : EmissionSet B} {q}
        → Flags C (cs {Γ} {X} cl sl sa p as ow cx ea sr sc) β → Flags C (cs cl sl sa nothing q ow cx ea sr sc) β
re-body fl = record { shut = Flags.shut fl ; unshut = Flags.unshut fl ; torn = Flags.torn fl }

-- A body's run finds no attach owed in it: the body's every attach is
-- keyed after its own run, and no mark of the tree is keyed before it.
body-noisle : ∀ {R Γ A X} (c : Ctx R Γ A) {k : CS Γ X} {o : St Γ X} {b : St (X ∷ Γ) A} {p}
            → StOK (connS k o b) → G (connS k o b) → CS.bodyAt k ≡ just p → Lo (plug c (connS k o b)) (at (p ++ [ ix 1 ])) → NoIsle b
body-noisle c {b = b} {p} (_ , _ , hb , _) (_ , up , _ , gb) e lo = noatt-noisle b hb gb na
  where
    na : NoAttB b
    na a = at-after-≮ (p ++ [ ix 1 ]) _ (proj₂ (up a) e) (lo (plug-in c (k-kid (k-body (att-key a)))))

module _ {R : Set} (Rt : EmissionSet R) where

  -- What a body's run reaches.
  Ran : Cur → Conf R → Set₁
  Ran Cr k′ = Σ Cur λ Cr′ → Σ Cur λ C′ → Inv Rt Cr′ C′ k′ × Moves (RT Rt Cr) [] (RT Rt Cr′)

  -- A SOURCE IN A PART NO LIVE NODE READS, subscribed by its body's run:
  -- not yet subscribed, an isle born at its own cursor there; otherwise
  -- what it was.
  unread-body : ∀ {Cr C Γ X B} {c : Ctx R Γ B} {cl sl sa p as ow cx ea sr sc} {o₀ q} {b : St (X ∷ Γ) B} {P Ps Qb}
              → Unread Rt Cr C c (cs cl sl sa nothing (just (p ++ [ ix 1 ])) ow cx ea sr sc) P
              → SrcH (scopeOf c) (cs cl sl sa (just p) as ow cx ea sr sc) (pend o₀ q) Ps
              → Husk (binds sr cx sc) b Qb → P ⊑ (Ps ∪ᵖ Qb) → NoIsle b
              → Ran Cr ⟨ inSrc (cs cl sl sa nothing (just (p ++ [ ix 1 ])) ow cx ea sr sc) b c , pend o₀ q , subscribing , p ++ [ ix 1 ] ⟩
  unread-body {Cr} {C} {cl = cl} {sl} {sa} {p} {as} {ow} {cx} {ea} {sr} {sc} un (sh-pend na nc refl scp (ok , adm) pe wn ss) hb le nb =
    Cr , bef (cx ++ [ ix 1 ]) ,
    pending (f-isle un hb le na nc (behind-pend {C = bef (cx ++ [ ix 1 ])} {k = cs cl sl sa nothing (just (p ++ [ ix 1 ])) ow cx ea sr sc} scp (ok , adm) (≼-refl {cx ++ [ ix 1 ]})) (subd (λ o → o) ok) ss nb)
            (≼-refl {cx ++ [ ix 1 ]} , ok-step cx ok , adm , pe , wn) ,
    silent ≃-refl
  unread-body {Cr} {C} un (sh-dead hk) hb le nb = Cr , C , settled {Rg = nowhere} {E = none′} c-sub (d-src un hb le nb) (_ , hk , ⊑-refl) , silent ≃-refl
  unread-body un (sh-isle _ _ sy _ _ _) hb le nb = ⊥-elim (sync-pend tt sy)
  unread-body {Cr} {C} un (sh-islec na cl sp tp hk bh sd) hb le nb =
    Cr , C , settled {Rg = nowhere} {E = none′} c-sub (f-islec un hb le na cl sp tp bh sd) (_ , hk , ⊑-refl) , silent ≃-refl

  -- THE BODY'S RUN.  A live source owed at the connect's `ix 1` is the
  -- new hole, every frame shifted to just before it, its mark being the
  -- tree's least; an ended one is left to its husk; a torn-down one, or
  -- one in a part no live node reads, is `unread-body`'s.
  con-body : ∀ {Cr C Γ X B} {c : Ctx R Γ B} {cl sl sa p as ow cx ea sr sc} {o₀ q} {b : St (X ∷ Γ) B} {r}
           → NoIsle b → Lo (plug c (connS (cs cl sl sa (just p) as ow cx ea sr sc) (pend o₀ q) b)) (at (p ++ [ ix 1 ]))
           → Inv Rt Cr C ⟨ c , connS (cs cl sl sa (just p) as ow cx ea sr sc) (pend o₀ q) b , absorbed , r ⟩
           → Ran Cr ⟨ inSrc (cs cl sl sa nothing (just (p ++ [ ix 1 ])) ow cx ea sr sc) b c , pend o₀ q , subscribing , p ++ [ ix 1 ] ⟩
  con-body {sl = true} {cx = cx} nb lo (settled {N = owes} c-abs fr sy@(s-conn scp pt bs ss tn fl eq)) with ss tt
  ... | src-on _ sy′ _ _ _ = ⊥-elim (sync-pend tt sy′)
  ... | src-shut cl′ sp tp hk bh sd =
    _ , _ , settled {Rg = nowhere} {E = none′} c-sub (f-srcc fr scp (re-parts refl pt) tt cl′ sp tp bh sd (bs tt) (re-body fl) eq) (_ , hk , ⊑-refl) , silent ≃-refl
  ... | src-pend _ nc₀ refl _ _ _ ow with fr-shift Rt fr sy ow lo
  ...   | Cr′ , fr′ , s-conn scp′ pt′ bs′ ss′ _ fl′ eq′ , d with ss′ tt
  ...     | src-on _ sy′ _ _ _ = ⊥-elim (sync-pend tt sy′)
  ...     | src-shut cl′ _ _ _ _ _ = ⊥-elim (notT _ nc₀ cl′)
  ...     | src-pend {k = k} na nc refl (ok , adm) pe wn _ =
    Cr′ , bef (cx ++ [ ix 1 ]) ,
    pending (f-src fr′ scp′ (re-parts refl pt′) tt nc (bs′ tt) (re-body fl′) ≈-refl eq′
                   (behind-pend {C = bef (cx ++ [ ix 1 ])} {k = k} scp′ (ok , adm) (≼-refl {cx ++ [ ix 1 ]})) (subd (λ o → o) ok)
                   (λ t → ⊥-elim (notT _ na t)) nb)
            (≼-refl {cx ++ [ ix 1 ]} , ok-step cx ok , adm , pe , wn) ,
    silent (vis-≃ d)
  con-body {sl = false} nb lo (settled {N = owes} c-abs fr (s-conn scp pt bs ss tn fl eq)) =
    unread-body (un-torn fr scp (re-parts refl pt) tt (re-body fl) eq (Torn.tl (tn tt))) (Torn.sh (tn tt)) (Torn.bh (tn tt)) ⊑-refl nb
  con-body {Cr} {C} nb lo (settled {N = dead _} c-abs fr (_ , h-blank , le)) =
    Cr , C , settled {Rg = nowhere} {E = none′} c-sub (d-src {N = ∅ᵖ} (un-dead fr) h-blank (⊑-trans le ∅-⊑) nb) (∅ᵖ , h-blank , ⊑-refl) , silent ≃-refl
  con-body nb lo (settled {N = dead _} c-abs fr (_ , h-conn sh hb , le)) = unread-body (un-dead fr) sh hb le nb
  con-body nb lo (settled {N = lane _ _} c-abs fr (_ , _ , () , _))
  con-body nb lo (settled {N = lanecut _ _} c-abs fr (_ , _ , () , _))
  con-body nb lo (settled {N = pnd _} c-abs fr (_ , () , _))
