{-# OPTIONS --guardedness #-}

module adequacy.Cursor.Rise where

open import Data.Bool using (Bool; T; true; false; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; [_]; _++_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; sym)
open import Relation.Nullary using (¬_)

open import denotation.Events using (ix; last)
open import denotation.Read using (Visible)
open import denotation.EmissionSet using (EmissionSet; out; end; _≺_; _≼_; MapT; map-out; map-end; module Scan; module TakeWhile)
open import operation.PureObservable using (module Machine; Tape; play; ending) renaming (over to tapeOver)
open Machine using (St; Ctx; Conf; ⟨_,_,_,_⟩; Scope; unbound; binds; CS; Owe; closed; free; cpAt; cutAt; overAt; scopeOf;
                    Att; attached; attAt; subscribing; absorbed; rising; mapEv; nx; cp;
                    pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
                    top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody; unsub; cut; killAll; unsubIf)
                    renaming (Ev to Evᴹ; Shown to Shownᴹ)
open import denotation.Laws.Modulus using (≼-refl; ≺→≼; ≺-ext; ≺-irrefl; ≺-trans; ≼-or-≻)
open import adequacy.Rows using (≼-≢; _≃_; _⇄_; ≃-refl; Moves; silent; shown; toEv; full; pendRows)
open import denotation.Laws.Worlds using (Ok; Hots)
open import adequacy.Cursor using (Adm; Calm; Cur; Due; Folded; Husk; NoFail; Owes; Sound; SrcH; Sync; Within; _∪ᵖ_; _≈_; _⊑_; aft; alike; bef; c-abs; cut-husk; fd-last; fd-none; h-conn; h-cut; h-ln; h-map; h-scan; h-take; husk-of; notT; o-cp; o-cut; o-over; peel-cut; peel-take; s-conn; s-cut; s-map; s-scan; s-take; s-took; tailp-dn; tailp-⊑; unsub-husk; unsubIf-husk; vis; ∪-⊑; ⊑-refl; ⊑-trans)
open import adequacy.Cursor.Frame using (Fly; Fr; Hold; Rest; Unread; d-body; d-cut; d-ln; d-map; d-scan; d-take; dead; f-body; f-cut; f-lane; f-lnct; f-map; f-scan; f-take; f-took; f-top; lane; lanecut; owes; pnd; un-dead; un-torn)
open import adequacy.PinTail using (took-tail)

open _≃_

module _ {R : Set} (Rt : EmissionSet R) where

  -- THE INVARIANT, at the root's cursor and the hole's: settled, the hole
  -- and every frame in step; a subscription owed where the cursor has not
  -- passed, its program's entry; a rise in flight at `p`, its row in the
  -- hole's entry, delivered below and not yet seen above; or a rise in a
  -- part no live node reads, reaching nothing owed.
  data Inv : Cur → Cur → Conf R → Set₁ where
    settled : ∀ {Γ A} {c : Ctx R Γ A} {s m p Cr C Rg N E} → Calm m
            → Fr Rt Cr C Rg c N E → Hold (scopeOf c) Rg C N s E → Inv Cr C ⟨ c , s , m , p ⟩
    pending : ∀ {Γ A} {c : Ctx R Γ A} {o q p Cr C Rg E}
            → Fr Rt Cr C Rg c owes E
            → Owes C q × Ok (Hots (full (scopeOf c))) q × Adm (scopeOf c) × pendRows (full (scopeOf c)) o q ≈ E
              × Within Rg (scopeOf c) q (pendRows (full (scopeOf c)) o q)
            → Inv Cr C ⟨ c , pend o q , subscribing , p ⟩
    flying  : ∀ {Γ A} {c : Ctx R Γ A} {s e p Cr Rg N E}
            → Fr Rt Cr (bef p) Rg c N E → closed c ≡ false → Fly (scopeOf c) Rg p N s E e → Inv Cr (bef p) ⟨ c , s , rising e , p ⟩
    adrift  : ∀ {Γ A} {c : Ctx R Γ A} {s e p Cr C Rg P E}
            → Fr Rt Cr C Rg c (dead P) E → closed c ≡ false → Rest (scopeOf c) s P → Inv Cr C ⟨ c , s , rising e , p ⟩

  -- What the root owes: its entry past the cursor.
  RT : Cur → EmissionSet R
  RT C = Due C Rt

  -- A step: the invariant kept at some cursors, the rows moved.
  SimC : Conf R → Shownᴹ R → Conf R → Set₁
  SimC k sh k′ = ∀ {Cr C} → Inv Cr C k → Σ Cur λ Cr′ → Σ Cur λ C′ → Inv Cr′ C′ k′ × Moves (RT Cr) sh (RT Cr′)

  -- The invariant kept at its cursors.
  keeps : ∀ {k k′} → (∀ {Cr C} → Inv Cr C k → Inv Cr C k′) → SimC k [] k′
  keeps g {Cr} {C} i = Cr , C , g i , silent ≃-refl

  -- A connect no live node reads, settled where it is read.
  unread-at : ∀ {Cr C Γ X B} {c : Ctx R Γ B} {k : CS Γ X} {o b P Ps Qb p}
            → Unread Rt Cr C c k P → SrcH (scopeOf c) k o Ps → Husk (binds (CS.src k) (CS.connAt k) (CS.scope k)) b Qb → P ⊑ (Ps ∪ᵖ Qb)
            → Inv Cr C ⟨ c , connS k o b , absorbed , p ⟩
  unread-at (un-dead fr) sh hb le = settled c-abs fr (_ , h-conn sh hb , le)
  unread-at {C = C} (un-torn fr sc pt nl fl eq tp) sh hb le =
    settled c-abs fr (s-conn sc pt (λ t → ⊥-elim (notT _ nl t)) (λ t → ⊥-elim (notT _ nl t)) (λ t → ⊥-elim (notT _ nl t))
                             (λ _ → record { Ps = _ ; Pb = _ ; sh = sh ; bh = hb ; tl = tailp-⊑ {C = C} tp le }) fl eq)

  ----------------------------------------------------------------------
  -- THE ROW SHOWN IS THE LEAST OWED, for free: a rise reaching the root
  -- at `p` is in the root's entry, and the cursor at `bef p` owes nothing
  -- before `p`.

  show-top : ∀ {s e p Rg E} → Fr Rt (bef p) (bef p) Rg top owes E → Sync unbound Rg (aft p) s E × E p (toEv e)
           → Moves (RT (bef p)) [ (p , e) ] (RT (aft p))
  show-top {e = e} {p = p} (f-top eq) (_ , row) = shown ((proj₁ (to (alike eq) (row , vis e)) , vis e , ≼-refl {p}) , vis e) (λ ((_ , _ , o) , _) → o) past
    where
      past : _
      past = (λ { (((x , v , _) , pq) , v′) → (x , v , pq) , v′ })
           ⇄ (λ { {q} ((x , v , pq) , v′) → ((x , v , ≺→≼ {p} {q} pq) , pq) , v′ })

  -- THE ROOT: the row shown, the cursor past it.
  rise-top : ∀ {s : St [] R} {e p} → SimC ⟨ top , s , rising e , p ⟩ [ (p , e) ] ⟨ top , s , absorbed , p ⟩
  rise-top {p = p} (flying fr@(f-top eq) _ h) = aft p , aft p , settled c-abs (f-top eq) (proj₁ h) , show-top fr h
  rise-top (settled () _ _)
  rise-top (adrift () _ _)

  ----------------------------------------------------------------------
  -- FRAMES THAT ONLY PASS A RISE

  -- MAP: the hole's row mapped.
  rise-map : ∀ {Γ A B} {f : A → B} {c : Ctx R Γ B} {s e p}
           → SimC ⟨ inMap f c , s , rising e , p ⟩ [] ⟨ c , mapS f s , rising (mapEv f e) , p ⟩
  rise-map {f = f} {e = e} = keeps λ
    { (flying (f-map fr eq sd) cl (sy , row)) → flying fr cl (s-map sy eq sd , proj₁ (to (alike eq) (mapped e row , vis (mapEv f e))))
    ; (flying (d-map _) _ ())
    ; (adrift (d-map fr) cl (Q , hk , le))    → adrift fr cl (Q , h-map hk , le)
    ; (settled () _ _) }
    where
      mapped : ∀ {E q} (e : Evᴹ _) → E q (toEv e) → MapT f E q (toEv (mapEv f e))
      mapped (nx a) r = map-out r
      mapped cp     r = map-end r

  -- A SCAN'S VALUE: the hole's value folded into the last fold, the
  -- fold's value at `p`.
  rise-scan-nx : ∀ {Γ A B} {f : B → A → B} {z} {c : Ctx R Γ B} {s a p}
               → SimC ⟨ inScan f z c , s , rising (nx a) , p ⟩ [] ⟨ c , scanS f (f z a) s , rising (nx (f z a)) , p ⟩
  rise-scan-nx {f = f} {z = z} {a = a} {p = p} = keeps λ
    { (flying (f-scan fr fd eq sd) cl (sy , row)) → let ac = folds fd row
                                                    in flying fr cl (s-scan sy (fd-last ac (≺-irrefl {p}) (λ _ pk → pk)) eq sd , proj₁ (to (alike eq) (Scan.sval ac , _)))
    ; (flying (d-scan _) _ ())
    ; (adrift (d-scan fr) cl (Q , hk , le))      → adrift fr cl (Q , h-scan hk , le)
    ; (settled () _ _) }
    where
      folds : ∀ {z₀ E} → Folded (bef p) f z₀ E z → E p (out a) → Scan.Acc f z₀ E p (f z a)
      folds (fd-none ow) row = Scan.acc₀ row ow
      folds (fd-last {q = q} ac nq nx′) row with ≼-or-≻ p q
      ... | inj₁ pq = ⊥-elim (nq pq)
      ... | inj₂ qp = Scan.acc ac row qp λ r qk → nx′ r qk

  -- A SCAN'S END: the fold kept, no value of its source at the end's
  -- position.
  rise-scan-cp : ∀ {Γ A B} {f : B → A → B} {z} {c : Ctx R Γ B} {s p}
               → SimC ⟨ inScan f z c , s , rising cp , p ⟩ [] ⟨ c , scanS f z s , rising cp , p ⟩
  rise-scan-cp {f = f} {z = z} {p = p} = keeps λ
    { (flying (f-scan fr fd eq sd) cl (sy , row)) → flying fr cl (s-scan sy (past sd row fd) eq sd , proj₁ (to (alike eq) (Scan.send row , _)))
    ; (flying (d-scan _) _ ())
    ; (adrift (d-scan fr) cl (Q , hk , le))      → adrift fr cl (Q , h-scan hk , le)
    ; (settled () _ _) }
    where
      after : ∀ {Rg E} → Sound Rg E → E p end → ∀ {q a} → E q (out a) → p ≼ q → p ≺ q
      after sd row {q} y pq = ≼-≢ {p} {q} pq λ { refl → out≢end (Sound.fn sd y row _ _) }
        where
          out≢end : ∀ {A} {a : A} → out a ≡ end → ⊥
          out≢end ()
      past : ∀ {z₀ Rg E} → Sound Rg E → E p end → Folded (bef p) f z₀ E z → Folded (aft p) f z₀ E z
      past sd row (fd-none ow)        = fd-none λ y → after sd row y (ow y)
      past sd row (fd-last ac nq nx′) = fd-last ac (λ pq → nq (≺→≼ {p} pq)) λ y qk → after sd row y (nx′ y qk)

  -- A TAKEWHILE NOT YET FAILED: a value it keeps, or its source's end,
  -- passed on; no failing value shares the row's position.
  module _ {Γ A} {i} {keep : A → Bool} {c : Ctx R Γ A} {s p} where
    unfailed : ∀ {E} → NoFail (bef p) keep E → ¬ TakeWhile.Failed i keep E p
    unfailed {E} nf (q , _ , y , nk , qp) = nf {q} y nk qp

    nf-aft : ∀ {Rg E e′} → Sound Rg E → E p e′ → Visible e′ → (∀ {a′} → out a′ ≡ e′ → T (not (keep a′)) → ⊥)
           → NoFail (bef p) keep E → NoFail (aft p) keep E
    nf-aft sd row v ok nf {q} y nk = ≼-≢ {p} {q} (nf y nk) λ { refl → ok (Sound.fn sd y row _ v) nk }

    rise-take-pass : ∀ {a} → keep a ≡ true
                   → SimC ⟨ inTake i keep free c , s , rising (nx a) , p ⟩ [] ⟨ c , takeS i keep free s , rising (nx a) , p ⟩
    rise-take-pass {a} kt = keeps λ
      { (flying (f-take {E = E} fr nf eq sd) cl (sy , row)) →
          flying fr cl (s-take sy (nf-aft sd row _ kept nf) eq sd , proj₁ (to (alike eq) (TakeWhile.pass row (subst T (sym kt) _) (unfailed {E} nf) , _)))
      ; (flying (f-took _ _ _ _ _ _ _ _) _ ())
      ; (flying (d-take _) _ ())
      ; (adrift (f-took _ _ _ _ () _ _ _) _ _)
      ; (adrift (d-take fr) cl (Q , hk , le)) → adrift fr cl (Q , h-take hk , le)
      ; (settled () _ _) }
      where
        kept : ∀ {a′} → out a′ ≡ out a → T (not (keep a′)) → ⊥
        kept refl nk = subst (λ b → T (not b)) kt nk

    rise-take-cp : SimC ⟨ inTake i keep free c , s , rising cp , p ⟩ [] ⟨ c , takeS i keep free s , rising cp , p ⟩
    rise-take-cp = keeps λ
      { (flying (f-take {E = E} fr nf eq sd) cl (sy , row)) →
          flying fr cl (s-take sy (nf-aft sd row _ (λ ()) nf) eq sd , proj₁ (to (alike eq) (TakeWhile.tend row (unfailed {E} nf) , _)))
      ; (flying (f-took _ _ _ _ _ _ _ _) _ ())
      ; (flying (d-take _) _ ())
      ; (adrift (f-took _ _ _ _ () _ _ _) _ _)
      ; (adrift (d-take fr) cl (Q , hk , le)) → adrift fr cl (Q , h-take hk , le)
      ; (settled () _ _) }

  -- A LIVE CUT passes the row; one off absorbs it.
  rise-cut : ∀ {Γ A} {a} {c : Ctx R Γ A} {s e p}
           → SimC ⟨ inCut true a c , s , rising e , p ⟩ [] ⟨ c , cutS true a s , rising e , p ⟩
  rise-cut = keeps λ
    { (flying (f-cut fr) cl (sy , row))   → flying fr cl (s-cut sy , row)
    ; (flying (f-lnct fr) cl h)           → flying fr cl (_ , _ , refl , _ , h)
    ; (flying (d-cut _) _ ())
    ; (adrift (d-cut fr) cl (Q , hk , le)) → adrift fr cl (Q , h-cut hk , le)
    ; (settled () _ _) }

  rise-cutx : ∀ {Γ A} {a} {c : Ctx R Γ A} {s e p}
            → SimC ⟨ inCut false a c , s , rising e , p ⟩ [] ⟨ c , cutS false a s , absorbed , p ⟩
  rise-cutx = keeps λ
    { (flying (f-lnct _) _ ())
    ; (flying (d-cut _) _ ())
    ; (adrift (f-lnct fr) cl (Q , hk , le)) → settled c-abs fr (_ , _ , refl , Q , hk , le)
    ; (adrift (d-cut fr) cl (Q , hk , le))  → settled c-abs fr (Q , h-cut hk , le)
    ; (settled () _ _) }

  -- A LANE'S OWN FRAME passes the row.
  rise-ln : ∀ {Γ A} {b} {c : Ctx R Γ A} {s e p}
          → SimC ⟨ inLn b c , s , rising e , p ⟩ [] ⟨ c , lnS b s , rising e , p ⟩
  rise-ln = keeps λ
    { (flying (f-lane fr) cl (at , l , refl , h)) → flying fr cl (at , l , refl , h)
    ; (flying (d-ln _) _ ())
    ; (adrift (d-ln fr) cl (Q , hk , le))        → adrift fr cl (Q , h-ln hk , le)
    ; (settled () _ _) }

  -- A TAKEWHILE OVER absorbs whatever still reaches it.
  rise-took : ∀ {Γ A} {i} {keep : A → Bool} {w} {c : Ctx R Γ A} {s e p} → w ≢ free
            → SimC ⟨ inTake i keep w c , s , rising e , p ⟩ [] ⟨ c , takeS i keep w s , absorbed , p ⟩
  rise-took nf = keeps λ
    { (flying (f-took _ _ _ _ _ _ _ _) _ ())
    ; (flying (f-take fr _ _ _) cl h)            → ⊥-elim (nf refl)
    ; (flying (d-take _) _ ())
    ; (adrift (f-took {C = C} fr fl nr fz ow tp eq sd) cl (Q , hk , le)) → settled c-abs fr (s-took fl (λ {q} → nr {q}) fz ow (tailp-⊑ {C = C} tp le) hk eq sd)
    ; (adrift (d-take fr) cl (Q , hk , le))      → settled c-abs fr (Q , h-take hk , le)
    ; (settled () _ _) }

  -- A TAKEWHILE'S FIRST FAILURE, NOT INCLUSIVE: nothing leaves, and it
  -- settles before `p` with the failing row passed, owing what its
  -- source's isles still run.
  rise-take-fail : ∀ {Γ A} {keep : A → Bool} {c : Ctx R Γ A} {s a p} → keep a ≡ false
                 → SimC ⟨ inTake false keep free c , s , rising (nx a) , p ⟩ [] ⟨ c , takeS false keep (cpAt p) s , absorbed , p ⟩
  rise-take-fail {keep = keep} {a = a} {p = p} kf = keeps λ
    { (flying (f-take fr nf eq sd) cl (sy , row)) → let nk = subst (λ b → T (not b)) (sym kf) _ in
        settled c-abs fr (s-took (a , row , nk , λ (_ , _ , y , nk , qp) → nf y nk qp)
                                 (λ pq → pq) (λ ()) (o-cp (≺→≼ {p} {p ++ [ last ]} (≺-ext p {last} [])))
                                 (took-tail sy row nk nf) (proj₂ (husk-of sy)) eq sd)
    ; (flying (f-took _ _ _ _ _ _ _ _) _ ())
    ; (flying (d-take _) _ ())
    ; (adrift (f-took _ _ _ _ () _ _ _) _ _)
    ; (adrift (d-take fr) cl (Q , hk , le)) → settled c-abs fr (Q , h-take hk , le)
    ; (settled () _ _) }

  -- A BODY OF A TORN-DOWN SOURCE has completed: it is stopped, and
  -- nothing reads it.
  rise-bodyx : ∀ {Γ X B} {k : CS Γ X} {o} {c : Ctx R Γ B} {s e p} → CS.srcLive k ≡ false
             → SimC ⟨ inBody k o c , s , rising e , p ⟩ [] ⟨ c , connS k o s , absorbed , p ⟩
  rise-bodyx nl = keeps λ
    { (flying (f-body _ _ _ lv _ _ _ _) _ _) → ⊥-elim (unlive nl lv)
    ; (flying (d-body _ _ _) _ ())
    ; (adrift (d-body u sh le) cl (Q , hk , le′)) → unread-at u sh hk (⊑-trans le (∪-⊑ ⊑-refl le′))
    ; (settled () _ _) }
    where
      unlive : ∀ {b} → b ≡ false → T b → ⊥
      unlive refl ()

  ----------------------------------------------------------------------
  -- RUNS OF A TAKEWHILE'S OWN MARKS

  -- Its completion owed, under `last` of the failing value.
  run-stop : ∀ {Cr Γ A} {i} {keep : A → Bool} {c : Ctx R Γ A} {s r p}
           → closed c ≡ false → Inv Cr (bef (r Machine.⊕ [ last ])) ⟨ c , takeS i keep (cpAt r) s , absorbed , p ⟩
           → Inv Cr (bef (r Machine.⊕ [ last ])) ⟨ c , takeS i keep (cutAt r) s , rising cp , r Machine.⊕ [ last ] ⟩
  run-stop {r = r} cl (settled {N = owes} _ fr h) = flying fr cl (stopped h)
    where
      stopped : ∀ {Γ A} {sc : Scope Γ} {Rg} {i} {keep : A → Bool} {s E}
              → Sync sc Rg (bef (r ++ [ last ])) (takeS i keep (cpAt r) s) E
              → Sync sc Rg (aft (r ++ [ last ])) (takeS i keep (cutAt r) s) E × E (r ++ [ last ]) end
      stopped {A = A} (s-took (a , x , nk , nf) _ fz (o-cp _) tp hk eq sd) =
        s-took (a , x , nk , nf) (λ {q} lt → ≺→≼ {r} {q} (≺-trans {r} {r ++ [ last ]} {q} (≺-ext r {last} []) lt))
               (λ t lt → fz t (≺→≼ {r ++ [ last ]} {r ++ [ ix 0 ]} lt)) (o-cut (≺-irrefl {r ++ [ last ]}))
               (tailp-dn {C = bef (r ++ [ last ])} {C′ = aft (r ++ [ last ])} (λ {y} → ≺→≼ {r ++ [ last ]} {y}) tp) hk eq sd
        , proj₁ (to (alike eq) (TakeWhile.stop x nk nf , vis {A = A} cp))
  run-stop cl (settled {N = dead _} _ fr (Q , hk , le)) = adrift fr cl (let (Q′ , h , le′) = peel-take hk in Q′ , h-take h , ⊑-trans le le′)
  run-stop _ (settled {N = lane _ _} _ fr (_ , _ , () , _))
  run-stop _ (settled {N = lanecut _ _} _ fr (_ , _ , () , _))
  run-stop _ (settled {N = pnd _} _ fr (_ , () , _))

  -- Its source cut: the source is not read, and keeps its isles.
  run-cut : ∀ {Cr C Γ A} {i} {keep : A → Bool} {c : Ctx R Γ A} {s r p p′}
          → Inv Cr C ⟨ c , takeS i keep (cutAt r) s , absorbed , p ⟩ → Inv Cr C ⟨ c , takeS i keep (overAt r) (proj₁ (cut s)) , absorbed , p′ ⟩
  run-cut (settled {N = owes} m fr h) = settled c-abs fr (over h)
    where
      over : ∀ {Γ A} {sc : Scope Γ} {Rg} {C} {i} {keep : A → Bool} {s r} {E : EmissionSet A}
           → Sync sc Rg C (takeS i keep (cutAt r) s) E → Sync sc Rg C (takeS i keep (overAt r) (proj₁ (cut s))) E
      over {C = C} (s-took fl nr fz (o-cut n) tp hk eq sd) = let (_ , h , le) = cut-husk hk in s-took fl (λ {q} → nr {q}) fz (o-over n) (tailp-⊑ {C = C} tp le) h eq sd
  run-cut (settled {N = dead _} m fr (Q , hk , le)) =
    settled c-abs fr (let (_ , h₁ , l₁) = peel-take hk ; (Q₂ , h₂ , l₂) = cut-husk h₁ in Q₂ , h-take h₂ , ⊑-trans le (⊑-trans l₁ l₂))
  run-cut (settled {N = lane _ _} _ fr (_ , _ , () , _))
  run-cut (settled {N = lanecut _ _} _ fr (_ , _ , () , _))
  run-cut (settled {N = pnd _} _ fr (_ , () , _))

  -- A KILL SWITCH ATTACHED: live, nothing changes; off, what it ran is
  -- unsubscribed, keeping its isles.
  run-att : ∀ {Cr C Γ A} {l} {c : Ctx R Γ A} {s s′ q p p′}
          → s′ ≡ proj₁ (unsubIf (not l) s)
          → Inv Cr C ⟨ c , cutS l (attAt q) s , absorbed , p ⟩ → Inv Cr C ⟨ c , cutS l attached s′ , absorbed , p′ ⟩
  run-att {l = true} refl (settled {N = owes} m fr (s-cut sy)) = settled c-abs fr (s-cut sy)
  run-att {l = false} _ (settled {N = owes} m fr ())
  run-att {l = l} refl (settled {N = dead _} m fr (Q , hk , le)) =
    settled c-abs fr (let (_ , h₁ , l₁) = peel-cut hk ; (Q₂ , h₂ , l₂) = unsubIf-husk (not l) h₁ in Q₂ , h-cut h₂ , ⊑-trans le (⊑-trans l₁ l₂))
  run-att {l = true} refl (settled {N = lanecut _ _} m fr (_ , _ , refl , h)) = settled c-abs fr (_ , _ , refl , h)
  run-att {l = false} refl (settled {N = lanecut _ _} m fr (_ , _ , refl , (Q , hk , le))) =
    settled c-abs fr (_ , _ , refl , (let (Q₂ , h₂ , l₂) = unsub-husk hk in Q₂ , h₂ , ⊑-trans le l₂))
  run-att _ (settled {N = lane _ _} _ fr (_ , _ , () , _))
  run-att _ (settled {N = pnd _} _ fr (_ , () , _))
