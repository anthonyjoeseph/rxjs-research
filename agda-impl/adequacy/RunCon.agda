{-# OPTIONS --guardedness #-}

-- A CONNECT'S OWN MARKS, run over the cursor invariant: its body's run
-- subscribes its source at the connect's `ix 1`, its source's attach
-- returns from that subscribe call, and its owed teardown stops the
-- source once the body is over.  None shows a row.
module adequacy.RunCon where

open import Data.Bool using (true; false; T; not; _∨_; _∧_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; _∷_) renaming ([] to []ᴬ)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Data.Bool.Properties using (T-≡)
open import Function using (Equivalence)
open import Relation.Nullary using (¬_)

open import denotation.Events using (Pos; ix; inside; inside-++)
open import denotation.EmissionSet using (EmissionSet; pin; end; _≺_; Reach; module Connecting)
open import denotation.Laws.Modulus using (≼-refl; ≺→≼; ≺-trans)
open import denotation.Laws.Worlds using (ok-step)
open import operation.Key using (at; after; at-after-≮)
open import operation.PureObservable using (module Machine)
open Machine using (St; Ctx; Conf; Scope; ⟨_,_,_,_⟩; subscribing; absorbed; moved; plug; run; own; CS; cs; bodyM; srcAttM; owedM;
                    pend; connS; inSrc; scopeOf; binds; closed; unsubIf)
open import adequacy.Rows using (Frozen; ≃-refl; Vis; _≃_; _⇄_; silent; Moves)
open _≃_
open import adequacy.Cursor using (Cur; bef; Owes; Behind; Pts; Held; AttFin; AttOwed; TailP; tailp; Src; Sync; Subd; re-parts;
  under-⊑; tailp-⊑; ∪-⊑; Parts; Flags; Sound; Husk; SrcH; _∪ᵖ_; _⊑_; ⊑-refl; ⊑-trans; h-blank;
  h-conn; sh-dead; sh-isle; sh-islec; sh-pend; src-pend; src-on; src-shut; s-conn; Torn;
  ≈-refl; notT; subd; Thru; Up; up; InCall; Bursts; BurstsAt)
open import adequacy.Cursor.Show using (up-pre; conn-up-body; in-call; thru-dn)
open import adequacy.Cursor.Tear using (husk-of; src-husk; unsubIf-husk; quiet-unsubIf; NoIsle; c-abs; sync-pend)
open import adequacy.Cursor.Frame using (Unread; un-dead; un-torn; owes; dead; lane; lanecut; pnd; Need; Fr; f-top; f-map; f-scan; f-cut; f-take; f-took; f-outer; f-lanes; f-lane; f-lnct; f-src; f-srcc; f-srcp; f-isle; f-islec; f-islep; f-body; d-map; d-scan; d-cut; d-ln; d-take; d-outer; d-lanes; d-src; d-body)
open import adequacy.Cursor.Rise using (Inv; settled; pending; RT)
open import adequacy.Least using (Lo; k-kid; k-body)
open import adequacy.Floor.Keys using (plug-in)
open import adequacy.Bound using (behind-pend; owes?; owes-≼; lo-att; in-slot)
open import adequacy.Few using (few; before; subd-env; nxt; cl; owes-call; tailp-lag; husk-f)
open import adequacy.FrShift using (fr-shift)
open import adequacy.PinTail using (pin-tail; ptl; end-tail; SrcPT; src-pt)
open import adequacy.Stamped using (StOK)
open import adequacy.Isle using (G; NoAttB; att-key; noatt-noisle)

-- What the root owes, moved row for row.
vis-≃ : ∀ {A} {E E′ : EmissionSet A} → E ≃ E′ → Vis E ≃ Vis E′
vis-≃ d = (λ (x , v) → to d x , v) ⇄ (λ (x , v) → from d x , v)

-- A connect's flags read again under fields they do not read.
re-flags : ∀ {Γ X B} {C} {cl sl sa p as ow cx ea sr sc sa′ p′ as′} {β : EmissionSet B}
         → Flags C (cs {Γ} {X} cl sl sa p as ow cx ea sr sc) β → Flags C (cs cl sl sa′ p′ as′ ow cx ea sr sc) β
re-flags fl = record { shut = Flags.shut fl ; unshut = Flags.unshut fl ; torn = Flags.torn fl ; owed = Flags.owed fl ; ended = Flags.ended fl ; owing = Flags.owing fl }

------------------------------------------------------------------------
-- A SOURCE'S ATTACH: its subscribe call has returned, so every key
-- inside it has run, and a source that ran in step through it has only
-- finitely many rows inside it.  An isle attaching leaves its burst to
-- what its source still runs: a row its cursor owes either inside the
-- call, a pin its husk holds, or one of finitely many.

-- Rows before the slot after a subscription: finitely many.
Slot : ∀ {Γ X} → CS Γ X → Set
Slot k = Σ (List Pos) λ ks → ∀ {y e} → Frozen k y e → y ≺ (CS.connAt k ++ [ ix 2 ]) → y ∈ ks

-- A source in step up to its attach: finitely many of its rows before
-- the slot after its subscribe call.
att-rows : ∀ {Γ X} {sc : Scope Γ} {Rg C} {k : CS Γ X} {o} → Sync sc Rg C o (Frozen k) → Behind C (Frozen k) → Subd sc C k
         → Lo o (after (CS.connAt k ++ [ ix 1 ])) → Slot k
att-rows {C = C} {k = k} sy bh sd lo with subd-env {k = k} {p = CS.connAt k ++ [ ix 2 ]} sd (≼-refl {CS.connAt k ++ [ ix 2 ]})
... | env , envl = before {C = C} {E = Frozen k} bh (few sy env envl (lo-att lo))

-- An ended one: likewise, through what its husk still runs.
islec-rows : ∀ {Γ X} {sc : Scope Γ} {Ci D} {k : CS Γ X} {o P} → TailP Ci (Frozen k) P → Husk sc D o (Frozen k) P → Behind Ci (Frozen k)
           → Lo o (after (CS.connAt k ++ [ ix 1 ])) → Slot k
islec-rows {Ci = Ci} {k = k} tp hk bh lo = before {C = Ci} {E = Frozen k} bh (tailp-lag {C = Ci} tp (husk-f hk (lo-att lo)))

-- Finitely many of its rows inside its subscribe call.
att-fin : ∀ {Γ X} {sc : Scope Γ} {Rg C} {k : CS Γ X} {o} → Sync sc Rg C o (Frozen k) → Behind C (Frozen k) → Subd sc C k
        → Lo o (after (CS.connAt k ++ [ ix 1 ]))
        → Σ (List Pos) λ ks → ∀ {y e} → Frozen k y e → T (inside (CS.connAt k ++ [ ix 1 ]) y) → y ∈ ks
att-fin {k = k} sy bh sd lo with att-rows {k = k} sy bh sd lo
... | ks , f = ks , λ x i → f x (in-slot (CS.connAt k) _ i)

-- AN ISLE ATTACHING: its pins, read through its cursor, show in its
-- connect's entry a level down.  A row inside the subscription has
-- finitely many before it, so it is the connect's own pin; one past it
-- was pinned within the call, so to a connect enclosing this one.
isle-up : ∀ {Γ X B} {k : CS Γ X} {Ci D} {E : EmissionSet B} → InCall Ci k → Slot k → Bursts k E → Thru D (CS.connAt k)
        → Up Ci (Frozen k) D E
isle-up {k = k} {Ci} {D} {E} ic (ks , f) bu nr = up lift
  where
    c = CS.connAt k
    lift : ∀ {y r} → Thru Ci r → T (inside r y) → Frozen k y (pin r) → Reach (Frozen k) y (pin r)
         → Σ Pos λ xs → Σ Pos λ r′ → Thru D r′ × T (inside r′ (y ++ xs)) × E (y ++ xs) (pin r′) × Reach E (y ++ xs) (pin r′)
           × All (_≡ ix 0) xs
    lift {y} {r} t i x rc with inside (c ++ [ ix 1 ]) y in iw
    ... | false =
      let (rc′ , x′ , q) = BurstsAt.kept bu x (λ t′ → subst T iw t′) i (ic t) rc
      in [ ix 0 ] , r , thru-dn D {r} {c} rc′ nr
       , Equivalence.from T-≡ (inside-++ r y [ ix 0 ] (Equivalence.to T-≡ i)) , x′ , q , refl ∷ []ᴬ
    ... | true  =
      let iw′ = subst T (sym iw) tt
          (x′ , rc′) = BurstsAt.win bu x iw′ (ks , λ {k′} x″ lt → f x″ (≺-trans {k′} {y} {c ++ [ ix 2 ]} lt (in-slot c y iw′)))
      in [ ix 0 ] , c , nr , in-call c y iw′ , x′ , rc′ , refl ∷ []ᴬ

-- Attached now: already, or its attach owed just after its `ix 1`.
att-now : ∀ {Γ X} {cl sl p ow cx ea sr sc y} sa
        → AttFin (cs {Γ} {X} cl sl sa p (just y) ow cx ea sr sc) → (T (not sa) → AttOwed (cs {Γ} {X} cl sl sa p (just y) ow cx ea sr sc))
        → (y ≡ cx ++ [ ix 1 ] → AttFin (cs {Γ} {X} cl sl true p nothing ow cx ea sr sc)) → AttFin (cs {Γ} {X} cl sl true p nothing ow cx ea sr sc)
att-now true  af _  _ = af
att-now false _  ao f with ao tt
... | inj₁ refl     = f refl
... | inj₂ (_ , ())

-- A burst row its cursor owes: inside the call, a pin of a connect
-- passed, or neither and passed.
held-in : ∀ {Γ X} {Ci} {k : CS Γ X} {P : Pts} {bs fs ps : List Pos}
        → (∀ {y e} → Frozen k y e → ¬ Owes Ci y → y ∈ bs)
        → (∀ {y e} → Frozen k y e → T (inside (CS.connAt k ++ [ ix 1 ]) y) → y ∈ fs)
        → (∀ {y r} → Frozen k y (pin r) → Owes Ci y → ¬ Owes Ci r → P y ⊎ y ∈ ps)
        → ∀ {k′ e} → Frozen k k′ e → Held Ci k k′ e → P k′ ⊎ k′ ∈ bs ++ fs ++ ps
held-in {Ci = Ci} {bs = bs} {fs} bf ff pf {k′} x h with owes? Ci k′
... | inj₂ no = inj₂ (∈-++⁺ˡ (bf x no))
... | inj₁ ow with h
...   | inj₁ i              = inj₂ (∈-++⁺ʳ bs (∈-++⁺ˡ (ff x i)))
...   | inj₂ (_ , refl , np) = [ inj₁ , (λ i → inj₂ (∈-++⁺ʳ bs (∈-++⁺ʳ fs i))) ]′ (pf x ow np)

-- A live isle attaching: its burst in what its source still runs.
isle-att : ∀ {Γ X} {sc : Scope Γ} {Ri Ci} {k : CS Γ X} {o} (sy : Sync sc Ri Ci o (Frozen k)) → Behind Ci (Frozen k)
         → Σ (List Pos) (λ ks → ∀ {y e} → Frozen k y e → T (inside (CS.connAt k ++ [ ix 1 ]) y) → y ∈ ks)
         → (λ k′ → Σ _ λ e → Frozen k k′ e × Held Ci k k′ e) ⊑ proj₁ (husk-of sy)
isle-att {Ci = Ci} {k = k} sy (bs , bf) (fs , ff) with pin-tail sy
... | ptl ps pf = bs ++ fs ++ ps , λ (_ , x , h) → held-in {Ci = Ci} {k = k} bf ff pf x h

-- An ended isle attaching: its burst in what its source still runs.
islec-att : ∀ {Γ X} {Ci} {k : CS Γ X} {P} → TailP Ci (Frozen k) P → Behind Ci (Frozen k)
          → (λ k′ → Σ _ λ e → Frozen k k′ e × Held Ci k k′ e) ⊑ P
islec-att {Ci = Ci} (tailp ts tf) (bs , bf) = ts ++ bs , λ { {k′} (_ , x , _) →
  [ (λ ow → [ inj₁ , (λ i → inj₂ (∈-++⁺ˡ i)) ]′ (tf x ow)) , (λ no → inj₂ (∈-++⁺ʳ ts (bf x no))) ]′ (owes? Ci k′) }

-- A source no live node reads, attached: what it runs, unsubscribed
-- or not.
srch-att : ∀ {Γ X B} {sc : Scope Γ} {D} {cl sl sa p ow cx ea sr sc′} {y} {o : St Γ X} {E : EmissionSet B} {P} bb
         → Lo o (after y) → SrcH sc D (cs cl sl sa p (just y) ow cx ea sr sc′) o E P
         → Σ Pts λ P′ → SrcH sc D (cs cl sl true p nothing ow cx ea sr sc′) (proj₁ (unsubIf bb o)) E P′ × P ⊑ P′
srch-att bb lo (sh-dead hk u _) with unsubIf-husk bb hk
... | _ , h , le = _ , sh-dead h u (inj₁ tt) , under-⊑ le
srch-att {cl = cl} {sl} {sa} {p} {ow} {cx} {ea} {sr} {sc′} bb lo (sh-isle na nc sy bh sd ss (inj₁ refl) ic bu nr) with unsubIf-husk bb (proj₂ (husk-of sy))
... | _ , h , le = _ , sh-dead h (isle-up {k = k} ic (att-rows {k = k} sy bh sd lo) bu nr) (inj₁ tt)
                 , ⊑-trans (under-⊑ (isle-att {k = k} sy bh (att-fin {k = k} sy bh sd lo))) (under-⊑ le)
  where k = cs cl sl sa p (just (cx ++ [ ix 1 ])) ow cx ea sr sc′
srch-att bb lo (sh-isle _ _ _ _ _ _ (inj₂ (_ , ())) _ _ _)
srch-att {cl = cl} {sl} {sa} {p} {ow} {cx} {ea} {sr} {sc′} bb lo (sh-islec _ _ _ tp hk dm bh _ (inj₁ refl) ic bu nr) with unsubIf-husk bb hk
... | _ , h , le = _ , sh-dead h (up-pre dm (isle-up {k = k} ic (islec-rows {k = k} tp hk bh lo) bu nr)) (inj₁ tt)
                 , ⊑-trans (under-⊑ (islec-att {k = k} tp bh)) (under-⊑ le)
  where k = cs cl sl sa p (just (cx ++ [ ix 1 ])) ow cx ea sr sc′
srch-att bb lo (sh-islec _ _ _ _ _ _ _ _ (inj₂ (_ , ())) _ _ _)
srch-att bb lo (sh-pend _ _ _ () _ _ _ _ _ _ _)

-- A live source, attached.
src-att : ∀ {Γ X} {sc : Scope Γ} {Rg C} {cl sl sa p ow cx ea sr sc′} {y} {o : St Γ X}
        → Lo o (after y) → Src sc Rg C (cs cl sl sa p (just y) ow cx ea sr sc′) o → Src sc Rg C (cs cl sl true p nothing ow cx ea sr sc′) o
src-att lo (src-pend _ _ _ () _ _ _ _ _)
src-att {cl = cl} {sl} {sa} {p} {ow} {cx} {ea} {sr} {sc′} lo (src-on nc sy bh sd af ao _ lv) =
  src-on nc sy bh sd (att-now {cl = cl} {sl} {p} {ow} {cx} {ea} {sr} {sc′} sa af ao λ { refl → λ _ → att-fin {k = cs cl sl sa p (just (cx ++ [ ix 1 ])) ow cx ea sr sc′} sy bh sd lo }) (λ ()) (λ ()) lv
src-att {cl = cl} {sl} {sa} {p} {ow} {cx} {ea} {sr} {sc′} lo (src-shut cl′ sp tp hk dm bh sd ic af lv) =
  src-shut cl′ sp tp hk dm bh sd (λ ())
    (att-now {cl = cl} {sl} {p} {ow} {cx} {ea} {sr} {sc′} sa af (λ na → proj₁ (ic na))
      λ { refl → λ _ → let (ks , f) = islec-rows {k = cs cl sl sa p (just (cx ++ [ ix 1 ])) ow cx ea sr sc′} tp hk bh lo
                       in ks , λ x i → f x (in-slot cx _ i) }) lv

-- A torn connect's source, attached and stopped.
torn-att : ∀ {Γ X B} {sc : Scope Γ} {C} {cl sl sa p ow cx ea sr sc′} {y} {o : St Γ X} {b : St (X ∷ Γ) B} {β E}
         → Lo o (after y) → Torn sc C (cs cl sl sa p (just y) ow cx ea sr sc′) o b β E
         → Torn sc C (cs cl sl true p nothing ow cx ea sr sc′) (proj₁ (unsubIf true o)) b β E
torn-att lo tn with srch-att true lo (Torn.sh tn)
... | P′ , sh′ , le = record { D = Torn.D tn ; Db = Torn.Db tn ; dom = Torn.dom tn ; Ps = P′ ; Pb = Torn.Pb tn ; sh = sh′ ; bh = Torn.bh tn ; bu = Torn.bu tn
                            ; tl = tailp-⊑ (Torn.tl tn) (∪-⊑ le ⊑-refl) }

------------------------------------------------------------------------
-- A CONNECT'S OWED TEARDOWN: its body ended at a row the cursor has
-- passed (`Flags.owed`), so past it the connect owes only pins of its
-- source's burst, finitely many echoes, and what its body's isles still
-- run (`end-tail`).  Its source, stopped if attached, keeps what it runs.

-- A source torn down: what it runs, unsubscribed if attached.
srch-off : ∀ {Γ X B} {sc : Scope Γ} {D} {cl sl sa p as ow cx ea sr sc′} {o : St Γ X} {E : EmissionSet B} {P}
         → SrcH sc D (cs cl sl sa p as ow cx ea sr sc′) o E P
         → Σ Pts λ P′ → SrcH sc D (cs cl false sa p as nothing cx ea sr sc′) (proj₁ (unsubIf sa o)) E P′ × P ⊑ P′
srch-off {sa = true} (sh-dead hk u f) with unsubIf-husk true hk
... | _ , h , le = _ , sh-dead h u f , under-⊑ le
srch-off {sa = true}  (sh-isle () _ _ _ _ _ _ _ _ _)
srch-off {sa = true}  (sh-islec () _ _ _ _ _ _ _ _ _ _ _)
srch-off {sa = true}  (sh-pend () _ _ _ _ _ _ _ _ _ _)
srch-off {sa = false} (sh-dead hk u f)                              = _ , sh-dead hk u f , ⊑-refl
srch-off {sa = false} (sh-isle na nc sy bh sd ss ao ic bu nr)       = _ , sh-isle na nc sy bh sd ss ao ic bu nr , ⊑-refl
srch-off {sa = false} (sh-islec na cl sp tp hk dm bh sd ao ic bu nr) = _ , sh-islec na cl sp tp hk dm bh sd ao ic bu nr , ⊑-refl
srch-off {sa = false} (sh-pend na nc ba an sc adm pe wn ss bu nr)   = _ , sh-pend na nc ba an sc adm pe wn ss bu nr , ⊑-refl

-- A torn connect, torn again: its source stopped if attached.
torn-off : ∀ {Γ X B} {sc : Scope Γ} {C} {cl sl sa p as ow cx ea sr sc′} {o : St Γ X} {b : St (X ∷ Γ) B} {β E}
         → Torn sc C (cs cl sl sa p as ow cx ea sr sc′) o b β E
         → Torn sc C (cs cl false sa p as nothing cx ea sr sc′) (proj₁ (unsubIf sa o)) b β E
torn-off tn with srch-off (Torn.sh tn)
... | P′ , sh′ , le = record { D = Torn.D tn ; Db = Torn.Db tn ; dom = Torn.dom tn ; Ps = P′ ; Pb = Torn.Pb tn ; sh = sh′ ; bh = Torn.bh tn ; bu = Torn.bu tn
                            ; tl = tailp-⊑ (Torn.tl tn) (∪-⊑ le ⊑-refl) }

-- What a connect owes past its body's end.
owed-tl : ∀ {Γ X B} {Rb C} {k : CS Γ X} {b : St (X ∷ Γ) B} {β : EmissionSet B} {Ps P′ q}
        → (sy : Sync (binds (CS.src k) (CS.connAt k) (CS.scope k)) Rb C b β) → Sound Rb β → β q end → ¬ Owes C q
        → SrcPT C k Ps → Ps ⊑ P′ → TailP C (Connecting.ConnT (CS.connAt k) (Frozen k) β) (P′ ∪ᵖ proj₁ (husk-of sy))
owed-tl {C = C} {k = k} {β = β} {Ps = Ps} {P′} {q} sy sb qe nq (ks , fs) (ls , g) with end-tail sy sb qe nq
... | tailp kb fb = tailp (kb ++ ls ++ ks ++ cl C) row
  where
    src : ∀ {y} → Ps y ⊎ y ∈ ks → (P′ ∪ᵖ proj₁ (husk-of sy)) y ⊎ y ∈ kb ++ ls ++ ks ++ cl C
    src (inj₁ h) = [ (λ h′ → inj₁ (inj₁ h′)) , (λ i → inj₂ (∈-++⁺ʳ kb (∈-++⁺ˡ i))) ]′ (g h)
    src (inj₂ i) = inj₂ (∈-++⁺ʳ kb (∈-++⁺ʳ ls (∈-++⁺ˡ i)))

    row : ∀ {y e} → Connecting.ConnT (CS.connAt k) (Frozen k) β y e → Owes C y → (P′ ∪ᵖ proj₁ (husk-of sy)) y ⊎ y ∈ kb ++ ls ++ ks ++ cl C
    row (Connecting.body x) o = [ (λ h → inj₁ (inj₂ h)) , (λ i → inj₂ (∈-++⁺ˡ i)) ]′ (fb x o)
    row (Connecting.burst x ins) o = src (fs x (inj₁ ins) o)
    row (Connecting.echo {y} x al _ _) o with owes? C y
    ... | inj₁ oy = ⊥-elim (nq (owes-≼ C oy (≺→≼ {y} {q} (al qe))))
    ... | inj₂ ny = inj₂ (∈-++⁺ʳ kb (∈-++⁺ʳ ls (∈-++⁺ʳ ks (nxt C ny o))))
    row (Connecting.kept {p′ = p′} x al _ _) o = src (fs x (inj₂ (_ , refl , λ op → nq (owes-≼ C op (≺→≼ {p′} {q} (al qe))))) o)

-- A body's run finds no attach owed in it: the body's every attach is
-- keyed after its own run, and no mark of the tree is keyed before it.
body-noisle : ∀ {R Γ A X} (c : Ctx R Γ A) {k : CS Γ X} {o : St Γ X} {b : St (X ∷ Γ) A} {p}
            → StOK (connS k o b) → G (connS k o b) → CS.bodyAt k ≡ just p → Lo (plug c (connS k o b)) (at (p ++ [ ix 1 ])) → NoIsle b
body-noisle c {b = b} {p} (_ , _ , hb , _) (_ , ua , _ , gb) e lo = noatt-noisle b hb gb na
  where
    na : NoAttB b
    na a = at-after-≮ (p ++ [ ix 1 ]) _ (proj₂ (ua a) e) (lo (plug-in c (k-kid (k-body (att-key a)))))

or-right : ∀ a {b} → T (not a) → T (a ∨ b) → T b
or-right false _ t = t

and-right : ∀ a {b} → T (a ∧ b) → T b
and-right true t = t

and-left : ∀ a {b} → T (a ∧ b) → T a
and-left true _ = tt

-- Under a closed context nothing is owed: only a connect's ended
-- source or a switched-off lane closes one, and both are parts no live
-- node reads, or a source not yet subscribed.
Off : Need → Set
Off owes          = ⊥
Off (dead _ _)    = ⊤
Off (lane _ _ _)  = ⊥
Off (lanecut _ _ _) = ⊥
Off (pnd _)       = ⊤

-- A live connect's parts close only with what is above it.
live-or : ∀ b {x} → T b → T (not b ∨ x) → T x
live-or true _ t = t

module _ {R : Set} (Rt : EmissionSet R) where

  closed-off : ∀ {Cr C Γ A} {c : Ctx R Γ A} {Rg N E} → Fr Rt Cr C Rg c N E → T (closed c) → Off N
  closed-off (f-top _)                                           ()
  closed-off (f-map fr _ _)                                      t = closed-off fr t
  closed-off (f-scan fr _ _ _)                                   t = closed-off fr t
  closed-off (f-cut fr)                                          t = closed-off fr t
  closed-off (f-take fr _ _ _)                                   t = closed-off fr t
  closed-off (f-took _ _ _ _ _ _ _ _ _ _)                            _ = tt
  closed-off (f-outer fr _ _ _ _ _)                              t = closed-off fr t
  closed-off (f-lanes fr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) t = closed-off fr t
  closed-off (f-lane fr)                                         t = closed-off fr t
  closed-off (f-lnct {b = true} fr)                              t = closed-off fr t
  closed-off (f-lnct {b = false} fr)                             _ = tt
  closed-off (f-src {k = k} fr _ _ lv nc _ _ _ _ _ _ _ _ _ _ _)  t = closed-off fr (live-or (CS.srcLive k) lv (and-right (CS.srcAtt k) (or-right (CS.closed k) nc t)))
  closed-off (f-srcc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)                  _ = tt
  closed-off (f-srcp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)              _ = tt
  closed-off (f-body {k = k} fr _ _ lv _ _ _ _)                  t = closed-off fr (live-or (CS.srcLive k) lv t)
  closed-off (d-map _ _)                                           _ = tt
  closed-off (d-scan _ _)                                          _ = tt
  closed-off (d-cut _ _)                                           _ = tt
  closed-off (d-ln _ _)                                            _ = tt
  closed-off (d-take _ _)                                          _ = tt
  closed-off (d-outer _ _ _ _)                                     _ = tt
  closed-off (d-lanes _ _ _ _ _ _ _)                                 _ = tt
  closed-off (d-src _ _ _ _ _ _ _)                                   _ = tt
  closed-off (d-body _ _ _ _)                                      _ = tt
  closed-off (f-isle {k = k} _ _ _ _ na nc _ _ _ _ _ _ _ _)      t = ⊥-elim (notT _ na (and-left (CS.srcAtt k) (or-right (CS.closed k) nc t)))
  closed-off (f-islec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)                         _ = tt
  closed-off (f-islep {k = k} _ _ _ _ na nc _ _ _ _ _ _ _ _)     t = ⊥-elim (notT _ na (and-left (CS.srcAtt k) (or-right (CS.closed k) nc t)))

  -- What a body's run reaches.
  Ran : Cur → Conf R → Set₁
  Ran Cr k′ = Σ Cur λ Cr′ → Σ Cur λ C′ → Inv Rt Cr′ C′ k′ × Moves (RT Rt Cr) [] (RT Rt Cr′)

  -- A SOURCE IN A PART NO LIVE NODE READS, subscribed by its body's run:
  -- not yet subscribed, an isle born at its own cursor there; otherwise
  -- what it was.
  unread-body : ∀ {Cr C D Db Γ X B} {c : Ctx R Γ B} {cl sl sa p as ow cx ea sr sc} {o₀ q} {b : St (X ∷ Γ) B} {E β : EmissionSet B} {P Ps Qb}
              → Unread Rt Cr C D E β c (cs cl sl sa nothing (just (p ++ [ ix 1 ])) ow cx ea sr sc) P
              → SrcH (scopeOf c) D (cs cl sl sa (just p) as ow cx ea sr sc) (pend o₀ q) E Ps
              → Husk (binds sr cx sc) Db b β Qb → Up Db β D E → P ⊑ (Ps ∪ᵖ Qb) → NoIsle b
              → Ran Cr ⟨ inSrc (cs cl sl sa nothing (just (p ++ [ ix 1 ])) ow cx ea sr sc) b c , pend o₀ q , subscribing , p ++ [ ix 1 ] ⟩
  unread-body {Cr} {C} {cl = cl} {sl} {sa} {p} {as} {ow} {cx} {ea} {sr} {sc} un (sh-pend na nc refl _ scp (ok , adm) pe wn ss bu nr) hb ub le nb =
    Cr , bef (cx ++ [ ix 1 ]) ,
    pending (f-isle un hb ub le na nc (behind-pend {C = bef (cx ++ [ ix 1 ])} {k = k} scp (ok , adm) (≼-refl {cx ++ [ ix 1 ]})) (subd (λ o → o) ok) ss (inj₁ refl)
                    (owes-call {k = k} (bef (cx ++ [ ix 1 ])) (≼-refl {cx ++ [ ix 1 ]})) bu nr nb)
            (≼-refl {cx ++ [ ix 1 ]} , ok-step cx ok , adm , pe , wn) ,
    silent ≃-refl
    where k = cs cl sl sa nothing (just (p ++ [ ix 1 ])) ow cx ea sr sc
  unread-body un (sh-dead (h-blank ()) _ _) hb ub le nb
  unread-body un (sh-isle _ _ sy _ _ _ _ _ _ _) hb ub le nb = ⊥-elim (sync-pend tt sy)
  unread-body un (sh-islec _ _ _ _ (h-blank ()) _ _ _ _ _ _ _) hb ub le nb

  -- THE BODY'S RUN.  A live source owed at the connect's `ix 1` is the
  -- new hole, every frame shifted to just before it, its mark being the
  -- tree's least; an ended one is left to its husk; a torn-down one, or
  -- one in a part no live node reads, is `unread-body`'s.
  con-body : ∀ {Cr C Γ X B} {c : Ctx R Γ B} {cl sl sa p as ow cx ea sr sc} {o₀ q} {b : St (X ∷ Γ) B} {r}
           → NoIsle b → Lo (plug c (connS (cs cl sl sa (just p) as ow cx ea sr sc) (pend o₀ q) b)) (at (p ++ [ ix 1 ]))
           → Inv Rt Cr C ⟨ c , connS (cs cl sl sa (just p) as ow cx ea sr sc) (pend o₀ q) b , absorbed , r ⟩
           → Ran Cr ⟨ inSrc (cs cl sl sa nothing (just (p ++ [ ix 1 ])) ow cx ea sr sc) b c , pend o₀ q , subscribing , p ++ [ ix 1 ] ⟩
  con-body {sl = true} {cx = cx} nb lo (settled {N = owes} c-abs fr sy@(s-conn scp pt bs bb ss tn fl eq)) with ss tt
  ... | src-on _ sy′ _ _ _ _ _ _ = ⊥-elim (sync-pend tt sy′)
  ... | src-shut _ _ _ (h-blank ()) _ _ _ _ _ _
  ... | src-pend _ nc₀ refl _ _ _ _ ow _ with fr-shift Rt fr sy ow lo
  ...   | Cr′ , fr′ , s-conn scp′ pt′ bs′ bb′ ss′ _ fl′ eq′ , d with ss′ tt
  ...     | src-on _ sy′ _ _ _ _ _ _ = ⊥-elim (sync-pend tt sy′)
  ...     | src-shut cl′ _ _ _ _ _ _ _ _ _ = ⊥-elim (notT _ nc₀ cl′)
  ...     | src-pend {k = k} na nc refl _ (ok , adm) pe wn _ _ =
    Cr′ , bef (cx ++ [ ix 1 ]) ,
    pending (f-src fr′ scp′ (re-parts refl refl pt′) tt nc (bs′ tt) (bb′ tt) (re-flags fl′) ≈-refl eq′
                   (behind-pend {C = bef (cx ++ [ ix 1 ])} {k = k} scp′ (ok , adm) (≼-refl {cx ++ [ ix 1 ]})) (subd (λ o → o) ok)
                   (λ t → ⊥-elim (notT _ na t)) (λ _ → inj₁ refl) (λ _ → owes-call {k = k} (bef (cx ++ [ ix 1 ])) (≼-refl {cx ++ [ ix 1 ]})) nb)
            (≼-refl {cx ++ [ ix 1 ]} , ok-step cx ok , adm , pe , wn) ,
    silent (vis-≃ d)
  con-body {sl = false} nb lo (settled {N = owes} c-abs fr (s-conn scp pt bs _ ss tn fl eq)) =
    unread-body (un-torn fr scp (re-parts refl refl pt) tt (re-flags fl) eq (Torn.tl (tn tt)) (Torn.dom (tn tt))) (Torn.sh (tn tt)) (Torn.bh (tn tt)) (Torn.bu (tn tt)) ⊑-refl nb
  con-body nb lo (settled {N = dead _ _} c-abs fr (_ , h-blank (_ , () , _) , le))
  con-body nb lo (settled {N = dead _ _} c-abs fr (_ , h-conn sh hb u , le)) = unread-body (un-dead fr) sh hb u le nb
  con-body nb lo (settled {N = lane _ _ _} c-abs fr (_ , _ , () , _))
  con-body nb lo (settled {N = lanecut _ _ _} c-abs fr (_ , _ , () , _))
  con-body nb lo (settled {N = pnd _} c-abs fr (_ , () , _))

  -- THE SOURCE'S ATTACH.  Live, under a context no close has reached,
  -- its source is left running; torn down, it is stopped; in a part no
  -- live node reads, either.
  con-att : ∀ {Cr C Γ X B} {c : Ctx R Γ B} {cl sl sa p ow cx ea sr sc} {y} {o : St Γ X} {b : St (X ∷ Γ) B} {r}
          → Lo o (after y)
          → Inv Rt Cr C ⟨ c , connS (cs cl sl sa p (just y) ow cx ea sr sc) o b , absorbed , r ⟩
          → Ran Cr ⟨ c , connS (cs cl sl true p nothing ow cx ea sr sc) (proj₁ (unsubIf (not sl ∨ closed c) o)) b , absorbed , y ⟩
  con-att {Cr} {C} {c = c} {sl = true} lo (settled {N = owes} c-abs fr (s-conn scp pt bs bb ss tn fl eq)) with closed c | closed-off fr
  ... | true  | off = ⊥-elim (off tt)
  ... | false | _   =
    Cr , C , settled c-abs fr (s-conn scp (re-parts refl refl pt) bs bb (λ t → src-att lo (ss t)) (λ ()) (re-flags fl) eq) , silent ≃-refl
  con-att {Cr} {C} {sl = false} lo (settled {N = owes} c-abs fr (s-conn scp pt bs _ ss tn fl eq)) =
    Cr , C , settled c-abs fr (s-conn scp (re-parts refl refl pt) (λ ()) (λ ()) (λ ()) (λ t → torn-att lo (tn t)) (re-flags fl) eq) , silent ≃-refl
  con-att {Cr} {C} {c = c} {sl = sl} {o = o} lo (settled {N = dead _ _} c-abs fr (_ , h-blank (_ , qo , qb) , le)) =
    Cr , C , settled c-abs fr (_ , h-blank (inj₁ tt , quiet-unsubIf (not sl ∨ closed c) {s = o} qo , qb) , le) , silent ≃-refl
  con-att {Cr} {C} {c = c} {sl = sl} lo (settled {N = dead _ _} c-abs fr (_ , h-conn sh hb u , le)) with srch-att (not sl ∨ closed c) lo sh
  ... | _ , sh′ , le′ = Cr , C , settled c-abs fr (_ , h-conn sh′ hb u , ⊑-trans le (∪-⊑ le′ ⊑-refl)) , silent ≃-refl
  con-att lo (settled {N = lane _ _ _} c-abs fr (_ , _ , () , _))
  con-att lo (settled {N = lanecut _ _ _} c-abs fr (_ , _ , () , _))
  con-att lo (settled {N = pnd _} c-abs fr (_ , () , _))

  -- THE OWED TEARDOWN.  Live, its source is torn down with it, its body
  -- spent; already torn, its source is stopped if attached; in a part no
  -- live node reads, either.
  con-owed : ∀ {Cr C Γ X B} {c : Ctx R Γ B} {cl sl sa p as cx ea sr sc} {q} {o : St Γ X} {b : St (X ∷ Γ) B} {r}
           → Inv Rt Cr C ⟨ c , connS (cs cl sl sa p as (just q) cx ea sr sc) o b , absorbed , r ⟩
           → Ran Cr ⟨ c , connS (cs cl false sa p as nothing cx ea sr sc) (proj₁ (unsubIf sa o)) b , absorbed , q ⟩
  con-owed {Cr} {C} {cl = cl} {sl = true} {sa} {p} {as} {cx} {ea} {sr} {sc} (settled {N = owes} c-abs fr (s-conn refl pt bs bb ss tn fl eq)) =
    Cr , C , settled c-abs fr (s-conn refl (re-parts refl refl pt) (λ ()) (λ ()) (λ ()) (λ _ → tn′)
      (record { shut = Flags.shut fl ; unshut = λ () ; owed = λ () ; ended = λ () ; owing = λ ()
              ; torn = λ _ (x , v , o) → proj₂ (Flags.owed fl refl) (owes-≼ C o (Sound.ends (Parts.sb pt) (proj₁ (Flags.owed fl refl)) x v)) }) eq) ,
    silent ≃-refl
    where
      srh = src-husk refl pt (ss tt) (bb tt) fl eq
      off = srch-off (proj₂ srh)
      tn′ = record { D = C ; Db = C ; dom = λ t → t ; Ps = proj₁ off ; Pb = proj₁ (husk-of (bs tt)) ; sh = proj₁ (proj₂ off) ; bh = proj₂ (husk-of (bs tt))
                   ; bu = conn-up-body refl pt (ss tt) (bb tt) fl eq
                   ; tl = owed-tl {k = cs cl false sa p as nothing cx ea sr sc} (bs tt) (Parts.sb pt) (proj₁ (Flags.owed fl refl)) (proj₂ (Flags.owed fl refl)) (src-pt pt (ss tt) (bb tt) fl eq) (proj₂ (proj₂ off)) }
  con-owed {Cr} {C} {sl = false} (settled {N = owes} c-abs fr (s-conn scp pt bs _ ss tn fl eq)) =
    Cr , C , settled c-abs fr (s-conn scp (re-parts refl refl pt) (λ ()) (λ ()) (λ ()) (λ t → torn-off (tn t))
      (record { shut = Flags.shut fl ; unshut = λ () ; torn = Flags.torn fl ; owed = λ () ; ended = λ () ; owing = λ () }) eq) ,
    silent ≃-refl
  con-owed {Cr} {C} {sa = sa} {o = o} (settled {N = dead _ _} c-abs fr (_ , h-blank (f , qo , qb) , le)) =
    Cr , C , settled c-abs fr (_ , h-blank (f , quiet-unsubIf sa {s = o} qo , qb) , le) , silent ≃-refl
  con-owed {Cr} {C} (settled {N = dead _ _} c-abs fr (_ , h-conn sh hb u , le)) with srch-off sh
  ... | _ , sh′ , le′ = Cr , C , settled c-abs fr (_ , h-conn sh′ hb u , ⊑-trans le (∪-⊑ le′ ⊑-refl)) , silent ≃-refl
  con-owed (settled {N = lane _ _ _} c-abs fr (_ , _ , () , _))
  con-owed (settled {N = lanecut _ _ _} c-abs fr (_ , _ , () , _))
  con-owed (settled {N = pnd _} c-abs fr (_ , () , _))
