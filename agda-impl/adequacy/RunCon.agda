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
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import denotation.Events using (Pos; ix; inside)
open import denotation.EmissionSet using (EmissionSet; pin; end; module Connecting)
open import denotation.Laws.Modulus using (≼-refl; ≺→≼)
open import denotation.Laws.Worlds using (ok-step)
open import operation.Key using (at; after; at-after-≮)
open import operation.PureObservable using (module Machine)
open Machine using (St; Ctx; Conf; Scope; ⟨_,_,_,_⟩; subscribing; absorbed; moved; plug; run; own; CS; cs; bodyM; srcAttM; owedM;
                    pend; connS; inSrc; scopeOf; binds; closed; unsubIf)
open import adequacy.Rows using (Frozen; ≃-refl; Vis; _≃_; _⇄_; silent; Moves)
open _≃_
open import adequacy.Cursor using (Cur; bef; Owes; Behind; Pts; Held; AttFin; AttOwed; TailP; tailp; Src; Sync; Subd; husk-of;
  src-husk; re-parts; unsubIf-husk; under-⊑; tailp-⊑; ∪-⊑; Parts; Flags; Sound; Husk; SrcH;
  Unread; NoIsle; _∪ᵖ_; _⊑_; ∅ᵖ; ∅-⊑; ⊑-refl; ⊑-trans; h-blank; h-conn; sh-dead; sh-isle;
  sh-islec; sh-pend; src-pend; src-on; src-shut; s-conn; Torn; un-dead; un-torn; owes; dead;
  lane; lanecut; pnd; c-abs; c-sub; ≈-refl; notT; sync-pend; subd; Need; Fr; f-top; f-map;
  f-scan; f-cut; f-take; f-took; f-outer; f-lanes; f-lane; f-lnct; f-src; f-srcc; f-srcp;
  f-isle; f-islec; f-islep; f-body; d-map; d-scan; d-cut; d-ln; d-take; d-outer; d-lanes;
  d-src; d-body)
open import adequacy.Cursor.Rise using (Inv; settled; pending; RT)
open import adequacy.Least using (Lo; k-kid; k-body)
open import adequacy.Floor.Keys using (plug-in)
open import adequacy.Bound using (behind-pend; owes?; owes-≼; lo-att; in-slot)
open import adequacy.Few using (fr-shift; few; before; subd-env; nxt; cl)
open import adequacy.PinTail using (pin-tail; ptl; end-tail; SrcPT; src-pt)
open import adequacy.Walk using (nowhere; none′)
open import adequacy.Stamped using (StOK)
open import adequacy.Isle using (G; NoAttB; att-key; noatt-noisle)

-- What the root owes, moved row for row.
vis-≃ : ∀ {A} {E E′ : EmissionSet A} → E ≃ E′ → Vis E ≃ Vis E′
vis-≃ d = (λ (x , v) → to d x , v) ⇄ (λ (x , v) → from d x , v)

-- A connect's flags read again under fields they do not read.
re-flags : ∀ {Γ X B} {C} {cl sl sa p as ow cx ea sr sc sa′ p′ as′} {β : EmissionSet B}
         → Flags C (cs {Γ} {X} cl sl sa p as ow cx ea sr sc) β → Flags C (cs cl sl sa′ p′ as′ ow cx ea sr sc) β
re-flags fl = record { shut = Flags.shut fl ; unshut = Flags.unshut fl ; torn = Flags.torn fl ; owed = Flags.owed fl }

------------------------------------------------------------------------
-- A SOURCE'S ATTACH: its subscribe call has returned, so every key
-- inside it has run, and a source that ran in step through it has only
-- finitely many rows inside it.  An isle attaching leaves its burst to
-- what its source still runs: a row its cursor owes either inside the
-- call, a pin its husk holds, or one of finitely many.

-- A source in step up to its attach: finitely many of its rows inside
-- its subscribe call.
att-fin : ∀ {Γ X} {sc : Scope Γ} {Rg C} {k : CS Γ X} {o} → Sync sc Rg C o (Frozen k) → Behind C (Frozen k) → Subd sc C k
        → Lo o (after (CS.connAt k ++ [ ix 1 ]))
        → Σ (List Pos) λ ks → ∀ {y e} → Frozen k y e → T (inside (CS.connAt k ++ [ ix 1 ]) y) → y ∈ ks
att-fin {C = C} {k = k} sy bh sd lo with subd-env {k = k} {p = CS.connAt k ++ [ ix 2 ]} sd (≼-refl {CS.connAt k ++ [ ix 2 ]})
... | env , envl with before {C = C} {E = Frozen k} bh (few sy env envl (lo-att lo))
...   | ks , f = ks , λ x i → f x (in-slot (CS.connAt k) _ i)

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
srch-att : ∀ {Γ X} {sc : Scope Γ} {cl sl sa p ow cx ea sr sc′} {y} {o : St Γ X} {P} bb
         → Lo o (after y) → SrcH sc (cs cl sl sa p (just y) ow cx ea sr sc′) o P
         → Σ Pts λ P′ → SrcH sc (cs cl sl true p nothing ow cx ea sr sc′) (proj₁ (unsubIf bb o)) P′ × P ⊑ P′
srch-att bb lo (sh-dead hk) with unsubIf-husk bb hk
... | _ , h , le = _ , sh-dead h , under-⊑ le
srch-att {cl = cl} {sl} {sa} {p} {ow} {cx} {ea} {sr} {sc′} bb lo (sh-isle na nc sy bh sd ss (inj₁ refl)) with unsubIf-husk bb (proj₂ (husk-of sy))
... | _ , h , le = _ , sh-dead h , ⊑-trans (under-⊑ (isle-att {k = k} sy bh (att-fin {k = k} sy bh sd lo))) (under-⊑ le)
  where k = cs cl sl sa p (just (cx ++ [ ix 1 ])) ow cx ea sr sc′
srch-att bb lo (sh-isle _ _ _ _ _ _ (inj₂ (_ , ())))
srch-att {cl = cl} {sl} {sa} {p} {ow} {cx} {ea} {sr} {sc′} {y} bb lo (sh-islec _ _ _ tp hk bh _) with unsubIf-husk bb hk
... | _ , h , le = _ , sh-dead h , ⊑-trans (under-⊑ (islec-att {k = cs cl sl sa p (just y) ow cx ea sr sc′} tp bh)) (under-⊑ le)
srch-att bb lo (sh-pend _ _ _ () _ _ _ _ _)

-- A live source, attached.
src-att : ∀ {Γ X} {sc : Scope Γ} {Rg C} {cl sl sa p ow cx ea sr sc′} {y} {o : St Γ X}
        → Lo o (after y) → Src sc Rg C (cs cl sl sa p (just y) ow cx ea sr sc′) o → Src sc Rg C (cs cl sl true p nothing ow cx ea sr sc′) o
src-att lo (src-pend _ _ _ () _ _ _ _)
src-att {cl = cl} {sl} {sa} {p} {ow} {cx} {ea} {sr} {sc′} lo (src-on nc sy bh sd af ao) =
  src-on nc sy bh sd (att-now {cl = cl} {sl} {p} {ow} {cx} {ea} {sr} {sc′} sa af ao λ { refl → λ _ → att-fin {k = cs cl sl sa p (just (cx ++ [ ix 1 ])) ow cx ea sr sc′} sy bh sd lo }) (λ ())
src-att lo (src-shut cl sp tp hk bh sd) = src-shut cl sp tp hk bh sd

-- A torn connect's source, attached and stopped.
torn-att : ∀ {Γ X B} {sc : Scope Γ} {C} {cl sl sa p ow cx ea sr sc′} {y} {o : St Γ X} {b : St (X ∷ Γ) B} {β}
         → Lo o (after y) → Torn sc C (cs cl sl sa p (just y) ow cx ea sr sc′) o b β
         → Torn sc C (cs cl sl true p nothing ow cx ea sr sc′) (proj₁ (unsubIf true o)) b β
torn-att lo tn with srch-att true lo (Torn.sh tn)
... | P′ , sh′ , le = record { Ps = P′ ; Pb = Torn.Pb tn ; sh = sh′ ; bh = Torn.bh tn ; tl = tailp-⊑ (Torn.tl tn) (∪-⊑ le ⊑-refl) }

------------------------------------------------------------------------
-- A CONNECT'S OWED TEARDOWN: its body ended at a row the cursor has
-- passed (`Flags.owed`), so past it the connect owes only pins of its
-- source's burst, finitely many echoes, and what its body's isles still
-- run (`end-tail`).  Its source, stopped if attached, keeps what it runs.

-- A source torn down: what it runs, unsubscribed if attached.
srch-off : ∀ {Γ X} {sc : Scope Γ} {cl sl sa p as ow cx ea sr sc′} {o : St Γ X} {P}
         → SrcH sc (cs cl sl sa p as ow cx ea sr sc′) o P
         → Σ Pts λ P′ → SrcH sc (cs cl false sa p as nothing cx ea sr sc′) (proj₁ (unsubIf sa o)) P′ × P ⊑ P′
srch-off {sa = true} (sh-dead hk) with unsubIf-husk true hk
... | _ , h , le = _ , sh-dead h , under-⊑ le
srch-off {sa = true}  (sh-isle () _ _ _ _ _ _)
srch-off {sa = true}  (sh-islec () _ _ _ _ _ _)
srch-off {sa = true}  (sh-pend () _ _ _ _ _ _ _ _)
srch-off {sa = false} (sh-dead hk)                          = _ , sh-dead hk , ⊑-refl
srch-off {sa = false} (sh-isle na nc sy bh sd ss ao)        = _ , sh-isle na nc sy bh sd ss ao , ⊑-refl
srch-off {sa = false} (sh-islec na cl sp tp hk bh sd)       = _ , sh-islec na cl sp tp hk bh sd , ⊑-refl
srch-off {sa = false} (sh-pend na nc ba an sc adm pe wn ss) = _ , sh-pend na nc ba an sc adm pe wn ss , ⊑-refl

-- A torn connect, torn again: its source stopped if attached.
torn-off : ∀ {Γ X B} {sc : Scope Γ} {C} {cl sl sa p as ow cx ea sr sc′} {o : St Γ X} {b : St (X ∷ Γ) B} {β}
         → Torn sc C (cs cl sl sa p as ow cx ea sr sc′) o b β
         → Torn sc C (cs cl false sa p as nothing cx ea sr sc′) (proj₁ (unsubIf sa o)) b β
torn-off tn with srch-off (Torn.sh tn)
... | P′ , sh′ , le = record { Ps = P′ ; Pb = Torn.Pb tn ; sh = sh′ ; bh = Torn.bh tn ; tl = tailp-⊑ (Torn.tl tn) (∪-⊑ le ⊑-refl) }

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
body-noisle c {b = b} {p} (_ , _ , hb , _) (_ , up , _ , gb) e lo = noatt-noisle b hb gb na
  where
    na : NoAttB b
    na a = at-after-≮ (p ++ [ ix 1 ]) _ (proj₂ (up a) e) (lo (plug-in c (k-kid (k-body (att-key a)))))

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
Off (dead _)      = ⊤
Off (lane _ _)    = ⊥
Off (lanecut _ _) = ⊥
Off (pnd _)       = ⊤

module _ {R : Set} (Rt : EmissionSet R) where

  closed-off : ∀ {Cr C Γ A} {c : Ctx R Γ A} {Rg N E} → Fr Rt Cr C Rg c N E → T (closed c) → Off N
  closed-off (f-top _)                                           ()
  closed-off (f-map fr _ _)                                      t = closed-off fr t
  closed-off (f-scan fr _ _ _)                                   t = closed-off fr t
  closed-off (f-cut fr)                                          t = closed-off fr t
  closed-off (f-take fr _ _ _)                                   t = closed-off fr t
  closed-off (f-took _ _ _ _ _ _ _ _)                            _ = tt
  closed-off (f-outer fr _ _ _ _ _)                              t = closed-off fr t
  closed-off (f-lanes fr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) t = closed-off fr t
  closed-off (f-lane fr)                                         t = closed-off fr t
  closed-off (f-lnct {b = true} fr)                              t = closed-off fr t
  closed-off (f-lnct {b = false} fr)                             _ = tt
  closed-off (f-src {k = k} fr _ _ _ nc _ _ _ _ _ _ _ _ _)       t = closed-off fr (and-right (CS.srcAtt k) (or-right (CS.closed k) nc t))
  closed-off (f-srcc _ _ _ _ _ _ _ _ _ _ _ _)                    _ = tt
  closed-off (f-srcp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)                _ = tt
  closed-off (f-body fr _ _ _ _ _ _)                             t = closed-off fr t
  closed-off (d-map _)                                           _ = tt
  closed-off (d-scan _)                                          _ = tt
  closed-off (d-cut _)                                           _ = tt
  closed-off (d-ln _)                                            _ = tt
  closed-off (d-take _)                                          _ = tt
  closed-off (d-outer _ _ _)                                     _ = tt
  closed-off (d-lanes _ _ _ _ _)                                 _ = tt
  closed-off (d-src _ _ _ _)                                     _ = tt
  closed-off (d-body _ _ _)                                      _ = tt
  closed-off (f-isle {k = k} _ _ _ na nc _ _ _ _ _)              t = ⊥-elim (notT _ na (and-left (CS.srcAtt k) (or-right (CS.closed k) nc t)))
  closed-off (f-islec _ _ _ _ _ _ _ _ _)                         _ = tt
  closed-off (f-islep {k = k} _ _ _ na nc _ _ _ _ _ _)            t = ⊥-elim (notT _ na (and-left (CS.srcAtt k) (or-right (CS.closed k) nc t)))

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
  unread-body {Cr} {C} {cl = cl} {sl} {sa} {p} {as} {ow} {cx} {ea} {sr} {sc} un (sh-pend na nc refl _ scp (ok , adm) pe wn ss) hb le nb =
    Cr , bef (cx ++ [ ix 1 ]) ,
    pending (f-isle un hb le na nc (behind-pend {C = bef (cx ++ [ ix 1 ])} {k = cs cl sl sa nothing (just (p ++ [ ix 1 ])) ow cx ea sr sc} scp (ok , adm) (≼-refl {cx ++ [ ix 1 ]})) (subd (λ o → o) ok) ss (inj₁ refl) nb)
            (≼-refl {cx ++ [ ix 1 ]} , ok-step cx ok , adm , pe , wn) ,
    silent ≃-refl
  unread-body {Cr} {C} un (sh-dead hk) hb le nb = Cr , C , settled {Rg = nowhere} {E = none′} c-sub (d-src un hb le nb) (_ , hk , ⊑-refl) , silent ≃-refl
  unread-body un (sh-isle _ _ sy _ _ _ _) hb le nb = ⊥-elim (sync-pend tt sy)
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
  ... | src-on _ sy′ _ _ _ _ = ⊥-elim (sync-pend tt sy′)
  ... | src-shut cl′ sp tp hk bh sd =
    _ , _ , settled {Rg = nowhere} {E = none′} c-sub (f-srcc fr scp (re-parts refl pt) tt cl′ sp tp bh sd (bs tt) (re-flags fl) eq) (_ , hk , ⊑-refl) , silent ≃-refl
  ... | src-pend _ nc₀ refl _ _ _ _ ow with fr-shift Rt fr sy ow lo
  ...   | Cr′ , fr′ , s-conn scp′ pt′ bs′ ss′ _ fl′ eq′ , d with ss′ tt
  ...     | src-on _ sy′ _ _ _ _ = ⊥-elim (sync-pend tt sy′)
  ...     | src-shut cl′ _ _ _ _ _ = ⊥-elim (notT _ nc₀ cl′)
  ...     | src-pend {k = k} na nc refl _ (ok , adm) pe wn _ =
    Cr′ , bef (cx ++ [ ix 1 ]) ,
    pending (f-src fr′ scp′ (re-parts refl pt′) tt nc (bs′ tt) (re-flags fl′) ≈-refl eq′
                   (behind-pend {C = bef (cx ++ [ ix 1 ])} {k = k} scp′ (ok , adm) (≼-refl {cx ++ [ ix 1 ]})) (subd (λ o → o) ok)
                   (λ t → ⊥-elim (notT _ na t)) (λ _ → inj₁ refl) nb)
            (≼-refl {cx ++ [ ix 1 ]} , ok-step cx ok , adm , pe , wn) ,
    silent (vis-≃ d)
  con-body {sl = false} nb lo (settled {N = owes} c-abs fr (s-conn scp pt bs ss tn fl eq)) =
    unread-body (un-torn fr scp (re-parts refl pt) tt (re-flags fl) eq (Torn.tl (tn tt))) (Torn.sh (tn tt)) (Torn.bh (tn tt)) ⊑-refl nb
  con-body {Cr} {C} nb lo (settled {N = dead _} c-abs fr (_ , h-blank , le)) =
    Cr , C , settled {Rg = nowhere} {E = none′} c-sub (d-src {N = ∅ᵖ} (un-dead fr) h-blank (⊑-trans le ∅-⊑) nb) (∅ᵖ , h-blank , ⊑-refl) , silent ≃-refl
  con-body nb lo (settled {N = dead _} c-abs fr (_ , h-conn sh hb , le)) = unread-body (un-dead fr) sh hb le nb
  con-body nb lo (settled {N = lane _ _} c-abs fr (_ , _ , () , _))
  con-body nb lo (settled {N = lanecut _ _} c-abs fr (_ , _ , () , _))
  con-body nb lo (settled {N = pnd _} c-abs fr (_ , () , _))

  -- THE SOURCE'S ATTACH.  Live, under a context no close has reached,
  -- its source is left running; torn down, it is stopped; in a part no
  -- live node reads, either.
  con-att : ∀ {Cr C Γ X B} {c : Ctx R Γ B} {cl sl sa p ow cx ea sr sc} {y} {o : St Γ X} {b : St (X ∷ Γ) B} {r}
          → Lo o (after y)
          → Inv Rt Cr C ⟨ c , connS (cs cl sl sa p (just y) ow cx ea sr sc) o b , absorbed , r ⟩
          → Ran Cr ⟨ c , connS (cs cl sl true p nothing ow cx ea sr sc) (proj₁ (unsubIf (not sl ∨ closed c) o)) b , absorbed , y ⟩
  con-att {Cr} {C} {c = c} {sl = true} lo (settled {N = owes} c-abs fr (s-conn scp pt bs ss tn fl eq)) with closed c | closed-off fr
  ... | true  | off = ⊥-elim (off tt)
  ... | false | _   =
    Cr , C , settled c-abs fr (s-conn scp (re-parts refl pt) bs (λ t → src-att lo (ss t)) (λ ()) (re-flags fl) eq) , silent ≃-refl
  con-att {Cr} {C} {sl = false} lo (settled {N = owes} c-abs fr (s-conn scp pt bs ss tn fl eq)) =
    Cr , C , settled c-abs fr (s-conn scp (re-parts refl pt) (λ ()) (λ ()) (λ t → torn-att lo (tn t)) (re-flags fl) eq) , silent ≃-refl
  con-att {Cr} {C} lo (settled {N = dead _} c-abs fr (_ , h-blank , le)) = Cr , C , settled c-abs fr (_ , h-blank , le) , silent ≃-refl
  con-att {Cr} {C} {c = c} {sl = sl} lo (settled {N = dead _} c-abs fr (_ , h-conn sh hb , le)) with srch-att (not sl ∨ closed c) lo sh
  ... | _ , sh′ , le′ = Cr , C , settled c-abs fr (_ , h-conn sh′ hb , ⊑-trans le (∪-⊑ le′ ⊑-refl)) , silent ≃-refl
  con-att lo (settled {N = lane _ _} c-abs fr (_ , _ , () , _))
  con-att lo (settled {N = lanecut _ _} c-abs fr (_ , _ , () , _))
  con-att lo (settled {N = pnd _} c-abs fr (_ , () , _))

  -- THE OWED TEARDOWN.  Live, its source is torn down with it, its body
  -- spent; already torn, its source is stopped if attached; in a part no
  -- live node reads, either.
  con-owed : ∀ {Cr C Γ X B} {c : Ctx R Γ B} {cl sl sa p as cx ea sr sc} {q} {o : St Γ X} {b : St (X ∷ Γ) B} {r}
           → Inv Rt Cr C ⟨ c , connS (cs cl sl sa p as (just q) cx ea sr sc) o b , absorbed , r ⟩
           → Ran Cr ⟨ c , connS (cs cl false sa p as nothing cx ea sr sc) (proj₁ (unsubIf sa o)) b , absorbed , q ⟩
  con-owed {Cr} {C} {cl = cl} {sl = true} {sa} {p} {as} {cx} {ea} {sr} {sc} (settled {N = owes} c-abs fr (s-conn refl pt bs ss tn fl eq)) =
    Cr , C , settled c-abs fr (s-conn refl (re-parts refl pt) (λ ()) (λ ()) (λ _ → tn′)
      (record { shut = Flags.shut fl ; unshut = λ () ; owed = λ ()
              ; torn = λ _ (x , v , o) → proj₂ (Flags.owed fl refl) (owes-≼ C o (Sound.ends (Parts.sb pt) (proj₁ (Flags.owed fl refl)) x v)) }) eq) ,
    silent ≃-refl
    where
      srh = src-husk refl (ss tt) (Parts.ss pt)
      off = srch-off (proj₂ srh)
      tn′ = record { Ps = proj₁ off ; Pb = proj₁ (husk-of (bs tt)) ; sh = proj₁ (proj₂ off) ; bh = proj₂ (husk-of (bs tt))
                   ; tl = owed-tl {k = cs cl false sa p as nothing cx ea sr sc} (bs tt) (Parts.sb pt) (proj₁ (Flags.owed fl refl)) (proj₂ (Flags.owed fl refl)) (src-pt (ss tt) (Parts.ss pt)) (proj₂ (proj₂ off)) }
  con-owed {Cr} {C} {sl = false} (settled {N = owes} c-abs fr (s-conn scp pt bs ss tn fl eq)) =
    Cr , C , settled c-abs fr (s-conn scp (re-parts refl pt) (λ ()) (λ ()) (λ t → torn-off (tn t))
      (record { shut = Flags.shut fl ; unshut = λ () ; torn = Flags.torn fl ; owed = λ () }) eq) ,
    silent ≃-refl
  con-owed {Cr} {C} (settled {N = dead _} c-abs fr (_ , h-blank , le)) = Cr , C , settled c-abs fr (_ , h-blank , le) , silent ≃-refl
  con-owed {Cr} {C} (settled {N = dead _} c-abs fr (_ , h-conn sh hb , le)) with srch-off sh
  ... | _ , sh′ , le′ = Cr , C , settled c-abs fr (_ , h-conn sh′ hb , ⊑-trans le (∪-⊑ le′ ⊑-refl)) , silent ≃-refl
  con-owed (settled {N = lane _ _} c-abs fr (_ , _ , () , _))
  con-owed (settled {N = lanecut _ _} c-abs fr (_ , _ , () , _))
  con-owed (settled {N = pnd _} c-abs fr (_ , () , _))
