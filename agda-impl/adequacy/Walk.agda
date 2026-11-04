{-# OPTIONS --guardedness #-}

-- THE WALK: the frames above a hole and the hole's state, zipped up into
-- the whole tree in step at the root, and the whole tree unzipped down
-- to any hole.  So the invariant at one focus is the invariant at every
-- focus of the same tree, at the same root cursor.
module adequacy.Walk where

open import Data.Bool using (Bool; T; true; false; not; _∨_; _∧_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; reverse; _ʳ++_)
open import Data.List.Properties using (ʳ++-defn)
open import Data.Nat using (ℕ; _+_)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import denotation.Events using (Pos)
open import denotation.Laws.Modulus using (≺-ext)
open import denotation.EmissionSet using (EmissionSet; out)
open import operation.PureObservable using (module Machine)
open Machine using (St; Ctx; Conf; ⟨_,_,_,_⟩; absorbed; Scope; unbound; binds; CS; scopeOf; plug; lnS; cutS; mapS; scanS; takeS; flatS; connS;
                    top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody; closed; free; cpAt; cutAt; overAt)
open import adequacy.Rows using (_≃_; _⇄_; ≃-sym; ≃-trans)
open import adequacy.Cursor using (Up; up; Dom; Thru; Lane; NoKill; Cur; Rgn; SubdAt; notT; Owes; Due; Spent; _≈_; alike; ≈-refl; ≈-trans; fin-≈; tail-≈; Pol; Runs; Hole; h-live; h-end; h-kill; LaneSt; l-live; l-dead; Begun; none; more; bump; joined; Sync; Sound; src-pend; src-on; src-shut; s-cold; s-of; s-done; s-map; s-scan; s-cut; s-take; s-took; s-flat; s-conn; s-join; s-joinx; Torn; Pts; ∅ᵖ; _∪ᵖ_; _⊑_; ⊑-refl; ⊑-trans; ∪-⊑; under-⊑; ∅-⊑; tailp-⊑; Husk; HuskL; h-blank; h-map; h-scan; h-cut; h-ln; h-take; h-flat; h-conn; hl-none; hl-more; SrcH; sh-dead; sh-isle; sh-islec; o-cp; o-cut; o-over; Quiet; QuietL; sh-pend; voc; BurstsAt; bursts)
open import adequacy.Cursor.Tear using (c-abs; NoIsle; Clear; Pending)
open import adequacy.Cursor.Show using (up-id; up-≈; up-∘)
open import adequacy.PinLift using (reach-≈)
open import adequacy.Cursor.Frame using (Need; owes; dead; lane; lanecut; pnd; onoff; LaneHold; Hold; Fr; Unread; un-dead; un-torn; f-top; f-map; f-scan; f-cut; f-take; f-took; f-outer; f-lanes; f-lane; f-lnct; f-src; f-srcc; f-srcp; f-body; d-map; d-scan; d-cut; d-ln; d-take; d-outer; d-lanes; d-src; d-body; f-isle; f-islec; f-islep)
open import adequacy.Cursor.Rise using (Inv; settled)
open _≃_

------------------------------------------------------------------------
-- Entries alike in every visible row tie a state alike.

due-≈ : ∀ {A} {C} {E E′ : EmissionSet A} → E ≈ E′ → Due C E ≃ Due C E′
due-≈ eq = (λ (x , v , o) → let (y , v′) = to (alike eq) (x , v) in y , v′ , o)
         ⇄ (λ (x , v , o) → let (y , v′) = from (alike eq) (x , v) in y , v′ , o)

spent-≈ : ∀ {A} {C} {E E′ : EmissionSet A} → Spent C E → E ≈ E′ → Spent C E′
spent-≈ {C = C} sp eq d = sp (from (due-≈ {C = C} eq) d)

-- A burst's rows read through an alike entry.
bursts-≈ : ∀ {X B} {F : EmissionSet X} {c} {E E′ : EmissionSet B} → E ≈ E′ → BurstsAt F c E → BurstsAt F c E′
bursts-≈ m (bursts w kp) = bursts (λ x i f → let (r , rc) = w x i f in voc m r , reach-≈ m rc)
                                  (λ x ni i le rc → let (a , r , q) = kp x ni i le rc in a , voc m r , reach-≈ m q)

-- A torn connect read through an alike entry.
srch-≈ : ∀ {Γ X B} {sc : Scope Γ} {D} {k : CS Γ X} {o} {E E′ : EmissionSet B} {P} → E ≈ E′ → SrcH sc D k o E P → SrcH sc D k o E′ P
srch-≈ m (sh-dead hk u sf) = sh-dead hk (up-∘ u (up-≈ m)) sf
srch-≈ m (sh-isle na nc sy bh sd ss ao ic bu nr) = sh-isle na nc sy bh sd ss ao ic (bursts-≈ m bu) nr
srch-≈ m (sh-islec na cl sp tp hk dm bh sd ao ic bu nr) = sh-islec na cl sp tp hk dm bh sd ao ic (bursts-≈ m bu) nr
srch-≈ m (sh-pend na nc ba an sc adm pe wn ss bu nr) = sh-pend na nc ba an sc adm pe wn ss (bursts-≈ m bu) nr

torn-≈ : ∀ {Γ X B} {sc : Scope Γ} {C} {k : CS Γ X} {o b} {β E E′ : EmissionSet B} → E ≈ E′ → Torn sc C k o b β E → Torn sc C k o b β E′
torn-≈ m t = record { D = Torn.D t ; Db = Torn.Db t ; dom = Torn.dom t ; Ps = Torn.Ps t ; Pb = Torn.Pb t ; sh = srch-≈ m (Torn.sh t) ; bh = Torn.bh t
                    ; bu = up-∘ (Torn.bu t) (up-≈ m) ; tl = Torn.tl t }

sync-≈ : ∀ {Γ} {sc : Scope Γ} {Rg C A} {s : St Γ A} {E E′} → Sync sc Rg C s E → E ≈ E′ → Sync sc Rg C s E′
sync-≈ {C = C} (s-cold tk d tl) e = s-cold tk (≃-trans (≃-sym (due-≈ {C = C} e)) d) (tail-≈ {C = C} e tl)
sync-≈ {C = C} (s-of d tl) e = s-of (≃-trans (≃-sym (due-≈ {C = C} e)) d) (tail-≈ {C = C} e tl)
sync-≈ {C = C} (s-done sp fn) e = s-done (spent-≈ {C = C} sp e) (fin-≈ {C = C} e fn)
sync-≈ (s-map sy eq sd)      e = s-map sy (≈-trans eq e) sd
sync-≈ (s-scan sy fd eq sd)  e = s-scan sy fd (≈-trans eq e) sd
sync-≈ (s-cut sy)            e = s-cut (sync-≈ sy e)
sync-≈ (s-take sy nf eq sd)  e = s-take sy nf (≈-trans eq e) sd
sync-≈ (s-took fl nr fz ow tp hk dm nf eq sd) e = s-took fl (λ {q} → nr {q}) fz ow tp hk dm nf (≈-trans eq e) sd
sync-≈ (s-flat ji sy j (pn , eq) sd bh) e = s-flat ji sy j (pn , ≈-trans eq e) sd bh
sync-≈ (s-conn sc pt b bb o tn fl (eq , cl)) e = s-conn sc pt b bb o (λ nl → torn-≈ e (tn nl)) fl (≈-trans eq e , cl)
sync-≈ {C = C} (s-join eq d ap lt a) e = s-join (≈-trans eq e) (≃-trans (≃-sym (due-≈ {C = C} e)) d) ap lt a
sync-≈ {C = C} (s-joinx sp fn) e = s-joinx (spent-≈ {C = C} sp e) (fin-≈ {C = C} e fn)

------------------------------------------------------------------------
-- A joiner's begun lanes, cut at one lane and put back.

bump-+ : ∀ b m k → bump b (m + k) ≡ bump b m + k
bump-+ true  m k = refl
bump-+ false m k = refl

data Split {Γ A B} (sc : Scope Γ) (Rl : Pos → Rgn) (C : Cur) (P : Pol A B) (O : EmissionSet A)
           (xs : List (St Γ B)) (s : St Γ B) (post : List (St Γ B)) (vs : List (Pos × A)) (n : ℕ) : Set₁ where
  split : ∀ {vs₁ vs₂ n₁ n₂ q a b}
        → Begun sc Rl C P O vs₁ xs n₁ → O q (out a) → (Owes C q → ⊥) → Runs P q → LaneSt sc (Rl q) C P q a s b
        → Begun sc Rl C P O vs₂ post n₂ → n ≡ n₁ + bump b n₂ → vs ≡ vs₁ ++ (q , a) ∷ vs₂
        → Split sc Rl C P O xs s post vs n

begun-split : ∀ {Γ A B} {sc : Scope Γ} {Rl C} {P : Pol A B} {O} xs {s post vs n}
            → Begun sc Rl C P O vs (xs ++ s ∷ post) n → Split sc Rl C P O xs s post vs n
begun-split []       (more o nq r l bg) = split none o nq r l bg refl refl
begun-split (x ∷ xs) (more {b = b′} o nq r l bg) with begun-split xs bg
... | split {n₁ = n₁} {n₂} {b = b} lf o′ nq′ r′ l′ rt refl refl =
  split (more o nq r l lf) o′ nq′ r′ l′ rt (bump-+ b′ n₁ (bump b n₂)) refl

begun-join : ∀ {Γ A B} {sc : Scope Γ} {Rl C} {P : Pol A B} {O} {xs s post vs₁ vs₂ n₁ n₂ q a b}
           → Begun sc Rl C P O vs₁ xs n₁ → O q (out a) → (Owes C q → ⊥) → Runs P q → LaneSt sc (Rl q) C P q a s b
           → Begun sc Rl C P O vs₂ post n₂ → Begun sc Rl C P O (vs₁ ++ (q , a) ∷ vs₂) (xs ++ s ∷ post) (n₁ + bump b n₂)
begun-join none o nq r l rt = more o nq r l rt
begun-join {n₂ = n₂} {b = b} (more {b = b′} {n = n₁} o′ nq′ r′ l′ lf) o nq r l rt =
  subst (Begun _ _ _ _ _ _ _) (bump-+ b′ n₁ (bump b n₂)) (more o′ nq′ r′ l′ (begun-join lf o nq r l rt))

-- Positions moved pointwise.
pt-⊑ : ∀ {P Q : Pts} → (∀ {y} → P y → Q y) → P ⊑ Q
pt-⊑ f = [] , λ x → inj₁ (f x)

-- A lane list's husk, one lane taken out of its reversed prefix and put
-- back.
hl-rev : ∀ {Γ} {sc : Scope Γ} {D} {A} {pre rest : List (St Γ A)} {E Qa Qr} → HuskL sc D pre E Qa → HuskL sc D rest E Qr
       → Σ Pts λ Q → HuskL sc D (pre ʳ++ rest) E Q × (Qa ∪ᵖ Qr) ⊑ Q
hl-rev hl-none hr = _ , hr , pt-⊑ λ { (inj₁ ()) ; (inj₂ y) → y }
hl-rev (hl-more hx ux ha) hr with hl-rev ha (hl-more hx ux hr)
... | Q , h , le = Q , h , ⊑-trans (pt-⊑ λ { (inj₁ (inj₁ x)) → inj₂ (inj₁ x) ; (inj₁ (inj₂ x)) → inj₁ x ; (inj₂ x) → inj₂ (inj₂ x) }) le

hl-unrev : ∀ {Γ} {sc : Scope Γ} {D} {A} (pre : List (St Γ A)) {rest E Q} → HuskL sc D (pre ʳ++ rest) E Q
         → Σ Pts λ Qa → Σ Pts λ Qr → HuskL sc D pre E Qa × HuskL sc D rest E Qr × Q ⊑ (Qa ∪ᵖ Qr)
hl-unrev []        h = ∅ᵖ , _ , hl-none , h , pt-⊑ inj₂
hl-unrev (x ∷ pre) h with hl-unrev pre h
... | Qa , _ , ha , hl-more hx ux hr , le =
  _ , _ , hl-more hx ux ha , hr , ⊑-trans le (pt-⊑ λ { (inj₁ a) → inj₁ (inj₂ a) ; (inj₂ (inj₁ x)) → inj₁ (inj₁ x) ; (inj₂ (inj₂ r)) → inj₂ r })

-- A list of states nothing in step runs in.
hl-blank : ∀ {Γ} {sc : Scope Γ} {D} {A} (ls : List (St Γ A)) {E} → QuietL ls → Σ Pts λ Q → HuskL sc D ls E Q × Q ⊑ ∅ᵖ
hl-blank []       _        = _ , hl-none , ⊑-refl
hl-blank (l ∷ ls) (q , ql) with hl-blank ls ql
... | Q , h , le = _ , hl-more (h-blank q) up-id h , ⊑-trans (∪-⊑ ⊑-refl le) (pt-⊑ λ { (inj₁ ()) ; (inj₂ ()) })

-- A list of states nothing in step runs in, cut at one of them.
quiet-split : ∀ {Γ A} (pre : List (St Γ A)) {s post} → QuietL (pre ʳ++ s ∷ post) → QuietL pre × Quiet s × QuietL post
quiet-split []        (q , ql) = tt , q , ql
quiet-split (x ∷ pre) {s} {post} ql with quiet-split pre {x} {s ∷ post} ql
... | qa , qx , (qs , qb) = (qx , qa) , qs , qb

-- A dead lane's hole, its tail within more.
hole-⊑ : ∀ {A B} {C} {P : Pol A B} {q a Ph Q E} → Hole C P q a Ph E false → Ph ⊑ Q → Hole C P q a Q E false
hole-⊑ {C = C} (h-end x o tp)  le = h-end x o (tailp-⊑ {C = C} tp le)
hole-⊑ {C = C} (h-kill x o tp) le = h-kill x o (tailp-⊑ {C = C} tp le)

-- A dead lane's hole, read at any entry.
hole-re : ∀ {A B} {C} {P : Pol A B} {q a Ph E E′} → Hole C P q a Ph E false → Hole C P q a Ph E′ false
hole-re (h-end x o tp)  = h-end x o tp
hole-re (h-kill x o tp) = h-kill x o tp

-- What a dead lane was last read at.
LaneDead : ∀ {A B} → Cur → Cur → Pol A B → Pos → A → Bool → EmissionSet B → Set₁
LaneDead C D P q a b E = T (not b) → E ≡ Lane P q a × Dom C D × (∀ {r} → Thru D r → NoKill P q r)

-- A lane's state as its list entry holds it.
laneSt : ∀ {Γ A B} {sc : Scope Γ} {Rg C D} {P : Pol A B} {q a} b {at l E Ph}
       → Hole C P q a Ph E b → LaneHold sc Rg C b D Ph l E → (T b → Sound Rg E) → LaneDead C D P q a b E → LaneSt sc Rg C P q a (lnS b (cutS b at l)) b
laneSt true  hl@(h-live _ _ _) h sd _ = l-live hl h (sd _)
laneSt {sc = sc} {D = D} false {l = l} hl (Q , hk , le) _ dl =
  let (eq , dm , nk) = dl tt in l-dead (hole-⊑ hl le) (subst (λ E → Husk sc D l E Q) eq hk) dm nk

laneHold : ∀ {Γ A B} {sc : Scope Γ} {Rg C} {P : Pol A B} {q a s b}
         → LaneSt sc Rg C P q a s b → Σ Cur λ D → Σ Pts λ Ph → Σ (EmissionSet B) λ E → Hole C P q a Ph E b × Hold sc Rg C (lane b D Ph) s E × (T b → Sound Rg E) × LaneDead C D P q a b E
laneHold {C = C} (l-live hl sy sd) = C , _ , _ , hl , (_ , _ , refl , sy) , (λ _ → sd) , λ ()
laneHold {P = P} {q = q} {a = a} (l-dead hl hk dm nk) = _ , _ , Lane P q a , hole-re hl , (_ , _ , refl , (_ , hk , ⊑-refl)) , (λ ()) , λ _ → refl , dm , nk

-- A switch's hole, on or off.
lh-hold : ∀ {Γ} {sc : Scope Γ} {Rg C} b {D P} {A} {l : St Γ A} {E} → LaneHold sc Rg C b D P l E → Hold sc Rg C (onoff b D P) l E
lh-hold true  h = h
lh-hold false h = h

hold-lh : ∀ {Γ} {sc : Scope Γ} {Rg C} b {D P} {A} {l : St Γ A} {E} → Hold sc Rg C (onoff b D P) l E → LaneHold sc Rg C b D P l E
hold-lh true  h = h
hold-lh false h = h

live? : ∀ b → T b ⊎ T (not b)
live? true  = inj₁ _
live? false = inj₂ _

none′ : ∀ {A : Set} → EmissionSet A
none′ _ _ = ⊥

up-none : ∀ {A B} {D D′} {E : EmissionSet B} → Up D (none′ {A}) D′ E
up-none = up λ _ _ ()

nowhere : Rgn
nowhere _ = ⊥

module _ {R : Set} (Rt : EmissionSet R) where

  -- The whole tree in step at the root's cursor.
  Top : ∀ {Γ A} → Cur → Ctx R Γ A → St Γ A → Set₁
  Top Cr c s = Σ Rgn λ Rg₀ → Σ (EmissionSet R) λ E′ → E′ ≈ Rt × Sync unbound Rg₀ Cr (plug c s) E′

  ----------------------------------------------------------------------
  -- UP: every frame composes its hole's state into its parent's; a part
  -- no live node reads composes its husk, up to the connect nobody reads.

  mutual
    climb : ∀ {Cr C Γ A} {c : Ctx R Γ A} {Rg N E s} → Fr Rt Cr C Rg c N E → Hold (scopeOf c) Rg C N s E → Top Cr c s
    climb (f-top eq)                    h = _ , _ , eq , h
    climb (f-map fr eq sd)              h = climb fr (s-map h eq sd)
    climb (f-scan fr fd eq sd)          h = climb fr (s-scan h fd eq sd)
    climb (f-cut fr)                    h = climb fr (s-cut h)
    climb (f-take fr nf eq sd)          h = climb fr (s-take h nf eq sd)
    climb (f-took fr fl nr fz ow tp dm nf eq sd) (Q , hk , le) = climb fr (s-took fl (λ {q} → nr {q}) fz ow (tailp-⊑ tp le) hk dm nf eq sd)
    climb (f-outer fr ji j eq sd bh)    h = climb fr (s-flat ji h j eq sd bh)
    climb (f-lanes {pre = pre} {b = b} fr ji sy lf o nq r hl rt cnt wt wh od ah ao en li eq so sd bh dl) (_ , _ , refl , h) =
      climb fr (s-flat ji sy (joined bg wt wh od ah ao en li) eq so bh)
      where
        bg = subst (Begun _ _ _ _ _ _ _) (sym cnt)
               (subst (λ ls → Begun _ _ _ _ _ _ ls _) (sym (ʳ++-defn pre)) (begun-join lf o nq r (laneSt b hl h sd dl) rt))
    climb (f-lane fr)                   (at , l , refl , h) = climb fr (at , l , refl , h)
    climb (f-lnct {b = b} fr)           h = climb fr (_ , _ , refl , hold-lh b h)
    climb (f-src fr sc pt lv nc bs bb fl fe eq bh sd af ao ic _) h =
      climb fr (s-conn sc pt (λ _ → bs) (λ _ → bb) (λ _ → src-on nc (sync-≈ h fe) bh sd af ao ic lv) (λ nl → ⊥-elim (notT _ nl lv)) fl eq)
    climb (f-srcc fr sc pt lv cl sp tp dm bh sd ic af bs bb fl eq) (Q , hk , le) =
      climb fr (s-conn sc pt (λ _ → bs) (λ _ → bb) (λ _ → src-shut cl sp (tailp-⊑ tp le) hk dm bh sd ic af lv) (λ nl → ⊥-elim (notT _ nl lv)) fl eq)
    climb (f-srcp {k = k} fr sc pt lv nc na ba an adm bs bb fl fe eq ow sd _) (_ , refl , pe , wn) =
      climb fr (s-conn sc pt (λ _ → bs) (λ _ → bb) (λ _ → src-pend na nc ba an adm (≈-trans pe fe) wn ow (λ o → SubdAt.past sd o (≺-ext (CS.connAt k) [])))
                       (λ nl → ⊥-elim (notT _ nl lv)) fl eq)
    climb (f-body {k = k} fr sc pt lv os bb fl eq) h =
      climb fr (s-conn sc pt (λ _ → subst (λ x → Sync (binds (CS.src k) (CS.connAt k) x) _ _ _ _) sc h) (λ _ → bb) (λ _ → os) (λ nl → ⊥-elim (notT _ nl lv)) fl eq)
    climb (d-map fr u)                  (Q , hk , le) = climb fr (Q , h-map hk u , le)
    climb (d-scan fr u)                 (Q , hk , le) = climb fr (Q , h-scan hk u , le)
    climb (d-cut fr u)                  (Q , hk , le) = climb fr (Q , h-cut hk u , le)
    climb (d-ln fr u)                   (Q , hk , le) = climb fr (Q , h-ln hk u , le)
    climb (d-take fr u)                 (Q , hk , le) = climb fr (Q , h-take hk u , le)
    climb (d-outer fr u hl le)          (Q , hk , le′) = climb fr (_ , h-flat hk u hl , ⊑-trans le (∪-⊑ le′ ⊑-refl))
    climb (d-lanes fr ho uo ha hb u le) (Q , hk , le′) with hl-rev ha (hl-more hk u hb)
    ... | Q′ , hl , le″ = climb fr (_ , h-flat ho uo hl , ⊑-trans le (∪-⊑ ⊑-refl (⊑-trans (∪-⊑ ⊑-refl (∪-⊑ le′ ⊑-refl)) le″)))
    climb (d-src u hb ub us le _ f)     (Q , hk , le′) = unread-up u (sh-dead hk us f) hb ub (⊑-trans le (∪-⊑ (under-⊑ le′) ⊑-refl))
    climb (d-body u sh us le)           (Q , hk , le′) = unread-up u sh hk us (⊑-trans le (∪-⊑ ⊑-refl le′))
    climb (f-isle u hb ub le na nc bh sd ss ao ic bu nr _) h = unread-up u (sh-isle na nc h bh sd ss ao ic bu nr) hb ub le
    climb (f-islec u hb ub le na cl sp tp dm bh sd ao ic bu nr) (Q , hk , le′) = unread-up u (sh-islec na cl sp (tailp-⊑ tp le′) hk dm bh sd ao ic bu nr) hb ub le
    climb (f-islep u hb ub le na nc ba an sc adm ss bu nr _) (_ , refl , pe , wn) = unread-up u (sh-pend na nc ba an sc adm pe wn ss bu nr) hb ub le

    unread-up : ∀ {Cr C D Db Γ X B} {E : EmissionSet B} {c : Ctx R Γ B} {k : CS Γ X} {o b β P Ps Qb} → Unread Rt Cr C D E β c k P → SrcH (scopeOf c) D k o E Ps
              → Husk (binds (CS.src k) (CS.connAt k) (CS.scope k)) Db b β Qb → Up Db β D E → P ⊑ (Ps ∪ᵖ Qb) → Top Cr c (connS k o b)
    unread-up (un-dead fr) sh hb u le = climb fr (_ , h-conn sh hb u , le)
    unread-up {D = D} {Db = Db} (un-torn fr sc pt nl fl eq tp dm) sh hb u le =
      climb fr (s-conn sc pt (λ t → ⊥-elim (notT _ nl t)) (λ t → ⊥-elim (notT _ nl t)) (λ t → ⊥-elim (notT _ nl t))
                       (λ _ → record { D = D ; Db = Db ; dom = dm ; Ps = _ ; Pb = _ ; sh = sh ; bh = hb ; bu = u ; tl = tailp-⊑ tp le }) fl eq)

  ----------------------------------------------------------------------
  -- A part no live node reads is closed to its own observer: a failed
  -- takeWhile, a switched-off lane, an ended source, or a connect torn or
  -- dead whose source is attached or ended.

  private
    or-l : ∀ a b → T a → T (a ∨ b)
    or-l true _ _ = tt

    or-r : ∀ a b → T b → T (a ∨ b)
    or-r true  _ _ = tt
    or-r false _ t = t

    and-i : ∀ a b → T a → T b → T (a ∧ b)
    and-i true _ _ t = t

  mutual
    dead-closed : ∀ {Cr C Γ A} {c : Ctx R Γ A} {Rg N E D P} → Fr Rt Cr C Rg c N E → N ≡ dead D P → T (closed c)
    dead-closed (f-top _) ()
    dead-closed (f-map _ _ _) ()
    dead-closed (f-scan _ _ _ _) ()
    dead-closed (f-cut _) ()
    dead-closed (f-take _ _ _ _) ()
    dead-closed (f-took _ _ _ _ (o-cp _) _ _ _ _ _) refl = tt
    dead-closed (f-took _ _ _ _ (o-cut _) _ _ _ _ _) refl = tt
    dead-closed (f-took _ _ _ _ (o-over _) _ _ _ _ _) refl = tt
    dead-closed (f-outer _ _ _ _ _ _) ()
    dead-closed (f-lanes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ()
    dead-closed (f-lane _) ()
    dead-closed (f-lnct {b = true} _) ()
    dead-closed (f-lnct {b = false} _) refl = tt
    dead-closed (f-src _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ()
    dead-closed (f-srcc {k = k} {c = c} _ _ _ _ cl _ _ _ _ _ _ _ _ _ _ _) refl =
      or-l (CS.closed k) (CS.srcAtt k ∧ (not (CS.srcLive k) ∨ closed c)) cl
    dead-closed (f-srcp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ()
    dead-closed (f-body _ _ _ _ _ _ _ _) ()
    dead-closed (d-map fr _) refl = dead-closed fr refl
    dead-closed (d-scan fr _) refl = dead-closed fr refl
    dead-closed (d-cut {l = l} fr _) refl = or-r (not l) _ (dead-closed fr refl)
    dead-closed (d-ln fr _) refl = dead-closed fr refl
    dead-closed (d-take {w = free} fr _) refl = dead-closed fr refl
    dead-closed (d-take {w = cpAt _} _ _) refl = tt
    dead-closed (d-take {w = cutAt _} _ _) refl = tt
    dead-closed (d-take {w = overAt _} _ _) refl = tt
    dead-closed (d-outer fr _ _ _) refl = dead-closed fr refl
    dead-closed (d-lanes fr _ _ _ _ _ _) refl = dead-closed fr refl
    dead-closed (d-src {k = k} {c = c} _ _ _ _ _ _ (inj₂ cl)) refl =
      or-l (CS.closed k) (CS.srcAtt k ∧ (not (CS.srcLive k) ∨ closed c)) cl
    dead-closed (d-src {k = k} {c = c} u _ _ _ _ _ (inj₁ at)) refl =
      or-r (CS.closed k) (CS.srcAtt k ∧ (not (CS.srcLive k) ∨ closed c))
           (and-i (CS.srcAtt k) (not (CS.srcLive k) ∨ closed c) at (unread-closed u))
    dead-closed (d-body u _ _ _) refl = unread-closed u
    dead-closed (f-isle _ _ _ _ _ _ _ _ _ _ _ _ _ _) ()
    dead-closed (f-islec {k = k} {c = c} _ _ _ _ _ cl _ _ _ _ _ _ _ _ _) refl =
      or-l (CS.closed k) (CS.srcAtt k ∧ (not (CS.srcLive k) ∨ closed c)) cl
    dead-closed (f-islep _ _ _ _ _ _ _ _ _ _ _ _ _ _) ()

    unread-closed : ∀ {Cr C D Γ X B} {E : EmissionSet B} {c : Ctx R Γ B} {k : CS Γ X} {β P} → Unread Rt Cr C D E β c k P → T (not (CS.srcLive k) ∨ closed c)
    unread-closed {c = c} {k = k} (un-dead fr) = or-r (not (CS.srcLive k)) (closed c) (dead-closed fr refl)
    unread-closed {c = c} {k = k} (un-torn _ _ _ nl _ _ _ _) = or-l (not (CS.srcLive k)) (closed c) nl

  ----------------------------------------------------------------------
  -- DOWN: every frame splits its parent's state into its hole's.

  Res : ∀ {Γ A} → Cur → Ctx R Γ A → St Γ A → Set₁
  Res {A = A} Cr c s = Σ Cur λ C → Σ Need λ N → Σ Rgn λ Rg → Σ (EmissionSet A) λ E → Fr Rt Cr C Rg c N E × Hold (scopeOf c) Rg C N s E

  -- Down through a part no live node reads.
  src-dead : ∀ {Cr C D Db Γ X B} {E : EmissionSet B} {c : Ctx R Γ B} {k : CS Γ X} {s b β P Ps Qb} → Unread Rt Cr C D E β c k P → SrcH (scopeOf c) D k s E Ps
           → Husk (binds (CS.src k) (CS.connAt k) (CS.scope k)) Db b β Qb → Up Db β D E → P ⊑ (Ps ∪ᵖ Qb) → NoIsle b → Res Cr (inSrc k b c) s
  src-dead {C = C} u (sh-dead hk us f) hb ub le nb                = C , dead _ _ , nowhere , _ , d-src u hb ub us le nb f , (_ , hk , ⊑-refl)
  src-dead u (sh-isle na nc sy bh sd ss ao ic bu nr) hb ub le nb     = _ , owes , _ , _ , f-isle u hb ub le na nc bh sd ss ao ic bu nr nb , sy
  src-dead {C = C} u (sh-islec na cl sp tp hk dm bh sd ao ic bu nr) hb ub le _ = C , dead _ _ , nowhere , _ , f-islec u hb ub le na cl sp tp dm bh sd ao ic bu nr , (_ , hk , ⊑-refl)
  src-dead u (sh-pend na nc ba an sc adm pe wn ss bu nr) hb ub le nb = _ , pnd _ , _ , _ , f-islep u hb ub le na nc ba an sc adm ss bu nr nb , (_ , refl , pe , wn)

  body-dead : ∀ {Cr C D Db Γ X B} {E : EmissionSet B} {c : Ctx R Γ B} {k : CS Γ X} {o b β P Ps Qb} → Unread Rt Cr C D E β c k P → SrcH (scopeOf c) D k o E Ps
            → Husk (binds (CS.src k) (CS.connAt k) (CS.scope k)) Db b β Qb → Up Db β D E → P ⊑ (Ps ∪ᵖ Qb) → Res Cr (inBody k o c) b
  body-dead {C = C} u sh hb ub le = C , dead _ _ , nowhere , _ , d-body u sh ub le , (_ , hb , ⊑-refl)

  down-map : ∀ {Cr Γ A B} {f : A → B} {c : Ctx R Γ B} {s} → Res Cr c (mapS f s) → Res Cr (inMap f c) s
  down-map (C , owes , _ , _ , fr , s-map sy me sd)            = C , owes , _ , _ , f-map fr me sd , sy
  down-map (C , dead D P , _ , _ , fr , (Q , h-map hk u , le))  = C , dead _ P , nowhere , _ , d-map fr u , (Q , hk , le)
  down-map (C , dead D P , _ , _ , fr , (Q , h-blank q , le))   = C , dead D P , nowhere , none′ , d-map fr up-none , (Q , h-blank q , le)
  down-map (_ , lane _ _ _ , _ , _ , _ , (_ , _ , () , _))
  down-map (_ , lanecut _ _ _ , _ , _ , _ , (_ , _ , () , _))
  down-map (_ , pnd _ , _ , _ , _ , (_ , () , _))

  down-scan : ∀ {Cr Γ A B} {f : B → A → B} {z} {c : Ctx R Γ B} {s} → Res Cr c (scanS f z s) → Res Cr (inScan f z c) s
  down-scan (C , owes , _ , _ , fr , s-scan sy fd eq sd)         = C , owes , _ , _ , f-scan fr fd eq sd , sy
  down-scan (C , dead D P , _ , _ , fr , (Q , h-scan hk u , le)) = C , dead _ P , nowhere , _ , d-scan fr u , (Q , hk , le)
  down-scan (C , dead D P , _ , _ , fr , (Q , h-blank q , le))   = C , dead D P , nowhere , none′ , d-scan fr up-none , (Q , h-blank q , le)
  down-scan (_ , lane _ _ _ , _ , _ , _ , (_ , _ , () , _))
  down-scan (_ , lanecut _ _ _ , _ , _ , _ , (_ , _ , () , _))
  down-scan (_ , pnd _ , _ , _ , _ , (_ , () , _))

  down-cut : ∀ {Cr Γ A} {l a} {c : Ctx R Γ A} {s} → Res Cr c (cutS l a s) → Res Cr (inCut l a c) s
  down-cut (C , owes , _ , _ , fr , s-cut sy)                    = C , owes , _ , _ , f-cut fr , sy
  down-cut (C , dead D P , _ , _ , fr , (Q , h-cut hk u , le))   = C , dead _ P , nowhere , _ , d-cut fr u , (Q , hk , le)
  down-cut (C , dead D P , _ , _ , fr , (Q , h-blank q , le))    = C , dead D P , nowhere , none′ , d-cut fr up-none , (Q , h-blank q , le)
  down-cut (_ , lane _ _ _ , _ , _ , _ , (_ , _ , () , _))
  down-cut (C , lanecut b D P , _ , _ , fr , (_ , _ , refl , h)) = C , onoff b D P , _ , _ , f-lnct fr , lh-hold b h
  down-cut (_ , pnd _ , _ , _ , _ , (_ , () , _))

  down-ln : ∀ {Cr Γ A} {b} {c : Ctx R Γ A} {s} → Res Cr c (lnS b s) → Res Cr (inLn b c) s
  down-ln (_ , owes , _ , _ , _ , ())
  down-ln (C , dead D P , _ , _ , fr , (Q , h-ln hk u , le))   = C , dead _ P , nowhere , _ , d-ln fr u , (Q , hk , le)
  down-ln (C , dead D P , _ , _ , fr , (Q , h-blank q , le))   = C , dead D P , nowhere , none′ , d-ln fr up-none , (Q , h-blank q , le)
  down-ln (C , lane b D P , _ , _ , fr , (at , l , refl , h))  = C , lanecut b D P , _ , _ , f-lane fr , (at , l , refl , h)
  down-ln (_ , lanecut _ _ _ , _ , _ , _ , (_ , _ , () , _))
  down-ln (_ , pnd _ , _ , _ , _ , (_ , () , _))

  down-take : ∀ {Cr Γ A} {i keep w} {c : Ctx R Γ A} {s} → Res Cr c (takeS i keep w s) → Res Cr (inTake i keep w c) s
  down-take (C , owes , _ , _ , fr , s-take sy nf eq sd)                  = C , owes , _ , _ , f-take fr nf eq sd , sy
  down-take (C , owes , _ , _ , fr , s-took fl nr fz ow tp hk dm nf eq sd) = C , dead _ _ , nowhere , _ , f-took fr fl nr fz ow tp dm nf eq sd , (_ , hk , ⊑-refl)
  down-take (C , dead D P , _ , _ , fr , (Q , h-take hk u , le))          = C , dead _ P , nowhere , _ , d-take fr u , (Q , hk , le)
  down-take (C , dead D P , _ , _ , fr , (Q , h-blank q , le))            = C , dead D P , nowhere , none′ , d-take fr up-none , (Q , h-blank q , le)
  down-take (_ , lane _ _ _ , _ , _ , _ , (_ , _ , () , _))
  down-take (_ , lanecut _ _ _ , _ , _ , _ , (_ , _ , () , _))
  down-take (_ , pnd _ , _ , _ , _ , (_ , () , _))

  down-outer : ∀ {Cr Γ A B} {op} {f} {ω} {d n qu ls} {c : Ctx R Γ B} {s : St Γ A}
             → Res Cr c (flatS op f ω d n qu s ls) → Res Cr (inOuter op f ω d n qu ls c) s
  down-outer (C , owes , _ , _ , fr , s-flat ji sy j eq sd bh)      = C , owes , _ , _ , f-outer fr ji j eq sd bh , sy
  down-outer (C , dead D P , _ , _ , fr , (Q , h-flat ho u hl , le)) = C , dead _ _ , nowhere , _ , d-outer fr u hl le , (_ , ho , ⊑-refl)
  down-outer {ls = ls} (C , dead D P , _ , _ , fr , (Q , h-blank (qo , ql) , le)) with hl-blank ls ql
  ... | _ , hl , _ = C , dead D ∅ᵖ , nowhere , none′ , d-outer fr up-none hl (⊑-trans le ∅-⊑) , (_ , h-blank qo , ⊑-refl)
  down-outer (_ , lane _ _ _ , _ , _ , _ , (_ , _ , () , _))
  down-outer (_ , lanecut _ _ _ , _ , _ , _ , (_ , _ , () , _))
  down-outer (_ , pnd _ , _ , _ , _ , (_ , () , _))

  down-lanes : ∀ {Cr Γ A B} {op} {f} {ω} {d n qu} {o : St Γ A} {pre post} {c : Ctx R Γ B} {s}
             → Res Cr c (flatS op f ω d n qu o (pre ʳ++ s ∷ post)) → Res Cr (inLanes op f ω d n qu o pre post c) s
  down-lanes {pre = pre} (C , owes , _ , _ , fr , s-flat ji sy (joined bg wt wh od ah ao en li) eq so bh)
    with begun-split (reverse pre) (subst (λ ls → Begun _ _ _ _ _ _ ls _) (ʳ++-defn pre) bg)
  ... | split lf o nq r l rt cnt refl with laneHold l
  ...   | _ , _ , _ , hl , hd , sd , dl = C , lane _ _ _ , _ , _ , f-lanes fr ji sy lf o nq r hl rt cnt wt wh od ah ao en li eq so sd bh dl , hd
  down-lanes {pre = pre} (C , dead D P , _ , _ , fr , (Q , h-flat ho uo hl , le)) with hl-unrev pre hl
  ... | _ , _ , ha , hl-more hs us hb , le′ = C , dead _ _ , nowhere , _ , d-lanes fr ho uo ha hb us (⊑-trans le (∪-⊑ ⊑-refl le′)) , (_ , hs , ⊑-refl)
  down-lanes {pre = pre} {post = post} {s = s} (C , dead D P , _ , _ , fr , (Q , h-blank (qo , ql) , le)) with quiet-split pre {s} {post} ql
  ... | qa , qs , qb with hl-blank pre qa | hl-blank post qb
  ...   | _ , ha , _ | _ , hb , _ = C , dead D ∅ᵖ , nowhere , none′ , d-lanes fr (h-blank {D = D} qo) (up-none {D = D}) ha hb up-none (⊑-trans le ∅-⊑) , (_ , h-blank qs , ⊑-refl)
  down-lanes (_ , lane _ _ _ , _ , _ , _ , (_ , _ , () , _))
  down-lanes (_ , lanecut _ _ _ , _ , _ , _ , (_ , _ , () , _))
  down-lanes (_ , pnd _ , _ , _ , _ , (_ , () , _))

  down-src : ∀ {Cr Γ X B} {k : CS Γ X} {b} {c : Ctx R Γ B} {s} → (Pending s → ⊥) → NoIsle b → Res Cr c (connS k s b) → Res Cr (inSrc k b c) s
  down-src {k = k} np nb (C , owes , _ , _ , fr , s-conn sc pt bs bb os tn fl eq) with live? (CS.srcLive k)
  ... | inj₂ nl = let t = tn nl in src-dead (un-torn fr sc pt nl fl eq (Torn.tl t) (Torn.dom t)) (Torn.sh t) (Torn.bh t) (Torn.bu t) ⊑-refl nb
  ... | inj₁ lv with os lv
  ...   | src-on nc sy bh sd af ao ic _   = C , owes , _ , _ , f-src fr sc pt lv nc (bs lv) (bb lv) fl ≈-refl eq bh sd af ao ic nb , sy
  ...   | src-shut cl sp tp hk dm bh sd ic af _ = C , dead _ _ , nowhere , _ , f-srcc fr sc pt lv cl sp tp dm bh sd ic af (bs lv) (bb lv) fl eq , (_ , hk , ⊑-refl)
  ...   | src-pend _ _ _ _ _ _ _ _ _    = ⊥-elim (np tt)
  down-src _ nb (C , dead D P , _ , _ , fr , (Q , h-conn sh hb u , le)) = src-dead (un-dead fr) sh hb u le nb
  down-src _ nb (C , dead D P , _ , _ , fr , (Q , h-blank (f , qs , qb) , le)) =
    C , dead D ∅ᵖ , nowhere , none′ , d-src (un-dead fr) (h-blank {D = D} qb) (up-none {D = D}) up-none (⊑-trans le ∅-⊑) nb f , (_ , h-blank qs , ⊑-refl)
  down-src _ _ (_ , lane _ _ _ , _ , _ , _ , (_ , _ , () , _))
  down-src _ _ (_ , lanecut _ _ _ , _ , _ , _ , (_ , _ , () , _))
  down-src _ _ (_ , pnd _ , _ , _ , _ , (_ , () , _))

  down-body : ∀ {Cr Γ X B} {k : CS Γ X} {o} {c : Ctx R Γ B} {s} → Res Cr c (connS k o s) → Res Cr (inBody k o c) s
  down-body {k = k} {s = s} (C , owes , _ , _ , fr , s-conn sc pt bs bb os tn fl eq) with live? (CS.srcLive k)
  ... | inj₂ nl = let t = tn nl in body-dead (un-torn fr sc pt nl fl eq (Torn.tl t) (Torn.dom t)) (Torn.sh t) (Torn.bh t) (Torn.bu t) ⊑-refl
  ... | inj₁ lv = C , owes , _ , _ , f-body fr sc pt lv (os lv) (bb lv) fl eq , subst (λ x → Sync (binds (CS.src k) (CS.connAt k) x) _ C s _) (sym sc) (bs lv)
  down-body (C , dead D P , _ , _ , fr , (Q , h-conn sh hb u , le)) = body-dead (un-dead fr) sh hb u le
  down-body (C , dead D P , _ , _ , fr , (Q , h-blank (f , qo , qs) , le)) =
    C , dead D ∅ᵖ , nowhere , none′ , d-body (un-dead fr) (sh-dead (h-blank {D = D} qo) (up-none {D = D}) f) up-none (⊑-trans le ∅-⊑) , (_ , h-blank qs , ⊑-refl)
  down-body (_ , lane _ _ _ , _ , _ , _ , (_ , _ , () , _))
  down-body (_ , lanecut _ _ _ , _ , _ , _ , (_ , _ , () , _))
  down-body (_ , pnd _ , _ , _ , _ , (_ , () , _))

  -- The hole no pending subscription: a pending source is never
  -- descended to, only subscribed from its connect's mark.
  descend : ∀ {Cr Γ A} (c : Ctx R Γ A) s {Rg E} → (Pending s → ⊥) → Clear c → Sync unbound Rg Cr (plug c s) E → E ≈ Rt → Res Cr c s
  descend {Cr} top                            s _  _          sy eq = Cr , owes , _ , _ , f-top eq , sy
  descend (inMap f c)                         s _  cl         sy eq = down-map (descend c _ (λ ()) cl sy eq)
  descend (inScan f z c)                      s _  cl         sy eq = down-scan (descend c _ (λ ()) cl sy eq)
  descend (inCut l a c)                       s _  cl         sy eq = down-cut (descend c _ (λ ()) cl sy eq)
  descend (inLn b c)                          s _  cl         sy eq = down-ln (descend c _ (λ ()) cl sy eq)
  descend (inTake i p w c)                    s _  cl         sy eq = down-take (descend c _ (λ ()) cl sy eq)
  descend (inOuter op f ω d n q ls c)         s _  cl         sy eq = down-outer (descend c _ (λ ()) cl sy eq)
  descend (inLanes op f ω d n q o pre post c) s _  cl         sy eq = down-lanes (descend c _ (λ ()) cl sy eq)
  descend (inSrc k b c)                       s np (nb , cl)  sy eq = down-src np nb (descend c _ (λ ()) cl sy eq)
  descend (inBody k o c)                      s _  cl         sy eq = down-body (descend c _ (λ ()) cl sy eq)

  ----------------------------------------------------------------------
  -- REFOCUSING keeps the invariant: the same tree, the same root cursor;
  -- the hole's world is wherever the new hole lies, along a clear path.

  refocus : ∀ {Cr C Γ A Γ′ A′} {c : Ctx R Γ A} {c′ : Ctx R Γ′ A′} {s s′ r}
          → Inv Rt Cr C ⟨ c , s , absorbed , r ⟩ → plug c′ s′ ≡ plug c s → (Pending s′ → ⊥) → Clear c′ → Σ Cur λ C′ → Inv Rt Cr C′ ⟨ c′ , s′ , absorbed , r ⟩
  refocus {c′ = c′} {s′ = s′} (settled _ fr h) eq np cl with climb fr h
  ... | _ , _ , top≈ , sy with descend c′ s′ np cl (subst (λ t → Sync unbound _ _ t _) (sym eq) sy) top≈
  ...   | C′ , _ , _ , _ , fr′ , h′ = C′ , settled c-abs fr′ h′
