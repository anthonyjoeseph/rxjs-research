{-# OPTIONS --guardedness #-}

-- THE WALK: the frames above a hole and the hole's state, zipped up into
-- the whole tree in step at the root, and the whole tree unzipped down
-- to any hole.  So the invariant at one focus is the invariant at every
-- focus of the same tree, at the same root cursor.
module adequacy.Walk where

open import Data.Bool using (T; true; false; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; reverse; _ʳ++_)
open import Data.List.Properties using (ʳ++-defn)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import denotation.Events using (Pos)
open import denotation.EmissionSet using (EmissionSet; out)
open import operation.PureObservable using (module Machine)
open Machine using (St; Ctx; Conf; ⟨_,_,_,_⟩; absorbed; Scope; unbound; binds; CS; scopeOf; plug; lnS; cutS; mapS; scanS; takeS; flatS; connS;
                    top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody)
open import adequacy.Rows using (_≃_; _⇄_; ≃-sym; ≃-trans)
open import adequacy.Cursor using (Cur; Rgn; notT; Owes; Due; Spent; _≈_; alike; ≈-refl; ≈-sym; ≈-trans; fin-≈; tail-≈; Pol; Runs; Hole; h-live; h-end; h-kill;
  LaneSt; l-live; l-dead; Begun; none; more; bump; joined; Sync; Sound; src-pend; src-on; src-shut; s-cold; s-of; s-done; s-map; s-scan;
  s-cut; s-take; s-took; s-flat; s-conn; s-join; s-joinx; Torn; Pts; ∅ᵖ; _∪ᵖ_; _⊑_; ⊑-refl; ⊑-trans; ∪-⊑; under-⊑; ∅-⊑; tailp-⊑;
  Husk; HuskL; h-blank; h-map; h-scan; h-cut; h-ln; h-take; h-flat; h-conn; hl-none; hl-more; SrcH; sh-dead; sh-isle; sh-islec; unbind;
  Need; owes; dead; lane; lanecut; pnd; onoff; Rest; LaneHold; Hold; Fr; Unread; un-dead; un-torn; f-top; f-map; f-scan; f-cut;
  f-take; f-took; f-outer; f-lanes; f-lane; f-lnct; f-src; f-srcc; f-srcp; f-body; d-map; d-scan; d-cut; d-ln; d-take; d-outer; d-lanes;
  d-src; d-body; f-isle; f-islec; Inv; settled; c-abs; NoIsle; Clear; Pending; pd)
open _≃_

------------------------------------------------------------------------
-- Entries alike in every visible row tie a state alike.

due-≈ : ∀ {A} {C} {E E′ : EmissionSet A} → E ≈ E′ → Due C E ≃ Due C E′
due-≈ eq = (λ (x , v , o) → let (y , v′) = to (alike eq) (x , v) in y , v′ , o)
         ⇄ (λ (x , v , o) → let (y , v′) = from (alike eq) (x , v) in y , v′ , o)

spent-≈ : ∀ {A} {C} {E E′ : EmissionSet A} → Spent C E → E ≈ E′ → Spent C E′
spent-≈ {C = C} sp eq d = sp (from (due-≈ {C = C} eq) d)

sync-≈ : ∀ {Γ} {sc : Scope Γ} {Rg C A} {s : St Γ A} {E E′} → Sync sc Rg C s E → E ≈ E′ → Sync sc Rg C s E′
sync-≈ {C = C} (s-cold tk d tl) e = s-cold tk (≃-trans (≃-sym (due-≈ {C = C} e)) d) (tail-≈ {C = C} e tl)
sync-≈ {C = C} (s-of d tl) e = s-of (≃-trans (≃-sym (due-≈ {C = C} e)) d) (tail-≈ {C = C} e tl)
sync-≈ {C = C} (s-done sp fn) e = s-done (spent-≈ {C = C} sp e) (fin-≈ {C = C} e fn)
sync-≈ (s-map sy eq sd)      e = s-map sy (≈-trans eq e) sd
sync-≈ (s-scan sy fd eq sd)  e = s-scan sy fd (≈-trans eq e) sd
sync-≈ (s-cut sy)            e = s-cut (sync-≈ sy e)
sync-≈ (s-take sy nf eq sd)  e = s-take sy nf (≈-trans eq e) sd
sync-≈ (s-took fl nr fz ow tp hk eq sd) e = s-took fl (λ {q} → nr {q}) fz ow tp hk (≈-trans eq e) sd
sync-≈ (s-flat ji sy j (pn , eq) sd bh) e = s-flat ji sy j (pn , ≈-trans eq e) sd bh
sync-≈ (s-conn sc pt b o tn fl (eq , cl)) e = s-conn sc pt b o tn fl (≈-trans eq e , cl)
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
hl-rev : ∀ {Γ} {sc : Scope Γ} {A} {pre rest : List (St Γ A)} {Qa Qr} → HuskL sc pre Qa → HuskL sc rest Qr
       → Σ Pts λ Q → HuskL sc (pre ʳ++ rest) Q × (Qa ∪ᵖ Qr) ⊑ Q
hl-rev hl-none hr = _ , hr , pt-⊑ λ { (inj₁ ()) ; (inj₂ y) → y }
hl-rev (hl-more hx ha) hr with hl-rev ha (hl-more hx hr)
... | Q , h , le = Q , h , ⊑-trans (pt-⊑ λ { (inj₁ (inj₁ x)) → inj₂ (inj₁ x) ; (inj₁ (inj₂ x)) → inj₁ x ; (inj₂ x) → inj₂ (inj₂ x) }) le

hl-unrev : ∀ {Γ} {sc : Scope Γ} {A} (pre : List (St Γ A)) {rest Q} → HuskL sc (pre ʳ++ rest) Q
         → Σ Pts λ Qa → Σ Pts λ Qr → HuskL sc pre Qa × HuskL sc rest Qr × Q ⊑ (Qa ∪ᵖ Qr)
hl-unrev []        h = ∅ᵖ , _ , hl-none , h , pt-⊑ inj₂
hl-unrev (x ∷ pre) h with hl-unrev pre h
... | Qa , _ , ha , hl-more hx hr , le =
  _ , _ , hl-more hx ha , hr , ⊑-trans le (pt-⊑ λ { (inj₁ a) → inj₁ (inj₂ a) ; (inj₂ (inj₁ x)) → inj₁ (inj₁ x) ; (inj₂ (inj₂ r)) → inj₂ r })

-- A list of states nothing in step runs in.
hl-blank : ∀ {Γ} {sc : Scope Γ} {A} (ls : List (St Γ A)) → Σ Pts λ Q → HuskL sc ls Q × Q ⊑ ∅ᵖ
hl-blank []       = _ , hl-none , ⊑-refl
hl-blank (l ∷ ls) with hl-blank ls
... | Q , h , le = _ , hl-more h-blank h , ⊑-trans (∪-⊑ ⊑-refl le) (pt-⊑ λ { (inj₁ ()) ; (inj₂ ()) })

-- A dead lane's hole, its tail within more.
hole-⊑ : ∀ {A B} {C} {P : Pol A B} {q a Ph Q E} → Hole C P q a Ph E false → Ph ⊑ Q → Hole C P q a Q E false
hole-⊑ (h-end x o tp)  le = h-end x o (tailp-⊑ tp le)
hole-⊑ (h-kill x o tp) le = h-kill x o (tailp-⊑ tp le)

-- A lane's state as its list entry holds it.
laneSt : ∀ {Γ A B} {sc : Scope Γ} {Rg C} {P : Pol A B} {q a} b {at l E Ph}
       → Hole C P q a Ph E b → LaneHold sc Rg C b Ph l E → (T b → Sound Rg E) → LaneSt sc Rg C P q a (lnS b (cutS b at l)) b
laneSt true  hl@(h-live _ _ _) h sd = l-live hl h (sd _)
laneSt false hl (Q , hk , le) _     = l-dead (hole-⊑ hl le) hk

laneHold : ∀ {Γ A B} {sc : Scope Γ} {Rg C} {P : Pol A B} {q a s b}
         → LaneSt sc Rg C P q a s b → Σ Pts λ Ph → Σ (EmissionSet B) λ E → Hole C P q a Ph E b × Hold sc Rg C (lane b Ph) s E × (T b → Sound Rg E)
laneHold (l-live hl sy sd) = _ , _ , hl , (_ , _ , refl , sy) , λ _ → sd
laneHold (l-dead hl hk)    = _ , _ , hl , (_ , _ , refl , (_ , hk , ⊑-refl)) , λ ()

-- A switch's hole, on or off.
lh-hold : ∀ {Γ} {sc : Scope Γ} {Rg C} b {P} {A} {l : St Γ A} {E} → LaneHold sc Rg C b P l E → Hold sc Rg C (onoff b P) l E
lh-hold true  h = h
lh-hold false h = h

hold-lh : ∀ {Γ} {sc : Scope Γ} {Rg C} b {P} {A} {l : St Γ A} {E} → Hold sc Rg C (onoff b P) l E → LaneHold sc Rg C b P l E
hold-lh true  h = h
hold-lh false h = h

live? : ∀ b → T b ⊎ T (not b)
live? true  = inj₁ _
live? false = inj₂ _

none′ : ∀ {A : Set} → EmissionSet A
none′ _ _ = ⊥

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
    climb (f-took fr fl nr fz ow tp eq sd) (Q , hk , le) = climb fr (s-took fl (λ {q} → nr {q}) fz ow (tailp-⊑ tp le) hk eq sd)
    climb (f-outer fr ji j eq sd bh)    h = climb fr (s-flat ji h j eq sd bh)
    climb (f-lanes {pre = pre} {b = b} fr ji sy lf o nq r hl rt cnt wt wh od ah ao en li eq so sd bh) (_ , _ , refl , h) =
      climb fr (s-flat ji sy (joined bg wt wh od ah ao en li) eq so bh)
      where
        bg = subst (Begun _ _ _ _ _ _ _) (sym cnt)
               (subst (λ ls → Begun _ _ _ _ _ _ ls _) (sym (ʳ++-defn pre)) (begun-join lf o nq r (laneSt b hl h sd) rt))
    climb (f-lane fr)                   (at , l , refl , h) = climb fr (at , l , refl , h)
    climb (f-lnct {b = b} fr)           h = climb fr (_ , _ , refl , hold-lh b h)
    climb (f-src fr sc pt lv nc bs fl fe eq bh sd _) h =
      climb fr (s-conn sc pt (λ _ → bs) (λ _ → src-on nc (sync-≈ h (≈-sym fe)) bh sd) (λ nl → ⊥-elim (notT _ nl lv)) fl eq)
    climb (f-srcc fr sc pt lv cl sp tp bh sd bs fl eq) (Q , hk , le) =
      climb fr (s-conn sc pt (λ _ → bs) (λ _ → src-shut cl sp (tailp-⊑ tp le) hk bh sd) (λ nl → ⊥-elim (notT _ nl lv)) fl eq)
    climb (f-srcp fr sc pt lv nc ba adm bs fl fe eq ow _ _) (_ , refl , pe , wn) =
      climb fr (s-conn sc pt (λ _ → bs) (λ _ → src-pend nc ba adm (≈-trans pe (≈-sym fe)) wn ow) (λ nl → ⊥-elim (notT _ nl lv)) fl eq)
    climb (f-body {k = k} fr sc pt lv os fl eq) h =
      climb fr (s-conn sc pt (λ _ → subst (λ x → Sync (binds (CS.src k) (CS.connAt k) x) _ _ _ _) sc h) (λ _ → os) (λ nl → ⊥-elim (notT _ nl lv)) fl eq)
    climb (d-map fr)                    (Q , hk , le) = climb fr (Q , h-map hk , le)
    climb (d-scan fr)                   (Q , hk , le) = climb fr (Q , h-scan hk , le)
    climb (d-cut fr)                    (Q , hk , le) = climb fr (Q , h-cut hk , le)
    climb (d-ln fr)                     (Q , hk , le) = climb fr (Q , h-ln hk , le)
    climb (d-take fr)                   (Q , hk , le) = climb fr (Q , h-take hk , le)
    climb (d-outer fr hl le)            (Q , hk , le′) = climb fr (_ , h-flat hk hl , ⊑-trans le (∪-⊑ le′ ⊑-refl))
    climb (d-lanes fr ho ha hb le)      (Q , hk , le′) with hl-rev ha (hl-more hk hb)
    ... | Q′ , hl , le″ = climb fr (_ , h-flat ho hl , ⊑-trans le (∪-⊑ ⊑-refl (⊑-trans (∪-⊑ ⊑-refl (∪-⊑ le′ ⊑-refl)) le″)))
    climb (d-src u hb le _)             (Q , hk , le′) = unread-up u (sh-dead hk) hb (⊑-trans le (∪-⊑ (under-⊑ le′) ⊑-refl))
    climb (d-body u sh le)              (Q , hk , le′) = unread-up u sh hk (⊑-trans le (∪-⊑ ⊑-refl le′))
    climb (f-isle u hb le na nc bh sd ss _) h = unread-up u (sh-isle na nc h bh sd ss) hb le
    climb (f-islec u hb le na cl sp tp bh sd) (Q , hk , le′) = unread-up u (sh-islec na cl sp (tailp-⊑ tp le′) hk bh sd) hb le

    unread-up : ∀ {Cr C Γ X B} {c : Ctx R Γ B} {k : CS Γ X} {o b P Ps Qb} → Unread Rt Cr C c k P → SrcH (scopeOf c) k o Ps
              → Husk (binds (CS.src k) (CS.connAt k) (CS.scope k)) b Qb → P ⊑ (Ps ∪ᵖ Qb) → Top Cr c (connS k o b)
    unread-up (un-dead fr) sh hb le = climb fr (_ , h-conn sh hb , le)
    unread-up (un-torn fr sc pt nl fl eq tp) sh hb le =
      climb fr (s-conn sc pt (λ t → ⊥-elim (notT _ nl t)) (λ t → ⊥-elim (notT _ nl t))
                       (λ _ → record { Ps = _ ; Pb = _ ; sh = sh ; bh = hb ; tl = tailp-⊑ tp le }) fl eq)

  ----------------------------------------------------------------------
  -- DOWN: every frame splits its parent's state into its hole's.

  Res : ∀ {Γ A} → Cur → Ctx R Γ A → St Γ A → Set₁
  Res {A = A} Cr c s = Σ Cur λ C → Σ Need λ N → Σ Rgn λ Rg → Σ (EmissionSet A) λ E → Fr Rt Cr C Rg c N E × Hold (scopeOf c) Rg C N s E

  -- Down through a part no live node reads.
  src-dead : ∀ {Cr C Γ X B} {c : Ctx R Γ B} {k : CS Γ X} {s b P Ps Qb} → Unread Rt Cr C c k P → SrcH (scopeOf c) k s Ps
           → Husk (binds (CS.src k) (CS.connAt k) (CS.scope k)) b Qb → P ⊑ (Ps ∪ᵖ Qb) → NoIsle b → Res Cr (inSrc k b c) s
  src-dead {C = C} u (sh-dead hk) hb le nb                    = C , dead _ , nowhere , none′ , d-src u hb le nb , (_ , hk , ⊑-refl)
  src-dead u (sh-isle na nc sy bh sd ss) hb le nb             = _ , owes , _ , _ , f-isle u hb le na nc bh sd ss nb , sy
  src-dead {C = C} u (sh-islec na cl sp tp hk bh sd) hb le _  = C , dead _ , nowhere , none′ , f-islec u hb le na cl sp tp bh sd , (_ , hk , ⊑-refl)

  body-dead : ∀ {Cr C Γ X B} {c : Ctx R Γ B} {k : CS Γ X} {o b P Ps Qb} → Unread Rt Cr C c k P → SrcH (scopeOf c) k o Ps
            → Husk (binds (CS.src k) (CS.connAt k) (CS.scope k)) b Qb → P ⊑ (Ps ∪ᵖ Qb) → Res Cr (inBody k o c) b
  body-dead {C = C} u sh hb le = C , dead _ , nowhere , none′ , d-body u sh le , (_ , hb , ⊑-refl)

  down-map : ∀ {Cr Γ A B} {f : A → B} {c : Ctx R Γ B} {s} → Res Cr c (mapS f s) → Res Cr (inMap f c) s
  down-map (C , owes , _ , _ , fr , s-map sy me sd)       = C , owes , _ , _ , f-map fr me sd , sy
  down-map (C , dead P , _ , _ , fr , (Q , h-map hk , le)) = C , dead P , nowhere , none′ , d-map fr , (Q , hk , le)
  down-map (C , dead P , _ , _ , fr , (Q , h-blank , le))  = C , dead P , nowhere , none′ , d-map fr , (Q , h-blank , le)
  down-map (_ , lane _ _ , _ , _ , _ , (_ , _ , () , _))
  down-map (_ , lanecut _ _ , _ , _ , _ , (_ , _ , () , _))
  down-map (_ , pnd _ , _ , _ , _ , (_ , () , _))

  down-scan : ∀ {Cr Γ A B} {f : B → A → B} {z} {c : Ctx R Γ B} {s} → Res Cr c (scanS f z s) → Res Cr (inScan f z c) s
  down-scan (C , owes , _ , _ , fr , s-scan sy fd eq sd)    = C , owes , _ , _ , f-scan fr fd eq sd , sy
  down-scan (C , dead P , _ , _ , fr , (Q , h-scan hk , le)) = C , dead P , nowhere , none′ , d-scan fr , (Q , hk , le)
  down-scan (C , dead P , _ , _ , fr , (Q , h-blank , le))   = C , dead P , nowhere , none′ , d-scan fr , (Q , h-blank , le)
  down-scan (_ , lane _ _ , _ , _ , _ , (_ , _ , () , _))
  down-scan (_ , lanecut _ _ , _ , _ , _ , (_ , _ , () , _))
  down-scan (_ , pnd _ , _ , _ , _ , (_ , () , _))

  down-cut : ∀ {Cr Γ A} {l a} {c : Ctx R Γ A} {s} → Res Cr c (cutS l a s) → Res Cr (inCut l a c) s
  down-cut (C , owes , _ , _ , fr , s-cut sy)                 = C , owes , _ , _ , f-cut fr , sy
  down-cut (C , dead P , _ , _ , fr , (Q , h-cut hk , le))     = C , dead P , nowhere , none′ , d-cut fr , (Q , hk , le)
  down-cut (C , dead P , _ , _ , fr , (Q , h-blank , le))      = C , dead P , nowhere , none′ , d-cut fr , (Q , h-blank , le)
  down-cut (_ , lane _ _ , _ , _ , _ , (_ , _ , () , _))
  down-cut (C , lanecut b P , _ , _ , fr , (_ , _ , refl , h)) = C , onoff b P , _ , _ , f-lnct fr , lh-hold b h
  down-cut (_ , pnd _ , _ , _ , _ , (_ , () , _))

  down-ln : ∀ {Cr Γ A} {b} {c : Ctx R Γ A} {s} → Res Cr c (lnS b s) → Res Cr (inLn b c) s
  down-ln (_ , owes , _ , _ , _ , ())
  down-ln (C , dead P , _ , _ , fr , (Q , h-ln hk , le))     = C , dead P , nowhere , none′ , d-ln fr , (Q , hk , le)
  down-ln (C , dead P , _ , _ , fr , (Q , h-blank , le))     = C , dead P , nowhere , none′ , d-ln fr , (Q , h-blank , le)
  down-ln (C , lane b P , _ , _ , fr , (at , l , refl , h))  = C , lanecut b P , _ , _ , f-lane fr , (at , l , refl , h)
  down-ln (_ , lanecut _ _ , _ , _ , _ , (_ , _ , () , _))
  down-ln (_ , pnd _ , _ , _ , _ , (_ , () , _))

  down-take : ∀ {Cr Γ A} {i keep w} {c : Ctx R Γ A} {s} → Res Cr c (takeS i keep w s) → Res Cr (inTake i keep w c) s
  down-take (C , owes , _ , _ , fr , s-take sy nf eq sd)            = C , owes , _ , _ , f-take fr nf eq sd , sy
  down-take (C , owes , _ , _ , fr , s-took fl nr fz ow tp hk eq sd) = C , dead _ , nowhere , none′ , f-took fr fl nr fz ow tp eq sd , (_ , hk , ⊑-refl)
  down-take (C , dead P , _ , _ , fr , (Q , h-take hk , le))        = C , dead P , nowhere , none′ , d-take fr , (Q , hk , le)
  down-take (C , dead P , _ , _ , fr , (Q , h-blank , le))          = C , dead P , nowhere , none′ , d-take fr , (Q , h-blank , le)
  down-take (_ , lane _ _ , _ , _ , _ , (_ , _ , () , _))
  down-take (_ , lanecut _ _ , _ , _ , _ , (_ , _ , () , _))
  down-take (_ , pnd _ , _ , _ , _ , (_ , () , _))

  down-outer : ∀ {Cr Γ A B} {op} {f} {ω} {d n qu ls} {c : Ctx R Γ B} {s : St Γ A}
             → Res Cr c (flatS op f ω d n qu s ls) → Res Cr (inOuter op f ω d n qu ls c) s
  down-outer (C , owes , _ , _ , fr , s-flat ji sy j eq sd bh)    = C , owes , _ , _ , f-outer fr ji j eq sd bh , sy
  down-outer (C , dead P , _ , _ , fr , (Q , h-flat ho hl , le))  = C , dead _ , nowhere , none′ , d-outer fr hl le , (_ , ho , ⊑-refl)
  down-outer {ls = ls} (C , dead P , _ , _ , fr , (Q , h-blank , le)) with hl-blank ls
  ... | _ , hl , _ = C , dead ∅ᵖ , nowhere , none′ , d-outer fr hl (⊑-trans le ∅-⊑) , (_ , h-blank , ⊑-refl)
  down-outer (_ , lane _ _ , _ , _ , _ , (_ , _ , () , _))
  down-outer (_ , lanecut _ _ , _ , _ , _ , (_ , _ , () , _))
  down-outer (_ , pnd _ , _ , _ , _ , (_ , () , _))

  down-lanes : ∀ {Cr Γ A B} {op} {f} {ω} {d n qu} {o : St Γ A} {pre post} {c : Ctx R Γ B} {s}
             → Res Cr c (flatS op f ω d n qu o (pre ʳ++ s ∷ post)) → Res Cr (inLanes op f ω d n qu o pre post c) s
  down-lanes {pre = pre} (C , owes , _ , _ , fr , s-flat ji sy (joined bg wt wh od ah ao en li) eq so bh)
    with begun-split (reverse pre) (subst (λ ls → Begun _ _ _ _ _ _ ls _) (ʳ++-defn pre) bg)
  ... | split lf o nq r l rt cnt refl with laneHold l
  ...   | _ , _ , hl , hd , sd = C , lane _ _ , _ , _ , f-lanes fr ji sy lf o nq r hl rt cnt wt wh od ah ao en li eq so sd bh , hd
  down-lanes {pre = pre} (C , dead P , _ , _ , fr , (Q , h-flat ho hl , le)) with hl-unrev pre hl
  ... | _ , _ , ha , hl-more hs hb , le′ = C , dead _ , nowhere , none′ , d-lanes fr ho ha hb (⊑-trans le (∪-⊑ ⊑-refl le′)) , (_ , hs , ⊑-refl)
  down-lanes {pre = pre} {post = post} (C , dead P , _ , _ , fr , (Q , h-blank , le)) with hl-blank pre | hl-blank post
  ... | _ , ha , _ | _ , hb , _ = C , dead ∅ᵖ , nowhere , none′ , d-lanes fr h-blank ha hb (⊑-trans le ∅-⊑) , (_ , h-blank , ⊑-refl)
  down-lanes (_ , lane _ _ , _ , _ , _ , (_ , _ , () , _))
  down-lanes (_ , lanecut _ _ , _ , _ , _ , (_ , _ , () , _))
  down-lanes (_ , pnd _ , _ , _ , _ , (_ , () , _))

  down-src : ∀ {Cr Γ X B} {k : CS Γ X} {b} {c : Ctx R Γ B} {s} → (Pending s → ⊥) → NoIsle b → Res Cr c (connS k s b) → Res Cr (inSrc k b c) s
  down-src {k = k} np nb (C , owes , _ , _ , fr , s-conn sc pt bs os tn fl eq) with live? (CS.srcLive k)
  ... | inj₂ nl = let t = tn nl in src-dead (un-torn fr sc pt nl fl eq (Torn.tl t)) (Torn.sh t) (Torn.bh t) ⊑-refl nb
  ... | inj₁ lv with os lv
  ...   | src-on nc sy bh sd         = C , owes , _ , _ , f-src fr sc pt lv nc (bs lv) fl ≈-refl eq bh sd nb , sy
  ...   | src-shut cl sp tp hk bh sd = C , dead _ , nowhere , none′ , f-srcc fr sc pt lv cl sp tp bh sd (bs lv) fl eq , (_ , hk , ⊑-refl)
  ...   | src-pend _ _ _ _ _ _       = ⊥-elim (np pd)
  down-src _ nb (C , dead P , _ , _ , fr , (Q , h-conn sh hb , le)) = src-dead (un-dead fr) sh hb le nb
  down-src _ nb (C , dead P , _ , _ , fr , (Q , h-blank , le))     =
    C , dead ∅ᵖ , nowhere , none′ , d-src (un-dead fr) h-blank (⊑-trans le ∅-⊑) nb , (_ , h-blank , ⊑-refl)
  down-src _ _ (_ , lane _ _ , _ , _ , _ , (_ , _ , () , _))
  down-src _ _ (_ , lanecut _ _ , _ , _ , _ , (_ , _ , () , _))
  down-src _ _ (_ , pnd _ , _ , _ , _ , (_ , () , _))

  down-body : ∀ {Cr Γ X B} {k : CS Γ X} {o} {c : Ctx R Γ B} {s} → Res Cr c (connS k o s) → Res Cr (inBody k o c) s
  down-body {k = k} {s = s} (C , owes , _ , _ , fr , s-conn sc pt bs os tn fl eq) with live? (CS.srcLive k)
  ... | inj₂ nl = let t = tn nl in body-dead (un-torn fr sc pt nl fl eq (Torn.tl t)) (Torn.sh t) (Torn.bh t) ⊑-refl
  ... | inj₁ lv = C , owes , _ , _ , f-body fr sc pt lv (os lv) fl eq , subst (λ x → Sync (binds (CS.src k) (CS.connAt k) x) _ C s _) (sym sc) (bs lv)
  down-body (C , dead P , _ , _ , fr , (Q , h-conn sh hb , le)) = body-dead (un-dead fr) sh hb le
  down-body (C , dead P , _ , _ , fr , (Q , h-blank , le))     =
    C , dead ∅ᵖ , nowhere , none′ , d-body (un-dead fr) (sh-dead h-blank) (⊑-trans le ∅-⊑) , (_ , h-blank , ⊑-refl)
  down-body (_ , lane _ _ , _ , _ , _ , (_ , _ , () , _))
  down-body (_ , lanecut _ _ , _ , _ , _ , (_ , _ , () , _))
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
