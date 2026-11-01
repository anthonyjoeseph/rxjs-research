{-# OPTIONS --guardedness #-}

-- THE WALK: the frames above a hole and the hole's state, zipped up into
-- the whole tree in step at the root, and the whole tree unzipped down
-- to any hole.  So the invariant at one focus is the invariant at every
-- focus of the same tree, at the same cursor.
module adequacy.Walk where

open import Data.Bool using (T; true; false; not; _∧_)
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
open import adequacy.Rows using (_≃_; _⇄_; ≃-refl; ≃-sym; ≃-trans)
open import adequacy.Cursor using (Cur; Rgn; notT; Owes; Due; Spent; _≈_; Pol; Runs; Hole; LaneSt; l-live; l-dead; Begun; none; more; bump;
  joined; Sync; Sound; src-pend; src-on; src-shut; s-cold; s-of; s-done; s-map; s-scan; s-cut; s-take; s-took;
  s-flat; s-conn; s-join; s-joinx; Need; owes; lane; lanecut; pnd; Hold; u-map; u-scan; u-cut;
  u-ln; u-take; u-outer; u-lanes; u-src; u-body; Fr; f-top; f-off; f-map; f-scan; f-cut;
  f-take; f-took; f-outer; f-lanes; f-lane; f-lnct; f-src; f-srcc; f-srcp; f-srcx; f-body; Inv;
  settled; c-abs)
open _≃_

------------------------------------------------------------------------
-- Entries alike in every visible row tie a state alike.

due-≈ : ∀ {A} {C} {E E′ : EmissionSet A} → E ≈ E′ → Due C E ≃ Due C E′
due-≈ eq = (λ (x , v , o) → let (y , v′) = to eq (x , v) in y , v′ , o)
         ⇄ (λ (x , v , o) → let (y , v′) = from eq (x , v) in y , v′ , o)

spent-≈ : ∀ {A} {C} {E E′ : EmissionSet A} → Spent C E → E ≈ E′ → Spent C E′
spent-≈ {C = C} sp eq d = sp (from (due-≈ {C = C} eq) d)

sync-≈ : ∀ {Γ} {sc : Scope Γ} {Rg C A} {s : St Γ A} {E E′} → Sync sc Rg C s E → E ≈ E′ → Sync sc Rg C s E′
sync-≈ {C = C} (s-cold tk d) e = s-cold tk (≃-trans (≃-sym (due-≈ {C = C} e)) d)
sync-≈ {C = C} (s-of d)   e = s-of (≃-trans (≃-sym (due-≈ {C = C} e)) d)
sync-≈ {C = C} (s-done sp) e = s-done (spent-≈ {C = C} sp e)
sync-≈ (s-map sy eq sd)      e = s-map sy (≃-trans eq e) sd
sync-≈ (s-scan sy fd eq sd)  e = s-scan sy fd (≃-trans eq e) sd
sync-≈ (s-cut sy)            e = s-cut (sync-≈ sy e)
sync-≈ (s-take sy nf eq sd)  e = s-take sy nf (≃-trans eq e) sd
sync-≈ (s-took fl nr fz ow eq sd) e = s-took fl (λ {q} → nr {q}) fz ow (≃-trans eq e) sd
sync-≈ (s-flat sy j eq sd)   e = s-flat sy j (≃-trans eq e) sd
sync-≈ (s-conn sc pt b o fl eq) e = s-conn sc pt b o fl (≃-trans eq e)
sync-≈ {C = C} (s-join eq d ap lt a) e = s-join (≃-trans eq e) (≃-trans (≃-sym (due-≈ {C = C} e)) d) ap lt a
sync-≈ {C = C} (s-joinx sp) e = s-joinx (spent-≈ {C = C} sp e)

------------------------------------------------------------------------
-- A joiner's begun lanes, cut at one lane and put back.

bump-+ : ∀ b m k → bump b (m + k) ≡ bump b m + k
bump-+ true  m k = refl
bump-+ false m k = refl

data Split {Γ A B} (sc : Scope Γ) (Rg : Rgn) (C : Cur) (P : Pol A B) (O : EmissionSet A)
           (xs : List (St Γ B)) (s : St Γ B) (post : List (St Γ B)) (vs : List (Pos × A)) (n : ℕ) : Set₁ where
  split : ∀ {vs₁ vs₂ n₁ n₂ q a b}
        → Begun sc Rg C P O vs₁ xs n₁ → O q (out a) → (Owes C q → ⊥) → Runs P q → LaneSt sc Rg C P q a s b
        → Begun sc Rg C P O vs₂ post n₂ → n ≡ n₁ + bump b n₂ → vs ≡ vs₁ ++ (q , a) ∷ vs₂
        → Split sc Rg C P O xs s post vs n

begun-split : ∀ {Γ A B} {sc : Scope Γ} {Rg C} {P : Pol A B} {O} xs {s post vs n}
            → Begun sc Rg C P O vs (xs ++ s ∷ post) n → Split sc Rg C P O xs s post vs n
begun-split []       (more o nq r l bg) = split none o nq r l bg refl refl
begun-split (x ∷ xs) (more {b = b′} o nq r l bg) with begun-split xs bg
... | split {n₁ = n₁} {n₂} {b = b} lf o′ nq′ r′ l′ rt refl refl =
  split (more o nq r l lf) o′ nq′ r′ l′ rt (bump-+ b′ n₁ (bump b n₂)) refl

begun-join : ∀ {Γ A B} {sc : Scope Γ} {Rg C} {P : Pol A B} {O} {xs s post vs₁ vs₂ n₁ n₂ q a b}
           → Begun sc Rg C P O vs₁ xs n₁ → O q (out a) → (Owes C q → ⊥) → Runs P q → LaneSt sc Rg C P q a s b
           → Begun sc Rg C P O vs₂ post n₂ → Begun sc Rg C P O (vs₁ ++ (q , a) ∷ vs₂) (xs ++ s ∷ post) (n₁ + bump b n₂)
begun-join none o nq r l rt = more o nq r l rt
begun-join {n₂ = n₂} {b = b} (more {b = b′} {n = n₁} o′ nq′ r′ l′ lf) o nq r l rt =
  subst (Begun _ _ _ _ _ _ _) (bump-+ b′ n₁ (bump b n₂)) (more o′ nq′ r′ l′ (begun-join lf o nq r l rt))

-- A lane's state as its list entry holds it.
laneSt : ∀ {Γ A B} {sc : Scope Γ} {Rg C} {P : Pol A B} {q a} b {at l E}
       → Hole C P q a E b → (T b → Sync sc Rg C l E) → (T b → Sound Rg E) → LaneSt sc Rg C P q a (lnS b (cutS b at l)) b
laneSt true  hl h sd = l-live hl (h _) (sd _)
laneSt false hl h _  = l-dead hl

laneHold : ∀ {Γ A B} {sc : Scope Γ} {Rg C} {P : Pol A B} {q a s b}
         → LaneSt sc Rg C P q a s b → Σ (EmissionSet B) λ E → Hole C P q a E b × Hold sc Rg C (lane b) s E × (T b → Sound Rg E)
laneHold (l-live hl sy sd) = _ , hl , (_ , _ , refl , λ _ → sy) , λ _ → sd
laneHold (l-dead hl)       = _ , hl , (_ , _ , refl , λ ()) , λ ()

live? : ∀ b → T b ⊎ T (not b)
live? true  = inj₁ _
live? false = inj₂ _

none′ : ∀ {A : Set} → EmissionSet A
none′ _ _ = ⊥

nowhere : Rgn
nowhere _ = ⊥

both : ∀ w v → T w → T v → T (w ∧ v)
both true  _ _ x = x
both false _ () _

module _ {R : Set} (Rt : EmissionSet R) where

  ----------------------------------------------------------------------
  -- UP: every frame composes its hole's state into its parent's.

  climb : ∀ {C Γ A} {c : Ctx R Γ A} {Rg w E s} → Fr Rt C Rg c w E → Hold (scopeOf c) Rg C w s E
        → Σ Rgn λ Rg₀ → Σ (EmissionSet R) λ E′ → E′ ≈ Rt × Sync unbound Rg₀ C (plug c s) E′
  climb (f-top eq)                    h = _ , _ , eq , h _
  climb (f-off u-map fr)              h = climb fr λ ()
  climb (f-off u-scan fr)             h = climb fr λ ()
  climb (f-off u-cut fr)              h = climb fr λ ()
  climb (f-off u-ln fr)               h = climb fr λ ()
  climb (f-off u-take fr)             h = climb fr λ ()
  climb (f-off u-outer fr)            h = climb fr λ ()
  climb (f-off u-lanes fr)            h = climb fr λ ()
  climb (f-off u-src fr)              h = climb fr λ ()
  climb (f-off u-body fr)             h = climb fr λ ()
  climb (f-map fr eq sd)              h = climb fr λ t → s-map (h t) eq sd
  climb (f-scan fr fd eq sd)          h = climb fr λ t → s-scan (h t) fd eq sd
  climb (f-cut fr)                    h = climb fr λ t → s-cut (h t)
  climb (f-take fr nf eq sd)          h = climb fr λ t → s-take (h t) nf eq sd
  climb (f-took fr fl nr fz ow eq sd) h = climb fr λ _ → s-took fl (λ {q} → nr {q}) fz ow eq sd
  climb (f-outer fr j eq sd)          h = climb fr λ t → s-flat (h t) j eq sd
  climb (f-lanes {pre = pre} {b = b} fr sy lf o nq r hl rt cnt wt wh od ah en li eq so sd) (_ , _ , refl , h) =
    climb fr λ _ → s-flat sy (joined bg wt wh od ah en li) eq so
    where
      bg = subst (Begun _ _ _ _ _ _ _) (sym cnt)
             (subst (λ ls → Begun _ _ _ _ _ _ ls _) (sym (ʳ++-defn pre)) (begun-join lf o nq r (laneSt b hl h sd) rt))
  climb (f-lane fr)                   (at , l , refl , h) = climb fr (at , l , refl , h)
  climb (f-lnct fr)                   h = climb fr (_ , _ , refl , h)
  climb (f-src fr sc pt lv nc bs fl fe eq) h = climb fr λ t → s-conn sc pt (λ _ → bs) (λ _ → src-on nc (sync-≈ (h t) (≃-sym fe))) fl eq
  climb (f-srcc fr sc pt lv cl sp bs fl eq) h = climb fr λ _ → s-conn sc pt (λ _ → bs) (λ _ → src-shut cl sp) fl eq
  climb (f-srcp fr sc pt lv ba adm bs fl fe eq) (_ , refl , pe , wn) =
    climb fr λ _ → s-conn sc pt (λ _ → bs) (λ _ → src-pend ba adm (≃-trans pe (≃-sym fe)) wn) fl eq
  climb (f-srcx fr sc pt nl fl eq)    h = climb fr λ _ → s-conn sc pt (λ lv → ⊥-elim (notT _ nl lv)) (λ lv → ⊥-elim (notT _ nl lv)) fl eq
  climb (f-body {k = k} {w = w} fr sc pt ev os fl eq) h =
    climb fr λ t → s-conn sc pt (λ lv → subst (λ x → Sync (binds (CS.src k) (CS.connAt k) x) _ _ _ _) sc (h (subst T (sym ev) (both w (CS.srcLive k) t lv)))) os fl eq

  ----------------------------------------------------------------------
  -- DOWN: every frame splits its parent's state into its hole's.

  Res : ∀ {Γ A} → Cur → Ctx R Γ A → St Γ A → Set₁
  Res {A = A} C c s = Σ Need λ w → Σ Rgn λ Rg → Σ (EmissionSet A) λ E → Fr Rt C Rg c w E × Hold (scopeOf c) Rg C w s E

  down-map : ∀ {C Γ A B} {f : A → B} {c : Ctx R Γ B} {s} → Res C c (mapS f s) → Res C (inMap f c) s
  down-map (owes true , _ , _ , fr , h) with h _
  ... | s-map sy me sd = owes true , _ , _ , f-map fr me sd , λ _ → sy
  down-map (owes false , _ , _ , fr , _)            = owes false , nowhere , none′ , f-off u-map fr , λ ()
  down-map (lane _ , _ , _ , _ , (_ , _ , () , _))
  down-map (lanecut _ , _ , _ , _ , (_ , _ , () , _))
  down-map (pnd _ , _ , _ , _ , (_ , () , _))

  down-scan : ∀ {C Γ A B} {f : B → A → B} {z} {c : Ctx R Γ B} {s} → Res C c (scanS f z s) → Res C (inScan f z c) s
  down-scan (owes true , _ , _ , fr , h) with h _
  ... | s-scan sy fd eq sd = owes true , _ , _ , f-scan fr fd eq sd , λ _ → sy
  down-scan (owes false , _ , _ , fr , _)            = owes false , nowhere , none′ , f-off u-scan fr , λ ()
  down-scan (lane _ , _ , _ , _ , (_ , _ , () , _))
  down-scan (lanecut _ , _ , _ , _ , (_ , _ , () , _))
  down-scan (pnd _ , _ , _ , _ , (_ , () , _))

  down-cut : ∀ {C Γ A} {l a} {c : Ctx R Γ A} {s} → Res C c (cutS l a s) → Res C (inCut l a c) s
  down-cut (owes true , _ , _ , fr , h) with h _
  ... | s-cut sy = owes true , _ , _ , f-cut fr , λ _ → sy
  down-cut (owes false , _ , _ , fr , _)                  = owes false , nowhere , none′ , f-off u-cut fr , λ ()
  down-cut (lane _ , _ , _ , _ , (_ , _ , () , _))
  down-cut (lanecut b , _ , _ , fr , (_ , _ , refl , h))  = owes b , _ , _ , f-lnct fr , h
  down-cut (pnd _ , _ , _ , _ , (_ , () , _))

  down-ln : ∀ {C Γ A} {b} {c : Ctx R Γ A} {s} → Res C c (lnS b s) → Res C (inLn b c) s
  down-ln (owes true , _ , _ , fr , h) with h _
  ... | ()
  down-ln (owes false , _ , _ , fr , _)                  = owes false , nowhere , none′ , f-off u-ln fr , λ ()
  down-ln (lane b , _ , _ , fr , (at , l , refl , h))    = lanecut b , _ , _ , f-lane fr , (at , l , refl , h)
  down-ln (lanecut _ , _ , _ , _ , (_ , _ , () , _))
  down-ln (pnd _ , _ , _ , _ , (_ , () , _))

  down-take : ∀ {C Γ A} {i keep w} {c : Ctx R Γ A} {s} → Res C c (takeS i keep w s) → Res C (inTake i keep w c) s
  down-take (owes true , _ , _ , fr , h) with h _
  ... | s-take sy nf eq sd   = owes true , _ , _ , f-take fr nf eq sd , λ _ → sy
  ... | s-took fl nr fz ow eq sd = owes false , nowhere , none′ , f-took fr fl nr fz ow eq sd , λ ()
  down-take (owes false , _ , _ , fr , _)            = owes false , nowhere , none′ , f-off u-take fr , λ ()
  down-take (lane _ , _ , _ , _ , (_ , _ , () , _))
  down-take (lanecut _ , _ , _ , _ , (_ , _ , () , _))
  down-take (pnd _ , _ , _ , _ , (_ , () , _))

  down-outer : ∀ {C Γ A B} {op} {f} {d n qu ls} {c : Ctx R Γ B} {s : St Γ A}
             → Res C c (flatS op f d n qu s ls) → Res C (inOuter op f d n qu ls c) s
  down-outer (owes true , _ , _ , fr , h) with h _
  ... | s-flat sy j eq sd = owes true , _ , _ , f-outer fr j eq sd , λ _ → sy
  down-outer (owes false , _ , _ , fr , _)            = owes false , nowhere , none′ , f-off u-outer fr , λ ()
  down-outer (lane _ , _ , _ , _ , (_ , _ , () , _))
  down-outer (lanecut _ , _ , _ , _ , (_ , _ , () , _))
  down-outer (pnd _ , _ , _ , _ , (_ , () , _))

  down-lanes : ∀ {C Γ A B} {op} {f} {d n qu} {o : St Γ A} {pre post} {c : Ctx R Γ B} {s}
             → Res C c (flatS op f d n qu o (pre ʳ++ s ∷ post)) → Res C (inLanes op f d n qu o pre post c) s
  down-lanes {pre = pre} (owes true , _ , _ , fr , h) with h _
  ... | s-flat sy (joined bg wt wh od ah en li) eq so
    with begun-split (reverse pre) (subst (λ ls → Begun _ _ _ _ _ _ ls _) (ʳ++-defn pre) bg)
  ...   | split lf o nq r l rt cnt refl with laneHold l
  ...     | _ , hl , hd , sd = lane _ , _ , _ , f-lanes fr sy lf o nq r hl rt cnt wt wh od ah en li eq so sd , hd
  down-lanes (owes false , _ , _ , fr , _)            = owes false , nowhere , none′ , f-off u-lanes fr , λ ()
  down-lanes (lane _ , _ , _ , _ , (_ , _ , () , _))
  down-lanes (lanecut _ , _ , _ , _ , (_ , _ , () , _))
  down-lanes (pnd _ , _ , _ , _ , (_ , () , _))

  down-src : ∀ {C Γ X B} {k : CS Γ X} {b} {c : Ctx R Γ B} {s} → Res C c (connS k s b) → Res C (inSrc k b c) s
  down-src {k = k} (owes true , _ , _ , fr , h) with h _
  ... | s-conn sc pt bs os fl eq with live? (CS.srcLive k)
  ...   | inj₂ nl = owes false , _ , none′ , f-srcx fr sc pt nl fl eq , λ ()
  ...   | inj₁ lv with os lv
  ...     | src-on nc sy        = owes true , _ , _ , f-src fr sc pt lv nc (bs lv) fl ≃-refl eq , λ _ → sy
  ...     | src-shut cl sp      = owes false , _ , none′ , f-srcc fr sc pt lv cl sp (bs lv) fl eq , λ ()
  ...     | src-pend ba adm pe wn = pnd _ , _ , _ , f-srcp fr sc pt lv ba adm (bs lv) fl ≃-refl eq , (_ , refl , pe , wn)
  down-src (owes false , _ , _ , fr , _)            = owes false , nowhere , none′ , f-off u-src fr , λ ()
  down-src (lane _ , _ , _ , _ , (_ , _ , () , _))
  down-src (lanecut _ , _ , _ , _ , (_ , _ , () , _))
  down-src (pnd _ , _ , _ , _ , (_ , () , _))

  down-body : ∀ {C Γ X B} {k : CS Γ X} {o} {c : Ctx R Γ B} {s} → Res C c (connS k o s) → Res C (inBody k o c) s
  down-body {C = C} {k = k} {s = s} (owes true , _ , _ , fr , h) with h _
  ... | s-conn sc pt bs os fl eq =
    owes (CS.srcLive k) , _ , _ , f-body fr sc pt refl os fl eq , λ lv → subst (λ x → Sync (binds (CS.src k) (CS.connAt k) x) _ C s _) (sym sc) (bs lv)
  down-body (owes false , _ , _ , fr , _)            = owes false , nowhere , none′ , f-off u-body fr , λ ()
  down-body (lane _ , _ , _ , _ , (_ , _ , () , _))
  down-body (lanecut _ , _ , _ , _ , (_ , _ , () , _))
  down-body (pnd _ , _ , _ , _ , (_ , () , _))

  descend : ∀ {C Γ A} (c : Ctx R Γ A) s {Rg E} → Sync unbound Rg C (plug c s) E → E ≈ Rt → Res C c s
  descend top                               s sy eq = owes true , _ , _ , f-top eq , λ _ → sy
  descend (inMap f c)                       s sy eq = down-map (descend c _ sy eq)
  descend (inScan f z c)                    s sy eq = down-scan (descend c _ sy eq)
  descend (inCut l a c)                     s sy eq = down-cut (descend c _ sy eq)
  descend (inLn b c)                        s sy eq = down-ln (descend c _ sy eq)
  descend (inTake i p w c)                  s sy eq = down-take (descend c _ sy eq)
  descend (inOuter op f d n q ls c)         s sy eq = down-outer (descend c _ sy eq)
  descend (inLanes op f d n q o pre post c) s sy eq = down-lanes (descend c _ sy eq)
  descend (inSrc k b c)                     s sy eq = down-src (descend c _ sy eq)
  descend (inBody k o c)                    s sy eq = down-body (descend c _ sy eq)

  ----------------------------------------------------------------------
  -- REFOCUSING keeps the invariant: the same tree, the same cursor.

  refocus : ∀ {C Γ A Γ′ A′} {c : Ctx R Γ A} {c′ : Ctx R Γ′ A′} {s s′ r}
          → Inv Rt C ⟨ c , s , absorbed , r ⟩ → plug c′ s′ ≡ plug c s → Inv Rt C ⟨ c′ , s′ , absorbed , r ⟩
  refocus {c′ = c′} {s′ = s′} (settled _ fr h) eq with climb fr h
  ... | _ , _ , top≈ , sy with descend c′ s′ (subst (λ t → Sync unbound _ _ t _) (sym eq) sy) top≈
  ...   | _ , _ , _ , fr′ , h′ = settled c-abs fr′ h′
