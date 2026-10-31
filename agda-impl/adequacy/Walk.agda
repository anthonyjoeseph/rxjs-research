{-# OPTIONS --guardedness #-}

-- THE WALK: the frames above a hole and the hole's state, zipped up into
-- the whole tree in step at the root, and the whole tree unzipped down
-- to any hole.  So the invariant at one focus is the invariant at every
-- focus of the same tree, at the same cursor.
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
open import adequacy.Rows using (_≃_; _⇄_; ≃-refl; ≃-sym; ≃-trans)
open import adequacy.Cursor using (Cur; Owes; Due; Spent; _≈_; Pol; Runs; Hole; LaneSt; l-live; l-dead; Begun; none; more; bump;
  joined; Sync; s-pend; s-cold; s-of; s-done; s-map; s-scan; s-cut; s-take; s-took; s-flat;
  s-conn; s-join; s-joinx; Need; owes; lane; lanecut; Hold; u-map; u-scan; u-cut; u-ln; u-take;
  u-outer; u-lanes; u-src; u-body; Fr; f-top; f-off; f-map; f-scan; f-cut; f-take; f-took;
  f-outer; f-lanes; f-lane; f-lnct; f-src; f-srcx; f-body; Inv; settled; c-abs)
open _≃_

------------------------------------------------------------------------
-- Entries alike in every visible row tie a state alike.

due-≈ : ∀ {A} {C} {E E′ : EmissionSet A} → E ≈ E′ → Due C E ≃ Due C E′
due-≈ eq = (λ (x , v , o) → let (y , v′) = to eq (x , v) in y , v′ , o)
         ⇄ (λ (x , v , o) → let (y , v′) = from eq (x , v) in y , v′ , o)

spent-≈ : ∀ {A} {C} {E E′ : EmissionSet A} → Spent C E → E ≈ E′ → Spent C E′
spent-≈ {C = C} sp eq d = sp (from (due-≈ {C = C} eq) d)

sync-≈ : ∀ {Γ} {sc : Scope Γ} {C A} {s : St Γ A} {E E′} → Sync sc C s E → E ≈ E′ → Sync sc C s E′
sync-≈ (s-pend o ok adm eq)  e = s-pend o ok adm (≃-trans eq e)
sync-≈ {C = C} (s-cold d) e = s-cold (≃-trans (≃-sym (due-≈ {C = C} e)) d)
sync-≈ {C = C} (s-of d)   e = s-of (≃-trans (≃-sym (due-≈ {C = C} e)) d)
sync-≈ {C = C} (s-done sp) e = s-done (spent-≈ {C = C} sp e)
sync-≈ (s-map sy eq)         e = s-map sy (≃-trans eq e)
sync-≈ (s-scan sy fd eq)     e = s-scan sy fd (≃-trans eq e)
sync-≈ (s-cut sy)            e = s-cut (sync-≈ sy e)
sync-≈ (s-take sy nf eq)     e = s-take sy nf (≃-trans eq e)
sync-≈ (s-took fl nr ow eq)  e = s-took fl nr ow (≃-trans eq e)
sync-≈ (s-flat sy j eq)      e = s-flat sy j (≃-trans eq e)
sync-≈ (s-conn sc b o fl eq) e = s-conn sc b o fl (≃-trans eq e)
sync-≈ {C = C} (s-join eq d ap lt a) e = s-join (≃-trans eq e) (≃-trans (≃-sym (due-≈ {C = C} e)) d) ap lt a
sync-≈ {C = C} (s-joinx sp) e = s-joinx (spent-≈ {C = C} sp e)

------------------------------------------------------------------------
-- A joiner's begun lanes, cut at one lane and put back.

bump-+ : ∀ b m k → bump b (m + k) ≡ bump b m + k
bump-+ true  m k = refl
bump-+ false m k = refl

data Split {Γ A B} (sc : Scope Γ) (C : Cur) (P : Pol A B) (O : EmissionSet A)
           (xs : List (St Γ B)) (s : St Γ B) (post : List (St Γ B)) (vs : List (Pos × A)) (n : ℕ) : Set₁ where
  split : ∀ {vs₁ vs₂ n₁ n₂ q a b}
        → Begun sc C P O vs₁ xs n₁ → O q (out a) → (Owes C q → ⊥) → Runs P q → LaneSt sc C P q a s b
        → Begun sc C P O vs₂ post n₂ → n ≡ n₁ + bump b n₂ → vs ≡ vs₁ ++ (q , a) ∷ vs₂
        → Split sc C P O xs s post vs n

begun-split : ∀ {Γ A B} {sc : Scope Γ} {C} {P : Pol A B} {O} xs {s post vs n}
            → Begun sc C P O vs (xs ++ s ∷ post) n → Split sc C P O xs s post vs n
begun-split []       (more o nq r l bg) = split none o nq r l bg refl refl
begun-split (x ∷ xs) (more {b = b′} o nq r l bg) with begun-split xs bg
... | split {n₁ = n₁} {n₂} {b = b} lf o′ nq′ r′ l′ rt refl refl =
  split (more o nq r l lf) o′ nq′ r′ l′ rt (bump-+ b′ n₁ (bump b n₂)) refl

begun-join : ∀ {Γ A B} {sc : Scope Γ} {C} {P : Pol A B} {O} {xs s post vs₁ vs₂ n₁ n₂ q a b}
           → Begun sc C P O vs₁ xs n₁ → O q (out a) → (Owes C q → ⊥) → Runs P q → LaneSt sc C P q a s b
           → Begun sc C P O vs₂ post n₂ → Begun sc C P O (vs₁ ++ (q , a) ∷ vs₂) (xs ++ s ∷ post) (n₁ + bump b n₂)
begun-join none o nq r l rt = more o nq r l rt
begun-join {n₂ = n₂} {b = b} (more {b = b′} {n = n₁} o′ nq′ r′ l′ lf) o nq r l rt =
  subst (Begun _ _ _ _ _ _) (bump-+ b′ n₁ (bump b n₂)) (more o′ nq′ r′ l′ (begun-join lf o nq r l rt))

-- A lane's state as its list entry holds it.
laneSt : ∀ {Γ A B} {sc : Scope Γ} {C} {P : Pol A B} {q a} b {at l E}
       → Hole C P q a E b → (T b → Sync sc C l E) → LaneSt sc C P q a (lnS b (cutS b at l)) b
laneSt true  hl h = l-live hl (h _)
laneSt false hl h = l-dead hl

laneHold : ∀ {Γ A B} {sc : Scope Γ} {C} {P : Pol A B} {q a s b}
         → LaneSt sc C P q a s b → Σ (EmissionSet B) λ E → Hole C P q a E b × Hold sc C (lane b) s E
laneHold (l-live hl sy) = _ , hl , (_ , _ , refl , λ _ → sy)
laneHold (l-dead hl)    = _ , hl , (_ , _ , refl , λ ())

live? : ∀ b → T b ⊎ T (not b)
live? true  = inj₁ _
live? false = inj₂ _

notT : ∀ b → T (not b) → T b → ⊥
notT true  () _
notT false _  ()

none′ : ∀ {A : Set} → EmissionSet A
none′ _ _ = ⊥

module _ {R : Set} (Rt : EmissionSet R) where

  ----------------------------------------------------------------------
  -- UP: every frame composes its hole's state into its parent's.

  climb : ∀ {C Γ A} {c : Ctx R Γ A} {w E s} → Fr Rt C c w E → Hold (scopeOf c) C w s E
        → Σ (EmissionSet R) λ E′ → E′ ≈ Rt × Sync unbound C (plug c s) E′
  climb (f-top eq)                    h = _ , eq , h _
  climb (f-off u-map fr)              h = climb fr λ ()
  climb (f-off u-scan fr)             h = climb fr λ ()
  climb (f-off u-cut fr)              h = climb fr λ ()
  climb (f-off u-ln fr)               h = climb fr λ ()
  climb (f-off u-take fr)             h = climb fr λ ()
  climb (f-off u-outer fr)            h = climb fr λ ()
  climb (f-off u-lanes fr)            h = climb fr λ ()
  climb (f-off u-src fr)              h = climb fr λ ()
  climb (f-off u-body fr)             h = climb fr λ ()
  climb (f-map fr eq)                 h = climb fr λ t → s-map (h t) eq
  climb (f-scan fr fd eq)             h = climb fr λ t → s-scan (h t) fd eq
  climb (f-cut fr)                    h = climb fr λ t → s-cut (h t)
  climb (f-take fr nf eq)             h = climb fr λ t → s-take (h t) nf eq
  climb (f-took fr fl nr ow eq)       h = climb fr λ _ → s-took fl nr ow eq
  climb (f-outer fr j eq)             h = climb fr λ t → s-flat (h t) j eq
  climb (f-lanes {pre = pre} {b = b} fr sy lf o nq r hl rt cnt wt wh od eq) (_ , _ , refl , h) =
    climb fr λ _ → s-flat sy (joined bg wt wh od) eq
    where
      bg = subst (Begun _ _ _ _ _ _) (sym cnt)
             (subst (λ ls → Begun _ _ _ _ _ ls _) (sym (ʳ++-defn pre)) (begun-join lf o nq r (laneSt b hl h) rt))
  climb (f-lane fr)                   (at , l , refl , h) = climb fr (at , l , refl , h)
  climb (f-lnct fr)                   h = climb fr (_ , _ , refl , h)
  climb (f-src fr sc lv bs fl fe eq)  h = climb fr λ t → s-conn sc bs (λ _ → sync-≈ (h t) (≃-sym fe)) fl eq
  climb (f-srcx fr sc nl bs fl eq)    h = climb fr λ _ → s-conn sc bs (λ lv → ⊥-elim (notT _ nl lv)) fl eq
  climb (f-body {k = k} fr sc os fl eq) h =
    climb fr λ t → s-conn sc (subst (λ x → Sync (binds (CS.src k) (CS.connAt k) x) _ _ _) sc (h t)) os fl eq

  ----------------------------------------------------------------------
  -- DOWN: every frame splits its parent's state into its hole's.

  Res : ∀ {Γ A} → Cur → Ctx R Γ A → St Γ A → Set₁
  Res {A = A} C c s = Σ Need λ w → Σ (EmissionSet A) λ E → Fr Rt C c w E × Hold (scopeOf c) C w s E

  down-map : ∀ {C Γ A B} {f : A → B} {c : Ctx R Γ B} {s} → Res C c (mapS f s) → Res C (inMap f c) s
  down-map (owes true , _ , fr , h) with h _
  ... | s-map sy me = owes true , _ , f-map fr me , λ _ → sy
  down-map (owes false , _ , fr , _)            = owes false , none′ , f-off u-map fr , λ ()
  down-map (lane _ , _ , _ , (_ , _ , () , _))
  down-map (lanecut _ , _ , _ , (_ , _ , () , _))

  down-scan : ∀ {C Γ A B} {f : B → A → B} {z} {c : Ctx R Γ B} {s} → Res C c (scanS f z s) → Res C (inScan f z c) s
  down-scan (owes true , _ , fr , h) with h _
  ... | s-scan sy fd eq = owes true , _ , f-scan fr fd eq , λ _ → sy
  down-scan (owes false , _ , fr , _)            = owes false , none′ , f-off u-scan fr , λ ()
  down-scan (lane _ , _ , _ , (_ , _ , () , _))
  down-scan (lanecut _ , _ , _ , (_ , _ , () , _))

  down-cut : ∀ {C Γ A} {l a} {c : Ctx R Γ A} {s} → Res C c (cutS l a s) → Res C (inCut l a c) s
  down-cut (owes true , _ , fr , h) with h _
  ... | s-cut sy = owes true , _ , f-cut fr , λ _ → sy
  down-cut (owes false , _ , fr , _)                  = owes false , none′ , f-off u-cut fr , λ ()
  down-cut (lane _ , _ , _ , (_ , _ , () , _))
  down-cut (lanecut b , _ , fr , (_ , _ , refl , h))  = owes b , _ , f-lnct fr , h

  down-ln : ∀ {C Γ A} {b} {c : Ctx R Γ A} {s} → Res C c (lnS b s) → Res C (inLn b c) s
  down-ln (owes true , _ , fr , h) with h _
  ... | ()
  down-ln (owes false , _ , fr , _)                  = owes false , none′ , f-off u-ln fr , λ ()
  down-ln (lane b , _ , fr , (at , l , refl , h))    = lanecut b , _ , f-lane fr , (at , l , refl , h)
  down-ln (lanecut _ , _ , _ , (_ , _ , () , _))

  down-take : ∀ {C Γ A} {i keep w} {c : Ctx R Γ A} {s} → Res C c (takeS i keep w s) → Res C (inTake i keep w c) s
  down-take (owes true , _ , fr , h) with h _
  ... | s-take sy nf eq      = owes true , _ , f-take fr nf eq , λ _ → sy
  ... | s-took fl nr ow eq   = owes false , none′ , f-took fr fl nr ow eq , λ ()
  down-take (owes false , _ , fr , _)            = owes false , none′ , f-off u-take fr , λ ()
  down-take (lane _ , _ , _ , (_ , _ , () , _))
  down-take (lanecut _ , _ , _ , (_ , _ , () , _))

  down-outer : ∀ {C Γ A B} {op} {f} {d n qu ls} {c : Ctx R Γ B} {s : St Γ A}
             → Res C c (flatS op f d n qu s ls) → Res C (inOuter op f d n qu ls c) s
  down-outer (owes true , _ , fr , h) with h _
  ... | s-flat sy j eq = owes true , _ , f-outer fr j eq , λ _ → sy
  down-outer (owes false , _ , fr , _)            = owes false , none′ , f-off u-outer fr , λ ()
  down-outer (lane _ , _ , _ , (_ , _ , () , _))
  down-outer (lanecut _ , _ , _ , (_ , _ , () , _))

  down-lanes : ∀ {C Γ A B} {op} {f} {d n qu} {o : St Γ A} {pre post} {c : Ctx R Γ B} {s}
             → Res C c (flatS op f d n qu o (pre ʳ++ s ∷ post)) → Res C (inLanes op f d n qu o pre post c) s
  down-lanes {pre = pre} (owes true , _ , fr , h) with h _
  ... | s-flat sy (joined bg wt wh od) eq
    with begun-split (reverse pre) (subst (λ ls → Begun _ _ _ _ _ ls _) (ʳ++-defn pre) bg)
  ...   | split lf o nq r l rt cnt refl with laneHold l
  ...     | _ , hl , hd = lane _ , _ , f-lanes fr sy lf o nq r hl rt cnt wt wh od eq , hd
  down-lanes (owes false , _ , fr , _)            = owes false , none′ , f-off u-lanes fr , λ ()
  down-lanes (lane _ , _ , _ , (_ , _ , () , _))
  down-lanes (lanecut _ , _ , _ , (_ , _ , () , _))

  down-src : ∀ {C Γ X B} {k : CS Γ X} {b} {c : Ctx R Γ B} {s} → Res C c (connS k s b) → Res C (inSrc k b c) s
  down-src {k = k} (owes true , _ , fr , h) with h _
  ... | s-conn sc bs os fl eq with live? (CS.srcLive k)
  ...   | inj₁ lv = owes true , _ , f-src fr sc lv bs fl ≃-refl eq , λ _ → os lv
  ...   | inj₂ nl = owes false , none′ , f-srcx fr sc nl bs fl eq , λ ()
  down-src (owes false , _ , fr , _)            = owes false , none′ , f-off u-src fr , λ ()
  down-src (lane _ , _ , _ , (_ , _ , () , _))
  down-src (lanecut _ , _ , _ , (_ , _ , () , _))

  down-body : ∀ {C Γ X B} {k : CS Γ X} {o} {c : Ctx R Γ B} {s} → Res C c (connS k o s) → Res C (inBody k o c) s
  down-body {C = C} {k = k} {s = s} (owes true , _ , fr , h) with h _
  ... | s-conn sc bs os fl eq =
    owes true , _ , f-body fr sc os fl eq , λ _ → subst (λ x → Sync (binds (CS.src k) (CS.connAt k) x) C s _) (sym sc) bs
  down-body (owes false , _ , fr , _)            = owes false , none′ , f-off u-body fr , λ ()
  down-body (lane _ , _ , _ , (_ , _ , () , _))
  down-body (lanecut _ , _ , _ , (_ , _ , () , _))

  descend : ∀ {C Γ A} (c : Ctx R Γ A) s {E} → Sync unbound C (plug c s) E → E ≈ Rt → Res C c s
  descend top                               s sy eq = owes true , _ , f-top eq , λ _ → sy
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
  ... | _ , top≈ , sy with descend c′ s′ (subst (λ t → Sync unbound _ t _) (sym eq) sy) top≈
  ...   | _ , _ , fr′ , h′ = settled c-abs fr′ h′
