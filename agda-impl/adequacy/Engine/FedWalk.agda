{-# OPTIONS --guardedness #-}

-- A SOURCE'S SKIPS FED ITS BODY, NODE BY NODE.  The body of a live
-- connect, fed its source's run on one side and the run with its leading
-- skips dropped on the other, is walked down: every node below it is read
-- in both environments (`envOf`), each inner connect's body fed its own
-- source as that source runs in each.  A node whose run reads no
-- environment is alike on both sides; a frame of one child passes its
-- child's relation as it is; a joiner, a merge, a connect, and a run
-- read only through its tail are the leaves.
--
-- What a leaf may read off the configuration: the body's joiners of the
-- source joined before its skip and hold nothing fed, no defer there
-- holds a step of it, nothing there is held under the skip, and the
-- source's run nests nothing under a skip.
module adequacy.Engine.FedWalk where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; _ʳ++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.Maybe using (Maybe; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans)

open import denotation.MonotonicList.Events using (Events; Events∞; Pos)
open import denotation.MonotonicList using (Agree; Agreeᵀ)
open import denotation.Unfold using (NEnv; stateᴺ)
open import operation.Key using (after)
open import operation.PureObservable using (module Machine)
open Machine using (St; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS; Ctx; inMap; inScan; inCut; inLn;
  inTake; inOuter; inLanes; inSrc; inBody; plug; own; cs; CS; Owe; free; cpAt; cutAt; overAt; Att; Ev)
open import operation.PureObservable using (ending; play; over)
open import adequacy.Engine.Meaning using (_≋_; ≋-by; gh; envAt; srcRun; srcG; mapped; scanned; took)
open import adequacy.Engine.Head using (Frag; cand)
open import adequacy.Engine.Pick using (KAfter; Before)
open import adequacy.Engine.Erase using (Eraseˢ; _,ᵉ_; Eraseᵀ; Erase; Lead⁼; _⊒_)
open import adequacy.Engine.Drop using (Dropsˢ; dropˢ; dropsˢ; Fed; ≋-⊒; mapped-⊒; scanned-⊒; took-⊒; mapped-drops; scanned-drops; took-drops)
open Events∞

------------------------------------------------------------------------
-- Where a pass is asked

-- The positions a pass is asked of: the skip's own, or any under it.
Sought : Bool → Pos → (Pos → Set) → Set
Sought false q P = ∀ k → P k → k ≡ q
Sought true  q P = ∀ k → P k → Σ Pos λ y → k ≡ q ++ y

------------------------------------------------------------------------
-- Relations read through their parts

-- Runs read alike part by part are related alike.
eraseˢ-by : ∀ {A m} {g h g′ h′ : Events∞ A} → force g ≡ force h → cut g ≡ cut h → force g′ ≡ force h′ → cut g′ ≡ cut h′
          → Eraseˢ m h h′ → Eraseˢ m g g′
eraseˢ-by {m = m} {g} {h} {g′} {h′} f c f′ c′ (e ,ᵉ x) =
  subst (λ t → Eraseᵀ m t (cut g′)) (sym c) (subst (Eraseᵀ m (cut h)) (sym c′) e)
  ,ᵉ subst (λ y → Erase m y (cut g′) (force g′)) (sym f)
       (subst (λ t → Erase m (force h) t (force g′)) (sym c′) (subst (Erase m (force h) (cut h′)) (sym f′) x))

⊒-by : ∀ {A} {g h g′ h′ : Events∞ A} → force g ≡ force h → cut g ≡ cut h → force g′ ≡ force h′ → cut g′ ≡ cut h′ → h ⊒ h′ → g ⊒ g′
⊒-by {g = g} {h} {g′} {h′} f c f′ c′ (l , u , e) =
  subst (λ y → Lead⁼ y (force g′)) (sym f) (subst (Lead⁼ (force h)) (sym f′) l)
  , (λ w d → subst (λ t → Agreeᵀ d t (cut g′)) (sym c) (subst (Agreeᵀ d (cut h)) (sym c′) (u (trans (sym f) w) d)))
  , λ n → eraseˢ-by f c f′ c′ (e n)

drops-byʳ : ∀ {A Q} {h g′ h′ : Events∞ A} → force g′ ≡ force h′ → cut g′ ≡ cut h′ → Dropsˢ Q h h′ → Dropsˢ Q h g′
drops-byʳ f′ c′ (dropˢ p a r)  = dropˢ p a (⊒-by refl refl f′ c′ r)
drops-byʳ f′ c′ (dropsˢ p a d) = dropsˢ p a (drops-byʳ f′ c′ d)

drops-by : ∀ {A Q} {g h g′ h′ : Events∞ A} → force g ≡ force h → force g′ ≡ force h′ → cut g′ ≡ cut h′ → Dropsˢ Q h h′ → Dropsˢ Q g g′
drops-by {g = g} f f′ c′ (dropˢ {k} {r} p a s)  = dropˢ p (λ n → subst (λ y → Agree n y _) (sym f) (a n)) (⊒-by refl refl f′ c′ s)
drops-by {g = g} f f′ c′ (dropsˢ {k} {r} p a d) = dropsˢ p (λ n → subst (λ y → Agree n y _) (sym f) (a n)) (drops-byʳ f′ c′ d)

fed-by : ∀ {A P} {g h g′ h′ : Events∞ A} → force g ≡ force h → cut g ≡ cut h → force g′ ≡ force h′ → cut g′ ≡ cut h′
       → Fed P h h′ → Fed P g g′
fed-by f c f′ c′ (inj₁ x) = inj₁ (⊒-by f c f′ c′ x)
fed-by f c f′ c′ (inj₂ x) = inj₂ (drops-by f f′ c′ x)

-- A frame of one child passes its child's relation.
fed-map : ∀ {A B P} (g : A → B) {h h′ : Events∞ A} → Fed P h h′ → Fed P (mapped g h) (mapped g h′)
fed-map g (inj₁ x) = inj₁ (mapped-⊒ g x)
fed-map g (inj₂ x) = inj₂ (mapped-drops g x)

fed-scan : ∀ {A B P} (g : B → A → B) z {h h′ : Events∞ A} → Fed P h h′ → Fed P (scanned g z h) (scanned g z h′)
fed-scan g z (inj₁ x) = inj₁ (scanned-⊒ g z x)
fed-scan g z (inj₂ x) = inj₂ (scanned-drops g z x)

fed-took : ∀ {A P} i (q : A → Bool) {h h′ : Events∞ A} → Fed P h h′ → Fed P (took i q h) (took i q h′)
fed-took i q (inj₁ x) = inj₁ (took-⊒ i q x)
fed-took i q (inj₂ x) = inj₂ (took-drops i q x)

------------------------------------------------------------------------
-- The walk

module Walk {R Γ X B} (v : Bool) (q : Pos) {P : Pos → Set} (c : Ctx R Γ B) (sa : Bool) (ba as : Maybe Pos) (r en : Pos)
            (o : St Γ X) (b : St (X ∷ Γ) B) {h h′ : Events∞ X}
            (so : Sought v q P) (ka : KAfter (after q) (cand (inBody (cs false true sa ba as nothing r en) o c) b))
            (bf : Before (after q) (own (connS (cs false true sa ba as nothing r en) o b)))
            (ft : Frag (plug c (connS (cs false true sa ba as nothing r en) o b)))
            (x : h ≋ stateᴺ (gh o) (envAt c)) (d : Dropsˢ P h h′) where

  -- A context below the fed body.
  data Down : ∀ {Δ C} → Ctx R Δ C → Set₁ where
    base   : Down (inBody (cs false true sa ba as nothing r en) o c)
    dMap   : ∀ {Δ A C} {f : A → C} {e : Ctx R Δ C} → Down e → Down (inMap f e)
    dScan  : ∀ {Δ A C} {f : C → A → C} {z} {e : Ctx R Δ C} → Down e → Down (inScan f z e)
    dCut   : ∀ {Δ A l a} {e : Ctx R Δ A} → Down e → Down (inCut l a e)
    dLn    : ∀ {Δ A l} {e : Ctx R Δ A} → Down e → Down (inLn l e)
    dTake  : ∀ {Δ A i p w} {e : Ctx R Δ A} → Down e → Down (inTake i p w e)
    dOuter : ∀ {Δ A C op f dn n qs ls} {e : Ctx R Δ C} → Down e → Down (inOuter {A = A} op f dn n qs ls e)
    dLanes : ∀ {Δ A C op f dn n qs s pre post} {e : Ctx R Δ C} → Down e → Down (inLanes {A = A} op f dn n qs s pre post e)
    dSrc   : ∀ {Δ Y C k t} {e : Ctx R Δ C} → Down e → Down (inSrc {X = Y} k t e)
    dBody  : ∀ {Δ Y C k s} {e : Ctx R Δ C} → Down e → Down (inBody {X = Y} k s e)

  -- The environment below, the fed source's run given.
  envOf : ∀ {Δ C} {e : Ctx R Δ C} → Events X → Down e → NEnv Δ
  envOf y base                     = y ∷ᴬ envAt c
  envOf y (dMap dd)                = envOf y dd
  envOf y (dScan dd)               = envOf y dd
  envOf y (dCut dd)                = envOf y dd
  envOf y (dLn dd)                 = envOf y dd
  envOf y (dTake dd)               = envOf y dd
  envOf y (dOuter dd)              = envOf y dd
  envOf y (dLanes dd)              = envOf y dd
  envOf y (dSrc dd)                = envOf y dd
  envOf y (dBody {k = k} {s} dd)   = srcRun (srcG k s) (envOf y dd) ∷ᴬ envOf y dd

  -- A node fed the source's run, beside it fed the rest.
  FedAt : ∀ {Δ C A} {e : Ctx R Δ C} → Down e → St Δ A → Set
  FedAt dd s = Fed P (stateᴺ (gh s) (envOf (force h) dd)) (stateᴺ (gh s) (envOf (force h′) dd))

  postulate
    -- A KILL SWITCH OFF, its child read through its tail.
    fed-cut : ∀ {Δ C} {e : Ctx R Δ C} (dd : Down e) a (s : St Δ C) → Frag (plug e (cutS false a s))
            → FedAt dd s → FedAt dd (cutS false a s)
    -- A takeWhile owing, its child read through its tail or ending.
    fed-taken : ∀ {Δ C} {e : Ctx R Δ C} (dd : Down e) i (p : C → Bool) w (s : St Δ C) → Frag (plug e (takeS i p w s))
              → FedAt dd s → FedAt dd (takeS i p w s)
    -- A LIVE JOINER rejoins its source's relation under its own position.
    fed-join : ∀ {Δ C} {e : Ctx R Δ C} (dd : Down e) j (y : C ∈ Δ) (ib : List (Pos × Ev C)) → Frag (plug e (joinS j true y ib))
             → FedAt dd (joinS j true y ib)
    -- A MERGE interleaves its parts' relations; a lane it subscribes is
    -- related as its outer's value is.
    --
    -- REFUTED: 413cf07a over any node and any source, by a source whose value comes before the skip it follows, merged beside a lane that leads: the skip neither leads nor is erasable.
    -- RECOVERY: git show 413cf07a^:agda-impl/adequacy/Engine/Shown.agda restores a node owing its source nothing and a run nesting nothing, as definitions over a node, and the node-level statement
    fed-flat : ∀ {Δ A C} {e : Ctx R Δ C} (dd : Down e) op (f : A → _) dn n qs (s : St Δ A) (ls : List (St Δ C))
             → Frag (plug e (flatS op f dn n qs s ls)) → FedAt dd s → All (FedAt dd) ls → FedAt dd (flatS op f dn n qs s ls)
    -- A CONNECT feeds its body its own source's relation, by the erasure
    -- beside a source (`adequacy.Engine.Beside.body-⊒`), which asks the
    -- current inner source's place and the fed one's trail.  The fed inner
    -- source is the run of no configuration given here, so its trail is
    -- the open part: the stepped configuration's, or a relation that
    -- cannot erase forever.
    --
    -- DEAD ROUTE: the fed inner source's trail read off its relation to the current one, which trails: an erased step spends depth, so endless erased skips leave the rest unconstrained (refuted at f1f7d119).
    fed-conn : ∀ {Δ Y C} {e : Ctx R Δ C} (dd : Down e) k (s : St Δ Y) (t : St (Y ∷ Δ) C) → Frag (plug e (connS k s t))
             → FedAt dd s → FedAt (dBody {k = k} {s} dd) t → FedAt dd (connS k s t)

  mutual
    walk : ∀ {Δ C} {e : Ctx R Δ C} (dd : Down e) (s : St Δ C) → Frag (plug e s) → FedAt dd s
    walk dd (pend p)                  fs = inj₁ (≋-⊒ (≋-by refl refl))
    walk dd (coldS l (ending p))      fs = inj₁ (≋-⊒ (≋-by refl refl))
    walk dd (coldS true (play τ u i t fr)) fs = inj₁ (≋-⊒ (≋-by refl refl))
    walk dd (coldS false (play τ u i t fr)) fs = inj₁ (≋-⊒ (≋-by refl refl))
    walk dd (coldS l over)            fs = inj₁ (≋-⊒ (≋-by refl refl))
    walk dd (ofS i p xs)              fs = inj₁ (≋-⊒ (≋-by refl refl))
    walk dd doneS                     fs = inj₁ (≋-⊒ (≋-by refl refl))
    walk dd (mapS f s)                fs = fed-by refl refl refl refl (fed-map f (walk (dMap dd) s fs))
    walk dd (scanS f z s)             fs = fed-by refl refl refl refl (fed-scan f z (walk (dScan dd) s fs))
    walk dd (cutS true a s)           fs = walk (dCut dd) s fs
    walk dd (cutS false a s)          fs = fed-cut dd a s fs (walk (dCut dd) s fs)
    walk dd (lnS l s)                 fs = walk (dLn dd) s fs
    walk dd (takeS i p free s)        fs = fed-by refl refl refl refl (fed-took i p (walk (dTake dd) s fs))
    walk dd (takeS i p (cpAt k) s)    fs = fed-taken dd i p (cpAt k) s fs (walk (dTake dd) s fs)
    walk dd (takeS i p (cutAt k) s)   fs = fed-taken dd i p (cutAt k) s fs (walk (dTake dd) s fs)
    walk dd (takeS i p (overAt k) s)  fs = fed-taken dd i p (overAt k) s fs (walk (dTake dd) s fs)
    walk dd (flatS op f dn n qs s ls) fs = fed-flat dd op f dn n qs s ls fs (walk (dOuter dd) s fs) (walkLanes dd op f dn n qs s [] ls fs)
    walk dd (connS k s t)             fs = fed-conn dd k s t fs (walk (dSrc dd) s fs) (walk (dBody dd) t fs)
    walk dd (joinS j false y ib)      fs = inj₁ (≋-⊒ (≋-by refl refl))
    walk dd (joinS j true y ib)       fs = fed-join dd j y ib fs

    -- A flatMap's lanes, those before nearest first.
    walkLanes : ∀ {Δ A C} {e : Ctx R Δ C} (dd : Down e) op (f : A → _) dn n qs (s : St Δ A) (pre post : List (St Δ C))
              → Frag (plug e (flatS op f dn n qs s (pre ʳ++ post))) → All (FedAt dd) post
    walkLanes dd op f dn n qs s pre []         fs = []ᴬ
    walkLanes dd op f dn n qs s pre (l ∷ post) fs =
      walk (dLanes {pre = pre} {post} dd) l fs ∷ᴬ walkLanes dd op f dn n qs s (l ∷ pre) post fs

-- A SOURCE'S SKIPS FED ITS BODY: the body fed a live source's skips
-- drops its own leading skips, each under one of them, and erases none
-- or more past them, to the body fed the rest.
src-fed : ∀ {R Γ X B} v q {P} (c : Ctx R Γ B) sa ba as r en (o : St Γ X) (b : St (X ∷ Γ) B) {h h′ : Events∞ X}
        → Sought v q P → KAfter (after q) (cand (inBody (cs false true sa ba as nothing r en) o c) b)
        → Before (after q) (own (connS (cs false true sa ba as nothing r en) o b))
        → Frag (plug c (connS (cs false true sa ba as nothing r en) o b))
        → h ≋ stateᴺ (gh o) (envAt c) → Dropsˢ P h h′
        → Fed P (stateᴺ (gh b) (force h ∷ᴬ envAt c)) (stateᴺ (gh b) (force h′ ∷ᴬ envAt c))
src-fed v q c sa ba as r en o b so ka bf ft x d = Walk.walk v q c sa ba as r en o b so ka bf ft x d (Walk.base) b ft
