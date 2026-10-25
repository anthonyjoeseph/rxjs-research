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
open import Data.List using (List; []; _∷_; _++_; _ʳ++_; [_])
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans)

open import denotation.MonotonicList.Events using (Events; Events∞; Pos; hush; idle; ix)
open import denotation.MonotonicList using (head; Agree; Agreeᵀ; agree-sym; agreeᵀ-sym; agree-refl)
open import denotation.NonExpansive using (Agreeˢ)
open import denotation.Unfold using (NEnv; meaning; stateᴺ; Source; live; ended)
open import operation.Key using (after)
open import operation.PureObservable using (module Machine)
open Machine using (St; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS; Ctx; inMap; inScan; inCut; inLn;
  inTake; inOuter; inLanes; inSrc; inBody; plug; own; cs; CS; Owe; free; cpAt; cutAt; overAt; Att; Ev; _⊕_)
open import operation.PureObservable using (ending; play; over)
open import adequacy.Engine.Meaning using (_≋_; ≋-by; gh; envAt; srcRun; srcG; srcState; subOr; bodyConn; mapped; scanned; took)
open import adequacy.Engine.Head using (Frag; cand)
open import adequacy.Engine.Keys using (Held)
open import adequacy.Engine.Pick using (KAfter; Before)
open import adequacy.Engine.Erase using (Eraseˢ; _,ᵉ_; Eraseᵀ; Erase; Lead⁼; _⊒_)
open import adequacy.Engine.Race using (After; NotBefore)
open import adequacy.Engine.Ahead using (Under; shown)
open import adequacy.Engine.Beside using (Sourced; body-⊒)
open import adequacy.Placed.Trail using (Trailing)
open import adequacy.Engine.Trails using (shape-src)
open import adequacy.Engine.Kept using (sub-settled)
open import adequacy.Engine.Inv using (Unpended)
open import adequacy.Env using (NAgree; nagree-refl; meaning-ne; state-ne)
open import adequacy.Placed.Trail using (trail-≈)
open import adequacy.Engine.Drop using (Dropsˢ; dropˢ; dropsˢ; Fed; src-alone; body-alone; both; ≋-⊒; mapped-⊒; scanned-⊒; took-⊒;
  mapped-drops; scanned-drops; took-drops)
open Events∞
open Agreeˢ

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

-- Positions under a position under one are under it.
under-under : ∀ {P : Pos → Set} {k} → Under (Under P) k → Under P k
under-under (_ , (k₀ , p₀ , y₀ , refl) , y , refl) = k₀ , p₀ , y₀ ++ y , ++-assoc k₀ y₀ y

under-self : ∀ {P : Pos → Set} {k} → P k → Under P k
under-self {k = k} p = k , p , [] , sym (++-identityʳ k)

drops-mono : ∀ {A} {Q Q′ : Pos → Set} → (∀ {k} → Q k → Q′ k) → {h h′ : Events∞ A} → Dropsˢ Q h h′ → Dropsˢ Q′ h h′
drops-mono m (dropˢ p a r)  = dropˢ (m p) a r
drops-mono m (dropsˢ p a d) = dropsˢ (m p) a (drops-mono m d)

-- A live source not pending runs as its node does, however its body
-- subscribed it.
settled-run : ∀ {Γ X} sa ba as r en (o : St Γ X) (ρ : NEnv Γ) → Unpended o
            → srcRun (srcG (cs false true sa ba as nothing r en) o) ρ ≡ meaning (gh o) ρ
settled-run sa nothing  as r en o ρ u = refl
settled-run sa (just p) as r en o ρ u rewrite sub-settled (p ⊕ [ ix 1 ]) o u = refl

-- A source, in environments alike, runs alike.
srcRun-ne : ∀ {Γ X m} (σ : Source Γ X) {ρ ρ′ : NEnv Γ} → NAgree m ρ ρ′ → Agree m (srcRun σ ρ) (srcRun σ ρ′)
srcRun-ne (live s)    a = meaning-ne s a
srcRun-ne (ended e t) a = agree-refl _ _

srcState-ne : ∀ {Γ X m} (σ : Source Γ X) {ρ ρ′ : NEnv Γ} → NAgree m ρ ρ′ → Agreeˢ m (srcState σ ρ) (srcState σ ρ′)
srcState-ne (live s)    a = state-ne s a
srcState-ne (ended e t) a = state-ne t a

-- A connect passes its source's relation and its body's, the source
-- subscribed where it is, the one fed the rest trailing, past every
-- position asked of, and leaving nothing running hushed, and the body
-- fed the rest past each.
conn-fed : ∀ {Y C P} r {σ σ′ : Events∞ Y} {β β′ : Events∞ C} → Sourced r σ → Trailing σ′
         → (force σ′ ≡ hush → ∀ d → Agreeᵀ d (cut σ′) idle) → (∀ k → Under P k → NotBefore k (shown (force σ′)))
         → (∀ k → Under P k → After (k ++ [ ix 0 ]) (head (force β′)))
         → Fed P σ σ′ → Fed P β β′ → Fed P (bodyConn r σ β) (bodyConn r σ′ β′)
conn-fed r so t hc nb bo (inj₁ x) (inj₁ y) = inj₁ (body-⊒ r so t x y)
conn-fed r so t hc nb bo (inj₁ x) (inj₂ d) = inj₂ (body-alone r hc nb so t x d)
conn-fed r so t hc nb bo (inj₂ d) (inj₁ y) = inj₂ (drops-mono under-under (src-alone r y bo so t d))
conn-fed r so t hc nb bo (inj₂ d) (inj₂ e) =
  inj₂ (drops-mono under-under (both r hc (λ k u → nb k (under-under u)) bo so t d (drops-mono under-self e)))

-- A connect whose run is read through its tail: its source's teardown
-- owed, or its source gone.
data Rests : Maybe Pos → Bool → Set where
  owed : ∀ {w l} → Rests (just w) l
  off  : Rests nothing false

------------------------------------------------------------------------
-- The walk

module Walk {R Γ X B} (v : Bool) (q : Pos) {P : Pos → Set} (c : Ctx R Γ B) (sa : Bool) (ba as : Maybe Pos) (r en : Pos)
            (o : St Γ X) (b : St (X ∷ Γ) B) {h h′ : Events∞ X}
            (so : Sought v q P) (ka : KAfter (after q) (cand (inBody (cs false true sa ba as nothing r en) o c) b))
            (bf : Before (after q) (own (connS (cs false true sa ba as nothing r en) o b)))
            (ft : Held (plug c (connS (cs false true sa ba as nothing r en) o b)))
            (x : h ≋ stateᴺ (gh o) (envAt c)) (d : Dropsˢ P h h′)
            (o′ : St Γ X) (ft′ : Held (plug c (connS (cs false true sa ba as nothing r en) o′ b))) (u′ : Unpended o′)
            (x′ : h′ ≋ stateᴺ (gh o′) (envAt c)) where

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

  -- The context below in the stepped tree: the source stepped, the body
  -- as it stands.
  rebase : ∀ {Δ C} {e : Ctx R Δ C} → Down e → Ctx R Δ C
  rebase base                                                         = inBody (cs false true sa ba as nothing r en) o′ c
  rebase (dMap {f = f} dd)                                            = inMap f (rebase dd)
  rebase (dScan {f = f} {z = z} dd)                                   = inScan f z (rebase dd)
  rebase (dCut {l = l} {a = a} dd)                                    = inCut l a (rebase dd)
  rebase (dLn {l = l} dd)                                             = inLn l (rebase dd)
  rebase (dTake {i = i} {p = p} {w = w} dd)                           = inTake i p w (rebase dd)
  rebase (dOuter {op = op} {f = f} {dn = dn} {n = n} {qs = qs} {ls = ls} dd) = inOuter op f dn n qs ls (rebase dd)
  rebase (dLanes {op = op} {f = f} {dn = dn} {n = n} {qs = qs} {s = s} {pre = pre} {post = post} dd) =
    inLanes op f dn n qs s pre post (rebase dd)
  rebase (dSrc {k = k} {t = t} dd)                                    = inSrc k t (rebase dd)
  rebase (dBody {k = k} {s = s} dd)                                   = inBody k s (rebase dd)

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
    -- A CONNECT READ THROUGH ITS TAIL.
    fed-done : ∀ {Δ Y C} {e : Ctx R Δ C} (dd : Down e) k (s : St Δ Y) (t : St (Y ∷ Δ) C) → Rests (CS.owedAt k) (CS.srcLive k)
             → Frag (plug e (connS k s t)) → FedAt dd s → FedAt (dBody {k = k} {s} dd) t → FedAt dd (connS k s t)
    -- A CLOSED SOURCE beside its body, read through its tail.
    fed-ended : ∀ {Δ Y C} {e : Ctx R Δ C} (dd : Down e) sa as r en (s : St Δ Y) (t : St (Y ∷ Δ) C)
              → Frag (plug e (connS (cs true true sa nothing as nothing r en) s t)) → FedAt dd s
              → Fed P (srcState (srcG (cs true true sa nothing as nothing r en) s) (envOf (force h) dd))
                      (srcState (srcG (cs true true sa nothing as nothing r en) s) (envOf (force h′) dd))
    -- A SOURCE SUBSCRIBED beside its body, fresh.
    fed-fresh : ∀ {Δ Y C} {e : Ctx R Δ C} (dd : Down e) cl sa p as r en o (t : St (Y ∷ Δ) C)
              → Frag (plug e (connS (cs cl true sa (just p) as nothing r en) (pend o) t))
              → Fed P (stateᴺ (subOr (p ⊕ [ ix 1 ]) (pend o)) (envOf (force h) dd)) (stateᴺ (subOr (p ⊕ [ ix 1 ]) (pend o)) (envOf (force h′) dd))
    -- AN INNER SOURCE, fed the source's run, is subscribed where its
    -- connect is.
    fed-sourced : ∀ {Δ Y C} {e : Ctx R Δ C} (dd : Down e) cl sa ba as r en (s : St Δ Y) (t : St (Y ∷ Δ) C)
                → Frag (plug e (connS (cs cl true sa ba as nothing r en) s t))
                → Sourced r (srcState (srcG (cs cl true sa ba as nothing r en) s) (envOf (force h) dd))
    -- Hushed, it leaves nothing running; its next shows no earlier than
    -- any position asked of (as `adequacy.Engine.Shown.src-next` at the
    -- fed source).
    fed-src-next : ∀ {Δ Y C} {e : Ctx R Δ C} (dd : Down e) cl sa ba as r en (s : St Δ Y) (t : St (Y ∷ Δ) C)
                 → Frag (plug e (connS (cs cl true sa ba as nothing r en) s t))
                 → (force (srcState (srcG (cs cl true sa ba as nothing r en) s) (envOf (force h′) dd)) ≡ hush
                     → ∀ d → Agreeᵀ d (cut (srcState (srcG (cs cl true sa ba as nothing r en) s) (envOf (force h′) dd))) idle)
                   × (∀ k → Under P k → NotBefore k (shown (force (srcState (srcG (cs cl true sa ba as nothing r en) s) (envOf (force h′) dd)))))
    -- Its body fed the rest comes after each position asked of shows (as
    -- `adequacy.Engine.Shown.src-body-on` at the fed source).
    fed-body-on : ∀ {Δ Y C} {e : Ctx R Δ C} (dd : Down e) cl sa ba as r en (s : St Δ Y) (t : St (Y ∷ Δ) C)
                → Frag (plug e (connS (cs cl true sa ba as nothing r en) s t))
                → ∀ k → Under P k → After (k ++ [ ix 0 ])
                    (head (force (stateᴺ (gh t) (srcRun (srcG (cs cl true sa ba as nothing r en) s) (envOf (force h′) dd) ∷ᴬ envOf (force h′) dd))))

  -- THE ENVIRONMENT FED THE REST is the stepped tree's.
  env-agree : ∀ m {Δ C} {e : Ctx R Δ C} (dd : Down e) → NAgree m (envOf (force h′) dd) (envAt (rebase dd))
  env-agree m base =
    subst (Agree m (force h′)) (sym (settled-run sa ba as r en o′ (envAt c) u′)) (nowˢ (x′ m)) , nagree-refl m (envAt c)
  env-agree m (dMap dd)                 = env-agree m dd
  env-agree m (dScan dd)                = env-agree m dd
  env-agree m (dCut dd)                 = env-agree m dd
  env-agree m (dLn dd)                  = env-agree m dd
  env-agree m (dTake dd)                = env-agree m dd
  env-agree m (dOuter dd)               = env-agree m dd
  env-agree m (dLanes dd)               = env-agree m dd
  env-agree m (dSrc dd)                 = env-agree m dd
  env-agree m (dBody {k = k} {s = s} dd) = srcRun-ne (srcG k s) (env-agree m dd) , env-agree m dd

  -- AN INNER SOURCE FED THE REST: what it leaves running trails it.
  --
  -- It is the stepped tree's inner source, read in that tree's own
  -- environment.
  --
  -- DEAD ROUTE: the fed inner source's trail read off its relation to the current one, which trails: an erased step spends depth, so endless erased skips leave the rest unconstrained (refuted at f1f7d119); likewise read off the current environment thinned.
  fed-trail : ∀ {Δ Y C} {e : Ctx R Δ C} (dd : Down e) cl sa ba as r en (s : St Δ Y) (t : St (Y ∷ Δ) C)
            → Held (plug (rebase dd) (connS (cs cl true sa ba as nothing r en) s t))
            → Trailing (srcState (srcG (cs cl true sa ba as nothing r en) s) (envOf (force h′) dd))
  fed-trail dd cl sa ba as r en s t fs′ =
    trail-≈ _ _ _ _ (λ n → agree-sym (nowˢ (g n))) (λ n → agreeᵀ-sym (cutˢ (g n))) (proj₂ (shape-src (rebase dd) k s t fs′))
    where k = cs cl true sa ba as nothing r en
          g = λ n → srcState-ne (srcG k s) (env-agree n dd)

  -- A source subscribed at its body's mark: fresh, or as it stands.
  sub-fed : ∀ {Δ Y C} {e : Ctx R Δ C} (dd : Down e) cl sa p as r en (s : St Δ Y) (t : St (Y ∷ Δ) C)
          → Held (plug e (connS (cs cl true sa (just p) as nothing r en) s t)) → FedAt dd s
          → Fed P (stateᴺ (subOr (p ⊕ [ ix 1 ]) s) (envOf (force h) dd)) (stateᴺ (subOr (p ⊕ [ ix 1 ]) s) (envOf (force h′) dd))
  sub-fed dd cl sa p as r en (pend o)                t fs is = fed-fresh dd cl sa p as r en o t (proj₁ fs)
  sub-fed dd cl sa p as r en (coldS b l)             t fs is = is
  sub-fed dd cl sa p as r en (ofS i q xs)            t fs is = is
  sub-fed dd cl sa p as r en doneS                   t fs is = is
  sub-fed dd cl sa p as r en (mapS f s)              t fs is = is
  sub-fed dd cl sa p as r en (scanS f z s)           t fs is = is
  sub-fed dd cl sa p as r en (cutS l a s)            t fs is = is
  sub-fed dd cl sa p as r en (lnS l s)               t fs is = is
  sub-fed dd cl sa p as r en (takeS i q w s)         t fs is = is
  sub-fed dd cl sa p as r en (flatS op f dn n q o ls) t fs is = is
  sub-fed dd cl sa p as r en (connS k o b)           t fs is = is
  sub-fed dd cl sa p as r en (joinS j l y ib)        t fs is = is

  -- A live connect, its source live or closed, beside its body.
  live-fed : ∀ {Δ Y C} {e : Ctx R Δ C} (dd : Down e) cl sa ba as r en (s : St Δ Y) (t : St (Y ∷ Δ) C)
           → Held (plug e (connS (cs cl true sa ba as nothing r en) s t))
           → Held (plug (rebase dd) (connS (cs cl true sa ba as nothing r en) s t))
           → Fed P (srcState (srcG (cs cl true sa ba as nothing r en) s) (envOf (force h) dd))
                   (srcState (srcG (cs cl true sa ba as nothing r en) s) (envOf (force h′) dd))
           → FedAt (dBody {k = cs cl true sa ba as nothing r en} {s} dd) t
           → Fed P (bodyConn r (srcState (srcG (cs cl true sa ba as nothing r en) s) (envOf (force h) dd))
                     (stateᴺ (gh t) (envOf (force h) (dBody {k = cs cl true sa ba as nothing r en} {s} dd))))
                   (bodyConn r (srcState (srcG (cs cl true sa ba as nothing r en) s) (envOf (force h′) dd))
                     (stateᴺ (gh t) (envOf (force h′) (dBody {k = cs cl true sa ba as nothing r en} {s} dd))))
  live-fed dd cl sa ba as r en s t fs fs′ σ β =
    conn-fed r (fed-sourced dd cl sa ba as r en s t (proj₁ fs)) (fed-trail dd cl sa ba as r en s t fs′)
      (proj₁ nx) (proj₂ nx) (fed-body-on dd cl sa ba as r en s t (proj₁ fs)) σ β
    where nx = fed-src-next dd cl sa ba as r en s t (proj₁ fs)

  -- A CONNECT feeds its body its own source's relation.
  fed-conn : ∀ {Δ Y C} {e : Ctx R Δ C} (dd : Down e) k (s : St Δ Y) (t : St (Y ∷ Δ) C) → Held (plug e (connS k s t))
           → Held (plug (rebase dd) (connS k s t))
           → FedAt dd s → FedAt (dBody {k = k} {s} dd) t → FedAt dd (connS k s t)
  fed-conn dd k@(cs cl sl sa ba as (just w) r en) s t fs fs′ is it = fed-done dd k s t owed (proj₁ fs) is it
  fed-conn dd k@(cs cl false sa ba as nothing r en) s t fs fs′ is it = fed-done dd k s t off (proj₁ fs) is it
  fed-conn dd (cs false true sa nothing as nothing r en) s t fs fs′ is it =
    fed-by refl refl refl refl (live-fed dd false sa nothing as r en s t fs fs′ is it)
  fed-conn dd (cs true true sa nothing as nothing r en) s t fs fs′ is it =
    fed-by refl refl refl refl (live-fed dd true sa nothing as r en s t fs fs′ (fed-ended dd sa as r en s t (proj₁ fs) is) it)
  fed-conn dd (cs cl true sa (just p) as nothing r en) s t fs fs′ is it =
    fed-by refl refl refl refl (live-fed dd cl sa (just p) as r en s t fs fs′ (sub-fed dd cl sa p as r en s t fs is) it)

  mutual
    walk : ∀ {Δ C} {e : Ctx R Δ C} (dd : Down e) (s : St Δ C) → Held (plug e s) → Held (plug (rebase dd) s) → FedAt dd s
    walk dd (pend p)                  fs fs′ = inj₁ (≋-⊒ (≋-by refl refl))
    walk dd (coldS l (ending p))      fs fs′ = inj₁ (≋-⊒ (≋-by refl refl))
    walk dd (coldS true (play τ u i t fr)) fs fs′ = inj₁ (≋-⊒ (≋-by refl refl))
    walk dd (coldS false (play τ u i t fr)) fs fs′ = inj₁ (≋-⊒ (≋-by refl refl))
    walk dd (coldS l over)            fs fs′ = inj₁ (≋-⊒ (≋-by refl refl))
    walk dd (ofS i p xs)              fs fs′ = inj₁ (≋-⊒ (≋-by refl refl))
    walk dd doneS                     fs fs′ = inj₁ (≋-⊒ (≋-by refl refl))
    walk dd (mapS f s)                fs fs′ = fed-by refl refl refl refl (fed-map f (walk (dMap dd) s fs fs′))
    walk dd (scanS f z s)             fs fs′ = fed-by refl refl refl refl (fed-scan f z (walk (dScan dd) s fs fs′))
    walk dd (cutS true a s)           fs fs′ = walk (dCut dd) s fs fs′
    walk dd (cutS false a s)          fs fs′ = fed-cut dd a s (proj₁ fs) (walk (dCut dd) s fs fs′)
    walk dd (lnS l s)                 fs fs′ = walk (dLn dd) s fs fs′
    walk dd (takeS i p free s)        fs fs′ = fed-by refl refl refl refl (fed-took i p (walk (dTake dd) s fs fs′))
    walk dd (takeS i p (cpAt k) s)    fs fs′ = fed-taken dd i p (cpAt k) s (proj₁ fs) (walk (dTake dd) s fs fs′)
    walk dd (takeS i p (cutAt k) s)   fs fs′ = fed-taken dd i p (cutAt k) s (proj₁ fs) (walk (dTake dd) s fs fs′)
    walk dd (takeS i p (overAt k) s)  fs fs′ = fed-taken dd i p (overAt k) s (proj₁ fs) (walk (dTake dd) s fs fs′)
    walk dd (flatS op f dn n qs s ls) fs fs′ = fed-flat dd op f dn n qs s ls (proj₁ fs) (walk (dOuter dd) s fs fs′) (walkLanes dd op f dn n qs s [] ls fs fs′)
    walk dd (connS k s t)             fs fs′ = fed-conn dd k s t fs fs′ (walk (dSrc dd) s fs fs′) (walk (dBody dd) t fs fs′)
    walk dd (joinS j false y ib)      fs fs′ = inj₁ (≋-⊒ (≋-by refl refl))
    walk dd (joinS j true y ib)       fs fs′ = fed-join dd j y ib (proj₁ fs)

    -- A flatMap's lanes, those before nearest first.
    walkLanes : ∀ {Δ A C} {e : Ctx R Δ C} (dd : Down e) op (f : A → _) dn n qs (s : St Δ A) (pre post : List (St Δ C))
              → Held (plug e (flatS op f dn n qs s (pre ʳ++ post))) → Held (plug (rebase dd) (flatS op f dn n qs s (pre ʳ++ post)))
              → All (FedAt dd) post
    walkLanes dd op f dn n qs s pre []         fs fs′ = []ᴬ
    walkLanes dd op f dn n qs s pre (l ∷ post) fs fs′ =
      walk (dLanes {pre = pre} {post} dd) l fs fs′ ∷ᴬ walkLanes dd op f dn n qs s (l ∷ pre) post fs fs′

-- A SOURCE'S SKIPS FED ITS BODY: the body fed a live source's skips
-- drops its own leading skips, each under one of them, and erases none
-- or more past them, to the body fed the rest.
src-fed : ∀ {R Γ X B} v q {P} (c : Ctx R Γ B) sa ba as r en (o : St Γ X) (b : St (X ∷ Γ) B) {h h′ : Events∞ X}
        → Sought v q P → KAfter (after q) (cand (inBody (cs false true sa ba as nothing r en) o c) b)
        → Before (after q) (own (connS (cs false true sa ba as nothing r en) o b))
        → Held (plug c (connS (cs false true sa ba as nothing r en) o b))
        → h ≋ stateᴺ (gh o) (envAt c) → Dropsˢ P h h′
        → (o′ : St Γ X) → Held (plug c (connS (cs false true sa ba as nothing r en) o′ b)) → Unpended o′ → h′ ≋ stateᴺ (gh o′) (envAt c)
        → Fed P (stateᴺ (gh b) (force h ∷ᴬ envAt c)) (stateᴺ (gh b) (force h′ ∷ᴬ envAt c))
src-fed v q c sa ba as r en o b so ka bf ft x d o′ ft′ u′ x′ =
  Walk.walk v q c sa ba as r en o b so ka bf ft x d o′ ft′ u′ x′ (Walk.base) b ft ft′
