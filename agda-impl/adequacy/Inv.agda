{-# OPTIONS --guardedness #-}

-- THE INVARIANT OF THE DIRECT LINK: a good tree, and by mode what the
-- focus is owed.  A rising event leads every other part of each merge it
-- climbs, and its own node owes only rows past it; a subscription in
-- flight is made where its binders are hot.
module adequacy.Inv where

open import Data.Bool using (Bool; true; false; T; _∧_)
open import Data.Bool.Properties using (∧-zeroʳ; ∧-identityʳ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Relation.Unary.All using ([])
open import Data.List using (List; _∷_; _ʳ++_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to tt₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst; cong)

open import Tree using (Obs; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.EmissionSet using (EmissionSet; DenEnv)
open import denotation.Events using (Timeline)
open import operation.PureObservable using (module Machine)
open Machine using (St; Ctx; Conf; ⟨_,_,_,_⟩; subscribing; absorbed; rising; plug; alive; nx; cp;
                    pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
                    free; cpAt; cutAt; overAt; closed; CS; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody)
                    renaming (Ev to Evᴹ; Shown to Shownᴹ)
open import adequacy.Rows using (env; rows; rowsL; pendRows; RT; Moves; Plus; toEv)
open import adequacy.Up using (≃-refl)
open import denotation.Laws.Worlds using (Ok; Hots)
open import adequacy.Bound using (Empty; EndLast; Good; G; GL; GLn; LnBody; SrcG; Held; HeldAt; held-shape; MergeG; mergeG-map; shape; Live; live)
open import adequacy.Skip using (After; LeadC)
open import adequacy.Swap using (goodL-ʳ++; goodL-ʳ++⁻; goodL-swap; Swap; good-swap; rowsL-ʳ++)
open import adequacy.Above using (Anc; Join; JR; rows-jr; IsLn; IsCutT; LnParent; HeldIf)

-- The frames a rising or subscribing event climbs, open.
UpO : ∀ {R Γ A} → Ctx R Γ A → Set
UpO top                           = ⊤
UpO (inMap f c)                   = UpO c
UpO (inScan f z c)                = UpO c
UpO (inTake i q w c)              = UpO c
UpO (inCut true a c)              = UpO c
UpO (inLn true c)                 = UpO c
UpO (inOuter op f d n q ls c)     = UpO c
UpO (inLanes op f d n q o pre post c) = UpO c
UpO (inSrc k b c)                 = UpO c
UpO (inBody k o c)                = UpO c
UpO _                             = ⊥

-- A node an event can rise out of: not cut, not out of its list.
Open : ∀ {Γ A} → St Γ A → Set
Open (lnS false s)   = ⊥
Open (cutS false a s) = ⊥
Open _               = ⊤

-- An end leaves nothing owed.
Ends : ∀ {A} → Evᴹ A → EmissionSet A → Set
Ends (nx _) t = ⊤
Ends cp     t = Empty t

-- A subscription owed is made where the binders in scope are hot.
Subs : ∀ {Γ A} → DenEnv Γ → St Γ A → Set
Subs ρ (pend o q) = Ok (Hots ρ) q
Subs ρ _          = ⊤

Lead : ∀ {R} → Conf R → Set
Lead ⟨ c , s , rising e , p ⟩ = UpO c × LeadC c p × Open s × After p (rows (env c) s) × Ends e (rows (env c) s)
Lead ⟨ c , s , subscribing , p ⟩ = UpO c × Subs (env c) s
Lead ⟨ c , s , absorbed , p ⟩    = ⊤

open-alive : ∀ {Γ A} (s : St Γ A) → Open s → alive s ≡ false → ⊥
open-alive (lnS false _)       () _
open-alive (lnS true _)        _ ()
open-alive (pend _ _)            _ ()
open-alive (coldS _ _)         _ ()
open-alive (ofS _ _ _)         _ ()
open-alive doneS               _ ()
open-alive (mapS _ _)          _ ()
open-alive (scanS _ _ _)       _ ()
open-alive (cutS _ _ _)        _ ()
open-alive (takeS _ _ _ _)     _ ()
open-alive (flatS _ _ _ _ _ _ _) _ ()
open-alive (connS _ _ _)       _ ()
open-alive (joinS _ _ _ _)     _ ()

------------------------------------------------------------------------
-- A good tree, cut at a hole

-- Whether a hole is still owed: no cut switched off above it.
liv : ∀ {R Γ A} → Ctx R Γ A → Bool
liv top                               = true
liv (inMap f c)                       = liv c
liv (inScan f z c)                    = liv c
liv (inCut l a c)                     = liv c ∧ l
liv (inLn b c)                        = liv c
liv (inTake i q w c)                  = liv c
liv (inOuter op f d n q ls c)         = liv c
liv (inLanes op f d n q o pre post c) = liv c
liv (inSrc k b c)                     = liv c
liv (inBody k o c)                    = liv c

-- What a frame's hole must be: under a merge's lanes, a lane.
GoodF : ∀ {R Γ A} → Ctx R Γ A → St Γ A → Set₁
GoodF (inLanes op f d n q o pre post c) s = GLn (env c) (liv c) s
GoodF top                s = G [] true s
GoodF (inMap f c)        s = G (env c) (liv c) s
GoodF (inScan f z c)     s = G (env c) (liv c) s
GoodF (inCut l a c)      s = G (env c) (liv c ∧ l) s
GoodF (inLn b c)         s = G (env c) (liv c) s
GoodF (inTake i q w c)   s = G (env c) (liv c) s
GoodF (inOuter op f d n q ls c) s = G (env c) (liv c) s
GoodF (inSrc k b c)      s = SrcG (env c) (liv c) (CS.bodyAt k) s
GoodF (inBody k o c)     s = G (env (inBody k o c)) (liv c) s

-- A hole's rows, good either way.
unF : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) → GoodF c s → G (env c) (liv c) s ⊎ (GLn (env c) (liv c) s ⊎ Held s)
unF (inLanes op f d n q o pre post c) s g = inj₂ (inj₁ g)
unF top                s g = inj₁ g
unF (inMap f c)        s g = inj₁ g
unF (inScan f z c)     s g = inj₁ g
unF (inCut l a c)      s g = inj₁ g
unF (inLn b c)         s g = inj₁ g
unF (inTake i q w c)   s g = inj₁ g
unF (inOuter op f d n q ls c) s g = inj₁ g
unF (inSrc k b c)      s g = srcUn (CS.bodyAt k) g
  where
    srcUn : ∀ m → SrcG (env c) (liv c) m s → G (env c) (liv c) s ⊎ (GLn (env c) (liv c) s ⊎ Held s)
    srcUn nothing  g′ = inj₁ g′
    srcUn (just _) g′ = inj₂ (inj₂ (held-shape g′))
unF (inBody k o c)     s g = inj₁ g

lnbody-good : ∀ {Γ A} {ρ : DenEnv Γ} v b (s : St Γ A) → LnBody ρ v b s → G ρ v s
lnbody-good v b (cutS l a s) (refl , g , _) = g
lnbody-good v b (pend _ _)              ()
lnbody-good v b (coldS _ _)           ()
lnbody-good v b (ofS _ _ _)           ()
lnbody-good v b doneS                 ()
lnbody-good v b (mapS _ _)            ()
lnbody-good v b (scanS _ _ _)         ()
lnbody-good v b (lnS _ _)             ()
lnbody-good v b (takeS _ _ _ _)       ()
lnbody-good v b (flatS _ _ _ _ _ _ _) ()
lnbody-good v b (connS _ _ _)         ()
lnbody-good v b (joinS _ _ _ _)       ()

good-split : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) → Good [] (plug c s) → GoodF c s
good-split top s g = g
good-split (inMap f c) s g with good-split c (mapS f s) g
... | gf with unF c _ gf
... | inj₁ gm = gm
... | inj₂ (inj₁ ())
... | inj₂ (inj₂ ())
good-split (inScan f z c) s g with good-split c (scanS f z s) g
... | gf with unF c _ gf
... | inj₁ gm = gm
... | inj₂ (inj₁ ())
... | inj₂ (inj₂ ())
good-split (inCut l a c) s g with good-split c (cutS l a s) g
... | gf with unF c _ gf
... | inj₁ gm = gm
... | inj₂ (inj₁ ())
... | inj₂ (inj₂ ())
good-split (inLn b c) s g with good-split c (lnS b s) g
... | gf with unF c _ gf
... | inj₁ ()
... | inj₂ (inj₁ gl) = lnbody-good {ρ = env c} (liv c) b s gl
... | inj₂ (inj₂ ())
good-split (inTake i q w c) s g with good-split c (takeS i q w s) g
... | gf with unF c _ gf
... | inj₁ gm = gm
... | inj₂ (inj₁ ())
... | inj₂ (inj₂ ())
good-split (inOuter (mergeᶠ nothing) f d n q ls c) s g with good-split c (flatS (mergeᶠ nothing) f d n q s ls) g
... | gf with unF c _ gf
... | inj₁ gm = MergeG.outer gm
... | inj₂ (inj₁ ())
... | inj₂ (inj₂ ())
good-split (inOuter (mergeᶠ (just m)) f d n q ls c) s g with good-split c (flatS (mergeᶠ (just m)) f d n q s ls) g
... | gf with unF c _ gf
... | inj₁ gm = MergeG.outer (proj₁ gm)
... | inj₂ (inj₁ ())
... | inj₂ (inj₂ ())
good-split (inOuter switchᶠ f d n q ls c) s g with good-split c (flatS switchᶠ f d n q s ls) g
... | gf with unF c _ gf
... | inj₁ gm = MergeG.outer gm
... | inj₂ (inj₁ ())
... | inj₂ (inj₂ ())
good-split (inOuter exhaustᶠ f d n q ls c) s g with good-split c (flatS exhaustᶠ f d n q s ls) g
... | gf with unF c _ gf
... | inj₁ gm = MergeG.outer gm
... | inj₂ (inj₁ ())
... | inj₂ (inj₂ ())
good-split (inLanes (mergeᶠ nothing) f d n q o pre post c) s g with good-split c (flatS (mergeᶠ nothing) f d n q o (pre ʳ++ s ∷ post)) g
... | gf with unF c _ gf
... | inj₁ gm = proj₁ (proj₂ (goodL-ʳ++⁻ pre (MergeG.lanesG gm)))
... | inj₂ (inj₁ ())
... | inj₂ (inj₂ ())
good-split (inLanes (mergeᶠ (just m)) f d n q o pre post c) s g with good-split c (flatS (mergeᶠ (just m)) f d n q o (pre ʳ++ s ∷ post)) g
... | gf with unF c _ gf
... | inj₁ gm = proj₁ (proj₂ (goodL-ʳ++⁻ pre (MergeG.lanesG (proj₁ gm))))
... | inj₂ (inj₁ ())
... | inj₂ (inj₂ ())
good-split (inLanes switchᶠ f d n q o pre post c) s g with good-split c (flatS switchᶠ f d n q o (pre ʳ++ s ∷ post)) g
... | gf with unF c _ gf
... | inj₁ gm = proj₁ (proj₂ (goodL-ʳ++⁻ pre (MergeG.lanesG gm)))
... | inj₂ (inj₁ ())
... | inj₂ (inj₂ ())
good-split (inLanes exhaustᶠ f d n q o pre post c) s g with good-split c (flatS exhaustᶠ f d n q o (pre ʳ++ s ∷ post)) g
... | gf with unF c _ gf
... | inj₁ gm = proj₁ (proj₂ (goodL-ʳ++⁻ pre (MergeG.lanesG gm)))
... | inj₂ (inj₁ ())
... | inj₂ (inj₂ ())
good-split (inSrc k b c) s g with good-split c (connS k s b) g
... | gf with unF c _ gf
... | inj₁ (gs , _) = gs
... | inj₂ (inj₁ ())
... | inj₂ (inj₂ ())
good-split (inBody k o c) s g with good-split c (connS k o s) g
... | gf with unF c _ gf
... | inj₁ (_ , gb , _) = gb
... | inj₂ (inj₁ ())
... | inj₂ (inj₂ ())

-- The good node a frame sits on.
node-good : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) → Good [] (plug c s) → (GLn (env c) (liv c) s → ⊥) → (Held s → ⊥) → G (env c) (liv c) s
node-good c s g nl nh with unF c s (good-split c s g)
... | inj₁ gs        = gs
... | inj₂ (inj₁ gl) = ⊥-elim (nl gl)
... | inj₂ (inj₂ h)  = ⊥-elim (nh h)

-- Under open frames every hole is owed.
upo-liv : ∀ {R Γ A} (c : Ctx R Γ A) → UpO c → liv c ≡ true
upo-liv top              _ = refl
upo-liv (inMap f c)      u = upo-liv c u
upo-liv (inScan f z c)   u = upo-liv c u
upo-liv (inTake i q w c) u = upo-liv c u
upo-liv (inCut true a c) u rewrite upo-liv c u = refl
upo-liv (inLn true c)    u = upo-liv c u
upo-liv (inOuter op f d n q ls c) u = upo-liv c u
upo-liv (inLanes op f d n q o pre post c) u = upo-liv c u
upo-liv (inCut false a c) ()
upo-liv (inLn false c)    ()
upo-liv (inSrc k b c)  u       = upo-liv c u
upo-liv (inBody k o c) u     = upo-liv c u

------------------------------------------------------------------------
-- A good tree, read through its hole's rows

tr : ∀ {Γ A} {ρ : DenEnv Γ} {v} (s : St Γ A) → v ≡ true → G ρ v s → G ρ true s
tr s refl g = g

live-t : ∀ {X : Set} v → v ≡ true → X → Live v X
live-t true refl x = x

live-g : ∀ {X : Set} v → v ≡ true → Live v X → X
live-g true refl x = x

ln-g : ∀ {Γ A} {ρ : DenEnv Γ} {v} (s : St Γ A) → IsLn s → G ρ v s → ⊥
ln-g (lnS _ _)             _  ()
ln-g (pend _ _)            ()
ln-g (coldS _ _)           ()
ln-g (ofS _ _ _)           ()
ln-g doneS                 ()
ln-g (mapS _ _)            ()
ln-g (scanS _ _ _)         ()
ln-g (cutS _ _ _)          ()
ln-g (takeS _ _ _ _)       ()
ln-g (flatS _ _ _ _ _ _ _) ()
ln-g (connS _ _ _)         ()
ln-g (joinS _ _ _ _)       ()

held-g : ∀ {Γ A} {ρ : DenEnv Γ} {v} (s : St Γ A) → Held s → G ρ v s → ⊥
held-g (pend _ _)            _  ()
held-g (lnS _ _)             ()
held-g (coldS _ _)           ()
held-g (ofS _ _ _)           ()
held-g doneS                 ()
held-g (mapS _ _)            ()
held-g (scanS _ _ _)         ()
held-g (cutS _ _ _)          ()
held-g (takeS _ _ _ _)       ()
held-g (flatS _ _ _ _ _ _ _) ()
held-g (connS _ _ _)         ()
held-g (joinS _ _ _ _)       ()

gln-ln : ∀ {Γ A} {ρ : DenEnv Γ} {v} (s : St Γ A) → GLn ρ v s → IsLn s
gln-ln (lnS _ _)             _ = tt
gln-ln (pend _ _)            ()
gln-ln (coldS _ _)           ()
gln-ln (ofS _ _ _)           ()
gln-ln doneS                 ()
gln-ln (mapS _ _)            ()
gln-ln (scanS _ _ _)         ()
gln-ln (cutS _ _ _)          ()
gln-ln (takeS _ _ _ _)       ()
gln-ln (flatS _ _ _ _ _ _ _) ()
gln-ln (connS _ _ _)         ()
gln-ln (joinS _ _ _ _)       ()

held-if : ∀ {Γ A} {ρ : DenEnv Γ} {v} m (s : St Γ A) → SrcG ρ v m s → HeldIf m s
held-if nothing  s g = tt₁
held-if (just _) s g = held-shape g

-- A joiner node from its parts' facts, and back.
mkG : ∀ {Γ A B} op {ρ : DenEnv Γ} {f : A → Obs Timeline Γ B} {d n q} {o : St Γ A} {ls : List (St Γ B)}
    → G ρ true o → GL ρ true ls → Join op d n q (live ls) (rows ρ o) (rowsL ρ ls) → G ρ true (flatS op f d n q o ls)
mkG (mergeᶠ nothing)  go gl j = record { outer = go ; lanesG = gl ; fresh = Join.fresh j ; count = Join.count j ; spent = Join.spent j ; rooted = Join.rooted j }
mkG (mergeᶠ (just m)) go gl j = record { outer = go ; lanesG = gl ; fresh = refl ; count = Join.count j ; spent = Join.spent j ; rooted = Join.rooted j } , Join.fresh j
mkG switchᶠ           go gl j = record { outer = go ; lanesG = gl ; fresh = Join.fresh j ; count = Join.count j ; spent = Join.spent j ; rooted = Join.rooted j }
mkG exhaustᶠ          go gl j = record { outer = go ; lanesG = gl ; fresh = Join.fresh j ; count = Join.count j ; spent = Join.spent j ; rooted = Join.rooted j }

unG : ∀ {Γ A B} op {ρ : DenEnv Γ} {f : A → Obs Timeline Γ B} {d n q} {o : St Γ A} {ls : List (St Γ B)}
    → G ρ true (flatS op f d n q o ls) → G ρ true o × GL ρ true ls × Join op d n q (live ls) (rows ρ o) (rowsL ρ ls)
unG (mergeᶠ nothing)  m       = MergeG.outer m , MergeG.lanesG m , record { fresh = MergeG.fresh m ; count = MergeG.count m ; spent = MergeG.spent m ; rooted = MergeG.rooted m }
unG (mergeᶠ (just k)) (m , w) = MergeG.outer m , MergeG.lanesG m , record { fresh = w ; count = MergeG.count m ; spent = MergeG.spent m ; rooted = MergeG.rooted m }
unG switchᶠ           m       = MergeG.outer m , MergeG.lanesG m , record { fresh = MergeG.fresh m ; count = MergeG.count m ; spent = MergeG.spent m ; rooted = MergeG.rooted m }
unG exhaustᶠ          m       = MergeG.outer m , MergeG.lanesG m , record { fresh = MergeG.fresh m ; count = MergeG.count m ; spent = MergeG.spent m ; rooted = MergeG.rooted m }

-- Frames read through any rows are open.
anc-liv : ∀ {R Γ A} (c : Ctx R Γ A) {s : St Γ A} {H} → Anc c s H → liv c ≡ true
anc-liv top                a = refl
anc-liv (inMap f c)        a = anc-liv c a
anc-liv (inScan f z c)     a = anc-liv c a
anc-liv (inCut true a′ c)  a = trans (∧-identityʳ (liv c)) (anc-liv c a)
anc-liv (inCut false a′ c) ()
anc-liv (inLn true c)      (_ , _ , _ , a) = anc-liv c a
anc-liv (inLn false c)     ()
anc-liv (inTake i q w c)   a = anc-liv c a
anc-liv (inOuter op f d n q ls c) (_ , _ , a) = anc-liv c a
anc-liv (inLanes op f d n q o pre post c) (_ , _ , _ , _ , _ , a) = anc-liv c a
anc-liv (inSrc k b c)      (_ , _ , _ , _ , _ , a) = anc-liv c a
anc-liv (inBody k o c)     (_ , _ , _ , _ , a) = anc-liv c a

-- A GOOD NODE, IN ITS FRAME: where its frames place it, a node good
-- outright is what its frame asks.
node-f : ∀ {R Γ A} (c : Ctx R Γ A) (N : St Γ A) {H} → Anc c N H → G (env c) true N → GoodF c N
node-f top                N a g = g
node-f (inMap f c)        N a g = subst (λ v → G (env c) v N) (sym (anc-liv (inMap f c) a)) g
node-f (inScan f z c)     N a g = subst (λ v → G (env c) v N) (sym (anc-liv (inScan f z c) a)) g
node-f (inCut l a′ c)     N a g = subst (λ v → G (env c) v N) (sym (anc-liv (inCut l a′ c) a)) g
node-f (inLn b c)         N a g = subst (λ v → G (env c) v N) (sym (anc-liv (inLn b c) a)) g
node-f (inTake i q w c)   N a g = subst (λ v → G (env c) v N) (sym (anc-liv (inTake i q w c) a)) g
node-f (inOuter op f d n q ls c) N a g = subst (λ v → G (env c) v N) (sym (anc-liv (inOuter op f d n q ls c) a)) g
node-f (inLanes op f d n q o pre post c) N (il , _) g = ⊥-elim (ln-g N il g)
node-f (inSrc k b c)      N a@(h , _) g = src (CS.bodyAt k) h (anc-liv (inSrc k b c) a)
  where
    src : ∀ m → HeldIf m N → liv c ≡ true → SrcG (env c) (liv c) m N
    src nothing  _ lv = subst (λ v → G (env c) v N) (sym lv) g
    src (just _) h lv = ⊥-elim (held-g N h g)
node-f (inBody k o c)     N a g = subst (λ v → G (env (inBody k o c)) v N) (sym (anc-liv (inBody k o c) a)) g

data CutT {Γ A} : St Γ A → Set₁ where
  cutT : ∀ a s → CutT (cutS true a s)

cut-t : ∀ {Γ A} (s : St Γ A) → IsCutT s → CutT s
cut-t (cutS true a s)       _ = cutT a s
cut-t (cutS false a s)      ()
cut-t (pend _ _)            ()
cut-t (coldS _ _)           ()
cut-t (ofS _ _ _)           ()
cut-t doneS                 ()
cut-t (mapS _ _)            ()
cut-t (scanS _ _ _)         ()
cut-t (lnS _ _)             ()
cut-t (takeS _ _ _ _)       ()
cut-t (flatS _ _ _ _ _ _ _) ()
cut-t (connS _ _ _)         ()
cut-t (joinS _ _ _ _)       ()

-- A lane's body, in its lane.
ln-f : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) → IsCutT s → LnParent c → EndLast (rows (env c) s) → G (env c) (liv c) s → liv c ≡ true → GoodF c (lnS true s)
ln-f (inLanes op f d n q o pre post c) s ct _ el g lv with cut-t s ct
... | cutT a s₀ = refl , g , live-t (liv c ∧ true) (trans (∧-identityʳ (liv c)) lv) (λ {x} {y} {z} → el {x} {y} {z})
ln-f top                s ct () el g lv
ln-f (inMap f c)        s ct () el g lv
ln-f (inScan f z c)     s ct () el g lv
ln-f (inCut l a c)      s ct () el g lv
ln-f (inLn b c)         s ct () el g lv
ln-f (inTake i q w c)   s ct () el g lv
ln-f (inOuter op f d n q ls c) s ct () el g lv
ln-f (inSrc k b c)      s ct () el g lv
ln-f (inBody k o c)     s ct () el g lv

-- THE TREE BACK FROM ITS FRAMES: a hole good in its frame, its frames
-- read through its own rows, is a good tree.
anc-join : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) → Anc c s (rows (env c) s) → GoodF c s → Good [] (plug c s)
anc-join top                s _ g = g
anc-join (inMap f c)        s a g = anc-join c (mapS f s) a (node-f c (mapS f s) a (tr s (anc-liv (inMap f c) a) g))
anc-join (inScan f z c)     s a g = anc-join c (scanS f z s) a (node-f c (scanS f z s) a (tr s (anc-liv (inScan f z c) a) g))
anc-join (inCut true a′ c)  s a g = anc-join c (cutS true a′ s) a (node-f c (cutS true a′ s) a (tr s (anc-liv (inCut true a′ c) a) g))
anc-join (inCut false a′ c) s () g
anc-join (inLn true c)      s (ct , el , lp , a) g = anc-join c (lnS true s) a (ln-f c s ct lp el g (anc-liv c a))
anc-join (inLn false c)     s () g
anc-join (inTake i q w c)   s a g = anc-join c (takeS i q w s) a (node-f c (takeS i q w s) a (tr s (anc-liv (inTake i q w c) a) g))
anc-join (inOuter op f d n q ls c) s (gl , j , a) g =
  anc-join c N a′ (node-f c N a (mkG op (tr s (anc-liv c a) g) gl j))
  where
    N  = flatS op f d n q s ls
    a′ = subst (Anc c N) (sym (rows-jr (env c) op f d n q s ls)) a
anc-join (inLanes op f d n q o pre post c) s (il , go , gp , gq , j , a) g =
  anc-join c N a′ (node-f c N a (mkG op go (goodL-ʳ++ pre gp (subst (λ v → GLn (env c) v s) (anc-liv c a) g , gq))
                                    (subst (Join op d n q _ (rows (env c) o)) (sym (rowsL-ʳ++ pre)) j)))
  where
    N  = flatS op f d n q o (pre ʳ++ s ∷ post)
    a′ = subst (Anc c N) (sym (trans (rows-jr (env c) op f d n q o (pre ʳ++ s ∷ post))
                                     (cong (JR op (λ x → pendRows (env c) (f x)) (rows (env c) o) d n q) (rowsL-ʳ++ pre)))) a
anc-join (inSrc k b c)      s a@(h , gb , sp , tl , ok , a₁) g =
  anc-join c (connS k s b) a₁ (node-f c (connS k s b) a₁ (subst (λ v → SrcG (env c) v (CS.bodyAt k) s) (anc-liv (inSrc k b c) a) g , gb , sp , tl , ok))
anc-join (inBody k o c)     s a@(gs , sp , tl , ok , a₁) g =
  anc-join c (connS k o s) a₁ (node-f c (connS k o s) a₁ (gs , tr s (anc-liv (inBody k o c) a) g , sp , tl , ok))

-- A lane's facts, its frame's.
ln-split : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) → GoodF c (lnS true s) → liv c ≡ true → IsCutT s × EndLast (rows (env c) s) × LnParent c
ln-split (inLanes op f d n q o pre post c) (cutS true a s₀) (refl , _ , el) lv = tt , (λ {x} {y} {z} → live-g (liv c ∧ true) (trans (∧-identityʳ (liv c)) lv) el {x} {y} {z}) , tt
ln-split (inLanes op f d n q o pre post c) (cutS false a s₀) (() , _) lv
ln-split (inLanes op f d n q o pre post c) (pend _ _)            () lv
ln-split (inLanes op f d n q o pre post c) (coldS _ _)           () lv
ln-split (inLanes op f d n q o pre post c) (ofS _ _ _)           () lv
ln-split (inLanes op f d n q o pre post c) doneS                 () lv
ln-split (inLanes op f d n q o pre post c) (mapS _ _)            () lv
ln-split (inLanes op f d n q o pre post c) (scanS _ _ _)         () lv
ln-split (inLanes op f d n q o pre post c) (lnS _ _)             () lv
ln-split (inLanes op f d n q o pre post c) (takeS _ _ _ _)       () lv
ln-split (inLanes op f d n q o pre post c) (flatS _ _ _ _ _ _ _) () lv
ln-split (inLanes op f d n q o pre post c) (connS _ _ _)         () lv
ln-split (inLanes op f d n q o pre post c) (joinS _ _ _ _)       () lv
ln-split top                s () lv
ln-split (inMap f c)        s () lv
ln-split (inScan f z c)     s () lv
ln-split (inCut l a c)      s () lv
ln-split (inLn b c)         s () lv
ln-split (inTake i q w c)   s () lv
ln-split (inOuter op f d n q ls c) s () lv
ln-split (inSrc k b c)      s g lv with CS.bodyAt k | g
... | nothing | ()
... | just _  | ()
ln-split (inBody k o c)     s () lv

-- THE TREE READ FROM ITS FRAMES: a good tree, its frames open, reads
-- every frame through its hole's rows.
anc-split : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) → UpO c → Good [] (plug c s) → Anc c s (rows (env c) s)
anc-split top                s u g = tt₁
anc-split (inMap f c)        s u g = anc-split c (mapS f s) u g
anc-split (inScan f z c)     s u g = anc-split c (scanS f z s) u g
anc-split (inCut true a c)   s u g = anc-split c (cutS true a s) u g
anc-split (inCut false a c)  s () g
anc-split (inLn true c)      s u g =
  let (ct , el , lp) = ln-split c s (good-split c (lnS true s) g) (upo-liv c u) in ct , el , lp , anc-split c (lnS true s) u g
anc-split (inLn false c)     s () g
anc-split (inTake i q w c)   s u g = anc-split c (takeS i q w s) u g
anc-split (inOuter op f d n q ls c) s u g =
  let (_ , gl , j) = unG op (tr N (upo-liv c u) (node-good c N g (λ ()) (λ ())))
  in gl , j , subst (Anc c N) (rows-jr (env c) op f d n q s ls) (anc-split c N u g)
  where N = flatS op f d n q s ls
anc-split (inLanes op f d n q o pre post c) s u g =
  let (go , gl , j) = unG op (tr N (upo-liv c u) (node-good c N g (λ ()) (λ ())))
      (gp , gs , gq) = goodL-ʳ++⁻ pre gl
  in gln-ln s gs , go , gp , gq , subst (Join op d n q _ (rows (env c) o)) (rowsL-ʳ++ pre) j
     , subst (Anc c N) (trans (rows-jr (env c) op f d n q o (pre ʳ++ s ∷ post))
                              (cong (JR op (λ x → pendRows (env c) (f x)) (rows (env c) o) d n q) (rowsL-ʳ++ pre))) (anc-split c N u g)
  where N = flatS op f d n q o (pre ʳ++ s ∷ post)
anc-split (inSrc k b c)      s u g =
  let (gs , gb , sp , tl , ok) = tr N (upo-liv c u) (node-good c N g (λ ()) (λ ()))
  in held-if (CS.bodyAt k) s gs , gb , sp , tl , ok , anc-split c N u g
  where N = connS k s b
anc-split (inBody k o c)     s u g =
  let (gs , gb , sp , tl , ok) = tr N (upo-liv c u) (node-good c N g (λ ()) (λ ()))
  in gs , sp , tl , ok , anc-split c N u g
  where N = connS k o s

-- The tree the seeker reads: a subscription still owed owes it nothing.
Seen : ∀ {Γ A} → St Γ A → St Γ A
Seen (pend o q) = doneS
Seen s          = s

-- What the tree is owed, by mode: a rising event's frames read through
-- it, its hole's facts its frame's.
GoodC : ∀ {R} → Conf R → Set₁
GoodC ⟨ c , s , rising e , p ⟩    = Anc c s (Plus (rows (env c) s) p (toEv e)) × GoodF c s
GoodC ⟨ c , s , subscribing , p ⟩ = Good [] (plug c (Seen s))
GoodC ⟨ c , s , absorbed , p ⟩    = Good [] (plug c s)

record Inv {R} (k : Conf R) : Set₁ where
  constructor inv
  field
    good : GoodC k
    lead : Lead k
open Inv public

-- One step against the rows, the invariant kept.
Sim : ∀ {R} → Conf R → Shownᴹ R → Conf R → Set₁
Sim k sh k′ = Inv k → Inv k′ × Moves (RT k) sh (RT k′)

------------------------------------------------------------------------
-- A hole under a cut switched off

-- A source its connect has seen complete, above the hole.
Shut : ∀ {R Γ A} → Ctx R Γ A → Set
Shut top                               = ⊥
Shut (inMap f c)                       = Shut c
Shut (inScan f z c)                    = Shut c
Shut (inCut l a c)                     = Shut c
Shut (inLn b c)                        = Shut c
Shut (inTake i q w c)                  = Shut c
Shut (inOuter op f d n q ls c)         = Shut c
Shut (inLanes op f d n q o pre post c) = Shut c
Shut (inSrc k b c)                     = T (CS.closed k) ⊎ Shut c
Shut (inBody k o c)                    = Shut c

-- A closed hole is under a cut switched off, or in a completed source.
closed-dead : ∀ {R Γ A} (c : Ctx R Γ A) → closed c ≡ true → liv c ≡ false ⊎ Shut c
closed-dead top              ()
closed-dead (inMap f c)      cl = closed-dead c cl
closed-dead (inScan f z c)   cl = closed-dead c cl
closed-dead (inTake i q w c) cl = closed-dead c cl
closed-dead (inCut false a c) _  = inj₁ (∧-zeroʳ (liv c))
closed-dead (inCut true a c) cl with closed-dead c cl
... | inj₁ d = inj₁ (trans (∧-identityʳ (liv c)) d)
... | inj₂ h = inj₂ h
closed-dead (inLn b c)       cl = closed-dead c cl
closed-dead (inOuter op f d n q ls c) cl = closed-dead c cl
closed-dead (inLanes op f d n q o pre post c) cl = closed-dead c cl
closed-dead (inSrc k b c)    cl with CS.closed k
... | true  = inj₂ (inj₁ tt)
... | false with closed-dead c cl
...   | inj₁ d  = inj₁ d
...   | inj₂ sh = inj₂ (inj₂ sh)
closed-dead (inBody k o c)   cl = closed-dead c cl

-- Swapped where nothing is owed: only the shape asked.
record Swap₀ {Γ A} (ρ : DenEnv Γ) (s s′ : St Γ A) : Set₁ where
  field
    node₀ : G ρ false s → G ρ false s′
    lane₀ : GLn ρ false s → GLn ρ false s′
    body₀ : ∀ b → LnBody ρ false b s → LnBody ρ false b s′
    held₀ : ∀ {q} → HeldAt ρ false q s → HeldAt ρ false q s′
open Swap₀

-- The cut that switched the lane off: nothing under it is owed above.
killed : ∀ {Γ A} {ρ : DenEnv Γ} a {s s′ : St Γ A} → Swap₀ ρ s s′ → Swap ρ (cutS false a s) (cutS false a s′)
killed a sw = record
  { same  = ≃-refl
  ; live≡ = refl
  ; node  = λ { true g → node₀ sw g ; false g → node₀ sw g }
  ; lane  = λ _ ()
  ; body  = λ { true _ (refl , g , _) → refl , node₀ sw g , tt ; false _ (refl , g , _) → refl , node₀ sw g , tt }
  ; held  = λ ()
  ; told  = λ _ _ → tt }

dead-swap : ∀ {R Γ A} (c : Ctx R Γ A) {s s′ : St Γ A} → liv c ≡ false → Swap₀ (env c) s s′ → Good [] (plug c s) → Good [] (plug c s′)
dead-swap top               () sw g
dead-swap (inMap f c)       dd sw g = dead-swap c dd (record { node₀ = node₀ sw ; lane₀ = λ () ; body₀ = λ _ () ; held₀ = λ () }) g
dead-swap (inScan f z c)    dd sw g = dead-swap c dd (record { node₀ = node₀ sw ; lane₀ = λ () ; body₀ = λ _ () ; held₀ = λ () }) g
dead-swap (inCut false a c) dd sw g = good-swap c (killed a sw) g
dead-swap (inCut true a c)  dd sw g =
  dead-swap c (trans (sym (∧-identityʳ (liv c))) dd) (record { node₀ = node₀ sw ; lane₀ = λ () ; body₀ = λ { b (eq , g′ , _) → eq , node₀ sw g′ , tt } ; held₀ = λ () }) g
dead-swap (inLn b c)        dd sw g = dead-swap c dd (record { node₀ = λ () ; lane₀ = body₀ sw b ; body₀ = λ _ () ; held₀ = λ () }) g
dead-swap (inTake i q w c)  dd sw g = dead-swap c dd (record { node₀ = node₀ sw ; lane₀ = λ () ; body₀ = λ _ () ; held₀ = λ () }) g
dead-swap (inOuter (mergeᶠ nothing) f d n q ls c) dd sw g =
  dead-swap c dd (record { node₀ = mergeG-map (node₀ sw) (λ x → x) (λ x → x) (λ x → x) (λ x → x) ; lane₀ = λ () ; body₀ = λ _ () ; held₀ = λ () }) g
dead-swap (inOuter (mergeᶠ (just _)) f d n q ls c) dd sw g =
  dead-swap c dd (record { node₀ = λ (m , w) → mergeG-map (node₀ sw) (λ x → x) (λ x → x) (λ x → x) (λ x → x) m , w ; lane₀ = λ () ; body₀ = λ _ () ; held₀ = λ () }) g
dead-swap (inOuter switchᶠ f d n q ls c)  dd sw g =
  dead-swap c dd (record { node₀ = mergeG-map (node₀ sw) (λ x → x) (λ x → x) (λ x → x) (λ x → x) ; lane₀ = λ () ; body₀ = λ _ () ; held₀ = λ () }) g
dead-swap (inOuter exhaustᶠ f d n q ls c) dd sw g =
  dead-swap c dd (record { node₀ = mergeG-map (node₀ sw) (λ x → x) (λ x → x) (λ x → x) (λ x → x) ; lane₀ = λ () ; body₀ = λ _ () ; held₀ = λ () }) g
dead-swap (inLanes (mergeᶠ nothing) f d n q o pre post c) dd sw g =
  dead-swap c dd (record { node₀ = mergeG-map (λ x → x) (goodL-swap pre (lane₀ sw)) (λ x → x) (λ x → x) (λ x → x) ; lane₀ = λ () ; body₀ = λ _ () ; held₀ = λ () }) g
dead-swap (inLanes (mergeᶠ (just _)) f d n q o pre post c) dd sw g =
  dead-swap c dd (record { node₀ = λ (m , w) → mergeG-map (λ x → x) (goodL-swap pre (lane₀ sw)) (λ x → x) (λ x → x) (λ x → x) m , w ; lane₀ = λ () ; body₀ = λ _ () ; held₀ = λ () }) g
dead-swap (inLanes switchᶠ f d n q o pre post c)  dd sw g =
  dead-swap c dd (record { node₀ = mergeG-map (λ x → x) (goodL-swap pre (lane₀ sw)) (λ x → x) (λ x → x) (λ x → x) ; lane₀ = λ () ; body₀ = λ _ () ; held₀ = λ () }) g
dead-swap (inLanes exhaustᶠ f d n q o pre post c) dd sw g =
  dead-swap c dd (record { node₀ = mergeG-map (λ x → x) (goodL-swap pre (lane₀ sw)) (λ x → x) (λ x → x) (λ x → x) ; lane₀ = λ () ; body₀ = λ _ () ; held₀ = λ () }) g
dead-swap (inSrc k b c)     dd sw g =
  dead-swap c dd (record { node₀ = λ { (gs , gb , _) → src₀ (CS.bodyAt k) gs , shape b gb , tt , tt , tt } ; lane₀ = λ () ; body₀ = λ _ () ; held₀ = λ () }) g
  where
    src₀ : ∀ m → SrcG (env c) false m _ → SrcG (env c) false m _
    src₀ nothing  = node₀ sw
    src₀ (just _) = held₀ sw
dead-swap (inBody k o c)    dd sw g = dead-swap c dd (record { node₀ = λ { (gs , gb , sp , tl) → gs , node₀ sw gb , sp , tl } ; lane₀ = λ () ; body₀ = λ _ () ; held₀ = λ () }) g
