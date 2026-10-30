{-# OPTIONS --guardedness #-}

-- THE INVARIANT OF THE DIRECT LINK: a good tree, and by mode what the
-- focus is owed.  A rising event leads every other part of each merge it
-- climbs, and its own node owes only rows past it; a mark run or a
-- subscription in flight asks only that every live part still owes.
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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)

open import Tree using (mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.EmissionSet using (EmissionSet; DenEnv; module Connecting; module Scan)
open import operation.PureObservable using (module Machine)
open Machine using (St; Ctx; Conf; ⟨_,_,_,_⟩; subscribing; absorbed; rising; plug; alive; nx; cp;
                    pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
                    free; cpAt; cutAt; overAt; closed; CS; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody)
                    renaming (Ev to Evᴹ; Shown to Shownᴹ)
open import adequacy.Rows using (TakeR; Kept; stop; env; rows; rowsL; pendRows; here; RT; Moves; Lanes; module Flat; module BoundedF; module SwitchF; module ExhaustF)
open import adequacy.Up using (≃-refl; any-ʳ++ʳ)
open import denotation.Laws.Worlds using (Ok; Hots)
open import adequacy.Bound using (Empty; Good; G; GLn; LnBody; SrcG; Held; MergeG; mergeG-map; shape)
open import adequacy.Skip using (After; LeadC)
open import adequacy.Owes using (Owes; UpO; Need; SrcO; Owing; map-owing; flat-owing-o; flat-owing-l; owing-≃; ≡→≃; rowsL-ʳ++; goodL-ʳ++⁻; goodL-swap; Swap; good-swap)

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
Lead ⟨ c , s , rising e , p ⟩ = UpO c × LeadC c p × Owes (env c) s × Open s × After p (rows (env c) s) × Ends e (rows (env c) s)
                                × SrcO c (here (env c) s (rising e) p)
Lead ⟨ c , s , subscribing , p ⟩ = UpO c × Owes (env c) s × Subs (env c) s × SrcO c (rows (env c) s)
Lead ⟨ c , s , absorbed , p ⟩    = Owes [] (plug c s)

-- The tree the seeker reads: a subscription still owed owes it nothing.
Seen : ∀ {Γ A} → St Γ A → St Γ A
Seen (pend o q) = doneS
Seen s          = s

Settled : ∀ {R} → Conf R → St _ R
Settled ⟨ c , s , subscribing , p ⟩ = plug c (Seen s)
Settled ⟨ c , s , rising e , p ⟩    = plug c s
Settled ⟨ c , s , absorbed , p ⟩    = plug c s

record Inv {R} (k : Conf R) : Set₁ where
  constructor inv
  field
    good : Good [] (Settled k)
    lead : Lead k
open Inv public

-- One step against the rows, the invariant kept.
Sim : ∀ {R} → Conf R → Shownᴹ R → Conf R → Set₁
Sim k sh k′ = Inv k → Inv k′ × Moves (RT k) sh (RT k′)

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
    srcUn (just _) g′ = inj₂ (inj₂ g′)
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

-- A MERGE OWING A ROW, AS ENTERED: a joiner of good parts owing a row
-- owes one with finitely many before it.  Every part of a good node owes
-- only rows with finitely many of its own before them, and finitely many
-- parts lie before any row, so the earliest part with infinitely many
-- rows before a row offers one with finitely many.
postulate
  owing-row : ∀ {Γ A B} {ρ : DenEnv Γ} {b} f d n q (o : St Γ A) (ls : List (St Γ B)) → G ρ b (flatS (mergeᶠ nothing) f d n q o ls)
            → Owing (Flat.JoinT (λ a → pendRows ρ (f a)) (rows ρ o) d (rowsL ρ ls)) → Owing (rows ρ (flatS (mergeᶠ nothing) f d n q o ls))

-- A JOINER OWING A ROW, AS ENTERED, a bounded merge, a switch or an
-- exhaust: one of its parts owing a row, it owes one with finitely many
-- before it, as a merge does.  A lane a switch's value cuts leaves that
-- value's row owed instead.
postulate
  bounded-owing : ∀ {Γ A B} {ρ : DenEnv Γ} {b} m f d n q (o : St Γ A) (ls : List (St Γ B)) → G ρ b (flatS (mergeᶠ (just m)) f d n q o ls)
                → Owing (rows ρ o) ⊎ Owing (Lanes (rowsL ρ ls)) → Owing (rows ρ (flatS (mergeᶠ (just m)) f d n q o ls))
  switch-owing  : ∀ {Γ A B} {ρ : DenEnv Γ} {b} f d n q (o : St Γ A) (ls : List (St Γ B)) → G ρ b (flatS switchᶠ f d n q o ls)
                → Owing (rows ρ o) ⊎ Owing (Lanes (rowsL ρ ls)) → Owing (rows ρ (flatS switchᶠ f d n q o ls))
  exhaust-owing : ∀ {Γ A B} {ρ : DenEnv Γ} {b} f d n q (o : St Γ A) (ls : List (St Γ B)) → G ρ b (flatS exhaustᶠ f d n q o ls)
                → Owing (rows ρ o) ⊎ Owing (Lanes (rowsL ρ ls)) → Owing (rows ρ (flatS exhaustᶠ f d n q o ls))

-- A SCAN OF A SOURCE OWING, OWES: a source value is a scan row only once
-- a least value stands before it, so the row it is owed must have one.
postulate
  scan-owing : ∀ {A B} (f : B → A → B) z {t : EmissionSet A} → Owing t → Owing (Scan.ScanT f z t)

-- A TAKE OF A SOURCE OWING, OWES, while no value has failed: its least
-- row passes, or is the first failing value, kept or stopped at.
postulate
  take-owing : ∀ {A} i (q : A → Bool) {t : EmissionSet A} → Owing t → Owing (TakeR i q free t)

-- A FAILED TAKE PAST ITS STOP OWES: what it keeps of a source owing.
-- Suspect: a source owing only rows past its failing value keeps none,
-- while the machine's take stays alive owing only its cut, as a hushing
-- cold does; one with THE OWED.
postulate
  kept-owing : ∀ {A} p {t : EmissionSet A} → Owing t → Owing (Kept p t)

take-owes : ∀ {A} i (q : A → Bool) w {t : EmissionSet A} → Owing t → Owing (TakeR i q w t)
take-owes i q free       ow = take-owing i q ow
take-owes i q (cpAt p)   ow = λ em → em stop
take-owes i q (cutAt p)  ow = kept-owing p ow
take-owes i q (overAt p) ow = kept-owing p ow

-- A CONNECT WHOSE SOURCE OWES, OWES: a live connect's source row is a
-- burst pin, an echo while the body runs, or a pin its own connect keeps,
-- and once the body has ended the body's end is a row of its own.
postulate
  conn-owing : ∀ {Γ A X} {ρ : DenEnv Γ} (k : CS) (o : St Γ X) (b : St (X ∷ Γ) A) → G ρ true (connS k o b) → Owing (rows ρ o) → Owing (rows ρ (connS k o b))

-- Under open frames every hole is owed.
upo-liv : ∀ {R Γ A} (c : Ctx R Γ A) → UpO c → liv c ≡ true
upo-liv top              _ = refl
upo-liv (inMap f c)      u = upo-liv c u
upo-liv (inScan f z c)   u = upo-liv c u
upo-liv (inTake i q w c) u = upo-liv c u
upo-liv (inCut true a c) u rewrite upo-liv c u = refl
upo-liv (inLn true c)    u = upo-liv c u
upo-liv (inOuter op f d n q ls c) (_ , u) = upo-liv c u
upo-liv (inLanes op f d n q o pre post c) (_ , _ , _ , _ , u) = upo-liv c u
upo-liv (inCut false a c) ()
upo-liv (inLn false c)    ()
upo-liv (inSrc k b c)  u       = upo-liv c u
upo-liv (inBody k o c) (_ , u) = upo-liv c u

-- A part owing a row under open frames: its frame's node owes one, and
-- each connect it is the source of owes in its body.
need-of : ∀ {R Γ A} (c : Ctx R Γ A) {s : St Γ A} → UpO c → Good [] (plug c s) → Owing (rows (env c) s) → SrcO c (rows (env c) s) → Need c s
need-of top                                     u g ow so = tt
need-of (inMap f c)                             u g ow so = need-of c u g (map-owing f ow) so
need-of (inScan f z c)                          u g ow so = need-of c u g (scan-owing f z ow) so
need-of (inTake i q w c)                        u g ow so = need-of c u g (take-owes i q w ow) so
need-of (inCut true a c)                        u g ow so = need-of c u g ow so
need-of (inLn true c)                           u g ow so = need-of c u g ow so
need-of (inOuter (mergeᶠ nothing) f d n q ls c) {s} (_ , u) g ow so =
  (λ _ → ow) , need-of c u g (owing-row f d n q s ls (node-good c _ g (λ ()) (λ ())) (flat-owing-o _ ow)) so
need-of (inLanes (mergeᶠ nothing) f d n q o pre post c) {s} (_ , _ , _ , _ , u) g ow so =
  (λ _ → ow) , need-of c u g (owing-row f d n q o (pre ʳ++ s ∷ post) (node-good c _ g (λ ()) (λ ()))
                                (owing-≃ (≡→≃ (cong (Flat.JoinT _ (rows (env c) o) d) (sym (rowsL-ʳ++ pre))))
                                         (flat-owing-l _ λ em → ow λ r → em (any-ʳ++ʳ (rowsL (env c) pre) (inj₁ r)))))
                 (subst (λ X → SrcO c (Flat.RowT (λ a → pendRows (env c) (f a)) (rows (env c) o) d X)) (sym (rowsL-ʳ++ pre)) so)
need-of (inOuter (mergeᶠ (just m)) f d n q ls c) {s} (_ , u) g ow so =
  (λ _ → ow) , need-of c u g (bounded-owing m f d n q s ls (node-good c _ g (λ ()) (λ ())) (inj₁ ow)) so
need-of (inLanes (mergeᶠ (just m)) f d n q o pre post c) {s} (_ , _ , _ , _ , u) g ow so =
  (λ _ → ow) , need-of c u g (bounded-owing m f d n q o (pre ʳ++ s ∷ post) (node-good c _ g (λ ()) (λ ()))
                                (inj₂ (owing-≃ (≡→≃ (cong Lanes (sym (rowsL-ʳ++ pre)))) λ em → ow λ r → em (any-ʳ++ʳ (rowsL (env c) pre) (inj₁ r)))))
                 (subst (λ X → SrcO c (BoundedF.RowT m (λ a → pendRows (env c) (f a)) (rows (env c) o) d n q X)) (sym (rowsL-ʳ++ pre)) so)
need-of (inOuter switchᶠ f d n q ls c) {s} (_ , u) g ow so =
  (λ _ → ow) , need-of c u g (switch-owing f d n q s ls (node-good c _ g (λ ()) (λ ())) (inj₁ ow)) so
need-of (inLanes switchᶠ f d n q o pre post c) {s} (_ , _ , _ , _ , u) g ow so =
  (λ _ → ow) , need-of c u g (switch-owing f d n q o (pre ʳ++ s ∷ post) (node-good c _ g (λ ()) (λ ()))
                                (inj₂ (owing-≃ (≡→≃ (cong Lanes (sym (rowsL-ʳ++ pre)))) λ em → ow λ r → em (any-ʳ++ʳ (rowsL (env c) pre) (inj₁ r)))))
                 (subst (λ X → SrcO c (SwitchF.RowT (λ a → pendRows (env c) (f a)) (rows (env c) o) d n X)) (sym (rowsL-ʳ++ pre)) so)
need-of (inOuter exhaustᶠ f d n q ls c) {s} (_ , u) g ow so =
  (λ _ → ow) , need-of c u g (exhaust-owing f d n q s ls (node-good c _ g (λ ()) (λ ())) (inj₁ ow)) so
need-of (inLanes exhaustᶠ f d n q o pre post c) {s} (_ , _ , _ , _ , u) g ow so =
  (λ _ → ow) , need-of c u g (exhaust-owing f d n q o (pre ʳ++ s ∷ post) (node-good c _ g (λ ()) (λ ()))
                                (inj₂ (owing-≃ (≡→≃ (cong Lanes (sym (rowsL-ʳ++ pre)))) λ em → ow λ r → em (any-ʳ++ʳ (rowsL (env c) pre) (inj₁ r)))))
                 (subst (λ X → SrcO c (ExhaustF.RowT (λ a → pendRows (env c) (f a)) (rows (env c) o) d n X)) (sym (rowsL-ʳ++ pre)) so)
need-of (inSrc k b c) {s} u g ow (ob , so) =
  ob , need-of c u g (conn-owing k s b (subst (λ v → G (env c) v (connS k s b)) (upo-liv c u) (node-good c _ g (λ ()) (λ ()))) ow) so
need-of (inBody k o c)                          (_ , u) g ow so = need-of c u g (λ em → ow λ r → em (Connecting.body r)) so

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
    held₀ : Held s → Held s′
open Swap₀

-- The cut that switched the lane off: nothing under it is owed above.
killed : ∀ {Γ A} {ρ : DenEnv Γ} a {s s′ : St Γ A} → Swap₀ ρ s s′ → Swap ρ (cutS false a s) (cutS false a s′)
killed a sw = record
  { same  = ≃-refl
  ; live≡ = refl
  ; node  = λ { true g → node₀ sw g ; false g → node₀ sw g }
  ; lane  = λ _ ()
  ; body  = λ { true _ (refl , g , _) → refl , node₀ sw g , tt ; false _ (refl , g , _) → refl , node₀ sw g , tt }
  ; held  = λ () }

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
  dead-swap c dd (record { node₀ = λ { (gs , gb , _) → src₀ (CS.bodyAt k) gs , shape b gb , tt } ; lane₀ = λ () ; body₀ = λ _ () ; held₀ = λ () }) g
  where
    src₀ : ∀ m → SrcG (env c) false m _ → SrcG (env c) false m _
    src₀ nothing  = node₀ sw
    src₀ (just _) = held₀ sw
dead-swap (inBody k o c)    dd sw g = dead-swap c dd (record { node₀ = λ { (gs , gb , sp) → gs , node₀ sw gb , sp } ; lane₀ = λ () ; body₀ = λ _ () ; held₀ = λ () }) g
