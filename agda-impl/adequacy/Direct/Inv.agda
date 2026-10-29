{-# OPTIONS --guardedness #-}

-- THE INVARIANT OF THE DIRECT LINK: a good tree, and by mode what the
-- focus is owed.  A rising event leads every other part of each merge it
-- climbs, and its own node owes only rows past it; a mark run or a
-- subscription in flight asks only that every live part still owes.
module adequacy.Direct.Inv where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _ʳ++_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Tree using (mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.EmissionSet using (EmissionSet)
open import operation.PureObservable using (module Machine)
open Machine using (St; Ctx; Conf; ⟨_,_,_,_⟩; subscribing; absorbed; rising; plug; alive; nx; cp;
                    pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
                    top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody)
                    renaming (Ev to Evᴹ; Shown to Shownᴹ)
open import adequacy.Direct using (rows; RT; Moves)
open import adequacy.Direct.Bound using (Empty; Good; GoodL; GoodLn; LnBody)
open import adequacy.Direct.Skip using (After; LeadC)
open import adequacy.Direct.Owes using (Owes; UpO; goodL-ʳ++⁻)

-- A node an event can rise out of: not cut, not out of its list.
Open : ∀ {Γ A} → St Γ A → Set
Open (lnS false s)   = ⊥
Open (cutS false a s) = ⊥
Open _               = ⊤

-- An end leaves nothing owed.
Ends : ∀ {A} → Evᴹ A → EmissionSet A → Set
Ends (nx _) t = ⊤
Ends cp     t = Empty t

Lead : ∀ {R} → Conf R → Set
Lead ⟨ c , s , rising e , p ⟩ = UpO c × LeadC c p × Owes s × Open s × After p (rows s) × Ends e (rows s)
Lead ⟨ c , s , subscribing , p ⟩ = UpO c × Owes s
Lead ⟨ c , s , absorbed , p ⟩    = Owes (plug c s)

record Inv {R} (k : Conf R) : Set where
  constructor inv
  field
    good : Good (plug (Conf.ctx k) (Conf.foc k))
    lead : Lead k
open Inv public

-- One step against the rows, the invariant kept.
Sim : ∀ {R} → Conf R → Shownᴹ R → Conf R → Set₁
Sim k sh k′ = Inv k → Inv k′ × Moves (RT k) sh (RT k′)

open-alive : ∀ {Γ A} (s : St Γ A) → Open s → alive s ≡ false → ⊥
open-alive (lnS false _)       () _
open-alive (lnS true _)        _ ()
open-alive (pend _)            _ ()
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

-- The frames the fragment builds.
GoodC : ∀ {R Γ A} → Ctx R Γ A → Set
GoodC top                                          = ⊤
GoodC (inMap f c)                                  = GoodC c
GoodC (inCut l a c)                                = GoodC c
GoodC (inLn b c)                                   = GoodC c
GoodC (inOuter (mergeᶠ nothing) f d n q ls c)      = GoodC c
GoodC (inLanes (mergeᶠ nothing) f d n q o pre post c) = GoodC c
GoodC _                                            = ⊥

-- What a frame's hole must be: under a merge's lanes, a lane.
GoodF : ∀ {R Γ A} → Ctx R Γ A → St Γ A → Set
GoodF (inLanes op f d n q o pre post c) s = GoodLn s
GoodF top                s = Good s
GoodF (inMap f c)        s = Good s
GoodF (inScan f z c)     s = Good s
GoodF (inCut l a c)      s = Good s
GoodF (inLn b c)         s = Good s
GoodF (inTake i q w c)   s = Good s
GoodF (inOuter op f d n q ls c) s = Good s
GoodF (inSrc k b c)      s = Good s
GoodF (inBody k o c)     s = Good s

-- A hole's rows, good either way.
unF : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) → GoodF c s → Good s ⊎ GoodLn s
unF (inLanes op f d n q o pre post c) s g = inj₂ g
unF top                s g = inj₁ g
unF (inMap f c)        s g = inj₁ g
unF (inScan f z c)     s g = inj₁ g
unF (inCut l a c)      s g = inj₁ g
unF (inLn b c)         s g = inj₁ g
unF (inTake i q w c)   s g = inj₁ g
unF (inOuter op f d n q ls c) s g = inj₁ g
unF (inSrc k b c)      s g = inj₁ g
unF (inBody k o c)     s g = inj₁ g

lnbody-good : ∀ {Γ A} b (s : St Γ A) → LnBody b s → Good s
lnbody-good b (cutS l a s) (_ , g , _) = g
lnbody-good b (pend _)              ()
lnbody-good b (coldS _ _)           ()
lnbody-good b (ofS _ _ _)           ()
lnbody-good b doneS                 ()
lnbody-good b (mapS _ _)            ()
lnbody-good b (scanS _ _ _)         ()
lnbody-good b (lnS _ _)             ()
lnbody-good b (takeS _ _ _ _)       ()
lnbody-good b (flatS _ _ _ _ _ _ _) ()
lnbody-good b (connS _ _ _)         ()
lnbody-good b (joinS _ _ _ _)       ()

good-split : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) → Good (plug c s) → GoodC c × GoodF c s
good-split top s g = tt , g
good-split (inMap f c) s g with good-split c (mapS f s) g
... | gc , gf with unF c _ gf
... | inj₁ gm = gc , gm
... | inj₂ ()
good-split (inScan f z c) s g with good-split c (scanS f z s) g
... | _ , gf with unF c _ gf
... | inj₁ ()
... | inj₂ ()
good-split (inCut l a c) s g with good-split c (cutS l a s) g
... | gc , gf with unF c _ gf
... | inj₁ gm = gc , gm
... | inj₂ ()
good-split (inLn b c) s g with good-split c (lnS b s) g
... | gc , gf with unF c _ gf
... | inj₁ ()
... | inj₂ gl = gc , lnbody-good b s gl
good-split (inTake i q w c) s g with good-split c (takeS i q w s) g
... | _ , gf with unF c _ gf
... | inj₁ ()
... | inj₂ ()
good-split (inOuter (mergeᶠ nothing) f d n q ls c) s g with good-split c (flatS (mergeᶠ nothing) f d n q s ls) g
... | gc , gf with unF c _ gf
... | inj₁ gm = gc , proj₁ gm
... | inj₂ ()
good-split (inOuter (mergeᶠ (just m)) f d n q ls c) s g with good-split c (flatS (mergeᶠ (just m)) f d n q s ls) g
... | _ , gf with unF c _ gf
... | inj₁ ()
... | inj₂ ()
good-split (inOuter switchᶠ f d n q ls c) s g with good-split c (flatS switchᶠ f d n q s ls) g
... | _ , gf with unF c _ gf
... | inj₁ ()
... | inj₂ ()
good-split (inOuter exhaustᶠ f d n q ls c) s g with good-split c (flatS exhaustᶠ f d n q s ls) g
... | _ , gf with unF c _ gf
... | inj₁ ()
... | inj₂ ()
good-split (inLanes (mergeᶠ nothing) f d n q o pre post c) s g with good-split c (flatS (mergeᶠ nothing) f d n q o (pre ʳ++ s ∷ post)) g
... | gc , gf with unF c _ gf
... | inj₁ (_ , gl , _) = gc , proj₁ (proj₂ (goodL-ʳ++⁻ pre gl))
... | inj₂ ()
good-split (inLanes (mergeᶠ (just m)) f d n q o pre post c) s g with good-split c (flatS (mergeᶠ (just m)) f d n q o (pre ʳ++ s ∷ post)) g
... | _ , gf with unF c _ gf
... | inj₁ ()
... | inj₂ ()
good-split (inLanes switchᶠ f d n q o pre post c) s g with good-split c (flatS switchᶠ f d n q o (pre ʳ++ s ∷ post)) g
... | _ , gf with unF c _ gf
... | inj₁ ()
... | inj₂ ()
good-split (inLanes exhaustᶠ f d n q o pre post c) s g with good-split c (flatS exhaustᶠ f d n q o (pre ʳ++ s ∷ post)) g
... | _ , gf with unF c _ gf
... | inj₁ ()
... | inj₂ ()
good-split (inSrc k b c) s g with good-split c (connS k s b) g
... | _ , gf with unF c _ gf
... | inj₁ ()
... | inj₂ ()
good-split (inBody k o c) s g with good-split c (connS k o s) g
... | _ , gf with unF c _ gf
... | inj₁ ()
... | inj₂ ()

-- The good node a frame sits on.
node-good : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) → Good (plug c s) → (GoodLn s → ⊥) → Good s
node-good c s g nl with unF c s (proj₂ (good-split c s g))
... | inj₁ gs = gs
... | inj₂ gl = ⊥-elim (nl gl)
