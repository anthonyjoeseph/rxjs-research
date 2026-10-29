{-# OPTIONS --guardedness #-}

-- THE INVARIANT OF THE DIRECT LINK: a good tree, and by mode what the
-- focus is owed.  A rising event leads every other part of each merge it
-- climbs, and its own node owes only rows past it; a mark run or a
-- subscription in flight asks only that every live part still owes.
module adequacy.Inv where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Bool.Properties using (∧-zeroʳ; ∧-identityʳ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (_∷_; _ʳ++_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym)

open import Tree using (mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.EmissionSet using (EmissionSet)
open import operation.PureObservable using (module Machine)
open Machine using (St; Ctx; Conf; ⟨_,_,_,_⟩; subscribing; absorbed; rising; plug; alive; nx; cp;
                    pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
                    closed; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody)
                    renaming (Ev to Evᴹ; Shown to Shownᴹ)
open import adequacy.Rows using (rows; RT; Moves)
open import adequacy.Up using (≃-refl)
open import adequacy.Bound using (Empty; Good; G; GLn; LnBody)
open import adequacy.Skip using (After; LeadC)
open import adequacy.Owes using (Owes; UpO; goodL-ʳ++⁻; goodL-swap; Swap; good-swap)

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
GoodF : ∀ {R Γ A} → Ctx R Γ A → St Γ A → Set
GoodF (inLanes op f d n q o pre post c) s = GLn (liv c) s
GoodF top                s = G true s
GoodF (inMap f c)        s = G (liv c) s
GoodF (inScan f z c)     s = G (liv c) s
GoodF (inCut l a c)      s = G (liv c ∧ l) s
GoodF (inLn b c)         s = G (liv c) s
GoodF (inTake i q w c)   s = G (liv c) s
GoodF (inOuter op f d n q ls c) s = G (liv c) s
GoodF (inSrc k b c)      s = G (liv c) s
GoodF (inBody k o c)     s = G (liv c) s

-- A hole's rows, good either way.
unF : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) → GoodF c s → G (liv c) s ⊎ GLn (liv c) s
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

lnbody-good : ∀ {Γ A} v b (s : St Γ A) → LnBody v b s → G v s
lnbody-good v b (cutS l a s) (refl , g , _) = g
lnbody-good v b (pend _)              ()
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
... | inj₂ gl = gc , lnbody-good (liv c) b s gl
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
node-good : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) → Good (plug c s) → (GLn (liv c) s → ⊥) → G (liv c) s
node-good c s g nl with unF c s (proj₂ (good-split c s g))
... | inj₁ gs = gs
... | inj₂ gl = ⊥-elim (nl gl)

-- Under open frames every hole is owed.
upo-liv : ∀ {R Γ A} (c : Ctx R Γ A) → UpO c → liv c ≡ true
upo-liv top              _ = refl
upo-liv (inMap f c)      u = upo-liv c u
upo-liv (inCut true a c) u rewrite upo-liv c u = refl
upo-liv (inLn true c)    u = upo-liv c u
upo-liv (inOuter (mergeᶠ nothing) f d n q ls c) (_ , u) = upo-liv c u
upo-liv (inLanes (mergeᶠ nothing) f d n q o pre post c) (_ , _ , _ , _ , u) = upo-liv c u
upo-liv (inScan f z c)    ()
upo-liv (inCut false a c) ()
upo-liv (inLn false c)    ()
upo-liv (inTake i q w c)  ()
upo-liv (inOuter (mergeᶠ (just _)) f d n q ls c) ()
upo-liv (inOuter switchᶠ f d n q ls c)  ()
upo-liv (inOuter exhaustᶠ f d n q ls c) ()
upo-liv (inLanes (mergeᶠ (just _)) f d n q o pre post c) ()
upo-liv (inLanes switchᶠ f d n q o pre post c)  ()
upo-liv (inLanes exhaustᶠ f d n q o pre post c) ()
upo-liv (inSrc k b c)  ()
upo-liv (inBody k o c) ()

------------------------------------------------------------------------
-- A hole under a cut switched off

-- A closed hole is under a cut switched off.
closed-dead : ∀ {R Γ A} (c : Ctx R Γ A) → GoodC c → closed c ≡ true → liv c ≡ false
closed-dead top              _  ()
closed-dead (inMap f c)      gc cl = closed-dead c gc cl
closed-dead (inCut false a c) _ _  = ∧-zeroʳ (liv c)
closed-dead (inCut true a c) gc cl rewrite closed-dead c gc cl = refl
closed-dead (inLn b c)       gc cl = closed-dead c gc cl
closed-dead (inOuter (mergeᶠ nothing) f d n q ls c) gc cl = closed-dead c gc cl
closed-dead (inLanes (mergeᶠ nothing) f d n q o pre post c) gc cl = closed-dead c gc cl

-- Swapped where nothing is owed: only the shape asked.
record Swap₀ {Γ A} (s s′ : St Γ A) : Set where
  field
    node₀ : G false s → G false s′
    lane₀ : GLn false s → GLn false s′
    body₀ : ∀ b → LnBody false b s → LnBody false b s′
open Swap₀

-- The cut that switched the lane off: nothing under it is owed above.
killed : ∀ {Γ A} a {s s′ : St Γ A} → Swap₀ s s′ → Swap (cutS false a s) (cutS false a s′)
killed a sw = record
  { same  = ≃-refl
  ; live≡ = refl
  ; node  = λ { true g → node₀ sw g ; false g → node₀ sw g }
  ; lane  = λ _ ()
  ; body  = λ { true _ (refl , g , _) → refl , node₀ sw g , tt ; false _ (refl , g , _) → refl , node₀ sw g , tt } }

nothing₀ : ∀ {Γ A} {s s′ : St Γ A} → (G false s → ⊥) → (GLn false s → ⊥) → (∀ b → LnBody false b s → ⊥) → Swap₀ s s′
nothing₀ ng nl nb = record { node₀ = λ g → ⊥-elim (ng g) ; lane₀ = λ g → ⊥-elim (nl g) ; body₀ = λ b g → ⊥-elim (nb b g) }

dead-swap : ∀ {R Γ A} (c : Ctx R Γ A) {s s′ : St Γ A} → liv c ≡ false → Swap₀ s s′ → Good (plug c s) → Good (plug c s′)
dead-swap top               () sw g
dead-swap (inMap f c)       dd sw g = dead-swap c dd (record { node₀ = node₀ sw ; lane₀ = λ () ; body₀ = λ _ () }) g
dead-swap (inScan f z c)    dd sw g = dead-swap c dd (nothing₀ (λ ()) (λ ()) (λ _ ())) g
dead-swap (inCut false a c) dd sw g = good-swap c (killed a sw) g
dead-swap (inCut true a c)  dd sw g =
  dead-swap c (trans (sym (∧-identityʳ (liv c))) dd) (record { node₀ = node₀ sw ; lane₀ = λ () ; body₀ = λ { b (eq , g′ , _) → eq , node₀ sw g′ , tt } }) g
dead-swap (inLn b c)        dd sw g = dead-swap c dd (record { node₀ = λ () ; lane₀ = body₀ sw b ; body₀ = λ _ () }) g
dead-swap (inTake i q w c)  dd sw g = dead-swap c dd (nothing₀ (λ ()) (λ ()) (λ _ ())) g
dead-swap (inOuter (mergeᶠ nothing) f d n q ls c) dd sw g =
  dead-swap c dd (record { node₀ = λ { (go , gl , qe , fa , _) → node₀ sw go , gl , qe , fa , tt } ; lane₀ = λ () ; body₀ = λ _ () }) g
dead-swap (inOuter (mergeᶠ (just _)) f d n q ls c) dd sw g = dead-swap c dd (nothing₀ (λ ()) (λ ()) (λ _ ())) g
dead-swap (inOuter switchᶠ f d n q ls c)  dd sw g = dead-swap c dd (nothing₀ (λ ()) (λ ()) (λ _ ())) g
dead-swap (inOuter exhaustᶠ f d n q ls c) dd sw g = dead-swap c dd (nothing₀ (λ ()) (λ ()) (λ _ ())) g
dead-swap (inLanes (mergeᶠ nothing) f d n q o pre post c) dd sw g =
  dead-swap c dd (record { node₀ = λ { (go , gl , qe , fa , _) → go , goodL-swap pre (lane₀ sw) gl , qe , fa , tt } ; lane₀ = λ () ; body₀ = λ _ () }) g
dead-swap (inLanes (mergeᶠ (just _)) f d n q o pre post c) dd sw g = dead-swap c dd (nothing₀ (λ ()) (λ ()) (λ _ ())) g
dead-swap (inLanes switchᶠ f d n q o pre post c)  dd sw g = dead-swap c dd (nothing₀ (λ ()) (λ ()) (λ _ ())) g
dead-swap (inLanes exhaustᶠ f d n q o pre post c) dd sw g = dead-swap c dd (nothing₀ (λ ()) (λ ()) (λ _ ())) g
dead-swap (inSrc k b c)     dd sw g = dead-swap c dd (nothing₀ (λ ()) (λ ()) (λ _ ())) g
dead-swap (inBody k o c)    dd sw g = dead-swap c dd (nothing₀ (λ ()) (λ ()) (λ _ ())) g
