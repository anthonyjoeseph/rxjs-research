{-# OPTIONS --guardedness #-}

-- THE FRAMES ABOVE A HOLE, and what a hole owes there.
module adequacy.Cursor.Frame where

open import Data.Bool using (Bool; T; true; false; not)
open import Data.List using (_∷_; [_]; _++_; reverse)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (_+_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; [_,_]′)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

open import Tree using (Obs)
open import denotation.Events using (Pos; Timeline; ix)
open import denotation.EmissionSet using (EmissionSet; Ev; out; ⟦_⟧; MapT; module Scan; module TakeWhile; module Connecting)
open import operation.PureObservable using (module Machine; Tape; play; ending) renaming (over to tapeOver)

open Machine using (St; Ctx; Conf; ⟨_,_,_,_⟩; Scope; unbound; binds; CS; Owe; closed; free; cpAt; cutAt; overAt; scopeOf;
                    Att; attached; attAt; subscribing; absorbed; rising; mapEv; nx; cp;
                    pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
                    top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody; unsub; cut; killAll; unsubIf)
                    renaming (Ev to Evᴹ; Shown to Shownᴹ)
open import adequacy.Rows using (toEv; full; pendRows; Frozen)
open import denotation.Laws.Worlds using (Ok; Hots; Real; W; W⁼; Plain; InvAt; InvD) renaming (_⊑_ to _⊑ʷ_)
open import adequacy.Cursor using (Adm; Ahead; Asc; AttFin; AttOwed; Begun; Behind; Burst; ConnE; Cur; Ends; Failure; Flags; Folded; Gone; Hole; Husk; HuskL; JInv; JRl; JRo; JoinE; JoinF; Joined; LanesIn; NoFail; NoIsle; OuterDone; OweAt; Owes; Parts; Pts; Rgn; Runs; Sound; Spent; Src; SrcH; Subd; Sync; TailP; Under; Waiting; Whole; Within; _∪ᵖ_; _≈_; _⊑_; aft; bef; bump; polF)


------------------------------------------------------------------------
-- THE FRAMES ABOVE A HOLE: the hole's entry `E`, composed up to the
-- root's, every other part in step.  What the hole itself owes is its
-- `Need`: its entry; where it may still run on (a part no live node
-- reads); or a lane's shape — the joiner's list entry and the switch
-- under it, both on or both off — which the joiner reads off the lane's
-- state.

data Need : Set₁ where
  owes    : Need
  dead    : Pts → Need
  lane    : Bool → Pts → Need
  lanecut : Bool → Pts → Need
  pnd     : Pos → Need

-- On, its entry; off, where it may still run on.
onoff : Bool → Pts → Need
onoff true  _ = owes
onoff false P = dead P

-- A part no live node reads: what it still runs covers its need.
Rest : ∀ {Γ} → Scope Γ → ∀ {A} → St Γ A → Pts → Set₁
Rest sc s P = Σ Pts λ Q → Husk sc s Q × P ⊑ Q

LaneHold : ∀ {Γ} → Scope Γ → Rgn → Cur → Bool → Pts → ∀ {A} → St Γ A → EmissionSet A → Set₁
LaneHold sc Rg C true  P l E = Sync sc Rg C l E
LaneHold sc Rg C false P l E = Rest sc l P

-- The hole's state against its need.
Hold : ∀ {Γ} → Scope Γ → Rgn → Cur → Need → ∀ {A} → St Γ A → EmissionSet A → Set₁
Hold sc Rg C owes          s E = Sync sc Rg C s E
Hold sc Rg C (dead P)      s E = Rest sc s P
Hold sc Rg C (lane b P)    s E = Σ Att λ at → Σ (St _ _) λ l → s ≡ lnS b (cutS b at l) × LaneHold sc Rg C b P l E
Hold sc Rg C (lanecut b P) s E = Σ Att λ at → Σ (St _ _) λ l → s ≡ cutS b at l × LaneHold sc Rg C b P l E
Hold {Γ} sc Rg C (pnd q) {A} s E = Σ (Obs Timeline Γ A) λ o → s ≡ pend o q × pendRows (full sc) o q ≈ E × Within Rg sc q (pendRows (full sc) o q)

data ⊥₁ : Set₁ where

-- A rise in flight at `p` from the hole: delivered there, its row in the
-- hole's entry.
Fly : ∀ {Γ} → Scope Γ → Rgn → Pos → Need → ∀ {A} → St Γ A → EmissionSet A → Evᴹ A → Set₁
Fly sc Rg p owes          s E e = Sync sc Rg (aft p) s E × E p (toEv e)
Fly sc Rg p (dead _)      s E e = ⊥₁
Fly sc Rg p (lane b P)    s E e = Σ Att λ at → Σ (St _ _) λ l → s ≡ lnS b (cutS b at l) × T b × Sync sc Rg (aft p) l E × E p (toEv e)
Fly sc Rg p (lanecut b P) s E e = Σ Att λ at → Σ (St _ _) λ l → s ≡ cutS b at l × T b × Sync sc Rg (aft p) l E × E p (toEv e)
Fly sc Rg p (pnd q)       s E e = ⊥₁

module _ {R : Set} (Rt : EmissionSet R) where

  -- The root's cursor, and the cursor of the world the hole is in: the
  -- root's, or an isle's.
  data Fr (Cr : Cur) : Cur → ∀ {Γ A} → Rgn → Ctx R Γ A → Need → EmissionSet A → Set₁

  -- A connect no live node reads, as what is above it sees it: inside a
  -- part no live node reads, its need there; or torn down under a live
  -- node, its rows owed within what its parts still run.
  data Unread (Cr C : Cur) {Γ X B} (c : Ctx R Γ B) (k : CS Γ X) : Pts → Set₁ where
    un-dead : ∀ {Rg P E} → Fr Cr C Rg c (dead P) E → Unread Cr C c k P
    un-torn : ∀ {Rg E P β} → Fr Cr C Rg c owes E → CS.scope k ≡ scopeOf c → (pt : Parts (scopeOf c) Rg k β) → T (not (CS.srcLive k))
            → Flags C k β → ConnE (CS.connAt k) (Frozen k) β E → TailP C (Connecting.ConnT (CS.connAt k) (Frozen k) β) P
            → Unread Cr C c k P

  data Fr Cr where
    f-top   : ∀ {Rg E} → E ≈ Rt → Fr Cr Cr Rg top owes E
    f-map   : ∀ {Γ A B} {f : A → B} {c : Ctx R Γ B} {C Rg E E′} → Fr Cr C Rg c owes E′ → MapT f E ≈ E′ → Sound Rg E → Fr Cr C Rg (inMap f c) owes E
    f-scan  : ∀ {Γ A B} {f : B → A → B} {z z₀} {c : Ctx R Γ B} {C Rg E E′}
            → Fr Cr C Rg c owes E′ → Folded C f z₀ E z → Scan.ScanT f z₀ E ≈ E′ → Sound Rg E → Fr Cr C Rg (inScan f z c) owes E
    f-cut   : ∀ {Γ A} {a} {c : Ctx R Γ A} {C Rg E} → Fr Cr C Rg c owes E → Fr Cr C Rg (inCut true a c) owes E
    f-take  : ∀ {Γ A} {i} {keep : A → Bool} {c : Ctx R Γ A} {C Rg E E′}
            → Fr Cr C Rg c owes E′ → NoFail C keep E → TakeWhile.TakeT i keep E ≈ E′ → Sound Rg E → Fr Cr C Rg (inTake i keep free c) owes E
    -- a takeWhile failed at `r`: what it still owes within what its
    -- source still runs
    f-took  : ∀ {Γ A} {i} {keep : A → Bool} {o} {c : Ctx R Γ A} {C Rg Rg′ E Es E′ r P}
            → Fr Cr C Rg c owes E′ → Failure keep Es r → Gone C r → (T i → ¬ Owes C (r ++ [ ix 0 ])) → OweAt C o r
            → TailP C (TakeWhile.TakeT i keep Es) P → TakeWhile.TakeT i keep Es ≈ E′ → Sound Rg Es
            → Fr Cr C Rg′ (inTake i keep o c) (dead P) E
    f-outer : ∀ {Γ A B} {op} {f : A → Obs Timeline Γ B} {ω} {d n qu ls} {c : Ctx R Γ B} {C Rg E E′}
            → Fr Cr C Rg c owes E′ → JInv (scopeOf c) f E
            → Joined (scopeOf c) (JRl (scopeOf c) Rg op f E) C (polF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) E) E d n qu ls
            → JoinE (scopeOf c) op f ω E E′ → Sound (JRo (scopeOf c) Rg op f E) E
            → Behind C (JoinF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) E)
            → Fr Cr C (JRo (scopeOf c) Rg op f E) (inOuter op f ω d n qu ls c) owes E
    -- the hole a begun lane, between those before it and after it, in a
    -- joiner some live node reads
    f-lanes : ∀ {Γ A B} {op} {f : A → Obs Timeline Γ B} {ω} {d n qu} {o : St Γ A} {pre post} {c : Ctx R Γ B}
                {C Rg E E′ O vs₁ vs₂ ws n₁ n₂ q a b Ph}
            → Fr Cr C Rg c owes E′ → JInv (scopeOf c) f O
            → Sync (scopeOf c) (JRo (scopeOf c) Rg op f O) C o O
            → Begun (scopeOf c) (JRl (scopeOf c) Rg op f O) C (polF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) O) O vs₁ (reverse pre) n₁
            → O q (out a) → ¬ Owes C q → Runs (polF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) O) q
            → Hole C (polF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) O) q a Ph E b
            → Begun (scopeOf c) (JRl (scopeOf c) Rg op f O) C (polF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) O) O vs₂ post n₂
            → n ≡ n₁ + bump b n₂
            → Waiting C (polF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) O) O ws qu
            → Whole C (polF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) O) O (vs₁ ++ (q , a) ∷ vs₂) ws
            → OuterDone C O d
            → Ahead C (polF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) O) (vs₁ ++ (q , a) ∷ vs₂) ws
            → Asc (vs₁ ++ (q , a) ∷ vs₂)
            → Ends (polF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) O) O
            → LanesIn (Hots (full (scopeOf c))) (JRl (scopeOf c) Rg op f O) (polF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) O) O
            → JoinE (scopeOf c) op f ω O E′ → Sound (JRo (scopeOf c) Rg op f O) O → (T b → Sound (JRl (scopeOf c) Rg op f O q) E)
            → Behind C (JoinF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) O)
            → Fr Cr C (JRl (scopeOf c) Rg op f O q) (inLanes op f ω d n qu o pre post c) (lane b Ph) E
    -- under a lane's list entry, its switch; under that, its program
    f-lane  : ∀ {Γ A} {c : Ctx R Γ A} {C Rg b P E} → Fr Cr C Rg c (lane b P) E → Fr Cr C Rg (inLn b c) (lanecut b P) E
    f-lnct  : ∀ {Γ A} {a} {c : Ctx R Γ A} {C Rg b P E} → Fr Cr C Rg c (lanecut b P) E → Fr Cr C Rg (inCut b a c) (onoff b P) E
    f-src   : ∀ {Γ X B} {k : CS Γ X} {b} {c : Ctx R Γ B} {C Rg E E′ β}
            → Fr Cr C Rg c owes E′ → CS.scope k ≡ scopeOf c → (pt : Parts (scopeOf c) Rg k β) → T (CS.srcLive k) → T (not (CS.closed k))
            → Sync (binds (CS.src k) (CS.connAt k) (scopeOf c)) (Parts.Rb pt) C b β → Behind C β
            → Flags C k β → E ≈ Frozen k → ConnE (CS.connAt k) (Frozen k) β E′ → Behind C (Frozen k) → Subd (scopeOf c) C k
            → AttFin k → (T (not (CS.srcAtt k)) → AttOwed k) → NoIsle b → Fr Cr C (Parts.Rs pt) (inSrc k b c) owes E
    -- a source ended while its connect runs: nothing reads what is left
    f-srcc  : ∀ {Γ X B} {k : CS Γ X} {b} {c : Ctx R Γ B} {C Rg Rg′ E E′ β P}
            → Fr Cr C Rg c owes E′ → CS.scope k ≡ scopeOf c → (pt : Parts (scopeOf c) Rg k β) → T (CS.srcLive k) → T (CS.closed k)
            → Spent C (Frozen k) → TailP C (Frozen k) P → Behind C (Frozen k) → Subd (scopeOf c) C k
            → Sync (binds (CS.src k) (CS.connAt k) (scopeOf c)) (Parts.Rb pt) C b β → Behind C β
            → Flags C k β → ConnE (CS.connAt k) (Frozen k) β E′
            → Fr Cr C Rg′ (inSrc k b c) (dead P) E
    -- a source being subscribed: its program, owed at the connect's
    -- `ix 1`; its body's burst over, so the cursor is past it and the
    -- body holds no isle
    f-srcp  : ∀ {Γ X B} {k : CS Γ X} {b} {c : Ctx R Γ B} {C Rg E E′ β}
            → Fr Cr C Rg c owes E′ → CS.scope k ≡ scopeOf c → (pt : Parts (scopeOf c) Rg k β) → T (CS.srcLive k) → T (not (CS.closed k))
            → T (not (CS.srcAtt k)) → CS.bodyAt k ≡ just (CS.connAt k) → CS.attSrc k ≡ nothing → Adm (binds (CS.src k) (CS.connAt k) (scopeOf c))
            → Sync (binds (CS.src k) (CS.connAt k) (scopeOf c)) (Parts.Rb pt) C b β → Behind C β
            → Flags C k β → E ≈ Frozen k → ConnE (CS.connAt k) (Frozen k) β E′
            → Owes C (CS.connAt k ++ [ ix 1 ]) → Subd (scopeOf c) C k → NoIsle b
            → Fr Cr C (Parts.Rs pt) (inSrc k b c) (pnd (CS.connAt k ++ [ ix 1 ])) E
    -- a body while its source runs
    f-body  : ∀ {Γ X B} {k : CS Γ X} {o} {c : Ctx R Γ B} {C Rg E E′}
            → Fr Cr C Rg c owes E′ → CS.scope k ≡ scopeOf c → (pt : Parts (scopeOf c) Rg k E) → T (CS.srcLive k)
            → Src (scopeOf c) (Parts.Rs pt) C k o → Behind C E → Flags C k E → ConnE (CS.connAt k) (Frozen k) E E′
            → Fr Cr C (Parts.Rb pt) (inBody k o c) owes E
    -- inside a part no live node reads
    d-map   : ∀ {Γ A B} {f : A → B} {c : Ctx R Γ B} {C Rg Rg′ P E E′} → Fr Cr C Rg c (dead P) E′ → Fr Cr C Rg′ (inMap f c) (dead P) E
    d-scan  : ∀ {Γ A B} {f : B → A → B} {z} {c : Ctx R Γ B} {C Rg Rg′ P E E′} → Fr Cr C Rg c (dead P) E′ → Fr Cr C Rg′ (inScan f z c) (dead P) E
    d-cut   : ∀ {Γ A} {l a} {c : Ctx R Γ A} {C Rg Rg′ P E E′} → Fr Cr C Rg c (dead P) E′ → Fr Cr C Rg′ (inCut l a c) (dead P) E
    d-ln    : ∀ {Γ A} {b} {c : Ctx R Γ A} {C Rg Rg′ P E E′} → Fr Cr C Rg c (dead P) E′ → Fr Cr C Rg′ (inLn b c) (dead P) E
    d-take  : ∀ {Γ A} {i} {keep : A → Bool} {w} {c : Ctx R Γ A} {C Rg Rg′ P E E′} → Fr Cr C Rg c (dead P) E′ → Fr Cr C Rg′ (inTake i keep w c) (dead P) E
    d-outer : ∀ {Γ A B} {op} {f : A → Obs Timeline Γ B} {ω} {d n qu ls} {c : Ctx R Γ B} {C Rg Rg′ P N Q E E′}
            → Fr Cr C Rg c (dead P) E′ → HuskL (scopeOf c) ls Q → P ⊑ (N ∪ᵖ Q) → Fr Cr C Rg′ (inOuter op f ω d n qu ls c) (dead N) E
    d-lanes : ∀ {Γ A B} {op} {f : A → Obs Timeline Γ B} {ω} {d n qu} {o : St Γ A} {pre post} {c : Ctx R Γ B} {C Rg Rg′ P N Qo Qa Qb E E′}
            → Fr Cr C Rg c (dead P) E′ → Husk (scopeOf c) o Qo → HuskL (scopeOf c) pre Qa → HuskL (scopeOf c) post Qb
            → P ⊑ (Qo ∪ᵖ (Qa ∪ᵖ (N ∪ᵖ Qb))) → Fr Cr C Rg′ (inLanes op f ω d n qu o pre post c) (dead N) E
    d-src   : ∀ {Γ X B} {k : CS Γ X} {b : St (X ∷ Γ) B} {c : Ctx R Γ B} {C Rg′ P N Qb E}
            → Unread Cr C c k P → Husk (binds (CS.src k) (CS.connAt k) (CS.scope k)) b Qb
            → P ⊑ (Under N ∪ᵖ Qb) → NoIsle b → T (CS.srcAtt k) ⊎ T (CS.closed k) → Fr Cr C Rg′ (inSrc k b c) (dead N) E
    d-body  : ∀ {Γ X B} {k : CS Γ X} {o} {c : Ctx R Γ B} {C Rg′ P N Ps E}
            → Unread Cr C c k P → SrcH (scopeOf c) k o Ps
            → P ⊑ (Ps ∪ᵖ N) → Fr Cr C Rg′ (inBody k o c) (dead N) E
    -- an isle: its source in step at its own cursor
    f-isle  : ∀ {Γ X B} {k : CS Γ X} {b : St (X ∷ Γ) B} {c : Ctx R Γ B} {C Ri Ci P Qb}
            → Unread Cr C c k P → Husk (binds (CS.src k) (CS.connAt k) (CS.scope k)) b Qb
            → P ⊑ (Burst Ci k ∪ᵖ Qb) → T (not (CS.srcAtt k)) → T (not (CS.closed k))
            → Behind Ci (Frozen k) → Subd (scopeOf c) Ci k → Sound Ri (Frozen k) → AttOwed k
            → NoIsle b → Fr Cr Ci Ri (inSrc k b c) owes (Frozen k)
    -- an isle whose source has ended
    f-islec : ∀ {Γ X B} {k : CS Γ X} {b : St (X ∷ Γ) B} {c : Ctx R Γ B} {C Ci Rg′ P N Qb E}
            → Unread Cr C c k P → Husk (binds (CS.src k) (CS.connAt k) (CS.scope k)) b Qb
            → P ⊑ (Burst Ci k ∪ᵖ Qb) → T (not (CS.srcAtt k)) → T (CS.closed k)
            → Spent Ci (Frozen k) → TailP Ci (Frozen k) N → Behind Ci (Frozen k) → Subd (scopeOf c) Ci k
            → Fr Cr C Rg′ (inSrc k b c) (dead N) E
    -- an isle's source not yet subscribed: its cursor at where it will be
    f-islep : ∀ {Γ X B} {k : CS Γ X} {b : St (X ∷ Γ) B} {c : Ctx R Γ B} {C Ri P Qb}
            → Unread Cr C c k P → Husk (binds (CS.src k) (CS.connAt k) (CS.scope k)) b Qb
            → P ⊑ (Burst (bef (CS.connAt k ++ [ ix 1 ])) k ∪ᵖ Qb) → T (not (CS.srcAtt k)) → T (not (CS.closed k)) → CS.bodyAt k ≡ just (CS.connAt k) → CS.attSrc k ≡ nothing
            → CS.scope k ≡ scopeOf c → Adm (binds (CS.src k) (CS.connAt k) (scopeOf c)) → Sound Ri (Frozen k) → NoIsle b
            → Fr Cr (bef (CS.connAt k ++ [ ix 1 ])) Ri (inSrc k b c) (pnd (CS.connAt k ++ [ ix 1 ])) (Frozen k)
