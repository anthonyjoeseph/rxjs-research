{-# OPTIONS --guardedness #-}

-- THE FROZEN ENTRY PAST A CURSOR.  Every node of a running tree is tied to
-- the meaning of the program it was subscribed as, entered where it was
-- subscribed, its binders read whole (`full`): its FROZEN ENTRY.  The run
-- carries one global cursor, the last position delivered; a node owes
-- exactly its frozen entry's visible rows past that cursor.  So the root
-- owes its own entry past the cursor, and a step changes what the root
-- owes only by moving the cursor: no residual meaning of a node part way
-- through is ever built.
--
-- What a node's state still tracks is only the bookkeeping the entry
-- cannot see: an of's index, a scan's fold, a joiner's begun lanes and
-- queue, a takeWhile's owe, a joiner's inbox.  `Sync` ties each to its
-- entry and the cursor.  Entries are tied by `_≈_`: visible rows alike,
-- and every row, hidden or not, matched but for finitely many.
--
-- A rise in flight splits the cursor: the focus's subtree has delivered
-- the row (`aft p`), every other node has not seen it (`bef p`).  The
-- frames the rise climbs read their hole at `bef p`, and the hole's entry
-- holds the row in flight there.
--
-- A subtree no live node reads — under a failed takeWhile, a torn
-- source, an ended or killed lane — is tied to no entry, but may still
-- run: a connect inside it whose source is still in its subscribe call
-- (an ISLE) goes on bursting.  What such a subtree is owed is covered by
-- its `Husk`, the bursts of its isles; every other row past the cursor is
-- one of finitely many.  An isle is in step at its own cursor, and the
-- isles form one chain, the call stack, so a program whose synchronous
-- burst never ends is modelled as one that never returns.
--
-- A joiner never reads its source's state: its source's frozen entry,
-- past the cursor, is what is still to feed it.
module adequacy.Cursor where

open import Data.Bool using (Bool; T; true; false; not)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; [_]; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Data.List.Relation.Unary.All using (All; lookup)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; suc; _+_; _≤_; z≤n)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-map⁺)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Position using (Pos; ix; last; tick; tickᴿ; inside; _⊕_; Path)
open import denotation.Events using (Timeline; ofᴱ)
open import denotation.Read using (Visible)
open import denotation.EmissionSet using (EmissionSet; Ev; out; end; pin; _≺_; _≼_; Few; Reach; Truncate; enter; ⟦_⟧; Den; hot; coldAt;
  Rejoin; InE; MapT; LaneOf; module Scan; module TakeWhile; module Connecting; module Merge;
  module Bounded; module Switch; module Exhaust; module Values)
open import operation.PureObservable using (module Machine; Tape; play; ending) renaming (over to tapeOver)

open Machine using (St; Ctx; Conf; ⟨_,_,_,_⟩; Scope; unbound; binds; CS; Owe; closed; free; cpAt; cutAt; overAt; scopeOf;
                    Att; attached; attAt; subscribing; absorbed; rising; mapEv; nx; cp;
                    pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
                    top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody; unsub; cut; killAll; unsubIf; off; offL; offIf)
                    renaming (Ev to Evᴹ; Shown to Shownᴹ)
open import denotation.Laws.Modulus using (≺-ext; ≺-trans)
open import adequacy.Rows using (_≃_; ≃-refl; ≃-trans; Vis; toEv; Inbox; full; pendRows; Frozen; tapeE)
open import denotation.Laws.Worlds using (Ok; Hots; Real; RealR; W; W⁼; Plain; InvAt; InvD) renaming (_⊑_ to _⊑ʷ_)
open _≃_

------------------------------------------------------------------------
-- The cursor

-- Nothing delivered yet; a row in flight at `p`, not yet seen; the row at
-- `p` delivered.
data Cur : Set where
  origin : Cur
  bef aft : Pos → Cur

Owes : Cur → Pos → Set
Owes origin  q = ⊤
Owes (bef p) q = p ≼ q
Owes (aft p) q = p ≺ q

-- The visible rows of `E` the cursor has not passed.
Due : ∀ {A} → Cur → EmissionSet A → EmissionSet A
Due C E q e = E q e × Visible e × Owes C q

-- Owing nothing more.
Spent : ∀ {A} → Cur → EmissionSet A → Set
Spent C E = ∀ {q e} → Due C E q e → ⊥

-- The rows of `E`, of any kind, the cursor has passed: finitely many.
-- What a connect's body and a joiner read before the row in flight.
Behind : ∀ {A} → Cur → EmissionSet A → Set
Behind C E = Σ (List Pos) λ ks → ∀ {y e} → E y e → ¬ Owes C y → y ∈ ks

-- Every row of `E′` a row of `E` at its position, but for finitely many.
Beneath : ∀ {A} → EmissionSet A → EmissionSet A → Set
Beneath E E′ = Σ (List Pos) λ ks → ∀ {y e} → E′ y e → E y e ⊎ y ∈ ks

-- Alike in every row a reader meets; every row of `E` a row of `E′`, and
-- every row of `E′` one of `E` but for finitely many: a defer's guard is a
-- skip no reader meets, left above when the defer passes it.
record _≈_ {A} (E E′ : EmissionSet A) : Set where
  field
    alike : Vis E ≃ Vis E′
    cov   : Beneath E E′
    voc   : ∀ {y e} → E y e → E′ y e
open _≈_ public

beneath-trans : ∀ {A} {E E′ E″ : EmissionSet A} → Beneath E E′ → Beneath E′ E″ → Beneath E E″
beneath-trans (ks , f) (ls , g) = ls ++ ks , λ r → [ (λ r′ → [ inj₁ , (λ i → inj₂ (∈-++⁺ʳ ls i)) ]′ (f r′)) , (λ i → inj₂ (∈-++⁺ˡ i)) ]′ (g r)

≈-refl : ∀ {A} {E : EmissionSet A} → E ≈ E
≈-refl = record { alike = ≃-refl ; cov = [] , inj₁ ; voc = λ r → r }

≈-trans : ∀ {A} {E E′ E″ : EmissionSet A} → E ≈ E′ → E′ ≈ E″ → E ≈ E″
≈-trans m n = record { alike = ≃-trans (alike m) (alike n) ; cov = beneath-trans (cov m) (cov n) ; voc = λ r → voc n (voc m r) }

-- Finitely many rows of `E` the cursor has not passed.
Fin : ∀ {A} → Cur → EmissionSet A → Set
Fin C E = Σ (List Pos) λ ks → ∀ {y e} → E y e → Owes C y → y ∈ ks

-- Every row of `E` the cursor has not passed a row of `T` at its
-- position, but for finitely many.
Tail : ∀ {A} → Cur → EmissionSet A → EmissionSet A → Set
Tail C E T = Σ (List Pos) λ ks → ∀ {y e} → E y e → Owes C y → T y e ⊎ y ∈ ks

-- Owing less, still finitely many.
fin-dn : ∀ {A} {C C′} {E : EmissionSet A} → (∀ {y} → Owes C′ y → Owes C y) → Fin C E → Fin C′ E
fin-dn d (ks , f) = ks , λ r o → f r (d o)

tail-dn : ∀ {A} {C C′} {E T : EmissionSet A} → (∀ {y} → Owes C′ y → Owes C y) → Tail C E T → Tail C′ E T
tail-dn d (ks , f) = ks , λ r o → f r (d o)

-- Row for row, still finitely many.
fin-≈ : ∀ {A} {C} {E E′ : EmissionSet A} → E ≈ E′ → Fin C E → Fin C E′
fin-≈ m (ks , f) with cov m
... | ls , g = ls ++ ks , λ r o → [ (λ r′ → ∈-++⁺ʳ ls (f r′ o)) , ∈-++⁺ˡ ]′ (g r)

tail-≈ : ∀ {A} {C} {E E′ T : EmissionSet A} → E ≈ E′ → Tail C E T → Tail C E′ T
tail-≈ m (ks , f) with cov m
... | ls , g = ls ++ ks , λ r o → [ (λ r′ → [ inj₁ , (λ i → inj₂ (∈-++⁺ʳ ls i)) ]′ (f r′ o)) , (λ i → inj₂ (∈-++⁺ˡ i)) ]′ (g r)

------------------------------------------------------------------------
-- WHERE A PART NO LIVE NODE READS STILL RUNS ON.  Unsubscribing cannot
-- reach a source still in its subscribe call, so a connect whose source
-- has not attached keeps its burst running, read by nobody: an ISLE.  Its
-- pins are what a dead part may owe without end; everything else it owes
-- is finitely many.

-- A set of positions.
Pts : Set₁
Pts = Pos → Set

∅ᵖ : Pts
∅ᵖ _ = ⊥

_∪ᵖ_ : Pts → Pts → Pts
(P ∪ᵖ Q) y = P y ⊎ Q y

-- Each position's first effect.
Under : Pts → Pts
Under P y = Σ Pos λ k → P k × y ≡ k ⊕ [ ix 0 ]

-- A connect's source row that its burst holds, read at the cursor its
-- source runs at: inside its subscription, or a pin of a connect that
-- cursor has passed.  A source still in its subscribe call never runs
-- past it, so a pin past it is one a cut keeps (`Connecting.kept`), of a
-- burst begun before the cursor.
Held : ∀ {Γ X} → Cur → CS Γ X → Pos → Ev X → Set
Held C k k′ e = T (inside (CS.connAt k ⊕ [ ix 1 ]) k′) ⊎ Σ Pos λ p′ → e ≡ pin p′ × ¬ Owes C p′

-- Its burst, at each row's first effect.
Burst : ∀ {Γ X} → Cur → CS Γ X → Pts
Burst C k = Under λ k′ → Σ _ λ e → Frozen k k′ e × Held C k k′ e

-- A cursor moved on holds more.
held-dn : ∀ {Γ X} {C C′} {k : CS Γ X} {k′ e} → (∀ {y} → Owes C′ y → Owes C y) → Held C k k′ e → Held C′ k k′ e
held-dn d (inj₁ i)              = inj₁ i
held-dn d (inj₂ (p′ , e , np))  = inj₂ (p′ , e , λ o → np (d o))

-- An attached source's subscribe call has returned: finitely many of its
-- rows lie inside it.
AttFin : ∀ {Γ X} → CS Γ X → Set
AttFin k = T (CS.srcAtt k) → Σ (List Pos) λ ks → ∀ {y e} → Frozen k y e → T (inside (CS.connAt k ⊕ [ ix 1 ]) y) → y ∈ ks

-- An unattached source's subscribe call still to return: its attach
-- owed just after its connect's `ix 1`, or its body not yet run.
AttOwed : ∀ {Γ X} → CS Γ X → Set
AttOwed k = CS.attSrc k ≡ just (CS.connAt k ⊕ [ ix 1 ]) ⊎ (CS.bodyAt k ≡ just (CS.connAt k) × CS.attSrc k ≡ nothing)

-- Within `Q` but for finitely many.
_⊑_ : Pts → Pts → Set
P ⊑ Q = Σ (List Pos) λ ks → ∀ {y} → P y → Q y ⊎ y ∈ ks

-- An isle's cursor moved on: its burst holds more.
burst-dn : ∀ {Γ X} {C C′} {k : CS Γ X} {P Q} → (∀ {y} → Owes C′ y → Owes C y) → P ⊑ (Burst C k ∪ᵖ Q) → P ⊑ (Burst C′ k ∪ᵖ Q)
burst-dn {C = C} {C′} {k = k} d (ks , f) = ks , λ x → [ (λ { (inj₁ (k′ , (e , r , h) , q)) → inj₁ (inj₁ (k′ , (e , r , held-dn {C = C} {C′} {k = k} d h) , q)) ; (inj₂ q) → inj₁ (inj₂ q) }) , inj₂ ]′ (f x)

-- Every row of `E` the cursor has not passed in `P`, but for finitely
-- many.
record TailP {A} (C : Cur) (E : EmissionSet A) (P : Pts) : Set where
  constructor tailp
  field
    tks : List Pos
    ttl : ∀ {y e} → E y e → Owes C y → P y ⊎ y ∈ tks

⊑-refl : ∀ {P} → P ⊑ P
⊑-refl = [] , inj₁

⊑-trans : ∀ {P Q S} → P ⊑ Q → Q ⊑ S → P ⊑ S
⊑-trans (ks , f) (ls , g) = ls ++ ks , λ x → [ (λ q → [ inj₁ , (λ i → inj₂ (∈-++⁺ˡ i)) ]′ (g q)) , (λ i → inj₂ (∈-++⁺ʳ ls i)) ]′ (f x)

∪-⊑ : ∀ {P Q P′ Q′} → P ⊑ P′ → Q ⊑ Q′ → (P ∪ᵖ Q) ⊑ (P′ ∪ᵖ Q′)
∪-⊑ (ks , f) (ls , g) = ks ++ ls , λ
  { (inj₁ x) → [ (λ y → inj₁ (inj₁ y)) , (λ i → inj₂ (∈-++⁺ˡ i)) ]′ (f x)
  ; (inj₂ x) → [ (λ y → inj₁ (inj₂ y)) , (λ i → inj₂ (∈-++⁺ʳ ks i)) ]′ (g x) }

under-⊑ : ∀ {P Q} → P ⊑ Q → Under P ⊑ Under Q
under-⊑ (ks , f) = map (_⊕ [ ix 0 ]) ks , λ { (k , x , refl) → [ (λ y → inj₁ (k , y , refl)) , (λ i → inj₂ (∈-map⁺ (_⊕ [ ix 0 ]) i)) ]′ (f x) }

∅-⊑ : ∀ {P} → ∅ᵖ ⊑ P
∅-⊑ = [] , λ ()

tailp-⊑ : ∀ {A} {C} {E : EmissionSet A} {P Q} → TailP C E P → P ⊑ Q → TailP C E Q
tailp-⊑ (tailp ks f) (ls , g) = tailp (ls ++ ks) λ r o → [ (λ x → [ inj₁ , (λ i → inj₂ (∈-++⁺ˡ i)) ]′ (g x)) , (λ i → inj₂ (∈-++⁺ʳ ls i)) ]′ (f r o)

tailp-dn : ∀ {A} {C C′} {E : EmissionSet A} {P} → (∀ {y} → Owes C′ y → Owes C y) → TailP C E P → TailP C′ E P
tailp-dn d (tailp ks f) = tailp ks λ r o → f r (d o)

-- The engine's events are all visible.
vis : ∀ {A} (e : Evᴹ A) → Visible (toEv e)
vis (nx _) = _
vis cp     = _

-- Where a subtree's rows may lie.
Rgn : Set₁
Rgn = Pos → Set

-- A frozen entry is a meaning: one visible row at a position, none past
-- its end, each inside its subtree's region.  What lies past its end is
-- a pin of a connect subscribed before it: a hot binder is read `Proper`,
-- a leaf stops at its end, a connect's echo waits on its body (`Alive`)
-- and its burst is of its own subscription, which its body ends after.
record Sound {A} (Rg : Rgn) (E : EmissionSet A) : Set where
  field
    fn   : ∀ {y e e′} → E y e → E y e′ → Visible e → Visible e′ → e ≡ e′
    ends : ∀ {c y e} → E c end → E y e → Visible e → y ≼ c
    past : ∀ {c y e} → E c end → E y e → c ≺ y → Σ Pos λ r → e ≡ pin r × r ≺ c
    rg   : ∀ {y e} → E y e → Visible e → Rg y

-- Outside what `E`'s rows subscribe below them: no row's plain child's
-- world leads `y`.
Excl : ∀ {A} → (Pos → Set) → EmissionSet A → Pos → Set
Excl H E y = ∀ {r e l w} → E r e → Plain l → W⁼ H (r ⊕ [ l ]) w → w ⊑ʷ y → ⊥

-- A subscription at `q` reading `E`: it and its world lie in the region,
-- but for what its rows subscribe below them, which is its children's.
Within : ∀ {Γ A} → Rgn → Scope Γ → Pos → EmissionSet A → Set
Within Rg sc q E = Rg q × (∀ {y} → W (Hots (full sc)) q y → Excl (Hots (full sc)) E y → Rg y)

------------------------------------------------------------------------
-- A joiner's feed

-- A joiner's rows whose source row the cursor has not passed: still to
-- be fed to it.
Unfed : ∀ {A} → Cur → Den A → Pos → EmissionSet A
Unfed C (hot t)    j = Rejoin j (λ k e → t k e × Owes C k)
Unfed C (coldAt _) j = λ _ _ → ⊥

------------------------------------------------------------------------
-- A JOINER'S POLICY, read off its outer's frozen entry: each value's
-- lane, whether it runs, where its lane is subscribed, and which later
-- value kills it.

record Pol (A B : Set) : Set₁ where
  field
    Lane  : Pos → A → EmissionSet B
    Runs  : Pos → Set
    -- what a passed value needs to be begun or waiting: a bounded merge
    -- drops none
    Takes : Pos → Set
    takes : ∀ {q} → Runs q → Takes q
    Start : Pos → A → Pos → Set
    Kill  : Pos → Pos → Set
    -- whether a value can wait for a slot
    Queues : Bool
    -- what its slots hold of the values begun and waiting, and the live
    -- count, at a cursor
    Slots : Cur → List (Pos × A) → List (Pos × A) → ℕ → Set
open Pol public

-- The values listed, numbered in the outer's order from `i`.
Nths : ∀ {A} → EmissionSet A → ℕ → List (Pos × A) → Set
Nths O i []             = ⊤
Nths O i ((q , a) ∷ xs) = Values.Nth O i q a × Nths O (suc i) xs

-- No later value cuts the lane by `k`.
NoKill : ∀ {A B} → Pol A B → Pos → Pos → Set
NoKill P q k = ∀ {q′} → Kill P q q′ → k ≼ q′

-- A lane's rows its joiner keeps: those before any cut, and the pins of
-- a burst begun before it.
Kept : ∀ {A B} → Pol A B → Pos → A → EmissionSet B
Kept P q a k e = (Lane P q a k e × NoKill P q k) ⊎ Σ Pos λ r → e ≡ pin r × Lane P q a k e × NoKill P q r × T (inside r k)

-- An exhaust's last value passed, at `x`, and the lane it last ran, at
-- `q`, the last begun: every lane begun before ended before `q`.  None
-- passed, none begun.
ExSlots : ∀ {A B} → (A → Den B) → EmissionSet A → Cur → List (Pos × A) → Set
ExSlots {A} f O C vs =
    (vs ≡ [] × (∀ {k b} → O k (out b) → Owes C k))
  ⊎ Σ Pos λ x → Σ (List (Pos × A)) λ us → Σ Pos λ q → Σ A λ a →
      vs ≡ us ++ (q , a) ∷ [] × (Σ A λ b → O x (out b)) × (¬ Owes C x) × (∀ {k b} → O k (out b) → ¬ Owes C k → k ≼ x)
      × Exhaust.Cur f O x q × (∀ {q′ a′} → (q′ , a′) ∈ us → Σ Pos λ c → LaneOf f q′ a′ c end × c ≺ q)

polF : ∀ {A B} → FlatOp → (A → Den B) → EmissionSet A → Pol A B
polF (mergeᶠ nothing)  f O = record { Lane = LaneOf f ; Runs = λ _ → ⊤ ; Takes = λ _ → ⊤ ; takes = λ r → r
                                    ; Start = λ q _ s → s ≡ q ⊕ [ ix 1 ] ; Kill = λ _ _ → ⊥ ; Queues = false
                                    ; Slots = λ _ _ _ _ → ⊤ }
polF (mergeᶠ (just m)) f O = record { Lane = Bounded.Lane m f O ; Runs = Bounded.Indexed m f O ; Takes = λ _ → ⊤ ; takes = λ _ → tt
                                    ; Start = λ q a s → Σ ℕ λ i → Bounded.Sub m f O i q s a ; Kill = λ _ _ → ⊥ ; Queues = true
                                    ; Slots = λ _ vs ws n → Nths O 0 (vs ++ ws) × n ≤ m × (ws ≡ [] ⊎ n ≡ m) }
polF switchᶠ           f O = record { Lane = LaneOf f ; Runs = λ _ → ⊤ ; Takes = λ _ → ⊤ ; takes = λ r → r
                                    ; Start = λ q _ s → s ≡ q ⊕ [ ix 1 ] ; Kill = λ q q′ → Σ _ λ a′ → O q′ (out a′) × q ≺ q′ ; Queues = false
                                    ; Slots = λ _ _ _ _ → ⊤ }
polF exhaustᶠ          f O = record { Lane = LaneOf f ; Runs = Exhaust.Run f O ; Takes = Exhaust.Run f O ; takes = λ r → r
                                    ; Start = λ q _ s → s ≡ q ⊕ [ ix 1 ] ; Kill = λ _ _ → ⊥ ; Queues = false
                                    ; Slots = λ C vs _ _ → ExSlots f O C vs }

-- A joiner with nothing begun or queued, its outer's values all owed,
-- fills no slot.
slots-0 : ∀ {A B} op (f : A → Den B) O {C} → (∀ {k b} → O k (out b) → Owes C k) → Pol.Slots (polF op f O) C [] [] 0
slots-0 (mergeᶠ nothing)  f O _ = tt
slots-0 (mergeᶠ (just m)) f O _ = tt , z≤n , inj₁ refl
slots-0 switchᶠ           f O _ = tt
slots-0 exhaustᶠ          f O o = inj₁ (refl , o)

-- The cursor moved on past none of the outer's values: the slots hold.
SlotsMv : ∀ {A B} → Pol A B → EmissionSet A → Set
SlotsMv P O = ∀ {C C′ vs ws n} → (∀ {y} → Owes C′ y → Owes C y) → (∀ {k b} → O k (out b) → Owes C k → Owes C′ k)
            → Pol.Slots P C vs ws n → Pol.Slots P C′ vs ws n

slots-mv : ∀ {A B} op {f : A → Den B} {O} → SlotsMv (polF op f O) O
slots-mv (mergeᶠ nothing)  dn nv s = s
slots-mv (mergeᶠ (just m)) dn nv s = s
slots-mv switchᶠ           dn nv s = s
slots-mv exhaustᶠ          dn nv (inj₁ (e , o)) = inj₁ (e , λ x → nv x (o x))
slots-mv exhaustᶠ          dn nv (inj₂ (x , us , q , a , e , xv , nxo , lt , cu , ue)) =
  inj₂ (x , us , q , a , e , xv , (λ o → nxo (dn o)) , (λ y nk → lt y (λ o → nk (nv y o))) , cu , ue)

-- The joiner's rows, as its operator's meaning reads them.
JoinF : ∀ {A B} → FlatOp → (A → Den B) → EmissionSet A → EmissionSet B
JoinF (mergeᶠ nothing)  f O = Merge.JoinT f O
JoinF (mergeᶠ (just m)) f O = Bounded.JoinT m f O
JoinF switchᶠ           f O = Switch.JoinT f O
JoinF exhaustᶠ          f O = Exhaust.JoinT f O

-- A connect's entry: its rows truncated, and its body's rows each with
-- few before it.
ConnE : ∀ {X B} → Pos → EmissionSet X → EmissionSet B → EmissionSet B → Set
ConnE r σ β E = Truncate (Connecting.ConnT r σ β) ≈ E × (∀ {y e} → β y e → Reach β y e)

-- A joiner's entry: its rows truncated, its outer's rows the ghost's.
JoinE : ∀ {Γ A B} → Scope Γ → FlatOp → (A → Obs Timeline Γ B) → Obs Timeline Γ A × Pos → EmissionSet A → EmissionSet B → Set₁
JoinE sc op f ω O E = pendRows (full sc) (proj₁ ω) (proj₂ ω) ≡ O × Truncate (JoinF op (λ a → ⟦ f a ⟧ (full sc)) O) ≈ E

-- A source's rows a connect reads before `p`, few.
FewBefore : ∀ {X} → EmissionSet X → Pos → Set
FewBefore σ p = Σ (List Pos) λ ks → ∀ {y e} → σ y e → (y ⊕ [ ix 0 ]) ≺ p → y ∈ ks

-- Passed before a row in flight at `p`: a source's few rows a connect reads.
few-behind : ∀ {X} {σ : EmissionSet X} {p} → Behind (bef p) σ → FewBefore σ p
few-behind {p = p} (ks , f) = ks , λ {y} r lt → f r (λ py → py (≺-trans {y} {y ⊕ [ ix 0 ]} {p} (≺-ext y {ix 0} []) lt))

-- No value that kills the lane at `q` passed.
Unkilled : ∀ {A B} → Cur → Pol A B → Pos → Set
Unkilled C P q = ∀ {q′} → Kill P q q′ → Owes C q′

-- A live lane's end before any cut not passed.
Unended : ∀ {A B} → Cur → Pol A B → Pos → A → Set
Unended C P q a = ∀ {c} → Lane P q a c end → NoKill P q c → Owes C c

-- What kills a lane is a later value of its outer.
kill-out : ∀ {A B} op {F : A → Den B} {O q q′} → Kill (polF op F O) q q′ → Σ A λ a′ → O q′ (out a′) × q ≺ q′
kill-out (mergeᶠ nothing)  ()
kill-out (mergeᶠ (just m)) ()
kill-out switchᶠ           k = k
kill-out exhaustᶠ          ()

-- A begun lane as its joiner reads it: running from where it was
-- subscribed, its entry its lane's, no value killing it passed; or over,
-- by its end or a later value, what it still owes within what its state
-- still runs.
data Hole {A B} (C : Cur) (P : Pol A B) (q : Pos) (a : A) : Pts → EmissionSet B → Bool → Set₁ where
  h-live : ∀ {s E} → Start P q a s → E ≈ Lane P q a → Unkilled C P q → Unended C P q a → Hole C P q a ∅ᵖ E true
  h-end  : ∀ {c E Ph} → Lane P q a c end → ¬ Owes C c → TailP C (Kept P q a) Ph → Hole C P q a Ph E false
  h-kill : ∀ {q′ E Ph} → Kill P q q′ → ¬ Owes C q′ → TailP C (Kept P q a) Ph → Hole C P q a Ph E false

bump : Bool → ℕ → ℕ
bump true  n = suc n
bump false n = n

-- Every connect of a scope subscribed where admissible: what makes each
-- of its handles a lawful hot, whose rows lie none below another.
Adm : ∀ {Γ} → Scope Γ → Set
Adm unbound        = ⊤
Adm (binds o p sc) = Ok (Hots (full sc)) p × Adm sc

-- A source subscribed: the cursor at or past where, its connect
-- admissible, so no handle in scope has a row inside it.
record SubdAt {Γ} (sc : Scope Γ) (C : Cur) (r : Pos) : Set where
  constructor subd
  field
    past : ∀ {y} → Owes C y → (r ⊕ [ ix 1 ]) ≼ y
    hok  : Ok (Hots (full sc)) r

Subd : ∀ {Γ X} → Scope Γ → Cur → CS Γ X → Set
Subd sc C k = SubdAt sc C (CS.connAt k)

-- A begun lane's end, owed and before any cut.
OwedEnd : ∀ {A B} → Cur → Pol A B → List (Pos × A) → Pos → Set
OwedEnd C P vs c = Σ Pos λ q → Σ _ λ a → (q , a) ∈ vs × Lane P q a c end × NoKill P q c × Owes C c

-- The queue's head starts under the first owed end of a begun lane.
Head : ∀ {A B} → Cur → Pol A B → List (Pos × A) → List (Pos × A) → Set
Head C P vs []              = ⊤
Head C P vs ((q , a) ∷ ws) = ∀ {c} → OwedEnd C P vs c → (∀ {c′} → OwedEnd C P vs c′ → c ≼ c′) → Start P q a (c ⊕ [ ix 1 ])

-- The values passed that wait for a slot, as the state's queue holds
-- them: their lanes not yet subscribed.  The queue is FIFO and a freed
-- slot goes to the head, so the queue is in the outer's position order;
-- only a policy that queues has one; and the head starts where the first
-- owed end of a begun lane frees its slot.
Waiting : ∀ {A B} → Cur → Pol A B → EmissionSet A → List (Pos × A) → List (Pos × A) → List A → Set
Waiting C P O vs ws qu = map proj₂ ws ≡ qu × AllPairs (λ u v → proj₁ u ≺ proj₁ v) ws
  × (∀ {q a} → (q , a) ∈ ws → O q (out a) × ¬ Owes C q × Runs P q × (∀ {s} → Start P q a s → Owes C s))
  × (T (not (Queues P)) → ws ≡ []) × Head C P vs ws

-- A head read at another cursor owing the same begun lanes' ends.
head-≡ : ∀ {A B} {C C′ : Cur} {P : Pol A B} {vs ws} → (∀ {c} → OwedEnd C′ P vs c → OwedEnd C P vs c)
       → (∀ {c} → OwedEnd C P vs c → OwedEnd C′ P vs c) → Head C P vs ws → Head C′ P vs ws
head-≡ {ws = []}    _  _  _  = tt
head-≡ {ws = _ ∷ _} dn up hd oe least = hd (dn oe) λ oe′ → least (up oe′)

-- No queue, no head.
head-[] : ∀ {A B} {C : Cur} {P : Pol A B} {vs ws} → ws ≡ [] → Head C P vs ws
head-[] refl = tt

-- An empty queue waits on any lanes begun.
wait-[] : ∀ {A B} {C : Cur} {P : Pol A B} {O : EmissionSet A} {vs vs′ ws qu} → ws ≡ []
        → Waiting C P O vs ws qu → Waiting C P O vs′ ws qu
wait-[] e (eq , ap , wf , nq , _) = eq , ap , wf , nq , head-[] e

-- Every value passed that its policy takes has begun its lane or waits.
Whole : ∀ {A B} → Cur → Pol A B → EmissionSet A → List (Pos × A) → List (Pos × A) → Set
Whole C P O vs ws = ∀ {q a} → O q (out a) → ¬ Owes C q → Takes P q → (q , a) ∈ vs ⊎ (q , a) ∈ ws

-- The state's flag: the outer's end passed.
OuterDone : ∀ {A} → Cur → EmissionSet A → Bool → Set
OuterDone C O d = (T d → Σ Pos λ c → O c end × ¬ Owes C c) × (∀ {c} → O c end → ¬ Owes C c → T d)

-- Every waiting value's lane starts past the end, still owed, of a begun
-- lane no later value kills: the end that frees its slot.
Ahead : ∀ {A B} → Cur → Pol A B → List (Pos × A) → List (Pos × A) → Set
Ahead C P vs ws = ∀ {q a s} → (q , a) ∈ ws → Start P q a s
  → Σ Pos λ q′ → Σ _ λ a′ → Σ Pos λ c → (q′ , a′) ∈ vs × Lane P q′ a′ c end × (∀ {q″} → Kill P q′ q″ → c ≼ q″) × Owes C c × c ≺ s

-- A lane's rows lie none past its end.
Ends : ∀ {A B} → Pol A B → EmissionSet A → Set
Ends P O = ∀ {q a c k e} → O q (out a) → Lane P q a c end → Lane P q a k e → Visible e → k ≼ c

-- A value's lane's world, but for what its rows subscribe below them,
-- lies in the lane's region.
LanesIn : ∀ {A B} → (Pos → Set) → (Pos → Rgn) → Pol A B → EmissionSet A → Set
LanesIn H Rl P O = ∀ {q a s y} → O q (out a) → Start P q a s → W⁼ H s y → Excl H (Lane P q a) y → Rl q y

-- In the outer's position order.
Asc : ∀ {A} → List (Pos × A) → Set
Asc = AllPairs (λ u v → proj₁ u ≺ proj₁ v)

-- A lane's region, read off its policy: the world it subscribes in, but
-- for what its rows subscribe below them.  A bounded merge subscribes a
-- queued lane below the end of the lane it frees, inside that lane's
-- world, so the exclusion is what keeps the two apart.
LaneRg : ∀ {A B} → (Pos → Set) → Pol A B → EmissionSet A → Pos → Rgn
LaneRg H P O q y = Σ _ λ a → Σ Pos λ s → O q (out a) × Start P q a s × W⁼ H s y × Excl H (Lane P q a) y

-- A joiner's parts: each value's lane in its region, the outer in what
-- no lane's holds.
JRl : ∀ {Γ A B} → Scope Γ → Rgn → FlatOp → (A → Obs Timeline Γ B) → EmissionSet A → Pos → Rgn
JRl sc Rg op f O q y = Rg y × LaneRg (Hots (full sc)) (polF op (λ a → ⟦ f a ⟧ (full sc)) O) O q y

JRo : ∀ {Γ A B} → Scope Γ → Rgn → FlatOp → (A → Obs Timeline Γ B) → EmissionSet A → Rgn
JRo sc Rg op f O y = Rg y × (∀ {q} → LaneRg (Hots (full sc)) (polF op (λ a → ⟦ f a ⟧ (full sc)) O) O q y → ⊥)

-- A joiner's outer entry keeps the invariant where it subscribed, and
-- every lane's program everywhere admissible.
record JInv {Γ A B} (sc : Scope Γ) (f : A → Obs Timeline Γ B) (O : EmissionSet A) : Set where
  field
    at : Pos
    ok : Ok (Hots (full sc)) at
    io : InvAt (Hots (full sc)) at O
    fi : ∀ a → InvD (Hots (full sc)) (⟦ f a ⟧ (full sc))
    adm : Adm sc

-- A cold's frame played where its timeline puts it: under a reachable
-- root, at or after the root's tick.
Ticked : ∀ {A} → Tape A → Set
Ticked (play τ u i t fr) = RealR u × tickᴿ u ≤ τ + t
Ticked (ending _)        = ⊤
Ticked tapeOver          = ⊤

------------------------------------------------------------------------
-- WHAT A DEAD NODE STILL SHOWS.  A part no live node reads is read by
-- nobody, but its isles' pins still show above it: frozen where the node
-- died, at `D`, a row it holds pinned to a connect subscribed by then
-- shows in what holds it, at or under the row, pinned to a connect
-- subscribed by the holder's death.

-- A connect at `r` the cursor has reached: at or before the row last
-- delivered, or the one about to be.  Alike either side of a rise, so a
-- part dying as its row rises keeps what it had reached.
Thru : Cur → Pos → Set
Thru origin  r = ⊥
Thru (bef p) r = r ≼ p
Thru (aft p) r = r ≼ p

-- Reached at `C` whatever `D` reached: `C` is `D` moved on.
Dom : Cur → Cur → Set
Dom C D = ∀ {r} → Thru D r → Thru C r

-- A pin of `E` shows in `E′`, down a first-child chain.
Lifts : ∀ {A B} → Cur → EmissionSet A → Cur → EmissionSet B → Set
Lifts D E D′ E′ = ∀ {y r} → Thru D r → T (inside r y) → E y (pin r) → Reach E y (pin r)
                → Σ Path λ xs → Σ Pos λ r′ → Thru D′ r′ × T (inside r′ (y ⊕ xs)) × E′ (y ⊕ xs) (pin r′) × Reach E′ (y ⊕ xs) (pin r′)
                  × All (_≡ ix 0) xs

-- Its pins shown above, by a reader that has read whatever it has.
record Up {A B} (D : Cur) (E : EmissionSet A) (D′ : Cur) (E′ : EmissionSet B) : Set where
  constructor up
  field
    lift : Lifts D E D′ E′
    dom  : Dom D′ D

-- An attached source's pins shown above: read on, perhaps, past its
-- reader, within its subscribe call.
record UpA {A B} (D : Cur) (E : EmissionSet A) (D′ : Cur) (E′ : EmissionSet B) : Set where
  constructor upa
  field
    lift : Lifts D E D′ E′

-- A connect's body, read under the scope it was bound in.
InScope : ∀ {Γ X} → CS Γ X → Scope Γ → Set₁
InScope k sc = CS.scope k ≡ sc

-- Every position `D` has reached lies at or before `c`.
Onward : Cur → Pos → Set
Onward D c = ∀ {r} → Thru D r → r ≼ c

-- A connect's source's end: not closed, past what `D` has reached;
-- closed, the row it ended at.
Open : ∀ {Γ X} → CS Γ X → Cur → Set
Open k D = (T (not (CS.closed k)) → ∀ {c} → Frozen k c end → Onward D c) × (T (CS.closed k) → Frozen k (CS.endAt k) end)

-- An unattached source's cursor: within its subscribe call, reaching
-- nothing past the slot after it.
InCall : ∀ {Γ X} → Cur → CS Γ X → Set
InCall C k = Dom (bef (CS.connAt k ⊕ [ ix 2 ])) C

-- An isle's pins show in its connect's entry a level down.  A row inside
-- its subscription, with finitely many before it, is pinned there to the
-- connect (`burst`).  A row past it pinned to a connect no later than the
-- slot after the subscription is pinned to one enclosing the connect,
-- and kept (`kept`).
record BurstsAt {X B} (F : EmissionSet X) (c : Pos) (E : EmissionSet B) : Set where
  constructor bursts
  field
    win  : ∀ {y} {e : Ev X} → F y e → T (inside (c ⊕ [ ix 1 ]) y) → Few F y
         → E (y ⊕ [ ix 0 ]) (pin c) × Reach E (y ⊕ [ ix 0 ]) (pin c)
    kept : ∀ {y r} → F y (pin r) → ¬ T (inside (c ⊕ [ ix 1 ]) y) → T (inside r y) → r ≼ (c ⊕ [ ix 2 ])
         → Reach F y (pin r)
         → r ≼ c × E (y ⊕ [ ix 0 ]) (pin r) × Reach E (y ⊕ [ ix 0 ]) (pin r)

Bursts : ∀ {Γ X B} → CS Γ X → EmissionSet B → Set
Bursts k E = BurstsAt (Frozen k) (CS.connAt k) E

------------------------------------------------------------------------
-- A NODE IN STEP WITH ITS FROZEN ENTRY: what its state still owes is
-- exactly `E`'s visible rows past `C`.  `E` is pinned from above by the
-- frame it sits in; a subscription not yet run is pinned by its program
-- outside `Sync`, in `src-pend` and `pending`.

data Sync : ∀ {Γ} → Scope Γ → Rgn → Cur → ∀ {A} → St Γ A → EmissionSet A → Set₁

-- A connect's source: running, its frozen entry what it owes; or not yet
-- subscribed, which its body's own mark does at the connect's `ix 1`.
data Src : ∀ {Γ X} → Scope Γ → Rgn → Cur → CS Γ X → St Γ X → Set₁

-- NOTHING IN STEP: no subscription pending, every connect's source
-- attached or ended.
QuietL : ∀ {Γ A} → List (St Γ A) → Set

Quiet : ∀ {Γ A} → St Γ A → Set
Quiet (pend _ _)               = ⊥
Quiet (mapS _ s)               = Quiet s
Quiet (scanS _ _ s)            = Quiet s
Quiet (cutS _ _ s)             = Quiet s
Quiet (lnS _ s)                = Quiet s
Quiet (takeS _ _ _ s)          = Quiet s
Quiet (flatS _ _ _ _ _ _ o ls) = Quiet o × QuietL ls
Quiet (connS k o b)            = (T (CS.srcAtt k) ⊎ T (CS.closed k)) × Quiet o × Quiet b
Quiet _                        = ⊤

QuietL []       = ⊤
QuietL (l ∷ ls) = Quiet l × QuietL ls

-- A part's connects, each read under the scope it was bound in, and each
-- closed one at the row its source ended at.
SealedL : ∀ {Γ A} → Scope Γ → List (St Γ A) → Set₁

Sealed : ∀ {Γ A} → Scope Γ → St Γ A → Set₁
Sealed sc (mapS _ s)               = Sealed sc s
Sealed sc (scanS _ _ s)            = Sealed sc s
Sealed sc (cutS _ _ s)             = Sealed sc s
Sealed sc (lnS _ s)                = Sealed sc s
Sealed sc (takeS _ _ _ s)          = Sealed sc s
Sealed sc (flatS _ _ _ _ _ _ o ls) = Sealed sc o × SealedL sc ls
Sealed sc (connS k o b)            = CS.scope k ≡ sc × (T (CS.closed k) → Frozen k (CS.endAt k) end) × Sealed sc o
                                     × Sealed (binds (CS.src k) (CS.connAt k) (CS.scope k)) b
Sealed sc _                        = ⊤₁

SealedL sc []       = ⊤₁
SealedL sc (l ∷ ls) = Sealed sc l × SealedL sc ls

-- A PART NO LIVE NODE READS: no entry ties it, only where it may still
-- run on, cursor-free.  Its isles are the one thing in it still in step.
data Husk : ∀ {Γ} → Scope Γ → Cur → ∀ {A} → St Γ A → EmissionSet A → Pts → Set₁

-- A joiner's lanes, none read, each showing in the joiner's entry.
data HuskL : ∀ {Γ} → Scope Γ → Cur → ∀ {A} → List (St Γ A) → EmissionSet A → Pts → Set₁

-- A connect's source in a part no live node reads: what its state runs,
-- at each row's first effect; or, still in its subscribe call where the
-- part was last read, an ISLE, its whole burst, running on in step at its
-- own cursor.
data SrcH : ∀ {Γ X B} → Scope Γ → Cur → CS Γ X → St Γ X → EmissionSet B → Pts → Set₁

-- A connect torn down: what its source and body still run, and its rows
-- owed within them.
record Torn {Γ X B} (sc : Scope Γ) (C : Cur) (k : CS Γ X) (o : St Γ X) (b : St (X ∷ Γ) B) (β E : EmissionSet B) : Set₁ where
  inductive
  field
    D Db  : Cur
    dom   : Dom C D
    Ps Pb : Pts
    sh    : SrcH sc D k o E Ps
    bh    : Husk (binds (CS.src k) (CS.connAt k) (CS.scope k)) Db b β Pb
    bu    : Up Db β D E
    tl    : TailP C (Connecting.ConnT (CS.connAt k) (Frozen k) β) (Ps ∪ᵖ Pb)
    opn   : Open k Db

-- A lane in its joiner's list, live or over: its list entry over its
-- switch, both on while it runs and both off once it is over.
data LaneSt {Γ A B} (sc : Scope Γ) (Rg : Rgn) (C : Cur) (P : Pol A B) (q : Pos) (a : A) : St Γ B → Bool → Set₁ where
  l-live : ∀ {at l E} → Hole C P q a ∅ᵖ E true → Sync sc Rg C l E → Sound Rg E → LaneSt sc Rg C P q a (lnS true (cutS true at l)) true
  l-dead : ∀ {at l E Ph D} → Hole C P q a Ph E false → Husk sc D l (Lane P q a) Ph → Dom C D → (∀ {r} → Thru D r → NoKill P q r) → LaneSt sc Rg C P q a (lnS false (cutS false at l)) false

-- The values passed that began a lane, oldest first, and how many of
-- their lanes run.
data Begun {Γ A B} (sc : Scope Γ) (Rl : Pos → Rgn) (C : Cur) (P : Pol A B) (O : EmissionSet A) : List (Pos × A) → List (St Γ B) → ℕ → Set₁ where
  none : Begun sc Rl C P O [] [] 0
  more : ∀ {q a l b vs ls n} → O q (out a) → ¬ Owes C q → Runs P q → LaneSt sc (Rl q) C P q a l b
       → Begun sc Rl C P O vs ls n → Begun sc Rl C P O ((q , a) ∷ vs) (l ∷ ls) (bump b n)

-- A joiner's bookkeeping: its begun lanes and live count, its queue, and
-- its outer's end.
data Joined {Γ A B} (sc : Scope Γ) (Rl : Pos → Rgn) (C : Cur) (P : Pol A B) (O : EmissionSet A) (d : Bool) (n : ℕ) (qu : List A)
            (ls : List (St Γ B)) : Set₁ where
  joined : ∀ {vs ws} → Begun sc Rl C P O vs ls n → Waiting C P O vs ws qu → Whole C P O vs ws → OuterDone C O d
         → Ahead C P vs ws → Asc vs → Ends P O → LanesIn (Hots (full sc)) Rl P O → Slots P C vs ws n
         → Joined sc Rl C P O d n qu ls

-- A scan's fold: of the values passed, the seed if none.
data Folded {A B} (C : Cur) (f : B → A → B) (z₀ : B) (Es : EmissionSet A) : B → Set where
  fd-none : (∀ {q a} → Es q (out a) → Owes C q) → Folded C f z₀ Es z₀
  fd-last : ∀ {q b} → Scan.Acc f z₀ Es q b → ¬ Owes C q → (∀ {k a} → Es k (out a) → q ≺ k → Owes C k) → Folded C f z₀ Es b

-- No failing value passed.
NoFail : ∀ {A} → Cur → (A → Bool) → EmissionSet A → Set
NoFail C keep Es = ∀ {q a} → Es q (out a) → T (not (keep a)) → Owes C q

-- The first failing value, at `r`.
Failure : ∀ {A} → (A → Bool) → EmissionSet A → Pos → Set
Failure keep Es r = Σ _ λ a → Es r (out a) × T (not (keep a)) × ¬ TakeWhile.Failed true keep Es r

-- Passed at `r`: whatever is still owed lies at or past it.
Gone : Cur → Pos → Set
Gone C r = ∀ {q} → Owes C q → r ≼ q

notT : ∀ b → T (not b) → T b → ⊥
notT true  () _
notT false _  ()

-- What a takeWhile failed at `r` still owes itself: its completion, under
-- `last`, until the cursor passes it.
data OweAt (C : Cur) : Owe → Pos → Set where
  o-cp   : ∀ {r} → Owes C (r ⊕ [ last ]) → OweAt C (cpAt r) r
  o-cut  : ∀ {r} → ¬ Owes C (r ⊕ [ last ]) → OweAt C (cutAt r) r
  o-over : ∀ {r} → ¬ Owes C (r ⊕ [ last ]) → OweAt C (overAt r) r

-- A connect's flags, read off its source's frozen entry and its body's:
-- closed once the source's end is passed while it runs, where it ended;
-- torn only once the body owes nothing; its teardown owed only once the
-- body's end is passed, where it ended.
record Flags {Γ X B} (C : Cur) (k : CS Γ X) (β : EmissionSet B) : Set where
  field
    shut   : T (CS.closed k) → Frozen k (CS.endAt k) end × ¬ Owes C (CS.endAt k)
    unshut : T (CS.srcLive k) → ∀ {c} → Frozen k c end → ¬ Owes C c → T (CS.closed k)
    torn   : T (not (CS.srcLive k)) → Spent C β
    owed   : ∀ {q} → CS.owedAt k ≡ just q → β q end × ¬ Owes C q
    ended  : T (CS.srcLive k) → ∀ {c} → β c end → ¬ Owes C c → CS.owedAt k ≡ just c
    -- its teardown not yet run: nothing reached past its body's end but
    -- under it
    owing  : ∀ {q} → CS.owedAt k ≡ just q → ∀ {r} → Thru C r → r ≼ q ⊎ T (inside q r)

-- A first-child chain from `q` down to `w`, `q` itself included.
data Ze (q : Pos) : Pos → Set where
  e₀ : Ze q q
  e+ : ∀ {w} → Ze q w → Ze q (w ⊕ [ ix 0 ])

-- A connect's two parts: its body's region and its source's, inside its
-- own and apart, each holding no row of a handle in scope.  The body's
-- region leads none of the source's, nor reaches down a first-child chain
-- from a point of the source's past its subscription.
record Parts {Γ X B} (sc : Scope Γ) (Rg : Rgn) (k : CS Γ X) (β : EmissionSet B) : Set₁ where
  field
    Rb Rs : Rgn
    b⊆    : ∀ {y} → Rb y → Rg y
    s⊆    : ∀ {y} → Rs y → Rg y
    apart : ∀ {y} → Rb y → Rs y → ⊥
    b-lead  : ∀ {w x} → Rb w → Rs x → w ⊑ʷ x → ⊥
    b-chain : ∀ {x w} → (CS.connAt k ⊕ [ ix 1 ]) ≼ x → Rs x → Ze x w → Rb w → ⊥
    clear-b : ∀ {y} → Hots (full sc) y → Rb y → ⊥
    clear-s : ∀ {y} → Hots (full sc) y → Rs y → ⊥
    sb    : Sound Rb β
    ss    : Sound Rs (Frozen k)
    -- each read where it was entered, the two worlds apart
    cr     : Real (CS.connAt k)
    Hβ     : Pos → Set
    iβ     : InvAt Hβ (CS.connAt k ⊕ [ ix 0 ]) β
    iσ     : InvAt (Hots (full sc)) (CS.connAt k ⊕ [ ix 1 ]) (Frozen k)
    wapart : ∀ {w x} → W⁼ Hβ (CS.connAt k ⊕ [ ix 0 ]) w → W⁼ (Hots (full sc)) (CS.connAt k ⊕ [ ix 1 ]) x → w ⊑ʷ x → ⊥

data Sync where
  -- a started cold: what its tape has left is what its entry owes, and
  -- every row its tape has left a row of its entry, owed, in its region
  s-cold : ∀ {Γ} {sc : Scope Γ} {Rg} {C} {A} {l} {E : EmissionSet A}
         → Ticked l → Due C E ≃ Due origin (InE (tapeE l)) → Tail C E (InE (tapeE l))
         → (∀ {y e} → InE (tapeE l) y e → Owes C y × E y e × Rg y) → Sync sc Rg C (coldS true l) E
  -- a cold leaf completed: nothing left to owe
  s-coldx : ∀ {Γ} {sc : Scope Γ} {Rg} {C} {A} {l : Tape A} {E} → Spent C E → Fin C E → Sync sc Rg C (coldS false l) E
  -- an of: what it has left is what its entry owes
  s-of   : ∀ {Γ} {sc : Scope Γ} {Rg} {C} {A} {i q} {xs : List A} {E}
         → Due C E ≃ Due origin (InE (ofᴱ q i xs)) → Tail C E (InE (ofᴱ q i xs)) → Sync sc Rg C (ofS i q xs) E
  s-done : ∀ {Γ} {sc : Scope Γ} {Rg} {C} {A} {E : EmissionSet A} → Spent C E → Fin C E → Sync sc Rg C doneS E
  s-map  : ∀ {Γ} {sc : Scope Γ} {Rg} {C} {A B} {f : A → B} {s E E′} → Sync sc Rg C s E → MapT f E ≈ E′ → Sound Rg E → Sync sc Rg C (mapS f s) E′
  -- a scan: its fold of the values passed
  s-scan : ∀ {Γ} {sc : Scope Γ} {Rg} {C} {A B} {f : B → A → B} {z z₀ s Es E}
         → Sync sc Rg C s Es → Folded C f z₀ Es z → Scan.ScanT f z₀ Es ≈ E → Sound Rg Es → Sync sc Rg C (scanS f z s) E
  s-cut  : ∀ {Γ} {sc : Scope Γ} {Rg} {C} {A} {a : Att} {s : St Γ A} {E} → Sync sc Rg C s E → Sync sc Rg C (cutS true a s) E
  -- a takeWhile not yet failed: no failing value passed
  s-take : ∀ {Γ} {sc : Scope Γ} {Rg} {C} {A} {i} {keep : A → Bool} {s Es E}
         → Sync sc Rg C s Es → NoFail C keep Es
         → TakeWhile.TakeT i keep Es ≈ E → Sound Rg Es → Sync sc Rg C (takeS i keep free s) E
  -- failed at `r`: its source is not read again, and what it still owes
  -- lies in what its source still runs
  s-took : ∀ {Γ} {sc : Scope Γ} {Rg} {C} {A} {i} {keep : A → Bool} {w s Es E r P}
         → Failure keep Es r → Gone C r → (T i → ¬ Owes C (r ⊕ [ ix 0 ])) → OweAt C w r
         → TailP C (TakeWhile.TakeT i keep Es) P → ∀ {D} → Husk sc D s Es P → Dom C D → (∀ {r′} → Thru D r′ → ¬ TakeWhile.Failed i keep Es r′)
         → TakeWhile.TakeT i keep Es ≈ E → Sound Rg Es → Sync sc Rg C (takeS i keep w s) E
  -- a joiner: its outer, and its bookkeeping over its policy
  s-flat : ∀ {Γ} {sc : Scope Γ} {Rg} {C} {A B} {op} {f : A → Obs Timeline Γ B} {ω} {d n qu o ls O E}
         → JInv sc f O → Sync sc (JRo sc Rg op f O) C o O → Joined sc (JRl sc Rg op f O) C (polF op (λ a → ⟦ f a ⟧ (full sc)) O) O d n qu ls
         → JoinE sc op f ω O E → Sound (JRo sc Rg op f O) O → Behind C (JoinF op (λ a → ⟦ f a ⟧ (full sc)) O)
         → Sync sc Rg C (flatS op f ω d n qu o ls) E
  -- a connect: its body, under its binder read whole, and its source,
  -- while the source runs; torn down, its body owes nothing and nothing
  -- reads either
  s-conn : ∀ {Γ} {sc : Scope Γ} {Rg} {C} {X B} {k : CS Γ X} {o : St Γ X} {b : St (X ∷ Γ) B} {β : EmissionSet B} {E}
         → CS.scope k ≡ sc → (pt : Parts sc Rg k β)
         → (T (CS.srcLive k) → Sync (binds (CS.src k) (CS.connAt k) sc) (Parts.Rb pt) C b β)
         → (T (CS.srcLive k) → Behind C β)
         → (T (CS.srcLive k) → Src sc (Parts.Rs pt) C k o)
         → (T (not (CS.srcLive k)) → Torn sc C k o b β E)
         → Flags C k β
         → ConnE (CS.connAt k) (Frozen k) β E
         → Sync sc Rg C (connS k o b) E
  -- a joiner: what it was fed and has not shown, and what is still to
  -- feed it.  The engine shows its inbox's head and appends in its
  -- source's order, while the entry orders rows by their rejoined
  -- position, so the inbox is ascending and ahead of all still unfed.
  s-join : ∀ {Γ} {sc : Scope Γ} {Rg} {C} {A} {j} {x : A ∈ Γ} {ib E}
         → enter (lookup (full sc) x) j ≈ E
         → Due C E ≃ (λ q e → Inbox ib q e ⊎ Due C (Unfed C (lookup (full sc) x) j) q e)
         → AllPairs (λ u v → proj₁ u ≺ proj₁ v) ib
         → (∀ {u q e} → u ∈ ib → Due C (Unfed C (lookup (full sc) x) j) q e → proj₁ u ≺ q)
         → Adm sc
         → Sync sc Rg C (joinS j true x ib) E
  s-joinx : ∀ {Γ} {sc : Scope Γ} {Rg} {C} {A} {j} {x : A ∈ Γ} {ib E} → Spent C E → Fin C E → Sync sc Rg C (joinS j false x ib) E

data Src where
  src-pend : ∀ {Γ X} {sc : Scope Γ} {Rg} {C} {k : CS Γ X} {o}
           → T (not (CS.srcAtt k)) → T (not (CS.closed k)) → CS.bodyAt k ≡ just (CS.connAt k) → CS.attSrc k ≡ nothing
           → Adm (binds (CS.src k) (CS.connAt k) sc)
           → pendRows (full sc) o (CS.connAt k ⊕ [ ix 1 ]) ≈ Frozen k
           → Within Rg sc (CS.connAt k ⊕ [ ix 1 ]) (pendRows (full sc) o (CS.connAt k ⊕ [ ix 1 ]))
           → Owes C (CS.connAt k ⊕ [ ix 1 ]) → Thru C (CS.connAt k ⊕ [ ix 0 ])
           → Src sc Rg C k (pend o (CS.connAt k ⊕ [ ix 1 ]))
  -- subscribed: the cursor at or past its subscription, made where
  -- admissible
  src-on   : ∀ {Γ X} {sc : Scope Γ} {Rg} {C} {k : CS Γ X} {o} → T (not (CS.closed k)) → Sync sc Rg C o (Frozen k) → Behind C (Frozen k)
           → Subd sc C k → AttFin k → (T (not (CS.srcAtt k)) → AttOwed k) → (T (not (CS.srcAtt k)) → InCall C k) → T (CS.srcLive k)
           → Src sc Rg C k o
  -- ended: nothing visible left to owe, the rest within what its subtree
  -- still runs
  src-shut : ∀ {Γ X} {sc : Scope Γ} {Rg} {C} {k : CS Γ X} {o P} → T (CS.closed k) → Spent C (Frozen k)
           → TailP C (Frozen k) P → ∀ {D} → Husk sc D o (Frozen k) P → Dom C D → Behind C (Frozen k)
           → Subd sc C k → (T (not (CS.srcAtt k)) → AttOwed k × InCall C k) → AttFin k → T (CS.srcLive k) → Src sc Rg C k o

data Husk where
  -- nothing in it still in step
  h-blank : ∀ {Γ} {sc : Scope Γ} {D} {A} {s : St Γ A} {E} → Quiet s → Sealed sc s → Husk sc D s E ∅ᵖ
  h-map   : ∀ {Γ} {sc : Scope Γ} {D D₁} {A B} {f : A → B} {s E₁ E P} → Husk sc D₁ s E₁ P → Up D₁ E₁ D E → Husk sc D (mapS f s) E P
  h-scan  : ∀ {Γ} {sc : Scope Γ} {D D₁} {A B} {f : B → A → B} {z s E₁ E P} → Husk sc D₁ s E₁ P → Up D₁ E₁ D E → Husk sc D (scanS f z s) E P
  h-cut   : ∀ {Γ} {sc : Scope Γ} {D D₁} {A} {l a} {s : St Γ A} {E₁ E P} → Husk sc D₁ s E₁ P → Up D₁ E₁ D E → Husk sc D (cutS l a s) E P
  h-ln    : ∀ {Γ} {sc : Scope Γ} {D D₁} {A} {b} {s : St Γ A} {E₁ E P} → Husk sc D₁ s E₁ P → Up D₁ E₁ D E → Husk sc D (lnS b s) E P
  h-take  : ∀ {Γ} {sc : Scope Γ} {D D₁} {A} {i} {keep : A → Bool} {w s E₁ E P} → Husk sc D₁ s E₁ P → Up D₁ E₁ D E → Husk sc D (takeS i keep w s) E P
  h-flat  : ∀ {Γ} {sc : Scope Γ} {D D₁} {A B} {op} {f : A → Obs Timeline Γ B} {ω} {d n qu o ls O E P Q}
          → Husk sc D₁ o O P → Up D₁ O D E → HuskL sc D ls E Q → Husk sc D (flatS op f ω d n qu o ls) E (P ∪ᵖ Q)
  h-conn  : ∀ {Γ} {sc : Scope Γ} {D D₁} {X B} {k : CS Γ X} {o} {b : St (X ∷ Γ) B} {β E P Q}
          → SrcH sc D k o E P → Husk (binds (CS.src k) (CS.connAt k) (CS.scope k)) D₁ b β Q → Up D₁ β D E → Open k D₁ → InScope k sc
          → Husk sc D (connS k o b) E (P ∪ᵖ Q)

data HuskL where
  hl-none : ∀ {Γ} {sc : Scope Γ} {D} {A} {E} → HuskL sc D {A} [] E ∅ᵖ
  hl-more : ∀ {Γ} {sc : Scope Γ} {D D₁} {A} {l : St Γ A} {ls E₁ E P Q} → Husk sc D₁ l E₁ P → Up D₁ E₁ D E → HuskL sc D ls E Q → HuskL sc D (l ∷ ls) E (P ∪ᵖ Q)

data SrcH where
  sh-dead  : ∀ {Γ X B} {sc : Scope Γ} {D D₁} {k : CS Γ X} {o} {E₁ : EmissionSet X} {E : EmissionSet B} {P} → Husk sc D₁ o E₁ P → UpA D₁ E₁ D E
           → T (CS.srcAtt k) ⊎ T (CS.closed k) → (∀ {c} → Hots (full sc) c → Onward D c → Onward D₁ c)
           → SrcH sc D k o E (Under P)
  sh-isle  : ∀ {Γ X B} {sc : Scope Γ} {D} {k : CS Γ X} {o} {E : EmissionSet B} {Ri Ci}
           → T (not (CS.srcAtt k)) → T (not (CS.closed k)) → Sync sc Ri Ci o (Frozen k) → Behind Ci (Frozen k) → Subd sc Ci k
           → Sound Ri (Frozen k) → AttOwed k → InCall Ci k → Bursts k E → Thru D (CS.connAt k ⊕ [ ix 0 ]) → SrcH sc D k o E (Burst Ci k)
  -- an isle whose source has ended
  sh-islec : ∀ {Γ X B} {sc : Scope Γ} {D D₁} {k : CS Γ X} {o} {E : EmissionSet B} {Ci P}
           → T (not (CS.srcAtt k)) → T (CS.closed k) → Spent Ci (Frozen k) → TailP Ci (Frozen k) P → Husk sc D₁ o (Frozen k) P → Dom Ci D₁
           → Behind Ci (Frozen k) → Subd sc Ci k → AttOwed k → InCall Ci k → Bursts k E → Thru D (CS.connAt k ⊕ [ ix 0 ]) → SrcH sc D k o E (Burst Ci k)
  -- a source not yet subscribed: its whole burst, which runs whatever
  -- happens above it, its body's mark subscribing it regardless
  sh-pend  : ∀ {Γ X B} {sc : Scope Γ} {D} {k : CS Γ X} {o} {E : EmissionSet B} {Ri}
           → T (not (CS.srcAtt k)) → T (not (CS.closed k)) → CS.bodyAt k ≡ just (CS.connAt k) → CS.attSrc k ≡ nothing → CS.scope k ≡ sc
           → Adm (binds (CS.src k) (CS.connAt k) sc) → pendRows (full sc) o (CS.connAt k ⊕ [ ix 1 ]) ≈ Frozen k
           → Within Ri sc (CS.connAt k ⊕ [ ix 1 ]) (pendRows (full sc) o (CS.connAt k ⊕ [ ix 1 ])) → Sound Ri (Frozen k)
           → Bursts k E → Thru D (CS.connAt k ⊕ [ ix 0 ])
           → SrcH sc D k (pend o (CS.connAt k ⊕ [ ix 1 ])) E (Burst (bef (CS.connAt k ⊕ [ ix 1 ])) k)

-- A connect's parts read again under fields they do not read.
re-parts : ∀ {Γ X B} {sc : Scope Γ} {Rg} {k k′ : CS Γ X} {β : EmissionSet B} → CS.connAt k ≡ CS.connAt k′ → Frozen k ≡ Frozen k′
         → Parts sc Rg k β → Parts sc Rg k′ β
re-parts {k = k} {k′} ca e pt = record { Rb = Parts.Rb pt ; Rs = Parts.Rs pt ; b⊆ = Parts.b⊆ pt ; s⊆ = Parts.s⊆ pt ; apart = Parts.apart pt
                       ; b-lead = Parts.b-lead pt
                       ; b-chain = λ {x} px → Parts.b-chain pt (subst (λ u → (u ⊕ [ ix 1 ]) ≼ x) (sym ca) px)
                       ; clear-b = Parts.clear-b pt ; clear-s = Parts.clear-s pt ; sb = Parts.sb pt ; ss = subst (Sound (Parts.Rs pt)) e (Parts.ss pt)
                       ; cr = subst Real ca (Parts.cr pt) ; Hβ = Parts.Hβ pt
                       ; iβ = subst (λ u → InvAt (Parts.Hβ pt) (u ⊕ [ ix 0 ]) _) ca (Parts.iβ pt)
                       ; iσ = subst (λ u → InvAt _ (u ⊕ [ ix 1 ]) (Frozen k′)) ca (subst (InvAt _ _) e (Parts.iσ pt))
                       ; wapart = λ {w} {x} → subst (λ u → W⁼ (Parts.Hβ pt) (u ⊕ [ ix 0 ]) w → W⁼ _ (u ⊕ [ ix 1 ]) x → w ⊑ʷ x → ⊥) ca (Parts.wapart pt) }
