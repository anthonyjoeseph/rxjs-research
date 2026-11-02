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
open import Data.List using (List; []; _∷_; [_]; _++_; reverse; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Data.List.Relation.Unary.All using (lookup)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; suc; _+_; _≤_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-map⁺)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Events using (Pos; Timeline; ix; last; ofᴱ; tick; inside)
open import denotation.Read using (Visible)
open import denotation.EmissionSet using (EmissionSet; out; end; pin; Unpinned; _≺_; _≼_; Reach; Truncate; enter; ⟦_⟧; Den; hot; coldAt; Rejoin;
  InE; MapT; LaneOf; module Scan; module TakeWhile; module Connecting; module Merge;
  module Bounded; module Switch; module Exhaust)
open import operation.PureObservable using (module Machine; Tape; play; ending) renaming (over to tapeOver)

open Machine using (St; Ctx; Conf; ⟨_,_,_,_⟩; Scope; unbound; binds; CS; Owe; closed; free; cpAt; cutAt; overAt; scopeOf;
                    Att; attached; attAt; subscribing; absorbed; rising; mapEv; nx; cp;
                    pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
                    top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody; unsub; cut; killAll; unsubIf)
                    renaming (Ev to Evᴹ; Shown to Shownᴹ)
open import denotation.Laws.Modulus using (≺-ext; ≺-trans)
open import adequacy.Rows using (_≃_; ≃-refl; ≃-sym; ≃-trans; Vis; toEv; Inbox; full; pendRows; Frozen; tapeE)
open import denotation.Laws.Worlds using (Ok; Hots; Real; W⁼; InvAt; InvD)
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

-- Alike in every row a reader meets, and row for row but for finitely
-- many: a defer's guard is a skip no reader meets.
record _≈_ {A} (E E′ : EmissionSet A) : Set where
  field
    alike : Vis E ≃ Vis E′
    cov   : Beneath E E′
    voc   : Beneath E′ E
open _≈_ public

beneath-trans : ∀ {A} {E E′ E″ : EmissionSet A} → Beneath E E′ → Beneath E′ E″ → Beneath E E″
beneath-trans (ks , f) (ls , g) = ls ++ ks , λ r → [ (λ r′ → [ inj₁ , (λ i → inj₂ (∈-++⁺ʳ ls i)) ]′ (f r′)) , (λ i → inj₂ (∈-++⁺ˡ i)) ]′ (g r)

≈-refl : ∀ {A} {E : EmissionSet A} → E ≈ E
≈-refl = record { alike = ≃-refl ; cov = [] , inj₁ ; voc = [] , inj₁ }

≈-sym : ∀ {A} {E E′ : EmissionSet A} → E ≈ E′ → E′ ≈ E
≈-sym m = record { alike = ≃-sym (alike m) ; cov = voc m ; voc = cov m }

≈-trans : ∀ {A} {E E′ E″ : EmissionSet A} → E ≈ E′ → E′ ≈ E″ → E ≈ E″
≈-trans m n = record { alike = ≃-trans (alike m) (alike n) ; cov = beneath-trans (cov m) (cov n) ; voc = beneath-trans (voc n) (voc m) }

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
Under P y = Σ Pos λ k → P k × y ≡ k ++ [ ix 0 ]

-- A connect's burst, at each row's first effect: its source's rows
-- inside its subscription, and its source's pins.  A source still in its
-- subscribe call never runs past it, so a pin past it is one a cut keeps
-- (`Connecting.kept`) that nothing reads.
Burst : ∀ {Γ X} → CS Γ X → Pts
Burst k = Under λ k′ → Σ _ λ e → Frozen k k′ e × (T (inside (CS.connAt k ++ [ ix 1 ]) k′) ⊎ ¬ Unpinned e)

-- An attached source's subscribe call has returned: finitely many of its
-- rows lie inside it.
AttFin : ∀ {Γ X} → CS Γ X → Set
AttFin k = T (CS.srcAtt k) → Σ (List Pos) λ ks → ∀ {y e} → Frozen k y e → T (inside (CS.connAt k ++ [ ix 1 ]) y) → y ∈ ks

-- An unattached source's subscribe call still to return: its attach
-- owed just after its connect's `ix 1`, or its body not yet run.
AttOwed : ∀ {Γ X} → CS Γ X → Set
AttOwed k = CS.attSrc k ≡ just (CS.connAt k ++ [ ix 1 ]) ⊎ CS.bodyAt k ≡ just (CS.connAt k)

-- Within `Q` but for finitely many.
_⊑_ : Pts → Pts → Set
P ⊑ Q = Σ (List Pos) λ ks → ∀ {y} → P y → Q y ⊎ y ∈ ks

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
under-⊑ (ks , f) = map (_++ [ ix 0 ]) ks , λ { (k , x , refl) → [ (λ y → inj₁ (k , y , refl)) , (λ i → inj₂ (∈-map⁺ (_++ [ ix 0 ]) i)) ]′ (f x) }

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
-- its end, each inside its subtree's region.
record Sound {A} (Rg : Rgn) (E : EmissionSet A) : Set where
  field
    fn   : ∀ {y e e′} → E y e → E y e′ → Visible e → Visible e′ → e ≡ e′
    ends : ∀ {c y e} → E c end → E y e → Visible e → y ≼ c
    rg   : ∀ {y e} → E y e → Visible e → Rg y

-- A subscription at `q` whose world lies in the region.
Within : ∀ {Γ} → Rgn → Scope Γ → Pos → Set
Within Rg sc q = ∀ {y} → W⁼ (Hots (full sc)) q y → Rg y

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
    Start : Pos → A → Pos → Set
    Kill  : Pos → Pos → Set
open Pol public

-- No later value cuts the lane by `k`.
NoKill : ∀ {A B} → Pol A B → Pos → Pos → Set
NoKill P q k = ∀ {q′} → Kill P q q′ → k ≼ q′

-- A lane's rows its joiner keeps: those before any cut, and the pins of
-- a burst begun before it.
Kept : ∀ {A B} → Pol A B → Pos → A → EmissionSet B
Kept P q a k e = (Lane P q a k e × NoKill P q k) ⊎ Σ Pos λ r → e ≡ pin r × Lane P q a k e × NoKill P q r × T (inside r k)

polF : ∀ {A B} → FlatOp → (A → Den B) → EmissionSet A → Pol A B
polF (mergeᶠ nothing)  f O = record { Lane = LaneOf f ; Runs = λ _ → ⊤
                                    ; Start = λ q _ s → s ≡ q ++ [ ix 1 ] ; Kill = λ _ _ → ⊥ }
polF (mergeᶠ (just m)) f O = record { Lane = Bounded.Lane m f O ; Runs = Bounded.Indexed m f O
                                    ; Start = λ q a s → Σ ℕ λ i → Bounded.Sub m f O i q s a ; Kill = λ _ _ → ⊥ }
polF switchᶠ           f O = record { Lane = LaneOf f ; Runs = λ _ → ⊤
                                    ; Start = λ q _ s → s ≡ q ++ [ ix 1 ] ; Kill = λ q q′ → Σ _ λ a′ → O q′ (out a′) × q ≺ q′ }
polF exhaustᶠ          f O = record { Lane = LaneOf f ; Runs = Exhaust.Run f O
                                    ; Start = λ q _ s → s ≡ q ++ [ ix 1 ] ; Kill = λ _ _ → ⊥ }

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
FewBefore σ p = Σ (List Pos) λ ks → ∀ {y e} → σ y e → (y ++ [ ix 0 ]) ≺ p → y ∈ ks

-- Passed before a row in flight at `p`: a source's few rows a connect reads.
few-behind : ∀ {X} {σ : EmissionSet X} {p} → Behind (bef p) σ → FewBefore σ p
few-behind {p = p} (ks , f) = ks , λ {y} r lt → f r (λ py → py (≺-trans {y} {y ++ [ ix 0 ]} {p} (≺-ext y {ix 0} []) lt))

-- A begun lane as its joiner reads it: running from where it was
-- subscribed, its entry its lane's; or over, by its end or a later value,
-- what it still owes within what its state still runs.
data Hole {A B} (C : Cur) (P : Pol A B) (q : Pos) (a : A) : Pts → EmissionSet B → Bool → Set₁ where
  h-live : ∀ {s E} → Start P q a s → ¬ Owes C s → Lane P q a ≈ E → Hole C P q a ∅ᵖ E true
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
    past : ∀ {y} → Owes C y → (r ++ [ ix 1 ]) ≼ y
    hok  : Ok (Hots (full sc)) r

Subd : ∀ {Γ X} → Scope Γ → Cur → CS Γ X → Set
Subd sc C k = SubdAt sc C (CS.connAt k)

-- The values passed that wait for a slot, as the state's queue holds
-- them: their lanes not yet subscribed.  The queue is FIFO and a freed
-- slot goes to the head, so the queue is in the outer's position order.
Waiting : ∀ {A B} → Cur → Pol A B → EmissionSet A → List (Pos × A) → List A → Set
Waiting C P O ws qu = map proj₂ ws ≡ qu × AllPairs (λ u v → proj₁ u ≺ proj₁ v) ws
  × (∀ {q a} → (q , a) ∈ ws → O q (out a) × ¬ Owes C q × Runs P q × (∀ {s} → Start P q a s → Owes C s))

-- Every value passed that runs has begun its lane or waits.
Whole : ∀ {A B} → Cur → Pol A B → EmissionSet A → List (Pos × A) → List (Pos × A) → Set
Whole C P O vs ws = ∀ {q a} → O q (out a) → ¬ Owes C q → Runs P q → (q , a) ∈ vs ⊎ (q , a) ∈ ws

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

-- A value's lane rows lie in the lane's region.
LanesIn : ∀ {A B} → (Pos → Rgn) → Pol A B → EmissionSet A → Set
LanesIn Rl P O = ∀ {q a k e} → O q (out a) → Lane P q a k e → Visible e → Rl q k

-- In the outer's position order.
Asc : ∀ {A} → List (Pos × A) → Set
Asc = AllPairs (λ u v → proj₁ u ≺ proj₁ v)

-- A lane's region, read off its policy: the world it subscribes in, up to
-- its end.  A bounded merge subscribes a queued lane under the end of the
-- lane it frees, inside that lane's world, so the cap is what keeps the
-- two apart.
LaneRg : ∀ {A B} → (Pos → Set) → Pol A B → EmissionSet A → Pos → Rgn
LaneRg H P O q y = Real y × Σ _ λ a → Σ Pos λ s → O q (out a) × Start P q a s × W⁼ H s y × (∀ {c} → Lane P q a c end → y ≼ c)

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

-- A cold's frame played where its timeline puts it: under a reachable
-- root, at or after the root's tick.
Ticked : ∀ {A} → Tape A → Set
Ticked (play τ u i t fr) = Real u × tick u ≤ τ + t
Ticked (ending _)        = ⊤
Ticked tapeOver          = ⊤

------------------------------------------------------------------------
-- A NODE IN STEP WITH ITS FROZEN ENTRY: what its state still owes is
-- exactly `E`'s visible rows past `C`.  `E` is pinned from above by the
-- frame it sits in; a subscription not yet run is pinned by its program
-- outside `Sync`, in `src-pend` and `pending`.

data Sync : ∀ {Γ} → Scope Γ → Rgn → Cur → ∀ {A} → St Γ A → EmissionSet A → Set₁

-- A connect's source: running, its frozen entry what it owes; or not yet
-- subscribed, which its body's own mark does at the connect's `ix 1`.
data Src : ∀ {Γ X} → Scope Γ → Rgn → Cur → CS Γ X → St Γ X → Set₁

-- A PART NO LIVE NODE READS: no entry ties it, only where it may still
-- run on, cursor-free.  Its isles are the one thing in it still in step.
data Husk : ∀ {Γ} → Scope Γ → ∀ {A} → St Γ A → Pts → Set₁

-- A joiner's lanes, none read.
data HuskL : ∀ {Γ} → Scope Γ → ∀ {A} → List (St Γ A) → Pts → Set₁

-- A connect's source in a part no live node reads: what its state runs,
-- at each row's first effect; or, still in its subscribe call where the
-- part was last read, an ISLE, its whole burst, running on in step at its
-- own cursor.
data SrcH : ∀ {Γ X} → Scope Γ → CS Γ X → St Γ X → Pts → Set₁

-- A connect torn down: what its source and body still run, and its rows
-- owed within them.
record Torn {Γ X B} (sc : Scope Γ) (C : Cur) (k : CS Γ X) (o : St Γ X) (b : St (X ∷ Γ) B) (β : EmissionSet B) : Set₁ where
  inductive
  field
    Ps Pb : Pts
    sh    : SrcH sc k o Ps
    bh    : Husk (binds (CS.src k) (CS.connAt k) (CS.scope k)) b Pb
    tl    : TailP C (Connecting.ConnT (CS.connAt k) (Frozen k) β) (Ps ∪ᵖ Pb)

-- A lane in its joiner's list, live or over: its list entry over its
-- switch, both on while it runs and both off once it is over.
data LaneSt {Γ A B} (sc : Scope Γ) (Rg : Rgn) (C : Cur) (P : Pol A B) (q : Pos) (a : A) : St Γ B → Bool → Set₁ where
  l-live : ∀ {at l E} → Hole C P q a ∅ᵖ E true → Sync sc Rg C l E → Sound Rg E → LaneSt sc Rg C P q a (lnS true (cutS true at l)) true
  l-dead : ∀ {at l E Ph} → Hole C P q a Ph E false → Husk sc l Ph → LaneSt sc Rg C P q a (lnS false (cutS false at l)) false

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
  joined : ∀ {vs ws} → Begun sc Rl C P O vs ls n → Waiting C P O ws qu → Whole C P O vs ws → OuterDone C O d
         → Ahead C P vs ws → Asc vs → Ends P O → LanesIn Rl P O
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
  o-cp   : ∀ {r} → Owes C (r ++ [ last ]) → OweAt C (cpAt r) r
  o-cut  : ∀ {r} → ¬ Owes C (r ++ [ last ]) → OweAt C (cutAt r) r
  o-over : ∀ {r} → ¬ Owes C (r ++ [ last ]) → OweAt C (overAt r) r

-- A connect's flags, read off its source's frozen entry and its body's:
-- closed once the source's end is passed while it runs, where it ended;
-- torn only once the body owes nothing.
record Flags {Γ X B} (C : Cur) (k : CS Γ X) (β : EmissionSet B) : Set where
  field
    shut   : T (CS.closed k) → Frozen k (CS.endAt k) end × ¬ Owes C (CS.endAt k)
    unshut : T (CS.srcLive k) → ∀ {c} → Frozen k c end → ¬ Owes C c → T (CS.closed k)
    torn   : T (not (CS.srcLive k)) → Spent C β

-- A connect's two parts: its body's region and its source's, inside its
-- own and apart, its own holding no row of a handle in scope.
record Parts {Γ X B} (sc : Scope Γ) (Rg : Rgn) (k : CS Γ X) (β : EmissionSet B) : Set₁ where
  field
    Rb Rs : Rgn
    b⊆    : ∀ {y} → Rb y → Rg y
    s⊆    : ∀ {y} → Rs y → Rg y
    apart : ∀ {y} → Rb y → Rs y → ⊥
    clear : ∀ {y} → Hots (full sc) y → Rg y → ⊥
    sb    : Sound Rb β
    ss    : Sound Rs (Frozen k)

data Sync where
  -- a started cold: what its tape has left is what its entry owes
  s-cold : ∀ {Γ} {sc : Scope Γ} {Rg} {C} {A} {l} {E : EmissionSet A}
         → Ticked l → Due C E ≃ Due origin (InE (tapeE l)) → Tail C E (InE (tapeE l)) → Sync sc Rg C (coldS true l) E
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
         → Failure keep Es r → Gone C r → (T i → ¬ Owes C (r ++ [ ix 0 ])) → OweAt C w r
         → TailP C (TakeWhile.TakeT i keep Es) P → Husk sc s P
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
         → (T (CS.srcLive k) → Src sc (Parts.Rs pt) C k o)
         → (T (not (CS.srcLive k)) → Torn sc C k o b β)
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
           → T (not (CS.srcAtt k)) → T (not (CS.closed k)) → CS.bodyAt k ≡ just (CS.connAt k) → Adm (binds (CS.src k) (CS.connAt k) sc)
           → pendRows (full sc) o (CS.connAt k ++ [ ix 1 ]) ≈ Frozen k → Within Rg sc (CS.connAt k ++ [ ix 1 ])
           → Owes C (CS.connAt k ++ [ ix 1 ])
           → Src sc Rg C k (pend o (CS.connAt k ++ [ ix 1 ]))
  -- subscribed: the cursor at or past its subscription, made where
  -- admissible
  src-on   : ∀ {Γ X} {sc : Scope Γ} {Rg} {C} {k : CS Γ X} {o} → T (not (CS.closed k)) → Sync sc Rg C o (Frozen k) → Behind C (Frozen k)
           → Subd sc C k → AttFin k → (T (not (CS.srcAtt k)) → AttOwed k) → Src sc Rg C k o
  -- ended: nothing visible left to owe, the rest within what its subtree
  -- still runs
  src-shut : ∀ {Γ X} {sc : Scope Γ} {Rg} {C} {k : CS Γ X} {o P} → T (CS.closed k) → Spent C (Frozen k)
           → TailP C (Frozen k) P → Husk sc o P → Behind C (Frozen k)
           → Subd sc C k → Src sc Rg C k o

data Husk where
  -- nothing in it still in step
  h-blank : ∀ {Γ} {sc : Scope Γ} {A} {s : St Γ A} → Husk sc s ∅ᵖ
  h-map   : ∀ {Γ} {sc : Scope Γ} {A B} {f : A → B} {s P} → Husk sc s P → Husk sc (mapS f s) P
  h-scan  : ∀ {Γ} {sc : Scope Γ} {A B} {f : B → A → B} {z s P} → Husk sc s P → Husk sc (scanS f z s) P
  h-cut   : ∀ {Γ} {sc : Scope Γ} {A} {l a} {s : St Γ A} {P} → Husk sc s P → Husk sc (cutS l a s) P
  h-ln    : ∀ {Γ} {sc : Scope Γ} {A} {b} {s : St Γ A} {P} → Husk sc s P → Husk sc (lnS b s) P
  h-take  : ∀ {Γ} {sc : Scope Γ} {A} {i} {keep : A → Bool} {w s P} → Husk sc s P → Husk sc (takeS i keep w s) P
  h-flat  : ∀ {Γ} {sc : Scope Γ} {A B} {op} {f : A → Obs Timeline Γ B} {ω} {d n qu o ls P Q}
          → Husk sc o P → HuskL sc ls Q → Husk sc (flatS op f ω d n qu o ls) (P ∪ᵖ Q)
  h-conn  : ∀ {Γ} {sc : Scope Γ} {X B} {k : CS Γ X} {o} {b : St (X ∷ Γ) B} {P Q}
          → SrcH sc k o P → Husk (binds (CS.src k) (CS.connAt k) (CS.scope k)) b Q → Husk sc (connS k o b) (P ∪ᵖ Q)

data HuskL where
  hl-none : ∀ {Γ} {sc : Scope Γ} {A} → HuskL sc {A} [] ∅ᵖ
  hl-more : ∀ {Γ} {sc : Scope Γ} {A} {l : St Γ A} {ls P Q} → Husk sc l P → HuskL sc ls Q → HuskL sc (l ∷ ls) (P ∪ᵖ Q)

data SrcH where
  sh-dead  : ∀ {Γ X} {sc : Scope Γ} {k : CS Γ X} {o P} → Husk sc o P → SrcH sc k o (Under P)
  sh-isle  : ∀ {Γ X} {sc : Scope Γ} {k : CS Γ X} {o Ri Ci}
           → T (not (CS.srcAtt k)) → T (not (CS.closed k)) → Sync sc Ri Ci o (Frozen k) → Behind Ci (Frozen k) → Subd sc Ci k
           → Sound Ri (Frozen k) → AttOwed k → SrcH sc k o (Burst k)
  -- an isle whose source has ended
  sh-islec : ∀ {Γ X} {sc : Scope Γ} {k : CS Γ X} {o Ci P}
           → T (not (CS.srcAtt k)) → T (CS.closed k) → Spent Ci (Frozen k) → TailP Ci (Frozen k) P → Husk sc o P
           → Behind Ci (Frozen k) → Subd sc Ci k → SrcH sc k o (Burst k)
  -- a source not yet subscribed: its whole burst, which runs whatever
  -- happens above it, its body's mark subscribing it regardless
  sh-pend  : ∀ {Γ X} {sc : Scope Γ} {k : CS Γ X} {o Ri}
           → T (not (CS.srcAtt k)) → T (not (CS.closed k)) → CS.bodyAt k ≡ just (CS.connAt k) → CS.scope k ≡ sc
           → Adm (binds (CS.src k) (CS.connAt k) sc) → pendRows (full sc) o (CS.connAt k ++ [ ix 1 ]) ≈ Frozen k
           → Within Ri sc (CS.connAt k ++ [ ix 1 ]) → Sound Ri (Frozen k)
           → SrcH sc k (pend o (CS.connAt k ++ [ ix 1 ])) (Burst k)

-- No rise in flight.
data Calm {A : Set} : Machine.Mode A → Set where
  c-sub : Calm subscribing
  c-abs : Calm absorbed

------------------------------------------------------------------------
-- WHAT A PART STILL RUNS, read off a node in step: its isles, each in
-- step at the cursor it was read at.

-- By a flag.
by : ∀ {ℓ} {X : Set ℓ} b → (T b → X) → (T (not b) → X) → X
by true  t _ = t tt
by false _ f = f tt

-- A body's husk read at its connect's own scope.
unbind : ∀ {Γ X B} {k : CS Γ X} {sc} {b : St (X ∷ Γ) B} {Q} → CS.scope k ≡ sc
       → Husk (binds (CS.src k) (CS.connAt k) sc) b Q → Husk (binds (CS.src k) (CS.connAt k) (CS.scope k)) b Q
unbind refl h = h

mutual
  husk-of : ∀ {Γ} {sc : Scope Γ} {Rg C A} {s : St Γ A} {E} → Sync sc Rg C s E → Σ Pts (Husk sc s)
  husk-of (s-cold _ _ _)            = _ , h-blank
  husk-of (s-of _ _)                = _ , h-blank
  husk-of (s-done _ _)              = _ , h-blank
  husk-of (s-map sy _ _)            = _ , h-map (proj₂ (husk-of sy))
  husk-of (s-scan sy _ _ _)         = _ , h-scan (proj₂ (husk-of sy))
  husk-of (s-cut sy)                = _ , h-cut (proj₂ (husk-of sy))
  husk-of (s-take sy _ _ _)         = _ , h-take (proj₂ (husk-of sy))
  husk-of (s-took _ _ _ _ _ hk _ _) = _ , h-take hk
  husk-of (s-flat _ sy (joined bg _ _ _ _ _ _ _) _ _ _) = _ , h-flat (proj₂ (husk-of sy)) (proj₂ (begun-husk bg))
  husk-of (s-conn {k = k} sc pt bs ss tn _ _) =
    by (CS.srcLive k) (λ l → _ , h-conn (proj₂ (src-husk sc (ss l) (Parts.ss pt))) (unbind {k = k} sc (proj₂ (husk-of (bs l)))))
                      (λ nl → _ , h-conn (Torn.sh (tn nl)) (Torn.bh (tn nl)))
  husk-of (s-join _ _ _ _ _)        = _ , h-blank
  husk-of (s-joinx _ _)             = _ , h-blank

  src-husk : ∀ {Γ X} {sc : Scope Γ} {Rg C} {k : CS Γ X} {o} → CS.scope k ≡ sc → Src sc Rg C k o → Sound Rg (Frozen k) → Σ Pts (SrcH sc k o)
  src-husk sc (src-pend na nc ba adm pe wn _) ss       = _ , sh-pend na nc ba sc adm pe wn ss
  src-husk _ (src-on {k = k} nc sy bh sd _ ao) ss       = by (CS.srcAtt k) (λ _ → _ , sh-dead (proj₂ (husk-of sy))) (λ na → _ , sh-isle na nc sy bh sd ss (ao na))
  src-husk _ (src-shut {C = C} {k = k} cl sp tp hk bh sd) _ = by (CS.srcAtt k) (λ _ → _ , sh-dead hk) (λ na → _ , sh-islec {Ci = C} na cl sp tp hk bh sd)

  begun-husk : ∀ {Γ A B} {sc : Scope Γ} {Rl C} {P : Pol A B} {O vs ls n} → Begun sc Rl C P O vs ls n → Σ Pts (HuskL sc ls)
  begun-husk none               = _ , hl-none
  begun-husk (more _ _ _ ln bg) = _ , hl-more (proj₂ (lane-husk ln)) (proj₂ (begun-husk bg))

  lane-husk : ∀ {Γ A B} {sc : Scope Γ} {Rg C} {P : Pol A B} {q a l b} → LaneSt sc Rg C P q a l b → Σ Pts (Husk sc l)
  lane-husk (l-live _ sy _) = _ , h-ln (h-cut (proj₂ (husk-of sy)))
  lane-husk (l-dead _ hk)   = _ , h-ln (h-cut hk)

-- One node's state in from what still runs around it.
peel-take : ∀ {Γ} {sc : Scope Γ} {A} {i} {keep : A → Bool} {w s Q} → Husk sc (takeS i keep w s) Q → Σ Pts λ Q′ → Husk sc s Q′ × Q ⊑ Q′
peel-take h-blank     = _ , h-blank , ⊑-refl
peel-take (h-take hk) = _ , hk , ⊑-refl

peel-cut : ∀ {Γ} {sc : Scope Γ} {A} {l a} {s : St Γ A} {Q} → Husk sc (cutS l a s) Q → Σ Pts λ Q′ → Husk sc s Q′ × Q ⊑ Q′
peel-cut h-blank    = _ , h-blank , ⊑-refl
peel-cut (h-cut hk) = _ , hk , ⊑-refl

-- UNSUBSCRIBING keeps every isle: it never reaches a source in its
-- subscribe call.
-- An unsubscribe its flag withholds.
unsubIf-off : ∀ {Γ A} b {s : St Γ A} → T (not b) → proj₁ (unsubIf b s) ≡ s
unsubIf-off false _ = refl

mutual
  unsub-husk : ∀ {Γ} {sc : Scope Γ} {A} {s : St Γ A} {P} → Husk sc s P → Σ Pts λ P′ → Husk sc (proj₁ (unsub s)) P′ × P ⊑ P′
  unsub-husk h-blank        = _ , h-blank , ⊑-refl
  unsub-husk (h-map hk)     = let (_ , h , le) = unsub-husk hk in _ , h-map h , le
  unsub-husk (h-scan hk)    = let (_ , h , le) = unsub-husk hk in _ , h-scan h , le
  unsub-husk (h-cut hk)     = _ , h-cut hk , ⊑-refl
  unsub-husk (h-ln hk)      = _ , h-ln hk , ⊑-refl
  unsub-husk (h-take hk)    = let (_ , h , le) = cut-husk hk in _ , h-take h , le
  unsub-husk (h-flat ho hl) = let (_ , h , le) = cut-husk ho ; (_ , g , le′) = kill-husk hl in _ , h-flat h g , ∪-⊑ le le′
  unsub-husk (h-conn sh bh) = let (_ , h , le) = srch-unsub sh ; (_ , g , le′) = unsub-husk bh in _ , h-conn h g , ∪-⊑ le le′

  cut-husk : ∀ {Γ} {sc : Scope Γ} {A} {s : St Γ A} {P} → Husk sc s P → Σ Pts λ P′ → Husk sc (proj₁ (cut s)) P′ × P ⊑ P′
  cut-husk h-blank                   = _ , h-blank , ⊑-refl
  cut-husk (h-cut {a = attached} hk) = let (_ , h , le) = unsub-husk hk in _ , h-cut h , le
  cut-husk (h-cut {a = attAt _} hk)  = _ , h-cut hk , ⊑-refl
  cut-husk hk@(h-map _)              = _ , hk , ⊑-refl
  cut-husk hk@(h-scan _)             = _ , hk , ⊑-refl
  cut-husk hk@(h-ln _)               = _ , hk , ⊑-refl
  cut-husk hk@(h-take _)             = _ , hk , ⊑-refl
  cut-husk hk@(h-flat _ _)           = _ , hk , ⊑-refl
  cut-husk hk@(h-conn _ _)           = _ , hk , ⊑-refl

  kill-husk : ∀ {Γ} {sc : Scope Γ} {A} {ls : List (St Γ A)} {P} → HuskL sc ls P → Σ Pts λ P′ → HuskL sc (proj₁ (killAll ls)) P′ × P ⊑ P′
  kill-husk hl-none                          = _ , hl-none , ⊑-refl
  kill-husk (hl-more {l = l} h-blank hl)     = kill-blank l hl
  kill-husk (hl-more (h-ln {b = true} hk) hl) = let (_ , h , le) = cut-husk hk ; (_ , g , le′) = kill-husk hl in _ , hl-more (h-ln h) g , ∪-⊑ le le′
  kill-husk (hl-more hk@(h-ln {b = false} _) hl) = kill-keep hk hl
  kill-husk (hl-more hk@(h-map _) hl)        = kill-keep hk hl
  kill-husk (hl-more hk@(h-scan _) hl)       = kill-keep hk hl
  kill-husk (hl-more hk@(h-cut _) hl)        = kill-keep hk hl
  kill-husk (hl-more hk@(h-take _) hl)       = kill-keep hk hl
  kill-husk (hl-more hk@(h-flat _ _) hl)     = kill-keep hk hl
  kill-husk (hl-more hk@(h-conn _ _) hl)     = kill-keep hk hl

  -- A list entry no kill reaches, kept.
  kill-keep : ∀ {Γ} {sc : Scope Γ} {A} {l : St Γ A} {ls P Q} → Husk sc l P → HuskL sc ls Q
            → Σ Pts λ P′ → HuskL sc (l ∷ proj₁ (killAll ls)) P′ × (P ∪ᵖ Q) ⊑ P′
  kill-keep hk hl = let (_ , g , le) = kill-husk hl in _ , hl-more hk g , ∪-⊑ ⊑-refl le

  kill-blank : ∀ {Γ} {sc : Scope Γ} {A} (l : St Γ A) {ls Q} → HuskL sc ls Q
             → Σ Pts λ P′ → HuskL sc (proj₁ (killAll (l ∷ ls))) P′ × (∅ᵖ ∪ᵖ Q) ⊑ P′
  kill-blank (lnS true _)        hl = let (_ , g , le) = kill-husk hl in _ , hl-more h-blank g , ∪-⊑ ⊑-refl le
  kill-blank (lnS false _)       hl = kill-keep h-blank hl
  kill-blank (pend _ _)          hl = kill-keep h-blank hl
  kill-blank (coldS _ _)         hl = kill-keep h-blank hl
  kill-blank (ofS _ _ _)         hl = kill-keep h-blank hl
  kill-blank doneS               hl = kill-keep h-blank hl
  kill-blank (mapS _ _)          hl = kill-keep h-blank hl
  kill-blank (scanS _ _ _)       hl = kill-keep h-blank hl
  kill-blank (cutS _ _ _)        hl = kill-keep h-blank hl
  kill-blank (takeS _ _ _ _)     hl = kill-keep h-blank hl
  kill-blank (flatS _ _ _ _ _ _ _ _) hl = kill-keep h-blank hl
  kill-blank (connS _ _ _)       hl = kill-keep h-blank hl
  kill-blank (joinS _ _ _ _)     hl = kill-keep h-blank hl

  srch-unsub : ∀ {Γ X} {sc : Scope Γ} {k : CS Γ X} {o P} → SrcH sc k o P
             → Σ Pts λ P′ → SrcH sc k (proj₁ (unsubIf (CS.srcAtt k) o)) P′ × P ⊑ P′
  srch-unsub {k = k} (sh-dead hk) with CS.srcAtt k
  ... | true  = let (_ , h , le) = unsub-husk hk in _ , sh-dead h , under-⊑ le
  ... | false = _ , sh-dead hk , ⊑-refl
  srch-unsub {k = k} sh@(sh-isle na _ _ _ _ _ _)  = _ , subst (λ o′ → SrcH _ k o′ _) (sym (unsubIf-off (CS.srcAtt k) na)) sh , ⊑-refl
  srch-unsub {k = k} sh@(sh-islec na _ _ _ _ _ _) = _ , subst (λ o′ → SrcH _ k o′ _) (sym (unsubIf-off (CS.srcAtt k) na)) sh , ⊑-refl
  srch-unsub {k = k} sh@(sh-pend na _ _ _ _ _ _ _) = _ , subst (λ o′ → SrcH _ k o′ _) (sym (unsubIf-off (CS.srcAtt k) na)) sh , ⊑-refl

unsubIf-husk : ∀ {Γ} {sc : Scope Γ} {A} {s : St Γ A} {P} b → Husk sc s P → Σ Pts λ P′ → Husk sc (proj₁ (unsubIf b s)) P′ × P ⊑ P′
unsubIf-husk true  hk = unsub-husk hk
unsubIf-husk false hk = _ , hk , ⊑-refl

------------------------------------------------------------------------
-- NO ISLE IN A PART: every connect in it attached, closed, or not yet
-- subscribed.  An isle's subscribe call is still running, so whatever
-- runs lies inside its source: a connect whose source rises has no isle
-- in its body, and a row fed there reaches none.

isPend : ∀ {Γ A} → St Γ A → Bool
isPend (pend _ _) = true
isPend _          = false

Pending : ∀ {Γ A} → St Γ A → Set
Pending s = T (isPend s)

-- A pending subscription by its shape.
pend-shape : ∀ {Γ A} (s : St Γ A) → Pending s → Σ (Obs Timeline Γ A) λ o → Σ Pos λ q → s ≡ pend o q
pend-shape (pend o q) _ = o , q , refl
pend-shape (coldS _ _) ()
pend-shape (ofS _ _ _) ()
pend-shape doneS ()
pend-shape (mapS _ _) ()
pend-shape (scanS _ _ _) ()
pend-shape (cutS _ _ _) ()
pend-shape (lnS _ _) ()
pend-shape (takeS _ _ _ _) ()
pend-shape (flatS _ _ _ _ _ _ _ _) ()
pend-shape (connS _ _ _) ()
pend-shape (joinS _ _ _ _) ()

-- Not an isle.
Settles : ∀ {Γ X} → CS Γ X → St Γ X → Set
Settles k o = T (CS.srcAtt k) ⊎ T (CS.closed k) ⊎ Pending o

mutual
  NoIsle : ∀ {Γ A} → St Γ A → Set
  NoIsle (mapS _ s)                = NoIsle s
  NoIsle (scanS _ _ s)             = NoIsle s
  NoIsle (cutS _ _ s)              = NoIsle s
  NoIsle (lnS _ s)                 = NoIsle s
  NoIsle (takeS _ _ _ s)           = NoIsle s
  NoIsle (flatS _ _ _ _ _ _ o ls)  = NoIsle o × NoIsleL ls
  NoIsle (connS k o b)             = Settles k o × NoIsle o × NoIsle b
  NoIsle _                         = ⊤

  NoIsleL : ∀ {Γ A} → List (St Γ A) → Set
  NoIsleL []       = ⊤
  NoIsleL (l ∷ ls) = NoIsle l × NoIsleL ls

-- The path clear: no isle in the body of a connect whose source it
-- enters.
Clear : ∀ {R Γ A} → Ctx R Γ A → Set
Clear top                                 = ⊤
Clear (inMap _ c)                         = Clear c
Clear (inScan _ _ c)                      = Clear c
Clear (inCut _ _ c)                       = Clear c
Clear (inLn _ c)                          = Clear c
Clear (inTake _ _ _ c)                    = Clear c
Clear (inOuter _ _ _ _ _ _ _ c)           = Clear c
Clear (inLanes _ _ _ _ _ _ _ _ _ c)       = Clear c
Clear (inSrc _ b c)                       = NoIsle b × Clear c
Clear (inBody _ _ c)                      = Clear c

-- A node in step is no pending subscription.
sync-pend : ∀ {Γ} {sc : Scope Γ} {Rg C A} {s : St Γ A} {E} → Pending s → Sync sc Rg C s E → ⊥
sync-pend {s = s} p sy with pend-shape s p
... | _ , _ , refl with sy
...   | ()

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
Hold {Γ} sc Rg C (pnd q) {A} s E = Σ (Obs Timeline Γ A) λ o → s ≡ pend o q × pendRows (full sc) o q ≈ E × Within Rg sc q

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
            → LanesIn (JRl (scopeOf c) Rg op f O) (polF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) O) O
            → JoinE (scopeOf c) op f ω O E′ → Sound (JRo (scopeOf c) Rg op f O) O → (T b → Sound (JRl (scopeOf c) Rg op f O q) E)
            → Behind C (JoinF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) O)
            → Fr Cr C (JRl (scopeOf c) Rg op f O q) (inLanes op f ω d n qu o pre post c) (lane b Ph) E
    -- under a lane's list entry, its switch; under that, its program
    f-lane  : ∀ {Γ A} {c : Ctx R Γ A} {C Rg b P E} → Fr Cr C Rg c (lane b P) E → Fr Cr C Rg (inLn b c) (lanecut b P) E
    f-lnct  : ∀ {Γ A} {a} {c : Ctx R Γ A} {C Rg b P E} → Fr Cr C Rg c (lanecut b P) E → Fr Cr C Rg (inCut b a c) (onoff b P) E
    f-src   : ∀ {Γ X B} {k : CS Γ X} {b} {c : Ctx R Γ B} {C Rg E E′ β}
            → Fr Cr C Rg c owes E′ → CS.scope k ≡ scopeOf c → (pt : Parts (scopeOf c) Rg k β) → T (CS.srcLive k) → T (not (CS.closed k))
            → Sync (binds (CS.src k) (CS.connAt k) (scopeOf c)) (Parts.Rb pt) C b β
            → Flags C k β → Frozen k ≈ E → ConnE (CS.connAt k) (Frozen k) β E′ → Behind C (Frozen k) → Subd (scopeOf c) C k
            → AttFin k → (T (not (CS.srcAtt k)) → AttOwed k) → NoIsle b → Fr Cr C (Parts.Rs pt) (inSrc k b c) owes E
    -- a source ended while its connect runs: nothing reads what is left
    f-srcc  : ∀ {Γ X B} {k : CS Γ X} {b} {c : Ctx R Γ B} {C Rg Rg′ E E′ β P}
            → Fr Cr C Rg c owes E′ → CS.scope k ≡ scopeOf c → (pt : Parts (scopeOf c) Rg k β) → T (CS.srcLive k) → T (CS.closed k)
            → Spent C (Frozen k) → TailP C (Frozen k) P → Behind C (Frozen k) → Subd (scopeOf c) C k
            → Sync (binds (CS.src k) (CS.connAt k) (scopeOf c)) (Parts.Rb pt) C b β
            → Flags C k β → ConnE (CS.connAt k) (Frozen k) β E′
            → Fr Cr C Rg′ (inSrc k b c) (dead P) E
    -- a source being subscribed: its program, owed at the connect's
    -- `ix 1`; its body's burst over, so the cursor is past it and the
    -- body holds no isle
    f-srcp  : ∀ {Γ X B} {k : CS Γ X} {b} {c : Ctx R Γ B} {C Rg E E′ β}
            → Fr Cr C Rg c owes E′ → CS.scope k ≡ scopeOf c → (pt : Parts (scopeOf c) Rg k β) → T (CS.srcLive k) → T (not (CS.closed k))
            → T (not (CS.srcAtt k)) → CS.bodyAt k ≡ just (CS.connAt k) → Adm (binds (CS.src k) (CS.connAt k) (scopeOf c))
            → Sync (binds (CS.src k) (CS.connAt k) (scopeOf c)) (Parts.Rb pt) C b β
            → Flags C k β → Frozen k ≈ E → ConnE (CS.connAt k) (Frozen k) β E′
            → Owes C (CS.connAt k ++ [ ix 1 ]) → Subd (scopeOf c) C k → NoIsle b
            → Fr Cr C (Parts.Rs pt) (inSrc k b c) (pnd (CS.connAt k ++ [ ix 1 ])) E
    -- a body while its source runs
    f-body  : ∀ {Γ X B} {k : CS Γ X} {o} {c : Ctx R Γ B} {C Rg E E′}
            → Fr Cr C Rg c owes E′ → CS.scope k ≡ scopeOf c → (pt : Parts (scopeOf c) Rg k E) → T (CS.srcLive k)
            → Src (scopeOf c) (Parts.Rs pt) C k o → Flags C k E → ConnE (CS.connAt k) (Frozen k) E E′
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
            → P ⊑ (Under N ∪ᵖ Qb) → NoIsle b → Fr Cr C Rg′ (inSrc k b c) (dead N) E
    d-body  : ∀ {Γ X B} {k : CS Γ X} {o} {c : Ctx R Γ B} {C Rg′ P N Ps E}
            → Unread Cr C c k P → SrcH (scopeOf c) k o Ps
            → P ⊑ (Ps ∪ᵖ N) → Fr Cr C Rg′ (inBody k o c) (dead N) E
    -- an isle: its source in step at its own cursor
    f-isle  : ∀ {Γ X B} {k : CS Γ X} {b : St (X ∷ Γ) B} {c : Ctx R Γ B} {C Ri Ci P Qb}
            → Unread Cr C c k P → Husk (binds (CS.src k) (CS.connAt k) (CS.scope k)) b Qb
            → P ⊑ (Burst k ∪ᵖ Qb) → T (not (CS.srcAtt k)) → T (not (CS.closed k))
            → Behind Ci (Frozen k) → Subd (scopeOf c) Ci k → Sound Ri (Frozen k) → AttOwed k
            → NoIsle b → Fr Cr Ci Ri (inSrc k b c) owes (Frozen k)
    -- an isle whose source has ended
    f-islec : ∀ {Γ X B} {k : CS Γ X} {b : St (X ∷ Γ) B} {c : Ctx R Γ B} {C Ci Rg′ P N Qb E}
            → Unread Cr C c k P → Husk (binds (CS.src k) (CS.connAt k) (CS.scope k)) b Qb
            → P ⊑ (Burst k ∪ᵖ Qb) → T (not (CS.srcAtt k)) → T (CS.closed k)
            → Spent Ci (Frozen k) → TailP Ci (Frozen k) N → Behind Ci (Frozen k) → Subd (scopeOf c) Ci k
            → Fr Cr C Rg′ (inSrc k b c) (dead N) E
    -- an isle's source not yet subscribed: its cursor at where it will be
    f-islep : ∀ {Γ X B} {k : CS Γ X} {b : St (X ∷ Γ) B} {c : Ctx R Γ B} {C Ri P Qb}
            → Unread Cr C c k P → Husk (binds (CS.src k) (CS.connAt k) (CS.scope k)) b Qb
            → P ⊑ (Burst k ∪ᵖ Qb) → T (not (CS.srcAtt k)) → T (not (CS.closed k)) → CS.bodyAt k ≡ just (CS.connAt k)
            → CS.scope k ≡ scopeOf c → Adm (binds (CS.src k) (CS.connAt k) (scopeOf c)) → Sound Ri (Frozen k) → NoIsle b
            → Fr Cr (bef (CS.connAt k ++ [ ix 1 ])) Ri (inSrc k b c) (pnd (CS.connAt k ++ [ ix 1 ])) (Frozen k)
