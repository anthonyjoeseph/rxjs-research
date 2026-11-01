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
-- entry and the cursor.  Entries are tied by `_≈_`, visible rows alike:
-- a defer's guard and a joiner's echoes are skips no reader meets.
--
-- A rise in flight splits the cursor: the focus's subtree has delivered
-- the row (`aft p`), every other node has not seen it (`bef p`).  The
-- frames the rise climbs read their hole at `bef p`, and the hole's entry
-- holds the row in flight there.
--
-- A subtree no live node reads — under a failed takeWhile, a torn
-- source, an ended or killed lane — owes nothing: its frames are `false`
-- and nothing ties its nodes to an entry.
--
-- A joiner never reads its source's state: its source's frozen entry,
-- past the cursor, is what is still to feed it.
module adequacy.Cursor where

open import Data.Bool using (Bool; T; true; false; not; _∧_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_; reverse; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Data.List.Relation.Unary.All using (lookup)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; suc; _+_; _≤_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; sym)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Events using (Pos; Timeline; ix; last; ofᴱ; tick)
open import denotation.Read using (Visible)
open import denotation.EmissionSet using (EmissionSet; out; end; _≺_; _≼_; enter; ⟦_⟧; Den; hot; coldAt; Rejoin; InE;
  MapT; map-out; map-end; LaneOf; module Scan; module TakeWhile; module Connecting;
  module Merge; module Bounded; module Switch; module Exhaust)
open import operation.PureObservable using (module Machine; Tape; play; ending) renaming (over to tapeOver)
open Machine using (St; Ctx; Conf; ⟨_,_,_,_⟩; Scope; unbound; binds; CS; Owe; free; cpAt; cutAt; overAt; scopeOf;
                    Att; attached; attAt; subscribing; absorbed; rising; mapEv; nx; cp;
                    pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
                    top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody)
                    renaming (Ev to Evᴹ; Shown to Shownᴹ)
open import denotation.Laws.Modulus using (≼-refl; ≺→≼; ≺-absurd; ≺-ext; ≺-irrefl; ≼-or-≻)
open import adequacy.Rows using (≼-≢; _≃_; _⇄_; ≃-refl; Vis; Moves; silent; shown; toEv; Inbox; full; pendRows; Frozen; tapeE)
open import denotation.Laws.Worlds using (Ok; Hots; Real)
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

-- Alike in every row a reader meets.
_≈_ : ∀ {A} → EmissionSet A → EmissionSet A → Set
E ≈ E′ = Vis E ≃ Vis E′

-- The engine's events are all visible.
vis : ∀ {A} (e : Evᴹ A) → Visible (toEv e)
vis (nx _) = _
vis cp     = _

-- A frozen entry is a meaning: one visible row at a position.
record Sound {A} (E : EmissionSet A) : Set where
  field
    fn : ∀ {y e e′} → E y e → E y e′ → Visible e → Visible e′ → e ≡ e′

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

-- A begun lane as its joiner reads it: running from where it was
-- subscribed, its entry its lane's; or over, by its end or a later value.
data Hole {A B} (C : Cur) (P : Pol A B) (q : Pos) (a : A) : EmissionSet B → Bool → Set₁ where
  h-live : ∀ {s E} → Start P q a s → ¬ Owes C s → Lane P q a ≈ E → Hole C P q a E true
  h-end  : ∀ {c E} → Lane P q a c end → ¬ Owes C c → Hole C P q a E false
  h-kill : ∀ {q′ E} → Kill P q q′ → ¬ Owes C q′ → Hole C P q a E false

bump : Bool → ℕ → ℕ
bump true  n = suc n
bump false n = n

-- Every connect of a scope subscribed where admissible: what makes each
-- of its handles a lawful hot, whose rows lie none below another.
Adm : ∀ {Γ} → Scope Γ → Set
Adm unbound        = ⊤
Adm (binds o p sc) = Ok (Hots (full sc)) p × Adm sc

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

data Sync : ∀ {Γ} → Scope Γ → Cur → ∀ {A} → St Γ A → EmissionSet A → Set₁

-- A lane in its joiner's list, live or over: its list entry over its
-- switch, both on while it runs and both off once it is over.
data LaneSt {Γ A B} (sc : Scope Γ) (C : Cur) (P : Pol A B) (q : Pos) (a : A) : St Γ B → Bool → Set₁ where
  l-live : ∀ {at l E} → Hole C P q a E true → Sync sc C l E → Sound E → LaneSt sc C P q a (lnS true (cutS true at l)) true
  l-dead : ∀ {at l E} → Hole C P q a E false → LaneSt sc C P q a (lnS false (cutS false at l)) false

-- The values passed that began a lane, oldest first, and how many of
-- their lanes run.
data Begun {Γ A B} (sc : Scope Γ) (C : Cur) (P : Pol A B) (O : EmissionSet A) : List (Pos × A) → List (St Γ B) → ℕ → Set₁ where
  none : Begun sc C P O [] [] 0
  more : ∀ {q a l b vs ls n} → O q (out a) → ¬ Owes C q → Runs P q → LaneSt sc C P q a l b
       → Begun sc C P O vs ls n → Begun sc C P O ((q , a) ∷ vs) (l ∷ ls) (bump b n)

-- A joiner's bookkeeping: its begun lanes and live count, its queue, and
-- its outer's end.
data Joined {Γ A B} (sc : Scope Γ) (C : Cur) (P : Pol A B) (O : EmissionSet A) (d : Bool) (n : ℕ) (qu : List A)
            (ls : List (St Γ B)) : Set₁ where
  joined : ∀ {vs ws} → Begun sc C P O vs ls n → Waiting C P O ws qu → Whole C P O vs ws → OuterDone C O d
         → Ahead C P vs ws → Ends P O
         → Joined sc C P O d n qu ls

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

-- A connect's source: running, its frozen entry what it owes; or not yet
-- subscribed, which its body's own mark does at the connect's `ix 1`.
data Src : ∀ {Γ X} → Scope Γ → Cur → CS Γ X → St Γ X → Set₁

data Sync where
  -- a started cold: what its tape has left is what its entry owes
  s-cold : ∀ {Γ} {sc : Scope Γ} {C} {A} {l} {E : EmissionSet A}
         → Ticked l → Due C E ≃ Due origin (InE (tapeE l)) → Sync sc C (coldS true l) E
  -- an of: what it has left is what its entry owes
  s-of   : ∀ {Γ} {sc : Scope Γ} {C} {A} {i q} {xs : List A} {E}
         → Due C E ≃ Due origin (InE (ofᴱ q i xs)) → Sync sc C (ofS i q xs) E
  s-done : ∀ {Γ} {sc : Scope Γ} {C} {A} {E : EmissionSet A} → Spent C E → Sync sc C doneS E
  s-map  : ∀ {Γ} {sc : Scope Γ} {C} {A B} {f : A → B} {s E E′} → Sync sc C s E → MapT f E ≈ E′ → Sound E → Sync sc C (mapS f s) E′
  -- a scan: its fold of the values passed
  s-scan : ∀ {Γ} {sc : Scope Γ} {C} {A B} {f : B → A → B} {z z₀ s Es E}
         → Sync sc C s Es → Folded C f z₀ Es z → Scan.ScanT f z₀ Es ≈ E → Sound Es → Sync sc C (scanS f z s) E
  s-cut  : ∀ {Γ} {sc : Scope Γ} {C} {A} {a : Att} {s : St Γ A} {E} → Sync sc C s E → Sync sc C (cutS true a s) E
  -- a takeWhile not yet failed: no failing value passed
  s-take : ∀ {Γ} {sc : Scope Γ} {C} {A} {i} {keep : A → Bool} {s Es E}
         → Sync sc C s Es → NoFail C keep Es
         → TakeWhile.TakeT i keep Es ≈ E → Sound Es → Sync sc C (takeS i keep free s) E
  -- failed at `r`: its source is not read again
  s-took : ∀ {Γ} {sc : Scope Γ} {C} {A} {i} {keep : A → Bool} {w s Es E r}
         → Failure keep Es r → ¬ Owes C r → (T i → ¬ Owes C (r ++ [ ix 0 ])) → OweAt C w r
         → TakeWhile.TakeT i keep Es ≈ E → Sync sc C (takeS i keep w s) E
  -- a joiner: its outer, and its bookkeeping over its policy
  s-flat : ∀ {Γ} {sc : Scope Γ} {C} {A B} {op} {f : A → Obs Timeline Γ B} {d n qu o ls O E}
         → Sync sc C o O → Joined sc C (polF op (λ a → ⟦ f a ⟧ (full sc)) O) O d n qu ls
         → JoinF op (λ a → ⟦ f a ⟧ (full sc)) O ≈ E → Sound O
         → Sync sc C (flatS op f d n qu o ls) E
  -- a connect: its body, under its binder read whole, and its source,
  -- while the source runs; torn down, its body owes nothing and nothing
  -- reads either
  s-conn : ∀ {Γ} {sc : Scope Γ} {C} {X B} {k : CS Γ X} {o : St Γ X} {b : St (X ∷ Γ) B} {β : EmissionSet B} {E}
         → CS.scope k ≡ sc
         → (T (CS.srcLive k) → Sync (binds (CS.src k) (CS.connAt k) sc) C b β)
         → (T (CS.srcLive k) → Src sc C k o)
         → Flags C k β
         → Connecting.ConnT (CS.connAt k) (Frozen k) β ≈ E → Sound β
         → Sync sc C (connS k o b) E
  -- a joiner: what it was fed and has not shown, and what is still to
  -- feed it.  The engine shows its inbox's head and appends in its
  -- source's order, while the entry orders rows by their rejoined
  -- position, so the inbox is ascending and ahead of all still unfed.
  s-join : ∀ {Γ} {sc : Scope Γ} {C} {A} {j} {x : A ∈ Γ} {ib E}
         → enter (lookup (full sc) x) j ≈ E
         → Due C E ≃ (λ q e → Inbox ib q e ⊎ Due C (Unfed C (lookup (full sc) x) j) q e)
         → AllPairs (λ u v → proj₁ u ≺ proj₁ v) ib
         → (∀ {u q e} → u ∈ ib → Due C (Unfed C (lookup (full sc) x) j) q e → proj₁ u ≺ q)
         → Adm sc
         → Sync sc C (joinS j true x ib) E
  s-joinx : ∀ {Γ} {sc : Scope Γ} {C} {A} {j} {x : A ∈ Γ} {ib E} → Spent C E → Sync sc C (joinS j false x ib) E

data Src where
  src-pend : ∀ {Γ X} {sc : Scope Γ} {C} {k : CS Γ X} {o}
           → CS.bodyAt k ≡ just (CS.connAt k) → Adm (binds (CS.src k) (CS.connAt k) sc)
           → pendRows (full sc) o (CS.connAt k ++ [ ix 1 ]) ≈ Frozen k
           → Src sc C k (pend o (CS.connAt k ++ [ ix 1 ]))
  src-on   : ∀ {Γ X} {sc : Scope Γ} {C} {k : CS Γ X} {o} → T (not (CS.closed k)) → Sync sc C o (Frozen k) → Src sc C k o
  -- ended: nothing left to owe, whatever its subtree still holds
  src-shut : ∀ {Γ X} {sc : Scope Γ} {C} {k : CS Γ X} {o} → T (CS.closed k) → Spent C (Frozen k) → Src sc C k o

-- No rise in flight.
data Calm {A : Set} : Machine.Mode A → Set where
  c-sub : Calm subscribing
  c-abs : Calm absorbed

------------------------------------------------------------------------
-- THE FRAMES ABOVE A HOLE: the hole's entry `E`, composed up to the
-- root's, every other part in step.  What the hole itself owes is its
-- `Need`: its entry, nothing (a subtree no live node reads), or a lane's
-- shape — the joiner's list entry and the switch under it, both on or
-- both off — which the joiner reads off the lane's state.

data Need : Set where
  owes    : Bool → Need
  lane    : Bool → Need
  lanecut : Bool → Need
  pnd     : Pos → Need

-- The hole's state against its need.
Hold : ∀ {Γ} → Scope Γ → Cur → Need → ∀ {A} → St Γ A → EmissionSet A → Set₁
Hold sc C (owes w)    s E = T w → Sync sc C s E
Hold sc C (lane b)    s E = Σ Att λ at → Σ (St _ _) λ l → s ≡ lnS b (cutS b at l) × (T b → Sync sc C l E)
Hold sc C (lanecut b) s E = Σ Att λ at → Σ (St _ _) λ l → s ≡ cutS b at l × (T b → Sync sc C l E)
Hold {Γ} sc C (pnd q) {A} s E = Σ (Obs Timeline Γ A) λ o → s ≡ pend o q × pendRows (full sc) o q ≈ E

-- A rise in flight at `p` from the hole: delivered there, its row in the
-- hole's entry.
Fly : ∀ {Γ} → Scope Γ → Pos → Need → ∀ {A} → St Γ A → EmissionSet A → Evᴹ A → Set₁
Fly sc p (owes w)    s E e = T w → Sync sc (aft p) s E × E p (toEv e)
Fly sc p (lane b)    s E e = Σ Att λ at → Σ (St _ _) λ l → s ≡ lnS b (cutS b at l) × (T b → Sync sc (aft p) l E × E p (toEv e))
Fly sc p (lanecut b) s E e = Σ Att λ at → Σ (St _ _) λ l → s ≡ cutS b at l × (T b → Sync sc (aft p) l E × E p (toEv e))
Fly {Γ} sc p (pnd q) {A} s E e = Σ (Obs Timeline Γ A) λ o → s ≡ pend o q × ⊥

-- One frame inside another.
data Up1 {R : Set} : ∀ {Γ A Γ′ A′} → Ctx R Γ A → Ctx R Γ′ A′ → Set₁ where
  u-map   : ∀ {Γ A B} {f : A → B} {c : Ctx R Γ B} → Up1 (inMap f c) c
  u-scan  : ∀ {Γ A B} {f : B → A → B} {z} {c : Ctx R Γ B} → Up1 (inScan f z c) c
  u-cut   : ∀ {Γ A} {l a} {c : Ctx R Γ A} → Up1 (inCut l a c) c
  u-ln    : ∀ {Γ A} {b} {c : Ctx R Γ A} → Up1 (inLn b c) c
  u-take  : ∀ {Γ A} {i} {keep : A → Bool} {w} {c : Ctx R Γ A} → Up1 (inTake i keep w c) c
  u-outer : ∀ {Γ A B} {op} {f : A → Obs Timeline Γ B} {d n qu ls} {c : Ctx R Γ B} → Up1 (inOuter op f d n qu ls c) c
  u-lanes : ∀ {Γ A B} {op} {f : A → Obs Timeline Γ B} {d n qu} {o : St Γ A} {pre post} {c : Ctx R Γ B}
          → Up1 (inLanes op f d n qu o pre post c) c
  u-src   : ∀ {Γ X B} {k : CS Γ X} {b : St (X ∷ Γ) B} {c : Ctx R Γ B} → Up1 (inSrc k b c) c
  u-body  : ∀ {Γ X B} {k : CS Γ X} {o} {c : Ctx R Γ B} → Up1 (inBody k o c) c

module _ {R : Set} (Rt : EmissionSet R) where

  data Fr (C : Cur) : ∀ {Γ A} → Ctx R Γ A → Need → EmissionSet A → Set₁ where
    f-top   : ∀ {E} → E ≈ Rt → Fr C top (owes true) E
    -- inside a subtree no live node reads
    f-off   : ∀ {Γ A Γ′ A′} {c′ : Ctx R Γ A} {c : Ctx R Γ′ A′} {E E′} → Up1 c′ c → Fr C c (owes false) E′ → Fr C c′ (owes false) E
    f-map   : ∀ {Γ A B} {f : A → B} {c : Ctx R Γ B} {w E E′} → Fr C c (owes w) E′ → MapT f E ≈ E′ → Sound E → Fr C (inMap f c) (owes w) E
    f-scan  : ∀ {Γ A B} {f : B → A → B} {z z₀} {c : Ctx R Γ B} {w E E′}
            → Fr C c (owes w) E′ → Folded C f z₀ E z → Scan.ScanT f z₀ E ≈ E′ → Sound E → Fr C (inScan f z c) (owes w) E
    f-cut   : ∀ {Γ A} {a} {c : Ctx R Γ A} {w E} → Fr C c (owes w) E → Fr C (inCut true a c) (owes w) E
    f-take  : ∀ {Γ A} {i} {keep : A → Bool} {c : Ctx R Γ A} {w E E′}
            → Fr C c (owes w) E′ → NoFail C keep E → TakeWhile.TakeT i keep E ≈ E′ → Sound E → Fr C (inTake i keep free c) (owes w) E
    f-took  : ∀ {Γ A} {i} {keep : A → Bool} {o} {c : Ctx R Γ A} {w E Es E′ r}
            → Fr C c (owes w) E′ → Failure keep Es r → ¬ Owes C r → (T i → ¬ Owes C (r ++ [ ix 0 ])) → OweAt C o r
            → TakeWhile.TakeT i keep Es ≈ E′
            → Fr C (inTake i keep o c) (owes false) E
    f-outer : ∀ {Γ A B} {op} {f : A → Obs Timeline Γ B} {d n qu ls} {c : Ctx R Γ B} {w E E′}
            → Fr C c (owes w) E′
            → Joined (scopeOf c) C (polF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) E) E d n qu ls
            → JoinF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) E ≈ E′ → Sound E
            → Fr C (inOuter op f d n qu ls c) (owes w) E
    -- the hole a begun lane, between those before it and after it, in a
    -- joiner some live node reads
    f-lanes : ∀ {Γ A B} {op} {f : A → Obs Timeline Γ B} {d n qu} {o : St Γ A} {pre post} {c : Ctx R Γ B}
                {E E′ O vs₁ vs₂ ws n₁ n₂ q a b}
            → Fr C c (owes true) E′
            → Sync (scopeOf c) C o O
            → Begun (scopeOf c) C (polF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) O) O vs₁ (reverse pre) n₁
            → O q (out a) → ¬ Owes C q → Runs (polF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) O) q
            → Hole C (polF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) O) q a E b
            → Begun (scopeOf c) C (polF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) O) O vs₂ post n₂
            → n ≡ n₁ + bump b n₂
            → Waiting C (polF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) O) O ws qu
            → Whole C (polF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) O) O (vs₁ ++ (q , a) ∷ vs₂) ws
            → OuterDone C O d
            → Ahead C (polF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) O) (vs₁ ++ (q , a) ∷ vs₂) ws
            → Ends (polF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) O) O
            → JoinF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) O ≈ E′ → Sound O → (T b → Sound E)
            → Fr C (inLanes op f d n qu o pre post c) (lane b) E
    -- under a lane's list entry, its switch; under that, its program
    f-lane  : ∀ {Γ A} {c : Ctx R Γ A} {b E} → Fr C c (lane b) E → Fr C (inLn b c) (lanecut b) E
    f-lnct  : ∀ {Γ A} {a} {c : Ctx R Γ A} {b E} → Fr C c (lanecut b) E → Fr C (inCut b a c) (owes b) E
    f-src   : ∀ {Γ X B} {k : CS Γ X} {b} {c : Ctx R Γ B} {w E E′ β}
            → Fr C c (owes w) E′ → CS.scope k ≡ scopeOf c → T (CS.srcLive k) → T (not (CS.closed k))
            → Sync (binds (CS.src k) (CS.connAt k) (scopeOf c)) C b β
            → Flags C k β → Frozen k ≈ E → Connecting.ConnT (CS.connAt k) (Frozen k) β ≈ E′ → Sound β
            → Fr C (inSrc k b c) (owes w) E
    -- a source ended while its connect runs: nothing reads what is left
    f-srcc  : ∀ {Γ X B} {k : CS Γ X} {b} {c : Ctx R Γ B} {w E E′ β}
            → Fr C c (owes w) E′ → CS.scope k ≡ scopeOf c → T (CS.srcLive k) → T (CS.closed k) → Spent C (Frozen k)
            → Sync (binds (CS.src k) (CS.connAt k) (scopeOf c)) C b β
            → Flags C k β → Connecting.ConnT (CS.connAt k) (Frozen k) β ≈ E′ → Sound β
            → Fr C (inSrc k b c) (owes false) E
    -- a source not yet subscribed: its program, owed at the connect's
    -- `ix 1`
    f-srcp  : ∀ {Γ X B} {k : CS Γ X} {b} {c : Ctx R Γ B} {w E E′ β}
            → Fr C c (owes w) E′ → CS.scope k ≡ scopeOf c → T (CS.srcLive k)
            → CS.bodyAt k ≡ just (CS.connAt k) → Adm (binds (CS.src k) (CS.connAt k) (scopeOf c))
            → Sync (binds (CS.src k) (CS.connAt k) (scopeOf c)) C b β
            → Flags C k β → Frozen k ≈ E → Connecting.ConnT (CS.connAt k) (Frozen k) β ≈ E′ → Sound β
            → Fr C (inSrc k b c) (pnd (CS.connAt k ++ [ ix 1 ])) E
    -- a source torn down: nothing reads it
    f-srcx  : ∀ {Γ X B} {k : CS Γ X} {b} {c : Ctx R Γ B} {w E E′ β}
            → Fr C c (owes w) E′ → CS.scope k ≡ scopeOf c → T (not (CS.srcLive k))
            → Flags C k β → Connecting.ConnT (CS.connAt k) (Frozen k) β ≈ E′ → Sound β
            → Fr C (inSrc k b c) (owes false) E
    -- a body: owed while its source runs
    f-body  : ∀ {Γ X B} {k : CS Γ X} {o} {c : Ctx R Γ B} {w v E E′}
            → Fr C c (owes w) E′ → CS.scope k ≡ scopeOf c → v ≡ (w ∧ CS.srcLive k)
            → (T (CS.srcLive k) → Src (scopeOf c) C k o)
            → Flags C k E
            → Connecting.ConnT (CS.connAt k) (Frozen k) E ≈ E′ → Sound E
            → Fr C (inBody k o c) (owes v) E

  -- THE INVARIANT: settled, the hole and every frame at one cursor; a
  -- subscription owed where the cursor has not passed, its program's
  -- entry; a rise in flight at `p`, its row in the hole's entry, delivered
  -- below and not yet seen above; or a rise in a subtree no live node
  -- reads, at any cursor, reaching nothing owed.
  data Inv : Cur → Conf R → Set₁ where
    settled : ∀ {Γ A} {c : Ctx R Γ A} {s m p C w E} → Calm m
            → Fr C c w E → Hold (scopeOf c) C w s E → Inv C ⟨ c , s , m , p ⟩
    pending : ∀ {Γ A} {c : Ctx R Γ A} {o q p C w E}
            → Fr C c (owes w) E
            → (T w → Owes C q × Ok (Hots (full (scopeOf c))) q × Adm (scopeOf c) × pendRows (full (scopeOf c)) o q ≈ E)
            → Inv C ⟨ c , pend o q , subscribing , p ⟩
    flying  : ∀ {Γ A} {c : Ctx R Γ A} {s e p w E}
            → Fr (bef p) c w E → Fly (scopeOf c) p w s E e
            → Inv (bef p) ⟨ c , s , rising e , p ⟩
    adrift  : ∀ {Γ A} {c : Ctx R Γ A} {s e p C E}
            → Fr C c (owes false) E → Inv C ⟨ c , s , rising e , p ⟩

  -- What the root owes: its entry past the cursor.
  RT : Cur → EmissionSet R
  RT C = Due C Rt

  -- A step: the invariant kept at some cursor, the rows moved.
  SimC : Conf R → Shownᴹ R → Conf R → Set₁
  SimC k sh k′ = ∀ {C} → Inv C k → Σ Cur λ C′ → Inv C′ k′ × Moves (RT C) sh (RT C′)

  -- The invariant kept at its cursor.
  keeps : ∀ {k k′} → (∀ {C} → Inv C k → Inv C k′) → SimC k [] k′
  keeps g {C} i = C , g i , silent ≃-refl

  ----------------------------------------------------------------------
  -- THE ROW SHOWN IS THE LEAST OWED, for free: a rise reaching the root
  -- at `p` is in the root's entry, and the cursor at `bef p` owes nothing
  -- before `p`.

  show-top : ∀ {s e p w E} → Fr (bef p) top (owes w) E → (T w → Sync unbound (aft p) s E × E p (toEv e))
           → Moves (RT (bef p)) [ (p , e) ] (RT (aft p))
  show-top {e = e} {p = p} (f-top eq) h with h _
  ... | _ , row = shown ((proj₁ (to eq (row , vis e)) , vis e , ≼-refl {p}) , vis e) (λ ((_ , _ , o) , _) → o) past
    where
      past : _
      past = (λ { (((x , v , _) , pq) , v′) → (x , v , pq) , v′ })
           ⇄ (λ { {q} ((x , v , pq) , v′) → ((x , v , ≺→≼ {p} {q} pq) , pq) , v′ })

  -- THE ROOT: the row shown, the cursor past it.
  rise-top : ∀ {s : St [] R} {e p} → SimC ⟨ top , s , rising e , p ⟩ [ (p , e) ] ⟨ top , s , absorbed , p ⟩
  rise-top {p = p} (flying fr@(f-top eq) h) = aft p , settled c-abs (f-top eq) (λ w → proj₁ (h w)) , show-top fr h
  rise-top (settled () _ _)
  rise-top (adrift (f-off () _))

  ----------------------------------------------------------------------
  -- FRAMES THAT ONLY PASS A RISE

  -- MAP: the hole's row mapped.
  rise-map : ∀ {Γ A B} {f : A → B} {c : Ctx R Γ B} {s e p}
           → SimC ⟨ inMap f c , s , rising e , p ⟩ [] ⟨ c , mapS f s , rising (mapEv f e) , p ⟩
  rise-map {f = f} {e = e} = keeps λ
    { (flying (f-map fr eq sd) h) → flying fr λ w → let (sy , row) = h w in s-map sy eq sd , proj₁ (to eq (mapped e row , vis (mapEv f e)))
    ; (flying (f-off u-map fr) h) → flying fr λ ()
    ; (adrift (f-map fr _ _))     → adrift fr
    ; (adrift (f-off u-map fr))   → adrift fr
    ; (settled () _ _) }
    where
      mapped : ∀ {E q} (e : Evᴹ _) → E q (toEv e) → MapT f E q (toEv (mapEv f e))
      mapped (nx a) r = map-out r
      mapped cp     r = map-end r

  -- A SCAN'S VALUE: the hole's value folded into the last fold, the
  -- fold's value at `p`.
  rise-scan-nx : ∀ {Γ A B} {f : B → A → B} {z} {c : Ctx R Γ B} {s a p}
               → SimC ⟨ inScan f z c , s , rising (nx a) , p ⟩ [] ⟨ c , scanS f (f z a) s , rising (nx (f z a)) , p ⟩
  rise-scan-nx {f = f} {z = z} {a = a} {p = p} = keeps λ
    { (flying (f-scan fr fd eq sd) h) → flying fr λ w → let (sy , row) = h w ; ac = folds fd row
                                                      in s-scan sy (fd-last ac (≺-irrefl {p}) (λ _ pk → pk)) eq sd , proj₁ (to eq (Scan.sval ac , _))
    ; (flying (f-off u-scan fr) h)    → flying fr λ ()
    ; (adrift (f-scan fr _ _ _))      → adrift fr
    ; (adrift (f-off u-scan fr))      → adrift fr
    ; (settled () _ _) }
    where
      folds : ∀ {z₀ E} → Folded (bef p) f z₀ E z → E p (out a) → Scan.Acc f z₀ E p (f z a)
      folds (fd-none ow) row = Scan.acc₀ row ow
      folds (fd-last {q = q} ac nq nx′) row with ≼-or-≻ p q
      ... | inj₁ pq = ⊥-elim (nq pq)
      ... | inj₂ qp = Scan.acc ac row qp λ r qk → nx′ r qk

  -- A SCAN'S END: the fold kept, no value of its source at the end's
  -- position.
  rise-scan-cp : ∀ {Γ A B} {f : B → A → B} {z} {c : Ctx R Γ B} {s p}
               → SimC ⟨ inScan f z c , s , rising cp , p ⟩ [] ⟨ c , scanS f z s , rising cp , p ⟩
  rise-scan-cp {f = f} {z = z} {p = p} = keeps λ
    { (flying (f-scan fr fd eq sd) h) → flying fr λ w → let (sy , row) = h w
                                                      in s-scan sy (past sd row fd) eq sd , proj₁ (to eq (Scan.send row , _))
    ; (flying (f-off u-scan fr) h)    → flying fr λ ()
    ; (adrift (f-scan fr _ _ _))      → adrift fr
    ; (adrift (f-off u-scan fr))      → adrift fr
    ; (settled () _ _) }
    where
      after : ∀ {E} → Sound E → E p end → ∀ {q a} → E q (out a) → p ≼ q → p ≺ q
      after sd row {q} y pq = ≼-≢ {p} {q} pq λ { refl → out≢end (Sound.fn sd y row _ _) }
        where
          out≢end : ∀ {A} {a : A} → out a ≡ end → ⊥
          out≢end ()
      past : ∀ {z₀ E} → Sound E → E p end → Folded (bef p) f z₀ E z → Folded (aft p) f z₀ E z
      past sd row (fd-none ow)        = fd-none λ y → after sd row y (ow y)
      past sd row (fd-last ac nq nx′) = fd-last ac (λ pq → nq (≺→≼ {p} pq)) λ y qk → after sd row y (nx′ y qk)

  -- A TAKEWHILE NOT YET FAILED: a value it keeps, or its source's end,
  -- passed on; no failing value shares the row's position.
  module _ {Γ A} {i} {keep : A → Bool} {c : Ctx R Γ A} {s p} where
    unfailed : ∀ {E} → NoFail (bef p) keep E → ¬ TakeWhile.Failed i keep E p
    unfailed {E} nf (q , _ , y , nk , qp) = nf {q} y nk qp

    nf-aft : ∀ {E e′} → Sound E → E p e′ → Visible e′ → (∀ {a′} → out a′ ≡ e′ → T (not (keep a′)) → ⊥)
           → NoFail (bef p) keep E → NoFail (aft p) keep E
    nf-aft sd row v ok nf {q} y nk = ≼-≢ {p} {q} (nf y nk) λ { refl → ok (Sound.fn sd y row _ v) nk }

    rise-take-pass : ∀ {a} → keep a ≡ true
                   → SimC ⟨ inTake i keep free c , s , rising (nx a) , p ⟩ [] ⟨ c , takeS i keep free s , rising (nx a) , p ⟩
    rise-take-pass {a} kt = keeps λ
      { (flying (f-take {E = E} fr nf eq sd) h) → flying fr λ w → let (sy , row) = h w
          in s-take sy (nf-aft sd row _ kept nf) eq sd , proj₁ (to eq (TakeWhile.pass row (subst T (sym kt) _) (unfailed {E} nf) , _))
      ; (flying (f-took _ _ _ _ () _) _)
      ; (flying (f-off u-take fr) h)      → flying fr λ ()
      ; (adrift (f-take fr _ _ _))        → adrift fr
      ; (adrift (f-took _ _ _ _ () _))
      ; (adrift (f-off u-take fr))        → adrift fr
      ; (settled () _ _) }
      where
        kept : ∀ {a′} → out a′ ≡ out a → T (not (keep a′)) → ⊥
        kept refl nk = subst (λ b → T (not b)) kt nk

    rise-take-cp : SimC ⟨ inTake i keep free c , s , rising cp , p ⟩ [] ⟨ c , takeS i keep free s , rising cp , p ⟩
    rise-take-cp = keeps λ
      { (flying (f-take {E = E} fr nf eq sd) h) → flying fr λ w → let (sy , row) = h w
          in s-take sy (nf-aft sd row _ (λ ()) nf) eq sd , proj₁ (to eq (TakeWhile.tend row (unfailed {E} nf) , _))
      ; (flying (f-took _ _ _ _ () _) _)
      ; (flying (f-off u-take fr) h)      → flying fr λ ()
      ; (adrift (f-take fr _ _ _))        → adrift fr
      ; (adrift (f-took _ _ _ _ () _))
      ; (adrift (f-off u-take fr))        → adrift fr
      ; (settled () _ _) }

  -- A LIVE CUT passes the row; one off absorbs it.
  rise-cut : ∀ {Γ A} {a} {c : Ctx R Γ A} {s e p}
           → SimC ⟨ inCut true a c , s , rising e , p ⟩ [] ⟨ c , cutS true a s , rising e , p ⟩
  rise-cut = keeps λ
    { (flying (f-cut fr) h)       → flying fr λ w → let (sy , row) = h w in s-cut sy , row
    ; (flying (f-lnct fr) h)      → flying fr (_ , _ , refl , h)
    ; (flying (f-off u-cut fr) h) → flying fr λ ()
    ; (adrift (f-cut fr))         → adrift fr
    ; (adrift (f-off u-cut fr))   → adrift fr
    ; (settled () _ _) }

  rise-cutx : ∀ {Γ A} {a} {c : Ctx R Γ A} {s e p}
            → SimC ⟨ inCut false a c , s , rising e , p ⟩ [] ⟨ c , cutS false a s , absorbed , p ⟩
  rise-cutx = keeps λ
    { (flying (f-lnct fr) h)      → settled c-abs fr (_ , _ , refl , λ ())
    ; (flying (f-off u-cut fr) h) → settled c-abs fr (λ ())
    ; (adrift (f-lnct fr))        → settled c-abs fr (_ , _ , refl , λ ())
    ; (adrift (f-off u-cut fr))   → settled c-abs fr (λ ())
    ; (settled () _ _) }

  -- A LANE'S OWN FRAME passes the row.
  rise-ln : ∀ {Γ A} {b} {c : Ctx R Γ A} {s e p}
          → SimC ⟨ inLn b c , s , rising e , p ⟩ [] ⟨ c , lnS b s , rising e , p ⟩
  rise-ln = keeps λ
    { (flying (f-lane fr) (at , l , refl , h)) → flying fr (at , l , refl , h)
    ; (flying (f-off u-ln fr) h)             → flying fr λ ()
    ; (adrift (f-off u-ln fr))               → adrift fr
    ; (settled () _ _) }

  -- A TAKEWHILE OVER absorbs whatever still reaches it.
  rise-took : ∀ {Γ A} {i} {keep : A → Bool} {w} {c : Ctx R Γ A} {s e p} → w ≢ free
            → SimC ⟨ inTake i keep w c , s , rising e , p ⟩ [] ⟨ c , takeS i keep w s , absorbed , p ⟩
  rise-took nf = keeps λ
    { (flying (f-took fr fl nr fz ow eq) h) → settled c-abs fr (λ _ → s-took fl nr fz ow eq)
    ; (flying (f-take fr _ _ _) h)          → ⊥-elim (nf refl)
    ; (flying (f-off u-take fr) h)          → settled c-abs fr (λ ())
    ; (adrift (f-took fr fl nr fz ow eq))   → settled c-abs fr (λ _ → s-took fl nr fz ow eq)
    ; (adrift (f-take fr _ _ _))            → ⊥-elim (nf refl)
    ; (adrift (f-off u-take fr))            → settled c-abs fr (λ ())
    ; (settled () _ _) }

  -- A BODY OF A TORN-DOWN SOURCE has completed: it is stopped, and
  -- nothing reads it.
  rise-bodyx : ∀ {Γ X B} {k : CS Γ X} {o} {c : Ctx R Γ B} {s e p} → CS.srcLive k ≡ false
             → SimC ⟨ inBody k o c , s , rising e , p ⟩ [] ⟨ c , connS k o s , absorbed , p ⟩
  rise-bodyx nl = keeps λ
    { (flying (f-body fr sc _ _ fl eq sd) _) → settled c-abs fr λ _ → s-conn sc (dead nl) (dead nl) fl eq sd
    ; (flying (f-off u-body fr) _)        → settled c-abs fr (λ ())
    ; (adrift (f-body fr sc _ _ fl eq sd))   → settled c-abs fr λ _ → s-conn sc (dead nl) (dead nl) fl eq sd
    ; (adrift (f-off u-body fr))          → settled c-abs fr (λ ())
    ; (settled () _ _) }
    where
      dead : ∀ {b} {X : Set₁} → b ≡ false → T b → X
      dead refl ()

  ----------------------------------------------------------------------
  -- RUNS OF A TAKEWHILE'S OWN MARKS

  -- Its completion owed, under `last` of the failing value.
  run-stop : ∀ {Γ A} {i} {keep : A → Bool} {c : Ctx R Γ A} {s r p}
           → Inv (bef (r Machine.⊕ [ last ])) ⟨ c , takeS i keep (cpAt r) s , absorbed , p ⟩
           → Inv (bef (r Machine.⊕ [ last ])) ⟨ c , takeS i keep (cutAt r) s , rising cp , r Machine.⊕ [ last ] ⟩
  run-stop {r = r} (settled {w = owes _} _ fr h) = flying fr λ w → stopped (h w)
    where
      stopped : ∀ {Γ A} {sc : Scope Γ} {i} {keep : A → Bool} {s E}
              → Sync sc (bef (r ++ [ last ])) (takeS i keep (cpAt r) s) E
              → Sync sc (aft (r ++ [ last ])) (takeS i keep (cutAt r) s) E × E (r ++ [ last ]) end
      stopped {A = A} (s-took (a , x , nk , nf) _ fz (o-cp _) eq) =
        s-took (a , x , nk , nf) (≺-absurd {r} {r ++ [ last ]} (≺-ext r {last} []))
               (λ t lt → fz t (≺→≼ {r ++ [ last ]} {r ++ [ ix 0 ]} lt)) (o-cut (≺-irrefl {r ++ [ last ]})) eq
        , proj₁ (to eq (TakeWhile.stop x nk nf , vis {A = A} cp))
  run-stop (settled {w = lane _} _ fr (_ , _ , () , _))
  run-stop (settled {w = lanecut _} _ fr (_ , _ , () , _))
  run-stop (settled {w = pnd _} _ fr (_ , () , _))

  -- Its source cut: the source is not read.
  run-cut : ∀ {C Γ A} {i} {keep : A → Bool} {c : Ctx R Γ A} {s s′ r p p′}
          → Inv C ⟨ c , takeS i keep (cutAt r) s , absorbed , p ⟩ → Inv C ⟨ c , takeS i keep (overAt r) s′ , absorbed , p′ ⟩
  run-cut (settled {w = owes _} m fr h) = settled c-abs fr λ w → over (h w)
    where
      over : ∀ {Γ A} {sc : Scope Γ} {C} {i} {keep : A → Bool} {s s′ r} {E : EmissionSet A}
           → Sync sc C (takeS i keep (cutAt r) s) E → Sync sc C (takeS i keep (overAt r) s′) E
      over (s-took fl nr fz (o-cut n) eq) = s-took fl nr fz (o-over n) eq
  run-cut (settled {w = lane _} _ fr (_ , _ , () , _))
  run-cut (settled {w = lanecut _} _ fr (_ , _ , () , _))
  run-cut (settled {w = pnd _} _ fr (_ , () , _))

  -- A KILL SWITCH ATTACHED: live, nothing changes; off, nothing reads it.
  run-att : ∀ {C Γ A} {l} {c : Ctx R Γ A} {s s′ q p p′}
          → (T l → s′ ≡ s)
          → Inv C ⟨ c , cutS l (attAt q) s , absorbed , p ⟩ → Inv C ⟨ c , cutS l attached s′ , absorbed , p′ ⟩
  run-att {l = true} same (settled {w = owes _} m fr h) with same _
  ... | refl = settled c-abs fr λ w → att (h w)
    where
      att : ∀ {Γ A} {sc : Scope Γ} {C} {q} {s : St Γ A} {E} → Sync sc C (cutS true (attAt q) s) E → Sync sc C (cutS true attached s) E
      att (s-cut sy) = s-cut sy
  run-att {l = false} same (settled {w = owes _} m fr h) = settled c-abs fr λ w → off (h w)
    where
      off : ∀ {Γ A} {sc : Scope Γ} {C} {q} {s s′ : St Γ A} {E} → Sync sc C (cutS false (attAt q) s) E → Sync sc C (cutS false attached s′) E
      off ()
  run-att {l = true} same (settled {w = lanecut _} m fr (_ , _ , refl , h)) with same _
  ... | refl = settled c-abs fr (_ , _ , refl , h)
  run-att {l = false} same (settled {w = lanecut _} m fr (_ , _ , refl , h)) = settled c-abs fr (_ , _ , refl , λ ())
  run-att same (settled {w = lane _} _ fr (_ , _ , () , _))
  run-att same (settled {w = pnd _} _ fr (_ , () , _))
