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
-- cannot see: an of's index, a merge's begun lanes, a takeWhile's owe, a
-- joiner's inbox.  `Sync` ties each to its entry and the cursor.
--
-- A rise in flight splits the cursor: the focus's subtree has delivered
-- the row (`aft p`), every other node has not seen it (`bef p`).  The
-- frames the rise climbs read their hole at `bef p`, and the hole's entry
-- holds the row in flight there.
--
-- A joiner never reads its source's state: its source's frozen entry,
-- past the cursor, is what is still to feed it.
module adequacy.Cursor where

open import Data.Bool using (Bool; T; true; false; not)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; [_]; _++_; _ʳ++_; reverse)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (lookup) renaming ([] to []ᴬ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat as ℕ using (ℕ)
import Data.List.Relation.Unary.Any as Any

open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; mergeᶠ)
open import denotation.Events using (Pos; Timeline; ix; last; root)
open import denotation.Read using (Visible)
open import denotation.EmissionSet using (EmissionSet; Ev; out; end; _≺_; _≼_; enter; ⟦_⟧; Den; hot; coldAt; Rejoin;
  MapT; map-out; map-end; LaneOf; module Merge; module TakeWhile; module Connecting; DenEnv)
open import operation.PureObservable using (PureObs; module Machine)
open Machine using (St; Ctx; Conf; ⟨_,_,_,_⟩; Scope; unbound; binds; CS; Owe; free; cpAt; cutAt; overAt; scopeOf;
                    subscribing; absorbed; rising; search; found; start; feed; mapEv; nx; cp;
                    pend; ofS; doneS; mapS; cutS; lnS; takeS; flatS; connS; joinS;
                    top; inMap; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody)
                    renaming (Ev to Evᴹ; Shown to Shownᴹ)
open import denotation.Laws.Modulus using (≼-refl; ≺→≼; ≺-absurd; ≺-ext)
open import adequacy.Rows using (_≃_; _⇄_; shown; toEv; Inbox; full; pendRows; Frozen; Moves; Steps; Shows*; conv)
open import denotation.Events using (ofᴱ)
open import denotation.EmissionSet using (InE; Truncate)

------------------------------------------------------------------------
-- The cursor

-- Nothing delivered yet; a row in flight at `p`, not yet seen; the row at
-- `p` delivered.
data Cur : Set where
  origin : Cur
  bef aft : Pos → Cur

Owes : Cur → Pos → Set
Owes origin  q = Pos
Owes (bef p) q = p ≼ q
Owes (aft p) q = p ≺ q

-- The visible rows of `E` the cursor has not passed.
Due : ∀ {A} → Cur → EmissionSet A → EmissionSet A
Due C E q e = E q e × Visible e × Owes C q

-- Owing nothing more.
Spent : ∀ {A} → Cur → EmissionSet A → Set
Spent C E = ∀ {q e} → Due C E q e → ⊥

-- The engine's events are all visible.
vis : ∀ {A} (e : Evᴹ A) → Visible (toEv e)
vis (nx _) = _
vis cp     = _

------------------------------------------------------------------------
-- A joiner's feed

-- A joiner's rows whose source row the cursor has not passed: still to
-- be fed to it.
Unfed : ∀ {A} → Cur → Den A → Pos → EmissionSet A
Unfed C (hot t)    j = Rejoin j (λ k e → t k e × Owes C k)
Unfed C (coldAt _) j = λ _ _ → ⊥

------------------------------------------------------------------------
-- A NODE IN STEP WITH ITS FROZEN ENTRY: what its state still owes is
-- exactly `E`'s visible rows past `C`.  `E` is pinned from below by a
-- subscription's program (`s-pend`) and from above by the frame it sits
-- in; every clause but those two only composes.

-- The outer's values the cursor has passed, oldest first: one lane each.
data Begun {Γ A B} (sc : Scope Γ) (C : Cur) (f : A → Den B) (O : EmissionSet A)
           (Sy : St Γ B → EmissionSet B → Set₁) : List (Pos × A) → List (St Γ B) → Set₁ where
  none : Begun sc C f O Sy [] []
  more : ∀ {q a vs l ls E} → O q (out a) → ¬ Owes C q → Sy l E → LaneOf f q a ≃ E
       → Begun sc C f O Sy vs ls → Begun sc C f O Sy ((q , a) ∷ vs) (l ∷ ls)

-- No failing value passed.
NoFail : ∀ {A} → Cur → (A → Bool) → EmissionSet A → Set
NoFail C keep Es = ∀ {q a} → Es q (out a) → T (not (keep a)) → Owes C q

-- The first failing value, at `r`.
Failure : ∀ {A} → (A → Bool) → EmissionSet A → Pos → Set
Failure keep Es r = Σ _ λ a → Es r (out a) × T (not (keep a)) × ¬ TakeWhile.Failed true keep Es r

-- What a takeWhile failed at `r` still owes itself.
data OweAt : Owe → Pos → Set where
  o-cp   : ∀ {r} → OweAt (cpAt r) r
  o-cut  : ∀ {r} → OweAt (cutAt r) r
  o-over : ∀ {r} → OweAt (overAt r) r

-- A connect's flags, read off its source's frozen entry and its body's:
-- closed once the source's end is passed, where it ended; torn only once
-- the body owes nothing.
record Flags {Γ X B} (C : Cur) (k : CS Γ X) (β : EmissionSet B) : Set where
  field
    shut   : T (CS.closed k) → Frozen k (CS.endAt k) end × ¬ Owes C (CS.endAt k)
    unshut : ∀ {c} → Frozen k c end → ¬ Owes C c → T (CS.closed k)
    torn   : T (not (CS.srcLive k)) → Spent C β

-- Every value the cursor has passed has begun its lane.
Whole : ∀ {A} → Cur → EmissionSet A → List (Pos × A) → Set
Whole C O vs = ∀ {q a} → O q (out a) → ¬ Owes C q → (q , a) ∈ vs

data Sync : ∀ {Γ} → Scope Γ → Cur → ∀ {A} → St Γ A → EmissionSet A → Set₁ where
  -- a subscription owed where the cursor has not passed: its program's
  -- entry
  s-pend : ∀ {Γ} {sc : Scope Γ} {C} {A} {o : Obs Timeline Γ A} {q}
         → Owes C q
         → Sync sc C (pend o q) (pendRows (full sc) o q)
  -- an of: what it has left is what its entry owes
  s-of   : ∀ {Γ} {sc : Scope Γ} {C} {A} {ys : List A} {i q xs}
         → Due C (pendRows (full sc) (Tree.of ys) q) ≃ Due origin (InE (ofᴱ q i xs))
         → Sync sc C (ofS i q xs) (pendRows (full sc) (Tree.of ys) q)
  s-done : ∀ {Γ} {sc : Scope Γ} {C} {A} {E : EmissionSet A} → Spent C E → Sync sc C doneS E
  s-map  : ∀ {Γ} {sc : Scope Γ} {C} {A B} {f : A → B} {s E E′} → Sync sc C s E → MapT f E ≃ E′ → Sync sc C (mapS f s) E′
  s-cut  : ∀ {Γ} {sc : Scope Γ} {C} {A} {a} {s : St Γ A} {E} → Sync sc C s E → Sync sc C (cutS true a s) E
  s-ln   : ∀ {Γ} {sc : Scope Γ} {C} {A} {s : St Γ A} {E} → Sync sc C s E → Sync sc C (lnS true s) E
  s-lnx  : ∀ {Γ} {sc : Scope Γ} {C} {A} {s : St Γ A} {E} → Spent C E → Sync sc C (lnS false s) E
  -- a takeWhile not yet failed: no failing value passed
  s-take : ∀ {Γ} {sc : Scope Γ} {C} {A} {i} {keep : A → Bool} {s Es E}
         → Sync sc C s Es → NoFail C keep Es
         → TakeWhile.TakeT i keep Es ≃ E → Sync sc C (takeS i keep free s) E
  -- failed at `r`: its source is not read again
  s-took : ∀ {Γ} {sc : Scope Γ} {C} {A} {i} {keep : A → Bool} {w s Es E r}
         → Failure keep Es r → ¬ Owes C r → OweAt w r
         → TakeWhile.TakeT i keep Es ≃ E → Sync sc C (takeS i keep w s) E
  -- a merge: its outer, and a lane for each value passed
  s-merge : ∀ {Γ} {sc : Scope Γ} {C} {A B} {f : A → Obs Timeline Γ B} {d n o ls O E vs}
          → Sync sc C o O → Begun sc C (λ a → ⟦ f a ⟧ (full sc)) O (Sync sc C) vs ls
          → Whole C O vs
          → Merge.JoinT (λ a → ⟦ f a ⟧ (full sc)) O ≃ E
          → Sync sc C (flatS (mergeᶠ nothing) f d n [] o ls) E
  -- a connect: its body, under its binder read whole, and its source
  -- while the body owes
  s-conn : ∀ {Γ} {sc : Scope Γ} {C} {X B} {k : CS Γ X} {o : St Γ X} {b : St (X ∷ Γ) B} {β : EmissionSet B} {E}
         → CS.scope k ≡ sc
         → Sync (binds (CS.src k) (CS.connAt k) sc) C b β
         → (T (CS.srcLive k) → Sync sc C o (Frozen k))
         → Flags C k β
         → Connecting.ConnT (CS.connAt k) (Frozen k) β ≃ E
         → Sync sc C (connS k o b) E
  -- a joiner: what it was fed and has not shown, and what is still to
  -- feed it
  s-join : ∀ {Γ} {sc : Scope Γ} {C} {A} {j} {x : A ∈ Γ} {ib}
         → Due C (enter (lookup (full sc) x) j) ≃ (λ q e → Inbox ib q e ⊎ Due C (Unfed C (lookup (full sc) x) j) q e)
         → Sync sc C (joinS j true x ib) (enter (lookup (full sc) x) j)
  s-joinx : ∀ {Γ} {sc : Scope Γ} {C} {A} {j} {x : A ∈ Γ} {ib} → Spent C (enter (lookup (full sc) x) j)
          → Sync sc C (joinS j false x ib) (enter (lookup (full sc) x) j)

-- No rise in flight.
data Calm {A : Set} : Machine.Mode A → Set where
  c-sub : Calm subscribing
  c-abs : Calm absorbed

------------------------------------------------------------------------
-- THE FRAMES ABOVE A HOLE: the hole's entry `E`, composed up to the
-- root's, every other part in step.  `w` false: the hole is cut off, and
-- nothing reads its entry.

module _ {R : Set} (Rt : EmissionSet R) where

  data Fr (C : Cur) : ∀ {Γ A} → Ctx R Γ A → Bool → EmissionSet A → Set₁ where
    f-top   : ∀ {E} → E ≃ Rt → Fr C top true E
    f-map   : ∀ {Γ A B} {f : A → B} {c : Ctx R Γ B} {w E E′} → Fr C c w E′ → MapT f E ≃ E′ → Fr C (inMap f c) w E
    f-cut   : ∀ {Γ A} {a} {c : Ctx R Γ A} {w E} → Fr C c w E → Fr C (inCut true a c) w E
    f-cutx  : ∀ {Γ A} {a} {c : Ctx R Γ A} {w E E′} → Fr C c w E′ → Fr C (inCut false a c) false E
    f-ln    : ∀ {Γ A} {c : Ctx R Γ A} {w E} → Fr C c w E → Fr C (inLn true c) w E
    f-lnx   : ∀ {Γ A} {c : Ctx R Γ A} {w E E′} → Fr C c w E′ → Fr C (inLn false c) false E
    f-take  : ∀ {Γ A} {i} {keep : A → Bool} {c : Ctx R Γ A} {w E E′}
            → Fr C c w E′ → NoFail C keep E → TakeWhile.TakeT i keep E ≃ E′ → Fr C (inTake i keep free c) w E
    f-took  : ∀ {Γ A} {i} {keep : A → Bool} {o} {c : Ctx R Γ A} {w E Es E′ r}
            → Fr C c w E′ → Failure keep Es r → ¬ Owes C r → OweAt o r → TakeWhile.TakeT i keep Es ≃ E′
            → Fr C (inTake i keep o c) false E
    f-outer : ∀ {Γ A B} {f : A → Obs Timeline Γ B} {d n ls} {c : Ctx R Γ B} {w E E′ vs}
            → Fr C c w E′
            → Begun (scopeOf c) C (λ a → ⟦ f a ⟧ (full (scopeOf c))) E (Sync (scopeOf c) C) vs ls → Whole C E vs
            → Merge.JoinT (λ a → ⟦ f a ⟧ (full (scopeOf c))) E ≃ E′
            → Fr C (inOuter (mergeᶠ nothing) f d n [] ls c) w E
    f-lanes : ∀ {Γ A B} {f : A → Obs Timeline Γ B} {d n o pre post} {c : Ctx R Γ B} {w E E′ O vs₁ vs₂ q a}
            → Fr C c w E′
            → Sync (scopeOf c) C o O
            → Begun (scopeOf c) C (λ a → ⟦ f a ⟧ (full (scopeOf c))) O (Sync (scopeOf c) C) vs₁ (reverse pre)
            → O q (out a) → ¬ Owes C q → LaneOf (λ a → ⟦ f a ⟧ (full (scopeOf c))) q a ≃ E
            → Begun (scopeOf c) C (λ a → ⟦ f a ⟧ (full (scopeOf c))) O (Sync (scopeOf c) C) vs₂ post
            → Whole C O (vs₁ ++ (q , a) ∷ vs₂)
            → Merge.JoinT (λ a → ⟦ f a ⟧ (full (scopeOf c))) O ≃ E′
            → Fr C (inLanes (mergeᶠ nothing) f d n [] o pre post c) w E
    f-src   : ∀ {Γ X B} {k : CS Γ X} {b} {c : Ctx R Γ B} {w E E′ β}
            → Fr C c w E′ → CS.scope k ≡ scopeOf c → T (CS.srcLive k)
            → Sync (binds (CS.src k) (CS.connAt k) (scopeOf c)) C b β
            → Flags C k β → Frozen k ≃ E → Connecting.ConnT (CS.connAt k) (Frozen k) β ≃ E′
            → Fr C (inSrc k b c) w E
    f-body  : ∀ {Γ X B} {k : CS Γ X} {o} {c : Ctx R Γ B} {w E E′}
            → Fr C c w E′ → CS.scope k ≡ scopeOf c
            → (T (CS.srcLive k) → Sync (scopeOf c) C o (Frozen k))
            → Flags C k E
            → Connecting.ConnT (CS.connAt k) (Frozen k) E ≃ E′
            → Fr C (inBody k o c) w E

  -- THE INVARIANT: settled, the hole and every frame at one cursor; a
  -- rise in flight at `p`, its row in the hole's entry, delivered below
  -- and not yet seen above.
  data Inv : Cur → Conf R → Set₁ where
    settled : ∀ {Γ A} {c : Ctx R Γ A} {s m p C w E} → Calm m
            → Fr C c w E → (T w → Sync (scopeOf c) C s E) → Inv C ⟨ c , s , m , p ⟩
    flying  : ∀ {Γ A} {c : Ctx R Γ A} {s e p w E}
            → Fr (bef p) c w E → (T w → Sync (scopeOf c) (aft p) s E × E p (toEv e))
            → Inv (bef p) ⟨ c , s , rising e , p ⟩

  -- What the root owes: its entry past the cursor.
  RT : Cur → EmissionSet R
  RT C = Due C Rt

  -- A step: the invariant kept at some cursor, the rows moved.
  SimC : Conf R → Shownᴹ R → Conf R → Set₁
  SimC k sh k′ = ∀ {C} → Inv C k → Σ Cur λ C′ → Inv C′ k′ × Moves (RT C) sh (RT C′)

  ----------------------------------------------------------------------
  -- THE ROW SHOWN IS THE LEAST OWED, for free: a rise reaching the root
  -- at `p` is in the root's entry, and the cursor at `bef p` owes nothing
  -- before `p`.

  show-top : ∀ {s e p w E} → Fr (bef p) top w E → (T w → Sync unbound (aft p) s E × E p (toEv e))
           → Moves (RT (bef p)) [ (p , e) ] (RT (aft p))
  show-top {e = e} {p = p} (f-top eq) h with h _
  ... | _ , row = shown ((_≃_.to eq row , vis e , ≼-refl {p}) , vis e) (λ ((_ , _ , o) , _) → o) past
    where
      past : _
      past = (λ { (((x , v , _) , pq) , v′) → (x , v , pq) , v′ })
           ⇄ (λ { {q} ((x , v , pq) , v′) → ((x , v , ≺→≼ {p} {q} pq) , pq) , v′ })

  ----------------------------------------------------------------------
  -- THE STEPS, as leaves.  Only three kinds move the root's rows: the
  -- search, which moves the cursor to the next delivery; a rise absorbed
  -- or moved, which must leave no visible root row behind it; and the
  -- top, proven above.  Every other step keeps the cursor and owes only
  -- the invariant.

  -- Where a mark run delivers, if it does.
  data Delivers {Γ A} : St Γ A → Machine.Mark → Pos → Set₁ where
    d-of   : ∀ {i q x xs} → Delivers (ofS i q (x ∷ xs)) Machine.ofM (q Machine.⊕ [ ix i ])
    d-ofx  : ∀ {i q} → Delivers (ofS i q []) Machine.ofM (q Machine.⊕ [ last ])
    d-join : ∀ {j g x q e ib} → Delivers (joinS j g x ((q , e) ∷ ib)) Machine.joinM q
    d-stop : ∀ {i keep r s} → Delivers (takeS i keep (cpAt r) s) Machine.cpM (r Machine.⊕ [ last ])

  -- MAP: a rise up one frame, the hole's row mapped.
  rise-map : ∀ {Γ A B} {f : A → B} {c : Ctx R Γ B} {s e p}
           → Inv (bef p) ⟨ inMap f c , s , rising e , p ⟩ → Inv (bef p) ⟨ c , mapS f s , rising (mapEv f e) , p ⟩
  rise-map {f = f} {e = e} (settled () _ _)
  rise-map {f = f} {e = e} (flying (f-map fr eq) h) = flying fr λ w → let (sy , row) = h w in s-map sy eq , _≃_.to eq (mapped e row)
    where
      mapped : ∀ {E q} (e : Evᴹ _) → E q (toEv e) → MapT f E q (toEv (mapEv f e))
      mapped (nx a) r = map-out r
      mapped cp     r = map-end r

  -- TAKEWHILE: its completion owed, under `last` of the failing value.
  run-stop : ∀ {Γ A} {i} {keep : A → Bool} {c : Ctx R Γ A} {s r p}
           → Inv (bef (r Machine.⊕ [ last ])) ⟨ c , takeS i keep (cpAt r) s , absorbed , p ⟩
           → Inv (bef (r Machine.⊕ [ last ])) ⟨ c , takeS i keep (cutAt r) s , rising cp , r Machine.⊕ [ last ] ⟩
  run-stop {r = r} (settled _ fr h) = flying fr λ w → stopped (h w)
    where
      stopped : ∀ {Γ A} {sc : Scope Γ} {i} {keep : A → Bool} {s E}
              → Sync sc (bef (r ++ [ last ])) (takeS i keep (cpAt r) s) E
              → Sync sc (aft (r ++ [ last ])) (takeS i keep (cutAt r) s) E × E (r ++ [ last ]) end
      stopped (s-took (a , x , nk , nf) _ o-cp eq) =
        s-took (a , x , nk , nf) (≺-absurd {r} {r ++ [ last ]} (≺-ext r {last} [])) o-cut eq , _≃_.to eq (TakeWhile.stop x nk nf)

  postulate
    -- THE SEARCH LEMMA: the least mark leads everything owed.  The
    -- focus moves to it, and the cursor to just before its delivery:
    -- nothing owed anywhere in the tree lies between.
    search-least : ∀ {C Γ A} {c : Ctx R Γ A} {s r Γ′ A′} {c′ : Ctx R Γ′ A′} {s′ m κ p}
                 → Inv C ⟨ c , s , absorbed , r ⟩
                 → search top (Machine.plug c s) ≡ just (found (Γ′ , A′ , c′ , s′) m κ)
                 → Delivers s′ m p
                 → Inv (bef p) ⟨ c′ , s′ , absorbed , r ⟩ × RT C ≃ RT (bef p)
    -- A mark that delivers nothing: the focus moves, the cursor stays.
    search-quiet : ∀ {C Γ A} {c : Ctx R Γ A} {s r Γ′ A′} {c′ : Ctx R Γ′ A′} {s′ m κ}
                 → Inv C ⟨ c , s , absorbed , r ⟩
                 → search top (Machine.plug c s) ≡ just (found (Γ′ , A′ , c′ , s′) m κ)
                 → (∀ {p} → Delivers s′ m p → ⊥)
                 → Inv C ⟨ c′ , s′ , absorbed , r ⟩

    -- OF: its next value, in flight.
    run-of : ∀ {Γ A} {c : Ctx R Γ A} {i q x xs r}
           → Inv (bef (q Machine.⊕ [ ix i ])) ⟨ c , ofS i q (x ∷ xs) , absorbed , r ⟩ → Machine.closed c ≡ false
           → Inv (bef (q Machine.⊕ [ ix i ])) ⟨ c , ofS (ℕ.suc i) q xs , rising (nx x) , q Machine.⊕ [ ix i ] ⟩

    -- MERGE: a lane's value passes; the outer's value begins a lane, and
    -- no root row is left at it.
    rise-lane : ∀ {Γ A B} {f : A → Obs Timeline Γ B} {d n o pre post} {c : Ctx R Γ B} {s b p}
              → Inv (bef p) ⟨ inLanes (mergeᶠ nothing) f d n [] o pre post c , s , rising (nx b) , p ⟩
              → Machine.alive s ≡ true
              → Inv (bef p) ⟨ c , flatS (mergeᶠ nothing) f d n [] o (pre ʳ++ s ∷ post) , rising (nx b) , p ⟩
    rise-outer : ∀ {Γ A B} {f : A → Obs Timeline Γ B} {d n ls} {c : Ctx R Γ B} {o a p}
               → Inv (bef p) ⟨ inOuter (mergeᶠ nothing) f d n [] ls c , o , rising (nx a) , p ⟩
               → Machine.closed c ≡ false
               → Inv (aft p) (start c (mergeᶠ nothing) f d n [] o ls a p) × RT (bef p) ≃ RT (aft p)

    -- TAKEWHILE: an inclusive failing value moves under `ix 0`; the
    -- completion owed runs under `last`.
    rise-fail : ∀ {Γ A} {keep : A → Bool} {c : Ctx R Γ A} {s a p}
              → Inv (bef p) ⟨ inTake true keep free c , s , rising (nx a) , p ⟩ → keep a ≡ false
              → Inv (bef (p Machine.⊕ [ ix 0 ])) ⟨ c , takeS true keep (cpAt p) s , rising (nx a) , p Machine.⊕ [ ix 0 ] ⟩
                × RT (bef p) ≃ RT (bef (p Machine.⊕ [ ix 0 ]))

    -- CONNECT: the source's value fed to every live joiner and absorbed;
    -- a joiner shows what it was fed, at its own position.
    rise-src : ∀ {Γ X B} {k : CS Γ X} {b} {c : Ctx R Γ B} {s a p}
             → Inv (bef p) ⟨ inSrc k b c , s , rising (nx a) , p ⟩
             → Inv (aft p) ⟨ c , connS k s (feed (Any.here refl) p (nx a) b) , absorbed , p ⟩ × RT (bef p) ≃ RT (aft p)
    run-join : ∀ {Γ A} {c : Ctx R Γ A} {j} {x : A ∈ Γ} {q a ib r}
             → Inv (bef q) ⟨ c , joinS j true x ((q , nx a) ∷ ib) , absorbed , r ⟩ → Machine.closed c ≡ false
             → Inv (bef q) ⟨ c , joinS j true x ib , rising (nx a) , q ⟩

    -- SUBSCRIPTIONS keep the cursor and the rows.
    sub-of  : ∀ {C Γ A} {c : Ctx R Γ A} {xs : List A} {q p}
            → Inv C ⟨ c , pend (Tree.of xs) q , subscribing , p ⟩ → Inv C ⟨ c , ofS 0 q xs , absorbed , q ⟩
    sub-map : ∀ {C Γ A B} {c : Ctx R Γ B} {f : A → B} {o q p}
            → Inv C ⟨ c , pend (Tree.map f o) q , subscribing , p ⟩ → Inv C ⟨ inMap f c , pend o q , subscribing , q ⟩
    sub-merge : ∀ {C Γ A B} {c : Ctx R Γ B} {f : A → Obs Timeline Γ B} {o q p}
              → Inv C ⟨ c , pend (Tree.flatMap (mergeᶠ nothing) f o) q , subscribing , p ⟩
              → Inv C ⟨ inCut true (Machine.attAt q) (inOuter (mergeᶠ nothing) f false 0 [] [] c) , pend o q , subscribing , q ⟩
    sub-take : ∀ {C Γ A} {c : Ctx R Γ A} {i} {keep : A → Bool} {o q p}
             → Inv C ⟨ c , pend (Tree.takeWhile i keep o) q , subscribing , p ⟩
             → Inv C ⟨ inCut true (Machine.attAt q) (inTake i keep free c) , pend o q , subscribing , q ⟩
    sub-conn : ∀ {C Γ X B} {c : Ctx R Γ B} {o : Obs Timeline Γ X} {b q p}
             → Inv C ⟨ c , pend (Tree.connect o b) q , subscribing , p ⟩
             → Inv C ⟨ inBody (Machine.cs false true false (just q) nothing nothing q root o (scopeOf c)) (pend o (q Machine.⊕ [ ix 1 ])) c
                     , pend b (q Machine.⊕ [ ix 0 ]) , subscribing , q Machine.⊕ [ ix 0 ] ⟩
    sub-join : ∀ {C Γ A} {c : Ctx R Γ A} {x : A ∈ Γ} {q p}
             → Inv C ⟨ c , pend (Tree.connected x) q , subscribing , p ⟩ → Machine.closedUp c x ≡ false
             → Inv C ⟨ c , joinS q true x [] , absorbed , q ⟩
