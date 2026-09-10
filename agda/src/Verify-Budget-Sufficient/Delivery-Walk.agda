-- STRATUM 0b of Verify-Budget-Sufficient: THE DELIVERY WALK FITS dCapᶜ.
--
-- .Deliveries proved WHERE the ledger moves (§ B–§ E) and turned the
-- delivery recurrence into nine proven equations (§ D).  This module
-- consumes those equations and maps the evaluator's delivery clique
-- onto the well-founded walk `dCapᶜ` / `dWalkᶜ` (.Caps):
--
--     foldPath      sf gas … path …  ↦  dCapᶜ  S W R gas J
--     dispatchShare sf gas … i …     ↦  dCapᶜ  S W R gas J
--     shareGo       sf gas … ps …    ↦  dWalkᶜ S W R d gas J (length ps)
--     cascadeGo     a id chains …    ↦  dWalkᶜ S W R d n   J (length chains)
--
-- with J the CAPS LEVEL at the call's entry state.  That is forced: the walk used to thread a
-- REGISTRY and charge each delivery a fixed `Q` read once at the
-- cascade's entry caps, and charging anything per-frame at the entry
-- caps is machine-refuted — one `map-f` frame's output breaches the very
-- cap it was charged at, because `applyFn` grows a value.  The honest per-frame face is the
-- PROVEN `stepFrame-caps`, which REPORTS its growth as an index j′ and
-- lands at `frameStep (j + j′) c`, so the walk carries that index.

-- WHAT THE LEVEL BUYS, and why it is simpler rather than harder:
--
--   · THE REGISTRY NEEDS NO ACCOUNTING.  `capsOK?`'s own fifth conjunct
--     is `length registry ≤ cReg (frameStep J c)`, so the walk length a
--     dispatch fans out over is `regAt S R J` — read off the level.  The
--     old `sf-mint` / `sf-len` budget and the whole `R + Q · suc d`
--     threading are gone.
--   · A DELIVERY COSTS ONE `dLvl`, an ITERATION of the per-frame receipt
--     over the chain (`pathSz?`'s length conjunct caps it at
--     `suc (sizeAt S J)`), not a product — because each frame runs at
--     the level the one before it LEFT.
--   · AND THE WALK STILL DECOMPOSES FROM THE FRONT: `dWalkᶜ-front`
--     (.Caps) is an equality, so the change of direction the head-first
--     evaluator forces costs nothing, exactly as before.

-- WHY THE HYPOTHESES ARE A RECORD AND NOT POSTULATES.  The frame face is
-- a fact about `stepFrame` under a caps invariant, and `capsOK?` lives
-- two strata up (.Caps-Face).  Rather than postulate a caps-flavoured
-- statement in a module that cannot see caps — which would be either
-- false (unconditional) or unstateable (conditional) — the walk is
-- proven RELATIVE to a level-indexed state predicate `OK`, two
-- level-indexed SYNTACTIC ledgers (`Pb` on chains, `Vb` on payload
-- lists), and the facts about one frame under them.  .Caps-Face is
-- where they are instantiated, at `capsOK? (frameStep J c)`,
-- `pathSz? (cSize (frameStep J c))` and `valsCaps? (frameStep J c) sl`.

-- AND THE TWO SYNTACTIC LEDGERS ARE NOT OPTIONAL: without them the
-- frame fact is FALSE, not merely unproven.  Quantified over an
-- arbitrary `vals` it is refuted by one `thru-outer` frame, which
-- subscribes once per payload and so grows with a burst width no fixed
-- receipt bounds; quantified over an arbitrary `f` it is refuted by
-- `scan-f BIG`, which stores an accumulator over any cap.  So the frame
-- fact reads `Pb J (f ↠ path′)` and `Vb J vals`, and the walk THREADS
-- both: `Pb` down a chain by `p-tail` and across a dispatch by the
-- registry's own ledger (`regP?`, which shareAdmit filters and
-- shareFinish shrinks), `Vb` through a frame by the frame fact itself —
-- and both WIDEN with the level, which is what lets one walk position's
-- output feed the next at a higher one.
module Verify-Budget-Sufficient.Delivery-Walk where

open import Data.Bool    using (Bool; true; false; if_then_else_)
open import Data.Nat     using (ℕ; zero; suc; _+_; _≤_; _≡ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; ≤-refl; ≤-reflexive; +-mono-≤; n≤1+n; m≤m+n; m≤m⊔n; m≤n⊔m; ≡ᵇ⇒≡)
open import Data.List    using (List; []; _∷_; _++_; length; map)
open import Data.Bool.ListAction using (all; any)
open import Data.Fin     using (Fin; toℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Vec     using (lookup)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Rx.Prim      using (Tick; Id; Source; InstEvent;
                                close; exhausted; value; handoff; complete;
                                _at_from_as_; delivery; Gas)
open import Rx.Exp       using (Ctx; Closed; Val; _≟ᵗ_)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; RegId; Chain; Path; Frame; root; share-sink; _↠_; Stream; stepFrame;
  foldPath; dispatchShare; shareGo; shareAdmit; shareLatch; shareFinish; chainStep; cascadeGo; chainsGo;
  sameSource; arrTy; arrTick; arrSource; arrVal; budgetAt; sizeAt; regAt; fLvlD; iterL; lvls;
  dCapᶜ; dWalkᶜ)

-- .Caps for the level walk and its monotonicity toolkit (dCapᶜ-mono /
-- dWalkᶜ-mono / lvls-mono) and, under it, .Measures for pathLen and the
-- dropSource lemmas
open import Verify-Budget-Sufficient.Caps using
  (dCapᶜ-mono; dWalkᶜ-front; dWalkᶜ-mono; iterL-infl; iterL-mono; lvls-add;
   lvls-infl; lvls-mono)
open import Verify-Budget-Sufficient.Measures using
  (dropSource-all; dropSource-len;
                                                      pathLen; ∧-true)
open import Verify-Budget-Sufficient.Deliveries using
  (cascadeGo-deliv; chainStep-deliv; consᵈ; delivN; delivN-cons; delivN-split;
   delivN-≡; dispatchShare-suc-N; dispatchShare-zero-N; foldPath-deliv;
   foldPath-frame-N; foldPath-root-N; shareGo-deliv; ⊑ᵈ-trans)

-- THE DELIVERY-SIDE DEPTH MEASURES, and the ⊔-projections that read a
-- three-callee clause.  NOT A CYCLE: `Caps-Depth` imports only `Rx.*`,
-- so it sits BESIDE `Caps` rather than above it.  The walk carries a
-- depth premise because `stepFrame-face`'s from-inner chain needs one at
-- the bottom (`innerFinish`'s concat drain is unreachable at `dep = 0`),
-- and `d` — the record's own parameter — is the bound it is carried at
open import Verify-Budget-Sufficient.Caps-Depth
  using (depthFrame; depthFold; depthDisp; depthShareGo; depthChain;
         depthCascade; lub3-l; lub3-m; lub3-r)
open import Decide using (∧-intro; T-to)

------------------------------------------------------------------
-- § B.  THE REGISTRY LEDGER THE WALK READS.
--
-- A registration carries a chain, and the walk needs two things of it:
-- that the chain is SAFE TO FOLD (what the frame facts of § C read),
-- and that it is SHORT (the per-delivery budget is per FRAME, so a
-- delivery's total is the chain's length).  Both come out of ONE
-- abstract Bool `Pb` on paths — the length by `p-len` — because at
-- .Caps-Face's instantiation they are one predicate: `pathSz?` carries
-- the length as its own conjunct, and its ledger over the registry IS
-- capsOK?'s `regsSz?` conjunct, so the walk's ledger costs the caller
-- nothing.
------------------------------------------------------------------

regP? : ∀ {n} {Γ : Ctx n} {t} → (∀ {u} → Path Γ u t → Bool) →
        List (RegId × Source × Chain Γ t) → Bool
regP? Pb = all (λ en → Pb (proj₂ (proj₂ (proj₂ en))))

chP? : ∀ {n} {Γ : Ctx n} {s t} → (∀ {u} → Path Γ u t → Bool) →
       List (RegId × Path Γ s t) → Bool
chP? Pb = all (λ rc → Pb (proj₂ rc))

-- WHAT A LEDGER THAT DOES NOT READ THE PATH COSTS TO DISTRIBUTE: nothing.
-- A face whose payload reading ignores the chain hands the same Bool to
-- every entry, so the list-level form is the entry-level one repeated —
-- which is what lets the index be introduced without any face that has
-- nothing to say about the chain paying for it
chP?-const : ∀ {n} {Γ : Ctx n} {s t} (b : Bool)
  (ps : List (RegId × Path Γ s t)) → b ≡ true → chP? (λ _ → b) ps ≡ true
chP?-const b []       h = refl
chP?-const b (p ∷ ps) h = ∧-intro h (chP?-const b ps h)

-- the two share-boundary bookkeeping steps, on the REGISTRY axis (the
-- ledger axis is .Deliveries' shareLatch-deliv / shareFinish-deliv)
shareLatch-reg : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (i : Fin n) (fin : Bool) (st : EvalSt e) →
  EvalSt.registry (shareLatch i fin st) ≡ EvalSt.registry st
shareLatch-reg i false st = refl
shareLatch-reg i true  st = refl

shareFinish-len : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (i : Fin n) (fin : Bool) (out : Stream Γ t × Sched Γ × EvalSt e) →
  length (EvalSt.registry (proj₂ (proj₂ (shareFinish i fin out))))
    ≤ length (EvalSt.registry (proj₂ (proj₂ out)))
shareFinish-len i false out                = ≤-refl
shareFinish-len i true  (emits , sd , st′) = dropSource-len (toℕ i) (EvalSt.registry st′)

shareFinish-regP : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (Pb : ∀ {u} → Path Γ u t → Bool)
  (i : Fin n) (fin : Bool) (out : Stream Γ t × Sched Γ × EvalSt e) →
  regP? Pb (EvalSt.registry (proj₂ (proj₂ out))) ≡ true →
  regP? Pb (EvalSt.registry (proj₂ (proj₂ (shareFinish i fin out)))) ≡ true
shareFinish-regP Pb i false out                h = h
shareFinish-regP Pb i true  (emits , sd , st′) h =
  dropSource-all (λ en → Pb (proj₂ (proj₂ (proj₂ en))))
                 (toℕ i) (EvalSt.registry st′) h

-- the EMITS projection, on the same axis as the two above.  shareFinish
-- touches only the registry and the live set — the stream rides through
-- both branches untouched — but that is not usable DEFINITIONALLY: with
-- `fin` a variable neither clause fires, so `proj₁ (shareFinish i fin out)`
-- is stuck rather than equal to `proj₁ out`.  Hence the case split, exactly
-- as `shareFinish-len` and `shareFinish-regP` need one
shareFinish-emits : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (i : Fin n) (fin : Bool) (out : Stream Γ t × Sched Γ × EvalSt e) →
  proj₁ (shareFinish i fin out) ≡ proj₁ out
shareFinish-emits i false out                = refl
shareFinish-emits i true  (emits , sd , st′) = refl

-- the admitted sublist: shorter than the registry, and inheriting its
-- ledger.  Same filter shape as chainsGo's
shareAdmit-len : ∀ {n} {Γ : Ctx n} {t} (i : Fin n)
  (rs : List (RegId × Source × Chain Γ t)) →
  length (shareAdmit {t = t} i rs) ≤ length rs
shareAdmit-len i [] = z≤n
shareAdmit-len {Γ = Γ} i ((rid , s , (u , p)) ∷ r)
  with sameSource (toℕ i) s | u ≟ᵗ lookup Γ i
... | false | _        = ≤-trans (shareAdmit-len i r) (n≤1+n _)
... | true  | no  _    = ≤-trans (shareAdmit-len i r) (n≤1+n _)
... | true  | yes refl = s≤s (shareAdmit-len i r)

shareAdmit-chP : ∀ {n} {Γ : Ctx n} {t} (Pb : ∀ {u} → Path Γ u t → Bool)
  (i : Fin n) (rs : List (RegId × Source × Chain Γ t)) →
  regP? Pb rs ≡ true → chP? Pb (shareAdmit {t = t} i rs) ≡ true
shareAdmit-chP Pb i [] h = refl
shareAdmit-chP {Γ = Γ} Pb i ((rid , s , (u , p)) ∷ r) h
  with sameSource (toℕ i) s | u ≟ᵗ lookup Γ i
... | false | _        = shareAdmit-chP Pb i r (proj₂ (∧-true _ _ h))
... | true  | no  _    = shareAdmit-chP Pb i r (proj₂ (∧-true _ _ h))
... | true  | yes refl = ∧-intro (proj₁ (∧-true _ _ h))
                                 (shareAdmit-chP Pb i r (proj₂ (∧-true _ _ h)))

-- THE SAME LEDGER READ AT AN ENTRY'S OWN SOURCE, which is the half a
-- path-level `Pb` cannot state.  A stratification reading of a chain
-- wants two things, and only one of them is about the path: that the
-- chain's frames are stratified, and that its floor is at or above the
-- SOURCE it listens to.  The second names the registration rather than
-- the path, so no `Pb` can carry it, and a face wanting both would
-- otherwise have to ask for them as two ledgers over the same list.
--
-- WHAT MAKES THE SOURCE FORGETTABLE AGAIN IS THAT EACH FILTER TESTS
-- THE SOURCE IT FILTERS FOR.  Both transports below drop the source
-- from every entry they keep, and both may: the entry survives only
-- past `sameSource`, so its source IS the one the filter was given,
-- and the predicate arrives on the output list already instantiated
-- there.  That is what lets the consumers stay `chP?`-shaped and share
-- every lemma the path-level ledger already has.
regQ? : ∀ {n} {Γ : Ctx n} {t} → (∀ {u} → Source → Path Γ u t → Bool) →
        List (RegId × Source × Chain Γ t) → Bool
regQ? Q = all (λ en → Q (proj₁ (proj₂ en)) (proj₂ (proj₂ (proj₂ en))))

shareAdmit-chQ : ∀ {n} {Γ : Ctx n} {t} (Q : ∀ {u} → Source → Path Γ u t → Bool)
  (i : Fin n) (rs : List (RegId × Source × Chain Γ t)) →
  regQ? Q rs ≡ true → chP? (λ {u} → Q {u} (toℕ i)) (shareAdmit {t = t} i rs) ≡ true
shareAdmit-chQ Q i [] h = refl
shareAdmit-chQ {Γ = Γ} Q i ((rid , s , (u , p)) ∷ r) h
  with sameSource (toℕ i) s in eqs | u ≟ᵗ lookup Γ i
... | false | _        = shareAdmit-chQ Q i r (proj₂ (∧-true _ _ h))
... | true  | no  _    = shareAdmit-chQ Q i r (proj₂ (∧-true _ _ h))
... | true  | yes refl =
  ∧-intro (subst (λ z → Q z p ≡ true) (sym (≡ᵇ⇒≡ (toℕ i) s (T-to eqs)))
                 (proj₁ (∧-true _ _ h)))
          (shareAdmit-chQ Q i r (proj₂ (∧-true _ _ h)))

-- the cascade's side of the same step, and it is the same filter: an
-- arrival's chains are the registry's entries past a source test and a
-- type test, in that order, so the clauses correspond one for one
chainsGo-chQ : ∀ {n} {Γ : Ctx n} {t} (Q : ∀ {u} → Source → Path Γ u t → Bool)
  (a : Arrival Γ) (rs : List (RegId × Source × Chain Γ t)) →
  regQ? Q rs ≡ true → chP? (λ {u} → Q {u} (arrSource a)) (chainsGo {t = t} a rs) ≡ true
chainsGo-chQ Q a [] h = refl
chainsGo-chQ Q a ((rid , s , (u , p)) ∷ r) h
  with sameSource (arrSource a) s in eqs | u ≟ᵗ arrTy a
... | false | _        = chainsGo-chQ Q a r (proj₂ (∧-true _ _ h))
... | true  | no  _    = chainsGo-chQ Q a r (proj₂ (∧-true _ _ h))
... | true  | yes refl =
  ∧-intro (subst (λ z → Q z p ≡ true) (sym (≡ᵇ⇒≡ (arrSource a) s (T-to eqs)))
                 (proj₁ (∧-true _ _ h)))
          (chainsGo-chQ Q a r (proj₂ (∧-true _ _ h)))

------------------------------------------------------------------
-- § C.  THE HYPOTHESES: ONE FRAME, AT THE LEVEL IT RUNS AT.
--
-- Everything below is proven from ONE fact about `stepFrame` — it
-- reports a growth index j′ whose LANDING LEVEL `J + j′` sits under one
-- refreshed per-frame level `fLvlD S W d J`, and lands its post-state,
-- its output burst and the registry's ledger at level `J + j′` — plus the three closure facts the walk's own
-- bookkeeping needs (the delivered cons, the share latch, the share
-- finish, none of which is a frame) and the two LEDGER readings the
-- level supplies: a chain is shorter than `sizeAt S J` and the registry
-- is shorter than `regAt S R J`.
--
-- THE SHAPE IS THE PROVEN ONE, and that is the whole point of the
-- rewrite.  `stepFrame-caps` (.Caps-Face, ground) reports
-- `Σ j′ → capsOK? (frameStep (j + j′) c) …`: growth REPORTED, not
-- denied.  The face this record asks for is that shape with a bound on
-- j′, where the previous record asked for same-level preservation —
-- which is FALSE, machine-refuted by one `map-f` frame
-- (machine-refuted).
--
-- AND THE TWO SYNTACTIC LEDGERS ARE STILL NOT OPTIONAL, for the same
-- reasons they never were: `sf-step` quantified over an arbitrary
-- `vals` is refuted by one `thru-outer` frame, which subscribes once
-- per payload and so grows in proportion to a burst width no fixed
-- receipt bounds; over an arbitrary `f` it is refuted by `scan-f BIG`,
-- which stores an accumulator over any cap.  So both ledgers are read
-- at the CURRENT level and both WIDEN with it — which they do, because
-- `frameStep` is monotone in its index and `capsOK?` widens along ⊑ᶜ.
------------------------------------------------------------------

record Walk-Hyps {n} {Γ : Ctx n} {t} (e : Closed Γ t) (S W R d : ℕ) : Set₁ where
  field
    OK : ℕ → Sched Γ → EvalSt e → Set

    -- the two syntactic side conditions, now READ AT A LEVEL
    Pb : ℕ → ∀ {u} → Path Γ u t → Bool
    -- AND THE PAYLOAD LEDGER IS READ AGAINST THE CHAIN THE PAYLOAD IS
    -- TRAVELLING, not against the slot that emitted it.  A frame applies
    -- the syntax of whichever definition PUSHED it, so a reading taken
    -- at the source is not preserved across one step while a reading
    -- taken at the chain is.  Every face that has nothing to say about
    -- the chain ignores the index, which is most of them.
    --
    -- AND THE COST ONCE CHARGED TO THIS INDEX IS NOT A COST.  The burst
    -- face read as a multiple of its pre-index self, and a shape reading
    -- stood ready to explain it: three loop premises turned from one
    -- Bool into an `all` over the chain list, so a face whose own
    -- reading is a fold nests one wherever it states its ledger THROUGH
    -- this field.  The face is cut in three, and all three pieces check
    -- in SECONDS — the one naming this record in a type included — and
    -- so does the uncut face they came from.  Every reading that ever
    -- ran past the dev budget here was taken against a cone the
    -- container had not built, and the attribution followed the FILE
    -- rather than what the run was paying for; a control truncated to
    -- the imports prices that cone at very nearly the whole of what the
    -- face costs.  So this index is not a build cost and there is no
    -- cost to recover by sealing it.  The figures live in
    -- `typecheck-performance-numbers.md`, and the misattribution's shape
    -- is in `docs/agda-dev.md`, which is where the next one gets caught.
    Vb : ∀ {u} → Path Γ u t → ℕ → ∀ {s} → List (Val Γ s) → Bool

    -- BURST LEDGERS: an abstract Bool over the accumulated protocol events
    -- in one emit (Eb) and over a whole stream (Bb).  Threaded through the
    -- walk so that the anchor can recover a burst bound from the walk
    -- rather than having to state it as a separate postulate.
    Eb : ℕ → List (InstEvent (Val Γ t)) → Bool
    Bb : ℕ → Stream Γ t → Bool

    -- GAS ADEQUACY HOOK.  `sf-step` quantifies over an arbitrary frame
    -- gas, and a gas-conditional ledger flavour (the nodry conjunct:
    -- `subscribeInner g0` emits a dried close, and the depth premise
    -- does not exclude g0 — depth measures nesting demand, not supply)
    -- is FALSE at sf = g0.  So the frame obligation may read `GOK sf
    -- id`, and `g-mint` supplies it for the one gas the walk itself
    -- mints: `chainStep`'s `budgetAt e (Sched.slots sched) id`
    -- (cascadeGo-go below).  Gas-blind instantiations set GOK = ⊤.
    GOK : Gas → Id → Set
    g-mint : ∀ (J : ℕ) (id : Id) (sched : Sched Γ) (st : EvalSt e) →
             OK J sched st → GOK (budgetAt e (Sched.slots sched) id) id

    -- THE PER-FRAME CEILING CHANNEL.  A frame that SUBSCRIBES prices its
    -- new registration against the NEXT instant's caps, and nothing native
    -- to this record links the walk's level to that tower (the Burst-Walk
    -- ceiling debt).  `CL L id` is an abstract per-level ceiling,
    -- DOWNWARD closed (`cl-anti`) because its honest instantiation
    -- (`cSize (frameStep L c) ≤ sizeCapAt e sl (suc id)`, .Burst-Walk) is
    -- anti-monotone in L.  Each -go lemma carries ONE `CL Λ id` premise —
    -- Λ its own delivery-counted level cap — and restricts it per frame
    -- to `CL (fLvlD S W d J) id` by the same lvls/dCapᶜ arithmetic the
    -- receipts spend, run in the premise direction.  Ceiling-blind
    -- instantiations set CL = ⊤.
    CL : ℕ → Id → Set
    cl-anti : ∀ {L L′ : ℕ} (id : Id) → L ≤ L′ → CL L′ id → CL L id

    -- closure facts for Eb.  e-close covers only the close the walk
    -- itself seeds (`eb-seed`: a spent source's `exhausted`) — stated
    -- at that reason, not all of CloseReason, so a nodry Eb flavour
    -- stays satisfiable (`dried` never passes it)
    e-nil   : ∀ J → Eb J [] ≡ true
    e-close : ∀ J (src : Source) → Eb J (close src exhausted ∷ []) ≡ true
    e-app   : ∀ J evs₁ evs₂ → Eb J evs₁ ≡ true → Eb J evs₂ ≡ true →
              Eb J (evs₁ ++ evs₂) ≡ true
    e-widen : ∀ {J J′} → J ≤ J′ → ∀ evs → Eb J evs ≡ true → Eb J′ evs ≡ true

    -- closure facts for Bb
    b-nil   : ∀ J → Bb J [] ≡ true
    b-app   : ∀ J (s₁ s₂ : Stream Γ t) → Bb J s₁ ≡ true → Bb J s₂ ≡ true →
              Bb J (s₁ ++ s₂) ≡ true
    b-widen : ∀ {J J′} → J ≤ J′ → ∀ (str : Stream Γ t) → Bb J str ≡ true →
              Bb J′ str ≡ true
    -- foldPath's root envelope: events + mapped values + optional complete
    b-deliv : ∀ J (id : Id) (src : Source)
              (evs : List (InstEvent (Val Γ t))) (vals : List (Val Γ t)) (fin : Bool) →
              Eb J evs ≡ true → Vb root J vals ≡ true →
              Bb J (((evs ++ map value vals ++ (if fin then complete ∷ [] else []))
                      at id from src as delivery) ∷ []) ≡ true
    -- foldPath's share-sink envelope: events + handoff (valueless)
    b-handoff : ∀ J (id : Id) (src : Source)
                (evs : List (InstEvent (Val Γ t))) (i : Fin n) →
                Eb J evs ≡ true →
                Bb J (((evs ++ handoff (toℕ i) ∷ []) at id from src as delivery) ∷ []) ≡ true

    -- the level's two ledger readings: a chain is shorter than the size
    -- cap, and the registry is shorter than the registration cap
    p-len : ∀ (J : ℕ) {u} (p : Path Γ u t) → Pb J p ≡ true → pathLen p ≤ sizeAt S J
    p-tail : ∀ (J : ℕ) {s u} (f : Frame Γ s u) (p : Path Γ u t) →
             Pb J (f ↠ p) ≡ true → Pb J p ≡ true

    -- and both ledgers widen along the level
    p-widen : ∀ {J J′ : ℕ} → J ≤ J′ → ∀ {u} (p : Path Γ u t) →
              Pb J p ≡ true → Pb J′ p ≡ true
    v-widen : ∀ {J J′ : ℕ} → J ≤ J′ → ∀ {u} (κ : Path Γ u t) {s} (vs : List (Val Γ s)) →
              Vb κ J vs ≡ true → Vb κ J′ vs ≡ true

    -- AND THE FAN IS WHERE THE INDEX MOVES, which is the one step the
    -- widening above cannot do.  Values reaching a share's sink are
    -- re-emitted BY that share, so their reading at the sink is what
    -- every chain the share admits inherits -- and the state predicate
    -- is what carries whatever makes that inheritance sound, since the
    -- admitted chains are read out of the registry it speaks about.
    v-fan : ∀ (J : ℕ) (i : Fin n) {s} (vs : List (Val Γ s))
            (sched : Sched Γ) (st : EvalSt e) → OK J sched st →
            Vb (share-sink {t = t} i) J vs ≡ true →
            chP? (λ κ → Vb κ J vs) (shareAdmit {t = t} i (EvalSt.registry st)) ≡ true

    -- AND THE CHAIN'S TWO ENTRY READINGS, AS ONE STATE-INDEXED LEDGER
    -- ON PATHS.  `Pb` cannot carry them: an order reading is against the
    -- scheduler's counter and a park reading is against the store, and
    -- `Pb` sees neither.  Nor can `OK`, which sees both and no chain.
    -- So the reading is its own ledger, carried rather than derived --
    -- a caps-legal state the evaluator never built satisfies the receipt
    -- and fails the reading, refuted beside the rows that spend it.
    Ob : Sched Γ → EvalSt e → ∀ {u} → Path Γ u t → Bool

    -- and the three places the walk MOVES it, one per shape of step the
    -- walk takes that the frame fact does not: the delivery mark, the
    -- fan out of the registry, and a sibling chain's run
    o-cons : ∀ (rid : RegId) (sched : Sched Γ) (st : EvalSt e)
             {u} (p : Path Γ u t) →
             Ob sched st p ≡ true → Ob sched (consᵈ rid st) p ≡ true

    o-fan : ∀ (J : ℕ) (i : Fin n) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
            OK J sched st →
            chP? (Ob sched (shareLatch i fin st))
                 (shareAdmit {t = t} i (EvalSt.registry st)) ≡ true

    o-fold : ∀ (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
             {u} (p : Path Γ u t) (vals : List (Val Γ u))
             (evs : List (InstEvent (Val Γ t))) (fin : Bool)
             (sched : Sched Γ) (st : EvalSt e) (ps : List (RegId × Path Γ u t)) →
             chP? (Ob sched st) ps ≡ true →
             let fp = foldPath sf gas id now envSrc p vals evs fin sched st in
             chP? (Ob (proj₁ (proj₂ fp)) (proj₂ (proj₂ fp))) ps ≡ true

    o-chain : ∀ (id : Id) (a : Arrival Γ) (p : Path Γ (arrTy a) t)
              (sched : Sched Γ) (st : EvalSt e)
              (chains : List (RegId × Path Γ (arrTy a) t)) →
              chP? (Ob sched st) chains ≡ true →
              let cs = chainStep id a p sched st in
              chP? (Ob (proj₁ (proj₂ cs)) (proj₂ (proj₂ cs))) chains ≡ true

    ok-reg : ∀ (J : ℕ) (sched : Sched Γ) (st : EvalSt e) → OK J sched st →
             length (EvalSt.registry st) ≤ regAt S R J

    ok-cons : ∀ (J : ℕ) (rid : RegId) (sched : Sched Γ) (st : EvalSt e) →
      OK J sched st → OK J sched (consᵈ rid st)

    ok-latch : ∀ (J : ℕ) (i : Fin n) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
      OK J sched st → OK J sched (shareLatch i fin st)

    ok-finish : ∀ (J : ℕ) (i : Fin n) (fin : Bool)
      (out : Stream Γ t × Sched Γ × EvalSt e) →
      OK J (proj₁ (proj₂ out)) (proj₂ (proj₂ out)) →
      OK J (proj₁ (proj₂ (shareFinish i fin out)))
           (proj₂ (proj₂ (shareFinish i fin out)))

    -- ONE FRAME, and its receipt is the level's own per-frame charge
    sf-step : ∀ (J : ℕ) {s u} (sf : Gas) (id : Id) (now : Tick) (f : Frame Γ s u)
      (path′ : Path Γ u t) (vals : List (Val Γ s)) (fin : Bool)
      (sched : Sched Γ) (st : EvalSt e) → OK J sched st →
      Pb J (f ↠ path′) ≡ true → Vb (f ↠ path′) J vals ≡ true →
      regP? (Pb J) (EvalSt.registry st) ≡ true →
      GOK sf id →
      CL (fLvlD S W d J) id →
      -- THE DEPTH PREMISE.  A frame that SUBSCRIBES lands its budget in
      -- `fLvlD S W dep j` at its own `dep`, and widening that to the
      -- walk's `d` is the only thing the from-inner faces cannot source
      -- locally.  Carried here rather than derived because the walk is
      -- where the frame is reached
      depthFrame sf id now f path′ vals fin sched st ≤ d →
      -- AND THE CHAIN'S OWN READING, which the step SPENDS at its head
      -- and re-establishes at its tail: the two halves are what the
      -- from-inner faces read the node table and the counter through
      Ob sched st (f ↠ path′) ≡ true →
      let r = stepFrame sf id now f path′ vals fin sched st in
      Σ ℕ λ j′ → (J + j′ ≤ fLvlD S W d J)
        × OK (J + j′) (proj₁ (proj₂ (proj₂ (proj₂ r))))
                      (proj₂ (proj₂ (proj₂ (proj₂ r))))
        × (Vb path′ (J + j′) (proj₁ r) ≡ true)
        × (regP? (Pb (J + j′))
                 (EvalSt.registry (proj₂ (proj₂ (proj₂ (proj₂ r))))) ≡ true)
        -- NEW: the frame's protocol events are covered by Eb at the
        -- landing level.  `proj₁ (proj₂ r)` is the events list stepFrame
        -- emits; the walk threads this so the anchor can recover a burst
        -- bound on the accumulated evs without a separate postulate
        × (Eb (J + j′) (proj₁ (proj₂ r)) ≡ true)
        × (Ob (proj₁ (proj₂ (proj₂ (proj₂ r))))
              (proj₂ (proj₂ (proj₂ (proj₂ r)))) path′ ≡ true)

------------------------------------------------------------------
-- § D.  THE WALK, RELATIVE TO THOSE HYPOTHESES.
--
-- Each lemma returns the LEVEL its run lands at, boxed with everything
-- the caller needs of it: that the level only grew, that it grew by no
-- more than one `dLvl` per delivery, that the state predicate and both
-- ledgers hold THERE, and that the deliveries fit the walk.  The four
-- clauses are the four lines of `dCapᶜ` / `dWalkᶜ`, with .Deliveries'
-- § D supplying the counting and `dWalkᶜ-front` the change of direction.
------------------------------------------------------------------

module Walk {n} {Γ : Ctx n} {t} {e : Closed Γ t}
            (S W R d : ℕ) (2≤S : 2 ≤ S) (H : Walk-Hyps e S W R d) where

  open Walk-Hyps H

  -- the state predicate the walk actually threads: the caller's, plus
  -- the registry's own ledger, both at one level
  Good : ℕ → Sched Γ → EvalSt e → Set
  Good J sched st = OK J sched st × (regP? (Pb J) (EvalSt.registry st) ≡ true)

  -- the chain ledger widens with the level, one entry at a time
  chP?-widen : ∀ {J J′ : ℕ} → J ≤ J′ → ∀ {s} (ps : List (RegId × Path Γ s t)) →
    chP? (Pb J) ps ≡ true → chP? (Pb J′) ps ≡ true
  chP?-widen le []             h = refl
  chP?-widen le ((rid , p) ∷ ps) h =
    ∧-intro (p-widen le p (proj₁ (∧-true _ _ h)))
            (chP?-widen le ps (proj₂ (∧-true _ _ h)))

  -- and the payload ledger widens the same way once it is read per chain:
  -- `v-widen` moves ONE reading up a level, and a chain list is that
  -- reading pointwise, so the distributed form widens entry by entry
  chV?-widen : ∀ {J J′ : ℕ} → J ≤ J′ → ∀ {s} (vs : List (Val Γ s)) →
    ∀ {u} (ps : List (RegId × Path Γ u t)) →
    chP? (λ κ → Vb κ J vs) ps ≡ true → chP? (λ κ → Vb κ J′ vs) ps ≡ true
  chV?-widen le vs []             h = refl
  chV?-widen le vs ((rid , p) ∷ ps) h =
    ∧-intro (v-widen le p vs (proj₁ (∧-true _ _ h)))
            (chV?-widen le vs ps (proj₂ (∧-true _ _ h)))

  -- the delivery mark moves the chain reading pointwise, which is the
  -- one lift a list needs: the record states the transport at a single
  -- chain, because that is the shape the head of a fan-out spends
  chOb-cons : ∀ (rid : RegId) (sched : Sched Γ) (st : EvalSt e)
    {u} (ps : List (RegId × Path Γ u t)) →
    chP? (Ob sched st) ps ≡ true → chP? (Ob sched (consᵈ rid st)) ps ≡ true
  chOb-cons rid sched st []            h = refl
  chOb-cons rid sched st ((r , p) ∷ ps) h =
    ∧-intro (o-cons rid sched st p (proj₁ (∧-true _ _ h)))
            (chOb-cons rid sched st ps (proj₂ (∧-true _ _ h)))

  -- THE SEED EVENTS a delivery starts from: a spent source contributes its
  -- own exhausted close, an unspent one contributes nothing.  Both callers
  -- (shareGo-go, cascadeGo-go) need this, and neither can inline it as a
  -- `with`: their clauses already `with` on the cancellation test, and Agda
  -- refuses to `with` on a variable bound by a parent clause's pattern.
  -- Taking the Bool as an explicit argument moves the split somewhere it is
  -- allowed to happen
  eb-seed : ∀ (J : ℕ) (src : Source) (fin : Bool) →
            Eb J (if fin then close src exhausted ∷ [] else []) ≡ true
  eb-seed J src true  = e-close J src
  eb-seed J src false = e-nil J

  -- WHAT ONE RUN REPORTS.  `lvl` is where it landed, `lo` that it only
  -- climbed, `hi` that it climbed by at most one delivery-charge per
  -- delivery from the level `base` its frames left it at, `cnt` that
  -- its deliveries fit the walk, and `burst` that the emitted stream
  -- fits Bb at the landing level.  `str` is a type parameter so that
  -- the CALLER names the exact stream — `proj₁ fp`, `proj₁ ds`, etc. —
  -- and `burst` is a field that depends on the earlier field `lvl`
  record Res (J base cap : ℕ) (str : Stream Γ t)
             (sched′ : Sched Γ) (st st′ : EvalSt e) : Set where
    constructor res
    field
      lvl   : ℕ
      lo    : J ≤ lvl
      hi    : lvl ≤ lvls S W d base (delivN st st′)
      good  : Good lvl sched′ st′
      cnt   : delivN st st′ ≤ cap
      burst : Bb lvl str ≡ true

  ----------------------------------------------------------------
  -- (i) THE FOUR WALKS, FUSED: predicate, level and delivery count in
  -- one induction, because the frame fact hands them back together.
  ----------------------------------------------------------------

  foldPath-go : ∀ (J : ℕ) (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
    {u} (path : Path Γ u t) (vals : List (Val Γ u))
    (evs : List (InstEvent (Val Γ t))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) → Good J sched st →
    Pb J path ≡ true → Vb path J vals ≡ true →
    Eb J evs ≡ true →
    GOK sf id →
    CL (lvls S W d (iterL S W d (pathLen path) J)
                   (dCapᶜ S W R d gas (iterL S W d (pathLen path) J))) id →
    depthFold sf gas id now envSrc path vals evs fin sched st ≤ d →
    Ob sched st path ≡ true →
    let fp = foldPath sf gas id now envSrc path vals evs fin sched st in
    Res J (iterL S W d (pathLen path) J)
          (dCapᶜ S W R d gas (iterL S W d (pathLen path) J))
          (proj₁ fp) (proj₁ (proj₂ fp)) st (proj₂ (proj₂ fp))

  dispatchShare-go : ∀ (J : ℕ) (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) → Good J sched st →
    chP? (λ κ → Vb κ J vals) (shareAdmit {t = t} i (EvalSt.registry st)) ≡ true →
    GOK sf id →
    CL (lvls S W d J (dCapᶜ S W R d gas J)) id →
    depthDisp sf gas id now i vals fin sched st ≤ d →
    let ds = dispatchShare {t = t} sf gas id now i vals fin sched st in
    Res J J (dCapᶜ S W R d gas J) (proj₁ ds) (proj₁ (proj₂ ds)) st (proj₂ (proj₂ ds))

  shareGo-go : ∀ (J : ℕ) (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (ps : List (RegId × Path Γ (lookup Γ i) t))
    (sched : Sched Γ) (st : EvalSt e) → Good J sched st →
    chP? (Pb J) ps ≡ true → chP? (λ κ → Vb κ J vals) ps ≡ true →
    GOK sf id →
    CL (lvls S W d J (dWalkᶜ S W R d gas J (length ps))) id →
    depthShareGo sf gas id now i vals fin ps sched st ≤ d →
    chP? (Ob sched st) ps ≡ true →
    let sg = shareGo sf gas id now i vals fin ps sched st in
    Res J J (dWalkᶜ S W R d gas J (length ps))
          (proj₁ sg) (proj₁ (proj₂ sg)) st (proj₂ (proj₂ sg))

  ----------------------------------------------------------------
  -- foldPath: root is a stop, a sink is a dispatch, and a frame is one
  -- `sf-step` followed by the rest of the chain AT THE LEVEL THE FRAME
  -- LEFT — which is the whole repair, in one line.
  ----------------------------------------------------------------

  foldPath-go J sf gas id now envSrc root vals evs fin sched st g hP hV hE _ _ _ _ =
    res J ≤-refl
        (≤-trans (≤-reflexive refl)
                 (lvls-infl S W d J (delivN st st)))
        g
        (≤-trans (≤-reflexive (foldPath-root-N sf gas id now envSrc vals evs fin sched st))
                 z≤n)
        (b-deliv J id envSrc evs vals fin hE hV)

  -- `depthFold … (share-sink i) … = depthDisp …` definitionally, so the
  -- depth premise passes through unchanged.  The stream of
  -- `foldPath … (share-sink i) …` is `envelope ∷ proj₁ ds` where
  -- envelope is the handoff-carrying header and `proj₁ ds` is
  -- dispatchShare's stream, so the burst is `b-app` of the envelope
  -- (from `b-handoff`) and `Res.burst DS`.
  -- `pathLen (share-sink i) = 0` and `iterL … zero J = J`, so the
  -- ceiling premise is dispatchShare-go's VERBATIM
  foldPath-go J sf gas id now envSrc (share-sink i) vals evs fin sched st g hP hV hE gk hC hD _ =
    res (Res.lvl DS) (Res.lo DS) (Res.hi DS) (Res.good DS) (Res.cnt DS)
      (b-app (Res.lvl DS) (envelope ∷ []) (proj₁ ds)
        (b-widen (Res.lo DS) (envelope ∷ [])
                 (b-handoff J id envSrc evs i hE))
        (Res.burst DS))
    where
    ds       = dispatchShare {t = t} sf gas id now i vals fin sched st
    DS       = dispatchShare-go J sf gas id now i vals fin sched st g
                 (v-fan J i vals sched st (proj₁ g) hV) gk hC hD
    envelope = (evs ++ handoff (toℕ i) ∷ []) at id from envSrc as delivery

  foldPath-go J sf gas id now envSrc (f ↠ path′) vals evs fin sched st (ok , len) hP hV hE gk hC hD hOb =
    res (Res.lvl IH) (≤-trans (m≤m+n J j′) (Res.lo IH))
        (≤-trans (Res.hi IH)
                 (≤-trans (lvls-mono (delivN st₁ (proj₂ (proj₂ fp)))
                             (delivN st₁ (proj₂ (proj₂ fp)))
                             2≤S ≤-refl ≤-refl step ≤-refl)
                          (≤-reflexive (cong (lvls S W d (iterL S W d (suc (pathLen path′)) J))
                                             (sym eqD)))))
        (Res.good IH)
        (≤-trans (≤-reflexive eqD)
                 (≤-trans (Res.cnt IH)
                          (dCapᶜ-mono gas gas 2≤S ≤-refl ≤-refl ≤-refl ≤-refl step)))
        (Res.burst IH)
    where
    r   = stepFrame sf id now f path′ vals fin sched st
    -- `depthFold … (f ↠ path′) … = dF ⊔ dR`, and the tail's arguments
    -- below are LITERALLY the ones `IH` recurses with, so both halves
    -- are one ⊔-projection away.  BOUNDS NAMED ON PURPOSE — see the
    -- `lub3` header in .Caps-Depth: `_⊔_` is a defined recursive
    -- function, so an unnamed bound turns the projection into an
    -- inversion Agda cannot solve
    dF  = depthFrame sf id now f path′ vals fin sched st
    -- projections spelled out rather than via `sd₁`/`st₁`: a `where`
    -- block is not mutual, and those two are bound further down
    dR  = depthFold sf gas id now envSrc path′ (proj₁ r) (evs ++ proj₁ (proj₂ r))
            (proj₁ (proj₂ (proj₂ r)))
            (proj₁ (proj₂ (proj₂ (proj₂ r)))) (proj₂ (proj₂ (proj₂ (proj₂ r))))
    -- the frame's ceiling: `fLvlD J` sits under the head's own iterL rung
    -- (`iterL (suc k) J = iterL k (fLvlD J)` definitionally), then under
    -- the level cap by inflation
    hC-f : CL (fLvlD S W d J) id
    hC-f = cl-anti id
             (≤-trans (iterL-infl S W d (pathLen path′) (fLvlD S W d J))
                      (lvls-infl S W d (iterL S W d (suc (pathLen path′)) J)
                         (dCapᶜ S W R d gas (iterL S W d (suc (pathLen path′)) J))))
             hC
    SF  = sf-step J sf id now f path′ vals fin sched st ok hP hV len gk hC-f
            (≤-trans (m≤m⊔n dF dR) hD) hOb
    j′  = proj₁ SF
    st₁ = proj₂ (proj₂ (proj₂ (proj₂ r)))
    sd₁ = proj₁ (proj₂ (proj₂ (proj₂ r)))
    fp  = foldPath sf gas id now envSrc path′ (proj₁ r)
            (evs ++ proj₁ (proj₂ r)) (proj₁ (proj₂ (proj₂ r))) sd₁ st₁
    -- the tail runs at `J + j′`, and one frame of budget covers it —
    -- the frame LEAVES its level under one `fLvlD`, which is exactly
    -- what one step of `iterL` spends (.Caps, the refreshed level).  The
    -- face reports the landing level rather than the receipt alone,
    -- because a frame that SUBSCRIBES costs more than `fCharge`
    step : iterL S W d (pathLen path′) (J + j′) ≤ iterL S W d (suc (pathLen path′)) J
    step = iterL-mono (pathLen path′) (pathLen path′) 2≤S ≤-refl ≤-refl
             (proj₁ (proj₂ SF)) ≤-refl
    -- the tail's ceiling: restrict along `step`, the same monotone rung
    -- the receipts climb
    hC-IH : CL (lvls S W d (iterL S W d (pathLen path′) (J + j′))
                  (dCapᶜ S W R d gas (iterL S W d (pathLen path′) (J + j′)))) id
    hC-IH = cl-anti id
              (lvls-mono (dCapᶜ S W R d gas (iterL S W d (pathLen path′) (J + j′)))
                         (dCapᶜ S W R d gas (iterL S W d (suc (pathLen path′)) J))
                         2≤S ≤-refl ≤-refl step
                         (dCapᶜ-mono gas gas 2≤S ≤-refl ≤-refl ≤-refl ≤-refl step))
              hC
    -- IH's Eb premise: widen hE to J+j′, then append the frame's own
    -- events using sf-step's new last conjunct
    hE-IH : Eb (J + j′) (evs ++ proj₁ (proj₂ r)) ≡ true
    hE-IH = e-app (J + j′) evs (proj₁ (proj₂ r))
                  (e-widen (m≤m+n J j′) evs hE)
                  (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SF))))))
    IH = foldPath-go (J + j′) sf gas id now envSrc path′ (proj₁ r)
           (evs ++ proj₁ (proj₂ r)) (proj₁ (proj₂ (proj₂ r))) sd₁ st₁
           ( proj₁ (proj₂ (proj₂ SF))
           , proj₁ (proj₂ (proj₂ (proj₂ (proj₂ SF)))) )
           (p-widen (m≤m+n J j′) path′ (p-tail J f path′ hP))
           (proj₁ (proj₂ (proj₂ (proj₂ SF))))
           hE-IH gk hC-IH
           (≤-trans (m≤n⊔m dF dR) hD)
           (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SF))))))
    eqD : delivN st (proj₂ (proj₂ fp)) ≡ delivN st₁ (proj₂ (proj₂ fp))
    eqD = foldPath-frame-N sf gas id now envSrc f path′ vals evs fin sched st

  ----------------------------------------------------------------
  -- dispatchShare: out of gas nothing happens; with gas, the share
  -- fan-out is a walk over the registry AS OF NOW, and the level says
  -- how long that is (`ok-reg`, capsOK?'s own fifth conjunct)
  ----------------------------------------------------------------

  dispatchShare-go J sf zero id now i vals fin sched st g hV _ _ _ =
    res J ≤-refl (lvls-infl S W d J (delivN st st)) g
        (≤-reflexive (dispatchShare-zero-N sf id now i vals fin sched st))
        (b-nil J)

  -- `depthDisp sf (suc gas) … = depthShareGo sf gas … (shareAdmit …)
  -- sched (shareLatch i fin st)`, which is exactly `GO`'s argument list.
  -- shareFinish returns the emits stream UNCHANGED in both branches, so
  -- `proj₁ (dispatchShare … (suc gas) …) = proj₁ out = proj₁ GO_stream`,
  -- and `Res.burst GO` is exactly the burst for the outer Res
  dispatchShare-go J sf (suc gas) id now i vals fin sched st (ok , len) hV gk hC hD =
    res (Res.lvl GO) (Res.lo GO)
        (≤-trans (Res.hi GO)
                 (≤-reflexive (cong (lvls S W d J) (sym eqD))))
        ( ok-finish (Res.lvl GO) i fin out (proj₁ (Res.good GO))
        , shareFinish-regP (Pb (Res.lvl GO)) i fin out (proj₂ (Res.good GO)) )
        (≤-trans (≤-reflexive eqD)
                 (≤-trans (Res.cnt GO)
                          (dWalkᶜ-mono gas gas (length (shareAdmit i (EvalSt.registry st)))
                             (regAt S R J) 2≤S ≤-refl ≤-refl ≤-refl ≤-refl ≤-refl
                             (≤-trans (shareAdmit-len i (EvalSt.registry st))
                                      (ok-reg J sched st ok)))))
        (subst (λ s → Bb (Res.lvl GO) s ≡ true)
               (sym (shareFinish-emits i fin out))
               (Res.burst GO))
    where
    stL = shareLatch i fin st
    out = shareGo sf gas id now i vals fin
            (shareAdmit i (EvalSt.registry st)) sched stL
    eqD : delivN st (proj₂ (proj₂ (dispatchShare {t = t} sf (suc gas) id now i vals fin sched st)))
            ≡ delivN stL (proj₂ (proj₂ out))
    eqD = dispatchShare-suc-N sf gas id now i vals fin sched st
    GO : Res J J (dWalkᶜ S W R d gas J (length (shareAdmit i (EvalSt.registry st))))
                 (proj₁ out) (proj₁ (proj₂ out)) stL (proj₂ (proj₂ out))
    -- the fan-out's ceiling: `dCapᶜ (suc gas) J` IS `dWalkᶜ gas J (regAt S R J)`
    -- definitionally, so restricting to the admitted sublist's length is one
    -- dWalkᶜ-mono — the cnt transport above, premise-directed
    hC-GO : CL (lvls S W d J (dWalkᶜ S W R d gas J
                  (length (shareAdmit i (EvalSt.registry st))))) id
    hC-GO = cl-anti id
              (lvls-mono (dWalkᶜ S W R d gas J (length (shareAdmit i (EvalSt.registry st))))
                         (dWalkᶜ S W R d gas J (regAt S R J))
                         2≤S ≤-refl ≤-refl ≤-refl
                         (dWalkᶜ-mono gas gas (length (shareAdmit i (EvalSt.registry st)))
                            (regAt S R J) 2≤S ≤-refl ≤-refl ≤-refl ≤-refl ≤-refl
                            (≤-trans (shareAdmit-len i (EvalSt.registry st))
                                     (ok-reg J sched st ok))))
              hC
    GO = shareGo-go J sf gas id now i vals fin
           (shareAdmit i (EvalSt.registry st)) sched stL
           ( ok-latch J i fin sched st ok
           , subst (λ rs → regP? (Pb J) rs ≡ true) (sym (shareLatch-reg i fin st)) len )
           (shareAdmit-chP (Pb J) i (EvalSt.registry st) len) hV gk hC-GO hD
           (o-fan J i fin sched st ok)

  ----------------------------------------------------------------
  -- shareGo: one delivery per uncancelled registration, each a chain
  -- fold at the level the deliveries before it left — `dWalkᶜ-front` is
  -- the identity that says the definition's back-to-front recursion and
  -- the evaluator's front-to-back fold agree exactly.
  ----------------------------------------------------------------

  shareGo-go J sf gas id now i vals fin [] sched st g hp hV _ _ _ _ =
    res J ≤-refl (lvls-infl S W d J (delivN st st)) g
        (≤-reflexive (delivN-≡ st st refl))
        (b-nil J)

  -- THE THREE-CALLEE CLAUSE.  `depthShareGo`'s cons clause is branch-free
  -- `dSK ⊔ (dFP ⊔ dREST)` precisely so this `with` cannot strand the
  -- premise (a with-abstraction does not rewrite a bound hypothesis's
  -- type), and `lub3-l/m/r` read the three summands back out — one per
  -- callee, with the bounds named as that header requires
  shareGo-go J sf gas id now i vals fin ((rid , p) ∷ ps) sched st g hp hV gk hC hD hOb
    with any (_≡ᵇ rid) (EvalSt.cancelled st)
  ... | true  =
        -- when cancelled, shareGo recurses on ps with the same state —
        -- definitionally `proj₁ (shareGo … ((rid,p)∷ps) … | true)
        --   = proj₁ (shareGo … ps …)`, so `Res.burst SK` is the burst
        res (Res.lvl SK) (Res.lo SK) (Res.hi SK) (Res.good SK)
            (≤-trans (Res.cnt SK)
                     (dWalkᶜ-mono gas gas (length ps) (suc (length ps))
                        2≤S ≤-refl ≤-refl ≤-refl ≤-refl ≤-refl (n≤1+n (length ps))))
            (Res.burst SK)
        where
        -- spelled out only to NAME the three ⊔ bounds; the skip branch
        -- reaches none of the other two
        evs₀  = if fin then close (toℕ i) exhausted ∷ [] else []
        st₀   = consᵈ rid st
        fp    = foldPath sf gas id now (toℕ i) p vals evs₀ fin sched st₀
        dSK   = depthShareGo sf gas id now i vals fin ps sched st
        dFP   = depthFold sf gas id now (toℕ i) p vals evs₀ fin sched st₀
        dREST = depthShareGo sf gas id now i vals fin ps
                  (proj₁ (proj₂ fp)) (proj₂ (proj₂ fp))
        SK = shareGo-go J sf gas id now i vals fin ps sched st g
               (proj₂ (∧-true _ _ hp)) (proj₂ (∧-true _ _ hV)) gk
               (cl-anti id
                  (lvls-mono (dWalkᶜ S W R d gas J (length ps))
                     (dWalkᶜ S W R d gas J (suc (length ps)))
                     2≤S ≤-refl ≤-refl ≤-refl
                     (dWalkᶜ-mono gas gas (length ps) (suc (length ps))
                        2≤S ≤-refl ≤-refl ≤-refl ≤-refl ≤-refl (n≤1+n (length ps))))
                  hC)
               (lub3-l dSK dFP dREST hD)
               (proj₂ (∧-true _ _ hOb))
  ... | false =
        -- output is `proj₁ fp ++ proj₁ rest`; burst is b-app of
        -- b-widen (Res.lo REST) applied to Res.burst FP, and Res.burst REST
        res (Res.lvl REST) (≤-trans (Res.lo FP) (Res.lo REST))
            (≤-trans (Res.hi REST)
               (≤-trans (lvls-mono D₂ D₂ 2≤S ≤-refl ≤-refl J₁≤ ≤-refl)
                  (≤-trans (≤-reflexive (sym (lvls-add S W d J (suc D₁) D₂)))
                           (≤-reflexive (cong (lvls S W d J) (sym eqN))))))
            (Res.good REST)
            (≤-trans (≤-reflexive eqN)
               (≤-trans (s≤s (+-mono-≤ D₁≤A restCnt))
                        (≤-reflexive (sym (dWalkᶜ-front S W R d gas J (length ps))))))
            (b-app (Res.lvl REST) (proj₁ fp) (proj₁ rest)
              (b-widen (Res.lo REST) (proj₁ fp) (Res.burst FP))
              (Res.burst REST))
        where
        st₀ = consᵈ rid st
        evs₀ = if fin then close (toℕ i) exhausted ∷ [] else []
        -- Eb premise for foldPath-go: case on fin to pick e-close or e-nil
        hE₀ : Eb J evs₀ ≡ true
        hE₀ = eb-seed J (toℕ i) fin
        fp  = foldPath sf gas id now (toℕ i) p vals evs₀ fin sched st₀
        st₁ = proj₂ (proj₂ fp)
        dSK   = depthShareGo sf gas id now i vals fin ps sched st
        dFP   = depthFold sf gas id now (toℕ i) p vals evs₀ fin sched st₀
        dREST = depthShareGo sf gas id now i vals fin ps (proj₁ (proj₂ fp)) st₁
        A   = dCapᶜ S W R d gas (lvls S W d J 1)
        -- one chain is at most `suc (sizeAt S J)` frames, so its frames
        -- fit inside ONE delivery's level charge
        chain≤ : iterL S W d (pathLen p) J ≤ lvls S W d J 1
        chain≤ = iterL-mono (pathLen p) (suc (sizeAt S J)) 2≤S ≤-refl ≤-refl ≤-refl
                   (≤-trans (p-len J p (proj₁ (∧-true _ _ hp))) (n≤1+n (sizeAt S J)))
        -- the head chain's ceiling: its whole level cap sits under ONE
        -- delivery's charge (`chain≤`), peeled off the front of the walk's
        -- cap by `dWalkᶜ-front` — the cnt receipt's arithmetic, premise-directed
        hC-FP : CL (lvls S W d (iterL S W d (pathLen p) J)
                      (dCapᶜ S W R d gas (iterL S W d (pathLen p) J))) id
        hC-FP = cl-anti id
                  (≤-trans (lvls-mono (dCapᶜ S W R d gas (iterL S W d (pathLen p) J)) A
                              2≤S ≤-refl ≤-refl chain≤
                              (dCapᶜ-mono gas gas 2≤S ≤-refl ≤-refl ≤-refl ≤-refl chain≤))
                     (≤-trans (≤-reflexive (sym (lvls-add S W d J 1 A)))
                        (≤-trans (lvls-mono (suc A)
                                    (suc (A + dWalkᶜ S W R d gas (lvls S W d J (suc A)) (length ps)))
                                    2≤S ≤-refl ≤-refl ≤-refl
                                    (s≤s (m≤m+n A (dWalkᶜ S W R d gas (lvls S W d J (suc A)) (length ps)))))
                           (≤-reflexive (cong (lvls S W d J)
                              (sym (dWalkᶜ-front S W R d gas J (length ps))))))))
                  hC
        FP  = foldPath-go J sf gas id now (toℕ i) p vals evs₀ fin sched st₀
                ( ok-cons J rid sched st (proj₁ g) , proj₂ g )
                (proj₁ (∧-true _ _ hp)) (proj₁ (∧-true _ _ hV)) hE₀ gk hC-FP
                (lub3-m dSK dFP dREST hD)
                (o-cons rid sched st p (proj₁ (∧-true _ _ hOb)))
        J₁  = Res.lvl FP
        rest = shareGo sf gas id now i vals fin ps (proj₁ (proj₂ fp)) st₁
        st₂ = proj₂ (proj₂ rest)
        D₁  = delivN st₀ st₁
        D₂  = delivN st₁ st₂
        J₁≤ : J₁ ≤ lvls S W d J (suc D₁)
        J₁≤ = ≤-trans (Res.hi FP)
                (≤-trans (lvls-mono D₁ D₁ 2≤S ≤-refl ≤-refl chain≤ ≤-refl)
                         (≤-reflexive (sym (lvls-add S W d J 1 D₁))))
        D₁≤A : D₁ ≤ A
        D₁≤A = ≤-trans (Res.cnt FP)
                 (dCapᶜ-mono gas gas 2≤S ≤-refl ≤-refl ≤-refl ≤-refl chain≤)
        -- the tail's ceiling: J₁ fits under `lvls J (suc A)` (the head's
        -- delivery charge, `J₁≤` + `D₁≤A`), and the rest of the walk's cap
        -- re-fuses under the front peel by `lvls-add`
        J₁≤JA : J₁ ≤ lvls S W d J (suc A)
        J₁≤JA = ≤-trans J₁≤ (lvls-mono (suc D₁) (suc A) 2≤S ≤-refl ≤-refl ≤-refl (s≤s D₁≤A))
        hC-REST : CL (lvls S W d J₁ (dWalkᶜ S W R d gas J₁ (length ps))) id
        hC-REST = cl-anti id
                    (≤-trans (lvls-mono (dWalkᶜ S W R d gas J₁ (length ps))
                                (dWalkᶜ S W R d gas (lvls S W d J (suc A)) (length ps))
                                2≤S ≤-refl ≤-refl J₁≤JA
                                (dWalkᶜ-mono gas gas (length ps) (length ps)
                                   2≤S ≤-refl ≤-refl ≤-refl ≤-refl J₁≤JA ≤-refl))
                       (≤-trans (≤-reflexive (sym (lvls-add S W d J (suc A)
                                    (dWalkᶜ S W R d gas (lvls S W d J (suc A)) (length ps)))))
                          (≤-reflexive (cong (lvls S W d J)
                             (sym (dWalkᶜ-front S W R d gas J (length ps)))))))
                    hC
        REST = shareGo-go J₁ sf gas id now i vals fin ps (proj₁ (proj₂ fp)) st₁
                 (Res.good FP)
                 (chP?-widen (Res.lo FP) ps (proj₂ (∧-true _ _ hp)))
                 (chV?-widen (Res.lo FP) vals ps (proj₂ (∧-true _ _ hV)))
                 gk hC-REST (lub3-r dSK dFP dREST hD)
                 (o-fold sf gas id now (toℕ i) p vals evs₀ fin sched st₀ ps
                    (chOb-cons rid sched st ps (proj₂ (∧-true _ _ hOb))))
        restCnt : D₂ ≤ dWalkᶜ S W R d gas (lvls S W d J (suc A)) (length ps)
        restCnt = ≤-trans (Res.cnt REST)
                    (dWalkᶜ-mono gas gas (length ps) (length ps) 2≤S ≤-refl ≤-refl ≤-refl
                       ≤-refl (≤-trans J₁≤ (lvls-mono (suc D₁) (suc A) 2≤S ≤-refl ≤-refl
                                              ≤-refl (s≤s D₁≤A))) ≤-refl)
        eqN : delivN st st₂ ≡ suc (D₁ + D₂)
        eqN = trans (delivN-cons rid st st₂
                       (⊑ᵈ-trans (foldPath-deliv sf gas id now (toℕ i) p vals evs₀ fin sched st₀)
                                 (shareGo-deliv sf gas id now i vals fin ps
                                    (proj₁ (proj₂ fp)) st₁)))
                    (cong suc (delivN-split
                                 (foldPath-deliv sf gas id now (toℕ i) p vals evs₀ fin sched st₀)
                                 (shareGo-deliv sf gas id now i vals fin ps
                                    (proj₁ (proj₂ fp)) st₁)))

  ----------------------------------------------------------------
  -- (ii) THE CASCADE, one level up: the same walk with `chainStep` in
  -- place of the share fan-out and the dispatch gas at its seed, `n`.
  ----------------------------------------------------------------

  cascadeGo-go : ∀ (J : ℕ) (a : Arrival Γ) (id : Id)
    (chains : List (RegId × Path Γ (arrTy a) t))
    (sched : Sched Γ) (st : EvalSt e) → Good J sched st →
    chP? (Pb J) chains ≡ true →
    chP? (λ κ → Vb κ J (arrVal a ∷ [])) chains ≡ true →
    CL (lvls S W d J (dWalkᶜ S W R d n J (length chains))) id →
    depthCascade a id chains sched st ≤ d →
    chP? (Ob sched st) chains ≡ true →
    let cg = cascadeGo a id chains sched st in
    Res J J (dWalkᶜ S W R d n J (length chains))
          (proj₁ cg) (proj₁ (proj₂ cg)) st (proj₂ (proj₂ cg))

  cascadeGo-go J a id [] sched st g hp hV _ _ _ =
    res J ≤-refl (lvls-infl S W d J (delivN st st)) g
        (≤-reflexive (delivN-≡ st st refl))
        (b-nil J)

  -- same three-callee shape as `shareGo-go`, and `depthCascade` is
  -- branch-free for the same reason: this `with` would otherwise strand
  -- the premise on the unabstracted cancellation test
  cascadeGo-go J a id ((rid , c) ∷ chains) sched st g hp hV hC hD hOb
    with any (_≡ᵇ rid) (EvalSt.cancelled st)
  ... | true  =
        -- cancelled: output = proj₁ (cascadeGo … chains …) = proj₁ SK_stream
        res (Res.lvl SK) (Res.lo SK) (Res.hi SK) (Res.good SK)
            (≤-trans (Res.cnt SK)
                     (dWalkᶜ-mono n n (length chains) (suc (length chains))
                        2≤S ≤-refl ≤-refl ≤-refl ≤-refl ≤-refl (n≤1+n (length chains))))
            (Res.burst SK)
        where
        st₀   = consᵈ rid st
        cs    = chainStep id a c sched st₀
        dSK   = depthCascade a id chains sched st
        dFP   = depthChain id a c sched st₀
        dREST = depthCascade a id chains (proj₁ (proj₂ cs)) (proj₂ (proj₂ cs))
        SK = cascadeGo-go J a id chains sched st g (proj₂ (∧-true _ _ hp))
               (proj₂ (∧-true _ _ hV))
               (cl-anti id
                  (lvls-mono (dWalkᶜ S W R d n J (length chains))
                     (dWalkᶜ S W R d n J (suc (length chains)))
                     2≤S ≤-refl ≤-refl ≤-refl
                     (dWalkᶜ-mono n n (length chains) (suc (length chains))
                        2≤S ≤-refl ≤-refl ≤-refl ≤-refl ≤-refl (n≤1+n (length chains))))
                  hC)
               (lub3-l dSK dFP dREST hD)
               (proj₂ (∧-true _ _ hOb))
  ... | false =
        -- output is `proj₁ cs ++ proj₁ rest`; burst is b-app of
        -- b-widen (Res.lo REST) applied to Res.burst FP, and Res.burst REST
        res (Res.lvl REST) (≤-trans (Res.lo FP) (Res.lo REST))
            (≤-trans (Res.hi REST)
               (≤-trans (lvls-mono D₂ D₂ 2≤S ≤-refl ≤-refl J₁≤ ≤-refl)
                  (≤-trans (≤-reflexive (sym (lvls-add S W d J (suc D₁) D₂)))
                           (≤-reflexive (cong (lvls S W d J) (sym eqN))))))
            (Res.good REST)
            (≤-trans (≤-reflexive eqN)
               (≤-trans (s≤s (+-mono-≤ D₁≤A restCnt))
                        (≤-reflexive (sym (dWalkᶜ-front S W R d n J (length chains))))))
            (b-app (Res.lvl REST) (proj₁ cs) (proj₁ rest)
              (b-widen (Res.lo REST) (proj₁ cs) (Res.burst FP))
              (Res.burst REST))
        where
        st₀  = consᵈ rid st
        sf₀  = budgetAt e (Sched.slots sched) id
        evs₀ = if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else []
        -- Eb premise for foldPath-go: case on isLast for e-close or e-nil
        hE₀ : Eb J evs₀ ≡ true
        hE₀ = eb-seed J (arrSource a) (Arrival.isLast a)
        cs   = chainStep id a c sched st₀
        st₁  = proj₂ (proj₂ cs)
        rest = cascadeGo a id chains (proj₁ (proj₂ cs)) st₁
        -- `depthChain` IS this `depthFold` — same `sf₀`, same `evs₀` —
        -- so the middle projection lands on `FP`'s premise definitionally
        dSK   = depthCascade a id chains sched st
        dFP   = depthChain id a c sched st₀
        dREST = depthCascade a id chains (proj₁ (proj₂ cs)) st₁
        -- THE MINT: sf₀ IS `budgetAt e (Sched.slots sched) id`, so
        -- g-mint at the incoming OK supplies its GOK verbatim
        gk₀  : GOK sf₀ id
        gk₀  = g-mint J id sched st (proj₁ g)
        A    = dCapᶜ S W R d n (lvls S W d J 1)
        chain≤ : iterL S W d (pathLen c) J ≤ lvls S W d J 1
        chain≤ = iterL-mono (pathLen c) (suc (sizeAt S J)) 2≤S ≤-refl ≤-refl ≤-refl
                   (≤-trans (p-len J c (proj₁ (∧-true _ _ hp))) (n≤1+n (sizeAt S J)))
        -- head/tail ceilings: shareGo-go's front-peel arithmetic, at gas = n
        hC-FP : CL (lvls S W d (iterL S W d (pathLen c) J)
                      (dCapᶜ S W R d n (iterL S W d (pathLen c) J))) id
        hC-FP = cl-anti id
                  (≤-trans (lvls-mono (dCapᶜ S W R d n (iterL S W d (pathLen c) J)) A
                              2≤S ≤-refl ≤-refl chain≤
                              (dCapᶜ-mono n n 2≤S ≤-refl ≤-refl ≤-refl ≤-refl chain≤))
                     (≤-trans (≤-reflexive (sym (lvls-add S W d J 1 A)))
                        (≤-trans (lvls-mono (suc A)
                                    (suc (A + dWalkᶜ S W R d n (lvls S W d J (suc A)) (length chains)))
                                    2≤S ≤-refl ≤-refl ≤-refl
                                    (s≤s (m≤m+n A (dWalkᶜ S W R d n (lvls S W d J (suc A)) (length chains)))))
                           (≤-reflexive (cong (lvls S W d J)
                              (sym (dWalkᶜ-front S W R d n J (length chains))))))))
                  hC
        FP   = foldPath-go J sf₀ n id (arrTick a) (arrSource a) c (arrVal a ∷ [])
                 evs₀ (Arrival.isLast a) sched st₀
                 ( ok-cons J rid sched st (proj₁ g) , proj₂ g )
                 (proj₁ (∧-true _ _ hp)) (proj₁ (∧-true _ _ hV)) hE₀ gk₀ hC-FP
                 (lub3-m dSK dFP dREST hD)
                 (o-cons rid sched st c (proj₁ (∧-true _ _ hOb)))
        J₁   = Res.lvl FP
        st₂  = proj₂ (proj₂ rest)
        D₁   = delivN st₀ st₁
        D₂   = delivN st₁ st₂
        J₁≤ : J₁ ≤ lvls S W d J (suc D₁)
        J₁≤ = ≤-trans (Res.hi FP)
                (≤-trans (lvls-mono D₁ D₁ 2≤S ≤-refl ≤-refl chain≤ ≤-refl)
                         (≤-reflexive (sym (lvls-add S W d J 1 D₁))))
        D₁≤A : D₁ ≤ A
        D₁≤A = ≤-trans (Res.cnt FP)
                 (dCapᶜ-mono n n 2≤S ≤-refl ≤-refl ≤-refl ≤-refl chain≤)
        J₁≤JA : J₁ ≤ lvls S W d J (suc A)
        J₁≤JA = ≤-trans J₁≤ (lvls-mono (suc D₁) (suc A) 2≤S ≤-refl ≤-refl ≤-refl (s≤s D₁≤A))
        hC-REST : CL (lvls S W d J₁ (dWalkᶜ S W R d n J₁ (length chains))) id
        hC-REST = cl-anti id
                    (≤-trans (lvls-mono (dWalkᶜ S W R d n J₁ (length chains))
                                (dWalkᶜ S W R d n (lvls S W d J (suc A)) (length chains))
                                2≤S ≤-refl ≤-refl J₁≤JA
                                (dWalkᶜ-mono n n (length chains) (length chains)
                                   2≤S ≤-refl ≤-refl ≤-refl ≤-refl J₁≤JA ≤-refl))
                       (≤-trans (≤-reflexive (sym (lvls-add S W d J (suc A)
                                    (dWalkᶜ S W R d n (lvls S W d J (suc A)) (length chains)))))
                          (≤-reflexive (cong (lvls S W d J)
                             (sym (dWalkᶜ-front S W R d n J (length chains)))))))
                    hC
        REST = cascadeGo-go J₁ a id chains (proj₁ (proj₂ cs)) st₁
                 (Res.good FP)
                 (chP?-widen (Res.lo FP) chains (proj₂ (∧-true _ _ hp)))
                 (chV?-widen (Res.lo FP) (arrVal a ∷ []) chains (proj₂ (∧-true _ _ hV)))
                 hC-REST (lub3-r dSK dFP dREST hD)
                 (o-chain id a c sched st₀ chains
                    (chOb-cons rid sched st chains (proj₂ (∧-true _ _ hOb))))
        restCnt : D₂ ≤ dWalkᶜ S W R d n (lvls S W d J (suc A)) (length chains)
        restCnt = ≤-trans (Res.cnt REST)
                    (dWalkᶜ-mono n n (length chains) (length chains) 2≤S ≤-refl ≤-refl ≤-refl
                       ≤-refl (≤-trans J₁≤ (lvls-mono (suc D₁) (suc A) 2≤S ≤-refl ≤-refl
                                              ≤-refl (s≤s D₁≤A))) ≤-refl)
        eqN : delivN st st₂ ≡ suc (D₁ + D₂)
        eqN = trans (delivN-cons rid st st₂
                       (⊑ᵈ-trans (chainStep-deliv id a c sched st₀)
                                 (cascadeGo-deliv a id chains (proj₁ (proj₂ cs)) st₁)))
                    (cong suc (delivN-split (chainStep-deliv id a c sched st₀)
                                 (cascadeGo-deliv a id chains (proj₁ (proj₂ cs)) st₁)))
