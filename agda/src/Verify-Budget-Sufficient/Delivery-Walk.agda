-- STRATUM 0b of Verify-Budget-Sufficient: THE DELIVERY WALK FITS dCapᶜ.
--
-- .Deliveries proved WHERE the ledger moves (§ B–§ E) and turned the
-- delivery recurrence into nine proven equations (§ D).  This module
-- consumes those equations and maps the evaluator's delivery clique
-- onto the well-founded walk `dCapᶜ` / `dWalkᶜ` (.Caps):
--
--     foldPath      sf gas … path …  ↦  dCapᶜ  S W R gas J
--     dispatchShare sf gas … i …     ↦  dCapᶜ  S W R gas J
--     shareGo       sf gas … ps …    ↦  dWalkᶜ S W R gas J (length ps)
--     cascadeGo     a id chains …    ↦  dWalkᶜ S W R n   J (length chains)
--
-- with J the CAPS LEVEL at the call's entry state.  That is the
-- 2026-08-02 repair, and it is forced: the walk used to thread a
-- REGISTRY and charge each delivery a fixed `Q` read once at the
-- cascade's entry caps, and charging anything per-frame at the entry
-- caps is machine-refuted (agda/probe/Entry-Caps-Refuted.agda — one
-- `map-f` frame's output breaches the very cap it was charged at,
-- because `applyFn` grows a value).  The honest per-frame face is the
-- PROVEN `stepFrame-caps`, which REPORTS its growth as an index j′ and
-- lands at `frameStep (j + j′) c`, so the walk carries that index.
--
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
--
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
--
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
open import Data.Nat     using (ℕ; zero; suc; _+_; _*_; _≤_; _≤ᵇ_; _≡ᵇ_;
                                z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; ≤-refl; ≤-reflexive;
                                       +-mono-≤; *-mono-≤; +-monoˡ-≤;
                                       +-monoʳ-≤; *-monoʳ-≤; *-monoˡ-≤;
                                       +-assoc; +-comm; +-identityʳ;
                                       *-identityʳ; *-zeroʳ; *-distribˡ-+;
                                       ≤ᵇ⇒≤; n≤1+n; m≤m+n; m≤n+m)
open import Data.List    using (List; []; _∷_; _++_; length; all; any; map)
open import Data.Fin     using (Fin; toℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Vec     using (lookup)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Rx.Prim      using (Tick; Id; Source; InstEvent; close; exhausted;
                                Gas)
open import Rx.Exp       using (Ty; Ctx; Closed; Val; _≟ᵗ_)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; RegId; Chain;
                                Path; Frame; root; share-sink; _↠_; Stream;
                                stepFrame; foldPath; dispatchShare; shareGo;
                                shareAdmit; shareLatch; shareFinish;
                                chainStep; cascadeGo; dropSource; sameSource;
                                arrTy; arrTick; arrSource; arrVal;
                                budgetAt;
                                sizeAt; regAt; fCharge; iterL; lvls;
                                dCapᶜ; dWalkᶜ)

-- .Caps for the level walk and its monotonicity toolkit (dCapᶜ-mono /
-- dWalkᶜ-mono / lvls-mono) and, under it, .Measures for pathLen and the
-- dropSource lemmas
open import Verify-Budget-Sufficient.Caps public
open import Verify-Budget-Sufficient.Deliveries public

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

------------------------------------------------------------------
-- § C.  THE HYPOTHESES: ONE FRAME, AT THE LEVEL IT RUNS AT.
--
-- Everything below is proven from ONE fact about `stepFrame` — it
-- reports a growth index j′ inside the per-frame receipt `fCharge S W J`
-- and lands its post-state, its output burst and the registry's ledger
-- at level `J + j′` — plus the three closure facts the walk's own
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
-- (agda/probe/Entry-Caps-Refuted.agda).
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

record Walk-Hyps {n} {Γ : Ctx n} {t} (e : Closed Γ t) (S W R : ℕ) : Set₁ where
  field
    OK : ℕ → Sched Γ → EvalSt e → Set

    -- the two syntactic side conditions, now READ AT A LEVEL
    Pb : ℕ → ∀ {u} → Path Γ u t → Bool
    Vb : ℕ → ∀ {s} → List (Val Γ s) → Bool

    -- the level's two ledger readings: a chain is shorter than the size
    -- cap, and the registry is shorter than the registration cap
    p-len : ∀ (J : ℕ) {u} (p : Path Γ u t) → Pb J p ≡ true → pathLen p ≤ sizeAt S J
    p-tail : ∀ (J : ℕ) {s u} (f : Frame Γ s u) (p : Path Γ u t) →
             Pb J (f ↠ p) ≡ true → Pb J p ≡ true

    -- and both ledgers widen along the level
    p-widen : ∀ {J J′ : ℕ} → J ≤ J′ → ∀ {u} (p : Path Γ u t) →
              Pb J p ≡ true → Pb J′ p ≡ true
    v-widen : ∀ {J J′ : ℕ} → J ≤ J′ → ∀ {s} (vs : List (Val Γ s)) →
              Vb J vs ≡ true → Vb J′ vs ≡ true

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
      Pb J (f ↠ path′) ≡ true → Vb J vals ≡ true →
      regP? (Pb J) (EvalSt.registry st) ≡ true →
      let r = stepFrame sf id now f path′ vals fin sched st in
      Σ ℕ λ j′ → (j′ ≤ fCharge S W J)
        × OK (J + j′) (proj₁ (proj₂ (proj₂ (proj₂ r))))
                      (proj₂ (proj₂ (proj₂ (proj₂ r))))
        × (Vb (J + j′) (proj₁ r) ≡ true)
        × (regP? (Pb (J + j′))
                 (EvalSt.registry (proj₂ (proj₂ (proj₂ (proj₂ r))))) ≡ true)

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
            (S W R : ℕ) (2≤S : 2 ≤ S) (H : Walk-Hyps e S W R) where

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

  -- WHAT ONE RUN REPORTS.  `lvl` is where it landed, `lo` that it only
  -- climbed, `hi` that it climbed by at most one delivery-charge per
  -- delivery from the level `base` its frames left it at, and `cnt`
  -- that its deliveries fit the walk
  record Res (J base cap : ℕ) (sched′ : Sched Γ) (st st′ : EvalSt e) : Set where
    constructor res
    field
      lvl  : ℕ
      lo   : J ≤ lvl
      hi   : lvl ≤ lvls S W base (delivN st st′)
      good : Good lvl sched′ st′
      cnt  : delivN st st′ ≤ cap

  ----------------------------------------------------------------
  -- (i) THE FOUR WALKS, FUSED: predicate, level and delivery count in
  -- one induction, because the frame fact hands them back together.
  ----------------------------------------------------------------

  foldPath-go : ∀ (J : ℕ) (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
    {u} (path : Path Γ u t) (vals : List (Val Γ u))
    (evs : List (InstEvent (Val Γ t))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) → Good J sched st →
    Pb J path ≡ true → Vb J vals ≡ true →
    let fp = foldPath sf gas id now envSrc path vals evs fin sched st in
    Res J (iterL S W (pathLen path) J)
          (dCapᶜ S W R gas (iterL S W (pathLen path) J))
          (proj₁ (proj₂ fp)) st (proj₂ (proj₂ fp))

  dispatchShare-go : ∀ (J : ℕ) (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) → Good J sched st → Vb J vals ≡ true →
    let ds = dispatchShare {t = t} sf gas id now i vals fin sched st in
    Res J J (dCapᶜ S W R gas J) (proj₁ (proj₂ ds)) st (proj₂ (proj₂ ds))

  shareGo-go : ∀ (J : ℕ) (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (ps : List (RegId × Path Γ (lookup Γ i) t))
    (sched : Sched Γ) (st : EvalSt e) → Good J sched st →
    chP? (Pb J) ps ≡ true → Vb J vals ≡ true →
    let sg = shareGo sf gas id now i vals fin ps sched st in
    Res J J (dWalkᶜ S W R gas J (length ps))
          (proj₁ (proj₂ sg)) st (proj₂ (proj₂ sg))

  ----------------------------------------------------------------
  -- foldPath: root is a stop, a sink is a dispatch, and a frame is one
  -- `sf-step` followed by the rest of the chain AT THE LEVEL THE FRAME
  -- LEFT — which is the whole repair, in one line.
  ----------------------------------------------------------------

  foldPath-go J sf gas id now envSrc root vals evs fin sched st g hP hV =
    res J ≤-refl
        (≤-trans (≤-reflexive refl)
                 (lvls-infl S W J (delivN st st)))
        g
        (≤-trans (≤-reflexive (foldPath-root-N sf gas id now envSrc vals evs fin sched st))
                 z≤n)

  foldPath-go J sf gas id now envSrc (share-sink i) vals evs fin sched st g hP hV =
    dispatchShare-go J sf gas id now i vals fin sched st g hV

  foldPath-go J sf gas id now envSrc (f ↠ path′) vals evs fin sched st (ok , len) hP hV =
    res (Res.lvl IH) (≤-trans (m≤m+n J j′) (Res.lo IH))
        (≤-trans (Res.hi IH)
                 (≤-trans (lvls-mono (delivN st₁ (proj₂ (proj₂ fp)))
                             (delivN st₁ (proj₂ (proj₂ fp)))
                             2≤S ≤-refl ≤-refl step ≤-refl)
                          (≤-reflexive (cong (lvls S W (iterL S W (suc (pathLen path′)) J))
                                             (sym eqD)))))
        (Res.good IH)
        (≤-trans (≤-reflexive eqD)
                 (≤-trans (Res.cnt IH)
                          (dCapᶜ-mono gas gas 2≤S ≤-refl ≤-refl ≤-refl ≤-refl step)))
    where
    r   = stepFrame sf id now f path′ vals fin sched st
    SF  = sf-step J sf id now f path′ vals fin sched st ok hP hV len
    j′  = proj₁ SF
    st₁ = proj₂ (proj₂ (proj₂ (proj₂ r)))
    sd₁ = proj₁ (proj₂ (proj₂ (proj₂ r)))
    fp  = foldPath sf gas id now envSrc path′ (proj₁ r)
            (evs ++ proj₁ (proj₂ r)) (proj₁ (proj₂ (proj₂ r))) sd₁ st₁
    -- the tail runs at `J + j′`, and one frame of budget covers it —
    -- the receipt lands inside `fLvl`, and `fLvl ≤ fLvl′` is what one
    -- step of `iterL` now spends (.Caps, the nesting-budgeted level)
    step : iterL S W (pathLen path′) (J + j′) ≤ iterL S W (suc (pathLen path′)) J
    step = iterL-mono (pathLen path′) (pathLen path′) 2≤S ≤-refl ≤-refl
             (≤-trans (+-monoʳ-≤ J (proj₁ (proj₂ SF))) (fLvl≤fLvl′ S W J)) ≤-refl
    IH = foldPath-go (J + j′) sf gas id now envSrc path′ (proj₁ r)
           (evs ++ proj₁ (proj₂ r)) (proj₁ (proj₂ (proj₂ r))) sd₁ st₁
           ( proj₁ (proj₂ (proj₂ SF))
           , proj₂ (proj₂ (proj₂ (proj₂ SF))) )
           (p-widen (m≤m+n J j′) path′ (p-tail J f path′ hP))
           (proj₁ (proj₂ (proj₂ (proj₂ SF))))
    eqD : delivN st (proj₂ (proj₂ fp)) ≡ delivN st₁ (proj₂ (proj₂ fp))
    eqD = foldPath-frame-N sf gas id now envSrc f path′ vals evs fin sched st

  ----------------------------------------------------------------
  -- dispatchShare: out of gas nothing happens; with gas, the share
  -- fan-out is a walk over the registry AS OF NOW, and the level says
  -- how long that is (`ok-reg`, capsOK?'s own fifth conjunct)
  ----------------------------------------------------------------

  dispatchShare-go J sf zero id now i vals fin sched st g hV =
    res J ≤-refl (lvls-infl S W J (delivN st st)) g
        (≤-reflexive (dispatchShare-zero-N sf id now i vals fin sched st))

  dispatchShare-go J sf (suc gas) id now i vals fin sched st (ok , len) hV =
    res (Res.lvl GO) (Res.lo GO)
        (≤-trans (Res.hi GO)
                 (≤-reflexive (cong (lvls S W J) (sym eqD))))
        ( ok-finish (Res.lvl GO) i fin out (proj₁ (Res.good GO))
        , shareFinish-regP (Pb (Res.lvl GO)) i fin out (proj₂ (Res.good GO)) )
        (≤-trans (≤-reflexive eqD)
                 (≤-trans (Res.cnt GO)
                          (dWalkᶜ-mono gas gas (length (shareAdmit i (EvalSt.registry st)))
                             (regAt S R J) 2≤S ≤-refl ≤-refl ≤-refl ≤-refl ≤-refl
                             (≤-trans (shareAdmit-len i (EvalSt.registry st))
                                      (ok-reg J sched st ok)))))
    where
    stL = shareLatch i fin st
    out = shareGo sf gas id now i vals fin
            (shareAdmit i (EvalSt.registry st)) sched stL
    eqD : delivN st (proj₂ (proj₂ (dispatchShare {t = t} sf (suc gas) id now i vals fin sched st)))
            ≡ delivN stL (proj₂ (proj₂ out))
    eqD = dispatchShare-suc-N sf gas id now i vals fin sched st
    GO : Res J J (dWalkᶜ S W R gas J (length (shareAdmit i (EvalSt.registry st))))
                 (proj₁ (proj₂ out)) stL (proj₂ (proj₂ out))
    GO = shareGo-go J sf gas id now i vals fin
           (shareAdmit i (EvalSt.registry st)) sched stL
           ( ok-latch J i fin sched st ok
           , subst (λ rs → regP? (Pb J) rs ≡ true) (sym (shareLatch-reg i fin st)) len )
           (shareAdmit-chP (Pb J) i (EvalSt.registry st) len) hV

  ----------------------------------------------------------------
  -- shareGo: one delivery per uncancelled registration, each a chain
  -- fold at the level the deliveries before it left — `dWalkᶜ-front` is
  -- the identity that says the definition's back-to-front recursion and
  -- the evaluator's front-to-back fold agree exactly.
  ----------------------------------------------------------------

  shareGo-go J sf gas id now i vals fin [] sched st g hp hV =
    res J ≤-refl (lvls-infl S W J (delivN st st)) g
        (≤-reflexive (delivN-≡ st st refl))

  shareGo-go J sf gas id now i vals fin ((rid , p) ∷ ps) sched st g hp hV
    with any (_≡ᵇ rid) (EvalSt.cancelled st)
  ... | true  =
        res (Res.lvl SK) (Res.lo SK) (Res.hi SK) (Res.good SK)
            (≤-trans (Res.cnt SK)
                     (dWalkᶜ-mono gas gas (length ps) (suc (length ps))
                        2≤S ≤-refl ≤-refl ≤-refl ≤-refl ≤-refl (n≤1+n (length ps))))
        where
        SK = shareGo-go J sf gas id now i vals fin ps sched st g
               (proj₂ (∧-true _ _ hp)) hV
  ... | false =
        res (Res.lvl REST) (≤-trans (Res.lo FP) (Res.lo REST))
            (≤-trans (Res.hi REST)
               (≤-trans (lvls-mono D₂ D₂ 2≤S ≤-refl ≤-refl J₁≤ ≤-refl)
                  (≤-trans (≤-reflexive (sym (lvls-add S W J (suc D₁) D₂)))
                           (≤-reflexive (cong (lvls S W J) (sym eqN))))))
            (Res.good REST)
            (≤-trans (≤-reflexive eqN)
               (≤-trans (s≤s (+-mono-≤ D₁≤A restCnt))
                        (≤-reflexive (sym (dWalkᶜ-front S W R gas J (length ps))))))
        where
        st₀ = consᵈ rid st
        evs₀ = if fin then close (toℕ i) exhausted ∷ [] else []
        fp  = foldPath sf gas id now (toℕ i) p vals evs₀ fin sched st₀
        st₁ = proj₂ (proj₂ fp)
        FP  = foldPath-go J sf gas id now (toℕ i) p vals evs₀ fin sched st₀
                ( ok-cons J rid sched st (proj₁ g) , proj₂ g )
                (proj₁ (∧-true _ _ hp)) hV
        J₁  = Res.lvl FP
        rest = shareGo sf gas id now i vals fin ps (proj₁ (proj₂ fp)) st₁
        st₂ = proj₂ (proj₂ rest)
        D₁  = delivN st₀ st₁
        D₂  = delivN st₁ st₂
        A   = dCapᶜ S W R gas (lvls S W J 1)
        -- one chain is at most `suc (sizeAt S J)` frames, so its frames
        -- fit inside ONE delivery's level charge
        chain≤ : iterL S W (pathLen p) J ≤ lvls S W J 1
        chain≤ = iterL-mono (pathLen p) (suc (sizeAt S J)) 2≤S ≤-refl ≤-refl ≤-refl
                   (≤-trans (p-len J p (proj₁ (∧-true _ _ hp))) (n≤1+n (sizeAt S J)))
        J₁≤ : J₁ ≤ lvls S W J (suc D₁)
        J₁≤ = ≤-trans (Res.hi FP)
                (≤-trans (lvls-mono D₁ D₁ 2≤S ≤-refl ≤-refl chain≤ ≤-refl)
                         (≤-reflexive (sym (lvls-add S W J 1 D₁))))
        D₁≤A : D₁ ≤ A
        D₁≤A = ≤-trans (Res.cnt FP)
                 (dCapᶜ-mono gas gas 2≤S ≤-refl ≤-refl ≤-refl ≤-refl chain≤)
        REST = shareGo-go J₁ sf gas id now i vals fin ps (proj₁ (proj₂ fp)) st₁
                 (Res.good FP)
                 (chP?-widen (Res.lo FP) ps (proj₂ (∧-true _ _ hp)))
                 (v-widen (Res.lo FP) vals hV)
        restCnt : D₂ ≤ dWalkᶜ S W R gas (lvls S W J (suc A)) (length ps)
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
    chP? (Pb J) chains ≡ true → Vb J (arrVal a ∷ []) ≡ true →
    let cg = cascadeGo a id chains sched st in
    Res J J (dWalkᶜ S W R n J (length chains))
          (proj₁ (proj₂ cg)) st (proj₂ (proj₂ cg))

  cascadeGo-go J a id [] sched st g hp hV =
    res J ≤-refl (lvls-infl S W J (delivN st st)) g
        (≤-reflexive (delivN-≡ st st refl))

  cascadeGo-go J a id ((rid , c) ∷ chains) sched st g hp hV
    with any (_≡ᵇ rid) (EvalSt.cancelled st)
  ... | true  =
        res (Res.lvl SK) (Res.lo SK) (Res.hi SK) (Res.good SK)
            (≤-trans (Res.cnt SK)
                     (dWalkᶜ-mono n n (length chains) (suc (length chains))
                        2≤S ≤-refl ≤-refl ≤-refl ≤-refl ≤-refl (n≤1+n (length chains))))
        where
        SK = cascadeGo-go J a id chains sched st g (proj₂ (∧-true _ _ hp)) hV
  ... | false =
        res (Res.lvl REST) (≤-trans (Res.lo FP) (Res.lo REST))
            (≤-trans (Res.hi REST)
               (≤-trans (lvls-mono D₂ D₂ 2≤S ≤-refl ≤-refl J₁≤ ≤-refl)
                  (≤-trans (≤-reflexive (sym (lvls-add S W J (suc D₁) D₂)))
                           (≤-reflexive (cong (lvls S W J) (sym eqN))))))
            (Res.good REST)
            (≤-trans (≤-reflexive eqN)
               (≤-trans (s≤s (+-mono-≤ D₁≤A restCnt))
                        (≤-reflexive (sym (dWalkᶜ-front S W R n J (length chains))))))
        where
        st₀  = consᵈ rid st
        sf₀  = budgetAt e (Sched.slots sched) id
        evs₀ = if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else []
        cs   = chainStep id a c sched st₀
        st₁  = proj₂ (proj₂ cs)
        FP   = foldPath-go J sf₀ n id (arrTick a) (arrSource a) c (arrVal a ∷ [])
                 evs₀ (Arrival.isLast a) sched st₀
                 ( ok-cons J rid sched st (proj₁ g) , proj₂ g )
                 (proj₁ (∧-true _ _ hp)) hV
        J₁   = Res.lvl FP
        rest = cascadeGo a id chains (proj₁ (proj₂ cs)) st₁
        st₂  = proj₂ (proj₂ rest)
        D₁   = delivN st₀ st₁
        D₂   = delivN st₁ st₂
        A    = dCapᶜ S W R n (lvls S W J 1)
        chain≤ : iterL S W (pathLen c) J ≤ lvls S W J 1
        chain≤ = iterL-mono (pathLen c) (suc (sizeAt S J)) 2≤S ≤-refl ≤-refl ≤-refl
                   (≤-trans (p-len J c (proj₁ (∧-true _ _ hp))) (n≤1+n (sizeAt S J)))
        J₁≤ : J₁ ≤ lvls S W J (suc D₁)
        J₁≤ = ≤-trans (Res.hi FP)
                (≤-trans (lvls-mono D₁ D₁ 2≤S ≤-refl ≤-refl chain≤ ≤-refl)
                         (≤-reflexive (sym (lvls-add S W J 1 D₁))))
        D₁≤A : D₁ ≤ A
        D₁≤A = ≤-trans (Res.cnt FP)
                 (dCapᶜ-mono n n 2≤S ≤-refl ≤-refl ≤-refl ≤-refl chain≤)
        REST = cascadeGo-go J₁ a id chains (proj₁ (proj₂ cs)) st₁
                 (Res.good FP)
                 (chP?-widen (Res.lo FP) chains (proj₂ (∧-true _ _ hp)))
                 (v-widen (Res.lo FP) (arrVal a ∷ []) hV)
        restCnt : D₂ ≤ dWalkᶜ S W R n (lvls S W J (suc A)) (length chains)
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
