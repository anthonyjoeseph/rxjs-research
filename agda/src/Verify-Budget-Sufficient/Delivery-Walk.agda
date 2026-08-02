-- STRATUM 0b of Verify-Budget-Sufficient: THE DELIVERY WALK FITS dCap.
--
-- .Deliveries proved WHERE the ledger moves (§ B–§ E) and turned the
-- delivery recurrence into nine proven equations (§ D).  This module
-- consumes those equations and maps the evaluator's delivery clique
-- onto the well-founded walk `dCap` / `dWalk` (Rx.Evaluator) that
-- replaced the refuted closed forms:
--
--     foldPath      sf gas … path …  ↦  dCap  Q gas R
--     dispatchShare sf gas … i …     ↦  dCap  Q gas R
--     shareGo       sf gas … ps …    ↦  dWalk Q gas R (length ps)
--     cascadeGo     a id chains …    ↦  dWalk Q n   R (length chains)
--
-- with R the registry length at the call's entry state.  `dWalk`'s
-- recursion was WRITTEN for this induction — its (i+1)-st summand runs
-- at registry `R + Q · suc d`, d the deliveries already made — so the
-- mapping is not an estimate but a fit, and the one thing it needs from
-- outside is the MINT BUDGET: how many registrations one delivery's
-- processing can add.  That is `Walk-Hyps` below, and it is the ONLY
-- hypothesis this module takes.  Everything else — the walk's own
-- combinatorics, the front decomposition of `dWalk`, the composition of
-- the ledger along the walk — is proven here.
--
-- WHY THE HYPOTHESES ARE A RECORD AND NOT POSTULATES.  The mint budget
-- is a fact about `stepFrame` under a caps invariant, and `capsOK?`
-- lives two strata up (.Caps-Face).  Rather than postulate a
-- caps-flavoured statement in a module that cannot see caps — which
-- would be either false (unconditional) or unstateable (conditional) —
-- the walk is proven RELATIVE to an abstract state predicate `OK`, two
-- abstract SYNTACTIC ledgers (`Pb` on chains, `Vb` on payload lists),
-- and four facts about one frame under them.  .Caps-Face is where they
-- are instantiated, at `capsOK? c`, `pathSz? (cSize c)` and
-- `valsCaps? c sl` respectively.
--
-- AND THE TWO SYNTACTIC LEDGERS ARE NOT OPTIONAL: without them the
-- frame facts are FALSE, not merely unproven.  `sf-mint` quantified
-- over an arbitrary `vals` is refuted by one `thru-outer` frame, which
-- subscribes once per payload and so mints in proportion to a burst
-- width no fixed `Qf` bounds; `sf-ok` quantified over an arbitrary `f`
-- is refuted by `scan-f BIG`, which stores an accumulator over any cap.
-- So each frame fact reads `Pb (f ↠ path′)` and `Vb vals`, and the walk
-- THREADS both: `Pb` down a chain by `p-tail` and across a dispatch by
-- the registry's own ledger (`regP?`, which shareAdmit filters and
-- shareFinish shrinks), `Vb` through a frame by `sf-vals`.  This is the
-- same discipline the caps companion tree runs on, in the two places
-- the walk actually needs it.
--
-- THE PER-FRAME SHAPE, and why it is per FRAME rather than per
-- delivery.  A delivery's processing is a chain walk: `pathLen` frames,
-- each of which may subscribe (hence mint), then one dispatch.  So the
-- budget is stated per frame — `Qf` — and a chain is capped at `B` by
-- `p-len`, `Pb`'s own length reading, which makes the per-DELIVERY
-- budget `Qf * suc B`.  At .Caps-Face's instantiation Qf = cSize *
-- suc cWid (one subscribe per payload of a width-capped burst, each
-- minting at most one registration per source reference of a cap-sized
-- term) and B = cSize, so `Qf * suc B ≤ chargeW c` with room to spare —
-- which is exactly the factorisation chargeW was written in.
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
open import Data.Nat.Solver     using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
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
                                dCap; dWalk; arrTy; arrTick; arrSource; arrVal;
                                budgetAt)

-- .Caps for the walk's monotonicity toolkit (dCap-mono / dWalk-mono) and,
-- under it, .Measures for pathLen and the dropSource lemmas
open import Verify-Budget-Sufficient.Caps public
open import Verify-Budget-Sufficient.Deliveries public

------------------------------------------------------------------
-- § A.  THE WALK'S OWN ARITHMETIC: dWalk DECOMPOSES FROM THE FRONT.
--
-- `dWalk` recurses on its LAST element (i ↦ suc i peels the tail's
-- total off the front), but the evaluator's walks recurse on their
-- FIRST — shareGo and cascadeGo both fold a cons list head-first.  The
-- two agree EXACTLY, and that is the identity below: the first element
-- runs at the entry registry plus one delivery's mints (R + Q), and the
-- rest of the walk runs at the registry that leaves it.
--
-- It is an equality, not an estimate, which is what makes the mapping a
-- fit rather than a bound: nothing is thrown away in the change of
-- direction.
------------------------------------------------------------------

-- the shape both the identity and the mint accounting reduce to
shift : ∀ (a q x : ℕ) → a + q + q * x ≡ a + q * suc x
shift = solve 3 (λ a q x → a :+ q :+ q :* x := a :+ q :* (con 1 :+ x)) refl

dWalk-front : ∀ (Q g R i : ℕ) →
  dWalk Q g R (suc i)
    ≡ suc (dCap Q g (R + Q))
      + dWalk Q g (R + Q * suc (dCap Q g (R + Q))) i
dWalk-front Q g R zero =
  trans (cong (λ x → suc (dCap Q g (R + x))) (*-identityʳ Q))
        (sym (+-identityʳ (suc (dCap Q g (R + Q)))))
dWalk-front Q g R (suc i) =
  trans (cong (λ x → x + suc (dCap Q g (R + Q * suc x)))
              (dWalk-front Q g R i))
    (trans (+-assoc (suc A) W′ (suc (dCap Q g (R + Q * suc (suc A + W′)))))
           (cong (λ x → suc A + (W′ + suc (dCap Q g x))) (sym re)))
  where
  A  = dCap Q g (R + Q)
  R′ = R + Q * suc A
  W′ = dWalk Q g R′ i
  re : R′ + Q * suc W′ ≡ R + Q * suc (suc A + W′)
  re = solve 4 (λ q r a w → (r :+ q :* (con 1 :+ a)) :+ q :* (con 1 :+ w)
                              := r :+ q :* (con 1 :+ (con 1 :+ a :+ w)))
             refl Q R A W′

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
-- § C.  THE HYPOTHESES: ONE FRAME'S MINT BUDGET.
--
-- Everything below is proven from these four facts about ONE
-- `stepFrame` under an abstract state predicate `OK` and the two
-- syntactic ledgers, plus the three closure facts the walk's own
-- bookkeeping needs (the ledger cons, the share latch, the share
-- finish — none of which is a frame).  A frame is where the evaluator
-- subscribes, so a frame is where the registry can grow: `sf-mint` is
-- the budget, `sf-len` says minted chains stay in the ledger,
-- `sf-vals` says the payloads it hands the next frame stay in theirs,
-- and `sf-ok` carries the state predicate across.
------------------------------------------------------------------

record Walk-Hyps {n} {Γ : Ctx n} {t} (e : Closed Γ t) (Qf B : ℕ) : Set₁ where
  field
    OK : Sched Γ → EvalSt e → Set

    -- the two syntactic side conditions.  Bool rather than Set because
    -- both are LEDGERS: the registry carries `Pb` for every entry it
    -- holds, and that ledger is what a dispatch reads its chains out of
    Pb : ∀ {u} → Path Γ u t → Bool
    Vb : ∀ {s} → List (Val Γ s) → Bool

    -- `Pb`'s length reading, and its descent along a chain
    p-len  : ∀ {u} (p : Path Γ u t) → Pb p ≡ true → pathLen p ≤ B
    p-tail : ∀ {s u} (f : Frame Γ s u) (p : Path Γ u t) →
             Pb (f ↠ p) ≡ true → Pb p ≡ true

    ok-cons : (rid : RegId) (sched : Sched Γ) (st : EvalSt e) →
      OK sched st → OK sched (consᵈ rid st)

    ok-latch : (i : Fin n) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
      OK sched st → OK sched (shareLatch i fin st)

    ok-finish : (i : Fin n) (fin : Bool) (out : Stream Γ t × Sched Γ × EvalSt e) →
      OK (proj₁ (proj₂ out)) (proj₂ (proj₂ out)) →
      OK (proj₁ (proj₂ (shareFinish i fin out)))
         (proj₂ (proj₂ (shareFinish i fin out)))

    sf-ok : ∀ {s u} (sf : Gas) (id : Id) (now : Tick) (f : Frame Γ s u)
      (path′ : Path Γ u t) (vals : List (Val Γ s)) (fin : Bool)
      (sched : Sched Γ) (st : EvalSt e) → OK sched st →
      Pb (f ↠ path′) ≡ true → Vb vals ≡ true →
      OK (proj₁ (proj₂ (proj₂ (proj₂ (stepFrame sf id now f path′ vals fin sched st)))))
         (proj₂ (proj₂ (proj₂ (proj₂ (stepFrame sf id now f path′ vals fin sched st)))))

    sf-vals : ∀ {s u} (sf : Gas) (id : Id) (now : Tick) (f : Frame Γ s u)
      (path′ : Path Γ u t) (vals : List (Val Γ s)) (fin : Bool)
      (sched : Sched Γ) (st : EvalSt e) → OK sched st →
      Pb (f ↠ path′) ≡ true → Vb vals ≡ true →
      Vb (proj₁ (stepFrame sf id now f path′ vals fin sched st)) ≡ true

    sf-mint : ∀ {s u} (sf : Gas) (id : Id) (now : Tick) (f : Frame Γ s u)
      (path′ : Path Γ u t) (vals : List (Val Γ s)) (fin : Bool)
      (sched : Sched Γ) (st : EvalSt e) → OK sched st →
      Pb (f ↠ path′) ≡ true → Vb vals ≡ true →
      length (EvalSt.registry
        (proj₂ (proj₂ (proj₂ (proj₂ (stepFrame sf id now f path′ vals fin sched st))))))
        ≤ length (EvalSt.registry st) + Qf

    sf-len : ∀ {s u} (sf : Gas) (id : Id) (now : Tick) (f : Frame Γ s u)
      (path′ : Path Γ u t) (vals : List (Val Γ s)) (fin : Bool)
      (sched : Sched Γ) (st : EvalSt e) → OK sched st →
      Pb (f ↠ path′) ≡ true → Vb vals ≡ true →
      regP? Pb (EvalSt.registry st) ≡ true →
      regP? Pb (EvalSt.registry
        (proj₂ (proj₂ (proj₂ (proj₂ (stepFrame sf id now f path′ vals fin sched st))))))
        ≡ true

------------------------------------------------------------------
-- § D.  THE WALK, RELATIVE TO THOSE HYPOTHESES.
------------------------------------------------------------------

module Walk {n} {Γ : Ctx n} {t} {e : Closed Γ t}
            (Qf Q B : ℕ) (fits : Qf * suc B ≤ Q)
            (H : Walk-Hyps e Qf B) where

  open Walk-Hyps H

  -- the state predicate the walk actually threads: the caller's, plus
  -- the registry's own ledger
  Good : Sched Γ → EvalSt e → Set
  Good sched st = OK sched st × (regP? Pb (EvalSt.registry st) ≡ true)

  ∣_∣ : EvalSt e → ℕ
  ∣ st ∣ = length (EvalSt.registry st)

  ----------------------------------------------------------------
  -- (i) THE PREDICATE SURVIVES THE WALK.
  ----------------------------------------------------------------

  foldPath-good : ∀ (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
    {u} (path : Path Γ u t) (vals : List (Val Γ u))
    (evs : List (InstEvent (Val Γ t))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) → Good sched st →
    Pb path ≡ true → Vb vals ≡ true →
    Good (proj₁ (proj₂ (foldPath sf gas id now envSrc path vals evs fin sched st)))
         (proj₂ (proj₂ (foldPath sf gas id now envSrc path vals evs fin sched st)))

  dispatchShare-good : ∀ (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) → Good sched st → Vb vals ≡ true →
    Good (proj₁ (proj₂ (dispatchShare {t = t} sf gas id now i vals fin sched st)))
         (proj₂ (proj₂ (dispatchShare {t = t} sf gas id now i vals fin sched st)))

  shareGo-good : ∀ (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (ps : List (RegId × Path Γ (lookup Γ i) t))
    (sched : Sched Γ) (st : EvalSt e) → Good sched st →
    chP? Pb ps ≡ true → Vb vals ≡ true →
    Good (proj₁ (proj₂ (shareGo sf gas id now i vals fin ps sched st)))
         (proj₂ (proj₂ (shareGo sf gas id now i vals fin ps sched st)))

  foldPath-good sf gas id now envSrc root vals evs fin sched st g hP hV = g
  foldPath-good sf gas id now envSrc (share-sink i) vals evs fin sched st g hP hV =
    dispatchShare-good sf gas id now i vals fin sched st g hV
  foldPath-good sf gas id now envSrc (f ↠ path′) vals evs fin sched st (ok , len) hP hV =
    let r = stepFrame sf id now f path′ vals fin sched st in
    foldPath-good sf gas id now envSrc path′ (proj₁ r)
      (evs ++ proj₁ (proj₂ r)) (proj₁ (proj₂ (proj₂ r)))
      (proj₁ (proj₂ (proj₂ (proj₂ r)))) (proj₂ (proj₂ (proj₂ (proj₂ r))))
      ( sf-ok  sf id now f path′ vals fin sched st ok hP hV
      , sf-len sf id now f path′ vals fin sched st ok hP hV len )
      (p-tail f path′ hP)
      (sf-vals sf id now f path′ vals fin sched st ok hP hV)

  dispatchShare-good sf zero id now i vals fin sched st g hV = g
  dispatchShare-good sf (suc gas) id now i vals fin sched st (ok , len) hV =
    let stL = shareLatch i fin st
        GO  = shareGo-good sf gas id now i vals fin
                (shareAdmit i (EvalSt.registry st)) sched stL
                ( ok-latch i fin sched st ok
                , subst (λ rs → regP? Pb rs ≡ true)
                        (sym (shareLatch-reg i fin st)) len )
                (shareAdmit-chP Pb i (EvalSt.registry st) len) hV
        out = shareGo sf gas id now i vals fin
                (shareAdmit i (EvalSt.registry st)) sched stL in
    ( ok-finish i fin out (proj₁ GO)
    , shareFinish-regP Pb i fin out (proj₂ GO) )

  shareGo-good sf gas id now i vals fin []               sched st g hp hV = g
  shareGo-good sf gas id now i vals fin ((rid , p) ∷ ps) sched st g hp hV
    with any (_≡ᵇ rid) (EvalSt.cancelled st)
  ... | true  = shareGo-good sf gas id now i vals fin ps sched st g
                  (proj₂ (∧-true _ _ hp)) hV
  ... | false =
        let st₀ = consᵈ rid st
            FP  = foldPath-good sf gas id now (toℕ i) p vals
                    (if fin then close (toℕ i) exhausted ∷ [] else []) fin sched st₀
                    ( ok-cons rid sched st (proj₁ g) , proj₂ g )
                    (proj₁ (∧-true _ _ hp)) hV
            fp  = foldPath sf gas id now (toℕ i) p vals
                    (if fin then close (toℕ i) exhausted ∷ [] else []) fin sched st₀ in
        shareGo-good sf gas id now i vals fin ps
          (proj₁ (proj₂ fp)) (proj₂ (proj₂ fp)) FP (proj₂ (∧-true _ _ hp)) hV

  ----------------------------------------------------------------
  -- (ii) THE MINT BUDGET, LIFTED FROM ONE FRAME TO THE WHOLE WALK.
  --
  -- A delivery's processing costs `Qf` per frame of its chain and `Q`
  -- per delivery it causes.  This is the fact the walk's registry
  -- argument is threaded by, and it is what `dWalk`'s `R + Q * suc d`
  -- was written to be.
  ----------------------------------------------------------------

  foldPath-mint : ∀ (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
    {u} (path : Path Γ u t) (vals : List (Val Γ u))
    (evs : List (InstEvent (Val Γ t))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) → Good sched st →
    Pb path ≡ true → Vb vals ≡ true →
    let st′ = proj₂ (proj₂ (foldPath sf gas id now envSrc path vals evs fin sched st)) in
    ∣ st′ ∣ ≤ ∣ st ∣ + Qf * pathLen path + Q * delivN st st′

  dispatchShare-mint : ∀ (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) → Good sched st → Vb vals ≡ true →
    let st′ = proj₂ (proj₂ (dispatchShare {t = t} sf gas id now i vals fin sched st)) in
    ∣ st′ ∣ ≤ ∣ st ∣ + Q * delivN st st′

  shareGo-mint : ∀ (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (ps : List (RegId × Path Γ (lookup Γ i) t))
    (sched : Sched Γ) (st : EvalSt e) → Good sched st →
    chP? Pb ps ≡ true → Vb vals ≡ true →
    let st′ = proj₂ (proj₂ (shareGo sf gas id now i vals fin ps sched st)) in
    ∣ st′ ∣ ≤ ∣ st ∣ + Q * delivN st st′

  foldPath-mint sf gas id now envSrc root vals evs fin sched st g hP hV =
    ≤-trans (m≤m+n ∣ st ∣ _) (m≤m+n _ _)
  foldPath-mint sf gas id now envSrc (share-sink i) vals evs fin sched st g hP hV =
    ≤-trans (dispatchShare-mint sf gas id now i vals fin sched st g hV)
            (+-monoˡ-≤ _ (m≤m+n ∣ st ∣ (Qf * 0)))
  foldPath-mint sf gas id now envSrc (f ↠ path′) vals evs fin sched st (ok , len) hP hV =
    ≤-trans ih
      (≤-trans (+-monoˡ-≤ (Q * D₁)
                  (+-monoˡ-≤ (Qf * pathLen path′)
                     (sf-mint sf id now f path′ vals fin sched st ok hP hV)))
        (≤-trans (≤-reflexive (cong (_+ Q * D₁) (shift ∣ st ∣ Qf (pathLen path′))))
                 (+-monoʳ-≤ (∣ st ∣ + Qf * suc (pathLen path′))
                    (*-monoʳ-≤ Q (≤-reflexive (sym eqD))))))
    where
    r   = stepFrame sf id now f path′ vals fin sched st
    st₁ = proj₂ (proj₂ (proj₂ (proj₂ r)))
    sd₁ = proj₁ (proj₂ (proj₂ (proj₂ r)))
    fp  = foldPath sf gas id now envSrc path′ (proj₁ r)
            (evs ++ proj₁ (proj₂ r)) (proj₁ (proj₂ (proj₂ r))) sd₁ st₁
    D₁  = delivN st₁ (proj₂ (proj₂ fp))
    eqD : delivN st (proj₂ (proj₂ (foldPath sf gas id now envSrc (f ↠ path′)
                                     vals evs fin sched st))) ≡ D₁
    eqD = foldPath-frame-N sf gas id now envSrc f path′ vals evs fin sched st
    ih : ∣ proj₂ (proj₂ fp) ∣ ≤ ∣ st₁ ∣ + Qf * pathLen path′ + Q * D₁
    ih = foldPath-mint sf gas id now envSrc path′ (proj₁ r)
           (evs ++ proj₁ (proj₂ r)) (proj₁ (proj₂ (proj₂ r))) sd₁ st₁
           ( sf-ok  sf id now f path′ vals fin sched st ok hP hV
           , sf-len sf id now f path′ vals fin sched st ok hP hV len )
           (p-tail f path′ hP)
           (sf-vals sf id now f path′ vals fin sched st ok hP hV)

  dispatchShare-mint sf zero id now i vals fin sched st g hV = m≤m+n ∣ st ∣ _
  dispatchShare-mint sf (suc gas) id now i vals fin sched st (ok , len) hV =
    ≤-trans (shareFinish-len i fin out)
      (≤-trans GO
        (≤-trans (+-monoˡ-≤ (Q * delivN stL (proj₂ (proj₂ out)))
                    (≤-reflexive (cong length (shareLatch-reg i fin st))))
                 (+-monoʳ-≤ ∣ st ∣ (*-monoʳ-≤ Q (≤-reflexive (sym eqD))))))
    where
    stL = shareLatch i fin st
    out = shareGo sf gas id now i vals fin
            (shareAdmit i (EvalSt.registry st)) sched stL
    eqD : delivN st (proj₂ (proj₂ (dispatchShare {t = t} sf (suc gas) id now i vals fin sched st)))
            ≡ delivN stL (proj₂ (proj₂ out))
    eqD = dispatchShare-suc-N sf gas id now i vals fin sched st
    GO : ∣ proj₂ (proj₂ out) ∣ ≤ ∣ stL ∣ + Q * delivN stL (proj₂ (proj₂ out))
    GO = shareGo-mint sf gas id now i vals fin
           (shareAdmit i (EvalSt.registry st)) sched stL
           ( ok-latch i fin sched st ok
           , subst (λ rs → regP? Pb rs ≡ true) (sym (shareLatch-reg i fin st)) len )
           (shareAdmit-chP Pb i (EvalSt.registry st) len) hV

  shareGo-mint sf gas id now i vals fin []               sched st g hp hV = m≤m+n ∣ st ∣ _
  shareGo-mint sf gas id now i vals fin ((rid , p) ∷ ps) sched st g hp hV
    with any (_≡ᵇ rid) (EvalSt.cancelled st)
  ... | true  = shareGo-mint sf gas id now i vals fin ps sched st g
                  (proj₂ (∧-true _ _ hp)) hV
  ... | false =
        ≤-trans ih
          (≤-trans (+-monoˡ-≤ (Q * D₂) step₁)
            (≤-trans (≤-reflexive (+-assoc ∣ st ∣ (Q * suc D₁) (Q * D₂)))
              (≤-trans (+-monoʳ-≤ ∣ st ∣
                          (≤-reflexive (sym (*-distribˡ-+ Q (suc D₁) D₂))))
                       (≤-reflexive (cong (λ d → ∣ st ∣ + Q * d) (sym eqN))))))
    where
    st₀ = consᵈ rid st
    evs₀ = if fin then close (toℕ i) exhausted ∷ [] else []
    fp  = foldPath sf gas id now (toℕ i) p vals evs₀ fin sched st₀
    st₁ = proj₂ (proj₂ fp)
    rest = shareGo sf gas id now i vals fin ps (proj₁ (proj₂ fp)) st₁
    st₂ = proj₂ (proj₂ rest)
    D₁  = delivN st₀ st₁
    D₂  = delivN st₁ st₂
    eqN : delivN st st₂ ≡ suc (D₁ + D₂)
    eqN = trans (delivN-cons rid st st₂
                   (⊑ᵈ-trans (foldPath-deliv sf gas id now (toℕ i) p vals evs₀ fin sched st₀)
                             (shareGo-deliv sf gas id now i vals fin ps
                                (proj₁ (proj₂ fp)) st₁)))
                (cong suc (delivN-split
                             (foldPath-deliv sf gas id now (toℕ i) p vals evs₀ fin sched st₀)
                             (shareGo-deliv sf gas id now i vals fin ps
                                (proj₁ (proj₂ fp)) st₁)))
    g₀ : Good sched st₀
    g₀ = ( ok-cons rid sched st (proj₁ g) , proj₂ g )
    g₁ : Good (proj₁ (proj₂ fp)) st₁
    g₁ = foldPath-good sf gas id now (toℕ i) p vals evs₀ fin sched st₀ g₀
           (proj₁ (∧-true _ _ hp)) hV
    FPm : ∣ st₁ ∣ ≤ ∣ st₀ ∣ + Qf * pathLen p + Q * D₁
    FPm = foldPath-mint sf gas id now (toℕ i) p vals evs₀ fin sched st₀ g₀
            (proj₁ (∧-true _ _ hp)) hV
    -- one chain's frames cost Qf each and there are at most B of them,
    -- so the whole chain is inside ONE delivery's budget
    chainQ : Qf * pathLen p ≤ Q
    chainQ = ≤-trans (*-monoʳ-≤ Qf (≤-trans (p-len p (proj₁ (∧-true _ _ hp)))
                                            (n≤1+n B)))
                     fits
    step₁ : ∣ st₁ ∣ ≤ ∣ st ∣ + Q * suc D₁
    step₁ = ≤-trans FPm
              (≤-trans (+-monoˡ-≤ (Q * D₁) (+-monoʳ-≤ ∣ st ∣ chainQ))
                       (≤-reflexive (shift ∣ st ∣ Q D₁)))
    ih : ∣ st₂ ∣ ≤ ∣ st₁ ∣ + Q * D₂
    ih = shareGo-mint sf gas id now i vals fin ps (proj₁ (proj₂ fp)) st₁ g₁
           (proj₂ (∧-true _ _ hp)) hV

  ----------------------------------------------------------------
  -- (iii) AND THE WALK ITSELF.  Each clause is the corresponding line
  -- of `dCap` / `dWalk`, with .Deliveries' § D supplying the counting
  -- and (ii) supplying the registry each summand runs at.
  ----------------------------------------------------------------

  foldPath-walk : ∀ (R : ℕ) (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
    {u} (path : Path Γ u t) (vals : List (Val Γ u))
    (evs : List (InstEvent (Val Γ t))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) → Good sched st →
    Pb path ≡ true → Vb vals ≡ true →
    ∣ st ∣ + Qf * pathLen path ≤ R →
    delivN st (proj₂ (proj₂ (foldPath sf gas id now envSrc path vals evs fin sched st)))
      ≤ dCap Q gas R

  dispatchShare-walk : ∀ (R : ℕ) (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) → Good sched st → Vb vals ≡ true →
    ∣ st ∣ ≤ R →
    delivN st (proj₂ (proj₂ (dispatchShare {t = t} sf gas id now i vals fin sched st)))
      ≤ dCap Q gas R

  shareGo-walk : ∀ (R : ℕ) (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (ps : List (RegId × Path Γ (lookup Γ i) t))
    (sched : Sched Γ) (st : EvalSt e) → Good sched st →
    chP? Pb ps ≡ true → Vb vals ≡ true →
    ∣ st ∣ ≤ R →
    delivN st (proj₂ (proj₂ (shareGo sf gas id now i vals fin ps sched st)))
      ≤ dWalk Q gas R (length ps)

  foldPath-walk R sf gas id now envSrc root vals evs fin sched st g hP hV h =
    ≤-trans (≤-reflexive (foldPath-root-N sf gas id now envSrc vals evs fin sched st))
            z≤n
  foldPath-walk R sf gas id now envSrc (share-sink i) vals evs fin sched st g hP hV h =
    dispatchShare-walk R sf gas id now i vals fin sched st g hV
      (≤-trans (m≤m+n ∣ st ∣ (Qf * 0)) h)
  foldPath-walk R sf gas id now envSrc (f ↠ path′) vals evs fin sched st (ok , len) hP hV h =
    ≤-trans (≤-reflexive (foldPath-frame-N sf gas id now envSrc f path′ vals evs fin sched st))
      (foldPath-walk R sf gas id now envSrc path′ (proj₁ r)
         (evs ++ proj₁ (proj₂ r)) (proj₁ (proj₂ (proj₂ r))) sd₁ st₁
         ( sf-ok  sf id now f path′ vals fin sched st ok hP hV
         , sf-len sf id now f path′ vals fin sched st ok hP hV len )
         (p-tail f path′ hP)
         (sf-vals sf id now f path′ vals fin sched st ok hP hV)
         (≤-trans (+-monoˡ-≤ (Qf * pathLen path′)
                     (sf-mint sf id now f path′ vals fin sched st ok hP hV))
                  (≤-trans (≤-reflexive (shift ∣ st ∣ Qf (pathLen path′))) h)))
    where
    r   = stepFrame sf id now f path′ vals fin sched st
    st₁ = proj₂ (proj₂ (proj₂ (proj₂ r)))
    sd₁ = proj₁ (proj₂ (proj₂ (proj₂ r)))

  dispatchShare-walk R sf zero id now i vals fin sched st g hV h =
    ≤-reflexive (dispatchShare-zero-N sf id now i vals fin sched st)
  dispatchShare-walk R sf (suc gas) id now i vals fin sched st (ok , len) hV h =
    ≤-trans (≤-reflexive (dispatchShare-suc-N sf gas id now i vals fin sched st))
      (≤-trans GO (dWalk-mono Q Q gas gas R R (length (shareAdmit i (EvalSt.registry st))) R
                     ≤-refl ≤-refl ≤-refl
                     (≤-trans (shareAdmit-len i (EvalSt.registry st)) h)))
    where
    stL = shareLatch i fin st
    GO : delivN stL (proj₂ (proj₂ (shareGo sf gas id now i vals fin
                                     (shareAdmit i (EvalSt.registry st)) sched stL)))
           ≤ dWalk Q gas R (length (shareAdmit i (EvalSt.registry st)))
    GO = shareGo-walk R sf gas id now i vals fin
           (shareAdmit i (EvalSt.registry st)) sched stL
           ( ok-latch i fin sched st ok
           , subst (λ rs → regP? Pb rs ≡ true) (sym (shareLatch-reg i fin st)) len )
           (shareAdmit-chP Pb i (EvalSt.registry st) len) hV
           (≤-trans (≤-reflexive (cong length (shareLatch-reg i fin st))) h)

  shareGo-walk R sf gas id now i vals fin []               sched st g hp hV h =
    ≤-reflexive (delivN-≡ st st refl)
  shareGo-walk R sf gas id now i vals fin ((rid , p) ∷ ps) sched st g hp hV h
    with any (_≡ᵇ rid) (EvalSt.cancelled st)
  ... | true  =
        ≤-trans (shareGo-walk R sf gas id now i vals fin ps sched st g
                   (proj₂ (∧-true _ _ hp)) hV h)
                (dWalk-mono Q Q gas gas R R (length ps) (suc (length ps))
                   ≤-refl ≤-refl ≤-refl (n≤1+n (length ps)))
  ... | false =
        ≤-trans (≤-reflexive eqN)
          (≤-trans (s≤s (+-mono-≤ h₁ h₂))
                   (≤-reflexive (sym (dWalk-front Q gas R (length ps)))))
    where
    st₀ = consᵈ rid st
    evs₀ = if fin then close (toℕ i) exhausted ∷ [] else []
    fp  = foldPath sf gas id now (toℕ i) p vals evs₀ fin sched st₀
    st₁ = proj₂ (proj₂ fp)
    rest = shareGo sf gas id now i vals fin ps (proj₁ (proj₂ fp)) st₁
    st₂ = proj₂ (proj₂ rest)
    D₁  = delivN st₀ st₁
    D₂  = delivN st₁ st₂
    A   = dCap Q gas (R + Q)
    g₀ : Good sched st₀
    g₀ = ( ok-cons rid sched st (proj₁ g) , proj₂ g )
    g₁ : Good (proj₁ (proj₂ fp)) st₁
    g₁ = foldPath-good sf gas id now (toℕ i) p vals evs₀ fin sched st₀ g₀
           (proj₁ (∧-true _ _ hp)) hV
    chainQ : Qf * pathLen p ≤ Q
    chainQ = ≤-trans (*-monoʳ-≤ Qf (≤-trans (p-len p (proj₁ (∧-true _ _ hp)))
                                            (n≤1+n B)))
                     fits
    -- the ledger: one cons, this chain's fold, then the rest of the walk
    eqN : delivN st st₂ ≡ suc (D₁ + D₂)
    eqN = trans (delivN-cons rid st st₂
                   (⊑ᵈ-trans (foldPath-deliv sf gas id now (toℕ i) p vals evs₀ fin sched st₀)
                             (shareGo-deliv sf gas id now i vals fin ps
                                (proj₁ (proj₂ fp)) st₁)))
                (cong suc (delivN-split
                             (foldPath-deliv sf gas id now (toℕ i) p vals evs₀ fin sched st₀)
                             (shareGo-deliv sf gas id now i vals fin ps
                                (proj₁ (proj₂ fp)) st₁)))
    h₁ : D₁ ≤ A
    h₁ = foldPath-walk (R + Q) sf gas id now (toℕ i) p vals evs₀ fin sched st₀ g₀
           (proj₁ (∧-true _ _ hp)) hV (+-mono-≤ h chainQ)
    -- and the rest runs at the registry this delivery leaves, which is
    -- the entry registry plus ONE delivery's mints per delivery made
    h₂ : D₂ ≤ dWalk Q gas (R + Q * suc A) (length ps)
    h₂ = ≤-trans (shareGo-walk ∣ st₁ ∣ sf gas id now i vals fin ps
                    (proj₁ (proj₂ fp)) st₁ g₁ (proj₂ (∧-true _ _ hp)) hV ≤-refl)
                 (dWalk-mono Q Q gas gas ∣ st₁ ∣ (R + Q * suc A)
                    (length ps) (length ps) ≤-refl ≤-refl
                    (≤-trans (≤-trans (foldPath-mint sf gas id now (toℕ i) p vals evs₀
                                         fin sched st₀ g₀ (proj₁ (∧-true _ _ hp)) hV)
                               (≤-trans (+-monoˡ-≤ (Q * D₁) (+-monoʳ-≤ ∣ st ∣ chainQ))
                                        (≤-reflexive (shift ∣ st ∣ Q D₁))))
                             (+-mono-≤ h (*-monoʳ-≤ Q (s≤s h₁))))
                    ≤-refl)

  ----------------------------------------------------------------
  -- (iv) THE CASCADE, one level up: the same walk with `chainStep` in
  -- place of the share fan-out and the dispatch gas at its seed, `n`.
  ----------------------------------------------------------------

  cascadeGo-walk : ∀ (R : ℕ) (a : Arrival Γ) (id : Id)
    (chains : List (RegId × Path Γ (arrTy a) t))
    (sched : Sched Γ) (st : EvalSt e) → Good sched st →
    chP? Pb chains ≡ true → Vb (arrVal a ∷ []) ≡ true →
    ∣ st ∣ ≤ R →
    delivN st (proj₂ (proj₂ (cascadeGo a id chains sched st)))
      ≤ dWalk Q n R (length chains)
  cascadeGo-walk R a id []                   sched st g hp hV h =
    ≤-reflexive (delivN-≡ st st refl)
  cascadeGo-walk R a id ((rid , c) ∷ chains) sched st g hp hV h
    with any (_≡ᵇ rid) (EvalSt.cancelled st)
  ... | true  =
        ≤-trans (cascadeGo-walk R a id chains sched st g (proj₂ (∧-true _ _ hp)) hV h)
                (dWalk-mono Q Q n n R R (length chains) (suc (length chains))
                   ≤-refl ≤-refl ≤-refl (n≤1+n (length chains)))
  ... | false =
        ≤-trans (≤-reflexive eqN)
          (≤-trans (s≤s (+-mono-≤ h₁ h₂))
                   (≤-reflexive (sym (dWalk-front Q n R (length chains)))))
    where
    st₀  = consᵈ rid st
    sf₀  = budgetAt e (Sched.slots sched) id
    evs₀ = if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else []
    cs   = chainStep id a c sched st₀
    st₁  = proj₂ (proj₂ cs)
    rest = cascadeGo a id chains (proj₁ (proj₂ cs)) st₁
    st₂  = proj₂ (proj₂ rest)
    D₁   = delivN st₀ st₁
    D₂   = delivN st₁ st₂
    A    = dCap Q n (R + Q)
    g₀ : Good sched st₀
    g₀ = ( ok-cons rid sched st (proj₁ g) , proj₂ g )
    g₁ : Good (proj₁ (proj₂ cs)) st₁
    g₁ = foldPath-good sf₀ n id (arrTick a) (arrSource a) c (arrVal a ∷ [])
           evs₀ (Arrival.isLast a) sched st₀ g₀ (proj₁ (∧-true _ _ hp)) hV
    chainQ : Qf * pathLen c ≤ Q
    chainQ = ≤-trans (*-monoʳ-≤ Qf (≤-trans (p-len c (proj₁ (∧-true _ _ hp)))
                                            (n≤1+n B)))
                     fits
    eqN : delivN st st₂ ≡ suc (D₁ + D₂)
    eqN = trans (delivN-cons rid st st₂
                   (⊑ᵈ-trans (chainStep-deliv id a c sched st₀)
                             (cascadeGo-deliv a id chains (proj₁ (proj₂ cs)) st₁)))
                (cong suc (delivN-split (chainStep-deliv id a c sched st₀)
                             (cascadeGo-deliv a id chains (proj₁ (proj₂ cs)) st₁)))
    h₁ : D₁ ≤ A
    h₁ = foldPath-walk (R + Q) sf₀ n id (arrTick a) (arrSource a) c (arrVal a ∷ [])
           evs₀ (Arrival.isLast a) sched st₀ g₀ (proj₁ (∧-true _ _ hp)) hV
           (+-mono-≤ h chainQ)
    h₂ : D₂ ≤ dWalk Q n (R + Q * suc A) (length chains)
    h₂ = ≤-trans (cascadeGo-walk ∣ st₁ ∣ a id chains (proj₁ (proj₂ cs)) st₁ g₁
                    (proj₂ (∧-true _ _ hp)) hV ≤-refl)
                 (dWalk-mono Q Q n n ∣ st₁ ∣ (R + Q * suc A)
                    (length chains) (length chains) ≤-refl ≤-refl
                    (≤-trans (≤-trans (foldPath-mint sf₀ n id (arrTick a) (arrSource a) c
                                         (arrVal a ∷ []) evs₀ (Arrival.isLast a) sched st₀ g₀
                                         (proj₁ (∧-true _ _ hp)) hV)
                               (≤-trans (+-monoˡ-≤ (Q * D₁) (+-monoʳ-≤ ∣ st ∣ chainQ))
                                        (≤-reflexive (shift ∣ st ∣ Q D₁))))
                             (+-mono-≤ h (*-monoʳ-≤ Q (s≤s h₁))))
                    ≤-refl)
