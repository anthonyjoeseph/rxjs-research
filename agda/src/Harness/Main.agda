-- THE MEASUREMENT HARNESS — a COMPILED calculator for the machine's own
-- arithmetic.  A MODULE_ROOT (`make harness-build` / `make harness`), so it
-- lives in `src` under the wiring law rather than in a staging directory
-- outside the claim graph.  `src/Main.agda` never reaches it, so `make gate-heavy`
-- does not pay for it.
--
-- WHY IT EXISTS.  Two of this machine's number families do not normalise in
-- the TYPECHECKER at all:
--
--   * the `fLvlD`/`sizeAt`/`widAt`/`regAt` family is `abstract`
--     `abstract` in `Rx.Evaluator`, as is `blowH`, both for a
--     measured performance reason — with the bodies visible, one whnf
--     unfolds the whole loop and the consuming module runs past an hour.
--     `poolCount` is NOT itself abstract, but it calls `fLvlD`, so
--     `poolCount 1 0` is STUCK at the smallest possible arguments;
--   * the deep rungs simply exceed the typechecker (one was killed at
--     12.6 GB after 20 minutes).
--
-- THE GHC BACKEND RUNS THE SAME DEFINITIONS AND IGNORES `abstract`, because
-- opacity is a TYPECHECKING contract and not a runtime one.  So a number
-- unreachable by `refl` is reachable here.
--
-- ⚠ ANYTHING READ OFF THIS BINARY IS `measured-not-rechecked` BY
-- CONSTRUCTION, and must be flagged as such wherever it is recorded.  A
-- compiled number is NOT a `refl` pin and must never be reported as one: no
-- proof may depend on it, and it cannot discharge a postulate.  Its use is
-- to AIM the grind and to REFUTE — a single compiled row that contradicts a
-- postulate is a finding worth chasing back to a type-level witness.
--
-- THE GUARD against a backend that has quietly diverged from the
-- typechecker is CALIBRATION.  Row 0 is a value this very module also pins
-- by `refl` (`calibration-pin` below), so the typechecker fixes the
-- expected number at compile time and the binary prints the computed one.
-- IF ROW 0 DOES NOT PRINT 65536, EVERY OTHER ROW IS VOID — stop and
-- diagnose the backend, do not read on.
--
-- ONE ROW PER PROCESS, deliberately: a single process that computes several
-- deep rungs retains all of them and dies of memory; a fresh process per row
-- does not.
--
--     make harness-build          compile it
--     make harness                every row, one process each
--     make harness ARGS='1'       just row 1
module Harness.Main where

open import Data.Bool using (Bool; false; if_then_else_)
open import Data.Char using (toℕ)
open import Data.List using (List; []; _∷_; map; length; foldr)
open import Data.Nat using (_≡ᵇ_; ℕ; suc; _+_; _*_; _∸_; _≤ᵇ_; _⊔_)
open import Data.Nat.DivMod using (_/_; _%_)
open import Data.Nat.Show using (show)
open import Data.String using (String; _++_; toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Agda.Builtin.IO using (IO)
open import CLI.IO using (_>>=_; getContents; putStr; Unit)
open import Data.Product using (proj₁; proj₂; _,_; _×_)
open import Data.Sum using (inj₁; inj₂)
open import Rx.Exp using (Ctx; Closed; sizeᵉ)
open import Rx.Slots using (Slots; slotsSize)
open import Rx.Frame-Width using (entryCeil)
open import Rx.Prim using (towerℕ; gasPad; g0; Id)
open import Rx.Evaluator using (poolCount; blowH; capsHgo; lvls; iterL; capsBase; subscribeE; sched-init; st-init; root;
  Sched; EvalSt; sched-next; cascade; arrTy; arrVal)
open import Rx.Nest-Depth using (nestDᵛ; nestDᵉ)
open import Rx.Evaluator using (budgetAt; chainsOf; cascadeLatch; cascadeGo; chainStep; Arrival; RegId; Path)
open import Verify-Budget-Sufficient.Caps-Depth using (depthCascade; depthChain)
open import Verify-Budget-Sufficient.Caps-Depth using (depthE)
open import Verify-Budget-Sufficient.Deliveries using (delivN)
open import Verify-Budget-Sufficient.Demand-Programs
  using (progD; sucG; ins₀; progT; sucGT; progU; sucGU; progB; sucGB; progN; sucGN; progF; sucGF;
  insF; insT; subjN; pathN; progC; sucGC; progW; sucGW; progO; sucGO)
open import Verify-Budget-Sufficient.Nest-Store
  using (nestSyn; nestCapAt; storeNestMax; slotsNestSum; nestOK?; pathNestD; chainsNestD; liveNest;
  nodeNest; regsNestMax)

------------------------------------------------------------------
-- THE CALIBRATION PIN.  `towerℕ` is the one member of this
-- neighbourhood that DOES normalise in the typechecker, which is what
-- makes it usable as a cross-check: the same expression is fixed here by
-- `refl` (so `make agda-dev` checks it) and printed by the compiled
-- binary as row 0.  Agreement is the evidence that the backend computes
-- what the typechecker computes; divergence voids every other row.
--
-- NB `towerℕ` is NOT the thing the harness exists to reach — it was
-- tested and found NOT to be the blocker for the anchor.  It is here
-- precisely BECAUSE it is computable on both sides.
------------------------------------------------------------------

calibration : ℕ
calibration = towerℕ 4

-- ANONYMOUS by the bug-cache idiom (`_ : lhs ≡ rhs`), not by accident: a
-- NAMED pin is a proven definition with no consumer, i.e. an orphan, and
-- `make wiring-gate` rightly fails it (observed while landing this file).
-- Anonymous, the typechecker still fixes the number at compile time and
-- there is no name to orphan.
_ : calibration ≡ 65536
_ = refl

------------------------------------------------------------------
-- THE ROWS.  Add rows freely; keep row 0 where it is.  State for each
-- what it would take to make the row INTERESTING — a row that could not
-- have surprised anyone is not a row (CLAUDE.md, de-risk mode).
------------------------------------------------------------------

-- ROWS 0–2 TERMINATE and are what `make harness` sweeps.
-- ROWS 10+ ARE THE QUARANTINE: measured non-terminating, kept because
-- they are the exact expressions someone will want to retry.  They are
-- NOT in the default sweep — running them is an explicit `ARGS=10`.
-- Indices 20+ cannot be literal PATTERNS (Agda expands a numeric
-- literal pattern to that many constructors), so Series N dispatches on
-- an offset instead.  Row 20+k is `nestRow k`.

-- THE WIDTH READ AS A LOWER BOUND, because the real one stopped
-- rendering when it became the registry cap and `capsAt` does not
-- terminate.  Every charge below that used to spell `realWidAt e sl 0`
-- now spells the REGISTRY LENGTH, which the true width dominates
-- wherever `capsOK?` holds -- the same premise no row here can
-- discharge anyway.  So a row reading `ok` is evidence for its target a
-- fortiori, and a row reading OVER is INCONCLUSIVE rather than a
-- refutation: it says the honest width was needed, not that the bound
-- is short.
regW : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} → EvalSt e → ℕ
regW st = length (EvalSt.registry st)

-- SERIES D — `depth-nest-compositional`'s conclusion at the ROOT call,
-- which is the instance `depthE≤capsH-root` spends and the one index
-- where the fresh term is `capsBase` rather than the wrap tower.  Both
-- sides compute; only the `capsOK?` premise does not: `capsOK?` reads
-- `capsAt`, which sits on the caps recurrence and does not terminate
-- even in native code, so no row can discharge it.  A row reading OVER
-- is a refutation candidate modulo that premise.
--
-- TARGET: depth-nest-compositional
depthRow : ℕ → ℕ → String
depthRow d k =
  let p   = progD d k
      sd  = sched-init p ins₀
      st  = st-init p
      lhs = depthE (budgetAt p ins₀ 0) p root 0 0 sd st
      rhs = nestDᵉ p + storeNestMax sd st
            + regW st * nestSyn p ins₀
  in "d=" ++ show d ++ " k=" ++ show k
     ++ "  depthE = " ++ show lhs
     ++ "  bound = " ++ show rhs
     ++ (if lhs ≤ᵇ rhs then "  ok" else "  OVER")

-- SERIES E — the same conclusion at an INNER subject under a CLIMBED
-- path, which is the axis Series D fixes.  The state is the one the
-- root subscribe hands over, so it is reached by running; only the
-- subject and the path are chosen, and the statement quantifies over
-- both.  `thru-outer` peels one `obs`, so the two move together.
--
-- TARGET: depth-nest-compositional
depthRowInner : ℕ → ℕ → ℕ → String
depthRowInner j d k =
  let p   = progD d k
      r   = subscribeE (gasPad (sucG p) g0) p root 0 0
                       (sched-init p ins₀) (st-init p)
      sd  = proj₁ (proj₂ r)
      st  = proj₂ (proj₂ r)
      b   = subjN j d k
      κ   = pathN j
      lhs = depthE (budgetAt p ins₀ 0) b κ 0 0 sd st
      rhs = nestDᵉ b + pathNestD κ + storeNestMax sd st
            + regW st * nestSyn p ins₀
  in "j=" ++ show j ++ " d=" ++ show d ++ " k=" ++ show k
     ++ "  depthE = " ++ show lhs
     ++ "  bound = " ++ show rhs
     ++ (if lhs ≤ᵇ rhs then "  ok" else "  OVER")


-- SERIES H — the same walk read against the DEPTH face rather than the
-- delivery face, which is the half Series D and E left at the state the
-- subscribe frame produced.  Re-descending the root subject from a state
-- deep in a run is a real question and not a repeat of the delivery face: the two
-- faces charge different things, so a margin that is invariant for one
-- carries nothing about the other.
--
-- TARGET: depth-nest-compositional
depthRunWalk : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
          → ℕ → ℕ → Sched Γ → EvalSt e → String
depthRunWalk e sl 0       nextId sched st = ""
depthRunWalk e sl (suc m) nextId sched st with sched-next sched
... | inj₁ _        = " [done]"
... | inj₂ (a , sd) =
  let lhs = depthE (budgetAt e sl 0) e root 0 0 sched st
      rhs = nestDᵉ e + storeNestMax sched st
            + regW st * nestSyn e sl
      r   = cascade a nextId sd st
  in " | " ++ show lhs ++ "/" ++ show rhs
     ++ (if lhs ≤ᵇ rhs then " ok" else " OVER")
     ++ depthRunWalk e sl m (suc nextId)
                  (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

depthRunWalkRow : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → String
depthRunWalkRow steps ds ks j d k =
  let sl = insT ds ks j
      p  = progT d k
      r  = subscribeE (gasPad (sucGT ds ks j d k) g0) p root 0 0
                      (sched-init p sl) (st-init p)
  in "ds=" ++ show ds ++ " ks=" ++ show ks ++ " j=" ++ show j
     ++ " d=" ++ show d ++ " k=" ++ show k
     ++ depthRunWalk p sl steps 1 (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

-- SERIES J — both walks over the LATE-CONNECT family, which is the only
-- one here whose slot state moves after the root subscribe.  Series H
-- read the depth face along a run and reported a constant; that row is
-- degenerate rather than reassuring, because the T family spends its
-- share in the subscribe burst and the descent has nothing left to see.
-- J is where the depth face's state axis is actually load-bearing: if
-- the mid-run connect raises the descent above the bound, this is the
-- row that says so.
--
-- TARGET: depth-nest-compositional
depthRunWalkRowU : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → String
depthRunWalkRowU steps ds ks j d k =
  let sl = insT ds ks j
      p  = progU d k
      r  = subscribeE (gasPad (sucGU ds ks j d k) g0) p root 0 0
                      (sched-init p sl) (st-init p)
  in "ds=" ++ show ds ++ " ks=" ++ show ks ++ " j=" ++ show j
     ++ " d=" ++ show d ++ " k=" ++ show k
     ++ depthRunWalk p sl steps 1 (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

-- SERIES Y (12000000): DOES THE WALK'S STORE GROWTH SATURATE OR
-- ACCUMULATE?  This is the one question that decides the shape of the
-- store row's induction, and it is decidable by instantiation because
-- `storeNestMax` is a MAX -- a `⊔` of four `⊔`-folds -- so a walk that
-- stores repeatedly need not grow repeatedly.  A row runs `cascadeGo`
-- on every PREFIX of the arrival's chain list and prints the store
-- after each, so the sequence itself is the answer: flat after the
-- first step means the max absorbs every later one and the induction
-- needs no budget, while a sequence that climbs per step means the
-- growth has to be threaded and the width factor is what pays.
--
-- LOAD-BEARING only where the chain list has more than one entry; a
-- one-chain family reports a two-element sequence that cannot
-- distinguish the two readings, so `c` is printed and a row with `c`
-- at one is evidence about nothing here.
--
-- TARGET: cascade-nest-store
pfxL : ∀ {A : Set} → ℕ → List A → List A
pfxL 0       xs       = []
pfxL (suc i) []       = []
pfxL (suc i) (x ∷ xs) = x ∷ pfxL i xs

satGo : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (a : Arrival Γ) → ℕ
      → List (RegId × Path Γ (arrTy a) t) → Sched Γ → EvalSt e → ℕ → String
satGo a nextId ch sd stL 0       = ""
satGo a nextId ch sd stL (suc i) =
  let g = cascadeGo a nextId (pfxL (suc i) ch) sd stL
  in " " ++ show (suc i) ++ ":"
     ++ show (storeNestMax (proj₁ (proj₂ g)) (proj₂ (proj₂ g)))
     ++ satGo a nextId ch sd stL i

four : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} → Sched Γ → EvalSt e → String
four sched st =
  "[sl=" ++ show (slotsNestSum (Sched.slots sched))
  ++ " lv=" ++ show (foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched))
  ++ " nd=" ++ show (foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st))
  ++ " rg=" ++ show (regsNestMax (EvalSt.registry st)) ++ "]"

satWalk : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
        → ℕ → ℕ → Sched Γ → EvalSt e → String
satWalk e sl 0       nextId sched st = ""
satWalk {n = n} e sl (suc m) nextId sched st with sched-next sched
... | inj₁ _        = " [done]"
... | inj₂ (a , sd) =
  let stL = cascadeLatch a st
      ch  = chainsOf a st
      g   = cascadeGo a nextId ch sd stL
      aft = storeNestMax (proj₁ (proj₂ g)) (proj₂ (proj₂ g))
      dep = depthCascade a nextId ch sd stL
      nv  = nestDᵛ (arrTy a) (arrVal a)
      cn  = chainsNestD ch
      r   = cascade a nextId sd st
  in " | c=" ++ show (length ch)
     ++ " d=" ++ show (delivN stL (proj₂ (proj₂ g)))
     ++ " S=" ++ show (storeNestMax sd stL)
     ++ " ns=" ++ show (nestSyn e sl)
     ++ " N=" ++ show nv ++ " C=" ++ show cn
     ++ " D=" ++ show dep ++ " A=" ++ show aft
     ++ " B" ++ four sd stL
     ++ " A" ++ four (proj₁ (proj₂ g)) (proj₂ (proj₂ g))
     ++ " nn=" ++ show (Sched.nextNode sd)
     ++ "→" ++ show (Sched.nextNode (proj₁ (proj₂ g)))
     ++ (let ndB = foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes stL)
             ndA = foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes (proj₂ (proj₂ g)))
             mm  = Sched.nextNode (proj₁ (proj₂ g)) ∸ Sched.nextNode sd
         in (if ndA ≤ᵇ ndB + mm * nestSyn e sl then " MINT-ok" else " MINT-FAIL")
            ++ " m=" ++ show mm
            ++ " reg=" ++ show (regW (proj₂ (proj₂ g)))
            ++ (if nestOK? e sl 0 sd stL then " NEST0-holds" else " NEST0-fails")
            ++ (let sz = sizeᵉ e + slotsSize sl
                in " sz=" ++ show sz
                   ++ (if mm ≤ᵇ sz then " SZ-ok" else " SZ-OVER"))
            ++ (let ec = entryCeil n sl e
                in " ec=" ++ show ec
                   ++ (if mm ≤ᵇ ec then " EC-ok" else " EC-OVER")))
     ++ (if dep ≤ᵇ suc aft then " ok" else " AFT-OVER")
     ++ (if dep ≤ᵇ nv + cn + aft then "" else " BASE-OVER")
     ++ " |" ++ satGo a nextId ch sd stL (length ch)
     ++ satWalk e sl m (suc nextId)
                (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

-- SERIES S (6000000): is the SUBSCRIBE side also width-blind?  The
-- delivery leaf turned out to need one `nestSyn` and no width, for a
-- reason that says nothing about deliveries in particular -- nesting
-- depth does not see width.  If that reason is the whole story then
-- `depthE` fits the same bound with a single `nestSyn` too, the
-- nineteen-member family it belongs to has ONE uniform shape rather
-- than two, and the subscribe-side statement is a widening of it
-- rather than a separate induction.  This reads `depthE` against BOTH
-- bounds at once so the gap between them is visible.
--
-- LOAD-BEARING wherever `one` is smaller than `wide`, which is
-- everywhere the width exceeds one; a row where they coincide is
-- evidence about nothing
--
-- TARGET: depth-nest-compositional

-- SERIES S2 (7000000): the same question with the WIDTH actually
-- driven.  SERIES S runs on `progD`, whose subscribe registers one
-- thing at a time, so a one-`nestSyn` bound and a width-scaled one
-- cannot be told apart there any more than they could on the delivery
-- side.  This reads the ROOT subscribe of `progW`, where one emission
-- hands over `suc ww` inners, so the registration count the width term
-- is charged for is the swept axis.  If the subscribe side needs its
-- width anywhere, it needs it here
--
-- TARGET: depth-nest-compositional
depthWideRow : ℕ → ℕ → ℕ → ℕ → ℕ → String
depthWideRow ds ks j ww w =
  let slF = insF ds ks j
      p   = progW ww w 1
      r   = subscribeE (gasPad (sucGW ds ks j ww w 1) g0) p root 0 0
                       (sched-init p slF) (st-init p)
      sd  = proj₁ (proj₂ r)
      st  = proj₂ (proj₂ r)
      κ   = root
      lhs = depthE (budgetAt p slF 0) p κ 0 0 sd st
      bas = nestDᵉ p + pathNestD κ + storeNestMax sd st
      one = bas + nestSyn p slF
      wid = bas + regW st * nestSyn p slF
  in "ww=" ++ show ww ++ " w=" ++ show w
     ++ "  depthE=" ++ show lhs
     ++ "  one=" ++ show one ++ "  wide=" ++ show wid
     ++ (if lhs ≤ᵇ one then "  ok" else "  ONE-OVER")

-- SERIES T (8000000): the CONCAT DRAIN arc, which is the one arc of the
-- depth family whose `suc` the bound has no path term to pay.  A
-- `thru-outer` frame's `suc` is paid by `pathNestD`, which charges that
-- frame and only that frame — but `depthFinC`'s drain also spends a
-- `suc`, and it is reached through a `from-inner` frame, which the path
-- measure charges nothing for.  So on the accounting the drain's level
-- has to come out of the single `nestSyn`, and whether that is enough is
-- not something reading the definitions settles.  `progU` is the
-- limit-1 mergeAll family — three inners queued behind one — so its root
-- subscribe is where the drain actually fires.
--
-- TARGET: depth-nest-compositional
depthConcatRow : ℕ → ℕ → ℕ → ℕ → ℕ → String
depthConcatRow ds ks j d k =
  let sl  = insT ds ks j
      p   = progU d k
      sd  = sched-init p sl
      st  = st-init p
      κ   = root
      lhs = depthE (budgetAt p sl 0) p κ 0 0 sd st
      bas = nestDᵉ p + pathNestD κ + storeNestMax sd st
      one = bas + nestSyn p sl
      wid = bas + regW st * nestSyn p sl
  in "ds=" ++ show ds ++ " ks=" ++ show ks ++ " j=" ++ show j
     ++ " d=" ++ show d ++ " k=" ++ show k
     ++ "  depthE=" ++ show lhs
     ++ "  one=" ++ show one ++ "  wide=" ++ show wid
     ++ (if lhs ≤ᵇ one then "  ok" else "  ONE-OVER")

-- SERIES U (10000000): THE ONE REGION NEITHER REMOVED PRIMITIVE COULD
-- REACH.  Every probe and every refutation in this campaign was built
-- on a family whose limits are `nothing` or `just 1`, because until
-- the syntax moved those were the only two that existed — so the
-- bounded gate, the whole content of the change, has no coverage at
-- all.  `progB` moves that axis alone: at `lim = 0` it is `progU`
-- exactly, which makes the row its own control, and above that the
-- drain has to refill several lanes in one instant.
--
-- LOAD-BEARING: the row asks whether the drain arc still fits the single
-- `nestSyn` once the gate has to refill several lanes at once, and
-- `ONE-OVER` is the answer SERIES T was built to look for.  A row where
-- the two `lim` values print the same numbers is the finding that the
-- gate costs nothing, which is what the depth mirror's
-- over-approximation predicts.
--
-- TARGET: depth-nest-compositional
depthLimRow : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → String
depthLimRow lim ds ks j d k =
  let sl  = insT ds ks j
      p   = progB lim d k
      sd  = sched-init p sl
      st  = st-init p
      κ   = root
      lhs = depthE (budgetAt p sl 0) p κ 0 0 sd st
      bas = nestDᵉ p + pathNestD κ + storeNestMax sd st
      one = bas + nestSyn p sl
      wid = bas + regW st * nestSyn p sl
      r   = subscribeE (gasPad (sucGB ds ks j lim d k) g0) p root 0 0 sd st
  in "lim=" ++ show (suc lim) ++ " ds=" ++ show ds ++ " ks=" ++ show ks
     ++ " j=" ++ show j ++ " d=" ++ show d ++ " k=" ++ show k
     ++ "  depthE=" ++ show lhs ++ "  one=" ++ show one
     ++ "  wide=" ++ show wid
     ++ (if lhs ≤ᵇ one then "  ok" else "  ONE-OVER")
     ++ (if lhs ≤ᵇ wid then "" else "  WIDE-OVER")

-- SERIES V.  The same verdict as SERIES U, over `progN`, whose
-- source width is an axis of its own.  This is the only family in which
-- the gate is a gate: at `w` inners and limit `l` with `l < w` the drain
-- parks, refills, and parks again, which is the state no probe in this
-- campaign has ever reached -- every earlier family predates the limit
-- argument and so sits at one of the two saturated ends.
--
-- TARGET: depth-nest-compositional
depthFanRow : ℕ → ℕ → ℕ → ℕ → String
depthFanRow lim w d k =
  let sl  = insT 1 1 1
      p   = progN lim w d k
      sd  = sched-init p sl
      st  = st-init p
      κ   = root
      lhs = depthE (budgetAt p sl 0) p κ 0 0 sd st
      bas = nestDᵉ p + pathNestD κ + storeNestMax sd st
      one = bas + nestSyn p sl
      wid = bas + regW st * nestSyn p sl
      r   = subscribeE (gasPad (sucGN 1 1 1 lim w d k) g0) p root 0 0 sd st
  in "lim=" ++ show (suc lim) ++ " w=" ++ show (2 + suc w)
     ++ " d=" ++ show d ++ " k=" ++ show k
     ++ "  depthE=" ++ show lhs ++ "  one=" ++ show one
     ++ "  wide=" ++ show wid
     ++ (if lhs ≤ᵇ one then "  ok" else "  ONE-OVER")
     ++ (if lhs ≤ᵇ wid then "" else "  WIDE-OVER")

depthOneRow : ℕ → ℕ → ℕ → String
depthOneRow j d k =
  let p   = progD d k
      r   = subscribeE (gasPad (sucG p) g0) p root 0 0
                       (sched-init p ins₀) (st-init p)
      sd  = proj₁ (proj₂ r)
      st  = proj₂ (proj₂ r)
      b   = subjN j d k
      κ   = pathN j
      lhs = depthE (budgetAt p ins₀ 0) b κ 0 0 sd st
      bas = nestDᵉ b + pathNestD κ + storeNestMax sd st
      one = bas + nestSyn p ins₀
      wid = bas + regW st * nestSyn p ins₀
  in "j=" ++ show j ++ " d=" ++ show d ++ " k=" ++ show k
     ++ "  depthE=" ++ show lhs
     ++ "  one=" ++ show one ++ "  wide=" ++ show wid
     ++ (if lhs ≤ᵇ one then "  ok" else "  ONE-OVER")

chainsRep : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
          → (a : Arrival Γ) → Id → List (RegId × Path Γ (arrTy a) t)
          → Sched Γ → EvalSt e → String
chainsRep e sl a nid []              sched st = ""
chainsRep e sl a nid ((rid , c) ∷ cs) sched st =
  let st₀ = record st { delivered = rid ∷ EvalSt.delivered st }
      lhs = depthChain nid a c sched st₀
      rhs = nestDᵛ (arrTy a) (arrVal a) + pathNestD c
            + storeNestMax sched st₀ + nestSyn e sl
      k   = chainStep nid a c sched st₀
  in " [" ++ show lhs ++ "/" ++ show rhs
     ++ (if lhs ≤ᵇ rhs then "" else " CHAIN-OVER") ++ "]"
     ++ chainsRep e sl a nid cs (proj₁ (proj₂ k)) (proj₂ (proj₂ k))

leafWalk : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
         → ℕ → ℕ → Sched Γ → EvalSt e → String
leafWalk e sl 0       nextId sched st = ""
leafWalk e sl (suc m) nextId sched st with sched-next sched
... | inj₁ _        = " [done]"
... | inj₂ (a , sd) =
  let stL = cascadeLatch a st
      r   = cascade a nextId sd st
  in " |" ++ chainsRep e sl a nextId (chainsOf a st) sd stL
     ++ leafWalk e sl m (suc nextId)
                 (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
satRow : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → String
satRow fam ds ks j w k =
  let slF = insF ds ks j
  in if fam ≡ᵇ 0
     then (let p = progC ds w k
               r = subscribeE (gasPad (sucGC ds ks j ds w k) g0) p root 0 0
                              (sched-init p slF) (st-init p)
           in "C dd=" ++ show ds ++ " w=" ++ show w ++ " k=" ++ show k
              ++ satWalk p slF 3 1 (proj₁ (proj₂ r)) (proj₂ (proj₂ r)))
     else if fam ≡ᵇ 4
     then (let p = progU w k
               r = subscribeE (gasPad (sucGU ds ks j w k) g0) p root 0 0
                              (sched-init p slF) (st-init p)
           in "Uh d=" ++ show w ++ " k=" ++ show k
              ++ satWalk p slF 3 1 (proj₁ (proj₂ r)) (proj₂ (proj₂ r)))
     else if fam ≡ᵇ 2
     then (let p = progW ds w k
               r = subscribeE (gasPad (sucGW ds ks j ds w k) g0) p root 0 0
                              (sched-init p slF) (st-init p)
           in "W ww=" ++ show ds ++ " w=" ++ show w ++ " k=" ++ show k
              ++ satWalk p slF 3 1 (proj₁ (proj₂ r)) (proj₂ (proj₂ r)))
     else if fam ≡ᵇ 5
     then (let slO = insT ds ks j
               p = progO w k
               r = subscribeE (gasPad (sucGO ds ks j w k) g0) p root 0 0
                              (sched-init p slO) (st-init p)
           in "O d=" ++ show w ++ " k=" ++ show k
              ++ satWalk p slO 3 1 (proj₁ (proj₂ r)) (proj₂ (proj₂ r)))
     else if fam ≡ᵇ 3
     then (let slT = insT ds ks j
               p   = progU w k
               r   = subscribeE (gasPad (sucGU ds ks j w k) g0) p root 0 0
                                (sched-init p slT) (st-init p)
           in "U d=" ++ show w ++ " k=" ++ show k
              ++ satWalk p slT 3 1 (proj₁ (proj₂ r)) (proj₂ (proj₂ r)))
     else (let p = progF w k
               r = subscribeE (gasPad (sucGF ds ks j w k) g0) p root 0 0
                              (sched-init p slF) (st-init p)
           in "F ds=" ++ show ds ++ " w=" ++ show w ++ " k=" ++ show k
              ++ satWalk p slF 3 1 (proj₁ (proj₂ r)) (proj₂ (proj₂ r)))
nestRow : ℕ → String
nestRow 0 = "capsBase (progD 1 1) ins₀ = "      ++ show (capsBase (progD 1 1) ins₀)
nestRow 1 = "nestSyn (progD 1 1) ins₀ = "       ++ show (nestSyn (progD 1 1) ins₀)
nestRow 2 = "nestCapAt (progD 1 1) ins₀ 0 = "   ++ show (nestCapAt (progD 1 1) ins₀ 0)
nestRow 4 = "nestCapAt (progD 1 1) ins₀ 1 = "   ++ show (nestCapAt (progD 1 1) ins₀ 1)
nestRow 6 = "nestCapAt (progD 1 1) ins₀ 2 = "   ++ show (nestCapAt (progD 1 1) ins₀ 2)
nestRow _ = "(no such row)"

-- the second half of the dispatch, split off only because one function
-- with this many arms is unreadable.  Ranges are stable: a row index
-- written down in a receipt has to keep meaning what it meant.
rowAt′ : ℕ → String
rowAt′ n =
  if 700000 ≤ᵇ n
  then (let m = n ∸ 700000
        in depthRunWalkRowU 16 ((m % 100000) / 10000)
                            ((m % 10000) / 1000) ((m % 1000) / 100)
                            ((m % 100) / 10) (m % 10))
  else if 600000 ≤ᵇ n
  then (let m = n ∸ 600000
        in depthRunWalkRow 12 ((m % 100000) / 10000)
                           ((m % 10000) / 1000) ((m % 1000) / 100)
                           ((m % 100) / 10) (m % 10))
  else if 300000 ≤ᵇ n
  then (let m = n ∸ 300000
        in depthRowInner (m / 10000) ((m % 10000) / 100) (m % 100))
  else if 200000 ≤ᵇ n
  then (let m = n ∸ 200000
        in depthRow (m / 100) (m % 100))
  else if 20 ≤ᵇ n then nestRow (n ∸ 20)
  else "(no such row)"

------------------------------------------------------------------
-- stdin: a single row index.  Anything unparseable reads as 0, which is
-- the calibration row — the safe default, since a mis-typed index then
-- reports the one number whose expected value is written down.
------------------------------------------------------------------

private
  isDigit : ℕ → Bool
  isDigit c = if 48 ≤ᵇ c then c ≤ᵇ 57 else false

  digits : List ℕ → ℕ → ℕ
  digits []       acc = acc
  digits (c ∷ cs) acc =
    if isDigit c then digits cs (acc * 10 + (c ∸ 48)) else acc

  skipToDigit : List ℕ → List ℕ
  skipToDigit []       = []
  skipToDigit (c ∷ cs) = if isDigit c then (c ∷ cs) else skipToDigit cs

rowAt : ℕ → String
rowAt 0 = "CALIBRATION towerℕ 4 (refl-pinned 65536 in this module) = "
            ++ show calibration
-- towerℕ is the SCALE REFERENCE, not a target: it is the one member of
-- this neighbourhood the typechecker also evaluates, and it shows how
-- fast the caps arithmetic's inputs climb.  towerℕ 5 = 2^65536 is a
-- ~19730-digit number, hence printed as its digit count rather than in
-- full.
rowAt 1 = "towerℕ 3 = " ++ show (towerℕ 3)
rowAt 2 = "towerℕ 4 = " ++ show (towerℕ 4)

------------------------------------------------------------------
-- SERIES N, THE NESTING CURRENCY — rows 20-26.  The re-denominated cap
-- is the one quantity in this neighbourhood designed to stay OFF the
-- caps recurrence, so unlike the anchor it has no `blowH` in it and
-- there is a real question whether it computes.  These rows answer
-- that question and nothing else: they are a COMPUTABILITY BOUNDARY,
-- not evidence for any inequality, because the side these caps would
-- have to fit under is the anchor and the anchor does not compute.
--
-- AND THE ANSWER IS NOW HALF NO, WHICH IS THE FINDING.  The width is
-- the registry cap, so it sits ON the caps recurrence after all and no
-- row of it renders at any index; the rows that read it are gone.  What
-- is left is the CAP side, which is a syntactic reading and does
-- compute — row 20 load-bearing in the weakest sense that matters
-- here, since `capsBase` reaches `entryCeil` and a divergence there
-- would make even the cap symbolic-only.
--
-- TARGET: nest-height
------------------------------------------------------------------

------------------------------------------------------------------
-- QUARANTINE.  The caps counting family is UNREACHABLE BY MEASUREMENT,
-- and compiling it does not change that.
--
-- WHAT WAS TRIED.  This harness was built partly on the hypothesis that
-- `poolCount`'s silence in the typechecker was OPACITY (`fLvlD` is
-- `abstract` at Rx.Evaluator, `blowH` at :899) and that the GHC backend,
-- which ignores `abstract`, would therefore compute it.
--
-- WHAT HAPPENED.  Native, -O, at the SMALLEST POSSIBLE ARGUMENTS:
-- `poolCount 1 0` and `blowH 0` each still running at 45 s, killed with
-- no value.  Row 0 calibrated at 65536 in the same binary, so this is
-- not a broken build — it is the arithmetic.
--
-- WHY IT IS STRUCTURAL, not a matter of waiting longer or of hardware:
-- `blowH m = 6 + m + 2 * poolCount (towerℕ m) m` feeds `poolCount` a
-- TOWER as its first argument, and `poolCount` pools that through
-- `lvls`/`dLvl`/`iterL`, where `dLvl S W d J = iterL S W d (suc (sizeAt S J)) J`
-- iterates a number that itself grows with the level.  The value is
-- astronomically large by construction; no backend prints it.
--
-- CONSEQUENCE — this CONFIRMS the ruling "THE ANCHOR CANNOT
-- BE PROBED" by an INDEPENDENT route (native code, no typechecker in the
-- loop), and confirms its stated reason: the blowup is COMPUTATIONAL,
-- not definitional.  Un-sealing the `abstract` blocks would not help,
-- and neither would a faster machine.  **Do not build a probe, a
-- harness row, or a `refl` pin against this family.  The anchor is
-- symbolic-or-nothing.**
------------------------------------------------------------------

rowAt 10 = "poolCount 1 0 = " ++ show (poolCount 1 0)   -- DIVERGENT (45s+, killed)
rowAt 11 = "poolCount 1 1 = " ++ show (poolCount 1 1)   -- DIVERGENT
rowAt 12 = "poolCount 2 0 = " ++ show (poolCount 2 0)   -- DIVERGENT
rowAt 13 = "blowH 0 = "       ++ show (blowH 0)         -- DIVERGENT (45s+, killed)
rowAt 14 = "blowH 1 = "       ++ show (blowH 1)         -- DIVERGENT
rowAt 15 = "capsHgo 0 0 = "   ++ show (capsHgo 0 0)     -- DIVERGENT
rowAt 16 = "lvls 1 1 0 0 1 = "  ++ show (lvls 1 1 0 0 1)
rowAt 17 = "iterL 1 1 0 1 0 = " ++ show (iterL 1 1 0 1 0)
-- THE SWEEPABLE ROW — `d*100 + k + 1000`, so 1608 is (6,8).  Rows 6-8
-- above are the three points the model singles out; this one exists
-- because the COST CURVE of the family had to be measured before any of
-- them could be trusted to terminate, and a rebuild per point is not a
-- measurement loop.  Prints the sum side and the verdict together, so a
-- row is readable without cross-referencing row 5.
rowAt n =
  if 20000000 ≤ᵇ n
  then (let m = n ∸ 20000000
        in depthFanRow (m / 1000) ((m % 1000) / 100)
                       ((m % 100) / 10) (m % 10))
  else if 12000000 ≤ᵇ n
  then (let m = n ∸ 12000000
        in satRow (m / 100000) ((m % 100000) / 10000)
                  ((m % 10000) / 1000) ((m % 1000) / 100)
                  ((m % 100) / 10) (m % 10))
  else if 10000000 ≤ᵇ n
  then (let m = n ∸ 10000000
        in depthLimRow (m / 100000) ((m % 100000) / 10000)
                       ((m % 10000) / 1000) ((m % 1000) / 100)
                       ((m % 100) / 10) (m % 10))
  else if 8000000 ≤ᵇ n
  then (let m = n ∸ 8000000
        in depthConcatRow (m / 10000) ((m % 10000) / 1000) ((m % 1000) / 100)
                          ((m % 100) / 10) (m % 10))
  else if 7000000 ≤ᵇ n
  then (let m = n ∸ 7000000
        in depthWideRow (m / 10000) ((m % 10000) / 1000) ((m % 1000) / 100)
                        ((m % 100) / 10) (m % 10))
  else if 6000000 ≤ᵇ n
  then (let m = n ∸ 6000000
        in depthOneRow (m / 10000) ((m % 10000) / 100) (m % 100))
  else rowAt′ n

main : IO Unit
main = getContents >>= λ s →
  putStr (rowAt (digits (skipToDigit (map toℕ (toList s))) 0) ++ "\n")
