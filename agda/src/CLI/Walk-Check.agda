-- THE IMPL RUN'S OWN DERIVATION, WALKED: every claim the simulation
-- threads through a walk, decided at the very state the walk hands it.
-- The store harness reads a run only where an arrival ends, and the
-- ended-outer leaves are about states INSIDE a walk -- an end crossing a
-- frame, an outer's wrap, a subscribe below a flattener -- which no
-- boundary shows.  A derivation binds every one of those states, so the
-- walker reads them off it, one clause per constructor.
--
-- WHY A BINARY OF ITS OWN.  The derivation is `Σ⁰.snd⁰` of the builder's
-- answer, and the oracle's tree erases it along with every proof it
-- carries; unerasing it alone does not typecheck, since it is built
-- through erased answers.  So this module is compiled only in a tree that
-- keeps the markers as comments (`make walk-build`), and nothing the
-- erased tree builds imports it.
--
-- WHAT IS DECIDED, BY TAG:
--   `carry`     a fold carrying an end down a path finds `Gone` there --
--               what `Steps` asks of every frame, and what every
--               `gone-*` leaf is a starting point of;
--   `lanes`     an outer's wrap that reports its flattener idle finds no
--               alive row down an inner lane (`idle-lanes`), counted
--               where the lane held a row as the outer's end arrived;
--   `subscribe` a path being subscribed finds `Gone` (`gone-subscribed`);
--   `skipped`   a share reader skipped at its fan-out finds `Gone`
--               (`gone-skipped`);
--   `dying`     a fold keeps every dying mark it starts with (`dying-kept`);
--   `control`   a fold carrying values and NO end, decided as `carry`: a
--               row walking its own path is alive there, so this one
--               fails, and its failures are what show the decider fires;
--   `finish`, `cut`, `wrap`   a `carry` whose end the frame just above
--               HANDED ON, counted again under the leaf it concludes: an
--               inner's finish ending its flattener (`gone-finish`), a take
--               cutting with no end come into it (`gone-cut`), an outer's
--               idle wrap (`gone-wrap`, over `gone-walk` and `idle-lanes`);
--   `walk`      an outer's walk that starts with its path `Gone` ends with
--               it `Gone` (`gone-walk`).
--
-- A check COUNTS where something could break it: an alive row meeting the
-- path (at the walk's end, for `walk`), a lane holding a row, a dying mark
-- at the fold's start.
module CLI.Walk-Check where

open import Data.Bool    using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.Bool.ListAction using (any; all)
open import Data.List    using (List; []; _∷_; _++_; length; filterᵇ)
open import Data.Nat     using (ℕ; _+_; _≡ᵇ_)
open import Data.Nat.Show using (show)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String  using (String) renaming (_++_ to _++ˢ_)

open import Rx.Prim      using (Fuel)
open import Rx.Exp       using (Ctx; Closed)
open import Rx.Evaluator using (EvalSt; Path; RegRow; NodeId; _↠[_]_; Frame; map-f; from-inner; thru-outer;
  memberSource; regSource; regFloor; skipᵇ; thruWrap)
open import Rx.Evaluator.Domain using (subscribeE⇓; subscribeInner⇓; thruConsume⇓; thruWalk⇓; mergeAllDrain⇓;
  innerFinish⇓; innerReact⇓; stepFrame⇓; subscribeAll⇓; sharedConnect⇓; subscribeSharedSlot⇓; dispatchShare⇓;
  shareWalk⇓; shareGo⇓; foldPath⇓; chainStep⇓; cascadeGo⇓; cascade⇓; drain⇓; evaluate⇓;
  subs-floor; subs-shared; subs-hot-done; subs-hot-live; subs-cold-sync; subs-cold-async; subs-of; subs-empty;
  subs-takeWhile; subs-batchSync; subs-map; subs-scan; subs-flatten; subs-μ; subs-defer; subs-mint;
  inner; consume-all-sub; consume-all-enqueue; consume-all-nil; consume-switch-sub; consume-switch-nil;
  consume-exhaust-sub; consume-exhaust-nil; walk-nil; walk-echo; walk-cons;
  drain-spent; drain-nil; drain-no-room; drain-room;
  finish-all-drain; finish-switch-clear; finish-exhaust-clear; finish-nil;
  react-false; react-alive; react-dead;
  step-map; step-scan; step-take; step-batchSync; step-from-inner; step-thru-outer;
  sub-all; connect; slot-spent; slot-join; slot-connect; disp; walk-end; walk-more;
  go-nil; go-cut; go-live; fold-root; fold-sink; fold-step; chain-step;
  casc-nil; casc-cut; casc-live; casc-run; casc-run-last; drain-done; drain-empty; drain-step; eval-run)
open import Rx.Evaluator.Builder using (evaluate!)
open import Rx.Evaluator.Reducible.Support using (Σ⁰)
open import SExp.Syntax  using (SExp; Kinds)
open import SExp.Simul-Slots using (SimulSlots)
open import SExp.Impl-Slots using (elaborateImpl; embedSlotsImpl)
open import CLI.Emit-Eq  using (eqListℕ)
open import CLI.Store-Check using (headKey; frameKey; skel)

-- a check's tag, whether it held, whether anything could have broken it,
-- and what to print if it did not hold
Ev : Set
Ev = ℕ × Bool × Bool × String

carryᵗ lanesᵗ subscribeᵗ skippedᵗ dyingᵗ controlᵗ finishᵗ cutᵗ wrapᵗ walkᵗ : ℕ
carryᵗ     = 0
lanesᵗ     = 1
subscribeᵗ = 2
skippedᵗ   = 3
dyingᵗ     = 4
controlᵗ   = 5
finishᵗ    = 6
cutᵗ       = 7
wrapᵗ      = 8
walkᵗ      = 9

tagName : ℕ → String
tagName 0 = "carry"
tagName 1 = "lanes"
tagName 2 = "subscribe"
tagName 3 = "skipped"
tagName 4 = "dying"
tagName 5 = "control"
tagName 6 = "finish"
tagName 7 = "cut"
tagName 8 = "wrap"
tagName _ = "walk"

module Decide {m} {Δ : Ctx m} {u} {e : Closed Δ u} where

  rowPath : (r : RegRow Δ u) → Path Δ (regFloor (proj₁ (proj₂ r))) (proj₁ (proj₂ (proj₂ r))) u
  rowPath r = proj₂ (proj₂ (proj₂ r))

  alive : EvalSt e → RegRow Δ u → Bool
  alive st r = not (skipᵇ (regSource (proj₁ (proj₂ r))) (proj₁ r) st)

  -- `Passes`, read off a path
  passes : ∀ {lo s v} → List ℕ → Path Δ lo s v → Bool
  passes key (f ↠[ _ ] q) = eqListℕ (frameKey f) key ∨ passes key q
  passes key _            = false

  -- any of a flattener's lanes
  lane : ∀ {lo s v} → NodeId → Path Δ lo s v → Bool
  lane k (from-inner _ k′ _ ↠[ _ ] q) = (k′ ≡ᵇ k) ∨ lane k q
  lane k (_ ↠[ _ ] q)                 = lane k q
  lane k _                            = false

  -- `Through`
  through : ∀ {s v lo s′ v′} → Frame Δ s v → Path Δ lo s′ v′ → Bool
  through (from-inner _ k _) p = passes (2 ∷ k ∷ []) p ∨ lane k p
  through (thru-outer _ k)   p = passes (2 ∷ k ∷ []) p ∨ lane k p
  through f                  p = passes (frameKey f) p

  -- `Clean`, then `Fed`, as `Simulation.Arm` states them
  cleanᵇ : ∀ {lo s} → Path Δ lo s u → EvalSt e → Bool
  cleanᵇ q st = all (λ r → not (alive st r) ∨ not (passes (headKey q) (rowPath r))) (EvalSt.registry st)

  fedᵇ : ∀ {lo s} → Path Δ lo s u → EvalSt e → Bool
  fedᵇ (map-f _ ↠[ _ ] q) st = fedᵇ q st
  fedᵇ (f ↠[ _ ] q)       st =
    all (λ r → not (alive st r) ∨ not (passes (headKey q) (rowPath r)) ∨ through f (rowPath r)) (EvalSt.registry st)
    ∧ fedᵇ q st
  fedᵇ _                  st = true

  goneᵇ : ∀ {lo s} → Path Δ lo s u → EvalSt e → Bool
  goneᵇ q st = cleanᵇ q st ∧ fedᵇ q st

  -- the node keys a path names
  keys : ∀ {lo s v} → Path Δ lo s v → List (List ℕ)
  keys (map-f _ ↠[ _ ] q) = keys q
  keys (f ↠[ _ ] q)       = frameKey f ∷ keys q
  keys _                  = []

  -- an alive row meets the path at one of its nodes
  meets : ∀ {lo s} → Path Δ lo s u → EvalSt e → Bool
  meets q st = any (λ r → alive st r ∧ any (λ k → passes k (rowPath r)) (keys q)) (EvalSt.registry st)

  -- the alive rows, for a report
  culprits : EvalSt e → String
  culprits st = go (filterᵇ (alive st) (EvalSt.registry st))
    where
    go : List (RegRow Δ u) → String
    go []       = ""
    go (r ∷ rs) = "\n      alive row #" ++ˢ show (proj₁ r) ++ˢ ": " ++ˢ skel (rowPath r) ++ˢ go rs

  goneAt : ℕ → ∀ {lo s} → Path Δ lo s u → EvalSt e → List Ev
  goneAt tag q st =
    (tag , goneᵇ q st , meets q st ,
     tagName tag ++ˢ ": at " ++ˢ skel q
       ++ˢ (if cleanᵇ q st then " (clean, not fed)" else " (not clean)") ++ˢ culprits st) ∷ []

  -- counted where the lane was occupied when the outer's end came in, or
  -- still holds a row once its walk is done
  lanesAt : NodeId → EvalSt e → EvalSt e → List Ev
  lanesAt k st₀ st =
    (lanesᵗ ,
     all (λ r → not (alive st r) ∨ not (lane k (rowPath r))) (EvalSt.registry st) ,
     any (λ r → lane k (rowPath r)) (EvalSt.registry st₀ ++ EvalSt.registry st) ,
     "lanes: flattener #" ++ˢ show k ++ˢ " reported idle with an alive lane" ++ˢ culprits st) ∷ []

  dyingAt : List ℕ → EvalSt e → List Ev
  dyingAt ds st =
    (dyingᵗ , all (λ d → memberSource d (EvalSt.dying st)) ds , not (length ds ≡ᵇ 0) ,
     "dying: a fold dropped a dying mark") ∷ []

  -- the end a frame started, decided under the leaf that concludes it
  -- a take's end is a cut only where no end came into it
  started : ∀ {s v lo now f q vs sched st r} → (fin : Bool)
          → stepFrame⇓ {e = e} {s = s} {u = v} {lo = lo} now f q vs fin sched st r
          → ∀ {lo′ s′} → Path Δ lo′ s′ u → EvalSt e → List Ev
  started _     (step-from-inner _) q st = goneAt finishᵗ q st
  started false step-take           q st = goneAt cutᵗ q st
  started _     (step-thru-outer _) q st = goneAt wrapᵗ q st
  started _     _                   q st = []

  -- an outer's walk, read at the WHOLE path its fold was handed
  walked : ∀ {s v lo now f q vs fin sched st r}
         → stepFrame⇓ {e = e} {s = s} {u = v} {lo = lo} now f q vs fin sched st r
         → ∀ {lo′ s′} → Path Δ lo′ s′ u → EvalSt e → List Ev
  walked (step-thru-outer {st′ = st′} _) q st =
    (walkᵗ , not (goneᵇ q st) ∨ goneᵇ q st′ , goneᵇ q st ∧ meets q st′ ,
     "walk: an outer's walk lost `Gone` at " ++ˢ skel q
       ++ˢ (if cleanᵇ q st′ then " (clean, not fed)" else " (not clean)") ++ˢ culprits st′) ∷ []
  walked _ q st = []

  ------------------------------------------------------------------
  -- the walker: one clause per constructor, its premises walked in order
  ------------------------------------------------------------------

  wE  : ∀ {v lo X q now sched st r} → subscribeE⇓ {e = e} {u = v} {lo = lo} X q now sched st r → List Ev
  wI  : ∀ {v lo op k q now o sched st r} → subscribeInner⇓ {e = e} {u = v} {lo = lo} op k q now o sched st r → List Ev
  wC  : ∀ {v lo op k q now o sched st r} → thruConsume⇓ {e = e} {u = v} {lo = lo} op k q now o sched st r → List Ev
  wW  : ∀ {v lo op k q now os sched st r} → thruWalk⇓ {e = e} {u = v} {lo = lo} op k q now os sched st r → List Ev
  wD  : ∀ {s lo k q now fs lim act od qs sched st r} → mergeAllDrain⇓ {e = e} {s = s} {lo = lo} k q now fs lim act od qs sched st r → List Ev
  wFi : ∀ {s lo op k j q now vs sched st x r} → innerFinish⇓ {e = e} {s = s} {lo = lo} op k j q now vs sched st x r → List Ev
  wR  : ∀ {s lo op k j q now vs sched st b r} → innerReact⇓ {e = e} {s = s} {lo = lo} op k j q now vs sched st b r → List Ev
  wS  : ∀ {s v lo now f q vs fin sched st r} → stepFrame⇓ {e = e} {s = s} {u = v} {lo = lo} now f q vs fin sched st r → List Ev
  wA  : ∀ {v lo op ns b q now sched st r} → subscribeAll⇓ {e = e} {u = v} {lo = lo} op ns b q now sched st r → List Ev
  wSc : ∀ {lo i d q below now sched st r} → sharedConnect⇓ {e = e} {lo = lo} i d q below now sched st r → List Ev
  wSs : ∀ {lo i d q below now sched st r} → subscribeSharedSlot⇓ {e = e} {lo = lo} i d q below now sched st r → List Ev
  wDs : ∀ {lo now i below vs fin sched st r} → dispatchShare⇓ {e = e} {lo = lo} now i below vs fin sched st r → List Ev
  wSw : ∀ {now i vs fin sched st r} → shareWalk⇓ {e = e} now i vs fin sched st r → List Ev
  wSg : ∀ {lo now i vs fin ps sched st r} → shareGo⇓ {e = e} {lo = lo} now i vs fin ps sched st r → List Ev
  wF  : ∀ {v lo now q vs fin sched st r} → foldPath⇓ {e = e} {u = v} {lo = lo} now q vs fin sched st r → List Ev
  wCh : ∀ {a vs fin c sched st r} → chainStep⇓ {e = e} a vs fin c sched st r → List Ev
  wG  : ∀ {a vs fin cs sched st r} → cascadeGo⇓ {e = e} a vs fin cs sched st r → List Ev
  wK  : ∀ {a sched st r} → cascade⇓ {e = e} a sched st r → List Ev
  wDr : ∀ {k sched st r} → drain⇓ {e = e} k sched st r → List Ev

  wE {q = q} {st = st} d = goneAt subscribeᵗ q st ++ go d
    where
    go : ∀ {v lo X q now sched st r} → subscribeE⇓ {e = e} {u = v} {lo = lo} X q now sched st r → List Ev
    go (subs-floor _ f)                  = wF f
    go (subs-shared _ s)                 = wSs s
    go (subs-hot-done _ _ _ f)           = wF f
    go (subs-hot-live _ _ _ _)           = []
    go (subs-cold-sync _ _ f)            = wF f
    go (subs-cold-async _ _ _ _ _ f)     = wF f
    go (subs-of f)                       = wF f
    go (subs-empty f)                    = wF f
    go (subs-takeWhile _ s)              = wE s
    go (subs-batchSync _ s f)            = wE s ++ wF f
    go (subs-map s)                      = wE s
    go (subs-scan _ s)                   = wE s
    go (subs-flatten a)                  = wA a
    go (subs-μ s)                        = wE s
    go (subs-defer _ _ _ _)              = []
    go (subs-mint _ s)                   = wE s

  wI (inner _ s) = wE s

  wC (consume-all-sub _ _ s)      = wI s
  wC (consume-all-enqueue _ _)    = []
  wC (consume-all-nil _)          = []
  wC (consume-switch-sub _ _ _ s) = wI s
  wC (consume-switch-nil _)       = []
  wC (consume-exhaust-sub _ s)    = wI s
  wC (consume-exhaust-nil _)      = []

  wW walk-nil          = []
  wW (walk-echo f w)   = wF f ++ wW w
  wW (walk-cons c w)   = wC c ++ wW w

  wD drain-spent            = []
  wD drain-nil              = []
  wD (drain-no-room _)      = []
  wD (drain-room _ s _ d)   = wI s ++ wD d

  wFi (finish-all-drain f d)  = wF f ++ wD d
  wFi (finish-switch-clear _) = []
  wFi finish-exhaust-clear    = []
  wFi (finish-nil _)          = []

  wR react-false      = []
  wR (react-alive _)  = []
  wR (react-dead _ f) = wFi f

  -- AN OUTER'S WRAP: the walk below it, then the verdict read at the
  -- state the walk left
  wS step-map                 = []
  wS step-scan                = []
  wS step-take                = []
  wS step-batchSync           = []
  wS (step-from-inner r)      = wR r
  wS {f = thru-outer op k} {fin = fin} {st = st} (step-thru-outer {sched′ = sched′} {st′ = st′} w) =
    wW w ++ (if fin ∧ proj₁ (thruWrap op k true (sched′ , st′)) then lanesAt k st st′ else [])

  wA (sub-all _ s) = wE s

  wSc (connect _ s) = wE s

  wSs (slot-spent _ f)   = wF f
  wSs (slot-join _ _ _)  = []
  wSs (slot-connect _ _ c) = wSc c

  wDs (disp w) = wSw w

  wSw walk-nil        = []
  wSw (walk-end g)    = wSg g
  wSw (walk-more g w) = wSg g ++ wSw w

  wSg go-nil                              = []
  wSg {st = st} (go-cut {p = p} _ g)      = goneAt skippedᵗ p st ++ wSg g
  wSg (go-live _ f g)                     = wF f ++ wSg g

  -- EVERY FOLD: an end it carries finds `Gone`, a value-only one is the
  -- control, and every dying mark it starts with survives it
  wF {q = q} {vs = vs} {fin = fin} {st = st} {r = r} d =
    (if fin then goneAt carryᵗ q st
     else if length vs ≡ᵇ 0 then [] else goneAt controlᵗ q st)
    ++ dyingAt (EvalSt.dying st) (proj₂ (proj₂ r))
    ++ go d
    where
    go : ∀ {v lo now q vs fin sched st r} → foldPath⇓ {e = e} {u = v} {lo = lo} now q vs fin sched st r → List Ev
    go fold-root        = []
    go (fold-sink s)    = wDs s
    go {q = q} {fin = fin} {st = st} (fold-step {path′ = q′} {fin′ = fin′} {st₁ = st₁} s f) =
      wS s ++ walked s q st ++ (if fin′ then started fin s q′ st₁ else []) ++ wF f


  wCh (chain-step f) = wF f

  wG casc-nil          = []
  wG (casc-cut _ g)    = wG g
  wG (casc-live _ c g) = wCh c ++ wG g

  wK (casc-run _ g)        = wG g
  wK (casc-run-last _ g h) = wG g ++ wG h

  wDr drain-done         = []
  wDr (drain-empty _)    = []
  wDr (drain-step _ k d) = wK k ++ wDr d

  wEval : ∀ {fuel ins s} → evaluate⇓ {Γ = Δ} {t = u} fuel e ins s → List Ev
  wEval (eval-run s d) = wE s ++ wDr d

------------------------------------------------------------------
-- a case: the impl run, walked, tallied by tag
------------------------------------------------------------------

-- checked, counted, failed, and the first failure's report
Tally : Set
Tally = ℕ × ℕ × ℕ × String

tallyOf : ℕ → List Ev → Tally
tallyOf tag []                       = 0 , 0 , 0 , ""
tallyOf tag ((t , ok , c , w) ∷ evs) with tallyOf tag evs
... | k , n , f , w′ =
  if t ≡ᵇ tag
  then (1 + k , (if c then 1 + n else n) , (if ok then f else 1 + f) , (if ok then w′ else w))
  else (k , n , f , w′)

tags : List ℕ
tags = carryᵗ ∷ lanesᵗ ∷ subscribeᵗ ∷ skippedᵗ ∷ dyingᵗ ∷ controlᵗ ∷ finishᵗ ∷ cutᵗ ∷ wrapᵗ ∷ walkᵗ ∷ []

-- every tag's tally on one case's impl run
walkSides : ∀ {n} {Γ : Ctx n} {κ : Kinds n} {t} → Fuel → SExp Γ [] [] [] t → SimulSlots Γ κ → List (ℕ × Tally)
walkSides {κ = κ} f e ins with evaluate! f (elaborateImpl κ e) (embedSlotsImpl ins)
... | d = mapT (Decide.wEval (Σ⁰.snd⁰ d))
  where
  mapT : List Ev → List (ℕ × Tally)
  mapT evs = go tags
    where
    go : List ℕ → List (ℕ × Tally)
    go []       = []
    go (g ∷ gs) = (g , tallyOf g evs) ∷ go gs
