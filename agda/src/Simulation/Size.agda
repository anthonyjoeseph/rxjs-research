------------------------------------------------------------------
-- THE PLAIN DERIVATION'S SIZE: one per constructor, plus its
-- sub-derivations.  The walk descends it, not the author's tree: an
-- inner the walk reaches through an `of`'s fold is a value the fold
-- carried, of no size the tree can see, but its subscribe is a premise
-- of the fold's, so strictly smaller here.
------------------------------------------------------------------
module Simulation.Size where

open import Data.Nat using (ℕ; suc; _+_; _<_; s≤s)
open import Data.Nat.Properties using (<-trans; m≤m+n; m≤n+m; n<1+n)
open import Rx.Evaluator.Domain using (dispatchShare⇓; foldPath⇓; innerFinish⇓; innerReact⇓; mergeAllDrain⇓; shareGo⇓; shareWalk⇓; sharedConnect⇓; stepFrame⇓; subscribeAll⇓; subscribeE⇓; subscribeInner⇓; subscribeSharedSlot⇓; thruConsume⇓; thruWalk⇓;
  connect; consume-all-enqueue; consume-all-nil; consume-all-sub; consume-exhaust-nil; consume-exhaust-sub; consume-switch-nil; consume-switch-sub; disp; drain-nil; drain-no-room; drain-room; drain-spent; finish-all-drain; finish-exhaust-clear; finish-nil; finish-switch-clear; fold-root; fold-sink; fold-step; go-cut; go-live; go-nil; inner; react-alive; react-dead; react-false; slot-connect; slot-join; slot-spent; step-batchSync; step-from-inner; step-map; step-scan; step-take; step-thru-outer; sub-all; subs-batchSync; subs-cold-async; subs-cold-sync; subs-defer; subs-empty; subs-flatten; subs-floor; subs-hot-done; subs-hot-live; subs-map; subs-mint; subs-of; subs-scan; subs-shared; subs-takeWhile; subs-μ; walk-cons; walk-echo; walk-end; walk-more; walk-nil)

mutual
  sz-subscribeE : ∀ {n Γ t e u lo x1 x2 x3 x4 x5 x6} → subscribeE⇓ {n} {Γ} {t} {e} {u} {lo} x1 x2 x3 x4 x5 x6 → ℕ
  sz-subscribeE (subs-floor _ d1) = suc (sz-foldPath d1)
  sz-subscribeE (subs-shared _ d1) = suc (sz-subscribeSharedSlot d1)
  sz-subscribeE (subs-hot-done _ _ _ d1) = suc (sz-foldPath d1)
  sz-subscribeE (subs-hot-live _ _ _ _) = suc 0
  sz-subscribeE (subs-cold-sync _ _ d1) = suc (sz-foldPath d1)
  sz-subscribeE (subs-cold-async _ _ _ _ _ d1) = suc (sz-foldPath d1)
  sz-subscribeE (subs-of d1) = suc (sz-foldPath d1)
  sz-subscribeE (subs-empty d1) = suc (sz-foldPath d1)
  sz-subscribeE (subs-takeWhile _ d1) = suc (sz-subscribeE d1)
  sz-subscribeE (subs-batchSync _ d1 d2) = suc (sz-subscribeE d1 + sz-foldPath d2)
  sz-subscribeE (subs-map d1) = suc (sz-subscribeE d1)
  sz-subscribeE (subs-scan _ d1) = suc (sz-subscribeE d1)
  sz-subscribeE (subs-flatten d1) = suc (sz-subscribeAll d1)
  sz-subscribeE (subs-μ d1) = suc (sz-subscribeE d1)
  sz-subscribeE (subs-defer _ _ _ _) = suc 0
  sz-subscribeE (subs-mint _ d1) = suc (sz-subscribeE d1)

  sz-subscribeInner : ∀ {n Γ t e u lo x1 x2 x3 x4 x5 x6 x7 x8} → subscribeInner⇓ {n} {Γ} {t} {e} {u} {lo} x1 x2 x3 x4 x5 x6 x7 x8 → ℕ
  sz-subscribeInner (inner _ d1) = suc (sz-subscribeE d1)

  sz-thruConsume : ∀ {n Γ t e u lo x1 x2 x3 x4 x5 x6 x7 x8} → thruConsume⇓ {n} {Γ} {t} {e} {u} {lo} x1 x2 x3 x4 x5 x6 x7 x8 → ℕ
  sz-thruConsume (consume-all-sub _ _ d1) = suc (sz-subscribeInner d1)
  sz-thruConsume (consume-all-enqueue _ _) = suc 0
  sz-thruConsume (consume-all-nil _) = suc 0
  sz-thruConsume (consume-switch-sub _ _ _ d1) = suc (sz-subscribeInner d1)
  sz-thruConsume (consume-switch-nil _) = suc 0
  sz-thruConsume (consume-exhaust-sub _ d1) = suc (sz-subscribeInner d1)
  sz-thruConsume (consume-exhaust-nil _) = suc 0

  sz-thruWalk : ∀ {n Γ t e u lo x1 x2 x3 x4 x5 x6 x7 x8} → thruWalk⇓ {n} {Γ} {t} {e} {u} {lo} x1 x2 x3 x4 x5 x6 x7 x8 → ℕ
  sz-thruWalk walk-nil = suc 0
  sz-thruWalk (walk-echo d1 d2) = suc (sz-foldPath d1 + sz-thruWalk d2)
  sz-thruWalk (walk-cons d1 d2) = suc (sz-thruConsume d1 + sz-thruWalk d2)

  sz-mergeAllDrain : ∀ {n Γ t e s lo x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11} → mergeAllDrain⇓ {n} {Γ} {t} {e} {s} {lo} x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 → ℕ
  sz-mergeAllDrain drain-spent = suc 0
  sz-mergeAllDrain drain-nil = suc 0
  sz-mergeAllDrain (drain-no-room _) = suc 0
  sz-mergeAllDrain (drain-room _ d1 _ d2) = suc (sz-subscribeInner d1 + sz-mergeAllDrain d2)

  sz-innerFinish : ∀ {n Γ t e s lo x1 x2 x3 x4 x5 x6 x7 x8 x9 x10} → innerFinish⇓ {n} {Γ} {t} {e} {s} {lo} x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 → ℕ
  sz-innerFinish (finish-all-drain d1 d2) = suc (sz-foldPath d1 + sz-mergeAllDrain d2)
  sz-innerFinish (finish-switch-clear _) = suc 0
  sz-innerFinish finish-exhaust-clear = suc 0
  sz-innerFinish (finish-nil _) = suc 0

  sz-innerReact : ∀ {n Γ t e s lo x1 x2 x3 x4 x5 x6 x7 x8 x9 x10} → innerReact⇓ {n} {Γ} {t} {e} {s} {lo} x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 → ℕ
  sz-innerReact react-false = suc 0
  sz-innerReact (react-alive _) = suc 0
  sz-innerReact (react-dead _ d1) = suc (sz-innerFinish d1)

  sz-stepFrame : ∀ {n Γ t e s u lo x1 x2 x3 x4 x5 x6 x7 x8} → stepFrame⇓ {n} {Γ} {t} {e} {s} {u} {lo} x1 x2 x3 x4 x5 x6 x7 x8 → ℕ
  sz-stepFrame step-map = suc 0
  sz-stepFrame step-scan = suc 0
  sz-stepFrame step-take = suc 0
  sz-stepFrame step-batchSync = suc 0
  sz-stepFrame (step-from-inner d1) = suc (sz-innerReact d1)
  sz-stepFrame (step-thru-outer d1) = suc (sz-thruWalk d1)

  sz-subscribeAll : ∀ {n Γ t e u lo x1 x2 x3 x4 x5 x6 x7 x8} → subscribeAll⇓ {n} {Γ} {t} {e} {u} {lo} x1 x2 x3 x4 x5 x6 x7 x8 → ℕ
  sz-subscribeAll (sub-all _ d1) = suc (sz-subscribeE d1)

  sz-sharedConnect : ∀ {n Γ t e lo i x1 x2 x3 x4 x5 x6 x7} → sharedConnect⇓ {n} {Γ} {t} {e} {lo} i x1 x2 x3 x4 x5 x6 x7 → ℕ
  sz-sharedConnect (connect _ d1) = suc (sz-subscribeE d1)

  sz-subscribeSharedSlot : ∀ {n Γ t e lo i x1 x2 x3 x4 x5 x6 x7} → subscribeSharedSlot⇓ {n} {Γ} {t} {e} {lo} i x1 x2 x3 x4 x5 x6 x7 → ℕ
  sz-subscribeSharedSlot (slot-spent _ d1) = suc (sz-foldPath d1)
  sz-subscribeSharedSlot (slot-join _ _ _) = suc 0
  sz-subscribeSharedSlot (slot-connect _ _ d1) = suc (sz-sharedConnect d1)

  sz-dispatchShare : ∀ {n Γ t e lo x1 i x2 x3 x4 x5 x6 x7} → dispatchShare⇓ {n} {Γ} {t} {e} {lo} x1 i x2 x3 x4 x5 x6 x7 → ℕ
  sz-dispatchShare (disp d1) = suc (sz-shareWalk d1)

  sz-shareWalk : ∀ {n Γ t e x1 i x2 x3 x4 x5 x6} → shareWalk⇓ {n} {Γ} {t} {e} x1 i x2 x3 x4 x5 x6 → ℕ
  sz-shareWalk walk-nil = suc 0
  sz-shareWalk (walk-end d1) = suc (sz-shareGo d1)
  sz-shareWalk (walk-more d1 d2) = suc (sz-shareGo d1 + sz-shareWalk d2)

  sz-shareGo : ∀ {n Γ t e lo x1 i x2 x3 x4 x5 x6 x7} → shareGo⇓ {n} {Γ} {t} {e} {lo} x1 i x2 x3 x4 x5 x6 x7 → ℕ
  sz-shareGo go-nil = suc 0
  sz-shareGo (go-cut _ d1) = suc (sz-shareGo d1)
  sz-shareGo (go-live _ d1 d2) = suc (sz-foldPath d1 + sz-shareGo d2)

  sz-foldPath : ∀ {n Γ t e u lo x1 x2 x3 x4 x5 x6 x7} → foldPath⇓ {n} {Γ} {t} {e} {u} {lo} x1 x2 x3 x4 x5 x6 x7 → ℕ
  sz-foldPath fold-root = suc 0
  sz-foldPath (fold-sink d1) = suc (sz-dispatchShare d1)
  sz-foldPath (fold-step d1 d2) = suc (sz-stepFrame d1 + sz-foldPath d2)

-- A PREMISE IS BELOW ANY BOUND ITS CONCLUSION IS BELOW
sz-l : ∀ {a b N} → suc (a + b) < N → a < N
sz-l {a} {b} h = <-trans (s≤s (m≤m+n a b)) h

sz-r : ∀ {a b N} → suc (a + b) < N → b < N
sz-r {a} {b} h = <-trans (s≤s (m≤n+m b a)) h

sz-1 : ∀ {a N} → suc a < N → a < N
sz-1 {a} h = <-trans (n<1+n a) h
