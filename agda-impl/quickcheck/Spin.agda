{-# OPTIONS --guardedness #-}

-- PROGRESS, AGAINST SPINS.  Adequacy's liveness half, `reached`, says the run passes
-- every position the root's meaning shows, the two sides ending, falling
-- quiet or spinning at the same point.  `quickcheck.Placing` cannot see a
-- spin on one side only: running out of fuel reads as a pass.  This can:
-- each side's first `n` events, each found within a fixed budget of
-- silent steps after the last, are the same events at the same
-- positions.  A side spinning where the other shows an event runs out
-- of budget there; both spinning, both run out together.  The budget is
-- per event because a program emitting forever costs the machine more
-- steps per value the deeper its recursion, and the meaning fewer.  The programs spin on
-- purpose, through `defer` with no `μ` budget: a source spinning beside
-- its body's later events, a lane spinning on subscribe, a switch onto a
-- spinning lane, a `takeWhile` cutting a spinning source.
module quickcheck.Spin where

open import Data.Bool using (Bool; true; false; _∧_; not)
open import Data.List using (List; []; _∷_; _++_) renaming (map to mapL)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing; just)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
import Data.String as S
open import Data.Nat.Show using () renaming (show to showℕ)
open import Relation.Binary.PropositionalEquality using (refl)

open import Tree using (Obs; Later; of; map; takeWhile; flatMap; connect; connected; defer; merge; ones; mergeᶠ; switchᶠ; exhaustᶠ)
import Tree as T
open import denotation.MonotonicList.Events using (Events; Events∞; out; skip; end; hush; Pos; Label; ix; sub; last; _<ᵖ_; root; Timeline)
open import denotation.MonotonicList using (observe)
open import denotation.Unfold using (⟦_⟧ˢ; [])
open import operation.StateTree.Pure using (module Driver)
open import quickcheck.Code using (script; timeline; module Leaf)

open Driver ℕ using (Trace; Trace∞; tau; out; end; idle; trace; begin)

-- A position, printed.
mutual
  showL : Label → String
  showL (ix n)  = showℕ n
  showL (sub p) = "s(" S.++ showP p S.++ ")"
  showL last    = "L"

  showP : Pos → String
  showP []       = ""
  showP (l ∷ []) = showL l
  showP (l ∷ ls) = showL l S.++ "." S.++ showP ls

-- What a side shows, silent steps dropped.
data Ev : Set where
  val  : Pos → ℕ → Ev
  fin  : Pos → Ev
  done : Ev

private
  budget : ℕ
  budget = 3000

  -- `n` events, `k` silent steps left before the next.
  run : ℕ → ℕ → Trace → List Ev
  run zero    _       _             = []
  run (suc n) zero    _             = []
  run (suc n) (suc k) (tau _ l)     = run (suc n) k (Trace∞.force l)
  run (suc n) (suc k) (out _ p a l) = val p a ∷ run n budget (Trace∞.force l)
  run (suc n) (suc k) (end p)       = fin p ∷ []
  run (suc n) (suc k) idle          = done ∷ []

  meant : ℕ → ℕ → Events ℕ → List Ev
  meant zero    _       _           = []
  meant (suc n) zero    _           = []
  meant (suc n) (suc k) (skip _ r)  = meant (suc n) k (Events∞.force r)
  meant (suc n) (suc k) (out p a r) = val p a ∷ meant n budget (Events∞.force r)
  meant (suc n) (suc k) (end p)     = fin p ∷ []
  meant (suc n) (suc k) hush        = done ∷ []

  samePos : Pos → Pos → Bool
  samePos p q = not (p <ᵖ q) ∧ not (q <ᵖ p)

  same : Ev → Ev → Bool
  same (val p a) (val q b) = samePos p q ∧ (a ≡ᵇ b)
  same (fin p)   (fin q)   = samePos p q
  same done      done      = true
  same _         _         = false

  sameAll : List Ev → List Ev → Bool
  sameAll []       []       = true
  sameAll (x ∷ xs) (y ∷ ys) = same x y ∧ sameAll xs ys
  sameAll _        _        = false

-- Each side's first `n` events, the same.
progress : ℕ → Obs Timeline [] ℕ → Bool
progress n o = sameAll (run n budget (trace (begin o))) (meant n budget (observe (⟦ o ⟧ˢ []) root))

-- Each side's first `n` events.
progressWhy : ℕ → Obs Timeline [] ℕ → List String
progressWhy n o = "machine:" ∷ shows (run n budget (trace (begin o)))
               ++ "meaning:" ∷ shows (meant n budget (observe (⟦ o ⟧ˢ []) root))
  where
        showE : Ev → String
        showE (val p a) = "  " S.++ showℕ a S.++ " @" S.++ showP p
        showE (fin p)   = "  end @" S.++ showP p
        showE done      = "  quiet"
        shows : List Ev → List String
        shows = mapL showE

private
  -- Subscribing it subscribes it again, forever: rxjs's stack overflow.
  spin : ∀ {Γ} → Obs Timeline Γ ℕ
  spin = defer λ where .Later.force → spin

  at : ∀ {Γ} → ℕ → ℕ → Obs Timeline Γ ℕ
  at t v = T.cold (Leaf.scripted timeline (script ((t , v ∷ []) ∷ []) true false))

  spinAt1 : ∀ {Γ} → ℕ → Obs Timeline Γ ℕ
  spinAt1 1 = spin
  spinAt1 n = of (n ∷ [])

  onesAt1 : ∀ {Γ} → ℕ → Obs Timeline Γ ℕ
  onesAt1 1 = ones
  onesAt1 n = of (n ∷ [])

cases : List (String × Obs Timeline [] ℕ)
cases =
    ("a connect whose source spins, its body due later"
    , connect spin (at 1 5))
  ∷ ("a connect whose source emits forever unjoined, its body due later"
    , connect ones (at 1 5))
  ∷ ("a connect whose source emits forever, joined and cut"
    , connect ones (takeWhile true (λ _ → false) (connected (here refl))))
  ∷ ("a lane spinning on subscribe, a sibling due later"
    , merge (at 2 7) (flatMap (mergeᶠ nothing) (λ _ → spin) (at 1 1)))
  ∷ ("a lane spinning on subscribe, a sibling subscribed after it"
    , merge (flatMap (mergeᶠ nothing) (λ _ → spin) (at 1 1)) (at 2 7))
  ∷ ("a switch onto a lane spinning on subscribe, the outer's next inline"
    , flatMap switchᶠ spinAt1 (of (1 ∷ 2 ∷ [])))
  ∷ ("a switch onto a lane emitting forever, the outer's next inline"
    , flatMap switchᶠ onesAt1 (of (1 ∷ 2 ∷ [])))
  ∷ ("an exhaust onto a lane spinning on subscribe"
    , flatMap exhaustᶠ spinAt1 (of (1 ∷ 2 ∷ [])))
  ∷ ("a concat whose first lane spins"
    , flatMap (mergeᶠ (just 1)) spinAt1 (of (1 ∷ 2 ∷ [])))
  ∷ ("a merge whose second lane spins, the third queued inline"
    , flatMap (mergeᶠ nothing) spinAt1 (of (0 ∷ 1 ∷ 2 ∷ [])))
  ∷ ("a takeWhile cutting a source emitting forever"
    , takeWhile true (λ _ → false) ones)
  ∷ ("a takeWhile over a spinning source"
    , takeWhile true (λ _ → false) spin)
  ∷ ("a source emitting forever beside a later timer"
    , merge ones (at 1 5))
  ∷ ("a map over a spin inside a connect's joiner lane"
    , connect (at 1 3) (flatMap (mergeᶠ nothing) (λ _ → map (λ x → x) spin) (connected (here refl))))
  ∷ []
