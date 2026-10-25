{-# OPTIONS --guardedness #-}

-- THE KEPT DEPTH, TESTED: every silent step of the engine drops leading
-- skips of what its configuration means (`adequacy.Engine.Meaning.M`), or
-- means the same, event for event, skips and positions included
-- (`adequacy.Content.silent-exact`), with less work left
-- (`adequacy.Engine.Spent.Spending.silent-spent`), and never the same
-- when the step is one whose work may grow (`adequacy.Content`'s drops).
-- Also the longest run of silent steps meaning the same, and that no
-- configuration puts a live connect's body just past its source
-- (`adequacy.Engine.Pick.Untied`).
module quickcheck.KeptDepth where

open import Data.Bool using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.List using (List; []; _∷_; upTo) renaming (map to mapL; _++_ to _++L_)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _<ᵇ_; _≡ᵇ_)
open import Data.Product using (_×_; _,_)
open import Data.Maybe using (just; nothing)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.String using (String; _++_)

open import denotation.MonotonicList.Events using (Events; Events∞; out; skip; end; hush)
open import Tree using (defer; mergeᶠ)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (refl)
open import quickcheck.Tm using (nat; bool; var)
open import quickcheck.Code using (Code; Prog; of; takeWhile; flatMap; connect; connected) renaming (defer to deferᶜ)
open import denotation.MonotonicList.Events using (stall; close)
open import operation.PureObservable using (play; module Driver; module Machine)
open import adequacy.Engine.Meaning using (M)
open import quickcheck.Code using (toObs; timeline; showCode)
open import quickcheck.Ty using (natᵗ)
open import quickcheck.Quickcheck using (program)
open import quickcheck.Stepping using (exactᵇ)
open import adequacy.Ghost using (module Ghosting)
open import quickcheck.Spin using (showP)

open Driver ℕ using (Step; step; silent; value; complete; drained)
open Ghosting ℕ using (work; Measure)
open Machine using (Conf; ⟨_,_,_,_⟩; load; spot; subscribing; absorbed; rising; nx; cp; pend; coldS; top; inOuter; inLanes;
  plug; closed; alive; search; found; leafM; St; Ctx; Out; mapS; scanS; cutS; lnS; takeS; flatS; connS; inMap; inScan; inCut; inLn;
  inTake; inSrc; inBody; over; shift)
open import Data.Maybe using (Maybe)
open import operation.Key using (Key; _<ᴷ_)
open import Tree using (Obs; FlatOp)
open import denotation.MonotonicList.Events using (Timeline)
open import adequacy.Engine.Head using (cand)

private
  -- A run's verdict, carrying its longest run of steps meaning the same.
  data Verdict : Set where
    yes : ℕ → Verdict
    no  : ℕ → String → Verdict

  -- The first `k` events of a run, printed.
  showE : ℕ → Events ℕ → String
  showE zero    _           = "…"
  showE (suc k) (out p a r) = "o(" ++ showP p ++ "," ++ showℕ a ++ ") " ++ showE k (Events∞.force r)
  showE (suc k) (skip p r)  = "k(" ++ showP p ++ ") " ++ showE k (Events∞.force r)
  showE (suc k) (end p)     = "e(" ++ showP p ++ ")"
  showE (suc k) hush        = "h"

  showMode : Conf ℕ → String
  showMode m with Conf.mode m
  ... | subscribing = "subscribing"
  ... | absorbed    = "absorbed"
  ... | rising _    = "rising"

  showSpot : List ℕ → String
  showSpot []      = ""
  showSpot (i ∷ π) = showℕ i ++ "." ++ showSpot π

  -- `work`'s order, decided.
  lowerᵇ : Measure → Measure → Bool
  lowerᵇ ((a , b , c , d , e) , f) ((a′ , b′ , c′ , d′ , e′) , f′) =
    lex₆ a a′ (lex₆ b b′ (lex₆ c c′ (lex₆ d d′ (lex₆ e e′ (f <ᵇ f′)))))
    where lex₆ : ℕ → ℕ → Bool → Bool
          lex₆ x y r = (x <ᵇ y) ∨ ((x ≡ᵇ y) ∧ r)

  showW : Measure → String
  showW ((a , b , c , d , e) , f) = showℕ a ++ "," ++ showℕ b ++ "," ++ showℕ c ++ "," ++ showℕ d ++ "," ++ showℕ e ++ ";" ++ showℕ f

  -- The steps whose work may grow (`adequacy.Engine.Spent.Spending.Skipped`).
  skippedᵇ : Conf ℕ → Bool
  skippedᵇ ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩         = true
  skippedᵇ ⟨ inLanes op f d n (a ∷ q) o pre post c , s , rising cp , p ⟩ = alive s
  skippedᵇ ⟨ c , pend (defer l) , subscribing , p ⟩                     = true
  skippedᵇ ⟨ c , s , absorbed , p ⟩ with search top (plug c s)
  ... | just (found (Γ′ , A′ , c′ , coldS true (play τ u i t (stall k))) leafM key) = not (closed c′)
  ... | just (found (Γ′ , A′ , c′ , coldS true (play τ u i t (close k))) leafM key) = not (closed c′)
  ... | _ = false
  skippedᵇ _ = false

  -- `adequacy.Engine.Pick.Untied`, decided: keys order totally, so alike
  -- is neither before the other.
  untieᵇ : ∀ {A B} → Maybe (Key × Out A) → Maybe (Key × Out B) → Bool
  untieᵇ (just (h , _)) (just (k , _)) = (shift h <ᴷ k) ∨ (k <ᴷ shift h)
  untieᵇ _              _              = true

  mutual
    untiedᵇ : ∀ {R Γ A} → Ctx R Γ A → St Γ A → Bool
    untiedᵇ c (mapS f s)              = untiedᵇ (inMap f c) s
    untiedᵇ c (scanS f z s)           = untiedᵇ (inScan f z c) s
    untiedᵇ c (cutS l a s)            = untiedᵇ (inCut l a c) s
    untiedᵇ c (lnS b s)               = untiedᵇ (inLn b c) s
    untiedᵇ c (takeS i q w s)         = untiedᵇ (inTake i q w c) s
    untiedᵇ c (flatS op f d n q o ls) = untiedᵇ (inOuter op f d n q ls c) o ∧ untiedsᵇ c op f d n q o [] ls
    untiedᵇ c (connS k o b)           =
      (over k ∨ untieᵇ (cand (inSrc k b c) o) (cand (inBody k o c) b)) ∧ untiedᵇ (inSrc k b c) o ∧ untiedᵇ (inBody k o c) b
    untiedᵇ c _                       = true

    untiedsᵇ : ∀ {R Γ A B} → Ctx R Γ B → FlatOp → (A → Obs Timeline Γ B) → Bool → ℕ → List A → St Γ A
             → List (St Γ B) → List (St Γ B) → Bool
    untiedsᵇ c op f d n q o pre []         = true
    untiedsᵇ c op f d n q o pre (s ∷ post) = untiedᵇ (inLanes op f d n q o pre post c) s ∧ untiedsᵇ c op f d n q o (s ∷ pre) post

  -- What a silent step neither dropping nor keeping its meaning did.
  why : Conf ℕ → Conf ℕ → String
  why m m′ = "\n  from " ++ showMode m ++ " at " ++ showSpot (spot m) ++ " to " ++ showMode m′ ++ " at " ++ showSpot (spot m′)
             ++ (if skippedᵇ m then " (skipped)" else "") ++ "\n  work " ++ showW (work m) ++ " to " ++ showW (work m′)
             ++ "\n  before " ++ showE 10 (M m) ++ "\n  after  " ++ showE 10 (M m′)

  depth : ℕ
  depth = 60

  -- Whether `e′` is `e` past one or more of its first `k` leading skips.
  dropped : ℕ → Events ℕ → Events ℕ → Bool
  dropped zero    e          e′ = false
  dropped (suc k) (skip p r) e′ = exactᵇ depth (Events∞.force r) e′ ∨ dropped k (Events∞.force r) e′
  dropped (suc k) _          e′ = false

  -- A silent step from `m` to `m′`: 2 dropped leading skips, 1 meant the
  -- same with less work left and not skipped, 0 neither.
  kind : Conf ℕ → Conf ℕ → ℕ
  kind m m′ = if exactᵇ depth (M m) (M m′) then (if lowerᵇ (work m′) (work m) ∧ not (skippedᵇ m) then 1 else 0)
              else (if dropped 64 (M m) (M m′) then 2 else 0)

  -- Whether every silent step keeps its meaning so, and the longest run
  -- meaning the same.
  mutual
    walk : ℕ → ℕ → ℕ → Conf ℕ → Verdict
    walk zero    run best m = yes (best ⊔ run)
    walk (suc n) run best m = if untiedᵇ top (plug (Conf.ctx m) (Conf.foc m)) then next n run best m (step m)
                              else no (best ⊔ run) ("\n  tied: a connect's body due just past its source, " ++ showMode m ++ " at " ++ showSpot (spot m))

    next : ℕ → ℕ → ℕ → Conf ℕ → Step → Verdict
    next n run best m (silent t m′)     = after n run best m m′ (kind m m′)
    next n run best m (value t p a m′)  = walk n 0 (best ⊔ run) m′
    next n run best m (complete p)      = yes (best ⊔ run)
    next n run best m drained           = yes (best ⊔ run)

    after : ℕ → ℕ → ℕ → Conf ℕ → Conf ℕ → ℕ → Verdict
    after n run best m m′ zero          = no (best ⊔ run) (why m m′)
    after n run best m m′ (suc zero)    = walk n (suc run) best m′
    after n run best m m′ (suc (suc _)) = walk n 0 (best ⊔ run) m′

-- One program's verdict, under a label.
keptLine : String → Prog natᵗ → String
keptLine n p with walk 400 0 0 (load (toObs timeline 3 p []ᴬ []ᴬ []ᴬ))
... | yes l = "kept-depth: ok   " ++ n ++ " longest " ++ showℕ l
... | no l w = "kept-depth: FAIL " ++ n ++ " longest " ++ showℕ l ++ "\n  program " ++ showCode natᵗ p ++ w

private
  -- A connect whose body's first value ends the takeWhile above it while
  -- the connect is still being subscribed, so its source is begun under
  -- a closed cut; a lane of a merge, so the run goes on past it.
  closedSrc : ∀ {Γ Δᵍ Δ Θ} → Bool → Code Γ Δᵍ Δ Θ natᵗ → Code Γ Δᵍ Δ Θ natᵗ
  closedSrc i s = takeWhile i (bool false) (connect s (of (nat 0 ∷ nat 1 ∷ [])))

  inLane : Code [] [] [] (natᵗ ∷ []) natᵗ → Prog natᵗ
  inLane l = flatMap (mergeᶠ nothing) l (of (nat 0 ∷ nat 1 ∷ []))

  -- Steps drawn programs rarely take: a step begun under a closed cut.
  hands : List (String × Prog natᵗ)
  hands =
      ("a deferred source begun under a closed cut" , inLane (closedSrc false (deferᶜ (of (nat 5 ∷ [])))))
    ∷ ("a deferred source begun under a closed cut, inclusive" , inLane (closedSrc true (deferᶜ (of (nat 5 ∷ [])))))
    ∷ ("a deferred connect begun under a closed cut"
      , inLane (closedSrc false (deferᶜ (connect (of (nat 5 ∷ [])) (connected (here refl))))))
    ∷ ("a deferred merge begun under a closed cut"
      , inLane (closedSrc false (deferᶜ (flatMap (mergeᶠ nothing) (deferᶜ (of (var (here refl) ∷ []))) (of (nat 5 ∷ nat 6 ∷ []))))))
    ∷ []

-- The verdicts on seeds from f, then on the hand programs.
keptLines : ℕ → ℕ → List String
keptLines f c = mapL (λ s → keptLine ("seed " ++ showℕ (f + s)) (program (f + s))) (upTo c) ++L mapL (λ (n , p) → keptLine n p) hands
