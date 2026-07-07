-- The shared vocabulary of the two proof halves: the referee's grouped
-- view of a run (`groupsOf`), the positional clock (`stamped`), and the
-- validity domain (`Canonical`). Everything here is DEFINED; both
-- Counting-Recovers and Trace-Faithful import it, and Main-Theorem
-- composes them.
module Formal-Verification.Bridge where

open import Prelude
open import Shared-Types
open import Spec.MonotonicList
open import Implementation.Naive-Rx
open import Implementation.Batch-Simultaneous

------------------------------------------------------------------------
-- the referee's grouped view of a run.
--
-- The machine's own experience is the flattened output stream (`run`
-- concatenates it away); the referee keeps the responses grouped BY
-- INPUT — and since flatten places input j at tick j (frame = 0, async
-- k = k+1, endSlot i = K+1+i), stamping is just: group j's values get
-- time (j , 0).

groupsGo : {I O : Set} (m : Machine I O) → State m → List I → List (List O)
groupsGo m s []       = []
groupsGo m s (i ∷ is) = snd (step m s i) ∷ groupsGo m (fst (step m s i)) is

groupsOf : {I O : Set} → Machine I O → List I → List (List O)
groupsOf m = groupsGo m (start m)

concatL : {A : Set} → List (List A) → List A
concatL = concatMap (λ g → g)

-- PROVEN: flattening the referee's grouped view is exactly the
-- machine's own flattened experience — the grouping is knowledge the
-- referee ADDS, never information the machine had
feed-groups : {I O : Set} (m : Machine I O) (s : State m) (is : List I)
            → snd (feed m s is) ≡ concatL (groupsGo m s is)
feed-groups m s []       = refl
feed-groups m s (i ∷ is) =
  cong (λ ys → snd (step m s i) ++ ys) (feed-groups m (fst (step m s i)) is)

run-groups : {I O : Set} (m : Machine I O) (is : List I)
           → run m is ≡ concatL (groupsOf m is)
run-groups m = feed-groups m (start m)

-- the referee's clock, re-attached: group j's values at time (j , 0)
stampFrom : ℕ → List (List (Emit Val)) → List (Time × Val)
stampFrom k []       = []
stampFrom k (g ∷ gs) =
  map (λ v → (k , 0) , v) (concatMap (λ e → values (snd e)) g)
    ++ stampFrom (suc k) gs

-- the implementation's protocol trace, stamped — fully DEFINED
stamped : {n : ℕ} → Emissions n → Exp n → List (Time × Val)
stamped em e = stampFrom 0 (groupsOf (compile e) (flatten em))

------------------------------------------------------------------------
-- the validity domain: REGISTRATION-CANONICAL trees (the previous generation's
-- fence). Share semantics themselves are untouched — this is a
-- syntactic discipline: per letShareE binder, the slot's pre-order-
-- FIRST ref is its connecting ref (flagged true, exactly rxjs's "first
-- subscriber triggers connect") and every later ref is flagged false.
-- The relation threads "is the connecting ref still owed" per slot
-- through the tree in registration (pre-order) order; a spawn arm
-- written left of its slot's connecting static arm fails, matching
-- the previous generation's ranked-delivery derivation. mapS templates are quantified over
-- their trigger value and may not change the state (a spawned ref can
-- never connect).

lookupB : List Bool → ℕ → Bool
lookupB []       _       = false
lookupB (b ∷ bs) zero    = b
lookupB (b ∷ bs) (suc i) = lookupB bs i

clearB : List Bool → ℕ → List Bool
clearB []       _       = []
clearB (b ∷ bs) zero    = false ∷ bs
clearB (b ∷ bs) (suc i) = b ∷ clearB bs i

data CanE {n : ℕ} : List Bool → Exp n → List Bool → Set
data CanS {n : ℕ} : List Bool → ExpS n → List Bool → Set
data CanL {n : ℕ} : List Bool → List (Exp n) → List Bool → Set

data CanE {n} where
  can-src   : {w : List Bool} {i : Fin n} → CanE w (srcE i) w
  can-empty : {w : List Bool} → CanE w emptyE w
  can-of    : {w : List Bool} {vs : List Val} → CanE w (ofE vs) w
  -- a ref's flag must be exactly what its slot is owed: the first
  -- (pre-order) ref connects and consumes the debt, later refs are late
  can-ref   : {w : List Bool} {i : ℕ} → ltℕ i (length w) ≡ true
            → CanE w (shareE (lookupB w i) i) (clearB w i)
  can-let   : {w w₁ w₂ : List Bool} {b₀ : Bool} {s b : Exp n}
            → CanE w s w₁ → CanE (true ∷ w₁) b (b₀ ∷ w₂)
            → CanE w (letShareE s b) w₂
  can-map   : {w w′ : List Bool} {f : Val → Val} {e : Exp n}
            → CanE w e w′ → CanE w (mapE f e) w′
  can-take  : {w w′ : List Bool} {k : ℕ} {e : Exp n}
            → CanE w e w′ → CanE w (takeE k e) w′
  can-scan  : {w w′ : List Bool} {f : Val → Val → Val} {z : Val} {e : Exp n}
            → CanE w e w′ → CanE w (scanE f z e) w′
  can-mergeAll   : {w w′ : List Bool} {ss : ExpS n}
                 → CanS w ss w′ → CanE w (mergeAllE ss) w′
  can-concatAll  : {w w′ : List Bool} {ss : ExpS n}
                 → CanS w ss w′ → CanE w (concatAllE ss) w′
  can-switchAll  : {w w′ : List Bool} {ss : ExpS n}
                 → CanS w ss w′ → CanE w (switchAllE ss) w′
  can-exhaustAll : {w w′ : List Bool} {ss : ExpS n}
                 → CanS w ss w′ → CanE w (exhaustAllE ss) w′

data CanS {n} where
  can-ofS  : {w w′ : List Bool} {es : List (Exp n)}
           → CanL w es w′ → CanS w (ofS es) w′
  can-mapS : {w w′ : List Bool} {f : Val → Exp n} {e : Exp n}
           → CanE w e w′
           → ((v : Val) → CanE w′ (f v) w′)
           → CanS w (mapS f e) w′

data CanL {n} where
  canl-[] : {w : List Bool} → CanL w [] w
  canl-∷  : {w w₁ w₂ : List Bool} {e : Exp n} {es : List (Exp n)}
          → CanE w e w₁ → CanL w₁ es w₂ → CanL w (e ∷ es) w₂

Canonical : {n : ℕ} → Exp n → Set
Canonical e = CanE [] e []
