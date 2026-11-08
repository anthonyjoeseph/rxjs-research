{-# OPTIONS --guardedness #-}

-- A FLATMAP'S SCAN HOLDS WHAT ITS SOURCE PROMISES.  The scan steps
-- `react` over each row its source meets and lays the step's outputs
-- under that row, the `j`-th at `q ++ ix 1 ∷ ix j ∷ []`; past the
-- source's end it ends at the same position.  So what the scanned
-- stream holds is read off its source's rows alone: what a begin is
-- named, what precedes an over, and, run by run, the counts of the
-- outputs laid out (`CombIn`).
module simultaneous.HeldComb where

open import Data.Bool using (false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Data.Unit using (⊤)
open import denotation.Read using (Run; _∷_; Visible)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; FlatOp; scan)
open import denotation.Events using (Pos; Timeline; root; fresh; _≟ᵖ_; ix)
open import denotation.EmissionSet using (EmissionSet; Ev; out; end; skip; pin; Den; enter; DenEnv; ⟦_⟧; approx)
open import denotation.Laws.Worlds using (Ok; Hots; GoodEnv; _⊑_)
open import simultaneous.InstEmit using (instEmit; value; mark; begin; stop; over)
open import simultaneous.SObs using (Flat; flat; module Elaborate)
open import simultaneous.Relations using (Met; values)
open import simultaneous.Shut using (r₀)
open import simultaneous.FlatSim using (Inv)
open import simultaneous.Routed using (Carried; c-end)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Routed using (Held; Carried; cnt; Ex; nameOf; Early; Valued; opos; Routing; Idle)

open Elaborate {C = Timeline} _≟ᵖ_ root fresh using (IE; Routes; count; Out; Input; react; each)

------------------------------------------------------------------------
-- What the scan lays out

-- The meaning, or its n-th approximant.
ev : Maybe ℕ → ∀ {Γ A} → Obs Timeline Γ A → DenEnv Γ → Den A
ev nothing  o ρ = ⟦ o ⟧ ρ
ev (just n) o ρ = approx n o ρ

-- The scan's first state: nothing counted, no output.
init : ∀ {B} → Out B
init = flat root 0 0 false false false false 0 0 0 0 0 [] , []

-- A step's outputs, laid under the row that caused them.
lay : ∀ {B} → Pos → ℕ → List (IE B) → List (Pos × Ev (IE B))
lay q j []       = []
lay q j (x ∷ xs) = (q ++ ix 1 ∷ ix j ∷ [] , out x) ∷ lay q (suc j) xs

-- Every output a run of the source causes, from a state, then the end.
outRows : ∀ {B} → FlatOp → Out B → List (Pos × Ev (Maybe (Input B))) → List (Pos × Ev (IE B))
outRows op o []                  = []
outRows op o ((q , out x) ∷ rx)  = lay q 0 (proj₂ (react op o x)) ++ outRows op (react op o x) rx
outRows op o ((q , end) ∷ rx)    = (q , end) ∷ []
outRows op o ((q , skip) ∷ rx)   = outRows op o rx
outRows op o ((q , pin _) ∷ rx)  = outRows op o rx

------------------------------------------------------------------------
-- Held, run by run

-- Past a point where a run's count holds no route of the instant it last
-- began, no value of that instant.
ShutRun : ∀ {A : Set} → List (Pos × Ev (IE A)) → Set
ShutRun rs = ∀ r₁ r₂ → rs ≡ r₁ ++ r₂ → proj₂ (cnt r₁) ≡ 0
           → ∀ {q} → (q , out (instEmit (mark begin) (proj₁ (cnt r₁)))) ∈ r₁
           → ∀ {y a j} → (y , out (instEmit (value a) j)) ∈ r₂ → instantOf y ≡ instantOf q → ⊥

-- What `Held` asks of one run met.
record RunHeld {A : Set} (cs : List Pos) (rs : List (Pos × Ev (IE A))) : Set where
  field
    covered : ∀ r₁ {y e} r₂ → rs ≡ r₁ ++ (y , e) ∷ r₂ → Carried e → ¬ Ex cs y
            → Σ ℕ λ k → cnt r₁ ≡ (nameOf y , suc k)
    exact   : ∀ r₁ {y n} r₂ → rs ≡ r₁ ++ (y , out (instEmit (mark stop) n)) ∷ r₂
            → Σ ℕ λ k → proj₂ (cnt r₁) ≡ suc k
    shut    : ShutRun rs

-- Held is its rows' facts and every run's.
held-runs : ∀ {A} {t : EmissionSet (IE A)} {cs}
          → (∀ {y n} → t y (out (instEmit (mark begin) n)) → n ≡ nameOf y)
          → (∀ {y m n} → t y (out (instEmit (mark m) n)) → Routing m)
          → (∀ {y a n} → t y (out (instEmit (value a) n)) → Early y)
          → (∀ {y} → t y end → Early y)
          → (∀ {y n} → t y (out (instEmit (mark over) n)) → Valued (instantOf y) × opos (instantOf y) ⊑ y)
          → Idle t
          → (∀ {rs} → Met t rs → RunHeld cs rs)
          → Held t cs
held-runs nm rt ea en lt id rh = record
  { named = nm
  ; covered = λ m → RunHeld.covered (rh m)
  ; exact = λ m → RunHeld.exact (rh m)
  ; routing = rt
  ; shut = λ m r₁ r₂ e z bq vy iq → RunHeld.shut (rh m) r₁ r₂ e z bq vy iq
  ; early = ea
  ; ends = en
  ; late = lt
  ; idle = id
  }

------------------------------------------------------------------------
-- Held, row by row

-- The count a list of rows leaves, from a count.
from : ∀ {B} → Routes → List (Pos × Ev (IE B)) → Routes
from c rs = L.foldl count c (values rs)

-- The scan's state past a run of its source.
past : ∀ {B} → FlatOp → Out B → List (Pos × Ev (Maybe (Input B))) → Out B
past op o []                 = o
past op o ((q , out x) ∷ rx) = past op (react op o x) rx
past op o ((q , end) ∷ rx)   = o
past op o ((q , skip) ∷ rx)  = past op o rx
past op o ((q , pin _) ∷ rx) = past op o rx

-- What one row owes, given the count before it.
record Local {B : Set} (cs : List Pos) (c : Routes) (y : Pos) (e : Ev (IE B)) : Set where
  field
    carried : Carried e → ¬ Ex cs y → Σ ℕ λ k → c ≡ (nameOf y , suc k)
    stops   : ∀ {n} → e ≡ out (instEmit (mark stop) n) → Σ ℕ λ k → proj₂ c ≡ suc k

-- What every row of a list owes, each from the count the rows before it
-- leave.
Locals : ∀ {B} → List Pos → Routes → List (Pos × Ev (IE B)) → Set
Locals cs c []             = ⊤
Locals cs c ((y , e) ∷ rs) = Local cs c y e × Locals cs (from c ((y , e) ∷ [])) rs

locals-at : ∀ {B cs c} r₁ {y} {e : Ev (IE B)} {r₂} → Locals cs c (r₁ ++ (y , e) ∷ r₂) → Local cs (from c r₁) y e
locals-at []                   (l , _)  = l
locals-at ((_ , out _) ∷ r₁)   (_ , ls) = locals-at r₁ ls
locals-at ((_ , end) ∷ r₁)     (_ , ls) = locals-at r₁ ls
locals-at ((_ , skip) ∷ r₁)    (_ , ls) = locals-at r₁ ls
locals-at ((_ , pin _) ∷ r₁)   (_ , ls) = locals-at r₁ ls

-- A run whose rows each owe what they should holds, but for its dead
-- instants.
locals-runs : ∀ {B cs} {rs : List (Pos × Ev (IE B))} → Locals cs r₀ rs → ShutRun rs → RunHeld cs rs
locals-runs {cs = cs} L sh = record
  { covered = λ r₁ r₂ eq → Local.carried (at r₁ r₂ eq)
  ; exact   = λ r₁ r₂ eq → Local.stops (at r₁ r₂ eq) refl
  ; shut    = sh }
  where
    at : ∀ r₁ {y e} r₂ → _ ≡ r₁ ++ (y , e) ∷ r₂ → Local cs (cnt r₁) y e
    at r₁ r₂ eq = locals-at r₁ (subst (Locals cs r₀) eq L)

-- A row met lies in what is read, and is shown.
run-row : ∀ {A} {t : EmissionSet A} {c} r₁ {q e r₂} → Run t c (r₁ ++ (q , e) ∷ r₂) → t q e × Visible e
run-row []       ((sn , vi , _) ∷ _) = proj₁ (proj₁ sn) , vi
run-row (_ ∷ r₁) (_ ∷ rn)            = run-row r₁ rn

-- The end owes a route of its instant.
local-end : ∀ {B cs c y} → (¬ Ex cs y → Σ ℕ λ k → c ≡ (nameOf y , suc k)) → Local {B} cs c y end
local-end cov = record { carried = λ { c-end → cov } ; stops = λ () }

postulate
  -- WHAT THE SCAN LAYS OUT IS READ OFF ITS STEPS: each step's outputs,
  -- from the count the outputs before them leave, and the end.
  walk : ∀ {B} op cs (o : Out B) c rx
       → (∀ rx₁ {q x} rx₂ → rx ≡ rx₁ ++ (q , out x) ∷ rx₂
          → Locals cs (from c (outRows op o rx₁)) (lay q 0 (proj₂ (react op (past op o rx₁) x))))
       → (∀ rx₁ {q} rx₂ → rx ≡ rx₁ ++ (q , end) ∷ rx₂ → Local {B} cs (from c (outRows op o rx₁)) q end)
       → Locals cs c (outRows op o rx)
  -- The scan's count of what it sent is the one it keeps.
  inv-past : ∀ {B} op rx → Inv (from r₀ (outRows {B} op init rx)) (proj₁ (past op init rx))
  -- ONE STEP'S OUTPUTS OWE WHAT THEY SHOULD when the routes open at its
  -- row are of the row's instant, a begin it reads is named for it, and
  -- a value or a live over it reads finds a route.
  step-local : ∀ {B} op cs (o : Out B) c q x → Inv c (proj₁ o)
             → (proj₂ c ≡ 0 ⊎ proj₁ c ≡ nameOf q)
             → (∀ {b n} → x ≡ just (inj₁ (b , instEmit (mark begin) n)) → n ≡ nameOf q)
             → (∀ {b a n} → x ≡ just (inj₁ (b , instEmit (value a) n)) → ¬ Ex cs q → Σ ℕ λ k → proj₂ c ≡ suc k)
             → (∀ {b n} → x ≡ just (inj₁ (b , instEmit (mark over) n)) → Flat.spent (proj₁ o) ≡ false → ¬ Ex cs q
                → Σ ℕ λ k → proj₂ c ≡ suc k)
             → (∀ j → instantOf (q ++ ix 1 ∷ ix j ∷ []) ≡ instantOf q)
             → Locals cs c (lay q 0 (proj₂ (react op o x)))

------------------------------------------------------------------------
-- What the source promises

record CombIn {B : Set} (op : FlatOp) (M : EmissionSet (Maybe (Input B))) (cs : List Pos) : Set where
  field
    named  : ∀ {q b n} → M q (out (just (inj₁ (b , instEmit (mark begin) n)))) → n ≡ nameOf q
    early  : ∀ {q b a n} → M q (out (just (inj₁ (b , instEmit (value a) n)))) → Early q
    ends   : ∀ {q} → M q end → Early q
    late   : ∀ {q b n} → M q (out (just (inj₁ (b , instEmit (mark over) n)))) → Valued (instantOf q) × opos (instantOf q) ⊑ q
    runs   : ∀ {rx} → Met M rx → RunHeld cs (outRows op init rx)

-- THE SCANNED STREAM HOLDS what its source promises: a run met of it is
-- laid out from a run met of the source, a prefix of what that run lays.
postulate
  comb-held : ∀ m {Γ B} op (s : Obs Timeline Γ (Maybe (Input B))) (ρ : DenEnv Γ) P cs → GoodEnv ρ → Ok (Hots ρ) P
            → CombIn op (enter (ev m s ρ) P) cs → Held (enter (ev m (each proj₂ (scan (react op) init s)) ρ) P) cs
