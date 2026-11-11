{-# OPTIONS --guardedness #-}

-- A FLATMAP'S SCAN HOLDS WHAT ITS SOURCE PROMISES.  The scan steps
-- `react` over each row its source meets and lays the step's outputs
-- under that row, the `j`-th at `q ⊕ (ix 1 ∷ ix j ∷ [])`; past the
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
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import Data.Unit using (⊤)
open import denotation.Position using (Pos; root; _≟ᵖ_; ix; _⊕_)
open import denotation.Read using (Run; _∷_; Visible)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; FlatOp)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (EmissionSet; Ev; out; end; skip; pin; Den; DenEnv; ⟦_⟧; approx)
open import denotation.Laws.Worlds using (_⊑_)
open import simultaneous.InstEmit using (instEmit; value; mark; begin; stop; over)
open import simultaneous.SObs using (Flat; flat; module Elaborate)
open import simultaneous.Relations using (Met; values; values-++)
open import Data.List.Properties using (foldl-++; ++-assoc)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ)
open import Data.List.Relation.Unary.Any using (here; there)
open import simultaneous.Shut using (r₀)
open import simultaneous.FlatSim using (Inv; inv₀; react-inv; react-exact; NoCB; tot; live; dead)
open import simultaneous.Routed using (Carried; c-end)
open import simultaneous.Readings using (rootOf)
open import simultaneous.Routed using (Held; Carried; cnt; Ex; nameOf; Early; Valued; opos; Routing; Idle; Rest)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) using (IE; Routes; count; Out; Input; react; each)

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
lay q j (x ∷ xs) = (q ⊕ (ix 1 ∷ ix j ∷ []) , out x) ∷ lay q (suc j) xs

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
           → ∀ {y a j} → (y , out (instEmit (value a) j)) ∈ r₂ → rootOf y ≡ rootOf q → ⊥

-- What `Held` asks of one run met.
record RunHeld {A : Set} (cs : List Pos) (rs : List (Pos × Ev (IE A))) : Set where
  field
    covered : ∀ r₁ {y e} r₂ → rs ≡ r₁ ++ (y , e) ∷ r₂ → Carried e → ¬ Ex cs y
            → Σ ℕ λ k → cnt r₁ ≡ (nameOf y , suc k)
    exact   : ∀ r₁ {y n} r₂ → rs ≡ r₁ ++ (y , out (instEmit (mark stop) n)) ∷ r₂
            → Σ ℕ λ k → proj₂ (cnt r₁) ≡ suc k
    shut    : ShutRun rs

-- What a run holds, its prefixes hold.
runs-prefix : ∀ {A cs} {rs : List (Pos × Ev (IE A))} ext → RunHeld cs (rs ++ ext) → RunHeld cs rs
runs-prefix {rs = rs} ext h = record
  { covered = λ r₁ r₂ eq → RunHeld.covered h r₁ (r₂ ++ ext) (ext-eq r₁ r₂ eq)
  ; exact   = λ r₁ r₂ eq → RunHeld.exact h r₁ (r₂ ++ ext) (ext-eq r₁ r₂ eq)
  ; shut    = λ r₁ r₂ eq z bq vy iq → RunHeld.shut h r₁ (r₂ ++ ext) (trans (cong (_++ ext) eq) (++-assoc r₁ r₂ ext)) z bq (∈-++⁺ˡ vy) iq }
  where
    ext-eq : ∀ r₁ {y} r₂ → rs ≡ r₁ ++ y ∷ r₂ → rs ++ ext ≡ r₁ ++ y ∷ (r₂ ++ ext)
    ext-eq r₁ {y} r₂ eq = trans (cong (_++ ext) eq) (++-assoc r₁ (y ∷ r₂) ext)

-- Held is its rows' facts and every run's.
held-runs : ∀ {A} {t : EmissionSet (IE A)} {cs}
          → (∀ {y n} → t y (out (instEmit (mark begin) n)) → n ≡ nameOf y)
          → (∀ {y m n} → t y (out (instEmit (mark m) n)) → Routing m)
          → (∀ {y a n} → t y (out (instEmit (value a) n)) → Early y)
          → (∀ {y} → t y end → Early y)
          → (∀ {y n} → t y (out (instEmit (mark over) n)) → Valued (rootOf y) × opos (rootOf y) ⊑ y)
          → Idle t
          → Rest t
          → (∀ {rs} → Met t rs → RunHeld cs rs)
          → Held t cs
held-runs nm rt ea en lt id re rh = record
  { named = nm
  ; covered = λ m → RunHeld.covered (rh m)
  ; exact = λ m → RunHeld.exact (rh m)
  ; routing = rt
  ; shut = λ m r₁ r₂ e z bq vy iq → RunHeld.shut (rh m) r₁ r₂ e z bq vy iq
  ; early = ea
  ; ends = en
  ; late = lt
  ; idle = id
  ; rest = re
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

-- A ROW A RUN OF THE SOURCE LAYS OUT: a step's output under the row it
-- read, or the source's end.
data Laid {B} (op : FlatOp) (o : Out B) (rx : List (Pos × Ev (Maybe (Input B)))) : Pos → Ev (IE B) → Set where
  laid  : ∀ rx₁ {q x} rx₂ {j v} → rx ≡ rx₁ ++ (q , out x) ∷ rx₂ → v ∈ proj₂ (react op (past op o rx₁) x)
        → Laid op o rx (q ⊕ (ix 1 ∷ ix j ∷ [])) (out v)
  ended : ∀ rx₁ {q} rx₂ → rx ≡ rx₁ ++ (q , end) ∷ rx₂ → Laid op o rx q end

lay-in : ∀ {B} q j (xs : List (IE B)) {y e} → (y , e) ∈ lay q j xs
       → Σ ℕ λ j′ → Σ (IE B) λ v → y ≡ q ⊕ (ix 1 ∷ ix j′ ∷ []) × e ≡ out v × v ∈ xs
lay-in q j (x ∷ xs) (here refl) = j , x , refl , refl , here refl
lay-in q j (x ∷ xs) (there i) with lay-in q (suc j) xs i
... | j′ , v , ey , ee , vi = j′ , v , ey , ee , there vi

laid-in : ∀ {B} op (o : Out B) rx {y e} → (y , e) ∈ outRows op o rx → Laid op o rx y e
laid-in op o ((q , out x) ∷ rx) i with ∈-++⁻ (lay q 0 (proj₂ (react op o x))) i
... | inj₁ li with lay-in q 0 _ li
...   | j′ , v , refl , refl , vi = laid [] rx refl vi
laid-in op o ((q , out x) ∷ rx) i | inj₂ ri with laid-in op (react op o x) rx ri
... | laid rx₁ rx₂ refl vi = laid ((q , out x) ∷ rx₁) rx₂ refl vi
... | ended rx₁ rx₂ refl   = ended ((q , out x) ∷ rx₁) rx₂ refl
laid-in op o ((q , end) ∷ rx) (here refl) = ended [] rx refl
laid-in op o ((q , skip) ∷ rx) i with laid-in op o rx i
... | laid rx₁ rx₂ refl vi = laid ((q , skip) ∷ rx₁) rx₂ refl vi
... | ended rx₁ rx₂ refl   = ended ((q , skip) ∷ rx₁) rx₂ refl
laid-in op o ((q , pin r) ∷ rx) i with laid-in op o rx i
... | laid rx₁ rx₂ refl vi = laid ((q , pin r) ∷ rx₁) rx₂ refl vi
... | ended rx₁ rx₂ refl   = ended ((q , pin r) ∷ rx₁) rx₂ refl

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

-- A step's outputs, laid out, count as the step sent them.
values-lay : ∀ {B} q j (xs : List (IE B)) → values (lay q j xs) ≡ xs
values-lay q j []       = refl
values-lay q j (x ∷ xs) = cong (x ∷_) (values-lay q (suc j) xs)

from-++ : ∀ {B} c (r₁ r₂ : List (Pos × Ev (IE B))) → from c (r₁ ++ r₂) ≡ from (from c r₁) r₂
from-++ c r₁ r₂ = trans (cong (L.foldl count c) (values-++ r₁ r₂)) (foldl-++ count c (values r₁) (values r₂))

-- THE SCAN'S COUNT OF WHAT IT SENT IS THE ONE IT KEEPS: each step keeps
-- its counters within what it has sent.
inv-from : ∀ {B} op (o : Out B) c rx → Inv c (proj₁ o) → Inv (from c (outRows op o rx)) (proj₁ (past op o rx))
inv-from op o c []                 i = i
inv-from op o c ((q , out x) ∷ rx) i =
  subst (λ c′ → Inv c′ (proj₁ (past op (react op o x) rx))) (sym (from-++ c (lay q 0 (proj₂ (react op o x))) (outRows op (react op o x) rx)))
    (inv-from op (react op o x) (from c (lay q 0 (proj₂ (react op o x)))) rx
      (subst (λ c′ → Inv c′ (proj₁ (react op o x))) (cong (L.foldl count c) (sym (values-lay q 0 (proj₂ (react op o x)))))
        (react-inv op o x i)))
inv-from op o c ((q , end) ∷ rx)   i = i
inv-from op o c ((q , skip) ∷ rx)  i = inv-from op o c rx i
inv-from op o c ((q , pin _) ∷ rx) i = inv-from op o c rx i

inv-past : ∀ {B} op rx → Inv (from r₀ (outRows {B} op init rx)) (proj₁ (past op init rx))
inv-past op rx = inv-from op init r₀ rx inv₀

-- The count's instant is the scan's.
inv-at : ∀ {c s} → Inv c s → proj₁ c ≡ Flat.at s
inv-at (live _ _) = refl
inv-at (dead _ _) = refl

-- THE SCAN'S COUNT OF WHAT IT SENT IS EXACTLY ITS COUNTERS, so long as
-- no closer begins a route.
exact-from : ∀ {B} op (o : Out B) c rx → (∀ rx₁ {q x} rx₂ → rx ≡ rx₁ ++ (q , out x) ∷ rx₂ → NoCB x)
           → Inv c (proj₁ o) → proj₂ c ≡ tot (proj₁ o) → proj₂ (from c (outRows op o rx)) ≡ tot (proj₁ (past op o rx))
exact-from op o c []                 nc i e = e
exact-from op o c ((q , out x) ∷ rx) nc i e =
  trans (cong proj₂ (from-++ c (lay q 0 (proj₂ (react op o x))) (outRows op (react op o x) rx)))
    (exact-from op (react op o x) (from c (lay q 0 (proj₂ (react op o x)))) rx
      (λ rx₁ rx₂ eq → nc ((q , out x) ∷ rx₁) rx₂ (cong (_ ∷_) eq))
      (subst (λ c′ → Inv c′ (proj₁ (react op o x))) cv (react-inv op o x i))
      (subst (λ c′ → proj₂ c′ ≡ tot (proj₁ (react op o x))) cv (react-exact op o x (nc [] rx refl) i e)))
  where cv = cong (L.foldl count c) (sym (values-lay q 0 (proj₂ (react op o x))))
exact-from op o c ((q , end) ∷ rx)   nc i e = e
exact-from op o c ((q , skip) ∷ rx)  nc i e = exact-from op o c rx (λ rx₁ rx₂ eq → nc ((q , skip) ∷ rx₁) rx₂ (cong (_ ∷_) eq)) i e
exact-from op o c ((q , pin r) ∷ rx) nc i e = exact-from op o c rx (λ rx₁ rx₂ eq → nc ((q , pin r) ∷ rx₁) rx₂ (cong (_ ∷_) eq)) i e

exact-past : ∀ {B} op rx → (∀ rx₁ {q x} rx₂ → rx ≡ rx₁ ++ (q , out x) ∷ rx₂ → NoCB x)
           → proj₂ (from r₀ (outRows {B} op init rx)) ≡ tot (proj₁ (past op init rx))
exact-past op rx nc = exact-from op init r₀ rx nc inv₀ refl

postulate
  -- WHAT THE SCAN LAYS OUT IS READ OFF ITS STEPS: each step's outputs,
  -- from the count the outputs before them leave, and the end.
  walk : ∀ {B} op cs (o : Out B) c rx
       → (∀ rx₁ {q x} rx₂ → rx ≡ rx₁ ++ (q , out x) ∷ rx₂
          → Locals cs (from c (outRows op o rx₁)) (lay q 0 (proj₂ (react op (past op o rx₁) x))))
       → (∀ rx₁ {q} rx₂ → rx ≡ rx₁ ++ (q , end) ∷ rx₂ → Local {B} cs (from c (outRows op o rx₁)) q end)
       → Locals cs c (outRows op o rx)
  -- ONE STEP'S OUTPUTS OWE WHAT THEY SHOULD when the routes open at its
  -- row are of the row's instant, a begin it reads is named for it, and
  -- a value or a live over it reads finds a route.
  step-local : ∀ {B} op cs (o : Out B) c q x → Inv c (proj₁ o)
             → (proj₂ c ≡ 0 ⊎ proj₁ c ≡ nameOf q)
             → (∀ {b n} → x ≡ just (inj₁ (b , instEmit (mark begin) n)) → n ≡ nameOf q)
             → (∀ {b a n} → x ≡ just (inj₁ (b , instEmit (value a) n)) → ¬ Ex cs q → Σ ℕ λ k → proj₂ c ≡ suc k)
             → (∀ {b n} → x ≡ just (inj₁ (b , instEmit (mark over) n)) → Flat.spent (proj₁ o) ≡ false → ¬ Ex cs q
                → Σ ℕ λ k → proj₂ c ≡ suc k)
             → (∀ j → rootOf (q ⊕ (ix 1 ∷ ix j ∷ [])) ≡ rootOf q)
             → Locals cs c (lay q 0 (proj₂ (react op o x)))

------------------------------------------------------------------------
-- What the source promises

record CombIn {B : Set} (op : FlatOp) (M : EmissionSet (Maybe (Input B))) (cs : List Pos) : Set where
  field
    named  : ∀ {q b n} → M q (out (just (inj₁ (b , instEmit (mark begin) n)))) → n ≡ nameOf q
    early  : ∀ {q b a n} → M q (out (just (inj₁ (b , instEmit (value a) n)))) → Early q
    ends   : ∀ {q} → M q end → Early q
    late   : ∀ {q b n} → M q (out (just (inj₁ (b , instEmit (mark over) n)))) → Valued (rootOf q) × opos (rootOf q) ⊑ q
    runs   : ∀ {rx} → Met M rx → RunHeld cs (outRows op init rx)

