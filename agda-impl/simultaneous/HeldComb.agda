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
open import simultaneous.SObs using (Flat; flat; lone; module Elaborate)
open import simultaneous.Relations using (Met; values; values-++)
open import Data.List.Properties using (foldl-++; ++-assoc)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ)
open import Data.List.Relation.Unary.Any using (here; there)
open import simultaneous.Shut using (r₀)
open import simultaneous.FlatSim using (Inv; inv₀; react-inv; react-exact; NoCB; tot; live; dead)
open import simultaneous.Routed using (Carried; c-end; c-value; c-stop; c-over; nm)
open import Data.Nat using (_≤_; s≤s; z≤n; _⊓_; zero; _+_; _∸_)
open import Data.Nat.Properties using (≤-trans; ≤-reflexive; m≤m+n; m≤n+m; m⊓n≤n; +-monoˡ-≤)
open import Data.Bool using (true; if_then_else_; _∧_; _∨_)
open import Data.Empty using (⊥-elim)
open import Data.List.Relation.Unary.Any using () renaming (map to any-map)
open import denotation.Laws.Worlds using (⊑-trans; ⊑-inside; inside-⊑)
open import Tree using (mergeᶠ; switchᶠ; exhaustᶠ)
open import simultaneous.InstEmit using (carry; outerOpen; outerClose; laneStart; laneDone; burstEnd; outerDone; subscribed; completed)
open import simultaneous.SObs using (isZero; outerB; laneB; closeB)
open import Relation.Nullary using (does)
open import simultaneous.Readings using (rootOf)
open import simultaneous.Routed using (Held; Carried; cnt; Ex; nameOf; Early; Valued; opos; Routing; Idle; Rest)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; Routes; count; Out; Input; react; each;
  cut; unpark; arrive; burstOver; left; begun; overed; stopped; onMark; share; anyHolds; setAt)
  renaming (ended to laneEnded; stops to stopsᵒ)

------------------------------------------------------------------------
-- What the scan lays out

-- The meaning, or its n-th approximant.
ev : Maybe ℕ → ∀ {Γ A} → Obs Timeline Γ A → DenEnv Γ → Den A
ev nothing  o ρ = ⟦ o ⟧ ρ
ev (just n) o ρ = approx n o ρ

-- The scan's first state: nothing counted, no output.
init : ∀ {B} → Out B
init = flat root 0 0 false false false 0 0 0 0 0 [] , []

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

-- Rows owing what they should, then more from the count they leave.
locals-++ : ∀ {B cs c} (r₁ : List (Pos × Ev (IE B))) {r₂} → Locals cs c r₁ → Locals cs (from c r₁) r₂ → Locals cs c (r₁ ++ r₂)
locals-++ []                 _        l₂ = l₂
locals-++ ((_ , out _) ∷ r₁) (l , ls) l₂ = l , locals-++ r₁ ls l₂
locals-++ ((_ , end) ∷ r₁)   (l , ls) l₂ = l , locals-++ r₁ ls l₂
locals-++ ((_ , skip) ∷ r₁)  (l , ls) l₂ = l , locals-++ r₁ ls l₂
locals-++ ((_ , pin _) ∷ r₁) (l , ls) l₂ = l , locals-++ r₁ ls l₂

-- WHAT THE SCAN LAYS OUT IS READ OFF ITS STEPS: each step's outputs,
-- from the count the outputs before them leave, and the end.
walk : ∀ {B} op cs (o : Out B) c rx
     → (∀ rx₁ {q x} rx₂ → rx ≡ rx₁ ++ (q , out x) ∷ rx₂
        → Locals cs (from c (outRows op o rx₁)) (lay q 0 (proj₂ (react op (past op o rx₁) x))))
     → (∀ rx₁ {q} rx₂ → rx ≡ rx₁ ++ (q , end) ∷ rx₂ → Local {B} cs (from c (outRows op o rx₁)) q end)
     → Locals cs c (outRows op o rx)
walk op cs o c []                 st fn = _
walk op cs o c ((q , out x) ∷ rx) st fn =
  locals-++ (lay q 0 (proj₂ (react op o x))) (st [] rx refl)
    (walk op cs (react op o x) (from c (lay q 0 (proj₂ (react op o x)))) rx
      (λ rx₁ {q′} {x′} rx₂ eq → subst (λ c′ → Locals cs c′ (lay q′ 0 (proj₂ (react op (past op (react op o x) rx₁) x′))))
                        (from-++ c (lay q 0 (proj₂ (react op o x))) (outRows op (react op o x) rx₁))
                        (st ((q , out x) ∷ rx₁) rx₂ (cong ((q , out x) ∷_) eq)))
      (λ rx₁ {q′} rx₂ eq → subst (λ c′ → Local cs c′ q′ end) (from-++ c (lay q 0 (proj₂ (react op o x))) (outRows op (react op o x) rx₁))
                        (fn ((q , out x) ∷ rx₁) rx₂ (cong ((q , out x) ∷_) eq))))
walk op cs o c ((q , end) ∷ rx)   st fn = fn [] rx refl , _
walk op cs o c ((q , skip) ∷ rx)  st fn =
  walk op cs o c rx (λ rx₁ rx₂ eq → st ((q , skip) ∷ rx₁) rx₂ (cong ((q , skip) ∷_) eq)) (λ rx₁ rx₂ eq → fn ((q , skip) ∷ rx₁) rx₂ (cong ((q , skip) ∷_) eq))
walk op cs o c ((q , pin r) ∷ rx) st fn =
  walk op cs o c rx (λ rx₁ rx₂ eq → st ((q , pin r) ∷ rx₁) rx₂ (cong ((q , pin r) ∷_) eq)) (λ rx₁ rx₂ eq → fn ((q , pin r) ∷ rx₁) rx₂ (cong ((q , pin r) ∷_) eq))

-- WHAT ONE STEP SENDS, row by row, from the count before it: nothing, one
-- row, or stops, each finding a route of the row's instant.
private
  -- What a run is exempt for at its read, it is exempt for below it.
  ex-lay : ∀ cs q j → (∀ j → rootOf (q ⊕ (ix 1 ∷ ix j ∷ [])) ≡ rootOf q) → Ex cs q → Ex cs (q ⊕ (ix 1 ∷ ix j ∷ []))
  ex-lay cs q j rt = any-map λ {c} (i , r) → ⊑-inside (⊑-trans (inside-⊑ c q i) ((ix 1 ∷ ix j ∷ []) , refl)) , trans (rt j) r

  -- An open count, of the read's instant or none, is of the row's.
  open-at : ∀ {m K q k} j → (∀ j → rootOf (q ⊕ (ix 1 ∷ ix j ∷ [])) ≡ rootOf q) → (K ≡ 0 ⊎ m ≡ nameOf q) → K ≡ suc k
          → (m , K) ≡ (nameOf (q ⊕ (ix 1 ∷ ix j ∷ [])) , suc k)
  open-at j rt (inj₁ refl) ()
  open-at {k = k} j rt (inj₂ refl) refl = cong (λ z → z , suc k) (cong nm (sym (rt j)))

  named-of : ∀ {m K q} → suc K ≡ 0 ⊎ m ≡ nameOf q → m ≡ nameOf q
  named-of (inj₁ ())
  named-of (inj₂ e) = e

  locals-stops : ∀ {B} cs (m : Pos) K k n q j → (∀ j → rootOf (q ⊕ (ix 1 ∷ ix j ∷ [])) ≡ rootOf q)
               → (K ≡ 0 ⊎ m ≡ nameOf q) → k ≤ K → Locals cs (m , K) (lay q j (stopsᵒ {B} k n))
  locals-stops cs m K       zero    n q j rt cur le       = _
  locals-stops cs m (suc K) (suc k) n q j rt cur (s≤s le) =
    record { carried = λ { c-stop _ → K , open-at {m = m} {K = suc K} {q = q} j rt cur refl } ; stops = λ _ → K , refl }
    , locals-stops cs m K k n q (suc j) rt (inj₂ (named-of {q = q} cur)) le

  locals-cut : ∀ {B} cs (m : Pos) K k n s q → (∀ j → rootOf (q ⊕ (ix 1 ∷ ix j ∷ [])) ≡ rootOf q)
             → (K ≡ 0 ⊎ m ≡ nameOf q) → k ≤ K → Locals cs (m , K) (lay q 0 (proj₂ (cut {B} k n s)))
  locals-cut cs m K k n s q rt cur le with Flat.spent s | anyHolds (Flat.at s) (Flat.live s)
  ... | true  | _     = _
  ... | false | true  = _
  ... | false | false = locals-stops cs m K k n q 0 rt cur le

  -- The counters hold no more routes than are counted.
  inv-tot : ∀ {c s} → Inv c s → tot s ≤ proj₂ c
  inv-tot (live _ le) = le
  inv-tot (dead _ z)  = ≤-reflexive z

  outer≤ : ∀ s → Flat.outer s ≤ tot s
  outer≤ s = ≤-trans (m≤m+n (Flat.outer s) (Flat.lanes s)) (≤-trans (m≤m+n _ (Flat.held s)) (m≤m+n _ (Flat.parked s)))

  lanes≤ : ∀ s → Flat.lanes s ≤ tot s
  lanes≤ s = ≤-trans (m≤n+m (Flat.lanes s) (Flat.outer s)) (≤-trans (m≤m+n _ (Flat.held s)) (m≤m+n _ (Flat.parked s)))

  held≤ : ∀ s → Flat.held s ≤ tot s
  held≤ s = ≤-trans (m≤n+m (Flat.held s) (Flat.outer s + Flat.lanes s)) (m≤m+n _ (Flat.parked s))

  parked≤ : ∀ s → Flat.parked s ≤ tot s
  parked≤ s = m≤n+m (Flat.parked s) _

  ended≤ : ∀ s → Flat.acc s ⊓ Flat.lanes s + Flat.held s ≤ tot s
  ended≤ s = ≤-trans (+-monoˡ-≤ (Flat.held s) (≤-trans (m⊓n≤n (Flat.acc s) (Flat.lanes s)) (m≤n+m (Flat.lanes s) (Flat.outer s))))
                     (m≤m+n _ (Flat.parked s))

  share≤ : ∀ b s → share b s ≤ tot s
  share≤ outerB s = outer≤ s
  share≤ laneB  s = lanes≤ s
  share≤ closeB s = z≤n

  stop≤ : ∀ b s {c} → Inv c s → (if Flat.spent s then 0 else share b s) ≤ proj₂ c
  stop≤ b s (live sp le) rewrite sp = ≤-trans (share≤ b s) le
  stop≤ b s (dead sp _)  rewrite sp = z≤n

  module Step {B : Set} (cs : List Pos) (m : Pos) (K : ℕ) (q : Pos)
              (rt : ∀ j → rootOf (q ⊕ (ix 1 ∷ ix j ∷ [])) ≡ rootOf q) (cur : K ≡ 0 ⊎ m ≡ nameOf q) where

    quiet : ∀ {mk n} → (mk ≡ stop → ⊥) → (mk ≡ over → ⊥) → Locals cs (m , K) (lay {B} q 0 (instEmit (mark mk) n ∷ []))
    quiet ns no = record { carried = λ { c-stop → ⊥-elim (ns refl) ; c-over → ⊥-elim (no refl) }
                         ; stops = λ { refl → ⊥-elim (ns refl) } } , _

    stopped-l : ∀ b n s k → k ≤ K → Locals cs (m , K) (lay q 0 (proj₂ (stopped {B} b n s k)))
    stopped-l b n s zero    _        = _
    stopped-l b n s (suc _) le = locals-stops cs m K 1 n q 0 rt cur (≤-trans (s≤s z≤n) le)

    ended-l : ∀ k n s → k + Flat.held s ≤ K → Locals cs (m , K) (lay q 0 (proj₂ (laneEnded {B} k n s)))
    ended-l k n s le with Flat.queue s
    ... | suc _ = _
    ... | zero with Flat.finished s | Flat.active s
    ...   | true  | zero  = _
    ...   | true  | suc _ = locals-cut cs m K (k + Flat.held s) n (record s { held = 0 }) q rt cur le
    ...   | false | _     = locals-cut cs m K (k + Flat.held s) n (record s { held = 0 }) q rt cur le

    burst-l : ∀ h n s → Flat.held s ≤ K → Locals cs (m , K) (lay q 0 (proj₂ (burstOver {B} h n s)))
    burst-l true  n s _  = _
    burst-l false n s le = locals-cut cs m K (Flat.held s) n (record s { held = 0 }) q rt cur le

    left-l : ∀ n s → Flat.outer s ≤ K → Locals cs (m , K) (lay q 0 (proj₂ (left {B} n s)))
    left-l n s le with isZero (Flat.active s) ∧ isZero (Flat.queue s)
    ... | true  = _
    ... | false = locals-cut cs m K (Flat.outer s) n (record s { outer = 0 }) q rt cur le

    unpark-l : ∀ n s → Flat.parked s ≤ K → Locals cs (m , K) (lay q 0 (proj₂ (unpark {B} n s)))
    unpark-l n s le with anyHolds (Flat.at s) (Flat.live s)
    ... | true  = _
    ... | false = locals-stops cs m K (Flat.parked s) n q 0 rt cur le

    arrive-l : ∀ op n s → Flat.lanes s ≤ K → Locals cs (m , K) (lay q 0 (proj₂ (arrive {B} op n s)))
    arrive-l (mergeᶠ (just _)) n s _  = _
    arrive-l (mergeᶠ nothing)  n s _  = _
    arrive-l switchᶠ           n s le = locals-cut cs m K (Flat.lanes s) n (record s { active = 0 ; lanes = 0 }) q rt cur le
    arrive-l exhaustᶠ          n s _  = _

    begun-l : ∀ b n s → Locals cs (m , K) (lay q 0 (proj₂ (begun {B} b n s)))
    begun-l b n s with does (n ≟ᵖ Flat.at s) ∧ Flat.spent s
    ... | true  = _
    ... | false = quiet (λ ()) (λ ())

    overed-l : ∀ n s → (Flat.spent s ≡ false → ¬ Ex cs q → Σ ℕ λ k → K ≡ suc k) → Locals cs (m , K) (lay q 0 (proj₂ (overed {B} n s)))
    overed-l n s oo with Flat.spent s
    ... | true  = _
    ... | false = record { carried = λ { c-over ne → let k , e = oo refl (λ x → ne (ex-lay cs q 0 rt x)) in k , open-at {m = m} {K = K} {q = q} 0 rt cur e }
                         ; stops = λ () } , _

    mark-l : ∀ op b mk n s → Inv (m , K) s → (Flat.spent s ≡ false → mk ≡ over → ¬ Ex cs q → Σ ℕ λ k → K ≡ suc k)
           → Locals cs (m , K) (lay q 0 (proj₂ (onMark {B} op b s mk n)))
    mark-l op b begin      n s iv oo = begun-l b n s
    mark-l op b stop       n s iv oo = stopped-l b n s _ (stop≤ b s iv)
    mark-l op b over       n s iv oo = overed-l n s (λ sp → oo sp refl)
    mark-l op b carry      n s iv oo = _
    mark-l op b outerOpen  n s iv oo = arrive-l op n s (≤-trans (lanes≤ s) (inv-tot iv))
    mark-l op b outerClose n s iv oo = _
    mark-l op b laneStart  n s iv oo = _
    mark-l op b laneDone   n s iv oo = ended-l (Flat.acc s ⊓ Flat.lanes s) n (record s { active = Flat.active s ∸ 1 ; lanes = Flat.lanes s ∸ Flat.acc s ; acc = 0 ; dead = true }) (≤-trans (ended≤ s) (inv-tot iv))
    mark-l op b burstEnd   n s iv oo = burst-l (isZero (Flat.held s) ∨ Flat.dead s) n s (≤-trans (held≤ s) (inv-tot iv))
    mark-l op b outerDone  n s iv oo = left-l n (record s { finished = true }) (≤-trans (outer≤ s) (inv-tot iv))
    mark-l op b subscribed n s iv oo = quiet (λ ()) (λ ())
    mark-l op b completed  n s iv oo = quiet (λ ()) (λ ())

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
step-local op cs (s , _) (m , K) q nothing iv cur bn vo oo rt = _
step-local op cs (s , _) (m , K) q (just (inj₁ (b , instEmit (value v) n))) iv cur bn vo oo rt =
  record { carried = λ { c-value ne → let k , e = vo refl (λ x → ne (ex-lay cs q 0 rt x)) in k , open-at {m = m} {K = K} {q = q} 0 rt cur e }
         ; stops = λ () } , _
step-local op cs (s , _) (m , K) q (just (inj₁ (b , instEmit (mark mk) n))) iv cur bn vo oo rt =
  Step.mark-l cs m K q rt cur op b mk n s iv λ { sp refl → oo refl sp }
step-local op cs (s , _) (m , K) q (just (inj₂ (i , r))) iv cur bn vo oo rt =
  Step.unpark-l cs m K q rt cur root (record s { live = setAt i r (Flat.live s) }) (≤-trans (parked≤ s) (inv-tot iv))

------------------------------------------------------------------------
-- What the source promises

record CombIn {B : Set} (op : FlatOp) (M : EmissionSet (Maybe (Input B))) (cs : List Pos) : Set where
  field
    named  : ∀ {q b n} → M q (out (just (inj₁ (b , instEmit (mark begin) n)))) → n ≡ nameOf q
    early  : ∀ {q b a n} → M q (out (just (inj₁ (b , instEmit (value a) n)))) → Early q
    ends   : ∀ {q} → M q end → Early q
    late   : ∀ {q b n} → M q (out (just (inj₁ (b , instEmit (mark over) n)))) → Valued (rootOf q) × opos (rootOf q) ⊑ q
    runs   : ∀ {rx} → Met M rx → RunHeld cs (outRows op init rx)

