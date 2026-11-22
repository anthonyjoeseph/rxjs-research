{-# OPTIONS --guardedness #-}

-- FLATMAP'S SCAN COUNTS NO MORE OF A BRANCH'S ROUTES THAN THE BRANCH SHOWS
-- (`past-within`), for the outer and the lanes alike.  The branch's counter
-- is none, or at most the count of the branch's own rows, of the name they
-- last began: its begin adds one to both, under a new name restarting
-- both; its stop takes one from both; an over ends both; nothing else
-- touches the branch's rows, and every other step leaves the counter, its
-- instant and its over alone, or lowers the counter, or clears it.  Past
-- the over the counter is none, so a begin the scan drops there costs
-- nothing.
module simultaneous.FlatLanes where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_])
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊓_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; m∸n≤m; n≤0⇒n≡0; ∸-monoˡ-≤)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Relation.Nullary using (does; yes; no)
open import Data.Bool.Properties using (not-¬)
open import quickcheck.Tabled.Exact.Base using (≟-true)

open import Tree using (mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Position using (Pos; root; _≟ᵖ_; sub; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; EmissionSet; out; end; skip; pin)
open import denotation.Read using (Run; []; _∷_; loud)
open import denotation.Laws.Worlds using (InvAt; pinby-silent)
open import simultaneous.InstEmit using (instEmit; value; mark; begin; stop; over; outerOpen; outerClose; laneStart; carry;
  laneDone; burstEnd; outerDone; subscribed; completed)
open import simultaneous.SObs using (Flat; Branch; outerB; laneB; closeB; isZero; lone; module Elaborate)
open import simultaneous.Relations using (Met; values)
open import simultaneous.HeldComb using (past; init)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; Routes; count; Out; Input; react; onMark; begun; entered;
  bump; stopped; overed; cut; unpark; arrive; ended; burstOver; left; anyHolds; setAt; share; anew)

-- A branch's row, as the scan's source tags it.
Tg : ∀ {B} → Branch → IE B → Maybe (Input B)
Tg b x = just (inj₁ (b , x))

-- A BRANCH OF THE SCAN'S SOURCE: the branch's row, where it shows it.
sameB : ∀ {B} → Branch → Branch → IE B → Maybe (Ev (IE B))
sameB outerB outerB x = just (out x)
sameB laneB  laneB  x = just (out x)
sameB closeB closeB x = just (out x)
sameB _      _      _ = nothing

brTag : ∀ {B} → Branch → Ev (Maybe (Input B)) → Maybe (Ev (IE B))
brTag b (out (just (inj₁ (b′ , x)))) = sameB b b′ x
brTag b _                            = nothing

-- A branch's row is its own.
tagged : ∀ {B} b {x} → brTag {B} b (out (Tg b x)) ≡ nothing → ⊥
tagged outerB ()
tagged laneB  ()
tagged closeB ()

-- WHERE A RUN OF THE SOURCE MEETS A BRANCH'S ROWS: one `sub J` below the
-- branch's own, as the source reads its value through `h`.
data BProj {A B : Set} (b : Branch) (h : IE A → IE B) (J : Pos)
     : List (Pos × Ev (Maybe (Input B))) → List (Pos × Ev (IE A)) → Set where
  []   : BProj b h J [] []
  keep : ∀ {y x rx rs} → BProj b h J rx rs → BProj b h J ((y ⊕ [ sub J ] , out (Tg b (h x))) ∷ rx) ((y , out x) ∷ rs)
  drop : ∀ {q e rx rs} → brTag b e ≡ nothing → BProj b h J rx rs → BProj b h J ((q , e) ∷ rx) rs

-- A projection keeps only the branch's values.
bproj-end : ∀ {A B b} {h : IE A → IE B} {J rx rs c} → BProj b h J rx rs → (c , end) ∈ rs → ⊥
bproj-end []          ()
bproj-end (keep pr)   (here ())
bproj-end (keep pr)   (there i) = bproj-end pr i
bproj-end (drop _ pr) i         = bproj-end pr i

-- Nothing is met past the end.
end-last : ∀ {A H p} {t : EmissionSet A} → InvAt H p t → ∀ r₁ {q r₂} → Met t (r₁ ++ (q , end) ∷ r₂) → r₂ ≡ []
end-last {t = t} I r₁ {q} mt = go r₁ mt
  where
    past-end : ∀ {rs} → t q end → Run t (just q) rs → rs ≡ []
    past-end _  []                                   = refl
    past-end tq ((((ty , _) , _) , vi , aq , _) ∷ _) = ⊥-elim (loud vi (pinby-silent (InvAt.quiet I tq ty aq)))
    go : ∀ r₁ {c r₂} → Run t c (r₁ ++ (q , end) ∷ r₂) → r₂ ≡ []
    go []       ((((tq , _) , _) , _) ∷ rn) = past-end tq rn
    go (_ ∷ r₁) (_ ∷ rn)                    = go r₁ rn

------------------------------------------------------------------------
-- The invariant

-- The branches the scan counts.
data Counted : Branch → Set where
  co : Counted outerB
  cl : Counted laneB

-- A branch's counter: none past the over, within the branch's count, and
-- of its name unless none.
record Within (b : Branch) (s : Flat Pos) (c : Routes) : Set where
  constructor within
  field
    spent : Flat.spent s ≡ true → share b s ≡ 0
    le    : share b s ≤ proj₂ c
    named : share b s ≡ 0 ⊎ Flat.at s ≡ proj₁ c

-- A step that keeps the instant and the over and lowers both counters.
record Same (s s′ : Flat Pos) : Set where
  constructor same
  field
    lowL : Flat.lanes s′ ≤ Flat.lanes s
    lowO : Flat.outer s′ ≤ Flat.outer s
    at≡  : Flat.at s′ ≡ Flat.at s
    sp≡  : Flat.spent s′ ≡ Flat.spent s

-- …or only the one branch's.
record SameB (b : Branch) (s s′ : Flat Pos) : Set where
  constructor sameB′
  field
    lower : share b s′ ≤ share b s
    at≡   : Flat.at s′ ≡ Flat.at s
    sp≡   : Flat.spent s′ ≡ Flat.spent s

-- FlatSim's own counters: the outer's and the lanes'.
same-trans : ∀ {s₁ s₂ s₃} → Same s₁ s₂ → Same s₂ s₃ → Same s₁ s₃
same-trans (same l₁ o₁ a₁ p₁) (same l₂ o₂ a₂ p₂) = same (≤-trans l₂ l₁) (≤-trans o₂ o₁) (trans a₂ a₁) (trans p₂ p₁)

same-b : ∀ b {s s′} → Same s s′ → SameB b s s′
same-b outerB (same _ o a p) = sameB′ o a p
same-b laneB  (same l _ a p) = sameB′ l a p
same-b closeB (same _ _ a p) = sameB′ z≤n a p

within-sameB : ∀ {b s s′ c} → SameB b s s′ → Within b s c → Within b s′ c
within-sameB {b} {s} {s′} (sameB′ l a p) (within sp le nm) =
  within (λ e → n≤0⇒n≡0 (subst (share b s′ ≤_) (sp (trans (sym p) e)) l)) (≤-trans l le) (nm′ nm)
  where
    nm′ : _ → _
    nm′ (inj₁ z) = inj₁ (n≤0⇒n≡0 (subst (share b s′ ≤_) z l))
    nm′ (inj₂ e) = inj₂ (trans a e)

within-same : ∀ {b s s′ c} → Same s s′ → Within b s c → Within b s′ c
within-same {b} sm = within-sameB (same-b b sm)

within-zero : ∀ {b s c} → share b s ≡ 0 → Within b s c
within-zero {b} {s} {c} z = within (λ _ → z) (subst (_≤ proj₂ c) (sym z) z≤n) (inj₁ z)

-- A state with both counters cleared holds none of any branch's.
zero-share : ∀ b s → Flat.outer s ≡ 0 → Flat.lanes s ≡ 0 → share b s ≡ 0
zero-share outerB s o _ = o
zero-share laneB  s _ l = l
zero-share closeB s _ _ = refl

-- A branch's bump leaves the instant, the over and the other counter.
bump-at : ∀ b f s → Flat.at (bump b f s) ≡ Flat.at s
bump-at outerB f s = refl
bump-at laneB  f s = refl
bump-at closeB f s = refl

bump-sp : ∀ b f s → Flat.spent (bump b f s) ≡ Flat.spent s
bump-sp outerB f s = refl
bump-sp laneB  f s = refl
bump-sp closeB f s = refl

bump-other : ∀ b b′ f s → (b′ ≡ b → ⊥) → share b (bump b′ f s) ≡ share b s
bump-other outerB outerB f s ne = ⊥-elim (ne refl)
bump-other outerB laneB  f s ne = refl
bump-other outerB closeB f s ne = refl
bump-other laneB  outerB f s ne = refl
bump-other laneB  laneB  f s ne = ⊥-elim (ne refl)
bump-other laneB  closeB f s ne = refl
bump-other closeB _      f s ne = refl

bump-self : ∀ {b} → Counted b → ∀ f s → share b (bump b f s) ≡ f (share b s)
bump-self co f s = refl
bump-self cl f s = refl

------------------------------------------------------------------------
-- Steps that leave the counted routes alone

cut-same : ∀ {B} k n s → Same s (proj₁ (cut {B} k n s))
cut-same k n s with Flat.spent s | anyHolds (Flat.at s) (Flat.live s)
... | true  | true  = same ≤-refl ≤-refl refl refl
... | true  | false = same ≤-refl ≤-refl refl refl
... | false | true  = same ≤-refl ≤-refl refl refl
... | false | false = same ≤-refl ≤-refl refl refl

arrive-same : ∀ {B} op n s → Same s (proj₁ (arrive {B} op n s))
arrive-same (mergeᶠ (just _)) n s = same ≤-refl ≤-refl refl refl
arrive-same (mergeᶠ nothing)  n s = same ≤-refl ≤-refl refl refl
arrive-same switchᶠ           n s =
  same-trans (same z≤n ≤-refl refl refl) (cut-same (Flat.lanes s) n (record s { active = 0 ; lanes = 0 }))
arrive-same exhaustᶠ          n s = same ≤-refl ≤-refl refl refl

ended-same : ∀ {B} k n s → Same s (proj₁ (ended {B} k n s))
ended-same k n s with isZero (Flat.queue s)
... | false = same ≤-refl ≤-refl refl refl
... | true with Flat.finished s ∧ isZero (Flat.active s)
...   | true  = same ≤-refl ≤-refl refl refl
...   | false = same-trans (same ≤-refl ≤-refl refl refl) (cut-same (k + Flat.held s) n (record s { held = 0 }))

burst-same : ∀ {B} h n s → Same s (proj₁ (burstOver {B} h n s))
burst-same true  n s = same ≤-refl ≤-refl refl refl
burst-same false n s = same-trans (same ≤-refl ≤-refl refl refl) (cut-same (Flat.held s) n (record s { held = 0 }))

left-same : ∀ {B} n s → Same s (proj₁ (left {B} n s))
left-same n s with isZero (Flat.active s) ∧ isZero (Flat.queue s)
... | true  = same ≤-refl ≤-refl refl refl
... | false = same-trans (same ≤-refl z≤n refl refl) (cut-same (Flat.outer s) n (record s { outer = 0 }))

unpark-same : ∀ {B} n s → Same s (proj₁ (unpark {B} n s))
unpark-same n s with anyHolds (Flat.at s) (Flat.live s)
... | true  = same ≤-refl ≤-refl refl refl
... | false = same ≤-refl ≤-refl refl refl

overed-within : ∀ {B} b n s {c} → Within b s c → Within b (proj₁ (overed {B} n s)) c
overed-within b n s L with Flat.spent s in e
... | true  = within-zero (Within.spent L e)
... | false = within-zero (zero-share b _ refl refl)

-- A mark no route reads, from any branch.
quiet-same : ∀ {B} op b m n s → (m ≡ begin → ⊥) → (m ≡ stop → ⊥) → (m ≡ over → ⊥) → Same s (proj₁ (onMark {B} op b s m n))
quiet-same op b begin      n s nb _  _  = ⊥-elim (nb refl)
quiet-same op b stop       n s _  ns _  = ⊥-elim (ns refl)
quiet-same op b over       n s _  _  no′ = ⊥-elim (no′ refl)
quiet-same op b carry      n s _  _  _  = same ≤-refl ≤-refl refl refl
quiet-same op b outerOpen  n s _  _  _  = arrive-same op n s
quiet-same op b outerClose n s _  _  _  = same ≤-refl ≤-refl refl refl
quiet-same op b laneStart  n s _  _  _  = same ≤-refl ≤-refl refl refl
quiet-same op b laneDone   n s _  _  _  =
  same-trans (same (m∸n≤m (Flat.lanes s) (Flat.acc s)) ≤-refl refl refl)
    (ended-same (Flat.acc s ⊓ Flat.lanes s) n (record s { active = Flat.active s ∸ 1 ; lanes = Flat.lanes s ∸ Flat.acc s ; acc = 0 ; dead = true }))
quiet-same op b burstEnd   n s _  _  _  = burst-same (isZero (Flat.held s) ∨ Flat.dead s) n s
quiet-same op b outerDone  n s _  _  _  = same-trans (same ≤-refl ≤-refl refl refl) (left-same n (record s { finished = true }))
quiet-same op b subscribed n s _  _  _  = same ≤-refl ≤-refl refl refl
quiet-same op b completed  n s _  _  _  = same ≤-refl ≤-refl refl refl

quiet : ∀ {B} op b b′ m n s {c} → (m ≡ begin → ⊥) → (m ≡ stop → ⊥) → (m ≡ over → ⊥) → Within b′ s c
      → Within b′ (proj₁ (onMark {B} op b s m n)) c
quiet op b b′ m n s nb ns no′ L = within-same (quiet-same op b m n s nb ns no′) L

------------------------------------------------------------------------
-- Another branch's routes

entered-other : ∀ b b′ n s → (b′ ≡ b → ⊥) → SameB b s (entered b′ n s) ⊎ share b (entered b′ n s) ≡ 0
entered-other b b′ n s ne with does (n ≟ᵖ Flat.at s)
... | true  = inj₁ (sameB′ (≤-reflexive (bump-other b b′ suc s ne)) (bump-at b′ suc s) (bump-sp b′ suc s))
... | false = inj₂ (trans (bump-other b b′ suc (anew n s) ne) (zero-share b (anew n s) refl refl))

begun-other : ∀ {B} b b′ n s {c} → (b′ ≡ b → ⊥) → Within b s c → Within b (proj₁ (begun {B} b′ n s)) c
begun-other b b′ n s ne L with does (n ≟ᵖ Flat.at s) ∧ Flat.spent s
... | true  = L
... | false with entered-other b b′ n s ne
...   | inj₁ sm = within-sameB sm L
...   | inj₂ z  = within-zero z

stopped-other : ∀ {B} b b′ n s k → (b′ ≡ b → ⊥) → SameB b s (proj₁ (stopped {B} b′ n s k))
stopped-other b b′ n s zero    ne = sameB′ ≤-refl refl refl
stopped-other b b′ n s (suc _) ne =
  sameB′ (≤-reflexive (bump-other b b′ (_∸ 1) s ne)) (bump-at b′ (_∸ 1) s) (bump-sp b′ (_∸ 1) s)

onMark-other : ∀ {B} op b b′ m n s {c} → (b′ ≡ b → ⊥) → Within b s c → Within b (proj₁ (onMark {B} op b′ s m n)) c
onMark-other op b b′ begin      n s ne L = begun-other b b′ n s ne L
onMark-other op b b′ stop       n s ne L = within-sameB (stopped-other b b′ n s (if Flat.spent s then 0 else share b′ s) ne) L
onMark-other op b b′ over       n s ne L = overed-within b n s L
onMark-other {B} op b b′ carry      n s ne L = quiet {B} op b′ b carry n s (λ ()) (λ ()) (λ ()) L
onMark-other {B} op b b′ outerOpen  n s ne L = quiet {B} op b′ b outerOpen n s (λ ()) (λ ()) (λ ()) L
onMark-other {B} op b b′ outerClose n s ne L = quiet {B} op b′ b outerClose n s (λ ()) (λ ()) (λ ()) L
onMark-other {B} op b b′ laneStart  n s ne L = quiet {B} op b′ b laneStart n s (λ ()) (λ ()) (λ ()) L
onMark-other {B} op b b′ laneDone   n s ne L = quiet {B} op b′ b laneDone n s (λ ()) (λ ()) (λ ()) L
onMark-other {B} op b b′ burstEnd   n s ne L = quiet {B} op b′ b burstEnd n s (λ ()) (λ ()) (λ ()) L
onMark-other {B} op b b′ outerDone  n s ne L = quiet {B} op b′ b outerDone n s (λ ()) (λ ()) (λ ()) L
onMark-other {B} op b b′ subscribed n s ne L = quiet {B} op b′ b subscribed n s (λ ()) (λ ()) (λ ()) L
onMark-other {B} op b b′ completed  n s ne L = quiet {B} op b′ b completed n s (λ ()) (λ ()) (λ ()) L

------------------------------------------------------------------------
-- The branch's own routes

does-no : ∀ {n m : Pos} → does (n ≟ᵖ m) ≡ false → n ≡ m → ⊥
does-no {n} {m} e q with n ≟ᵖ m
does-no () q | yes _
... | no nq = nq q

∧-t : ∀ {a b : Bool} → a ∧ b ≡ true → b ≡ true
∧-t {true} e = e

-- The branch's begin, of the instant open.
begin-same : ∀ {B b} → Counted b → ∀ n s cm ck → Within b s (cm , ck) → n ≡ Flat.at s → Flat.spent s ≡ false
           → Within b (bump b suc s) (count (cm , ck) (instEmit {A = B} (mark begin) n))
begin-same {b = b} cb n s cm ck L na sf with does (n ≟ᵖ cm) in e
... | true  = within (λ t → ⊥-elim (not-¬ (trans (bump-sp b suc s) sf) t))
                (subst (_≤ suc ck) (sym (bump-self cb suc s)) (s≤s (Within.le L)))
                (inj₂ (trans (bump-at b suc s) (trans (sym na) (≟-true {n} {cm} e))))
... | false with Within.named L
...   | inj₂ ac = ⊥-elim (does-no {n} {cm} e (trans na ac))
...   | inj₁ z  = within (λ t → ⊥-elim (not-¬ (trans (bump-sp b suc s) sf) t))
                    (subst (_≤ 1) (sym (trans (bump-self cb suc s) (cong suc z))) ≤-refl)
                    (inj₂ (trans (bump-at b suc s) (sym na)))

-- The branch's begin, of a new instant.
begin-new : ∀ {B b} → Counted b → ∀ n s cm ck → Within b (bump b suc (anew n s)) (count (cm , ck) (instEmit {A = B} (mark begin) n))
begin-new co n s cm ck with does (n ≟ᵖ cm) in e
... | true  = within (λ ()) (s≤s z≤n) (inj₂ (≟-true {n} {cm} e))
... | false = within (λ ()) ≤-refl (inj₂ refl)
begin-new cl n s cm ck with does (n ≟ᵖ cm) in e
... | true  = within (λ ()) (s≤s z≤n) (inj₂ (≟-true {n} {cm} e))
... | false = within (λ ()) ≤-refl (inj₂ refl)

entered-own : ∀ {B b} → Counted b → ∀ n s cm ck → Within b s (cm , ck) → Flat.spent s ≡ false ⊎ does (n ≟ᵖ Flat.at s) ≡ false
            → Within b (entered b n s) (count (cm , ck) (instEmit {A = B} (mark begin) n))
entered-own {B} cb n s cm ck L sf with does (n ≟ᵖ Flat.at s) in e
... | true  = begin-same {B} cb n s cm ck L (≟-true {n} {Flat.at s} e) (fresh′ sf)
  where
    fresh′ : Flat.spent s ≡ false ⊎ true ≡ false → Flat.spent s ≡ false
    fresh′ (inj₁ f) = f
... | false = begin-new {B} cb n s cm ck

begun-own : ∀ {B b} → Counted b → ∀ n s cm ck → Within b s (cm , ck)
          → Within b (proj₁ (begun {B} b n s)) (count (cm , ck) (instEmit {A = B} (mark begin) n))
begun-own {B} cb n s cm ck L with does (n ≟ᵖ Flat.at s) ∧ Flat.spent s in e
... | true  = within-zero (Within.spent L (∧-t {does (n ≟ᵖ Flat.at s)} {Flat.spent s} e))
... | false = entered-own {B} cb n s cm ck L (split (does (n ≟ᵖ Flat.at s)) refl e)
  where
    split : ∀ d → does (n ≟ᵖ Flat.at s) ≡ d → d ∧ Flat.spent s ≡ false → Flat.spent s ≡ false ⊎ does (n ≟ᵖ Flat.at s) ≡ false
    split true  _  e′ = inj₁ e′
    split false eq _  = inj₂ eq

stopped-own : ∀ {B b} → Counted b → ∀ n s cm ck → Within b s (cm , ck)
            → Within b (proj₁ (stopped {B} b n s (if Flat.spent s then 0 else share b s))) (cm , ck ∸ 1)
stopped-own {b = b} cb n s cm ck L with Flat.spent s in e
... | true  = within-zero (Within.spent L e)
... | false with share b s in z
...   | zero  = within-zero z
...   | suc j = within (λ t → ⊥-elim (not-¬ (trans (bump-sp b (_∸ 1) s) e) t))
                  (subst (_≤ ck ∸ 1) (sym (trans (bump-self cb (_∸ 1) s) (cong (_∸ 1) z))) (∸-monoˡ-≤ 1 (subst (_≤ ck) z (Within.le L))))
                  nm
  where
    nm : share b (bump b (_∸ 1) s) ≡ 0 ⊎ Flat.at (bump b (_∸ 1) s) ≡ cm
    nm with Within.named L
    ... | inj₁ z′ with () ← trans (sym z) z′
    ... | inj₂ a  = inj₂ (trans (bump-at b (_∸ 1) s) a)

onMark-own : ∀ {B b} → Counted b → ∀ op m n s cm ck → Within b s (cm , ck)
           → Within b (proj₁ (onMark {B} op b s m n)) (count (cm , ck) (instEmit {A = B} (mark m) n))
onMark-own cb op begin      n s cm ck L = begun-own cb n s cm ck L
onMark-own cb op stop       n s cm ck L = stopped-own cb n s cm ck L
onMark-own {b = b} cb op over n s cm ck L with Flat.spent s in e
... | true  = within-zero (Within.spent L e)
... | false = within-zero (zero-share b _ refl refl)
onMark-own {B} {b} cb op carry      n s cm ck L = quiet {B} op b b carry n s (λ ()) (λ ()) (λ ()) L
onMark-own {B} {b} cb op outerOpen  n s cm ck L = quiet {B} op b b outerOpen n s (λ ()) (λ ()) (λ ()) L
onMark-own {B} {b} cb op outerClose n s cm ck L = quiet {B} op b b outerClose n s (λ ()) (λ ()) (λ ()) L
onMark-own {B} {b} cb op laneStart  n s cm ck L = quiet {B} op b b laneStart n s (λ ()) (λ ()) (λ ()) L
onMark-own {B} {b} cb op laneDone   n s cm ck L = quiet {B} op b b laneDone n s (λ ()) (λ ()) (λ ()) L
onMark-own {B} {b} cb op burstEnd   n s cm ck L = quiet {B} op b b burstEnd n s (λ ()) (λ ()) (λ ()) L
onMark-own {B} {b} cb op outerDone  n s cm ck L = quiet {B} op b b outerDone n s (λ ()) (λ ()) (λ ()) L
onMark-own {B} {b} cb op subscribed n s cm ck L = quiet {B} op b b subscribed n s (λ ()) (λ ()) (λ ()) L
onMark-own {B} {b} cb op completed  n s cm ck L = quiet {B} op b b completed n s (λ ()) (λ ()) (λ ()) L

react-own : ∀ {B b} → Counted b → ∀ op (o : Out B) v c → Within b (proj₁ o) c → Within b (proj₁ (react op o (just (inj₁ (b , v))))) (count c v)
react-own cb op o (instEmit (value _) n) c L = L
react-own cb op o (instEmit (mark m) n) (cm , ck) L = onMark-own cb op m n (proj₁ o) cm ck L

-- Another branch's row is not this one's.
other : ∀ {B} b b′ {v} → brTag {B} b (out (Tg b′ v)) ≡ nothing → b′ ≡ b → ⊥
other b .b nl refl = tagged b nl

react-other : ∀ {B} b op (o : Out B) x c → brTag {B} b (out x) ≡ nothing → Within b (proj₁ o) c → Within b (proj₁ (react op o x)) c
react-other b op o (just (inj₁ (b′ , instEmit (value _) n))) c _  L = L
react-other b op o (just (inj₁ (b′ , instEmit (mark m) n)))  c nl L = onMark-other op b b′ m n (proj₁ o) (other b b′ nl) L
react-other b op o (just (inj₂ (j , r))) c _ L =
  within-same (same-trans (same ≤-refl ≤-refl refl refl) (unpark-same root (record (proj₁ o) { live = setAt j r (Flat.live (proj₁ o)) }))) L
react-other b op o nothing c _ L = L

-- A BRANCH'S COUNTER IS WITHIN ITS COUNT, past a run that meets nothing
-- past its end.
past-within : ∀ {A B b} → Counted b → ∀ (h : IE A → IE B) → (∀ c x → count c (h x) ≡ count c x) → ∀ J op (o : Out B) c rx rs
            → (∀ r₁ {q} r₂ → rx ≡ r₁ ++ (q , end) ∷ r₂ → r₂ ≡ []) → BProj b h J rx rs
            → Within b (proj₁ o) c → Within b (proj₁ (past op o rx)) (L.foldl count c (values rs))
past-within cb h hc J op o c [] [] _ [] L = L
past-within {b = b} cb h hc J op o c (_ ∷ rx) (_ ∷ rs) tl (keep {x = x} pr) L =
  past-within cb h hc J op (react op o (just (inj₁ (b , h x)))) (count c x) rx rs (λ r₁ r₂ eq → tl (_ ∷ r₁) r₂ (cong (_ ∷_) eq)) pr
    (subst (Within b _) (hc c x) (react-own cb op o (h x) c L))
past-within {b = b} cb h hc J op o c ((q , out x) ∷ rx) rs tl (drop tg pr) L =
  past-within cb h hc J op (react op o x) c rx rs (λ r₁ r₂ eq → tl (_ ∷ r₁) r₂ (cong (_ ∷_) eq)) pr (react-other b op o x c tg L)
past-within cb h hc J op o c ((q , end) ∷ rx) rs tl (drop _ pr) L with tl [] rx refl
past-within cb h hc J op o c ((q , end) ∷ .[]) .[] tl (drop _ []) L | refl = L
past-within cb h hc J op o c ((q , skip) ∷ rx) rs tl (drop _ pr) L =
  past-within cb h hc J op o c rx rs (λ r₁ r₂ eq → tl (_ ∷ r₁) r₂ (cong (_ ∷_) eq)) pr L
past-within cb h hc J op o c ((q , pin _) ∷ rx) rs tl (drop _ pr) L =
  past-within cb h hc J op o c rx rs (λ r₁ r₂ eq → tl (_ ∷ r₁) r₂ (cong (_ ∷_) eq)) pr L

-- So the scan's counter is none, or of the name the branch last began,
-- with a route of it open.
within-of : ∀ {b s c} → Within b s c → share b s ≡ 0 ⊎ Flat.at s ≡ proj₁ c × Σ ℕ λ k → proj₂ c ≡ suc k
within-of {b} {s} {c} L with share b s in z | Within.named L
... | zero  | _       = inj₁ refl
... | suc j | inj₁ ()
... | suc j | inj₂ a  = inj₂ (a , open′ (subst (_≤ proj₂ c) z (Within.le L)))
  where
    open′ : ∀ {j k} → suc j ≤ k → Σ ℕ λ k′ → k ≡ suc k′
    open′ {k = suc k′} _ = k′ , refl

within₀ : ∀ {B} b c → Within b (proj₁ (init {B})) c
within₀ outerB c = within (λ _ → refl) z≤n (inj₁ refl)
within₀ laneB  c = within (λ _ → refl) z≤n (inj₁ refl)
within₀ closeB c = within (λ _ → refl) z≤n (inj₁ refl)
