{-# OPTIONS --guardedness #-}

-- FLATMAP'S SCAN COUNTS NO MORE LANE ROUTES THAN THE LANES SHOW
-- (`past-lanes`).  The lanes' counter is none, or at most the count of
-- the lanes' own rows, of the name they last began: a lane's begin adds
-- one to both, under a new name restarting both; a lane's stop takes one
-- from both; an over ends both; nothing else touches the lanes' rows,
-- and every other step leaves the counter, its instant and its over
-- alone, or lowers the counter, or clears it.  Past the over the counter
-- is none, so a begin the scan drops there costs nothing.
module simultaneous.FlatLanes where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; _++_)
import Data.List as L
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊓_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m∸n≤m; n≤0⇒n≡0; ∸-monoˡ-≤)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Relation.Nullary using (does; yes; no)
open import Data.Bool.Properties using (not-¬)
open import quickcheck.Tabled.Exact.Base using (≟-true)

open import Tree using (mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Position using (Pos; root; _≟ᵖ_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; EmissionSet; out; end; skip; pin)
open import denotation.Read using (Run; []; _∷_; loud)
open import denotation.Laws.Worlds using (InvAt; pinby-silent)
open import simultaneous.InstEmit using (instEmit; value; mark; begin; stop; over; outerOpen; outerClose; laneStart; carry;
  laneDone; burstEnd; outerDone; subscribed; completed)
open import simultaneous.SObs using (Flat; outerB; laneB; closeB; isZero; lone; module Elaborate)
open import simultaneous.Relations using (Met; values)
open import simultaneous.Project using (Proj; []; keep; drop)
open import simultaneous.HeldComb using (past; init)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; Routes; count; Out; Input; react; onMark; begun; entered;
  bump; stopped; overed; cut; unpark; arrive; ended; burstOver; left; anyHolds; setAt; share; anew)

-- THE LANES' BRANCH OF THE SCAN'S SOURCE: a lane's row, where the lanes
-- show it.
laneTag : ∀ {B} → Ev (Maybe (Input B)) → Maybe (Ev (IE B))
laneTag (out (just (inj₁ (laneB , x)))) = just (out x)
laneTag _                              = nothing

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

-- The lanes' counter: none past the over, within the lanes' count, and
-- of its name unless none.
record Lanes (s : Flat Pos) (c : Routes) : Set where
  constructor lanes
  field
    spent : Flat.spent s ≡ true → Flat.lanes s ≡ 0
    le    : Flat.lanes s ≤ proj₂ c
    named : Flat.lanes s ≡ 0 ⊎ Flat.at s ≡ proj₁ c

-- A step that keeps the instant and the over and lowers the lanes.
record Same (s s′ : Flat Pos) : Set where
  constructor same
  field
    lower : Flat.lanes s′ ≤ Flat.lanes s
    at≡   : Flat.at s′ ≡ Flat.at s
    sp≡   : Flat.spent s′ ≡ Flat.spent s

private
  same-trans : ∀ {s₁ s₂ s₃} → Same s₁ s₂ → Same s₂ s₃ → Same s₁ s₃
  same-trans (same l₁ a₁ p₁) (same l₂ a₂ p₂) = same (≤-trans l₂ l₁) (trans a₂ a₁) (trans p₂ p₁)

  lanes-same : ∀ {s s′ c} → Same s s′ → Lanes s c → Lanes s′ c
  lanes-same {s} {s′} (same l a p) (lanes sp le nm) =
    lanes (λ e → n≤0⇒n≡0 (subst (Flat.lanes s′ ≤_) (sp (trans (sym p) e)) l)) (≤-trans l le) (nm′ nm)
    where
      nm′ : _ → _
      nm′ (inj₁ z) = inj₁ (n≤0⇒n≡0 (subst (Flat.lanes s′ ≤_) z l))
      nm′ (inj₂ e) = inj₂ (trans a e)

  lanes-zero : ∀ {s c} → Flat.lanes s ≡ 0 → Lanes s c
  lanes-zero {s} {c} z = lanes (λ _ → z) (subst (_≤ proj₂ c) (sym z) z≤n) (inj₁ z)

  ------------------------------------------------------------------------
  -- Steps that leave the lanes alone

  cut-same : ∀ {B} k n s → Same s (proj₁ (cut {B} k n s))
  cut-same k n s with Flat.spent s | anyHolds (Flat.at s) (Flat.live s)
  ... | true  | true  = same ≤-refl refl refl
  ... | true  | false = same ≤-refl refl refl
  ... | false | true  = same ≤-refl refl refl
  ... | false | false = same ≤-refl refl refl

  arrive-same : ∀ {B} op n s → Same s (proj₁ (arrive {B} op n s))
  arrive-same (mergeᶠ (just _)) n s = same ≤-refl refl refl
  arrive-same (mergeᶠ nothing)  n s = same ≤-refl refl refl
  arrive-same switchᶠ           n s = same-trans (same z≤n refl refl) (cut-same (Flat.lanes s) n (record s { active = 0 ; lanes = 0 }))
  arrive-same exhaustᶠ          n s = same ≤-refl refl refl

  ended-same : ∀ {B} k n s → Same s (proj₁ (ended {B} k n s))
  ended-same k n s with isZero (Flat.queue s)
  ... | false = same ≤-refl refl refl
  ... | true with Flat.finished s ∧ isZero (Flat.active s)
  ...   | true  = same ≤-refl refl refl
  ...   | false = same-trans (same ≤-refl refl refl) (cut-same (k + Flat.held s) n (record s { held = 0 }))

  burst-same : ∀ {B} h n s → Same s (proj₁ (burstOver {B} h n s))
  burst-same true  n s = same ≤-refl refl refl
  burst-same false n s = same-trans (same ≤-refl refl refl) (cut-same (Flat.held s) n (record s { held = 0 }))

  left-same : ∀ {B} n s → Same s (proj₁ (left {B} n s))
  left-same n s with isZero (Flat.active s) ∧ isZero (Flat.queue s)
  ... | true  = same ≤-refl refl refl
  ... | false = same-trans (same ≤-refl refl refl) (cut-same (Flat.outer s) n (record s { outer = 0 }))

  unpark-same : ∀ {B} n s → Same s (proj₁ (unpark {B} n s))
  unpark-same n s with anyHolds (Flat.at s) (Flat.live s)
  ... | true  = same ≤-refl refl refl
  ... | false = same ≤-refl refl refl

  overed-lanes : ∀ {B} n s {c} → Lanes s c → Lanes (proj₁ (overed {B} n s)) c
  overed-lanes n s L with Flat.spent s in e
  ... | true  = lanes-zero (Lanes.spent L e)
  ... | false = lanes-zero refl

  -- A mark no route reads, from any branch.
  quiet-same : ∀ {B} op b m n s → (m ≡ begin → ⊥) → (m ≡ stop → ⊥) → (m ≡ over → ⊥) → Same s (proj₁ (onMark {B} op b s m n))
  quiet-same op b begin      n s nb _  _  = ⊥-elim (nb refl)
  quiet-same op b stop       n s _  ns _  = ⊥-elim (ns refl)
  quiet-same op b over       n s _  _  no′ = ⊥-elim (no′ refl)
  quiet-same op b carry      n s _  _  _  = same ≤-refl refl refl
  quiet-same op b outerOpen  n s _  _  _  = arrive-same op n s
  quiet-same op b outerClose n s _  _  _  = same ≤-refl refl refl
  quiet-same op b laneStart  n s _  _  _  = same ≤-refl refl refl
  quiet-same op b laneDone   n s _  _  _  =
    same-trans (same (m∸n≤m (Flat.lanes s) (Flat.acc s)) refl refl)
      (ended-same (Flat.acc s ⊓ Flat.lanes s) n (record s { active = Flat.active s ∸ 1 ; lanes = Flat.lanes s ∸ Flat.acc s ; acc = 0 ; dead = true }))
  quiet-same op b burstEnd   n s _  _  _  = burst-same (isZero (Flat.held s) ∨ Flat.dead s) n s
  quiet-same op b outerDone  n s _  _  _  = same-trans (same ≤-refl refl refl) (left-same n (record s { finished = true }))
  quiet-same op b subscribed n s _  _  _  = same ≤-refl refl refl
  quiet-same op b completed  n s _  _  _  = same ≤-refl refl refl

  ------------------------------------------------------------------------
  -- Another branch's routes

  entered-other : ∀ b n s → (b ≡ laneB → ⊥) → Same s (entered b n s) ⊎ Flat.lanes (entered b n s) ≡ 0
  entered-other laneB  n s nl = ⊥-elim (nl refl)
  entered-other outerB n s nl with does (n ≟ᵖ Flat.at s)
  ... | true  = inj₁ (same ≤-refl refl refl)
  ... | false = inj₂ refl
  entered-other closeB n s nl with does (n ≟ᵖ Flat.at s)
  ... | true  = inj₁ (same ≤-refl refl refl)
  ... | false = inj₂ refl

  begun-other : ∀ {B} b n s {c} → (b ≡ laneB → ⊥) → Lanes s c → Lanes (proj₁ (begun {B} b n s)) c
  begun-other b n s nl L with does (n ≟ᵖ Flat.at s) ∧ Flat.spent s
  ... | true  = L
  ... | false with entered-other b n s nl
  ...   | inj₁ sm = lanes-same sm L
  ...   | inj₂ z  = lanes-zero z

  stopped-other : ∀ {B} b n s k → (b ≡ laneB → ⊥) → Same s (proj₁ (stopped {B} b n s k))
  stopped-other b      n s zero    nl = same ≤-refl refl refl
  stopped-other laneB  n s (suc _) nl = ⊥-elim (nl refl)
  stopped-other outerB n s (suc _) nl = same ≤-refl refl refl
  stopped-other closeB n s (suc _) nl = same ≤-refl refl refl

  onMark-other : ∀ {B} op b m n s {c} → (b ≡ laneB → ⊥) → Lanes s c → Lanes (proj₁ (onMark {B} op b s m n)) c
  onMark-other op b begin      n s nl L = begun-other b n s nl L
  onMark-other op b stop       n s nl L = lanes-same (stopped-other b n s (if Flat.spent s then 0 else share b s) nl) L
  onMark-other op b over       n s nl L = overed-lanes n s L
  onMark-other {B} op b carry      n s nl L = lanes-same (quiet-same {B} op b carry n s (λ ()) (λ ()) (λ ())) L
  onMark-other {B} op b outerOpen  n s nl L = lanes-same (quiet-same {B} op b outerOpen n s (λ ()) (λ ()) (λ ())) L
  onMark-other {B} op b outerClose n s nl L = lanes-same (quiet-same {B} op b outerClose n s (λ ()) (λ ()) (λ ())) L
  onMark-other {B} op b laneStart  n s nl L = lanes-same (quiet-same {B} op b laneStart n s (λ ()) (λ ()) (λ ())) L
  onMark-other {B} op b laneDone   n s nl L = lanes-same (quiet-same {B} op b laneDone n s (λ ()) (λ ()) (λ ())) L
  onMark-other {B} op b burstEnd   n s nl L = lanes-same (quiet-same {B} op b burstEnd n s (λ ()) (λ ()) (λ ())) L
  onMark-other {B} op b outerDone  n s nl L = lanes-same (quiet-same {B} op b outerDone n s (λ ()) (λ ()) (λ ())) L
  onMark-other {B} op b subscribed n s nl L = lanes-same (quiet-same {B} op b subscribed n s (λ ()) (λ ()) (λ ())) L
  onMark-other {B} op b completed  n s nl L = lanes-same (quiet-same {B} op b completed n s (λ ()) (λ ()) (λ ())) L

  ------------------------------------------------------------------------
  -- The lanes' own routes

  does-no : ∀ {n m : Pos} → does (n ≟ᵖ m) ≡ false → n ≡ m → ⊥
  does-no {n} {m} e q with n ≟ᵖ m
  does-no () q | yes _
  ... | no nq = nq q

  ∧-t : ∀ {a b : Bool} → a ∧ b ≡ true → b ≡ true
  ∧-t {true} e = e

  -- A lane's begin, of the instant open.
  begin-same : ∀ {B} n s cm ck → Lanes s (cm , ck) → n ≡ Flat.at s → Flat.spent s ≡ false
             → Lanes (bump laneB suc s) (count (cm , ck) (instEmit {A = B} (mark begin) n))
  begin-same n s cm ck L na sf with does (n ≟ᵖ cm) in e
  ... | true  = lanes (λ t → ⊥-elim (not-¬ sf t)) (s≤s (Lanes.le L)) (inj₂ (trans (sym na) (≟-true {n} {cm} e)))
  ... | false with Lanes.named L
  ...   | inj₂ ac = ⊥-elim (does-no {n} {cm} e (trans na ac))
  ...   | inj₁ z  = lanes (λ t → ⊥-elim (not-¬ sf t)) (subst (λ x → suc x ≤ 1) (sym z) ≤-refl) (inj₂ (sym na))

  -- A lane's begin, of a new instant.
  begin-new : ∀ {B} n s cm ck → Lanes (bump laneB suc (anew n s)) (count (cm , ck) (instEmit {A = B} (mark begin) n))
  begin-new n s cm ck with does (n ≟ᵖ cm) in e
  ... | true  = lanes (λ ()) (s≤s z≤n) (inj₂ (≟-true {n} {cm} e))
  ... | false = lanes (λ ()) ≤-refl (inj₂ refl)

  entered-lane : ∀ {B} n s cm ck → Lanes s (cm , ck) → Flat.spent s ≡ false ⊎ does (n ≟ᵖ Flat.at s) ≡ false
               → Lanes (entered laneB n s) (count (cm , ck) (instEmit {A = B} (mark begin) n))
  entered-lane {B} n s cm ck L sf with does (n ≟ᵖ Flat.at s) in e
  ... | true  = begin-same {B} n s cm ck L (≟-true {n} {Flat.at s} e) (fresh′ sf)
    where
      fresh′ : Flat.spent s ≡ false ⊎ true ≡ false → Flat.spent s ≡ false
      fresh′ (inj₁ f) = f
  ... | false = begin-new {B} n s cm ck

  begun-lane : ∀ {B} n s cm ck → Lanes s (cm , ck) → Lanes (proj₁ (begun {B} laneB n s)) (count (cm , ck) (instEmit {A = B} (mark begin) n))
  begun-lane {B} n s cm ck L with does (n ≟ᵖ Flat.at s) ∧ Flat.spent s in e
  ... | true  = lanes-zero (Lanes.spent L (∧-t {does (n ≟ᵖ Flat.at s)} {Flat.spent s} e))
  ... | false = entered-lane {B} n s cm ck L (split (does (n ≟ᵖ Flat.at s)) refl e)
    where
      split : ∀ d → does (n ≟ᵖ Flat.at s) ≡ d → d ∧ Flat.spent s ≡ false → Flat.spent s ≡ false ⊎ does (n ≟ᵖ Flat.at s) ≡ false
      split true  _  e′ = inj₁ e′
      split false eq _  = inj₂ eq

  stopped-lane : ∀ {B} n s cm ck → Lanes s (cm , ck)
               → Lanes (proj₁ (stopped {B} laneB n s (if Flat.spent s then 0 else Flat.lanes s))) (cm , ck ∸ 1)
  stopped-lane n s cm ck L with Flat.spent s in e
  ... | true  = lanes-zero (Lanes.spent L e)
  ... | false with Flat.lanes s in z
  ...   | zero  = lanes-zero z
  ...   | suc j = lanes (λ t → ⊥-elim (not-¬ e t)) (∸-monoˡ-≤ 1 (Lanes.le L)) nm
    where
      nm : Flat.lanes s ∸ 1 ≡ 0 ⊎ Flat.at s ≡ cm
      nm with Lanes.named L
      ... | inj₁ z′ with () ← trans (sym z) z′
      ... | inj₂ a  = inj₂ a

  onMark-lane : ∀ {B} op m n s cm ck → Lanes s (cm , ck)
              → Lanes (proj₁ (onMark {B} op laneB s m n)) (count (cm , ck) (instEmit {A = B} (mark m) n))
  onMark-lane op begin      n s cm ck L = begun-lane n s cm ck L
  onMark-lane op stop       n s cm ck L = stopped-lane n s cm ck L
  onMark-lane op over       n s cm ck L with Flat.spent s in e
  ... | true  = lanes-zero (Lanes.spent L e)
  ... | false = lanes-zero refl
  onMark-lane {B} op carry      n s cm ck L = lanes-same (quiet-same {B} op laneB carry n s (λ ()) (λ ()) (λ ())) L
  onMark-lane {B} op outerOpen  n s cm ck L = lanes-same (quiet-same {B} op laneB outerOpen n s (λ ()) (λ ()) (λ ())) L
  onMark-lane {B} op outerClose n s cm ck L = lanes-same (quiet-same {B} op laneB outerClose n s (λ ()) (λ ()) (λ ())) L
  onMark-lane {B} op laneStart  n s cm ck L = lanes-same (quiet-same {B} op laneB laneStart n s (λ ()) (λ ()) (λ ())) L
  onMark-lane {B} op laneDone   n s cm ck L = lanes-same (quiet-same {B} op laneB laneDone n s (λ ()) (λ ()) (λ ())) L
  onMark-lane {B} op burstEnd   n s cm ck L = lanes-same (quiet-same {B} op laneB burstEnd n s (λ ()) (λ ()) (λ ())) L
  onMark-lane {B} op outerDone  n s cm ck L = lanes-same (quiet-same {B} op laneB outerDone n s (λ ()) (λ ()) (λ ())) L
  onMark-lane {B} op subscribed n s cm ck L = lanes-same (quiet-same {B} op laneB subscribed n s (λ ()) (λ ()) (λ ())) L
  onMark-lane {B} op completed  n s cm ck L = lanes-same (quiet-same {B} op laneB completed n s (λ ()) (λ ()) (λ ())) L

  react-lane : ∀ {B} op (o : Out B) v c → Lanes (proj₁ o) c → Lanes (proj₁ (react op o (just (inj₁ (laneB , v))))) (count c v)
  react-lane op o (instEmit (value _) n) c L = L
  react-lane op o (instEmit (mark m) n) (cm , ck) L = onMark-lane op m n (proj₁ o) cm ck L

  react-other : ∀ {B} op (o : Out B) x c → laneTag {B} (out x) ≡ nothing → Lanes (proj₁ o) c → Lanes (proj₁ (react op o x)) c
  react-other op o (just (inj₁ (laneB , _))) c () L
  react-other op o (just (inj₁ (outerB , instEmit (value _) n))) c _ L = L
  react-other op o (just (inj₁ (closeB , instEmit (value _) n))) c _ L = L
  react-other op o (just (inj₁ (outerB , instEmit (mark m) n))) c _ L = onMark-other op outerB m n (proj₁ o) (λ ()) L
  react-other op o (just (inj₁ (closeB , instEmit (mark m) n))) c _ L = onMark-other op closeB m n (proj₁ o) (λ ()) L
  react-other op o (just (inj₂ (j , r))) c _ L = lanes-same (same-trans (same ≤-refl refl refl) (unpark-same root (record (proj₁ o) { live = setAt j r (Flat.live (proj₁ o)) }))) L
  react-other op o nothing c _ L = L

-- THE LANES' COUNTER IS WITHIN THE LANES' COUNT, past a run that meets
-- nothing past its end.
past-lanes : ∀ {B} op (o : Out B) c rx rs → (∀ r₁ {q} r₂ → rx ≡ r₁ ++ (q , end) ∷ r₂ → r₂ ≡ []) → Proj laneTag rx rs
           → Lanes (proj₁ o) c → Lanes (proj₁ (past op o rx)) (L.foldl count c (values rs))
past-lanes op o c [] [] _ [] L = L
past-lanes op o c ((q , out (just (inj₁ (laneB , v)))) ∷ rx) ((_ , _) ∷ rs) tl (keep refl _ pr) L =
  past-lanes op (react op o (just (inj₁ (laneB , v)))) (count c v) rx rs (λ r₁ r₂ eq → tl (_ ∷ r₁) r₂ (cong (_ ∷_) eq)) pr
    (react-lane op o v c L)
past-lanes op o c ((q , out x) ∷ rx) rs tl (drop tg pr) L =
  past-lanes op (react op o x) c rx rs (λ r₁ r₂ eq → tl (_ ∷ r₁) r₂ (cong (_ ∷_) eq)) pr
    (react-other op o x c tg L)
past-lanes op o c ((q , out (just (inj₁ (outerB , _)))) ∷ rx) _ _ (keep () _ _) L
past-lanes op o c ((q , out (just (inj₁ (closeB , _)))) ∷ rx) _ _ (keep () _ _) L
past-lanes op o c ((q , out (just (inj₂ _))) ∷ rx) _ _ (keep () _ _) L
past-lanes op o c ((q , out nothing) ∷ rx) _ _ (keep () _ _) L
past-lanes op o c ((q , end) ∷ rx) rs tl (drop _ pr) L with tl [] rx refl
past-lanes op o c ((q , end) ∷ .[]) .[] tl (drop _ []) L | refl = L
past-lanes op o c ((q , end) ∷ rx) _ _ (keep () _ _) L
past-lanes op o c ((q , skip) ∷ rx) rs tl (drop _ pr) L =
  past-lanes op o c rx rs (λ r₁ r₂ eq → tl (_ ∷ r₁) r₂ (cong (_ ∷_) eq)) pr L
past-lanes op o c ((q , skip) ∷ rx) _ _ (keep () _ _) L
past-lanes op o c ((q , pin _) ∷ rx) rs tl (drop _ pr) L =
  past-lanes op o c rx rs (λ r₁ r₂ eq → tl (_ ∷ r₁) r₂ (cong (_ ∷_) eq)) pr L
past-lanes op o c ((q , pin _) ∷ rx) _ _ (keep () _ _) L

-- So the scan's lanes' counter is none, or of the name the lanes last
-- began, with a route of it open.
lanes-of : ∀ {s c} → Lanes s c → Flat.lanes s ≡ 0 ⊎ Flat.at s ≡ proj₁ c × Σ ℕ λ k → proj₂ c ≡ suc k
lanes-of {s} {c} L with Flat.lanes s in z | Lanes.named L
... | zero  | _       = inj₁ refl
... | suc j | inj₁ ()
... | suc j | inj₂ a  = inj₂ (a , open′ (subst (_≤ proj₂ c) z (Lanes.le L)))
  where
    open′ : ∀ {j k} → suc j ≤ k → Σ ℕ λ k′ → k ≡ suc k′
    open′ {k = suc k′} _ = k′ , refl

lanes₀ : ∀ {B} c → Lanes (proj₁ (init {B})) c
lanes₀ c = lanes-zero refl
