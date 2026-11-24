{-# OPTIONS --guardedness #-}

-- THE LANES COUNTER HOLDS WHAT LIVE LANES BEGAN OF ONE INSTANT `N`
-- (`floor`), the converse of `simultaneous.LaneEpoch`'s bound.  Along a
-- run each lane keeps a share (`sh`), at least its own count of `N`
-- while it is live, and the shares sum within the counter wherever the
-- scan is at `N` and not spent.  A `begin` of `N` adds one to both; a
-- `stop` of `N` takes one from both, for the stopping lane holds a route
-- of `N`; a lane's `laneDone` drops its share as the scan drops the routes
-- it tells; a cut ends every lane.  Rows before the instant (`InN`) hold
-- no share, and past its first row no begin names another instant.
module simultaneous.LaneFloor where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; if_then_else_)
open import Data.Bool.Properties using (not-¬)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Properties using (++-assoc; ++-identityʳ; ∷ʳ-injective; ++-conicalʳ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (Any; here; there; any?)
open import Data.List.Relation.Unary.Any.Properties using (++⁺ˡ; ++⁺ʳ; ++⁻)
open import Data.List.Relation.Unary.All.Properties using (¬Any⇒All¬)
open import Data.List.Relation.Unary.AllPairs using () renaming ([] to []ᵖ; _∷_ to _∷ᵖ_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊓_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; ≤-refl; ≤-reflexive; n≤0⇒n≡0; ∸-monoˡ-≤; ∸-monoʳ-≤; m∸n≤m; +-suc; +-identityʳ;
  +-cancelʳ-≤; +-monoʳ-≤; m≤m+n; m≤n+m; m+n∸n≡m)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
import Data.Sum as Sum
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Relation.Nullary using (¬_; Dec; yes; no; does)

open import Tree using (FlatOp; switchᶠ; mergeᶠ; exhaustᶠ)
open import denotation.Position using (Pos; root; _≟ᵖ_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; end; skip; pin)
open import simultaneous.SObs using (Flat; Branch; laneB; outerB; closeB; lone; isZero; module Elaborate)
open import simultaneous.InstEmit using (instEmit; value; mark; begin; over; stop; outerOpen; outerClose; laneStart; laneDone;
  burstEnd; outerDone; subscribed; completed)
open import simultaneous.HeldComb using (past; init)
open import simultaneous.ScanCount using (markAct; pstep; past-snoc)
open import simultaneous.LaneCount using (kStart; kDone; kCut; kOther)
open import simultaneous.FlatLanes using (Tg; ∧-l; ∧-t; bump-at; bump-sp)
open import quickcheck.Tabled.Exact.Base using (≟-true)
open import simultaneous.LaneEpoch using (cancelʳ; set; set-self; set-other; sumK; sum-zero; sum-set; begin-count; module Lanes)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; Routes; count; Input; react; onMark; ended; begun; entered;
  stopped; overed; cut; arrive; burstOver; left; unpark; anyHolds; bump; anew; setAt)

------------------------------------------------------------------------
-- Arithmetic

private
  -- What a share sum is past one share set lower.
  lower : ∀ a b c d → a + c ≡ b + d → d ≤ c → a ≤ b
  lower a b c d eq dc = +-cancelʳ-≤ c a b (≤-trans (≤-reflexive eq) (+-monoʳ-≤ b dc))

  lower∸ : ∀ a b c → a + c ≡ b → a ≡ b ∸ c
  lower∸ a b c eq = trans (sym (m+n∸n≡m a c)) (cong (_∸ c) eq)

sum-mem : ∀ {q} K (e : Pos → ℕ) → q ∈ K → e q ≤ sumK K e
sum-mem (_ ∷ K) e (here refl) = m≤m+n _ (sumK K e)
sum-mem (q ∷ K) e (there i)   = ≤-trans (sum-mem K e i) (m≤n+m (sumK K e) (e q))

------------------------------------------------------------------------
-- The scan under one row: the lanes counter, the instant and the over

record Keep (s s′ : Flat Pos) : Set where
  constructor keep
  field
    lanes≡ : Flat.lanes s′ ≡ Flat.lanes s
    at≡    : Flat.at s′ ≡ Flat.at s
    sp≡    : Flat.spent s′ ≡ Flat.spent s

keep-trans : ∀ {s₁ s₂ s₃} → Keep s₁ s₂ → Keep s₂ s₃ → Keep s₁ s₃
keep-trans (keep l₁ a₁ p₁) (keep l₂ a₂ p₂) = keep (trans l₂ l₁) (trans a₂ a₁) (trans p₂ p₁)

cut-keep : ∀ {B} k n s → Keep s (proj₁ (cut {B} k n s))
cut-keep k n s with Flat.spent s | anyHolds (Flat.at s) (Flat.live s)
... | true  | true  = keep refl refl refl
... | true  | false = keep refl refl refl
... | false | true  = keep refl refl refl
... | false | false = keep refl refl refl

ended-keep : ∀ {B} k n s → Keep s (proj₁ (ended {B} k n s))
ended-keep k n s with isZero (Flat.queue s)
... | false = keep refl refl refl
... | true with Flat.finished s ∧ isZero (Flat.active s)
...   | true  = keep refl refl refl
...   | false = keep-trans (keep refl refl refl) (cut-keep (k + Flat.held s) n (record s { held = 0 }))

burst-keep : ∀ {B} h n s → Keep s (proj₁ (burstOver {B} h n s))
burst-keep true  n s = keep refl refl refl
burst-keep false n s = keep-trans (keep refl refl refl) (cut-keep (Flat.held s) n (record s { held = 0 }))

left-keep : ∀ {B} n s → Keep s (proj₁ (left {B} n s))
left-keep n s with isZero (Flat.active s) ∧ isZero (Flat.queue s)
... | true  = keep refl refl refl
... | false = keep-trans (keep refl refl refl) (cut-keep (Flat.outer s) n (record s { outer = 0 }))

-- A connect's move.
conn-keep : ∀ {B} op i r s (os : List (IE B)) → Keep s (proj₁ (react {B} op (s , os) (just (inj₂ (i , r)))))
conn-keep op i r s os with anyHolds (Flat.at s) (setAt i r (Flat.live s))
... | true  = keep refl refl refl
... | false = keep refl refl refl

-- A mark that moves no route the lanes counter holds.
quiet-keep : ∀ {B} op b m n s → (m ≡ begin → ⊥) → (m ≡ stop → ⊥) → (m ≡ over → ⊥) → (∀ {kd} → m ≡ laneDone kd → ⊥)
           → (markAct op m ≡ kCut → ⊥) → Keep s (proj₁ (onMark {B} op b s m n))
quiet-keep op b begin n s nb _ _ _ _ = ⊥-elim (nb refl)
quiet-keep op b stop n s _ ns _ _ _ = ⊥-elim (ns refl)
quiet-keep op b over n s _ _ no′ _ _ = ⊥-elim (no′ refl)
quiet-keep (mergeᶠ (just _)) b outerOpen n s _ _ _ _ _ = keep refl refl refl
quiet-keep (mergeᶠ nothing) b outerOpen n s _ _ _ _ _ = keep refl refl refl
quiet-keep switchᶠ b outerOpen n s _ _ _ _ nc = ⊥-elim (nc refl)
quiet-keep exhaustᶠ b outerOpen n s _ _ _ _ _ = keep refl refl refl
quiet-keep op b outerClose n s _ _ _ _ _ = keep refl refl refl
quiet-keep op b laneStart n s _ _ _ _ _ = keep refl refl refl
quiet-keep op b (laneDone kd) n s _ _ _ nd _ = ⊥-elim (nd refl)
quiet-keep op b burstEnd n s _ _ _ _ _ = burst-keep (isZero (Flat.held s) ∨ Flat.dead s) n s
quiet-keep op b outerDone n s _ _ _ _ _ = keep-trans (keep refl refl refl) (left-keep n (record s { finished = true }))
quiet-keep op b subscribed n s _ _ _ _ _ = keep refl refl refl
quiet-keep op b completed n s _ _ _ _ _ = keep refl refl refl

-- A cut keeps the instant and the over.
cut-at : ∀ {B} op b n s → markAct op outerOpen ≡ kCut
       → Flat.at (proj₁ (onMark {B} op b s outerOpen n)) ≡ Flat.at s × Flat.spent (proj₁ (onMark {B} op b s outerOpen n)) ≡ Flat.spent s
cut-at switchᶠ b n s _ = let k = cut-keep (Flat.lanes s) n (record s { active = 0 ; lanes = 0 }) in Keep.at≡ k , Keep.sp≡ k
cut-at (mergeᶠ (just _)) b n s ()
cut-at (mergeᶠ nothing) b n s ()
cut-at exhaustᶠ b n s ()

-- A `laneDone` drops the routes it tells.
done-scan : ∀ {B} op b kd n s → let s′ = proj₁ (onMark {B} op b s (laneDone kd) n) in
            Flat.lanes s′ ≡ Flat.lanes s ∸ kd × Flat.at s′ ≡ Flat.at s × Flat.spent s′ ≡ Flat.spent s
done-scan op b kd n s =
  let k = ended-keep (kd ⊓ Flat.lanes s) n (record s { active = Flat.active s ∸ 1 ; lanes = Flat.lanes s ∸ kd ; dead = true })
  in Keep.lanes≡ k , Keep.at≡ k , Keep.sp≡ k

-- A stop takes at most one from the lanes counter, none from another
-- branch's.
stop-lane : ∀ {B} n s k → let s′ = proj₁ (stopped {B} laneB n s k) in
            Flat.lanes s ∸ 1 ≤ Flat.lanes s′ × Flat.at s′ ≡ Flat.at s × Flat.spent s′ ≡ Flat.spent s
stop-lane n s zero    = m∸n≤m (Flat.lanes s) 1 , refl , refl
stop-lane n s (suc _) = ≤-refl , refl , refl

stop-other : ∀ {B} b n s k → (b ≡ laneB → ⊥) → Keep s (proj₁ (stopped {B} b n s k))
stop-other b      n s zero    _  = keep refl refl refl
stop-other outerB n s (suc _) _  = keep refl refl refl
stop-other laneB  n s (suc _) nl = ⊥-elim (nl refl)
stop-other closeB n s (suc _) _  = keep refl refl refl

-- An over spends the instant.
over-scan : ∀ {B} n s → Flat.at (proj₁ (overed {B} n s)) ≡ Flat.at s × Flat.spent (proj₁ (overed {B} n s)) ≡ true
over-scan n s with Flat.spent s in e
... | true  = refl , e
... | false = refl , refl

-- What a `begin` adds: one to its branch's counter.
bl : Branch → ℕ
bl laneB = 1
bl _     = 0

bump-suc : ∀ b (s : Flat Pos) → Flat.lanes (bump b suc s) ≡ bl b + Flat.lanes s
bump-suc outerB s = refl
bump-suc laneB  s = refl
bump-suc closeB s = refl

-- A begin a spent scan of its own instant ignores, or one that enters its
-- name live.
data Begun (b : Branch) (n : Pos) (s s′ : Flat Pos) : Set where
  ignored  : n ≡ Flat.at s → Flat.spent s ≡ true → s′ ≡ s → Begun b n s s′
  entering : Flat.at s′ ≡ n → Flat.spent s′ ≡ false
           → (n ≡ Flat.at s → Flat.spent s ≡ false × bl b + Flat.lanes s ≡ Flat.lanes s′) → bl b ≤ Flat.lanes s′
           → Begun b n s s′

entered-cls : ∀ b n s → does (n ≟ᵖ Flat.at s) ∧ Flat.spent s ≡ false → Begun b n s (entered b n s)
entered-cls b n s e with n ≟ᵖ Flat.at s
... | yes p = entering (trans (bump-at b suc s) (sym p)) (trans (bump-sp b suc s) e) (λ _ → e , sym (bump-suc b s))
                (≤-trans (m≤m+n (bl b) (Flat.lanes s)) (≤-reflexive (sym (bump-suc b s))))
... | no np = entering (bump-at b suc (anew n s)) (bump-sp b suc (anew n s)) (λ p → ⊥-elim (np p))
                (≤-reflexive (trans (sym (+-identityʳ (bl b))) (sym (bump-suc b (anew n s)))))

begun-cls : ∀ {B} b n s → Begun b n s (proj₁ (begun {B} b n s))
begun-cls b n s with does (n ≟ᵖ Flat.at s) ∧ Flat.spent s in e
... | true  = ignored (≟-true (∧-l e)) (∧-t e) refl
... | false = entered-cls b n s e

begin-name : ∀ {A} (c : Routes) n → proj₁ (count {A} c (instEmit (mark begin) n)) ≡ n
begin-name {A} c n with begin-count {A} c n
... | inj₁ (e , ce) = trans (cong proj₁ ce) e
... | inj₂ (_ , ce) = cong proj₁ ce

------------------------------------------------------------------------
-- The floor

module Floor {B : Set} (op : FlatOp) (Own : Pos → Set) (St Dn : Pos → Pos × Ev (Maybe (Input B)) → Set)
             (act : List (Pos × Ev (Maybe (Input B))) → ℕ) (LE : Pos → Pos × Ev (Maybe (Input B)) → IE B → Set) where

  open Lanes op Own St Dn act LE using (Row; module AC; Sc; OC; oc[]; oc-in; oc-out; oc-total)

  private
    nil-snoc : ∀ {A : Set} (xs : List A) x → [] ≡ xs ++ [ x ] → ⊥
    nil-snoc xs x e with ++-conicalʳ xs [ x ] (sym e)
    ... | ()

  -- A lane's count past a row, read back to the count before it.
  oc-inv : ∀ {q r c} xs x → OC q r c → r ≡ xs ++ [ x ]
         → (Σ Routes λ c₀ → OC q xs c₀ × Σ (IE B) λ v → LE q x v × c ≡ count c₀ v) ⊎ (OC q xs c × (∀ {v} → LE q x v → ⊥))
  oc-inv xs x oc[] e = ⊥-elim (nil-snoc xs x e)
  oc-inv xs x (oc-in {r} o l) e with ∷ʳ-injective r xs e
  ... | refl , refl = inj₁ (_ , o , _ , l , refl)
  oc-inv xs x (oc-out {r} o nl) e with ∷ʳ-injective r xs e
  ... | refl , refl = inj₂ (o , nl)

  cut-snoc : ∀ {xs q} x → AC.CutIn [] xs q → AC.CutIn [] (xs ++ [ x ]) q
  cut-snoc x (a , b , eq , si , cb) = a , b ++ [ x ] , trans (cong (_++ [ x ]) eq) (++-assoc a b [ x ]) , si , ++⁺ˡ cb

  module Run′ (rx : List Row) (N : Pos) (InN : Row → Set)
              (no-end : ∀ {c} → (c , end) ∈ rx → ⊥)
              (lane-of : ∀ xs k v ys → rx ≡ xs ++ (k , out (Tg laneB v)) ∷ ys → ¬ ¬ Σ Pos λ q → LE q (k , out (Tg laneB v)) v)
              (le-row : ∀ {q x v} → LE q x v → Σ Pos λ k → x ≡ (k , out (Tg laneB v)))
              (le-one : ∀ {q q′ x v v′} → LE q x v → LE q′ x v′ → q ≡ q′)
              (st-le : ∀ {q x} → St q x → Σ Pos λ n → LE q x (instEmit (mark laneStart) n))
              (le-dn : ∀ {q x kd n} → LE q x (instEmit (mark (laneDone kd)) n) → Dn q x)
              (done-lane : ∀ xs k b kd n ys → rx ≡ xs ++ (k , out (Tg b (instEmit (mark (laneDone kd)) n))) ∷ ys → b ≡ laneB)
              (stop-live : ∀ xs x ys → rx ≡ xs ++ x ∷ ys → ∀ {q n} → LE q x (instEmit (mark stop) n) → AC.Live [] xs q)
              (done-live : ∀ xs x ys → rx ≡ xs ++ x ∷ ys → ∀ {q kd n} → LE q x (instEmit (mark (laneDone kd)) n) → AC.Live [] xs q)
              (done-told : ∀ xs x ys → rx ≡ xs ++ x ∷ ys → ∀ {q kd n c} → LE q x (instEmit (mark (laneDone kd)) n) → OC q xs c
                         → proj₂ c ≡ kd)
              (start-own : ∀ xs x ys → rx ≡ xs ++ x ∷ ys → ∀ {q n c} → LE q x (instEmit (mark laneStart) n) → OC q xs c → proj₂ c ≡ 0)
              (stop-own : ∀ xs x ys → rx ≡ xs ++ x ∷ ys → InN x → ∀ {q n c} → LE q x (instEmit (mark stop) n) → OC q xs c
                        → proj₁ c ≡ N × ¬ proj₂ c ≡ 0)
              (done-own : ∀ xs x ys → rx ≡ xs ++ x ∷ ys → InN x → ∀ {q kd n c} → LE q x (instEmit (mark (laneDone kd)) n) → OC q xs c
                        → proj₂ c ≡ 0 ⊎ proj₁ c ≡ N)
              (named-in : ∀ xs k b n ys → rx ≡ xs ++ (k , out (Tg b (instEmit (mark begin) n))) ∷ ys
                        → InN (k , out (Tg b (instEmit (mark begin) n))) → n ≡ N)
              (in-named : ∀ xs k b ys → rx ≡ xs ++ (k , out (Tg b (instEmit (mark begin) N))) ∷ ys
                        → InN (k , out (Tg b (instEmit (mark begin) N))))
              (fwd-in : ∀ xs x ys → rx ≡ xs ++ x ∷ ys → Any InN xs → InN x)
              (init-in : root ≡ N → ∀ {x} → x ∈ rx → InN x) where

    OverIn : Row → Set
    OverIn x = InN x × Σ Pos λ k → Σ Branch λ b → Σ Pos λ n → x ≡ (k , out (Tg b (instEmit (mark over) n)))

    -- A live lane's own count of `N` is within its share.
    Ent : List Row → Pos → ℕ → Set
    Ent xs q v = ∀ {c} → OC q xs c → AC.Live [] xs q → proj₁ c ≡ N → proj₂ c ≤ v

    record Fl (xs : List Row) : Set where
      constructor fl
      field
        K    : List Pos
        sh   : Pos → ℕ
        uq   : Unique K
        outK : ∀ {q} → ¬ q ∈ K → sh q ≡ 0
        ent  : ∀ q → Ent xs q (sh q)
        nil  : ¬ Flat.at (Sc xs) ≡ N → sumK K sh ≡ 0
        flo  : Flat.spent (Sc xs) ≡ false → Flat.at (Sc xs) ≡ N → sumK K sh ≤ Flat.lanes (Sc xs)
        ov   : Flat.spent (Sc xs) ≡ true → Flat.at (Sc xs) ≡ N → Any OverIn xs
        atN  : Flat.at (Sc xs) ≡ N → Any InN xs ⊎ root ≡ N

    le-emit : ∀ {q k b v₀ v} → LE q (k , out (Tg b v₀)) v → v ≡ v₀ × b ≡ laneB
    le-emit l with le-row l
    ... | _ , refl = refl , refl

    -- The lane that sent a row is in the count.
    ensure : ∀ {xs} q₀ → Fl xs → Σ (Fl xs) λ F → q₀ ∈ Fl.K F
    ensure q₀ F@(fl K sh u oK en nl fo ov′ aN) with any? (q₀ ≟ᵖ_) K
    ... | yes i = F , i
    ... | no ni = fl (q₀ ∷ K) sh ((¬Any⇒All¬ K ni) ∷ᵖ u) oK′ en (λ na → trans S≡ (nl na)) (λ sp a → subst (_≤ _) (sym S≡) (fo sp a)) ov′ aN
                  , here refl
      where
        S≡ : sumK (q₀ ∷ K) sh ≡ sumK K sh
        S≡ = cong (_+ sumK K sh) (oK ni)

        oK′ : ∀ {q} → ¬ q ∈ q₀ ∷ K → sh q ≡ 0
        oK′ n′ = oK (λ i → n′ (there i))

    module At (xs : List Row) (x : Row) (ys : List Row) (eq : rx ≡ xs ++ x ∷ ys) where
      x-in : x ∈ rx
      x-in = subst (x ∈_) (sym eq) (++⁺ʳ xs (here refl))

      ne : ∀ {c} → (c , end) ∈ xs → ⊥
      ne i = no-end (subst (_ ∈_) (sym eq) (++⁺ˡ i))

      sc≡ : Sc (xs ++ [ x ]) ≡ proj₁ (pstep op (past op init xs) x)
      sc≡ = cong proj₁ (past-snoc op init xs x ne)

      inx : Fl xs → Flat.at (Sc xs) ≡ N → InN x
      inx F a = [ fwd-in xs x ys eq , (λ r → init-in r x-in) ]′ (Fl.atN F a)

      back : ∀ {q} → AC.Live [] (xs ++ [ x ]) q → (∀ {n} → LE q x (instEmit (mark laneStart) n) → ⊥) → AC.Live [] xs q
      back (o , si , nd , nc) nst with ++⁻ xs si
      ... | inj₁ si′       = o , si′ , (λ d → nd (++⁺ˡ d)) , (λ c → nc (cut-snoc x c))
      ... | inj₂ (here st) = ⊥-elim (nst (proj₂ (st-le st)))

      dead : ∀ {q kd n} → LE q x (instEmit (mark (laneDone kd)) n) → AC.Live [] (xs ++ [ x ]) q → ⊥
      dead l (_ , _ , nd , _) = nd (++⁺ʳ xs (here (le-dn l)))

      -- A share past the row: the sending lane's by `fin`, every other kept.
      ent-by : (F : Fl xs) (sh′ : Pos → ℕ)
             → (∀ {q c₀ v} → OC q xs c₀ → LE q x v → AC.Live [] (xs ++ [ x ]) q → proj₁ (count c₀ v) ≡ N → proj₂ (count c₀ v) ≤ sh′ q)
             → (∀ {q} → (∀ {v} → LE q x v → ⊥) → sh′ q ≡ Fl.sh F q)
             → ∀ q → Ent (xs ++ [ x ]) q (sh′ q)
      ent-by F sh′ fin fout q oc lv nm with oc-inv xs x oc refl
      ... | inj₁ (c₀ , oc₀ , v , l , refl) = fin oc₀ l lv nm
      ... | inj₂ (oc₀ , nl) = subst (_ ≤_) (sym (fout nl)) (Fl.ent F q oc₀ (back lv (λ l → nl l)) nm)

      -- A row that moves no share and keeps the scan's lanes, instant and over.
      keep-row : (F : Fl xs) → Keep (Sc xs) (Sc (xs ++ [ x ]))
               → (∀ {q c₀ v} → OC q xs c₀ → LE q x v → AC.Live [] (xs ++ [ x ]) q → proj₁ (count c₀ v) ≡ N → proj₂ (count c₀ v) ≤ Fl.sh F q)
               → Fl (xs ++ [ x ])
      keep-row F (keep l a p) fin = fl K sh uq outK (ent-by F sh fin (λ _ → refl))
        (λ na → nil (λ e → na (trans a e)))
        (λ sp at → subst (sumK K sh ≤_) (sym l) (flo (trans (sym p) sp) (trans (sym a) at)))
        (λ sp at → ++⁺ˡ (ov (trans (sym p) sp) (trans (sym a) at)))
        (λ at → Sum.map₁ ++⁺ˡ (atN (trans (sym a) at)))
        where open Fl F

      via : (P : Flat Pos → Set) → P (proj₁ (pstep op (past op init xs) x)) → P (Sc (xs ++ [ x ]))
      via P = subst P (sym sc≡)

      keep′ : Keep (Sc xs) (proj₁ (pstep op (past op init xs) x)) → Keep (Sc xs) (Sc (xs ++ [ x ]))
      keep′ = via (Keep (Sc xs))

      -- A row whose emit leaves a count as it is.
      fin-q : (F : Fl xs) → ∀ {k b v₀} → x ≡ (k , out (Tg b v₀)) → (∀ c → count c v₀ ≡ c) → (∀ {n} → instEmit (mark laneStart) n ≡ v₀ → ⊥)
            → ∀ {q c₀ v} → OC q xs c₀ → LE q x v → AC.Live [] (xs ++ [ x ]) q → proj₁ (count c₀ v) ≡ N → proj₂ (count c₀ v) ≤ Fl.sh F q
      fin-q F refl cq ns {q} {c₀} oc l lv nm with le-emit l
      ... | refl , refl rewrite cq c₀ = Fl.ent F q oc (back lv (λ l′ → ns (proj₁ (le-emit l′)))) nm

      -- A row no lane sent.
      fin-none : (F : Fl xs) → (∀ {q v} → LE q x v → ⊥)
               → ∀ {q c₀ v} → OC q xs c₀ → LE q x v → AC.Live [] (xs ++ [ x ]) q → proj₁ (count c₀ v) ≡ N → proj₂ (count c₀ v) ≤ Fl.sh F q
      fin-none F nl _ l = ⊥-elim (nl l)

    open At

    lower-sum : ∀ K (sh : Pos → ℕ) {q₀} v → Unique K → q₀ ∈ K → v ≤ sh q₀ → sumK K (set q₀ v sh) ≤ sumK K sh
    lower-sum K sh v u i vl = lower _ _ (sh _) v (sum-set K v sh u i) vl

    zero-of : ∀ {a b} → a ≤ b → b ≡ 0 → a ≡ 0
    zero-of l e = n≤0⇒n≡0 (≤-trans l (≤-reflexive e))

    private
      isStart : IE B → Bool
      isStart (instEmit (mark laneStart) _) = true
      isStart _                             = false

      ns-of : ∀ {n v} → isStart v ≡ false → instEmit (mark laneStart) n ≡ v → ⊥
      ns-of f e = (not-¬ refl) (trans (cong isStart e) f)

      o≢l : outerB ≡ laneB → ⊥
      o≢l ()

      c≢l : closeB ≡ laneB → ⊥
      c≢l ()

      ¬any : ∀ {P : Row → Set} → Any P [] → ⊥
      ¬any ()

      -- What lowering a share does to the sum.
      stop-ar : ∀ S S′ e₀ L L′ → S′ + e₀ ≡ S + (e₀ ∸ 1) → ¬ e₀ ≡ 0 → S ≤ L → L ∸ 1 ≤ L′ → S′ ≤ L′
      stop-ar S S′ zero    L L′ h nz _ _ = ⊥-elim (nz refl)
      stop-ar S S′ (suc e) L L′ h _ SL LL =
        ≤-trans (≤-reflexive (cong (_∸ 1) (cancelʳ e (suc S′) S (trans (sym (+-suc S′ e)) h)))) (≤-trans (∸-monoˡ-≤ 1 SL) LL)

      done-ar : ∀ S S′ e₀ kd L → S′ + e₀ ≡ S + 0 → kd ≤ e₀ → S ≤ L → S′ ≤ L ∸ kd
      done-ar S S′ e₀ kd L h ke SL =
        ≤-trans (≤-reflexive (lower∸ S′ S e₀ (trans h (+-identityʳ S)))) (≤-trans (∸-monoˡ-≤ e₀ SL) (∸-monoʳ-≤ L ke))

    ------------------------------------------------------------------------
    -- A begin

    begin-row : ∀ xs k b n ys (eq : rx ≡ xs ++ (k , out (Tg b (instEmit (mark begin) n))) ∷ ys) → Fl xs
              → ¬ ¬ Fl (xs ++ [ (k , out (Tg b (instEmit (mark begin) n))) ])
    begin-row xs k b n ys eq F with n ≟ᵖ N
    ... | no n≢ = λ κ → κ (other (subst (Begun b n (Sc xs)) (sym (sc≡ xs x ys eq)) (begun-cls b n (Sc xs))))
      where
        x : Row
        x = (k , out (Tg b (instEmit (mark begin) n)))

        nat : ¬ Flat.at (Sc xs) ≡ N
        nat a = n≢ (named-in xs k b n ys eq (inx xs x ys eq F a))

        fin : ∀ {q c₀ v} → OC q xs c₀ → LE q x v → AC.Live [] (xs ++ [ x ]) q → proj₁ (count c₀ v) ≡ N → proj₂ (count c₀ v) ≤ Fl.sh F q
        fin {c₀ = c₀} _ l _ nm with le-emit l
        ... | refl , _ = ⊥-elim (n≢ (trans (sym (begin-name {B} c₀ n)) nm))

        other : Begun b n (Sc xs) (Sc (xs ++ [ x ])) → Fl (xs ++ [ x ])
        other (ignored _ _ e₃) = keep-row xs x ys eq F (keep (cong Flat.lanes e₃) (cong Flat.at e₃) (cong Flat.spent e₃)) fin
        other (entering a′ sp′ _ _) = fl (Fl.K F) (Fl.sh F) (Fl.uq F) (Fl.outK F) (ent-by xs x ys eq F (Fl.sh F) fin (λ _ → refl))
          (λ _ → Fl.nil F nat)
          (λ _ at′ → ⊥-elim (n≢ (trans (sym a′) at′)))
          (λ sp _ → ⊥-elim ((not-¬ refl) (trans (sym sp) sp′)))
          (λ at′ → ⊥-elim (n≢ (trans (sym a′) at′)))
    ... | yes refl = by-branch b eq
      where
        grow : ∀ {b} (eq : rx ≡ xs ++ (k , out (Tg b (instEmit (mark begin) N))) ∷ ys) (F : Fl xs) (sh′ : Pos → ℕ)
             → let x = (k , out (Tg b (instEmit (mark begin) N))) in
               (∀ {q} → ¬ q ∈ Fl.K F → sh′ q ≡ 0)
             → (∀ {q c₀ v} → OC q xs c₀ → LE q x v → AC.Live [] (xs ++ [ x ]) q → proj₁ (count c₀ v) ≡ N → proj₂ (count c₀ v) ≤ sh′ q)
             → (∀ {q} → (∀ {v} → LE q x v → ⊥) → sh′ q ≡ Fl.sh F q)
             → sumK (Fl.K F) sh′ ≡ bl b + sumK (Fl.K F) (Fl.sh F)
             → Begun b N (Sc xs) (Sc (xs ++ [ x ])) → Fl (xs ++ [ x ])
        grow {b} eq F@(fl K sh u oK en nl fo ovv aN) sh′ oK′ fin fout S≡ (ignored n≡ sp e₃) =
          fl K sh′ u oK′ (ent-by xs _ ys eq F sh′ fin fout)
            (λ na → ⊥-elim (na (trans (cong Flat.at e₃) (sym n≡))))
            (λ sp′ _ → ⊥-elim ((not-¬ refl) (trans (sym sp) (trans (sym (cong Flat.spent e₃)) sp′))))
            (λ _ _ → ++⁺ˡ (ovv sp (sym n≡)))
            (λ _ → inj₁ (++⁺ʳ xs (here (in-named xs k b ys eq))))
        grow {b} eq F@(fl K sh u oK en nl fo ovv aN) sh′ oK′ fin fout S≡ (entering a′ sp′ same bl≤) =
          fl K sh′ u oK′ (ent-by xs _ ys eq F sh′ fin fout)
            (λ na → ⊥-elim (na a′))
            (λ _ _ → flo′ (Flat.at (Sc xs) ≟ᵖ N))
            (λ sp _ → ⊥-elim ((not-¬ refl) (trans (sym sp) sp′)))
            (λ _ → inj₁ (++⁺ʳ xs (here (in-named xs k b ys eq))))
          where
            flo′ : Dec (Flat.at (Sc xs) ≡ N) → sumK K sh′ ≤ Flat.lanes (Sc (xs ++ [ (k , out (Tg b (instEmit (mark begin) N))) ]))
            flo′ (yes a) = let (spf , ln) = same (sym a) in
              subst (_≤ _) (sym S≡) (≤-trans (+-monoʳ-≤ (bl b) (fo spf a)) (≤-reflexive ln))
            flo′ (no na) = subst (_≤ _) (sym (trans S≡ (trans (cong (bl b +_) (nl na)) (+-identityʳ (bl b))))) bl≤

        bc : ∀ {b} (eq : rx ≡ xs ++ (k , out (Tg b (instEmit (mark begin) N))) ∷ ys)
           → Begun b N (Sc xs) (Sc (xs ++ [ (k , out (Tg b (instEmit (mark begin) N))) ]))
        bc {b} eq = subst (Begun b N (Sc xs)) (sym (sc≡ xs _ ys eq)) (begun-cls b N (Sc xs))

        quiet : ∀ {b} → (b ≡ laneB → ⊥) → bl b ≡ 0 → (eq : rx ≡ xs ++ (k , out (Tg b (instEmit (mark begin) N))) ∷ ys)
              → Fl (xs ++ [ (k , out (Tg b (instEmit (mark begin) N))) ])
        quiet {b} nb z eq = grow eq F (Fl.sh F) (Fl.outK F) (λ _ l → ⊥-elim (nb (proj₂ (le-emit l)))) (λ _ → refl)
          (sym (cong (_+ sumK (Fl.K F) (Fl.sh F)) z)) (bc eq)

        by-branch : ∀ b (eq : rx ≡ xs ++ (k , out (Tg b (instEmit (mark begin) N))) ∷ ys)
                  → ¬ ¬ Fl (xs ++ [ (k , out (Tg b (instEmit (mark begin) N))) ])
        by-branch outerB eq = λ κ → κ (quiet o≢l refl eq)
        by-branch closeB eq = λ κ → κ (quiet c≢l refl eq)
        by-branch laneB eq = λ κ → lane-of xs k _ ys eq λ (q₀ , l₀) → κ (lane q₀ l₀ (ensure q₀ F))
          where
            x : Row
            x = (k , out (Tg laneB (instEmit (mark begin) N)))

            lane : ∀ q₀ → LE q₀ x (instEmit (mark begin) N) → Σ (Fl xs) (λ F′ → q₀ ∈ Fl.K F′) → Fl (xs ++ [ x ])
            lane q₀ l₀ (F′@(fl K sh u oK en _ _ _ _) , i₀) = grow eq F′ sh′ oK′ fin fout S≡ (bc eq)
              where
                sh′ : Pos → ℕ
                sh′ = set q₀ (suc (sh q₀)) sh

                oK′ : ∀ {q} → ¬ q ∈ K → sh′ q ≡ 0
                oK′ {q} ni = trans (set-other (suc (sh q₀)) sh (λ e → ni (subst (_∈ K) (sym e) i₀))) (oK ni)

                fin : ∀ {q c₀ v} → OC q xs c₀ → LE q x v → AC.Live [] (xs ++ [ x ]) q → proj₁ (count c₀ v) ≡ N → proj₂ (count c₀ v) ≤ sh′ q
                fin {q} {c₀} oc l lv nm with le-emit l | le-one l l₀
                ... | refl , _ | refl rewrite set-self q₀ (suc (sh q₀)) sh with begin-count {B} c₀ N
                ...   | inj₁ (e , ce) rewrite ce = s≤s (en q₀ oc (back xs x ys eq lv (λ l′ → ns-of refl (proj₁ (le-emit l′)))) e)
                ...   | inj₂ (_ , ce) rewrite ce = s≤s z≤n

                fout : ∀ {q} → (∀ {v} → LE q x v → ⊥) → sh′ q ≡ sh q
                fout nl′ = set-other (suc (sh q₀)) sh (λ e → nl′ (subst (λ z → LE z x _) (sym e) l₀))

                S≡ : sumK K sh′ ≡ suc (sumK K sh)
                S≡ = cancelʳ (sh q₀) (sumK K sh′) (suc (sumK K sh)) (trans (sum-set K (suc (sh q₀)) sh u i₀) (+-suc (sumK K sh) (sh q₀)))

    ------------------------------------------------------------------------
    -- A stop

    stop-row : ∀ xs k b n ys (eq : rx ≡ xs ++ (k , out (Tg b (instEmit (mark stop) n))) ∷ ys) → Fl xs
             → ¬ ¬ Fl (xs ++ [ (k , out (Tg b (instEmit (mark stop) n))) ])
    stop-row xs k outerB n ys eq F κ =
      κ (keep-row xs x ys eq F (keep′ xs x ys eq (stop-other outerB n (Sc xs) (if Flat.spent (Sc xs) then 0 else Flat.outer (Sc xs)) o≢l))
         (fin-none xs x ys eq F (λ l → o≢l (proj₂ (le-emit l)))))
      where x = (k , out (Tg outerB (instEmit (mark stop) n)))
    stop-row xs k closeB n ys eq F κ =
      κ (keep-row xs x ys eq F (keep′ xs x ys eq (stop-other closeB n (Sc xs) (if Flat.spent (Sc xs) then 0 else 0) c≢l))
         (fin-none xs x ys eq F (λ l → c≢l (proj₂ (le-emit l)))))
      where x = (k , out (Tg closeB (instEmit (mark stop) n)))
    stop-row xs k laneB n ys eq F κ =
      lane-of xs k _ ys eq λ (q₀ , l₀) → oc-total q₀ xs λ (c₀ , oc₀) → κ (lane q₀ l₀ c₀ oc₀ (ensure q₀ F))
      where
        x : Row
        x = (k , out (Tg laneB (instEmit (mark stop) n)))

        sl = stop-lane {B} n (Sc xs) (if Flat.spent (Sc xs) then 0 else Flat.lanes (Sc xs))

        lanes≤ : Flat.lanes (Sc xs) ∸ 1 ≤ Flat.lanes (Sc (xs ++ [ x ]))
        lanes≤ = via xs x ys eq (λ t → Flat.lanes (Sc xs) ∸ 1 ≤ Flat.lanes t) (proj₁ sl)

        at≡ : Flat.at (Sc (xs ++ [ x ])) ≡ Flat.at (Sc xs)
        at≡ = via xs x ys eq (λ t → Flat.at t ≡ Flat.at (Sc xs)) (proj₁ (proj₂ sl))

        sp≡ : Flat.spent (Sc (xs ++ [ x ])) ≡ Flat.spent (Sc xs)
        sp≡ = via xs x ys eq (λ t → Flat.spent t ≡ Flat.spent (Sc xs)) (proj₂ (proj₂ sl))

        lane : ∀ q₀ → LE q₀ x (instEmit (mark stop) n) → ∀ c₀ → OC q₀ xs c₀ → Σ (Fl xs) (λ F′ → q₀ ∈ Fl.K F′) → Fl (xs ++ [ x ])
        lane q₀ l₀ c₀ oc₀ (F′@(fl K sh u oK en nl fo ovv aN) , i₀) =
          fl K sh′ u oK′ (ent-by xs x ys eq F′ sh′ fin fout)
            (λ na → zero-of S′≤ (nl (λ a → na (trans at≡ a))))
            (λ sp a → flo′ (trans (sym sp≡) sp) (trans (sym at≡) a))
            (λ sp a → ++⁺ˡ (ovv (trans (sym sp≡) sp) (trans (sym at≡) a)))
            (λ a → Sum.map₁ ++⁺ˡ (aN (trans (sym at≡) a)))
          where
            sh′ : Pos → ℕ
            sh′ = set q₀ (sh q₀ ∸ 1) sh

            oK′ : ∀ {q} → ¬ q ∈ K → sh′ q ≡ 0
            oK′ {q} ni = trans (set-other (sh q₀ ∸ 1) sh (λ e → ni (subst (_∈ K) (sym e) i₀))) (oK ni)

            fin : ∀ {q c v} → OC q xs c → LE q x v → AC.Live [] (xs ++ [ x ]) q → proj₁ (count c v) ≡ N → proj₂ (count c v) ≤ sh′ q
            fin {q} {c} oc l lv nm with le-emit l | le-one l l₀
            ... | refl , _ | refl rewrite set-self q₀ (sh q₀ ∸ 1) sh =
              ∸-monoˡ-≤ 1 (en q₀ oc (back xs x ys eq lv (λ l′ → ns-of refl (proj₁ (le-emit l′)))) nm)

            fout : ∀ {q} → (∀ {v} → LE q x v → ⊥) → sh′ q ≡ sh q
            fout nl′ = set-other (sh q₀ ∸ 1) sh (λ e → nl′ (subst (λ z → LE z x _) (sym e) l₀))

            S′≤ : sumK K sh′ ≤ sumK K sh
            S′≤ = lower-sum K sh (sh q₀ ∸ 1) u i₀ (m∸n≤m (sh q₀) 1)

            flo′ : Flat.spent (Sc xs) ≡ false → Flat.at (Sc xs) ≡ N → sumK K sh′ ≤ Flat.lanes (Sc (xs ++ [ x ]))
            flo′ sp a =
              let (cN , nz) = stop-own xs x ys eq (inx xs x ys eq F′ a) l₀ oc₀
                  own = en q₀ oc₀ (stop-live xs x ys eq l₀) cN
              in stop-ar (sumK K sh) (sumK K sh′) (sh q₀) _ _ (sum-set K (sh q₀ ∸ 1) sh u i₀) (λ z → nz (zero-of own z)) (fo sp a) lanes≤

    ------------------------------------------------------------------------
    -- An over

    over-row : ∀ xs k b n ys (eq : rx ≡ xs ++ (k , out (Tg b (instEmit (mark over) n))) ∷ ys) → Fl xs
             → Fl (xs ++ [ (k , out (Tg b (instEmit (mark over) n))) ])
    over-row xs k b n ys eq F@(fl K sh u oK en nl fo ovv aN) =
      fl K sh u oK (ent-by xs x ys eq F sh fin (λ _ → refl))
        (λ na → nl (λ a → na (trans at≡ a)))
        (λ sp _ → ⊥-elim ((not-¬ refl) (trans (sym sp≡) sp)))
        (λ _ a → ++⁺ʳ xs (here (inx xs x ys eq F (trans (sym at≡) a) , k , b , n , refl)))
        (λ a → Sum.map₁ ++⁺ˡ (aN (trans (sym at≡) a)))
      where
        x : Row
        x = (k , out (Tg b (instEmit (mark over) n)))

        os = over-scan {B} n (Sc xs)

        at≡ : Flat.at (Sc (xs ++ [ x ])) ≡ Flat.at (Sc xs)
        at≡ = via xs x ys eq (λ t → Flat.at t ≡ Flat.at (Sc xs)) (proj₁ os)

        sp≡ : Flat.spent (Sc (xs ++ [ x ])) ≡ true
        sp≡ = via xs x ys eq (λ t → Flat.spent t ≡ true) (proj₂ os)

        fin : ∀ {q c v} → OC q xs c → LE q x v → AC.Live [] (xs ++ [ x ]) q → proj₁ (count c v) ≡ N → proj₂ (count c v) ≤ sh q
        fin _ l _ _ with le-emit l
        ... | refl , _ = z≤n

    ------------------------------------------------------------------------
    -- A lane's end

    done-row : ∀ xs k b kd n ys (eq : rx ≡ xs ++ (k , out (Tg b (instEmit (mark (laneDone kd)) n))) ∷ ys) → Fl xs
             → ¬ ¬ Fl (xs ++ [ (k , out (Tg b (instEmit (mark (laneDone kd)) n))) ])
    done-row xs k b kd n ys eq F with done-lane xs k b kd n ys eq
    ... | refl = λ κ → lane-of xs k _ ys eq λ (q₀ , l₀) → oc-total q₀ xs λ (c₀ , oc₀) → κ (lane q₀ l₀ c₀ oc₀ (ensure q₀ F))
      where
        x : Row
        x = (k , out (Tg laneB (instEmit (mark (laneDone kd)) n)))

        ds = done-scan {B} op laneB kd n (Sc xs)

        lanes≡ : Flat.lanes (Sc (xs ++ [ x ])) ≡ Flat.lanes (Sc xs) ∸ kd
        lanes≡ = via xs x ys eq (λ t → Flat.lanes t ≡ Flat.lanes (Sc xs) ∸ kd) (proj₁ ds)

        at≡ : Flat.at (Sc (xs ++ [ x ])) ≡ Flat.at (Sc xs)
        at≡ = via xs x ys eq (λ t → Flat.at t ≡ Flat.at (Sc xs)) (proj₁ (proj₂ ds))

        sp≡ : Flat.spent (Sc (xs ++ [ x ])) ≡ Flat.spent (Sc xs)
        sp≡ = via xs x ys eq (λ t → Flat.spent t ≡ Flat.spent (Sc xs)) (proj₂ (proj₂ ds))

        lane : ∀ q₀ → LE q₀ x (instEmit (mark (laneDone kd)) n) → ∀ c₀ → OC q₀ xs c₀ → Σ (Fl xs) (λ F′ → q₀ ∈ Fl.K F′) → Fl (xs ++ [ x ])
        lane q₀ l₀ c₀ oc₀ (F′@(fl K sh u oK en nl fo ovv aN) , i₀) =
          fl K sh′ u oK′ (ent-by xs x ys eq F′ sh′ fin fout)
            (λ na → zero-of S′≤ (nl (λ a → na (trans at≡ a))))
            (λ sp a → flo′ (trans (sym sp≡) sp) (trans (sym at≡) a))
            (λ sp a → ++⁺ˡ (ovv (trans (sym sp≡) sp) (trans (sym at≡) a)))
            (λ a → Sum.map₁ ++⁺ˡ (aN (trans (sym at≡) a)))
          where
            sh′ : Pos → ℕ
            sh′ = set q₀ 0 sh

            oK′ : ∀ {q} → ¬ q ∈ K → sh′ q ≡ 0
            oK′ {q} ni = trans (set-other 0 sh (λ e → ni (subst (_∈ K) (sym e) i₀))) (oK ni)

            fin : ∀ {q c v} → OC q xs c → LE q x v → AC.Live [] (xs ++ [ x ]) q → proj₁ (count c v) ≡ N → proj₂ (count c v) ≤ sh′ q
            fin _ l lv _ with le-emit l
            ... | refl , _ = ⊥-elim (dead xs x ys eq l lv)

            fout : ∀ {q} → (∀ {v} → LE q x v → ⊥) → sh′ q ≡ sh q
            fout nl′ = set-other 0 sh (λ e → nl′ (subst (λ z → LE z x _) (sym e) l₀))

            S′≤ : sumK K sh′ ≤ sumK K sh
            S′≤ = lower-sum K sh 0 u i₀ z≤n

            flo′ : Flat.spent (Sc xs) ≡ false → Flat.at (Sc xs) ≡ N → sumK K sh′ ≤ Flat.lanes (Sc (xs ++ [ x ]))
            flo′ sp a = subst (sumK K sh′ ≤_) (sym lanes≡)
              (done-ar (sumK K sh) (sumK K sh′) (sh q₀) kd _ (sum-set K 0 sh u i₀) kd≤ (fo sp a))
              where
                told : proj₂ c₀ ≡ kd
                told = done-told xs x ys eq l₀ oc₀

                kd≤ : kd ≤ sh q₀
                kd≤ = [ (λ z → ≤-trans (≤-reflexive (trans (sym told) z)) z≤n)
                      , (λ cN → subst (_≤ sh q₀) told (en q₀ oc₀ (done-live xs x ys eq l₀) cN)) ]′
                      (done-own xs x ys eq (inx xs x ys eq F′ a) l₀ oc₀)

    ------------------------------------------------------------------------
    -- An outer's value: a switch's cut

    open-row : ∀ xs k b n ys (eq : rx ≡ xs ++ (k , out (Tg b (instEmit (mark outerOpen) n))) ∷ ys) → Fl xs
             → Fl (xs ++ [ (k , out (Tg b (instEmit (mark outerOpen) n))) ])
    open-row xs k b n ys eq F = by (markAct op outerOpen) refl
      where
        x : Row
        x = (k , out (Tg b (instEmit (mark outerOpen) n)))

        quiet : (markAct op outerOpen ≡ kCut → ⊥) → Fl (xs ++ [ x ])
        quiet nc = keep-row xs x ys eq F (keep′ xs x ys eq (quiet-keep op b outerOpen n (Sc xs) (λ ()) (λ ()) (λ ()) (λ ()) nc))
                     (fin-q xs x ys eq F refl (λ _ → refl) (ns-of refl))

        cut-row : markAct op outerOpen ≡ kCut → Fl (xs ++ [ x ])
        cut-row mk = fl K (λ _ → 0) uq (λ _ → refl) (λ q oc lv _ → ⊥-elim (no-live lv)) (λ _ → sum-zero K)
                       (λ _ _ → subst (_≤ Flat.lanes (Sc (xs ++ [ x ]))) (sym (sum-zero K)) z≤n)
                       (λ sp a → ++⁺ˡ (ov (trans (sym sp≡) sp) (trans (sym at≡) a)))
                       (λ a → Sum.map₁ ++⁺ˡ (atN (trans (sym at≡) a)))
          where
            open Fl F

            ca = cut-at {B} op b n (Sc xs) mk

            at≡ : Flat.at (Sc (xs ++ [ x ])) ≡ Flat.at (Sc xs)
            at≡ = via xs x ys eq (λ t → Flat.at t ≡ Flat.at (Sc xs)) (proj₁ ca)

            sp≡ : Flat.spent (Sc (xs ++ [ x ])) ≡ Flat.spent (Sc xs)
            sp≡ = via xs x ys eq (λ t → Flat.spent t ≡ Flat.spent (Sc xs)) (proj₂ ca)

            no-live : ∀ {q} → AC.Live [] (xs ++ [ x ]) q → ⊥
            no-live (_ , si , _ , nc) with ++⁻ xs si
            ... | inj₁ si′       = nc (xs , [ x ] , refl , si′ , here mk)
            ... | inj₂ (here st) = ns-of refl (proj₁ (le-emit (proj₂ (st-le st))))

        by : ∀ κ → markAct op outerOpen ≡ κ → Fl (xs ++ [ x ])
        by kCut   mk = cut-row mk
        by kStart mk = quiet (λ e → kc (trans (sym mk) e)) where kc : kStart ≡ kCut → ⊥ ; kc ()
        by kDone  mk = quiet (λ e → kc (trans (sym mk) e)) where kc : kDone ≡ kCut → ⊥ ; kc ()
        by kOther mk = quiet (λ e → kc (trans (sym mk) e)) where kc : kOther ≡ kCut → ⊥ ; kc ()

    ------------------------------------------------------------------------
    -- Every other row

    quiet-row : ∀ xs k b m n ys (eq : rx ≡ xs ++ (k , out (Tg b (instEmit (mark m) n))) ∷ ys) (F : Fl xs)
              → (m ≡ begin → ⊥) → (m ≡ stop → ⊥) → (m ≡ over → ⊥) → (∀ {kd} → m ≡ laneDone kd → ⊥) → (markAct op m ≡ kCut → ⊥)
              → (∀ c → count {B} c (instEmit (mark m) n) ≡ c) → isStart (instEmit (mark m) n) ≡ false
              → Fl (xs ++ [ (k , out (Tg b (instEmit (mark m) n))) ])
    quiet-row xs k b m n ys eq F nb ns no′ nd nc cq st =
      keep-row xs _ ys eq F (keep′ xs _ ys eq (quiet-keep op b m n (Sc xs) nb ns no′ nd nc)) (fin-q xs _ ys eq F refl cq (ns-of st))

    start-row : ∀ xs k b n ys (eq : rx ≡ xs ++ (k , out (Tg b (instEmit (mark laneStart) n))) ∷ ys) (F : Fl xs)
              → Fl (xs ++ [ (k , out (Tg b (instEmit (mark laneStart) n))) ])
    start-row xs k b n ys eq F = keep-row xs (k , out (Tg b (instEmit (mark laneStart) n))) ys eq F (keep′ xs (k , out (Tg b (instEmit (mark laneStart) n))) ys eq (quiet-keep {B} op b laneStart n (Sc xs) (λ ()) (λ ()) (λ ()) (λ ()) (λ ()))) fin
      where
        fin : ∀ {q c v} → OC q xs c → LE q (k , out (Tg b (instEmit (mark laneStart) n))) v
            → AC.Live [] (xs ++ [ (k , out (Tg b (instEmit (mark laneStart) n))) ]) q → proj₁ (count c v) ≡ N
            → proj₂ (count c v) ≤ Fl.sh F q
        fin oc l _ _ with le-emit l
        ... | refl , _ = ≤-trans (≤-reflexive (start-own xs _ ys eq l oc)) z≤n

    no-le : ∀ {q x v} → (∀ {k v′} → x ≡ (k , out (Tg laneB v′)) → ⊥) → LE q x v → ⊥
    no-le nt l = nt (proj₂ (le-row l))

    step : ∀ xs x ys → rx ≡ xs ++ x ∷ ys → Fl xs → ¬ ¬ Fl (xs ++ [ x ])
    step xs (k , out (just (inj₁ (b , instEmit (mark begin) n)))) ys eq F = begin-row xs k b n ys eq F
    step xs (k , out (just (inj₁ (b , instEmit (mark stop) n)))) ys eq F = stop-row xs k b n ys eq F
    step xs (k , out (just (inj₁ (b , instEmit (mark over) n)))) ys eq F κ = κ (over-row xs k b n ys eq F)
    step xs (k , out (just (inj₁ (b , instEmit (mark (laneDone kd)) n)))) ys eq F = done-row xs k b kd n ys eq F
    step xs (k , out (just (inj₁ (b , instEmit (mark outerOpen) n)))) ys eq F κ = κ (open-row xs k b n ys eq F)
    step xs (k , out (just (inj₁ (b , instEmit (mark laneStart) n)))) ys eq F κ = κ (start-row xs k b n ys eq F)
    step xs (k , out (just (inj₁ (b , instEmit (mark outerClose) n)))) ys eq F κ =
      κ (quiet-row xs k b outerClose n ys eq F (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ _ → refl) refl)
    step xs (k , out (just (inj₁ (b , instEmit (mark burstEnd) n)))) ys eq F κ =
      κ (quiet-row xs k b burstEnd n ys eq F (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ _ → refl) refl)
    step xs (k , out (just (inj₁ (b , instEmit (mark outerDone) n)))) ys eq F κ =
      κ (quiet-row xs k b outerDone n ys eq F (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ _ → refl) refl)
    step xs (k , out (just (inj₁ (b , instEmit (mark subscribed) n)))) ys eq F κ =
      κ (quiet-row xs k b subscribed n ys eq F (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ _ → refl) refl)
    step xs (k , out (just (inj₁ (b , instEmit (mark completed) n)))) ys eq F κ =
      κ (quiet-row xs k b completed n ys eq F (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ _ → refl) refl)
    step xs (k , out (just (inj₁ (b , instEmit (value w) n)))) ys eq F κ =
      κ (keep-row xs _ ys eq F (keep′ xs _ ys eq (keep refl refl refl)) (fin-q xs _ ys eq F refl (λ _ → refl) (ns-of refl)))
    step xs (k , out (just (inj₂ (i , r)))) ys eq F κ =
      κ (keep-row xs x ys eq F (keep′ xs x ys eq (conn-keep op i r (Sc xs) (proj₂ (past op init xs)))) (fin-none xs x ys eq F (no-le (λ ()))))
      where x = (k , out (just (inj₂ (i , r))))
    step xs (k , out nothing) ys eq F κ =
      κ (keep-row xs _ ys eq F (keep′ xs _ ys eq (keep refl refl refl)) (fin-none xs _ ys eq F (no-le (λ ()))))
    step xs (k , skip) ys eq F κ =
      κ (keep-row xs _ ys eq F (keep′ xs _ ys eq (keep refl refl refl)) (fin-none xs _ ys eq F (no-le (λ ()))))
    step xs (k , pin p) ys eq F κ =
      κ (keep-row xs _ ys eq F (keep′ xs _ ys eq (keep refl refl refl)) (fin-none xs _ ys eq F (no-le (λ ()))))
    step xs (k , end) ys eq F κ = no-end (x-in xs _ ys eq)

    fl₀ : Fl []
    fl₀ = fl [] (λ _ → 0) []ᵖ (λ _ → refl) (λ q oc lv nm → ⊥-elim (¬any (proj₁ (proj₂ lv)))) (λ _ → refl) (λ _ _ → z≤n) (λ ()) inj₂

    go : ∀ xs ys → rx ≡ xs ++ ys → Fl xs → ¬ ¬ Fl rx
    go xs []       e F κ = κ (subst Fl (sym (trans e (++-identityʳ xs))) F)
    go xs (y ∷ ys) e F κ = step xs y ys e F λ F′ → go (xs ++ [ y ]) ys (trans e (sym (++-assoc xs [ y ] ys))) F′ κ

    -- A live lane holding a route of `N` finds the scan at `N`.
    floor-at : ∀ {Q c} → AC.Live [] rx Q → OC Q rx c → proj₁ c ≡ N → ¬ proj₂ c ≡ 0 → ¬ ¬ Flat.at (Sc rx) ≡ N
    floor-at {Q} {c} lv oc nm nz na = go [] rx refl fl₀ fin
      where
        fin : Fl rx → ⊥
        fin (fl K sh u oK en nl fo ovv aN) with any? (Q ≟ᵖ_) K
        ... | no ni = nz (zero-of (en Q oc lv nm) (oK ni))
        ... | yes i = nz (zero-of (en Q oc lv nm) (zero-of (sum-mem K sh i) (nl na)))

    -- A live lane holding a route of `N` holds it in the lanes counter,
    -- unless the instant is over.
    floor : ∀ {Q c} → AC.Live [] rx Q → OC Q rx c → proj₁ c ≡ N → ¬ proj₂ c ≡ 0
          → (Any OverIn rx → Flat.spent (Sc rx) ≡ false) → ¬ Flat.lanes (Sc rx) ≡ 0
    floor {Q} {c} lv oc nm nz hov z = go [] rx refl fl₀ fin
      where
        fin : Fl rx → ⊥
        fin (fl K sh u oK en nl fo ovv aN) = pick (any? (Q ≟ᵖ_) K) (Flat.at (Sc rx) ≟ᵖ N) (Flat.spent (Sc rx)) refl
          where
            own : proj₂ c ≤ sh Q
            own = en Q oc lv nm

            S≢ : Q ∈ K → ¬ sumK K sh ≡ 0
            S≢ i e = nz (zero-of own (zero-of (sum-mem K sh i) e))

            pick : Dec (Q ∈ K) → Dec (Flat.at (Sc rx) ≡ N) → ∀ b → Flat.spent (Sc rx) ≡ b → ⊥
            pick (no ni)  _        _     _ = nz (zero-of own (oK ni))
            pick (yes i)  (no na)  _     _ = S≢ i (nl na)
            pick (yes i)  (yes a)  true  e = (not-¬ refl) (trans (sym e) (hov (ovv e a)))
            pick (yes i)  (yes a)  false e = S≢ i (zero-of (fo e a) z)
