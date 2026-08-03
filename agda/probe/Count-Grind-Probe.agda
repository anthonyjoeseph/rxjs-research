------------------------------------------------------------------
-- THE COUNT-GRIND PROBE: the four facts Phase 2 stands on, settled
-- before a single Subscribe-Face clause is touched.
--
-- Phase 1 landed `burstCount?` as the third conjunct of the subscribe
-- clique's Σ and left TWELVE `TODO-count` sites plus `TODO-len`.  Ten
-- of the original twenty-two were already free (`refl`: a one-emit,
-- zero-value envelope reduces both conjuncts at EVERY caps).  The
-- twelve that are left need exactly four things, and only ONE of them
-- was in doubt.
--
--   § 1  THE SIZE→WIDTH BRIDGE, and it is NOT one fold.  Both leaf
--     clauses that burst a stored list — `ofᵉ ts` and the cold
--     `input i` — bound their length by a SIZE (`sizeᵗˢ ts` under
--     `sizeᵉ b ≤ cSize (frameStep j c)`, `length sync` under
--     `slotsSize sl ≤ cSize c`) and owe it against a WIDTH.  At the
--     base that is `size≤widAt1` — `cSize c ≡ cSize c * 1 ≤ cSize c *
--     cSize c ^ cWid c ≡ cWid (frameStep 1 c)` — and one fold suffices.
--     AT A GENERAL LEVEL IT DOES NOT.  `cSize (frameStep j c) ≤ cWid
--     (frameStep (suc j) c)` is FALSE, and the counterexample is a
--     single row: `caps 2 0 r` at j = 1, where the size is
--     `sizeStep 2 2 = 10` and the width is `foldStep 2 (foldStep 2 0)
--     = 2 ^ 3 = 8`.  It is the ONLY violation in S ∈ [2,10), W ∈ [0,8),
--     j ∈ [0,10) — every W ≥ 1 clears it — but one row is one row.
--     THREE folds clear it outright and clear it structurally:
--     `sizeBelowWid` below, by induction on j, with the step
--     `sizeStep S s ≤ foldStep S R` for `s ≤ R`, `3 ≤ R`, which is
--     `suc (2 * R) ≤ S ^ R` — true from R = 3 (7 ≤ 8) and the reason
--     the +3 is not +1.  `3 ≤ iterFold S (j + 3) W` is then free from
--     `k≤iterFold`, which is why the bridge is stated at +3 rather
--     than at +2: at +2 the same induction needs `3 ≤ iterFold S 2 W`,
--     a fact about the SECOND iterate rather than about the count.
--
--   § 2  THE EMIT'S VALUE COUNT IS THE PAYLOAD LIST'S LENGTH, on the
--     nose.  `splitEvents`'s bookkeeping half and `retagEvents` both
--     drop every `value`, `map value vs` contributes `length vs`, and
--     the completion flag contributes nothing — so pushBurst's
--     reassembled envelope counts exactly the values `stepFrame`
--     returned, and the length half of `valsCaps?` (Phase 1's
--     upgrade) is precisely the receipt for it.
--
--   § 3  pushBurst IS LENGTH-PRESERVING and sharedPlumb IS A `map`.
--     So the emit half of every pushBurst clause is its INPUT count
--     widened, with no witness move at all — and sharedConnect, which
--     PREPENDS its own envelope, needs one fold and one only
--     (`suc W ≤ foldStep S W`, `suc≤foldStep`), so its witness moves
--     from `suc j₂` to `suc (suc j₂)`.
--
--   § 4  A LIST IS NO LONGER THAN THE SIZE THAT COUNTS IT, since
--     `sizeᵗ` and `sizeᵛ` are positive.  `length ts ≤ sizeᵗˢ ts` and
--     `length sync ≤ inputSize (cold sync async)`, and a slot is a
--     summand of the telescope (`fᵢ≤sum-tab`).
------------------------------------------------------------------
module Count-Grind-Probe where

open import Data.Bool    using (Bool; true; false; if_then_else_; _∧_)
open import Data.Nat     using (ℕ; zero; suc; _+_; _*_; _^_; _≤_; _≤ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; ≤-refl; ≤-reflexive; +-suc; +-assoc;
                                       *-mono-≤; *-monoʳ-≤; *-monoˡ-≤;
                                       *-identityˡ; *-identityʳ; *-suc;
                                       ^-monoˡ-≤; n≤1+n; +-monoʳ-≤; +-monoˡ-≤;
                                       +-mono-≤; m≤m+n; m≤n+m; +-identityʳ;
                                       ≤⇒≤ᵇ)
open import Data.List    using (List; []; _∷_; _++_; all; length; map; sum)
open import Data.Fin     using (Fin)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Rx.Prim      using (Gas; Id; Tick; InstEmit; InstEvent;
                                init; close; handoff; complete; value;
                                ObservableInput; cold; hot; Timed;
                                exhausted; _at_from_as_; subscribe)
open import Data.Sum     using (inj₁; inj₂)
open import Rx.Exp       using (Ctx; Ty; Closed; Val; Tm; sizeᵗ; sizeᵗˢ; sizeᵛ; sizeᵉ;
                                unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_; obs)
open import Rx.Evaluator using (Slots; Slot; scripted; shared; Sched; EvalSt;
                                Path; Stream; Frame;
                                slotSize; slotsSize; inputSize;
                                foldStep; iterFold; sizeStep; iterSize;
                                splitEvents; retagEvents; sharedPlumb;
                                pushBurst; stepFrame; oneShotBurst)

open import Verify-Budget-Sufficient.Subscribe-Face

------------------------------------------------------------------
-- § 1.  THE SIZE→WIDTH BRIDGE
------------------------------------------------------------------

two* : ∀ (X : ℕ) → 2 * X ≡ X + X
two* X = cong (X +_) (*-identityˡ X)

sucX≤2X : ∀ (X : ℕ) → 1 ≤ X → suc X ≤ 2 * X
sucX≤2X X h = ≤-trans (+-monoˡ-≤ X h) (≤-reflexive (sym (two* X)))

-- THE CRUX.  1 + 2R ≤ 2^R from R = 3 up — 7 ≤ 8 at the base, and the
-- step doubles the right while adding two to the left
suc2≤pow2 : ∀ (m : ℕ) → suc (2 * (3 + m)) ≤ 2 ^ (3 + m)
suc2≤pow2 zero    = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))
suc2≤pow2 (suc m) = ≤-trans step (*-monoʳ-≤ 2 (suc2≤pow2 m))
  where
  k : ℕ
  k = 3 + m
  1≤2k : 1 ≤ 2 * k
  1≤2k = s≤s z≤n
  step : suc (2 * suc k) ≤ 2 * suc (2 * k)
  step = ≤-trans (≤-reflexive (cong suc (*-suc 2 k)))
           (≤-trans (+-monoʳ-≤ 2 (sucX≤2X (2 * k) 1≤2k))
                    (≤-reflexive (sym (*-suc 2 (2 * k)))))

suc2≤pow : ∀ (S R : ℕ) → 2 ≤ S → 3 ≤ R → suc (2 * R) ≤ S ^ R
suc2≤pow S zero                  2≤S ()
suc2≤pow S (suc zero)            2≤S (s≤s ())
suc2≤pow S (suc (suc zero))      2≤S (s≤s (s≤s ()))
suc2≤pow S (suc (suc (suc m)))   2≤S _ =
  ≤-trans (suc2≤pow2 m) (^-monoˡ-≤ (3 + m) 2≤S)

-- one size step lands inside one fold step, once the width is past 3
sizeStep≤foldStep : ∀ (S s R : ℕ) → 2 ≤ S → 3 ≤ R → s ≤ R →
  sizeStep S s ≤ foldStep S R
sizeStep≤foldStep S s R 2≤S 3≤R s≤R =
  *-monoʳ-≤ S (≤-trans (s≤s (*-monoʳ-≤ 2 s≤R)) (suc2≤pow S R 2≤S 3≤R))

-- THREE FOLDS DOMINATE THE SIZE AT EVERY LEVEL
pow-pos′ : ∀ (S w : ℕ) → 1 ≤ S → 1 ≤ S ^ w
pow-pos′ S zero    h = s≤s z≤n
pow-pos′ S (suc w) h = *-mono-≤ h (pow-pos′ S w h)

sizeBelowWid : ∀ (S W j : ℕ) → 2 ≤ S → iterSize S j S ≤ iterFold S (j + 3) W
sizeBelowWid S W zero 2≤S =
  ≤-trans (≤-trans (≤-reflexive (sym (*-identityʳ S)))
                   (*-monoʳ-≤ S (pow-pos′ S W (≤-trans (s≤s z≤n) 2≤S))))
          (iterFold-mono-count S W 2≤S {1} {3} (s≤s z≤n))
sizeBelowWid S W (suc j) 2≤S =
  ≤-trans (≤-reflexive (iterSize-suc S j S))
    (≤-trans (sizeStep≤foldStep S (iterSize S j S) (iterFold S (j + 3) W)
                2≤S 3≤R (sizeBelowWid S W j 2≤S))
             (≤-reflexive (sym (iterFold-suc S (j + 3) W))))
  where
  3≤R : 3 ≤ iterFold S (j + 3) W
  3≤R = ≤-trans (m≤n+m 3 j) (k≤iterFold S (j + 3) W 2≤S)

frameStep-size≤wid : ∀ (c : Caps) (j : ℕ) → 2 ≤ Caps.cSize c →
  Caps.cSize (frameStep j c) ≤ Caps.cWid (frameStep (j + 3) c)
frameStep-size≤wid c j 2≤S = sizeBelowWid (Caps.cSize c) (Caps.cWid c) j 2≤S

-- AND AT THE BASE, ONE FOLD IS ENOUGH — the leaf keeps its 0→1 move
size≤widAt1 : ∀ (c : Caps) → 1 ≤ Caps.cSize c →
  Caps.cSize c ≤ Caps.cWid (frameStep 1 c)
size≤widAt1 c 1≤S =
  ≤-trans (≤-reflexive (sym (*-identityʳ (Caps.cSize c))))
          (*-monoʳ-≤ (Caps.cSize c) (pow-pos′ (Caps.cSize c) (Caps.cWid c) 1≤S))

-- THE ROW THAT FORCES THE +3.  One fold is NOT enough at a general
-- level: caps 2 0 1 at j = 1
_ : Caps.cSize (frameStep 1 (caps 2 0 1)) ≡ 10
_ = refl

_ : Caps.cWid (frameStep 2 (caps 2 0 1)) ≡ 8
_ = refl

_ : Caps.cWid (frameStep 3 (caps 2 0 1)) ≡ 512
_ = refl

------------------------------------------------------------------
-- § 2.  THE EMIT'S VALUE COUNT
------------------------------------------------------------------

valCountᵉ-++ : ∀ {A : Set} (xs ys : List (InstEvent A)) →
  valCountᵉ (xs ++ ys) ≡ valCountᵉ xs + valCountᵉ ys
valCountᵉ-++ []              ys = refl
valCountᵉ-++ (value _   ∷ xs) ys = cong suc (valCountᵉ-++ xs ys)
valCountᵉ-++ (init _    ∷ xs) ys = valCountᵉ-++ xs ys
valCountᵉ-++ (close _ _ ∷ xs) ys = valCountᵉ-++ xs ys
valCountᵉ-++ (handoff _ ∷ xs) ys = valCountᵉ-++ xs ys
valCountᵉ-++ (complete  ∷ xs) ys = valCountᵉ-++ xs ys

valCountᵉ-mapValue : ∀ {n} {Γ : Ctx n} {u} (vs : List (Val Γ u)) →
  valCountᵉ (map value vs) ≡ length vs
valCountᵉ-mapValue []       = refl
valCountᵉ-mapValue (v ∷ vs) = cong suc (valCountᵉ-mapValue vs)

valCountᵉ-retag : ∀ {A B : Set} (es : List (InstEvent A)) →
  valCountᵉ (retagEvents {A = A} {B = B} es) ≡ 0
valCountᵉ-retag []              = refl
valCountᵉ-retag {B = B} (value _   ∷ es) = valCountᵉ-retag {B = B} es
valCountᵉ-retag {B = B} (init _    ∷ es) = valCountᵉ-retag {B = B} es
valCountᵉ-retag {B = B} (close _ _ ∷ es) = valCountᵉ-retag {B = B} es
valCountᵉ-retag {B = B} (handoff _ ∷ es) = valCountᵉ-retag {B = B} es
valCountᵉ-retag {B = B} (complete  ∷ es) = valCountᵉ-retag {B = B} es

valCountᵉ-bk : ∀ {n} {Γ : Ctx n} {s} {A : Set} (es : List (InstEvent (Val Γ s))) →
  valCountᵉ (proj₁ (proj₂ (splitEvents {A = A} es))) ≡ 0
valCountᵉ-bk []              = refl
valCountᵉ-bk {A = A} (value _   ∷ es) = valCountᵉ-bk {A = A} es
valCountᵉ-bk {A = A} (init _    ∷ es) = valCountᵉ-bk {A = A} es
valCountᵉ-bk {A = A} (close _ _ ∷ es) = valCountᵉ-bk {A = A} es
valCountᵉ-bk {A = A} (handoff _ ∷ es) = valCountᵉ-bk {A = A} es
valCountᵉ-bk {A = A} (complete  ∷ es) = valCountᵉ-bk {A = A} es

valCountᵉ-fin : ∀ {A : Set} (b : Bool) →
  valCountᵉ {A = A} (if b then complete ∷ [] else []) ≡ 0
valCountᵉ-fin true  = refl
valCountᵉ-fin false = refl

-- THE WHOLE REASSEMBLED ENVELOPE, counted
pushEmit-count : ∀ {n} {Γ : Ctx n} {s u} {A : Set}
  (es : List (InstEvent (Val Γ s))) (evs : List (InstEvent A))
  (vs : List (Val Γ u)) (b : Bool) →
  valCountᵉ (proj₁ (proj₂ (splitEvents {A = Val Γ u} es))
              ++ retagEvents {A = A} {B = Val Γ u} evs
              ++ map value vs
              ++ (if b then complete ∷ [] else []))
    ≡ length vs
pushEmit-count {Γ = Γ} {u = u} {A = A} es evs vs b =
  trans (valCountᵉ-++ (proj₁ (proj₂ (splitEvents {A = Val Γ u} es))) _)
  (trans (cong (_+ valCountᵉ (retagEvents {A = A} {B = Val Γ u} evs
                                ++ map value vs
                                ++ (if b then complete ∷ [] else [])))
               (valCountᵉ-bk {A = Val Γ u} es))
  (trans (valCountᵉ-++ (retagEvents {A = A} {B = Val Γ u} evs) _)
  (trans (cong (_+ valCountᵉ (map value vs ++ (if b then complete ∷ [] else [])))
               (valCountᵉ-retag {A = A} {B = Val Γ u} evs))
  (trans (valCountᵉ-++ (map value vs) (if b then complete ∷ [] else []))
  (trans (cong (valCountᵉ (map value vs) +_) (valCountᵉ-fin {A = Val Γ u} b))
  (trans (+-identityʳ (valCountᵉ (map value vs)))
         (valCountᵉ-mapValue vs)))))))

-- and the one-shot leaf's envelope, counted
oneShot-count : ∀ {n} {Γ : Ctx n} {u} (vs : List (Val Γ u)) (src : ℕ) →
  valCountᵉ (init src ∷ map value vs ++ close src exhausted ∷ complete ∷ [])
    ≡ length vs
oneShot-count vs src =
  trans (valCountᵉ-++ (map value vs) (close src exhausted ∷ complete ∷ []))
  (trans (+-identityʳ (valCountᵉ (map value vs)))
         (valCountᵉ-mapValue vs))

------------------------------------------------------------------
-- § 3.  pushBurst IS LENGTH-PRESERVING; sharedPlumb IS A map
------------------------------------------------------------------

pushBurst-len : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (g : Gas) (id : Id) (now : Tick) (f : Frame Γ s u) (κ : Path Γ u t)
  (str : Stream Γ s) (sched : Sched Γ) (st : EvalSt e) →
  length (proj₁ (pushBurst g id now f κ str sched st)) ≡ length str
pushBurst-len g id now f κ [] sched st = refl
pushBurst-len {Γ = Γ} {u = u} g id now f κ (em ∷ ems) sched st =
  cong suc (pushBurst-len g id now f κ ems
              (proj₁ (proj₂ (proj₂ (proj₂ SF))))
              (proj₂ (proj₂ (proj₂ (proj₂ SF)))))
  where
  sp = splitEvents {A = Val Γ u} (InstEmit.events em)
  SF = stepFrame g id now f κ (proj₁ sp) (proj₂ (proj₂ sp)) sched st

sharedPlumb-len : ∀ {n} {Γ : Ctx n} {u} (str : Stream Γ u) →
  length (sharedPlumb str) ≡ length str
sharedPlumb-len []         = refl
sharedPlumb-len (em ∷ ems) = cong suc (sharedPlumb-len ems)

sharedPlumb-count : ∀ {n} {Γ : Ctx n} {u} (N : ℕ) (str : Stream Γ u) →
  all (λ em → valCountᵉ (InstEmit.events em) ≤ᵇ N) str ≡ true →
  all (λ em → valCountᵉ (InstEmit.events em) ≤ᵇ N) (sharedPlumb str) ≡ true
sharedPlumb-count N []         h = refl
sharedPlumb-count N (em ∷ ems) h =
  ∧-intro (proj₁ (∧-true (valCountᵉ (InstEmit.events em) ≤ᵇ N)
                         (all (λ em′ → valCountᵉ (InstEmit.events em′) ≤ᵇ N) ems) h))
          (sharedPlumb-count N ems
             (proj₂ (∧-true (valCountᵉ (InstEmit.events em) ≤ᵇ N)
                            (all (λ em′ → valCountᵉ (InstEmit.events em′) ≤ᵇ N) ems) h)))

-- ONE FOLD ABSORBS ONE PREPENDED ENVELOPE — sharedConnect's move
prepend-fits : ∀ (S W L : ℕ) → 2 ≤ S → L ≤ suc W → suc L ≤ suc (foldStep S W)
prepend-fits S W L 2≤S h = s≤s (≤-trans h (suc≤foldStep S W 2≤S))

------------------------------------------------------------------
-- § 4.  A LIST IS NO LONGER THAN THE SIZE THAT COUNTS IT
------------------------------------------------------------------

-- `len≤sizeᵗˢ` is already in Caps-Face (:1122), same statement, same proof

1≤sizeᵛ : ∀ {n} {Γ : Ctx n} (t : Ty) (v : Val Γ t) → 1 ≤ sizeᵛ t v
1≤sizeᵛ unitᵗ    _        = s≤s z≤n
1≤sizeᵛ boolᵗ    _        = s≤s z≤n
1≤sizeᵛ natᵗ     _        = s≤s z≤n
1≤sizeᵛ (s ×ᵗ t) (a , b)  = s≤s z≤n
1≤sizeᵛ (s +ᵗ t) (inj₁ a) = s≤s z≤n
1≤sizeᵛ (s +ᵗ t) (inj₂ b) = s≤s z≤n
1≤sizeᵛ (obs t)  e        = sizeᵉ-pos e

len≤sum-sizeᵛ : ∀ {n} {Γ : Ctx n} (t : Ty) (vs : List (Val Γ t)) →
  length vs ≤ sum (map (sizeᵛ t) vs)
len≤sum-sizeᵛ t []       = z≤n
len≤sum-sizeᵛ t (v ∷ vs) = +-mono-≤ (1≤sizeᵛ t v) (len≤sum-sizeᵛ t vs)

len≤inputSize : ∀ {n} {Γ : Ctx n} (t : Ty) (sync : List (Val Γ t))
  (async : List (Timed (Val Γ t))) →
  length sync ≤ inputSize {Γ = Γ} {t = t} (cold sync async)
len≤inputSize t sync async =
  ≤-trans (≤-trans (len≤sum-sizeᵛ t sync) (m≤m+n _ _)) (n≤1+n _)

slotSize≤slotsSize : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (i : Fin n) →
  slotSize (sl i) ≤ slotsSize sl
slotSize≤slotsSize sl i = fᵢ≤sum-tab (λ k → slotSize (sl k)) i
