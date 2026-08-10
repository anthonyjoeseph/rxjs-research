-- ROADMAP: ROUTE GUARD — nest-e is the WRONG measure (Caps-Face.agda:6294 says nobody should re-derive it).
-- DELETE WHEN: The-Proof.agda is discharged — a dead route cannot be retried once the proof is done  [T7]
-- Mirrored in PROOF-STATE.md § "PROBE ROADMAP TIES".  If you change one,
-- change the other -- the duplication is deliberate cross-checking.
--
------------------------------------------------------------------
-- THE NESTING-BUDGET PROBE: may `k` be read off the SIZE CAP?
--
-- The signature pass (step 2) strengthens `subscribeE-caps`'s Σ with
-- `j + j′ ≤ sLvlK S W k j` under a NESTING HYPOTHESIS on the subscribed
-- term, and the standing ruling (Rx.Evaluator, the block above the
-- `fLvlK` family) instantiates that budget at `suc (sizeAt S J)`, read
-- at each frame's own level, on three facts:
--
--   (i)   WITHIN one delivery the recursion descends the VALUE
--         structurally — each `thru` layer subscribes payload
--         observables sitting strictly deeper in the pushed value, so
--         the k threaded downward strictly DECREASES;
--   (ii)  the k at a delivery's top is the arriving value's nesting,
--         and nesting ≤ size ≤ `sizeAt S J` by `valCaps?` at that
--         delivery's own level;
--   (iii) values grown by folds are delivered LATER, at a higher J.
--
-- The pass owes ONE non-arithmetic lemma for (ii) — `nestᵛ ≤ sizeᵛ` —
-- and this probe was written to gate it before the grind.  § 1 defines
-- the measure and PROVES that lemma (and its two syntactic halves).
-- § 2 carries the (b)-conjunct arithmetic the two *All faces wait on.
--
-- § 3 IS THE FINDING, AND IT IS NEGATIVE: (i) IS FALSE, and (iii) does
-- not save it.  A payload subscribed inside another payload's subscribe
-- need not sit anywhere inside the pushed value — a `scanᵉ` under an
-- *All MINTS one per fold, and the k-th mint nests k deep, from syntax
-- of CONSTANT nesting.  `acc` below is that family, built with the real
-- `applyFn`, and the numbers are refl-checked: `nestᵉ (acc k) ≡ k`
-- against a carrier whose own `nestᵉ` is 2 for every k.
--
-- WHY THAT BITES THE FAMILY AND NOT ONLY THE LEMMA.  `k` is INHERITED
-- everywhere and decremented at exactly one place:
--
--     fLvl′ S W J            = fLvlK S W (suc (sizeAt S J)) J
--     fLvlK  S W k J         = sIterK S W k (suc (widAt S W J)) (fLvl S W J)
--     sIterK S W k (suc m) J = sIterK S W k m (sLvlK S W k (suc J))
--     sLvlK  S W (suc k) J   = opIterK S W k (suc (sizeAt S J)) J   ← here
--     opIterK S W k (suc m) J = fIterK S W k (suc (widAt S W J₂)) J₂
--     fIterK S W k (suc m) J = fIterK S W k m (fLvlK S W k J)
--
-- ONE FRAME IS FINE, and that is worth saying, because it is where the
-- ruling was looking.  A frame's own payloads are its INPUT values,
-- which `FrameFace` bounds by `valsCaps? (frameStep j c)` at the
-- frame's ENTRY level — so `suc (sizeAt S J)` covers their nesting by
-- § 1, and `iterL` re-reads the budget at each frame of the delivery's
-- chain, so no frame inherits another frame's reading.
--
-- ONE NESTING LEVEL IN IS NOT.  Inside a payload's own subscribe the
-- budget is FIXED at `k ∸ 1` — the size cap read where that subscribe
-- BEGAN — while the frames of the payload's chain are handed values
-- bounded, by `burstCaps?` / `valsCaps?` (the only suppliers), at the
-- levels that subscribe has CLIMBED TO.  Those climb: `fLvlK` starts
-- the payload subscribes at `fLvl S W J`, and every operator and every
-- emit moves the level again.  At S = 2, W = 1, J = 0 the budget one
-- level in is 2 and the payload's chain already runs at level 7, where
-- the admissible size — hence, by § 1, the admissible nesting — is
-- 43690.  Nothing at that site reports anything smaller.  It is the
-- distinction `Entry-Caps-Refuted` killed one stratum down, moved from
-- the caps to the budget: read at an entry, spent after a climb.
--
-- AND THE ROOM IS USED RATHER THAN MERELY ALLOWED.  The mint count is
-- the FOLD count, which the WIDTH cap pays for, and `widAt` outruns
-- `sizeAt` by an exponential per level (§ 3a) — so the payload a frame
-- inside the subscribe mints is deeper than the budget for the same
-- reason the caps themselves have to climb.
--
-- WHAT IS NOT CLAIMED.  The family's arithmetic is untouched: it
-- terminates, it is monotone and inflationary, it dominates `fLvl`
-- (.Caps), and every composition-gate step (Sub-Charge-Probe § 5) still
-- goes through.  What fails is the LICENCE to instantiate k off the
-- size cap — the descent it was ruled on.  Only the design session
-- re-rules the family's shape, so this is reported, not repaired.
------------------------------------------------------------------
module Nest-Budget-Probe where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; _:=_; con)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Vec  using (Vec) renaming ([] to []ᵛ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum     using (inj₁; inj₂)
open import Data.Unit    using (⊤; tt)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)

open import Rx.Exp
open import Rx.Evaluator using (sizeAt; widAt; fCharge; fLvl; foldStep)

------------------------------------------------------------------
-- § 1  THE MEASURE, and the lemma the pass owes.
--
-- `nestᵉ e` counts the SUBSCRIBE RE-ENTRIES a subscription of `e` can
-- make: one per *All frame it installs (each subscribes a payload), one
-- per μ (Worker 35's defect 3 — a μ is charged as a nesting level, not
-- as an operator step), and none under a `deferᵉ`, which crosses a tick
-- and is subscribed in a LATER instant (the same leaf rule `syncSizeᵉ`
-- already takes).
--
-- ALONG A PATH IT ADDS, ACROSS BRANCHES IT MAXES.  A template applied
-- to a source's values concatenates the two walks, so `mapᵉ` is `+`
-- (the `⊔` reading is already false one stratum down — Rx.Hop-Depth's
-- first design point).  Duplication costs nothing, because a DEPTH is a
-- max and not a count: that is exactly where this measure parts company
-- with `hopDᵉ`, whose plug coefficients are multipliers.
------------------------------------------------------------------

mutual
  nestᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Exp Γ Δᵍ Δ Θ t → ℕ
  nestᵉ (input i)       = 0
  nestᵉ (ofᵉ ts)        = nestᵗˢ ts
  nestᵉ emptyᵉ          = 0
  nestᵉ (mapᵉ f e)      = nestᵗ f + nestᵉ e
  nestᵉ (takeᵉ c e)     = nestᵗ c + nestᵉ e
  nestᵉ (scanᵉ f z e)   = nestᵗ f + nestᵗ z + nestᵉ e
  nestᵉ (mergeAllᵉ e)   = suc (nestᵉ e)
  nestᵉ (concatAllᵉ e)  = suc (nestᵉ e)
  nestᵉ (switchAllᵉ e)  = suc (nestᵉ e)
  nestᵉ (exhaustAllᵉ e) = suc (nestᵉ e)
  nestᵉ (μᵉ e)          = suc (nestᵉ e)
  nestᵉ (varᵉ x)        = 0
  nestᵉ (deferᵉ e)      = 0

  nestᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Tm Γ Δᵍ Δ Θ t → ℕ
  nestᵗ (varᵗ x)      = 0
  nestᵗ unit̂          = 0
  nestᵗ (bool̂ _)      = 0
  nestᵗ (nat̂ _)       = 0
  nestᵗ (pairᵗ a b)   = nestᵗ a ⊔ nestᵗ b
  nestᵗ (fstᵗ p)      = nestᵗ p
  nestᵗ (sndᵗ p)      = nestᵗ p
  nestᵗ (inlᵗ a)      = nestᵗ a
  nestᵗ (inrᵗ a)      = nestᵗ a
  nestᵗ (caseᵗ s l r) = nestᵗ s + (nestᵗ l ⊔ nestᵗ r)
  nestᵗ (ifᵗ c a b)   = nestᵗ c + (nestᵗ a ⊔ nestᵗ b)
  nestᵗ (primᵗ _ a)   = nestᵗ a
  nestᵗ (strmᵗ e)     = nestᵉ e

  nestᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → List (Tm Γ Δᵍ Δ Θ t) → ℕ
  nestᵗˢ []       = 0
  nestᵗˢ (y ∷ ys) = nestᵗ y ⊔ nestᵗˢ ys

-- the value measure, beside `sizeᵛ`: an embedded observable contributes
-- its own re-entry count, a base payload none
nestᵛ : ∀ {n} {Γ : Ctx n} (t : Ty) → Val Γ t → ℕ
nestᵛ unitᵗ    _        = 0
nestᵛ boolᵗ    _        = 0
nestᵛ natᵗ     _        = 0
nestᵛ (s ×ᵗ t) (a , b)  = nestᵛ s a ⊔ nestᵛ t b
nestᵛ (s +ᵗ t) (inj₁ a) = nestᵛ s a
nestᵛ (s +ᵗ t) (inj₂ b) = nestᵛ t b
nestᵛ (obs t)  e        = nestᵉ e

------------------------------------------------------------------
-- and it is under the size, structurally — the lemma the step-2 pass
-- owes for fact (ii).  Every clause is `+-mono-≤` or `⊔-lub` against
-- the matching `sizeᵉ` / `sizeᵗ` clause, with one `n≤1+n` for the node
------------------------------------------------------------------

mutual
  nest≤sizeᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (e : Exp Γ Δᵍ Δ Θ t) →
    nestᵉ e ≤ sizeᵉ e
  nest≤sizeᵉ (input i)       = z≤n
  nest≤sizeᵉ (ofᵉ ts)        = ≤-trans (nest≤sizeᵗˢ ts) (n≤1+n (sizeᵗˢ ts))
  nest≤sizeᵉ emptyᵉ          = z≤n
  nest≤sizeᵉ (mapᵉ f e)      =
    ≤-trans (+-mono-≤ (nest≤sizeᵗ f) (nest≤sizeᵉ e)) (n≤1+n (sizeᵗ f + sizeᵉ e))
  nest≤sizeᵉ (takeᵉ c e)     =
    ≤-trans (+-mono-≤ (nest≤sizeᵗ c) (nest≤sizeᵉ e)) (n≤1+n (sizeᵗ c + sizeᵉ e))
  nest≤sizeᵉ (scanᵉ f z e)   =
    ≤-trans (+-mono-≤ (+-mono-≤ (nest≤sizeᵗ f) (nest≤sizeᵗ z)) (nest≤sizeᵉ e))
            (n≤1+n (sizeᵗ f + sizeᵗ z + sizeᵉ e))
  nest≤sizeᵉ (mergeAllᵉ e)   = s≤s (nest≤sizeᵉ e)
  nest≤sizeᵉ (concatAllᵉ e)  = s≤s (nest≤sizeᵉ e)
  nest≤sizeᵉ (switchAllᵉ e)  = s≤s (nest≤sizeᵉ e)
  nest≤sizeᵉ (exhaustAllᵉ e) = s≤s (nest≤sizeᵉ e)
  nest≤sizeᵉ (μᵉ e)          = s≤s (nest≤sizeᵉ e)
  nest≤sizeᵉ (varᵉ x)        = z≤n
  nest≤sizeᵉ (deferᵉ e)      = z≤n

  nest≤sizeᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (a : Tm Γ Δᵍ Δ Θ t) →
    nestᵗ a ≤ sizeᵗ a
  nest≤sizeᵗ (varᵗ x)      = z≤n
  nest≤sizeᵗ unit̂          = z≤n
  nest≤sizeᵗ (bool̂ _)      = z≤n
  nest≤sizeᵗ (nat̂ _)       = z≤n
  nest≤sizeᵗ (pairᵗ a b)   =
    ⊔-lub (≤-trans (nest≤sizeᵗ a) (≤-trans (m≤m+n (sizeᵗ a) (sizeᵗ b))
                                           (n≤1+n (sizeᵗ a + sizeᵗ b))))
          (≤-trans (nest≤sizeᵗ b) (≤-trans (m≤n+m (sizeᵗ b) (sizeᵗ a))
                                           (n≤1+n (sizeᵗ a + sizeᵗ b))))
  nest≤sizeᵗ (fstᵗ p)      = ≤-trans (nest≤sizeᵗ p) (n≤1+n (sizeᵗ p))
  nest≤sizeᵗ (sndᵗ p)      = ≤-trans (nest≤sizeᵗ p) (n≤1+n (sizeᵗ p))
  nest≤sizeᵗ (inlᵗ a)      = ≤-trans (nest≤sizeᵗ a) (n≤1+n (sizeᵗ a))
  nest≤sizeᵗ (inrᵗ a)      = ≤-trans (nest≤sizeᵗ a) (n≤1+n (sizeᵗ a))
  nest≤sizeᵗ (caseᵗ s l r) =
    ≤-trans (+-mono-≤ (nest≤sizeᵗ s)
              (⊔-lub (≤-trans (nest≤sizeᵗ l) (m≤m+n (sizeᵗ l) (sizeᵗ r)))
                     (≤-trans (nest≤sizeᵗ r) (m≤n+m (sizeᵗ r) (sizeᵗ l)))))
            (≤-trans (≤-reflexive (sym (+-assoc (sizeᵗ s) (sizeᵗ l) (sizeᵗ r))))
                     (n≤1+n (sizeᵗ s + sizeᵗ l + sizeᵗ r)))
  nest≤sizeᵗ (ifᵗ c a b)   =
    ≤-trans (+-mono-≤ (nest≤sizeᵗ c)
              (⊔-lub (≤-trans (nest≤sizeᵗ a) (m≤m+n (sizeᵗ a) (sizeᵗ b)))
                     (≤-trans (nest≤sizeᵗ b) (m≤n+m (sizeᵗ b) (sizeᵗ a)))))
            (≤-trans (≤-reflexive (sym (+-assoc (sizeᵗ c) (sizeᵗ a) (sizeᵗ b))))
                     (n≤1+n (sizeᵗ c + sizeᵗ a + sizeᵗ b)))
  nest≤sizeᵗ (primᵗ _ a)   = ≤-trans (nest≤sizeᵗ a) (n≤1+n (sizeᵗ a))
  nest≤sizeᵗ (strmᵗ e)     = ≤-trans (nest≤sizeᵉ e) (n≤1+n (sizeᵉ e))

  nest≤sizeᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (ts : List (Tm Γ Δᵍ Δ Θ t)) →
    nestᵗˢ ts ≤ sizeᵗˢ ts
  nest≤sizeᵗˢ []       = z≤n
  nest≤sizeᵗˢ (y ∷ ys) =
    ⊔-lub (≤-trans (nest≤sizeᵗ y) (m≤m+n (sizeᵗ y) (sizeᵗˢ ys)))
          (≤-trans (nest≤sizeᵗˢ ys) (m≤n+m (sizeᵗˢ ys) (sizeᵗ y)))

-- THE LEMMA THE PASS OWES: nesting is under the size, so `valCaps?`'s
-- size half supplies the nesting hypothesis at the level it is read at
nest≤sizeᵛ : ∀ {n} {Γ : Ctx n} (t : Ty) (v : Val Γ t) → nestᵛ t v ≤ sizeᵛ t v
nest≤sizeᵛ unitᵗ    _        = z≤n
nest≤sizeᵛ boolᵗ    _        = z≤n
nest≤sizeᵛ natᵗ     _        = z≤n
nest≤sizeᵛ (s ×ᵗ t) (a , b)  =
  ⊔-lub (≤-trans (nest≤sizeᵛ s a) (≤-trans (m≤m+n (sizeᵛ s a) (sizeᵛ t b))
                                           (n≤1+n (sizeᵛ s a + sizeᵛ t b))))
        (≤-trans (nest≤sizeᵛ t b) (≤-trans (m≤n+m (sizeᵛ t b) (sizeᵛ s a))
                                           (n≤1+n (sizeᵛ s a + sizeᵛ t b))))
nest≤sizeᵛ (s +ᵗ t) (inj₁ a) = ≤-trans (nest≤sizeᵛ s a) (n≤1+n (sizeᵛ s a))
nest≤sizeᵛ (s +ᵗ t) (inj₂ b) = ≤-trans (nest≤sizeᵛ t b) (n≤1+n (sizeᵛ t b))
nest≤sizeᵛ (obs t)  e        = nest≤sizeᵉ e

------------------------------------------------------------------
-- § 2  THE (b) CONJUNCT'S ARITHMETIC, for step 3.
--
-- `thruOuter-face` / `innerFinish-concat-face` append one burst per
-- payload: at most `suc cWid` payloads, each contributing at most
-- `suc cWid` values, so the output list is at most `suc cWid * suc
-- cWid` long — and ONE j takes cWid to `foldStep cSize cWid`
-- (frameStep-wid-suc, .Caps), which dominates a square from 2 ≤ S on.
--
-- The engine is `n * n ≤ suc (2 ^ n)`, TIGHT at n = 3 (9 against 9) and
-- slack either side.  Four base cases and then the square-under-the-
-- exponential induction, which is `sq≤pow`'s (.Caps-Face) — restated
-- here rather than imported, because importing .Caps-Face into a probe
-- costs the 18-minute module
------------------------------------------------------------------

sqStep : ∀ (t : ℕ) → suc t * suc t ≡ t * t + suc (2 * t)
sqStep = solve 1 (λ a → (con 1 :+ a) :* (con 1 :+ a)
                      := a :* a :+ (con 1 :+ con 2 :* a)) refl

linStep : ∀ (t : ℕ) → suc (2 * suc t) ≡ suc (2 * t) + 2
linStep = solve 1 (λ a → con 1 :+ con 2 :* (con 1 :+ a)
                       := (con 1 :+ con 2 :* a) :+ con 2) refl

dbl : ∀ (y : ℕ) → 2 * y ≡ y + y
dbl = solve 1 (λ a → con 2 :* a := a :+ a) refl

sq-exp : ∀ (k : ℕ) →
  ((4 + k) * (4 + k) ≤ 2 ^ (4 + k)) × (suc (2 * (4 + k)) ≤ 2 ^ (4 + k))
sq-exp zero    = ≤ᵇ⇒≤ 16 16 tt , ≤ᵇ⇒≤ 9 16 tt
sq-exp (suc k) = SQ , LIN
  where
  t   = 4 + k
  ih  = sq-exp k
  half : 2 ^ suc t ≡ 2 ^ t + 2 ^ t
  half = dbl (2 ^ t)
  two≤ : 2 ≤ 2 ^ t
  two≤ = ≤-trans (≤ᵇ⇒≤ 2 4 tt) (^-monoʳ-≤ 2 (≤ᵇ⇒≤ 2 t tt))
  SQ : suc t * suc t ≤ 2 ^ suc t
  SQ = ≤-trans (≤-reflexive (sqStep t))
               (≤-trans (+-mono-≤ (proj₁ ih) (proj₂ ih)) (≤-reflexive (sym half)))
  LIN : suc (2 * suc t) ≤ 2 ^ suc t
  LIN = ≤-trans (≤-reflexive (linStep t))
                (≤-trans (+-mono-≤ (proj₂ ih) two≤) (≤-reflexive (sym half)))

-- the four small cases the induction does not cover, and n = 3 is where
-- the inequality is TIGHT
nsq : ∀ (n : ℕ) → n * n ≤ suc (2 ^ n)
nsq zero                             = z≤n
nsq (suc zero)                       = ≤ᵇ⇒≤ 1 3 tt
nsq (suc (suc zero))                 = ≤ᵇ⇒≤ 4 5 tt
nsq (suc (suc (suc zero)))           = ≤ᵇ⇒≤ 9 9 tt
nsq (suc (suc (suc (suc k))))        =
  ≤-trans (proj₁ (sq-exp k)) (n≤1+n (2 ^ (4 + k)))

-- ONE FOLD DOMINATES THE SQUARE, which is conjunct (b) of both faces
sq-fold : ∀ (S w : ℕ) → 2 ≤ S → suc w * suc w ≤ suc (foldStep S w)
sq-fold S w 2≤S = ≤-trans (nsq (suc w)) (s≤s (^-monoˡ-≤ (suc w) 2≤S))

-- the tight rung and its neighbours, at the smallest cSize the faces
-- admit (S = 2, so the worst case)
_ : (suc 2 * suc 2 ≤ᵇ suc (foldStep 2 2)) ≡ true
_ = refl

_ : (suc 3 * suc 3 ≤ᵇ suc (foldStep 2 3)) ≡ true
_ = refl

_ : (suc 6 * suc 6 ≤ᵇ suc (foldStep 2 6)) ≡ true
_ = refl

------------------------------------------------------------------
-- § 3  THE FINDING: the descent the budget is ruled on is FALSE.
--
-- `acc` is the accumulator of a `scanᵉ` whose step wraps the running
-- value in a fresh observable — built with the REAL `applyFn`, so this
-- is the evaluator's own value, not a hand-drawn picture of one.  After
-- k folds it nests k deep
------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ᵛ

-- the step function: `λ (acc , x) → strm (mergeAll (of [ fst (acc,x) ]))`
wrapFn : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
wrapFn = strmᵗ (mergeAllᵉ (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ [])))

acc : ℕ → Val Γ₀ (obs natᵗ)
acc zero    = emptyᵉ
acc (suc k) = applyFn wrapFn (acc k , 0)

-- the CARRIER: one *All over that scan.  Its syntax does not move — the
-- payloads it subscribes are minted by the folds
carrier : Closed Γ₀ natᵗ
carrier =
  mergeAllᵉ (scanᵉ wrapFn (strmᵗ emptyᵉ)
              (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ nat̂ 4 ∷ [])))

-- THE PAYLOAD NESTING IS THE FOLD COUNT
_ : nestᵛ (obs natᵗ) (acc 0) ≡ 0
_ = refl

_ : nestᵛ (obs natᵗ) (acc 1) ≡ 1
_ = refl

_ : nestᵛ (obs natᵗ) (acc 2) ≡ 2
_ = refl

_ : nestᵛ (obs natᵗ) (acc 3) ≡ 3
_ = refl

_ : nestᵛ (obs natᵗ) (acc 5) ≡ 5
_ = refl

-- WHILE THE CARRIER'S OWN NESTING STANDS STILL at 2, for every k
_ : nestᵉ carrier ≡ 2
_ = refl

-- and the size does move with the fold count, which is what keeps the
-- CAPS side true — `nestᵛ ≤ sizeᵛ` holds at every rung (§ 1), it is the
-- DESCENT that fails, not the ceiling
_ : sizeᵛ (obs natᵗ) (acc 0) ≡ 1
_ = refl

_ : sizeᵛ (obs natᵗ) (acc 1) ≡ 8
_ = refl

_ : sizeᵛ (obs natᵗ) (acc 5) ≡ 36
_ = refl

-- THE DESCENT THAT DOES HOLD, and it is the one the ruling saw: a
-- payload's OWN payload is one shallower, so subscribing `acc k`
-- re-enters at `acc (k ∸ 1)` and the walk down a single minted value
-- terminates.  What does not hold is that the mint is inside the pushed
-- value: `carrier` pushes NOTHING of depth k, it BUILDS it
_ : nestᵛ (obs natᵗ) (acc 5) ≡ suc (nestᵛ (obs natᵗ) (acc 4))
_ = refl

------------------------------------------------------------------
-- § 3a  THE GAP, AS ARITHMETIC — the entry-charge error moved from the
-- caps to the BUDGET: read where a subscribe begins, spent after it has
-- climbed.
--
-- Read the rows at S = 2, W = 1 (the smallest cSize either face admits,
-- so the worst case) and J = 0 (a delivery's first frame).
------------------------------------------------------------------

-- THE FRAME ITSELF IS PAID FOR.  Its budget, and the ceiling its own
-- input values sit under — `valsCaps?` at the frame's ENTRY level —
-- so `nestᵛ ≤ sizeᵛ ≤ sizeAt S J < suc (sizeAt S J)` closes it
_ : suc (sizeAt 2 0) ≡ 3
_ = refl

_ : (sizeAt 2 0 ≤ᵇ suc (sizeAt 2 0)) ≡ true
_ = refl

-- ONE NESTING LEVEL IN IT IS NOT.  `sLvlK` spends one budget on the
-- payload, leaving 2, and that payload's own chain starts at `fLvl`:
_ : fLvl 2 1 0 ≡ 7
_ = refl

-- where the size — hence, by § 1, the nesting — the suppliers admit is
_ : sizeAt 2 7 ≡ 43690
_ = refl

-- 43690 against a budget of 2, and nothing at that site reports
-- anything smaller
_ : (suc (sizeAt 2 7) ≤ᵇ sizeAt 2 0) ≡ false
_ = refl

-- THE GAP OPENS AT THE FIRST STEP, not only in the limit: one level of
-- the walk already puts the admissible size above the budget
_ : sizeAt 2 1 ≡ 10
_ = refl

_ : sizeAt 2 2 ≡ 42
_ = refl

_ : (suc (sizeAt 2 1) ≤ᵇ sizeAt 2 0) ≡ false
_ = refl

-- AND THE ROOM IS USED.  § 3's mint depth is the FOLD count, and the
-- fold count is the burst length, which the WIDTH cap pays for — and
-- `widAt` outruns `sizeAt`, so a frame inside the payload's subscribe
-- may be handed more values than the size cap at its own level, and
-- mints deeper than the budget without any nesting in the syntax at all
_ : widAt 2 1 1 ≡ 4
_ = refl

_ : widAt 2 1 2 ≡ 32
_ = refl

_ : sizeAt 2 3 ≡ 170
_ = refl

_ : (suc (sizeAt 2 3) ≤ᵇ suc (widAt 2 1 3)) ≡ true
_ = refl
