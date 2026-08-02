------------------------------------------------------------------
-- THE VISITED-SET SLOT DESCENT, AS LANDED: the entry width ceiling IS
-- linear in the program, now that the width measures no longer re-enter
-- a shared slot.
--
-- WHAT THIS IS AGAINST, and it is now HISTORY rather than a live form.
-- The retired descent reached a shared slot by SPENDING FUEL —
-- `outWᵉ (suc j) sl (input i) | shared d = outWᵉ j sl d` — and every
-- consumer instantiated that fuel at `n`, the slot count.  So a def in a
-- slot CYCLE was re-entered once per level and exponentiated again each
-- time: a def of k wraps in a 2-cycle padded with n−2 one-node dummy
-- slots demanded k·(n−1) stories off sz = 19 + 28k + n — a PRODUCT, with
-- slope k in sz, unbounded.  At k = 8, n = 100 that was 792 stories
-- against the 689 that `3 + 2 * sz` allows.  §4 re-runs that row.
--
-- WHAT REPLACED IT, in `Rx.Frame-Width` and measured here.  The descent
-- carries the set of shared slots already entered; `input i` at an
-- unvisited `shared d` descends into `d` with `i` marked, and A REVISIT
-- CONTRIBUTES ZERO.
--
-- WHY ZERO IS THE FAITHFUL NUMBER, and not a convenient one.  A share is
-- reached by a CONNECT, and the README's share-connect-no-replay theorem
-- says a late join gets no replay of the connect burst.  So the second
-- arrival at slot i inside one connect cascade delivers NOTHING in that
-- frame: it hands back the existing subject.  What the slot does emit
-- LATER flows through registrations, and the cascade side — cReg, the
-- delivery bound — is what counts those.  The static measure must not
-- count them twice.
--
-- WHAT IS MEASURED HERE, all refl or structural:
--
--   §2  THE COLLAPSE.  The 4-slot cycle `insC`, whose retired fuel
--       measure was above 2 ^ (2 ^ (2 ^ (2 ^ 256))) at fuel 4, sits at a
--       FIXED POINT of 258 · 2 ^ 521 from fuel 2 up — two stories, one
--       per shared slot, and more fuel buys nothing.  The fuel axis is
--       gone as a source of growth; `j` survives for TERMINATION only.
--
--       AND WHAT THE COLLECTORS COST.  A def read with an EMPTY visited
--       set goes round the cycle ONE MORE TIME than any connect does,
--       because its own slot is not yet marked.  Marking removes the
--       turn — but `capsOK?` reads a STORED value at the entry form and
--       cannot supply a marked one, so the collectors STAY at `[]` and
--       the base pays that one turn.  One, not `n`: still linear.
--
--   §3  AGREEMENT OFF THE CYCLE.  The visited set can only fire on a
--       slot appearing TWICE on one descent path, and that IS a cycle in
--       the slot graph.  So on an ACYCLIC telescope neither the fuel
--       above the depth nor an OFF-PATH mark changes the number, refl —
--       which is why nothing acyclic re-pins, and why the soundness gate
--       is confined to cyclic telescopes.  No State-Blowup or Frame-Work
--       row has one.
--
--   §4  THE BASE HEIGHT, gated.  The (k, n) row that refuted the linear
--       price is re-run: the demand is now 2k (one entry per SHARED slot
--       on a path, and a 2-cycle has two), not k·(n−1), and 2k sits
--       under 3 + 2·sz with the whole telescope to spare.  Stated
--       generally as `visited-height-fits`, and — because the collectors
--       stay unmarked — as `visited-height-fits-unmarked`, which pays
--       the extra turn and is still linear.
--
-- A NOTE ON WHAT IS NOT WRITTEN HERE, paid for twice by an OOM: `_≤ᵇ_`
-- and `_≤_` on ℕ recurse UNARILY, so neither a `≤ᵇ` bracket nor a
-- `≤-refl` may be pointed at these numbers — 258 · 2 ^ 521 is 10 ^ 159
-- constructors.  Magnitudes are pinned as CLOSED-FORM EQUALITIES, which
-- the builtin nat compares in binary, and the two-sided facts are `≡`
-- rather than `≤`.
--
-- Standalone, so src/Main.agda never reaches it.  Fast.
------------------------------------------------------------------
module Visited-Width-Probe where

open import Data.Bool using (Bool; true; false)
open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _^_; _⊔_; _≤_; _≤ᵇ_;
                             z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-trans; ≤-reflexive; *-monoʳ-≤; +-mono-≤; +-monoʳ-≤;
         m≤n+m; m≤m+n; ⊔-lub)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.List using (List; []; _∷_)
open import Data.Vec  using (Vec) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Fin  using (Fin) renaming (zero to fz; suc to fs)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Rx.Prim using (hot)
open import Rx.Exp
open import Rx.Evaluator using (Slots; Slot; scripted; shared; slotsSize)
open import Rx.Frame-Width using (outWⱽ; innWⱽ; dWⱽ; outWᵉ; entryCeil; slotsCeil)

------------------------------------------------------------------
-- §1  THE TELESCOPE WITH THE CYCLE.
--
-- `insC` is a 4-slot telescope: two SHARED slots whose defs reference
-- each other, plus two one-node scripted dummies whose only job is to
-- raise the slot count (and hence, under the retired form, the fuel).
-- One `wrap` is a scanᵉ whose step function mentions the accumulator
-- twice, unwrapped by a mergeAllᵉ — Frame-Work-Probe's deepScan shape —
-- and it buys ONE tower story for FOURTEEN syntax nodes.
------------------------------------------------------------------

Γ₄ : Ctx 4
Γ₄ = natᵗ ∷ᵛ natᵗ ∷ᵛ natᵗ ∷ᵛ natᵗ ∷ᵛ []ᵛ

accV : ∀ {Θ} → Tm Γ₄ [] [] (obs natᵗ ×ᵗ natᵗ ∷ Θ) (obs natᵗ)
accV = fstᵗ (varᵗ (here refl))

seedO : ∀ {Θ} → Tm Γ₄ [] [] Θ (obs natᵗ)
seedO = strmᵗ (ofᵉ (nat̂ 7 ∷ []))

W2 : Fn Γ₄ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
W2 = strmᵗ (mergeAllᵉ (ofᵉ (accV ∷ accV ∷ [])))

base0 : Closed Γ₄ natᵗ
base0 = ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ [])

mix : Closed Γ₄ natᵗ → Closed Γ₄ natᵗ
mix e = mergeAllᵉ (ofᵉ (strmᵗ e ∷ strmᵗ base0 ∷ []))

wrap : Closed Γ₄ natᵗ → Closed Γ₄ natᵗ
wrap e = mergeAllᵉ (scanᵉ W2 seedO e)

d0 d1 : Closed Γ₄ natᵗ
d0 = wrap (mix (input (fs fz)))
d1 = wrap (mix (input fz))

insC : Slots Γ₄
insC fz                = shared d0
insC (fs fz)           = shared d1
insC (fs (fs fz))      = scripted (hot [])
insC (fs (fs (fs fz))) = scripted (hot [])

in0 in1 : Closed Γ₄ natᵗ
in0 = input fz
in1 = input (fs fz)

_ : slotsSize insC ≡ 50
_ = refl

-- ONE WRAP IS FOURTEEN NODES, which is the rate §4's arithmetic prices
_ : sizeᵉ (mix in1) ≡ 10
_ = refl

_ : sizeᵉ (wrap (mix in1)) ≡ 24
_ = refl

_ : sizeᵉ (wrap (wrap (mix in1))) ≡ 38
_ = refl

------------------------------------------------------------------
-- §2  THE COLLAPSE.
------------------------------------------------------------------

-- ONE LEVEL, the number the retired fuel form also reported: at fuel 1
-- nothing has cycled yet, so the two descents cannot differ
_ : outWⱽ 1 [] insC in0 ≡ 256
_ = refl

-- THE FIXED POINT, refl and with no numeral spelled: more fuel buys
-- NOTHING once the cycle closes.  Under the retired descent each of
-- these steps was one more tower story
_ : outWⱽ 3 [] insC in0 ≡ outWⱽ 2 [] insC in0
_ = refl

_ : outWⱽ 4 [] insC in0 ≡ outWⱽ 2 [] insC in0
_ = refl

_ : outWⱽ 20 [] insC in0 ≡ outWⱽ 2 [] insC in0
_ = refl

_ : outWⱽ 20 [] insC in1 ≡ outWⱽ 2 [] insC in1
_ = refl

-- AND WHAT THE COLLECTORS COST — measured, because the ruling turns on
-- it.  `slotPW` / `slotIW` read the DEF: `slotPW j sl (shared d) =
-- pWᵉ j sl d`, i.e. at an EMPTY visited set.  The def's own slot is then
-- not yet marked, so the descent comes back round to it ONE MORE TIME
-- than a connect does — on `insC` a third `wrap` layer, i.e. a THIRD
-- tower story, `2 ^ (258 · 2 ^ 521)`, which is why it is not computed
-- here.
--
-- MARKING FIRST REMOVES THAT TURN, and the def then agrees with the
-- reference on the nose:
_ : outWⱽ 3 (fz ∷ []) insC d0 ≡ outWⱽ 20 (fz ∷ []) insC d0
_ = refl

_ : outWⱽ 20 (fz ∷ []) insC d0 ≡ outWⱽ 4 [] insC in0
_ = refl

-- BUT THE COLLECTORS STAY UNMARKED ANYWAY, and this is the ruling the
-- port ran into rather than a preference.  `capsOK?` bounds a STORED
-- value, and a stored value carries no record of which connect put it
-- there — its width is read at the ENTRY form.  So `subscribeE`'s shared
-- branch needs the def at `[]`, and a slot side condition stated at
-- `i ∷ []` cannot supply it: the two differ by exactly the turn above,
-- and no monotonicity closes a gap in that direction.
--
-- The cost of staying at `[]` is ONE turn, not `n`: the descent marks
-- slot i on the way back in, so a path meets at most one shared def
-- twice and none three times.  The base height is therefore
-- `Σkᵢ + max kᵢ` rather than `Σkᵢ` — still LINEAR, which is all the
-- ceiling needs (§4's `visited-height-fits-unmarked`).
--
-- WHAT THE PORT PAID FOR IT is visited-set ANTITONICITY beside the fuel
-- monotonicity Caps-Face already had — one induction over both axes,
-- `q ≤ q′` together with `Sub vs′ vs`, since `Sub [] _` is vacuous and
-- that is the instance `slotsCaps?-slotWid` uses.

-- THE MAGNITUDE, in CLOSED FORM rather than as a wall of digits — and as
-- an EQUALITY rather than a `≤ᵇ` bracket, because `_≤ᵇ_` and `_≤_` on ℕ
-- recurse unarily and a 159-digit numeral is not something to count down
-- from (the container dies; measured).  Two shared slots of one wrap
-- apiece buy TWO stories and stop:
--
--     outW(mix (input 1)) = 512    innW(scanᵉ …) = 2 ^ 512 * 258
--
-- so the whole static width is 258 · 2 ^ 521, which sits under
-- towerℕ 4 = 2 ^ 65536 — against a retired measure that was above
-- 2 ^ (2 ^ (2 ^ (2 ^ 256))) at the same fuel
_ : outWⱽ 4 [] insC in0 ≡ 258 * 2 ^ 521
_ = refl

_ : outWⱽ 4 [] insC in1 ≡ 258 * 2 ^ 521
_ = refl

-- THE REVISIT CLAUSE ITSELF, isolated: slot 0 met with slot 0 already on
-- the path contributes nothing, at any fuel, on all three measures
_ : outWⱽ 9 (fz ∷ []) insC in0 ≡ 0
_ = refl

_ : innWⱽ 9 (fz ∷ []) insC in0 ≡ 0
_ = refl

_ : dWⱽ 9 (fz ∷ []) insC in0 ≡ 0
_ = refl

------------------------------------------------------------------
-- §3  AGREEMENT OFF THE CYCLE.
--
-- Gated on an acyclic 4-slot telescope of the same shape and size as the
-- cycle: slot 0's def reaches slot 1, slot 1's def reaches a SCRIPTED
-- slot instead of reaching back.  Two things must not move there, and
-- both are what "nothing acyclic re-pins" means:
--
--   · FUEL above the descent depth buys nothing (it did not under the
--     retired form either — the difference only ever showed on a cycle)
--   · marking a slot that is NOT on the descent path changes nothing
------------------------------------------------------------------

a0 a1 : Closed Γ₄ natᵗ
a0 = wrap (mix (input (fs fz)))
a1 = wrap (mix (input (fs (fs fz))))

insA : Slots Γ₄
insA fz                = shared a0
insA (fs fz)           = shared a1
insA (fs (fs fz))      = scripted (hot [])
insA (fs (fs (fs fz))) = scripted (hot [])

_ : slotsSize insA ≡ 50
_ = refl

_ : outWⱽ 20 [] insA in0 ≡ outWⱽ 4 [] insA in0
_ = refl

_ : outWⱽ 20 [] insA in1 ≡ outWⱽ 4 [] insA in1
_ = refl

-- an OFF-PATH mark: slot 3 is never entered from slot 0
_ : outWⱽ 4 (fs (fs (fs fz)) ∷ []) insA in0 ≡ outWⱽ 4 [] insA in0
_ = refl

_ : dWⱽ 4 [] insA a0 ≡ 0
_ = refl

-- and on a telescope with NO shared slots at all nothing can fire at
-- all, which is the State-Blowup / Frame-Work case
insS : Slots Γ₄
insS fz                = scripted (hot [])
insS (fs fz)           = scripted (hot [])
insS (fs (fs fz))      = scripted (hot [])
insS (fs (fs (fs fz))) = scripted (hot [])

_ : outWⱽ 9 [] insS (mix (input fz)) ≡ outWⱽ 4 [] insS (mix (input fz))
_ = refl

_ : outWⱽ 4 (fz ∷ []) insS (mix (input (fs fz))) ≡ outWⱽ 4 [] insS (mix (input (fs fz)))
_ = refl

------------------------------------------------------------------
-- §4  THE BASE HEIGHT, AND THE INEQUALITY THE PORT MADE REAL.
--
-- The refuting row was a def of k wraps in a 2-cycle padded with n − 2
-- one-node dummy slots:
--
--     sz      = 19 + 28k + n          stories ≥ k * (n − 1)     (retired)
--
-- and at k = 8, n = 100 that is 792 against the 689 that 3 + 2·sz
-- allows.  Under the visited descent the SAME program demands 2k: a
-- descent path enters each SHARED slot at most once, there are two of
-- them, and each contributes its own k wraps.  The dummies contribute
-- nothing at all — they are scripted, and they were only ever raising
-- the FUEL.
------------------------------------------------------------------

-- the row that refuted the linear price, re-run: 16 against 689
_ : 2 * 8 ≡ 16
_ = refl

_ : (2 * 8 ≤ᵇ 3 + 2 * (19 + 28 * 8 + 100)) ≡ true
_ = refl

-- and the retired form's own demand, for the comparison
_ : 19 + 28 * 8 + 100 ≡ 343
_ = refl

_ : 3 + 2 * 343 ≡ 689
_ = refl

_ : 8 * 99 ≡ 792
_ = refl

_ : (8 * 99 ≤ᵇ 3 + 2 * (19 + 28 * 8 + 100)) ≡ false
_ = refl

-- THE GENERAL SHAPE, and it is not the 2-cycle that matters — it is that
-- a shared slot pays for its own stories in its own syntax.  A descent
-- path visits distinct shared slots d₁ … d_m; slot i of kᵢ wraps demands
-- kᵢ stories (one story per wrap) and costs 10 + 14·kᵢ nodes of
-- `slotsSize`.  So the demand along the whole path is Σkᵢ against a size
-- of Σ(10 + 14kᵢ), and
--
--     Σkᵢ ≤ 2 * Σ(10 + 14kᵢ)
--
-- with a factor of 28 to spare.  Under the RETIRED descent the same path
-- was re-entered once per fuel level and the demand was (Σkᵢ)·n, with n
-- bought at ONE node apiece — which is the product the ruling retired.
-- Stated per slot and summed by monotonicity:
visited-slot-fits : ∀ (k : ℕ) → k ≤ 2 * (10 + 14 * k)
visited-slot-fits k =
  ≤-trans (≤-trans (m≤n+m k 20) (+-monoʳ-≤ 20 (m≤m+n k (27 * k))))
          (≤-reflexive (shape k))
  where
  shape : ∀ (x : ℕ) → 20 + (x + 27 * x) ≡ 2 * (10 + 14 * x)
  shape = solve 1 (λ x → con 20 :+ (x :+ con 27 :* x)
                           := con 2 :* (con 10 :+ con 14 :* x)) refl

visited-height-fits : ∀ (a b : ℕ) →
  a + b ≤ 3 + 2 * ((10 + 14 * a) + (10 + 14 * b))
visited-height-fits a b =
  ≤-trans (+-mono-≤ (visited-slot-fits a) (visited-slot-fits b))
          (≤-trans (≤-reflexive (sym (split a b)))
                   (m≤n+m (2 * ((10 + 14 * a) + (10 + 14 * b))) 3))
  where
  split : ∀ (x y : ℕ) → 2 * ((10 + 14 * x) + (10 + 14 * y))
                          ≡ 2 * (10 + 14 * x) + 2 * (10 + 14 * y)
  split = solve 2 (λ x y → con 2 :* ((con 10 :+ con 14 :* x)
                                       :+ (con 10 :+ con 14 :* y))
                             := con 2 :* (con 10 :+ con 14 :* x)
                                :+ con 2 :* (con 10 :+ con 14 :* y)) refl

------------------------------------------------------------------
-- §5  THE SOUNDNESS DIRECTION.
--
-- Every clause of the family is built from ⊔, +, * and ^ with the
-- measured children in POSITIVE position, so replacing a descent by 0
-- can only lower the result: the visited-set measure is everywhere at or
-- below the retired one at the same fuel.  §2 shows the gap on the
-- cycle, where it is the whole tower; §3 shows it is zero off one.
--
-- That is the shape of the soundness argument, and it is also its LIMIT:
-- `≤ the old cap` is not the gate.  The gate is that every REAL RUN's
-- measured width still sits under the new (smaller) cap, which only the
-- State-Blowup wall can say — and §3 confines that question to
-- telescopes with a slot CYCLE, since every acyclic one computes the
-- IDENTICAL number.  No State-Blowup or Frame-Work row has a cyclic
-- telescope, so no measured row moves.
--
-- The general inequality is a clause-by-clause induction, and it now
-- LIVES IN Caps-Face beside `monoᵉ` rather than in a probe: the fuel and
-- visited axes are one mutual block, `q ≤ q′` with `Sub vs′ vs`.
------------------------------------------------------------------

-- AND THE SAME WITH THE UNMARKED TURN PAID FOR.  Reading defs at `[]`
-- lets ONE of them be met twice, so the demand is `Σkᵢ + max kᵢ` rather
-- than `Σkᵢ`.  Still linear, and still with room: the max is under the
-- sum, and the sum is under the syntax twice over
visited-height-fits-unmarked : ∀ (a b : ℕ) →
  (a + b) + (a ⊔ b) ≤ 3 + 2 * ((10 + 14 * a) + (10 + 14 * b))
visited-height-fits-unmarked a b =
  ≤-trans (≤-trans (+-monoʳ-≤ (a + b) (⊔-lub (m≤m+n a b) (m≤n+m b a)))
                   (≤-reflexive (dbl (a + b))))
          (≤-trans (*-monoʳ-≤ 2 sum≤) (m≤n+m (2 * ((10 + 14 * a) + (10 + 14 * b))) 3))
  where
  dbl : ∀ (x : ℕ) → x + x ≡ 2 * x
  dbl = solve 1 (λ x → x :+ x := con 2 :* x) refl
  m14 : ∀ (x : ℕ) → x + 13 * x ≡ 14 * x
  m14 = solve 1 (λ x → x :+ con 13 :* x := con 14 :* x) refl
  sum≤ : a + b ≤ (10 + 14 * a) + (10 + 14 * b)
  sum≤ = +-mono-≤ (≤-trans (m≤m+n a (13 * a))
                           (≤-trans (≤-reflexive (m14 a)) (m≤n+m (14 * a) 10)))
                  (≤-trans (m≤m+n b (13 * b))
                           (≤-trans (≤-reflexive (m14 b)) (m≤n+m (14 * b) 10)))

------------------------------------------------------------------
-- §6  THE ENTRY CEILING, ON THE SAME CYCLE.
--
-- `capsAt`'s base cWid is no longer the program's own three-term ⊔ but
-- the CEILING — the ⊔-collect of all five measures over every SUBTERM
-- of the program and of every shared def (Rx.Frame-Width.entryCeil).
-- The question §4's arithmetic has to survive is whether collecting
-- SUBTERMS costs tower stories, and it does not: a subterm of a def
-- with kᵢ wraps demands at most kᵢ stories, exactly as the def itself
-- does, so the demand along a descent path is the SAME `Σkᵢ + max kᵢ`
-- that `visited-height-fits-unmarked` already gates.  A ⊔ of numbers
-- each under `towerℕ h` is under `towerℕ h`; that is the whole content.
--
-- MEASURED on a 2-cycle small enough to compute (two shared defs
-- referencing each other through `mix`, no wraps, so no tower).  The
-- ceiling comes out at exactly TWICE the entry measure — the one
-- unmarked turn §2 already prices, a factor and not a story.
------------------------------------------------------------------

insM : Slots Γ₄
insM fz                = shared (mix (input (fs fz)))
insM (fs fz)           = shared (mix (input fz))
insM (fs (fs fz))      = scripted (hot [])
insM (fs (fs (fs fz))) = scripted (hot [])

_ : slotsSize insM ≡ 22
_ = refl

_ : outWᵉ 4 insM in0 ≡ 8
_ = refl

-- the collector agrees with the telescope's own, and both are one
-- unmarked turn above the entry measure
_ : slotsCeil 4 insM ≡ 16
_ = refl

_ : entryCeil 4 insM in0 ≡ 16
_ = refl

-- and 16 is towerℕ 3, against the `3 + 2 * sz` this base is allowed:
-- sz = 1 + 22 = 23, so 3 + 46 = 49 stories available for 3 demanded
_ : 3 + 2 * (1 + 22) ≡ 49
_ = refl

_ : (3 ≤ᵇ 3 + 2 * (1 + 22)) ≡ true
_ = refl
