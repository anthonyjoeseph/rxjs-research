-- ══════════════════════════════════════════════════════════════════
-- THE FOLD'S CHARGE IS A POWER IN THE BURST AND THE FRAME'S FACTOR
-- BUYS A FIXED NUMBER OF THEM, so a burst wider than the cap admits
-- crosses however generous the factor is.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE`
-- notes.
--
-- WHAT THE STATEMENT SAID.  A scan frame handed a legal path and a
-- burst whose values are affordable can name a ceiling on its
-- accumulator and pay for the fold under the instant's budget.  What
-- it must pay is `(2 ^ sizeᵗ fn) ^ length vals` times that ceiling --
-- one re-wrap of the accumulator per value folded in, which is what a
-- scan does.
--
-- WHERE IT BREAKS, AND IT IS NOT THE BUDGET.  Three of the four
-- premises are about the PATH -- its size legality, its nesting
-- depth, the frame's own shape -- and the fourth is an `all` over the
-- values, which constrains each value separately and says nothing
-- about how many there are.  So the count is a free parameter of the
-- statement while both sides are exponentials in fixed exponents, and
-- the burst that beats the frame's own factor is arithmetic: the
-- premise surrenders one power per unit of `suc (sizeᵗ fn)` per unit
-- of cap, the conclusion charges one per unit of `sizeᵗ fn` per value,
-- and the second overtakes the first at a burst just past the cap.
-- ══════════════════════════════════════════════════════════════════

-- AND THAT IS A NAMED THRESHOLD RATHER THAN A GAP, which is what
-- separates this reading from the one it replaces.  The witness below
-- is the SMALLEST burst that crosses at the reachable size floor, so
-- what the arm is short of is exactly a premise bounding the count by
-- the cap -- the conjunct the caps face's own value ledger carries and
-- `stepFrame-scan-caps`, proven about this very frame, takes.  The Φ
-- face's version of the same operation does not take it, so the two
-- faces disagree about the ARGUMENTS rather than about the
-- mathematics, and the undischarged side is the one that has not been
-- checked.
--
-- AND A WIDTH CONJUNCT ON ITS OWN IS STILL NOT THE REPAIR, which is
-- what the second statement below is for.  It carries the missing
-- premise and dies at the same witness at every width the crossing
-- admits, the width left UNIVERSALLY quantified: a ledger that bounds
-- the count by a number of its own choosing buys nothing, because the
-- number that has to bound it is the instant's SIZE CAP and no
-- conjunct on the values names that.
module Refuted.Scan-Phi-Width where

open import Data.Bool using (true)
open import Data.Empty using (⊥)
open import Data.List using (List; []; length; replicate)
open import Data.Nat using (ℕ; suc; _≤_; z≤n; s≤s; _+_; _*_; _^_; _⊔_)
open import Data.Nat.Properties using (≤-trans; ≤-refl; ≤-reflexive; n≮n;
  ≤ᵇ⇒≤; *-identityˡ; *-monoʳ-≤; +-mono-≤; m≤n+m; m≤m+n)
open import Data.Product using (Σ; _×_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Rx.Exp using (Ctx; Closed; Val; Fn; natᵗ; obs; _×ᵗ_; emptyᵉ; sizeᵗ)
open import Rx.Nest-Depth using (nestDᵗ)
open import Rx.Slots using (Slots)
open import Rx.Evaluator using (Sched; EvalSt; Path; NodeId; root; _↠_;
  scan-f; sched-init; st-init)
open import Verify-Budget-Sufficient.Nest-Store using (pathNestD)
open import Verify-Budget-Sufficient.Nest-Walk using (nestDᵛˢ; nodeNestAt)
open import Verify-Budget-Sufficient.Walk-Factor using (pathΦF)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (pathSz?)
open import Verify-Budget-Sufficient.Regs-Nest-Walk using (valsΦ?)
open import Refuted.Demand-Programs using (Γ₂; foldD; insT)

----------------------------------------------------------------------
-- THE STATEMENT, WRITTEN OUT RATHER THAN IMPORTED.  Importing the
-- postulate would prove the tower inconsistent instead of refuting
-- anything -- and it could not be instantiated in any case, since its
-- cap does not return at any program and its budget is sealed.  So the
-- obligation is stated over the quantities the arm's own premises
-- deliver: an abstract cap, budget and nesting unit, with every one of
-- the four premises kept, and the scan arm of `FrameΦHyp` written out
-- as the conclusion.
----------------------------------------------------------------------
ScanΦFits : Set
ScanΦFits = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (sl : Slots Γ) (B U nu : ℕ) (nid : NodeId)
  (fn : Fn Γ [] [] [] (u ×ᵗ s) u)
  (p : Path Γ u t) (vals : List (Val Γ s))
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  pathSz? B (scan-f fn nid ↠ p) ≡ true →
  pathNestD (scan-f fn nid ↠ p) ≤ nu →
  valsΦ? B U (scan-f fn nid ↠ p) vals ≡ true →
  Σ ℕ λ G →
    (nodeNestAt nid st ⊔ nestDᵛˢ vals ≤ G)
    × (pathΦF B p * ((2 ^ sizeᵗ fn) ^ length vals
                       * (G + length vals * nestDᵗ fn)
                     + pathNestD p) ≤ U)

----------------------------------------------------------------------
-- THE WITNESS.  One scan frame whose function wraps its accumulator a
-- single level -- the smallest fold that nests at all -- sitting at
-- the ROOT, so the path contributes no factor and no depth of its own
-- and the crossing cannot be blamed on anything but the fold.  The
-- burst is one bare nat repeated: every value is at depth zero, so
-- the premise is the same single inequality however many there are,
-- and the size cap is the REACHABLE floor this development discharges
-- from rather than the weakest one proven.
--
-- AND THE COUNT IS THE LEAST ONE THAT CROSSES AT THAT FLOOR, which is
-- what makes the row a reading of the threshold rather than of a
-- number chosen large.  The frame surrenders seven powers per unit of
-- cap and the fold charges six per value, so twenty-four values is
-- the first burst whose charge outruns twenty-one caps' worth of
-- factor -- at twenty-three the fold is still four hundred and
-- eighty-nine charges short.
----------------------------------------------------------------------

sl : Slots Γ₂
sl = insT 0 0 0

prog : Closed Γ₂ (obs natᵗ)
prog = emptyᵉ

st₀ : EvalSt prog
st₀ = st-init prog

sd : Sched Γ₂
sd = sched-init prog sl

fn : Fn Γ₂ [] [] [] ((obs natᵗ) ×ᵗ natᵗ) (obs natᵗ)
fn = foldD 1

rt : Path Γ₂ (obs natᵗ) (obs natᵗ)
rt = root

whole : Path Γ₂ natᵗ (obs natᵗ)
whole = scan-f fn 0 ↠ rt

v : Val Γ₂ natᵗ
v = 0

burst : List (Val Γ₂ natᵗ)
burst = replicate 24 v

-- THE BUDGET IS TAKEN AT EXACTLY WHAT ONE VALUE COSTS, so the
-- refutation cannot be dismissed as a budget chosen too small: it is
-- the least one at which the burst is affordable at all, and the
-- crossing is already there at the twenty-fourth value.  A larger
-- budget is beaten by the same construction further along, since the
-- premise grows with neither.
U : ℕ
U = pathΦF 21 whole * (0 + pathNestD whole)

-- THE QUANTITIES, PINNED, so a repair moving any of them fails here
-- naming the number rather than turning the crossing into an
-- equality.
size≡ : sizeᵗ fn ≡ 6
size≡ = refl

nestD≡ : nestDᵗ fn ≡ 1
nestD≡ = refl

depth≡ : pathNestD whole ≡ 1
depth≡ = refl

rootFac≡ : pathΦF 21 rt ≡ 1
rootFac≡ = refl

legal : pathSz? 21 whole ≡ true
legal = refl

unit-ok : pathNestD whole ≤ pathNestD whole
unit-ok = ≤-refl

-- every value clears the budget, since it was taken at their cost
premΦ : valsΦ? 21 U whole burst ≡ true
premΦ = refl

----------------------------------------------------------------------
-- THE ARITHMETIC, AND THE CEILING PLAYS NO PART IN IT.  The bound is
-- taken through the burst's own contribution, so it holds at every
-- `G` the fold could be granted -- including zero.  What crosses is
-- the twenty-fourth power of the re-wrap against a factor that bought
-- twenty-one caps' worth, which is why no ceiling and no larger
-- budget is the repair.
----------------------------------------------------------------------
-- THE CROSSING, AND IT IS ALL BETWEEN CLOSED NUMERALS.  Nothing here
-- mentions the ceiling, so every comparison costs one machine
-- operation rather than a walk down a forty-five digit literal.
charge : ℕ
charge = (2 ^ 6) ^ 24

one≤ : 1 ≤ charge
one≤ = s≤s z≤n

-- EVERY IMPLICIT IS SUPPLIED, and that is not style: left to solve
-- them the checker inverts a builtin addition against that literal and
-- dies.
refl≤ : U ≤ U
refl≤ = ≤-refl

-- the budget plus a single unit still fits inside nine charges,
-- because the factor bought only three powers more than the charge
-- and the burst's own additive share is what tips it
step : suc U ≤ charge + U
step = +-mono-≤ {1} {charge} {U} {U} one≤ refl≤

nine : charge + U ≡ charge * 9
nine = refl

crossing : suc U ≤ (2 ^ sizeᵗ fn) ^ length burst
                     * (length burst * nestDᵗ fn)
crossing = ≤-trans step
             (≤-trans (≤-reflexive nine)
                      (*-monoʳ-≤ charge (≤ᵇ⇒≤ 9 24 tt)))

-- THE WIDENING IS STATED OVER VARIABLES, and that is load-bearing.  A
-- literal multiplied by a term the checker cannot close is compared by
-- peeling one successor at a time, so the same step written at the
-- concrete quantities unfolds the factor rather than looking at it and
-- never finishes.  Over variables there is nothing to unfold, and the
-- application below lands on the obligation's own spellings, where the
-- comparison is syntactic.
widen : ∀ (X F E K D G : ℕ) → F ≡ 1 → X ≤ E * K → X ≤ F * (E * (G + K) + D)
widen X _ E K D G refl h =
  ≤-trans h
    (≤-trans (*-monoʳ-≤ E (m≤n+m K G))
    (≤-trans (m≤m+n (E * (G + K)) D)
             (≤-reflexive (sym (*-identityˡ (E * (G + K) + D))))))

bound : ∀ (G : ℕ) →
  suc U ≤ pathΦF 21 rt * ((2 ^ sizeᵗ fn) ^ length burst
                            * (G + length burst * nestDᵗ fn)
                          + pathNestD rt)
bound G = widen (suc U) (pathΦF 21 rt) ((2 ^ sizeᵗ fn) ^ length burst)
                (length burst * nestDᵗ fn) (pathNestD rt) G
                rootFac≡ crossing

-- THE RESULT IS TAKEN APART BY PROJECTION, NOT BY `with`, and that is
-- the same finding as the widening above arriving from the other side:
-- abstracting over this Σ reduces the type it carries, and reducing a
-- product of the factor with a term holding the ceiling walks the
-- factor down one successor at a time.  A projection leaves the type
-- exactly as the statement wrote it.
scan-phi-width-absurd : ScanΦFits → ⊥
scan-phi-width-absurd pr = n≮n U (≤-trans (bound (proj₁ res))
                                          (proj₂ (proj₂ res)))
  where
  res = pr {Γ = Γ₂} {t = obs natᵗ} {e = prog} {s = natᵗ} {u = obs natᵗ}
           sl 21 U (pathNestD whole) 0 fn rt burst sd st₀
           refl legal unit-ok premΦ

----------------------------------------------------------------------
-- THE SAME STATEMENT WITH THE MISSING PREMISE, so that the finding is
-- about WHICH number the conjunct has to name and not about its
-- absence.  Everything else is held fixed -- the same four premises,
-- the same conclusion, the same witness -- and the width is left
-- UNIVERSALLY quantified over the range the crossing admits, so no
-- choice of it is what the refutation rests on.  A ledger free to
-- pick its own width picks one that admits this burst; only a width
-- read off the instant's size cap does not.
----------------------------------------------------------------------
ScanΦFitsWide : Set
ScanΦFitsWide = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (sl : Slots Γ) (B U nu W : ℕ) (nid : NodeId)
  (fn : Fn Γ [] [] [] (u ×ᵗ s) u)
  (p : Path Γ u t) (vals : List (Val Γ s))
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  pathSz? B (scan-f fn nid ↠ p) ≡ true →
  pathNestD (scan-f fn nid ↠ p) ≤ nu →
  length vals ≤ suc W →
  valsΦ? B U (scan-f fn nid ↠ p) vals ≡ true →
  Σ ℕ λ G →
    (nodeNestAt nid st ⊔ nestDᵛˢ vals ≤ G)
    × (pathΦF B p * ((2 ^ sizeᵗ fn) ^ length vals
                       * (G + length vals * nestDᵗ fn)
                     + pathNestD p) ≤ U)

-- the burst clears the conjunct at every width the ledger could
-- choose that admits it, which is what makes the row a fact about
-- which quantity the width must be read off rather than about a
-- number chosen for it
wide : ∀ (W : ℕ) → 23 ≤ W → length burst ≤ suc W
wide W 23≤W = s≤s 23≤W

scan-phi-wide-absurd : ScanΦFitsWide → ∀ (W : ℕ) → 23 ≤ W → ⊥
scan-phi-wide-absurd pr W 23≤W = n≮n U (≤-trans (bound (proj₁ res))
                                                (proj₂ (proj₂ res)))
  where
  res = pr {Γ = Γ₂} {t = obs natᵗ} {e = prog} {s = natᵗ} {u = obs natᵗ}
           sl 21 U (pathNestD whole) W 0 fn rt burst sd st₀
           refl legal unit-ok (wide W 23≤W) premΦ
