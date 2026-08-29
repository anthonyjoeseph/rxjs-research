-- ══════════════════════════════════════════════════════════════════
-- THE WALK CANNOT SUPPLY THE DRAIN'S HEADROOM AT ITS OWN LEVELS.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- THE TWO CURRENCIES DISAGREE, AND NOTHING IN THE WALK TIES THEM.  The
-- drain's headroom conjunct charges the level against the BASE size cap
-- -- `Lv + (3 + (sizeᵉ o + slotsSize sl)) ≤ Caps.cSize c` -- because its
-- consumer climbs the relative ceiling one operator per level from the
-- bottom, and that climb is only paid for while the level fits under the
-- base.  The walk's own level ledger is stated against the COUNT
-- instead: the Σ it hands its tail permits `Lv` anywhere up to
-- `sizeCount c d ⊔ Caps.cSize c`, and the arrival face confirms levels
-- genuinely reach the count rather than the size.  So the walk hands the
-- drain a level the drain's arithmetic cannot absorb, and no hypothesis
-- in the bundle relates the two.
--
-- CLAUDE.md's first almost-always-wrong shape: a conclusion needing
-- information that appears in NO hypothesis.  The witness below takes
-- the level to be exactly the base size cap -- a value the ladder
-- premise admits, and the ONLY quantity the conjunct is sensitive to,
-- since at level zero `capsOK?` at the base already delivers the
-- conjunct verbatim through `parkRoom`.
--
-- WHAT IS AND IS NOT ADVERSARIAL HERE.  The parked term is one literal
-- stream smaller than the program itself, so every cap premise it has to
-- meet is met by the entry bounds and nothing is tuned; the state is
-- `st-init` with one node installed through the proven installer, so
-- `capsOK?` is not asserted but derived.  The level is the whole
-- witness.  The state is HAND-BUILT rather than reached by running, so
-- what this pins is that the STATEMENT is false, not that a run gets
-- here -- and that is the right reading, because the statement carries
-- no reachability hypothesis to appeal to.
--
-- WHAT THIS DOES NOT SHOW.  Nothing here says the drain face is wrong.
-- The base-cap conjunct is what its own proven consumer spends, so the
-- repair belongs on the walk side: either a level invariant tight enough
-- to keep `Lv` under the size cap, or a ceiling carried through the walk
-- in the relative form the drain's consumer already uses -- which is the
-- form the walk's Σ is ALREADY in, one `opIterD` away.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Walk-Frame-Drain-Level where

open import Data.Bool using (Bool; true; false)
open import Data.Nat  using (ℕ; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; ≤ᵇ⇒≤;
                                       m≤m⊔n; m+1+n≰m; n≤1+n)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just)
open import Data.Empty using (⊥)
open import Data.Unit using (tt)
open import Data.Product using (proj₁; proj₂; _,_)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Rx.Prim using (Gas; g0; Id; Tick; Source; InstEvent)
open import Rx.Exp  using (Ctx; Closed; Val; natᵗ; ofᵉ; nat̂; sizeᵉ)
open import Rx.Slots using (Slots; slotsSize)
open import Rx.Frame-Width using (pWᵉ)
open import Rx.Evaluator using (Sched; EvalSt; NodeState; mergeAll-st; setNode; mergeAllᵒ; Frame; from-inner; Path; root;
  _↠_; sched-init; st-init; iterL; dLvl; sizeAt)
open import Verify-Budget-Sufficient.Caps using (Caps; frameStep; capsAt; capsH;
                               sizeCount; cDel; sizeCount-body; cDel-body;
                               iterL-mono; dLvl-mono; lvls-mono; J+n≤iterL;
                               capsAt-base-size; capsAt-base-wid;
                               2≤capsAt-size; 1≤capsAt-reg)
open import Verify-Budget-Sufficient.Measures using (boundedNode; parkRoom)
open import Verify-Budget-Sufficient.Op-Budget using (tail-fits)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (widNode; capsOK?)
open import Verify-Budget-Sufficient.Caps-Face.Part4 using (capsOK?-setNode)
open import Verify-Budget-Sufficient.Caps-Face.Part5 using (cSize≤frameStep)
open import Verify-Budget-Sufficient.Caps-Bridge using (init-capsOK?)
open import Verify-Budget-Sufficient.Nest-Walk using (capsOK?-lvl; frameDrainOK)
open import Verify-Budget-Sufficient.Caps-Face.Part7 using (WalkHyps)
open import Decide using (∧-intro; ≤ᵇ-true)

----------------------------------------------------------------------
-- THE WITNESS.  Empty context, a four-element literal source, and one
-- parked inner strictly smaller than it, so the entry caps cover the
-- node outright.  The level is the base size cap.
----------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ⱽ

sl₀ : Slots Γ₀
sl₀ = λ ()

e₀ : Closed Γ₀ natᵗ
e₀ = ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ [])

o₀ : Closed Γ₀ natᵗ
o₀ = ofᵉ (nat̂ 0 ∷ [])

c₀ : Caps
c₀ = capsAt e₀ sl₀ 0

S₀ W₀ d₀ : ℕ
S₀ = Caps.cSize c₀
W₀ = Caps.cWid  c₀
d₀ = capsH e₀ sl₀ 0

2≤S₀ : 2 ≤ S₀
2≤S₀ = 2≤capsAt-size e₀ sl₀ 0

1≤W₀ : 1 ≤ W₀
1≤W₀ = ≤-trans (s≤s z≤n) (capsAt-base-wid e₀ sl₀ 0)

node₀ : NodeState Γ₀
node₀ = mergeAll-st (just 1) 1 (o₀ ∷ []) false

sched₀ : Sched Γ₀
sched₀ = sched-init e₀ sl₀

st₁ : EvalSt e₀
st₁ = record (st-init e₀)
        { nodes = setNode 0 node₀ (EvalSt.nodes (st-init e₀)) }

f₀ : Frame Γ₀ natᵗ natᵗ
f₀ = from-inner mergeAllᵒ 0 1

----------------------------------------------------------------------
-- THE NODE FITS THE ENTRY CAPS, all three ways the installer asks: the
-- parked term is smaller than the program the caps were minted from, so
-- each bound is the entry inequality with a numeral in front of it.
----------------------------------------------------------------------

BN : boundedNode S₀ node₀ ≡ true
BN = ∧-intro (≤ᵇ-true (sizeᵉ o₀) S₀
               (≤-trans (≤ᵇ⇒≤ (sizeᵉ o₀) (2 + sizeᵉ e₀ + slotsSize sl₀) tt)
                        (capsAt-base-size e₀ sl₀ 0)))
             refl

PK : parkRoom S₀ (slotsSize sl₀) node₀ ≡ true
PK = ∧-intro (≤ᵇ-true (3 + (sizeᵉ o₀ + slotsSize sl₀)) S₀
               (≤-trans (≤ᵇ⇒≤ (3 + (sizeᵉ o₀ + slotsSize sl₀))
                              (2 + sizeᵉ e₀ + slotsSize sl₀) tt)
                        (capsAt-base-size e₀ sl₀ 0)))
             refl

WN : widNode W₀ sl₀ node₀ ≡ true
WN = ∧-intro (∧-intro (≤ᵇ-true (pWᵉ 0 sl₀ o₀) W₀
                        (≤-trans (≤ᵇ⇒≤ (pWᵉ 0 sl₀ o₀) 1 tt) 1≤W₀))
                      refl)
             (≤ᵇ-true 1 W₀ 1≤W₀)

----------------------------------------------------------------------
-- THE BUNDLE.  Nothing here is tuned: the caps receipt is the proven
-- installer over the proven initial receipt, the depth is zero because a
-- frame that is not finishing reaches no subscribe, and the ladder
-- premise is the count dominating two of its own delivery steps.
----------------------------------------------------------------------

COK : capsOK? (frameStep S₀ c₀) sched₀ st₁ ≡ true
COK = capsOK?-lvl c₀ S₀ sched₀ st₁ 2≤S₀
        (capsOK?-setNode c₀ 0 node₀ sched₀ (st-init e₀) BN PK WN
           (init-capsOK? e₀ sl₀ 0))

1≤B : 1 ≤ Caps.cSize (frameStep S₀ c₀)
1≤B = ≤-trans (≤-trans (s≤s z≤n) 2≤S₀) (cSize≤frameStep c₀ S₀ 2≤S₀)

S≤dLvl0 : S₀ ≤ dLvl S₀ W₀ d₀ 0
S≤dLvl0 = ≤-trans (n≤1+n S₀) (J+n≤iterL S₀ W₀ d₀ (suc (sizeAt S₀ 0)) 0)

2≤D : 2 ≤ cDel c₀ d₀
2≤D = ≤-trans (s≤s 1≤W₀)
        (≤-trans (tail-fits S₀ W₀ d₀ (Caps.cReg c₀) 0 (suc S₀) 2≤S₀
                    (1≤capsAt-reg e₀ sl₀ 0) (≤-trans 2≤S₀ (n≤1+n S₀)))
                 (≤-reflexive (sym (cDel-body c₀ d₀))))

LADDER : iterL S₀ W₀ d₀ 1 S₀ ≤ sizeCount c₀ d₀ Data.Nat.⊔ S₀
LADDER =
  ≤-trans (iterL-mono {S₀} {S₀} {W₀} {W₀} {S₀} {S₀} {d₀}
             1 (suc (sizeAt S₀ S₀)) 2≤S₀ ≤-refl ≤-refl ≤-refl (s≤s z≤n))
  (≤-trans (dLvl-mono {S₀} {S₀} {W₀} {W₀} {S₀} {dLvl S₀ W₀ d₀ 0} {d₀}
              2≤S₀ ≤-refl ≤-refl S≤dLvl0)
  (≤-trans (lvls-mono {S₀} {S₀} {W₀} {W₀} {0} {0} {d₀}
              2 (cDel c₀ d₀) 2≤S₀ ≤-refl ≤-refl ≤-refl 2≤D)
  (≤-trans (≤-reflexive (sym (sizeCount-body c₀ d₀)))
           (m≤m⊔n (sizeCount c₀ d₀) S₀))))

HYPS : WalkHyps sl₀ 0 S₀ g0 0 0 0 0 (f₀ ↠ root) [] [] false sched₀ st₁
HYPS = refl
     , COK
     , refl
     , ∧-intro refl (∧-intro (≤ᵇ-true 1 (Caps.cSize (frameStep S₀ c₀)) 1≤B) refl)
     , z≤n
     , LADDER

----------------------------------------------------------------------
-- THE DEFECT, in one line: the drain's headroom conjunct is the level
-- ON TOP OF a positive quantity, under the base size cap, and the level
-- the walk is entitled to hand it IS that cap.
----------------------------------------------------------------------

walk-frame-drain-absurd :
  (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
     (sl : Slots Γ) (id : ℕ) (L : ℕ) (sf : Gas) (gas : ℕ) (nid : Id) (now : Tick)
     (src : Source) (f : Frame Γ s u) (p : Path Γ u t) (vals : List (Val Γ s))
     (evs : List (InstEvent (Val Γ t))) (fin : Bool)
     (sched : Sched Γ) (st : EvalSt e) →
     WalkHyps sl id L sf gas nid now src (f ↠ p) vals evs fin sched st →
     frameDrainOK (capsAt e sl id) sl (capsH e sl id) L sf nid now f p vals sched st)
  → ⊥
walk-frame-drain-absurd wd =
  m+1+n≰m S₀ {2 + (sizeᵉ o₀ + slotsSize sl₀)}
    (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ DR)))))))
  where
  DR = wd sl₀ 0 S₀ g0 0 0 0 0 f₀ root [] [] false sched₀ st₁ HYPS
         (just 1) 1 (o₀ ∷ []) false refl
