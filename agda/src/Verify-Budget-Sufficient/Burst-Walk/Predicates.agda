------------------------------------------------------------------
-- THE BURST LEDGER'S PREDICATES, hoisted below the level face.
--
-- Five pure ledger definitions, each a caps half conjoined with a Ψ
-- half read at `frameStep J c`, and the event and stream flavours
-- carrying `nodry` beside them.  Nothing here mentions the walk, the
-- level face, or a frame's step relation.
--
-- THEY SIT HERE RATHER THAN BESIDE THE THEOREMS THAT SPEND THEM, and
-- the reason is a build cost paid by consumers who want a ledger and
-- nothing else.  `.Burst-Walk` imports the level face for its own
-- theorems, so a module taking one predicate from it inherits that
-- face and its whole cone.  The refutations are exactly such
-- consumers: three of them import this ledger and no theorem, and in
-- the shared form they were the sole route by which the evidence
-- trees built the top of the tower.
--
-- `VbB` STAYS OUTSIDE THE ANONYMOUS MODULE, as it did before the
-- hoist: it never mentions `t`, and an unmentioned module implicit is
-- an unsolvable meta at every use site.
------------------------------------------------------------------
module Verify-Budget-Sufficient.Burst-Walk.Predicates where

open import Data.Bool using (Bool; true; _∧_; not)
open import Data.Bool.ListAction using (all; any)
open import Data.List using (List)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Prim using (InstEvent)
open import Rx.Exp using (Ctx; Closed; Val; Ty)
open import Rx.Slots using (Slots)
open import Rx.Evaluator using (Path; Stream; Sched; EvalSt; dryEvent; hasDry)

open import Verify-Budget-Sufficient.Caps using (Caps; frameStep)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using
  (burstCaps?; eventCaps?; pathSz?)
open import Verify-Budget-Sufficient.Caps-Face.Part4 using
  (valsCaps?; walkOK)
open import Verify-Budget-Sufficient.Measures using (fnCapBounded?)
open import Verify-Budget-Sufficient.Psi-Split using
  (burstΨ?; eventsΨ?; pathBΨ?; valsΨ?)

VbB : ∀ {n} {Γ : Ctx n} → Caps → Slots Γ → ℕ → ℕ → ∀ {s} → List (Val Γ s) → Bool
VbB c sl Ψ J vs = valsCaps? (frameStep J c) sl vs ∧ valsΨ? Ψ vs

module _ {n} {Γ : Ctx n} {t : Ty} where

  PbB : Caps → ℕ → ℕ → ∀ {u} → Path Γ u t → Bool
  PbB c Ψ J p = pathSz? (Caps.cSize (frameStep J c)) p ∧ pathBΨ? Ψ p

  EbB : Caps → Slots Γ → ℕ → ℕ → List (InstEvent (Val Γ t)) → Bool
  EbB c sl Ψ J es =
    all (eventCaps? (frameStep J c) sl) es ∧ eventsΨ? Ψ es
      ∧ not (any dryEvent es)

  BbB : Caps → Slots Γ → ℕ → ℕ → Stream Γ t → Bool
  BbB c sl Ψ J str =
    burstCaps? (frameStep J c) sl str ∧ burstΨ? Ψ str
      ∧ not (hasDry str)

OKB : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    → Caps → Slots Γ → ℕ → ℕ → Sched Γ → EvalSt e → Set
OKB c sl Ψ J sched st =
  walkOK c sl J sched st × (fnCapBounded? Ψ sched st ≡ true)
