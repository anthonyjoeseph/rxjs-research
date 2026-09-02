-- ══════════════════════════════════════════════════════════════════
-- A CASCADE'S LEVEL LEDGER IS NOT BOUNDED BY ANYTHING THE STATEMENT
-- CARRIES, SO THE WALK'S CEILING CANNOT PAY FOR IT.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE`
-- notes.
--
-- WHAT THE STATEMENT SAID.  Every level a whole cascade reaches is
-- affordable against the walk's charge: the selection's own total
-- length plus its count bounds the level, and `nestΦAt` pays.
--
-- WHERE IT BREAKS, AND IT IS NOT THE ARITHMETIC.  `nestΦAt e sl id`
-- is a function of the PROGRAM, the slot vocabulary and the instant --
-- it never reads the state.  The level ledger reads the state and
-- NOTHING ELSE: `chainsLenSum (chainsOf a st) + length (chainsOf a st)`
-- is as large as the registry is long.  So the two sides are not
-- comparable quantities at all, and no reading of the ceiling repairs
-- it: hand the statement a registry longer than the charge and the
-- premise is satisfied while the conclusion is a level above it.
--
-- THE WITNESS IS THEREFORE SYMBOLIC RATHER THAN NUMERIC, which is what
-- makes it total instead of a row.  The count is `suc` of the charge
-- itself, so no arithmetic about caps, towers or exponentials is
-- needed and none of the sealed families has to reduce.  What the
-- refutation spends is one inflation fact -- `k + s ≤ iterSize S k s`,
-- since one `sizeStep` at a positive cap is strictly inflationary --
-- and the proven fact that the charge dominates the cap.
--
-- WHAT IS OWED INSTEAD.  The registry this builds is not one the
-- evaluator can reach: `capsOK?` is what pins a reachable registry's
-- width to the cap and each chain's length to it, and it is the
-- standing premise of every sibling on this face -- `chains-count-width`
-- and `arr-chains-len-sum` both take it, at these very indices.  So
-- the repair is to THREAD it, not to weaken the conclusion: with it,
-- the ledger is a width times a cap plus a width, which is a cap
-- SQUARED plus a cap, and that is a bounded range the charge can be
-- widened to cover.  The statement's own header already argued the
-- width-times-a-cap reading; what it did not have was any hypothesis
-- entitling it to one.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Cascade-Afford-Wide where

open import Data.Bool using (false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; zero; suc; _≤_; _+_; _*_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-trans; ≤-refl; ≤-reflexive;
  +-monoʳ-≤; *-monoˡ-≤; *-identityˡ; m≤n+m; m≤m+n; m≤n*m; n≮n; +-comm; +-suc)
open import Data.Product using (_×_; _,_)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Data.Fin using () renaming (zero to fzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong;
  subst; sym)

open import Rx.Prim using (hot; Source)
open import Rx.Exp using (Ctx; Closed; natᵗ; obs; input)
open import Rx.Slots using (Slots; scripted)
open import Rx.Evaluator using (EvalSt; Arrival; Path; Chain; RegId; root;
  _↠_; thru-outer; mergeAllᵒ; chainsOf; st-init; sizeStep; iterSize)
open import Verify-Budget-Sufficient.Deliver-Measure using (chainsLenSum)
open import Verify-Budget-Sufficient.Caps using (Caps; capsAt; 8≤capsAt-size)
open import Verify-Budget-Sufficient.Caps-Face.Nest-Arith
  using (nestΦAt; nestWalkAt≤nestΦAt; unit+size≤nestWalkAt)

----------------------------------------------------------------------
-- THE STATEMENT, WRITTEN OUT RATHER THAN IMPORTED.  Importing the
-- postulate would prove the tower inconsistent instead of refuting
-- anything.
----------------------------------------------------------------------
CascadeAffordWide : Set
CascadeAffordWide = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (st : EvalSt e) (k : ℕ) →
  Caps.cSize (capsAt e sl id) ≤ k →
  k ≤ chainsLenSum (chainsOf a st) + length (chainsOf a st) →
  iterSize (Caps.cSize (capsAt e sl id)) k (Caps.cSize (capsAt e sl id))
    ≤ nestΦAt e sl id

----------------------------------------------------------------------
-- ONE `sizeStep` AT A POSITIVE CAP IS STRICTLY INFLATIONARY, so the
-- level a k-fold iteration reaches is at least k above where it began.
-- This is the whole arithmetic the refutation spends.
----------------------------------------------------------------------
suc≤sizeStep : ∀ (S s : ℕ) → 1 ≤ S → suc s ≤ sizeStep S s
suc≤sizeStep S s hS =
  ≤-trans (s≤s (m≤n*m s 2))
          (≤-trans (≤-reflexive (sym (*-identityˡ (suc (2 * s)))))
                   (*-monoˡ-≤ (suc (2 * s)) hS))

iterSize-lb : ∀ (S k s : ℕ) → 1 ≤ S → k + s ≤ iterSize S k s
iterSize-lb S zero    s hS = ≤-refl
iterSize-lb S (suc k) s hS =
  ≤-trans (≤-reflexive (sym (+-suc k s)))
          (≤-trans (+-monoʳ-≤ k (suc≤sizeStep S s hS))
                   (iterSize-lb S k (sizeStep S s) hS))

----------------------------------------------------------------------
-- THE WITNESS
----------------------------------------------------------------------
Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

sl₁ : Slots Γ₁
sl₁ fzero = scripted (hot [])

e₁ : Closed Γ₁ natᵗ
e₁ = input fzero

a : Arrival Γ₁
a = record { tick = 0 ; ordinal = 0 ; source = 0
           ; elemTy = obs natᵗ ; payload = input fzero ; isLast = false }

chain : Path Γ₁ (obs natᵗ) natᵗ
chain = thru-outer mergeAllᵒ 0 ↠ root

entry : RegId × Source × Chain Γ₁ natᵗ
entry = 0 , 0 , (obs natᵗ , chain)

-- A REGISTRY OF ANY LENGTH.  Nothing in the statement bounds it; that
-- is the refutation.
reg : ℕ → List (RegId × Source × Chain Γ₁ natᵗ)
reg zero    = []
reg (suc m) = entry ∷ reg m

stOf : ℕ → EvalSt e₁
stOf m = record (st-init e₁) { registry = reg m }

-- every entry matches the arrival, so the selection is the registry
selLen : ∀ (m : ℕ) → length (chainsOf a (stOf m)) ≡ m
selLen zero    = refl
selLen (suc m) = cong suc (selLen m)

S : ℕ
S = Caps.cSize (capsAt e₁ sl₁ 0)

1≤S : 1 ≤ S
1≤S = ≤-trans (s≤s z≤n) (8≤capsAt-size e₁ sl₁ 0)

N : ℕ
N = nestΦAt e₁ sl₁ 0

-- the charge dominates the cap, which is the one proven fact the
-- witness needs about a family it never unfolds
S≤N : S ≤ N
S≤N = ≤-trans (≤-trans (m≤n+m S _) (unit+size≤nestWalkAt e₁ sl₁ 0))
              (nestWalkAt≤nestΦAt e₁ sl₁ 0)

K : ℕ
K = suc N

S≤K : S ≤ K
S≤K = ≤-trans S≤N (≤-trans (m≤m+n N 1) (≤-reflexive (+-comm N 1)))

hK : K ≤ chainsLenSum (chainsOf a (stOf K)) + length (chainsOf a (stOf K))
hK = subst (λ z → K ≤ chainsLenSum (chainsOf a (stOf K)) + z)
           (sym (selLen K))
           (m≤n+m K (chainsLenSum (chainsOf a (stOf K))))

cascade-afford-wide-absurd : CascadeAffordWide → ⊥
cascade-afford-wide-absurd pr =
  n≮n N (≤-trans (m≤m+n K S)
                 (≤-trans (iterSize-lb S K S 1≤S)
                          (pr {e = e₁} sl₁ 0 a (stOf K) K S≤K hK)))
