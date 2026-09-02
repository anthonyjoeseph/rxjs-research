-- THE CUTTING FRAME, THE ONE AXIS THREE SWEEPS LEFT UNTOUCHED.  Depth,
-- share telescope and fan width are all instantiated, and every row of
-- all three flattens with `mergeAllᵉ` -- so every frame those sweeps
-- walked SUBSCRIBES, which is the arm the statement's arithmetic is
-- about.  The other arm is the cut: `takeᵉ` expiring its count,
-- `switchAllᵉ` abandoning an inner, `exhaustAllᵉ` refusing one.  A cut
-- mid-path leaves the fold running on an EMPTY value list, so the emit
-- is emptied rather than swallowed and `shareGo` walks on to the next
-- registration with the cut one named a victim.  Nothing says what the
-- registry does across that.

-- A CUT AT THE LEAF AND A CUT INSIDE THE TELESCOPE ARE DIFFERENT
-- QUESTIONS, and only the second can reach the recursion.  A cutting
-- branch of the ROOT bottoms out where it cuts, so it tests the arm
-- and nothing else.  A cut on the def of share two sits BETWEEN two
-- sinks: the fold crosses share one, meets the cutting frame, and must
-- still arrive at share two's own sink with whatever the cut left it.
-- Both are here, and the second is the row that matters.

-- AND ONE MIXED ROW, BECAUSE A CUT SIBLING IS NOT A CUT CHAIN.
-- `shareGo` threads the state through its registrations in order, so a
-- branch that cuts changes what the branches AFTER it are folded
-- against -- the `cancelled` list it consults is the one the earlier
-- fold left behind.  A width-two share with one cutting branch and one
-- live one is the smallest program where that ordering is observable,
-- and it is not covered by either uniform row.

-- WHAT COULD REFUTE, and it is the registered length alone.  The
-- statement prices a registry by `pathSz?`, whose only unbounded
-- conjunct is `suc (pathLen p) ≤ B` at every frame.  A cut can only
-- refute by leaving a LONGER path registered than a subscribing frame
-- would -- a dead entry the sweep failed to collect, say -- so the
-- reading to take is the maximum registered length against the same
-- shape built out of flattens.

-- WHAT THESE ROWS DO NOT BUY, AND TWO OF THEM BUY LESS THAN THEY
-- LOOK LIKE.  The switch and exhaust rows read IDENTICAL to the
-- flatten control on every figure, and the reason is that they did not
-- cut: on a FIRST arrival there is no earlier inner for `switchAllᵉ`
-- to abandon and none active for `exhaustAllᵉ` to refuse, so both take
-- the subscribing arm.  They are evidence that those two operators do
-- not lengthen a path when they behave as flattens, and evidence about
-- nothing else; reaching their cut needs a SECOND arrival, which is a
-- second `chainStep` and not this shape.
--
-- AND ON EVERY ROW THAT DOES CUT, THE REGISTRY SHRINKS -- three
-- entries to one where both branches cut, four to one through the
-- telescope.  A growth bound is satisfied by any shrinking step
-- whatever the frames did, so those rows say nothing about the size
-- conjunct and everything about the LENGTH one, which is the conjunct
-- named above as the only unbounded one.  The mixed row is the one
-- with a survivor: it drops one entry and keeps the other at exactly
-- the control's length.

-- TARGET: foldPath-regsLen @68fc23
module Probed.Chain-Step-Regs-Cut where

open import Data.Bool using (true; _∧_)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.List using ([]; _∷_; map; foldr; length)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; suc; _+_; _*_; _⊔_; _≤ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx; Closed; natᵗ; ofᵉ; mapᵉ; mergeAllᵉ; takeᵉ;
  switchAllᵉ; exhaustAllᵉ; strmᵗ; nat̂; input; syncSizeᵉ)
open import Rx.Prim using (gasPad; g0; cold; after_,_)
open import Rx.Slots using (Slots; scripted; shared)
open import Rx.Evaluator using (Sched; EvalSt; subscribeE; sched-init;
  st-init; root; sched-next; cascadeLatch; chainStep; chainsOf)
open import Rx.Hop-Depth using (hopDᵉ)
open import Rx.Slot-Hop using (slotHop)
open import Verify-Budget-Sufficient.Measures using (pathLen)

Γ₃ : Ctx 3
Γ₃ = natᵗ ∷ⱽ natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

-- the SUBSCRIBING frame, kept as the control every cut is read against
feedM : Closed Γ₃ natᵗ → Closed Γ₃ natᵗ
feedM src = mergeAllᵉ nothing (mapᵉ (strmᵗ (ofᵉ (nat̂ 1 ∷ []))) src)

-- the three cutting frames, each over the identical inner, so the only
-- thing that differs between a control row and a cut row is the arm
feedSw : Closed Γ₃ natᵗ → Closed Γ₃ natᵗ
feedSw src = switchAllᵉ (mapᵉ (strmᵗ (ofᵉ (nat̂ 1 ∷ []))) src)

feedEx : Closed Γ₃ natᵗ → Closed Γ₃ natᵗ
feedEx src = exhaustAllᵉ (mapᵉ (strmᵗ (ofᵉ (nat̂ 1 ∷ []))) src)

-- a count of ONE, so the cut lands on the very arrival the rows step
cut1 : Closed Γ₃ natᵗ → Closed Γ₃ natᵗ
cut1 src = takeᵉ (nat̂ 1) (feedM src)

-- two branches merged, the diamond shape the width sweep established,
-- reused here so the cut is read at a share that genuinely fans
two : Closed Γ₃ natᵗ → Closed Γ₃ natᵗ → Closed Γ₃ natᵗ
two l r = mergeAllᵉ nothing (ofᵉ (strmᵗ l ∷ strmᵗ r ∷ []))

slots : Slots Γ₃
-- SHARE TWO'S DEF IS THE CUTTING ONE: a program rooted at slot two
-- puts the cut BETWEEN the two sinks, which is the only arrangement
-- where a cut frame is re-entered rather than bottomed out.
slots fzero               = scripted (cold [] ((after 0 , 7) ∷ (after 0 , 8) ∷ []))
slots (fsuc fzero)        = shared (feedM (input fzero))
slots (fsuc (fsuc fzero)) = shared (cut1 (input (fsuc fzero)))

sucG : Closed Γ₃ natᵗ → ℕ
sucG e = suc (syncSizeᵉ e + hopDᵉ 0 (slotHop 0 slots) e)

sub : (e : Closed Γ₃ natᵗ) → Sched Γ₃ × EvalSt e
sub e = let r = subscribeE (gasPad (sucG e) g0) e root 0 0
                           (sched-init e slots) (st-init e)
        in proj₁ (proj₂ r) , proj₂ (proj₂ r)

maxLenOf : (e : Closed Γ₃ natᵗ) → EvalSt e → ℕ
maxLenOf e st = foldr _⊔_ 0
  (map (λ en → pathLen (proj₂ (proj₂ (proj₂ en)))) (EvalSt.registry st))

row : (e : Closed Γ₃ natᵗ) → ℕ × ℕ × ℕ × ℕ × ℕ
row e with sched-next (proj₁ (sub e))
... | inj₁ _        = 0 , 0 , 0 , 0 , 0
... | inj₂ (a , sd) with chainsOf a (proj₂ (sub e))
...   | []            = 0 , 0 , 0 , 0 , 0
...   | (rid , c) ∷ _ =
        let st₀ = cascadeLatch a (proj₂ (sub e))
            r   = chainStep 1 a c sd st₀
        in maxLenOf e st₀ , maxLenOf e (proj₂ (proj₂ r))
         , length (EvalSt.registry st₀)
         , length (EvalSt.registry (proj₂ (proj₂ r)))
         , length (proj₁ r)

-- WHICH ARM EACH ROW IS TAKEN ON, so a row cannot read as covered
-- while the program never reached a real `chainStep`
stage : Closed Γ₃ natᵗ → ℕ
stage e with sched-next (proj₁ (sub e))
... | inj₁ _        = 1
... | inj₂ (a , sd) with chainsOf a (proj₂ (sub e))
...   | []          = 2
...   | _ ∷ _       = 3

lenBefore : Closed Γ₃ natᵗ → ℕ
lenBefore e = proj₁ (row e)
lenAfter : Closed Γ₃ natᵗ → ℕ
lenAfter e = proj₁ (proj₂ (row e))
regsBefore : Closed Γ₃ natᵗ → ℕ
regsBefore e = proj₁ (proj₂ (proj₂ (row e)))
regsAfter : Closed Γ₃ natᵗ → ℕ
regsAfter e = proj₁ (proj₂ (proj₂ (proj₂ (row e))))
emits : Closed Γ₃ natᵗ → ℕ
emits e = proj₂ (proj₂ (proj₂ (proj₂ (row e))))

sh₁ sh₂ : Closed Γ₃ natᵗ
sh₁ = input (fsuc fzero)
sh₂ = input (fsuc (fsuc fzero))

-- LEAF ROWS: the cut bottoms out on the branch that carries it.
-- `ctl` is the all-flatten control the other three are read against.
ctl swi exh tak : Closed Γ₃ natᵗ
ctl = two (feedM sh₁) (feedM sh₁)
swi = two (feedSw sh₁) (feedSw sh₁)
exh = two (feedEx sh₁) (feedEx sh₁)
tak = two (cut1  sh₁) (cut1  sh₁)

-- MIXED: one branch cuts and one does not, so the live branch is
-- folded against the `cancelled` list the cut branch left behind
mix : Closed Γ₃ natᵗ
mix = two (cut1 sh₁) (feedM sh₁)

-- THE TELESCOPE ROW: rooted at share two, whose def CUTS, so the fold
-- crosses share one, meets the cutting frame, and must still reach
-- share two's own sink.  It has no same-slots control -- `slots` fixes
-- share two's def as the cutting one, so an uncut program rooted there
-- does not exist in this family -- and it is read against `ctl` one
-- share lower plus the one level the statement licenses.
deepCut : Closed Γ₃ natᵗ
deepCut = two (feedM sh₂) (feedM sh₂)

packed : Closed Γ₃ natᵗ → ℕ
packed e = lenBefore e + 100 * lenAfter e + 10000 * regsBefore e
         + 1000000 * regsAfter e + 100000000 * emits e

-- EVERY ROW ON THE CHAIN ARM: a plain sum, so no row can be carried by
-- another and a program that never reached `chainStep` shows up as a
-- wrong total rather than as a silent zero
reaches : stage ctl + stage swi + stage exh + stage tak
        + stage mix + stage deepCut ≡ 18
reaches = refl

figuresC : packed ctl ≡ 303030303
figuresC = refl

figuresSw : packed swi ≡ 303030303
figuresSw = refl

figuresEx : packed exh ≡ 303030303
figuresEx = refl

figuresTk : packed tak ≡ 301030204
figuresTk = refl

figuresMx : packed mix ≡ 302030304
figuresMx = refl

figuresDp : packed deepCut ≡ 401040203
figuresDp = refl

-- NO CUT LENGTHENS A REGISTERED PATH PAST ITS FLATTEN CONTROL, the
-- claim the sweep is here to test.  The leaf rows are read against
-- `ctl` and the telescope row against `deep`, which is the same shape
-- one share lower; a cut that left a longer entry standing than the
-- subscribing frame does is what a refutation looks like.
no-longer-than-control : (lenAfter swi ≤ᵇ lenAfter ctl)
                       ∧ (lenAfter exh ≤ᵇ lenAfter ctl)
                       ∧ (lenAfter tak ≤ᵇ lenAfter ctl)
                       ∧ (lenAfter mix ≤ᵇ lenAfter ctl)
                       ∧ (lenAfter deepCut ≤ᵇ suc (lenAfter ctl)) ≡ true
no-longer-than-control = refl
