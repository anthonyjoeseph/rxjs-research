-- THE FOLD FAMILY'S TIE TO ITS STATEMENT, HELD ONCE FOR THE WHOLE
-- FAMILY.  Every probe module reading `foldPath`'s registry against one
-- frame step does so at its own program and its own axis; what they
-- share is the STATEMENT, and this module is the one place it is
-- instantiated.  The satellites spend `foldRow` under a type they write
-- out themselves, so a restatement of the target breaks all of them at
-- once, while the point is chosen and paid for here.  The harness is
-- deliberately its own -- two slots and one lift -- so that every one
-- of them can import it, the nesting spine included.

-- WHY THE POINT IS THE ONE IT IS, and it is the premise side that
-- constrains it.  The state must be one a RUN reached, so it is the
-- subscribe's own output rather than a record written by hand.  The
-- path is a `thru-outer` frame, the one shape whose step SUBSCRIBES
-- what it is handed, so the conclusion is about a registry this fold
-- grew rather than one it passed through untouched.  And both caps are
-- read at their own least, searched upward rather than picked, since
-- every instantiation above the least is strictly easier.

-- WHICH ROWS BEAR WEIGHT.  `censusIs` is the non-vacuity witness and
-- carries the reading: the registry goes from one entry to two, so the
-- conclusion is quantified over something the fold itself put there.
-- Its cap digits are load-bearing too -- entry least at two and path
-- least at one, so the frame step the exit has to clear is five and the
-- exit is two.  `foldRow` is the tie, and it is LOAD-BEARING in that
-- margin: a registration longer than five turns it red.  NOT
-- COVERED: one path of length one, one arrival's worth of values, one
-- program.  The families -- depth, the cut, the inner's operators, the
-- duplicating frame, the separated caps, the nesting spine -- are read
-- by the modules that import this one, and their readings carry the
-- coverage.

-- TARGET: foldPath-regsLen @d58775
module Probed.Fold-Regs-Row where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; s≤s; z≤n)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx; Closed; Exp; Val; natᵗ; obs; mapᵉ; mergeAllᵉ;
  strmᵗ; input; syncSizeᵉ)
open import Rx.Prim using (Gas; InstEvent; gasPad; g0; cold; after_,_)
open import Rx.Slots using (Slots; scripted)
open import Rx.Evaluator using (Sched; EvalSt; Path; root; _↠_; thru-outer;
  mergeAllᵒ; foldPath; subscribeE; sched-init; st-init; budgetAt)
open import Rx.Hop-Depth using (hopDᵉ)
open import Rx.Slot-Hop using (slotHop)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (pathSz?; regsSz?)
open import Verify-Budget-Sufficient.Regs-Nest-Walk using (valsSz?)
open import Verify-Budget-Sufficient.Regs-Fold-Len using (foldPath-regsLen)

open import Probed.Apparatus using (Confirms)

Γ₂ : Ctx 2
Γ₂ = natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

outer : Closed Γ₂ natᵗ
outer = input fzero

inner : ∀ {Δᵍ Δ Θ} → Exp Γ₂ Δᵍ Δ Θ natᵗ
inner = input (fsuc fzero)

e₀ : Closed Γ₂ natᵗ
e₀ = mergeAllᵉ nothing (mapᵉ (strmᵗ inner) outer)

slots : Slots Γ₂
slots fzero        = scripted (cold [] ((after 0 , 7) ∷ (after 2 , 8) ∷ []))
slots (fsuc fzero) = scripted (cold [] ((after 9 , 1) ∷ []))

sub : Sched Γ₂ × EvalSt e₀
sub = let r = subscribeE
                (gasPad (suc (syncSizeᵉ e₀ + hopDᵉ 0 (slotHop 0 slots) e₀)) g0)
                e₀ root 0 0 (sched-init e₀ slots) (st-init e₀)
      in proj₁ (proj₂ r) , proj₂ (proj₂ r)

sd₀ : Sched Γ₂
sd₀ = proj₁ sub

st₀ : EvalSt e₀
st₀ = proj₂ sub

pth : Path Γ₂ (obs natᵗ) natᵗ
pth = thru-outer mergeAllᵒ 0 ↠ root

vls : List (Val Γ₂ (obs natᵗ))
vls = inner ∷ []

after : EvalSt e₀
after = proj₂ (proj₂
  (foldPath (budgetAt e₀ slots 1) 3 1 0 0 pth vls [] false sd₀ st₀))

-- the least cap at which a Boolean reading holds, searched upward from
-- zero.  Running off the fuel reports zero, which a satisfied search
-- can never return here, so an exhausted search shows in the figures
least : (ℕ → Bool) → ℕ → ℕ → ℕ
least p zero    b = 0
least p (suc f) b = if p b then b else least p f (suc b)

census : ℕ
census = length (EvalSt.registry st₀)
       + 100 * length (EvalSt.registry after)
       + 10000 * least (λ b → regsSz? b (EvalSt.registry st₀)) 400 0
       + 1000000 * least (λ b → pathSz? b pth) 400 0
       + 100000000 * least (λ b → regsSz? b (EvalSt.registry after)) 400 0

censusIs : census ≡ 201020201
censusIs = refl

-- THE POINT, NAMED PIECE BY PIECE, so a satellite writes the tie out
-- of imported names alone and its `using` clause says exactly what the
-- tie stands on.  The two caps are the leasts the census reports.
gp : Gas
gp = budgetAt e₀ slots 1

evs₀ : List (InstEvent (Val Γ₂ natᵗ))
evs₀ = []

fin₀ : Bool
fin₀ = false

le1 : 1 ≤ 1
le1 = s≤s z≤n

le2 : 1 ≤ 2
le2 = s≤s z≤n

pv : valsSz? 2 vls ≡ true
pv = refl

pp : pathSz? 1 pth ≡ true
pp = refl

pr : regsSz? 2 (EvalSt.registry st₀) ≡ true
pr = refl

foldRow : Confirms
  (foldPath-regsLen {e = e₀} gp 3 1 0 0 pth vls evs₀ fin₀ sd₀ st₀ 1 2
     le1 le2 pv pp pr)
foldRow = refl
