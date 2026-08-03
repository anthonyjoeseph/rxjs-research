------------------------------------------------------------------
-- THE SHARE-LADDER COUNT PROBE: at WHICH LEVEL is a subscribe burst's
-- EMIT COUNT bounded?
--
-- `subscribeE-count` (.Subscribe-Face) was stated at the ENTRY level
-- `frameStep j c`, on the reasoning that `widAt` is monotone in j so an
-- entry bound implies the exit bound the charge side (Sub-Charge-Probe
-- § 5's `op-step`) actually consumes, and a sibling at entry costs no
-- existential threading.  The reasoning about `widAt` is right; the
-- statement is FALSE.
--
-- WHY.  Every clause of `subscribeE` is emit-for-emit — `pushBurst`
-- conses one envelope per input emit and the leaves mint exactly one —
-- with ONE exception: `sharedConnect` PREPENDS its own `init` envelope
-- onto the def's whole burst.  So a ladder of shares, each slot's def
-- being the next slot, hands back one emit PER CONNECT plus the leaf's:
-- k nested shares ⟹ k+1 emits, and NOTHING in the entry hypotheses
-- bounds k.  `slotsCaps?` bounds each slot's def POINTWISE (`sizeᵉ d ≤
-- cSize`, `pWᵉ d ≤ cWid`), never the telescope's length, and a share
-- ladder keeps every pointwise number at 1 however long it gets.
--
-- THE EXIT LEVEL IS FINE, and that is the repair rather than a
-- weakening: `sharedConnect-caps` reports `suc j₂` — one fold PER
-- CONNECT — so a k-deep ladder leaves at level `j + k`, and
-- `widAt S W (j+k) = iterFold S (j+k) W` with `foldStep S w = S ^ suc w`
-- clears k+1 after two rungs (S ≥ 2 ⟹ widAt ≥ 2 ^ suc (2 ^ suc W)).
-- The count face therefore has to SHARE `subscribeE-caps`'s existential
-- — a third conjunct of its Σ, not a sibling lemma.
--
-- The row below is the smallest witness: THREE shares over a spent
-- scripted leaf, at `c = caps 2 1 1` (the smallest caps the hypotheses
-- admit for this telescope), `j = 0`.  Every hypothesis of the entry
-- statement holds by `refl`; the conclusion computes to `false`.
------------------------------------------------------------------
module Share-Count-Probe where

open import Data.Nat  using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; length)
open import Data.Fin  using (Fin; zero; suc)
open import Data.Empty using (⊥)
open import Data.Product using (proj₁)
open import Data.Vec  using (Vec) renaming (_∷_ to _∷ᵛ_; [] to []ᵛ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gs; Id; Tick; ObservableInput; cold)
open import Rx.Exp  using (Ctx; Closed; Val; natᵗ; input; sizeᵉ)
open import Rx.Evaluator using (Slots; scripted; shared; Sched; EvalSt;
                                sched-init; st-init; Path; root; Stream;
                                subscribeE)
open import Rx.Frame-Width using (dWᵉ)
open import Verify-Budget-Sufficient.Caps
  using (Caps; caps; frameStep)
open import Verify-Budget-Sufficient.Caps-Face
  using (capsOK?; pathSz?; slotsCaps?; burstCount?; pathLen)

------------------------------------------------------------------
-- FOUR SLOTS, three of them a ladder of shares over a spent leaf
------------------------------------------------------------------

Γ₄ : Ctx 4
Γ₄ = natᵗ ∷ᵛ natᵗ ∷ᵛ natᵗ ∷ᵛ natᵗ ∷ᵛ []ᵛ

leaf : ObservableInput (Val Γ₄ natᵗ)
leaf = cold [] []

sl : Slots Γ₄
sl zero                      = shared (input (suc zero))
sl (suc zero)                = shared (input (suc (suc zero)))
sl (suc (suc zero))          = shared (input (suc (suc (suc zero))))
sl (suc (suc (suc zero)))    = scripted leaf
sl (suc (suc (suc (suc ()))))

prog : Closed Γ₄ natᵗ
prog = input zero

sched₀ : Sched Γ₄
sched₀ = sched-init prog sl

st₀ : EvalSt prog
st₀ = st-init prog

fuel : Gas
fuel = gs (gs (gs (gs (gs g0))))

burst : Stream Γ₄ natᵗ
burst = proj₁ (subscribeE fuel prog root 0 0 sched₀ st₀)

-- FOUR EMITS: one per connect, plus the leaf's one-shot
_ : length burst ≡ 4
_ = refl

------------------------------------------------------------------
-- THE SMALLEST CAPS THE ENTRY HYPOTHESES ADMIT.  cSize 2 is forced by
-- `2 ≤ cSize`; cWid 1 is forced by `slotsCaps?` (each def is `input k`,
-- whose pWᵉ and innWᵉ are 1); cReg 1 by `1 ≤ cReg`
------------------------------------------------------------------

c₀ : Caps
c₀ = caps 2 1 1

_ : Caps.cWid (frameStep 0 c₀) ≡ 1
_ = refl

-- every hypothesis of `subscribeE-count`, at j = 0, by computation
h2≤S : 2 ≤ Caps.cSize c₀
h2≤S = s≤s (s≤s z≤n)

h1≤R : 1 ≤ Caps.cReg c₀
h1≤R = s≤s z≤n

hSlots : Sched.slots sched₀ ≡ sl
hSlots = refl

hSlotsCaps : slotsCaps? (Caps.cSize c₀) (Caps.cWid c₀) sl ≡ true
hSlotsCaps = refl

hOK : capsOK? (frameStep 0 c₀) sched₀ st₀ ≡ true
hOK = refl

hSize : sizeᵉ prog ≤ Caps.cSize (frameStep 0 c₀)
hSize = s≤s z≤n

hWid : dWᵉ 4 sl prog ≤ Caps.cWid (frameStep 0 c₀)
hWid = z≤n

hPath : pathSz? (Caps.cSize (frameStep 0 c₀)) (root {Γ = Γ₄} {t = natᵗ}) ≡ true
hPath = refl

hLen : suc (pathLen (root {Γ = Γ₄} {t = natᵗ})) ≤ Caps.cSize (frameStep 0 c₀)
hLen = s≤s z≤n

-- AND THE CONCLUSION IS FALSE: 4 emits against `suc (cWid) = 2`
hCount : burstCount? {Γ = Γ₄} {u = natᵗ} (frameStep 0 c₀) burst ≡ false
hCount = refl

------------------------------------------------------------------
-- the entry statement, transcribed verbatim from .Subscribe-Face, and
-- the ⊥ it yields
------------------------------------------------------------------

Entry-Count : Set
Entry-Count = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (j : ℕ) (g : Gas) (b : Closed Γ u) (κ : Path Γ u t)
  (bid : Id) (now : Tick) (sl′ : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Sched.slots sched ≡ sl′ →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl′ ≡ true →
  capsOK? (frameStep j c) sched st ≡ true →
  sizeᵉ b ≤ Caps.cSize (frameStep j c) →
  dWᵉ n sl′ b ≤ Caps.cWid (frameStep j c) →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  burstCount? (frameStep j c) (proj₁ (subscribeE g b κ bid now sched st))
    ≡ true

entry-count-absurd : Entry-Count → ⊥
entry-count-absurd H
  with H {e = prog} c₀ 0 fuel prog root 0 0 sl sched₀ st₀
         h2≤S h1≤R hSlots hSlotsCaps hOK hSize hWid hPath hLen
... | ()

------------------------------------------------------------------
-- AND THE LADDER SCALES: nothing in the hypotheses moves as it grows.
-- `slotsCaps? 2 1 sl` stays `true` at every rung — each def is one
-- `input`, so every pointwise measure the predicate reads is 1 — while
-- the emit count is the rung count plus one.  A five-slot telescope
-- (four shares) is five emits against the same `suc (cWid) = 2`
------------------------------------------------------------------

Γ₅ : Ctx 5
Γ₅ = natᵗ ∷ᵛ natᵗ ∷ᵛ natᵗ ∷ᵛ natᵗ ∷ᵛ natᵗ ∷ᵛ []ᵛ

leaf₅ : ObservableInput (Val Γ₅ natᵗ)
leaf₅ = cold [] []

sl₅ : Slots Γ₅
sl₅ zero                          = shared (input (suc zero))
sl₅ (suc zero)                    = shared (input (suc (suc zero)))
sl₅ (suc (suc zero))              = shared (input (suc (suc (suc zero))))
sl₅ (suc (suc (suc zero)))        = shared (input (suc (suc (suc (suc zero)))))
sl₅ (suc (suc (suc (suc zero))))  = scripted leaf₅
sl₅ (suc (suc (suc (suc (suc ())))))

prog₅ : Closed Γ₅ natᵗ
prog₅ = input zero

sched₅ : Sched Γ₅
sched₅ = sched-init prog₅ sl₅

st₅ : EvalSt prog₅
st₅ = st-init prog₅

burst₅ : Stream Γ₅ natᵗ
burst₅ = proj₁ (subscribeE (gs (gs (gs (gs (gs (gs g0))))))
                  prog₅ root 0 0 sched₅ st₅)

_ : length burst₅ ≡ 5
_ = refl

-- the SAME caps, every hypothesis still `refl`, the count one higher
_ : slotsCaps? (Caps.cSize c₀) (Caps.cWid c₀) sl₅ ≡ true
_ = refl

_ : capsOK? (frameStep 0 c₀) sched₅ st₅ ≡ true
_ = refl

_ : pathSz? (Caps.cSize (frameStep 0 c₀)) (root {Γ = Γ₅} {t = natᵗ}) ≡ true
_ = refl

_ : burstCount? {Γ = Γ₅} {u = natᵗ} (frameStep 0 c₀) burst₅ ≡ false
_ = refl

entry-count-absurd₅ : Entry-Count → ⊥
entry-count-absurd₅ H
  with H {e = prog₅} c₀ 0 (gs (gs (gs (gs (gs (gs g0)))))) prog₅ root 0 0
         sl₅ sched₅ st₅
         h2≤S h1≤R refl refl refl (s≤s z≤n) z≤n refl (s≤s z≤n)
... | ()

------------------------------------------------------------------
-- AND THE POSITIVE HALF: THE EXIT LEVEL IS NOT MERELY UNREFUTED, IT IS
-- ROOMY.  `sharedConnect-caps` pays one fold PER CONNECT, so the three-
-- rung row leaves at `0 + 3` and the four-rung row at `0 + 4`.  ONE fold
-- already covers both: `frameStep 1 (caps 2 1 1)` is `caps 10 4 3`, so
-- `suc cWid` is 5 against emit counts of 4 and 5.  Two more folds and the
-- bound is `suc (2 ^ 33)`.  That is the margin the third conjunct buys,
-- and it is why the repair is the exit level rather than a weaker
-- predicate
------------------------------------------------------------------

_ : frameStep 1 c₀ ≡ caps 10 4 3
_ = refl

_ : burstCount? {Γ = Γ₄} {u = natᵗ} (frameStep 1 c₀) burst ≡ true
_ = refl

_ : burstCount? {Γ = Γ₅} {u = natᵗ} (frameStep 1 c₀) burst₅ ≡ true
_ = refl
