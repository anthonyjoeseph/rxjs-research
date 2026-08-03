------------------------------------------------------------------
-- THE REFUTATION OF `stepFrame-entry-caps`, by the very witness its
-- own comment asked for: "ONE frame, run under `capsOK? c` with a
-- chain inside `pathSz? cSize` and a burst inside `valsCaps? c sl`,
-- whose post-state breaches `capsOK? c` (for the first) or adds more
-- than `cSize * suc cWid` registrations (for the second)".
--
-- It is the SECOND conjunct that falls, and it falls on the cheapest
-- frame there is — a `map-f`, which touches no state at all.  A map
-- frame's output is `map (applyFn fn) vals`, and `applyFn` GROWS a
-- value: the doubling term `pairᵗ x x` has size 3, and it takes a
-- payload of size 3 to a payload of size 7.  So with `cSize c = 3`
-- every hypothesis holds by `refl` and the conclusion is `false ≡ true`.
--
-- This is the same fact `frameStep`'s own header states — "same-level
-- preservation is false, so the face must report growth, and the honest
-- index of growth inside a frame is the fold count" — and the same fact
-- `caps-frame-boundary-absurd` proves in the abstract, and the same fact
-- .Wet's cascadeGo-wet names ("a fixed-bound start @ level L → land @
-- level L step statement is FALSE over its full quantification").  The
-- entry axiom asserts same-level preservation.
--
-- WHAT IT COST, AND WHAT REPLACED IT.  `cascadeGo-deliveries` was
-- ground on this axiom and on `stepFrame-entry-mint`, via `walkH` — so
-- it was not a theorem, and the 2026-08-02 entry-charging ruling was
-- refuted rather than unproven.  Both axioms and that instantiation are
-- GONE from .Caps-Face; this module is the reason, and it is what keeps
-- them from coming back.
--
-- THE REPAIR IS LANDED, and it is the one this refutation dictates: the
-- walk now carries the LEVEL (`dCapᶜ` / `dWalkᶜ`, .Caps), `Walk-Hyps` is
-- level-indexed, and the frame face it asks for — `stepFrame-face` — is
-- the shape the PROVEN `stepFrame-caps` already reports in, `Σ j′ →
-- j′ ≤ fCharge × capsOK? (frameStep (j + j′) c) …`.  The witness below
-- satisfies THAT face with room: the map-f frame's receipt is
-- `suc (sizeᵗ dup) = 4` inside `fCharge 3 1 0 = 9`, and its size-7
-- output sits inside `cSize (frameStep 4 c₀) = 4665`.  Growth reported
-- is growth paid for; growth denied is what falls below.
--
-- AND THE CIRCLE THE OLD REPAIR-SHAPE FEARED DOES NOT BITE.  The worry
-- was that at a ledger read at `frameStep j c` the per-frame receipt's
-- two factors both grow with j, while `sizeCount` (which DEFINES the
-- growth) is what the sum of the j′s must fit inside.  It does not bite
-- because the walk is a RECURSION rather than a closed form: `dLvl`
-- iterates the receipt at the level each frame actually runs at, and
-- `sizeCount` reads the walk instead of bounding it.
--
-- AND THE FIRST CONJUNCT COULD NOT STAND EITHER, though the witness
-- below does not exhibit it: `capsOK? c`'s fifth conjunct is
-- `length registry ≤ᵇ cReg c`, and `stepFrame-entry-mint` — the axiom
-- beside it — granted each frame up to `cSize * suc cWid` NEW
-- registrations.  The two are jointly satisfiable only where no frame
-- ever mints, and Frame-Mint-Probe measured frames minting 1 on every
-- row of the amplifier family.  The registry is read off the LEVEL now
-- (`regAt S R J`, capsOK?'s own conjunct), so there is nothing left to
-- charge at entry.
------------------------------------------------------------------
module Entry-Caps-Refuted where

open import Data.Nat  using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Fin  using (Fin)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Vec  using (Vec) renaming ([] to []ᵛ)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; Id; Tick)
open import Rx.Exp  using (Ty; Ctx; Closed; Val; Fn; Tm; natᵗ; _×ᵗ_;
                           varᵗ; pairᵗ; emptyᵉ; sizeᵗ; sizeᵛ)
open import Rx.Evaluator using (Slots; Sched; EvalSt; sched-init; st-init;
                                Frame; map-f; Path; root; _↠_; stepFrame)
open import Verify-Budget-Sufficient.Caps-Face
  using (Caps; caps; capsOK?; pathSz?; valsCaps?)

------------------------------------------------------------------
-- the smallest possible world: no slots, so the state predicate is
-- five empty conjuncts
------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ᵛ

ins : Slots Γ₀
ins ()

S : Ty                         -- the payload type: a value of size 3
S = natᵗ ×ᵗ natᵗ

T : Ty                         -- the root type: its double, size 7
T = S ×ᵗ S

e₀ : Closed Γ₀ T
e₀ = emptyᵉ

sched₀ : Sched Γ₀
sched₀ = sched-init e₀ ins

st₀ : EvalSt e₀
st₀ = st-init e₀

-- `λ x → (x , x)`: size 3, and it doubles the size of its argument
dup : Fn Γ₀ [] [] [] S T
dup = pairᵗ (varᵗ (here refl)) (varᵗ (here refl))

v₀ : Val Γ₀ S
v₀ = 0 , 0

c₀ : Caps
c₀ = caps 3 1 1

-- the numbers, so the row is readable rather than implicit
_ : sizeᵗ dup ≡ 3
_ = refl

_ : sizeᵛ {Γ = Γ₀} S v₀ ≡ 3
_ = refl

_ : sizeᵛ {Γ = Γ₀} T (v₀ , v₀) ≡ 7
_ = refl

-- every hypothesis of the axiom, at these arguments, by computation
hSlots : Sched.slots sched₀ ≡ ins
hSlots = refl

hOK : capsOK? c₀ sched₀ st₀ ≡ true
hOK = refl

hPath : pathSz? (Caps.cSize c₀) (map-f dup ↠ root) ≡ true
hPath = refl

hVals : valsCaps? c₀ ins (v₀ ∷ []) ≡ true
hVals = refl

-- and the conclusion it would give, at these arguments, by computation
hOut : valsCaps? c₀ ins
         (proj₁ (stepFrame {e = e₀} g0 0 0 (map-f dup) root (v₀ ∷ []) false
                           sched₀ st₀))
         ≡ false
hOut = refl

------------------------------------------------------------------
-- the axiom, transcribed verbatim from .Caps-Face, and the ⊥
------------------------------------------------------------------

Entry-Caps : Set
Entry-Caps = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (c : Caps) (sl : Slots Γ) (g : Gas) (id : Id) (now : Tick)
  (f : Frame Γ s u) (κ : Path Γ u t) (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? c sched st ≡ true →
  pathSz? (Caps.cSize c) (f ↠ κ) ≡ true →
  valsCaps? c sl vals ≡ true →
  let r = stepFrame g id now f κ vals fin sched st
  in (capsOK? c (proj₁ (proj₂ (proj₂ (proj₂ r))))
                (proj₂ (proj₂ (proj₂ (proj₂ r)))) ≡ true)
     × (valsCaps? c sl (proj₁ r) ≡ true)

entry-caps-absurd : Entry-Caps → ⊥
entry-caps-absurd H
  with proj₂ (H {e = e₀} c₀ ins g0 0 0 (map-f dup) root (v₀ ∷ []) false
                sched₀ st₀ refl refl refl refl)
... | ()

------------------------------------------------------------------
-- LEG 0, THE NAMED OPEN MEASUREMENT — ANSWERED, AND IT IS NOT THE
-- WIDTH CONJUNCT THAT BREAKS.
--
-- The question at the axiom was: the deepening-scan family hands one
-- frame 120 payloads at cascade 1, and `valsCaps?`'s width conjunct is
-- `length vals ≤ suc cWid` read at the cascade's ENTRY caps — does
-- `capsAt`'s cWid at cascade 1's entry dominate 120?  `capsAt` is a
-- tower and does not normalise there, so it was open.
--
-- It does, with eleven orders of margin, and the argument needs no
-- normalisation at all: cascade (suc id)'s entry cWid is
-- `iterFold S (sizeCount c) W`, `sizeCount c` is at least 2 whenever
-- there is one registration to walk, and TWO rungs of iterFold already
-- put the width at `S ^ suc (S ^ suc W) ≥ 4 ^ 5 = 1024`.  The width
-- conjunct is not close to tight either.
--
-- So the entry axiom does not fail on the axis it was flagged on.  It
-- fails on the SIZE axis, at cascade 0, on one payload — above.
------------------------------------------------------------------

open import Data.Nat using (_+_; _*_; _^_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; ≤-refl; ≤-reflexive;
                                       *-identityʳ; *-identityˡ; *-monoʳ-≤; *-monoˡ-≤;
                                       ^-monoˡ-≤; ≤ᵇ⇒≤)
open import Relation.Binary.PropositionalEquality using (sym)
open import Data.Unit using (tt)
open import Rx.Evaluator using (iterFold; foldStep)
open import Verify-Budget-Sufficient.Caps
  using (frameBlowup; frameStep; sizeCount; 2≤sizeCount;
         iterFold-mono-count)
open import Verify-Budget-Sufficient.Caps-Face using (powʳ1)

-- TWO RUNGS ARE ALREADY 1024
wid-dominates-120 : ∀ (c : Caps) → 4 ≤ Caps.cSize c → 1 ≤ Caps.cReg c →
  120 ≤ Caps.cWid (frameBlowup c)
wid-dominates-120 c 4≤S 1≤R =
  ≤-trans two-rungs
          (iterFold-mono-count (Caps.cSize c) (Caps.cWid c) 2≤S
             (2≤sizeCount c 2≤S 1≤R))
  where
  Sz = Caps.cSize c
  Wd = Caps.cWid c
  2≤S : 2 ≤ Sz
  2≤S = ≤-trans (s≤s (s≤s z≤n)) 4≤S
  1≤S : 1 ≤ Sz
  1≤S = ≤-trans (s≤s z≤n) 4≤S
  S≤S^ : Sz ≤ Sz ^ suc Wd
  S≤S^ = ≤-trans (≤-reflexive (sym (*-identityʳ Sz)))
                 (*-monoʳ-≤ Sz (powʳ1 Sz 1≤S (z≤n {Wd})))
  5≤ : 5 ≤ suc (Sz ^ suc Wd)
  5≤ = s≤s (≤-trans 4≤S S≤S^)
  two-rungs : 120 ≤ iterFold Sz 2 Wd
  two-rungs = ≤-trans (≤ᵇ⇒≤ 120 1024 tt)
                (≤-trans (^-monoˡ-≤ 5 4≤S) (powʳ1 Sz 1≤S 5≤))
