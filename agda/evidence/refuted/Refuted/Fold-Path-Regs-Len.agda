-- ══════════════════════════════════════════════════════════════════
-- A LINEAR GRANT CANNOT PAY A PRODUCT: THE FOLD'S DOUBLING IS FALSE.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE`
-- notes.
--
-- WHAT THE STATEMENT SAID.  One walk of a path takes a registry
-- priced under `B` to a registry priced under `B + B`, given that the
-- arriving values, the walked path and the standing registry are all
-- priced by `B`.
--
-- WHERE IT BREAKS, AND WHY IT IS ARITHMETIC RATHER THAN AN OFF-BY-ONE.
-- `B` has to dominate two independent quantities: every frame's own
-- syntax, and the length of the path.  It is therefore their MAXIMUM.
-- But a frame whose function NESTS its argument -- `d` flatten levels
-- wrapped around the incoming observable -- pushes about `d` frames of
-- its own when it subscribes, and `k` such frames compose down ONE
-- spine, so what gets registered is about `k * d`.  A maximum is
-- doubled; a product is not bounded by twice a maximum, and taking
-- `d` and `k` up together outruns the grant at any constant factor.
-- The witness below takes `d = 2` and `k = 10`: the maximum is the
-- frame syntax at `13`, the doubling therefore offers `26`, and the
-- registered chain is longer than that.  The boundary sits where that
-- arithmetic says it does rather than at one lucky program -- two
-- frames shallower fits, two more still breaks, and the same height
-- at depth three fits again because the deeper frame's own syntax has
-- raised the maximum with it.
--
-- WHY THE SIBLING SHAPE DOES NOT REFUTE, WHICH IS WHAT MAKES THE
-- NESTING ONE THE FINDING.  A frame that DUPLICATES its argument
-- rather than nesting it makes sibling copies, siblings register as
-- separate chains, and `regsSz?` is an `all` over entries -- so width
-- is free however much of it there is.  Only depth composes.
--
-- WHAT THE REPAIR HAS TO BE.  The value inflation this tree already
-- prices charges one step per FRAME, and the proven walk-face
-- siblings each carry a premise in that currency rather than in a
-- doubling.  So the fold's own conclusion belongs at the level the
-- frames it walked have reached, not at twice its entry.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Fold-Path-Regs-Len where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; foldr)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (Maybe; just; nothing; is-just)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _⊔_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Rx.Prim using (Gas; Id; Tick; Source; InstEvent; gasPad; g0;
  cold; after_,_)
open import Rx.Exp using (Ctx; Closed; Val; Exp; Fn; natᵗ; obs; ofᵉ; mapᵉ;
  mergeAllᵉ; strmᵗ; varᵗ; input; syncSizeᵉ)
open import Rx.Slots using (Slots; scripted)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; Path; foldPath;
  subscribeE; sched-init; st-init; root; sched-next; cascadeLatch;
  chainsOf; arrTy; arrVal; arrTick; arrSource; budgetAt)
open import Rx.Hop-Depth using (hopDᵉ)
open import Rx.Slot-Hop using (slotHop)
open import Verify-Budget-Sufficient.Measures using (pathLen)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (pathSz?; regsSz?)
open import Verify-Budget-Sufficient.Regs-Nest-Walk using (valsSz?)

----------------------------------------------------------------------
-- THE STATEMENT, WRITTEN OUT RATHER THAN IMPORTED.  Importing the
-- postulate would prove the tower inconsistent instead of refuting
-- anything.
----------------------------------------------------------------------
FoldPathRegsLen : Set
FoldPathRegsLen = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
  (path : Path Γ u t) (vals : List (Val Γ u))
  (evs : List (InstEvent (Val Γ t))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (B : ℕ) →
  valsSz? B vals ≡ true →
  pathSz? B path ≡ true →
  regsSz? B (EvalSt.registry st) ≡ true →
  regsSz? (B + B)
    (EvalSt.registry (proj₂ (proj₂
      (foldPath sf gas id now envSrc path vals evs fin sched st))))
    ≡ true

f≡t : false ≡ true → ⊥
f≡t ()

----------------------------------------------------------------------
-- THE PROGRAM.  Three slots: one drives the outer source, the other
-- two sit behind a late tick so nothing else is in flight when the
-- door is read.
----------------------------------------------------------------------
Γ₃ : Ctx 3
Γ₃ = natᵗ ∷ⱽ natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

outer : Closed Γ₃ natᵗ
outer = input fzero

inner : ∀ {Δᵍ Δ Θ} → Exp Γ₃ Δᵍ Δ Θ natᵗ
inner = input (fsuc fzero)

-- the nesting frame's body: `d` flatten levels wrapped around the
-- incoming observable, each one a `mergeAllᵉ` over a singleton
nest : ℕ → Exp Γ₃ [] [] (obs natᵗ ∷ []) natᵗ
nest zero    = mergeAllᵉ nothing (ofᵉ (varᵗ (here refl) ∷ []))
nest (suc d) = mergeAllᵉ nothing (ofᵉ (strmᵗ (nest d) ∷ []))

deep : ℕ → Fn Γ₃ [] [] [] (obs natᵗ) (obs natᵗ)
deep d = strmᵗ (nest d)

lifted : Closed Γ₃ (obs natᵗ)
lifted = mapᵉ (strmᵗ inner) outer

dstack : ℕ → ℕ → Closed Γ₃ (obs natᵗ) → Closed Γ₃ (obs natᵗ)
dstack d zero    s = s
dstack d (suc k) s = mapᵉ (deep d) (dstack d k s)

prog : ℕ → ℕ → Closed Γ₃ natᵗ
prog d k = mergeAllᵉ nothing (dstack d k lifted)

e₃ : Closed Γ₃ natᵗ
e₃ = prog 2 10

slots : Slots Γ₃
slots fzero               = scripted (cold [] ((after 0 , 7) ∷ (after 2 , 8) ∷ (after 0 , 9) ∷ []))
slots (fsuc fzero)        = scripted (cold [] ((after 9 , 1) ∷ []))
slots (fsuc (fsuc fzero)) = scripted (cold [] ((after 9 , 2) ∷ []))

sucG : Closed Γ₃ natᵗ → ℕ
sucG e = suc (syncSizeᵉ e + hopDᵉ 0 (slotHop 0 slots) e)

sub : Sched Γ₃ × EvalSt e₃
sub = let r = subscribeE (gasPad (sucG e₃) g0) e₃ root 0 0
                         (sched-init e₃ slots) (st-init e₃)
      in proj₁ (proj₂ r) , proj₂ (proj₂ r)

----------------------------------------------------------------------
-- THE REACHED STATE.  Everything the door is applied to is produced by
-- RUNNING -- the first arrival the scheduler hands out and the first
-- chain the registry holds for it -- so nothing here is a state
-- written by hand.  The bundle is a plain `Maybe` because the chain's
-- type depends on the arrival, and `reached` is what discharges the
-- branches the run never takes.
----------------------------------------------------------------------
Bundle : Set
Bundle = Σ (Arrival Γ₃) (λ a → Sched Γ₃ × Path Γ₃ (arrTy a) natᵗ × EvalSt e₃)

bundle? : Maybe Bundle
bundle? with sched-next (proj₁ sub)
... | inj₁ _         = nothing
... | inj₂ (a , s) with chainsOf a (proj₂ sub)
...   | []            = nothing
...   | (rid , c) ∷ _ =
        just (a , s , c , record (cascadeLatch a (proj₂ sub)) { delivered = rid ∷ [] })

reached : is-just bundle? ≡ true
reached = refl

get : (m : Maybe Bundle) → is-just m ≡ true → Bundle
get (just b) _ = b
get nothing ()

bnd : Bundle
bnd = get bundle? reached

a₁ : Arrival Γ₃
a₁ = proj₁ bnd

s₁ : Sched Γ₃
s₁ = proj₁ (proj₂ bnd)

chain : Path Γ₃ (arrTy a₁) natᵗ
chain = proj₁ (proj₂ (proj₂ bnd))

st₀ : EvalSt e₃
st₀ = proj₂ (proj₂ (proj₂ bnd))

----------------------------------------------------------------------
-- THE READING.  `B` is the smallest cap that prices the arrival, the
-- walked chain and the standing registry together -- it is pinned by
-- the three premises below, each of which is a `refl`.
----------------------------------------------------------------------
B : ℕ
B = 13

after : EvalSt e₃
after = proj₂ (proj₂ (foldPath (budgetAt e₃ (Sched.slots s₁) 1) 3 1
                       (arrTick a₁) (arrSource a₁) chain (arrVal a₁ ∷ [])
                       [] false s₁ st₀))

entryVals : valsSz? {Γ = Γ₃} {s = arrTy a₁} B (arrVal a₁ ∷ []) ≡ true
entryVals = refl

entryPath : pathSz? B chain ≡ true
entryPath = refl

entryRegs : regsSz? B (EvalSt.registry st₀) ≡ true
entryRegs = refl

-- what the walk actually leaves behind.  `regsSz?` is an `all`, so
-- only the LONGEST registered chain can break the length conjunct --
-- which is why the figure is a maximum and not a sum, and why the
-- width the sibling shape produces never appears here at all.
longest : EvalSt e₃ → ℕ
longest s = foldr (λ en m → pathLen (proj₂ (proj₂ (proj₂ en))) ⊔ m) 0
                  (EvalSt.registry s)

entryLongest exitLongest : ℕ
entryLongest = longest st₀
exitLongest  = longest after

-- the walked chain and the standing registry both sit inside the cap;
-- what the step registers does not sit inside twice it
figures : entryLongest + 100 * pathLen chain + 10000 * exitLongest ≡ 311212
figures = refl

exitRow : Bool
exitRow = regsSz? (B + B) (EvalSt.registry after)

exitRow≡false : exitRow ≡ false
exitRow≡false = refl

fold-path-regs-len-absurd : FoldPathRegsLen → ⊥
fold-path-regs-len-absurd pr =
  f≡t (trans (sym exitRow≡false)
             (pr {e = e₃} (budgetAt e₃ (Sched.slots s₁) 1) 3 1
                 (arrTick a₁) (arrSource a₁) chain (arrVal a₁ ∷ [])
                 [] false s₁ st₀ B entryVals entryPath entryRegs))
