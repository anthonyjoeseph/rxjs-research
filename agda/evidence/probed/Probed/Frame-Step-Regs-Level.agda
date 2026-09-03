-- ══════════════════════════════════════════════════════════════════
-- ONE FRAME'S REGISTRY STEP, INSTANTIATED AT THE SUBSCRIBING FRAME --
-- the only frame kind that can grow the registry at all, driven to
-- the longest chain and the largest inner its own premises admit.
--
-- PROBE: `refl` rows at concrete programs.  Not a theorem; see
-- EVIDENCE.md for what a probe may and may not be read as.
-- TARGET: stepFrame-regsSz @4069f2
--
-- WHY THIS SHAPE IS THE RISKY ONE.  Four of the five frame kinds
-- return the state they were handed, so the conclusion is the premise
-- and no instantiation of them can fail.  A `thru-outer` subscribes
-- the observable it received, and that subscribe REGISTERS: the
-- walked path with a `from-inner` head pushed on, under one frame per
-- operator of the inner.  So the registered chain is longer than
-- anything the premises directly measure, and the question the rows
-- answer is whether ONE level of `sizeStep` covers the sum.
--
-- WHAT THE ROWS DRIVE, AND WHY A HAND-BUILT STATE IS IN SCOPE HERE.
-- The statement quantifies over an arbitrary `st` under three size
-- premises and no reachability premise, so a state assembled by
-- `installNode` is an instance of it by construction -- and a state
-- meeting the premises whose row came out `false` would refute it
-- outright.  Each load-bearing row therefore pins all three premises
-- `true` and pushes both measured quantities to the boundary the
-- premises allow: the walked path at the longest length `pathSz?`
-- admits, the inner at the largest syntax `valsSz?` admits.
--
-- WHAT THE MARGIN TURNED OUT TO BE, which is the part worth carrying
-- forward.  Every operator costs at least TWO in `sizeᵉ` (its own
-- node plus a term of size at least one) and pushes at most ONE
-- frame, so an inner admitted at level `L` contributes at most
-- `(L-1)/2` frames while the walked path contributes at most `L-1`.
-- One level buys `S * suc (2 * L)`, which at `S = 1` is `2L+1`
-- against a registered length of about `3L/2`.  The margin is
-- therefore LINEAR in the level and not a constant, so no row at any
-- reachable size sits near the edge -- which is why the rows below
-- report the slack as a figure rather than merely reporting `true`.
-- ══════════════════════════════════════════════════════════════════
module Probed.Frame-Step-Regs-Level where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (nothing)
open import Data.Product using (proj₂; _×_)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Data.Fin using () renaming (zero to fzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (g0; gs; hot; Source)
open import Rx.Exp using (Ctx; Closed; Val; natᵗ; obs; emptyᵉ; input; takeᵉ; nat̂; sizeᵛ)
open import Rx.Slots using (Slots; scripted)
open import Rx.Evaluator using (EvalSt; thru-outer; take-f; Path; root; _↠_; stepFrame; sched-init; st-init; iterSize;
  mergeAllᵒ; mergeAll-st; scan-st; installNode; register; RegId; Chain)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (pathSz?; regsSz?)
open import Verify-Budget-Sufficient.Measures using (pathLen)
open import Verify-Budget-Sufficient.Regs-Nest-Walk using (valsSz?; stepFrame-regsSz)

open import Probed.Apparatus using (Confirms)

----------------------------------------------------------------------
-- ONE SCRIPTED SLOT, live and unspent, so the inner's leaf registers
-- rather than closing immediately.
----------------------------------------------------------------------
Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

sl₁ : Slots Γ₁
sl₁ fzero = scripted (hot [])

e₀ : Closed Γ₁ natᵗ
e₀ = emptyᵉ

-- THE WALKED PATH, at a chosen length.  `take-f` is charged nothing by
-- `frameSz?` and its node is never consulted on this step, so the
-- length is the only quantity these frames contribute -- which is what
-- makes them the right filler for driving `pathLen` to its ceiling.
κ : ℕ → Path Γ₁ natᵗ natᵗ
κ zero    = root
κ (suc k) = take-f 9 ↠ κ k

-- THE INNER, at a chosen operator count.  `sizeᵉ (takeᵉ c e)` is
-- `suc (sizeᵗ c + sizeᵉ e)` and `nat̂` costs one, so this is `2k+1` at
-- `k` operators -- the cheapest frame-per-size ratio the syntax
-- offers, and therefore the worst case for the statement.
inner : ℕ → Closed Γ₁ natᵗ
inner zero    = input fzero
inner (suc k) = takeᵉ (nat̂ 5) (inner k)

-- THE STATE: a `mergeAll-st` at node 0, unlimited and idle, so
-- `thruConsume` takes its subscribing arm.
st₀ : EvalSt e₀
st₀ = installNode 0 (mergeAll-st {Γ = Γ₁} {t = natᵗ} nothing 0 [] false)
        (st-init e₀)

-- THE QUANTITY THE CONCLUSION IS ABOUT, read off the registry rather
-- than inferred from the inputs.  `regsSz?` prices each entry's own
-- path, so a row reporting only the walked length and the inner's
-- size would be claiming a boundary it never measured.
regLens : List (RegId × Source × Chain Γ₁ natᵗ) → List ℕ
regLens []        = []
regLens (en ∷ r) = pathLen (proj₂ (proj₂ (proj₂ en))) ∷ regLens r

post : ℕ → List (Val Γ₁ (obs natᵗ)) → EvalSt e₀ → EvalSt e₀
post kκ vals st =
  proj₂ (proj₂ (proj₂ (proj₂
    (stepFrame {e = e₀} (gs (gs g0)) 0 0 (thru-outer mergeAllᵒ 0)
               (κ kκ) vals false (sched-init e₀ sl₁) st))))

----------------------------------------------------------------------
-- ROW A — LOAD-BEARING.  `S = 1, j = 2`: the level in hand is 7 and
-- one step buys 15.  The walked path is 6 frames, the ceiling
-- `pathSz? 7` allows; the inner is 3 operators at size 7, the ceiling
-- `valsSz? 7` allows.  The registered chain is `6 + 1 + 3 = 10`, so
-- the row fails if one level buys anything under 11.
----------------------------------------------------------------------
premA₁ : valsSz? {Γ = Γ₁} {s = obs natᵗ} (iterSize 1 2 1) (inner 3 ∷ []) ≡ true
premA₁ = refl

premA₂ : pathSz? (iterSize 1 2 1) (thru-outer {Γ = Γ₁} mergeAllᵒ 0 ↠ κ 6) ≡ true
premA₂ = refl

premA₃ : regsSz? (iterSize 1 2 1) (EvalSt.registry st₀) ≡ true
premA₃ = refl

-- LOAD-BEARING FIGURES: the level in hand, the level one step buys,
-- the inner's syntax size, the walked length, and the length of the
-- chain the subscribe actually registered.  Any of the five moving
-- fails this line by name, so the row cannot be read as covering a
-- shorter registration than it claims.
figuresA : List ℕ
figuresA =
    iterSize 1 2 1
  ∷ iterSize 1 3 1
  ∷ sizeᵛ {Γ = Γ₁} (obs natᵗ) (inner 3)
  ∷ pathLen (κ 6)
  ∷ length (EvalSt.registry (post 6 (inner 3 ∷ []) st₀))
  ∷ regLens (EvalSt.registry (post 6 (inner 3 ∷ []) st₀))

figuresA≡ : figuresA ≡ 7 ∷ 15 ∷ 7 ∷ 6 ∷ 1 ∷ 10 ∷ []
figuresA≡ = refl

rowA : regsSz? (iterSize 1 3 1) (EvalSt.registry (post 6 (inner 3 ∷ []) st₀))
         ≡ true
rowA = refl

----------------------------------------------------------------------
-- ROW B — LOAD-BEARING, at the smallest level the premises admit.
-- `S = 1, j = 0`: the level is 1, so the walked path must be `root`
-- and the inner must be a bare leaf.  One step buys 3 against a
-- registered length of 1, so this row fails if the `from-inner` head
-- is charged more than twice what the level pays for.
----------------------------------------------------------------------
premB₁ : valsSz? {Γ = Γ₁} {s = obs natᵗ} (iterSize 1 0 1) (inner 0 ∷ []) ≡ true
premB₁ = refl

premB₂ : pathSz? (iterSize 1 0 1) (thru-outer {Γ = Γ₁} mergeAllᵒ 0 ↠ κ 0) ≡ true
premB₂ = refl

figuresB : List ℕ
figuresB =
    iterSize 1 0 1
  ∷ iterSize 1 1 1
  ∷ sizeᵛ {Γ = Γ₁} (obs natᵗ) (inner 0)
  ∷ length (EvalSt.registry (post 0 (inner 0 ∷ []) st₀))
  ∷ regLens (EvalSt.registry (post 0 (inner 0 ∷ []) st₀))

figuresB≡ : figuresB ≡ 1 ∷ 3 ∷ 1 ∷ 1 ∷ 1 ∷ []
figuresB≡ = refl

rowB : regsSz? (iterSize 1 1 1) (EvalSt.registry (post 0 (inner 0 ∷ []) st₀))
         ≡ true
rowB = refl

----------------------------------------------------------------------
-- ROW C — LOAD-BEARING, one level up, to read the margin's GROWTH
-- rather than its value.  `S = 1, j = 3`: the level is 15, buying 31,
-- against a registered chain of `14 + 1 + 7 = 22`.  Against row A's
-- 10 against 15, the slack has gone from 4 to 8 while the level
-- doubled -- which is the linear margin the header states, and is
-- what rules out a crossing at any larger size.
----------------------------------------------------------------------
premC₁ : valsSz? {Γ = Γ₁} {s = obs natᵗ} (iterSize 1 3 1) (inner 7 ∷ []) ≡ true
premC₁ = refl

premC₂ : pathSz? (iterSize 1 3 1) (thru-outer {Γ = Γ₁} mergeAllᵒ 0 ↠ κ 14) ≡ true
premC₂ = refl

figuresC : List ℕ
figuresC =
    iterSize 1 3 1
  ∷ iterSize 1 4 1
  ∷ sizeᵛ {Γ = Γ₁} (obs natᵗ) (inner 7)
  ∷ pathLen (κ 14)
  ∷ regLens (EvalSt.registry (post 14 (inner 7 ∷ []) st₀))

figuresC≡ : figuresC ≡ 15 ∷ 31 ∷ 15 ∷ 14 ∷ 22 ∷ []
figuresC≡ = refl

rowC : regsSz? (iterSize 1 4 1) (EvalSt.registry (post 14 (inner 7 ∷ []) st₀))
         ≡ true
rowC = refl

----------------------------------------------------------------------
-- ROW D — LOAD-BEARING at `S = 2`, since every quantity in the
-- statement is read at `iterSize S j S` and the count `S` moves both
-- the level and what a step buys.  `j = 1`: the level is 10, one step
-- buys 42, the chain is `9 + 1 + 4 = 14`.
----------------------------------------------------------------------
premD₁ : valsSz? {Γ = Γ₁} {s = obs natᵗ} (iterSize 2 1 2) (inner 4 ∷ []) ≡ true
premD₁ = refl

premD₂ : pathSz? (iterSize 2 1 2) (thru-outer {Γ = Γ₁} mergeAllᵒ 0 ↠ κ 9) ≡ true
premD₂ = refl

figuresD : List ℕ
figuresD = iterSize 2 1 2 ∷ iterSize 2 2 2 ∷ sizeᵛ {Γ = Γ₁} (obs natᵗ) (inner 4)
  ∷ regLens (EvalSt.registry (post 9 (inner 4 ∷ []) st₀))

figuresD≡ : figuresD ≡ 10 ∷ 42 ∷ 9 ∷ 14 ∷ []
figuresD≡ = refl

rowD : regsSz? (iterSize 2 2 2) (EvalSt.registry (post 9 (inner 4 ∷ []) st₀))
         ≡ true
rowD = refl

----------------------------------------------------------------------
-- ROW E — LOAD-BEARING: SEVERAL inners in one step.  `thruWalk` folds
-- the value list, so a step can register once per arriving value and
-- the registry grows by three here.  The premises bound each value
-- separately and nothing in the statement bounds the LIST's length,
-- so this is the arm where an accounting that charged the list rather
-- than the value would show.
----------------------------------------------------------------------
valsE : List (Val Γ₁ (obs natᵗ))
valsE = inner 3 ∷ inner 3 ∷ inner 3 ∷ []

premE₁ : valsSz? {Γ = Γ₁} {s = obs natᵗ} (iterSize 1 2 1) valsE ≡ true
premE₁ = refl

figuresE : List ℕ
figuresE = length (EvalSt.registry (post 6 valsE st₀))
  ∷ regLens (EvalSt.registry (post 6 valsE st₀))

figuresE≡ : figuresE ≡ 3 ∷ 10 ∷ 10 ∷ 10 ∷ []
figuresE≡ = refl

rowE : regsSz? (iterSize 1 3 1) (EvalSt.registry (post 6 valsE st₀)) ≡ true
rowE = refl

----------------------------------------------------------------------
-- ROW F — LOAD-BEARING: the registry is NOT empty on the way in, so
-- the conclusion has to widen the entries already there as well as
-- price the new one.  The pre-loaded chain is at the incoming
-- ceiling, so a conclusion that failed to widen would fail here.
----------------------------------------------------------------------
stF : EvalSt e₀
stF = register 0 (κ 6) st₀

premF : regsSz? (iterSize 1 2 1) (EvalSt.registry stF) ≡ true
premF = refl

figuresF : List ℕ
figuresF =
    length (EvalSt.registry stF)
  ∷ length (EvalSt.registry (post 6 (inner 3 ∷ []) stF))
  ∷ regLens (EvalSt.registry (post 6 (inner 3 ∷ []) stF))

figuresF≡ : figuresF ≡ 1 ∷ 2 ∷ 6 ∷ 10 ∷ []
figuresF≡ = refl

rowF : regsSz? (iterSize 1 3 1) (EvalSt.registry (post 6 (inner 3 ∷ []) stF))
         ≡ true
rowF = refl

----------------------------------------------------------------------
-- ROW G — DEGENERATE, and recorded as such because it is what the
-- other rows are being contrasted against.  With no `mergeAll-st` at
-- the node, `thruConsume` forwards nothing and returns the state it
-- was handed, so the registry does not move and the conclusion is the
-- premise.  Its only content is that the load-bearing rows above are
-- NOT of this shape -- their registries grew.
----------------------------------------------------------------------
figuresG : List ℕ
figuresG = length (EvalSt.registry (post 6 (inner 3 ∷ []) (st-init e₀))) ∷ []

figuresG≡ : figuresG ≡ 0 ∷ []
figuresG≡ = refl

rowG : regsSz? (iterSize 1 3 1)
         (EvalSt.registry (post 6 (inner 3 ∷ []) (st-init e₀))) ≡ true
rowG = refl

----------------------------------------------------------------------
-- ROW H — DEGENERATE for the same reason and a different cause: the
-- node is present but holds a state of the wrong kind, so the `≟ᵗ`
-- the evaluator pays on every read of the cell sends this to the same
-- quiet arm.  Kept beside G because the two are the arms a green must
-- not be read off.
----------------------------------------------------------------------
stH : EvalSt e₀
stH = installNode 0 (scan-st {Γ = Γ₁} {t = natᵗ} 0) (st-init e₀)

figuresH : List ℕ
figuresH = length (EvalSt.registry (post 6 (inner 3 ∷ []) stH)) ∷ []

figuresH≡ : figuresH ≡ 0 ∷ []
figuresH≡ = refl

----------------------------------------------------------------------
-- AND THE TIE TO THE STATEMENT, at the two points that carry the
-- reading.  The rows above are the READING -- a Boolean recomputed
-- from the registry the step produced -- and nothing in them is held
-- to `stepFrame-regsSz` as it reads.  The two rows below are: Agda
-- generates each type from the statement itself, so the probe chooses
-- the point and a restatement of the target breaks here rather than
-- leaving a green reading about text that is gone.
--
-- WHY THESE TWO AND NOT ALL EIGHT.  Row A is the boundary row -- both
-- measured quantities at the ceiling their premises admit -- and row F
-- is the only one entering with a NON-EMPTY registry, which is the arm
-- where the conclusion must widen entries it did not create.  The
-- remaining load-bearing rows move the level, the count or the value
-- list, and each of those axes is already tied through one of these
-- two; the degenerate arms are tied by nothing deliberately, since a
-- row whose conclusion is its own premise buys the statement nothing.
----------------------------------------------------------------------
regsRowA : Confirms
  (stepFrame-regsSz {e = e₀} (gs (gs g0)) 0 0 (thru-outer mergeAllᵒ 0) (κ 6)
     (inner 3 ∷ []) false (sched-init e₀ sl₁) st₀ 1 2 premA₁ premA₂ premA₃)
regsRowA = refl

regsRowF : Confirms
  (stepFrame-regsSz {e = e₀} (gs (gs g0)) 0 0 (thru-outer mergeAllᵒ 0) (κ 6)
     (inner 3 ∷ []) false (sched-init e₀ sl₁) stF 1 2 premA₁ premA₂ premF)
regsRowF = refl
