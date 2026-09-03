-- THE SEMANTIC BURST AGAINST THE SYNTACTIC PAYLOAD COUNT, which is the
-- one leaf left under the descent's ceiling and the first leaf on that
-- face either of whose sides could be instantiated at all.
--
-- WHAT THE ROWS COMPUTE IS THE STATEMENT'S OWN LEFT SIDE.  The leaf is
-- stated over the SPLIT of a real subscribe's emission stream rather
-- than over `burstW`, which is `abstract` and reduces at no point; the
-- assembly that gives the sealed name back is a body in `src`.  So
-- `lhs` here is the claim's left side and not a restatement of it.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.
-- TARGET: burst-out @08e9cd
module Probed.Burst-OutW where

open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ)
open import Data.Nat.Properties using (≤ᵇ⇒≤)
open import Data.Unit using (tt)
open import Data.Product using (proj₁)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gs)
open import Rx.Exp
  using (Closed; Val; Fn; natᵗ; _×ᵗ_; ofᵉ; emptyᵉ; takeᵉ; scanᵉ; mergeAllᵉ; switchAllᵉ; μᵉ; varᵉ;
  deferᵉ; input; nat̂; strmᵗ; primᵗ; pairᵗ; fstᵗ; sndᵗ; varᵗ; add)
open import Rx.Frame-Width using (outWⱽ)
open import Rx.Slots using (Slots)
open import Rx.Evaluator
  using (subscribeE; splitBurst; root; sched-init; st-init; Path; map-f; _↠_)
open import Verify-Budget-Sufficient.Desc-Ceil using (burst-out)
open import Probed.Apparatus using (Confirms)
open import Refuted.Demand-Programs using (Γ₂; insT)

slots : Slots Γ₂
slots = insT 1 1 2

gasBig : Gas
gasBig = gs (gs (gs (gs (gs (gs (gs (gs (gs (gs g0)))))))))

-- the two sides at the ROOT frame
lhs : ∀ {t} (e : Closed Γ₂ t) → ℕ
lhs {t} e =
  length (proj₁ (splitBurst {A = Val Γ₂ t}
    (proj₁ (subscribeE gasBig e root 0 0 (sched-init e slots) (st-init e)))))

rhs : ∀ {t} (e : Closed Γ₂ t) → ℕ
rhs e = outWⱽ 2 [] slots e

p-of : Closed Γ₂ natᵗ
p-of = ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ [])

p-empty : Closed Γ₂ natᵗ
p-empty = emptyᵉ

p-take0 : Closed Γ₂ natᵗ
p-take0 = takeᵉ (nat̂ 0) p-of

p-defer : Closed Γ₂ natᵗ
p-defer = deferᵉ p-of

p-script : Closed Γ₂ natᵗ
p-script = input (fsuc fzero)

p-share : Closed Γ₂ natᵗ
p-share = input fzero

p-merge : Closed Γ₂ natᵗ
p-merge = mergeAllᵉ nothing
            (ofᵉ (strmᵗ p-of ∷ strmᵗ p-of ∷ []))

-- THE μ HEAD, whose body reaches its own variable only from under a
-- defer -- the shape the ceiling's whole design turns on.  A frame at
-- a μ subscribes the UNFOLDING; the reading is of the body.
p-mu : Closed Γ₂ natᵗ
p-mu = μᵉ (mergeAllᵉ nothing
             (ofᵉ (strmᵗ (deferᵉ (varᵉ (here refl)))
                 ∷ strmᵗ (ofᵉ (nat̂ 0 ∷ nat̂ 0 ∷ [])) ∷ [])))

p-switch : Closed Γ₂ natᵗ
p-switch = switchAllᵉ (ofᵉ (strmᵗ p-of ∷ strmᵗ p-of ∷ []))

readout : List ℕ
readout = lhs p-of ∷ rhs p-of
        ∷ lhs p-empty ∷ rhs p-empty
        ∷ lhs p-take0 ∷ rhs p-take0
        ∷ lhs p-defer ∷ rhs p-defer
        ∷ lhs p-script ∷ rhs p-script
        ∷ lhs p-share ∷ rhs p-share
        ∷ lhs p-merge ∷ rhs p-merge
        ∷ lhs p-mu ∷ rhs p-mu
        ∷ lhs p-switch ∷ rhs p-switch
        ∷ []

-- THE ROWS, `lhs` then `rhs` at each program.  THREE ARE TIGHT and
-- those are the load-bearing ones: `ofᵉ` at 3, `mergeAllᵉ` at 6 and
-- `switchAllᵉ` at 6 are equalities, so any payload the frame emits
-- beyond the reading would refute the claim outright -- and the two
-- `*All` heads are where the reading is a PRODUCT, which is the only
-- place it could be under-counted.  The `takeᵉ 0`, scripted and shared
-- rows carry slack and are DEGENERATE on the failure axis: nothing
-- they could report would fail.  The defer row is neither -- it reads
-- 0 against 0, and it is the row the whole ceiling rests on, since a
-- single payload delivered under a defer would refute both this and
-- the ceiling's right to stop there.
readout≡ : readout ≡ 3 ∷ 3 ∷ 0 ∷ 0 ∷ 0 ∷ 3 ∷ 0 ∷ 0 ∷ 0 ∷ 1
                   ∷ 1 ∷ 2 ∷ 6 ∷ 6 ∷ 2 ∷ 4 ∷ 6 ∷ 6 ∷ []
readout≡ = refl

-- THE TIE, at the three rows above that are EQUALITIES and so are the
-- ones a row here can be load-bearing on: the source at three and the
-- two `*All` heads at six.  `≤ᵇ⇒≤` takes the goal's own terms, so what
-- is compared is the statement as it reads and not a copy of it.
tieOf : Confirms
  (burst-out gasBig slots p-of root 0 0 (sched-init p-of slots) (st-init p-of) refl)
tieOf = ≤ᵇ⇒≤ _ _ tt

tieMerge : Confirms
  (burst-out gasBig slots p-merge root 0 0
     (sched-init p-merge slots) (st-init p-merge) refl)
tieMerge = ≤ᵇ⇒≤ _ _ tt

tieSwitch : Confirms
  (burst-out gasBig slots p-switch root 0 0
     (sched-init p-switch slots) (st-init p-switch) refl)
tieSwitch = ≤ᵇ⇒≤ _ _ tt

----------------------------------------------------------------------
-- THE TWO REGIONS THE ROWS ABOVE NAMED AS UNCOVERED.
----------------------------------------------------------------------

-- THE SCAN HEAD, and it is where the reading is TIGHTEST rather than
-- widest: `outWⱽ` walks straight through a `scanᵉ` and hands back the
-- source's count, while the frame emits one value per arriving one.
-- So the row is an EQUALITY and load-bearing on the failure axis --
-- a scan emitting so much as one extra payload at its subscribe, a
-- seed among them, would put the left side over.  The exponent this
-- family is known for lives on the INNER reading and reaches the outer
-- one only through a flatten, which is why a bare scan is tight and
-- the refold below is not.
stepFn : Fn Γ₂ [] [] [] (natᵗ ×ᵗ natᵗ) natᵗ
stepFn = primᵗ add (pairᵗ (fstᵗ (varᵗ (here refl))) (sndᵗ (varᵗ (here refl))))

p-scan : Closed Γ₂ natᵗ
p-scan = scanᵉ stepFn (nat̂ 0) p-of

-- THE REFOLD, which is the same scan under the flatten that turns its
-- accumulator into emissions -- the one family whose syntactic reading
-- towers in the layer count.  Read here for the CEILING's sake rather
-- than the family's: it says what the slack looks like where the
-- reading is a power, and so which region of this leaf cannot refute.
p-refold : Closed Γ₂ natᵗ
p-refold = mergeAllᵉ nothing
             (scanᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ []))) (strmᵗ p-of) p-of)

-- THE FRAME BELOW THE ROOT.  A non-root continuation cannot graft
-- anything into the stream this leaf measures -- `subscribeE` returns
-- the TERM's own burst and the caller applies its frame -- so what a
-- deeper `κ` can move is the STATE the frame steps against, and only a
-- term whose subscribe recurses passes `κ` down at all.  These rows
-- are therefore read at the recursing heads and not at `ofᵉ`, where
-- the clause ignores `κ` outright and the row could not have failed.
κ₁ : Path Γ₂ natᵗ natᵗ
κ₁ = map-f (varᵗ (here refl)) ↠ root

lhsκ : (e : Closed Γ₂ natᵗ) → ℕ
lhsκ e =
  length (proj₁ (splitBurst {Γ = Γ₂} {u = natᵗ} {A = Val Γ₂ natᵗ}
    (proj₁ (subscribeE {e = e} gasBig e κ₁ 0 0 (sched-init e slots) (st-init e)))))

deeper : List ℕ
deeper = lhs p-scan ∷ rhs p-scan
       ∷ lhs p-refold ∷ rhs p-refold
       ∷ lhsκ p-scan ∷ lhsκ p-merge ∷ lhsκ p-switch
       ∷ []

-- THE ROWS.  The scan head is an EQUALITY at three and LOAD-BEARING:
-- one extra payload out of the fold's subscribe, its seed among them,
-- puts the left side over a reading that walks straight through the
-- `scanᵉ`.  The refold reads six against EIGHTEEN, and the slack is
-- the finding rather than the fit -- the flatten multiplies the two
-- readings, so this whole region is DEGENERATE on the failure axis and
-- probing the ceiling at a refold buys nothing.  The three deeper-`κ`
-- rows repeat the tight heads one frame below the root and are
-- UNMOVED, which is what says a continuation does not reach this
-- count.
deeper≡ : deeper ≡ 3 ∷ 3 ∷ 6 ∷ 18 ∷ 3 ∷ 6 ∷ 6 ∷ []
deeper≡ = refl

-- THE TIE AT THE SCAN HEAD, at the root and again one frame below it.
tieScan : Confirms
  (burst-out gasBig slots p-scan root 0 0
     (sched-init p-scan slots) (st-init p-scan) refl)
tieScan = ≤ᵇ⇒≤ _ _ tt

tieScanκ : Confirms
  (burst-out gasBig slots p-scan κ₁ 0 0
     (sched-init p-scan slots) (st-init p-scan) refl)
tieScanκ = ≤ᵇ⇒≤ _ _ tt
