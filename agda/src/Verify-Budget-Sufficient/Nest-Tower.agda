------------------------------------------------------------------
-- THE DEPTH FACE'S TOWER, and the height it is stated at.
--
-- `nest-store≤capsH` (.Caps-Bridge) needs the depth measure under
-- `capsH e ins 0`, and the caps side of that is fully proven:
-- `tower-le-blowH k m` delivers `towerℕ k ≤ blowH m` for ANY k with
-- `suc k ≤ towerℕ m`, so the height is free and the depth side may
-- spend a FACTOR rather than a constant.  This module spends it at
-- `k = 3 * capsBase e ins`.
--
-- WHY A FACTOR AND NOT A CONSTANT, since a constant is what the first
-- statement asked for.  `nestDᵉ` multiplies by `outWᵉ` at every
-- `scanᵉ`; `wid-iterFold` bounds `outWᵉ` by `iterFold 2 (sizeᵉ e) M`
-- and `iterFold-tower` puts that at height `k + 2 * sizeᵉ e`; one more
-- tower level per product on top lands the induction near
-- `k + 3 * sizeᵉ e`.  `capsBase` carries `sizeᵉ e` ONCE, and nothing
-- relates its `entryCeil` term back to `sizeᵉ e` — its only two facts
-- bound SLOT widths by it.  Three times `capsBase` is what covers it.
--
-- WHAT MAKES THE WIDTH MACHINERY REACHABLE FROM HERE.  `wid-iterFold`
-- wants `SlotWid sl M`, and its only proven producer
-- (`slotsCaps?-slotWid`) is conditioned on `slotsCaps? B W sl ≡ true`
-- — a hypothesis this face does not have and must not acquire, since
-- adding one is a restatement and the unconditional form is not
-- refuted.  `entryCeil-slotWid` below is the unconditional producer:
-- the entry ceiling already dominates `slotsPW` and `slotsIW` for
-- every `e`, and those are the maxima a slot's own pW and innW sit
-- under.  It is the conditioned lemma's body with the side condition's
-- two bounds replaced by that pair of facts.
------------------------------------------------------------------
module Verify-Budget-Sufficient.Nest-Tower where

open import Data.Nat using (ℕ; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; ≤-refl; ≤-reflexive; +-mono-≤;
  +-monoˡ-≤; m≤m+n; m≤n+m; m≤m⊔n; m≤n⊔m; n≤1+n; ⊔-identityʳ)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (towerℕ)
open import Rx.Exp using (Ctx; Closed; Exp; sizeᵉ)
open import Rx.Slots using (Slots; slotsSize; shared; scripted)
open import Rx.Nest-Depth using (nestDᵉ)
open import Rx.Frame-Width using (entryCeil; pWᵉ; innWᵉ; outWᵉ; dWᵉ;
  slotsPW≤entryCeil; slotsIW≤entryCeil)
open import Rx.Evaluator using (capsBase; sched-init; st-init)

open import Verify-Budget-Sufficient.Measures using (k≤towerℕ; towerℕ-mono)
open import Verify-Budget-Sufficient.Caps using (3T≤)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (SlotWid; Sub-[];
  slotsPW-lb; slotsIW-lb)
open import Verify-Budget-Sufficient.Caps-Face.Part2 using (monoᵉ; monoᴰᵉ)
open import Verify-Budget-Sufficient.Depth-Compositional using
  (storeNestMax; slotsNestSum)

------------------------------------------------------------------
-- THE UNCONDITIONAL LEAF BOUND.
------------------------------------------------------------------

-- A slot's own parked and inner widths sit under the entry ceiling by
-- construction, so the leaf bound needs no side condition.  Same body
-- as `slotsCaps?-slotWid`: the fuel/visited descent (`monoᵉ`, `monoᴰᵉ`)
-- lifts what the `input` clause reads off the def up to the def's own
-- `pWᵉ`/`innWᵉ`, and the max-over-slots lemmas take it from there.  A
-- scripted slot presents 1, 1 and 0, which is what the `suc` is for.
--
-- THE TWO LOOKUPS RIDE THE `with`, not the branch, because
-- `with sl i` rewrites the GOAL and not the types of terms written
-- inside the branch — the same reason the conditioned twin carries its
-- side-condition lookup there.
entryCeil-slotWid : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (sl : Slots Γ)
  (e : Exp Γ Δᵍ Δ Θ t) → SlotWid sl (suc (entryCeil n sl e))
entryCeil-slotWid {n = suc m} sl e i
  with sl i | slotsPW-lb (suc m) sl i | slotsIW-lb (suc m) sl i
... | scripted _ | _  | _  = s≤s z≤n , s≤s z≤n , z≤n
... | shared d   | hp | hi =
    ≤-trans (proj₁ (mono d))
            (≤-trans (m≤m⊔n (outWᵉ (suc m) sl d) (dWᵉ (suc m) sl d)) pw′)
  , ≤-trans (proj₁ (proj₂ (mono d))) iw′
  , ≤-trans (monoᴰᵉ sl m (n≤1+n m) {i ∷ []} {[]} (Sub-[] {vs = i ∷ []}) d)
            (≤-trans (m≤n⊔m (outWᵉ (suc m) sl d) (dWᵉ (suc m) sl d)) pw′)
  where
  mono = λ dd → monoᵉ sl m (n≤1+n m) {i ∷ []} {[]} (Sub-[] {vs = i ∷ []}) dd
  pw : pWᵉ (suc m) sl d ≤ entryCeil (suc m) sl e
  pw = ≤-trans hp (slotsPW≤entryCeil (suc m) sl e)
  iw : innWᵉ (suc m) sl d ≤ entryCeil (suc m) sl e
  iw = ≤-trans hi (slotsIW≤entryCeil (suc m) sl e)
  pw′ : pWᵉ (suc m) sl d ≤ suc (entryCeil (suc m) sl e)
  pw′ = ≤-trans pw (n≤1+n (entryCeil (suc m) sl e))
  iw′ : innWᵉ (suc m) sl d ≤ suc (entryCeil (suc m) sl e)
  iw′ = ≤-trans iw (n≤1+n (entryCeil (suc m) sl e))

------------------------------------------------------------------
-- THE TWO HALVES OF THE MEASURE, each at the height the width
-- machinery forces.  `S` is fixed at 2 inside — it is the base
-- `wid-iterFold` asks for and it never reaches the conclusion, so
-- carrying it as a parameter would say nothing.
------------------------------------------------------------------

postulate
  -- THE TERM HALF.  Induction on `e`, and the height was chosen so that
  -- EVERY CLAUSE HAS A LEVEL LEFT OVER: `3 * suc x` is `3 + 3 * x`, so
  -- each syntax node grants three levels and no clause needs more than
  -- two.  The budget, clause by clause:
  --
  --   input i          0, nothing to pay
  --   mergeAllᵉ &c.    suc of the child — one level, via `3T≤`
  --   mapᵉ / takeᵉ     a sum of two children — one level
  --   ofᵉ ts           a sum over the list; the LENGTH is under `sizeᵉ`,
  --                    so `tower-mul` turns it into one level
  --   scanᵉ f z e      TWO: `outWᵉ n sl e * nestDᵗ f` is a `tower-mul`
  --                    over `wid-iterFold` (at base 2) composed with
  --                    `iterFold-tower`, which lands `outWᵉ` at height
  --                    `k + 2 * sizeᵉ e` — inside the `3 * sizeᵉ e` this
  --                    is stated at — and then the three-way sum costs
  --                    the second
  --
  -- The two precedents are for the two HALVES and not for the pair, so
  -- this is not a mechanical transcription of either: `wid-iterFold` is
  -- the same Exp/Tm induction with the same slot leaf and is where the
  -- `outWᵉ` bound comes from, and `iterFold-tower` is the worked
  -- instance of the tower arithmetic.
  nestD-tower : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (k M : ℕ) → 3 ≤ k → 1 ≤ M →
    M ≤ towerℕ k → (sl : Slots Γ) → SlotWid sl M → (e : Exp Γ Δᵍ Δ Θ t) →
    nestDᵉ sl e ≤ towerℕ (k + 3 * sizeᵉ e)

  -- THE STORE HALF, at the entry state, where the node table is empty
  -- and the whole store is the slot telescope.  A scripted slot pays
  -- nothing and a shared slot's summand is its def's size plus the term
  -- half at that def, so the count of nonzero summands is under
  -- `slotsSize sl` — which is the height this is stated at.
  storeNest-tower : ∀ {n} {Γ : Ctx n} (k M : ℕ) → 3 ≤ k → 1 ≤ M →
    M ≤ towerℕ k → (sl : Slots Γ) → SlotWid sl M →
    slotsNestSum sl ≤ towerℕ (k + 3 * slotsSize sl)

------------------------------------------------------------------
-- THE ASSEMBLY.  Three bounds at one height, `3T≤` to add them, and
-- `towerℕ-mono` to land on `3 * capsBase`.  The height is
-- `(4 + E) + 3 * S + 3 * L`, so each half's own height is a PREFIX of
-- it and no reassociation is needed to spend either.
------------------------------------------------------------------

nestD-le-tower : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  sizeᵉ e + nestDᵉ ins e + 0
    + storeNestMax (sched-init e ins) (st-init e)
    ≤ towerℕ (3 * capsBase e ins)
nestD-le-tower {n = n} e ins =
  ≤-trans (+-mono-≤ (+-mono-≤ (+-mono-≤ sizeLe nestLe) ≤-refl) storeLe)
  (≤-trans (≤-reflexive (solve 1 (λ x → ((x :+ x) :+ con 0) :+ x := con 3 :* x)
                               refl T))
  (≤-trans (3T≤ H 3≤H) (towerℕ-mono {suc H} {3 * capsBase e ins} fits)))
  where
  S = sizeᵉ e
  L = slotsSize ins
  E = entryCeil n ins e
  M = suc E
  K = 4 + E
  H = K + 3 * S + 3 * L
  T = towerℕ H

  3≤K : 3 ≤ K
  3≤K = s≤s (s≤s (s≤s z≤n))

  M≤TK : M ≤ towerℕ K
  M≤TK = ≤-trans (k≤towerℕ M) (towerℕ-mono {M} {K} (s≤s (m≤n+m E 3)))

  3≤H : 3 ≤ H
  3≤H = ≤-trans 3≤K (≤-trans (m≤m+n K (3 * S)) (m≤m+n (K + 3 * S) (3 * L)))

  nestLe : nestDᵉ ins e ≤ T
  nestLe = ≤-trans (nestD-tower K M 3≤K (s≤s z≤n) M≤TK ins wid e)
                   (towerℕ-mono {K + 3 * S} {H} (m≤m+n (K + 3 * S) (3 * L)))
    where wid = entryCeil-slotWid ins e

  storeLe : storeNestMax (sched-init e ins) (st-init e) ≤ T
  storeLe = ≤-trans (≤-reflexive (⊔-identityʳ (slotsNestSum ins)))
            (≤-trans (storeNest-tower K M 3≤K (s≤s z≤n) M≤TK ins wid)
                     (towerℕ-mono {K + 3 * L} {H}
                        (+-monoˡ-≤ (3 * L) (m≤m+n K (3 * S)))))
    where wid = entryCeil-slotWid ins e

  sizeLe : S ≤ T
  sizeLe = ≤-trans (k≤towerℕ S) (towerℕ-mono {S} {H} S≤H)
    where
    S≤H : S ≤ H
    S≤H = ≤-trans (m≤m+n S (S + (S + 0)))
          (≤-trans (m≤n+m (3 * S) K) (m≤m+n (K + 3 * S) (3 * L)))

  -- suc H plus its own slack IS 3 * capsBase, which is the one place
  -- the two shapes have to be reconciled
  fits : suc H ≤ 3 * capsBase e ins
  fits = ≤-trans (m≤m+n (suc H) (7 + 2 * E)) (≤-reflexive eq)
    where
    eq : suc H + (7 + 2 * E) ≡ 3 * capsBase e ins
    eq = solve 3 (λ s l x →
           (con 1 :+ (((con 4 :+ x) :+ con 3 :* s) :+ con 3 :* l))
             :+ (con 7 :+ con 2 :* x)
           := con 3 :* ((con 3 :+ (s :+ l)) :+ (con 1 :+ x)))
         refl S L E
