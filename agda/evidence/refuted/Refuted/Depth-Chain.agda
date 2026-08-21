-- A SLOT CHAIN OUTRUNS ANY MAX OVER THE SLOTS — so neither
-- `depth-conn-input` nor `depth-compositional` itself is true as
-- stated.
--
-- THE MECHANISM, and it is the finding rather than either witness.
-- Slots are STRATIFIED: slot k's def may reference inputs strictly
-- below k, so a def can connect to another def, and the connects
-- CHAIN.  Each link is traversed by one `thru-outer` frame, and the
-- arcs ADD.  The slot half of `storeNestMax` WAS a `foldr _⊔_ 0` — a
-- MAX over the slots, which for a chain of identical links does not
-- grow with the chain at all.
--
-- So the two sides grew in DIFFERENT VARIABLES: the left in the chain
-- LENGTH, the right in one def's SIZE.  Both slopes were measured
-- before they were crossed, which is why this is a mechanism finding
-- and not a lucky counterexample:
--
--   § A  one slot, k nested merge layers in its def
--          def size 7  → depth 1        def size 15 → depth 3
--        depth tracks the def's own NESTING; the store tracks its SIZE,
--        and nesting is the cheaper of the two.  Comfortably true here,
--        which is why the bound survived every earlier row.
--   § B  a 5-link chain of size-5 links over a size-7 base
--          store 7  →  depth 5
--        depth is now exactly the LINK COUNT.  Still true — barely.
--   § C  the same chain at 9 links
--          store 7  →  depth 9        RHS of the parent = 1 + 0 + 7 = 8
--
-- § C needs no bigger def, only more slots, and the chain length is
-- bounded by `n` — which appears nowhere in either right-hand side.
--
-- WHAT THIS SAYS ABOUT THE REPAIR.  A `⊔` is worse, not better: the
-- shape floated in `depth-conn-input`'s header,
-- `(sizeᵉ b + pathLen κ) ⊔ storeNestMax`, gives `1 ⊔ 7 = 7` at § C and
-- is refuted a fortiori by the same witness.  The currency the chain
-- actually spends is a SUM over the slots (here 7 + 8×5 = 47), which
-- is the shape `slotsSize` already has and which `storeNest-capped`
-- already knows how to cap.  That is a measurement, not a route.
--
-- THE MAX IS STATED LOCALLY, BECAUSE `src` NO LONGER HAS ONE.  The
-- repair this refutation forced replaced `slotsNestMax`'s
-- `foldr _⊔_ 0` with a sum, so `storeNestMax`'s definition moved while
-- every statement written over it kept its text.  Re-deriving the max
-- HERE is not resurrecting vocabulary in `src` — it is the only way to
-- keep the finding state-able, and the finding is about the currency,
-- which is precisely what left `src`.  `slotNest` and `slotsSize` are
-- still the real ones.
--
-- WHEN THE WITNESSES WERE WRITTEN both were INHABITED: the sum landed
-- in the same commit, and before it `depth-compositional` was a live
-- definition resting on `depth-conn-input`, so the postulate set was
-- inconsistent.  They are stated as hypotheses so the refutation
-- survives that repair and any later one.
--
-- ONLY THE CROSSING IS IN CODE.  The § A and § B slopes above are
-- measurements, and a `refl` row no witness consumes has no route home
-- from `Refuted.Main` — so they are recorded as numbers here and the
-- file keeps the rows the two witnesses actually spend.
--
-- SUPERSEDES nothing: `Refuted.Depth-Conn` kills the free-def
-- QUANTIFICATION and is a different defect, repairable inside the
-- max currency.  This one is about the currency.
module Refuted.Depth-Chain where

open import Data.Empty using (⊥)
open import Data.Fin   using (Fin) renaming (zero to fz; suc to fs)
open import Data.List  using ([]; _∷_; foldr; tabulate)
open import Data.Nat   using (ℕ; _≤_; s≤s; _+_; _⊔_)
open import Data.Unit  using (tt)
open import Data.Vec   using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst₂)

open import Rx.Prim using (Gas; g0; gs; Id; Tick)
open import Rx.Exp  using (Ctx; Closed; natᵗ; nat̂; strmᵗ; input; ofᵉ;
  mergeAllᵉ; sizeᵉ)
open import Rx.Slots using (Slots; shared)
open import Rx.Evaluator using (EvalSt; Sched; Path; root; sched-init; st-init)
open import Verify-Budget-Sufficient.Caps-Depth using (depthE)
open import Verify-Budget-Sufficient.Measures using (pathLen)
open import Verify-Budget-Sufficient.Depth-Compositional using (slotNest;
  nodesNestMax)

-- gas enough to walk the longest chain here twice over: each link
-- peels one at the connect and one at the payload entry
g30 : Gas
g30 = gs (gs (gs (gs (gs (gs (gs (gs (gs (gs
      (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs
      (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs g0)))))))))))))))))))))))))))))

----------------------------------------------------------------------
-- THE CROSSING — a 9-link chain of size-5 links over a size-7 base.
-- The left side has outrun a right side that never moved.
----------------------------------------------------------------------

-- the measure as it stood: a MAX over the slots
slotsNestMaxOld : ∀ {n} {Γ : Ctx n} → Slots Γ → ℕ
slotsNestMaxOld {n} sl = foldr _⊔_ 0 (tabulate {n = n} (λ i → slotNest (sl i)))

storeNestMaxOld : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} →
  Sched Γ → EvalSt e → ℕ
storeNestMaxOld sched st =
  slotsNestMaxOld (Sched.slots sched) ⊔ nodesNestMax (EvalSt.nodes st)

Γ₉ : Ctx 9
Γ₉ = natᵗ ∷ⱽ natᵗ ∷ⱽ natᵗ ∷ⱽ natᵗ ∷ⱽ natᵗ ∷ⱽ natᵗ ∷ⱽ natᵗ ∷ⱽ natᵗ ∷ⱽ
     natᵗ ∷ⱽ []ⱽ

base₉ : Closed Γ₉ natᵗ
base₉ = mergeAllᵉ (ofᵉ (strmᵗ (ofᵉ (nat̂ 7 ∷ [])) ∷ []))

lk0 : Closed Γ₉ natᵗ
lk0 = mergeAllᵉ (ofᵉ (strmᵗ (input fz) ∷ []))

lk1 : Closed Γ₉ natᵗ
lk1 = mergeAllᵉ (ofᵉ (strmᵗ (input (fs fz)) ∷ []))

lk2 : Closed Γ₉ natᵗ
lk2 = mergeAllᵉ (ofᵉ (strmᵗ (input (fs (fs fz))) ∷ []))

lk3 : Closed Γ₉ natᵗ
lk3 = mergeAllᵉ (ofᵉ (strmᵗ (input (fs (fs (fs fz)))) ∷ []))

lk4 : Closed Γ₉ natᵗ
lk4 = mergeAllᵉ (ofᵉ (strmᵗ (input (fs (fs (fs (fs fz))))) ∷ []))

lk5 : Closed Γ₉ natᵗ
lk5 = mergeAllᵉ (ofᵉ (strmᵗ (input (fs (fs (fs (fs (fs fz)))))) ∷ []))

lk6 : Closed Γ₉ natᵗ
lk6 = mergeAllᵉ (ofᵉ (strmᵗ (input (fs (fs (fs (fs (fs (fs fz))))))) ∷ []))

lk7 : Closed Γ₉ natᵗ
lk7 = mergeAllᵉ (ofᵉ (strmᵗ (input (fs (fs (fs (fs (fs (fs (fs fz)))))))) ∷ []))

slots₉ : Slots Γ₉
slots₉ fz                                         = shared base₉ {ok = tt}
slots₉ (fs fz)                                    = shared lk0 {ok = tt}
slots₉ (fs (fs fz))                               = shared lk1 {ok = tt}
slots₉ (fs (fs (fs fz)))                          = shared lk2 {ok = tt}
slots₉ (fs (fs (fs (fs fz))))                     = shared lk3 {ok = tt}
slots₉ (fs (fs (fs (fs (fs fz)))))                = shared lk4 {ok = tt}
slots₉ (fs (fs (fs (fs (fs (fs fz))))))           = shared lk5 {ok = tt}
slots₉ (fs (fs (fs (fs (fs (fs (fs fz)))))))      = shared lk6 {ok = tt}
slots₉ (fs (fs (fs (fs (fs (fs (fs (fs fz)))))))) = shared lk7 {ok = tt}

topᶠ : Fin 9
topᶠ = fs (fs (fs (fs (fs (fs (fs (fs fz)))))))

progC : Closed Γ₉ natᵗ
progC = input topᶠ

schedC : Sched Γ₉
schedC = sched-init progC slots₉

stC : EvalSt progC
stC = st-init progC

depthC : depthE g30 progC root 0 0 schedC stC ≡ 9
depthC = refl

storeC : storeNestMaxOld schedC stC ≡ 7
storeC = refl

-- the PARENT's right-hand side at the same program: 1 + 0 + 7
parentC : sizeᵉ progC + pathLen (root {Γ = Γ₉} {t = natᵗ})
            + storeNestMaxOld schedC stC ≡ 8
parentC = refl

----------------------------------------------------------------------
-- THE WITNESSES
----------------------------------------------------------------------

depth-conn-input-absurd :
  (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
     (g : Gas) (i : Fin n)
     (κ : Path Γ (Data.Vec.lookup Γ i) t) (bid : Id) (now : Tick)
     (sched : Sched Γ) (st : EvalSt e) →
     depthE g (input i) κ bid now sched st ≤ storeNestMaxOld sched st) → ⊥
depth-conn-input-absurd h
  with subst₂ _≤_ depthC storeC (h g30 topᶠ root 0 0 schedC stC)
... | s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ()))))))

depth-compositional-absurd :
  (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
     (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (bid : Id) (now : Tick)
     (sched : Sched Γ) (st : EvalSt e) →
     depthE g b κ bid now sched st
       ≤ sizeᵉ b + pathLen κ + storeNestMaxOld sched st) → ⊥
depth-compositional-absurd h
  with subst₂ _≤_ depthC parentC (h g30 progC root 0 0 schedC stC)
... | s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ())))))))
