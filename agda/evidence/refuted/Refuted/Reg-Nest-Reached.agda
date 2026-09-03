-- ══════════════════════════════════════════════════════════════════
-- THE REGISTRY'S DEPTH IS NOT UNDER THE PROGRAM'S SYNTACTIC UNIT AT
-- THE STATES A RUN REACHES, which is the reading the conjunct was
-- left standing on.  Its own header concedes the arbitrary state and
-- answers that a registered chain's frames are the program's own; the
-- witness here runs `subscribeE` from `st-init` and mints a chain
-- deeper than the unit anyway, so the concession does not save it.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE`
-- notes.
-- ══════════════════════════════════════════════════════════════════

-- WHERE THE TWO MEASURES COME APART, and it is a `map-f` frame.  The
-- path measure charges a map its FUNCTION's nesting, and the unit is
-- read off the program's syntax once.  A scan whose accumulator is
-- observable-typed carries syntax as a VALUE, and its fold may fold
-- the previous accumulator back into the next one's map function --
-- so the function grows one layer per delivery while the unit does
-- not move.  A `natᵗ`-typed function cannot BE the accumulator, but
-- `sndᵗ (pairᵗ _ _)` lets it CARRY it, and the measure charges the ⊔
-- of a pair's sides, so carrying is enough.

-- AND THE CLIMB IS EXACTLY ONE PER FOLD, which is what makes this a
-- refutation of the shape rather than a margin that happens to be
-- tight: `k` synchronous deliveries put a registered chain at depth
-- `k` against a unit of four, so every `k > 4` refutes and the gap
-- diverges.  No cap could be chosen large enough -- the unit is not a
-- cap, and there is no number of the program's that the run's depth
-- is under.

-- THE STATE IS REACHED, NOT BUILT.  `run` is `subscribeE` applied to
-- `st-init` and `sched-init` at the program's own gas, which is the
-- only way into the registry a run has; nothing here is a hand-built
-- record, and no `register` is called by this module at all.
module Refuted.Reg-Nest-Reached where

open import Data.Bool using (true)
open import Data.Empty using (⊥)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; map; foldr; length)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _⊔_; _≤ᵇ_)
open import Data.Product using (_,_; proj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gasPad; Id; Tick; cold; after_,_)
open import Rx.Exp using (Ctx; Closed; Exp; Fn; natᵗ; obs; _×ᵗ_;
  scanᵉ; mergeAllᵉ; mapᵉ; ofᵉ; input; varᵗ; fstᵗ; sndᵗ; pairᵗ; nat̂; strmᵗ)
open import Rx.Slots using (Slots; scripted)
open import Rx.Evaluator using (Path; subscribeE; root; sched-init; st-init;
  EvalSt)
open import Verify-Budget-Sufficient.Delivery-Walk using (regP?)
open import Verify-Budget-Sufficient.Nest-Store using (pathNestD; nestUnit)

------------------------------------------------------------------
-- THE STATEMENT, restricted to the states a run reaches -- the
-- reading the conjunct's own header offers in its defence.
------------------------------------------------------------------

RegsNestReached : Set
RegsNestReached = ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t)
  (sl : Slots Γ) (fuel : Gas) (id : Id) (now : Tick) →
  regP? (λ {u} (p : Path Γ u t) → pathNestD p ≤ᵇ nestUnit e sl)
        (EvalSt.registry
           (proj₂ (proj₂ (subscribeE fuel e root id now
                            (sched-init e sl) (st-init e)))))
    ≡ true

------------------------------------------------------------------
-- THE WITNESS
------------------------------------------------------------------

Γ₂ : Ctx 2
Γ₂ = natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

-- slot 0 is an async cold: it mints a source and REGISTERS on every
-- subscribe.  slot 1 is a synchronous cold script of length k: it
-- drives the fold k times and registers nothing.
countdown : ℕ → List ℕ
countdown zero    = []
countdown (suc k) = k ∷ countdown k

slots : ℕ → Slots Γ₂
slots k fzero        = scripted (cold [] ((after 0 , 7) ∷ []))
slots k (fsuc fzero) = scripted (cold (countdown k) [])

-- a registering source of nesting one: the `ofᵉ` emits an inner that
-- bottoms out at the async slot, which is what mints the chain
base : ∀ {Θ} → Exp Γ₂ [] [] Θ natᵗ
base = mergeAllᵉ nothing (ofᵉ (strmᵗ (input fzero) ∷ []))

-- the map function is `natᵗ`-typed and so cannot BE the accumulator;
-- the pair lets it CARRY it, and `nestDᵗ` charges the ⊔ of the sides
carry : Fn Γ₂ [] [] ((obs natᵗ ×ᵗ natᵗ) ∷ []) natᵗ natᵗ
carry = sndᵗ (pairᵗ (fstᵗ (varᵗ (there (here refl)))) (nat̂ 0))

-- one fold: the next accumulator is a map whose function holds the
-- previous one, so the syntax the accumulator carries grows by one
-- layer per delivery
deepen : Fn Γ₂ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
deepen = strmᵗ (mapᵉ carry base)

prog : Closed Γ₂ natᵗ
prog = mergeAllᵉ nothing (scanᵉ deepen (strmᵗ base) (input (fsuc fzero)))

fuel : Gas
fuel = gasPad 400 g0

run : ℕ → EvalSt prog
run k = proj₂ (proj₂ (subscribeE fuel prog root 0 0
                        (sched-init prog (slots k)) (st-init prog)))

deepest : ℕ → ℕ
deepest k = foldr _⊔_ 0
  (map (λ en → pathNestD (proj₂ (proj₂ (proj₂ en)))) (EvalSt.registry (run k)))

------------------------------------------------------------------
-- THE READINGS.  The unit is fixed at four; the deepest reachable
-- chain climbs one per fold and passes it.
------------------------------------------------------------------

unit≡4 : nestUnit prog (slots 5) ≡ 4
unit≡4 = refl

deepest₁≡1 : deepest 1 ≡ 1
deepest₁≡1 = refl

deepest₃≡3 : deepest 3 ≡ 3
deepest₃≡3 = refl

deepest₅≡5 : deepest 5 ≡ 5
deepest₅≡5 = refl

regsLen₅≡5 : length (EvalSt.registry (run 5)) ≡ 5
regsLen₅≡5 = refl

regs-nest-reached-absurd : RegsNestReached → ⊥
regs-nest-reached-absurd pr with pr prog (slots 5) fuel 0 0
... | ()
