-- ══════════════════════════════════════════════════════════════════
-- THE SHARE SINK DEEPENS THE STORE AND THE PATH MEASURE CHARGES IT
-- NOTHING, so no charge denominated in the walked path survives a
-- delivery that reaches one.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHAT THE STATEMENT SAID.  One chain's step leaves the nodes map no
-- deeper than it found it plus the arriving payload's nesting and the
-- wraps of the path it walks -- `nestDᵛ` plus `pathNestD`, premise-free.
--
-- WHY IT LOOKED RIGHT.  Every frame that STORES is a frame the path
-- measure charges, and a walk down a chain is exactly its frames.  The
-- reading holds on five program families, at the width that killed the
-- charge before it, and with the selection adversarially duplicated.
--
-- WHERE IT BREAKS.  `pathNestD` charges a `share-sink` zero, and a
-- chain ending at a share does not stop there: the sink fans the same
-- values into every registration on the share, each of which walks its
-- OWN path and stores at its own node.  Those paths live in the
-- registry, not in the one being charged, so the step spends wraps the
-- statement never counted.  Charging the whole STORE measure in place
-- of the nodes map does not repair it -- three against two on this
-- same witness -- because the registry arm the store measure carries
-- is what the fan-out already sits AT, not headroom above it.
--
-- WHY NO EARLIER ROW SAW IT, and it is a property of the VOCABULARY, not
-- of the sweep.  A shared slot's def may only reference inputs strictly
-- BELOW its own index, so a share installed at index zero -- which is
-- where every family in this development installs one -- has a def that
-- nothing can arrive into.  Its fan-out therefore happens once, during
-- the connect burst at subscribe time, and no DELIVERY ever reaches a
-- `share-sink` at all.  `insS` puts the share above the async slot
-- instead, which is the only arrangement in this context in which this
-- arm runs.
--
-- THE WITNESS is `progF 1 1` under `insS 2` -- one async slot beneath a
-- share whose def merges it -- read at the first arrival's own chain.
-- Three against one.
--
-- WHAT DIES AND WHAT DOES NOT.  The path-denominated form dies, for the
-- share arm alone; the frame arm it was proven from is untouched, and so
-- is the walk that telescopes them.  The repair the numbers point at is
-- a charge that carries the REGISTRY's own nesting, which is the thing
-- the fan-out reaches and the path measure cannot see.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Share-Sink-Nodes where

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; foldr)
open import Data.Nat using (ℕ; suc; _+_; _≤_; _⊔_)
open import Data.Nat.Properties using (≤⇒≤ᵇ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Closed; natᵗ; ofᵉ; mergeAllᵉ; strmᵗ; input; syncSizeᵉ)
open import Rx.Nest-Depth using (nestDᵛ)
open import Rx.Prim using (gasPad; g0; hot)
open import Rx.Evaluator
  using (Sched; EvalSt; subscribeE; sched-init; st-init; root; sched-next;
         cascadeLatch; chainsOf; chainStep; arrTy; arrVal; Arrival; Path; RegId)
open import Rx.Slots using (Slots; shared; scripted)
open import Verify-Budget-Sufficient.Nest-Store using (nodeNest; pathNestD)
open import Verify-Budget-Sufficient.Demand-Programs
  using (Γ₂; progF; asyncNats)
open import Rx.Hop-Depth using (hopDᵉ)
open import Rx.Slot-Hop using (slotHop)
open import Data.Maybe using (nothing)
open import Data.Unit using (tt)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)

-- THE SHARE-SINK VOCABULARY, and the arrangement is the content.  A
-- shared slot's def may only reference inputs BELOW its own index, so
-- the shared slot every other family here installs -- at index zero --
-- can reference nothing, and no arrival ever flows INTO it.  Its share
-- therefore fans out only during the connect burst, at subscribe time,
-- and a DELIVERY never reaches a `share-sink`.  Putting the shared slot
-- above the async one instead is what lets an arrival travel through
-- the def and fan out to every registration on the share, which is the
-- one arm of the walk no other vocabulary reaches.
shareDef : Closed Γ₂ natᵗ
shareDef = mergeAllᵉ nothing (ofᵉ (strmᵗ (input fzero) ∷ []))

insS : ℕ → Slots Γ₂
insS j fzero        = scripted (hot (asyncNats j))
insS j (fsuc fzero) = shared shareDef {ok = tt}

sucGS : ℕ → ℕ → ℕ → ℕ
sucGS j w k =
  suc (syncSizeᵉ (progF w k)
       + hopDᵉ 0 (slotHop 0 (insS j)) (progF w k))


prog : Closed Γ₂ natᵗ
prog = progF 1 1

slots : Slots Γ₂
slots = insS 2

ent : Sched Γ₂ × EvalSt prog
ent = let r = subscribeE (gasPad (sucGS 2 1 1) g0) prog root 0 0
                         (sched-init prog slots) (st-init prog)
      in proj₁ (proj₂ r) , proj₂ (proj₂ r)

nodesMax : ∀ {t} {e : Closed Γ₂ t} → EvalSt e → ℕ
nodesMax st = foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st)

stepOn : ∀ {t} {e : Closed Γ₂ t} (a : Arrival Γ₂)
       → List (RegId × Path Γ₂ (arrTy a) t) → Sched Γ₂ → EvalSt e → ℕ × ℕ
stepOn a []              sched st = 0 , 0
stepOn a ((rid , c) ∷ _) sched st =
  let r = chainStep 1 a c sched st
  in nodesMax (proj₂ (proj₂ r))
   , nodesMax st + (nestDᵛ (arrTy a) (arrVal a) + pathNestD c)

row : ℕ × ℕ
row with sched-next (proj₁ ent)
... | inj₁ _        = 0 , 0
... | inj₂ (a , sd) = let stL = cascadeLatch a (proj₂ ent)
                      in stepOn a (chainsOf a stL) sd stL

-- THE FIGURES, PINNED, so that a repair moving either side fails here
-- naming the number instead of turning the crossing into an equality
grown≡3 : proj₁ row ≡ 3
grown≡3 = refl

charge≡1 : proj₂ row ≡ 1
charge≡1 = refl

share-sink-nodes-absurd : proj₁ row ≤ proj₂ row → ⊥
-- `3 ≤ᵇ 1` reduces to `false`, so `T` of it IS the empty type
share-sink-nodes-absurd h = ≤⇒≤ᵇ h
