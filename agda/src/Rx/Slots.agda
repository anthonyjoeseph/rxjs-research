-- THE SLOT TELESCOPE, on its own so that BOTH the width measures and
-- the evaluator can read it.
--
-- WHY IT IS NOT IN Rx.Evaluator.  A width measure has to walk a shared
-- def, so it needs `Slot` / `Slots`; the evaluator needs the same
-- telescope to seed its descent.  With the telescope inside the
-- evaluator that is a cycle; here it is a shared prerequisite, and
-- Rx.Evaluator re-exports the whole module so the ~1400 sites that read
-- `Slots` off the evaluator are untouched.
module Rx.Slots where

open import Data.Bool    using (T)
open import Data.Nat     using (ℕ)
open import Data.Vec     using (lookup)
open import Data.Fin     using (toℕ)

open import Rx.Prim using (ObservableInput)
open import Rx.Exp  using (Ty; Ctx; Val; Closed; isData; inputsBelowᵉ)

-- slot i of Γ is either an external SCRIPTED input (hot/cold) or a
-- SHARED observable: a plain tree with an implicit all-resets-false
-- share() at its root.  Share identity is the de Bruijn index -- the
-- binding, not the expression, exactly as a JS `const`.
--
-- EVERY SLOT CARRIES DATA ONLY (`T (isData t)`, discharged by
-- unification at every data type, so ordinary tables are written
-- unchanged).  THE CONDITION IS ON THE TYPE AND SO IS THE HOLE, which
-- is why it reads the same on both arms rather than being two
-- conditions that happen to coincide.
--
-- WHAT THE HOLE IS.  An elaborated slot stands at `plainᵗ`, and
-- `plainᵗ (obs u) = obs (emitᵗ u)` -- so at an observable type the
-- slot's VALUES are themselves observables OF ENVELOPES, and a
-- `mergeAllˢ` on the reference flattens them via `laneᵛ`, subscribing
-- them DIRECTLY.  Whatever they emit reaches the wire having never
-- passed `stamp`.  In the surface language that is
--
--   forgedInner : Observable<InstEmit<A>>              -- hand-built
--   slot        : Observable<Observable<InstEmit<A>>>  -- carries it
--   theInput    : Observable<InstEmit<Observable<InstEmit<A>>>>
--
-- where the outer envelope is honest and the inner one was never
-- issued.  A machine-checked table walked through exactly this,
--
--   shared (ofᵉ (strmᵗ (mintᵉ (ofᵉ (instEmitᵛ nilᵗ tok tok deliveryᵛ ∷ []))))
--                ∷ [])
--
-- driving the protocol automaton to `nothing`: a `delivery` whose
-- source no `init` ever enlisted, with the author having written
-- nothing unusual.
--
-- WHY `inputᵖ` CANNOT ANSWER IT, which is the first place to look.
-- `inputᵖ` wraps the CARRIER; here the CARGO is already a stream, and
-- no wrapper applied to the outside reaches inside one.  The two
-- repairs available are therefore to make `inputᵖ` recurse -- wrapping
-- at every depth, so the slot could stand at the author's bare type --
-- or to make the cargo never BE a stream.  This is the second.  It is
-- the cheaper of the two and it is also what the surface says: srxjs
-- overloads `wrapCold` to return `never` on an
-- `Observable<Observable<A>>`.
--
-- WHY THE SCRIPTED ARM LOOKS REDUNDANT AND IS NOT.  It carried
-- `isData` long before any of this, for DESCENT: a value at observable
-- type is a body paired with an environment, so an obs-typed script
-- could emit the very program being walked, and the *All hop off it
-- would be asked to descend from a rank to itself.  The regress is
-- real, not merely undescending -- such a program re-enters itself
-- unboundedly -- so no edge can pay for it.  That bar closed the
-- legality hole on the scripted arm as a side effect, which is why
-- hot and cold were never implicated; `shared` was simply the arm
-- still open.  Both reasons are now live on both arms and neither is
-- load-bearing alone.
--
-- WHAT `subs-shared` HAS TO DO WITH IT, SINCE IT IS EASY TO OVERSTATE.
-- It is not a second channel.  It subscribes a definition STRAIGHT
-- DOWN the consumer's path -- no `inputᵖ`, no `stamp` -- which sounds
-- like one, and at a DATA type it is harmless for a reason worth
-- keeping: the reference site elaborates to `inputᵖ i`, whose
-- deliveries arm is `mergeAllᵉ (mapᵉ stamp (batchSyncᵉ (input i)))`,
-- and `subs-shared` fires at that INNER `input i`, so the definition
-- is substituted UNDER `stamp` and is wrapped on its way out.  That is
-- Probed.Share-Channel's probe D, and it is why a data-typed share
-- needs no condition beyond the one above.  At an observable type
-- `subs-shared` adds nothing the type had not already opened.
--
-- `isData` bars all of it, and bars an observable buried in a product
-- or a list with it, since `isData` recurses.
--
-- WHAT THE BAR COSTS, WHICH IS NOTHING.  It deletes the slot that
-- SUPPLIES observables -- and no such slot is generated, decoded or
-- tested.  The TS generator draws every slot type from `genValTy`,
-- whose comment reads "value types only (no obs)", and marks the `obs`
-- arm of `genVal` unreachable "slots are value-typed".  The library's
-- own surface says the same: `wrapCold` is overloaded to return
-- `never` on an `Observable<Observable<A>>`, so a consumer of srxjs
-- cannot build one either.  The restriction is the spec, not the
-- proof narrowing the evaluator behind the spec's back.
--
-- THE TELESCOPE IS STRATIFIED (`inputsBelowᵉ k`): slot k's def may
-- reference only inputs at indices strictly below k -- a real JS
-- `const` telescope, where reading a later `const` is a TDZ error,
-- and exactly what the TS generator builds (a def is generated
-- against the strict prefix of earlier slot types).  The index `k`
-- is a parameter of `Slot` so the side condition can name it; like
-- `isData`, it discharges by unification at every concrete program.
-- What it buys: any per-slot reading is computable by recursion on
-- the slot index, since slot k's def consults only slots j < k.
-- Without it a slot's reading would have to be sought as a
-- simultaneous solution over the whole table.
data Slot {n} (Γ : Ctx n) (k : ℕ) (t : Ty) : Set where
  scripted : {ok : T (isData t)} → ObservableInput (Val Γ t) → Slot Γ k t
  shared   : (d : Closed Γ t) {ok : T (isData t)}
           → {ok′ : T (inputsBelowᵉ k d)} → Slot Γ k t

Slots : ∀ {n} → Ctx n → Set
Slots Γ = ∀ i → Slot Γ (toℕ i) (lookup Γ i)
