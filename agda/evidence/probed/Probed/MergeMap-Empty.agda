-- WHY `batchSimultaneousᵖ` MAY USE `mergeAllᵉ`, AND WHY THE NOTE THAT
-- SAID IT MAY NOT WAS WRONG.
--
-- `Rx.Batch` used to read: "IT MUST SUBSCRIBE NOTHING.  A `mergeAllᵉ`
-- formulation moves the mint counter and leaves every id downstream
-- shifted by a renaming, so the two runs the theorem compares would no
-- longer share a scheduler."  That ruled out the one shape a batcher
-- needs -- DECLINING TO EMIT -- and left the operator a postulate,
-- because a `scanᵉ` is one value in and one value out while a batcher
-- is one in and zero-or-one out.
--
-- WHAT THE RELATION SAYS.  `subs-merge-all` and `subscribeInner⇓` mint
-- at `nodeᵏ` and at no other key; only `subs-defer` mints a `sourceᵏ`,
-- and a synchronous inner never reaches it.  Node instances live in the
-- registry and never appear on the wire, which carries `sourceᵏ` ids
-- (init/close) and `mintᵉ` tokens (instants).  `subs-scan` mints a
-- `nodeᵏ` too -- so the shape the note recommended was paying the same
-- cost it warned about.
--
-- WHAT THE RUN SAYS, which is the point of this file.  Both readings
-- below are `refl`.
--
-- THE BASELINE IS CHECKED FIRST AND THAT IS NOT CEREMONY.  An earlier
-- version of this probe used a slot-fed program that ran DRY at this
-- fuel, so every reading compared `[]` against `[]` and the file was
-- green while saying nothing.  `nonvacuous` is what makes the two
-- readings below mean something; it is stated as a refutation because
-- there is no positive form of "this list is not empty" that does not
-- also pin its contents.
module Probed.MergeMap-Empty where

open import Data.List using (List; []; _∷_; concat)
open import Data.Maybe using (nothing)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (InstEmit)
open import Rx.Exp using (Ctx; natᵗ; Closed; Val; ofᵉ; mapᵉ; mergeAllᵉ;
                          emptyᵉ; varᵗ; strmᵗ)
open import Rx.SExp using (ofˢ; natˢ; plainᵏ; Kinds; emitᵗ)
open import Rx.Elaborate using (elaborate)
open import Rx.Slots using (Slots)
open import Rx.Envelope.Decode using (decodeStream)
open import Rx.Evaluator.Builder using (evaluate↓)

-- NO SLOTS AT ALL: a pure synchronous source, so nothing here can go
-- dry and an empty reading would mean something rather than nothing.
Γ₀ : Ctx 0
Γ₀ = []ⱽ

κ₀ : Kinds 0
κ₀ = []ⱽ

Γ₀ᵉ : Ctx 0
Γ₀ᵉ = plainᵏ Γ₀ κ₀

ins₀ : Slots Γ₀ᵉ
ins₀ ()

prog : Closed Γ₀ᵉ (emitᵗ natᵗ)
prog = elaborate κ₀ (ofˢ (natˢ 7 ∷ natˢ 9 ∷ []))

-- the identity mergeMap: every value becomes a one-element inner
idMM : Closed Γ₀ᵉ (emitᵗ natᵗ) → Closed Γ₀ᵉ (emitᵗ natᵗ)
idMM e = mergeAllᵉ nothing (mapᵉ (strmᵗ (ofᵉ (varᵗ (here refl) ∷ []))) e)

-- and the DECLINING one: every value becomes EMPTY
noMM : Closed Γ₀ᵉ (emitᵗ natᵗ) → Closed Γ₀ᵉ (emitᵗ natᵗ)
noMM e = mergeAllᵉ nothing (mapᵉ (strmᵗ emptyᵉ) e)

run : Closed Γ₀ᵉ (emitᵗ natᵗ) → List (InstEmit (Val Γ₀ᵉ natᵗ))
run e = decodeStream {Γ = Γ₀ᵉ} {a = natᵗ} (concat (evaluate↓ 60 e ins₀))

-- the baseline emits: without this the two readings below are vacuous
nonvacuous : run prog ≡ [] → ⊥
nonvacuous ()

-- THE WRAPPER IS TRANSPARENT ON THE WIRE
transparent : run (idMM prog) ≡ run prog
transparent = refl

-- AND DECLINING IS SILENT
silent : run (noMM prog) ≡ []
silent = refl
