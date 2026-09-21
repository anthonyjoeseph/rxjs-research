------------------------------------------------------------------
-- THE RUN'S HALF OF THE SANDWICH: every run of an elaborated program
-- decodes to a stream the protocol automaton accepts.
------------------------------------------------------------------

-- WHAT THIS MODULE IS FOR.  `batch-agreement` proves the batcher
-- matches the spec on any ACCEPTED stream, and it is postulate-free.
-- What the top line still owes is the step from a RUN to an accepted
-- stream, and that is what is stated here.
--
-- THE INDUCTION IS ON THE RUN AND NOT ON THE TREE, AND THAT IS A
-- MEASURED FINDING RATHER THAN A PREFERENCE.  The obvious shape is to
-- induct on `SExp`, assuming a subtree's run is accepted and showing
-- each former preserves it.  It does not work, because `evaluate↓` is
-- not structurally recursive on the expression: a run is a subscribe
-- burst followed by a DRAIN, and `drain!` recurses on FUEL over a flat
-- scheduler queue, taking the expression only as an implicit index.
-- Every `delivery`-kind emit -- which is every instant carrying values,
-- which is the whole subject of batching -- is produced there, so a
-- tree induction reaches only the half that does not matter.
--
-- PROBED: `mapᵉ` compositionality, the most favourable former in the
--   palette -- `step-map` passes `sched` and `st` through untouched and
--   `frameNodes (map-f _) ≡ []`, so it installs nothing and burns no
--   fuel.  Three facts typecheck by `refl`:
--   `sched-init (mapᵉ f b) ins ≡ sched-init b ins` (the two runs share
--   a scheduler outright -- `sched-init` and `st-init` both IGNORE
--   their expression argument, and `NodeSt e` is phantom in `e`), both
--   initial registries are `[]`, and the whole difference between the
--   runs is a definable transport that re-roots every registry path
--   through `map-f`.
-- DEAD ROUTE: proving that transport correct.  It must commute with
--   the evaluator, and the evaluator is TWENTY mutually-defined `⇓`
--   relations; `subs-map` alone reaches `pushBurst⇓`, `stepFrame⇓`,
--   `innerReact⇓` and `subscribeAll⇓` and back.  Worse, the transport
--   changes the ROOT TYPE, which is a parameter of all twenty -- so it
--   is a twenty-way mutual commutation stated HETEROGENEOUSLY, across
--   two expressions at two root types, re-running a well-founded
--   recursion.  For the easiest former there is.  Fuel accounting was
--   the expected obstruction and is not one; the type indexing is.
--
-- SO THE INVARIANT GOES ON THE STATE, WHICH IS WHERE THE PROBE SAYS
-- THE RUN ACTUALLY LIVES.  The same measurements that killed the tree
-- route recommend this one: the scheduler is shared, the state starts
-- identical, the expression is a phantom in both initialisers.
--
-- AND THE AUTOMATON'S HALF IS NO LONGER HERE AT ALL.  It moved to
-- `Well-Shaped`, where it is PROVEN: `runProtocol` is a pure fold, so
-- acceptance is characterised by a predicate over the stream alone,
-- and `stepProtocol`'s seven reachable rejection sites are that
-- predicate's premises, one for one.  What is left in this module is
-- the evaluator's half -- two leaves -- and ONE coupling, `Owes`,
-- whose content the census pins down exactly.
module Verify-Input-Well-Formed.Run-Well-Formed where

open import Data.Fin     using (Fin)
open import Data.List    using (List; []; _∷_; _++_; concat; length)
open import Data.List.Properties using (++-assoc)
open import Data.Maybe   using (just)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Rx.Prim     using (Fuel; InstEmit; PlainEvent; valueᵖ; completeᵖ)
open import Rx.Exp      using (Ctx; Closed; Val; []ᵉ)
open import Rx.SExp     using (inputˢ; plainᵛ)
open import Rx.Authored using (Authᵉ)
open import Rx.Palette.SExp using (sexpPalette)
open import Rx.Slots sexpPalette using (Slots)
open import Rx.Elaborate using (elaborate)
open import Rx.Envelope using (machineEmitᵗ)
open import Rx.Envelope.Decode using (decodeStream)
open import Rx.Evaluator sexpPalette using (Sched; EvalSt; Arrival; Stream;
  chainsOf; arrSource; sched-init; st-init; root)
open import Rx.Evaluator.Domain sexpPalette using (subscribeE⇓; cascade⇓; drain⇓;
                                       evaluate⇓; eval-run;
                                       drain-done; drain-empty; drain-step)
open import Rx.Evaluator.Builder sexpPalette using (evaluate!; evaluate↓)
open import Rx.Protocol using (ProtocolSt; protocol-init; runProtocol;
                               countIn; Accepted; accepted)
open import Verify-Input-Well-Formed.Well-Shaped using
  (WellShaped; ws-nil; ws-++; wellShaped-accepted)

------------------------------------------------------------------
-- Glue: the three ways a run's two halves are spliced.
------------------------------------------------------------------

-- CONCATENATION SURVIVES EVERY STAGE BETWEEN THE RUN AND THE
-- AUTOMATON, which is what lets a burst and a drain be reasoned about
-- separately and then joined.  All three are the obvious inductions;
-- they are here rather than in a shared module because nothing else
-- crosses all three levels.

concat-++ : ∀ {A : Set} (xss yss : List (List A)) →
  concat (xss ++ yss) ≡ concat xss ++ concat yss
concat-++ []         yss = refl
concat-++ (xs ∷ xss) yss =
  trans (cong (xs ++_) (concat-++ xss yss))
        (sym (++-assoc xs (concat xss) (concat yss)))

decodeStream-++ : ∀ {n} {Γ : Ctx n} {a}
  (xs ys : List (PlainEvent (Val Γ (machineEmitᵗ a)))) →
  decodeStream (xs ++ ys) ≡ decodeStream xs ++ decodeStream ys
decodeStream-++ []              ys = refl
decodeStream-++ (valueᵖ e ∷ xs) ys = cong (_ ∷_) (decodeStream-++ xs ys)
decodeStream-++ (completeᵖ ∷ xs) ys = decodeStream-++ xs ys

------------------------------------------------------------------
-- The one coupling, and the two leaves over it.
------------------------------------------------------------------

-- THE SINGLE PLACE THE EVALUATOR'S STATE REACHES THE WIRE.
--
-- Of `stepProtocol`'s seven reachable rejection sites, four are
-- ordering and bracketing facts about the stream and are settled
-- inside `Well-Shaped`.  The other three -- over-delivery, under-
-- delivery, and an emit into an already-settled instant -- are one
-- scalar equation seen from three directions, and it is this one:
-- every arrival fans out to exactly as many chains as its source has
-- live announces on the wire.
--
-- IT IS DEFINED, NOT POSTULATED, because a named predicate with an
-- unknown body is what four refuted guesses looked like.  With a body
-- it is checkable against the elaboration as `toPlain` is written --
-- which is the point of having the proof before the implementation.
-- Expect it to be wrong in detail and corrected by contact.
--
-- NOTE WHICH NAMESPACE EACH SIDE COUNTS IN.  `chainsOf` counts
-- registry rows, which carry the evaluator's dynamic source ids;
-- `ProtocolSt.live` counts announces, which carry the ids
-- `Rx.Elaborate` bound with `mintᵉ`.  Measured, those differ -- a
-- registry row reading `4` against a wire reading `3`, both off the
-- one `sourceᵏ` mint at two different moments.  `arrSource` is the
-- arrival's own id, so the equation below holds only if the arrival
-- carries the WIRE's naming.  That is a requirement on the
-- elaboration, and stating it here is what makes it one.
Owes : ∀ {n} {Γ : Ctx n} {a} {e : Closed Γ (machineEmitᵗ a)}
     → EvalSt e → ProtocolSt → Set
Owes {Γ = Γ} st S =
  ∀ (ar : Arrival Γ) →
    length (chainsOf ar st) ≡ countIn (arrSource ar) (ProtocolSt.live S)

-- LEAF 1: the root subscribe emits a well-shaped burst and leaves the
-- two ledgers agreeing.  `st-init`'s registry is empty and
-- `protocol-init`'s live set is empty, so the seed is trivial; the
-- content is what the subscribe walk installs on the way down.
postulate
  subscribe-shaped :
    ∀ {n} {Γ : Ctx n} {a} {e : Closed Γ (machineEmitᵗ a)} {ins : Slots Γ}
      {burst sched₀ st₀} →
    Authᵉ e →
    subscribeE⇓ {e = e} {lo = n} ([] , e , []ᵉ) root 0
      (sched-init e ins) (st-init e) (burst , sched₀ , st₀) →
    Σ ProtocolSt λ S₀ →
        WellShaped protocol-init (decodeStream (concat burst)) S₀
      × Owes st₀ S₀

-- LEAF 2: one cascade emits a well-shaped burst and preserves the
-- agreement.
--
-- ITS AUTHORSHIP PREMISE IS ON `e` AND THAT IS PROBABLY NOT YET
-- ENOUGH, which is worth saying before the grind rather than after.
-- `Authᵉ e` says the ROOT is authored; what this leaf walks is `st`,
-- whose nodes were installed by subscribing `e` and are therefore
-- authored in any REAL run -- but `st` is universally quantified here,
-- so nothing in the statement says so.  The missing piece is a
-- node-authorship invariant on `EvalSt`, carried alongside `Owes` and
-- threaded by `drain-shaped` exactly as `Owes` already is.  It is not
-- written because guessing its shape is the expensive kind of mistake:
-- `Owes` itself replaced two guessed bridge clauses that measurement
-- refuted.  What settles it is the first traffic-bearing frame -- the
-- cut, or a share's connect -- since that is where a node is read back
-- out of the registry and the invariant has to be strong enough to
-- survive it.  THIS is where the per-former split belongs, and where
-- the remaining work is: `map-f` and `scan-f` leave `sched` and `st`
-- untouched and rebuild each emit under the incoming envelope's own
-- instant, source and kind, so the automaton takes the same
-- transition and those arms are cheap.  The traffic-bearing frames --
-- the cut, the three flatteners, a share's connect -- are where the
-- content is, and they are exactly the srxjs operators whose
-- implementations this proof exists to judge.
postulate
  cascade-shaped :
    ∀ {n} {Γ : Ctx n} {a} {e : Closed Γ (machineEmitᵗ a)}
      {ar : Arrival Γ} {sched′ sched″ st st′ out} {S : ProtocolSt} →
    Authᵉ e →
    Owes {e = e} st S →
    cascade⇓ {e = e} ar sched′ st (out , sched″ , st′) →
    Σ ProtocolSt λ S′ →
        WellShaped S (decodeStream (concat out)) S′
      × Owes st′ S′

------------------------------------------------------------------
-- The drain, by induction on fuel -- a BODY, not a leaf.
------------------------------------------------------------------

-- IT MIRRORS `drain!` CLAUSE FOR CLAUSE: `drain-done` and
-- `drain-empty` emit nothing, so the automaton stands still;
-- `drain-step` is one cascade spliced onto the tail by the induction
-- hypothesis.  Fuel is the recursion the evaluator actually performs,
-- so the induction lines up with the code instead of fighting it.
--
-- AND THE SPLICE IS NOW STRUCTURAL.  `ws-++` joins two well-shaped
-- stretches whose endpoints meet, so nothing here reasons about
-- `runProtocol` at all -- the previous version needed a
-- `runProtocol-++` and two transports to say the same thing.
drain-shaped :
  ∀ {n} {Γ : Ctx n} {a} {e : Closed Γ (machineEmitᵗ a)}
    {fuel : Fuel} {sched : Sched Γ} {st : EvalSt e} {rest} {S : ProtocolSt} →
  Authᵉ e →
  Owes {e = e} st S →
  drain⇓ {e = e} fuel sched st rest →
  Σ ProtocolSt λ S′ → WellShaped S (decodeStream (concat rest)) S′
drain-shaped {S = S} au ow drain-done      = S , ws-nil
drain-shaped {S = S} au ow (drain-empty _) = S , ws-nil
drain-shaped {S = S} au ow (drain-step {out = out} {rest = rest} _ c d)
  with cascade-shaped au ow c
... | S′ , wsOut , ow′ with drain-shaped au ow′ d
...   | S″ , wsRest =
      S″ , subst (λ z → WellShaped S z S″) (sym dEq) (ws-++ wsOut wsRest)
      where
      dEq : decodeStream (concat (out ++ rest))
              ≡ decodeStream (concat out) ++ decodeStream (concat rest)
      dEq = trans (cong decodeStream (concat-++ out rest))
                  (decodeStream-++ (concat out) (concat rest))

------------------------------------------------------------------
-- The statement.
------------------------------------------------------------------

-- EVERY RUN OF EVERY ELABORATED PROGRAM DECODES TO AN ACCEPTED
-- STREAM.  A real body: the subscribe burst and the drain are each
-- well-shaped, `ws-++` joins them, and `wellShaped-accepted` turns
-- the join into acceptance.  Quantified over the plain tree rather
-- than over `SExp`, so the simul statement is an instance of this one
-- rather than a separate claim.
--
-- IT CARRIES `Authᵉ e`, AND THE COMMENT THAT USED TO STAND HERE GAVE
-- THE REASON IT WAS WRONG AS THE REASON IT WAS RIGHT: "the two leaves
-- know nothing of the author's syntax."  They do not need the author's
-- syntax; they need to know there IS one.  Without the premise the
-- statement is FALSE, and not subtly -- `sexpPalette` shut the forgery
-- channel in the slot TABLE and left the ROOT PROGRAM arbitrary, so
-- the same three lines that inhabited the table's gap inhabit this
-- one: `mintᵉ (ofᵉ (instEmitᵛ nilᵗ tok tok deliveryᵛ ∷ []))` is
-- rejected by `refl` against an ordinary one-input table
-- (Refuted.Forged-Root).
--
-- The index is GENERALISED before the derivation is matched on:
-- `evaluate⇓`'s stream argument is `burst ++ rest`, and matching it
-- against `proj₁ (evaluate! ...)` in place loses the connection
-- between the two halves and the term.
run-wellFormed⇓ :
  ∀ {n} {Γ : Ctx n} {a} {fuel : Fuel} {e : Closed Γ (machineEmitᵗ a)}
    {ins : Slots Γ} (s : Stream Γ (machineEmitᵗ a)) →
  Authᵉ e →
  evaluate⇓ fuel e ins s →
  Accepted (runProtocol protocol-init (decodeStream (concat s)))
run-wellFormed⇓ _ au (eval-run {burst = burst} {rest = rest} sub dr)
  with subscribe-shaped au sub
... | S₀ , wsBurst , ow₀ with drain-shaped au ow₀ dr
...   | S₁ , wsRest =
      wellShaped-accepted (subst (λ z → WellShaped protocol-init z S₁)
                                 (sym dEq) (ws-++ wsBurst wsRest))
      where
      dEq : decodeStream (concat (burst ++ rest))
              ≡ decodeStream (concat burst) ++ decodeStream (concat rest)
      dEq = trans (cong decodeStream (concat-++ burst rest))
                  (decodeStream-++ (concat burst) (concat rest))

run-wellFormed :
  ∀ {n} {Γ : Ctx n} {a} (fuel : Fuel) (e : Closed Γ (machineEmitᵗ a))
    (ins : Slots Γ) →
  Authᵉ e →
  Accepted (runProtocol protocol-init
             (decodeStream (concat (evaluate↓ fuel e ins))))
run-wellFormed fuel e ins au = run-wellFormed⇓ _ au (proj₂ (evaluate! fuel e ins))
