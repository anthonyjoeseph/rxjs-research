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
-- identical, the expression is a phantom in both initialisers.  `Inv`
-- is seeded by the root subscribe and preserved per cascade, and
-- `drain-sound` below inducts on fuel to mirror `drain!` clause for
-- clause -- which is why it is a BODY and not a third leaf.
module Verify-Input-Well-Formed.Run-Well-Formed where

open import Data.Fin     using (Fin)
open import Data.List    using (List; []; _∷_; _++_; concat)
open import Data.List.Properties using (++-assoc)
open import Data.Maybe   using (just)
open import Data.Product using (Σ; _×_; _,_; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Rx.Prim     using (Fuel; InstEmit; PlainEvent; valueᵖ; completeᵖ)
open import Rx.Exp      using (Ctx; Closed; Val; []ᵉ)
open import Rx.SExp     using (inputˢ; plainᵛ)
open import Rx.Slots    using (Slots)
open import Rx.Elaborate using (elaborate)
open import Rx.Envelope using (machineEmitᵗ)
open import Rx.Envelope.Decode using (decodeStream)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; Stream;
                                sched-init; st-init; root)
open import Rx.Evaluator.Domain using (subscribeE⇓; cascade⇓; drain⇓;
                                       evaluate⇓; eval-run;
                                       drain-done; drain-empty; drain-step)
open import Rx.Evaluator.Builder using (evaluate!; evaluate↓)
open import Rx.Protocol using (ProtocolSt; protocol-init; runProtocol;
                               stepProtocol; Accepted; accepted)
open import Decide      using (just-injᵂ)

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

-- the automaton's run splits at any point its first half accepts
runProtocol-++ : ∀ {A : Set} (xs ys : List (InstEmit A)) (S S′ : ProtocolSt) →
  runProtocol S xs ≡ just S′ → runProtocol S (xs ++ ys) ≡ runProtocol S′ ys
runProtocol-++ []       ys S S′ eq rewrite just-injᵂ eq = refl
runProtocol-++ (x ∷ xs) ys S S′ eq with stepProtocol x S
... | just S₁ = runProtocol-++ xs ys S₁ S′ eq

------------------------------------------------------------------
-- The invariant, and the two leaves over it.
------------------------------------------------------------------

-- THE COUPLING BETWEEN THE EVALUATOR'S STATE AND THE AUTOMATON'S,
-- SAMPLED BETWEEN CASCADES.  Its SHAPE is forced and its CONTENT is
-- the open design question, which is why it is a leaf: minting a
-- definition here would be asserting the answer rather than scheduling
-- it.  What it has to say is read straight off `ProtocolSt`'s fields:
--
--   live    ↔ the REGISTRY.  The protocol's live-source multiset is the
--             registry's per-source chain count.  This is the heart of
--             it -- `settle` seeds an instant's owed from `countIn s
--             live`, so a registry that disagrees makes every delivery
--             underflow or over-owe.  It is also the clause the refuted
--             `evaluate-accepted` never had.
--   horizon ↔ the MINT COUNTER.  Every instant already emitted is below
--             the next token a `mintᵉ` will draw, so freshness falls
--             out of the counter being monotone rather than out of any
--             claim about the program.
--   current ↔ whether a cascade is in flight, and its outstanding owed
--             against the chains that have not yet folded.
--   done    ↔ completedSources.
--
-- WHAT IT DOES NOT HAVE TO SAY, and the reason the sampling point is
-- named: `delivered`, `cancelled` and `dying` are per-cascade
-- bookkeeping that a cascade resets, so an invariant read BETWEEN
-- cascades never sees them mid-flight and owes them nothing.
--
-- AND IT IS STATED OVER THE REGISTRY RATHER THAN OVER THE SLOT TABLE,
-- which is where the earlier reading of this obligation was aimed.  A
-- predicate on the slots answers the wrong question: the table is what
-- SEEDS the run, and what `settle` reads is the registry the run has
-- built, which a share's fan-out and a take's cut both rewrite while
-- the table stands still.
postulate
  Inv : ∀ {n} {Γ : Ctx n} {a} {e : Closed Γ (machineEmitᵗ a)}
      → Sched Γ → EvalSt e → ProtocolSt → Set

-- LEAF: the root subscribe seeds the invariant, and its own burst is
-- accepted from the empty protocol state.  This is the BASE CASE, and
-- it is the one the previous attempt could not state honestly -- with
-- the slot at the envelope type an arbitrary script reached the output
-- through `input` untouched, so no claim of this shape was true.  With
-- `inputᵖ` performing the wrap, every envelope a source contributes is
-- built by a term in `Rx.Elaborate` and the burst is a lemma about
-- those terms.
postulate
  subscribe-sound :
    ∀ {n} {Γ : Ctx n} {a} {e : Closed Γ (machineEmitᵗ a)} {ins : Slots Γ}
      {burst sched₀ st₀} →
    subscribeE⇓ {e = e} {lo = n} ([] , e , []ᵉ) root 0
      (sched-init e ins) (st-init e) (burst , sched₀ , st₀) →
    Σ ProtocolSt λ S₀ →
        (runProtocol protocol-init (decodeStream (concat burst)) ≡ just S₀)
      × Inv sched₀ st₀ S₀

-- LEAF: one cascade preserves the invariant and emits only what the
-- automaton accepts from the state the invariant names.  THIS is where
-- the per-former split lives, and where the per-emission reasoning is
-- honest: `map-f` and `scan-f` leave `sched` and `st` untouched and
-- rebuild each emit under the incoming envelope's own instant, source
-- and kind, so the automaton takes the SAME transition and those arms
-- are cheap.  The traffic-bearing frames -- the cut, the three
-- flatteners, a share's connect -- are where the content is.
--
-- The scheduler is threaded exactly as `drain-step` threads it: the
-- invariant holds of `sched` BEFORE `sched-next`, and the cascade runs
-- on what `sched-next` left.  Stating it over the popped scheduler
-- instead would oblige a separate claim that popping preserves `Inv`.
postulate
  cascade-sound :
    ∀ {n} {Γ : Ctx n} {a} {e : Closed Γ (machineEmitᵗ a)}
      {ar : Arrival Γ} {sched sched′ sched″ st st′ out} {S : ProtocolSt} →
    Inv {e = e} sched st S →
    cascade⇓ {e = e} ar sched′ st (out , sched″ , st′) →
    Σ ProtocolSt λ S′ →
        (runProtocol S (decodeStream (concat out)) ≡ just S′)
      × Inv sched″ st′ S′

------------------------------------------------------------------
-- The drain, by induction on fuel -- a BODY, not a leaf.
------------------------------------------------------------------

-- THE WHOLE POINT OF THE ROUTE IS THAT THIS IS WRITABLE.  It mirrors
-- `drain!` clause for clause: `drain-done` and `drain-empty` emit
-- nothing, so the automaton stands still; `drain-step` is one cascade
-- spliced onto the tail by the induction hypothesis.  Fuel is the
-- recursion the evaluator actually performs, so the induction lines up
-- with the code instead of fighting it.
drain-sound :
  ∀ {n} {Γ : Ctx n} {a} {e : Closed Γ (machineEmitᵗ a)}
    {fuel : Fuel} {sched : Sched Γ} {st : EvalSt e} {rest} {S : ProtocolSt} →
  Inv {e = e} sched st S →
  drain⇓ {e = e} fuel sched st rest →
  Σ ProtocolSt λ S′ →
    runProtocol S (decodeStream (concat rest)) ≡ just S′
drain-sound {S = S} inv drain-done       = S , refl
drain-sound {S = S} inv (drain-empty _)  = S , refl
drain-sound {Γ = Γ} {S = S} inv (drain-step {out = out} {rest = rest} eqn c d)
  with cascade-sound inv c
... | S′ , accOut , inv′ with drain-sound inv′ d
...   | S″ , accRest =
      S″ , trans (cong (runProtocol S) (trans (cong decodeStream (concat-++ out rest))
                                               (decodeStream-++ (concat out) (concat rest))))
                 (trans (runProtocol-++ (decodeStream (concat out))
                                        (decodeStream (concat rest)) S S′ accOut)
                        accRest)

------------------------------------------------------------------
-- THE STATEMENT.
------------------------------------------------------------------

-- EVERY RUN OF EVERY ELABORATED PROGRAM DECODES TO AN ACCEPTED
-- STREAM.  A real body: the subscribe burst seeds the invariant, the
-- drain preserves it, and the two splice.  Quantified over the plain
-- tree rather than over `SExp`, because the two leaves above are about
-- the EVALUATOR and know nothing of the author's syntax -- so the
-- simul statement below is an instance of this one rather than a
-- separate claim.
-- The index is GENERALISED before the derivation is matched on:
-- `evaluate⇓`'s stream argument is `burst ++ rest`, and matching it
-- against `proj₁ (evaluate! …)` in place loses the connection between
-- the two halves and the term. Abstracting the stream, then
-- instantiating at the builder's own projection, is what keeps it.
run-wellFormed⇓ :
  ∀ {n} {Γ : Ctx n} {a} {fuel : Fuel} {e : Closed Γ (machineEmitᵗ a)}
    {ins : Slots Γ} (s : Stream Γ (machineEmitᵗ a)) →
  evaluate⇓ fuel e ins s →
  Accepted (runProtocol protocol-init (decodeStream (concat s)))
run-wellFormed⇓ _ (eval-run {burst = burst} {rest = rest} sub dr)
  with subscribe-sound sub
... | S₀ , accBurst , inv₀ with drain-sound inv₀ dr
...   | S₁ , accRest = subst Accepted (sym eq) accepted
      where
      dEq : decodeStream (concat (burst ++ rest))
              ≡ decodeStream (concat burst) ++ decodeStream (concat rest)
      dEq = trans (cong decodeStream (concat-++ burst rest))
                  (decodeStream-++ (concat burst) (concat rest))

      eq : runProtocol protocol-init (decodeStream (concat (burst ++ rest)))
             ≡ just S₁
      eq = trans (cong (runProtocol protocol-init) dEq)
                 (trans (runProtocol-++ (decodeStream (concat burst))
                                        (decodeStream (concat rest))
                                        protocol-init S₀ accBurst)
                        accRest)

run-wellFormed :
  ∀ {n} {Γ : Ctx n} {a} (fuel : Fuel) (e : Closed Γ (machineEmitᵗ a))
    (ins : Slots Γ) →
  Accepted (runProtocol protocol-init
             (decodeStream (concat (evaluate↓ fuel e ins))))
run-wellFormed fuel e ins = run-wellFormed⇓ _ (proj₂ (evaluate! fuel e ins))