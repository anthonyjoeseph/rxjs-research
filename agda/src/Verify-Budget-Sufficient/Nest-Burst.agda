------------------------------------------------------------------
-- HOW WIDE THE DESCENT GETS, WHICH IS NOT HOW WIDE ITS ANSWER IS.
--
-- A subscribe's nest charge is a power in the burst it hands back --
-- that much a refutation settled, at a step function applied once per
-- value.  But the INDUCTION runs on the expression, and the inner
-- descent's own conclusion is a power in the INNER burst, so a bound on
-- what leaves the outer frame has to bound what left the inner one too.
--
-- FOUR OF THE FIVE RECURSIVE HEADS GIVE THAT FOR FREE and one does not.
-- A source mints its own burst and recurses nowhere; `map` and `scan`
-- hand back one value per value they were given; a `*All` head pushes
-- the outer's burst through a frame that emits per emit.  `take` DROPS,
-- and a bound on the output of a filter is no bound on its input --
-- which is why this measure exists rather than the length of the answer.
--
-- SO THE PREMISE IS ABOUT THE WHOLE DESCENT.  `descW` is the largest
-- burst produced anywhere under one subscribe, by recursion on
-- `subscribeE`'s own recursive positions, and every head reads off both
-- its own conjunct and its child's by a projection out of one `⊔`.
--
-- THE SLOT HEAD IS A LEAF HERE ON PURPOSE.  A shared slot's connect
-- re-enters the walk, so the descent genuinely continues past it; the
-- statement it feeds is a leaf that calls no inductive hypothesis, so
-- widening the measure to reach the connect would buy a premise nothing
-- consumes.  When that leaf splits, the measure splits with it.
--
-- AND IT IS SEALED.  This lands in a PREMISE, so a transparent body is
-- normalised at every application of every statement carrying it, and
-- the body recurses on the evaluator.  The equations below are the
-- interface: each is `refl` inside the block and nothing outside needs
-- more than the one for the head it is at.
--
-- SO A HEAD'S PROJECTION IS MINTED WITH THAT HEAD'S BODY, one line of
-- `⊔`-elimination each, and not a moment before.  The nine heads land
-- one at a time and a projection ahead of its consumer is a definition
-- with no route home -- which the wiring gate calls what it is.
------------------------------------------------------------------
module Verify-Budget-Sufficient.Nest-Burst where

open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; nothing)
open import Data.Bool using (false; T)
open import Data.Nat using (ℕ; suc; _⊔_; _≤_)
open import Data.Nat.Properties using (≤-refl; ≤-reflexive; ≤-trans; m≤m⊔n; m≤n⊔m; ⊔-identityʳ)
open import Data.Fin using (Fin; toℕ)
open import Data.Vec using (lookup)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)

open import Rx.Prim using (Tick; Id; Gas; g0; gs; ObservableInput)
open import Rx.Exp using
  (Ctx; Closed; Exp; Val; Fn; Tm; natᵗ; obs; _×ᵗ_; unfoldμ; evalTm; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ;
  switchAllᵉ; exhaustAllᵉ; μᵉ; input; inputsBelowᵉ; ofᵉ; emptyᵉ; deferᵉ;
  isData)
open import Rx.Slots using (Slot; scripted; shared)
open import Rx.Evaluator using
  (Sched; EvalSt; Path; _↠_; map-f; scan-f; take-f; thru-outer; from-inner; NodeId;
   AllOp; mergeAllᵒ; switchᵒ; exhaustᵒ; scan-st; take-st; mergeAll-st; switch-st; exhaust-st;
   mintNode; installNode; subscribeE; subscribeInner; splitBurst;
   share-sink; register)

abstract
  -- THE BURST ONE SUBSCRIBE HANDS BACK, named so the recursion below
  -- reads as `this one, and the child's`.
  burstW : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    → Gas → Closed Γ u → Path Γ u t → Id → Tick → Sched Γ → EvalSt e → ℕ
  burstW {Γ = Γ} {t = t} g o κ id now sched st =
    length (proj₁ (splitBurst {A = Val Γ t}
              (proj₁ (subscribeE g o κ id now sched st))))

  -- THE SEAL'S WHOLE CONTENT AT THIS NAME, exported for the one
  -- consumer that cannot be served by a projection: a statement ABOUT
  -- this reading rather than a bound carrying it.  The seal keeps the
  -- evaluator out of every premise that names the measure; a leaf
  -- asserting something about the measure is the one place the body has
  -- to be visible, since a claim nothing can instantiate is a claim
  -- nothing can refute.
  burstW-eq : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (o : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) →
    burstW g o κ id now sched st
      ≡ length (proj₁ (splitBurst {A = Val Γ t}
                  (proj₁ (subscribeE g o κ id now sched st))))
  burstW-eq g o κ id now sched st = refl

  connW : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    → Gas → (i : Fin n) → Closed Γ (lookup Γ i) → Path Γ (lookup Γ i) t
    → Id → Tick → Sched Γ → EvalSt e → ℕ

  -- THE SPLIT IS A NAMED FUNCTION OF THE SLOT, not a `with` and not a
  -- where-helper, because the projection below is a `cong` OVER IT: a
  -- consumer holds the slots equation and needs the two readings to be
  -- the same term applied to the two sides of it.
  slotW : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    → Gas → (i : Fin n) → Path Γ (lookup Γ i) t
    → Id → Tick → Sched Γ → EvalSt e → Slot Γ (toℕ i) (lookup Γ i) → ℕ

  descW : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    → Gas → Closed Γ u → Path Γ u t → Id → Tick → Sched Γ → EvalSt e → ℕ
  -- THE SLOT HEAD, WHICH USED TO BE A LEAF AND STOPPED BEING ONE WHEN
  -- ITS STATEMENT DID.  A shared slot's connect re-enters the walk on
  -- the DEFINITION, so the widest burst under this subscribe is not
  -- the one the slot hands back; a statement about the slot that calls
  -- an inductive hypothesis needs its child's width, and there is no
  -- projection to give it while this clause reads a leaf.  The split
  -- is by helper rather than by `with` for the reason the count is,
  -- one clause down.  It OVER-APPROXIMATES the two early exits of the
  -- join -- a spent share and a live one descend nowhere -- which is
  -- sound in a premise's direction and is why the helper does not
  -- read the state those exits branch on.
  descW g (input i) κ id now sched st =
    burstW g (input i) κ id now sched st
      ⊔ slotW g i κ id now sched st (Sched.slots sched i)
  descW g (mapᵉ f b) κ id now sched st =
    burstW g (mapᵉ f b) κ id now sched st
      ⊔ descW g b (map-f f ↠ κ) id now sched st
  -- THE COUNT IS SPLIT IN A HELPER RATHER THAN BY A `with`, and that is
  -- not a style choice: a `with` here abstracts `evalTm cnt` in this
  -- clause and NOT inside the `subscribeE` the burst term names, so the
  -- two branches stop being comparable and the head conjunct's own
  -- `refl` fails to typecheck.
  descW g (takeᵉ cnt b) κ id now sched st =
    burstW g (takeᵉ cnt b) κ id now sched st ⊔ child (evalTm cnt)
    where
    child : ℕ → ℕ
    child 0 = 0
    child (suc k) =
      descW g b (take-f (proj₁ (mintNode sched)) ↠ κ) id now
            (proj₂ (mintNode sched))
            (installNode (proj₁ (mintNode sched)) (take-st (suc k)) st)
  descW g (scanᵉ f z b) κ id now sched st =
    burstW g (scanᵉ f z b) κ id now sched st
      ⊔ descW g b (scan-f f (proj₁ (mintNode sched)) ↠ κ) id now
          (proj₂ (mintNode sched))
          (installNode (proj₁ (mintNode sched)) (scan-st (evalTm z)) st)
  descW {u = u} g (mergeAllᵉ lim b) κ id now sched st =
    burstW g (mergeAllᵉ lim b) κ id now sched st
      ⊔ descW g b (thru-outer mergeAllᵒ (proj₁ (mintNode sched)) ↠ κ) id now
          (proj₂ (mintNode sched))
          (installNode (proj₁ (mintNode sched))
                       (mergeAll-st {t = u} lim 0 [] false) st)
  descW g (switchAllᵉ b) κ id now sched st =
    burstW g (switchAllᵉ b) κ id now sched st
      ⊔ descW g b (thru-outer switchᵒ (proj₁ (mintNode sched)) ↠ κ) id now
          (proj₂ (mintNode sched))
          (installNode (proj₁ (mintNode sched)) (switch-st nothing false) st)
  descW g (exhaustAllᵉ b) κ id now sched st =
    burstW g (exhaustAllᵉ b) κ id now sched st
      ⊔ descW g b (thru-outer exhaustᵒ (proj₁ (mintNode sched)) ↠ κ) id now
          (proj₂ (mintNode sched))
          (installNode (proj₁ (mintNode sched)) (exhaust-st false false) st)
  descW g0 (μᵉ body) κ id now sched st = burstW g0 (μᵉ body) κ id now sched st
  descW (gs fuel) (μᵉ body) κ id now sched st =
    burstW (gs fuel) (μᵉ body) κ id now sched st
      ⊔ descW fuel (unfoldμ body) κ id now sched st
  descW g o κ id now sched st = burstW g o κ id now sched st

  slotW g i κ id now sched st (scripted _) = 0
  slotW g i κ id now sched st (shared d)   = connW g i d κ id now sched st

  connW g0 i d κ id now sched st = 0
  connW (gs fuel) i d κ id now sched st =
    descW fuel d (share-sink i) id now sched
      (register (toℕ i) κ
        (record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st }))

  -- THE CONNECT'S OWN DESCENT, named for the reason `innerW` is: the
  -- fuel the definition is walked at is the PEELED one, so an inlined
  -- term would name a subscribe the out-of-gas arm never makes.  The
  -- state it descends from is the one the connect registers into,
  -- because a measure that read the caller's state would be about a
  -- different run.
  -- AND THE SAME QUESTION ONE LEVEL UP, at the inner subscription a
  -- drain performs.  It is a definition rather than the descent term
  -- written out because the fuel the descent runs at is the PEELED one,
  -- so an inlined premise would name a subscribe the out-of-gas clause
  -- never makes.
  innerW : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    → Gas → AllOp → NodeId → Path Γ s t → Id → Tick → Closed Γ s
    → Sched Γ → EvalSt e → ℕ
  innerW g0 op allNid κ id now o sched st = 0
  innerW (gs fuel) op allNid κ id now o sched st =
    descW fuel o (from-inner op allNid (Sched.nextNode sched) ↠ κ) id now
          (record sched { nextNode = suc (Sched.nextNode sched) }) st

  innerW-gs : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (fuel : Gas) (op : AllOp) (allNid : NodeId) (κ : Path Γ s t) (id : Id)
    (now : Tick) (o : Closed Γ s) (sched : Sched Γ) (st : EvalSt e) →
    descW fuel o (from-inner op allNid (Sched.nextNode sched) ↠ κ) id now
          (record sched { nextNode = suc (Sched.nextNode sched) }) st
      ≤ innerW (gs fuel) op allNid κ id now o sched st
  innerW-gs fuel op allNid κ id now o sched st = ≤-refl

  -- AND THE SAME READING FROM ABOVE, AT BOTH CLAUSES.  The projection
  -- directly above hands a consumer the descent as a LOWER bound,
  -- which is what a statement SPENDING the measure needs; a statement
  -- BOUNDING it needs the other direction, and the seal makes neither
  -- half derivable from the other.  Exporting the equation rather than
  -- the `≥` keeps the elimination on the consumer's side, as the
  -- descent's own equations below already do.  The clauses are the
  -- seal's whole content at this name, so both bodies are `refl`.
  innerW-g0-eq : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (op : AllOp) (allNid : NodeId) (κ : Path Γ s t) (id : Id)
    (now : Tick) (o : Closed Γ s) (sched : Sched Γ) (st : EvalSt e) →
    innerW g0 op allNid κ id now o sched st ≡ 0
  innerW-g0-eq op allNid κ id now o sched st = refl

  innerW-gs-eq : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (fuel : Gas) (op : AllOp) (allNid : NodeId) (κ : Path Γ s t) (id : Id)
    (now : Tick) (o : Closed Γ s) (sched : Sched Γ) (st : EvalSt e) →
    innerW (gs fuel) op allNid κ id now o sched st
      ≡ descW fuel o (from-inner op allNid (Sched.nextNode sched) ↠ κ) id now
              (record sched { nextNode = suc (Sched.nextNode sched) }) st
  innerW-gs-eq fuel op allNid κ id now o sched st = refl

  -- AND THE CHILD'S HALF AT THE SUBSTITUTING HEAD.  The clause already
  -- names the child's descent as one side of its own join, so the fact
  -- is a projection -- but the family is SEALED, so a consumer outside
  -- this module cannot see that and needs the equation exported.
  descW-map : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (g : Gas) (f : Fn Γ [] [] [] s u) (b : Closed Γ s) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    descW g b (map-f f ↠ κ) id now sched st
      ≤ descW g (mapᵉ f b) κ id now sched st
  descW-map g f b κ id now sched st = m≤n⊔m _ _

  -- AND THE FOLD'S HALF, which is `descW-map`'s shape at a head that
  -- mints a node: the child is read under the fresh node's path and the
  -- initial accumulator's install, so a consumer that has widened the
  -- parent's width still has to name the same state the clause does.
  descW-scan : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (g : Gas) (f : Fn Γ [] [] [] (u ×ᵗ s) u) (z : Tm Γ [] [] [] u)
    (b : Closed Γ s) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    descW g b (scan-f f (proj₁ (mintNode sched)) ↠ κ) id now
          (proj₂ (mintNode sched))
          (installNode (proj₁ (mintNode sched)) (scan-st (evalTm z)) st)
      ≤ descW g (scanᵉ f z b) κ id now sched st
  descW-scan g f z b κ id now sched st = m≤n⊔m _ _

  -- AND THE UNFOLDING'S HALF AT THE μ HEAD, which is the one place the
  -- child is not a subterm.  That is exactly why the width premise is
  -- this family and not a syntactic reading: `descW` prices the
  -- unfolding by construction, naming the unfolded body's own descent
  -- as one side of the join, so the recursive call's premise is a
  -- projection where a syntactic width would need a transfer that is
  -- refuted.
  descW-mu : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (fuel : Gas) (body : Exp Γ (u ∷ []) [] [] u) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    descW fuel (unfoldμ body) κ id now sched st
      ≤ descW (gs fuel) (μᵉ body) κ id now sched st
  descW-mu fuel body κ id now sched st = m≤n⊔m _ _

  -- AND THE CHILD'S HALF AT THE FILTER HEAD, under the count the source
  -- evaluates to.  The hypothesis is what lets this be stated at all:
  -- `descW`'s own take clause splits on that count, so the equation has
  -- to be in hand before the two sides are comparable.
  descW-take : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (cnt : Tm Γ [] [] [] natᵗ) (b : Closed Γ u) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e)
    (k : ℕ) → evalTm cnt ≡ suc k →
    descW g b (take-f (proj₁ (mintNode sched)) ↠ κ) id now
          (proj₂ (mintNode sched))
          (installNode (proj₁ (mintNode sched)) (take-st (suc k)) st)
      ≤ descW g (takeᵉ cnt b) κ id now sched st
  descW-take g cnt b κ id now sched st k h with evalTm cnt | h
  ... | .(suc k) | refl = m≤n⊔m _ _

  -- AND THE CHILD'S HALF AT THE THREE `*All` HEADS, each the projection
  -- of the head clause's own join at the child's freshly minted node and
  -- installed initial state.  Exported for the reason `descW-map` is:
  -- the family is SEALED, so the clause's shape is invisible outside.
  descW-merge : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (lim : Maybe ℕ) (b : Closed Γ (obs u)) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    descW g b (thru-outer mergeAllᵒ (proj₁ (mintNode sched)) ↠ κ) id now
          (proj₂ (mintNode sched))
          (installNode (proj₁ (mintNode sched))
                       (mergeAll-st {t = u} lim 0 [] false) st)
      ≤ descW g (mergeAllᵉ lim b) κ id now sched st
  descW-merge g lim b κ id now sched st = m≤n⊔m _ _

  descW-switch : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (b : Closed Γ (obs u)) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    descW g b (thru-outer switchᵒ (proj₁ (mintNode sched)) ↠ κ) id now
          (proj₂ (mintNode sched))
          (installNode (proj₁ (mintNode sched)) (switch-st nothing false) st)
      ≤ descW g (switchAllᵉ b) κ id now sched st
  descW-switch g b κ id now sched st = m≤n⊔m _ _

  descW-exhaust : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (b : Closed Γ (obs u)) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    descW g b (thru-outer exhaustᵒ (proj₁ (mintNode sched)) ↠ κ) id now
          (proj₂ (mintNode sched))
          (installNode (proj₁ (mintNode sched)) (exhaust-st false false) st)
      ≤ descW g (exhaustAllᵉ b) κ id now sched st
  descW-exhaust g b κ id now sched st = m≤n⊔m _ _

  -- AND THE CONNECT'S HALF AT THE SLOT HEAD, which is the projection the
  -- slot clause was split for.  A consumer holds the slots equation and
  -- needs the two readings of the join's right side to be the same term
  -- applied to the two sides of it -- which is available exactly because
  -- the split is a named function of the slot rather than a `with`.
  -- AND THE PEELED FUEL'S HALF UNDER THE CONNECT, which is the same
  -- shape `innerW-gs` has and is exported for the same reason: the
  -- family is sealed, so a consumer cannot see that the recursive call
  -- it needs a width for is the one this measure already names.
  connW-gs : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (fuel : Gas) (i : Fin n) (d : Closed Γ (lookup Γ i))
    (κ : Path Γ (lookup Γ i) t) (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) →
    descW fuel d (share-sink i) id now sched
      (register (toℕ i) κ
        (record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st }))
      ≤ connW (gs fuel) i d κ id now sched st
  connW-gs fuel i d κ id now sched st = ≤-refl

  descW-conn : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (g : Gas) (i : Fin n) (d : Closed Γ (lookup Γ i))
    {ok : T (inputsBelowᵉ (toℕ i) d)}
    (κ : Path Γ (lookup Γ i) t) (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched i ≡ shared d {ok = ok} →
    connW g i d κ id now sched st ≤ descW g (input i) κ id now sched st
  descW-conn g i d κ id now sched st eqs =
    ≤-trans (≤-reflexive (sym (cong (slotW g i κ id now sched st) eqs)))
            (m≤n⊔m _ _)

  -- AND THE WHOLE DRAIN'S WORTH, one `⊔` per queued inner at the state
  -- that inner is actually subscribed at.  It is a SEPARATE measure
  -- rather than a conjunct bolted onto the drain's caps predicate for
  -- the reason the walk face already keeps its caps bundle apart from
  -- its burst bundle: the two travel together but say different things,
  -- and a predicate carrying both has to be taken apart at every site
  -- that wants either.
  drainW : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (sf : Gas) (allNid : NodeId) (κ : Path Γ s t) (id : Id) (now : Tick)
    (q : List (Closed Γ s)) (sched : Sched Γ) (st : EvalSt e) → ℕ
  drainW sf allNid κ id now [] sched st = 0
  drainW sf allNid κ id now (o ∷ q) sched st =
    innerW sf mergeAllᵒ allNid κ id now o sched st
      ⊔ drainW sf allNid κ id now q
          (proj₁ (proj₂ (proj₂ (proj₂ (proj₂
             (subscribeInner sf mergeAllᵒ allNid κ id now o sched st))))))
          (proj₂ (proj₂ (proj₂ (proj₂ (proj₂
             (subscribeInner sf mergeAllᵒ allNid κ id now o sched st))))))

  drainW-here : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (sf : Gas) (allNid : NodeId) (κ : Path Γ s t) (id : Id) (now : Tick)
    (o : Closed Γ s) (q : List (Closed Γ s)) (sched : Sched Γ) (st : EvalSt e) →
    innerW sf mergeAllᵒ allNid κ id now o sched st
      ≤ drainW sf allNid κ id now (o ∷ q) sched st
  drainW-here sf allNid κ id now o q sched st = m≤m⊔n _ _

  drainW-tail : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (sf : Gas) (allNid : NodeId) (κ : Path Γ s t) (id : Id) (now : Tick)
    (o : Closed Γ s) (q : List (Closed Γ s)) (sched : Sched Γ) (st : EvalSt e) →
    let r = subscribeInner sf mergeAllᵒ allNid κ id now o sched st in
    drainW sf allNid κ id now q
      (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r)))))
      (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r)))))
      ≤ drainW sf allNid κ id now (o ∷ q) sched st
  drainW-tail sf allNid κ id now o q sched st = m≤n⊔m _ _

  -- AND THE DRAIN'S OWN CLAUSES, for the reason the pair of projections
  -- directly above cannot serve: they hand a consumer either side of the
  -- join, which is what SPENDING the queue's measure needs, while a
  -- statement BOUNDING it has to discharge both sides at once and the
  -- seal makes neither equation derivable from the two `≤`s.  The
  -- clauses are the seal's whole content at this name, so both bodies
  -- are `refl`.
  drainW-nil-eq : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (sf : Gas) (allNid : NodeId) (κ : Path Γ s t) (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) →
    drainW sf allNid κ id now [] sched st ≡ 0
  drainW-nil-eq sf allNid κ id now sched st = refl

  drainW-cons-eq : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (sf : Gas) (allNid : NodeId) (κ : Path Γ s t) (id : Id) (now : Tick)
    (o : Closed Γ s) (q : List (Closed Γ s)) (sched : Sched Γ) (st : EvalSt e) →
    let r = subscribeInner sf mergeAllᵒ allNid κ id now o sched st in
    drainW sf allNid κ id now (o ∷ q) sched st
      ≡ innerW sf mergeAllᵒ allNid κ id now o sched st
          ⊔ drainW sf allNid κ id now q
              (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r)))))
              (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r)))))
  drainW-cons-eq sf allNid κ id now o q sched st = refl

  -- AND THE JOIN ITSELF AT EVERY HEAD, which is what a proof ABOUT the
  -- whole descent needs and the projections above deliberately do not
  -- give.  A projection hands a consumer one side; an induction has to
  -- discharge BOTH, so it needs the equation rather than either half.
  -- Exporting the equation rather than a `⊔-lub` wrapper keeps the
  -- elimination on the consumer's side, where the two bounds are
  -- already in hand and the shape of the join is the only thing
  -- missing.  The clauses are the seal's whole content at these heads,
  -- so every body here is `refl`.
  descW-map-eq : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (g : Gas) (f : Fn Γ [] [] [] s u) (b : Closed Γ s) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    descW g (mapᵉ f b) κ id now sched st
      ≡ burstW g (mapᵉ f b) κ id now sched st
          ⊔ descW g b (map-f f ↠ κ) id now sched st
  descW-map-eq g f b κ id now sched st = refl

  descW-scan-eq : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (g : Gas) (f : Fn Γ [] [] [] (u ×ᵗ s) u) (z : Tm Γ [] [] [] u)
    (b : Closed Γ s) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    descW g (scanᵉ f z b) κ id now sched st
      ≡ burstW g (scanᵉ f z b) κ id now sched st
          ⊔ descW g b (scan-f f (proj₁ (mintNode sched)) ↠ κ) id now
              (proj₂ (mintNode sched))
              (installNode (proj₁ (mintNode sched)) (scan-st (evalTm z)) st)
  descW-scan-eq g f z b κ id now sched st = refl

  descW-merge-eq : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (lim : Maybe ℕ) (b : Closed Γ (obs u)) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    descW g (mergeAllᵉ lim b) κ id now sched st
      ≡ burstW g (mergeAllᵉ lim b) κ id now sched st
          ⊔ descW g b (thru-outer mergeAllᵒ (proj₁ (mintNode sched)) ↠ κ) id now
              (proj₂ (mintNode sched))
              (installNode (proj₁ (mintNode sched))
                           (mergeAll-st {t = u} lim 0 [] false) st)
  descW-merge-eq g lim b κ id now sched st = refl

  descW-switch-eq : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (b : Closed Γ (obs u)) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    descW g (switchAllᵉ b) κ id now sched st
      ≡ burstW g (switchAllᵉ b) κ id now sched st
          ⊔ descW g b (thru-outer switchᵒ (proj₁ (mintNode sched)) ↠ κ) id now
              (proj₂ (mintNode sched))
              (installNode (proj₁ (mintNode sched)) (switch-st nothing false) st)
  descW-switch-eq g b κ id now sched st = refl

  descW-exhaust-eq : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (b : Closed Γ (obs u)) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    descW g (exhaustAllᵉ b) κ id now sched st
      ≡ burstW g (exhaustAllᵉ b) κ id now sched st
          ⊔ descW g b (thru-outer exhaustᵒ (proj₁ (mintNode sched)) ↠ κ) id now
              (proj₂ (mintNode sched))
              (installNode (proj₁ (mintNode sched)) (exhaust-st false false) st)
  descW-exhaust-eq g b κ id now sched st = refl

  descW-mu-eq : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (fuel : Gas) (body : Exp Γ (u ∷ []) [] [] u) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    descW (gs fuel) (μᵉ body) κ id now sched st
      ≡ burstW (gs fuel) (μᵉ body) κ id now sched st
          ⊔ descW fuel (unfoldμ body) κ id now sched st
  descW-mu-eq fuel body κ id now sched st = refl

  descW-mu0-eq : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (body : Exp Γ (u ∷ []) [] [] u) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    descW g0 (μᵉ body) κ id now sched st ≡ burstW g0 (μᵉ body) κ id now sched st
  descW-mu0-eq body κ id now sched st = refl

  -- AND THE FILTER HEAD IN BOTH DIRECTIONS OF ITS OWN SPLIT.  The count
  -- is evaluated inside the clause, so neither reading is available
  -- until it is in hand -- which is why this is two statements and not
  -- one, and why each carries the equation as a hypothesis.
  descW-take0-eq : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (cnt : Tm Γ [] [] [] natᵗ) (b : Closed Γ u) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    evalTm cnt ≡ 0 →
    descW g (takeᵉ cnt b) κ id now sched st
      ≡ burstW g (takeᵉ cnt b) κ id now sched st
  descW-take0-eq g cnt b κ id now sched st h with evalTm cnt | h
  ... | .0 | refl = ⊔-identityʳ _

  descW-takeS-eq : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (cnt : Tm Γ [] [] [] natᵗ) (b : Closed Γ u) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e)
    (k : ℕ) → evalTm cnt ≡ suc k →
    descW g (takeᵉ cnt b) κ id now sched st
      ≡ burstW g (takeᵉ cnt b) κ id now sched st
          ⊔ descW g b (take-f (proj₁ (mintNode sched)) ↠ κ) id now
              (proj₂ (mintNode sched))
              (installNode (proj₁ (mintNode sched)) (take-st (suc k)) st)
  descW-takeS-eq g cnt b κ id now sched st k h with evalTm cnt | h
  ... | .(suc k) | refl = refl

  descW-input-eq : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (g : Gas) (i : Fin n) (κ : Path Γ (lookup Γ i) t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    descW g (input i) κ id now sched st
      ≡ burstW g (input i) κ id now sched st
          ⊔ slotW g i κ id now sched st (Sched.slots sched i)
  descW-input-eq g i κ id now sched st = refl

  slotW-scripted-eq : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (g : Gas) (i : Fin n) (κ : Path Γ (lookup Γ i) t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e)
    {ok : T (isData (lookup Γ i))} (v : ObservableInput (Val Γ (lookup Γ i))) →
    slotW g i κ id now sched st (scripted {ok = ok} v) ≡ 0
  slotW-scripted-eq g i κ id now sched st v = refl

  slotW-shared-eq : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (g : Gas) (i : Fin n) (κ : Path Γ (lookup Γ i) t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e)
    (d : Closed Γ (lookup Γ i)) {ok : T (inputsBelowᵉ (toℕ i) d)} →
    slotW g i κ id now sched st (shared d {ok = ok})
      ≡ connW g i d κ id now sched st
  slotW-shared-eq g i κ id now sched st d = refl

  connW-g0-eq : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (i : Fin n) (d : Closed Γ (lookup Γ i)) (κ : Path Γ (lookup Γ i) t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    connW g0 i d κ id now sched st ≡ 0
  connW-g0-eq i d κ id now sched st = refl

  connW-gs-eq : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (fuel : Gas) (i : Fin n) (d : Closed Γ (lookup Γ i))
    (κ : Path Γ (lookup Γ i) t) (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) →
    connW (gs fuel) i d κ id now sched st
      ≡ descW fuel d (share-sink i) id now sched
          (register (toℕ i) κ
            (record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st }))
  connW-gs-eq fuel i d κ id now sched st = refl

  -- AND THE THREE HEADS THE DESCENT DOES NOT ENTER, where the join has
  -- one side and the equation says so.  A defer is one of them, and
  -- that is the whole reason a ceiling that stops at a defer can bound
  -- this family at all.
  descW-of-eq : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (ts : List (Tm Γ [] [] [] u)) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    descW g (ofᵉ ts) κ id now sched st ≡ burstW g (ofᵉ ts) κ id now sched st
  descW-of-eq g ts κ id now sched st = refl

  descW-empty-eq : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    descW g emptyᵉ κ id now sched st ≡ burstW g emptyᵉ κ id now sched st
  descW-empty-eq g κ id now sched st = refl

  descW-defer-eq : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (b : Exp Γ [] [] [] u) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    descW g (deferᵉ b) κ id now sched st
      ≡ burstW g (deferᵉ b) κ id now sched st
  descW-defer-eq g b κ id now sched st = refl
