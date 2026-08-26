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
open import Data.Bool using (false)
open import Data.Nat using (ℕ; suc; _⊔_; _≤_)
open import Data.Nat.Properties using (≤-refl; m≤m⊔n; m≤n⊔m)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Tick; Id; Gas; g0; gs)
open import Rx.Exp using
  (Ctx; Closed; Exp; Val; Fn; Tm; natᵗ; obs; unfoldμ; evalTm; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ; switchAllᵉ;
  exhaustAllᵉ; μᵉ)
open import Rx.Evaluator using
  (Sched; EvalSt; Path; _↠_; map-f; scan-f; take-f; thru-outer; from-inner; NodeId;
   mergeAllᵒ; switchᵒ; exhaustᵒ; scan-st; take-st; mergeAll-st; switch-st; exhaust-st;
   mintNode; installNode; subscribeE; subscribeInner; splitBurst)

abstract
  -- THE BURST ONE SUBSCRIBE HANDS BACK, named so the recursion below
  -- reads as `this one, and the child's`.
  burstW : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    → Gas → Closed Γ u → Path Γ u t → Id → Tick → Sched Γ → EvalSt e → ℕ
  burstW {Γ = Γ} {t = t} g o κ id now sched st =
    length (proj₁ (splitBurst {A = Val Γ t}
              (proj₁ (subscribeE g o κ id now sched st))))

  descW : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    → Gas → Closed Γ u → Path Γ u t → Id → Tick → Sched Γ → EvalSt e → ℕ
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

  -- AND THE SAME QUESTION ONE LEVEL UP, at the inner subscription a
  -- drain performs.  It is a definition rather than the descent term
  -- written out because the fuel the descent runs at is the PEELED one,
  -- so an inlined premise would name a subscribe the out-of-gas clause
  -- never makes.
  innerW : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    → Gas → NodeId → Path Γ s t → Id → Tick → Closed Γ s
    → Sched Γ → EvalSt e → ℕ
  innerW g0 allNid κ id now o sched st = 0
  innerW (gs fuel) allNid κ id now o sched st =
    descW fuel o (from-inner mergeAllᵒ allNid (Sched.nextNode sched) ↠ κ) id now
          (record sched { nextNode = suc (Sched.nextNode sched) }) st

  innerW-gs : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (fuel : Gas) (allNid : NodeId) (κ : Path Γ s t) (id : Id) (now : Tick)
    (o : Closed Γ s) (sched : Sched Γ) (st : EvalSt e) →
    descW fuel o (from-inner mergeAllᵒ allNid (Sched.nextNode sched) ↠ κ) id now
          (record sched { nextNode = suc (Sched.nextNode sched) }) st
      ≤ innerW (gs fuel) allNid κ id now o sched st
  innerW-gs fuel allNid κ id now o sched st = ≤-refl

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
    innerW sf allNid κ id now o sched st
      ⊔ drainW sf allNid κ id now q
          (proj₁ (proj₂ (proj₂ (proj₂ (proj₂
             (subscribeInner sf mergeAllᵒ allNid κ id now o sched st))))))
          (proj₂ (proj₂ (proj₂ (proj₂ (proj₂
             (subscribeInner sf mergeAllᵒ allNid κ id now o sched st))))))

  drainW-here : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (sf : Gas) (allNid : NodeId) (κ : Path Γ s t) (id : Id) (now : Tick)
    (o : Closed Γ s) (q : List (Closed Γ s)) (sched : Sched Γ) (st : EvalSt e) →
    innerW sf allNid κ id now o sched st
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
