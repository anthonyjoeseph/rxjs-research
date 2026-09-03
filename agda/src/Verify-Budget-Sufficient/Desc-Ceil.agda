------------------------------------------------------------------
-- THE DESCENT IS UNDER THE BURST CEILING, at every subterm the walk
-- reaches and at every fuel it reaches it with.
--
-- `descW` is the widest burst any ONE subscribe frame under this
-- subscribe hands back, and it is a semantic reading: it runs the
-- evaluator.  `bCeilᵉ` is syntax.  The induction below is the whole
-- bridge between them, and it is structured exactly as `descW` is --
-- lexicographic on the fuel and then the term, since the two clauses
-- that leave the subterm order are the two that spend fuel.
--
-- AND IT IS MET BY THE BURST CEILING, NOT THE JOINED ONE, which is the
-- part that had to be found rather than written.  The joined ceiling
-- descends into defers and reads every measure at every node; a
-- subscribe frame does neither, and the gap is not slack -- it is
-- fatal at the μ head, where `descW` descends into the UNFOLDING while
-- a ceiling reads the body.  `bCeilᵉ` cuts at the defer exactly as the
-- descent does: a μ's variable is reachable only from under a defer,
-- so a ceiling that stops there cannot see the plug.  It is still
-- under the joined reading node for node, so the caps base goes on
-- paying.
--
-- WHAT IS LEFT AS A LEAF IS THE ONE FRAME, and that is the design.
-- Every clause here is bookkeeping over the join `descW` already is;
-- the only thing this proof cannot see is how many payloads one
-- subscribe emits, which is `burst-out` and is semantic to its core.
-- REFUTED: `Refuted.Ceil-Unfold-Mu` -- the joined ceiling is NOT
--   monotone across an unfold, and not by a constant either: the plug
--   lands once per occurrence, so k mentions of the μ-var read k copies
--   of the μ's own width against a ceiling that counted the var at
--   zero.  Eighteen against six at three mentions, twelve at two.
------------------------------------------------------------------
module Verify-Budget-Sufficient.Desc-Ceil where

open import Data.Bool using (false)
open import Data.List using ([]; _∷_; length)
open import Data.Maybe using (nothing)
open import Data.Nat using (zero; suc; _≤_; _⊔_; z≤n)
open import Data.Nat.Properties
  using (≤-trans; ≤-reflexive; ⊔-lub; ⊔-monoˡ-≤; m≤m⊔n; m≤n⊔m)
open import Data.Fin using (Fin; toℕ)
open import Data.Vec using (lookup)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; sym; trans; cong; subst)

open import Rx.Prim using (Tick; Id; Gas; g0; gs)
open import Rx.Exp using
  (Ctx; Closed; Val; input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ;
  varᵉ; deferᵉ; unfoldμ; evalTm)
open import Rx.Slots using (Slots; scripted; shared)
open import Rx.Frame-Width using (outWⱽ)
open import Rx.Burst-Ceil using
  (bCeilᵉ; slotsBCeil; slotBCeil; slotsB-lb; outW≤bCeil;
   bCeil-map; bCeil-take; bCeil-scan; bCeil-merge; bCeil-switch;
   bCeil-exhaust)
open import Rx.Width-Subst using (bCeil-unfoldμ)
open import Rx.Evaluator using
  (Sched; EvalSt; Path; _↠_; map-f; scan-f; take-f; thru-outer;
   mergeAllᵒ; switchᵒ; exhaustᵒ; scan-st; take-st; mergeAll-st;
   switch-st; exhaust-st; mintNode; installNode; share-sink; register;
   subscribeE; splitBurst)

open import Verify-Budget-Sufficient.Nest-Burst using
  (burstW; burstW-eq; descW; slotW; descW-map-eq; descW-scan-eq; descW-merge-eq; descW-switch-eq;
  descW-exhaust-eq; descW-mu-eq; descW-mu0-eq; descW-take0-eq; descW-takeS-eq; descW-input-eq;
  slotW-scripted-eq; slotW-shared-eq; connW-g0-eq; connW-gs-eq; descW-of-eq; descW-empty-eq;
  descW-defer-eq)

-- THE ONE FRAME'S OWN PAYLOAD COUNT, which is the only semantic step
-- in this module.  `burstW` splits a real subscribe's emission stream
-- and counts the first burst; `outWⱽ` counts the payloads the term can
-- syntactically carry, descending a share on the slot fuel exactly as
-- the evaluator's connect does.  The slots equation is what ties the
-- two descents together, and it is the hypothesis every consumer of
-- this face already holds.
-- AND THE LEAF IS STATED OVER THE SPLIT AND NOT OVER THE MEASURE'S
-- NAME, which is what makes it instantiable at all.  `burstW` is
-- SEALED, so a statement carrying it on the SMALL side of a `≤`
-- reduces at no point whatever and no row can be written against it --
-- a claim nothing can instantiate is a claim nothing can refute, and
-- that is a property of the statement rather than of the evidence
-- against it.  The seal exists to keep the evaluator out of the
-- PREMISES that name the measure, and it goes on doing that: the
-- equation is spent once, here, in a body.
-- PROBED: `Probed.Burst-OutW` -- nine rows at the root frame, three of
--   them EQUALITIES and so load-bearing: `ofᵉ` at three, and the two
--   `*All` heads at six, which is where the reading is a product and
--   the only place it could be under-counted.  The defer reads zero
--   against zero, which is the row the ceiling's right to stop there
--   rests on.  TIED at the three equality rows, which are the ones a
--   tie can be load-bearing on at all.  NOT covered: a frame below the
--   root, a scan head, and a shared slot whose definition itself
--   reaches a share.
postulate
  burst-out : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (sl : Slots Γ) (o : Closed Γ u) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl →
    length (proj₁ (splitBurst {A = Val Γ t}
      (proj₁ (subscribeE g o κ id now sched st))))
      ≤ outWⱽ n [] sl o

burst-outW : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (g : Gas) (sl : Slots Γ) (o : Closed Γ u) (κ : Path Γ u t)
  (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  burstW g o κ id now sched st ≤ outWⱽ n [] sl o
burst-outW {n = n} g sl o κ id now sched st eqs =
  subst (_≤ outWⱽ n [] sl o)
        (sym (burstW-eq g o κ id now sched st))
        (burst-out g sl o κ id now sched st eqs)

burst-ceil : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (g : Gas) (sl : Slots Γ) (o : Closed Γ u) (κ : Path Γ u t)
  (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  burstW g o κ id now sched st ≤ bCeilᵉ n sl o ⊔ slotsBCeil n sl
burst-ceil {n = n} g sl o κ id now sched st eqs =
  ≤-trans (burst-outW g sl o κ id now sched st eqs)
          (≤-trans (outW≤bCeil n sl o)
                   (m≤m⊔n (bCeilᵉ n sl o) (slotsBCeil n sl)))

descW-ceil : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (g : Gas) (sl : Slots Γ) (o : Closed Γ u) (κ : Path Γ u t)
  (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  descW g o κ id now sched st ≤ bCeilᵉ n sl o ⊔ slotsBCeil n sl

-- THE SLOT HEAD, SPLIT ON THE SLOT AND NOT ON THE SCHEDULE'S READING
-- OF IT.  A scripted slot descends nowhere; a shared one re-enters the
-- walk on the definition, and the ceiling that pays for it is the
-- SLOTS collector rather than anything under this term -- which is why
-- the statement carries that collector at all.
slot-ceil : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (g : Gas) (sl : Slots Γ) (i : Fin n) (κ : Path Γ (lookup Γ i) t)
  (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  slotW g i κ id now sched st (Sched.slots sched i)
    ≤ bCeilᵉ n sl (input {Δᵍ = []} {Δ = []} {Θ = []} i) ⊔ slotsBCeil n sl
slot-ceil {n = n} g sl i κ id now sched st eqs with sl i in eqi
... | scripted v =
  subst (λ s → slotW g i κ id now sched st s ≤ _) (sym eqsi)
        (≤-trans (≤-reflexive (slotW-scripted-eq g i κ id now sched st v))
                 z≤n)
  where
  eqsi : Sched.slots sched i ≡ scripted v
  eqsi = trans (cong (λ f → f i) eqs) eqi
... | shared d =
  subst (λ s → slotW g i κ id now sched st s ≤ _) (sym eqsi) (conn g)
  where
  eqsi : Sched.slots sched i ≡ shared d
  eqsi = trans (cong (λ f → f i) eqs) eqi

  slots≤ : bCeilᵉ n sl d ≤ slotsBCeil n sl
  slots≤ = ≤-trans (≤-reflexive (sym (cong (slotBCeil n sl) eqi)))
                   (slotsB-lb n sl i)

  conn : ∀ (g′ : Gas) → slotW g′ i κ id now sched st (shared d)
           ≤ bCeilᵉ n sl (input {Δᵍ = []} {Δ = []} {Θ = []} i)
               ⊔ slotsBCeil n sl
  conn g0 =
    ≤-trans (≤-reflexive
              (trans (slotW-shared-eq g0 i κ id now sched st d)
                     (connW-g0-eq i d κ id now sched st)))
            z≤n
  conn (gs fuel) =
    ≤-trans (≤-reflexive
              (trans (slotW-shared-eq (gs fuel) i κ id now sched st d)
                     (connW-gs-eq fuel i d κ id now sched st)))
            (≤-trans (descW-ceil fuel sl d (share-sink i) id now sched
                        (register (toℕ i) κ
                          (record st { connectedShares =
                             toℕ i ∷ EvalSt.connectedShares st }))
                        eqs)
                     (≤-trans (⊔-lub slots≤ (m≤n⊔m _ _)) (m≤n⊔m _ _)))

descW-ceil g sl (input i) κ id now sched st eqs =
  ≤-trans (≤-reflexive (descW-input-eq g i κ id now sched st))
          (⊔-lub (burst-ceil g sl (input i) κ id now sched st eqs)
                 (slot-ceil g sl i κ id now sched st eqs))
descW-ceil g sl (ofᵉ ts) κ id now sched st eqs =
  ≤-trans (≤-reflexive (descW-of-eq g ts κ id now sched st))
          (burst-ceil g sl (ofᵉ ts) κ id now sched st eqs)
descW-ceil g sl emptyᵉ κ id now sched st eqs =
  ≤-trans (≤-reflexive (descW-empty-eq g κ id now sched st))
          (burst-ceil g sl emptyᵉ κ id now sched st eqs)
descW-ceil {n = n} g sl (mapᵉ f b) κ id now sched st eqs =
  ≤-trans (≤-reflexive (descW-map-eq g f b κ id now sched st))
          (⊔-lub (burst-ceil g sl (mapᵉ f b) κ id now sched st eqs)
                 (≤-trans (descW-ceil g sl b (map-f f ↠ κ) id now sched st eqs)
                          (⊔-monoˡ-≤ (slotsBCeil n sl) (bCeil-map n sl f b))))
descW-ceil {n = n} g sl (takeᵉ c b) κ id now sched st eqs with evalTm c in h
... | zero =
  ≤-trans (≤-reflexive (descW-take0-eq g c b κ id now sched st h))
          (burst-ceil g sl (takeᵉ c b) κ id now sched st eqs)
... | suc k =
  ≤-trans (≤-reflexive (descW-takeS-eq g c b κ id now sched st k h))
          (⊔-lub (burst-ceil g sl (takeᵉ c b) κ id now sched st eqs)
                 (≤-trans (descW-ceil g sl b (take-f (proj₁ (mintNode sched)) ↠ κ)
                             id now (proj₂ (mintNode sched))
                             (installNode (proj₁ (mintNode sched))
                                          (take-st (suc k)) st) eqs)
                          (⊔-monoˡ-≤ (slotsBCeil n sl) (bCeil-take n sl c b))))
descW-ceil {n = n} g sl (scanᵉ f z b) κ id now sched st eqs =
  ≤-trans (≤-reflexive (descW-scan-eq g f z b κ id now sched st))
          (⊔-lub (burst-ceil g sl (scanᵉ f z b) κ id now sched st eqs)
                 (≤-trans (descW-ceil g sl b (scan-f f (proj₁ (mintNode sched)) ↠ κ)
                             id now (proj₂ (mintNode sched))
                             (installNode (proj₁ (mintNode sched))
                                          (scan-st (evalTm z)) st) eqs)
                          (⊔-monoˡ-≤ (slotsBCeil n sl) (bCeil-scan n sl f z b))))
descW-ceil {n = n} {u = u} g sl (mergeAllᵉ lim b) κ id now sched st eqs =
  ≤-trans (≤-reflexive (descW-merge-eq g lim b κ id now sched st))
          (⊔-lub (burst-ceil g sl (mergeAllᵉ lim b) κ id now sched st eqs)
                 (≤-trans (descW-ceil g sl b
                             (thru-outer mergeAllᵒ (proj₁ (mintNode sched)) ↠ κ)
                             id now (proj₂ (mintNode sched))
                             (installNode (proj₁ (mintNode sched))
                                          (mergeAll-st {t = u} lim 0 [] false) st)
                             eqs)
                          (⊔-monoˡ-≤ (slotsBCeil n sl) (bCeil-merge n sl lim b))))
descW-ceil {n = n} g sl (switchAllᵉ b) κ id now sched st eqs =
  ≤-trans (≤-reflexive (descW-switch-eq g b κ id now sched st))
          (⊔-lub (burst-ceil g sl (switchAllᵉ b) κ id now sched st eqs)
                 (≤-trans (descW-ceil g sl b
                             (thru-outer switchᵒ (proj₁ (mintNode sched)) ↠ κ)
                             id now (proj₂ (mintNode sched))
                             (installNode (proj₁ (mintNode sched))
                                          (switch-st nothing false) st) eqs)
                          (⊔-monoˡ-≤ (slotsBCeil n sl) (bCeil-switch n sl b))))
descW-ceil {n = n} g sl (exhaustAllᵉ b) κ id now sched st eqs =
  ≤-trans (≤-reflexive (descW-exhaust-eq g b κ id now sched st))
          (⊔-lub (burst-ceil g sl (exhaustAllᵉ b) κ id now sched st eqs)
                 (≤-trans (descW-ceil g sl b
                             (thru-outer exhaustᵒ (proj₁ (mintNode sched)) ↠ κ)
                             id now (proj₂ (mintNode sched))
                             (installNode (proj₁ (mintNode sched))
                                          (exhaust-st false false) st) eqs)
                          (⊔-monoˡ-≤ (slotsBCeil n sl) (bCeil-exhaust n sl b))))
descW-ceil g0 sl (μᵉ body) κ id now sched st eqs =
  ≤-trans (≤-reflexive (descW-mu0-eq body κ id now sched st))
          (burst-ceil g0 sl (μᵉ body) κ id now sched st eqs)
descW-ceil {n = n} (gs fuel) sl (μᵉ body) κ id now sched st eqs =
  ≤-trans (≤-reflexive (descW-mu-eq fuel body κ id now sched st))
          (⊔-lub (burst-ceil (gs fuel) sl (μᵉ body) κ id now sched st eqs)
                 (≤-trans (descW-ceil fuel sl (unfoldμ body) κ id now sched st eqs)
                          (⊔-monoˡ-≤ (slotsBCeil n sl)
                            (≤-reflexive (bCeil-unfoldμ n sl body)))))
descW-ceil g sl (deferᵉ b) κ id now sched st eqs =
  ≤-trans (≤-reflexive (descW-defer-eq g b κ id now sched st))
          (burst-ceil g sl (deferᵉ b) κ id now sched st eqs)
descW-ceil g sl (varᵉ ()) κ id now sched st eqs
