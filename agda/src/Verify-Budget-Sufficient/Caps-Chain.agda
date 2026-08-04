------------------------------------------------------------------
-- THE COMPOSITION GATE: one lemma per clause SHAPE of the subscribe
-- clique, and the two conversions the OPERATOR COUNT needs.
--
-- Step C gives each member of the clique a conjunct bounding the level
-- it LEAVES.  The arithmetic that lands each clause's total inside its
-- transformer is proven here, ahead of the grind and against the
-- receipts as ABSTRACT NUMBERS under exactly the bound the ground
-- clauses hand back — so a clause proof applies one of these and does no
-- arithmetic of its own.  The shape is right precisely because the
-- clauses go through with the pieces they already have; an earlier draft
-- of the hierarchy admitted none of the four (it ran the frames before
-- the rest of the operator chain, it charged a payload's subscribe at J
-- rather than at `suc J`, and its eval receipt was linear where
-- `unfoldμ-caps` pays `m + suc (m * m)`).
--
-- EVERY ONE OF THEM HOLDS AT A FIXED DEPTH FUEL `d`.  One subscribe's
-- whole operator walk — its payloads, its nested subscribes, its
-- pushBurst frames — runs at the SAME d; the fuel is spent only by
-- `fIterD`'s step into `fLvlD S W d`, i.e. only when a frame re-reads
-- the budget at its own level.  So the steps below quantify d and never
-- touch it, exactly as they quantify S and W.
--
-- AND THE MEMBERS REPORT AT AN INDEX, not at the transformer their own
-- entry is priced by.  A fresh subscribe at level J on budget `suc k` is
-- priced by `sLvlD S W d (suc k) J`, an operator sweep long enough for a
-- whole chain; the gate's operator step consumes its SOURCE's receipt at
-- `opIterD S W d k m (suc j)` — the sweep with m operators LEFT — and m
-- descends by one per operator.  So the recursive call inside an
-- operator clause is not a fresh entry but the same sweep, one shorter,
-- and the conversion the grind would need in the other direction is
-- REFUTED (agda/probe/Chain-Index-Probe.agda § 1: it asks that a sweep
-- sized for a whole chain fit inside the operators the caller has
-- remaining, and at zero operators left the walk transformer is the
-- identity).  § 2 below is the pair that does hold: a callee reporting
-- at m feeds a caller holding `suc m` by monotonicity alone, and a
-- member entered FRESH instantiates the index at the size cap and
-- converts by the clause equation, at the same site that spends the
-- budget descent.
--
-- This module is not mutual with any of them — it consumes the `-mono`
-- and `-infl` families as finished facts — so it is its own compilation
-- unit and the clique imports it.  The transformers being abstract costs
-- one `≤-reflexive` per lemma: the goal's `suc`-argument has to be
-- opened by hand through the clause equation (`sIterD-suc`,
-- `opIterD-suc`) rather than by reduction.
------------------------------------------------------------------
module Verify-Budget-Sufficient.Caps-Chain where

open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-trans; ≤-refl; ≤-reflexive; +-suc; +-assoc; +-identityʳ; +-comm;
         +-mono-≤; +-monoʳ-≤; *-mono-≤; *-suc; n≤1+n;
         m≤m+n; m≤n+m; m≤m*n)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Rx.Evaluator
  using (sizeAt; widAt; fCharge;
         fLvlD; sIterD; sLvlD; opIterD; fIterD;
         fLvlD-suc; sIterD-suc; sLvlD-suc; opIterD-suc;
         fIterD-suc; fIterD-0; sIterD-0)
open import Verify-Budget-Sufficient.Caps
  using (widAt-mono;
         sLvlD-infl; opIterD-infl; fIterD-infl; sIterD-infl;
         sIterD-mono; sLvlD-mono; opIterD-mono; fIterD-mono)

------------------------------------------------------------------
-- § 1.  THE FIVE CLAUSE SHAPES.
------------------------------------------------------------------

-- ONE PAYLOAD of a thruWalk / concatDrain: the head subscribes an inner
-- under one more frame (`subscribeInner-caps` recurses at `suc j`), and
-- the tail is the walk's own IH at the level the head left
walk-step : ∀ (S W d k m j j₁ j₂ : ℕ) → 2 ≤ S →
  j + j₁ ≤ sLvlD S W d k (suc j) →
  (j + j₁) + j₂ ≤ sIterD S W d k m (j + j₁) →
  j + (j₁ + j₂) ≤ sIterD S W d k (suc m) j
walk-step S W d k m j j₁ j₂ 2≤S hd tl =
  ≤-trans (≤-trans (≤-trans (≤-reflexive (sym (+-assoc j j₁ j₂))) tl)
                   (sIterD-mono m m d d k k 2≤S ≤-refl ≤-refl hd ≤-refl ≤-refl ≤-refl))
          (≤-reflexive (sym (sIterD-suc S W d k m j)))

-- and an empty payload list leaves the level where it found it
walk-nil : ∀ (S W d k j : ℕ) → j + 0 ≤ sIterD S W d k 0 j
walk-nil S W d k j =
  ≤-trans (≤-reflexive (+-identityʳ j)) (≤-reflexive (sym (sIterD-0 S W d k j)))

-- a dry payload subscribe, which does not move the level either
inner-nil : ∀ (S W d k j : ℕ) → suc (j + 0) ≤ sLvlD S W d k (suc j)
inner-nil S W d k j =
  ≤-trans (≤-reflexive (cong suc (+-identityʳ j))) (sLvlD-infl S W d k (suc j))

-- and a leaf subscribe: no operator is entered, so the sweep is
-- inflationary and nothing else is owed
leaf-lvl : ∀ (S W d k m j : ℕ) → j + 0 ≤ opIterD S W d k m j
leaf-lvl S W d k m j =
  ≤-trans (≤-reflexive (+-identityʳ j)) (opIterD-infl S W d k m j)

-- ONE EMIT of a pushBurst, and it is the fIterD twin of `walk-step`:
-- the emit is stepped through the ONE frame just built (`stepFrame-caps`,
-- which reports the level that frame LEAVES) and the rest of the burst
-- runs from there.  The gate had no fIterD row at all — .Caps-Face's pass
-- memo (~6090) names both this and `burst-index` below as what the
-- signature pass would need, and `pushBurst-caps` is the head that needs
-- them: it recurses on `em ∷ ems`, so its index is the EMIT COUNT
burst-step : ∀ (S W d k m j j₁ j₂ : ℕ) → 2 ≤ S →
  j + j₁ ≤ fLvlD S W d j →
  (j + j₁) + j₂ ≤ fIterD S W d k m (j + j₁) →
  j + (j₁ + j₂) ≤ fIterD S W d k (suc m) j
burst-step S W d k m j j₁ j₂ 2≤S hd tl =
  ≤-trans (≤-trans (≤-trans (≤-reflexive (sym (+-assoc j j₁ j₂))) tl)
                   (fIterD-mono m m d d k k 2≤S ≤-refl ≤-refl hd ≤-refl ≤-refl ≤-refl))
          (≤-reflexive (sym (fIterD-suc S W d k m j)))

-- and the empty burst leaves the level where it found it
burst-nil : ∀ (S W d k j : ℕ) → j + 0 ≤ fIterD S W d k 0 j
burst-nil S W d k j =
  ≤-trans (≤-reflexive (+-identityʳ j)) (≤-reflexive (sym (fIterD-0 S W d k j)))

-- ONE FRAME, and this is the step the REFRESH buys: the frame's own
-- receipt (`fCharge`, what the ground frame clauses pay) and then its
-- payload walk under the budget READ HERE, at this frame's own level.
-- No inherited `k` appears anywhere in it — that is the whole content
-- of the refresh, and one unit of depth fuel is its price
frame-step : ∀ (S W d j j₀ j₁ : ℕ) → 2 ≤ S →
  j₀ ≤ fCharge S W j →
  (j + j₀) + j₁
    ≤ sIterD S W d (suc (sizeAt S (suc j))) (suc (widAt S W j)) (j + j₀) →
  j + (j₀ + j₁) ≤ fLvlD S W (suc d) j
frame-step S W d j j₀ j₁ 2≤S rcpt walk =
  ≤-trans (≤-trans (≤-trans (≤-reflexive (sym (+-assoc j j₀ j₁))) walk)
                   (sIterD-mono (suc (widAt S W j)) (suc (widAt S W j)) d d
                      (suc (sizeAt S (suc j))) (suc (sizeAt S (suc j)))
                      2≤S ≤-refl ≤-refl
                      (+-monoʳ-≤ j rcpt) ≤-refl ≤-refl ≤-refl))
          (≤-reflexive (sym (fLvlD-suc S W d j)))

-- ONE OPERATOR, map / take / *All shape: one j for the frame the chain
-- gains, the SOURCE's subscribe at `suc j`, then pushBurst's frames at
-- the level that subscribe left
op-step : ∀ (S W d k m j j₁ j₂ : ℕ) → 2 ≤ S →
  suc j + j₁ ≤ opIterD S W d k m (suc j) →
  (suc j + j₁) + j₂ ≤ fIterD S W d k (suc (widAt S W (suc j + j₁))) (suc j + j₁) →
  j + suc (j₁ + j₂) ≤ opIterD S W d k (suc m) j
op-step S W d k m j j₁ j₂ 2≤S src pb =
  ≤-trans (≤-trans (≤-trans (≤-reflexive (trans (+-suc j (j₁ + j₂))
                                                (cong suc (sym (+-assoc j j₁ j₂)))))
                            pb)
                   (fIterD-mono (suc (widAt S W (suc j + j₁))) (suc (widAt S W X))
                      d d k k 2≤S ≤-refl ≤-refl A≤X ≤-refl ≤-refl
                      (s≤s (widAt-mono 2≤S ≤-refl ≤-refl A≤X))))
          (≤-reflexive (sym (opIterD-suc S W d k m j)))
  where
  J₀ = suc (j + suc (sizeAt S j) * suc (sizeAt S j))
  X  = opIterD S W d k m (sLvlD S W d k J₀)
  sucj≤J₁ : suc j ≤ sLvlD S W d k J₀
  sucj≤J₁ = ≤-trans (s≤s (m≤m+n j (suc (sizeAt S j) * suc (sizeAt S j))))
                    (sLvlD-infl S W d k J₀)
  A≤X : suc j + j₁ ≤ X
  A≤X = ≤-trans src (opIterD-mono m m d d k k 2≤S ≤-refl ≤-refl sucj≤J₁
                       ≤-refl ≤-refl ≤-refl)

-- ONE OPERATOR, scan shape: an EVAL receipt first (`evalSeed-caps`,
-- `suc (sizeᵗ z)`, so at most `suc (sizeAt S j)`), then the same three
op-step-eval : ∀ (S W d k m j j₀ j₁ j₂ : ℕ) → 2 ≤ S →
  j₀ ≤ suc (sizeAt S j) →
  suc (j + j₀) + j₁ ≤ opIterD S W d k m (suc (j + j₀)) →
  (suc (j + j₀) + j₁) + j₂
    ≤ fIterD S W d k (suc (widAt S W (suc (j + j₀) + j₁))) (suc (j + j₀) + j₁) →
  j + (j₀ + suc (j₁ + j₂)) ≤ opIterD S W d k (suc m) j
op-step-eval S W d k m j j₀ j₁ j₂ 2≤S hj₀ src pb =
  ≤-trans (≤-trans (≤-trans (≤-reflexive
                              (trans (sym (+-assoc j j₀ (suc (j₁ + j₂))))
                                (trans (+-suc (j + j₀) (j₁ + j₂))
                                       (cong suc (sym (+-assoc (j + j₀) j₁ j₂))))))
                            pb)
                   (fIterD-mono (suc (widAt S W (suc (j + j₀) + j₁)))
                      (suc (widAt S W X)) d d k k 2≤S ≤-refl ≤-refl A≤X ≤-refl ≤-refl
                      (s≤s (widAt-mono 2≤S ≤-refl ≤-refl A≤X))))
          (≤-reflexive (sym (opIterD-suc S W d k m j)))
  where
  J₀ = suc (j + suc (sizeAt S j) * suc (sizeAt S j))
  X  = opIterD S W d k m (sLvlD S W d k J₀)
  seed≤ : suc (j + j₀) ≤ sLvlD S W d k J₀
  seed≤ = ≤-trans (s≤s (+-monoʳ-≤ j
                    (≤-trans hj₀ (m≤m*n (suc (sizeAt S j)) (suc (sizeAt S j))))))
                  (sLvlD-infl S W d k J₀)
  A≤X : suc (j + j₀) + j₁ ≤ X
  A≤X = ≤-trans src (opIterD-mono m m d d k k 2≤S ≤-refl ≤-refl seed≤
                       ≤-refl ≤-refl ≤-refl)

-- B + suc (B · B) ≤ suc B · suc B — the arithmetic the μ receipt needs,
-- and the reason the per-operator eval receipt is a SQUARE
quad-arith : ∀ (B : ℕ) → B + suc (B * B) ≤ suc B * suc B
quad-arith B =
  ≤-trans (≤-reflexive (+-suc B (B * B)))
          (≤-trans (s≤s (+-monoʳ-≤ B (m≤n+m (B * B) B)))
                   (≤-reflexive (sym (cong (λ x → suc (B + x)) (*-suc B B)))))

-- ANY EDGE THAT ENTERS A FRESH SUBSCRIBE, with its receipt abstracted.
-- This is the shape the μ step was first written in, and it is not about
-- μ: the proof spends the premise, then `sLvlD-mono` under a bound
-- showing the receipt FITS the room `opIterD … (suc m) j` opens, then two
-- `-infl` steps, then the clause equation.  Only that bound mentions the
-- edge at all, so it becomes a hypothesis and the μ unfolding, the share
-- connect and any other fresh entry are instances rather than copies.
-- The room is QUADRATIC in the level's size cap, which is why any receipt
-- a clause can actually pay fits inside it
op-step-entry : ∀ (S W d k m j r j₁ : ℕ) → 2 ≤ S →
  j + r ≤ suc (j + suc (sizeAt S j) * suc (sizeAt S j)) →
  (j + r) + j₁ ≤ sLvlD S W d k (j + r) →
  j + (r + j₁) ≤ opIterD S W d k (suc m) j
op-step-entry S W d k m j r j₁ 2≤S fits sub =
  ≤-trans (≤-trans (≤-trans (≤-reflexive (sym (+-assoc j r j₁))) sub)
                   (≤-trans (sLvlD-mono d d k k 2≤S ≤-refl ≤-refl fits ≤-refl ≤-refl)
                            (≤-trans (opIterD-infl S W d k m (sLvlD S W d k J₀))
                                     (fIterD-infl S W d k (suc (widAt S W X)) X))))
          (≤-reflexive (sym (opIterD-suc S W d k m j)))
  where
  B  = sizeAt S j
  J₀ = suc (j + suc B * suc B)
  X  = opIterD S W d k m (sLvlD S W d k J₀)

-- THE μ OPERATOR: the unfolding receipt `m₀ + suc (m₀ * m₀)`, and then a
-- FRESH subscribe on a LARGER term — which is why it is charged as one
-- NESTING level rather than as a continuation of the same chain, and
-- why the budget k has to count μ-nesting as well as *All-nesting.  Its
-- whole content is now the `fits` argument: the quadratic receipt inside
-- the quadratic room
op-step-mu : ∀ (S W d k m j m₀ j₁ : ℕ) → 2 ≤ S →
  m₀ ≤ sizeAt S j →
  (j + (m₀ + suc (m₀ * m₀))) + j₁ ≤ sLvlD S W d k (j + (m₀ + suc (m₀ * m₀))) →
  j + ((m₀ + suc (m₀ * m₀)) + j₁) ≤ opIterD S W d k (suc m) j
op-step-mu S W d k m j m₀ j₁ 2≤S hm₀ =
  op-step-entry S W d k m j (m₀ + suc (m₀ * m₀)) j₁ 2≤S quad
  where
  B  = sizeAt S j
  quad : j + (m₀ + suc (m₀ * m₀)) ≤ suc (j + suc B * suc B)
  quad = ≤-trans (+-monoʳ-≤ j (≤-trans (+-mono-≤ hm₀ (s≤s (*-mono-≤ hm₀ hm₀)))
                                       (quad-arith B)))
                 (n≤1+n (j + suc B * suc B))

-- THE SHARE CONNECT: the receipt is 1, the registration for the joining
-- subscriber, and its `fits` is free — one registration sits inside the
-- quadratic room at every cap.  Stated at `suc j` rather than at `j + 1`
-- because that is the shape a clause presents, and `_+_` recursing on its
-- FIRST argument leaves `j + 1` stuck: the conversion belongs here once
-- rather than at every call site
share-fits : ∀ (S j : ℕ) → j + 1 ≤ suc (j + suc (sizeAt S j) * suc (sizeAt S j))
share-fits S j =
  ≤-trans (≤-reflexive (+-comm j 1))
          (s≤s (m≤m+n j (suc (sizeAt S j) * suc (sizeAt S j))))

op-step-share : ∀ (S W d k m j j₁ : ℕ) → 2 ≤ S →
  suc j + j₁ ≤ sLvlD S W d k (suc j) →
  j + suc j₁ ≤ opIterD S W d k (suc m) j
op-step-share S W d k m j j₁ 2≤S sub =
  op-step-entry S W d k m j 1 j₁ 2≤S (share-fits S j)
    (subst (λ x → x + j₁ ≤ sLvlD S W d k x) (sym (+-comm j 1)) sub)

------------------------------------------------------------------
-- § 2.  THE INDEX, and the two directions it travels.
------------------------------------------------------------------

-- THE WALK DIRECTION: fewer operators left is a smaller sweep, so a
-- callee that reports at m feeds a caller that holds `suc m` — which is
-- the gate's own step above, needing no lemma of its own
index-mono : ∀ (S W d k m m′ J : ℕ) → 2 ≤ S → m ≤ m′ →
  opIterD S W d k m J ≤ opIterD S W d k m′ J
index-mono S W d k m m′ J 2≤S hm =
  opIterD-mono m m′ d d k k 2≤S ≤-refl ≤-refl ≤-refl ≤-refl ≤-refl hm

-- THE ENTRY DIRECTION: a fresh subscribe IS the sweep at the index the
-- size cap licenses, by the clause equation alone.  This is the ONE
-- place a unit of budget is spent, and it is an equation rather than a
-- choice: `sIterD`, `opIterD` and `fIterD` all pass k through untouched,
-- so a CARRYING edge — a chain step, a μ step — cannot spend one even if
-- it wanted to, and no clause needs a case split on the budget to thread
-- the hypothesis
entry-is-sweep : ∀ (S W d k J : ℕ) →
  sLvlD S W d (suc k) J ≡ opIterD S W d k (suc (sizeAt S J)) J
entry-is-sweep = sLvlD-suc

-- so a chain member's conjunct is `opIterD S W dep bud m j` with m the
-- operators it has left, and the member that is ENTERED fresh converts
-- once, at the site that also spends the budget descent
entry-to-index : ∀ (S W d k J m : ℕ) → 2 ≤ S → suc (sizeAt S J) ≤ m →
  sLvlD S W d (suc k) J ≤ opIterD S W d k m J
entry-to-index S W d k J m 2≤S hm =
  ≤-trans (≤-reflexive (entry-is-sweep S W d k J))
          (index-mono S W d k (suc (sizeAt S J)) m J 2≤S hm)

-- AND THE WALK'S OWN INDEX IS THE PAYLOAD COUNT.  `sIterD S W d k m J`
-- prices m payloads in sequence, so a walk's conjunct reads
-- `m = length vals` while `frame-step` above consumes the walk at
-- `suc (widAt S W j)`.  Those meet by monotonicity in the index, on the
-- length the caller has in hand — `valsCaps?`'s length conjunct, whose
-- cap `Caps.cWid (frameStep j c)` IS `widAt (cSize c) (cWid c) j`
-- definitionally, so no arithmetic sits between the two
walk-index : ∀ (S W d k m j J : ℕ) → 2 ≤ S → m ≤ suc (widAt S W j) →
  sIterD S W d k m J ≤ sIterD S W d k (suc (widAt S W j)) J
walk-index S W d k m j J 2≤S hm =
  sIterD-mono m (suc (widAt S W j)) d d k k 2≤S ≤-refl ≤-refl ≤-refl ≤-refl ≤-refl hm

-- AND THE BURST'S OWN INDEX IS THE EMIT COUNT, met the same way: on the
-- length `burstCount?` already carries (`countLen`), whose cap
-- `Caps.cWid (frameStep j c)` IS `widAt (cSize c) (cWid c) j`
-- definitionally, so nothing sits between the receipt and the index
burst-index : ∀ (S W d k m j J : ℕ) → 2 ≤ S → m ≤ suc (widAt S W j) →
  fIterD S W d k m J ≤ fIterD S W d k (suc (widAt S W j)) J
burst-index S W d k m j J 2≤S hm =
  fIterD-mono m (suc (widAt S W j)) d d k k 2≤S ≤-refl ≤-refl ≤-refl ≤-refl ≤-refl hm

------------------------------------------------------------------
-- § 3.  AND THE INDEX DESCENDS ACROSS A CHAIN EDGE.
--
-- `op-step` concludes at `suc m`, so an operator clause can only report
-- if its own index is a SUCCESSOR — which means every clause that
-- recurses splits its index, and hands the source the predecessor.
-- `chain-desc` is what the source's hypothesis costs at that handoff.
--
-- The clause holds `suc (sizeᵉ TERM) ≤ suc m′` and owes
-- `suc (sizeᵉ SOURCE) ≤ m′`, and every chain constructor's size is
-- `suc (head + source)` (Rx.Exp:466-475), so ONE lemma covers the whole
-- family: `hd := sizeᵗ f` for map and take, `hd := sizeᵗ f + sizeᵗ z`
-- for scan (`+` associates left, so its head being a sum costs no
-- rewrite), and `hd := 0` for the headless six (mergeAll, concatAll,
-- switchAll, exhaustAll, μ, defer), where `0 + src` reduces to `src`
-- definitionally and the lemma degenerates to `≤-pred`.
--
-- The zero case needs nothing at all: `suc x ≤ zero` is uninhabited by
-- CONSTRUCTOR — neither `z≤n` nor `s≤s` can build it — so the split's
-- other half is an absurd pattern whatever the stuck head term is, and
-- costs one line per clause rather than a proof.
chain-desc : ∀ (hd src m′ : ℕ) → suc (suc (hd + src)) ≤ suc m′ → suc src ≤ m′
chain-desc hd src m′ (s≤s h) = ≤-trans (s≤s (m≤n+m src hd)) h
