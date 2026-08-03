------------------------------------------------------------------
-- THE PER-FRAME BUDGET REFRESH: does the re-ruling close?
--
-- Worker 36 (agda/probe/Nest-Budget-Probe.agda § 3) refuted the descent
-- the nesting budget `k` was ruled on: a `scanᵉ` under an *All MINTS a
-- payload per fold, the k-th mint nests k deep, and it is subscribed in
-- the SAME delivery — so a k read once at a subscribe's start is spent
-- at levels the walk has CLIMBED to, where the admissible nesting is
-- larger.  The design session re-ruled it as a PER-FRAME REFRESH: k is
-- not inherited down the subscribe tree, every FRAME ENTRY re-reads
-- `k := suc (sizeAt S J)` at that frame's own level.
--
-- THIS PROBE GATES THAT RULING, AND IT SPLITS IN TWO.
--
-- § 1  THE SOUNDNESS SIDE PASSES, and it passes as a THEOREM rather than
--      as a table: NO row can breach it.  A frame subscribes exactly two
--      kinds of payload — the values ARRIVING at it (thru-outer's own
--      `vals`, which `thruWalk` walks one at a time) and the values a
--      concat frame QUEUED at an EARLIER arrival (`concat-st`'s q).  The
--      first are bounded by `valsCaps?` at THAT frame's entry level; the
--      second at a level the walk has since climbed PAST, so the current
--      reading dominates them by `sizeAt-mono`.  With Worker 36's
--      `nest≤sizeᵛ` on top, every arriving payload has
--      `nestᵛ ≤ sizeᵛ ≤ sizeAt S J_entry`.  § 1 pins the two suppliers
--      against the evaluator's own clauses and carries the rows on
--      values the REAL `applyFn` minted (Worker 36's `acc` family, and a
--      deepening one built here), so the gate is measured as well as
--      argued.
--
-- § 2  THE TERMINATION SIDE FAILS, MACHINE-CHECKED.  Taken literally —
--      `fLvlK` drops the inherited k and re-reads its own — the family
--      is NOT a function: Agda rejects it, and the reason is structural
--      rather than a checker weakness.  `k` was the ONLY descending
--      argument in the cycle
--
--        fLvlK → sIterK → sLvlK → opIterK → fIterK → fLvlK
--
--      (every cycle passes `sLvlK`, where `suc k ↦ k`).  Refreshing k at
--      `fLvlK` regenerates it at a HIGHER level, i.e. LARGER, so the one
--      descent is gone and nothing replaces it: `sIterK`'s and
--      `fIterK`'s m — the "frame fuel the family already iterates" — are
--      themselves regenerated from `widAt` at the climbed level on every
--      turn, so they ascend too.  The rejection is in the report.
--
-- § 3-§ 7  SO THE PROBE CARRIES THE REPAIR THAT DOES CLOSE: the refresh
--      with an explicit DEPTH FUEL `d` that the frame entry spends.  `k`
--      is re-read at each frame from that frame's own level (the ruling)
--      and `d` is what descends (termination).  § 3 is the family, § 4
--      its inflation, § 5 its monotonicity in all five arguments, § 6
--      the gate `fLvl ≤ fLvlD` and the DOMINATION `fLvlK ≤ fLvlD`, § 7
--      the four composition-gate steps of Sub-Charge-Probe § 5 re-proven
--      against it.  All of it typechecks with no pragmas.
--
-- § 8  AND NAMES WHAT IS STILL OPEN, WHICH IS ONE NUMBER: what `d` is
--      instantiated at.  It cannot be read off (S, W, J) at the
--      delivery's entry — the SAME mint that refuted the nesting budget
--      refutes a depth budget read there, because a mint at a deep frame
--      contributes ITS nesting to the remaining depth and is bounded
--      only by `sizeAt` at the level it was minted at.  The one supplier
--      that is not circular is the evaluator's OWN fuel: `subscribeInner
--      g0` returns a dry burst, so the subscribe-nesting depth is
--      bounded by the `Gas` argument `subscribeE-caps` already carries,
--      and an induction on it owes nothing new.  Whether that is
--      affordable — `Gas` is `budgetAt`, and `budgetAt`'s tower HEIGHT
--      runs through `poolCount`, hence through `lvls`, hence through the
--      very level the fuel is being threaded into — is a ruling, not a
--      grind, and § 8 states the cycle exactly.
------------------------------------------------------------------
module Refresh-Probe where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Bool using (Bool; true; false)
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Rx.Exp
  using (Ctx; Val; Fn; natᵗ; obs; _×ᵗ_; emptyᵉ; ofᵉ; mergeAllᵉ; strmᵗ;
         fstᵗ; varᵗ; sizeᵉ; sizeᵛ; applyFn)

open import Nest-Budget-Probe
  using (nestᵛ; nest≤sizeᵛ; acc; carrier; Γ₀)

------------------------------------------------------------------
-- the repo's arithmetic, off the walk probe that already carries it,
-- exactly as Sub-Charge-Probe takes it — so this probe costs no rebuild
-- of the tree
------------------------------------------------------------------

open import Level-Walk-Probe
  using (sizeAt; widAt; fCharge; fLvl; sizeAt-mono; widAt-mono; fLvl-mono)

------------------------------------------------------------------
-- § 1  THE SOUNDNESS SIDE, and it is a THEOREM.
--
-- WHAT A FRAME SUBSCRIBES.  Read off Rx.Evaluator's `stepFrame`, the
-- only two clauses that reach `subscribeInner`:
--
--   stepFrame … (thru-outer op nid) κ vals fin …
--     = thruWrap op nid fin (thruWalk fuel op nid κ id now vals … )
--   thruWalk … (o ∷ os) … = … subscribeInner fuel op nid κ id now o …
--
-- so a thru-outer frame's payloads are ITS OWN ARRIVING VALUES, one for
-- one — `valsCaps?` at that frame's entry level is exactly the
-- hypothesis `FrameFace` already carries about them; and
--
--   … | just (concat-st {w} q true od) = … setNode nid (concat-st (q ++ o ∷ []) true od) …
--   concatDrain … (o ∷ q) … = … subscribeInner fuel concatᵒ allNid κ id now o …
--
-- so a concat frame may subscribe a payload it QUEUED at an earlier
-- arrival.  That value was capped at the level of the arrival that
-- enqueued it, which the walk has since climbed PAST — and levels only
-- climb (`fLvlD-infl`, § 4), so the CURRENT reading dominates the one it
-- was capped at.  `switch-st` and `exhaust-st` hold no values at all
-- (`Maybe NodeId` and two `Bool`s), so there is no third supplier.
--
-- THE ARITHMETIC OF THE SECOND SUPPLIER is one `sizeAt-mono`: a payload
-- queued at level J₀ ≤ J is admitted by the reading at J
------------------------------------------------------------------

queued-admits : ∀ (S J₀ J : ℕ) → 1 ≤ S → J₀ ≤ J →
  suc (sizeAt S J₀) ≤ suc (sizeAt S J)
queued-admits S J₀ J 1≤S hJ = s≤s (sizeAt-mono 1≤S ≤-refl hJ)

-- and the gate itself, with Worker 36's proven `nestᵛ ≤ sizeᵛ` on top:
-- a payload capped in SIZE at the reading is capped in NESTING by it
gate : ∀ {n} {Γ : Ctx n} (S J : ℕ) (t : _) (v : Val Γ t) →
  sizeᵛ t v ≤ sizeAt S J → nestᵛ t v ≤ sizeAt S J
gate S J t v h = ≤-trans (nest≤sizeᵛ t v) h

-- the same for the queued supplier, composed: capped at the level it was
-- enqueued at, admitted by the level the frame reads at
gate-queued : ∀ {n} {Γ : Ctx n} (S J₀ J : ℕ) (t : _) (v : Val Γ t) →
  1 ≤ S → J₀ ≤ J → sizeᵛ t v ≤ sizeAt S J₀ → nestᵛ t v ≤ sizeAt S J
gate-queued S J₀ J t v 1≤S hJ h =
  ≤-trans (gate S J₀ t v h) (sizeAt-mono 1≤S ≤-refl hJ)

------------------------------------------------------------------
-- § 1a  THE ROWS, on values the REAL `applyFn` minted.
--
-- Worker 36's `acc` family is the hardest case there is for the ruling —
-- it is the one that refuted the OLD budget — so it is the one the gate
-- is read on.  Every row is `nestᵛ ≤ᵇ sizeᵛ`, and the gate is that
-- inequality composed with the frame's own size admission
------------------------------------------------------------------

_ : (nestᵛ (obs natᵗ) (acc 0) ≤ᵇ sizeᵛ (obs natᵗ) (acc 0)) ≡ true
_ = refl

_ : (nestᵛ (obs natᵗ) (acc 1) ≤ᵇ sizeᵛ (obs natᵗ) (acc 1)) ≡ true
_ = refl

_ : (nestᵛ (obs natᵗ) (acc 2) ≤ᵇ sizeᵛ (obs natᵗ) (acc 2)) ≡ true
_ = refl

_ : (nestᵛ (obs natᵗ) (acc 3) ≤ᵇ sizeᵛ (obs natᵗ) (acc 3)) ≡ true
_ = refl

_ : (nestᵛ (obs natᵗ) (acc 5) ≤ᵇ sizeᵛ (obs natᵗ) (acc 5)) ≡ true
_ = refl

_ : (nestᵛ (obs natᵗ) (acc 8) ≤ᵇ sizeᵛ (obs natᵗ) (acc 8)) ≡ true
_ = refl

-- A DEEPENING MINT: the step wraps the accumulator under TWO *All
-- layers, so one fold buys two nesting levels.  The point of the row is
-- that the RATIO nest/size does not approach 1 — the gate has slack that
-- grows, so no sharpening of the mint closes it
wrap2Fn : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
wrap2Fn = strmᵗ (mergeAllᵉ (ofᵉ (strmᵗ (mergeAllᵉ
            (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ []))) ∷ [])))

acc2 : ℕ → Val Γ₀ (obs natᵗ)
acc2 zero    = emptyᵉ
acc2 (suc k) = applyFn wrap2Fn (acc2 k , 0)

-- two nesting levels per fold
_ : nestᵛ (obs natᵗ) (acc2 3) ≡ 6
_ = refl

_ : nestᵛ (obs natᵗ) (acc2 5) ≡ 10
_ = refl

-- and the size outruns it anyway, by a factor that GROWS
_ : sizeᵛ (obs natᵗ) (acc2 3) ≡ 34
_ = refl

_ : sizeᵛ (obs natᵗ) (acc2 5) ≡ 56
_ = refl

_ : (nestᵛ (obs natᵗ) (acc2 3) ≤ᵇ sizeᵛ (obs natᵗ) (acc2 3)) ≡ true
_ = refl

_ : (nestᵛ (obs natᵗ) (acc2 5) ≤ᵇ sizeᵛ (obs natᵗ) (acc2 5)) ≡ true
_ = refl

-- THE CARRIER'S OWN READING, which is what a frame at level 0 admits:
-- the mint sits under it at every rung of both families, so the gate
-- passes on the row that refuted the old budget
_ : sizeᵉ carrier ≡ 17
_ = refl

-- AND THE ENTRY READING DOES NOT ADMIT THE MINT, which is what the
-- refresh is FOR: `acc 5` has size 36 against a level-0 reading of 17
_ : sizeᵛ (obs natᵗ) (acc 5) ≡ 36
_ = refl

_ : sizeAt (sizeᵉ carrier) 0 ≡ 17
_ = refl

_ : (sizeᵛ (obs natᵗ) (acc 5) ≤ᵇ sizeAt (sizeᵉ carrier) 0) ≡ false
_ = refl

-- ONE LEVEL OF CLIMB ADMITS IT, and the frame the mint arrives at is
-- past that level by construction — the scan's own frames ran first.
-- This is the refresh, on the row that refuted the inherited budget
_ : sizeAt (sizeᵉ carrier) 1 ≡ 595
_ = refl

_ : (sizeᵛ (obs natᵗ) (acc 5) ≤ᵇ sizeAt (sizeᵉ carrier) 1) ≡ true
_ = refl

_ : (nestᵛ (obs natᵗ) (acc 5) ≤ᵇ sizeAt (sizeᵉ carrier) 1) ≡ true
_ = refl

------------------------------------------------------------------
-- § 2  THE LITERAL RESHAPE IS NOT A FUNCTION.
--
-- The ruling's family, verbatim — `fLvlK` drops the inherited k and
-- re-reads `suc (sizeAt S J)` at its own level:
--
--   fLvlA  S W J         = sIterA S W (suc (sizeAt S J)) (suc (widAt S W J)) (fLvl S W J)
--   sIterA S W k (suc m) J = sIterA S W k m (sLvlA S W k (suc J))
--   sLvlA  S W (suc k) J = opIterA S W k (suc (sizeAt S J)) J
--   opIterA … (suc m) J  = fIterA S W k (suc (widAt S W J₂)) J₂
--   fIterA S W k (suc m) J = fIterA S W k m (fLvlA S W J)
--
-- Agda rejects it, naming every clause:
--
--   Termination checking failed for the following functions:
--     fLvlA, sIterA, sLvlA, opIterA, fIterA
--
-- and the rejection is not a checker weakness.  `k` was the ONE
-- descending argument: every cycle in the call graph passes `sLvlK`,
-- whose clause is `suc k ↦ k`, and all four other functions carry k
-- unchanged.  The refresh regenerates it at the frame's own level, which
-- by inflation is HIGHER than the level it was last read at, so the
-- regenerated budget is LARGER (`sizeAt-mono`) — the descent is not
-- weakened, it is reversed.  Nor do the iteration counts replace it:
-- `fIterK`'s m is `suc (widAt S W J₂)` and `fLvlK`'s is
-- `suc (widAt S W J)`, both re-read at the climbed level, so they ascend
-- for the same reason.
--
-- WHAT THE REFRESH ACTUALLY NEEDS is a second, DESCENDING index — the
-- subscribe-nesting DEPTH, spent once per frame entry.  That is § 3, and
-- it is the ruling's own lexicographic pairing with the two roles `k`
-- was carrying pulled apart: `d` bounds how DEEP the frame tree goes,
-- `k` bounds how deep ONE frame's payloads nest, and only the first has
-- to descend
------------------------------------------------------------------

------------------------------------------------------------------
-- § 3  THE FAMILY, RESHAPED.  Identical to Rx.Evaluator's clause for
-- clause except at `fLvlD`, which spends one `d` and re-reads
-- `suc (sizeAt S J)` at its own level instead of inheriting.
--
-- THE d = 0 CLAUSE is not arbitrary: it is exactly what the old family
-- does at k = 0 (`sIterK S W 0 m J = J + m`, § 6's `sIterK-zero`), so
-- the reshape dominates the old one at EVERY budget including the empty
-- one, and the fuel-exhausted case is a bound rather than a hole.  It
-- also carries the termination: the clause makes no recursive call, so
-- every cycle must pass the `suc d` clause, where d descends
------------------------------------------------------------------

mutual
  -- ONE FRAME that ran at J: its own receipt, then one inner subscribe
  -- per payload — at most `suc (widAt S W J)` of them.  The budget its
  -- payloads are walked under is read HERE, at this frame's own level
  fLvlD : ℕ → ℕ → ℕ → ℕ → ℕ            -- S W d J
  fLvlD S W zero    J = fLvl S W J + suc (widAt S W J)
  fLvlD S W (suc d) J =
    sIterD S W d (suc (sizeAt S J)) (suc (widAt S W J)) (fLvl S W J)

  -- m payloads in sequence, each at the level the one before it LEFT
  sIterD : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ   -- S W d k m J
  sIterD S W d k zero    J = J
  sIterD S W d k (suc m) J = sIterD S W d k m (sLvlD S W d k (suc J))

  -- ONE SUBSCRIBE at J, walking the target's operator chain
  sLvlD : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ        -- S W d k J
  sLvlD S W d zero    J = J
  sLvlD S W d (suc k) J = opIterD S W d k (suc (sizeAt S J)) J

  -- ONE OPERATOR, in the order the clause runs it
  opIterD : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ  -- S W d k m J
  opIterD S W d k zero    J = J
  opIterD S W d k (suc m) J =
    let J₀ = suc (J + suc (sizeAt S J) * suc (sizeAt S J))
        J₂ = opIterD S W d k m (sLvlD S W d k J₀)
    in fIterD S W d k (suc (widAt S W J₂)) J₂

  fIterD : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ   -- S W d k m J
  fIterD S W d k zero    J = J
  fIterD S W d k (suc m) J = fIterD S W d k m (fLvlD S W d J)

------------------------------------------------------------------
-- § 4  EVERY TRANSFORMER IS STILL INFLATIONARY — a level never goes
-- down, which is what the § 1 queued-payload argument reads and what
-- every gate below is built from
------------------------------------------------------------------

mutual

  fLvlD-infl : ∀ (S W d J : ℕ) → J ≤ fLvlD S W d J
  fLvlD-infl S W zero    J =
    ≤-trans (m≤m+n J (fCharge S W J)) (m≤m+n (fLvl S W J) (suc (widAt S W J)))
  fLvlD-infl S W (suc d) J =
    ≤-trans (m≤m+n J (fCharge S W J))
            (sIterD-infl S W d (suc (sizeAt S J)) (suc (widAt S W J)) (fLvl S W J))

  sIterD-infl : ∀ (S W d k m J : ℕ) → J ≤ sIterD S W d k m J
  sIterD-infl S W d k zero    J = ≤-refl
  sIterD-infl S W d k (suc m) J =
    ≤-trans (≤-trans (n≤1+n J) (sLvlD-infl S W d k (suc J)))
            (sIterD-infl S W d k m (sLvlD S W d k (suc J)))

  sLvlD-infl : ∀ (S W d k J : ℕ) → J ≤ sLvlD S W d k J
  sLvlD-infl S W d zero    J = ≤-refl
  sLvlD-infl S W d (suc k) J = opIterD-infl S W d k (suc (sizeAt S J)) J

  opIterD-infl : ∀ (S W d k m J : ℕ) → J ≤ opIterD S W d k m J
  opIterD-infl S W d k zero    J = ≤-refl
  opIterD-infl S W d k (suc m) J =
    ≤-trans (≤-trans (≤-trans (n≤1+n J)
                              (s≤s (m≤m+n J (suc (sizeAt S J) * suc (sizeAt S J)))))
                     (≤-trans (sLvlD-infl S W d k
                                 (suc (J + suc (sizeAt S J) * suc (sizeAt S J))))
                              (opIterD-infl S W d k m
                                 (sLvlD S W d k
                                    (suc (J + suc (sizeAt S J) * suc (sizeAt S J)))))))
            (fIterD-infl S W d k
               (suc (widAt S W (opIterD S W d k m
                       (sLvlD S W d k
                          (suc (J + suc (sizeAt S J) * suc (sizeAt S J)))))))
               (opIterD S W d k m
                  (sLvlD S W d k (suc (J + suc (sizeAt S J) * suc (sizeAt S J))))))

  fIterD-infl : ∀ (S W d k m J : ℕ) → J ≤ fIterD S W d k m J
  fIterD-infl S W d k zero    J = ≤-refl
  fIterD-infl S W d k (suc m) J =
    ≤-trans (fLvlD-infl S W d J) (fIterD-infl S W d k m (fLvlD S W d J))

------------------------------------------------------------------
-- § 5  AND MONOTONE IN ALL FIVE ARGUMENTS, the depth fuel included.
-- This is what keeps the rewiring cheap: `iterL-mono`, `dLvl-mono`,
-- `lvls-mono` and `dCapᶜ-mono` are built from `fLvl-mono` and nothing
-- else, so the whole ladder above the frame moves with this one lemma
------------------------------------------------------------------

mutual

  fLvlD-mono : ∀ {S S′ W W′ J J′} (d d′ : ℕ) → 2 ≤ S → S ≤ S′ → W ≤ W′ → J ≤ J′ →
    d ≤ d′ → fLvlD S W d J ≤ fLvlD S′ W′ d′ J′
  fLvlD-mono {S} {S′} {W} {W′} {J} {J′} zero zero 2≤S hS hW hJ hd =
    +-mono-≤ (fLvl-mono 2≤S hS hW hJ) (s≤s (widAt-mono 2≤S hS hW hJ))
  fLvlD-mono {S} {S′} {W} {W′} {J} {J′} zero (suc d′) 2≤S hS hW hJ hd =
    ≤-trans (+-mono-≤ (fLvl-mono 2≤S hS hW hJ) (s≤s (widAt-mono 2≤S hS hW hJ)))
            (sIterD-zero≤ S′ W′ d′ (suc (sizeAt S′ J′)) (suc (widAt S′ W′ J′))
                          (fLvl S′ W′ J′))
  fLvlD-mono (suc d) zero 2≤S hS hW hJ ()
  fLvlD-mono {S} {S′} {W} {W′} {J} {J′} (suc d) (suc d′) 2≤S hS hW hJ (s≤s hd) =
    sIterD-mono (suc (widAt S W J)) (suc (widAt S′ W′ J′)) d d′
      (suc (sizeAt S J)) (suc (sizeAt S′ J′)) 2≤S hS hW
      (fLvl-mono 2≤S hS hW hJ) hd
      (s≤s (sizeAt-mono (≤-trans (s≤s z≤n) 2≤S) hS hJ))
      (s≤s (widAt-mono 2≤S hS hW hJ))

  -- the d = 0 clause is UNDER the general one: `J + m` is what `sIterD`
  -- does when its budget is empty, and its budget is never emptier than
  -- that
  sIterD-zero≤ : ∀ (S W d k m J : ℕ) → J + m ≤ sIterD S W d k m J
  sIterD-zero≤ S W d k zero    J = ≤-reflexive (+-identityʳ J)
  sIterD-zero≤ S W d k (suc m) J =
    ≤-trans (≤-reflexive (+-suc J m))
            (≤-trans (+-monoˡ-≤ m (sLvlD-infl S W d k (suc J)))
                     (sIterD-zero≤ S W d k m (sLvlD S W d k (suc J))))

  sIterD-mono : ∀ {S S′ W W′ J J′} (m m′ d d′ k k′ : ℕ) →
    2 ≤ S → S ≤ S′ → W ≤ W′ → J ≤ J′ → d ≤ d′ → k ≤ k′ → m ≤ m′ →
    sIterD S W d k m J ≤ sIterD S′ W′ d′ k′ m′ J′
  sIterD-mono {S′ = S′} {W′ = W′} {J′ = J′} zero m′ d d′ k k′ 2≤S hS hW hJ hd hk hm =
    ≤-trans hJ (sIterD-infl S′ W′ d′ k′ m′ J′)
  sIterD-mono (suc m) zero    d d′ k k′ 2≤S hS hW hJ hd hk ()
  sIterD-mono (suc m) (suc m′) d d′ k k′ 2≤S hS hW hJ hd hk (s≤s hm) =
    sIterD-mono m m′ d d′ k k′ 2≤S hS hW
      (sLvlD-mono d d′ k k′ 2≤S hS hW (s≤s hJ) hd hk) hd hk hm

  sLvlD-mono : ∀ {S S′ W W′ J J′} (d d′ k k′ : ℕ) →
    2 ≤ S → S ≤ S′ → W ≤ W′ → J ≤ J′ → d ≤ d′ → k ≤ k′ →
    sLvlD S W d k J ≤ sLvlD S′ W′ d′ k′ J′
  sLvlD-mono {S′ = S′} {W′ = W′} {J′ = J′} d d′ zero k′ 2≤S hS hW hJ hd hk =
    ≤-trans hJ (sLvlD-infl S′ W′ d′ k′ J′)
  sLvlD-mono d d′ (suc k) zero 2≤S hS hW hJ hd ()
  sLvlD-mono {S} {S′} {J = J} {J′ = J′} d d′ (suc k) (suc k′)
             2≤S hS hW hJ hd (s≤s hk) =
    opIterD-mono (suc (sizeAt S J)) (suc (sizeAt S′ J′)) d d′ k k′ 2≤S hS hW hJ hd hk
      (s≤s (sizeAt-mono (≤-trans (s≤s z≤n) 2≤S) hS hJ))

  opIterD-mono : ∀ {S S′ W W′ J J′} (m m′ d d′ k k′ : ℕ) →
    2 ≤ S → S ≤ S′ → W ≤ W′ → J ≤ J′ → d ≤ d′ → k ≤ k′ → m ≤ m′ →
    opIterD S W d k m J ≤ opIterD S′ W′ d′ k′ m′ J′
  opIterD-mono {S′ = S′} {W′ = W′} {J′ = J′} zero m′ d d′ k k′ 2≤S hS hW hJ hd hk hm =
    ≤-trans hJ (opIterD-infl S′ W′ d′ k′ m′ J′)
  opIterD-mono (suc m) zero    d d′ k k′ 2≤S hS hW hJ hd hk ()
  opIterD-mono {S} {S′} {W} {W′} {J} {J′} (suc m) (suc m′) d d′ k k′
               2≤S hS hW hJ hd hk (s≤s hm) =
    fIterD-mono (suc (widAt S W X)) (suc (widAt S′ W′ X′)) d d′ k k′ 2≤S hS hW
      inner hd hk (s≤s (widAt-mono 2≤S hS hW inner))
    where
    sz≤ = sizeAt-mono (≤-trans (s≤s z≤n) 2≤S) hS hJ
    J₀≤ : suc (J + suc (sizeAt S J) * suc (sizeAt S J))
            ≤ suc (J′ + suc (sizeAt S′ J′) * suc (sizeAt S′ J′))
    J₀≤ = s≤s (+-mono-≤ hJ (*-mono-≤ (s≤s sz≤) (s≤s sz≤)))
    X  = opIterD S W d k m
           (sLvlD S W d k (suc (J + suc (sizeAt S J) * suc (sizeAt S J))))
    X′ = opIterD S′ W′ d′ k′ m′
           (sLvlD S′ W′ d′ k′ (suc (J′ + suc (sizeAt S′ J′) * suc (sizeAt S′ J′))))
    inner : X ≤ X′
    inner = opIterD-mono m m′ d d′ k k′ 2≤S hS hW
              (sLvlD-mono d d′ k k′ 2≤S hS hW J₀≤ hd hk) hd hk hm

  fIterD-mono : ∀ {S S′ W W′ J J′} (m m′ d d′ k k′ : ℕ) →
    2 ≤ S → S ≤ S′ → W ≤ W′ → J ≤ J′ → d ≤ d′ → k ≤ k′ → m ≤ m′ →
    fIterD S W d k m J ≤ fIterD S′ W′ d′ k′ m′ J′
  fIterD-mono {S′ = S′} {W′ = W′} {J′ = J′} zero m′ d d′ k k′ 2≤S hS hW hJ hd hk hm =
    ≤-trans hJ (fIterD-infl S′ W′ d′ k′ m′ J′)
  fIterD-mono (suc m) zero    d d′ k k′ 2≤S hS hW hJ hd hk ()
  fIterD-mono (suc m) (suc m′) d d′ k k′ 2≤S hS hW hJ hd hk (s≤s hm) =
    fIterD-mono m m′ d d′ k k′ 2≤S hS hW
      (fLvlD-mono d d′ 2≤S hS hW hJ hd) hd hk hm

------------------------------------------------------------------
-- § 6  THE GATES.
--
-- (a) the old per-frame receipt survives inside the new one as its first
--     step, at EVERY depth fuel — so everything above `fLvl` in the walk
--     moves up by the monotonicity lemmas already proven
------------------------------------------------------------------

fLvl≤fLvlD : ∀ (S W d J : ℕ) → fLvl S W J ≤ fLvlD S W d J
fLvl≤fLvlD S W zero    J = m≤m+n (fLvl S W J) (suc (widAt S W J))
fLvl≤fLvlD S W (suc d) J =
  sIterD-infl S W d (suc (sizeAt S J)) (suc (widAt S W J)) (fLvl S W J)

------------------------------------------------------------------
-- (b) AND THE RESHAPE DOMINATES THE FAMILY IT REPLACES.  This is the
-- gate that says the re-ruling costs nothing already proven: at every
-- budget the old family reads at a subscribe's start, the refreshed one
-- is above it, because the refresh happens at a level the walk has
-- CLIMBED to and `sizeAt` is monotone in the level — the regenerated
-- budget is never smaller than the inherited one it replaces.
--
-- The invariant is carried as a REFERENCE LEVEL L: the level the old
-- family read its k at, with `L ≤ J` at every site.  `sizeAt-mono` then
-- hands the refreshed reading back whenever `fLvlD` re-reads
------------------------------------------------------------------

-- the old family, restated here (Sub-Charge-Probe's, so the domination
-- is against the shape actually landed in Rx.Evaluator)
mutual
  fLvlK : ℕ → ℕ → ℕ → ℕ → ℕ
  fLvlK S W k J = sIterK S W k (suc (widAt S W J)) (fLvl S W J)

  sIterK : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  sIterK S W k zero    J = J
  sIterK S W k (suc m) J = sIterK S W k m (sLvlK S W k (suc J))

  sLvlK : ℕ → ℕ → ℕ → ℕ → ℕ
  sLvlK S W zero    J = J
  sLvlK S W (suc k) J = opIterK S W k (suc (sizeAt S J)) J

  opIterK : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  opIterK S W k zero    J = J
  opIterK S W k (suc m) J =
    let J₀ = suc (J + suc (sizeAt S J) * suc (sizeAt S J))
        J₂ = opIterK S W k m (sLvlK S W k J₀)
    in fIterK S W k (suc (widAt S W J₂)) J₂

  fIterK : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  fIterK S W k zero    J = J
  fIterK S W k (suc m) J = fIterK S W k m (fLvlK S W k J)

-- what the old family does with an EMPTY budget, which is what fixes
-- `fLvlD`'s d = 0 clause: one level per payload and nothing else
sIterK-zero : ∀ (S W m J : ℕ) → sIterK S W 0 m J ≡ J + m
sIterK-zero S W zero    J = sym (+-identityʳ J)
sIterK-zero S W (suc m) J =
  trans (sIterK-zero S W m (suc J)) (sym (+-suc J m))

mutual

  fLvlK≤fLvlD : ∀ (S W k d J : ℕ) → 2 ≤ S → k ≤ suc (sizeAt S J) → k ≤ d →
    fLvlK S W k J ≤ fLvlD S W d J
  fLvlK≤fLvlD S W zero zero J 2≤S hk hd =
    ≤-reflexive (sIterK-zero S W (suc (widAt S W J)) (fLvl S W J))
  fLvlK≤fLvlD S W zero (suc d) J 2≤S hk hd =
    ≤-trans (≤-reflexive (sIterK-zero S W (suc (widAt S W J)) (fLvl S W J)))
            (sIterD-zero≤ S W d (suc (sizeAt S J)) (suc (widAt S W J)) (fLvl S W J))
  fLvlK≤fLvlD S W (suc k) zero J 2≤S hk ()
  fLvlK≤fLvlD S W (suc k) (suc d) J 2≤S hk (s≤s hd) =
    sIterK≤sIterD S W (suc k) (suc (sizeAt S J)) d
      (suc (widAt S W J)) J (fLvl S W J) 2≤S hk hk
      (≤-trans (m≤m+n J (fCharge S W J)) ≤-refl) (s≤s hd)

  -- L is the reference level: the level the OLD family read its k at
  sIterK≤sIterD : ∀ (S W k k′ d m L J : ℕ) → 2 ≤ S →
    k ≤ k′ → k ≤ suc (sizeAt S L) → L ≤ J → k ≤ suc d →
    sIterK S W k m J ≤ sIterD S W d k′ m J
  sIterK≤sIterD S W k k′ d zero    L J 2≤S hk′ hL hLJ hd = ≤-refl
  sIterK≤sIterD S W k k′ d (suc m) L J 2≤S hk′ hL hLJ hd =
    ≤-trans (sIterK≤sIterD S W k k′ d m L (sLvlK S W k (suc J)) 2≤S hk′ hL
               (≤-trans hLJ (≤-trans (n≤1+n J) (sLvlK-infl S W k (suc J)))) hd)
            (sIterD-mono m m d d k′ k′ 2≤S ≤-refl ≤-refl
               (sLvlK≤sLvlD S W k k′ d L (suc J) 2≤S hk′ hL
                  (≤-trans hLJ (n≤1+n J)) hd)
               ≤-refl ≤-refl ≤-refl)

  sLvlK≤sLvlD : ∀ (S W k k′ d L J : ℕ) → 2 ≤ S →
    k ≤ k′ → k ≤ suc (sizeAt S L) → L ≤ J → k ≤ suc d →
    sLvlK S W k J ≤ sLvlD S W d k′ J
  sLvlK≤sLvlD S W zero k′ d L J 2≤S hk′ hL hLJ hd = sLvlD-infl S W d k′ J
  sLvlK≤sLvlD S W (suc k) zero d L J 2≤S () hL hLJ hd
  sLvlK≤sLvlD S W (suc k) (suc k′) d L J 2≤S (s≤s hk′) hL hLJ (s≤s hd) =
    opIterK≤opIterD S W k k′ d (suc (sizeAt S J)) L J 2≤S hk′
      (≤-trans (n≤1+n k) hL) hLJ hd

  opIterK≤opIterD : ∀ (S W k k′ d m L J : ℕ) → 2 ≤ S →
    k ≤ k′ → k ≤ suc (sizeAt S L) → L ≤ J → k ≤ d →
    opIterK S W k m J ≤ opIterD S W d k′ m J
  opIterK≤opIterD S W k k′ d zero    L J 2≤S hk′ hL hLJ hd = ≤-refl
  opIterK≤opIterD S W k k′ d (suc m) L J 2≤S hk′ hL hLJ hd =
    ≤-trans (fIterK≤fIterD S W k k′ d (suc (widAt S W Xᴷ)) L Xᴷ 2≤S hk′ hL
               (≤-trans hLJ L≤Xᴷ) hd)
            (fIterD-mono (suc (widAt S W Xᴷ)) (suc (widAt S W Xᴰ)) d d k′ k′
               2≤S ≤-refl ≤-refl X≤ ≤-refl ≤-refl
               (s≤s (widAt-mono 2≤S ≤-refl ≤-refl X≤)))
    where
    J₀ = suc (J + suc (sizeAt S J) * suc (sizeAt S J))
    J≤J₀ : J ≤ J₀
    J≤J₀ = ≤-trans (n≤1+n J) (s≤s (m≤m+n J (suc (sizeAt S J) * suc (sizeAt S J))))
    Xᴷ = opIterK S W k m (sLvlK S W k J₀)
    Xᴰ = opIterD S W d k′ m (sLvlD S W d k′ J₀)
    L≤Xᴷ : J ≤ Xᴷ
    L≤Xᴷ = ≤-trans J≤J₀ (≤-trans (sLvlK-infl S W k J₀)
                                 (opIterK-infl S W k m (sLvlK S W k J₀)))
    X≤ : Xᴷ ≤ Xᴰ
    X≤ = ≤-trans (opIterK≤opIterD S W k k′ d m L (sLvlK S W k J₀) 2≤S hk′ hL
                    (≤-trans hLJ (≤-trans J≤J₀ (sLvlK-infl S W k J₀))) hd)
                 (opIterD-mono m m d d k′ k′ 2≤S ≤-refl ≤-refl
                    (sLvlK≤sLvlD S W k k′ d L J₀ 2≤S hk′ hL
                       (≤-trans hLJ J≤J₀) (≤-trans hd (n≤1+n d)))
                    ≤-refl ≤-refl ≤-refl)

  fIterK≤fIterD : ∀ (S W k k′ d m L J : ℕ) → 2 ≤ S →
    k ≤ k′ → k ≤ suc (sizeAt S L) → L ≤ J → k ≤ d →
    fIterK S W k m J ≤ fIterD S W d k′ m J
  fIterK≤fIterD S W k k′ d zero    L J 2≤S hk′ hL hLJ hd = ≤-refl
  fIterK≤fIterD S W k k′ d (suc m) L J 2≤S hk′ hL hLJ hd =
    ≤-trans (fIterK≤fIterD S W k k′ d m L (fLvlK S W k J) 2≤S hk′ hL
               (≤-trans hLJ (fLvlK-infl S W k J)) hd)
            (fIterD-mono m m d d k′ k′ 2≤S ≤-refl ≤-refl
               (fLvlK≤fLvlD S W k d J 2≤S
                  (≤-trans hL (s≤s (sizeAt-mono (≤-trans (s≤s z≤n) 2≤S) ≤-refl hLJ)))
                  hd)
               ≤-refl ≤-refl ≤-refl)

  -- the old family's inflation, needed by the domination above
  fLvlK-infl : ∀ (S W k J : ℕ) → J ≤ fLvlK S W k J
  fLvlK-infl S W k J =
    ≤-trans (m≤m+n J (fCharge S W J))
            (sIterK-infl S W k (suc (widAt S W J)) (fLvl S W J))

  sIterK-infl : ∀ (S W k m J : ℕ) → J ≤ sIterK S W k m J
  sIterK-infl S W k zero    J = ≤-refl
  sIterK-infl S W k (suc m) J =
    ≤-trans (≤-trans (n≤1+n J) (sLvlK-infl S W k (suc J)))
            (sIterK-infl S W k m (sLvlK S W k (suc J)))

  sLvlK-infl : ∀ (S W k J : ℕ) → J ≤ sLvlK S W k J
  sLvlK-infl S W zero    J = ≤-refl
  sLvlK-infl S W (suc k) J = opIterK-infl S W k (suc (sizeAt S J)) J

  opIterK-infl : ∀ (S W k m J : ℕ) → J ≤ opIterK S W k m J
  opIterK-infl S W k zero    J = ≤-refl
  opIterK-infl S W k (suc m) J =
    ≤-trans (≤-trans (≤-trans (n≤1+n J)
                              (s≤s (m≤m+n J (suc (sizeAt S J) * suc (sizeAt S J)))))
                     (≤-trans (sLvlK-infl S W k
                                 (suc (J + suc (sizeAt S J) * suc (sizeAt S J))))
                              (opIterK-infl S W k m
                                 (sLvlK S W k
                                    (suc (J + suc (sizeAt S J) * suc (sizeAt S J)))))))
            (fIterK-infl S W k
               (suc (widAt S W (opIterK S W k m
                       (sLvlK S W k
                          (suc (J + suc (sizeAt S J) * suc (sizeAt S J)))))))
               (opIterK S W k m
                  (sLvlK S W k (suc (J + suc (sizeAt S J) * suc (sizeAt S J))))))

  fIterK-infl : ∀ (S W k m J : ℕ) → J ≤ fIterK S W k m J
  fIterK-infl S W k zero    J = ≤-refl
  fIterK-infl S W k (suc m) J =
    ≤-trans (fLvlK-infl S W k J) (fIterK-infl S W k m (fLvlK S W k J))

-- the gate at the instantiation the walk actually uses: the old
-- per-frame level with the budget read at the frame's own level is under
-- the refreshed one at any depth fuel that covers it
fLvl′≤fLvlD : ∀ (S W d J : ℕ) → 2 ≤ S → suc (sizeAt S J) ≤ d →
  fLvlK S W (suc (sizeAt S J)) J ≤ fLvlD S W d J
fLvl′≤fLvlD S W d J 2≤S hd = fLvlK≤fLvlD S W (suc (sizeAt S J)) d J 2≤S ≤-refl hd

------------------------------------------------------------------
-- § 7  THE COMPOSITION GATE, RE-PROVEN.  Sub-Charge-Probe § 5's four
-- steps are the per-clause arithmetic the signature pass consumes; each
-- one goes through against the reshaped family with the depth fuel
-- carried unchanged, because none of them touches the budget's
-- instantiation — they compose receipts in the order the clauses run
-- them, and that order did not move.
--
-- ONE STEP IS NEW, and it is the one the refresh is FOR: `frame-step`.
-- A frame's payload walk no longer needs a nesting hypothesis handed
-- down from the subscribe that installed it — the frame reads its own
------------------------------------------------------------------

-- ONE PAYLOAD of a thruWalk / concatDrain
walk-step : ∀ (S W d k m j j₁ j₂ : ℕ) → 2 ≤ S →
  j + j₁ ≤ sLvlD S W d k (suc j) →
  (j + j₁) + j₂ ≤ sIterD S W d k m (j + j₁) →
  j + (j₁ + j₂) ≤ sIterD S W d k (suc m) j
walk-step S W d k m j j₁ j₂ 2≤S hd tl =
  ≤-trans (≤-trans (≤-reflexive (sym (+-assoc j j₁ j₂))) tl)
          (sIterD-mono m m d d k k 2≤S ≤-refl ≤-refl hd ≤-refl ≤-refl ≤-refl)

-- ONE FRAME, and this is the step the refresh buys: the frame's own
-- receipt (`fCharge`, what `scanFrame-caps` pays) and then its payload
-- walk under the budget READ HERE — no inherited k appears
frame-step : ∀ (S W d j j₀ j₁ : ℕ) → 2 ≤ S →
  j₀ ≤ fCharge S W j →
  (j + j₀) + j₁ ≤ sIterD S W d (suc (sizeAt S j)) (suc (widAt S W j)) (j + j₀) →
  j + (j₀ + j₁) ≤ fLvlD S W (suc d) j
frame-step S W d j j₀ j₁ 2≤S rcpt walk =
  ≤-trans (≤-trans (≤-reflexive (sym (+-assoc j j₀ j₁))) walk)
          (sIterD-mono (suc (widAt S W j)) (suc (widAt S W j)) d d
             (suc (sizeAt S j)) (suc (sizeAt S j)) 2≤S ≤-refl ≤-refl
             (+-monoʳ-≤ j rcpt) ≤-refl ≤-refl ≤-refl)

-- ONE OPERATOR, map / take / *All shape
op-step : ∀ (S W d k m j j₁ j₂ : ℕ) → 2 ≤ S →
  suc j + j₁ ≤ opIterD S W d k m (suc j) →
  (suc j + j₁) + j₂ ≤ fIterD S W d k (suc (widAt S W (suc j + j₁))) (suc j + j₁) →
  j + suc (j₁ + j₂) ≤ opIterD S W d k (suc m) j
op-step S W d k m j j₁ j₂ 2≤S src pb =
  ≤-trans (≤-trans (≤-reflexive (trans (+-suc j (j₁ + j₂))
                                       (cong suc (sym (+-assoc j j₁ j₂)))))
                   pb)
          (fIterD-mono (suc (widAt S W (suc j + j₁))) (suc (widAt S W X)) d d k k
             2≤S ≤-refl ≤-refl A≤X ≤-refl ≤-refl
             (s≤s (widAt-mono 2≤S ≤-refl ≤-refl A≤X)))
  where
  J₀ = suc (j + suc (sizeAt S j) * suc (sizeAt S j))
  X  = opIterD S W d k m (sLvlD S W d k J₀)
  sucj≤J₁ : suc j ≤ sLvlD S W d k J₀
  sucj≤J₁ = ≤-trans (s≤s (m≤m+n j (suc (sizeAt S j) * suc (sizeAt S j))))
                    (sLvlD-infl S W d k J₀)
  A≤X : suc j + j₁ ≤ X
  A≤X = ≤-trans src
          (opIterD-mono m m d d k k 2≤S ≤-refl ≤-refl sucj≤J₁ ≤-refl ≤-refl ≤-refl)

-- ONE OPERATOR, scan shape: an EVAL receipt first, then the same three
op-step-eval : ∀ (S W d k m j j₀ j₁ j₂ : ℕ) → 2 ≤ S →
  j₀ ≤ suc (sizeAt S j) →
  suc (j + j₀) + j₁ ≤ opIterD S W d k m (suc (j + j₀)) →
  (suc (j + j₀) + j₁) + j₂
    ≤ fIterD S W d k (suc (widAt S W (suc (j + j₀) + j₁))) (suc (j + j₀) + j₁) →
  j + (j₀ + suc (j₁ + j₂)) ≤ opIterD S W d k (suc m) j
op-step-eval S W d k m j j₀ j₁ j₂ 2≤S hj₀ src pb =
  ≤-trans (≤-trans (≤-reflexive (trans (sym (+-assoc j j₀ (suc (j₁ + j₂))))
                                  (trans (+-suc (j + j₀) (j₁ + j₂))
                                         (cong suc (sym (+-assoc (j + j₀) j₁ j₂))))))
                   pb)
          (fIterD-mono (suc (widAt S W (suc (j + j₀) + j₁))) (suc (widAt S W X)) d d k k
             2≤S ≤-refl ≤-refl A≤X ≤-refl ≤-refl
             (s≤s (widAt-mono 2≤S ≤-refl ≤-refl A≤X)))
  where
  J₀ = suc (j + suc (sizeAt S j) * suc (sizeAt S j))
  X  = opIterD S W d k m (sLvlD S W d k J₀)
  seed≤ : suc (j + j₀) ≤ sLvlD S W d k J₀
  seed≤ = ≤-trans (s≤s (+-monoʳ-≤ j
                    (≤-trans hj₀ (m≤m*n (suc (sizeAt S j)) (suc (sizeAt S j))))))
                  (sLvlD-infl S W d k J₀)
  A≤X : suc (j + j₀) + j₁ ≤ X
  A≤X = ≤-trans src
          (opIterD-mono m m d d k k 2≤S ≤-refl ≤-refl seed≤ ≤-refl ≤-refl ≤-refl)

-- B + suc (B · B) ≤ suc B · suc B — why the per-operator eval receipt is
-- a SQUARE
quad-arith : ∀ (B : ℕ) → B + suc (B * B) ≤ suc B * suc B
quad-arith B =
  ≤-trans (≤-reflexive (+-suc B (B * B)))
          (≤-trans (s≤s (+-monoʳ-≤ B (m≤n+m (B * B) B)))
                   (≤-reflexive (sym (cong (λ x → suc (B + x)) (*-suc B B)))))

-- THE μ OPERATOR: the unfolding receipt and then a FRESH subscribe on a
-- LARGER term, charged as one nesting level
op-step-mu : ∀ (S W d k m j m₀ j₁ : ℕ) → 2 ≤ S →
  m₀ ≤ sizeAt S j →
  (j + (m₀ + suc (m₀ * m₀))) + j₁ ≤ sLvlD S W d k (j + (m₀ + suc (m₀ * m₀))) →
  j + ((m₀ + suc (m₀ * m₀)) + j₁) ≤ opIterD S W d k (suc m) j
op-step-mu S W d k m j m₀ j₁ 2≤S hm₀ sub =
  ≤-trans (≤-trans (≤-reflexive (sym (+-assoc j (m₀ + suc (m₀ * m₀)) j₁))) sub)
          (≤-trans (sLvlD-mono d d k k 2≤S ≤-refl ≤-refl quad ≤-refl ≤-refl)
                   (≤-trans (opIterD-infl S W d k m (sLvlD S W d k J₀))
                            (fIterD-infl S W d k (suc (widAt S W X)) X)))
  where
  B  = sizeAt S j
  J₀ = suc (j + suc B * suc B)
  X  = opIterD S W d k m (sLvlD S W d k J₀)
  quad : j + (m₀ + suc (m₀ * m₀)) ≤ J₀
  quad = ≤-trans (+-monoʳ-≤ j (≤-trans (+-mono-≤ hm₀ (s≤s (*-mono-≤ hm₀ hm₀)))
                                       (quad-arith B)))
                 (n≤1+n (j + suc B * suc B))

------------------------------------------------------------------
-- § 8  WHAT IS STILL OPEN: the one number `d`.
--
-- Everything above is a function of (S, W, d, J).  The walk instantiates
-- the per-frame level as `fLvlD S W d J` and needs `d` ≥ the actual
-- subscribe-nesting DEPTH under that frame.  Three readings, and only
-- the third is not refuted or circular.
--
-- (1) READ IT OFF THE CAPS AT THE DELIVERY'S ENTRY — `d := suc (sizeAt S J)`.
--     REFUTED, by Worker 36's own witness, one stratum up.  Depth is
--     spent one unit per frame entry, and the payload a frame entry
--     descends into may be a MINT: at a frame the walk has climbed to,
--     `valsCaps?` admits nesting up to `sizeAt S J_deep`, and that is
--     the ONLY bound the invariant supplies there.  So the remaining
--     depth after one entry is bounded by a reading at the CLIMBED level,
--     which exceeds the entry reading for exactly the reason the nesting
--     budget did.  The refresh moves the problem from the budget to the
--     fuel; it does not remove it.
--
--     The rows: at S = 2, W = 1, J = 0 the entry reading is 3, one
--     nesting level in the chain already runs at `fLvl 2 1 0 = 7`, and
--     `sizeAt 2 7 = 43690` (Nest-Budget-Probe § 3a).  Nothing at that
--     site reports anything smaller.
--
-- (2) READ IT OFF THE WIDTH — `d := suc (widAt S W J)`.  Same refutation,
--     same rows: `widAt` is read at the entry too, and § 3a's last block
--     is the demonstration that the room between an entry reading and a
--     climbed one is USED rather than merely allowed.
--
-- (3) TAKE IT FROM THE EVALUATOR'S OWN FUEL.  `subscribeInner g0 … =
--     … close drySource dried ∷ [] …` — a subscribe with no gas returns
--     a dry burst and installs nothing.  So the subscribe-nesting depth
--     is bounded by the `Gas` argument that `subscribeE` (hence
--     `subscribeE-caps`) ALREADY carries, and `d :=` its height owes no
--     new invariant at all: the induction is on the evaluator's own
--     recursion.
--
--     THE COST IS A CYCLE, and it is worth stating exactly, because it
--     is what the ruling has to break:
--
--        budgetAt e sl id = syncBudget (sizeᵉ e + slotsSize sl) (capsBase e sl) id
--        syncBudget sz m id = gasPad (2 ^ (sz * suc id * suc id))
--                                    (gasTower (3 + capsHgo m (suc id)))
--        capsHgo m (suc id) = blowH (capsHgo m id)
--        blowH m            = 6 + m + 2 * poolCount (towerℕ m)
--        poolBody M         = lvls M M 0 (dCapᶜ M M M (suc M) 0)
--        lvls  → dLvl → iterL → fLvl′        ← the level the fuel feeds
--
--     so threading the gas HEIGHT into the level makes `poolCount`
--     depend on `budgetAt` and `budgetAt` depend on `poolCount`.  The two
--     ways out are both rulings: STRATIFY (instantiate d at a
--     program-static quantity the gas provably dominates — `gasPad`'s own
--     `2 ^ (sz * suc id * suc id)` is the only factor of `budgetAt` that
--     does not run through `poolCount`, but the gas is pad PLUS tower and
--     the depth is bounded by the sum, not by the pad), or take Worker
--     36's candidate 2 and move the whole accounting to INSTANT
--     boundaries, where a subscribe's nesting is bounded by what the
--     instant admits rather than by what a frame reads.
--
--     Reported, not chosen: the shape above is neutral between them —
--     § 3-§ 7 hold for EVERY d, and § 6's gate says the reshape sits
--     above the family it replaces at any d that covers the old budget
------------------------------------------------------------------

-- the rows § 8 (1) reads, restated here so the refutation of the DEPTH
-- fuel is on the page beside the family it refutes
_ : suc (sizeAt 2 0) ≡ 3
_ = refl

_ : fLvl 2 1 0 ≡ 7
_ = refl

_ : sizeAt 2 7 ≡ 43690
_ = refl

_ : (suc (sizeAt 2 7) ≤ᵇ suc (sizeAt 2 0)) ≡ false
_ = refl
