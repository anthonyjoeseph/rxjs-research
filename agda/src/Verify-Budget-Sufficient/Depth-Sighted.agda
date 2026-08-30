-- THE SUBSCRIBE-SIDE CEILING, and the induction that carries it.  The
-- statement is one file's worth of subject matter: a descent measured
-- against what the subscribing state can see.  Its shape, what is
-- traded at each edge and what the size factor buys are argued at the
-- assembly below; the leaves above it are the clauses that argument
-- does not close.
module Verify-Budget-Sufficient.Depth-Sighted where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _⊔_; _≤_; z≤n)
open import Data.Nat.Properties using (≤-trans; ≤-refl; ≤-reflexive; ⊔-lub; +-assoc; +-comm;
  *-mono-≤; *-monoˡ-≤; ^-monoʳ-≤; +-mono-≤; +-monoʳ-≤; +-monoˡ-≤; m≤n+m; m≤m+n; n≤1+n; m⊔n≤m+n;
  *-distribˡ-+; +-identityʳ; <ᵇ⇒<)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; con)
open import Data.Bool using (Bool; false; T; _∧_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (nothing)
open import Data.Fin using (toℕ)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; cong₂; trans; sym; refl; subst)

open import Rx.Exp using (Ctx; Closed; Fn; Val; obs; sizeᵉ; syncSizeᵉ; syncSizeᵗ; evalTm; unfoldμ; ofᵉ; emptyᵉ; deferᵉ; μᵉ; varᵉ;
  input; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; inputsBelowᵉ; inputsBelowᵗ)
open import Rx.Slots using (scripted; shared)
open import Rx.Inputs-Below using (ib-unfoldμ)
open import Decide using (∧ʳ)
open import Rx.Prim using (Gas; g0; gs; Id; Tick)
open import Rx.Evaluator using (Sched; EvalSt; Path; Frame; Stream; map-f; take-f; _↠_; subscribeE;
  mintNode; installNode; register; take-st; scan-st; scan-f; share-sink;
  AllOp; mergeAllᵒ; switchᵒ; exhaustᵒ; NodeState; mergeAll-st; switch-st; exhaust-st)
open import Rx.Nest-Depth using (nestDᵉ; nestDᵗ)
open import Verify-Budget-Sufficient.Caps-Depth using (depthE; depthBurst; depthAll; depthFrame)
open import Verify-Budget-Sufficient.Measures using (syncSize-unfoldμ)
open import Verify-Budget-Sufficient.Nest-Subst using (nestD-unfoldμ; evalTm-nest-sync)
open import Verify-Budget-Sufficient.Nest-Store using
  (pathNestD; sightCeil; sightCeil-mono; sightCeil-sum; storeNestMax;
   storeNestMax-install; storeNestMax-register; nestUnit; nodeNest;
   slotWrap; slotWrapSum; slotWrap≤sum)

-- WHAT THE SUBSCRIBING STATE CAN SEE, named once so the clauses below
-- read as the trade rather than as four arguments.
--
-- THE TRADED SUM IS SCALED, by the SUBJECT's sync size, and the choice
-- of which sync size is what makes the induction go through.  It is
-- scaled at all because the two clauses that BUILD a value -- a scan's
-- seed and a map frame's payload -- pay for what they build once per
-- OCCURRENCE of the syntax that builds it, which is the shape this
-- tree proves and the shape an additive charge is refuted at; a
-- summand of slack cannot meet a factor, and a scaled summand can.
--
-- AND THE SUBJECT'S IS THE ONE THAT MOVES THE RIGHT WAY.  Every
-- structural descent shrinks the sync size while the traded sum stays
-- put, so each clause gets its exponent for free and the spare factor
-- the built value needs is exactly the head's own `suc`.  Reading the
-- PROGRAM's sync size instead would leave the exponent constant along
-- the walk -- tidier at each edge, and then no clause has any room at
-- all, since nothing relates a subterm's sync size to the program's
-- without an invariant the statement does not carry.
Sight : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u} →
  ℕ → Closed Γ u → Path Γ u t → Sched Γ → EvalSt e → ℕ
Sight {e = e} k b κ sched st =
  sightCeil (sizeᵉ e) (2 ^ syncSizeᵉ b * (pathNestD κ + nestDᵉ b)
                        + k * slotWrapSum (Sched.slots sched))
            (storeNestMax sched st) (nestUnit e (Sched.slots sched))

-- A CHAIN FRAME COSTS THE BURST NOTHING, and the three heads that mint a
-- node are chain frames.  A `map`, a `scan` and a `take` transform in
-- place: they push no story, so `depthFrame` is flatly zero at each of
-- them, and a burst is a fold of `depthFrame` over the emitted stream
-- with the state threaded through.  The threading is why this is an
-- induction rather than a computation -- every element is read at a
-- state the one before it produced -- and it is why the hypothesis
-- quantifies over the state rather than fixing it.
burst-flat : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (g : Gas) (bid : Id) (now : Tick) (f : Frame Γ s u) (κ : Path Γ u t) →
  (∀ (vals : List (Val Γ s)) (fin : Bool) (sch : Sched Γ) (sto : EvalSt e) →
     depthFrame g bid now f κ vals fin sch sto ≡ 0) →
  ∀ (ems : Stream Γ s) (sched : Sched Γ) (st : EvalSt e) →
  depthBurst g bid now f κ ems sched st ≡ 0
burst-flat g bid now f κ h []         sched st = refl
burst-flat g bid now f κ h (em ∷ ems) sched st =
  cong₂ _⊔_ (h _ _ sched st) (burst-flat g bid now f κ h ems _ _)

-- MOVING A CONSTANT SUMMAND ACROSS A TRADED SUM, which is what every
-- clause below needs once the ceiling's subject place carries a term
-- the step does not move: the trade is stated on the two places that
-- DO move, and the constant rides along.
shuffle : ∀ (a c s b s′ : ℕ) → a + s ≤ b + s′ → (a + c) + s ≤ (b + c) + s′
shuffle a c s b s′ h =
  ≤-trans (≤-reflexive (swap a c s))
          (≤-trans (+-monoˡ-≤ c h) (≤-reflexive (sym (swap b c s′))))
  where
  swap : ∀ (x y z : ℕ) → (x + y) + z ≡ (x + z) + y
  swap = solve 3 (λ x y z → (x :+ y) :+ z := (x :+ z) :+ y) refl

-- THE DRAIN, and it is ONE leaf for the three heads rather than three:
-- all of them delegate to `depthAll`, all of them wrap the subject in
-- exactly one nesting level, and none of them is distinguished by
-- anything the bound reads.  The payload subscribe under it is the one
-- descent that charges the path nothing, so this is where the size
-- factor is spent, and it is the head every program in the corpus wears
-- at its root.
--
-- PROBED: `Probed.Depth-Sighted` reads the assembly at `root`, where
--   this head is the one it lands on, at fold depths two and twenty:
--   descents of nine and eighty-one against ceilings of eleven and
--   thirty-four decimal digits.  On the family whose mergeAll is
--   unbounded, five against eleven digits; under the vocabulary that
--   connects at once rather than late, four against nineteen.  The
--   margin is the scale factor and it outruns every axis the corpus
--   moves.  Not covered: any `sl` past the two-slot vocabularies, which
--   is where both remaining families are; every path other than `root`,
--   which is the whole of what generalising added; and the two heads
--   other than `mergeAllᵉ`, which no row reaches.
postulate
  sight-all : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (k : ℕ) (op : AllOp) (ist : NodeState Γ) (b : Closed Γ (obs u))
    (κ : Path Γ u t) (bid : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    T (inputsBelowᵉ k b) →
    depthAll g op ist b κ bid now sched st
      ≤ sightCeil (sizeᵉ e) (2 ^ suc (syncSizeᵉ b) * (pathNestD κ + suc (nestDᵉ b))
                              + k * slotWrapSum (Sched.slots sched))
                  (storeNestMax sched st) (nestUnit e (Sched.slots sched))

-- ANY SUBSCRIBE'S DESCENT AGAINST WHAT IT CAN SEE, which is the
-- statement the induction is actually over.  A sweep crosses
-- `thru-outer` frames and drains bounded mergeAlls, and both are paid
-- for out of structure it already has: the subject it is descending,
-- the path it has built, the store it walks, and the program's own
-- wrap unit.  The entry claim is this at `root`, where the path
-- charges nothing and the two readings of the subject coincide.
--
-- THE SUBJECT AND THE PATH ARE ONE QUANTITY, and stating it that way
-- is the whole reason this form can be induced on.  Every structural
-- descent TRADES: a `map` moves its function's nesting off the subject
-- and onto the frame it pushes, a `*All` moves its own wrap `suc` the
-- same way, and a `scan` moves less than it drops.  So `pathNestD κ +
-- nestDᵉ b` is non-increasing along the walk while neither summand is,
-- and a bound stated on either alone has to be re-established at every
-- edge.
--
-- WHAT THE SIZE FACTOR PAYS FOR IS THE ONE DESCENT THAT DOES NOT
-- TRADE.  A drain runs under a `from-inner`, which the path measure
-- charges nothing for -- deliberately, since the layer it would charge
-- is the one the `thru-outer` above it already bought -- so a program
-- whose folds nest spends one per layer against a sum that sees none
-- of them.  The layers are bounded by the program, which is why the
-- size enters as a FACTOR rather than a summand: as a summand it is
-- outrun, one per delivered value against the descent's eight.
--
-- REFUTED: `Refuted.Nest-Depth-One` is the subscribe-side witness the
--   ceiling is calibrated against -- a limit-one mergeAll over three
--   queued inners under nested folds, read at the root subscribe, whose
--   descent climbs four per fold layer against the bare sum's three.
depthE-sighted : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (g : Gas) (k : ℕ) (b : Closed Γ u) (κ : Path Γ u t) (bid : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) → T (inputsBelowᵉ k b) →
  depthE g b κ bid now sched st ≤ Sight k b κ sched st
depthE-sighted g0 k (input i) κ bid now sched st ok
  with Sched.slots sched i
... | scripted _ = z≤n
... | shared d   = z≤n
depthE-sighted {e = e} (gs g) k (input i) κ bid now sched st ok
  with Sched.slots sched i in eqsl
... | scripted _        = z≤n
... | shared d {okd} =
  ≤-trans (depthE-sighted g (toℕ i) d (share-sink i) bid now sched st₁ okd)
          (sightCeil-sum (sizeᵉ e)
            (2 ^ syncSizeᵉ d * (0 + nestDᵉ d) + toℕ i * W)
            (storeNestMax sched st₁)
            (2 ^ 1 * (pathNestD κ + 0) + k * W)
            (storeNestMax sched st) (nestUnit e (Sched.slots sched)) step)
  where
  W  = slotWrapSum (Sched.slots sched)
  st₁ = register (toℕ i) κ
          (record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st })
  wrap≤ : 2 ^ syncSizeᵉ d * (0 + nestDᵉ d) ≤ W
  wrap≤ = subst (λ w → slotWrap w ≤ W) eqsl (slotWrap≤sum (Sched.slots sched) i)
  strat : suc (toℕ i) * W ≤ k * W
  strat = *-monoˡ-≤ W (<ᵇ⇒< (toℕ i) k ok)
  store≤ : storeNestMax sched st₁ ≤ pathNestD κ + storeNestMax sched st
  store≤ = ≤-trans (storeNestMax-register (toℕ i) κ sched
                     (record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st }))
                   (m⊔n≤m+n (pathNestD κ) (storeNestMax sched st))
  head≥ : pathNestD κ ≤ 2 ^ 1 * (pathNestD κ + 0)
  head≥ = ≤-trans (≤-reflexive (sym (+-identityʳ (pathNestD κ))))
                  (m≤m+n (pathNestD κ + 0) (pathNestD κ + 0 + 0))
  step : (2 ^ syncSizeᵉ d * (0 + nestDᵉ d) + toℕ i * W) + storeNestMax sched st₁
           ≤ (2 ^ 1 * (pathNestD κ + 0) + k * W) + storeNestMax sched st
  step =
    ≤-trans (+-mono-≤ (+-monoˡ-≤ (toℕ i * W) wrap≤) store≤)
    (≤-trans (+-monoˡ-≤ (pathNestD κ + storeNestMax sched st) strat)
    (≤-trans (≤-reflexive (sym (+-assoc (k * W) (pathNestD κ) (storeNestMax sched st))))
             (+-monoˡ-≤ (storeNestMax sched st)
               (≤-trans (+-monoʳ-≤ (k * W) head≥)
                        (≤-reflexive (+-comm (k * W) (2 ^ 1 * (pathNestD κ + 0))))))))
depthE-sighted g k (ofᵉ ts)           κ bid now sched st ok = z≤n
depthE-sighted g k emptyᵉ             κ bid now sched st ok = z≤n
depthE-sighted g k (deferᵉ b)         κ bid now sched st ok = z≤n
depthE-sighted g0 k (μᵉ body)         κ bid now sched st ok = z≤n
-- THE UNFOLD, which is the one descent whose subject is not a subterm
-- -- and it costs nothing, because both readings of the measure are
-- INVARIANT under the substitution: the copy a `μ` plants carries the
-- body's own nesting and the body's own sync size, and the head it
-- replaces charged a `suc` on top of each.
depthE-sighted {e = e} (gs g) k (μᵉ body) κ bid now sched st ok =
  ≤-trans (depthE-sighted g k (unfoldμ body) κ bid now sched st
             (ib-unfoldμ k body ok))
          (sightCeil-mono (sizeᵉ e) (nestUnit e (Sched.slots sched))
            (+-monoˡ-≤ (k * slotWrapSum (Sched.slots sched))
              (*-mono-≤ (^-monoʳ-≤ 2 (≤-trans (≤-reflexive (syncSize-unfoldμ body))
                                              (n≤1+n _)))
                        (+-monoʳ-≤ (pathNestD κ)
                                   (≤-reflexive (nestD-unfoldμ body)))))
            ≤-refl)
depthE-sighted g k (varᵉ ())        κ bid now sched st ok
-- THE SCAN, whose descent half IS the trade and whose store transport is
-- what the scale factor was minted for.  The trade is generous -- the
-- seed's and the function's nesting come off the subject and only the
-- function's goes onto the frame -- but the store takes the seed's back,
-- because the node a scan installs holds the EVALUATED seed and the
-- ceiling reads the store beside the measure.  So the two sides are
-- compared as one sum, and the spare the head's own `suc` buys is spent
-- on an evaluated seed's per-occurrence bound.
--
-- AND PER-OCCURRENCE IS THE ONLY BOUND AVAILABLE.  A closed term still
-- BINDS, and a branch may name what was bound on both sides of a sum
-- the observable measure takes, so an evaluated seed can outnest the
-- term that built it.
--
-- REFUTED: `Refuted.Eval-Seed-Nest` is the witness -- a `caseᵗ` whose
--   left branch names its bound observable both as a fold's SEED and
--   inside the source that fold runs over, weighing three against a
--   term that charges two, with the gap growing as the occurrence
--   count.  `Refuted.Apply-Fn-Nest` is the same failure with an
--   explicit payload rather than an empty environment.
depthE-sighted {e = e} g k (scanᵉ f z b) κ bid now sched st ok =
  ⊔-lub (≤-trans (depthE-sighted g k b (scan-f f nid ↠ κ) bid now sched₁ st₀
                    (∧ʳ (inputsBelowᵗ k z) (inputsBelowᵉ k b)
                        (∧ʳ (inputsBelowᵗ k f)
                            (inputsBelowᵗ k z ∧ inputsBelowᵉ k b) ok)))
                 (sightCeil-sum (sizeᵉ e) (2 ^ syncSizeᵉ b * A + k * W)
                   (storeNestMax sched₁ st₀)
                   (2 ^ K * (pathNestD κ + nestDᵉ (scanᵉ f z b)) + k * W) sR
                   (nestUnit e (Sched.slots sched)) hsum′))
        (≤-trans (≤-reflexive (burst-flat g bid now (scan-f f nid) κ
                                 (λ _ _ _ _ → refl)
                                 (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)))) z≤n)
  where
  nid    = proj₁ (mintNode sched)
  sched₁ = proj₂ (mintNode sched)
  st₀    = installNode nid (scan-st (evalTm z)) st
  r      = subscribeE g b (scan-f f nid ↠ κ) bid now sched₁ st₀
  K      = syncSizeᵉ (scanᵉ f z b)
  W      = slotWrapSum (Sched.slots sched)
  A      = nestDᵗ f + pathNestD κ + nestDᵉ b
  NV     = nodeNest (scan-st (evalTm z))
  sR     = storeNestMax sched st
  z≤K : syncSizeᵗ z ≤ K
  z≤K = ≤-trans (m≤n+m (syncSizeᵗ z) (syncSizeᵗ f))
                (≤-trans (m≤m+n _ (syncSizeᵉ b)) (n≤1+n _))
  b≤K : syncSizeᵉ b ≤ K
  b≤K = ≤-trans (m≤n+m (syncSizeᵉ b) _) (n≤1+n _)
  hNV : NV ≤ 2 ^ K * nestDᵗ z
  hNV = ≤-trans (evalTm-nest-sync z) (*-monoˡ-≤ (nestDᵗ z) (^-monoʳ-≤ 2 z≤K))
  eqv : 2 ^ K * A + 2 ^ K * nestDᵗ z ≡ 2 ^ K * (pathNestD κ + nestDᵉ (scanᵉ f z b))
  eqv = trans (sym (*-distribˡ-+ (2 ^ K) A (nestDᵗ z)))
              (cong (2 ^ K *_)
                (solve 4 (λ x y w v → (x :+ y :+ w) :+ v := y :+ (v :+ x :+ w))
                       refl (nestDᵗ f) (pathNestD κ) (nestDᵉ b) (nestDᵗ z)))
  hv : 2 ^ syncSizeᵉ b * A + NV
         ≤ 2 ^ K * (pathNestD κ + nestDᵉ (scanᵉ f z b))
  hv = ≤-trans (+-mono-≤ (*-monoˡ-≤ A (^-monoʳ-≤ 2 b≤K)) hNV)
               (≤-reflexive eqv)
  hsum : 2 ^ syncSizeᵉ b * (pathNestD (scan-f f nid ↠ κ) + nestDᵉ b)
           + storeNestMax sched₁ st₀
           ≤ 2 ^ K * (pathNestD κ + nestDᵉ (scanᵉ f z b)) + sR
  hsum =
    ≤-trans (+-monoʳ-≤ (2 ^ syncSizeᵉ b * A)
              (≤-trans (storeNestMax-install nid (scan-st (evalTm z)) sched₁ st)
                       (m⊔n≤m+n NV sR)))
            (≤-trans (≤-reflexive (sym (+-assoc (2 ^ syncSizeᵉ b * A) NV sR)))
                     (+-monoˡ-≤ sR hv))
  hsum′ : (2 ^ syncSizeᵉ b * (pathNestD (scan-f f nid ↠ κ) + nestDᵉ b) + k * W)
            + storeNestMax sched₁ st₀
            ≤ (2 ^ K * (pathNestD κ + nestDᵉ (scanᵉ f z b)) + k * W) + sR
  hsum′ = shuffle (2 ^ syncSizeᵉ b * (pathNestD (scan-f f nid ↠ κ) + nestDᵉ b))
                  (k * W) (storeNestMax sched₁ st₀)
                  (2 ^ K * (pathNestD κ + nestDᵉ (scanᵉ f z b))) sR hsum
depthE-sighted {u = u} g k (mergeAllᵉ lim b) κ bid now sched st ok =
  sight-all g k mergeAllᵒ (mergeAll-st {t = u} lim 0 [] false) b κ bid now sched st ok
depthE-sighted g k (switchAllᵉ b)   κ bid now sched st ok =
  sight-all g k switchᵒ (switch-st nothing false) b κ bid now sched st ok
depthE-sighted g k (exhaustAllᵉ b)  κ bid now sched st ok =
  sight-all g k exhaustᵒ (exhaust-st false false) b κ bid now sched st ok
-- THE TAKE, whose descent half costs nothing on either side of the
-- trade: a take charges the path nothing and drops the subject nothing,
-- and the node it installs carries no nesting at all, so the reading the
-- recursive call gets is the reading this call was handed.  What is left
-- of the clause is its burst.
depthE-sighted {e = e} g k (takeᵉ c b) κ bid now sched st ok
  with evalTm c
... | zero  = z≤n
... | suc m =
  ⊔-lub (≤-trans (depthE-sighted g k b (take-f nid ↠ κ) bid now sched₁ st₀
                    (∧ʳ (inputsBelowᵗ k c) (inputsBelowᵉ k b) ok))
                 (sightCeil-mono (sizeᵉ e) (nestUnit e (Sched.slots sched))
                   (+-monoˡ-≤ (k * slotWrapSum (Sched.slots sched))
                     (*-monoˡ-≤ (pathNestD κ + nestDᵉ b)
                       (^-monoʳ-≤ 2 (≤-trans (m≤n+m (syncSizeᵉ b) (syncSizeᵗ c))
                                             (n≤1+n _)))))
                   (≤-trans (storeNestMax-install nid (take-st (suc m)) sched₁ st)
                            (⊔-lub z≤n ≤-refl))))
        (≤-trans (≤-reflexive (burst-flat g bid now (take-f nid) κ
                                 (λ _ _ _ _ → refl)
                                 (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)))) z≤n)
  where
  nid    = proj₁ (mintNode sched)
  sched₁ = proj₂ (mintNode sched)
  st₀    = installNode nid (take-st (suc m)) st
  r      = subscribeE g b (take-f nid ↠ κ) bid now sched₁ st₀

-- THE ONE CLAUSE THAT IS THE TRADE ITSELF, and it needs no store
-- transport: a map mints nothing, so the state the recursive call reads
-- is the state this call was handed.  The whole step is the charge
-- moving off the subject and onto the frame, which is an associativity
-- and a commutativity on the measure and nothing else.
depthE-sighted {e = e} g k (mapᵉ f b) κ bid now sched st ok =
  ⊔-lub (≤-trans (depthE-sighted g k b (map-f f ↠ κ) bid now sched st
                    (∧ʳ (inputsBelowᵗ k f) (inputsBelowᵉ k b) ok))
                 (sightCeil-mono (sizeᵉ e) (nestUnit e (Sched.slots sched))
                   (+-monoˡ-≤ (k * slotWrapSum (Sched.slots sched))
                     (*-mono-≤ (^-monoʳ-≤ 2 (≤-trans (m≤n+m (syncSizeᵉ b) (syncSizeᵗ f))
                                                     (n≤1+n _)))
                               (≤-reflexive (trade f b κ))))
                   ≤-refl))
        (≤-trans (≤-reflexive (burst-flat g bid now (map-f f) κ
                                 (λ _ _ _ _ → refl)
                                 (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)))) z≤n)
  where
  r = subscribeE g b (map-f f ↠ κ) bid now sched st
  trade : ∀ {s u} (f : Fn _ [] [] [] s u) (b : Closed _ s) (κ : Path _ u _) →
    pathNestD (map-f f ↠ κ) + nestDᵉ b ≡ pathNestD κ + nestDᵉ (mapᵉ f b)
  trade f b κ = trans (cong (_+ nestDᵉ b) (+-comm (nestDᵗ f) (pathNestD κ)))
                      (+-assoc (pathNestD κ) (nestDᵗ f) (nestDᵉ b))
