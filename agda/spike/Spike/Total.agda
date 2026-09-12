------------------------------------------------------------------
-- THE ORDER DISCHARGES THE DOMAIN — no gas, no caps, no tower.
--
-- `Spike.Order` refuted the syntax-directed scan clause, so this
-- module works the fragment that survives: `Spike.Mini` minus `scanᵉ`.
-- It is written out rather than carved out of Mini by a hereditary
-- `Refoldless` predicate, because preserving such a predicate across
-- `run` is itself an induction mutual with the ind-rec block, and it
-- would be apparatus about the carve-out rather than about the claim.
--
-- TWO CLAIMS, and the second is the one the whole detour was for.
--
-- `emit-hop`: every value a subscription emits has hop depth at most
-- its emitter's, and the proof reads NO size bound, NO store invariant
-- and NO cap.  That is the conjunct the inner-hop edge needs, and in
-- the real development it is what the `(2 + pm)^V` scan clause and the
-- caps tower behind `V` are paying for.  Here it costs three
-- congruences and a sub-induction on the template.  It costs so little
-- because the statement quantifies over the ACTUAL burst and bounds it
-- by the emitter's own hop: nothing predicts, so nothing needs a cap
-- to predict with.  A gas budget must be fixed before the run starts
-- and is therefore forced to predict; that is where `V` enters, not
-- from anything the semantics needs.
--
-- `total`: every expression is in the domain, by well-founded
-- induction on the lexicographic triple
--
--     (unconn cs , hopD e , syncSize e)
--
-- read as a genuine lex order rather than positionally encoded.  The
-- carry conditions the encoded form needs — a hop edge's `s′ ≤ V`, a
-- connect edge's `r′ ≤ R` and `s′ ≤ V` — are absent, because a lex
-- order has no digits to carry between.  Nothing in this file computes
-- a budget, and the only quantity any clause reads is one the
-- expression already carries.
--
-- The delicate step is `dAll`: its witness must be built from a burst
-- that only exists once its own first field has been applied to `run`.
-- `total` does exactly that, and Agda accepts it.
--
-- Two simplifications, both faithful rather than convenient.  The
-- recursive occurrence is a single constructor `recᵉ` unfolding to
-- `deferᵉ (μᵉ b)`, because the real language's `μᵉ` binds into the
-- guarded context and `deferᵉ` is its sole gate — a recursive
-- occurrence is a gated one by typing, and collapsing the two makes
-- that structural instead of a side condition.  And the slot-hop
-- environment `η` is a parameter satisfying `hopD (def i) ≤ η i`,
-- which is `Rx.Slot-Hop`'s `slotHop-fix` taken as given: it is proven
-- there by recursion on the slot index, and re-proving it here would
-- test the telescope's stratification rather than the order.
------------------------------------------------------------------
module Spike.Total where

open import Level using (0ℓ)
open import Data.Nat  using (ℕ; zero; suc; _+_; _⊔_; _≤_; _<_; _<?_; z≤n; s≤s; _≡ᵇ_)
open import Data.Nat.Properties using
  ( ≤-refl; ≤-trans; ≤-reflexive; n≤1+n; +-suc
  ; m≤m+n; m≤n+m; m≤m⊔n; m≤n⊔m; ⊔-lub
  ; +-monoʳ-≤
  ; m≤n⇒m<n∨m≡n; m<1+n⇒m<n∨m≡n )
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Any.Properties using (++⁻)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Product.Relation.Binary.Lex.Strict using (×-Lex; ×-wellFounded)
open import Induction.WellFounded using (Acc; acc; WellFounded)
open import Relation.Binary using (Rel)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂)

------------------------------------------------------------------
-- THE LANGUAGE — Mini without `scanᵉ`, and with the gate folded into
-- the recursive occurrence.
------------------------------------------------------------------

data Val : Set
data Exp : Set
data Tm  : Set

data Val where
  natᵛ : ℕ → Val
  obsᵛ : Exp → Val

data Tm where
  inᵗ    : Tm
  konstᵗ : Val → Tm
  nestᵗ  : Tm → Tm

data Exp where
  ofᵉ    : List Val → Exp
  mapᵉ   : Tm → Exp → Exp
  allᵉ   : Exp → Exp
  μᵉ     : Exp → Exp
  recᵉ   : Exp
  deferᵉ : Exp → Exp
  slotᵉ  : ℕ → Exp

evalTm : Tm → Val → Val
evalTm inᵗ        v = v
evalTm (konstᵗ k) v = k
evalTm (nestᵗ t)  v = obsᵛ (allᵉ (ofᵉ (evalTm t v ∷ [])))

mapB : Tm → List Val → List Val
mapB f []       = []
mapB f (v ∷ vs) = evalTm f v ∷ mapB f vs

------------------------------------------------------------------
-- THE UNFOLD.  `recᵉ` becomes a GATED copy, which is why the unfold
-- costs nothing in hop and strictly decreases synchronous size.
------------------------------------------------------------------

substE : Exp → Exp → Exp
substV : Val → Exp → Val
substL : List Val → Exp → List Val
substT : Tm → Exp → Tm

substE (ofᵉ vs)   m = ofᵉ (substL vs m)
substE (mapᵉ f e) m = mapᵉ (substT f m) (substE e m)
substE (allᵉ e)   m = allᵉ (substE e m)
substE (μᵉ b)     m = μᵉ b
substE recᵉ       m = deferᵉ m
substE (deferᵉ b) m = deferᵉ b
substE (slotᵉ i)  m = slotᵉ i

substV (natᵛ n) m = natᵛ n
substV (obsᵛ e) m = obsᵛ (substE e m)

substL []       m = []
substL (v ∷ vs) m = substV v m ∷ substL vs m

substT inᵗ        m = inᵗ
substT (konstᵗ k) m = konstᵗ (substV k m)
substT (nestᵗ t)  m = nestᵗ (substT t m)

unfoldμ : Exp → Exp
unfoldμ b = substE b (μᵉ b)

------------------------------------------------------------------
-- THE MEASURE'S TWO EXPRESSION COMPONENTS.  `η` is the slot-hop
-- environment; no clause of either reads a cap.
------------------------------------------------------------------

hopDv : (ℕ → ℕ) → Val → ℕ
hopD  : (ℕ → ℕ) → Exp → ℕ
hopDt : (ℕ → ℕ) → Tm  → ℕ
hopDl : (ℕ → ℕ) → List Val → ℕ

hopDv η (natᵛ n) = 0
hopDv η (obsᵛ e) = hopD η e

hopDl η []       = 0
hopDl η (v ∷ vs) = hopDv η v ⊔ hopDl η vs

hopDt η inᵗ        = 0
hopDt η (konstᵗ k) = hopDv η k
hopDt η (nestᵗ t)  = suc (hopDt η t)

hopD η (ofᵉ vs)   = hopDl η vs
hopD η (mapᵉ f e) = hopDt η f + hopD η e
hopD η (allᵉ e)   = suc (hopD η e)
hopD η (μᵉ b)     = hopD η b
hopD η recᵉ       = 0
hopD η (deferᵉ b) = 0
hopD η (slotᵉ i)  = η i

syncSize : Exp → ℕ
syncSize (ofᵉ vs)   = 1
syncSize (mapᵉ f e) = suc (syncSize e)
syncSize (allᵉ e)   = suc (syncSize e)
syncSize (μᵉ b)     = suc (syncSize b)
syncSize recᵉ       = 1
syncSize (deferᵉ b) = 1
syncSize (slotᵉ i)  = 1

------------------------------------------------------------------
-- THE UNFOLD IS HOP-NEUTRAL AND SIZE-NEUTRAL, structurally: every
-- substitution point is a `recᵉ`, and it becomes a `deferᵉ`, which
-- both measures read exactly as they read a `recᵉ`.
------------------------------------------------------------------

hopD-subst  : ∀ η b m → hopD η (substE b m) ≡ hopD η b
hopDv-subst : ∀ η v m → hopDv η (substV v m) ≡ hopDv η v
hopDl-subst : ∀ η vs m → hopDl η (substL vs m) ≡ hopDl η vs
hopDt-subst : ∀ η f m → hopDt η (substT f m) ≡ hopDt η f

hopD-subst η (ofᵉ vs)   m = hopDl-subst η vs m
hopD-subst η (mapᵉ f e) m =
  cong₂ _+_ (hopDt-subst η f m) (hopD-subst η e m)
hopD-subst η (allᵉ e)   m = cong suc (hopD-subst η e m)
hopD-subst η (μᵉ b)     m = refl
hopD-subst η recᵉ       m = refl
hopD-subst η (deferᵉ b) m = refl
hopD-subst η (slotᵉ i)  m = refl

hopDv-subst η (natᵛ n) m = refl
hopDv-subst η (obsᵛ e) m = hopD-subst η e m

hopDl-subst η []       m = refl
hopDl-subst η (v ∷ vs) m = cong₂ _⊔_ (hopDv-subst η v m) (hopDl-subst η vs m)

hopDt-subst η inᵗ        m = refl
hopDt-subst η (konstᵗ k) m = hopDv-subst η k m
hopDt-subst η (nestᵗ t)  m = cong suc (hopDt-subst η t m)

syncSize-subst : ∀ b m → syncSize (substE b m) ≡ syncSize b
syncSize-subst (ofᵉ vs)   m = refl
syncSize-subst (mapᵉ f e) m = cong suc (syncSize-subst e m)
syncSize-subst (allᵉ e)   m = cong suc (syncSize-subst e m)
syncSize-subst (μᵉ b)     m = refl
syncSize-subst recᵉ       m = refl
syncSize-subst (deferᵉ b) m = refl
syncSize-subst (slotᵉ i)  m = refl

------------------------------------------------------------------
-- THE TEMPLATE BOUND IS ADDITIVE HERE, AND THAT IS A PROPERTY OF THIS
-- FRAGMENT AND NOT OF DEPTH.  A template applied to a value of hop `h`
-- produces one of hop at most `hopDt f + h` — precisely the `mapᵉ`
-- clause, with no multiplier — and the reason is that `Tm` above can
-- mention its argument AT MOST ONCE.  Every template expressible here
-- therefore has plug slope 1, so a multiplier would be vacuous, and a
-- fragment in which a law is vacuous says nothing about a language in
-- which it is not.
--
-- READ IT THE OTHER WAY AND IT IS FALSE.  A template whose argument
-- reaches two ADDED positions — an inner map's template and that same
-- map's source — has slope 2, and the additive clause then underprices
-- the map's own first emission.  Depth does not compose by `⊔` there,
-- because neither occurrence is under the other.  `Spike.Scan` extends
-- `Tm` with exactly that template (`dupᵗ`) so the property stops
-- holding by accident of the fragment.
--
-- REFUTED: `Refuted.Hop-Mul-Clause` — the additive `mapᵉ` clause in the
-- real language, by `refl`-checked numerals against a one-value source.
--
-- `nestᵗ` is the case that matters for the refold: it adds a hop frame,
-- and the clause's own `suc` pays for it ONCE, independently of how
-- many values arrive.  That is the whole difference from the refold,
-- where the cost is per-arrival and no syntactic clause can see the
-- arrival count.
------------------------------------------------------------------

evalTm-hop : ∀ η f v → hopDv η (evalTm f v) ≤ hopDt η f + hopDv η v
evalTm-hop η inᵗ        v = ≤-refl
evalTm-hop η (konstᵗ k) v = m≤m+n _ _
evalTm-hop η (nestᵗ t)  v = s≤s (⊔-lub (evalTm-hop η t v) z≤n)

hopD-map-mono : ∀ η f e → hopD η e ≤ hopD η (mapᵉ f e)
hopD-map-mono η f e = m≤n+m _ _

hopDl-mem : ∀ η ws {u} → u ∈ ws → hopDv η u ≤ hopDl η ws
hopDl-mem η (w ∷ ws) (here refl) = m≤m⊔n _ _
hopDl-mem η (w ∷ ws) (there p)   = ≤-trans (hopDl-mem η ws p) (m≤n⊔m _ _)

mapB-mem : ∀ η f ws {u B} → (∀ {x} → x ∈ ws → hopDv η x ≤ B) →
           u ∈ mapB f ws → hopDv η u ≤ hopDt η f + B
mapB-mem η f (w ∷ ws) h (here refl) =
  ≤-trans (evalTm-hop η f w)
          (+-monoʳ-≤ (hopDt η f) (h (here refl)))
mapB-mem η f (w ∷ ws) h (there p) = mapB-mem η f ws (λ q → h (there q)) p

------------------------------------------------------------------
-- THE OUTERMOST COMPONENT: unconnected slots.  A connect extends the
-- connected set before recursing, so this strictly drops at exactly
-- the one edge that can raise both the others.
------------------------------------------------------------------

memberℕ : ℕ → List ℕ → Bool
memberℕ i []       = false
memberℕ i (j ∷ js) = if i ≡ᵇ j then true else memberℕ i js

≡ᵇ-refl : ∀ i → (i ≡ᵇ i) ≡ true
≡ᵇ-refl zero    = refl
≡ᵇ-refl (suc i) = ≡ᵇ-refl i

idxs : ℕ → List ℕ
idxs zero    = []
idxs (suc n) = n ∷ idxs n

idxs-mem : ∀ n {i} → i < n → i ∈ idxs n
idxs-mem (suc n) i<sn with m<1+n⇒m<n∨m≡n i<sn
... | inj₁ i<n  = there (idxs-mem n i<n)
... | inj₂ refl = here refl

cnt : List ℕ → List ℕ → ℕ
cnt []       cs = 0
cnt (j ∷ js) cs = (if memberℕ j cs then 0 else 1) + cnt js cs

cnt-mono : ∀ js i cs → cnt js (i ∷ cs) ≤ cnt js cs
cnt-mono []       i cs = z≤n
cnt-mono (j ∷ js) i cs with j ≡ᵇ i
... | true  = ≤-trans (cnt-mono js i cs) (m≤n+m _ _)
... | false = +-monoʳ-≤ _ (cnt-mono js i cs)

cnt-drop : ∀ js i cs → i ∈ js → memberℕ i cs ≡ false →
           cnt js (i ∷ cs) < cnt js cs
cnt-drop (j ∷ js) i cs (here refl) nm
  rewrite ≡ᵇ-refl i | nm = s≤s (cnt-mono js i cs)
cnt-drop (j ∷ js) i cs (there p) nm with j ≡ᵇ i
... | true  = ≤-trans (cnt-drop js i cs p nm) (m≤n+m _ _)
... | false = ≤-trans (≤-reflexive (sym (+-suc _ _)))
                      (+-monoʳ-≤ _ (cnt-drop js i cs p nm))

------------------------------------------------------------------
-- THE LEX ORDER.  Three strict components, no carries between them.
------------------------------------------------------------------

Meas : Set
Meas = ℕ × ℕ × ℕ

_≺_ : Rel Meas 0ℓ
_≺_ = ×-Lex _≡_ _<_ (×-Lex _≡_ _<_ _<_)

≺-wf : WellFounded _≺_
≺-wf = ×-wellFounded <-wellFounded (×-wellFounded <-wellFounded <-wellFounded)

-- the share connect: the outermost component drops, and the other two
-- are free to rise — which is the whole reason it is outermost
dropU : ∀ {U₁ U₂ r₁ r₂ s₁ s₂} → U₁ < U₂ → (U₁ , r₁ , s₁) ≺ (U₂ , r₂ , s₂)
dropU u = inj₁ u

-- the inner hop: the middle component drops, the innermost is free
hopStep : ∀ {U₁ U₂ r₁ r₂ s₁ s₂} → U₁ ≤ U₂ → r₁ < r₂ →
          (U₁ , r₁ , s₁) ≺ (U₂ , r₂ , s₂)
hopStep u≤ r< with m≤n⇒m<n∨m≡n u≤
... | inj₁ u<   = inj₁ u<
... | inj₂ refl = inj₂ (refl , inj₁ r<)

-- structural descent and the μ unfold: same slots, hop non-increasing,
-- synchronous size strictly down
descend : ∀ {U r₁ r₂ s₁ s₂} → r₁ ≤ r₂ → s₁ < s₂ →
          (U , r₁ , s₁) ≺ (U , r₂ , s₂)
descend r≤ s< with m≤n⇒m<n∨m≡n r≤
... | inj₁ r<   = inj₂ (refl , inj₁ r<)
... | inj₂ refl = inj₂ (refl , inj₂ (refl , s<))

------------------------------------------------------------------
-- THE EVALUATOR, as in Mini.  `N` is the slot count; an out-of-range
-- slot has its own domain constructor rather than a range side
-- condition, which is the untyped toy's stand-in for the real
-- language's `Fin n` slot index.
------------------------------------------------------------------

module Run (N : ℕ) (sl : List Exp) (η : ℕ → ℕ) where

  nth : ℕ → List Exp → Exp
  nth i       []       = ofᵉ []
  nth zero    (e ∷ _)  = e
  nth (suc i) (_ ∷ es) = nth i es

  def : ℕ → Exp
  def i = nth i sl

  unconn : List ℕ → ℕ
  unconn cs = cnt (idxs N) cs

  unconn-insert : ∀ i cs → i < N → memberℕ i cs ≡ false →
                  unconn (i ∷ cs) < unconn cs
  unconn-insert i cs i<N nm = cnt-drop (idxs N) i cs (idxs-mem N i<N) nm

  unconn-keeps : ∀ i cs → unconn (i ∷ cs) ≤ unconn cs
  unconn-keeps i cs = cnt-mono (idxs N) i cs

  data Dom  : Exp → List ℕ → Set
  data DomL : List Val → List ℕ → Set
  run  : ∀ e  cs → Dom  e  cs → List Val × List ℕ
  runL : ∀ vs cs → DomL vs cs → List Val × List ℕ

  data Dom where
    dOf    : ∀ {vs cs} → Dom (ofᵉ vs) cs
    dMap   : ∀ {f e cs} → Dom e cs → Dom (mapᵉ f e) cs
    dMu    : ∀ {b cs} → Dom (unfoldμ b) cs → Dom (μᵉ b) cs
    dRec   : ∀ {cs} → Dom recᵉ cs
    dDefer : ∀ {b cs} → Dom (deferᵉ b) cs
    dSlotC : ∀ {i cs} → memberℕ i cs ≡ true → Dom (slotᵉ i) cs
    dSlotX : ∀ {i cs} → N ≤ i → Dom (slotᵉ i) cs
    dSlotN : ∀ {i cs} → i < N → memberℕ i cs ≡ false →
             Dom (def i) (i ∷ cs) → Dom (slotᵉ i) cs
    dAll   : ∀ {e cs} (d : Dom e cs) →
             DomL (proj₁ (run e cs d)) (proj₂ (run e cs d)) →
             Dom (allᵉ e) cs

  data DomL where
    dLNil : ∀ {cs} → DomL [] cs
    dLNat : ∀ {n vs cs} → DomL vs cs → DomL (natᵛ n ∷ vs) cs
    dLObs : ∀ {o vs cs} (d : Dom o cs) →
            DomL vs (proj₂ (run o cs d)) → DomL (obsᵛ o ∷ vs) cs

  run (ofᵉ vs)   cs dOf            = vs , cs
  run (mapᵉ f e) cs (dMap d)       =
    mapB f (proj₁ (run e cs d)) , proj₂ (run e cs d)
  run (μᵉ b)     cs (dMu d)        = run (unfoldμ b) cs d
  run recᵉ       cs dRec           = [] , cs
  run (deferᵉ b) cs dDefer         = [] , cs
  run (slotᵉ i)  cs (dSlotC _)     = [] , cs
  run (slotᵉ i)  cs (dSlotX _)     = [] , cs
  run (slotᵉ i)  cs (dSlotN _ _ d) = run (def i) (i ∷ cs) d
  run (allᵉ e)   cs (dAll d ds)    =
    runL (proj₁ (run e cs d)) (proj₂ (run e cs d)) ds

  runL []             cs dLNil        = [] , cs
  runL (natᵛ n ∷ vs)  cs (dLNat ds)   = runL vs cs ds
  runL (obsᵛ o ∷ vs)  cs (dLObs d ds) =
    proj₁ (run o cs d) ++ proj₁ (runL vs (proj₂ (run o cs d)) ds)
      , proj₂ (runL vs (proj₂ (run o cs d)) ds)

  ------------------------------------------------------------------
  -- A RUN ONLY CONNECTS.  The outermost component never rises, which
  -- is what lets the inner-hop edge spend the middle one.
  ------------------------------------------------------------------

  run-unconn  : ∀ e cs (d : Dom e cs) → unconn (proj₂ (run e cs d)) ≤ unconn cs
  runL-unconn : ∀ vs cs (ds : DomL vs cs) →
                unconn (proj₂ (runL vs cs ds)) ≤ unconn cs

  run-unconn (ofᵉ vs)   cs dOf            = ≤-refl
  run-unconn (mapᵉ f e) cs (dMap d)       = run-unconn e cs d
  run-unconn (μᵉ b)     cs (dMu d)        = run-unconn (unfoldμ b) cs d
  run-unconn recᵉ       cs dRec           = ≤-refl
  run-unconn (deferᵉ b) cs dDefer         = ≤-refl
  run-unconn (slotᵉ i)  cs (dSlotC _)     = ≤-refl
  run-unconn (slotᵉ i)  cs (dSlotX _)     = ≤-refl
  run-unconn (slotᵉ i)  cs (dSlotN _ _ d) =
    ≤-trans (run-unconn (def i) (i ∷ cs) d) (unconn-keeps i cs)
  run-unconn (allᵉ e)   cs (dAll d ds)    =
    ≤-trans (runL-unconn (proj₁ (run e cs d)) (proj₂ (run e cs d)) ds)
            (run-unconn e cs d)

  runL-unconn []            cs dLNil        = ≤-refl
  runL-unconn (natᵛ n ∷ vs) cs (dLNat ds)   = runL-unconn vs cs ds
  runL-unconn (obsᵛ o ∷ vs) cs (dLObs d ds) =
    ≤-trans (runL-unconn vs (proj₂ (run o cs d)) ds) (run-unconn o cs d)

  ------------------------------------------------------------------
  -- THE INVARIANT.  Read the statement twice: it quantifies over the
  -- ACTUAL burst, and its bound is the emitter's own hop.
  ------------------------------------------------------------------

  module _ (η-fix : ∀ i → hopD η (def i) ≤ η i) where

    emit-hop  : ∀ e cs (d : Dom e cs) {v} →
                v ∈ proj₁ (run e cs d) → hopDv η v ≤ hopD η e
    emit-hopL : ∀ vs cs (ds : DomL vs cs) {w B} →
                (∀ {u} → u ∈ vs → hopDv η u ≤ B) →
                w ∈ proj₁ (runL vs cs ds) → hopDv η w ≤ B

    emit-hop (ofᵉ vs)   cs dOf      mem = hopDl-mem η vs mem
    emit-hop (mapᵉ f e) cs (dMap d) mem =
      mapB-mem η f (proj₁ (run e cs d)) (λ p → emit-hop e cs d p) mem
    emit-hop (μᵉ b) cs (dMu d) mem =
      ≤-trans (emit-hop (unfoldμ b) cs d mem)
              (≤-reflexive (hopD-subst η b (μᵉ b)))
    emit-hop recᵉ       cs dRec           ()
    emit-hop (deferᵉ b) cs dDefer         ()
    emit-hop (slotᵉ i)  cs (dSlotC _)     ()
    emit-hop (slotᵉ i)  cs (dSlotX _)     ()
    emit-hop (slotᵉ i)  cs (dSlotN _ _ d) mem =
      ≤-trans (emit-hop (def i) (i ∷ cs) d mem) (η-fix i)
    emit-hop (allᵉ e) cs (dAll d ds) mem =
      ≤-trans (emit-hopL (proj₁ (run e cs d)) (proj₂ (run e cs d)) ds
                (λ p → emit-hop e cs d p) mem)
              (n≤1+n (hopD η e))

    emit-hopL []             cs dLNil        h ()
    emit-hopL (natᵛ n ∷ vs)  cs (dLNat ds)   h mem =
      emit-hopL vs cs ds (λ p → h (there p)) mem
    emit-hopL (obsᵛ o ∷ vs)  cs (dLObs d ds) h mem
      with ++⁻ (proj₁ (run o cs d)) mem
    ... | inj₁ p = ≤-trans (emit-hop o cs d p) (h (here refl))
    ... | inj₂ q =
      emit-hopL vs (proj₂ (run o cs d)) ds (λ r → h (there r)) q

    ------------------------------------------------------------------
    -- TOTALITY.  Nothing here computes a budget.
    ------------------------------------------------------------------

    meas : Exp → List ℕ → Meas
    meas e cs = unconn cs , hopD η e , syncSize e

    totalL : ∀ vs cs (U R : ℕ) → unconn cs ≤ U →
             (∀ {u} → u ∈ vs → hopDv η u ≤ R) →
             (∀ o cs′ → unconn cs′ ≤ U → hopD η o ≤ R → Dom o cs′) →
             DomL vs cs
    totalL []             cs U R hU h rec = dLNil
    totalL (natᵛ n ∷ vs)  cs U R hU h rec =
      dLNat (totalL vs cs U R hU (λ p → h (there p)) rec)
    totalL (obsᵛ o ∷ vs)  cs U R hU h rec =
      dLObs d (totalL vs (proj₂ (run o cs d)) U R
                 (≤-trans (run-unconn o cs d) hU)
                 (λ p → h (there p)) rec)
      where d = rec o cs hU (h (here refl))

    total : ∀ e cs → Acc _≺_ (meas e cs) → Dom e cs
    total (ofᵉ vs)   cs a        = dOf
    total (mapᵉ f e) cs (acc rs) =
      dMap (total e cs (rs (descend (hopD-map-mono η f e) ≤-refl)))
    total (μᵉ b) cs (acc rs) =
      dMu (total (unfoldμ b) cs
             (rs (descend (≤-reflexive (hopD-subst η b (μᵉ b)))
                          (s≤s (≤-reflexive (syncSize-subst b (μᵉ b)))))))
    total recᵉ       cs a = dRec
    total (deferᵉ b) cs a = dDefer
    total (slotᵉ i) cs (acc rs) with memberℕ i cs in mem
    ... | true  = dSlotC mem
    ... | false with i <? N
    ...   | yes i<N =
      dSlotN i<N mem
        (total (def i) (i ∷ cs) (rs (dropU (unconn-insert i cs i<N mem))))
    ...   | no  i≮N = dSlotX (≮⇒≥ i≮N)
      where
        open import Data.Nat.Properties using (≮⇒≥)
    total (allᵉ e) cs (acc rs) =
      dAll d (totalL (proj₁ (run e cs d)) (proj₂ (run e cs d))
                (unconn cs) (hopD η e)
                (run-unconn e cs d)
                (λ p → emit-hop e cs d p)
                (λ o cs′ hU hR → total o cs′ (rs (hopStep hU (s≤s hR)))))
      where d = total e cs (rs (descend (n≤1+n (hopD η e)) ≤-refl))

    -- THE RESULT: the domain is everything, on a lex order with no
    -- budget in it anywhere.
    total! : ∀ e cs → Dom e cs
    total! e cs = total e cs (≺-wf (meas e cs))

------------------------------------------------------------------
-- NON-VACUITY.  A totality theorem over an evaluator that emits
-- nothing is not a result, so the witness `total!` builds is spent
-- here on a program exercising all four edges at once: `allᵉ` hops
-- into a value its own source emitted (E3), through a `μᵉ` unfold
-- (E2) and a `mapᵉ` descent (E1), onto a slot that is unconnected at
-- entry and connected on the way out (E4).
--
-- LOAD-BEARING, and each row says how it could fail: the burst is
-- `natᵛ 7`, which lives two subscriptions down and is reachable ONLY
-- through the inner hop — a degenerate `run` returns `[]` here; and
-- the connected set comes back non-empty, which a `run` that never
-- took the connect branch could not produce.
------------------------------------------------------------------

module Demo where

  def0 : Exp
  def0 = ofᵉ (obsᵛ (ofᵉ (natᵛ 7 ∷ [])) ∷ [])

  open Run 1 (def0 ∷ []) (λ _ → 0)

  η-fix0 : ∀ i → hopD (λ _ → 0) (def i) ≤ 0
  η-fix0 zero    = z≤n
  η-fix0 (suc i) = z≤n

  prog : Exp
  prog = allᵉ (μᵉ (mapᵉ inᵗ (slotᵉ 0)))

  witness : Dom prog []
  witness = total! η-fix0 prog []

  demo-burst : proj₁ (run prog [] witness) ≡ natᵛ 7 ∷ []
  demo-burst = refl

  demo-connected : proj₂ (run prog [] witness) ≡ 0 ∷ []
  demo-connected = refl
