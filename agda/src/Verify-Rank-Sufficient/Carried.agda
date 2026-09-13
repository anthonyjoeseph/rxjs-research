------------------------------------------------------------------
-- WHAT A BURST CARRIES: the deepest reading of any value a stream
-- delivers.
--
-- THE HOP EDGE SUBSCRIBES A VALUE, AND THAT IS THE WHOLE REASON THIS
-- MEASURE EXISTS.  `subscribeInner` steps the rank from `suc r` to `r`
-- and hands `subscribeE` an emitted value, structurally unrelated to
-- the term the caller was walking — so no quantity read off that term
-- bounds what comes next unless the walk CARRIES its emissions'
-- reading beside them.  A measure over the burst is what can be
-- carried: it is a property of what was produced, so a bound on it is
-- a postcondition the producing induction can strengthen to, rather
-- than a claim about an arbitrary value asserted from outside.
--
-- IT IS A ⊔ OVER THE `value` EVENTS AND NOTHING ELSE.  Bookkeeping
-- carries no payload, so `init`, `close`, `handoff` and `complete`
-- contribute nothing and the empty burst reads zero — which is what
-- makes the shapes that emit no values discharge their half of the
-- report by `z≤n` rather than by argument.  The same choice is what
-- `stHopᶜˢ` already makes about a queue, in the same currency, so a
-- stored value and a delivered one are comparable without a bridge.
--
-- THE COMPARISON THIS FEEDS IS NON-STRICT, and the strict one the peel
-- needs comes from the flattener's own clause rather than from here: a
-- `*All` node reads `suc` of its source by definition, so an inner
-- delivered by that source and bounded by the source's reading is
-- bounded STRICTLY by the node's.  Stating the strict form here
-- instead would be false at every shape that is not a flattener.
------------------------------------------------------------------
module Verify-Rank-Sufficient.Carried where

open import Data.Bool using (Bool; true; false; T; if_then_else_)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Nat using (ℕ; _⊔_; _≡ᵇ_; _≤_; z≤n)
open import Data.Nat.Properties using (⊔-assoc; ⊔-identityʳ; ⊔-lub; ≤-trans;
  m≤m⊔n; m≤n⊔m)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans;
  cong; cong₂)

open import Rx.Prim using (Id; InstEvent; init; value; close; handoff;
  complete; InstEmit)
open import Rx.Exp using (Ty; Ctx; Closed; Val; isData; unitᵗ; boolᵗ; natᵗ;
  _×ᵗ_; _+ᵗ_; obs)
open import Rx.Hop-Depth using (Rd; Rd₃; rdᵛ; _⊔ᴿ_)
open import Rx.Evaluator using (Stream; Sched; EvalSt; NodeId; NodeState;
  splitEvents; retagEvents; oneShotBurst; setNode; installNode; sharedPlumb;
  hasDry; stHopⁿ; stHopᴺ; stHop)

----------------------------------------------------------------------
-- THE MEASURE, at the three shapes the pipeline hands around: a run of
-- values, one emit's event list, and a whole burst.
--
-- IT IS TAKEN AT A PROJECTION OF THE READING RATHER THAN AT THE DEPTH,
-- AND THAT IS WHAT MAKES THE COUNT HALF FREE.  A value reads as a PAIR
-- — how many it delivers, and how deep it is — and a bound stated in
-- the depth alone cannot separate two payloads that differ only in the
-- first, which is what the frame shelf's refutations turn on.  Every ⊔
-- these measures take is pointwise in that pair, so one induction
-- proven at an ARBITRARY component is proven at both, and the shelf
-- pays for the wider currency in statements rather than in arithmetic.
----------------------------------------------------------------------

valsAt : ∀ {n} {Γ : Ctx n} (p : Rd → ℕ) (ψ : Fin n → Rd₃) (u : Ty)
       → List (Val Γ u) → ℕ
valsAt p ψ u []       = 0
valsAt p ψ u (v ∷ vs) = p (rdᵛ ψ u v) ⊔ valsAt p ψ u vs

emitAt : ∀ {n} {Γ : Ctx n} (p : Rd → ℕ) (ψ : Fin n → Rd₃) (u : Ty)
       → List (InstEvent (Val Γ u)) → ℕ
emitAt p ψ u []             = 0
emitAt p ψ u (value v ∷ es) = p (rdᵛ ψ u v) ⊔ emitAt p ψ u es
emitAt p ψ u (_       ∷ es) = emitAt p ψ u es

burstAt : ∀ {n} {Γ : Ctx n} (p : Rd → ℕ) (ψ : Fin n → Rd₃) (u : Ty)
        → Stream Γ u → ℕ
burstAt p ψ u []         = 0
burstAt p ψ u (em ∷ ems) =
  emitAt p ψ u (InstEmit.events em) ⊔ burstAt p ψ u ems

-- the reading in full, which is what a frame is entered under.  The
-- HOP alone is `proj₂` of it rather than a definition of its own, so a
-- statement wanting the depth and a statement wanting the pair cannot
-- drift apart into two currencies the way they once did.
valsRd : ∀ {n} {Γ : Ctx n} (ψ : Fin n → Rd₃) (u : Ty) → List (Val Γ u) → Rd
valsRd ψ u vs = valsAt proj₁ ψ u vs , valsAt proj₂ ψ u vs

burstRd : ∀ {n} {Γ : Ctx n} (ψ : Fin n → Rd₃) (u : Ty) → Stream Γ u → Rd
burstRd ψ u b = burstAt proj₁ ψ u b , burstAt proj₂ ψ u b

-- the order on readings is POINTWISE, and it has to be: the two
-- components are independent quantities and a lexicographic or summed
-- order would let a payload trade depth for deliveries
_⊑_ : Rd → Rd → Set
r ⊑ q = proj₁ r ≤ proj₁ q × proj₂ r ≤ proj₂ q

-- rewriting either end of a comparison, which is what every arm of the
-- walk does with the reading's own clause: the machine's reading and
-- the term's are EQUAL there, and only the direction differs
≡-⊑ : ∀ {a b c : Rd} → a ≡ b → b ⊑ c → a ⊑ c
≡-⊑ refl h = h

⊑-≡ : ∀ {a b c : Rd} → a ⊑ b → b ≡ c → a ⊑ c
⊑-≡ h refl = h

----------------------------------------------------------------------
-- THE ARITHMETIC.  Every one of these is a ⊔ being reassociated across
-- a concatenation the pipeline performs, so they are what a clause
-- spends and never what it has to think about.
----------------------------------------------------------------------

emitAt-++ : ∀ {n} {Γ : Ctx n} (p : Rd → ℕ) (ψ : Fin n → Rd₃) (u : Ty)
  (xs ys : List (InstEvent (Val Γ u))) →
  emitAt p ψ u (xs ++ ys) ≡ emitAt p ψ u xs ⊔ emitAt p ψ u ys
emitAt-++ p ψ u []               ys = refl
emitAt-++ p ψ u (value v   ∷ es) ys =
  trans (cong (p (rdᵛ ψ u v) ⊔_) (emitAt-++ p ψ u es ys))
        (sym (⊔-assoc (p (rdᵛ ψ u v)) (emitAt p ψ u es) (emitAt p ψ u ys)))
emitAt-++ p ψ u (init s    ∷ es) ys = emitAt-++ p ψ u es ys
emitAt-++ p ψ u (close s r ∷ es) ys = emitAt-++ p ψ u es ys
emitAt-++ p ψ u (handoff s ∷ es) ys = emitAt-++ p ψ u es ys
emitAt-++ p ψ u (complete  ∷ es) ys = emitAt-++ p ψ u es ys

emitAt-map : ∀ {n} {Γ : Ctx n} (p : Rd → ℕ) (ψ : Fin n → Rd₃) (u : Ty)
  (vs : List (Val Γ u)) → emitAt p ψ u (map value vs) ≡ valsAt p ψ u vs
emitAt-map p ψ u []       = refl
emitAt-map p ψ u (v ∷ vs) = cong (p (rdᵛ ψ u v) ⊔_) (emitAt-map p ψ u vs)

-- a payload run plus the completion the split saw: the completion is
-- bookkeeping, so the reading is exactly the run's
emitAt-values : ∀ {n} {Γ : Ctx n} (p : Rd → ℕ) (ψ : Fin n → Rd₃) (u : Ty)
  (vs : List (Val Γ u)) (fin : Bool) →
  emitAt p ψ u (map value vs ++ (if fin then complete ∷ [] else []))
    ≡ valsAt p ψ u vs
emitAt-values p ψ u vs true =
  trans (emitAt-++ p ψ u (map value vs) (complete ∷ []))
        (trans (⊔-identityʳ _) (emitAt-map p ψ u vs))
emitAt-values p ψ u vs false =
  trans (emitAt-++ p ψ u (map value vs) [])
        (trans (⊔-identityʳ _) (emitAt-map p ψ u vs))

----------------------------------------------------------------------
-- THE TWO PARTS THE PIPELINE STRIPS.  A split pulls the payload out
-- and a retag drops it, so neither of the event lists `pushBurst`
-- rebuilds an emit from carries anything — which is what leaves a
-- re-emitted burst reading exactly what the FRAME produced.
----------------------------------------------------------------------

emitAt-bk : ∀ {n} {Γ : Ctx n} (p : Rd → ℕ) (ψ : Fin n → Rd₃) (u w : Ty)
  (es : List (InstEvent (Val Γ u))) →
  emitAt p ψ w (proj₁ (proj₂ (splitEvents {A = Val Γ w} es))) ≡ 0
emitAt-bk p ψ u w []               = refl
emitAt-bk p ψ u w (value v   ∷ es) = emitAt-bk p ψ u w es
emitAt-bk p ψ u w (init s    ∷ es) = emitAt-bk p ψ u w es
emitAt-bk p ψ u w (close s r ∷ es) = emitAt-bk p ψ u w es
emitAt-bk p ψ u w (handoff s ∷ es) = emitAt-bk p ψ u w es
emitAt-bk p ψ u w (complete  ∷ es) = emitAt-bk p ψ u w es

emitAt-retag : ∀ {n} {Γ : Ctx n} (p : Rd → ℕ) (ψ : Fin n → Rd₃) (u w : Ty)
  (es : List (InstEvent (Val Γ u))) →
  emitAt p ψ w (retagEvents {Val Γ u} {Val Γ w} es) ≡ 0
emitAt-retag p ψ u w []               = refl
emitAt-retag p ψ u w (value v   ∷ es) = emitAt-retag p ψ u w es
emitAt-retag p ψ u w (init s    ∷ es) = emitAt-retag p ψ u w es
emitAt-retag p ψ u w (close s r ∷ es) = emitAt-retag p ψ u w es
emitAt-retag p ψ u w (handoff s ∷ es) = emitAt-retag p ψ u w es
emitAt-retag p ψ u w (complete  ∷ es) = emitAt-retag p ψ u w es

-- and what it strips out reads exactly what the emit did: the split is
-- a partition, so nothing deep is lost on the way to the frame
splitEvents-valsAt : ∀ {n} {Γ : Ctx n} (p : Rd → ℕ) (ψ : Fin n → Rd₃)
  (u : Ty) {A : Set} (es : List (InstEvent (Val Γ u))) →
  valsAt p ψ u (proj₁ (splitEvents {A = A} es)) ≡ emitAt p ψ u es
splitEvents-valsAt p ψ u []               = refl
splitEvents-valsAt p ψ u (value v   ∷ es) =
  cong (p (rdᵛ ψ u v) ⊔_) (splitEvents-valsAt p ψ u es)
splitEvents-valsAt p ψ u (init s    ∷ es) = splitEvents-valsAt p ψ u es
splitEvents-valsAt p ψ u (close s r ∷ es) = splitEvents-valsAt p ψ u es
splitEvents-valsAt p ψ u (handoff s ∷ es) = splitEvents-valsAt p ψ u es
splitEvents-valsAt p ψ u (complete  ∷ es) = splitEvents-valsAt p ψ u es

----------------------------------------------------------------------
-- THE ONE-SHOT SOURCE reads exactly its payload: the three shapes that
-- live and die inside their own subscribe frame announce, deliver and
-- close, and only the middle part carries anything.
----------------------------------------------------------------------

oneShotBurst-at : ∀ {n} {Γ : Ctx n} (p : Rd → ℕ) (ψ : Fin n → Rd₃)
  (u : Ty) (vals : List (Val Γ u)) (id : Id) (sched : Sched Γ) →
  burstAt p ψ u (proj₁ (oneShotBurst vals id sched)) ≡ valsAt p ψ u vals
oneShotBurst-at p ψ u vals id sched =
  trans (⊔-identityʳ _)
    (trans (emitAt-++ p ψ u (map value vals) _)
           (trans (⊔-identityʳ _) (emitAt-map p ψ u vals)))

oneShotBurst-rd : ∀ {n} {Γ : Ctx n} (ψ : Fin n → Rd₃) (u : Ty)
  (vals : List (Val Γ u)) (id : Id) (sched : Sched Γ) →
  burstRd ψ u (proj₁ (oneShotBurst vals id sched)) ≡ valsRd ψ u vals
oneShotBurst-rd ψ u vals id sched =
  cong₂ _,_ (oneShotBurst-at proj₁ ψ u vals id sched)
            (oneShotBurst-at proj₂ ψ u vals id sched)

----------------------------------------------------------------------
-- THE STORE, UNDER ONE BOUND.  Every write the walk makes goes through
-- `setNode`, which replaces where the id is present and installs where
-- it is not — so a bound holding of the state written and of the store
-- already there holds of the result either way.
----------------------------------------------------------------------

setNode-hop : ∀ {n} {Γ : Ctx n} (ψ : Fin n → Rd₃) (nid : NodeId)
  (s : NodeState Γ) (ns : List (NodeId × NodeState Γ)) (R : ℕ) →
  stHopⁿ ψ s ≤ R → stHopᴺ ψ ns ≤ R → stHopᴺ ψ (setNode nid s ns) ≤ R
setNode-hop ψ nid s []             R hs hn = ⊔-lub hs z≤n
setNode-hop ψ nid s ((k , s′) ∷ r) R hs hn with k ≡ᵇ nid
... | true  = ⊔-lub hs (≤-trans (m≤n⊔m _ _) hn)
... | false = ⊔-lub (≤-trans (m≤m⊔n _ _) hn)
                    (setNode-hop ψ nid s r R hs (≤-trans (m≤n⊔m _ _) hn))

installNode-hop : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (ψ : Fin n → Rd₃)
  (nid : NodeId) (s : NodeState Γ) (st : EvalSt e) (R : ℕ) →
  stHopⁿ ψ s ≤ R → stHop ψ st ≤ R → stHop ψ (installNode nid s st) ≤ R
installNode-hop ψ nid s st R hs hst =
  setNode-hop ψ nid s (EvalSt.nodes st) R hs hst

----------------------------------------------------------------------
-- PLUMBING RETAGS AND NOTHING ELSE, so a definition's burst reads the
-- same on the far side of a share boundary as it did on the near one.
----------------------------------------------------------------------

burstAt-plumb : ∀ {n} {Γ : Ctx n} (p : Rd → ℕ) (ψ : Fin n → Rd₃) (u : Ty)
  (b : Stream Γ u) → burstAt p ψ u (sharedPlumb b) ≡ burstAt p ψ u b
burstAt-plumb p ψ u []         = refl
burstAt-plumb p ψ u (em ∷ ems) =
  cong (emitAt p ψ u (InstEmit.events em) ⊔_) (burstAt-plumb p ψ u ems)

burstRd-plumb : ∀ {n} {Γ : Ctx n} (ψ : Fin n → Rd₃) (u : Ty)
  (b : Stream Γ u) → burstRd ψ u (sharedPlumb b) ≡ burstRd ψ u b
burstRd-plumb ψ u b =
  cong₂ _,_ (burstAt-plumb proj₁ ψ u b) (burstAt-plumb proj₂ ψ u b)

----------------------------------------------------------------------
-- A DATA-TYPED VALUE READS ZERO, and that is the whole of what a
-- SCRIPTED slot owes the report.  The telescope admits only `isData`
-- payloads at a script — an observable-typed slot could emit the very
-- program being walked — so the one leaf of the value reading that is
-- not literally zero cannot occur there, and the arm discharges by
-- computation rather than by argument.
----------------------------------------------------------------------

andT : (b c : Bool) → T (if b then c else false) → T b × T c
andT true  c ok = tt , ok
andT false c ()

data-rd : ∀ {n} {Γ : Ctx n} (ψ : Fin n → Rd₃) (t : Ty) (v : Val Γ t) →
  T (isData t) → rdᵛ ψ t v ≡ (0 , 0)
data-rd ψ unitᵗ    v        ok = refl
data-rd ψ boolᵗ    v        ok = refl
data-rd ψ natᵗ     v        ok = refl
data-rd ψ (s ×ᵗ t) (a , b)  ok =
  cong₂ _⊔ᴿ_ (data-rd ψ s a (proj₁ (andT (isData s) (isData t) ok)))
             (data-rd ψ t b (proj₂ (andT (isData s) (isData t) ok)))
data-rd ψ (s +ᵗ t) (inj₁ a) ok =
  data-rd ψ s a (proj₁ (andT (isData s) (isData t) ok))
data-rd ψ (s +ᵗ t) (inj₂ b) ok =
  data-rd ψ t b (proj₂ (andT (isData s) (isData t) ok))
data-rd ψ (obs t)  v        ()

-- AND THE COMPONENT HAS TO SAY WHAT IT READS AT THE ORIGIN, because a
-- projection is arbitrary here and the value reading is only known to
-- BE the origin.  Both projections this development takes satisfy it by
-- computation, so the premise costs a `refl` at every call.
valsAt-data : ∀ {n} {Γ : Ctx n} (p : Rd → ℕ) (ψ : Fin n → Rd₃) (t : Ty)
  (vs : List (Val Γ t)) → T (isData t) → p (0 , 0) ≡ 0 →
  valsAt p ψ t vs ≡ 0
valsAt-data p ψ t []       ok pz = refl
valsAt-data p ψ t (v ∷ vs) ok pz =
  cong₂ _⊔_ (trans (cong p (data-rd ψ t v ok)) pz)
            (valsAt-data p ψ t vs ok pz)

valsRd-data : ∀ {n} {Γ : Ctx n} (ψ : Fin n → Rd₃) (t : Ty)
  (vs : List (Val Γ t)) → T (isData t) → valsRd ψ t vs ≡ (0 , 0)
valsRd-data ψ t vs ok =
  cong₂ _,_ (valsAt-data proj₁ ψ t vs ok refl)
            (valsAt-data proj₂ ψ t vs ok refl)

----------------------------------------------------------------------
-- THE REPORT ITSELF, as a walk's strengthened postcondition: the burst
-- carries no dry marker, reads under the term's own reading, and leaves
-- the store reading under the RANK.
--
-- THE TWO BOUNDS ARE IN DIFFERENT CURRENCIES ON PURPOSE.  Every
-- operator clause of the reading joins its source's hop in or takes
-- `suc` of it, so a subterm reads under its parent and a TERM-relative
-- burst bound widens freely as the walk descends.  A store bound cannot
-- ride the term for exactly that reason, since the store holds nodes an
-- ANCESTOR installed and the current subterm does not dominate their
-- readings — so it rides the rank, which the descent preserves.  The
-- ordering between the two is not assumed: it is the entry invariant's
-- own second conjunct, handed to the one frame that writes what it
-- emits.
--
-- AND THE BURST HALF IS INSTANTIATED AT THE FAMILY THAT KILLED ITS
-- PREDECESSOR, in `Probed.Carried-Leaf` — a doubling fold at a late
-- slot, where the carried depth once climbed one per source literal
-- against a bound flat in source length.  Read against the iterating
-- clause the two sides agree at every length reached and the margin is
-- CONSTANT rather than closing, which is the shape a crossing would
-- have shown up in.  A definition carries no receipt, so this is a
-- finding rather than a coverage claim: every row there is a SUBSCRIBE
-- at the root, so none of it says what the loop preserves.
----------------------------------------------------------------------

WalkCarries : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (ψ : Fin n → Rd₃)
  (u : Ty) → Stream Γ u × Sched Γ × EvalSt e → Rd → ℕ → Set
WalkCarries ψ u r Rv Rst =
  hasDry (proj₁ r) ≡ false
  × burstRd ψ u (proj₁ r) ⊑ Rv
  × stHop ψ (proj₂ (proj₂ r)) ≤ Rst

-- the machine's own branch, one half of the report at a time: a connect
-- decides between two shapes that differ in their bookkeeping and in a
-- registry the reading does not look at, so each half holds of both
burstRd-if : ∀ {n} {Γ : Ctx n} {u} {B C : Set} (ψ : Fin n → Rd₃) (b : Bool)
  (x y : Stream Γ u × B × C) (R : Rd) →
  burstRd ψ u (proj₁ x) ⊑ R → burstRd ψ u (proj₁ y) ⊑ R →
  burstRd ψ u (proj₁ (if b then x else y)) ⊑ R
burstRd-if ψ true  x y R hx hy = hx
burstRd-if ψ false x y R hx hy = hy

stHop-if : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {A B : Set}
  (ψ : Fin n → Rd₃) (b : Bool) (x y : A × B × EvalSt e) (R : ℕ) →
  stHop ψ (proj₂ (proj₂ x)) ≤ R → stHop ψ (proj₂ (proj₂ y)) ≤ R →
  stHop ψ (proj₂ (proj₂ (if b then x else y))) ≤ R
stHop-if ψ true  x y R hx hy = hx
stHop-if ψ false x y R hx hy = hy
