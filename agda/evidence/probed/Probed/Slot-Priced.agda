-- A SLOT REFERENCE REPORTS THE WHOLE OF ITS DEF'S READING, AND A PAIR
-- CANNOT CARRY IT.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.
--
-- THE CLAUSE NOTHING HAD INSTANTIATED.  Every program the plug-priced
-- rows reach is CLOSED, so its `input` clause has only ever been read at
-- the empty environment — the position the whole reading stood in before
-- the clause sweep, narrowed to one clause and no smaller a risk for it.
-- A shared def of observable type emits values of positive hop and a
-- subscription connecting to it receives them, so the constant a caller
-- is always free to pick is false at the first flattener over an input.
--
-- WHAT THE STAGING COSTS, WHICH IS NOTHING.  The telescope is
-- stratified, so the environment is built by recursion on the slot
-- index — the same shape the delivery count's slot reading already has,
-- and it ports unchanged.
--
-- WHAT DOES NOT PORT, AND IT IS THE FINDING.  An expression's reading is
-- a TRIPLE — what it delivers, what one delivered value itself delivers,
-- and how deep it is — while what the environment carries is the PAIR a
-- plug needs.  A slot is not a plug: a reference stands for the def
-- itself, so the middle component is exactly the part a reference has to
-- report, and projecting to the pair throws it away and then re-invents
-- it from the top count.  A def delivering one observable of three
-- values reads as delivering one value of one, and a fold over the
-- flattener above it iterates once where the run refolds three times.
-- The pair candidate is not coarse there — it reads UNDER the run, which
-- is a crossing at the one clause the sweep left standing.
--
-- AND EXACTNESS DOES NOT SURVIVE A SOURCE CARRYING HOP, WHICH NOTHING
-- WAS LOOKING FOR.  The triple candidate reads four where the run hands
-- out three, so it is a true bound here and no longer the run's own
-- depth.  The cause is the iteration: it joins the SOURCE's reading into
-- the accumulator at every refold, and an accumulator is not a source —
-- the step's inner flattener is over what the fold has built.  Every
-- family swept so far sources from literals, whose hop is zero, so the
-- join was invisible; an input under a flattener is the first source
-- with a hop to contribute.  The slack is one and does not grow with the
-- refolds, which says this is the join and not the rate.
--
-- THE BOUNDARY.  One slot, so the staging is picked rather than
-- exercised: a second stage is the same clause again.  Nothing here
-- reaches a scripted slot carrying hop, because a scripted slot carries
-- DATA by construction and its hop is zero for that reason rather than
-- by a choice this file could test.  And the delivery COUNT is bounded
-- rather than exact wherever a literal's arms differ in width: the
-- reading takes one per-value figure for all of them, so the recursion
-- below reads four deliveries against a run of two, which is the join
-- over arms and is not the projection this file forks on.
--
-- FORK: dry-operator
module Probed.Slot-Priced where

open import Data.Bool using (true; false; if_then_else_)
open import Data.Fin using (Fin; toℕ) renaming (zero to fzero)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _⊔_; _⊔′_; _≡ᵇ_; _≤ᵇ_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (InstEvent; value; InstEmit)
open import Rx.Exp using (Ctx; Closed; Exp; Tm; Fn; obs; natᵗ; _×ᵗ_;
                         input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ;
                         mergeAllᵉ; switchAllᵉ; exhaustAllᵉ;
                         μᵉ; varᵉ; deferᵉ;
                         varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ;
                         inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ)
open import Rx.Slots using (Slot; Slots; scripted; shared)
open import Rx.Hop-Depth using (varIx)
open import Rx.Evaluator using (Stream)

open import Probed.Apparatus using (Separates; separates-at)
open import Probed.Plug-Priced using (Rd; Rd₃; Env; ε; _▸_; _⊔ᴿ_;
                                      litOf; flatten; topOf;
                                      rdᵉ; depthᴾ; carriedᴾ)
open import Probed.Slot-Defer using (syncOf; delivered; burstOf)
open import Refuted.Root-Refold using (burstAt)

----------------------------------------------------------------------
-- THE TELESCOPE THIS FILE IS ABOUT.  One slot, observable-typed, so it
-- can carry hop at all: a scripted slot is data by construction, and a
-- shared def is the only shape a reference can receive a stream from.
----------------------------------------------------------------------

Γₒ : Ctx 1
Γₒ = obs natᵗ ∷ⱽ []ⱽ

-- one observable of three values: the def's own delivery is ONE, and
-- what that one delivered value delivers is THREE, which is the gap a
-- pair cannot hold
wideVal : Tm Γₒ [] [] [] (obs natᵗ)
wideVal = strmᵗ (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ []))

defₒ : Closed Γₒ (obs natᵗ)
defₒ = ofᵉ (wideVal ∷ [])

insₒ : Slots Γₒ
insₒ fzero = shared defₒ

-- the same slot, holding a recursion: the gate cuts the unfolding out of
-- the subscribe frame, so the staged reading must survive it
defμ : Closed Γₒ (obs natᵗ)
defμ = μᵉ (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ [])) ∷
                strmᵗ (mergeAllᵉ nothing (deferᵉ (varᵉ (here refl)))) ∷ []))

insμ : Slots Γₒ
insμ fzero = shared defμ

----------------------------------------------------------------------
-- CANDIDATE A: THE ENVIRONMENT CARRIES A PAIR, staged exactly the way
-- the live hop reading and the delivery count both stage theirs — slot
-- k's reading against the readings of the slots below it.  The clause
-- under test is the projection: a def's triple is cut down to what a
-- plug needs, and `slotOf` re-invents the missing middle from the top.
----------------------------------------------------------------------

slotRdD : ∀ {n} {Γ : Ctx n} {k t} (ψ : Fin n → Rd) → Slot Γ k t → Rd
slotRdD ψ (scripted src) = syncOf src , 0
slotRdD ψ (shared d)     = topOf (rdᵉ ψ ε d)

ψAt : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (k : ℕ) → Fin n → Rd
ψAt sl zero    i = 0 , 0
ψAt sl (suc k) i =
  if toℕ i ≡ᵇ k then slotRdD (ψAt sl k) (sl i)
                else ψAt sl k i

slotRd : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) → Fin n → Rd
slotRd sl i = slotRdD (ψAt sl (toℕ i)) (sl i)

-- the candidate a caller is always free to pick, and the one every
-- closed program leaves the clause standing on
ψZero : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) → Fin n → Rd
ψZero sl i = 0 , 0

----------------------------------------------------------------------
-- CANDIDATE B: THE ENVIRONMENT CARRIES THE DEF'S WHOLE READING.  Every
-- clause below is the plug-priced one unchanged; the single difference
-- is that a reference reports its def's triple rather than a pair
-- widened back out, which is why the duplication is the separation.
----------------------------------------------------------------------

mutual
  rd3ᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (ψ : Fin n → Rd₃) (ρ : Env) →
         Exp Γ Δᵍ Δ Θ t → Rd₃
  rd3ᵉ ψ ρ (input i)         = ψ i
  rd3ᵉ ψ ρ (ofᵉ ts)          = litOf (length ts) (rd3ᵗˢ ψ ρ ts)
  rd3ᵉ ψ ρ emptyᵉ            = 0 , 0 , 0
  rd3ᵉ ψ ρ (mapᵉ f e)        = map3 ψ ρ (rd3ᵉ ψ ρ e) f
  rd3ᵉ ψ ρ (takeᵉ c e)       = rd3ᵉ ψ ρ e
  rd3ᵉ ψ ρ (scanᵉ f z e)     = scan3 ψ ρ (rd3ᵉ ψ ρ e) z f
  rd3ᵉ ψ ρ (mergeAllᵉ lim e) = flatten (rd3ᵉ ψ ρ e)
  rd3ᵉ ψ ρ (switchAllᵉ e)    = flatten (rd3ᵉ ψ ρ e)
  rd3ᵉ ψ ρ (exhaustAllᵉ e)   = flatten (rd3ᵉ ψ ρ e)
  rd3ᵉ ψ ρ (μᵉ e)            = rd3ᵉ ψ ρ e
  rd3ᵉ ψ ρ (varᵉ x)          = 0 , 0 , 0
  rd3ᵉ ψ ρ (deferᵉ e)        = 0 , 0 , 0

  map3 : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s t} (ψ : Fin n → Rd₃) (ρ : Env) →
         Rd₃ → Fn Γ Δᵍ Δ Θ s t → Rd₃
  map3 ψ ρ (d , ev , h) f = d , proj₁ r , proj₂ r ⊔′ h
    where r = rd3ᵗ ψ (ρ ▸ (ev , h)) f

  scan3 : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s t} (ψ : Fin n → Rd₃) (ρ : Env) →
          Rd₃ → Tm Γ Δᵍ Δ Θ t → Fn Γ Δᵍ Δ Θ s t → Rd₃
  scan3 ψ ρ (d , ev , h) z f = d , proj₁ a , proj₂ a ⊔′ h
    where a = fold3 ψ ρ (rd3ᵗ ψ ρ z) (ev , h) d f

  fold3 : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s t} (ψ : Fin n → Rd₃) (ρ : Env)
          (acc src : Rd) (R : ℕ) → Fn Γ Δᵍ Δ Θ s t → Rd
  fold3 ψ ρ acc src zero    f = acc
  fold3 ψ ρ acc src (suc R) f =
    acc ⊔ᴿ fold3 ψ ρ (rd3ᵗ ψ (ρ ▸ (acc ⊔ᴿ src)) f) src R f

  rd3ᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (ψ : Fin n → Rd₃) (ρ : Env) →
         Tm Γ Δᵍ Δ Θ t → Rd
  rd3ᵗ ψ ρ (varᵗ x)      = ρ (varIx x)
  rd3ᵗ ψ ρ unit̂          = 0 , 0
  rd3ᵗ ψ ρ (bool̂ _)      = 0 , 0
  rd3ᵗ ψ ρ (nat̂ _)       = 0 , 0
  rd3ᵗ ψ ρ (pairᵗ a b)   = rd3ᵗ ψ ρ a ⊔ᴿ rd3ᵗ ψ ρ b
  rd3ᵗ ψ ρ (fstᵗ p)      = rd3ᵗ ψ ρ p
  rd3ᵗ ψ ρ (sndᵗ p)      = rd3ᵗ ψ ρ p
  rd3ᵗ ψ ρ (inlᵗ a)      = rd3ᵗ ψ ρ a
  rd3ᵗ ψ ρ (inrᵗ a)      = rd3ᵗ ψ ρ a
  rd3ᵗ ψ ρ (caseᵗ s l r) = case3 ψ ρ (rd3ᵗ ψ ρ s) l r
  rd3ᵗ ψ ρ (ifᵗ c a b)   = rd3ᵗ ψ ρ a ⊔ᴿ rd3ᵗ ψ ρ b
  rd3ᵗ ψ ρ (primᵗ _ a)   = 0 , 0
  rd3ᵗ ψ ρ (strmᵗ e)     = topOf (rd3ᵉ ψ ρ e)

  case3 : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s u t} (ψ : Fin n → Rd₃) (ρ : Env) →
          Rd → Fn Γ Δᵍ Δ Θ s t → Fn Γ Δᵍ Δ Θ u t → Rd
  case3 ψ ρ p l r = rd3ᵗ ψ (ρ ▸ p) l ⊔ᴿ rd3ᵗ ψ (ρ ▸ p) r

  rd3ᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (ψ : Fin n → Rd₃) (ρ : Env) →
          List (Tm Γ Δᵍ Δ Θ t) → Rd
  rd3ᵗˢ ψ ρ []       = 0 , 0
  rd3ᵗˢ ψ ρ (y ∷ ys) = rd3ᵗ ψ ρ y ⊔ᴿ rd3ᵗˢ ψ ρ ys

-- the same staging again, at the triple
slotRd3D : ∀ {n} {Γ : Ctx n} {k t} (ψ : Fin n → Rd₃) → Slot Γ k t → Rd₃
slotRd3D ψ (scripted src) = syncOf src , 0 , 0
slotRd3D ψ (shared d)     = rd3ᵉ ψ ε d

ψ3At : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (k : ℕ) → Fin n → Rd₃
ψ3At sl zero    i = 0 , 0 , 0
ψ3At sl (suc k) i =
  if toℕ i ≡ᵇ k then slotRd3D (ψ3At sl k) (sl i)
                else ψ3At sl k i

slotRd3 : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) → Fin n → Rd₃
slotRd3 sl i = slotRd3D (ψ3At sl (toℕ i)) (sl i)

depth3 : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (ψ : Fin n → Rd₃) →
         Exp Γ Δᵍ Δ Θ t → ℕ
depth3 ψ e = proj₂ (topOf (rd3ᵉ ψ ε e))

evHop3 : ∀ {n} {Γ : Ctx n} {u} (ψ : Fin n → Rd₃) →
         List (InstEvent (Closed Γ u)) → ℕ
evHop3 ψ []             = 0
evHop3 ψ (value v ∷ es) = depth3 ψ v ⊔ evHop3 ψ es
evHop3 ψ (_ ∷ es)       = evHop3 ψ es

carried3 : ∀ {n} {Γ : Ctx n} {u} (ψ : Fin n → Rd₃) →
           Stream Γ (obs u) → ℕ
carried3 ψ []         = 0
carried3 ψ (em ∷ ems) = evHop3 ψ (InstEmit.events em) ⊔ carried3 ψ ems

----------------------------------------------------------------------
-- THE PROGRAMS.  One flattener over the slot, and a fold over that
-- flattener whose step emits a fold of its own accumulator — the family
-- that killed both dead readings, entered here through an input rather
-- than through a literal source, so what moves between the rows is the
-- slot's reading and nothing else.
----------------------------------------------------------------------

progM : Closed Γₒ natᵗ
progM = mergeAllᵉ nothing (input fzero)

innerₒ : Fn Γₒ [] [] (obs natᵗ ×ᵗ natᵗ ∷ []) (natᵗ ×ᵗ natᵗ) natᵗ
innerₒ = fstᵗ (varᵗ (here refl))

stepₒ : Fn Γₒ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
stepₒ = strmᵗ (scanᵉ innerₒ (nat̂ 0)
                (mergeAllᵉ nothing (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ []))))

seedₒ : Tm Γₒ [] [] [] (obs natᵗ)
seedₒ = strmᵗ (ofᵉ (nat̂ 0 ∷ []))

progF : Closed Γₒ (obs natᵗ)
progF = scanᵉ stepₒ seedₒ progM

----------------------------------------------------------------------
-- WHAT THE SLOT DELIVERS, read three ways and run once.  Each row is
-- LOAD-BEARING: the zero candidate has to differ for the staging to be
-- buying anything, and the pair candidate has to differ from the triple
-- for the projection to be the finding rather than a spelling.
----------------------------------------------------------------------

_ : proj₁ (topOf (rdᵉ (ψZero insₒ) ε progM)) ≡ 0        -- LOAD-BEARING
_ = refl

_ : proj₁ (topOf (rdᵉ (slotRd insₒ) ε progM)) ≡ 1       -- LOAD-BEARING
_ = refl

_ : proj₁ (topOf (rd3ᵉ (slotRd3 insₒ) ε progM)) ≡ 3     -- LOAD-BEARING
_ = refl

-- the run, and it settles which of the three is right: the reference
-- receives the def's one observable and the flattener above it hands out
-- that observable's three values
_ : delivered (burstOf progM insₒ) ≡ 3                  -- LOAD-BEARING
_ = refl

----------------------------------------------------------------------
-- THE CROSSING, AT DEPTH.  A fold takes its refold count off its
-- source, so a source read short of what it delivers is a fold read
-- short by the same refolds — and this family's depth climbs one per
-- refold.  The pair candidate lands UNDER the run, which is what makes
-- this a refutation of the clause and not a report that it is loose.
-- The triple candidate lands one OVER it: the guard holds and the rows
-- are the coverage for the second finding rather than for exactness,
-- which this source's own hop is what costs.
----------------------------------------------------------------------

_ : depthᴾ (slotRd insₒ) progF ≡ 2                      -- LOAD-BEARING
_ = refl

_ : depth3 (slotRd3 insₒ) progF ≡ 4                     -- LOAD-BEARING
_ = refl

_ : carried3 (slotRd3 insₒ) (burstAt 1 progF insₒ) ≡ 3  -- LOAD-BEARING
_ = refl

_ : (carried3 (slotRd3 insₒ) (burstAt 1 progF insₒ) ≤ᵇ
       depth3 (slotRd3 insₒ) progF) ≡ true
_ = refl

_ : (carriedᴾ (slotRd insₒ) (burstAt 1 progF insₒ) ≤ᵇ
       depthᴾ (slotRd insₒ) progF) ≡ false
_ = refl

----------------------------------------------------------------------
-- AND AT A SHARE HOLDING A RECURSION, where the two candidates AGREE —
-- the def's top count and its per-value count coincide there, so the
-- projection loses nothing and the rows say the STAGING is sound rather
-- than that the projection is.  The gate is what makes them coincide:
-- the recursive arm contributes nothing, so what is joined into the
-- per-value figure is the literal arm's width.  That join is also why
-- both read four against a run of two — the arms differ in width and one
-- figure is taken for both, which bounds and does not refute.
----------------------------------------------------------------------

_ : proj₁ (topOf (rdᵉ (slotRd insμ) ε progM)) ≡ 4        -- LOAD-BEARING
_ = refl

_ : proj₁ (topOf (rd3ᵉ (slotRd3 insμ) ε progM)) ≡ 4      -- LOAD-BEARING
_ = refl

_ : delivered (burstOf progM insμ) ≡ 2                   -- LOAD-BEARING
_ = refl

_ : (carried3 (slotRd3 insμ) (burstAt 1 progF insμ) ≤ᵇ
       depth3 (slotRd3 insμ) progF) ≡ true
_ = refl

----------------------------------------------------------------------
-- THE FORK.  The choice is what a slot environment CARRIES: the pair a
-- plug needs, which is what both staged readings already in this tree
-- carry and what the plug-priced clause was written against, or the
-- whole triple, which is what a reference to a def actually stands for.
-- They are apart at the first def whose own delivery and whose values'
-- deliveries differ — which no closed program can exhibit, and which is
-- why the clause reached this leg untested.
----------------------------------------------------------------------

Point : Set
Point = Slots Γₒ

pairEnv tripleEnv : Point → ℕ
pairEnv   sl = depthᴾ (slotRd sl) progF
tripleEnv sl = depth3 (slotRd3 sl) progF

slot-priced-fork : Separates pairEnv tripleEnv
slot-priced-fork = separates-at insₒ (λ ())
