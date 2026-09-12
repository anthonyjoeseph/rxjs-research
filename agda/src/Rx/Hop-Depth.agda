------------------------------------------------------------------
-- THE REMAINING-HOP DEPTH: an upper bound on how many more *All
-- frames a subscription can still enter.
--
-- Every reading SEEDED from the program is refuted: the hop edge
-- subscribes a runtime VALUE, structurally unrelated to the caller, so
-- no quantity read off the term, the store or the arrival bounds what
-- comes after it.  This measure is the other direction — it is a
-- quantity a value CARRIES, so a bound on it can be threaded as a
-- strengthened postcondition through the very induction that builds
-- the value, instead of being asserted about the value from outside.
------------------------------------------------------------------

------------------------------------------------------------------
-- AN EXPRESSION READS AS A TRIPLE AND A TERM AS A PAIR, and the odd
-- component is what every earlier reading was missing.  An expression
-- is a stream: what it delivers at the TOP of its own burst, what ONE
-- delivered value itself delivers, and how deep it is.  A term of
-- observable type stands for a stream a binder will be handed, so what
-- a plug has to report is the outer two and no more.
--
-- The middle component is the one a fold consumes.  A fold refolds once
-- per delivery of its SOURCE, so the top count is the refold count; what
-- the accumulator is built out of is what one delivered value carries.
-- Collapsing the two is what made a reference report its def as
-- delivering one value of one.
------------------------------------------------------------------

------------------------------------------------------------------
-- A FOLD ITERATES; IT DOES NOT EXPONENTIATE, AND THE WHOLE SHAPE OF
-- THIS MODULE FOLLOWS FROM THAT.  A closed form is what a reading
-- carries when the plug's own reading is unavailable; at a fold it IS
-- available, because the fold knows its accumulator — that starts at
-- the seed, and each refold is the step read against the previous one.
-- So the scan clause ITERATES over its refold count, and every variable
-- is read off an ENVIRONMENT the descent through the term extends at
-- each binder rather than scaled by a slope.
--
-- WHAT THAT BUYS is not a larger bound but an EXACT one, which is the
-- part worth having: a bound dominating by a growing margin is unusable
-- as a descent measure however true it is.  The same program that reads
-- exactly here prices a closed form twelve orders of magnitude above
-- its own run.
--
-- AND WHAT IT COSTS is the closed form itself: a fold's contribution
-- stops being a power a proof can rewrite and becomes a recursion over
-- the refold count, so every arithmetic fact about this measure is a
-- fact about that recursion.  Against that, a multiplicity family has
-- no job left — a slope exists to price a variable, and an environment
-- prices it exactly.
--
-- DEAD ROUTE: a reading whose fold clause charges a power of the STORE
--   BOUND, where `evaluate` sets that bound from the FUEL.  Fuel counts
--   ARRIVALS and a refold happens per DELIVERY, so a cascade delivering
--   entirely inside one subscribe frame refolds as many times as its
--   source has literals while consuming no fuel at all, and the run then
--   goes dry.  It was machine-refuted at four cascade programs and two
--   fuels while that reading stood; the environment reading below is
--   what closed it, and the same programs now come back dry-free, so
--   there is no ⊥ left to state and the finding is prose.
-- DEAD ROUTE: swapping that exponent for a delivery count, which fixes
--   the refutation's own family and dies one clause across.  A step
--   whose emission is itself a FOLD hands out a term the entry never
--   read, since a fold builds its accumulator at RUN time; the entry
--   sees the accumulator as a VARIABLE, prices the emitted fold's
--   exponent at one, and the run pays it in full once per refold.  Two
--   families separate it decisively: one crosses by a constant, the
--   other doubles the emitted fold's exponent per refold on the same
--   reading, so no coefficient reaches it.
-- DEAD ROUTE: an OCCURRENCE COUNT as the coefficient of a slope, in
--   either of its forms, and the two failures point opposite ways.  An
--   index-blind count OVER-prices the join clauses, where mentioning a
--   value twice deepens nothing, and inflates further under a
--   substitution that duplicates nothing, because the plug arrives
--   carrying its own binders' variables.  Restricting the count to the
--   binder's own index fixes the phantom inflation and is still wrong,
--   because it is still a count: a plug in an inner map's source is
--   scaled by that inner template's coefficient, a factor no count of
--   outer mentions can see.
-- RECOVERY: git show f205085 restores the size invariant and the
--   id-growing budget an earlier route's refold premise fell out of.
------------------------------------------------------------------

------------------------------------------------------------------
-- THE MAXIMUM IS THE PRIMITIVE ONE, AND THAT IS FORCED.  The library's
-- ordinary maximum is unary-recursive with no builtin behind it, so it
-- costs one step — and one allocated cell — per unit of its SMALLER
-- operand.  Every maximum here is taken between two READINGS, and a
-- delivery count is a PRODUCT at each flattener, so both operands grow
-- with the nesting and a single maximum becomes a recursion long enough
-- to be an out-of-memory kill rather than a slow check.  It lands on
-- anything that evaluates a program at all, since the entry rank is
-- read off this measure.  The primitive variant decides by the builtin
-- comparison instead and is free at any magnitude, and the library
-- proves the two equal — so every statement here means exactly what it
-- meant, and the one site that spends a maximum LEMMA transports across
-- that equality.
--
-- The maxima elsewhere in the evaluator are deliberately left as they
-- are: they combine NESTINGS, which are bounded by the syntax, and a
-- maximum whose smaller operand is small is already cheap.
------------------------------------------------------------------

------------------------------------------------------------------
-- WHY IT IS ψ-PARAMETERISED, AND WHY ψ CARRIES A TRIPLE.  ψ assigns a
-- reading to each slot of the telescope, and the `input` clause reports
-- it.  A constant-zero reading there is false: an obs-typed shared
-- slot's def emits values of positive hop, and a subscription
-- connecting to that slot receives them, so zeroing the share boundary
-- breaks at the first flattener over an input.  The honest
-- instantiation recurses on the slot index, which terminates because
-- the telescope is stratified — a shared def reads only earlier inputs.
--
-- A SLOT IS PRICED BY THE DEF'S WHOLE READING, NOT BY THE PAIR A PLUG
-- TAKES.  A reference stands for the def, so the middle component is
-- precisely what it has to report; an environment built at the pair
-- rebuilds that middle from the top count, and a def delivering one
-- observable of three values then reads as delivering one value of one.
-- The fold above it iterates once where the run refolds three times —
-- a crossing and not a coarseness, since a fold takes its refold count
-- off its source.
--
-- AND IT BOUNDS RATHER THAN EQUALS THE RUN WHERE A DEF'S ARMS DIFFER IN
-- WIDTH, since one per-value figure is joined over all of them.  That is
-- an instantiated boundary and not a reading of the clauses: the staged
-- environment was computed both ways over a def delivering one
-- observable of three values, and at a share holding a recursion.
-- `git show 8c6fc8d:agda/evidence/probed/Probed/Slot-Priced.agda` holds
-- those rows.
------------------------------------------------------------------

------------------------------------------------------------------
-- AND EXACTNESS STOPS AT A SOURCE THAT CARRIES HOP.  The iteration
-- joins the SOURCE's reading into the accumulator at every refold, and
-- an accumulator is not a source — a step's inner flattener is over what
-- the fold has built.  Every family swept before sources from literals,
-- whose hop is zero, so the join cost nothing and the rows read as
-- exact; a flattened input is the first source with a hop to contribute,
-- and there the reading sits one above its run.  The slack does not grow
-- with the refolds, which is what says it is the join and not the rate,
-- so the reading is still a bound tight enough to descend against.
------------------------------------------------------------------

------------------------------------------------------------------
-- THE CLAUSES NO FOLD FAMILY TOUCHES READ CORRECTLY TOO, and that is
-- the risk rather than a caveat: both dead readings above were exact at
-- the families THEY were tried on and each died at the first shape
-- nobody had instantiated, so a reading whose whole receipt was one
-- operator would stand exactly where those two stood before their
-- refutations.
--
-- WHAT HAS BEEN INSTANTIATED AGAINST THAT RISK, and where it stops.  A
-- template that reads its plug, one that drops it, a case binder at both
-- tags, a switch and an exhaust root beside a merge, and a recursion
-- through the defer gate: the door equals the run at every one
-- (`git show 8c6fc8d:agda/evidence/probed/Probed/Clause-Sweep.agda`).  So
-- do the refutation's own inner family and both emitted-fold families
-- that killed the swap, at every length
-- (`git show 8c6fc8d:agda/evidence/probed/Probed/Plug-Priced.agda`).  The
-- boundary of both is sources of hop ZERO — where the join above is free
-- — and refold counts in single and double digits.
------------------------------------------------------------------

------------------------------------------------------------------
-- THE INVARIANCE that makes the reading usable under the μ edge: a
-- substitution plugs Δᵍ-closed expressions, and Δᵍ-variables are
-- reachable only under a `deferᵉ`, which every recursion here cuts.  So
-- an unfolding reads EQUAL to its redex, and the μ guard pays with the
-- sync component alone.
--
-- RECOVERY: `git show 919f115:agda/src/Verify-Budget-Sufficient/Walk-Level.agda`
--   restores the walk these congruences were first proven against, whose
--   evaluator this development has replaced.
------------------------------------------------------------------
module Rx.Hop-Depth where

open import Data.Nat  using (ℕ; zero; suc; _*_; _⊔′_)
open import Data.Fin  using (Fin)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum     using (inj₁; inj₂)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any       using (here; there)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans)

open import Rx.Exp using (Ty; unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_; obs;
                          Ctx; Exp; Tm; Fn; Val;
                          input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ;
                          mergeAllᵉ; switchAllᵉ; exhaustAllᵉ;
                          μᵉ; varᵉ; deferᵉ;
                          varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ;
                          inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ;
                          elimGExp; elimGTm; elimGTms; unfoldμ)

-- the de Bruijn index a Θ-variable stands at.  It has exactly one
-- consumer, the term reading's leaf clause, so it lives here rather
-- than beside the syntax it reads
varIx : ∀ {t} {Θ : List Ty} → t ∈ Θ → ℕ
varIx (here _)  = zero
varIx (there p) = suc (varIx p)

------------------------------------------------------------------
-- THE TWO SHAPES, and the four changes between them, each named so no
-- clause below needs a `with` and no reading is computed twice.
------------------------------------------------------------------

Rd : Set
Rd = ℕ × ℕ

Rd₃ : Set
Rd₃ = ℕ × ℕ × ℕ

_⊔ᴿ_ : Rd → Rd → Rd
(a , b) ⊔ᴿ (c , d) = a ⊔′ c , b ⊔′ d

-- the Θ environment, indexed by de Bruijn index
Env : Set
Env = ℕ → Rd

-- a Θ-variable with nothing plugged into it
ε : Env
ε _ = 0 , 0

_▸_ : Env → Rd → Env
(ρ ▸ p) zero    = p
(ρ ▸ p) (suc k) = ρ k

-- a literal source delivers as many values as it has terms, each
-- reading what the terms read
litOf : ℕ → Rd → Rd₃
litOf k (ev , h) = k , ev , h

-- THE HOP EDGE: entering an inner costs exactly one, and what the frame
-- then delivers is what one arriving inner delivers
flatten : Rd₃ → Rd₃
flatten (d , ev , h) = d * ev , ev , suc h

topOf : Rd₃ → Rd
topOf (d , _ , h) = d , h

hopOf : Rd₃ → ℕ
hopOf (_ , _ , h) = h

------------------------------------------------------------------
-- THE READING.
------------------------------------------------------------------

mutual
  rdᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (ψ : Fin n → Rd₃) (ρ : Env) →
        Exp Γ Δᵍ Δ Θ t → Rd₃
  -- THE SLOT: a connect delivers the def's emissions, all three
  -- components of them
  rdᵉ ψ ρ (input i)         = ψ i
  rdᵉ ψ ρ (ofᵉ ts)          = litOf (length ts) (rdᵗˢ ψ ρ ts)
  rdᵉ ψ ρ emptyᵉ            = 0 , 0 , 0
  rdᵉ ψ ρ (mapᵉ f e)        = mapStep ψ ρ (rdᵉ ψ ρ e) f
  -- the count is a natᵗ term: its value carries no observable
  rdᵉ ψ ρ (takeᵉ c e)       = rdᵉ ψ ρ e
  rdᵉ ψ ρ (scanᵉ f z e)     = scanStep ψ ρ (rdᵉ ψ ρ e) z f
  rdᵉ ψ ρ (mergeAllᵉ lim e) = flatten (rdᵉ ψ ρ e)
  rdᵉ ψ ρ (switchAllᵉ e)    = flatten (rdᵉ ψ ρ e)
  rdᵉ ψ ρ (exhaustAllᵉ e)   = flatten (rdᵉ ψ ρ e)
  rdᵉ ψ ρ (μᵉ e)            = rdᵉ ψ ρ e
  rdᵉ ψ ρ (varᵉ x)          = 0 , 0 , 0
  rdᵉ ψ ρ (deferᵉ e)        = 0 , 0 , 0

  -- A TEMPLATE IS READ AGAINST ITS ARGUMENT, not scaled by a slope.  A
  -- map delivers one value per source value, so the top count is the
  -- source's; the join with the source's own depth is what a template
  -- that DROPS its argument needs, since the source is still subscribed
  mapStep : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s t} (ψ : Fin n → Rd₃) (ρ : Env) →
            Rd₃ → Fn Γ Δᵍ Δ Θ s t → Rd₃
  mapStep ψ ρ (d , ev , h) f = d , proj₁ r , proj₂ r ⊔′ h
    where r = rdᵗ ψ (ρ ▸ (ev , h)) f

  -- THE CLAUSE THE MODULE IS ABOUT.  The accumulator starts at the
  -- seed's own reading and each refold reads the step against the
  -- previous one, so an emitted fold is read at the accumulator it will
  -- actually be handed.  The source's top count is how many refolds
  -- there are
  scanStep : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s t} (ψ : Fin n → Rd₃) (ρ : Env) →
             Rd₃ → Tm Γ Δᵍ Δ Θ t → Fn Γ Δᵍ Δ Θ s t → Rd₃
  scanStep ψ ρ (d , ev , h) z f = d , proj₁ a , proj₂ a ⊔′ h
    where a = foldGo ψ ρ (rdᵗ ψ ρ z) (ev , h) d f

  -- the accumulator's reading after each refold, joined over all of
  -- them because the fold EMITS every one and the claim is about the
  -- deepest
  foldGo : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s t} (ψ : Fin n → Rd₃) (ρ : Env)
           (acc src : Rd) (R : ℕ) → Fn Γ Δᵍ Δ Θ s t → Rd
  foldGo ψ ρ acc src zero    f = acc
  foldGo ψ ρ acc src (suc R) f =
    acc ⊔ᴿ foldGo ψ ρ (rdᵗ ψ (ρ ▸ (acc ⊔ᴿ src)) f) src R f

  rdᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (ψ : Fin n → Rd₃) (ρ : Env) →
        Tm Γ Δᵍ Δ Θ t → Rd
  -- THE LEAF: what is plugged here is READ, not assumed absent
  rdᵗ ψ ρ (varᵗ x)      = ρ (varIx x)
  rdᵗ ψ ρ unit̂          = 0 , 0
  rdᵗ ψ ρ (bool̂ _)      = 0 , 0
  rdᵗ ψ ρ (nat̂ _)       = 0 , 0
  rdᵗ ψ ρ (pairᵗ a b)   = rdᵗ ψ ρ a ⊔ᴿ rdᵗ ψ ρ b
  rdᵗ ψ ρ (fstᵗ p)      = rdᵗ ψ ρ p
  rdᵗ ψ ρ (sndᵗ p)      = rdᵗ ψ ρ p
  rdᵗ ψ ρ (inlᵗ a)      = rdᵗ ψ ρ a
  rdᵗ ψ ρ (inrᵗ a)      = rdᵗ ψ ρ a
  rdᵗ ψ ρ (caseᵗ s l r) = caseStep ψ ρ (rdᵗ ψ ρ s) l r
  rdᵗ ψ ρ (ifᵗ c a b)   = rdᵗ ψ ρ a ⊔ᴿ rdᵗ ψ ρ b
  -- a PrimOp lands in natᵗ or boolᵗ: nothing plugged into it reaches a
  -- hop
  rdᵗ ψ ρ (primᵗ _ a)   = 0 , 0
  rdᵗ ψ ρ (strmᵗ e)     = topOf (rdᵉ ψ ρ e)

  -- a case BINDS, so it plugs like a template: the scrutinee's reading
  -- lands at every occurrence of the branch's bound variable
  caseStep : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s u t} (ψ : Fin n → Rd₃) (ρ : Env) →
             Rd → Fn Γ Δᵍ Δ Θ s t → Fn Γ Δᵍ Δ Θ u t → Rd
  caseStep ψ ρ p l r = rdᵗ ψ (ρ ▸ p) l ⊔ᴿ rdᵗ ψ (ρ ▸ p) r

  rdᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (ψ : Fin n → Rd₃) (ρ : Env) →
         List (Tm Γ Δᵍ Δ Θ t) → Rd
  rdᵗˢ ψ ρ []       = 0 , 0
  rdᵗˢ ψ ρ (y ∷ ys) = rdᵗ ψ ρ y ⊔ᴿ rdᵗˢ ψ ρ ys

-- the same reading on a runtime value: an embedded observable is its
-- expression's, a ground payload carries no hops
rdᵛ : ∀ {n} {Γ : Ctx n} (ψ : Fin n → Rd₃) (t : Ty) → Val Γ t → Rd
rdᵛ ψ unitᵗ    _        = 0 , 0
rdᵛ ψ boolᵗ    _        = 0 , 0
rdᵛ ψ natᵗ     _        = 0 , 0
rdᵛ ψ (s ×ᵗ t) (a , b)  = rdᵛ ψ s a ⊔ᴿ rdᵛ ψ t b
rdᵛ ψ (s +ᵗ t) (inj₁ a) = rdᵛ ψ s a
rdᵛ ψ (s +ᵗ t) (inj₂ b) = rdᵛ ψ t b
rdᵛ ψ (obs t)  e        = topOf (rdᵉ ψ ε e)

-- THE NUMBER the descent compares.  A reading taken at the top of a
-- term has nothing plugged into it, so the environment is empty there
-- and only the hop component is the rank's business
depthᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (ψ : Fin n → Rd₃) →
         Exp Γ Δᵍ Δ Θ t → ℕ
depthᵉ ψ e = hopOf (rdᵉ ψ ε e)

depthᵛ : ∀ {n} {Γ : Ctx n} (ψ : Fin n → Rd₃) (t : Ty) → Val Γ t → ℕ
depthᵛ ψ t v = proj₂ (rdᵛ ψ t v)

------------------------------------------------------------------
-- THE READING IS INVARIANT UNDER Δᵍ-ELIMINATION, which is what makes
-- the μ edge free.  Every clause is either a congruence over subterms
-- or an outright `refl` at the two leaves that could have seen the
-- substitution.  The binders need their own congruences because their
-- clauses consume a reading and a term TOGETHER, so neither `cong` nor
-- `cong₂` reaches them: the term is not equal to its image, only its
-- reading is.
------------------------------------------------------------------

-- a substitution rewrites terms in place, so a literal source keeps
-- its length — needed because the literal clause reads that length
length-elimG : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
  (cl : Exp Γ [] [] [] t) (ts : List (Tm Γ Δᵍ Δ Θ u)) →
  length (elimGTms x cl ts) ≡ length ts
length-elimG x cl []       = refl
length-elimG x cl (y ∷ ys) = cong suc (length-elimG x cl ys)

mutual
  rd-elimGᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (ψ : Fin n → Rd₃) (ρ : Env)
    (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t) (b : Exp Γ Δᵍ Δ Θ u) →
    rdᵉ ψ ρ (elimGExp x cl b) ≡ rdᵉ ψ ρ b
  rd-elimGᵉ ψ ρ x cl (input i)       = refl
  rd-elimGᵉ ψ ρ x cl (ofᵉ ts)        =
    cong₂ litOf (length-elimG x cl ts) (rd-elimGᵗˢ ψ ρ x cl ts)
  rd-elimGᵉ ψ ρ x cl emptyᵉ          = refl
  rd-elimGᵉ ψ ρ x cl (mapᵉ f b)      =
    trans (cong (λ p → mapStep ψ ρ p (elimGTm x cl f))
                (rd-elimGᵉ ψ ρ x cl b))
          (mapStep-elimG ψ ρ (rdᵉ ψ ρ b) x cl f)
  rd-elimGᵉ ψ ρ x cl (takeᵉ c b)     = rd-elimGᵉ ψ ρ x cl b
  rd-elimGᵉ ψ ρ x cl (scanᵉ f z b)   =
    trans (cong (λ p → scanStep ψ ρ p (elimGTm x cl z) (elimGTm x cl f))
                (rd-elimGᵉ ψ ρ x cl b))
          (scanStep-elimG ψ ρ (rdᵉ ψ ρ b) x cl z f)
  rd-elimGᵉ ψ ρ x cl (mergeAllᵉ lim b) = cong flatten (rd-elimGᵉ ψ ρ x cl b)
  rd-elimGᵉ ψ ρ x cl (switchAllᵉ b)  = cong flatten (rd-elimGᵉ ψ ρ x cl b)
  rd-elimGᵉ ψ ρ x cl (exhaustAllᵉ b) = cong flatten (rd-elimGᵉ ψ ρ x cl b)
  rd-elimGᵉ ψ ρ x cl (μᵉ b)          = rd-elimGᵉ ψ ρ (there x) cl b
  rd-elimGᵉ ψ ρ x cl (varᵉ y)        = refl
  rd-elimGᵉ ψ ρ x cl (deferᵉ b)      = refl

  mapStep-elimG : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s u t} (ψ : Fin n → Rd₃)
    (ρ : Env) (p : Rd₃) (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t)
    (f : Fn Γ Δᵍ Δ Θ s u) →
    mapStep ψ ρ p (elimGTm x cl f) ≡ mapStep ψ ρ p f
  mapStep-elimG ψ ρ (d , ev , h) x cl f =
    cong (λ r → d , proj₁ r , proj₂ r ⊔′ h)
         (rd-elimGᵗ ψ (ρ ▸ (ev , h)) x cl f)

  scanStep-elimG : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s u} {t} (ψ : Fin n → Rd₃)
    (ρ : Env) (p : Rd₃) (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t)
    (z : Tm Γ Δᵍ Δ Θ u) (f : Fn Γ Δᵍ Δ Θ s u) →
    scanStep ψ ρ p (elimGTm x cl z) (elimGTm x cl f) ≡ scanStep ψ ρ p z f
  scanStep-elimG ψ ρ (d , ev , h) x cl z f =
    cong (λ a → d , proj₁ a , proj₂ a ⊔′ h)
      (trans (cong (λ s → foldGo ψ ρ s (ev , h) d (elimGTm x cl f))
                   (rd-elimGᵗ ψ ρ x cl z))
             (foldGo-elimG ψ ρ (rdᵗ ψ ρ z) (ev , h) d x cl f))

  -- the fold's own congruence, by induction on the refold count.  It is
  -- general in the accumulator because the step changes it, so the
  -- inductive call is at a reading the previous line just rewrote
  foldGo-elimG : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s u t} (ψ : Fin n → Rd₃)
    (ρ : Env) (acc src : Rd) (R : ℕ) (x : t ∈ Δᵍ)
    (cl : Exp Γ [] [] [] t) (f : Fn Γ Δᵍ Δ Θ s u) →
    foldGo ψ ρ acc src R (elimGTm x cl f) ≡ foldGo ψ ρ acc src R f
  foldGo-elimG ψ ρ acc src zero    x cl f = refl
  foldGo-elimG ψ ρ acc src (suc R) x cl f =
    cong (acc ⊔ᴿ_)
      (trans (cong (λ a → foldGo ψ ρ a src R (elimGTm x cl f))
                   (rd-elimGᵗ ψ (ρ ▸ (acc ⊔ᴿ src)) x cl f))
             (foldGo-elimG ψ ρ (rdᵗ ψ (ρ ▸ (acc ⊔ᴿ src)) f) src R x cl f))

  rd-elimGᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (ψ : Fin n → Rd₃) (ρ : Env)
    (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t) (f : Tm Γ Δᵍ Δ Θ u) →
    rdᵗ ψ ρ (elimGTm x cl f) ≡ rdᵗ ψ ρ f
  rd-elimGᵗ ψ ρ x cl (varᵗ y)      = refl
  rd-elimGᵗ ψ ρ x cl unit̂          = refl
  rd-elimGᵗ ψ ρ x cl (bool̂ b)      = refl
  rd-elimGᵗ ψ ρ x cl (nat̂ m)       = refl
  rd-elimGᵗ ψ ρ x cl (pairᵗ a b)   =
    cong₂ _⊔ᴿ_ (rd-elimGᵗ ψ ρ x cl a) (rd-elimGᵗ ψ ρ x cl b)
  rd-elimGᵗ ψ ρ x cl (fstᵗ p)      = rd-elimGᵗ ψ ρ x cl p
  rd-elimGᵗ ψ ρ x cl (sndᵗ p)      = rd-elimGᵗ ψ ρ x cl p
  rd-elimGᵗ ψ ρ x cl (inlᵗ a)      = rd-elimGᵗ ψ ρ x cl a
  rd-elimGᵗ ψ ρ x cl (inrᵗ a)      = rd-elimGᵗ ψ ρ x cl a
  rd-elimGᵗ ψ ρ x cl (caseᵗ s l r) =
    trans (cong (λ p → caseStep ψ ρ p (elimGTm x cl l) (elimGTm x cl r))
                (rd-elimGᵗ ψ ρ x cl s))
          (caseStep-elimG ψ ρ (rdᵗ ψ ρ s) x cl l r)
  rd-elimGᵗ ψ ρ x cl (ifᵗ c a b)   =
    cong₂ _⊔ᴿ_ (rd-elimGᵗ ψ ρ x cl a) (rd-elimGᵗ ψ ρ x cl b)
  rd-elimGᵗ ψ ρ x cl (primᵗ op a)  = refl
  rd-elimGᵗ ψ ρ x cl (strmᵗ b)     = cong topOf (rd-elimGᵉ ψ ρ x cl b)

  caseStep-elimG : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s u v t} (ψ : Fin n → Rd₃)
    (ρ : Env) (p : Rd) (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t)
    (l : Fn Γ Δᵍ Δ Θ s v) (r : Fn Γ Δᵍ Δ Θ u v) →
    caseStep ψ ρ p (elimGTm x cl l) (elimGTm x cl r) ≡ caseStep ψ ρ p l r
  caseStep-elimG ψ ρ p x cl l r =
    cong₂ _⊔ᴿ_ (rd-elimGᵗ ψ (ρ ▸ p) x cl l) (rd-elimGᵗ ψ (ρ ▸ p) x cl r)

  rd-elimGᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (ψ : Fin n → Rd₃) (ρ : Env)
    (x : t ∈ Δᵍ) (cl : Exp Γ [] [] [] t) (ts : List (Tm Γ Δᵍ Δ Θ u)) →
    rdᵗˢ ψ ρ (elimGTms x cl ts) ≡ rdᵗˢ ψ ρ ts
  rd-elimGᵗˢ ψ ρ x cl []       = refl
  rd-elimGᵗˢ ψ ρ x cl (y ∷ ys) =
    cong₂ _⊔ᴿ_ (rd-elimGᵗ ψ ρ x cl y) (rd-elimGᵗˢ ψ ρ x cl ys)

-- THE μ EDGE, in one line: the redex and its unfolding read EQUAL, so
-- the rank component survives the step at no cost and the μ guard pays
-- with the sync component alone.
rd-unfoldμ : ∀ {n} {Γ : Ctx n} {t} (ψ : Fin n → Rd₃) (ρ : Env)
  (body : Exp Γ (t ∷ []) [] [] t) →
  rdᵉ ψ ρ (unfoldμ body) ≡ rdᵉ ψ ρ (μᵉ body)
rd-unfoldμ ψ ρ body = rd-elimGᵉ ψ ρ (here refl) (μᵉ body) body
