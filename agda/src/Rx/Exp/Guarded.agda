------------------------------------------------------------------
-- THE MEASURE A μ UNFOLDING DOES NOT MOVE.
------------------------------------------------------------------

-- WHY A FIXPOINT AT ONE TYPE IS STILL A DESCENT.  The reducibility
-- candidate recurses on the TYPE, which the flatteners move strictly
-- down and the term-structural formers leave alone; a μ moves neither,
-- since its unfolding sits at the same type and is no subterm of the
-- fixpoint.  That reads as the one edge nothing can pay for, and it is
-- not, because the SYNTAX has already paid: `μᵉ` binds its variable
-- into the guarded context and `varᵉ` reads only from the usable one,
-- so a synchronous self-reference does not typecheck at all and every
-- recursive occurrence sits under a `deferᵉ`.
--
-- WHAT MAKES THAT A MEASURE RATHER THAN AN OBSERVATION.  The gate is
-- visible in the ELIMINATOR: the guarded-context elimination never
-- substitutes anything, its variable clause is the identity, and its
-- single route to the clause that DOES substitute is its `deferᵉ`
-- clause.  So a size that stops at a `deferᵉ` cannot see any inserted
-- copy, and the unfolding has exactly the size the body had.  The μ
-- former is the one thing that spends a unit, which is what makes the
-- peel a strict decrease.
--
-- AND IT COUNTS TERMS, WHICH IS WHAT PAYS FOR THE OTHER DESCENT.  A
-- term can carry an expression, and the fundamental theorem at terms
-- is a mutual partner of the expression recursion rather than a leaf
-- beside it, so the partner's own descent — from a frame's function
-- into the expression that function embeds — has to be funded here or
-- nowhere.  Counting is free of the gate argument above: the two
-- clauses that could see an inserted copy are the variable, which this
-- elimination leaves alone, and the gate, where the size stops — and
-- that stays true however deep inside a term the copy lands, since a
-- term's own route to an inserted copy is through an expression and
-- therefore through the same gate.
--
-- WHAT IT MUST NOT BE ASKED IS A SUBSTITUTION IT DOES NOT SEE.  This
-- counts RAW syntax, and the value environment a term is evaluated
-- under is arbitrary — an entry at observable type is a whole
-- expression — so the substituted copy is unbounded against the term
-- that binds it.  The partner therefore carries its environment and
-- recurses on the unsubstituted syntax, and the measure is read off
-- that; a partner stated over the substituted expression cannot be
-- funded by this size or by any other on the syntax.
module Rx.Exp.Guarded where

open import Data.List using ([]; _∷_; List; _++_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Rx.Exp using (Ctx; Ty; Exp; Tm; elimGExp; elimGTm; elimGTms; unfoldμ;
  input; ofᵉ; emptyᵉ; takeᵉ; liftᵉ; mergeAllᵉ; switchAllᵉ;
  exhaustAllᵉ; μᵉ; varᵉ; deferᵉ;
  varᵗ; unit̂; bool̂; nat̂; uniq̂; pairᵗ; fstᵗ; sndᵗ; inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ;
  nilᵗ; consᵗ; foldᵗ)

-- The size, counting the formers a subscription actually descends
-- through — an operator's own spine and the terms it carries — and
-- stopping at the gate.
mutual
  gsizeᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Exp Γ Δᵍ Δ Θ t → ℕ
  gsizeᵉ (input i)         = zero
  gsizeᵉ (ofᵉ ts)          = suc (gsizeᵗˢ ts)
  gsizeᵉ emptyᵉ            = zero
  gsizeᵉ (takeᵉ c e)       = suc (gsizeᵗ c + gsizeᵉ e)
  gsizeᵉ (liftᵉ f z e)     = suc (gsizeᵗ f + (gsizeᵗ z + gsizeᵉ e))
  gsizeᵉ (mergeAllᵉ lim e) = suc (gsizeᵉ e)
  gsizeᵉ (switchAllᵉ e)    = suc (gsizeᵉ e)
  gsizeᵉ (exhaustAllᵉ e)   = suc (gsizeᵉ e)
  gsizeᵉ (μᵉ e)            = suc (gsizeᵉ e)
  gsizeᵉ (varᵉ x)          = zero
  gsizeᵉ (deferᵉ e)        = zero

  gsizeᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Tm Γ Δᵍ Δ Θ t → ℕ
  gsizeᵗ (varᵗ x)     = zero
  gsizeᵗ unit̂         = zero
  gsizeᵗ (bool̂ b)     = zero
  gsizeᵗ (nat̂ k)      = zero
  gsizeᵗ (uniq̂ k)      = zero
  gsizeᵗ nilᵗ         = zero
  gsizeᵗ (consᵗ a as) = suc (gsizeᵗ a + gsizeᵗ as)
  gsizeᵗ (foldᵗ l z f) = suc (gsizeᵗ l + (gsizeᵗ z + gsizeᵗ f))
  gsizeᵗ (pairᵗ a b)  = suc (gsizeᵗ a + gsizeᵗ b)
  gsizeᵗ (fstᵗ p)     = suc (gsizeᵗ p)
  gsizeᵗ (sndᵗ p)     = suc (gsizeᵗ p)
  gsizeᵗ (inlᵗ a)     = suc (gsizeᵗ a)
  gsizeᵗ (inrᵗ a)     = suc (gsizeᵗ a)
  gsizeᵗ (caseᵗ s l r) = suc (gsizeᵗ s + (gsizeᵗ l + gsizeᵗ r))
  gsizeᵗ (ifᵗ c a b)  = suc (gsizeᵗ c + (gsizeᵗ a + gsizeᵗ b))
  gsizeᵗ (primᵗ op a) = suc (gsizeᵗ a)
  gsizeᵗ (strmᵗ e)    = suc (gsizeᵉ e)

  gsizeᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → List (Tm Γ Δᵍ Δ Θ t) → ℕ
  gsizeᵗˢ []       = zero
  gsizeᵗˢ (t ∷ ts) = suc (gsizeᵗ t + gsizeᵗˢ ts)

-- THE WHOLE CONTENT, AND IT IS ONE LINE PER FORMER.  The two clauses
-- that carry the argument are the variable and the gate, and both are
-- constant: the variable is untouched by this elimination and the gate
-- is where the size stops looking.  Everything else is a congruence,
-- the term half included — a term's only way to reach an inserted copy
-- is an expression it embeds, so it arrives at the same two clauses.
mutual
  gsize-elimG : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub u t} (Θloc : List Ty) (x : t ∈ Δᵍ)
                (cl : Exp Γ [] [] Θsub t) (e : Exp Γ Δᵍ Δ (Θloc ++ Θsub) u)
              → gsizeᵉ (elimGExp Θloc x cl e) ≡ gsizeᵉ e
  gsize-elimG Θl x cl (input i)         = refl
  gsize-elimG Θl x cl (ofᵉ ts)          = cong suc (gsize-elimGs Θl x cl ts)
  gsize-elimG Θl x cl emptyᵉ            = refl
  gsize-elimG Θl x cl (takeᵉ c e)       =
    cong suc (cong₂ _+_ (gsize-elimGt Θl x cl c) (gsize-elimG Θl x cl e))
  gsize-elimG Θl x cl (liftᵉ f z e)     =
    cong suc (cong₂ _+_ (gsize-elimGt (_ ∷ Θl) x cl f)
                        (cong₂ _+_ (gsize-elimGt Θl x cl z) (gsize-elimG Θl x cl e)))
  gsize-elimG Θl x cl (mergeAllᵉ lim e) = cong suc (gsize-elimG Θl x cl e)
  gsize-elimG Θl x cl (switchAllᵉ e)    = cong suc (gsize-elimG Θl x cl e)
  gsize-elimG Θl x cl (exhaustAllᵉ e)   = cong suc (gsize-elimG Θl x cl e)
  gsize-elimG Θl x cl (μᵉ e)            = cong suc (gsize-elimG Θl (there x) cl e)
  gsize-elimG Θl x cl (varᵉ y)          = refl
  gsize-elimG Θl x cl (deferᵉ e)        = refl

  gsize-elimGt : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub u t} (Θloc : List Ty) (x : t ∈ Δᵍ)
                 (cl : Exp Γ [] [] Θsub t) (tm : Tm Γ Δᵍ Δ (Θloc ++ Θsub) u)
               → gsizeᵗ (elimGTm Θloc x cl tm) ≡ gsizeᵗ tm
  gsize-elimGt Θl x cl (varᵗ y)      = refl
  gsize-elimGt Θl x cl unit̂          = refl
  gsize-elimGt Θl x cl (bool̂ b)      = refl
  gsize-elimGt Θl x cl (nat̂ k)       = refl
  gsize-elimGt Θl x cl (uniq̂ k)       = refl
  gsize-elimGt Θl x cl nilᵗ          = refl
  gsize-elimGt Θl x cl (consᵗ a as)  =
    cong suc (cong₂ _+_ (gsize-elimGt Θl x cl a) (gsize-elimGt Θl x cl as))
  gsize-elimGt Θl x cl (foldᵗ l z f) =
    cong suc (cong₂ _+_ (gsize-elimGt Θl x cl l)
                        (cong₂ _+_ (gsize-elimGt Θl x cl z)
                                   (gsize-elimGt (_ ∷ _ ∷ Θl) x cl f)))
  gsize-elimGt Θl x cl (pairᵗ a b)   =
    cong suc (cong₂ _+_ (gsize-elimGt Θl x cl a) (gsize-elimGt Θl x cl b))
  gsize-elimGt Θl x cl (fstᵗ p)      = cong suc (gsize-elimGt Θl x cl p)
  gsize-elimGt Θl x cl (sndᵗ p)      = cong suc (gsize-elimGt Θl x cl p)
  gsize-elimGt Θl x cl (inlᵗ a)      = cong suc (gsize-elimGt Θl x cl a)
  gsize-elimGt Θl x cl (inrᵗ a)      = cong suc (gsize-elimGt Θl x cl a)
  gsize-elimGt Θl x cl (caseᵗ s l r) =
    cong suc (cong₂ _+_ (gsize-elimGt Θl x cl s)
                        (cong₂ _+_ (gsize-elimGt (_ ∷ Θl) x cl l) (gsize-elimGt (_ ∷ Θl) x cl r)))
  gsize-elimGt Θl x cl (ifᵗ c a b)   =
    cong suc (cong₂ _+_ (gsize-elimGt Θl x cl c)
                        (cong₂ _+_ (gsize-elimGt Θl x cl a) (gsize-elimGt Θl x cl b)))
  gsize-elimGt Θl x cl (primᵗ op a)  = cong suc (gsize-elimGt Θl x cl a)
  gsize-elimGt Θl x cl (strmᵗ e)     = cong suc (gsize-elimG Θl x cl e)

  gsize-elimGs : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub u t} (Θloc : List Ty) (x : t ∈ Δᵍ)
                 (cl : Exp Γ [] [] Θsub t) (ts : List (Tm Γ Δᵍ Δ (Θloc ++ Θsub) u))
               → gsizeᵗˢ (elimGTms Θloc x cl ts) ≡ gsizeᵗˢ ts
  gsize-elimGs Θl x cl []       = refl
  gsize-elimGs Θl x cl (t ∷ ts) =
    cong suc (cong₂ _+_ (gsize-elimGt Θl x cl t) (gsize-elimGs Θl x cl ts))

-- THE PEEL, WHICH IS THE LEMMA ABOVE AT THE ONE POSITION THAT MATTERS.
gsize-unfoldμ : ∀ {n} {Γ : Ctx n} {Θ t} (body : Exp Γ (t ∷ []) [] Θ t)
              → gsizeᵉ (unfoldμ body) ≡ gsizeᵉ body
gsize-unfoldμ body = gsize-elimG [] (here refl) (μᵉ body) body
