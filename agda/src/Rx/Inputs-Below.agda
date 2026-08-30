------------------------------------------------------------------
-- THE INPUT STRATUM IS PRESERVED BY UNFOLDING, which is the one fact
-- the sighted walk's stratum term cannot be stated without.
--
-- `inputsBelowᵉ k e` says every `input i` occurring in `e` has
-- `toℕ i < k`.  The depth walk carries it as a hypothesis so that the
-- descent into a slot's definition can be charged against a STRICTLY
-- SMALLER stratum than the head's: at `input i` the guard hands over
-- `toℕ i < k` definitionally, and the slot's own well-formedness field
-- hands over the definition's stratum.  Nothing else in the walk reads
-- it; every other clause is a congruence.
--
-- THE μ CLAUSE IS WHY THIS IS A MODULE AND NOT A LINE.  The walk peels
-- a gas at `μᵉ` and recurses on `unfoldμ body`, so the hypothesis must
-- survive elimination — and the guard does NOT truncate at the defer
-- gate, unlike the hop and nesting measures, because an input under a
-- gate is still an input into the same context.  So the induction has
-- to follow `elimGExp` all the way through the gate: into `elimDExp`,
-- across the index `subst` that retypes the gate's own context, and
-- into the weakening that the variable-hit clause plants.  That is the
-- same path the synchronous size already walks, and its family is what
-- this one is shaped after.
--
-- TWIN: `size-elimGᵉ` is the proven walk of exactly this path — the
--   same three-way mutual recursion, the same `subst` transport, the
--   same `wkExp` at the hit clause.
------------------------------------------------------------------
module Rx.Inputs-Below where

open import Data.Bool using (Bool; true; false; T; _∧_)
open import Data.Unit using (tt)
open import Data.Nat  using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.Sum  using (inj₁; inj₂)
open import Data.Fin.Properties using (toℕ<n)
open import Data.Nat.Properties using (<⇒<ᵇ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst; cong₂)

open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ)

open import Rx.Exp using (Ctx; Exp; Tm; Closed; Ren∈; ext∈;
                          renExp; renTm; renTms; wkExp;
                          elimGExp; elimGTm; elimGTms;
                          elimDExp; elimDTm; elimDTms;
                          unfoldμ; compare∈; ⊟-++ˡ; ⊟-++ʳ;
                          input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ;
                          mergeAllᵉ; switchAllᵉ; exhaustAllᵉ;
                          μᵉ; varᵉ; deferᵉ;
                          varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ;
                          inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ;
                          inputsBelowᵉ; inputsBelowᵗ; inputsBelowᵗˢ)
open import Decide using (∧ʳ; ∧ˡ)

-- The introduction rule the projections in `Decide` are missing.  The
-- Bools are explicit for the same reason they are there: `T` is a
-- function on Bool and cannot be inverted on a stuck argument.
∧⁺ : ∀ (a b : Bool) → T a → T b → T (a ∧ b)
∧⁺ true  b _ hb = hb
∧⁺ false b () _

------------------------------------------------------------------
-- RENAMING IS INVISIBLE TO THE GUARD: it moves the three binder
-- contexts and never touches Γ, which is where an input's index lives.
mutual
  ib-renᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (k : ℕ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′)
    (e : Exp Γ Δᵍ Δ Θ t) →
    inputsBelowᵉ k (renExp ρg ρd ρt e) ≡ inputsBelowᵉ k e
  ib-renᵉ k ρg ρd ρt (input i)       = refl
  ib-renᵉ k ρg ρd ρt (ofᵉ ts)        = ib-renᵗˢ k ρg ρd ρt ts
  ib-renᵉ k ρg ρd ρt emptyᵉ          = refl
  ib-renᵉ k ρg ρd ρt (mapᵉ f e)      =
    cong₂ _∧_ (ib-renᵗ k ρg ρd (ext∈ ρt) f) (ib-renᵉ k ρg ρd ρt e)
  ib-renᵉ k ρg ρd ρt (takeᵉ c e)     =
    cong₂ _∧_ (ib-renᵗ k ρg ρd ρt c) (ib-renᵉ k ρg ρd ρt e)
  ib-renᵉ k ρg ρd ρt (scanᵉ f z e)   =
    cong₂ _∧_ (ib-renᵗ k ρg ρd (ext∈ ρt) f)
              (cong₂ _∧_ (ib-renᵗ k ρg ρd ρt z) (ib-renᵉ k ρg ρd ρt e))
  ib-renᵉ k ρg ρd ρt (mergeAllᵉ _ e) = ib-renᵉ k ρg ρd ρt e
  ib-renᵉ k ρg ρd ρt (switchAllᵉ e)  = ib-renᵉ k ρg ρd ρt e
  ib-renᵉ k ρg ρd ρt (exhaustAllᵉ e) = ib-renᵉ k ρg ρd ρt e
  ib-renᵉ k ρg ρd ρt (μᵉ e)          = ib-renᵉ k (ext∈ ρg) ρd ρt e
  ib-renᵉ k ρg ρd ρt (varᵉ x)        = refl
  ib-renᵉ k ρg ρd ρt (deferᵉ e)      = ib-renᵉ k (λ ()) _ ρt e

  ib-renᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (k : ℕ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′)
    (tm : Tm Γ Δᵍ Δ Θ t) →
    inputsBelowᵗ k (renTm ρg ρd ρt tm) ≡ inputsBelowᵗ k tm
  ib-renᵗ k ρg ρd ρt (varᵗ x)      = refl
  ib-renᵗ k ρg ρd ρt unit̂          = refl
  ib-renᵗ k ρg ρd ρt (bool̂ _)      = refl
  ib-renᵗ k ρg ρd ρt (nat̂ _)       = refl
  ib-renᵗ k ρg ρd ρt (pairᵗ a b)   =
    cong₂ _∧_ (ib-renᵗ k ρg ρd ρt a) (ib-renᵗ k ρg ρd ρt b)
  ib-renᵗ k ρg ρd ρt (fstᵗ p)      = ib-renᵗ k ρg ρd ρt p
  ib-renᵗ k ρg ρd ρt (sndᵗ p)      = ib-renᵗ k ρg ρd ρt p
  ib-renᵗ k ρg ρd ρt (inlᵗ a)      = ib-renᵗ k ρg ρd ρt a
  ib-renᵗ k ρg ρd ρt (inrᵗ a)      = ib-renᵗ k ρg ρd ρt a
  ib-renᵗ k ρg ρd ρt (caseᵗ s l r) =
    cong₂ _∧_ (ib-renᵗ k ρg ρd ρt s)
              (cong₂ _∧_ (ib-renᵗ k ρg ρd (ext∈ ρt) l)
                         (ib-renᵗ k ρg ρd (ext∈ ρt) r))
  ib-renᵗ k ρg ρd ρt (ifᵗ c a b)   =
    cong₂ _∧_ (ib-renᵗ k ρg ρd ρt c)
              (cong₂ _∧_ (ib-renᵗ k ρg ρd ρt a) (ib-renᵗ k ρg ρd ρt b))
  ib-renᵗ k ρg ρd ρt (primᵗ _ a)   = ib-renᵗ k ρg ρd ρt a
  ib-renᵗ k ρg ρd ρt (strmᵗ e)     = ib-renᵉ k ρg ρd ρt e

  ib-renᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (k : ℕ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′)
    (ts : List (Tm Γ Δᵍ Δ Θ t)) →
    inputsBelowᵗˢ k (renTms ρg ρd ρt ts) ≡ inputsBelowᵗˢ k ts
  ib-renᵗˢ k ρg ρd ρt []       = refl
  ib-renᵗˢ k ρg ρd ρt (y ∷ ys) =
    cong₂ _∧_ (ib-renᵗ k ρg ρd ρt y) (ib-renᵗˢ k ρg ρd ρt ys)

ib-wk : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (k : ℕ) (e : Closed Γ t) →
  T (inputsBelowᵉ k e) → T (inputsBelowᵉ k (wkExp {Δᵍ = Δᵍ} {Δ} {Θ} e))
ib-wk k e h = subst T (sym (ib-renᵉ k (λ ()) (λ ()) (λ ()) e)) h

-- The gate's own index coercion is transparent to the guard.
ib-substᴱ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Δ′ Θ t} (k : ℕ) (p : Δ ≡ Δ′)
  (e : Exp Γ Δᵍ Δ Θ t) →
  inputsBelowᵉ k (subst (λ ζ → Exp Γ Δᵍ ζ Θ t) p e) ≡ inputsBelowᵉ k e
ib-substᴱ k refl e = refl

------------------------------------------------------------------
-- ELIMINATION PRESERVES THE GUARD, given it of the closure being
-- planted.  Only elimD's variable-hit clause plants anything; every
-- other clause is a congruence, and the gate is followed through
-- rather than truncated at.
mutual
  ib-elimGᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (k : ℕ) (x : t ∈ Δᵍ)
    (cl : Closed Γ t) → T (inputsBelowᵉ k cl) →
    (e : Exp Γ Δᵍ Δ Θ u) → T (inputsBelowᵉ k e) →
    T (inputsBelowᵉ k (elimGExp x cl e))
  ib-elimGᵉ k x cl hcl (input i)       ok = ok
  ib-elimGᵉ k x cl hcl (ofᵉ ts)        ok = ib-elimGᵗˢ k x cl hcl ts ok
  ib-elimGᵉ k x cl hcl emptyᵉ          ok = tt
  ib-elimGᵉ k x cl hcl (mapᵉ f e)      ok =
    ∧⁺ (inputsBelowᵗ k (elimGTm x cl f)) (inputsBelowᵉ k (elimGExp x cl e))
       (ib-elimGᵗ k x cl hcl f (∧ˡ (inputsBelowᵗ k f) (inputsBelowᵉ k e) ok))
       (ib-elimGᵉ k x cl hcl e (∧ʳ (inputsBelowᵗ k f) (inputsBelowᵉ k e) ok))
  ib-elimGᵉ k x cl hcl (takeᵉ c e)     ok =
    ∧⁺ (inputsBelowᵗ k (elimGTm x cl c)) (inputsBelowᵉ k (elimGExp x cl e))
       (ib-elimGᵗ k x cl hcl c (∧ˡ (inputsBelowᵗ k c) (inputsBelowᵉ k e) ok))
       (ib-elimGᵉ k x cl hcl e (∧ʳ (inputsBelowᵗ k c) (inputsBelowᵉ k e) ok))
  ib-elimGᵉ k x cl hcl (scanᵉ f z e)   ok =
    ∧⁺ (inputsBelowᵗ k (elimGTm x cl f))
       (inputsBelowᵗ k (elimGTm x cl z) ∧ inputsBelowᵉ k (elimGExp x cl e))
       (ib-elimGᵗ k x cl hcl f (∧ˡ (inputsBelowᵗ k f) zbe ok))
       (∧⁺ (inputsBelowᵗ k (elimGTm x cl z)) (inputsBelowᵉ k (elimGExp x cl e))
           (ib-elimGᵗ k x cl hcl z
             (∧ˡ (inputsBelowᵗ k z) (inputsBelowᵉ k e) rest))
           (ib-elimGᵉ k x cl hcl e
             (∧ʳ (inputsBelowᵗ k z) (inputsBelowᵉ k e) rest)))
    where
      zbe = inputsBelowᵗ k z ∧ inputsBelowᵉ k e
      rest = ∧ʳ (inputsBelowᵗ k f) zbe ok
  ib-elimGᵉ k x cl hcl (mergeAllᵉ _ e) ok = ib-elimGᵉ k x cl hcl e ok
  ib-elimGᵉ k x cl hcl (switchAllᵉ e)  ok = ib-elimGᵉ k x cl hcl e ok
  ib-elimGᵉ k x cl hcl (exhaustAllᵉ e) ok = ib-elimGᵉ k x cl hcl e ok
  ib-elimGᵉ k x cl hcl (μᵉ e)          ok = ib-elimGᵉ k (there x) cl hcl e ok
  ib-elimGᵉ k x cl hcl (varᵉ y)        ok = tt
  ib-elimGᵉ k x cl hcl (deferᵉ e)      ok =
    subst T (sym (ib-substᴱ k (⊟-++ˡ x) (elimDExp (∈-++⁺ˡ x) cl e)))
            (ib-elimDᵉ k (∈-++⁺ˡ x) cl hcl e ok)

  ib-elimGᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (k : ℕ) (x : t ∈ Δᵍ)
    (cl : Closed Γ t) → T (inputsBelowᵉ k cl) →
    (tm : Tm Γ Δᵍ Δ Θ u) → T (inputsBelowᵗ k tm) →
    T (inputsBelowᵗ k (elimGTm x cl tm))
  ib-elimGᵗ k x cl hcl (varᵗ y)      ok = tt
  ib-elimGᵗ k x cl hcl unit̂          ok = tt
  ib-elimGᵗ k x cl hcl (bool̂ _)      ok = tt
  ib-elimGᵗ k x cl hcl (nat̂ _)       ok = tt
  ib-elimGᵗ k x cl hcl (pairᵗ a b)   ok =
    ∧⁺ (inputsBelowᵗ k (elimGTm x cl a)) (inputsBelowᵗ k (elimGTm x cl b))
       (ib-elimGᵗ k x cl hcl a (∧ˡ (inputsBelowᵗ k a) (inputsBelowᵗ k b) ok))
       (ib-elimGᵗ k x cl hcl b (∧ʳ (inputsBelowᵗ k a) (inputsBelowᵗ k b) ok))
  ib-elimGᵗ k x cl hcl (fstᵗ p)      ok = ib-elimGᵗ k x cl hcl p ok
  ib-elimGᵗ k x cl hcl (sndᵗ p)      ok = ib-elimGᵗ k x cl hcl p ok
  ib-elimGᵗ k x cl hcl (inlᵗ a)      ok = ib-elimGᵗ k x cl hcl a ok
  ib-elimGᵗ k x cl hcl (inrᵗ a)      ok = ib-elimGᵗ k x cl hcl a ok
  ib-elimGᵗ k x cl hcl (caseᵗ s l r) ok =
    ∧⁺ (inputsBelowᵗ k (elimGTm x cl s))
       (inputsBelowᵗ k (elimGTm x cl l) ∧ inputsBelowᵗ k (elimGTm x cl r))
       (ib-elimGᵗ k x cl hcl s (∧ˡ (inputsBelowᵗ k s) lr ok))
       (∧⁺ (inputsBelowᵗ k (elimGTm x cl l)) (inputsBelowᵗ k (elimGTm x cl r))
           (ib-elimGᵗ k x cl hcl l
             (∧ˡ (inputsBelowᵗ k l) (inputsBelowᵗ k r) rest))
           (ib-elimGᵗ k x cl hcl r
             (∧ʳ (inputsBelowᵗ k l) (inputsBelowᵗ k r) rest)))
    where
      lr   = inputsBelowᵗ k l ∧ inputsBelowᵗ k r
      rest = ∧ʳ (inputsBelowᵗ k s) lr ok
  ib-elimGᵗ k x cl hcl (ifᵗ c a b)   ok =
    ∧⁺ (inputsBelowᵗ k (elimGTm x cl c))
       (inputsBelowᵗ k (elimGTm x cl a) ∧ inputsBelowᵗ k (elimGTm x cl b))
       (ib-elimGᵗ k x cl hcl c (∧ˡ (inputsBelowᵗ k c) ab ok))
       (∧⁺ (inputsBelowᵗ k (elimGTm x cl a)) (inputsBelowᵗ k (elimGTm x cl b))
           (ib-elimGᵗ k x cl hcl a
             (∧ˡ (inputsBelowᵗ k a) (inputsBelowᵗ k b) rest))
           (ib-elimGᵗ k x cl hcl b
             (∧ʳ (inputsBelowᵗ k a) (inputsBelowᵗ k b) rest)))
    where
      ab   = inputsBelowᵗ k a ∧ inputsBelowᵗ k b
      rest = ∧ʳ (inputsBelowᵗ k c) ab ok
  ib-elimGᵗ k x cl hcl (primᵗ _ a)   ok = ib-elimGᵗ k x cl hcl a ok
  ib-elimGᵗ k x cl hcl (strmᵗ e)     ok = ib-elimGᵉ k x cl hcl e ok

  ib-elimGᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (k : ℕ) (x : t ∈ Δᵍ)
    (cl : Closed Γ t) → T (inputsBelowᵉ k cl) →
    (ts : List (Tm Γ Δᵍ Δ Θ u)) → T (inputsBelowᵗˢ k ts) →
    T (inputsBelowᵗˢ k (elimGTms x cl ts))
  ib-elimGᵗˢ k x cl hcl []       ok = tt
  ib-elimGᵗˢ k x cl hcl (y ∷ ys) ok =
    ∧⁺ (inputsBelowᵗ k (elimGTm x cl y)) (inputsBelowᵗˢ k (elimGTms x cl ys))
       (ib-elimGᵗ k x cl hcl y (∧ˡ (inputsBelowᵗ k y) (inputsBelowᵗˢ k ys) ok))
       (ib-elimGᵗˢ k x cl hcl ys (∧ʳ (inputsBelowᵗ k y) (inputsBelowᵗˢ k ys) ok))

  ib-elimDᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (k : ℕ) (x : t ∈ Δ)
    (cl : Closed Γ t) → T (inputsBelowᵉ k cl) →
    (e : Exp Γ Δᵍ Δ Θ u) → T (inputsBelowᵉ k e) →
    T (inputsBelowᵉ k (elimDExp x cl e))
  ib-elimDᵉ k x cl hcl (input i)       ok = ok
  ib-elimDᵉ k x cl hcl (ofᵉ ts)        ok = ib-elimDᵗˢ k x cl hcl ts ok
  ib-elimDᵉ k x cl hcl emptyᵉ          ok = tt
  ib-elimDᵉ k x cl hcl (mapᵉ f e)      ok =
    ∧⁺ (inputsBelowᵗ k (elimDTm x cl f)) (inputsBelowᵉ k (elimDExp x cl e))
       (ib-elimDᵗ k x cl hcl f (∧ˡ (inputsBelowᵗ k f) (inputsBelowᵉ k e) ok))
       (ib-elimDᵉ k x cl hcl e (∧ʳ (inputsBelowᵗ k f) (inputsBelowᵉ k e) ok))
  ib-elimDᵉ k x cl hcl (takeᵉ c e)     ok =
    ∧⁺ (inputsBelowᵗ k (elimDTm x cl c)) (inputsBelowᵉ k (elimDExp x cl e))
       (ib-elimDᵗ k x cl hcl c (∧ˡ (inputsBelowᵗ k c) (inputsBelowᵉ k e) ok))
       (ib-elimDᵉ k x cl hcl e (∧ʳ (inputsBelowᵗ k c) (inputsBelowᵉ k e) ok))
  ib-elimDᵉ k x cl hcl (scanᵉ f z e)   ok =
    ∧⁺ (inputsBelowᵗ k (elimDTm x cl f))
       (inputsBelowᵗ k (elimDTm x cl z) ∧ inputsBelowᵉ k (elimDExp x cl e))
       (ib-elimDᵗ k x cl hcl f (∧ˡ (inputsBelowᵗ k f) zbe ok))
       (∧⁺ (inputsBelowᵗ k (elimDTm x cl z)) (inputsBelowᵉ k (elimDExp x cl e))
           (ib-elimDᵗ k x cl hcl z
             (∧ˡ (inputsBelowᵗ k z) (inputsBelowᵉ k e) rest))
           (ib-elimDᵉ k x cl hcl e
             (∧ʳ (inputsBelowᵗ k z) (inputsBelowᵉ k e) rest)))
    where
      zbe  = inputsBelowᵗ k z ∧ inputsBelowᵉ k e
      rest = ∧ʳ (inputsBelowᵗ k f) zbe ok
  ib-elimDᵉ k x cl hcl (mergeAllᵉ _ e) ok = ib-elimDᵉ k x cl hcl e ok
  ib-elimDᵉ k x cl hcl (switchAllᵉ e)  ok = ib-elimDᵉ k x cl hcl e ok
  ib-elimDᵉ k x cl hcl (exhaustAllᵉ e) ok = ib-elimDᵉ k x cl hcl e ok
  ib-elimDᵉ k x cl hcl (μᵉ e)          ok = ib-elimDᵉ k x cl hcl e ok
  ib-elimDᵉ k x cl hcl (varᵉ y)        ok with compare∈ x y
  ... | inj₁ refl = ib-wk k cl hcl
  ... | inj₂ y′   = tt
  ib-elimDᵉ {Δᵍ = Δᵍ} k x cl hcl (deferᵉ e) ok =
    subst T (sym (ib-substᴱ k (⊟-++ʳ {Δᵍ = Δᵍ} x)
                    (elimDExp (∈-++⁺ʳ Δᵍ x) cl e)))
            (ib-elimDᵉ k (∈-++⁺ʳ Δᵍ x) cl hcl e ok)

  ib-elimDᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (k : ℕ) (x : t ∈ Δ)
    (cl : Closed Γ t) → T (inputsBelowᵉ k cl) →
    (tm : Tm Γ Δᵍ Δ Θ u) → T (inputsBelowᵗ k tm) →
    T (inputsBelowᵗ k (elimDTm x cl tm))
  ib-elimDᵗ k x cl hcl (varᵗ y)      ok = tt
  ib-elimDᵗ k x cl hcl unit̂          ok = tt
  ib-elimDᵗ k x cl hcl (bool̂ _)      ok = tt
  ib-elimDᵗ k x cl hcl (nat̂ _)       ok = tt
  ib-elimDᵗ k x cl hcl (pairᵗ a b)   ok =
    ∧⁺ (inputsBelowᵗ k (elimDTm x cl a)) (inputsBelowᵗ k (elimDTm x cl b))
       (ib-elimDᵗ k x cl hcl a (∧ˡ (inputsBelowᵗ k a) (inputsBelowᵗ k b) ok))
       (ib-elimDᵗ k x cl hcl b (∧ʳ (inputsBelowᵗ k a) (inputsBelowᵗ k b) ok))
  ib-elimDᵗ k x cl hcl (fstᵗ p)      ok = ib-elimDᵗ k x cl hcl p ok
  ib-elimDᵗ k x cl hcl (sndᵗ p)      ok = ib-elimDᵗ k x cl hcl p ok
  ib-elimDᵗ k x cl hcl (inlᵗ a)      ok = ib-elimDᵗ k x cl hcl a ok
  ib-elimDᵗ k x cl hcl (inrᵗ a)      ok = ib-elimDᵗ k x cl hcl a ok
  ib-elimDᵗ k x cl hcl (caseᵗ s l r) ok =
    ∧⁺ (inputsBelowᵗ k (elimDTm x cl s))
       (inputsBelowᵗ k (elimDTm x cl l) ∧ inputsBelowᵗ k (elimDTm x cl r))
       (ib-elimDᵗ k x cl hcl s (∧ˡ (inputsBelowᵗ k s) lr ok))
       (∧⁺ (inputsBelowᵗ k (elimDTm x cl l)) (inputsBelowᵗ k (elimDTm x cl r))
           (ib-elimDᵗ k x cl hcl l
             (∧ˡ (inputsBelowᵗ k l) (inputsBelowᵗ k r) rest))
           (ib-elimDᵗ k x cl hcl r
             (∧ʳ (inputsBelowᵗ k l) (inputsBelowᵗ k r) rest)))
    where
      lr   = inputsBelowᵗ k l ∧ inputsBelowᵗ k r
      rest = ∧ʳ (inputsBelowᵗ k s) lr ok
  ib-elimDᵗ k x cl hcl (ifᵗ c a b)   ok =
    ∧⁺ (inputsBelowᵗ k (elimDTm x cl c))
       (inputsBelowᵗ k (elimDTm x cl a) ∧ inputsBelowᵗ k (elimDTm x cl b))
       (ib-elimDᵗ k x cl hcl c (∧ˡ (inputsBelowᵗ k c) ab ok))
       (∧⁺ (inputsBelowᵗ k (elimDTm x cl a)) (inputsBelowᵗ k (elimDTm x cl b))
           (ib-elimDᵗ k x cl hcl a
             (∧ˡ (inputsBelowᵗ k a) (inputsBelowᵗ k b) rest))
           (ib-elimDᵗ k x cl hcl b
             (∧ʳ (inputsBelowᵗ k a) (inputsBelowᵗ k b) rest)))
    where
      ab   = inputsBelowᵗ k a ∧ inputsBelowᵗ k b
      rest = ∧ʳ (inputsBelowᵗ k c) ab ok
  ib-elimDᵗ k x cl hcl (primᵗ _ a)   ok = ib-elimDᵗ k x cl hcl a ok
  ib-elimDᵗ k x cl hcl (strmᵗ e)     ok = ib-elimDᵉ k x cl hcl e ok

  ib-elimDᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (k : ℕ) (x : t ∈ Δ)
    (cl : Closed Γ t) → T (inputsBelowᵉ k cl) →
    (ts : List (Tm Γ Δᵍ Δ Θ u)) → T (inputsBelowᵗˢ k ts) →
    T (inputsBelowᵗˢ k (elimDTms x cl ts))
  ib-elimDᵗˢ k x cl hcl []       ok = tt
  ib-elimDᵗˢ k x cl hcl (y ∷ ys) ok =
    ∧⁺ (inputsBelowᵗ k (elimDTm x cl y)) (inputsBelowᵗˢ k (elimDTms x cl ys))
       (ib-elimDᵗ k x cl hcl y (∧ˡ (inputsBelowᵗ k y) (inputsBelowᵗˢ k ys) ok))
       (ib-elimDᵗˢ k x cl hcl ys (∧ʳ (inputsBelowᵗ k y) (inputsBelowᵗˢ k ys) ok))

-- THE CLAUSE THE WALK SPENDS: the guard survives one μ peel.
ib-unfoldμ : ∀ {n} {Γ : Ctx n} {t} (k : ℕ) (body : Exp Γ (t ∷ []) [] [] t) →
  T (inputsBelowᵉ k (μᵉ body)) → T (inputsBelowᵉ k (unfoldμ body))
ib-unfoldμ k body ok = ib-elimGᵉ k (here refl) (μᵉ body) ok body ok

-- EVERY PROGRAM SITS AT THE TOP STRATUM, which is how the root of the
-- walk discharges the hypothesis with nothing to supply it.
mutual
  ib-topᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (e : Exp Γ Δᵍ Δ Θ t) →
    T (inputsBelowᵉ n e)
  ib-topᵉ (input i)       = <⇒<ᵇ (toℕ<n i)
  ib-topᵉ (ofᵉ ts)        = ib-topᵗˢ ts
  ib-topᵉ emptyᵉ          = tt
  ib-topᵉ (mapᵉ f e)      =
    ∧⁺ _ _ (ib-topᵗ f) (ib-topᵉ e)
  ib-topᵉ (takeᵉ c e)     =
    ∧⁺ _ _ (ib-topᵗ c) (ib-topᵉ e)
  ib-topᵉ (scanᵉ f z e)   =
    ∧⁺ _ _ (ib-topᵗ f) (∧⁺ _ _ (ib-topᵗ z) (ib-topᵉ e))
  ib-topᵉ (mergeAllᵉ _ e) = ib-topᵉ e
  ib-topᵉ (switchAllᵉ e)  = ib-topᵉ e
  ib-topᵉ (exhaustAllᵉ e) = ib-topᵉ e
  ib-topᵉ (μᵉ e)          = ib-topᵉ e
  ib-topᵉ (varᵉ x)        = tt
  ib-topᵉ (deferᵉ e)      = ib-topᵉ e

  ib-topᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (tm : Tm Γ Δᵍ Δ Θ t) →
    T (inputsBelowᵗ n tm)
  ib-topᵗ (varᵗ x)      = tt
  ib-topᵗ unit̂          = tt
  ib-topᵗ (bool̂ _)      = tt
  ib-topᵗ (nat̂ _)       = tt
  ib-topᵗ (pairᵗ a b)   = ∧⁺ _ _ (ib-topᵗ a) (ib-topᵗ b)
  ib-topᵗ (fstᵗ p)      = ib-topᵗ p
  ib-topᵗ (sndᵗ p)      = ib-topᵗ p
  ib-topᵗ (inlᵗ a)      = ib-topᵗ a
  ib-topᵗ (inrᵗ a)      = ib-topᵗ a
  ib-topᵗ (caseᵗ s l r) = ∧⁺ _ _ (ib-topᵗ s) (∧⁺ _ _ (ib-topᵗ l) (ib-topᵗ r))
  ib-topᵗ (ifᵗ c a b)   = ∧⁺ _ _ (ib-topᵗ c) (∧⁺ _ _ (ib-topᵗ a) (ib-topᵗ b))
  ib-topᵗ (primᵗ _ a)   = ib-topᵗ a
  ib-topᵗ (strmᵗ e)     = ib-topᵉ e

  ib-topᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (ts : List (Tm Γ Δᵍ Δ Θ t)) →
    T (inputsBelowᵗˢ n ts)
  ib-topᵗˢ []       = tt
  ib-topᵗˢ (y ∷ ys) = ∧⁺ _ _ (ib-topᵗ y) (ib-topᵗˢ ys)
