------------------------------------------------------------------
-- THE INPUT STRATUM IS PRESERVED BY UNFOLDING, which is the one fact
-- the reducibility walk's ceiling cannot be threaded without.
--
-- `inputsBelowᵉ k e` says every `input i` occurring in `e` has
-- `toℕ i < k`.  The candidate's accumulating face carries it as a
-- measure component so that the descent into a SHARED SLOT's
-- definition can be charged against a STRICTLY SMALLER ceiling than
-- the head's: at `input i` the guard hands over `toℕ i < k`
-- definitionally, and the slot's own well-formedness field hands over
-- the definition's stratum.  Nothing else in that walk reads it; every
-- other clause passes the ceiling through untouched.
--
-- THE μ CLAUSE IS WHY THIS IS A MODULE AND NOT A LINE.  The walk peels
-- a μ and recurses on `unfoldμ body`, so the hypothesis must survive
-- elimination — and the guard does NOT truncate at the defer gate,
-- because an input under a gate is still an input into the same
-- context.  So the induction has to follow `elimGExp` all the way
-- through the gate: into `elimDExp`, across the index `subst` that
-- retypes the gate's own context, and into the renaming that the
-- variable-hit clause plants.
--
-- AND THE ROOT NEEDS NOTHING SUPPLIED TO IT.  `ib-topᵉ` reads every
-- program at the ceiling `n`, which is free because `toℕ i < n` holds
-- of every `i : Fin n` — so the top line of the reducibility argument
-- instantiates the measure without a hypothesis of its own, and the
-- ceiling stays internal to the recursion rather than leaking into any
-- statement the tower exports.
------------------------------------------------------------------
module Rx.Inputs-Below where

open import Data.Bool using (T; _∧_)
open import Data.Unit using (tt)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Nat  using (ℕ)
open import Data.Sum  using (inj₁; inj₂)
open import Data.Fin.Properties using (toℕ<n)
open import Data.Nat.Properties using (<⇒<ᵇ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst; cong₂)

open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ)

open import Decide using (∧ˡ; ∧ʳ; ∧⁺)
open import Rx.Exp using (Ty; Ctx; Exp; Tm; Ren∈; ext∈;
                          renExp; renTm; renTms;
                          elimGExp; elimGTm; elimGTms;
                          elimDExp; elimDTm; elimDTms;
                          unfoldμ; compare∈; ⊟-++ˡ; ⊟-++ʳ;
                          input; ofᵉ; emptyᵉ; takeᵉ; batchSyncᵉ; mapᵉ; scanᵉ;
                          mergeAllᵉ; switchAllᵉ; exhaustAllᵉ;
                          μᵉ; varᵉ; deferᵉ; mintᵉ;
                          varᵗ; unit̂; bool̂; nat̂; uniq̂; pairᵗ; fstᵗ; sndᵗ;
                          inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ;
                          nilᵗ; consᵗ; foldᵗ;
                          inputsBelowᵉ; inputsBelowᵗ; inputsBelowᵗˢ)

------------------------------------------------------------------
-- RENAMING IS INVISIBLE TO THE GUARD: it moves the three binder
-- contexts and never touches Γ, which is where an input's index lives.
------------------------------------------------------------------
mutual
  ib-renᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (k : ℕ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′)
    (e : Exp Γ Δᵍ Δ Θ t) →
    inputsBelowᵉ k (renExp ρg ρd ρt e) ≡ inputsBelowᵉ k e
  ib-renᵉ k ρg ρd ρt (input i)       = refl
  ib-renᵉ k ρg ρd ρt (ofᵉ ts)        = ib-renᵗˢ k ρg ρd ρt ts
  ib-renᵉ k ρg ρd ρt emptyᵉ          = refl
  ib-renᵉ k ρg ρd ρt (takeᵉ c e)     =
    cong₂ _∧_ (ib-renᵗ k ρg ρd ρt c) (ib-renᵉ k ρg ρd ρt e)
  ib-renᵉ k ρg ρd ρt (mapᵉ f e)      =
    cong₂ _∧_ (ib-renᵗ k ρg ρd (ext∈ ρt) f) (ib-renᵉ k ρg ρd ρt e)
  ib-renᵉ k ρg ρd ρt (scanᵉ f z e)   =
    cong₂ _∧_ (ib-renᵗ k ρg ρd (ext∈ ρt) f)
              (cong₂ _∧_ (ib-renᵗ k ρg ρd ρt z) (ib-renᵉ k ρg ρd ρt e))
  ib-renᵉ k ρg ρd ρt (mergeAllᵉ _ e) = ib-renᵉ k ρg ρd ρt e
  ib-renᵉ k ρg ρd ρt (switchAllᵉ e)  = ib-renᵉ k ρg ρd ρt e
  ib-renᵉ k ρg ρd ρt (batchSyncᵉ e)  = ib-renᵉ k ρg ρd ρt e
  ib-renᵉ k ρg ρd ρt (exhaustAllᵉ e) = ib-renᵉ k ρg ρd ρt e
  ib-renᵉ k ρg ρd ρt (μᵉ e)          = ib-renᵉ k (ext∈ ρg) ρd ρt e
  ib-renᵉ k ρg ρd ρt (varᵉ x)        = refl
  ib-renᵉ k ρg ρd ρt (deferᵉ e)      = ib-renᵉ k (λ ()) _ ρt e
  ib-renᵉ k ρg ρd ρt (mintᵉ e)       = ib-renᵉ k ρg ρd (ext∈ ρt) e

  ib-renᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (k : ℕ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′)
    (tm : Tm Γ Δᵍ Δ Θ t) →
    inputsBelowᵗ k (renTm ρg ρd ρt tm) ≡ inputsBelowᵗ k tm
  ib-renᵗ k ρg ρd ρt (varᵗ x)      = refl
  ib-renᵗ k ρg ρd ρt unit̂          = refl
  ib-renᵗ k ρg ρd ρt (bool̂ _)      = refl
  ib-renᵗ k ρg ρd ρt (nat̂ _)       = refl
  ib-renᵗ k ρg ρd ρt (uniq̂ _)       = refl
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
  ib-renᵗ k ρg ρd ρt nilᵗ          = refl
  ib-renᵗ k ρg ρd ρt (consᵗ a as)  =
    cong₂ _∧_ (ib-renᵗ k ρg ρd ρt a) (ib-renᵗ k ρg ρd ρt as)
  ib-renᵗ k ρg ρd ρt (foldᵗ l z f) =
    cong₂ _∧_ (ib-renᵗ k ρg ρd ρt l)
              (cong₂ _∧_ (ib-renᵗ k ρg ρd ρt z)
                         (ib-renᵗ k ρg ρd (ext∈ (ext∈ ρt)) f))
  ib-renᵗ k ρg ρd ρt (strmᵗ e)     = ib-renᵉ k ρg ρd ρt e

  ib-renᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (k : ℕ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′)
    (ts : List (Tm Γ Δᵍ Δ Θ t)) →
    inputsBelowᵗˢ k (renTms ρg ρd ρt ts) ≡ inputsBelowᵗˢ k ts
  ib-renᵗˢ k ρg ρd ρt []       = refl
  ib-renᵗˢ k ρg ρd ρt (y ∷ ys) =
    cong₂ _∧_ (ib-renᵗ k ρg ρd ρt y) (ib-renᵗˢ k ρg ρd ρt ys)

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
------------------------------------------------------------------
mutual
  ib-elimGᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub u t} (k : ℕ)
    (Θl : List Ty) (x : t ∈ Δᵍ)
    (cl : Exp Γ [] [] Θsub t) → T (inputsBelowᵉ k cl) →
    (e : Exp Γ Δᵍ Δ (Θl ++ Θsub) u) → T (inputsBelowᵉ k e) →
    T (inputsBelowᵉ k (elimGExp Θl x cl e))
  ib-elimGᵉ k Θl x cl hcl (input i)       ok = ok
  ib-elimGᵉ k Θl x cl hcl (ofᵉ ts)        ok = ib-elimGᵗˢ k Θl x cl hcl ts ok
  ib-elimGᵉ k Θl x cl hcl emptyᵉ          ok = tt
  ib-elimGᵉ k Θl x cl hcl (takeᵉ c e)     ok =
    ∧⁺ (inputsBelowᵗ k (elimGTm Θl x cl c))
       (inputsBelowᵉ k (elimGExp Θl x cl e))
       (ib-elimGᵗ k Θl x cl hcl c
         (∧ˡ (inputsBelowᵗ k c) (inputsBelowᵉ k e) ok))
       (ib-elimGᵉ k Θl x cl hcl e
         (∧ʳ (inputsBelowᵗ k c) (inputsBelowᵉ k e) ok))
  ib-elimGᵉ k Θl x cl hcl (mapᵉ f e)      ok =
    ∧⁺ (inputsBelowᵗ k (elimGTm (_ ∷ Θl) x cl f))
       (inputsBelowᵉ k (elimGExp Θl x cl e))
       (ib-elimGᵗ k (_ ∷ Θl) x cl hcl f (∧ˡ (inputsBelowᵗ k f) _ ok))
       (ib-elimGᵉ k Θl x cl hcl e (∧ʳ (inputsBelowᵗ k f) _ ok))
  ib-elimGᵉ k Θl x cl hcl (scanᵉ f z e)   ok =
    ∧⁺ (inputsBelowᵗ k (elimGTm (_ ∷ Θl) x cl f))
       (inputsBelowᵗ k (elimGTm Θl x cl z)
         ∧ inputsBelowᵉ k (elimGExp Θl x cl e))
       (ib-elimGᵗ k (_ ∷ Θl) x cl hcl f (∧ˡ (inputsBelowᵗ k f) zbe ok))
       (∧⁺ (inputsBelowᵗ k (elimGTm Θl x cl z))
           (inputsBelowᵉ k (elimGExp Θl x cl e))
           (ib-elimGᵗ k Θl x cl hcl z
             (∧ˡ (inputsBelowᵗ k z) (inputsBelowᵉ k e) rest))
           (ib-elimGᵉ k Θl x cl hcl e
             (∧ʳ (inputsBelowᵗ k z) (inputsBelowᵉ k e) rest)))
    where
      zbe  = inputsBelowᵗ k z ∧ inputsBelowᵉ k e
      rest = ∧ʳ (inputsBelowᵗ k f) zbe ok
  ib-elimGᵉ k Θl x cl hcl (mergeAllᵉ _ e) ok = ib-elimGᵉ k Θl x cl hcl e ok
  ib-elimGᵉ k Θl x cl hcl (switchAllᵉ e)  ok = ib-elimGᵉ k Θl x cl hcl e ok
  ib-elimGᵉ k Θl x cl hcl (batchSyncᵉ e)  ok = ib-elimGᵉ k Θl x cl hcl e ok
  ib-elimGᵉ k Θl x cl hcl (exhaustAllᵉ e) ok = ib-elimGᵉ k Θl x cl hcl e ok
  ib-elimGᵉ k Θl x cl hcl (μᵉ e)          ok =
    ib-elimGᵉ k Θl (there x) cl hcl e ok
  ib-elimGᵉ k Θl x cl hcl (varᵉ y)        ok = tt
  ib-elimGᵉ k Θl x cl hcl (deferᵉ e)      ok =
    subst T (sym (ib-substᴱ k (⊟-++ˡ x) (elimDExp Θl (∈-++⁺ˡ x) cl e)))
            (ib-elimDᵉ k Θl (∈-++⁺ˡ x) cl hcl e ok)
  ib-elimGᵉ k Θl x cl hcl (mintᵉ e)       ok = ib-elimGᵉ k (_ ∷ Θl) x cl hcl e ok

  ib-elimGᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub u t} (k : ℕ)
    (Θl : List Ty) (x : t ∈ Δᵍ)
    (cl : Exp Γ [] [] Θsub t) → T (inputsBelowᵉ k cl) →
    (tm : Tm Γ Δᵍ Δ (Θl ++ Θsub) u) → T (inputsBelowᵗ k tm) →
    T (inputsBelowᵗ k (elimGTm Θl x cl tm))
  ib-elimGᵗ k Θl x cl hcl (varᵗ y)      ok = tt
  ib-elimGᵗ k Θl x cl hcl unit̂          ok = tt
  ib-elimGᵗ k Θl x cl hcl (bool̂ _)      ok = tt
  ib-elimGᵗ k Θl x cl hcl (nat̂ _)       ok = tt
  ib-elimGᵗ k Θl x cl hcl (uniq̂ _)       ok = tt
  ib-elimGᵗ k Θl x cl hcl (pairᵗ a b)   ok =
    ∧⁺ (inputsBelowᵗ k (elimGTm Θl x cl a))
       (inputsBelowᵗ k (elimGTm Θl x cl b))
       (ib-elimGᵗ k Θl x cl hcl a
         (∧ˡ (inputsBelowᵗ k a) (inputsBelowᵗ k b) ok))
       (ib-elimGᵗ k Θl x cl hcl b
         (∧ʳ (inputsBelowᵗ k a) (inputsBelowᵗ k b) ok))
  ib-elimGᵗ k Θl x cl hcl (fstᵗ p)      ok = ib-elimGᵗ k Θl x cl hcl p ok
  ib-elimGᵗ k Θl x cl hcl (sndᵗ p)      ok = ib-elimGᵗ k Θl x cl hcl p ok
  ib-elimGᵗ k Θl x cl hcl (inlᵗ a)      ok = ib-elimGᵗ k Θl x cl hcl a ok
  ib-elimGᵗ k Θl x cl hcl (inrᵗ a)      ok = ib-elimGᵗ k Θl x cl hcl a ok
  ib-elimGᵗ k Θl x cl hcl (caseᵗ s l r) ok =
    ∧⁺ (inputsBelowᵗ k (elimGTm Θl x cl s))
       (inputsBelowᵗ k (elimGTm (_ ∷ Θl) x cl l)
         ∧ inputsBelowᵗ k (elimGTm (_ ∷ Θl) x cl r))
       (ib-elimGᵗ k Θl x cl hcl s (∧ˡ (inputsBelowᵗ k s) lr ok))
       (∧⁺ (inputsBelowᵗ k (elimGTm (_ ∷ Θl) x cl l))
           (inputsBelowᵗ k (elimGTm (_ ∷ Θl) x cl r))
           (ib-elimGᵗ k (_ ∷ Θl) x cl hcl l
             (∧ˡ (inputsBelowᵗ k l) (inputsBelowᵗ k r) rest))
           (ib-elimGᵗ k (_ ∷ Θl) x cl hcl r
             (∧ʳ (inputsBelowᵗ k l) (inputsBelowᵗ k r) rest)))
    where
      lr   = inputsBelowᵗ k l ∧ inputsBelowᵗ k r
      rest = ∧ʳ (inputsBelowᵗ k s) lr ok
  ib-elimGᵗ k Θl x cl hcl (ifᵗ c a b)   ok =
    ∧⁺ (inputsBelowᵗ k (elimGTm Θl x cl c))
       (inputsBelowᵗ k (elimGTm Θl x cl a)
         ∧ inputsBelowᵗ k (elimGTm Θl x cl b))
       (ib-elimGᵗ k Θl x cl hcl c (∧ˡ (inputsBelowᵗ k c) ab ok))
       (∧⁺ (inputsBelowᵗ k (elimGTm Θl x cl a))
           (inputsBelowᵗ k (elimGTm Θl x cl b))
           (ib-elimGᵗ k Θl x cl hcl a
             (∧ˡ (inputsBelowᵗ k a) (inputsBelowᵗ k b) rest))
           (ib-elimGᵗ k Θl x cl hcl b
             (∧ʳ (inputsBelowᵗ k a) (inputsBelowᵗ k b) rest)))
    where
      ab   = inputsBelowᵗ k a ∧ inputsBelowᵗ k b
      rest = ∧ʳ (inputsBelowᵗ k c) ab ok
  ib-elimGᵗ k Θl x cl hcl (primᵗ _ a)   ok = ib-elimGᵗ k Θl x cl hcl a ok
  ib-elimGᵗ k Θl x cl hcl nilᵗ          ok = tt
  ib-elimGᵗ k Θl x cl hcl (consᵗ a as)  ok =
    ∧⁺ (inputsBelowᵗ k (elimGTm Θl x cl a))
       (inputsBelowᵗ k (elimGTm Θl x cl as))
       (ib-elimGᵗ k Θl x cl hcl a
         (∧ˡ (inputsBelowᵗ k a) (inputsBelowᵗ k as) ok))
       (ib-elimGᵗ k Θl x cl hcl as
         (∧ʳ (inputsBelowᵗ k a) (inputsBelowᵗ k as) ok))
  ib-elimGᵗ k Θl x cl hcl (foldᵗ l z f) ok =
    ∧⁺ (inputsBelowᵗ k (elimGTm Θl x cl l))
       (inputsBelowᵗ k (elimGTm Θl x cl z)
         ∧ inputsBelowᵗ k (elimGTm (_ ∷ _ ∷ Θl) x cl f))
       (ib-elimGᵗ k Θl x cl hcl l
         (∧ˡ (inputsBelowᵗ k l) _ ok))
       (∧⁺ (inputsBelowᵗ k (elimGTm Θl x cl z))
           (inputsBelowᵗ k (elimGTm (_ ∷ _ ∷ Θl) x cl f))
           (ib-elimGᵗ k Θl x cl hcl z
             (∧ˡ (inputsBelowᵗ k z) (inputsBelowᵗ k f)
               (∧ʳ (inputsBelowᵗ k l) _ ok)))
           (ib-elimGᵗ k (_ ∷ _ ∷ Θl) x cl hcl f
             (∧ʳ (inputsBelowᵗ k z) (inputsBelowᵗ k f)
               (∧ʳ (inputsBelowᵗ k l) _ ok))))
  ib-elimGᵗ k Θl x cl hcl (strmᵗ e)     ok = ib-elimGᵉ k Θl x cl hcl e ok

  ib-elimGᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub u t} (k : ℕ)
    (Θl : List Ty) (x : t ∈ Δᵍ)
    (cl : Exp Γ [] [] Θsub t) → T (inputsBelowᵉ k cl) →
    (ts : List (Tm Γ Δᵍ Δ (Θl ++ Θsub) u)) → T (inputsBelowᵗˢ k ts) →
    T (inputsBelowᵗˢ k (elimGTms Θl x cl ts))
  ib-elimGᵗˢ k Θl x cl hcl []       ok = tt
  ib-elimGᵗˢ k Θl x cl hcl (y ∷ ys) ok =
    ∧⁺ (inputsBelowᵗ k (elimGTm Θl x cl y))
       (inputsBelowᵗˢ k (elimGTms Θl x cl ys))
       (ib-elimGᵗ k Θl x cl hcl y
         (∧ˡ (inputsBelowᵗ k y) (inputsBelowᵗˢ k ys) ok))
       (ib-elimGᵗˢ k Θl x cl hcl ys
         (∧ʳ (inputsBelowᵗ k y) (inputsBelowᵗˢ k ys) ok))

  ib-elimDᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub u t} (k : ℕ)
    (Θl : List Ty) (x : t ∈ Δ)
    (cl : Exp Γ [] [] Θsub t) → T (inputsBelowᵉ k cl) →
    (e : Exp Γ Δᵍ Δ (Θl ++ Θsub) u) → T (inputsBelowᵉ k e) →
    T (inputsBelowᵉ k (elimDExp Θl x cl e))
  ib-elimDᵉ k Θl x cl hcl (input i)       ok = ok
  ib-elimDᵉ k Θl x cl hcl (ofᵉ ts)        ok = ib-elimDᵗˢ k Θl x cl hcl ts ok
  ib-elimDᵉ k Θl x cl hcl emptyᵉ          ok = tt
  ib-elimDᵉ k Θl x cl hcl (takeᵉ c e)     ok =
    ∧⁺ (inputsBelowᵗ k (elimDTm Θl x cl c))
       (inputsBelowᵉ k (elimDExp Θl x cl e))
       (ib-elimDᵗ k Θl x cl hcl c
         (∧ˡ (inputsBelowᵗ k c) (inputsBelowᵉ k e) ok))
       (ib-elimDᵉ k Θl x cl hcl e
         (∧ʳ (inputsBelowᵗ k c) (inputsBelowᵉ k e) ok))
  ib-elimDᵉ k Θl x cl hcl (mapᵉ f e)      ok =
    ∧⁺ (inputsBelowᵗ k (elimDTm (_ ∷ Θl) x cl f))
       (inputsBelowᵉ k (elimDExp Θl x cl e))
       (ib-elimDᵗ k (_ ∷ Θl) x cl hcl f (∧ˡ (inputsBelowᵗ k f) _ ok))
       (ib-elimDᵉ k Θl x cl hcl e (∧ʳ (inputsBelowᵗ k f) _ ok))
  ib-elimDᵉ k Θl x cl hcl (scanᵉ f z e)   ok =
    ∧⁺ (inputsBelowᵗ k (elimDTm (_ ∷ Θl) x cl f))
       (inputsBelowᵗ k (elimDTm Θl x cl z)
         ∧ inputsBelowᵉ k (elimDExp Θl x cl e))
       (ib-elimDᵗ k (_ ∷ Θl) x cl hcl f (∧ˡ (inputsBelowᵗ k f) zbe ok))
       (∧⁺ (inputsBelowᵗ k (elimDTm Θl x cl z))
           (inputsBelowᵉ k (elimDExp Θl x cl e))
           (ib-elimDᵗ k Θl x cl hcl z
             (∧ˡ (inputsBelowᵗ k z) (inputsBelowᵉ k e) rest))
           (ib-elimDᵉ k Θl x cl hcl e
             (∧ʳ (inputsBelowᵗ k z) (inputsBelowᵉ k e) rest)))
    where
      zbe  = inputsBelowᵗ k z ∧ inputsBelowᵉ k e
      rest = ∧ʳ (inputsBelowᵗ k f) zbe ok
  ib-elimDᵉ k Θl x cl hcl (mergeAllᵉ _ e) ok = ib-elimDᵉ k Θl x cl hcl e ok
  ib-elimDᵉ k Θl x cl hcl (switchAllᵉ e)  ok = ib-elimDᵉ k Θl x cl hcl e ok
  ib-elimDᵉ k Θl x cl hcl (batchSyncᵉ e)  ok = ib-elimDᵉ k Θl x cl hcl e ok
  ib-elimDᵉ k Θl x cl hcl (exhaustAllᵉ e) ok = ib-elimDᵉ k Θl x cl hcl e ok
  ib-elimDᵉ k Θl x cl hcl (μᵉ e)          ok = ib-elimDᵉ k Θl x cl hcl e ok
  ib-elimDᵉ k Θl x cl hcl (varᵉ y)        ok with compare∈ x y
  ... | inj₁ refl =
    subst T (sym (ib-renᵉ k (λ ()) (λ ()) (∈-++⁺ʳ Θl) cl)) hcl
  ... | inj₂ y′   = tt
  ib-elimDᵉ {Δᵍ = Δᵍ} k Θl x cl hcl (deferᵉ e) ok =
    subst T (sym (ib-substᴱ k (⊟-++ʳ {Δᵍ = Δᵍ} x)
                    (elimDExp Θl (∈-++⁺ʳ Δᵍ x) cl e)))
            (ib-elimDᵉ k Θl (∈-++⁺ʳ Δᵍ x) cl hcl e ok)
  ib-elimDᵉ k Θl x cl hcl (mintᵉ e)       ok = ib-elimDᵉ k (_ ∷ Θl) x cl hcl e ok

  ib-elimDᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub u t} (k : ℕ)
    (Θl : List Ty) (x : t ∈ Δ)
    (cl : Exp Γ [] [] Θsub t) → T (inputsBelowᵉ k cl) →
    (tm : Tm Γ Δᵍ Δ (Θl ++ Θsub) u) → T (inputsBelowᵗ k tm) →
    T (inputsBelowᵗ k (elimDTm Θl x cl tm))
  ib-elimDᵗ k Θl x cl hcl (varᵗ y)      ok = tt
  ib-elimDᵗ k Θl x cl hcl unit̂          ok = tt
  ib-elimDᵗ k Θl x cl hcl (bool̂ _)      ok = tt
  ib-elimDᵗ k Θl x cl hcl (nat̂ _)       ok = tt
  ib-elimDᵗ k Θl x cl hcl (uniq̂ _)       ok = tt
  ib-elimDᵗ k Θl x cl hcl (pairᵗ a b)   ok =
    ∧⁺ (inputsBelowᵗ k (elimDTm Θl x cl a))
       (inputsBelowᵗ k (elimDTm Θl x cl b))
       (ib-elimDᵗ k Θl x cl hcl a
         (∧ˡ (inputsBelowᵗ k a) (inputsBelowᵗ k b) ok))
       (ib-elimDᵗ k Θl x cl hcl b
         (∧ʳ (inputsBelowᵗ k a) (inputsBelowᵗ k b) ok))
  ib-elimDᵗ k Θl x cl hcl (fstᵗ p)      ok = ib-elimDᵗ k Θl x cl hcl p ok
  ib-elimDᵗ k Θl x cl hcl (sndᵗ p)      ok = ib-elimDᵗ k Θl x cl hcl p ok
  ib-elimDᵗ k Θl x cl hcl (inlᵗ a)      ok = ib-elimDᵗ k Θl x cl hcl a ok
  ib-elimDᵗ k Θl x cl hcl (inrᵗ a)      ok = ib-elimDᵗ k Θl x cl hcl a ok
  ib-elimDᵗ k Θl x cl hcl (caseᵗ s l r) ok =
    ∧⁺ (inputsBelowᵗ k (elimDTm Θl x cl s))
       (inputsBelowᵗ k (elimDTm (_ ∷ Θl) x cl l)
         ∧ inputsBelowᵗ k (elimDTm (_ ∷ Θl) x cl r))
       (ib-elimDᵗ k Θl x cl hcl s (∧ˡ (inputsBelowᵗ k s) lr ok))
       (∧⁺ (inputsBelowᵗ k (elimDTm (_ ∷ Θl) x cl l))
           (inputsBelowᵗ k (elimDTm (_ ∷ Θl) x cl r))
           (ib-elimDᵗ k (_ ∷ Θl) x cl hcl l
             (∧ˡ (inputsBelowᵗ k l) (inputsBelowᵗ k r) rest))
           (ib-elimDᵗ k (_ ∷ Θl) x cl hcl r
             (∧ʳ (inputsBelowᵗ k l) (inputsBelowᵗ k r) rest)))
    where
      lr   = inputsBelowᵗ k l ∧ inputsBelowᵗ k r
      rest = ∧ʳ (inputsBelowᵗ k s) lr ok
  ib-elimDᵗ k Θl x cl hcl (ifᵗ c a b)   ok =
    ∧⁺ (inputsBelowᵗ k (elimDTm Θl x cl c))
       (inputsBelowᵗ k (elimDTm Θl x cl a)
         ∧ inputsBelowᵗ k (elimDTm Θl x cl b))
       (ib-elimDᵗ k Θl x cl hcl c (∧ˡ (inputsBelowᵗ k c) ab ok))
       (∧⁺ (inputsBelowᵗ k (elimDTm Θl x cl a))
           (inputsBelowᵗ k (elimDTm Θl x cl b))
           (ib-elimDᵗ k Θl x cl hcl a
             (∧ˡ (inputsBelowᵗ k a) (inputsBelowᵗ k b) rest))
           (ib-elimDᵗ k Θl x cl hcl b
             (∧ʳ (inputsBelowᵗ k a) (inputsBelowᵗ k b) rest)))
    where
      ab   = inputsBelowᵗ k a ∧ inputsBelowᵗ k b
      rest = ∧ʳ (inputsBelowᵗ k c) ab ok
  ib-elimDᵗ k Θl x cl hcl (primᵗ _ a)   ok = ib-elimDᵗ k Θl x cl hcl a ok
  ib-elimDᵗ k Θl x cl hcl nilᵗ          ok = tt
  ib-elimDᵗ k Θl x cl hcl (consᵗ a as)  ok =
    ∧⁺ (inputsBelowᵗ k (elimDTm Θl x cl a))
       (inputsBelowᵗ k (elimDTm Θl x cl as))
       (ib-elimDᵗ k Θl x cl hcl a
         (∧ˡ (inputsBelowᵗ k a) (inputsBelowᵗ k as) ok))
       (ib-elimDᵗ k Θl x cl hcl as
         (∧ʳ (inputsBelowᵗ k a) (inputsBelowᵗ k as) ok))
  ib-elimDᵗ k Θl x cl hcl (foldᵗ l z f) ok =
    ∧⁺ (inputsBelowᵗ k (elimDTm Θl x cl l))
       (inputsBelowᵗ k (elimDTm Θl x cl z)
         ∧ inputsBelowᵗ k (elimDTm (_ ∷ _ ∷ Θl) x cl f))
       (ib-elimDᵗ k Θl x cl hcl l
         (∧ˡ (inputsBelowᵗ k l) _ ok))
       (∧⁺ (inputsBelowᵗ k (elimDTm Θl x cl z))
           (inputsBelowᵗ k (elimDTm (_ ∷ _ ∷ Θl) x cl f))
           (ib-elimDᵗ k Θl x cl hcl z
             (∧ˡ (inputsBelowᵗ k z) (inputsBelowᵗ k f)
               (∧ʳ (inputsBelowᵗ k l) _ ok)))
           (ib-elimDᵗ k (_ ∷ _ ∷ Θl) x cl hcl f
             (∧ʳ (inputsBelowᵗ k z) (inputsBelowᵗ k f)
               (∧ʳ (inputsBelowᵗ k l) _ ok))))
  ib-elimDᵗ k Θl x cl hcl (strmᵗ e)     ok = ib-elimDᵉ k Θl x cl hcl e ok

  ib-elimDᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub u t} (k : ℕ)
    (Θl : List Ty) (x : t ∈ Δ)
    (cl : Exp Γ [] [] Θsub t) → T (inputsBelowᵉ k cl) →
    (ts : List (Tm Γ Δᵍ Δ (Θl ++ Θsub) u)) → T (inputsBelowᵗˢ k ts) →
    T (inputsBelowᵗˢ k (elimDTms Θl x cl ts))
  ib-elimDᵗˢ k Θl x cl hcl []       ok = tt
  ib-elimDᵗˢ k Θl x cl hcl (y ∷ ys) ok =
    ∧⁺ (inputsBelowᵗ k (elimDTm Θl x cl y))
       (inputsBelowᵗˢ k (elimDTms Θl x cl ys))
       (ib-elimDᵗ k Θl x cl hcl y
         (∧ˡ (inputsBelowᵗ k y) (inputsBelowᵗˢ k ys) ok))
       (ib-elimDᵗˢ k Θl x cl hcl ys
         (∧ʳ (inputsBelowᵗ k y) (inputsBelowᵗˢ k ys) ok))

-- THE CLAUSE THE WALK SPENDS: the guard survives one μ peel.
ib-unfoldμ : ∀ {n} {Γ : Ctx n} {Θ t} (k : ℕ) (body : Exp Γ (t ∷ []) [] Θ t) →
  T (inputsBelowᵉ k (μᵉ body)) → T (inputsBelowᵉ k (unfoldμ body))
ib-unfoldμ k body ok = ib-elimGᵉ k [] (here refl) (μᵉ body) ok body ok

------------------------------------------------------------------
-- EVERY PROGRAM SITS AT THE TOP STRATUM, which is how the root of the
-- walk discharges the hypothesis with nothing to supply it.
------------------------------------------------------------------
mutual
  ib-topᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (e : Exp Γ Δᵍ Δ Θ t) →
    T (inputsBelowᵉ n e)
  ib-topᵉ (input i)       = <⇒<ᵇ (toℕ<n i)
  ib-topᵉ (ofᵉ ts)        = ib-topᵗˢ ts
  ib-topᵉ emptyᵉ          = tt
  ib-topᵉ (takeᵉ c e)     = ∧⁺ _ _ (ib-topᵗ c) (ib-topᵉ e)
  ib-topᵉ (mapᵉ f e)      = ∧⁺ _ _ (ib-topᵗ f) (ib-topᵉ e)
  ib-topᵉ (scanᵉ f z e)   = ∧⁺ _ _ (ib-topᵗ f) (∧⁺ _ _ (ib-topᵗ z) (ib-topᵉ e))
  ib-topᵉ (mergeAllᵉ _ e) = ib-topᵉ e
  ib-topᵉ (switchAllᵉ e)  = ib-topᵉ e
  ib-topᵉ (batchSyncᵉ e)  = ib-topᵉ e
  ib-topᵉ (exhaustAllᵉ e) = ib-topᵉ e
  ib-topᵉ (μᵉ e)          = ib-topᵉ e
  ib-topᵉ (varᵉ x)        = tt
  ib-topᵉ (deferᵉ e)      = ib-topᵉ e
  ib-topᵉ (mintᵉ e)       = ib-topᵉ e

  ib-topᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (tm : Tm Γ Δᵍ Δ Θ t) →
    T (inputsBelowᵗ n tm)
  ib-topᵗ (varᵗ x)      = tt
  ib-topᵗ unit̂          = tt
  ib-topᵗ (bool̂ _)      = tt
  ib-topᵗ (nat̂ _)       = tt
  ib-topᵗ (uniq̂ _)       = tt
  ib-topᵗ (pairᵗ a b)   = ∧⁺ _ _ (ib-topᵗ a) (ib-topᵗ b)
  ib-topᵗ (fstᵗ p)      = ib-topᵗ p
  ib-topᵗ (sndᵗ p)      = ib-topᵗ p
  ib-topᵗ (inlᵗ a)      = ib-topᵗ a
  ib-topᵗ (inrᵗ a)      = ib-topᵗ a
  ib-topᵗ (caseᵗ s l r) = ∧⁺ _ _ (ib-topᵗ s) (∧⁺ _ _ (ib-topᵗ l) (ib-topᵗ r))
  ib-topᵗ (ifᵗ c a b)   = ∧⁺ _ _ (ib-topᵗ c) (∧⁺ _ _ (ib-topᵗ a) (ib-topᵗ b))
  ib-topᵗ (primᵗ _ a)   = ib-topᵗ a
  ib-topᵗ nilᵗ          = tt
  ib-topᵗ (consᵗ a as)  = ∧⁺ _ _ (ib-topᵗ a) (ib-topᵗ as)
  ib-topᵗ (foldᵗ l z f) = ∧⁺ _ _ (ib-topᵗ l) (∧⁺ _ _ (ib-topᵗ z) (ib-topᵗ f))
  ib-topᵗ (strmᵗ e)     = ib-topᵉ e

  ib-topᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (ts : List (Tm Γ Δᵍ Δ Θ t)) →
    T (inputsBelowᵗˢ n ts)
  ib-topᵗˢ []       = tt
  ib-topᵗˢ (y ∷ ys) = ∧⁺ _ _ (ib-topᵗ y) (ib-topᵗˢ ys)
