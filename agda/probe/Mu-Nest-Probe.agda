------------------------------------------------------------------
-- THE μ-NEST PROBE: what the budget `k` may be a hypothesis ABOUT.
--
-- The pass that surfaces the receipts into the subscribe clique's
-- signatures gives `subscribeE-caps` the conjunct
-- `j + j′ ≤ sLvlD S W d k j` "under a nesting hypothesis on b"
-- (.Caps-Face, the block above the two postulates).  This probe fixes
-- WHAT that hypothesis is, because the obvious reading — `1 ≤ k`, the
-- side condition that lets `sLvlD S W d (suc k) J` unfold to
-- `opIterD S W d k (suc (sizeAt S J)) J` and the chain walk begin — is
-- NOT MAINTAINABLE, and the probe machine-checks both halves of that.
--
-- § 1  WHY `1 ≤ k` FAILS.  `k` descends by exactly one at ONE place:
--   the `sLvlD (suc k) ↦ opIterD k` boundary.  Chain walking
--   (`op-step`, `op-step-eval`) keeps k and decrements m; the payload
--   walk (`walk-step`) keeps k; a frame REFRESHES it (`frame-step`).
--   So the one k-consuming recursion inside a subscribe's own subtree
--   is `op-step-mu`, whose premise is read at `sLvlD S W d k _` while
--   its conclusion sits at `opIterD S W d k (suc m) j` — i.e. one level
--   of μ per unit of k.  `subscribeE-caps`'s own μ clause
--   (.Subscribe-Face, the `(gs fuel) (μᵉ body)` clause) therefore calls
--   itself at `k − 1`, and a bare `1 ≤ k` hypothesis cannot hand
--   `1 ≤ k − 1` to that call.  `one≤k-absurd` is that, machine-checked:
--   the maintenance step at k = 1 demands `1 ≤ 0`.
--
-- § 2  WHAT WORKS: `syncSizeᵉ b ≤ k`.  syncSize is Rx.Exp's own
--   sync-reachable size — `deferᵉ` is a LEAF in it — and the type
--   discipline is what makes it the right measure: `μᵉ` binds into Δᵍ,
--   `varᵉ` reads out of Δ, and `deferᵉ` is the SOLE gate moving Δᵍ into
--   Δ, so an unfolding substitutes `μᵉ body` only at defer-gated
--   positions, which syncSize counts as leaves.  Hence
--
--     syncSizeᵉ (unfoldμ body) ≡ syncSizeᵉ body       (`syncSize-unfoldμ`)
--     syncSizeᵉ (μᵉ body)      ≡ suc (syncSizeᵉ body) (a clause)
--
--   — the measure DROPS BY EXACTLY ONE across the μ edge, the same
--   step k takes.  Every other subscribeE edge is a strict subterm, so
--   the hypothesis survives at the SAME k.  § 2 checks each edge.
--
-- § 3  AND IT IS SUPPLIABLE WHERE k IS REFRESHED.  A frame instantiates
--   k at `suc (sizeAt S J)` and subscribes payload observables it has a
--   `valsCaps?` receipt for, i.e. `sizeᵛ o ≤ S`.  `syncSize≤sizeᵉ`
--   (.Measures, already proven) plus `S ≤ sizeAt S J` closes it — so
--   the piece .Caps-Face records as owed, "`nestᵛ ≤ sizeᵛ`, proven in
--   Nest-Budget-Probe beside the other value measures", is ALREADY IN
--   TREE under the name `syncSize≤sizeᵉ`, provided `nest` is read as
--   `syncSize`.
--
-- § 4  AND ONE CALL SITE STILL CANNOT SUPPLY IT: the share connect.
--   `sharedConnect` peels a gas and calls `subscribeE` on the SLOT'S
--   STORED DEFINITION, which the evaluator's own comment calls
--   "structurally unrelated to the `input i` being subscribed" — so the
--   caller's term is `input i`, syncSize 1, and a term-only hypothesis
--   has one unit to hand a callee that may need the whole size cap.
--   `plain-share-absurd` refutes that step.  THE REPAIR is to carry the
--   UNCONNECTED SLOTS' residue alongside: `sharedConnect` writes the
--   slot into `connectedShares` BEFORE subscribing the def and
--   `subscribeSharedSlot` short-circuits on an already-connected one, so
--   a share connects at most once per instant and
--   `M b U = syncSizeᵉ b + Σ_{i∈U} syncSizeᵉ (def i)` drops by exactly
--   one across the share edge — the residue loses precisely the
--   callee's own size.  `share-residue-step`, `mu-residue-step` and
--   `chain-residue-step` are the three edge shapes under M.
------------------------------------------------------------------
module Mu-Nest-Probe where

open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; ≤-refl; n≤1+n; m≤n+m; +-monoˡ-≤)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥)
open import Data.Fin  using (Fin; zero)
open import Data.Vec  using (Vec) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Rx.Exp
  using (Ctx; Closed; Exp; Tm; Val; Fn; Ty; natᵗ; obs;
         input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ;
         mergeAllᵉ; concatAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ;
         varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ; inlᵗ; inrᵗ;
         caseᵗ; ifᵗ; primᵗ; strmᵗ;
         syncSizeᵉ; syncSizeᵗ; syncSizeᵗˢ; sizeᵉ; sizeᵛ;
         elimGExp; elimGTm; elimGTms; unfoldμ)
open import Rx.Evaluator using (sizeAt)
open import Verify-Budget-Sufficient.Caps using (sizeAt-mono)
open import Verify-Budget-Sufficient.Measures using (syncSize≤sizeᵉ)

------------------------------------------------------------------
-- § 1.  THE BARE SIDE CONDITION IS NOT MAINTAINABLE.  The μ clause of
-- `subscribeE-caps` reads its own bound at k and its recursive call's
-- at `k − 1`; a hypothesis that says only `1 ≤ k` has nothing to hand
-- the call.  Stated as the maintenance step it would have to be
------------------------------------------------------------------

One≤K-Maintains : Set
One≤K-Maintains = ∀ (k : ℕ) → 1 ≤ suc k → 1 ≤ k

one≤k-absurd : One≤K-Maintains → ⊥
one≤k-absurd H with H 0 (s≤s z≤n)
... | ()

------------------------------------------------------------------
-- § 2.  THE MEASURE.  Substitution for a μ-var preserves syncSize
-- EXACTLY: every clause is congruence, `varᵉ` is untouched (a Δᵍ var is
-- not readable as a varᵉ), and `deferᵉ` — the only clause that rewrites
-- under a context identity — is a syncSize LEAF, so its body is never
-- measured and the `subst` never has to be transported through
------------------------------------------------------------------

mutual
  syncSize-elimG : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
    (cl : Exp Γ [] [] [] t) (e : Exp Γ Δᵍ Δ Θ u) →
    syncSizeᵉ (elimGExp x cl e) ≡ syncSizeᵉ e
  syncSize-elimG x cl (input i)       = refl
  syncSize-elimG x cl (ofᵉ ts)        = cong suc (syncSize-elimGs x cl ts)
  syncSize-elimG x cl emptyᵉ          = refl
  syncSize-elimG x cl (mapᵉ f e)      =
    cong suc (cong₂ _+_ (syncSize-elimGt x cl f) (syncSize-elimG x cl e))
  syncSize-elimG x cl (takeᵉ c e)     =
    cong suc (cong₂ _+_ (syncSize-elimGt x cl c) (syncSize-elimG x cl e))
  syncSize-elimG x cl (scanᵉ f z e)   =
    cong suc (cong₂ _+_ (cong₂ _+_ (syncSize-elimGt x cl f)
                                   (syncSize-elimGt x cl z))
                        (syncSize-elimG x cl e))
  syncSize-elimG x cl (mergeAllᵉ e)   = cong suc (syncSize-elimG x cl e)
  syncSize-elimG x cl (concatAllᵉ e)  = cong suc (syncSize-elimG x cl e)
  syncSize-elimG x cl (switchAllᵉ e)  = cong suc (syncSize-elimG x cl e)
  syncSize-elimG x cl (exhaustAllᵉ e) = cong suc (syncSize-elimG x cl e)
  syncSize-elimG x cl (μᵉ e)          = cong suc (syncSize-elimG (there x) cl e)
  syncSize-elimG x cl (varᵉ y)        = refl
  syncSize-elimG x cl (deferᵉ e)      = refl

  syncSize-elimGt : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
    (cl : Exp Γ [] [] [] t) (tm : Tm Γ Δᵍ Δ Θ u) →
    syncSizeᵗ (elimGTm x cl tm) ≡ syncSizeᵗ tm
  syncSize-elimGt x cl (varᵗ y)      = refl
  syncSize-elimGt x cl unit̂          = refl
  syncSize-elimGt x cl (bool̂ b)      = refl
  syncSize-elimGt x cl (nat̂ m)       = refl
  syncSize-elimGt x cl (pairᵗ a b)   =
    cong suc (cong₂ _+_ (syncSize-elimGt x cl a) (syncSize-elimGt x cl b))
  syncSize-elimGt x cl (fstᵗ p)      = cong suc (syncSize-elimGt x cl p)
  syncSize-elimGt x cl (sndᵗ p)      = cong suc (syncSize-elimGt x cl p)
  syncSize-elimGt x cl (inlᵗ a)      = cong suc (syncSize-elimGt x cl a)
  syncSize-elimGt x cl (inrᵗ a)      = cong suc (syncSize-elimGt x cl a)
  syncSize-elimGt x cl (caseᵗ s l r) =
    cong suc (cong₂ _+_ (cong₂ _+_ (syncSize-elimGt x cl s)
                                   (syncSize-elimGt x cl l))
                        (syncSize-elimGt x cl r))
  syncSize-elimGt x cl (ifᵗ c a b)   =
    cong suc (cong₂ _+_ (cong₂ _+_ (syncSize-elimGt x cl c)
                                   (syncSize-elimGt x cl a))
                        (syncSize-elimGt x cl b))
  syncSize-elimGt x cl (primᵗ op a)  = cong suc (syncSize-elimGt x cl a)
  syncSize-elimGt x cl (strmᵗ e)     = cong suc (syncSize-elimG x cl e)

  syncSize-elimGs : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (x : t ∈ Δᵍ)
    (cl : Exp Γ [] [] [] t) (ts : List (Tm Γ Δᵍ Δ Θ u)) →
    syncSizeᵗˢ (elimGTms x cl ts) ≡ syncSizeᵗˢ ts
  syncSize-elimGs x cl []       = refl
  syncSize-elimGs x cl (y ∷ ys) =
    cong₂ _+_ (syncSize-elimGt x cl y) (syncSize-elimGs x cl ys)

-- THE μ EDGE, exactly one step
syncSize-unfoldμ : ∀ {n} {Γ : Ctx n} {t} (body : Exp Γ (t ∷ []) [] [] t) →
  syncSizeᵉ (unfoldμ body) ≡ syncSizeᵉ body
syncSize-unfoldμ body = syncSize-elimG (here refl) (μᵉ body) body

syncSize-μ-drop : ∀ {n} {Γ : Ctx n} {t} (body : Exp Γ (t ∷ []) [] [] t) →
  suc (syncSizeᵉ (unfoldμ body)) ≡ syncSizeᵉ (μᵉ body)
syncSize-μ-drop body = cong suc (syncSize-unfoldμ body)

------------------------------------------------------------------
-- THE MAINTENANCE STEPS, one per subscribeE edge.  The hypothesis is
-- `syncSizeᵉ b ≤ k`; the μ clause hands its call `k − 1` and every
-- other clause hands its call the same k
------------------------------------------------------------------

-- μ with gas: the ONE clause that spends a k
mu-step : ∀ {n} {Γ : Ctx n} {t} (body : Exp Γ (t ∷ []) [] [] t) (k : ℕ) →
  syncSizeᵉ (μᵉ body) ≤ suc k → syncSizeᵉ (unfoldμ body) ≤ k
mu-step body k h =
  subst (λ x → x ≤ k) (sym (syncSize-unfoldμ body)) (unsuc h)
  where
  unsuc : ∀ {a b} → suc a ≤ suc b → a ≤ b
  unsuc (s≤s p) = p

-- and it also yields the side condition the clause unfolds on
mu-1≤k : ∀ {n} {Γ : Ctx n} {t} (body : Exp Γ (t ∷ []) [] [] t) (k : ℕ) →
  syncSizeᵉ (μᵉ body) ≤ k → 1 ≤ k
mu-1≤k body zero    ()
mu-1≤k body (suc k) h = s≤s z≤n

-- the chain edges: map / take / scan and the four *All heads, each a
-- strict subterm, so the SAME k serves
map-step : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s t}
  (f : Fn Γ Δᵍ Δ Θ s t) (b : Exp Γ Δᵍ Δ Θ s) (k : ℕ) →
  syncSizeᵉ (mapᵉ f b) ≤ k → syncSizeᵉ b ≤ k
map-step f b k h = ≤-trans (≤-trans (n≤1+n (syncSizeᵉ b)) (s≤s (m≤n+m (syncSizeᵉ b) (syncSizeᵗ f)))) h

take-step : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t}
  (c : Tm Γ Δᵍ Δ Θ natᵗ) (b : Exp Γ Δᵍ Δ Θ t) (k : ℕ) →
  syncSizeᵉ (takeᵉ c b) ≤ k → syncSizeᵉ b ≤ k
take-step c b k h = ≤-trans (≤-trans (n≤1+n (syncSizeᵉ b)) (s≤s (m≤n+m (syncSizeᵉ b) (syncSizeᵗ c)))) h

merge-step : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (b : Exp Γ Δᵍ Δ Θ (obs t)) (k : ℕ) →
  syncSizeᵉ (mergeAllᵉ b) ≤ k → syncSizeᵉ b ≤ k
merge-step b k h = ≤-trans (n≤1+n (syncSizeᵉ b)) h

concat-step : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (b : Exp Γ Δᵍ Δ Θ (obs t)) (k : ℕ) →
  syncSizeᵉ (concatAllᵉ b) ≤ k → syncSizeᵉ b ≤ k
concat-step b k h = ≤-trans (n≤1+n (syncSizeᵉ b)) h

switch-step : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (b : Exp Γ Δᵍ Δ Θ (obs t)) (k : ℕ) →
  syncSizeᵉ (switchAllᵉ b) ≤ k → syncSizeᵉ b ≤ k
switch-step b k h = ≤-trans (n≤1+n (syncSizeᵉ b)) h

exhaust-step : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (b : Exp Γ Δᵍ Δ Θ (obs t)) (k : ℕ) →
  syncSizeᵉ (exhaustAllᵉ b) ≤ k → syncSizeᵉ b ≤ k
exhaust-step b k h = ≤-trans (n≤1+n (syncSizeᵉ b)) h

-- every expression has syncSize at least one, so the hypothesis
-- SUBSUMES the bare side condition at every node
1≤syncSize : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (e : Exp Γ Δᵍ Δ Θ t) → 1 ≤ syncSizeᵉ e
1≤syncSize (input i)       = s≤s z≤n
1≤syncSize (ofᵉ ts)        = s≤s z≤n
1≤syncSize emptyᵉ          = s≤s z≤n
1≤syncSize (mapᵉ f e)      = s≤s z≤n
1≤syncSize (takeᵉ c e)     = s≤s z≤n
1≤syncSize (scanᵉ f z e)   = s≤s z≤n
1≤syncSize (mergeAllᵉ e)   = s≤s z≤n
1≤syncSize (concatAllᵉ e)  = s≤s z≤n
1≤syncSize (switchAllᵉ e)  = s≤s z≤n
1≤syncSize (exhaustAllᵉ e) = s≤s z≤n
1≤syncSize (μᵉ e)          = s≤s z≤n
1≤syncSize (varᵉ x)        = s≤s z≤n
1≤syncSize (deferᵉ e)      = s≤s z≤n

------------------------------------------------------------------
-- § 3.  THE REFRESH SUPPLIES IT.  A frame instantiates k at
-- `suc (sizeAt S J)`; the payloads it subscribes carry `sizeᵛ o ≤ S`
-- from `valsCaps?`.  `syncSize≤sizeᵉ` and `S ≤ sizeAt S J` close it
------------------------------------------------------------------

S≤sizeAt : ∀ (S J : ℕ) → 1 ≤ S → S ≤ sizeAt S J
S≤sizeAt S J 1≤S = sizeAt-mono {S} {S} {0} {J} 1≤S ≤-refl z≤n

refresh-supplies : ∀ {n} {Γ : Ctx n} {t} (S J : ℕ) (o : Closed Γ t) →
  1 ≤ S → sizeᵉ o ≤ S → syncSizeᵉ o ≤ suc (sizeAt S J)
refresh-supplies S J o 1≤S hsz =
  ≤-trans (≤-trans (≤-trans (syncSize≤sizeᵉ o) hsz) (S≤sizeAt S J 1≤S))
          (n≤1+n (sizeAt S J))

-- and the same reading of a payload VALUE, which is how valsCaps?
-- states it (`sizeᵛ (obs t) o` is `sizeᵉ o`, definitionally)
refresh-supplies-val : ∀ {n} {Γ : Ctx n} {t} (S J : ℕ) (o : Val Γ (obs t)) →
  1 ≤ S → sizeᵛ (obs t) o ≤ S → syncSizeᵉ o ≤ suc (sizeAt S J)
refresh-supplies-val S J o 1≤S hsz = refresh-supplies S J o 1≤S hsz

------------------------------------------------------------------
-- § 4.  BUT ONE CALL SITE STILL CANNOT SUPPLY IT: THE SHARE CONNECT.
--
-- `sharedConnect` is a nesting edge like μ — it peels a gas and calls
-- `subscribeE` — but its callee is the SLOT'S STORED DEFINITION, and
-- the evaluator says so in as many words (Rx.Evaluator, above
-- `sharedConnect`): "the def d is a stored expression, STRUCTURALLY
-- UNRELATED to the `input i` being subscribed".  The caller's own
-- expression is `input i`, whose syncSize is 1, so a hypothesis that
-- speaks only of the subscribed term has one unit to spend and the
-- callee may need any amount up to the size cap.  `share-plain-absurd`
-- is that step, refuted at k = 0
------------------------------------------------------------------

Plain-Share-Maintains : Set
Plain-Share-Maintains = ∀ {n} {Γ : Ctx n} {t} (i : Fin n) (d : Closed Γ t) (k : ℕ) →
  syncSizeᵉ (input {Γ = Γ} {Δᵍ = []} {Δ = []} {Θ = []} i) ≤ suc k →
  syncSizeᵉ d ≤ k

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ᵛ []ᵛ

plain-share-absurd : Plain-Share-Maintains → ⊥
plain-share-absurd H with H {Γ = Γ₁} {t = natᵗ} zero emptyᵉ 0 (s≤s z≤n)
... | ()

------------------------------------------------------------------
-- THE REPAIR THAT DOES CLOSE IT: carry the UNCONNECTED SLOTS' residue.
-- `sharedConnect` writes `toℕ i` into `connectedShares` BEFORE it
-- subscribes the def, and `subscribeSharedSlot` short-circuits on a
-- share already in that list — so a share connects AT MOST ONCE per
-- instant and the residue is a genuine descending quantity.  Measure a
-- subscribe by
--
--     M b U = syncSizeᵉ b + Σ_{i ∈ U} syncSizeᵉ (def i)
--
-- with U the still-unconnected slots.  At the share edge the caller is
-- `input i` (syncSize 1) with i ∈ U, and the callee is `def i` with
-- U ∖ {i}: the residue loses exactly the callee's own size, so
-- M drops by exactly one — the same step k takes.  The three lemmas
-- below are the three edge shapes under M, and they are the whole
-- content of the repair: the µ and chain steps are unchanged, and the
-- share step is the new one
------------------------------------------------------------------

-- the share edge: `resid ≡ szᵢ + resid′` is the removal equation
share-residue-step : ∀ (szᵢ resid resid′ k : ℕ) →
  resid ≡ szᵢ + resid′ →
  1 + resid ≤ suc k →
  szᵢ + resid′ ≤ k
share-residue-step szᵢ resid resid′ k eq (s≤s h) = subst (λ x → x ≤ k) eq h

-- the μ edge, under the same measure: the residue is untouched
mu-residue-step : ∀ {n} {Γ : Ctx n} {t} (body : Exp Γ (t ∷ []) [] [] t)
  (resid k : ℕ) →
  syncSizeᵉ (μᵉ body) + resid ≤ suc k →
  syncSizeᵉ (unfoldμ body) + resid ≤ k
mu-residue-step body resid k (s≤s h) =
  subst (λ x → x + resid ≤ k) (sym (syncSize-unfoldμ body)) h

-- a chain edge, under the same measure: strict subterm, same k
chain-residue-step : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t}
  (b : Exp Γ Δᵍ Δ Θ (obs t)) (resid k : ℕ) →
  syncSizeᵉ (concatAllᵉ b) + resid ≤ k → syncSizeᵉ b + resid ≤ k
chain-residue-step b resid k h =
  ≤-trans (+-monoˡ-≤ resid (n≤1+n (syncSizeᵉ b))) h
