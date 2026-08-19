------------------------------------------------------------------
-- THE SPINE-INDEXED BURST BOUND, and the one lemma that spends it.
--
-- `burstHopD? V η r` asks every emitted value to sit under a SINGLE
-- number `r`.  For a scan frame that number is `hopDᵉ V η (scanᵉ f z b)
-- = (2 + pmᵗ V 0 f) ^ V * B`, and the exponent V arrives only through
-- the store bound.  Getting there in one step forces the fold's
-- induction to carry `V` in the exponent from the start, which is what
-- `Refuted.Hop-Drag` refutes: a fold step can DEEPEN the accumulator
-- while shrinking its `sizeᵛ`, so no per-step size comparison funds the
-- exponent.
--
-- So the burst is bounded at each value's OWN SPINE first — a quantity
-- the refuting step does not decrease — and the exponent is raised to V
-- afterwards, here, once, using the size receipt the same walk already
-- proves.  That is the whole content of this module: `burstHopSpn?` is
-- the fold's natural conclusion, `burstHopD?` is the walk's, and
-- `burstHopSpn-cap` is the conversion.
------------------------------------------------------------------
module Verify-Budget-Sufficient.Hop-Spine-Face where

open import Data.Bool using (Bool; true; T; _∧_)
open import Data.Bool.ListAction using (all)
open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _^_; _⊔_; _≤_; _≤ᵇ_; s≤s; z≤n)
open import Data.Nat.Properties using (≤ᵇ⇒≤; ≤⇒≤ᵇ; ≤-trans; ≤-refl;
                                       ^-monoʳ-≤; *-monoˡ-≤;
                                       ⊔-lub; m≤m⊔n; m≤n⊔m; n≤1+n)
open import Data.List using (List; []; _∷_)
open import Data.Fin  using (Fin)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum     using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim  using (InstEmit; InstEvent; init; value; close;
                            handoff; complete)
open import Rx.Exp   using (Ty; Ctx; Val; sizeᵛ;
                            unitᵗ; boolᵗ; natᵗ; obs; _×ᵗ_; _+ᵗ_)
open import Rx.Hop-Depth using (hopDᵉ; hopDᵛ)
open import Rx.Hop-Spine using (spnᵉ; spnᵛ; spn≤sizeᵛ)
open import Rx.Evaluator using (Stream)
open import Verify-Budget-Sufficient.Measures using
  (burstB?; burstHopD?; valB?; eventB?; hopDev?; all-impl;
   ∧-true; ∧-intro; T⇒≡true; T-to; all-zip)

-- the same event walk as hopDev?, with the bound read off the VALUE
hopSpnev? : ∀ {n} {Γ : Ctx n} {u} → ℕ → (Fin n → ℕ) → ℕ → ℕ →
            InstEvent (Val Γ u) → Bool
hopSpnev? {u = u} V η base B (value v) = hopDᵛ V η u v ≤ᵇ base ^ spnᵛ u v * B
hopSpnev? V η base B (init _)    = true
hopSpnev? V η base B (close _ _) = true
hopSpnev? V η base B (handoff _) = true
hopSpnev? V η base B complete    = true

burstHopSpn? : ∀ {n} {Γ : Ctx n} {u} → ℕ → (Fin n → ℕ) → ℕ → ℕ →
               Stream Γ u → Bool
burstHopSpn? V η base B =
  all (λ em → all (hopSpnev? V η base B) (InstEmit.events em))

------------------------------------------------------------------
-- THE CONVERSION.  `spn≤sizeᵛ` (Rx.Hop-Spine) is what makes the size
-- receipt pay for the hop exponent: the spine is size along the
-- hop-deepest path, so a cap on the whole value caps it too.
------------------------------------------------------------------

burstHopSpn-cap : ∀ {n} {Γ : Ctx n} {u} (V Ψ base B Bsz : ℕ)
  (η : Fin n → ℕ) (str : Stream Γ u) →
  1 ≤ base → Bsz ≤ V →
  burstB? Bsz Ψ str ≡ true →
  burstHopSpn? V η base B str ≡ true →
  burstHopD? V η (base ^ V * B) str ≡ true
-- base ≡ 0 is vacuous, and matching on `suc base` is also what puts the
-- NonZero instance ^-monoʳ-≤ asks for in scope
burstHopSpn-cap V Ψ zero B Bsz η str () hBsz hB hS
burstHopSpn-cap {u = u} V Ψ (suc base) B Bsz η str 1≤b hBsz hB hS =
  all-zip (λ em → all (eventB? Bsz Ψ) (InstEmit.events em))
            (λ em → all (hopSpnev? V η (suc base) B) (InstEmit.events em))
            (λ em → all (hopDev? V η (suc base ^ V * B)) (InstEmit.events em))
            (λ em → all-zip (eventB? Bsz Ψ)
                              (hopSpnev? V η (suc base) B)
                              (hopDev? V η (suc base ^ V * B))
                              ev (InstEmit.events em))
            str hB hS
  where
  ev : (x : InstEvent (Val _ u)) →
       eventB? Bsz Ψ x ≡ true → hopSpnev? V η (suc base) B x ≡ true →
       hopDev? V η (suc base ^ V * B) x ≡ true
  ev (value v) hb hs =
    T⇒≡true _ (≤⇒≤ᵇ
      (≤-trans (≤ᵇ⇒≤ (hopDᵛ V η u v) (suc base ^ spnᵛ u v * B) (T-to hs))
               (*-monoˡ-≤ B (^-monoʳ-≤ (suc base)
                 (≤-trans (spn≤sizeᵛ u v)
                   (≤-trans (≤ᵇ⇒≤ (sizeᵛ u v) Bsz
                              (T-to (proj₁ (∧-true (sizeᵛ u v ≤ᵇ Bsz) _ hb))))
                            hBsz))))))
  ev (init _)    hb hs = refl
  ev (close _ _) hb hs = refl
  ev (handoff _) hb hs = refl
  ev complete    hb hs = refl

------------------------------------------------------------------
-- THE HEREDITARY FORM, and why the headline one is not enough.
--
-- The fold's invariant cannot be `hopDᵛ accᵢ ≤ (2 + P) ^ spnᵛ accᵢ * B`
-- on the accumulator ALONE, because it does not survive `fstᵗ`:
-- projecting a pair yields a component whose SPINE is smaller than the
-- pair's (spnᵛ takes `⊔` and adds one) while its DEPTH may be the whole
-- pair's (hopDᵛ takes the same `⊔`).  The headline bound at the pair
-- therefore says nothing at the component, and `evalWith` projects.
--
-- So the invariant is carried at every component: `valHopSpn?` recurses
-- through pairs and sums and bottoms out at `obs` with the headline
-- inequality.
--
-- IT STOPS AT `obs`, AND THAT IS THE WHOLE DESIGN DECISION (2026-08-19).
-- Hereditary-everywhere would mean recursing into the EXPRESSION a
-- stream value is, which is a second structural induction and a second
-- predicate to preserve.  It is not needed, and the reason is a property
-- of the syntax rather than of this proof: `Tm` HAS NO ELIMINATOR FOR
-- `obs`.  Nothing projects a component out of a stream value — the only
-- eliminating term formers are `fstᵗ`, `sndᵗ` and `caseᵗ`, which take
-- pairs and sums apart and nothing else.  Streams are only ever BUILT
-- (mapᵉ, mergeAllᵉ, …), and a builder needs its argument's headline
-- bound, not its interior.  So pairs and sums are exactly the positions
-- where a bound can be projected away, and exactly the positions the
-- recursion covers.
------------------------------------------------------------------

valHopSpn? : ∀ {n} {Γ : Ctx n} → ℕ → (Fin n → ℕ) → ℕ → ℕ →
             (u : Ty) → Val Γ u → Bool
valHopSpn? V η P B unitᵗ    _        = true
valHopSpn? V η P B boolᵗ    _        = true
valHopSpn? V η P B natᵗ     _        = true
valHopSpn? V η P B (s ×ᵗ t) (a , b)  =
  valHopSpn? V η P B s a ∧ valHopSpn? V η P B t b
valHopSpn? V η P B (s +ᵗ t) (inj₁ a) = valHopSpn? V η P B s a
valHopSpn? V η P B (s +ᵗ t) (inj₂ b) = valHopSpn? V η P B t b
valHopSpn? V η P B (obs t)  e        = hopDᵉ V η e ≤ᵇ (2 + P) ^ spnᵉ e * B

-- the headline follows from the hereditary form, and this is what makes
-- the extra structure free at the consumer: `⊔` of two exponentials is
-- the exponential of the `⊔`, and the pair node's own `suc` pays for it
valHopSpn?-hopD : ∀ {n} {Γ : Ctx n} (V : ℕ) (η : Fin n → ℕ) (P B : ℕ)
  (u : Ty) (v : Val Γ u) → valHopSpn? V η P B u v ≡ true →
  hopDᵛ V η u v ≤ (2 + P) ^ spnᵛ u v * B
valHopSpn?-hopD V η P B unitᵗ _ h = z≤n
valHopSpn?-hopD V η P B boolᵗ _ h = z≤n
valHopSpn?-hopD V η P B natᵗ  _ h = z≤n
valHopSpn?-hopD V η P B (s ×ᵗ t) (a , b) h =
  ⊔-lub (≤-trans (valHopSpn?-hopD V η P B s a (proj₁ sp)) (up (m≤m⊔n (spnᵛ s a) (spnᵛ t b))))
        (≤-trans (valHopSpn?-hopD V η P B t b (proj₂ sp)) (up (m≤n⊔m (spnᵛ s a) (spnᵛ t b))))
  where
  sp = ∧-true (valHopSpn? V η P B s a) (valHopSpn? V η P B t b) h
  up : ∀ {k} → k ≤ spnᵛ s a ⊔ spnᵛ t b →
       (2 + P) ^ k * B ≤ (2 + P) ^ suc (spnᵛ s a ⊔ spnᵛ t b) * B
  up le = *-monoˡ-≤ B (^-monoʳ-≤ (2 + P) (≤-trans le (n≤1+n (spnᵛ s a ⊔ spnᵛ t b))))
valHopSpn?-hopD V η P B (s +ᵗ t) (inj₁ a) h =
  ≤-trans (valHopSpn?-hopD V η P B s a h)
          (*-monoˡ-≤ B (^-monoʳ-≤ (2 + P) (n≤1+n (spnᵛ s a))))
valHopSpn?-hopD V η P B (s +ᵗ t) (inj₂ b) h =
  ≤-trans (valHopSpn?-hopD V η P B t b h)
          (*-monoˡ-≤ B (^-monoʳ-≤ (2 + P) (n≤1+n (spnᵛ t b))))
valHopSpn?-hopD V η P B (obs t) e h =
  ≤ᵇ⇒≤ (hopDᵉ V η e) ((2 + P) ^ spnᵉ e * B) (T-to h)

evHopSpnH? : ∀ {n} {Γ : Ctx n} {u} → ℕ → (Fin n → ℕ) → ℕ → ℕ →
             InstEvent (Val Γ u) → Bool
evHopSpnH? {u = u} V η P B (value v) = valHopSpn? V η P B u v
evHopSpnH? V η P B (init _)    = true
evHopSpnH? V η P B (close _ _) = true
evHopSpnH? V η P B (handoff _) = true
evHopSpnH? V η P B complete    = true

burstHopSpnH? : ∀ {n} {Γ : Ctx n} {u} → ℕ → (Fin n → ℕ) → ℕ → ℕ →
                Stream Γ u → Bool
burstHopSpnH? V η P B =
  all (λ em → all (evHopSpnH? V η P B) (InstEmit.events em))

-- and the burst-level projection, which is all the consumer needs
burstHopSpnH-headline : ∀ {n} {Γ : Ctx n} {u} (V P B : ℕ) (η : Fin n → ℕ)
  (str : Stream Γ u) →
  burstHopSpnH? V η P B str ≡ true →
  burstHopSpn? V η (2 + P) B str ≡ true
burstHopSpnH-headline {u = u} V P B η str h =
  all-impl (λ em → all (evHopSpnH? V η P B) (InstEmit.events em))
           (λ em → all (hopSpnev? V η (2 + P) B) (InstEmit.events em))
           (λ em → all-impl (evHopSpnH? V η P B) (hopSpnev? V η (2 + P) B)
                            ev (InstEmit.events em))
           str h
  where
  ev : (x : InstEvent (Val _ u)) →
       evHopSpnH? V η P B x ≡ true → hopSpnev? V η (2 + P) B x ≡ true
  ev (value v) hv = T⇒≡true _ (≤⇒≤ᵇ (valHopSpn?-hopD V η P B _ v hv))
  ev (init _)    _ = refl
  ev (close _ _) _ = refl
  ev (handoff _) _ = refl
  ev complete    _ = refl
