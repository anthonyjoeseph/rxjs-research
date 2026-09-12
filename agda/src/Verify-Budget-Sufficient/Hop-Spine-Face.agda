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
--
-- DEAD ROUTE: A BOUND ON THE VALUE ALONE, however it is denominated —
--   the obvious repair, and one instantiation from looking checkable.
--   Read `hopDᵛ w ≤ (2 + fnCapᵛ w) ^ sizeᵛ w * <leaf depth>` and the
--   fold carries only ⊔-shaped quantities, immune to the shrink.  DEAD
--   because the base is wrong by an unbounded margin: the conjunct is
--   measured against a SLOPE (`pmᵗ V 0 f`) and fnCap is a CAP.  Take a
--   step function pairing a projection with a `strmᵗ` that ignores its
--   argument and carries a large `caseWᵗ` — the slope is 1 while the
--   cap grows without bound, and no choice of leaf depth repairs a base
--   already too big.  The same objection kills every measure of the
--   value alone, which is why the spine is spent INSIDE the fold rather
--   than instead of it.
------------------------------------------------------------------
module Verify-Budget-Sufficient.Hop-Spine-Face where

open import Data.Bool using (Bool; true; _∧_)
open import Data.Bool.ListAction using (all)
open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _^_; _⊔_; _≤_; _≤ᵇ_; z≤n)
open import Data.Nat.Properties using (≤ᵇ⇒≤; ≤⇒≤ᵇ; ≤-trans; ≤-reflexive; ^-monoʳ-≤; ^-monoˡ-≤; *-monoˡ-≤; ⊔-lub; m≤m⊔n; m≤n⊔m;
  n≤1+n; m≤m+n; *-identityˡ; +-identityʳ)
open import Data.List using ([])
open import Data.Fin  using (Fin)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum     using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Rx.Prim  using (InstEmit; InstEvent; init; value; close;
                            handoff; complete)
open import Data.Unit using (tt)
open import Data.Sum using () renaming (inj₁ to inl; inj₂ to inr)
open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Rx.Exp   using (Ty; Ctx; Val; Tm; evalTm; sizeᵛ; unitᵗ; boolᵗ; natᵗ; obs; _×ᵗ_; _+ᵗ_)
open import Rx.Hop-Depth using (hopDᵉ; hopDᵗ; hopDᵛ)
open import Rx.Hop-Spine using (spnᵉ; spnᵛ; spn≤sizeᵛ)
open import Rx.Evaluator using (Stream)
open import Verify-Budget-Sufficient.Measures using
  (burstB?; burstHopD?; eventB?; hopDev?; all-impl; ∧-true; all-zip; 1≤2^; hopD-evalWith)
open import Decide using (T-to; T⇒≡true; ∧-intro)

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
-- IT STOPS AT `obs`, AND THAT IS THE WHOLE DESIGN DECISION.
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

------------------------------------------------------------------
-- THE INTRODUCTION, and it is why the walk face does NOT have to be
-- restated hereditarily.
--
-- `hopDᵛ` is a `⊔` over the value's obs-leaves and nothing else — pairs
-- take `⊔`, sums pass through, the ground types are 0 — so a PLAIN
-- headline bound `hopDᵛ v ≤ B` already bounds EVERY leaf by B.  The
-- hereditary predicate asks each leaf for `hopDᵉ e ≤ (2 + P) ^ spnᵉ e *
-- B`, and `1 ≤ (2 + P) ^ k`, so the leaf's own spine is never needed:
-- the exponent is spare room.
--
-- That is the whole reason the source values arrive for free.  The fold
-- consumes `b`'s burst, whose receipt is the ORDINARY `burstHopD?` the
-- walk face already proves at a single number, and the seed's is
-- `hopDᵗ z`.  Both are headlines and both land here.  Only the
-- ACCUMULATOR needs the hereditary form maintained, because only it is
-- fed back through `applyFn` where a projection can strip a pair.
------------------------------------------------------------------

B≤powB : ∀ (P B k : ℕ) → B ≤ (2 + P) ^ k * B
B≤powB P B k =
  ≤-trans (≤-reflexive (sym (*-identityˡ B)))
          (*-monoˡ-≤ B (≤-trans (1≤2^ k) (^-monoˡ-≤ k (m≤m+n 2 P))))

valHopSpn?-intro : ∀ {n} {Γ : Ctx n} (V : ℕ) (η : Fin n → ℕ) (P B : ℕ)
  (u : Ty) (v : Val Γ u) → hopDᵛ V η u v ≤ B →
  valHopSpn? V η P B u v ≡ true
valHopSpn?-intro V η P B unitᵗ _ h = refl
valHopSpn?-intro V η P B boolᵗ _ h = refl
valHopSpn?-intro V η P B natᵗ  _ h = refl
valHopSpn?-intro V η P B (s ×ᵗ t) (a , b) h =
  ∧-intro (valHopSpn?-intro V η P B s a
            (≤-trans (m≤m⊔n (hopDᵛ V η s a) (hopDᵛ V η t b)) h))
          (valHopSpn?-intro V η P B t b
            (≤-trans (m≤n⊔m (hopDᵛ V η s a) (hopDᵛ V η t b)) h))
valHopSpn?-intro V η P B (s +ᵗ t) (inj₁ a) h = valHopSpn?-intro V η P B s a h
valHopSpn?-intro V η P B (s +ᵗ t) (inj₂ b) h = valHopSpn?-intro V η P B t b h
valHopSpn?-intro V η P B (obs t) e h =
  T⇒≡true _ (≤⇒≤ᵇ (≤-trans h (B≤powB P B (spnᵉ e))))

------------------------------------------------------------------
-- WHAT THE INTRODUCTION BUYS AT THE TWO PLACES THE SCAN WALK NEEDS IT.
-- The seed and the source burst both arrive as ORDINARY headline
-- receipts — `hopDᵗ z` and the walk face's own `burstHopD?` — and both
-- become hereditary here at no cost.
------------------------------------------------------------------

-- a closed term's value is no deeper than the term: hopD-evalWith at the
-- empty environment, where the slope sum is empty
hopD-evalTm : ∀ {n} {Γ : Ctx n} {u} (V : ℕ) (η : Fin n → ℕ)
  (z : Tm Γ [] [] [] u) → hopDᵛ V η u (evalTm z) ≤ hopDᵗ V η z
hopD-evalTm V η z =
  ≤-trans (hopD-evalWith V η (λ _ → 0) z []ᵃ tt)
          (≤-reflexive (+-identityʳ (hopDᵗ V η z)))

scanSeed-hopSpn : ∀ {n} {Γ : Ctx n} {u} (V : ℕ) (η : Fin n → ℕ) (P B : ℕ)
  (z : Tm Γ [] [] [] u) → hopDᵗ V η z ≤ B →
  valHopSpn? V η P B u (evalTm z) ≡ true
scanSeed-hopSpn V η P B z hz =
  valHopSpn?-intro V η P B _ (evalTm z) (≤-trans (hopD-evalTm V η z) hz)

burstHopSpnH-intro : ∀ {n} {Γ : Ctx n} {u} (V : ℕ) (η : Fin n → ℕ) (P B C : ℕ)
  (str : Stream Γ u) → C ≤ B → burstHopD? V η C str ≡ true →
  burstHopSpnH? V η P B str ≡ true
burstHopSpnH-intro {u = u} V η P B C str hCB h =
  all-impl (λ em → all (hopDev? V η C) (InstEmit.events em))
           (λ em → all (evHopSpnH? V η P B) (InstEmit.events em))
           (λ em → all-impl (hopDev? V η C) (evHopSpnH? V η P B)
                            ev (InstEmit.events em))
           str h
  where
  ev : (x : InstEvent (Val _ u)) →
       hopDev? V η C x ≡ true → evHopSpnH? V η P B x ≡ true
  ev (value v) hx =
    valHopSpn?-intro V η P B u v
      (≤-trans (≤ᵇ⇒≤ (hopDᵛ V η u v) C (T-to hx)) hCB)
  ev (init _)    _ = refl
  ev (close _ _) _ = refl
  ev (handoff _) _ = refl
  ev complete    _ = refl
