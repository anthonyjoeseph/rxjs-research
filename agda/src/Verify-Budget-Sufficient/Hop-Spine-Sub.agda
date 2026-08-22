------------------------------------------------------------------
-- THE PLUG SIDE OF THE SPINE BOUND: what a substitution costs.
--
-- Split from .Hop-Spine-Step because it is a new mutual family over
-- `Exp`/`Tm` and is not mutual with the step's induction over `Tm` —
-- the step consumes `hopD-sub-spnᵉ` as a finished fact, which is an
-- import.
--
-- WHAT IT PROVES.  `hopDᵉ` of a SUBSTITUTED expression is under
-- `(2 + P) ^ spnᵉ` of that substituted expression, times the budget.
-- The exponent is read off the SUBSTITUTED side deliberately: a plugged
-- value carries its own spine into the result, and that is precisely
-- what pays for the slope the plug is multiplied by.
--
-- WHY THE COEFFICIENT IS CARRIED (`c`), which is the whole design.  A
-- uniform-budget statement fails at `mapᵉ`: the clause's own
-- coefficient `pmᵗ V 0 f ⊔ 1` is a TEMPLATE-INTERNAL slope, bounded by
-- no hypothesis, so `hopDᵗ f + C * hopDᵉ e ≤ B` cannot be split into
-- two facts at budget `B`.  Carrying `c` splits it as `c * hopDᵗ f ≤ B`
-- and `(c * C) * hopDᵉ e ≤ B`, and the two recursive calls run at the
-- two different coefficients.  Nothing else in the statement moves.
------------------------------------------------------------------
module Verify-Budget-Sufficient.Hop-Spine-Sub where

open import Data.Bool using (Bool; true; _∧_)
open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _^_; _⊔_; _≤_; _≤ᵇ_; s≤s; z≤n)
open import Data.Nat.Properties using (≤ᵇ⇒≤; ≤⇒≤ᵇ; ≤-trans; 1+n≰n; ≤-refl; ≤-reflexive; ≤-total;
                                       ^-monoʳ-≤; *-mono-≤; *-monoˡ-≤; *-monoʳ-≤;
                                       +-mono-≤; +-monoˡ-≤; +-monoʳ-≤;
                                       ⊔-lub; m≤m⊔n; m≤n⊔m; ⊔-mono-≤;
                                       *-comm; *-identityˡ; *-identityʳ; *-distribˡ-⊔; *-assoc;
                                       +-identityʳ; +-comm; m≤m+n; m≤n+m; n≤1+n; *-zeroʳ;
                                       *-distribˡ-+; *-distribʳ-+; ^-distribˡ-+-*)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_) renaming (inj₁ to inl; inj₂ to inr)
open import Data.Sum     using (inj₁; inj₂)
open import Data.Fin  using (Fin)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans;
                                                          cong; cong₂; subst)

open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Rx.Exp using (Ty; Ctx; Val; Tm; Exp; Ren∈; ext∈;
                          renExp; renTm; renTms; wkTm; reify; ++Ren;
                          subΘExp; subΘTm; subΘTms; lookupEnv; varIx;
                          unitᵗ; boolᵗ; natᵗ; obs; _×ᵗ_; _+ᵗ_;
                          input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ;
                          mergeAllᵉ; concatAllᵉ; switchAllᵉ; exhaustAllᵉ;
                          μᵉ; varᵉ; deferᵉ;
                          varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ;
                          inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ)
open import Rx.Hop-Depth using (hopDᵉ; hopDᵗ; hopDᵛ; hopDᵗˢ; pmᵗ; pmᵉ; pmᵗˢ)
open import Rx.Hop-Spine using (spnᵉ; spnᵗ; spnᵗˢ)
open import Verify-Budget-Sufficient.Measures using (∧-true; 1*≤; hopD-wkReify; pm-subΘᵗ;
                                                    varIx-ix)
open import Verify-Budget-Sufficient.Hop-Spine-Face using (valHopSpn?; B≤powB)
open import Decide using (T-to; T⇒≡true; ifEq; ∧-intro)

------------------------------------------------------------------
-- THE ARITHMETIC, and it is one fact.  Every multiplying clause needs
-- to fold several `Q ^ sᵢ` summands into the single `Q ^ (Σ sᵢ)` its
-- own `spn` clause offers, and `2 ≤ x → 2 ≤ y → x + y ≤ x * y` is what
-- does it.  Both hypotheses hold for free: `Q = 2 + P` is at least 2,
-- and every spine is at least 1, so every `Q ^ sᵢ` is at least 2.
--
-- THIS IS WHY NO `1 ≤ P` HYPOTHESIS IS NEEDED ANYWHERE.  A cruder route
-- pulls the summands out as `k * Q ^ (Σ sᵢ)` and then needs `k ≤ Q`,
-- which fails at `scanᵉ` (three summands) when `P ≡ 0`.  Multiplying
-- the powers instead spends the spine that is already there.
------------------------------------------------------------------

m+m≡m*2 : ∀ m → m + m ≡ m * 2
m+m≡m*2 m = sym (trans (*-comm m 2) (cong (m +_) (+-identityʳ m)))

add≤mul : ∀ x y → 2 ≤ x → 2 ≤ y → x + y ≤ x * y
add≤mul x y hx hy with ≤-total x y
... | inl x≤y = ≤-trans (+-monoˡ-≤ y x≤y)
                (≤-trans (≤-reflexive (m+m≡m*2 y))
                (≤-trans (*-monoʳ-≤ y hx) (≤-reflexive (*-comm y x))))
... | inr y≤x = ≤-trans (+-monoʳ-≤ x y≤x)
                        (≤-trans (≤-reflexive (m+m≡m*2 x)) (*-monoʳ-≤ x hy))

-- three summands, by two applications: `x * y` is itself at least 2
add3≤mul3 : ∀ x y z → 2 ≤ x → 2 ≤ y → 2 ≤ z → x + y + z ≤ x * y * z
add3≤mul3 x y z hx hy hz =
  ≤-trans (+-monoˡ-≤ z (add≤mul x y hx hy))
          (add≤mul (x * y) z (≤-trans hx x≤xy) hz)
  where
  x≤xy : x ≤ x * y
  x≤xy = ≤-trans (≤-reflexive (sym (*-identityʳ x)))
                 (*-monoʳ-≤ x (≤-trans (n≤1+n 1) hy))

------------------------------------------------------------------
-- THE SPINE IS POSITIVE.  Every clause of `spnᵉ`/`spnᵗ` is literally
-- `1` or a `suc`, so this needs no induction except through `obs`.
------------------------------------------------------------------

1≤spnᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (e : Exp Γ Δᵍ Δ Θ t) → 1 ≤ spnᵉ e
1≤spnᵉ (input i)       = ≤-refl
1≤spnᵉ (ofᵉ ts)        = s≤s z≤n
1≤spnᵉ emptyᵉ          = ≤-refl
1≤spnᵉ (mapᵉ f e)      = s≤s z≤n
1≤spnᵉ (takeᵉ c e)     = s≤s z≤n
1≤spnᵉ (scanᵉ f z e)   = s≤s z≤n
1≤spnᵉ (mergeAllᵉ e)   = s≤s z≤n
1≤spnᵉ (concatAllᵉ e)  = s≤s z≤n
1≤spnᵉ (switchAllᵉ e)  = s≤s z≤n
1≤spnᵉ (exhaustAllᵉ e) = s≤s z≤n
1≤spnᵉ (μᵉ e)          = s≤s z≤n
1≤spnᵉ (varᵉ x)        = ≤-refl
1≤spnᵉ (deferᵉ e)      = s≤s z≤n

1≤spnᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (tm : Tm Γ Δᵍ Δ Θ t) → 1 ≤ spnᵗ tm
1≤spnᵗ (varᵗ x)      = ≤-refl
1≤spnᵗ unit̂          = ≤-refl
1≤spnᵗ (bool̂ _)      = ≤-refl
1≤spnᵗ (nat̂ _)       = ≤-refl
1≤spnᵗ (pairᵗ a b)   = s≤s z≤n
1≤spnᵗ (fstᵗ p)      = s≤s z≤n
1≤spnᵗ (sndᵗ p)      = s≤s z≤n
1≤spnᵗ (inlᵗ a)      = s≤s z≤n
1≤spnᵗ (inrᵗ a)      = s≤s z≤n
1≤spnᵗ (caseᵗ s l r) = s≤s z≤n
1≤spnᵗ (ifᵗ c a b)   = s≤s z≤n
1≤spnᵗ (primᵗ _ a)   = s≤s z≤n
1≤spnᵗ (strmᵗ e)     = s≤s z≤n

-- so every power of Q is at least 2, which is `add≤mul`'s hypothesis
1≤powQ : ∀ (P k : ℕ) → 1 ≤ (2 + P) ^ k
1≤powQ P zero    = ≤-refl
1≤powQ P (suc k) =
  *-mono-≤ {1} {2 + P} {1} {(2 + P) ^ k} (s≤s z≤n) (1≤powQ P k)

2≤powQ : ∀ (P s : ℕ) → 1 ≤ s → 2 ≤ (2 + P) ^ s
2≤powQ P zero    ()
2≤powQ P (suc s) _ =
  *-mono-≤ {2} {2 + P} {1} {(2 + P) ^ s} (s≤s (s≤s z≤n)) (1≤powQ P s)

-- THE EXPONENTS ARE EXPLICIT ON PURPOSE.  `(2 + P) ^ a` is not
-- invertible, so Agda cannot solve `a` from a goal mentioning the power
-- — an implicit-exponent version type-checks at its declaration and then
-- leaves an unsolved meta at EVERY call site.
powQ-mono : ∀ (P a b : ℕ) → a ≤ b → (2 + P) ^ a ≤ (2 + P) ^ b
powQ-mono P a b le = ^-monoʳ-≤ (2 + P) le

powB-mono : ∀ (P B a b : ℕ) → a ≤ b → (2 + P) ^ a * B ≤ (2 + P) ^ b * B
powB-mono P B a b le = *-monoˡ-≤ B (powQ-mono P a b le)

powB-suc : ∀ (P B a : ℕ) → (2 + P) ^ a * B ≤ (2 + P) ^ suc a * B
powB-suc P B a = powB-mono P B a (suc a) (n≤1+n a)

------------------------------------------------------------------
-- THE SPINE IS RENAMING-INVARIANT.  Every clause is a congruence:
-- `spn` reads only the SHAPE, and unlike `hopD`/`pm` it never looks at
-- a variable's index, so this needs none of `hopD-renᵉ`'s
-- index-preservation side condition.
------------------------------------------------------------------

mutual
  spn-renᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t}
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′)
    (e : Exp Γ Δᵍ Δ Θ t) → spnᵉ (renExp ρg ρd ρt e) ≡ spnᵉ e
  spn-renᵉ ρg ρd ρt (input i)  = refl
  spn-renᵉ ρg ρd ρt (ofᵉ ts)   = cong suc (spn-renᵗˢ ρg ρd ρt ts)
  spn-renᵉ ρg ρd ρt emptyᵉ     = refl
  spn-renᵉ ρg ρd ρt (mapᵉ f e) =
    cong suc (cong₂ _+_ (spn-renᵗ ρg ρd (ext∈ ρt) f) (spn-renᵉ ρg ρd ρt e))
  spn-renᵉ ρg ρd ρt (takeᵉ c e) =
    cong suc (cong₂ _+_ (spn-renᵗ ρg ρd ρt c) (spn-renᵉ ρg ρd ρt e))
  spn-renᵉ ρg ρd ρt (scanᵉ f z e) =
    cong suc (cong₂ _+_ (cong₂ _+_ (spn-renᵗ ρg ρd (ext∈ ρt) f)
                                   (spn-renᵗ ρg ρd ρt z))
                        (spn-renᵉ ρg ρd ρt e))
  spn-renᵉ ρg ρd ρt (mergeAllᵉ e)   = cong suc (spn-renᵉ ρg ρd ρt e)
  spn-renᵉ ρg ρd ρt (concatAllᵉ e)  = cong suc (spn-renᵉ ρg ρd ρt e)
  spn-renᵉ ρg ρd ρt (switchAllᵉ e)  = cong suc (spn-renᵉ ρg ρd ρt e)
  spn-renᵉ ρg ρd ρt (exhaustAllᵉ e) = cong suc (spn-renᵉ ρg ρd ρt e)
  spn-renᵉ ρg ρd ρt (μᵉ e)     = cong suc (spn-renᵉ (ext∈ ρg) ρd ρt e)
  spn-renᵉ ρg ρd ρt (varᵉ x)   = refl
  spn-renᵉ ρg ρd ρt (deferᵉ e) =
    cong suc (spn-renᵉ (λ ()) (++Ren ρg ρd) ρt e)

  spn-renᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t}
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′)
    (tm : Tm Γ Δᵍ Δ Θ t) → spnᵗ (renTm ρg ρd ρt tm) ≡ spnᵗ tm
  spn-renᵗ ρg ρd ρt (varᵗ x)     = refl
  spn-renᵗ ρg ρd ρt unit̂         = refl
  spn-renᵗ ρg ρd ρt (bool̂ _)     = refl
  spn-renᵗ ρg ρd ρt (nat̂ _)      = refl
  spn-renᵗ ρg ρd ρt (pairᵗ a b)  =
    cong suc (cong₂ _⊔_ (spn-renᵗ ρg ρd ρt a) (spn-renᵗ ρg ρd ρt b))
  spn-renᵗ ρg ρd ρt (fstᵗ p)     = cong suc (spn-renᵗ ρg ρd ρt p)
  spn-renᵗ ρg ρd ρt (sndᵗ p)     = cong suc (spn-renᵗ ρg ρd ρt p)
  spn-renᵗ ρg ρd ρt (inlᵗ a)     = cong suc (spn-renᵗ ρg ρd ρt a)
  spn-renᵗ ρg ρd ρt (inrᵗ a)     = cong suc (spn-renᵗ ρg ρd ρt a)
  spn-renᵗ ρg ρd ρt (caseᵗ s l r) =
    cong suc (cong₂ _+_ (spn-renᵗ ρg ρd ρt s)
                        (cong₂ _⊔_ (spn-renᵗ ρg ρd (ext∈ ρt) l)
                                   (spn-renᵗ ρg ρd (ext∈ ρt) r)))
  spn-renᵗ ρg ρd ρt (ifᵗ c a b) =
    cong suc (cong₂ _+_ (spn-renᵗ ρg ρd ρt c)
                        (cong₂ _⊔_ (spn-renᵗ ρg ρd ρt a)
                                   (spn-renᵗ ρg ρd ρt b)))
  spn-renᵗ ρg ρd ρt (primᵗ _ a) = cong suc (spn-renᵗ ρg ρd ρt a)
  spn-renᵗ ρg ρd ρt (strmᵗ e)   = cong suc (spn-renᵉ ρg ρd ρt e)

  spn-renᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t}
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′)
    (ts : List (Tm Γ Δᵍ Δ Θ t)) → spnᵗˢ (renTms ρg ρd ρt ts) ≡ spnᵗˢ ts
  spn-renᵗˢ ρg ρd ρt []       = refl
  spn-renᵗˢ ρg ρd ρt (y ∷ ys) =
    cong₂ _⊔_ (spn-renᵗ ρg ρd ρt y) (spn-renᵗˢ ρg ρd ρt ys)

------------------------------------------------------------------
-- THE PLUG, AND IT IS WHERE THE DRAG IS SPENT.  A value carrying the
-- hereditary receipt, plugged in and multiplied by a slope of at most
-- `2 + P`, still lands under `(2 + P) ^ spnᵗ` OF THE PLUGGED TERM.
--
-- WHY THE HEREDITARY PREDICATE AND NOT `valHopSpn?-hopD`'s FLATTENED
-- FORM.  The flattened route wants `spnᵛ t v < spnᵗ (wkTm
-- (reify v))` — one spare unit to pay for the slope — and that is
-- FALSE.  Take a pair of an `obs` of spine 1 with a ground nest of
-- spine 10: `spnᵛ` is `suc (1 ⊔ 10) ≡ 11`, and reifying gives `suc
-- (2 ⊔ 10) ≡ 11` as well, because the ground sibling reifies with no
-- extra node and is what the `⊔` selects.  The unit exists only on the
-- branch that actually CARRIES the hop, so it has to be collected
-- component by component — which is what recursing on the predicate
-- does, and the reason the predicate is hereditary in the first place.
------------------------------------------------------------------

plug-hopSpn : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ} (V : ℕ) (η : Fin n → ℕ) (P B c : ℕ)
  (t : Ty) (v : Val Γ t) → valHopSpn? V η P B t v ≡ true → c ≤ 2 + P →
  c * hopDᵛ V η t v
    ≤ (2 + P) ^ spnᵗ (wkTm {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} (reify v)) * B
plug-hopSpn V η P B c unitᵗ _ h hc = ≤-trans (≤-reflexive (*-zeroʳ c)) z≤n
plug-hopSpn V η P B c boolᵗ _ h hc = ≤-trans (≤-reflexive (*-zeroʳ c)) z≤n
plug-hopSpn V η P B c natᵗ  _ h hc = ≤-trans (≤-reflexive (*-zeroʳ c)) z≤n
plug-hopSpn {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} V η P B c (s ×ᵗ t) (a , b) h hc =
  ≤-trans (≤-reflexive (*-distribˡ-⊔ c (hopDᵛ V η s a) (hopDᵛ V η t b)))
          (⊔-lub (≤-trans (plug-hopSpn V η P B c s a (proj₁ sp) hc)
                          (up (m≤m⊔n sA sB)))
                 (≤-trans (plug-hopSpn V η P B c t b (proj₂ sp) hc)
                          (up (m≤n⊔m sA sB))))
  where
  sA = spnᵗ (wkTm {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} (reify a))
  sB = spnᵗ (wkTm {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} (reify b))
  sp = ∧-true (valHopSpn? V η P B s a) (valHopSpn? V η P B t b) h
  up : ∀ {k} → k ≤ sA ⊔ sB →
       (2 + P) ^ k * B ≤ (2 + P) ^ suc (sA ⊔ sB) * B
  up {k} le = powB-mono P B k (suc (sA ⊔ sB)) (≤-trans le (n≤1+n (sA ⊔ sB)))
plug-hopSpn {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} V η P B c (s +ᵗ t) (inl a) h hc =
  ≤-trans (plug-hopSpn V η P B c s a h hc)
          (powB-suc P B (spnᵗ (wkTm {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} (reify a))))
plug-hopSpn {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} V η P B c (s +ᵗ t) (inr b) h hc =
  ≤-trans (plug-hopSpn V η P B c t b h hc)
          (powB-suc P B (spnᵗ (wkTm {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} (reify b))))
-- THE ONE UNIT: the reified observable lands under a `strmᵗ`, and that
-- node's own `suc` in `spnᵗ` is the factor of `2 + P` the slope needs
plug-hopSpn {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} V η P B c (obs t) e h hc =
  ≤-trans (*-mono-≤ hc (≤ᵇ⇒≤ (hopDᵉ V η e) ((2 + P) ^ spnᵉ e * B) (T-to h)))
          (≤-reflexive
            (trans (sym (*-assoc (2 + P) ((2 + P) ^ spnᵉ e) B))
                   (cong (λ k → (2 + P) ^ k * B) (sym eqn))))
  where
  eqn : spnᵗ (wkTm {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} (reify {t = obs t} e))
          ≡ suc (spnᵉ e)
  eqn = cong suc (spn-renᵉ (λ ()) (λ ()) (λ ()) e)

------------------------------------------------------------------
-- FOLDING SUMMANDS INTO THE SPINE.  Each multiplying clause of `hopDᵉ`
-- has two or three summands and its `spnᵉ` clause offers their SUM as
-- an exponent, so the summands fold by `add≤mul` — no clause needs the
-- coefficient bounded, which is why `scanᵉ`'s three summands cost
-- nothing extra and `P ≡ 0` is fine.
------------------------------------------------------------------

pow-suc-add : ∀ (P B s : ℕ) → 1 ≤ s →
  B + (2 + P) ^ s * B ≤ (2 + P) ^ suc s * B
pow-suc-add P B s hs = *-monoˡ-≤ B step
  where
  x = (2 + P) ^ s
  step : suc x ≤ (2 + P) * x
  step = ≤-trans (+-monoˡ-≤ x (1≤powQ P s))
                 (≤-trans (≤-reflexive (m+m≡m*2 x))
                          (≤-trans (*-monoʳ-≤ x (m≤m+n 2 P))
                                   (≤-reflexive (*-comm x (2 + P)))))

pow2-fold : ∀ (P B a b : ℕ) → 1 ≤ a → 1 ≤ b →
  (2 + P) ^ a * B + (2 + P) ^ b * B ≤ (2 + P) ^ suc (a + b) * B
pow2-fold P B a b ha hb =
  ≤-trans (≤-reflexive (sym (*-distribʳ-+ B ((2 + P) ^ a) ((2 + P) ^ b))))
          (*-monoˡ-≤ B
            (≤-trans (add≤mul ((2 + P) ^ a) ((2 + P) ^ b)
                              (2≤powQ P a ha) (2≤powQ P b hb))
                     (≤-trans (≤-reflexive (sym (^-distribˡ-+-* (2 + P) a b)))
                              (powQ-mono P (a + b) (suc (a + b)) (n≤1+n (a + b))))))

pow3-fold : ∀ (P B a b d : ℕ) → 1 ≤ a → 1 ≤ b → 1 ≤ d →
  (2 + P) ^ a * B + (2 + P) ^ b * B + (2 + P) ^ d * B
    ≤ (2 + P) ^ suc (a + b + d) * B
pow3-fold P B a b d ha hb hd =
  ≤-trans (≤-reflexive
            (trans (cong (_+ ((2 + P) ^ d * B))
                         (sym (*-distribʳ-+ B ((2 + P) ^ a) ((2 + P) ^ b))))
                   (sym (*-distribʳ-+ B ((2 + P) ^ a + (2 + P) ^ b)
                                        ((2 + P) ^ d)))))
          (*-monoˡ-≤ B
            (≤-trans (add3≤mul3 ((2 + P) ^ a) ((2 + P) ^ b) ((2 + P) ^ d)
                                (2≤powQ P a ha) (2≤powQ P b hb) (2≤powQ P d hd))
                     (≤-trans (≤-reflexive
                                (trans (cong (_* ((2 + P) ^ d))
                                         (sym (^-distribˡ-+-* (2 + P) a b)))
                                       (sym (^-distribˡ-+-* (2 + P) (a + b) d))))
                              (powQ-mono P (a + b + d) (suc (a + b + d)) (n≤1+n (a + b + d))))))

-- the `⊔` clauses: a max of two budgeted things is budgeted at the max
pow⊔-fold : ∀ (P B a b : ℕ) →
  (2 + P) ^ a * B ⊔ (2 + P) ^ b * B ≤ (2 + P) ^ (a ⊔ b) * B
pow⊔-fold P B a b =
  ⊔-lub (powB-mono P B a (a ⊔ b) (m≤m⊔n a b))
        (powB-mono P B b (a ⊔ b) (m≤n⊔m a b))

------------------------------------------------------------------
-- THE SLOPE-SCALED RECEIPT.  `valHopSpn?` with a COEFFICIENT on the
-- hop, hereditarily.  It is what a value pushed onto the environment by
-- `caseᵗ` can carry and the plain receipt cannot: the scrutinee's value
-- is read through the branch's own binder slope, and that slope is
-- template-internal, so no hypothesis bounds it.  Scaling the receipt
-- instead of the budget keeps the statement closed under the `⊔` and
-- `+` clauses alike — which `Ps * hopDᵛ v ≤ B` is not, since a `mapᵉ`
-- splits into two summands and `B + B` is not `B`.
--
-- `valHopSpn?` is this at `c ≡ 1` (`valHopSpnC?-one`), and the two are
-- kept separate rather than one defined from the other because the
-- unscaled form is what every consumer of this family already reads.
valHopSpnC? : ∀ {n} {Γ : Ctx n} → ℕ → (Fin n → ℕ) → ℕ → ℕ → ℕ →
              (t : Ty) → Val Γ t → Bool
valHopSpnC? V η P B c unitᵗ    _        = true
valHopSpnC? V η P B c boolᵗ    _        = true
valHopSpnC? V η P B c natᵗ     _        = true
valHopSpnC? V η P B c (s ×ᵗ t) (a , b)  =
  valHopSpnC? V η P B c s a ∧ valHopSpnC? V η P B c t b
valHopSpnC? V η P B c (s +ᵗ t) (inj₁ a) = valHopSpnC? V η P B c s a
valHopSpnC? V η P B c (s +ᵗ t) (inj₂ b) = valHopSpnC? V η P B c t b
valHopSpnC? V η P B c (obs t)  e        =
  c * hopDᵉ V η e ≤ᵇ (2 + P) ^ spnᵉ e * B

-- ANTITONE IN THE COEFFICIENT, which is how every recursive call spends
-- it: a subterm's slope is under its parent's, so the parent's receipt
-- is already the subterm's.
valHopSpnC?-mono : ∀ {n} {Γ : Ctx n} (V : ℕ) (η : Fin n → ℕ) (P B c d : ℕ)
  (t : Ty) (v : Val Γ t) → c ≤ d →
  valHopSpnC? V η P B d t v ≡ true → valHopSpnC? V η P B c t v ≡ true
valHopSpnC?-mono V η P B c d unitᵗ _ le h = refl
valHopSpnC?-mono V η P B c d boolᵗ _ le h = refl
valHopSpnC?-mono V η P B c d natᵗ  _ le h = refl
valHopSpnC?-mono V η P B c d (s ×ᵗ t) (a , b) le h =
  ∧-intro (valHopSpnC?-mono V η P B c d s a le (proj₁ sp))
          (valHopSpnC?-mono V η P B c d t b le (proj₂ sp))
  where
  sp = ∧-true (valHopSpnC? V η P B d s a) (valHopSpnC? V η P B d t b) h
valHopSpnC?-mono V η P B c d (s +ᵗ t) (inj₁ a) le h =
  valHopSpnC?-mono V η P B c d s a le h
valHopSpnC?-mono V η P B c d (s +ᵗ t) (inj₂ b) le h =
  valHopSpnC?-mono V η P B c d t b le h
valHopSpnC?-mono V η P B c d (obs t) e le h =
  T⇒≡true _ (≤⇒≤ᵇ (≤-trans (*-monoˡ-≤ (hopDᵉ V η e) le)
                           (≤ᵇ⇒≤ (d * hopDᵉ V η e)
                                 ((2 + P) ^ spnᵉ e * B) (T-to h))))

-- a ZERO coefficient asserts nothing, and that is load-bearing: a
-- position the scrutinee does not mention arrives with exactly this
valHopSpnC?-zero : ∀ {n} {Γ : Ctx n} (V : ℕ) (η : Fin n → ℕ) (P B : ℕ)
  (t : Ty) (v : Val Γ t) → valHopSpnC? V η P B 0 t v ≡ true
valHopSpnC?-zero V η P B unitᵗ _ = refl
valHopSpnC?-zero V η P B boolᵗ _ = refl
valHopSpnC?-zero V η P B natᵗ  _ = refl
valHopSpnC?-zero V η P B (s ×ᵗ t) (a , b) =
  ∧-intro (valHopSpnC?-zero V η P B s a) (valHopSpnC?-zero V η P B t b)
valHopSpnC?-zero V η P B (s +ᵗ t) (inj₁ a) = valHopSpnC?-zero V η P B s a
valHopSpnC?-zero V η P B (s +ᵗ t) (inj₂ b) = valHopSpnC?-zero V η P B t b
valHopSpnC?-zero V η P B (obs t) e =
  T⇒≡true _ (≤⇒≤ᵇ (z≤n {(2 + P) ^ spnᵉ e * B}))

valHopSpnC?-one : ∀ {n} {Γ : Ctx n} (V : ℕ) (η : Fin n → ℕ) (P B : ℕ)
  (t : Ty) (v : Val Γ t) →
  valHopSpnC? V η P B 1 t v ≡ true → valHopSpn? V η P B t v ≡ true
valHopSpnC?-one V η P B unitᵗ _ h = refl
valHopSpnC?-one V η P B boolᵗ _ h = refl
valHopSpnC?-one V η P B natᵗ  _ h = refl
valHopSpnC?-one V η P B (s ×ᵗ t) (a , b) h =
  ∧-intro (valHopSpnC?-one V η P B s a (proj₁ sp))
          (valHopSpnC?-one V η P B t b (proj₂ sp))
  where
  sp = ∧-true (valHopSpnC? V η P B 1 s a) (valHopSpnC? V η P B 1 t b) h
valHopSpnC?-one V η P B (s +ᵗ t) (inj₁ a) h = valHopSpnC?-one V η P B s a h
valHopSpnC?-one V η P B (s +ᵗ t) (inj₂ b) h = valHopSpnC?-one V η P B t b h
valHopSpnC?-one V η P B (obs t) e h =
  T⇒≡true _ (≤⇒≤ᵇ (≤-trans (≤-reflexive (sym (*-identityˡ (hopDᵉ V η e))))
                           (≤ᵇ⇒≤ (1 * hopDᵉ V η e)
                                 ((2 + P) ^ spnᵉ e * B) (T-to h))))

-- THE PLUG, from a SCALED receipt.  Simpler than `plug-hopSpn`: the
-- coefficient is already inside the predicate, so the plug's own spine
-- unit is pure slack rather than the thing that pays.
plug-hopSpnC : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ} (V : ℕ) (η : Fin n → ℕ)
  (P B d : ℕ) (t : Ty) (v : Val Γ t) → valHopSpnC? V η P B d t v ≡ true →
  d * hopDᵛ V η t v
    ≤ (2 + P) ^ spnᵗ (wkTm {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} (reify v)) * B
plug-hopSpnC V η P B d unitᵗ _ h = ≤-trans (≤-reflexive (*-zeroʳ d)) z≤n
plug-hopSpnC V η P B d boolᵗ _ h = ≤-trans (≤-reflexive (*-zeroʳ d)) z≤n
plug-hopSpnC V η P B d natᵗ  _ h = ≤-trans (≤-reflexive (*-zeroʳ d)) z≤n
plug-hopSpnC {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} V η P B d (s ×ᵗ t) (a , b) h =
  ≤-trans (≤-reflexive (*-distribˡ-⊔ d (hopDᵛ V η s a) (hopDᵛ V η t b)))
          (⊔-lub (≤-trans (plug-hopSpnC V η P B d s a (proj₁ sp))
                          (powB-mono P B sA (suc (sA ⊔ sB))
                                     (≤-trans (m≤m⊔n sA sB) (n≤1+n (sA ⊔ sB)))))
                 (≤-trans (plug-hopSpnC V η P B d t b (proj₂ sp))
                          (powB-mono P B sB (suc (sA ⊔ sB))
                                     (≤-trans (m≤n⊔m sA sB) (n≤1+n (sA ⊔ sB))))))
  where
  sA = spnᵗ (wkTm {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} (reify a))
  sB = spnᵗ (wkTm {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} (reify b))
  sp = ∧-true (valHopSpnC? V η P B d s a) (valHopSpnC? V η P B d t b) h
plug-hopSpnC {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} V η P B d (s +ᵗ t) (inj₁ a) h =
  ≤-trans (plug-hopSpnC V η P B d s a h)
          (powB-suc P B (spnᵗ (wkTm {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} (reify a))))
plug-hopSpnC {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} V η P B d (s +ᵗ t) (inj₂ b) h =
  ≤-trans (plug-hopSpnC V η P B d t b h)
          (powB-suc P B (spnᵗ (wkTm {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} (reify b))))
plug-hopSpnC {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} V η P B d (obs t) e h =
  ≤-trans (≤ᵇ⇒≤ (d * hopDᵉ V η e) ((2 + P) ^ spnᵉ e * B) (T-to h))
          (≤-trans (powB-suc P B (spnᵉ e))
                   (≤-reflexive (cong (λ k → (2 + P) ^ k * B) (sym eqn))))
  where
  eqn : spnᵗ (wkTm {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} (reify {t = obs t} e))
          ≡ suc (spnᵉ e)
  eqn = cong suc (spn-renᵉ (λ ()) (λ ()) (λ ()) e)

------------------------------------------------------------------
-- THE ENVIRONMENT CONDITION, PER POSITION, AND THE DISJUNCTION IS THE
-- FINDING.  Three single-number hypotheses were tried and
-- each died at the opposite end from the one it fixed — a derived bound
-- decays per fold step, a global `∀ j → pmᵗ V j tm ≤ P` dies at a
-- CLOSED `caseᵗ` scrutinee, and a global product `pmᵗ V j tm * Ds j ≤ B`
-- is false at the fold's own call site, where `Ds 0` is the
-- accumulator's hop and exponential in its spine by construction.
--
-- What the three failures say together is that the multiplier condition
-- is NOT one inequality: a leaf of the result is either COPIED out of
-- the environment or BUILT by a `strmᵗ`, and the two need different
-- arithmetic.  A position whose slope is under `P` feeds a value that
-- must carry the hereditary receipt, and the plug's own spine unit pays
-- for the slope (`plug-hopSpn`).  A position whose slope is NOT under
-- `P` is reachable only through a PRODUCT the parent's own `hopDᵗ`
-- clause already paid for, and then no receipt on the value is needed.
--
-- DOWNWARD CLOSED IN THE SLOPE, which is what makes it usable at every
-- recursive call: a subterm's slope is under its parent's at every
-- index, so `EnvPlug-mono` re-uses the parent's condition unchanged.
EnvPlug : ∀ {n} {Γ : Ctx n} {Θ} (V : ℕ) (η : Fin n → ℕ) (P B : ℕ) →
  All (Val Γ) Θ → (ℕ → ℕ) → Set
EnvPlug V η P B []ᵃ                Ps = ⊤
EnvPlug V η P B (_∷ᵃ_ {x = t} v σ) Ps =
  ((Ps 0 ≤ P) × (valHopSpn? V η P B t v ≡ true)
     ⊎ (valHopSpnC? V η P B (Ps 0) t v ≡ true))
  × EnvPlug V η P B σ (λ j → Ps (suc j))

EnvPlug-mono : ∀ {n} {Γ : Ctx n} {Θ} (V : ℕ) (η : Fin n → ℕ) (P B : ℕ)
  (σ : All (Val Γ) Θ) (Ps Qs : ℕ → ℕ) → (∀ j → Qs j ≤ Ps j) →
  EnvPlug V η P B σ Ps → EnvPlug V η P B σ Qs
EnvPlug-mono V η P B []ᵃ      Ps Qs le h = tt
EnvPlug-mono V η P B (v ∷ᵃ σ) Ps Qs le (h0 , hσ) =
  head h0 , EnvPlug-mono V η P B σ (λ j → Ps (suc j)) (λ j → Qs (suc j))
                         (λ j → le (suc j)) hσ
  where
  head : ((Ps 0 ≤ P) × (valHopSpn? V η P B _ v ≡ true)
            ⊎ (valHopSpnC? V η P B (Ps 0) _ v ≡ true)) →
         ((Qs 0 ≤ P) × (valHopSpn? V η P B _ v ≡ true)
            ⊎ (valHopSpnC? V η P B (Qs 0) _ v ≡ true))
  head (inl (hp , hv)) = inl (≤-trans (le 0) hp , hv)
  head (inr hsc)       =
    inr (valHopSpnC?-mono V η P B (Qs 0) (Ps 0) _ v (le 0) hsc)

-- THE PLUG SITE.  Either disjunct lands the plugged value under the
-- spine of the term it becomes: the first spends the plug's own spine
-- unit on the slope (`plug-hopSpn`), the second is already under `B`
-- and the exponent is pure slack.
envPlug-plug : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θloc Θ t} (V : ℕ) (η : Fin n → ℕ)
  (P B d : ℕ) (Ps : ℕ → ℕ) (σ : All (Val Γ) Θ) → EnvPlug V η P B σ Ps →
  (z : t ∈ Θ) → d ≤ Ps (varIx z) →
  d * hopDᵛ V η t (lookupEnv σ z)
    ≤ (2 + P) ^ spnᵗ (wkTm {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θloc}
                           (reify (lookupEnv σ z))) * B
envPlug-plug V η P B d Ps (_∷ᵃ_ {x = t} v σ) (inl (hp , hv) , _) (here refl) hd =
  plug-hopSpn V η P B d t v hv
              (≤-trans hd (≤-trans hp (≤-trans (n≤1+n P) (n≤1+n (suc P)))))
-- the SCALED disjunct spends `plug-hopSpnC`; the plug's own spine unit
-- is slack here, because the coefficient is already inside the receipt
envPlug-plug V η P B d Ps (_∷ᵃ_ {x = t} v σ) (inr hsc , _) (here refl) hd =
  plug-hopSpnC V η P B d t v
               (valHopSpnC?-mono V η P B d (Ps 0) t v hd hsc)
envPlug-plug V η P B d Ps (v ∷ᵃ σ) (_ , hσ) (there z) hd =
  envPlug-plug V η P B d (λ j → Ps (suc j)) σ hσ z hd

-- the shape every multiplying clause needs twice: to feed a recursive
-- call at coefficient `c * w`, and to bound its slope by the parent's
-- picking a summand out of a three-way sum, and a branch out of a `⊔`
-- plus a remainder.  Stated as ℕ-only lemmas with EXPLICIT arguments
-- because the `≤-trans` chains they replace leave the middle term
-- unsolved: `+` is no more invertible than `^`, so nothing pins it.
fst3 : ∀ (a b d : ℕ) → a ≤ a + b + d
fst3 a b d = ≤-trans (m≤m+n a b) (m≤m+n (a + b) d)

mid3 : ∀ (a b d : ℕ) → b ≤ a + b + d
mid3 a b d = ≤-trans (m≤n+m b a) (m≤m+n (a + b) d)

lst3 : ∀ (a b d : ℕ) → d ≤ a + b + d
lst3 a b d = m≤n+m d (a + b)

⊔₁+ : ∀ (x y w : ℕ) → x ≤ (x ⊔ y) + w
⊔₁+ x y w = ≤-trans (m≤m⊔n x y) (m≤m+n (x ⊔ y) w)

⊔₂+ : ∀ (x y w : ℕ) → y ≤ (x ⊔ y) + w
⊔₂+ x y w = ≤-trans (m≤n⊔m x y) (m≤m+n (x ⊔ y) w)

c*w≤ : ∀ (c w x y : ℕ) → x ≤ y → (c * w) * x ≤ c * (w * y)
c*w≤ c w x y le =
  ≤-trans (≤-reflexive (*-assoc c w x)) (*-monoʳ-≤ c (*-monoʳ-≤ w le))

------------------------------------------------------------------
-- THE SUBSTITUTION INDUCTION.  `hopD-subΘᵉ` (.Measures) already prices
-- a substitution AFFINELY, with `pm` as the slope and `sumW` collecting
-- the plugs; that route cannot be used here and the reason is worth
-- recording, because it looks like the obvious one.
--
-- x DEAD ROUTE: one shot through `hopD-subΘᵉ`.  Its bound
-- SUMS over environment positions, so it pays for every plug even when
-- the plugs sit on different branches of a `⊔` — where `hopDᵉ` itself
-- takes the max and the spine grows by the max too.  Feeding that sum
-- into a `Q ^ spn` budget then demands `1 + M * P ≤ 2 + P` for an
-- environment of length M, false at M ≥ 2.  The information lost is the
-- `⊔` structure, and no arithmetic downstream of the sum can recover it.
--
-- x DEAD ROUTE: `sumW` replaced by a `⊔`-weighted `maxW`.
-- This was the recorded plan and it is REFUTED at `mapᵉ`, one clause in:
-- the clause needs `maxW Gf + C * maxW Ge ≤ maxW (λ j → Gf j + C * Ge j)`
-- — a sum of maxes under a max of sums — and that is backwards.  At
-- M ≡ 2 with weights `1 , 1`, `Gf ≡ (1 , 0)` and `Ge ≡ (0 , 1)` the
-- left is 2 and the right is 1.  `sumW`'s additivity is exactly what
-- the multiplying clauses consume, and `⊔` does not have it.
--
-- WHAT WORKS is to keep the sum out of the statement altogether and
-- induct with the COEFFICIENT carried, so each clause hands its own
-- coefficient to each recursive call and the `⊔` clauses stay `⊔`.
------------------------------------------------------------------

mutual
  hopD-sub-spnᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (V : ℕ) (η : Fin n → ℕ)
    (P B c : ℕ) (Θloc : List Ty) (σ : All (Val Γ) Θsub)
    (e : Exp Γ Δᵍ Δ (Θloc ++ Θsub) t) →
    c * hopDᵉ V η e ≤ B →
    EnvPlug V η P B σ (λ j → c * pmᵉ V (length Θloc + j) e) →
    c * hopDᵉ V η (subΘExp Θloc σ e)
      ≤ (2 + P) ^ spnᵉ (subΘExp Θloc σ e) * B
  hopD-sub-spnᵉ V η P B c Θloc σ (input i) hB hσ =
    ≤-trans hB (B≤powB P B 1)
  hopD-sub-spnᵉ V η P B c Θloc σ (ofᵉ ts) hB hσ =
    ≤-trans (hopD-sub-spnᵗˢ V η P B c Θloc σ ts hB hσ)
            (powB-suc P B (spnᵗˢ (subΘTms Θloc σ ts)))
  hopD-sub-spnᵉ V η P B c Θloc σ emptyᵉ hB hσ =
    ≤-trans (≤-reflexive (*-zeroʳ c)) z≤n
  hopD-sub-spnᵉ V η P B c Θloc σ (mapᵉ {s = s} f e) hB hσ
    rewrite pm-subΘᵗ V 0 (s ∷ Θloc) σ f (s≤s z≤n) =
    ≤-trans (≤-reflexive (*-distribˡ-+ c (hopDᵗ V η fs) (C * hopDᵉ V η es)))
            (≤-trans (+-mono-≤ ihf
                       (≤-trans (≤-reflexive (sym (*-assoc c C (hopDᵉ V η es)))) ihe))
                     (pow2-fold P B (spnᵗ fs) (spnᵉ es) (1≤spnᵗ fs) (1≤spnᵉ es)))
    where
    C  = pmᵗ V 0 f ⊔ 1
    fs = subΘTm (s ∷ Θloc) σ f
    es = subΘExp Θloc σ e
    ihf = hopD-sub-spnᵗ V η P B c (s ∷ Θloc) σ f
            (≤-trans (*-monoʳ-≤ c (m≤m+n (hopDᵗ V η f) (C * hopDᵉ V η e))) hB)
            (EnvPlug-mono V η P B σ
                          (λ j → c * pmᵉ V (length Θloc + j) (mapᵉ f e))
                          (λ j → c * pmᵗ V (suc (length Θloc + j)) f)
                          (λ j → *-monoʳ-≤ c (m≤m+n _ _)) hσ)
    ihe = hopD-sub-spnᵉ V η P B (c * C) Θloc σ e
            (≤-trans (c*w≤ c C (hopDᵉ V η e) (hopDᵉ V η e) ≤-refl)
                     (≤-trans (*-monoʳ-≤ c (m≤n+m (C * hopDᵉ V η e) (hopDᵗ V η f)))
                              hB))
            (EnvPlug-mono V η P B σ
                          (λ j → c * pmᵉ V (length Θloc + j) (mapᵉ f e))
                          (λ j → (c * C) * pmᵉ V (length Θloc + j) e)
                          (λ j → ≤-trans (c*w≤ c C _ _ ≤-refl)
                                         (*-monoʳ-≤ c (m≤n+m _ _))) hσ)
  hopD-sub-spnᵉ V η P B c Θloc σ (takeᵉ cnt e) hB hσ =
    ≤-trans (hopD-sub-spnᵉ V η P B c Θloc σ e hB hσ)
            (powB-mono P B (spnᵉ (subΘExp Θloc σ e))
                       (suc (spnᵗ (subΘTm Θloc σ cnt) + spnᵉ (subΘExp Θloc σ e)))
                       (≤-trans (m≤n+m _ _) (n≤1+n _)))
  hopD-sub-spnᵉ V η P B c Θloc σ (scanᵉ {s = s} {t = t} f z e) hB hσ
    rewrite pm-subΘᵗ V 0 ((t ×ᵗ s) ∷ Θloc) σ f (s≤s z≤n) =
    ≤-trans (≤-reflexive
              (trans (sym (*-assoc c Pw (hopDᵗ V η fs + hopDᵗ V η zs + hopDᵉ V η es)))
                     (trans (*-distribˡ-+ (c * Pw) (hopDᵗ V η fs + hopDᵗ V η zs)
                                                   (hopDᵉ V η es))
                            (cong (_+ ((c * Pw) * hopDᵉ V η es))
                                  (*-distribˡ-+ (c * Pw) (hopDᵗ V η fs)
                                                         (hopDᵗ V η zs))))))
            (≤-trans (+-mono-≤ (+-mono-≤ ihf ihz) ihe)
                     (pow3-fold P B (spnᵗ fs) (spnᵗ zs) (spnᵉ es)
                                (1≤spnᵗ fs) (1≤spnᵗ zs) (1≤spnᵉ es)))
    where
    Pw = (2 + pmᵗ V 0 f) ^ V
    fs = subΘTm ((t ×ᵗ s) ∷ Θloc) σ f
    zs = subΘTm Θloc σ z
    es = subΘExp Θloc σ e
    S  = hopDᵗ V η f + hopDᵗ V η z + hopDᵉ V η e
    inS : ∀ (x : ℕ) → x ≤ S → (c * Pw) * x ≤ B
    inS x le = ≤-trans (c*w≤ c Pw x S le) hB
    slope : ∀ (g : ℕ → ℕ) →
            (∀ j → g j ≤ pmᵗ V (suc (length Θloc + j)) f
                         + pmᵗ V (length Θloc + j) z
                         + pmᵉ V (length Θloc + j) e) →
            EnvPlug V η P B σ (λ j → (c * Pw) * g j)
    slope g le = EnvPlug-mono V η P B σ
                   (λ j → c * pmᵉ V (length Θloc + j) (scanᵉ f z e))
                   (λ j → (c * Pw) * g j) (λ j → c*w≤ c Pw _ _ (le j)) hσ
    ihf = hopD-sub-spnᵗ V η P B (c * Pw) ((t ×ᵗ s) ∷ Θloc) σ f
            (inS (hopDᵗ V η f) (fst3 (hopDᵗ V η f) (hopDᵗ V η z) (hopDᵉ V η e)))
            (slope (λ j → pmᵗ V (suc (length Θloc + j)) f)
                   (λ j → fst3 (pmᵗ V (suc (length Θloc + j)) f) (pmᵗ V (length Θloc + j) z)
                            (pmᵉ V (length Θloc + j) e)))
    ihz = hopD-sub-spnᵗ V η P B (c * Pw) Θloc σ z
            (inS (hopDᵗ V η z) (mid3 (hopDᵗ V η f) (hopDᵗ V η z) (hopDᵉ V η e)))
            (slope (λ j → pmᵗ V (length Θloc + j) z)
                   (λ j → mid3 (pmᵗ V (suc (length Θloc + j)) f) (pmᵗ V (length Θloc + j) z)
                            (pmᵉ V (length Θloc + j) e)))
    ihe = hopD-sub-spnᵉ V η P B (c * Pw) Θloc σ e
            (inS (hopDᵉ V η e) (lst3 (hopDᵗ V η f) (hopDᵗ V η z) (hopDᵉ V η e)))
            (slope (λ j → pmᵉ V (length Θloc + j) e)
                   (λ j → lst3 (pmᵗ V (suc (length Θloc + j)) f) (pmᵗ V (length Θloc + j) z)
                            (pmᵉ V (length Θloc + j) e)))
  hopD-sub-spnᵉ V η P B c Θloc σ (mergeAllᵉ e)   hB hσ = hop V η P B c Θloc σ e hB hσ
  hopD-sub-spnᵉ V η P B c Θloc σ (concatAllᵉ e)  hB hσ = hop V η P B c Θloc σ e hB hσ
  hopD-sub-spnᵉ V η P B c Θloc σ (switchAllᵉ e)  hB hσ = hop V η P B c Θloc σ e hB hσ
  hopD-sub-spnᵉ V η P B c Θloc σ (exhaustAllᵉ e) hB hσ = hop V η P B c Θloc σ e hB hσ
  hopD-sub-spnᵉ V η P B c Θloc σ (μᵉ e) hB hσ =
    ≤-trans (hopD-sub-spnᵉ V η P B c Θloc σ e hB hσ)
            (powB-suc P B (spnᵉ (subΘExp Θloc σ e)))
  hopD-sub-spnᵉ V η P B c Θloc σ (varᵉ x)   hB hσ =
    ≤-trans (≤-reflexive (*-zeroʳ c)) z≤n
  hopD-sub-spnᵉ V η P B c Θloc σ (deferᵉ e) hB hσ =
    ≤-trans (≤-reflexive (*-zeroʳ c)) z≤n

  -- THE HOP EDGE, shared by the four *All frames.  The frame's own `suc`
  -- costs a bare `c`, and the budget covers it because that same `suc`
  -- is inside the hypothesis: `c * suc x ≤ B` gives `c ≤ B` outright.
  hop : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (V : ℕ) (η : Fin n → ℕ)
    (P B c : ℕ) (Θloc : List Ty) (σ : All (Val Γ) Θsub)
    (e : Exp Γ Δᵍ Δ (Θloc ++ Θsub) t) →
    c * suc (hopDᵉ V η e) ≤ B →
    EnvPlug V η P B σ (λ j → c * pmᵉ V (length Θloc + j) e) →
    c * suc (hopDᵉ V η (subΘExp Θloc σ e))
      ≤ (2 + P) ^ suc (spnᵉ (subΘExp Θloc σ e)) * B
  hop V η P B c Θloc σ e hB hσ =
    ≤-trans (≤-reflexive (*-distribˡ-+ c 1 (hopDᵉ V η (subΘExp Θloc σ e))))
            (≤-trans (+-mono-≤ (≤-trans (≤-reflexive (*-identityʳ c)) c≤B)
                               (hopD-sub-spnᵉ V η P B c Θloc σ e
                                 (≤-trans (*-monoʳ-≤ c (n≤1+n (hopDᵉ V η e))) hB)
                                 hσ))
                     (pow-suc-add P B (spnᵉ (subΘExp Θloc σ e))
                                  (1≤spnᵉ (subΘExp Θloc σ e))))
    where
    c≤B : c ≤ B
    c≤B = ≤-trans (≤-trans (≤-reflexive (sym (*-identityʳ c)))
                           (*-monoʳ-≤ c (s≤s z≤n))) hB

  hopD-sub-spnᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (V : ℕ) (η : Fin n → ℕ)
    (P B c : ℕ) (Θloc : List Ty) (σ : All (Val Γ) Θsub)
    (tm : Tm Γ Δᵍ Δ (Θloc ++ Θsub) t) →
    c * hopDᵗ V η tm ≤ B →
    EnvPlug V η P B σ (λ j → c * pmᵗ V (length Θloc + j) tm) →
    c * hopDᵗ V η (subΘTm Θloc σ tm)
      ≤ (2 + P) ^ spnᵗ (subΘTm Θloc σ tm) * B
  -- THE PLUG.  A local variable stays and carries no hop; an
  -- environment one becomes its reified value, and `envPlug-plug` pays
  -- for the slope out of that value's own spine.
  hopD-sub-spnᵗ {Γ = Γ} {Δᵍ = Δᵍ} {Δ = Δ} V η P B c Θloc σ (varᵗ x) hB hσ
    with ∈-++⁻ Θloc x in eq
  ... | inl y = ≤-trans (≤-reflexive (*-zeroʳ c)) z≤n
  ... | inr z =
    ≤-trans (≤-reflexive (cong (c *_) (hopD-wkReify V η _ (lookupEnv σ z))))
            (envPlug-plug V η P B c
                          (λ j → c * pmᵗ {Γ = Γ} {Δᵍ = Δᵍ} {Δ = Δ}
                                         V (length Θloc + j) (varᵗ x))
                          σ hσ z hit)
    where
    hit : c ≤ c * pmᵗ {Γ = Γ} {Δᵍ = Δᵍ} {Δ = Δ}
                      V (length Θloc + varIx z) (varᵗ x)
    hit = ≤-trans (≤-reflexive (sym (*-identityʳ c)))
                  (*-monoʳ-≤ c (ifEq (varIx x) (length Θloc + varIx z)
                                     (varIx-ix Θloc x eq)))
  hopD-sub-spnᵗ V η P B c Θloc σ unit̂     hB hσ = ≤-trans (≤-reflexive (*-zeroʳ c)) z≤n
  hopD-sub-spnᵗ V η P B c Θloc σ (bool̂ _) hB hσ = ≤-trans (≤-reflexive (*-zeroʳ c)) z≤n
  hopD-sub-spnᵗ V η P B c Θloc σ (nat̂ _)  hB hσ = ≤-trans (≤-reflexive (*-zeroʳ c)) z≤n
  hopD-sub-spnᵗ V η P B c Θloc σ (pairᵗ a b) hB hσ =
    ≤-trans (≤-reflexive (*-distribˡ-⊔ c (hopDᵗ V η as) (hopDᵗ V η bs)))
            (≤-trans (⊔-mono-≤ iha ihb)
                     (≤-trans (pow⊔-fold P B (spnᵗ as) (spnᵗ bs))
                              (powB-suc P B (spnᵗ as ⊔ spnᵗ bs))))
    where
    as = subΘTm Θloc σ a
    bs = subΘTm Θloc σ b
    iha = hopD-sub-spnᵗ V η P B c Θloc σ a
            (≤-trans (*-monoʳ-≤ c (m≤m⊔n (hopDᵗ V η a) (hopDᵗ V η b))) hB)
            (EnvPlug-mono V η P B σ (λ j → c * pmᵗ V (length Θloc + j) (pairᵗ a b))
                          (λ j → c * pmᵗ V (length Θloc + j) a)
                          (λ j → *-monoʳ-≤ c (m≤m⊔n _ _)) hσ)
    ihb = hopD-sub-spnᵗ V η P B c Θloc σ b
            (≤-trans (*-monoʳ-≤ c (m≤n⊔m (hopDᵗ V η a) (hopDᵗ V η b))) hB)
            (EnvPlug-mono V η P B σ (λ j → c * pmᵗ V (length Θloc + j) (pairᵗ a b))
                          (λ j → c * pmᵗ V (length Θloc + j) b)
                          (λ j → *-monoʳ-≤ c (m≤n⊔m _ _)) hσ)
  hopD-sub-spnᵗ V η P B c Θloc σ (fstᵗ q) hB hσ =
    ≤-trans (hopD-sub-spnᵗ V η P B c Θloc σ q hB hσ)
            (powB-suc P B (spnᵗ (subΘTm Θloc σ q)))
  hopD-sub-spnᵗ V η P B c Θloc σ (sndᵗ q) hB hσ =
    ≤-trans (hopD-sub-spnᵗ V η P B c Θloc σ q hB hσ)
            (powB-suc P B (spnᵗ (subΘTm Θloc σ q)))
  hopD-sub-spnᵗ V η P B c Θloc σ (inlᵗ a) hB hσ =
    ≤-trans (hopD-sub-spnᵗ V η P B c Θloc σ a hB hσ)
            (powB-suc P B (spnᵗ (subΘTm Θloc σ a)))
  hopD-sub-spnᵗ V η P B c Θloc σ (inrᵗ a) hB hσ =
    ≤-trans (hopD-sub-spnᵗ V η P B c Θloc σ a hB hσ)
            (powB-suc P B (spnᵗ (subΘTm Θloc σ a)))
  hopD-sub-spnᵗ V η P B c Θloc σ (caseᵗ {s = s} {t = t} sc l r) hB hσ
    rewrite pm-subΘᵗ V 0 (s ∷ Θloc) σ l (s≤s z≤n)
          | pm-subΘᵗ V 0 (t ∷ Θloc) σ r (s≤s z≤n) =
    ≤-trans (≤-reflexive (*-distribˡ-+ c (hopDᵗ V η ls ⊔ hopDᵗ V η rs)
                                         (C * hopDᵗ V η scs)))
            (≤-trans (+-mono-≤ branch
                       (≤-trans (≤-reflexive (sym (*-assoc c C (hopDᵗ V η scs)))) ihsc))
                     (≤-trans (pow2-fold P B (spnᵗ ls ⊔ spnᵗ rs) (spnᵗ scs)
                                 (≤-trans (1≤spnᵗ ls) (m≤m⊔n (spnᵗ ls) (spnᵗ rs)))
                                 (1≤spnᵗ scs))
                              (≤-reflexive
                                (cong (λ k → (2 + P) ^ suc k * B)
                                      (+-comm (spnᵗ ls ⊔ spnᵗ rs) (spnᵗ scs))))))
    where
    C   = pmᵗ V 0 l ⊔ pmᵗ V 0 r ⊔ 1
    ls  = subΘTm (s ∷ Θloc) σ l
    rs  = subΘTm (t ∷ Θloc) σ r
    scs = subΘTm Θloc σ sc
    LR  = hopDᵗ V η l ⊔ hopDᵗ V η r
    ihl = hopD-sub-spnᵗ V η P B c (s ∷ Θloc) σ l
            (≤-trans (*-monoʳ-≤ c (≤-trans (m≤m⊔n (hopDᵗ V η l) (hopDᵗ V η r))
                                           (m≤m+n LR (C * hopDᵗ V η sc)))) hB)
            (EnvPlug-mono V η P B σ
                          (λ j → c * pmᵗ V (length Θloc + j) (caseᵗ sc l r))
                          (λ j → c * pmᵗ V (suc (length Θloc + j)) l)
                          (λ j → *-monoʳ-≤ c (⊔₁+ _ _ _)) hσ)
    ihr = hopD-sub-spnᵗ V η P B c (t ∷ Θloc) σ r
            (≤-trans (*-monoʳ-≤ c (≤-trans (m≤n⊔m (hopDᵗ V η l) (hopDᵗ V η r))
                                           (m≤m+n LR (C * hopDᵗ V η sc)))) hB)
            (EnvPlug-mono V η P B σ
                          (λ j → c * pmᵗ V (length Θloc + j) (caseᵗ sc l r))
                          (λ j → c * pmᵗ V (suc (length Θloc + j)) r)
                          (λ j → *-monoʳ-≤ c
                            (⊔₂+ (pmᵗ V (suc (length Θloc + j)) l)
                                 (pmᵗ V (suc (length Θloc + j)) r)
                                 (C * pmᵗ V (length Θloc + j) sc))) hσ)
    ihsc = hopD-sub-spnᵗ V η P B (c * C) Θloc σ sc
            (≤-trans (c*w≤ c C (hopDᵗ V η sc) (hopDᵗ V η sc) ≤-refl)
                     (≤-trans (*-monoʳ-≤ c (m≤n+m (C * hopDᵗ V η sc) LR)) hB))
            (EnvPlug-mono V η P B σ
                          (λ j → c * pmᵗ V (length Θloc + j) (caseᵗ sc l r))
                          (λ j → (c * C) * pmᵗ V (length Θloc + j) sc)
                          (λ j → ≤-trans (c*w≤ c C _ _ ≤-refl)
                                         (*-monoʳ-≤ c (m≤n+m _ _))) hσ)
    branch : c * (hopDᵗ V η ls ⊔ hopDᵗ V η rs)
               ≤ (2 + P) ^ (spnᵗ ls ⊔ spnᵗ rs) * B
    branch = ≤-trans (≤-reflexive (*-distribˡ-⊔ c (hopDᵗ V η ls) (hopDᵗ V η rs)))
                     (≤-trans (⊔-mono-≤ ihl ihr)
                              (pow⊔-fold P B (spnᵗ ls) (spnᵗ rs)))
  hopD-sub-spnᵗ V η P B c Θloc σ (ifᵗ cnd a b) hB hσ =
    ≤-trans (≤-reflexive (*-distribˡ-⊔ c (hopDᵗ V η as) (hopDᵗ V η bs)))
            (≤-trans (⊔-mono-≤ iha ihb)
                     (≤-trans (pow⊔-fold P B (spnᵗ as) (spnᵗ bs))
                              (powB-mono P B (spnᵗ as ⊔ spnᵗ bs)
                                (suc (spnᵗ (subΘTm Θloc σ cnd)
                                        + (spnᵗ as ⊔ spnᵗ bs)))
                                (≤-trans (m≤n+m _ _) (n≤1+n _)))))
    where
    as = subΘTm Θloc σ a
    bs = subΘTm Θloc σ b
    iha = hopD-sub-spnᵗ V η P B c Θloc σ a
            (≤-trans (*-monoʳ-≤ c (m≤m⊔n (hopDᵗ V η a) (hopDᵗ V η b))) hB)
            (EnvPlug-mono V η P B σ (λ j → c * pmᵗ V (length Θloc + j) (ifᵗ cnd a b))
                          (λ j → c * pmᵗ V (length Θloc + j) a)
                          (λ j → *-monoʳ-≤ c (m≤m⊔n _ _)) hσ)
    ihb = hopD-sub-spnᵗ V η P B c Θloc σ b
            (≤-trans (*-monoʳ-≤ c (m≤n⊔m (hopDᵗ V η a) (hopDᵗ V η b))) hB)
            (EnvPlug-mono V η P B σ (λ j → c * pmᵗ V (length Θloc + j) (ifᵗ cnd a b))
                          (λ j → c * pmᵗ V (length Θloc + j) b)
                          (λ j → *-monoʳ-≤ c (m≤n⊔m _ _)) hσ)
  hopD-sub-spnᵗ V η P B c Θloc σ (primᵗ _ a) hB hσ =
    ≤-trans (≤-reflexive (*-zeroʳ c)) z≤n
  hopD-sub-spnᵗ V η P B c Θloc σ (strmᵗ e) hB hσ =
    ≤-trans (hopD-sub-spnᵉ V η P B c Θloc σ e hB hσ)
            (powB-suc P B (spnᵉ (subΘExp Θloc σ e)))

  hopD-sub-spnᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (V : ℕ) (η : Fin n → ℕ)
    (P B c : ℕ) (Θloc : List Ty) (σ : All (Val Γ) Θsub)
    (ts : List (Tm Γ Δᵍ Δ (Θloc ++ Θsub) t)) →
    c * hopDᵗˢ V η ts ≤ B →
    EnvPlug V η P B σ (λ j → c * pmᵗˢ V (length Θloc + j) ts) →
    c * hopDᵗˢ V η (subΘTms Θloc σ ts)
      ≤ (2 + P) ^ spnᵗˢ (subΘTms Θloc σ ts) * B
  hopD-sub-spnᵗˢ V η P B c Θloc σ [] hB hσ =
    ≤-trans (≤-reflexive (*-zeroʳ c)) z≤n
  hopD-sub-spnᵗˢ V η P B c Θloc σ (y ∷ ys) hB hσ =
    ≤-trans (≤-reflexive (*-distribˡ-⊔ c (hopDᵗ V η yss) (hopDᵗˢ V η yss′)))
            (≤-trans (⊔-mono-≤ ihy ihys)
                     (pow⊔-fold P B (spnᵗ yss) (spnᵗˢ yss′)))
    where
    yss  = subΘTm Θloc σ y
    yss′ = subΘTms Θloc σ ys
    ihy = hopD-sub-spnᵗ V η P B c Θloc σ y
            (≤-trans (*-monoʳ-≤ c (m≤m⊔n (hopDᵗ V η y) (hopDᵗˢ V η ys))) hB)
            (EnvPlug-mono V η P B σ (λ j → c * pmᵗˢ V (length Θloc + j) (y ∷ ys))
                          (λ j → c * pmᵗ V (length Θloc + j) y)
                          (λ j → *-monoʳ-≤ c (m≤m⊔n _ _)) hσ)
    ihys = hopD-sub-spnᵗˢ V η P B c Θloc σ ys
            (≤-trans (*-monoʳ-≤ c (m≤n⊔m (hopDᵗ V η y) (hopDᵗˢ V η ys))) hB)
            (EnvPlug-mono V η P B σ (λ j → c * pmᵗˢ V (length Θloc + j) (y ∷ ys))
                          (λ j → c * pmᵗˢ V (length Θloc + j) ys)
                          (λ j → *-monoʳ-≤ c (m≤n⊔m _ _)) hσ)

------------------------------------------------------------------
-- THE SAME CONDITION WITHOUT THE DISJUNCTION.  Every position carries
-- the SCALED receipt outright.  This is strictly stronger than
-- `EnvPlug` (`envC⇒envPlug`), and it is what a COEFFICIENT-CARRYING
-- induction over terms needs, because its `varᵗ` clause copies a value
-- straight out of the environment into a conclusion that is itself
-- scaled — a slope bound plus an unscaled receipt is a factor `P` short
-- there, which is exactly why the two conditions both have to exist.
--
-- `EnvPlug` survives as the OUTER interface: the fold supplies an
-- unscaled receipt and a slope under `P`, which is its first disjunct,
-- and only that form can be met at the top.
EnvC : ∀ {n} {Γ : Ctx n} {Θ} (V : ℕ) (η : Fin n → ℕ) (P B : ℕ) →
  All (Val Γ) Θ → (ℕ → ℕ) → Set
EnvC V η P B []ᵃ                Ps = ⊤
EnvC V η P B (_∷ᵃ_ {x = t} v σ) Ps =
  (valHopSpnC? V η P B (Ps 0) t v ≡ true) × EnvC V η P B σ (λ j → Ps (suc j))

EnvC-mono : ∀ {n} {Γ : Ctx n} {Θ} (V : ℕ) (η : Fin n → ℕ) (P B : ℕ)
  (σ : All (Val Γ) Θ) (Ps Qs : ℕ → ℕ) → (∀ j → Qs j ≤ Ps j) →
  EnvC V η P B σ Ps → EnvC V η P B σ Qs
EnvC-mono V η P B []ᵃ      Ps Qs le h = tt
EnvC-mono V η P B (v ∷ᵃ σ) Ps Qs le (h0 , hσ) =
  valHopSpnC?-mono V η P B (Qs 0) (Ps 0) _ v (le 0) h0
  , EnvC-mono V η P B σ (λ j → Ps (suc j)) (λ j → Qs (suc j))
              (λ j → le (suc j)) hσ

envC-lookup : ∀ {n} {Γ : Ctx n} {Θ t} (V : ℕ) (η : Fin n → ℕ) (P B : ℕ)
  (Ps : ℕ → ℕ) (σ : All (Val Γ) Θ) → EnvC V η P B σ Ps → (z : t ∈ Θ) →
  valHopSpnC? V η P B (Ps (varIx z)) t (lookupEnv σ z) ≡ true
envC-lookup V η P B Ps (v ∷ᵃ σ) (h0 , _) (here refl) = h0
envC-lookup V η P B Ps (v ∷ᵃ σ) (_ , hσ) (there z) =
  envC-lookup V η P B (λ j → Ps (suc j)) σ hσ z

envC⇒envPlug : ∀ {n} {Γ : Ctx n} {Θ} (V : ℕ) (η : Fin n → ℕ) (P B : ℕ)
  (σ : All (Val Γ) Θ) (Ps : ℕ → ℕ) →
  EnvC V η P B σ Ps → EnvPlug V η P B σ Ps
envC⇒envPlug V η P B []ᵃ      Ps h         = tt
envC⇒envPlug V η P B (v ∷ᵃ σ) Ps (h0 , hσ) =
  inr h0 , envC⇒envPlug V η P B σ (λ j → Ps (suc j)) hσ

------------------------------------------------------------------
-- FROM THE DISJUNCTIVE CONDITION TO THE SCALED ONE.  This is what the
-- outer `caseᵗ` clause needs, and the side condition is the whole
-- content: a position held under the FIRST disjunct carries only an
-- unscaled receipt, so it can be re-used at a coefficient of at most 1.
-- The way out is that such a position must have coefficient ZERO, and
-- `big-forces-zero` is what makes that happen — when the branch
-- coefficient exceeds `P`, any position the scrutinee actually mentions
-- has parent slope above `P` and so cannot be under the first disjunct
-- at all.
------------------------------------------------------------------

-- the second summand of a `caseᵗ` clause dominates its own factor
≤2nd : ∀ (a c x : ℕ) → 1 ≤ c → x ≤ a + c * x
≤2nd a c x h = ≤-trans (1*≤ x c h) (m≤n+m (c * x) a)

1≤C : ∀ (x : ℕ) → 1 ≤ x ⊔ 1
1≤C x = m≤n⊔m x 1

big-forces-zero : ∀ (P C k : ℕ) → suc P ≤ C → C * k ≤ P → k ≡ 0
big-forces-zero P C zero    hC hle = refl
big-forces-zero P C (suc m) hC hle =
  ⊥-elim (1+n≰n (≤-trans hC
                   (≤-trans (≤-trans (≤-reflexive (sym (*-identityʳ C)))
                                     (*-monoʳ-≤ C (s≤s z≤n)))
                            hle)))

envPlug⇒envC : ∀ {n} {Γ : Ctx n} {Θ} (V : ℕ) (η : Fin n → ℕ) (P B : ℕ)
  (σ : All (Val Γ) Θ) (Ps Qs : ℕ → ℕ) →
  (∀ j → Qs j ≤ Ps j) → (∀ j → Ps j ≤ P → Qs j ≡ 0) →
  EnvPlug V η P B σ Ps → EnvC V η P B σ Qs
envPlug⇒envC V η P B []ᵃ      Ps Qs le hz h = tt
envPlug⇒envC V η P B (v ∷ᵃ σ) Ps Qs le hz (h0 , hσ) =
  head h0 , envPlug⇒envC V η P B σ (λ j → Ps (suc j)) (λ j → Qs (suc j))
                         (λ j → le (suc j)) (λ j → hz (suc j)) hσ
  where
  head : ((Ps 0 ≤ P) × (valHopSpn? V η P B _ v ≡ true)
            ⊎ (valHopSpnC? V η P B (Ps 0) _ v ≡ true)) →
         valHopSpnC? V η P B (Qs 0) _ v ≡ true
  head (inl (hp , _)) =
    subst (λ k → valHopSpnC? V η P B k _ v ≡ true) (sym (hz 0 hp))
          (valHopSpnC?-zero V η P B _ v)
  head (inr hsc) = valHopSpnC?-mono V η P B (Qs 0) (Ps 0) _ v (le 0) hsc
