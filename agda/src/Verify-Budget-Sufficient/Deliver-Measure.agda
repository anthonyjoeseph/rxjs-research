-- THE MEASURES A DELIVERY IS CHARGED IN, and the caps-side facts that
-- price them.  A path measure charges the share sink NOTHING, which is
-- what the sink's own refutations kill: the fan-out walks registrations
-- the chain being charged never mentions.  The deliver measures below
-- are the path measures with that one clause replaced by a gas-indexed
-- allowance out of `Fan-Caps`, so every frame bound transfers clause by
-- clause and only the sink differs -- which is what the bridges at the
-- foot of this module state, each one a path measure plus the fan's
-- share.
--
-- The head of the file is the caps side: a program's nest depth is
-- bounded by its size, a frame's stored size by the cap that admitted
-- it, and a path's sums by its length times that cap.  Those are what
-- let a delivery's charge be read off `capsOK?` rather than off the
-- program, which is the whole reason the sink can be priced at all.

module Verify-Budget-Sufficient.Deliver-Measure where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Bool.ListAction using (all)
open import Data.Fin using (Fin; toℕ)
open import Data.List using (List; []; _∷_; length; foldr)
open import Data.Nat using (ℕ; suc; _+_; _*_; _^_; _⊔_; _≤_; z≤n; s≤s; _≤ᵇ_)
open import Data.Nat.Properties using
  (≤-refl; ≤-trans; ≤-reflexive; ≤ᵇ⇒≤; n≤1+n; m≤m+n; m≤n+m; m≤n⇒m≤1+n; +-assoc; +-comm;
  +-mono-≤; +-monoʳ-≤; +-monoˡ-≤; *-monoˡ-≤; *-monoʳ-≤; *-mono-≤; m^n>0; ⊔-lub; m≤m⊔n; m≤n⊔m;
  ^-distribˡ-+-*)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Vec using (lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (yes; no)

open import Rx.Exp using
  (Ctx; Exp; Tm; sizeᵉ; sizeᵗ; sizeᵗˢ; _≟ᵗ_;
   input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ;
   varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ; inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ)
open import Rx.Nest-Depth using (nestDᵉ; nestDᵗ; nestDᵗˢ)
open import Rx.Prim using (Source)
open import Rx.Evaluator using
  (Frame; map-f; scan-f; take-f; from-inner; thru-outer;
   Path; root; share-sink; _↠_; RegId; Chain; shareAdmit; sameSource)
open import Verify-Budget-Sufficient.Caps using (Caps)
open import Verify-Budget-Sufficient.Fan-Caps using (fanLen; fanSq)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (frameSz?; pathSz?; regsSz?)
open import Verify-Budget-Sufficient.Caps-Face.Part4 using (pathSz?-len)
open import Verify-Budget-Sufficient.Measures using (pathLen; ∧-true)
open import Verify-Budget-Sufficient.Nest-Store using
  (pathNestD; frameSzD; pathSzSum; pathNestF; frameNestF; 1≤frameNestF; frameNestF≡;
   chainsNestD; chainsNestF; chainsSzSum)
open import Decide using (T-to; ∧-intro)

-- EVERY NEST DEPTH IS UNDER A SIZE, over the whole term language at
-- once.  The mutuality is the language's: a term may carry a stream and
-- a stream may carry terms, so the three arms are one induction.
mutual
  nestDᵉ≤sizeᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (e : Exp Γ Δᵍ Δ Θ t) → nestDᵉ e ≤ sizeᵉ e
  nestDᵉ≤sizeᵉ (input i)        = z≤n
  nestDᵉ≤sizeᵉ (ofᵉ ts)         = m≤n⇒m≤1+n (nestDᵗˢ≤sizeᵗˢ ts)
  nestDᵉ≤sizeᵉ emptyᵉ           = z≤n
  nestDᵉ≤sizeᵉ (mapᵉ f e)       = m≤n⇒m≤1+n (+-mono-≤ (nestDᵗ≤sizeᵗ f) (nestDᵉ≤sizeᵉ e))
  nestDᵉ≤sizeᵉ (takeᵉ c e)      = m≤n⇒m≤1+n (≤-trans (nestDᵉ≤sizeᵉ e) (m≤n+m (sizeᵉ e) (sizeᵗ c)))
  nestDᵉ≤sizeᵉ (scanᵉ f z e)    =
    m≤n⇒m≤1+n (+-mono-≤ (≤-trans (+-mono-≤ (nestDᵗ≤sizeᵗ z) (nestDᵗ≤sizeᵗ f))
                                 (≤-reflexive (+-comm (sizeᵗ z) (sizeᵗ f))))
                        (nestDᵉ≤sizeᵉ e))
  nestDᵉ≤sizeᵉ (mergeAllᵉ _ e)  = s≤s (nestDᵉ≤sizeᵉ e)
  nestDᵉ≤sizeᵉ (switchAllᵉ e)   = s≤s (nestDᵉ≤sizeᵉ e)
  nestDᵉ≤sizeᵉ (exhaustAllᵉ e)  = s≤s (nestDᵉ≤sizeᵉ e)
  nestDᵉ≤sizeᵉ (μᵉ e)           = m≤n⇒m≤1+n (nestDᵉ≤sizeᵉ e)
  nestDᵉ≤sizeᵉ (varᵉ x)         = z≤n
  nestDᵉ≤sizeᵉ (deferᵉ e)       = z≤n

  nestDᵗ≤sizeᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (f : Tm Γ Δᵍ Δ Θ t) → nestDᵗ f ≤ sizeᵗ f
  nestDᵗ≤sizeᵗ (varᵗ x)      = z≤n
  nestDᵗ≤sizeᵗ unit̂          = z≤n
  nestDᵗ≤sizeᵗ (bool̂ _)      = z≤n
  nestDᵗ≤sizeᵗ (nat̂ _)       = z≤n
  nestDᵗ≤sizeᵗ (pairᵗ a b)   =
    m≤n⇒m≤1+n (⊔-lub (≤-trans (nestDᵗ≤sizeᵗ a) (m≤m+n (sizeᵗ a) (sizeᵗ b)))
                     (≤-trans (nestDᵗ≤sizeᵗ b) (m≤n+m (sizeᵗ b) (sizeᵗ a))))
  nestDᵗ≤sizeᵗ (fstᵗ p)      = m≤n⇒m≤1+n (nestDᵗ≤sizeᵗ p)
  nestDᵗ≤sizeᵗ (sndᵗ p)      = m≤n⇒m≤1+n (nestDᵗ≤sizeᵗ p)
  nestDᵗ≤sizeᵗ (inlᵗ a)      = m≤n⇒m≤1+n (nestDᵗ≤sizeᵗ a)
  nestDᵗ≤sizeᵗ (inrᵗ a)      = m≤n⇒m≤1+n (nestDᵗ≤sizeᵗ a)
  nestDᵗ≤sizeᵗ (caseᵗ s l r) =
    m≤n⇒m≤1+n (≤-trans
      (+-mono-≤ (nestDᵗ≤sizeᵗ s)
                (⊔-lub (≤-trans (nestDᵗ≤sizeᵗ l) (m≤m+n (sizeᵗ l) (sizeᵗ r)))
                       (≤-trans (nestDᵗ≤sizeᵗ r) (m≤n+m (sizeᵗ r) (sizeᵗ l)))))
      (≤-reflexive (sym (+-assoc (sizeᵗ s) (sizeᵗ l) (sizeᵗ r)))))
  nestDᵗ≤sizeᵗ (ifᵗ c a b)   =
    m≤n⇒m≤1+n (⊔-lub (⊔-lub
      (≤-trans (nestDᵗ≤sizeᵗ c) (≤-trans (m≤m+n (sizeᵗ c) (sizeᵗ a)) (m≤m+n (sizeᵗ c + sizeᵗ a) (sizeᵗ b))))
      (≤-trans (nestDᵗ≤sizeᵗ a) (≤-trans (m≤n+m (sizeᵗ a) (sizeᵗ c)) (m≤m+n (sizeᵗ c + sizeᵗ a) (sizeᵗ b)))))
      (≤-trans (nestDᵗ≤sizeᵗ b) (m≤n+m (sizeᵗ b) (sizeᵗ c + sizeᵗ a))))
  nestDᵗ≤sizeᵗ (primᵗ _ a)   = m≤n⇒m≤1+n (nestDᵗ≤sizeᵗ a)
  nestDᵗ≤sizeᵗ (strmᵗ e)     = m≤n⇒m≤1+n (nestDᵉ≤sizeᵉ e)

  nestDᵗˢ≤sizeᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (ts : List (Tm Γ Δᵍ Δ Θ t)) → nestDᵗˢ ts ≤ sizeᵗˢ ts
  nestDᵗˢ≤sizeᵗˢ []       = z≤n
  nestDᵗˢ≤sizeᵗˢ (y ∷ ys) =
    ⊔-lub (≤-trans (nestDᵗ≤sizeᵗ y) (m≤m+n (sizeᵗ y) (sizeᵗˢ ys)))
          (≤-trans (nestDᵗˢ≤sizeᵗˢ ys) (m≤n+m (sizeᵗˢ ys) (sizeᵗ y)))

-- AND THE CAPS SIDE OF A PATH: what `capsOK?` says about a frame is a
-- bound on the size it stores, and a path's sums are that bound once
-- per hop.  `pathSz?` carries the length bound in the same conjunct, so
-- the length factor comes out of the same receipt rather than needing a
-- premise of its own -- which is what makes the square form available
-- to the caller without a second hypothesis.
frameSzD≤ : ∀ {n} {Γ : Ctx n} {s u} (B : ℕ) (f : Frame Γ s u) →
  frameSz? B f ≡ true → frameSzD f ≤ B
frameSzD≤ B (map-f fn)         h = ≤ᵇ⇒≤ (sizeᵗ fn) B (T-to h)
frameSzD≤ B (scan-f fn _)      h = ≤ᵇ⇒≤ (sizeᵗ fn) B (T-to h)
frameSzD≤ B (take-f _)         h = z≤n
frameSzD≤ B (from-inner _ _ _) h = z≤n
frameSzD≤ B (thru-outer _ _)   h = z≤n

pathSzSum-len : ∀ {n} {Γ : Ctx n} {s t} (B : ℕ) (p : Path Γ s t) →
  pathSz? B p ≡ true → pathSzSum p ≤ pathLen p * B
pathSzSum-len B root           h = z≤n
pathSzSum-len B (share-sink _) h = z≤n
pathSzSum-len B (f ↠ p) h
  with ∧-true (frameSz? B f) ((suc (pathLen p) ≤ᵇ B) ∧ pathSz? B p) h
... | hf , hr with ∧-true (suc (pathLen p) ≤ᵇ B) (pathSz? B p) hr
...   | _ , hp = +-mono-≤ (frameSzD≤ B f hf) (pathSzSum-len B p hp)

pathNestD-len : ∀ {n} {Γ : Ctx n} {s t} (B : ℕ) (p : Path Γ s t) →
  1 ≤ B → pathSz? B p ≡ true → pathNestD p ≤ pathLen p * B
pathNestD-len B root           _  h = z≤n
pathNestD-len B (share-sink _) _  h = z≤n
pathNestD-len B (map-f fn ↠ p) 1B h
  with ∧-true (frameSz? B (map-f fn)) ((suc (pathLen p) ≤ᵇ B) ∧ pathSz? B p) h
... | hf , hr with ∧-true (suc (pathLen p) ≤ᵇ B) (pathSz? B p) hr
...   | _ , hp = +-mono-≤ (≤-trans (nestDᵗ≤sizeᵗ fn) (≤ᵇ⇒≤ (sizeᵗ fn) B (T-to hf)))
                          (pathNestD-len B p 1B hp)
pathNestD-len B (scan-f fn i ↠ p) 1B h
  with ∧-true (frameSz? B (scan-f fn i)) ((suc (pathLen p) ≤ᵇ B) ∧ pathSz? B p) h
... | hf , hr with ∧-true (suc (pathLen p) ≤ᵇ B) (pathSz? B p) hr
...   | _ , hp = +-mono-≤ (≤-trans (nestDᵗ≤sizeᵗ fn) (≤ᵇ⇒≤ (sizeᵗ fn) B (T-to hf)))
                          (pathNestD-len B p 1B hp)
pathNestD-len B (take-f i ↠ p) 1B h
  with ∧-true (suc (pathLen p) ≤ᵇ B) (pathSz? B p) h
... | _ , hp = ≤-trans (pathNestD-len B p 1B hp) (m≤n+m (pathLen p * B) B)
pathNestD-len B (from-inner o a i ↠ p) 1B h
  with ∧-true (suc (pathLen p) ≤ᵇ B) (pathSz? B p) h
... | _ , hp = ≤-trans (pathNestD-len B p 1B hp) (m≤n+m (pathLen p * B) B)
pathNestD-len B (thru-outer o i ↠ p) 1B h
  with ∧-true (suc (pathLen p) ≤ᵇ B) (pathSz? B p) h
... | _ , hp = +-mono-≤ 1B (pathNestD-len B p 1B hp)

pathSzSum-cap : ∀ {n} {Γ : Ctx n} {s t} (B : ℕ) (p : Path Γ s t) →
  pathSz? B p ≡ true → pathSzSum p ≤ B * B
pathSzSum-cap B p h =
  ≤-trans (pathSzSum-len B p h) (*-monoˡ-≤ B (pathSz?-len B p h))

-- THE DELIVER MEASURES: the path measures with the sink clause charging
-- its fan-out allowance instead of zero.  Frames step exactly as the
-- path measures do, so every bound on a frame transfers clause by
-- clause; only the sink differs.
deliverLen : ∀ {n} {Γ : Ctx n} {s t} → ℕ → Caps → Path Γ s t → ℕ
deliverLen g c root           = 0
deliverLen g c (share-sink _) = fanLen g c
deliverLen g c (f ↠ p)        = suc (deliverLen g c p)

deliverSzSum : ∀ {n} {Γ : Ctx n} {s t} → ℕ → Caps → Path Γ s t → ℕ
deliverSzSum g c root           = 0
deliverSzSum g c (share-sink _) = fanSq g c
deliverSzSum g c (f ↠ p)        = frameSzD f + deliverSzSum g c p

deliverNestD : ∀ {n} {Γ : Ctx n} {s t} → ℕ → Caps → Path Γ s t → ℕ
deliverNestD g c root                   = 0
deliverNestD g c (share-sink _)         = fanSq g c
deliverNestD g c (map-f f ↠ p)          = nestDᵗ f + deliverNestD g c p
deliverNestD g c (scan-f f _ ↠ p)       = nestDᵗ f + deliverNestD g c p
deliverNestD g c (take-f _ ↠ p)         = deliverNestD g c p
deliverNestD g c (from-inner _ _ _ ↠ p) = deliverNestD g c p
deliverNestD g c (thru-outer _ _ ↠ p)   = suc (deliverNestD g c p)

deliverNestF : ∀ {n} {Γ : Ctx n} {s t} → ℕ → Caps → Path Γ s t → ℕ
deliverNestF g c root           = 1
deliverNestF g c (share-sink _) = 2 ^ fanSq g c
deliverNestF g c (f ↠ p)        = frameNestF f * deliverNestF g c p

1≤deliverNestF : ∀ {n} {Γ : Ctx n} {s t} (g : ℕ) (c : Caps) (p : Path Γ s t) →
  1 ≤ deliverNestF g c p
1≤deliverNestF g c root           = s≤s z≤n
1≤deliverNestF g c (share-sink _) = m^n>0 2 (fanSq g c)
1≤deliverNestF g c (f ↠ p)        = *-mono-≤ (1≤frameNestF f) (1≤deliverNestF g c p)

deliverNestF≡ : ∀ {n} {Γ : Ctx n} {s t} (g : ℕ) (c : Caps) (p : Path Γ s t) →
  deliverNestF g c p ≡ 2 ^ deliverSzSum g c p
deliverNestF≡ g c root           = refl
deliverNestF≡ g c (share-sink _) = refl
deliverNestF≡ g c (f ↠ p)        =
  trans (cong₂ _*_ (frameNestF≡ f) (deliverNestF≡ g c p))
        (sym (^-distribˡ-+-* 2 (frameSzD f) (deliverSzSum g c p)))

-- a deliver measure exceeds its path measure by exactly one sink's
-- allowance, since a path ends in at most one sink
deliverLen-path : ∀ {n} {Γ : Ctx n} {s t} (g : ℕ) (c : Caps) (p : Path Γ s t) →
  deliverLen g c p ≤ pathLen p + fanLen g c
deliverLen-path g c root           = z≤n
deliverLen-path g c (share-sink _) = ≤-reflexive refl
deliverLen-path g c (f ↠ p)        = s≤s (deliverLen-path g c p)

deliverSzSum-path : ∀ {n} {Γ : Ctx n} {s t} (g : ℕ) (c : Caps) (p : Path Γ s t) →
  deliverSzSum g c p ≤ pathSzSum p + fanSq g c
deliverSzSum-path g c root           = z≤n
deliverSzSum-path g c (share-sink _) = ≤-reflexive refl
deliverSzSum-path g c (f ↠ p)        =
  ≤-trans (+-monoʳ-≤ (frameSzD f) (deliverSzSum-path g c p))
          (≤-reflexive (sym (+-assoc (frameSzD f) (pathSzSum p) (fanSq g c))))

deliverNestD-path : ∀ {n} {Γ : Ctx n} {s t} (g : ℕ) (c : Caps) (p : Path Γ s t) →
  deliverNestD g c p ≤ pathNestD p + fanSq g c
deliverNestD-path g c root                   = z≤n
deliverNestD-path g c (share-sink _)         = ≤-reflexive refl
deliverNestD-path g c (map-f f ↠ p)          =
  ≤-trans (+-monoʳ-≤ (nestDᵗ f) (deliverNestD-path g c p))
          (≤-reflexive (sym (+-assoc (nestDᵗ f) (pathNestD p) (fanSq g c))))
deliverNestD-path g c (scan-f f _ ↠ p)       =
  ≤-trans (+-monoʳ-≤ (nestDᵗ f) (deliverNestD-path g c p))
          (≤-reflexive (sym (+-assoc (nestDᵗ f) (pathNestD p) (fanSq g c))))
deliverNestD-path g c (take-f _ ↠ p)         = deliverNestD-path g c p
deliverNestD-path g c (from-inner _ _ _ ↠ p) = deliverNestD-path g c p
deliverNestD-path g c (thru-outer _ _ ↠ p)   = s≤s (deliverNestD-path g c p)

-- what a share hands each admitted chain: the admitted list is a
-- sublist of the registry, so it inherits the registry's caps facts —
-- its length bound and every path's `pathSz?` receipt
admSz? : ∀ {n} {Γ : Ctx n} {s t} → ℕ → List (RegId × Path Γ s t) → Bool
admSz? B = all (λ en → pathSz? B (proj₂ en))

shareAdmit-len : ∀ {n} {Γ : Ctx n} {t} (i : Fin n)
  (rs : List (RegId × Source × Chain Γ t)) →
  length (shareAdmit i rs) ≤ length rs
shareAdmit-len i [] = z≤n
shareAdmit-len {Γ = Γ} i ((rid , s , (u , p)) ∷ r)
  with sameSource (toℕ i) s | u ≟ᵗ lookup Γ i
... | false | _        = ≤-trans (shareAdmit-len i r) (n≤1+n (length r))
... | true  | no _     = ≤-trans (shareAdmit-len i r) (n≤1+n (length r))
... | true  | yes refl = s≤s (shareAdmit-len i r)

shareAdmit-sz : ∀ {n} {Γ : Ctx n} {t} (i : Fin n) (B : ℕ)
  (rs : List (RegId × Source × Chain Γ t)) →
  regsSz? B rs ≡ true → admSz? B (shareAdmit i rs) ≡ true
shareAdmit-sz i B [] h = refl
shareAdmit-sz {Γ = Γ} i B ((rid , s , (u , p)) ∷ r) h
  with sameSource (toℕ i) s | u ≟ᵗ lookup Γ i
     | ∧-true (pathSz? B p) (regsSz? B r) h
... | false | _        | _ , hr  = shareAdmit-sz i B r hr
... | true  | no _     | _ , hr  = shareAdmit-sz i B r hr
... | true  | yes refl | hp , hr = ∧-intro hp (shareAdmit-sz i B r hr)

-- and the same measures aggregated over a cascade's chain list,
-- mirroring the path aggregates its fold spends: lengths and depths
-- accumulate across the fold, factors multiply
chainsDelLen : ∀ {n} {Γ : Ctx n} {s t} → ℕ → Caps → List (RegId × Path Γ s t) → ℕ
chainsDelLen g c = foldr (λ rc acc → deliverLen g c (proj₂ rc) + acc) 0

chainsDelNestD : ∀ {n} {Γ : Ctx n} {s t} → ℕ → Caps → List (RegId × Path Γ s t) → ℕ
chainsDelNestD g c = foldr (λ rc acc → deliverNestD g c (proj₂ rc) ⊔ acc) 0

chainsDelNestF : ∀ {n} {Γ : Ctx n} {s t} → ℕ → Caps → List (RegId × Path Γ s t) → ℕ
chainsDelNestF g c = foldr (λ rc acc → deliverNestF g c (proj₂ rc) * acc) 1

1≤chainsDelNestF : ∀ {n} {Γ : Ctx n} {s t} (g : ℕ) (c : Caps)
  (cs : List (RegId × Path Γ s t)) → 1 ≤ chainsDelNestF g c cs
1≤chainsDelNestF g c []             = s≤s z≤n
1≤chainsDelNestF g c ((_ , p) ∷ cs) =
  *-mono-≤ (1≤deliverNestF g c p) (1≤chainsDelNestF g c cs)

-- THE EXPONENT THE CAPS RIDER TELESCOPES TO OVER A CHAIN LIST.  One
-- factor is spent per FRAME, so the fold's exponent is the total frame
-- count and not the chain count -- the same reason `chainsNestF` is a
-- product where `chainsNestD` is a max.  The path form sits beside the
-- deliver form because the bridges directly below relate the two, and
-- a fact relating two aggregates belongs with both of them.
chainsLenSum : ∀ {n} {Γ : Ctx n} {s t} →
  List (RegId × Path Γ s t) → ℕ
chainsLenSum = foldr (λ rc acc → pathLen (proj₂ rc) + acc) 0

chainsDelSzSum : ∀ {n} {Γ : Ctx n} {s t} → ℕ → Caps → List (RegId × Path Γ s t) → ℕ
chainsDelSzSum g c = foldr (λ rc acc → deliverSzSum g c (proj₂ rc) + acc) 0

chainsDelNestF≡ : ∀ {n} {Γ : Ctx n} {s t} (g : ℕ) (c : Caps)
  (cs : List (RegId × Path Γ s t)) →
  chainsDelNestF g c cs ≡ 2 ^ chainsDelSzSum g c cs
chainsDelNestF≡ g c []             = refl
chainsDelNestF≡ g c ((_ , p) ∷ cs) =
  trans (cong₂ _*_ (deliverNestF≡ g c p) (chainsDelNestF≡ g c cs))
        (sym (^-distribˡ-+-* 2 (deliverSzSum g c p) (chainsDelSzSum g c cs)))

-- THE BRIDGES A CONSUMER SPENDS, one per aggregate: a chain list costs
-- what its paths cost plus ONE fan allowance per chain, the allowance
-- being what the share sink charges and the path measures charge zero
-- for.  The depth bridge is the cheap one -- a max over the list needs
-- the allowance only once, however many chains carry it.
chainsDelLen-chains : ∀ {n} {Γ : Ctx n} {s t} (g : ℕ) (c : Caps)
  (cs : List (RegId × Path Γ s t)) →
  chainsDelLen g c cs ≤ chainsLenSum cs + length cs * fanLen g c
chainsDelLen-chains g c []             = z≤n
chainsDelLen-chains g c ((_ , p) ∷ cs) =
  ≤-trans (+-mono-≤ (deliverLen-path g c p) (chainsDelLen-chains g c cs))
          (≤-reflexive (shuffle (pathLen p) (fanLen g c) (chainsLenSum cs)
                                (length cs * fanLen g c)))
  where
  shuffle : ∀ w x y z → (w + x) + (y + z) ≡ (w + y) + (x + z)
  shuffle w x y z =
    trans (+-assoc w x (y + z))
      (trans (cong (w +_)
               (trans (sym (+-assoc x y z))
                      (trans (cong (_+ z) (+-comm x y)) (+-assoc y x z))))
             (sym (+-assoc w y (x + z))))

chainsDelSzSum-chains : ∀ {n} {Γ : Ctx n} {s t} (g : ℕ) (c : Caps)
  (cs : List (RegId × Path Γ s t)) →
  chainsDelSzSum g c cs ≤ chainsSzSum cs + length cs * fanSq g c
chainsDelSzSum-chains g c []             = z≤n
chainsDelSzSum-chains g c ((_ , p) ∷ cs) =
  ≤-trans (+-mono-≤ (deliverSzSum-path g c p) (chainsDelSzSum-chains g c cs))
          (≤-reflexive (shuffle (pathSzSum p) (fanSq g c) (chainsSzSum cs)
                                (length cs * fanSq g c)))
  where
  shuffle : ∀ w x y z → (w + x) + (y + z) ≡ (w + y) + (x + z)
  shuffle w x y z =
    trans (+-assoc w x (y + z))
      (trans (cong (w +_)
               (trans (sym (+-assoc x y z))
                      (trans (cong (_+ z) (+-comm x y)) (+-assoc y x z))))
             (sym (+-assoc w y (x + z))))

chainsDelNestD-chains : ∀ {n} {Γ : Ctx n} {s t} (g : ℕ) (c : Caps)
  (cs : List (RegId × Path Γ s t)) →
  chainsDelNestD g c cs ≤ chainsNestD cs + fanSq g c
chainsDelNestD-chains g c []             = z≤n
chainsDelNestD-chains g c ((_ , p) ∷ cs) =
  ⊔-lub (≤-trans (deliverNestD-path g c p)
                 (+-monoˡ-≤ (fanSq g c) (m≤m⊔n (pathNestD p) (chainsNestD cs))))
        (≤-trans (chainsDelNestD-chains g c cs)
                 (+-monoˡ-≤ (fanSq g c) (m≤n⊔m (pathNestD p) (chainsNestD cs))))

-- AND THE PATH FACTOR SITS UNDER THE DELIVERY FACTOR, frame for frame,
-- the two differing only at the sink -- where one charges nothing and
-- the other charges the fan.  A consumer holding a delivery bound and
-- owing a path one spends this rather than re-deriving the product.
pathNestF≤deliver : ∀ {n} {Γ : Ctx n} {s t} (g : ℕ) (c : Caps) (p : Path Γ s t) →
  pathNestF p ≤ deliverNestF g c p
pathNestF≤deliver g c root           = ≤-refl
pathNestF≤deliver g c (share-sink _) = m^n>0 2 (fanSq g c)
pathNestF≤deliver g c (f ↠ p)        =
  *-monoʳ-≤ (frameNestF f) (pathNestF≤deliver g c p)

chainsNestF≤ : ∀ {n} {Γ : Ctx n} {s t} (g : ℕ) (c : Caps)
  (cs : List (RegId × Path Γ s t)) → chainsNestF cs ≤ chainsDelNestF g c cs
chainsNestF≤ g c []             = ≤-refl
chainsNestF≤ g c ((_ , p) ∷ cs) =
  *-mono-≤ (pathNestF≤deliver g c p) (chainsNestF≤ g c cs)
