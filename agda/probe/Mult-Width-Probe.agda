------------------------------------------------------------------
-- THE MULTIPLICATIVE WIDTH ENGINE, PRICED BEFORE IT IS BUILT.
--
-- The ruling under test (2026-08-01): frameStep's WIDTH component stops
-- exponentiating per fold and starts MULTIPLYING —
--
--     cWid (frameStep j c) = cWid c * cSize c ^ j
--
-- — so that the COUNT may read cWid (which Width-Count-Probe refuted
-- against the exponential step, and which the charge face needs, since
-- scanFrame's receipt is `suc (length vals * suc (sizeᵗ fn))` and
-- `length vals` is a burst width).
--
-- Everything below is arithmetic on the recurrence alone — no
-- evaluator, no caps face — so it is checkable in seconds and it
-- answers the three questions the engine swap turns on BEFORE the
-- swap costs a day of clause work.
--
--   §1  WHAT THE SWAP IS, and the exact exchange rate against the old
--       step: ONE exponential fold IS `suc w` multiplicative ones.
--       That is the whole design claim in one equation — the swap is
--       sound exactly when a frame that exponentiates a width `w`
--       spends `w`-many receipts, which is what the scan receipt says
--       when `length vals` IS the exponent `outWᵉ e`.
--
--   §2  THE JOINT SLOPE.  blowup-tower-mult: one instant of the
--       multiplicative recurrence, with the count reading cWid, costs
--       FOUR tower stories on ALL THREE axes — the same four the size
--       axis alone cost before.  So σ = 4 and budgetAt does NOT move.
--       (Width-Count-Probe's `slope-fits` is the consumer: 2σ ≤ 8 + sz.)
--
--   §3  WHERE THE MARGIN ACTUALLY GOES, and it is not the slope: the
--       BASE.  capsAt's base cWid is a STATIC syntax measure, and the
--       static measure towers in the syntax (innWᵉ's scanᵉ clause
--       exponentiates once per node).  Two stories per node is the
--       right rate (iterFold-tower≤), so the base height is 3 + 2·sz
--       against the 3 + sz the size axis needs — and the root fuel then
--       fits EXACTLY, with zero margin.  One more story and it fails at
--       every program size.  This is the number the design session has
--       to rule on: budgetAt's `(7 + sz) * (id + 2)`.
--
-- Standalone, so src/Main.agda never reaches it.  Fast (~15 s).
------------------------------------------------------------------
module Mult-Width-Probe where

open import Data.Bool using (Bool; true; false)
open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _^_; _≤_; _≤ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤ᵇ⇒≤; ≤-trans; ≤-refl; ≤-reflexive; +-identityʳ; +-monoˡ-≤;
         +-monoʳ-≤; +-mono-≤; *-mono-≤; *-monoˡ-≤; *-monoʳ-≤; *-assoc;
         *-comm; *-identityʳ; *-identityˡ; *-suc; ^-monoʳ-≤; ^-monoˡ-≤; ^-*-assoc;
         ^-distribˡ-+-*; n≤1+n; m≤m+n; m≤n+m; m≤m*n; <⇒≤)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Verify-Budget-Sufficient
  using (Caps; caps; foldStep; iterFold; iterFold-suc;
         iterSize; iterSize-pow; iterSize-infl;
         towerℕ; towerℕ-mono; k≤towerℕ; sq≤2^; 1≤2^; n<2^n;
         tower-mul; tower-mul-suc; sum-fits; k≤tower; 2T≤; 3T≤)

------------------------------------------------------------------
-- §1  THE SWAP, AND ITS EXCHANGE RATE
--
-- The old step is ONE exponential per fold; the new one is ONE
-- multiplication per fold.  They are not far apart, and the distance
-- is exactly the width being folded:
--
--     foldStep S w = S ^ suc w = the multiplicative iterate at
--                                count `suc w`, from seed 1
--
-- so the swap is affordable EXACTLY when a frame that exponentiates a
-- width `w` reports `w`-or-more folds.  It does, by the shape of the
-- measure that does the exponentiating: `innWᵉ (scanᵉ f z e)` is
-- `(pmIᵗ 0 f ⊔ 1) ^ (outWᵉ e) * …`, whose exponent IS the source's
-- payload count — and the receipt `scanFrame-caps` reports is
-- `suc (length vals * suc (sizeᵗ fn))`, one per payload.  The
-- exponent and the receipt count are the same number.
------------------------------------------------------------------

-- the multiplicative iterate, in the definitional-equality style of
-- iterSize (so `frameStep`'s components stay a family)
iterMul : ℕ → ℕ → ℕ → ℕ
iterMul S j w = w * S ^ j

iterMul-0 : ∀ (S w : ℕ) → iterMul S 0 w ≡ w
iterMul-0 S w = *-identityʳ w

-- the step, as the caps face will consume it: one more fold is one
-- more factor of S, on the OUTSIDE
iterMul-suc : ∀ (S j w : ℕ) → iterMul S (suc j) w ≡ S * iterMul S j w
iterMul-suc S j w =
  solve 3 (λ s j′ w′ → w′ :* (s :* j′) := s :* (w′ :* j′)) refl S (S ^ j) w

-- THE EXCHANGE RATE.  One exponential fold is `suc w` multiplicative
-- folds from seed 1 — and from seed w, `suc w` of them are already
-- more than enough
fold-as-mult : ∀ (S w : ℕ) → foldStep S w ≡ iterMul S (suc w) 1
fold-as-mult S w = sym (*-identityˡ (S ^ suc w))

mult-covers-fold : ∀ (S w : ℕ) → 1 ≤ w → foldStep S w ≤ iterMul S (suc w) w
mult-covers-fold S w hw =
  ≤-trans (≤-reflexive (fold-as-mult S w))
          (*-monoˡ-≤ (S ^ suc w) hw)

------------------------------------------------------------------
-- §2  THE ENGINE, AND ITS JOINT SLOPE
--
-- The count now reads cWid — `D̂ c * cSize c * suc (cWid c)`, the
-- charge face's own shape (one subscribe's / one delivery's worth,
-- times the deliveries) — and the width axis is multiplicative.  The
-- question capsAt-tower asks is what ONE instant costs in tower
-- stories, jointly, on all three axes.
--
-- IT IS FOUR, the same four the size axis cost with the count that did
-- NOT read cWid.  The accounting, at a level T = towerℕ m (m ≥ 3, so
-- T ≥ 16), with cSize ≤ T, suc cWid ≤ T, suc cReg ≤ T:
--
--   THE COUNT      J = D̂·S·(1+W(1+S)) = 2^(2^R) · (S·(1+W(1+S)))
--                    ≤ 2^(2^R) · 2^(T+T) = 2^(2^R + 2T) ≤ 2^(2^T)
--                    = towerℕ (2+m)                        TWO stories
--                  (the whole receipt rides in the EXPONENT beside the
--                   delivery tower, by sq≤2^ TWICE — which is why the
--                   width factor is free and the fifth story
--                   Width-Count-Probe priced never appears.  The strict
--                   registry hypothesis is what pays for it: `suc R ≤ T`
--                   leaves half of 2^T for the receipt)
--   THE SIZE       (3T) per fold, J folds, T·(J+1) ≤ towerℕ (3+m)
--                                                        TWO more
--   THE WIDTH      W · S^J ≤ T^(J+1) ≤ 2^(T·(J+1))       rides along
--   THE REGISTRY   R · suc (J·S)                          rides along
--
-- So σ = 4, `slope-fits` is satisfied with sz stories to spare, and
-- budgetAt's (7 + sz)·(id + 2) does not move.  THAT IS THE WHOLE POINT
-- OF THE SWAP: under the exponential step the width axis was not
-- boundable by ANY linear-height tower once the count read it
-- (Width-Count-Probe's two-instants); under this one it lands at the
-- same level as the size axis.
------------------------------------------------------------------

D̂ : Caps → ℕ
D̂ c = 2 ^ (2 ^ Caps.cReg c)

-- the multiplicative frameStep
mFrame : ℕ → Caps → Caps
mFrame j c =
  caps (iterSize (Caps.cSize c) j (Caps.cSize c))
       (iterMul (Caps.cSize c) j (Caps.cWid c))
       (Caps.cReg c * suc (j * Caps.cSize c))

-- THE COUNT, READING cWid — and reading it through the RECEIPT rather
-- than bare, because bare is measured false.  Charge-Probe's progW row
-- breaks `D * cSize * suc cWid` at the tight admissible caps (47
-- against 1 * 20 * 2 = 40); what the receipt table dictates is one
-- frame ≤ `suc (cWid * suc cSize)`, a chain ≤ cSize frames, a cascade
-- ≤ D deliveries — and that form covers every measured row (47 against
-- 440).  So the count is CUBIC in the caps, and the question §2 answers
-- is whether a cubic count still costs four stories.  It does.
mCount : Caps → ℕ
mCount c = D̂ c * Caps.cSize c * suc (Caps.cWid c * suc (Caps.cSize c))

mBlow : Caps → Caps
mBlow c = mFrame (mCount c) c

-- the entry endpoint, by computation (frameStep-0's counterpart)
mFrame-0 : ∀ (c : Caps) → mFrame 0 c ≡ c
mFrame-0 (caps s w r) =
  trans (cong (λ x → caps s x (r * suc (0 * s))) (*-identityʳ w))
        (cong (λ x → caps s w x) (*-identityʳ r))

-- THE COUNT'S ARITHMETIC, and the one place the registry bound must be
-- STRICT — .Caps's `sum-fits` with room for TWO level-sized summands
-- instead of one, which is what the cubic bracket costs
sum-fits2 : ∀ (R T : ℕ) → suc R ≤ T → 7 ≤ T → 2 ^ R + (T + T) ≤ 2 ^ T
sum-fits2 R (suc T′) (s≤s hR) (s≤s h6) =
  ≤-trans (+-mono-≤ (^-monoʳ-≤ 2 hR) two-fits)
          (≤-reflexive (cong (2 ^ T′ +_) (sym (+-identityʳ (2 ^ T′)))))
  where
  two-fits : suc T′ + suc T′ ≤ 2 ^ T′
  two-fits =
    ≤-trans (≤-reflexive (solve 1 (λ x → (con 1 :+ x) :+ (con 1 :+ x)
                                          := con 2 :+ con 2 :* x) refl T′))
    (≤-trans (m≤m+n (2 + 2 * T′) (2 + 2 * T′ + T′ * T′))
    (≤-trans (≤-reflexive (solve 1 (λ x → (con 2 :+ con 2 :* x)
                                            :+ ((con 2 :+ con 2 :* x) :+ x :* x)
                                            := (con 2 :+ x) :* (con 2 :+ x))
                                 refl T′))
             (sq≤2^ T′ h6)))

blowup-tower-mult : ∀ (m : ℕ) (c : Caps) → 3 ≤ m →
  1 ≤ Caps.cSize c →
  Caps.cSize c ≤ towerℕ m →
  suc (Caps.cWid c) ≤ towerℕ m →
  suc (Caps.cReg c) ≤ towerℕ m →
  (Caps.cSize (mBlow c) ≤ towerℕ (4 + m))
  × (suc (Caps.cWid (mBlow c)) ≤ towerℕ (4 + m))
  × (suc (Caps.cReg (mBlow c)) ≤ towerℕ (4 + m))
blowup-tower-mult m c 3≤m 1≤S hS hW hR = sizeGoal , widGoal , regGoal
  where
  S  = Caps.cSize c
  W  = Caps.cWid c
  R  = Caps.cReg c
  Tw = towerℕ m
  J  = mCount c

  hR′ : R ≤ Tw
  hR′ = ≤-trans (n≤1+n R) hR

  hW′ : W ≤ Tw
  hW′ = ≤-trans (n≤1+n W) hW

  1≤Tw : 1 ≤ Tw
  1≤Tw = ≤-trans 1≤S hS

  6≤Tw : 6 ≤ Tw
  6≤Tw = ≤-trans (≤ᵇ⇒≤ 6 16 _) (towerℕ-mono {3} {m} 3≤m)

  1≤J : 1 ≤ J
  1≤J = *-mono-≤ (*-mono-≤ (1≤2^ (2 ^ R)) 1≤S) (s≤s z≤n)

  7≤Tw : 7 ≤ Tw
  7≤Tw = ≤-trans (≤ᵇ⇒≤ 7 16 _) (towerℕ-mono {3} {m} 3≤m)

  -- ONE FRAME'S RECEIPT sits under a square, hence under 2 ^ T
  B≤ : suc (W * suc S) ≤ 2 ^ Tw
  B≤ =
    ≤-trans (s≤s (*-mono-≤ hW′ (s≤s hS)))
    (≤-trans (≤-trans (m≤m+n (suc (Tw * suc Tw)) (3 + 3 * Tw))
                      (≤-reflexive
                        (sym (solve 1 (λ x → (con 2 :+ x) :* (con 2 :+ x)
                                              := (con 1 :+ x :* (con 1 :+ x))
                                                 :+ (con 3 :+ con 3 :* x))
                                    refl Tw))))
             (sq≤2^ Tw 6≤Tw))

  -- the two non-delivery factors together sit under TWO of them, which
  -- is what makes the count cubic-but-still-two-stories
  SB≤ : S * suc (W * suc S) ≤ 2 ^ (Tw + Tw)
  SB≤ = ≤-trans (*-mono-≤ (≤-trans hS (<⇒≤ (n<2^n Tw))) B≤)
                (≤-reflexive (sym (^-distribˡ-+-* 2 Tw Tw)))

  -- THE COUNT: two stories, the whole receipt riding in the exponent
  J≤P : J ≤ towerℕ (2 + m)
  J≤P =
    ≤-trans (≤-reflexive (*-assoc (2 ^ (2 ^ R)) S (suc (W * suc S))))
    (≤-trans (*-monoʳ-≤ (2 ^ (2 ^ R)) SB≤)
    (≤-trans (≤-reflexive (sym (^-distribˡ-+-* 2 (2 ^ R) (Tw + Tw))))
             (^-monoʳ-≤ 2 (sum-fits2 R Tw hR 7≤Tw))))

  2T≤P : 2 * Tw ≤ towerℕ (2 + m)
  2T≤P = ≤-trans (2T≤ m 3≤m) (towerℕ-mono (n≤1+n (suc m)))

  2T≤Z : 2 * Tw ≤ towerℕ (3 + m)
  2T≤Z = ≤-trans (2T≤ m 3≤m)
                 (towerℕ-mono (≤-trans (n≤1+n (suc m)) (n≤1+n (2 + m))))

  Tw≤TJ : Tw ≤ Tw * J
  Tw≤TJ = ≤-trans (≤-reflexive (sym (*-identityʳ Tw))) (*-monoʳ-≤ Tw 1≤J)

  -- the exponent both the size and the width axis land under
  expo : Tw * suc J ≤ towerℕ (3 + m)
  expo =
    ≤-trans (≤-reflexive (*-suc Tw J))
    (≤-trans (+-monoˡ-≤ (Tw * J) Tw≤TJ)
    (≤-trans (≤-reflexive (solve 2 (λ x y → x :* y :+ x :* y
                                             := (con 2 :* x) :* y) refl Tw J))
             (tower-mul (2 + m) (2 * Tw) J (≤-trans 3≤m (m≤n+m m 2)) 2T≤P J≤P)))

  -- and the STRICT form of it, which the width axis needs to report
  -- strictly (the next level's `sum-fits`-free width hypothesis)
  expo-suc : suc (Tw * suc J) ≤ towerℕ (3 + m)
  expo-suc =
    ≤-trans (s≤s (≤-trans (≤-reflexive (*-suc Tw J))
                  (≤-trans (+-monoˡ-≤ (Tw * J) Tw≤TJ)
                           (≤-reflexive (solve 2 (λ x y → x :* y :+ x :* y
                                                   := (con 2 :* x) :* y)
                                               refl Tw J)))))
            (tower-mul-suc (2 + m) (2 * Tw) J (≤-trans 3≤m (m≤n+m m 2)) 2T≤P J≤P)

  -- SIZE: (3T) per fold, J folds, one story to land the product
  sizeGoal : Caps.cSize (mBlow c) ≤ towerℕ (4 + m)
  sizeGoal =
    ≤-trans (iterSize-pow S Tw J S 1≤Tw hS hS)
    (≤-trans (*-monoʳ-≤ ((3 * Tw) ^ J) (m≤m+n Tw (Tw + (Tw + 0))))
    (≤-trans (≤-reflexive (*-comm ((3 * Tw) ^ J) (3 * Tw)))
    (≤-trans (^-monoˡ-≤ (suc J) (3T≤ m 3≤m))
    (≤-trans (≤-reflexive (^-*-assoc 2 Tw (suc J)))
             (^-monoʳ-≤ 2 expo)))))

  -- WIDTH: W · S^J ≤ T^(J+1), which is the same exponent the size axis
  -- lands under — so the width rides along at no extra story, and it
  -- reports STRICTLY, which is what feeds the next level's hypothesis
  widGoal : suc (Caps.cWid (mBlow c)) ≤ towerℕ (4 + m)
  widGoal =
    ≤-trans (s≤s (≤-trans (*-mono-≤ hW′ (^-monoˡ-≤ J hS))
                          (≤-trans (^-monoˡ-≤ (suc J) (<⇒≤ (n<2^n Tw)))
                                   (≤-reflexive (^-*-assoc 2 Tw (suc J))))))
    (≤-trans (+-monoˡ-≤ (2 ^ (Tw * suc J)) (1≤2^ (Tw * suc J)))
    (≤-trans (≤-reflexive (solve 1 (λ x → x :+ x := con 2 :* x)
                                 refl (2 ^ (Tw * suc J))))
             (^-monoʳ-≤ 2 expo-suc)))

  -- REGISTRATIONS: linear in the count, one story below the size, and
  -- reported strictly (this is the axis `sum-fits` consumes)
  regGoal : suc (Caps.cReg (mBlow c)) ≤ towerℕ (4 + m)
  regGoal =
    ≤-trans (s≤s (≤-trans (*-mono-≤ hR′ (≤-trans sucJS (*-monoʳ-≤ 2 JS≤Z)))
                          (≤-reflexive (solve 2 (λ x y → x :* (con 2 :* y)
                                                          := (con 2 :* x) :* y)
                                              refl Tw (towerℕ (3 + m))))))
            (tower-mul-suc (3 + m) (2 * Tw) (towerℕ (3 + m))
                           (≤-trans 3≤m (m≤n+m m 3)) 2T≤Z ≤-refl)
    where
    JS≤Z : J * S ≤ towerℕ (3 + m)
    JS≤Z = tower-mul (2 + m) J S (≤-trans 3≤m (m≤n+m m 2)) J≤P
             (≤-trans hS (≤-trans (towerℕ-mono (n≤1+n m))
                                  (towerℕ-mono (n≤1+n (suc m)))))
    1≤JS : 1 ≤ J * S
    1≤JS = *-mono-≤ 1≤J 1≤S
    sucJS : suc (J * S) ≤ 2 * (J * S)
    sucJS = ≤-trans (+-monoˡ-≤ (J * S) 1≤JS)
                    (≤-reflexive (solve 1 (λ y → y :+ y := con 2 :* y)
                                        refl (J * S)))

------------------------------------------------------------------
-- §3  THE BASE, WHICH IS WHERE THE MARGIN GOES.
--
-- capsAt's base cWid is `suc (pWᵉ n sl e ⊔ slotsPW n sl ⊔ slotsIW n sl)`
-- — a STATIC measure of the entry syntax.  Under the exponential engine
-- the base only had to be a Caps component; under the multiplicative
-- one capsAt-tower has to bound it, and the static width measure
-- TOWERS in the syntax: `innWᵉ (scanᵉ f z e)` is
-- `(pmIᵗ 0 f ⊔ 1) ^ (outWᵉ e) * …`, so a scanᵉ under a *All
-- exponentiates the width once per nesting level, ~7 syntax nodes
-- apiece.  That is not a defect of the measure — it is the deepScan
-- family, and it is why `foldStep` was exponential in the first place.
--
-- THE RATE IS TWO STORIES PER SYNTAX NODE (iterFold-tower≤ below), and
-- the width lemma Caps-Face already proves — outW/innW/dW of `e` under
-- `iterFold S (sizeᵉ e) M` — then puts the base cWid under
-- towerℕ (2·sz + 3).
--
-- AND THAT IS EXACTLY THE ROOT FUEL'S WHOLE MARGIN.  With base height
-- b, capsH e sl id = (b + σ) + σ·id, and caps-fuel-root needs
-- `3 + capsH e sl 1 ≤ (7 + sz) * 2`.  At σ = 4 and b = 3 + 2·sz that is
-- 14 + 2·sz ≤ 14 + 2·sz — an EQUALITY, no margin at all.  One more
-- story anywhere in the base and the root fuel is false at every
-- program size.
------------------------------------------------------------------

-- ONE exponential fold costs TWO tower stories, and that is tight:
-- S ^ suc w with both S and w at a level T needs T·(T+1) ≤ 2^T
foldStep-tower : ∀ (m S w : ℕ) → 3 ≤ m →
  S ≤ towerℕ m → w ≤ towerℕ m → foldStep S w ≤ towerℕ (2 + m)
foldStep-tower m S w 3≤m hS hw =
  ≤-trans (^-monoˡ-≤ (suc w) (≤-trans hS (<⇒≤ (n<2^n Tw))))
  (≤-trans (≤-reflexive (^-*-assoc 2 Tw (suc w)))
           (^-monoʳ-≤ 2 fits))
  where
  Tw = towerℕ m
  6≤Tw : 6 ≤ Tw
  6≤Tw = ≤-trans (≤ᵇ⇒≤ 6 16 _) (towerℕ-mono {3} {m} 3≤m)
  fits : Tw * suc w ≤ 2 ^ Tw
  fits = ≤-trans (*-monoʳ-≤ Tw (s≤s hw))
         (≤-trans (*-mono-≤ (m≤n+m Tw 2) (s≤s (m≤n+m Tw 1)))
                  (sq≤2^ Tw 6≤Tw))

-- so the static width lemma's count costs TWO stories per syntax node
iterFold-tower≤ : ∀ (k m S w : ℕ) → 3 ≤ m →
  S ≤ towerℕ m → w ≤ towerℕ m → iterFold S k w ≤ towerℕ (2 * k + m)
iterFold-tower≤ zero    m S w 3≤m hS hw = hw
iterFold-tower≤ (suc k) m S w 3≤m hS hw =
  subst (λ h → iterFold S k (foldStep S w) ≤ towerℕ h) shape
    (iterFold-tower≤ k (2 + m) S (foldStep S w)
       (≤-trans 3≤m (m≤n+m m 2))
       (≤-trans hS (towerℕ-mono (m≤n+m m 2)))
       (foldStep-tower m S w 3≤m hS hw))
  where
  shape : 2 * k + (2 + m) ≡ 2 * suc k + m
  shape = solve 2 (λ x y → con 2 :* x :+ (con 2 :+ y)
                             := con 2 :* (con 1 :+ x) :+ y) refl k m

-- THE ROOT MARGIN, at the base the static width forces.  This is an
-- EQUALITY, so the fit is exact: capsH e sl 1 = (3 + 2·sz + 4) + 4
base-2sz-fits : ∀ (sz : ℕ) → 3 + ((3 + 2 * sz + 4) + 4 * 1) ≤ (7 + sz) * 2
base-2sz-fits sz =
  ≤-reflexive (solve 1 (λ z → con 3 :+ ((con 3 :+ con 2 :* z :+ con 4)
                                          :+ con 4 :* con 1)
                                := (con 7 :+ z) :* con 2)
                     refl sz)

-- and ONE more story in the base fails, at the smallest program there
-- is (sz = 1, `emptyᵉ` over an empty telescope — Width-Count-Probe
-- computes that size) and at every size above it
_ : (3 + ((4 + 2 * 1 + 4) + 4 * 1) ≤ᵇ (7 + 1) * 2) ≡ false
_ = refl
_ : (3 + ((4 + 2 * 5 + 4) + 4 * 1) ≤ᵇ (7 + 5) * 2) ≡ false
_ = refl

-- the size axis's own base is unchanged and cheap: cSize₀ = 2 + sz and
-- cReg₀ = suc sz both sit under towerℕ (3 + sz) with room, so the
-- WIDTH axis is the only one that moves the base at all
_ : (2 + 5 ≤ᵇ towerℕ 3) ≡ true
_ = refl
_ : (suc 5 ≤ᵇ towerℕ 3) ≡ true
_ = refl

------------------------------------------------------------------
-- §4  THE MEASURED WIDTHS, AGAINST THE NEW STEP.
--
-- State-Blowup-Probe's rows, re-read as arithmetic (the Fold-Count
-- economy: compare numerals, do not re-run the evaluator).  Its
-- per-instant stored widths and sizes are
--
--     pA   wid 1 → 3 → 9 → 27      size 3 → 24 → 87 → 276
--     pD   wid 1 → 6 → 3072        size 3 → 24 → 45
--
-- Under the multiplicative step an instant that spends j folds buys
-- `W · S^j`, so the question each row asks is HOW MANY FOLDS the
-- instant has to have spent.  Two is enough for every measured row,
-- and the frames in question deliver more than two payloads.
------------------------------------------------------------------

-- pA: one fold each, at the entry size
_ : (3    ≤ᵇ 1 * 3 ^ 1)  ≡ true
_ = refl
_ : (9    ≤ᵇ 3 * 24 ^ 1) ≡ true
_ = refl
_ : (27   ≤ᵇ 9 * 87 ^ 1) ≡ true
_ = refl

-- pD, the deepening scan — the family the exponential step was built
-- for.  Its steepest measured instant (6 ↦ 3072) needs TWO folds
_ : (6    ≤ᵇ 1 * 24 ^ 1) ≡ true
_ = refl
_ : (3072 ≤ᵇ 6 * 45 ^ 1) ≡ false
_ = refl
_ : (3072 ≤ᵇ 6 * 45 ^ 2) ≡ true
_ = refl

-- and the count the new frameBlowup hands that instant is not two but
-- `D̂ · cSize · suc cWid` — at pD's own tight triple (cReg 1, cSize 45,
-- cWid 6) that is 4 · 45 · 7 = 1260 folds, i.e. 45 ^ 1260 of width
-- headroom against a measured factor of 512
_ : (2 ^ (2 ^ 1) * 45 * suc 6 ≡ 1260)
_ = refl
_ : (512 ≤ᵇ 45 ^ 1260) ≡ true
_ = refl

------------------------------------------------------------------
-- §5  AND THE CLAUSE THE RISK CLAUSE NAMED, MEASURED: NO
--     SYNTAX-COUNTED MULTIPLICATIVE WIDTH LEMMA EXISTS.
--
-- The engine swap is not just a change to `frameStep`.  Caps-Face's
-- width axis is the matching half: `wid-iterFold` bounds every width
-- measure of an expression by `iterFold S (sizeᵉ e) M` — ONE foldStep
-- per syntax node, seeded at the slot widths — and every receipt in the
-- eval cluster is a count of syntax nodes (`suc (sizeᵗ fn)`,
-- `suc (length vals * suc (sizeᵗ fn))`, `m + suc (m * m)`).  Under the
-- exponential step, `suc k` folds buy a TOWER of height k over the
-- seed, which is exactly what a static syntax bound needs.  Under the
-- multiplicative step the same receipt buys only `M * S ^ suc k`.
--
-- SO THE QUESTION IS WHETHER THE STATIC WIDTH IS EVER BIGGER THAN
-- `M * S ^ (a polynomial in the syntax)`.  It is, and not by a little:
-- the static measure TOWERS in the syntax, because
-- `innWᵉ (scanᵉ f z e)` has `outWᵉ e` IN AN EXPONENT and
-- `outWᵉ (mergeAllᵉ e)` multiplies that back into an outW.  Nest the
-- two and each level exponentiates the last.
--
-- THE FAMILY, four constructors wide: `lvl (suc k)` wraps `lvl k` in a
-- scan whose step function mentions the accumulator twice (so its plug
-- slope is 2) and unwraps it with a mergeAll.  Every level is a
-- LEGITIMATE closed program — this is Frame-Work-Probe's deepScan
-- shape, one nesting deeper.
--
-- The numbers are read off the measures themselves, and the top level's
-- width is NOT formed as a numeral (it is above 2 ^ 10485760):
-- `levelStep` is a structural lower bound on one level, and the
-- comparison against the multiplicative bound is done in the EXPONENT,
-- where every number is small.  That is the 457bb52 discipline — a
-- 2-tower is not a numeral — and it is load-bearing here: spelling the
-- top level as `lvl 3` rather than `wrap (lvl 2)` in the two conclusion
-- types below sends the conversion checker into normalising it, which
-- takes the container past 9 GB.
------------------------------------------------------------------

open import Data.List using (List; []; _∷_)
open import Data.Vec  using () renaming ([] to []ᵛ)
open import Data.List.Relation.Unary.Any using (here)
open import Rx.Exp using (Ctx; Closed; Tm; Fn; natᵗ; obs; _×ᵗ_;
                          ofᵉ; mergeAllᵉ; scanᵉ; strmᵗ; nat̂; fstᵗ; varᵗ;
                          sizeᵉ)
open import Rx.Evaluator using (Slots)
open import Rx.Frame-Width using (outWᵉ; innWᵉ; entryCeil)

Γ₀ : Ctx 0
Γ₀ = []ᵛ

ins₀ : Slots Γ₀
ins₀ ()

accV : ∀ {Θ} → Tm Γ₀ [] [] (obs natᵗ ×ᵗ natᵗ ∷ Θ) (obs natᵗ)
accV = fstᵗ (varᵗ (here refl))

seedO : ∀ {Θ} → Tm Γ₀ [] [] Θ (obs natᵗ)
seedO = strmᵗ (ofᵉ (nat̂ 7 ∷ []))

-- the doubling step: two occurrences of the accumulator, so the plug
-- slope `pmIᵗ 0` is 2 and the scanᵉ clause's base is 2
W2 : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
W2 = strmᵗ (mergeAllᵉ (ofᵉ (accV ∷ accV ∷ [])))

wrap : Closed Γ₀ natᵗ → Closed Γ₀ natᵗ
wrap e = mergeAllᵉ (scanᵉ W2 seedO e)

lvl : ℕ → Closed Γ₀ natᵗ
lvl zero    = ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ [])
lvl (suc k) = wrap (lvl k)

-- ONE LEVEL EXPONENTIATES, structurally — no numeral is formed
grow : ∀ (W P K : ℕ) → 1 ≤ W → 1 ≤ K → P ≤ W * (P * K)
grow W P K hW hK =
  ≤-trans (≤-trans (≤-reflexive (sym (*-identityʳ P))) (*-monoʳ-≤ P hK))
          (≤-trans (≤-reflexive (sym (*-identityˡ (P * K))))
                   (*-monoˡ-≤ (P * K) hW))

levelStep : ∀ (e : Closed Γ₀ natᵗ) → 1 ≤ outWᵉ 0 ins₀ e →
  2 ^ (outWᵉ 0 ins₀ e) ≤ outWᵉ 0 ins₀ (wrap e)
levelStep e h = grow _ _ _ h (s≤s z≤n)

-- THE MEASURED LEVELS.  outW doubles its way up: 2, 16, and then ten
-- MILLION at three nesting levels — and the fourth level is
-- 2 ^ 10485760, which is why it is bounded structurally rather than
-- computed
_ : outWᵉ 0 ins₀ (lvl 0) ≡ 2
_ = refl

_ : outWᵉ 0 ins₀ (lvl 1) ≡ 16
_ = refl

_ : outWᵉ 0 ins₀ (lvl 2) ≡ 10485760
_ = refl

-- and the syntax stays small: FORTY-SIX nodes for the whole thing
_ : sizeᵉ (lvl 3) ≡ 46
_ = refl

-- THE REFUTATION, STATED OVER AN ABSTRACT CHILD and instantiated at
-- the measured one — which is not a stylistic choice: instantiating it
-- with the top level SPELLED OUT would ask Agda to normalise
-- 2 ^ 10485760, and a 2-tower is not a numeral (457bb52).  Everything
-- below happens in the EXPONENT, where every number is small.
--
-- Read it as: for a program `wrap e` whose syntax is at most 62 nodes
-- (so its tightest entry cSize is under 2 ^ 6), a multiplicative bound
-- at ANY count k with 6·k below the child's width is EXCEEDED
refute : ∀ (e : Closed Γ₀ natᵗ) (k : ℕ) →
  1 ≤ outWᵉ 0 ins₀ e →
  2 + sizeᵉ (wrap e) ≤ 2 ^ 6 →
  suc (6 * k) ≤ outWᵉ 0 ins₀ e →
  suc ((2 + sizeᵉ (wrap e)) ^ k) ≤ outWᵉ 0 ins₀ (wrap e)
refute e k h1 hsz hk =
  ≤-trans (s≤s (≤-trans (^-monoˡ-≤ k hsz)
                        (≤-reflexive (^-*-assoc 2 6 k))))
  (≤-trans (+-monoˡ-≤ (2 ^ (6 * k)) (1≤2^ (6 * k)))
  (≤-trans (≤-reflexive (solve 1 (λ x → x :+ x := con 2 :* x)
                               refl (2 ^ (6 * k))))
  (≤-trans (^-monoʳ-≤ 2 hk) (levelStep e h1))))

-- LINEAR IN THE SYNTAX — the count every eval receipt actually reports.
-- 48 ^ 46 against a width of 2 ^ 10485760
mult-bound-fails-linear :
  suc ((2 + sizeᵉ (wrap (lvl 2))) ^ 46) ≤ outWᵉ 0 ins₀ (wrap (lvl 2))
mult-bound-fails-linear =
  refute (lvl 2) 46 (≤ᵇ⇒≤ 1 10485760 _) (≤ᵇ⇒≤ 48 64 _) (≤ᵇ⇒≤ 277 10485760 _)

-- AND CUBIC IN IT, so the gap is not a constant factor or a slack
-- receipt: 6 · 46³ = 584016, still far under the exponent
mult-bound-fails-cubic :
  suc ((2 + sizeᵉ (wrap (lvl 2))) ^ (46 * 46 * 46)) ≤ outWᵉ 0 ins₀ (wrap (lvl 2))
mult-bound-fails-cubic =
  refute (lvl 2) (46 * 46 * 46)
         (≤ᵇ⇒≤ 1 10485760 _) (≤ᵇ⇒≤ 48 64 _) (≤ᵇ⇒≤ 584017 10485760 _)

-- WHAT THIS DOES AND DOES NOT SAY.  It does NOT refute the engine: the
-- entry caps' own cWid is `suc (pWᵉ n sl e ⊔ …)`, which for THIS
-- program already IS the tower — the base pays for the program's own
-- static widths, at j = 0.  What it refutes is the width lemma AS
-- STATED AND CONSUMED: `wid-iterFold`'s seed is the SLOT telescope's
-- width and its count is the syntax, and the five eval receipts are
-- counts of syntax nodes.  Those receipts buy a tower under the
-- exponential step and 2 ^ (6 · count) under the multiplicative one,
-- and the gap between them is this row.
--
-- So the ruling's restructure is not optional, it is the whole job: the
-- static widths must be paid by an ENTRY CEILING carried in the base
-- (a ⊔-collect over every subterm of all five measures — syntax, hence
-- entry-computable), and the receipts may then pay only for the
-- DYNAMIC growth, which is per-payload and multiplicative.  The
-- dynamic side is where the engine is right: one fold through a scan
-- whose source carries W payloads takes a width to ~2 ^ W, and that
-- frame's receipt is `length vals * suc (sizeᵗ fn)` ≈ W · size folds,
-- which buys S ^ (W · size) ≥ 2 ^ W.  Exponent and receipt count are
-- the same number (§1) — on the DELIVERY side only

------------------------------------------------------------------
-- §6  THE ENTRY CEILING, ON THE FAMILY THAT REFUTED THE RECEIPT.
--
-- §5's refutation is what forces the base to carry a CEILING rather
-- than the program's own width: the static measure towers in the
-- syntax, and no syntax-counted receipt buys a tower.  The ceiling
-- (Rx.Frame-Width.entryCeil) is the ⊔-collect of all five measures
-- over every SUBTERM — so the question §3's accounting has to survive
-- is whether collecting subterms costs STORIES over collecting the
-- root alone.
--
-- IT DOES NOT, and the measure says so directly: on this family the
-- ceiling is the root's own width at the first two levels and exactly
-- TWICE it at the third.  A factor of two is not a story — the base
-- height is still `3 + 2 * sz`, and `budgetAt`'s (7 + sz)(id + 2)
-- does not move.
------------------------------------------------------------------

_ : outWᵉ 0 ins₀ (lvl 0) ≡ 2
_ = refl

_ : entryCeil 0 ins₀ (lvl 0) ≡ 2
_ = refl

_ : entryCeil 0 ins₀ (lvl 1) ≡ 16
_ = refl

_ : sizeᵉ (lvl 2) ≡ 32
_ = refl

_ : entryCeil 0 ins₀ (lvl 2) ≡ 20971520
_ = refl

-- 20971520 sits under towerℕ 3 = 2 ^ 65536, i.e. THREE stories against
-- the 3 + 2 * 32 = 67 the base is allowed on a program of this size
_ : 3 + 2 * 32 ≡ 67
_ = refl

_ : (3 ≤ᵇ 67) ≡ true
_ = refl
