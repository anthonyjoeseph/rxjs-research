-- ══════════════════════════════════════════════════════════════════
-- THE NESTING CURRENCY CANNOT SIT UNDER THE CAPS HEIGHT, so the one
-- arithmetic obligation the whole nesting cap rests on is FALSE, and
-- the postulate holding it up is false with it.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE`
-- notes.
--
-- WHAT THE ROUTE SAID.  The nesting cap was designed to grow by ONE
-- EXPONENTIAL per instant off program-shaped bases, while the caps
-- height gains `blowH`'s pooled summand -- a tower -- per instant, so
-- the sum of three nesting caps would sit under the height with stories
-- to spare.  That reading is recorded in the currency's own header and
-- it was true of the currency it was written for.
--
-- WHERE IT BREAKS, AND IT IS THE RE-DENOMINATION AND NOT THE
-- ARITHMETIC.  The width stopped being an invention of the nesting
-- module and became the REGISTRY CAP, which is a field of the caps
-- recurrence; the per-instant factor now reads `delSq` of the caps at
-- the instant AFTER the one being bounded.  So the cap no longer reads
-- program-shaped quantities: it exponentiates a caps field, and the
-- caps field at that instant is built by iterating the size step
-- `sizeCount c d` times AT THE DEPTH FUEL `d = capsH`.  That count is
-- inflationary IN ITS DEPTH -- `fLvlD` at depth `suc d` runs a whole
-- nested iteration whose innermost call is `fLvlD` at depth `d` -- so
-- the height is inside the count, the count is inside the size, and the
-- size is inside an exponent.  One instant's cap therefore exceeds
-- `2 ^ capsH`, and it was asked to be at most `capsH`.
--
-- WHAT THIS DOES NOT SHOW.  It says nothing against the nesting
-- invariant itself, and nothing against the caps recurrence.  It kills
-- the CALIBRATION: a cap that reads the SUCCESSOR instant's caps field
-- cannot be bounded by the height that instant's own step was fuelled
-- by, because part THREE puts the fuel under that field for every
-- fuel.
--
-- AND THE TOWER ESCAPE IS CLOSED TOO, which is why part THREE is
-- stated over an arbitrary fuel rather than over `capsH`.  Restating
-- the obligation against a bigger height does not help: whatever the
-- height is, the exit cap's size field is at least it, so the currency
-- is at least it, and the two grow together rather than apart.  The
-- repair has to break the READ, and part FIVE says how completely --
-- not one summand of the currency may read `capsAt` at the successor
-- instant, the increment's unit term included, so re-denominating the
-- factor alone leaves the obligation refuted.
--
-- AND THE ARITHMETIC BELOW IS NOT ABOUT THE PROGRAM.  No conjunct reads
-- the witness beyond needing one closed program to exist, because the
-- gap is between two definitions and not at any instantiation; the
-- concrete program is there so the statement is not vacuously
-- quantified over an empty type.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Nest-Cap-Height where

open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using
  (≤-refl; ≤-trans; ≤-reflexive; +-comm; +-suc; +-monoˡ-≤; +-monoʳ-≤; m≤m+n; m≤n+m; n≤1+n;
   1+n≰n; *-monoˡ-≤; *-monoʳ-≤; *-identityˡ; *-identityʳ; ^-monoʳ-≤)
open import Data.Product using (Σ; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (sym; subst)

open import Rx.Exp using (Ctx; Closed; natᵗ)
open import Rx.Prim using (towerℕ)
open import Rx.Slots using (Slots)
open import Rx.Evaluator using
  (fLvl; fCharge; widAt; sizeAt; iterSize; sizeStep; fLvlD; sLvlD; opIterD; fLvlD-0; fLvlD-suc;
  sIterD-suc; sLvlD-suc; opIterD-suc; fIterD-suc; dLvl; lvls)
open import Verify-Budget-Sufficient.Measures using (n<2^n)
open import Verify-Budget-Sufficient.Caps using
  (Caps; capsAt; capsH; frameStep; frameBlowup; sizeCount; sizeCount-body; cDel; cDel-body;
   1≤dCapᶜ; 2≤capsAt-size; 1≤capsAt-reg; tower-le-blowH;
   sIterD-infl; sLvlD-infl; opIterD-infl; fIterD-infl; iterL-infl)
open import Verify-Budget-Sufficient.Fan-Caps using (delSize; delSq; cSize≤delSq)
open import Verify-Budget-Sufficient.Nest-Cap using (nestU; nestU-room)
open import Verify-Budget-Sufficient.Nest-Store using
  (nestCapAt; nestCapAt-suc; nestFacAt; nestFacAt-def; 1≤nestFacAt; nestIncAt;
   nestIncAt-def; nestUnit; size≤nestIncAt; realWidAt; realWidAt-def;
   nestBurstAt; 1≤nestBurstAt; capsHpred; capsH-blow; 1≤capsHpred)
open import Verify-Budget-Sufficient.Demand-Programs using (Γ₀; ins₀; progD)

----------------------------------------------------------------------
-- ONE.  THE DEPTH FUEL IS INSIDE THE LEVEL.  `fLvlD` at depth `suc d`
-- opens a chain that reaches `fLvlD` at depth `d` on an argument
-- strictly above the one it started at, so each unit of depth buys at
-- least one unit of level.  Every step is an exported clause equation
-- or an exported inflation, because the whole family is sealed.
----------------------------------------------------------------------

fLvlD-depth : ∀ (S W d J : ℕ) → d + J ≤ fLvlD S W d J
fLvlD-depth S W zero J =
  ≤-trans (≤-trans (m≤m+n J (fCharge S W J))
                   (m≤m+n (fLvl S W J) (suc (widAt S W J))))
          (≤-reflexive (sym (fLvlD-0 S W J)))
fLvlD-depth S W (suc d) J =
  ≤-trans step
  (≤-trans (fLvlD-depth S W d J₂)
  (≤-trans (fIterD-infl S W d k₀ w₂ (fLvlD S W d J₂))
  (≤-trans (≤-reflexive (sym (fIterD-suc S W d k₀ w₂ J₂)))
  (≤-trans (≤-reflexive (sym (opIterD-suc S W d k₀ m′ Y)))
  (≤-trans (≤-reflexive (sym (sLvlD-suc S W d k₀ Y)))
  (≤-trans (sIterD-infl S W d K m₀ (sLvlD S W d K Y))
  (≤-trans (≤-reflexive (sym (sIterD-suc S W d K m₀ X)))
           (≤-reflexive (sym (fLvlD-suc S W d J))))))))))
  where
  X  = fLvl S W J
  k₀ = sizeAt S (suc J)
  K  = suc k₀
  m₀ = widAt S W J
  Y  = suc X
  m′ = sizeAt S Y
  J₀ = suc (Y + suc m′ * suc m′)
  J₂ = opIterD S W d k₀ m′ (sLvlD S W d k₀ J₀)
  w₂ = widAt S W J₂

  sucJ≤J₂ : suc J ≤ J₂
  sucJ≤J₂ =
    ≤-trans (s≤s (m≤m+n J (fCharge S W J)))
    (≤-trans (≤-trans (m≤m+n Y (suc m′ * suc m′)) (n≤1+n (Y + suc m′ * suc m′)))
             (≤-trans (sLvlD-infl S W d k₀ J₀)
                      (opIterD-infl S W d k₀ m′ (sLvlD S W d k₀ J₀))))

  step : suc d + J ≤ d + J₂
  step = ≤-trans (≤-reflexive (sym (+-suc d J))) (+-monoʳ-≤ d sucJ≤J₂)

d≤dLvl : ∀ (S W d J : ℕ) → d ≤ dLvl S W d J
d≤dLvl S W d J =
  ≤-trans (≤-trans (m≤m+n d J) (fLvlD-depth S W d J))
          (iterL-infl S W d (sizeAt S J) (fLvlD S W d J))

d≤lvls : ∀ (S W d J n : ℕ) → 1 ≤ n → d ≤ lvls S W d J n
d≤lvls S W d J zero    ()
d≤lvls S W d J (suc n) _  = d≤dLvl S W d (lvls S W d J n)

d≤sizeCount : ∀ (c : Caps) (d : ℕ) → 1 ≤ Caps.cReg c → d ≤ sizeCount c d
d≤sizeCount c d 1≤R =
  ≤-trans (d≤lvls (Caps.cSize c) (Caps.cWid c) d 0 (cDel c d) 1≤D)
          (≤-reflexive (sym (sizeCount-body c d)))
  where
  1≤D : 1 ≤ cDel c d
  1≤D = ≤-trans (1≤dCapᶜ (Caps.cSize c) (Caps.cWid c) (Caps.cReg c) d
                         (Caps.cSize c) 0 1≤R)
                (≤-reflexive (sym (cDel-body c d)))

----------------------------------------------------------------------
-- TWO.  THE COUNT IS INSIDE THE SIZE.  One size step adds at least one,
-- so iterating it `k` times from `s` lands at least at `k + s`.
----------------------------------------------------------------------

suc≤sizeStep : ∀ (S s : ℕ) → 1 ≤ S → suc s ≤ sizeStep S s
suc≤sizeStep S s 1≤S =
  ≤-trans (s≤s (m≤m+n s (1 * s)))
          (≤-trans (≤-reflexive (sym (*-identityˡ (suc (2 * s)))))
                   (*-monoˡ-≤ (suc (2 * s)) 1≤S))

add≤iterSize : ∀ (S : ℕ) → 1 ≤ S → ∀ (k s : ℕ) → k + s ≤ iterSize S k s
add≤iterSize S 1≤S zero    s = ≤-refl
add≤iterSize S 1≤S (suc k) s =
  ≤-trans (≤-trans (≤-reflexive (sym (+-suc k s)))
                   (+-monoʳ-≤ k (suc≤sizeStep S s 1≤S)))
          (add≤iterSize S 1≤S k (sizeStep S s))

----------------------------------------------------------------------
-- THREE.  THE FUEL IS INSIDE ITS OWN BLOWUP, FOR EVERY FUEL -- and
-- stating it in the fuel rather than in `capsH` is the point.  It says
-- the gap below is not a miscalibration of the height sequence that a
-- different one would close: whatever depth budget the caps recurrence
-- is driven by, the size it produces already dominates that budget, so
-- a cap read off that size can never be paid for out of it.  The
-- instant's own reading is the specialisation directly beneath.
----------------------------------------------------------------------

fuel≤blowup : ∀ (c : Caps) (F : ℕ) →
  1 ≤ Caps.cReg c → 1 ≤ Caps.cSize c →
  F ≤ Caps.cSize (frameBlowup c F)
fuel≤blowup c F 1≤R 1≤S =
  ≤-trans (≤-trans (d≤sizeCount c F 1≤R) (m≤m+n J S))
          (add≤iterSize S 1≤S J S)
  where
  S = Caps.cSize c
  J = sizeCount c F

-- AND THE RECURRENCE'S OWN LEVEL COUNT IS ALREADY PAST THE FUEL, which
-- is what closes the widening the caps face performs on a walk's
-- report.  The count the recurrence steps by at instant `id` is
-- `sizeCount` of the entry cap at fuel `capsH e sl id`, and part ONE
-- puts the fuel under it, so a quantity charging one unit per level of
-- THAT count exceeds the height whatever it is keyed on.
--
-- AND THE SCOPE IS EXACTLY THAT COUNT, NOT EVERY PER-LEVEL CHARGE.  A
-- descent's own flattening is keyed on the PATH, whose length the entry
-- cap bounds by an invariant conjunct, and that is a much smaller
-- quantity than the recurrence's worst case -- so a currency flattened
-- at the entry cap's size is not caught here.  What is caught is the
-- step that replaces a walk's reported level by the recurrence's
-- maximum in order to state the bound as a function of the instant.
capsH≤levels : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  capsH e sl id ≤ sizeCount (capsAt e sl id) (capsH e sl id)
capsH≤levels e sl id =
  d≤sizeCount (capsAt e sl id) (capsH e sl id) (1≤capsAt-reg e sl id)

capsH≤size : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  capsH e sl id ≤ Caps.cSize (capsAt e sl (suc id))
capsH≤size e sl id =
  fuel≤blowup (capsAt e sl id) (capsH e sl id)
    (1≤capsAt-reg e sl id)
    (≤-trans (s≤s z≤n) (2≤capsAt-size e sl id))

----------------------------------------------------------------------
-- FOUR.  THE SIZE FIELD IS INSIDE THE NESTING FACTOR'S EXPONENT, and
-- `n < 2 ^ n` is the whole of the crossing.
----------------------------------------------------------------------

size<fac : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  suc (Caps.cSize (capsAt e sl (suc id))) ≤ nestFacAt e sl id
size<fac {n = n} e sl id =
  ≤-trans (s≤s (cSize≤delSq n (capsAt e sl (suc id)) 1≤S′))
  (≤-trans (n<2^n Q)
  (≤-trans (^-monoʳ-≤ 2 Q≤E)
           (≤-reflexive (sym (nestFacAt-def e sl id)))))
  where
  b  = nestBurstAt e sl id
  D  = delSize n (capsAt e sl (suc id))
  R  = realWidAt e sl id
  Q  = delSq n (capsAt e sl (suc id))
  1≤S′ : 1 ≤ Caps.cSize (capsAt e sl (suc id))
  1≤S′ = ≤-trans (s≤s z≤n) (2≤capsAt-size e sl (suc id))
  1≤R : 1 ≤ R
  1≤R = subst (1 ≤_) (sym (realWidAt-def e sl id)) (1≤capsAt-reg e sl id)
  1≤sD : 1 ≤ suc D
  1≤sD = s≤s z≤n
  1≤bb : 1 ≤ suc b * suc b
  1≤bb = s≤s z≤n
  s1 : Q ≤ R * Q
  s1 = ≤-trans (≤-reflexive (sym (*-identityˡ Q))) (*-monoˡ-≤ Q 1≤R)
  s2 : R * Q ≤ suc D * (R * Q)
  s2 = ≤-trans (≤-reflexive (sym (*-identityˡ (R * Q))))
               (*-monoˡ-≤ (R * Q) 1≤sD)
  s3 : suc D * (R * Q) ≤ suc b * suc b * (suc D * (R * Q))
  s3 = ≤-trans (≤-reflexive (sym (*-identityˡ (suc D * (R * Q)))))
               (*-monoˡ-≤ (suc D * (R * Q)) 1≤bb)
  Q≤E : Q ≤ suc b * suc b * (suc D * (R * Q))
  Q≤E = ≤-trans s1 (≤-trans s2 s3)

fac≤cap : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  nestFacAt e sl id ≤ nestCapAt e sl (suc id)
fac≤cap e sl id =
  ≤-trans (≤-trans (≤-reflexive (sym (*-identityʳ (nestFacAt e sl id))))
                   (*-monoʳ-≤ (nestFacAt e sl id) 1≤rest))
          (≤-reflexive (sym (nestCapAt-suc e sl id)))
  where
  1≤rest : 1 ≤ nestCapAt e sl id + nestIncAt e sl id
  1≤rest = ≤-trans (≤-trans (s≤s z≤n)
                            (≤-trans (2≤capsAt-size e sl id)
                                     (size≤nestIncAt e sl id)))
                   (m≤n+m (nestIncAt e sl id) (nestCapAt e sl id))

----------------------------------------------------------------------
-- FIVE.  THE INCREMENT ALONE ALREADY CROSSES, WITHOUT THE FACTOR --
-- which is what narrows the repair from "re-denominate the factor" to
-- "no summand of the currency may read the cap at the instant AFTER
-- the one it prices".  The increment's unit term is `nestU` at the
-- delivery square of the exit cap, and `nestU` is `suc` of its key
-- times a unit that is a successor by construction, so the exit cap's
-- own size field sits STRICTLY under one summand of the increment
-- before any exponent is reached.  Part THREE puts the fuel under that
-- size field, so the increment exceeds the fuel it is priced against.
----------------------------------------------------------------------

capsH<inc : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  suc (capsH e sl id) ≤ nestIncAt e sl id
capsH<inc {n = n} e sl id =
  ≤-trans (s≤s (≤-trans (capsH≤size e sl id)
                        (cSize≤delSq n (capsAt e sl (suc id)) 1≤S′)))
  (≤-trans sQ≤nu (≤-trans nu≤mid (≤-trans mid≤b b≤r)))
  where
  Q = delSq n (capsAt e sl (suc id))
  U = nestUnit e sl
  R = realWidAt e sl id
  b = nestBurstAt e sl id
  D = delSize n (capsAt e sl id)

  1≤S′ : 1 ≤ Caps.cSize (capsAt e sl (suc id))
  1≤S′ = ≤-trans (s≤s z≤n) (2≤capsAt-size e sl (suc id))

  1≤U : 1 ≤ U
  1≤U = s≤s z≤n

  1≤R : 1 ≤ R
  1≤R = subst (1 ≤_) (sym (realWidAt-def e sl id)) (1≤capsAt-reg e sl id)

  sQ≤nu : suc Q ≤ nestU Q U
  sQ≤nu = ≤-trans (+-monoˡ-≤ Q 1≤U) (nestU-room Q U Q 1≤U ≤-refl)

  1≤mid : 1 ≤ suc (suc (R * D))
  1≤mid = s≤s z≤n

  nu≤mid : nestU Q U ≤ suc (suc (R * D)) * nestU Q U
  nu≤mid = ≤-trans (≤-reflexive (sym (*-identityˡ (nestU Q U))))
                   (*-monoˡ-≤ (nestU Q U) 1≤mid)

  mid≤b : suc (suc (R * D)) * nestU Q U
            ≤ b * (suc (suc (R * D)) * nestU Q U)
  mid≤b = ≤-trans (≤-reflexive (sym (*-identityˡ (suc (suc (R * D)) * nestU Q U))))
                  (*-monoˡ-≤ (suc (suc (R * D)) * nestU Q U)
                             (1≤nestBurstAt e sl id))

  b≤r : b * (suc (suc (R * D)) * nestU Q U) ≤ nestIncAt e sl id
  b≤r =
    ≤-trans (≤-trans (≤-reflexive
                       (sym (*-identityˡ (b * (suc (suc (R * D)) * nestU Q U)))))
                     (*-monoˡ-≤ (b * (suc (suc (R * D)) * nestU Q U)) 1≤R))
            (≤-reflexive (sym (nestIncAt-def e sl id)))

inc≤cap : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  nestIncAt e sl id ≤ nestCapAt e sl (suc id)
inc≤cap e sl id =
  ≤-trans (≤-trans (m≤n+m (nestIncAt e sl id) (nestCapAt e sl id))
                   (≤-trans (≤-reflexive
                              (sym (*-identityˡ (nestCapAt e sl id
                                                   + nestIncAt e sl id))))
                            (*-monoˡ-≤ (nestCapAt e sl id + nestIncAt e sl id)
                                       (1≤nestFacAt e sl id))))
          (≤-reflexive (sym (nestCapAt-suc e sl id)))

----------------------------------------------------------------------
-- SIX.  AND THE LEVEL KEY IS IN THE DEAD ZONE TOO, at every level at
-- or above the fuel -- which is what closes the repair that keys the
-- currency at the level a walk REACHED rather than at the
-- recurrence's maximum.  One frame of the size recurrence adds at
-- least its own entry size, so the size field at level `j` is at
-- least `j`, and the fuel is the thing the height is priced in.  Part
-- THREE puts the recurrence's own count at or above the fuel, so the
-- exit cap is one instance of this and not a separate fact.
--
-- WHAT THIS DOES NOT CLOSE, and it is the whole of what survives: a
-- walk that halts STRICTLY BELOW the fuel.  That escape is refused on
-- the walk face rather than here, by a reset-anchor pin recording
-- that a level cap cannot ceiling a walk which climbs past the level
-- it is keyed at -- prose, and so outside this file's guarantee.
----------------------------------------------------------------------

level-step : ∀ (c : Caps) (j : ℕ) → 1 ≤ Caps.cSize c →
  j + Caps.cSize c ≤ Caps.cSize (frameStep j c)
level-step c j 1≤S = add≤iterSize (Caps.cSize c) 1≤S j (Caps.cSize c)

level-crosses : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id j : ℕ) → capsH e sl id ≤ j →
  suc (capsH e sl id) ≤ Caps.cSize (frameStep j (capsAt e sl id))
level-crosses e sl id j hj =
  ≤-trans (s≤s hj)
  (≤-trans (≤-trans (≤-reflexive (+-comm 1 j)) (+-monoʳ-≤ j 1≤S))
           (level-step (capsAt e sl id) j 1≤S))
  where
  1≤S : 1 ≤ Caps.cSize (capsAt e sl id)
  1≤S = ≤-trans (s≤s z≤n) (2≤capsAt-size e sl id)

----------------------------------------------------------------------
-- THE STATEMENT, AND ITS REFUTATION.  `NestCapCapsH` is the arithmetic
-- obligation the nesting cap rests on, verbatim.
----------------------------------------------------------------------

NestCapCapsH : Set
NestCapCapsH = ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  2 * nestCapAt e sl id + nestCapAt e sl (suc id) ≤ capsH e sl id

nestCap-3≤capsH-absurd : NestCapCapsH → ⊥
nestCap-3≤capsH-absurd pr =
  1+n≰n (≤-trans (s≤s (capsH≤size e sl 0))
        (≤-trans (size<fac e sl 0)
        (≤-trans (fac≤cap e sl 0)
        (≤-trans (m≤n+m (nestCapAt e sl 1) (2 * nestCapAt e sl 0))
                 (pr e sl 0)))))
  where
  e : Closed Γ₀ natᵗ
  e = progD 0 0
  sl : Slots Γ₀
  sl = ins₀

-- AND THE SAME OBLIGATION DIES A SECOND, SHORTER DEATH, one that no
-- change to the FACTOR can repair.  This replay never reaches
-- `nestFacAt`'s exponent: it walks the fuel into the exit cap's size
-- field, the size field into the increment's unit summand, and the
-- increment into the cap.  So a repair that re-denominates only the
-- factor leaves the obligation refuted, and the constraint the repair
-- has to satisfy is that NO summand of the currency reads `capsAt` at
-- the successor instant.
nestCap-3≤capsH-absurd-inc : NestCapCapsH → ⊥
nestCap-3≤capsH-absurd-inc pr =
  1+n≰n (≤-trans (capsH<inc e sl 0)
        (≤-trans (inc≤cap e sl 0)
        (≤-trans (m≤n+m (nestCapAt e sl 1) (2 * nestCapAt e sl 0))
                 (pr e sl 0))))
  where
  e : Closed Γ₀ natᵗ
  e = progD 0 0
  sl : Slots Γ₀
  sl = ins₀

-- AND THE LEVEL-KEYED FORM DIES WITH THEM.  `NestLevelKeyed` is the
-- repair stated as its own obligation: price the currency at the cap
-- a walk's own level reaches, and ask that cap to stay under the fuel
-- the height is denominated in.  It fails at every level the fuel
-- itself reaches, so the surviving form of the repair is not "key it
-- lower" but "stop denominating the height in this fuel".
NestLevelKeyed : Set
NestLevelKeyed = ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id j : ℕ) → capsH e sl id ≤ j →
  Caps.cSize (frameStep j (capsAt e sl id)) ≤ capsH e sl id

nestCap-level-absurd : NestLevelKeyed → ⊥
nestCap-level-absurd pr =
  1+n≰n (≤-trans (level-crosses e sl 0 (capsH e sl 0) ≤-refl)
                 (pr e sl 0 (capsH e sl 0) ≤-refl))
  where
  e : Closed Γ₀ natᵗ
  e = progD 0 0
  sl : Slots Γ₀
  sl = ins₀

----------------------------------------------------------------------
-- AND THE POSTULATE ITSELF.  `nest-height` is the sole support of the
-- obligation above -- the composition is `tower-le-blowH` at the height
-- the Σ hands back -- so refuting the obligation refutes the postulate,
-- and the replay below says so in code rather than in prose.
----------------------------------------------------------------------

NestHeight : Set
NestHeight = ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  Σ ℕ λ h →
    (2 * nestCapAt e sl id + nestCapAt e sl (suc id) ≤ towerℕ h)
    × (suc h ≤ towerℕ (capsHpred e sl id))

nest-height-absurd : NestHeight → ⊥
nest-height-absurd nh = nestCap-3≤capsH-absurd replay
  where
  replay : NestCapCapsH
  replay e sl id =
    ≤-trans (proj₁ (proj₂ (nh e sl id)))
            (subst (towerℕ (proj₁ (nh e sl id)) ≤_) (sym (capsH-blow e sl id))
               (tower-le-blowH (proj₁ (nh e sl id)) (capsHpred e sl id)
                               (1≤capsHpred e sl id)
                               (proj₂ (proj₂ (nh e sl id)))))
