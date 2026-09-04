-- THE CAPS ARITHMETIC THE ROUND'S CEILING STANDS ON, and nothing that
-- reads a run.  Every statement here is about numbers the caps
-- recurrence produces -- the cap, the increment, the selection factor,
-- the walk's charge -- and the fuel they have to fit under.  They were
-- one shelf inside the cascade face and they are hoisted because a
-- module is an indivisible checking unit: none of them is in a cycle
-- with the walk, so leaving them there made every check of the walk
-- re-prove the whole shelf.
module Verify-Budget-Sufficient.Caps-Face.Nest-Arith where

open import Data.Nat     using (ℕ; zero; suc; _+_; _*_; _^_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (<⇒≤; *-identityˡ; ^-distribˡ-+-*; ≤ᵇ⇒≤; ^-monoʳ-≤; ^-monoˡ-≤; *-monoˡ-≤; ≤-trans; ≤-refl;
  ≤-reflexive; m≤m+n; m≤n+m; n≤1+n; *-identityʳ; *-mono-≤; *-monoʳ-≤; +-monoʳ-≤; +-monoˡ-≤;
  +-mono-≤; *-distribʳ-+; *-distribˡ-+; ^-*-assoc; *-comm; +-comm; ≤-pred; m^n>0; m≤n*m;
  *-assoc; *-cancelˡ-≤)
open import Data.Nat.Solver     using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.Fin     using (Fin)
import Data.Fin as Fin
open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []ᵃ; _∷_ to _∷ᵃ_; map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties
  using (concat⁺; tabulate⁺)
  renaming (++⁺ to all-++; ++⁻ˡ to all-++ˡ; ++⁻ʳ to all-++ʳ)
open import Data.Vec     using (Vec; lookup) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Unit    using (tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst; cong)

open import Rx.Prim      using (_at_from_as_)
open import Rx.Exp       using (Ctx; Closed; sizeᵉ; syncSizeᵉ)
open import Rx.Evaluator using (iterSize; root)
open import Rx.Frame-Width using (entryCeil)
open import Rx.Slot-Clos using (slotsClos)
open import Verify-Budget-Sufficient.Nest-Cap using (nestU; nestU-def; nestB; nestB≤pow)
open import Verify-Budget-Sufficient.Nest-Depth-Size using (nestDᵉ≤sizeᵉ)
open import Rx.Nest-Depth using (nestDᵉ)
open import Verify-Budget-Sufficient.Fan-Caps using
  (delSize; delSq; delSq-def; delSize-exp)
open import Verify-Budget-Sufficient.Nest-Store using
  (nestCapAt; nestFacAt; nestFacAt-def; realWidAt; realWidAt-def; nestIncAt;
  nestIncAt-def; nestBurstAt; nestUnit; slotsNestSum; nestCapAt-0; nestCap-mono₀; slotNest;
  nestBurstAt-def; nestCapAt-suc; slotWrap; slotWrapSum; fitG; slotWrapB; slotWrapBSum)
open import Rx.Slots using (Slot; Slots; scripted; shared; slotSize; slotsSize)

-- .Delivery-Walk re-exports BOTH prerequisites of the cascade
-- conjuncts and adds the walk itself:
--
--   · .Caps holds the recurrence (Caps / frameStep / frameBlowup /
--     capsAt and their supply lemmas) and re-exports .Keeps-Ring, hence
--     .Measures.  Extracted so that a grind here no longer
--     re-checks .Wet — see that module's head.
--   · .Deliveries is the ledger stratum: where EvalSt.delivered moves
--     and where it provably does not, plus delivN and its composition
--     laws.  delivN is the currency the cascade conjuncts are stated in.
--   · .Delivery-Walk maps the delivery clique onto the LEVEL walk —
--     foldPath ↦ dCapᶜ, dispatchShare ↦ dCapᶜ, shareGo ↦ dWalkᶜ,
--     cascadeGo ↦ dWalkᶜ — RELATIVE to one frame's face at the level it
--     RUNS at, which it takes as a record of hypotheses rather than
--     postulating.  `walkH` below instantiates that record and
--     `cascadeGo-deliveries` is the theorem it buys.
open import Verify-Budget-Sufficient.Caps using
  (1≤capsAt-reg; 1≤pow≤; 2≤capsAt-size; 8≤capsAt-size; 21≤capsAt-size; B2-cReg≤cSize;
  Caps; capsAt;
  capsAt-base-size; capsAt-size-mono; capsH; capsAt-exp-gain; size≤sizeCount;
  sizeCount; frameBlowup; iterSize-pow; size-lower; capsAt-exp2≤capsH)
open import Verify-Budget-Sufficient.Measures using
  (n<2^n; sq≤2^; sum-tab-mono; sum-tab-const; fᵢ≤sum-tab; n≤slotsSize;
   syncSize≤sizeᵉ; 2X≡X+X; 1≤pow)
-- the nesting measure the subscribe budget descends on, and the frame
-- row that supplies it.  Re-exported, so the clique names one module
-- the depth mirror: `depthInner` is the fuel `thruOuter-face-core`'s
-- new hypothesis ranges over.  The rest of the family
-- carries THE DEPTH PREMISE down the frame chain, and it threads by
-- IDENTITY because the mirror is definitionally equal at every hop:
--   depthFrame … (from-inner op allNid inst) … fin = depthReact … fin
--   depthReact … true  = depthFin … (lookupNode allNid (EvalSt.nodes st))
--   depthReact … false = 0
-- so each face passes its premise straight to the next and the absorbed
-- branch needs nothing at all
-- arithmetic lemmas consumed by thruOuter-face-core's walk helpers

open import Verify-Budget-Sufficient.Caps-Face.Part1 using
  (n≤capsAt-size; powʳ1; sq≤pow)

-- THE WALK'S CHARGE, AND IT IS SEALED.  A quantity named in a PREMISE
-- is normalised at every application of every statement carrying it,
-- and this one reaches an exponential of a caps field -- so left
-- transparent it puts that exponential inside each of the walk's sites,
-- measured at half again the module's whole check.  Consumers need two
-- facts about it and both are proven here: it dominates the unscaled
-- charge the other two arms are stated in, and the ceiling leaf below
-- reads it back through its own equation.

-- AND ITS EXPONENT IS A CHOICE RATHER THAN A FLOOR, WHICH IS WHAT
-- DECIDES THE WALKED SINK HOP.  The charge carries a cap CUBED in its
-- exponent while the fuel affords a cap's own EXPONENTIAL there, so the
-- level range a caller can afford against it comes out QUADRATIC in the
-- cap where it could be exponential.  That range is the one the sink
-- hop's refutations measure against, and the registry's reading one
-- level up is quadratic too -- which is why the two cross at all.
-- Every level bought past that crossing is bought HERE, by a
-- redefinition whose whole cost lands on the ceiling leaf below, which
-- is where this instant's fuel headroom is spent.
--
-- WHAT WIDENING CANNOT BUY IS UNBOUNDED NESTING.  A fan-out enters at
-- the size reading of the level it left, so the levels one cascade
-- consumes are a TOWER whose height is the dispatch gas, while any
-- exponent under this instant's fuel affords a range that is merely
-- exponential.  So it settles the hop only if ONE cascade's own level
-- count fits that range.  Reading the next instant's size instead is
-- not the way out: the caps advance by a whole instant's folds, so that
-- reading is the increment the ceiling leaf below already records dead.
--
-- AND THE TOWER IS STRUCTURAL, SO THE MEASUREMENT COMES OUT NEGATIVE.
-- What drives it is not slack anywhere: one chain step moves the
-- registry's own pricing by a LEVEL, because a subscribing frame swaps
-- its head for an inner and pushes that inner's operators on as frames,
-- and `Refuted.Chain-Step-Regs-Cap` pins the repair as exactly that
-- level rather than as a further hypothesis.  So a fan-out entered at
-- one level meets chains priced a level up, and the count towers with
-- the dispatch gas by construction.  No exponent this fuel affords is a
-- tower, so what moves is the walked side's MECHANISM and not its
-- number -- and the potential face, whose receipt shrinks along the
-- path and carries no level ledger at all, is the one already standing.

abstract
  nestWalkAt : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
    (id : ℕ) → ℕ
  nestWalkAt e sl id =
    2 ^ suc (Caps.cSize (capsAt e sl id)
               * (Caps.cSize (capsAt e sl id) * Caps.cSize (capsAt e sl id))
             + Caps.cSize (capsAt e sl id)
               * (Caps.cSize (capsAt e sl id) * Caps.cSize (capsAt e sl id))
             + (Caps.cSize (capsAt e sl id) * Caps.cSize (capsAt e sl id)
                + Caps.cSize (capsAt e sl id) * Caps.cSize (capsAt e sl id)))
      * (nestUnit e sl
         + (Caps.cSize (capsAt e sl id) * Caps.cSize (capsAt e sl id)
            + Caps.cSize (capsAt e sl id) * Caps.cSize (capsAt e sl id))
         + Caps.cSize (capsAt e sl id)
         + Caps.cSize (capsAt e sl id) * slotWrapSum sl)

  nestWalkAt-def : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
    (id : ℕ) →
    nestWalkAt e sl id
      ≡ 2 ^ suc (Caps.cSize (capsAt e sl id)
                   * (Caps.cSize (capsAt e sl id) * Caps.cSize (capsAt e sl id))
                 + Caps.cSize (capsAt e sl id)
                   * (Caps.cSize (capsAt e sl id) * Caps.cSize (capsAt e sl id))
                 + (Caps.cSize (capsAt e sl id) * Caps.cSize (capsAt e sl id)
                    + Caps.cSize (capsAt e sl id) * Caps.cSize (capsAt e sl id)))
          * (nestUnit e sl
             + (Caps.cSize (capsAt e sl id) * Caps.cSize (capsAt e sl id)
                + Caps.cSize (capsAt e sl id) * Caps.cSize (capsAt e sl id))
             + Caps.cSize (capsAt e sl id)
             + Caps.cSize (capsAt e sl id) * slotWrapSum sl)
  nestWalkAt-def _ _ _ = refl

  capΦAt : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
    (id : ℕ) → ℕ
  capΦAt e sl id =
    2 ^ suc (Caps.cSize (capsAt e sl id)
               * (Caps.cSize (capsAt e sl id) * Caps.cSize (capsAt e sl id))
             + Caps.cSize (capsAt e sl id) * Caps.cSize (capsAt e sl id))
      * nestCapAt e sl id

  capΦAt-def : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
    (id : ℕ) →
    capΦAt e sl id
      ≡ 2 ^ suc (Caps.cSize (capsAt e sl id)
                   * (Caps.cSize (capsAt e sl id) * Caps.cSize (capsAt e sl id))
                 + Caps.cSize (capsAt e sl id) * Caps.cSize (capsAt e sl id))
          * nestCapAt e sl id
  capΦAt-def _ _ _ = refl

  nestΦAt : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
    (id : ℕ) → ℕ
  nestΦAt e sl id = capΦAt e sl id + nestWalkAt e sl id

  nestΦAt-def : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
    (id : ℕ) →
    nestΦAt e sl id ≡ capΦAt e sl id + nestWalkAt e sl id
  nestΦAt-def _ _ _ = refl

  nestWalkAt≤nestΦAt : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
    (id : ℕ) → nestWalkAt e sl id ≤ nestΦAt e sl id
  nestWalkAt≤nestΦAt e sl id = m≤n+m (nestWalkAt e sl id) (capΦAt e sl id)

  nestCapAt≤nestΦAt : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
    (id : ℕ) → nestCapAt e sl id ≤ nestΦAt e sl id
  nestCapAt≤nestΦAt e sl id =
    ≤-trans (≤-trans (≤-reflexive (sym (*-identityˡ (nestCapAt e sl id))))
                     (*-monoˡ-≤ (nestCapAt e sl id)
                                (m^n>0 2 (suc (Caps.cSize (capsAt e sl id)
                                                 * (Caps.cSize (capsAt e sl id)
                                                    * Caps.cSize (capsAt e sl id))
                                               + Caps.cSize (capsAt e sl id)
                                                 * Caps.cSize (capsAt e sl id))))))
            (m≤m+n (capΦAt e sl id) (nestWalkAt e sl id))

-- THE SLOT VOCABULARY'S NESTING UNDER ITS SIZE, slot by slot: a
-- scripted slot's own index makes its nesting zero, and a shared one's
-- is its expression's, which that expression's size dominates.
slotNest≤slotSize : ∀ {n} {Γ : Ctx n} {k t} (s : Slot Γ k t) →
  slotNest s ≤ slotSize s
slotNest≤slotSize (scripted _) = z≤n
slotNest≤slotSize (shared d)   = nestDᵉ≤sizeᵉ d

slotsNestSum≤slotsSize : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) →
  slotsNestSum sl ≤ slotsSize sl
slotsNestSum≤slotsSize sl =
  sum-tab-mono (λ i → slotNest (sl i)) (λ i → slotSize (sl i))
               (λ i → slotNest≤slotSize (sl i))

-- ONE SLOT'S WRAP UNDER THE VOCABULARY'S SIZE.  The wrap reads a shared
-- definition through the same per-occurrence factor the walk charges
-- every subject through, and both of its readings -- the exponent and
-- the nesting -- are under that definition's own size, which is one
-- summand of the telescope.  A scripted slot is zero.
slotWrap≤size : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (S : ℕ) →
  slotsSize sl ≤ S → (i : Fin n) → slotWrap (sl i) ≤ 2 ^ S * S
slotWrap≤size sl S hS i
  with sl i | ≤-trans (fᵢ≤sum-tab (λ j → slotSize (sl j)) i) hS
... | scripted _ | _  = z≤n
... | shared d   | hd =
  *-mono-≤ (^-monoʳ-≤ 2 (≤-trans (syncSize≤sizeᵉ d) hd))
           (≤-trans (nestDᵉ≤sizeᵉ d) hd)

-- AND THE WHOLE TELESCOPE'S, which is the per-slot ceiling times a
-- length -- and the length is under the size too, since a slot costs at
-- least one.
slotWrapSum≤size : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (S : ℕ) →
  slotsSize sl ≤ S → slotWrapSum sl ≤ S * (2 ^ S * S)
slotWrapSum≤size {n = n} sl S hS =
  ≤-trans (sum-tab-mono (λ i → slotWrap (sl i)) (λ _ → 2 ^ S * S)
                        (slotWrap≤size sl S hS))
          (≤-trans (≤-reflexive (sum-tab-const {n} (2 ^ S * S)))
                   (*-monoˡ-≤ (2 ^ S * S) (≤-trans (n≤slotsSize sl) hS)))

-- FOUR SQUARES UNDER THE EXPONENTIAL, which is where the base case's
-- room comes from and why the size floor is eight rather than six.
sq4≤2^ : ∀ (S : ℕ) → 8 ≤ S → 4 * (S * S) ≤ 2 ^ S
sq4≤2^ (suc (suc k)) (s≤s (s≤s 6≤k)) =
  ≤-trans (*-monoʳ-≤ 4 (sq≤2^ k 6≤k))
          (≤-reflexive (sym (^-distribˡ-+-* 2 2 k)))

-- ONE CUBE'S EXPANSION, which is the whole ring content of the
-- induction below: a successor adds a SQUARE's worth of terms to a
-- cube.
cubeStep : ∀ (t : ℕ) →
  suc t * (suc t * suc t) ≡ t * (t * t) + (3 * (t * t) + (3 * t + 1))
cubeStep = solve 1 (λ a → (con 1 :+ a) :* ((con 1 :+ a) :* (con 1 :+ a))
                        := a :* (a :* a)
                           :+ (con 3 :* (a :* a) :+ (con 3 :* a :+ con 1)))
                 refl

-- AND WHAT IT ADDS IS UNDER THE CUBE ITSELF from seven on, so a
-- successor at most DOUBLES the cube -- which is exactly what one more
-- factor of two buys.
cubeGap : ∀ (t : ℕ) → 7 ≤ t → 3 * (t * t) + (3 * t + 1) ≤ t * (t * t)
cubeGap t 7≤t =
  ≤-trans (+-monoʳ-≤ (3 * (t * t)) lin)
          (≤-trans (≤-reflexive sevenEq) (*-monoˡ-≤ (t * t) 7≤t))
  where
  1≤t : 1 ≤ t
  1≤t = ≤-trans (s≤s z≤n) 7≤t
  t≤tt : t ≤ t * t
  t≤tt = ≤-trans (≤-reflexive (sym (*-identityʳ t))) (*-monoʳ-≤ t 1≤t)
  fourEq : 3 * t + t ≡ 4 * t
  fourEq = solve 1 (λ a → con 3 :* a :+ a := con 4 :* a) refl t
  lin : 3 * t + 1 ≤ 4 * (t * t)
  lin = ≤-trans (+-monoʳ-≤ (3 * t) 1≤t)
                (≤-trans (≤-reflexive fourEq) (*-monoʳ-≤ 4 t≤tt))
  sevenEq : 3 * (t * t) + 4 * (t * t) ≡ 7 * (t * t)
  sevenEq = solve 1 (λ a → con 3 :* a :+ con 4 :* a := con 7 :* a) refl (t * t)

-- THE THRESHOLD IS CARRIED IN SUC FORM, AND THAT IS A COST DECISION
-- RATHER THAN A SPELLING ONE.  Writing the shifted index as `14 + j`
-- gives the exponent two spellings that differ at EVERY rung, and the
-- conversion check reconciling them descends into both halves of each
-- doubling, so a threshold that reads as a numeral costs two to the
-- power of the threshold.  The square below runs at six and survives
-- that; a cube starts at fourteen and does not.  Everything here --
-- the statement, the pattern, the recursive call -- therefore names
-- `from14`, so the two sides meet already identical.
from14 : ℕ → ℕ
from14 j =
  suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc j)))))))))))))

7≤from14 : ∀ (j : ℕ) → 7 ≤ from14 j
7≤from14 j = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))

-- FOUR CUBES UNDER THE EXPONENTIAL, and FOURTEEN is where that starts
-- -- the cube overtakes seven rungs later than the square does, which
-- is the whole reason the caps floor had to be read at a bigger
-- number.  Below fourteen the statement is FALSE rather than merely
-- unproven, so the base case is where it first holds and not where it
-- is convenient.
cube-exp : ∀ (j : ℕ) →
  4 * (from14 j * (from14 j * from14 j)) ≤ 2 ^ from14 j
cube-exp zero    = ≤ᵇ⇒≤ 10976 16384 tt
cube-exp (suc j) =
  ≤-trans (≤-reflexive step)
          (≤-trans (+-mono-≤ (cube-exp j)
                             (≤-trans (*-monoʳ-≤ 4 (cubeGap t (7≤from14 j)))
                                      (cube-exp j)))
                   (≤-reflexive (sym (2X≡X+X (2 ^ t)))))
  where
  t = from14 j
  step : 4 * (suc t * (suc t * suc t))
           ≡ 4 * (t * (t * t)) + 4 * (3 * (t * t) + (3 * t + 1))
  step = trans (cong (4 *_) (cubeStep t))
               (*-distribˡ-+ 4 (t * (t * t)) (3 * (t * t) + (3 * t + 1)))

-- ONE CLAUSE COVERS, because fourteen `s≤s` is the only way the
-- premise can be built and it fixes the subject's shape as it goes.
cube4≤2^ : ∀ (S : ℕ) → 14 ≤ S → 4 * (S * (S * S)) ≤ 2 ^ S
cube4≤2^ _
  (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s _))))))))))))))
  = cube-exp _

-- THE INSTANT'S SIZE GROWTH, OVER A BARE COUNT.  A frame multiplies
-- the size by a fixed step, so `j` of them is a power whose base is a
-- small multiple of the cap and whose exponent is the count itself;
-- and the cap's own square sits under an exponential once the cap is
-- past fourteen, so the whole power reduces to base two at an exponent
-- LINEAR in the count.  That linearity is the content: the statement
-- says nothing about which counts are reachable, which is what makes
-- it reusable at a charge the caller chooses.
--
-- AND THE COUNT BOUND IS THE CALLER'S, DELIBERATELY.  This used to
-- carry a `j ≤ S * S + S + S * S` premise and conclude at the walk
-- factor directly, which pinned the arithmetic to one reading of what
-- a cascade's levels run to -- so the statement had to be restated
-- every time the charge did, and it was.  The count now rides in the
-- exponent, the affordability is the consumer's leaf, and a
-- re-denomination of the charge moves neither.
iterSize≤2^ : ∀ (S j s : ℕ) → 8 ≤ S → s ≤ S →
  iterSize S j s ≤ 2 ^ (S * j) * S
iterSize≤2^ S j s h8 hs =
  ≤-trans (iterSize-pow S S j s 1≤S ≤-refl hs) (*-monoˡ-≤ S powFit)
  where
  1≤S : 1 ≤ S
  1≤S = ≤-trans (≤ᵇ⇒≤ 1 8 tt) h8
  3≤4S : 3 ≤ 4 * S
  3≤4S = ≤-trans (≤ᵇ⇒≤ 3 4 tt)
                 (≤-trans (≤-reflexive (sym (*-identityʳ 4)))
                          (*-monoʳ-≤ 4 1≤S))
  3S≤2^S : 3 * S ≤ 2 ^ S
  3S≤2^S =
    ≤-trans (*-monoˡ-≤ S 3≤4S)
            (≤-trans (≤-reflexive (*-assoc 4 S S)) (sq4≤2^ S h8))
  powFit : (3 * S) ^ j ≤ 2 ^ (S * j)
  powFit =
    ≤-trans (^-monoˡ-≤ j 3S≤2^S) (≤-reflexive (^-*-assoc 2 S j))

-- THE STEP'S ARITHMETIC, OVER BARE NUMBERS, and it is a body rather
-- than a leaf.  Nothing about caps survives here: a cap that steps by
-- multiplying an exponential onto a sum fits two exponentials of the
-- next size exactly when that exponent, the increment's own exponent,
-- the previous budget and the next size all fit ONE.  Stating it over
-- numerals is what makes the step instantiable at all -- both sides of
-- the caps-indexed form sit on a recurrence that does not terminate
-- natively, so the statement it came from could not be reached by any
-- row.
nest-step-ℕ : ∀ (S S′ Q Q′ q′ C I C′ L M : ℕ) → 1 ≤ Q → Q′ ≤ 2 ^ q′ →
  C′ ≤ 2 ^ L * (C + I) →
  I ≤ 2 ^ M →
  q′ + 3 + (2 ^ S + M) + L ≤ 2 ^ S′ →
  Q * (4 * C) ≤ 2 ^ (2 ^ S) →
  Q′ * (4 * C′) ≤ 2 ^ (2 ^ S′)
nest-step-ℕ S S′ Q Q′ q′ C I C′ L M 1≤Q hQ′ hC′ hI hroom ih =
  ≤-trans (*-mono-≤ hQ′ (*-monoʳ-≤ 4 hC′E))
          (≤-trans (≤-reflexive (sym collect)) (^-monoʳ-≤ 2 hroom′))
  where
  K = 2 ^ S + M
  C≤4C : C ≤ 4 * C
  C≤4C = ≤-trans (≤-reflexive (sym (*-identityˡ C)))
                 (*-monoˡ-≤ C {1} {4} (s≤s z≤n))
  4C≤S4C : 4 * C ≤ Q * (4 * C)
  4C≤S4C = ≤-trans (≤-reflexive (sym (*-identityˡ (4 * C))))
                   (*-monoˡ-≤ (4 * C) 1≤Q)
  C≤ : C ≤ 2 ^ K
  C≤ = ≤-trans (≤-trans C≤4C 4C≤S4C)
               (≤-trans ih (^-monoʳ-≤ 2 (m≤m+n (2 ^ S) M)))
  I≤ : I ≤ 2 ^ K
  I≤ = ≤-trans hI (^-monoʳ-≤ 2 (m≤n+m M (2 ^ S)))
  CI≤ : C + I ≤ 2 ^ suc K
  CI≤ = ≤-trans (+-mono-≤ C≤ I≤) (≤-reflexive (sym (2X≡X+X (2 ^ K))))
  hC′E : C′ ≤ 2 ^ L * 2 ^ suc K
  hC′E = ≤-trans hC′ (*-monoʳ-≤ (2 ^ L) CI≤)
  collect : 2 ^ (q′ + (2 + (L + suc K))) ≡ 2 ^ q′ * (4 * (2 ^ L * 2 ^ suc K))
  collect = trans (^-distribˡ-+-* 2 q′ (2 + (L + suc K)))
                  (cong (2 ^ q′ *_)
                    (trans (^-distribˡ-+-* 2 2 (L + suc K))
                           (cong (4 *_) (^-distribˡ-+-* 2 L (suc K)))))
  reshape : q′ + (2 + (L + suc K)) ≡ q′ + 3 + K + L
  reshape = solve 3 (λ s l k → s :+ (con 2 :+ (l :+ (con 1 :+ k)))
                                 := s :+ con 3 :+ k :+ l)
                  refl q′ L K
  hroom′ : q′ + (2 + (L + suc K)) ≤ 2 ^ S′
  hroom′ = ≤-trans (≤-reflexive reshape) hroom

-- THE PROGRAM'S OWN VOCABULARY UNDER THE INSTANT'S SIZE.  The wrap
-- unit reads the expression's nesting and the slots', each of which its
-- own size dominates, and the caps recurrence's base bound already
-- holds that sum -- so the unit is a caps quantity and the increment
-- below can be priced without any syntax in it.
nestUnit≤size : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  nestUnit e sl ≤ Caps.cSize (capsAt e sl id)
nestUnit≤size e sl id =
  ≤-trans (≤-trans (s≤s (+-mono-≤ (nestDᵉ≤sizeᵉ e) (slotsNestSum≤slotsSize sl)))
                   (n≤1+n _))
          (capsAt-base-size e sl id)

-- THE INCREMENT'S EXPONENT, AND EVERY FIELD IN IT READ AT THE NEXT
-- INSTANT'S SIZE.  The burst is a `suc` of the width and the width at
-- an instant is strictly under the size at the next one; the registry
-- is under its own size and that size is under the next; the wrap unit
-- is under the size too.  What stays unreduced is the delivery, at both
-- instants -- which is the recurrence the room has to pay for.
nestIncLog : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) → ℕ
nestIncLog {n = n} e sl id =
  S′ * (S′ * (suc (suc (S′ * delSize n (capsAt e sl (suc id))))
              * (suc (delSq n (capsAt e sl (suc id))) * S′)))
  where S′ = Caps.cSize (capsAt e sl (suc id))

-- the burst and the registry at the next size, which both exponents want
burst≤size′ : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  nestBurstAt e sl id ≤ Caps.cSize (capsAt e sl (suc id))
burst≤size′ e sl id = ≤-reflexive (nestBurstAt-def e sl id)

reg≤size′ : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  realWidAt e sl id ≤ Caps.cSize (capsAt e sl (suc id))
reg≤size′ e sl id =
  ≤-trans (≤-trans (≤-reflexive (realWidAt-def e sl id))
                   (B2-cReg≤cSize e sl id))
          (capsAt-size-mono e sl id)

nestInc≤exp : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  nestIncAt e sl id ≤ 2 ^ nestIncLog e sl id
nestInc≤exp {n = n} e sl id =
  ≤-trans (≤-trans (≤-reflexive (nestIncAt-def e sl id)) shape)
          (<⇒≤ (n<2^n (nestIncLog e sl id)))
  where
  shape : realWidAt e sl id
            * (nestBurstAt e sl id
               * (suc (suc (realWidAt e sl id * delSize n (capsAt e sl (suc id))))
                  * nestU (delSq n (capsAt e sl (suc id))) (nestUnit e sl)))
            ≤ nestIncLog e sl id
  shape =
    *-mono-≤ (reg≤size′ e sl id)
      (*-mono-≤ (burst≤size′ e sl id)
        (*-mono-≤ (s≤s (s≤s (*-monoˡ-≤ (delSize n (capsAt e sl (suc id)))
                                      (reg≤size′ e sl id))))
                  (≤-trans (≤-reflexive (nestU-def (delSq n (capsAt e sl (suc id)))
                                                   (nestUnit e sl)))
                           (*-monoʳ-≤ (suc (delSq n (capsAt e sl (suc id))))
                                      (≤-trans (nestUnit≤size e sl id)
                                               (capsAt-size-mono e sl id))))))

-- THE FACTOR'S EXPONENT, read the same way and with the same residue.
nestFacLog : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) → ℕ
nestFacLog {n = n} e sl id =
  suc S′ * suc S′ * (suc (delSize n (capsAt e sl (suc id)))
                     * (S′ * delSq n (capsAt e sl (suc id))))
  where S′ = Caps.cSize (capsAt e sl (suc id))

nestFac≤exp : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  nestFacAt e sl id ≤ 2 ^ nestFacLog e sl id
nestFac≤exp {n = n} e sl id =
  ≤-trans (≤-reflexive (nestFacAt-def e sl id))
          (^-monoʳ-≤ 2 (*-mono-≤ (*-mono-≤ (s≤s (burst≤size′ e sl id))
                                           (s≤s (burst≤size′ e sl id)))
                                 (*-monoʳ-≤ (suc (delSize n (capsAt e sl (suc id))))
                                            (*-monoˡ-≤ (delSq n (capsAt e sl (suc id)))
                                                       (reg≤size′ e sl id)))))

-- BOTH EXPONENTS UNDER ONE POWER OF THE NEXT SIZE.  Each is a product
-- whose only non-size factors are a delivery size and a delivery
-- square, and a delivery size is a closed power of `suc cSize` -- two
-- factors per unit of context depth, since the length recurrence
-- multiplies a registry by a successor of the size and the registry
-- is under that size.  Counting the factors of the two products gives
-- the same ceiling for both, so the room the step needs stops being
-- stated over two recurrences and becomes one inequality in three
-- numbers.
--
-- The delivery size at the PREVIOUS instant is read against the next
-- instant's base too, which is what lets one power serve both: the
-- size is monotone across the instant, and the bound is monotone in
-- its base.
bump : ∀ (a b z : ℕ) → 1 ≤ z → a + 1 ≤ b → a + z ≤ b * z
bump a b z 1≤z h =
  ≤-trans (+-monoˡ-≤ z (≤-trans (≤-reflexive (sym (*-identityʳ a)))
                                (*-monoʳ-≤ a 1≤z)))
  (≤-trans (+-monoʳ-≤ (a * z) (≤-reflexive (sym (*-identityˡ z))))
  (≤-trans (≤-reflexive (sym (*-distribʳ-+ z a 1)))
           (*-monoˡ-≤ z h)))

pow3 : ∀ (b a k : ℕ) → b ^ a * (b ^ k * (b ^ k * b ^ k)) ≡ b ^ (a + (k + (k + k)))
pow3 b a k =
  sym (trans (^-distribˡ-+-* b a (k + (k + k)))
             (cong (b ^ a *_)
               (trans (^-distribˡ-+-* b k (k + k))
                      (cong (b ^ k *_) (^-distribˡ-+-* b k k)))))

del-pow′ : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  suc (delSize n (capsAt e sl (suc id)))
    ≤ suc (Caps.cSize (capsAt e sl (suc id))) ^ suc (n + n)
del-pow′ {n = n} e sl id =
  delSize-exp n (capsAt e sl (suc id)) (B2-cReg≤cSize e sl (suc id))

nestIncLog≤pow : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  nestIncLog e sl id ≤ suc (Caps.cSize (capsAt e sl (suc id))) ^ (6 * n + 9)
nestIncLog≤pow {n = n} e sl id =
  ≤-trans (*-mono-≤ S′≤B
            (*-mono-≤ S′≤B (*-mono-≤ f3 (*-mono-≤ f4 S′≤B))))
          (≤-trans (≤-reflexive collect)
                   (≤-reflexive (trans (pow3 B 6 K1) (cong (B ^_) expo))))
  where
  S′ : ℕ
  S′ = Caps.cSize (capsAt e sl (suc id))
  B : ℕ
  B = suc S′
  K1 : ℕ
  K1 = suc (n + n)
  P : ℕ
  P = B ^ K1
  S′≤B : S′ ≤ B
  S′≤B = n≤1+n S′
  1≤P : 1 ≤ P
  1≤P = 1≤pow S′ K1
  1≤BP : 1 ≤ B * P
  1≤BP = 1≤pow S′ (suc K1)
  1≤PP : 1 ≤ P * P
  1≤PP = ≤-trans (1≤pow S′ (K1 + K1)) (≤-reflexive (^-distribˡ-+-* B K1 K1))
  3≤B : 2 + 1 ≤ B
  3≤B = s≤s (2≤capsAt-size e sl (suc id))
  2≤B : 1 + 1 ≤ B
  2≤B = ≤-trans (s≤s (s≤s z≤n)) 3≤B
  f3 : suc (suc (S′ * delSize n (capsAt e sl (suc id)))) ≤ B * (B * P)
  f3 = ≤-trans (+-monoʳ-≤ 2 (*-mono-≤ S′≤B
                              (≤-trans (n≤1+n (delSize n (capsAt e sl (suc id))))
                                       (del-pow′ e sl id))))
               (bump 2 B (B * P) 1≤BP 3≤B)
  f4 : suc (delSq n (capsAt e sl (suc id))) ≤ B * (P * P)
  f4 = ≤-trans (+-monoʳ-≤ 1
                 (≤-trans (≤-reflexive (delSq-def n (capsAt e sl (suc id))))
                          (*-mono-≤ (≤-trans (n≤1+n _) (del-pow′ e sl id))
                                    (≤-trans (n≤1+n _) (del-pow′ e sl id)))))
               (bump 1 B (P * P) 1≤PP 2≤B)
  collect : B * (B * ((B * (B * P)) * ((B * (P * P)) * B)))
              ≡ B ^ 6 * (P * (P * P))
  collect =
    solve 2 (λ b p → b :* (b :* ((b :* (b :* p)) :* ((b :* (p :* p)) :* b)))
                  := (b :* (b :* (b :* (b :* (b :* (b :* con 1)))))) :* (p :* (p :* p)))
            refl B P
  expo : 6 + (K1 + (K1 + K1)) ≡ 6 * n + 9
  expo = solve 1 (λ x → con 6 :+ ((con 1 :+ (x :+ x))
                                   :+ ((con 1 :+ (x :+ x)) :+ (con 1 :+ (x :+ x))))
                     := con 6 :* x :+ con 9)
               refl n

nestFacLog≤pow : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  nestFacLog e sl id ≤ suc (Caps.cSize (capsAt e sl (suc id))) ^ (6 * n + 9)
nestFacLog≤pow {n = n} e sl id =
  ≤-trans (*-mono-≤ (≤-refl {B * B}) (*-mono-≤ (del-pow′ e sl id) (*-mono-≤ S′≤B f4)))
          (≤-trans (≤-reflexive collect)
                   (≤-trans (≤-reflexive (trans (pow3 B 3 K1) (cong (B ^_) expo)))
                            (powʳ1 B (s≤s z≤n)
                                   (+-monoʳ-≤ (6 * n) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))))
  where
  S′ : ℕ
  S′ = Caps.cSize (capsAt e sl (suc id))
  B : ℕ
  B = suc S′
  K1 : ℕ
  K1 = suc (n + n)
  P : ℕ
  P = B ^ K1
  S′≤B : S′ ≤ B
  S′≤B = n≤1+n S′
  f4 : delSq n (capsAt e sl (suc id)) ≤ P * P
  f4 = ≤-trans (≤-reflexive (delSq-def n (capsAt e sl (suc id))))
               (*-mono-≤ (≤-trans (n≤1+n _) (del-pow′ e sl id))
                         (≤-trans (n≤1+n _) (del-pow′ e sl id)))
  collect : B * B * (P * (B * (P * P))) ≡ B ^ 3 * (P * (P * P))
  collect =
    solve 2 (λ b p → b :* b :* (p :* (b :* (p :* p)))
                  := (b :* (b :* (b :* con 1))) :* (p :* (p :* p)))
            refl B P
  expo : 3 + (K1 + (K1 + K1)) ≡ 6 * n + 6
  expo = solve 1 (λ x → con 3 :+ ((con 1 :+ (x :+ x))
                                   :+ ((con 1 :+ (x :+ x)) :+ (con 1 :+ (x :+ x))))
                     := con 6 :* x :+ con 6)
               refl n

-- THE CEILING ON THE NEXT SIZE, which is what makes its BIT LENGTH a
-- nameable number: the step is a quadratic iterated count-many times,
-- and once the size is at least four its square already sits under two
-- to it, so every factor the iteration contributes is a power of two
-- and the whole product is one.
size-upper : ∀ (c : Caps) (d : ℕ) → 4 ≤ Caps.cSize c →
  suc (Caps.cSize (frameBlowup c d))
    ≤ 2 ^ (Caps.cSize c * sizeCount c d + Caps.cSize c + 1)
size-upper c d 4≤S =
  ≤-trans (s≤s (≤-trans (iterSize-pow S S J S 1≤S ≤-refl ≤-refl) body))
          (≤-trans (+-monoˡ-≤ X (1≤pow≤ 2 (S * J + S) (s≤s z≤n)))
                   (≤-reflexive fin))
  where
  S : ℕ
  S = Caps.cSize c
  J : ℕ
  J = sizeCount c d
  X : ℕ
  X = 2 ^ (S * J + S)
  1≤S : 1 ≤ S
  1≤S = ≤-trans (s≤s z≤n) 4≤S
  3S≤ : 3 * S ≤ 2 ^ S
  3S≤ = ≤-trans (*-monoˡ-≤ S (≤-trans (n≤1+n 3) 4≤S)) (sq≤pow S 4≤S)
  body : (3 * S) ^ J * S ≤ 2 ^ (S * J + S)
  body =
    ≤-trans (*-mono-≤ (≤-trans (^-monoˡ-≤ J 3S≤)
                               (≤-reflexive (^-*-assoc 2 S J)))
                      (<⇒≤ (n<2^n S)))
            (≤-reflexive (sym (^-distribˡ-+-* 2 (S * J) S)))
  fin : X + X ≡ 2 ^ (S * J + S + 1)
  fin = trans (sym (2X≡X+X X))
              (trans (*-comm 2 X) (sym (^-distribˡ-+-* 2 (S * J + S) 1)))

capsAt-size-lower : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  Caps.cSize (capsAt e sl id)
    ^ suc (sizeCount (capsAt e sl id) (capsH e sl id))
    ≤ Caps.cSize (capsAt e sl (suc id))
capsAt-size-lower e sl id =
  size-lower (capsAt e sl id) (capsH e sl id)
    (≤-trans (s≤s z≤n) (2≤capsAt-size e sl id))

capsAt-size-upper : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  suc (Caps.cSize (capsAt e sl (suc id)))
    ≤ 2 ^ (Caps.cSize (capsAt e sl id)
             * sizeCount (capsAt e sl id) (capsH e sl id)
           + Caps.cSize (capsAt e sl id) + 1)
capsAt-size-upper e sl id =
  size-upper (capsAt e sl id) (capsH e sl id)
    (≤-trans (s≤s (s≤s (s≤s (s≤s z≤n)))) (8≤capsAt-size e sl id))

-- A LINEAR TERM UNDER A POWER, with four factors of the base already
-- spent.  The induction is on the exponent past five: one more step
-- multiplies the right by the base and the left by less than two, and
-- the base is at least eight.  Five is where the base case fits --
-- five copies of the fourth power are under the fifth once the base is
-- above five.
lin≤pow : ∀ (S j : ℕ) → 8 ≤ S → S * S * S * S * (5 + j) ≤ S ^ (5 + j)
lin≤pow S zero    8≤S =
  ≤-trans (*-monoʳ-≤ (S * S * S * S) (≤-trans (≤ᵇ⇒≤ 5 8 tt) 8≤S))
          (≤-reflexive (solve 1 (λ x → x :* x :* x :* x :* x
                                    := x :* (x :* (x :* (x :* (x :* con 1)))))
                              refl S))
lin≤pow S (suc j) 8≤S =
  ≤-trans (*-monoʳ-≤ (S * S * S * S) grow)
  (≤-trans (≤-reflexive shape)
  (≤-trans (*-monoˡ-≤ (S * S * S * S * (5 + j)) 2≤S)
           (*-monoʳ-≤ S (lin≤pow S j 8≤S))))
  where
  grow : 5 + suc j ≤ 2 * (5 + j)
  grow = ≤-trans (m≤m+n (5 + suc j) (4 + j))
                 (≤-reflexive (solve 1 (λ x → (con 6 :+ x) :+ (con 4 :+ x)
                                            := con 2 :* (con 5 :+ x))
                                     refl j))
  shape : S * S * S * S * (2 * (5 + j)) ≡ 2 * (S * S * S * S * (5 + j))
  shape = solve 2 (λ a y → a :* (con 2 :* y) := con 2 :* (a :* y))
                  refl (S * S * S * S) (5 + j)
  2≤S : 2 ≤ S
  2≤S = ≤-trans (≤ᵇ⇒≤ 2 8 tt) 8≤S

lin≤powJ : ∀ (S J : ℕ) → 8 ≤ S → 5 ≤ J → S * S * S * S * J ≤ S ^ J
lin≤powJ S _ 8≤S (s≤s (s≤s (s≤s (s≤s (s≤s _))))) = lin≤pow S _ 8≤S

-- WHAT THE STEP HAS TO PAY FOR, in the currency the room is stated
-- in: the exponent times the bit length of the next size, plus the
-- four constant terms.  Every factor here is linear in the size or in
-- the count, so the whole obligation is a fourth power of the size
-- times the count -- and the next size is a power of the size whose
-- exponent IS the count, which swallows it with four factors to
-- spare.
room-arith : ∀ (S J K : ℕ) → 8 ≤ S → S ≤ J → K ≤ 6 * S + 9 →
  K * (S * J + S + 1) + 4 ≤ S ^ suc J
room-arith S J K 8≤S S≤J K≤ =
  ≤-trans (+-monoˡ-≤ 4 (*-mono-≤ (≤-trans K≤ K15) bIsSmall))
  (≤-trans (+-mono-≤ (≤-reflexive collect) 4≤SSJ)
  (≤-trans (≤-reflexive (solve 1 (λ y → con 45 :* y :+ y := con 46 :* y)
                               refl (S * S * J)))
  (≤-trans (*-monoˡ-≤ (S * S * J) 46≤SS)
  (≤-trans (≤-reflexive (solve 3 (λ a b y → (a :* b) :* (a :* b :* y)
                                         := a :* b :* a :* b :* y)
                               refl S S J))
  (≤-trans (lin≤powJ S J 8≤S (≤-trans (≤ᵇ⇒≤ 5 8 tt) (≤-trans 8≤S S≤J)))
           (powʳ1 S (≤-trans (s≤s z≤n) 8≤S) (n≤1+n J)))))))
  where
  1≤S : 1 ≤ S
  1≤S = ≤-trans (s≤s z≤n) 8≤S
  1≤J : 1 ≤ J
  1≤J = ≤-trans 1≤S S≤J
  1≤SJ : 1 ≤ S * J
  1≤SJ = *-mono-≤ 1≤S 1≤J
  S≤SJ : S ≤ S * J
  S≤SJ = ≤-trans (≤-reflexive (sym (*-identityʳ S))) (*-monoʳ-≤ S 1≤J)
  K15 : 6 * S + 9 ≤ 15 * S
  K15 = ≤-trans (+-monoʳ-≤ (6 * S)
                  (≤-trans (≤-reflexive (sym (*-identityʳ 9))) (*-monoʳ-≤ 9 1≤S)))
                (≤-reflexive (solve 1 (λ x → con 6 :* x :+ con 9 :* x := con 15 :* x)
                                    refl S))
  bIsSmall : S * J + S + 1 ≤ 3 * (S * J)
  bIsSmall = ≤-trans (+-mono-≤ (+-monoʳ-≤ (S * J) S≤SJ) 1≤SJ)
                     (≤-reflexive (solve 1 (λ y → y :+ y :+ y := con 3 :* y)
                                         refl (S * J)))
  collect : 15 * S * (3 * (S * J)) ≡ 45 * (S * S * J)
  collect = solve 2 (λ x y → con 15 :* x :* (con 3 :* (x :* y))
                          := con 45 :* (x :* x :* y))
                  refl S J
  4≤SSJ : 4 ≤ S * S * J
  4≤SSJ = ≤-trans (≤ᵇ⇒≤ 4 64 tt) (*-mono-≤ (*-mono-≤ 8≤S 8≤S) 1≤J)
  46≤SS : 46 ≤ S * S
  46≤SS = ≤-trans (≤ᵇ⇒≤ 46 64 tt) (*-mono-≤ 8≤S 8≤S)

-- THE ROOM ITSELF, and it is three numbers now.  The budget is two to
-- the next size; the next size and its bit length are named
-- separately, because what has to be paid for is the exponent TIMES
-- that length, and the hypothesis says the next size covers it with
-- four to spare.  The two halves are then each under half the budget:
-- the constant part by the square lemma, the two powers because the
-- length was bought.
room-gen : ∀ (A E S′ K b : ℕ) → 7 ≤ S′ → suc S′ ≤ 2 ^ b →
  K * b + 4 ≤ S′ → 2 * (A + 3 + E) ≤ 2 ^ S′ →
  A + 3 + (E + suc S′ ^ K) + suc S′ ^ K ≤ 2 ^ S′
room-gen A E (suc S″) K b (s≤s 6≤S″) hB hK hA =
  ≤-trans (≤-reflexive regroup)
  (≤-trans (+-mono-≤ half twoP)
           (≤-reflexive (sym (2X≡X+X (2 ^ S″)))))
  where
  P : ℕ
  P = suc (suc S″) ^ K
  regroup : A + 3 + (E + P) + P ≡ (A + 3 + E) + (P + P)
  regroup = solve 3 (λ a e p → a :+ con 3 :+ (e :+ p) :+ p
                            := (a :+ con 3 :+ e) :+ (p :+ p))
                  refl A E P
  half : A + 3 + E ≤ 2 ^ S″
  half = *-cancelˡ-≤ 2 hA
  P≤ : P ≤ 2 ^ (b * K)
  P≤ = ≤-trans (^-monoˡ-≤ K hB) (≤-reflexive (^-*-assoc 2 b K))
  bK+1≤ : suc (b * K) ≤ S″
  bK+1≤ = ≤-trans (s≤s (≤-reflexive (*-comm b K)))
                  (≤-pred (≤-trans (≤-reflexive (+-comm 2 (K * b)))
                          (≤-trans (+-monoʳ-≤ (K * b) (≤ᵇ⇒≤ 2 4 tt)) hK)))
  twoP : P + P ≤ 2 ^ S″
  twoP = ≤-trans (+-mono-≤ P≤ P≤)
         (≤-trans (≤-reflexive (sym (2X≡X+X (2 ^ (b * K)))))
                  (^-monoʳ-≤ 2 bK+1≤))

nestFac-room : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id A : ℕ) →
  2 * (A + 3 + 2 ^ Caps.cSize (capsAt e sl id))
    ≤ 2 ^ Caps.cSize (capsAt e sl (suc id)) →
  A + 3
    + (2 ^ Caps.cSize (capsAt e sl id) + nestIncLog e sl id)
    + nestFacLog e sl id
    ≤ 2 ^ Caps.cSize (capsAt e sl (suc id))
nestFac-room {n = n} e sl id A hA =
  ≤-trans (+-mono-≤ (+-monoʳ-≤ (A + 3)
                      (+-monoʳ-≤ (2 ^ Caps.cSize (capsAt e sl id))
                                 (nestIncLog≤pow e sl id)))
                    (nestFacLog≤pow e sl id))
          (room-gen A
                    (2 ^ Caps.cSize (capsAt e sl id))
                    (Caps.cSize (capsAt e sl (suc id)))
                    (6 * n + 9)
                    (Caps.cSize (capsAt e sl id) * J
                      + Caps.cSize (capsAt e sl id) + 1)
                    (≤-trans (≤ᵇ⇒≤ 7 8 tt) (8≤capsAt-size e sl (suc id)))
                    (capsAt-size-upper e sl id)
                    (≤-trans (room-arith (Caps.cSize (capsAt e sl id)) J (6 * n + 9)
                                (8≤capsAt-size e sl id)
                                (size≤sizeCount (capsAt e sl id) (capsH e sl id)
                                  (2≤capsAt-size e sl id) (1≤capsAt-reg e sl id))
                                (+-monoˡ-≤ 9 (*-monoʳ-≤ 6 (n≤capsAt-size e sl id))))
                             (capsAt-size-lower e sl id))
                    hA)
  where
  J : ℕ
  J = sizeCount (capsAt e sl id) (capsH e sl id)

-- WHY THE EXPONENT AND NOT THE SIZE.  The cap exponentiates a caps
-- field once per instant, so it stands above the size at its own
-- instant and no bound denominated in the size can hold it.  Two
-- exponentials is what it costs and not one, because the exponent the
-- cap raises is a POLYNOMIAL of the caps field rather than the field:
-- it reads a delivery SQUARE of the caps at the next instant, which is
-- cubic in a size one exponential would only have matched linearly.
--
-- AND THE CONSTRAINT THE SHAPE HAS TO RESPECT IS THE INDEX: no summand
-- may price the cap at the instant AFTER the one being bounded.  The
-- hypothesis and the conclusion are read one instant apart and that is
-- the whole of it -- the delivery the exponents read is the next
-- instant's, which is what the room, not the cap, is charged for.
-- THE RE-ASSOCIATION THE STEP IS APPLIED THROUGH.  The induction is
-- carried at a LEADING COEFFICIENT rather than at the size, so the
-- statement reads the sealed charge while the step reads a coefficient
-- times a bare cap; the two are one product read two ways.
mash4 : ∀ (s q c : ℕ) → s * (4 * (q * c)) ≡ s * q * (4 * c)
mash4 s q c =
  solve 3 (λ s′ q′ c′ → s′ :* (con 4 :* (q′ :* c′)) := s′ :* q′ :* (con 4 :* c′))
        refl s q c

-- THE ROOM THE FATTER COEFFICIENT ASKS FOR, over bare numbers.  The
-- coefficient the walk's own charge carries is an exponential of a size
-- CUBE, so the room premise gains that cube beside the size it already
-- had -- and a cube with four to spare is exactly what the size cap's
-- reachable floor buys, with the linear and constant parts absorbed
-- into a square along the way.
capΦ-room-ℕ : ∀ (S′ p : ℕ) → 21 ≤ S′ → p ≤ S′ →
  2 * (S′ + suc (S′ * (S′ * S′) + S′ * S′) + 3 + p) ≤ 2 ^ S′
capΦ-room-ℕ S′ p 21≤S′ hp =
  ≤-trans (*-monoʳ-≤ 2 (+-monoʳ-≤ (S′ + suc (Cu + Sq) + 3) hp))
  (≤-trans (≤-reflexive expand)
  (≤-trans (+-monoʳ-≤ (2 * Cu) rest)
  (≤-trans (≤-reflexive four) (cube4≤2^ S′ 14≤S′))))
  where
  Sq = S′ * S′
  Cu = S′ * (S′ * S′)
  1≤S′ : 1 ≤ S′
  1≤S′ = ≤-trans (≤ᵇ⇒≤ 1 21 tt) 21≤S′
  7≤S′ : 7 ≤ S′
  7≤S′ = ≤-trans (≤ᵇ⇒≤ 7 21 tt) 21≤S′
  14≤S′ : 14 ≤ S′
  14≤S′ = ≤-trans (≤ᵇ⇒≤ 14 21 tt) 21≤S′
  1≤Sq : 1 ≤ Sq
  1≤Sq = *-mono-≤ 1≤S′ 1≤S′
  S′≤Sq : S′ ≤ Sq
  S′≤Sq = ≤-trans (≤-reflexive (sym (*-identityʳ S′))) (*-monoʳ-≤ S′ 1≤S′)
  expand : 2 * (S′ + suc (Cu + Sq) + 3 + S′) ≡ 2 * Cu + (2 * Sq + 4 * S′ + 8)
  expand = solve 3 (λ s c q → con 2 :* (s :+ (con 1 :+ (c :+ q)) :+ con 3 :+ s)
                           := con 2 :* c :+ (con 2 :* q :+ con 4 :* s :+ con 8))
                 refl S′ Cu Sq
  collect14 : 2 * Sq + 4 * Sq + 8 * Sq ≡ 2 * (7 * Sq)
  collect14 = solve 1 (λ q → con 2 :* q :+ con 4 :* q :+ con 8 :* q
                          := con 2 :* (con 7 :* q))
                    refl Sq
  rest : 2 * Sq + 4 * S′ + 8 ≤ 2 * Cu
  rest =
    ≤-trans (+-mono-≤ (+-monoʳ-≤ (2 * Sq) (*-monoʳ-≤ 4 S′≤Sq))
                      (*-monoʳ-≤ 8 1≤Sq))
    (≤-trans (≤-reflexive collect14) (*-monoʳ-≤ 2 (*-monoˡ-≤ Sq 7≤S′)))
  four : 2 * Cu + 2 * Cu ≡ 4 * Cu
  four = solve 1 (λ c → con 2 :* c :+ con 2 :* c := con 4 :* c) refl Cu

-- AND THE BASE, at the same coefficient.  The cap at instant zero is
-- the program's nesting unit, which the size cap covers, so what is
-- being fitted is a square times the coefficient -- and the square
-- costs one size while the coefficient costs its own exponent, both of
-- them under the cube the floor affords.
capΦ-base-ℕ : ∀ (S u : ℕ) → 21 ≤ S → u ≤ S →
  S * (4 * (2 ^ suc (S * (S * S) + S * S) * u)) ≤ 2 ^ (2 ^ S)
capΦ-base-ℕ S u 21≤S hu =
  ≤-trans (*-monoʳ-≤ S (*-monoʳ-≤ 4 (*-monoʳ-≤ (2 ^ Ê) hu)))
  (≤-trans (≤-reflexive shape)
  (≤-trans (*-monoˡ-≤ (2 ^ Ê) (sq4≤2^ S 8≤S))
  (≤-trans (≤-reflexive (sym (^-distribˡ-+-* 2 S Ê)))
           (^-monoʳ-≤ 2 fit))))
  where
  Sq = S * S
  Cu = S * (S * S)
  Ê  = suc (Cu + Sq)
  1≤S : 1 ≤ S
  1≤S = ≤-trans (≤ᵇ⇒≤ 1 21 tt) 21≤S
  8≤S : 8 ≤ S
  8≤S = ≤-trans (≤ᵇ⇒≤ 8 21 tt) 21≤S
  14≤S : 14 ≤ S
  14≤S = ≤-trans (≤ᵇ⇒≤ 14 21 tt) 21≤S
  shape : S * (4 * (2 ^ Ê * S)) ≡ 4 * (S * S) * 2 ^ Ê
  shape = solve 2 (λ s q → s :* (con 4 :* (q :* s)) := con 4 :* (s :* s) :* q)
                refl S (2 ^ Ê)
  S≤Sq : S ≤ Sq
  S≤Sq = ≤-trans (≤-reflexive (sym (*-identityʳ S))) (*-monoʳ-≤ S 1≤S)
  Sq≤Cu : Sq ≤ Cu
  Sq≤Cu = ≤-trans (≤-reflexive (sym (*-identityʳ Sq)))
                  (≤-trans (*-monoʳ-≤ Sq 1≤S)
                           (≤-reflexive (solve 1 (λ s → s :* s :* s := s :* (s :* s))
                                               refl S)))
  S≤Cu : S ≤ Cu
  S≤Cu = ≤-trans S≤Sq Sq≤Cu
  1≤Cu : 1 ≤ Cu
  1≤Cu = ≤-trans 1≤S S≤Cu
  fshape : S + Ê ≡ Cu + (S + Sq + 1)
  fshape = solve 3 (λ s c q → s :+ (con 1 :+ (c :+ q)) := c :+ (s :+ q :+ con 1))
                 refl S Cu Sq
  threeEq : Cu + Cu + Cu ≡ 3 * Cu
  threeEq = solve 1 (λ c → c :+ c :+ c := con 3 :* c) refl Cu
  fourEq : Cu + 3 * Cu ≡ 4 * Cu
  fourEq = solve 1 (λ c → c :+ con 3 :* c := con 4 :* c) refl Cu
  fit : S + Ê ≤ 2 ^ S
  fit =
    ≤-trans (≤-reflexive fshape)
    (≤-trans (+-monoʳ-≤ Cu (≤-trans (+-mono-≤ (+-mono-≤ S≤Cu Sq≤Cu) 1≤Cu)
                                    (≤-reflexive threeEq)))
    (≤-trans (≤-reflexive fourEq) (cube4≤2^ S 14≤S)))

nestCap≤exp-suc : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id : ℕ) →
  Caps.cSize (capsAt e sl id) * (4 * capΦAt e sl id)
    ≤ 2 ^ (2 ^ Caps.cSize (capsAt e sl id)) →
  Caps.cSize (capsAt e sl (suc id)) * (4 * capΦAt e sl (suc id))
    ≤ 2 ^ (2 ^ Caps.cSize (capsAt e sl (suc id)))
nestCap≤exp-suc e sl id ih =
  subst (_≤ 2 ^ (2 ^ S′)) (sym stepOut)
    (nest-step-ℕ S S′ (S * P) (S′ * P′) (S′ + Ê′)
                 (nestCapAt e sl id) (nestIncAt e sl id)
                 (nestCapAt e sl (suc id))
                 (nestFacLog e sl id) (nestIncLog e sl id)
                 1≤Q hQ′ hC′ (nestInc≤exp e sl id)
                 (nestFac-room e sl id (S′ + Ê′) hA)
                 (subst (_≤ 2 ^ (2 ^ S)) stepIn ih))
  where
  S  = Caps.cSize (capsAt e sl id)
  S′ = Caps.cSize (capsAt e sl (suc id))
  Ê  = suc (S * (S * S) + S * S)
  Ê′ = suc (S′ * (S′ * S′) + S′ * S′)
  P  = 2 ^ Ê
  P′ = 2 ^ Ê′
  1≤S : 1 ≤ S
  1≤S = ≤-trans (s≤s z≤n) (2≤capsAt-size e sl id)
  1≤Q : 1 ≤ S * P
  1≤Q = *-mono-≤ 1≤S (m^n>0 2 Ê)
  hQ′ : S′ * P′ ≤ 2 ^ (S′ + Ê′)
  hQ′ = ≤-trans (*-monoˡ-≤ P′ (<⇒≤ (n<2^n S′)))
                (≤-reflexive (sym (^-distribˡ-+-* 2 S′ Ê′)))
  hA : 2 * (S′ + Ê′ + 3 + 2 ^ S) ≤ 2 ^ S′
  hA = capΦ-room-ℕ S′ (2 ^ S) (21≤capsAt-size e sl (suc id))
         (≤-trans (≤-trans (≤-reflexive (sym (*-identityʳ (2 ^ S))))
                           (*-monoʳ-≤ (2 ^ S) 1≤S))
                  (capsAt-exp-gain e sl id))
  stepIn : S * (4 * capΦAt e sl id) ≡ S * P * (4 * nestCapAt e sl id)
  stepIn = trans (cong (λ z → S * (4 * z)) (capΦAt-def e sl id))
                 (mash4 S P (nestCapAt e sl id))
  stepOut : S′ * (4 * capΦAt e sl (suc id))
              ≡ S′ * P′ * (4 * nestCapAt e sl (suc id))
  stepOut = trans (cong (λ z → S′ * (4 * z)) (capΦAt-def e sl (suc id)))
                  (mash4 S′ P′ (nestCapAt e sl (suc id)))
  hC′ : nestCapAt e sl (suc id)
          ≤ 2 ^ nestFacLog e sl id
              * (nestCapAt e sl id + nestIncAt e sl id)
  hC′ = ≤-trans (≤-reflexive (nestCapAt-suc e sl id))
                (*-monoˡ-≤ (nestCapAt e sl id + nestIncAt e sl id)
                           (nestFac≤exp e sl id))

nestCap≤exp : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id : ℕ) →
  Caps.cSize (capsAt e sl id) * (4 * capΦAt e sl id)
    ≤ 2 ^ (2 ^ Caps.cSize (capsAt e sl id))
nestCap≤exp e sl zero =
  subst (_≤ 2 ^ (2 ^ S)) (sym (cong (λ z → S * (4 * z)) (capΦAt-def e sl 0)))
    (capΦ-base-ℕ S (nestCapAt e sl 0) (21≤capsAt-size e sl 0) C≤S)
  where
  S = Caps.cSize (capsAt e sl 0)
  C≤S : nestCapAt e sl 0 ≤ S
  C≤S = ≤-trans (≤-reflexive (nestCapAt-0 e sl)) (nestUnit≤size e sl 0)
nestCap≤exp e sl (suc id) =
  nestCap≤exp-suc e sl id (nestCap≤exp e sl id)

-- AND THE CEILING'S SYNTAX IS PAID BY THE SIZE CAP, which is what lets
-- the leaf above be stated in caps alone.  The ceiling reads the
-- program's own size as a factor, and the caps recurrence carries the
-- base bound at every instant, so that factor sits under the size cap
-- with no run consulted; the `suc` beside the tripled cap is under a
-- fourth copy of it because the cap is at least one, being the wrap
-- unit at instant zero and nondecreasing after.
nestCap-sight≤exp : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id : ℕ) →
  suc (sizeᵉ e) * suc (3 * capΦAt e sl id)
    ≤ 2 ^ (2 ^ Caps.cSize (capsAt e sl id))
nestCap-sight≤exp e sl id =
  ≤-trans (*-mono-≤ 1+z≤S h4) (nestCap≤exp e sl id)
  where
  C = capΦAt e sl id
  1≤C : 1 ≤ C
  1≤C =
    subst (1 ≤_) (sym (capΦAt-def e sl id))
      (*-mono-≤ (m^n>0 2 (suc (Caps.cSize (capsAt e sl id)
                                 * (Caps.cSize (capsAt e sl id)
                                    * Caps.cSize (capsAt e sl id))
                               + Caps.cSize (capsAt e sl id)
                                 * Caps.cSize (capsAt e sl id))))
                (≤-trans (subst (1 ≤_) (sym (nestCapAt-0 e sl)) (s≤s z≤n))
                         (nestCap-mono₀ e sl id)))
  four : 4 * C ≡ C + 3 * C
  four = solve 1 (λ c → con 4 :* c := c :+ con 3 :* c) refl C
  h4 : suc (3 * C) ≤ 4 * C
  h4 = ≤-trans (+-monoˡ-≤ (3 * C) 1≤C) (≤-reflexive (sym four))
  1+z≤S : suc (sizeᵉ e) ≤ Caps.cSize (capsAt e sl id)
  1+z≤S = ≤-trans (≤-trans (n≤1+n (suc (sizeᵉ e))) (m≤m+n (2 + sizeᵉ e) _))
                  (capsAt-base-size e sl id)

-- AND THE CHARGE BESIDE IT IS THE WALK'S, which is what keeps the whole
-- ceiling at ONE instant.  A chain's growth is priced against the
-- program under the factor the path can still apply, and both halves
-- are readings of the size cap: the unit is under it and the factor is
-- two to its square, since every frame's size is under it and so is the
-- count of frames.  Two to a square sits under two to two-to-the-cap
-- with room for the tripling and the program's own size beside it,
-- which is the whole of why the ceiling still closes.
--
-- DEAD ROUTE: charging the walk the INCREMENT instead, which is what
--   the arms first carried by mirroring the entry burst.  The
--   increment's exponent reads the delivery at the NEXT instant and
--   the size there is already a blowup story above this instant's
--   fuel, so no reading of it fits under the exponential the fuel
--   supplies here.  That is the index constraint the cap's own step
--   lemma states, arriving at the consumer rather than at the step.

-- AND THIS IS THE WHOLE CEILING THE WALK'S SIDE GETS, WHICH IS WORTH
-- SAYING AS A NUMBER RATHER THAN AS A SHAPE.  Whatever the walk's
-- charge is written as, it is spent at the instant's own fuel, and the
-- fuel supplies two to two-to-the-size -- so an exponent under it may
-- reach two to the size and no further.  A threading frame's charge is
-- a power in the COUNT of values it is handed, so what the exponent
-- has to hold is that count times a size, and affording it asks the
-- count under two to the size.  A width cap is not: the width folds
-- through a power tower where the size steps geometrically, so the two
-- cross a few folds in and never come back.  The consequence is that
-- this ceiling, and not any statement about a frame, is what decides
-- whether the fold's arm on the depth face can be stated at all.
walk-sight≤exp : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id : ℕ) →
  suc (sizeᵉ e) * (3 * nestWalkAt e sl id)
    ≤ 2 ^ (2 ^ Caps.cSize (capsAt e sl id))
walk-sight≤exp e sl id =
  subst (λ z → suc (sizeᵉ e) * (3 * z) ≤ 2 ^ (2 ^ Caps.cSize (capsAt e sl id)))
        (sym (nestWalkAt-def e sl id))
        (≤-trans (*-mono-≤ hz (*-mono-≤ h3 (*-monoʳ-≤ (2 ^ E) hM)))
        (≤-trans (≤-reflexive collapse)
                 (^-monoʳ-≤ 2 expfit)))
  where
  S = Caps.cSize (capsAt e sl id)
  -- the cube the walk's charge now carries, named once so the two
  -- collapse equations and the fit below read the same expression
  C = S * (S * S)
  E = suc (C + C + (S * S + S * S))
  8≤S : 8 ≤ S
  8≤S = 8≤capsAt-size e sl id
  14≤S : 14 ≤ S
  14≤S = ≤-trans (≤ᵇ⇒≤ 14 21 tt) (21≤capsAt-size e sl id)
  1≤S : 1 ≤ S
  1≤S = ≤-trans (s≤s z≤n) 8≤S
  2≤S : 2 ≤ S
  2≤S = ≤-trans (s≤s (s≤s z≤n)) 8≤S
  S≤SS : S ≤ S * S
  S≤SS = ≤-trans (≤-reflexive (sym (*-identityʳ S))) (*-monoʳ-≤ S 1≤S)
  S≤2^S : S ≤ 2 ^ S
  S≤2^S = <⇒≤ (n<2^n S)
  2S≤2^S : 2 * S ≤ 2 ^ S
  2S≤2^S =
    ≤-trans (*-monoˡ-≤ S (≤ᵇ⇒≤ 2 4 tt))
            (≤-trans (*-monoʳ-≤ 4 S≤SS) (sq4≤2^ S 8≤S))
  SS≤2^S : S * S ≤ 2 ^ S
  SS≤2^S = ≤-trans (m≤n*m (S * S) 4) (sq4≤2^ S 8≤S)
  slSz : slotsSize sl ≤ S
  slSz = ≤-trans (m≤n+m (slotsSize sl) (2 + sizeᵉ e))
                 (capsAt-base-size e sl id)
  1+z≤S : suc (sizeᵉ e) ≤ S
  1+z≤S = ≤-trans (≤-trans (n≤1+n (suc (sizeᵉ e))) (m≤m+n (2 + sizeᵉ e) _))
                  (capsAt-base-size e sl id)
  hz : suc (sizeᵉ e) ≤ 2 ^ S
  hz = ≤-trans 1+z≤S S≤2^S
  h3 : 3 ≤ 2 ^ S
  h3 = ≤-trans (≤-trans (≤ᵇ⇒≤ 3 8 tt) 8≤S) S≤2^S
  -- THE UNIT, THE TWO SQUARES AND THE SIZE, four exponentials.  The
  -- squares are what the walk's own leaf costs, so the trailing factor
  -- carries them beside the unit rather than under it.
  quadEq : 2 ^ S + (2 ^ S + 2 ^ S) + 2 ^ S ≡ 2 ^ (2 + S)
  quadEq =
    trans (solve 1 (λ q → q :+ (q :+ q) :+ q := con 4 :* q) refl (2 ^ S))
          (sym (^-distribˡ-+-* 2 2 S))
  hA : nestUnit e sl + (S * S + S * S) + S ≤ 2 ^ (2 + S)
  hA =
    ≤-trans (+-mono-≤ (+-mono-≤ (≤-trans (nestUnit≤size e sl id) S≤2^S)
                                (+-mono-≤ SS≤2^S SS≤2^S))
                      S≤2^S)
            (≤-reflexive quadEq)
  -- AND THE TELESCOPE'S WRAP, three of them: the per-slot ceiling is one
  -- exponential times a size, the length is another size, and the
  -- summand outside is the third.
  wrapShape : S * (S * (2 ^ S * S)) ≡ 2 ^ S * (S * (S * S))
  wrapShape = solve 2 (λ s p → s :* (s :* (p :* s)) := p :* (s :* (s :* s)))
                    refl S (2 ^ S)
  3SEq : S + (S + S) ≡ 3 * S
  3SEq = solve 1 (λ s → s :+ (s :+ s) := con 3 :* s) refl S
  tripleEq : 2 ^ S * (2 ^ S * 2 ^ S) ≡ 2 ^ (3 * S)
  tripleEq =
    trans (cong (2 ^ S *_) (sym (^-distribˡ-+-* 2 S S)))
    (trans (sym (^-distribˡ-+-* 2 S (S + S)))
           (cong (2 ^_) 3SEq))
  hB : S * slotWrapSum sl ≤ 2 ^ (3 * S)
  hB =
    ≤-trans (*-monoʳ-≤ S (slotWrapSum≤size sl S slSz))
    (≤-trans (≤-reflexive wrapShape)
    (≤-trans (*-monoʳ-≤ (2 ^ S) (*-mono-≤ S≤2^S SS≤2^S))
             (≤-reflexive tripleEq)))
  dbl : 2 ^ (3 * S) + 2 ^ (3 * S) ≡ 2 ^ (1 + 3 * S)
  dbl = sym (2X≡X+X (2 ^ (3 * S)))
  2+S≤3S : 2 + S ≤ 3 * S
  2+S≤3S =
    ≤-trans (+-monoˡ-≤ S (≤-trans (≤ᵇ⇒≤ 2 8 tt) 8≤S))
    (≤-trans (≤-reflexive (solve 1 (λ a → a :+ a := con 2 :* a) refl S))
             (*-monoˡ-≤ S (≤ᵇ⇒≤ 2 3 tt)))
  hM : nestUnit e sl + (S * S + S * S) + S + S * slotWrapSum sl ≤ 2 ^ (1 + 3 * S)
  hM = ≤-trans (+-mono-≤ (≤-trans hA (^-monoʳ-≤ 2 2+S≤3S)) hB)
               (≤-reflexive dbl)
  collapse : 2 ^ S * (2 ^ S * (2 ^ E * 2 ^ (1 + 3 * S)))
               ≡ 2 ^ (S + (S + (E + (1 + 3 * S))))
  collapse =
    trans (cong (λ z → 2 ^ S * (2 ^ S * z))
                (sym (^-distribˡ-+-* 2 E (1 + 3 * S))))
    (trans (cong (2 ^ S *_)
                 (sym (^-distribˡ-+-* 2 S (E + (1 + 3 * S)))))
           (sym (^-distribˡ-+-* 2 S (S + (E + (1 + 3 * S))))))
  -- THE EXPONENT SUM IS A CUBE PLUS A SQUARE PLUS A LINE, and the
  -- three summands are each paid by one cube, which is what the four
  -- on offer covers.
  shapeL : S + (S + (E + (1 + 3 * S))) ≡ C + (C + (S * S + S * S + (5 * S + 2)))
  shapeL = solve 1 (λ a → a :+ (a :+ ((con 1 :+ (a :* (a :* a) :+ a :* (a :* a)
                                                  :+ (a :* a :+ a :* a)))
                                       :+ (con 1 :+ con 3 :* a)))
                            := a :* (a :* a)
                               :+ (a :* (a :* a)
                                   :+ (a :* a :+ a :* a :+ (con 5 :* a :+ con 2))))
                 refl S
  -- THE SQUARES ARE PAID BY ONE CUBE BETWEEN THEM, which is what the
  -- fourth on offer is for: two squares and the line all sit under a
  -- single cube once the size is past its floor, so the doubled walk
  -- exponent still lands inside the four this ceiling affords.
  6≤S : 6 ≤ S
  6≤S = ≤-trans (≤ᵇ⇒≤ 6 8 tt) 8≤S
  3≤S : 3 ≤ S
  3≤S = ≤-trans (≤ᵇ⇒≤ 3 8 tt) 8≤S
  sixEq : 5 * S + S ≡ 6 * S
  sixEq = solve 1 (λ a → con 5 :* a :+ a := con 6 :* a) refl S
  lin≤SS : 5 * S + 2 ≤ S * S
  lin≤SS =
    ≤-trans (+-monoʳ-≤ (5 * S) 2≤S)
    (≤-trans (≤-reflexive sixEq) (*-monoˡ-≤ S 6≤S))
  twoSq+lin≤C : S * S + S * S + (5 * S + 2) ≤ C
  twoSq+lin≤C =
    ≤-trans (+-monoʳ-≤ (S * S + S * S) lin≤SS)
    (≤-trans (≤-reflexive (solve 1 (λ a → a :* a :+ a :* a :+ a :* a
                                            := con 3 :* (a :* a)) refl S))
             (*-monoˡ-≤ (S * S) 3≤S))
  threeC : C + (C + C) ≡ 3 * C
  threeC = solve 1 (λ c → c :+ (c :+ c) := con 3 :* c) refl C
  expfit : S + (S + (E + (1 + 3 * S))) ≤ 2 ^ S
  expfit =
    ≤-trans (≤-reflexive shapeL)
    (≤-trans (+-monoʳ-≤ C (+-monoʳ-≤ C twoSq+lin≤C))
    (≤-trans (≤-reflexive threeC)
    (≤-trans (*-monoˡ-≤ C (≤ᵇ⇒≤ 3 4 tt)) (cube4≤2^ S 14≤S))))

-- THE SPLIT ITSELF IS RING ARITHMETIC: the ceiling's factor distributes
-- over the two halves of its store slot, so each half is priced by its
-- own leaf and neither has to be read at the other's index.
sight-split : ∀ (z C I : ℕ) →
  suc z * suc (3 * (C + I)) ≡ suc z * suc (3 * C) + suc z * (3 * I)
sight-split z C I =
  solve 3 (λ z′ c i →
             (con 1 :+ z′) :* (con 1 :+ con 3 :* (c :+ i))
               := (con 1 :+ z′) :* (con 1 :+ con 3 :* c)
                  :+ (con 1 :+ z′) :* (con 3 :* i))
          refl z C I

nestΦ-sight≤capsH : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id : ℕ) →
  suc (sizeᵉ e) * suc (3 * nestΦAt e sl id) ≤ capsH e sl id
nestΦ-sight≤capsH e sl id =
  ≤-trans (≤-reflexive
            (trans (cong (λ z → suc (sizeᵉ e) * suc (3 * z))
                         (nestΦAt-def e sl id))
                   (sight-split (sizeᵉ e) (capΦAt e sl id)
                                (nestWalkAt e sl id))))
          (≤-trans (+-mono-≤ (nestCap-sight≤exp e sl id)
                             (walk-sight≤exp e sl id))
                   (capsAt-exp2≤capsH e sl id))

-- THE GRANT AT THE VOCABULARY, WHICH IS WHERE EVERY READING IT TAKES
-- ALREADY LIVES.  A grant reads four numbers off the program and its
-- slot telescope -- the base size, the nesting unit, the descent depth
-- and the sync size -- and each of the four is a summand of the base
-- cap's size coordinate.  So one number bounds all four, and the whole
-- grant collapses onto a power of two whose exponent is a fixed
-- polynomial in that number and the burst width.
nestB-vocab : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ)
  (V W B m : ℕ) → sizeᵉ e ≤ V → nestUnit e ins ≤ V → B ≤ V → m ≤ V →
  nestB (sizeᵉ e) W (nestUnit e ins) B m
    ≤ 2 ^ (V * suc W * V + (V + suc V * V))
nestB-vocab e ins V W B m hz hu hB hm =
  ≤-trans (nestB≤pow (sizeᵉ e) W (nestUnit e ins) B m)
          (^-monoʳ-≤ 2 (+-mono-≤ (*-mono-≤ (*-monoˡ-≤ (suc W) hz) hm)
                                 (+-mono-≤ hB (*-mono-≤ (s≤s hm) hu))))

slotWrapB≤pow : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ)
  (V W : ℕ) → sizeᵉ e ≤ V → nestUnit e ins ≤ V → slotsSize ins ≤ V →
  (i : Fin n) →
  slotWrapB e ins W (ins i) ≤ 2 ^ (V * suc W * V + (V + suc V * V))
slotWrapB≤pow e ins V W hz hu hs i
  with ins i | ≤-trans (fᵢ≤sum-tab (λ j → slotSize (ins j)) i) hs
... | scripted _ | _  = z≤n
... | shared d   | hd =
  nestB-vocab e ins V W (nestDᵉ d) (syncSizeᵉ d) hz hu
              (≤-trans (nestDᵉ≤sizeᵉ d) hd) (≤-trans (syncSize≤sizeᵉ d) hd)

slotWrapBSum≤pow : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ)
  (V W : ℕ) → sizeᵉ e ≤ V → nestUnit e ins ≤ V → slotsSize ins ≤ V →
  slotWrapBSum e ins W ≤ V * 2 ^ (V * suc W * V + (V + suc V * V))
slotWrapBSum≤pow {n = n} e ins V W hz hu hs =
  ≤-trans (sum-tab-mono (λ i → slotWrapB e ins W (ins i)) (λ _ → 2 ^ EXP)
                        (slotWrapB≤pow e ins V W hz hu hs))
          (≤-trans (≤-reflexive (sum-tab-const {n} (2 ^ EXP)))
                   (*-monoˡ-≤ (2 ^ EXP) (≤-trans (n≤slotsSize ins) hs)))
  where
  EXP = V * suc W * V + (V + suc V * V)

-- AND THE ROOT'S WHOLE FIT IS TWO OF THEM, the descent's own and one
-- per slot -- so a length under the vocabulary turns the telescope's
-- sum into a square of it, and nothing else in the fit reads anything
-- the four numbers above do not already cover.
fit-root≤pow : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ)
  (V W : ℕ) → sizeᵉ e ≤ V → nestUnit e ins ≤ V → slotsSize ins ≤ V →
  n ≤ V →
  fitG e ins n W root e ≤ suc (V * V) * 2 ^ (V * suc W * V + (V + suc V * V))
fit-root≤pow e ins V W hz hu hs hn =
  +-mono-≤ (nestB-vocab e ins V W (nestDᵉ e) (syncSizeᵉ e) hz hu
              (≤-trans (nestDᵉ≤sizeᵉ e) hz) (≤-trans (syncSize≤sizeᵉ e) hz))
           (≤-trans (*-mono-≤ hn (slotWrapBSum≤pow e ins V W hz hu hs))
                    (≤-reflexive (sym (*-assoc V V (2 ^ EXP)))))
  where
  EXP = V * suc W * V + (V + suc V * V)

-- THE ENTRY'S SIGHTED CEILING UNDER TWO EXPONENTIALS OF THE
-- VOCABULARY, which is the whole ladder the bridge's root reading
-- stands on.  Everything the ceiling reads is a summand of the base
-- cap's SIZE coordinate and the burst width IS its WIDTH coordinate,
-- so the grant's exponent is a product of two numbers already on the
-- record rather than a quantity the comparison has to invent.  A
-- product of readings sits under a sum of their own exponentials,
-- which is what turns the polynomial into the single exponent a cap
-- can be compared with, and seven copies of one power is all the
-- collapse ever costs.
entry-fit≤pow : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  suc (sizeᵉ e) * suc (fitG e ins n (suc (entryCeil n ins e)) root e
                        + nestCapAt e ins 0 + nestUnit e ins)
    ≤ 2 ^ (2 ^ (4 + ((2 + sizeᵉ e + slotsSize ins + slotsClos ins)
                    + (2 + sizeᵉ e + slotsSize ins + slotsClos ins))
                  + suc (entryCeil n ins e)))
entry-fit≤pow {n = n} e ins =
  ≤-trans (*-mono-≤ hsz hinner)
          (≤-trans (≤-reflexive (sym (^-distribˡ-+-* 2 V (2 + (V + V) + EXP))))
                   (^-monoʳ-≤ 2 hexp))
  where
  V = 2 + sizeᵉ e + slotsSize ins + slotsClos ins
  W = suc (entryCeil n ins e)
  EXP = V * suc W * V + (V + suc V * V)
  R = 2 ^ EXP
  K = suc (V * V)
  P = 2 ^ V
  PW = 2 ^ W
  Q = P * P * PW

  hsucz : suc (sizeᵉ e) ≤ V
  hsucz = ≤-trans (≤-trans (n≤1+n (suc (sizeᵉ e)))
                           (m≤m+n (2 + sizeᵉ e) (slotsSize ins)))
                  (m≤m+n (2 + sizeᵉ e + slotsSize ins) (slotsClos ins))
  hV : sizeᵉ e ≤ V
  hV = ≤-trans (n≤1+n (sizeᵉ e)) hsucz
  1≤V : 1 ≤ V
  1≤V = ≤-trans (s≤s z≤n) hsucz
  hVP : V ≤ P
  hVP = <⇒≤ (n<2^n V)
  hsz : suc (sizeᵉ e) ≤ P
  hsz = ≤-trans hsucz hVP
  hsucVP : suc V ≤ P
  hsucVP = n<2^n V
  1≤P : 1 ≤ P
  1≤P = 1≤pow≤ 2 V (s≤s z≤n)
  1≤PW : 1 ≤ PW
  1≤PW = 1≤pow≤ 2 W (s≤s z≤n)
  1≤R : 1 ≤ R
  1≤R = 1≤pow≤ 2 EXP (s≤s z≤n)

  hs : slotsSize ins ≤ V
  hs = ≤-trans (m≤n+m (slotsSize ins) (2 + sizeᵉ e))
               (m≤m+n (2 + sizeᵉ e + slotsSize ins) (slotsClos ins))
  hn : n ≤ V
  hn = ≤-trans (n≤slotsSize ins) hs
  hu : nestUnit e ins ≤ V
  hu = ≤-trans (s≤s (+-mono-≤ (nestDᵉ≤sizeᵉ e) (slotsNestSum≤slotsSize ins)))
               (≤-trans (n≤1+n (suc (sizeᵉ e + slotsSize ins)))
                        (m≤m+n (2 + sizeᵉ e + slotsSize ins) (slotsClos ins)))
  hB : nestCapAt e ins 0 ≤ V
  hB = ≤-trans (≤-reflexive (nestCapAt-0 e ins)) hu

  -- the inner sum, collapsed onto one power
  hVV : V * V ≤ P * P
  hVV = *-mono-≤ hVP hVP
  hVVpow : V * V ≤ 2 ^ (V + V)
  hVVpow = ≤-trans hVV (≤-reflexive (sym (^-distribˡ-+-* 2 V V)))
  1≤VV : 1 ≤ 2 ^ (V + V)
  1≤VV = 1≤pow≤ 2 (V + V) (s≤s z≤n)
  hG : K + (V + V + 1) ≤ 2 ^ (2 + (V + V))
  hG = ≤-trans (+-mono-≤ (+-mono-≤ 1≤VV hVVpow)
                         (+-mono-≤ (<⇒≤ (n<2^n (V + V))) 1≤VV))
               (≤-trans (≤-reflexive (four (2 ^ (V + V))))
                        (≤-reflexive (sym (^-distribˡ-+-* 2 2 (V + V)))))
    where
    four : ∀ (x : ℕ) → x + x + (x + x) ≡ 4 * x
    four x = solve 1 (λ y → y :+ y :+ (y :+ y) := con 4 :* y) refl x

  hinner : suc (fitG e ins n W root e + nestCapAt e ins 0 + nestUnit e ins)
             ≤ 2 ^ (2 + (V + V) + EXP)
  hinner =
    ≤-trans (s≤s (+-mono-≤ (+-mono-≤ (fit-root≤pow e ins V W hV hu hs hn) hB) hu))
      (≤-trans (≤-reflexive shift)
        (≤-trans (+-monoʳ-≤ (K * R) lift)
          (≤-trans (≤-reflexive (sym (*-distribʳ-+ R K (V + V + 1))))
            (≤-trans (*-monoˡ-≤ R hG)
                     (≤-reflexive (sym (^-distribˡ-+-* 2 (2 + (V + V)) EXP)))))))
    where
    shift : suc (K * R + V + V) ≡ K * R + (V + V + 1)
    shift = solve 3 (λ a b c → con 1 :+ (a :+ b :+ c) := a :+ (b :+ c :+ con 1))
                  refl (K * R) V V
    lift : V + V + 1 ≤ (V + V + 1) * R
    lift = ≤-trans (≤-reflexive (sym (*-identityʳ (V + V + 1))))
                   (*-monoʳ-≤ (V + V + 1) 1≤R)

  -- and the exponent under the cap's own reading
  V≤Q : V ≤ Q
  V≤Q = ≤-trans hVP
          (≤-trans (≤-trans (≤-reflexive (sym (*-identityʳ P)))
                            (*-monoʳ-≤ P 1≤P))
                   (≤-trans (≤-reflexive (sym (*-identityʳ (P * P))))
                            (*-monoʳ-≤ (P * P) 1≤PW)))
  2≤Q : 2 ≤ Q
  2≤Q = ≤-trans (≤-trans (^-monoʳ-≤ 2 1≤V) (≤-reflexive refl)) (≤-trans hPQ ≤-refl)
    where
    hPQ : P ≤ Q
    hPQ = ≤-trans (≤-trans (≤-reflexive (sym (*-identityʳ P)))
                           (*-monoʳ-≤ P 1≤P))
                  (≤-trans (≤-reflexive (sym (*-identityʳ (P * P))))
                           (*-monoʳ-≤ (P * P) 1≤PW))
  hprod : V * suc W * V ≤ Q
  hprod = ≤-trans (*-mono-≤ (*-mono-≤ hVP (n<2^n W)) hVP)
                  (≤-reflexive swap)
    where
    swap : P * PW * P ≡ P * P * PW
    swap = solve 2 (λ a b → a :* b :* a := a :* a :* b) refl P PW
  hsucVV : suc V * V ≤ Q
  hsucVV = ≤-trans (*-mono-≤ hsucVP hVP)
             (≤-trans (≤-reflexive (sym (*-identityʳ (P * P))))
                      (*-monoʳ-≤ (P * P) 1≤PW))

  hexp : V + (2 + (V + V) + EXP) ≤ 2 ^ (4 + (V + V) + W)
  hexp =
    ≤-trans (+-mono-≤ V≤Q
              (+-mono-≤ (+-mono-≤ 2≤Q (+-mono-≤ V≤Q V≤Q))
                        (+-mono-≤ hprod (+-mono-≤ V≤Q hsucVV))))
      (≤-trans (≤-reflexive seven)
        (≤-trans (*-monoˡ-≤ Q {7} {16}
                    (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))
                 (≤-reflexive (sym sixteen))))
    where
    seven : Q + (Q + (Q + Q) + (Q + (Q + Q))) ≡ 7 * Q
    seven = solve 1 (λ q → q :+ (q :+ (q :+ q) :+ (q :+ (q :+ q))) := con 7 :* q)
                  refl Q
    sixteen : 2 ^ (4 + (V + V) + W) ≡ 16 * Q
    sixteen =
      trans (^-distribˡ-+-* 2 (4 + (V + V)) W)
        (trans (cong (_* PW)
                 (trans (^-distribˡ-+-* 2 4 (V + V))
                        (cong (16 *_) (^-distribˡ-+-* 2 V V))))
               (solve 2 (λ a b → con 16 :* a :* b := con 16 :* (a :* b))
                      refl (P * P) PW))
