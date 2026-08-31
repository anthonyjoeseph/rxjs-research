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
  +-mono-≤; *-distribʳ-+; ^-*-assoc; *-comm; +-comm; ≤-pred; m^n>0)
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
open import Rx.Exp       using (Ctx; Closed; sizeᵉ)
open import Verify-Budget-Sufficient.Nest-Cap using (nestU; nestU-def)
open import Verify-Budget-Sufficient.Deliver-Measure using
  (nestDᵉ≤sizeᵉ)
open import Verify-Budget-Sufficient.Fan-Caps using
  (delSize; delSq; delSq-def; delSize-exp)
open import Verify-Budget-Sufficient.Nest-Store using
  (nestCapAt; nestFacAt; nestFacAt-def; nest-inflate; realWidAt; realWidAt-def; nestIncAt;
  nestIncAt-def; nestBurstAt; nestUnit; slotsNestSum; nestCapAt-0; nestCap-mono₀; slotNest;
  nestBurstAt-def; nestCapAt-suc)
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
  (1≤capsAt-reg; 1≤pow≤; 2≤capsAt-size; 8≤capsAt-size; B2-cReg≤cSize; Caps; capsAt;
  capsAt-base-size; capsAt-size-mono; capsAt-wid<size; capsH; capsAt-exp-gain; size≤sizeCount;
  sizeCount; frameBlowup; iterSize-pow; size-lower; capsAt-exp2≤capsH)
open import Verify-Budget-Sufficient.Measures using
  (n<2^n; sq≤2^; sum-tab-mono; 2X≡X+X; 1≤pow)
-- the nesting measure the subscribe budget descends on, and the frame
-- row that supplies it.  Re-exported, so the clique names one module
-- the depth mirror: `depthInner` is the fuel `thruOuter-face-core`'s
-- new hypothesis ranges over (see below, ~6307).  The rest of the family
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
abstract
  nestWalkAt : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
    (id : ℕ) → ℕ
  nestWalkAt e sl id =
    2 ^ (Caps.cSize (capsAt e sl id) * Caps.cSize (capsAt e sl id))
      * (nestUnit e sl + Caps.cSize (capsAt e sl id))

  nestWalkAt-def : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
    (id : ℕ) →
    nestWalkAt e sl id
      ≡ 2 ^ (Caps.cSize (capsAt e sl id) * Caps.cSize (capsAt e sl id))
          * (nestUnit e sl + Caps.cSize (capsAt e sl id))
  nestWalkAt-def _ _ _ = refl

  unit+size≤nestWalkAt : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
    (id : ℕ) →
    nestUnit e sl + Caps.cSize (capsAt e sl id) ≤ nestWalkAt e sl id
  unit+size≤nestWalkAt e sl id =
    nest-inflate (2 ^ (Caps.cSize (capsAt e sl id) * Caps.cSize (capsAt e sl id)))
                 (nestUnit e sl + Caps.cSize (capsAt e sl id))
                 (m^n>0 2 (Caps.cSize (capsAt e sl id) * Caps.cSize (capsAt e sl id)))

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

-- FOUR SQUARES UNDER THE EXPONENTIAL, which is where the base case's
-- room comes from and why the size floor is eight rather than six.
sq4≤2^ : ∀ (S : ℕ) → 8 ≤ S → 4 * (S * S) ≤ 2 ^ S
sq4≤2^ (suc (suc k)) (s≤s (s≤s 6≤k)) =
  ≤-trans (*-monoʳ-≤ 4 (sq≤2^ k 6≤k))
          (≤-reflexive (sym (^-distribˡ-+-* 2 2 k)))

-- THE STEP'S ARITHMETIC, OVER BARE NUMBERS, and it is a body rather
-- than a leaf.  Nothing about caps survives here: a cap that steps by
-- multiplying an exponential onto a sum fits two exponentials of the
-- next size exactly when that exponent, the increment's own exponent,
-- the previous budget and the next size all fit ONE.  Stating it over
-- numerals is what makes the step instantiable at all -- both sides of
-- the caps-indexed form sit on a recurrence that does not terminate
-- natively, so the statement it came from could not be reached by any
-- row.
nest-step-ℕ : ∀ (S S′ C I C′ L M : ℕ) → 1 ≤ S →
  C′ ≤ 2 ^ L * (C + I) →
  I ≤ 2 ^ M →
  S′ + 3 + (2 ^ S + M) + L ≤ 2 ^ S′ →
  S * (4 * C) ≤ 2 ^ (2 ^ S) →
  S′ * (4 * C′) ≤ 2 ^ (2 ^ S′)
nest-step-ℕ S S′ C I C′ L M 1≤S hC′ hI hroom ih =
  ≤-trans (*-mono-≤ (<⇒≤ (n<2^n S′)) (*-monoʳ-≤ 4 hC′E))
          (≤-trans (≤-reflexive (sym collect)) (^-monoʳ-≤ 2 hroom′))
  where
  K = 2 ^ S + M
  C≤4C : C ≤ 4 * C
  C≤4C = ≤-trans (≤-reflexive (sym (*-identityˡ C)))
                 (*-monoˡ-≤ C {1} {4} (s≤s z≤n))
  4C≤S4C : 4 * C ≤ S * (4 * C)
  4C≤S4C = ≤-trans (≤-reflexive (sym (*-identityˡ (4 * C))))
                   (*-monoˡ-≤ (4 * C) 1≤S)
  C≤ : C ≤ 2 ^ K
  C≤ = ≤-trans (≤-trans C≤4C 4C≤S4C)
               (≤-trans ih (^-monoʳ-≤ 2 (m≤m+n (2 ^ S) M)))
  I≤ : I ≤ 2 ^ K
  I≤ = ≤-trans hI (^-monoʳ-≤ 2 (m≤n+m M (2 ^ S)))
  CI≤ : C + I ≤ 2 ^ suc K
  CI≤ = ≤-trans (+-mono-≤ C≤ I≤) (≤-reflexive (sym (2X≡X+X (2 ^ K))))
  hC′E : C′ ≤ 2 ^ L * 2 ^ suc K
  hC′E = ≤-trans hC′ (*-monoʳ-≤ (2 ^ L) CI≤)
  collect : 2 ^ (S′ + (2 + (L + suc K))) ≡ 2 ^ S′ * (4 * (2 ^ L * 2 ^ suc K))
  collect = trans (^-distribˡ-+-* 2 S′ (2 + (L + suc K)))
                  (cong (2 ^ S′ *_)
                    (trans (^-distribˡ-+-* 2 2 (L + suc K))
                           (cong (4 *_) (^-distribˡ-+-* 2 L (suc K)))))
  reshape : S′ + (2 + (L + suc K)) ≡ S′ + 3 + K + L
  reshape = solve 3 (λ s l k → s :+ (con 2 :+ (l :+ (con 1 :+ k)))
                                 := s :+ con 3 :+ k :+ l)
                  refl S′ L K
  hroom′ : S′ + (2 + (L + suc K)) ≤ 2 ^ S′
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
burst≤size′ e sl id =
  ≤-trans (≤-reflexive (nestBurstAt-def e sl id)) (capsAt-wid<size e sl id)

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

-- THE CONSTANT PART OF THE ROOM: twice a size and three more sits
-- under two to that size, once the size is at least six.  The square
-- lemma does it -- a successor squared is already above a linear term
-- with four to spare.
lin≤2^ : ∀ (m : ℕ) → 6 ≤ m → 2 * suc m + 3 ≤ 2 ^ m
lin≤2^ m 6≤m =
  ≤-trans (≤-reflexive lhs)
  (≤-trans (+-monoʳ-≤ (2 * m + 4) 1≤mm)
  (≤-trans (≤-reflexive (sym rhs)) (sq≤2^ m 6≤m)))
  where
  lhs : 2 * suc m + 3 ≡ 2 * m + 4 + 1
  lhs = solve 1 (λ x → con 2 :* (con 1 :+ x) :+ con 3
                    := con 2 :* x :+ con 4 :+ con 1)
              refl m
  rhs : (2 + m) * (2 + m) ≡ 2 * m + 4 + m * (2 + m)
  rhs = solve 1 (λ x → (con 2 :+ x) :* (con 2 :+ x)
                    := con 2 :* x :+ con 4 :+ x :* (con 2 :+ x))
              refl m
  1≤mm : 1 ≤ m * (2 + m)
  1≤mm = *-mono-≤ (≤-trans (≤ᵇ⇒≤ 1 6 tt) 6≤m) (s≤s z≤n)

-- THE ROOM ITSELF, and it is three numbers now.  The budget is two to
-- the next size; the next size and its bit length are named
-- separately, because what has to be paid for is the exponent TIMES
-- that length, and the hypothesis says the next size covers it with
-- four to spare.  The two halves are then each under half the budget:
-- the constant part by the square lemma, the two powers because the
-- length was bought.
room-gen : ∀ (E S′ K b : ℕ) → 7 ≤ S′ → E ≤ S′ → suc S′ ≤ 2 ^ b →
  K * b + 4 ≤ S′ →
  S′ + 3 + (E + suc S′ ^ K) + suc S′ ^ K ≤ 2 ^ S′
room-gen E (suc S″) K b (s≤s 6≤S″) hE hB hK =
  ≤-trans (+-monoˡ-≤ P (+-monoʳ-≤ (suc S″ + 3) (+-monoˡ-≤ P hE)))
  (≤-trans (≤-reflexive regroup)
  (≤-trans (+-mono-≤ (lin≤2^ S″ 6≤S″) twoP)
           (≤-reflexive (sym (2X≡X+X (2 ^ S″))))))
  where
  P : ℕ
  P = suc (suc S″) ^ K
  regroup : suc S″ + 3 + (suc S″ + P) + P ≡ 2 * suc S″ + 3 + (P + P)
  regroup = solve 2 (λ x p → (con 1 :+ x) :+ con 3 :+ ((con 1 :+ x) :+ p) :+ p
                          := con 2 :* (con 1 :+ x) :+ con 3 :+ (p :+ p))
                  refl S″ P
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
  (id : ℕ) →
  Caps.cSize (capsAt e sl (suc id)) + 3
    + (2 ^ Caps.cSize (capsAt e sl id) + nestIncLog e sl id)
    + nestFacLog e sl id
    ≤ 2 ^ Caps.cSize (capsAt e sl (suc id))
nestFac-room {n = n} e sl id =
  ≤-trans (+-mono-≤ (+-monoʳ-≤ (Caps.cSize (capsAt e sl (suc id)) + 3)
                      (+-monoʳ-≤ (2 ^ Caps.cSize (capsAt e sl id))
                                 (nestIncLog≤pow e sl id)))
                    (nestFacLog≤pow e sl id))
          (room-gen (2 ^ Caps.cSize (capsAt e sl id))
                    (Caps.cSize (capsAt e sl (suc id)))
                    (6 * n + 9)
                    (Caps.cSize (capsAt e sl id) * J
                      + Caps.cSize (capsAt e sl id) + 1)
                    (≤-trans (≤ᵇ⇒≤ 7 8 tt) (8≤capsAt-size e sl (suc id)))
                    (≤-trans (≤-trans (≤-reflexive (sym (*-identityʳ _)))
                                      (*-monoʳ-≤ (2 ^ Caps.cSize (capsAt e sl id))
                                                 (≤-trans (s≤s z≤n)
                                                   (2≤capsAt-size e sl id))))
                             (capsAt-exp-gain e sl id))
                    (capsAt-size-upper e sl id)
                    (≤-trans (room-arith (Caps.cSize (capsAt e sl id)) J (6 * n + 9)
                                (8≤capsAt-size e sl id)
                                (size≤sizeCount (capsAt e sl id) (capsH e sl id)
                                  (2≤capsAt-size e sl id) (1≤capsAt-reg e sl id))
                                (+-monoˡ-≤ 9 (*-monoʳ-≤ 6 (n≤capsAt-size e sl id))))
                             (capsAt-size-lower e sl id)))
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
nestCap≤exp-suc : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id : ℕ) →
  Caps.cSize (capsAt e sl id) * (4 * nestCapAt e sl id)
    ≤ 2 ^ (2 ^ Caps.cSize (capsAt e sl id)) →
  Caps.cSize (capsAt e sl (suc id)) * (4 * nestCapAt e sl (suc id))
    ≤ 2 ^ (2 ^ Caps.cSize (capsAt e sl (suc id)))
nestCap≤exp-suc e sl id ih =
  nest-step-ℕ (Caps.cSize (capsAt e sl id))
              (Caps.cSize (capsAt e sl (suc id)))
              (nestCapAt e sl id) (nestIncAt e sl id)
              (nestCapAt e sl (suc id))
              (nestFacLog e sl id) (nestIncLog e sl id)
              (≤-trans (s≤s z≤n) (2≤capsAt-size e sl id))
              hC′ (nestInc≤exp e sl id) (nestFac-room e sl id) ih
  where
  hC′ : nestCapAt e sl (suc id)
          ≤ 2 ^ nestFacLog e sl id
              * (nestCapAt e sl id + nestIncAt e sl id)
  hC′ = ≤-trans (≤-reflexive (nestCapAt-suc e sl id))
                (*-monoˡ-≤ (nestCapAt e sl id + nestIncAt e sl id)
                           (nestFac≤exp e sl id))

nestCap≤exp : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id : ℕ) →
  Caps.cSize (capsAt e sl id) * (4 * nestCapAt e sl id)
    ≤ 2 ^ (2 ^ Caps.cSize (capsAt e sl id))
nestCap≤exp e sl zero =
  ≤-trans (*-monoʳ-≤ S (*-monoʳ-≤ 4 C≤S))
          (≤-trans (≤-reflexive shape)
                   (≤-trans (sq4≤2^ S (8≤capsAt-size e sl 0))
                            (^-monoʳ-≤ 2 (<⇒≤ (n<2^n S)))))
  where
  S = Caps.cSize (capsAt e sl 0)
  shape : S * (4 * S) ≡ 4 * (S * S)
  shape = solve 1 (λ s → s :* (con 4 :* s) := con 4 :* (s :* s)) refl S
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
  suc (sizeᵉ e) * suc (3 * nestCapAt e sl id)
    ≤ 2 ^ (2 ^ Caps.cSize (capsAt e sl id))
nestCap-sight≤exp e sl id =
  ≤-trans (*-mono-≤ 1+z≤S h4) (nestCap≤exp e sl id)
  where
  C = nestCapAt e sl id
  1≤C : 1 ≤ C
  1≤C = ≤-trans (subst (1 ≤_) (sym (nestCapAt-0 e sl)) (s≤s z≤n))
                (nestCap-mono₀ e sl id)
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
walk-sight≤exp : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id : ℕ) →
  suc (sizeᵉ e) * (3 * nestWalkAt e sl id)
    ≤ 2 ^ (2 ^ Caps.cSize (capsAt e sl id))
walk-sight≤exp e sl id =
  subst (λ z → suc (sizeᵉ e) * (3 * z) ≤ 2 ^ (2 ^ Caps.cSize (capsAt e sl id)))
        (sym (nestWalkAt-def e sl id)) (
  ≤-trans (*-mono-≤ 1+z≤S (*-monoʳ-≤ 3 (*-monoʳ-≤ E unit2S)))
  (≤-trans (≤-reflexive shape)
  (≤-trans (*-monoˡ-≤ E six≤2^)
  (≤-trans (≤-reflexive (sym (^-distribˡ-+-* 2 (1 + S) (S * S))))
           (^-monoʳ-≤ 2 exp≤)))))
  where
  S = Caps.cSize (capsAt e sl id)
  E = 2 ^ (S * S)
  8≤S : 8 ≤ S
  8≤S = 8≤capsAt-size e sl id
  1≤S : 1 ≤ S
  1≤S = ≤-trans (s≤s z≤n) 8≤S
  S≤SS : S ≤ S * S
  S≤SS = ≤-trans (≤-reflexive (sym (*-identityʳ S))) (*-monoʳ-≤ S 1≤S)
  1≤SS : 1 ≤ S * S
  1≤SS = ≤-trans 1≤S S≤SS
  1+z≤S : suc (sizeᵉ e) ≤ S
  1+z≤S = ≤-trans (≤-trans (n≤1+n (suc (sizeᵉ e))) (m≤m+n (2 + sizeᵉ e) _))
                  (capsAt-base-size e sl id)
  unit2S : nestUnit e sl + S ≤ 2 * S
  unit2S = ≤-trans (+-monoˡ-≤ S (nestUnit≤size e sl id))
                   (≤-reflexive (solve 1 (λ s → s :+ s := con 2 :* s) refl S))
  shape : S * (3 * (E * (2 * S))) ≡ 6 * (S * S) * E
  shape = solve 2 (λ s ee → s :* (con 3 :* (ee :* (con 2 :* s)))
                              := con 6 :* (s :* s) :* ee) refl S E
  six≤2^ : 6 * (S * S) ≤ 2 ^ (1 + S)
  six≤2^ =
    ≤-trans (*-monoˡ-≤ (S * S) (≤ᵇ⇒≤ 6 8 tt))
    (≤-trans (≤-reflexive (solve 1 (λ x → con 8 :* x := con 2 :* (con 4 :* x))
                                 refl (S * S)))
             (*-monoʳ-≤ 2 (sq4≤2^ S 8≤S)))
  exp≤ : 1 + S + S * S ≤ 2 ^ S
  exp≤ =
    ≤-trans (+-monoˡ-≤ (S * S) (+-mono-≤ 1≤SS S≤SS))
    (≤-trans (≤-reflexive (solve 1 (λ x → x :+ x :+ x := con 3 :* x)
                                 refl (S * S)))
    (≤-trans (*-monoˡ-≤ (S * S) (≤ᵇ⇒≤ 3 4 tt))
             (sq4≤2^ S 8≤S)))

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

nestCap-inc-sight≤capsH : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id : ℕ) →
  suc (sizeᵉ e) * suc (3 * (nestCapAt e sl id + (nestWalkAt e sl id)))
    ≤ capsH e sl id
nestCap-inc-sight≤capsH e sl id =
  ≤-trans (≤-reflexive (sight-split (sizeᵉ e) (nestCapAt e sl id)
                                    (nestWalkAt e sl id)))
          (≤-trans (+-mono-≤ (nestCap-sight≤exp e sl id)
                             (walk-sight≤exp e sl id))
                   (capsAt-exp2≤capsH e sl id))

