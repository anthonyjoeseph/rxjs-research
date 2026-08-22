------------------------------------------------------------------
-- THE DEPTH FACE'S TOWER, and the height it is stated at.
--
-- `nest-store≤capsH` (.Caps-Bridge) needs the depth measure under
-- `capsH e ins 0`, and the caps side of that is fully proven:
-- `tower-le-blowH k m` delivers `towerℕ k ≤ blowH m` for ANY k with
-- `suc k ≤ towerℕ m`, so the height is free and the depth side may
-- spend a FACTOR rather than a constant.  This module spends it at
-- `k = 3 * capsBase e ins`.
--
-- WHY A FACTOR AND NOT A CONSTANT, since a constant is what the first
-- statement asked for.  `nestDᵉ` multiplies by `outWᵉ` at every
-- `scanᵉ`; `wid-iterFold` bounds `outWᵉ` by `iterFold 2 (sizeᵉ e) M`
-- and `iterFold-tower` puts that at height `k + 2 * sizeᵉ e`; one more
-- tower level per product on top lands the induction near
-- `k + 3 * sizeᵉ e`.  `capsBase` carries `sizeᵉ e` ONCE, and nothing
-- relates its `entryCeil` term back to `sizeᵉ e` — its only two facts
-- bound SLOT widths by it.  Three times `capsBase` is what covers it.
--
-- WHAT MAKES THE WIDTH MACHINERY REACHABLE FROM HERE.  `wid-iterFold`
-- wants `SlotWid sl M`, and its only proven producer
-- (`slotsCaps?-slotWid`) is conditioned on `slotsCaps? B W sl ≡ true`
-- — a hypothesis this face does not have and must not acquire, since
-- adding one is a restatement and the unconditional form is not
-- refuted.  `entryCeil-slotWid` below is the unconditional producer:
-- the entry ceiling already dominates `slotsPW` and `slotsIW` for
-- every `e`, and those are the maxima a slot's own pW and innW sit
-- under.  It is the conditioned lemma's body with the side condition's
-- two bounds replaced by that pair of facts.
------------------------------------------------------------------
module Verify-Budget-Sufficient.Nest-Tower where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _⊔_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; ≤-refl; ≤-reflexive; +-mono-≤;
  +-monoˡ-≤; +-monoʳ-≤; *-monoʳ-≤; +-comm; +-identityʳ; m≤m+n; m≤n+m; m≤m⊔n;
  m≤n⊔m; ⊔-lub; n≤1+n; ⊔-identityʳ)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.List using (List; []; _∷_; tabulate)
open import Data.Nat.ListAction using (sum)
open import Data.Fin using (Fin)
import Data.Fin as Fin
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Rx.Prim using (towerℕ)
open import Rx.Exp using (Ctx; Closed; Exp; Tm; sizeᵉ; sizeᵗ; sizeᵗˢ;
  input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ; concatAllᵉ; switchAllᵉ;
  exhaustAllᵉ; μᵉ; varᵉ; deferᵉ; varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ;
  inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ)
open import Rx.Slots using (Slots; Slot; slotSize; slotsSize; shared; scripted)
open import Rx.Nest-Depth using (nestDᵉ; nestDᵗ; nestDᵗˢ)
open import Rx.Frame-Width using (entryCeil; pWᵉ; innWᵉ; outWᵉ; dWᵉ;
  slotsPW≤entryCeil; slotsIW≤entryCeil)
open import Rx.Evaluator using (capsBase; sched-init; st-init)

open import Verify-Budget-Sufficient.Measures using (k≤towerℕ; towerℕ-mono; sizeᵉ-pos; 1≤slotSize; n≤sum-tab)
open import Verify-Budget-Sufficient.Caps using (3T≤; tower-mul;
  iterFold-tower; 1≤towerℕ; 2≤towerℕ)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (SlotWid; Sub-[];
  slotsPW-lb; slotsIW-lb)
open import Verify-Budget-Sufficient.Caps-Face.Part2 using (monoᵉ; monoᴰᵉ;
  wid-iterFold)
open import Verify-Budget-Sufficient.Depth-Compositional using
  (storeNestMax; slotNest; slotsNestSum)

------------------------------------------------------------------
-- THE UNCONDITIONAL LEAF BOUND.
------------------------------------------------------------------

-- A slot's own parked and inner widths sit under the entry ceiling by
-- construction, so the leaf bound needs no side condition.  Same body
-- as `slotsCaps?-slotWid`: the fuel/visited descent (`monoᵉ`, `monoᴰᵉ`)
-- lifts what the `input` clause reads off the def up to the def's own
-- `pWᵉ`/`innWᵉ`, and the max-over-slots lemmas take it from there.  A
-- scripted slot presents 1, 1 and 0, which is what the `suc` is for.
--
-- THE TWO LOOKUPS RIDE THE `with`, not the branch, because
-- `with sl i` rewrites the GOAL and not the types of terms written
-- inside the branch — the same reason the conditioned twin carries its
-- side-condition lookup there.
entryCeil-slotWid : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (sl : Slots Γ)
  (e : Exp Γ Δᵍ Δ Θ t) → SlotWid sl (suc (entryCeil n sl e))
entryCeil-slotWid {n = suc m} sl e i
  with sl i | slotsPW-lb (suc m) sl i | slotsIW-lb (suc m) sl i
... | scripted _ | _  | _  = s≤s z≤n , s≤s z≤n , z≤n
... | shared d   | hp | hi =
    ≤-trans (proj₁ (mono d))
            (≤-trans (m≤m⊔n (outWᵉ (suc m) sl d) (dWᵉ (suc m) sl d)) pw′)
  , ≤-trans (proj₁ (proj₂ (mono d))) iw′
  , ≤-trans (monoᴰᵉ sl m (n≤1+n m) {i ∷ []} {[]} (Sub-[] {vs = i ∷ []}) d)
            (≤-trans (m≤n⊔m (outWᵉ (suc m) sl d) (dWᵉ (suc m) sl d)) pw′)
  where
  mono = λ dd → monoᵉ sl m (n≤1+n m) {i ∷ []} {[]} (Sub-[] {vs = i ∷ []}) dd
  pw : pWᵉ (suc m) sl d ≤ entryCeil (suc m) sl e
  pw = ≤-trans hp (slotsPW≤entryCeil (suc m) sl e)
  iw : innWᵉ (suc m) sl d ≤ entryCeil (suc m) sl e
  iw = ≤-trans hi (slotsIW≤entryCeil (suc m) sl e)
  pw′ : pWᵉ (suc m) sl d ≤ suc (entryCeil (suc m) sl e)
  pw′ = ≤-trans pw (n≤1+n (entryCeil (suc m) sl e))
  iw′ : innWᵉ (suc m) sl d ≤ suc (entryCeil (suc m) sl e)
  iw′ = ≤-trans iw (n≤1+n (entryCeil (suc m) sl e))

------------------------------------------------------------------
-- THE TWO HALVES OF THE MEASURE, both real bodies below.  `S` is
-- fixed at 2 inside — it is the base `wid-iterFold` asks for and it
-- never reaches the conclusion, so carrying it as a parameter would
-- say nothing.
------------------------------------------------------------------

------------------------------------------------------------------
-- THE ADDITION KIT.  Every clause of the measure is a sum, and each
-- summand arrives at ITS OWN height, so these take one height PER
-- SUMMAND and ask only for a `suc` of headroom above each.  A single
-- shared height would have been cheaper to state and does not work:
-- the `ofᵉ` list's cons clause gains no `suc` of its own, and pays
-- for its level out of the positivity of the head's `sizeᵗ` — which
-- is a fact about one summand and not about a maximum.
------------------------------------------------------------------

sum2H : ∀ (hx hy h : ℕ) → 3 ≤ hx → ∀ {x y} →
  x ≤ towerℕ hx → y ≤ towerℕ hy → suc hx ≤ h → suc hy ≤ h →
  x + y ≤ towerℕ h
sum2H hx hy h 3x xle yle sx sy =
  ≤-trans (+-mono-≤ (≤-trans xle (towerℕ-mono (m≤m⊔n hx hy)))
                    (≤-trans yle (towerℕ-mono (m≤n⊔m hx hy))))
  (≤-trans (m≤m+n (T + T) T)
  (≤-trans (≤-reflexive (solve 1 (λ t → (t :+ t) :+ t := con 3 :* t) refl T))
  (≤-trans (3T≤ (hx ⊔ hy) (≤-trans 3x (m≤m⊔n hx hy)))
           (towerℕ-mono (⊔-lub sx sy)))))
  where T = towerℕ (hx ⊔ hy)

sum3H : ∀ (hx hy hz h : ℕ) → 3 ≤ hx → ∀ {x y z} →
  x ≤ towerℕ hx → y ≤ towerℕ hy → z ≤ towerℕ hz →
  suc hx ≤ h → suc hy ≤ h → suc hz ≤ h →
  x + y + z ≤ towerℕ h
sum3H hx hy hz h 3x xle yle zle sx sy sz =
  ≤-trans (+-mono-≤ (+-mono-≤ (≤-trans xle (towerℕ-mono ax))
                              (≤-trans yle (towerℕ-mono ay)))
                    (≤-trans zle (towerℕ-mono az)))
  (≤-trans (≤-reflexive (solve 1 (λ t → (t :+ t) :+ t := con 3 :* t) refl T))
  (≤-trans (3T≤ H (≤-trans 3x ax))
           (towerℕ-mono (⊔-lub (⊔-lub sx sy) sz))))
  where
  H = hx ⊔ hy ⊔ hz
  T = towerℕ H
  ax : hx ≤ H
  ax = ≤-trans (m≤m⊔n hx hy) (m≤m⊔n (hx ⊔ hy) hz)
  ay : hy ≤ H
  ay = ≤-trans (m≤n⊔m hx hy) (m≤m⊔n (hx ⊔ hy) hz)
  az : hz ≤ H
  az = m≤n⊔m (hx ⊔ hy) hz

sucH : ∀ (hx h : ℕ) → 3 ≤ hx → ∀ {x} →
  x ≤ towerℕ hx → suc hx ≤ h → suc x ≤ towerℕ h
sucH hx h 3x xle sx = sum2H hx hx h 3x (1≤towerℕ hx) xle sx sx

-- A node's three levels, spending one.  `hIn` spends none, for the
-- clauses where the measure does not grow at all.
hUp : ∀ (k a s : ℕ) → a ≤ s → suc (k + 3 * a) ≤ k + 3 * suc s
hUp k a s a≤s =
  ≤-trans (s≤s (+-monoʳ-≤ k (*-monoʳ-≤ 3 a≤s)))
  (≤-trans (m≤m+n (suc (k + 3 * s)) 2)
           (≤-reflexive (solve 2 (λ n x → (con 1 :+ (n :+ con 3 :* x)) :+ con 2
                                       := n :+ con 3 :* (con 1 :+ x))
                               refl k s)))

hIn : ∀ (k a s : ℕ) → a ≤ s → k + 3 * a ≤ k + 3 * s
hIn k a s a≤s = +-monoʳ-≤ k (*-monoʳ-≤ 3 a≤s)

1≤3x : ∀ (x : ℕ) → 1 ≤ x → 1 ≤ 3 * x
1≤3x x 1x = ≤-trans (s≤s z≤n) (*-monoʳ-≤ 3 1x)

-- A POSITIVE SUMMAND PAYS FOR THE `+` IT IS ADDED BY, which is the
-- only reason any of these clauses close: a sum's two heights are
-- both the FULL height, so the level has to come from a size that
-- cannot be zero rather than from headroom in the statement.
payL : ∀ (k a b : ℕ) → 1 ≤ 3 * a → suc (k + 3 * b) ≤ k + 3 * (a + b)
payL k a b 1≤3a =
  ≤-trans (≤-reflexive (+-comm 1 (k + 3 * b)))
  (≤-trans (+-monoʳ-≤ (k + 3 * b) 1≤3a)
           (≤-reflexive (solve 3 (λ n x y → (n :+ con 3 :* y) :+ con 3 :* x
                                         := n :+ con 3 :* (x :+ y))
                               refl k a b)))

payR : ∀ (k a b : ℕ) → 1 ≤ 3 * b → suc (k + 3 * a) ≤ k + 3 * (a + b)
payR k a b 1≤3b =
  ≤-trans (payL k b a 1≤3b)
          (≤-reflexive (solve 3 (λ n x y → n :+ con 3 :* (y :+ x)
                                        := n :+ con 3 :* (x :+ y))
                              refl k a b))

------------------------------------------------------------------
-- THE TERM HALF.  Induction on the syntax, at a height chosen so
-- that EVERY CLAUSE HAS A LEVEL LEFT OVER: `3 * suc x` is
-- `3 + 3 * x`, so each node grants three levels and no clause needs
-- more than two.  `scanᵉ` is the clause that needs both — its
-- product goes through `wid-iterFold` at base 2 composed with
-- `iterFold-tower`, which lands `outWᵉ` at height `k + 2 * sizeᵉ e`,
-- strictly inside the `3 * sizeᵉ e` this is stated at, and then the
-- three-way sum costs the second.
--
-- AND THE CLAUSES THAT ARE A `⊔` SPEND NOTHING AT ALL, which is what
-- retired the level accounting the list companion used to need.  A max
-- of two things each under `towerℕ h` is under `towerℕ h`, so `⊔-lub`
-- over two `hIn` widenings closes those clauses with no node to pay
-- from — the list companion no longer carries a spare `suc`, and `ofᵉ`
-- no longer redeems one.  `caseᵗ` is the one mixed clause left, its
-- scrutinee a genuine summand because its value is substituted into the
-- branch that runs, and its two branches a `⊔` because only one does.
------------------------------------------------------------------

mutual
  nestD-tower : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (k M : ℕ) → 3 ≤ k → 1 ≤ M →
    M ≤ towerℕ k → (sl : Slots Γ) → SlotWid sl M → (e : Exp Γ Δᵍ Δ Θ t) →
    nestDᵉ sl e ≤ towerℕ (k + 3 * sizeᵉ e)
  nestD-tower k M 3k 1M MT sl w (input i)  = z≤n
  nestD-tower k M 3k 1M MT sl w emptyᵉ     = z≤n
  nestD-tower k M 3k 1M MT sl w (varᵉ x)   = z≤n
  nestD-tower k M 3k 1M MT sl w (ofᵉ ts)   =
    ≤-trans (nestD-towerᵗˢ k M 3k 1M MT sl w ts)
            (towerℕ-mono (hIn k (sizeᵗˢ ts) (suc (sizeᵗˢ ts)) (n≤1+n _)))
  nestD-tower k M 3k 1M MT sl w (mapᵉ f e) =
    sum2H (k + 3 * sizeᵗ f) (k + 3 * sizeᵉ e) _
      (≤-trans 3k (m≤m+n k (3 * sizeᵗ f)))
      (nestD-towerᵗ k M 3k 1M MT sl w f)
      (nestD-tower  k M 3k 1M MT sl w e)
      (hUp k (sizeᵗ f) (sizeᵗ f + sizeᵉ e) (m≤m+n (sizeᵗ f) (sizeᵉ e)))
      (hUp k (sizeᵉ e) (sizeᵗ f + sizeᵉ e) (m≤n+m (sizeᵉ e) (sizeᵗ f)))
  nestD-tower k M 3k 1M MT sl w (takeᵉ c e) =
    ≤-trans (nestD-tower k M 3k 1M MT sl w e)
            (towerℕ-mono (hIn k (sizeᵉ e) (suc (sizeᵗ c + sizeᵉ e))
               (≤-trans (m≤n+m (sizeᵉ e) (sizeᵗ c)) (n≤1+n _))))
  nestD-tower k M 3k 1M MT sl w (μᵉ e) =
    ≤-trans (nestD-tower k M 3k 1M MT sl w e)
            (towerℕ-mono (hIn k (sizeᵉ e) (suc (sizeᵉ e)) (n≤1+n _)))
  nestD-tower k M 3k 1M MT sl w (deferᵉ e) =
    ≤-trans (nestD-tower k M 3k 1M MT sl w e)
            (towerℕ-mono (hIn k (sizeᵉ e) (suc (sizeᵉ e)) (n≤1+n _)))
  nestD-tower k M 3k 1M MT sl w (mergeAllᵉ e) =
    sucH (k + 3 * sizeᵉ e) _ (≤-trans 3k (m≤m+n k (3 * sizeᵉ e)))
      (nestD-tower k M 3k 1M MT sl w e) (hUp k (sizeᵉ e) (sizeᵉ e) ≤-refl)
  nestD-tower k M 3k 1M MT sl w (concatAllᵉ e) =
    sucH (k + 3 * sizeᵉ e) _ (≤-trans 3k (m≤m+n k (3 * sizeᵉ e)))
      (nestD-tower k M 3k 1M MT sl w e) (hUp k (sizeᵉ e) (sizeᵉ e) ≤-refl)
  nestD-tower k M 3k 1M MT sl w (switchAllᵉ e) =
    sucH (k + 3 * sizeᵉ e) _ (≤-trans 3k (m≤m+n k (3 * sizeᵉ e)))
      (nestD-tower k M 3k 1M MT sl w e) (hUp k (sizeᵉ e) (sizeᵉ e) ≤-refl)
  nestD-tower k M 3k 1M MT sl w (exhaustAllᵉ e) =
    sucH (k + 3 * sizeᵉ e) _ (≤-trans 3k (m≤m+n k (3 * sizeᵉ e)))
      (nestD-tower k M 3k 1M MT sl w e) (hUp k (sizeᵉ e) (sizeᵉ e) ≤-refl)
  nestD-tower {n = n} k M 3k 1M MT sl w (scanᵉ f z e) =
    sum3H (k + 3 * Sz) (suc m₀) (k + 3 * Se) _
      (≤-trans 3k (m≤m+n k (3 * Sz)))
      (nestD-towerᵗ k M 3k 1M MT sl w z)
      mid
      (nestD-tower k M 3k 1M MT sl w e)
      (hUp k Sz (Sf + Sz + Se)
         (≤-trans (m≤n+m Sz Sf) (m≤m+n (Sf + Sz) Se)))
      midUp
      (hUp k Se (Sf + Sz + Se) (m≤n+m Se (Sf + Sz)))
    where
    Sf = sizeᵗ f
    Sz = sizeᵗ z
    Se = sizeᵉ e
    m₀ = k + 2 * Se + 3 * Sf
    3m₀ : 3 ≤ m₀
    3m₀ = ≤-trans 3k (≤-trans (m≤m+n k (2 * Se)) (m≤m+n (k + 2 * Se) (3 * Sf)))
    outW≤ : outWᵉ n sl e ≤ towerℕ (k + 2 * Se)
    outW≤ = ≤-trans (proj₁ (wid-iterFold 2 M (s≤s (s≤s z≤n)) 1M sl w e))
                    (iterFold-tower k 2 M Se 3k
                       (2≤towerℕ k (≤-trans (s≤s z≤n) 3k)) MT)
    mid : outWᵉ n sl e * nestDᵗ sl f ≤ towerℕ (suc m₀)
    mid = tower-mul m₀ _ _ 3m₀
            (≤-trans outW≤ (towerℕ-mono (m≤m+n (k + 2 * Se) (3 * Sf))))
            (≤-trans (nestD-towerᵗ k M 3k 1M MT sl w f)
                     (towerℕ-mono (+-monoˡ-≤ (3 * Sf) (m≤m+n k (2 * Se)))))
    midUp : suc (suc m₀) ≤ k + 3 * suc (Sf + Sz + Se)
    midUp = ≤-trans (m≤m+n (suc (suc m₀)) (suc (3 * Sz + Se)))
                    (≤-reflexive (solve 4 (λ a x y u →
                       (con 2 :+ ((a :+ con 2 :* u) :+ con 3 :* x))
                         :+ (con 1 :+ (con 3 :* y :+ u))
                       := a :+ con 3 :* (con 1 :+ ((x :+ y) :+ u)))
                      refl k Sf Sz Se))

  nestD-towerᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (k M : ℕ) → 3 ≤ k → 1 ≤ M →
    M ≤ towerℕ k → (sl : Slots Γ) → SlotWid sl M → (f : Tm Γ Δᵍ Δ Θ t) →
    nestDᵗ sl f ≤ towerℕ (k + 3 * sizeᵗ f)
  nestD-towerᵗ k M 3k 1M MT sl w (varᵗ x)  = z≤n
  nestD-towerᵗ k M 3k 1M MT sl w unit̂      = z≤n
  nestD-towerᵗ k M 3k 1M MT sl w (bool̂ _)  = z≤n
  nestD-towerᵗ k M 3k 1M MT sl w (nat̂ _)   = z≤n
  nestD-towerᵗ k M 3k 1M MT sl w (pairᵗ a b) =
    ⊔-lub (≤-trans (nestD-towerᵗ k M 3k 1M MT sl w a)
                   (towerℕ-mono (hIn k (sizeᵗ a) (suc (sizeᵗ a + sizeᵗ b))
                      (≤-trans (m≤m+n (sizeᵗ a) (sizeᵗ b)) (n≤1+n _)))))
          (≤-trans (nestD-towerᵗ k M 3k 1M MT sl w b)
                   (towerℕ-mono (hIn k (sizeᵗ b) (suc (sizeᵗ a + sizeᵗ b))
                      (≤-trans (m≤n+m (sizeᵗ b) (sizeᵗ a)) (n≤1+n _)))))
  nestD-towerᵗ k M 3k 1M MT sl w (fstᵗ p) =
    ≤-trans (nestD-towerᵗ k M 3k 1M MT sl w p)
            (towerℕ-mono (hIn k (sizeᵗ p) (suc (sizeᵗ p)) (n≤1+n _)))
  nestD-towerᵗ k M 3k 1M MT sl w (sndᵗ p) =
    ≤-trans (nestD-towerᵗ k M 3k 1M MT sl w p)
            (towerℕ-mono (hIn k (sizeᵗ p) (suc (sizeᵗ p)) (n≤1+n _)))
  nestD-towerᵗ k M 3k 1M MT sl w (inlᵗ a) =
    ≤-trans (nestD-towerᵗ k M 3k 1M MT sl w a)
            (towerℕ-mono (hIn k (sizeᵗ a) (suc (sizeᵗ a)) (n≤1+n _)))
  nestD-towerᵗ k M 3k 1M MT sl w (inrᵗ a) =
    ≤-trans (nestD-towerᵗ k M 3k 1M MT sl w a)
            (towerℕ-mono (hIn k (sizeᵗ a) (suc (sizeᵗ a)) (n≤1+n _)))
  nestD-towerᵗ k M 3k 1M MT sl w (primᵗ _ a) =
    ≤-trans (nestD-towerᵗ k M 3k 1M MT sl w a)
            (towerℕ-mono (hIn k (sizeᵗ a) (suc (sizeᵗ a)) (n≤1+n _)))
  nestD-towerᵗ k M 3k 1M MT sl w (strmᵗ e) =
    ≤-trans (nestD-tower k M 3k 1M MT sl w e)
            (towerℕ-mono (hIn k (sizeᵉ e) (suc (sizeᵉ e)) (n≤1+n _)))
  nestD-towerᵗ k M 3k 1M MT sl w (caseᵗ s l r) =
    sum2H (k + 3 * sizeᵗ s) (k + 3 * (sizeᵗ l + sizeᵗ r)) _
      (≤-trans 3k (m≤m+n k (3 * sizeᵗ s)))
      (nestD-towerᵗ k M 3k 1M MT sl w s)
      (⊔-lub (≤-trans (nestD-towerᵗ k M 3k 1M MT sl w l)
                      (towerℕ-mono (hIn k (sizeᵗ l) (sizeᵗ l + sizeᵗ r)
                         (m≤m+n (sizeᵗ l) (sizeᵗ r)))))
             (≤-trans (nestD-towerᵗ k M 3k 1M MT sl w r)
                      (towerℕ-mono (hIn k (sizeᵗ r) (sizeᵗ l + sizeᵗ r)
                         (m≤n+m (sizeᵗ r) (sizeᵗ l))))))
      (hUp k (sizeᵗ s) _ (≤-trans (m≤m+n (sizeᵗ s) (sizeᵗ l))
                                  (m≤m+n (sizeᵗ s + sizeᵗ l) (sizeᵗ r))))
      (hUp k (sizeᵗ l + sizeᵗ r) _
         (+-mono-≤ (m≤n+m (sizeᵗ l) (sizeᵗ s)) ≤-refl))
  nestD-towerᵗ k M 3k 1M MT sl w (ifᵗ c a b) =
    ⊔-lub (⊔-lub (arm c (≤-trans (m≤m+n (sizeᵗ c) (sizeᵗ a))
                                 (m≤m+n (sizeᵗ c + sizeᵗ a) (sizeᵗ b))))
                 (arm a (≤-trans (m≤n+m (sizeᵗ a) (sizeᵗ c))
                                 (m≤m+n (sizeᵗ c + sizeᵗ a) (sizeᵗ b)))))
          (arm b (m≤n+m (sizeᵗ b) (sizeᵗ c + sizeᵗ a)))
    where
    S = sizeᵗ c + sizeᵗ a + sizeᵗ b
    arm : ∀ {t′} (x : Tm _ _ _ _ t′) → sizeᵗ x ≤ S →
      nestDᵗ sl x ≤ towerℕ (k + 3 * suc S)
    arm x le = ≤-trans (nestD-towerᵗ k M 3k 1M MT sl w x)
                       (towerℕ-mono (hIn k (sizeᵗ x) (suc S)
                          (≤-trans le (n≤1+n S))))

  nestD-towerᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (k M : ℕ) → 3 ≤ k → 1 ≤ M →
    M ≤ towerℕ k → (sl : Slots Γ) → SlotWid sl M →
    (ts : List (Tm Γ Δᵍ Δ Θ t)) →
    nestDᵗˢ sl ts ≤ towerℕ (k + 3 * sizeᵗˢ ts)
  nestD-towerᵗˢ k M 3k 1M MT sl w []       = z≤n
  nestD-towerᵗˢ k M 3k 1M MT sl w (y ∷ ys) =
    ⊔-lub (≤-trans (nestD-towerᵗ  k M 3k 1M MT sl w y)
                   (towerℕ-mono (hIn k A (A + B) (m≤m+n A B))))
          (≤-trans (nestD-towerᵗˢ k M 3k 1M MT sl w ys)
                   (towerℕ-mono (hIn k B (A + B) (m≤n+m B A))))
    where
    A = sizeᵗ y
    B = sizeᵗˢ ys

------------------------------------------------------------------
-- THE STORE HALF.  The level accounting is per-SLOT rather than
-- per-node: `slotSize` is at least 1, so each slot grants three
-- levels, and a shared slot spends two — one for the `+` inside its
-- own summand and one for the cons that adds it to the rest.
--
-- THE SPARE `suc` IN THE CONCLUSION IS FORCED, not slack, and the
-- one-slot telescope is the whole argument: a shared slot's summand
-- is `sizeᵉ d + nestDᵉ sl d`, and BOTH sides already sit at the full
-- `k + 3 * sizeᵉ d` — the term half is stated exactly there and
-- `k≤towerℕ` puts the size no lower — so no routing brings the
-- per-slot bound below `suc (k + 3 * slotSize s)`, and at one slot
-- that bound IS the statement.  The assembly pays for it out of
-- `3 * sizeᵉ e`, which is at least 3.
------------------------------------------------------------------

-- ONE SUMMAND PER SLOT, each arriving at its own height.  The
-- one-slot case is its own clause and not a degenerate instance of
-- the cons: the cons is paid for by the TAIL being nonempty, and at
-- one slot the tail is `sum []`, which is 0 and pays nothing.  There
-- is nothing to pay for there either, since `x + 0` adds no level.
tower-sum-tab : ∀ {m} (k : ℕ) → 3 ≤ k → (f g : Fin m → ℕ) →
  (∀ i → 1 ≤ g i) → (∀ i → f i ≤ towerℕ (suc (k + 3 * g i))) →
  sum (tabulate f) ≤ towerℕ (suc (k + 3 * sum (tabulate g)))
tower-sum-tab {zero}          k 3k f g 1g hf = z≤n
tower-sum-tab {suc zero}      k 3k f g 1g hf =
  ≤-trans (≤-reflexive (+-identityʳ (f Fin.zero)))
  (≤-trans (hf Fin.zero)
           (towerℕ-mono (s≤s (hIn k (g Fin.zero) (g Fin.zero + 0)
              (≤-reflexive (sym (+-identityʳ (g Fin.zero))))))))
tower-sum-tab {suc (suc m)} k 3k f g 1g hf =
  sum2H (suc (k + 3 * A)) (suc (k + 3 * B)) _
    (≤-trans 3k (≤-trans (m≤m+n k (3 * A)) (n≤1+n (k + 3 * A))))
    (hf Fin.zero)
    (tower-sum-tab k 3k (λ i → f (Fin.suc i)) (λ i → g (Fin.suc i))
       (λ i → 1g (Fin.suc i)) (λ i → hf (Fin.suc i)))
    (s≤s (payR k A B (1≤3x B (≤-trans (s≤s z≤n)
             (n≤sum-tab (λ i → g (Fin.suc i)) (λ i → 1g (Fin.suc i)))))))
    (s≤s (payL k A B (1≤3x A (1g Fin.zero))))
  where
  A = g Fin.zero
  B = sum (tabulate (λ i → g (Fin.suc i)))

-- The per-slot bound.  A scripted slot pays nothing; a shared slot's
-- ONE summand is the term half at that def, so this is `nestD-tower`
-- with a level to spare.  It used to add the def's SIZE as a second
-- summand and needed `sum2H` to combine two heights; the slot measure
-- pays only nesting now, and the spare `suc` — which the store half of
-- the assembly wants for its own reasons — is pure slack here.
slotNest-tower : ∀ {n} {Γ : Ctx n} {j t} (k M : ℕ) → 3 ≤ k → 1 ≤ M →
  M ≤ towerℕ k → (sl : Slots Γ) → SlotWid sl M → (s : Slot Γ j t) →
  slotNest sl s ≤ towerℕ (suc (k + 3 * slotSize s))
slotNest-tower k M 3k 1M MT sl w (scripted i) = z≤n
slotNest-tower k M 3k 1M MT sl w (shared d) =
  ≤-trans (nestD-tower k M 3k 1M MT sl w d)
          (towerℕ-mono (n≤1+n (k + 3 * sizeᵉ d)))

storeNest-tower : ∀ {n} {Γ : Ctx n} (k M : ℕ) → 3 ≤ k → 1 ≤ M →
  M ≤ towerℕ k → (sl : Slots Γ) → SlotWid sl M →
  slotsNestSum sl ≤ towerℕ (suc (k + 3 * slotsSize sl))
storeNest-tower {n = n} k M 3k 1M MT sl w =
  tower-sum-tab {m = n} k 3k (λ i → slotNest sl (sl i)) (λ i → slotSize (sl i))
    (λ i → 1≤slotSize (sl i))
    (λ i → slotNest-tower k M 3k 1M MT sl w (sl i))

------------------------------------------------------------------
-- THE ASSEMBLY.  Three bounds at one height, `3T≤` to add them, and
-- `towerℕ-mono` to land on `3 * capsBase`.  The height is
-- `(4 + E) + 3 * S + 3 * L`, so each half's own height is a PREFIX of
-- it and no reassociation is needed to spend either.
------------------------------------------------------------------

nestD-le-tower : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  sizeᵉ e + nestDᵉ ins e + 0
    + storeNestMax (sched-init e ins) (st-init e)
    ≤ towerℕ (3 * capsBase e ins)
nestD-le-tower {n = n} e ins =
  ≤-trans (+-mono-≤ (+-mono-≤ (+-mono-≤ sizeLe nestLe) ≤-refl) storeLe)
  (≤-trans (≤-reflexive (solve 1 (λ x → ((x :+ x) :+ con 0) :+ x := con 3 :* x)
                               refl T))
  (≤-trans (3T≤ H 3≤H) (towerℕ-mono {suc H} {3 * capsBase e ins} fits)))
  where
  S = sizeᵉ e
  L = slotsSize ins
  E = entryCeil n ins e
  M = suc E
  K = 4 + E
  H = K + 3 * S + 3 * L
  T = towerℕ H

  3≤K : 3 ≤ K
  3≤K = s≤s (s≤s (s≤s z≤n))

  M≤TK : M ≤ towerℕ K
  M≤TK = ≤-trans (k≤towerℕ M) (towerℕ-mono {M} {K} (s≤s (m≤n+m E 3)))

  3≤H : 3 ≤ H
  3≤H = ≤-trans 3≤K (≤-trans (m≤m+n K (3 * S)) (m≤m+n (K + 3 * S) (3 * L)))

  nestLe : nestDᵉ ins e ≤ T
  nestLe = ≤-trans (nestD-tower K M 3≤K (s≤s z≤n) M≤TK ins wid e)
                   (towerℕ-mono {K + 3 * S} {H} (m≤m+n (K + 3 * S) (3 * L)))
    where wid = entryCeil-slotWid ins e

  storeLe : storeNestMax (sched-init e ins) (st-init e) ≤ T
  storeLe = ≤-trans (≤-reflexive (⊔-identityʳ (slotsNestSum ins)))
            (≤-trans (storeNest-tower K M 3≤K (s≤s z≤n) M≤TK ins wid)
                     (towerℕ-mono {suc (K + 3 * L)} {H} fitsL))
    where
    wid = entryCeil-slotWid ins e
    -- `sizeᵉ e` is at least 1, so the term half's three levels cover
    -- the store half's spare one with two to spare.
    fitsL : suc (K + 3 * L) ≤ H
    fitsL = ≤-trans (payL K S L (1≤3x S (sizeᵉ-pos e)))
                    (≤-reflexive (solve 3 (λ n x y →
                       n :+ con 3 :* (x :+ y) := (n :+ con 3 :* x) :+ con 3 :* y)
                      refl K S L))

  sizeLe : S ≤ T
  sizeLe = ≤-trans (k≤towerℕ S) (towerℕ-mono {S} {H} S≤H)
    where
    S≤H : S ≤ H
    S≤H = ≤-trans (m≤m+n S (S + (S + 0)))
          (≤-trans (m≤n+m (3 * S) K) (m≤m+n (K + 3 * S) (3 * L)))

  -- suc H plus its own slack IS 3 * capsBase, which is the one place
  -- the two shapes have to be reconciled
  fits : suc H ≤ 3 * capsBase e ins
  fits = ≤-trans (m≤m+n (suc H) (7 + 2 * E)) (≤-reflexive eq)
    where
    eq : suc H + (7 + 2 * E) ≡ 3 * capsBase e ins
    eq = solve 3 (λ s l x →
           (con 1 :+ (((con 4 :+ x) :+ con 3 :* s) :+ con 3 :* l))
             :+ (con 7 :+ con 2 :* x)
           := con 3 :* ((con 3 :+ (s :+ l)) :+ (con 1 :+ x)))
         refl S L E
