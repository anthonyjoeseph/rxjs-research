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

open import Data.Nat using (ℕ; suc; _+_; _*_; _⊔_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; ≤-refl; ≤-reflexive; +-mono-≤;
  +-monoˡ-≤; +-monoʳ-≤; *-monoʳ-≤; +-comm; m≤m+n; m≤n+m; m≤m⊔n; m≤n⊔m; ⊔-lub;
  n≤1+n; ⊔-identityʳ)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (towerℕ)
open import Rx.Exp using (Ctx; Closed; Exp; Tm; sizeᵉ; sizeᵗ; sizeᵗˢ;
  input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ; concatAllᵉ; switchAllᵉ;
  exhaustAllᵉ; μᵉ; varᵉ; deferᵉ; varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ;
  inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ)
open import Rx.Slots using (Slots; slotsSize; shared; scripted)
open import Rx.Nest-Depth using (nestDᵉ; nestDᵗ; nestDᵗˢ)
open import Rx.Frame-Width using (entryCeil; pWᵉ; innWᵉ; outWᵉ; dWᵉ;
  slotsPW≤entryCeil; slotsIW≤entryCeil)
open import Rx.Evaluator using (capsBase; sched-init; st-init)

open import Verify-Budget-Sufficient.Measures using (k≤towerℕ; towerℕ-mono;
  sizeᵗ-pos)
open import Verify-Budget-Sufficient.Caps using (3T≤; tower-mul;
  iterFold-tower; 1≤towerℕ; 2≤towerℕ)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (SlotWid; Sub-[];
  slotsPW-lb; slotsIW-lb)
open import Verify-Budget-Sufficient.Caps-Face.Part2 using (monoᵉ; monoᴰᵉ;
  wid-iterFold)
open import Verify-Budget-Sufficient.Depth-Compositional using
  (storeNestMax; slotsNestSum)

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
-- THE TWO HALVES OF THE MEASURE.  The term half is a real body below;
-- the store half is still a leaf.  `S` is fixed at 2 inside — it is
-- the base `wid-iterFold` asks for and it never reaches the
-- conclusion, so carrying it as a parameter would say nothing.
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
-- THE LIST COMPANION CARRIES A SPARE `suc`, and that is forced
-- rather than slack: `sizeᵗˢ (y ∷ ys)` is `sizeᵗ y + sizeᵗˢ ys` with
-- no `suc` of its own, so the cons clause has no level of its own to
-- spend on its `+`.  It pays out of `sizeᵗ-pos` at the HEAD, which
-- is worth three levels — one for the cons, and the parent `ofᵉ`
-- redeems the carried `suc` against its own node.  The alternative,
-- a `1 ≤ sizeᵗˢ` lemma, does not exist in the tree and would have
-- to be stated for this one clause.
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
            (towerℕ-mono (hUp k (sizeᵗˢ ts) (sizeᵗˢ ts) ≤-refl))
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
    sum2H (k + 3 * sizeᵗ a) (k + 3 * sizeᵗ b) _
      (≤-trans 3k (m≤m+n k (3 * sizeᵗ a)))
      (nestD-towerᵗ k M 3k 1M MT sl w a)
      (nestD-towerᵗ k M 3k 1M MT sl w b)
      (hUp k (sizeᵗ a) (sizeᵗ a + sizeᵗ b) (m≤m+n (sizeᵗ a) (sizeᵗ b)))
      (hUp k (sizeᵗ b) (sizeᵗ a + sizeᵗ b) (m≤n+m (sizeᵗ b) (sizeᵗ a)))
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
    sum3H (k + 3 * sizeᵗ s) (k + 3 * sizeᵗ l) (k + 3 * sizeᵗ r) _
      (≤-trans 3k (m≤m+n k (3 * sizeᵗ s)))
      (nestD-towerᵗ k M 3k 1M MT sl w s)
      (nestD-towerᵗ k M 3k 1M MT sl w l)
      (nestD-towerᵗ k M 3k 1M MT sl w r)
      (hUp k (sizeᵗ s) _ (≤-trans (m≤m+n (sizeᵗ s) (sizeᵗ l))
                                  (m≤m+n (sizeᵗ s + sizeᵗ l) (sizeᵗ r))))
      (hUp k (sizeᵗ l) _ (≤-trans (m≤n+m (sizeᵗ l) (sizeᵗ s))
                                  (m≤m+n (sizeᵗ s + sizeᵗ l) (sizeᵗ r))))
      (hUp k (sizeᵗ r) _ (m≤n+m (sizeᵗ r) (sizeᵗ s + sizeᵗ l)))
  nestD-towerᵗ k M 3k 1M MT sl w (ifᵗ c a b) =
    sum3H (k + 3 * sizeᵗ c) (k + 3 * sizeᵗ a) (k + 3 * sizeᵗ b) _
      (≤-trans 3k (m≤m+n k (3 * sizeᵗ c)))
      (nestD-towerᵗ k M 3k 1M MT sl w c)
      (nestD-towerᵗ k M 3k 1M MT sl w a)
      (nestD-towerᵗ k M 3k 1M MT sl w b)
      (hUp k (sizeᵗ c) _ (≤-trans (m≤m+n (sizeᵗ c) (sizeᵗ a))
                                  (m≤m+n (sizeᵗ c + sizeᵗ a) (sizeᵗ b))))
      (hUp k (sizeᵗ a) _ (≤-trans (m≤n+m (sizeᵗ a) (sizeᵗ c))
                                  (m≤m+n (sizeᵗ c + sizeᵗ a) (sizeᵗ b))))
      (hUp k (sizeᵗ b) _ (m≤n+m (sizeᵗ b) (sizeᵗ c + sizeᵗ a)))

  nestD-towerᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (k M : ℕ) → 3 ≤ k → 1 ≤ M →
    M ≤ towerℕ k → (sl : Slots Γ) → SlotWid sl M →
    (ts : List (Tm Γ Δᵍ Δ Θ t)) →
    nestDᵗˢ sl ts ≤ towerℕ (suc (k + 3 * sizeᵗˢ ts))
  nestD-towerᵗˢ k M 3k 1M MT sl w []       = z≤n
  nestD-towerᵗˢ k M 3k 1M MT sl w (y ∷ ys) =
    sum2H (k + 3 * A) (suc (k + 3 * B)) _
      (≤-trans 3k (m≤m+n k (3 * A)))
      (nestD-towerᵗ  k M 3k 1M MT sl w y)
      (nestD-towerᵗˢ k M 3k 1M MT sl w ys)
      (s≤s (hIn k A (A + B) (m≤m+n A B)))
      (s≤s headPays)
    where
    A = sizeᵗ y
    B = sizeᵗˢ ys
    1≤3A : 1 ≤ 3 * A
    1≤3A = ≤-trans (s≤s z≤n) (*-monoʳ-≤ 3 (sizeᵗ-pos y))
    headPays : suc (k + 3 * B) ≤ k + 3 * (A + B)
    headPays =
      ≤-trans (≤-reflexive (+-comm 1 (k + 3 * B)))
      (≤-trans (+-monoʳ-≤ (k + 3 * B) 1≤3A)
               (≤-reflexive (solve 3 (λ a x y′ →
                  (a :+ con 3 :* y′) :+ con 3 :* x := a :+ con 3 :* (x :+ y′))
                 refl k A B)))

------------------------------------------------------------------
-- THE STORE HALF, still a leaf.
------------------------------------------------------------------

postulate
  -- THE STORE HALF, at the entry state, where the node table is empty
  -- and the whole store is the slot telescope.  A scripted slot pays
  -- nothing and a shared slot's summand is its def's size plus the term
  -- half at that def, so the count of nonzero summands is under
  -- `slotsSize sl` — which is the height this is stated at.
  --
  -- ITS SIBLING HALF IS NOW PROVEN, AND COVERS THE ARITHMETIC BUT NOT
  -- THE INDUCTION.  `nestD-tower` bounds the second summand of a shared
  -- slot at height `k + 3 * sizeᵉ d`, `k≤towerℕ` bounds the first at the
  -- same height, and the kit above adds them for one level — so the
  -- PER-SLOT bound is settled, at `suc (k + 3 * slotSize (sl i))`.
  -- What is not settled is the sum: this is an induction over
  -- `sum (tabulate …)` against `sum (tabulate slotSize)`, which is
  -- vector machinery and not the Exp/Tm recursion the sibling runs on.
  -- Each slot grants three levels and needs about two — one for its own
  -- `+` and one for the cons — so the budget is there; how to route it
  -- through a tabulate is the open decision, and it is why this stays
  -- DIFFICULTY rather than inheriting the sibling's shape.
  storeNest-tower : ∀ {n} {Γ : Ctx n} (k M : ℕ) → 3 ≤ k → 1 ≤ M →
    M ≤ towerℕ k → (sl : Slots Γ) → SlotWid sl M →
    slotsNestSum sl ≤ towerℕ (k + 3 * slotsSize sl)

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
                     (towerℕ-mono {K + 3 * L} {H}
                        (+-monoˡ-≤ (3 * L) (m≤m+n K (3 * S)))))
    where wid = entryCeil-slotWid ins e

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
