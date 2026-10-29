{-# OPTIONS --guardedness #-}

-- A COLD TIMELINE KEEPS THE INVARIANT.  Its rows lie one plain label below
-- a burst's root: the subscription itself, or a timer's root
-- `ix T ∷ sub e ∷ []` for `e` the previous burst's end, at a tick past
-- it.  Each root lies in the world, so each row does, and none lies below
-- another.  The rows run in order, each after the one before, so a
-- position holds one event and nothing follows the end.
module denotation.EmissionSet.Laws.ColdInv where

open import Data.Bool.Properties using (T-≡)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; _++_; [_])
open import Data.List.Properties using (++-conicalˡ; ∷ʳ-injectiveˡ; ∷ʳ-injectiveʳ)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; +-suc; +-monoʳ-≤; m≤m+n; m<m+n)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import denotation.MonotonicList.Events using (Pos; Label; ix; sub; last; Time; tick; From; done; quiet; at; Frame; emit; stall; close;
  module Frame∞; module From∞; Timeline; timelineAt; <ᵖ-ix; <ᵖ-part; ix-<)
open import denotation.MonotonicList using (frames; burst; start)
open import denotation.EmissionSet using (end; _≺_; _≼_; InE; at-out; at-skip; at-end; on-out; on-skip; coldᵀ)
open import denotation.EmissionSet.Laws.Modulus using (≺→≼; ≼-refl; ≺-≼-≺)
open import denotation.EmissionSet.Laws.Worlds using (Plain; plain-ix; plain-last; plain-sub; W; W⁼; step; timer; here; inW; Real; real-snoc; InvD;
  world-after; ⊑-≼; ⊑-snoc; ext≢; snoc≢[])

private
  -- A reachable position before a timer's later tick.
  before-timer : ∀ e {T} ys → Real e → tick e < T → e ≺ (ix T ∷ ys)
  before-timer (ix a ∷ es) {T} ys _ lt = Equivalence.from T-≡ (<ᵖ-part [] {ix a} {ix T} es ys (ix-< lt))
  before-timer []          ys ()
  before-timer (sub _ ∷ _) ys ()
  before-timer (last ∷ _)  ys ()

  tick-snoc : ∀ r {l} → Real r → tick (r ++ [ l ]) ≡ tick r
  tick-snoc (ix _ ∷ _) _ = refl
  tick-snoc []          ()
  tick-snoc (sub _ ∷ _) ()
  tick-snoc (last ∷ _)  ()

  slot : ∀ r i → (r ++ [ ix i ]) ≺ (r ++ [ ix (suc i) ])
  slot r i = Equivalence.from T-≡ (<ᵖ-part r [] [] (<ᵖ-ix i))

  slot-last : ∀ r i → (r ++ [ ix i ]) ≺ (r ++ [ last ])
  slot-last r i = Equivalence.from T-≡ (<ᵖ-part r [] [] refl)

  step≼ : ∀ a b {y} → a ≺ b → b ≼ y → a ≼ y
  step≼ a b {y} ab by = ≺→≼ {a} {y} (≺-≼-≺ {a} {b} {y} ab by)

  module CI {A : Set} (H : Pos → Set) (p : Pos) where
    -- A burst's root: the subscription, or a timer's.
    Root : Pos → Set
    Root r = W⁼ H p r × Real r × (r ≡ p ⊎ Σ ℕ λ T → Σ Pos λ e → r ≡ ix T ∷ sub e ∷ [])

    Row : Pos → Set
    Row y = Σ Pos λ r → Σ Label λ l → Root r × Plain l × y ≡ r ++ [ l ]

    -- The next frame lies past the end before it.
    FrOk : ∀ {t} → Time → Pos → From A t → Set
    FrOk τ e (at t′ _ _) = tick e < τ + t′
    FrOk τ e done        = ⊤
    FrOk τ e quiet       = ⊤

    close-ok : ∀ {τ t} r → Real r → tick r ≤ τ + t → (m : From A (suc t)) → FrOk τ (r ++ [ last ]) m
    close-ok         r rr le done          = tt
    close-ok         r rr le quiet         = tt
    close-ok {τ} {t} r rr le (at t′ le′ _) =
      subst (_< τ + t′) (sym (tick-snoc r rr)) (≤-trans (s≤s le) (subst (_≤ τ + t′) (+-suc τ t) (+-monoʳ-≤ τ le′)))

    timer-real : ∀ τ {t′} e → Real e → tick e < τ + t′ → Real (ix (τ + t′) ∷ sub e ∷ [])
    timer-real τ e re lt = re , before-timer e (sub e ∷ []) re lt , tt

    mutual
      row-b : ∀ {t y e′} τ r i (b : Frame A t) → Root r → tick r ≤ τ + t → InE (burst τ r i b) y e′ → Row y
      row-b τ r i (emit a k) R le at-out      = r , ix i , R , plain-ix , refl
      row-b τ r i (emit a k) R le (on-out x)  = row-b τ r (suc i) k R le x
      row-b τ r i (stall k)  R le at-skip     = r , ix i , R , plain-ix , refl
      row-b τ r i (stall k)  R le (on-skip x) = row-b τ r (suc i) (Frame∞.force k) R le x
      row-b τ r i (close k)  R le at-skip     = r , ix i , R , plain-ix , refl
      row-b τ r i (close k)  R le (on-skip x) = row-f τ r (From∞.force k) R (close-ok r (proj₁ (proj₂ R)) le (From∞.force k)) x

      row-f : ∀ {t y e′} τ r (m : From A t) → Root r → FrOk τ (r ++ [ last ]) m → InE (frames τ (r ++ [ last ]) m) y e′ → Row y
      row-f τ r done          R _  at-end = r , last , R , plain-last , refl
      row-f τ r quiet         R _  ()
      row-f τ r (at t′ _ b) (w , rr , _) ok x =
        row-b τ (ix (τ + t′) ∷ sub (r ++ [ last ]) ∷ []) 0 b
          (inW (timer (τ + t′) (inW (step w plain-last))) , timer-real τ (r ++ [ last ]) (real-snoc r plain-last rr) ok , inj₂ (_ , _ , refl))
          ≤-refl x

    -- Every row lies at or after the stream's first.
    mutual
      lb-b : ∀ {t y e′} τ r i (b : Frame A t) → Real r → tick r ≤ τ + t → InE (burst τ r i b) y e′ → (r ++ [ ix i ]) ≼ y
      lb-b τ r i (emit a k) rr le at-out      = ≼-refl {r ++ [ ix i ]}
      lb-b {y = y} τ r i (emit a k) rr le (on-out x)  = step≼ (r ++ [ ix i ]) (r ++ [ ix (suc i) ]) {y} (slot r i) (lb-b τ r (suc i) k rr le x)
      lb-b τ r i (stall k)  rr le at-skip     = ≼-refl {r ++ [ ix i ]}
      lb-b {y = y} τ r i (stall k)  rr le (on-skip x) = step≼ (r ++ [ ix i ]) (r ++ [ ix (suc i) ]) {y} (slot r i) (lb-b τ r (suc i) (Frame∞.force k) rr le x)
      lb-b τ r i (close k)  rr le at-skip     = ≼-refl {r ++ [ ix i ]}
      lb-b {y = y} τ r i (close k)  rr le (on-skip x) =
        step≼ (r ++ [ ix i ]) (r ++ [ last ]) {y} (slot-last r i) (lb-f τ (r ++ [ last ]) (From∞.force k) (real-snoc r plain-last rr) (close-ok r rr le (From∞.force k)) x)

      lb-f : ∀ {t y e′} τ e (m : From A t) → Real e → FrOk τ e m → InE (frames τ e m) y e′ → e ≼ y
      lb-f τ e done        re _  at-end = ≼-refl {e}
      lb-f τ e quiet       re _  ()
      lb-f {y = y} τ e (at t′ _ b) re ok x =
        step≼ e (ix (τ + t′) ∷ sub e ∷ ix 0 ∷ []) {y} (before-timer e (sub e ∷ ix 0 ∷ []) re ok) (lb-b τ (ix (τ + t′) ∷ sub e ∷ []) 0 b (timer-real τ e re ok) ≤-refl x)

    -- One event at a position.
    mutual
      fu-b : ∀ {t y e₁ e₂} τ r i (b : Frame A t) → Real r → tick r ≤ τ + t → InE (burst τ r i b) y e₁ → InE (burst τ r i b) y e₂ → e₁ ≡ e₂
      fu-b τ r i (emit a k) rr le at-out      at-out       = refl
      fu-b τ r i (emit a k) rr le at-out      (on-out x′)  = ⊥-elim (lb-b τ r (suc i) k rr le x′ (slot r i))
      fu-b τ r i (emit a k) rr le (on-out x)  at-out       = ⊥-elim (lb-b τ r (suc i) k rr le x (slot r i))
      fu-b τ r i (emit a k) rr le (on-out x)  (on-out x′)  = fu-b τ r (suc i) k rr le x x′
      fu-b τ r i (stall k)  rr le at-skip     at-skip      = refl
      fu-b τ r i (stall k)  rr le at-skip     (on-skip x′) = ⊥-elim (lb-b τ r (suc i) (Frame∞.force k) rr le x′ (slot r i))
      fu-b τ r i (stall k)  rr le (on-skip x) at-skip      = ⊥-elim (lb-b τ r (suc i) (Frame∞.force k) rr le x (slot r i))
      fu-b τ r i (stall k)  rr le (on-skip x) (on-skip x′) = fu-b τ r (suc i) (Frame∞.force k) rr le x x′
      fu-b τ r i (close k)  rr le at-skip     at-skip      = refl
      fu-b τ r i (close k)  rr le at-skip     (on-skip x′) =
        ⊥-elim (lb-f τ (r ++ [ last ]) (From∞.force k) (real-snoc r plain-last rr) (close-ok r rr le (From∞.force k)) x′ (slot-last r i))
      fu-b τ r i (close k)  rr le (on-skip x) at-skip      =
        ⊥-elim (lb-f τ (r ++ [ last ]) (From∞.force k) (real-snoc r plain-last rr) (close-ok r rr le (From∞.force k)) x (slot-last r i))
      fu-b τ r i (close k)  rr le (on-skip x) (on-skip x′) =
        fu-f τ (r ++ [ last ]) (From∞.force k) (real-snoc r plain-last rr) (close-ok r rr le (From∞.force k)) x x′

      fu-f : ∀ {t y e₁ e₂} τ e (m : From A t) → Real e → FrOk τ e m → InE (frames τ e m) y e₁ → InE (frames τ e m) y e₂ → e₁ ≡ e₂
      fu-f τ e done        re _  at-end at-end = refl
      fu-f τ e quiet       re _  ()     _
      fu-f τ e (at t′ _ b) re ok x      x′     = fu-b τ (ix (τ + t′) ∷ sub e ∷ []) 0 b (timer-real τ e re ok) ≤-refl x x′

    -- Nothing follows the end.
    mutual
      la-b : ∀ {t c y e′} τ r i (b : Frame A t) → Real r → tick r ≤ τ + t → InE (burst τ r i b) c end → InE (burst τ r i b) y e′ → y ≼ c
      la-b {c = c} τ r i (emit a k) rr le (on-out xc)  at-out       = step≼ (r ++ [ ix i ]) (r ++ [ ix (suc i) ]) {c} (slot r i) (lb-b τ r (suc i) k rr le xc)
      la-b τ r i (emit a k) rr le (on-out xc)  (on-out x)   = la-b τ r (suc i) k rr le xc x
      la-b {c = c} τ r i (stall k)  rr le (on-skip xc) at-skip      =
        step≼ (r ++ [ ix i ]) (r ++ [ ix (suc i) ]) {c} (slot r i) (lb-b τ r (suc i) (Frame∞.force k) rr le xc)
      la-b τ r i (stall k)  rr le (on-skip xc) (on-skip x)  = la-b τ r (suc i) (Frame∞.force k) rr le xc x
      la-b {c = c} τ r i (close k)  rr le (on-skip xc) at-skip      =
        step≼ (r ++ [ ix i ]) (r ++ [ last ]) {c}  (slot-last r i)
          (lb-f τ (r ++ [ last ]) (From∞.force k) (real-snoc r plain-last rr) (close-ok r rr le (From∞.force k)) xc)
      la-b τ r i (close k)  rr le (on-skip xc) (on-skip x)  =
        la-f τ (r ++ [ last ]) (From∞.force k) (real-snoc r plain-last rr) (close-ok r rr le (From∞.force k)) xc x

      la-f : ∀ {t c y e′} τ e (m : From A t) → Real e → FrOk τ e m → InE (frames τ e m) c end → InE (frames τ e m) y e′ → y ≼ c
      la-f τ e done        re _  at-end at-end = ≼-refl {e}
      la-f τ e quiet       re _  ()     _
      la-f τ e (at t′ _ b) re ok xc     x      = la-b τ (ix (τ + t′) ∷ sub e ∷ []) 0 b (timer-real τ e re ok) ≤-refl xc x

    -- The subscription's own stream.
    module S (rp : Real p) where
      root : Root p
      root = here , rp , inj₁ refl

      late-ok : ∀ n {le : 0 ≤ suc n} {b : Frame A (suc n)} → FrOk (tick p) (p ++ [ last ]) (at (suc n) le b)
      late-ok n = subst (_< tick p + suc n) (sym (tick-snoc p rp)) (m<m+n (tick p) (s≤s z≤n))

      row : ∀ (m : From A 0) {y e} → InE (start p m) y e → Row y
      row (at zero _ b)      x = row-b (tick p) p 0 b root (m≤m+n (tick p) 0) x
      row (at (suc n) le b)  x = row-f (tick p) p (at (suc n) le b) root (late-ok n {le} {b}) x
      row done               x = row-f {0} (tick p) p done root tt x
      row quiet              x = row-f {0} (tick p) p quiet root tt x

      fu : ∀ (m : From A 0) {y e e′} → InE (start p m) y e → InE (start p m) y e′ → e ≡ e′
      fu (at zero _ b)     x x′ = fu-b (tick p) p 0 b rp (m≤m+n (tick p) 0) x x′
      fu (at (suc n) le b) x x′ = fu-f (tick p) (p ++ [ last ]) (at (suc n) le b) (real-snoc p plain-last rp) (late-ok n {le} {b}) x x′
      fu done              x x′ = fu-f {0} (tick p) (p ++ [ last ]) done (real-snoc p plain-last rp) tt x x′
      fu quiet             x x′ = fu-f {0} (tick p) (p ++ [ last ]) quiet (real-snoc p plain-last rp) tt x x′

      la : ∀ (m : From A 0) {c y e} → InE (start p m) c end → InE (start p m) y e → y ≼ c
      la (at zero _ b)     xc x = la-b (tick p) p 0 b rp (m≤m+n (tick p) 0) xc x
      la (at (suc n) le b) xc x = la-f (tick p) (p ++ [ last ]) (at (suc n) le b) (real-snoc p plain-last rp) (late-ok n {le} {b}) xc x
      la done              xc x = la-f {0} (tick p) (p ++ [ last ]) done (real-snoc p plain-last rp) tt xc x
      la quiet             xc x = la-f {0} (tick p) (p ++ [ last ]) quiet (real-snoc p plain-last rp) tt xc x

    wo : ∀ {y} → Row y → W H p y
    wo (_ , _ , (w , _ , _) , pl , refl) = step w pl

    re : ∀ {y} → Row y → Real y
    re (r , _ , (_ , rr , _) , pl , refl) = real-snoc r pl rr

    -- No row lies below another: what leads a row leads its root.
    fl : ∀ {y y′ l ys} → Row y → Row y′ → y′ ≡ y ++ l ∷ ys → ⊥
    fl {l = l} {ys} (r , l₀ , (w , rr , _) , pl , refl) (r′ , l′ , (_ , _ , form) , _ , eq′) eq
      with ⊑-snoc {r ++ [ l₀ ]} r′ (l ∷ ys , trans (sym eq′) eq)
    ... | inj₂ e = ext≢ (r ++ [ l₀ ]) ys (trans (sym eq) (trans eq′ (sym e)))
    ... | inj₁ le with form
    ...   | inj₁ refl = ⊑-≼ {r ++ [ l₀ ]} {p} le (world-after (step w pl) (real-snoc r pl rr))
    ...   | inj₂ (T , e′ , refl) with ⊑-snoc {r ++ [ l₀ ]} (ix T ∷ []) {sub e′} le
    ...     | inj₂ e2 = plain-sub pl (∷ʳ-injectiveʳ r (ix T ∷ []) e2)
    ...     | inj₁ le2 with ⊑-snoc {r ++ [ l₀ ]} [] {ix T} le2
    ...       | inj₂ e3 = subst Real (∷ʳ-injectiveˡ r [] e3) rr
    ...       | inj₁ (zs , e4) = snoc≢[] r (++-conicalˡ (r ++ [ l₀ ]) zs (sym e4))

cold-inv : ∀ {A H} (c : Timeline A) → InvD H (coldᵀ c)
cold-inv {A} {H} c p (rp , _) = record
  { world = λ x → wo (row m (proj₁ x))
  ; real  = λ x → re (row m (proj₁ x))
  ; func  = λ x x′ → fu m (proj₁ x) (proj₁ x′)
  ; flat  = λ x x′ → fl (row m (proj₁ x)) (row m (proj₁ x′)) refl
  ; burst = λ ce y cy → ⊥-elim (la m (proj₁ ce) (proj₁ y) cy)
  }
  where
    m = timelineAt c p
    open CI {A} H p
    open S rp
