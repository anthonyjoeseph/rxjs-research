{-# OPTIONS --guardedness #-}

-- A COLD TIMELINE KEEPS THE INVARIANT.  Its rows lie one plain label below
-- a burst's root: the subscription itself, or a timer's root
-- `ix T ∷ sub e ∷ []` for `e` the previous burst's end, at a tick past
-- it.  Each root lies in the world, so each row does, and none lies below
-- another.  The rows run in order, each after the one before, so a
-- position holds one event and nothing follows the end.
module denotation.Laws.ColdInv where

open import Data.Bool.Properties using (T-≡)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; _++_; [_])
open import Data.List.Properties using (++-conicalˡ; ∷ʳ-injectiveˡ; ∷ʳ-injectiveʳ)
open import Data.Nat using (zero; suc; _+_; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; +-suc; +-monoʳ-≤; m≤m+n; m<m+n)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import denotation.Events using (Pos; Label; ix; sub; last; Time; tick; From; done; quiet; at; Frame; emit; stall; close;
  module Frame∞; module From∞; Timeline; timelineAt; <ᵖ-ix; <ᵖ-part; ix-<)
open import denotation.Events using (frames; burst; start)
open import denotation.EmissionSet using (Ev; end; _≺_; _≼_; InE; at-out; at-skip; at-end; on-out; on-skip; module Op)
open import denotation.Laws.Modulus using (≺→≼; ≼-refl; ≺-≼-≺; ≼-≺-≺; ≺-irrefl; ≺-ext)
open import denotation.Laws.Worlds using (Plain; plain-ix; plain-last; plain-sub; W; W⁼; step; timer; here; inW; Real; real-snoc; real-init; InvD; world-after; _⊑_; ⊑-≼; ⊑-snoc; ext≢; snoc≢[]; Anc; self; up; plain; named; anc-view; parent-fun; step-parent; anc-trans; anc-≼; world-anc⁼; nest-in; nonempty⁼; lone)
open import denotation.Laws.Worlds.Leaves using (ine-pin)

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
    -- A burst's root: the subscription, or a timer's from the end of a
    -- burst before.
    data RootI : Pos → Set where
      r-sub   : RootI p
      r-timer : ∀ {T r} → RootI r → RootI (ix T ∷ sub (r ++ [ last ]) ∷ [])

    Root : Pos → Set
    Root r = W⁼ H p r × Real r × RootI r

    -- A row: one plain label below a root, and an end where it is `last`.
    Row : Pos → Ev A → Set
    Row y e = Σ Pos λ r → Σ Label λ l → Root r × Plain l × y ≡ r ++ [ l ] × (l ≡ last → e ≡ end)

    -- What leads a root: what leads the subscription, a root, or the end
    -- of a burst before one.
    anc-root : ∀ {a r} → RootI r → Anc a r → Anc a p ⊎ RootI a ⊎ Σ Pos λ r′ → RootI r′ × a ≡ r′ ++ [ last ]
    anc-root r-sub x = inj₁ x
    anc-root (r-timer {T} {r} R) x with anc-view x
    ... | inj₁ refl = inj₂ (inj₁ (r-timer R))
    ... | inj₂ (b , x′ , pb) with parent-fun pb (named (ix T ∷ []) refl)
    ...   | refl with anc-view x′
    ...     | inj₁ refl = inj₂ (inj₂ (r , R , refl))
    ...     | inj₂ (b′ , x″ , pb′) with parent-fun pb′ (step-parent r plain-last)
    ...       | refl = anc-root R x″

    root-plain : ∀ {a x l} → RootI a → a ≡ x ++ [ l ] → Plain l → a ≡ p
    root-plain r-sub _ _ = refl
    root-plain {x = x} (r-timer {T} _) eq pl = ⊥-elim (plain-sub pl (sym (∷ʳ-injectiveʳ (ix T ∷ []) x eq)))

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
      row-b : ∀ {t y e′} τ r i (b : Frame A t) → Root r → tick r ≤ τ + t → InE (burst τ r i b) y e′ → Row y e′
      row-b τ r i (emit a k) R le at-out      = r , ix i , R , plain-ix , refl , λ ()
      row-b τ r i (emit a k) R le (on-out x)  = row-b τ r (suc i) k R le x
      row-b τ r i (stall k)  R le at-skip     = r , ix i , R , plain-ix , refl , λ ()
      row-b τ r i (stall k)  R le (on-skip x) = row-b τ r (suc i) (Frame∞.force k) R le x
      row-b τ r i (close k)  R le at-skip     = r , ix i , R , plain-ix , refl , λ ()
      row-b τ r i (close k)  R le (on-skip x) = row-f τ r (From∞.force k) R (close-ok r (proj₁ (proj₂ R)) le (From∞.force k)) x

      row-f : ∀ {t y e′} τ r (m : From A t) → Root r → FrOk τ (r ++ [ last ]) m → InE (frames τ (r ++ [ last ]) m) y e′ → Row y e′
      row-f τ r done          R _  at-end = r , last , R , plain-last , refl , λ _ → refl
      row-f τ r quiet         R _  ()
      row-f τ r (at t′ _ b) (w , rr , ri) ok x =
        row-b τ (ix (τ + t′) ∷ sub (r ++ [ last ]) ∷ []) 0 b
          (inW (timer (τ + t′) (inW (step w plain-last))) , timer-real τ (r ++ [ last ]) (real-snoc r plain-last rr) ok , r-timer ri)
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
      root = here , rp , r-sub

      late-ok : ∀ n {le : 0 ≤ suc n} {b : Frame A (suc n)} → FrOk (tick p) (p ++ [ last ]) (at (suc n) le b)
      late-ok n = subst (_< tick p + suc n) (sym (tick-snoc p rp)) (m<m+n (tick p) (s≤s z≤n))

      row : ∀ (m : From A 0) {y e} → InE (start p m) y e → Row y e
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

    wo : ∀ {y e} → Row y e → W H p y
    wo (_ , _ , (w , _ , _) , pl , refl , _) = step w pl

    re : ∀ {y e} → Row y e → Real y
    re (r , _ , (_ , rr , _) , pl , refl , _) = real-snoc r pl rr

    -- No row lies below another: what leads a row leads its root.
    fl : ∀ {y y′ e e′ l ys} → Row y e → Row y′ e′ → y′ ≡ y ++ l ∷ ys → ⊥
    fl {l = l} {ys} (r , l₀ , (w , rr , _) , pl , refl , _) (r′ , l′ , (_ , _ , form) , _ , eq′ , _) eq
      with ⊑-snoc {r ++ [ l₀ ]} r′ (l ∷ ys , trans (sym eq′) eq)
    ... | inj₂ e = ext≢ (r ++ [ l₀ ]) ys (trans (sym eq) (trans eq′ (sym e)))
    ... | inj₁ le with form
    ...   | r-sub = ⊑-≼ {r ++ [ l₀ ]} {p} le (world-after (step w pl) (real-snoc r pl rr))
    ...   | r-timer {T} {r₀} _ with ⊑-snoc {r ++ [ l₀ ]} (ix T ∷ []) {sub (r₀ ++ [ last ])} le
    ...     | inj₂ e2 = plain-sub pl (∷ʳ-injectiveʳ r (ix T ∷ []) e2)
    ...     | inj₁ le2 with ⊑-snoc {r ++ [ l₀ ]} [] {ix T} le2
    ...       | inj₂ e3 = subst Real (∷ʳ-injectiveˡ r [] e3) rr
    ...       | inj₁ (zs , e4) = snoc≢[] r (++-conicalˡ (r ++ [ l₀ ]) zs (sym e4))

cold-inv : ∀ {A H} (c : Timeline A) → InvD H (Op.cold c)
cold-inv {A} {H} c p (rp , dj) = record
  { world = λ x → wo (row m (proj₁ x))
  ; real  = λ x → re (row m (proj₁ x))
  ; func  = λ x x′ → fu m (proj₁ x) (proj₁ x′)
  ; flat  = λ x x′ → fl (row m (proj₁ x)) (row m (proj₁ x′)) refl
  ; burst = λ ce y cy → ⊥-elim (la m (proj₁ ce) (proj₁ y) cy)
  ; under = λ x y pl v le → un (proj₁ x) (proj₁ y) (row m (proj₁ x)) (row m (proj₁ y)) pl v le
  ; quiet = λ ce y cy → ⊥-elim (la m (proj₁ ce) (proj₁ y) cy)
  ; pinned = λ x → ⊥-elim (ine-pin (proj₁ x))
  }
  where
    m = timelineAt c p
    open CI {A} H p
    open S rp

    -- A row leads no root of a row after it: what leads a root is the
    -- subscription's, a root, or an end.
    off : ∀ {q y r e e′} → InE (start p m) q e → InE (start p m) y e′ → Row q e → Root r → r ≺ y → Anc q r → ⊥
    off {q} {y} {r} xq xy Rq (_ , rr , ri) ry a with anc-root ri a | Rq
    ... | inj₁ ap | _ = anc-≼ ap rp (world-after (wo Rq) (re Rq))
    ... | inj₂ (inj₁ rq) | (r₁ , l₁ , _ , pl₁ , eq₁ , _) = ≺-irrefl {p} (subst (p ≺_) (root-plain rq eq₁ pl₁) (world-after (wo Rq) (re Rq)))
    ... | inj₂ (inj₂ (r′ , _ , eq)) | (r₁ , l₁ , _ , pl₁ , eq₁ , lst) with ∷ʳ-injectiveʳ r₁ r′ (trans (sym eq₁) eq)
    ...   | refl with lst refl
    ...     | refl = la m xq xy (≼-≺-≺ {q} {r} {y} (anc-≼ a rr) ry)

    un : ∀ {q y w l e e′} → InE (start p m) q e → InE (start p m) y e′ → Row q e → Row y e′ → Plain l → W⁼ H (q ++ [ l ]) w → w ⊑ y → ⊥
    un {q} {y} {w} {l} xq xy Rq Ry pl v (zs , eq) with real-init w zs (subst Real eq (re Ry))
    ... | inj₁ refl = nonempty⁼ (snoc≢[] q) v
    ... | inj₂ rw = go xy Ry (zs , eq)
      where
        wp : W H p w
        wp = nest-in (step (inW (wo Rq)) pl) v

        aq : Anc q (q ++ [ l ])
        aq = up self (plain pl refl)

        go : ∀ {y e′} → InE (start p m) y e′ → Row y e′ → w ⊑ y → ⊥
        go xy (r₂ , l₂ , R₂ , pl₂ , refl , _) le with ⊑-snoc r₂ le
        ... | inj₂ e with anc-view (world-anc⁼ (subst (W⁼ H (q ++ [ l ])) e v))
        ...   | inj₁ e′ = off xq xy Rq R₂ (≺-ext r₂ {l₂} []) (subst (Anc q) (∷ʳ-injectiveˡ q r₂ e′) self)
        ...   | inj₂ (b , a , pb) with parent-fun pb (step-parent r₂ pl₂)
        ...     | refl = off xq xy Rq R₂ (≺-ext r₂ {l₂} []) (anc-trans aq a)
        go xy (r₂ , l₂ , R₂ , pl₂ , refl , _) le | inj₁ le₂ with proj₂ (proj₂ R₂)
        ... | r-sub = ⊑-≼ le₂ (world-after wp rw)
        ... | r-timer {T} {r₀} _ with ⊑-snoc (ix T ∷ []) {sub (r₀ ++ [ last ])} le₂
        ...   | inj₁ le₃ = lone rp wp le₃
        ...   | inj₂ e   = off xq xy Rq R₂ (≺-ext r₂ {l₂} []) (anc-trans aq (world-anc⁼ (subst (W⁼ H (q ++ [ l ])) e v)))
