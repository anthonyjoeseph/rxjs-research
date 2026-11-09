{-# OPTIONS --guardedness #-}

-- A COLD TIMELINE KEEPS THE INVARIANT.  Its rows lie one plain label below
-- a burst's root: the subscription itself, or a timer's root
-- `cascadeAt T e` for `e` the previous burst's end, at a tick past it.  Each root lies in the world, so each row does, and none lies below
-- another.  The rows run in order, each after the one before, so a
-- position holds one event and nothing follows the end.
module denotation.Laws.ColdInv where

open import Data.Bool.Properties using (T-≡)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using () renaming (here to hd; there to th)
open import Data.Nat using (zero; suc; _+_; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; +-suc; +-monoʳ-≤; m≤m+n; m<m+n)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import denotation.Position using (Pos; Label; ix; last; Time; tick; _∙_; frame; cascadeAt; _⊕_)
open import denotation.Events using (From; done; quiet; at; Frame; emit; stall; close; module Frame∞; module From∞; Timeline; timelineAt; <ᵖ-ix; <ᵖ-part)
open import denotation.Events using (Events; frames; burst; start)
open import denotation.EmissionSet using (Ev; end; _≺_; _≼_; Reach; InE; at-out; at-skip; at-end; on-out; on-skip; module Op)
open import denotation.Laws.Modulus using (≺→≼; ≼-refl; ≺-≼-≺; ≼-≺-≺; ≺-trans; ≺-ext)
open import denotation.Laws.Worlds using (TimerRoot; ext-untimed; Plain; plain-ix; plain-last; W; W⁼; step; timer; here; inW; Real; real-snoc; real-init; InvD; world-after; _⊑_; ⊑-≼; ⊑-snoc; ext≢; Anc; self; up; plain; anc-view; parent-fun; step-parent; timed; anc-trans; anc-≼; world-anc⁼; nest-in; ⊕-injˡ; ⊕-injʳ; ⊑-unit; step≢root; timer-after)
open import denotation.Laws.Worlds.Leaves using (ine-pin)
open import denotation.Simultaneity using (effect-tick)

-- One slot before the next, and before the end.
slot : ∀ r i → (r ⊕ [ ix i ]) ≺ (r ⊕ [ ix (suc i) ])
slot r i = Equivalence.from T-≡ (<ᵖ-part r [] [] (<ᵖ-ix i))

slot-last : ∀ r i → (r ⊕ [ ix i ]) ≺ (r ⊕ [ last ])
slot-last r i = Equivalence.from T-≡ (<ᵖ-part r [] [] refl)

-- A stream's positions up to a row of it.
upTo : ∀ {A} {ev : Events A} {y e} → InE ev y e → List Pos
upTo (at-out {k})    = k ∷ []
upTo (at-skip {k})   = k ∷ []
upTo (at-end {k})    = k ∷ []
upTo (on-out {k} x)  = k ∷ upTo x
upTo (on-skip {k} x) = k ∷ upTo x

private
  step≼ : ∀ a b {y} → a ≺ b → b ≼ y → a ≼ y
  step≼ a b {y} ab by = ≺→≼ {a} {y} (≺-≼-≺ {a} {b} {y} ab by)

  module CI {A : Set} (H : Pos → Set) (p : Pos) where
    -- A burst's root: the subscription, a timer's from the end of a burst
    -- before, or a burst's end, under which its last callback runs on.
    data RootI : Pos → Set where
      r-sub   : RootI p
      r-fin   : ∀ {r} → RootI r → RootI (r ⊕ [ last ])
      r-timer : ∀ {T r} → RootI r → RootI (cascadeAt T (r ⊕ [ last ]))

    data Timer : Pos → Set where
      tm : ∀ {T r} → Timer (cascadeAt T (r ⊕ [ last ]))

    Root : Pos → Set
    Root r = W⁼ H p r × Real r × RootI r

    -- A row: one plain label below a root, and an end where it is `last`.
    Row : Pos → Ev A → Set
    Row y e = Σ Pos λ r → Σ Label λ l → Root r × Plain l × y ≡ r ⊕ [ l ] × (l ≡ last → e ≡ end)

    -- What leads a root: what leads the subscription, a root, or the end
    -- of a burst before one.
    anc-root : ∀ {a r} → RootI r → Anc a r → Anc a p ⊎ Timer a ⊎ Σ Pos λ r′ → RootI r′ × a ≡ r′ ⊕ [ last ]
    anc-root r-sub x = inj₁ x
    anc-root (r-fin {r} R) x with anc-view x
    ... | inj₁ refl = inj₂ (inj₂ (r , R , refl))
    ... | inj₂ (b , x′ , pb) with parent-fun pb (step-parent r plain-last)
    ...   | refl = anc-root R x′
    anc-root (r-timer {T} {r} R) x with anc-view x
    ... | inj₁ refl = inj₂ (inj₁ tm)
    ... | inj₂ (b , x′ , pb) with parent-fun pb (timed T refl)
    ...   | refl with anc-view x′
    ...     | inj₁ refl = inj₂ (inj₂ (r , R , refl))
    ...     | inj₂ (b′ , x″ , pb′) with parent-fun pb′ (step-parent r plain-last)
    ...       | refl = anc-root R x″

    timer-plain : ∀ {a x l} → Timer a → a ≡ x ⊕ [ l ] → ⊥
    timer-plain {x = x} tm eq = step≢root x _ (sym eq)

    -- The next frame lies past the end before it.
    FrOk : ∀ {t} → Time → Pos → From A t → Set
    FrOk τ e (at t′ _ _) = tick e < τ + t′
    FrOk τ e done        = ⊤
    FrOk τ e quiet       = ⊤

    close-ok : ∀ {τ t} r → Real r → tick r ≤ τ + t → (m : From A (suc t)) → FrOk τ (r ⊕ [ last ]) m
    close-ok         r rr le done          = tt
    close-ok         r rr le quiet         = tt
    close-ok {τ} {t} r rr le (at t′ le′ _) =
      subst (_< τ + t′) (sym (effect-tick r _)) (≤-trans (s≤s le) (subst (_≤ τ + t′) (+-suc τ t) (+-monoʳ-≤ τ le′)))

    timer-real : ∀ τ {t′} e → Real e → tick e < τ + t′ → Real (cascadeAt (τ + t′) e)
    timer-real τ e re lt = re , lt , tt

    -- A burst's end, as the root its last callback runs on under.
    fin-root : ∀ {r} → Root r → Root (r ⊕ [ last ])
    fin-root {r} (w , rr , ri) = inW (step w plain-last) , real-snoc r plain-last rr , r-fin ri

    fin-le : ∀ {τ t} r → Real r → tick r ≤ τ + t → tick (r ⊕ [ last ]) ≤ τ + t
    fin-le {τ} {t} r rr le = subst (_≤ τ + t) (sym (effect-tick r _)) le

    -- The frame after a last callback lies past its end.
    fin-ok : ∀ {τ t} r → Real r → tick r ≤ τ + t → (m : From A (suc t)) → FrOk τ ((r ⊕ [ last ]) ⊕ [ last ]) m
    fin-ok {τ} {t} r rr le = close-ok {τ} {t} (r ⊕ [ last ]) (real-snoc r plain-last rr) (fin-le {τ} {t} r rr le)

    fin-real : ∀ r → Real r → Real ((r ⊕ [ last ]) ⊕ [ last ])
    fin-real r rr = real-snoc (r ⊕ [ last ]) plain-last (real-snoc r plain-last rr)

    -- A slot before a last callback's value, which is before its end.
    slot-fin : ∀ r i → (r ⊕ [ ix i ]) ≺ ((r ⊕ [ last ]) ⊕ [ ix 0 ])
    slot-fin r i = ≺-trans {r ⊕ [ ix i ]} {r ⊕ [ last ]} {(r ⊕ [ last ]) ⊕ [ ix 0 ]} (slot-last r i) (≺-ext (r ⊕ [ last ]) {ix 0} [])

    mutual
      row-b : ∀ {t y e′} τ r i (b : Frame A t) → Root r → tick r ≤ τ + t → InE (burst τ r i b) y e′ → Row y e′
      row-b τ r i (emit a (close k)) R le at-out = r ⊕ [ last ] , ix 0 , fin-root R , plain-ix , refl , λ ()
      row-b τ r i (emit a (close k)) R@(_ , rr , _) le (on-out x) =
        row-f τ (r ⊕ [ last ]) (From∞.force k) (fin-root R) (fin-ok r rr le (From∞.force k)) x
      row-b τ r i (emit a k@(emit _ _)) R le at-out     = r , ix i , R , plain-ix , refl , λ ()
      row-b τ r i (emit a k@(emit _ _)) R le (on-out x) = row-b τ r (suc i) k R le x
      row-b τ r i (emit a k@(stall _))  R le at-out     = r , ix i , R , plain-ix , refl , λ ()
      row-b τ r i (emit a k@(stall _))  R le (on-out x) = row-b τ r (suc i) k R le x
      row-b τ r i (stall k)  R le at-skip     = r , ix i , R , plain-ix , refl , λ ()
      row-b τ r i (stall k)  R le (on-skip x) = row-b τ r (suc i) (Frame∞.force k) R le x
      row-b τ r i (close k)  R le at-skip     = r , ix i , R , plain-ix , refl , λ ()
      row-b τ r i (close k)  R le (on-skip x) = row-f τ r (From∞.force k) R (close-ok r (proj₁ (proj₂ R)) le (From∞.force k)) x

      row-f : ∀ {t y e′} τ r (m : From A t) → Root r → FrOk τ (r ⊕ [ last ]) m → InE (frames τ (r ⊕ [ last ]) m) y e′ → Row y e′
      row-f τ r done          R _  at-end = r , last , R , plain-last , refl , λ _ → refl
      row-f τ r quiet         R _  ()
      row-f τ r (at t′ _ b) (w , rr , ri) ok x =
        row-b τ (cascadeAt (τ + t′) (r ⊕ [ last ])) 0 b
          (inW (timer (τ + t′) (inW (step w plain-last)) ok) , timer-real τ (r ⊕ [ last ]) (real-snoc r plain-last rr) ok , r-timer ri)
          ≤-refl x

    -- Every row lies at or after the stream's first.
    mutual
      lb-b : ∀ {t y e′} τ r i (b : Frame A t) → Real r → tick r ≤ τ + t → InE (burst τ r i b) y e′ → (r ⊕ [ ix i ]) ≼ y
      lb-b τ r i (emit a (close k)) rr le at-out = ≺→≼ {r ⊕ [ ix i ]} {(r ⊕ [ last ]) ⊕ [ ix 0 ]} (slot-fin r i)
      lb-b {y = y} τ r i (emit a (close k)) rr le (on-out x) =
        step≼ (r ⊕ [ ix i ]) (r ⊕ [ last ]) {y} (slot-last r i)
          (step≼ (r ⊕ [ last ]) ((r ⊕ [ last ]) ⊕ [ last ]) {y} (≺-ext (r ⊕ [ last ]) {last} [])
            (lb-f τ ((r ⊕ [ last ]) ⊕ [ last ]) (From∞.force k) (fin-real r rr) (fin-ok r rr le (From∞.force k)) x))
      lb-b τ r i (emit a k@(emit _ _)) rr le at-out = ≼-refl {r ⊕ [ ix i ]}
      lb-b {y = y} τ r i (emit a k@(emit _ _)) rr le (on-out x) = step≼ (r ⊕ [ ix i ]) (r ⊕ [ ix (suc i) ]) {y} (slot r i) (lb-b τ r (suc i) k rr le x)
      lb-b τ r i (emit a k@(stall _)) rr le at-out = ≼-refl {r ⊕ [ ix i ]}
      lb-b {y = y} τ r i (emit a k@(stall _)) rr le (on-out x) = step≼ (r ⊕ [ ix i ]) (r ⊕ [ ix (suc i) ]) {y} (slot r i) (lb-b τ r (suc i) k rr le x)
      lb-b τ r i (stall k)  rr le at-skip     = ≼-refl {r ⊕ [ ix i ]}
      lb-b {y = y} τ r i (stall k)  rr le (on-skip x) = step≼ (r ⊕ [ ix i ]) (r ⊕ [ ix (suc i) ]) {y} (slot r i) (lb-b τ r (suc i) (Frame∞.force k) rr le x)
      lb-b τ r i (close k)  rr le at-skip     = ≼-refl {r ⊕ [ ix i ]}
      lb-b {y = y} τ r i (close k)  rr le (on-skip x) =
        step≼ (r ⊕ [ ix i ]) (r ⊕ [ last ]) {y} (slot-last r i) (lb-f τ (r ⊕ [ last ]) (From∞.force k) (real-snoc r plain-last rr) (close-ok r rr le (From∞.force k)) x)

      lb-f : ∀ {t y e′} τ e (m : From A t) → Real e → FrOk τ e m → InE (frames τ e m) y e′ → e ≼ y
      lb-f τ e done        re _  at-end = ≼-refl {e}
      lb-f τ e quiet       re _  ()
      lb-f {y = y} τ e (at t′ _ b) re ok x =
        step≼ e (cascadeAt (τ + t′) e ⊕ [ ix 0 ]) {y}
          (≺-trans {e} {cascadeAt (τ + t′) e} {cascadeAt (τ + t′) e ⊕ [ ix 0 ]} (timer-after e ok) (≺-ext (cascadeAt (τ + t′) e) {ix 0} []))
          (lb-b τ (cascadeAt (τ + t′) e) 0 b (timer-real τ e re ok) ≤-refl x)

    -- One event at a position.
    mutual
      fu-b : ∀ {t y e₁ e₂} τ r i (b : Frame A t) → Real r → tick r ≤ τ + t → InE (burst τ r i b) y e₁ → InE (burst τ r i b) y e₂ → e₁ ≡ e₂
      fu-b τ r i (emit a (close k)) rr le at-out     at-out      = refl
      fu-b τ r i (emit a (close k)) rr le at-out     (on-out x′) =
        ⊥-elim (lb-f τ ((r ⊕ [ last ]) ⊕ [ last ]) (From∞.force k) (fin-real r rr) (fin-ok r rr le (From∞.force k)) x′ (slot-last (r ⊕ [ last ]) 0))
      fu-b τ r i (emit a (close k)) rr le (on-out x) at-out      =
        ⊥-elim (lb-f τ ((r ⊕ [ last ]) ⊕ [ last ]) (From∞.force k) (fin-real r rr) (fin-ok r rr le (From∞.force k)) x (slot-last (r ⊕ [ last ]) 0))
      fu-b τ r i (emit a (close k)) rr le (on-out x) (on-out x′) =
        fu-f τ ((r ⊕ [ last ]) ⊕ [ last ]) (From∞.force k) (fin-real r rr) (fin-ok r rr le (From∞.force k)) x x′
      fu-b τ r i (emit a k@(emit _ _)) rr le at-out     at-out      = refl
      fu-b τ r i (emit a k@(emit _ _)) rr le at-out     (on-out x′) = ⊥-elim (lb-b τ r (suc i) k rr le x′ (slot r i))
      fu-b τ r i (emit a k@(emit _ _)) rr le (on-out x) at-out      = ⊥-elim (lb-b τ r (suc i) k rr le x (slot r i))
      fu-b τ r i (emit a k@(emit _ _)) rr le (on-out x) (on-out x′) = fu-b τ r (suc i) k rr le x x′
      fu-b τ r i (emit a k@(stall _))  rr le at-out     at-out      = refl
      fu-b τ r i (emit a k@(stall _))  rr le at-out     (on-out x′) = ⊥-elim (lb-b τ r (suc i) k rr le x′ (slot r i))
      fu-b τ r i (emit a k@(stall _))  rr le (on-out x) at-out      = ⊥-elim (lb-b τ r (suc i) k rr le x (slot r i))
      fu-b τ r i (emit a k@(stall _))  rr le (on-out x) (on-out x′) = fu-b τ r (suc i) k rr le x x′
      fu-b τ r i (stall k)  rr le at-skip     at-skip      = refl
      fu-b τ r i (stall k)  rr le at-skip     (on-skip x′) = ⊥-elim (lb-b τ r (suc i) (Frame∞.force k) rr le x′ (slot r i))
      fu-b τ r i (stall k)  rr le (on-skip x) at-skip      = ⊥-elim (lb-b τ r (suc i) (Frame∞.force k) rr le x (slot r i))
      fu-b τ r i (stall k)  rr le (on-skip x) (on-skip x′) = fu-b τ r (suc i) (Frame∞.force k) rr le x x′
      fu-b τ r i (close k)  rr le at-skip     at-skip      = refl
      fu-b τ r i (close k)  rr le at-skip     (on-skip x′) =
        ⊥-elim (lb-f τ (r ⊕ [ last ]) (From∞.force k) (real-snoc r plain-last rr) (close-ok r rr le (From∞.force k)) x′ (slot-last r i))
      fu-b τ r i (close k)  rr le (on-skip x) at-skip      =
        ⊥-elim (lb-f τ (r ⊕ [ last ]) (From∞.force k) (real-snoc r plain-last rr) (close-ok r rr le (From∞.force k)) x (slot-last r i))
      fu-b τ r i (close k)  rr le (on-skip x) (on-skip x′) =
        fu-f τ (r ⊕ [ last ]) (From∞.force k) (real-snoc r plain-last rr) (close-ok r rr le (From∞.force k)) x x′

      fu-f : ∀ {t y e₁ e₂} τ e (m : From A t) → Real e → FrOk τ e m → InE (frames τ e m) y e₁ → InE (frames τ e m) y e₂ → e₁ ≡ e₂
      fu-f τ e done        re _  at-end at-end = refl
      fu-f τ e quiet       re _  ()     _
      fu-f τ e (at t′ _ b) re ok x      x′     = fu-b τ (cascadeAt (τ + t′) e) 0 b (timer-real τ e re ok) ≤-refl x x′

    -- Nothing follows the end.
    mutual
      la-b : ∀ {t c y e′} τ r i (b : Frame A t) → Real r → tick r ≤ τ + t → InE (burst τ r i b) c end → InE (burst τ r i b) y e′ → y ≼ c
      la-b {c = c} τ r i (emit a (close k)) rr le (on-out xc) at-out =
        step≼ ((r ⊕ [ last ]) ⊕ [ ix 0 ]) ((r ⊕ [ last ]) ⊕ [ last ]) {c} (slot-last (r ⊕ [ last ]) 0)
          (lb-f τ ((r ⊕ [ last ]) ⊕ [ last ]) (From∞.force k) (fin-real r rr) (fin-ok r rr le (From∞.force k)) xc)
      la-b τ r i (emit a (close k)) rr le (on-out xc) (on-out x) =
        la-f τ ((r ⊕ [ last ]) ⊕ [ last ]) (From∞.force k) (fin-real r rr) (fin-ok r rr le (From∞.force k)) xc x
      la-b {c = c} τ r i (emit a k@(emit _ _)) rr le (on-out xc) at-out     = step≼ (r ⊕ [ ix i ]) (r ⊕ [ ix (suc i) ]) {c} (slot r i) (lb-b τ r (suc i) k rr le xc)
      la-b         τ r i (emit a k@(emit _ _)) rr le (on-out xc) (on-out x) = la-b τ r (suc i) k rr le xc x
      la-b {c = c} τ r i (emit a k@(stall _))  rr le (on-out xc) at-out     = step≼ (r ⊕ [ ix i ]) (r ⊕ [ ix (suc i) ]) {c} (slot r i) (lb-b τ r (suc i) k rr le xc)
      la-b         τ r i (emit a k@(stall _))  rr le (on-out xc) (on-out x) = la-b τ r (suc i) k rr le xc x
      la-b {c = c} τ r i (stall k)  rr le (on-skip xc) at-skip      =
        step≼ (r ⊕ [ ix i ]) (r ⊕ [ ix (suc i) ]) {c} (slot r i) (lb-b τ r (suc i) (Frame∞.force k) rr le xc)
      la-b τ r i (stall k)  rr le (on-skip xc) (on-skip x)  = la-b τ r (suc i) (Frame∞.force k) rr le xc x
      la-b {c = c} τ r i (close k)  rr le (on-skip xc) at-skip      =
        step≼ (r ⊕ [ ix i ]) (r ⊕ [ last ]) {c}  (slot-last r i)
          (lb-f τ (r ⊕ [ last ]) (From∞.force k) (real-snoc r plain-last rr) (close-ok r rr le (From∞.force k)) xc)
      la-b τ r i (close k)  rr le (on-skip xc) (on-skip x)  =
        la-f τ (r ⊕ [ last ]) (From∞.force k) (real-snoc r plain-last rr) (close-ok r rr le (From∞.force k)) xc x

      la-f : ∀ {t c y e′} τ e (m : From A t) → Real e → FrOk τ e m → InE (frames τ e m) c end → InE (frames τ e m) y e′ → y ≼ c
      la-f τ e done        re _  at-end at-end = ≼-refl {e}
      la-f τ e quiet       re _  ()     _
      la-f τ e (at t′ _ b) re ok xc     x      = la-b τ (cascadeAt (τ + t′) e) 0 b (timer-real τ e re ok) ≤-refl xc x

    -- Every row before another lies in the stream up to it.
    mutual
      pre-b : ∀ {t q y e e′} τ r i (b : Frame A t) → Real r → tick r ≤ τ + t → (x : InE (burst τ r i b) q e) → InE (burst τ r i b) y e′ → y ≺ q → y ∈ upTo x
      pre-b τ r i (emit a (close k)) rr le at-out at-out _ = hd refl
      pre-b {y = y} τ r i (emit a (close k)) rr le at-out (on-out x′) yq =
        ⊥-elim (step≼ ((r ⊕ [ last ]) ⊕ [ ix 0 ]) ((r ⊕ [ last ]) ⊕ [ last ]) {y} (slot-last (r ⊕ [ last ]) 0)
          (lb-f τ ((r ⊕ [ last ]) ⊕ [ last ]) (From∞.force k) (fin-real r rr) (fin-ok r rr le (From∞.force k)) x′) yq)
      pre-b τ r i (emit a (close k)) rr le (on-out x) at-out _ = hd refl
      pre-b τ r i (emit a (close k)) rr le (on-out x) (on-out x′) yq =
        th (pre-f τ ((r ⊕ [ last ]) ⊕ [ last ]) (From∞.force k) (fin-real r rr) (fin-ok r rr le (From∞.force k)) x x′ yq)
      pre-b τ r i (emit a k@(emit _ _)) rr le at-out at-out _ = hd refl
      pre-b {y = y} τ r i (emit a k@(emit _ _)) rr le at-out (on-out x′) yq = ⊥-elim (step≼ (r ⊕ [ ix i ]) (r ⊕ [ ix (suc i) ]) {y} (slot r i) (lb-b τ r (suc i) k rr le x′) yq)
      pre-b τ r i (emit a k@(emit _ _)) rr le (on-out x) at-out _ = hd refl
      pre-b τ r i (emit a k@(emit _ _)) rr le (on-out x) (on-out x′) yq = th (pre-b τ r (suc i) k rr le x x′ yq)
      pre-b τ r i (emit a k@(stall _)) rr le at-out at-out _ = hd refl
      pre-b {y = y} τ r i (emit a k@(stall _)) rr le at-out (on-out x′) yq = ⊥-elim (step≼ (r ⊕ [ ix i ]) (r ⊕ [ ix (suc i) ]) {y} (slot r i) (lb-b τ r (suc i) k rr le x′) yq)
      pre-b τ r i (emit a k@(stall _)) rr le (on-out x) at-out _ = hd refl
      pre-b τ r i (emit a k@(stall _)) rr le (on-out x) (on-out x′) yq = th (pre-b τ r (suc i) k rr le x x′ yq)
      pre-b τ r i (stall k)  rr le at-skip     at-skip      _  = hd refl
      pre-b {y = y} τ r i (stall k) rr le at-skip (on-skip x′) yq =
        ⊥-elim (step≼ (r ⊕ [ ix i ]) (r ⊕ [ ix (suc i) ]) {y} (slot r i) (lb-b τ r (suc i) (Frame∞.force k) rr le x′) yq)
      pre-b τ r i (stall k)  rr le (on-skip x) at-skip      _  = hd refl
      pre-b τ r i (stall k)  rr le (on-skip x) (on-skip x′) yq = th (pre-b τ r (suc i) (Frame∞.force k) rr le x x′ yq)
      pre-b τ r i (close k)  rr le at-skip     at-skip      _  = hd refl
      pre-b {y = y} τ r i (close k) rr le at-skip (on-skip x′) yq =
        ⊥-elim (step≼ (r ⊕ [ ix i ]) (r ⊕ [ last ]) {y} (slot-last r i)
          (lb-f τ (r ⊕ [ last ]) (From∞.force k) (real-snoc r plain-last rr) (close-ok r rr le (From∞.force k)) x′) yq)
      pre-b τ r i (close k)  rr le (on-skip x) at-skip      _  = hd refl
      pre-b τ r i (close k)  rr le (on-skip x) (on-skip x′) yq =
        th (pre-f τ (r ⊕ [ last ]) (From∞.force k) (real-snoc r plain-last rr) (close-ok r rr le (From∞.force k)) x x′ yq)

      pre-f : ∀ {t q y e₁ e₂} τ e (m : From A t) → Real e → FrOk τ e m → (x : InE (frames τ e m) q e₁) → InE (frames τ e m) y e₂ → y ≺ q → y ∈ upTo x
      pre-f τ e done        re _  at-end at-end _  = hd refl
      pre-f τ e quiet       re _  ()     _      _
      pre-f τ e (at t′ _ b) re ok x      x′     yq = pre-b τ (cascadeAt (τ + t′) e) 0 b (timer-real τ e re ok) ≤-refl x x′ yq

    -- The subscription's own stream.
    module S (rp : Real p) where
      root : Root p
      root = here , rp , r-sub

      late-ok : ∀ n {le : 0 ≤ suc n} {b : Frame A (suc n)} → FrOk (tick p) (p ⊕ [ last ]) (at (suc n) le b)
      late-ok n = subst (_< tick p + suc n) (sym (effect-tick p _)) (m<m+n (tick p) (s≤s z≤n))

      row : ∀ (m : From A 0) {y e} → InE (start p m) y e → Row y e
      row (at zero _ b)      x = row-b (tick p) p 0 b root (m≤m+n (tick p) 0) x
      row (at (suc n) le b)  x = row-f (tick p) p (at (suc n) le b) root (late-ok n {le} {b}) x
      row done               x = row-f {0} (tick p) p done root tt x
      row quiet              x = row-f {0} (tick p) p quiet root tt x

      fu : ∀ (m : From A 0) {y e e′} → InE (start p m) y e → InE (start p m) y e′ → e ≡ e′
      fu (at zero _ b)     x x′ = fu-b (tick p) p 0 b rp (m≤m+n (tick p) 0) x x′
      fu (at (suc n) le b) x x′ = fu-f (tick p) (p ⊕ [ last ]) (at (suc n) le b) (real-snoc p plain-last rp) (late-ok n {le} {b}) x x′
      fu done              x x′ = fu-f {0} (tick p) (p ⊕ [ last ]) done (real-snoc p plain-last rp) tt x x′
      fu quiet             x x′ = fu-f {0} (tick p) (p ⊕ [ last ]) quiet (real-snoc p plain-last rp) tt x x′

      la : ∀ (m : From A 0) {c y e} → InE (start p m) c end → InE (start p m) y e → y ≼ c
      la (at zero _ b)     xc x = la-b (tick p) p 0 b rp (m≤m+n (tick p) 0) xc x
      la (at (suc n) le b) xc x = la-f (tick p) (p ⊕ [ last ]) (at (suc n) le b) (real-snoc p plain-last rp) (late-ok n {le} {b}) xc x
      la done              xc x = la-f {0} (tick p) (p ⊕ [ last ]) done (real-snoc p plain-last rp) tt xc x
      la quiet             xc x = la-f {0} (tick p) (p ⊕ [ last ]) quiet (real-snoc p plain-last rp) tt xc x

      pre : ∀ (m : From A 0) {q y e e′} (x : InE (start p m) q e) → InE (start p m) y e′ → y ≺ q → y ∈ upTo x
      pre (at zero _ b)     x x′ yq = pre-b (tick p) p 0 b rp (m≤m+n (tick p) 0) x x′ yq
      pre (at (suc n) le b) x x′ yq = pre-f (tick p) (p ⊕ [ last ]) (at (suc n) le b) (real-snoc p plain-last rp) (late-ok n {le} {b}) x x′ yq
      pre done              x x′ yq = pre-f {0} (tick p) (p ⊕ [ last ]) done (real-snoc p plain-last rp) tt x x′ yq
      pre quiet             x x′ yq = pre-f {0} (tick p) (p ⊕ [ last ]) quiet (real-snoc p plain-last rp) tt x x′ yq

    wo : ∀ {y e} → Row y e → W H p y
    wo (_ , _ , (w , _ , _) , pl , refl , _) = step w pl

    re : ∀ {y e} → Row y e → Real y
    re (r , _ , (_ , rr , _) , pl , refl , _) = real-snoc r pl rr

    -- A row at a burst's end is that end.
    row-last : ∀ {y e r} → Row y e → y ≡ r ⊕ [ last ] → e ≡ end
    row-last {r = r} (r₁ , _ , _ , _ , refl , lst) eq = lst (⊕-injʳ r₁ r eq)

    -- A row leads no root, unless it is an end: what leads a row leads its
    -- root.
    fl-root : ∀ {y e r} → Row y e → (e ≡ end → ⊥) → RootI r → y ⊑ r → ⊥
    fl-root (r , l₀ , (w , rr , _) , pl , refl , _) ne r-sub le = ⊑-≼ {r ⊕ [ l₀ ]} {p} le (world-after (step w pl) (real-snoc r pl rr))
    fl-root Ry ne (r-fin {r₀} R₀) le with ⊑-snoc r₀ {last} le
    ... | inj₁ le′ = fl-root Ry ne R₀ le′
    ... | inj₂ e   = ne (row-last Ry e)
    fl-root (r , _ , _ , _ , refl , _) ne (r-timer _) le = step≢root r _ (⊑-unit _ le)

    -- No row lies below another, unless an end: what leads a row leads its
    -- root.
    fl : ∀ {y y′ e e′ l ys} → Row y e → (e ≡ end → ⊥) → Row y′ e′ → y′ ≡ y ⊕ (l ∷ ys) → ⊥
    fl {y} {l = l} {ys} Ry ne (r′ , l′ , (_ , _ , form) , _ , eq′ , _) eq
      with ⊑-snoc {y} r′ (l ∷ ys , trans (sym eq′) eq)
    ... | inj₂ e  = ext≢ y ys (trans (sym eq) (trans eq′ (sym e)))
    ... | inj₁ le = fl-root Ry ne form le

cold-inv : ∀ {A H} (c : Timeline A) → InvD H (Op.cold c)
cold-inv {A} {H} c p (rp , dj) = record
  { world = λ x → wo (row m (proj₁ x))
  ; real  = λ x → re (row m (proj₁ x))
  ; func  = λ x x′ → fu m (proj₁ x) (proj₁ x′)
  ; flat  = λ x x′ → flt (proj₁ x) (proj₁ x′)
  ; burst = λ ce y cy → ⊥-elim (la m (proj₁ ce) (proj₁ y) cy)
  ; under = λ x y pl v le → un (proj₁ x) (proj₁ y) (row m (proj₁ x)) (row m (proj₁ y)) pl v le
  ; quiet = λ ce y cy → ⊥-elim (la m (proj₁ ce) (proj₁ y) cy)
  ; pinned = λ x → ⊥-elim (ine-pin (proj₁ x))
  ; untimed = λ x → ut (row m (proj₁ x))
  }
  where
    m = timelineAt c p
    open CI {A} H p
    open S rp

    ut : ∀ {y e} → Row y e → TimerRoot y → ⊥
    ut (r , _ , _ , _ , refl , _) = ext-untimed r

    -- Nothing follows an end, so no row lies below one.
    flt : ∀ {y e e′ l ys} → InE (start p m) y e → InE (start p m) (y ⊕ (l ∷ ys)) e′ → ⊥
    flt {y} {l = l} {ys} x x′ = fl (row m x) (λ { refl → la m x x′ (≺-ext y {l} ys) }) (row m x′) refl

    -- A row leads no root of a row after it: what leads a root is the
    -- subscription's, a timer's, or an end.
    off : ∀ {q y r e e′} → InE (start p m) q e → InE (start p m) y e′ → Row q e → Real r → RootI r → r ≺ y → Anc q r → ⊥
    off {q} {y} {r} xq xy Rq rr ri ry a with anc-root ri a | Rq
    ... | inj₁ ap | _ = anc-≼ ap rp (world-after (wo Rq) (re Rq))
    ... | inj₂ (inj₁ tq) | (_ , _ , _ , _ , eq₁ , _) = timer-plain tq eq₁
    ... | inj₂ (inj₂ (r′ , _ , eq)) | (r₁ , _ , _ , _ , eq₁ , lst) with ⊕-injʳ r₁ r′ (trans (sym eq₁) eq)
    ...   | refl with lst refl
    ...     | refl = la m xq xy (≼-≺-≺ {q} {r} {y} (anc-≼ a rr) ry)

    un : ∀ {q y w l e e′} → InE (start p m) q e → InE (start p m) y e′ → Row q e → Row y e′ → Plain l → W⁼ H (q ⊕ [ l ]) w → w ⊑ y → ⊥
    un {q} {y} {w} {l} xq xy Rq Ry pl v (zs , eq) = go xy Ry (zs , eq)
      where
        rw : Real w
        rw = real-init w zs (subst Real eq (re Ry))

        wp : W H p w
        wp = nest-in (step (inW (wo Rq)) pl) v

        aq : Anc q (q ⊕ [ l ])
        aq = up self (plain pl refl)

        -- Not at or above a root before a row.
        gr : ∀ {r y e′} → InE (start p m) y e′ → RootI r → Real r → r ≺ y → w ⊑ r → ⊥
        gr xy r-sub _ _ le = ⊑-≼ le (world-after wp rw)
        gr xy (r-timer R) rr ry le with ⊑-unit _ le
        ... | e = off xq xy Rq rr (r-timer R) ry (anc-trans aq (world-anc⁼ (subst (W⁼ H (q ⊕ [ l ])) e v)))
        gr {y = y} xy (r-fin {r₀} R) rr ry le with ⊑-snoc r₀ {last} le
        ... | inj₂ e  = off xq xy Rq rr (r-fin R) ry (anc-trans aq (world-anc⁼ (subst (W⁼ H (q ⊕ [ l ])) e v)))
        ... | inj₁ le′ = gr xy R (real-init r₀ [ last ] rr) (≺-trans {r₀} {r₀ ⊕ [ last ]} {y} (≺-ext r₀ {last} []) ry) le′

        go : ∀ {y e′} → InE (start p m) y e′ → Row y e′ → w ⊑ y → ⊥
        go xy (r₂ , l₂ , R₂ , pl₂ , refl , _) le with ⊑-snoc r₂ le
        ... | inj₂ e with anc-view (world-anc⁼ (subst (W⁼ H (q ⊕ [ l ])) e v))
        ...   | inj₁ e′ = off xq xy Rq (proj₁ (proj₂ R₂)) (proj₂ (proj₂ R₂)) (≺-ext r₂ {l₂} []) (subst (Anc q) (⊕-injˡ q r₂ e′) self)
        ...   | inj₂ (b , a , pb) with parent-fun pb (step-parent r₂ pl₂)
        ...     | refl = off xq xy Rq (proj₁ (proj₂ R₂)) (proj₂ (proj₂ R₂)) (≺-ext r₂ {l₂} []) (anc-trans aq a)
        go xy (r₂ , l₂ , R₂ , pl₂ , refl , _) le | inj₁ le₂ = gr xy (proj₂ (proj₂ R₂)) (proj₁ (proj₂ R₂)) (≺-ext r₂ {l₂} []) le₂

-- A frame played at or after its root's tick: every row at or after its
-- next slot.
burst-lb : ∀ {A t y e′} τ r i (b : Frame A t) → Real r → tick r ≤ τ + t → InE (burst τ r i b) y e′ → (r ⊕ [ ix i ]) ≼ y
burst-lb {A} = CI.lb-b {A} (λ _ → ⊥) (frame ∙ [])

-- A cold stream from a reachable subscription: finitely many rows before
-- each.
cold-reach : ∀ {A} p (m : From A 0) → Real p → ∀ {q e} (x : InE (start p m) q e) → Reach (InE (start p m)) q e
cold-reach {A} p m rp x = upTo x , λ x′ yq _ → CI.S.pre {A} (λ _ → ⊥) p rp m x x′ yq

-- A burst's end: reachable, at its root's tick.
fin-ticked : ∀ {τ t} u → Real u → tick u ≤ τ + t → Real (u ⊕ [ last ]) × tick (u ⊕ [ last ]) ≤ τ + t
fin-ticked {τ} {t} u ru le = real-snoc u plain-last ru , subst (_≤ τ + t) (sym (effect-tick u _)) le

-- A last callback's value lies before everything after it.
fin-lb : ∀ {A t y e′} τ u (m : From A (suc t)) → Real u → tick u ≤ τ + t
       → InE (frames τ ((u ⊕ [ last ]) ⊕ [ last ]) m) y e′ → ((u ⊕ [ last ]) ⊕ [ ix 0 ]) ≺ y
fin-lb {A} {y = y} τ u m ru le x =
  ≺-≼-≺ {(u ⊕ [ last ]) ⊕ [ ix 0 ]} {(u ⊕ [ last ]) ⊕ [ last ]} {y} (slot-last (u ⊕ [ last ]) 0)
    (CI.lb-f {A} (λ _ → ⊥) (frame ∙ []) τ ((u ⊕ [ last ]) ⊕ [ last ]) m (CI.fin-real {A} (λ _ → ⊥) (frame ∙ []) u ru) (CI.fin-ok {A} (λ _ → ⊥) (frame ∙ []) {τ} u ru le m) x)

-- The next frame's root, past a reachable burst's end.
next-real : ∀ τ {t′} r → Real r → tick r < τ + t′ → Real (cascadeAt (τ + t′) (r ⊕ [ last ]))
next-real τ r rr lt = CI.timer-real {⊤} (λ _ → ⊥) (frame ∙ []) τ (r ⊕ [ last ]) (real-snoc r plain-last rr) (subst (_< τ + _) (sym (effect-tick r _)) lt)
