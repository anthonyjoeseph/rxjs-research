{-# OPTIONS --guardedness #-}

-- SPIKE 7: KEPT THROUGH THE ORDER-DEPENDENT OPERATORS.  The content
-- obligation compares residuals by what they hold (`Has`), and a scan's
-- or a takeWhile's output depends on the ORDER its source delivers in,
-- not only on what it holds.  So two facts are needed of each, and both
-- are stated here over streams alone, with no machine in them.
--
-- CONGRUENCE: two strict streams holding the same things give a scan, or
-- a takeWhile, outputs holding the same things.  Same set, strictly
-- ordered, is the same trace.
--
-- THE STEP: a child whose residual pops its head `(k , a)` leaves a scan
-- popping `(k , f z a)` with its accumulator moved to `f z a`; and a
-- takeWhile holding what `taking` holds at `(k , a)`, passing on a
-- value it keeps, and stopping as `taking` stops on one it fails.
--
-- `Strict` is what both need, and it is `Ordered` and `Steady` together,
-- the two order invariants the denotation already proves of a fresh
-- subscription.  What the content side owes in their place is that every
-- node's ghost meaning, at a quiet configuration, is `Ordered` and
-- `Steady`: an order invariant of the same kind as spike 6's `least`, by
-- a walk over `gh` with the `ordered-`/`steady-` lemmas per stream
-- function.
--
-- The machine matches these shapes as they stand: its `rise` through a
-- scan rebuilds it at `f z a` and passes `f z a` up, and through a
-- takeWhile it keeps the node on a value it keeps, and on one it fails
-- owes exactly what `taking` still holds past what it shows.
module spike.StateTree3Kept where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import denotation.MonotonicList.Events using (Events; Events∞; Pos; out; skip; end; hush; idle; _<ᵖ_; <ᵖ-trans; <ᵖ-irrefl; <ᵖ-asym; <ᵖ-split)
open import denotation.MonotonicList using (scanᴱ; takeWhileᴱ; taking)
open import adequacy.Placed.Order using (Ordered; ordered; Steady; steady; Atop; Past)
open import spike.StateTree3Ghost using (Has; atOut; atEnd; pastOut; pastSkip)

open Events∞

------------------------------------------------------------------------
-- Strict streams

data Reach {A : Set} : Events A → Events A → Set where
  stay   : ∀ {e} → Reach e e
  byOut  : ∀ {k a r e′} → Reach (force r) e′ → Reach (out k a r) e′
  bySkip : ∀ {k r e′} → Reach (force r) e′ → Reach (skip k r) e′

-- Everything `e` holds is strictly past `k`.
Past⁺ : ∀ {A} → Pos → Events A → Set
Past⁺ k e = ∀ {q b} → Has e q b → k <ᵖ q ≡ true

-- Everything after a value is strictly past it.
Strict : ∀ {A} → Events A → Set
Strict e = ∀ {k a r} → Reach e (out k a r) → Past⁺ k (force r)

_⊆_ : ∀ {A} → Events A → Events A → Set
e ⊆ e₁ = ∀ {q b} → Has e q b → Has e₁ q b

strict-out : ∀ {A k a} {r : Events∞ A} → Strict (out k a r) → Strict (force r)
strict-out s h = s (byOut h)

strict-skip : ∀ {A k} {r : Events∞ A} → Strict (skip k r) → Strict (force r)
strict-skip s h = s (bySkip h)

unskip : ∀ {A k} {r : Events∞ A} {q b} → Has (skip k r) q b → Has (force r) q b
unskip (pastSkip h) = h

t≢f : true ≡ false → ⊥
t≢f ()

from-head : ∀ {A k a} {r : Events∞ A} {q b} → Strict (out k a r) → Has (out k a r) q b → k ≡ q ⊎ k <ᵖ q ≡ true
from-head s atOut       = inj₁ refl
from-head s (pastOut h) = inj₂ (s stay h)

not-both : ∀ k k′ → k′ <ᵖ k ≡ true → k ≡ k′ ⊎ k <ᵖ k′ ≡ true → ⊥
not-both k .k lt (inj₁ refl) = t≢f (trans (sym lt) (<ᵖ-irrefl k))
not-both k k′ lt (inj₂ gt)   = t≢f (trans (sym gt) (<ᵖ-asym k′ k lt))

------------------------------------------------------------------------
-- Skips to the first event

data Skips {A : Set} : Events A → Events A → Set where
  none : ∀ {e} → Skips e e
  more : ∀ {k r e′} → Skips (force r) e′ → Skips (skip k r) e′

skips-has : ∀ {A} {e e′ : Events A} {q b} → Skips e e′ → Has e′ q b → Has e q b
skips-has none     h = h
skips-has (more s) h = pastSkip (skips-has s h)

skips-has⁻ : ∀ {A} {e e′ : Events A} {q b} → Skips e e′ → Has e q b → Has e′ q b
skips-has⁻ none     h            = h
skips-has⁻ (more s) (pastSkip h) = skips-has⁻ s h

skips-reach : ∀ {A} {e e′ x : Events A} → Skips e e′ → Reach e′ x → Reach e x
skips-reach none     h = h
skips-reach (more s) h = bySkip (skips-reach s h)

skips-strict : ∀ {A} {e e′ : Events A} → Skips e e′ → Strict e → Strict e′
skips-strict sk s h = s (skips-reach sk h)

-- A strict stream holding no more than `out k a r`, and its head, reaches
-- that head by skips alone.
first-out : ∀ {A k a} {r : Events∞ A} {e₁ : Events A} → Strict (out k a r) → Strict e₁ → e₁ ⊆ out k a r → Has e₁ k (just a)
          → Σ (Events∞ A) λ r₁ → Skips e₁ (out k a r₁)
first-out s s₁ sup atOut                       = _ , none
first-out {k = k} s s₁ sup (pastOut {k = k′} h) = ⊥-elim (not-both k k′ (s₁ stay h) (from-head s (sup atOut)))
first-out s s₁ sup (pastSkip h) with first-out s (λ x → s₁ (bySkip x)) (λ x → sup (pastSkip x)) h
... | r₁ , sk = r₁ , more sk

first-end : ∀ {A k} {e₁ : Events A} → e₁ ⊆ end k → Has e₁ k nothing → Skips e₁ (end k)
first-end sup atEnd        = none
first-end sup (pastOut h)  with sup atOut
... | ()
first-end sup (pastSkip h) = more (first-end (λ x → sup (pastSkip x)) h)

-- What follows the head, both ways.
rest⊆ : ∀ {A k a} {r r₁ : Events∞ A} {e₁} → Strict (out k a r) → Skips e₁ (out k a r₁) → out k a r ⊆ e₁ → force r ⊆ force r₁
rest⊆ {k = k} s sk sub h with skips-has⁻ sk (sub (pastOut h))
... | atOut      = ⊥-elim (t≢f (trans (sym (s stay h)) (<ᵖ-irrefl k)))
... | pastOut h′ = h′

rest⊇ : ∀ {A k a} {r r₁ : Events∞ A} {e₁} → Strict (out k a r₁) → Skips e₁ (out k a r₁) → e₁ ⊆ out k a r → force r₁ ⊆ force r
rest⊇ {k = k} s₁ sk sup h with sup (skips-has sk (pastOut h))
... | atOut      = ⊥-elim (t≢f (trans (sym (s₁ stay h)) (<ᵖ-irrefl k)))
... | pastOut h′ = h′

------------------------------------------------------------------------
-- Congruence

scan-skips : ∀ {A B} (f : B → A → B) z {e e′ : Events A} {q b} → Skips e e′ → Has (scanᴱ f z e′) q b → Has (scanᴱ f z e) q b
scan-skips f z none     h = h
scan-skips f z (more s) h = pastSkip (scan-skips f z s h)

scan⊆ : ∀ {A B} (f : B → A → B) z {e e₁ : Events A} → Strict e → Strict e₁ → e ⊆ e₁ → e₁ ⊆ e → scanᴱ f z e ⊆ scanᴱ f z e₁
scan⊆ f z {out k a r} s s₁ sub sup atOut with first-out s s₁ sup (sub atOut)
... | r₁ , sk = scan-skips f z sk atOut
scan⊆ f z {out k a r} s s₁ sub sup (pastOut h) with first-out s s₁ sup (sub atOut)
... | r₁ , sk = scan-skips f z sk (pastOut (scan⊆ f (f z a) (strict-out s) (strict-out (skips-strict sk s₁))
                  (rest⊆ s sk sub) (rest⊇ (skips-strict sk s₁) sk sup) h))
scan⊆ f z {skip k r}  s s₁ sub sup (pastSkip h) = scan⊆ f z (strict-skip s) s₁ (λ x → sub (pastSkip x)) (λ x → unskip (sup x)) h
scan⊆ f z {end k}     s s₁ sub sup atEnd = scan-skips f z (first-end sup (sub atEnd)) atEnd

take-skips : ∀ {A} i (p : A → Bool) {e e′ : Events A} {q b} → Skips e e′ → Has (takeWhileᴱ i p e′) q b → Has (takeWhileᴱ i p e) q b
take-skips i p none     h = h
take-skips i p (more s) h = pastSkip (take-skips i p s h)

mutual
  take⊆ : ∀ {A} i (p : A → Bool) {e e₁ : Events A} → Strict e → Strict e₁ → e ⊆ e₁ → e₁ ⊆ e → takeWhileᴱ i p e ⊆ takeWhileᴱ i p e₁
  take⊆ i p {out k a r} s s₁ sub sup h with first-out s s₁ sup (sub atOut)
  ... | r₁ , sk = take-skips i p sk (taking⊆ i p k a (p a) s (skips-strict sk s₁) (rest⊆ s sk sub) (rest⊇ (skips-strict sk s₁) sk sup) h)
  take⊆ i p {skip k r} s s₁ sub sup (pastSkip h) = take⊆ i p (strict-skip s) s₁ (λ x → sub (pastSkip x)) (λ x → unskip (sup x)) h
  take⊆ i p {end k}    s s₁ sub sup atEnd = take-skips i p (first-end sup (sub atEnd)) atEnd

  taking⊆ : ∀ {A} i (p : A → Bool) k a c {r r₁ : Events∞ A} → Strict (out k a r) → Strict (out k a r₁)
          → force r ⊆ force r₁ → force r₁ ⊆ force r → taking i p k a c r ⊆ taking i p k a c r₁
  taking⊆ i    p k a true  s s₁ sub sup atOut           = atOut
  taking⊆ i    p k a true  s s₁ sub sup (pastOut h)     = pastOut (take⊆ i p (strict-out s) (strict-out s₁) sub sup h)
  taking⊆ true p k a false s s₁ sub sup atOut           = atOut
  taking⊆ true p k a false s s₁ sub sup (pastOut atEnd) = pastOut atEnd
  taking⊆ false p k a false s s₁ sub sup atEnd          = atEnd

------------------------------------------------------------------------
-- The step: a residual pops its head

rest : ∀ {A} → Events A → Events∞ A
rest e .force = e
rest e .cut   = idle

put : ∀ {A} → Pos → A → Events A → Events A
put k a e = out k a (rest e)

-- `e` holds `(k , a)`, then what `e′` holds, all of it past `k`.
Pops : ∀ {A} → Pos → A → Events A → Events A → Set
Pops k a e e′ = Past⁺ k e′ × e ⊆ put k a e′ × put k a e′ ⊆ e

strict-put : ∀ {A k a} {e′ : Events A} → Past⁺ k e′ → Strict e′ → Strict (put k a e′)
strict-put pk s stay      = pk
strict-put pk s (byOut h) = s h

scan-pos : ∀ {A B} (f : B → A → B) z (e : Events A) {q b} → Has (scanᴱ f z e) q b → Σ (Maybe A) (Has e q)
scan-pos f z (out k a r) atOut        = _ , atOut
scan-pos f z (out k a r) (pastOut h)  with scan-pos f (f z a) (force r) h
... | _ , h′ = _ , pastOut h′
scan-pos f z (skip k r)  (pastSkip h) with scan-pos f z (force r) h
... | _ , h′ = _ , pastSkip h′
scan-pos f z (end k)     atEnd        = _ , atEnd

scan-put : ∀ {A B} (f : B → A → B) z k a (e′ : Events A) → scanᴱ f z (put k a e′) ⊆ put k (f z a) (scanᴱ f (f z a) e′)
scan-put f z k a e′ atOut       = atOut
scan-put f z k a e′ (pastOut h) = pastOut h

scan-put⁻ : ∀ {A B} (f : B → A → B) z k a (e′ : Events A) → put k (f z a) (scanᴱ f (f z a) e′) ⊆ scanᴱ f z (put k a e′)
scan-put⁻ f z k a e′ atOut       = atOut
scan-put⁻ f z k a e′ (pastOut h) = pastOut h

pops-scan : ∀ {A B} (f : B → A → B) z {k a} {e e′ : Events A} → Strict e → Strict e′ → Pops k a e e′
          → Pops k (f z a) (scanᴱ f z e) (scanᴱ f (f z a) e′)
pops-scan f z {k} {a} {e} {e′} s s′ (pk , sub , sup) =
    (λ h → pk (proj₂ (scan-pos f (f z a) e′ h)))
  , (λ h → scan-put f z k a e′ (scan⊆ f z s s₀ sub sup h))
  , (λ h → scan⊆ f z s₀ s sup sub (scan-put⁻ f z k a e′ h))
  where s₀ = strict-put pk s′

-- A takeWhile holds what `taking` holds at the popped head.
pops-take : ∀ {A} i (p : A → Bool) {k a} {e e′ : Events A} → Strict e → Strict e′ → Pops k a e e′
          → takeWhileᴱ i p e ⊆ taking i p k a (p a) (rest e′) × taking i p k a (p a) (rest e′) ⊆ takeWhileᴱ i p e
pops-take i p s s′ (pk , sub , sup) = take⊆ i p s s₀ sub sup , take⊆ i p s₀ s sup sub
  where s₀ = strict-put pk s′

-- ... so a value it keeps is popped through it,
passes : ∀ {A} i (p : A → Bool) k a c (e′ : Events A) → c ≡ true
       → taking i p k a c (rest e′) ⊆ put k a (takeWhileᴱ i p e′) × put k a (takeWhileᴱ i p e′) ⊆ taking i p k a c (rest e′)
passes i p k a .true e′ refl = (λ { atOut → atOut ; (pastOut h) → pastOut h }) , (λ { atOut → atOut ; (pastOut h) → pastOut h })

-- and one it fails ends it, whatever followed.
stops : ∀ {A} i (p : A → Bool) k a c (e′ e″ : Events A) → c ≡ false → taking i p k a c (rest e′) ⊆ taking i p k a false (rest e″)
stops true  p k a .false e′ e″ refl atOut             = atOut
stops true  p k a .false e′ e″ refl (pastOut atEnd)   = pastOut atEnd
stops false p k a .false e′ e″ refl atEnd             = atEnd

------------------------------------------------------------------------
-- Strict is Ordered and Steady

Lead : ∀ {A} → Pos → Events A → Set
Lead lo (out h _ _) = lo <ᵖ h ≡ true
Lead lo (skip h _)  = lo <ᵖ h ≡ true
Lead lo (end h)     = lo <ᵖ h ≡ true
Lead lo hush        = ⊤

lead-past : ∀ {A k} (x : Events A) → Past k x → Lead k x
lead-past (out h _ _) p = proj₁ p
lead-past (skip h _)  p = proj₁ p
lead-past (end h)     p = proj₁ p
lead-past hush        p = p

lead-next : ∀ {A lo h} → lo <ᵖ h ≡ true → (x : Events A) → Atop h x → Lead lo x
lead-next {lo = lo} {h} l x t = go x t
  where
    up : ∀ h′ → h′ <ᵖ h ≡ false → lo <ᵖ h′ ≡ true
    up h′ t′ with <ᵖ-split h h′ t′
    ... | inj₁ lt   = <ᵖ-trans lo h h′ l lt
    ... | inj₂ refl = l
    go : (x : Events _) → Atop h x → Lead lo x
    go (out h′ _ _) t′ = up h′ t′
    go (skip h′ _)  t′ = up h′ t′
    go (end h′)     t′ = up h′ t′
    go hush         t′ = t′

over : ∀ {A lo} (x : Events A) → Ordered x → Lead lo x → Past⁺ lo x
over (out h a r) o l atOut        = l
over {lo = lo} (out h a r) o l (pastOut y)  = over {lo = lo} (force r) (proj₂ (ordered o)) (lead-next l (force r) (proj₁ (ordered o))) y
over {lo = lo} (skip h r)  o l (pastSkip y) = over {lo = lo} (force r) (proj₂ (ordered o)) (lead-next l (force r) (proj₁ (ordered o))) y
over (end h)     o l atEnd        = l

strict-of : ∀ {A} (e : Events A) → Ordered e → Steady e → Strict e
strict-of (out k a r) o st stay       = over (force r) (proj₂ (ordered o)) (lead-past (force r) (proj₁ (steady st)))
strict-of (out k a r) o st (byOut h)  = strict-of (force r) (proj₂ (ordered o)) (proj₂ (steady st)) h
strict-of (skip k r)  o st (bySkip h) = strict-of (force r) (proj₂ (ordered o)) (proj₂ (steady st)) h
