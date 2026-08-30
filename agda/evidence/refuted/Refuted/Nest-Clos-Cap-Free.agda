-- ══════════════════════════════════════════════════════════════════
-- NO CAP PAYS FOR THE CLOSURE KEY, `capsAt`'s INCLUDED: a value's
-- closure can be made to outrun ITS OWN admitted size by a fixed
-- ratio, at a FIXED width of one, so raising the cap raises the
-- counterexample with it.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHAT THE STATEMENT SAID.  An inner observable admitted by
-- `valCaps?` at the frame's cap -- its size under `cSize`, its width
-- under `cWid` -- also passes `nestClosOK?`, which reads the same value
-- through the slot telescope.  The cap here is not arbitrary: it is
-- `frameStep L (capsAt e sl id)`, an `iterSize` tower, and the standing
-- reading was that a tower that large might simply dominate a telescope.
--
-- WHY THAT READING FAILED, AND IT IS NOT ABOUT THE TOWER'S SIZE.  The
-- deficit is PER REFERENCE, so the admitted value grows with the cap
-- and takes the deficit with it.  The family here is a `map` spine
-- whose every step is a template that merely NAMES the slot: each step
-- costs three of syntax and nine of closure, so the ratio is three to
-- one at every length and no cap is large enough to be a cap.  What the
-- premise then buys is only a LENGTH -- one member of the family is
-- admitted at every size, and the one admitted at `C` reads a closure
-- above `C`.
--
-- AND THE WIDTH CONJUNCT DOES NOT SAVE IT, which is the half worth
-- recording, because it very nearly does.  A value's slot references
-- CAN be capped by `cWid`: `outWⱽ (ofᵉ ts)` is the list's length, so
-- the parallel family -- N references side by side -- is width N and
-- runs out at `cWid`.  The spine is where that gate is absent:
-- `outWⱽ (mapᵉ f e) = outWⱽ e` and every `dW` clause is a `⊔`, so this
-- family sits at width ONE for every length.  Width bounds how many
-- references arrive TOGETHER, and the closure reading counts how many
-- there are.
--
-- WHAT DIES.  The leaf as stated, and with it the whole route of
-- reading the closure key off `valCaps?` at any cap whatever -- the
-- open question `Refuted.Nest-Clos-Flat` left standing.  What survives
-- is the key itself: a premise that bounds the value's closure has to
-- be CARRIED to the frame head, not derived there.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Nest-Clos-Cap-Free where

open import Data.Bool using (true)
open import Data.Empty using (⊥)
open import Data.Fin using () renaming (zero to fzero)
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-trans; ≤-refl; +-assoc; +-monoˡ-≤;
  +-mono-≤; *-mono-≤; m∸n+n≡m)
open import Data.Unit using (tt)
open import Data.Vec using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)

open import Decide using (≤ᵇ-true; ∧-intro)
open import Rx.Exp
  using (Ctx; Closed; Val; Fn; Ty; natᵗ; obs; ofᵉ; nat̂; strmᵗ; input; mapᵉ; sizeᵛ)
open import Rx.Slots using (Slots; shared)
open import Rx.Clos-Size using (closSizeᵉ)
open import Rx.Slot-Clos using (slotClos)
open import Rx.Frame-Width using (pWᵛ)
open import Rx.Evaluator using (Sched; EvalSt; sched-init; st-init)
open import Verify-Budget-Sufficient.Caps
  using (Caps; frameStep; capsAt; 2≤capsAt-size; capsAt-base-size; capsAt-base-wid)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (valCaps?; capsOK?; capsOK?-mono; nestClosOK?)
open import Verify-Budget-Sufficient.Caps-Bridge using (init-capsOK?)
open import Verify-Budget-Sufficient.Nest-Walk using (nestClosOK?-size; c⊑step)

----------------------------------------------------------------------
-- THE VOCABULARY: one shared slot, whose definition is bigger than the
-- reference that names it
----------------------------------------------------------------------

Γₛ : Ctx 1
Γₛ = obs natᵗ ∷ []

defn : Closed Γₛ (obs natᵗ)
defn = ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ [])

sl : Slots Γₛ
sl fzero = shared defn {ok = tt}

prog : Closed Γₛ (obs natᵗ)
prog = input fzero

U : Ty
U = obs (obs natᵗ)

----------------------------------------------------------------------
-- THE FAMILY: a `map` spine, every step a template that names the slot
----------------------------------------------------------------------

step : Fn Γₛ [] [] [] U U
step = strmᵗ (input fzero)

o : ℕ → Val Γₛ (obs U)
o zero    = ofᵉ (strmᵗ (input fzero) ∷ [])
o (suc k) = mapᵉ step (o k)

size≡ : ∀ (k : ℕ) → sizeᵛ (obs U) (o k) ≡ k * 3 + 4
size≡ zero    = refl
size≡ (suc k) = subst (λ x → 3 + sizeᵛ (obs U) (o k) ≡ x) (sym (+-assoc 3 (k * 3) 4))
                      (cong (λ x → 3 + x) (size≡ k))

clos≡ : ∀ (k : ℕ) → closSizeᵉ (slotClos sl) (o k) ≡ k * 9 + 10
clos≡ zero    = refl
clos≡ (suc k) = subst (λ x → 9 + closSizeᵉ (slotClos sl) (o k) ≡ x)
                      (sym (+-assoc 9 (k * 9) 10))
                      (cong (λ x → 9 + x) (clos≡ k))

-- THE WIDTH NEVER MOVES: `outWⱽ` walks straight through a `mapᵉ` and
-- every `dW` clause is a join, so the spine is one payload wide however
-- many references it names
wid≡ : ∀ (k : ℕ) → pWᵛ 1 sl (obs U) (o k) ≡ 1
wid≡ zero    = refl
wid≡ (suc k) = wid≡ k

----------------------------------------------------------------------
-- PICKING THE LENGTH FROM THE CAP, by a hand-rolled third so nothing
-- depends on how a division lemma is spelled
----------------------------------------------------------------------

third : ℕ → ℕ
third zero                = 0
third (suc zero)          = 0
third (suc (suc zero))    = 0
third (suc (suc (suc m))) = suc (third m)

third-lo : ∀ (m : ℕ) → third m * 3 ≤ m
third-lo zero                = z≤n
third-lo (suc zero)          = z≤n
third-lo (suc (suc zero))    = z≤n
third-lo (suc (suc (suc m))) = s≤s (s≤s (s≤s (third-lo m)))

third-hi : ∀ (m : ℕ) → m < third m * 3 + 3
third-hi zero                = s≤s z≤n
third-hi (suc zero)          = s≤s (s≤s z≤n)
third-hi (suc (suc zero))    = s≤s (s≤s (s≤s z≤n))
third-hi (suc (suc (suc m))) = s≤s (s≤s (s≤s (third-hi m)))

----------------------------------------------------------------------
-- THE STATEMENT, verbatim
----------------------------------------------------------------------

NestClosCaps : Set
NestClosCaps = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (s : Slots Γ) (id : ℕ) (L : ℕ) (sched : Sched Γ) (st : EvalSt e)
  (v : Val Γ (obs u)) →
  Sched.slots sched ≡ s →
  capsOK? (frameStep L (capsAt e s id)) sched st ≡ true →
  valCaps? (frameStep L (capsAt e s id)) s (obs u) v ≡ true →
  nestClosOK? (frameStep L (capsAt e s id)) s v ≡ true

<-irr : ∀ {a : ℕ} → suc a ≤ a → ⊥
<-irr {suc a} (s≤s le) = <-irr le

nest-clos-cap-free-absurd : NestClosCaps → ⊥
nest-clos-cap-free-absurd f = <-irr (≤-trans gap read)
  where
  c : Caps
  c = frameStep 0 (capsAt prog sl 0)

  C : ℕ
  C = Caps.cSize c

  4≤C : 4 ≤ C
  4≤C = ≤-trans (s≤s (s≤s (s≤s (s≤s z≤n)))) (capsAt-base-size prog sl 0)

  1≤W : 1 ≤ Caps.cWid c
  1≤W = ≤-trans (s≤s z≤n) (capsAt-base-wid prog sl 0)

  E : ℕ
  E = C ∸ 4

  EC : E + 4 ≡ C
  EC = m∸n+n≡m 4≤C

  k : ℕ
  k = third E

  cok : capsOK? c (sched-init prog sl) (st-init prog) ≡ true
  cok = capsOK?-mono (capsAt prog sl 0) c (sched-init prog sl) (st-init prog)
          (c⊑step (capsAt prog sl 0) 0 (2≤capsAt-size prog sl 0))
          (init-capsOK? prog sl 0)

  fits : sizeᵛ (obs U) (o k) ≤ C
  fits = subst (_≤ C) (sym (size≡ k))
           (subst (k * 3 + 4 ≤_) EC (+-monoˡ-≤ 4 (third-lo E)))

  vc : valCaps? c sl (obs U) (o k) ≡ true
  vc = ∧-intro (≤ᵇ-true (sizeᵛ (obs U) (o k)) C fits)
               (≤ᵇ-true (pWᵛ 1 sl (obs U) (o k)) (Caps.cWid c)
                        (subst (_≤ Caps.cWid c) (sym (wid≡ k)) 1≤W))

  read : k * 9 + 10 ≤ C
  read = subst (_≤ C) (clos≡ k)
           (nestClosOK?-size c sl (o k)
             (f {e = prog} sl 0 0 (sched-init prog sl) (st-init prog) (o k) refl cok vc))

  gap : suc C ≤ k * 9 + 10
  gap = subst (λ x → suc x ≤ k * 9 + 10) EC
          (≤-trans (+-monoˡ-≤ 4 (third-hi E))
          (≤-trans (≤-reflexive-shift)
                   (+-mono-≤ (*-mono-≤ (≤-refl {k}) (s≤s (s≤s (s≤s z≤n))))
                             (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))) 
    where
    ≤-reflexive-shift : (k * 3 + 3) + 4 ≤ k * 3 + 7
    ≤-reflexive-shift = subst (λ x → (k * 3 + 3) + 4 ≤ x) (+-assoc (k * 3) 3 4) ≤-refl
