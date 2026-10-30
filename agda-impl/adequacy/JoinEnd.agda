{-# OPTIONS --guardedness #-}

-- A BEGUN LANE'S END, READ AT ANY JOINER: two policies alike past `p`
-- but for one begun lane, which owes only its end at `p` in the one and
-- nothing in the other, unhanded.  The joiners agree but for a skip at
-- `p`, where the first owes its own end exactly when it is done.  A
-- policy's own facts say why its two readings are alike past `p`.
module adequacy.JoinEnd where

open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import denotation.Events using (Pos)
open import denotation.EmissionSet using (EmissionSet; out; end; module Joining; _≼_)
open import adequacy.Policy using (Policy; JoinP; DoneP)
open import adequacy.Skip using (Since; _≈⟨_⟩_; _⇆_; Skip)

open Policy

-- What two readings of a joiner past `p` share, the first's begun lane
-- ending at `p`.
record EndsAt {A B : Set} (PX PY : Policy A B) (p : Pos) : Set where
  field
    o→  : ∀ {q e} → outer PX q e → outer PY q e
    o←  : ∀ {q e} → outer PY q e → outer PX q e
    so  : Since p (outer PX)
    sb  : Since p (begun PX)
    sl  : ∀ {q a k e} → outer PX q (out a) → lanes PX q a k e → p ≼ k
    ln→ : ∀ {q a k e} → outer PX q (out a) → lanes PX q a k e → lanes PY q a k e
    ln← : ∀ {q a k e} → outer PX q (out a) → lanes PY q a k e → lanes PX q a k e
    ru→ : ∀ {q a} → outer PX q (out a) → runs PX q → runs PY q
    ru← : ∀ {q a} → outer PX q (out a) → runs PY q → runs PX q
    cu→ : ∀ {q a k} → outer PX q (out a) → cut PX q k → cut PY q k
    cu← : ∀ {q a k} → outer PX q (out a) → cut PY q k → cut PX q k
    ha→ : ∀ {c} → p ≼ c → hand PX c → hand PY c
    ha← : ∀ {c} → p ≼ c → hand PY c → hand PX c
    dn→ : ∀ {c} → p ≼ c → DoneP PX c → DoneP PY c
    dn← : ∀ {c} → p ≼ c → DoneP PY c → DoneP PX c
    bg→ : ∀ {k e} → begun PX k e → begun PY k e ⊎ (k ≡ p × e ≡ end)
    bg← : ∀ {k e} → begun PY k e → begun PX k e
    at  : begun PX p end
    nh  : ¬ hand PX p

module Frame {A B : Set} {PX PY : Policy A B} {p : Pos} (E : EndsAt PX PY p) where
  open EndsAt E

  -- THE FRAME: the joiner read as `Y′`, which owes `JoinP PY` and at most
  -- the joiner's own end at `p`.
  module _ (Y′ : EmissionSet B) (dp : DoneP PX p → Y′ p end) (y→ : ∀ {k e} → JoinP PY k e → Y′ k e)
           (y← : ∀ {k e} → Y′ k e → JoinP PY k e ⊎ (k ≡ p × e ≡ end × DoneP PX p)) where

    fwd′ : ∀ {k e} → JoinP PX k e → Y′ k e ⊎ Skip p k e
    fwd′ (Joining.val r)                      = inj₁ (y→ (Joining.val (o→ r)))
    fwd′ (Joining.step r)                     = inj₁ (y→ (Joining.step (o→ r)))
    fwd′ (Joining.opin r)                     = inj₁ (y→ (Joining.opin (o→ r)))
    fwd′ (Joining.oend r d)                   = inj₁ (y→ (Joining.oend (o→ r) (dn→ (so r) d)))
    fwd′ (Joining.opass r nd)                 = inj₁ (y→ (Joining.opass (o→ r) λ d → nd (dn← (so r) d)))
    fwd′ (Joining.lane r u l nc w)            = inj₁ (y→ (Joining.lane (o→ r) (ru→ r u) (ln→ r l) (λ y → nc (cu← r y)) w))
    fwd′ (Joining.lend r u l nc nh′ d)        = inj₁ (y→ (Joining.lend (o→ r) (ru→ r u) (ln→ r l) (λ y → nc (cu← r y)) (λ h → nh′ (ha← (sl r l) h)) (dn→ (sl r l) d)))
    fwd′ (Joining.lpass r u l nc nh′ nd)      = inj₁ (y→ (Joining.lpass (o→ r) (ru→ r u) (ln→ r l) (λ y → nc (cu← r y)) (λ h → nh′ (ha← (sl r l) h)) λ d → nd (dn← (sl r l) d)))
    fwd′ (Joining.hand r u l nc h)            = inj₁ (y→ (Joining.hand (o→ r) (ru→ r u) (ln→ r l) (λ y → nc (cu← r y)) (ha→ (sl r l) h)))
    fwd′ (Joining.left r u l nc i)            = inj₁ (y→ (Joining.left (o→ r) (ru→ r u) (ln→ r l) (λ y → nc (cu← r y)) i))
    fwd′ (Joining.run x w) with bg→ x
    ... | inj₁ x′            = inj₁ (y→ (Joining.run x′ w))
    ... | inj₂ (refl , refl) = ⊥-elim w
    fwd′ (Joining.rend x nh′ d) with bg→ x
    ... | inj₁ x′            = inj₁ (y→ (Joining.rend x′ (λ h → nh′ (ha← (sb x) h)) (dn→ (sb x) d)))
    ... | inj₂ (refl , refl) = inj₁ (dp d)
    fwd′ (Joining.rpass x nh′ nd) with bg→ x
    ... | inj₁ x′            = inj₁ (y→ (Joining.rpass x′ (λ h → nh′ (ha← (sb x) h)) λ d → nd (dn← (sb x) d)))
    ... | inj₂ (refl , refl) = inj₂ (refl , refl)
    fwd′ (Joining.rhand x h) with bg→ x
    ... | inj₁ x′            = inj₁ (y→ (Joining.rhand x′ (ha→ (sb x) h)))
    ... | inj₂ (refl , refl) = ⊥-elim (nh h)

    back : ∀ {k e} → JoinP PY k e → JoinP PX k e
    back (Joining.val r)                 = Joining.val (o← r)
    back (Joining.step r)                = Joining.step (o← r)
    back (Joining.opin r)                = Joining.opin (o← r)
    back (Joining.oend r d)              = Joining.oend (o← r) (dn← (so (o← r)) d)
    back (Joining.opass r nd)            = Joining.opass (o← r) λ d → nd (dn→ (so (o← r)) d)
    back (Joining.lane r u l nc w)       = Joining.lane (o← r) (ru← (o← r) u) (ln← (o← r) l) (λ y → nc (cu→ (o← r) y)) w
    back (Joining.lend r u l nc nh′ d)   = Joining.lend (o← r) (ru← (o← r) u) l′ (λ y → nc (cu→ (o← r) y)) (λ h → nh′ (ha→ (sl (o← r) l′) h)) (dn← (sl (o← r) l′) d)
      where l′ = ln← (o← r) l
    back (Joining.lpass r u l nc nh′ nd) = Joining.lpass (o← r) (ru← (o← r) u) l′ (λ y → nc (cu→ (o← r) y)) (λ h → nh′ (ha→ (sl (o← r) l′) h)) λ d → nd (dn→ (sl (o← r) l′) d)
      where l′ = ln← (o← r) l
    back (Joining.hand r u l nc h)       = Joining.hand (o← r) (ru← (o← r) u) l′ (λ y → nc (cu→ (o← r) y)) (ha← (sl (o← r) l′) h)
      where l′ = ln← (o← r) l
    back (Joining.left r u l nc i)       = Joining.left (o← r) (ru← (o← r) u) (ln← (o← r) l) (λ y → nc (cu→ (o← r) y)) i
    back (Joining.run x w)               = Joining.run (bg← x) w
    back (Joining.rend x nh′ d)          = Joining.rend (bg← x) (λ h → nh′ (ha→ (sb (bg← x)) h)) (dn← (sb (bg← x)) d)
    back (Joining.rpass x nh′ nd)        = Joining.rpass (bg← x) (λ h → nh′ (ha→ (sb (bg← x)) h)) λ d → nd (dn→ (sb (bg← x)) d)
    back (Joining.rhand x h)             = Joining.rhand (bg← x) (ha← (sb (bg← x)) h)

    bwd′ : ∀ {k e} → Y′ k e → JoinP PX k e ⊎ Skip p k e
    bwd′ r with y← r
    ... | inj₁ r′                = inj₁ (back r′)
    ... | inj₂ (refl , refl , d) = inj₁ (Joining.rend at nh d)

    frame-≈ : JoinP PX ≈⟨ p ⟩ Y′
    frame-≈ = fwd′ ⇆ bwd′

-- A joiner over nothing shows nothing.
join-empty : ∀ {A B} (P : Policy A B) → (∀ {q e} → ¬ outer P q e) → (∀ {q e} → ¬ begun P q e) → ∀ {q e} → ¬ JoinP P q e
join-empty P eo eb (Joining.val r)             = eo r
join-empty P eo eb (Joining.step r)            = eo r
join-empty P eo eb (Joining.opin r)            = eo r
join-empty P eo eb (Joining.oend r _)          = eo r
join-empty P eo eb (Joining.opass r _)         = eo r
join-empty P eo eb (Joining.lane r _ _ _ _)    = eo r
join-empty P eo eb (Joining.lend r _ _ _ _ _)  = eo r
join-empty P eo eb (Joining.lpass r _ _ _ _ _) = eo r
join-empty P eo eb (Joining.hand r _ _ _ _)    = eo r
join-empty P eo eb (Joining.left r _ _ _ _)    = eo r
join-empty P eo eb (Joining.run x _)           = eb x
join-empty P eo eb (Joining.rend x _ _)        = eb x
join-empty P eo eb (Joining.rpass x _ _)       = eb x
join-empty P eo eb (Joining.rhand x _)         = eb x
