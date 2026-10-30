{-# OPTIONS --guardedness #-}

-- A BEGUN LANE'S END OR VALUE, READ AT ANY JOINER: two policies alike
-- past `p` but for one begun lane, which owes its end, or a value, at `p`
-- in the one and not in the other.  For an end, unhanded, the joiners
-- agree but for a skip at `p`, where the first owes its own end exactly
-- when it is done; for a value, the first owes it at `p` over the second.
-- A policy's own facts say why its two readings are alike past `p`.
module adequacy.JoinEnd where

open import Data.Empty using (⊥-elim)
open import Data.List using ([]; _++_; [_])
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import denotation.Events using (Pos; ix)
open import denotation.EmissionSet using (EmissionSet; Ev; Work; out; end; module Joining; _≺_; _≼_)
open import denotation.Laws.Modulus using (≺-trans; ≺-ext)
open import adequacy.Policy using (Policy; JoinP; DoneP)
open import adequacy.Rows using (Plus; old; new; _≃_; _⇄_)
open import adequacy.Skip using (After; Since; _≈⟨_⟩_; _⇆_; Skip)

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

-- A joiner's rows lie strictly past `p` where its outer's, its begun
-- lanes' and each value's lane's do.
after-join : ∀ {A B} {p} (P : Policy A B) → After p (outer P) → After p (begun P)
           → (∀ {q a k e} → outer P q (out a) → lanes P q a k e → p ≺ k) → After p (JoinP P)
after-join {p = p} P ao ab al (Joining.val {q} r)              = ≺-trans {p} {q} {q ++ [ ix 0 ]} (ao r) (≺-ext q [])
after-join P ao ab al (Joining.step r)                         = ao r
after-join P ao ab al (Joining.opin r)                         = ao r
after-join P ao ab al (Joining.oend r _)                       = ao r
after-join P ao ab al (Joining.opass r _)                      = ao r
after-join P ao ab al (Joining.lane r _ l _ _)                 = al r l
after-join P ao ab al (Joining.lend r _ l _ _ _)               = al r l
after-join P ao ab al (Joining.lpass r _ l _ _ _)              = al r l
after-join {p = p} P ao ab al (Joining.hand {c = c} r _ l _ _) = ≺-trans {p} {c} {c ++ [ ix 0 ]} (al r l) (≺-ext c [])
after-join P ao ab al (Joining.left r _ l _ _)                 = al r l
after-join P ao ab al (Joining.run x _)                        = ab x
after-join P ao ab al (Joining.rend x _ _)                     = ab x
after-join P ao ab al (Joining.rpass x _ _)                    = ab x
after-join {p = p} P ao ab al (Joining.rhand {c} x _)         = ≺-trans {p} {c} {c ++ [ ix 0 ]} (ab x) (≺-ext c [])

-- A BEGUN LANE'S VALUE, READ AT ANY JOINER: two policies alike but for one
-- begun lane, which owes a value `v` at `p` in the one and not in the
-- other, every other part strictly past `p`.
record ValAt {A B : Set} (PX PY : Policy A B) (p : Pos) (v : Ev B) : Set where
  field
    o→  : ∀ {q e} → outer PX q e → outer PY q e
    o←  : ∀ {q e} → outer PY q e → outer PX q e
    ao  : After p (outer PY)
    ab  : After p (begun PY)
    al  : ∀ {q a k e} → outer PY q (out a) → lanes PY q a k e → p ≺ k
    ln→ : ∀ {q a k e} → outer PX q (out a) → lanes PX q a k e → lanes PY q a k e
    ln← : ∀ {q a k e} → outer PX q (out a) → lanes PY q a k e → lanes PX q a k e
    ru→ : ∀ {q a} → outer PX q (out a) → runs PX q → runs PY q
    ru← : ∀ {q a} → outer PX q (out a) → runs PY q → runs PX q
    cu→ : ∀ {q a k} → outer PX q (out a) → cut PX q k → cut PY q k
    cu← : ∀ {q a k} → outer PX q (out a) → cut PY q k → cut PX q k
    ha→ : ∀ {c} → hand PX c → hand PY c
    ha← : ∀ {c} → hand PY c → hand PX c
    dn→ : ∀ {c} → DoneP PX c → DoneP PY c
    dn← : ∀ {c} → DoneP PY c → DoneP PX c
    bg→ : ∀ {k e} → begun PX k e → begun PY k e ⊎ (k ≡ p × e ≡ v)
    bg← : ∀ {k e} → begun PY k e → begun PX k e
    at  : begun PX p v
    wk  : Work v

-- The joiner owes the value at `p` over what it owes without it.
module Val {A B : Set} {PX PY : Policy A B} {p : Pos} {v : Ev B} (V : ValAt PX PY p v) where
  open ValAt V

  to′ : ∀ {k e} → JoinP PX k e → Plus (JoinP PY) p v k e
  to′ (Joining.val r)                 = old (Joining.val (o→ r))
  to′ (Joining.step r)                = old (Joining.step (o→ r))
  to′ (Joining.opin r)                = old (Joining.opin (o→ r))
  to′ (Joining.oend r d)              = old (Joining.oend (o→ r) (dn→ d))
  to′ (Joining.opass r nd)            = old (Joining.opass (o→ r) λ d → nd (dn← d))
  to′ (Joining.lane r u l nc w)       = old (Joining.lane (o→ r) (ru→ r u) (ln→ r l) (λ y → nc (cu← r y)) w)
  to′ (Joining.lend r u l nc nh d)    = old (Joining.lend (o→ r) (ru→ r u) (ln→ r l) (λ y → nc (cu← r y)) (λ h → nh (ha← h)) (dn→ d))
  to′ (Joining.lpass r u l nc nh nd)  = old (Joining.lpass (o→ r) (ru→ r u) (ln→ r l) (λ y → nc (cu← r y)) (λ h → nh (ha← h)) λ d → nd (dn← d))
  to′ (Joining.hand r u l nc h)       = old (Joining.hand (o→ r) (ru→ r u) (ln→ r l) (λ y → nc (cu← r y)) (ha→ h))
  to′ (Joining.left r u l nc i)       = old (Joining.left (o→ r) (ru→ r u) (ln→ r l) (λ y → nc (cu← r y)) i)
  to′ (Joining.run x w) with bg→ x
  ... | inj₁ x′            = old (Joining.run x′ w)
  ... | inj₂ (refl , refl) = new
  to′ (Joining.rend x nh d) with bg→ x
  ... | inj₁ x′          = old (Joining.rend x′ (λ h → nh (ha← h)) (dn→ d))
  ... | inj₂ (refl , eq) = ⊥-elim (subst Work (sym eq) wk)
  to′ (Joining.rpass x nh nd) with bg→ x
  ... | inj₁ x′          = old (Joining.rpass x′ (λ h → nh (ha← h)) λ d → nd (dn← d))
  ... | inj₂ (refl , eq) = ⊥-elim (subst Work (sym eq) wk)
  to′ (Joining.rhand x h) with bg→ x
  ... | inj₁ x′          = old (Joining.rhand x′ (ha→ h))
  ... | inj₂ (refl , eq) = ⊥-elim (subst Work (sym eq) wk)

  back : ∀ {k e} → JoinP PY k e → JoinP PX k e
  back (Joining.val r)                 = Joining.val (o← r)
  back (Joining.step r)                = Joining.step (o← r)
  back (Joining.opin r)                = Joining.opin (o← r)
  back (Joining.oend r d)              = Joining.oend (o← r) (dn← d)
  back (Joining.opass r nd)            = Joining.opass (o← r) λ d → nd (dn→ d)
  back (Joining.lane r u l nc w)       = Joining.lane (o← r) (ru← (o← r) u) (ln← (o← r) l) (λ y → nc (cu→ (o← r) y)) w
  back (Joining.lend r u l nc nh d)    = Joining.lend (o← r) (ru← (o← r) u) (ln← (o← r) l) (λ y → nc (cu→ (o← r) y)) (λ h → nh (ha→ h)) (dn← d)
  back (Joining.lpass r u l nc nh nd)  = Joining.lpass (o← r) (ru← (o← r) u) (ln← (o← r) l) (λ y → nc (cu→ (o← r) y)) (λ h → nh (ha→ h)) λ d → nd (dn→ d)
  back (Joining.hand r u l nc h)       = Joining.hand (o← r) (ru← (o← r) u) (ln← (o← r) l) (λ y → nc (cu→ (o← r) y)) (ha← h)
  back (Joining.left r u l nc i)       = Joining.left (o← r) (ru← (o← r) u) (ln← (o← r) l) (λ y → nc (cu→ (o← r) y)) i
  back (Joining.run x w)               = Joining.run (bg← x) w
  back (Joining.rend x nh d)           = Joining.rend (bg← x) (λ h → nh (ha→ h)) (dn← d)
  back (Joining.rpass x nh nd)         = Joining.rpass (bg← x) (λ h → nh (ha→ h)) λ d → nd (dn→ d)
  back (Joining.rhand x h)             = Joining.rhand (bg← x) (ha← h)

  from′ : ∀ {k e} → Plus (JoinP PY) p v k e → JoinP PX k e
  from′ (old r) = back r
  from′ new     = Joining.run at wk

  val-≃ : JoinP PX ≃ Plus (JoinP PY) p v
  val-≃ = to′ ⇄ from′

  after-y : After p (JoinP PY)
  after-y = after-join {p = p} PY ao ab al
