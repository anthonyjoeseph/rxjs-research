{-# OPTIONS --guardedness #-}

-- A LANE'S END, READ AT ITS MERGE: a lane owing only its end at `p`,
-- every other part of the merge strictly past `p`.  Off `p` the merge
-- owes what it owes with the lane gone; at `p` it owes its own end when
-- every other part owes nothing, and a skip otherwise.
module adequacy.LaneEnd where

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _ʳ++_)
open import Data.Product using (_×_; _,_)
open import Data.Bool using (Bool; T)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import denotation.Events using (Pos)
open import denotation.EmissionSet using (EmissionSet; end; _≼_)
open import denotation.Laws.Modulus using (≺→≼; ≼-refl)
open import adequacy.Rows using (∅; Plus; old; new; Gone; Lanes; Each; module Flat)
open import adequacy.Up using (any-ʳ++; any-ʳ++ˡ; any-ʳ++ʳ; all-ʳ++; all-ʳ++⁻)
open import adequacy.Bound using (Empty)
open import adequacy.Skip using (After; Since; _≈⟨_⟩_; _⇆_; Skip; after-since; since-lanes; lane-since; since-flat)

-- A lane's rows, by `c`, each: one of them, by `c`.
gone-any : ∀ {B} (Ls : List (EmissionSet B)) {c k e} → Each (λ t → Gone t c) Ls → Lanes Ls k e → k ≼ c
gone-any (_ ∷ _)  (g , _)  (inj₁ r) = g r
gone-any (_ ∷ Ls) {c} (_ , gs) (inj₂ x) = gone-any Ls {c} gs x

after-lanes : ∀ {B} {p} (Ls : List (EmissionSet B)) → Each (After p) Ls → ∀ {k e} → Lanes Ls k e → ¬ k ≼ p
after-lanes (_ ∷ _)  (a , _)  (inj₁ r) kp = kp (a r)
after-lanes {p = p} (_ ∷ Ls) (_ , as) (inj₂ x) kp = after-lanes {p = p} Ls as x kp

module _ {A B : Set} (L : A → Pos → EmissionSet B) {p : Pos} {O : EmissionSet A} {d : Bool} (Pre Post : List (EmissionSet B)) {t₀ : EmissionSet B}
         (ao : After p O) (apre : Each (After p) Pre) (apost : Each (After p) Post) (e₀ : Empty t₀) where

  LX = Pre ʳ++ (Plus t₀ p end ∷ Post)
  LY = Pre ʳ++ (∅ ∷ Post)
  X  = Flat.JoinT L O d LX
  Y  = Flat.JoinT L O d LY

  so : Since p O
  so {q} {e} r = ≺→≼ {p} {q} (ao {q} {e} r)

  sx : Each (Since p) LX
  sx = all-ʳ++ Pre (after-since Pre apre) (hole , after-since Post apost)
    where
      hole : Since p (Plus t₀ p end)
      hole (old r) = ⊥-elim (e₀ r)
      hole new     = ≼-refl {p}

  sy : Each (Since p) LY
  sy = all-ʳ++ Pre (after-since Pre apre) ((λ ()) , after-since Post apost)

  lanes-xy : ∀ {k e} → Lanes LX k e → Lanes LY k e ⊎ (k ≡ p × e ≡ end)
  lanes-xy x with any-ʳ++ Pre x
  ... | inj₁ a              = inj₁ (any-ʳ++ˡ Pre a)
  ... | inj₂ (inj₁ (old r)) = ⊥-elim (e₀ r)
  ... | inj₂ (inj₁ new)     = inj₂ (refl , refl)
  ... | inj₂ (inj₂ b)       = inj₁ (any-ʳ++ʳ Pre (inj₂ b))

  lanes-yx : ∀ {k e} → Lanes LY k e → Lanes LX k e
  lanes-yx x with any-ʳ++ Pre x
  ... | inj₁ a        = any-ʳ++ˡ Pre a
  ... | inj₂ (inj₁ ())
  ... | inj₂ (inj₂ b) = any-ʳ++ʳ Pre (inj₂ b)

  done-xy : ∀ c → p ≼ c → Flat.Done L O d LX c → Flat.Done L O d LY c
  done-xy c pc ((g , ls) , h) with all-ʳ++⁻ Pre ls
  ... | gp , (_ , gq) = (g , all-ʳ++ Pre gp ((λ ()) , gq)) , h

  done-yx : ∀ c → p ≼ c → Flat.Done L O d LY c → Flat.Done L O d LX c
  done-yx c pc ((g , ls) , h) with all-ʳ++⁻ Pre ls
  ... | gp , (_ , gq) = (g , all-ʳ++ Pre gp (hole , gq)) , h
    where
      hole : Gone (Plus t₀ p end) c
      hole (old r) = ⊥-elim (e₀ r)
      hole new     = pc

  -- The merge done at `p` exactly when every other part owes nothing.
  done-at : T d → Each Empty Pre → Each Empty Post → Flat.Done L O d LX p
  done-at td ep eq = (inj₁ td , all-ʳ++ Pre (gone Pre ep) (hole , gone Post eq)) , λ {q} r _ lt _ → ⊥-elim (≺→≼ {p} {q} (ao r) lt)
    where
      gone : ∀ (Ls : List (EmissionSet B)) → Each Empty Ls → Each (λ t → Gone t p) Ls
      gone []       _        = _
      gone (_ ∷ Ls) (n , ns) = (λ r → ⊥-elim (n r)) , gone Ls ns
      hole : Gone (Plus t₀ p end) p
      hole (old r) = ⊥-elim (e₀ r)
      hole new     = ≼-refl {p}

  outer-owes : ¬ T d → ¬ Flat.Done L O d LX p
  outer-owes nd ((inj₁ td , _) , _)             = nd td
  outer-owes nd ((inj₂ (c₀ , x , c₀p) , _) , _) = c₀p (ao x)

  lanes-owe : ¬ Empty (Lanes Pre) ⊎ ¬ Empty (Lanes Post) → ¬ Flat.Done L O d LX p
  lanes-owe w ((_ , ls) , _) with all-ʳ++⁻ Pre ls
  ... | gp , (_ , gq) with w
  ... | inj₁ ne = ne λ x → after-lanes {p = p} Pre apre x (gone-any Pre {p} gp x)
  ... | inj₂ ne = ne λ x → after-lanes {p = p} Post apost x (gone-any Post {p} gq x)

  -- THE FRAME: the merge with the lane read as `Y′`, which owes `Y` and
  -- at most the merge's own end at `p`.
  module _ (Y′ : EmissionSet B) (dp : Flat.Done L O d LX p → Y′ p end) (y→ : ∀ {k e} → Y k e → Y′ k e)
           (y← : ∀ {k e} → Y′ k e → Y k e ⊎ (k ≡ p × e ≡ end × Flat.Done L O d LX p)) where

    fwd′ : ∀ {k e} → X k e → Y′ k e ⊎ Skip p k e
    fwd′ (Flat.val r)    = inj₁ (y→ (Flat.val r))
    fwd′ (Flat.step r)   = inj₁ (y→ (Flat.step r))
    fwd′ (Flat.oend {c} r d)   = inj₁ (y→ (Flat.oend r (done-xy c (so r) d)))
    fwd′ (Flat.opass {c} r nd) = inj₁ (y→ (Flat.opass r λ d → nd (done-yx c (so r) d)))
    fwd′ (Flat.lane r ru l nc w) = inj₁ (y→ (Flat.lane r ru l nc w))
    fwd′ (Flat.lend {q} {a} {c} r ru l nc dn)   = inj₁ (y→ (Flat.lend r ru l nc (done-xy c (lane-since L {d = d} {O = O} {Ls = LX} {q = q} {a = a} so r l) dn)))
    fwd′ (Flat.lpass {q} {a} {c} r ru l nc nd) = inj₁ (y→ (Flat.lpass r ru l nc λ dn → nd (done-yx c (lane-since L {d = d} {O = O} {Ls = LX} {q = q} {a = a} so r l) dn)))
    fwd′ (Flat.left _ _ _ () _)
    fwd′ (Flat.run x w) with lanes-xy x
    ... | inj₁ x′           = inj₁ (y→ (Flat.run x′ w))
    ... | inj₂ (refl , refl) = ⊥-elim w
    fwd′ (Flat.rend {c} x d) with lanes-xy x
    ... | inj₁ x′           = inj₁ (y→ (Flat.rend x′ (done-xy c (since-lanes LX sx x) d)))
    ... | inj₂ (refl , refl) = inj₁ (dp d)
    fwd′ (Flat.rpass {c} x nd) with lanes-xy x
    ... | inj₁ x′           = inj₁ (y→ (Flat.rpass x′ λ d → nd (done-yx c (since-lanes LX sx x) d)))
    ... | inj₂ (refl , refl) = inj₂ (refl , refl)

    back : ∀ {k e} → Y k e → X k e
    back (Flat.val r)    = Flat.val r
    back (Flat.step r)   = Flat.step r
    back (Flat.oend {c} r d)   = Flat.oend r (done-yx c (so r) d)
    back (Flat.opass {c} r nd) = Flat.opass r λ d → nd (done-xy c (so r) d)
    back (Flat.lane r ru l nc w) = Flat.lane r ru l nc w
    back (Flat.lend {q} {a} {c} r ru l nc dn)   = Flat.lend r ru l nc (done-yx c (lane-since L {d = d} {O = O} {Ls = LY} {q = q} {a = a} so r l) dn)
    back (Flat.lpass {q} {a} {c} r ru l nc nd) = Flat.lpass r ru l nc λ dn → nd (done-xy c (lane-since L {d = d} {O = O} {Ls = LY} {q = q} {a = a} so r l) dn)
    back (Flat.left _ _ _ () _)
    back (Flat.run x w)  = Flat.run (lanes-yx x) w
    back (Flat.rend {c} x d)   = Flat.rend (lanes-yx x) (done-yx c (since-lanes LY sy x) d)
    back (Flat.rpass {c} x nd) = Flat.rpass (lanes-yx x) λ d → nd (done-xy c (since-lanes LY sy x) d)

    bwd′ : ∀ {k e} → Y′ k e → X k e ⊎ Skip p k e
    bwd′ r with y← r
    ... | inj₁ r′                  = inj₁ (back r′)
    ... | inj₂ (refl , refl , d)   = inj₁ (Flat.rend (any-ʳ++ʳ Pre (inj₁ new)) d)

    frame-≈ : X ≈⟨ p ⟩ Y′
    frame-≈ = fwd′ ⇆ bwd′

  since-x : Since p X
  since-x = since-flat L O LX so sx

  since-y : Since p Y
  since-y = since-flat L O LY so sy
