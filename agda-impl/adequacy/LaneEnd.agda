{-# OPTIONS --guardedness #-}

-- A LANE'S END, READ AT ITS MERGE: a lane owing only its end at `p`,
-- every other part of the merge strictly past `p`.  Off `p` the merge
-- owes what it owes with the lane gone, out of its count; at `p` it owes
-- its own end when the outer is done and no other lane is counted, and a
-- skip otherwise.
module adequacy.LaneEnd where

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _ʳ++_)
open import Data.Product using (_×_; _,_)
open import Data.Bool using (Bool; T)
open import Data.Nat using (ℕ; zero; suc; pred)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import denotation.Events using (Pos)
open import denotation.EmissionSet using (EmissionSet; end; _≼_; Ended)
open import denotation.Laws.Modulus using (≺→≼; ≼-refl)
open import adequacy.Rows using (∅; Plus; old; new; Enough; Lanes; Each; module Flat)
open import adequacy.Up using (any-ʳ++; any-ʳ++ˡ; any-ʳ++ʳ; all-ʳ++; all-ʳ++⁻)
open import adequacy.Bound using (Empty; end-enough)
open import adequacy.Skip using (After; Since; _≈⟨_⟩_; _⇆_; Skip; after-since; since-lanes; lane-since; since-flat)

module _ {B : Set} where
  enough-cons : ∀ k {t} (Ls : List (EmissionSet B)) {c} → Enough k Ls c → Enough k (t ∷ Ls) c
  enough-cons zero    Ls e = tt
  enough-cons (suc k) Ls e = inj₂ e

  enough-pred : ∀ k (Ls : List (EmissionSet B)) {c} → Enough (suc k) Ls c → Enough k Ls c
  enough-pred k       []       ()
  enough-pred zero    (t ∷ Ls) e              = tt
  enough-pred (suc k) (t ∷ Ls) (inj₁ (x , y)) = inj₁ (x , enough-pred k Ls y)
  enough-pred (suc k) (t ∷ Ls) (inj₂ y)       = inj₂ (enough-pred (suc k) Ls y)

  -- No lane ended by `c`: nothing is.
  none-ended : ∀ (Ls : List (EmissionSet B)) {c} → Each (λ t → ¬ Ended t c) Ls → ∀ k → ¬ Enough (suc k) Ls c
  none-ended []       _        k ()
  none-ended (t ∷ Ls) (n , _)  k (inj₁ (x , _)) = n x
  none-ended (t ∷ Ls) (_ , ns) k (inj₂ y)       = none-ended Ls ns k y

  not-ended : ∀ {p} (Ls : List (EmissionSet B)) → Each (After p) Ls → Each (λ t → ¬ Ended t p) Ls
  not-ended []       _        = _
  not-ended {p} (_ ∷ Ls) (a , as) = (λ { (_ , r , le) → le (a r) }) , not-ended {p} Ls as

  -- One lane of a list, `t`, read as `u`.
  data Hole (t u : EmissionSet B) : List (EmissionSet B) → List (EmissionSet B) → Set₁ where
    here  : ∀ {Ls} → Hole t u (t ∷ Ls) (u ∷ Ls)
    there : ∀ {x Ls Ls′} → Hole t u Ls Ls′ → Hole t u (x ∷ Ls) (x ∷ Ls′)

  hole-ʳ++ : ∀ (xs : List (EmissionSet B)) {t u Ls Ls′} → Hole t u Ls Ls′ → Hole t u (xs ʳ++ Ls) (xs ʳ++ Ls′)
  hole-ʳ++ []       h = h
  hole-ʳ++ (x ∷ xs) h = hole-ʳ++ xs (there h)

  -- The hole's lane out of the count: one fewer ended.
  hole-out : ∀ {t u Ls Ls′} → Hole t u Ls Ls′ → ∀ k {c} → Enough (suc k) Ls c → Enough k Ls′ c
  hole-out here      k       (inj₁ (_ , y)) = enough-cons k _ y
  hole-out here      k       (inj₂ y)       = enough-cons k _ (enough-pred k _ y)
  hole-out (there h) zero    _              = tt
  hole-out (there h) (suc k) (inj₁ (x , y)) = inj₁ (x , hole-out h k y)
  hole-out (there h) (suc k) (inj₂ y)       = inj₂ (hole-out h (suc k) y)

  -- The hole's lane into the count, ended, read as owing nothing: one more.
  hole-in : ∀ {t u Ls Ls′} → Hole t u Ls Ls′ → Empty u → ∀ k {c} → Ended t c → Enough k Ls′ c → Enough (suc k) Ls c
  hole-in {Ls = _ ∷ Ls} here eu k {c} et y = inj₁ (et , drop k y)
    where
      drop : ∀ k → Enough k (_ ∷ Ls) c → Enough k Ls c
      drop zero    _                    = tt
      drop (suc k) (inj₁ ((_ , r , _) , _)) = ⊥-elim (eu r)
      drop (suc k) (inj₂ y)             = y
  hole-in (there h) eu zero    et _              = inj₂ (hole-in h eu zero et tt)
  hole-in (there h) eu (suc k) et (inj₁ (x , y)) = inj₁ (x , hole-in h eu k et y)
  hole-in (there h) eu (suc k) et (inj₂ y)       = inj₂ (hole-in h eu (suc k) et y)

module _ {A B : Set} (L : A → Pos → EmissionSet B) {p : Pos} {O : EmissionSet A} {d : Bool} {n : ℕ} (Pre Post : List (EmissionSet B)) {t₀ : EmissionSet B}
         (ao : After p O) (apre : Each (After p) Pre) (apost : Each (After p) Post) (e₀ : Empty t₀) where

  LX = Pre ʳ++ (Plus t₀ p end ∷ Post)
  LY = Pre ʳ++ (∅ ∷ Post)
  X  = Flat.JoinT L O d n LX
  Y  = Flat.JoinT L O d (pred n) LY

  hx : Hole (Plus t₀ p end) ∅ LX LY
  hx = hole-ʳ++ Pre here

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

  done-xy : ∀ c → p ≼ c → Flat.Done L O d n LX c → Flat.Done L O d (pred n) LY c
  done-xy c _ ((g , ls) , h) = (g , out n ls) , h
    where
      out : ∀ m → Enough m LX c → Enough (pred m) LY c
      out zero    _ = tt
      out (suc m) e = hole-out hx m e

  done-yx : ∀ c → p ≼ c → Flat.Done L O d (pred n) LY c → Flat.Done L O d n LX c
  done-yx c pc ((g , ls) , h) = (g , into n ls) , h
    where
      into : ∀ m → Enough (pred m) LY c → Enough m LX c
      into zero    _ = tt
      into (suc m) e = hole-in hx (λ ()) m (p , new , pc) e

  -- The merge done at `p` when the outer is and this was its last lane.
  done-at : T d → pred n ≡ 0 → Flat.Done L O d n LX p
  done-at td pz = (inj₁ td , one n pz) , λ {q} r _ lt _ → ⊥-elim (≺→≼ {p} {q} (ao r) lt)
    where
      one : ∀ m → pred m ≡ 0 → Enough m LX p
      one zero          _  = tt
      one (suc zero)    _  = end-enough LX (any-ʳ++ʳ Pre (inj₁ new))
      one (suc (suc _)) ()

  outer-owes : ¬ T d → ¬ Flat.Done L O d n LX p
  outer-owes nd ((inj₁ td , _) , _)             = nd td
  outer-owes nd ((inj₂ (c₀ , x , c₀p) , _) , _) = c₀p (ao x)

  -- Another lane in the list: it lies past `p`, so has not ended by it.
  lanes-owe : ∀ k → pred n ≡ suc k → ¬ Flat.Done L O d n LX p
  lanes-owe k e ((_ , ls) , _) = go n e ls
    where
      ny : Each (λ t → ¬ Ended t p) LY
      ny = all-ʳ++ Pre (not-ended {p = p} Pre apre) ((λ { (_ , () , _) }) , not-ended {p = p} Post apost)
      go : ∀ m → pred m ≡ suc k → Enough m LX p → ⊥
      go zero    ()   _
      go (suc m) refl en = none-ended LY ny k (hole-out hx (suc k) en)

  -- THE FRAME: the merge with the lane read as `Y′`, which owes `Y` and
  -- at most the merge's own end at `p`.
  module _ (Y′ : EmissionSet B) (dp : Flat.Done L O d n LX p → Y′ p end) (y→ : ∀ {k e} → Y k e → Y′ k e)
           (y← : ∀ {k e} → Y′ k e → Y k e ⊎ (k ≡ p × e ≡ end × Flat.Done L O d n LX p)) where

    fwd′ : ∀ {k e} → X k e → Y′ k e ⊎ Skip p k e
    fwd′ (Flat.val r)    = inj₁ (y→ (Flat.val r))
    fwd′ (Flat.step r)   = inj₁ (y→ (Flat.step r))
    fwd′ (Flat.oend {c} r d)   = inj₁ (y→ (Flat.oend r (done-xy c (so r) d)))
    fwd′ (Flat.opass {c} r nd) = inj₁ (y→ (Flat.opass r λ d → nd (done-yx c (so r) d)))
    fwd′ (Flat.lane r ru l nc w) = inj₁ (y→ (Flat.lane r ru l nc w))
    fwd′ (Flat.lend {q} {a} {c} r ru l nc nh dn)   = inj₁ (y→ (Flat.lend r ru l nc nh (done-xy c (lane-since L {d = d} {n = n} {O = O} {q = q} {a = a} so r l) dn)))
    fwd′ (Flat.lpass {q} {a} {c} r ru l nc nh nd) = inj₁ (y→ (Flat.lpass r ru l nc nh λ dn → nd (done-yx c (lane-since L {d = d} {n = n} {O = O} {q = q} {a = a} so r l) dn)))
    fwd′ (Flat.left _ _ _ () _)
    fwd′ (Flat.hand _ _ _ _ ())
    fwd′ (Flat.rhand _ ())
    fwd′ (Flat.run x w) with lanes-xy x
    ... | inj₁ x′           = inj₁ (y→ (Flat.run x′ w))
    ... | inj₂ (refl , refl) = ⊥-elim w
    fwd′ (Flat.rend {c} x nh d) with lanes-xy x
    ... | inj₁ x′           = inj₁ (y→ (Flat.rend x′ nh (done-xy c (since-lanes LX sx x) d)))
    ... | inj₂ (refl , refl) = inj₁ (dp d)
    fwd′ (Flat.rpass {c} x nh nd) with lanes-xy x
    ... | inj₁ x′           = inj₁ (y→ (Flat.rpass x′ nh λ d → nd (done-yx c (since-lanes LX sx x) d)))
    ... | inj₂ (refl , refl) = inj₂ (refl , refl)

    back : ∀ {k e} → Y k e → X k e
    back (Flat.val r)    = Flat.val r
    back (Flat.step r)   = Flat.step r
    back (Flat.oend {c} r d)   = Flat.oend r (done-yx c (so r) d)
    back (Flat.opass {c} r nd) = Flat.opass r λ d → nd (done-xy c (so r) d)
    back (Flat.lane r ru l nc w) = Flat.lane r ru l nc w
    back (Flat.lend {q} {a} {c} r ru l nc nh dn)   = Flat.lend r ru l nc nh (done-yx c (lane-since L {d = d} {n = n} {O = O} {q = q} {a = a} so r l) dn)
    back (Flat.lpass {q} {a} {c} r ru l nc nh nd) = Flat.lpass r ru l nc nh λ dn → nd (done-xy c (lane-since L {d = d} {n = n} {O = O} {q = q} {a = a} so r l) dn)
    back (Flat.left _ _ _ () _)
    back (Flat.hand _ _ _ _ ())
    back (Flat.rhand _ ())
    back (Flat.run x w)  = Flat.run (lanes-yx x) w
    back (Flat.rend {c} x nh d)   = Flat.rend (lanes-yx x) nh (done-yx c (since-lanes LY sy x) d)
    back (Flat.rpass {c} x nh nd) = Flat.rpass (lanes-yx x) nh λ d → nd (done-xy c (since-lanes LY sy x) d)

    bwd′ : ∀ {k e} → Y′ k e → X k e ⊎ Skip p k e
    bwd′ r with y← r
    ... | inj₁ r′                  = inj₁ (back r′)
    ... | inj₂ (refl , refl , d)   = inj₁ (Flat.rend (any-ʳ++ʳ Pre (inj₁ new)) (λ ()) d)

    frame-≈ : X ≈⟨ p ⟩ Y′
    frame-≈ = fwd′ ⇆ bwd′

  since-x : Since p X
  since-x = since-flat L O LX so sx

  since-y : Since p Y
  since-y = since-flat L O LY so sy
