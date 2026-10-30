{-# OPTIONS --guardedness #-}

-- A LANE'S VALUE, READ AT ITS JOINER: a begun lane owing a value `b` at
-- `p`, every other part of the joiner strictly past `p`.  The value ends
-- no lane, so the lanes' ends read alike with it or without, and the
-- joiner owes what it owes without the value and the value at `p`.  Read
-- at each joiner by its own policy.
module adequacy.LaneVal where

open import Data.List using (List; []; _∷_; _ʳ++_; _++_; [_])
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Bool using (Bool)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import Tree using (mergeᶠ; switchᶠ; exhaustᶠ)

open import denotation.Events using (Pos; ix)
open import denotation.EmissionSet using (EmissionSet; end; out; _≺_)
open import denotation.Laws.Modulus using (≺→≼; ≺-trans; ≺-ext)
open import adequacy.Rows using (Plus; old; new; Lanes; Lane; reads; Each; Kth; AllEnd; EndsOf; module Flat; module SwitchF; module ExhaustF)
open import adequacy.Up using (any-ʳ++; any-ʳ++ʳ; any-ʳ++ˡ)
open import adequacy.Skip using (After)
open import adequacy.Policy using (polOf; flatP; switchP; exhaustP; boundedP)
open import adequacy.JoinEnd using (ValAt)
open import adequacy.LaneEnd using (Sw; here; there; sw-ends)

-- Two lists of ends alike but for one place, the one's ends there among
-- the other's: as many among them.
kth-sw : ∀ {P x y xs ys} → Sw x y xs ys → (∀ {c} → x c → y c) → ∀ k → Kth P xs k → Kth P ys k
kth-sw here      f zero    (inj₁ (c , xc , pc))       = inj₁ (c , f xc , pc)
kth-sw here      f zero    (inj₂ r)                   = inj₂ r
kth-sw here      f (suc k) (inj₁ ((c , xc , pc) , r)) = inj₁ ((c , f xc , pc) , r)
kth-sw here      f (suc k) (inj₂ r)                   = inj₂ r
kth-sw (there s) f zero    (inj₁ h)                   = inj₁ h
kth-sw (there s) f zero    (inj₂ r)                   = inj₂ (kth-sw s f zero r)
kth-sw (there s) f (suc k) (inj₁ (h , r))             = inj₁ (h , kth-sw s f k r)
kth-sw (there s) f (suc k) (inj₂ r)                   = inj₂ (kth-sw s f (suc k) r)

sw-sym : ∀ {x y xs ys} → Sw x y xs ys → Sw y x ys xs
sw-sym here      = here
sw-sym (there s) = there (sw-sym s)

allend-sw : ∀ {P x y xs ys} → Sw x y xs ys → (∀ {c} → x c → y c) → ∀ k → AllEnd P k xs → AllEnd P k ys
allend-sw s f zero    _ = _
allend-sw s f (suc k) h = kth-sw s f k h

-- Lanes each past `p` are past `p`.
after-any : ∀ {B} {p} (Ls : List (EmissionSet B)) → Each (After p) Ls → After p (Lanes Ls)
after-any (_ ∷ _)  (a , _)  (inj₁ r) = a r
after-any {p = p} (_ ∷ Ls) (_ , as) (inj₂ x) = after-any {p = p} Ls as x

-- A lane begun past an outer value past `p` is past `p`.
lane-after : ∀ {A B} {L : A → Pos → EmissionSet B} {p q a k e} → p ≺ q → Lane L q a k e → p ≺ k
lane-after {p = p} {q} {k = k} pq (reads _ s) = ≺-trans {p} {q} {k} pq (≺-trans {q} {q ++ [ ix 1 ]} {k} (≺-ext q []) s)

postulate
  -- A BOUNDED MERGE'S TWO READINGS PAST A LANE'S VALUE: the value ends no
  -- lane, so each value's schedule, its start and its hand-off read alike
  -- with or without it.
  bounded-val-at : ∀ {A B} m (L : A → Pos → EmissionSet B) {p O d n} (Qu : List A) (Pre Post : List (EmissionSet B)) {t₀ : EmissionSet B} (b : B)
                 → After p O → Each (After p) Pre → Each (After p) Post → After p t₀
                 → ValAt (boundedP m L O d n Qu (Pre ʳ++ (Plus t₀ p (out b) ∷ Post))) (boundedP m L O d n Qu (Pre ʳ++ (t₀ ∷ Post))) p (out b)

module _ {A B : Set} (L : A → Pos → EmissionSet B) {p : Pos} {O : EmissionSet A} {d : Bool} {n : ℕ} (Qu : List A) (Pre Post : List (EmissionSet B))
         {t₀ : EmissionSet B} (b : B) (ao : After p O) (apre : Each (After p) Pre) (apost : Each (After p) Post) (at : After p t₀) where

  LX = Pre ʳ++ (Plus t₀ p (out b) ∷ Post)
  LY = Pre ʳ++ (t₀ ∷ Post)

  sw : Sw (λ c → Plus t₀ p (out b) c end) (λ c → t₀ c end) (EndsOf LX) (EndsOf LY)
  sw = sw-ends Pre here

  x→y : ∀ {c} → Plus t₀ p (out b) c end → t₀ c end
  x→y (old r) = r

  ends→ : ∀ {P} k → AllEnd P k (EndsOf LX) → AllEnd P k (EndsOf LY)
  ends→ = allend-sw sw x→y

  ends← : ∀ {P} k → AllEnd P k (EndsOf LY) → AllEnd P k (EndsOf LX)
  ends← = allend-sw (sw-sym sw) old

  lanes-xy : ∀ {k e} → Lanes LX k e → Lanes LY k e ⊎ (k ≡ p × e ≡ out b)
  lanes-xy x with any-ʳ++ Pre x
  ... | inj₁ a              = inj₁ (any-ʳ++ˡ Pre a)
  ... | inj₂ (inj₁ (old r)) = inj₁ (any-ʳ++ʳ Pre (inj₁ r))
  ... | inj₂ (inj₁ new)     = inj₂ (refl , refl)
  ... | inj₂ (inj₂ c)       = inj₁ (any-ʳ++ʳ Pre (inj₂ c))

  lanes-yx : ∀ {k e} → Lanes LY k e → Lanes LX k e
  lanes-yx x with any-ʳ++ Pre x
  ... | inj₁ a        = any-ʳ++ˡ Pre a
  ... | inj₂ (inj₁ r) = any-ʳ++ʳ Pre (inj₁ (old r))
  ... | inj₂ (inj₂ c) = any-ʳ++ʳ Pre (inj₂ c)

  after-y : After p (Lanes LY)
  after-y x with any-ʳ++ Pre x
  ... | inj₁ a        = after-any {p = p} Pre apre a
  ... | inj₂ (inj₁ r) = at r
  ... | inj₂ (inj₂ c) = after-any {p = p} Post apost c

  al : ∀ {q a k e} → O q (out a) → Lane L q a k e → p ≺ k
  al {q} r l = lane-after {p = p} {q} (ao r) l

  -- No outer value before `p`.
  unkilled : ∀ {q a} → O q (out a) → ¬ q ≺ p
  unkilled {q} r lt = ≺→≼ {p} {q} (ao r) lt

  ----------------------------------------------------------------------
  -- Merge

  merge-val : ValAt (flatP L O d n LX) (flatP L O d n LY) p (out b)
  merge-val = record
    { o→ = λ r → r ; o← = λ r → r ; ao = ao ; ab = after-y ; al = al
    ; ln→ = λ _ l → l ; ln← = λ _ l → l ; ru→ = λ _ u → u ; ru← = λ _ u → u ; cu→ = λ _ () ; cu← = λ _ ()
    ; ha→ = λ () ; ha← = λ ()
    ; dn→ = λ { (Flat.over-at g ls , h) → Flat.over-at g (ends→ n ls) , h }
    ; dn← = λ { (Flat.over-at g ls , h) → Flat.over-at g (ends← n ls) , h }
    ; bg→ = lanes-xy ; bg← = lanes-yx ; at = any-ʳ++ʳ Pre (inj₁ new) ; wk = tt }

  ----------------------------------------------------------------------
  -- Switch: nothing kills before `p`

  sw-bg→ : ∀ {k e} → SwitchF.Bg L O d n LX k e → SwitchF.Bg L O d n LY k e ⊎ (k ≡ p × e ≡ out b)
  sw-bg→ (SwitchF.bg x nk) with lanes-xy x
  ... | inj₁ y  = inj₁ (SwitchF.bg y nk)
  ... | inj₂ eq = inj₂ eq
  sw-bg→ (SwitchF.bpin x nk i) with lanes-xy x
  ... | inj₁ y       = inj₁ (SwitchF.bpin y nk i)
  ... | inj₂ (_ , ())

  sw-bg← : ∀ {k e} → SwitchF.Bg L O d n LY k e → SwitchF.Bg L O d n LX k e
  sw-bg← (SwitchF.bg y nk)     = SwitchF.bg (lanes-yx y) nk
  sw-bg← (SwitchF.bpin y nk i) = SwitchF.bpin (lanes-yx y) nk i

  sw-ab : After p (SwitchF.Bg L O d n LY)
  sw-ab (SwitchF.bg x _)     = after-y x
  sw-ab (SwitchF.bpin x _ _) = after-y x

  switch-val : ValAt (switchP L O d n LX) (switchP L O d n LY) p (out b)
  switch-val = record
    { o→ = λ r → r ; o← = λ r → r ; ao = ao ; ab = sw-ab ; al = al
    ; ln→ = λ _ l → l ; ln← = λ _ l → l ; ru→ = λ _ u → u ; ru← = λ _ u → u ; cu→ = λ _ y → y ; cu← = λ _ y → y
    ; ha→ = λ () ; ha← = λ ()
    ; dn→ = λ { ((g , inj₁ ls) , h) → (g , inj₁ (ends→ n ls)) , h ; ((g , inj₂ k) , h) → (g , inj₂ k) , h }
    ; dn← = λ { ((g , inj₁ ls) , h) → (g , inj₁ (ends← n ls)) , h ; ((g , inj₂ k) , h) → (g , inj₂ k) , h }
    ; bg→ = sw-bg→ ; bg← = sw-bg← ; at = SwitchF.bg (any-ʳ++ʳ Pre (inj₁ new)) (λ (_ , _ , r , lt) → unkilled r lt) ; wk = tt }

  ----------------------------------------------------------------------
  -- Exhaust: the lanes free alike

  ex-cur→ : ∀ {q w} → ExhaustF.Cur L O d n LX q w → ExhaustF.Cur L O d n LY q w
  ex-cur← : ∀ {q w} → ExhaustF.Cur L O d n LY q w → ExhaustF.Cur L O d n LX q w
  ex-cur→ (ExhaustF.cur₀ r m f)              = ExhaustF.cur₀ r m (ends→ n f)
  ex-cur→ (ExhaustF.bg₀ r m nf)              = ExhaustF.bg₀ r m (λ f → nf (ends← n f))
  ex-cur→ (ExhaustF.run c r l lt r₂ lt′ nx)  = ExhaustF.run (ex-cur→ c) r l lt r₂ lt′ nx
  ex-cur→ (ExhaustF.drop c r f r₂ lt′ nx)    = ExhaustF.drop (ex-cur→ c) r f r₂ lt′ nx
  ex-cur→ (ExhaustF.brun c f r₂ lt nx)       = ExhaustF.brun (ex-cur→ c) (ends→ n f) r₂ lt nx
  ex-cur→ (ExhaustF.bdrop c nf r₂ lt nx)     = ExhaustF.bdrop (ex-cur→ c) (λ f → nf (ends← n f)) r₂ lt nx
  ex-cur← (ExhaustF.cur₀ r m f)              = ExhaustF.cur₀ r m (ends← n f)
  ex-cur← (ExhaustF.bg₀ r m nf)              = ExhaustF.bg₀ r m (λ f → nf (ends→ n f))
  ex-cur← (ExhaustF.run c r l lt r₂ lt′ nx)  = ExhaustF.run (ex-cur← c) r l lt r₂ lt′ nx
  ex-cur← (ExhaustF.drop c r f r₂ lt′ nx)    = ExhaustF.drop (ex-cur← c) r f r₂ lt′ nx
  ex-cur← (ExhaustF.brun c f r₂ lt nx)       = ExhaustF.brun (ex-cur← c) (ends← n f) r₂ lt nx
  ex-cur← (ExhaustF.bdrop c nf r₂ lt nx)     = ExhaustF.bdrop (ex-cur← c) (λ f → nf (ends→ n f)) r₂ lt nx

  exhaust-val : ValAt (exhaustP L O d n LX) (exhaustP L O d n LY) p (out b)
  exhaust-val = record
    { o→ = λ r → r ; o← = λ r → r ; ao = ao ; ab = after-y ; al = al
    ; ln→ = λ _ l → l ; ln← = λ _ l → l ; ru→ = λ _ u → ex-cur→ u ; ru← = λ _ u → ex-cur← u ; cu→ = λ _ () ; cu← = λ _ ()
    ; ha→ = λ () ; ha← = λ ()
    ; dn→ = λ { ((g , ls) , h) → (g , ends→ n ls) , λ r u → h r (ex-cur← u) }
    ; dn← = λ { ((g , ls) , h) → (g , ends← n ls) , λ r u → h r (ex-cur→ u) }
    ; bg→ = lanes-xy ; bg← = lanes-yx ; at = any-ʳ++ʳ Pre (inj₁ new) ; wk = tt }

  ----------------------------------------------------------------------
  -- Every joiner

  val-at : ∀ op → ValAt (polOf op L O d n Qu LX) (polOf op L O d n Qu LY) p (out b)
  val-at (mergeᶠ nothing)  = merge-val
  val-at (mergeᶠ (just m)) = bounded-val-at m L Qu Pre Post b ao apre apost at
  val-at switchᶠ           = switch-val
  val-at exhaustᶠ          = exhaust-val
