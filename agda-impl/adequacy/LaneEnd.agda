{-# OPTIONS --guardedness #-}

-- A LANE'S END, READ AT ITS JOINER: a lane owing only its end at `p`,
-- every other part of the joiner strictly past `p`, `n` lanes live.  Off
-- `p` the joiner owes what it owes with the lane gone and `pred n` live;
-- at `p` it owes its own end when the lane was the last live one and its
-- outer is done, and a skip otherwise.  Read at each joiner by its own
-- policy, none waiting.
module adequacy.LaneEnd where

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _ʳ++_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; pred)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Bool using (Bool; T)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Tree using (FlatOp; mergeᶠ; switchᶠ; exhaustᶠ)

open import denotation.Events using (Pos)
open import denotation.EmissionSet using (EmissionSet; end; out; _≺_; _≼_)
open import denotation.Laws.Modulus using (≺→≼; ≼-refl)
open import adequacy.Rows using (∅; Plus; old; new; Lanes; Each; Kth; AllEnd; EndsOf; module Flat; module SwitchF; module ExhaustF)
open import adequacy.Up using (any-ʳ++; any-ʳ++ˡ; any-ʳ++ʳ; all-ʳ++)
open import adequacy.Bound using (Empty)
open import adequacy.Skip using (After; Since; _≈⟨_⟩_; after-since; since-lanes; lane-since; since-join)
open import adequacy.Policy using (Policy; JoinP; DoneP; polOf; flatP; switchP; exhaustP; boundedP)
open import adequacy.JoinEnd using (EndsAt; module Frame)

-- Two lists of ends one place apart: `x` in the one where `y` is in the
-- other.
data Sw (x y : Pos → Set) : List (Pos → Set) → List (Pos → Set) → Set₁ where
  here  : ∀ {r} → Sw x y (x ∷ r) (y ∷ r)
  there : ∀ {l xs ys} → Sw x y xs ys → Sw x y (l ∷ xs) (l ∷ ys)

sw-ends : ∀ {B} {x y} (Pre : List (EmissionSet B)) {Z W} → Sw x y (EndsOf Z) (EndsOf W) → Sw x y (EndsOf (Pre ʳ++ Z)) (EndsOf (Pre ʳ++ W))
sw-ends []        s = s
sw-ends (_ ∷ Pre) s = sw-ends Pre (there s)

-- A end somewhere among the lanes.
Has : (Pos → Set) → (Pos → Set) → Set
Has P l = Σ Pos λ c → l c × P c

kth-skip : ∀ {P l} ls k → Kth P ls k → Kth P (l ∷ ls) k
kth-skip ls zero    x = inj₂ x
kth-skip ls (suc k) x = inj₂ x

kth-less : ∀ {P} ls k → Kth P ls (suc k) → Kth P ls k
kth-less (_ ∷ ls) zero    (inj₁ (h , _)) = inj₁ h
kth-less (_ ∷ ls) zero    (inj₂ x)       = inj₂ (kth-less ls zero x)
kth-less (_ ∷ ls) (suc k) (inj₁ (h , x)) = inj₁ (h , kth-less ls k x)
kth-less (_ ∷ ls) (suc k) (inj₂ x)       = inj₂ (kth-less ls (suc k) x)

-- One end fewer: at most one fewer among them.
kth-drop : ∀ {P x y xs ys} → Sw x y xs ys → ∀ k → Kth P xs (suc k) → Kth P ys k
kth-drop {ys = _ ∷ r} here k (inj₁ (_ , kr)) = kth-skip r k kr
kth-drop {ys = _ ∷ r} here k (inj₂ kr)       = kth-skip r k (kth-less r k kr)
kth-drop (there s) zero    (inj₁ (h , _))  = inj₁ h
kth-drop (there s) zero    (inj₂ x)        = inj₂ (kth-drop s zero x)
kth-drop (there s) (suc k) (inj₁ (h , x))  = inj₁ (h , kth-drop s k x)
kth-drop (there s) (suc k) (inj₂ x)        = inj₂ (kth-drop s (suc k) x)

kth-at : ∀ {P x y xs ys} → Sw x y xs ys → Has P x → Kth P xs 0
kth-at here      h = inj₁ h
kth-at (there s) h = inj₂ (kth-at s h)

-- An end in for one that never comes: one more among them.
kth-add : ∀ {P x y xs ys} → Sw x y xs ys → Has P x → (∀ {c} → ¬ y c) → ∀ k → Kth P ys k → Kth P xs (suc k)
kth-add here      h ny zero    (inj₁ (_ , yc , _)) = ⊥-elim (ny yc)
kth-add here      h ny zero    (inj₂ kr)           = inj₁ (h , kr)
kth-add here      h ny (suc k) (inj₁ ((_ , yc , _) , _)) = ⊥-elim (ny yc)
kth-add here      h ny (suc k) (inj₂ kr)           = inj₁ (h , kr)
kth-add (there s) h ny zero    (inj₁ hl)       = inj₁ (hl , kth-at s h)
kth-add (there s) h ny zero    (inj₂ x)        = inj₂ (kth-add s h ny zero x)
kth-add (there s) h ny (suc k) (inj₁ (hl , x)) = inj₁ (hl , kth-add s h ny k x)
kth-add (there s) h ny (suc k) (inj₂ x)        = inj₂ (kth-add s h ny (suc k) x)

-- An end among the lanes is a lane's end.
kth-lanes : ∀ {B P} (Ls : List (EmissionSet B)) k → Kth P (EndsOf Ls) k → Σ Pos λ c → Lanes Ls c end × P c
kth-lanes (_ ∷ Ls) zero    (inj₁ (c , r , pc))     = c , inj₁ r , pc
kth-lanes (_ ∷ Ls) zero    (inj₂ x) with kth-lanes Ls zero x
... | c , l , pc = c , inj₂ l , pc
kth-lanes (_ ∷ Ls) (suc k) (inj₁ ((c , r , pc) , _)) = c , inj₁ r , pc
kth-lanes (_ ∷ Ls) (suc k) (inj₂ x) with kth-lanes Ls (suc k) x
... | c , l , pc = c , inj₂ l , pc

after-lanes : ∀ {B} {p} (Ls : List (EmissionSet B)) → Each (After p) Ls → ∀ {k e} → Lanes Ls k e → ¬ k ≼ p
after-lanes (_ ∷ _)  (a , _)  (inj₁ r) kp = kp (a r)
after-lanes {p = p} (_ ∷ Ls) (_ , as) (inj₂ x) kp = after-lanes {p = p} Ls as x kp

postulate
  -- A BOUNDED MERGE'S TWO READINGS PAST A LANE'S END, NONE WAITING: the
  -- ended lane frees its slot before any outer value arrives, so each
  -- value's schedule, its start and its hand-off read alike with the lane
  -- gone and one fewer live.
  bounded-ends-at : ∀ {A B} m (L : A → Pos → EmissionSet B) {p O d n} (Pre Post : List (EmissionSet B)) {t₀ : EmissionSet B}
                  → After p O → Each (After p) Pre → Each (After p) Post → Empty t₀
                  → EndsAt (boundedP m L O d n [] (Pre ʳ++ (Plus t₀ p end ∷ Post))) (boundedP m L O d (pred n) [] (Pre ʳ++ (∅ ∷ Post))) p

module _ {A B : Set} (L : A → Pos → EmissionSet B) {p : Pos} {O : EmissionSet A} {d : Bool} {n : ℕ} (Pre Post : List (EmissionSet B)) {t₀ : EmissionSet B}
         (ao : After p O) (apre : Each (After p) Pre) (apost : Each (After p) Post) (e₀ : Empty t₀) where

  LX = Pre ʳ++ (Plus t₀ p end ∷ Post)
  LY = Pre ʳ++ (∅ ∷ Post)

  PX PY : FlatOp → Policy A B
  PX op = polOf op L O d n [] LX
  PY op = polOf op L O d (pred n) [] LY

  sw : Sw (λ c → Plus t₀ p end c end) (λ c → ∅ {B} c end) (EndsOf LX) (EndsOf LY)
  sw = sw-ends Pre here

  none : ∀ {c} → ¬ ∅ {B} c end
  none ()

  ends-xy : ∀ {P} k → AllEnd P k (EndsOf LX) → AllEnd P (pred k) (EndsOf LY)
  ends-xy zero          _ = _
  ends-xy (suc zero)    _ = _
  ends-xy {P} (suc (suc k)) x = kth-drop {P = P} sw k x

  ends-yx : ∀ {P} k → P p → AllEnd P (pred k) (EndsOf LY) → AllEnd P k (EndsOf LX)
  ends-yx zero          pp _ = _
  ends-yx {P} (suc zero)    pp _ = kth-at {P = P} sw (p , new , pp)
  ends-yx {P} (suc (suc k)) pp y = kth-add {P = P} sw (p , new , pp) (λ {c′} → none {c′}) k y

  -- The lane the last live one: every live one ended at `p`.
  ends-p : pred n ≡ 0 → AllEnd (_≼ p) n (EndsOf LX)
  ends-p = go n
    where
      go : ∀ k → pred k ≡ 0 → AllEnd (_≼ p) k (EndsOf LX)
      go zero          _ = _
      go (suc zero)    _ = kth-at {P = _≼ p} sw (p , new , ≼-refl {p})
      go (suc (suc _)) ()

  after-y : ∀ {k e} → Lanes LY k e → ¬ k ≼ p
  after-y x with any-ʳ++ Pre x
  ... | inj₁ a        = after-lanes {p = p} Pre apre a
  ... | inj₂ (inj₁ ())
  ... | inj₂ (inj₂ b) = after-lanes {p = p} Post apost b

  -- Another lane live: it ends past `p`.
  ends-owe : ∀ m {k} → pred m ≡ suc k → ¬ AllEnd (_≼ p) m (EndsOf LX)
  ends-owe zero          ()
  ends-owe (suc zero)    ()
  ends-owe (suc (suc m)) refl x with kth-lanes LY m (kth-drop {P = _≼ p} sw m x)
  ... | c , l , cp = after-y l cp

  so : Since p O
  so {q} {e} r = ≺→≼ {p} {q} (ao {q} {e} r)

  -- No outer value before `p`.
  unkilled : ∀ {q a} → O q (out a) → ¬ q ≺ p
  unkilled {q} r lt = ≺→≼ {p} {q} (ao r) lt

  outer-on : ¬ T d → ¬ (T d ⊎ Σ Pos λ c₀ → O c₀ end × c₀ ≼ p)
  outer-on nd (inj₁ td)            = nd td
  outer-on nd (inj₂ (c₀ , x , c₀p)) = c₀p (ao x)

  sx : Each (Since p) LX
  sx = all-ʳ++ Pre (after-since Pre apre) (hole , after-since Post apost)
    where
      hole : Since p (Plus t₀ p end)
      hole (old r) = ⊥-elim (e₀ r)
      hole new     = ≼-refl {p}

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

  ----------------------------------------------------------------------
  -- Merge

  done-xy : ∀ c → p ≼ c → Flat.Done L O d n LX c → Flat.Done L O d (pred n) LY c
  done-xy c pc (Flat.over-at g ls , h) = Flat.over-at g (ends-xy n ls) , h

  done-yx : ∀ c → p ≼ c → Flat.Done L O d (pred n) LY c → Flat.Done L O d n LX c
  done-yx c pc (Flat.over-at g ls , h) = Flat.over-at g (ends-yx n pc ls) , h

  merge-ends : EndsAt (flatP L O d n LX) (flatP L O d (pred n) LY) p
  merge-ends = record
    { o→ = λ r → r ; o← = λ r → r ; so = so ; sb = since-lanes LX sx
    ; sl = λ {q} {a} r l → lane-since L {d = d} {n = n} {O = O} {q = q} {a = a} so r l
    ; ln→ = λ _ l → l ; ln← = λ _ l → l ; ru→ = λ _ u → u ; ru← = λ _ u → u ; cu→ = λ _ () ; cu← = λ _ ()
    ; ha→ = λ _ () ; ha← = λ _ () ; dn→ = λ {c} → done-xy c ; dn← = λ {c} → done-yx c
    ; bg→ = lanes-xy ; bg← = lanes-yx ; at = any-ʳ++ʳ Pre (inj₁ new) ; nh = λ () }

  ----------------------------------------------------------------------
  -- Switch: nothing kills before `p`

  sw-bg→ : ∀ {k e} → SwitchF.Bg L O d n LX k e → SwitchF.Bg L O d (pred n) LY k e ⊎ (k ≡ p × e ≡ end)
  sw-bg→ (SwitchF.bg x nk) with lanes-xy x
  ... | inj₁ y  = inj₁ (SwitchF.bg y nk)
  ... | inj₂ eq = inj₂ eq
  sw-bg→ (SwitchF.bpin x nk i) with lanes-xy x
  ... | inj₁ y       = inj₁ (SwitchF.bpin y nk i)
  ... | inj₂ (_ , ())

  sw-bg← : ∀ {k e} → SwitchF.Bg L O d (pred n) LY k e → SwitchF.Bg L O d n LX k e
  sw-bg← (SwitchF.bg y nk)     = SwitchF.bg (lanes-yx y) nk
  sw-bg← (SwitchF.bpin y nk i) = SwitchF.bpin (lanes-yx y) nk i

  sw-sb : Since p (SwitchF.Bg L O d n LX)
  sw-sb (SwitchF.bg x _)     = since-lanes LX sx x
  sw-sb (SwitchF.bpin x _ _) = since-lanes LX sx x

  sw-over→ : ∀ {c} → SwitchF.Over L O d n LX c → SwitchF.Over L O d (pred n) LY c
  sw-over→ (g , inj₁ ls) = g , inj₁ (ends-xy n ls)
  sw-over→ (g , inj₂ k)  = g , inj₂ k

  sw-over← : ∀ {c} → p ≼ c → SwitchF.Over L O d (pred n) LY c → SwitchF.Over L O d n LX c
  sw-over← pc (g , inj₁ ls) = g , inj₁ (ends-yx n pc ls)
  sw-over← pc (g , inj₂ k)  = g , inj₂ k

  switch-ends : EndsAt (switchP L O d n LX) (switchP L O d (pred n) LY) p
  switch-ends = record
    { o→ = λ r → r ; o← = λ r → r ; so = so ; sb = sw-sb
    ; sl = λ {q} {a} r l → lane-since L {d = d} {n = n} {O = O} {q = q} {a = a} so r l
    ; ln→ = λ _ l → l ; ln← = λ _ l → l ; ru→ = λ _ u → u ; ru← = λ _ u → u ; cu→ = λ _ y → y ; cu← = λ _ y → y
    ; ha→ = λ _ () ; ha← = λ _ () ; dn→ = λ { _ (v , h) → sw-over→ v , h } ; dn← = λ { pc (v , h) → sw-over← pc v , h }
    ; bg→ = sw-bg→ ; bg← = sw-bg← ; at = SwitchF.bg (any-ʳ++ʳ Pre (inj₁ new)) (λ (_ , _ , r , lt) → unkilled r lt) ; nh = λ () }

  ----------------------------------------------------------------------
  -- Exhaust: every value arrives past `p`, where the lane has ended

  ex-cur→ : ∀ {q w} → ExhaustF.Cur L O d n LX q w → ExhaustF.Cur L O d (pred n) LY q w
  ex-cur← : ∀ {q w} → ExhaustF.Cur L O d (pred n) LY q w → ExhaustF.Cur L O d n LX q w
  ex-cur→ (ExhaustF.cur₀ r m f)              = ExhaustF.cur₀ r m (ends-xy n f)
  ex-cur→ (ExhaustF.bg₀ r m nf)              = ExhaustF.bg₀ r m (λ f → nf (ends-yx n (ao r) f))
  ex-cur→ (ExhaustF.run c r l lt r₂ lt′ nx)  = ExhaustF.run (ex-cur→ c) r l lt r₂ lt′ nx
  ex-cur→ (ExhaustF.drop c r f r₂ lt′ nx)    = ExhaustF.drop (ex-cur→ c) r f r₂ lt′ nx
  ex-cur→ (ExhaustF.brun c f r₂ lt nx)       = ExhaustF.brun (ex-cur→ c) (ends-xy n f) r₂ lt nx
  ex-cur→ (ExhaustF.bdrop c nf r₂ lt nx)     = ExhaustF.bdrop (ex-cur→ c) (λ f → nf (ends-yx n (ao r₂) f)) r₂ lt nx
  ex-cur← (ExhaustF.cur₀ r m f)              = ExhaustF.cur₀ r m (ends-yx n (ao r) f)
  ex-cur← (ExhaustF.bg₀ r m nf)              = ExhaustF.bg₀ r m (λ f → nf (ends-xy n f))
  ex-cur← (ExhaustF.run c r l lt r₂ lt′ nx)  = ExhaustF.run (ex-cur← c) r l lt r₂ lt′ nx
  ex-cur← (ExhaustF.drop c r f r₂ lt′ nx)    = ExhaustF.drop (ex-cur← c) r f r₂ lt′ nx
  ex-cur← (ExhaustF.brun c f r₂ lt nx)       = ExhaustF.brun (ex-cur← c) (ends-yx n (ao r₂) f) r₂ lt nx
  ex-cur← (ExhaustF.bdrop c nf r₂ lt nx)     = ExhaustF.bdrop (ex-cur← c) (λ f → nf (ends-xy n f)) r₂ lt nx

  exhaust-ends : EndsAt (exhaustP L O d n LX) (exhaustP L O d (pred n) LY) p
  exhaust-ends = record
    { o→ = λ r → r ; o← = λ r → r ; so = so ; sb = since-lanes LX sx
    ; sl = λ {q} {a} r l → lane-since L {d = d} {n = n} {O = O} {q = q} {a = a} so r l
    ; ln→ = λ _ l → l ; ln← = λ _ l → l ; ru→ = λ _ u → ex-cur→ u ; ru← = λ _ u → ex-cur← u ; cu→ = λ _ () ; cu← = λ _ ()
    ; ha→ = λ _ () ; ha← = λ _ ()
    ; dn→ = λ { _ ((g , ls) , h) → (g , ends-xy n ls) , λ r u → h r (ex-cur← u) }
    ; dn← = λ { pc ((g , ls) , h) → (g , ends-yx n pc ls) , λ r u → h r (ex-cur→ u) }
    ; bg→ = lanes-xy ; bg← = lanes-yx ; at = any-ʳ++ʳ Pre (inj₁ new) ; nh = λ () }

  ----------------------------------------------------------------------
  -- Every joiner

  -- The joiner's two readings past `p`, the lane's end at `p` unhanded.
  ends-at : ∀ op → EndsAt (PX op) (PY op) p
  ends-at (mergeᶠ nothing)  = merge-ends
  ends-at (mergeᶠ (just m)) = bounded-ends-at m L Pre Post ao apre apost e₀
  ends-at switchᶠ           = switch-ends
  ends-at exhaustᶠ          = exhaust-ends

  -- THE FRAME: the joiner with the lane read as `Y′`, which owes `PY`'s
  -- joiner and at most its own end at `p`.
  frame-≈ : ∀ op (Y′ : EmissionSet B) → (DoneP (PX op) p → Y′ p end) → (∀ {k e} → JoinP (PY op) k e → Y′ k e)
          → (∀ {k e} → Y′ k e → JoinP (PY op) k e ⊎ (k ≡ p × e ≡ end × DoneP (PX op) p)) → JoinP (PX op) ≈⟨ p ⟩ Y′
  frame-≈ op = Frame.frame-≈ (ends-at op)

  since-x : ∀ op → Since p (JoinP (PX op))
  since-x op = since-join (PX op) (EndsAt.so E) (EndsAt.sb E) (EndsAt.sl E)
    where E = ends-at op

  since-y : ∀ op → Since p (JoinP (PY op))
  since-y op = since-join (PY op) (λ r → EndsAt.so E (EndsAt.o← E r)) (λ x → EndsAt.sb E (EndsAt.bg← E x))
                          (λ r l → EndsAt.sl E (EndsAt.o← E r) (EndsAt.ln← E (EndsAt.o← E r) l))
    where E = ends-at op

  -- The joiner done at `p` exactly when the lane was the last live one.
  done-at : ∀ op → T d → pred n ≡ 0 → DoneP (PX op) p
  done-at (mergeᶠ nothing)  td pn = Flat.over-at (inj₁ td) (ends-p pn) , λ r _ lt _ → ⊥-elim (unkilled r lt)
  done-at (mergeᶠ (just m)) td pn = (inj₁ td , subst (λ k → AllEnd (_≼ p) k (EndsOf LX)) (sym (+-identityʳ n)) (ends-p pn))
                                  , λ r _ lt _ → ⊥-elim (unkilled r lt)
  done-at switchᶠ           td pn = (inj₁ td , inj₁ (ends-p pn)) , λ r _ lt _ → ⊥-elim (unkilled r lt)
  done-at exhaustᶠ          td pn = (inj₁ td , ends-p pn) , λ r _ lt _ → ⊥-elim (unkilled r lt)

  outer-owes : ∀ op → ¬ T d → ¬ DoneP (PX op) p
  outer-owes (mergeᶠ nothing)  nd (Flat.over-at g _ , _) = outer-on nd g
  outer-owes (mergeᶠ (just m)) nd ((g , _) , _)          = outer-on nd g
  outer-owes switchᶠ           nd ((g , _) , _)          = outer-on nd g
  outer-owes exhaustᶠ          nd ((g , _) , _)          = outer-on nd g

  lanes-owe : ∀ op {k} → pred n ≡ suc k → ¬ DoneP (PX op) p
  lanes-owe (mergeᶠ nothing)  pn (Flat.over-at _ ls , _)          = ends-owe n pn ls
  lanes-owe (mergeᶠ (just m)) pn ((_ , ls) , _)                   = ends-owe n pn (subst (λ k → AllEnd (_≼ p) k (EndsOf LX)) (+-identityʳ n) ls)
  lanes-owe switchᶠ           pn ((_ , inj₁ ls) , _)              = ends-owe n pn ls
  lanes-owe switchᶠ           pn ((_ , inj₂ (_ , _ , r , lt)) , _) = unkilled r lt
  lanes-owe exhaustᶠ          pn ((_ , ls) , _)                   = ends-owe n pn ls
