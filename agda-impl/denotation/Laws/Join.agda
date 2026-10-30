{-# OPTIONS --guardedness #-}

-- A JOINER READS A LANE ONLY WHERE IT SUBSCRIBES IT, and only past the
-- subscription, so a lane row at or before the bound has its outer value
-- there too.  The rest it reads (a cut, a first value, an unended lane)
-- holds past the bound by order alone.
--
-- The lanes agree only where one side subscribes them (`Lanes`): what
-- shows a subscription on the other side is carried over first, by the
-- lanes it reads, each earlier.  A switch reads a lane only until it is
-- cut, but a pin past the cut whose connect is uncut it keeps, reading the
-- cut no later than the connect (`lanes-left`).
--
-- KEEPING THE ORDER MODULUS: a lane row is read only where its joiner
-- shows a row at it, and an outer row under the row that shows it, so
-- what is few before a cut in the joiner is few in what it reads there.
-- A pin waits only on what lies before its connect and on its own pins:
-- its value, its lane's subscription and its cut all lie at or before the
-- connect, and its lane's own pins show as themselves (`pin-row`).
module denotation.Laws.Join where

open import Data.Bool using (T)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Properties using (∷ʳ-injectiveˡ)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Nullary using (¬_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)

open import Tree using (FlatOp; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Events using (Pos; ix; inside)
open import denotation.EmissionSet using (out; skip; end; pin; EmissionSet; _≺_; _≼_; Den; enter; After; module Op)
import denotation.EmissionSet as ES
open import denotation.Laws.Modulus
  using (≺-trans; ≺→≼; ≼-refl; ≼-trans; ≼-or-≻; ≺-≼-≺; ≼-≺-≺; ≺-ext; AgreeTo; ⟨_⟩; upto; AgreeTo-sym; _~⟨_⟩_; ~-cold)
open import denotation.Laws.Count
  using (Cnt; DCnt; AgC; agc; ag-cnt; _≈ᶜ⟨_∣_⟩_; ≈ᶜ-sym; cnt-up; cnt-down; cnt-at; dcnt-pin; dcnt-pin-up; pinned-after; trunc-ag; Img; em; seen; seen-under)
open import denotation.Laws.Worlds using (Ok; InvAt; InvD; world-after; ok-in; ok-step; ⊑-≼; inside-⊑)
open import denotation.Laws.JoinInv using (switch-cut-up)
open import denotation.Laws.Nth using (module Nths)

-- A condition on every value: read at or before `Q`, free past it.
over : ∀ {A Q} {t t′ : EmissionSet A} → AgreeTo Q t t′ → (P : Pos → Set) → (∀ {k} → Q ≺ k → P k)
     → (∀ {k b} → t k (out b) → P k) → ∀ {k b} → t′ k (out b) → P k
over {Q = Q} a P far h {k} x with ≼-or-≻ k Q
... | inj₁ kQ = h (proj₂ (upto a {k} kQ) x)
... | inj₂ Qk = far Qk

module Join {A B : Set} (Q : Pos) where
  below : ∀ x y → x ≺ y → y ≼ Q → x ≼ Q
  below x y xy yQ = ≺→≼ {x} {Q} (≺-≼-≺ {x} {y} {Q} xy yQ)

  trans≼ : ∀ x y → x ≼ y → y ≼ Q → x ≼ Q
  trans≼ x y xy yQ = ≼-trans {x} {y} {Q} xy yQ

  beyond : ∀ x y → x ≼ Q → Q ≺ y → x ≼ y
  beyond x y xQ Qy = ≺→≼ {x} {y} (≼-≺-≺ {x} {Q} {y} xQ Qy)

  fwd : ∀ {X} {t t′ : EmissionSet X} {R} → AgreeTo R t t′ → ∀ y {e} → y ≼ R → t y e → t′ y e
  fwd a y yR = proj₁ (upto a {y} yR)

  bwd : ∀ {X} {t t′ : EmissionSet X} {R} → AgreeTo R t t′ → ∀ y {e} → y ≼ R → t′ y e → t y e
  bwd a y yR = proj₂ (upto a {y} yR)

  -- A lane at `q ++ [ ix 1 ]` with a row at or before the bound.
  value-below : ∀ q k → (q ++ [ ix 1 ]) ≺ k → k ≼ Q → q ≼ Q
  value-below q k sk kQ = below q k (≺-trans {q} {q ++ [ ix 1 ]} {k} (≺-ext q []) sk) kQ

  -- Unended before `x`: past the bound by order.
  unended : ∀ {X} {t t′ : EmissionSet X} → (∀ c → c ≼ Q → t′ c ES.end → t c ES.end) → ∀ x → x ≼ Q
          → (∀ {c} → t c ES.end → x ≼ c) → ∀ {c} → t′ c ES.end → x ≼ c
  unended tr x xQ nl {c} y with ≼-or-≻ c Q
  ... | inj₁ cQ = nl (tr c cQ y)
  ... | inj₂ Qc = beyond x c xQ Qc

  least-to : ∀ {o o′ : EmissionSet A} → AgreeTo Q o o′ → ∀ q → q ≼ Q
           → (∀ {k b} → o k (out b) → q ≼ k) → ∀ {k b} → o′ k (out b) → q ≼ k
  least-to ao q qQ mn = over ao (λ k → q ≼ k) (λ {k} Qk → beyond q k qQ Qk) mn

  next-to : ∀ {o o′ : EmissionSet A} → AgreeTo Q o o′ → ∀ q q′ → q′ ≼ Q → ES.Values.Next o q q′ → ES.Values.Next o′ q q′
  next-to ao q q′ q′Q nx = over ao (λ k → q ≺ k → q′ ≼ k) (λ {k} Qk _ → beyond q′ k q′Q Qk) nx

  -- A lane row is read before its lane is cut; past it, only a pin its
  -- cut fell after.
  Read : (Pos → Pos → Set) → Pos → Pos → Set
  Read Cut q k = ¬ Cut q k

  -- A pin's connect, before it.
  conn≼ : ∀ r k → T (inside r k) → k ≼ Q → r ≼ Q
  conn≼ r k i kQ = trans≼ r k (⊑-≼ (inside-⊑ r k i)) kQ

  -- A joiner, given its policy: its lanes, which values run them, where a
  -- lane is cut, where an end hands off, and what agreeing lanes are.
  module JoiningJ (Ln : (A → Den B) → EmissionSet A → Pos → A → EmissionSet B)
                  (Runs : (A → Den B) → EmissionSet A → Pos → Set) (Cut : (A → Den B) → EmissionSet A → Pos → Pos → Set)
                  (Hand : (A → Den B) → EmissionSet A → Pos → Set) (Lanes : EmissionSet A → (A → Den B) → (A → Den B) → Set) where
    module JF (f : A → Den B) (o : EmissionSet A) = ES.Joining (Ln f o) o (λ _ _ → ⊥) (ES.Ended o) (Runs f o) (Cut f o) (Hand f o)

    JT : (A → Den B) → EmissionSet A → EmissionSet B
    JT f o = JF.JoinT f o

    -- Who runs, and where an end hands off, is read from the other side
    -- by the lanes before; a cut is read from the outer alone, and only
    -- grows; a lane row is read where it is subscribed, past its value.
    module Policy (lanes-sym : ∀ {o o′ : EmissionSet A} {f f′} → AgreeTo Q o o′ → Lanes o f f′ → Lanes o′ f′ f)
                  (lane-to : ∀ {f f′ : A → Den B} {o o′ : EmissionSet A} → AgreeTo Q o o′ → Lanes o f f′ → ∀ {q a k e} → o q (out a) → Runs f o q
                           → k ≼ Q → Read (Cut f o) q k → Ln f o q a k e → Ln f′ o′ q a k e)
                  (lane-past : ∀ {f : A → Den B} {o : EmissionSet A} {q a k e} → Ln f o q a k e → q ≺ k)
                  (runs-to : ∀ {f f′ : A → Den B} {o o′ : EmissionSet A} → AgreeTo Q o o′ → Lanes o f f′ → ∀ q → q ≼ Q → Runs f o q → Runs f′ o′ q)
                  (cut-to : ∀ {f f′ : A → Den B} {o o′ : EmissionSet A} → AgreeTo Q o o′ → ∀ q k → k ≼ Q → Cut f o q k → Cut f′ o′ q k)
                  (cut-up : ∀ {f : A → Den B} {o : EmissionSet A} {q k y} → Cut f o q k → k ≼ y → Cut f o q y)
                  (hand-to : ∀ {f f′ : A → Den B} {o o′ : EmissionSet A} → AgreeTo Q o o′ → Lanes o f f′ → ∀ c → c ≼ Q → Hand f o c → Hand f′ o′ c)
                  (left-to : ∀ {f f′ : A → Den B} {o o′ : EmissionSet A} → AgreeTo Q o o′ → Lanes o f f′ → ∀ {q a k r} → o q (out a) → Runs f o q
                           → k ≼ Q → ¬ Cut f o q r → T (inside r k) → Ln f o q a k (pin r) → Ln f′ o′ q a k (pin r)) where

      done-to : ∀ {f f′ : A → Den B} {o o′ : EmissionSet A} → AgreeTo Q o o′ → Lanes o f f′ → ∀ c → c ≼ Q → JF.Done f o c → JF.Done f′ o′ c
      done-to {f} {f′} {o} ao L c cQ ((c₀ , x , c₀c) , h) =
          (c₀ , fwd ao c₀ (trans≼ c₀ c c₀c cQ) x , c₀c)
        , λ {q} {a} x′ r′ qc nc′ →
            let qQ = below q c qc cQ
                x  = bwd ao q qQ x′
                r  = runs-to (AgreeTo-sym ao) (lanes-sym ao L) q qQ r′
                (c′ , y , c′c) = h x r qc (λ ct → nc′ (cut-to {f} {f′} ao q c cQ ct))
            in c′ , lane-to ao L x r (trans≼ c′ c c′c cQ) (λ ct → nc′ (cut-to {f} {f′} ao q c cQ (cut-up ct c′c))) y , c′c

      join-to : ∀ {f f′ : A → Den B} {o o′ : EmissionSet A} → AgreeTo Q o o′ → Lanes o f f′ → ∀ y {e} → y ≼ Q → JT f o y e → JT f′ o′ y e
      join-to ao L _ yQ (JF.val {q} x)  = JF.val (fwd ao q (below q (q ++ [ ix 0 ]) (≺-ext q []) yQ) x)
      join-to ao L y yQ (JF.step x)     = JF.step (fwd ao y yQ x)
      join-to ao L y yQ (JF.opin x)     = JF.opin (fwd ao y yQ x)
      join-to ao L y yQ (JF.oend x d)   = JF.oend (fwd ao y yQ x) (done-to ao L y yQ d)
      join-to ao L y yQ (JF.opass x nd) = JF.opass (fwd ao y yQ x) (λ d → nd (done-to (AgreeTo-sym ao) (lanes-sym ao L) y yQ d))
      join-to {f} {f′} ao L y yQ (JF.lane {q} x r l nc w) =
        JF.lane (fwd ao q qQ x) (runs-to ao L q qQ r) (lane-to ao L x r yQ nc l) (λ c → nc (cut-to {f′} {f} (AgreeTo-sym ao) q y yQ c)) w
        where qQ = below q y (lane-past l) yQ
      join-to {f} {f′} ao L y yQ (JF.lend {q} x r l nc nh d) =
        JF.lend (fwd ao q qQ x) (runs-to ao L q qQ r) (lane-to ao L x r yQ nc l) (λ c → nc (cut-to {f′} {f} (AgreeTo-sym ao) q y yQ c))
                (λ h → nh (hand-to (AgreeTo-sym ao) (lanes-sym ao L) y yQ h)) (done-to ao L y yQ d)
        where qQ = below q y (lane-past l) yQ
      join-to {f} {f′} ao L y yQ (JF.lpass {q} x r l nc nh nd) =
        JF.lpass (fwd ao q qQ x) (runs-to ao L q qQ r) (lane-to ao L x r yQ nc l) (λ c → nc (cut-to {f′} {f} (AgreeTo-sym ao) q y yQ c))
                 (λ h → nh (hand-to (AgreeTo-sym ao) (lanes-sym ao L) y yQ h)) (λ d → nd (done-to (AgreeTo-sym ao) (lanes-sym ao L) y yQ d))
        where qQ = below q y (lane-past l) yQ
      join-to {f} {f′} ao L _ yQ (JF.hand {q} {c = c} x r l nc h) =
        JF.hand (fwd ao q qQ x) (runs-to ao L q qQ r) (lane-to ao L x r cQ nc l) (λ ct → nc (cut-to {f′} {f} (AgreeTo-sym ao) q c cQ ct))
                (hand-to ao L c cQ h)
        where
          cQ = below c (c ++ [ ix 0 ]) (≺-ext c []) yQ
          qQ = below q c (lane-past l) cQ
      join-to {f} {f′} ao L y yQ (JF.left {q} {r = r₀} x r l nc i) =
        JF.left (fwd ao q qQ x) (runs-to ao L q qQ r) (left-to ao L x r yQ nc i l)
                (λ c′ → nc (cut-to {f′} {f} (AgreeTo-sym ao) q r₀ (conn≼ r₀ y i yQ) c′)) i
        where qQ = below q y (lane-past l) yQ
      join-to ao L _ _ (JF.run () _)
      join-to ao L _ _ (JF.rend () _ _)
      join-to ao L _ _ (JF.rpass () _ _)
      join-to ao L _ _ (JF.rhand () _)

      agree : ∀ {f f′ : A → Den B} {o o′ : EmissionSet A} → AgreeTo Q o o′ → Lanes o f f′ → AgreeTo Q (JT f o) (JT f′ o′)
      agree ao L = ⟨ (λ {y} yQ → join-to ao L y yQ , join-to (AgreeTo-sym ao) (lanes-sym ao L) y yQ) ⟩

  -- A JOINER: each lane at its value's second child, never handing off.
  module JoinerJ (Runs : (A → Den B) → EmissionSet A → Pos → Set) (Cut : (A → Den B) → EmissionSet A → Pos → Pos → Set) where
    -- Every lane the outer runs agrees at each row it reads.
    record Lanes (o : EmissionSet A) (f f′ : A → Den B) : Set where
      constructor lanes
      field lanes-at : ∀ {q a k} → o q (out a) → Runs f o q → q ≼ Q → k ≼ Q → Read (Cut f o) q k
                     → AgreeTo k (enter (f a) (q ++ [ ix 1 ])) (enter (f′ a) (q ++ [ ix 1 ]))
            -- A pin whose connect is uncut, at or before the bound.
            lanes-left : ∀ {q a k r} → o q (out a) → Runs f o q → q ≼ Q → k ≼ Q → ¬ Cut f o q r → T (inside r k)
                       → (enter (f a) (q ++ [ ix 1 ]) k (pin r) → enter (f′ a) (q ++ [ ix 1 ]) k (pin r))
                       × (enter (f′ a) (q ++ [ ix 1 ]) k (pin r) → enter (f a) (q ++ [ ix 1 ]) k (pin r))
    open Lanes public

    open JoiningJ (λ f _ → ES.LaneOf f) Runs Cut (λ _ _ _ → ⊥) Lanes public using (JT)

    lane-to : ∀ {o : EmissionSet A} {f f′} → Lanes o f f′ → ∀ {q a k e} → o q (out a) → Runs f o q → k ≼ Q → Read (Cut f o) q k
            → After (f a) (q ++ [ ix 1 ]) k e → After (f′ a) (q ++ [ ix 1 ]) k e
    lane-to L {q} {k = k} x r kQ rd (y , sk) = fwd (lanes-at L x r (value-below q k sk kQ) kQ rd) k (≼-refl {k}) y , sk

    -- Who runs is read from the other side by the lanes run before.
    module Policy (runs-from : ∀ {f f′ : A → Den B} {o o′ : EmissionSet A} → AgreeTo Q o o′ → Lanes o f f′ → ∀ q → q ≼ Q → Runs f′ o′ q → Runs f o q)
                  (cut-to : ∀ {f f′ : A → Den B} {o o′ : EmissionSet A} → AgreeTo Q o o′ → ∀ q k → k ≼ Q → Cut f o q k → Cut f′ o′ q k)
                  (cut-up : ∀ {f : A → Den B} {o : EmissionSet A} {q k y} → Cut f o q k → k ≼ y → Cut f o q y) where
      read-from : ∀ {f f′ : A → Den B} {o o′ : EmissionSet A} → AgreeTo Q o o′ → ∀ q k → k ≼ Q → Read (Cut f′ o′) q k → Read (Cut f o) q k
      read-from {f} {f′} ao q k kQ nc c = nc (cut-to {f} {f′} ao q k kQ c)

      lanes-sym : ∀ {o o′ : EmissionSet A} {f f′} → AgreeTo Q o o′ → Lanes o f f′ → Lanes o′ f′ f
      lanes-sym {o} {o′} {f} {f′} ao L = lanes
        (λ {q} {_} {k} x r qQ kQ rd → AgreeTo-sym (lanes-at L (bwd ao q qQ x) (runs-from ao L q qQ r) qQ kQ (read-from {f} {f′} ao q k kQ rd)))
        (λ {q} {_} {k} {r₀} x r qQ kQ nc i →
           let (to , from) = lanes-left L (bwd ao q qQ x) (runs-from ao L q qQ r) qQ kQ (λ c₀ → nc (cut-to {f} {f′} ao q r₀ (conn≼ r₀ k i kQ) c₀)) i
           in from , to)

      runs-to : ∀ {f f′ : A → Den B} {o o′ : EmissionSet A} → AgreeTo Q o o′ → Lanes o f f′ → ∀ q → q ≼ Q → Runs f o q → Runs f′ o′ q
      runs-to ao L = runs-from (AgreeTo-sym ao) (lanes-sym ao L)

      open JoiningJ (λ f _ → ES.LaneOf f) Runs Cut (λ _ _ _ → ⊥) Lanes using (module Policy)
      open Policy lanes-sym (λ ao L x r kQ rd l → lane-to L x r kQ rd l) (λ {_} {_} {q} (_ , sk) → ≺-trans {q} {q ++ [ ix 1 ]} (≺-ext q []) sk)
                  runs-to cut-to cut-up (λ _ _ _ _ ())
                  (λ ao L {q} {_} {k} x r kQ nc i (y , sk) → proj₁ (lanes-left L x r (value-below q k sk kQ) kQ nc i) y , sk) public

  -- Every value runs, and no lane is cut.
  module MergeJ where
    open JoinerJ (λ _ _ _ → ⊤) (λ _ _ _ _ → ⊥) public
    open Policy (λ _ _ _ _ _ → tt) (λ _ _ _ _ ()) (λ ()) public

  module SwitchJ where
    open JoinerJ (λ _ _ _ → ⊤) ES.Switch.Cut public

    cut-to : ∀ {f f′ : A → Den B} {o o′ : EmissionSet A} → AgreeTo Q o o′ → ∀ q k → k ≼ Q → ES.Switch.Cut f o q k → ES.Switch.Cut f′ o′ q k
    cut-to ao q k kQ (q′ , a′ , x , qq′ , q′k) = q′ , a′ , fwd ao q′ (below q′ k q′k kQ) x , qq′ , q′k

    open Policy (λ _ _ _ _ _ → tt) (λ {f} {f′} {o} {o′} → cut-to {f} {f′} {o} {o′})
                (λ {f} {o} {q} {k} {y} → switch-cut-up f o {q} {k} {y}) public

  module ExhaustJ where
    open ES.Exhaust using (Cur; cur₀; run; drop; Run)
    open JoinerJ Run (λ _ _ _ _ → ⊥) public

    cur-le : ∀ {f : A → Den B} {o : EmissionSet A} {q₁ q} → Cur f o q₁ q → q ≼ q₁
    cur-le {q₁ = q₁} (cur₀ _ _)            = ≼-refl {q₁}
    cur-le {q₁ = q₂} (run _ _ _ _ _ _ _)    = ≼-refl {q₂}
    cur-le (drop {q₁} {q} {q₂ = q₂} cu _ _ _ lt _) = ≺→≼ {q} {q₂} (≼-≺-≺ {q} {q₁} {q₂} (cur-le cu) lt)

    -- The last lane run ran.
    cur-run : ∀ {f : A → Den B} {o : EmissionSet A} {q₁ q} → Cur f o q₁ q → Cur f o q q
    cur-run (cur₀ x mn)            = cur₀ x mn
    cur-run (run cu x l c x₂ lt nx) = run cu x l c x₂ lt nx
    cur-run (drop cu _ _ _ _ _)    = cur-run cu

    -- From the other side, by the lanes run before.
    cur-from : ∀ {f f′ : A → Den B} {o o′ : EmissionSet A} → AgreeTo Q o o′ → Lanes o f f′ → ∀ q₁ q → q₁ ≼ Q → Cur f′ o′ q₁ q → Cur f o q₁ q
    cur-from ao L q₁ _ q₁Q (cur₀ x mn) = cur₀ (bwd ao q₁ q₁Q x) (least-to (AgreeTo-sym ao) q₁ q₁Q mn)
    cur-from ao L q₂ _ q₂Q (run {q₁} {q} {a} {c} cu x l cq₂ x₂ lt nx) =
      run cu₀ x₀ (bwd (lanes-at L x₀ (cur-run cu₀) qQ cQ (λ ())) c (≼-refl {c}) (proj₁ l) , proj₂ l) cq₂ (bwd ao q₂ q₂Q x₂) lt
          (next-to (AgreeTo-sym ao) q₁ q₂ q₂Q nx)
      where
        q₁Q = below q₁ q₂ lt q₂Q
        qQ  = trans≼ q q₁ (cur-le cu) q₁Q
        cQ  = below c q₂ cq₂ q₂Q
        cu₀ = cur-from ao L q₁ q q₁Q cu
        x₀  = bwd ao q qQ x
    cur-from {f} {f′} ao L q₂ q q₂Q (drop {q₁} {a = a} cu x nl x₂ lt nx) =
      drop cu₀ x₀ (unended {t = After (f′ a) (q ++ [ ix 1 ])} {After (f a) (q ++ [ ix 1 ])}
                     (λ c cQ y → fwd (lanes-at L x₀ (cur-run cu₀) qQ cQ (λ ())) c (≼-refl {c}) (proj₁ y) , proj₂ y) q₂ q₂Q nl)
           (bwd ao q₂ q₂Q x₂) lt (next-to (AgreeTo-sym ao) q₁ q₂ q₂Q nx)
      where
        q₁Q = below q₁ q₂ lt q₂Q
        qQ  = trans≼ q q₁ (cur-le cu) q₁Q
        cu₀ = cur-from ao L q₁ q q₁Q cu
        x₀  = bwd ao q qQ x

    open Policy (λ ao L q qQ → cur-from ao L q q qQ) (λ _ _ _ _ ()) (λ ()) public

  module BoundedJ (n : ℕ) where
    open ES.Values using (Nth; first; next)
    open ES.Bounded using (Kth; Starts; room; freed; queued; Ends; Sched; Sub; Queued; Lane; Indexed)

    -- Every lane subscribed at or before the bound agrees there.
    record Lanes (o : EmissionSet A) (f f′ : A → Den B) : Set where
      constructor lanes
      field lanes-at : ∀ {i q s a} → Sub n f o i q s a → s ≼ Q → AgreeTo Q (enter (f a) s) (enter (f′ a) s)
    open Lanes

    -- Two lists of lanes, each by its ends, agreeing at and below the bound.
    data LAg : List (Pos → Set) → List (Pos → Set) → Set₁ where
      none : LAg [] []
      _&_  : ∀ {l l′ ls ls′} → (∀ c → c ≼ Q → (l c → l′ c) × (l′ c → l c)) → LAg ls ls′ → LAg (l ∷ ls) (l′ ∷ ls′)

    lag-sym : ∀ {ls ls′} → LAg ls ls′ → LAg ls′ ls
    lag-sym none    = none
    lag-sym (g & L) = (λ c cQ → proj₂ (g c cQ) , proj₁ (g c cQ)) & lag-sym L

    -- `Kth` reads neither family, so both are named.
    kth-to : ∀ (f f′ : A → Den B) (o o′ : EmissionSet A) {P ls ls′} → LAg ls ls′ → (∀ c → P c → c ≼ Q)
           → ∀ k → Kth n f o P ls k → Kth n f′ o′ P ls′ k
    kth-to f f′ o o′ none    bP k ()
    kth-to f f′ o o′ (g & L) bP zero    (inj₁ (c , y , pc))       = inj₁ (c , proj₁ (g c (bP c pc)) y , pc)
    kth-to f f′ o o′ (g & L) bP zero    (inj₂ r)                  = inj₂ (kth-to f f′ o o′ L bP zero r)
    kth-to f f′ o o′ (g & L) bP (suc k) (inj₁ ((c , y , pc) , r)) = inj₁ ((c , proj₁ (g c (bP c pc)) y , pc) , kth-to f f′ o o′ L bP k r)
    kth-to f f′ o o′ (g & L) bP (suc k) (inj₂ r)                  = inj₂ (kth-to f f′ o o′ L bP (suc k) r)

    -- What a subscription `x ++ [ ix 1 ]` hangs on lies at or before the bound.
    Stem : Pos → Set
    Stem s = ∀ x → s ≡ x ++ [ ix 1 ] → x ≼ Q

    stem-≼ : ∀ s → s ≼ Q → Stem s
    stem-≼ s sQ x refl = below x (x ++ [ ix 1 ]) (≺-ext x []) sQ

    stem-at : ∀ c → c ≼ Q → Stem (c ++ [ ix 1 ])
    stem-at c cQ x e = subst (_≼ Q) (∷ʳ-injectiveˡ c x e) cQ

    starts-q : ∀ {f : A → Den B} {o : EmissionSet A} {i q ls s} → Stem s → Starts n f o i q ls s → q ≼ Q
    starts-q {q = q} st (room _)                = st q refl
    starts-q {q = q} st (freed _ _)             = st q refl
    starts-q {q = q} st (queued {c} _ qc _ _ _) = below q c qc (st c refl)

    starts-to : ∀ {f f′ : A → Den B} {o o′ : EmissionSet A} {i q ls ls′ s} → LAg ls ls′ → Stem s → Starts n f o i q ls s → Starts n f′ o′ i q ls′ s
    starts-to L st (room lt) = room lt
    starts-to {f} {f′} {o} {o′} {q = q} L st (freed le h) =
      freed le (kth-to f f′ o o′ L (λ c cq → below c q cq (st q refl)) _ h)
    starts-to {f} {f′} {o} {o′} L st (queued {c} le qc one h nh) =
      queued le qc (kth-to f f′ o o′ L (λ { c′ refl → cQ }) 0 one) (kth-to f f′ o o′ L (λ c′ c′c → trans≼ c′ c c′c cQ) _ h)
             (λ h′ → nh (kth-to f′ f o′ o (lag-sym L) (λ c′ c′c → below c′ c c′c cQ) _ h′))
      where cQ = st c refl

    nth-to : ∀ {o o′ : EmissionSet A} {i q a} → AgreeTo Q o o′ → q ≼ Q → Nth o i q a → Nth o′ i q a
    nth-to {q = q} ao qQ (first x mn)                = first (fwd ao q qQ x) (least-to ao q qQ mn)
    nth-to {q = q′} ao q′Q (next {q = q} N x lt nx)  =
      next (nth-to ao (below q q′ lt q′Q) N) (fwd ao q′ q′Q x) lt (next-to ao q q′ q′Q nx)

    -- The schedules agree lane by lane, each lane read where it is subscribed.
    sched-ag : ∀ {f f′ : A → Den B} {o o′ : EmissionSet A} → AgreeTo Q o o′ → Lanes o f f′ → ∀ i → LAg (Sched n f o i) (Sched n f′ o′ i)
    sched-ag ao L zero    = none
    sched-ag {f} {f′} {o} {o′} ao L (suc i) = (λ c cQ → there c cQ , back c cQ) & G
      where
        G = sched-ag ao L i

        there : ∀ c → c ≼ Q → Ends n f o i (Sched n f o i) c → Ends n f′ o′ i (Sched n f′ o′ i) c
        there c cQ (q , a , s , N , St , (y , sc)) =
          q , a , s , nth-to ao (starts-q st St) N , starts-to G st St , fwd (lanes-at L (N , St) sQ) c cQ y , sc
          where
            sQ = below s c sc cQ
            st = stem-≼ s sQ

        back : ∀ c → c ≼ Q → Ends n f′ o′ i (Sched n f′ o′ i) c → Ends n f o i (Sched n f o i) c
        back c cQ (q , a , s , N′ , St′ , (y′ , sc)) =
          q , a , s , N , St , bwd (lanes-at L (N , St) sQ) c cQ y′ , sc
          where
            sQ = below s c sc cQ
            st = stem-≼ s sQ
            N  = nth-to (AgreeTo-sym ao) (starts-q st St′) N′
            St = starts-to (lag-sym G) st St′

    sub-to : ∀ {f f′ : A → Den B} {o o′ : EmissionSet A} → AgreeTo Q o o′ → Lanes o f f′ → ∀ {i q s a} → Stem s → Sub n f o i q s a → Sub n f′ o′ i q s a
    sub-to ao L {i} st (N , St) = nth-to ao (starts-q st St) N , starts-to (sched-ag ao L i) st St

    sub-from : ∀ {f f′ : A → Den B} {o o′ : EmissionSet A} → AgreeTo Q o o′ → Lanes o f f′ → ∀ {i q s a} → Stem s → Sub n f′ o′ i q s a → Sub n f o i q s a
    sub-from ao L {i} st (N , St) = nth-to (AgreeTo-sym ao) (starts-q st St) N , starts-to (lag-sym (sched-ag ao L i)) st St

    lanes-sym : ∀ {o o′ : EmissionSet A} {f f′} → AgreeTo Q o o′ → Lanes o f f′ → Lanes o′ f′ f
    lanes-sym ao L = lanes λ {_} {_} {s} sb sQ → AgreeTo-sym (lanes-at L (sub-from ao L (stem-≼ s sQ) sb) sQ)

    lane-to : ∀ {o : EmissionSet A} {f f′} → Lanes o f f′ → ∀ {i q s a k e} → Sub n f o i q s a → k ≼ Q
            → After (f a) s k e → After (f′ a) s k e
    lane-to L {s = s} {k = k} sb kQ (y , sk) = fwd (lanes-at L sb (below s k sk kQ)) k kQ y , sk

    queued-to : ∀ {f f′ : A → Den B} {o o′ : EmissionSet A} → AgreeTo Q o o′ → Lanes o f f′ → ∀ c → c ≼ Q → Queued n f o c → Queued n f′ o′ c
    queued-to ao L c cQ (i , q , a , sb) = i , q , a , sub-to ao L (stem-at c cQ) sb

    -- A lane starts past its value.
    starts-past : ∀ {f : A → Den B} {o : EmissionSet A} {i q ls s} → Starts n f o i q ls s → q ≺ s
    starts-past {q = q} (room _)    = ≺-ext q []
    starts-past {q = q} (freed _ _) = ≺-ext q []
    starts-past {q = q} (queued {c} _ qc _ _ _) = ≺-trans {q} {c} {c ++ [ ix 1 ]} qc (≺-ext c [])

    lane-fwd : ∀ {f f′ : A → Den B} {o o′ : EmissionSet A} → AgreeTo Q o o′ → Lanes o f f′ → ∀ {q a k e} → k ≼ Q → Lane n f o q a k e → Lane n f′ o′ q a k e
    lane-fwd {f} {f′} {o} {o′} ao L {k = k} kQ (i , s , sb , (y , sk)) = i , s , sub-to ao L (stem-≼ s (below s k sk kQ)) sb , lane-to {o} {f} {f′} L sb kQ (y , sk)

    open JoiningJ (λ f o → Lane n f o) (λ f o → Indexed n f o) (λ _ _ _ _ → ⊥) (λ f o → Queued n f o) Lanes using (JT; module Policy)
    module BP = Policy lanes-sym (λ ao L _ _ kQ _ l → lane-fwd ao L kQ l)
                (λ {_} {_} {q} {_} {k} (_ , s , (_ , st) , (_ , sk)) → ≺-trans {q} {s} {k} (starts-past st) sk)
                (λ ao _ q qQ (i , a , N) → i , a , nth-to ao qQ N)
                (λ _ _ _ _ ()) (λ ()) queued-to (λ ao L _ _ kQ _ _ l → lane-fwd ao L kQ l)
    open BP public

------------------------------------------------------------------------
-- Causality

-- A lane agreeing at the bound agrees at every row before it.
lane-upto : ∀ {A B : Set} q {f f′ : A → Den B} → (∀ a → f a ~⟨ q ⟩ f′ a) → ∀ q′ a {k} → k ≼ q → AgreeTo k (enter (f a) (q′ ++ [ ix 1 ])) (enter (f′ a) (q′ ++ [ ix 1 ]))
lane-upto q af q′ a {k} kq = ⟨ (λ {y} yk → upto (af a (q′ ++ [ ix 1 ])) (≼-trans {y} {k} {q} yk kq)) ⟩

-- And at the bound itself.
lane-at : ∀ {A B : Set} q {f f′ : A → Den B} → (∀ a → f a ~⟨ q ⟩ f′ a) → ∀ q′ a {k e} → k ≼ q
        → (enter (f a) (q′ ++ [ ix 1 ]) k e → enter (f′ a) (q′ ++ [ ix 1 ]) k e) × (enter (f′ a) (q′ ++ [ ix 1 ]) k e → enter (f a) (q′ ++ [ ix 1 ]) k e)
lane-at q af q′ a {k} kq = upto (af a (q′ ++ [ ix 1 ])) kq

flatMap-causal : ∀ {A B q} (op : FlatOp) {f f′ : A → Den B} {s s′ : Den A}
               → s ~⟨ q ⟩ s′ → (∀ a → f a ~⟨ q ⟩ f′ a) → Op.flatMap op f s ~⟨ q ⟩ Op.flatMap op f′ s′
flatMap-causal {A} {q = q} (mergeᶠ nothing) {f} {f′} as af = ~-cold λ p → agree (as p) L
  where
    open Join.MergeJ q
    L : ∀ {o : EmissionSet A} → Lanes o f f′
    L = lanes (λ {q′} {a} _ _ _ kq _ → lane-upto q {f = f} {f′} af q′ a kq) (λ {q′} {a} _ _ _ kq _ _ → lane-at q {f = f} {f′} af q′ a kq)
flatMap-causal {A} {q = q} (mergeᶠ (just n)) {f} {f′} as af = ~-cold λ p → BP.agree (as p) L
  where
    open Join.BoundedJ q n
    L : ∀ {o : EmissionSet A} → Lanes o f f′
    L = lanes λ {_} {_} {s} {a} _ _ → af a s
flatMap-causal {A} {q = q} switchᶠ {f} {f′} as af = ~-cold λ p → agree (as p) L
  where
    open Join.SwitchJ q
    L : ∀ {o : EmissionSet A} → Lanes o f f′
    L = lanes (λ {q′} {a} _ _ _ kq _ → lane-upto q {f = f} {f′} af q′ a kq) (λ {q′} {a} _ _ _ kq _ _ → lane-at q {f = f} {f′} af q′ a kq)
flatMap-causal {A} {q = q} exhaustᶠ {f} {f′} as af = ~-cold λ p → agree (as p) L
  where
    open Join.ExhaustJ q
    L : ∀ {o : EmissionSet A} → Lanes o f f′
    L = lanes (λ {q′} {a} _ _ _ kq _ → lane-upto q {f = f} {f′} af q′ a kq) (λ {q′} {a} _ _ _ kq _ _ → lane-at q {f = f} {f′} af q′ a kq)

------------------------------------------------------------------------
-- The order modulus

private
  -- Every bounded lane subscribes where the invariant holds: at a value, or past an earlier lane's end.
  module BOk {A B H} (m : ℕ) {g : A → Den B} {d : Den A} (Id : InvD H d) (Ig : ∀ a → InvD H (g a)) (p : Pos) (ok : Ok H p) where
    open ES.Values (enter d p) using (Nth)
    open ES.Bounded m g (enter d p) using (Kth; Starts; room; freed; queued; Ends; Sched; Sub)
    open Nths (enter d p) using (nth-val)

    val-ok : ∀ {q a} → enter d p q (out a) → Ok H (q ++ [ ix 1 ])
    val-ok {q} x = ok-step q (ok-in ok (InvAt.world (Id p ok) x) (InvAt.real (Id p ok) x))

    starts-ok : ∀ i {q a s₀} → Nth i q a → Starts i q (Sched i) s₀ → Ok H s₀
    kth-ok    : ∀ {P} i k → Kth P (Sched i) k → Σ Pos λ c → P c × Ok H c
    end-ok    : ∀ i {c} → Ends i (Sched i) c → Ok H c

    starts-ok i N (room _)    = val-ok (nth-val N)
    starts-ok i N (freed _ _) = val-ok (nth-val N)
    starts-ok i N (queued {c} _ _ one _ _) with kth-ok i 0 one
    ... | _ , refl , k₀ = ok-step c k₀

    kth-ok zero    k       ()
    kth-ok (suc i) zero    (inj₁ (c , y , pc))       = c , pc , end-ok i y
    kth-ok (suc i) zero    (inj₂ r)                  = kth-ok i zero r
    kth-ok (suc i) (suc k) (inj₁ ((c , y , pc) , _)) = c , pc , end-ok i y
    kth-ok (suc i) (suc k) (inj₂ r)                  = kth-ok i (suc k) r

    end-ok i (q , a , s₀ , N , St , (y , _)) = ok-in k₀ (InvAt.world I y) (InvAt.real I y)
      where
        k₀ = starts-ok i N St
        I  = Ig a s₀ k₀

    sub-ok : ∀ {i q s₀ a} → Sub i q s₀ a → Ok H s₀
    sub-ok {i} (N , St) = starts-ok i N St

  -- Within `n`, from each side's few-bounded cuts and pins.
  both : ∀ {B n} {t t′ : EmissionSet B}
       → (∀ {Q} → Cnt n t Q → AgreeTo Q t t′) → (∀ {Q} → Cnt n t′ Q → AgreeTo Q t′ t)
       → (∀ {y r} → T (inside r y) → DCnt n t y (pin r) → (t y (pin r) → t′ y (pin r)) × (t′ y (pin r) → t y (pin r)))
       → (∀ {y r} → T (inside r y) → DCnt n t′ y (pin r) → (t′ y (pin r) → t y (pin r)) × (t y (pin r) → t′ y (pin r)))
       → AgC n t t′
  both sd sd′ pr pr′ = agc (λ { Q (inj₁ c) → sd c ; Q (inj₂ c) → AgreeTo-sym (sd′ c) })
                           (λ { q r i (inj₁ d) → pr i d ; q r i (inj₂ d) → proj₂ (pr′ i d) , proj₁ (pr′ i d) })

  -- What one side's joiner reads, few before a cut where it is, or few
  -- before a pin's connect.
  module Keep {A B H n} {f f′ : A → Den B} {s s′ : Den A} (Is : InvD H s) (Is′ : InvD H s′) (If : ∀ a → InvD H (f a)) (If′ : ∀ a → InvD H (f′ a))
              (as : s ≈ᶜ⟨ Ok H ∣ n ⟩ s′) (af : ∀ a → f a ≈ᶜ⟨ Ok H ∣ n ⟩ f′ a) (p : Pos) (ok : Ok H p) where
    o o′ : EmissionSet A
    o  = enter s p
    o′ = enter s′ p

    Io = Is p ok

    val-ok : ∀ {q a} → o q (out a) → Ok H (q ++ [ ix 1 ])
    val-ok {q} x = ok-step q (ok-in ok (InvAt.world Io x) (InvAt.real Io x))

    -- A lane's rows lie past its subscription.
    past : ∀ {a s₀} (k₀ : Ok H s₀) {y e} → enter (f a) s₀ y e → s₀ ≺ y
    past {a} {s₀} k₀ x = world-after (InvAt.world I x) (InvAt.real I x) where I = If a s₀ k₀

    -- And its pins' connects at or past it.
    pin-past : ∀ {g : A → Den B} → (∀ a → InvD H (g a)) → ∀ {a s₀ y r} → Ok H s₀ → enter (g a) s₀ y (pin r) → s₀ ≼ r
    pin-past Ig {a} {s₀} k₀ l = pinned-after (Ig a s₀ k₀) (proj₁ k₀) l

    outer : ∀ {Q} {t : EmissionSet B} → Cnt n t Q → (∀ {y e} → o y e → y ≺ Q → ¬ ¬ Img t Q y) → AgreeTo Q o o′
    outer {Q} c im = ag-cnt (as p ok) Q (inj₁ (cnt-up c im))

    lane-ag : ∀ {Q a s₀} {t : EmissionSet B} → Ok H s₀ → Cnt n t Q
            → (∀ {y e} → enter (f a) s₀ y e → y ≺ Q → ¬ ¬ Img t Q y) → AgreeTo Q (enter (f a) s₀) (enter (f′ a) s₀)
    lane-ag {Q} {a} {s₀} k₀ c im = ag-cnt (af a s₀ k₀) Q (inj₁ (cnt-up c im))

    -- A pin of a lane, read through the joiner: its lane's rows before its
    -- connect through their images, its own pins where they lie.
    lane-pin : ∀ {a s₀ y r} {t : EmissionSet B} → Ok H s₀ → T (inside r y) → DCnt n t y (pin r)
             → (∀ {k e} → enter (f a) s₀ k e → k ≺ r → ¬ ¬ Img t r k) → (∀ {k} → enter (f a) s₀ k (pin r) → t k (pin r))
             → (enter (f a) s₀ y (pin r) → enter (f′ a) s₀ y (pin r)) × (enter (f′ a) s₀ y (pin r) → enter (f a) s₀ y (pin r))
    lane-pin {a} {s₀} {y} {r} k₀ i d im sh = af a s₀ k₀ y (pin r) (inj₁ (dcnt-pin-up i d im (λ l _ → sh l)))

    -- An outer pin, likewise.
    outer-pin : ∀ {y r} {t : EmissionSet B} → T (inside r y) → DCnt n t y (pin r)
              → (∀ {k e} → o k e → k ≺ r → ¬ ¬ Img t r k) → (∀ {k} → o k (pin r) → t k (pin r))
              → (o y (pin r) → o′ y (pin r)) × (o′ y (pin r) → o y (pin r))
    outer-pin {y} {r} i d im sh = as p ok y (pin r) (inj₁ (dcnt-pin-up i d im (λ x _ → sh x)))

    -- A lane pin's connect lies past its value.
    value-pin : ∀ {g : A → Den B} → (∀ a → InvD H (g a)) → ∀ {q a y r} → Ok H (q ++ [ ix 1 ]) → enter (g a) (q ++ [ ix 1 ]) y (pin r) → q ≼ r
    value-pin {g} Ig {q} {a} {y} {r} k₀ l = ≺→≼ {q} {r} (≺-≼-≺ {q} {q ++ [ ix 1 ]} {r} (≺-ext q []) (pin-past {g} Ig {a} {q ++ [ ix 1 ]} {y} {r} k₀ l))

    module KJ (Runs : (A → Den B) → EmissionSet A → Pos → Set) (Cut : (A → Den B) → EmissionSet A → Pos → Pos → Set)
              (cut-up : ∀ {q k y} → Cut f o q k → k ≼ y → Cut f o q y) (cut-up′ : ∀ {q k y} → Cut f′ o′ q k → k ≼ y → Cut f′ o′ q y)
              (agree : ∀ Q → AgreeTo Q o o′ → Join.JoinerJ.Lanes {A} {B} Q Runs Cut o f f′
                     → AgreeTo Q (ES.Joiner.JoinT f o (Runs f o) (Cut f o)) (ES.Joiner.JoinT f′ o′ (Runs f′ o′) (Cut f′ o′)))
              (runs-to : ∀ Q → AgreeTo Q o o′ → Join.JoinerJ.Lanes {A} {B} Q Runs Cut o f f′ → ∀ q → q ≼ Q → Runs f o q → Runs f′ o′ q)
              (runs-from : ∀ Q → AgreeTo Q o o′ → Join.JoinerJ.Lanes {A} {B} Q Runs Cut o f f′ → ∀ q → q ≼ Q → Runs f′ o′ q → Runs f o q)
              (cut-to : ∀ Q → AgreeTo Q o o′ → ∀ q k → k ≼ Q → Cut f o q k → Cut f′ o′ q k)
              (cut-from : ∀ Q → AgreeTo Q o o′ → ∀ q k → k ≼ Q → Cut f′ o′ q k → Cut f o q k) where
      open ES.Joiner f o (Runs f o) (Cut f o) using (JoinT; val; step; opin; oend; opass; lane; lend; lpass; left; run)
      module J′ = ES.Joiner f′ o′ (Runs f′ o′) (Cut f′ o′)

      img-o : ∀ {Q y e} → o y e → y ≺ Q → ¬ ¬ Img JoinT Q y
      img-o {e = out _} x yQ = seen-under (val x) yQ
      img-o {e = skip}  x yQ = seen (step x) yQ
      img-o {e = pin _} x yQ = seen (opin x) yQ
      img-o {e = end}   x yQ = em (λ d → seen (oend x d) yQ) (λ nd → seen (opass x nd) yQ)

      -- Uncut at `k`, a lane row before it shows.
      img-l : ∀ {q a k} (x : o q (out a)) → Runs f o q → ¬ Cut f o q k
            → ∀ {y e} → enter (f a) (q ++ [ ix 1 ]) y e → y ≺ k → ¬ ¬ Img JoinT k y
      img-l {q} {a} {k} x r rd {y} {e} l yk = em (λ cy _ → rd (cut-up cy (≺→≼ {y} {k} yk))) (go e l)
        where
          ly : ∀ {e′} → enter (f a) (q ++ [ ix 1 ]) y e′ → ES.LaneOf f q a y e′
          ly l′ = l′ , past {a = _} (val-ok x) l′
          go : ∀ e′ → enter (f a) (q ++ [ ix 1 ]) y e′ → ¬ Cut f o q y → ¬ ¬ Img JoinT k y
          go (out _) l′ nc = seen (lane x r (ly l′) nc tt) yk
          go skip    l′ nc = seen (lane x r (ly l′) nc tt) yk
          go (pin _) l′ nc = seen (lane x r (ly l′) nc tt) yk
          go end     l′ nc = em (λ d → seen (lend x r (ly l′) nc (λ ()) d) yk) (λ nd → seen (lpass x r (ly l′) nc (λ ()) nd) yk)

      -- A lane pin whose connect is uncut: the lane is read up to the connect, and at its own pins.
      pin-ag : ∀ {q a y r} → o q (out a) → Runs f o q → ¬ Cut f o q r → T (inside r y) → DCnt n JoinT y (pin r)
             → (enter (f a) (q ++ [ ix 1 ]) y (pin r) → enter (f′ a) (q ++ [ ix 1 ]) y (pin r))
             × (enter (f′ a) (q ++ [ ix 1 ]) y (pin r) → enter (f a) (q ++ [ ix 1 ]) y (pin r))
      pin-ag {q} {a} x r nc i d =
        lane-pin (val-ok x) i d (img-l x r nc) λ l → left x r (l , past (val-ok x) l) nc (proj₂ (InvAt.pinned (If a (q ++ [ ix 1 ]) (val-ok x)) l))

      ao-at : ∀ {Q} → Cnt n JoinT Q → AgreeTo Q o o′
      ao-at c = outer c img-o

      L-at : ∀ {Q} → Cnt n JoinT Q → Join.JoinerJ.Lanes {A} {B} Q Runs Cut o f f′
      L-at {Q} c = lanes (λ {q} {a} {k} x r _ kQ rd → lane-ag (val-ok x) (cnt-down c kQ) (img-l x r rd))
                         (λ x r _ kQ nc i → pin-ag x r nc i (cnt-at c kQ))
        where open Join.JoinerJ {A} {B} Q Runs Cut using (lanes)

      side : ∀ {Q} → Cnt n JoinT Q → AgreeTo Q JoinT J′.JoinT
      side {Q} c = agree Q (ao-at c) (L-at c)

      -- A pin: an outer one, or a lane's whose connect is uncut, each read
      -- at itself and before its connect.
      pin-row : ∀ {y r} → T (inside r y) → DCnt n JoinT y (pin r) → (JoinT y (pin r) → J′.JoinT y (pin r)) × (J′.JoinT y (pin r) → JoinT y (pin r))
      pin-row {y} {r} i d = to , from
        where
          c : Cnt n JoinT r
          c = dcnt-pin i d

          ao : AgreeTo r o o′
          ao = ao-at c

          L = L-at c

          ry : r ≼ y
          ry = ⊑-≼ (inside-⊑ r y i)

          op = outer-pin i d img-o opin

          to-lane : ∀ {q a} → o q (out a) → Runs f o q → ¬ Cut f o q r → ES.LaneOf f q a y (pin r) → J′.JoinT y (pin r)
          to-lane {q} {a} x rn nc (l , ps) =
            J′.left (proj₁ (upto ao {q} qr) x) (runs-to r ao L q qr rn) (proj₁ (pin-ag x rn nc i d) l , ps) (λ c′ → nc (cut-from r ao q r (≼-refl {r}) c′)) i
            where qr = value-pin {f} If {q} {a} {y} {r} (val-ok x) l

          to : JoinT y (pin r) → J′.JoinT y (pin r)
          to (opin x)           = J′.opin (proj₁ op x)
          to (lane x rn l nc _) = to-lane x rn (λ cr → nc (cut-up cr ry)) l
          to (left x rn l nc _) = to-lane x rn nc l
          to (run () _)

          from-lane : ∀ {q a} → o′ q (out a) → Runs f′ o′ q → ¬ Cut f′ o′ q r → ES.LaneOf f′ q a y (pin r) → JoinT y (pin r)
          from-lane {q} {a} x′ rn′ nc′ (l′ , ps) = left x rn (proj₂ (pin-ag x rn nc i d) l′ , ps) nc i
            where
              qr : q ≼ r
              qr = value-pin {f′} If′ {q} {a} {y} {r} (ok-step q (ok-in ok (InvAt.world (Is′ p ok) x′) (InvAt.real (Is′ p ok) x′))) l′
              x : o q (out a)
              x = proj₂ (upto ao {q} qr) x′
              rn : Runs f o q
              rn = runs-from r ao L q qr rn′
              nc : ¬ Cut f o q r
              nc cr = nc′ (cut-to r ao q r (≼-refl {r}) cr)

          from : J′.JoinT y (pin r) → JoinT y (pin r)
          from (J′.opin x′)            = opin (proj₂ op x′)
          from (J′.lane x′ rn′ l′ nc′ _) = from-lane x′ rn′ (λ cr → nc′ (cut-up′ cr ry)) l′
          from (J′.left x′ rn′ l′ nc′ _) = from-lane x′ rn′ nc′ l′
          from (J′.run () _)

    module KM = KJ (λ _ _ _ → ⊤) (λ _ _ _ _ → ⊥) (λ ()) (λ ()) (λ Q → Join.MergeJ.agree {A} {B} Q)
                   (λ _ _ _ _ _ _ → tt) (λ _ _ _ _ _ _ → tt) (λ _ _ _ _ _ ()) (λ _ _ _ _ _ ())
    module KS = KJ (λ _ _ _ → ⊤) ES.Switch.Cut (λ {q} {k} {y} → switch-cut-up f o {q} {k} {y}) (λ {q} {k} {y} → switch-cut-up f′ o′ {q} {k} {y})
                   (λ Q → Join.SwitchJ.agree {A} {B} Q) (λ _ _ _ _ _ _ → tt) (λ _ _ _ _ _ _ → tt)
                   (λ Q ao → Join.SwitchJ.cut-to {A} {B} Q {f} {f′} {o} {o′} ao) (λ Q ao → Join.SwitchJ.cut-to {A} {B} Q {f′} {f} {o′} {o} (AgreeTo-sym ao))
    module KE = KJ ES.Exhaust.Run (λ _ _ _ _ → ⊥) (λ ()) (λ ()) (λ Q → Join.ExhaustJ.agree {A} {B} Q)
                   (λ Q → Join.ExhaustJ.runs-to {A} {B} Q) (λ Q ao L q qQ → Join.ExhaustJ.cur-from {A} {B} Q ao L q q qQ)
                   (λ _ _ _ _ _ ()) (λ _ _ _ _ _ ())

    module KB (m : ℕ) where
      open ES.Bounded m f o using (JoinT; Lane; val; step; opin; oend; opass; lane; hand; lend; lpass; left; run)
      module J′ = ES.Bounded m f′ o′
      open BOk {A} {B} {H} m {f} {s} Is If p ok using (sub-ok)
      module O′ = BOk {A} {B} {H} m {f′} {s′} Is′ If′ p ok

      img-o : ∀ {Q y e} → o y e → y ≺ Q → ¬ ¬ Img JoinT Q y
      img-o {e = out _} x yQ = seen-under (val x) yQ
      img-o {e = skip}  x yQ = seen (step x) yQ
      img-o {e = pin _} x yQ = seen (opin x) yQ
      img-o {e = end}   x yQ = em (λ d → seen (oend x d) yQ) (λ nd → seen (opass x nd) yQ)

      img-l : ∀ {i q s₀ a} (sb : ES.Bounded.Sub m f o i q s₀ a) → ∀ {Q y e} → enter (f a) s₀ y e → y ≺ Q → ¬ ¬ Img JoinT Q y
      img-l {i} {s₀ = s₀} {a} sb {e = out _} l yQ = seen (lane (nth-val (proj₁ sb)) (i , a , proj₁ sb) (i , s₀ , sb , l , past (sub-ok sb) l) (λ ()) tt) yQ
        where open Nths o using (nth-val)
      img-l {i} {s₀ = s₀} {a} sb {e = skip}  l yQ = seen (lane (nth-val (proj₁ sb)) (i , a , proj₁ sb) (i , s₀ , sb , l , past (sub-ok sb) l) (λ ()) tt) yQ
        where open Nths o using (nth-val)
      img-l {i} {s₀ = s₀} {a} sb {e = pin _} l yQ = seen (lane (nth-val (proj₁ sb)) (i , a , proj₁ sb) (i , s₀ , sb , l , past (sub-ok sb) l) (λ ()) tt) yQ
        where open Nths o using (nth-val)
      img-l {i} {q} {s₀} {a} sb {y = y} {e = end} l yQ =
        em (λ qd → seen-under (hand x r ly (λ ()) qd) yQ)
           (λ nq → em (λ d → seen (lend x r ly (λ ()) nq d) yQ) (λ nd → seen (lpass x r ly (λ ()) nq nd) yQ))
        where
          open Nths o using (nth-val)
          x : o q (out a)
          x = nth-val (proj₁ sb)
          r : ES.Bounded.Indexed m f o q
          r = i , a , proj₁ sb
          ly : Lane q a y end
          ly = i , s₀ , sb , l , past (sub-ok sb) l

      -- A lane pin: the lane is read up to the connect, and at its own pins.
      pin-ag : ∀ {i q s₀ a y r} (sb : ES.Bounded.Sub m f o i q s₀ a) → T (inside r y) → DCnt n JoinT y (pin r)
             → (enter (f a) s₀ y (pin r) → enter (f′ a) s₀ y (pin r)) × (enter (f′ a) s₀ y (pin r) → enter (f a) s₀ y (pin r))
      pin-ag {i} {q} {s₀} {a} sb ins d =
        lane-pin (sub-ok sb) ins d (img-l sb) λ l →
          left (nth-val (proj₁ sb)) (i , a , proj₁ sb) (i , s₀ , sb , l , past (sub-ok sb) l) (λ ()) (proj₂ (InvAt.pinned (If a s₀ (sub-ok sb)) l))
        where open Nths o using (nth-val)

      ao-at : ∀ {Q} → Cnt n JoinT Q → AgreeTo Q o o′
      ao-at c = outer c img-o

      L-at : ∀ {Q} → Cnt n JoinT Q → Join.BoundedJ.Lanes {A} {B} Q m o f f′
      L-at {Q} c = lanes λ sb _ → lane-ag (sub-ok sb) c (img-l sb)
        where open Join.BoundedJ {A} {B} Q m using (lanes)

      side : ∀ {Q} → Cnt n JoinT Q → AgreeTo Q JoinT J′.JoinT
      side {Q} c = BJ.BP.agree (ao-at c) (L-at c)
        where module BJ = Join.BoundedJ {A} {B} Q m

      pin-row : ∀ {y r} → T (inside r y) → DCnt n JoinT y (pin r) → (JoinT y (pin r) → J′.JoinT y (pin r)) × (J′.JoinT y (pin r) → JoinT y (pin r))
      pin-row {y} {r} ins d = to , from
        where
          module BJ = Join.BoundedJ {A} {B} r m
          open Nths o using (nth-val)

          c : Cnt n JoinT r
          c = dcnt-pin ins d

          ao : AgreeTo r o o′
          ao = ao-at c

          L = L-at c

          op = outer-pin ins d img-o opin

          to-lane : ∀ {q a} → Lane q a y (pin r) → J′.JoinT y (pin r)
          to-lane {q} {a} (i , s₀ , sb , l , ps) =
            J′.left (proj₁ (upto ao {q} qr) (nth-val (proj₁ sb))) (i , a , BJ.nth-to ao qr (proj₁ sb))
                    (i , s₀ , BJ.sub-to ao L (BJ.stem-≼ s₀ s₀r) sb , proj₁ (pin-ag sb ins d) l , ps) (λ ()) ins
            where
              s₀r : s₀ ≼ r
              s₀r = pin-past {f} If {a} {s₀} {y} {r} (sub-ok sb) l
              qr : q ≼ r
              qr  = ≺→≼ {q} {r} (≺-≼-≺ {q} {s₀} {r} (BJ.starts-past (proj₂ sb)) s₀r)

          to : JoinT y (pin r) → J′.JoinT y (pin r)
          to (opin x)          = J′.opin (proj₁ op x)
          to (lane _ _ ly _ _) = to-lane ly
          to (left _ _ ly _ _) = to-lane ly
          to (run () _)

          from-lane : ∀ {q a} → J′.Lane q a y (pin r) → JoinT y (pin r)
          from-lane {q} {a} (i , s₀ , sb′ , l′ , ps) =
            left (nth-val (proj₁ sb)) (i , a , proj₁ sb) (i , s₀ , sb , proj₂ (pin-ag sb ins d) l′ , ps) (λ ()) ins
            where
              s₀r : s₀ ≼ r
              s₀r = pin-past {f′} If′ {a} {s₀} {y} {r} (O′.sub-ok sb′) l′
              sb : ES.Bounded.Sub m f o i q s₀ a
              sb  = BJ.sub-from ao L (BJ.stem-≼ s₀ s₀r) sb′

          from : J′.JoinT y (pin r) → JoinT y (pin r)
          from (J′.opin x′)          = opin (proj₂ op x′)
          from (J′.lane _ _ ly′ _ _) = from-lane ly′
          from (J′.left _ _ ly′ _ _) = from-lane ly′
          from (J′.run () _)

  -- Both sides' readings.
  module Sides {A B H k} {f f′ : A → Den B} {s s′ : Den A} (Is : InvD H s) (Is′ : InvD H s′) (If : ∀ a → InvD H (f a)) (If′ : ∀ a → InvD H (f′ a))
               (as : s ≈ᶜ⟨ Ok H ∣ k ⟩ s′) (af : ∀ a → f a ≈ᶜ⟨ Ok H ∣ k ⟩ f′ a) (p : Pos) (ok : Ok H p) where
    module K  = Keep {A} {B} {H} {k} {f} {f′} {s} {s′} Is Is′ If If′ as af p ok
    module K′ = Keep {A} {B} {H} {k} {f′} {f} {s′} {s} Is′ Is If′ If (≈ᶜ-sym {d = s} {s′} as) (λ a → ≈ᶜ-sym {d = f a} {f′ a} (af a)) p ok

-- EACH JOINER KEEPS THE ORDER MODULUS at admissible subscriptions: what
-- a row waits on, few in one side's joiner, is few in what it reads there.
flatMap-ne : ∀ {A B H k} (op : FlatOp) {f f′ : A → Den B} {s s′ : Den A}
           → InvD H s → InvD H s′ → (∀ a → InvD H (f a)) → (∀ a → InvD H (f′ a))
           → s ≈ᶜ⟨ Ok H ∣ k ⟩ s′ → (∀ a → f a ≈ᶜ⟨ Ok H ∣ k ⟩ f′ a) → Op.flatMap op f s ≈ᶜ⟨ Ok H ∣ k ⟩ Op.flatMap op f′ s′
flatMap-ne {A} {B} {H} {k} (mergeᶠ nothing) {f} {f′} {s} {s′} Is Is′ If If′ as af p ok =
  trunc-ag (both S.K.KM.side S.K′.KM.side S.K.KM.pin-row S.K′.KM.pin-row)
  where module S = Sides {A} {B} {H} {k} {f} {f′} {s} {s′} Is Is′ If If′ as af p ok
flatMap-ne {A} {B} {H} {k} (mergeᶠ (just m)) {f} {f′} {s} {s′} Is Is′ If If′ as af p ok =
  trunc-ag (both (S.K.KB.side m) (S.K′.KB.side m) (S.K.KB.pin-row m) (S.K′.KB.pin-row m))
  where module S = Sides {A} {B} {H} {k} {f} {f′} {s} {s′} Is Is′ If If′ as af p ok
flatMap-ne {A} {B} {H} {k} switchᶠ {f} {f′} {s} {s′} Is Is′ If If′ as af p ok =
  trunc-ag (both S.K.KS.side S.K′.KS.side S.K.KS.pin-row S.K′.KS.pin-row)
  where module S = Sides {A} {B} {H} {k} {f} {f′} {s} {s′} Is Is′ If If′ as af p ok
flatMap-ne {A} {B} {H} {k} exhaustᶠ {f} {f′} {s} {s′} Is Is′ If If′ as af p ok =
  trunc-ag (both S.K.KE.side S.K′.KE.side S.K.KE.pin-row S.K′.KE.pin-row)
  where module S = Sides {A} {B} {H} {k} {f} {f′} {s} {s′} Is Is′ If If′ as af p ok
