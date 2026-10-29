{-# OPTIONS --guardedness #-}

-- A JOINER READS A LANE ONLY WHERE IT SUBSCRIBES IT, and only past the
-- subscription, so a lane row at or before the bound has its outer value
-- there too.  The rest it reads (a cut, a latest value, a first value, an
-- unended lane) holds past the bound by order alone.
--
-- The lanes agree only where one side subscribes them (`Lanes`): what
-- shows a subscription on the other side is carried over first, by the
-- lanes it reads, each earlier.  A switch reads a lane only until it is
-- cut, and under its subscription after.
--
-- KEEPING THE ORDER MODULUS: a lane row is read only where its joiner
-- shows a row at it, and an outer row under the row that shows it, so
-- what is few before a cut in the joiner is few in what it reads there.
module denotation.EmissionSet.Laws.Join where

open import Data.Bool using (T)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Properties using (∷ʳ-injectiveˡ)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Nullary using (¬_)
open import Data.Unit using (tt)

open import Tree using (FlatOp; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.MonotonicList.Events using (Pos; ix; inside)
open import denotation.EmissionSet using (out; skip; end; EmissionSet; _≺_; _≼_; Den; enter; After; flatMapᵀ)
import denotation.EmissionSet as ES
open import denotation.EmissionSet.Laws.Modulus
  using (≺-trans; ≺→≼; ≼-refl; ≼-trans; ≼-or-≻; ≺-≼-≺; ≼-≺-≺; ≺-ext; AgreeTo; ⟨_⟩; upto; AgreeTo-sym; _~⟨_⟩_; ~-cold)
open import denotation.EmissionSet.Laws.Count using (Cnt; _≈ᶜ⟨_∣_⟩_; ≈ᶜ-sym; cnt-up; cnt-down; trunc-ag; Img; em; seen; seen-under)
open import denotation.EmissionSet.Laws.Worlds using (Ok; InvAt; InvD; world-after; ok-in; ok-step; in-world)

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

  module MergeJ where
    open ES.Merge using (Done; MergeT; val; step; oend; opass; lane; lend; lpass)

    -- Every lane the outer subscribes at or before the bound agrees there.
    record Lanes (o : EmissionSet A) (f f′ : A → Den B) : Set where
      constructor lanes
      field lanes-at : ∀ {q a} → o q (out a) → q ≼ Q → AgreeTo Q (enter (f a) (q ++ [ ix 1 ])) (enter (f′ a) (q ++ [ ix 1 ]))
    open Lanes

    lanes-sym : ∀ {o o′ : EmissionSet A} {f f′} → AgreeTo Q o o′ → Lanes o f f′ → Lanes o′ f′ f
    lanes-sym ao L = lanes λ {q} x qQ → AgreeTo-sym (lanes-at L (bwd ao q qQ x) qQ)

    lane-to : ∀ {o : EmissionSet A} {f f′} → Lanes o f f′ → ∀ {q a k e} → o q (out a) → k ≼ Q
            → After (f a) (q ++ [ ix 1 ]) k e → After (f′ a) (q ++ [ ix 1 ]) k e
    lane-to L {q} {k = k} x kQ (y , sk) = fwd (lanes-at L x (value-below q k sk kQ)) k kQ y , sk

    done-to : ∀ {f f′ : A → Den B} {o o′ : EmissionSet A} → AgreeTo Q o o′ → Lanes o f f′ → ∀ c → c ≼ Q → Done f o c → Done f′ o′ c
    done-to {f} {f′} {o} ao L c cQ ((c₀ , x , c₀c) , h) =
        (c₀ , fwd ao c₀ (trans≼ c₀ c c₀c cQ) x , c₀c)
      , λ {q} {a} x′ qc → let x = bwd ao q (below q c qc cQ) x′
                              (c′ , y , c′c) = h x qc
                          in c′ , lane-to {o} {f} {f′} L {q} {a} x (trans≼ c′ c c′c cQ) y , c′c

    merge-to : ∀ {f f′ : A → Den B} {o o′ : EmissionSet A} → AgreeTo Q o o′ → Lanes o f f′ → ∀ y {e} → y ≼ Q → MergeT f o y e → MergeT f′ o′ y e
    merge-to ao L _ yQ (val {q} x)          = val (fwd ao q (below q (q ++ [ ix 0 ]) (≺-ext q []) yQ) x)
    merge-to ao L y yQ (step x)             = step (fwd ao y yQ x)
    merge-to ao L y yQ (oend x d)           = oend (fwd ao y yQ x) (done-to ao L y yQ d)
    merge-to ao L y yQ (opass x nd)         = opass (fwd ao y yQ x) (λ d → nd (done-to (AgreeTo-sym ao) (lanes-sym ao L) y yQ d))
    merge-to ao L y yQ (lane {q} x l w)     = lane (fwd ao q (value-below q y (proj₂ l) yQ) x) (lane-to L x yQ l) w
    merge-to ao L y yQ (lend {q} x l d)     = lend (fwd ao q (value-below q y (proj₂ l) yQ) x) (lane-to L x yQ l) (done-to ao L y yQ d)
    merge-to ao L y yQ (lpass {q} x l nd)   =
      lpass (fwd ao q (value-below q y (proj₂ l) yQ) x) (lane-to L x yQ l) (λ d → nd (done-to (AgreeTo-sym ao) (lanes-sym ao L) y yQ d))

  module SwitchJ where
    open ES.Switch using (Cut; Latest; Done; SwitchT; val; step; oend; opass; lane; lend; lpass; left)

    -- A lane row is read before its lane is cut, or under its subscription.
    Read : (A → Den B) → EmissionSet A → Pos → Pos → Set
    Read f o q k = ¬ Cut f o q k ⊎ T (inside (q ++ [ ix 1 ]) k)

    -- Every lane the outer subscribes agrees at each row it reads.
    record Lanes (o : EmissionSet A) (f f′ : A → Den B) : Set where
      constructor lanes
      field lanes-at : ∀ {q a k} → o q (out a) → q ≼ Q → k ≼ Q → Read f o q k
                     → AgreeTo k (enter (f a) (q ++ [ ix 1 ])) (enter (f′ a) (q ++ [ ix 1 ]))
    open Lanes

    cut-to : ∀ (f f′ : A → Den B) {o o′ : EmissionSet A} → AgreeTo Q o o′ → ∀ q k → k ≼ Q → Cut f o q k → Cut f′ o′ q k
    cut-to f f′ ao q k kQ (q′ , a′ , x , qq′ , q′k) = q′ , a′ , fwd ao q′ (below q′ k q′k kQ) x , qq′ , q′k

    latest-to : ∀ (f f′ : A → Den B) {o o′ : EmissionSet A} → AgreeTo Q o o′ → ∀ q c → c ≼ Q → Latest f o q c → Latest f′ o′ q c
    latest-to f f′ ao q c cQ la {q′} x′ q′c = la {q′} (bwd ao q′ (below q′ c q′c cQ) x′) q′c

    lanes-sym : ∀ {o o′ : EmissionSet A} {f f′} → AgreeTo Q o o′ → Lanes o f f′ → Lanes o′ f′ f
    lanes-sym {f = f} {f′} ao L = lanes λ
      { {q} {_} {k} x qQ kQ (inj₁ nc) → AgreeTo-sym (lanes-at L (bwd ao q qQ x) qQ kQ (inj₁ λ c → nc (cut-to f f′ ao q k kQ c)))
      ; {q} x qQ kQ (inj₂ i) → AgreeTo-sym (lanes-at L (bwd ao q qQ x) qQ kQ (inj₂ i)) }

    lane-to : ∀ {o : EmissionSet A} {f f′} → Lanes o f f′ → ∀ {q a k e} → o q (out a) → k ≼ Q → Read f o q k
            → After (f a) (q ++ [ ix 1 ]) k e → After (f′ a) (q ++ [ ix 1 ]) k e
    lane-to L {q} {k = k} x kQ r (y , sk) = fwd (lanes-at L x (value-below q k sk kQ) kQ r) k (≼-refl {k}) y , sk

    -- The latest lane is not cut before `c`.
    uncut : ∀ {f : A → Den B} {o : EmissionSet A} {q c c′} → Latest f o q c → c′ ≼ c → ¬ Cut f o q c′
    uncut {q = q} {c} {c′} la c′c (q′ , _ , x , qq′ , q′c′) = la x (≺-≼-≺ {q′} {c′} {c} q′c′ c′c) qq′

    done-to : ∀ (f f′ : A → Den B) {o o′ : EmissionSet A} → AgreeTo Q o o′ → Lanes o f f′ → ∀ c → c ≼ Q → Done f o c → Done f′ o′ c
    done-to f f′ {o} {o′} ao L c cQ ((c₀ , x , c₀c) , h) =
        (c₀ , fwd ao c₀ (trans≼ c₀ c c₀c cQ) x , c₀c)
      , λ {q} {a} x′ qc la′ →
          let x  = bwd ao q (below q c qc cQ) x′
              la = latest-to f′ f {o′} {o} (AgreeTo-sym ao) q c cQ la′
              (c′ , y , c′c) = h x qc la
          in c′ , lane-to {o} {f} {f′} L {q} {a} x (trans≼ c′ c c′c cQ) (inj₁ (uncut {f = f} {o} {q} {c} {c′} la c′c)) y , c′c

    switch-to : ∀ (f f′ : A → Den B) {o o′ : EmissionSet A} → AgreeTo Q o o′ → Lanes o f f′ → ∀ y {e} → y ≼ Q → SwitchT f o y e → SwitchT f′ o′ y e
    switch-to f f′ ao L _ yQ (val {q} x)           = val (fwd ao q (below q (q ++ [ ix 0 ]) (≺-ext q []) yQ) x)
    switch-to f f′ ao L y yQ (step x)              = step (fwd ao y yQ x)
    switch-to f f′ ao L y yQ (oend x d)            = oend (fwd ao y yQ x) (done-to f f′ ao L y yQ d)
    switch-to f f′ ao L y yQ (opass x nd)          =
      opass (fwd ao y yQ x) (λ d → nd (done-to f′ f (AgreeTo-sym ao) (lanes-sym ao L) y yQ d))
    switch-to f f′ ao L y yQ (lane {q} x l w nc)   =
      lane (fwd ao q (value-below q y (proj₂ l) yQ) x) (lane-to L x yQ (inj₁ nc) l) w
           (λ c → nc (cut-to f′ f (AgreeTo-sym ao) q y yQ c))
    switch-to f f′ ao L y yQ (lend {q} x l nc d)   =
      lend (fwd ao q (value-below q y (proj₂ l) yQ) x) (lane-to L x yQ (inj₁ nc) l)
           (λ c → nc (cut-to f′ f (AgreeTo-sym ao) q y yQ c)) (done-to f f′ ao L y yQ d)
    switch-to f f′ ao L y yQ (lpass {q} x l nc nd) =
      lpass (fwd ao q (value-below q y (proj₂ l) yQ) x) (lane-to L x yQ (inj₁ nc) l)
            (λ c → nc (cut-to f′ f (AgreeTo-sym ao) q y yQ c)) (λ d → nd (done-to f′ f (AgreeTo-sym ao) (lanes-sym ao L) y yQ d))
    switch-to f f′ ao L y yQ (left {q} x l c ins)  =
      left (fwd ao q (value-below q y (proj₂ l) yQ) x) (lane-to L x yQ (inj₂ ins) l) (cut-to f f′ ao q y yQ c) ins

  module ExhaustJ where
    open ES.Exhaust using (Cur; cur₀; run; drop; Done; ExhaustT; val; step; oend; opass; lane; lend; lpass)

    -- Every lane the outer runs at or before the bound agrees there.
    record Lanes (o : EmissionSet A) (f f′ : A → Den B) : Set where
      constructor lanes
      field lanes-at : ∀ {q a} → o q (out a) → Cur f o q q → q ≼ Q → AgreeTo Q (enter (f a) (q ++ [ ix 1 ])) (enter (f′ a) (q ++ [ ix 1 ]))
    open Lanes

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
      run cu₀ x₀ (bwd (lanes-at L x₀ (cur-run cu₀) qQ) c cQ (proj₁ l) , proj₂ l) cq₂ (bwd ao q₂ q₂Q x₂) lt (next-to (AgreeTo-sym ao) q₁ q₂ q₂Q nx)
      where
        q₁Q = below q₁ q₂ lt q₂Q
        qQ  = trans≼ q q₁ (cur-le cu) q₁Q
        cQ  = below c q₂ cq₂ q₂Q
        cu₀ = cur-from ao L q₁ q q₁Q cu
        x₀  = bwd ao q qQ x
    cur-from {f} {f′} ao L q₂ q q₂Q (drop {q₁} {a = a} cu x nl x₂ lt nx) =
      drop cu₀ x₀ (unended {t = After (f′ a) (q ++ [ ix 1 ])} {After (f a) (q ++ [ ix 1 ])} (λ c cQ y → fwd (lanes-at L x₀ (cur-run cu₀) qQ) c cQ (proj₁ y) , proj₂ y) q₂ q₂Q nl)
           (bwd ao q₂ q₂Q x₂) lt (next-to (AgreeTo-sym ao) q₁ q₂ q₂Q nx)
      where
        q₁Q = below q₁ q₂ lt q₂Q
        qQ  = trans≼ q q₁ (cur-le cu) q₁Q
        cu₀ = cur-from ao L q₁ q q₁Q cu
        x₀  = bwd ao q qQ x

    lanes-sym : ∀ {o o′ : EmissionSet A} {f f′} → AgreeTo Q o o′ → Lanes o f f′ → Lanes o′ f′ f
    lanes-sym ao L = lanes λ {q} x r qQ → AgreeTo-sym (lanes-at L (bwd ao q qQ x) (cur-from ao L q q qQ r) qQ)

    cur-to : ∀ {f f′ : A → Den B} {o o′ : EmissionSet A} → AgreeTo Q o o′ → Lanes o f f′ → ∀ q₁ q → q₁ ≼ Q → Cur f o q₁ q → Cur f′ o′ q₁ q
    cur-to ao L = cur-from (AgreeTo-sym ao) (lanes-sym ao L)

    lane-to : ∀ {o : EmissionSet A} {f f′} → Lanes o f f′ → ∀ {q a k e} → o q (out a) → Cur f o q q → k ≼ Q
            → After (f a) (q ++ [ ix 1 ]) k e → After (f′ a) (q ++ [ ix 1 ]) k e
    lane-to L {q} {k = k} x r kQ (y , sk) = fwd (lanes-at L x r (value-below q k sk kQ)) k kQ y , sk

    done-to : ∀ {f f′ : A → Den B} {o o′ : EmissionSet A} → AgreeTo Q o o′ → Lanes o f f′ → ∀ c → c ≼ Q → Done f o c → Done f′ o′ c
    done-to {f} {f′} {o} ao L c cQ ((c₀ , x , c₀c) , h) =
        (c₀ , fwd ao c₀ (trans≼ c₀ c c₀c cQ) x , c₀c)
      , λ {q} {a} x′ qc r′ →
          let qQ = below q c qc cQ
              x  = bwd ao q qQ x′
              r  = cur-from ao L q q qQ r′
              (c′ , y , c′c) = h x qc r
          in c′ , lane-to {o} {f} {f′} L {q} {a} x r (trans≼ c′ c c′c cQ) y , c′c

    exhaust-to : ∀ {f f′ : A → Den B} {o o′ : EmissionSet A} → AgreeTo Q o o′ → Lanes o f f′ → ∀ y {e} → y ≼ Q → ExhaustT f o y e → ExhaustT f′ o′ y e
    exhaust-to ao L _ yQ (val {q} x)       = val (fwd ao q (below q (q ++ [ ix 0 ]) (≺-ext q []) yQ) x)
    exhaust-to ao L y yQ (step x)          = step (fwd ao y yQ x)
    exhaust-to ao L y yQ (oend x d)        = oend (fwd ao y yQ x) (done-to ao L y yQ d)
    exhaust-to ao L y yQ (opass x nd)      = opass (fwd ao y yQ x) (λ d → nd (done-to (AgreeTo-sym ao) (lanes-sym ao L) y yQ d))
    exhaust-to ao L y yQ (lane {q} x r l w) =
      lane (fwd ao q qQ x) (cur-to ao L q q qQ r) (lane-to L x r yQ l) w
      where qQ = value-below q y (proj₂ l) yQ
    exhaust-to ao L y yQ (lend {q} x r l d) =
      lend (fwd ao q qQ x) (cur-to ao L q q qQ r) (lane-to L x r yQ l) (done-to ao L y yQ d)
      where qQ = value-below q y (proj₂ l) yQ
    exhaust-to ao L y yQ (lpass {q} x r l nd) =
      lpass (fwd ao q qQ x) (cur-to ao L q q qQ r) (lane-to L x r yQ l)
            (λ d → nd (done-to (AgreeTo-sym ao) (lanes-sym ao L) y yQ d))
      where qQ = value-below q y (proj₂ l) yQ

  module BoundedJ (n : ℕ) where
    open ES.Values using (Nth; first; next)
    open ES.Bounded using (Kth; Starts; room; freed; queued; Ends; Sched; Sub; Queued; Done; BoundedT;
                           val; step; oend; opass; lane; handoff; lend; lpass)

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

    done-to : ∀ {f f′ : A → Den B} {o o′ : EmissionSet A} → AgreeTo Q o o′ → Lanes o f f′ → ∀ c → c ≼ Q → Done n f o c → Done n f′ o′ c
    done-to {f} {f′} {o} ao L c cQ ((c₀ , x , c₀c) , h) =
        (c₀ , fwd ao c₀ (trans≼ c₀ c c₀c cQ) x , c₀c)
      , λ {i} {q} {a} N′ qc →
          let (s , c′ , sb , (y , sc′) , c′c) = h (nth-to (AgreeTo-sym ao) (below q c qc cQ) N′) qc
              c′Q = trans≼ c′ c c′c cQ
          in s , c′ , sub-to ao L (stem-≼ s (below s c′ sc′ c′Q)) sb , lane-to {o} {f} {f′} L {i} {q} {s} {a} sb c′Q (y , sc′) , c′c

    bounded-to : ∀ {f f′ : A → Den B} {o o′ : EmissionSet A} → AgreeTo Q o o′ → Lanes o f f′ → ∀ y {e} → y ≼ Q → BoundedT n f o y e → BoundedT n f′ o′ y e
    bounded-to ao L _ yQ (val {q} x)    = val (fwd ao q (below q (q ++ [ ix 0 ]) (≺-ext q []) yQ) x)
    bounded-to ao L y yQ (step x)       = step (fwd ao y yQ x)
    bounded-to ao L y yQ (oend x d)     = oend (fwd ao y yQ x) (done-to ao L y yQ d)
    bounded-to ao L y yQ (opass x nd)   = opass (fwd ao y yQ x) (λ d → nd (done-to (AgreeTo-sym ao) (lanes-sym ao L) y yQ d))
    bounded-to ao L y yQ (lane {s = s} sb (x , sy) w) =
      lane (sub-to ao L (stem-≼ s (below s y sy yQ)) sb) (lane-to L sb yQ (x , sy)) w
    bounded-to ao L _ yQ (handoff {s = s} {c = c} sb (x , sc) qd) =
      handoff (sub-to ao L (stem-≼ s (below s c sc cQ)) sb) (lane-to L sb cQ (x , sc)) (queued-to ao L c cQ qd)
      where cQ = below c (c ++ [ ix 0 ]) (≺-ext c []) yQ
    bounded-to ao L y yQ (lend {s = s} sb (x , sy) nq d) =
      lend (sub-to ao L (stem-≼ s (below s y sy yQ)) sb) (lane-to L sb yQ (x , sy))
           (λ q′ → nq (queued-to (AgreeTo-sym ao) (lanes-sym ao L) y yQ q′)) (done-to ao L y yQ d)
    bounded-to ao L y yQ (lpass {s = s} sb (x , sy) nq nd) =
      lpass (sub-to ao L (stem-≼ s (below s y sy yQ)) sb) (lane-to L sb yQ (x , sy))
            (λ q′ → nq (queued-to (AgreeTo-sym ao) (lanes-sym ao L) y yQ q′)) (λ d → nd (done-to (AgreeTo-sym ao) (lanes-sym ao L) y yQ d))

------------------------------------------------------------------------
-- Causality

flatMap-causal : ∀ {A B q} (op : FlatOp) {f f′ : A → Den B} {s s′ : Den A}
               → s ~⟨ q ⟩ s′ → (∀ a → f a ~⟨ q ⟩ f′ a) → flatMapᵀ op f s ~⟨ q ⟩ flatMapᵀ op f′ s′
flatMap-causal {A} {q = q} (mergeᶠ nothing) {f} {f′} as af = ~-cold λ p →
  ⟨ (λ {y} yq → merge-to (as p) L y yq , merge-to (AgreeTo-sym (as p)) (lanes-sym (as p) L) y yq) ⟩
  where
    open Join.MergeJ q
    L : ∀ {o : EmissionSet A} → Lanes o f f′
    L = lanes λ {q′} {a} _ _ → af a (q′ ++ [ ix 1 ])
flatMap-causal {A} {q = q} (mergeᶠ (just n)) {f} {f′} as af = ~-cold λ p →
  ⟨ (λ {y} yq → bounded-to (as p) L y yq , bounded-to (AgreeTo-sym (as p)) (lanes-sym (as p) L) y yq) ⟩
  where
    open Join.BoundedJ q n
    L : ∀ {o : EmissionSet A} → Lanes o f f′
    L = lanes λ {_} {_} {s} {a} _ _ → af a s
flatMap-causal {A} {q = q} switchᶠ {f} {f′} as af = ~-cold λ p →
  ⟨ (λ {y} yq → switch-to f f′ (as p) L y yq , switch-to f′ f (AgreeTo-sym (as p)) (lanes-sym (as p) L) y yq) ⟩
  where
    open Join.SwitchJ q
    L : ∀ {o : EmissionSet A} → Lanes o f f′
    L = lanes λ {q′} {a} {k} _ _ kq _ → ⟨ (λ {y} yk → upto (af a (q′ ++ [ ix 1 ])) (≼-trans {y} {k} {q} yk kq)) ⟩
flatMap-causal {A} {q = q} exhaustᶠ {f} {f′} as af = ~-cold λ p →
  ⟨ (λ {y} yq → exhaust-to (as p) L y yq , exhaust-to (AgreeTo-sym (as p)) (lanes-sym (as p) L) y yq) ⟩
  where
    open Join.ExhaustJ q
    L : ∀ {o : EmissionSet A} → Lanes o f f′
    L = lanes λ {q′} {a} _ _ _ → af a (q′ ++ [ ix 1 ])

------------------------------------------------------------------------
-- The order modulus

private
  -- What one side's joiner reads, few before a cut where it is.
  module Keep {A B H n} {f f′ : A → Den B} {s s′ : Den A} (Is : InvD H s) (If : ∀ a → InvD H (f a))
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

    outer : ∀ {Q} {t : EmissionSet B} → Cnt n t Q → (∀ {y e} → o y e → y ≺ Q → ¬ ¬ Img t Q y) → AgreeTo Q o o′
    outer {Q} c im = as p ok Q (inj₁ (cnt-up c im))

    lane-ag : ∀ {Q a s₀} {t : EmissionSet B} → Ok H s₀ → Cnt n t Q
            → (∀ {y e} → enter (f a) s₀ y e → y ≺ Q → ¬ ¬ Img t Q y) → AgreeTo Q (enter (f a) s₀) (enter (f′ a) s₀)
    lane-ag {Q} {a} {s₀} k₀ c im = af a s₀ k₀ Q (inj₁ (cnt-up c im))

    module KM (Q : Pos) where
      open ES.Merge f o using (Done; MergeT; val; step; oend; opass; lane; lend; lpass)
      open Join.MergeJ {A} {B} Q using (lanes; merge-to; lanes-sym)

      side : Cnt n MergeT Q → AgreeTo Q MergeT (ES.Merge.MergeT f′ o′)
      side c = ⟨ (λ {y} yq → merge-to ao L y yq , merge-to (AgreeTo-sym ao) (lanes-sym ao L) y yq) ⟩
        where
          img-o : ∀ {y e} → o y e → y ≺ Q → ¬ ¬ Img MergeT Q y
          img-o {e = out _} x yQ = seen-under (val x) yQ
          img-o {e = skip}  x yQ = seen (step x) yQ
          img-o {e = end}   x yQ = em (λ d → seen (oend x d) yQ) (λ nd → seen (opass x nd) yQ)

          ao = outer c img-o

          img-l : ∀ {q a} (x : o q (out a)) {y e} → enter (f a) (q ++ [ ix 1 ]) y e → y ≺ Q → ¬ ¬ Img MergeT Q y
          img-l x {e = out _} l yQ = seen (lane x (l , past {a = _} (val-ok x) l) tt) yQ
          img-l x {e = skip}  l yQ = seen (lane x (l , past {a = _} (val-ok x) l) tt) yQ
          img-l x {e = end}   l yQ = em (λ d → seen (lend x (l , past {a = _} (val-ok x) l) d) yQ) (λ nd → seen (lpass x (l , past {a = _} (val-ok x) l) nd) yQ)

          L = lanes λ x _ → lane-ag (val-ok x) c (img-l x)

    module KS (Q : Pos) where
      open ES.Switch f o using (Cut; Done; SwitchT; val; step; oend; opass; lane; lend; lpass; left)
      open Join.SwitchJ {A} {B} Q using (lanes; switch-to; lanes-sym; Read)

      side : Cnt n SwitchT Q → AgreeTo Q SwitchT (ES.Switch.SwitchT f′ o′)
      side c = ⟨ (λ {y} yq → switch-to f f′ ao L y yq , switch-to f′ f (AgreeTo-sym ao) (lanes-sym ao L) y yq) ⟩
        where
          img-o : ∀ {y e} → o y e → y ≺ Q → ¬ ¬ Img SwitchT Q y
          img-o {e = out _} x yQ = seen-under (val x) yQ
          img-o {e = skip}  x yQ = seen (step x) yQ
          img-o {e = end}   x yQ = em (λ d → seen (oend x d) yQ) (λ nd → seen (opass x nd) yQ)

          ao = outer c img-o

          -- Read at the cut `k`, read at every lane row before it.
          img-l : ∀ {q a k} (x : o q (out a)) → k ≼ Q → Read f o q k
                → ∀ {y e} → enter (f a) (q ++ [ ix 1 ]) y e → y ≺ k → ¬ ¬ Img SwitchT k y
          img-l {q} {a} {k} x kQ r {y} {e} l yk = em (cut r) (uncut e l)
            where
              ly : ∀ {e′} → enter (f a) (q ++ [ ix 1 ]) y e′ → ES.Switch.Lane f o q a y e′
              ly l′ = l′ , past {a = _} (val-ok x) l′
              cut : Read f o q k → Cut q y → ¬ ¬ Img SwitchT k y
              cut (inj₁ nc)  (q′ , a′ , x′ , qq′ , q′y) = λ _ → nc (q′ , a′ , x′ , qq′ , ≺-trans {q′} {y} {k} q′y yk)
              cut (inj₂ ins) cy = seen (left x (ly l) cy (in-world (If a (q ++ [ ix 1 ]) (val-ok x)) l yk ins)) yk
              uncut : ∀ e′ → enter (f a) (q ++ [ ix 1 ]) y e′ → ¬ Cut q y → ¬ ¬ Img SwitchT k y
              uncut (out _) l′ nc = seen (lane x (ly l′) tt nc) yk
              uncut skip    l′ nc = seen (lane x (ly l′) tt nc) yk
              uncut end     l′ nc = em (λ d → seen (lend x (ly l′) nc d) yk) (λ nd → seen (lpass x (ly l′) nc nd) yk)

          L = lanes λ {q} {a} {k} x _ kQ r → lane-ag (val-ok x) (cnt-down c kQ) (img-l x kQ r)

    module KE (Q : Pos) where
      open ES.Exhaust f o using (Done; ExhaustT; val; step; oend; opass; lane; lend; lpass)
      open Join.ExhaustJ {A} {B} Q using (lanes; exhaust-to; lanes-sym)

      side : Cnt n ExhaustT Q → AgreeTo Q ExhaustT (ES.Exhaust.ExhaustT f′ o′)
      side c = ⟨ (λ {y} yq → exhaust-to ao L y yq , exhaust-to (AgreeTo-sym ao) (lanes-sym ao L) y yq) ⟩
        where
          img-o : ∀ {y e} → o y e → y ≺ Q → ¬ ¬ Img ExhaustT Q y
          img-o {e = out _} x yQ = seen-under (val x) yQ
          img-o {e = skip}  x yQ = seen (step x) yQ
          img-o {e = end}   x yQ = em (λ d → seen (oend x d) yQ) (λ nd → seen (opass x nd) yQ)

          ao = outer c img-o

          img-l : ∀ {q a} (x : o q (out a)) → ES.Exhaust.Run f o q → ∀ {y e} → enter (f a) (q ++ [ ix 1 ]) y e → y ≺ Q → ¬ ¬ Img ExhaustT Q y
          img-l x r {e = out _} l yQ = seen (lane x r (l , past {a = _} (val-ok x) l) tt) yQ
          img-l x r {e = skip}  l yQ = seen (lane x r (l , past {a = _} (val-ok x) l) tt) yQ
          img-l x r {e = end}   l yQ = em (λ d → seen (lend x r (l , past {a = _} (val-ok x) l) d) yQ) (λ nd → seen (lpass x r (l , past {a = _} (val-ok x) l) nd) yQ)

          L = lanes λ x r _ → lane-ag (val-ok x) c (img-l x r)

    module KB (m : ℕ) (Q : Pos) where
      open ES.Values o using (Nth; first; next)
      open ES.Bounded m f o using (Kth; Starts; room; freed; queued; Ends; Sched; Sub; Queued; Done; BoundedT;
                                   val; step; oend; opass; lane; handoff; lend; lpass)
      open Join.BoundedJ {A} {B} Q m using (lanes; bounded-to; lanes-sym)

      nth-val : ∀ {i q a} → Nth i q a → o q (out a)
      nth-val (first x _)    = x
      nth-val (next _ x _ _) = x

      -- Every lane subscribes where the invariant holds: at a value, or past an earlier lane's end.
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
          I  = If a s₀ k₀

      sub-ok : ∀ {i q s₀ a} → Sub i q s₀ a → Ok H s₀
      sub-ok {i} (N , St) = starts-ok i N St

      side : Cnt n BoundedT Q → AgreeTo Q BoundedT (ES.Bounded.BoundedT m f′ o′)
      side c = ⟨ (λ {y} yq → bounded-to ao L y yq , bounded-to (AgreeTo-sym ao) (lanes-sym ao L) y yq) ⟩
        where
          img-o : ∀ {y e} → o y e → y ≺ Q → ¬ ¬ Img BoundedT Q y
          img-o {e = out _} x yQ = seen-under (val x) yQ
          img-o {e = skip}  x yQ = seen (step x) yQ
          img-o {e = end}   x yQ = em (λ d → seen (oend x d) yQ) (λ nd → seen (opass x nd) yQ)

          ao = outer c img-o

          img-l : ∀ {i q s₀ a} (sb : Sub i q s₀ a) → ∀ {y e} → enter (f a) s₀ y e → y ≺ Q → ¬ ¬ Img BoundedT Q y
          img-l sb {e = out _} l yQ = seen (lane sb (l , past (sub-ok sb) l) tt) yQ
          img-l sb {e = skip}  l yQ = seen (lane sb (l , past (sub-ok sb) l) tt) yQ
          img-l sb {e = end}   l yQ =
            em (λ qd → seen-under (handoff sb ly qd) yQ)
               (λ nq → em (λ d → seen (lend sb ly nq d) yQ) (λ nd → seen (lpass sb ly nq nd) yQ))
            where ly = l , past (sub-ok sb) l

          L = lanes λ sb _ → lane-ag (sub-ok sb) c (img-l sb)

-- EACH JOINER KEEPS THE ORDER MODULUS at admissible subscriptions: what
-- is few before a cut in one side's joiner is few in what it reads there.
flatMap-ne : ∀ {A B H k} (op : FlatOp) {f f′ : A → Den B} {s s′ : Den A}
           → InvD H s → InvD H s′ → (∀ a → InvD H (f a)) → (∀ a → InvD H (f′ a))
           → s ≈ᶜ⟨ Ok H ∣ k ⟩ s′ → (∀ a → f a ≈ᶜ⟨ Ok H ∣ k ⟩ f′ a) → flatMapᵀ op f s ≈ᶜ⟨ Ok H ∣ k ⟩ flatMapᵀ op f′ s′
flatMap-ne {H = H} {k} (mergeᶠ nothing) {f} {f′} {s} {s′} Is Is′ If If′ as af p ok = trunc-ag λ
  { Q (inj₁ c) → Keep.KM.side {H = H} {k} {f = f} {f′} {s} {s′} Is If as af p ok Q c
  ; Q (inj₂ c) → AgreeTo-sym (Keep.KM.side {H = H} {k} {f = f′} {f} {s′} {s} Is′ If′ (≈ᶜ-sym {d = s} {s′} as) (λ a → ≈ᶜ-sym {d = f a} {f′ a} (af a)) p ok Q c) }
flatMap-ne {H = H} {k} (mergeᶠ (just m)) {f} {f′} {s} {s′} Is Is′ If If′ as af p ok = trunc-ag λ
  { Q (inj₁ c) → Keep.KB.side {H = H} {k} {f = f} {f′} {s} {s′} Is If as af p ok m Q c
  ; Q (inj₂ c) → AgreeTo-sym (Keep.KB.side {H = H} {k} {f = f′} {f} {s′} {s} Is′ If′ (≈ᶜ-sym {d = s} {s′} as) (λ a → ≈ᶜ-sym {d = f a} {f′ a} (af a)) p ok m Q c) }
flatMap-ne {H = H} {k} switchᶠ {f} {f′} {s} {s′} Is Is′ If If′ as af p ok = trunc-ag λ
  { Q (inj₁ c) → Keep.KS.side {H = H} {k} {f = f} {f′} {s} {s′} Is If as af p ok Q c
  ; Q (inj₂ c) → AgreeTo-sym (Keep.KS.side {H = H} {k} {f = f′} {f} {s′} {s} Is′ If′ (≈ᶜ-sym {d = s} {s′} as) (λ a → ≈ᶜ-sym {d = f a} {f′ a} (af a)) p ok Q c) }
flatMap-ne {H = H} {k} exhaustᶠ {f} {f′} {s} {s′} Is Is′ If If′ as af p ok = trunc-ag λ
  { Q (inj₁ c) → Keep.KE.side {H = H} {k} {f = f} {f′} {s} {s′} Is If as af p ok Q c
  ; Q (inj₂ c) → AgreeTo-sym (Keep.KE.side {H = H} {k} {f = f′} {f} {s′} {s} Is′ If′ (≈ᶜ-sym {d = s} {s′} as) (λ a → ≈ᶜ-sym {d = f a} {f′ a} (af a)) p ok Q c) }
