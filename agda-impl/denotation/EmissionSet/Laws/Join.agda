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
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Properties using (∷ʳ-injectiveˡ)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Nullary using (¬_)

open import Tree using (FlatOp; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.MonotonicList.Events using (Pos; ix; inside)
open import denotation.EmissionSet using (Ev; out; EmissionSet; _≺_; _≼_; Den; enter; After; flatMapᵀ)
import denotation.EmissionSet as ES
open import denotation.EmissionSet.Laws.Modulus
  using (≺-trans; ≺→≼; ≼-refl; ≼-trans; ≼-or-≻; ≺-≼-≺; ≼-≺-≺; ≺-ext; AgreeTo; ⟨_⟩; upto; AgreeTo-sym; _~⟨_⟩_; ~-cold)

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
