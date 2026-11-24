{-# OPTIONS --guardedness #-}

-- A VALUE WAITING AT A LANE'S END: its lane begun before the end, or a
-- lane queued there.  The lanes before the first one not begun by the
-- end are counted (`Census`): the dead among them leave exactly the
-- slots, so the queue's head starts one step below the end (`head-at`).
-- Which lanes are begun, and which ended, is not decidable, so the count
-- is taken classically.
module adequacy.QueuedAt where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_]; length)
open import Data.List.Properties using (length-++)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _<_; z≤n; s≤s; _≟_)
open import Data.Nat.Properties using (+-comm; +-identityʳ; ≤-pred; <-cmp; m≤n⇒m<n∨m≡n; n<1+n; m<n⇒m<1+n; ≤-trans; <⇒≤; m+n≤o⇒m≤o∸n;
  m∸n+n≡m; m+n∸n≡m; m≤n+m; <⇒≱; ≤-refl; ∸-monoˡ-≤; +-∸-assoc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable.Core using (¬¬-excluded-middle)

open import denotation.Position using (Pos; ix; sub; last; _⊕_; _≟ᵖ_)
open import denotation.EmissionSet using (EmissionSet; Den; out; end; enter; Few; After; _≺_; _≼_; module Bounded; module Values)
open import denotation.Laws.Modulus using (≼-or-≻; ≺-irrefl; ≺-trans; ≼-refl; ≼-≺-≺; ≺-ext; ≺-absurd; ≺→≼; few-ind)
open import denotation.Laws.Worlds using (Ok; InvAt; InvD; W⁼; plain-ix; step; here; inW; nest; nest⁼; ⊑-refl; ⊑-snoc; ⊑-≼; _⊑_; world-after; world-after⁼;
                                          w-up; leads; flat-under; conv; PinBy; ⊕-assoc; ⊕-identityʳ; ⊕-injʳ)
open import denotation.Laws.JoinInv using (ix01; ix10)
open import denotation.Events using (<ᵖ-between; <ᵖ-part)
open import Data.Bool.Properties using (T-≡)
open import Function using (Equivalence)
open import denotation.Laws.Worlds.Leaves using (out-inj)
open import denotation.Laws.Fold using (latest)
open import denotation.Laws.Nth using (module Nths)
open import denotation.Laws.BoundedInv using (module BoundedI)
open import adequacy.Cursor using (bef) renaming (Nths to Listed)
open import adequacy.Census using (module Count)

------------------------------------------------------------------------
-- A value with few rows before it has an index.

module _ {A : Set} (t : EmissionSet A) where
  open Values t using (Nth; first; next)

  few-nth : ∀ {w} → Few t w → ∀ {a} → t w (out a) → ¬ ¬ Σ ℕ λ i → Nth i w a
  few-nth = few-ind (λ w → ∀ {a} → t w (out a) → ¬ ¬ Σ ℕ λ i → Nth i w a) by-latest
    where
      Val : Pos → Set
      Val k = Σ A λ a → t k (out a)
      by-latest : ∀ {w} → Few t w → (∀ {v e} → t v e → v ≺ w → ∀ {a} → t v (out a) → ¬ ¬ Σ ℕ λ i → Nth i v a)
           → ∀ {a} → t w (out a) → ¬ ¬ Σ ℕ λ i → Nth i w a
      by-latest {w} (ks , h) ih x ¬N = latest Val w ks λ
        { (inj₁ none) → ¬N (0 , first x λ y kw → none (h y kw) (_ , y) kw)
        ; (inj₂ (v , (_ , xv) , vw , mx)) → ih xv vw xv λ
            { (i , nv) → ¬N (suc i , next nv x vw λ y vk kw → mx (h y kw) (_ , y) kw vk) } }

module QueuedAt {A B H at} (ok : Ok H at) (m : ℕ) (F : A → Den B) (fi : ∀ a → InvD H (F a)) {O : EmissionSet A} (Io : InvAt H at O) where
  open Bounded m F O
  open Values O using (Nth; first; next)
  open Count ok m F fi Io using (Census; c-nil; c-dead; c-on; cen-lo; cen-hi; head-at; nths-snoc; ends-at; ends-fun; kth-le)
  open BoundedI ok m F fi Io using (kth-cons; kth-down; kth-mono; kth-lane; ending; at-c; strip; split≼; seat*; seat′; row-w; end-w; LI; sub-fun;
                                    lane-end; rel; apart; queued-in; apart-ww; apart-lead)
  open Nths O using (nth-val; nth-fun; nth-lt)

  -- Lane i subscribed before `c₀`.
  Early : Pos → ℕ → Set
  Early c₀ i = Σ Pos λ q → Σ A λ a → Σ Pos λ s → Sub i q s a × s ≺ c₀

  ------------------------------------------------------------------------
  -- A LANE'S END LIES PAST THE SECOND CHILD OF A VALUE, OR OF ANOTHER
  -- LANE'S END, BEFORE IT: nothing of a lane sits under such a first
  -- child, and no lane ends where a lane is subscribed.

  private
    -- Past the subscription and at or before a row under it: under it.
    under-c₀ : ∀ s y c₀ → s ⊑ y → s ≺ c₀ → c₀ ≼ y → s ⊑ c₀
    under-c₀ s y c₀ sy sc le =
      [ (λ c₀y → conv {s} {s} {c₀} {y} (⊑-refl s) (≺→≼ {s} {c₀} sc) c₀y sy) , (λ eq → subst (s ⊑_) (sym eq) sy) ]′ (split≼ {c₀} {y} le)

    -- Past `r` and not past its second child: at it, or under its first.
    split-kid : ∀ r {c} → r ≺ c → (r ⊕ [ ix 1 ]) ≺ c ⊎ (c ≡ r ⊕ [ ix 1 ] ⊎ (r ⊕ [ ix 0 ]) ⊑ c)
    split-kid r {c} rc with ≼-or-≻ c (r ⊕ [ ix 1 ])
    ... | inj₂ lt = inj₁ lt
    ... | inj₁ le with split≼ {c} {r ⊕ [ ix 1 ]} le
    ...   | inj₂ eq = inj₂ (inj₁ eq)
    ...   | inj₁ lt with <ᵖ-between r c [ ix 1 ] (Equivalence.to T-≡ rc) (Equivalence.to T-≡ lt)
    ...     | [] , refl = ⊥-elim (≺-irrefl {r} (subst (r ≺_) (⊕-identityʳ r) rc))
    ...     | ix zero ∷ ws , refl = inj₂ (inj₂ (ws , sym (⊕-assoc r [ ix 0 ] ws)))
    ...     | ix (suc zero) ∷ ws , refl = ⊥-elim (⊑-≼ {r ⊕ [ ix 1 ]} {r ⊕ (ix 1 ∷ ws)} (ws , sym (⊕-assoc r [ ix 1 ] ws)) lt)
    ...     | ix (suc (suc _)) ∷ ws , refl = ⊥-elim (≺-absurd {r ⊕ (ix (suc (suc _)) ∷ ws)} {r ⊕ [ ix 1 ]} lt (Equivalence.from T-≡ (<ᵖ-part r [] ws refl)))
    ...     | sub _ ∷ ws , refl = ⊥-elim (≺-absurd {r ⊕ (sub _ ∷ ws)} {r ⊕ [ ix 1 ]} lt (Equivalence.from T-≡ (<ᵖ-part r [] ws refl)))
    ...     | last ∷ ws , refl = ⊥-elim (≺-absurd {r ⊕ (last ∷ ws)} {r ⊕ [ ix 1 ]} lt (Equivalence.from T-≡ (<ᵖ-part r [] ws refl)))

    -- A value's children: its lane's root, apart from every other lane;
    -- its first child in no lane's world.
    end-val : ∀ {j q a s c r b} → Sub j q s a → After (F a) s c end → O r (out b)
            → c ≡ r ⊕ [ ix 1 ] ⊎ (r ⊕ [ ix 0 ]) ⊑ c → ⊥
    end-val {s = s} {c} {r} sb af xr k with seat* sb
    ... | seat′ {r = r₀} _ rs _ nr rw = [ at-kid , led ]′ k
      where
        xr₀ = nth-val nr
        at-kid : c ≡ r ⊕ [ ix 1 ] → ⊥
        at-kid eq with r ≟ᵖ r₀
        ... | yes refl = world-after⁼ (subst (λ z → W⁼ H z s) (sym eq) rw) rs (proj₂ af)
        ... | no ne    = apart-ww xr₀ xr (λ e → ne (sym e)) (nest⁼ rw (inW (row-w sb af))) (subst (W⁼ H (r ⊕ [ ix 1 ])) (sym eq) here)
        led : (r ⊕ [ ix 0 ]) ⊑ c → ⊥
        led = leads (proj₂ ok) (step (inW (InvAt.world Io xr)) plain-ix)
                (λ v → [ (λ eq → ix10 (⊕-injʳ r₀ r eq)) , (λ v′ → InvAt.under Io xr₀ xr plain-ix v′ (⊑-refl r)) ]′ (w-up plain-ix v))
                (λ le → [ flat-under Io xr xr₀ , (λ eq → ix01 (⊕-injʳ r r₀ eq)) ]′ (⊑-snoc r₀ le))
                (nest⁼ rw (inW (row-w sb af)))

    -- Two lanes' ends: apart, or one queued past the other.
    end-ends : ∀ {j q a s c j′ q′ a′ s′ r} → Sub j q s a → After (F a) s c end → Sub j′ q′ s′ a′ → After (F a′) s′ r end
             → r ≺ c → c ≡ r ⊕ [ ix 1 ] ⊎ (r ⊕ [ ix 0 ]) ⊑ c → (r ⊕ [ ix 1 ]) ≺ c
    end-ends {j} {j′ = j′} sb af sb′ af′ rc k with <-cmp j j′
    end-ends {r = r} sb af sb′ af′ rc k | tri≈ _ refl _ with sub-fun sb sb′
    ... | refl , refl , refl = ⊥-elim (≺-irrefl {r} (subst (r ≺_) (lane-end sb af af′) rc))
    end-ends {c = c} {r = r} sb af sb′ af′ rc k | tri< lt _ _ with rel lt sb sb′
    ... | apart xr xr′ ne rw rw′ =
      ⊥-elim ([ (λ eq → apart-ww xr xr′ ne (nest⁼ rw (inW (row-w sb af))) (subst (W⁼ H _) (sym eq) (nest⁼ rw′ (inW (end-w sb′ af′)))))
              , (λ le → apart-lead xr′ xr (λ e → ne (sym e)) (nest⁼ rw′ (inW (step (inW (row-w sb′ af′)) plain-ix))) (nest rw (row-w sb af)) le) ]′ k)
    ... | queued-in e _ v =
      ⊥-elim (≺-irrefl {r} (≺-trans {r} {c} {r} rc (≺-trans {c} {c ⊕ [ ix 1 ]} {r} (≺-ext c [])
        (world-after (nest (subst (λ z → W⁼ H (z ⊕ [ ix 1 ]) _) (lane-end sb e af) v) (row-w sb′ af′)) (InvAt.real (LI sb′) (proj₁ af′))))))
    end-ends {c = c} {r = r} sb af sb′ af′ rc k | tri> _ _ gt with rel gt sb′ sb
    ... | apart xr′ xr ne rw′ rw =
      ⊥-elim ([ (λ eq → apart-ww xr′ xr ne (subst (W⁼ H _) (sym eq) (nest⁼ rw′ (inW (end-w sb′ af′)))) (nest⁼ rw (inW (row-w sb af))))
              , (λ le → apart-lead xr′ xr ne (nest⁼ rw′ (inW (step (inW (row-w sb′ af′)) plain-ix))) (nest rw (row-w sb af)) le) ]′ k)
    ... | queued-in e _ v = world-after (nest (subst (λ z → W⁼ H (z ⊕ [ ix 1 ]) _) (lane-end sb′ e af′) v) (row-w sb af)) (InvAt.real (LI sb) (proj₁ af))

  end-past : ∀ {j q a s c r} → Sub j q s a → After (F a) s c end
           → (Σ A λ b → O r (out b)) ⊎ (Σ ℕ λ j′ → Ends j′ (Sched j′) r)
           → r ≺ c → (r ⊕ [ ix 1 ]) ≺ c
  end-past {c = c} {r} sb af rt rc with split-kid r {c} rc
  ... | inj₁ lt = lt
  ... | inj₂ k with rt
  ...   | inj₁ (_ , xr) = ⊥-elim (end-val {c = c} {r} sb af xr k)
  ...   | inj₂ (_ , (_ , _ , _ , nj′ , st′ , af′)) = end-ends {c = c} {r = r} sb af (nj′ , st′) af′ rc k

  private
    no-pin : ∀ {c} {b : B} → PinBy c (out b) → ⊥
    no-pin (_ , () , _)

    no-eo : ∀ {b : B} → end ≡ out b → ⊥
    no-eo ()

    -- A lane's value lies before its end.
    own-before : ∀ {i q a s y b c} → Sub i q s a → enter (F a) s y (out b) → enter (F a) s c end → y ≺ c
    own-before {a = a} {s} {y} {c = c} sb ry rc with ≼-or-≻ c y
    ... | inj₂ lt = lt
    ... | inj₁ le = ⊥-elim ([ (λ lt → no-pin (InvAt.quiet (LI sb) rc ry lt))
                            , (λ eq → no-eo (InvAt.func (LI sb) rc (subst (λ z → enter (F a) s z _) (sym eq) ry))) ]′ (split≼ {c} {y} le))

  -- A LANE'S VALUE UNDER ITS SUBSCRIPTION LIES BEFORE A LANE'S END PAST
  -- THAT SUBSCRIPTION: the end is the same lane's, or another's apart, or
  -- queued past the first lane's end.
  row-before : ∀ {i q a s y b j₀ q₀ a₀ s₀ c₀} → Sub i q s a → enter (F a) s y (out b) → s ⊑ y
             → Sub j₀ q₀ s₀ a₀ → After (F a₀) s₀ c₀ end → s ≺ c₀ → y ≺ c₀
  row-before {i} {s = s} {y} {j₀ = j₀} {c₀ = c₀} sb ry sy sb₀ af₀ sc with ≼-or-≻ c₀ y
  ... | inj₂ lt = lt
  ... | inj₁ le with <-cmp i j₀
  ...   | tri≈ _ refl _ with sub-fun sb sb₀
  ...     | refl , refl , refl = own-before sb ry (proj₁ af₀)
  row-before {i} {s = s} {y} {j₀ = j₀} {c₀ = c₀} sb ry sy sb₀ af₀ sc | inj₁ le | tri< lt _ _ with rel lt sb sb₀
  ... | apart xr xr₀ ne rw rw₀ = ⊥-elim (apart-lead xr xr₀ ne rw (nest rw₀ (row-w sb₀ af₀)) (under-c₀ s y c₀ sy sc le))
  ... | queued-in {c} e _ v =
    ≺-trans {y} {c} {c₀} (own-before sb ry (proj₁ e))
      (≺-trans {c} {c ⊕ [ ix 1 ]} {c₀} (≺-ext c []) (world-after (nest v (row-w sb₀ af₀)) (InvAt.real (LI sb₀) (proj₁ af₀))))
  row-before {i} {s = s} {y} {j₀ = j₀} {c₀ = c₀} sb ry sy sb₀ af₀ sc | inj₁ le | tri> _ _ gt with rel gt sb₀ sb
  ... | apart xr₀ xr ne rw₀ rw = ⊥-elim (apart-lead xr xr₀ (λ e → ne (sym e)) rw (nest rw₀ (row-w sb₀ af₀)) (under-c₀ s y c₀ sy sc le))
  ... | queued-in e _ v with seat* sb
  ...   | seat′ _ rs _ _ _ =
    ⊥-elim (world-after⁼ (subst (λ z → W⁼ H (z ⊕ [ ix 1 ]) s) (lane-end sb₀ e af₀) v) rs (≺-trans {s} {c₀} {c₀ ⊕ [ ix 1 ]} sc (≺-ext c₀ [])))

  ------------------------------------------------------------------------
  -- The values and lanes, by index

  private
    val-fun : ∀ {i q q′ a a′} → Nth i q a → Nth i q′ a′ → q ≡ q′ × a ≡ a′
    val-fun n n′ with nth-fun n n′
    ... | refl = refl , out-inj (InvAt.func Io (nth-val n) (nth-val n′))

    nth-down : ∀ {i j q a} → j ≤ i → Nth i q a → Σ Pos λ q′ → Σ A λ a′ → Nth j q′ a′
    nth-down le n with m≤n⇒m<n∨m≡n le
    nth-down le n | inj₂ refl = _ , _ , n
    nth-down le (first _ _) | inj₁ ()
    nth-down le (next N _ _ _) | inj₁ lt = nth-down (≤-pred lt) N

    -- The value at a later index lies later.
    nth-le : ∀ {i j q q′ a a′} → j ≤ i → Nth j q′ a′ → Nth i q a → q′ ≼ q
    nth-le {q = q} {q′} le nj ni with m≤n⇒m<n∨m≡n le
    ... | inj₁ lt   = λ qq → ≺-irrefl {q} (≺-trans {q} {q′} {q} qq (nth-lt lt nj ni))
    ... | inj₂ refl with nth-fun nj ni
    ...   | refl = ≼-refl {q}

    -- A value listed between its first and last index is listed.
    in-ls : ∀ {i j q a} xs → Listed O i xs → i ≤ j → j < i + length xs → Nth j q a → (q , a) ∈ xs
    in-ls {i} {j} [] _ le lt _ = ⊥-elim (<⇒≱ lt (subst (_≤ j) (sym (+-identityʳ i)) le))
    in-ls {i} {j} ((q′ , a′) ∷ xs) (nx , ns) le lt nj with m≤n⇒m<n∨m≡n le
    ... | inj₂ refl with val-fun nx nj
    ...   | refl , refl = here refl
    in-ls {i} {j} ((q′ , a′) ∷ xs) (nx , ns) le lt nj | inj₁ i<j =
      there (in-ls xs ns i<j (subst (j <_) (+-suc′ i (length xs)) lt) nj)
      where
        +-suc′ : ∀ a b → a + suc b ≡ suc a + b
        +-suc′ zero    b = refl
        +-suc′ (suc a) b = cong suc (+-suc′ a b)

    lt-or-ge : ∀ x y → x < y ⊎ y ≤ x
    lt-or-ge x y with <-cmp x y
    ... | tri< lt _ _   = inj₁ lt
    ... | tri≈ _ refl _ = inj₂ ≤-refl
    ... | tri> _ _ gt   = inj₂ (<⇒≤ gt)

    -- Where a lane starts lies past its value.
    q-before : ∀ {i q ls s} → Starts i q ls s → q ≺ s
    q-before {q = q} (room _)          = ≺-ext q []
    q-before {q = q} (freed _ _)       = ≺-ext q []
    q-before {q = q} (queued {c} _ qc _ _ _) = ≺-trans {q} {c} {c ⊕ [ ix 1 ]} qc (≺-ext c [])

  -- Lane i begun by `c₀` is its value's.
  early-at : ∀ {c₀ i q a} → Early c₀ i → Nth i q a → Σ Pos λ s → Sub i q s a × s ≺ c₀
  early-at (_ , _ , s , (nq , st) , sc) n with val-fun nq n
  ... | refl , refl = s , (nq , st) , sc

  ------------------------------------------------------------------------
  -- The k-th end in order, below a bound.

  pick : ∀ i {k b} → Kth (_≺ b) (Sched i) k → ¬ ¬ Σ Pos λ c → c ≺ b × Kth (_≼ c) (Sched i) k × ¬ Kth (_≺ c) (Sched i) k
  pick zero ()
  pick (suc i) {k} {b} K κ = ¬¬-excluded-middle {A = Σ Pos λ e → Ends i (Sched i) e × e ≺ b} λ
    { (no ¬X) → pick i (tl ¬X K) λ (c , cb , Kl , nK) →
        κ (c , cb , kth-cons Kl , λ K′ → nK (tl (λ (e , ee , ec) → ¬X (e , ee , ≺-trans {e} {c} {b} ec cb)) K′))
    ; (yes (e , ee , eb)) → with-e k K κ e ee eb }
    where
      -- Without lane i below `b`, the count is the earlier lanes'.
      tl : ∀ {k b′} → ¬ (Σ Pos λ e → Ends i (Sched i) e × e ≺ b′) → Kth (_≺ b′) (Sched (suc i)) k → Kth (_≺ b′) (Sched i) k
      tl {zero}  ¬X (inj₁ (e , ee , eb))       = ⊥-elim (¬X (e , ee , eb))
      tl {zero}  ¬X (inj₂ K′)                  = K′
      tl {suc k} ¬X (inj₁ ((e , ee , eb) , _)) = ⊥-elim (¬X (e , ee , eb))
      tl {suc k} ¬X (inj₂ K′)                  = K′
      own : ∀ {e e′} → Ends i (Sched i) e → Ends i (Sched i) e′ → e′ ≺ e → ⊥
      own {e} ee ee′ lt with ends-fun ee ee′
      ... | refl = ≺-irrefl {e} lt
      with-e : ∀ k → Kth (_≺ b) (Sched (suc i)) k → ¬ (Σ Pos λ c → c ≺ b × Kth (_≼ c) (Sched (suc i)) k × ¬ Kth (_≺ c) (Sched (suc i)) k)
             → ∀ e → Ends i (Sched i) e → e ≺ b → ⊥
      with-e zero _ κ e ee eb = ¬¬-excluded-middle {A = Kth (_≺ e) (Sched i) 0} λ
        { (no nKe) → κ (e , eb , inj₁ (e , ee , ≼-refl {e}) , λ { (inj₁ (e′ , ee′ , lt)) → own ee ee′ lt ; (inj₂ K′) → nKe K′ })
        ; (yes Ke) → pick i Ke λ (c , ce , Kl , nK) →
            κ (c , ≺-trans {c} {e} {b} ce eb , inj₂ Kl , λ { (inj₁ (e′ , ee′ , lt)) → own ee ee′ (≺-trans {e′} {c} {e} lt ce) ; (inj₂ K′) → nK K′ }) }
      with-e (suc k) K κ e ee eb = pick i (down K) λ (c′ , c′b , Kl′ , nK′) → [ (λ ec′ → κ (c′ , c′b , inj₁ ((e , ee , ec′) , Kl′) , λ { (inj₁ (_ , K′)) → nK′ K′ ; (inj₂ K′) → nK′ (kth-down (Sched i) K′) }))
                                                                            , (λ c′e → past c′ c′e Kl′) ]′ (≼-or-≻ e c′)
        where
          down : Kth (_≺ b) (Sched (suc i)) (suc k) → Kth (_≺ b) (Sched i) k
          down (inj₁ (_ , K′)) = K′
          down (inj₂ K′)       = kth-down (Sched i) K′
          past : ∀ c′ → c′ ≺ e → Kth (_≼ c′) (Sched i) k → ⊥
          past c′ c′e Kl′ = ¬¬-excluded-middle {A = Kth (_≺ e) (Sched i) (suc k)} λ
            { (no nKe) → κ (e , eb , inj₁ ((e , ee , ≼-refl {e}) , kth-mono (λ {x} xc′ → ≼-≺-≺′ {x} xc′ c′e) (Sched i) Kl′)
                            , λ { (inj₁ ((e′ , ee′ , lt) , _)) → own ee ee′ lt ; (inj₂ K′) → nKe K′ })
            ; (yes Ke) → pick i Ke λ (c , ce , Kl , nK) →
                κ (c , ≺-trans {c} {e} {b} ce eb , inj₂ Kl , λ { (inj₁ ((e′ , ee′ , lt) , _)) → own ee ee′ (≺-trans {e′} {c} {e} lt ce) ; (inj₂ K′) → nK K′ }) }
            where
              ≼-≺-≺′ : ∀ {x} → x ≼ c′ → c′ ≺ e → x ≼ e
              ≼-≺-≺′ {x} xc′ ce′ ex = xc′ (≺-trans {c′} {e} {x} ce′ ex)

  ------------------------------------------------------------------------
  -- Lane h started before a lane's end, given the room or the ends.

  module _ {j₀ q₀ a₀ s₀ c₀} (sb₀ : Sub j₀ q₀ s₀ a₀) (af₀ : After (F a₀) s₀ c₀ end) where

    -- No lane ends where a value is.
    private
      no-at : ∀ {j c q a} → Ends j (Sched j) c → O q (out a) → c ≡ q → ⊥
      no-at {c = c} (_ , _ , _ , nj , stj , afj) xq refl with seat* (nj , stj)
      ... | seat′ _ _ _ nr rw = InvAt.under Io (nth-val nr) xq plain-ix (nest⁼ rw (inW (row-w (nj , stj) afj))) (⊑-refl c)

    start-by : ∀ {h q a} → Nth h q a → q ≺ c₀ → h < m ⊎ (m ≤ h × Kth (_≺ c₀) (Sched h) (h ∸ m)) → ¬ ¬ Early c₀ h
    start-by {q = q} {a} nq qc (inj₁ lt) κ = κ (q , a , _ , (nq , room lt) , end-past sb₀ af₀ (inj₁ (a , nth-val nq)) qc)
    start-by {h} {q} {a} nq qc (inj₂ (le , K)) κ = ¬¬-excluded-middle {A = Kth (_≺ q) (Sched h) (h ∸ m)} λ
      { (yes Kq) → κ (q , a , _ , (nq , freed le Kq) , end-past sb₀ af₀ (inj₁ (a , nth-val nq)) qc)
      ; (no nKq) → pick h K λ (c , cc₀ , Kl , nKl) →
          let K0 = at-c (Sched h) (h ∸ m) Kl nKl in
          [ (λ cq → [ (λ c<q → nKq (kth-mono (λ {x} xc → ≼-≺-≺ {x} {c} {q} xc c<q) (Sched h) Kl))
                    , (λ c≡q → end-at K0 (λ e → no-at e (nth-val nq) c≡q)) ]′ (split≼ {c} {q} cq))
          , (λ q<c → end-at K0 λ e → κ (q , a , _ , (nq , queued le q<c K0 Kl nKl) , end-past sb₀ af₀ (inj₂ (_ , e)) cc₀)) ]′
          (≼-or-≻ c q) }
      where
        end-at : ∀ {c} → Kth (_≡ c) (Sched h) 0 → (∀ {j} → Ends j (Sched j) c → ⊥) → ⊥
        end-at K0 k with kth-lane h K0
        ... | ending _ e refl = k e

    -- A lane begun before the end, its slot taken: as many ends before.
    ends-by : ∀ {j q s} → m ≤ j → Starts j q (Sched j) s → s ≺ c₀ → Kth (_≺ c₀) (Sched j) (j ∸ m)
    ends-by m≤j (room lt) _ = ⊥-elim (<⇒≱ lt m≤j)
    ends-by {q = q} m≤j (freed _ K) sc = kth-mono (λ {x} xq → ≺-trans {x} {q} {c₀} xq (≺-trans {q} {q ⊕ [ ix 1 ]} {c₀} (≺-ext q []) sc)) _ K
    ends-by m≤j (queued {c} _ _ _ K _) sc = kth-mono (λ {x} xc → ≼-≺-≺ {x} {c} {c₀} xc (≺-trans {c} {c ⊕ [ ix 1 ]} {c₀} (≺-ext c []) sc)) _ K

    -- LANES START IN ORDER: a lane before one begun by the end is.
    begun-down : ∀ {h j} → h < j → Early c₀ j → ¬ ¬ Early c₀ h
    begun-down {h} {j} h<j (qj , aj , sj , (nj , stj) , sc) κ =
      let (qh , ah , nh) = nth-down (<⇒≤ h<j) nj
          qhc = ≺-trans {qh} {qj} {c₀} (nth-lt h<j nh nj) (≺-trans {qj} {sj} {c₀} (q-before stj) sc)
      in [ (λ h<m → start-by nh qhc (inj₁ h<m) κ)
         , (λ m≤h → start-by nh qhc (inj₂ (m≤h , shrink m≤h (ends-by (≤-trans m≤h (<⇒≤ h<j)) stj sc))) κ) ]′ (lt-or-ge h m)
      where
        shrink : ∀ {Q} → m ≤ h → Kth Q (Sched j) (j ∸ m) → Kth Q (Sched h) (h ∸ m)
        shrink {Q} m≤h K = strip (j ∸ h) h m≤h (subst (λ x → Kth Q (Sched x) (x ∸ m)) (sym (m∸n+n≡m (<⇒≤ h<j))) K)

  ------------------------------------------------------------------------
  -- The census before a lane's end.

  private
    -- The lanes before the first not begun.
    least : ∀ c₀ n → ¬ ¬ ((∀ {j} → j < n → Early c₀ j) ⊎ Σ ℕ λ h → h < n × ¬ Early c₀ h × (∀ {j} → j < h → Early c₀ j))
    least c₀ zero κ = κ (inj₁ λ ())
    least c₀ (suc n) κ = least c₀ n λ
      { (inj₂ (h , h<n , nh , bl)) → κ (inj₂ (h , m<n⇒m<1+n h<n , nh , bl))
      ; (inj₁ all) → ¬¬-excluded-middle {A = Early c₀ n} λ
          { (yes e) → κ (inj₁ λ {j} j<1+n → [ all , (λ { refl → e }) ]′ (m≤n⇒m<n∨m≡n (≤-pred j<1+n)))
          ; (no ne) → κ (inj₂ (n , n<1+n n , ne , all)) } }

    -- Their values, in order.
    listing : ∀ c₀ h → (∀ {j} → j < h → Early c₀ j) → Σ (List (Pos × A)) λ vs → Listed O 0 vs × length vs ≡ h
    listing c₀ zero _ = [] , _ , refl
    listing c₀ (suc h) bl =
      let (vs , Lv , eq) = listing c₀ h (λ lt → bl (m<n⇒m<1+n lt))
          (q , a , _ , (nq , _) , _) = bl (n<1+n h)
      in vs ++ [ (q , a) ] , nths-snoc vs Lv (subst (λ k → Nth k q a) (sym eq) nq)
       , trans (length-++ vs) (trans (+-comm (length vs) 1) (cong suc eq))

    -- Each lane dead, its end before `c₀`; or on, its end at or past it.
    census : ∀ c₀ vs N → (∀ {j q a} → j < N → Nth j q a → (q , a) ∈ vs) → ¬ ¬ Σ ℕ λ d → Census (bef c₀) vs N d
    census c₀ vs zero _ κ = κ (0 , c-nil)
    census c₀ vs (suc N) inv κ = census c₀ vs N (λ lt → inv (m<n⇒m<1+n lt)) λ (d , cs) →
      ¬¬-excluded-middle {A = Σ Pos λ c → Ends N (Sched N) c × c ≺ c₀} λ
        { (yes (c , e , cc)) → κ (suc d , c-dead cs e (λ o → o cc))
        ; (no ne) → κ (d , c-on cs λ {c} e@(q , a , s , nq , st , af) →
            c , (q , a , inv (n<1+n N) nq , ends-at nq e , (λ ()) , (λ cc → ne (c , e , cc))) , ≼-refl {c}) }

  ------------------------------------------------------------------------
  -- A VALUE BEFORE A LANE'S END IS BEGUN BY IT, OR A LANE IS QUEUED AT IT.

  queued-at : ∀ {q₀ a₀ c₀ iv qv av} → Lane q₀ a₀ c₀ end → Nth iv qv av → qv ≺ c₀ → ¬ ¬ (Early c₀ iv ⊎ Queued c₀)
  queued-at {q₀} {a₀} {c₀} {iv} {qv} {av} (j₀ , s₀ , sb₀ , af₀) nv qvc κ = least c₀ (suc iv) λ
    { (inj₁ all) → κ (inj₁ (all (n<1+n iv)))
    ; (inj₂ (h , h<iv , nh , bl)) → after h (≤-pred h<iv) nh bl }
    where
      e₀ : Early c₀ j₀
      e₀ = q₀ , a₀ , s₀ , sb₀ , proj₂ af₀

      -- Every lane before index `length vs` begun, that one not.
      fin : ∀ vs → Listed O 0 vs → ∀ {qh ah} → Nth (length vs) qh ah → qh ≺ c₀ → j₀ < length vs
          → ¬ Early c₀ (length vs) → (∀ {j} → j < length vs → Early c₀ j) → ⊥
      fin vs Lv {qh} {ah} nqh qhc j₀<h nh bl = census c₀ vs (length vs) (λ lt nj → in-ls vs Lv z≤n lt nj) λ (d , cs) →
        [ (λ full → κ (inj₂ (full-head d cs full))) , short d cs ]′ (count d)
        where
          count : ∀ d → d + m ≡ length vs ⊎ ¬ (d + m ≡ length vs)
          count d with d + m ≟ length vs
          ... | yes e = inj₁ e
          ... | no ne = inj₂ ne

          -- Every slot taken: the queue's head starts below the end.
          full-head : ∀ d → Census (bef c₀) vs (length vs) d → d + m ≡ length vs → Queued c₀
          full-head d cs full =
            let (i , sb) = head-at Lv cs full (λ o → o qhc) nqh {ws = []}
                             (q₀ , a₀ , in-ls vs Lv z≤n j₀<h (proj₁ sb₀) , (j₀ , s₀ , sb₀ , af₀) , (λ ()) , ≼-refl {c₀})
                             (λ (_ , _ , _ , _ , _ , o) → o)
            in i , qh , ah , sb

          -- More running than the slots: the latest lane began with the
          -- dead too few.  Fewer: lane `length vs` began by the end.
          short : ∀ d → Census (bef c₀) vs (length vs) d → ¬ (d + m ≡ length vs) → ⊥
          short d cs ne with <-cmp (d + m) (length vs)
          ... | tri≈ _ e _ = ne e
          ... | tri< dm<h _ _ = over (length vs) dm<h bl cs
            where
              over : ∀ h → d + m < h → (∀ {j} → j < h → Early c₀ j) → Census (bef c₀) vs h d → ⊥
              over zero () _ _
              over (suc h′) dm<h bl′ cs′ =
                let (q′ , a′ , s′ , (_ , st′) , sc′) = bl′ (n<1+n h′)
                    dm≤ = ≤-pred dm<h
                    m≤h′ = ≤-trans (m≤n+m m d) dm≤
                in cen-hi (λ {c′} {c} (_ , _ , _ , _ , _ , oc) le lt → oc (≼-≺-≺ {c′} {c} {c₀} le lt)) cs′
                     (kth-le (Sched (suc h′)) (m+n≤o⇒m≤o∸n d dm≤) (kth-cons (ends-by sb₀ af₀ m≤h′ st′ sc′)))
          ... | tri> _ _ h<dm = [ (λ h<m → start-by sb₀ af₀ nqh qhc (inj₁ h<m) nh)
                                , (λ m≤h → start-by sb₀ af₀ nqh qhc (inj₂ (m≤h , dead d cs (subst₂ _≤_ (+-∸-assoc 1 m≤h) (m+n∸n≡m d m) (∸-monoˡ-≤ m h<dm)))) nh) ]′
                                (lt-or-ge (length vs) m)
            where
              dead : ∀ d′ → Census (bef c₀) vs (length vs) d′ → suc (length vs ∸ m) ≤ d′ → Kth (_≺ c₀) (Sched (length vs)) (length vs ∸ m)
              dead zero _ ()
              dead (suc d′) cs′ (s≤s le) = kth-le (Sched (length vs)) le (cen-lo (λ {c} nc → [ (λ le′ → ⊥-elim (nc le′)) , (λ lt → lt) ]′ (≼-or-≻ c₀ c)) cs′)

      at-len : ∀ {h} vs → Listed O 0 vs → length vs ≡ h → ∀ {qh ah} → Nth h qh ah → qh ≺ c₀ → j₀ < h
         → ¬ Early c₀ h → (∀ {j} → j < h → Early c₀ j) → ⊥
      at-len vs Lv refl = fin vs Lv

      after : ∀ h → h ≤ iv → ¬ Early c₀ h → (∀ {j} → j < h → Early c₀ j) → ⊥
      after h h≤iv nh bl with <-cmp j₀ h
      ... | tri≈ _ refl _ = nh e₀
      ... | tri> _ _ h<j₀ = begun-down sb₀ af₀ h<j₀ e₀ nh
      ... | tri< j₀<h _ _ =
        let (vs , Lv , eq) = listing c₀ h bl
            (qh , ah , nqh) = nth-down h≤iv nv
        in at-len vs Lv eq nqh (≼-≺-≺ {qh} {qv} {c₀} (nth-le h≤iv nqh nv) qvc) j₀<h nh bl
