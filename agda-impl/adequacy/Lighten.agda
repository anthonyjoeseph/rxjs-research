{-# OPTIONS --guardedness #-}

-- STILL STEPS LIGHTEN: a still step weighed, both confs at the clock it
-- starts from, by the step's mode — a climb, a subscribe, a mark run.
module adequacy.Lighten where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (suc; _+_; _*_; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; +-mono-≤; +-monoˡ-≤; +-monoˡ-<)
open import Data.Nat.Tactic.RingSolver using (solve-∀)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

open import Tree using (cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.Events using (Pos; root; ix; last; <ᵖ-below; <ᵖ-part)
open import denotation.EmissionSet using (enter; ⟦_⟧; _≼_)
open import denotation.Read using (Meets)
open import operation.PureObservable using (PureObs; module Machine; module Driver; opening; due; Tape)
open import denotation.Events using (timelineAt)
open Machine using (Ctx; St; pend; ofS; coldS; joinS; Conf; ⟨_,_,_,_⟩; load; subscribing; absorbed; rising; closedUp)
open import operation.Key using (at; _<ᴷ_; at-<ᴷ; <ᴷ-trans; <ᴷ-irrefl; clash)
open import adequacy.Rows using (conv)
open import adequacy.Weight using (Clock; W; Wᶜ; anc; depth; syn; module Weigh)
open import adequacy.Path using (Path; Still)

-- A position's child keyed strictly after it.
below : ∀ q {l} → at q <ᴷ at (q ++ [ l ]) ≡ true
below q = trans (at-<ᴷ q _) (<ᵖ-below q [])

postulate
  -- A SUBSCRIBING RUN IS AT ITS SUBSCRIPTION: every conf a run reaches
  -- subscribing has a pending subscription in focus, owed where the run is.
  pend-focus : ∀ {R} (o : PureObs [] R) {rs Γ A} {c : Ctx R Γ A} {s q}
             → Path (load o) rs ⟨ c , s , subscribing , q ⟩ → Σ (PureObs Γ A) λ o′ → s ≡ pend o′ q

  -- A COLD OPENS AHEAD: a cold a run subscribes first comes due strictly
  -- after where it was subscribed.
  opening-ahead : ∀ {R} (o : PureObs [] R) {rs Γ A} {c : Ctx R Γ A} {x q κ}
                → Path (load o) rs ⟨ c , pend (cold x) q , subscribing , q ⟩
                → due (opening q (timelineAt x q)) ≡ just κ → at q <ᴷ κ ≡ true

  -- A DEFER'S GUARD IS MET: short of a row a reader meets next, a defer a
  -- run subscribes has its guard row, at or before the row met next.
  defer-guard : ∀ {R} (o : PureObs [] R) {rs Γ A} {c : Ctx R Γ A} {l q p e}
              → Path (load o) rs ⟨ c , pend (defer l) q , subscribing , q ⟩
              → Meets (enter (⟦ o ⟧ []ᴬ) root) (conv rs ++ [ (p , e) ])
              → Σ _ λ e′ → enter (⟦ o ⟧ []ᴬ) root (q ++ [ ix 0 ]) e′ × (q ++ [ ix 0 ]) ≼ p

  -- A STILL CLIMB LIGHTENS: a rise passing no listed row lowers the weight
  -- at its clock.
  lightens-rise : ∀ {R} (o : PureObs [] R) {rs Γ A} {c : Ctx R Γ A} {s ε q k′ p e}
                → Path (load o) rs ⟨ c , s , rising ε , q ⟩
                → Meets (enter (⟦ o ⟧ []ᴬ) root) (conv rs ++ [ (p , e) ])
                → ∀ ks → (∀ {q′ e′} → enter (⟦ o ⟧ []ᴬ) root q′ e′ → q′ ≼ p → q′ ∈ ks)
                → Still (ks ++ anc ks) k′ ⟨ c , s , rising ε , q ⟩
                → Wᶜ (ks ++ anc ks) p (at q) k′ < Wᶜ (ks ++ anc ks) p (at q) ⟨ c , s , rising ε , q ⟩

  -- A STILL MARK RUN LIGHTENS: the least mark run, passing no listed row,
  -- lowers the weight at its clock.
  lightens-run : ∀ {R} (o : PureObs [] R) {rs Γ A} {c : Ctx R Γ A} {s q k′ p e}
               → Path (load o) rs ⟨ c , s , absorbed , q ⟩
               → Meets (enter (⟦ o ⟧ []ᴬ) root) (conv rs ++ [ (p , e) ])
               → ∀ ks → (∀ {q′ e′} → enter (⟦ o ⟧ []ᴬ) root q′ e′ → q′ ≼ p → q′ ∈ ks)
               → Still (ks ++ anc ks) k′ ⟨ c , s , absorbed , q ⟩
               → Wᶜ (ks ++ anc ks) p (Clock ⟨ c , s , absorbed , q ⟩) k′ < W (ks ++ anc ks) p ⟨ c , s , absorbed , q ⟩

private
  conn-arith : ∀ w e x y → w ≤ e → suc ((((w + e) + 0) + 0 + e) + x + y) ≤ 1 + 3 * e + y + x
  conn-arith w e x y h =
    ≤-trans (s≤s (+-monoˡ-≤ y (+-monoˡ-≤ x (+-monoˡ-≤ e (+-monoˡ-≤ 0 (+-monoˡ-≤ 0 (+-monoˡ-≤ e h)))))))
            (≤-reflexive (eq e x y))
    where eq : ∀ e x y → suc ((((e + e) + 0) + 0 + e) + x + y) ≡ 1 + 3 * e + y + x
          eq = solve-∀

  take-arith : ∀ a b y → suc (a + (b + y)) ≤ 1 + a + b + y
  take-arith a b y = ≤-reflexive (eq a b y)
    where eq : ∀ a b y → suc (a + (b + y)) ≡ 1 + a + b + y
          eq = solve-∀

  flat-arith : ∀ b y → suc ((b + y) + 0) ≤ 1 + b + y
  flat-arith b y = ≤-reflexive (eq b y)
    where eq : ∀ b y → suc ((b + y) + 0) ≡ 1 + b + y
          eq = solve-∀


module Begun {R} (o : PureObs [] R) {rs p e} (m : Meets (enter (⟦ o ⟧ []ᴬ) root) (conv rs ++ [ (p , e) ]))
             (ks : List Pos) (cov : ∀ {q′ e′} → enter (⟦ o ⟧ []ᴬ) root q′ e′ → q′ ≼ p → q′ ∈ ks)
             {Γ A} (c : Ctx R Γ A) (q : Pos) where
  private
    L = ks ++ anc ks
    open Weigh L p (at q)
    D = depth c

    -- An of's marks, each strictly past where it was subscribed.
    ofW-ahead : ∀ {X : Set} i (xs : List X) → ofW D i q xs ≤ length xs * (2 + D) + (2 + D)
    ofW-ahead i []       = wt-ahead D (at (q ++ [ last ])) (below q)
    ofW-ahead i (_ ∷ xs) =
      ≤-trans (+-mono-≤ (wt-ahead D (at (q ++ [ ix i ])) (below q)) (ofW-ahead (suc i) xs)) (≤-reflexive (asc (2 + D) (length xs * (2 + D)) (2 + D)))
      where asc : ∀ a b c → a + (b + c) ≡ (a + b) + c
            asc = solve-∀

    of-lt : ∀ {X : Set} (xs : List X) → ofW D 0 q xs < 3 + D + length xs * (2 + D)
    of-lt xs = ≤-trans (s≤s (ofW-ahead 0 xs)) (≤-reflexive (eq (length xs * (2 + D)) D))
      where eq : ∀ n d → suc (n + (2 + d)) ≡ 3 + d + n
            eq = solve-∀

    lt0 : ∀ {a b} → a < b → a + 0 < b + 0
    lt0 lt = +-monoˡ-< 0 lt

    cold-lt : ∀ {X : Set} (l : Tape X) → (∀ {κ} → due l ≡ just κ → at q <ᴷ κ ≡ true) → pot {Γ} D (coldS true l) < 3 + D
    cold-lt l h with due l
    ... | just κ  = s≤s (wt-ahead D κ (h refl))
    ... | nothing = s≤s z≤n

    part : at (q ++ [ ix 0 ]) <ᴷ at (q ++ [ ix 1 ]) ≡ true
    part = trans (at-<ᴷ (q ++ [ ix 0 ]) (q ++ [ ix 1 ])) (<ᵖ-part q {ix 0} {ix 1} [] [] refl)

  begun : ∀ (o′ : PureObs Γ A) {τ k′} → Path (load o) rs ⟨ c , pend o′ q , subscribing , q ⟩
        → Driver.step R ⟨ c , pend o′ q , subscribing , q ⟩ ≡ Driver.silent τ k′
        → (∀ {q′} → q′ ∈ L → at q <ᴷ at q′ ≡ true → Clock k′ <ᴷ at q′ ≡ true)
        → Wᶜ L p (at q) k′ < Wᶜ L p (at q) ⟨ c , pend o′ q , subscribing , q ⟩
  begun (map f s′)         pth refl _ = lt0 (lighter-at c ≤-refl)
  begun (scan f z s′)      pth refl _ = lt0 (lighter-at c ≤-refl)
  begun (takeWhile i f s′) pth refl _ = lt0 (lighter-at c (take-arith (2 * (2 + D)) (3 + D) (syn (2 + D) s′)))
  begun (flatMap op f s′)  pth refl _ = lt0 (lighter-at c (flat-arith (3 + D) (syn (2 + D) s′)))
  begun (connect s′ b)     pth refl _ =
    lt0 (lighter-at c (conn-arith _ (2 + D) (syn (suc D) s′) (syn (suc D) b) (wt-ahead D (at (q ++ [ ix 1 ])) (below q))))
  begun (defer l)          pth refl kept =
    let (_ , tq , le) = defer-guard o pth m
    in ⊥-elim (clash (<ᴷ-trans (at (q ++ [ ix 1 ])) (at (q ++ [ ix 0 ])) (at (q ++ [ ix 1 ])) (kept (∈-++⁺ˡ (cov tq le)) (below q)) part)
                       (<ᴷ-irrefl (at (q ++ [ ix 1 ]))))
  begun (cold x)           pth refl _ = lt0 (lighter-at c (cold-lt _ (opening-ahead o pth)))
  begun empty              pth refl _ = lt0 (lighter-at c (s≤s (wt-ahead D (at (q ++ [ last ])) (below q))))
  begun (of xs)            pth refl _ = lt0 (lighter-at c (of-lt xs))
  begun (connected x)      pth eq   _ with closedUp c x
  begun (connected x)      pth refl _ | true  = lt0 (lighter-at c (s≤s (wt-ahead D (at (q ++ [ last ])) (below q))))
  begun (connected x)      pth refl _ | false = lt0 (lighter-at c (s≤s z≤n))

-- A STILL SUBSCRIBE LIGHTENS: a subscribe trades its syntax for what it
-- leaves — its source pending a level down, or the marks it owes, each
-- strictly past where it was made; a defer passes its guard row, so is
-- never still.
lightens-begin : ∀ {R} (o : PureObs [] R) {rs Γ A} {c : Ctx R Γ A} {s q k′ p e}
               → Path (load o) rs ⟨ c , s , subscribing , q ⟩
               → Meets (enter (⟦ o ⟧ []ᴬ) root) (conv rs ++ [ (p , e) ])
               → ∀ ks → (∀ {q′ e′} → enter (⟦ o ⟧ []ᴬ) root q′ e′ → q′ ≼ p → q′ ∈ ks)
               → Still (ks ++ anc ks) k′ ⟨ c , s , subscribing , q ⟩
               → Wᶜ (ks ++ anc ks) p (at q) k′ < Wᶜ (ks ++ anc ks) p (at q) ⟨ c , s , subscribing , q ⟩
lightens-begin o {c = c} {q = q} pth m ks cov ((τ , eq) , kept) with pend-focus o pth
... | o′ , refl = Begun.begun o m ks cov c q o′ pth eq kept

-- STILL STEPS LIGHTEN, WEIGHED AT THE CLOCK THEY START FROM.
still-lightens : ∀ {R} (o : PureObs [] R) {rs k k′ p e} → Path (load o) rs k
               → Meets (enter (⟦ o ⟧ []ᴬ) root) (conv rs ++ [ (p , e) ])
               → ∀ ks → (∀ {q e′} → enter (⟦ o ⟧ []ᴬ) root q e′ → q ≼ p → q ∈ ks)
               → Still (ks ++ anc ks) k′ k → Wᶜ (ks ++ anc ks) p (Clock k) k′ < W (ks ++ anc ks) p k
still-lightens o {k = ⟨ c , s , rising ε , q ⟩} pth m ks cov st = lightens-rise o pth m ks cov st
still-lightens o {k = ⟨ c , s , subscribing , q ⟩} pth m ks cov st = lightens-begin o pth m ks cov st
still-lightens o {k = ⟨ c , s , absorbed , q ⟩} pth m ks cov st = lightens-run o pth m ks cov st
