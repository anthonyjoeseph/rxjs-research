-- COUNTING LANES ALONG A RUN: a counter that rises at each lane's start,
-- falls at each lane's end and empties at a cut covers every lane
-- started and neither ended nor cut, wherever each end is of a lane so
-- covered and each start of at most one lane.  At zero, every lane
-- started and never cut has ended (`drained`).
module simultaneous.LaneCount where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_]; length)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.Any.Properties using (++⁺ˡ; ++⁺ʳ; ++⁻)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (ℕ; zero; suc; _≤_; _∸_; z≤n; s≤s)
open import Data.Nat.Properties using (∸-monoˡ-≤; n≤1+n; ≤-trans; n≤0⇒n≡0)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import denotation.Laws.Count using (em)

-- How a row moves the counter.
data Kind : Set where
  kStart kDone kCut kOther : Kind

stepK : Kind → ℕ → ℕ
stepK kStart n = suc n
stepK kDone  n = n ∸ 1
stepK kCut   _ = 0
stepK kOther n = n

private
  kind-start : ∀ {k} → k ≡ kStart → k ≡ kDone → ⊥
  kind-start refl ()

  kind-cut : ∀ {k} → k ≡ kStart → k ≡ kCut → ⊥
  kind-cut refl ()

  kind-other : ∀ {k} → k ≡ kStart → k ≡ kOther → ⊥
  kind-other refl ()

module Count {R O : Set} (_≟_ : DecidableEquality O) (K : R → Kind) (Own : O → Set) (St Dn : O → R → Set)
             (act : List R → ℕ) (rs : List R) where

  StartIn DoneIn : List R → O → Set
  StartIn r s = Any (St s) r
  DoneIn r s = Any (Dn s) r

  -- A cut follows the lane's start.
  CutIn : List R → O → Set
  CutIn r s = Σ (List R) λ a → Σ (List R) λ b → r ≡ a ++ b × StartIn a s × Any (λ x → K x ≡ kCut) b

  Live : List R → O → Set
  Live r s = Own s × StartIn r s × ¬ DoneIn r s × ¬ CutIn r s

  Inv : List R → Set
  Inv r = Σ (List O) λ L → length L ≤ act r × (∀ {s} → Live r s → s ∈ L)

  private
    del : O → List O → List O
    del s []      = []
    del s (t ∷ L) with s ≟ t
    ... | yes _ = L
    ... | no _  = t ∷ del s L

    del-len : ∀ {s L} → s ∈ L → suc (length (del s L)) ≡ length L
    del-len {s} {t ∷ L} i with s ≟ t
    ... | yes _ = refl
    ... | no ne with i
    ...   | here e  = ⊥-elim (ne e)
    ...   | there j = cong suc (del-len j)

    del-keep : ∀ {s s₀ L} → s ∈ L → ¬ s ≡ s₀ → s ∈ del s₀ L
    del-keep {s₀ = s₀} {t ∷ L} i ne with s₀ ≟ t
    del-keep (here refl) ne | yes refl = ⊥-elim (ne refl)
    del-keep (there j)   ne | yes refl = j
    del-keep (here e)    ne | no _     = here e
    del-keep (there j)   ne | no _     = there (del-keep j ne)

    cut-mono : ∀ {xs s} x → CutIn xs s → CutIn (xs ++ [ x ]) s
    cut-mono x (a , b , eq , si , cb) = a , b ++ [ x ] , trans (cong (_++ [ x ]) eq) (++-assoc a b [ x ]) , si , ++⁺ˡ cb

  module _ (act-step : ∀ xs x ys → rs ≡ xs ++ x ∷ ys → act (xs ++ [ x ]) ≡ stepK (K x) (act xs))
           (st-kind : ∀ {s x} → St s x → K x ≡ kStart) (dn-kind : ∀ {s x} → Dn s x → K x ≡ kDone)
           (st-one : ∀ xs x ys → rs ≡ xs ++ x ∷ ys → ∀ {s s′} → Own s → Own s′ → St s x → St s′ x → s ≡ s′)
           (dn-live : ∀ xs x ys → rs ≡ xs ++ x ∷ ys → K x ≡ kDone → ¬ ¬ Σ O λ s → Dn s x × Live xs s) where

    private
      -- A lane live past a row that starts none was live before it.
      before : ∀ {xs x s} → (K x ≡ kStart → ⊥) → Live (xs ++ [ x ]) s → Live xs s
      before {xs} {x} nk (o , si , nd , nc) with ++⁻ xs si
      ... | inj₁ si′        = o , si′ , (λ d → nd (++⁺ˡ d)) , λ c → nc (cut-mono x c)
      ... | inj₂ (here st)  = ⊥-elim (nk (st-kind st))

      step : ∀ xs x ys → rs ≡ xs ++ x ∷ ys → Inv xs → ¬ ¬ Inv (xs ++ [ x ])
      step xs x ys eq (L , le , mem) with K x in kx
      ... | kStart = em {P = Σ O λ s → Own s × St s x}
        (λ (s₀ , o₀ , st₀) κ → κ (s₀ ∷ L , subst (suc (length L) ≤_) (sym a≡) (s≤s le) , λ where
          {s} (o , si , nd , nc) → [ (λ si′ → there (mem (o , si′ , (λ d → nd (++⁺ˡ d)) , λ c → nc (cut-mono x c))))
                                   , (λ { (here st) → here (st-one xs x ys eq o o₀ st st₀) }) ]′ (++⁻ xs si)))
        (λ ne κ → κ (L , subst (length L ≤_) (sym a≡) (≤-trans le (n≤1+n _)) , λ where
          {s} (o , si , nd , nc) → [ (λ si′ → mem (o , si′ , (λ d → nd (++⁺ˡ d)) , λ c → nc (cut-mono x c)))
                                   , (λ { (here st) → ⊥-elim (ne (s , o , st)) }) ]′ (++⁻ xs si)))
        where
          a≡ : act (xs ++ [ x ]) ≡ suc (act xs)
          a≡ = trans (act-step xs x ys eq) (cong (λ k → stepK k (act xs)) kx)
      ... | kDone = λ κ → dn-live xs x ys eq kx λ (s₀ , dn₀ , lv₀) →
        κ (del s₀ L , subst (_≤ act (xs ++ [ x ])) (sym (cong (_∸ 1) (del-len (mem lv₀))))
                        (subst (length L ∸ 1 ≤_) (sym a≡) (∸-monoˡ-≤ 1 le))
          , λ {s} lv → del-keep (mem (before (λ k → kind-start k kx) lv))
                         λ { refl → let (_ , _ , nd , _) = lv in nd (++⁺ʳ xs (here dn₀)) })
        where
          a≡ : act (xs ++ [ x ]) ≡ act xs ∸ 1
          a≡ = trans (act-step xs x ys eq) (cong (λ k → stepK k (act xs)) kx)
      ... | kCut = λ κ → κ ([] , z≤n , λ { {s} (o , si , nd , nc) → [ (λ si′ → ⊥-elim (nc (xs , [ x ] , refl , si′ , here kx)))
                                                                    , (λ { (here st) → ⊥-elim (kind-cut (st-kind st) kx) }) ]′ (++⁻ xs si) })
      ... | kOther = λ κ → κ (L , subst (length L ≤_) (sym a≡) le , λ lv → mem (before (λ k → kind-other k kx) lv))
        where
          a≡ : act (xs ++ [ x ]) ≡ act xs
          a≡ = trans (act-step xs x ys eq) (cong (λ k → stepK k (act xs)) kx)

      go : ∀ xs ys → rs ≡ xs ++ ys → Inv xs → ¬ ¬ Inv rs
      go xs []       eq I κ = κ (subst Inv (sym (trans eq (++-identityʳ xs))) I)
      go xs (y ∷ ys) eq I κ = step xs y ys eq I λ I′ → go (xs ++ [ y ]) ys (trans eq (sym (++-assoc xs [ y ] ys))) I′ κ

    covered : ¬ ¬ Inv rs
    covered = go [] rs refl ([] , z≤n , λ { (_ , () , _) })

    -- AT ZERO, EVERY LANE STARTED AND NEVER CUT HAS ENDED.
    drained : act rs ≡ 0 → ∀ {s} → Own s → StartIn rs s → ¬ CutIn rs s → ¬ ¬ DoneIn rs s
    drained z o si nc nd = covered λ (L , le , mem) → empty L (subst (length L ≤_) z le) (mem (o , si , nd , nc))
      where
        empty : ∀ {s} L → length L ≤ 0 → s ∈ L → ⊥
        empty (_ ∷ _) () _
