{-# OPTIONS --guardedness #-}

-- THE EMISSION SET'S LAWS: the meaning of a node is its operator applied to its
-- children's meanings, so proofs over it go one operator at a time; and
-- `map` fuses.  Every former but `defer` means its operator by
-- definition; `defer` unfolds.
--
-- THE UNFOLDING is read through the size modulus (`Laws.Modulus`).  Each
-- approximant is within its index of the next (`settle`): a `defer` adds
-- one level below its subscription, so unfolding once more moves only rows
-- past a bigger one.  The meaning is within every index of its approximant
-- (`from`), and `defer` is contractive, so a `defer`'s meaning agrees with
-- its unfolded body at every bound, which is having the same rows.
--
-- Each operator keeps the modulus (`-ne`) only where its subscriptions are
-- ADMISSIBLE (`Laws.Worlds`): reachable positions whose world no hot row
-- lies in, under an environment whose handles keep the invariant.  A
-- `connect` reads its source's rows and its body's apart by their worlds.
--
-- The unfolding holds only there.  At a position headed by `last`, a timer
-- row `ix (τ + t) ∷ sub e ∷ []` sorts before the spin of an unreached
-- `defer`: with `l` a merge over `of [true, false]`, `true` to `defer l`
-- and `false` to a cold whose first frame is at 1, each depth's timer row
-- has an earlier one below it, so the limit truncates them all, while the
-- unfolded body shows the first.  A cold handle whose rows include
-- `[ix 0, sub p]` does the same at a reachable position.
module denotation.EmissionSet.Laws where

open import Data.Bool using (Bool; T; true; false; not)
open import Data.Bool.Properties using (T-≡)
open import Data.Unit using (tt)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (_∷_; lookup)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _≤?_)
open import Data.Nat.Properties using (n≤1+n; ≤-trans; m≤m+n)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Data.List.Properties using (∷ʳ-injectiveˡ; ++-identityʳ)
open import Data.Maybe using (just; nothing)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable.Core using (decidable-stable; ¬¬-excluded-middle)

open import Tree using (Obs; Later; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.MonotonicList.Events using (Timeline; Pos; ix; sub; last; inside; <ᵖ-apart)
open import denotation.EmissionSet
  using (Ev; out; skip; end; EmissionSet; _≺_; _≼_; Few; Truncate; Rejoin; shown; ended; late; guard; body;
  Den; hot; enter; After; DenEnv; approxᵀ; ⟦_⟧ᵀ; coldᵀ; emptyᵀ; ofᵀ; mapᵀ; scanᵀ; takeWhileᵀ;
  flatMapᵀ; connectᵀ; deferᵀ; ⊥ᵀ; MapT; map-out; map-skip; map-end)
import denotation.EmissionSet as ES
open import denotation.EmissionSet.Laws.Modulus
  using (size; size-++; ≺-irrefl; Bnd<; few-ind; entered-few; ≺-trans; ≺→≼; ≼-refl; ≼-trans; ≼-or-≻; ≺-≼-≺; ≼-≺-≺; ≺-ext; few-via; AgreeTo; ⟨_⟩; upto; AgreeTo-sym; AgS; trunc-ag; trunc-to; ~-cold; _≈⟨_∣_⟩_; ≈-refl; ≈-sym; ≈-trans; ≈-mono; Same; agree-all; LimD; limit; ticks; contract; unfold₀; _~⟨_⟩_; ~-refl)
open import denotation.EmissionSet.Laws.Worlds using (Ok; _⊕_; Lawful; InvAt; in-world; InvD; Hots; GoodEnv; world-after; ok-step; inv-widen; empty-inv; of-inv; spin-inv; map-inv; scan-inv; defer-inv; lim-inv)
open import denotation.EmissionSet.Laws.Connect using (connect-inv)
open import denotation.EmissionSet.Laws.TakeInv using (takeWhile-inv)
open import denotation.EmissionSet.Laws.ConnectNe using (Causal; proper-ag; connect-ne)

-- The same rows at every subscription.
_≅_ : ∀ {A} → Den A → Den A → Set
d ≅ d′ = ∀ p {q e} → (enter d p q e → enter d′ p q e) × (enter d′ p q e → enter d p q e)

private
  ≅-refl : ∀ {A} (d : Den A) → d ≅ d
  ≅-refl d p = (λ x → x) , (λ x → x)

record Compositionalᵀ : Set₁ where
  field
    coldᶜ      : ∀ {Γ A} (c : Timeline A) (ρ : DenEnv Γ) → ⟦ cold c ⟧ᵀ ρ ≅ coldᵀ c
    emptyᶜ     : ∀ {Γ A} (ρ : DenEnv Γ) → ⟦ empty {Γ = Γ} {A = A} ⟧ᵀ ρ ≅ emptyᵀ
    ofᶜ        : ∀ {Γ A} (xs : List A) (ρ : DenEnv Γ) → ⟦ of {Γ = Γ} xs ⟧ᵀ ρ ≅ ofᵀ xs
    mapᶜ       : ∀ {Γ A B} (f : A → B) (s : Obs Timeline Γ A) (ρ : DenEnv Γ) → ⟦ map f s ⟧ᵀ ρ ≅ mapᵀ f (⟦ s ⟧ᵀ ρ)
    scanᶜ      : ∀ {Γ A B} (f : B → A → B) z (s : Obs Timeline Γ A) (ρ : DenEnv Γ) → ⟦ scan f z s ⟧ᵀ ρ ≅ scanᵀ f z (⟦ s ⟧ᵀ ρ)
    takeWhileᶜ : ∀ {Γ A} (i : Bool) (k : A → Bool) (s : Obs Timeline Γ A) (ρ : DenEnv Γ) → ⟦ takeWhile i k s ⟧ᵀ ρ ≅ takeWhileᵀ i k (⟦ s ⟧ᵀ ρ)
    flatMapᶜ   : ∀ {Γ A B} (op : FlatOp) (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) (ρ : DenEnv Γ)
               → ⟦ flatMap op f s ⟧ᵀ ρ ≅ flatMapᵀ op (λ a → ⟦ f a ⟧ᵀ ρ) (⟦ s ⟧ᵀ ρ)
    connectᶜ   : ∀ {Γ A B} (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) (ρ : DenEnv Γ)
               → ⟦ connect s b ⟧ᵀ ρ ≅ connectᵀ (⟦ s ⟧ᵀ ρ) (λ h → ⟦ b ⟧ᵀ (h ∷ ρ))
    connectedᶜ : ∀ {Γ A} (i : A ∈ Γ) (ρ : DenEnv Γ) → ⟦ connected i ⟧ᵀ ρ ≅ lookup ρ i
    deferᶜ     : ∀ {Γ A} (l : Later Timeline Γ A) (ρ : DenEnv Γ) → GoodEnv ρ
               → Same (Ok (Hots ρ)) (⟦ defer l ⟧ᵀ ρ) (deferᵀ (⟦ Later.force l ⟧ᵀ ρ))

------------------------------------------------------------------------
-- Causality

-- Every handle alike at and below `q`.
EnvAg : ∀ {Γ} → Pos → DenEnv Γ → DenEnv Γ → Set₁
EnvAg {Γ} q ρ ρ′ = ∀ {A} (i : A ∈ Γ) → lookup ρ i ~⟨ q ⟩ lookup ρ′ i

------------------------------------------------------------------------
-- Leaves

postulate
  -- EACH OPERATOR KEEPS THE MODULUS at admissible subscriptions.
  -- A JOINER keeps the bound uniformly in the lane: no lane is listed.
  --
  -- DEAD ROUTE: an index per lane, the largest over the outer values that
  --   `Few` lists.  `Few` lists positions, and which value a position
  --   holds is not decidable.
  flatMap-ne   : ∀ {A B H k} (op : FlatOp) {f f′ : A → Den B} {s s′ : Den A}
               → InvD H s → InvD H s′ → (∀ a → InvD H (f a)) → (∀ a → InvD H (f′ a))
               → s ≈⟨ Ok H ∣ k ⟩ s′ → (∀ a → f a ≈⟨ Ok H ∣ k ⟩ f′ a) → flatMapᵀ op f s ≈⟨ Ok H ∣ k ⟩ flatMapᵀ op f′ s′

  -- EACH OPERATOR KEEPS THE INVARIANT.
  cold-inv      : ∀ {A H} (c : Timeline A) → InvD H (coldᵀ c)
  flatMap-inv   : ∀ {A B H} (op : FlatOp) {f : A → Den B} {s : Den A} → InvD H s → (∀ a → InvD H (f a)) → InvD H (flatMapᵀ op f s)

  -- A lawful hot keeps it among its own rows.
  lawful-hot : ∀ {A H} {t : EmissionSet A} → Lawful t → InvD (H ⊕ t) (hot t)


------------------------------------------------------------------------
-- Operators that read a row where it lies

-- MAP KEEPS EVERY ROW where it is.
private
  map-ag : ∀ {A B q} (f : A → B) {t t′ : EmissionSet A} → AgreeTo q t t′ → AgreeTo q (MapT f t) (MapT f t′)
  map-ag {A} f {t} {t′} a = ⟨ (λ {y} yq → go (λ {e} → proj₁ (upto a {y} {e} yq)) , go (λ {e} → proj₂ (upto a {y} {e} yq))) ⟩
    where
      go : ∀ {u u′ : EmissionSet A} {y} → (∀ {e} → u y e → u′ y e) → ∀ {e} → MapT f u y e → MapT f u′ y e
      go h (map-out x)  = map-out (h x)
      go h (map-skip x) = map-skip (h x)
      go h (map-end x)  = map-end (h x)

  map-up : ∀ {A B} (f : A → B) {t : EmissionSet A} {y e} → t y e → Σ (Ev B) (MapT f t y)
  map-up f {e = out a} x = _ , map-out x
  map-up f {e = skip}  x = _ , map-skip x
  map-up f {e = end}   x = _ , map-end x

  map-agS : ∀ {A B N} (f : A → B) {t t′ : EmissionSet A} → AgS N t t′ → AgS N (MapT f t) (MapT f t′)
  map-agS f ag q (inj₁ b) = map-ag f (ag q (inj₁ λ x yq → b (proj₂ (map-up f x)) yq))
  map-agS f ag q (inj₂ b) = map-ag f (ag q (inj₂ λ x yq → b (proj₂ (map-up f x)) yq))

map-ne : ∀ {A B R k} (f : A → B) {s s′ : Den A} → s ≈⟨ R ∣ k ⟩ s′ → mapᵀ f s ≈⟨ R ∣ k ⟩ mapᵀ f s′
map-ne f ag p r = trunc-ag (map-agS f (ag p r))

map-causal : ∀ {A B q} (f : A → B) {s s′ : Den A} → s ~⟨ q ⟩ s′ → mapᵀ f s ~⟨ q ⟩ mapᵀ f s′
map-causal f a = ~-cold λ p → map-ag f (a p)

-- SCAN AND TAKEWHILE read every value, but past the bound only to know
-- it lies past it.
private
  -- A condition on every value: read at or before `Q`, free past it.
  over : ∀ {A Q} {t t′ : EmissionSet A} → AgreeTo Q t t′ → (P : Pos → Set) → (∀ {k} → Q ≺ k → P k)
       → (∀ {k b} → t k (out b) → P k) → ∀ {k b} → t′ k (out b) → P k
  over {Q = Q} a P far h {k} x with ≼-or-≻ k Q
  ... | inj₁ kQ = h (proj₂ (upto a {k} kQ) x)
  ... | inj₂ Qk = far Qk

  module SC {A B : Set} (f : B → A → B) (z : B) {Q : Pos} where
    open ES.Scan using (Acc; acc₀; acc; ScanT; sval; sstep; send)

    acc-to : ∀ {t t′ : EmissionSet A} → AgreeTo Q t t′ → ∀ {q b} → q ≼ Q → Acc f z t q b → Acc f z t′ q b
    acc-to a {q} qQ (acc₀ x mn) =
      acc₀ (proj₁ (upto a {q} qQ) x) (over a (λ k → q ≼ k) (λ {k} Qk → ≺→≼ {q} {k} (≼-≺-≺ {q} {Q} {k} qQ Qk)) mn)
    acc-to a {q′} q′Q (acc {q} ac x lt nx) =
      acc (acc-to a qQ ac) (proj₁ (upto a {q′} q′Q) x) lt
          (over a (λ k → q ≺ k → q′ ≼ k) (λ {k} Qk _ → ≺→≼ {q′} {k} (≼-≺-≺ {q′} {Q} {k} q′Q Qk)) nx)
      where qQ = ≺→≼ {q} {Q} (≺-≼-≺ {q} {q′} {Q} lt q′Q)

    scan-to : ∀ {t t′ : EmissionSet A} → AgreeTo Q t t′ → ∀ {y e} → y ≼ Q → ScanT f z t y e → ScanT f z t′ y e
    scan-to a {y} yQ (sval ac) = sval (acc-to a yQ ac)
    scan-to a {y} yQ (sstep x) = sstep (proj₁ (upto a {y} yQ) x)
    scan-to a {y} yQ (send x)  = send (proj₁ (upto a {y} yQ) x)

  module TW {A : Set} (incl : Bool) (keep : A → Bool) (p : Pos) {Q : Pos} where
    open ES.TakeWhile using (TakeT; Failed; pass; fail; stop; step; tend; left)

    fail-to : ∀ {t t′ : EmissionSet A} {q} → AgreeTo Q t t′ → q ≼ Q → Failed incl keep t p q → Failed incl keep t′ p q
    fail-to {q = q} a qQ (q′ , b , x , nk , lt) = q′ , b , proj₁ (upto a {q′} (≺→≼ {q′} {Q} (≺-≼-≺ {q′} {q} {Q} lt qQ))) x , nk , lt

    take-to : ∀ {t t′ : EmissionSet A} → AgreeTo Q t t′ → ∀ {y e} → y ≼ Q → TakeT incl keep t p y e → TakeT incl keep t′ p y e
    take-to a {y} yQ (pass x k nf)      = pass (proj₁ (upto a {y} yQ) x) k (λ g → nf (fail-to (AgreeTo-sym a) yQ g))
    take-to a     yQ (fail {q} x k nf i) = fail (proj₁ (upto a {q} qQ) x) k (λ g → nf (fail-to (AgreeTo-sym a) qQ g)) i
      where qQ = ≺→≼ {q} {Q} (≺-≼-≺ {q} {q ++ [ ix 0 ]} {Q} (≺-ext q []) yQ)
    take-to a     yQ (stop {q} x k nf)  = stop (proj₁ (upto a {q} qQ) x) k (λ g → nf (fail-to (AgreeTo-sym a) qQ g))
      where qQ = ≺→≼ {q} {Q} (≺-≼-≺ {q} {q ++ [ last ]} {Q} (≺-ext q []) yQ)
    take-to a {y} yQ (step x nf)        = step (proj₁ (upto a {y} yQ) x) (λ g → nf (fail-to (AgreeTo-sym a) yQ g))
    take-to a {y} yQ (tend x nf)        = tend (proj₁ (upto a {y} yQ) x) (λ g → nf (fail-to (AgreeTo-sym a) yQ g))
    take-to a {y} yQ (left x fd ins)    = left (proj₁ (upto a {y} yQ) x) (fail-to a yQ fd) ins

scan-causal : ∀ {A B q} (f : B → A → B) z {s s′ : Den A} → s ~⟨ q ⟩ s′ → scanᵀ f z s ~⟨ q ⟩ scanᵀ f z s′
scan-causal f z a = ~-cold λ p → ⟨ (λ yq → SC.scan-to f z (a p) yq , SC.scan-to f z (AgreeTo-sym (a p)) yq) ⟩

-- A SCAN BOUNDS ITS SOURCE: a value with few rows before it has a fold,
-- from the latest value among those rows, or from none.  Which of them
-- holds a value is not decidable, but the bound is, so it is read
-- classically.
private
  module SN {A B : Set} (f : B → A → B) (z : B) (t : EmissionSet A) where
    open ES.Scan f z t using (Acc; acc₀; acc; ScanT; sval; sstep; send)

    Val : Pos → Set
    Val k = Σ A λ a → t k (out a)

    -- The latest value before `w` among `ks`, or none there.
    Latest : Pos → List Pos → Set
    Latest w ks = (∀ {k} → k ∈ ks → Val k → k ≺ w → ⊥)
                ⊎ Σ Pos λ v → Val v × v ≺ w × (∀ {k} → k ∈ ks → Val k → k ≺ w → k ≼ v)

    latest : ∀ w ks → ¬ ¬ Latest w ks
    latest w []       ¬L = ¬L (inj₁ λ ())
    latest w (k ∷ ks) ¬L = latest w ks λ L → ¬¬-excluded-middle {A = Val k × k ≺ w} λ d → ¬L (add L d)
      where
        add : Latest w ks → Dec (Val k × k ≺ w) → Latest w (k ∷ ks)
        add (inj₁ none) (no ¬h) = inj₁ λ { {_} (here refl) vk kw → ¬h (vk , kw) ; {_} (there m) → none m }
        add (inj₂ (v , vv , vw , mx)) (no ¬h) =
          inj₂ (v , vv , vw , λ { {_} (here refl) vk kw → ⊥-elim (¬h (vk , kw)) ; {_} (there m) → mx m })
        add (inj₁ none) (yes (vk , kw)) =
          inj₂ (k , vk , kw , λ { {_} (here refl) _ _ → ≼-refl {k} ; {_} (there m) vk′ k′w → ⊥-elim (none m vk′ k′w) })
        add (inj₂ (v , vv , vw , mx)) (yes (vk , kw)) with ≼-or-≻ v k
        ... | inj₁ vk≼ = inj₂ (k , vk , kw , λ { {_} (here refl) _ _ → ≼-refl {k} ; {k′} (there m) vk′ k′w → ≼-trans {k′} {v} {k} (mx m vk′ k′w) vk≼ })
        ... | inj₂ kv  = inj₂ (v , vv , vw , λ { {_} (here refl) _ _ → ≺→≼ {k} {v} kv ; {_} (there m) → mx m })

    fold : ∀ {w} → Few t w → ∀ {a} → t w (out a) → ¬ ¬ Σ B (Acc w)
    fold = few-ind (λ w → ∀ {a} → t w (out a) → ¬ ¬ Σ B (Acc w)) step
      where
        step : ∀ {w} → Few t w → (∀ {v e} → t v e → v ≺ w → ∀ {a} → t v (out a) → ¬ ¬ Σ B (Acc v))
             → ∀ {a} → t w (out a) → ¬ ¬ Σ B (Acc w)
        step {w} (ks , h) ih {a} x ¬A = latest w ks λ
          { (inj₁ none) → ¬A (f z a , acc₀ x λ y kw → none (h y kw) (_ , y) kw)
          ; (inj₂ (v , (_ , xv) , vw , mx)) → ih xv vw xv λ
              { (b , av) → ¬A (f b a , acc av x vw λ y vk kw → mx (h y kw) (_ , y) kw vk) } }

    bound : ∀ {N q} → (∀ {y e} → t y e → Few t y) → Bnd< N ScanT q → Bnd< N t q
    bound     fw bd {y} {skip}  x yq = bd (sstep x) yq
    bound     fw bd {y} {end}   x yq = bd (send x) yq
    bound {N} fw bd {y} {out a} x yq = decidable-stable (size y ≤? N) λ ¬le → fold (fw x) x λ { (_ , ac) → ¬le (bd (sval ac) yq) }

scan-ne : ∀ {A B R k} (f : B → A → B) z {s s′ : Den A} → s ≈⟨ R ∣ k ⟩ s′ → scanᵀ f z s ≈⟨ R ∣ k ⟩ scanᵀ f z s′
scan-ne f z {s} {s′} ag p r = trunc-ag go
  where
    go : AgS _ (ES.Scan.ScanT f z (enter s p)) (ES.Scan.ScanT f z (enter s′ p))
    go q (inj₁ bd) = ⟨ (λ yq → SC.scan-to f z a yq , SC.scan-to f z (AgreeTo-sym a) yq) ⟩
      where a = ag p r q (inj₁ (SN.bound f z (enter s p) (entered-few s p) bd))
    go q (inj₂ bd) = ⟨ (λ yq → SC.scan-to f z a yq , SC.scan-to f z (AgreeTo-sym a) yq) ⟩
      where a = ag p r q (inj₂ (SN.bound f z (enter s′ p) (entered-few s′ p) bd))

takeWhile-causal : ∀ {A q} (i : Bool) (keep : A → Bool) {s s′ : Den A} → s ~⟨ q ⟩ s′ → takeWhileᵀ i keep s ~⟨ q ⟩ takeWhileᵀ i keep s′
takeWhile-causal i keep a = ~-cold λ p → ⟨ (λ yq → TW.take-to i keep p (a p) yq , TW.take-to i keep p (AgreeTo-sym (a p)) yq) ⟩

-- A TAKEWHILE BOUNDS ITS SOURCE before each of its rows' sources.  A
-- source row before the first failure is passed, or is the failure, shown
-- one label down; one past it lies before a row under the subscription,
-- so is under it, and is left as a skip.  Whether a row is past the
-- failure is not decidable, but the bound is.
private
  module TN {A : Set} (incl : Bool) (keep : A → Bool) (p : Pos) where
    open ES.TakeWhile incl keep using (TakeT; Failed; pass; fail; stop; step; tend; left)

    fd-trans : ∀ {X : EmissionSet A} {w z} → Failed X p w → w ≺ z → Failed X p z
    fd-trans {w = w} {z} (q , a , x , nk , lt) wz = q , a , x , nk , ≺-trans {q} {w} {z} lt wz

    -- A row's source is where `at` agrees.
    move : ∀ {X Y : EmissionSet A} {Q} → (∀ {z e} → X z e → z ≼ Q → (Failed X p z → T (inside p z)) → AgreeTo z X Y)
         → ∀ {y e} → y ≼ Q → TakeT X p y e → TakeT Y p y e
    move at {y} yQ (pass x k nf)       = TW.take-to incl keep p (at x yQ (⊥-elim ∘ nf)) (≼-refl {y}) (pass x k nf)
    move at {y} yQ (step x nf)         = TW.take-to incl keep p (at x yQ (⊥-elim ∘ nf)) (≼-refl {y}) (step x nf)
    move at {y} yQ (tend x nf)         = TW.take-to incl keep p (at x yQ (⊥-elim ∘ nf)) (≼-refl {y}) (tend x nf)
    move at {y} yQ (left x fd ins)     = TW.take-to incl keep p (at x yQ (λ _ → ins)) (≼-refl {y}) (left x fd ins)
    move {Q = Q} at yQ (fail {q} x k nf i) =
      fail (proj₁ (upto a {q} (≼-refl {q})) x) k (λ g → nf (TW.fail-to incl keep p (AgreeTo-sym a) (≼-refl {q}) g)) i
      where a = at x (≺→≼ {q} {Q} (≺-≼-≺ {q} {q ++ [ ix 0 ]} {Q} (≺-ext q []) yQ)) (⊥-elim ∘ nf)
    move {Q = Q} at yQ (stop {q} x k nf) =
      stop (proj₁ (upto a {q} (≼-refl {q})) x) k (λ g → nf (TW.fail-to incl keep p (AgreeTo-sym a) (≼-refl {q}) g))
      where a = at x (≺→≼ {q} {Q} (≺-≼-≺ {q} {q ++ [ last ]} {Q} (≺-ext q []) yQ)) (⊥-elim ∘ nf)

    module Core {H : Pos → Set} {k : ℕ} {s s′ : Den A} (Is : InvD H s) (Is′ : InvD H s′)
                (ag : s ≈⟨ Ok H ∣ k ⟩ s′) (ok : Ok H p) {Q : Pos}
                (bd : Bnd< (size p + k) (TakeT (enter s p) p) Q) where
      t t′ : EmissionSet A
      t  = enter s p
      t′ = enter s′ p
      I  = Is p ok
      I′ = Is′ p ok

      -- A source row before `z`, which is under the subscription if the row is past the failure.
      row-b : ∀ {w e z} → t w e → w ≺ z → z ≼ Q → (∀ {l ys} → z ≡ w ++ l ∷ ys → ⊥) → (Failed t p w → T (inside p z))
            → size w ≤ size p + k
      row-b {w} {e} {z} x wz zQ nu fz = decidable-stable (size w ≤? size p + k) λ ¬le →
        ¬¬-excluded-middle {A = Failed t p w} λ
          { (yes f) → ¬le (bd (left x f (in-world I x wz (fz f))) wQ)
          ; (no nf) → ¬le (pre x nf) }
        where
          wQ = ≺-≼-≺ {w} {z} {Q} wz zQ
          nu′ : ∀ ys → z ≡ w ++ ys → ⊥
          nu′ []       eq = ≺-irrefl {w} (subst (w ≺_) (trans eq (++-identityʳ w)) wz)
          nu′ (l ∷ ys) eq = nu eq
          stopQ : (w ++ [ last ]) ≺ Q
          stopQ = ≺-≼-≺ {w ++ [ last ]} {z} {Q} (Equivalence.from T-≡ (<ᵖ-apart w z [ last ] (Equivalence.to T-≡ wz) nu′)) zQ
          pre : ∀ {e} → t w e → ¬ Failed t p w → size w ≤ size p + k
          pre {skip}  x nf = bd (step x nf) wQ
          pre {end}   x nf = bd (tend x nf) wQ
          pre {out a} x nf with keep a in eq
          ... | true  = bd (pass x (subst T (sym eq) tt) nf) wQ
          ... | false = ≤-trans (subst (size w ≤_) (sym (size-++ w last)) (m≤m+n (size w) 1)) (bd (stop x (subst (T ∘ not) (sym eq) tt) nf) stopQ)

      flat-nu : ∀ {X : EmissionSet A} → InvAt H p X → ∀ {w e z e′} → X w e → X z e′ → ∀ {l ys} → z ≡ w ++ l ∷ ys → ⊥
      flat-nu J x z refl = InvAt.flat J x z

      bnd : ∀ {z e} → t z e → z ≼ Q → (Failed t p z → T (inside p z)) → Bnd< (size p + k) t z
      bnd xz zQ fz {w} x wz = row-b x wz zQ (flat-nu I x xz) (λ f → fz (fd-trans {X = t} f wz))

      bnd′ : ∀ {z e} → t′ z e → z ≼ Q → (Failed t′ p z → T (inside p z)) → Bnd< (size p + k) t′ z
      bnd′ x′ = few-ind P stp (entered-few s′ p x′) x′
        where
          P : Pos → Set
          P z = ∀ {e} → t′ z e → z ≼ Q → (Failed t′ p z → T (inside p z)) → Bnd< (size p + k) t′ z
          stp : ∀ {z} → Few t′ z → (∀ {v e} → t′ v e → v ≺ z → P v) → P z
          stp {z} _ ih xz zQ fz {w} x′ wz =
            row-b (proj₂ (upto a {w} (≼-refl {w})) x′) wz zQ (flat-nu I′ x′ xz)
              (λ f → fz (fd-trans {X = t′} (TW.fail-to incl keep p {t = t} {t′} a (≼-refl {w}) f) wz))
            where
              a = ag p ok w (inj₂ (ih x′ wz x′ (≺→≼ {w} {Q} (≺-≼-≺ {w} {z} {Q} wz zQ)) λ f → in-world I′ x′ wz (fz (fd-trans {X = t′} f wz))))

      agree : AgreeTo Q (TakeT t p) (TakeT t′ p)
      agree = ⟨ (λ yQ → move {Q = Q} (λ {z} x zQ fz → ag p ok z (inj₁ (bnd x zQ fz))) yQ
                      , move {Q = Q} (λ {z} x zQ fz → AgreeTo-sym (ag p ok z (inj₂ (bnd′ x zQ fz)))) yQ) ⟩

takeWhile-ne : ∀ {A H k} (i : Bool) (keep : A → Bool) {s s′ : Den A} → InvD H s → InvD H s′
             → s ≈⟨ Ok H ∣ k ⟩ s′ → takeWhileᵀ i keep s ≈⟨ Ok H ∣ k ⟩ takeWhileᵀ i keep s′
takeWhile-ne {H = H} {k} i keep {s} {s′} Is Is′ ag p ok = trunc-ag go
  where
    go : AgS (size p + k) (ES.TakeWhile.TakeT i keep (enter s p) p) (ES.TakeWhile.TakeT i keep (enter s′ p) p)
    go q (inj₁ bd) = TN.Core.agree i keep p {s = s} {s′} Is Is′ ag ok bd
    go q (inj₂ bd) = AgreeTo-sym (TN.Core.agree i keep p {s = s′} {s} Is′ Is (≈-sym {R = Ok H} {k} {s} {s′} ag) ok bd)

-- A CONNECT reads its body's end only up to the source step it shows.
private
  alive-to : ∀ {B Q k} {β β′ : EmissionSet B} → AgreeTo Q β β′ → k ≼ Q → (∀ {c} → β c end → k ≺ c) → ∀ {c} → β′ c end → k ≺ c
  alive-to {Q = Q} {k} a kQ al {c} x with ≼-or-≻ c Q
  ... | inj₁ cQ = al (proj₂ (upto a {c} cQ) x)
  ... | inj₂ Qc = ≼-≺-≺ {k} {Q} {c} kQ Qc

  conn-to : ∀ {A B Q} (s s′ : Den A) (F F′ : Den A → Den B) p
          → AgreeTo Q (enter s (p ++ [ ix 1 ])) (enter s′ (p ++ [ ix 1 ]))
          → AgreeTo Q (ES.Connect.β s F p) (ES.Connect.β s′ F′ p)
          → ∀ {y e} → y ≼ Q → ES.Connect.ConnT s F p y e → ES.Connect.ConnT s′ F′ p y e
  conn-to s s′ F F′ p aσ aβ {y} yQ (ES.Connect.body x) = ES.Connect.body (proj₁ (upto aβ {y} yQ) x)
  conn-to {Q = Q} s s′ F F′ p aσ aβ yQ (ES.Connect.shown {k} x al) =
    ES.Connect.shown (proj₁ (upto aσ {k} kQ) x) (alive-to aβ kQ al)
    where kQ = ≺→≼ {k} {Q} (≺-≼-≺ {k} {k ++ [ ix 0 ]} {Q} (≺-ext k []) yQ)
  conn-to s s′ F F′ p aσ aβ {y} yQ (ES.Connect.pinned x nal ins) =
    ES.Connect.pinned (proj₁ (upto aσ {y} yQ) x) (λ al → nal (alive-to (AgreeTo-sym aβ) yQ al)) ins

connect-causal : ∀ {A B q} {s s′ : Den A} {F F′ : Den A → Den B}
               → s ~⟨ q ⟩ s′ → (∀ {t t′} → AgreeTo q t t′ → F (hot t) ~⟨ q ⟩ F′ (hot t′)) → connectᵀ s F ~⟨ q ⟩ connectᵀ s′ F′
connect-causal {s = s} {s′} {F} {F′} as af = ~-cold λ p →
  ⟨ (λ {y} yq → conn-to s s′ F F′ p (as (p ++ [ ix 1 ])) (af (proper-ag (as (p ++ [ ix 1 ]))) (p ++ [ ix 0 ])) yq
              , conn-to s′ s F′ F p (AgreeTo-sym (as (p ++ [ ix 1 ]))) (AgreeTo-sym (af (proper-ag (as (p ++ [ ix 1 ]))) (p ++ [ ix 0 ]))) yq) ⟩

-- DEFER READS ITS BODY where it lies.
defer-causal : ∀ {A q} {s s′ : Den A} → s ~⟨ q ⟩ s′ → deferᵀ s ~⟨ q ⟩ deferᵀ s′
defer-causal a = ~-cold λ p →
  ⟨ (λ {y} yq → (λ { guard → guard ; (body x) → body (proj₁ (upto (a (p ++ [ ix 1 ])) {y} yq) x) })
              , (λ { guard → guard ; (body x) → body (proj₂ (upto (a (p ++ [ ix 1 ])) {y} yq) x) })) ⟩

lim-causal : ∀ {A q} {c c′ : ℕ → Den A} → (∀ n → c n ~⟨ q ⟩ c′ n) → LimD c ~⟨ q ⟩ LimD c′
lim-causal a = ~-cold λ p →
  ⟨ (λ {y} yq → (λ { (ES.from N l) → ES.from N λ n le → proj₁ (upto (a n p) {y} yq) (l n le) })
              , (λ { (ES.from N l) → ES.from N λ n le → proj₂ (upto (a n p) {y} yq) (l n le) })) ⟩

-- A JOINED HOT reads a row before the one it shows.
private
  rejoin-ag : ∀ {A q p} {t t′ : EmissionSet A} → AgreeTo q t t′ → ∀ {y e} → y ≼ q → Rejoin p t y e → Rejoin p t′ y e
  rejoin-ag {q = q} {p} a yq (shown {k} x w pk) = shown (proj₁ (upto a {k} (≺→≼ {k} {q} (≺-≼-≺ {k} {k ++ [ sub p ]} {q} (≺-ext k []) yq))) x) w pk
  rejoin-ag {q = q} {p} a yq (ended {c} x pc)   = ended (proj₁ (upto a {c} (≺→≼ {c} {q} (≺-≼-≺ {c} {c ++ [ sub p ]} {q} (≺-ext c []) yq))) x) pc
  rejoin-ag {q = q} {p} a yq (late {c} x cp)    =
    late (proj₁ (upto a {c} (≺→≼ {c} {q} (≺-≼-≺ {c} {p ++ [ last ]} {q} (≼-≺-≺ {c} {p} {p ++ [ last ]} cp (≺-ext p [])) yq))) x) cp

hot-causal : ∀ {A q} {t t′ : EmissionSet A} → AgreeTo q t t′ → hot t ~⟨ q ⟩ hot t′
hot-causal {q = q} a p = trunc-to ⟨ (λ {y} yq → rejoin-ag {q = q} {p} a yq , rejoin-ag {q = q} {p} (AgreeTo-sym a) yq) ⟩

-- A JOINER reads a lane only past its subscription, so a lane row at or
-- before the bound has its outer value there too.  The rest it reads (a
-- cut, a latest value, a first value, an unended lane) holds past the
-- bound by order alone.
private
  module Join {A B : Set} (Q : Pos) where
    -- Every lane agrees; a record, so its type names both families.
    record Lanes (f f′ : A → Den B) : Set where
      constructor lanes
      field lanes-ag : ∀ a → f a ~⟨ Q ⟩ f′ a
    open Lanes

    lanes-sym : ∀ {f f′} → Lanes f f′ → Lanes f′ f
    lanes-sym af = lanes λ a p → AgreeTo-sym (lanes-ag af a p)

    below : ∀ x y → x ≺ y → y ≼ Q → x ≼ Q
    below x y xy yQ = ≺→≼ {x} {Q} (≺-≼-≺ {x} {y} {Q} xy yQ)

    trans≼ : ∀ x y → x ≼ y → y ≼ Q → x ≼ Q
    trans≼ x y xy yQ = ≼-trans {x} {y} {Q} xy yQ

    beyond : ∀ x y → x ≼ Q → Q ≺ y → x ≼ y
    beyond x y xQ Qy = ≺→≼ {x} {y} (≼-≺-≺ {x} {Q} {y} xQ Qy)

    fwd : ∀ {X} {t t′ : EmissionSet X} → AgreeTo Q t t′ → ∀ y {e} → y ≼ Q → t y e → t′ y e
    fwd a y yQ = proj₁ (upto a {y} yQ)

    bwd : ∀ {X} {t t′ : EmissionSet X} → AgreeTo Q t t′ → ∀ y {e} → y ≼ Q → t′ y e → t y e
    bwd a y yQ = proj₂ (upto a {y} yQ)

    lane-to : ∀ {f f′} → Lanes f f′ → ∀ a s k {e} → k ≼ Q → After (f a) s k e → After (f′ a) s k e
    lane-to af a s k kQ (x , sk) = fwd (lanes-ag af a s) k kQ x , sk

    -- A lane at `q ++ [ ix 1 ]` with a row at or before the bound.
    value-below : ∀ q k → (q ++ [ ix 1 ]) ≺ k → k ≼ Q → q ≼ Q
    value-below q k sk kQ = below q k (≺-trans {q} {q ++ [ ix 1 ]} {k} (≺-ext q []) sk) kQ

    -- An unended lane: unended before `x` past the bound by order.
    unended-to : ∀ {f f′} → Lanes f f′ → ∀ a s x → x ≼ Q → (∀ {c} → After (f a) s c end → x ≼ c)
               → ∀ {c} → After (f′ a) s c end → x ≼ c
    unended-to af a s x xQ nl {c} l′ with ≼-or-≻ c Q
    ... | inj₁ cQ = nl (lane-to (lanes-sym af) a s c cQ l′)
    ... | inj₂ Qc = beyond x c xQ Qc

    least-to : ∀ {o o′ : EmissionSet A} → AgreeTo Q o o′ → ∀ q → q ≼ Q
             → (∀ {k b} → o k (out b) → q ≼ k) → ∀ {k b} → o′ k (out b) → q ≼ k
    least-to ao q qQ mn = over ao (λ k → q ≼ k) (λ {k} Qk → beyond q k qQ Qk) mn

    next-to : ∀ {o o′ : EmissionSet A} → AgreeTo Q o o′ → ∀ q q′ → q′ ≼ Q → ES.Values.Next o q q′ → ES.Values.Next o′ q q′
    next-to ao q q′ q′Q nx = over ao (λ k → q ≺ k → q′ ≼ k) (λ {k} Qk _ → beyond q′ k q′Q Qk) nx

    module MergeJ where
      open ES.Merge using (Done; MergeT; val; step; oend; opass; lane; lend; lpass)

      done-to : ∀ {f f′ : A → Den B} {o o′ : EmissionSet A} → AgreeTo Q o o′ → Lanes f f′ → ∀ c → c ≼ Q → Done f o c → Done f′ o′ c
      done-to ao af c cQ ((c₀ , x , c₀c) , h) =
          (c₀ , fwd ao c₀ (trans≼ c₀ c c₀c cQ) x , c₀c)
        , λ {q} {a} x′ qc → let (c′ , y , c′c) = h (bwd ao q (below q c qc cQ) x′) qc
                            in c′ , lane-to af a (q ++ [ ix 1 ]) c′ (trans≼ c′ c c′c cQ) y , c′c

      merge-to : ∀ {f f′ : A → Den B} {o o′ : EmissionSet A} → AgreeTo Q o o′ → Lanes f f′ → ∀ y {e} → y ≼ Q → MergeT f o y e → MergeT f′ o′ y e
      merge-to ao af _ yQ (val {q} x)                = val (fwd ao q (below q (q ++ [ ix 0 ]) (≺-ext q []) yQ) x)
      merge-to ao af y yQ (step x)                   = step (fwd ao y yQ x)
      merge-to ao af y yQ (oend x d)                 = oend (fwd ao y yQ x) (done-to ao af y yQ d)
      merge-to ao af y yQ (opass x nd)               = opass (fwd ao y yQ x) (λ d → nd (done-to (AgreeTo-sym ao) (lanes-sym af) y yQ d))
      merge-to ao af y yQ (lane {q} {a} x l w)       =
        lane (fwd ao q (value-below q y (proj₂ l) yQ) x) (lane-to af a (q ++ [ ix 1 ]) y yQ l) w
      merge-to ao af y yQ (lend {q} {a} x l d)       =
        lend (fwd ao q (value-below q y (proj₂ l) yQ) x) (lane-to af a (q ++ [ ix 1 ]) y yQ l) (done-to ao af y yQ d)
      merge-to ao af y yQ (lpass {q} {a} x l nd)     =
        lpass (fwd ao q (value-below q y (proj₂ l) yQ) x) (lane-to af a (q ++ [ ix 1 ]) y yQ l)
              (λ d → nd (done-to (AgreeTo-sym ao) (lanes-sym af) y yQ d))

    module SwitchJ where
      open ES.Switch using (Cut; Latest; Done; SwitchT; val; step; oend; opass; lane; lend; lpass; left)

      cut-to : ∀ (f f′ : A → Den B) {o o′ : EmissionSet A} → AgreeTo Q o o′ → ∀ q k → k ≼ Q → Cut f o q k → Cut f′ o′ q k
      cut-to f f′ ao q k kQ (q′ , a′ , x , qq′ , q′k) = q′ , a′ , fwd ao q′ (below q′ k q′k kQ) x , qq′ , q′k

      latest-to : ∀ (f f′ : A → Den B) {o o′ : EmissionSet A} → AgreeTo Q o o′ → ∀ q c → c ≼ Q → Latest f o q c → Latest f′ o′ q c
      latest-to f f′ ao q c cQ la {q′} x′ q′c = la {q′} (bwd ao q′ (below q′ c q′c cQ) x′) q′c

      done-to : ∀ (f f′ : A → Den B) {o o′ : EmissionSet A} → AgreeTo Q o o′ → Lanes f f′ → ∀ c → c ≼ Q → Done f o c → Done f′ o′ c
      done-to f f′ ao af c cQ ((c₀ , x , c₀c) , h) =
          (c₀ , fwd ao c₀ (trans≼ c₀ c c₀c cQ) x , c₀c)
        , λ {q} {a} x′ qc la′ →
            let (c′ , y , c′c) = h (bwd ao q (below q c qc cQ) x′) qc (latest-to f′ f (AgreeTo-sym ao) q c cQ la′)
            in c′ , lane-to af a (q ++ [ ix 1 ]) c′ (trans≼ c′ c c′c cQ) y , c′c

      switch-to : ∀ (f f′ : A → Den B) {o o′ : EmissionSet A} → AgreeTo Q o o′ → Lanes f f′ → ∀ y {e} → y ≼ Q → SwitchT f o y e → SwitchT f′ o′ y e
      switch-to f f′ ao af _ yQ (val {q} x)           = val (fwd ao q (below q (q ++ [ ix 0 ]) (≺-ext q []) yQ) x)
      switch-to f f′ ao af y yQ (step x)              = step (fwd ao y yQ x)
      switch-to f f′ ao af y yQ (oend x d)            = oend (fwd ao y yQ x) (done-to f f′ ao af y yQ d)
      switch-to f f′ ao af y yQ (opass x nd)          =
        opass (fwd ao y yQ x) (λ d → nd (done-to f′ f (AgreeTo-sym ao) (lanes-sym af) y yQ d))
      switch-to f f′ ao af y yQ (lane {q} {a} x l w nc) =
        lane (fwd ao q (value-below q y (proj₂ l) yQ) x) (lane-to af a (q ++ [ ix 1 ]) y yQ l) w
             (λ c → nc (cut-to f′ f (AgreeTo-sym ao) q y yQ c))
      switch-to f f′ ao af y yQ (lend {q} {a} x l nc d) =
        lend (fwd ao q (value-below q y (proj₂ l) yQ) x) (lane-to af a (q ++ [ ix 1 ]) y yQ l)
             (λ c → nc (cut-to f′ f (AgreeTo-sym ao) q y yQ c)) (done-to f f′ ao af y yQ d)
      switch-to f f′ ao af y yQ (lpass {q} {a} x l nc nd) =
        lpass (fwd ao q (value-below q y (proj₂ l) yQ) x) (lane-to af a (q ++ [ ix 1 ]) y yQ l)
              (λ c → nc (cut-to f′ f (AgreeTo-sym ao) q y yQ c)) (λ d → nd (done-to f′ f (AgreeTo-sym ao) (lanes-sym af) y yQ d))
      switch-to f f′ ao af y yQ (left {q} {a} x l c ins) =
        left (fwd ao q (value-below q y (proj₂ l) yQ) x) (lane-to af a (q ++ [ ix 1 ]) y yQ l) (cut-to f f′ ao q y yQ c) ins

    module ExhaustJ where
      open ES.Exhaust using (Cur; cur₀; run; drop; Done; ExhaustT; val; step; oend; opass; lane; lend; lpass)

      cur-le : ∀ {f : A → Den B} {o : EmissionSet A} {q₁ q} → Cur f o q₁ q → q ≼ q₁
      cur-le {q₁ = q₁} (cur₀ _ _)            = ≼-refl {q₁}
      cur-le {q₁ = q₂} (run _ _ _ _ _ _ _)    = ≼-refl {q₂}
      cur-le (drop {q₁} {q} {q₂ = q₂} cu _ _ _ lt _) = ≺→≼ {q} {q₂} (≼-≺-≺ {q} {q₁} {q₂} (cur-le cu) lt)

      cur-to : ∀ {f f′ : A → Den B} {o o′ : EmissionSet A} → AgreeTo Q o o′ → Lanes f f′ → ∀ q₁ q → q₁ ≼ Q → Cur f o q₁ q → Cur f′ o′ q₁ q
      cur-to ao af q₁ _ q₁Q (cur₀ x mn) = cur₀ (fwd ao q₁ q₁Q x) (least-to ao q₁ q₁Q mn)
      cur-to ao af q₂ _ q₂Q (run {q₁} {q} {a} {c} cu x l cq₂ x₂ lt nx) =
        run (cur-to ao af q₁ q q₁Q cu) (fwd ao q qQ x) (lane-to af a (q ++ [ ix 1 ]) c (below c q₂ cq₂ q₂Q) l) cq₂
            (fwd ao q₂ q₂Q x₂) lt (next-to ao q₁ q₂ q₂Q nx)
        where
          q₁Q = below q₁ q₂ lt q₂Q
          qQ  = trans≼ q q₁ (cur-le cu) q₁Q
      cur-to ao af q₂ q q₂Q (drop {q₁} {a = a} cu x nl x₂ lt nx) =
        drop (cur-to ao af q₁ q q₁Q cu) (fwd ao q qQ x) (unended-to af a (q ++ [ ix 1 ]) q₂ q₂Q nl)
             (fwd ao q₂ q₂Q x₂) lt (next-to ao q₁ q₂ q₂Q nx)
        where
          q₁Q = below q₁ q₂ lt q₂Q
          qQ  = trans≼ q q₁ (cur-le cu) q₁Q

      done-to : ∀ {f f′ : A → Den B} {o o′ : EmissionSet A} → AgreeTo Q o o′ → Lanes f f′ → ∀ c → c ≼ Q → Done f o c → Done f′ o′ c
      done-to ao af c cQ ((c₀ , x , c₀c) , h) =
          (c₀ , fwd ao c₀ (trans≼ c₀ c c₀c cQ) x , c₀c)
        , λ {q} {a} x′ qc r′ →
            let qQ = below q c qc cQ
                (c′ , y , c′c) = h (bwd ao q qQ x′) qc (cur-to (AgreeTo-sym ao) (lanes-sym af) q q qQ r′)
            in c′ , lane-to af a (q ++ [ ix 1 ]) c′ (trans≼ c′ c c′c cQ) y , c′c

      exhaust-to : ∀ {f f′ : A → Den B} {o o′ : EmissionSet A} → AgreeTo Q o o′ → Lanes f f′ → ∀ y {e} → y ≼ Q → ExhaustT f o y e → ExhaustT f′ o′ y e
      exhaust-to ao af _ yQ (val {q} x)       = val (fwd ao q (below q (q ++ [ ix 0 ]) (≺-ext q []) yQ) x)
      exhaust-to ao af y yQ (step x)          = step (fwd ao y yQ x)
      exhaust-to ao af y yQ (oend x d)        = oend (fwd ao y yQ x) (done-to ao af y yQ d)
      exhaust-to ao af y yQ (opass x nd)      = opass (fwd ao y yQ x) (λ d → nd (done-to (AgreeTo-sym ao) (lanes-sym af) y yQ d))
      exhaust-to ao af y yQ (lane {q} {a} x r l w) =
        lane (fwd ao q qQ x) (cur-to ao af q q qQ r) (lane-to af a (q ++ [ ix 1 ]) y yQ l) w
        where qQ = value-below q y (proj₂ l) yQ
      exhaust-to ao af y yQ (lend {q} {a} x r l d) =
        lend (fwd ao q qQ x) (cur-to ao af q q qQ r) (lane-to af a (q ++ [ ix 1 ]) y yQ l) (done-to ao af y yQ d)
        where qQ = value-below q y (proj₂ l) yQ
      exhaust-to ao af y yQ (lpass {q} {a} x r l nd) =
        lpass (fwd ao q qQ x) (cur-to ao af q q qQ r) (lane-to af a (q ++ [ ix 1 ]) y yQ l)
              (λ d → nd (done-to (AgreeTo-sym ao) (lanes-sym af) y yQ d))
        where qQ = value-below q y (proj₂ l) yQ

    module BoundedJ (n : ℕ) where
      open ES.Values using (Nth; first; next)
      open ES.Bounded using (Kth; Starts; room; freed; queued; Ends; Sched; Sub; Queued; Done; BoundedT;
                             val; step; oend; opass; lane; handoff; lend; lpass)

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

      ends-to : ∀ {f f′ : A → Den B} {o o′ : EmissionSet A} → AgreeTo Q o o′ → Lanes f f′ → ∀ {i ls ls′} → LAg ls ls′
              → ∀ c → c ≼ Q → Ends n f o i ls c → Ends n f′ o′ i ls′ c
      ends-to ao af L c cQ (q , a , s , N , St , (y , sc)) =
        q , a , s , nth-to ao (starts-q st St) N , starts-to L st St , lane-to af a s c cQ (y , sc)
        where st = stem-≼ s (below s c sc cQ)

      sched-ag : ∀ {f f′ : A → Den B} {o o′ : EmissionSet A} → AgreeTo Q o o′ → Lanes f f′ → ∀ i → LAg (Sched n f o i) (Sched n f′ o′ i)
      sched-ag ao af zero    = none
      sched-ag ao af (suc i) =
        (λ c cQ → ends-to ao af (sched-ag ao af i) c cQ , ends-to (AgreeTo-sym ao) (lanes-sym af) (lag-sym (sched-ag ao af i)) c cQ)
        & sched-ag ao af i

      sub-to : ∀ {f f′ : A → Den B} {o o′ : EmissionSet A} → AgreeTo Q o o′ → Lanes f f′ → ∀ {i q s a} → Stem s → Sub n f o i q s a → Sub n f′ o′ i q s a
      sub-to ao af {i} st (N , St) = nth-to ao (starts-q st St) N , starts-to (sched-ag ao af i) st St

      queued-to : ∀ {f f′ : A → Den B} {o o′ : EmissionSet A} → AgreeTo Q o o′ → Lanes f f′ → ∀ c → c ≼ Q → Queued n f o c → Queued n f′ o′ c
      queued-to ao af c cQ (i , q , a , sb) = i , q , a , sub-to ao af (stem-at c cQ) sb

      done-to : ∀ {f f′ : A → Den B} {o o′ : EmissionSet A} → AgreeTo Q o o′ → Lanes f f′ → ∀ c → c ≼ Q → Done n f o c → Done n f′ o′ c
      done-to ao af c cQ ((c₀ , x , c₀c) , h) =
          (c₀ , fwd ao c₀ (trans≼ c₀ c c₀c cQ) x , c₀c)
        , λ {i} {q} {a} N′ qc →
            let (s , c′ , sb , (y , sc′) , c′c) = h (nth-to (AgreeTo-sym ao) (below q c qc cQ) N′) qc
                c′Q = trans≼ c′ c c′c cQ
            in s , c′ , sub-to ao af (stem-≼ s (below s c′ sc′ c′Q)) sb , lane-to af a s c′ c′Q (y , sc′) , c′c

      bounded-to : ∀ {f f′ : A → Den B} {o o′ : EmissionSet A} → AgreeTo Q o o′ → Lanes f f′ → ∀ y {e} → y ≼ Q → BoundedT n f o y e → BoundedT n f′ o′ y e
      bounded-to ao af _ yQ (val {q} x)    = val (fwd ao q (below q (q ++ [ ix 0 ]) (≺-ext q []) yQ) x)
      bounded-to ao af y yQ (step x)       = step (fwd ao y yQ x)
      bounded-to ao af y yQ (oend x d)     = oend (fwd ao y yQ x) (done-to ao af y yQ d)
      bounded-to ao af y yQ (opass x nd)   = opass (fwd ao y yQ x) (λ d → nd (done-to (AgreeTo-sym ao) (lanes-sym af) y yQ d))
      bounded-to ao af y yQ (lane {s = s} {a = a} sb (x , sy) w) =
        lane (sub-to ao af (stem-≼ s (below s y sy yQ)) sb) (lane-to af a s y yQ (x , sy)) w
      bounded-to ao af _ yQ (handoff {s = s} {a = a} {c = c} sb (x , sc) qd) =
        handoff (sub-to ao af (stem-≼ s (below s c sc cQ)) sb) (lane-to af a s c cQ (x , sc)) (queued-to ao af c cQ qd)
        where cQ = below c (c ++ [ ix 0 ]) (≺-ext c []) yQ
      bounded-to ao af y yQ (lend {s = s} {a = a} sb (x , sy) nq d) =
        lend (sub-to ao af (stem-≼ s (below s y sy yQ)) sb) (lane-to af a s y yQ (x , sy))
             (λ q′ → nq (queued-to (AgreeTo-sym ao) (lanes-sym af) y yQ q′)) (done-to ao af y yQ d)
      bounded-to ao af y yQ (lpass {s = s} {a = a} sb (x , sy) nq nd) =
        lpass (sub-to ao af (stem-≼ s (below s y sy yQ)) sb) (lane-to af a s y yQ (x , sy))
              (λ q′ → nq (queued-to (AgreeTo-sym ao) (lanes-sym af) y yQ q′)) (λ d → nd (done-to (AgreeTo-sym ao) (lanes-sym af) y yQ d))

flatMap-causal : ∀ {A B q} (op : FlatOp) {f f′ : A → Den B} {s s′ : Den A}
               → s ~⟨ q ⟩ s′ → (∀ a → f a ~⟨ q ⟩ f′ a) → flatMapᵀ op f s ~⟨ q ⟩ flatMapᵀ op f′ s′
flatMap-causal {q = q} (mergeᶠ nothing) as af = ~-cold λ p →
  ⟨ (λ {y} yq → Join.MergeJ.merge-to q (as p) (Join.lanes af) y yq , Join.MergeJ.merge-to q (AgreeTo-sym (as p)) (Join.lanes-sym q (Join.lanes af)) y yq) ⟩
flatMap-causal {q = q} (mergeᶠ (just n)) as af = ~-cold λ p →
  ⟨ (λ {y} yq → Join.BoundedJ.bounded-to q n (as p) (Join.lanes af) y yq , Join.BoundedJ.bounded-to q n (AgreeTo-sym (as p)) (Join.lanes-sym q (Join.lanes af)) y yq) ⟩
flatMap-causal {q = q} switchᶠ {f} {f′} as af = ~-cold λ p →
  ⟨ (λ {y} yq → Join.SwitchJ.switch-to q f f′ (as p) (Join.lanes af) y yq , Join.SwitchJ.switch-to q f′ f (AgreeTo-sym (as p)) (Join.lanes-sym q (Join.lanes af)) y yq) ⟩
flatMap-causal {q = q} exhaustᶠ as af = ~-cold λ p →
  ⟨ (λ {y} yq → Join.ExhaustJ.exhaust-to q (as p) (Join.lanes af) y yq , Join.ExhaustJ.exhaust-to q (AgreeTo-sym (as p)) (Join.lanes-sym q (Join.lanes af)) y yq) ⟩

------------------------------------------------------------------------
-- The environment

good-cons : ∀ {Γ A} {t : EmissionSet A} {ρ : DenEnv Γ} → Lawful t → GoodEnv ρ → GoodEnv (hot t ∷ ρ)
good-cons L g (here refl)          = lawful-hot L
good-cons {t = t} {ρ} L g (there i) = inv-widen {t = t} {d = lookup ρ i} (g i)

private
  ag-cons : ∀ {Γ A q} {d d′ : Den A} {ρ ρ′ : DenEnv Γ} → d ~⟨ q ⟩ d′ → EnvAg q ρ ρ′ → EnvAg q (d ∷ ρ) (d′ ∷ ρ′)
  ag-cons a e (here refl) = a
  ag-cons a e (there i)   = e i

------------------------------------------------------------------------
-- By structure

-- THE INVARIANT HOLDS of every approximant and of the meaning.
inv-approx : ∀ {Γ A} n (o : Obs Timeline Γ A) (ρ : DenEnv Γ) → GoodEnv ρ → InvD (Hots ρ) (approxᵀ n o ρ)
inv-approx n       (cold c)          ρ g = cold-inv c
inv-approx n       empty             ρ g = empty-inv
inv-approx n       (of xs)           ρ g = of-inv xs
inv-approx n       (map f s)         ρ g = map-inv f {approxᵀ n s ρ} (inv-approx n s ρ g)
inv-approx n       (scan f z s)      ρ g = scan-inv f z {approxᵀ n s ρ} (inv-approx n s ρ g)
inv-approx n       (takeWhile i k s) ρ g = takeWhile-inv i k {approxᵀ n s ρ} (inv-approx n s ρ g)
inv-approx n       (flatMap op f s)  ρ g = flatMap-inv op (inv-approx n s ρ g) λ a → inv-approx n (f a) ρ g
inv-approx n       (connect s b)     ρ g = connect-inv (inv-approx n s ρ g) λ {t} L → inv-approx n b (hot t ∷ ρ) (good-cons L g)
inv-approx n       (connected i)     ρ g = g i
inv-approx zero    (defer l)         ρ g = spin-inv
inv-approx (suc n) (defer l)         ρ g = defer-inv (inv-approx n (Later.force l) ρ g)

inv-⟦⟧ : ∀ {Γ A} (o : Obs Timeline Γ A) (ρ : DenEnv Γ) → GoodEnv ρ → InvD (Hots ρ) (⟦ o ⟧ᵀ ρ)
inv-⟦⟧ (cold c)          ρ g = cold-inv c
inv-⟦⟧ empty             ρ g = empty-inv
inv-⟦⟧ (of xs)           ρ g = of-inv xs
inv-⟦⟧ (map f s)         ρ g = map-inv f {⟦ s ⟧ᵀ ρ} (inv-⟦⟧ s ρ g)
inv-⟦⟧ (scan f z s)      ρ g = scan-inv f z {⟦ s ⟧ᵀ ρ} (inv-⟦⟧ s ρ g)
inv-⟦⟧ (takeWhile i k s) ρ g = takeWhile-inv i k {⟦ s ⟧ᵀ ρ} (inv-⟦⟧ s ρ g)
inv-⟦⟧ (flatMap op f s)  ρ g = flatMap-inv op (inv-⟦⟧ s ρ g) λ a → inv-⟦⟧ (f a) ρ g
inv-⟦⟧ (connect s b)     ρ g = connect-inv (inv-⟦⟧ s ρ g) λ {t} L → inv-⟦⟧ b (hot t ∷ ρ) (good-cons L g)
inv-⟦⟧ (connected i)     ρ g = g i
inv-⟦⟧ (defer l)         ρ g = lim-inv {c = λ n → approxᵀ n (defer l) ρ} λ n → inv-approx n (defer l) ρ g

-- EVERY APPROXIMANT AND THE MEANING ARE CAUSAL in the environment.
causal-approx : ∀ {Γ A q} n (o : Obs Timeline Γ A) {ρ ρ′ : DenEnv Γ} → EnvAg q ρ ρ′ → approxᵀ n o ρ ~⟨ q ⟩ approxᵀ n o ρ′
causal-approx n       (cold c)          e = ~-refl (coldᵀ c)
causal-approx n       empty             e = ~-refl emptyᵀ
causal-approx n       (of xs)           e = ~-refl (ofᵀ xs)
causal-approx n       (map f s)         {ρ} {ρ′} e = map-causal f {approxᵀ n s ρ} {approxᵀ n s ρ′} (causal-approx n s e)
causal-approx n       (scan f z s)      {ρ} {ρ′} e = scan-causal f z {approxᵀ n s ρ} {approxᵀ n s ρ′} (causal-approx n s e)
causal-approx n       (takeWhile i k s) {ρ} {ρ′} e = takeWhile-causal i k {approxᵀ n s ρ} {approxᵀ n s ρ′} (causal-approx n s e)
causal-approx n       (flatMap op f s)  e = flatMap-causal op (causal-approx n s e) λ a → causal-approx n (f a) e
causal-approx n       (connect s b)     e = connect-causal (causal-approx n s e) λ a → causal-approx n b (ag-cons (hot-causal a) e)
causal-approx n       (connected i)     e = e i
causal-approx zero    (defer l)         e = ~-refl ⊥ᵀ
causal-approx (suc n) (defer l)         e = defer-causal (causal-approx n (Later.force l) e)

causal-⟦⟧ : ∀ {Γ A q} (o : Obs Timeline Γ A) {ρ ρ′ : DenEnv Γ} → EnvAg q ρ ρ′ → ⟦ o ⟧ᵀ ρ ~⟨ q ⟩ ⟦ o ⟧ᵀ ρ′
causal-⟦⟧ (cold c)          e = ~-refl (coldᵀ c)
causal-⟦⟧ empty             e = ~-refl emptyᵀ
causal-⟦⟧ (of xs)           e = ~-refl (ofᵀ xs)
causal-⟦⟧ (map f s)         {ρ} {ρ′} e = map-causal f {⟦ s ⟧ᵀ ρ} {⟦ s ⟧ᵀ ρ′} (causal-⟦⟧ s e)
causal-⟦⟧ (scan f z s)      {ρ} {ρ′} e = scan-causal f z {⟦ s ⟧ᵀ ρ} {⟦ s ⟧ᵀ ρ′} (causal-⟦⟧ s e)
causal-⟦⟧ (takeWhile i k s) {ρ} {ρ′} e = takeWhile-causal i k {⟦ s ⟧ᵀ ρ} {⟦ s ⟧ᵀ ρ′} (causal-⟦⟧ s e)
causal-⟦⟧ (flatMap op f s)  e = flatMap-causal op (causal-⟦⟧ s e) λ a → causal-⟦⟧ (f a) e
causal-⟦⟧ (connect s b)     e = connect-causal (causal-⟦⟧ s e) λ a → causal-⟦⟧ b (ag-cons (hot-causal a) e)
causal-⟦⟧ (connected i)     e = e i
causal-⟦⟧ (defer l) {ρ} {ρ′} e = lim-causal {c = λ n → approxᵀ n (defer l) ρ} {c′ = λ n → approxᵀ n (defer l) ρ′} λ n → causal-approx n (defer l) e

private
  same-env : ∀ {Γ q} (ρ : DenEnv Γ) → EnvAg q ρ ρ
  same-env ρ i = ~-refl (lookup ρ i)

  causal-at : ∀ {Γ A B} n (b : Obs Timeline (A ∷ Γ) B) (ρ : DenEnv Γ) → Causal (λ h → approxᵀ n b (h ∷ ρ))
  causal-at n b ρ a = causal-approx n b (ag-cons (hot-causal a) (same-env ρ))

  causal-in : ∀ {Γ A B} (b : Obs Timeline (A ∷ Γ) B) (ρ : DenEnv Γ) → Causal (λ h → ⟦ b ⟧ᵀ (h ∷ ρ))
  causal-in b ρ a = causal-⟦⟧ b (ag-cons (hot-causal a) (same-env ρ))

------------------------------------------------------------------------
-- The approximants

-- THE RECURSION SETTLES: each approximant is within its index of the
-- next.  The first unfolding replaces the spin by the guard, the body
-- lying after it; each later one is the last, one level down.
settle : ∀ {Γ A} n (o : Obs Timeline Γ A) (ρ : DenEnv Γ) → GoodEnv ρ → approxᵀ n o ρ ≈⟨ Ok (Hots ρ) ∣ n ⟩ approxᵀ (suc n) o ρ
settle n       (cold c)          ρ g = ≈-refl (coldᵀ c)
settle n       empty             ρ g = ≈-refl emptyᵀ
settle n       (of xs)           ρ g = ≈-refl (ofᵀ xs)
settle n       (map f s)         ρ g = map-ne f {approxᵀ n s ρ} {approxᵀ (suc n) s ρ} (settle n s ρ g)
settle n       (scan f z s)      ρ g = scan-ne f z {approxᵀ n s ρ} {approxᵀ (suc n) s ρ} (settle n s ρ g)
settle n       (takeWhile i k s) ρ g = takeWhile-ne i k {approxᵀ n s ρ} {approxᵀ (suc n) s ρ} (inv-approx n s ρ g) (inv-approx (suc n) s ρ g) (settle n s ρ g)
settle n       (flatMap op f s)  ρ g =
  flatMap-ne op (inv-approx n s ρ g) (inv-approx (suc n) s ρ g) (λ a → inv-approx n (f a) ρ g) (λ a → inv-approx (suc n) (f a) ρ g)
    (settle n s ρ g) λ a → settle n (f a) ρ g
settle n       (connect s b)     ρ g =
  connect-ne (inv-approx n s ρ g) (inv-approx (suc n) s ρ g)
    (λ {t} L → inv-approx n b (hot t ∷ ρ) (good-cons L g)) (λ {t} L → inv-approx (suc n) b (hot t ∷ ρ) (good-cons L g))
    (causal-at n b ρ) (causal-at (suc n) b ρ)
    (settle n s ρ g) λ {t} L → settle n b (hot t ∷ ρ) (good-cons L g)
settle n       (connected i)     ρ g = ≈-refl (lookup ρ i)
settle zero    (defer l)         ρ g = unfold₀ after
  where
    after : ∀ p → Ok (Hots ρ) p → ∀ {y e} → enter (approxᵀ zero (Later.force l) ρ) (p ++ [ ix 1 ]) y e → (p ++ [ ix 0 ]) ≺ y
    after p ok {y} x = ≺-trans {p ++ [ ix 0 ]} {p ++ [ ix 1 ]} {y} (ticks p 0)
      (world-after (InvAt.world I x) (InvAt.real I x))
      where I = inv-approx zero (Later.force l) ρ g (p ++ [ ix 1 ]) (ok-step p ok)
settle (suc n) (defer l)         ρ g = contract ok-step (settle n (Later.force l) ρ g)

-- THE MEANING IS WITHIN EVERY INDEX of its approximant: the limit of a
-- chain settling as above.
from : ∀ {Γ A} k (o : Obs Timeline Γ A) (ρ : DenEnv Γ) → GoodEnv ρ → ⟦ o ⟧ᵀ ρ ≈⟨ Ok (Hots ρ) ∣ k ⟩ approxᵀ k o ρ
from k (cold c)          ρ g = ≈-refl (coldᵀ c)
from k empty             ρ g = ≈-refl emptyᵀ
from k (of xs)           ρ g = ≈-refl (ofᵀ xs)
from k (map f s)         ρ g = map-ne f {⟦ s ⟧ᵀ ρ} {approxᵀ k s ρ} (from k s ρ g)
from k (scan f z s)      ρ g = scan-ne f z {⟦ s ⟧ᵀ ρ} {approxᵀ k s ρ} (from k s ρ g)
from k (takeWhile i p s) ρ g = takeWhile-ne i p {⟦ s ⟧ᵀ ρ} {approxᵀ k s ρ} (inv-⟦⟧ s ρ g) (inv-approx k s ρ g) (from k s ρ g)
from k (flatMap op f s)  ρ g =
  flatMap-ne op (inv-⟦⟧ s ρ g) (inv-approx k s ρ g) (λ a → inv-⟦⟧ (f a) ρ g) (λ a → inv-approx k (f a) ρ g)
    (from k s ρ g) λ a → from k (f a) ρ g
from k (connect s b)     ρ g =
  connect-ne (inv-⟦⟧ s ρ g) (inv-approx k s ρ g)
    (λ {t} L → inv-⟦⟧ b (hot t ∷ ρ) (good-cons L g)) (λ {t} L → inv-approx k b (hot t ∷ ρ) (good-cons L g))
    (causal-in b ρ) (causal-at k b ρ)
    (from k s ρ g) λ {t} L → from k b (hot t ∷ ρ) (good-cons L g)
from k (connected i)     ρ g = ≈-refl (lookup ρ i)
from k (defer l)         ρ g =
  ≈-sym {R = Ok (Hots ρ)} {k} {approxᵀ k (defer l) ρ} {⟦ defer l ⟧ᵀ ρ} (limit {c = λ n → approxᵀ n (defer l) ρ} (λ n → settle n (defer l) ρ g) k)

-- THE UNFOLDING: a `defer` agrees at every bound with its body unfolded
-- once, through the approximant one past the bound.
defer-lim : ∀ {Γ A} (l : Later Timeline Γ A) (ρ : DenEnv Γ) → GoodEnv ρ
          → Same (Ok (Hots ρ)) (⟦ defer l ⟧ᵀ ρ) (deferᵀ (⟦ Later.force l ⟧ᵀ ρ))
defer-lim l ρ g = agree-all {R = Ok (Hots ρ)} {⟦ defer l ⟧ᵀ ρ} {deferᵀ b} λ k →
  ≈-mono {R = Ok (Hots ρ)} {k} {suc k} {⟦ defer l ⟧ᵀ ρ} {deferᵀ b} (n≤1+n k)
    (≈-trans {R = Ok (Hots ρ)} {suc k} {⟦ defer l ⟧ᵀ ρ} {deferᵀ (approxᵀ k (Later.force l) ρ)} {deferᵀ b}
      (from (suc k) (defer l) ρ g)
      (contract {R = Ok (Hots ρ)} {k} {approxᵀ k (Later.force l) ρ} {b} ok-step
        (≈-sym {R = Ok (Hots ρ)} {k} {b} {approxᵀ k (Later.force l) ρ} (from k (Later.force l) ρ g))))
  where b = ⟦ Later.force l ⟧ᵀ ρ

-- THE MEANING IS COMPOSITIONAL.
compositionalᵀ : Compositionalᵀ
compositionalᵀ = record
  { coldᶜ      = λ c ρ → ≅-refl (coldᵀ c)
  ; emptyᶜ     = λ ρ → ≅-refl emptyᵀ
  ; ofᶜ        = λ xs ρ → ≅-refl (ofᵀ xs)
  ; mapᶜ       = λ f s ρ → ≅-refl (mapᵀ f (⟦ s ⟧ᵀ ρ))
  ; scanᶜ      = λ f z s ρ → ≅-refl (scanᵀ f z (⟦ s ⟧ᵀ ρ))
  ; takeWhileᶜ = λ i k s ρ → ≅-refl (takeWhileᵀ i k (⟦ s ⟧ᵀ ρ))
  ; flatMapᶜ   = λ op f s ρ → ≅-refl (flatMapᵀ op (λ a → ⟦ f a ⟧ᵀ ρ) (⟦ s ⟧ᵀ ρ))
  ; connectᶜ   = λ s b ρ → ≅-refl (connectᵀ (⟦ s ⟧ᵀ ρ) (λ h → ⟦ b ⟧ᵀ (h ∷ ρ)))
  ; connectedᶜ = λ i ρ → ≅-refl (lookup ρ i)
  ; deferᶜ     = defer-lim
  }

-- MAP FUSES: `map (f ∘ g)` and `map f ∘ map g` have the same rows.
map-fusionᵀ : ∀ {Γ A B C} (f : B → C) (g : A → B) (s : Obs Timeline Γ A) (ρ : DenEnv Γ)
            → ⟦ map (f ∘ g) s ⟧ᵀ ρ ≅ ⟦ map f (map g s) ⟧ᵀ ρ
map-fusionᵀ f g s ρ p = fuse , split
  where
    down : ∀ {t k e} → MapT (f ∘ g) t k e → Σ (Ev _) (MapT g t k)
    down (map-out x)  = _ , map-out x
    down (map-skip x) = _ , map-skip x
    down (map-end x)  = _ , map-end x

    up : ∀ {t k e} → MapT g t k e → Σ (Ev _) (MapT (f ∘ g) t k)
    up (map-out x)  = _ , map-out x
    up (map-skip x) = _ , map-skip x
    up (map-end x)  = _ , map-end x

    across : ∀ {t k e} → MapT f (Truncate (MapT g t)) k e → Σ (Ev _) (MapT (f ∘ g) t k)
    across (map-out (map-out x , _))   = _ , map-out x
    across (map-skip (map-skip x , _)) = _ , map-skip x
    across (map-end (map-end x , _))   = _ , map-end x

    fuse : ∀ {t q e} → Truncate (MapT (f ∘ g) t) q e → Truncate (MapT f (Truncate (MapT g t))) q e
    fuse (map-out x , F)  = map-out (map-out x , few-via up F) , few-via across F
    fuse (map-skip x , F) = map-skip (map-skip x , few-via up F) , few-via across F
    fuse (map-end x , F)  = map-end (map-end x , few-via up F) , few-via across F

    split : ∀ {t q e} → Truncate (MapT f (Truncate (MapT g t))) q e → Truncate (MapT (f ∘ g) t) q e
    split (map-out (map-out x , G) , _)   = map-out x , few-via down G
    split (map-skip (map-skip x , G) , _) = map-skip x , few-via down G
    split (map-end (map-end x , G) , _)   = map-end x , few-via down G
