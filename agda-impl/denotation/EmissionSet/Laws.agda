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

open import Data.Bool using (Bool)
open import Data.List using (List; _∷_; _++_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (_∷_; lookup)
open import Data.Nat using (zero; suc)
open import Data.Nat.Properties using (n≤1+n)
open import Data.Product using (Σ; _×_; _,_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (refl)

open import Tree using (Obs; Later; FlatOp; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.MonotonicList.Events using (Timeline; Pos; ix)
open import denotation.EmissionSet
  using (Ev; EmissionSet; _≺_; Truncate; Den; hot; enter; DenEnv; approxᵀ; ⟦_⟧ᵀ; coldᵀ; emptyᵀ; ofᵀ; mapᵀ; scanᵀ; takeWhileᵀ; flatMapᵀ; connectᵀ; deferᵀ; ⊥ᵀ;
         MapT; map-out; map-skip; map-end)
open import denotation.EmissionSet.Laws.Modulus
  using (≺-trans; few-via; AgreeTo; _≈⟨_∣_⟩_; ≈-refl; ≈-sym; ≈-trans; ≈-mono; Same; agree-all; LimD; limit; ticks; contract; unfold₀; _~⟨_⟩_; ~-refl)
open import denotation.EmissionSet.Laws.Worlds using (Ok; _⊕_; Lawful; InvAt; InvD; Hots; GoodEnv; W; Real)

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

-- A body reads its hot no further than the hot has run.
Causal : ∀ {A B} → (Den A → Den B) → Set₁
Causal F = ∀ {q t t′} → AgreeTo q t t′ → F (hot t) ~⟨ q ⟩ F (hot t′)

-- Every handle alike at and below `q`.
EnvAg : ∀ {Γ} → Pos → DenEnv Γ → DenEnv Γ → Set₁
EnvAg {Γ} q ρ ρ′ = ∀ {A} (i : A ∈ Γ) → lookup ρ i ~⟨ q ⟩ lookup ρ′ i

------------------------------------------------------------------------
-- Leaves

postulate
  -- EACH OPERATOR KEEPS THE MODULUS at admissible subscriptions.
  map-ne       : ∀ {A B R k} (f : A → B) {s s′ : Den A} → s ≈⟨ R ∣ k ⟩ s′ → mapᵀ f s ≈⟨ R ∣ k ⟩ mapᵀ f s′
  scan-ne      : ∀ {A B R k} (f : B → A → B) z {s s′ : Den A} → s ≈⟨ R ∣ k ⟩ s′ → scanᵀ f z s ≈⟨ R ∣ k ⟩ scanᵀ f z s′
  takeWhile-ne : ∀ {A H k} (i : Bool) (keep : A → Bool) {s s′ : Den A} → InvD H s → InvD H s′
               → s ≈⟨ Ok H ∣ k ⟩ s′ → takeWhileᵀ i keep s ≈⟨ Ok H ∣ k ⟩ takeWhileᵀ i keep s′
  -- A JOINER keeps the bound uniformly in the lane: no lane is listed.
  --
  -- DEAD ROUTE: an index per lane, the largest over the outer values that
  --   `Few` lists.  `Few` lists positions, and which value a position
  --   holds is not decidable.
  flatMap-ne   : ∀ {A B H k} (op : FlatOp) {f f′ : A → Den B} {s s′ : Den A}
               → InvD H s → InvD H s′ → (∀ a → InvD H (f a)) → (∀ a → InvD H (f′ a))
               → s ≈⟨ Ok H ∣ k ⟩ s′ → (∀ a → f a ≈⟨ Ok H ∣ k ⟩ f′ a) → flatMapᵀ op f s ≈⟨ Ok H ∣ k ⟩ flatMapᵀ op f′ s′
  connect-ne   : ∀ {A B H k} {s s′ : Den A} {F F′ : Den A → Den B}
               → InvD H s → InvD H s′
               → (∀ {t} → Lawful t → InvD (H ⊕ t) (F (hot t))) → (∀ {t} → Lawful t → InvD (H ⊕ t) (F′ (hot t)))
               → Causal F → Causal F′
               → s ≈⟨ Ok H ∣ k ⟩ s′ → (∀ {t} → Lawful t → F (hot t) ≈⟨ Ok (H ⊕ t) ∣ k ⟩ F′ (hot t))
               → connectᵀ s F ≈⟨ Ok H ∣ k ⟩ connectᵀ s′ F′

  -- EACH OPERATOR READS ITS INPUTS NO FURTHER THAN IT RUNS.
  hot-causal       : ∀ {A q} {t t′ : EmissionSet A} → AgreeTo q t t′ → hot t ~⟨ q ⟩ hot t′
  map-causal       : ∀ {A B q} (f : A → B) {s s′ : Den A} → s ~⟨ q ⟩ s′ → mapᵀ f s ~⟨ q ⟩ mapᵀ f s′
  scan-causal      : ∀ {A B q} (f : B → A → B) z {s s′ : Den A} → s ~⟨ q ⟩ s′ → scanᵀ f z s ~⟨ q ⟩ scanᵀ f z s′
  takeWhile-causal : ∀ {A q} (i : Bool) (keep : A → Bool) {s s′ : Den A} → s ~⟨ q ⟩ s′ → takeWhileᵀ i keep s ~⟨ q ⟩ takeWhileᵀ i keep s′
  flatMap-causal   : ∀ {A B q} (op : FlatOp) {f f′ : A → Den B} {s s′ : Den A}
                   → s ~⟨ q ⟩ s′ → (∀ a → f a ~⟨ q ⟩ f′ a) → flatMapᵀ op f s ~⟨ q ⟩ flatMapᵀ op f′ s′
  connect-causal   : ∀ {A B q} {s s′ : Den A} {F F′ : Den A → Den B}
                   → s ~⟨ q ⟩ s′ → (∀ {t t′} → AgreeTo q t t′ → F (hot t) ~⟨ q ⟩ F′ (hot t′)) → connectᵀ s F ~⟨ q ⟩ connectᵀ s′ F′
  defer-causal     : ∀ {A q} {s s′ : Den A} → s ~⟨ q ⟩ s′ → deferᵀ s ~⟨ q ⟩ deferᵀ s′
  lim-causal       : ∀ {A q} {c c′ : _ → Den A} → (∀ n → c n ~⟨ q ⟩ c′ n) → LimD c ~⟨ q ⟩ LimD c′

  -- EACH OPERATOR KEEPS THE INVARIANT.
  cold-inv      : ∀ {A H} (c : Timeline A) → InvD H (coldᵀ c)
  empty-inv     : ∀ {A H} → InvD H (emptyᵀ {A})
  of-inv        : ∀ {A H} (xs : List A) → InvD H (ofᵀ xs)
  spin-inv      : ∀ {A H} → InvD H (⊥ᵀ {A})
  map-inv       : ∀ {A B H} (f : A → B) {s : Den A} → InvD H s → InvD H (mapᵀ f s)
  scan-inv      : ∀ {A B H} (f : B → A → B) z {s : Den A} → InvD H s → InvD H (scanᵀ f z s)
  takeWhile-inv : ∀ {A H} (i : Bool) (keep : A → Bool) {s : Den A} → InvD H s → InvD H (takeWhileᵀ i keep s)
  flatMap-inv   : ∀ {A B H} (op : FlatOp) {f : A → Den B} {s : Den A} → InvD H s → (∀ a → InvD H (f a)) → InvD H (flatMapᵀ op f s)
  connect-inv   : ∀ {A B H} {s : Den A} {F : Den A → Den B} → InvD H s → (∀ {t} → Lawful t → InvD (H ⊕ t) (F (hot t))) → InvD H (connectᵀ s F)
  defer-inv     : ∀ {A H} {s : Den A} → InvD H s → InvD H (deferᵀ s)
  lim-inv       : ∀ {A H} {c : _ → Den A} → (∀ n → InvD H (c n)) → InvD H (LimD c)

  -- A lawful hot keeps it among its own rows; a handle keeps it under
  -- more hot rows.
  lawful-hot : ∀ {A H} {t : EmissionSet A} → Lawful t → InvD (H ⊕ t) (hot t)
  inv-widen  : ∀ {A B H} {t : EmissionSet B} {d : Den A} → InvD H d → InvD (H ⊕ t) d

  -- The world lies after the subscription.
  world-after : ∀ {H p y} → W H p y → Real y → p ≺ y

  -- A `defer`'s body is subscribed admissibly.
  ok-step : ∀ {H} p → Ok H p → Ok H (p ++ [ ix 1 ])

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
