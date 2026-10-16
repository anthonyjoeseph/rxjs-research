{-# OPTIONS --guardedness #-}

-- UNSUB: an unsubscribe run on the machine.  A switch's cut reads its
-- attachment and cancels what is stashed there, a flatMap's reads its
-- lanes and cuts each, so the run writes exactly what `torn` writes, and
-- silently: no step of it allocates, emits, or hands the driver the turn.
--
-- An act is run against a CHAIN of what follows it, `m >>ᴬ x₁ >>ᴬ …`
-- nested to the left, so every bind unfolds by definition; what is left
-- once the act is done is the chain's tail, up to `_≗_` and the weakening
-- by nothing that a read hands its continuation.
module adequacy.Unsub where

open import Data.List using (List; []; _∷_; _++_; length; map)
open import Data.List.Properties using (∷-injectiveˡ; ∷-injectiveʳ; ++-identityʳ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false)
open import Data.Empty using (⊥-elim)
open import Level using (Lift; lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (lookup to lookupᴬ; tail to tailᴬ)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁻ to all-++⁻)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Any.Properties using (++⁺ˡ; ++⁺ʳ)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴸ_)

open import denotation.MonotonicList using (Timeline)
open import operation.AbstractObservable using (module Heap; module Run; base; ref; sink; quiet; list; maybe; _⊗_; joins) renaming (module Machine to Shared)
open import operation.PureObservable using (Pureᴾ; Out)
open import operation.Machine using (module Machine)
open import adequacy.Strong using (module Strongly)
open import adequacy.Moves using (module Moving)
open import adequacy.Torn using (module Tearing)

module Unsubbing (R : Set) where
  open Heap using (World; Quiet; _⊑_; same; grow; _⨾_)
  open Shared Timeline (Out R) using (Heapᴹ; Stack; ⟨_,_,_⟩; run; push; rest; store; look)
  open Machine R using (Mach; mach; step; silent)
  open Run (Pureᴾ R) using (Act; done; newRef; readRef; writeRef; register; send; finish; startCold; stop; stash; cancel; eff; under; diverge;
    unfold; wkAct; _>>=ᴬ_; _>>ᴬ_; El; wkEl; Env; wkEnv; Observer; module Kit; module FlatKit) renaming (here to hereᴬ)
  open Strongly R
  open Moving R using (pairs-r; pairs-split)
  open Tearing R

  ----------------------------------------------------------------------
  -- `m` runs silently to `m′`

  data _⇝_ (m : Mach) : Mach → Set₁ where
    now  : m ⇝ m
    then : ∀ {m₁ m′} → step m ≡ silent m₁ → m₁ ⇝ m′ → m ⇝ m′

  ⇝-trans : ∀ {m m₁ m₂} → m ⇝ m₁ → m₁ ⇝ m₂ → m ⇝ m₂
  ⇝-trans now          q = q
  ⇝-trans (then e p)   q = then e (⇝-trans p q)

  ----------------------------------------------------------------------
  -- `_≗_` composes, binds, weakens, and weakening by nothing is nothing

  ≗-trans : ∀ {w B} {m₁ m₂ m₃ : Act w B} → m₁ ≗ m₂ → m₂ ≗ m₃ → m₁ ≗ m₃
  ≗-trans (done≗ refl)            (done≗ refl)              = done≗ refl
  ≗-trans (newRef≗ refl f)        (newRef≗ refl g)          = newRef≗ refl λ σ r → ≗-trans (f σ r) (g σ r)
  ≗-trans (readRef≗ refl f)       (readRef≗ refl g)         = readRef≗ refl λ σ x → ≗-trans (f σ x) (g σ x)
  ≗-trans (writeRef≗ refl refl e) (writeRef≗ refl refl e′)  = writeRef≗ refl refl (≗-trans e e′)
  ≗-trans (register≗ n c x k)     (register≗ n′ c′ x′ k′)   =
    register≗ (λ a → ≗-trans (n a) (n′ a)) (≗-trans c c′) (≗-trans x x′) λ σ s → ≗-trans (k σ s) (k′ σ s)
  ≗-trans (send≗ refl e)          (send≗ refl e′)           = send≗ refl (≗-trans e e′)
  ≗-trans (finish≗ refl e)        (finish≗ refl e′)         = finish≗ refl (≗-trans e e′)
  ≗-trans (startCold≗ refl f)     (startCold≗ refl g)       = startCold≗ refl λ σ h → ≗-trans (f σ h) (g σ h)
  ≗-trans (stop≗ refl e)          (stop≗ refl e′)           = stop≗ refl (≗-trans e e′)
  ≗-trans (stash≗ m f)            (stash≗ m′ g)             = stash≗ (≗-trans m m′) λ σ q → ≗-trans (f σ q) (g σ q)
  ≗-trans (cancel≗ refl e)        (cancel≗ refl e′)         = cancel≗ refl (≗-trans e e′)
  ≗-trans (eff≗ f)                (eff≗ g)                  = eff≗ λ a → ≗-trans (f a) (g a)
  ≗-trans (here≗ f)               (here≗ g)                 = here≗ λ p → ≗-trans (f p) (g p)
  ≗-trans (under≗ m k)            (under≗ m′ k′)            = under≗ (≗-trans m m′) (≗-trans k k′)
  ≗-trans diverge≗                diverge≗                  = diverge≗
  ≗-trans (unfold≗ refl n c x k m) (unfold≗ refl n′ c′ x′ k′ m′) =
    unfold≗ refl (λ a → ≗-trans (n a) (n′ a)) (≗-trans c c′) (≗-trans x x′) (λ σ q → ≗-trans (k σ q) (k′ σ q)) (≗-trans m m′)

  wk≗ : ∀ {w v B} (ρ : w ⊑ v) {m m′ : Act w B} → m ≗ m′ → wkAct ρ m ≗ wkAct ρ m′
  wk≗ ρ (done≗ e)               = done≗ e
  wk≗ ρ (newRef≗ refl f)        = newRef≗ refl λ σ r → f (ρ ⨾ σ) r
  wk≗ ρ (readRef≗ refl f)       = readRef≗ refl λ σ x → f (ρ ⨾ σ) x
  wk≗ ρ (writeRef≗ refl refl e) = writeRef≗ refl refl (wk≗ ρ e)
  wk≗ ρ (register≗ n c x k)     = register≗ (λ a → wk≗ ρ (n a)) (wk≗ ρ c) (wk≗ ρ x) λ σ s → k (ρ ⨾ σ) s
  wk≗ ρ (send≗ refl e)          = send≗ refl (wk≗ ρ e)
  wk≗ ρ (finish≗ refl e)        = finish≗ refl (wk≗ ρ e)
  wk≗ ρ (startCold≗ refl f)     = startCold≗ refl λ σ h → f (ρ ⨾ σ) h
  wk≗ ρ (stop≗ refl e)          = stop≗ refl (wk≗ ρ e)
  wk≗ ρ (stash≗ m f)            = stash≗ (wk≗ ρ m) λ σ q → f (ρ ⨾ σ) q
  wk≗ ρ (cancel≗ refl e)        = cancel≗ refl (wk≗ ρ e)
  wk≗ ρ (eff≗ f)                = eff≗ λ a → wk≗ ρ (f a)
  wk≗ ρ (here≗ f)               = here≗ λ p → wk≗ ρ (f p)
  wk≗ ρ (under≗ m k)            = under≗ (wk≗ ρ m) (wk≗ ρ k)
  wk≗ ρ diverge≗                = diverge≗
  wk≗ ρ (unfold≗ refl n c x k m) = unfold≗ refl (λ a → wk≗ ρ (n a)) (wk≗ ρ c) (wk≗ ρ x) (λ σ q → k (ρ ⨾ σ) q) (wk≗ ρ m)

  bind≗ : ∀ {w A B} {m m′ : Act w A} {f f′ : A → Act w B} → m ≗ m′ → (∀ a → f a ≗ f′ a) → (m >>=ᴬ f) ≗ (m′ >>=ᴬ f′)
  bind≗ (done≗ refl)            g = g _
  bind≗ (newRef≗ refl k)        g = newRef≗ refl λ σ r → bind≗ (k σ r) λ x → wk≗ σ (g x)
  bind≗ (readRef≗ refl k)       g = readRef≗ refl λ σ a → bind≗ (k σ a) λ x → wk≗ σ (g x)
  bind≗ (writeRef≗ refl refl e) g = writeRef≗ refl refl (bind≗ e g)
  bind≗ (register≗ n c x k)     g = register≗ n c x λ σ s → bind≗ (k σ s) λ y → wk≗ σ (g y)
  bind≗ (send≗ refl e)          g = send≗ refl (bind≗ e g)
  bind≗ (finish≗ refl e)        g = finish≗ refl (bind≗ e g)
  bind≗ (startCold≗ refl k)     g = startCold≗ refl λ σ h → bind≗ (k σ h) λ x → wk≗ σ (g x)
  bind≗ (stop≗ refl e)          g = stop≗ refl (bind≗ e g)
  bind≗ (stash≗ m k)            g = stash≗ m λ σ q → bind≗ (k σ q) λ x → wk≗ σ (g x)
  bind≗ (cancel≗ refl e)        g = cancel≗ refl (bind≗ e g)
  bind≗ (eff≗ k)                g = eff≗ λ a → bind≗ (k a) g
  bind≗ (here≗ k)               g = here≗ λ p → bind≗ (k p) g
  bind≗ (under≗ m k)            g = under≗ m (bind≗ k g)
  bind≗ diverge≗                g = diverge≗
  bind≗ (unfold≗ refl n c x k m) g = unfold≗ refl n c x k (bind≗ m g)

  same-⨾ : ∀ {u w} (σ : u ⊑ w) → same ⨾ σ ≡ σ
  same-⨾ same     = refl
  same-⨾ (grow σ) = cong grow (same-⨾ σ)

  wkEl-same : ∀ {w} t (x : El w t) → wkEl t same x ≡ x
  wkEl-same (base X)  x              = refl
  wkEl-same (ref t)   r              = refl
  wkEl-same (sink A)  s              = refl
  wkEl-same quiet     q              = refl
  wkEl-same (list t)  []             = refl
  wkEl-same (list t)  (x ∷ xs)       = cong₂ _∷_ (wkEl-same t x) (wkEl-same (list t) xs)
  wkEl-same (maybe t) nothing        = refl
  wkEl-same (maybe t) (just x)       = cong just (wkEl-same t x)
  wkEl-same (s ⊗ t)   (x , y)        = cong₂ _,_ (wkEl-same s x) (wkEl-same t y)
  wkEl-same (joins A) []             = refl
  wkEl-same (joins A) ((s , j) ∷ xs) = cong ((s , j) ∷_) (wkEl-same (joins A) xs)

  wkEnv-same : ∀ {Γ w} (e : Env Γ w) → wkEnv same e ≡ e
  wkEnv-same []         = refl
  wkEnv-same (st ∷ sts) = cong (st ∷_) (wkEnv-same sts)

  -- A continuation reached by no growth, as it was.
  from-same : ∀ {w v B} (F : w ⊑ v → Act v B) (σ : w ⊑ v) → F (same ⨾ σ) ≗ F σ
  from-same F σ = subst (λ τ → F τ ≗ F σ) (sym (same-⨾ σ)) (≗-refl (F σ))

  wk-same : ∀ {w B} (m : Act w B) → wkAct same m ≗ m
  wk-same (done b)                 = done≗ refl
  wk-same (newRef t a k)           = newRef≗ (wkEl-same t a) λ σ r → from-same (λ τ → k τ r) σ
  wk-same (readRef r k)            = readRef≗ refl λ σ x → from-same (λ τ → k τ x) σ
  wk-same (writeRef {t = t} r a k) = writeRef≗ refl (wkEl-same t a) (wk-same k)
  wk-same (register n c x k)       = register≗ (λ a → wk-same (n a)) (wk-same c) (wk-same x) λ σ s → from-same (λ τ → k τ s) σ
  wk-same (send s a k)             = send≗ refl (wk-same k)
  wk-same (finish s k)             = finish≗ refl (wk-same k)
  wk-same (startCold c s k)        = startCold≗ refl λ σ h → from-same (λ τ → k τ h) σ
  wk-same (stop h k)               = stop≗ refl (wk-same k)
  wk-same (stash m k)              = stash≗ (wk-same m) λ σ q → from-same (λ τ → k τ q) σ
  wk-same (cancel t k)             = cancel≗ refl (wk-same k)
  wk-same (eff e k)                = eff≗ λ a → wk-same (k a)
  wk-same (hereᴬ k)                = here≗ λ p → wk-same (k p)
  wk-same (under l m k)            = under≗ (wk-same m) (wk-same k)
  wk-same diverge                  = diverge≗
  wk-same (unfold l e n c x k m)   = unfold≗ (wkEnv-same e) (λ a → wk-same (n a)) (wk-same c) (wk-same x) (λ σ q → from-same (λ τ → k τ q) σ) (wk-same m)

  ----------------------------------------------------------------------
  -- An act against what follows it

  chainᴬ : ∀ {h} → Act h ⊤ → List (Act h ⊤) → Act h ⊤
  chainᴬ m []       = m
  chainᴬ m (x ∷ xs) = chainᴬ (m >>ᴬ x) xs

  -- What follows once the act is done.
  afterᴬ : ∀ {h} → List (Act h ⊤) → Act h ⊤
  afterᴬ []       = done tt
  afterᴬ (x ∷ xs) = chainᴬ x xs

  chain-done : ∀ {h} (xs : List (Act h ⊤)) → chainᴬ (done tt) xs ≡ afterᴬ xs
  chain-done []       = refl
  chain-done (x ∷ xs) = refl

  chain-write : ∀ {h t} {r : El h (ref t)} {a : El h t} {k : Act h ⊤} xs → chainᴬ (writeRef r a k) xs ≡ writeRef r a (chainᴬ k xs)
  chain-write []       = refl
  chain-write (x ∷ xs) = chain-write xs

  chain-read : ∀ {h t} {r : El h (ref t)} {k : ∀ {v} → h ⊑ v → El v t → Act v ⊤} xs
             → chainᴬ (readRef r k) xs ≡ readRef r λ σ a → chainᴬ (k σ a) (map (wkAct σ) xs)
  chain-read []       = refl
  chain-read (x ∷ xs) = chain-read xs

  chain-stop : ∀ {h} {hd} {k : Act h ⊤} xs → chainᴬ (stop hd k) xs ≡ stop hd (chainᴬ k xs)
  chain-stop []       = refl
  chain-stop (x ∷ xs) = chain-stop xs

  chain-cancel : ∀ {h} {q} {k : Act h ⊤} xs → chainᴬ (cancel q k) xs ≡ cancel q (chainᴬ k xs)
  chain-cancel []       = refl
  chain-cancel (x ∷ xs) = chain-cancel xs

  chain≗ : ∀ {h} {m m′ : Act h ⊤} → m ≗ m′ → ∀ xs → chainᴬ m (map (wkAct same) xs) ≗ chainᴬ m′ xs
  chain≗ e []       = e
  chain≗ e (x ∷ xs) = chain≗ (bind≗ e λ _ → wk-same x) xs

  after-same : ∀ {h} (xs : List (Act h ⊤)) → afterᴬ (map (wkAct same) xs) ≗ afterᴬ xs
  after-same []       = done≗ refl
  after-same (x ∷ xs) = chain≗ (wk-same x) xs

  ----------------------------------------------------------------------
  -- Running

  -- From `a` at `H`, silently to an act like `n` at `H′`, the stack and
  -- everything else the machine holds untouched.
  Reach : ∀ {h} → Heapᴹ h → Act h ⊤ → Heapᴹ h → Act h ⊤ → Set₁
  Reach {h} H a H′ n = ∀ {p w} {σ : w ⊑ h} {K : Stack w ⊤} {clk ts bs td lg en mk}
    → Σ (Act h ⊤) λ a′ → a′ ≗ n × mach ⟨ H , p , run a σ K ⟩ clk ts bs td lg en mk ⇝ mach ⟨ H′ , p , run a′ σ K ⟩ clk ts bs td lg en mk

  -- Likewise, by at least one step.
  Reach⁺ : ∀ {h} → Heapᴹ h → Act h ⊤ → Heapᴹ h → Act h ⊤ → Set₁
  Reach⁺ {h} H a H′ n = ∀ {p w} {σ : w ⊑ h} {K : Stack w ⊤} {clk ts bs td lg en mk}
    → Σ (Act h ⊤) λ a′ → a′ ≗ n × Σ Mach λ m₁ → step (mach ⟨ H , p , run a σ K ⟩ clk ts bs td lg en mk) ≡ silent m₁
    × m₁ ⇝ mach ⟨ H′ , p , run a′ σ K ⟩ clk ts bs td lg en mk

  -- `m` run from `H` leaves `H′`, whatever follows it.
  Runs : ∀ {h} → Heapᴹ h → Act h ⊤ → Heapᴹ h → Set₁
  Runs H m H′ = ∀ xs {a} → a ≗ chainᴬ m xs → Reach H a H′ (afterᴬ xs)

  Runs⁺ : ∀ {h} → Heapᴹ h → Act h ⊤ → Heapᴹ h → Set₁
  Runs⁺ H m H′ = ∀ xs {a} → a ≗ chainᴬ m xs → Reach⁺ H a H′ (afterᴬ xs)

  runs⁺ : ∀ {h} {H H′ : Heapᴹ h} {m} → Runs⁺ H m H′ → Runs H m H′
  runs⁺ r xs e {p} {w} {σ} {K} {clk} {ts} {bs} {td} {lg} {en} {mk} with r xs e {p} {w} {σ} {K} {clk} {ts} {bs} {td} {lg} {en} {mk}
  ... | a′ , e′ , m₁ , st , path = a′ , e′ , then st path

  run-done : ∀ {h} {H : Heapᴹ h} → Runs H (done tt) H
  run-done xs {a} e = a , subst (a ≗_) (chain-done xs) e , now

  run-seq : ∀ {h} {H H₁ H₂ : Heapᴹ h} {m₁ m₂} → Runs H m₁ H₁ → Runs H₁ m₂ H₂ → Runs H (m₁ >>ᴬ m₂) H₂
  run-seq {m₂ = m₂} r₁ r₂ xs e {p} {w} {σ} {K} {clk} {ts} {bs} {td} {lg} {en} {mk} with r₁ (m₂ ∷ xs) e {p} {w} {σ} {K} {clk} {ts} {bs} {td} {lg} {en} {mk}
  ... | a₁ , e₁ , path₁ with r₂ xs e₁ {p} {w} {σ} {K} {clk} {ts} {bs} {td} {lg} {en} {mk}
  ... | a₂ , e₂ , path₂ = a₂ , e₂ , ⇝-trans path₁ path₂

  private
    write-at : ∀ {h t} {H H′ : Heapᴹ h} {r : El h (ref t)} {v : El h t} {k : Act h ⊤} xs → Runs (store H r (lift v)) k H′
             → ∀ {a} → a ≗ writeRef r v (chainᴬ k xs) → Reach⁺ H a H′ (afterᴬ xs)
    write-at xs rk (writeRef≗ refl refl e) {p} {w} {σ} {K} {clk} {ts} {bs} {td} {lg} {en} {mk} with rk xs e {p} {w} {σ} {K} {clk} {ts} {bs} {td} {lg} {en} {mk}
    ... | a′ , e′ , path = a′ , e′ , _ , refl , path

    stop-at : ∀ {h} {H H′ : Heapᴹ h} {hd} {k : Act h ⊤} xs → Runs (store H hd (lift true)) k H′
            → ∀ {a} → a ≗ stop hd (chainᴬ k xs) → Reach H a H′ (afterᴬ xs)
    stop-at xs rk (stop≗ refl e) {p} {w} {σ} {K} {clk} {ts} {bs} {td} {lg} {en} {mk} with rk xs e {p} {w} {σ} {K} {clk} {ts} {bs} {td} {lg} {en} {mk}
    ... | a′ , e′ , path = a′ , e′ , then refl path

    read-at : ∀ {h t} {H H′ : Heapᴹ h} {r : El h (ref t)} {k : ∀ {v} → h ⊑ v → El v t → Act v ⊤} xs
            → (∀ z → At.val H r ≡ z → Runs H (k same z) H′)
            → ∀ {a} → a ≗ readRef r (λ σ z → chainᴬ (k σ z) (map (wkAct σ) xs)) → Reach H a H′ (afterᴬ xs)
    read-at {H = H} {r = r} xs rk (readRef≗ refl f) {p} {w} {σ} {K} {clk} {ts} {bs} {td} {lg} {en} {mk}
      with rk (At.val H r) refl (map (wkAct same) xs) (f same (At.val H r)) {p} {w} {σ} {K} {clk} {ts} {bs} {td} {lg} {en} {mk}
    ... | a′ , e′ , path = a′ , ≗-trans e′ (after-same xs) , then refl path

    cancel-at : ∀ {h} {H H′ : Heapᴹ h} {q m} xs → look H q ≗ m → Runs H m H′
              → ∀ {a} → a ≗ cancel q (afterᴬ xs) → Reach H a H′ (afterᴬ xs)
    cancel-at {H = H} {q = q} xs st rm (cancel≗ refl e) {p} {w} {σ} {K} {clk} {ts} {bs} {td} {lg} {en} {mk}
      with rm [] st {p} {_} {same} {push (rest _) σ K} {clk} {ts} {bs} {td} {lg} {en} {mk}
    ... | .(done tt) , done≗ refl , path = _ , ≗-trans (wk-same _) e , then refl (⇝-trans path (then refl (then refl now)))

  run-write : ∀ {h t} {H H′ : Heapᴹ h} (r : El h (ref t)) (v : El h t) {k : Act h ⊤} → Runs (store H r (lift v)) k H′ → Runs⁺ H (writeRef r v k) H′
  run-write r v rk xs {a} e = write-at xs rk (subst (a ≗_) (chain-write xs) e)

  run-stop : ∀ {h} {H H′ : Heapᴹ h} hd {k : Act h ⊤} → Runs (store H hd (lift true)) k H′ → Runs H (stop hd k) H′
  run-stop hd rk xs {a} e = stop-at xs rk (subst (a ≗_) (chain-stop xs) e)

  run-read : ∀ {h t} {H H′ : Heapᴹ h} (r : El h (ref t)) {k : ∀ {v} → h ⊑ v → El v t → Act v ⊤}
           → (∀ z → At.val H r ≡ z → Runs H (k same z) H′) → Runs H (readRef r k) H′
  run-read r rk xs {a} e = read-at xs rk (subst (a ≗_) (chain-read xs) e)

  -- What is stashed at `q`, run.
  run-cancel : ∀ {h} {H H′ : Heapᴹ h} {q m} → look H q ≗ m → Runs H m H′ → Runs H (cancel q (done tt)) H′
  run-cancel st rm xs {a} e = cancel-at xs st rm (subst (a ≗_) (trans (chain-cancel xs) (cong (cancel _) (chain-done xs))) e)

  ----------------------------------------------------------------------
  -- What an unsubscribe reads: each switch's attachment, each stash, and
  -- a flatMap's lanes in flight, a prefix of its lanes' switches

  cuts : ∀ {h Δ B} → List (Lane h Δ B) → List (Kit.Cut h)
  cuts []                = []
  cuts (lane c _ _ ∷ ls) = c ∷ cuts ls

  cuts-switches : ∀ {h} (H : Heapᴹ h) {Δ B} (ls : List (Lane h Δ B)) → At.switches H ls ≡ cuts ls
  cuts-switches H []                = refl
  cuts-switches H (lane c _ _ ∷ ls) = cong (c ∷_) (cuts-switches H ls)

  mutual
    Tearable : ∀ {h} → Heapᴹ h → ∀ {Δ A} → Sub h Δ A → Set₁
    Tearable H (mapˢ f s)                              = Tearable H s
    Tearable H (scanˢ f r s)                           = Tearable H s
    Tearable H (takeWhileˢ i p c k tk s)               = At.Attached H c k (unsub s) × Tearable H s
    Tearable H (flatMapˢ op f fl oc k r pl so ls)      = At.Attached H oc k (unsub so) × Tearable H so
      × Σ (List (Kit.Cut _)) (λ gone → At.val H (FlatKit.Flat.lanes fl) ++ gone ≡ cuts ls) × TearableLanes H ls
    Tearable H (connectˢ S c b kb k fd rp e rt src bd) = At.Stashed H kb (unsub bd) × Tearable H src × Tearable H bd
    Tearable H (deferˢ k s)                            = At.Stashed H k (unsub s) × Tearable H s
    Tearable H _                                       = Lift _ ⊤

    TearableLanes : ∀ {h} → Heapᴹ h → ∀ {Δ B} → List (Lane h Δ B) → Set₁
    TearableLanes H []                = Lift _ ⊤
    TearableLanes H (lane c k s ∷ ls) = At.Attached H c k (unsub s) × Tearable H s × TearableLanes H ls

  -- Every subscription against its kernel is tearable.
  mutual
    tearable : ∀ {h} {H : Heapᴹ h} {Δ A} (u : Sub h Δ A) {E o} → At.Holds H u E o → Tearable H u
    tearable (pendingˢ s q)                          _                                     = lift tt
    tearable (coldˢ s hd ph)                         _                                     = lift tt
    tearable (ofˢ p i xs)                            _                                     = lift tt
    tearable doneˢ                                   _                                     = lift tt
    tearable (mapˢ f s)                              hs                                    = tearable s hs
    tearable (scanˢ f r s)                           hs                                    = tearable s hs
    tearable (takeWhileˢ i p c k tk s)               (a , hs)                              = a , tearable s hs
    tearable {H = H} (flatMapˢ op f fl oc k r pl so ls) {E} {o} (_ , _ , a , hso , _ , (gone , eq , _) , hl) =
      a , tearable so hso , (gone , trans eq (cuts-switches H ls)) , tearableLanes {op = op} {f = f} {E = E} {o = o} {fl = fl} ls hl
    tearable (connectˢ S c b kb k fd rp e rt src bd) (_ , _ , st , hsrc , hbd)             = st , tearable src hsrc , tearable bd hbd
    tearable (joinˢ j sk l x st)                     _                                     = lift tt
    tearable (deferˢ k s)                            (st , hs)                             = st , tearable s hs

    tearableLanes : ∀ {h} {H : Heapᴹ h} {Δ A B op f E o fl} (ls : List (Lane h Δ B)) → At.HoldsLanes H {A = A} op f E o fl ls → TearableLanes H ls
    tearableLanes []                _            = lift tt
    tearableLanes {op = op} {f = f} {E = E} {o = o} {fl = fl} (lane c k s ∷ ls) (a , hs , hl) =
      a , tearable s hs , tearableLanes {op = op} {f = f} {E = E} {o = o} {fl = fl} ls hl

  -- Every subscription below a path against its kernel.
  mutual
    holds-at : ∀ {h} {H : Heapᴹ h} {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} {E o} → Path t u → At.Holds H t E o
             → Σ (Env Δ′ h) λ E′ → Σ (Observer A′ h) λ o′ → At.Holds H u E′ o′
    holds-at here          hs                          = _ , _ , hs
    holds-at (in-map π)    hs                          = holds-at π hs
    holds-at (in-scan π)   hs                          = holds-at π hs
    holds-at (in-take π)   (_ , hs)                    = holds-at π hs
    holds-at (in-outer π)  (_ , _ , _ , hso , _)       = holds-at π hso
    holds-at {t = flatMapˢ op f fl _ _ _ _ _ _} {E = E} {o = o} (in-lanes π) (_ , _ , _ , _ , _ , _ , hl) =
      holdsL-at {op = op} {f = f} {E = E} {o = o} {fl = fl} π hl
    holds-at (in-source π) (_ , _ , _ , hsrc , _)      = holds-at π hsrc
    holds-at (in-body π)   (_ , _ , _ , _ , hbd)       = holds-at π hbd
    holds-at (in-defer π)  (_ , hs)                    = holds-at π hs

    holdsL-at : ∀ {h} {H : Heapᴹ h} {Δ A B Δ′ A′ op f E o fl} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} → PathLanes ls u
              → At.HoldsLanes H {A = A} op f E o fl ls → Σ (Env Δ′ h) λ E′ → Σ (Observer A′ h) λ o′ → At.Holds H u E′ o′
    holdsL-at (this-lane π) (_ , hs , _) = holds-at π hs
    holdsL-at {op = op} {f = f} {E = E} {o = o} {fl = fl} (next-lane π) (_ , _ , hl) = holdsL-at {op = op} {f = f} {E = E} {o = o} {fl = fl} π hl

  ----------------------------------------------------------------------
  -- Tearable reads only its own names

  attached-alike : ∀ {h} {H H′ : Heapᴹ h} (c : Kit.Cut h) (k : Maybe (Quiet h)) {u}
                 → Alike H H′ (cutNames c) → Alike H H′ (quietName k) → At.Attached H c k u → At.Attached H′ c k u
  attached-alike c nothing  agc agk (lift e) = lift (trans (cong lower (agc (Kit.held c) (there (here refl)))) e)
  attached-alike c (just q) agc agk (e , st) =
    trans (cong lower (agc (Kit.held c) (there (here refl)))) e , subst (_≗ _) (sym (agk q (here refl))) st

  stashed-alike : ∀ {h} {H H′ : Heapᴹ h} (k : Maybe (Quiet h)) {u} → Alike H H′ (quietName k) → At.Stashed H k u → At.Stashed H′ k u
  stashed-alike nothing  ag st = st
  stashed-alike (just q) ag st = subst (_≗ _) (sym (ag q (here refl))) st

  mutual
    tearable-alike : ∀ {h} {H H′ : Heapᴹ h} {Δ A} (u : Sub h Δ A) → Alike H H′ (names u) → Tearable H u → Tearable H′ u
    tearable-alike (pendingˢ s q)            ag t = t
    tearable-alike (coldˢ s hd ph)           ag t = t
    tearable-alike (ofˢ p i xs)              ag t = t
    tearable-alike doneˢ                     ag t = t
    tearable-alike (mapˢ f s)                ag t = tearable-alike s ag t
    tearable-alike (scanˢ f r s)             ag t = tearable-alike s (λ j m → ag j (there m)) t
    tearable-alike (takeWhileˢ i p c k tk s) ag (a , t) =
      attached-alike c k (λ j m → ag j (++⁺ˡ m)) (λ j m → ag j (++⁺ʳ (cutNames c) (++⁺ˡ m))) a
      , tearable-alike s (λ j m → ag j (++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) m))) t
    tearable-alike (flatMapˢ op f fl oc k r pl so ls) ag (a , t , (gone , eq) , tl) =
      attached-alike oc k (λ j m → ag j (++⁺ʳ (flatNames fl) (++⁺ˡ m))) (λ j m → ag j (++⁺ʳ (flatNames fl) (++⁺ʳ (cutNames oc) (++⁺ˡ m)))) a
      , tearable-alike so (λ j m → ag j (++⁺ʳ (flatNames fl) (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ˡ m)))))) t
      , (gone , trans (cong (λ z → lower z ++ gone) (ag (FlatKit.Flat.lanes fl) (there (there (there (here refl)))))) eq)
      , tearableL-alike ls (λ j m → ag j (++⁺ʳ (flatNames fl) (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ʳ (names so) m)))))) tl
    tearable-alike (connectˢ S c b kb k fd rp e rt src bd) ag (st , ts , tb) =
      stashed-alike kb (λ j m → ag j (++⁺ʳ (subjectNames S) (++⁺ʳ (cutNames c) (there (++⁺ˡ m))))) st
      , tearable-alike src (λ j m → ag j (++⁺ʳ (subjectNames S) (++⁺ʳ (cutNames c) (there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ˡ m))))))) ts
      , tearable-alike bd (λ j m → ag j (++⁺ʳ (subjectNames S) (++⁺ʳ (cutNames c) (there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ʳ (names src) m))))))) tb
    tearable-alike (joinˢ j sk l x st)       ag t = t
    tearable-alike (deferˢ k s)              ag (st , t) =
      stashed-alike k (λ j m → ag j (++⁺ˡ m)) st , tearable-alike s (λ j m → ag j (++⁺ʳ (quietName k) m)) t

    tearableL-alike : ∀ {h} {H H′ : Heapᴹ h} {Δ B} (ls : List (Lane h Δ B)) → Alike H H′ (laneNames ls) → TearableLanes H ls → TearableLanes H′ ls
    tearableL-alike []                ag t = t
    tearableL-alike (lane c k s ∷ ls) ag (a , t , tl) =
      attached-alike c k (λ j m → ag j (++⁺ˡ m)) (λ j m → ag j (++⁺ʳ (cutNames c) (++⁺ˡ m))) a
      , tearable-alike s (λ j m → ag j (++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) (++⁺ˡ m)))) t
      , tearableL-alike ls (λ j m → ag j (++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) (++⁺ʳ (names s) m)))) tl

  ----------------------------------------------------------------------
  -- An unsubscribe runs to the heap `torn` names

  -- What a thrown switch holds, unsubscribed.
  Via : ∀ {h} → Heapᴹ h → Maybe (Quiet h) → ∀ {Δ A} → Sub h Δ A → Set₁
  Via H nothing  s = Lift _ ⊤
  Via H (just _) s = Runs H (unsub s) (torn H s)

  -- A switch cut: thrown, its attachment read, what is stashed there run.
  cut-runs : ∀ {h} {H : Heapᴹ h} (c : Kit.Cut h) (k : Maybe (Quiet h)) {Δ A} (s : Sub h Δ A) → At.Attached H c k (unsub s)
           → _≢_ {A = Name h} (_ , Kit.live c) (_ , Kit.held c) → All (_≢_ {A = Name h} (_ , Kit.live c)) (quietName k)
           → Via (store H (Kit.live c) (lift false)) k s → Runs⁺ H (Kit.cut c) (thrown H c k s)
  cut-runs {H = H} c nothing s (lift e) nlh _ _ =
    run-write (Kit.live c) false (run-read (Kit.held c) λ where
      nothing   _  → run-done
      (just q′) ez → ⊥-elim (nothing≢just (trans (sym e) (trans (sym (cong lower (look-store H (Kit.live c) (Kit.held c) nlh))) ez))))
    where nothing≢just : ∀ {X : Set} {x : X} → nothing ≢ just x
          nothing≢just ()
  cut-runs {H = H} c (just q) s (e , st) nlh (nlq ∷ []) via =
    run-write (Kit.live c) false (run-read (Kit.held c) λ where
      nothing   ez → ⊥-elim (just≢nothing (trans (sym e) (trans (sym (cong lower (look-store H (Kit.live c) (Kit.held c) nlh))) ez)))
      (just q′) ez → run-cancel (subst (λ x → look (store H (Kit.live c) (lift false)) x ≗ unsub s)
                                  (just-injective (trans (sym e) (trans (sym (cong lower (look-store H (Kit.live c) (Kit.held c) nlh))) ez)))
                                  (subst (_≗ unsub s) (sym (look-store H (Kit.live c) q nlq)) st)) via)
    where just≢nothing : ∀ {X : Set} {x : X} → just x ≢ nothing
          just≢nothing ()

  -- A switch's names, apart from what follows them.
  cut-apart : ∀ {h} (c : Kit.Cut h) (k : Maybe (Quiet h)) ns {rest} → AllPairs _≢_ (cutNames c ++ quietName k ++ ns ++ rest)
            → _≢_ {A = Name h} (_ , Kit.live c) (_ , Kit.held c) × All (_≢_ {A = Name h} (_ , Kit.live c)) (quietName k)
            × All (_≢_ {A = Name h} (_ , Kit.live c)) ns × AllPairs _≢_ ns
  cut-apart c k ns ((nlh ∷ nr) ∷ (_ ∷ ps)) with all-++⁻ (quietName k) nr
  ... | nlk , nr₂ = nlh , nlk , proj₁ (all-++⁻ ns nr₂) , proj₁ (pairs-split ns (pairs-r (quietName k) ps))

  mutual
    tears : ∀ {h} {H : Heapᴹ h} {Δ A} (u : Sub h Δ A) → Tearable H u → AllPairs _≢_ (names u) → Runs H (unsub u) (torn H u)
    tears (pendingˢ s q)            _ _        = run-done
    tears (coldˢ s hd ph)           _ _        = run-stop hd run-done
    tears (ofˢ p i xs)              _ _        = run-done
    tears doneˢ                     _ _        = run-done
    tears (mapˢ f s)                t ps       = tears s t ps
    tears (scanˢ f r s)             t (_ ∷ ps) = tears s t ps
    tears (takeWhileˢ i p c k tk s) t ps with cut-apart c k (names s) (subst (λ z → AllPairs _≢_ (cutNames c ++ quietName k ++ z)) (sym (++-identityʳ (names s))) ps)
    ... | nlh , nlk , nls , pss = runs⁺ (cut-tears c k s t nlh nlk nls pss)
    tears {H = H} (flatMapˢ op f fl oc k r pl so ls) (a , t , (gone , eq) , tl) ps with cut-apart oc k ((_ , r) ∷ names so) (pairs-r (flatNames fl) ps)
    ... | nlh , nlk , _ ∷ nls , _ ∷ pss =
      run-seq (runs⁺ (cut-tears oc k so (a , t) nlh nlk nls pss))
        (kill-tears fl ls (trans (cong (λ z → lower z ++ gone) (thrown-off H oc k so (FlatKit.Flat.lanes fl) nlo nso)) eq)
          (tearableL-alike ls (λ j m → thrown-off H oc k so j (lookupᴬ (apart-l (cutNames oc) ps₁ (inL m)) (here refl))
                                                         (apart-l (names so) psL m)) tl)
          (pairs-r (names so) psL) λ m → apart-l (flatNames fl) ps (++⁺ʳ (cutNames oc) (inL m)))
      where
        ps₁  = pairs-r (flatNames fl) ps
        psL = pairs-r ((_ , r) ∷ []) (pairs-r (quietName k) (pairs-r (cutNames oc) ps₁))
        inL : ∀ {n} → n ∈ᴸ laneNames ls → n ∈ᴸ quietName k ++ (_ , r) ∷ names so ++ laneNames ls
        inL m = ++⁺ʳ (quietName k) (there (++⁺ʳ (names so) m))
        lanes-apart = apart-r (flatNames fl) ps (there (there (there (here refl))))
        nlo = lookupᴬ lanes-apart (here refl)
        nso = proj₁ (all-++⁻ (names so) (tailᴬ (proj₂ (all-++⁻ (quietName k) (proj₂ (all-++⁻ (cutNames oc) lanes-apart))))))
    tears {H = H} (connectˢ S c b kb k fd rp e rt src bd) (st , ts , tb) ps =
      run-seq (tears src ts (proj₁ (pairs-split (names src) P)))
        (via-tears kb bd (stashed-alike kb (λ j m → torn-off H src j (proj₁ (all-++⁻ (names src) (proj₂ (all-++⁻ (quietName k)
                                                         (apart-r (quietName kb) Q m)))))) st)
                         (tearable-alike bd (λ j m → torn-off H src j (apart-l (names src) P m)) tb)
                         (proj₁ (proj₂ (pairs-split (names src) P))))
      where
        Q = pairs-r ((_ , b) ∷ []) (pairs-r (cutNames c) (pairs-r (subjectNames S) ps))
        P = pairs-r (quietName k) (pairs-r (quietName kb) Q)
    tears (joinˢ j sk l x st)       _ _        = runs⁺ (run-write l false run-done)
    tears (deferˢ k s)              (st , t) ps = via-tears k s st t (pairs-r (quietName k) ps)

    -- A switch cut, what it holds below unsubscribed.
    cut-tears : ∀ {h} {H : Heapᴹ h} (c : Kit.Cut h) (k : Maybe (Quiet h)) {Δ A} (s : Sub h Δ A)
              → At.Attached H c k (unsub s) × Tearable H s
              → _≢_ {A = Name h} (_ , Kit.live c) (_ , Kit.held c) → All (_≢_ {A = Name h} (_ , Kit.live c)) (quietName k)
              → All (_≢_ {A = Name h} (_ , Kit.live c)) (names s) → AllPairs _≢_ (names s) → Runs⁺ H (Kit.cut c) (thrown H c k s)
    cut-tears {H = H} c k s (a , t) nlh nlk nls pss = cut-runs c k s a nlh nlk (below k)
      where
        below : ∀ k′ → Via (store H (Kit.live c) (lift false)) k′ s
        below nothing  = lift tt
        below (just _) = tears s (tearable-alike s (λ j m → look-store H (Kit.live c) j (lookupᴬ nls m)) t) pss

    -- What a stash holds, unsubscribed.
    via-tears : ∀ {h} {H : Heapᴹ h} (k : Maybe (Quiet h)) {Δ A} (s : Sub h Δ A) → At.Stashed H k (unsub s) → Tearable H s
              → AllPairs _≢_ (names s) → Runs H (Kit.unsubscribeVia k) (tornVia H k s)
    via-tears nothing  s _  _ _  = run-done
    via-tears (just q) s st t ps = run-cancel st (tears s t ps)

    -- A flatMap's lanes in flight read, emptied, each cut.
    kill-tears : ∀ {h} {H : Heapᴹ h} {A Δ B} (fl : FlatKit.Flat A h) (ls : List (Lane h Δ B)) {gone}
               → At.val H (FlatKit.Flat.lanes fl) ++ gone ≡ cuts ls → TearableLanes H ls → AllPairs _≢_ (laneNames ls)
               → (∀ {n} → n ∈ᴸ laneNames ls → All (n ≢_) (flatNames fl))
               → Runs H (killAllᶜ fl) (thrownLanes (store (store H (FlatKit.Flat.lanes fl) (lift [])) (FlatKit.Flat.active fl) (lift 0))
                                                   (length (At.val H (FlatKit.Flat.lanes fl))) ls)
    kill-tears {H = H} fl ls eq tl ps ap = run-read (FlatKit.Flat.lanes fl) (λ where
      _ refl → runs⁺ (run-write (FlatKit.Flat.lanes fl) [] (runs⁺ (run-write (FlatKit.Flat.active fl) 0
                 (lanes-tears (At.val H (FlatKit.Flat.lanes fl)) ls eq (tearableL-alike ls al tl) ps)))))
      where
        H₂ = store H (FlatKit.Flat.lanes fl) (lift [])
        al : Alike H (store H₂ (FlatKit.Flat.active fl) (lift 0)) (laneNames ls)
        al j m = trans (look-store H₂ (FlatKit.Flat.active fl) j (≢-flip (lookupᴬ (ap m) (here refl))))
                       (look-store H (FlatKit.Flat.lanes fl) j (≢-flip (lookupᴬ (ap m) (there (there (there (here refl)))))))

    lanes-tears : ∀ {h} {H : Heapᴹ h} {Δ B} (cs : List (Kit.Cut h)) (ls : List (Lane h Δ B)) {gone} → cs ++ gone ≡ cuts ls
                → TearableLanes H ls → AllPairs _≢_ (laneNames ls) → Runs H (Kit.each cs Kit.cut) (thrownLanes H (length cs) ls)
    lanes-tears []       ls                _  _            _  = run-done
    lanes-tears (c ∷ cs) []                () _            _
    lanes-tears {H = H} (c ∷ cs) (lane c′ k s ∷ ls) eq (a , t , tl) ps with ∷-injectiveˡ eq | cut-apart c′ k (names s) ps
    ... | refl | nlh , nlk , nls , pss =
      run-seq (runs⁺ (cut-tears c k s (a , t) nlh nlk nls pss))
        (lanes-tears cs ls (∷-injectiveʳ eq)
          (tearableL-alike ls (λ j m → thrown-off H c k s j (lookupᴬ (apart-l (cutNames c) ps (++⁺ʳ (quietName k) (++⁺ʳ (names s) m))) (here refl))
                                                       (apart-l (names s) (pairs-r (quietName k) (pairs-r (cutNames c) ps)) m)) tl)
          (pairs-r (names s) (pairs-r (quietName k) (pairs-r (cutNames c) ps))))

  ----------------------------------------------------------------------
  -- A cut from the agenda's head: a taken takeWhile's, or the cut of a
  -- connect whose body has ended

  site-runs : ∀ {h} (H : Heapᴹ h) {t : Sub h [] R} → At.Holds H t [] rootObs → AllPairs _≢_ (names t)
            → (z : Site t) → Runs⁺ H (code (siteCall z)) (siteHeap H z)
  site-runs H hd ps (takeSite {c = c} {k} {s} π) with holds-at π hd
  ... | _ , _ , (a , hs) with cut-apart c k (names s) (subst (λ z → AllPairs _≢_ (cutNames c ++ quietName k ++ z)) (sym (++-identityʳ (names s))) (fresh-path π ps))
  ... | nlh , nlk , nls , pss = cut-tears c k s (a , tearable s hs) nlh nlk nls pss
  site-runs H hd ps (bodySite {S = S} {c = c} {b = b} {kb = kb} {k = k} {s = s} π) with holds-at π hd | pairs-r (subjectNames S) (fresh-path π ps)
  ... | _ , _ , (a , _ , _ , hs , _) | (nlh ∷ nr) ∷ Pc = cut-tears c k s (a , tearable s hs) nlh nlk nls pss
    where
      nr′  = proj₂ (all-++⁻ (quietName kb) (tailᴬ nr))
      nlk  = proj₁ (all-++⁻ (quietName k) nr′)
      nls  = proj₁ (all-++⁻ (names s) (proj₂ (all-++⁻ (quietName k) nr′)))
      pss  = proj₁ (pairs-split (names s) (pairs-r (quietName k) (pairs-r (quietName kb) (pairs-r ((_ , b) ∷ []) (pairs-r (_ ∷ []) Pc)))))

  -- The cut run from the agenda's head, to the rest of the agenda.
  site-tears : ∀ {h} (H : Heapᴹ h) {t : Sub h [] R} → At.Holds H t [] rootObs → AllPairs _≢_ (names t) → (z : Site t)
             → ∀ {ks p w σ K act clk ts bs td lg en mk} → act ≗ ⟦ siteCall z ∷ ks ⟧
             → ∀ {m′} → step (mach ⟨ H , p , run {w = w} act σ K ⟩ clk ts bs td lg en mk) ≡ silent m′
             → Σ (Act h ⊤) λ act′ → act′ ≗ ⟦ ks ⟧ × m′ ⇝ mach ⟨ siteHeap H z , p , run act′ σ K ⟩ clk ts bs td lg en mk
  site-tears H hd ps z {ks} {p} {w} {σ} {K} {act} {clk} {ts} {bs} {td} {lg} {en} {mk} e eq
    with site-runs H hd ps z (⟦ ks ⟧ ∷ []) e {p} {w} {σ} {K} {clk} {ts} {bs} {td} {lg} {en} {mk}
  ... | a′ , e′ , m₁ , st , path with trans (sym eq) st
  ... | refl = a′ , e′ , path
