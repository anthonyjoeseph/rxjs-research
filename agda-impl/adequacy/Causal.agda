-- ROWS READ THEIR ENVIRONMENT CAUSALLY: a state's rows at and below `q`
-- are read off its binders' rows at and below `q`.  Every operator reads
-- its inputs row by row, a pending subscription is its program's meaning
-- (`causal-⟦⟧`), and a connect's binder is a hot over its source's rows,
-- so by induction over the state.
module adequacy.Causal where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.List.Relation.Unary.All using (lookup) renaming (_∷_ to _∷ᴬ_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using () renaming (map to ⊎-map)

open import Tree using (mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Events using (Pos)
open import denotation.EmissionSet using (EmissionSet; DenEnv; _≼_)
open import denotation.Laws.Modulus using (AgreeTo; ⟨_⟩; upto; AgreeTo-sym; trunc-to; _~⟨_⟩_; ~-refl; ≼-refl)
open import denotation.Laws.ConnectNe using (proper-ag)
open import denotation.Laws using (EnvAg; causal-⟦⟧; map-ag; scan-ag; take-ag; conn-ag; hot-causal; ag-cons)
open import operation.PureObservable using (module Machine)
open Machine using (St; CS; Owe; free; cpAt; cutAt; overAt; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS)

open import adequacy.Rows using (rows; rowsL; Hot; Closed; _∪_; TakeR; Kept; kept; Stops; stop; left; _≃_; _⇄_;
  module Flat; module SwitchF; module ExhaustF; module BoundedF)
open import adequacy.Policy using (join-ag; flat-to; switch-to; exhaust-to; bounded-to)

------------------------------------------------------------------------
-- Agreement, by operator

ag-refl : ∀ {A Q} (t : EmissionSet A) → AgreeTo Q t t
ag-refl t = ⟨ (λ _ → (λ x → x) , (λ x → x)) ⟩

∪-ag : ∀ {A Q} {t t′ u u′ : EmissionSet A} → AgreeTo Q t t′ → AgreeTo Q u u′ → AgreeTo Q (t ∪ u) (t′ ∪ u′)
∪-ag a b = ⟨ (λ {y} {e} yq → ⊎-map (proj₁ (upto a {y} {e} yq)) (proj₁ (upto b {y} {e} yq))
                           , ⊎-map (proj₂ (upto a {y} {e} yq)) (proj₂ (upto b {y} {e} yq))) ⟩

private
  kept-to : ∀ {A Q p} {t t′ : EmissionSet A} → AgreeTo Q t t′ → ∀ {y e} → y ≼ Q → Kept p t y e → Kept p t′ y e
  kept-to a {y} yq (kept x np i) = kept (proj₁ (upto a {y} yq) x) np i

  stops-to : ∀ {A Q p} {t t′ : EmissionSet A} → AgreeTo Q t t′ → ∀ {y e} → y ≼ Q → Stops p t y e → Stops p t′ y e
  stops-to a yq stop     = stop
  stops-to a yq (left x) = left (kept-to a yq x)

-- A TAKE reads its source where it lies, whatever it owes.
take-r : ∀ {A Q} i (w : A → _) (o : Owe) {t t′ : EmissionSet A} → AgreeTo Q t t′ → AgreeTo Q (TakeR i w o t) (TakeR i w o t′)
take-r i w free       a = trunc-to (take-ag i w a)
take-r i w (cpAt p)   a = ⟨ (λ yq → stops-to a yq , stops-to (AgreeTo-sym a) yq) ⟩
take-r i w (cutAt p)  a = ⟨ (λ yq → kept-to a yq , kept-to (AgreeTo-sym a) yq) ⟩
take-r i w (overAt p) a = ⟨ (λ yq → kept-to a yq , kept-to (AgreeTo-sym a) yq) ⟩

-- A BINDER over agreeing rows agrees.
hot-ag : ∀ {A Q} (k : CS) {t t′ : EmissionSet A} → AgreeTo Q t t′ → Hot t k ~⟨ Q ⟩ Hot t′ k
hot-ag k {t} {t′} a = hot-causal (proper-ag (∪-ag a (ag-refl (Closed k))))

------------------------------------------------------------------------
-- The joiners

-- A JOINER PART WAY THROUGH READS ITS INPUTS CAUSALLY: its outer, each
-- lane it would begin and each lane it has begun, at and below `q`,
-- decide its rows there.
private
  la-sym : ∀ {A B : Set} {Q} {L L′ : A → Pos → EmissionSet B} → (∀ a p → AgreeTo Q (L a p) (L′ a p)) → ∀ a p → AgreeTo Q (L′ a p) (L a p)
  la-sym la a p = AgreeTo-sym (la a p)

  ls-sym : ∀ {B : Set} {Q} {Ls Ls′ : List (EmissionSet B)} → Pointwise (AgreeTo Q) Ls Ls′ → Pointwise (AgreeTo Q) Ls′ Ls
  ls-sym []       = []
  ls-sym (g ∷ gs) = AgreeTo-sym g ∷ ls-sym gs

flat-ag : ∀ {A B Q} {L L′ : A → Pos → EmissionSet B} {O O′ : EmissionSet A} d n {Ls Ls′ : List (EmissionSet B)}
        → (∀ a p → AgreeTo Q (L a p) (L′ a p)) → AgreeTo Q O O′ → Pointwise (AgreeTo Q) Ls Ls′
        → AgreeTo Q (Flat.RowT L O d n Ls) (Flat.RowT L′ O′ d n Ls′)
flat-ag {Q = Q} d n la ao ls = trunc-to (join-ag Q (flat-to Q d n la ao ls) (flat-to Q d n (la-sym la) (AgreeTo-sym ao) (ls-sym ls)))

switch-ag : ∀ {A B Q} {L L′ : A → Pos → EmissionSet B} {O O′ : EmissionSet A} d n {Ls Ls′ : List (EmissionSet B)}
          → (∀ a p → AgreeTo Q (L a p) (L′ a p)) → AgreeTo Q O O′ → Pointwise (AgreeTo Q) Ls Ls′
          → AgreeTo Q (SwitchF.RowT L O d n Ls) (SwitchF.RowT L′ O′ d n Ls′)
switch-ag {Q = Q} d n la ao ls = trunc-to (join-ag Q (switch-to Q d n la ao ls) (switch-to Q d n (la-sym la) (AgreeTo-sym ao) (ls-sym ls)))

exhaust-ag : ∀ {A B Q} {L L′ : A → Pos → EmissionSet B} {O O′ : EmissionSet A} d n {Ls Ls′ : List (EmissionSet B)}
           → (∀ a p → AgreeTo Q (L a p) (L′ a p)) → AgreeTo Q O O′ → Pointwise (AgreeTo Q) Ls Ls′
           → AgreeTo Q (ExhaustF.RowT L O d n Ls) (ExhaustF.RowT L′ O′ d n Ls′)
exhaust-ag {Q = Q} d n la ao ls =
  trunc-to (join-ag Q (exhaust-to Q d n la ao ls (la-sym la) (ls-sym ls)) (exhaust-to Q d n (la-sym la) (AgreeTo-sym ao) (ls-sym ls) la ls))

bounded-ag : ∀ {A B Q} m {L L′ : A → Pos → EmissionSet B} {O O′ : EmissionSet A} d n Qu {Ls Ls′ : List (EmissionSet B)}
           → (∀ a p → AgreeTo Q (L a p) (L′ a p)) → AgreeTo Q O O′ → Pointwise (AgreeTo Q) Ls Ls′
           → AgreeTo Q (BoundedF.RowT m L O d n Qu Ls) (BoundedF.RowT m L′ O′ d n Qu Ls′)
bounded-ag {Q = Q} m d n Qu la ao ls =
  trunc-to (join-ag Q (bounded-to Q m d n Qu la ao ls (la-sym la) (ls-sym ls)) (bounded-to Q m d n Qu (la-sym la) (AgreeTo-sym ao) (ls-sym ls) la ls))

------------------------------------------------------------------------
-- By the state

mutual
  rows-causal : ∀ {Γ A Q} {ρ ρ′ : DenEnv Γ} → EnvAg Q ρ ρ′ → (s : St Γ A) → AgreeTo Q (rows ρ s) (rows ρ′ s)
  rows-causal e (pend o p)                            = causal-⟦⟧ o e p
  rows-causal e (coldS true l)                        = ag-refl _
  rows-causal e (coldS false l)                       = ag-refl _
  rows-causal e (ofS i p xs)                          = ag-refl _
  rows-causal e doneS                                 = ag-refl _
  rows-causal e (mapS f s)                            = map-ag f (rows-causal e s)
  rows-causal e (scanS f z s)                         = scan-ag f z (rows-causal e s)
  rows-causal e (takeS i w o s)                       = take-r i w o (rows-causal e s)
  rows-causal e (cutS true a s)                       = rows-causal e s
  rows-causal e (cutS false a s)                      = ag-refl _
  rows-causal e (lnS true s)                          = rows-causal e s
  rows-causal e (lnS false s)                         = ag-refl _
  rows-causal e (flatS (mergeᶠ nothing) f d n q o ls)  = flat-ag d n (λ a → causal-⟦⟧ (f a) e) (rows-causal e o) (rowsL-causal e ls)
  rows-causal e (flatS (mergeᶠ (just m)) f d n q o ls) = bounded-ag m d n q (λ a → causal-⟦⟧ (f a) e) (rows-causal e o) (rowsL-causal e ls)
  rows-causal e (flatS switchᶠ f d n q o ls)           = switch-ag d n (λ a → causal-⟦⟧ (f a) e) (rows-causal e o) (rowsL-causal e ls)
  rows-causal e (flatS exhaustᶠ f d n q o ls)          = exhaust-ag d n (λ a → causal-⟦⟧ (f a) e) (rows-causal e o) (rowsL-causal e ls)
  rows-causal e (connS k o b)                         = conn-ag (CS.connAt k) (rows-causal e o) (rows-causal (ag-cons (hot-ag k (rows-causal e o)) e) b)
  rows-causal e (joinS j true x ib)                   = ∪-ag (ag-refl _) (e x j)
  rows-causal e (joinS j false x ib)                  = ag-refl _

  rowsL-causal : ∀ {Γ A Q} {ρ ρ′ : DenEnv Γ} → EnvAg Q ρ ρ′ → (ls : List (St Γ A)) → Pointwise (AgreeTo Q) (rowsL ρ ls) (rowsL ρ′ ls)
  rowsL-causal e []       = []
  rowsL-causal e (s ∷ ls) = rows-causal e s ∷ rowsL-causal e ls

-- The same binders: every environment agrees with itself.
env-refl : ∀ {Γ Q} (ρ : DenEnv Γ) → EnvAg Q ρ ρ
env-refl ρ i = ~-refl (lookup ρ i)

-- AGREEING EVERYWHERE, THE SAME ROWS.
rows-≃ : ∀ {Γ A} {ρ ρ′ : DenEnv Γ} → (∀ Q → EnvAg Q ρ ρ′) → (s : St Γ A) → rows ρ s ≃ rows ρ′ s
rows-≃ e s = (λ {q} x → proj₁ (upto (rows-causal (e q) s) {q} (≼-refl {q})) x)
           ⇄ (λ {q} x → proj₂ (upto (rows-causal (e q) s) {q} (≼-refl {q})) x)

-- A BINDER'S MEANING, UP TO THE SAME ROWS: a body reads its binder only
-- through the rows it holds, so the same rows bound give the same body.
rows-hot : ∀ {Γ X B} {t u : EmissionSet X} (k : CS) (ρ : DenEnv Γ) (b : St (X ∷ Γ) B) → t ≃ u → rows (Hot t k ∷ᴬ ρ) b ≃ rows (Hot u k ∷ᴬ ρ) b
rows-hot k ρ b eq = rows-≃ (λ Q → ag-cons (hot-ag k ⟨ (λ _ → _≃_.to eq , _≃_.from eq) ⟩) (env-refl ρ)) b
