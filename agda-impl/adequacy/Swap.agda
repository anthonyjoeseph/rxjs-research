{-# OPTIONS --guardedness #-}

-- A NODE SWAPPED FOR ONE OWING THE SAME ROWS: the same good tree, and the
-- lists and counts its merges read.
module adequacy.Swap where

open import Data.Bool using (true; false; _∧_)
open import Data.List using (List; []; _∷_; _ʳ++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (_+_)
open import Data.Nat.Properties using (+-suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List.Relation.Unary.All using ([]; lookup) renaming (_∷_ to _∷ᴬ_)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (tt to tt₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

open import Tree using (mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Events using (Pos)
open import denotation.EmissionSet using (EmissionSet; DenEnv; enter)
open import denotation.Laws using (EnvAg; ag-cons)
open import denotation.Laws.Modulus using (⟨_⟩; upto; ≼-refl)
open import operation.PureObservable using (module Machine)
open Machine using (St; Ctx; CS; plug; alive; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
                    top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody)
open import adequacy.Rows using (env; rows; rowsL; _≃_; _⇄_; Hot)
open import adequacy.Causal using (rows-hot; rows-≃; rows-causal; hot-ag; env-refl)
open import adequacy.Up using (_≈ᴸ_; []; _∷_; ≈ᴸ-refl; row-≃; map-≃; scan-≃; take-≃; ≃-refl; conn-≃; bounded-≃;
  switch-≃; exhaust-≃)
open import adequacy.Bound using (Empty; empty-any; EndLast; Roots; Rooted; Live; Live₁; G; GL; GLn; LnBody; SrcG; HeldAt; live;
  mergeG-map; MergeG; Told; ToldL; Fed) renaming (held to heldᴮ)

open _≃_

------------------------------------------------------------------------
-- Rows owed up a frame

rowsL-ʳ++ : ∀ {Γ A} {ρ : DenEnv Γ} (xs : List (St Γ A)) {ys} → rowsL ρ (xs ʳ++ ys) ≡ rowsL ρ xs ʳ++ rowsL ρ ys
rowsL-ʳ++ []       = refl
rowsL-ʳ++ (x ∷ xs) = rowsL-ʳ++ xs

≡→≃ : ∀ {A} {t u : EmissionSet A} → t ≡ u → t ≃ u
≡→≃ refl = ≃-refl

------------------------------------------------------------------------
-- Lanes still in their list

live-ʳ++ : ∀ {Γ A} (xs : List (St Γ A)) {ys} → live (xs ʳ++ ys) ≡ live xs + live ys
live-ʳ++ []       = refl
live-ʳ++ (x ∷ xs) {ys} rewrite live-ʳ++ xs {x ∷ ys} with alive x
... | true  = +-suc (live xs) (live ys)
... | false = refl

goodL-ʳ++ : ∀ {Γ A} {ρ : DenEnv Γ} {v} (xs : List (St Γ A)) {ys} → GL ρ v xs → GL ρ v ys → GL ρ v (xs ʳ++ ys)
goodL-ʳ++ []       _        b = b
goodL-ʳ++ (x ∷ xs) (g , gs) b = goodL-ʳ++ xs gs (g , b)

goodL-ʳ++⁻ : ∀ {Γ A} {ρ : DenEnv Γ} {v} (xs : List (St Γ A)) {ys} → GL ρ v (xs ʳ++ ys) → GL ρ v xs × GL ρ v ys
goodL-ʳ++⁻ []       b = tt₁ , b
goodL-ʳ++⁻ (x ∷ xs) b with goodL-ʳ++⁻ xs b
... | a , (g , c) = (g , a) , c

------------------------------------------------------------------------
-- A node swapped for one owing the same rows

endlast-≃ : ∀ {A} {t u : EmissionSet A} → t ≃ u → EndLast t → EndLast u
endlast-≃ eq el r r′ = el (from eq r) (from eq r′)

empty-≃ : ∀ {A} {t u : EmissionSet A} → t ≃ u → Empty t → Empty u
empty-≃ eq em r = em (from eq r)

live-endlast : ∀ {A} v {t u : EmissionSet A} → t ≃ u → Live v (EndLast t) → Live v (EndLast u)
live-endlast true  eq el = endlast-≃ eq el
live-endlast false eq el = tt

-- The same rows, the same liveness, a good node and lane for a good one:
-- the same good tree.
record Swap {Γ A} (ρ : DenEnv Γ) (s s′ : St Γ A) : Set₁ where
  field
    same : rows ρ s ≃ rows ρ s′
    live≡ : alive s ≡ alive s′
    node : ∀ v → G ρ v s → G ρ v s′
    lane : ∀ v → GLn ρ v s → GLn ρ v s′
    body : ∀ v b → LnBody ρ v b s → LnBody ρ v b s′
    held : ∀ {v q} → HeldAt ρ v q s → HeldAt ρ v q s′
    told : ∀ {X} (x : X ∈ Γ) → Told x s → Told x s′
open Swap

live-swap : ∀ {Γ A} (xs : List (St Γ A)) {s s′ ys} → alive s ≡ alive s′ → live (xs ʳ++ s ∷ ys) ≡ live (xs ʳ++ s′ ∷ ys)
live-swap xs {s} {s′} {ys} eq rewrite live-ʳ++ xs {s ∷ ys} | live-ʳ++ xs {s′ ∷ ys} | eq = refl

toldL-ʳ++ : ∀ {Γ X A} {x : X ∈ Γ} (xs : List (St Γ A)) {ys} → ToldL x xs → ToldL x ys → ToldL x (xs ʳ++ ys)
toldL-ʳ++ []       _        b = b
toldL-ʳ++ (y ∷ xs) (t , ts) b = toldL-ʳ++ xs ts (t , b)

toldL-ʳ++⁻ : ∀ {Γ X A} {x : X ∈ Γ} (xs : List (St Γ A)) {ys} → ToldL x (xs ʳ++ ys) → ToldL x xs × ToldL x ys
toldL-ʳ++⁻ []       b = tt , b
toldL-ʳ++⁻ (y ∷ xs) b with toldL-ʳ++⁻ xs b
... | a , (t , c) = (t , a) , c

toldL-swap : ∀ {Γ X A} {x : X ∈ Γ} (xs : List (St Γ A)) {s s′ ys} → (Told x s → Told x s′) → ToldL x (xs ʳ++ s ∷ ys) → ToldL x (xs ʳ++ s′ ∷ ys)
toldL-swap xs h t with toldL-ʳ++⁻ xs t
... | tx , (ts , ty) = toldL-ʳ++ xs tx (h ts , ty)

-- A closed binder's joiners told, up to a swap that keeps them told.
live-told : ∀ v {P : Set} {t u : Set} → (t → u) → Live v (P → t) → Live v (P → u)
live-told true  h l p = h (l p)
live-told false h l   = tt

goodL-swap : ∀ {Γ A} {ρ : DenEnv Γ} {v} (xs : List (St Γ A)) {s s′ ys} → (GLn ρ v s → GLn ρ v s′) → GL ρ v (xs ʳ++ s ∷ ys) → GL ρ v (xs ʳ++ s′ ∷ ys)
goodL-swap xs h g with goodL-ʳ++⁻ xs g
... | gx , (gs , gy) = goodL-ʳ++ xs gx (h gs , gy)

lanes-≃ : ∀ {Γ A} {ρ : DenEnv Γ} (xs : List (St Γ A)) {ys ys′} → rowsL ρ ys ≈ᴸ rowsL ρ ys′ → rowsL ρ (xs ʳ++ ys) ≈ᴸ rowsL ρ (xs ʳ++ ys′)
lanes-≃ []       h = h
lanes-≃ (x ∷ xs) h = lanes-≃ xs (≃-refl ∷ h)

roots-≈ : ∀ {A B} {H : Pos → Set} {X : EmissionSet A} qs {Ls Ls′ : List (EmissionSet B)} → Ls ≈ᴸ Ls′ → Roots H X qs Ls → Roots H X qs Ls′
roots-≈ []       []       _                         = tt
roots-≈ (q ∷ qs) (e ∷ es) ((a , x , w) , nq , rs) = (a , x , λ l → w (from e l)) , nq , roots-≈ qs es rs
roots-≈ []       (_ ∷ _)  ()
roots-≈ (_ ∷ _)  []       ()

rooted-≃ : ∀ {A B} {O O′ : EmissionSet A} {Ls Ls′ : List (EmissionSet B)} → O ≃ O′ → Ls ≈ᴸ Ls′ → Rooted O Ls → Rooted O′ Ls′
rooted-≃ eo es r = record { H = H ; X = X ; p₀ = p₀ ; inv = inv ; sub = λ x → sub (from eo x) ; qs = qs ; roots = roots-≈ qs es roots }
  where open Rooted r

-- A source swapped: the same source to its connect.
src-swap : ∀ {Γ A} {ρ : DenEnv Γ} {s s′ : St Γ A} → Swap ρ s s′ → ∀ v m → SrcG ρ v m s → SrcG ρ v m s′
src-swap sw v nothing  g = node sw v g
src-swap sw v (just _) g = held sw g

-- A completed source owing nothing, up to the same rows.
spent-≃ : ∀ {A} {t u : EmissionSet A} {P : Set} v → t ≃ u → Live v (P → Empty t) → Live v (P → Empty u)
spent-≃ true  eq sp h = empty-≃ eq (sp h)
spent-≃ false eq sp   = tt

------------------------------------------------------------------------
-- The same goodness under agreeing binders

-- Environments agreeing at every bound.
Agree : ∀ {Γ} → DenEnv Γ → DenEnv Γ → Set₁
Agree ρ ρ′ = ∀ Q → EnvAg Q ρ ρ′

private
  agree-cons : ∀ {Γ X} {ρ ρ′ : DenEnv Γ} (k : CS Γ X) (o : St Γ X) → Agree ρ ρ′ → Agree (Hot ρ (rows ρ o) k ∷ᴬ ρ) (Hot ρ′ (rows ρ′ o) k ∷ᴬ ρ′)
  agree-cons k o e Q = ag-cons (hot-ag k (e Q) (rows-causal (e Q) o)) (e Q)

  enter-≃ : ∀ {Γ A} {ρ ρ′ : DenEnv Γ} → Agree ρ ρ′ → (x : A ∈ Γ) → ∀ j → enter (lookup ρ x) j ≃ enter (lookup ρ′ x) j
  enter-≃ e x j = (λ {q} r → proj₁ (upto (e q x j) {q} (≼-refl {q})) r) ⇄ (λ {q} r → proj₂ (upto (e q x j) {q} (≼-refl {q})) r)

  rowsL-≈ : ∀ {Γ A} {ρ ρ′ : DenEnv Γ} → Agree ρ ρ′ → (ls : List (St Γ A)) → rowsL ρ ls ≈ᴸ rowsL ρ′ ls
  rowsL-≈ e []       = []
  rowsL-≈ e (s ∷ ls) = rows-≃ e s ∷ rowsL-≈ e ls

  fed-≃ : ∀ {A} {t u : EmissionSet A} ib → t ≃ u → Fed ib t → Fed ib u
  fed-≃ []       eq _           = tt₁
  fed-≃ (_ ∷ ib) eq (a , b , f) = a , (λ y → b (from eq y)) , fed-≃ ib eq f

  live-rooted : ∀ {A B} v {O O′ : EmissionSet A} {Ls Ls′ : List (EmissionSet B)} → O ≃ O′ → Ls ≈ᴸ Ls′ → Live₁ v (Rooted O Ls) → Live₁ v (Rooted O′ Ls′)
  live-rooted true  eo es r = rooted-≃ eo es r
  live-rooted false eo es r = tt₁

-- A GOOD TREE UNDER AGREEING BINDERS: goodness reads its binders only
-- through the rows they give, and a joiner's inbox only against its
-- binder's rows.
mutual
  good-env : ∀ {Γ A} {ρ ρ′ : DenEnv Γ} → Agree ρ ρ′ → ∀ v (s : St Γ A) → G ρ v s → G ρ′ v s
  good-env e v (pend o p)                            ()
  good-env e v (lnS l s)                             ()
  good-env e v (ofS i p xs)                          g = g
  good-env e v doneS                                 g = g
  good-env e v (coldS w l)                           g = g
  good-env e v (mapS f s)                            g = good-env e v s g
  good-env e v (scanS f z s)                         g = good-env e v s g
  good-env e v (takeS i q w s)                       g = good-env e v s g
  good-env e v (cutS l a s)                          g = good-env e (v ∧ l) s g
  good-env e v (flatS (mergeᶠ nothing) f d n q o ls)  g       = merge-env e v o ls g
  good-env e v (flatS (mergeᶠ (just m)) f d n q o ls) (g , w) = merge-env e v o ls g , w
  good-env e v (flatS switchᶠ f d n q o ls)           g       = merge-env e v o ls g
  good-env e v (flatS exhaustᶠ f d n q o ls)          g       = merge-env e v o ls g
  good-env e v (connS k o s) (gs , gb , sp , tl) =
    src-env e v (CS.bodyAt k) o gs , good-env (agree-cons k o e) v s gb , spent-≃ v (rows-≃ e o) sp , tl
  good-env {ρ = ρ} {ρ′} e true (joinS j true x ib) g = fed-≃ ib (enter-≃ {ρ = ρ} {ρ′} e x j) g
  good-env e false (joinS j true x ib)  g = g
  good-env e v     (joinS j false x ib) g = g

  merge-env : ∀ {Γ A B} {ρ ρ′ : DenEnv Γ} → Agree ρ ρ′ → ∀ v {f d n q} (o : St Γ A) (ls : List (St Γ B))
            → MergeG (G ρ v o) (GL ρ v ls) ρ v f d n q o ls → MergeG (G ρ′ v o) (GL ρ′ v ls) ρ′ v f d n q o ls
  merge-env e v o ls m = record
    { outer  = good-env e v o (MergeG.outer m)
    ; lanesG = gl-env e v ls (MergeG.lanesG m)
    ; fresh  = MergeG.fresh m
    ; count  = MergeG.count m
    ; spent  = spent-≃ v (rows-≃ e o) (MergeG.spent m)
    ; rooted = live-rooted v (rows-≃ e o) (rowsL-≈ e ls) (MergeG.rooted m)
    }

  src-env : ∀ {Γ A} {ρ ρ′ : DenEnv Γ} → Agree ρ ρ′ → ∀ v m (s : St Γ A) → SrcG ρ v m s → SrcG ρ′ v m s
  src-env e v nothing  s                    g = good-env e v s g
  src-env e true  (just p) (pend o q) (heldᴮ h) = heldᴮ λ r → h (from (rows-≃ e (pend o q)) r)
  src-env e false (just p) (pend o q) (heldᴮ h) = heldᴮ tt

  gl-env : ∀ {Γ A} {ρ ρ′ : DenEnv Γ} → Agree ρ ρ′ → ∀ v (ls : List (St Γ A)) → GL ρ v ls → GL ρ′ v ls
  gl-env e v []       g       = tt₁
  gl-env e v (s ∷ ls) (a , b) = gln-env e v s a , gl-env e v ls b

  gln-env : ∀ {Γ A} {ρ ρ′ : DenEnv Γ} → Agree ρ ρ′ → ∀ v (s : St Γ A) → GLn ρ v s → GLn ρ′ v s
  gln-env e v (lnS l (cutS l′ a s)) (eq , g , el) = eq , good-env e (v ∧ l) s g , live-endlast (v ∧ l) (rows-≃ e s) el
  gln-env e v (lnS l (pend _ _))        ()
  gln-env e v (lnS l (coldS _ _))       ()
  gln-env e v (lnS l (ofS _ _ _))       ()
  gln-env e v (lnS l doneS)             ()
  gln-env e v (lnS l (mapS _ _))        ()
  gln-env e v (lnS l (scanS _ _ _))     ()
  gln-env e v (lnS l (lnS _ _))         ()
  gln-env e v (lnS l (takeS _ _ _ _))   ()
  gln-env e v (lnS l (flatS _ _ _ _ _ _ _)) ()
  gln-env e v (lnS l (connS _ _ _))     ()
  gln-env e v (lnS l (joinS _ _ _ _))   ()
  gln-env e v (pend _ _)                ()
  gln-env e v (coldS _ _)               ()
  gln-env e v (ofS _ _ _)               ()
  gln-env e v doneS                     ()
  gln-env e v (mapS _ _)                ()
  gln-env e v (scanS _ _ _)             ()
  gln-env e v (cutS _ _ _)              ()
  gln-env e v (takeS _ _ _ _)           ()
  gln-env e v (flatS _ _ _ _ _ _ _)     ()
  gln-env e v (connS _ _ _)             ()
  gln-env e v (joinS _ _ _ _)           ()

-- A BINDER'S GOOD BODY, UP TO THE SAME ROWS: a body reads its binder
-- only through the rows it holds.
good-hot : ∀ {Γ X B} {t u : EmissionSet X} (k : CS Γ X) (ρ : DenEnv Γ) (b : St (X ∷ Γ) B) → t ≃ u → ∀ v → G (Hot ρ t k ∷ᴬ ρ) v b → G (Hot ρ u k ∷ᴬ ρ) v b
good-hot k ρ b eq v = good-env (λ Q → ag-cons (hot-ag k (env-refl ρ) ⟨ (λ _ → to eq , from eq) ⟩) (env-refl ρ)) v b

good-swap : ∀ {R Γ A} (c : Ctx R Γ A) {s s′ : St Γ A} → Swap (env c) s s′ → ∀ {v} → G [] v (plug c s) → G [] v (plug c s′)
good-swap top              sw {v} g = node sw v g
good-swap (inMap f c)      sw g = good-swap c (record { same = map-≃ f (same sw) ; live≡ = refl ; node = node sw ; lane = λ _ () ; body = λ _ _ () ; held = λ () ; told = told sw }) g
good-swap (inScan f z c)   sw g = good-swap c (record { same = scan-≃ f z (same sw) ; live≡ = refl ; node = node sw ; lane = λ _ () ; body = λ _ _ () ; held = λ () ; told = told sw }) g
good-swap (inCut true a c) sw g = good-swap c (record { same = same sw ; live≡ = refl ; node = λ v → node sw (v ∧ true) ; lane = λ _ () ; body = λ { v b (eq , gs , el) → eq , node sw (v ∧ b) gs , live-endlast (v ∧ b) (same sw) el } ; held = λ () ; told = told sw }) g
good-swap (inCut false a c) sw g = good-swap c (record { same = ≃-refl ; live≡ = refl ; node = λ v → node sw (v ∧ false) ; lane = λ _ () ; body = λ { v b (eq , gs , el) → eq , node sw (v ∧ b) gs , live-endlast (v ∧ b) (same sw) el } ; held = λ () ; told = λ _ _ → tt }) g
good-swap (inLn true c)    sw g = good-swap c (record { same = same sw ; live≡ = refl ; node = λ _ () ; lane = λ v → body sw v true ; body = λ _ _ () ; held = λ () ; told = told sw }) g
good-swap (inLn false c)   sw g = good-swap c (record { same = ≃-refl ; live≡ = refl ; node = λ _ () ; lane = λ v → body sw v false ; body = λ _ _ () ; held = λ () ; told = told sw }) g
good-swap (inTake i q w c) sw g = good-swap c (record { same = take-≃ i q w (same sw) ; live≡ = refl ; node = node sw ; lane = λ _ () ; body = λ _ _ () ; held = λ () ; told = told sw }) g
good-swap (inOuter (mergeᶠ nothing) f d n q ls c) {s} {s′} sw g =
  good-swap c {s = flatS (mergeᶠ nothing) f d n q s ls} {s′ = flatS (mergeᶠ nothing) f d n q s′ ls} (record { same = row-≃ _ n (same sw) (≈ᴸ-refl (rowsL (env c) ls)) ; live≡ = refl ; lane = λ _ () ; body = λ _ _ () ; held = λ () ; told = λ x (a , b) → told sw x a , b
                      ; node = λ { true m → mergeG-map (node sw true) (λ x → x) (λ x → x) (λ ov t {q} {e} → empty-≃ (same sw) (ov t) {q} {e}) (rooted-≃ (same sw) (≈ᴸ-refl (rowsL (env c) ls))) m
                                 ; false m → mergeG-map (node sw false) (λ x → x) (λ x → x) (λ x → x) (λ x → x) m } }) g
good-swap (inOuter (mergeᶠ (just m)) f d n q ls c) {s} {s′} sw g =
  good-swap c {s = flatS (mergeᶠ (just m)) f d n q s ls} {s′ = flatS (mergeᶠ (just m)) f d n q s′ ls} (record { same = bounded-≃ m _ (same sw) (≈ᴸ-refl (rowsL (env c) ls)) ; live≡ = refl ; lane = λ _ () ; body = λ _ _ () ; held = λ () ; told = λ x (a , b) → told sw x a , b
                      ; node = λ { true (mg , w) → mergeG-map (node sw true) (λ x → x) (λ x → x) (λ ov t {q} {e} → empty-≃ (same sw) (ov t) {q} {e}) (rooted-≃ (same sw) (≈ᴸ-refl (rowsL (env c) ls))) mg , w
                                 ; false (mg , w) → mergeG-map (node sw false) (λ x → x) (λ x → x) (λ x → x) (λ x → x) mg , w } }) g
good-swap (inOuter switchᶠ f d n q ls c) {s} {s′} sw g =
  good-swap c {s = flatS switchᶠ f d n q s ls} {s′ = flatS switchᶠ f d n q s′ ls} (record { same = switch-≃ _ (same sw) (≈ᴸ-refl (rowsL (env c) ls)) ; live≡ = refl ; lane = λ _ () ; body = λ _ _ () ; held = λ () ; told = λ x (a , b) → told sw x a , b
                      ; node = λ { true m → mergeG-map (node sw true) (λ x → x) (λ x → x) (λ ov t {q} {e} → empty-≃ (same sw) (ov t) {q} {e}) (rooted-≃ (same sw) (≈ᴸ-refl (rowsL (env c) ls))) m
                                 ; false m → mergeG-map (node sw false) (λ x → x) (λ x → x) (λ x → x) (λ x → x) m } }) g
good-swap (inOuter exhaustᶠ f d n q ls c) {s} {s′} sw g =
  good-swap c {s = flatS exhaustᶠ f d n q s ls} {s′ = flatS exhaustᶠ f d n q s′ ls} (record { same = exhaust-≃ _ (same sw) (≈ᴸ-refl (rowsL (env c) ls)) ; live≡ = refl ; lane = λ _ () ; body = λ _ _ () ; held = λ () ; told = λ x (a , b) → told sw x a , b
                      ; node = λ { true m → mergeG-map (node sw true) (λ x → x) (λ x → x) (λ ov t {q} {e} → empty-≃ (same sw) (ov t) {q} {e}) (rooted-≃ (same sw) (≈ᴸ-refl (rowsL (env c) ls))) m
                                 ; false m → mergeG-map (node sw false) (λ x → x) (λ x → x) (λ x → x) (λ x → x) m } }) g
good-swap (inLanes (mergeᶠ nothing) f d n q o pre post c) {s} {s′} sw g =
  good-swap c {s = flatS (mergeᶠ nothing) f d n q o (pre ʳ++ s ∷ post)} {s′ = flatS (mergeᶠ nothing) f d n q o (pre ʳ++ s′ ∷ post)} (record { same = row-≃ _ n ≃-refl (lanes-≃ pre (same sw ∷ ≈ᴸ-refl (rowsL (env c) post))) ; live≡ = refl ; lane = λ _ () ; body = λ _ _ () ; held = λ () ; told = λ x (a , b) → a , toldL-swap pre (told sw x) b
                      ; node = λ { true m → mergeG-map (λ x → x) (goodL-swap pre (lane sw true)) (λ nl → trans nl (live-swap pre (live≡ sw))) (λ x → x) (rooted-≃ ≃-refl (lanes-≃ pre (same sw ∷ ≈ᴸ-refl (rowsL (env c) post)))) m
                                 ; false m → mergeG-map (λ x → x) (goodL-swap pre (lane sw false)) (λ x → x) (λ x → x) (λ x → x) m } }) g
good-swap (inLanes (mergeᶠ (just m)) f d n q o pre post c) {s} {s′} sw g =
  good-swap c {s = flatS (mergeᶠ (just m)) f d n q o (pre ʳ++ s ∷ post)} {s′ = flatS (mergeᶠ (just m)) f d n q o (pre ʳ++ s′ ∷ post)} (record { same = bounded-≃ m _ ≃-refl (lanes-≃ pre (same sw ∷ ≈ᴸ-refl (rowsL (env c) post))) ; live≡ = refl ; lane = λ _ () ; body = λ _ _ () ; held = λ () ; told = λ x (a , b) → a , toldL-swap pre (told sw x) b
                      ; node = λ { true (mg , w) → mergeG-map (λ x → x) (goodL-swap pre (lane sw true)) (λ nl → trans nl (live-swap pre (live≡ sw))) (λ x → x) (rooted-≃ ≃-refl (lanes-≃ pre (same sw ∷ ≈ᴸ-refl (rowsL (env c) post)))) mg , w
                                 ; false (mg , w) → mergeG-map (λ x → x) (goodL-swap pre (lane sw false)) (λ x → x) (λ x → x) (λ x → x) mg , w } }) g
good-swap (inLanes switchᶠ f d n q o pre post c) {s} {s′} sw g =
  good-swap c {s = flatS switchᶠ f d n q o (pre ʳ++ s ∷ post)} {s′ = flatS switchᶠ f d n q o (pre ʳ++ s′ ∷ post)} (record { same = switch-≃ _ ≃-refl (lanes-≃ pre (same sw ∷ ≈ᴸ-refl (rowsL (env c) post))) ; live≡ = refl ; lane = λ _ () ; body = λ _ _ () ; held = λ () ; told = λ x (a , b) → a , toldL-swap pre (told sw x) b
                      ; node = λ { true m → mergeG-map (λ x → x) (goodL-swap pre (lane sw true)) (λ nl → trans nl (live-swap pre (live≡ sw))) (λ x → x) (rooted-≃ ≃-refl (lanes-≃ pre (same sw ∷ ≈ᴸ-refl (rowsL (env c) post)))) m
                                 ; false m → mergeG-map (λ x → x) (goodL-swap pre (lane sw false)) (λ x → x) (λ x → x) (λ x → x) m } }) g
good-swap (inLanes exhaustᶠ f d n q o pre post c) {s} {s′} sw g =
  good-swap c {s = flatS exhaustᶠ f d n q o (pre ʳ++ s ∷ post)} {s′ = flatS exhaustᶠ f d n q o (pre ʳ++ s′ ∷ post)} (record { same = exhaust-≃ _ ≃-refl (lanes-≃ pre (same sw ∷ ≈ᴸ-refl (rowsL (env c) post))) ; live≡ = refl ; lane = λ _ () ; body = λ _ _ () ; held = λ () ; told = λ x (a , b) → a , toldL-swap pre (told sw x) b
                      ; node = λ { true m → mergeG-map (λ x → x) (goodL-swap pre (lane sw true)) (λ nl → trans nl (live-swap pre (live≡ sw))) (λ x → x) (rooted-≃ ≃-refl (lanes-≃ pre (same sw ∷ ≈ᴸ-refl (rowsL (env c) post)))) m
                                 ; false m → mergeG-map (λ x → x) (goodL-swap pre (lane sw false)) (λ x → x) (λ x → x) (λ x → x) m } }) g
good-swap (inSrc k b c) {s} {s′} sw g =
  good-swap c {s = connS k s b} {s′ = connS k s′ b} (record { same = conn-≃ _ (same sw) (rows-hot k (env c) b (same sw)) ; live≡ = refl ; lane = λ _ () ; body = λ _ _ () ; held = λ () ; told = λ x (a , b) → told sw x a , b
                      ; node = λ { v (gs , gb , sp , tl) → src-swap sw v (CS.bodyAt k) gs , good-hot k (env c) b (same sw) v gb , spent-≃ v (same sw) sp , tl } }) g
good-swap (inBody k o c) {s} {s′} sw g =
  good-swap c {s = connS k o s} {s′ = connS k o s′} (record { same = conn-≃ _ ≃-refl (same sw) ; live≡ = refl ; lane = λ _ () ; body = λ _ _ () ; held = λ () ; told = λ x (a , b) → a , told sw (there x) b
                      ; node = λ { v (gs , gb , sp , tl) → gs , node sw v gb , sp , live-told v (told sw (here refl)) tl } }) g
