{-# OPTIONS --guardedness #-}

-- A NODE SWAPPED FOR ONE OWING THE SAME ROWS: the same good tree, and the
-- lists and counts its merges read.
module adequacy.Swap where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using (List; []; _∷_; _ʳ++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; _+_)
open import Data.Nat.Properties using (+-suc)
open import Data.Product using (_×_; _,_)
open import Data.List.Relation.Unary.All using ([]) renaming (_∷_ to _∷ᴬ_)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to tt₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

open import Tree using (mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Events using (Pos)
open import denotation.EmissionSet using (EmissionSet; DenEnv)
open import operation.PureObservable using (module Machine)
open Machine using (St; Ctx; CS; plug; alive; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
                    top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody)
open import adequacy.Rows using (env; rows; rowsL; Each; module Flat; _≃_; Hot)
open import adequacy.Up using (_≈ᴸ_; []; _∷_; ≈ᴸ-refl; row-≃; map-≃; scan-≃; take-≃; ≃-refl; conn-≃; rows-hot; bounded-≃;
  switch-≃; exhaust-≃)
open import adequacy.Bound using (Empty; empty-any; EndLast; Roots; Rooted; Live; G; GL; GLn; LnBody; SrcG; Held; live;
  mergeG-map; Told; ToldL)

open _≃_

------------------------------------------------------------------------
-- Rows owed up a frame

rowsL-ʳ++ : ∀ {Γ A} {ρ : DenEnv Γ} (xs : List (St Γ A)) {ys} → rowsL ρ (xs ʳ++ ys) ≡ rowsL ρ xs ʳ++ rowsL ρ ys
rowsL-ʳ++ []       = refl
rowsL-ʳ++ (x ∷ xs) = rowsL-ʳ++ xs

≡→≃ : ∀ {A} {t u : EmissionSet A} → t ≡ u → t ≃ u
≡→≃ refl = ≃-refl

module _ {A B : Set} (L : A → Pos → EmissionSet B) {O : EmissionSet A} {d : Bool} {n : ℕ} {Ls : List (EmissionSet B)} where
  -- No part owing a row: the merge owes none.
  flat-empty : Empty O → Each Empty Ls → Empty (Flat.JoinT L O d n Ls)
  flat-empty eo el (Flat.val r)       = eo r
  flat-empty eo el (Flat.step r)      = eo r
  flat-empty eo el (Flat.opin r)      = eo r
  flat-empty eo el (Flat.oend r _)    = eo r
  flat-empty eo el (Flat.opass r _)   = eo r
  flat-empty eo el (Flat.lane r _ _ _ _)  = eo r
  flat-empty eo el (Flat.lend r _ _ _ _ _)  = eo r
  flat-empty eo el (Flat.lpass r _ _ _ _ _) = eo r
  flat-empty eo el (Flat.hand _ _ _ _ ())
  flat-empty eo el (Flat.left r _ _ _ _) = eo r
  flat-empty eo el (Flat.run x _)     = empty-any Ls el x
  flat-empty eo el (Flat.rend x _ _)  = empty-any Ls el x
  flat-empty eo el (Flat.rpass x _ _) = empty-any Ls el x
  flat-empty eo el (Flat.rhand _ ())

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
    held : Held s → Held s′
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

postulate
  -- A BINDER'S GOOD BODY, UP TO THE SAME ROWS: a body reads its binder
  -- only through the rows it holds, as `rows-hot` has it of its rows.
  good-hot : ∀ {Γ X B} {t u : EmissionSet X} (k : CS) (ρ : DenEnv Γ) (b : St (X ∷ Γ) B) → t ≃ u → ∀ v → G (Hot t k ∷ᴬ ρ) v b → G (Hot u k ∷ᴬ ρ) v b

-- A completed source owing nothing, up to the same rows.
spent-≃ : ∀ {A} {t u : EmissionSet A} {P : Set} v → t ≃ u → Live v (P → Empty t) → Live v (P → Empty u)
spent-≃ true  eq sp h = empty-≃ eq (sp h)
spent-≃ false eq sp   = tt

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
