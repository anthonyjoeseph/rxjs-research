{-# OPTIONS --guardedness --large-indices #-}

-- SPIKE 5's EVIDENCE: at every quiet configuration of each program's run,
-- what the root was shown, then what the ghost's meaning still holds,
-- is the whole run.  Checked by `refl`.
module spike.GhostCheck where

open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; [_]; length)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; _+_; _*_; _<ᵇ_; _≡ᵇ_)
open import Data.Product using (_,_; _×_)
open import Data.Maybe using (nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (does)

import Tree as T
open import Tree using (mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.MonotonicList.Events using (Pos; _≟ᵖ_)
open import spike.StateTree3 using (PObs; Ev; nx; cp; load; runN; Shown)
open import spike.StateTree3Ghost using (quiets; residual; seen)

eqEv : Ev ℕ → Ev ℕ → Bool
eqEv (nx a) (nx b) = a ≡ᵇ b
eqEv cp     cp     = true
eqEv _      _      = false

eqShown : Shown ℕ → Shown ℕ → Bool
eqShown []             []             = true
eqShown ((p , a) ∷ xs) ((q , b) ∷ ys) = does (p ≟ᵖ q) ∧ eqEv a b ∧ eqShown xs ys
eqShown _              _              = false

whole : PObs [] ℕ → Shown ℕ
whole o = runN 3000 (load o)

-- Each quiet configuration's shown-then-residual, against the whole run.
kept : PObs [] ℕ → List Bool
kept o = go (quiets 3000 (load o) [])
  where
    go : List (Shown ℕ × _) → List Bool
    go []              = []
    go ((sh , k) ∷ ks) = eqShown (sh ++ seen 3000 (residual k)) (whole o) ∷ go ks

-- How many quiet configurations failed.
failures : List Bool → ℕ
failures []           = 0
failures (true ∷ bs)  = failures bs
failures (false ∷ bs) = 1 + failures bs

-- And the loaded ghost's meaning is the whole run.
from-load : PObs [] ℕ → Bool
from-load o = eqShown (seen 3000 (residual (load o))) (whole o)

ofl : List ℕ → PObs [] ℕ
ofl = T.of

p1 : PObs [] ℕ
p1 = T.takeWhile false (_<ᵇ 3) (ofl (1 ∷ 2 ∷ 3 ∷ 4 ∷ []))

p2 : PObs [] ℕ
p2 = T.takeWhile true (_<ᵇ 3) (T.flatMap (mergeᶠ nothing) (λ x → ofl (x ∷ x + 10 ∷ [])) (ofl (1 ∷ 2 ∷ 3 ∷ 4 ∷ [])))

lanes : T.FlatOp → PObs [] ℕ
lanes op = T.connect (ofl (1 ∷ 2 ∷ 3 ∷ []))
  (T.flatMap op (λ x → T.map (λ y → x * 10 + y) (T.connected (here refl))) (T.of (1 ∷ 2 ∷ [])))

p6 : PObs [] ℕ
p6 = T.connect (ofl (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])) (T.takeWhile false (_<ᵇ 3) (T.connected (here refl)))

p7 : PObs [] ℕ
p7 = T.connect (ofl (1 ∷ 2 ∷ []))
       (T.connect (T.map (_* 10) (T.connected (here refl)))
         (T.flatMap (mergeᶠ nothing)
           (λ b → if b then T.connected (here refl) else T.map (_+ 100) (T.connected (there (here refl))))
           (T.of (true ∷ false ∷ []))))

p8 : PObs [] ℕ
p8 = T.takeWhile false (_<ᵇ 4) (T.scan _+_ 0 T.ones)

p9 : PObs [] ℕ
p9 = T.connect (ofl (1 ∷ 2 ∷ []))
       (T.flatMap (mergeᶠ nothing) (λ _ → T.connected (here refl)) (T.connected (here refl)))

p10 : PObs [] ℕ
p10 = T.flatMap switchᶠ (λ x → if x <ᵇ 2 then T.empty else ofl (x ∷ x ∷ [])) (ofl (1 ∷ 2 ∷ 3 ∷ []))

-- An inclusive take in every lane, on one subject: each owes its end
-- after its failing value, while the subject still feeds the others.
p11 : PObs [] ℕ
p11 = T.connect (ofl (1 ∷ 2 ∷ 3 ∷ 4 ∷ []))
        (T.flatMap (mergeᶠ nothing) (λ x → T.map (_+ x) (T.takeWhile true (_<ᵇ 3) (T.connected (here refl)))) (T.of (10 ∷ 20 ∷ [])))

-- A lane joining while the subject's value is being fed: it misses that value.
p12 : PObs [] ℕ
p12 = T.connect (ofl (1 ∷ 2 ∷ 3 ∷ []))
        (T.flatMap (mergeᶠ nothing) (λ x → T.map (λ y → x * 10 + y) (T.connected (here refl))) (T.connected (here refl)))

-- An exhaust whose lanes outlive its outer, joined to the subject.
p13 : PObs [] ℕ
p13 = T.connect (ofl (1 ∷ 2 ∷ 3 ∷ []))
        (T.flatMap exhaustᶠ (λ x → T.takeWhile false (_<ᵇ 3) (T.connected (here refl))) (T.scan _+_ 0 (T.connected (here refl))))

counts : List ℕ
counts = failures (kept p1) ∷ failures (kept p2) ∷ failures (kept (lanes (mergeᶠ nothing)))
       ∷ failures (kept (lanes switchᶠ)) ∷ failures (kept (lanes exhaustᶠ)) ∷ failures (kept p6)
       ∷ failures (kept p7) ∷ failures (kept p8) ∷ failures (kept p9) ∷ failures (kept p10)
       ∷ failures (kept p11) ∷ failures (kept p12) ∷ failures (kept p13) ∷ []

checked : counts ≡ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []
checked = refl

-- Not vacuous: each run passes several quiet configurations ...
quiets-many : (2 <ᵇ length (kept p1)) ∧ (2 <ᵇ length (kept p2)) ∧ (2 <ᵇ length (kept (lanes (mergeᶠ nothing))))
            ∧ (2 <ᵇ length (kept p6)) ∧ (2 <ᵇ length (kept p7)) ∧ (2 <ᵇ length (kept p8))
            ∧ (2 <ᵇ length (kept p9)) ∧ (2 <ᵇ length (kept p10)) ∧ (2 <ᵇ length (kept p11))
            ∧ (2 <ᵇ length (kept p12)) ∧ (2 <ᵇ length (kept p13)) ≡ true
quiets-many = refl

-- ... and forgetting what the root was shown fails at most of them.
forgetful : PObs [] ℕ → List Bool
forgetful o = go (quiets 3000 (load o) [])
  where
    go : List (Shown ℕ × _) → List Bool
    go []              = []
    go ((sh , k) ∷ ks) = eqShown (seen 3000 (residual k)) (whole o) ∷ go ks

forgetting-fails : (1 <ᵇ failures (forgetful p1)) ∧ (1 <ᵇ failures (forgetful p7)) ∧ (1 <ᵇ failures (forgetful p8)) ≡ true
forgetting-fails = refl
