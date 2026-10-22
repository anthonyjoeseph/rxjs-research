{-# OPTIONS --guardedness --large-indices #-}

-- SPIKE 3's EVIDENCE: each program run on the spike and on today's pure
-- machine, values AND positions compared by `refl`.
module spike.Differential3 where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; _+_; _*_; _<ᵇ_)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Data.Maybe using (nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Tree as T
open import Tree using (mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.MonotonicList.Events using (Timeline; Pos)
open import operation.PureObservable using (PureObs; module Pure)
open import operation.Machine using (module Machine)
open import spike.StateTree3 as S using (Ev; nx; cp; load; runN)

module Today (R : Set) where
  open Machine R using (Read; reading; trace; begin)
  open Pure R using (End; finished)

  mapL : ∀ {X Y : Set} → (X → Y) → List X → List Y
  mapL f []       = []
  mapL f (x ∷ xs) = f x ∷ mapL f xs

  ended : End → List (Ev R)
  ended finished = [ cp ]
  ended _        = []

  today : ℕ → PureObs [] R → List (Ev R)
  today n o = mapL (λ x → nx (proj₂ x)) (Read.log r) ++ ended (Read.ending r)
    where r = reading n 0 (trace (begin o))

  places : ℕ → PureObs [] R → List Pos
  places n o = Read.marks (reading n 0 (trace (begin o)))

open Today ℕ

shown : PureObs [] ℕ → List (Pos × Ev ℕ)
shown o = runN 3000 (load o)

spike : PureObs [] ℕ → List (Ev ℕ)
spike o = mapL proj₂ (shown o)

-- where the spike shows each value, and its completion
at : PureObs [] ℕ → List Pos
at o = mapL proj₁ (shown o)

-- where today's machine shows them
then : PureObs [] ℕ → List Pos
then o = places 3000 o

nowadays : PureObs [] ℕ → List (Ev ℕ)
nowadays o = today 3000 o

ofl : List ℕ → PureObs [] ℕ
ofl = T.of

-- takeWhile, exclusive, over an of
p1 : PureObs [] ℕ
p1 = T.takeWhile false (_<ᵇ 3) (ofl (1 ∷ 2 ∷ 3 ∷ 4 ∷ []))

t1 : spike p1 ≡ nowadays p1
t1 = refl

t1′ : spike p1 ≡ nx 1 ∷ nx 2 ∷ cp ∷ []
t1′ = refl

-- takeWhile, inclusive, over a merge: cut inside a lane's burst
p2 : PureObs [] ℕ
p2 = T.takeWhile true (_<ᵇ 3) (T.flatMap (mergeᶠ nothing) (λ x → ofl (x ∷ x + 10 ∷ [])) (ofl (1 ∷ 2 ∷ 3 ∷ 4 ∷ [])))

t2 : spike p2 ≡ nowadays p2
t2 = refl

-- Lanes that live on a subject: merge, switch, exhaust.
lanes : T.FlatOp → PureObs [] ℕ
lanes op = T.connect (ofl (1 ∷ 2 ∷ 3 ∷ []))
  (T.flatMap op (λ x → T.map (λ y → x * 10 + y) (T.connected (here refl))) (T.of (1 ∷ 2 ∷ [])))

t3 : spike (lanes (mergeᶠ nothing)) ≡ nowadays (lanes (mergeᶠ nothing))
t3 = refl

t4 : spike (lanes switchᶠ) ≡ nowadays (lanes switchᶠ)
t4 = refl

t5 : spike (lanes exhaustᶠ) ≡ nowadays (lanes exhaustᶠ)
t5 = refl

-- The body completing first: the source cut, its burst run out.
p6 : PureObs [] ℕ
p6 = T.connect (ofl (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])) (T.takeWhile false (_<ᵇ 3) (T.connected (here refl)))

t6 : spike p6 ≡ nowadays p6
t6 = refl

-- Two binders, joined from inside a lane, one through `there`.
p7 : PureObs [] ℕ
p7 = T.connect (ofl (1 ∷ 2 ∷ []))
       (T.connect (T.map (_* 10) (T.connected (here refl)))
         (T.flatMap (mergeᶠ nothing)
           (λ b → if b then T.connected (here refl) else T.map (_+ 100) (T.connected (there (here refl))))
           (T.of (true ∷ false ∷ []))))

t7 : spike p7 ≡ nowadays p7
t7 = refl

-- Synchronous recursion through `defer`, cut by a takeWhile.
p8 : PureObs [] ℕ
p8 = T.takeWhile false (_<ᵇ 4) (T.scan _+_ 0 T.ones)

t8 : spike p8 ≡ nowadays p8
t8 = refl

-- A late joiner: the subject already complete.
p9 : PureObs [] ℕ
p9 = T.connect (ofl (1 ∷ 2 ∷ []))
       (T.flatMap (mergeᶠ nothing) (λ _ → T.connected (here refl)) (T.connected (here refl)))

t9 : spike p9 ≡ nowadays p9
t9 = refl

-- empty, and a switch whose lanes run synchronously
p10 : PureObs [] ℕ
p10 = T.flatMap switchᶠ (λ x → if x <ᵇ 2 then T.empty else ofl (x ∷ x ∷ [])) (ofl (1 ∷ 2 ∷ 3 ∷ []))

t10 : spike p10 ≡ nowadays p10
t10 = refl

-- Pinned, so agreement is not two empty runs.
t3′ : spike (lanes (mergeᶠ nothing)) ≡ nx 11 ∷ nx 21 ∷ nx 12 ∷ nx 22 ∷ nx 13 ∷ nx 23 ∷ cp ∷ []
t3′ = refl

t4′ : spike (lanes switchᶠ) ≡ nx 21 ∷ nx 22 ∷ nx 23 ∷ cp ∷ []
t4′ = refl

t5′ : spike (lanes exhaustᶠ) ≡ nx 11 ∷ nx 12 ∷ nx 13 ∷ cp ∷ []
t5′ = refl

t8′ : spike p8 ≡ nx 1 ∷ nx 2 ∷ nx 3 ∷ cp ∷ []
t8′ = refl

-- Positions: each value's, and the completion's, as today's ghost places them.
q1 : at p1 ≡ then p1
q1 = refl

q2 : at p2 ≡ then p2
q2 = refl

q3 : at (lanes (mergeᶠ nothing)) ≡ then (lanes (mergeᶠ nothing))
q3 = refl

q4 : at (lanes switchᶠ) ≡ then (lanes switchᶠ)
q4 = refl

q5 : at (lanes exhaustᶠ) ≡ then (lanes exhaustᶠ)
q5 = refl

q6 : at p6 ≡ then p6
q6 = refl

q7 : at p7 ≡ then p7
q7 = refl

q8 : at p8 ≡ then p8
q8 = refl

q9 : at p9 ≡ then p9
q9 = refl

q10 : at p10 ≡ then p10
q10 = refl
