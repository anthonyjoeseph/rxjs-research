{-# OPTIONS --guardedness #-}

-- A shut can move a burst's step out of its range, onto a rest that
-- heads before every end it tells; so `bursts-down` is false, its rests
-- twinned below `q`.  A joiner subscribed outside the
-- burst's root is told an end that beats the burst's skip from
-- outside the root, so the burst falls back to its source's rest; a
-- sibling lane's rest heads first.
module port.ShutHeadsRefuted where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (_∷_; [])
open import Data.List.Relation.Unary.Any using (here)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (just; nothing)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import denotation.MonotonicList.Events using (Pos; ix) renaming (sub to subᴾ)
import denotation.Unfold as U
import Tree as T
open import port.Told using (untold; Tells)
open import port.Strong using (module Strongly)
open Strongly ⊤ using (Heads)
open import port.Frame using (module Framing)
open Framing ⊤ using (Down; skipᵗ)

Γ : List Set
Γ = ⊤ ∷ []

-- Joined at `[ix 1]`, untold.
joiner : U.Node Γ ⊤
joiner = U.joinᶜ (here refl) (ix 1 ∷ []) [] nothing

-- Steps inside the burst's root `[ix 5]`.
inner : U.Node Γ ⊤
inner = U.ofᶜ (ix 5 ∷ []) 0 (tt ∷ [])

-- Hushed, its rest a skip at `[ix 0, ix 0]`.
early : U.Node Γ ⊤
early = U.connectᶜ {A = ⊤} [] U.idleᶜ (U.ended [] (U.ofᶜ (ix 0 ∷ []) 0 (tt ∷ [])))

t : U.Node Γ ⊤
t = U.flatMapᶜ {A = ⊤} (T.mergeᶠ nothing) (λ _ _ → U.idleᶜ) nothing (joiner ∷ inner ∷ early ∷ []) [] U.idleᶜ

b : U.Node Γ ⊤
b = U.burstingᶜ {A = ⊤} (ix 5 ∷ []) t

c q : Pos
c = ix 2 ∷ []
q = ix 2 ∷ subᴾ (ix 1 ∷ []) ∷ []

heads : Heads q b
heads refl = inj₂ refl

tells : Tells q c (untold (here refl) b)
tells = inj₁ refl ∷ []

shut-head : U.headˢ (U.step (U.shut (here refl) c b)) ≡ just (ix 0 ∷ ix 0 ∷ [])
shut-head = refl

refuted : ¬ (∀ {Γ A B q} (i : A ∈ Γ) c (b : U.Node Γ B) → Heads q b → Tells q c (untold i b) → Heads q (U.shut i c b))
refuted shut-heads with shut-heads (here refl) c b heads tells shut-head
... | inj₁ ()
... | inj₂ ()

bursts-refuted : ¬ (∀ {Γ A B q} r (t t′ : U.Node Γ A) (st st′ : U.Step Γ A) → Down q st st′ → Down q (U.restˢ {B = B} t) (U.restˢ {B = B} t′)
                   → Down {Γ} {B} q (U.burstsˢ r t st) (U.burstsˢ r t′ st′))
bursts-refuted bd with bd {B = ⊤} {q = q} (ix 5 ∷ []) t (U.shut (here refl) c t) (U.step t) (U.step (U.shut (here refl) c t))
                          (inj₂ ((λ { refl → inj₂ refl }) , (λ { refl → inj₁ refl }))) (inj₁ skipᵗ)
... | inj₁ ()
... | inj₂ (_ , h′) with h′ refl
... | inj₁ ()
... | inj₂ ()
