{-# OPTIONS --guardedness #-}

-- A GENERATABLE PROGRAM: the tree's primitives, with `Tm` wherever the
-- tree takes a function and a finite script wherever it takes a cold.
-- First-order, so it can be generated, printed and sent to another
-- runtime.  `toObs` is the only bridge to the tree, and the tree never
-- sees this module.
--
-- Contexts: `Γ` shares in scope, `Δᵍ` recursion variables bound but not
-- yet usable, `Δ` usable ones, `Θ` values (an element, inside a lane).
-- `μ` binds into `Δᵍ`, and `defer` is the one gate moving `Δᵍ` into `Δ`,
-- so an unguarded self-reference is a type error rather than a hang.
module quickcheck.Code where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _++_) renaming (map to mapL)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; []; _∷_; lookup) renaming (map to mapAll)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Level using (lift)
open import Relation.Binary.PropositionalEquality using (refl)

open import AbstractObservable as T using (Obs; Later; renameLater)
open import MonotonicList using (ML; Burst; Burst∞; ML∞; done; quiet; at; emit; close; Timeline)
open import quickcheck.Ty
open import quickcheck.Tm

-- A cold, as data: frames at offsets from subscribe, then complete or not.
record Script (t : Ty) : Set where
  constructor script
  field
    frames    : List (ℕ × List ⟦ t ⟧ᵀ)
    completes : Bool

data Code (Γ Δᵍ Δ Θ : List Ty) : Ty → Set where
  cold      : ∀ {t} → Script t → Code Γ Δᵍ Δ Θ t
  empty     : ∀ {t} → Code Γ Δᵍ Δ Θ t
  of        : ∀ {t} → List (Tm Θ t) → Code Γ Δᵍ Δ Θ t
  map       : ∀ {s t} → Tm (s ∷ Θ) t → Code Γ Δᵍ Δ Θ s → Code Γ Δᵍ Δ Θ t
  -- the element, then the accumulator
  scan      : ∀ {s t} → Tm (s ∷ t ∷ Θ) t → Tm Θ t → Code Γ Δᵍ Δ Θ s → Code Γ Δᵍ Δ Θ t
  takeWhile : ∀ {t} → Tm (t ∷ Θ) boolᵗ → Code Γ Δᵍ Δ Θ t → Code Γ Δᵍ Δ Θ t
  -- per element: its echo, whether it opens a lane, and that lane
  flatten   : ∀ {s t} → T.FlatOp → Tm (s ∷ Θ) (maybeᵗ t) → Tm (s ∷ Θ) boolᵗ
            → Code Γ Δᵍ Δ (s ∷ Θ) t → Code Γ Δᵍ Δ Θ s → Code Γ Δᵍ Δ Θ t
  share     : ∀ {s t} → Code Γ Δᵍ Δ Θ s → Code (s ∷ Γ) Δᵍ Δ Θ t → Code Γ Δᵍ Δ Θ t
  shared    : ∀ {t} → t ∈ Γ → Code Γ Δᵍ Δ Θ t
  μ         : ∀ {t} → Code Γ (t ∷ Δᵍ) Δ Θ t → Code Γ Δᵍ Δ Θ t
  var       : ∀ {t} → t ∈ Δ → Code Γ Δᵍ Δ Θ t
  defer     : ∀ {t} → Code Γ [] (Δᵍ ++ Δ) Θ t → Code Γ Δᵍ Δ Θ t

-- A whole program.
Prog : Ty → Set
Prog = Code [] [] [] []

------------------------------------------------------------------------
-- To the tree

⟦_⟧ᴳ : List Ty → List Set
⟦_⟧ᴳ = mapL ⟦_⟧ᵀ

-- How a runtime realises a scripted cold.
Leaf : (Set → Set₁) → Set₁
Leaf C = ∀ {t} → Script t → C ⟦ t ⟧ᵀ

-- A recursion variable means the recursive program, not yet unfolded.
Rec : (Set → Set₁) → List Ty → List Ty → Set₁
Rec C Γ = All λ t → Later C ⟦ Γ ⟧ᴳ ⟦ t ⟧ᵀ

private
  mem : ∀ {t Γ} → t ∈ Γ → ⟦ t ⟧ᵀ ∈ ⟦ Γ ⟧ᴳ
  mem (here refl) = here refl
  mem (there i)   = there (mem i)

  maybe : ∀ {t} → ⟦ maybeᵗ t ⟧ᵀ → Maybe ⟦ t ⟧ᵀ
  maybe (inj₁ _) = nothing
  maybe (inj₂ x) = just x

-- FUEL: how many times any one `μ` may unfold along a path.  The
-- unfolded program is infinite, and Agda accepts a knot only when its
-- self-reference is guarded by a copattern, never when passed as an
-- argument; so a program is tested through a finite unfolding, cut at
-- `never`.  Every runtime is handed the SAME cut tree, so a comparison
-- between them is exact, and agreement up to the cut is all a finite
-- trace observes anyway.
mutual
  toObs : ∀ {C Γ Δᵍ Δ Θ t} → Leaf C → ℕ → Code Γ Δᵍ Δ Θ t
        → Rec C Γ Δᵍ → Rec C Γ Δ → Vals Θ → Obs C ⟦ Γ ⟧ᴳ ⟦ t ⟧ᵀ
  toObs leaf n (cold c)          g d θ = T.cold (leaf c)
  toObs leaf n empty           g d θ = T.empty
  toObs leaf n (of ts)           g d θ = T.of (mapL (λ x → ⟦ x ⟧ᵗ θ) ts)
  toObs leaf n (map f s)         g d θ = T.map (λ a → ⟦ f ⟧ᵗ (a ∷ θ)) (toObs leaf n s g d θ)
  toObs leaf n (scan f z s)      g d θ = T.scan (λ acc a → ⟦ f ⟧ᵗ (a ∷ acc ∷ θ)) (⟦ z ⟧ᵗ θ) (toObs leaf n s g d θ)
  toObs leaf n (takeWhile p s)   g d θ = T.takeWhile (λ a → ⟦ p ⟧ᵗ (a ∷ θ)) (toObs leaf n s g d θ)
  toObs leaf n (flatten op e h l s) g d θ =
    T.flatten op (λ a → maybe (⟦ e ⟧ᵗ (a ∷ θ)) , (if ⟦ h ⟧ᵗ (a ∷ θ) then just (toObs leaf n l g d (a ∷ θ)) else nothing))
                 (toObs leaf n s g d θ)
  toObs leaf n (share s b)       g d θ = T.share (toObs leaf n s g d θ) (toObs leaf n b (weaken g) (weaken d) θ)
  toObs leaf n (shared i)        g d θ = T.shared (mem i)
  toObs leaf n (μ c)             g d θ = toObs leaf n c (knot leaf n c g d θ ∷ g) d θ
  toObs leaf n (var i)           g d θ = Later.force (lookup d i)
  toObs leaf n (defer c)         g d θ = T.defer (later leaf n c g d θ)

  -- the recursive program, unfolded only when forced
  knot : ∀ {C Γ Δᵍ Δ Θ t} → Leaf C → ℕ → Code Γ (t ∷ Δᵍ) Δ Θ t
       → Rec C Γ Δᵍ → Rec C Γ Δ → Vals Θ → Later C ⟦ Γ ⟧ᴳ ⟦ t ⟧ᵀ
  knot leaf zero    c g d θ .Later.force = T.cold (leaf (script [] false))
  knot leaf (suc n) c g d θ .Later.force = toObs leaf n c (knot leaf n c g d θ ∷ g) d θ

  later : ∀ {C Γ Δᵍ Δ Θ t} → Leaf C → ℕ → Code Γ [] (Δᵍ ++ Δ) Θ t
        → Rec C Γ Δᵍ → Rec C Γ Δ → Vals Θ → Later C ⟦ Γ ⟧ᴳ ⟦ t ⟧ᵀ
  later leaf n c g d θ .Later.force = toObs leaf n c [] (++⁺ g d) θ

  -- a recursion variable bound outside a `share` is used inside it
  weaken : ∀ {C Γ Δ s} → Rec C Γ Δ → Rec C (s ∷ Γ) Δ
  weaken = mapAll (renameLater there)

------------------------------------------------------------------------
-- A script as a timeline

mutual
  scriptML : ∀ {A} → List (ℕ × List A) → Bool → ML A
  scriptML []               true  = done
  scriptML []               false = quiet
  scriptML ((t , xs) ∷ fs)  c     = at t (burst xs fs c)

  burst : ∀ {A} → List A → List (ℕ × List A) → Bool → Burst A
  burst []       fs c = close λ where .ML∞.force → scriptML fs c
  burst (x ∷ xs) fs c = emit x λ where .Burst∞.force → burst xs fs c

timeline : Leaf Timeline
timeline (script fs c) = lift (scriptML fs c)
