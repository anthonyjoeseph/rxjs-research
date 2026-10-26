{-# OPTIONS --guardedness #-}

-- THE SCOPE, TESTED: every subscribed connect's source and every lane,
-- its ghost read through the ended connects in scope, in order at every
-- node `Within` descends to, in the environment its frame reads
-- (`adequacy.Engine.Scope.GhE`), at every configuration a run passes
-- through, a rising one's tree with its hole stepped and the frames
-- above not yet rewritten included.  The order is decided on a prefix of
-- each meaning; a flatMap's lanes yet to subscribe, `Apart`, and a
-- defer's or joiner's sources are not decided (err toward true).
module quickcheck.Scoped where

open import Data.Bool using (Bool; true; false; not; _∧_)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using () renaming (_∷_ to _∷ᴬ_; [] to []ᴬ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)

open import denotation.MonotonicList.Events using (Events; Pos; out; skip; end; hush; _<ᵖ_)
open import denotation.Unfold using (Node; NEnv; mapᶜ; scanᶜ; takeWhileᶜ; flatMapᶜ; connectᶜ; live; ended; meaning)
open import operation.PureObservable using (module Machine)
open Machine using (Conf; ⟨_,_,_,_⟩; St; mapS; scanS; cutS; lnS; takeS; flatS; connS; cs; CS; plug)
open import adequacy.Engine.Meaning using (gh; lanesL; srcG; srcRun)
open import adequacy.Engine.Shuts using (Shuts; none; upˢ; shutAll)
open import adequacy.Engine.Scope using (closeOf)

open import denotation.MonotonicList.Events using (Events∞)
open Events∞

private
  -- `adequacy.Placed.Order.Atop` and `Ordered`, on the first `n` events.
  atopᵇ : ∀ {A} → Pos → Events A → Bool
  atopᵇ k (out h _ _) = not (h <ᵖ k)
  atopᵇ k (skip h _)  = not (h <ᵖ k)
  atopᵇ k (end h)     = not (h <ᵖ k)
  atopᵇ k hush        = true

  orderedᵇ : ∀ {A} → ℕ → Events A → Bool
  orderedᵇ zero    _           = true
  orderedᵇ (suc n) (out k _ r) = atopᵇ k (force r) ∧ orderedᵇ n (force r)
  orderedᵇ (suc n) (skip k r)  = atopᵇ k (force r) ∧ orderedᵇ n (force r)
  orderedᵇ (suc n) (end _)     = true
  orderedᵇ (suc n) hush        = true

  depth : ℕ
  depth = 8

  -- `adequacy.Placed.Order.Placed`'s order, at every node it descends to.
  mutual
    placeᵇ : ∀ {Γ A} → Node Γ A → NEnv Γ → Bool
    placeᵇ n ρ = orderedᵇ depth (meaning n ρ) ∧ withinᵇ n ρ

    withinᵇ : ∀ {Γ A} → Node Γ A → NEnv Γ → Bool
    withinᵇ (mapᶜ f c)                  ρ = placeᵇ c ρ
    withinᵇ (scanᶜ f z c)               ρ = placeᵇ c ρ
    withinᵇ (takeWhileᶜ i p c)          ρ = placeᵇ c ρ
    withinᵇ (flatMapᶜ op g o ls qs pl)  ρ = placeᴹᵇ o ρ ∧ placeᴸᵇ ls ρ
    withinᵇ (connectᶜ r b (live s))     ρ = placeᵇ b (meaning s ρ ∷ᴬ ρ) ∧ placeᵇ s ρ
    withinᵇ (connectᶜ r b (ended c t))  ρ = placeᵇ b (end c ∷ᴬ ρ)
    withinᵇ _                           ρ = true

    placeᴹᵇ : ∀ {Γ A} → Maybe (Node Γ A) → NEnv Γ → Bool
    placeᴹᵇ nothing  ρ = true
    placeᴹᵇ (just c) ρ = placeᵇ c ρ

    placeᴸᵇ : ∀ {Γ A} → List (Node Γ A) → NEnv Γ → Bool
    placeᴸᵇ []       ρ = true
    placeᴸᵇ (c ∷ ns) ρ = placeᵇ c ρ ∧ placeᴸᵇ ns ρ

  -- `adequacy.Engine.Scope.GhE`'s order, the shuts and environment in scope.
  mutual
    ghᵇ : ∀ {Γ A} → Shuts Γ → NEnv Γ → St Γ A → Bool
    ghᵇ V ρ (mapS f s)              = ghᵇ V ρ s
    ghᵇ V ρ (scanS f z s)           = ghᵇ V ρ s
    ghᵇ V ρ (cutS l a s)            = ghᵇ V ρ s
    ghᵇ V ρ (lnS b s)               = ghᵇ V ρ s
    ghᵇ V ρ (takeS i q w s)         = ghᵇ V ρ s
    ghᵇ V ρ (flatS op f d n q o ls) = placeᴸᵇ (map (shutAll V) (lanesL ls)) ρ ∧ ghᵇ V ρ o ∧ ghᴸᵇ V ρ ls
    ghᵇ V ρ (connS k o b)           =
      srcᵇ V ρ k o ∧ ghᵇ V ρ o ∧ ghᵇ (closeOf (srcG k o) (upˢ V)) (srcRun (srcG k o) ρ ∷ᴬ ρ) b
    ghᵇ V ρ _                       = true

    ghᴸᵇ : ∀ {Γ B} → Shuts Γ → NEnv Γ → List (St Γ B) → Bool
    ghᴸᵇ V ρ []       = true
    ghᴸᵇ V ρ (s ∷ ls) = ghᵇ V ρ s ∧ ghᴸᵇ V ρ ls

    srcᵇ : ∀ {Γ X} → Shuts Γ → NEnv Γ → CS → St Γ X → Bool
    srcᵇ V ρ (cs false sl sa nothing as ow r en) o = placeᵇ (shutAll V (gh o)) ρ
    srcᵇ V ρ k                                   o = true

-- The whole tree of a configuration, its scope in order.
scopedᵇ : Conf ℕ → Bool
scopedᵇ ⟨ c , s , _ , _ ⟩ = ghᵇ none []ᴬ (plug c s)
