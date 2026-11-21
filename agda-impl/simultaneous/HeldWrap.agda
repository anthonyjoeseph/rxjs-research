{-# OPTIONS --guardedness #-}

-- THE WRAPPED PROGRAM HOLDS.  The program, completed by a mark where it
-- ends, merged beside the subscribe mark and cut after the completion:
-- each layer holds what the one below it holds, and the completion mark
-- carries its end's route down to the cut, where the take ends.
module simultaneous.HeldWrap where

open import Data.Bool using (true; T; not)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Relation.Unary.All using () renaming ([] to []ᵉ; _∷_ to _∷ᵉ_)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Tree using (Obs; cold; merge; of; connected)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (refl)
open import denotation.Position using (Pos; root; _≟ᵖ_; ix; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (EmissionSet; out; Den; hot; enter; ⟦_⟧; module Op; module Connect; module Connecting)
open import denotation.Laws using (inv-⟦⟧; good-cons)
open import denotation.Laws.Shows using (k-shows)
open import denotation.Laws.ShowsEv using (sk-⟦⟧)
open import denotation.Laws.Worlds using (Hots; InvAt; InvD; Ok; Lawful; _∪ʰ_; ok-step)
open import simultaneous.InstEmit using (instEmit; value; mark; begin; stop; over; outerOpen; outerClose; laneStart; carry; laneDone;
  burstEnd; outerDone; subscribed; completed)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Relations using (Met)
open import simultaneous.Routed using (Held; HeldD; Early; Ex; cnt; nameOf)
open import simultaneous.HeldTake using (module Holds; Inert; i-done)
open import simultaneous.HeldConnect using (held-conn; module ConnRun; sync-body)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; marked; unfinished; completing; wrapped; concatˢ)

-- WHERE A STREAM COMPLETES, A ROUTE OF ITS INSTANT IS HELD: its
-- completion mark is counted for as an end is, and lies early.
record Closes {A : Set} (t : EmissionSet (IE A)) (cs : List Pos) : Set where
  field
    covered : ∀ {rs} → Met t rs → ∀ r₁ {y n} r₂ → rs ≡ r₁ ++ (y , out (instEmit (mark completed) n)) ∷ r₂ → ¬ Ex cs y
            → Σ ℕ λ k → cnt r₁ ≡ (nameOf y , suc k)
    early   : ∀ {y n} → t y (out (instEmit (mark completed) n)) → Early y

-- Where the merge subscribes the completed program.
sb₀ : Pos
sb₀ = (root ⊕ [ ix 0 ]) ⊕ [ ix 1 ]

-- The completed program beside the subscribe mark.
beside : ∀ {A} → Obs Timeline [] (IE A) → Den (IE A)
beside s = ⟦ merge (completing s) (cold (lone (marked subscribed))) ⟧ []ᵉ

-- A TAKE CUT AFTER THE COMPLETION holds what its source holds.
held-until : ∀ {X} (d : Den (IE X)) {H} p cs → InvAt H p (enter d p) → Held (enter d p) cs → Closes (enter d p) cs
           → Held (enter (Op.takeWhile true unfinished d) p) cs
held-until {X} d p cs iv h c = Holds.holds true unfinished d cs p iv h fails fcov fearly
  where
    fails : ∀ {x : IE X} → T (not (unfinished x)) → Inert x
    fails {instEmit (mark completed) _}  _ = i-done
    fails {instEmit (value _) _}         ()
    fails {instEmit (mark begin) _}      ()
    fails {instEmit (mark stop) _}       ()
    fails {instEmit (mark over) _}       ()
    fails {instEmit (mark outerOpen) _}  ()
    fails {instEmit (mark outerClose) _} ()
    fails {instEmit (mark laneStart) _}  ()
    fails {instEmit (mark carry) _}      ()
    fails {instEmit (mark laneDone) _}   ()
    fails {instEmit (mark burstEnd) _}   ()
    fails {instEmit (mark outerDone) _}  ()
    fails {instEmit (mark subscribed) _} ()

    fcov : ∀ {rs} → Met (enter d p) rs → ∀ r₁ {y x} r₂ → rs ≡ r₁ ++ (y , out x) ∷ r₂ → T (not (unfinished x)) → ¬ Ex cs y
         → Σ ℕ λ k → cnt r₁ ≡ (nameOf y , suc k)
    fcov m r₁ r₂ eq nk nx with fails nk
    ... | i-done = Closes.covered c m r₁ r₂ eq nx

    fearly : ∀ {y x} → enter d p y (out x) → T (not (unfinished x)) → Early y
    fearly x nk with fails nk
    ... | i-done = Closes.early c x

-- What completes a source read hot: its rows, then the completion mark.
closing : ∀ {A} → Den (IE A) → Den (IE A)
closing h = ⟦ concatˢ (connected (here refl)) (of (marked completed ∷ [])) ⟧ (h ∷ᵉ []ᵉ)

postulate
  -- READ HOT FROM BEFORE ITS FIRST ROW, A SOURCE COMPLETED BY A MARK holds
  -- what the source holds, and its mark lies where its end did.
  held-closing : ∀ {A} (D : Den (IE A)) {H} p cs → InvD H D → Ok H p → Held (enter D (p ⊕ [ ix 1 ])) ((p ⊕ [ ix 1 ]) ∷ cs)
               → Held (Connect.β D closing p) ((p ⊕ [ ix 0 ]) ∷ p ∷ cs) × Closes (Connect.β D closing p) ((p ⊕ [ ix 0 ]) ∷ p ∷ cs)

-- A PROGRAM COMPLETED BY A MARK holds what it holds, and its mark lies
-- where its end did.
held-completing : ∀ {A} (s : Obs Timeline [] (IE A)) p cs → Ok (Hots []ᵉ) p
                → Held (enter (⟦ s ⟧ []ᵉ) (p ⊕ [ ix 1 ])) ((p ⊕ [ ix 1 ]) ∷ cs)
                → Held (enter (⟦ completing s ⟧ []ᵉ) p) (p ∷ cs) × Closes (enter (⟦ completing s ⟧ []ᵉ) p) (p ∷ cs)
held-completing s p cs ok h = held-conn D closing Is IF p ok cs sh (proj₁ B) , record { covered = covered ; early = early }
  where
    D = ⟦ s ⟧ []ᵉ
    Is = inv-⟦⟧ s []ᵉ (λ ())

    IF : ∀ {t} → Lawful t → InvD (Hots []ᵉ ∪ʰ t) (closing (hot t))
    IF L = inv-⟦⟧ (concatˢ (connected (here refl)) (of (marked completed ∷ []))) (hot _ ∷ᵉ []ᵉ) (good-cons L (λ ()))

    sh = k-shows λ n → sk-⟦⟧ n s []ᵉ (λ ()) (p ⊕ [ ix 1 ]) (ok-step p ok)
    B = held-closing D p cs Is ok h

    open ConnRun D closing Is IF p ok sh using (C; back)

    covered : ∀ {rs} → Met C rs → ∀ r₁ {y n} r₂ → rs ≡ r₁ ++ (y , out (instEmit (mark completed) n)) ∷ r₂ → ¬ Ex (p ∷ cs) y
            → Σ ℕ λ k → cnt r₁ ≡ (nameOf y , suc k)
    covered m r₁ r₂ eq nx = Closes.covered (proj₂ B) (back m) r₁ r₂ eq λ
      { (here sy) → nx (here (sync-body {p} sy)) ; (there x) → nx x }

    early : ∀ {y n} → C y (out (instEmit (mark completed) n)) → Early y
    early (Connecting.body y , _) = Closes.early (proj₂ B) y

postulate
  -- BESIDE THE SUBSCRIBE MARK, the completed program holds as it did.
  held-merged : ∀ {A} (s : Obs Timeline [] (IE A))
              → Held (enter (⟦ completing s ⟧ []ᵉ) sb₀) (sb₀ ∷ []) → Closes (enter (⟦ completing s ⟧ []ᵉ) sb₀) (sb₀ ∷ [])
              → Held (enter (beside s) root) (root ∷ []) × Closes (enter (beside s) root) (root ∷ [])

held-wrapped : ∀ {A} (s : Obs Timeline [] (IE A)) → HeldD (Hots []ᵉ) (⟦ s ⟧ []ᵉ) [] → Held (enter (⟦ wrapped s ⟧ []ᵉ) root) (root ∷ [])
held-wrapped s hs =
  held-until (beside s) root (root ∷ []) (inv-⟦⟧ (merge (completing s) (cold (lone (marked subscribed)))) []ᵉ (λ ()) root (tt , λ ()))
    (proj₁ M) (proj₂ M)
  where
    C = held-completing s sb₀ [] (tt , λ ()) (hs (sb₀ ⊕ [ ix 1 ]) (tt , λ ()) λ ())
    M = held-merged s (proj₁ C) (proj₂ C)
