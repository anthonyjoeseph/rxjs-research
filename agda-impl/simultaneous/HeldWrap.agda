{-# OPTIONS --guardedness #-}

-- THE WRAPPED PROGRAM HOLDS.  The program, completed by a mark where it
-- ends, merged beside the subscribe mark and cut after the completion:
-- each layer holds what the one below it holds, and the completion mark
-- carries its end's route down to the cut, where the take ends.
module simultaneous.HeldWrap where

open import Data.Bool using (Bool; true; T; not; if_then_else_)
open import Data.List using ([]; _∷_; _++_; [_])
open import Data.List.Relation.Unary.All using () renaming ([] to []ᵉ; _∷_ to _∷ᵉ_)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ; _,_)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Tree using (Obs; cold; merge; of; connected)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (refl; sym; subst)
open import denotation.Position using (Pos; root; _≟ᵖ_; ix; last; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (EmissionSet; out; skip; pin; end; Den; hot; enter; Proper; Few; _≺_; _≼_; ⟦_⟧; module Op;
  module Connect)
open import denotation.Read using (Visible)
open import denotation.Laws.Modulus using (≺-trans; entered-few)
open import denotation.Laws using (inv-⟦⟧; good-cons)
open import denotation.Laws.Shows using (k-shows)
open import denotation.Laws.ShowsEv using (sk-⟦⟧)
open import denotation.Laws.Worlds using (Hots; InvAt; InvD; Ok; Lawful; Shows; _∪ʰ_; ok-step; world-after; full; ⊕-assoc)
open import simultaneous.InstEmit using (instEmit; value; mark; begin; stop; over; outerOpen; outerClose; laneStart; carry; laneDone;
  burstEnd; outerDone; subscribed; completed)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Relations using (Met)
open import simultaneous.Routed using (Held; HeldD; Early; Ex; cnt; nameOf; c-done)
open import simultaneous.HeldTake using (module Holds; Inert; i-done; HeldTo)
open import simultaneous.HeldConnect using (held-conn; held-ex)
open import simultaneous.HeldDefer using (sync-up)
open import simultaneous.HeldHot using (module HotRead)
open import simultaneous.HeldClose using (module CatClose; of-row₁; of-val₁; of-end₁)
open import simultaneous.HeldTrigger using (≺-part)
open import simultaneous.CombSent using (assoc³)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; marked; unfinished; completing; wrapped; concatˢ)

-- Where the merge subscribes the completed program.
sb₀ : Pos
sb₀ = (root ⊕ [ ix 0 ]) ⊕ [ ix 1 ]

-- The completed program beside the subscribe mark.
beside : ∀ {A} → Obs Timeline [] (IE A) → Den (IE A)
beside s = ⟦ merge (completing s) (cold (lone (marked subscribed))) ⟧ []ᵉ

-- A TAKE CUT AFTER THE COMPLETION holds what its source holds.
held-until : ∀ {X} (d : Den (IE X)) {H} p cs → InvAt H p (enter d p) → HeldTo unfinished (enter d p) cs
           → Held (enter (Op.takeWhile true unfinished d) p) cs
held-until {X} d p cs iv h = Holds.holds true unfinished d cs p iv h fails fcov fearly
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
    ... | i-done = HeldTo.covered h m r₁ r₂ eq c-done nx

    fearly : ∀ {y x} → enter d p y (out x) → T (not (unfinished x)) → Early y
    fearly x nk with fails nk
    ... | i-done = HeldTo.done h x

-- What completes a source read hot: its rows, then the completion mark.
closing : ∀ {A} → Den (IE A) → Den (IE A)
closing h = ⟦ concatˢ (connected (here refl)) (of (marked completed ∷ [])) ⟧ (h ∷ᵉ []ᵉ)

-- READ HOT FROM BEFORE ITS FIRST ROW, A SOURCE COMPLETED BY A MARK holds
-- what the source holds, and its mark lies where its end did: the reading
-- holds as the source does (`HotRead`), and the concat shows the reading
-- closed by the mark (`CatClose`).
held-closing : ∀ {A} (D : Den (IE A)) {H} p cs → InvD H D → Ok H p → Shows (enter D (p ⊕ [ ix 1 ]))
             → Held (enter D (p ⊕ [ ix 1 ])) ((p ⊕ [ ix 1 ]) ∷ cs)
             → Held (Connect.β D closing p) ((p ⊕ [ ix 0 ]) ∷ p ∷ cs)
held-closing {A} D p cs I ok sh h =
  CatClose.held G P _ HR.rd-proper HR.rd-func HR.rd-few (HR.rd-past {e₁} λ y → ≺-trans {e₁} {r} {_} e₁≺r (aft y)) HR.rd-nopin
    (of-row₁ _) (of-val₁ _) (of-end₁ _) (HR.held-hot (held-ex ex h))
  where
    P r sb e₁ : Pos
    P  = p ⊕ [ ix 0 ]
    r  = p ⊕ [ ix 1 ]
    sb = (P ⊕ [ ix 0 ]) ⊕ [ ix 1 ]
    e₁ = P ⊕ [ last ]

    S : EmissionSet (IE A)
    S = enter D r

    G : Bool → Den (IE A)
    G b = ⟦ if b then connected (here refl) else of (marked completed ∷ []) ⟧ (hot (Proper S) ∷ᵉ []ᵉ)

    IS = I r (ok-step p ok)

    aft : ∀ {y e} → S y e → r ≺ y
    aft y = world-after (InvAt.world IS y) (InvAt.real IS y)

    sb≺r : sb ≺ r
    sb≺r = subst (_≺ r) (sym (assoc³ p (ix 0) (ix 0) (ix 1))) (≺-part p (ix 0 ∷ ix 1 ∷ []) [] refl)

    e₁≺r : e₁ ≺ r
    e₁≺r = subst (_≺ r) (sym (⊕-assoc p [ ix 0 ] [ last ])) (≺-part p [ last ] [] refl)

    few-vis : ∀ {y e} → S y e → Visible e → Few S y
    few-vis {q} {out x} y _ = entered-few D r (λ {k} {e′} → full {IE A} {q} {out x} tt {k} {e′}) y
    few-vis {q} {end}   y _ = entered-few D r (λ {k} {e′} → full {IE A} {q} {end} tt {k} {e′}) y
    few-vis {e = skip}  _ ()
    few-vis {e = pin _} _ ()

    proper-vis : ∀ {c y e} → S c end → S y e → Visible e → y ≼ c
    proper-vis sc sy v cy with InvAt.quiet IS sc sy cy
    ... | _ , refl , _ = v

    module HR = HotRead S sb (InvAt.flat IS) (InvAt.func IS) (λ {y} y′ → ≺-trans {sb} {r} {y} sb≺r (aft y′)) few-vis proper-vis sh

    ex : ∀ {y} → Ex (r ∷ cs) y → Ex (P ∷ p ∷ cs) y
    ex {y} (here sy) = there (here (sync-up {p} {y} [ ix 1 ] sy))
    ex (there x)     = there (there x)

-- A PROGRAM COMPLETED BY A MARK holds what it holds, and its mark lies
-- where its end did.
held-completing : ∀ {A} (s : Obs Timeline [] (IE A)) p cs → Ok (Hots []ᵉ) p
                → Held (enter (⟦ s ⟧ []ᵉ) (p ⊕ [ ix 1 ])) ((p ⊕ [ ix 1 ]) ∷ cs)
                → Held (enter (⟦ completing s ⟧ []ᵉ) p) (p ∷ cs)
held-completing s p cs ok h = held-conn D closing Is IF p ok cs sh (held-closing D p cs Is ok sh h)
  where
    D = ⟦ s ⟧ []ᵉ
    Is = inv-⟦⟧ s []ᵉ (λ ())

    IF : ∀ {t} → Lawful t → InvD (Hots []ᵉ ∪ʰ t) (closing (hot t))
    IF L = inv-⟦⟧ (concatˢ (connected (here refl)) (of (marked completed ∷ []))) (hot _ ∷ᵉ []ᵉ) (good-cons L (λ ()))

    sh = k-shows λ n → sk-⟦⟧ n s []ᵉ (λ ()) (p ⊕ [ ix 1 ]) (ok-step p ok)

postulate
  -- BESIDE THE SUBSCRIBE MARK, the completed program holds as it did, up
  -- to its completion.  Past it the merge never ends, its end turned a
  -- skip, so idleness past the completion is not claimed.
  --
  -- DEAD ROUTE: unrestricted `Held` of the merge is false.  A program
  --   ending in a later instant holds a route of that instant at its end
  --   (`covered`), and the merge, never ending, idles past it later.
  held-merged : ∀ {A} (s : Obs Timeline [] (IE A))
              → Held (enter (⟦ completing s ⟧ []ᵉ) sb₀) (sb₀ ∷ [])
              → HeldTo unfinished (enter (beside s) root) (root ∷ [])

held-wrapped : ∀ {A} (s : Obs Timeline [] (IE A)) → HeldD (Hots []ᵉ) (⟦ s ⟧ []ᵉ) [] → Held (enter (⟦ wrapped s ⟧ []ᵉ) root) (root ∷ [])
held-wrapped s hs =
  held-until (beside s) root (root ∷ []) (inv-⟦⟧ (merge (completing s) (cold (lone (marked subscribed)))) []ᵉ (λ ()) root (tt , λ ()))
    (held-merged s (held-completing s sb₀ [] (tt , λ ()) (hs (sb₀ ⊕ [ ix 1 ]) (tt , λ ()) λ ())))
