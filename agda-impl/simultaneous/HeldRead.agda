{-# OPTIONS --guardedness #-}

-- A BOUND BINDER'S READER HOLDS.  A `connected` elaborates to a reader
-- of the binder's annotated source, read hot past the connect.  Each row
-- the reader shows is a row of the source moved below where the source
-- showed it, or a begin it sends joining the source's routes; so its
-- marks route, its values and ends are early, and its counts are the
-- source's (`HeldJoin`).
module simultaneous.HeldRead where

open import Data.List using (_∷_; [_])
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (lookup) renaming ([] to []ᵉ; _∷_ to _∷ᵉ_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import Tree using (connected)
open import denotation.Position using (Pos; Path; root; _≟ᵖ_; ix; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (EmissionSet; Den; enter; ⟦_⟧; out; end)
open import denotation.Laws.Worlds using (ok-step; ⊑-inside; inside-⊑; ⊑-trans; _⊑_)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.InstEmit using (instEmit; value; mark; begin; over; completed)
open import simultaneous.Relations using (Met)
open import simultaneous.Routed using (Held; Early; Ex; Sync; Idle; Rest; nameOf; r-begin; Routing; Valued; opos)
open import simultaneous.Readings using (rootOf)
open import simultaneous.Relabel using (Same; same-mark; same-value)
open import simultaneous.HeldConnect using (rootOf-ext; early-inst)
open import simultaneous.HeldTake using (name-ext; ex-ext)
open import simultaneous.HeldComb using (ev)
open import simultaneous.HeldBase using (Bound; IH; ih)
open import simultaneous.HeldJoin using (Joined; module Join)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; reader)

-- The reader of a binder's meaning.
RD : ∀ {X} → Den (AIE X) → Den (IE X)
RD d = ⟦ reader (connected (here refl)) ⟧ (d ∷ᵉ []ᵉ)

-- Where the binder's source is subscribed: under the connect's source,
-- under the annotation's own connect.
s₀ : ∀ {X} {d : Den (AIE X)} {cs} → Bound d cs → Pos
s₀ b = (Bound.at b ⊕ [ ix 1 ]) ⊕ [ ix 1 ]

-- The binder's source, subscribed there.
Src : ∀ {X} {d : Den (AIE X)} {cs} → Bound d cs → EmissionSet (IE X)
Src b = enter (ev (Bound.m b) (Bound.src b) (Bound.env b)) (s₀ b)

-- A reader row lies below the source row it shows.
Rl : Pos → Pos → Set
Rl y′ y = Σ Path λ zs → y′ ≡ y ⊕ zs

postulate
  -- A row the reader shows: a source row moved below, or a join.
  read-row  : ∀ {X} {d : Den (AIE X)} {cs} (b : Bound d cs) p {y} {x : IE X} → enter (RD d) p y (out x)
            → (Σ Pos λ y₀ → Σ (IE X) λ x₀ → Rl y y₀ × Src b y₀ (out x₀) × Same x x₀)
              ⊎ x ≡ instEmit (mark begin) (nameOf y)
  -- The reader ends below the source's end, or in its own subscribe.
  read-end  : ∀ {X} {d : Den (AIE X)} {cs} (b : Bound d cs) p {y} → enter (RD d) p y end
            → (Σ Pos λ y₀ → Rl y y₀ × Src b y₀ end) ⊎ (Σ Path λ zs → y ≡ p ⊕ zs)
  -- A run the reader meets is one of the source's, joined late.
  read-back : ∀ {X} {d : Den (AIE X)} {cs} (b : Bound d cs) p {rs′} → Met (enter (RD d) p) rs′
            → Joined (Src b) Rl (p ∷ cs) rs′
  read-idle : ∀ {X} {d : Den (AIE X)} {cs} (b : Bound d cs) p → Idle (enter (RD d) p)
  read-rest : ∀ {X} {d : Den (AIE X)} {cs} (b : Bound d cs) p → Rest (enter (RD d) p)

sync-up : ∀ {c y} zs → Sync (c ⊕ zs) y → Sync c y
sync-up {c} {y} zs (ins , rt) =
  ⊑-inside {c} {y} (⊑-trans {c} {c ⊕ zs} {y} (zs , refl) (inside-⊑ (c ⊕ zs) y ins)) , trans rt (rootOf-ext c zs)

∈-ex : ∀ {cs c y} → c ∈ cs → Sync c y → Ex cs y
∈-ex (here refl) s = here s
∈-ex (there i)   s = there (∈-ex i s)

sub-ex : ∀ {os cs y} → (∀ {c} → c ∈ os → c ∈ cs) → Ex os y → Ex cs y
sub-ex f (here s)  = ∈-ex (f (here refl)) s
sub-ex f (there e) = sub-ex (λ i → f (there i)) e

module Reader {X} {d : Den (AIE X)} {cs} (b : Bound d cs) (p : Pos) (ep : Early p) where

  HS : Held (Src b) (s₀ b ∷ Bound.outer b)
  HS = Bound.held b (s₀ b) (ok-step (Bound.at b ⊕ [ ix 1 ]) (ok-step (Bound.at b) (Bound.ok b)))
         (early-inst [ ix 1 ] (early-inst [ ix 1 ] (Bound.ep b)))

  T′ : EmissionSet (IE X)
  T′ = enter (RD d) p

  rt : ∀ {y′ y} → Rl y′ y → rootOf y′ ≡ rootOf y
  rt {y = y} (zs , refl) = rootOf-ext y zs

  lift : ∀ {y} → Ex (s₀ b ∷ Bound.outer b) y → Ex (p ∷ cs) y
  lift {y} (here s) = there (∈-ex (Bound.under b (here refl))
    (sync-up {Bound.at b} {y} [ ix 1 ] (sync-up {Bound.at b ⊕ [ ix 1 ]} {y} [ ix 1 ] s)))
  lift (there e) = there (sub-ex (λ i → Bound.under b (there i)) e)

  exR : ∀ {y′ y} → Rl y′ y → Ex (s₀ b ∷ Bound.outer b) y → Ex (p ∷ cs) y′
  exR (zs , refl) e = lift (ex-ext zs e)

  named : ∀ {y n} → T′ y (out (instEmit (mark begin) n)) → n ≡ nameOf y
  named x with read-row b p x
  ... | inj₁ (y₀ , _ , (zs , refl) , s , same-mark e) = trans (e refl) (trans (Held.named HS s) (sym (name-ext y₀ zs)))
  ... | inj₂ refl = refl

  ends : ∀ {y} → T′ y end → Early y
  ends x with read-end b p x
  ... | inj₁ (_ , (zs , refl) , s) = early-inst zs (Held.ends HS s)
  ... | inj₂ (zs , refl)           = early-inst zs ep

  module J = Join Rl rt exR named (read-back b p) HS

  held : Held T′ (p ∷ cs)
  held = record
    { named   = named
    ; covered = J.covered′
    ; exact   = J.exact′
    ; routing = routing
    ; shut    = J.shut′
    ; early   = early
    ; ends    = ends
    ; done    = done
    ; late    = late
    ; idle    = read-idle b p
    ; rest    = read-rest b p }
    where
      routing : ∀ {y m n} → T′ y (out (instEmit (mark m) n)) → Routing m
      routing x with read-row b p x
      ... | inj₁ (_ , _ , _ , s , same-mark _) = Held.routing HS s
      ... | inj₂ refl = r-begin
      early : ∀ {y a n} → T′ y (out (instEmit (value a) n)) → Early y
      early x with read-row b p x
      ... | inj₁ (_ , _ , (zs , refl) , s , same-value) = early-inst zs (Held.early HS s)
      ... | inj₂ ()
      done : ∀ {y n} → T′ y (out (instEmit (mark completed) n)) → Early y
      done x with read-row b p x
      ... | inj₁ (_ , _ , (zs , refl) , s , same-mark _) = early-inst zs (Held.done HS s)
      ... | inj₂ ()
      late : ∀ {y n} → T′ y (out (instEmit (mark over) n)) → Valued (rootOf y) × opos (rootOf y) ⊑ y
      late x with read-row b p x
      ... | inj₁ (y₀ , _ , (zs , refl) , s , same-mark _) =
        let (v , o) = Held.late HS s
        in subst (λ r → Valued r × opos r ⊑ (y₀ ⊕ zs)) (sym (rootOf-ext y₀ zs)) (v , ⊑-trans o (zs , refl))
      ... | inj₂ ()

held-connected : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (i : A ∈ Γ) → IH m ρ (connected i)
held-connected nothing  ρ i = ih λ env cs g eh p ok ep → Reader.held (eh i) p ep
held-connected (just n) ρ i = ih λ env cs g eh p ok ep → Reader.held (eh i) p ep
