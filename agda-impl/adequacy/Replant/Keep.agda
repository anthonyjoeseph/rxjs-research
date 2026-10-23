{-# OPTIONS --guardedness #-}

-- THE REPLANT FRAME, KEPT: what a replant keeps besides the heads,
-- walked up the path as `adequacy.Replant` walks them — every held
-- connect past its end without a source, every joiner told no sooner,
-- every done flag read alike.  Every node above reads its path child
-- only through whether the child shows, both ways round.
module adequacy.Replant.Keep where

open import Data.Bool using (true; false; _∨_)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴸ_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (Maybe; just; nothing; is-just; is-nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; subst)
open import Relation.Nullary using (¬_)

import denotation.Unfold as U
open import denotation.MonotonicList.Events using (Pos)
open import adequacy.Told using (untold)
open import adequacy.Strong using (module Strongly)
open import adequacy.Moves using (module Moving)
open import adequacy.Replant using (module Replanting)

module Keeping (R : Set) where
  open Strongly R using (Sub; Path; PathLanes; here; in-map; in-scan; in-cut; in-lane; in-take; in-outer; in-lanes; in-source; in-body;
    this-lane; next-lane; part; seen; seenL; isTaking; connected; Untold; Ended; DoneBy; ending; takeWhileˢ; flatMapˢ; connectˢ)
  open Moving R using (plant; plantᴸ; planted; replanted)
  open Replanting R using (_⊑[_/_]_; Pred; Binds; BindsL; Bound; Heading; module Walk; thru; ∧-join; ∨-r; ∨-mono; isj; just-of; en-sub; ut-sub; EndedL; UntoldL)

  -- Every flatMap's done flag as `N` names its path: unset if named,
  -- else its outer gone.
  FlagsBy : ∀ {Γ₀ A₀} → (List ℕ → Set) → Sub Γ₀ A₀ → Set₁
  FlagsBy N t = ∀ {Γ X A op f d n qs pl π} {o : Sub Γ X} {ls : List (Sub Γ A)}
              → (ψ : Path t (flatMapˢ op f d n qs pl o ls) π) → seen ψ ≡ true
              → (N π → d ≡ false) × (¬ N π → d ≡ is-nothing (part o))

  -- The same of a flatMap's lanes, `M` naming a lane by its index and
  -- the path within it.
  FlagsByL : ∀ {Γ₀ B₀} → (ℕ → List ℕ → Set) → List (Sub Γ₀ B₀) → Set₁
  FlagsByL M ls = ∀ {Γ X A op f d n qs pl i π} {o : Sub Γ X} {ls′ : List (Sub Γ A)}
                → (ψ : PathLanes ls (flatMapˢ op f d n qs pl o ls′) i π) → seenL ψ ≡ true
                → (M i π → d ≡ false) × (¬ M i π → d ≡ is-nothing (part o))

  -- THE NODE'S LIFE, MOVED: shown on one side exactly when on the
  -- other, a take above it ending alike both ways, and below it every
  -- held connect ended and every done flag read alike.
  record Alive {Δ A} (u v : Sub Δ A) : Set₁ where
    field
      alive-back  : is-just (part v) ≡ true → is-just (part u) ≡ true
      alive-fwd   : is-just (part u) ≡ true → is-just (part v) ≡ true
      take-back   : ∀ {i p k c} → is-just (part (takeWhileˢ i p (ending k c) v)) ≡ true → is-just (part (takeWhileˢ i p (ending k c) u)) ≡ true
      take-fwd    : ∀ {i p k c} → is-just (part (takeWhileˢ i p (ending k c) u)) ≡ true → is-just (part (takeWhileˢ i p (ending k c) v)) ≡ true
      alive-ended : Ended u → Ended v
      alive-flags : ∀ N → FlagsBy N u → FlagsBy N v

  private
    nothing-back : ∀ {X : Set₁} {m m′ : Maybe X} → (is-just m′ ≡ true → is-just m ≡ true) → m ≡ nothing → m′ ≡ nothing
    nothing-back {m′ = nothing} rv _ = refl
    nothing-back {m′ = just _}  rv refl with rv refl
    ... | ()

    nothing-eq : ∀ {X : Set₁} (m m′ : Maybe X) → (is-just m ≡ true → is-just m′ ≡ true) → (is-just m′ ≡ true → is-just m ≡ true)
               → is-nothing m ≡ is-nothing m′
    nothing-eq nothing  nothing  f g = refl
    nothing-eq (just _) (just _) f g = refl
    nothing-eq nothing  (just _) f g with g refl
    ... | ()
    nothing-eq (just _) nothing  f g with f refl
    ... | ()

    -- A connect past its source's end, its body showing, shows.
    conn-ended : ∀ {Γ A B} r c₀ (rt : U.Node Γ A) {s : Maybe (U.Node Γ A)} {mb : Maybe (U.Node (A ∷ Γ) B)} {b₀}
               → s ≡ nothing → mb ≡ just b₀ → Σ _ λ n → connected r (just c₀) rt s mb ≡ just n
    conn-ended r c₀ rt refl refl = _ , refl

    ----------------------------------------------------------------------
    -- THE WALK, KEPT: `u` replanted to `v`, every node above rebuilt
    -- from its path child.

    module Up {Δ₀ A₀} {u v : Sub Δ₀ A₀} (al : Alive u v) where
      open Walk {u = u} {v = v} (Alive.alive-back al) (λ {i} {p} {k} {c} → Alive.take-back al {i} {p} {k} {c}) using (revive; shown; module Telling)

      -- Above the node, shown on one side exactly when on the other.
      alive : ∀ {Γ A π} {t : Sub Γ A} (ρ : Path t u π) → is-just (part t) ≡ true → is-just (part (plant ρ v)) ≡ true
      alive ρ =
        subst (λ x → is-just (part x) ≡ true → is-just (part (plant ρ v)) ≡ true) (replanted ρ v)
          (Walk.revive {u = v} {v = u} (Alive.alive-fwd al) (λ {i} {p} {k} {c} → Alive.take-fwd al {i} {p} {k} {c}) (planted ρ v))

      -- No held connect above the node holds a source past its end.
      mutual
        endedUp : ∀ {Γ A π} {t : Sub Γ A} (ρ : Path t u π) → Ended t → Ended (plant ρ v)
        endedUp here en = Alive.alive-ended al en
        endedUp (in-map ρ) en = λ { (in-map ψ) sn → endedUp ρ (en-sub en (in-map here) refl) ψ sn }
        endedUp (in-scan ρ) en = λ { (in-scan ψ) sn → endedUp ρ (en-sub en (in-scan here) refl) ψ sn }
        endedUp (in-cut {l = l} ρ) en =
          λ { (in-cut ψ) sn → thru l sn (λ j s′ → endedUp ρ (en-sub en (in-cut here) (∧-join j refl)) ψ s′) }
        endedUp (in-lane ρ) en = λ { (in-lane ψ) sn → endedUp ρ (en-sub en (in-lane here) refl) ψ sn }
        endedUp (in-take {tk = tk} ρ) en =
          λ { (in-take ψ) sn → thru (isTaking tk) sn (λ j s′ → endedUp ρ (en-sub en (in-take here) (∧-join j refl)) ψ s′) }
        endedUp (in-outer ρ) en = λ
          { (in-outer ψ) sn → endedUp ρ (en-sub en (in-outer here) refl) ψ sn
          ; (in-lanes ψ) sn → en (in-lanes ψ) sn }
        endedUp (in-lanes ρ) en = λ
          { (in-outer ψ) sn → en (in-outer ψ) sn
          ; (in-lanes ψ) sn → endedL ρ (λ ψ′ → en (in-lanes ψ′)) ψ sn }
        endedUp (in-source {k = k} {r = r} {e = e} {rt = rt} {b = b} ρ) en = λ
          { here _ x pe → nothing-back (revive ρ) (en here refl (proj₂ (shown (in-source {k = k} {r = r} {e = e} {rt = rt} {b = b} ρ) x)) pe)
          ; (in-source ψ) sn → thru (is-just (part b)) sn (λ j s′ → endedUp ρ (en-sub en (in-source here) (∧-join j refl)) ψ s′)
          ; (in-body ψ) sn → thru (is-just (part (plant ρ v)) ∨ is-just e) sn (λ j s′ → en (in-body ψ) (∧-join (∨-mono (is-just e) (revive ρ) j) s′)) }
        endedUp (in-body {k = k} {r = r} {e = e} {rt = rt} {s = s} ρ) en = λ
          { here _ x pe → en here refl (proj₂ (shown (in-body {k = k} {r = r} {e = e} {rt = rt} {s = s} ρ) x)) pe
          ; (in-source ψ) sn → thru (is-just (part (plant ρ v))) sn (λ j s′ → en (in-source ψ) (∧-join (revive ρ j) s′))
          ; (in-body ψ) sn → thru (is-just (part s) ∨ is-just e) sn (λ j s′ → endedUp ρ (en-sub en (in-body here) (∧-join j refl)) ψ s′) }

        endedL : ∀ {Γ B i π} {ls : List (Sub Γ B)} (ρ : PathLanes ls u i π) → EndedL ls → EndedL (plantᴸ ρ v)
        endedL (this-lane ρ) en = λ
          { (this-lane ψ) sn → endedUp ρ (λ ψ′ → en (this-lane ψ′)) ψ sn
          ; (next-lane ψ) sn → en (next-lane ψ) sn }
        endedL (next-lane ρ) en = λ
          { (this-lane ψ) sn → en (this-lane ψ) sn
          ; (next-lane ψ) sn → endedL ρ (λ ψ′ → en (next-lane ψ′)) ψ sn }

      -- Every done flag above the node read alike.
      mutual
        flagsUp : ∀ {Γ A π} {t : Sub Γ A} (ρ : Path t u π) (N : List ℕ → Set) → FlagsBy N t → FlagsBy N (plant ρ v)
        flagsUp here N fl = Alive.alive-flags al N fl
        flagsUp (in-map ρ) N fl = λ { (in-map ψ) sn → flagsUp ρ (λ τ → N (0 ∷ τ)) (λ ψ′ s′ → fl (in-map ψ′) s′) ψ sn }
        flagsUp (in-scan ρ) N fl = λ { (in-scan ψ) sn → flagsUp ρ (λ τ → N (0 ∷ τ)) (λ ψ′ s′ → fl (in-scan ψ′) s′) ψ sn }
        flagsUp (in-cut {l = l} ρ) N fl =
          λ { (in-cut ψ) sn → thru l sn (λ j s′ → flagsUp ρ (λ τ → N (0 ∷ τ)) (λ ψ′ s″ → fl (in-cut ψ′) (∧-join j s″)) ψ s′) }
        flagsUp (in-lane ρ) N fl = λ { (in-lane ψ) sn → flagsUp ρ (λ τ → N (0 ∷ τ)) (λ ψ′ s′ → fl (in-lane ψ′) s′) ψ sn }
        flagsUp (in-take {tk = tk} ρ) N fl =
          λ { (in-take ψ) sn → thru (isTaking tk) sn (λ j s′ → flagsUp ρ (λ τ → N (0 ∷ τ)) (λ ψ′ s″ → fl (in-take ψ′) (∧-join j s″)) ψ s′) }
        flagsUp (in-outer {t = s} ρ) N fl = λ
          { here _ → proj₁ (fl here refl) , (λ nn → trans (proj₂ (fl here refl) nn) (nothing-eq (part s) (part (plant ρ v)) (alive ρ) (revive ρ)))
          ; (in-outer ψ) sn → flagsUp ρ (λ τ → N (0 ∷ τ)) (λ ψ′ s′ → fl (in-outer ψ′) s′) ψ sn
          ; (in-lanes ψ) sn → fl (in-lanes ψ) sn }
        flagsUp (in-lanes ρ) N fl = λ
          { here sn → fl here sn
          ; (in-outer ψ) sn → fl (in-outer ψ) sn
          ; (in-lanes ψ) sn → flagsL ρ (λ i τ → N (suc i ∷ τ)) (λ ψ′ s′ → fl (in-lanes ψ′) s′) ψ sn }
        flagsUp (in-source {e = e} {b = b} ρ) N fl = λ
          { (in-source ψ) sn → thru (is-just (part b)) sn (λ j s′ → flagsUp ρ (λ τ → N (0 ∷ τ)) (λ ψ′ s″ → fl (in-source ψ′) (∧-join j s″)) ψ s′)
          ; (in-body ψ) sn → thru (is-just (part (plant ρ v)) ∨ is-just e) sn (λ j s′ → fl (in-body ψ) (∧-join (∨-mono (is-just e) (revive ρ) j) s′)) }
        flagsUp (in-body {e = e} {s = s} ρ) N fl = λ
          { (in-source ψ) sn → thru (is-just (part (plant ρ v))) sn (λ j s′ → fl (in-source ψ) (∧-join (revive ρ j) s′))
          ; (in-body ψ) sn → thru (is-just (part s) ∨ is-just e) sn (λ j s′ → flagsUp ρ (λ τ → N (1 ∷ τ)) (λ ψ′ s″ → fl (in-body ψ′) (∧-join j s″)) ψ s′) }

        flagsL : ∀ {Γ B i π} {ls : List (Sub Γ B)} (ρ : PathLanes ls u i π) (M : ℕ → List ℕ → Set) → FlagsByL M ls → FlagsByL M (plantᴸ ρ v)
        flagsL (this-lane ρ) M fl = λ
          { (this-lane ψ) sn → flagsUp ρ (M 0) (λ ψ′ s′ → fl (this-lane ψ′) s′) ψ sn
          ; (next-lane ψ) sn → fl (next-lane ψ) sn }
        flagsL (next-lane ρ) M fl = λ
          { (this-lane ψ) sn → fl (this-lane ψ) sn
          ; (next-lane ψ) sn → flagsL ρ (λ i → M (suc i)) (λ ψ′ s′ → fl (next-lane ψ′) s′) ψ sn }

      -- EACH JOINER ABOVE THE NODE TOLD NO SOONER: a connect past its
      -- end above the node tells its body's joiners what the old body
      -- did, or less.
      module Told (q : Pos) (E : Pred Δ₀)
                  (tl₀ : ∀ {C} (i : C ∈ᴸ Δ₀) {c} → E i c → ∀ {b₀ b′} → part u ≡ just b₀ → part v ≡ just b′
                       → untold i b′ ⊑[ q / c ] untold i b₀)
                  (ut₀ : Ended u → Untold q u → Untold q v) where
        open Telling q E tl₀ using (told)

        mutual
          toldUp : ∀ {Γ A π} {t : Sub Γ A} (ρ : Path t u π) → Untold q t → Ended t
                 → ∀ {K : Pred Γ} → (∀ {C} (j : C ∈ᴸ Δ₀) {c} → Binds ρ K j c → E j c) → Untold q (plant ρ v)
          toldUp here ut en κ = ut₀ en ut
          toldUp (in-map ρ) ut en κ =
            λ { (in-map ψ) sn → toldUp ρ (ut-sub ut (in-map here) refl) (en-sub en (in-map here) refl) κ ψ sn }
          toldUp (in-scan ρ) ut en κ =
            λ { (in-scan ψ) sn → toldUp ρ (ut-sub ut (in-scan here) refl) (en-sub en (in-scan here) refl) κ ψ sn }
          toldUp (in-cut {l = l} ρ) ut en κ =
            λ { (in-cut ψ) sn → thru l sn (λ j s′ → toldUp ρ (ut-sub ut (in-cut here) (∧-join j refl)) (en-sub en (in-cut here) (∧-join j refl)) κ ψ s′) }
          toldUp (in-lane ρ) ut en κ =
            λ { (in-lane ψ) sn → toldUp ρ (ut-sub ut (in-lane here) refl) (en-sub en (in-lane here) refl) κ ψ sn }
          toldUp (in-take {tk = tk} ρ) ut en κ =
            λ { (in-take ψ) sn → thru (isTaking tk) sn (λ j s′ →
                  toldUp ρ (ut-sub ut (in-take here) (∧-join j refl)) (en-sub en (in-take here) (∧-join j refl)) κ ψ s′) }
          toldUp (in-outer ρ) ut en κ = λ
            { (in-outer ψ) sn → toldUp ρ (ut-sub ut (in-outer here) refl) (en-sub en (in-outer here) refl) κ ψ sn
            ; (in-lanes ψ) sn → ut (in-lanes ψ) sn }
          toldUp (in-lanes ρ) ut en κ = λ
            { (in-outer ψ) sn → ut (in-outer ψ) sn
            ; (in-lanes ψ) sn → toldL′ ρ (λ ψ′ → ut (in-lanes ψ′)) (λ ψ′ → en (in-lanes ψ′)) κ ψ sn }
          toldUp (in-source {k = k} {r = r} {e = just c} {rt = rt} {b = b} ρ) ut en κ = λ
            { here _ pn eb → ut here refl (en here refl (proj₂ (shown (in-source {k = k} {r = r} {e = just c} {rt = rt} {b = b} ρ) (proj₂ (conn-ended r c rt pn eb)))) refl) eb
            ; (in-source ψ) sn → thru (is-just (part b)) sn (λ j s′ →
                toldUp ρ (ut-sub ut (in-source here) (∧-join j refl)) (en-sub en (in-source here) (∧-join j refl)) κ ψ s′)
            ; (in-body ψ) sn → thru (is-just (part (plant ρ v)) ∨ true) sn (λ j s′ → ut (in-body ψ) (∧-join (∨-mono true (revive ρ) j) s′)) }
          toldUp (in-source {e = nothing} {b = b} ρ) ut en κ = λ
            { (in-source ψ) sn → thru (is-just (part b)) sn (λ j s′ →
                toldUp ρ (ut-sub ut (in-source here) (∧-join j refl)) (en-sub en (in-source here) (∧-join j refl)) κ ψ s′)
            ; (in-body ψ) sn → thru (is-just (part (plant ρ v)) ∨ false) sn (λ j s′ → ut (in-body ψ) (∧-join (∨-mono false (revive ρ) j) s′)) }
          toldUp (in-body {e = just c} {s = s} ρ) ut en κ = λ
            { here _ pn eb → told ρ (en-sub en (in-body here) (∧-join (∨-r (is-just (part s)) refl) refl)) κ (here refl) (refl , pn)
                               (proj₂ (just-of (revive ρ (isj eb)))) eb (ut here refl pn (proj₂ (just-of (revive ρ (isj eb)))))
            ; (in-source ψ) sn → thru (is-just (part (plant ρ v))) sn (λ j s′ → ut (in-source ψ) (∧-join (revive ρ j) s′))
            ; (in-body ψ) sn → thru (is-just (part s) ∨ true) sn (λ j s′ →
                toldUp ρ (ut-sub ut (in-body here) (∧-join j refl)) (en-sub en (in-body here) (∧-join j refl)) κ ψ s′) }
          toldUp (in-body {e = nothing} {s = s} ρ) ut en κ = λ
            { (in-source ψ) sn → thru (is-just (part (plant ρ v))) sn (λ j s′ → ut (in-source ψ) (∧-join (revive ρ j) s′))
            ; (in-body ψ) sn → thru (is-just (part s) ∨ false) sn (λ j s′ →
                toldUp ρ (ut-sub ut (in-body here) (∧-join j refl)) (en-sub en (in-body here) (∧-join j refl)) κ ψ s′) }

          toldL′ : ∀ {Γ B i π} {ls : List (Sub Γ B)} (ρ : PathLanes ls u i π) → UntoldL q ls → EndedL ls
                 → ∀ {K : Pred Γ} → (∀ {C} (j : C ∈ᴸ Δ₀) {c} → BindsL ρ K j c → E j c) → UntoldL q (plantᴸ ρ v)
          toldL′ (this-lane ρ) ut en κ = λ
            { (this-lane ψ) sn → toldUp ρ (λ ψ′ → ut (this-lane ψ′)) (λ ψ′ → en (this-lane ψ′)) κ ψ sn
            ; (next-lane ψ) sn → ut (next-lane ψ) sn }
          toldL′ (next-lane ρ) ut en κ = λ
            { (this-lane ψ) sn → ut (this-lane ψ) sn
            ; (next-lane ψ) sn → toldL′ ρ (λ ψ′ → ut (next-lane ψ′)) (λ ψ′ → en (next-lane ψ′)) κ ψ sn }

  -- A REPLANT AT `ρ` KEEPS what its node keeps.
  module Keep {T : Sub [] R} {Δ A π} {u : Sub Δ A} (ρ : Path T u π) where
    -- Every held connect past its end holds no source.
    shift-ended : (v : Sub Δ A) → Alive u v → Ended T → Ended (plant ρ v)
    shift-ended v al en = Up.endedUp al ρ en

    -- Every seen flatMap's done flag reads as it did.
    shift-flags : (v : Sub Δ A) → Alive u v → ∀ {ns} → DoneBy T ns → DoneBy (plant ρ v) ns
    shift-flags v al {ns} fl = Up.flagsUp al ρ (λ τ → τ ∈ᴸ ns) fl

    -- Every connect past its end tells its joiners no sooner than `q`.
    shift-told : (v : Sub Δ A) → Alive u v → ∀ {q} → Heading q (Bound ρ) u v → (Ended u → Untold q u → Untold q v)
               → Untold q T → Ended T → Untold q (plant ρ v)
    shift-told v al {q} hd ut₀ ut en = Up.Told.toldUp al q (Bound ρ) (Heading.head-told hd) ut₀ ρ ut en (λ j w → w)
