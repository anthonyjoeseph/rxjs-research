{-# OPTIONS --guardedness #-}

-- THE REPLANT FRAME, KEPT: what a replant keeps besides the heads,
-- walked up the path as `adequacy.Replant` walks them — every held
-- connect past its end without a source, every joiner told no sooner,
-- every done flag read alike.  Every node above reads its path child
-- only through whether the child shows, both ways round.
module adequacy.Replant.Keep where

open import Data.Bool using (true; false; _∧_; _∨_; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴸ_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (Maybe; just; nothing; is-just; is-nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; subst)
open import Relation.Nullary using (¬_)

import denotation.Unfold as U
open import denotation.MonotonicList.Events using (Pos)
open import adequacy.Told using (untold)
open import adequacy.Leaves using (Leaves; Twin; Restful; tw-refl; tw-union; lv-tie)
open import adequacy.Strong using (module Strongly)
open import adequacy.Moves using (module Moving)
open import adequacy.Replant using (module Replanting)
open import adequacy.Ghost.Paths using (module GhostingPaths)

module Keeping (R : Set) where
  open Strongly R using (Sub; Path; PathLanes; here; in-map; in-scan; in-cut; in-lane; in-take; in-outer; in-lanes; in-source; in-body;
    this-lane; next-lane; part; seen; seenL; isTaking; connected; Untold; Ended; DoneBy; ending; takeWhileˢ; flatMapˢ; connectˢ;
    Lingers; leftover; pooled; pooledL; ofˢ; pendingˢ; coldˢ; joinˢ; mapˢ; scanˢ; cutˢ; laneˢ)
  open Moving R using (plant; plantᴸ; planted; plantedᴸ; replanted)
  open Replanting R using (_⊑[_/_]_; Pred; Binds; BindsL; Bound; Heading; module Walk; thru; ∧-join; ∨-r; ∨-mono; isj; just-of; en-sub; ut-sub; EndedL; UntoldL;
    LingersL; lingers-sub; lingersL-of; lingersL-head; lingersL-tail; lgL-cons; lg-map; lg-scan; lg-lane; lg-cut; lg-take; lg-flat; lg-connect; pool-cons)
  open GhostingPaths R using (_⊕_; _⊕ᴸ_)

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

  -- A VALUE'S ROUTE, LIVE: every lane on it running, every flatMap it
  -- enters by the outer not yet past the outer's end, every connect it
  -- enters by the source showing that source.
  mutual
    Route : ∀ {Γ A Δ B π} {t : Sub Γ A} {u : Sub Δ B} → Path t u π → Set
    Route here                      = ⊤
    Route (in-map ψ)                = Route ψ
    Route (in-scan ψ)               = Route ψ
    Route (in-cut ψ)                = Route ψ
    Route (in-lane {r = r} ψ)       = r ≡ true × Route ψ
    Route (in-take ψ)               = Route ψ
    Route (in-outer {d = d} ψ)      = d ≡ false × Route ψ
    Route (in-lanes ψ)              = RouteL ψ
    Route (in-source {t = s} ψ)     = is-just (part s) ≡ true × Route ψ
    Route (in-body ψ)               = Route ψ

    RouteL : ∀ {Γ A Δ B i π} {ls : List (Sub Γ A)} {u : Sub Δ B} → PathLanes ls u i π → Set
    RouteL (this-lane ψ) = Route ψ
    RouteL (next-lane ψ) = RouteL ψ

  -- A live route's head is live.
  mutual
    route-pre : ∀ {Γ A Δ B Ε C π τ} {t : Sub Γ A} {x : Sub Δ B} {w : Sub Ε C} (ρ : Path t x π) (c : Path x w τ) → Route (ρ ⊕ c) → Route ρ
    route-pre here          c _       = tt
    route-pre (in-map ρ)    c r       = route-pre ρ c r
    route-pre (in-scan ρ)   c r       = route-pre ρ c r
    route-pre (in-cut ρ)    c r       = route-pre ρ c r
    route-pre (in-lane ρ)   c (e , r) = e , route-pre ρ c r
    route-pre (in-take ρ)   c r       = route-pre ρ c r
    route-pre (in-outer ρ)  c (e , r) = e , route-pre ρ c r
    route-pre (in-lanes ρ)  c r       = route-preL ρ c r
    route-pre (in-source ρ) c (e , r) = e , route-pre ρ c r
    route-pre (in-body ρ)   c r       = route-pre ρ c r

    route-preL : ∀ {Γ A Δ B Ε C i π τ} {ls : List (Sub Γ A)} {x : Sub Δ B} {w : Sub Ε C} (ρ : PathLanes ls x i π) (c : Path x w τ)
               → RouteL (ρ ⊕ᴸ c) → RouteL ρ
    route-preL (this-lane ρ) c r = route-pre ρ c r
    route-preL (next-lane ρ) c r = route-preL ρ c r

  -- A NODE BESIDE ITS REPLANT: the same node, or one of the same head
  -- whose subscriptions may differ; a takeWhile's source beside in turn,
  -- a connect's body ending no later.
  data _≈_ : ∀ {Γ A} → Sub Γ A → Sub Γ A → Set₁ where
    same      : ∀ {Γ A} {x : Sub Γ A} → x ≈ x
    ≈-map     : ∀ {Γ A B} {f : A → B} {s s′ : Sub Γ A} → mapˢ f s ≈ mapˢ f s′
    ≈-scan    : ∀ {Γ A B} {f : B → A → B} {z z′} {s s′ : Sub Γ A} → scanˢ f z s ≈ scanˢ f z′ s′
    ≈-cut     : ∀ {Γ A l a} {s s′ : Sub Γ A} → cutˢ l a s ≈ cutˢ l a s′
    ≈-lane    : ∀ {Γ A r} {s s′ : Sub Γ A} → laneˢ r s ≈ laneˢ r s′
    ≈-take    : ∀ {Γ A i q tk} {s s′ : Sub Γ A} → s ≈ s′ → takeWhileˢ i q tk s ≈ takeWhileˢ i q tk s′
    ≈-flat    : ∀ {Γ X A op f d n qs pl} {o o′ : Sub Γ X} {ls ls′ : List (Sub Γ A)}
              → flatMapˢ op f d n qs pl o ls ≈ flatMapˢ op f d n qs pl o′ ls′
    ≈-connect : ∀ {Γ X B k r e rt} {s s′ : Sub Γ X} {b b′ : Sub (X ∷ Γ) B} → (part b′ ≡ nothing → part b ≡ nothing)
              → connectˢ k r e rt s b ≈ connectˢ k r e rt s′ b′

  -- Beside a node with no subscription, the node.
  ≈-of : ∀ {Γ A p i xs} {x₀ : Sub Γ A} → x₀ ≈ ofˢ p i xs → x₀ ≡ ofˢ p i xs
  ≈-of same = refl

  ≈-pending : ∀ {Γ A o q} {x₀ : Sub Γ A} → x₀ ≈ pendingˢ o q → x₀ ≡ pendingˢ o q
  ≈-pending same = refl

  ≈-cold : ∀ {Γ A b ph} {x₀ : Sub Γ A} → x₀ ≈ coldˢ b ph → x₀ ≡ coldˢ b ph
  ≈-cold same = refl

  ≈-join : ∀ {Γ A j g x st} {x₀ : Sub Γ A} → x₀ ≈ joinˢ j g x st → x₀ ≡ joinˢ j g x st
  ≈-join same = refl

  -- Beside a switch, a takeWhile or a connect, one of the same head.
  ≈-cut-of : ∀ {Γ A l a} {s : Sub Γ A} {x₀} → x₀ ≈ cutˢ l a s → Σ (Sub Γ A) λ s₀ → x₀ ≡ cutˢ l a s₀
  ≈-cut-of same  = _ , refl
  ≈-cut-of ≈-cut = _ , refl

  ≈-take-of : ∀ {Γ A i q tk} {s : Sub Γ A} {x₀} → x₀ ≈ takeWhileˢ i q tk s → Σ (Sub Γ A) λ s₀ → x₀ ≡ takeWhileˢ i q tk s₀
  ≈-take-of same       = _ , refl
  ≈-take-of (≈-take _) = _ , refl

  ≈-take-cut : ∀ {Γ A i q tk l a} {s : Sub Γ A} {x₀} → x₀ ≈ takeWhileˢ i q tk (cutˢ l a s)
             → Σ (Sub Γ A) λ s₀ → x₀ ≡ takeWhileˢ i q tk (cutˢ l a s₀)
  ≈-take-cut same             = _ , refl
  ≈-take-cut (≈-take same)    = _ , refl
  ≈-take-cut (≈-take ≈-cut)   = _ , refl

  ≈-connect-of : ∀ {Γ X B k r e rt} {s : Sub Γ X} {b : Sub (X ∷ Γ) B} {x₀}
               → x₀ ≈ connectˢ k r e rt s b
               → Σ (Sub Γ X) λ s₀ → Σ (Sub (X ∷ Γ) B) λ b₀ → (part b ≡ nothing → part b₀ ≡ nothing) × x₀ ≡ connectˢ k r e rt s₀ b₀
  ≈-connect-of same            = _ , _ , (λ n → n) , refl
  ≈-connect-of (≈-connect h)   = _ , _ , h , refl

  -- EVERY NODE OF `t′` BESIDE ONE OF `t`'s AT ITS PATH, held when it is.
  Back : ∀ {Γ A} → Sub Γ A → Sub Γ A → Set₁
  Back t t′ = ∀ {Δ B π} {x : Sub Δ B} (ψ : Path t′ x π)
            → Σ (Sub Δ B) λ x₀ → Σ (Path t x₀ π) λ ψ₀ → x₀ ≈ x × (seen ψ ≡ true → seen ψ₀ ≡ true)

  private
    ∧-mapʳ : ∀ a {b c} → (b ≡ true → c ≡ true) → a ∧ b ≡ true → a ∧ c ≡ true
    ∧-mapʳ a h e = thru a e (λ x y → ∧-join x (h y))

    ∧-mapˡ : ∀ {a a′} b → (a′ ≡ true → a ≡ true) → a′ ∧ b ≡ true → a ∧ b ≡ true
    ∧-mapˡ {a′ = a′} b h e = thru a′ e (λ x y → ∧-join (h x) y)

    -- A part shown is not missing.
    shows-not : ∀ {X : Set₁} {m : Maybe X} → is-just m ≡ true → m ≡ nothing → ⊥
    shows-not {m = just _}  _  ()
    shows-not {m = nothing} () _

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

      -- The route to the node live as it was.
      mutual
        routed : ∀ {Γ A π} {t : Sub Γ A} (ρ : Path t u π) → Route ρ → Route (planted ρ v)
        routed here          _       = tt
        routed (in-map ρ)    w       = routed ρ w
        routed (in-scan ρ)   w       = routed ρ w
        routed (in-cut ρ)    w       = routed ρ w
        routed (in-lane ρ)   (e , w) = e , routed ρ w
        routed (in-take ρ)   w       = routed ρ w
        routed (in-outer ρ)  (e , w) = e , routed ρ w
        routed (in-lanes ρ)  w       = routedL ρ w
        routed (in-source ρ) (j , w) = alive ρ j , routed ρ w
        routed (in-body ρ)   w       = routed ρ w

        routedL : ∀ {Γ B i π} {ls : List (Sub Γ B)} (ρ : PathLanes ls u i π) → RouteL ρ → RouteL (plantedᴸ ρ v)
        routedL (this-lane ρ) w = routed ρ w
        routedL (next-lane ρ) w = routedL ρ w

      -- EVERY NODE OF THE REPLANTED TREE BESIDE ONE OF THE TREE's: off
      -- the path the same, on it one of the same head, under the node as
      -- `bk` says.
      module Beside (≈₀ : u ≈ v) (bk : Back u v) where
        beside : ∀ {Γ A π} {t : Sub Γ A} (ρ : Path t u π) → t ≈ plant ρ v
        beside here          = ≈₀
        beside (in-map ρ)    = ≈-map
        beside (in-scan ρ)   = ≈-scan
        beside (in-cut ρ)    = ≈-cut
        beside (in-lane ρ)   = ≈-lane
        beside (in-take ρ)   = ≈-take (beside ρ)
        beside (in-outer ρ)  = ≈-flat
        beside (in-lanes ρ)  = ≈-flat
        beside (in-source ρ) = ≈-connect (λ n → n)
        beside (in-body ρ)   = ≈-connect (nothing-back (alive ρ))

        mutual
          back : ∀ {Γ A π} {t : Sub Γ A} (ρ : Path t u π) → Back t (plant ρ v)
          back here ψ = bk ψ
          back ρ@(in-map _) here = _ , here , beside ρ , λ e → e
          back (in-map ρ) (in-map ψ) = let x₀ , ψ₀ , b , h = back ρ ψ in x₀ , in-map ψ₀ , b , h
          back ρ@(in-scan _) here = _ , here , beside ρ , λ e → e
          back (in-scan ρ) (in-scan ψ) = let x₀ , ψ₀ , b , h = back ρ ψ in x₀ , in-scan ψ₀ , b , h
          back ρ@(in-cut _) here = _ , here , beside ρ , λ e → e
          back (in-cut {l = l} ρ) (in-cut ψ) = let x₀ , ψ₀ , b , h = back ρ ψ in x₀ , in-cut ψ₀ , b , ∧-mapʳ l h
          back ρ@(in-lane _) here = _ , here , beside ρ , λ e → e
          back (in-lane ρ) (in-lane ψ) = let x₀ , ψ₀ , b , h = back ρ ψ in x₀ , in-lane ψ₀ , b , h
          back ρ@(in-take _) here = _ , here , beside ρ , λ e → e
          back (in-take {tk = tk} ρ) (in-take ψ) = let x₀ , ψ₀ , b , h = back ρ ψ in x₀ , in-take ψ₀ , b , ∧-mapʳ (isTaking tk) h
          back ρ@(in-outer _) here = _ , here , beside ρ , λ e → e
          back (in-outer ρ) (in-outer ψ) = let x₀ , ψ₀ , b , h = back ρ ψ in x₀ , in-outer ψ₀ , b , h
          back (in-outer ρ) (in-lanes ψ) = _ , in-lanes ψ , same , λ e → e
          back ρ@(in-lanes _) here = _ , here , beside ρ , λ e → e
          back (in-lanes ρ) (in-outer ψ) = _ , in-outer ψ , same , λ e → e
          back (in-lanes ρ) (in-lanes ψ) = let x₀ , ψ₀ , b , h = backL ρ ψ in x₀ , in-lanes ψ₀ , b , h
          back ρ@(in-source _) here = _ , here , beside ρ , λ e → e
          back (in-source {b = b′} ρ) (in-source ψ) =
            let x₀ , ψ₀ , b , h = back ρ ψ in x₀ , in-source ψ₀ , b , ∧-mapʳ (is-just (part b′)) h
          back (in-source {e = e} ρ) (in-body ψ) = _ , in-body ψ , same , ∧-mapˡ (seen ψ) (∨-mono (is-just e) (revive ρ))
          back ρ@(in-body _) here = _ , here , beside ρ , λ e → e
          back (in-body ρ) (in-source ψ) = _ , in-source ψ , same , ∧-mapˡ (seen ψ) (revive ρ)
          back (in-body {e = e} {s = s} ρ) (in-body ψ) =
            let x₀ , ψ₀ , b , h = back ρ ψ in x₀ , in-body ψ₀ , b , ∧-mapʳ (is-just (part s) ∨ is-just e) h

          backL : ∀ {Γ B i π} {ls : List (Sub Γ B)} (ρ : PathLanes ls u i π)
                → ∀ {Δ C j τ} {x : Sub Δ C} (ψ : PathLanes (plantᴸ ρ v) x j τ)
                → Σ (Sub Δ C) λ x₀ → Σ (PathLanes ls x₀ j τ) λ ψ₀ → x₀ ≈ x × (seenL ψ ≡ true → seenL ψ₀ ≡ true)
          backL (this-lane ρ) (this-lane ψ) = let x₀ , ψ₀ , b , h = back ρ ψ in x₀ , this-lane ψ₀ , b , h
          backL (this-lane ρ) (next-lane ψ) = _ , next-lane ψ , same , λ e → e
          backL (next-lane ρ) (this-lane ψ) = _ , this-lane ψ , same , λ e → e
          backL (next-lane ρ) (next-lane ψ) = let x₀ , ψ₀ , b , h = backL ρ ψ in x₀ , next-lane ψ₀ , b , h

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

      -- EVERY TIE ABOVE THE NODE HELD, ITS ROUTE LIVE: no pool above
      -- reads the path's leftover, every lane on it running and every
      -- outer on it unended, and no held connect reads its source's,
      -- every source on it showing.
      module Tie (lp₀ : ∀ {ls} → Twin (pooledL (u ∷ ls)) (pooledL (v ∷ ls))) (lb₀ : Lingers u → Lingers v) where
        lanePool : ∀ {Γ B π} {l : Sub Γ B} {ls} (ρ : Path l u π) → Route ρ → Twin (pooledL (l ∷ ls)) (pooledL (plant ρ v ∷ ls))
        lanePool here _ = lp₀
        lanePool {ls = ls} (in-lane ρ) (refl , _) = tw-refl (pooledL ls)
        lanePool {ls = ls} (in-map ρ)    _ = tw-refl (pooledL ls)
        lanePool {ls = ls} (in-scan ρ)   _ = tw-refl (pooledL ls)
        lanePool {ls = ls} (in-cut ρ)    _ = tw-refl (pooledL ls)
        lanePool {ls = ls} (in-take ρ)   _ = tw-refl (pooledL ls)
        lanePool {ls = ls} (in-outer ρ)  _ = tw-refl (pooledL ls)
        lanePool {ls = ls} (in-lanes ρ)  _ = tw-refl (pooledL ls)
        lanePool {ls = ls} (in-source ρ) _ = tw-refl (pooledL ls)
        lanePool {ls = ls} (in-body ρ)   _ = tw-refl (pooledL ls)

        poolL : ∀ {Γ B i π} {ls : List (Sub Γ B)} (ρ : PathLanes ls u i π) → RouteL ρ → Twin (pooledL ls) (pooledL (plantᴸ ρ v))
        poolL (this-lane ρ) w = lanePool ρ w
        poolL (next-lane {l = l} ρ) w = pool-cons l (poolL ρ w)

        mutual
          lingersUp : ∀ {Γ A π} {t : Sub Γ A} (ρ : Path t u π) → Route ρ → Lingers t → Lingers (plant ρ v)
          lingersUp here _ lg = lb₀ lg
          lingersUp (in-map ρ) w lg = lg-map (lingersUp ρ w (lingers-sub lg (in-map here) refl))
          lingersUp (in-scan ρ) w lg = lg-scan (lingersUp ρ w (lingers-sub lg (in-scan here) refl))
          lingersUp (in-cut ρ) w lg = lg-cut (λ x → lingersUp ρ w (lingers-sub lg (in-cut here) (∧-join x refl)))
          lingersUp (in-lane ρ) (_ , w) lg = lg-lane (lingersUp ρ w (lingers-sub lg (in-lane here) refl))
          lingersUp (in-take ρ) w lg = lg-take (λ x → lingersUp ρ w (lingers-sub lg (in-take here) (∧-join x refl)))
          lingersUp (in-outer {op = op} {f = f} {n = n} {qs = qs} {pl = pl} {ls = ls} ρ) (refl , w) lg =
            lg-flat (λ x → Lingers.pools lg here refl (proj₂ (shown (in-outer {op = op} {f = f} {d = false} {n = n} {qs = qs} {pl = pl} {ls = ls} ρ) x)))
                    (lingersUp ρ w (lingers-sub lg (in-outer here) refl)) (lingersL-of lg)
          lingersUp (in-lanes {op = op} {f = f} {d = d} {n = n} {qs = qs} {pl = pl} {o = o} {ls = ls} ρ) w lg =
            lg-flat pool (lingers-sub lg (in-outer here) refl) (lingersL ρ w (lingersL-of lg))
            where
              pool : ∀ {c} → part (flatMapˢ op f d n qs pl o (plantᴸ ρ v)) ≡ just c → Leaves pl (pooled d o (plantᴸ ρ v)) × Restful pl
              pool x = lv-tie (Lingers.pools lg here refl (proj₂ (shown (in-lanes {op = op} {f = f} {d = d} {n = n} {qs = qs} {pl = pl} {o = o} ρ) x)))
                         (proj₁ (tw-union (tw-refl (if d then leftover o else U.idleᶜ)) (poolL ρ w)))
          lingersUp (in-source {k = k} {r = r} {e = e} {rt = rt} {t = s} {b = b} ρ) (js , w) lg = lg-connect rest ls lb
            where
              ls : is-just (part b) ≡ true → Lingers (plant ρ v)
              ls jb = lingersUp ρ w (lingers-sub lg (in-source here) (∧-join jb refl))
              lb : (is-just (part (plant ρ v)) ∨ is-just e) ≡ true → Lingers b
              lb j = lingers-sub lg (in-body here) (∧-join (∨-mono (is-just e) (revive ρ) j) refl)
              rest : ∀ {n} → part (connectˢ k r e rt (plant ρ v) b) ≡ just n → part (plant ρ v) ≡ nothing → ∀ {c₀} → e ≡ just c₀
                   → Twin rt (leftover (plant ρ v)) × Restful rt
              rest _ pn _ = ⊥-elim (shows-not (alive ρ js) pn)
          lingersUp (in-body {k = k} {r = r} {e = e} {rt = rt} {s = s} {t = b} ρ) w lg = lg-connect rest ls lb
            where
              ls : is-just (part (plant ρ v)) ≡ true → Lingers s
              ls jb = lingers-sub lg (in-source here) (∧-join (revive ρ jb) refl)
              lb : (is-just (part s) ∨ is-just e) ≡ true → Lingers (plant ρ v)
              lb j = lingersUp ρ w (lingers-sub lg (in-body here) (∧-join j refl))
              rest : ∀ {n} → part (connectˢ k r e rt s (plant ρ v)) ≡ just n → part s ≡ nothing → ∀ {c₀} → e ≡ just c₀
                   → Twin rt (leftover s) × Restful rt
              rest x pn pe = Lingers.rests lg here refl (proj₂ (shown (in-body {k = k} {r = r} {e = e} {rt = rt} {s = s} ρ) x)) pn pe

          lingersL : ∀ {Γ B i π} {ls : List (Sub Γ B)} (ρ : PathLanes ls u i π) → RouteL ρ → LingersL ls → LingersL (plantᴸ ρ v)
          lingersL (this-lane ρ) w lL = lgL-cons (lingersUp ρ w (lingersL-head lL)) (lingersL-tail lL)
          lingersL (next-lane ρ) w lL = lgL-cons (lingersL-head lL) (lingersL ρ w (lingersL-tail lL))

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

    -- Every node of the replanted tree beside one of the tree's.
    back-planted : (v : Sub Δ A) → Alive u v → u ≈ v → Back u v → Back T (plant ρ v)
    back-planted v al ≈₀ bk = Up.Beside.back al ≈₀ bk ρ

    -- The route, live, lives on.
    route-planted : (v : Sub Δ A) → Alive u v → Route ρ → Route (planted ρ v)
    route-planted v al w = Up.routed al ρ w

    -- Every tie held, the route live and the node's own held.
    route-lingers : (v : Sub Δ A) → Alive u v → Route ρ
                  → (∀ {ls} → Twin (pooledL (u ∷ ls)) (pooledL (v ∷ ls))) → (Lingers u → Lingers v)
                  → Lingers T → Lingers (plant ρ v)
    route-lingers v al w lp lb lg = Up.Tie.lingersUp al lp lb ρ w lg
