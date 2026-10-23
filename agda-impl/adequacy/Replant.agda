{-# OPTIONS --guardedness #-}

-- THE REPLANT FRAME: a node `u` replanted to `v`, walked from the node up
-- to the root.  Every node above reads its path child only through the
-- child's part, its heads and its leftover, which the node's premises
-- carry; every node beside the path is the same node.
module adequacy.Replant where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴸ_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁻ˡ; ++⁻ʳ) renaming (++⁺ to all-++⁺)
open import Data.Maybe using (Maybe; just; nothing; is-just)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; if_then_else_)
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Data.Unit using (⊤)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

import denotation.Unfold as U
open import denotation.MonotonicList.Events using (Pos)
open import adequacy.Told using (Tells; untold; untoldᴹ; untoldᴸ)
open import adequacy.Leaves using (Leaves; Twin; Restful; rf-idle; rf-rest; rf-union; rf-burst; rf-under; tw-refl; tw-union; tw-under; tw-burst; tw-shift; tw-if; tw-tie; lv-tie)
open import adequacy.Strong using (module Strongly)
open import adequacy.Moves using (module Moving)
open import adequacy.Frame using (module Framing)
open import adequacy.Ghost.Paths using (module GhostingPaths)

module Replanting (R : Set) where
  open Strongly R using (Sub; Path; PathLanes; here; in-map; in-scan; in-cut; in-lane; in-take; in-outer; in-lanes; in-source; in-body;
    this-lane; next-lane; part; partLanes; leftover; leftoverL; pooledL; pooled; sourced; Each; Heads; Lingers; Untold; Ended; Taking; taking; ending; taken; taking?; merged; connected;
    consᴹ; mapᴹ; seen; seenL; isTaking;
    pendingˢ; coldˢ; ofˢ; doneˢ; mapˢ; scanˢ; cutˢ; laneˢ; takeWhileˢ; flatMapˢ; connectˢ; joinˢ)
  open Moving R using (plant; plantᴸ)
  open Framing R using (heads-map; heads-scan; heads-take; heads-source; shut-heads; heads-flat; untold-shut; ended-head)
  open GhostingPaths R using (_⊕_; _⊕ᴸ_)

  -- Joiners that tell past `q` at the end `c` if `ys`'s joiners do.
  _⊑[_/_]_ : List Pos → Pos → Pos → List Pos → Set
  xs ⊑[ q / c ] ys = Tells q c ys → Tells q c xs

  -- A claim about each binder in scope and an end.
  Pred : List Set → Set₂
  Pred Δ = ∀ {C} → C ∈ᴸ Δ → Pos → Set₁

  none : Pred []
  none () _

  -- A connect's own binder, ended at `c` with its source gone.
  gone : ∀ {Δ A} → Maybe Pos → Sub Δ A → Pred Δ → Pred (A ∷ Δ)
  gone e src K (here _)  c = e ≡ just c × part src ≡ nothing
  gone e src K (there i) c = K i c

  -- Each binder's claim, read down the path: the connects it passes
  -- bind theirs as ended.
  mutual
    Binds : ∀ {Γ A Δ B π} {t : Sub Γ A} {u : Sub Δ B} → Path t u π → Pred Γ → Pred Δ
    Binds here                            K = K
    Binds (in-map p)                      K = Binds p K
    Binds (in-scan p)                     K = Binds p K
    Binds (in-cut p)                      K = Binds p K
    Binds (in-lane p)                     K = Binds p K
    Binds (in-take p)                     K = Binds p K
    Binds (in-outer p)                    K = Binds p K
    Binds (in-lanes p)                    K = BindsL p K
    Binds (in-source p)                   K = Binds p K
    Binds (in-body {e = e} {s = src} p)   K = Binds p (gone e src K)

    BindsL : ∀ {Γ A Δ B i π} {ls : List (Sub Γ A)} {u : Sub Δ B} → PathLanes ls u i π → Pred Γ → Pred Δ
    BindsL (this-lane p) K = Binds p K
    BindsL (next-lane p) K = BindsL p K

  -- Every binder above the node, from the root: each one a connect
  -- ended at `c` with its source gone.
  Bound : ∀ {Δ A π} {T : Sub [] R} {u : Sub Δ A} → Path T u π → Pred Δ
  Bound ρ = Binds ρ none

  -- THE NODE'S HEADS, MOVED: no part revived, no take above it switched
  -- back on, each binder's joiners told no sooner, and below it every
  -- part heading as before.
  record Heading (q : Pos) {Δ A} (E : Pred Δ) (u v : Sub Δ A) : Set₁ where
    field
      head-revive : is-just (part v) ≡ true → is-just (part u) ≡ true
      head-take   : ∀ {i p k c} → is-just (part (takeWhileˢ i p (ending k c) v)) ≡ true → is-just (part (takeWhileˢ i p (ending k c) u)) ≡ true
      head-told   : ∀ {A′} (i : A′ ∈ᴸ Δ) {c} → E i c → ∀ {b₀ b′} → part u ≡ just b₀ → part v ≡ just b′ → untold i b′ ⊑[ q / c ] untold i b₀
      head-below  : Each (Heads q) u → Each (Heads q) v

  -- THE NODE'S TIES, MOVED: its part the same, under a take as well,
  -- what it leaves running and what it pools as a lane twinned as
  -- before, and below it every tie kept.
  -- A connect above a running source reads the source's part as what
  -- it leaves running, so a part moved moves a tie no twin of leftovers
  -- holds.
  record Lingering {Δ A} (u v : Sub Δ A) : Set₁ where
    field
      ling-same   : part v ≡ part u
      ling-take   : ∀ {i p tk} → part (takeWhileˢ i p tk v) ≡ part (takeWhileˢ i p tk u)
      ling-rested : ∀ {C} → Twin (leftover {B = C} u) (leftover {B = C} v)
      ling-pool   : ∀ {ls} → Twin (pooledL (u ∷ ls)) (pooledL (v ∷ ls))
      ling-below  : Lingers u → Lingers v

  ----------------------------------------------------------------------
  -- Booleans and options

  ∧-join : ∀ {a b} → a ≡ true → b ≡ true → a ∧ b ≡ true
  ∧-join refl b = b

  thru : ∀ {ℓ} {X : Set ℓ} a {b} → a ∧ b ≡ true → (a ≡ true → b ≡ true → X) → X
  thru true  s k = k refl s
  thru false () k

  ∨-l : ∀ {a b} → a ≡ true → a ∨ b ≡ true
  ∨-l refl = refl

  ∨-r : ∀ a {b} → b ≡ true → a ∨ b ≡ true
  ∨-r true  _ = refl
  ∨-r false e = e

  ∨-mono : ∀ {a a′} b → (a′ ≡ true → a ≡ true) → a′ ∨ b ≡ true → a ∨ b ≡ true
  ∨-mono {a′ = true}  b f _ = ∨-l (f refl)
  ∨-mono {a′ = false} b f e = ∨-r _ e

  false≢ : ∀ {ℓ} {X : Set ℓ} → false ≡ true → X
  false≢ ()

  isj : ∀ {X : Set₁} {m : Maybe X} {c} → m ≡ just c → is-just m ≡ true
  isj refl = refl

  just-of : ∀ {X : Set₁} {m : Maybe X} → is-just m ≡ true → Σ X λ c → m ≡ just c
  just-of {m = just c} _ = c , refl

  via : ∀ {X : Set₁} {m m′ : Maybe X} → m ≡ m′ → is-just m ≡ true → is-just m′ ≡ true
  via refl j = j

  map-fwd : ∀ {X Y : Set₁} {g : X → Y} (m : Maybe X) → is-just m ≡ true → is-just (mapᴹ g m) ≡ true
  map-fwd (just _) _ = refl

  map-back : ∀ {X Y : Set₁} {g : X → Y} (m : Maybe X) → is-just (mapᴹ g m) ≡ true → is-just m ≡ true
  map-back (just _) _ = refl

  ----------------------------------------------------------------------
  -- A take's switch: its source's, off only under a cut switched off,
  -- which shows nothing.

  Sw : ∀ {Γ A} → Bool → (A → Bool) → Sub Γ A → Set₁
  Sw i p x = (∀ tk → part (takeWhileˢ i p tk x) ≡ taking? i p tk (part x)) ⊎ ((∀ tk → part (takeWhileˢ i p tk x) ≡ nothing) × part x ≡ nothing)

  sw : ∀ {Γ A} i (p : A → Bool) (x : Sub Γ A) → Sw {Γ} i p x
  sw i p (pendingˢ o q)                 = inj₁ (λ _ → refl)
  sw i p (coldˢ b ph)                   = inj₁ (λ _ → refl)
  sw i p (ofˢ q j xs)                   = inj₁ (λ _ → refl)
  sw i p doneˢ                          = inj₁ (λ _ → refl)
  sw i p (mapˢ f s)                     = inj₁ (λ _ → refl)
  sw i p (scanˢ f z s)                  = inj₁ (λ _ → refl)
  sw i p (cutˢ true a s)                = inj₁ (λ _ → refl)
  sw i p (cutˢ false a s)               = inj₂ ((λ _ → refl) , refl)
  sw i p (laneˢ r s)                    = inj₁ (λ _ → refl)
  sw i p (takeWhileˢ j p′ tk s)         = inj₁ (λ _ → refl)
  sw i p (flatMapˢ op f d n qs pl o ls) = inj₁ (λ _ → refl)
  sw i p (connectˢ k r e rt s b)        = inj₁ (λ _ → refl)
  sw i p (joinˢ j g x st)               = inj₁ (λ _ → refl)

  -- A take showing: taking, its source showing; ending, the same end.
  take-rv : ∀ {Γ A} i (p : A → Bool) (tk : Taking Γ A) (x x′ : Sub Γ A)
          → (is-just (part x′) ≡ true → is-just (part x) ≡ true)
          → (∀ {k c} → is-just (part (takeWhileˢ i p (ending k c) x′)) ≡ true → is-just (part (takeWhileˢ i p (ending k c) x)) ≡ true)
          → is-just (part (takeWhileˢ i p tk x′)) ≡ true → is-just (part (takeWhileˢ i p tk x)) ≡ true
  take-rv i p (ending k c) x x′ rv te j = te j
  take-rv i p taking x x′ rv te j with sw i p x′ | sw i p x
  ... | inj₁ e′       | inj₁ e       = via (sym (e taking)) (map-fwd (part x) (rv (map-back (part x′) (via (e′ taking) j))))
  ... | inj₁ e′       | inj₂ (_ , n) = false≢ (trans (sym (cong is-just n)) (rv (map-back (part x′) (via (e′ taking) j))))
  ... | inj₂ (n′ , _) | _            = false≢ (via (n′ taking) j)
  take-rv i p taken x x′ rv te j with sw i p x′
  ... | inj₁ e′       = false≢ (via (e′ taken) j)
  ... | inj₂ (n′ , _) = false≢ (via (n′ taken) j)

  -- An ending take shows its end alike over either source.
  ending-eq : ∀ {Γ A} i (p : A → Bool) k (c : U.Node Γ A) (x x′ : Sub Γ A) {n}
            → is-just (part (takeWhileˢ i p (ending k c) x)) ≡ true → part (takeWhileˢ i p (ending k c) x′) ≡ just n
            → part (takeWhileˢ i p (ending k c) x) ≡ just n
  ending-eq i p k c x x′ j e′ with sw i p x′ | sw i p x
  ... | inj₁ f′       | inj₁ f       = trans (f (ending k c)) (trans (sym (f′ (ending k c))) e′)
  ... | _             | inj₂ (n , _) = false≢ (via (n (ending k c)) j)
  ... | inj₂ (n′ , _) | inj₁ _       = false≢ (via (n′ (ending k c)) (isj e′))

  -- A flatMap open: its outer, a lane or the queue.
  filled : ∀ {X : Set₁} → List X → Bool
  filled []      = false
  filled (_ ∷ _) = true

  cons-rv : ∀ {Γ B} (m m′ : Maybe (U.Node Γ B)) {L L′ : List (U.Node Γ B)} → (is-just m′ ≡ true → is-just m ≡ true)
          → (filled L′ ≡ true → filled L ≡ true) → filled (consᴹ m′ L′) ≡ true → filled (consᴹ m L) ≡ true
  cons-rv (just _) m′        rv fL j = refl
  cons-rv nothing  (just _)  rv fL j = false≢ (rv refl)
  cons-rv nothing  nothing   rv fL j = fL j

  merged-rv : ∀ {Γ A B} op (g : A → Pos → U.Node Γ B) (o o′ : Maybe (U.Node Γ A)) (L L′ : List (U.Node Γ B)) Q pl
            → (is-just o′ ≡ true → is-just o ≡ true) → (filled L′ ≡ true → filled L ≡ true)
            → is-just (merged op g o′ L′ Q pl) ≡ true → is-just (merged op g o L Q pl) ≡ true
  merged-rv op g (just _) o′        L        L′       Q       pl ro rL j = refl
  merged-rv op g nothing  (just _)  L        L′       Q       pl ro rL j = false≢ (ro refl)
  merged-rv op g nothing  nothing   (_ ∷ _)  L′       Q       pl ro rL j = refl
  merged-rv op g nothing  nothing   []       (_ ∷ _)  Q       pl ro rL j = false≢ (rL refl)
  merged-rv op g nothing  nothing   []       []       Q       pl ro rL j = j

  conn-src : ∀ {Γ A B} r e (rt : U.Node Γ A) (s s′ : Maybe (U.Node Γ A)) (mb : Maybe (U.Node (A ∷ Γ) B))
           → (is-just s′ ≡ true → is-just s ≡ true) → is-just (connected r e rt s′ mb) ≡ true → is-just (connected r e rt s mb) ≡ true
  conn-src r e        rt s        s′        nothing  rv ()
  conn-src r e        rt (just _) s′        (just _) rv j = refl
  conn-src r (just _) rt nothing  s′        (just _) rv j = refl
  conn-src r nothing  rt nothing  (just _)  (just _) rv j = false≢ (rv refl)
  conn-src r nothing  rt nothing  nothing   (just _) rv j = j

  conn-body : ∀ {Γ A B} r e (rt : U.Node Γ A) (s : Maybe (U.Node Γ A)) (mb mb′ : Maybe (U.Node (A ∷ Γ) B))
            → (is-just mb′ ≡ true → is-just mb ≡ true) → is-just (connected r e rt s mb′) ≡ true → is-just (connected r e rt s mb) ≡ true
  conn-body r e        rt s        mb       nothing  rv ()
  conn-body r e        rt s        nothing  (just _) rv j = false≢ (rv refl)
  conn-body r e        rt (just _) (just _) (just _) rv j = refl
  conn-body r (just _) rt nothing  (just _) (just _) rv j = refl
  conn-body r nothing  rt nothing  (just _) (just _) rv ()

  -- A flatMap's part, open.
  merged-eq : ∀ {Γ A B} op (g : A → Pos → U.Node Γ B) (o : Maybe (U.Node Γ A)) (L : List (U.Node Γ B)) Q pl {n}
            → merged op g o L Q pl ≡ just n → n ≡ U.flatMapᶜ op g o L Q pl
  merged-eq op g (just _) L       Q       pl refl = refl
  merged-eq op g nothing  (_ ∷ _) Q       pl refl = refl
  merged-eq op g nothing  []      (_ ∷ _) pl refl = refl
  merged-eq op g nothing  []      []      pl ()

  ----------------------------------------------------------------------
  -- A seen path, extended by a seen path

  mutual
    seen-⊕ : ∀ {Γ A Δ B Ε C π τ} {t : Sub Γ A} {x : Sub Δ B} {y : Sub Ε C} (ρ : Path t x π) (ψ : Path x y τ)
           → seen ρ ≡ true → seen ψ ≡ true → seen (ρ ⊕ ψ) ≡ true
    seen-⊕ here                       ψ a s = s
    seen-⊕ (in-map ρ)                 ψ a s = seen-⊕ ρ ψ a s
    seen-⊕ (in-scan ρ)                ψ a s = seen-⊕ ρ ψ a s
    seen-⊕ (in-cut {l = l} ρ)         ψ a s = thru l a (λ x a′ → ∧-join x (seen-⊕ ρ ψ a′ s))
    seen-⊕ (in-lane ρ)                ψ a s = seen-⊕ ρ ψ a s
    seen-⊕ (in-take {tk = tk} ρ)      ψ a s = thru (isTaking tk) a (λ x a′ → ∧-join x (seen-⊕ ρ ψ a′ s))
    seen-⊕ (in-outer ρ)               ψ a s = seen-⊕ ρ ψ a s
    seen-⊕ (in-lanes ρ)               ψ a s = seenL-⊕ ρ ψ a s
    seen-⊕ (in-source {b = b} ρ)      ψ a s = thru (is-just (part b)) a (λ x a′ → ∧-join x (seen-⊕ ρ ψ a′ s))
    seen-⊕ (in-body {e = e} {s = s₀} ρ) ψ a s = thru (is-just (part s₀) ∨ is-just e) a (λ x a′ → ∧-join x (seen-⊕ ρ ψ a′ s))

    seenL-⊕ : ∀ {Γ A Δ B Ε C i π τ} {ls : List (Sub Γ A)} {x : Sub Δ B} {y : Sub Ε C} (ρ : PathLanes ls x i π) (ψ : Path x y τ)
            → seenL ρ ≡ true → seen ψ ≡ true → seenL (ρ ⊕ᴸ ψ) ≡ true
    seenL-⊕ (this-lane ρ) ψ a s = seen-⊕ ρ ψ a s
    seenL-⊕ (next-lane ρ) ψ a s = seenL-⊕ ρ ψ a s

  ----------------------------------------------------------------------
  -- What a tree holds, of a seen subtree; of a flatMap's lanes

  module _ {P : ∀ {Γ A} → U.Node Γ A → Set} where
    each-sub : ∀ {Γ A Δ B π} {t : Sub Γ A} {x : Sub Δ B} → Each P t → (ρ : Path t x π) → seen ρ ≡ true → Each P x
    each-sub ev ρ sρ = record
      { parts = λ ψ sn → Each.parts ev (ρ ⊕ ψ) (seen-⊕ ρ ψ sρ sn)
      ; pools = λ ψ sn → Each.pools ev (ρ ⊕ ψ) (seen-⊕ ρ ψ sρ sn)
      ; rests = λ ψ sn → Each.rests ev (ρ ⊕ ψ) (seen-⊕ ρ ψ sρ sn) }

    record EachL {Γ₀ B₀} (ls : List (Sub Γ₀ B₀)) : Set₁ where
      field
        partsL : ∀ {Δ B i π} {x : Sub Δ B} (ψ : PathLanes ls x i π) → seenL ψ ≡ true → ∀ {c} → part x ≡ just c → P c
        poolsL : ∀ {Γ X A op f d n qs pl i π} {o : Sub Γ X} {ls′ : List (Sub Γ A)}
               → (ψ : PathLanes ls (flatMapˢ op f d n qs pl o ls′) i π) → seenL ψ ≡ true
               → ∀ {c} → part (flatMapˢ op f d n qs pl o ls′) ≡ just c → P pl
        restsL : ∀ {Γ X B k r e rt i π} {s : Sub Γ X} {b : Sub (X ∷ Γ) B}
               → (ψ : PathLanes ls (connectˢ k r e rt s b) i π) → seenL ψ ≡ true
               → ∀ {n} → part (connectˢ k r e rt s b) ≡ just n
               → part s ≡ nothing → ∀ {c₀} → e ≡ just c₀ → P rt

    eachL-of : ∀ {Γ X A op f d n qs pl} {o : Sub Γ X} {ls : List (Sub Γ A)} → Each P (flatMapˢ op f d n qs pl o ls) → EachL ls
    eachL-of ev = record { partsL = λ ψ → Each.parts ev (in-lanes ψ) ; poolsL = λ ψ → Each.pools ev (in-lanes ψ) ; restsL = λ ψ → Each.rests ev (in-lanes ψ) }

    eachL-head : ∀ {Γ B} {l : Sub Γ B} {ls} → EachL (l ∷ ls) → Each P l
    eachL-head eL = record { parts = λ ψ → EachL.partsL eL (this-lane ψ) ; pools = λ ψ → EachL.poolsL eL (this-lane ψ) ; rests = λ ψ → EachL.restsL eL (this-lane ψ) }

    eachL-tail : ∀ {Γ B} {l : Sub Γ B} {ls} → EachL (l ∷ ls) → EachL ls
    eachL-tail eL = record { partsL = λ ψ → EachL.partsL eL (next-lane ψ) ; poolsL = λ ψ → EachL.poolsL eL (next-lane ψ) ; restsL = λ ψ → EachL.restsL eL (next-lane ψ) }

    eachL-cons : ∀ {Γ B} {l : Sub Γ B} {ls} → Each P l → EachL ls → EachL (l ∷ ls)
    eachL-cons el eL = record
      { partsL = λ { (this-lane ψ) → Each.parts el ψ ; (next-lane ψ) → EachL.partsL eL ψ }
      ; poolsL = λ { (this-lane ψ) → Each.pools el ψ ; (next-lane ψ) → EachL.poolsL eL ψ }
      ; restsL = λ { (this-lane ψ) → Each.rests el ψ ; (next-lane ψ) → EachL.restsL eL ψ } }

    -- Every lane's part, from what each lane holds.
    lanes-all : ∀ {Γ B} (ls : List (Sub Γ B)) → EachL ls → All P (partLanes ls)
    lanes-all []       eL = []
    lanes-all (l ∷ ls) eL = all-cons (part l) (EachL.partsL eL (this-lane here) refl) (lanes-all ls (eachL-tail eL))
      where
        all-cons : ∀ {Γ B} (m : Maybe (U.Node Γ B)) {L} → (∀ {c} → m ≡ just c → P c) → All P L → All P (consᴹ m L)
        all-cons nothing  hm hL = hL
        all-cons (just c) hm hL = hm refl ∷ hL

    -- Building what a node holds from what its children hold.
    Root : ∀ {Γ A} → Sub Γ A → Set₁
    Root t = ∀ {c} → part t ≡ just c → P c

    each-map : ∀ {Γ A B} {f : A → B} {s : Sub Γ A} → Root (mapˢ f s) → Each P s → Each P (mapˢ f s)
    each-map root es = record
      { parts = λ { here _ e → root e ; (in-map ψ) → Each.parts es ψ }
      ; pools = λ { (in-map ψ) → Each.pools es ψ }
      ; rests = λ { (in-map ψ) → Each.rests es ψ } }

    each-scan : ∀ {Γ A B} {f : B → A → B} {z} {s : Sub Γ A} → Root (scanˢ f z s) → Each P s → Each P (scanˢ f z s)
    each-scan root es = record
      { parts = λ { here _ e → root e ; (in-scan ψ) → Each.parts es ψ }
      ; pools = λ { (in-scan ψ) → Each.pools es ψ }
      ; rests = λ { (in-scan ψ) → Each.rests es ψ } }

    each-lane : ∀ {Γ A r} {s : Sub Γ A} → Root (laneˢ r s) → Each P s → Each P (laneˢ r s)
    each-lane root es = record
      { parts = λ { here _ e → root e ; (in-lane ψ) → Each.parts es ψ }
      ; pools = λ { (in-lane ψ) → Each.pools es ψ }
      ; rests = λ { (in-lane ψ) → Each.rests es ψ } }

    each-cut : ∀ {Γ A l a} {s : Sub Γ A} → Root (cutˢ l a s) → (l ≡ true → Each P s) → Each P (cutˢ l a s)
    each-cut {l = l} root es = record
      { parts = λ { here _ e → root e ; (in-cut ψ) sn → thru l sn (λ x s′ → Each.parts (es x) ψ s′) }
      ; pools = λ { (in-cut ψ) sn → thru l sn (λ x s′ → Each.pools (es x) ψ s′) }
      ; rests = λ { (in-cut ψ) sn → thru l sn (λ x s′ → Each.rests (es x) ψ s′) } }

    each-take : ∀ {Γ A i p tk} {s : Sub Γ A} → Root (takeWhileˢ i p tk s) → (isTaking tk ≡ true → Each P s) → Each P (takeWhileˢ i p tk s)
    each-take {tk = tk} root es = record
      { parts = λ { here _ e → root e ; (in-take ψ) sn → thru (isTaking tk) sn (λ x s′ → Each.parts (es x) ψ s′) }
      ; pools = λ { (in-take ψ) sn → thru (isTaking tk) sn (λ x s′ → Each.pools (es x) ψ s′) }
      ; rests = λ { (in-take ψ) sn → thru (isTaking tk) sn (λ x s′ → Each.rests (es x) ψ s′) } }

    each-flat : ∀ {Γ X A op f d n qs pl} {o : Sub Γ X} {ls : List (Sub Γ A)}
              → Root (flatMapˢ op f d n qs pl o ls) → (∀ {c} → part (flatMapˢ op f d n qs pl o ls) ≡ just c → P pl)
              → Each P o → EachL ls → Each P (flatMapˢ op f d n qs pl o ls)
    each-flat root pool eo eL = record
      { parts = λ { here _ e → root e ; (in-outer ψ) → Each.parts eo ψ ; (in-lanes ψ) → EachL.partsL eL ψ }
      ; pools = λ { here _ e → pool e ; (in-outer ψ) → Each.pools eo ψ ; (in-lanes ψ) → EachL.poolsL eL ψ }
      ; rests = λ { (in-outer ψ) → Each.rests eo ψ ; (in-lanes ψ) → EachL.restsL eL ψ } }

    each-connect : ∀ {Γ X B k r e rt} {s : Sub Γ X} {b : Sub (X ∷ Γ) B}
                 → Root (connectˢ k r e rt s b)
                 → (∀ {n} → part (connectˢ k r e rt s b) ≡ just n → part s ≡ nothing → ∀ {c₀} → e ≡ just c₀ → P rt)
                 → (is-just (part b) ≡ true → Each P s) → ((is-just (part s) ∨ is-just e) ≡ true → Each P b)
                 → Each P (connectˢ k r e rt s b)
    each-connect {e = e} {s = s} {b} root rest es eb = record
      { parts = λ { here _ e′ → root e′
                  ; (in-source ψ) sn → thru (is-just (part b)) sn (λ x s′ → Each.parts (es x) ψ s′)
                  ; (in-body ψ) sn → thru (is-just (part s) ∨ is-just e) sn (λ x s′ → Each.parts (eb x) ψ s′) }
      ; pools = λ { (in-source ψ) sn → thru (is-just (part b)) sn (λ x s′ → Each.pools (es x) ψ s′)
                  ; (in-body ψ) sn → thru (is-just (part s) ∨ is-just e) sn (λ x s′ → Each.pools (eb x) ψ s′) }
      ; rests = λ { here _ e′ → rest e′
                  ; (in-source ψ) sn → thru (is-just (part b)) sn (λ x s′ → Each.rests (es x) ψ s′)
                  ; (in-body ψ) sn → thru (is-just (part s) ∨ is-just e) sn (λ x s′ → Each.rests (eb x) ψ s′) } }

  ----------------------------------------------------------------------
  -- Told and ended, of a seen subtree; of a flatMap's lanes

  ut-sub : ∀ {q Γ A Δ B π} {t : Sub Γ A} {x : Sub Δ B} → Untold q t → (ρ : Path t x π) → seen ρ ≡ true → Untold q x
  ut-sub ut ρ sρ ψ sn = ut (ρ ⊕ ψ) (seen-⊕ ρ ψ sρ sn)

  en-sub : ∀ {Γ A Δ B π} {t : Sub Γ A} {x : Sub Δ B} → Ended t → (ρ : Path t x π) → seen ρ ≡ true → Ended x
  en-sub en ρ sρ ψ sn = en (ρ ⊕ ψ) (seen-⊕ ρ ψ sρ sn)

  UntoldL : ∀ {Γ₀ B₀} → Pos → List (Sub Γ₀ B₀) → Set₁
  UntoldL q ls = ∀ {Γ X B k r c₀ rt i π} {s : Sub Γ X} {b : Sub (X ∷ Γ) B}
               → (ψ : PathLanes ls (connectˢ k r (just c₀) rt s b) i π) → seenL ψ ≡ true → part s ≡ nothing
               → ∀ {b₀} → part b ≡ just b₀ → Tells q c₀ (untold (here refl) b₀)

  EndedL : ∀ {Γ₀ B₀} → List (Sub Γ₀ B₀) → Set₁
  EndedL ls = ∀ {Γ X B k r e rt i π} {s : Sub Γ X} {b : Sub (X ∷ Γ) B}
            → (ψ : PathLanes ls (connectˢ k r e rt s b) i π) → seenL ψ ≡ true
            → ∀ {n} → part (connectˢ k r e rt s b) ≡ just n → ∀ {c₀} → e ≡ just c₀ → part s ≡ nothing

  -- A connect past its source's end, its joiners untold no sooner.
  untold-at : ∀ {q Γ X B k r e rt} {s : Sub Γ X} {b : Sub (X ∷ Γ) B} → Untold q (connectˢ k r e rt s b)
            → ∀ {c₀} → e ≡ just c₀ → part s ≡ nothing → ∀ {b₀} → part b ≡ just b₀ → Tells q c₀ (untold (here refl) b₀)
  untold-at ut refl pn eb = ut here refl pn eb

  ----------------------------------------------------------------------
  -- Joiners told no sooner

  ≡-⊑ : ∀ {q c xs ys} → xs ≡ ys → xs ⊑[ q / c ] ys
  ≡-⊑ refl t = t

  ++-⊑ : ∀ {q c} xs xs′ {ys ys′} → xs′ ⊑[ q / c ] xs → ys′ ⊑[ q / c ] ys → (xs′ ++ ys′) ⊑[ q / c ] (xs ++ ys)
  ++-⊑ xs xs′ fx fy t = all-++⁺ (fx (++⁻ˡ xs t)) (fy (++⁻ʳ xs t))

  cons-untold : ∀ {Γ A B} (i : A ∈ᴸ Γ) (m : Maybe (U.Node Γ B)) L → untoldᴸ i (consᴹ m L) ≡ untoldᴹ i m ++ untoldᴸ i L
  cons-untold i nothing  L = refl
  cons-untold i (just c) L = refl

  ------------------------------------------------------------------------
  -- THE WALK: `u` replanted to `v`, every node above it rebuilt from its
  -- path child, every node beside the path the same node.

  module Walk {Δ₀ A₀} {u v : Sub Δ₀ A₀}
              (rv₀ : is-just (part v) ≡ true → is-just (part u) ≡ true)
              (tk₀ : ∀ {i p k c} → is-just (part (takeWhileˢ i p (ending k c) v)) ≡ true → is-just (part (takeWhileˢ i p (ending k c) u)) ≡ true) where

    -- No take above the node switched back on.
    takes : ∀ {Γ A π} {t : Sub Γ A} (ρ : Path t u π)
          → ∀ {i p k c} → is-just (part (takeWhileˢ i p (ending k c) (plant ρ v))) ≡ true → is-just (part (takeWhileˢ i p (ending k c) t)) ≡ true
    takes here {i} {p} {k} {c} j = tk₀ {i} {p} {k} {c} j
    takes (in-map ρ)     j = j
    takes (in-scan ρ)    j = j
    takes (in-cut ρ)     j = j
    takes (in-lane ρ)    j = j
    takes (in-take ρ)    j = j
    takes (in-outer ρ)   j = j
    takes (in-lanes ρ)   j = j
    takes (in-source ρ)  j = j
    takes (in-body ρ)    j = j

    -- No part above the node revived.
    mutual
      revive : ∀ {Γ A π} {t : Sub Γ A} (ρ : Path t u π) → is-just (part (plant ρ v)) ≡ true → is-just (part t) ≡ true
      revive here j = rv₀ j
      revive (in-map {t = s} ρ) j = map-fwd (part s) (revive ρ (map-back (part (plant ρ v)) j))
      revive (in-scan {t = s} ρ) j = map-fwd (part s) (revive ρ (map-back (part (plant ρ v)) j))
      revive (in-cut {l = true} ρ) j = revive ρ j
      revive (in-cut {l = false} ρ) ()
      revive (in-lane ρ) j = revive ρ j
      revive (in-take {i = i} {q = p} {tk = tk} {t = s} ρ) j = take-rv i p tk s (plant ρ v) (revive ρ) (λ {k} {c} → takes ρ {i} {p} {k} {c}) j
      revive (in-outer {op = op} {f = f} {qs = qs} {pl = pl} {t = s} {ls = ls} ρ) j =
        merged-rv op (λ x r → U.subscribe (f x) r) (part s) (part (plant ρ v)) (partLanes ls) (partLanes ls) qs pl (revive ρ) (λ x → x) j
      revive (in-lanes {op = op} {f = f} {qs = qs} {pl = pl} {o = o} {ls = ls} ρ) j =
        merged-rv op (λ x r → U.subscribe (f x) r) (part o) (part o) (partLanes ls) (partLanes (plantᴸ ρ v)) qs pl (λ x → x) (reviveL ρ) j
      revive (in-source {r = r} {e = e} {rt = rt} {t = s} {b = b} ρ) j = conn-src r e rt (part s) (part (plant ρ v)) (part b) (revive ρ) j
      revive (in-body {r = r} {e = e} {rt = rt} {s = s} {t = b} ρ) j = conn-body r e rt (part s) (part b) (part (plant ρ v)) (revive ρ) j

      reviveL : ∀ {Γ B i π} {ls : List (Sub Γ B)} (ρ : PathLanes ls u i π) → filled (partLanes (plantᴸ ρ v)) ≡ true → filled (partLanes ls) ≡ true
      reviveL (this-lane {t = s} ρ) j = cons-rv (part s) (part (plant ρ v)) (revive ρ) (λ x → x) j
      reviveL (next-lane {l = l} ρ) j = cons-rv (part l) (part l) (λ x → x) (reviveL ρ) j

    -- Where the path's flatMap shows, it showed.
    shown : ∀ {Γ A π} {t : Sub Γ A} (ρ : Path t u π) → ∀ {n} → part (plant ρ v) ≡ just n → Σ _ λ n₀ → part t ≡ just n₀
    shown ρ x = just-of (revive ρ (isj x))

    ----------------------------------------------------------------------
    -- EACH BINDER'S JOINERS TOLD NO SOONER

    module Telling (q : Pos) (E : Pred Δ₀)
                   (tl₀ : ∀ {C} (i : C ∈ᴸ Δ₀) {c} → E i c → ∀ {b₀ b′} → part u ≡ just b₀ → part v ≡ just b′ → untold i b′ ⊑[ q / c ] untold i b₀) where

      told-ᴹ : ∀ {Δ A B C ω} (i : C ∈ᴸ Δ) (g : U.Node Δ A → U.Node Δ B) → (∀ c → untold i (g c) ≡ untold i c)
             → (m m′ : Maybe (U.Node Δ A)) → ∀ {b₀ b′} → mapᴹ g m ≡ just b₀ → mapᴹ g m′ ≡ just b′
             → (∀ {c c′} → m ≡ just c → m′ ≡ just c′ → untold i c′ ⊑[ q / ω ] untold i c) → untold i b′ ⊑[ q / ω ] untold i b₀
      told-ᴹ i g up (just c) (just c′) refl refl sub = λ t → ≡-⊑ (up c′) (sub refl refl (≡-⊑ (sym (up c)) t))

      toldᴹ : ∀ {Δ B C ω} (i : C ∈ᴸ Δ) (m m′ : Maybe (U.Node Δ B)) → (∀ {c c′} → m ≡ just c → m′ ≡ just c′ → untold i c′ ⊑[ q / ω ] untold i c)
            → (is-just m′ ≡ true → is-just m ≡ true) → untoldᴹ i m′ ⊑[ q / ω ] untoldᴹ i m
      toldᴹ i m        nothing   sub rv = λ _ → []
      toldᴹ i (just c) (just c′) sub rv = sub refl refl
      toldᴹ i nothing  (just c′) sub rv = false≢ (rv refl)

      flat-told : ∀ {Δ A B C ω} (i : C ∈ᴸ Δ) op (g : A → Pos → U.Node Δ B) (o o′ : Maybe (U.Node Δ A)) (L L′ : List (U.Node Δ B)) Q pl
                → untoldᴹ i o′ ⊑[ q / ω ] untoldᴹ i o → untoldᴸ i L′ ⊑[ q / ω ] untoldᴸ i L
                → ∀ {b₀ b′} → merged op g o L Q pl ≡ just b₀ → merged op g o′ L′ Q pl ≡ just b′ → untold i b′ ⊑[ q / ω ] untold i b₀
      flat-told i op g o o′ L L′ Q pl so sL e₀ e′ t
        rewrite merged-eq op g o L Q pl e₀ | merged-eq op g o′ L′ Q pl e′ =
        ++-⊑ (untoldᴹ i o) (untoldᴹ i o′) so (++-⊑ (untoldᴸ i L) (untoldᴸ i L′) sL (λ m → m)) t

      -- A take: taking, its source's joiners; ending, the same end.
      told-take : ∀ {Δ A C ω} (i : C ∈ᴸ Δ) ib (p : A → Bool) (tk : Taking Δ A) (x x′ : Sub Δ A)
                → ∀ {b₀ b′} → part (takeWhileˢ ib p tk x) ≡ just b₀ → part (takeWhileˢ ib p tk x′) ≡ just b′
                → (isTaking tk ≡ true → ∀ {c c′} → part x ≡ just c → part x′ ≡ just c′ → untold i c′ ⊑[ q / ω ] untold i c)
                → untold i b′ ⊑[ q / ω ] untold i b₀
      told-take i ib p taking x x′ e₀ e′ sub with sw ib p x | sw ib p x′
      ... | inj₁ f | inj₁ f′ =
        told-ᴹ i (U.takeWhileᶜ ib p) (λ _ → refl) (part x) (part x′) (trans (sym (f taking)) e₀) (trans (sym (f′ taking)) e′) (sub refl)
      ... | inj₂ (n , _) | _ = false≢ (via (n taking) (isj e₀))
      ... | inj₁ _ | inj₂ (n′ , _) = false≢ (via (n′ taking) (isj e′))
      told-take i ib p (ending k c) x x′ e₀ e′ sub with sw ib p x | sw ib p x′
      ... | inj₁ f | inj₁ f′ with trans (sym e₀) (trans (f (ending k c)) (trans (sym (f′ (ending k c))) e′))
      ...   | refl = λ t → t
      told-take i ib p (ending k c) x x′ e₀ e′ sub | inj₂ (n , _) | _ = false≢ (via (n (ending k c)) (isj e₀))
      told-take i ib p (ending k c) x x′ e₀ e′ sub | inj₁ _ | inj₂ (n′ , _) = false≢ (via (n′ (ending k c)) (isj e′))
      told-take i ib p taken x x′ e₀ e′ sub with sw ib p x
      ... | inj₁ f = false≢ (via (f taken) (isj e₀))
      ... | inj₂ (n , _) = false≢ (via (n taken) (isj e₀))

      -- The source replanted: a source still running past an end is
      -- refuted by the end, and one gone on both sides tells alike.
      src-told : ∀ {Δ A B C ω} (i : C ∈ᴸ Δ) r (e : Maybe Pos) (rt : U.Node Δ A) (s s′ : Maybe (U.Node Δ A)) (mb : Maybe (U.Node (A ∷ Δ) B))
               → (is-just s′ ≡ true → is-just s ≡ true)
               → (is-just mb ≡ true → ∀ {c c′} → s ≡ just c → s′ ≡ just c′ → untold i c′ ⊑[ q / ω ] untold i c)
               → (∀ {n} → connected r e rt s mb ≡ just n → ∀ {c₀} → e ≡ just c₀ → s ≡ nothing)
               → ∀ {b₀ b′} → connected r e rt s mb ≡ just b₀ → connected r e rt s′ mb ≡ just b′ → untold i b′ ⊑[ q / ω ] untold i b₀
      src-told i r e        rt s        s′        nothing  rv sub en ()   e′
      src-told i r e        rt (just c) (just c′) (just b) rv sub en refl refl = ++-⊑ (untold (there i) b) (untold (there i) b) (λ m → m) (sub refl refl refl)
      src-told i r (just x) rt (just c) nothing   (just b) rv sub en e₀   e′   with en e₀ refl
      ... | ()
      src-told i r nothing  rt (just c) nothing   (just b) rv sub en e₀   ()
      src-told i r e        rt nothing  (just c′) (just b) rv sub en e₀   e′   = false≢ (rv refl)
      src-told i r (just x) rt nothing  nothing   (just b) rv sub en refl refl = λ m → m
      src-told i r nothing  rt nothing  nothing   (just b) rv sub en ()   e′

      -- The body replanted: its joiners read one frame down, through a
      -- shut when the source has ended.
      body-told : ∀ {Δ A B C ω} (i : C ∈ᴸ Δ) r (e : Maybe Pos) (rt : U.Node Δ A) (s : Maybe (U.Node Δ A)) (mb mb′ : Maybe (U.Node (A ∷ Δ) B))
                → (is-just mb′ ≡ true → is-just mb ≡ true)
                → ((is-just s ∨ is-just e) ≡ true → ∀ {c c′} → mb ≡ just c → mb′ ≡ just c′ → untold (there i) c′ ⊑[ q / ω ] untold (there i) c)
                → ∀ {b₀ b′} → connected r e rt s mb ≡ just b₀ → connected r e rt s mb′ ≡ just b′ → untold i b′ ⊑[ q / ω ] untold i b₀
      body-told i r e        rt s        mb       nothing   rv sub e₀   ()
      body-told i r e        rt s        nothing  (just b′) rv sub e₀   e′   = false≢ (rv refl)
      body-told i r e        rt (just c) (just b) (just b′) rv sub refl refl = ++-⊑ (untold (there i) b) (untold (there i) b′) (sub refl refl refl) (λ m → m)
      body-told i r (just x) rt nothing  (just b) (just b′) rv sub refl refl =
        ++-⊑ (untold (there i) (U.shut (here refl) x b)) (untold (there i) (U.shut (here refl) x b′))
          (λ t → ≡-⊑ (untold-shut i x b′) (sub refl refl refl (≡-⊑ (sym (untold-shut i x b)) t))) (λ m → m)
      body-told i r nothing  rt nothing  (just b) (just b′) rv sub ()   e′

      mutual
        told : ∀ {Γ A π} {t : Sub Γ A} (ρ : Path t u π) → Ended t
             → ∀ {K : Pred Γ} → (∀ {C} (j : C ∈ᴸ Δ₀) {c} → Binds ρ K j c → E j c)
             → ∀ {C ω} (i : C ∈ᴸ Γ) → K i ω → ∀ {b₀ b′} → part t ≡ just b₀ → part (plant ρ v) ≡ just b′ → untold i b′ ⊑[ q / ω ] untold i b₀
        told here en κ i wk e₀ e′ = tl₀ i (κ i wk) e₀ e′
        told (in-map {f = f} {t = s} ρ) en κ i wk e₀ e′ =
          told-ᴹ i (U.mapᶜ f) (λ _ → refl) (part s) (part (plant ρ v)) e₀ e′ (told ρ (en-sub en (in-map here) refl) κ i wk)
        told (in-scan {f = f} {z = z} {t = s} ρ) en κ i wk e₀ e′ =
          told-ᴹ i (U.scanᶜ f z) (λ _ → refl) (part s) (part (plant ρ v)) e₀ e′ (told ρ (en-sub en (in-scan here) refl) κ i wk)
        told (in-cut {l = true} ρ) en κ i wk e₀ e′ = told ρ (en-sub en (in-cut here) refl) κ i wk e₀ e′
        told (in-cut {l = false} ρ) en κ i wk () e′
        told (in-lane ρ) en κ i wk e₀ e′ = told ρ (en-sub en (in-lane here) refl) κ i wk e₀ e′
        told (in-take {i = ib} {q = p} {tk = tk} {t = s} ρ) en κ i wk e₀ e′ =
          told-take i ib p tk s (plant ρ v) e₀ e′ (λ ok → told ρ (en-sub en (in-take here) (∧-join ok refl)) κ i wk)
        told (in-outer {op = op} {f = f} {qs = qs} {pl = pl} {t = s} {ls = ls} ρ) en κ i wk e₀ e′ =
          flat-told i op (λ a r → U.subscribe (f a) r) (part s) (part (plant ρ v)) (partLanes ls) (partLanes ls) qs pl
            (toldᴹ i (part s) (part (plant ρ v)) (told ρ (en-sub en (in-outer here) refl) κ i wk) (revive ρ)) (λ t → t) e₀ e′
        told (in-lanes {op = op} {f = f} {qs = qs} {pl = pl} {o = o} {ls = ls} ρ) en κ i wk e₀ e′ =
          flat-told i op (λ a r → U.subscribe (f a) r) (part o) (part o) (partLanes ls) (partLanes (plantᴸ ρ v)) qs pl
            (λ t → t) (toldL ρ (λ ψ → en (in-lanes ψ)) κ i wk) e₀ e′
        told (in-source {r = r} {e = e} {rt = rt} {t = s} {b = b} ρ) en κ i wk e₀ e′ =
          src-told i r e rt (part s) (part (plant ρ v)) (part b) (revive ρ)
            (λ jb → told ρ (en-sub en (in-source here) (∧-join jb refl)) κ i wk) (en here refl) e₀ e′
        told (in-body {r = r} {e = e} {rt = rt} {s = s} {t = b} ρ) en κ i wk e₀ e′ =
          body-told i r e rt (part s) (part b) (part (plant ρ v)) (revive ρ)
            (λ js → told ρ (en-sub en (in-body here) (∧-join js refl)) κ (there i) wk) e₀ e′

        toldL : ∀ {Γ B i₀ π} {ls : List (Sub Γ B)} (ρ : PathLanes ls u i₀ π) → EndedL ls
              → ∀ {K : Pred Γ} → (∀ {C} (j : C ∈ᴸ Δ₀) {c} → BindsL ρ K j c → E j c)
              → ∀ {C ω} (i : C ∈ᴸ Γ) → K i ω → untoldᴸ i (partLanes (plantᴸ ρ v)) ⊑[ q / ω ] untoldᴸ i (partLanes ls)
        toldL (this-lane {t = s} {ls = ls} ρ) en κ i wk t =
          ≡-⊑ (cons-untold i (part (plant ρ v)) (partLanes ls))
            (++-⊑ (untoldᴹ i (part s)) (untoldᴹ i (part (plant ρ v)))
              (toldᴹ i (part s) (part (plant ρ v)) (told ρ (λ ψ → en (this-lane ψ)) κ i wk) (revive ρ)) (λ m → m)
              (≡-⊑ (sym (cons-untold i (part s) (partLanes ls))) t))
        toldL (next-lane {l = l} {ls = ls} ρ) en κ i wk t =
          ≡-⊑ (cons-untold i (part l) (partLanes (plantᴸ ρ v)))
            (++-⊑ (untoldᴹ i (part l)) (untoldᴹ i (part l)) (λ m → m) (toldL ρ (λ ψ → en (next-lane ψ)) κ i wk)
              (≡-⊑ (sym (cons-untold i (part l) (partLanes ls))) t))

    ----------------------------------------------------------------------
    -- NO HEAD BEFORE `q`: every node above heads no sooner after the
    -- replant than before.

    module Behind (q : Pos) (E : Pred Δ₀)
                  (tl₀ : ∀ {C} (i : C ∈ᴸ Δ₀) {c} → E i c → ∀ {b₀ b′} → part u ≡ just b₀ → part v ≡ just b′ → untold i b′ ⊑[ q / c ] untold i b₀)
                  (bl₀ : Each (Heads q) u → Each (Heads q) v) where
      open Telling q E tl₀

      P : ∀ {Γ A} → U.Node Γ A → Set
      P c = Heads q c

      lift-ᴹ : ∀ {Δ A B} (g : U.Node Δ A → U.Node Δ B) (m : Maybe (U.Node Δ A)) → (∀ c → P c → P (g c))
             → (∀ {c} → m ≡ just c → P c) → ∀ {c} → mapᴹ g m ≡ just c → P c
      lift-ᴹ g (just c) up hm refl = up c (hm refl)

      -- A take: taking, its source heading; ending, as before.
      take-up : ∀ {Δ A} ib (p : A → Bool) (tk : Taking Δ A) (x x′ : Sub Δ A)
              → (∀ {c} → part (takeWhileˢ ib p tk x) ≡ just c → P c)
              → (∀ {k c} → is-just (part (takeWhileˢ ib p (ending k c) x′)) ≡ true → is-just (part (takeWhileˢ ib p (ending k c) x)) ≡ true)
              → (isTaking tk ≡ true → ∀ {c} → part x′ ≡ just c → P c)
              → ∀ {c} → part (takeWhileˢ ib p tk x′) ≡ just c → P c
      take-up ib p taking x x′ old te up e′ with sw ib p x′
      ... | inj₁ f′      = lift-ᴹ (U.takeWhileᶜ ib p) (part x′) (λ c → heads-take ib p {c}) (up refl) (trans (sym (f′ taking)) e′)
      ... | inj₂ (n , _) = false≢ (via (n taking) (isj e′))
      take-up ib p (ending k c) x x′ old te up e′ = old (ending-eq ib p k c x x′ (te (isj e′)) e′)
      take-up ib p taken x x′ old te up e′ with sw ib p x′
      ... | inj₁ f′      = false≢ (via (f′ taken) (isj e′))
      ... | inj₂ (n , _) = false≢ (via (n taken) (isj e′))

      root-flat : ∀ {Δ A B} op (g : A → Pos → U.Node Δ B) (o′ : Maybe (U.Node Δ A)) (L′ : List (U.Node Δ B)) (Q : List A) pl
                → P pl → (∀ {c} → o′ ≡ just c → P c) → All P L′
                → ∀ {c} → merged op g o′ L′ Q pl ≡ just c → P c
      root-flat op g o′ L′ Q pl hp ho hL x = subst P (sym (merged-eq op g o′ L′ Q pl x)) (heads-flat op g o′ L′ Q pl hp ho hL)

      -- The source replanted: a source running on either side heads
      -- the connect beside its body; past the end, nothing moved.
      src-up : ∀ {Δ A B} r (e : Maybe Pos) (rt : U.Node Δ A) (s s′ : Maybe (U.Node Δ A)) (mb : Maybe (U.Node (A ∷ Δ) B))
             → (∀ {c} → connected r e rt s mb ≡ just c → P c)
             → (∀ {n} → connected r e rt s mb ≡ just n → ∀ {c₀} → e ≡ just c₀ → s ≡ nothing)
             → (is-just s′ ≡ true → is-just s ≡ true)
             → (is-just mb ≡ true → ∀ {c} → s′ ≡ just c → P c)
             → ((is-just s ∨ is-just e) ≡ true → ∀ {c} → mb ≡ just c → P c)
             → ∀ {c} → connected r e rt s′ mb ≡ just c → P c
      src-up r e        rt s        s′        nothing  old en rv hs hb ()
      src-up r e        rt s        (just c′) (just b) old en rv hs hb refl = heads-source r {b} {c′} (hs refl refl) (hb (∨-l (rv refl)) refl)
      src-up r (just x) rt (just c) nothing   (just b) old en rv hs hb _    with en refl refl
      ... | ()
      src-up r (just x) rt nothing  nothing   (just b) old en rv hs hb refl = old refl
      src-up r nothing  rt s        nothing   (just b) old en rv hs hb ()

      -- The body replanted: past the source's end the new body heads
      -- through a shut, telling only what the old body left untold.
      body-up : ∀ {Δ A B} r (e : Maybe Pos) (rt : U.Node Δ A) (s : Maybe (U.Node Δ A)) (mb mb′ : Maybe (U.Node (A ∷ Δ) B))
              → (is-just mb′ ≡ true → is-just mb ≡ true)
              → (is-just mb ≡ true → ∀ {c} → s ≡ just c → P c)
              → ((is-just s ∨ is-just e) ≡ true → ∀ {c} → mb′ ≡ just c → P c)
              → (∀ {c₀} → e ≡ just c₀ → s ≡ nothing → ∀ {b₀ b′} → mb ≡ just b₀ → mb′ ≡ just b′ → untold (here refl) b′ ⊑[ q / c₀ ] untold (here refl) b₀)
              → (∀ {c₀} → e ≡ just c₀ → s ≡ nothing → ∀ {b₀} → mb ≡ just b₀ → Tells q c₀ (untold (here refl) b₀))
              → (∀ {n} → connected r e rt s mb ≡ just n → s ≡ nothing → ∀ {c₀} → e ≡ just c₀ → P rt)
              → ∀ {c} → connected r e rt s mb′ ≡ just c → P c
      body-up r e         rt s        mb        nothing   rv hs hb tl ut hr ()
      body-up r e         rt (just c) mb        (just b′) rv hs hb tl ut hr refl = heads-source r {b′} {c} (hs (rv refl) refl) (hb refl refl)
      body-up r (just c₀) rt nothing  nothing   (just b′) rv hs hb tl ut hr _    = false≢ (rv refl)
      body-up r (just c₀) rt nothing  (just b₀) (just b′) rv hs hb tl ut hr refl =
        ended-head r c₀ (U.shut (here refl) c₀ b′) rt (U.step rt)
          (shut-heads (here refl) c₀ b′ (hb refl refl) (tl refl refl refl refl (ut refl refl refl))) (hr refl refl refl)
      body-up r nothing   rt nothing  mb        (just b′) rv hs hb tl ut hr ()

      mutual
        shiftE : ∀ {Γ A π} {t : Sub Γ A} (ρ : Path t u π) → Each P t → Untold q t → Ended t
               → ∀ {K : Pred Γ} → (∀ {C} (j : C ∈ᴸ Δ₀) {c} → Binds ρ K j c → E j c) → Each P (plant ρ v)
        shiftE here ev ut en κ = bl₀ ev
        shiftE (in-map {f = f} ρ) ev ut en κ =
          each-map (lift-ᴹ (U.mapᶜ f) (part (plant ρ v)) (λ c → heads-map f {c}) (Each.parts es here refl)) es
          where
            es : Each P (plant ρ v)
            es = shiftE ρ (each-sub ev (in-map here) refl) (ut-sub ut (in-map here) refl) (en-sub en (in-map here) refl) κ
        shiftE (in-scan {f = f} {z = z} ρ) ev ut en κ =
          each-scan (lift-ᴹ (U.scanᶜ f z) (part (plant ρ v)) (λ c → heads-scan f z {c}) (Each.parts es here refl)) es
          where
            es : Each P (plant ρ v)
            es = shiftE ρ (each-sub ev (in-scan here) refl) (ut-sub ut (in-scan here) refl) (en-sub en (in-scan here) refl) κ
        shiftE (in-cut {l = true} ρ) ev ut en κ = each-cut (Each.parts es here refl) (λ _ → es)
          where
            es : Each P (plant ρ v)
            es = shiftE ρ (each-sub ev (in-cut here) refl) (ut-sub ut (in-cut here) refl) (en-sub en (in-cut here) refl) κ
        shiftE (in-cut {l = false} ρ) ev ut en κ = each-cut (λ ()) (λ ())
        shiftE (in-lane ρ) ev ut en κ = each-lane (Each.parts es here refl) es
          where
            es : Each P (plant ρ v)
            es = shiftE ρ (each-sub ev (in-lane here) refl) (ut-sub ut (in-lane here) refl) (en-sub en (in-lane here) refl) κ
        shiftE (in-take {i = ib} {q = p} {tk = tk} {t = s} ρ) ev ut en κ =
          each-take (take-up ib p tk s (plant ρ v) (Each.parts ev here refl) (λ {k} {c} → takes ρ {ib} {p} {k} {c}) (λ ok → Each.parts (es ok) here refl)) es
          where
            es : isTaking tk ≡ true → Each P (plant ρ v)
            es ok = shiftE ρ (each-sub ev (in-take here) sk) (ut-sub ut (in-take here) sk) (en-sub en (in-take here) sk) κ
              where
                sk : isTaking tk ∧ true ≡ true
                sk = ∧-join ok refl
        shiftE (in-outer {op = op} {f = f} {d = d₀} {n = n₀} {qs = qs} {pl = pl} {t = s} {ls = ls} ρ) ev ut en κ =
          each-flat root pool eo eL
          where
            eo : Each P (plant ρ v)
            eo = shiftE ρ (each-sub ev (in-outer here) refl) (ut-sub ut (in-outer here) refl) (en-sub en (in-outer here) refl) κ
            eL : EachL ls
            eL = eachL-of ev
            pool : ∀ {n} → part (plant (in-outer {op = op} {f = f} {d = d₀} {n = n₀} {qs = qs} {pl = pl} {ls = ls} ρ) v) ≡ just n → P pl
            pool x with shown (in-outer {op = op} {f = f} {d = d₀} {n = n₀} {qs = qs} {pl = pl} {ls = ls} ρ) x
            ... | _ , e₀ = Each.pools ev here refl e₀
            root : ∀ {n} → part (plant (in-outer {op = op} {f = f} {d = d₀} {n = n₀} {qs = qs} {pl = pl} {ls = ls} ρ) v) ≡ just n → P n
            root x = root-flat op (λ a r → U.subscribe (f a) r) (part (plant ρ v)) (partLanes ls) qs pl (pool x)
                       (Each.parts eo here refl) (lanes-all ls eL) x
        shiftE (in-lanes {op = op} {f = f} {d = d₀} {n = n₀} {qs = qs} {pl = pl} {o = o} {ls = ls} ρ) ev ut en κ =
          each-flat root pool eo eL
          where
            eo : Each P o
            eo = each-sub ev (in-outer here) refl
            eL : EachL (plantᴸ ρ v)
            eL = shiftL ρ (eachL-of ev) (λ ψ → ut (in-lanes ψ)) (λ ψ → en (in-lanes ψ)) κ
            pool : ∀ {n} → part (plant (in-lanes {op = op} {f = f} {d = d₀} {n = n₀} {qs = qs} {pl = pl} {o = o} ρ) v) ≡ just n → P pl
            pool x with shown (in-lanes {op = op} {f = f} {d = d₀} {n = n₀} {qs = qs} {pl = pl} {o = o} ρ) x
            ... | _ , e₀ = Each.pools ev here refl e₀
            root : ∀ {n} → part (plant (in-lanes {op = op} {f = f} {d = d₀} {n = n₀} {qs = qs} {pl = pl} {o = o} ρ) v) ≡ just n → P n
            root x = root-flat op (λ a r → U.subscribe (f a) r) (part o) (partLanes (plantᴸ ρ v)) qs pl (pool x)
                       (Each.parts eo here refl) (lanes-all (plantᴸ ρ v) eL) x
        shiftE (in-source {k = k} {r = r} {e = e} {rt = rt} {t = s} {b = b} ρ) ev ut en κ =
          each-connect root rest es eb
          where
            es : is-just (part b) ≡ true → Each P (plant ρ v)
            es jb = shiftE ρ (each-sub ev (in-source here) s₁) (ut-sub ut (in-source here) s₁) (en-sub en (in-source here) s₁) κ
              where
                s₁ : is-just (part b) ∧ true ≡ true
                s₁ = ∧-join jb refl
            eb : (is-just (part (plant ρ v)) ∨ is-just e) ≡ true → Each P b
            eb js = each-sub ev (in-body here) (∧-join (∨-mono (is-just e) (revive ρ) js) refl)
            rest : ∀ {n} → part (connectˢ k r e rt (plant ρ v) b) ≡ just n → part (plant ρ v) ≡ nothing → ∀ {c₀} → e ≡ just c₀ → P rt
            rest x _ pe with shown (in-source {k = k} {r = r} {e = e} {rt = rt} {b = b} ρ) x
            ... | _ , e₀ = Each.rests ev here refl e₀ (en here refl e₀ pe) pe
            root : ∀ {n} → part (connectˢ k r e rt (plant ρ v) b) ≡ just n → P n
            root = src-up r e rt (part s) (part (plant ρ v)) (part b) (Each.parts ev here refl) (en here refl) (revive ρ)
                     (λ jb → Each.parts (es jb) here refl) (λ j → Each.parts ev (in-body here) (∧-join j refl))
        shiftE (in-body {k = k} {r = r} {e = e} {rt = rt} {s = s} {t = b} ρ) ev ut en κ =
          each-connect root rest es eb
          where
            eb : (is-just (part s) ∨ is-just e) ≡ true → Each P (plant ρ v)
            eb js = shiftE ρ (each-sub ev (in-body here) sb) (ut-sub ut (in-body here) sb) (en-sub en (in-body here) sb) κ
              where
                sb : (is-just (part s) ∨ is-just e) ∧ true ≡ true
                sb = ∧-join js refl
            es : is-just (part (plant ρ v)) ≡ true → Each P s
            es jb = each-sub ev (in-source here) (∧-join (revive ρ jb) refl)
            rest : ∀ {n} → part (connectˢ k r e rt s (plant ρ v)) ≡ just n → part s ≡ nothing → ∀ {c₀} → e ≡ just c₀ → P rt
            rest x pn pe with shown (in-body {k = k} {r = r} {e = e} {rt = rt} {s = s} ρ) x
            ... | _ , e₀ = Each.rests ev here refl e₀ pn pe
            root : ∀ {n} → part (connectˢ k r e rt s (plant ρ v)) ≡ just n → P n
            root = body-up r e rt (part s) (part b) (part (plant ρ v)) (revive ρ)
                     (λ jb → Each.parts ev (in-source here) (∧-join jb refl))
                     (λ js → Each.parts (eb js) here refl)
                     (λ {c₀} pe pn → told ρ (en-sub en (in-body here) (∧-join (∨-r (is-just (part s)) (cong is-just pe)) refl)) κ (here refl) (pe , pn))
                     (untold-at ut) (Each.rests ev here refl)

        shiftL : ∀ {Γ B i π} {ls : List (Sub Γ B)} (ρ : PathLanes ls u i π) → EachL ls → UntoldL q ls → EndedL ls
               → ∀ {K : Pred Γ} → (∀ {C} (j : C ∈ᴸ Δ₀) {c} → BindsL ρ K j c → E j c) → EachL (plantᴸ ρ v)
        shiftL (this-lane ρ) eL ut en κ =
          eachL-cons (shiftE ρ (eachL-head eL) (λ ψ → ut (this-lane ψ)) (λ ψ → en (this-lane ψ)) κ) (eachL-tail eL)
        shiftL (next-lane ρ) eL ut en κ =
          eachL-cons (eachL-head eL) (shiftL ρ (eachL-tail eL) (λ ψ → ut (next-lane ψ)) (λ ψ → en (next-lane ψ)) κ)

  ------------------------------------------------------------------------
  -- THE TIES: `u` replanted to `v` with its part the same, every node
  -- above it shows the same part and leaves running what it did.

  -- Leftovers rest as they step.
  mutual
    leftover-restful : ∀ {Γ A B} (s : Sub Γ A) → Restful (leftover {B = B} s)
    leftover-restful (pendingˢ o q)                 = rf-rest
    leftover-restful (coldˢ b ph)                   = rf-idle
    leftover-restful (ofˢ q j xs)                   = rf-idle
    leftover-restful doneˢ                          = rf-idle
    leftover-restful (mapˢ f s)                     = leftover-restful s
    leftover-restful (scanˢ f z s)                  = leftover-restful s
    leftover-restful (cutˢ l a s)                   = leftover-restful s
    leftover-restful (laneˢ r s)                    = leftover-restful s
    leftover-restful (takeWhileˢ i q tk s)          = leftover-restful s
    leftover-restful (flatMapˢ op f d n qs pl o ls) = rf-union (leftover-restful o) (leftoverL-restful ls)
    leftover-restful (connectˢ k r e rt s b)        = rf-union rf-burst (rf-under (leftover-restful b))
    leftover-restful (joinˢ j g x st)               = rf-idle

    leftoverL-restful : ∀ {Γ A B} (ls : List (Sub Γ A)) → Restful (leftoverL {B = B} ls)
    leftoverL-restful []       = rf-idle
    leftoverL-restful (s ∷ ls) = rf-union (leftover-restful s) (leftoverL-restful ls)

  -- A lane's pool beside the same rest.
  pool-cons : ∀ {Γ B} (l : Sub Γ B) {ls ls′ : List (Sub Γ B)} → Twin (pooledL ls) (pooledL ls′) → Twin (pooledL (l ∷ ls)) (pooledL (l ∷ ls′))
  pool-cons (laneˢ r s)                    t = tw-if r t (tw-union (tw-refl (leftover s)) t)
  pool-cons (pendingˢ o q)                 t = t
  pool-cons (coldˢ b ph)                   t = t
  pool-cons (ofˢ q j xs)                   t = t
  pool-cons doneˢ                          t = t
  pool-cons (mapˢ f s)                     t = t
  pool-cons (scanˢ f z s)                  t = t
  pool-cons (cutˢ l a s)                   t = t
  pool-cons (takeWhileˢ i q tk s)          t = t
  pool-cons (flatMapˢ op f d n qs pl o ls) t = t
  pool-cons (connectˢ k r e rt s b)        t = t
  pool-cons (joinˢ j g x st)               t = t

  -- A connect's leftover over its source, the source's part the same.
  src-rested : ∀ {Γ A B} r (m m′ : Maybe (U.Node Γ A)) {l l′ : U.Node Γ A} (x : U.Node (A ∷ Γ) ⊤) → m′ ≡ m
             → Restful l → Restful l′ → Twin l l′
             → Twin (U.unionᶜ {B = B} (U.burstingᶜ r (sourced m l)) (U.underᶜ (U.live (sourced m l)) x))
                    (U.unionᶜ {B = B} (U.burstingᶜ r (sourced m′ l′)) (U.underᶜ (U.live (sourced m′ l′)) x))
  src-rested r (just n) _ x refl rf rf′ t = tw-refl _
  src-rested r nothing  _ x refl rf rf′ t = tw-union (tw-burst r rf rf′ t) (tw-shift x rf rf′ t)

  -- What a tree's ties hold, of a seen subtree; of a flatMap's lanes.
  lingers-sub : ∀ {Γ A Δ B π} {t : Sub Γ A} {x : Sub Δ B} → Lingers t → (ρ : Path t x π) → seen ρ ≡ true → Lingers x
  lingers-sub lg ρ sρ = record
    { pools = λ ψ sn → Lingers.pools lg (ρ ⊕ ψ) (seen-⊕ ρ ψ sρ sn)
    ; rests = λ ψ sn → Lingers.rests lg (ρ ⊕ ψ) (seen-⊕ ρ ψ sρ sn) }

  record LingersL {Γ₀ B₀} (ls : List (Sub Γ₀ B₀)) : Set₁ where
    field
      poolsL : ∀ {Γ X A op f d n qs pl i π} {o : Sub Γ X} {ls′ : List (Sub Γ A)}
             → (ψ : PathLanes ls (flatMapˢ op f d n qs pl o ls′) i π) → seenL ψ ≡ true
             → ∀ {c} → part (flatMapˢ op f d n qs pl o ls′) ≡ just c → Leaves pl (pooled d o ls′) × Restful pl
      restsL : ∀ {Γ X B k r e rt i π} {s : Sub Γ X} {b : Sub (X ∷ Γ) B}
             → (ψ : PathLanes ls (connectˢ k r e rt s b) i π) → seenL ψ ≡ true
             → ∀ {n} → part (connectˢ k r e rt s b) ≡ just n
             → part s ≡ nothing → ∀ {c₀} → e ≡ just c₀ → Twin rt (leftover {B = ⊤} s) × Restful rt

  lingersL-of : ∀ {Γ X A op f d n qs pl} {o : Sub Γ X} {ls : List (Sub Γ A)} → Lingers (flatMapˢ op f d n qs pl o ls) → LingersL ls
  lingersL-of lg = record { poolsL = λ ψ → Lingers.pools lg (in-lanes ψ) ; restsL = λ ψ → Lingers.rests lg (in-lanes ψ) }

  lingersL-head : ∀ {Γ B} {l : Sub Γ B} {ls} → LingersL (l ∷ ls) → Lingers l
  lingersL-head lL = record { pools = λ ψ → LingersL.poolsL lL (this-lane ψ) ; rests = λ ψ → LingersL.restsL lL (this-lane ψ) }

  lingersL-tail : ∀ {Γ B} {l : Sub Γ B} {ls} → LingersL (l ∷ ls) → LingersL ls
  lingersL-tail lL = record { poolsL = λ ψ → LingersL.poolsL lL (next-lane ψ) ; restsL = λ ψ → LingersL.restsL lL (next-lane ψ) }

  lgL-cons : ∀ {Γ B} {l : Sub Γ B} {ls} → Lingers l → LingersL ls → LingersL (l ∷ ls)
  lgL-cons ll lL = record
    { poolsL = λ { (this-lane ψ) → Lingers.pools ll ψ ; (next-lane ψ) → LingersL.poolsL lL ψ }
    ; restsL = λ { (this-lane ψ) → Lingers.rests ll ψ ; (next-lane ψ) → LingersL.restsL lL ψ } }

  -- Building a node's ties from its children's.
  lg-map : ∀ {Γ A B} {f : A → B} {s : Sub Γ A} → Lingers s → Lingers (mapˢ f s)
  lg-map ls = record
    { pools = λ { (in-map ψ) → Lingers.pools ls ψ }
    ; rests = λ { (in-map ψ) → Lingers.rests ls ψ } }

  lg-scan : ∀ {Γ A B} {f : B → A → B} {z} {s : Sub Γ A} → Lingers s → Lingers (scanˢ f z s)
  lg-scan ls = record
    { pools = λ { (in-scan ψ) → Lingers.pools ls ψ }
    ; rests = λ { (in-scan ψ) → Lingers.rests ls ψ } }

  lg-lane : ∀ {Γ A r} {s : Sub Γ A} → Lingers s → Lingers (laneˢ r s)
  lg-lane ls = record
    { pools = λ { (in-lane ψ) → Lingers.pools ls ψ }
    ; rests = λ { (in-lane ψ) → Lingers.rests ls ψ } }

  lg-cut : ∀ {Γ A l a} {s : Sub Γ A} → (l ≡ true → Lingers s) → Lingers (cutˢ l a s)
  lg-cut {l = l} ls = record
    { pools = λ { (in-cut ψ) sn → thru l sn (λ x s′ → Lingers.pools (ls x) ψ s′) }
    ; rests = λ { (in-cut ψ) sn → thru l sn (λ x s′ → Lingers.rests (ls x) ψ s′) } }

  lg-take : ∀ {Γ A i p tk} {s : Sub Γ A} → (isTaking tk ≡ true → Lingers s) → Lingers (takeWhileˢ i p tk s)
  lg-take {tk = tk} ls = record
    { pools = λ { (in-take ψ) sn → thru (isTaking tk) sn (λ x s′ → Lingers.pools (ls x) ψ s′) }
    ; rests = λ { (in-take ψ) sn → thru (isTaking tk) sn (λ x s′ → Lingers.rests (ls x) ψ s′) } }

  lg-flat : ∀ {Γ X A op f d n qs pl} {o : Sub Γ X} {ls : List (Sub Γ A)}
          → (∀ {c} → part (flatMapˢ op f d n qs pl o ls) ≡ just c → Leaves pl (pooled d o ls) × Restful pl)
          → Lingers o → LingersL ls → Lingers (flatMapˢ op f d n qs pl o ls)
  lg-flat pool lo lL = record
    { pools = λ { here _ x → pool x ; (in-outer ψ) → Lingers.pools lo ψ ; (in-lanes ψ) → LingersL.poolsL lL ψ }
    ; rests = λ { (in-outer ψ) → Lingers.rests lo ψ ; (in-lanes ψ) → LingersL.restsL lL ψ } }

  lg-connect : ∀ {Γ X B k r e rt} {s : Sub Γ X} {b : Sub (X ∷ Γ) B}
             → (∀ {n} → part (connectˢ k r e rt s b) ≡ just n → part s ≡ nothing → ∀ {c₀} → e ≡ just c₀ → Twin rt (leftover {B = ⊤} s) × Restful rt)
             → (is-just (part b) ≡ true → Lingers s) → ((is-just (part s) ∨ is-just e) ≡ true → Lingers b)
             → Lingers (connectˢ k r e rt s b)
  lg-connect {e = e} {s = s} {b} rest ls lb = record
    { pools = λ { (in-source ψ) sn → thru (is-just (part b)) sn (λ x s′ → Lingers.pools (ls x) ψ s′)
                ; (in-body ψ) sn → thru (is-just (part s) ∨ is-just e) sn (λ x s′ → Lingers.pools (lb x) ψ s′) }
    ; rests = λ { here _ x pn pe → rest x pn pe
                ; (in-source ψ) sn → thru (is-just (part b)) sn (λ x s′ → Lingers.rests (ls x) ψ s′)
                ; (in-body ψ) sn → thru (is-just (part s) ∨ is-just e) sn (λ x s′ → Lingers.rests (lb x) ψ s′) } }

  module Tying {Δ₀ A₀} {u v : Sub Δ₀ A₀}
               (same₀ : part v ≡ part u)
               (take₀ : ∀ {i p tk} → part (takeWhileˢ i p tk v) ≡ part (takeWhileˢ i p tk u))
               (rs₀ : ∀ {C} → Twin (leftover {B = C} u) (leftover {B = C} v))
               (lp₀ : ∀ {ls} → Twin (pooledL (u ∷ ls)) (pooledL (v ∷ ls)))
               (lb₀ : Lingers u → Lingers v) where

    -- Every part above the node the same.
    mutual
      same : ∀ {Γ A π} {t : Sub Γ A} (ρ : Path t u π) → part (plant ρ v) ≡ part t
      same here = same₀
      same (in-map {f = f} ρ) = cong (mapᴹ (U.mapᶜ f)) (same ρ)
      same (in-scan {f = f} {z = z} ρ) = cong (mapᴹ (U.scanᶜ f z)) (same ρ)
      same (in-cut {l = l} ρ) = cong (λ m → if l then m else nothing) (same ρ)
      same (in-lane ρ) = same ρ
      same (in-take {i = i} {q = p} {tk = tk} ρ) = take-same {i = i} {p = p} {tk = tk} ρ
      same (in-outer {op = op} {f = f} {qs = qs} {pl = pl} {ls = ls} ρ) =
        cong (λ m → merged op (λ x r → U.subscribe (f x) r) m (partLanes ls) qs pl) (same ρ)
      same (in-lanes {op = op} {f = f} {qs = qs} {pl = pl} {o = o} ρ) =
        cong (λ L → merged op (λ x r → U.subscribe (f x) r) (part o) L qs pl) (sameL ρ)
      same (in-source {r = r} {e = e} {rt = rt} {b = b} ρ) = cong (λ m → connected r e rt m (part b)) (same ρ)
      same (in-body {r = r} {e = e} {rt = rt} {s = s} ρ) = cong (connected r e rt (part s)) (same ρ)

      sameL : ∀ {Γ B i π} {ls : List (Sub Γ B)} (ρ : PathLanes ls u i π) → partLanes (plantᴸ ρ v) ≡ partLanes ls
      sameL (this-lane {ls = ls} ρ) = cong (λ m → consᴹ m (partLanes ls)) (same ρ)
      sameL (next-lane {l = l} ρ) = cong (consᴹ (part l)) (sameL ρ)

      -- A take above the node: switched alike, since only a cut
      -- switches it and the path keeps every node's own constructor.
      take-same : ∀ {Γ A π i p tk} {t : Sub Γ A} (ρ : Path t u π) → part (takeWhileˢ i p tk (plant ρ v)) ≡ part (takeWhileˢ i p tk t)
      take-same {i = i} {p} {tk} here = take₀ {i} {p} {tk}
      take-same {i = i} {p} {tk} (in-cut {l = l} {a = a} ρ) = cong (λ m → if l then taking? i p tk m else nothing) (same (in-cut {l = l} {a = a} ρ))
      take-same {i = i} {p} {tk} ρ@(in-map _)    = cong (taking? i p tk) (same ρ)
      take-same {i = i} {p} {tk} ρ@(in-scan _)   = cong (taking? i p tk) (same ρ)
      take-same {i = i} {p} {tk} ρ@(in-lane _)   = cong (taking? i p tk) (same ρ)
      take-same {i = i} {p} {tk} ρ@(in-take _)   = cong (taking? i p tk) (same ρ)
      take-same {i = i} {p} {tk} ρ@(in-outer _)  = cong (taking? i p tk) (same ρ)
      take-same {i = i} {p} {tk} ρ@(in-lanes _)  = cong (taking? i p tk) (same ρ)
      take-same {i = i} {p} {tk} ρ@(in-source _) = cong (taking? i p tk) (same ρ)
      take-same {i = i} {p} {tk} ρ@(in-body _)   = cong (taking? i p tk) (same ρ)

    -- Every node above leaves running what it did.
    mutual
      restedUp : ∀ {Γ A π} {t : Sub Γ A} (ρ : Path t u π) → ∀ {C} → Twin (leftover {B = C} t) (leftover {B = C} (plant ρ v))
      restedUp here = rs₀
      restedUp (in-map ρ) = restedUp ρ
      restedUp (in-scan ρ) = restedUp ρ
      restedUp (in-cut ρ) = restedUp ρ
      restedUp (in-lane ρ) = restedUp ρ
      restedUp (in-take ρ) = restedUp ρ
      restedUp (in-outer {ls = ls} ρ) = tw-union (restedUp ρ) (tw-refl (leftoverL ls))
      restedUp (in-lanes {o = o} ρ) = tw-union (tw-refl (leftover o)) (restedUpL ρ)
      restedUp (in-source {r = r} {t = s} {b = b} ρ) =
        src-rested r (part s) (part (plant ρ v)) (leftover b) (same ρ) (leftover-restful s) (leftover-restful (plant ρ v)) (restedUp ρ)
      restedUp (in-body {r = r} {s = s} ρ) =
        tw-union (tw-refl (U.burstingᶜ r (sourced (part s) (leftover s)))) (tw-under (U.live (sourced (part s) (leftover s))) (restedUp ρ))

      restedUpL : ∀ {Γ B i π} {ls : List (Sub Γ B)} (ρ : PathLanes ls u i π) → ∀ {C} → Twin (leftoverL {B = C} ls) (leftoverL {B = C} (plantᴸ ρ v))
      restedUpL (this-lane {ls = ls} ρ) = tw-union (restedUp ρ) (tw-refl (leftoverL ls))
      restedUpL (next-lane {l = l} ρ) = tw-union (tw-refl (leftover l)) (restedUpL ρ)

    -- A lane's pool, its lane replanted.
    lane-pool : ∀ {Γ B π} {l : Sub Γ B} {ls} (ρ : Path l u π) → Twin (pooledL (l ∷ ls)) (pooledL (plant ρ v ∷ ls))
    lane-pool here = lp₀
    lane-pool {ls = ls} (in-lane {r = r} ρ) = tw-if r (tw-refl (pooledL ls)) (tw-union (restedUp ρ) (tw-refl (pooledL ls)))
    lane-pool {ls = ls} (in-map ρ)    = tw-refl (pooledL ls)
    lane-pool {ls = ls} (in-scan ρ)   = tw-refl (pooledL ls)
    lane-pool {ls = ls} (in-cut ρ)    = tw-refl (pooledL ls)
    lane-pool {ls = ls} (in-take ρ)   = tw-refl (pooledL ls)
    lane-pool {ls = ls} (in-outer ρ)  = tw-refl (pooledL ls)
    lane-pool {ls = ls} (in-lanes ρ)  = tw-refl (pooledL ls)
    lane-pool {ls = ls} (in-source ρ) = tw-refl (pooledL ls)
    lane-pool {ls = ls} (in-body ρ)   = tw-refl (pooledL ls)

    pooledUpL : ∀ {Γ B i π} {ls : List (Sub Γ B)} (ρ : PathLanes ls u i π) → Twin (pooledL ls) (pooledL (plantᴸ ρ v))
    pooledUpL (this-lane ρ) = lane-pool ρ
    pooledUpL (next-lane {l = l} ρ) = pool-cons l (pooledUpL ρ)

    via-same : ∀ {Γ A π} {t : Sub Γ A} (ρ : Path t u π) {c} → part (plant ρ v) ≡ just c → part t ≡ just c
    via-same ρ x = trans (sym (same ρ)) x

    mutual
      shiftLg : ∀ {Γ A π} {t : Sub Γ A} (ρ : Path t u π) → Lingers t → Lingers (plant ρ v)
      shiftLg here lg = lb₀ lg
      shiftLg (in-map ρ) lg = lg-map (shiftLg ρ (lingers-sub lg (in-map here) refl))
      shiftLg (in-scan ρ) lg = lg-scan (shiftLg ρ (lingers-sub lg (in-scan here) refl))
      shiftLg (in-cut ρ) lg = lg-cut (λ x → shiftLg ρ (lingers-sub lg (in-cut here) (∧-join x refl)))
      shiftLg (in-lane ρ) lg = lg-lane (shiftLg ρ (lingers-sub lg (in-lane here) refl))
      shiftLg (in-take ρ) lg = lg-take (λ x → shiftLg ρ (lingers-sub lg (in-take here) (∧-join x refl)))
      shiftLg (in-outer {op = op} {f = f} {d = d} {n = n} {qs = qs} {pl = pl} {t = s} {ls = ls} ρ) lg =
        lg-flat pool (shiftLg ρ (lingers-sub lg (in-outer here) refl)) (lingersL-of lg)
        where
          pool : ∀ {c} → part (flatMapˢ op f d n qs pl (plant ρ v) ls) ≡ just c → Leaves pl (pooled d (plant ρ v) ls) × Restful pl
          pool x = lv-tie (Lingers.pools lg here refl (via-same (in-outer {op = op} {f = f} {d = d} {n = n} {qs = qs} {pl = pl} {ls = ls} ρ) x))
                     (proj₁ (tw-union (tw-if d (restedUp ρ) (tw-refl U.idleᶜ)) (tw-refl (pooledL ls))))
      shiftLg (in-lanes {op = op} {f = f} {d = d} {n = n} {qs = qs} {pl = pl} {o = o} {ls = ls} ρ) lg =
        lg-flat pool (lingers-sub lg (in-outer here) refl) (shiftLgL ρ (lingersL-of lg))
        where
          pool : ∀ {c} → part (flatMapˢ op f d n qs pl o (plantᴸ ρ v)) ≡ just c → Leaves pl (pooled d o (plantᴸ ρ v)) × Restful pl
          pool x = lv-tie (Lingers.pools lg here refl (via-same (in-lanes {op = op} {f = f} {d = d} {n = n} {qs = qs} {pl = pl} {o = o} ρ) x))
                     (proj₁ (tw-union (tw-refl (if d then leftover o else U.idleᶜ)) (pooledUpL ρ)))
      shiftLg (in-source {k = k} {r = r} {e = e} {rt = rt} {t = s} {b = b} ρ) lg = lg-connect rest ls lb
        where
          ls : is-just (part b) ≡ true → Lingers (plant ρ v)
          ls jb = shiftLg ρ (lingers-sub lg (in-source here) (∧-join jb refl))
          lb : (is-just (part (plant ρ v)) ∨ is-just e) ≡ true → Lingers b
          lb js = lingers-sub lg (in-body here) (∧-join (subst (λ m → (is-just m ∨ is-just e) ≡ true) (same ρ) js) refl)
          rest : ∀ {n} → part (connectˢ k r e rt (plant ρ v) b) ≡ just n → part (plant ρ v) ≡ nothing → ∀ {c₀} → e ≡ just c₀
               → Twin rt (leftover {B = ⊤} (plant ρ v)) × Restful rt
          rest x pn pe = tw-tie (Lingers.rests lg here refl (via-same (in-source {k = k} {r = r} {e = e} {rt = rt} {b = b} ρ) x) (trans (sym (same ρ)) pn) pe) (restedUp ρ)
      shiftLg (in-body {k = k} {r = r} {e = e} {rt = rt} {s = s} {t = b} ρ) lg = lg-connect rest ls lb
        where
          ls : is-just (part (plant ρ v)) ≡ true → Lingers s
          ls jb = lingers-sub lg (in-source here) (∧-join (subst (λ m → is-just m ≡ true) (same ρ) jb) refl)
          lb : (is-just (part s) ∨ is-just e) ≡ true → Lingers (plant ρ v)
          lb js = shiftLg ρ (lingers-sub lg (in-body here) (∧-join js refl))
          rest : ∀ {n} → part (connectˢ k r e rt s (plant ρ v)) ≡ just n → part s ≡ nothing → ∀ {c₀} → e ≡ just c₀
               → Twin rt (leftover {B = ⊤} s) × Restful rt
          rest x pn pe = Lingers.rests lg here refl (via-same (in-body {k = k} {r = r} {e = e} {rt = rt} {s = s} ρ) x) pn pe

      shiftLgL : ∀ {Γ B i π} {ls : List (Sub Γ B)} (ρ : PathLanes ls u i π) → LingersL ls → LingersL (plantᴸ ρ v)
      shiftLgL (this-lane ρ) lL = lgL-cons (shiftLg ρ (lingersL-head lL)) (lingersL-tail lL)
      shiftLgL (next-lane ρ) lL = lgL-cons (lingersL-head lL) (shiftLgL ρ (lingersL-tail lL))

  module Shift {T : Sub [] R} {Δ A π} {u : Sub Δ A} (ρ : Path T u π) where
    -- Every node the replanted tree holds heads no earlier than `q`.
    shift-behind : (v : Sub Δ A) → ∀ {q} → Untold q T → Ended T → Heading q (Bound ρ) u v → Each (Heads q) T → Each (Heads q) (plant ρ v)
    shift-behind v {q} ut en hd ev =
      Walk.Behind.shiftE (Heading.head-revive hd) (λ {i} {p} {k} {c} → Heading.head-take hd {i} {p} {k} {c}) q (Bound ρ) (Heading.head-told hd) (Heading.head-below hd)
        ρ ev ut en (λ j w → w)

    -- Every tie the replanted tree holds, kept.
    shift-lingers : (v : Sub Δ A) → Ended T → Lingering u v → Lingers T → Lingers (plant ρ v)
    shift-lingers v _ lg lt =
      Tying.shiftLg (Lingering.ling-same lg) (λ {i} {p} {tk} → Lingering.ling-take lg {i} {p} {tk}) (Lingering.ling-rested lg) (Lingering.ling-pool lg) (Lingering.ling-below lg) ρ lt
