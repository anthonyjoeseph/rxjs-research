{-# OPTIONS --guardedness #-}

-- THE FRAME: a write at one node's own cell, against everything the
-- relation holds of the rest of the tree.
module adequacy.Frame where

open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here)
import Data.List.Relation.Unary.Any as Any
open import Data.List.Relation.Unary.All using (All; []; _∷_; map) renaming (lookup to lookupᴬ)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to all-++⁺)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; _∷_)
open import Data.List.Relation.Unary.Linked using (_∷_)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴸ_)
open import Level using (lift)
open import Data.Maybe using (Maybe; just; nothing; is-just)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
open import Data.Sum using (_⊎_; [_,_]′)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Bool using (true; false)

open import denotation.MonotonicList using (Events∞; Timeline)
import denotation.Unfold as U
open import denotation.MonotonicList using () renaming (sub to subᴾ)
open import operation.Machine using (module Machine)
open import adequacy.Strong using (module Strongly)
open import adequacy.Torn using (module Tearing)
import Tree as T
open import operation.PureObservable using (Out)
open import operation.AbstractObservable using (module Heap; module Run) renaming (module Machine to Shared)
open import adequacy.Ghost using (module Ghosting)

open Events∞

module Framing (R : Set) where
  open Machine R using (Mach; Read)
  open Shared Timeline (Out R) using (Conf; Heapᴹ; store; stored)
  open Heap using () renaming (same to same⊑)
  open Strongly R using (Strong; Sub; scanˢ; here; module At; Queue; Kernels; Meaning; Owned; Path; in-scan; in-source; _⊕_; names; Each; Heads; seen; Books)
  open Strongly.Against R using (CtlAs)
  open Tearing R using (Alike; part-alike; look-store; get-put-same)
  open Ghosting R using (module Climbing; Lifts; Climbing)
  open Read

  -- A scan's part, its accumulator written: its source's part, the
  -- accumulator the value written, the source's names apart from it.
  scan-part : ∀ {h} (H : Heapᴹ h) {Δ A B} {f : B → A → B} {r} {u : Sub h Δ A} → AllPairs _≢_ (names (scanˢ f r u))
            → ∀ {c′} z → At.part H u ≡ just c′ → At.part (store H r (lift z)) (scanˢ f r u) ≡ just (U.scanᶜ f z c′)
  scan-part H {r = r} {u} (nr ∷ _) z pu
    rewrite get-put-same H r {y = stored (lift z) same⊑}
          | part-alike H (store H r (lift z)) u (λ j m → look-store H r j (lookupᴬ nr m)) | pu = refl

  -- A WRITE AT A SCAN'S ACCUMULATOR, FRAMED: nothing the relation holds
  -- reads an accumulator but the parts above it, and an ancestor's lift
  -- reads only its siblings and its own cells.
  postulate
    scan-owned   : ∀ {h} (H : Heapᴹ h) {T : Sub h [] R} {Δ A B} {f : B → A → B} {r} {u : Sub h Δ A} → Path T (scanˢ f r u) → AllPairs _≢_ (names T)
                 → ∀ {p ctl bs} {ca : CtlAs T p ctl bs} z → Owned H T ca → Owned (store H r (lift z)) T ca
    scan-kernels : ∀ {h} (H : Heapᴹ h) {T : Sub h [] R} {Δ A B} {f : B → A → B} {r} {u : Sub h Δ A} → Path T (scanˢ f r u) → AllPairs _≢_ (names T)
                 → ∀ z → Kernels H T → Kernels (store H r (lift z)) T
    scan-meaning : ∀ {h} (H : Heapᴹ h) {T : Sub h [] R} {Δ A B} {f : B → A → B} {r} {u : Sub h Δ A} → Path T (scanˢ f r u) → AllPairs _≢_ (names T)
                 → ∀ z → Meaning H T → Meaning (store H r (lift z)) T
    scan-queue   : ∀ {h} (H : Heapᴹ h) {T : Sub h [] R} {Δ A B} {f : B → A → B} {r} {u : Sub h Δ A} → Path T (scanˢ f r u) → AllPairs _≢_ (names T)
                 → ∀ {p clk ts} z → Queue H p clk ts T → Queue (store H r (lift z)) p clk ts T
    scan-lifts   : ∀ {h} (H : Heapᴹ h) {T : Sub h [] R} {Δ A B} {f : B → A → B} {r} {u : Sub h Δ A} (ρ : Path T (scanˢ f r u)) → AllPairs _≢_ (names T)
                 → ∀ {s S} z → Lifts H ρ s S → Lifts (store H r (lift z)) ρ s S

    -- A path the write leaves seen it saw before, to a node that reads
    -- alike or sits above the scan.
    scan-sees    : ∀ {h} (H : Heapᴹ h) {T : Sub h [] R} {Δ A B} {f : B → A → B} {r} {u : Sub h Δ A} → Path T (scanˢ f r u) → AllPairs _≢_ (names T)
                 → ∀ z {Δ′ A′} {x : Sub h Δ′ A′} (ψ : Path T x) → seen (store H r (lift z)) ψ ≡ true
                 → seen H ψ ≡ true × (Alike H (store H r (lift z)) (names x) ⊎ Path x (scanˢ f r u))

    -- Whether a node has a part never reads an accumulator.
    scan-defined : ∀ {h} (H : Heapᴹ h) {T : Sub h [] R} {Δ A B} {f : B → A → B} {r} {u : Sub h Δ A} → Path T (scanˢ f r u) → AllPairs _≢_ (names T)
                 → ∀ z {Δ′ A′} {x : Sub h Δ′ A′} → Path T x → is-just (At.part (store H r (lift z)) x) ≡ is-just (At.part H x)

    -- The scan and every part above it still head no sooner than where
    -- the run is: a part's next event is bounded by its children's, and
    -- the scan's is its source's.
    scan-above   : ∀ {g ℓ m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {f : B → A → B} {r} {u : Sub (Conf.world (Mach.conf m₁)) Δ A}
                   (ρ : Path T (scanˢ f r u)) {y : A} → Climbing g ℓ m₁ (ρ ⊕ in-scan here) y
                 → ∀ {Δ′ A′} {x : Sub (Conf.world (Mach.conf m₁)) Δ′ A′} (ψ : Path T x) → Path x (scanˢ f r u) → seen (Conf.heap (Mach.conf m₁)) ψ ≡ true
                 → ∀ {c} → At.part (store (Conf.heap (Mach.conf m₁)) r (lift (f (At.val (Conf.heap (Mach.conf m₁)) r) y))) x ≡ just c
                 → Heads (Conf.pos (Mach.conf m₁)) c

  just-of : ∀ {ℓ} {X : Set ℓ} {m : Maybe X} → is-just m ≡ true → Σ X λ c → m ≡ just c
  just-of {m = just c} _ = c , refl

  none-of : ∀ {ℓ} {X : Set ℓ} {m : Maybe X} → is-just m ≡ false → m ≡ nothing
  none-of {m = nothing} _ = refl

  -- The parts above the scan move with it; every other part reads alike.
  scan-behind : ∀ {g ℓ m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {f : B → A → B} {r} {u : Sub (Conf.world (Mach.conf m₁)) Δ A}
                (ρ : Path T (scanˢ f r u)) {y : A} → Climbing g ℓ m₁ (ρ ⊕ in-scan here) y
              → Each (store (Conf.heap (Mach.conf m₁)) r (lift (f (At.val (Conf.heap (Mach.conf m₁)) r) y))) (Heads (Conf.pos (Mach.conf m₁))) T
  scan-behind {m₁ = m₁} {f = f} {r} ρ {y} cl = record
    { parts = λ {u = x} ψ sn e → [ (λ (al : Alike H H′ (names x)) → Each.parts bh ψ (proj₁ (sees ψ sn)) (trans (sym (part-alike H H′ x al)) e))
                                 , (λ π → scan-above ρ cl ψ π (proj₁ (sees ψ sn)) e) ]′ (proj₂ (sees ψ sn))
    ; pools = λ ψ sn e → Each.pools bh ψ (proj₁ (sees ψ sn)) (proj₂ (just-of (trans (sym (def ψ)) (cong is-just e))))
    ; rests = λ ψ sn e none ej → Each.rests bh ψ (proj₁ (sees ψ sn)) (proj₂ (just-of (trans (sym (def ψ)) (cong is-just e))))
                                   (none-of (trans (sym (def (ψ ⊕ in-source here))) (cong is-just none))) ej }
    where
      H  = Conf.heap (Mach.conf m₁)
      H′ = store H r (lift (f (At.val H r) y))
      fs = Books.fresh (Climbing.books cl)
      bh = Climbing.behind cl
      sees = scan-sees H ρ fs (f (At.val H r) y)
      def  = scan-defined H ρ fs (f (At.val H r) y)
