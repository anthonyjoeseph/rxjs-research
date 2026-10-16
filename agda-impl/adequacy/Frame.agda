{-# OPTIONS --guardedness #-}

-- THE FRAME: a write at one node's own cell, against everything the
-- relation holds of the rest of the tree.
module adequacy.Frame where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
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

open import denotation.MonotonicList using (Events∞; Timeline; Pos)
import denotation.Unfold as U
open import denotation.MonotonicList using () renaming (sub to subᴾ)
open import operation.Machine using (module Machine)
open import adequacy.Strong using (module Strongly)
open import adequacy.Torn using (module Tearing)
import Tree as T
open import operation.PureObservable using (Out; Pureᴾ)
open import operation.AbstractObservable using (base; module Heap; module Run) renaming (module Machine to Shared)
open import adequacy.Ghost using (module Ghosting)

open Events∞

module Framing (R : Set) where
  open Machine R using (Mach; Read)
  open Run (Pureᴾ R) using (Ref)
  open Shared Timeline (Out R) using (Conf; Heapᴹ; store; stored)
  open Heap using () renaming (same to same⊑)
  open Strongly R using (Strong; Sub; scanˢ; here; module At; Queue; Kernels; Meaning; Owned; Path; in-scan; in-source; _⊕_; names; Each; Heads; seen; Books;
                         mapˢ; takeWhileˢ; flatMapˢ; connectˢ; Lane; lane; PathLanes; this-lane; next-lane; in-map; in-take; in-outer; in-lanes; in-body; in-defer; seen-join)
  open Strongly.Against R using (CtlAs)
  open Tearing R using (Alike; part-alike; look-store; get-put-same; fresh-path)
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


  head-map : ∀ {Γ A B} (g : A → B) (s : U.Step Γ A) → U.headˢ (U.mapˢ g s) ≡ U.headˢ s
  head-map g (U.outˢ k a c) = refl
  head-map g (U.skipˢ k c)  = refl
  head-map g (U.endˢ k)     = refl
  head-map g U.hushˢ        = refl

  head-scan : ∀ {Γ A B} (g : B → A → B) z (s : U.Step Γ A) → U.headˢ (U.scanˢ g z s) ≡ U.headˢ s
  head-scan g z (U.outˢ k a c) = refl
  head-scan g z (U.skipˢ k c)  = refl
  head-scan g z (U.endˢ k)     = refl
  head-scan g z U.hushˢ        = refl

  heads-map : ∀ {Γ A B q} (g : A → B) {c : U.Node Γ A} → Heads q c → Heads q (U.mapᶜ g c)
  heads-map g {c} hd e = hd (trans (sym (head-map g (U.step c))) e)

  heads-scan : ∀ {Γ A B q} (g : B → A → B) z {c : U.Node Γ A} → Heads q c → Heads q (U.scanᶜ g z c)
  heads-scan g z {c} hd e = hd (trans (sym (head-scan g z (U.step c))) e)

  -- A scan's head is its source's, whatever its accumulator.
  heads-rescan : ∀ {Γ A B q} (g : B → A → B) {z₁ z₂} {c : U.Node Γ A} → Heads q (U.scanᶜ g z₁ c) → Heads q (U.scanᶜ g z₂ c)
  heads-rescan g {z₁} {z₂} {c} hd e = hd (trans (head-scan g z₁ (U.step c)) (trans (sym (head-scan g z₂ (U.step c))) e))

  -- THE PARTS ABOVE A WRITTEN SCAN, walked down to it: a map's, a scan's
  -- and a defer's head is their child's; a take's, a flatMap's and a
  -- connect's are each bounded by what is below them.
  module Above {h} (H : Heapᴹ h) {T : Sub h [] R} {Δ A B} (f : B → A → B) (r : Ref h (base B)) (u : Sub h Δ A)
               (fs : AllPairs _≢_ (names T)) (z : B) (q : Pos) (bh : Each H (Heads q) T) where
    H′ = store H r (lift z)

    Up : ∀ {Δ′ A′} {x : Sub h Δ′ A′} → Path T x → Set₁
    Up {x = x} ψ = seen H ψ ≡ true → ∀ {c} → At.part H′ x ≡ just c → Heads q c

    via : ∀ {Δ₀ B₀} {c k} {t : Sub h Δ₀ B₀} {ls : List (Lane h Δ₀ B₀)} → lane c k t ∈ᴸ ls → PathLanes ls t
    via (here refl) = this-lane here
    via (there m)   = next-lane (via m)

    postulate
      up-take   : ∀ {Δ′ A′} {i p c k tk} {s : Sub h Δ′ A′} (ψ : Path T (takeWhileˢ i p c k tk s)) → Path s (scanˢ f r u)
                → Up (ψ ⊕ in-take here) → Up ψ
      up-outer  : ∀ {Δ′ A′ B′} {op g fl oc k rf pl} {so : Sub h Δ′ A′} {ls : List (Lane h Δ′ B′)}
                  (ψ : Path T (flatMapˢ op g fl oc k rf pl so ls)) → Path so (scanˢ f r u) → Up (ψ ⊕ in-outer here) → Up ψ
      up-lanes  : ∀ {Δ′ A′ B′} {op g fl oc k rf pl} {so : Sub h Δ′ A′} {ls : List (Lane h Δ′ B′)}
                  (ψ : Path T (flatMapˢ op g fl oc k rf pl so ls)) {c k′} {t : Sub h Δ′ B′} (m : lane c k′ t ∈ᴸ ls)
                → Path t (scanˢ f r u) → Up (ψ ⊕ in-lanes (via m)) → Up ψ
      up-source : ∀ {Δ′ A′ B′} {S c b kb k fd rp e rt} {src : Sub h Δ′ A′} {bd : Sub h (A′ ∷ Δ′) B′}
                  (ψ : Path T (connectˢ S c b kb k fd rp e rt src bd)) → Path src (scanˢ f r u) → Up (ψ ⊕ in-source here) → Up ψ
      up-body   : ∀ {Δ′ A′ B′} {S c b kb k fd rp e rt} {src : Sub h Δ′ A′} {bd : Sub h (A′ ∷ Δ′) B′}
                  (ψ : Path T (connectˢ S c b kb k fd rp e rt src bd)) → Path bd (scanˢ f r u) → Up (ψ ⊕ in-body here) → Up ψ

    lift-map : ∀ {Δ′ A′ B′} (g : A′ → B′) (m : Maybe (U.Node Δ′ A′)) → (∀ {c} → m ≡ just c → Heads q c)
             → ∀ {c} → At.mapᴹ H′ (U.mapᶜ g) m ≡ just c → Heads q c
    lift-map g (just c₀) up refl = heads-map g {c₀} (up refl)
    lift-map g nothing   up ()

    lift-scan : ∀ {Δ′ A′ B′} (g : B′ → A′ → B′) z′ (m : Maybe (U.Node Δ′ A′)) → (∀ {c} → m ≡ just c → Heads q c)
              → ∀ {c} → At.mapᴹ H′ (U.scanᶜ g z′) m ≡ just c → Heads q c
    lift-scan g z′ (just c₀) up refl = heads-scan g z′ {c₀} (up refl)
    lift-scan g z′ nothing   up ()

    base-lemma : (m m′ : Maybe (U.Node Δ A)) → m′ ≡ m → (∀ {c} → At.mapᴹ H (U.scanᶜ f (At.val H r)) m ≡ just c → Heads q c)
               → ∀ {c} → At.mapᴹ H′ (U.scanᶜ f (At.val H′ r)) m′ ≡ just c → Heads q c
    base-lemma (just c₀) .(just c₀) refl old refl = heads-rescan f {c = c₀} (old refl)
    base-lemma nothing   .nothing   refl old ()

    up-base : (ψ : Path T (scanˢ f r u)) → Up ψ
    up-base ψ sn e with fresh-path ψ fs
    ... | nr ∷ _ = base-lemma (At.part H u) (At.part H′ u) (part-alike H H′ u (λ j m → look-store H r j (lookupᴬ nr m))) (Each.parts bh ψ sn) e

    mutual
      above : ∀ {Δ′ A′} {x : Sub h Δ′ A′} (ψ : Path T x) → Path x (scanˢ f r u) → Up ψ
      above ψ here                               = up-base ψ
      above ψ (in-map {f = g} {t = s} π)       sn = lift-map g (At.part H′ s) (above (ψ ⊕ in-map here) π (seen-join H ψ (in-map here) sn refl))
      above ψ (in-scan {f = g} {r = r′} {t = s} π) sn =
        lift-scan g (At.val H′ r′) (At.part H′ s) (above (ψ ⊕ in-scan here) π (seen-join H ψ (in-scan here) sn refl))
      above ψ (in-defer π)                    sn = above (ψ ⊕ in-defer here) π (seen-join H ψ (in-defer here) sn refl)
      above ψ (in-take π)                        = up-take ψ π (above (ψ ⊕ in-take here) π)
      above ψ (in-outer π)                       = up-outer ψ π (above (ψ ⊕ in-outer here) π)
      above ψ (in-lanes πL)                      = aboveL ψ (λ m → m) πL
      above ψ (in-source π)                      = up-source ψ π (above (ψ ⊕ in-source here) π)
      above ψ (in-body π)                        = up-body ψ π (above (ψ ⊕ in-body here) π)

      aboveL : ∀ {Δ′ A′ B′} {op g fl oc k rf pl} {so : Sub h Δ′ A′} {ls₀ ls : List (Lane h Δ′ B′)}
               (ψ : Path T (flatMapˢ op g fl oc k rf pl so ls₀)) → (∀ {l} → l ∈ᴸ ls → l ∈ᴸ ls₀) → PathLanes ls (scanˢ f r u) → Up ψ
      aboveL ψ κ (this-lane π)  = up-lanes ψ (κ (here refl)) π (above (ψ ⊕ in-lanes (via (κ (here refl)))) π)
      aboveL ψ κ (next-lane πL) = aboveL ψ (λ m → κ (there m)) πL

  -- The scan and every part above it still head no sooner than where
  -- the run is.
  scan-above : ∀ {g ℓ m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {f : B → A → B} {r} {u : Sub (Conf.world (Mach.conf m₁)) Δ A}
               (ρ : Path T (scanˢ f r u)) {y : A} → Climbing g ℓ m₁ (ρ ⊕ in-scan here) y
             → ∀ {Δ′ A′} {x : Sub (Conf.world (Mach.conf m₁)) Δ′ A′} (ψ : Path T x) → Path x (scanˢ f r u) → seen (Conf.heap (Mach.conf m₁)) ψ ≡ true
             → ∀ {c} → At.part (store (Conf.heap (Mach.conf m₁)) r (lift (f (At.val (Conf.heap (Mach.conf m₁)) r) y))) x ≡ just c
             → Heads (Conf.pos (Mach.conf m₁)) c
  scan-above {m₁ = m₁} {f = f} {r} {u} ρ {y} cl =
    Above.above H f r u (Books.fresh (Climbing.books cl)) (f (At.val H r) y) (Conf.pos (Mach.conf m₁)) (Climbing.behind cl)
    where H = Conf.heap (Mach.conf m₁)

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
