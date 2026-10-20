{-# OPTIONS --guardedness #-}

-- THE FRAME: a write at one node's own cell, against everything the
-- relation holds of the rest of the tree.
module adequacy.Frame where

open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Relation.Unary.Any using (Any; here; there)
import Data.List.Relation.Unary.Any as Any
open import Data.List.Relation.Unary.All using (All; []; _∷_; map) renaming (lookup to lookupᴬ)
open import Data.List.Relation.Unary.All.Properties using (++⁻ˡ; ++⁻ʳ) renaming (++⁺ to all-++⁺)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; _∷_) renaming (head to pairs-hd)
open import Data.List.Relation.Unary.Linked using (_∷_)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴸ_)
open import Level using (lift)
open import Data.Maybe using (Maybe; just; nothing; is-just)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import adequacy.Sorted using (_≤ᵖ_; ≤ᵖ-child; ≤ᵖ-trans)
open import adequacy.Placed.Order using (Headed; headed-snoc)
open import adequacy.Placed.Rising using (tick-past)
open import Data.Nat using (zero; suc; _+_; s≤s; z≤n)
open import Data.Unit using (⊤; tt)
open import Data.Nat.Properties using (m<m+n)

open import denotation.MonotonicList.Events using (timelineAt; Events∞; Timeline; Pos; ix; last; _<ᵖ_; From; inside)
import Data.Maybe.Relation.Binary.Pointwise as MP
import Data.List.Relation.Binary.Pointwise as LP
open import denotation.MonotonicList.Events using () renaming (done to doneᶠ; quiet to quietᶠ; at to atᶠ; emit to emitᶠ; stall to stallᶠ; close to closeᶠ)
import denotation.Unfold as U
open import denotation.MonotonicList.Events using () renaming (sub to subᴾ)
open import operation.Machine using (module Machine)
open import adequacy.Strong using (module Strongly)
open import adequacy.Strong.Against using (module StrongAgainst)
open import adequacy.Strong.Held using (module StrongHeld)
open import adequacy.Torn using (module Tearing)
import Tree as T
open import operation.PureObservable using (Out; Pureᴾ)
open import operation.AbstractObservable using (base; module Heap; module Run) renaming (module Machine to Shared)
open import adequacy.Ghost using (module Ghosting)
open import adequacy.Ghost.Paths using (module GhostingPaths)
open import adequacy.Moves using (module Moving)
open import adequacy.Local using (module Locality)
open import adequacy.Every using (module Everywhere)
open import adequacy.Every.Gating using (module EverywhereGated)
open Events∞



module Framing (R : Set) where
  open Machine R using (Mach; Read)
  open Run (Pureᴾ R) using (Ref; Subject; module Kit; module FlatKit)
  open Shared Timeline (Out R) using (Conf; Heapᴹ; store; stored; look)
  open Heap using (_∋_; cell; slot) renaming (same to same⊑)
  open Strongly R using (Sub; scanˢ; here; module At; Path; in-scan; in-source; _⊕_; names; mapˢ; takeWhileˢ; flatMapˢ; connectˢ; deferˢ; Lane; lane; PathLanes; this-lane; next-lane; _⊕ᴸ_; in-map; in-take; in-outer; in-lanes; in-body; in-defer; Taking; taking; taken; cutNames; quietName; subjectNames; flatNames; laneNames; Name; pendings; subjects; joiners) renaming (ending to endingᵀ)
  open StrongAgainst R using (Queue; Kernels; Meaning; Each; seen; Books; seenL; seen-join)
  open StrongHeld R using (Strong; Heads)
  open Tearing R using (holds-at; Alike; Off; part-alike; partLanes-alike; lanes-path; module Seeing; look-store; get-put-same; fresh-path; names-path; apart-r; apart-l; ≢-flip)
  open Moving R using (pairs-r; pairs-split; plant; pendings-plant; subjects-plant; joiners-plant; head-map; head-scan)
  open Locality R using (module Heaps)
  open EverywhereGated.Holding R using (holds-alike)
  open Everywhere.Spending R using (spent-alike)
  open EverywhereGated.Gating R using (gated-alike)
  open Ghosting R using (Lifts; LiftsLane; lifts-here; lifts-map; lifts-scan; lifts-take; lifts-outer; lifts-lanes; lifts-source; lifts-body; lifts-shut; lifts-defer; lifts-this; lifts-next; OuterFirst; PoolBehind; LaneFirst)
  open GhostingPaths R using (each-lanes; module Calling; Calling; sends; opened; openedL)
  open Read

  -- A scan's part, its accumulator written: its source's part, the
  -- accumulator the value written, the source's names apart from it.
  scan-part : ∀ {h} (H : Heapᴹ h) {Δ A B} {f : B → A → B} {r} {u : Sub h Δ A} → AllPairs _≢_ (names (scanˢ f r u))
            → ∀ {c′} z → At.part H u ≡ just c′ → At.part (store H r (lift z)) (scanˢ f r u) ≡ just (U.scanᶜ f z c′)
  scan-part H {r = r} {u} (nr ∷ _) z pu
    rewrite get-put-same H r {y = stored (lift z) same⊑}
          | part-alike H (store H r (lift z)) u (λ j m → look-store H r j (lookupᴬ nr m)) | pu = refl

  -- A node's names, its scans' accumulators left out.
  mutual
    gates : ∀ {h Δ A} → Sub h Δ A → List (Name h)
    gates (mapˢ f s)                            = gates s
    gates (scanˢ f r s)                         = gates s
    gates (takeWhileˢ i p c k tk s)             = cutNames c ++ quietName k ++ gates s
    gates (flatMapˢ op f fl oc k r pl so ls)    = flatNames fl ++ cutNames oc ++ quietName k ++ (slot _ , r) ∷ gates so ++ gatesL ls
    gates (connectˢ S c b kb k fd rp e rt src bd) =
      subjectNames S ++ cutNames c ++ (cell _ , b) ∷ quietName kb ++ quietName k ++ gates src ++ gates bd
    gates (deferˢ k s)                          = quietName k ++ gates s
    gates u                                     = names u

    gatesL : ∀ {h Δ B} → List (Lane h Δ B) → List (Name h)
    gatesL []                = []
    gatesL (lane c k s ∷ ls) = cutNames c ++ quietName k ++ gates s ++ gatesL ls

  -- A WRITE AT A SCAN'S ACCUMULATOR, FRAMED: nothing the relation holds
  -- reads an accumulator but the parts above it.  A path the write leaves
  -- seen it saw before, to a node that reads alike or sits above the
  -- scan.
  postulate
    -- Whether a node has a part reads no accumulator.
    defined-alike : ∀ {h} (H H′ : Heapᴹ h) {Δ A} (u : Sub h Δ A) → Alike H H′ (gates u) → is-just (At.part H′ u) ≡ is-just (At.part H u)

    -- Whether a path is seen reads no accumulator.
    seen-gates : ∀ {h} (H H′ : Heapᴹ h) {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (ψ : Path t u) → Alike H H′ (gates t) → seen H′ ψ ≡ seen H ψ

    -- A scan's accumulator is no other node's name but an accumulator.
    gates-apart : ∀ {h} {T : Sub h [] R} {Δ A B} {f : B → A → B} {r} {u : Sub h Δ A} → Path T (scanˢ f r u) → AllPairs _≢_ (names T)
                → ∀ {Δ′ A′} {x : Sub h Δ′ A′} → Path T x → All (_≢_ {A = Name h} (cell _ , r)) (gates x)

    -- A node either sits above the scan or names nothing of its accumulator.
    scan-apart : ∀ {h} {T : Sub h [] R} {Δ A B} {f : B → A → B} {r} {u : Sub h Δ A} → Path T (scanˢ f r u) → AllPairs _≢_ (names T)
               → ∀ {Δ′ A′} {x : Sub h Δ′ A′} → Path T x → All (_≢_ {A = Name h} (cell _ , r)) (names x) ⊎ Path x (scanˢ f r u)

  -- Apart from a write's name, a heap reads as before the write.
  store-alike : ∀ {h} (H : Heapᴹ h) {k} (i : h ∋ k) {x} {ns : List (Name h)} → All (_≢_ {A = Name h} (k , i)) ns → Alike H (store H i x) ns
  store-alike H i ap j m = look-store H i j (lookupᴬ ap m)

  scan-defined : ∀ {h} (H : Heapᴹ h) {T : Sub h [] R} {Δ A B} {f : B → A → B} {r} {u : Sub h Δ A} → Path T (scanˢ f r u) → AllPairs _≢_ (names T)
               → ∀ z {Δ′ A′} {x : Sub h Δ′ A′} → Path T x → is-just (At.part (store H r (lift z)) x) ≡ is-just (At.part H x)
  scan-defined H {r = r} ρ fs z {x = x} ψ = defined-alike H (store H r (lift z)) x (store-alike H r {lift z} (gates-apart ρ fs ψ))

  scan-sees : ∀ {h} (H : Heapᴹ h) {T : Sub h [] R} {Δ A B} {f : B → A → B} {r} {u : Sub h Δ A} → Path T (scanˢ f r u) → AllPairs _≢_ (names T)
            → ∀ z {Δ′ A′} {x : Sub h Δ′ A′} (ψ : Path T x) → seen (store H r (lift z)) ψ ≡ true
            → seen H ψ ≡ true × (Alike H (store H r (lift z)) (names x) ⊎ Path x (scanˢ f r u))
  scan-sees H {r = r} ρ fs z ψ e =
    trans (sym (seen-gates H (store H r (lift z)) ψ (store-alike H r {lift z} (gates-apart ρ fs here)))) e
    , side (scan-apart ρ fs ψ)
    where
      side : ∀ {Δ′ A′} {x : Sub _ Δ′ A′} → All (_≢_ {A = Name _} (cell _ , r)) (names x) ⊎ Path x (scanˢ _ r _)
           → Alike H (store H r (lift z)) (names x) ⊎ Path x (scanˢ _ r _)
      side (inj₁ ap) = inj₁ (store-alike H r {lift z} ap)
      side (inj₂ π)  = inj₂ π


  heads-map : ∀ {Γ A B q} (g : A → B) {c : U.Node Γ A} → Heads q c → Heads q (U.mapᶜ g c)
  heads-map g {c} hd e = hd (trans (sym (head-map g (U.step c))) e)

  heads-scan : ∀ {Γ A B q} (g : B → A → B) z {c : U.Node Γ A} → Heads q c → Heads q (U.scanᶜ g z c)
  heads-scan g z {c} hd e = hd (trans (sym (head-scan g z (U.step c))) e)

  -- A scan's head is its source's, whatever its accumulator.
  heads-rescan : ∀ {Γ A B q} (g : B → A → B) {z₁ z₂} {c : U.Node Γ A} → Heads q (U.scanᶜ g z₁ c) → Heads q (U.scanᶜ g z₂ c)
  heads-rescan g {z₁} {z₂} {c} hd e = hd (trans (head-scan g z₁ (U.step c)) (trans (sym (head-scan g z₂ (U.step c))) e))

  -- A take's head is its source's, or under it.
  taking-head : ∀ {Γ A q} i (p : A → Bool) k a (c : U.Node Γ A) b → (∀ {k′} → just k ≡ just k′ → q ≤ᵖ k′)
              → ∀ {k′} → U.headˢ (U.taking i p k a c b) ≡ just k′ → q ≤ᵖ k′
  taking-head i     p k a c true  hd refl = hd refl
  taking-head true  p k a c false hd refl = ≤ᵖ-child k (hd refl)
  taking-head false p k a c false hd refl = ≤ᵖ-child k (hd refl)

  take-head : ∀ {Γ A q} i (p : A → Bool) (s : U.Step Γ A) → (∀ {k} → U.headˢ s ≡ just k → q ≤ᵖ k)
            → ∀ {k} → U.headˢ (U.takeWhileˢ i p s) ≡ just k → q ≤ᵖ k
  take-head i p (U.outˢ k a c) hd = taking-head i p k a c (p a) hd
  take-head i p (U.skipˢ k c)  hd = hd
  take-head i p (U.endˢ k)     hd = hd
  take-head i p U.hushˢ        hd ()

  heads-take : ∀ {Γ A q} i (p : A → Bool) {c : U.Node Γ A} → Heads q c → Heads q (U.takeWhileᶜ i p c)
  heads-take i p {c} hd = take-head i p (U.step c) hd

  HeadsS : ∀ {Γ A} → Pos → U.Step Γ A → Set
  HeadsS q s = ∀ {k} → U.headˢ s ≡ just k → q ≤ᵖ k

  if-head : ∀ {Γ A q} b (s₁ s₂ : U.Step Γ A) → HeadsS q s₁ → HeadsS q s₂ → HeadsS q (if b then s₁ else s₂)
  if-head true  s₁ s₂ h₁ h₂ = h₁
  if-head false s₁ s₂ h₁ h₂ = h₂

  child-skip : ∀ {Γ A q} k l (c : U.Node Γ A) → (∀ {k′} → just k ≡ just k′ → q ≤ᵖ k′) → HeadsS q (U.skipˢ (k ++ [ l ]) c)
  child-skip k l c hd refl = ≤ᵖ-child k (hd refl)

  body-head : ∀ {Γ A B q} r (s : U.Source Γ A) (sb : U.Step (A ∷ Γ) B) → HeadsS q sb → HeadsS q (U.bodyˢ r s sb)
  body-head r s (U.outˢ k a b) hd = hd
  body-head r s (U.skipˢ k b)  hd = hd
  body-head r s (U.endˢ c)     hd = hd
  body-head r s U.hushˢ        hd ()

  -- A live connect's head is its body's, or under its source's.
  source-head : ∀ {Γ A B q} r (b : U.Node (A ∷ Γ) B) sb (s : U.Node Γ A) (ss : U.Step Γ A) → HeadsS q sb → HeadsS q ss
              → HeadsS q (U.sourceˢ r b sb s ss)
  source-head r b sb s (U.outˢ k a s′) hb hs =
    if-head (U.beforeˢ (k ++ [ ix 0 ]) sb) (U.skipˢ (k ++ [ ix 0 ]) n) (U.bodyˢ r (U.live s) sb) (child-skip k (ix 0) n hs) (body-head r (U.live s) sb hb)
    where n = U.connectᶜ r (U.feed (here refl) k (just a) b) (U.live s′)
  source-head r b sb s (U.skipˢ k s′)  hb hs =
    if-head (U.beforeˢ (k ++ [ ix 0 ]) sb) (U.skipˢ (k ++ [ ix 0 ]) n) (U.bodyˢ r (U.live s) sb) (child-skip k (ix 0) n hs) (body-head r (U.live s) sb hb)
    where n = U.connectᶜ r (U.feed (here refl) k nothing b) (U.live s′)
  source-head r b sb s (U.endˢ c)      hb hs =
    if-head (U.beforeˢ (c ++ [ ix 0 ]) sb) (U.skipˢ (c ++ [ ix 0 ]) n) (U.bodyˢ r (U.live s) sb) (child-skip c (ix 0) n hs) (body-head r (U.live s) sb hb)
    where n = U.connectᶜ r (U.shut (here refl) c b) (U.ended c (U.restᶜ s))
  source-head r b sb s U.hushˢ         hb hs = body-head r (U.live s) sb hb

  heads-source : ∀ {Γ A B q} r {b : U.Node (A ∷ Γ) B} {s : U.Node Γ A} → Heads q s → Heads q b → Heads q (U.connectᶜ r b (U.live s))
  heads-source r {b} {s} hs hb = source-head r b (U.step b) s (U.step s) hb hs

  -- A timer frame past the tick it was subscribed at heads past a
  -- position that leads with that tick.
  timer-after : ∀ a q′ t e → (ix a ∷ q′) ≤ᵖ (ix (a + suc t) ∷ subᴾ e ∷ ix 0 ∷ [])
  timer-after a q′ t e = inj₂ (proj₁ (tick-past q′ (subᴾ e ∷ ix 0 ∷ []) (m<m+n a (s≤s z≤n))))

  -- A cold begun at a headed position heads no sooner than it: its
  -- first frame under it, its end under it, or a later tick.
  start-heads : ∀ {Γ A} q → Headed q → (m : From A 0) → Heads q (U.startᶜ {Γ} q m)
  start-heads q hq (atᶠ zero _ (emitᶠ x k)) refl = ≤ᵖ-child q (inj₁ refl)
  start-heads q hq (atᶠ zero _ (stallᶠ k))  refl = ≤ᵖ-child q (inj₁ refl)
  start-heads q hq (atᶠ zero _ (closeᶠ k))  refl = ≤ᵖ-child q (inj₁ refl)
  start-heads q hq doneᶠ                    refl = ≤ᵖ-child q (inj₁ refl)
  start-heads q hq quietᶠ                   ()
  start-heads (ix a ∷ q′) hq (atᶠ (suc t) _ (emitᶠ x k)) refl = timer-after a q′ t _
  start-heads (ix a ∷ q′) hq (atᶠ (suc t) _ (stallᶠ k))  refl = timer-after a q′ t _
  start-heads (ix a ∷ q′) hq (atᶠ (suc t) _ (closeᶠ k))  refl = timer-after a q′ t _
  start-heads []          () (atᶠ (suc t) _ b)
  start-heads (subᴾ _ ∷ _) () (atᶠ (suc t) _ b)
  start-heads (last ∷ _)  () (atᶠ (suc t) _ b)

  -- A flatMap begun: its outer's step, no lane, no pool.
  outer-heads : ∀ {Δ A B q} op (g : A → Pos → U.Node Δ B) (o : U.Node Δ A) (so : U.Step Δ A) → HeadsS q so
              → HeadsS q (U.outerˢ op g o so [] [] U.idleᶜ)
  outer-heads op g o (U.outˢ k a o′) hs refl = ≤ᵖ-child k (hs refl)
  outer-heads op g o (U.skipˢ k o′)  hs refl = hs refl
  outer-heads op g o (U.endˢ c)      hs refl = hs refl
  outer-heads op g o U.hushˢ         hs ()

  -- A subscription at a headed position heads no sooner than it.
  sub-heads : ∀ {Γ A} (s : T.Obs Timeline Γ A) q → Headed q → Heads q (U.subscribe s q)
  sub-heads (T.cold c)          q hq      = start-heads q hq (timelineAt c q)
  sub-heads T.empty             q hq refl = ≤ᵖ-child q (inj₁ refl)
  sub-heads (T.of [])           q hq refl = ≤ᵖ-child q (inj₁ refl)
  sub-heads (T.of (x ∷ xs))     q hq refl = ≤ᵖ-child q (inj₁ refl)
  sub-heads (T.map f s)         q hq      = heads-map f {U.subscribe s q} (sub-heads s q hq)
  sub-heads (T.scan f z s)      q hq      = heads-scan f z {U.subscribe s q} (sub-heads s q hq)
  sub-heads (T.takeWhile i p s) q hq      = heads-take i p {U.subscribe s q} (sub-heads s q hq)
  sub-heads (T.flatMap op f s)  q hq      = outer-heads op (λ a j → U.subscribe (f a) j) (U.subscribe s q) (U.step (U.subscribe s q)) (sub-heads s q hq)
  sub-heads (T.connect s b)     q hq      =
    heads-source (q ++ [ ix 1 ]) {U.subscribe b (q ++ [ ix 0 ])} {U.subscribe s (q ++ [ ix 1 ])}
      (λ e → ≤ᵖ-trans (≤ᵖ-child q (inj₁ refl)) (sub-heads s (q ++ [ ix 1 ]) (headed-snoc q hq) e))
      (λ e → ≤ᵖ-trans (≤ᵖ-child q (inj₁ refl)) (sub-heads b (q ++ [ ix 0 ]) (headed-snoc q hq) e))
  sub-heads (T.connected i)     q hq      ()
  sub-heads (T.defer l)         q hq refl = ≤ᵖ-child q (inj₁ refl)

  -- Where a shut at `i` tells a joiner its end, the joiners untold:
  -- each one's subscription.
  untoldᴶ : ∀ {A B : Set} → Pos → Maybe Pos → Maybe (A ≡ B) → List Pos
  untoldᴶ p nothing (just refl) = [ p ]
  untoldᴶ p e       m           = []

  mutual
    untold : ∀ {Γ A B} → A ∈ᴸ Γ → U.Node Γ B → List Pos
    untold i (U.mapᶜ f n)                 = untold i n
    untold i (U.scanᶜ f z n)              = untold i n
    untold i (U.takeWhileᶜ b p n)         = untold i n
    untold i (U.flatMapᶜ op g o ls qs pl) = untoldᴹ i o ++ untoldᴸ i ls ++ untold i pl
    untold i (U.joinᶜ j p xs e)           = untoldᴶ p e (U.same? i j)
    untold i (U.connectᶜ r b s)           = untold (there i) b ++ untoldˢ i s
    untold i (U.endingᶜ p n)              = untold i n
    untold i (U.restᶜ n)                  = untold i n
    untold i (U.unionᶜ x y)               = untold i x ++ untold i y
    untold i (U.burstingᶜ r t)            = untold i t
    untold i (U.underᶜ s b)               = untoldˢ i s ++ untold (there i) b
    untold i n                            = []

    untoldᴹ : ∀ {Γ A B} → A ∈ᴸ Γ → Maybe (U.Node Γ B) → List Pos
    untoldᴹ i nothing  = []
    untoldᴹ i (just n) = untold i n

    untoldᴸ : ∀ {Γ A B} → A ∈ᴸ Γ → List (U.Node Γ B) → List Pos
    untoldᴸ i []       = []
    untoldᴸ i (n ∷ ns) = untold i n ++ untoldᴸ i ns

    untoldˢ : ∀ {Γ A B} → A ∈ᴸ Γ → U.Source Γ B → List Pos
    untoldˢ i (U.live s)    = untold i s
    untoldˢ i (U.ended e t) = untold i t

  -- Two connects' indices, distinct.
  data Apart : ∀ {Γ : List Set} {A C : Set} → A ∈ᴸ Γ → C ∈ᴸ Γ → Set₁ where
    here-there  : ∀ {Γ A C} {i : C ∈ᴸ Γ} → Apart {A ∷ Γ} (here refl) (there i)
    there-here  : ∀ {Γ A C} {k : A ∈ᴸ Γ} → Apart {C ∷ Γ} (there k) (here refl)
    there-there : ∀ {Γ X A C} {k : A ∈ᴸ Γ} {i : C ∈ᴸ Γ} → Apart k i → Apart {X ∷ Γ} (there k) (there i)

  untoldᴶ-none : ∀ {A B : Set} p e → untoldᴶ {A} {B} p e nothing ≡ []
  untoldᴶ-none p nothing  = refl
  untoldᴶ-none p (just _) = refl

  untold-told : ∀ {Γ A C B} {k : A ∈ᴸ Γ} {i : C ∈ᴸ Γ} → Apart k i → ∀ c (j : B ∈ᴸ Γ) p e
              → untoldᴶ p (U.told k c j p e (U.same? k j)) (U.same? i j) ≡ untoldᴶ p e (U.same? i j)
  untold-told here-there      c (here refl) p e        = trans (untoldᴶ-none p _) (sym (untoldᴶ-none p e))
  untold-told here-there      c (there j)   p nothing  = refl
  untold-told here-there      c (there j)   p (just _) = refl
  untold-told there-here      c (here refl) p nothing  = refl
  untold-told there-here      c (here refl) p (just _) = refl
  untold-told there-here      c (there j)   p e        = trans (untoldᴶ-none p _) (sym (untoldᴶ-none p e))
  untold-told (there-there a) c (here refl) p e        = trans (untoldᴶ-none p _) (sym (untoldᴶ-none p e))
  untold-told (there-there a) c (there j)   p e        = untold-told a c j p e

  -- A shut tells only the joiners of the connect it ends.
  mutual
    untold-apart : ∀ {Γ A C B} {k : A ∈ᴸ Γ} {i : C ∈ᴸ Γ} → Apart k i → ∀ c (n : U.Node Γ B) → untold i (U.shut k c n) ≡ untold i n
    untold-apart a c (U.mapᶜ f n)                 = untold-apart a c n
    untold-apart a c (U.scanᶜ f z n)              = untold-apart a c n
    untold-apart a c (U.takeWhileᶜ b p n)         = untold-apart a c n
    untold-apart a c (U.flatMapᶜ op g o ls qs pl) =
      cong₂ _++_ (untold-apartᴹ a c o) (cong₂ _++_ (untold-apartᴸ a c ls) (untold-apart a c pl))
    untold-apart a c (U.joinᶜ j p xs e)           = untold-told a c j p e
    untold-apart a c (U.connectᶜ r b s)           = cong₂ _++_ (untold-apart (there-there a) c b) (untold-apartˢ a c s)
    untold-apart a c (U.endingᶜ p n)              = untold-apart a c n
    untold-apart a c (U.restᶜ n)                  = untold-apart a c n
    untold-apart a c (U.unionᶜ x y)               = cong₂ _++_ (untold-apart a c x) (untold-apart a c y)
    untold-apart a c (U.burstingᶜ r t)            = untold-apart a c t
    untold-apart a c (U.underᶜ s b)               = cong₂ _++_ (untold-apartˢ a c s) (untold-apart (there-there a) c b)
    untold-apart a c (U.framesᶜ _ _ _)            = refl
    untold-apart a c (U.burstᶜ _ _ _ _)           = refl
    untold-apart a c (U.ofᶜ _ _ _)                = refl
    untold-apart a c (U.deferᶜ _ _ _)             = refl
    untold-apart a c U.idleᶜ                      = refl

    untold-apartᴹ : ∀ {Γ A C B} {k : A ∈ᴸ Γ} {i : C ∈ᴸ Γ} → Apart k i → ∀ c (m : Maybe (U.Node Γ B)) → untoldᴹ i (U.shutᴹ k c m) ≡ untoldᴹ i m
    untold-apartᴹ a c nothing  = refl
    untold-apartᴹ a c (just n) = untold-apart a c n

    untold-apartᴸ : ∀ {Γ A C B} {k : A ∈ᴸ Γ} {i : C ∈ᴸ Γ} → Apart k i → ∀ c (ns : List (U.Node Γ B)) → untoldᴸ i (U.shutᴸ k c ns) ≡ untoldᴸ i ns
    untold-apartᴸ a c []       = refl
    untold-apartᴸ a c (n ∷ ns) = cong₂ _++_ (untold-apart a c n) (untold-apartᴸ a c ns)

    untold-apartˢ : ∀ {Γ A C B} {k : A ∈ᴸ Γ} {i : C ∈ᴸ Γ} → Apart k i → ∀ c (s : U.Source Γ B) → untoldˢ i (U.shutˢ k c s) ≡ untoldˢ i s
    untold-apartˢ a c (U.live s)    = untold-apart a c s
    untold-apartˢ a c (U.ended e t) = untold-apart a c t

  untold-shut : ∀ {Γ A B C} (i : C ∈ᴸ Γ) c (b : U.Node (A ∷ Γ) B) → untold (there i) (U.shut (here refl) c b) ≡ untold (there i) b
  untold-shut i c b = untold-apart here-there c b

  -- Every end a shut at `c` tells comes no sooner than `q`.
  Tells : Pos → Pos → List Pos → Set
  Tells q c = All (λ p → q ≤ᵖ (if p <ᵖ c then c ++ [ subᴾ p ] else p ++ [ last ]))

  -- Two steps alike but for their continuations.
  data Twin {Γ : List Set} {A : Set} : U.Step Γ A → U.Step Γ A → Set₁ where
    outᵗ  : ∀ {k a c c′} → Twin (U.outˢ k a c) (U.outˢ k a c′)
    skipᵗ : ∀ {k c c′}   → Twin (U.skipˢ k c) (U.skipˢ k c′)
    endᵗ  : ∀ {k}        → Twin (U.endˢ k) (U.endˢ k)
    hushᵗ :                Twin U.hushˢ U.hushˢ

  twin-refl : ∀ {Γ A} (s : U.Step Γ A) → Twin s s
  twin-refl (U.outˢ k a c) = outᵗ
  twin-refl (U.skipˢ k c)  = skipᵗ
  twin-refl (U.endˢ k)     = endᵗ
  twin-refl U.hushˢ        = hushᵗ

  twin-head : ∀ {Γ A} {s s′ : U.Step Γ A} → Twin s s′ → U.headˢ s ≡ U.headˢ s′
  twin-head outᵗ  = refl
  twin-head skipᵗ = refl
  twin-head endᵗ  = refl
  twin-head hushᵗ = refl

  -- A shut steps as its node did, or neither heads before `q`: an end it
  -- tells came first, so what that end beat came no sooner either.
  Down : ∀ {Γ A} → Pos → U.Step Γ A → U.Step Γ A → Set₁
  Down q s s′ = Twin s s′ ⊎ (HeadsS q s × HeadsS q s′)

  -- A rest's step: a skip, or nothing.
  data Hushed {Γ : List Set} {A : Set} : U.Step Γ A → Set₁ where
    skipʰ : ∀ {k c} → Hushed (U.skipˢ k c)
    hushʰ : Hushed U.hushˢ

  if-hushed : ∀ {Γ A} b {s₁ s₂ : U.Step Γ A} → Hushed s₁ → Hushed s₂ → Hushed (if b then s₁ else s₂)
  if-hushed true  h₁ h₂ = h₁
  if-hushed false h₁ h₂ = h₂

  union-hushed : ∀ {Γ B} (x : U.Node Γ B) sx y sy → Hushed sy → Hushed (U.unionˢ x sx y sy)
  union-hushed x (U.skipˢ k x′) y (U.skipˢ k′ y′) h = if-hushed (k <ᵖ k′) skipʰ skipʰ
  union-hushed x (U.skipˢ k x′) y (U.outˢ _ _ _)  h = skipʰ
  union-hushed x (U.skipˢ k x′) y (U.endˢ _)      h = skipʰ
  union-hushed x (U.skipˢ k x′) y U.hushˢ         h = skipʰ
  union-hushed x (U.outˢ _ _ _) y sy              h = h
  union-hushed x (U.endˢ _)     y sy              h = h
  union-hushed x U.hushˢ        y sy              h = h

  under-hushed : ∀ {Γ A B C} (s : U.Source Γ A) (sb : U.Step (A ∷ Γ) C) → Hushed {Γ} {B} (U.underˢ s sb)
  under-hushed s (U.skipˢ k b)  = skipʰ
  under-hushed s (U.outˢ _ _ _) = hushʰ
  under-hushed s (U.endˢ _)     = hushʰ
  under-hushed s U.hushˢ        = hushʰ

  bursts-hushed : ∀ {Γ A B} r (t : U.Node Γ A) (st : U.Step Γ A) → Hushed (U.restˢ {B = B} t) → Hushed {Γ} {B} (U.burstsˢ r t st)
  bursts-hushed r t (U.outˢ k _ _) h = if-hushed (inside r k) skipʰ h
  bursts-hushed r t (U.skipˢ k _)  h = if-hushed (inside r k) skipʰ h
  bursts-hushed r t (U.endˢ _)     h = h
  bursts-hushed r t U.hushˢ        h = h

  mutual
    rest-hushed : ∀ {Γ A B} (n : U.Node Γ A) → Hushed (U.restˢ {B = B} n)
    rest-hushed (U.framesᶜ τ e m)           = hushʰ
    rest-hushed (U.burstᶜ τ r k b)          = hushʰ
    rest-hushed (U.ofᶜ p k xs)              = hushʰ
    rest-hushed (U.mapᶜ f c)                = rest-hushed c
    rest-hushed (U.scanᶜ f z c)             = rest-hushed c
    rest-hushed (U.takeWhileᶜ i p c)        = rest-hushed c
    rest-hushed (U.flatMapᶜ op g o ls qs p) =
      union-hushed (U.outerᶜ o) (U.restᴹ o) (U.unionᶜ (U.restsᶜ ls) (U.restᶜ p)) (U.unionˢ (U.restsᶜ ls) (U.restsˢ ls) (U.restᶜ p) (U.restˢ p))
        (union-hushed (U.restsᶜ ls) (U.restsˢ ls) (U.restᶜ p) (U.restˢ p) (rest-hushed p))
    rest-hushed (U.joinᶜ i p xs e)          = hushʰ
    rest-hushed (U.connectᶜ {B = C} r b (U.live s)) =
      union-hushed (U.burstingᶜ r s) (U.burstsˢ r s (U.step s)) (U.underᶜ (U.live s) b) (U.underˢ (U.live s) (U.restˢ {B = C} b))
        (under-hushed (U.live s) (U.restˢ {B = C} b))
    rest-hushed (U.connectᶜ {B = C} r b (U.ended c t)) =
      union-hushed (U.burstingᶜ r t) (U.burstsˢ r t (U.step t)) (U.underᶜ (U.ended c t) b) (U.underˢ (U.ended c t) (U.restˢ {B = C} b))
        (under-hushed (U.ended c t) (U.restˢ {B = C} b))
    rest-hushed (U.deferᶜ l p ns)           = hushʰ
    rest-hushed (U.endingᶜ p n)             = rest-hushed n
    rest-hushed (U.restᶜ n)                 = rest-hushed n
    rest-hushed U.idleᶜ                     = hushʰ
    rest-hushed (U.unionᶜ x y)              = union-hushed (U.restᶜ x) (U.restˢ x) (U.restᶜ y) (U.restˢ y) (rest-hushed y)
    rest-hushed (U.burstingᶜ r t)           = bursts-hushed r t (U.step t) (rest-hushed t)
    rest-hushed (U.underᶜ {C = C} s b)      = under-hushed s (U.restˢ {B = C} b)

  rests-hushed : ∀ {Γ A B} (ls : List (U.Node Γ A)) → Hushed (U.restsˢ {B = B} ls)
  rests-hushed []       = hushʰ
  rests-hushed (l ∷ ls) = union-hushed (U.restᶜ l) (U.restˢ l) (U.restsᶜ ls) (U.restsˢ ls) (rests-hushed ls)

  map-down : ∀ {Γ A B q} (f : A → B) (s s′ : U.Step Γ A) → Down q s s′ → Down q (U.mapˢ f s) (U.mapˢ f s′)
  map-down f _ _ (inj₁ outᵗ)  = inj₁ outᵗ
  map-down f _ _ (inj₁ skipᵗ) = inj₁ skipᵗ
  map-down f _ _ (inj₁ endᵗ)  = inj₁ endᵗ
  map-down f _ _ (inj₁ hushᵗ) = inj₁ hushᵗ
  map-down f s s′ (inj₂ (h , h′)) = inj₂ ((λ e → h (trans (sym (head-map f s)) e)) , (λ e → h′ (trans (sym (head-map f s′)) e)))

  scan-down : ∀ {Γ A B q} (f : B → A → B) z (s s′ : U.Step Γ A) → Down q s s′ → Down q (U.scanˢ f z s) (U.scanˢ f z s′)
  scan-down f z _ _ (inj₁ outᵗ)  = inj₁ outᵗ
  scan-down f z _ _ (inj₁ skipᵗ) = inj₁ skipᵗ
  scan-down f z _ _ (inj₁ endᵗ)  = inj₁ endᵗ
  scan-down f z _ _ (inj₁ hushᵗ) = inj₁ hushᵗ
  scan-down f z s s′ (inj₂ (h , h′)) = inj₂ ((λ e → h (trans (sym (head-scan f z s)) e)) , (λ e → h′ (trans (sym (head-scan f z s′)) e)))

  taking-twin : ∀ {Γ A} i (p : A → Bool) k a (c c′ : U.Node Γ A) b → Twin (U.taking i p k a c b) (U.taking i p k a c′ b)
  taking-twin i     p k a c c′ true  = outᵗ
  taking-twin true  p k a c c′ false = outᵗ
  taking-twin false p k a c c′ false = endᵗ

  take-down : ∀ {Γ A q} i (p : A → Bool) (s s′ : U.Step Γ A) → Down q s s′ → Down q (U.takeWhileˢ i p s) (U.takeWhileˢ i p s′)
  take-down i p _ _ (inj₁ (outᵗ {k} {a} {c} {c′})) = inj₁ (taking-twin i p k a c c′ (p a))
  take-down i p _ _ (inj₁ skipᵗ) = inj₁ skipᵗ
  take-down i p _ _ (inj₁ endᵗ)  = inj₁ endᵗ
  take-down i p _ _ (inj₁ hushᵗ) = inj₁ hushᵗ
  take-down i p s s′ (inj₂ (h , h′)) = inj₂ (take-head i p s h , take-head i p s′ h′)

  under-heads : ∀ {Γ A B C q} (s : U.Source Γ A) (sb : U.Step (A ∷ Γ) C) → HeadsS q sb → HeadsS {Γ} {B} q (U.underˢ s sb)
  under-heads s (U.skipˢ k b)  h = h
  under-heads s (U.outˢ _ _ _) h ()
  under-heads s (U.endˢ _)     h ()
  under-heads s U.hushˢ        h ()

  under-down : ∀ {Γ A B C q} (s s′ : U.Source Γ A) (sb sb′ : U.Step (A ∷ Γ) C) → Down q sb sb′ → Down {Γ} {B} q (U.underˢ s sb) (U.underˢ s′ sb′)
  under-down s s′ _ _ (inj₁ outᵗ)  = inj₁ hushᵗ
  under-down s s′ _ _ (inj₁ skipᵗ) = inj₁ skipᵗ
  under-down s s′ _ _ (inj₁ endᵗ)  = inj₁ hushᵗ
  under-down s s′ _ _ (inj₁ hushᵗ) = inj₁ hushᵗ
  under-down s s′ sb sb′ (inj₂ (h , h′)) = inj₂ (under-heads s sb h , under-heads s′ sb′ h′)

  told-end : ∀ {Γ A q c p} → Tells q c [ p ] → Down {Γ} {A} q U.hushˢ (U.endˢ (if p <ᵖ c then c ++ [ subᴾ p ] else p ++ [ last ]))
  told-end (h ∷ []) = inj₂ ((λ ()) , λ { refl → h })

  DownN : ∀ {Γ A} → Pos → U.Node Γ A → U.Node Γ A → Set₁
  DownN q n n′ = Down q (U.step n) (U.step n′)

  -- THE STEP FUNCTIONS KEEP `Down`: each picks among its parts' steps by
  -- position, so a part shut to a told end leads only where that end
  -- comes first, and what it displaced came no sooner.

  -- A union's right side must be a rest's step: a non-skip there is
  -- dropped whole, so an end before `q` would vanish under a new left skip.
  postulate
    union-down : ∀ {Γ B q} (x x′ y y′ : U.Node Γ B) sx sx′ sy sy′ → Hushed sy → Hushed sy′ → Down q sx sx′ → Down q sy sy′
               → Down q (U.unionˢ x sx y sy) (U.unionˢ x′ sx′ y′ sy′)

  -- SUSPECT: a step that leaves `r` falls back to the rest, whose own
  -- head need not be past the step's; a shut moving the step inside `r`
  -- pins a skip the rest did not lead with.
  postulate
    bursts-down : ∀ {Γ A B q} r (t t′ : U.Node Γ A) (st st′ : U.Step Γ A) → Down q st st′ → Down q (U.restˢ {B = B} t) (U.restˢ {B = B} t′)
                → Down {Γ} {B} q (U.burstsˢ r t st) (U.burstsˢ r t′ st′)

  postulate
    source-down : ∀ {Γ A B q} r (b b′ : U.Node (A ∷ Γ) B) (s s′ : U.Node Γ A) sb sb′ ss ss′ → Down q sb sb′ → Down q ss ss′
                → Down q (U.sourceˢ r b sb s ss) (U.sourceˢ r b′ sb′ s′ ss′)

  postulate
    ended-down : ∀ {Γ A B q} r c (b b′ : U.Node (A ∷ Γ) B) (t t′ : U.Node Γ A) sb sb′ st st′ → Down q sb sb′ → Down q st st′
               → Down q (U.endedˢ r b sb c t st) (U.endedˢ r b′ sb′ c t′ st′)

  -- The lists keep their lengths and the outer its presence: the
  -- outer's and lanes' ends with nothing left are read off them.
  postulate
    flat-down : ∀ {Δ A B q} op (g : A → Pos → U.Node Δ B) (o o′ : Maybe (U.Node Δ A)) (ls ls′ : List (U.Node Δ B)) qs (pl pl′ : U.Node Δ B)
              → MP.Pointwise (DownN q) o o′ → LP.Pointwise (DownN q) ls ls′ → DownN q pl pl′
              → DownN q (U.flatMapᶜ op g o ls qs pl) (U.flatMapᶜ op g o′ ls′ qs pl′)

  mutual
    shut-down : ∀ {Γ A B q} (i : A ∈ᴸ Γ) c (b : U.Node Γ B) → Tells q c (untold i b) → DownN q b (U.shut i c b)
    shut-down i c (U.framesᶜ τ e m)            tl = inj₁ (twin-refl _)
    shut-down i c (U.burstᶜ τ r k b)           tl = inj₁ (twin-refl _)
    shut-down i c (U.ofᶜ p k xs)               tl = inj₁ (twin-refl _)
    shut-down i c (U.mapᶜ f n)                 tl = map-down f (U.step n) (U.step (U.shut i c n)) (shut-down i c n tl)
    shut-down i c (U.scanᶜ f z n)              tl = scan-down f z (U.step n) (U.step (U.shut i c n)) (shut-down i c n tl)
    shut-down i c (U.takeWhileᶜ t p n)         tl = take-down t p (U.step n) (U.step (U.shut i c n)) (shut-down i c n tl)
    shut-down i c (U.flatMapᶜ op g o ls qs pl) tl =
      flat-down op g o (U.shutᴹ i c o) ls (U.shutᴸ i c ls) qs pl (U.shut i c pl)
        (shut-downᴹ i c o (++⁻ˡ (untoldᴹ i o) tl))
        (shut-downᴸ i c ls (++⁻ˡ (untoldᴸ i ls) (++⁻ʳ (untoldᴹ i o) tl)))
        (shut-down i c pl (++⁻ʳ (untoldᴸ i ls) (++⁻ʳ (untoldᴹ i o) tl)))
    shut-down i c (U.joinᶜ j p ((_ , just a) ∷ xs) e)  tl = inj₁ outᵗ
    shut-down i c (U.joinᶜ j p ((_ , nothing) ∷ xs) e) tl = inj₁ skipᵗ
    shut-down i c (U.joinᶜ j p [] (just e))            tl = inj₁ endᵗ
    shut-down i c (U.joinᶜ j p [] nothing)             tl with U.same? i j
    ... | nothing   = inj₁ hushᵗ
    ... | just refl = told-end tl
    shut-down i c (U.connectᶜ r b (U.live s))  tl =
      source-down r b (U.shut (there i) c b) s (U.shut i c s) (U.step b) (U.step (U.shut (there i) c b)) (U.step s) (U.step (U.shut i c s))
        (shut-down (there i) c b (++⁻ˡ (untold (there i) b) tl)) (shut-down i c s (++⁻ʳ (untold (there i) b) tl))
    shut-down i c (U.connectᶜ r b (U.ended e t)) tl =
      ended-down r e b (U.shut (there i) c b) t (U.shut i c t) (U.step b) (U.step (U.shut (there i) c b)) (U.step t) (U.step (U.shut i c t))
        (shut-down (there i) c b (++⁻ˡ (untold (there i) b) tl)) (shut-down i c t (++⁻ʳ (untold (there i) b) tl))
    shut-down i c (U.deferᶜ l p ns)            tl = inj₁ (twin-refl _)
    shut-down i c (U.endingᶜ p n)              tl = inj₁ endᵗ
    shut-down i c (U.restᶜ n)                  tl = rest-down i c n tl
    shut-down i c U.idleᶜ                      tl = inj₁ hushᵗ
    shut-down i c (U.unionᶜ x y)               tl =
      union-down x (U.shut i c x) y (U.shut i c y) (U.restˢ x) (U.restˢ (U.shut i c x)) (U.restˢ y) (U.restˢ (U.shut i c y))
        (rest-hushed y) (rest-hushed (U.shut i c y)) (rest-down i c x (++⁻ˡ (untold i x) tl)) (rest-down i c y (++⁻ʳ (untold i x) tl))
    shut-down i c (U.burstingᶜ r t)            tl = bursts-down r t (U.shut i c t) (U.step t) (U.step (U.shut i c t)) (shut-down i c t tl) (rest-down i c t tl)
    shut-down i c (U.underᶜ {C = C} s b)       tl =
      under-down s (U.shutˢ i c s) (U.restˢ {B = C} b) (U.restˢ {B = C} (U.shut (there i) c b)) (rest-down (there i) c b (++⁻ʳ (untoldˢ i s) tl))

    shut-downᴹ : ∀ {Γ A B q} (i : A ∈ᴸ Γ) c (o : Maybe (U.Node Γ B)) → Tells q c (untoldᴹ i o) → MP.Pointwise (DownN q) o (U.shutᴹ i c o)
    shut-downᴹ i c nothing  tl = MP.nothing
    shut-downᴹ i c (just n) tl = MP.just (shut-down i c n tl)

    shut-downᴸ : ∀ {Γ A B q} (i : A ∈ᴸ Γ) c (ls : List (U.Node Γ B)) → Tells q c (untoldᴸ i ls) → LP.Pointwise (DownN q) ls (U.shutᴸ i c ls)
    shut-downᴸ i c []       tl = LP.[]
    shut-downᴸ i c (n ∷ ns) tl = shut-down i c n (++⁻ˡ (untold i n) tl) LP.∷ shut-downᴸ i c ns (++⁻ʳ (untold i n) tl)

    rest-down : ∀ {Γ A B C q} (i : A ∈ᴸ Γ) c (n : U.Node Γ B) → Tells q c (untold i n) → Down q (U.restˢ {B = C} n) (U.restˢ {B = C} (U.shut i c n))
    rest-down i c (U.framesᶜ τ e m)            tl = inj₁ hushᵗ
    rest-down i c (U.burstᶜ τ r k b)           tl = inj₁ hushᵗ
    rest-down i c (U.ofᶜ p k xs)               tl = inj₁ hushᵗ
    rest-down i c (U.mapᶜ f n)                 tl = rest-down i c n tl
    rest-down i c (U.scanᶜ f z n)              tl = rest-down i c n tl
    rest-down i c (U.takeWhileᶜ t p n)         tl = rest-down i c n tl
    rest-down i c (U.flatMapᶜ op g o ls qs pl) tl =
      union-down (U.outerᶜ o) (U.outerᶜ o′) (U.unionᶜ (U.restsᶜ ls) (U.restᶜ pl)) (U.unionᶜ (U.restsᶜ ls′) (U.restᶜ pl′))
        (U.restᴹ o) (U.restᴹ o′) (U.unionˢ (U.restsᶜ ls) (U.restsˢ ls) (U.restᶜ pl) (U.restˢ pl)) (U.unionˢ (U.restsᶜ ls′) (U.restsˢ ls′) (U.restᶜ pl′) (U.restˢ pl′))
        (union-hushed (U.restsᶜ ls) (U.restsˢ ls) (U.restᶜ pl) (U.restˢ pl) (rest-hushed pl))
        (union-hushed (U.restsᶜ ls′) (U.restsˢ ls′) (U.restᶜ pl′) (U.restˢ pl′) (rest-hushed pl′))
        (rest-downᴹ i c o (++⁻ˡ (untoldᴹ i o) tl))
        (union-down (U.restsᶜ ls) (U.restsᶜ ls′) (U.restᶜ pl) (U.restᶜ pl′) (U.restsˢ ls) (U.restsˢ ls′) (U.restˢ pl) (U.restˢ pl′)
          (rest-hushed pl) (rest-hushed pl′)
          (rests-down i c ls (++⁻ˡ (untoldᴸ i ls) (++⁻ʳ (untoldᴹ i o) tl)))
          (rest-down i c pl (++⁻ʳ (untoldᴸ i ls) (++⁻ʳ (untoldᴹ i o) tl))))
      where o′ = U.shutᴹ i c o
            ls′ = U.shutᴸ i c ls
            pl′ = U.shut i c pl
    rest-down i c (U.joinᶜ j p xs e)           tl = inj₁ hushᵗ
    rest-down i c (U.connectᶜ {B = C} r b (U.live s)) tl =
      union-down (U.burstingᶜ r s) (U.burstingᶜ r s′) (U.underᶜ (U.live s) b) (U.underᶜ (U.live s′) b′)
        (U.burstsˢ r s (U.step s)) (U.burstsˢ r s′ (U.step s′)) (U.underˢ (U.live s) (U.restˢ {B = C} b)) (U.underˢ (U.live s′) (U.restˢ {B = C} b′))
        (under-hushed (U.live s) (U.restˢ {B = C} b)) (under-hushed (U.live s′) (U.restˢ {B = C} b′))
        (bursts-down r s s′ (U.step s) (U.step s′) (shut-down i c s tlₛ) (rest-down i c s tlₛ))
        (under-down (U.live s) (U.live s′) (U.restˢ {B = C} b) (U.restˢ {B = C} b′) (rest-down (there i) c b (++⁻ˡ (untold (there i) b) tl)))
      where s′ = U.shut i c s
            b′ = U.shut (there i) c b
            tlₛ = ++⁻ʳ (untold (there i) b) tl
    rest-down i c (U.connectᶜ {B = C} r b (U.ended e t)) tl =
      union-down (U.burstingᶜ r t) (U.burstingᶜ r t′) (U.underᶜ (U.ended e t) b) (U.underᶜ (U.ended e t′) b′)
        (U.burstsˢ r t (U.step t)) (U.burstsˢ r t′ (U.step t′)) (U.underˢ (U.ended e t) (U.restˢ {B = C} b)) (U.underˢ (U.ended e t′) (U.restˢ {B = C} b′))
        (under-hushed (U.ended e t) (U.restˢ {B = C} b)) (under-hushed (U.ended e t′) (U.restˢ {B = C} b′))
        (bursts-down r t t′ (U.step t) (U.step t′) (shut-down i c t tlₜ) (rest-down i c t tlₜ))
        (under-down (U.ended e t) (U.ended e t′) (U.restˢ {B = C} b) (U.restˢ {B = C} b′) (rest-down (there i) c b (++⁻ˡ (untold (there i) b) tl)))
      where t′ = U.shut i c t
            b′ = U.shut (there i) c b
            tlₜ = ++⁻ʳ (untold (there i) b) tl
    rest-down i c (U.deferᶜ l p ns)            tl = inj₁ hushᵗ
    rest-down i c (U.endingᶜ p n)              tl = rest-down i c n tl
    rest-down i c (U.restᶜ n)                  tl = rest-down i c n tl
    rest-down i c U.idleᶜ                      tl = inj₁ hushᵗ
    rest-down i c (U.unionᶜ x y)               tl =
      union-down (U.restᶜ x) (U.restᶜ (U.shut i c x)) (U.restᶜ y) (U.restᶜ (U.shut i c y))
        (U.restˢ x) (U.restˢ (U.shut i c x)) (U.restˢ y) (U.restˢ (U.shut i c y))
        (rest-hushed y) (rest-hushed (U.shut i c y)) (rest-down i c x (++⁻ˡ (untold i x) tl)) (rest-down i c y (++⁻ʳ (untold i x) tl))
    rest-down i c (U.burstingᶜ r t)            tl = bursts-down r t (U.shut i c t) (U.step t) (U.step (U.shut i c t)) (shut-down i c t tl) (rest-down i c t tl)
    rest-down i c (U.underᶜ {C = C} s b)       tl =
      under-down s (U.shutˢ i c s) (U.restˢ {B = C} b) (U.restˢ {B = C} (U.shut (there i) c b)) (rest-down (there i) c b (++⁻ʳ (untoldˢ i s) tl))

    rest-downᴹ : ∀ {Γ A B C q} (i : A ∈ᴸ Γ) c (o : Maybe (U.Node Γ B)) → Tells q c (untoldᴹ i o) → Down q (U.restᴹ {B = C} o) (U.restᴹ {B = C} (U.shutᴹ i c o))
    rest-downᴹ i c nothing  tl = inj₁ hushᵗ
    rest-downᴹ i c (just n) tl = rest-down i c n tl

    rests-down : ∀ {Γ A B C q} (i : A ∈ᴸ Γ) c (ls : List (U.Node Γ B)) → Tells q c (untoldᴸ i ls) → Down q (U.restsˢ {B = C} ls) (U.restsˢ {B = C} (U.shutᴸ i c ls))
    rests-down i c []       tl = inj₁ hushᵗ
    rests-down i c (l ∷ ls) tl =
      union-down (U.restᶜ l) (U.restᶜ (U.shut i c l)) (U.restsᶜ ls) (U.restsᶜ (U.shutᴸ i c ls))
        (U.restˢ l) (U.restˢ (U.shut i c l)) (U.restsˢ ls) (U.restsˢ (U.shutᴸ i c ls))
        (rests-hushed ls) (rests-hushed (U.shutᴸ i c ls)) (rest-down i c l (++⁻ˡ (untold i l) tl)) (rests-down i c ls (++⁻ʳ (untold i l) tl))

  -- A shut heads where the node did, or at an end it tells.
  shut-heads : ∀ {Γ A B q} (i : A ∈ᴸ Γ) c (b : U.Node Γ B) → Heads q b → Tells q c (untold i b) → Heads q (U.shut i c b)
  shut-heads i c b hb tl e with shut-down i c b tl
  ... | inj₁ tw       = hb (trans (twin-head tw) e)
  ... | inj₂ (_ , h′) = h′ e

  shut-heads-step : ∀ {Γ A B q} r c (t : U.Node Γ A) (S : U.Step (A ∷ Γ) B) → HeadsS q S → HeadsS q (U.shutˢᵗ r c t S)
  shut-heads-step r c t (U.outˢ _ _ _) hs = hs
  shut-heads-step r c t (U.skipˢ _ _)  hs = hs
  shut-heads-step r c t (U.endˢ _)     hs = hs
  shut-heads-step r c t U.hushˢ        hs = hs

  just-of : ∀ {ℓ} {X : Set ℓ} {m : Maybe X} → is-just m ≡ true → Σ X λ c → m ≡ just c
  just-of {m = just c} _ = c , refl

  merged-eq : ∀ {h} (G : Heapᴹ h) {Δ A B} op (g : A → Pos → U.Node Δ B) o L Q pl {b} → At.merged G op g o L Q pl ≡ just b → U.flatMapᶜ op g o L Q pl ≡ b
  merged-eq G op g (just _) L       Q       pl refl = refl
  merged-eq G op g nothing  (_ ∷ _) Q       pl refl = refl
  merged-eq G op g nothing  []      (_ ∷ _) pl refl = refl
  merged-eq G op g nothing  []      []      pl ()

  -- A FLATMAP'S HEAD: its pool's skip, its outer's step or its
  -- earliest lane's, each moved at most a child down.  So it heads no
  -- sooner than `q` whenever its pool, its outer and its lanes do.
  outerˢ-heads : ∀ {Δ A B q} op (g : A → Pos → U.Node Δ B) (o : U.Node Δ A) (so : U.Step Δ A) ls qs p → HeadsS q so
               → HeadsS q (U.outerˢ op g o so ls qs p)
  outerˢ-heads op g o (U.outˢ k a o′) ls      qs      p hs refl = ≤ᵖ-child k (hs refl)
  outerˢ-heads op g o (U.skipˢ k o′)  ls      qs      p hs refl = hs refl
  outerˢ-heads op g o (U.endˢ c)      []      []      p hs refl = hs refl
  outerˢ-heads op g o (U.endˢ c)      []      (_ ∷ _) p hs refl = hs refl
  outerˢ-heads op g o (U.endˢ c)      (_ ∷ _) qs      p hs refl = hs refl
  outerˢ-heads op g o U.hushˢ         ls      qs      p hs ()

  laneˢ-heads : ∀ {Δ A B q} op (g : A → Pos → U.Node Δ B) (o : Maybe (U.Node Δ A)) bs l (s : U.Step Δ B) as qs p → HeadsS q s
              → HeadsS q (U.laneˢ op g o bs l s as qs p)
  laneˢ-heads op g o bs l (U.outˢ k b c) as qs p hs refl = hs refl
  laneˢ-heads op g o bs l (U.skipˢ k c)  as qs p hs refl = hs refl
  laneˢ-heads op g nothing  []      l (U.endˢ c) []      (a ∷ qs) p hs refl = ≤ᵖ-child c (hs refl)
  laneˢ-heads op g nothing  []      l (U.endˢ c) []      []       p hs refl = hs refl
  laneˢ-heads op g nothing  []      l (U.endˢ c) (_ ∷ _) (a ∷ qs) p hs refl = ≤ᵖ-child c (hs refl)
  laneˢ-heads op g nothing  []      l (U.endˢ c) (_ ∷ _) []       p hs refl = hs refl
  laneˢ-heads op g nothing  (_ ∷ _) l (U.endˢ c) []      (a ∷ qs) p hs refl = ≤ᵖ-child c (hs refl)
  laneˢ-heads op g nothing  (_ ∷ _) l (U.endˢ c) []      []       p hs refl = hs refl
  laneˢ-heads op g nothing  (_ ∷ _) l (U.endˢ c) (_ ∷ _) (a ∷ qs) p hs refl = ≤ᵖ-child c (hs refl)
  laneˢ-heads op g nothing  (_ ∷ _) l (U.endˢ c) (_ ∷ _) []       p hs refl = hs refl
  laneˢ-heads op g (just o) []      l (U.endˢ c) []      (a ∷ qs) p hs refl = ≤ᵖ-child c (hs refl)
  laneˢ-heads op g (just o) []      l (U.endˢ c) []      []       p hs refl = hs refl
  laneˢ-heads op g (just o) []      l (U.endˢ c) (_ ∷ _) (a ∷ qs) p hs refl = ≤ᵖ-child c (hs refl)
  laneˢ-heads op g (just o) []      l (U.endˢ c) (_ ∷ _) []       p hs refl = hs refl
  laneˢ-heads op g (just o) (_ ∷ _) l (U.endˢ c) []      (a ∷ qs) p hs refl = ≤ᵖ-child c (hs refl)
  laneˢ-heads op g (just o) (_ ∷ _) l (U.endˢ c) []      []       p hs refl = hs refl
  laneˢ-heads op g (just o) (_ ∷ _) l (U.endˢ c) (_ ∷ _) (a ∷ qs) p hs refl = ≤ᵖ-child c (hs refl)
  laneˢ-heads op g (just o) (_ ∷ _) l (U.endˢ c) (_ ∷ _) []       p hs refl = hs refl
  laneˢ-heads op g o bs l U.hushˢ        as qs p hs ()

  OuterHeads : ∀ {Δ A} → Pos → U.Outer Δ A → Set
  OuterHeads q U.doneᵒ      = ⊤
  OuterHeads q (U.runᵒ o s) = HeadsS q s

  EarliestHeads : ∀ {Δ B} → Pos → U.Earliest Δ B → Set
  EarliestHeads q U.none                = ⊤
  EarliestHeads q (U.found k bs l s as) = HeadsS q s

  pick-heads : ∀ {Δ B q} (l : U.Node Δ B) (s : U.Step Δ B) ls m (E : U.Earliest Δ B) → HeadsS q s → EarliestHeads q E
             → EarliestHeads q (U.pick l s ls m E)
  pick-heads l s ls nothing  U.none                  hs he = tt
  pick-heads l s ls nothing  (U.found k bs c sc as)  hs he = he
  pick-heads l s ls (just k) U.none                  hs he = hs
  pick-heads l s ls (just k) (U.found k′ bs c sc as) hs he with k <ᵖ k′
  ... | true  = hs
  ... | false = he

  earliest-heads : ∀ {Δ B q} (ls : List (U.Node Δ B)) → All (Heads q) ls → EarliestHeads q (U.earliest ls)
  earliest-heads []       []        = tt
  earliest-heads (l ∷ ls) (hl ∷ hL) = pick-heads l (U.step l) ls (U.headˢ (U.step l)) (U.earliest ls) hl (earliest-heads ls hL)

  race-heads : ∀ {Δ A B q} op (g : A → Pos → U.Node Δ B) o (so : U.Step Δ A) mk k bs l (s : U.Step Δ B) as qs p → HeadsS q so → HeadsS q s
             → HeadsS q (U.raceˢ op g o so mk k bs l s as qs p)
  race-heads op g o so nothing   k bs l s as qs p ho hs = laneˢ-heads op g (just o) bs l s as qs p hs
  race-heads op g o so (just k′) k bs l s as qs p ho hs =
    if-head (k′ <ᵖ k) (U.outerˢ op g o so (bs ++ l ∷ as) qs p) (U.laneˢ op g (just o) bs l s as qs p)
      (outerˢ-heads op g o so (bs ++ l ∷ as) qs p ho) (laneˢ-heads op g (just o) bs l s as qs p hs)

  go-heads : ∀ {Δ A B q} op (g : A → Pos → U.Node Δ B) (o : U.Outer Δ A) ls qs p (E : U.Earliest Δ B) → OuterHeads q o → EarliestHeads q E
           → HeadsS q (U.goˢ op g o ls qs p E)
  go-heads op g U.doneᵒ       ls qs p U.none                ho he ()
  go-heads op g (U.runᵒ o so) ls qs p U.none                ho he = outerˢ-heads op g o so ls qs p ho
  go-heads op g U.doneᵒ       ls qs p (U.found k bs l s as) ho he = laneˢ-heads op g nothing bs l s as qs p he
  go-heads op g (U.runᵒ o so) ls qs p (U.found k bs l s as) ho he = race-heads op g o so (U.headˢ so) k bs l s as qs p ho he

  flatˢ-heads : ∀ {Δ A B q} op (g : A → Pos → U.Node Δ B) (o : U.Outer Δ A) ls qs p (sp : U.Step Δ B) (E : U.Earliest Δ B)
              → HeadsS q sp → OuterHeads q o → EarliestHeads q E → HeadsS q (U.flatˢ op g o ls qs p sp E)
  flatˢ-heads op g o ls qs p (U.skipˢ k p′) E hp ho he =
    if-head (U.aheadˢ k o E) (U.skipˢ k (U.flatMapᶜ op g (U.nodeᵒ o) ls qs p′)) (U.goˢ op g o ls qs p E) hp (go-heads op g o ls qs p E ho he)
  flatˢ-heads op g o ls qs p (U.outˢ k b p′) E hp ho he = go-heads op g o ls qs p E ho he
  flatˢ-heads op g o ls qs p (U.endˢ k)      E hp ho he = go-heads op g o ls qs p E ho he
  flatˢ-heads op g o ls qs p U.hushˢ         E hp ho he = go-heads op g o ls qs p E ho he

  outer-of : ∀ {Δ A q} (o : Maybe (U.Node Δ A)) → (∀ {c} → o ≡ just c → Heads q c) → OuterHeads q (U.outerOf o)
  outer-of nothing  ho = tt
  outer-of (just c) ho = ho refl

  -- DEAD ROUTE: the flatMap's old head in place of its pool's.  A pool
  --   skip at the outer's out position, the flatMap a child under it,
  --   is first once the outer is done.
  heads-flat : ∀ {Δ A B q} op (g : A → Pos → U.Node Δ B) (o : Maybe (U.Node Δ A)) (L : List (U.Node Δ B)) Q pl
             → Heads q pl → (∀ {c} → o ≡ just c → Heads q c) → All (Heads q) L → Heads q (U.flatMapᶜ op g o L Q pl)
  heads-flat op g o L Q pl hp ho hL = flatˢ-heads op g (U.outerOf o) L Q pl (U.step pl) (U.earliest L) hp (outer-of o ho) (earliest-heads L hL)
