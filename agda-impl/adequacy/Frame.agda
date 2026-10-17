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
open import Level using (lift; lower)
open import Data.Maybe using (Maybe; just; nothing; is-just)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Data.Sum using (_⊎_; [_,_]′)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_; not)
open import Data.List.Relation.Unary.Any.Properties using (++⁺ˡ; ++⁺ʳ)
open import adequacy.Sorted using (_≤ᵖ_; ≤ᵖ-child)

open import denotation.MonotonicList using (Events∞; Timeline; Pos; ix; last; _<ᵖ_)
import denotation.Unfold as U
open import denotation.MonotonicList using () renaming (sub to subᴾ)
open import operation.Machine using (module Machine)
open import adequacy.Strong using (module Strongly)
open import adequacy.Torn using (module Tearing)
import Tree as T
open import operation.PureObservable using (Out; Pureᴾ)
open import operation.AbstractObservable using (base; module Heap; module Run) renaming (module Machine to Shared)
open import adequacy.Ghost using (module Ghosting)
open import adequacy.Moves using (module Moving)
open import adequacy.Local using (module Locality)

open Events∞

module Framing (R : Set) where
  open Machine R using (Mach; Read)
  open Run (Pureᴾ R) using (Ref; Subject; module Kit; module FlatKit)
  open Shared Timeline (Out R) using (Conf; Heapᴹ; store; stored; look)
  open Heap using (_∋_) renaming (same to same⊑)
  open Strongly R using (Strong; Sub; scanˢ; here; module At; Queue; Kernels; Meaning; Owned; Path; in-scan; in-source; _⊕_; names; Each; Heads; seen; Books;
                         mapˢ; takeWhileˢ; flatMapˢ; connectˢ; Lane; lane; PathLanes; this-lane; next-lane; in-map; in-take; in-outer; in-lanes; in-body; in-defer; seen-join;
                         Taking; taking; taken; cutNames; quietName; subjectNames; flatNames; laneNames; Name; pendings; subjects; joiners) renaming (ending to endingᵀ)
  open Strongly.Against R using (CtlAs)
  open Tearing R using (Alike; Off; part-alike; partLanes-alike; lanes-path; module Seeing; look-store; get-put-same; fresh-path; names-path; apart-r; apart-l; ≢-flip)
  open Moving R using (pairs-r; pairs-split; plant; pendings-plant; subjects-plant; joiners-plant; head-map; head-scan)
  open Locality R using (module Heaps)
  open Ghosting R using (module Calling; Lifts; LiftsLane; lifts-here; lifts-map; lifts-scan; lifts-take; lifts-outer; lifts-lanes; lifts-source;
                         lifts-body; lifts-shut; lifts-defer; lifts-this; lifts-next; OuterFirst; PoolBehind; LaneFirst; Calling; sends; opened; openedL)
  open Read

  -- A scan's part, its accumulator written: its source's part, the
  -- accumulator the value written, the source's names apart from it.
  scan-part : ∀ {h} (H : Heapᴹ h) {Δ A B} {f : B → A → B} {r} {u : Sub h Δ A} → AllPairs _≢_ (names (scanˢ f r u))
            → ∀ {c′} z → At.part H u ≡ just c′ → At.part (store H r (lift z)) (scanˢ f r u) ≡ just (U.scanᶜ f z c′)
  scan-part H {r = r} {u} (nr ∷ _) z pu
    rewrite get-put-same H r {y = stored (lift z) same⊑}
          | part-alike H (store H r (lift z)) u (λ j m → look-store H r j (lookupᴬ nr m)) | pu = refl

  -- A WRITE AT A SCAN'S ACCUMULATOR, FRAMED: nothing the relation holds
  -- reads an accumulator but the parts above it.
  postulate
    scan-owned   : ∀ {h} (H : Heapᴹ h) {T : Sub h [] R} {Δ A B} {f : B → A → B} {r} {u : Sub h Δ A} → Path T (scanˢ f r u) → AllPairs _≢_ (names T)
                 → ∀ {p ctl bs} {ca : CtlAs T p ctl bs} z → Owned H T ca → Owned (store H r (lift z)) T ca

    -- A path the write leaves seen it saw before, to a node that reads
    -- alike or sits above the scan.
    scan-sees    : ∀ {h} (H : Heapᴹ h) {T : Sub h [] R} {Δ A B} {f : B → A → B} {r} {u : Sub h Δ A} → Path T (scanˢ f r u) → AllPairs _≢_ (names T)
                 → ∀ z {Δ′ A′} {x : Sub h Δ′ A′} (ψ : Path T x) → seen (store H r (lift z)) ψ ≡ true
                 → seen H ψ ≡ true × (Alike H (store H r (lift z)) (names x) ⊎ Path x (scanˢ f r u))

    -- Whether a node has a part never reads an accumulator.
    scan-defined : ∀ {h} (H : Heapᴹ h) {T : Sub h [] R} {Δ A B} {f : B → A → B} {r} {u : Sub h Δ A} → Path T (scanˢ f r u) → AllPairs _≢_ (names T)
                 → ∀ z {Δ′ A′} {x : Sub h Δ′ A′} → Path T x → is-just (At.part (store H r (lift z)) x) ≡ is-just (At.part H x)


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

  -- Every end a shut at `c` tells comes no sooner than `q`.
  Tells : Pos → Pos → List Pos → Set
  Tells q c = All (λ p → q ≤ᵖ (if p <ᵖ c then c ++ [ subᴾ p ] else p ++ [ last ]))

  -- A shut heads where the node did, or at an end it tells.
  postulate
    shut-heads : ∀ {Γ A B q} (i : A ∈ᴸ Γ) c (b : U.Node Γ B) → Heads q b → Tells q c (untold i b) → Heads q (U.shut i c b)

  shut-heads-step : ∀ {Γ A B q} r c (t : U.Node Γ A) (S : U.Step (A ∷ Γ) B) → HeadsS q S → HeadsS q (U.shutˢᵗ r c t S)
  shut-heads-step r c t (U.outˢ _ _ _) hs = hs
  shut-heads-step r c t (U.skipˢ _ _)  hs = hs
  shut-heads-step r c t (U.endˢ _)     hs = hs
  shut-heads-step r c t U.hushˢ        hs = hs

  -- A connect past its source's end: its body's head, or a rest's skip
  -- under where the source would have skipped.
  ended-head : ∀ {Γ A B q} r c (b : U.Node (A ∷ Γ) B) (t : U.Node Γ A) (st : U.Step Γ A)
             → Heads q b → HeadsS q st → HeadsS q (U.endedˢ r b (U.step b) c t st)
  ended-head r c b t (U.skipˢ k t′) hb ht =
    if-head (U.beforeˢ (k ++ [ ix 0 ]) (U.step b)) (U.skipˢ (k ++ [ ix 0 ]) (U.connectᶜ r b (U.ended c t′))) (U.shutˢᵗ r c t (U.step b))
      (child-skip k (ix 0) (U.connectᶜ r b (U.ended c t′)) ht) (shut-heads-step r c t (U.step b) hb)
  ended-head r c b t (U.outˢ _ _ _) hb ht = shut-heads-step r c t (U.step b) hb
  ended-head r c b t (U.endˢ _)     hb ht = shut-heads-step r c t (U.step b) hb
  ended-head r c b t U.hushˢ        hb ht = shut-heads-step r c t (U.step b) hb

  -- What a connect past its source's end has not told its body's
  -- joiners, it tells no sooner than `q`.
  Untold : ∀ {h} (H : Heapᴹ h) (q : Pos) {Δ A} (t : Sub h Δ A) → Set₁
  Untold {h} H q t = ∀ {Δ′ A′ B′} {S c b kb k fd rp c₀ rt} {src : Sub h Δ′ A′} {bd : Sub h (A′ ∷ Δ′) B′}
                   → (ψ : Path t (connectˢ S c b kb k fd rp (just c₀) rt src bd)) → seen H ψ ≡ true → At.part H src ≡ nothing
                   → ∀ {b₀} → At.part H bd ≡ just b₀ → Tells q c₀ (untold (here refl) b₀)

  -- THE PARTS ABOVE A WRITTEN SCAN, walked down to it: a map's, a scan's
  -- and a defer's head is their child's; a take's, a flatMap's and a
  -- connect's are each bounded by what is below them.
  module Above {h} (H : Heapᴹ h) {T : Sub h [] R} {Δ A B} (f : B → A → B) (r : Ref h (base B)) (u : Sub h Δ A)
               (fs : AllPairs _≢_ (names T)) (z : B) (q : Pos) (bh : Each H (Heads q) T) (ut : Untold H q T) where
    H′ = store H r (lift z)

    Up : ∀ {Δ′ A′} {x : Sub h Δ′ A′} → Path T x → Set₁
    Up {x = x} ψ = seen H ψ ≡ true → ∀ {c} → At.part H′ x ≡ just c → Heads q c

    via : ∀ {Δ₀ B₀} {c k} {t : Sub h Δ₀ B₀} {ls : List (Lane h Δ₀ B₀)} → lane c k t ∈ᴸ ls → PathLanes ls t
    via (here refl) = this-lane here
    via (there m)   = next-lane (via m)

    postulate
      up-outer  : ∀ {Δ′ A′ B′} {op g fl oc k rf pl} {so : Sub h Δ′ A′} {ls : List (Lane h Δ′ B′)}
                  (ψ : Path T (flatMapˢ op g fl oc k rf pl so ls)) → Path so (scanˢ f r u) → Up (ψ ⊕ in-outer here) → Up ψ
      up-lanes  : ∀ {Δ′ A′ B′} {op g fl oc k rf pl} {so : Sub h Δ′ A′} {ls : List (Lane h Δ′ B′)}
                  (ψ : Path T (flatMapˢ op g fl oc k rf pl so ls)) {c k′} {t : Sub h Δ′ B′} (m : lane c k′ t ∈ᴸ ls)
                → Path t (scanˢ f r u) → Up (ψ ⊕ in-lanes (via m)) → Up ψ
      -- A written scan's part tells its joiners what it did.
      up-untold : ∀ {Δ′ B′} {x : Sub h Δ′ B′} → Path T x → Path x (scanˢ f r u)
                → ∀ {A′} (i : A′ ∈ᴸ Δ′) {b₀ b′} → At.part H x ≡ just b₀ → At.part H′ x ≡ just b′ → untold i b′ ≡ untold i b₀

    -- A connect past its source's end, the scan in its body: the body
    -- shut at the source's end.
    up-ended : ∀ {Δ′ A′ B′} {S c b kb k fd rp c₀ rt} {src : Sub h Δ′ A′} {bd : Sub h (A′ ∷ Δ′) B′}
               (ψ : Path T (connectˢ S c b kb k fd rp (just c₀) rt src bd)) → Path bd (scanˢ f r u) → Up (ψ ⊕ in-body here)
             → seen H ψ ≡ true → At.part H src ≡ nothing → ∀ {b₀ b′} → At.part H bd ≡ just b₀ → At.part H′ bd ≡ just b′
             → Heads q (U.connectᶜ rp (U.shut (here refl) c₀ b′) (U.ended c₀ rt))
    up-ended {rp = rp} {c₀} {rt} ψ π up sn p {b′ = b′} pb pb′ =
      ended-head rp c₀ (U.shut (here refl) c₀ b′) rt (U.step rt)
        (shut-heads (here refl) c₀ b′ (up (seen-join H ψ (in-body here) sn (cong (λ m → (is-just m ∨ true) ∧ true) p)) pb′)
                    (subst (Tells q c₀) (sym (up-untold (ψ ⊕ in-body here) π (here refl) pb pb′)) (ut ψ sn p pb)))
        (Each.rests bh ψ sn (cong₂ (At.connected H rp (just c₀) rt) p pb) p refl)

    lift-map : ∀ {Δ′ A′ B′} (g : A′ → B′) (m : Maybe (U.Node Δ′ A′)) → (∀ {c} → m ≡ just c → Heads q c)
             → ∀ {c} → At.mapᴹ H′ (U.mapᶜ g) m ≡ just c → Heads q c
    lift-map g (just c₀) up refl = heads-map g {c₀} (up refl)
    lift-map g nothing   up ()

    lift-scan : ∀ {Δ′ A′ B′} (g : B′ → A′ → B′) z′ (m : Maybe (U.Node Δ′ A′)) → (∀ {c} → m ≡ just c → Heads q c)
              → ∀ {c} → At.mapᴹ H′ (U.scanᶜ g z′) m ≡ just c → Heads q c
    lift-scan g z′ (just c₀) up refl = heads-scan g z′ {c₀} (up refl)
    lift-scan g z′ nothing   up ()

    lift-take : ∀ {Δ′ A′} i (p : A′ → Bool) (m : Maybe (U.Node Δ′ A′)) → (∀ {c} → m ≡ just c → Heads q c)
              → ∀ {c} → At.mapᴹ H′ (U.takeWhileᶜ i p) m ≡ just c → Heads q c
    lift-take i p (just c₀) up refl = heads-take i p {c₀} (up refl)
    lift-take i p nothing   up ()

    -- A take's switch is apart from the accumulator below it.
    live-apart : ∀ {Δ′ A′} {i p c k tk} {s : Sub h Δ′ A′} → Path T (takeWhileˢ i p c k tk s) → Path s (scanˢ f r u)
               → At.val H′ (Kit.live c) ≡ At.val H (Kit.live c)
    live-apart {c = c} {k} ψ π =
      cong lower (look-store H r (Kit.live c) (≢-flip (lookupᴬ (apart-r (cutNames c) (fresh-path ψ fs) (here refl)) (++⁺ʳ (quietName k) (names-path π (here refl))))))

    take-go : ∀ {Δ′ A′} {i p c k} {tk : Taking Δ′ A′} {s : Sub h Δ′ A′} (ψ : Path T (takeWhileˢ i p c k tk s)) → Up (ψ ⊕ in-take here) → seen H ψ ≡ true
            → ∀ b → At.val H (Kit.live c) ≡ b → ∀ {c′} → (if b then At.taking? H′ i p tk (At.part H′ s) else nothing) ≡ just c′ → Heads q c′
    take-go ψ up sn false lv ()
    take-go {i = i} {p} {tk = taking} {s} ψ up sn true lv e =
      lift-take i p (At.part H′ s) (up (seen-join H ψ (in-take here) sn (cong (λ b → b ∧ true ∧ true) lv))) e
    take-go {i = i} {p} {c} {tk = endingᵀ k′ n} {s} ψ up sn true lv {c′} e =
      Each.parts bh ψ sn (subst (λ b → (if b then At.taking? H i p (endingᵀ k′ n) (At.part H s) else nothing) ≡ just c′) (sym lv) e)
    take-go {tk = taken} ψ up sn true lv ()

    up-take : ∀ {Δ′ A′} {i p c k tk} {s : Sub h Δ′ A′} (ψ : Path T (takeWhileˢ i p c k tk s)) → Path s (scanˢ f r u)
            → Up (ψ ⊕ in-take here) → Up ψ
    up-take {i = i} {p} {c} {tk = tk} {s} ψ π up sn {c′} e =
      take-go ψ up sn (At.val H (Kit.live c)) refl (subst (λ b → (if b then At.taking? H′ i p tk (At.part H′ s) else nothing) ≡ just c′) (live-apart ψ π) e)

    -- A connect's source and body, apart.
    sides : ∀ {Δ′ A′ B′} {S c b kb k fd rp e rt} {src : Sub h Δ′ A′} {bd : Sub h (A′ ∷ Δ′) B′}
          → Path T (connectˢ S c b kb k fd rp e rt src bd) → AllPairs _≢_ (names src ++ names bd)
    sides {S = S} {c} {b} {kb} {k} ψ =
      pairs-r (quietName k) (pairs-r (quietName kb) (pairs-r ((_ , b) ∷ []) (pairs-r (cutNames c) (pairs-r (subjectNames S) (fresh-path ψ fs)))))

    src-go : ∀ {Δ′ A′ B′} {S c b kb k fd rp e rt} {src : Sub h Δ′ A′} {bd : Sub h (A′ ∷ Δ′) B′}
             (ψ : Path T (connectˢ S c b kb k fd rp e rt src bd)) → Up (ψ ⊕ in-source here) → seen H ψ ≡ true
           → ∀ ms′ ms mb → At.part H′ src ≡ ms′ → At.part H src ≡ ms → At.part H bd ≡ mb → is-just ms′ ≡ is-just ms
           → ∀ {c′} → At.connected H′ rp e rt ms′ mb ≡ just c′ → Heads q c′
    src-go ψ up sn ms′ ms nothing p′ p pb d ()
    src-go {rp = rp} {e} ψ up sn (just s′) (just s) (just b′) p′ p pb d refl =
      heads-source rp {b′} {s′} (up (seen-join H ψ (in-source here) sn (cong (λ m → is-just m ∧ true) pb)) p′)
        (Each.parts bh (ψ ⊕ in-body here) (seen-join H ψ (in-body here) sn (cong (λ m → (is-just m ∨ is-just e) ∧ true) p)) pb)
    src-go ψ up sn (just _) nothing  (just _) p′ p pb ()
    src-go ψ up sn nothing  (just _) (just _) p′ p pb ()
    src-go {e = nothing} ψ up sn nothing nothing (just b′) p′ p pb d ()
    src-go {rp = rp} {e = just c₀} {rt} ψ up sn nothing nothing (just b′) p′ p pb d eq =
      Each.parts bh ψ sn (trans (cong₂ (At.connected H rp (just c₀) rt) p pb) eq)

    up-source : ∀ {Δ′ A′ B′} {S c b kb k fd rp e rt} {src : Sub h Δ′ A′} {bd : Sub h (A′ ∷ Δ′) B′}
                (ψ : Path T (connectˢ S c b kb k fd rp e rt src bd)) → Path src (scanˢ f r u) → Up (ψ ⊕ in-source here) → Up ψ
    up-source {rp = rp} {e} {rt} {src} {bd} ψ π up sn {c′} pe =
      src-go ψ up sn (At.part H′ src) (At.part H src) (At.part H bd) refl refl refl
        (scan-defined H (ψ ⊕ in-source π) fs z (ψ ⊕ in-source here))
        (subst (λ m → At.connected H′ rp e rt (At.part H′ src) m ≡ just c′)
               (part-alike H H′ bd (λ j m → look-store H r j (lookupᴬ (apart-r (names src) (sides ψ) (names-path π (here refl))) m))) pe)

    body-go : ∀ {Δ′ A′ B′} {S c b kb k fd rp e rt} {src : Sub h Δ′ A′} {bd : Sub h (A′ ∷ Δ′) B′}
              (ψ : Path T (connectˢ S c b kb k fd rp e rt src bd)) → Path bd (scanˢ f r u) → Up (ψ ⊕ in-body here) → seen H ψ ≡ true
            → ∀ ms mb′ mb → At.part H src ≡ ms → At.part H′ bd ≡ mb′ → At.part H bd ≡ mb → is-just mb′ ≡ is-just mb
            → ∀ {c′} → At.connected H′ rp e rt ms mb′ ≡ just c′ → Heads q c′
    body-go ψ π up sn ms nothing mb p pb′ pb d ()
    body-go ψ π up sn ms (just _) nothing p pb′ pb ()
    body-go {rp = rp} {e} ψ π up sn (just s) (just b′) (just b) p pb′ pb d refl =
      heads-source rp {b′} {s} (Each.parts bh (ψ ⊕ in-source here) (seen-join H ψ (in-source here) sn (cong (λ m → is-just m ∧ true) pb)) p)
        (up (seen-join H ψ (in-body here) sn (cong (λ m → (is-just m ∨ is-just e) ∧ true) p)) pb′)
    body-go {e = nothing} ψ π up sn nothing (just b′) (just b) p pb′ pb d ()
    body-go {e = just c₀} ψ π up sn nothing (just b′) (just b) p pb′ pb d refl = up-ended ψ π up sn p pb pb′

    up-body : ∀ {Δ′ A′ B′} {S c b kb k fd rp e rt} {src : Sub h Δ′ A′} {bd : Sub h (A′ ∷ Δ′) B′}
              (ψ : Path T (connectˢ S c b kb k fd rp e rt src bd)) → Path bd (scanˢ f r u) → Up (ψ ⊕ in-body here) → Up ψ
    up-body {rp = rp} {e} {rt} {src} {bd} ψ π up sn {c′} pe =
      body-go ψ π up sn (At.part H src) (At.part H′ bd) (At.part H bd) refl refl refl
        (scan-defined H (ψ ⊕ in-body π) fs z (ψ ⊕ in-body here))
        (subst (λ m → At.connected H′ rp e rt m (At.part H′ bd) ≡ just c′)
               (part-alike H H′ src (λ j m → look-store H r j (lookupᴬ (apart-l (names src) (sides ψ) (names-path π (here refl))) m))) pe)

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

  -- A call under way: what the ghost has not told a shut body's
  -- joiners, it tells no sooner than where the run is.
  postulate
    tells-past : ∀ {g ℓ m₁ Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {v : Sub (Conf.world (Mach.conf m₁)) Δ A} {σ : Path T v} {sg}
               → Calling g ℓ m₁ σ sg → Untold (Conf.heap (Mach.conf m₁)) (Conf.pos (Mach.conf m₁)) T

  -- The scan and every part above it still head no sooner than where
  -- the run is.
  scan-above : ∀ {g ℓ m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {f : B → A → B} {r} {u : Sub (Conf.world (Mach.conf m₁)) Δ A}
               (ρ : Path T (scanˢ f r u)) {y : A} → Calling g ℓ m₁ (ρ ⊕ in-scan here) (sends y)
             → ∀ {Δ′ A′} {x : Sub (Conf.world (Mach.conf m₁)) Δ′ A′} (ψ : Path T x) → Path x (scanˢ f r u) → seen (Conf.heap (Mach.conf m₁)) ψ ≡ true
             → ∀ {c} → At.part (store (Conf.heap (Mach.conf m₁)) r (lift (f (At.val (Conf.heap (Mach.conf m₁)) r) y))) x ≡ just c
             → Heads (Conf.pos (Mach.conf m₁)) c
  scan-above {m₁ = m₁} {f = f} {r} {u} ρ {y} cl =
    Above.above H f r u (Books.fresh (Calling.books cl)) (f (At.val H r) y) (Conf.pos (Mach.conf m₁)) (Calling.behind cl) (tells-past cl)
    where H = Conf.heap (Mach.conf m₁)

  just-of : ∀ {ℓ} {X : Set ℓ} {m : Maybe X} → is-just m ≡ true → Σ X λ c → m ≡ just c
  just-of {m = just c} _ = c , refl

  none-of : ∀ {ℓ} {X : Set ℓ} {m : Maybe X} → is-just m ≡ false → m ≡ nothing
  none-of {m = nothing} _ = refl

  -- The parts above the scan move with it; every other part reads alike.
  scan-behind : ∀ {g ℓ m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {f : B → A → B} {r} {u : Sub (Conf.world (Mach.conf m₁)) Δ A}
                (ρ : Path T (scanˢ f r u)) {y : A} → Calling g ℓ m₁ (ρ ⊕ in-scan here) (sends y)
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
      fs = Books.fresh (Calling.books cl)
      bh = Calling.behind cl
      sees = scan-sees H ρ fs (f (At.val H r) y)
      def  = scan-defined H ρ fs (f (At.val H r) y)

  -- One store leaves every other name alike; two in turn, every name
  -- neither wrote.
  off-store : ∀ {h k} (H : Heapᴹ h) (i : h ∋ k) {x} → Off H (store H i x) ((k , i) ∷ [])
  off-store H i j (ne ∷ []) = look-store H i j (≢-flip ne)

  off-++ : ∀ {h} {H H₁ H₂ : Heapᴹ h} (ns : List (Name h)) {ms} → Off H H₁ ns → Off H₁ H₂ ms → Off H H₂ (ns ++ ms)
  off-++ ns o₁ o₂ j a = trans (o₂ j (++⁻ʳ ns a)) (o₁ j (++⁻ˡ ns a))

  -- A NODE REPLANTED, QUEUING ALIKE: its pending frames, its subjects
  -- and its joiners as before, the queue as before.
  plant-queue : ∀ {h} (H : Heapᴹ h) {T : Sub h [] R} {Δ A} {u : Sub h Δ A} (ρ : Path T u) (v : Sub h Δ A)
              → pendings u ≡ pendings v → subjects u ≡ subjects v → (∀ E → joiners u E ≡ joiners v E)
              → ∀ {q clk ts} → Queue H q clk ts T → Queue H q clk ts (plant ρ v)
  plant-queue H {T} ρ v ep es ej {ts = ts} qu =
    record { timed   = subst (At.Timed H ts) (sym pend) (Queue.timed qu)
           ; joined  = subst₂ (At.Joined H) (sym (subjects-plant ρ v es)) (sym (joiners-plant ρ v ej _)) (Queue.joined qu)
           ; ordered = Queue.ordered qu ; ahead = Queue.ahead qu }
    where
      pend : pendings (plant ρ v) ≡ pendings T
      pend with pendings-plant ρ v
      ... | xs , ys , e , e′ = trans e′ (trans (cong (λ z → xs ++ z ++ ys) (sym ep)) (sym e))

  -- A WRITE AT ONE NODE'S OWN NAMES: what the kernels and the meaning
  -- hold of the tree they hold after, the node's own clauses their
  -- premises.  The write reaches no name outside the node, so every
  -- other node reads alike.
  -- A WRITE INSIDE THE PATH'S END, LIFTED: no ancestor reads its path
  -- child's names, only its siblings' and its own cells, so every lift
  -- above the write reads alike.
  lane1-alike : ∀ {h} (H H′ : Heapᴹ h) {Δ B} {c : Kit.Cut h} {k} {s : Sub h Δ B} → look H′ (Kit.live c) ≡ look H (Kit.live c)
              → At.part H′ s ≡ At.part H s → At.partLanes H′ (lane c k s ∷ []) ≡ At.partLanes H (lane c k s ∷ [])
  lane1-alike H H′ el ep rewrite el | ep = refl

  mutual
    lifts-off : ∀ {h} (H H′ : Heapᴹ h) {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (ρ : Path t u) → AllPairs _≢_ (names t)
              → Off H H′ (names u) → ∀ {s S} → Lifts H ρ s S → Lifts H′ ρ s S
    lifts-off H H′ here ps off lifts-here = lifts-here
    lifts-off H H′ (in-map ρ) ps off (lifts-map L) = lifts-map (lifts-off H H′ ρ ps off L)
    lifts-off H H′ (in-scan {f = f} {r} ρ) (nr ∷ ps) off (lifts-scan {s = s} {S} L) =
      subst (λ z → Lifts H′ (in-scan {f = f} {r} ρ) s (U.scanˢ f z S)) (cong lower (Heaps.keep H H′ off (names-path ρ) r nr))
            (lifts-scan (lifts-off H H′ ρ ps off L))
    lifts-off H H′ (in-take {c = c} {k} ρ) ps@(nl ∷ _) off (lifts-take lv L) =
      lifts-take (trans (cong lower (Heaps.keep H H′ off (λ m → there (++⁺ʳ (quietName k) (names-path ρ m))) (Kit.live c) nl)) lv)
                 (lifts-off H H′ ρ (pairs-r (quietName k) (pairs-r (cutNames c) ps)) off L)
    lifts-off H H′ (in-outer {op = op} {f} {fl} {oc} {k} {r} {pl} {t = so} {ls} ρ) ps@(_ ∷ _ ∷ aq ∷ _) off (lifts-outer {s = s} {S} {o₀} of pb L) =
      subst₂ (λ zs qs → Lifts H′ (in-outer {op = op} {f} {fl} {oc} {k} {r} {pl} {ls = ls} ρ) s (U.outerˢ op (λ a q → U.subscribe (f a) q) o₀ S zs qs pl)) el eq
        (lifts-outer (subst (OuterFirst S) (sym el) of) (subst (λ zs → PoolBehind pl (U.outerOf (just o₀)) (U.earliest zs)) (sym el) pb)
                     (lifts-off H H′ ρ (proj₁ (pairs-split (names so) P)) off L))
      where
        P  = pairs-r ((_ , r) ∷ []) (pairs-r (quietName k) (pairs-r (cutNames oc) (pairs-r (flatNames fl) ps)))
        el = partLanes-alike H H′ ls (Heaps.keeps H H′ off (names-path ρ) (apart-l (names so) P))
        eq = cong lower (Heaps.keep H H′ off (λ m → there (there (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ˡ (names-path ρ m)))))))
                                    (FlatKit.Flat.queue fl) aq)
    lifts-off H H′ (in-lanes {op = op} {f} {fl} {oc} {k} {r} {pl} {t = so} {ls} πL) ps@(_ ∷ _ ∷ aq ∷ _) off (lifts-lanes {s = s} {bs} {l} {S} {as} {q} LL ee lf pb) =
      subst₂ (λ x qs → Lifts H′ (in-lanes {op = op} {f} {fl} {oc} {k} {r} {pl} {t = so} πL) s (U.laneˢ op (λ a q → U.subscribe (f a) q) x bs l S as qs pl)) ep eq
        (lifts-lanes (liftsL-off H H′ πL (pairs-r (names so) P) off LL) ee (subst (λ x → LaneFirst x q) (sym ep) lf)
                     (subst (λ x → PoolBehind pl (U.outerOf x) (U.found q bs l S as)) (sym ep) pb))
      where
        P  = pairs-r ((_ , r) ∷ []) (pairs-r (quietName k) (pairs-r (cutNames oc) (pairs-r (flatNames fl) ps)))
        ep = part-alike H H′ so (Heaps.keeps H H′ off (lanes-path πL) (apart-r (names so) P))
        eq = cong lower (Heaps.keep H H′ off (λ m → there (there (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ʳ (names so) (lanes-path πL m)))))))
                                    (FlatKit.Flat.queue fl) aq)
    lifts-off H H′ (in-source {S = Sj} {c} {b} {kb} {k} {t = src} {bd} ρ) ps off (lifts-source pb sf L) =
      lifts-source (trans (part-alike H H′ bd (Heaps.keeps H H′ off (names-path ρ) (apart-l (names src) Q₄))) pb) sf
                   (lifts-off H H′ ρ (proj₁ (pairs-split (names src) Q₄)) off L)
      where Q₄ = pairs-r (quietName k) (pairs-r (quietName kb) (pairs-r ((_ , b) ∷ []) (pairs-r (cutNames c) (pairs-r (subjectNames Sj) ps))))
    lifts-off H H′ (in-body {S = Sj} {c} {b} {kb} {k} {t = src} {bd} ρ) ps off (lifts-body pt bf L) =
      lifts-body (trans (part-alike H H′ src (Heaps.keeps H H′ off (names-path ρ) (apart-r (names src) Q₄))) pt) bf
                 (lifts-off H H′ ρ (pairs-r (names src) Q₄) off L)
      where Q₄ = pairs-r (quietName k) (pairs-r (quietName kb) (pairs-r ((_ , b) ∷ []) (pairs-r (cutNames c) (pairs-r (subjectNames Sj) ps))))
    lifts-off H H′ (in-body {S = Sj} {c} {b} {kb} {k} {t = src} {bd} ρ) ps off (lifts-shut pt e rb L) =
      lifts-shut (trans (part-alike H H′ src (Heaps.keeps H H′ off (names-path ρ) (apart-r (names src) Q₄))) pt) e rb
                 (lifts-off H H′ ρ (pairs-r (names src) Q₄) off L)
      where Q₄ = pairs-r (quietName k) (pairs-r (quietName kb) (pairs-r ((_ , b) ∷ []) (pairs-r (cutNames c) (pairs-r (subjectNames Sj) ps))))
    lifts-off H H′ (in-defer {k = k} ρ) ps off (lifts-defer L) = lifts-defer (lifts-off H H′ ρ (pairs-r (quietName k) ps) off L)

    liftsL-off : ∀ {h} (H H′ : Heapᴹ h) {Δ B Δ′ C} {ls : List (Lane h Δ B)} {u : Sub h Δ′ C} (πL : PathLanes ls u) → AllPairs _≢_ (laneNames ls)
               → Off H H′ (names u) → ∀ {s bs S as} → LiftsLane H πL s bs S as → LiftsLane H′ πL s bs S as
    liftsL-off H H′ (this-lane {c = c} {k} {t = s₀} {ls} ρ) ps@(nl ∷ _) off (lifts-this {s = s} {S} lv L) =
      subst (λ zs → LiftsLane H′ (this-lane {c = c} {k} {ls = ls} ρ) s [] S zs) el
        (lifts-this (trans (cong lower (Heaps.keep H H′ off (λ m → there (++⁺ʳ (quietName k) (++⁺ˡ (names-path ρ m)))) (Kit.live c) nl)) lv)
                    (lifts-off H H′ ρ (proj₁ (pairs-split (names s₀) P)) off L))
      where
        P  = pairs-r (quietName k) (pairs-r (cutNames c) ps)
        el = partLanes-alike H H′ ls (Heaps.keeps H H′ off (names-path ρ) (apart-l (names s₀) P))
    liftsL-off H H′ (next-lane {l = lane c k s₀} πL) ps@(nl ∷ _) off (lifts-next {s = s} {bs} {S} {as} LL) =
      subst (λ zs → LiftsLane H′ (next-lane {l = lane c k s₀} πL) s (zs ++ bs) S as) el
        (lifts-next (liftsL-off H H′ πL (pairs-r (names s₀) P) off LL))
      where
        P  = pairs-r (quietName k) (pairs-r (cutNames c) ps)
        el = lane1-alike H H′ {c = c} {k} {s₀} (Heaps.keep H H′ off (λ m → there (++⁺ʳ (quietName k) (++⁺ʳ (names s₀) (lanes-path πL m)))) (Kit.live c) nl)
                              (part-alike H H′ s₀ (Heaps.keeps H H′ off (lanes-path πL) (apart-r (names s₀) P)))

  -- A WRITE INSIDE THE PATH'S END, OPENED: the path opens through its
  -- ancestors' cuts and subjects, none of them the end's.
  mutual
    opened-off : ∀ {h} (H H′ : Heapᴹ h) {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (ρ : Path t u) → AllPairs _≢_ (names t)
               → Off H H′ (names u) → ∀ o → opened H′ o ρ ≡ opened H o ρ
    opened-off H H′ here ps off o = refl
    opened-off H H′ (in-map ρ) ps off o = opened-off H H′ ρ ps off o
    opened-off H H′ (in-scan ρ) (_ ∷ ps) off o = opened-off H H′ ρ ps off o
    opened-off H H′ (in-take {c = c} {k} ρ) ps@(nl ∷ _) off o =
      trans (cong (λ x → opened H′ (x ∧ o) ρ) (cong lower (Heaps.keep H H′ off (λ m → there (++⁺ʳ (quietName k) (names-path ρ m))) (Kit.live c) nl)))
            (opened-off H H′ ρ (pairs-r (quietName k) (pairs-r (cutNames c) ps)) off _)
    opened-off H H′ (in-outer {fl = fl} {oc} {k} {r} {t = so} ρ) ps off o =
      trans (cong (λ x → opened H′ (x ∧ o) ρ)
                  (cong lower (Heaps.keep H H′ off (λ m → there (++⁺ʳ (quietName k) (there (++⁺ˡ (names-path ρ m))))) (Kit.live oc) (pairs-hd (pairs-r (flatNames fl) ps)))))
            (opened-off H H′ ρ (proj₁ (pairs-split (names so) P)) off _)
      where P = pairs-r ((_ , r) ∷ []) (pairs-r (quietName k) (pairs-r (cutNames oc) (pairs-r (flatNames fl) ps)))
    opened-off H H′ (in-lanes {fl = fl} {oc} {k} {r} {t = so} πL) ps off o = openedL-off H H′ πL (pairs-r (names so) P) off o
      where P = pairs-r ((_ , r) ∷ []) (pairs-r (quietName k) (pairs-r (cutNames oc) (pairs-r (flatNames fl) ps)))
    opened-off H H′ (in-source {S = Sj} {c} {b} {kb} {k} {t = src} {bd} ρ) ps@(_ ∷ ac ∷ _) off o =
      trans (cong (λ x → opened H′ (not x) ρ)
                  (cong lower (Heaps.keep H H′ off (λ m → ++⁺ʳ (cutNames c) (there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ˡ (names-path ρ m))))))
                                          (Subject.closed Sj) ac)))
            (opened-off H H′ ρ (proj₁ (pairs-split (names src) Q₄)) off _)
      where Q₄ = pairs-r (quietName k) (pairs-r (quietName kb) (pairs-r ((_ , b) ∷ []) (pairs-r (cutNames c) (pairs-r (subjectNames Sj) ps))))
    opened-off H H′ (in-body {S = Sj} {c} {b} {kb} {k} {t = src} ρ) ps off o = opened-off H H′ ρ (pairs-r (names src) Q₄) off o
      where Q₄ = pairs-r (quietName k) (pairs-r (quietName kb) (pairs-r ((_ , b) ∷ []) (pairs-r (cutNames c) (pairs-r (subjectNames Sj) ps))))
    opened-off H H′ (in-defer {k = k} ρ) ps off o = opened-off H H′ ρ (pairs-r (quietName k) ps) off o

    openedL-off : ∀ {h} (H H′ : Heapᴹ h) {Δ B Δ′ C} {ls : List (Lane h Δ B)} {u : Sub h Δ′ C} (πL : PathLanes ls u) → AllPairs _≢_ (laneNames ls)
                → Off H H′ (names u) → ∀ o → openedL H′ o πL ≡ openedL H o πL
    openedL-off H H′ (this-lane {c = c} {k} {t = s₀} ρ) ps@(nl ∷ _) off o =
      trans (cong (λ x → opened H′ (x ∧ o) ρ) (cong lower (Heaps.keep H H′ off (λ m → there (++⁺ʳ (quietName k) (++⁺ˡ (names-path ρ m)))) (Kit.live c) nl)))
            (opened-off H H′ ρ (proj₁ (pairs-split (names s₀) (pairs-r (quietName k) (pairs-r (cutNames c) ps)))) off _)
    openedL-off H H′ (next-lane {l = lane c k s₀} πL) ps off o =
      openedL-off H H′ πL (pairs-r (names s₀) (pairs-r (quietName k) (pairs-r (cutNames c) ps))) off o

  module Wrote {h} (H H′ : Heapᴹ h) {T : Sub h [] R} {Δ A} {u : Sub h Δ A} (ρ : Path T u)
               {ns : List (Name h)} (off : Off H H′ ns) (mine : All (_∈ᴸ names u) ns) (fs : AllPairs _≢_ (names T)) where
    private
      offU : Off H H′ (names u)
      offU j a = off j (map (lookupᴬ a) mine)

    wr-kernels : (∀ {E o} → At.Holds H u E o → At.Holds H′ u E o) → (At.Gated H u → At.Gated H′ u) → (At.Spent H u → At.Spent H′ u)
               → Kernels H T → Kernels H′ T
    wr-kernels hv gv sv kn = record
      { holds   = Heaps.holds-path H H′ ρ fs offU hv (Kernels.holds kn)
      ; gated   = Heaps.gated-path H H′ ρ fs offU gv sv (Kernels.gated kn)
      ; settled = Kernels.settled kn }

    wr-meaning : (∀ ν → At.Fed H u ν → At.Fed H′ u ν) → Meaning H T → Meaning H′ T
    wr-meaning fv mn = record { fed = Heaps.fed-path H H′ ρ fs offU fv _ (Meaning.fed mn) }

    wr-lifts : ∀ {s S} → Lifts H ρ s S → Lifts H′ ρ s S
    wr-lifts = lifts-off H H′ ρ fs offU

    wr-opened : ∀ o → opened H′ o ρ ≡ opened H o ρ
    wr-opened = opened-off H H′ ρ fs offU

    wr-behind : At.part H′ u ≡ At.part H u → ∀ {q} → (Each H (Heads q) u → Each H′ (Heads q) u) → Each H (Heads q) T → Each H′ (Heads q) T
    wr-behind eq tr = Seeing.each-write H H′ {w = u} offU eq fs ρ tr

  -- A WRITE AT A SCAN'S ACCUMULATOR, ITS NODE'S CLAUSES: the source's
  -- names apart from the accumulator, so its kernels and feeds read
  -- alike.
  scan-lifts : ∀ {h} (H : Heapᴹ h) {T : Sub h [] R} {Δ A B} {f : B → A → B} {r} {u : Sub h Δ A} (ρ : Path T (scanˢ f r u)) → AllPairs _≢_ (names T)
             → ∀ {s S} z → Lifts H ρ s S → Lifts (store H r (lift z)) ρ s S
  scan-lifts H {r = r} ρ fs z = Wrote.wr-lifts H (store H r (lift z)) ρ (off-store H r) (here refl ∷ []) fs

  scan-holds : ∀ {h} (H : Heapᴹ h) {Δ A B} {f : B → A → B} {r} {u : Sub h Δ A} → AllPairs _≢_ (names (scanˢ f r u))
             → ∀ z {E o} → At.Holds H (scanˢ f r u) E o → At.Holds (store H r (lift z)) (scanˢ f r u) E o
  scan-holds H {r = r} {u} (nr ∷ _) z = Heaps.holds-alike H (store H r (lift z)) u (λ j m → look-store H r j (lookupᴬ nr m))

  scan-gated : ∀ {h} (H : Heapᴹ h) {Δ A B} {f : B → A → B} {r} {u : Sub h Δ A} → AllPairs _≢_ (names (scanˢ f r u))
             → ∀ z → At.Gated H (scanˢ f r u) → At.Gated (store H r (lift z)) (scanˢ f r u)
  scan-gated H {r = r} {u} (nr ∷ _) z = Heaps.gated-alike H (store H r (lift z)) u (λ j m → look-store H r j (lookupᴬ nr m))

  scan-spent : ∀ {h} (H : Heapᴹ h) {Δ A B} {f : B → A → B} {r} {u : Sub h Δ A} → AllPairs _≢_ (names (scanˢ f r u))
             → ∀ z → At.Spent H (scanˢ f r u) → At.Spent (store H r (lift z)) (scanˢ f r u)
  scan-spent H {r = r} {u} (nr ∷ _) z = Heaps.spent-alike H (store H r (lift z)) u (λ j m → look-store H r j (lookupᴬ nr m))

  scan-fed : ∀ {h} (H : Heapᴹ h) {Δ A B} {f : B → A → B} {r} {u : Sub h Δ A} → AllPairs _≢_ (names (scanˢ f r u))
           → ∀ z ν → At.Fed H (scanˢ f r u) ν → At.Fed (store H r (lift z)) (scanˢ f r u) ν
  scan-fed H {r = r} {u} (nr ∷ _) z = Heaps.fed-alike H (store H r (lift z)) u (λ j m → look-store H r j (lookupᴬ nr m))

  postulate
    scan-queue : ∀ {h} (H : Heapᴹ h) {T : Sub h [] R} {Δ A B} {f : B → A → B} {r} {u : Sub h Δ A} → Path T (scanˢ f r u) → AllPairs _≢_ (names T)
               → ∀ {p clk ts} z → Queue H p clk ts T → Queue (store H r (lift z)) p clk ts T

  -- A WRITE AT A SCAN'S ACCUMULATOR, FRAMED: the node's own clauses, the
  -- rest of the tree by the frame.
  module _ {h} (H : Heapᴹ h) {T : Sub h [] R} {Δ A B} {f : B → A → B} {r} {u : Sub h Δ A} (ρ : Path T (scanˢ f r u)) (fs : AllPairs _≢_ (names T)) where
    private
      fr : AllPairs _≢_ (names (scanˢ f r u))
      fr = fresh-path ρ fs

      module Wr z = Wrote H (store H r (lift z)) ρ (off-store H r) (here refl ∷ []) fs

    scan-kernels : ∀ z → Kernels H T → Kernels (store H r (lift z)) T
    scan-kernels z = Wr.wr-kernels z (λ {E} {o} → scan-holds H {f = f} {u = u} fr z {E} {o}) (scan-gated H {f = f} {u = u} fr z) (scan-spent H {f = f} {u = u} fr z)

    scan-meaning : ∀ z → Meaning H T → Meaning (store H r (lift z)) T
    scan-meaning z = Wr.wr-meaning z (scan-fed H {f = f} {u = u} fr z)
