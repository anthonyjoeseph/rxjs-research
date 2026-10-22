{-# OPTIONS --guardedness #-}

-- THE LIFT: the teardown's steps, and the ghost's step lifted from a
-- path whose siblings all wait (`lift-up`).
module adequacy.Lift where

open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Properties using (++-assoc)
open import Data.List.Relation.Unary.Any using (Any; here)
import Data.List.Relation.Unary.Any as Any
open import Data.Empty using (⊥)
open import Data.Sum using (inj₂; [_,_]′)
open import Data.Nat.Properties using (≤-refl)
open import Data.List.Relation.Unary.All using (All; []; _∷_; map) renaming (lookup to lookupᴬ)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to all-++⁺)
open import Data.List.Relation.Unary.AllPairs using (_∷_)
open import Data.List.Relation.Unary.Linked using (_∷_)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴸ_)
open import Level using (Lift)
open import Data.Maybe using (Maybe; just; nothing; is-just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import denotation.MonotonicList.Events using (Events∞; Pos; Timeline; at; ix; last; _<ᵖ_; <ᵖ-asym)
open import denotation.MonotonicList using (agree-refl)
import denotation.Unfold as U
open import denotation.MonotonicList.Events using () renaming (sub to subᴾ)
open import adequacy.Sorted using (_≤ᵖ_; Under)
open import adequacy.Sorted.Walk using (module SortingWalk)
open import operation.Machine using (module Machine)
open import adequacy.Strong using (module Strongly)
open import adequacy.Strong.Against using (module StrongAgainst)
open import adequacy.Strong.Held using (module StrongHeld)
open import adequacy.Moves using (module Moving)
open import adequacy.Torn using (module Tearing)
open import adequacy.Unsub using (module Unsubbing)
open import adequacy.Local using (module Locality)
open import adequacy.Lowers using (module Lowering)
open import denotation.Denote using (⟦_⟧)
import Tree as T
open import operation.PureObservable using (Out; note; Pureᴾ)
open import operation.AbstractObservable using (module Heap; module Run) renaming (module Machine to Shared)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import adequacy.Ghost using (module Ghosting)
open import adequacy.Ghost.Paths using (module GhostingPaths)
open import adequacy.Fork using (module Forking)
open import adequacy.Restages using (module Staging)
open import adequacy.Scanned using (module Scanning)
open import adequacy.Taken using (module Taking)
open import adequacy.Connected using (module Connecting)
open import adequacy.Flatted using (module Flatting)
open import adequacy.Replant using (module Replanting)
open import adequacy.Told using (untold)
open import adequacy.Frame.Repool using (module FramingRepool)
open import adequacy.Shift using (module Shifting)
open Events∞



module Lifting (R : Set) where
  open Machine R using (Mach; mach; Playing; Step; silent; step; Read)
  open Shared Timeline (Out R) using (Heapᴹ; Conf; ⟨_,_,_⟩; held; run; asking; bottom; spent?)
  open Heap using (_⊑_)
  open SortingWalk R using (Beyond)
  open Run (Pureᴾ R) using (Act; module Kit; module FlatKit)
  open Strongly R using (Sub; pendingˢ; coldˢ; ofˢ; mapˢ; scanˢ; takeWhileˢ; flatMapˢ; connectˢ; Lane; lane; here; module At; fired; waiting; Path; emitC; kontC; Leaf; feedC; srcC; taking; taken; feeding; PathLanes; this-lane; next-lane; in-map; in-scan; in-take; in-outer; in-lanes; in-source; in-body; in-defer; _⊕_; _≗_; rootObs; ⊕-here) renaming (ending to endingᵗ; ⟦_⟧ to ⟦_⟧ᶜ)
  open StrongAgainst R using (Books; Queue; Kernels; Meaning; Owned; Each; Lingers; pinned-skip; seen; seenL; owned-to)
  open StrongHeld R using (Strong; Carried; carried; Heads; DoneBy; Meets; module Eaching; module Lingering; Untold; Ended)
  open StrongAgainst.Against R using (CtlAs; calmAs; noteAs; runAs; subAs; burstAs; bursts; agenda) renaming (Placed to Placedᴬ)
  open Moving R using (plant; true≢false)
  open Tearing R using (Site; takeSite; bodySite; siteCall; siteHeap; torn-take-part; torn-body-part; torn-take-each; torn-body-each; torn-take-lingers; torn-body-lingers; torn-take-flags)
  open Unsubbing R using (_⇝_; site-tears)
  open Locality R using (site-holds; site-gated; site-fed)
  open Lowering R using (site-lowers; queue-keeps; module Lowers; torn-owned; torn-body-flags)
  open Ghosting R using (Has; residual; _⊏_; ⊏-trans; _≺_; measure; load; loadOf; passed; lowered; showing; Hopped; Hops; opening; firstCall; SourceFirst; BodyFirst; OuterFirst; PoolBehind; RestBehind; LaneFirst; Lifts; lifts-here; lifts-map; lifts-scan; lifts-take; lifts-outer; lifts-lanes; lifts-source; lifts-body; lifts-shut; lifts-defer; LiftsLane; lifts-this; lifts-next)
  open GhostingPaths R using (module Far; module Calling; Far; Off; Opt; Clear; ClearL; clear-zip; clear-each; far-apart; opt-zip; all-zip; opt-each; each-lanes; each-sub; OneLane; opened; Calling; sends; Rises; Called; Aloft; hop-sorted)
  open Forking R using (subOf)
  open Staging R using (Offers; of-restage; empty-restage; map-restage; Restages)
  open Scanning R using (scan-restage)
  open Replanting R using (module Shift; Heading; Lingering)
  open FramingRepool R using ()
  open Shifting R using (tw-alike; ⊆-⊑; Pred)
  open Taking R using (take-restage)
  open Connecting R using (connect-restage)
  open Flatting R using (flat-restage)
  open Read

  -- Every end a shut at `c` tells comes strictly after `q`.
  Late : Pos → Pos → List Pos → Set
  Late q c = All (λ p → q <ᵖ (if p <ᵖ c then c ++ [ subᴾ p ] else p ++ [ last ]) ≡ true)

  postulate
    -- The turn, nothing held and no timer queued: the ghost shows
    -- nothing.
    turn-dry : ∀ {g m w} {σ : w ⊑ Conf.world (Mach.conf m)} → Carried g m → Conf.ctl (Mach.conf m) ≡ held σ bottom
             → Mach.bursts m ≡ [] → Mach.timers m ≡ [] → ∀ {k b} → Has (residual g) k b → ⊥

    -- A subscription begun at its pending node, by what it begins: its
    -- kernel run to the next re-entry state, its program smaller by what
    -- was begun.
    sub-cold    : ∀ {g m} (cr : Carried g m) {Δ A} {c : Timeline A} → subOf (Carried.ctlAs cr) ≡ just (Δ , A , T.cold c) → Hops cr
    sub-joined  : ∀ {g m} (cr : Carried g m) {Δ A} {i : A ∈ᴸ Δ} → subOf (Carried.ctlAs cr) ≡ just (Δ , A , T.connected i) → Hops cr

    -- A defer begun: the ghost past its skip.  Under a part that has
    -- ended it still subscribes, inside a connect's source burst, and may
    -- unfold there forever (`connect spin` under a cut take, which the
    -- meaning shows as skips forever, as the machine spins): no load
    -- bounds it, so the hop is the ghost past the pin its rest holds,
    -- which `Carried.lingers` ties to the hidden subtree.
    sub-defer   : ∀ {g m} (cr : Carried g m) {Δ A} {l : T.Later Timeline Δ A} → subOf (Carried.ctlAs cr) ≡ just (Δ , A , T.defer l) → Hops cr

    -- An `of` reading its observer closed: its burst over, nothing
    -- delivered.  The ghost must hold nothing of it.
    emit-shut : ∀ {g m} (cr : Carried g m) {Δ A p i xs} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i xs))
              → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → opened (Conf.heap (Mach.conf m)) true π ≡ false → Hops cr

    -- An `of` reading its observer open, its value handed on under the
    -- `of`'s scope: the `of` past it, the value on its way up, the
    -- ghost's step the value lifted.
    emit-run : ∀ {g m} (cr : Carried g m) {Δ A p i x xs} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i (x ∷ xs)))
             → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → opened (Conf.heap (Mach.conf m)) true π ≡ true
             → Lifts (Conf.heap (Mach.conf m)) π (U.step (U.ofᶜ p i (x ∷ xs))) (U.step g)
             → ∀ {m′} → step m ≡ silent m′ → Σ Mach λ m₁ → m′ ⇝ m₁ × Aloft g (load m (Carried.tree cr)) m₁

    -- A connect whose source has ended, holding an `of` in its body: the
    -- body's first event comes strictly before every end the shut would
    -- tell.  What the body holds the shut can tell is a joiner owed a
    -- value (a feed under way past the source's end, `Fed`'s `feeding`
    -- beside an `e`), or a joiner not yet subscribed (a pending
    -- `connected`, its end told where it would subscribe).  The first
    -- must not exist, the second must end past the body's first event.
    -- `Carried.told` bounds every told end below by the run's position,
    -- not strictly by the body's head.
    shut-late : ∀ {g m} (cr : Carried g m) {Δ A B Sj c b kb k fd rp e rt} {src : Sub (Conf.world (Mach.conf m)) Δ A}
                {bd : Sub (Conf.world (Mach.conf m)) (A ∷ Δ) B} (ρ : Path (Carried.tree cr) (connectˢ Sj c b kb k fd rp e rt src bd))
                {Δ′ A′ p i x xs} (π : Path bd (ofˢ {Δ = Δ′} {A′} p i (x ∷ xs)))
              → At.part (Conf.heap (Mach.conf m)) src ≡ nothing → ∀ {c₁} → e ≡ just c₁ → ∀ {b₀} → At.part (Conf.heap (Mach.conf m)) bd ≡ just b₀
              → Σ Pos λ q → U.headˢ (U.step b₀) ≡ just q × Late q c₁ (untold (Any.here refl) b₀)

    -- The agenda's first call an open `of`, held or hidden: no sibling
    -- the path to a part the ghost holds passes heads under the `of`'s
    -- base.  A value under it the ghost still holds is the `of`'s own;
    -- what a connect's source fed the body's joiners under its earlier
    -- values, they have taken.  Not through a pool over a hidden `of`,
    -- which steps under the base (`pooled-pin`).
    spread-held : ∀ {g m} (cr : Carried g m) {Δ A p i x xs} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i (x ∷ xs)))
                → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → opened (Conf.heap (Mach.conf m)) true π ≡ true
                → ∀ {Δ′ A′} {v : Sub (Conf.world (Mach.conf m)) Δ′ A′} (ψ : Path (Carried.tree cr) v) (τ : Path v (ofˢ {Δ = Δ} {A} p i (x ∷ xs))) → ψ ⊕ τ ≡ π
                → seen (Conf.heap (Mach.conf m)) ψ ≡ true
                → is-just (At.part (Conf.heap (Mach.conf m)) v) ≡ true → Clear (Conf.heap (Mach.conf m)) (Off p) ψ

    -- A subscription's continuation handed its unsubscribe, which it
    -- stashes: the ghost alike, a call fewer.
    kont-onward : ∀ {g m} (cr : Carried g m) {Δ A} {u : Sub _ Δ A} (lf : Leaf u) (π : Path (Carried.tree cr) u)
                → firstCall (Carried.ctlAs cr) ≡ just (kontC lf π) → Hops cr

    -- The rest of a connect's feed of a value: each subscriber left
    -- shows it or skips it.
    feed-onward : ∀ {g m} (cr : Carried g m) {Δ A B S c b kb k x r ss e rp rt} {s : Sub _ Δ A} {bd : Sub _ (A ∷ Δ) B}
                  (π : Path (Carried.tree cr) (connectˢ S c b kb k (feeding x r ss) rp e rt s bd))
                → firstCall (Carried.ctlAs cr) ≡ just (feedC π) → Hops cr

    -- A connect's source subscribed once its body is: its program begun.
    src-onward : ∀ {g m} (cr : Carried g m) {Δ A B S c b kb k fd e s₁ q rp rt} {bd : Sub _ (A ∷ Δ) B}
                 (π : Path (Carried.tree cr) (connectˢ S c b kb k fd rp e rt (pendingˢ {Δ = Δ} s₁ q) bd))
               → firstCall (Carried.ctlAs cr) ≡ just (srcC π) → Hops cr

    -- A live burst's sink polled: open, the frame to play; closed, the
    -- burst dropped and the stack resumed.
    burst-poll : ∀ {g m w K b bs} {σ : w ⊑ Conf.world (Mach.conf m)} (cr : Carried g m) → Conf.ctl (Mach.conf m) ≡ held σ K
               → Mach.bursts m ≡ just b ∷ bs → spent? (Conf.heap (Mach.conf m)) (Playing.handle b) ≡ false → Playing.polled b ≡ false
               → ∀ {m′} → step m ≡ silent m′ → Hopped (carried cr) m′

    -- A polled burst's frame played: a value delivered and run to the
    -- next re-entry state, a stall's skip passed, or a close scheduling
    -- the rest.
    burst-play : ∀ {g m w K b bs} {σ : w ⊑ Conf.world (Mach.conf m)} (cr : Carried g m) → Conf.ctl (Mach.conf m) ≡ held σ K
               → Mach.bursts m ≡ just b ∷ bs → spent? (Conf.heap (Mach.conf m)) (Playing.handle b) ≡ false → Playing.polled b ≡ true
               → ∀ {m′} → step m ≡ silent m′ → Hopped (carried cr) m′

    -- A value recorded is the least the ghost still holds.
    note-least : ∀ {g g′ m w a k K} {σ : w ⊑ Conf.world (Mach.conf m)} → Carried g m
               → Conf.ctl (Mach.conf m) ≡ asking {B = ⊤} (note a) k σ K → U.step g ≡ U.outˢ (Conf.pos (Mach.conf m)) a g′
               → ∀ {q b} → Has (residual g′) q b → q ≤ᵖ Conf.pos (Mach.conf m) → ⊥

  -- A shut tells each joiner once: shutting again tells nothing.
  told-idem : ∀ {Γ A B} (i : A ∈ᴸ Γ) c (j : B ∈ᴸ Γ) p e m → U.told i c j p (U.told i c j p e m) m ≡ U.told i c j p e m
  told-idem i c j p (just x) m           = refl
  told-idem i c j p nothing  (just refl) = refl
  told-idem i c j p nothing  nothing     = refl

  mutual
    shut-idem : ∀ {Γ A B} (i : A ∈ᴸ Γ) c (n : U.Node Γ B) → U.shut i c (U.shut i c n) ≡ U.shut i c n
    shut-idem i c (U.framesᶜ τ e m)            = refl
    shut-idem i c (U.burstᶜ τ r k b)           = refl
    shut-idem i c (U.ofᶜ p k xs)               = refl
    shut-idem i c (U.mapᶜ f n)                 = cong (U.mapᶜ f) (shut-idem i c n)
    shut-idem i c (U.scanᶜ f z n)              = cong (U.scanᶜ f z) (shut-idem i c n)
    shut-idem i c (U.takeWhileᶜ b p n)         = cong (U.takeWhileᶜ b p) (shut-idem i c n)
    shut-idem i c (U.flatMapᶜ op g o ls qs pl) rewrite shut-idemᴹ i c o | shut-idemᴸ i c ls | shut-idem i c pl = refl
    shut-idem i c (U.joinᶜ j p xs e)           = cong (U.joinᶜ j p xs) (told-idem i c j p e (U.same? i j))
    shut-idem i c (U.connectᶜ r b s)           rewrite shut-idem (Any.there i) c b | shut-idemˢ i c s = refl
    shut-idem i c (U.deferᶜ l p ns)            = refl
    shut-idem i c (U.endingᶜ p n)              = cong (U.endingᶜ p) (shut-idem i c n)
    shut-idem i c (U.restᶜ n)                  = cong U.restᶜ (shut-idem i c n)
    shut-idem i c U.idleᶜ                      = refl
    shut-idem i c (U.unionᶜ x y)               rewrite shut-idem i c x | shut-idem i c y = refl
    shut-idem i c (U.burstingᶜ r t)            = cong (U.burstingᶜ r) (shut-idem i c t)
    shut-idem i c (U.underᶜ s b)               rewrite shut-idemˢ i c s | shut-idem (Any.there i) c b = refl

    shut-idemᴹ : ∀ {Γ A B} (i : A ∈ᴸ Γ) c (o : Maybe (U.Node Γ B)) → U.shutᴹ i c (U.shutᴹ i c o) ≡ U.shutᴹ i c o
    shut-idemᴹ i c nothing  = refl
    shut-idemᴹ i c (just n) = cong just (shut-idem i c n)

    shut-idemᴸ : ∀ {Γ A B} (i : A ∈ᴸ Γ) c (ls : List (U.Node Γ B)) → U.shutᴸ i c (U.shutᴸ i c ls) ≡ U.shutᴸ i c ls
    shut-idemᴸ i c []       = refl
    shut-idemᴸ i c (n ∷ ns) = cong₂ _∷_ (shut-idem i c n) (shut-idemᴸ i c ns)

    shut-idemˢ : ∀ {Γ A B} (i : A ∈ᴸ Γ) c (s : U.Source Γ B) → U.shutˢ i c (U.shutˢ i c s) ≡ U.shutˢ i c s
    shut-idemˢ i c (U.live s)    = cong U.live (shut-idem i c s)
    shut-idemˢ i c (U.ended e t) = cong (U.ended e) (shut-idem i c t)

  -- A step, what follows it shut.
  shutᵗ : ∀ {Γ A B} → A ∈ᴸ Γ → Pos → U.Step Γ B → U.Step Γ B
  shutᵗ i c (U.outˢ k a n) = U.outˢ k a (U.shut i c n)
  shutᵗ i c (U.skipˢ k n)  = U.skipˢ k (U.shut i c n)
  shutᵗ i c (U.endˢ k)     = U.endˢ k
  shutᵗ i c U.hushˢ        = U.hushˢ

  shutˢᵗ-idem : ∀ {Γ A B} r c (t : U.Node Γ A) (S : U.Step (A ∷ Γ) B) → U.shutˢᵗ r c t (shutᵗ (Any.here refl) c S) ≡ U.shutˢᵗ r c t S
  shutˢᵗ-idem r c t (U.outˢ k a b) = cong (λ n → U.outˢ k a (U.connectᶜ r n (U.ended c t))) (shut-idem (Any.here refl) c b)
  shutˢᵗ-idem r c t (U.skipˢ k b)  = cong (λ n → U.skipˢ k (U.connectᶜ r n (U.ended c t))) (shut-idem (Any.here refl) c b)
  shutˢᵗ-idem r c t (U.endˢ e)     = refl
  shutˢᵗ-idem r c t U.hushˢ        = refl

  -- A node shut steps as it did, up to shutting what follows, when its
  -- first event comes strictly before every end the shut tells: each end
  -- told lands where nothing it could displace stands.  What follows
  -- differs by what a step builds fresh (a lane begun, a source's feed
  -- or end under an inner connect), which the shut after reaches alike.
  postulate
    step-late : ∀ {Γ A B} (i : A ∈ᴸ Γ) c (b : U.Node Γ B) {q} → U.headˢ (U.step b) ≡ just q → Late q c (untold i b)
              → shutᵗ i c (U.step (U.shut i c b)) ≡ shutᵗ i c (U.step b)

  -- A body shut steps as the body does, shut after, when its first
  -- event comes strictly before every end the shut tells.
  step-shut : ∀ {Γ A B} r c (t : U.Node Γ A) (b : U.Node (A ∷ Γ) B) {q} → U.headˢ (U.step b) ≡ just q → Late q c (untold (Any.here refl) b)
            → U.shutˢᵗ r c t (U.step (U.shut (Any.here refl) c b)) ≡ U.shutˢᵗ r c t (U.step b)
  step-shut r c t b hq lt =
    trans (sym (shutˢᵗ-idem r c t (U.step (U.shut (Any.here refl) c b))))
      (trans (cong (U.shutˢᵗ r c t) (step-late (Any.here refl) c b hq lt)) (shutˢᵗ-idem r c t (U.step b)))

  -- A connect whose source has ended, holding an `of` in its body: the
  -- body shut steps as the body does, shut after.
  shut-step : ∀ {g m} (cr : Carried g m) {Δ A B Sj c b kb k fd rp e rt} {src : Sub (Conf.world (Mach.conf m)) Δ A}
              {bd : Sub (Conf.world (Mach.conf m)) (A ∷ Δ) B} (ρ : Path (Carried.tree cr) (connectˢ Sj c b kb k fd rp e rt src bd))
              {Δ′ A′ p i x xs} (π : Path bd (ofˢ {Δ = Δ′} {A′} p i (x ∷ xs)))
            → At.part (Conf.heap (Mach.conf m)) src ≡ nothing → ∀ {c₁} → e ≡ just c₁ → ∀ {b₀} → At.part (Conf.heap (Mach.conf m)) bd ≡ just b₀
            → U.shutˢᵗ rp c₁ rt (U.step (U.shut (Any.here refl) c₁ b₀)) ≡ U.shutˢᵗ rp c₁ rt (U.step b₀)
  shut-step cr {rp = rp} {rt = rt} ρ π ps {c₁} ec {b₀} pb with shut-late cr ρ π ps ec pb
  ... | q , hq , lt = step-shut rp c₁ rt b₀ hq lt

  ----------------------------------------------------------------------
  -- A HIDDEN STEP: AN `of` READING ITS OBSERVER OPEN WHERE THE GHOST DOES
  -- NOT HOLD IT

  -- A connect's source fed on past what held it.  The source is
  -- subscribed after the body and its cut attached only once its
  -- subscribe returns, and it reads its subject, not its connect's
  -- observer; so a body, or a takeWhile or lane above the connect,
  -- ending inside that burst leaves the rest of the burst to run into a
  -- subject nobody reads, as rxjs does.  The value climbs to the node
  -- that hides it and dies at a guard.  Nothing under a part that has
  -- ended reads open, so no lane is admitted, no subscription begun on
  -- the way.

  -- Where the ghost shows that run: the held node whose tie
  -- (`Carried.lingers`) runs over the hidden `of`.  A flatMap's pool took
  -- the ended lane's or outer's rest; an ended source's rest is its
  -- connect's.  Each shows the source's steps inside its subscription as
  -- `burstingᶜ` pins.  Never the root gone: a first call's run meets
  -- the ghost (`run-meets`).  No takeWhile is a site: one completes and is cut
  -- inside its failing value's call (`takeWhileᴷ`), before its source's
  -- burst runs on, and its `ending` part steps to its end, never a pin.
  data VoidSite {g m} (cr : Carried g m) {Δ A} {v : Sub (Conf.world (Mach.conf m)) Δ A} (π : Path (Carried.tree cr) v) : Set₁ where
    in-pool : ∀ {Δ′ A′ B′ op f fl oc k r pl} {so : Sub (Conf.world (Mach.conf m)) Δ′ A′} {ls : List (Lane (Conf.world (Mach.conf m)) Δ′ B′)}
                (ψ : Path (Carried.tree cr) (flatMapˢ op f fl oc k r pl so ls)) (σ : Path (flatMapˢ op f fl oc k r pl so ls) v) → ψ ⊕ σ ≡ π
            → seen (Conf.heap (Mach.conf m)) ψ ≡ true → ∀ {c} → At.part (Conf.heap (Mach.conf m)) (flatMapˢ op f fl oc k r pl so ls) ≡ just c
            → VoidSite cr π
    in-rest : ∀ {Δ′ A′ B′ S c b kb k fd rp e rt} {src : Sub (Conf.world (Mach.conf m)) Δ′ A′} {bd : Sub (Conf.world (Mach.conf m)) (A′ ∷ Δ′) B′}
                (ψ : Path (Carried.tree cr) (connectˢ S c b kb k fd rp e rt src bd)) (σ : Path src v) → ψ ⊕ in-source σ ≡ π
            → seen (Conf.heap (Mach.conf m)) ψ ≡ true → ∀ {n} → At.part (Conf.heap (Mach.conf m)) (connectˢ S c b kb k fd rp e rt src bd) ≡ just n
            → At.part (Conf.heap (Mach.conf m)) src ≡ nothing → ∀ {c₀} → e ≡ just c₀
            → VoidSite cr π

  -- At an open `of` the ghost holds, its whole path.
  spread-past : ∀ {g m} (cr : Carried g m) {Δ A p i x xs} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i (x ∷ xs)))
              → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → opened (Conf.heap (Mach.conf m)) true π ≡ true
              → seen (Conf.heap (Mach.conf m)) π ≡ true → Clear (Conf.heap (Mach.conf m)) (Off p) π
  spread-past cr π fc op sn = spread-held cr π fc op π here (⊕-here π) sn refl

  postulate
    -- Every hidden step has its site.
    -- DEAD ROUTE: the ghost past the burst's skip (`U.burstingᶜ`).  A
    --   part past its end shows nothing under it: a cut takeWhile and a
    --   connect with no body have no part, and an `ending` take's rest
    --   stops at its end, which sits before every later value of the
    --   burst.  No skip of the hidden part's own is this value.
    void-site : ∀ {g m} (cr : Carried g m) {Δ A p i x xs} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i (x ∷ xs)))
              → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → opened (Conf.heap (Mach.conf m)) true π ≡ true
              → seen (Conf.heap (Mach.conf m)) π ≡ false → VoidSite cr π

    -- At a pool over a hidden `of`: what the flatMap's ended parts left
    -- running pins next under the run.  The hidden part's rest shows the
    -- source's steps inside its subscription as `burstingᶜ` pins, the
    -- next of them this value's.
    pooled-pin : ∀ {g m} (cr : Carried g m) {Δ A p i x xs} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i (x ∷ xs)))
              → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → opened (Conf.heap (Mach.conf m)) true π ≡ true
              → seen (Conf.heap (Mach.conf m)) π ≡ false
              → ∀ {Δ′ A′ B′ op f fl oc k r pl} {so : Sub (Conf.world (Mach.conf m)) Δ′ A′} {ls : List (Lane (Conf.world (Mach.conf m)) Δ′ B′)}
                  (ψ : Path (Carried.tree cr) (flatMapˢ op f fl oc k r pl so ls)) (σ : Path (flatMapˢ op f fl oc k r pl so ls) _) → ψ ⊕ σ ≡ π
              → seen (Conf.heap (Mach.conf m)) ψ ≡ true → ∀ {c} → At.part (Conf.heap (Mach.conf m)) (flatMapˢ op f fl oc k r pl so ls) ≡ just c
              → Σ Pos λ q → Σ (U.Node Δ′ ⊤) λ y′ → U.restˢ {B = ⊤} (At.pooled (Conf.heap (Mach.conf m)) fl so ls) ≡ U.skipˢ q y′ × Under p q

    -- At a pool over a hidden `of`: neither the flatMap's outer nor any
    -- lane it holds heads under the run, as no sibling along its path
    -- does (`spread-held`).
    -- DEAD ROUTE: `spread-held` along the whole path, the flatMap's step
    --   read off its `Clear`.  That step's `Pooled` asks the pool off the
    --   run, and at a pool site the pool steps under it (`pooled-pin`).
    pool-off : ∀ {g m} (cr : Carried g m) {Δ A p i x xs} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i (x ∷ xs)))
              → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → opened (Conf.heap (Mach.conf m)) true π ≡ true
              → seen (Conf.heap (Mach.conf m)) π ≡ false
              → ∀ {Δ′ A′ B′ op f fl oc k r pl} {so : Sub (Conf.world (Mach.conf m)) Δ′ A′} {ls : List (Lane (Conf.world (Mach.conf m)) Δ′ B′)}
                  (ψ : Path (Carried.tree cr) (flatMapˢ op f fl oc k r pl so ls)) (σ : Path (flatMapˢ op f fl oc k r pl so ls) _) → ψ ⊕ σ ≡ π
              → seen (Conf.heap (Mach.conf m)) ψ ≡ true → ∀ {c} → At.part (Conf.heap (Mach.conf m)) (flatMapˢ op f fl oc k r pl so ls) ≡ just c
              → Opt (Off p) (At.part (Conf.heap (Mach.conf m)) so) × All (Off p) (At.partLanes (Conf.heap (Mach.conf m)) ls)

    -- At a pool, the ghost's step its pin lifted: the run climbs to its
    -- guard and dies, the pool a pin on, the ghost past that pin.
    -- `merge (takeWhile false (λ _ → false) (connect (of [1,2]) (of [5])))
    -- (of [7])` means skips at the source's 1 and 2 between the take's end
    -- and the 7: the ghost alike would leave those pins ahead of every
    -- later sibling.
    pool-land : ∀ {g m} (cr : Carried g m) {Δ A p i x xs} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i (x ∷ xs)))
              → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → opened (Conf.heap (Mach.conf m)) true π ≡ true
              → seen (Conf.heap (Mach.conf m)) π ≡ false
              → ∀ {Δ′ A′ B′ op f fl oc k r pl} {so : Sub (Conf.world (Mach.conf m)) Δ′ A′} {ls : List (Lane (Conf.world (Mach.conf m)) Δ′ B′)}
                  (ψ : Path (Carried.tree cr) (flatMapˢ op f fl oc k r pl so ls)) (σ : Path (flatMapˢ op f fl oc k r pl so ls) _) → ψ ⊕ σ ≡ π
              → seen (Conf.heap (Mach.conf m)) ψ ≡ true → ∀ {c} → At.part (Conf.heap (Mach.conf m)) (flatMapˢ op f fl oc k r pl so ls) ≡ just c
              → ∀ {q c′} → U.step c ≡ U.skipˢ q c′ → Lifts (Conf.heap (Mach.conf m)) ψ (U.skipˢ q c′) (U.step g)
              → Hops cr

    -- At an ended source over a hidden `of`: what the source left
    -- running pins next under the run, the hidden part's burst's next.
    left-pin : ∀ {g m} (cr : Carried g m) {Δ A p i x xs} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i (x ∷ xs)))
              → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → opened (Conf.heap (Mach.conf m)) true π ≡ true
              → seen (Conf.heap (Mach.conf m)) π ≡ false
              → ∀ {Δ′ A′ B′ S c b kb k fd rp e rt} {src : Sub (Conf.world (Mach.conf m)) Δ′ A′} {bd : Sub (Conf.world (Mach.conf m)) (A′ ∷ Δ′) B′}
                  (ψ : Path (Carried.tree cr) (connectˢ S c b kb k fd rp e rt src bd)) (σ : Path src _) → ψ ⊕ in-source σ ≡ π
              → seen (Conf.heap (Mach.conf m)) ψ ≡ true → ∀ {n} → At.part (Conf.heap (Mach.conf m)) (connectˢ S c b kb k fd rp e rt src bd) ≡ just n
              → At.part (Conf.heap (Mach.conf m)) src ≡ nothing → ∀ {c₀} → e ≡ just c₀
              → Σ Pos λ q → Σ (U.Node Δ′ ⊤) λ y′ → U.restˢ {B = ⊤} (At.leftover (Conf.heap (Mach.conf m)) {B = ⊤} src) ≡ U.skipˢ q y′ × Under p q

    -- There, the body shut at the source's end steps after that pin.
    rest-body : ∀ {g m} (cr : Carried g m) {Δ A p i x xs} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i (x ∷ xs)))
              → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → opened (Conf.heap (Mach.conf m)) true π ≡ true
              → seen (Conf.heap (Mach.conf m)) π ≡ false
              → ∀ {Δ′ A′ B′ S c b kb k fd rp e rt} {src : Sub (Conf.world (Mach.conf m)) Δ′ A′} {bd : Sub (Conf.world (Mach.conf m)) (A′ ∷ Δ′) B′}
                  (ψ : Path (Carried.tree cr) (connectˢ S c b kb k fd rp e rt src bd)) (σ : Path src _) → ψ ⊕ in-source σ ≡ π
              → seen (Conf.heap (Mach.conf m)) ψ ≡ true → ∀ {n} → At.part (Conf.heap (Mach.conf m)) (connectˢ S c b kb k fd rp e rt src bd) ≡ just n
              → At.part (Conf.heap (Mach.conf m)) src ≡ nothing → ∀ {c₀} → e ≡ just c₀
              → ∀ {bo} → At.part (Conf.heap (Mach.conf m)) bd ≡ just bo → ∀ {q} → Under p q
              → U.beforeˢ (q ++ [ ix 0 ]) (U.step (U.shut (Any.here refl) c₀ bo)) ≡ true

    -- At an ended source's rest, the ghost's step its pin lifted: the rest
    -- a pin on, the ghost past it.
    rest-land : ∀ {g m} (cr : Carried g m) {Δ A p i x xs} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i (x ∷ xs)))
              → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → opened (Conf.heap (Mach.conf m)) true π ≡ true
              → seen (Conf.heap (Mach.conf m)) π ≡ false
              → ∀ {Δ′ A′ B′ S c b kb k fd rp e rt} {src : Sub (Conf.world (Mach.conf m)) Δ′ A′} {bd : Sub (Conf.world (Mach.conf m)) (A′ ∷ Δ′) B′}
                  (ψ : Path (Carried.tree cr) (connectˢ S c b kb k fd rp e rt src bd)) (σ : Path src _) → ψ ⊕ in-source σ ≡ π
              → seen (Conf.heap (Mach.conf m)) ψ ≡ true → ∀ {n} → At.part (Conf.heap (Mach.conf m)) (connectˢ S c b kb k fd rp e rt src bd) ≡ just n
              → At.part (Conf.heap (Mach.conf m)) src ≡ nothing → ∀ {c₀} → e ≡ just c₀
              → ∀ {q n′} → U.step n ≡ U.skipˢ q n′ → Lifts (Conf.heap (Mach.conf m)) ψ (U.skipˢ q n′) (U.step g)
              → Hops cr

  ----------------------------------------------------------------------
  -- THE TEARDOWN: what unsubscribing leaves, in the order `unsub` runs

  -- A cut from the agenda's head runs silently to the rest of the
  -- agenda, over the heap its switch thrown leaves.
  tear-cut : ∀ {g h hp p w σ K act clk ts bs td lg en mk}
             (cr : Carried g (mach (⟨_,_,_⟩ {h} hp p (run {w = w} act σ K)) clk ts bs td lg en mk))
             (z : Site (Carried.tree cr)) {ks}
           → act ≗ ⟦ siteCall z ∷ ks ⟧ᶜ → ∀ {m′} → step (mach ⟨ hp , p , run act σ K ⟩ clk ts bs td lg en mk) ≡ silent m′
           → Σ (Act h ⊤) λ act′ → act′ ≗ ⟦ ks ⟧ᶜ × m′ ⇝ mach ⟨ siteHeap hp z , p , run act′ σ K ⟩ clk ts bs td lg en mk
  tear-cut {hp = hp} cr z {ks} e eq = site-tears hp (Kernels.holds (Carried.kernels cr)) (Books.fresh (Carried.books cr)) z {ks} e eq

  -- A joiner silenced owes nothing; every other as it was.
  torn-fed : ∀ {g m} (cr : Carried g m) (z : Site (Carried.tree cr))
           → At.Fed (siteHeap (Conf.heap (Mach.conf m)) z) (Carried.tree cr) []
  torn-fed cr z = site-fed _ (Books.fresh (Carried.books cr)) z (Meaning.fed (Carried.meaning cr))

  -- Every subscription still against its kernel, and every gate: the
  -- cut moves only the node it runs from.
  torn-holds : ∀ {g m} (cr : Carried g m) (z : Site (Carried.tree cr))
             → At.Holds (siteHeap (Conf.heap (Mach.conf m)) z) (Carried.tree cr) [] rootObs
  torn-holds cr z = site-holds _ (Books.fresh (Carried.books cr)) z (Kernels.holds (Carried.kernels cr))

  torn-gated : ∀ {g m} (cr : Carried g m) (z : Site (Carried.tree cr))
             → At.Gated (siteHeap (Conf.heap (Mach.conf m)) z) (Carried.tree cr)
  torn-gated cr z = site-gated _ (Books.fresh (Carried.books cr)) z (Kernels.holds (Carried.kernels cr)) (Kernels.gated (Carried.kernels cr))

  -- The queue as it was: a teardown only spends, lowers and silences.
  torn-queue : ∀ {g m} (cr : Carried g m) (z : Site (Carried.tree cr))
             → Queue (siteHeap (Conf.heap (Mach.conf m)) z) (Conf.pos (Mach.conf m)) (Mach.clock m) (Mach.timers m) (Carried.tree cr)
  torn-queue cr z = queue-keeps (Lowers.keeps (site-lowers _ z)) (Carried.queue cr)

  -- A site holds no part, a body's by `Owned.bodies`, so the tree's
  -- part is the same once its switch is thrown.
  torn-part : ∀ {g m} (cr : Carried g m) (z : Site (Carried.tree cr))
            → firstCall (Carried.ctlAs cr) ≡ just (siteCall z)
            → At.part (siteHeap (Conf.heap (Mach.conf m)) z) (Carried.tree cr) ≡ At.part (Conf.heap (Mach.conf m)) (Carried.tree cr)
  torn-part cr (takeSite π) _ = torn-take-part _ π (Books.fresh (Carried.books cr))
  torn-part {m = mach ⟨ _ , _ , _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = runAs (_ ∷ _) _ _ } (bodySite π) refl =
    torn-body-part _ π (Books.fresh (Carried.books cr)) (Owned.bodies (Carried.owned cr) π (here refl))

  -- A timer fired: its cold's part is the frame it waited on, read
  -- alike, and it holds nothing below it.
  module _ {h} (H : Heapᴹ h) {Δ A τ e v u x} {sk : Heap.Sink h A} {hd} {fr} where
    private
      w₀ = coldˢ {Δ = Δ} {A} sk hd (waiting {u = v} τ e (at u x fr))
      w₁ = coldˢ {Δ = Δ} {A} sk hd (fired τ e (at u x fr))

    fire-heading : ∀ {q} {E : Pred _} → Heading H H q E w₀ w₁
    fire-heading = record
      { head-revive = λ j → j
      ; head-told   = λ i _ e₀ e′ → ⊆-⊑ λ m → subst (λ b → _ ∈ᴸ untold i b) (just-injective (trans (sym e′) e₀)) m
      ; head-below  = λ ev → record { parts = λ { here sn e → Each.parts ev here sn e } ; pools = λ () ; rests = λ () }
      ; head-untold = λ _ _ ()
      ; head-ended  = λ _ () }

    fire-lingering : Lingering H H w₀ w₁
    fire-lingering = record
      { ling-revive = λ j → j
      ; ling-rested = λ {C} → tw-alike {Γ = Δ} {A = C} {x = U.idleᶜ} refl
      ; ling-below  = λ _ → record { pools = λ () ; rests = λ () }
      ; ling-ended  = λ _ () }

  -- A live timer popped at the turn: its cold, fired, heads past where
  -- the run is, the queue's timers being past it.
  behind-fire : ∀ {g m} (cr : Carried g m) {Δ A τ e v u x sk hd fr}
                (π : Path (Carried.tree cr) (coldˢ {Δ = Δ} {A} sk hd (waiting {u = v} τ e (at u x fr))))
              → Each (Conf.heap (Mach.conf m)) (Heads (Conf.pos (Mach.conf m))) (plant π (coldˢ sk hd (fired τ e (at u x fr))))
  behind-fire {m = m} cr π =
    Shift.shift-behind H H π (λ _ _ → refl) [] (Books.fresh (Carried.books cr)) _ (Carried.told cr) (Carried.ended cr) (fire-heading H) (Carried.behind cr)
    where H = Conf.heap (Mach.conf m)

  -- The untold and ended invariants survive the fire step.
  fire-told : ∀ {g m} (cr : Carried g m) {Δ A τ e v u x sk hd fr}
              (π : Path (Carried.tree cr) (coldˢ {Δ = Δ} {A} sk hd (waiting {u = v} τ e (at u x fr))))
            → Untold (Conf.heap (Mach.conf m)) (Conf.pos (Mach.conf m)) (plant π (coldˢ sk hd (fired τ e (at u x fr))))
  fire-told {m = m} cr π =
    Shift.shift-told H H π (λ _ _ → refl) [] (Books.fresh (Carried.books cr)) _ (Carried.told cr) (Carried.ended cr) (fire-heading H)
    where H = Conf.heap (Mach.conf m)

  fire-ended : ∀ {g m} (cr : Carried g m) {Δ A τ e v u x sk hd fr}
               (π : Path (Carried.tree cr) (coldˢ {Δ = Δ} {A} sk hd (waiting {u = v} τ e (at u x fr))))
             → Ended (Conf.heap (Mach.conf m)) (plant π (coldˢ sk hd (fired τ e (at u x fr))))
  fire-ended {m = m} cr π =
    Shift.shift-ended H H π (λ _ _ → refl) [] (Books.fresh (Carried.books cr)) _ (Carried.ended cr) (fire-lingering H)
    where H = Conf.heap (Mach.conf m)

  -- A timer fired leaves every tie held: a cold runs nothing past its end.
  fire-lingers : ∀ {g m} (cr : Carried g m) {Δ A τ e v u x sk hd fr}
                 (π : Path (Carried.tree cr) (coldˢ {Δ = Δ} {A} sk hd (waiting {u = v} τ e (at u x fr))))
               → Lingers (Conf.heap (Mach.conf m)) (plant π (coldˢ sk hd (fired τ e (at u x fr))))
  fire-lingers {m = m} cr π =
    Shift.shift-lingers H H π (λ _ _ → refl) [] (Books.fresh (Carried.books cr)) _ (Carried.ended cr) (fire-lingering H) (Carried.lingers cr)
    where H = Conf.heap (Mach.conf m)

  -- Every part the ghost holds still heads no earlier than the run:
  -- what the teardown reached it holds no longer, the rest reads alike.
  torn-behind : ∀ {g m} (cr : Carried g m) (z : Site (Carried.tree cr))
              → firstCall (Carried.ctlAs cr) ≡ just (siteCall z)
              → Each (siteHeap (Conf.heap (Mach.conf m)) z) (Heads (Conf.pos (Mach.conf m))) (Carried.tree cr)
  torn-behind cr (takeSite π) _ = torn-take-each _ π (Books.fresh (Carried.books cr)) (Carried.behind cr)
  torn-behind {m = mach ⟨ _ , _ , _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = runAs (_ ∷ _) _ _ } (bodySite π) refl =
    torn-body-each _ π (Books.fresh (Carried.books cr)) (Owned.bodies (Carried.owned cr) π (here refl)) (Carried.behind cr)

  -- What the teardown reached leaves every tie held: no flag a tie reads
  -- is a take's or a body's kill switch.
  torn-lingers : ∀ {g m} (cr : Carried g m) (z : Site (Carried.tree cr))
               → firstCall (Carried.ctlAs cr) ≡ just (siteCall z)
               → Lingers (siteHeap (Conf.heap (Mach.conf m)) z) (Carried.tree cr)
  torn-lingers cr (takeSite π) _ = torn-take-lingers _ π (Books.fresh (Carried.books cr)) (Carried.lingers cr)
  torn-lingers {m = mach ⟨ _ , _ , _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = runAs (_ ∷ _) _ _ } (bodySite π) refl =
    torn-body-lingers _ π (Books.fresh (Carried.books cr)) (Owned.bodies (Carried.owned cr) π (here refl)) (Carried.lingers cr)

  -- The untold and ended invariants survive the teardown step.
  postulate
    torn-told : ∀ {g m} (cr : Carried g m) (z : Site (Carried.tree cr))
              → firstCall (Carried.ctlAs cr) ≡ just (siteCall z)
              → Untold (siteHeap (Conf.heap (Mach.conf m)) z) (Conf.pos (Mach.conf m)) (Carried.tree cr)
    torn-ended : ∀ {g m} (cr : Carried g m) (z : Site (Carried.tree cr))
               → firstCall (Carried.ctlAs cr) ≡ just (siteCall z)
               → Ended (siteHeap (Conf.heap (Mach.conf m)) z) (Carried.tree cr)

  -- And every flag reads its outer: below the site nothing is seen that
  -- was not seen before.
  torn-flags : ∀ {g m} (cr : Carried g m) (z : Site (Carried.tree cr))
             → firstCall (Carried.ctlAs cr) ≡ just (siteCall z)
             → DoneBy (siteHeap (Conf.heap (Mach.conf m)) z) (Carried.tree cr) []
  torn-flags cr (takeSite π) _ = torn-take-flags _ π (Books.fresh (Carried.books cr)) (Carried.flags cr)
  torn-flags {m = mach ⟨ _ , _ , _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = runAs (_ ∷ _) _ _ } (bodySite π) refl =
    torn-body-flags _ π (Books.fresh (Carried.books cr)) (Owned.bodies (Carried.owned cr) π (here refl)) (Carried.flags cr)

  -- A cut: its kill switch thrown, what it holds unsubscribed; the ghost
  -- alike, a call fewer.
  cut-onward : ∀ {g m} (cr : Carried g m) (z : Site (Carried.tree cr))
             → firstCall (Carried.ctlAs cr) ≡ just (siteCall z) → Hops cr
  cut-onward {g} {mach ⟨ hp , p , _ ⟩ clk ts bs td lg en mk} cr@record { ctlAs = runAs (_ ∷ ks) e Kᴬ } z refl eq
    with tear-cut cr z {ks} e eq
  ... | act′ , e′ , path = g , _ , path
    , carried (record
        { sane = Carried.sane cr ; placed = Carried.placed cr ; deep = Carried.deep cr ; tree = Carried.tree cr ; ctlAs = runAs ks e′ Kᴬ
        ; meets = trans (torn-part cr z refl) (Carried.meets cr)
        ; owned′ = owned-to (torn-owned hp z (Carried.owned cr))
        ; kernels = record { holds = torn-holds cr z ; gated = torn-gated cr z ; settled = Kernels.settled (Carried.kernels cr) }
        ; meaning = record { fed = torn-fed cr z }
        ; queue = torn-queue cr z
        ; books = record { fresh = Books.fresh (Carried.books cr) ; clocked = Books.clocked (Carried.books cr)
                         ; paidUp = Books.paidUp (Carried.books cr) ; running = Books.running (Carried.books cr) }
        ; sorted = hop-sorted cr eq path ; behind′ = Eaching.each-to _ _ (torn-behind cr z refl) ; told = torn-told cr z refl ; ended = torn-ended cr z refl ; lingers′ = Lingering.lingers-to _ (torn-lingers cr z refl) ; flags = torn-flags cr z refl })
    , lowered (λ n → agree-refl n _) (inj₂ (refl , ≤-refl))

  ----------------------------------------------------------------------
  -- THE GHOST'S STEP, FROM A PATH EVERY SIBLING OF WHICH WAITS

  -- A step whose next event is under `p`.
  data Below (p : Pos) {Γ A} (S : U.Step Γ A) : Set where
    below : ∀ {k} → U.headˢ S ≡ just k → Under p k → Below p S

  under-++ : ∀ {p k} z → Under p k → Under p (k ++ z)
  under-++ {p} z (y , refl) = y ++ z , ++-assoc p y z

  far-lt : ∀ {p k k′} → Beyond p k′ → Under p k → k <ᵖ k′ ≡ true
  far-lt record { past = f } (y , refl) = f y

  far-gt : ∀ {p k k′} → Beyond p k′ → Under p k → k′ <ᵖ k ≡ false
  far-gt {k = k} {k′} bk uk = <ᵖ-asym k k′ (far-lt bk uk)

  -- Each operator keeps the next event under `p`.
  below-map : ∀ {p Γ A B} {f : A → B} {S : U.Step Γ A} → Below p S → Below p (U.mapˢ f S)
  below-map {S = U.outˢ _ _ _} (below h u) = below h u
  below-map {S = U.skipˢ _ _}  (below h u) = below h u
  below-map {S = U.endˢ _}     (below h u) = below h u
  below-map {S = U.hushˢ} (below () _)

  below-scan : ∀ {p Γ A B} {f : B → A → B} {z} {S : U.Step Γ A} → Below p S → Below p (U.scanˢ f z S)
  below-scan {S = U.outˢ _ _ _} (below h u) = below h u
  below-scan {S = U.skipˢ _ _}  (below h u) = below h u
  below-scan {S = U.endˢ _}     (below h u) = below h u
  below-scan {S = U.hushˢ} (below () _)

  below-take : ∀ {p Γ A} i (q : A → Bool) {S : U.Step Γ A} → Below p S → Below p (U.takeWhileˢ i q S)
  below-take true  q {U.outˢ k a c} (below refl u) with q a
  ... | true  = below refl u
  ... | false = below refl (under-++ _ u)
  below-take false q {U.outˢ k a c} (below refl u) with q a
  ... | true  = below refl u
  ... | false = below refl (under-++ _ u)
  below-take i q {U.skipˢ _ _} (below h u) = below h u
  below-take i q {U.endˢ _}    (below h u) = below h u
  below-take i q {U.hushˢ} (below () _)

  below-outer : ∀ {p Γ A B} {op} {g : A → Pos → U.Node Γ B} {o : U.Node Γ A} {S ls qs pl} → Below p S → Below p (U.outerˢ op g o S ls qs pl)
  below-outer {S = U.outˢ q _ _} (below refl u) = below refl (under-++ _ u)
  below-outer {S = U.skipˢ _ _} (below h u) = below h u
  below-outer {S = U.endˢ _} {[]} {[]} (below h u) = below h u
  below-outer {S = U.endˢ _} {[]} {_ ∷ _} (below h u) = below h u
  below-outer {S = U.endˢ _} {_ ∷ _} (below h u) = below h u
  below-outer {S = U.hushˢ} (below () _)

  below-lane : ∀ {p Γ A B} {op} {g : A → Pos → U.Node Γ B} {o : Maybe (U.Node Γ A)} {bs l S as qs pl}
             → Below p S → Below p (U.laneˢ op g o bs l S as qs pl)
  below-lane {S = U.outˢ _ _ _} (below h u) = below h u
  below-lane {S = U.skipˢ _ _} (below h u) = below h u
  below-lane {S = U.endˢ c} {qs = _ ∷ _} (below refl u) = below refl (under-++ _ u)
  below-lane {o = nothing} {[]} {S = U.endˢ _} {[]} {[]} (below h u) = below h u
  below-lane {o = nothing} {[]} {S = U.endˢ _} {_ ∷ _} {[]} (below h u) = below h u
  below-lane {o = nothing} {_ ∷ _} {S = U.endˢ _} {qs = []} (below h u) = below h u
  below-lane {o = just _} {S = U.endˢ _} {qs = []} (below h u) = below h u
  below-lane {S = U.hushˢ} (below () _)

  below-source : ∀ {p Γ A B} {r} {b : U.Node (A ∷ Γ) B} {sb} {s : U.Node Γ A} {S} → SourceFirst S sb → Below p S → Below p (U.sourceˢ r b sb s S)
  below-source {S = U.outˢ q _ _} sf (below refl u) rewrite sf = below refl (under-++ _ u)
  below-source {S = U.skipˢ q _}  sf (below refl u) rewrite sf = below refl (under-++ _ u)
  below-source {S = U.endˢ c}     sf (below refl u) rewrite sf = below refl (under-++ _ u)
  below-source {S = U.hushˢ} () _

  below-body : ∀ {p Γ A B} {r} {s : U.Source Γ A} {S : U.Step (A ∷ Γ) B} → Below p S → Below p (U.bodyˢ r s S)
  below-body {S = U.outˢ _ _ _} (below h u) = below h u
  below-body {S = U.skipˢ _ _}  (below h u) = below h u
  below-body {S = U.endˢ _}     (below h u) = below h u
  below-body {S = U.hushˢ} (below () _)

  below-shut : ∀ {p Γ A B} {r c} {t : U.Node Γ A} {S : U.Step (A ∷ Γ) B} → Below p S → Below p (U.shutˢᵗ r c t S)
  below-shut {S = U.outˢ _ _ _} (below h u) = below h u
  below-shut {S = U.skipˢ _ _}  (below h u) = below h u
  below-shut {S = U.endˢ _}     (below h u) = below h u
  below-shut {S = U.hushˢ} (below () _)
