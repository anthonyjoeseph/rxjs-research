{-# OPTIONS --guardedness #-}

-- THE LIFT: the teardown's steps, and the ghost's step lifted from a
-- path whose siblings all wait (`lift-up`).
module adequacy.Lift where

open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Properties using (++-assoc)
open import Data.List.Relation.Unary.Any using (Any; here)
import Data.List.Relation.Unary.Any as Any
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Data.Nat.Properties using (≤-refl; <-trans)
open import Data.List.Relation.Unary.All using (All; []; _∷_; map) renaming (lookup to lookupᴬ)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to all-++⁺)
open import Data.List.Relation.Unary.AllPairs using (_∷_)
open import Data.List.Relation.Unary.Linked using (_∷_)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴸ_)
open import Level using (Lift)
open import Data.Maybe using (Maybe; just; nothing; is-just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import denotation.MonotonicList using (Events∞; Pos; Timeline; Agree; skip⁼; inside; agree-refl; at; ix; _<ᵖ_; <ᵖ-trans; <ᵖ-asym; <ᵖ-below)
import denotation.Unfold as U
open import denotation.MonotonicList using () renaming (sub to subᴾ)
open import adequacy.Sorted using (_≤ᵖ_; Under; module Sorting)
open import operation.Machine using (module Machine)
open import adequacy.Strong using (module Strongly)
open import adequacy.Moves using (module Moving)
open import adequacy.Torn using (module Tearing)
open import adequacy.Unsub using (module Unsubbing)
open import adequacy.Local using (module Locality)
open import adequacy.Lowers using (module Lowering)
open import denotation.Denote using (⟦_⟧)
import Tree as T
open import operation.PureObservable using (Out; note; Pureᴾ)
open import operation.AbstractObservable using (module Heap; module Run) renaming (module Machine to Shared)
open import Data.Bool using (Bool; true; false; _∧_; _∨_)
open import Data.Bool.Properties using (∧-zeroʳ)
open import adequacy.Ghost using (module Ghosting)
open import adequacy.Restage using (module Restaging)

open Events∞

module Lifting (R : Set) where
  open Machine R using (Mach; mach; Playing; Step; silent; step; Read)
  open Shared Timeline (Out R) using (Conf; ⟨_,_,_⟩; held; run; asking; bottom; spent?)
  open Heap using (_⊑_)
  open Sorting R using (Beyond)
  open Run (Pureᴾ R) using (Act; module Kit; module FlatKit)
  open Strongly R using (Strong; Carried; Books; carried; Sub; pendingˢ; coldˢ; ofˢ; mapˢ; scanˢ; takeWhileˢ; flatMapˢ; connectˢ; Lane; lane; here; module At; Queue; Kernels; Meaning; fired; waiting; Owned; Path; emitC; kontC; Leaf; feedC; srcC; taking; taken; feeding; PathLanes; this-lane; next-lane; in-map; in-scan; in-take; in-outer; in-lanes; in-source; in-body; in-defer; _⊕_; _≗_; Each; Heads; Lingers; Ties; Tied; Meets; rootObs; seen; seenL) renaming (ending to endingᵗ; ⟦_⟧ to ⟦_⟧ᶜ)
  open Strongly.Against R using (CtlAs; calmAs; noteAs; runAs; subAs; burstAs; bursts; agenda) renaming (Placed to Placedᴬ)
  open Moving R using (plant; true≢false; ⊕-here)
  open Tearing R using (Site; takeSite; bodySite; siteCall; siteHeap; torn-take-part; torn-body-part; torn-take-each; torn-body-each)
  open Unsubbing R using (_⇝_; site-tears)
  open Locality R using (site-holds; site-gated)
  open Lowering R using (site-lowers; queue-lowers; torn-owned; fed-lowers)
  open Ghosting R using (module Far; module Calling; Has; residual; _⊏_; ⊏-trans; _≺_; measure; load; loadOf; passed; lowered; showing; Hopped; Hops; opening; firstCall; SourceFirst; BodyFirst; OuterFirst; PoolBehind; RestBehind; LaneFirst; Lifts; lifts-here; lifts-map; lifts-scan; lifts-take; lifts-outer; lifts-lanes; lifts-source; lifts-body; lifts-shut; lifts-defer; LiftsLane; lifts-this; lifts-next; Far; Off; Opt; Clear; ClearL; clear-zip; clear-each; far-apart; opt-zip; all-zip; opt-each; each-lanes; each-sub; OneLane; opened; Calling; sends; Rises; Called; Aloft; hop-sorted)
  open Restaging R using (subOf; Offers; of-restage; empty-restage; map-restage; Restages; scan-restage; take-restage; flat-restage; connect-restage)
  open Read

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
    -- body shut steps as the body does, shut after.  What the body holds
    -- the shut can tell is a joiner owed a value (a feed under way past
    -- the source's end, `Fed`'s `feeding` beside an `e`), or a joiner
    -- not yet subscribed (a pending `connected`, its end told where it
    -- would subscribe).  The first must not exist, the second must end
    -- past every event the body steps to first.
    shut-step : ∀ {g m} (cr : Carried g m) {Δ A B Sj c b kb k fd rp e rt} {src : Sub (Conf.world (Mach.conf m)) Δ A}
                {bd : Sub (Conf.world (Mach.conf m)) (A ∷ Δ) B} (ρ : Path (Carried.tree cr) (connectˢ Sj c b kb k fd rp e rt src bd))
                {Δ′ A′ p i x xs} (π : Path bd (ofˢ {Δ = Δ′} {A′} p i (x ∷ xs)))
              → At.part (Conf.heap (Mach.conf m)) src ≡ nothing → ∀ {c₁} → e ≡ just c₁ → ∀ {b₀} → At.part (Conf.heap (Mach.conf m)) bd ≡ just b₀
              → U.shutˢᵗ rp c₁ rt (U.step (U.shut (Any.here refl) c₁ b₀)) ≡ U.shutˢᵗ rp c₁ rt (U.step b₀)

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

    -- A live timer popped at the turn: its cold, fired, heads past where
    -- the run is, the queue's timers being past it.
    behind-fire : ∀ {g m} (cr : Carried g m) {Δ A τ e v u x sk hd fr}
                  (π : Path (Carried.tree cr) (coldˢ {Δ = Δ} {A} sk hd (waiting {u = v} τ e (at u x fr))))
                → Each (Conf.heap (Mach.conf m)) (Heads (Conf.pos (Mach.conf m))) (plant π (coldˢ sk hd (fired τ e (at u x fr))))

    -- A timer fired leaves every tie held: a cold runs nothing past its end.
    fire-lingers : ∀ {g m} (cr : Carried g m) {Δ A τ e v u x sk hd fr}
                   (π : Path (Carried.tree cr) (coldˢ {Δ = Δ} {A} sk hd (waiting {u = v} τ e (at u x fr))))
                 → Lingers (Conf.heap (Mach.conf m)) (plant π (coldˢ sk hd (fired τ e (at u x fr))))

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

  -- Two steps alike as rests: the same pin, or none.
  data Pinned {Γ} {B C : Set} : U.Step Γ B → U.Step Γ C → Set₁ where
    pinned   : ∀ {k x y} → Pinned (U.skipˢ k x) (U.skipˢ k y)
    unpinned : Pinned U.hushˢ U.hushˢ

  pinned-trans : ∀ {Γ B C D} {a : U.Step Γ B} {b : U.Step Γ C} {c : U.Step Γ D} → Pinned a b → Pinned b c → Pinned a c
  pinned-trans pinned   pinned   = pinned
  pinned-trans unpinned unpinned = unpinned

  pinned-skip : ∀ {Γ B C} {a : U.Step Γ B} {b : U.Step Γ C} {q y′} → Pinned a b → b ≡ U.skipˢ q y′ → Σ (U.Node Γ B) λ x′ → a ≡ U.skipˢ q x′
  pinned-skip pinned refl = _ , refl

  union-pinned : ∀ {Γ B C} {x y : U.Node Γ B} {sx sy} {x′ y′ : U.Node Γ C} {sx′ sy′}
               → Pinned sx sx′ → Pinned sy sy′ → Pinned (U.unionˢ x sx y sy) (U.unionˢ x′ sx′ y′ sy′)
  union-pinned (pinned {k}) (pinned {k′}) with k <ᵖ k′
  ... | true  = pinned
  ... | false = pinned
  union-pinned pinned   unpinned = pinned
  union-pinned unpinned q        = q

  under-pinned : ∀ {Γ A D B C} (s : U.Source Γ A) (st : U.Step (A ∷ Γ) D) → Pinned (U.underˢ {B = B} s st) (U.underˢ {B = C} s st)
  under-pinned s (U.skipˢ _ _)  = pinned
  under-pinned s (U.outˢ _ _ _) = unpinned
  under-pinned s (U.endˢ _)     = unpinned
  under-pinned s U.hushˢ        = unpinned

  -- A node's rest pins alike whatever it is read as.
  mutual
    rest-pinned : ∀ {Γ A B C} (c : U.Node Γ A) → Pinned (U.restˢ {B = B} c) (U.restˢ {B = C} c)
    rest-pinned (U.framesᶜ _ _ _)               = unpinned
    rest-pinned (U.burstᶜ _ _ _ _)              = unpinned
    rest-pinned (U.ofᶜ _ _ _)                   = unpinned
    rest-pinned (U.mapᶜ _ c)                    = rest-pinned c
    rest-pinned (U.scanᶜ _ _ c)                 = rest-pinned c
    rest-pinned (U.takeWhileᶜ _ _ c)            = rest-pinned c
    rest-pinned (U.flatMapᶜ _ _ o ls _ p)       = union-pinned (restᴹ-pinned o) (union-pinned (rests-pinned ls) (rest-pinned p))
    rest-pinned (U.joinᶜ _ _ _ _)               = unpinned
    rest-pinned {A = A} (U.connectᶜ r b (U.live s))    = union-pinned (bursts-pinned r s (U.step s)) (under-pinned (U.live s) (U.restˢ {B = A} b))
    rest-pinned {A = A} (U.connectᶜ r b (U.ended c t)) = union-pinned (bursts-pinned r t (U.step t)) (under-pinned (U.ended c t) (U.restˢ {B = A} b))
    rest-pinned (U.deferᶜ _ _ _)                = unpinned
    rest-pinned (U.endingᶜ _ n)                 = rest-pinned n
    rest-pinned (U.restᶜ n)                     = rest-pinned n
    rest-pinned U.idleᶜ                         = unpinned
    rest-pinned (U.unionᶜ x y)                  = union-pinned (rest-pinned x) (rest-pinned y)
    rest-pinned (U.burstingᶜ r t)               = bursts-pinned r t (U.step t)
    rest-pinned (U.underᶜ {C = D} s b)          = under-pinned s (U.restˢ {B = D} b)

    bursts-pinned : ∀ {Γ A B C} (r : Pos) (t : U.Node Γ A) (st : U.Step Γ A) → Pinned (U.burstsˢ {B = B} r t st) (U.burstsˢ {B = C} r t st)
    bursts-pinned r t (U.outˢ k _ _) with inside r k
    ... | true  = pinned
    ... | false = rest-pinned t
    bursts-pinned r t (U.skipˢ k _) with inside r k
    ... | true  = pinned
    ... | false = rest-pinned t
    bursts-pinned r t (U.endˢ _) = rest-pinned t
    bursts-pinned r t U.hushˢ    = rest-pinned t

    restᴹ-pinned : ∀ {Γ A B C} (o : Maybe (U.Node Γ A)) → Pinned (U.restᴹ {B = B} o) (U.restᴹ {B = C} o)
    restᴹ-pinned nothing  = unpinned
    restᴹ-pinned (just o) = rest-pinned o

    rests-pinned : ∀ {Γ A B C} (ls : List (U.Node Γ A)) → Pinned (U.restsˢ {B = B} ls) (U.restsˢ {B = C} ls)
    rests-pinned []       = unpinned
    rests-pinned (l ∷ ls) = union-pinned (rest-pinned l) (rests-pinned ls)

  -- A rest's shape: it steps as it rests.
  data Restful {Γ B} : U.Node Γ B → Set₁ where
    rf-idle  : Restful U.idleᶜ
    rf-rest  : ∀ {A} {n : U.Node Γ A} → Restful (U.restᶜ n)
    rf-union : ∀ {x y} → Restful (U.unionᶜ x y)
    rf-burst : ∀ {A r} {t : U.Node Γ A} → Restful (U.burstingᶜ r t)
    rf-under : ∀ {A C} {s : U.Source Γ A} {b : U.Node (A ∷ Γ) C} → Restful (U.underᶜ s b)

  restful-pinned : ∀ {Γ B} {c : U.Node Γ B} → Restful c → Pinned (U.step c) (U.restˢ {B = B} c)
  restful-pinned rf-idle                    = unpinned
  restful-pinned (rf-rest {n = n})          = rest-pinned n
  restful-pinned (rf-union {x = x} {y})     = union-pinned (rest-pinned x) (rest-pinned y)
  restful-pinned (rf-burst {r = r} {t = t}) = bursts-pinned r t (U.step t)
  restful-pinned (rf-under {C = C} {s = s} {b = b}) = under-pinned s (U.restˢ {B = C} b)

  -- Two rests tied: the one's next pin the other's.
  tied-skip : ∀ {Γ A B} {x : U.Node Γ A} {y : U.Node Γ B} {q y′} → Tied x y → U.restˢ {B = ⊤} y ≡ U.skipˢ q y′
            → Σ (U.Node Γ ⊤) λ x′ → U.restˢ {B = ⊤} x ≡ U.skipˢ q x′
  tied-skip {x = x} {y = y} t e = shown-skip (U.restˢ {B = ⊤} x) (t 1) e
    where
      shown-skip : ∀ {Γ} (s : U.Step Γ ⊤) {s′ : U.Step Γ ⊤} {q y′} → Agree 1 (U.shown s) (U.shown s′) → s′ ≡ U.skipˢ q y′
                 → Σ (U.Node Γ ⊤) λ x′ → s ≡ U.skipˢ q x′
      shown-skip (U.skipˢ k x′) (skip⁼ _ _) refl = x′ , refl
      shown-skip (U.outˢ _ _ _) ()          refl
      shown-skip (U.endˢ _)     ()          refl
      shown-skip U.hushˢ        ()          refl

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

    -- A flatMap's pool runs as its rests do: what it starts as, and
    -- what it gathers and steps to, are rests.
    pool-restful : ∀ {g m} (cr : Carried g m) {Δ′ A′ B′ op f fl oc k r pl} {so : Sub (Conf.world (Mach.conf m)) Δ′ A′}
                     {ls : List (Lane (Conf.world (Mach.conf m)) Δ′ B′)}
                 → Path (Carried.tree cr) (flatMapˢ op f fl oc k r pl so ls) → Restful pl

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

    -- An ended source's rest runs as rests do.
    rest-restful : ∀ {g m} (cr : Carried g m) {Δ′ A′ B′ S c b kb k fd rp e rt} {src : Sub (Conf.world (Mach.conf m)) Δ′ A′}
                     {bd : Sub (Conf.world (Mach.conf m)) (A′ ∷ Δ′) B′}
                 → Path (Carried.tree cr) (connectˢ S c b kb k fd rp e rt src bd) → ∀ {c₀} → e ≡ just c₀ → Restful rt

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
  torn-fed cr z = fed-lowers (site-lowers _ z) (Carried.tree cr) (Meaning.fed (Carried.meaning cr))

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
  torn-queue cr z = queue-lowers (site-lowers _ z) (Carried.queue cr)

  -- A site holds no part, a body's by `Owned.bodies`, so the tree's
  -- part is the same once its switch is thrown.
  torn-part : ∀ {g m} (cr : Carried g m) (z : Site (Carried.tree cr))
            → firstCall (Carried.ctlAs cr) ≡ just (siteCall z)
            → At.part (siteHeap (Conf.heap (Mach.conf m)) z) (Carried.tree cr) ≡ At.part (Conf.heap (Mach.conf m)) (Carried.tree cr)
  torn-part cr (takeSite π) _ = torn-take-part _ π (Books.fresh (Carried.books cr))
  torn-part {m = mach ⟨ _ , _ , _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = runAs (_ ∷ _) _ _ } (bodySite π) refl =
    torn-body-part _ π (Books.fresh (Carried.books cr)) (Owned.bodies (Carried.owned cr) π (here refl))

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
  postulate
    torn-lingers : ∀ {g m} (cr : Carried g m) (z : Site (Carried.tree cr))
                 → firstCall (Carried.ctlAs cr) ≡ just (siteCall z)
                 → Lingers (siteHeap (Conf.heap (Mach.conf m)) z) (Carried.tree cr)

  -- A cut: its kill switch thrown, what it holds unsubscribed; the ghost
  -- alike, a call fewer.
  cut-onward : ∀ {g m} (cr : Carried g m) (z : Site (Carried.tree cr))
             → firstCall (Carried.ctlAs cr) ≡ just (siteCall z) → Hops cr
  cut-onward {g} {mach ⟨ hp , p , _ ⟩ clk ts bs td lg en mk} cr@record { ctlAs = runAs (_ ∷ ks) e Kᴬ } z refl eq
    with tear-cut cr z {ks} e eq
  ... | act′ , e′ , path = g , _ , path
    , carried (record
        { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = Carried.tree cr ; ctlAs = runAs ks e′ Kᴬ
        ; meets = trans (torn-part cr z refl) (Carried.meets cr)
        ; owned = torn-owned hp z (Carried.owned cr)
        ; kernels = record { holds = torn-holds cr z ; gated = torn-gated cr z ; settled = Kernels.settled (Carried.kernels cr) }
        ; meaning = record { fed = torn-fed cr z }
        ; queue = torn-queue cr z
        ; books = record { fresh = Books.fresh (Carried.books cr) ; clocked = Books.clocked (Carried.books cr)
                         ; paidUp = Books.paidUp (Carried.books cr) ; running = Books.running (Carried.books cr) }
        ; sorted = hop-sorted cr eq path ; behind = torn-behind cr z refl ; lingers = torn-lingers cr z refl })
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

  -- A step's order against a position is its next event's.
  beforeᴹ : Pos → Maybe Pos → Bool
  beforeᴹ q nothing  = true
  beforeᴹ q (just k) = q <ᵖ k

  before-head : ∀ {Γ B} q (S : U.Step Γ B) → U.beforeˢ q S ≡ beforeᴹ q (U.headˢ S)
  before-head q (U.outˢ _ _ _) = refl
  before-head q (U.skipˢ _ _)  = refl
  before-head q (U.endˢ _)     = refl
  before-head q U.hushˢ        = refl

  shut-head : ∀ {Γ A B} {r c} {t : U.Node Γ A} (S : U.Step (A ∷ Γ) B) → U.headˢ (U.shutˢᵗ r c t S) ≡ U.headˢ S
  shut-head (U.outˢ _ _ _) = refl
  shut-head (U.skipˢ _ _)  = refl
  shut-head (U.endˢ _)     = refl
  shut-head U.hushˢ        = refl

  -- A sibling past `p` steps after the step under `p`.
  before-far : ∀ {p q Γ B} {b : U.Node Γ B} → Far p b → Under p q → U.beforeˢ q (U.step b) ≡ true
  before-far {b = b} fb u with U.step b in eb
  ... | U.outˢ _ _ _ = far-lt (Far.far-at fb (cong U.headˢ eb)) u
  ... | U.skipˢ _ _  = far-lt (Far.far-at fb (cong U.headˢ eb)) u
  ... | U.endˢ _     = far-lt (Far.far-at fb (cong U.headˢ eb)) u
  ... | U.hushˢ      = refl

  before-not : ∀ {p q Γ B} {S : U.Step Γ B} → Beyond p q → Below p S → U.beforeˢ (q ++ [ ix 0 ]) S ≡ false
  before-not {q = q} {S = U.outˢ k _ _} bq (below refl u) = <ᵖ-asym k (q ++ [ ix 0 ]) (<ᵖ-trans k q (q ++ [ ix 0 ]) (far-lt bq u) (<ᵖ-below q []))
  before-not {q = q} {S = U.skipˢ k _}  bq (below refl u) = <ᵖ-asym k (q ++ [ ix 0 ]) (<ᵖ-trans k q (q ++ [ ix 0 ]) (far-lt bq u) (<ᵖ-below q []))
  before-not {q = q} {S = U.endˢ k}     bq (below refl u) = <ᵖ-asym k (q ++ [ ix 0 ]) (<ᵖ-trans k q (q ++ [ ix 0 ]) (far-lt bq u) (<ᵖ-below q []))
  before-not {S = U.hushˢ} bq (below () _)

  source-first : ∀ {p Γ A B} {b : U.Node (A ∷ Γ) B} {S : U.Step Γ A} → Far p b → Below p S → SourceFirst S (U.step b)
  source-first {S = U.outˢ _ _ _} fb (below refl u) = before-far fb (under-++ [ ix 0 ] u)
  source-first {S = U.skipˢ _ _}  fb (below refl u) = before-far fb (under-++ [ ix 0 ] u)
  source-first {S = U.endˢ _}     fb (below refl u) = before-far fb (under-++ [ ix 0 ] u)
  source-first {S = U.hushˢ} fb (below () _)

  body-first : ∀ {p Γ A B} {c : U.Node Γ A} {S : U.Step (A ∷ Γ) B} → Far p c → Below p S → BodyFirst (U.step c) S
  body-first {c = c} fc b with U.step c in ec
  ... | U.outˢ _ _ _ = before-not (Far.far-at fc (cong U.headˢ ec)) b
  ... | U.skipˢ _ _  = before-not (Far.far-at fc (cong U.headˢ ec)) b
  ... | U.endˢ _     = before-not (Far.far-at fc (cong U.headˢ ec)) b
  ... | U.hushˢ      = tt

  body-step : ∀ {Γ A B} {r} {b : U.Node (A ∷ Γ) B} {sb} {s : U.Node Γ A} sc → BodyFirst sc sb → U.sourceˢ r b sb s sc ≡ U.bodyˢ r (U.live s) sb
  body-step (U.outˢ _ _ _) bf rewrite bf = refl
  body-step (U.skipˢ _ _)  bf rewrite bf = refl
  body-step (U.endˢ _)     bf rewrite bf = refl
  body-step U.hushˢ        _  = refl

  rest-behind : ∀ {p Γ A B} {t : U.Node Γ A} {S : U.Step (A ∷ Γ) B} → Far p t → Below p S → RestBehind t S
  rest-behind ft b et = before-not (Far.far-at ft (cong U.headˢ et)) b

  ended-shut : ∀ {Γ A B} {r c} {b : U.Node (A ∷ Γ) B} {t : U.Node Γ A} {X S : U.Step (A ∷ Γ) B} → RestBehind t S → U.headˢ X ≡ U.headˢ S
             → U.endedˢ r b X c t (U.step t) ≡ U.shutˢᵗ r c t X
  ended-shut {t = t} {X} {S} rb hx with U.step t in et
  ... | U.skipˢ k _ rewrite before-head (k ++ [ ix 0 ]) X | hx | sym (before-head (k ++ [ ix 0 ]) S) | rb refl = refl
  ... | U.outˢ _ _ _ = refl
  ... | U.endˢ _     = refl
  ... | U.hushˢ      = refl

  -- The earliest lane, read off the lanes.
  FarE : Pos → ∀ {Γ B} → U.Earliest Γ B → Set
  FarE p U.none                = ⊤
  FarE p (U.found k _ _ _ _)   = Beyond p k

  earliest-far : ∀ {p Γ B} (ls : List (U.Node Γ B)) → All (Far p) ls → FarE p (U.earliest ls)
  earliest-far []       []        = tt
  earliest-far (c ∷ ls) (fc ∷ fs) with U.headˢ (U.step c) in hc | U.earliest ls | earliest-far ls fs
  ... | nothing | U.none               | _ = tt
  ... | nothing | U.found _ _ _ _ _    | f = f
  ... | just k  | U.none               | _ = Far.far-at fc hc
  ... | just k  | U.found k′ _ _ _ _   | f with k <ᵖ k′
  ...   | true  = Far.far-at fc hc
  ...   | false = f

  earliest-split : ∀ {Γ B} (ls : List (U.Node Γ B)) {k bs l s as} → U.earliest ls ≡ U.found k bs l s as → bs ++ l ∷ as ≡ ls
  earliest-split []       ()
  earliest-split (c ∷ ls) e with U.headˢ (U.step c) | U.earliest ls in ee
  ... | nothing | U.none = ⊥-elim (none≢ e)
    where none≢ : ∀ {Γ B} {k bs l s as} → U.none {Γ} {B} ≡ U.found k bs l s as → ⊥
          none≢ ()
  ... | nothing | U.found _ _ _ _ _ with e
  ...   | refl = cong (c ∷_) (earliest-split ls ee)
  earliest-split (c ∷ ls) refl | just k | U.none = refl
  earliest-split (c ∷ ls) e | just k | U.found k′ _ _ _ _ with k <ᵖ k′ | e
  ...   | true  | refl = refl
  ...   | false | refl = cong (c ∷_) (earliest-split ls ee)

  earliest-found : ∀ {p Γ B} {bs : List (U.Node Γ B)} {l as k} → All (Far p) bs → All (Far p) as → U.headˢ (U.step l) ≡ just k → Under p k
                 → U.earliest (bs ++ l ∷ as) ≡ U.found k bs l (U.step l) as
  earliest-found {as = as} [] fas hl u rewrite hl with U.earliest as | earliest-far as fas
  ... | U.none                | _  = refl
  ... | U.found k′ _ _ _ _    | bk rewrite far-lt bk u = refl
  earliest-found {bs = b ∷ bs} {l} {as} (fb ∷ fbs) fas hl u with U.headˢ (U.step b) in hb
  ... | nothing = cong (U.pick b (U.step b) (bs ++ l ∷ as) nothing) (earliest-found fbs fas hl u)
  ... | just kb = trans (cong (U.pick b (U.step b) (bs ++ l ∷ as) (just kb)) (earliest-found fbs fas hl u)) (pick-past (far-gt (Far.far-at fb hb) u))
    where pick-past : ∀ {k} → kb <ᵖ k ≡ false → U.pick b (U.step b) (bs ++ l ∷ as) (just kb) (U.found k bs l (U.step l) as) ≡ U.found k (b ∷ bs) l (U.step l) as
          pick-past e rewrite e = refl

  outer-first : ∀ {p Γ A B} {S : U.Step Γ A} {ls : List (U.Node Γ B)} → Below p S → All (Far p) ls → OuterFirst S ls
  outer-first {p} {ls = ls} (below {k′} hk u) fs ee = k′ , hk , far-lt (subst (FarE p) ee (earliest-far ls fs)) u

  lane-first : ∀ {p Γ A} {o : Maybe (U.Node Γ A)} {q} → Opt (Far p) o → Under p q → LaneFirst o q
  lane-first {o = nothing} _  _ = tt
  lane-first {o = just o}  fo u ho = far-gt (Far.far-at fo ho) u

  pool-outer : ∀ {p Γ A B} {pl : U.Node Γ B} {o₀ : U.Node Γ A} {S} {E : U.Earliest Γ B} → Far p pl → Below p S → PoolBehind pl (U.runᵒ o₀ S) E
  pool-outer {E = U.none}              fp (below hS u) ep rewrite hS = far-gt (Far.far-at fp (cong U.headˢ ep)) u
  pool-outer {E = U.found _ _ _ _ _}   fp (below hS u) ep rewrite hS | far-gt (Far.far-at fp (cong U.headˢ ep)) u = refl

  pool-lane : ∀ {p Γ A B} {pl : U.Node Γ B} {o : Maybe (U.Node Γ A)} {q bs l S as} → Far p pl → Under p q
            → PoolBehind pl (U.outerOf o) (U.found q bs l S as)
  pool-lane {o = nothing} fp u ep = far-gt (Far.far-at fp (cong U.headˢ ep)) u
  pool-lane {o = just _}  fp u ep rewrite far-gt (Far.far-at fp (cong U.headˢ ep)) u = ∧-zeroʳ _

  -- A flatMap's step is its outer's, or a lane's, by the side conditions.
  flat-outer : ∀ {Γ A B} {op} {g : A → Pos → U.Node Γ B} {o₀ : U.Node Γ A} {S} {LS qs pl}
             → PoolBehind pl (U.runᵒ o₀ S) (U.earliest LS) → OuterFirst S LS
             → U.flatˢ op g (U.runᵒ o₀ S) LS qs pl (U.step pl) (U.earliest LS) ≡ U.outerˢ op g o₀ S LS qs pl
  flat-outer {op = op} {g} {o₀} {S} {LS} {qs} {pl} pb of with U.step pl in ep
  ... | U.skipˢ _ _  rewrite pb refl = go
    where go : U.goˢ op g (U.runᵒ o₀ S) LS qs pl (U.earliest LS) ≡ U.outerˢ op g o₀ S LS qs pl
          go with U.earliest LS in ee
          ... | U.none = refl
          ... | U.found k bs l s as with of refl
          ...   | k′ , hk , lt rewrite hk | lt | earliest-split LS ee = refl
  ... | U.outˢ _ _ _ = go
    where go : U.goˢ op g (U.runᵒ o₀ S) LS qs pl (U.earliest LS) ≡ U.outerˢ op g o₀ S LS qs pl
          go with U.earliest LS in ee
          ... | U.none = refl
          ... | U.found k bs l s as with of refl
          ...   | k′ , hk , lt rewrite hk | lt | earliest-split LS ee = refl
  ... | U.endˢ _     = go
    where go : U.goˢ op g (U.runᵒ o₀ S) LS qs pl (U.earliest LS) ≡ U.outerˢ op g o₀ S LS qs pl
          go with U.earliest LS in ee
          ... | U.none = refl
          ... | U.found k bs l s as with of refl
          ...   | k′ , hk , lt rewrite hk | lt | earliest-split LS ee = refl
  ... | U.hushˢ      = go
    where go : U.goˢ op g (U.runᵒ o₀ S) LS qs pl (U.earliest LS) ≡ U.outerˢ op g o₀ S LS qs pl
          go with U.earliest LS in ee
          ... | U.none = refl
          ... | U.found k bs l s as with of refl
          ...   | k′ , hk , lt rewrite hk | lt | earliest-split LS ee = refl

  go-lane : ∀ {Γ A B} {op} {g : A → Pos → U.Node Γ B} (o : Maybe (U.Node Γ A)) {LS qs pl k bs l S as} → LaneFirst o k
          → U.goˢ op g (U.outerOf o) LS qs pl (U.found k bs l S as) ≡ U.laneˢ op g o bs l S as qs pl
  go-lane nothing  _ = refl
  go-lane (just o) lf with U.headˢ (U.step o) in ho
  ... | nothing = refl
  ... | just k′ rewrite lf refl = refl

  flat-lane : ∀ {Γ A B} {op} {g : A → Pos → U.Node Γ B} {o : Maybe (U.Node Γ A)} {LS qs pl k bs l S as}
            → U.earliest LS ≡ U.found k bs l S as → PoolBehind pl (U.outerOf o) (U.found k bs l S as) → LaneFirst o k
            → U.flatˢ op g (U.outerOf o) LS qs pl (U.step pl) (U.earliest LS) ≡ U.laneˢ op g o bs l S as qs pl
  flat-lane {o = o} {pl = pl} ea pb lf rewrite ea with U.step pl in ep
  ... | U.skipˢ _ _  rewrite pb refl = go-lane o lf
  ... | U.outˢ _ _ _ = go-lane o lf
  ... | U.endˢ _     = go-lane o lf
  ... | U.hushˢ      = go-lane o lf

  -- A maybe, split without abstracting it from the goal.
  data Peek {ℓ} {X : Set ℓ} (x : Maybe X) : Set ℓ where
    peek-nothing : x ≡ nothing → Peek x
    peek-just    : ∀ {y} → x ≡ just y → Peek x

  peek : ∀ {ℓ} {X : Set ℓ} (x : Maybe X) → Peek x
  peek nothing  = peek-nothing refl
  peek (just _) = peek-just refl

  module _ {g m} (cr : Carried g m) where
    private
      W = Conf.world (Mach.conf m)
      H = Conf.heap (Mach.conf m)

    lanes-cons : ∀ {Δ B} (l : Lane W Δ B) (ls : List (Lane W Δ B)) → At.partLanes H (l ∷ ls) ≡ At.partLanes H (l ∷ []) ++ At.partLanes H ls
    lanes-cons (lane c k s) ls with At.val H (Kit.live c)
    ... | false = refl
    ... | true with At.part H s
    ...   | nothing = refl
    ...   | just _  = refl

    held-flat : ∀ {Δ A B} {op f fl oc k r pl} {so : Sub W Δ A} {ls : List (Lane W Δ B)} {o₀}
              → At.part H so ≡ just o₀
              → At.part H (flatMapˢ op f fl oc k r pl so ls)
                ≡ just (U.flatMapᶜ op (λ a q → U.subscribe (f a) q) (just o₀) (At.partLanes H ls) (At.val H (FlatKit.Flat.queue fl)) pl)
    held-flat po rewrite po = refl

    held-lanes : ∀ {Δ A B} {op f fl oc k r pl} {so : Sub W Δ A} {ls : List (Lane W Δ B)} {bs l as}
               → At.partLanes H ls ≡ bs ++ l ∷ as
               → At.part H (flatMapˢ op f fl oc k r pl so ls)
                 ≡ just (U.flatMapᶜ op (λ a q → U.subscribe (f a) q) (At.part H so) (At.partLanes H ls) (At.val H (FlatKit.Flat.queue fl)) pl)
    held-lanes {so = so} {bs = bs} eq rewrite eq with At.part H so
    ... | just _ = refl
    ... | nothing with bs
    ...   | []    = refl
    ...   | _ ∷ _ = refl

    held-src : ∀ {Δ A B Sj c b kb k fd rp e rt} {src : Sub W Δ A} {bd : Sub W (A ∷ Δ) B} {c₀ b₀}
             → At.part H src ≡ just c₀ → At.part H bd ≡ just b₀
             → At.part H (connectˢ Sj c b kb k fd rp e rt src bd) ≡ just (U.connectᶜ rp b₀ (U.live c₀))
    held-src ps pb rewrite ps | pb = refl

    held-shut : ∀ {Δ A B Sj c b kb k fd rp c₁ rt} {src : Sub W Δ A} {bd : Sub W (A ∷ Δ) B} {b₀}
              → At.part H src ≡ nothing → At.part H bd ≡ just b₀
              → At.part H (connectˢ Sj c b kb k fd rp (just c₁) rt src bd) ≡ just (U.connectᶜ rp (U.shut (Any.here refl) c₁ b₀) (U.ended c₁ rt))
    held-shut ps pb rewrite ps | pb = refl

    -- A step of a part the ghost holds, its next event under `p`, lifted
    -- up a path every sibling of which waits: the ghost's part there, its
    -- step the part's lifted, and its next event under `p`.
    mutual
      lift-up : ∀ {Δ A} {t : Sub W Δ A} (ρ₀ : Path (Carried.tree cr) t) {Δ′ A′ p} {v : Sub W Δ′ A′} {c₀} (π : Path t v)
                {Δ″ A″ i x xs} (τ : Path v (ofˢ {Δ = Δ″} {A″} p i (x ∷ xs)))
              → At.part H v ≡ just c₀ → Below p (U.step c₀) → seen H π ≡ true → Clear H (Far p) π
              → Σ (U.Node Δ A) λ c → At.part H t ≡ just c × Lifts H π (U.step c₀) (U.step c) × Below p (U.step c)
      lift-up ρ₀ here τ pv bv sn cl = _ , pv , lifts-here , bv
      lift-up ρ₀ (in-map {f = f} ρ) τ pv bv sn cl with lift-up (ρ₀ ⊕ in-map here) ρ τ pv bv sn cl
      ... | c , pc , L , b rewrite pc = U.mapᶜ f c , refl , lifts-map L , below-map b
      lift-up ρ₀ (in-scan {f = f} {r} ρ) τ pv bv sn cl with lift-up (ρ₀ ⊕ in-scan here) ρ τ pv bv sn cl
      ... | c , pc , L , b rewrite pc = U.scanᶜ f (At.val H r) c , refl , lifts-scan L , below-scan b
      lift-up ρ₀ (in-take {i = i} {q} {c} {tk = taking} ρ) τ pv bv sn cl with At.val H (Kit.live c) in lv
      lift-up ρ₀ (in-take {tk = taking} ρ) τ pv bv () cl | false
      ... | true with lift-up (ρ₀ ⊕ in-take here) ρ τ pv bv sn cl
      ...   | c′ , pc , L , b rewrite pc = U.takeWhileᶜ i q c′ , refl , lifts-take lv L , below-take i q b
      lift-up ρ₀ (in-take {c = c} {tk = endingᵗ _ _} ρ) τ pv bv sn cl with At.val H (Kit.live c)
      lift-up ρ₀ (in-take {tk = endingᵗ _ _} ρ) τ pv bv () cl | false
      lift-up ρ₀ (in-take {tk = endingᵗ _ _} ρ) τ pv bv () cl | true
      lift-up ρ₀ (in-take {c = c} {tk = taken} ρ) τ pv bv sn cl with At.val H (Kit.live c)
      lift-up ρ₀ (in-take {tk = taken} ρ) τ pv bv () cl | false
      lift-up ρ₀ (in-take {tk = taken} ρ) τ pv bv () cl | true
      lift-up ρ₀ (in-outer {Δ = Δf} {A = Af} {B = Bf} {op = op} {f = f} {fl = fl} {oc = oc} {k = k} {r = r} {pl = pl} {t = so} {ls = ls} ρ) τ pv bv sn (fl′ , pd , cl) with lift-up (ρ₀ ⊕ in-outer here) ρ τ pv bv sn cl
      ... | o₀ , po , L , b =
        _ , hp , subst (Lifts H (in-outer {op = op} {f = f} {fl = fl} {oc = oc} {k = k} {r = r} {pl = pl} {t = so} {ls = ls} ρ) _) (sym st) (lifts-outer (outer-first b fl′) (pool-outer {o₀ = o₀} {E = U.earliest (At.partLanes H ls)} fp b) L) ,
        subst (Below _) (sym st) (below-outer b)
        where hp = held-flat {Δ = Δf} {A = Af} {B = Bf} {op = op} {f = f} {fl = fl} {oc = oc} {k = k} {r = r} {pl = pl} {so = so} {ls = ls} po
              fp = pd hp
              st = flat-outer {op = op} {LS = At.partLanes H ls} {qs = At.val H (FlatKit.Flat.queue fl)} {pl = pl} (pool-outer {o₀ = o₀} {E = U.earliest (At.partLanes H ls)} fp b) (outer-first b fl′)
      lift-up ρ₀ (in-lanes {Δ = Δf} {A = Af} {B = Bf} {op = op} {f = f} {fl = fl} {oc = oc} {k = k} {r = r} {pl = pl} {t = so} {ls = ls} πL) τ pv bv sn (fo , pd , cl) with lift-up-lanes (λ πL′ → ρ₀ ⊕ in-lanes πL′) πL τ pv bv sn cl
      ... | bs , l , as , eq , LL , fbs , fas , below {q} hq u =
        _ , hp , subst (Lifts H (in-lanes {op = op} {f = f} {fl = fl} {oc = oc} {k = k} {r = r} {pl = pl} {t = so} {ls = ls} πL) _) (sym st) (lifts-lanes LL (earliest-found fbs fas hq u) (lane-first fo u) (pool-lane {o = At.part H so} {bs = bs} {l = l} {S = U.step l} {as = as} fp u)) ,
        subst (Below _) (sym st) (below-lane (below hq u))
        where hp = held-lanes {Δ = Δf} {A = Af} {B = Bf} {op = op} {f = f} {fl = fl} {oc = oc} {k = k} {r = r} {pl = pl} {so = so} {ls = ls} eq
              fp = pd hp
              ea : U.earliest (At.partLanes H ls) ≡ U.found q bs l (U.step l) as
              ea = trans (cong U.earliest eq) (earliest-found fbs fas hq u)
              st = flat-lane {op = op} {o = At.part H so} {LS = At.partLanes H ls} {qs = At.val H (FlatKit.Flat.queue fl)} ea (pool-lane {o = At.part H so} {bs = bs} {l = l} {S = U.step l} {as = as} fp u) (lane-first fo u)
      lift-up ρ₀ (in-source {S = Sj} {c = cj} {b = bj} {kb = kbj} {k = kj} {fd = fdj} {e = ej} {rp = rpj} {rt = rtj} {t = src} {bd = bd} ρ) τ pv bv sn (fb , cl) with peek (At.part H bd)
      ... | peek-nothing pb = ⊥-elim (true≢false (sym (subst (λ z → is-just z ∧ seen H ρ ≡ true) pb sn)))
      ... | peek-just pb with lift-up (ρ₀ ⊕ in-source here) ρ τ pv bv (subst (λ z → is-just z ∧ seen H ρ ≡ true) pb sn) cl
      ...   | c₀ , pc , L , b = _ , held-src {Sj = Sj} {c = cj} {b = bj} {kb = kbj} {k = kj} {fd = fdj} {rp = rpj} {e = ej} {rt = rtj} {src = src} {bd = bd} pc pb , lifts-source pb (source-first fb′ b) L , below-source (source-first fb′ b) b
        where fb′ = subst (Opt (Far _)) pb fb
      lift-up ρ₀ (in-body {S = Sj} {c = cj} {b = bj} {kb = kbj} {k = kj} {fd = fdj} {e = nothing} {rp = rpj} {rt = rtj} {t = src} {bd = bd} ρ) τ pv bv sn (fc , rd , cl) with peek (At.part H src)
      ... | peek-nothing ps = ⊥-elim (true≢false (sym (subst (λ z → (is-just z ∨ false) ∧ seen H ρ ≡ true) ps sn)))
      ... | peek-just {c₀} ps with lift-up (ρ₀ ⊕ in-body here) ρ τ pv bv (subst (λ z → (is-just z ∨ false) ∧ seen H ρ ≡ true) ps sn) cl
      ...   | b₀ , pb , L , b =
        _ , held-src {Sj = Sj} {c = cj} {b = bj} {kb = kbj} {k = kj} {fd = fdj} {rp = rpj} {rt = rtj} {src = src} {bd = bd} ps pb , subst (Lifts H _ _) (sym st) (lifts-body ps (body-first fc′ b) L) , subst (Below _) (sym st) (below-body b)
        where fc′ = subst (Opt (Far _)) ps fc
              st = body-step (U.step c₀) (body-first fc′ b)
      lift-up ρ₀ (in-body {S = Sj} {c = cj} {b = bj} {kb = kbj} {k = kj} {fd = fdj} {e = just c₁} {rp = rpj} {rt = rtj} {t = src} {bd = bd} ρ) τ pv bv sn (fc , rd , cl) with peek (At.part H src)
      ... | peek-just {c₀} ps with lift-up (ρ₀ ⊕ in-body here) ρ τ pv bv (subst (λ z → (is-just z ∨ true) ∧ seen H ρ ≡ true) ps sn) cl
      ...   | b₀ , pb , L , b =
        _ , held-src {Sj = Sj} {c = cj} {b = bj} {kb = kbj} {k = kj} {fd = fdj} {rp = rpj} {rt = rtj} {src = src} {bd = bd} ps pb , subst (Lifts H _ _) (sym st) (lifts-body ps (body-first fc′ b) L) , subst (Below _) (sym st) (below-body b)
        where fc′ = subst (Opt (Far _)) ps fc
              st = body-step (U.step c₀) (body-first fc′ b)
      lift-up ρ₀ (in-body {S = Sj} {c = cj} {b = bj} {kb = kbj} {k = kj} {fd = fdj} {e = just c₁} {rp = rpj} {rt = rtj} {t = src} {bd = bd} ρ) τ pv bv sn (fc , rd , cl) | peek-nothing ps
        with lift-up (ρ₀ ⊕ in-body here) ρ τ pv bv (subst (λ z → (is-just z ∨ true) ∧ seen H ρ ≡ true) ps sn) cl
      ...   | b₀ , pb , L , b =
        _ , held-shut {Sj = Sj} {c = cj} {b = bj} {kb = kbj} {k = kj} {fd = fdj} {rp = rpj} {rt = rtj} {src = src} {bd = bd} ps pb , subst (Lifts H _ _) (sym st) (lifts-shut ps refl rb L) , subst (Below _) (sym st) (below-shut b)
        where fr = rd (held-shut {Sj = Sj} {c = cj} {b = bj} {kb = kbj} {k = kj} {fd = fdj} {rp = rpj} {rt = rtj} {src = src} {bd = bd} ps pb) ps refl
              rb = rest-behind fr b
              sh = shut-step cr ρ₀ (ρ ⊕ τ) ps refl pb
              hx = trans (sym (shut-head (U.step (U.shut (Any.here refl) c₁ b₀)))) (trans (cong U.headˢ sh) (shut-head (U.step b₀)))
              st = trans (ended-shut rb hx) sh
      lift-up ρ₀ (in-defer ρ) τ pv bv sn cl with lift-up (ρ₀ ⊕ in-defer here) ρ τ pv bv sn cl
      ... | c , pc , L , b = c , pc , lifts-defer L , b

      lift-up-lanes : ∀ {Δ B} {ls : List (Lane W Δ B)} (κ : ∀ {Δ″ A″} {w : Sub W Δ″ A″} → PathLanes ls w → Path (Carried.tree cr) w)
                      {Δ′ A′ p} {v : Sub W Δ′ A′} {c₀} (πL : PathLanes ls v)
                      {Δ″ A″ i x xs} (τ : Path v (ofˢ {Δ = Δ″} {A″} p i (x ∷ xs)))
                    → At.part H v ≡ just c₀ → Below p (U.step c₀) → seenL H πL ≡ true → ClearL H (Far p) πL
                    → Σ (List (U.Node Δ B)) λ bs → Σ (U.Node Δ B) λ l → Σ (List (U.Node Δ B)) λ as
                      → At.partLanes H ls ≡ bs ++ l ∷ as × LiftsLane H πL (U.step c₀) bs (U.step l) as
                        × All (Far p) bs × All (Far p) as × Below p (U.step l)
      lift-up-lanes κ (this-lane {c = c} {ls = ls} ρ) τ pv bv sn (fas , cl) with At.val H (Kit.live c) in lv
      lift-up-lanes κ (this-lane ρ) τ pv bv () (fas , cl) | false
      ... | true with lift-up (κ (this-lane here)) ρ τ pv bv sn cl
      ...   | c′ , pc , L , b rewrite pc = [] , c′ , At.partLanes H ls , refl , lifts-this lv L , [] , fas , b
      lift-up-lanes κ (next-lane {l = l} {ls} πL) τ pv bv sn (fl , cl) with lift-up-lanes (λ πL′ → κ (next-lane πL′)) πL τ pv bv sn cl
      ... | bs , l′ , as , eq , LL , fbs , fas , b =
        At.partLanes H (l ∷ []) ++ bs , l′ , as ,
        trans (lanes-cons l ls) (trans (cong (At.partLanes H (l ∷ []) ++_) eq) (sym (++-assoc (At.partLanes H (l ∷ [])) bs (l′ ∷ as)))) ,
        lifts-next LL , all-++⁺ fl fbs , fas , b

  -- The ghost's step, from a path every sibling of which waits: the
  -- `of`'s step lifted, each operator's side condition read off `Clear`.
  heads-lift : ∀ {g m} (cr : Carried g m) {Δ A p i x xs} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i (x ∷ xs)))
             → seen (Conf.heap (Mach.conf m)) π ≡ true → Clear (Conf.heap (Mach.conf m)) (Far p) π
             → Σ (U.Node [] R) λ c → At.part (Conf.heap (Mach.conf m)) (Carried.tree cr) ≡ just c
               × Lifts (Conf.heap (Mach.conf m)) π (U.step (U.ofᶜ p i (x ∷ xs))) (U.step c)
  heads-lift cr {i = i} π sn cl with lift-up cr here π here refl (below refl ([ ix i ] , refl)) sn cl
  ... | c , pc , L , _ = c , pc , L

  -- An agenda under way: the ghost is the tree's part.
  run-meets : ∀ {h} {t : Sub h [] R} {p c bs} (ca : CtlAs t p c bs) {n g k} → firstCall ca ≡ just k → Meets ca n g → n ≡ just g
  run-meets (runAs (_ ∷ _) _ _) refl mt = mt
  run-meets (runAs [] _ _)      ()
  run-meets calmAs              ()
  run-meets (noteAs _ _ _)      ()
  run-meets (subAs _ _ _ _)     ()
  run-meets (burstAs _ _ _)     ()

  -- The agenda's first call an `of` at `p`: the run is at `p`.
  run-at : ∀ {h} {t : Sub h [] R} {q c bs} (ca : CtlAs t q c bs) {Δ A p i xs} {π : Path t (ofˢ {Δ = Δ} {A} p i xs)}
         → firstCall ca ≡ just (emitC π) → All (Placedᴬ t) (agenda t ca) → q ≡ p
  run-at (runAs (_ ∷ _) _ _) refl (pl ∷ _) = pl
  run-at (runAs [] _ _)      ()
  run-at calmAs              ()
  run-at (noteAs _ _ _)      ()
  run-at (subAs _ _ _ _)     ()
  run-at (burstAs _ _ _)     ()

  -- At a pool over a hidden `of`: the pool's own next event a pin under
  -- the run, as it is tied to what its ended parts left running.
  pl-pin : ∀ {g m} (cr : Carried g m) {Δ A p i x xs} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i (x ∷ xs)))
            → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → opened (Conf.heap (Mach.conf m)) true π ≡ true
            → seen (Conf.heap (Mach.conf m)) π ≡ false
            → ∀ {Δ′ A′ B′ op f fl oc k r pl} {so : Sub (Conf.world (Mach.conf m)) Δ′ A′} {ls : List (Lane (Conf.world (Mach.conf m)) Δ′ B′)}
                (ψ : Path (Carried.tree cr) (flatMapˢ op f fl oc k r pl so ls)) (σ : Path (flatMapˢ op f fl oc k r pl so ls) _) → ψ ⊕ σ ≡ π
            → seen (Conf.heap (Mach.conf m)) ψ ≡ true → ∀ {c} → At.part (Conf.heap (Mach.conf m)) (flatMapˢ op f fl oc k r pl so ls) ≡ just c
            → Σ Pos λ q → Σ (U.Node Δ′ B′) λ pl′ → U.step pl ≡ U.skipˢ q pl′ × Under p q
  pl-pin {m = m} cr π fc op sn {fl = fl} {pl = pl} {so = so} {ls = ls} ψ σ e se pt with pooled-pin cr π fc op sn ψ σ e se pt
  ... | q , y′ , ey , u with tied-skip {x = pl} {y = At.pooled (Conf.heap (Mach.conf m)) fl so ls} (Ties.pools (Lingers.rooted (Carried.lingers cr)) ψ se pt) ey
  ... | _ , ex with pinned-skip (pinned-trans (restful-pinned (pool-restful cr ψ)) (rest-pinned pl)) ex
  ... | pl′ , es = q , pl′ , es , u

  under-snoc : ∀ {p q} j → Under p q → Under p (q ++ [ j ])
  under-snoc {p} j (y , refl) = y ++ [ j ] , ++-assoc p y [ j ]

  -- A held connect past its source's end: its body shut there.
  ended-just : ∀ {h H Δ A B} r c t (mb : Maybe (U.Node (A ∷ Δ) B)) {n} → At.connected {h} H r (just c) t nothing mb ≡ just n
             → Σ (U.Node (A ∷ Δ) B) λ bo → mb ≡ just bo × U.connectᶜ r (U.shut (Any.here refl) c bo) (U.ended c t) ≡ n
  ended-just r c t nothing  ()
  ended-just r c t (just bo) refl = bo , refl , refl

  -- Its rest's skip ahead of the body: the connect's next event.
  ended-skip : ∀ {Γ A B} r (bo : U.Node (A ∷ Γ) B) c (t : U.Node Γ A) {k t′} → U.step t ≡ U.skipˢ k t′ → U.beforeˢ (k ++ [ ix 0 ]) (U.step bo) ≡ true
             → U.endedˢ r bo (U.step bo) c t (U.step t) ≡ U.skipˢ (k ++ [ ix 0 ]) (U.connectᶜ r bo (U.ended c t′))
  ended-skip r bo c t et bb rewrite et | bb = refl

  -- At an ended source over a hidden `of`: the connect's next event its
  -- rest's pin under the run, as the rest is tied to what the source
  -- left running.
  rest-pin : ∀ {g m} (cr : Carried g m) {Δ A p i x xs} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i (x ∷ xs)))
            → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → opened (Conf.heap (Mach.conf m)) true π ≡ true
            → seen (Conf.heap (Mach.conf m)) π ≡ false
            → ∀ {Δ′ A′ B′ S c b kb k fd rp e rt} {src : Sub (Conf.world (Mach.conf m)) Δ′ A′} {bd : Sub (Conf.world (Mach.conf m)) (A′ ∷ Δ′) B′}
                (ψ : Path (Carried.tree cr) (connectˢ S c b kb k fd rp e rt src bd)) (σ : Path src _) → ψ ⊕ in-source σ ≡ π
            → seen (Conf.heap (Mach.conf m)) ψ ≡ true → ∀ {n} → At.part (Conf.heap (Mach.conf m)) (connectˢ S c b kb k fd rp e rt src bd) ≡ just n
            → At.part (Conf.heap (Mach.conf m)) src ≡ nothing → ∀ {c₀} → e ≡ just c₀
            → Σ Pos λ q → Σ (U.Node Δ′ B′) λ n′ → U.step n ≡ U.skipˢ q n′ × Under p q
  rest-pin {m = m} cr π fc op sn {rp = rp} {rt = rt} {src = src} {bd = bd} ψ σ eq se {n} pt ps {c₀} refl
    with left-pin cr π fc op sn ψ σ eq se pt ps refl
  ... | q , y′ , ey , u
    with tied-skip {x = rt} {y = At.leftover (Conf.heap (Mach.conf m)) {B = ⊤} src} (Ties.rests (Lingers.rooted (Carried.lingers cr)) ψ se pt ps refl) ey
  ... | _ , ex
    with pinned-skip (pinned-trans (restful-pinned (rest-restful cr ψ refl)) (rest-pinned rt)) ex
  ... | rt′ , er
    with ended-just {H = Conf.heap (Mach.conf m)} rp c₀ rt (At.part (Conf.heap (Mach.conf m)) bd)
           (subst (λ s → At.connected (Conf.heap (Mach.conf m)) rp (just c₀) rt s (At.part (Conf.heap (Mach.conf m)) bd) ≡ just n) ps pt)
  ... | bo , pb , en =
    q ++ [ ix 0 ] , _ ,
    trans (cong U.step (sym en)) (ended-skip rp (U.shut (Any.here refl) c₀ bo) c₀ rt er (rest-body cr π fc op sn ψ σ eq se pt ps refl pb u)) ,
    under-snoc (ix 0) u

  -- A held flatMap's part is its merge.
  merged-just : ∀ {h H Δ A B} op (g : A → Pos → U.Node Δ B) o ls qs pl {c} → At.merged {h} H op g o ls qs pl ≡ just c → U.flatMapᶜ op g o ls qs pl ≡ c
  merged-just op g nothing  []      []      pl ()
  merged-just op g nothing  []      (_ ∷ _) pl refl = refl
  merged-just op g nothing  (_ ∷ _) qs      pl refl = refl
  merged-just op g (just _) ls      qs      pl refl = refl

  -- A pool's skip ahead of all else: the flatMap's next event.
  flat-skip : ∀ {Γ A B} op (g : A → Pos → U.Node Γ B) o ls qs p {q p′} → U.step p ≡ U.skipˢ q p′ → U.aheadˢ q o (U.earliest ls) ≡ true
            → U.flatˢ op g o ls qs p (U.step p) (U.earliest ls) ≡ U.skipˢ q (U.flatMapᶜ op g (U.nodeᵒ o) ls qs p′)
  flat-skip op g o ls qs p ep ah rewrite ep | ah = refl

  -- A pin under `p` comes before every part beyond `p`.
  clear-far : ∀ {p q} (s : Maybe Pos) → (∀ {k} → s ≡ just k → Beyond p k) → Under p q → U.clearˢ q s ≡ true
  clear-far nothing  f u = refl
  clear-far (just k) f u = far-lt (f refl) u

  ahead-far : ∀ {p Γ A B} (o : Maybe (U.Node Γ A)) (ls : List (U.Node Γ B)) {q} → Opt (Far p) o → All (Far p) ls → Under p q
            → U.aheadˢ q (U.outerOf o) (U.earliest ls) ≡ true
  ahead-far nothing  ls fo fs u with U.earliest ls | earliest-far ls fs
  ... | U.none               | _ = refl
  ... | U.found _ _ _ _ _    | b = far-lt b u
  ahead-far (just c) ls fo fs u with U.earliest ls | earliest-far ls fs
  ... | U.none               | _ = clear-far (U.headˢ (U.step c)) (Far.far-at fo) u
  ... | U.found _ _ _ _ _    | b = cong₂ _∧_ (clear-far (U.headˢ (U.step c)) (Far.far-at fo) u) (far-lt b u)

  -- At a pool: its pin ahead of the flatMap's outer and every lane it
  -- holds, each no earlier than the run and not under it.
  pool-ahead : ∀ {g m} (cr : Carried g m) {Δ A p i x xs} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i (x ∷ xs)))
            → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → opened (Conf.heap (Mach.conf m)) true π ≡ true
            → seen (Conf.heap (Mach.conf m)) π ≡ false
            → ∀ {Δ′ A′ B′ op f fl oc k r pl} {so : Sub (Conf.world (Mach.conf m)) Δ′ A′} {ls : List (Lane (Conf.world (Mach.conf m)) Δ′ B′)}
                (ψ : Path (Carried.tree cr) (flatMapˢ op f fl oc k r pl so ls)) (σ : Path (flatMapˢ op f fl oc k r pl so ls) _) → ψ ⊕ σ ≡ π
            → seen (Conf.heap (Mach.conf m)) ψ ≡ true → ∀ {c} → At.part (Conf.heap (Mach.conf m)) (flatMapˢ op f fl oc k r pl so ls) ≡ just c
            → ∀ {q pl′} → U.step pl ≡ U.skipˢ q pl′ → Under p q
            → U.aheadˢ q (U.outerOf (At.part (Conf.heap (Mach.conf m)) so)) (U.earliest (At.partLanes (Conf.heap (Mach.conf m)) ls)) ≡ true
  pool-ahead {m = m} cr {p = p} π fc op sn {so = so} {ls = ls} ψ σ e se pt ep un with pool-off cr π fc op sn ψ σ e se pt
  ... | oo , ol =
    ahead-far O (At.partLanes (Conf.heap (Mach.conf m)) ls)
      (opt-zip {P = Heads p} {Q = Off p} {R′ = Far p} (λ {Γ} {A} {c} → far-apart {p} {Γ} {A} {c}) O (opt-each {H = Conf.heap (Mach.conf m)} {P = Heads p} O (Each.parts ev (in-outer here) refl)) oo)
      (all-zip {P = Heads p} {Q = Off p} {R′ = Far p} (λ {Γ} {A} {c} → far-apart {p} {Γ} {A} {c}) (each-lanes {H = Conf.heap (Mach.conf m)} {P = Heads p} ls (λ πL sL → Each.parts ev (in-lanes πL) sL)) ol) un
    where O  = At.part (Conf.heap (Mach.conf m)) so
          ev = each-sub (subst (λ q′ → Each (Conf.heap (Mach.conf m)) (Heads q′) (Carried.tree cr))
                               (run-at (Carried.ctlAs cr) fc (Owned.placed (Carried.owned cr))) (Carried.behind cr)) ψ se

  -- At a pool: the flatMap's next event the pool's pin.
  pool-pin : ∀ {g m} (cr : Carried g m) {Δ A p i x xs} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i (x ∷ xs)))
            → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → opened (Conf.heap (Mach.conf m)) true π ≡ true
            → seen (Conf.heap (Mach.conf m)) π ≡ false
            → ∀ {Δ′ A′ B′ op f fl oc k r pl} {so : Sub (Conf.world (Mach.conf m)) Δ′ A′} {ls : List (Lane (Conf.world (Mach.conf m)) Δ′ B′)}
                (ψ : Path (Carried.tree cr) (flatMapˢ op f fl oc k r pl so ls)) (σ : Path (flatMapˢ op f fl oc k r pl so ls) _) → ψ ⊕ σ ≡ π
            → seen (Conf.heap (Mach.conf m)) ψ ≡ true → ∀ {c} → At.part (Conf.heap (Mach.conf m)) (flatMapˢ op f fl oc k r pl so ls) ≡ just c
            → Σ Pos λ q → Σ (U.Node Δ′ B′) λ c′ → U.step c ≡ U.skipˢ q c′ × Under p q
  pool-pin {m = m} cr π fc op sn {op = fo} {f = f} {fl = fl} {pl = pl} {so = so} {ls = ls} ψ σ e se {c} pt with pl-pin cr π fc op sn ψ σ e se pt
  ... | q , pl′ , ep , un =
    q , _ , trans (cong U.step (sym (merged-just {H = Conf.heap (Mach.conf m)} fo G O LS QS pl pt)))
                  (flat-skip fo G (U.outerOf O) LS QS pl ep (pool-ahead cr π fc op sn ψ σ e se pt ep un)) , un
    where G  = λ a j → U.subscribe (f a) j
          O  = At.part (Conf.heap (Mach.conf m)) so
          LS = At.partLanes (Conf.heap (Mach.conf m)) ls
          QS = At.val (Conf.heap (Mach.conf m)) (FlatKit.Flat.queue fl)

  -- Over a hidden `of`, a held part's pin lifted through its ancestors,
  -- every sibling of which waits.
  void-up : ∀ {g m} (cr : Carried g m) {Δ A p i x xs} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i (x ∷ xs)))
            → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → opened (Conf.heap (Mach.conf m)) true π ≡ true
            → seen (Conf.heap (Mach.conf m)) π ≡ false
            → ∀ {Δ′ A′} {v : Sub (Conf.world (Mach.conf m)) Δ′ A′} (ψ : Path (Carried.tree cr) v) (τ : Path v (ofˢ {Δ = Δ} {A} p i (x ∷ xs))) → ψ ⊕ τ ≡ π
            → seen (Conf.heap (Mach.conf m)) ψ ≡ true
            → ∀ {c} → At.part (Conf.heap (Mach.conf m)) v ≡ just c → ∀ {q c′} → U.step c ≡ U.skipˢ q c′ → Under p q
            → Lifts (Conf.heap (Mach.conf m)) ψ (U.skipˢ q c′) (U.step g)
  void-up {m = m} cr {p = p} π fc op sn ψ τ e se pt ps un
    with lift-up cr here ψ τ pt (below (cong U.headˢ ps) un) se
           (clear-zip {P = Heads p} {Q = Off p} {R′ = Far p} (λ {Γ} {A} {c} → far-apart {p} {Γ} {A} {c}) ψ
              (clear-each (subst (λ q′ → Each (Conf.heap (Mach.conf m)) (Heads q′) (Carried.tree cr))
                                 (run-at (Carried.ctlAs cr) fc (Owned.placed (Carried.owned cr))) (Carried.behind cr)) ψ se (cong is-just pt))
              (spread-held cr π fc op ψ τ e se (cong is-just pt)))
  ... | c₁ , pc , L , _ =
    subst₂ (λ s c″ → Lifts (Conf.heap (Mach.conf m)) ψ s (U.step c″)) ps (just-injective (trans (sym pc) (run-meets (Carried.ctlAs cr) fc (Carried.meets cr)))) L

  -- At a pool: the pool's pin lifted.
  void-pool : ∀ {g m} (cr : Carried g m) {Δ A p i x xs} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i (x ∷ xs)))
            → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → opened (Conf.heap (Mach.conf m)) true π ≡ true
            → seen (Conf.heap (Mach.conf m)) π ≡ false
            → ∀ {Δ′ A′ B′ op f fl oc k r pl} {so : Sub (Conf.world (Mach.conf m)) Δ′ A′} {ls : List (Lane (Conf.world (Mach.conf m)) Δ′ B′)}
                (ψ : Path (Carried.tree cr) (flatMapˢ op f fl oc k r pl so ls)) (σ : Path (flatMapˢ op f fl oc k r pl so ls) _) → ψ ⊕ σ ≡ π
            → seen (Conf.heap (Mach.conf m)) ψ ≡ true → ∀ {c} → At.part (Conf.heap (Mach.conf m)) (flatMapˢ op f fl oc k r pl so ls) ≡ just c
            → Hops cr
  void-pool cr π fc op sn ψ σ e se pt with pool-pin cr π fc op sn ψ σ e se pt
  ... | q , c′ , ps , un = pool-land cr π fc op sn ψ σ e se pt ps (void-up cr π fc op sn ψ σ e se pt ps un)

  -- At an ended source's rest: the rest's pin lifted.
  void-rest : ∀ {g m} (cr : Carried g m) {Δ A p i x xs} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i (x ∷ xs)))
            → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → opened (Conf.heap (Mach.conf m)) true π ≡ true
            → seen (Conf.heap (Mach.conf m)) π ≡ false
            → ∀ {Δ′ A′ B′ S c b kb k fd rp e rt} {src : Sub (Conf.world (Mach.conf m)) Δ′ A′} {bd : Sub (Conf.world (Mach.conf m)) (A′ ∷ Δ′) B′}
                (ψ : Path (Carried.tree cr) (connectˢ S c b kb k fd rp e rt src bd)) (σ : Path src _) → ψ ⊕ in-source σ ≡ π
            → seen (Conf.heap (Mach.conf m)) ψ ≡ true → ∀ {n} → At.part (Conf.heap (Mach.conf m)) (connectˢ S c b kb k fd rp e rt src bd) ≡ just n
            → At.part (Conf.heap (Mach.conf m)) src ≡ nothing → ∀ {c₀} → e ≡ just c₀
            → Hops cr
  void-rest cr π fc op sn ψ σ e se pt ps ee with rest-pin cr π fc op sn ψ σ e se pt ps ee
  ... | q , n′ , pn , un = rest-land cr π fc op sn ψ σ e se pt ps ee pn (void-up cr π fc op sn ψ (in-source σ) e se pt pn un)

  emit-void : ∀ {g m} (cr : Carried g m) {Δ A p i x xs} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i (x ∷ xs)))
            → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → opened (Conf.heap (Mach.conf m)) true π ≡ true
            → seen (Conf.heap (Mach.conf m)) π ≡ false → Hops cr
  emit-void cr π fc op sn with void-site cr π fc op sn
  ... | in-pool ψ σ e se pt         = void-pool cr π fc op sn ψ σ e se pt
  ... | in-rest ψ σ e se pt ps ee   = void-rest cr π fc op sn ψ σ e se pt ps ee

  ≺-trans : ∀ {a b c} → a ≺ b → b ≺ c → a ≺ c
  ≺-trans (inj₁ ab)          (inj₁ bc)          = inj₁ (⊏-trans ab bc)
  ≺-trans (inj₁ ab)          (inj₂ (refl , _))  = inj₁ ab
  ≺-trans (inj₂ (refl , _))  (inj₁ bc)          = inj₁ bc
  ≺-trans (inj₂ (refl , ab)) (inj₂ (refl , bc)) = inj₂ (refl , <-trans ab bc)

  -- A hop from a lighter configuration of the same ghost is a hop from
  -- the heavier.
  hopped-below : ∀ {g m m₁ m′} {st : Strong g m} {st′ : Strong g m₁} → measure st′ ≺ measure st → Hopped st′ m′ → Hopped st m′
  hopped-below lt (g″ , m₀ , p , st₀ , passed ag pp)   = g″ , m₀ , p , st₀ , passed ag pp
  hopped-below lt (g″ , m₀ , p , st₀ , lowered ag lt′) = g″ , m₀ , p , st₀ , lowered ag (≺-trans lt′ lt)
  hopped-below lt (g″ , m₀ , p , st₀ , showing pp ns)  = g″ , m₀ , p , st₀ , showing pp ns

  -- A kernel begun by allocating hops to its restaged configuration,
  -- the ghost alike, less owed.
  regrown : ∀ {g m} (cr : Carried g m) {Δ A} {s : T.Obs Timeline Δ A} → Restages cr s → Hops cr
  regrown cr rs st with rs st
  ... | m₀ , p , cr′ , _ , lt = _ , m₀ , p , carried cr′ , lowered (λ n → agree-refl n _) lt

  -- What an `of`'s first call hops to.
  Emits : Set₁
  Emits = ∀ {g m} (cr : Carried g m) {Δ A p i xs} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i xs))
        → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → Hops cr

  -- An `of` planted, its first call taken by `eo`.
  offered : Emits → ∀ {g m} {cr : Carried g m} {Δ A} {xs : List A} → Offers cr {Δ} {A} xs → Hops cr
  offered eo (cr′ , _ , π′ , fc , lt) eq = hopped-below lt (eo cr′ π′ fc eq)

  -- A subscription begun, by its program, an `of`'s first call by `eo`.
  sub-by : Emits → ∀ {g m} (cr : Carried g m) {Δ A} (s : T.Obs Timeline Δ A) → subOf (Carried.ctlAs cr) ≡ just (Δ , A , s) → Hops cr
  sub-by eo cr (T.cold c)          e eq = sub-cold cr e eq
  sub-by eo cr T.empty             e eq = offered eo (empty-restage cr e) eq
  sub-by eo cr (T.of xs)           e eq = offered eo (of-restage cr e) eq
  sub-by eo cr (T.map f s)         e eq with map-restage cr e
  ... | cr′ , e′ , lt = hopped-below lt (sub-by eo cr′ s e′ eq)
  sub-by eo cr (T.scan f z s)      e eq = regrown cr (scan-restage cr e) eq
  sub-by eo cr (T.takeWhile i p s) e eq = regrown cr (take-restage cr e) eq
  sub-by eo cr (T.flatMap op f s)  e eq = regrown cr (flat-restage cr e) eq
  sub-by eo cr (T.connect s b)     e eq = regrown cr (connect-restage cr e) eq
  sub-by eo cr (T.connected i)     e eq = sub-joined cr e eq
  sub-by eo cr (T.defer l)         e eq = sub-defer cr e eq

  sub-onward : Emits → ∀ {g m} (cr : Carried g m) → opening (Carried.ctlAs cr) ≡ true → Hops cr
  sub-onward eo {m = mach ⟨ _ , _ , _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = subAs {s = s} _ _ _ _ } _ = sub-by eo cr s refl
  sub-onward eo {m = mach ⟨ _ , _ , _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = calmAs } ()
  sub-onward eo {m = mach ⟨ _ , _ , _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = noteAs _ _ _ } ()
  sub-onward eo {m = mach ⟨ _ , _ , _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = runAs _ _ _ } ()
  sub-onward eo {m = mach ⟨ _ , _ , _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = burstAs _ _ _ } ()
