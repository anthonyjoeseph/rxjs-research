{-# OPTIONS --guardedness #-}

module adequacy.Lift.Order where

open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Properties using (++-assoc)
open import Data.List.Relation.Unary.Any using (Any; here)
import Data.List.Relation.Unary.Any as Any
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Data.Nat.Properties using (<-trans)
open import Data.List.Relation.Unary.All using (All; []; _∷_; map) renaming (lookup to lookupᴬ)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to all-++⁺)
open import Data.List.Relation.Unary.AllPairs using (_∷_)
open import Data.List.Relation.Unary.Linked using (_∷_)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴸ_)
open import Level using (Lift)
open import Data.Maybe using (Maybe; just; nothing; is-just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; Σ; proj₁)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import denotation.MonotonicList.Events using (Events∞; Pos; Timeline; ix; _<ᵖ_; <ᵖ-trans; <ᵖ-asym; <ᵖ-below)
open import denotation.MonotonicList using (agree-refl)
import denotation.Unfold as U
open import denotation.MonotonicList.Events using () renaming (sub to subᴾ)
open import adequacy.Sorted using (Under)
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
open import operation.PureObservable using (Out; Pureᴾ)
open import operation.AbstractObservable using (module Heap; module Run) renaming (module Machine to Shared)
open import Data.Bool using (Bool; true; false; _∧_; _∨_)
open import Data.Bool.Properties using (∧-zeroʳ)
open import adequacy.Ghost using (module Ghosting)
open import adequacy.Ghost.Paths using (module GhostingPaths)
open import adequacy.Fork using (module Forking)
open import adequacy.Restages using (module Staging)
open import adequacy.Scanned using (module Scanning)
open import adequacy.Taken using (module Taking)
open import adequacy.Connected using (module Connecting)
open import adequacy.Flatted using (module Flatting)
open import adequacy.Replant using (module Replanting)
open import adequacy.Frame using (module Framing)
open import adequacy.Frame.Repool using (module FramingRepool)
open import adequacy.Shift using (module Shifting)
open import adequacy.Lift using (module Lifting)
open Events∞

module LiftingOrder (R : Set) where
  open Machine R using (Mach; mach; Playing; Step; silent; step; Read)
  open Shared Timeline (Out R) using (Heapᴹ; Conf; ⟨_,_,_⟩; held; run; asking; bottom; spent?)
  open Heap using (_⊑_)
  open SortingWalk R using (Beyond)
  open Run (Pureᴾ R) using (Act; module Kit; module FlatKit)
  open Strongly R using (Sub; pendingˢ; coldˢ; ofˢ; mapˢ; scanˢ; takeWhileˢ; flatMapˢ; connectˢ; Lane; lane; here; module At; fired; waiting; Path; emitC; kontC; Leaf; feedC; srcC; taking; taken; feeding; PathLanes; this-lane; next-lane; in-map; in-scan; in-take; in-outer; in-lanes; in-source; in-body; in-defer; _⊕_; _≗_; rootObs; ⊕-here) renaming (ending to endingᵗ; ⟦_⟧ to ⟦_⟧ᶜ)
  open StrongAgainst R using (Books; Queue; Kernels; Meaning; Owned; Each; Lingers; pinned-skip; seen; seenL; owned-to)
  open StrongHeld R using (Strong; Carried; carried; Heads; DoneBy; Meets; module Eaching; module Lingering)
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
  open Framing R using (untold)
  open FramingRepool R using (Untold; Ended)
  open Shifting R using (pin-alike)
  open Taking R using (take-restage)
  open Connecting R using (connect-restage)
  open Flatting R using (flat-restage)
  open Read
  open Lifting R using (Below; below; below-body; below-lane; below-map; below-outer; below-scan; below-shut; below-source; below-take; far-gt; far-lt; in-pool; in-rest; left-pin; pool-land; pool-off; pooled-pin; rest-body; rest-land; shut-step; spread-held; sub-cold; sub-defer; sub-joined; under-++; void-site)

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
  ... | q , y′ , ey , u with pinned-skip (proj₁ (Lingers.pools (Carried.lingers cr) ψ se pt)) ey
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
    with pinned-skip (Lingers.rests (Carried.lingers cr) ψ se pt ps refl) ey
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
