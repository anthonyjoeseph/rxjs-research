{-# OPTIONS --guardedness --large-indices #-}

-- THE FOCUS: a firing cold's step, lifted through the subscriptions
-- around it to the meaning's next step.  At each level the cold's step
-- comes first when every sibling's next event comes later (`Clear`): a
-- flatMap's other lanes and its outer, a connect's body beside its
-- source, its source beside its body.  A connect shows its source's
-- step below the source's own position, at `ix 0`.
module Focus where

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Properties using (++-assoc; ++-conicalˡ; ++-conicalʳ; ++-identityʳ)
open import Data.List.Relation.Unary.All using (All; []; _∷_; head; lookup) renaming (map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties using (++⁺; ++⁻ˡ; ++⁻ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; Σ; _,_; proj₂)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Level using (Lift; lower; suc; zero) renaming (lift to up)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym; subst)

open import denotation.MonotonicList using (Pos; Frame; ix; sub; last; emit; stall; close; done; quiet; at; _<ᵖ_
                                           ; <ᵖ-asym; <ᵖ-ext; <ᵖ-trans; <ᵖ-past; <ᵖ-ix-sub; <ᵖ-cascade)
import denotation.Unfold as U
open import denotation.Unfold using (Srcs)
open import operation.AbstractObservable using (module Run)
open import operation.PureObservable using (Pureᴾ; World; Sink; module Pure)
open import Realize using (module Realizing)

-- A next event, if any, after `q`.
After : Pos → Maybe Pos → Set
After q nothing  = ⊤
After q (just k) = q <ᵖ k ≡ true

Later : ∀ {A} → Pos → U.Node A → Set
Later q n = After q (U.headˢ (U.step n))

Up : Set → Set₁
Up = Lift (suc zero)

Open : ∀ {A} → Pos → Maybe (U.Node A) → Set
Open q nothing  = ⊤
Open q (just n) = Later q n

-- A step that shows something, after `q`.
Leads : ∀ {A} → Pos → U.Step A → Set
Leads q (U.outˢ k _ _) = q <ᵖ k ≡ true
Leads q (U.skipˢ k _)  = q <ᵖ k ≡ true
Leads q _              = ⊤

-- A held source: one stepping beside a body, after `q`; one over, never shown.
Beside : ∀ {A} → Pos → Maybe (U.Node A) → Set
Beside q nothing  = ⊤
Beside q (just x) = Leads q (U.step x)

-- Past every step under `F`.
Beyond : Pos → Pos → Set
Beyond F k = ∀ Y → (F ++ Y) <ᵖ k ≡ true

private
  if-ok : ∀ {a p} {X : Set a} (P : X → Set p) b {x y : X} → P x → P y → P (if b then x else y)
  if-ok P true  px _  = px
  if-ok P false _  py = py

  nope : ∀ {X : Set} → false ≡ true → X
  nope ()

  -- The lane `earliest` finds, with the lanes around it.
  FoundIn : ∀ {B} → List (U.Node B) → U.Earliest B → Set₁
  FoundIn ls U.none                = Up ⊤
  FoundIn ls (U.found k bs l s as) = bs ++ l ∷ as ≡ ls × s ≡ U.step l × U.headˢ s ≡ just k

  pick-in : ∀ {B} (l : U.Node B) ls mk → U.headˢ (U.step l) ≡ mk → (e : U.Earliest B) → FoundIn ls e
          → FoundIn (l ∷ ls) (U.pick l (U.step l) ls mk e)
  pick-in l ls nothing  h U.none                  _            = up tt
  pick-in l ls nothing  h (U.found k bs c sc as)  (e , s , hk) = cong (l ∷_) e , s , hk
  pick-in l ls (just k) h U.none                  _            = refl , refl , h
  pick-in l ls (just k) h (U.found k′ bs c sc as) (e , s , hk) with k <ᵖ k′
  ... | true  = refl , refl , h
  ... | false = cong (l ∷_) e , s , hk

  found-in : ∀ {B} (ls : List (U.Node B)) → FoundIn ls (U.earliest ls)
  found-in []       = up tt
  found-in (l ∷ ls) = pick-in l ls (U.headˢ (U.step l)) refl (U.earliest ls) (found-in ls)

  later-found : ∀ {B L} {ls : List (U.Node B)} {k bs l s as} → All (Later L) ls → FoundIn ls (U.found k bs l s as) → L <ᵖ k ≡ true
  later-found {L = L} {bs = bs} a (refl , refl , hk) = subst (After L) hk (head (++⁻ʳ bs a))

  -- The outer's step first, every lane's next event later.
  go-outer : ∀ {A B} op (g : A → Pos → U.Node B) {n n₁ L} ls qs → U.step n ≡ U.skipˢ L n₁ → All (Later L) ls
           → (e : U.Earliest B) → FoundIn ls e
           → U.goˢ op g (just n) ls qs e ≡ U.skipˢ L (U.flatMapᶜ op g (just n₁) ls qs)
  go-outer op g ls qs sn a U.none _ = cong (λ z → U.outerˢ op g z ls qs) sn
  go-outer op g {n} {n₁} {L} _ qs sn a (U.found k bs l s as) fi@(refl , refl , _) =
    trans (cong (λ z → U.raceˢ op g n z (U.headˢ z) k bs l s as qs) sn)
          (cong (λ z → if z then U.outerˢ op g (U.skipˢ L n₁) (bs ++ l ∷ as) qs else U.laneˢ op g (just n) bs s as qs)
                (later-found a fi))

  -- The focused lane's step first, every other lane's next event later.
  pick-first : ∀ {B} (l : U.Node B) s as L (e : U.Earliest B) → FoundIn as e → All (Later L) as
             → U.pick l s as (just L) e ≡ U.found L [] l s as
  pick-first l s as L U.none                   _  _ = refl
  pick-first l s as L (U.found k′ bs c sc as′) fi a =
    cong (λ z → if z then U.found L [] l s as else U.found k′ (l ∷ bs) c sc as′) (later-found a fi)

  pick-after : ∀ {B} (b : U.Node B) s ls mk {L bs l sl as} → After L mk → U.pick b s ls mk (U.found L bs l sl as) ≡ U.found L (b ∷ bs) l sl as
  pick-after b s ls nothing  _ = refl
  pick-after b s ls (just k) {L} {bs} {l} {sl} {as} h = cong (λ z → if z then U.found k [] b s ls else U.found L (b ∷ bs) l sl as) (<ᵖ-asym L k h)

  earliest-at : ∀ {B} (bs : List (U.Node B)) n as {L n₁} → U.step n ≡ U.skipˢ L n₁ → All (Later L) bs → All (Later L) as
              → U.earliest (bs ++ n ∷ as) ≡ U.found L bs n (U.step n) as
  earliest-at []       n as sn _          a =
    trans (cong (λ z → U.pick n (U.step n) as z (U.earliest as)) (cong U.headˢ sn)) (pick-first n (U.step n) as _ (U.earliest as) (found-in as) a)
  earliest-at (b ∷ bs) n as sn (hb ∷ abs) a =
    trans (cong (U.pick b (U.step b) (bs ++ n ∷ as) (U.headˢ (U.step b))) (earliest-at bs n as sn abs a))
          (pick-after b (U.step b) (bs ++ n ∷ as) (U.headˢ (U.step b)) hb)

  race-lane : ∀ {A B} op (g : A → Pos → U.Node B) o so mk {L bs l s as qs} → After L mk
            → U.raceˢ op g o so mk L bs l s as qs ≡ U.laneˢ op g (just o) bs s as qs
  race-lane op g o so nothing  _ = refl
  race-lane op g o so (just k) {L} {bs} {l} {s} {as} {qs} h =
    cong (λ z → if z then U.outerˢ op g so (bs ++ l ∷ as) qs else U.laneˢ op g (just o) bs s as qs) (<ᵖ-asym L k h)

  go-lane : ∀ {A B} op (g : A → Pos → U.Node B) (o : Maybe (U.Node A)) bs n as qs {L n₁} → U.step n ≡ U.skipˢ L n₁ → Open L o
          → U.goˢ op g o (bs ++ n ∷ as) qs (U.found L bs n (U.step n) as) ≡ U.skipˢ L (U.flatMapᶜ op g o (bs ++ n₁ ∷ as) qs)
  go-lane op g nothing  bs n as qs sn _ = cong (λ z → U.laneˢ op g nothing bs z as qs) sn
  go-lane op g (just o) bs n as qs sn h =
    trans (race-lane op g o (U.step o) (U.headˢ (U.step o)) h) (cong (λ z → U.laneˢ op g (just o) bs z as qs) sn)

  -- A connect's source steps first, its body's next event later.
  before-after : ∀ {B} Q (sb : U.Step B) → After Q (U.headˢ sb) → U.beforeˢ Q sb ≡ true
  before-after Q (U.outˢ k _ _) h = h
  before-after Q (U.skipˢ k _)  h = h
  before-after Q (U.endˢ k)     h = h
  before-after Q U.hushˢ        _ = refl

  ahead-src : ∀ {A B} (b : U.Node B) sb (s : U.Node A) Q s₁ → After Q (U.headˢ sb)
            → U.aheadˢ b sb s Q s₁ (U.beforeˢ Q sb) ≡ U.skipˢ Q (U.connectᶜ b s₁)
  ahead-src b sb s Q s₁ h = cong (U.aheadˢ b sb s Q s₁) (before-after Q sb h)

  burst-head : ∀ {A t} τ r i (b : Frame A t) → U.headˢ (U.burstˢ τ r i b) ≡ just (r ++ [ ix i ])
  burst-head τ r i (emit _ _) = refl
  burst-head τ r i (stall _)  = refl
  burst-head τ r i (close _)  = refl

-- Where a configuration's next events lie: `Ok`, for a run at `pos`.  A
-- source a joiner copies steps past the run, its copy where `Ok` holds.
module Shape (pos : Pos) (Ok : Pos → Set) where
  OkM : Maybe Pos → Set
  OkM nothing  = ⊤
  OkM (just k) = Ok k

  Next : ∀ {A} → U.Node A → Set
  Next n = OkM (U.headˢ (U.step n))

  Opens : ∀ {A} → Maybe (U.Node A) → Set
  Opens nothing  = ⊤
  Opens (just n) = Next n

  SrcM : Maybe Pos → Set
  SrcM nothing  = ⊤
  SrcM (just k) = pos <ᵖ k ≡ true × (∀ p → Ok (k ++ [ sub p ]))

  Shows : ∀ {A} → Maybe (U.Node A) → Set
  Shows nothing  = ⊤
  Shows (just n) = SrcM (U.headˢ (U.step n))

  Fine : ∀ {Δ} → All (λ A → Maybe (U.Node A)) Δ → Set
  Fine []      = ⊤
  Fine (m ∷ ν) = Shows m × Fine ν

  fine-at : ∀ {Δ A} {ν : All (λ A → Maybe (U.Node A)) Δ} → Fine ν → (x : A ∈ Δ) → Shows (lookup ν x)
  fine-at {ν = _ ∷ _} (s , _) (here refl) = s
  fine-at {ν = _ ∷ _} (_ , f) (there x)   = fine-at f x

weaken : ∀ {pos} {Ok Ok′ : Pos → Set} → (∀ {k} → Ok k → Ok′ k) → ∀ {Δ} (ν : All (λ A → Maybe (U.Node A)) Δ)
       → Shape.Fine pos Ok ν → Shape.Fine pos Ok′ ν
weaken w []           _       = tt
weaken w (nothing ∷ ν) (_ , f) = tt , weaken w ν f
weaken {pos} {Ok} {Ok′} w (just n ∷ ν) (s , f) = src (U.headˢ (U.step n)) s , weaken w ν f
  where src : ∀ mk → Shape.SrcM pos Ok mk → Shape.SrcM pos Ok′ mk
        src nothing  _        = tt
        src (just k) (pk , o) = pk , λ p → w (o p)

-- Every step a node takes lies below one of its parts' next events, or
-- below the source a joiner copies.
module Steps (pos : Pos) (Ok : Pos → Set) (ext : ∀ k X → Ok k → Ok (k ++ X)) (above : ∀ {k} → Ok k → pos <ᵖ k ≡ true) where
  open Shape pos Ok

  shows : ∀ {A} (m : Maybe (U.Node A)) → Opens m → Shows m
  shows nothing  _ = tt
  shows (just n) o = src (U.headˢ (U.step n)) o
    where src : ∀ mk → OkM mk → SrcM mk
          src nothing  _ = tt
          src (just k) h = above h , λ p → ext k [ sub p ] h

  burst-ok : ∀ {A t} τ r i (b : Frame A t) → Ok (r ++ [ ix i ]) → OkM (U.headˢ (U.burstˢ τ r i b))
  burst-ok τ r i b h = subst OkM (sym (burst-head τ r i b)) h

  map-ok : ∀ {A B} (f : A → B) (s : U.Step A) → OkM (U.headˢ s) → OkM (U.headˢ (U.mapˢ f s))
  map-ok f (U.outˢ _ _ _) h = h
  map-ok f (U.skipˢ _ _)  h = h
  map-ok f (U.endˢ _)     h = h
  map-ok f U.hushˢ        h = h

  scan-ok : ∀ {A B} (f : B → A → B) z (s : U.Step A) → OkM (U.headˢ s) → OkM (U.headˢ (U.scanˢ f z s))
  scan-ok f z (U.outˢ _ _ _) h = h
  scan-ok f z (U.skipˢ _ _)  h = h
  scan-ok f z (U.endˢ _)     h = h
  scan-ok f z U.hushˢ        h = h

  take-ok : ∀ {A} i (p : A → Bool) (s : U.Step A) → OkM (U.headˢ s) → OkM (U.headˢ (U.takeWhileˢ i p s))
  take-ok i p (U.outˢ k a c) h = taking i (p a)
    where taking : ∀ i b → OkM (U.headˢ (U.taking i p k a c b))
          taking i     true  = h
          taking true  false = h
          taking false false = ext k [ last ] h
  take-ok i p (U.skipˢ _ _) h = h
  take-ok i p (U.endˢ _)    h = h
  take-ok i p U.hushˢ       h = h

  outer-ok : ∀ {A B} op (g : A → Pos → U.Node B) (s : U.Step A) ls qs → OkM (U.headˢ s) → OkM (U.headˢ (U.outerˢ op g s ls qs))
  outer-ok op g (U.outˢ q a o) ls      qs      h = ext q [ ix 0 ] h
  outer-ok op g (U.skipˢ q o)  ls      qs      h = h
  outer-ok op g (U.endˢ c)     []      []      h = h
  outer-ok op g (U.endˢ c)     []      (_ ∷ _) h = h
  outer-ok op g (U.endˢ c)     (_ ∷ _) _       h = h
  outer-ok op g U.hushˢ        ls      qs      h = tt

  lane-ok : ∀ {A B} op (g : A → Pos → U.Node B) o bs (s : U.Step B) as qs → OkM (U.headˢ s) → OkM (U.headˢ (U.laneˢ op g o bs s as qs))
  lane-ok op g o        bs      (U.outˢ k b c) as      qs       h = h
  lane-ok op g o        bs      (U.skipˢ k c)  as      qs       h = h
  lane-ok op g o        bs      (U.endˢ c)     as      (_ ∷ _)  h = ext c [ ix 0 ] h
  lane-ok op g nothing  []      (U.endˢ c)     []      []       h = h
  lane-ok op g nothing  []      (U.endˢ c)     (_ ∷ _) []       h = h
  lane-ok op g nothing  (_ ∷ _) (U.endˢ c)     as      []       h = h
  lane-ok op g (just _) bs      (U.endˢ c)     as      []       h = h
  lane-ok op g o        bs      U.hushˢ        as      qs       h = tt

  race-ok : ∀ {A B} op (g : A → Pos → U.Node B) o so mk k bs l (s : U.Step B) as qs → OkM (U.headˢ so) → OkM (U.headˢ s)
          → OkM (U.headˢ (U.raceˢ op g o so mk k bs l s as qs))
  race-ok op g o so nothing   k bs l s as qs ho hl = lane-ok op g (just o) bs s as qs hl
  race-ok op g o so (just k′) k bs l s as qs ho hl =
    if-ok (λ z → OkM (U.headˢ z)) (k′ <ᵖ k) (outer-ok op g so (bs ++ l ∷ as) qs ho) (lane-ok op g (just o) bs s as qs hl)

  go-ok : ∀ {A B} op (g : A → Pos → U.Node B) (o : Maybe (U.Node A)) ls qs → Opens o → All Next ls
        → (e : U.Earliest B) → FoundIn ls e → OkM (U.headˢ (U.goˢ op g o ls qs e))
  go-ok op g nothing  ls qs _  _ U.none _ = tt
  go-ok op g (just o) ls qs ho _ U.none _ = outer-ok op g (U.step o) ls qs ho
  go-ok op g nothing  _  qs _  a (U.found k bs l s as) (refl , refl , _) = lane-ok op g nothing bs (U.step l) as qs (head (++⁻ʳ bs a))
  go-ok op g (just o) _  qs ho a (U.found k bs l s as) (refl , refl , _) =
    race-ok op g o (U.step o) (U.headˢ (U.step o)) k bs l (U.step l) as qs ho (head (++⁻ʳ bs a))

  ahead-ok : ∀ {A B} (b : U.Node B) (sb : U.Step B) (x : U.Node A) Q x′ c → OkM (U.headˢ sb) → Ok Q
           → OkM (U.headˢ (U.aheadˢ b sb x Q x′ c))
  ahead-ok b sb             x Q x′ true  hb hq = hq
  ahead-ok b (U.outˢ _ _ _) x Q x′ false hb hq = hb
  ahead-ok b (U.skipˢ _ _)  x Q x′ false hb hq = hb
  ahead-ok b (U.endˢ _)     x Q x′ false hb hq = hb
  ahead-ok b U.hushˢ        x Q x′ false hb hq = tt

  rejoin-ok : ∀ {A} j i (s : U.Step A) → pos <ᵖ j ≡ false → SrcM (U.headˢ s) → OkM (U.headˢ (U.rejoinˢ j i s))
  rejoin-ok j i (U.outˢ q a c) pj (pq , o) = shown (j <ᵖ q) (<ᵖ-past pos j q pj pq)
    where shown : ∀ b → b ≡ true → OkM (U.headˢ (U.shownˢ j i q (just a) c b))
          shown true  _ = o j
          shown false ()
  rejoin-ok {A} j i (U.skipˢ q c) pj (pq , o) = shown (j <ᵖ q) (<ᵖ-past pos j q pj pq)
    where shown : ∀ b → b ≡ true → OkM (U.headˢ (U.shownˢ {A} j i q nothing c b))
          shown true  _ = o j
          shown false ()
  rejoin-ok {A} j i (U.endˢ c) pj (pc , o) = ended (j <ᵖ c) (<ᵖ-past pos j c pj pc)
    where ended : ∀ b → b ≡ true → OkM (U.headˢ (if b then U.endˢ {A} (c ++ [ sub j ]) else U.endˢ (j ++ [ last ])))
          ended true  _ = o j
          ended false ()
  rejoin-ok j i U.hushˢ _ _ = tt

  opens-if : ∀ {A} b {m : Maybe (U.Node A)} → Opens m → Opens (if b then m else nothing)
  opens-if true  h = h
  opens-if false h = tt

  live-or : ∀ {A} b {n : U.Node A} → (b ≡ false → Next n) → Opens (if b then nothing else just n)
  live-or true  _ = tt
  live-or false k = k refl

module Focusing (R : Set) where
  open Run (Pureᴾ R) using (Env; module Kit; module FlatKit)
  open FlatKit using (Flat)
  open Realizing R using (Sub; Lane; lane; Phase; nodeOf; Holding; Firing; firing; Spot; SpotLanes; cold-here; in-map; in-scan; in-take
                         ; in-outer; in-lanes; in-source; in-body; in-defer; this-lane; next-lane; spot-of; spot-lanes; spot-step
                         ; phaseAt; phaseAtLanes; over; one; firings; laneFirings; pendings; lanePendings; joiners; laneJoiners
                         ; Joiner; coldˢ; doneˢ; mapˢ; scanˢ; takeWhileˢ; flatMapˢ; connectˢ; joinˢ; deferˢ
                         ; waiting; popped; playing; module At)
  open Pure R using (State; Timer; get; cascade)

  -- Where the cold's step at `q` is shown at the root.
  mutual
    lift : ∀ {h Δ A B} {t : Sub h Δ A} {s : Sink h B} {hd} → Spot t s hd → Pos → Pos
    lift cold-here     q = q
    lift (in-map p)    q = lift p q
    lift (in-scan p)   q = lift p q
    lift (in-take p)   q = lift p q
    lift (in-outer p)  q = lift p q
    lift (in-lanes p)  q = liftLanes p q
    lift (in-source p) q = lift p q ++ [ ix 0 ]
    lift (in-body p)   q = lift p q
    lift (in-defer p)  q = lift p q

    liftLanes : ∀ {h Δ B C} {ls : List (Lane h Δ B)} {s : Sink h C} {hd} → SpotLanes ls s hd → Pos → Pos
    liftLanes (this-lane p) q = lift p q
    liftLanes (next-lane p) q = liftLanes p q

  -- Lifted, the step stays under where it was.
  mutual
    lift-ext : ∀ {h Δ A B} {t : Sub h Δ A} {s : Sink h B} {hd} (sp : Spot t s hd) q → Σ Pos λ Y → lift sp q ≡ q ++ Y
    lift-ext cold-here     q = [] , sym (++-identityʳ q)
    lift-ext (in-map p)    q = lift-ext p q
    lift-ext (in-scan p)   q = lift-ext p q
    lift-ext (in-take p)   q = lift-ext p q
    lift-ext (in-outer p)  q = lift-ext p q
    lift-ext (in-lanes p)  q = lift-ext-lanes p q
    lift-ext (in-source p) q with lift-ext p q
    ... | Y , e = Y ++ [ ix 0 ] , trans (cong (_++ [ ix 0 ]) e) (++-assoc q Y [ ix 0 ])
    lift-ext (in-body p)   q = lift-ext p q
    lift-ext (in-defer p)  q = lift-ext p q

    lift-ext-lanes : ∀ {h Δ B C} {ls : List (Lane h Δ B)} {s : Sink h C} {hd} (sp : SpotLanes ls s hd) q → Σ Pos λ Y → liftLanes sp q ≡ q ++ Y
    lift-ext-lanes (this-lane p) q = lift-ext p q
    lift-ext-lanes (next-lane p) q = lift-ext-lanes p q

  module On {h : World} (H : All (Pure.Val R h) h) where
    open At H

    -- Every sibling on the way up next steps after the cold's step there.
    mutual
      Clear : ∀ {Δ A B} {t : Sub h Δ A} {s : Sink h B} {hd} → Spot t s hd → Env Δ h → Srcs Δ → Pos → Set₁
      Clear cold-here                                  E ρ q = Up ⊤
      Clear (in-map p)                                 E ρ q = Clear p E ρ q
      Clear (in-scan p)                                E ρ q = Clear p E ρ q
      Clear (in-take p)                                E ρ q = Clear p E ρ q
      Clear (in-outer {ls = ls} p)                     E ρ q = Clear p E ρ q × All (Later (lift p q)) (partLanes ls E ρ)
      Clear (in-lanes {t = so} p)                      E ρ q = ClearLanes p E ρ q × Up (Open (liftLanes p q) (part so E ρ))
      Clear (in-source {S = S} {s₀ = s₀} {u = u} p)    E ρ q =
        Clear p E ρ q × Up (Open (lift p q ++ [ ix 0 ]) (part u (S ∷ E) (s₀ ∷ ρ)))
      Clear (in-body {S = S} {s₀ = s₀} {m = m} p)      E ρ q = Clear p (S ∷ E) (s₀ ∷ ρ) q × Up (Beside (lift p q) m)
      Clear (in-defer p)                               E ρ q = Clear p E ρ q

      ClearLanes : ∀ {Δ B C} {ls : List (Lane h Δ B)} {s : Sink h C} {hd} → SpotLanes ls s hd → Env Δ h → Srcs Δ → Pos → Set₁
      ClearLanes (this-lane {ls = ls} p) E ρ q = Clear p E ρ q × All (Later (lift p q)) (partLanes ls E ρ)
      ClearLanes (next-lane {l = l} p)   E ρ q = ClearLanes p E ρ q × All (Later (liftLanes p q)) (partLanes (l ∷ []) E ρ)

    private
      -- A gate above a live cold is open (`Gated`).
      live : ∀ {x : Bool} {hd} → (x ≡ false → spentʰ hd ≡ true) → spentʰ hd ≡ false → x ≡ true
      live {true}  d lv = refl
      live {false} d lv with trans (sym (d refl)) lv
      ... | ()

      opened : ∀ {X : Set₁} (mb : Maybe X) {hd} → (mb ≡ nothing → spentʰ hd ≡ true) → spentʰ hd ≡ false → Σ X λ b → mb ≡ just b
      opened (just b) d lv = b , refl
      opened nothing  d lv with trans (sym (d refl)) lv
      ... | ()

      -- A source stepping silently has something left to show, so the
      -- meaning holds it.
      held : ∀ {A} (m : Maybe (U.Node A)) {s′ : U.Node A} {L s₁} → Kept m (just s′) → U.step s′ ≡ U.skipˢ L s₁ → m ≡ just s′
      held (just x) k _ = cong just k
      held nothing  k e with trans (sym (cong over e)) (lower k)
      ... | ()

      lanes-split : ∀ {Δ B} (l : Lane h Δ B) ls (E : Env Δ h) ρ → partLanes (l ∷ ls) E ρ ≡ partLanes (l ∷ []) E ρ ++ partLanes ls E ρ
      lanes-split (lane c k s) ls E ρ with val (Kit.live c) | part s E ρ
      ... | true  | just x  = refl
      ... | true  | nothing = refl
      ... | false | _       = refl

      merged-lanes : ∀ {A B} op (g : A → Pos → U.Node B) o bs (n : U.Node B) as qs
                   → merged op g o (bs ++ n ∷ as) qs ≡ just (U.flatMapᶜ op g o (bs ++ n ∷ as) qs)
      merged-lanes op g (just _) bs      n as qs = refl
      merged-lanes op g nothing  []      n as qs = refl
      merged-lanes op g nothing  (_ ∷ _) n as qs = refl

      -- A connect's body steps first, the source it holds next stepping later.
      beside-body : ∀ {A B} (b : U.Node B) {L b₁} (x : U.Node A) sx → U.step b ≡ U.skipˢ L b₁ → Leads L sx
                  → Σ (U.Node B) λ n₁ → U.besideˢ b (U.step b) x sx ≡ U.skipˢ L n₁
                                      × connected (if over sx then nothing else just x) (just b₁) ≡ just n₁
      beside-body b {L} {b₁} x (U.outˢ k _ x′) sb h =
        U.connectᶜ b₁ x
        , trans (cong (λ z → U.aheadˢ b z x (k ++ [ ix 0 ]) x′ (U.beforeˢ (k ++ [ ix 0 ]) z)) sb)
                (cong (U.aheadˢ b (U.skipˢ L b₁) x (k ++ [ ix 0 ]) x′) (<ᵖ-asym L (k ++ [ ix 0 ]) (<ᵖ-ext L k [ ix 0 ] h)))
        , refl
      beside-body b {L} {b₁} x (U.skipˢ k x′) sb h =
        U.connectᶜ b₁ x
        , trans (cong (λ z → U.aheadˢ b z x (k ++ [ ix 0 ]) x′ (U.beforeˢ (k ++ [ ix 0 ]) z)) sb)
                (cong (U.aheadˢ b (U.skipˢ L b₁) x (k ++ [ ix 0 ]) x′) (<ᵖ-asym L (k ++ [ ix 0 ]) (<ᵖ-ext L k [ ix 0 ] h)))
        , refl
      beside-body b {b₁ = b₁} x (U.endˢ _) sb _ = b₁ , sb , refl
      beside-body b {b₁ = b₁} x U.hushˢ    sb _ = b₁ , sb , refl

    -- A live cold's silent step, every sibling above it clear, is the
    -- step of what is open around it, lifted, to the witness with its
    -- phase moved.
    mutual
      lift-skip : ∀ {Δ A B} {t : Sub h Δ A} {s : Sink h B} {hd} (sp : Spot t s hd) {E ρ q} {ph : Phase B}
                → spentʰ hd ≡ false → Gated t E ρ → Clear sp E ρ q
                → U.step (nodeOf (phaseAt sp)) ≡ U.skipˢ q (nodeOf ph)
                → Σ (U.Node A) λ n → Σ (U.Node A) λ n₁ → part t E ρ ≡ just n × U.step n ≡ U.skipˢ (lift sp q) n₁
                                                       × part (stepAt sp ph E ρ) E ρ ≡ just n₁
      lift-skip (cold-here {ph = ph₀}) {ph = ph} lv g c e =
        nodeOf ph₀ , nodeOf ph , cong (λ z → if z then nothing else just (nodeOf ph₀)) lv , e , cong (λ z → if z then nothing else just (nodeOf ph)) lv
      lift-skip (in-map {f = f} p) {E} {ρ} {q} {ph} lv g c e with lift-skip p {E} {ρ} {q} {ph} lv g c e
      ... | n , n₁ , o , sn , o₁ = U.mapᶜ f n , U.mapᶜ f n₁ , cong (mapᴹ (U.mapᶜ f)) o , cong (U.mapˢ f) sn , cong (mapᴹ (U.mapᶜ f)) o₁
      lift-skip (in-scan {f = f} {r} p) {E} {ρ} {q} {ph} lv g c e with lift-skip p {E} {ρ} {q} {ph} lv g c e
      ... | n , n₁ , o , sn , o₁ =
        U.scanᶜ f (val r) n , U.scanᶜ f (val r) n₁ , cong (mapᴹ (U.scanᶜ f (val r))) o , cong (U.scanˢ f (val r)) sn , cong (mapᴹ (U.scanᶜ f (val r))) o₁
      lift-skip (in-take {i = i} {p = pr} {c = c} {t = t} p) {E} {ρ} {q} {ph} lv (d , g) c′ e with lift-skip p {E} {ρ} {q} {ph} lv g c′ e
      ... | n , n₁ , o , sn , o₁ = U.takeWhileᶜ i pr n , U.takeWhileᶜ i pr n₁ , taken t o , cong (U.takeWhileˢ i pr) sn , taken (stepAt p ph E ρ) o₁
        where taken : ∀ t′ {n′} → part t′ E ρ ≡ just n′
                    → (if val (Kit.live c) then mapᴹ (U.takeWhileᶜ i pr) (part t′ E ρ) else nothing) ≡ just (U.takeWhileᶜ i pr n′)
              taken t′ o′ = trans (cong (λ z → if z then mapᴹ (U.takeWhileᶜ i pr) (part t′ E ρ) else nothing) (live (λ x → d x p) lv))
                                  (cong (mapᴹ (U.takeWhileᶜ i pr)) o′)
      lift-skip (in-outer {op = op} {f} {fl} {ls = ls} p) {E} {ρ} {q} {ph} lv (g , _) (c , al) e with lift-skip p {E} {ρ} {q} {ph} lv g c e
      ... | n , n₁ , o , sn , o₁ =
        U.flatMapᶜ op G (just n) PL Q , U.flatMapᶜ op G (just n₁) PL Q , cong (λ mo → merged op G mo PL Q) o
        , go-outer op G PL Q sn al (U.earliest PL) (found-in PL) , cong (λ mo → merged op G mo PL Q) o₁
        where G = λ a q → U.subscribe (f a) ρ q
              PL = partLanes ls E ρ
              Q = val (Flat.queue fl)
      lift-skip (in-lanes {op = op} {f} {fl} {t = so} p) {E} {ρ} {q} {ph} lv (_ , g) (c , oo) e with lift-skip-lanes p {E} {ρ} {q} {ph} lv g c e
      ... | bs , n , n₁ , as , pl , pl₁ , sn , abs , aas =
        U.flatMapᶜ op G O (bs ++ n ∷ as) Q , U.flatMapᶜ op G O (bs ++ n₁ ∷ as) Q
        , trans (cong (λ z → merged op G O z Q) pl) (merged-lanes op G O bs n as Q)
        , trans (cong (U.goˢ op G O (bs ++ n ∷ as) Q) (earliest-at bs n as sn abs aas)) (go-lane op G O bs n as Q sn (lower oo))
        , trans (cong (λ z → merged op G O z Q) pl₁) (merged-lanes op G O bs n₁ as Q)
        where G = λ a q → U.subscribe (f a) ρ q
              O = part so E ρ
              Q = val (Flat.queue fl)
      lift-skip (in-source {S = S} {s₀ = s₀} {m = m} {u = u} p) {E} {ρ} {q} {ph} lv (km , dead , gs , _) (c , ob) e
        with lift-skip p {E} {ρ} {q} {ph} lv gs c e | opened (part u (S ∷ E) (s₀ ∷ ρ)) (λ x → dead x p) lv
      ... | s′ , s₁ , o , sn , o₁ | b , eb =
        U.connectᶜ b s′ , U.connectᶜ b s₁ , cong₂ connected (held m (subst (Kept m) o km) sn) eb
        , trans (cong (U.besideˢ b (U.step b) s′) sn)
                (ahead-src b (U.step b) s′ (lift p q ++ [ ix 0 ]) s₁ (subst (Open (lift p q ++ [ ix 0 ])) eb (lower ob)))
        , cong₂ connected o₁ eb
      lift-skip (in-body {S = S} {s₀ = s₀} {m = nothing} p) {E} {ρ} {q} {ph} lv (_ , _ , _ , g) (c , _) e
        with lift-skip p {S ∷ E} {s₀ ∷ ρ} {q} {ph} lv g c e
      ... | b , b₁ , o , sn , o₁ = b , b₁ , cong (connected nothing) o , sn , cong (connected nothing) o₁
      lift-skip (in-body {S = S} {s₀ = s₀} {m = just x} p) {E} {ρ} {q} {ph} lv (_ , _ , _ , g) (c , ox) e
        with lift-skip p {S ∷ E} {s₀ ∷ ρ} {q} {ph} lv g c e
      ... | b , b₁ , o , sn , o₁ with beside-body b x (U.step x) sn (lower ox)
      ... | n₁ , st , pr = U.connectᶜ b x , n₁ , cong (connected (just x)) o , st , trans (cong (connected (pruned (just x))) o₁) pr
      lift-skip (in-defer p) {E} {ρ} {q} {ph} lv g c e = lift-skip p {E} {ρ} {q} {ph} lv g c e

      lift-skip-lanes : ∀ {Δ B C} {ls : List (Lane h Δ B)} {s : Sink h C} {hd} (sp : SpotLanes ls s hd) {E ρ q} {ph : Phase C}
                      → spentʰ hd ≡ false → GatedLanes ls E ρ → ClearLanes sp E ρ q
                      → U.step (nodeOf (phaseAtLanes sp)) ≡ U.skipˢ q (nodeOf ph)
                      → Σ (List (U.Node B)) λ bs → Σ (U.Node B) λ n → Σ (U.Node B) λ n₁ → Σ (List (U.Node B)) λ as
                        → partLanes ls E ρ ≡ bs ++ n ∷ as × partLanes (stepAtLanes sp ph E ρ) E ρ ≡ bs ++ n₁ ∷ as
                        × U.step n ≡ U.skipˢ (liftLanes sp q) n₁ × All (Later (liftLanes sp q)) bs × All (Later (liftLanes sp q)) as
      lift-skip-lanes (this-lane {c = c} {t = t} {ls = ls} p) {E} {ρ} {q} {ph} lv (d , g , _) (c′ , al) e
        with lift-skip p {E} {ρ} {q} {ph} lv g c′ e
      ... | n , n₁ , o , sn , o₁ = [] , n , n₁ , partLanes ls E ρ , spread t o , spread (stepAt p ph E ρ) o₁ , sn , [] , al
        where spread : ∀ t′ {n′} → part t′ E ρ ≡ just n′
                     → (if val (Kit.live c) then consᴹ (part t′ E ρ) (partLanes ls E ρ) else partLanes ls E ρ) ≡ n′ ∷ partLanes ls E ρ
              spread t′ o′ = trans (cong (λ z → if z then consᴹ (part t′ E ρ) (partLanes ls E ρ) else partLanes ls E ρ) (live (λ x → d x p) lv))
                                   (cong (λ z → consᴹ z (partLanes ls E ρ)) o′)
      lift-skip-lanes (next-lane {l = lane c k t} {ls = ls} p) {E} {ρ} {q} {ph} lv (_ , _ , g) (c′ , al) e
        with lift-skip-lanes p {E} {ρ} {q} {ph} lv g c′ e
      ... | bs , n , n₁ , as , pl , pl₁ , sn , abs , aas =
        L₀ ++ bs , n , n₁ , as , spread ls n pl , spread (stepAtLanes p ph E ρ) n₁ pl₁ , sn , ++⁺ al abs , aas
        where L₀ = partLanes (lane c k t ∷ []) E ρ
              spread : ∀ ls′ x → partLanes ls′ E ρ ≡ bs ++ x ∷ as → partLanes (lane c k t ∷ ls′) E ρ ≡ (L₀ ++ bs) ++ x ∷ as
              spread ls′ x pl′ = trans (lanes-split (lane c k t) ls′ E ρ) (trans (cong (L₀ ++_) pl′) (sym (++-assoc L₀ bs (x ∷ as))))

    -- With no cold firing in it, what is open next steps where `Ok`
    -- holds, when every live cold's timer does and every source a joiner
    -- copies is `Fine`: a joiner sits at or before the run (`past`), so
    -- its copy is shown below its source's step.
    module Far (pos : Pos) (Ok : Pos → Set) (ext : ∀ k X → Ok k → Ok (k ++ X)) (above : ∀ {k} → Ok k → pos <ᵖ k ≡ true) where
      open Shape pos Ok
      open Steps pos Ok ext above

      merged-ok : ∀ {A B} op (g : A → Pos → U.Node B) o ls qs → Opens o → All Next ls → Opens (merged op g o ls qs)
      merged-ok op g (just o) ls       qs       ho a = go-ok op g (just o) ls qs ho a (U.earliest ls) (found-in ls)
      merged-ok op g nothing  (l ∷ ls) qs       ho a = go-ok op g nothing (l ∷ ls) qs ho a (U.earliest (l ∷ ls)) (found-in (l ∷ ls))
      merged-ok op g nothing  []       []       ho a = tt
      merged-ok op g nothing  []       (_ ∷ _)  ho a = tt

      beside-ok : ∀ {A B} (b : U.Node B) (sb : U.Step B) (x : U.Node A) (sx : U.Step A) → OkM (U.headˢ sb)
                → OkM (U.headˢ sx) ⊎ over sx ≡ true → OkM (U.headˢ (U.besideˢ b sb x sx))
      beside-ok b sb x (U.outˢ q _ x′) hb (inj₁ h) = ahead-ok b sb x (q ++ [ ix 0 ]) x′ (U.beforeˢ (q ++ [ ix 0 ]) sb) hb (ext q [ ix 0 ] h)
      beside-ok b sb x (U.outˢ q _ x′) hb (inj₂ ())
      beside-ok b sb x (U.skipˢ q x′)  hb (inj₁ h) = ahead-ok b sb x (q ++ [ ix 0 ]) x′ (U.beforeˢ (q ++ [ ix 0 ]) sb) hb (ext q [ ix 0 ] h)
      beside-ok b sb x (U.skipˢ q x′)  hb (inj₂ ())
      beside-ok b sb x (U.endˢ _)      hb _ = hb
      beside-ok b sb x U.hushˢ         hb _ = hb

      conn-ok : ∀ {A B} (m ps : Maybe (U.Node A)) (pb : Maybe (U.Node B)) → Kept m ps → Opens ps → Opens pb → Opens (connected m pb)
      conn-ok m        ps        nothing  _  _  _  = tt
      conn-ok nothing  ps        (just b) _  _  hb = hb
      conn-ok (just x) (just s′) (just b) refl hs hb = beside-ok b (U.step b) x (U.step x) hb (inj₁ hs)
      conn-ok (just x) nothing   (just b) kp _  hb = beside-ok b (U.step b) x (U.step x) hb (inj₂ (lower kp))

      opens-map : ∀ {A B} (f : U.Node A → U.Node B) (m : Maybe (U.Node A)) → (∀ n → Next n → Next (f n)) → Opens m → Opens (mapᴹ f m)
      opens-map f nothing  _ _ = tt
      opens-map f (just n) k h = k n h

      cons-ok : ∀ {B} (m : Maybe (U.Node B)) {ls} → Opens m → All Next ls → All Next (consᴹ m ls)
      cons-ok nothing  _ a = a
      cons-ok (just n) h a = h ∷ a

      mutual
        far : ∀ {Δ A} (t : Sub h Δ A) {E ρ} {ν : Now Δ} → firings t ≡ [] → Gated t E ρ → Caught t E ρ ν → Fine ν
            → All (λ tm → spentʰ (Timer.handle tm) ≡ false → Ok (cascade tm)) (pendings t)
            → All (λ j → pos <ᵖ Joiner.at′ j ≡ false) (joiners t E)
            → Opens (part t E ρ)
        far (coldˢ s hd (waiting τ e (at t′ _ b))) _ _ _ _ (pt ∷ []) _ =
          live-or (spentʰ hd) (λ lv → burst-ok τ _ 0 b (ext _ [ ix 0 ] (pt lv)))
        far (coldˢ s hd (waiting τ e quiet))       _ _ _ _ _ _ = live-or (spentʰ hd) (λ _ → tt)
        far (coldˢ s hd (waiting τ e done))        _ g _ _ _ _ = live-or (spentʰ hd) (λ lv → nope (lower g lv))
        far (coldˢ s hd (popped _ _ _ _ _)) ()
        far (coldˢ s hd (playing _ _ _ _))  ()
        far doneˢ _ _ _ _ _ _ = tt
        far (mapˢ f t) {E} {ρ} fz g c fn pt pj = opens-map (U.mapᶜ f) (part t E ρ) (λ n → map-ok f (U.step n)) (far t fz g c fn pt pj)
        far (scanˢ f r t) {E} {ρ} fz g c fn pt pj =
          opens-map (U.scanᶜ f (val r)) (part t E ρ) (λ n → scan-ok f (val r) (U.step n)) (far t fz g c fn pt pj)
        far (takeWhileˢ i p c k t) {E} {ρ} fz (_ , g) cc fn pt pj =
          opens-if (val (Kit.live c)) (opens-map (U.takeWhileᶜ i p) (part t E ρ) (λ n → take-ok i p (U.step n)) (far t fz g cc fn pt pj))
        far (flatMapˢ op f fl oc k r so ls) {E} {ρ} fz (g , gl) (cs , cl) fn pt pj =
          merged-ok op (λ a q → U.subscribe (f a) ρ q) (part so E ρ) (partLanes ls E ρ) (val (Flat.queue fl))
            (far so (++-conicalˡ (firings so) _ fz) g cs fn (++⁻ˡ (pendings so) pt) (++⁻ˡ (joiners so E) pj))
            (far-lanes ls (++-conicalʳ (firings so) _ fz) gl cl fn (++⁻ʳ (pendings so) pt) (++⁻ʳ (joiners so E) pj))
        far (connectˢ S c k s₀ m src body) {E} {ρ} fz (km , _ , gs , gb) (cs , cb) fn pt pj =
          conn-ok m (part src E ρ) (part body (S ∷ E) (s₀ ∷ ρ)) km hs
            (far body (++-conicalʳ (firings src) _ fz) gb cb (shows (part src E ρ) hs , fn) (++⁻ʳ (pendings src) pt) (++⁻ʳ (joiners src E) pj))
          where hs = far src (++-conicalˡ (firings src) _ fz) gs cs fn (++⁻ˡ (pendings src) pt) (++⁻ˡ (joiners src E) pj)
        far (joinˢ j i sk l x cp) {ν = ν} _ _ cj fn _ (pj ∷ []) = join-ok (val l) cj
          where join-ok : ∀ b → (b ≡ true → lookup ν x ≡ just cp) → Opens (if b then just (U.joinᶜ j i cp) else nothing)
                join-ok false _ = tt
                join-ok true  e = rejoin-ok j i (U.step cp) pj (subst (λ z → Shows z) (e refl) (fine-at fn x))
        far (deferˢ k t) fz g c fn pt pj = far t fz g c fn pt pj

        far-lanes : ∀ {Δ B} (ls : List (Lane h Δ B)) {E ρ} {ν : Now Δ} → laneFirings ls ≡ [] → GatedLanes ls E ρ → CaughtLanes ls E ρ ν → Fine ν
                  → All (λ tm → spentʰ (Timer.handle tm) ≡ false → Ok (cascade tm)) (lanePendings ls)
                  → All (λ j → pos <ᵖ Joiner.at′ j ≡ false) (laneJoiners ls E)
                  → All Next (partLanes ls E ρ)
        far-lanes [] _ _ _ _ _ _ = []
        far-lanes (lane c k t ∷ ls) {E} {ρ} fz (_ , g , gl) (ct , cl) fn pt pj =
          if-ok (All Next) (val (Kit.live c))
                (cons-ok (part t E ρ) (far t (++-conicalˡ (firings t) _ fz) g ct fn (++⁻ˡ (pendings t) pt) (++⁻ˡ (joiners t E) pj)) rest) rest
          where rest = far-lanes ls (++-conicalʳ (firings t) _ fz) gl cl fn (++⁻ʳ (pendings t) pt) (++⁻ʳ (joiners t E) pj)

    -- Every sibling of the cold firing at `F` steps past the burst there,
    -- the run at `pos` short of it: but a connect's body, its source
    -- firing, steps after the source's step below its own position, its
    -- joiners' copies shown below that step.
    module Clearing (pos F : Pos) (pF : pos <ᵖ F ≡ true) where
      beyond-ext : ∀ k X → Beyond F k → Beyond F (k ++ X)
      beyond-ext k X h Y = <ᵖ-ext (F ++ Y) k X (h Y)

      beyond-above : ∀ {k} → Beyond F k → pos <ᵖ k ≡ true
      beyond-above {k} h = <ᵖ-trans pos F k pF (subst (λ z → z <ᵖ k ≡ true) (++-identityʳ F) (h []))

      open Shape pos (Beyond F)
      open Steps pos (Beyond F) beyond-ext beyond-above using (shows)
      open Far pos (Beyond F) beyond-ext beyond-above

      Under : Pos → Set
      Under L = Σ Pos λ Y → L ≡ F ++ Y

      under : ∀ {L} → Under L → pos <ᵖ L ≡ true
      under (Y , refl) = <ᵖ-ext pos F Y pF

      past : ∀ {L} → Under L → ∀ X {k} → Beyond F k → (L ++ X) <ᵖ k ≡ true
      past (Y , refl) X {k} h = subst (λ z → z <ᵖ k ≡ true) (sym (++-assoc F Y X)) (h (Y ++ X))

      later : ∀ {L} → Under L → ∀ mk → OkM mk → After L mk
      later _        nothing  _ = tt
      later (Y , refl) (just k) h = h Y

      open-of : ∀ {A L} → Under L → (m : Maybe (U.Node A)) → Opens m → Open L m
      open-of w nothing  _ = tt
      open-of w (just n) h = later w (U.headˢ (U.step n)) h

      leads : ∀ {A L} → Under L → (sx : U.Step A) → OkM (U.headˢ sx) ⊎ over sx ≡ true → Leads L sx
      leads (Y , refl) (U.outˢ k _ _) (inj₁ h) = h Y
      leads _          (U.outˢ k _ _) (inj₂ ())
      leads (Y , refl) (U.skipˢ k _)  (inj₁ h) = h Y
      leads _          (U.skipˢ k _)  (inj₂ ())
      leads _          (U.endˢ _)     _ = tt
      leads _          U.hushˢ        _ = tt

      beside : ∀ {A L} → Under L → (m ps : Maybe (U.Node A)) → Kept m ps → Opens ps → Beside L m
      beside w nothing  ps        _    _ = tt
      beside w (just x) (just s′) refl h = leads w (U.step x) (inj₁ h)
      beside w (just x) nothing   kp   _ = leads w (U.step x) (inj₂ (lower kp))

      -- The body beside a source whose step at `L` comes first.
      first : ∀ {L} → Under L → ∀ mk → Shape.OkM pos (λ k → (L ++ [ ix 0 ]) <ᵖ k ≡ true) mk → After (L ++ [ ix 0 ]) mk
      first _ nothing  _ = tt
      first _ (just k) h = h

      mutual
        clear-at : ∀ {Δ A} (t : Sub h Δ A) {f} (e : firings t ≡ f ∷ []) {E ρ} {ν : Now Δ} {ph : Phase (Firing.A f)}
                 → spentʰ (Firing.handle f) ≡ false → Gated t E ρ → Caught t E ρ ν → Fine ν
                 → All (λ tm → spentʰ (Timer.handle tm) ≡ false → Beyond F (cascade tm)) (pendings t)
                 → All (λ j → pos <ᵖ Joiner.at′ j ≡ false) (joiners t E)
                 → U.step (nodeOf (phaseAt (spot-of t e))) ≡ U.skipˢ F (nodeOf ph)
                 → Clear (spot-of t e) E ρ F
        clear-at (coldˢ s hd (waiting _ _ _))    ()
        clear-at (coldˢ s hd (popped _ _ _ _ _)) refl _ _ _ _ _ _ _ = up tt
        clear-at (coldˢ s hd (playing _ _ _ _))  refl _ _ _ _ _ _ _ = up tt
        clear-at doneˢ ()
        clear-at (mapˢ f t)             e lv g      c  fn pt pj sn = clear-at t e lv g c fn pt pj sn
        clear-at (scanˢ f r t)          e lv g      c  fn pt pj sn = clear-at t e lv g c fn pt pj sn
        clear-at (takeWhileˢ i p c k t) e lv (_ , g) cc fn pt pj sn = clear-at t e lv g cc fn pt pj sn
        clear-at (flatMapˢ op f fl oc k r so ls) e {E} {ρ} lv (g , gl) (cs , cl) fn pt pj sn with one (firings so) (laneFirings ls) e
        ... | inj₁ (e′ , z) =
          clear-at so e′ lv g cs fn (++⁻ˡ (pendings so) pt) (++⁻ˡ (joiners so E) pj) sn
          , mapᴬ (λ {n} h → later (lift-ext (spot-of so e′) F) (U.headˢ (U.step n)) h)
                 (far-lanes ls z gl cl fn (++⁻ʳ (pendings so) pt) (++⁻ʳ (joiners so E) pj))
        ... | inj₂ (z , e′) =
          clear-lanes ls e′ lv gl cl fn (++⁻ʳ (pendings so) pt) (++⁻ʳ (joiners so E) pj) sn
          , up (open-of (lift-ext-lanes (spot-lanes ls e′) F) (part so E ρ) (far so z g cs fn (++⁻ˡ (pendings so) pt) (++⁻ˡ (joiners so E) pj)))
        clear-at (connectˢ S c k s₀ m src body) e {E} {ρ} {ν} {ph} lv (km , _ , gs , gb) (cs , cb) fn pt pj sn
          with one (firings src) (firings body) e
        ... | inj₁ (e′ , z) with clear-at src e′ lv gs cs fn (++⁻ˡ (pendings src) pt) (++⁻ˡ (joiners src E) pj) sn
        ...   | cp with lift-skip (spot-of src e′) {E} {ρ} {F} {ph} lv gs cp sn
        ...     | n , _ , o , st , _ =
          cp , up (body-first (part body (S ∷ E) (s₀ ∷ ρ))
                     (FS.far body z gb cb (src-first , weaken (past w [ ix 0 ]) ν fn)
                             (mapᴬ (λ h lv′ → past w [ ix 0 ] (h lv′)) (++⁻ʳ (pendings src) pt)) (++⁻ʳ (joiners src E) pj)))
          where L = lift (spot-of src e′) F
                w = lift-ext (spot-of src e′) F
                OkS : Pos → Set
                OkS k = (L ++ [ ix 0 ]) <ᵖ k ≡ true
                module FS = Far pos OkS (λ k X h → <ᵖ-ext (L ++ [ ix 0 ]) k X h)
                                        (λ {k} h → <ᵖ-trans pos (L ++ [ ix 0 ]) k (<ᵖ-ext pos L [ ix 0 ] (under w)) h)
                src-first : Shape.Shows pos OkS (part src E ρ)
                src-first = subst (Shape.Shows pos OkS) (sym o)
                                  (subst (Shape.SrcM pos OkS) (sym (cong U.headˢ st)) (under w , λ p → <ᵖ-ix-sub L 0 p))
                body-first : ∀ {B} (mb : Maybe (U.Node B)) → Shape.Opens pos OkS mb → Open (L ++ [ ix 0 ]) mb
                body-first nothing  _ = tt
                body-first (just b) h = first w (U.headˢ (U.step b)) h
        clear-at (connectˢ S c k s₀ m src body) e {E} {ρ} {ν} {ph} lv (km , _ , gs , gb) (cs , cb) fn pt pj sn
            | inj₂ (z , e′) =
          clear-at body e′ {S ∷ E} {s₀ ∷ ρ} {part src E ρ ∷ ν} lv gb cb (shows (part src E ρ) hs , fn)
                   (++⁻ʳ (pendings src) pt) (++⁻ʳ (joiners src E) pj) sn
          , up (beside (lift-ext (spot-of body e′) F) m (part src E ρ) km hs)
          where hs = far src z gs cs fn (++⁻ˡ (pendings src) pt) (++⁻ˡ (joiners src E) pj)
        clear-at (joinˢ j i sk l x cp) ()
        clear-at (deferˢ k t) e lv g c fn pt pj sn = clear-at t e lv g c fn pt pj sn

        clear-lanes : ∀ {Δ B} (ls : List (Lane h Δ B)) {f} (e : laneFirings ls ≡ f ∷ []) {E ρ} {ν : Now Δ} {ph : Phase (Firing.A f)}
                    → spentʰ (Firing.handle f) ≡ false → GatedLanes ls E ρ → CaughtLanes ls E ρ ν → Fine ν
                    → All (λ tm → spentʰ (Timer.handle tm) ≡ false → Beyond F (cascade tm)) (lanePendings ls)
                    → All (λ j → pos <ᵖ Joiner.at′ j ≡ false) (laneJoiners ls E)
                    → U.step (nodeOf (phaseAtLanes (spot-lanes ls e))) ≡ U.skipˢ F (nodeOf ph)
                    → ClearLanes (spot-lanes ls e) E ρ F
        clear-lanes [] ()
        clear-lanes (lane c k t ∷ ls) e {E} {ρ} lv (d , g , gl) (ct , cl) fn pt pj sn with one (firings t) (laneFirings ls) e
        ... | inj₁ (e′ , z) =
          clear-at t e′ lv g ct fn (++⁻ˡ (pendings t) pt) (++⁻ˡ (joiners t E) pj) sn
          , mapᴬ (λ {n} h → later (lift-ext (spot-of t e′) F) (U.headˢ (U.step n)) h)
                 (far-lanes ls z gl cl fn (++⁻ʳ (pendings t) pt) (++⁻ʳ (joiners t E) pj))
        ... | inj₂ (z , e′) =
          clear-lanes ls e′ lv gl cl fn (++⁻ʳ (pendings t) pt) (++⁻ʳ (joiners t E) pj) sn
          , mapᴬ (λ {n} h → later (lift-ext-lanes (spot-lanes ls e′) F) (U.headˢ (U.step n)) h)
                 (far-lanes (lane c k t ∷ []) (cong (_++ []) z) (d , g , up tt) (ct , up tt) fn
                            (++⁺ (++⁻ˡ (pendings t) pt) []) (++⁺ (++⁻ˡ (joiners t E) pj) []))

  -- At a burst boundary every other node's next event comes after the
  -- firing cold's step: another cold's is a queued timer's, past the
  -- run's position (`Ordered`, `Timed`) and so past every step of the
  -- frame (cascades never nest, `rooted`); a joiner's copy is its
  -- source's (`caught`), shown below that source's step since it joined
  -- at or before the run (`past`).
  clear : ∀ {h c} {st : State h} {A u τ} {s : Sink h A} {hd r i} {b : Frame A u}
        → (H : Holding (firing s hd τ r i b ∷ []) c st) → lower (get (State.heap st) hd) ≡ false
        → ∀ {q} {ph : Phase A} → U.burstˢ τ r i b ≡ U.skipˢ q (nodeOf ph)
        → On.Clear (State.heap st) (spot-of (Holding.tree H) (Holding.firing≡ H)) [] [] q
  clear {r = []} H lv eq = ⊥-elim (head (Holding.rooted H) refl)
  clear {st = st} {τ = τ} {r = x ∷ r′} {i} {b} H lv {q} {ph} eq with head (Holding.behind H)
  ... | (d , pd) , lt =
    On.Clearing.clear-at (State.heap st) (State.pos st) q pF (Holding.tree H) (Holding.firing≡ H) {[]} {[]} {[]} {ph} lv
                         (Holding.gated H) (Holding.caught H) tt
                         (mapᴬ (λ {tm} h lv′ → beyond tm (proj₂ (lookup (proj₂ (Holding.ordered H)) (h lv′)))) (proj₂ (Holding.timed H)))
                         (Holding.past H) (trans (spot-step (Holding.tree H) (Holding.firing≡ H)) eq)
    where qe : (x ∷ r′) ++ [ ix i ] ≡ q
          qe = just-injective (trans (sym (burst-head τ (x ∷ r′) i b)) (cong U.headˢ eq))
          pF : State.pos st <ᵖ q ≡ true
          pF = subst (λ z → State.pos st <ᵖ z ≡ true) qe lt
          beyond : ∀ tm → State.pos st <ᵖ cascade tm ≡ true → Beyond q (cascade tm)
          beyond tm pc Y =
            subst (λ z → (z ++ Y) <ᵖ cascade tm ≡ true) qe
              (subst (λ z → z <ᵖ cascade tm ≡ true) (sym (++-assoc (x ∷ r′) [ ix i ] Y))
                (<ᵖ-cascade x r′ d i Y (Timer.due tm) (Timer.from tm) (subst (λ z → z <ᵖ cascade tm ≡ true) pd pc)))
