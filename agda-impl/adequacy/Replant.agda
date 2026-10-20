{-# OPTIONS --guardedness #-}

-- ONE REPLANT FRAME: a node at the path's end rewritten to a kin, or a
-- write at its own cells, or both at once, against everything the
-- relation holds of the rest of the tree.  The node's own clauses are
-- each frame's premises; the rest of the tree is the frame's.
module adequacy.Replant where

open import Data.List using (List; []; _∷_; _++_; [_]) renaming (map to mapList)
open import Data.List.Relation.Unary.Any using (here)
open import Data.List.Relation.Unary.Any.Properties using (++⁺ʳ)
open import Data.List.Relation.Unary.All using (All; map) renaming (lookup to lookupᴬ)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; _∷_)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴸ_)
open import Data.Maybe using (Maybe; just; nothing; is-just)
open import Data.Nat using (_≤_; zero; suc; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Bool using (true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Level using (lower)

open import denotation.MonotonicList.Events using (Timeline; Pos; Label; ix; sub; last; Frame; From; _<ᵖ_; <ᵖ-irrefl; <ᵖ-apart)
import denotation.Unfold as U
open import operation.PureObservable using (Out; Pureᴾ; module Pure)
open import operation.AbstractObservable using (module Heap; module Run) renaming (module Machine to Shared)
open import adequacy.Strong using (module Strongly)
open import adequacy.Strong.Against using (module StrongAgainst)
open import adequacy.Strong.Held using (module StrongHeld)
open import adequacy.Moves using (module Moving)
open import adequacy.Retag using (Retag; keep; module Retagging)
open import adequacy.Torn using (module Tearing)
open import adequacy.Frame using (module Framing)
open import adequacy.Frame.Repool using (module FramingRepool)
open import adequacy.Shift.Walk using (module ShiftWalk)

module Replanting (R : Set) where
  open Shared Timeline (Out R) using (Heapᴹ; Stack; store)
  open Heap using (_⊑_; _∋_; Handle; cell) renaming (same to sameʰ)
  open Run (Pureᴾ R) using (Act; wkAct; _>>ᴬ_; module Kit; emitAll; under; module Observer)
  open Pure R using (Timer; cascade)
  open Strongly R using (Sub; Path; PathLanes; _⊕_; here; in-map; in-scan; in-take; in-outer; in-lanes; in-source; in-body; in-defer; this-lane; next-lane; Lane; lane; Call; emitC; kontC; take1C; take2C; bodyC; feedC; finC; srcC; code; Leaf; of-leaf; cold-leaf; done-leaf; join-leaf; walk; walkLanes; top; module Here; unsub; unsubscribing; playing; fired; taken; pendingˢ; ofˢ; doneˢ; mapˢ; scanˢ; joinˢ; deferˢ; coldˢ; takeWhileˢ; flatMapˢ; connectˢ; taking; ending; idle; feeding; finishing; outers; Name; names; laneNames; cutNames; quietName; subjectNames; flatNames; module At; _≗_) renaming (⟦_⟧ to ⟦_⟧ᶜ)
  open StrongAgainst R using (spot; Owned; Each; Lingers; Pinned; Twin)
  open StrongHeld R using (Heads; DoneBy)
  open StrongAgainst.Against R using (StackAs; BurstAs; Held; bottomAs; restAs; backAs; reholdAs; playsAs; firesAs; overAs; bottomᴴ; restᴴ; BurstClocked; Ticked; CtlAs; runAs)
  open Moving R using (plant; plantᴸ; planted; plant-self; pairs-r; pairs-split; Same; same; same-map; same-scan; same-take; same-flat; same-connect; same-defer)
  open Retagging R using (retag; retagᴸ)
  open Tearing R using (Off; look-either; fresh-path; part-alike; names-path; lanes-path; apart-r; apart-l; narrow)
  open Framing R using (untold)
  open FramingRepool R using (Untold; Ended)
  open ShiftWalk R using (module Walk)

  -- A NODE'S KIN: what a move rewrites it to.  A take ended; a pool
  -- restaged; a connect's feed restaged from `idle`, its body's joiners
  -- retold; a flatMap given a lane ahead of its own and a pool.  Every
  -- kin keeps the node's cells and every child, so a call or a burst
  -- aimed anywhere in the tree aims at the same fields after.
  data Kin {h} : ∀ {Δ A} → Sub h Δ A → Sub h Δ A → Set₁ where
    kin-end  : ∀ {Δ A i p c k q n} {s : Sub h Δ A} → Kin (takeWhileˢ i p c k taking s) (takeWhileˢ i p c k (ending q n) s)
    kin-pool : ∀ {Δ A B op f fl oc k r pl pl′} {s : Sub h Δ A} {ls : List (Lane h Δ B)}
             → Kin (flatMapˢ op f fl oc k r pl s ls) (flatMapˢ op f fl oc k r pl′ s ls)
    kin-feed : ∀ {Δ A B S c b kb k x q ss rp e rt} {g : Retag (A ∷ Δ)} {s : Sub h Δ A} {bd : Sub h (A ∷ Δ) B}
             → Kin (connectˢ S c b kb k idle rp e rt s bd) (connectˢ S c b kb k (feeding x q ss) rp e rt s (retag g bd))
    kin-fin  : ∀ {Δ A B S c b kb k q ss rp e rt} {g : Retag (A ∷ Δ)} {s : Sub h Δ A} {bd : Sub h (A ∷ Δ) B}
             → Kin (connectˢ S c b kb k idle rp e rt s bd) (connectˢ S c b kb k (finishing q ss) rp e rt s (retag g bd))
    kin-lane : ∀ {Δ A B op f fl oc k r pl pl′} {l : Lane h Δ B} {s : Sub h Δ A} {ls : List (Lane h Δ B)}
             → Kin (flatMapˢ op f fl oc k r pl s ls) (flatMapˢ op f fl oc k r pl′ s (l ∷ ls))

  -- What the kin owes the agenda: an ended take its completion, a feed or
  -- a finish its delivery; a pool nothing, nor a lane, whose subscription
  -- the control owes.
  owed : ∀ {h Δ A} {T : Sub h [] R} {u v : Sub h Δ A} → Kin u v → (ρ : Path T u) → List (Call (plant ρ v))
  owed {v = v} kin-end  ρ = take1C (planted ρ v) ∷ []
  owed         kin-pool ρ = []
  owed         kin-lane ρ = []
  owed {v = v} kin-feed ρ = feedC (planted ρ v) ∷ []
  owed {v = v} kin-fin  ρ = finC (planted ρ v) ∷ []

  -- Where what is owed runs: the position the kin was made at.  A lane's
  -- is no run's.
  Owing : ∀ {h Δ A} {u v : Sub h Δ A} → Kin u v → Pos → Set
  Owing (kin-end {q = q})  p = p ≡ q
  Owing kin-pool           p = ⊤
  Owing kin-lane           p = ⊥
  Owing (kin-feed {q = q}) p = p ≡ q
  Owing (kin-fin {q = q})  p = p ≡ q

  -- A node and what it is after a kin is planted: the same but for its
  -- children, the kin itself, or a joiner retold.
  data Twin {h} : ∀ {Δ A} → Sub h Δ A → Sub h Δ A → Set₁ where
    twin-same : ∀ {Δ A} {x x′ : Sub h Δ A} → Same x x′ → Twin x x′
    twin-kin  : ∀ {Δ A} {x x′ : Sub h Δ A} → Kin x x′ → Twin x x′
    twin-join : ∀ {Δ A j sk l i st st′} → Twin (joinˢ {Δ = Δ} {A} j sk l i st) (joinˢ j sk l i st′)

  -- A path carried into a rewritten tree: to the node's twin, walked
  -- alike.
  Carry : ∀ {h Δ₀ A₀ Δ′ A′} {t : Sub h Δ₀ A₀} {x : Sub h Δ′ A′} (t′ : Sub h Δ₀ A₀) → Path t x → Set₁
  Carry {x = x} t′ ψ = Σ _ λ x′ → Σ (Path t′ x′) λ ψ′ → Twin x x′ × (∀ H → walk ψ′ H ≡ walk ψ H)

  CarryL : ∀ {h Δ₀ B Δ′ A′} {ls : List (Lane h Δ₀ B)} {x : Sub h Δ′ A′} (ls′ : List (Lane h Δ₀ B)) → PathLanes ls x → Set₁
  CarryL {x = x} ls′ ψ =
    Σ _ λ x′ → Σ (PathLanes ls′ x′) λ ψ′ → Twin x x′ × (∀ {A} op (f : A → _) fl H → walkLanes op f fl H ψ′ ≡ walkLanes op f fl H ψ)

  -- A retag moves no field a walk reads, and every node it moves is a
  -- twin.
  retag-twin : ∀ {h Δ A} (g : Retag Δ) (s : Sub h Δ A) → Twin s (retag g s)
  retag-twin g (pendingˢ s q)                          = twin-same same
  retag-twin g (coldˢ s hd ph)                         = twin-same same
  retag-twin g (ofˢ p i xs)                            = twin-same same
  retag-twin g doneˢ                                   = twin-same same
  retag-twin g (mapˢ f s)                              = twin-same same-map
  retag-twin g (scanˢ f r s)                           = twin-same same-scan
  retag-twin g (takeWhileˢ i p c k tk s)               = twin-same same-take
  retag-twin g (flatMapˢ op f fl oc k r pl so ls)      = twin-same same-flat
  retag-twin g (connectˢ S c b kb k fd rp e rt src bd) = twin-same same-connect
  retag-twin g (joinˢ j sk l x st)                     = twin-join
  retag-twin g (deferˢ k s)                            = twin-same same-defer

  mutual
    retag-carry : ∀ {h Δ A Δ′ A′} (g : Retag Δ) {s : Sub h Δ A} {x : Sub h Δ′ A′} (ψ : Path s x) → Carry (retag g s) ψ
    retag-carry g {s} here = _ , here , retag-twin g s , λ H → refl
    retag-carry g (in-map ψ) with retag-carry g ψ
    ... | _ , ψ′ , tw , we = _ , in-map ψ′ , tw , λ H → we _
    retag-carry g (in-scan ψ) with retag-carry g ψ
    ... | _ , ψ′ , tw , we = _ , in-scan ψ′ , tw , λ H → we _
    retag-carry g (in-take ψ) with retag-carry g ψ
    ... | _ , ψ′ , tw , we = _ , in-take ψ′ , tw , λ H → we _
    retag-carry g (in-outer ψ) with retag-carry g ψ
    ... | _ , ψ′ , tw , we = _ , in-outer ψ′ , tw , λ H → we _
    retag-carry g (in-lanes {op = op} {f = f} {fl = fl} ψ) with retag-carryᴸ g ψ
    ... | _ , ψ′ , tw , we = _ , in-lanes ψ′ , tw , λ H → we op f fl H
    retag-carry g (in-source ψ) with retag-carry g ψ
    ... | _ , ψ′ , tw , we = _ , in-source ψ′ , tw , λ H → we _
    retag-carry g (in-body ψ) with retag-carry (keep g) ψ
    ... | _ , ψ′ , tw , we = _ , in-body ψ′ , tw , λ H → we _
    retag-carry g (in-defer ψ) with retag-carry g ψ
    ... | _ , ψ′ , tw , we = _ , in-defer ψ′ , tw , λ H → we _

    retag-carryᴸ : ∀ {h Δ B Δ′ A′} (g : Retag Δ) {ls : List (Lane h Δ B)} {x : Sub h Δ′ A′} (ψ : PathLanes ls x) → CarryL (retagᴸ g ls) ψ
    retag-carryᴸ g (this-lane ψ) with retag-carry g ψ
    ... | _ , ψ′ , tw , we = _ , this-lane ψ′ , tw , λ op f fl H → we _
    retag-carryᴸ g (next-lane ψ) with retag-carryᴸ g ψ
    ... | _ , ψ′ , tw , we = _ , next-lane ψ′ , tw , we

  -- Beneath the kin: every child kept, a lane shifted one along, a body
  -- retagged.
  kin-carry : ∀ {h Δ A Δ′ A′} {u v : Sub h Δ A} {x : Sub h Δ′ A′} → Kin u v → (ψ : Path u x) → Carry v ψ
  kin-carry kn here                       = _ , here , twin-kin kn , λ H → refl
  kin-carry kin-end (in-take ψ)           = _ , in-take ψ , twin-same same , λ H → refl
  kin-carry kin-pool (in-outer ψ)         = _ , in-outer ψ , twin-same same , λ H → refl
  kin-carry kin-pool (in-lanes ψ)         = _ , in-lanes ψ , twin-same same , λ H → refl
  kin-carry kin-lane (in-outer ψ)         = _ , in-outer ψ , twin-same same , λ H → refl
  kin-carry kin-lane (in-lanes ψ)         = _ , in-lanes (next-lane ψ) , twin-same same , λ H → refl
  kin-carry kin-feed (in-source ψ)        = _ , in-source ψ , twin-same same , λ H → refl
  kin-carry (kin-feed {g = g}) (in-body ψ) with retag-carry g ψ
  ... | _ , ψ′ , tw , we = _ , in-body ψ′ , tw , λ H → we _
  kin-carry kin-fin (in-source ψ)         = _ , in-source ψ , twin-same same , λ H → refl
  kin-carry (kin-fin {g = g}) (in-body ψ) with retag-carry g ψ
  ... | _ , ψ′ , tw , we = _ , in-body ψ′ , tw , λ H → we _

  -- Anywhere in the tree: off the kin's path, the same node; on it, the
  -- same node but for the child the path takes.
  mutual
    carry : ∀ {h Δ₀ A₀ Δ A Δ′ A′} {t : Sub h Δ₀ A₀} {u v : Sub h Δ A} {x : Sub h Δ′ A′} → Kin u v → (ρ : Path t u) → (ψ : Path t x) → Carry (plant ρ v) ψ
    carry kn here ψ = kin-carry kn ψ
    carry kn (in-map ρ) here = _ , here , twin-same same-map , λ H → refl
    carry kn (in-map ρ) (in-map ψ) with carry kn ρ ψ
    ... | _ , ψ′ , tw , we = _ , in-map ψ′ , tw , λ H → we _
    carry kn (in-scan ρ) here = _ , here , twin-same same-scan , λ H → refl
    carry kn (in-scan ρ) (in-scan ψ) with carry kn ρ ψ
    ... | _ , ψ′ , tw , we = _ , in-scan ψ′ , tw , λ H → we _
    carry kn (in-take ρ) here = _ , here , twin-same same-take , λ H → refl
    carry kn (in-take ρ) (in-take ψ) with carry kn ρ ψ
    ... | _ , ψ′ , tw , we = _ , in-take ψ′ , tw , λ H → we _
    carry kn (in-outer ρ) here = _ , here , twin-same same-flat , λ H → refl
    carry kn (in-outer ρ) (in-outer ψ) with carry kn ρ ψ
    ... | _ , ψ′ , tw , we = _ , in-outer ψ′ , tw , λ H → we _
    carry kn (in-outer ρ) (in-lanes ψ) = _ , in-lanes ψ , twin-same same , λ H → refl
    carry kn (in-lanes ρ) here = _ , here , twin-same same-flat , λ H → refl
    carry kn (in-lanes ρ) (in-outer ψ) = _ , in-outer ψ , twin-same same , λ H → refl
    carry kn (in-lanes ρ) (in-lanes {op = op} {f = f} {fl = fl} ψ) with carryᴸ kn ρ ψ
    ... | _ , ψ′ , tw , we = _ , in-lanes ψ′ , tw , λ H → we op f fl H
    carry kn (in-source ρ) here = _ , here , twin-same same-connect , λ H → refl
    carry kn (in-source ρ) (in-source ψ) with carry kn ρ ψ
    ... | _ , ψ′ , tw , we = _ , in-source ψ′ , tw , λ H → we _
    carry kn (in-source ρ) (in-body ψ) = _ , in-body ψ , twin-same same , λ H → refl
    carry kn (in-body ρ) here = _ , here , twin-same same-connect , λ H → refl
    carry kn (in-body ρ) (in-source ψ) = _ , in-source ψ , twin-same same , λ H → refl
    carry kn (in-body ρ) (in-body ψ) with carry kn ρ ψ
    ... | _ , ψ′ , tw , we = _ , in-body ψ′ , tw , λ H → we _
    carry kn (in-defer ρ) here = _ , here , twin-same same-defer , λ H → refl
    carry kn (in-defer ρ) (in-defer ψ) with carry kn ρ ψ
    ... | _ , ψ′ , tw , we = _ , in-defer ψ′ , tw , λ H → we _

    carryᴸ : ∀ {h Δ₀ B Δ A Δ′ A′} {ls : List (Lane h Δ₀ B)} {u v : Sub h Δ A} {x : Sub h Δ′ A′} → Kin u v → (ρ : PathLanes ls u) → (ψ : PathLanes ls x)
           → CarryL (plantᴸ ρ v) ψ
    carryᴸ kn (this-lane ρ) (this-lane ψ) with carry kn ρ ψ
    ... | _ , ψ′ , tw , we = _ , this-lane ψ′ , tw , λ op f fl H → we _
    carryᴸ kn (this-lane ρ) (next-lane ψ) = _ , next-lane ψ , twin-same same , λ op f fl H → refl
    carryᴸ kn (next-lane ρ) (this-lane ψ) = _ , this-lane ψ , twin-same same , λ op f fl H → refl
    carryᴸ kn (next-lane ρ) (next-lane ψ) with carryᴸ kn ρ ψ
    ... | _ , ψ′ , tw , we = _ , next-lane ψ′ , tw , we

  -- A leaf is no kin's.
  leaf-kin : ∀ {h Δ A} {x x′ : Sub h Δ A} → Leaf x → Kin x x′ → ⊥
  leaf-kin of-leaf   ()
  leaf-kin cold-leaf ()
  leaf-kin done-leaf ()
  leaf-kin join-leaf ()

  -- A connect's source subscribed: the kin is never a pending, so the
  -- source is still one after.
  postulate
    rehome-src : ∀ {h Δ A} {T : Sub h [] R} {u v : Sub h Δ A} → Kin u v → (ρ : Path T u)
               → ∀ {Δ′ A′ B} {S c b kb k fd e s₁ q rp rt} {bd : Sub h (A′ ∷ Δ′) B}
               → (π : Path T (connectˢ S c b kb k fd rp e rt (pendingˢ {Δ = Δ′} s₁ q) bd))
               → Σ (Call (plant ρ v)) λ k′ → code k′ ≡ code (srcC π)

  -- A call aimed anywhere in the tree, aimed alike after: its code reads
  -- its node's fields and the walk to it, and a kin moves neither.  A
  -- cold likewise.
  rehome : ∀ {h Δ A} {T : Sub h [] R} {u v : Sub h Δ A} → Kin u v → (ρ : Path T u) → (k : Call T) → Σ (Call (plant ρ v)) λ k′ → code k′ ≡ code k
  rehome kn ρ (emitC {i = i} {xs} π) with carry kn ρ π
  ... | _ , π′ , twin-same same , we = emitC π′ , cong (λ W → emitAll (Here.obs W) i xs) (we top)
  ... | _ , π′ , twin-kin () , we
  rehome kn ρ (kontC {u = x} lf π) with carry kn ρ π
  ... | _ , π′ , twin-same same , we = kontC lf π′ , cong (λ W → Here.kont W sameʰ (unsubscribing (unsub x))) (we top)
  ... | _ , π′ , twin-kin kn′ , we = ⊥-elim (leaf-kin lf kn′)
  ... | _ , π′ , twin-join , we = kontC join-leaf π′ , cong (λ W → Here.kont W sameʰ (unsubscribing (unsub x))) (we top)
  rehome kn ρ (take1C {c = c} π) with carry kn ρ π
  ... | _ , π′ , twin-same same , we      = take1C π′ , cong (λ W → under last (Observer.complete (Here.obs W)) (Kit.cut c)) (we top)
  ... | _ , π′ , twin-same same-take , we = take1C π′ , cong (λ W → under last (Observer.complete (Here.obs W)) (Kit.cut c)) (we top)
  ... | _ , π′ , twin-kin () , we
  rehome kn ρ (take2C π) with carry kn ρ π
  ... | _ , π′ , twin-same same , we      = take2C π′ , refl
  ... | _ , π′ , twin-same same-take , we = take2C π′ , refl
  ... | _ , π′ , twin-kin () , we
  rehome kn ρ (bodyC π) with carry kn ρ π
  ... | _ , π′ , twin-same same , we         = bodyC π′ , refl
  ... | _ , π′ , twin-same same-connect , we = bodyC π′ , refl
  ... | _ , π′ , twin-kin kin-feed , we      = bodyC π′ , refl
  ... | _ , π′ , twin-kin kin-fin , we       = bodyC π′ , refl
  rehome kn ρ (feedC π) with carry kn ρ π
  ... | _ , π′ , twin-same same , we         = feedC π′ , refl
  ... | _ , π′ , twin-same same-connect , we = feedC π′ , refl
  ... | _ , π′ , twin-kin () , we
  rehome kn ρ (finC π) with carry kn ρ π
  ... | _ , π′ , twin-same same , we         = finC π′ , refl
  ... | _ , π′ , twin-same same-connect , we = finC π′ , refl
  ... | _ , π′ , twin-kin () , we
  rehome kn ρ (srcC π) = rehome-src kn ρ π

  recold : ∀ {h Δ A} {T : Sub h [] R} {u v : Sub h Δ A} → Kin u v → (ρ : Path T u)
         → ∀ {Δ′ A′ s hd ph} → Path T (coldˢ {Δ = Δ′} {A′} s hd ph) → Path (plant ρ v) (coldˢ {Δ = Δ′} {A′} s hd ph)
  recold kn ρ ψ with carry kn ρ ψ
  ... | _ , ψ′ , twin-same same , _ = ψ′
  ... | _ , ψ′ , twin-kin () , _

  rehomes : ∀ {h Δ A} {T : Sub h [] R} {u v : Sub h Δ A} → Kin u v → (ρ : Path T u) → List (Call T) → List (Call (plant ρ v))
  rehomes kn ρ = mapList (λ k → proj₁ (rehome kn ρ k))

  rehomes-code : ∀ {h Δ A} {T : Sub h [] R} {u v : Sub h Δ A} (kn : Kin u v) (ρ : Path T u) (ks : List (Call T)) → ⟦ rehomes kn ρ ks ⟧ᶜ ≡ ⟦ ks ⟧ᶜ
  rehomes-code kn ρ []       = refl
  rehomes-code kn ρ (k ∷ ks) = cong₂ _>>ᴬ_ (proj₂ (rehome kn ρ k)) (rehomes-code kn ρ ks)

  -- A burst read by its cold's fields alone: the same burst after.
  reburst : ∀ {h Δ A} {T : Sub h [] R} {u v : Sub h Δ A} → Kin u v → (ρ : Path T u) → ∀ {b} → BurstAs T b → BurstAs (plant ρ v) b
  reburst kn ρ (playsAs π) = playsAs (recold kn ρ π)
  reburst kn ρ (firesAs π) = firesAs (recold kn ρ π)
  reburst kn ρ overAs      = overAs

  reheld : ∀ {h Δ A} {T : Sub h [] R} {u v : Sub h Δ A} {ρ : Path T u} {w} {K : Stack w ⊤} → Held T K → Held (plant ρ v) K
  reheld bottomᴴ = bottomᴴ
  reheld restᴴ   = restᴴ

  -- THE STACK, CARRIED: every frame's calls rehomed, each frame where it
  -- was.
  restack : ∀ {h Δ A} {T : Sub h [] R} {u v : Sub h Δ A} → Kin u v → (ρ : Path T u)
          → ∀ {w p bs} {σ : w ⊑ h} {K : Stack w ⊤} → StackAs T p σ K bs → StackAs (plant ρ v) p σ K bs
  restack kn ρ bottomAs                               = bottomAs
  restack kn ρ (restAs {m = m} {σ = σ} ks e K)        =
    restAs (rehomes kn ρ ks) (subst (λ X → wkAct σ m ≗ X) (sym (rehomes-code kn ρ ks)) e) (restack kn ρ K)
  restack kn ρ (backAs q {m = m} {σ = σ} ks lt e K)   =
    backAs q (rehomes kn ρ ks) lt (subst (λ X → wkAct σ m ≗ X) (sym (rehomes-code kn ρ ks)) e) (restack kn ρ K)
  restack {v = v} kn ρ (reholdAs b hd K)              = reholdAs (reburst kn ρ b) (reheld {v = v} {ρ = ρ} hd) (restack kn ρ K)

  reclocked : ∀ {h Δ A} {T : Sub h [] R} {u v : Sub h Δ A} (kn : Kin u v) (ρ : Path T u) {n b} (x : BurstAs T b)
            → BurstClocked T n x → BurstClocked (plant ρ v) n (reburst kn ρ x)
  reclocked kn ρ (playsAs π) c = c
  reclocked kn ρ (firesAs π) c = c
  reclocked kn ρ overAs      c = c

  reticked : ∀ {h Δ A} {T : Sub h [] R} {u v : Sub h Δ A} (kn : Kin u v) (ρ : Path T u) {n w p bs} {σ : w ⊑ h} {K : Stack w ⊤}
             (sk : StackAs T p σ K bs) → Ticked T n sk → Ticked (plant ρ v) n (restack kn ρ sk)
  reticked kn ρ bottomAs             c        = c
  reticked kn ρ (restAs ks e K)      (c , cs) = c , reticked kn ρ K cs
  reticked kn ρ (backAs q ks lt e K) (c , cs) = c , reticked kn ρ K cs
  reticked kn ρ (reholdAs b hd K)    (c , cs) = reclocked kn ρ b c , reticked kn ρ K cs

  -- WHAT IS OWED, CARRIED: the kin's own call ahead of the run's, rehomed;
  -- every other clause aimed at a node the kin keeps.
  -- One clause per field: a node of the planted tree is the kin, beneath
  -- it, or an old node but for its children (`unplant`); the old
  -- clause's call, rehomed, is the new one's.
  module Rerun {h} (H : Heapᴹ h) {T : Sub h [] R} {Δ A} {u v : Sub h Δ A} (kn : Kin u v) (ρ : Path T u)
               {w p bs} {σ : w ⊑ h} {K : Stack w ⊤} (sk : StackAs T p σ K bs) (ks : List (Call T)) {act act′ : Act h ⊤} {e : act ≗ ⟦ ks ⟧ᶜ}
               (e′ : act′ ≗ ⟦ owed kn ρ ++ rehomes kn ρ ks ⟧ᶜ) (ow : Owing kn p) (old : Owned H T (runAs ks e sk)) where
    open At H
    T′ = plant ρ v
    ca′ = runAs (owed kn ρ ++ rehomes kn ρ ks) e′ (restack kn ρ sk)
    open StrongAgainst.Against R T′ using (agenda; bursts; begins; Placed)

    postulate
      run-ofs    : ∀ {Δ′ A′ q i xs} (π : Path T′ (ofˢ {Δ = Δ′} {A′} q i xs)) → (q , emitC π) ∈ᴸ agenda ca′
      run-plays  : ∀ {Δ′ A′ s hd τ r i u′} {b : Frame A′ u′} (π : Path T′ (coldˢ {Δ = Δ′} s hd (playing τ r i b)))
                 → spentʰ hd ≡ false → spot π ∈ᴸ bursts ca′
      run-fires  : ∀ {Δ′ A′ s hd τ e₁ u′} {m : From A′ u′} (π : Path T′ (coldˢ {Δ = Δ′} s hd (fired τ e₁ m)))
                 → spentʰ hd ≡ false → spot π ∈ᴸ bursts ca′
      run-begun  : ∀ {Δ′ A′ s q} (π : Path T′ (pendingˢ {Δ = Δ′} {A′} s q)) → spot π ∈ᴸ begins ca′
      run-ends   : ∀ {Δ′ A′ i p′ c k q n} {s : Sub h Δ′ A′} (π : Path T′ (takeWhileˢ i p′ c k (ending q n) s))
                 → val (Kit.live c) ≡ true → (q , take1C π) ∈ᴸ agenda ca′
      run-cuts   : ∀ {Δ′ A′ i p′ c k} {s : Sub h Δ′ A′} (π : Path T′ (takeWhileˢ i p′ c k taken s))
                 → val (Kit.live c) ≡ true → Σ Pos λ q → (q , take2C π) ∈ᴸ agenda ca′
      run-feeds  : ∀ {Δ′ A′ B S c b kb k x q ss e₁ rp rt} {s : Sub h Δ′ A′} {bd : Sub h (A′ ∷ Δ′) B}
                 → (π : Path T′ (connectˢ S c b kb k (feeding x q ss) rp e₁ rt s bd)) → (q , feedC π) ∈ᴸ agenda ca′
      run-fins   : ∀ {Δ′ A′ B S c b kb k q ss e₁ rp rt} {s : Sub h Δ′ A′} {bd : Sub h (A′ ∷ Δ′) B}
                 → (π : Path T′ (connectˢ S c b kb k (finishing q ss) rp e₁ rt s bd)) → (q , finC π) ∈ᴸ agenda ca′
      run-bodies : ∀ {Δ′ A′ B S c b kb k fd e₁ rp rt q} {s : Sub h Δ′ A′} {bd : Sub h (A′ ∷ Δ′) B}
                 → (π : Path T′ (connectˢ S c b kb k fd rp e₁ rt s bd)) → (q , bodyC π) ∈ᴸ agenda ca′ → part bd ≡ nothing
      run-placed : All Placed (agenda ca′)

  -- WHAT IS OWED, CARRIED: the kin's own call ahead of the run's, rehomed;
  -- every other clause aimed at a node the kin keeps.
  owned-run : ∀ {h} {H : Heapᴹ h} {T : Sub h [] R} {Δ A} {u v : Sub h Δ A} (kn : Kin u v) (ρ : Path T u)
              {w p bs} {σ : w ⊑ h} {K : Stack w ⊤} (sk : StackAs T p σ K bs) (ks : List (Call T)) {act act′ : Act h ⊤} {e : act ≗ ⟦ ks ⟧ᶜ}
              (e′ : act′ ≗ ⟦ owed kn ρ ++ rehomes kn ρ ks ⟧ᶜ) → Owing kn p
            → Owned H T (runAs ks e sk) → Owned H (plant ρ v) (runAs (owed kn ρ ++ rehomes kn ρ ks) e′ (restack kn ρ sk))
  owned-run {H = H} kn ρ sk ks {e = e} e′ ow old = record
    { ofs    = Rr.run-ofs
    ; plays  = Rr.run-plays
    ; fires  = Rr.run-fires
    ; begun  = Rr.run-begun
    ; ends   = Rr.run-ends
    ; cuts   = Rr.run-cuts
    ; feeds  = Rr.run-feeds
    ; fins   = Rr.run-fins
    ; bodies = Rr.run-bodies
    ; placed = Rr.run-placed }
    where module Rr = Rerun H kn ρ sk ks {e = e} e′ ow old

  -- TWO NODES OF ONE TREE: one beneath the other, or no name shared.
  data Fork {h Δ A Δ′ A′} (u : Sub h Δ A) (x : Sub h Δ′ A′) : Set₁ where
    under  : Path u x → Fork u x
    above  : Path x u → Fork u x
    beside : (∀ {n} → n ∈ᴸ names x → All (n ≢_) (names u)) → Fork u x

  mutual
    fork : ∀ {h Δ A Δ₁ A₁ Δ₂ A₂} {t : Sub h Δ A} {u : Sub h Δ₁ A₁} {x : Sub h Δ₂ A₂} → AllPairs _≢_ (names t) → Path t u → Path t x → Fork u x
    fork ps here ψ = under ψ
    fork ps ρ here = above ρ
    fork ps (in-map ρ) (in-map ψ) = fork ps ρ ψ
    fork (_ ∷ ps) (in-scan ρ) (in-scan ψ) = fork ps ρ ψ
    fork ps (in-take {c = c} {k} ρ) (in-take ψ) = fork (pairs-r (quietName k) (pairs-r (cutNames c) ps)) ρ ψ
    fork ps (in-outer {fl = fl} {oc} {k} {r} {t = so} ρ) (in-outer ψ) =
      fork (proj₁ (pairs-split (names so) (pairs-r ((_ , r) ∷ []) (pairs-r (quietName k) (pairs-r (cutNames oc) (pairs-r (flatNames fl) ps)))))) ρ ψ
    fork ps (in-outer {fl = fl} {oc} {k} {r} {t = so} ρ) (in-lanes ψ) =
      beside (λ m → narrow (names-path ρ) (apart-l (names so) (pairs-r ((_ , r) ∷ []) (pairs-r (quietName k) (pairs-r (cutNames oc) (pairs-r (flatNames fl) ps)))) (lanes-path ψ m)))
    fork ps (in-lanes {fl = fl} {oc} {k} {r} {t = so} ρ) (in-outer ψ) =
      beside (λ m → narrow (lanes-path ρ) (apart-r (names so) (pairs-r ((_ , r) ∷ []) (pairs-r (quietName k) (pairs-r (cutNames oc) (pairs-r (flatNames fl) ps)))) (names-path ψ m)))
    fork ps (in-lanes {fl = fl} {oc} {k} {r} {t = so} ρ) (in-lanes ψ) =
      forkL (pairs-r (names so) (pairs-r ((_ , r) ∷ []) (pairs-r (quietName k) (pairs-r (cutNames oc) (pairs-r (flatNames fl) ps))))) ρ ψ
    fork ps (in-source {S = S} {c} {b} {kb} {k} {t = src} ρ) (in-source ψ) =
      fork (proj₁ (pairs-split (names src) (pairs-r (quietName k) (pairs-r (quietName kb) (pairs-r ((_ , b) ∷ []) (pairs-r (cutNames c) (pairs-r (subjectNames S) ps))))))) ρ ψ
    fork ps (in-source {S = S} {c} {b} {kb} {k} {t = src} ρ) (in-body ψ) =
      beside (λ m → narrow (names-path ρ) (apart-l (names src) (pairs-r (quietName k) (pairs-r (quietName kb) (pairs-r ((_ , b) ∷ []) (pairs-r (cutNames c) (pairs-r (subjectNames S) ps))))) (names-path ψ m)))
    fork ps (in-body {S = S} {c} {b} {kb} {k} {t = src} ρ) (in-source ψ) =
      beside (λ m → narrow (names-path ρ) (apart-r (names src) (pairs-r (quietName k) (pairs-r (quietName kb) (pairs-r ((_ , b) ∷ []) (pairs-r (cutNames c) (pairs-r (subjectNames S) ps))))) (names-path ψ m)))
    fork ps (in-body {S = S} {c} {b} {kb} {k} {t = src} ρ) (in-body ψ) =
      fork (pairs-r (names src) (pairs-r (quietName k) (pairs-r (quietName kb) (pairs-r ((_ , b) ∷ []) (pairs-r (cutNames c) (pairs-r (subjectNames S) ps)))))) ρ ψ
    fork ps (in-defer {k = k} ρ) (in-defer ψ) = fork (pairs-r (quietName k) ps) ρ ψ

    forkL : ∀ {h Δ B Δ₁ A₁ Δ₂ A₂} {ls : List (Lane h Δ B)} {u : Sub h Δ₁ A₁} {x : Sub h Δ₂ A₂} → AllPairs _≢_ (laneNames ls) → PathLanes ls u → PathLanes ls x → Fork u x
    forkL ps (this-lane {c = c} {k} {t = s} ρ) (this-lane ψ) = fork (proj₁ (pairs-split (names s) (pairs-r (quietName k) (pairs-r (cutNames c) ps)))) ρ ψ
    forkL ps (this-lane {c = c} {k} {t = s} ρ) (next-lane ψ) =
      beside (λ m → narrow (names-path ρ) (apart-l (names s) (pairs-r (quietName k) (pairs-r (cutNames c) ps)) (lanes-path ψ m)))
    forkL ps (next-lane {l = lane c k s} ρ) (this-lane ψ) =
      beside (λ m → narrow (lanes-path ρ) (apart-r (names s) (pairs-r (quietName k) (pairs-r (cutNames c) ps)) (names-path ψ m)))
    forkL ps (next-lane {l = lane c k s} ρ) (next-lane ψ) = forkL (pairs-r (names s) (pairs-r (quietName k) (pairs-r (cutNames c) ps))) ρ ψ

  -- Every take beneath a node live after only if live before.
  Lives : ∀ {h} (H H′ : Heapᴹ h) {Δ A} (u : Sub h Δ A) → Set₁
  Lives {h} H H′ u = ∀ {Δ′ A′ i p c k tk} {s : Sub h Δ′ A′} → Path u (takeWhileˢ i p c k tk s) → At.val H′ (Kit.live c) ≡ true → At.val H (Kit.live c) ≡ true

  -- A write at names no take's switch beneath the node.
  lives-off : ∀ {h} {H H′ : Heapᴹ h} {ns} → Off H H′ ns → ∀ {Δ A} {u : Sub h Δ A}
            → (∀ {Δ′ A′ i p c k tk} {s : Sub h Δ′ A′} → Path u (takeWhileˢ i p c k tk s) → All (_≢_ (_ , Kit.live c)) ns)
            → Lives H H′ u
  lives-off off nl {c = c} ψ e = trans (sym (cong lower (off (Kit.live c) (nl ψ)))) e

  -- A write at a node's cells that revives no part and no take beneath
  -- it.
  record Gone {h} (H H′ : Heapᴹ h) {Δ A} (u : Sub h Δ A) : Set₁ where
    field
      gone-part : ∀ {Δ′ A′} {x : Sub h Δ′ A′} → Path u x → At.part H x ≡ nothing → At.part H′ x ≡ nothing
      gone-live : Lives H H′ u
      gone-held : ∀ (hd : Handle h) → At.spentʰ H′ hd ≡ At.spentʰ H hd

  -- A cell written leaves every handle as it was.
  store-held : ∀ {h t} (H : Heapᴹ h) (i : h ∋ cell t) {x} (hd : Handle h) → At.spentʰ (store H i x) hd ≡ At.spentʰ H hd
  store-held H i hd with look-either H i hd
  ... | inj₁ ()
  ... | inj₂ e = cong lower e

  -- THE NODE'S HEADS, MOVED: no part revived, no joiner left untold that
  -- was told, and below it every part heading no sooner than `q`.
  record Heading {h} (H H′ : Heapᴹ h) (q : Pos) {Δ A} (u v : Sub h Δ A) : Set₁ where
    field
      head-revive : is-just (At.part H′ v) ≡ true → is-just (At.part H u) ≡ true
      head-told   : ∀ {A′} (i : A′ ∈ᴸ Δ) {b₀ b′} → At.part H u ≡ just b₀ → At.part H′ v ≡ just b′ → ∀ {x} → x ∈ᴸ untold i b′ → x ∈ᴸ untold i b₀
      head-below  : Each H (Heads q) u → Each H′ (Heads q) v

  -- THE NODE'S TIES, MOVED: no part revived, what it leaves running
  -- twinned as before, and below it every tie kept.
  record Lingering {h} (H H′ : Heapᴹ h) {Δ A} (u v : Sub h Δ A) : Set₁ where
    field
      ling-revive : is-just (At.part H′ v) ≡ true → is-just (At.part H u) ≡ true
      ling-rested : ∀ {C} → Twin (At.leftover H {B = C} u) (At.leftover H′ {B = C} v)
      ling-below  : Lingers H u → Lingers H′ v

  -- THE FRAME: a write at the node's own names, its node replanted to
  -- `v`.  No ancestor reads its path child's cells, only its part, its
  -- heads and its leftover, which the node's premises carry; every part
  -- beside the path reads alike.
  module Shift {h} (H H′ : Heapᴹ h) {T : Sub h [] R} {Δ A} {u : Sub h Δ A} (ρ : Path T u)
               {ns : List (Name h)} (off : Off H H′ ns) (mine : All (_∈ᴸ names u) ns) (fs : AllPairs _≢_ (names T)) where
    private
      offU : Off H H′ (names u)
      offU j a = off j (map (λ m → lookupᴬ a m) mine)

      gone-just : ∀ {a} {X : Set a} {x x′ : Maybe X} → (is-just x′ ≡ true → is-just x ≡ true) → x ≡ nothing → x′ ≡ nothing
      gone-just {x′ = nothing} f e = refl
      gone-just {x′ = just _} f refl with f refl
      ... | ()

      just-back : ∀ {a} {X : Set a} {x x′ : Maybe X} → (x ≡ nothing → x′ ≡ nothing) → is-just x′ ≡ true → is-just x ≡ true
      just-back {x = just _} f j = refl
      just-back {x = nothing} {x′ = just _} f j with f refl
      ... | ()

    -- No part anywhere in the tree revived: beneath the node by the
    -- write, above it by the walk, beside it by the names.
    part-kept : Gone H H′ u → ∀ {Δ′ A′} {x : Sub h Δ′ A′} → Path T x → At.part H x ≡ nothing → At.part H′ x ≡ nothing
    part-kept gn {x = x} ψ e with fork fs ρ ψ
    ... | under ψ′ = Gone.gone-part gn ψ′ e
    ... | above ρ′ =
      gone-just (subst (λ y → is-just (At.part H′ y) ≡ true → is-just (At.part H x) ≡ true) (plant-self ρ′)
                       (Walk.revive H H′ {u = u} u offU (just-back (Gone.gone-part gn here)) ρ′ (fresh-path ψ fs))) e
    ... | beside dj = trans (part-alike H H′ x (λ j m → offU j (dj m))) e

    -- No take anywhere in the tree revived.
    live-kept : Gone H H′ u → Lives H H′ T
    live-kept gn {c = c} {k = k} ψ e with fork fs ρ ψ
    ... | under ψ′ = Gone.gone-live gn ψ′ e
    ... | above here = Gone.gone-live gn here e
    ... | above (in-take ρ″) =
      trans (sym (cong lower (offU (Kit.live c) (narrow (λ m → ++⁺ʳ (quietName k) (names-path ρ″ m)) (apart-r (cutNames c) (fresh-path ψ fs) (here refl)))))) e
    ... | beside dj = trans (sym (cong lower (offU (Kit.live c) (dj (here refl))))) e

    -- WHAT IS OWED, KEPT: the agenda is the tree's, and the heap is read
    -- only for a take's switch and a body's part.
    wr-owned : Gone H H′ u → ∀ {p ctl bs} {ca : CtlAs T p ctl bs} → Owned H T ca → Owned H′ T ca
    wr-owned gn ow = record
      { ofs    = Owned.ofs ow
      ; plays  = λ {hd = hd} π sp → Owned.plays ow π (trans (sym (Gone.gone-held gn hd)) sp)
      ; fires  = λ {hd = hd} π sp → Owned.fires ow π (trans (sym (Gone.gone-held gn hd)) sp)
      ; begun  = Owned.begun ow
      ; ends   = λ π lv → Owned.ends ow π (live-kept gn π lv)
      ; cuts   = λ π lv → Owned.cuts ow π (live-kept gn π lv)
      ; feeds  = Owned.feeds ow
      ; fins   = Owned.fins ow
      ; bodies = λ π m → part-kept gn (π ⊕ in-body here) (Owned.bodies ow π m)
      ; placed = Owned.placed ow
      }

    shift-behind : (v : Sub h Δ A) → ∀ {q} → Untold H q T → Ended H T → Heading H H′ q u v → Each H (Heads q) T → Each H′ (Heads q) (plant ρ v)
    shift-behind v {q} ut en hd ev =
      Walk.Behind.shiftE H H′ {u = u} v offU (Heading.head-revive hd) (λ i e₀ e′ → Heading.head-told hd i e₀ e′) q (Heading.head-below hd) ρ fs ev ut en

    -- Every flag named above the node still unset, every other reading
    -- its outer as before; the names the write let go, below the node.
    shift-flags : (v : Sub h Δ A) {ns₀ : List (Name h)} → (∀ {n} → n ∈ᴸ ns₀ → n ∈ᴸ names u)
                → (is-just (At.part H′ v) ≡ true → is-just (At.part H u) ≡ true)
                → (DoneBy H u (outers ρ ++ ns₀) → DoneBy H′ v (outers ρ)) → DoneBy H T (outers ρ ++ ns₀) → DoneBy H′ (plant ρ v) (outers ρ)
    shift-flags v {ns₀} nu rv fb d = Walk.Flags.shiftF H H′ {u = u} v offU rv (outers ρ) ns₀ nu fb ρ fs (λ m → m) d

    shift-lingers : (v : Sub h Δ A) → Ended H T → Lingering H H′ u v → Lingers H T → Lingers H′ (plant ρ v)
    shift-lingers v en lg l =
      Walk.Ties.shiftLg H H′ {u = u} v offU (Lingering.ling-revive lg) (Lingering.ling-rested lg) (Lingering.ling-below lg) ρ fs l en

  -- A cascade's root lies two labels down, a tick then a creation: past
  -- a position, it is past any of that position's children, unless the
  -- position is the run's top and the child a later tick's.
  private
    ix-le : ∀ {i d e} → i ≤ d → (ix i ∷ []) <ᵖ (ix d ∷ sub e ∷ []) ≡ true
    ix-le {d = zero}  z≤n     = refl
    ix-le {d = suc d} z≤n     = refl
    ix-le {e = e}     (s≤s le) = ix-le {e = e} le

    unrooted : ∀ {x y : Label} {d e} (q ys : Pos) → (x ∷ y ∷ q) <ᵖ (ix d ∷ sub e ∷ []) ≡ true → ix d ∷ sub e ∷ [] ≡ x ∷ y ∷ q ++ ys → ⊥
    unrooted {d = d} {e} [] [] lt refl with () ← trans (sym lt) (<ᵖ-irrefl (ix d ∷ sub e ∷ []))
    unrooted []      (_ ∷ _) lt ()
    unrooted (_ ∷ _) ys      lt ()

    under-root : ∀ q i d e → (q ≡ [] → i ≤ d) → q <ᵖ (ix d ∷ sub e ∷ []) ≡ true → (q ++ [ ix i ]) <ᵖ (ix d ∷ sub e ∷ []) ≡ true
    under-root []          i d e le lt = ix-le {e = e} (le refl)
    under-root (x ∷ [])    i d e le lt = lt
    under-root (x ∷ y ∷ q) i d e le lt = <ᵖ-apart (x ∷ y ∷ q) (ix d ∷ sub e ∷ []) [ ix i ] lt (λ ys → unrooted q ys lt)

  -- Every timer past a position past one of its children at `ix i`.
  ahead-under : ∀ {h} q i {clk} {ts : List (Timer h)} → (q ≡ [] → i ≤ clk) → All (λ tm → clk ≤ Timer.due tm × q <ᵖ cascade tm ≡ true) ts
              → All (λ tm → clk ≤ Timer.due tm × (q ++ [ ix i ]) <ᵖ cascade tm ≡ true) ts
  ahead-under q i top = map λ { (le , lt) → le , under-root q i _ _ (λ e → ≤-trans (top e) le) lt }
