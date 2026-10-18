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
open import Data.Nat using (_≤_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤)
open import Data.Sum using (inj₁; inj₂)
open import Data.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Level using (lower)

open import denotation.MonotonicList using (Timeline; Pos; ix; _<ᵖ_)
import denotation.Unfold as U
open import operation.PureObservable using (Out; Pureᴾ; module Pure)
open import operation.AbstractObservable using (module Heap; module Run) renaming (module Machine to Shared)
open import adequacy.Strong using (module Strongly)
open import adequacy.Moves using (module Moving)
open import adequacy.Retag using (Retag; module Retagging)
open import adequacy.Torn using (module Tearing)
open import adequacy.Frame using (module Framing)
open import adequacy.Shift using (module Shifting)

module Replanting (R : Set) where
  open Shared Timeline (Out R) using (Heapᴹ; Stack; store)
  open Heap using (_⊑_; _∋_; Handle; cell)
  open Run (Pureᴾ R) using (Act; wkAct; _>>ᴬ_; module Kit)
  open Pure R using (Timer; cascade)
  open Strongly R using (Sub; Path; PathLanes; _⊕_; here; in-map; in-scan; in-take; in-outer; in-lanes; in-source; in-body; in-defer; this-lane; next-lane;
                         Lane; lane; Call; take1C; feedC; finC; code; coldˢ; takeWhileˢ; flatMapˢ; connectˢ; taking; ending; idle; feeding; finishing;
                         Owned; Queue; Each; Heads; Lingers; Pinned; Name; names; laneNames; cutNames; quietName; subjectNames; flatNames; module At; _≗_) renaming (⟦_⟧ to ⟦_⟧ᶜ)
  open Strongly.Against R using (StackAs; BurstAs; Held; bottomAs; restAs; backAs; reholdAs; playsAs; firesAs; overAs; bottomᴴ; restᴴ;
                                 BurstClocked; Ticked; CtlAs; runAs)
  open Moving R using (plant; plantᴸ; planted; pairs-r; pairs-split)
  open Retagging R using (retag)
  open Tearing R using (Off; look-either; fresh-path; part-alike; names-path; lanes-path; apart-r; apart-l; narrow)
  open Framing R using (Untold; Ended; untold)
  open Shifting R using (module Walk)

  -- A NODE'S KIN: what a move rewrites it to.  A take ended; a pool
  -- restaged; a connect's feed restaged from `idle`, its body's joiners
  -- retold.  Every kin keeps the node's names, its cells and every
  -- child's shape, so a call or a burst aimed anywhere in the tree aims
  -- at the same fields after.
  data Kin {h} : ∀ {Δ A} → Sub h Δ A → Sub h Δ A → Set₁ where
    kin-end  : ∀ {Δ A i p c k q n} {s : Sub h Δ A} → Kin (takeWhileˢ i p c k taking s) (takeWhileˢ i p c k (ending q n) s)
    kin-pool : ∀ {Δ A B op f fl oc k r pl pl′} {s : Sub h Δ A} {ls : List (Lane h Δ B)}
             → Kin (flatMapˢ op f fl oc k r pl s ls) (flatMapˢ op f fl oc k r pl′ s ls)
    kin-feed : ∀ {Δ A B S c b kb k x q ss rp e rt} {g : Retag (A ∷ Δ)} {s : Sub h Δ A} {bd : Sub h (A ∷ Δ) B}
             → Kin (connectˢ S c b kb k idle rp e rt s bd) (connectˢ S c b kb k (feeding x q ss) rp e rt s (retag g bd))
    kin-fin  : ∀ {Δ A B S c b kb k q ss rp e rt} {g : Retag (A ∷ Δ)} {s : Sub h Δ A} {bd : Sub h (A ∷ Δ) B}
             → Kin (connectˢ S c b kb k idle rp e rt s bd) (connectˢ S c b kb k (finishing q ss) rp e rt s (retag g bd))

  -- What the kin owes the agenda: an ended take its completion, a feed or
  -- a finish its delivery; a pool nothing.
  owed : ∀ {h Δ A} {T : Sub h [] R} {u v : Sub h Δ A} → Kin u v → (ρ : Path T u) → List (Call (plant ρ v))
  owed {v = v} kin-end  ρ = take1C (planted ρ v) ∷ []
  owed         kin-pool ρ = []
  owed {v = v} kin-feed ρ = feedC (planted ρ v) ∷ []
  owed {v = v} kin-fin  ρ = finC (planted ρ v) ∷ []

  -- Where what is owed runs: the position the kin was made at.
  Owing : ∀ {h Δ A} {u v : Sub h Δ A} → Kin u v → Pos → Set
  Owing (kin-end {q = q})  p = p ≡ q
  Owing kin-pool           p = ⊤
  Owing (kin-feed {q = q}) p = p ≡ q
  Owing (kin-fin {q = q})  p = p ≡ q

  -- A call aimed anywhere in the tree, aimed alike after: its code reads
  -- its node's fields and the walk to it, and a kin moves neither.  A
  -- cold likewise.
  postulate
    rehome : ∀ {h Δ A} {T : Sub h [] R} {u v : Sub h Δ A} → Kin u v → (ρ : Path T u) → (k : Call T) → Σ (Call (plant ρ v)) λ k′ → code k′ ≡ code k
    recold : ∀ {h Δ A} {T : Sub h [] R} {u v : Sub h Δ A} → Kin u v → (ρ : Path T u)
           → ∀ {Δ′ A′ s hd ph} → Path T (coldˢ {Δ = Δ′} {A′} s hd ph) → Path (plant ρ v) (coldˢ {Δ = Δ′} {A′} s hd ph)

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
  postulate
    owned-run : ∀ {h} {H : Heapᴹ h} {T : Sub h [] R} {Δ A} {u v : Sub h Δ A} (kn : Kin u v) (ρ : Path T u)
                {w p bs} {σ : w ⊑ h} {K : Stack w ⊤} (sk : StackAs T p σ K bs) (ks : List (Call T)) {act act′ : Act h ⊤} {e : act ≗ ⟦ ks ⟧ᶜ}
                (e′ : act′ ≗ ⟦ owed kn ρ ++ rehomes kn ρ ks ⟧ᶜ) → Owing kn p
              → Owned H T (runAs ks e sk) → Owned H (plant ρ v) (runAs (owed kn ρ ++ rehomes kn ρ ks) e′ (restack kn ρ sk))

  -- A path planted with the node it ends at is the tree.
  mutual
    plant-self : ∀ {h Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) → plant π u ≡ t
    plant-self here          = refl
    plant-self (in-map π)    rewrite plant-self π = refl
    plant-self (in-scan π)   rewrite plant-self π = refl
    plant-self (in-take π)   rewrite plant-self π = refl
    plant-self (in-outer π)  rewrite plant-self π = refl
    plant-self (in-lanes π)  rewrite plantᴸ-self π = refl
    plant-self (in-source π) rewrite plant-self π = refl
    plant-self (in-body π)   rewrite plant-self π = refl
    plant-self (in-defer π)  rewrite plant-self π = refl

    plantᴸ-self : ∀ {h Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (π : PathLanes ls u) → plantᴸ π u ≡ ls
    plantᴸ-self (this-lane π) rewrite plant-self π = refl
    plantᴸ-self (next-lane π) rewrite plantᴸ-self π = refl

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
  -- pinned as before, and below it every tie kept.
  record Lingering {h} (H H′ : Heapᴹ h) {Δ A} (u v : Sub h Δ A) : Set₁ where
    field
      ling-revive : is-just (At.part H′ v) ≡ true → is-just (At.part H u) ≡ true
      ling-rested : ∀ {C} → Pinned (U.restˢ {B = ⊤} (At.leftover H {B = C} u)) (U.restˢ {B = ⊤} (At.leftover H′ {B = C} v))
      ling-below  : Lingers H u → Lingers H′ v

  -- THE FRAME: a write at the node's own names, its node replanted to
  -- `v`.  No ancestor reads its path child's cells, only its part, its
  -- heads and its leftover, which the node's premises carry; every part
  -- beside the path reads alike.
  --
  -- `wr-queue` is stated bare: `Joined` reads the subjects' subscribers,
  -- and its `Silenced` clause quantifies over every flag cell, so a write
  -- of one the node owns reaches a clause no premise of the node's names.
  module Shift {h} (H H′ : Heapᴹ h) {T : Sub h [] R} {Δ A} {u : Sub h Δ A} (ρ : Path T u)
               {ns : List (Name h)} (off : Off H H′ ns) (mine : All (_∈ᴸ names u) ns) (fs : AllPairs _≢_ (names T)) where
    postulate
      wr-queue      : ∀ {q clk ts} → Queue H q clk ts T → Queue H′ q clk ts T

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

    shift-lingers : (v : Sub h Δ A) → Ended H T → Lingering H H′ u v → Lingers H T → Lingers H′ (plant ρ v)
    shift-lingers v en lg l =
      Walk.Ties.shiftLg H H′ {u = u} v offU (Lingering.ling-revive lg) (Lingering.ling-rested lg) (Lingering.ling-below lg) ρ fs l en

  -- Every timer past a position past one of its children at `ix i`.
  postulate
    ahead-under : ∀ {h} q i {clk} {ts : List (Timer h)} → All (λ tm → clk ≤ Timer.due tm × q <ᵖ cascade tm ≡ true) ts
                → All (λ tm → clk ≤ Timer.due tm × (q ++ [ ix i ]) <ᵖ cascade tm ≡ true) ts
