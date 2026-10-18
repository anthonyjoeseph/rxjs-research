{-# OPTIONS --guardedness #-}

-- A WORLD GROWN BY ALLOCATION: a tree weakened along it owes, holds and
-- reads what it did.
module adequacy.Weaken where

open import Data.List using (List; []; _∷_; _++_; [_]; length) renaming (map to mapᴸ)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (tabulate to tabulateᴬ; lookup to lookupᴬ; map to all-map)
open import Data.List.Relation.Unary.Any using () renaming (here to hereᴬ; there to thereᴬ)
open import Data.List.Relation.Unary.Any.Properties using () renaming (++⁻ to any-++⁻; ++⁺ˡ to any-++⁺ˡ; ++⁺ʳ to any-++⁺ʳ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁻ to all-++⁻)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_) renaming (map to pairs-map)
open import Data.List.Relation.Unary.Linked using (Linked; []; [-]; _∷_)
open import Data.List.Relation.Unary.AllPairs.Properties using () renaming (map⁺ to pairs-map⁺; ++⁺ to pairs-++⁺)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_; ↭-sym; ↭-trans; ↭-reflexive) renaming (refl to ↭-refl′; prep to ↭-prep′; swap to ↭-swap′; trans to ↭-trans′)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (All-resp-↭; shifts) renaming (++⁺ˡ to ↭-++⁺ˡ; ++⁺ʳ to ↭-++⁺ʳ)
open import Data.List.Properties using (map-++; ++-assoc) renaming (++-identityʳ to ++-idʳ)
open import Data.Maybe using (Maybe; just; nothing; is-just) renaming (map to mapMaybe)
open import Data.Nat using (_+_)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤₁; tt to tt₁)
open import Data.Bool using (_∧_; _∨_; true; false; if_then_else_)
open import Relation.Nullary using (¬_)
open import Level using (Lift; lift)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import denotation.MonotonicList using (Timeline; Frame; From; Pos; ix; last; tick; at; _<ᵖ_; <ᵖ-below) renaming (done to doneᶠᵐ; quiet to quietᶠᵐ)
open import denotation.MonotonicList using () renaming (sub to subᴾ)
import Tree as T
import denotation.Unfold as U
open import operation.Machine using (module Machine)
open import operation.PureObservable using (Out; Pureᴾ)
open import operation.AbstractObservable using (module Heap; module Run) renaming (module Machine to Shared)
open import adequacy.Strong using (module Strongly)
open import adequacy.Moves using (module Moving)
open import adequacy.Unsub using (module Unsubbing)
open import adequacy.Grow using (module Growing)
open import adequacy.Seq using (module Sequencing)
open import operation.PureObservable using (module Pure)

module Weakening (R : Set) where
  open Machine R using (wkPlaying)
  open Unsubbing R using (then)
  open Growing R using (wkTree; wkLanes; wkPath; wkFeed)
  open Sequencing R using (wkEnv-wk)
  open Pure R using (Timer; wkTimer; mapList; cascade)
  open Shared Timeline (Out R) using (Heapᴹ; ⟨_,_,_⟩; look; cbs; wkVal)
  open Heap using (World; _⊑_; _⨾_; _∋_; there; grow; wk∋; slot; Sink; Quiet; Handle) renaming (same to same⊑)
  open Run (Pureᴾ R) using (done; compile; Env; wkEnv; wkAct; module Kit; module FlatKit; Ref; wkR; wkEl; Observer; Kont; wkObs; wkKont)
  open Strongly R using (Sub; pendingˢ; ofˢ; mapˢ; takeWhileˢ; connectˢ; Lane; ending; taken; idle; feeding; finishing; Path; PathLanes; here; in-map; in-scan; in-take; in-outer; in-lanes; in-source; in-body; in-defer; this-lane; next-lane; Here; walk; top; coldˢ; _≗_; module At; Owned; Kernels; Meaning; Queue; Each; Lingers; pendings; rootObs; Owes; Begun; Settled; SettledLanes; Feed; Phase; timerOf; lanePendings; subjects; joiners; Tied; seen; seenL; isTaking; flatMapˢ; scanˢ; joinˢ; doneˢ; deferˢ; lane; CbRel; ≗-refl; taking)
  open Strongly.Against R using (StackAs; subAs; stackJobs; SrcOf; Ticked)
  open Strongly.Phase R using (waiting; playing; fired)
  open Moving R using (pend; pendᴸ)

  -- A WORLD GROWN BY ALLOCATION: every name the old heap held reads as it
  -- did, weakened.
  record Grows {h v} (τ : h ⊑ v) (H : Heapᴹ h) (H′ : Heapᴹ v) : Set₁ where
    field
      cells   : ∀ {t} (x : Ref h t) → At.val H′ (wkR τ x) ≡ wkEl t τ (At.val H x)
      slots   : ∀ {X} (s : Sink h X) → CbRel (cbs H′ (wk∋ τ s)) (wkVal (slot X) τ (cbs H s))
      stashes : ∀ (u : Quiet h) → look H′ (wk∋ τ u) ≗ wkAct τ (look H u)
      handles : ∀ (hd : Handle h) → At.spentʰ H′ (wk∋ τ hd) ≡ At.spentʰ H hd

  -- Two observers, part for part; two continuations, pointwise.
  ObsRel : ∀ {A w} → Observer A w → Observer A w → Set₁
  ObsRel o o′ = (∀ a → Observer.next o a ≗ Observer.next o′ a) × Observer.complete o ≗ Observer.complete o′ × Observer.closed o ≗ Observer.closed o′

  KontRel : ∀ {w} → Kont w → Kont w → Set₁
  KontRel {w} k k′ = ∀ {v} (σ : w ⊑ v) sub → k σ sub ≗ k′ σ sub

  -- A tree weakened owes what it did.
  mutual
    pend-grow : ∀ {h v Δ A} (τ : h ⊑ v) (t : Sub h Δ A) → pend (wkTree τ t) ≡ pend t
    pend-grow τ (pendingˢ s q)                       = refl
    pend-grow τ (coldˢ s hd ph)                      = refl
    pend-grow τ (ofˢ p i xs)                         = refl
    pend-grow τ doneˢ                                = refl
    pend-grow τ (mapˢ f t)                           = pend-grow τ t
    pend-grow τ (scanˢ f r t)                        = pend-grow τ t
    pend-grow τ (takeWhileˢ i p c k tk t)            = pend-grow τ t
    pend-grow τ (flatMapˢ op f fl oc k r pl t ls)    = cong₂ _+_ (pend-grow τ t) (pend-growᴸ τ ls)
    pend-grow τ (connectˢ S c b kb k fd q e rt s bd) = cong₂ _+_ (pend-grow τ s) (pend-grow τ bd)
    pend-grow τ (joinˢ j s fl x m)                   = refl
    pend-grow τ (deferˢ k t)                         = pend-grow τ t

    pend-growᴸ : ∀ {h v Δ B} (τ : h ⊑ v) (ls : List (Lane h Δ B)) → pendᴸ (wkLanes τ ls) ≡ pendᴸ ls
    pend-growᴸ τ []                 = refl
    pend-growᴸ τ (lane c k t ∷ ls) = cong₂ _+_ (pend-grow τ t) (pend-growᴸ τ ls)

  module Grown {h v} (τ : h ⊑ v) where
    postulate
      -- The stack, its calls aimed along the weakened tree.
      grow-stack  : ∀ {t : Sub h [] R} {p w} {σ : w ⊑ h} {K bs} → StackAs t p σ K bs
                  → StackAs (wkTree τ t) p (σ ⨾ τ) K (mapList (mapMaybe (wkPlaying τ)) bs)
      grow-alone  : ∀ {t : Sub h [] R} {p w} {σ : w ⊑ h} {K bs} {Δ A s q} (π : Path t (pendingˢ {Δ = Δ} {A} s q)) (sk : StackAs t p σ K bs)
                  → All (λ j → ¬ SrcOf t π (proj₂ j)) (stackJobs t sk) → All (λ j → ¬ SrcOf (wkTree τ t) (wkPath τ π) (proj₂ j)) (stackJobs (wkTree τ t) (grow-stack sk))
      grow-ticked : ∀ {t : Sub h [] R} {n p w} {σ : w ⊑ h} {K bs} (sk : StackAs t p σ K bs) → Ticked t n sk → Ticked (wkTree τ t) n (grow-stack sk)
      -- A walk along the weakened path hands the weakened observer and
      -- continuation, up to `_≗_`, and the weakened subjects.
      walk-grow   : ∀ {Δ A} {t : Sub h [] R} {u : Sub h Δ A} (π : Path t u)
                  → ObsRel (wkObs τ (Here.obs (walk π top))) (Here.obs (walk (wkPath τ π) top))
                  × KontRel (wkKont τ (Here.kont (walk π top))) (Here.kont (walk (wkPath τ π) top))
                  × wkEnv τ (Here.env (walk π top)) ≡ Here.env (walk (wkPath τ π) top)

    env-grow : ∀ {t : Sub h [] R} {Δ A} {u′ : Sub h Δ A} (π : Path t u′) {u} (E′ : Env Δ u) (υ : u ⊑ h)
             → wkEnv υ E′ ≡ Here.env (walk π top) → wkEnv (υ ⨾ τ) E′ ≡ Here.env (walk (wkPath τ π) top)
    env-grow π E′ υ e = trans (sym (wkEnv-wk υ τ E′)) (trans (cong (wkEnv τ) e) (proj₂ (proj₂ (walk-grow π))))

    -- A subscription still pending, along the weakened path.
    code-grow : ∀ {t : Sub h [] R} {Δ A} {s : T.Obs Timeline Δ A} {q} (π : Path t (pendingˢ s q)) {u} (E′ : Env Δ u) (υ : u ⊑ h)
              → wkEnv υ E′ ≡ Here.env (walk π top)
              → Σ World λ u′ → Σ (Env Δ u′) λ E″ → Σ (u′ ⊑ v) λ υ′ → wkEnv υ′ E″ ≡ Here.env (walk (wkPath τ π) top)
                  × compile s E′ (υ ⨾ τ) (Here.obs (walk (wkPath τ π) top)) (Here.kont (walk (wkPath τ π) top))
                    ≗ compile s E″ υ′ (Here.obs (walk (wkPath τ π) top)) (Here.kont (walk (wkPath τ π) top))
    code-grow π {u} E′ υ e = u , E′ , υ ⨾ τ , env-grow π E′ υ e , ≗-refl _

    -- A node of the grown tree held where it is a flatMap, or a
    -- connect: the weakening of one, which the old tree held.
    data FlatBack {Δ′ B′} : Sub v Δ′ B′ → Sub h Δ′ B′ → Set₁ where
      flat-back : ∀ {A′} {op f fl oc k r pl} {so : Sub h Δ′ A′} {ls : List (Lane h Δ′ B′)}
                → FlatBack (wkTree τ (flatMapˢ op f fl oc k r pl so ls)) (flatMapˢ op f fl oc k r pl so ls)

    data ConnBack {Δ′ B′} : Sub v Δ′ B′ → Sub h Δ′ B′ → Set₁ where
      conn-back : ∀ {A′} {S c b kb k fd rp e rt} {src : Sub h Δ′ A′} {bd : Sub h (A′ ∷ Δ′) B′}
                → ConnBack (wkTree τ (connectˢ S c b kb k fd rp e rt src bd)) (connectˢ S c b kb k fd rp e rt src bd)

    flat-inv : ∀ {Δ′ A′ B′} {op f fl′ oc′ k′ r′ pl} {so′ : Sub v Δ′ A′} {ls′ : List (Lane v Δ′ B′)} (x : Sub h Δ′ B′)
             → flatMapˢ op f fl′ oc′ k′ r′ pl so′ ls′ ≡ wkTree τ x → FlatBack (flatMapˢ op f fl′ oc′ k′ r′ pl so′ ls′) x
    flat-inv (flatMapˢ op f fl oc k r pl so ls)     refl = flat-back
    flat-inv (pendingˢ s q)                         ()
    flat-inv (coldˢ s hd ph)                        ()
    flat-inv (ofˢ p i xs)                           ()
    flat-inv doneˢ                                  ()
    flat-inv (mapˢ f s)                             ()
    flat-inv (scanˢ f r s)                          ()
    flat-inv (takeWhileˢ i p c k tk s)              ()
    flat-inv (connectˢ S c b kb k fd rp e rt src bd) ()
    flat-inv (joinˢ j sk l x st)                    ()
    flat-inv (deferˢ k s)                           ()

    conn-inv : ∀ {Δ′ A′ B′} {S′ c′ b′ kb′ k′ fd′ rp e rt} {src′ : Sub v Δ′ A′} {bd′ : Sub v (A′ ∷ Δ′) B′} (x : Sub h Δ′ B′)
             → connectˢ S′ c′ b′ kb′ k′ fd′ rp e rt src′ bd′ ≡ wkTree τ x → ConnBack (connectˢ S′ c′ b′ kb′ k′ fd′ rp e rt src′ bd′) x
    conn-inv (connectˢ S c b kb k fd rp e rt src bd) refl = conn-back
    conn-inv (pendingˢ s q)                         ()
    conn-inv (coldˢ s hd ph)                        ()
    conn-inv (ofˢ p i xs)                           ()
    conn-inv doneˢ                                  ()
    conn-inv (mapˢ f s)                             ()
    conn-inv (scanˢ f r s)                          ()
    conn-inv (takeWhileˢ i p c k tk s)              ()
    conn-inv (flatMapˢ op f fl oc k r pl so ls)     ()
    conn-inv (joinˢ j sk l x st)                    ()
    conn-inv (deferˢ k s)                           ()

    -- What a weakened tree owes, and what it has begun.
    owes-wk : ∀ {Δ A} (u : Sub h Δ A) → Owes (wkTree τ u) → Owes u
    owes-wk (pendingˢ s q)                          o = o
    owes-wk (mapˢ f s)                              o = owes-wk s o
    owes-wk (scanˢ f r s)                           o = owes-wk s o
    owes-wk (connectˢ S c b kb k fd rp e rt src bd) o = owes-wk src o
    owes-wk (coldˢ s hd ph)                         ()
    owes-wk (ofˢ p i xs)                            ()
    owes-wk doneˢ                                   ()
    owes-wk (takeWhileˢ i p c k tk s)               ()
    owes-wk (flatMapˢ op f fl oc k r pl so ls)      ()
    owes-wk (joinˢ j sk l x st)                     ()
    owes-wk (deferˢ k s)                            ()

    begun-wk : ∀ {Δ A} (k : Maybe (Quiet h)) (u : Sub h Δ A) → Begun k u → Begun (mapMaybe (wk∋ τ) k) (wkTree τ u)
    begun-wk nothing  u _ = tt
    begun-wk (just _) u b = λ o → b (owes-wk u o)

    mutual
      settled-wk : ∀ {Δ A} (u : Sub h Δ A) → Settled u → Settled (wkTree τ u)
      settled-wk (pendingˢ s q)                          _                 = tt
      settled-wk (coldˢ s hd ph)                         _                 = tt
      settled-wk (ofˢ p i xs)                            _                 = tt
      settled-wk doneˢ                                   _                 = tt
      settled-wk (mapˢ f s)                              x                 = settled-wk s x
      settled-wk (scanˢ f r s)                           x                 = settled-wk s x
      settled-wk (takeWhileˢ i p c k tk s)               (b , x)           = begun-wk k s b , settled-wk s x
      settled-wk (flatMapˢ op f fl oc k r pl so ls)      (b , x , y)       = begun-wk k so b , settled-wk so x , settled-wkᴸ ls y
      settled-wk (connectˢ S c b kb k fd rp e rt src bd) (b₁ , b₂ , x , y) = begun-wk k src b₁ , begun-wk kb bd b₂ , settled-wk src x , settled-wk bd y
      settled-wk (joinˢ j sk l x st)                     _                 = tt
      settled-wk (deferˢ k s)                            (b , x)           = begun-wk k s b , settled-wk s x

      settled-wkᴸ : ∀ {Δ B} (ls : List (Lane h Δ B)) → SettledLanes ls → SettledLanes (wkLanes τ ls)
      settled-wkᴸ []                _           = tt
      settled-wkᴸ (lane c k s ∷ ls) (b , x , y) = begun-wk k s b , settled-wk s x , settled-wkᴸ ls y

    -- The pending frames' timers, weakened.
    timerOf-wk : ∀ {A} (s : Sink h A) (hd : Handle h) (ph : Phase A) → timerOf (wk∋ τ s) (wk∋ τ hd) ph ≡ mapList (wkTimer τ) (timerOf s hd ph)
    timerOf-wk s hd (waiting τ′ e (at t le b)) = refl
    timerOf-wk s hd (waiting τ′ e doneᶠᵐ)      = refl
    timerOf-wk s hd (waiting τ′ e quietᶠᵐ)     = refl
    timerOf-wk s hd (fired _ _ _)              = refl
    timerOf-wk s hd (playing _ _ _ _)          = refl

    mapL-++ : ∀ {a b} {X : Set a} {Y : Set b} (f : X → Y) (xs ys : List X) → mapList f (xs ++ ys) ≡ mapList f xs ++ mapList f ys
    mapL-++ f []       ys = refl
    mapL-++ f (x ∷ xs) ys = cong (f x ∷_) (mapL-++ f xs ys)

    ∈-mapL : ∀ {a b} {X : Set a} {Y : Set b} (f : X → Y) {x xs} → x ∈ xs → f x ∈ mapList f xs
    ∈-mapL f (hereᴬ refl) = hereᴬ refl
    ∈-mapL f (thereᴬ m)   = thereᴬ (∈-mapL f m)

    all-mapL : ∀ {a b p q} {X : Set a} {Y : Set b} {P : X → Set p} {Q : Y → Set q} (f : X → Y) → (∀ {x} → P x → Q (f x))
             → ∀ {xs} → All P xs → All Q (mapList f xs)
    all-mapL f g []         = []
    all-mapL f g (px ∷ pxs) = g px ∷ all-mapL f g pxs

    linked-mapL : ∀ {ts : List (Timer h)} → Linked (λ x y → cascade x <ᵖ cascade y ≡ true) ts
                → Linked (λ x y → cascade x <ᵖ cascade y ≡ true) (mapList (wkTimer τ) ts)
    linked-mapL []      = []
    linked-mapL [-]     = [-]
    linked-mapL (r ∷ l) = r ∷ linked-mapL l

    mutual
      pendings-wk : ∀ {Δ A} (u : Sub h Δ A) → pendings (wkTree τ u) ≡ mapList (wkTimer τ) (pendings u)
      pendings-wk (pendingˢ s q)                          = refl
      pendings-wk (coldˢ s hd ph)                         = timerOf-wk s hd ph
      pendings-wk (ofˢ p i xs)                            = refl
      pendings-wk doneˢ                                   = refl
      pendings-wk (mapˢ f s)                              = pendings-wk s
      pendings-wk (scanˢ f r s)                           = pendings-wk s
      pendings-wk (takeWhileˢ i p c k tk s)               = pendings-wk s
      pendings-wk (flatMapˢ op f fl oc k r pl so ls)      =
        trans (cong₂ _++_ (pendings-wk so) (pendings-wkᴸ ls)) (sym (mapL-++ (wkTimer τ) (pendings so) (lanePendings ls)))
      pendings-wk (connectˢ S c b kb k fd rp e rt src bd) =
        trans (cong₂ _++_ (pendings-wk src) (pendings-wk bd)) (sym (mapL-++ (wkTimer τ) (pendings src) (pendings bd)))
      pendings-wk (joinˢ j sk l x st)                     = refl
      pendings-wk (deferˢ k s)                            = pendings-wk s

      pendings-wkᴸ : ∀ {Δ B} (ls : List (Lane h Δ B)) → lanePendings (wkLanes τ ls) ≡ mapList (wkTimer τ) (lanePendings ls)
      pendings-wkᴸ []                = refl
      pendings-wkᴸ (lane c k s ∷ ls) =
        trans (cong₂ _++_ (pendings-wk s) (pendings-wkᴸ ls)) (sym (mapL-++ (wkTimer τ) (pendings s) (lanePendings ls)))

    module _ {H : Heapᴹ h} {H′ : Heapᴹ v} (gr : Grows τ H H′) where
      private
        cells : ∀ {t} (x : Ref h t) → At.val H′ (wkR τ x) ≡ wkEl t τ (At.val H x)
        cells = Grows.cells gr

        -- The heap-free combinators read alike from either heap.
        mapᴹ-≡ : ∀ {X Y : Set₁} (f : X → Y) m → At.mapᴹ H′ f m ≡ At.mapᴹ H f m
        mapᴹ-≡ f nothing  = refl
        mapᴹ-≡ f (just _) = refl

        consᴹ-≡ : ∀ {X : Set₁} (m : Maybe X) xs → At.consᴹ H′ m xs ≡ At.consᴹ H m xs
        consᴹ-≡ nothing  xs = refl
        consᴹ-≡ (just _) xs = refl

        merged-≡ : ∀ {Δ A B} op (g : A → Pos → U.Node Δ B) o L Q pl → At.merged H′ op g o L Q pl ≡ At.merged H op g o L Q pl
        merged-≡ op g nothing  []      []      pl = refl
        merged-≡ op g nothing  []      (_ ∷ _) pl = refl
        merged-≡ op g nothing  (_ ∷ _) Q       pl = refl
        merged-≡ op g (just _) L       Q       pl = refl

        connected-≡ : ∀ {Δ A B} r (e : Maybe Pos) (t : U.Node Δ A) s (mb : Maybe (U.Node (A ∷ Δ) B))
                    → At.connected H′ r e t s mb ≡ At.connected H r e t s mb
        connected-≡ r e        t s        nothing  = refl
        connected-≡ r e        t (just _) (just _) = refl
        connected-≡ r (just _) t nothing  (just _) = refl
        connected-≡ r nothing  t nothing  (just _) = refl

        joinedᶜ-≡ : ∀ {Δ A} (x : A ∈ Δ) j st → At.joinedᶜ H′ x j st ≡ At.joinedᶜ H x j st
        joinedᶜ-≡ x j nothing  = refl
        joinedᶜ-≡ x j (just _) = refl

        taking?-≡ : ∀ {Δ A} i p tk (s : Maybe (U.Node Δ A)) → At.taking? H′ i p tk s ≡ At.taking? H i p tk s
        taking?-≡ i p taking       s = mapᴹ-≡ (U.takeWhileᶜ i p) s
        taking?-≡ i p (ending k c) s = refl
        taking?-≡ i p taken        s = refl

        sourced-≡ : ∀ {Δ A} (s : Maybe (U.Node Δ A)) t → At.sourced H′ s t ≡ At.sourced H s t
        sourced-≡ (just _) t = refl
        sourced-≡ nothing  t = refl

      -- The open part, read through the weakening.
      mutual
        grow-part : ∀ {Δ A} (u : Sub h Δ A) → At.part H′ (wkTree τ u) ≡ At.part H u
        grow-part (pendingˢ s q)                 = refl
        grow-part (coldˢ s hd ph)                = cong (λ b → if b then nothing else _) (Grows.handles gr hd)
        grow-part (ofˢ p i xs)                   = refl
        grow-part doneˢ                          = refl
        grow-part (mapˢ f s)                     = trans (cong (At.mapᴹ H′ (U.mapᶜ f)) (grow-part s)) (mapᴹ-≡ (U.mapᶜ f) (At.part H s))
        grow-part (scanˢ f r s)                  =
          trans (cong₂ (λ a m → At.mapᴹ H′ (U.scanᶜ f a) m) (cells r) (grow-part s)) (mapᴹ-≡ (U.scanᶜ f (At.val H r)) (At.part H s))
        grow-part (takeWhileˢ i p c k tk s)      =
          trans (cong₂ (λ b m → if b then At.taking? H′ i p tk m else nothing) (cells (Kit.live c)) (grow-part s))
                (cong (λ m → if At.val H (Kit.live c) then m else nothing) (taking?-≡ i p tk (At.part H s)))
        grow-part (flatMapˢ op f fl oc k r pl so ls) =
          trans (cong₂ (λ o L → At.merged H′ op (λ a q → U.subscribe (f a) q) o L (At.val H′ (wkR τ (FlatKit.Flat.queue fl))) pl) (grow-part so) (grow-partᴸ ls))
                (trans (cong (λ Q → At.merged H′ op (λ a q → U.subscribe (f a) q) (At.part H so) (At.partLanes H ls) Q pl) (cells (FlatKit.Flat.queue fl)))
                       (merged-≡ op (λ a q → U.subscribe (f a) q) (At.part H so) (At.partLanes H ls) (At.val H (FlatKit.Flat.queue fl)) pl))
        grow-part (connectˢ S c b kb k fd rp e rt src bd) =
          trans (cong₂ (At.connected H′ rp e rt) (grow-part src) (grow-part bd)) (connected-≡ rp e rt (At.part H src) (At.part H bd))
        grow-part (joinˢ j sk l x st)            =
          trans (cong (λ b → if b then At.joinedᶜ H′ x j st else nothing) (cells l)) (cong (λ m → if At.val H l then m else nothing) (joinedᶜ-≡ x j st))
        grow-part (deferˢ k s)                   = grow-part s

        grow-partᴸ : ∀ {Δ B} (ls : List (Lane h Δ B)) → At.partLanes H′ (wkLanes τ ls) ≡ At.partLanes H ls
        grow-partᴸ []                = refl
        grow-partᴸ (lane c k s ∷ ls) =
          trans (cong₂ (λ b L → if b then At.consᴹ H′ (At.part H′ (wkTree τ s)) L else L) (cells (Kit.live c)) (grow-partᴸ ls))
                (cong (λ m → if At.val H (Kit.live c) then m else At.partLanes H ls)
                      (trans (cong (λ m → At.consᴹ H′ m (At.partLanes H ls)) (grow-part s)) (consᴹ-≡ (At.part H s) (At.partLanes H ls))))

      -- What the weakened tree leaves running, and what its pools run.
      mutual
        leftover-wk : ∀ {Δ A B} (u : Sub h Δ A) → At.leftover H′ {B = B} (wkTree τ u) ≡ At.leftover H {B = B} u
        leftover-wk (pendingˢ s q)                     = refl
        leftover-wk (coldˢ s hd ph)                    = refl
        leftover-wk (ofˢ p i xs)                       = refl
        leftover-wk doneˢ                              = refl
        leftover-wk (mapˢ f s)                         = leftover-wk s
        leftover-wk (scanˢ f r s)                      = leftover-wk s
        leftover-wk (takeWhileˢ i p c k tk s)          = leftover-wk s
        leftover-wk (flatMapˢ op f fl oc k r pl so ls) = cong₂ U.unionᶜ (leftover-wk so) (leftover-wkᴸ ls)
        leftover-wk (connectˢ S c b kb k fd rp e rt src bd) =
          cong₂ (λ n l → U.unionᶜ (U.burstingᶜ rp n) (U.underᶜ (U.live n) l))
                (trans (cong₂ (At.sourced H′) (grow-part src) (leftover-wk src)) (sourced-≡ (At.part H src) (At.leftover H src)))
                (leftover-wk {B = ⊤} bd)
        leftover-wk (joinˢ j sk l x st)                = refl
        leftover-wk (deferˢ k s)                       = leftover-wk s

        leftover-wkᴸ : ∀ {Δ A B} (ls : List (Lane h Δ A)) → At.leftoverL H′ {B = B} (wkLanes τ ls) ≡ At.leftoverL H {B = B} ls
        leftover-wkᴸ []                = refl
        leftover-wkᴸ (lane c k s ∷ ls) = cong₂ U.unionᶜ (leftover-wk s) (leftover-wkᴸ ls)

      pooled-wkᴸ : ∀ {Δ A B} (ls : List (Lane h Δ A)) → At.pooledL H′ {B = B} (wkLanes τ ls) ≡ At.pooledL H {B = B} ls
      pooled-wkᴸ []                = refl
      pooled-wkᴸ (lane c k s ∷ ls) =
        trans (cong₂ (λ b P → if b then P else U.unionᶜ (At.leftover H′ (wkTree τ s)) P) (cells (Kit.live c)) (pooled-wkᴸ ls))
              (cong (λ x → if At.val H (Kit.live c) then At.pooledL H ls else U.unionᶜ x (At.pooledL H ls)) (leftover-wk s))

      pooled-wk : ∀ {Δ A B} (fl : FlatKit.Flat A h) (so : Sub h Δ A) (ls : List (Lane h Δ B))
                → At.pooled H′ (FlatKit.wkFlat τ fl) (wkTree τ so) (wkLanes τ ls) ≡ At.pooled H fl so ls
      pooled-wk fl so ls =
        cong₂ U.unionᶜ (trans (cong (λ b → if b then At.leftover H′ (wkTree τ so) else U.idleᶜ) (cells (FlatKit.Flat.outerDone fl)))
                              (cong (λ x → if At.val H (FlatKit.Flat.outerDone fl) then x else U.idleᶜ) (leftover-wk so)))
                       (pooled-wkᴸ ls)

      -- A path through the weakened tree is the weakening of one through
      -- the old, seen alike.
      mutual
        unwk : ∀ {Δ A Δ′ A′} (t : Sub h Δ A) {x′ : Sub v Δ′ A′} (ψ′ : Path (wkTree τ t) x′)
             → Σ (Sub h Δ′ A′) λ x → Σ (Path t x) λ ψ → x′ ≡ wkTree τ x × seen H′ ψ′ ≡ seen H ψ
        unwk (pendingˢ s q)                     here = _ , here , refl , refl
        unwk (coldˢ s hd ph)                    here = _ , here , refl , refl
        unwk (ofˢ p i xs)                       here = _ , here , refl , refl
        unwk doneˢ                              here = _ , here , refl , refl
        unwk (joinˢ j sk l x st)                here = _ , here , refl , refl
        unwk (mapˢ f s)                         here = _ , here , refl , refl
        unwk (mapˢ f s)                         (in-map ψ′) = let x , ψ , e , sn = unwk s ψ′ in x , in-map ψ , e , sn
        unwk (scanˢ f r s)                      here = _ , here , refl , refl
        unwk (scanˢ f r s)                      (in-scan ψ′) = let x , ψ , e , sn = unwk s ψ′ in x , in-scan ψ , e , sn
        unwk (takeWhileˢ i p c k tk s)          here = _ , here , refl , refl
        unwk (takeWhileˢ i p c k tk s)          (in-take ψ′) =
          let x , ψ , e , sn = unwk s ψ′ in x , in-take ψ , e , cong₂ _∧_ (cells (Kit.live c)) (cong (isTaking tk ∧_) sn)
        unwk (flatMapˢ op f fl oc k r pl so ls) here = _ , here , refl , refl
        unwk (flatMapˢ op f fl oc k r pl so ls) (in-outer ψ′) = let x , ψ , e , sn = unwk so ψ′ in x , in-outer ψ , e , sn
        unwk (flatMapˢ op f fl oc k r pl so ls) (in-lanes ψ′) = let x , ψ , e , sn = unwkᴸ ls ψ′ in x , in-lanes ψ , e , sn
        unwk (connectˢ S c b kb k fd rp e rt src bd) here = _ , here , refl , refl
        unwk (connectˢ S c b kb k fd rp e rt src bd) (in-source ψ′) =
          let x , ψ , eq , sn = unwk src ψ′ in x , in-source ψ , eq , cong₂ _∧_ (cong is-just (grow-part bd)) sn
        unwk (connectˢ S c b kb k fd rp e rt src bd) (in-body ψ′) =
          let x , ψ , eq , sn = unwk bd ψ′ in x , in-body ψ , eq , cong₂ _∧_ (cong (λ z → is-just z ∨ is-just e) (grow-part src)) sn
        unwk (deferˢ k s)                       here = _ , here , refl , refl
        unwk (deferˢ k s)                       (in-defer ψ′) = let x , ψ , e , sn = unwk s ψ′ in x , in-defer ψ , e , sn

        unwkᴸ : ∀ {Δ B Δ′ A′} (ls : List (Lane h Δ B)) {x′ : Sub v Δ′ A′} (ψ′ : PathLanes (wkLanes τ ls) x′)
              → Σ (Sub h Δ′ A′) λ x → Σ (PathLanes ls x) λ ψ → x′ ≡ wkTree τ x × seenL H′ ψ′ ≡ seenL H ψ
        unwkᴸ (lane c k s ∷ ls) (this-lane ψ′) = let x , ψ , e , sn = unwk s ψ′ in x , this-lane ψ , e , cong₂ _∧_ (cells (Kit.live c)) sn
        unwkᴸ (lane c k s ∷ ls) (next-lane ψ′) = let x , ψ , e , sn = unwkᴸ ls ψ′ in x , next-lane ψ , e , sn

      grow-each : ∀ {t : Sub h [] R} {P : ∀ {Γ A} → U.Node Γ A → Set} → Each H P t → Each H′ P (wkTree τ t)
      Each.parts (grow-each {t = t} E) ψ′ sn {c} eq =
        let x , ψ , e , s = unwk t ψ′ in
        Each.parts E ψ (trans (sym s) sn) (trans (sym (grow-part x)) (subst (λ z → At.part H′ z ≡ just c) e eq))
      Each.pools (grow-each {t = t} E) {op = op} {f = f} {pl = pl} ψ′ sn eq with unwk t ψ′
      ... | x , ψ , e , s with flat-inv x e
      ... | flat-back {fl = fl} {oc = oc} {k = k} {r = r} {so = so} {ls = ls} =
        Each.pools E ψ (trans (sym s) sn) (trans (sym (grow-part (flatMapˢ op f fl oc k r pl so ls))) eq)
      Each.rests (grow-each {t = t} E) {rp = rp} {e = e₀} {rt = rt} ψ′ sn eq pn ec with unwk t ψ′
      ... | x , ψ , e , s with conn-inv x e
      ... | conn-back {S = S} {c = c} {b = b} {kb = kb} {k = k} {fd = fd} {src = src} {bd = bd} =
        Each.rests E ψ (trans (sym s) sn) (trans (sym (grow-part (connectˢ S c b kb k fd rp e₀ rt src bd))) eq) (trans (sym (grow-part src)) pn) ec

      grow-lingers : ∀ {t : Sub h [] R} → Lingers H t → Lingers H′ (wkTree τ t)
      Lingers.pools (grow-lingers {t = t} L) {op = op} {f = f} {pl = pl} ψ′ sn eq with unwk t ψ′
      ... | x , ψ , e , s with flat-inv x e
      ... | flat-back {fl = fl} {oc = oc} {k = k} {r = r} {so = so} {ls = ls} =
        subst (Tied pl) (sym (pooled-wk fl so ls)) (Lingers.pools L ψ (trans (sym s) sn) (trans (sym (grow-part (flatMapˢ op f fl oc k r pl so ls))) eq))
      Lingers.rests (grow-lingers {t = t} L) {rp = rp} {e = e₀} {rt = rt} ψ′ sn eq pn ec with unwk t ψ′
      ... | x , ψ , e , s with conn-inv x e
      ... | conn-back {S = S} {c = c} {b = b} {kb = kb} {k = k} {fd = fd} {src = src} {bd = bd} =
        subst (Tied rt) (sym (leftover-wk {B = ⊤} src))
              (Lingers.rests L ψ (trans (sym s) sn) (trans (sym (grow-part (connectˢ S c b kb k fd rp e₀ rt src bd))) eq) (trans (sym (grow-part src)) pn) ec)

      -- What unsubscribing reaches, and the gates, read through the
      -- weakening.
      mutual
        grow-spent : ∀ {Δ A} (u : Sub h Δ A) → At.Spent H u → At.Spent H′ (wkTree τ u)
        grow-spent (pendingˢ s q)                          _         = lift tt
        grow-spent (coldˢ s hd ph)                         (lift e)  = lift (trans (Grows.handles gr hd) e)
        grow-spent (ofˢ p i xs)                            _         = lift tt
        grow-spent doneˢ                                   _         = lift tt
        grow-spent (mapˢ f s)                              x         = grow-spent s x
        grow-spent (scanˢ f r s)                           x         = grow-spent s x
        grow-spent (takeWhileˢ i p c k tk s)               x         = grow-cut↓ k s x
        grow-spent (flatMapˢ op f fl oc k r pl so ls)      (x , y)   = grow-cut↓ k so x , grow-spentᴸ ls y
        grow-spent (connectˢ S c b kb k fd rp e rt src bd) (x , y)   = grow-cut↓ k src x , grow-cut↓ kb bd y
        grow-spent (joinˢ j sk l x st)                     _         = lift tt
        grow-spent (deferˢ k s)                            x         = grow-cut↓ k s x

        grow-spentᴸ : ∀ {Δ B} (ls : List (Lane h Δ B)) → At.SpentLanes H ls → At.SpentLanes H′ (wkLanes τ ls)
        grow-spentᴸ []                _       = lift tt
        grow-spentᴸ (lane c k s ∷ ls) (x , y) = grow-cut↓ k s x , grow-spentᴸ ls y

        grow-cut↓ : ∀ {Δ A} (k : Maybe (Quiet h)) (u : Sub h Δ A) → At.Cut↓ H k u → At.Cut↓ H′ (mapMaybe (wk∋ τ) k) (wkTree τ u)
        grow-cut↓ nothing  u _ = lift tt
        grow-cut↓ (just _) u x = grow-spent u x

      -- A cut read false through the weakening was false.
      cut-off : ∀ {Δ A} (c : Kit.Cut h) (k : Maybe (Quiet h)) (u : Sub h Δ A) → (At.val H (Kit.live c) ≡ false → At.Cut↓ H k u)
              → At.val H′ (Kit.live (Kit.wkCut τ c)) ≡ false → At.Cut↓ H′ (mapMaybe (wk∋ τ) k) (wkTree τ u)
      cut-off c k u g e = grow-cut↓ k u (g (trans (sym (cells (Kit.live c))) e))

      mutual
        grow-gated : ∀ {Δ A} (u : Sub h Δ A) → At.Gated H u → At.Gated H′ (wkTree τ u)
        grow-gated (pendingˢ s q)                          _           = lift tt
        grow-gated (coldˢ s hd ph)                         (lift g)    = lift (λ e → g (trans (sym (Grows.handles gr hd)) e))
        grow-gated (ofˢ p i xs)                            _           = lift tt
        grow-gated doneˢ                                   _           = lift tt
        grow-gated (mapˢ f s)                              x           = grow-gated s x
        grow-gated (scanˢ f r s)                           x           = grow-gated s x
        grow-gated (takeWhileˢ i p c k tk s)               (g , x)     = cut-off c k s g , grow-gated s x
        grow-gated (flatMapˢ op f fl oc k r pl so ls)      (x , y)     = grow-gated so x , grow-gatedᴸ ls y
        grow-gated (connectˢ S c b kb k fd rp e rt src bd) (g , x , y) = cut-off c k src g , grow-gated src x , grow-gated bd y
        grow-gated (joinˢ j sk l x st)                     _           = lift tt
        grow-gated (deferˢ k s)                            x           = grow-gated s x

        grow-gatedᴸ : ∀ {Δ B} (ls : List (Lane h Δ B)) → At.GatedLanes H ls → At.GatedLanes H′ (wkLanes τ ls)
        grow-gatedᴸ []                _           = lift tt
        grow-gatedᴸ (lane c k s ∷ ls) (g , x , y) = cut-off c k s g , grow-gated s x , grow-gatedᴸ ls y

      postulate
        -- Every registered callback reads, along the growth, as the
        -- weakened kernel registered it.
        grow-holds : ∀ (t : Sub h [] R) → At.Holds H t [] rootObs → At.Holds H′ (wkTree τ t) [] rootObs

      grow-kernels : ∀ {t : Sub h [] R} → Kernels H t → Kernels H′ (wkTree τ t)
      grow-kernels {t} kn = record { holds = grow-holds t (Kernels.holds kn) ; gated = grow-gated t (Kernels.gated kn) ; settled = settled-wk t (Kernels.settled kn) }

      -- A feed weakened owes whom it owed, and what.
      private
        ∋-inj : ∀ {u w k} (ρ : u ⊑ w) {i j : u ∋ k} → wk∋ ρ i ≡ wk∋ ρ j → i ≡ j
        ∋-inj same⊑    e = e
        ∋-inj (grow ρ) e = ∋-inj ρ (there-inj′ e)
          where
            there-inj′ : ∀ {j w k} {a b : w ∋ k} → _≡_ {A = (j ∷ w) ∋ k} (there a) (there b) → a ≡ b
            there-inj′ refl = refl

        pair-back : ∀ {A} {sk s : Sink h A} {j i : Pos} → _≡_ {A = Sink v A × Pos} (wk∋ τ sk , j) (wk∋ τ s , i) → (sk , j) ≡ (s , i)
        pair-back e with ∋-inj τ (cong proj₁ e) | cong proj₂ e
        ... | refl | refl = refl

      owed-back : ∀ {A} (fd : Feed A h) {sk : Sink h A} {j} → At.Owed H′ (wkFeed τ fd) (wk∋ τ sk) j → At.Owed H fd sk j
      owed-back idle                           ()
      owed-back (feeding a q [])               ()
      owed-back (feeding a q ((s , i) ∷ ss))   (hereᴬ e)  = hereᴬ (pair-back e)
      owed-back (feeding a q (_ ∷ ss))         (thereᴬ m) = thereᴬ (owed-back (feeding a q ss) m)
      owed-back (finishing q [])               ()
      owed-back (finishing q ((s , i) ∷ ss))   (hereᴬ e)  = hereᴬ (pair-back e)
      owed-back (finishing q (_ ∷ ss))         (thereᴬ m) = thereᴬ (owed-back (finishing q ss) m)

      owed-fwd : ∀ {A} (fd : Feed A h) {sk : Sink h A} {j} → At.Owed H fd sk j → At.Owed H′ (wkFeed τ fd) (wk∋ τ sk) j
      owed-fwd idle                   ()
      owed-fwd (feeding a q [])       ()
      owed-fwd (feeding a q (_ ∷ ss)) (hereᴬ refl) = hereᴬ refl
      owed-fwd (feeding a q (_ ∷ ss)) (thereᴬ m)   = thereᴬ (owed-fwd (feeding a q ss) m)
      owed-fwd (finishing q [])       ()
      owed-fwd (finishing q (_ ∷ ss)) (hereᴬ refl) = hereᴬ refl
      owed-fwd (finishing q (_ ∷ ss)) (thereᴬ m)   = thereᴬ (owed-fwd (finishing q ss) m)

      owing-wk : ∀ {A} (fd : Feed A h) j → At.owing H′ (wkFeed τ fd) j ≡ At.owing H fd j
      owing-wk idle             j = refl
      owing-wk (feeding a q ss) j = refl
      owing-wk (finishing q ss) j = refl

      owingNone-≡ : ∀ {A : Set} (e : Maybe Pos) → At.owingNone H′ {A} e ≡ At.owingNone H e
      owingNone-≡ nothing  = refl
      owingNone-≡ (just _) = refl

      wkNow : ∀ {Δ} → At.Now H Δ → At.Now H′ Δ
      wkNow []             = []
      wkNow ((fd , e) ∷ ν) = (wkFeed τ fd , e) ∷ wkNow ν

      lookup-wk : ∀ {Δ A} (ν : At.Now H Δ) (x : A ∈ Δ) → lookupᴬ (wkNow ν) x ≡ (wkFeed τ (proj₁ (lookupᴬ ν x)) , proj₂ (lookupᴬ ν x))
      lookup-wk (_ ∷ ν) (hereᴬ refl) = refl
      lookup-wk (_ ∷ ν) (thereᴬ x)   = lookup-wk ν x

      -- Every live joiner held what its feed owed it, read through the
      -- weakening.
      mutual
        fed-wk : ∀ {Δ A} (u : Sub h Δ A) (ν : At.Now H Δ) → At.Fed H u ν → At.Fed H′ (wkTree τ u) (wkNow ν)
        fed-wk (pendingˢ s q)                          ν _       = lift tt
        fed-wk (coldˢ s hd ph)                         ν _       = lift tt
        fed-wk (ofˢ p i xs)                            ν _       = lift tt
        fed-wk doneˢ                                   ν _       = lift tt
        fed-wk (mapˢ f s)                              ν x       = fed-wk s ν x
        fed-wk (scanˢ f r s)                           ν x       = fed-wk s ν x
        fed-wk (takeWhileˢ i p c k tk s)               ν x       = fed-wk s ν x
        fed-wk (flatMapˢ op f fl oc k r pl so ls)      ν (x , y) = fed-wk so ν x , fed-wkᴸ ls ν y
        fed-wk (connectˢ S c b kb k fd rp e rt src bd) ν (x , y) = fed-wk src ν x , fed-wk bd ((fd , e) ∷ ν) y
        fed-wk (joinˢ j sk l x st)                     ν (lift f) =
          subst (λ p → Lift _ (At.val H′ (wkR τ l) ≡ true → (At.Owed H′ (proj₁ p) (wk∋ τ sk) j → st ≡ At.owing H′ (proj₁ p) j)
                                                         × (¬ At.Owed H′ (proj₁ p) (wk∋ τ sk) j → st ≡ At.owingNone H′ (proj₂ p))))
                (sym (lookup-wk ν x))
                (lift λ on → let (o , n) = f (trans (sym (cells l)) on) in
                  (λ m → trans (o (owed-back (proj₁ (lookupᴬ ν x)) m)) (sym (owing-wk (proj₁ (lookupᴬ ν x)) j)))
                  , (λ ¬m → trans (n (λ m → ¬m (owed-fwd (proj₁ (lookupᴬ ν x)) m))) (sym (owingNone-≡ (proj₂ (lookupᴬ ν x))))))
        fed-wk (deferˢ k s)                            ν x       = fed-wk s ν x

        fed-wkᴸ : ∀ {Δ B} (ls : List (Lane h Δ B)) (ν : At.Now H Δ) → At.FedLanes H ls ν → At.FedLanes H′ (wkLanes τ ls) (wkNow ν)
        fed-wkᴸ []                ν _       = lift tt
        fed-wkᴸ (lane c k s ∷ ls) ν (x , y) = fed-wk s ν x , fed-wkᴸ ls ν y

      grow-meaning : ∀ {t : Sub h [] R} → Meaning H t → Meaning H′ (wkTree τ t)
      grow-meaning {t} mn = record { fed = fed-wk t [] (Meaning.fed mn) }

      -- Every live timer a pending frame's, read through the weakening.
      grow-timed : ∀ {ts : List (Timer h)} (t : Sub h [] R) → At.Timed H ts (pendings t) → At.Timed H′ (mapList (wkTimer τ) ts) (pendings (wkTree τ t))
      grow-timed {ts} t (a , b) =
        all-mapL (wkTimer τ) one a , subst (All (λ tm → At.spentʰ H′ (Timer.handle tm) ≡ false → tm ∈ mapList (wkTimer τ) ts)) (sym (pendings-wk t)) (all-mapL (wkTimer τ) two b)
        where
          one : ∀ {tm} → At.spentʰ H (Timer.handle tm) ≡ true ⊎ tm ∈ pendings t
              → At.spentʰ H′ (Timer.handle (wkTimer τ tm)) ≡ true ⊎ wkTimer τ tm ∈ pendings (wkTree τ t)
          one {tm} (inj₁ e) = inj₁ (trans (Grows.handles gr (Timer.handle tm)) e)
          one      (inj₂ m) = inj₂ (subst (_ ∈_) (sym (pendings-wk t)) (∈-mapL (wkTimer τ) m))

          two : ∀ {tm} → (At.spentʰ H (Timer.handle tm) ≡ false → tm ∈ ts)
              → At.spentʰ H′ (Timer.handle (wkTimer τ tm)) ≡ false → wkTimer τ tm ∈ mapList (wkTimer τ) ts
          two {tm} g e = ∈-mapL (wkTimer τ) (g (trans (sym (Grows.handles gr (Timer.handle tm))) e))

      postulate
        -- Every subject's subscribers its joiners, or silenced, read
        -- through the weakening.
        grow-joined : ∀ (t : Sub h [] R) → At.Joined H (subjects t) (joiners t []) → At.Joined H′ (subjects (wkTree τ t)) (joiners (wkTree τ t) [])

      grow-queue : ∀ {t : Sub h [] R} {p clk ts} → Queue H p clk ts t → Queue H′ p clk (mapList (wkTimer τ) ts) (wkTree τ t)
      grow-queue {t} qu = record { timed = grow-timed t (Queue.timed qu) ; joined = grow-joined t (Queue.joined qu)
                                 ; ordered = linked-mapL (Queue.ordered qu) ; ahead = all-mapL (wkTimer τ) (λ x → x) (Queue.ahead qu) }

      postulate
        grow-owned   : ∀ {t : Sub h [] R} {w} {σ : w ⊑ h} {K bs} {Δ A s q} {π : Path t (pendingˢ {Δ = Δ} {A} s q)} {act act′ cd cd′}
                         (sk : StackAs t q σ K bs) {a a′}
                     → Owned H t (subAs {act = act} π cd sk a) → Owned H′ (wkTree τ t) (subAs {act = act′} (wkPath τ π) cd′ (grow-stack sk) a′)
