{-# OPTIONS --guardedness --large-indices #-}

module adequacy.Strong.Held where

open import Data.Bool using (Bool; true; false; _∧_; _∨_)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.Maybe using (Maybe; just; nothing; is-just; is-nothing)
open import Data.Nat using (zero; suc)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Level using (Level; Lift; lift; lower) renaming (suc to lsuc; zero to lzero)
open import Relation.Nullary using (¬_)
open import Data.List.Relation.Unary.Linked using (Linked) renaming ([] to []ᴸ)
import Data.List.Relation.Unary.Any as Any
open import Data.List.Relation.Unary.All using (All; lookup) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.List.Relation.Unary.AllPairs using (AllPairs) renaming ([] to []ᴾ)

import Tree as T
open import Tree using (Obs)
open import denotation.MonotonicList.Events using (timelineAt; inside; Time; Pos; From; Frame; Timeline; at; emit; stall; close; ix; last; tick; root; _<ᵖ_) renaming (done to doneᶠ; quiet to quietᶠ; sub to subᴾ)
open import operation.AbstractObservable using (base; maybe; quiet; gate; module Run; module Heap) renaming (module Machine to Shared)
open import operation.PureObservable using (Pureᴾ; Out; fin; module Pure)
open import operation.Machine using (module Machine)
import denotation.Unfold as U
open import adequacy.Sane using (Sane; sane-subscribe)
open import adequacy.Placed.Order using () renaming (Placed to Placedᵍ)
open import adequacy.Placed using (placed-subscribe)
open import adequacy.Deep using (Deep; deep-subscribe)
open import adequacy.Sorted using (_≤ᵖ_)
open import adequacy.Sorted.Walk using (module SortingWalk)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴸ_)
open import adequacy.Strong using (module Strongly)
open import adequacy.Strong.Against using (module StrongAgainst)

module StrongHeld (R : Set) where
  open Heap using (World; Kind; cell; slot; hush; play; _⊑_; _∋_; Sink; Handle; Quiet; _⨾_; same)
  open Run (Pureᴾ R)
  open Kit
  open FlatKit
  open Shared Timeline (Out R) using (Callbacks; Heapᴹ; look; Conf; Ctl; Stack; bottom; push; rest; back; rehold; run; asking; ⟨_,_,_⟩) renaming (held to holding)
  open Pure R using (Timer; cascade)
  open Machine R using (Mach; Playing; begin)
  open SortingWalk R using (WellMach; begin-well)
  open Strongly R using (Alg; module At; module Canon; module Fold; Here; Lane; Name; Path; PathLanes; Sub; _⊕_; coldˢ; connectˢ; deferˢ; doneˢ; flatMapˢ; here; in-body; in-defer; in-lanes; in-map; in-outer; in-scan; in-source; in-take; joinˢ; lane; mapˢ; next-lane; ofˢ; pendingˢ; scanˢ; takeWhileˢ; taking; this-lane; ≗-refl)
  open StrongAgainst R using (module Against; Books; Each; Kernels; Leaves; Lingers; Meaning; Owned; OwnedF; Queue; Restful; Twin; _,ᴼ_; isTaking; owned-from; seen; seen-join; seenL; ∧-join; ∧-split)
  open Canon
  open Here

  module Held {h} (H : Heapᴹ h) (Nd Pl Rs : ∀ {Δ A} → Sub h Δ A → Set₁) where
    open At H

    If : Bool → Set₁ → Set₁
    If b X = b ≡ true → X

    HeldAlg : Alg {lsuc lzero} h
    Alg.Inh    HeldAlg _ = Lift _ Bool
    Alg.InhL   HeldAlg _ = Lift _ Bool
    Alg.pendᶜ  HeldAlg s q hb = If (lower hb) (Nd (pendingˢ s q))
    Alg.coldᶜ  HeldAlg {Δ} s hd ph hb = If (lower hb) (Nd (coldˢ {Δ = Δ} s hd ph))
    Alg.ofᶜ    HeldAlg {Δ} p i xs hb = If (lower hb) (Nd (ofˢ {Δ = Δ} p i xs))
    Alg.doneᶜ  HeldAlg {Δ} {A} hb = If (lower hb) (Nd (doneˢ {h} {Δ} {A}))
    Alg.mapᶜ   HeldAlg f s X hb = If (lower hb) (Nd (mapˢ f s)) × X hb
    Alg.scanᶜ  HeldAlg f r s X hb = If (lower hb) (Nd (scanˢ f r s)) × X hb
    Alg.takeᶜ  HeldAlg i p c k tk s X hb =
      If (lower hb) (Nd (takeWhileˢ i p c k tk s)) × X (lift (lower hb ∧ val (Kit.live c) ∧ isTaking tk))
    Alg.flatᶜ  HeldAlg op f fl oc k r pl so ls X L hb =
      If (lower hb) (Nd (flatMapˢ op f fl oc k r pl so ls)) × If (lower hb) (Pl (flatMapˢ op f fl oc k r pl so ls)) × X hb × L hb
    Alg.connᶜ  HeldAlg S c b kb k fd rp e rt src bd X Y hb =
      If (lower hb) (Nd (connectˢ S c b kb k fd rp e rt src bd)) × If (lower hb) (Rs (connectˢ S c b kb k fd rp e rt src bd))
      × X (lift (lower hb ∧ is-just (part bd))) × Y (lift (lower hb ∧ (is-just (part src) ∨ is-just e)))
    Alg.joinᶜ  HeldAlg j sk l x st hb = If (lower hb) (Nd (joinˢ j sk l x st))
    Alg.deferᶜ HeldAlg k s X hb = If (lower hb) (Nd (deferˢ k s)) × X hb
    Alg.nilᶜ   HeldAlg _ = Lift _ ⊤
    Alg.consᶜ  HeldAlg c k s ls X L hb = X (lift (lower hb ∧ val (Kit.live c))) × L hb

    Below : ∀ {Δ A} → Sub h Δ A → Set₁
    Below t = Fold.fold HeldAlg t (lift true)

    -- The same, read along every held path.
    record Over {Δ A} (t : Sub h Δ A) : Set₁ where
      field
        nodes : ∀ {Δ′ A′} {u : Sub h Δ′ A′} (ψ : Path t u) → seen H ψ ≡ true → Nd u
        pools : ∀ {Δ′ A′ B′} {op f fl oc k r pl} {so : Sub h Δ′ A′} {ls : List (Lane h Δ′ B′)}
              → (ψ : Path t (flatMapˢ op f fl oc k r pl so ls)) → seen H ψ ≡ true → Pl (flatMapˢ op f fl oc k r pl so ls)
        rests : ∀ {Δ′ A′ B′} {S c b kb k fd rp e rt} {src : Sub h Δ′ A′} {bd : Sub h (A′ ∷ Δ′) B′}
              → (ψ : Path t (connectˢ S c b kb k fd rp e rt src bd)) → seen H ψ ≡ true → Rs (connectˢ S c b kb k fd rp e rt src bd)

    record OverL {Δ B} (ls : List (Lane h Δ B)) : Set₁ where
      field
        nodes : ∀ {Δ′ A′} {u : Sub h Δ′ A′} (ψ : PathLanes ls u) → seenL H ψ ≡ true → Nd u
        pools : ∀ {Δ′ A′ B′} {op f fl oc k r pl} {so : Sub h Δ′ A′} {ls′ : List (Lane h Δ′ B′)}
              → (ψ : PathLanes ls (flatMapˢ op f fl oc k r pl so ls′)) → seenL H ψ ≡ true → Pl (flatMapˢ op f fl oc k r pl so ls′)
        rests : ∀ {Δ′ A′ B′} {S c b kb k fd rp e rt} {src : Sub h Δ′ A′} {bd : Sub h (A′ ∷ Δ′) B′}
              → (ψ : PathLanes ls (connectˢ S c b kb k fd rp e rt src bd)) → seenL H ψ ≡ true → Rs (connectˢ S c b kb k fd rp e rt src bd)

    restrict : ∀ {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} → Over t → (ρ : Path t u) → seen H ρ ≡ true → Over u
    restrict O ρ sρ = record
      { nodes = λ ψ s → Over.nodes O (ρ ⊕ ψ) (seen-join H ρ ψ sρ s)
      ; pools = λ ψ s → Over.pools O (ρ ⊕ ψ) (seen-join H ρ ψ sρ s)
      ; rests = λ ψ s → Over.rests O (ρ ⊕ ψ) (seen-join H ρ ψ sρ s) }

    private
      lanesOf : ∀ {Δ A B op f fl oc k r pl} {so : Sub h Δ A} {ls : List (Lane h Δ B)} → Over (flatMapˢ op f fl oc k r pl so ls) → OverL ls
      lanesOf O = record
        { nodes = λ ψ s → Over.nodes O (in-lanes ψ) s
        ; pools = λ ψ s → Over.pools O (in-lanes ψ) s
        ; rests = λ ψ s → Over.rests O (in-lanes ψ) s }

      thisOf : ∀ {Δ B c k} {s : Sub h Δ B} {ls} → OverL (lane c k s ∷ ls) → val (Kit.live c) ≡ true → Over s
      thisOf O v = record
        { nodes = λ ψ s → OverL.nodes O (this-lane ψ) (∧-join v s)
        ; pools = λ ψ s → OverL.pools O (this-lane ψ) (∧-join v s)
        ; rests = λ ψ s → OverL.rests O (this-lane ψ) (∧-join v s) }

      nextOf : ∀ {Δ B} {l : Lane h Δ B} {ls} → OverL (l ∷ ls) → OverL ls
      nextOf O = record
        { nodes = λ ψ s → OverL.nodes O (next-lane ψ) s
        ; pools = λ ψ s → OverL.pools O (next-lane ψ) s
        ; rests = λ ψ s → OverL.rests O (next-lane ψ) s }

      nd : ∀ {Δ A} {t : Sub h Δ A} {hb} → (hb ≡ true → Over t) → If hb (Nd t)
      nd O e = Over.nodes (O e) here refl

    mutual
      below : ∀ {Δ A} (t : Sub h Δ A) hb → (hb ≡ true → Over t) → Fold.fold HeldAlg t (lift hb)
      below (pendingˢ s q)                          hb O = nd O
      below (coldˢ s hd ph)                         hb O = nd O
      below (ofˢ p i xs)                            hb O = nd O
      below doneˢ                                   hb O = nd O
      below (mapˢ f s)                              hb O = nd O , below s hb (λ e → restrict (O e) (in-map here) refl)
      below (scanˢ f r s)                           hb O = nd O , below s hb (λ e → restrict (O e) (in-scan here) refl)
      below (takeWhileˢ i p c k tk s)               hb O =
        nd O , below s _ (λ e → let (e₁ , e₂) = ∧-split hb e ; (e₃ , e₄) = ∧-split (val (Kit.live c)) e₂
                                 in restrict (O e₁) (in-take here) (∧-join e₃ (∧-join e₄ refl)))
      below (flatMapˢ op f fl oc k r pl so ls)      hb O =
        nd O , (λ e → Over.pools (O e) here refl) , below so hb (λ e → restrict (O e) (in-outer here) refl) , belowL ls hb (λ e → lanesOf (O e))
      below (connectˢ S c b kb k fd rp e rt src bd) hb O =
        nd O , (λ x → Over.rests (O x) here refl)
        , below src _ (λ x → let (x₁ , x₂) = ∧-split hb x in restrict (O x₁) (in-source here) (∧-join x₂ refl))
        , below bd _ (λ x → let (x₁ , x₂) = ∧-split hb x in restrict (O x₁) (in-body here) (∧-join x₂ refl))
      below (joinˢ j sk l x st)                     hb O = nd O
      below (deferˢ k s)                            hb O = nd O , below s hb (λ e → restrict (O e) (in-defer here) refl)

      belowL : ∀ {Δ B} (ls : List (Lane h Δ B)) hb → (hb ≡ true → OverL ls) → Fold.foldL HeldAlg ls (lift hb)
      belowL []                hb O = lift tt
      belowL (lane c k s ∷ ls) hb O =
        below s _ (λ e → let (e₁ , e₂) = ∧-split hb e in thisOf (O e₁) e₂) , belowL ls hb (λ e → nextOf (O e))

    mutual
      reach : ∀ {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} {hb} → Fold.fold HeldAlg t (lift hb) → hb ≡ true
            → (ψ : Path t u) → seen H ψ ≡ true → Fold.fold HeldAlg u (lift true)
      reach f refl here           _ = f
      reach f refl (in-map ψ)     s = reach (proj₂ f) refl ψ s
      reach f refl (in-scan ψ)    s = reach (proj₂ f) refl ψ s
      reach f refl (in-take {c = c} {tk = tk} ψ) s =
        let (e₁ , e₂) = ∧-split (val (Kit.live c)) s ; (e₃ , e₄) = ∧-split (isTaking tk) e₂ in reach (proj₂ f) (∧-join e₁ e₃) ψ e₄
      reach f refl (in-outer ψ)   s = reach (proj₁ (proj₂ (proj₂ f))) refl ψ s
      reach f refl (in-lanes ψ)   s = reachL (proj₂ (proj₂ (proj₂ f))) refl ψ s
      reach f refl (in-source {bd = bd} ψ) s =
        let (e₁ , e₂) = ∧-split (is-just (part bd)) s in reach (proj₁ (proj₂ (proj₂ f))) e₁ ψ e₂
      reach f refl (in-body {e = e} {t = src} ψ) s =
        let (e₁ , e₂) = ∧-split (is-just (part src) ∨ is-just e) s in reach (proj₂ (proj₂ (proj₂ f))) e₁ ψ e₂
      reach f refl (in-defer ψ)   s = reach (proj₂ f) refl ψ s

      reachL : ∀ {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} {hb} → Fold.foldL HeldAlg ls (lift hb) → hb ≡ true
             → (ψ : PathLanes ls u) → seenL H ψ ≡ true → Fold.fold HeldAlg u (lift true)
      reachL f refl (this-lane {c = c} ψ) s = let (e₁ , e₂) = ∧-split (val (Kit.live c)) s in reach (proj₁ f) e₁ ψ e₂
      reachL f refl (next-lane ψ)         s = reachL (proj₂ f) refl ψ s

    private
      node : ∀ {Δ A} (u : Sub h Δ A) → Below u → Nd u
      node (pendingˢ s q)                          f = f refl
      node (coldˢ s hd ph)                         f = f refl
      node (ofˢ p i xs)                            f = f refl
      node doneˢ                                   f = f refl
      node (mapˢ g s)                              f = proj₁ f refl
      node (scanˢ g r s)                           f = proj₁ f refl
      node (takeWhileˢ i p c k tk s)               f = proj₁ f refl
      node (flatMapˢ op g fl oc k r pl so ls)      f = proj₁ f refl
      node (connectˢ S c b kb k fd rp e rt src bd) f = proj₁ f refl
      node (joinˢ j sk l x st)                     f = f refl
      node (deferˢ k s)                            f = proj₁ f refl

    held-from : ∀ {Δ A} {t : Sub h Δ A} → Below t → Over t
    held-from f = record
      { nodes = λ ψ s → node _ (reach f refl ψ s)
      ; pools = λ ψ s → proj₁ (proj₂ (reach f refl ψ s)) refl
      ; rests = λ ψ s → proj₁ (proj₂ (reach f refl ψ s)) refl }

    held-to : ∀ {Δ A} {t : Sub h Δ A} → Over t → Below t
    held-to {t = t} O = below t true (λ _ → O)

  -- `Each`, node by node.
  module Eaching {h} (H : Heapᴹ h) (P : ∀ {Γ A} → U.Node Γ A → Set) where
    open At H

    Part : ∀ {Δ A} → Sub h Δ A → Set₁
    Part u = ∀ {c} → part u ≡ just c → P c

    Pool : ∀ {Δ A} → Sub h Δ A → Set₁
    Pool (flatMapˢ op f fl oc k r pl so ls) = ∀ {c} → part (flatMapˢ op f fl oc k r pl so ls) ≡ just c → P pl
    Pool _                                   = Lift _ ⊤

    Rest : ∀ {Δ A} → Sub h Δ A → Set₁
    Rest (connectˢ S c b kb k fd rp e rt src bd) =
      ∀ {n} → part (connectˢ S c b kb k fd rp e rt src bd) ≡ just n → part src ≡ nothing → ∀ {c₀} → e ≡ just c₀ → P rt
    Rest _ = Lift _ ⊤

    open Held H Part Pool Rest using (Over; held-from; held-to) renaming (Below to Folded)

    record Below {Δ A} (t : Sub h Δ A) : Set₁ where
      constructor eaching
      field folded : Folded t

    each-from : ∀ {Δ A} {t : Sub h Δ A} → Below t → Each H P t
    each-from (eaching f) = record { parts = Over.nodes O ; pools = Over.pools O ; rests = Over.rests O }
      where O = held-from f

    each-to : ∀ {Δ A} {t : Sub h Δ A} → Each H P t → Below t
    each-to E = eaching (held-to (record { nodes = Each.parts E ; pools = Each.pools E ; rests = Each.rests E }))

  -- `Lingers`, node by node.
  module Lingering {h} (H : Heapᴹ h) where
    open At H

    Pool : ∀ {Δ A} → Sub h Δ A → Set₁
    Pool (flatMapˢ op f fl oc k r pl so ls) = ∀ {c} → part (flatMapˢ op f fl oc k r pl so ls) ≡ just c → Leaves pl (pooled fl so ls) × Restful pl
    Pool _                                   = Lift _ ⊤

    Rest : ∀ {Δ A} → Sub h Δ A → Set₁
    Rest (connectˢ S c b kb k fd rp e rt src bd) =
      ∀ {n} → part (connectˢ S c b kb k fd rp e rt src bd) ≡ just n → part src ≡ nothing → ∀ {c₀} → e ≡ just c₀ → Twin rt (leftover {B = ⊤} src) × Restful rt
    Rest _ = Lift _ ⊤

    open Held H (λ _ → Lift _ ⊤) Pool Rest using (Over; held-from; held-to) renaming (Below to Folded)

    record Below {Δ A} (t : Sub h Δ A) : Set₁ where
      constructor lingering
      field folded : Folded t

    lingers-from : ∀ {Δ A} {t : Sub h Δ A} → Below t → Lingers H t
    lingers-from (lingering f) = record { pools = Over.pools O ; rests = Over.rests O }
      where O = held-from f

    lingers-to : ∀ {Δ A} {t : Sub h Δ A} → Lingers H t → Below t
    lingers-to L = lingering (held-to (record { nodes = λ _ _ → lift tt ; pools = Lingers.pools L ; rests = Lingers.rests L }))

  -- EVERY SEEN FLATMAP'S DONE FLAG READS ITS OUTER GONE, but the flags
  -- named, which read unset: an outer ends at its leaf, its flag set
  -- only once the end has climbed to the flatMap.
  Flagged : ∀ {h} (H : Heapᴹ h) → List (Name h) → ∀ {Δ A} → Flat A h → Sub h Δ A → Set₁
  Flagged H ns fl so = ((cell _ , Flat.outerDone fl) ∈ᴸ ns → At.val H (Flat.outerDone fl) ≡ false)
                     × (¬ ((cell _ , Flat.outerDone fl) ∈ᴸ ns) → At.val H (Flat.outerDone fl) ≡ is-nothing (At.part H so))

  DoneBy : ∀ {h} (H : Heapᴹ h) {Δ A} (t : Sub h Δ A) → List (Name h) → Set₁
  DoneBy {h} H t ns = ∀ {Δ′ A′ B′} {op f fl oc k r pl} {so : Sub h Δ′ A′} {ls : List (Lane h Δ′ B′)}
                    → (ψ : Path t (flatMapˢ op f fl oc k r pl so ls)) → seen H ψ ≡ true → Flagged H ns fl so

  -- Its next event no earlier than `q`.
  Heads : ∀ {Γ A} → Pos → U.Node Γ A → Set
  Heads q c = ∀ {k} → U.headˢ (U.step c) ≡ just k → q ≤ᵖ k

  Meets : ∀ {h} {t : Sub h [] R} {p ctl bs} → Against.CtlAs t p ctl bs → Maybe (U.Node [] R) → U.Node [] R → Set₁
  Meets (Against.noteAs {p = p} {a} _ _ _) n g = Σ (U.Node [] R) λ g′ → n ≡ just g′ × U.step g ≡ U.outˢ p a g′
  Meets _                                  n g = n ≡ just g

  -- THE CONFIGURATION RUNS THE GHOST FROM A RE-ENTRY STATE: a witness
  -- holding every subscription the run reaches, whose open part is the
  -- ghost, and the machine's control and stack its agenda; the machine
  -- sorted, every frame it keeps under where it runs; every node the
  -- ghost holds heading no earlier than where the run is; what it keeps
  -- of ended parts, what they still run.
  record Carried (g : U.Node [] R) (m : Mach) : Set₁ where
    H = Conf.heap (Mach.conf m)
    field
      sane    : Sane []ᴬ g
      placed  : Placedᵍ g []ᴬ
      deep    : Deep g []ᴬ
      tree    : Sub (Conf.world (Mach.conf m)) [] R
      ctlAs   : Against.CtlAs tree (Conf.pos (Mach.conf m)) (Conf.ctl (Mach.conf m)) (Mach.bursts m)
      meets   : Meets ctlAs (At.part H tree) g
      owned′  : OwnedF H tree ctlAs
      kernels : Kernels H tree
      meaning : Meaning H tree
      queue   : Queue H (Conf.pos (Mach.conf m)) (Mach.clock m) (Mach.timers m) tree
      books   : Books tree ctlAs m
      sorted  : Σ Pos λ lo → WellMach lo m
      behind′ : Eaching.Below H (Heads (Conf.pos (Mach.conf m))) tree
      lingers′ : Lingering.Below H tree
      flags   : DoneBy H tree []

    owned : Owned H tree ctlAs
    owned = owned-from {H = H} {t = tree} {ca = ctlAs} owned′

    behind : Each H (Heads (Conf.pos (Mach.conf m))) tree
    behind = Eaching.each-from H (Heads (Conf.pos (Mach.conf m))) behind′

    lingers : Lingers H tree
    lingers = Lingering.lingers-from H lingers′

  -- A RE-ENTRY CONFIGURATION AGAINST THE GHOST: carried, or the root's
  -- completion about to be shown where the ghost ends.
  --
  -- DEAD ROUTE: a contract per kernel over the histories its observer is
  --   delivered, composed by `compile`.  The contract must hold under
  --   every context the subscription runs in, and a `Ref` is a
  --   membership proof into the world, forgeable by any computation at a
  --   larger world, so some context writes `scan`'s accumulator; only
  --   the compiled program's own configuration is honest.
  -- DEAD ROUTE: a relation over `Act` blind to the heap.  `scanᴷ`'s
  --   `next` reads its accumulator from a cell and delivers `f b a`; a
  --   relation whose `readRef` case quantifies over every content must
  --   accept every `b`.
  -- DEAD ROUTE: the owed bound at the run's position.  A scope returning
  --   puts the position back above what it just delivered, so a cut
  --   record owes the events up to its last mark, which lie past it.
  -- DEAD ROUTE: a spec per observer, its triples quantifying over the
  --   frame around it.  A cut flows ownership upstream: `takeWhile`'s
  --   completion cancels its source from inside the source's own
  --   callback, so the source's cells are written within its call and
  --   cannot be framed out of it.  And a frame naming other observers'
  --   specs sits a universe above them, so no heap can store it.
  data Strong (g : U.Node [] R) (m : Mach) : Set₁ where
    carried : Carried g m → Strong g m
    closing : ∀ {h hp p w B k σ K} → Mach.conf m ≡ ⟨_,_,_⟩ {h} hp p (asking {w = w} {B = B} fin k σ K)
            → Mach.ended m ≡ false → U.step g ≡ U.endˢ p → Sane []ᴬ g → Placedᵍ g []ᴬ → Strong g m

  -- THE LAUNCH IS A SUBSCRIPTION ABOUT TO BEGIN: the program, pending at
  -- the root, nothing yet allocated or owed.
  -- A program subscribed heads at a position, never the empty one: each
  -- head is something appended to, or a timer's cascade.
  Opens : Maybe Pos → Set
  Opens nothing        = ⊤
  Opens (just [])      = ⊥
  Opens (just (_ ∷ _)) = ⊤

  opens-++ : ∀ k x → Opens (just (k ++ [ x ]))
  opens-++ []      x = tt
  opens-++ (_ ∷ _) x = tt

  opens-map : ∀ {Γ A B} (f : A → B) (s : U.Step Γ A) → Opens (U.headˢ s) → Opens (U.headˢ (U.mapˢ f s))
  opens-map f (U.outˢ k a c) o = o
  opens-map f (U.skipˢ k c)  o = o
  opens-map f (U.endˢ k)     o = o
  opens-map f U.hushˢ        o = tt

  opens-scan : ∀ {Γ A B} (f : B → A → B) z (s : U.Step Γ A) → Opens (U.headˢ s) → Opens (U.headˢ (U.scanˢ f z s))
  opens-scan f z (U.outˢ k a c) o = o
  opens-scan f z (U.skipˢ k c)  o = o
  opens-scan f z (U.endˢ k)     o = o
  opens-scan f z U.hushˢ        o = tt

  opens-taking : ∀ {Γ A} i (p : A → Bool) k a (c : U.Node Γ A) b → Opens (just k) → Opens (U.headˢ (U.taking i p k a c b))
  opens-taking i     p k a c true  o = o
  opens-taking true  p k a c false o = opens-++ k (ix 0)
  opens-taking false p k a c false o = opens-++ k last

  opens-take : ∀ {Γ A} i (p : A → Bool) (s : U.Step Γ A) → Opens (U.headˢ s) → Opens (U.headˢ (U.takeWhileˢ i p s))
  opens-take i p (U.outˢ k a c) o = opens-taking i p k a c (p a) o
  opens-take i p (U.skipˢ k c)  o = o
  opens-take i p (U.endˢ k)     o = o
  opens-take i p U.hushˢ        o = tt

  opens-outer : ∀ {Γ A B} op (g : A → Pos → U.Node Γ B) (o : U.Node Γ A) (so : U.Step Γ A) → Opens (U.headˢ so)
              → Opens (U.headˢ (U.outerˢ op g o so [] [] U.idleᶜ))
  opens-outer op g o (U.outˢ q a o′) h = opens-++ q (ix 0)
  opens-outer op g o (U.skipˢ q o′)  h = h
  opens-outer op g o (U.endˢ c)      h = h
  opens-outer op g o U.hushˢ         h = tt

  opens-body : ∀ {Γ A B} r (s : U.Source Γ A) (sb : U.Step (A ∷ Γ) B) → Opens (U.headˢ sb) → Opens (U.headˢ (U.bodyˢ r s sb))
  opens-body r s (U.outˢ k a b) h = h
  opens-body r s (U.skipˢ k b)  h = h
  opens-body r s (U.endˢ c)     h = h
  opens-body r s U.hushˢ        h = tt

  opens-source : ∀ {Γ A B} r (b : U.Node (A ∷ Γ) B) sb (s : U.Node Γ A) ss → Opens (U.headˢ sb)
               → Opens (U.headˢ (U.sourceˢ r b sb s ss))
  opens-source r b sb s (U.outˢ q a s′) h with U.beforeˢ (q ++ [ ix 0 ]) sb
  ... | true  = opens-++ q (ix 0)
  ... | false = opens-body r (U.live s) sb h
  opens-source r b sb s (U.skipˢ q s′) h with U.beforeˢ (q ++ [ ix 0 ]) sb
  ... | true  = opens-++ q (ix 0)
  ... | false = opens-body r (U.live s) sb h
  opens-source r b sb s (U.endˢ c) h with U.beforeˢ (c ++ [ ix 0 ]) sb
  ... | true  = opens-++ c (ix 0)
  ... | false = opens-body r (U.live s) sb h
  opens-source r b sb s U.hushˢ h = opens-body r (U.live s) sb h

  opens-burst : ∀ {Γ A t} τ r i (f : Frame A t) → Opens (U.headˢ (U.burstˢ {Γ} τ r i f))
  opens-burst τ r i (emit a k) = opens-++ r (ix i)
  opens-burst τ r i (stall k)  = opens-++ r (ix i)
  opens-burst τ r i (close k)  = opens-++ r (ix i)

  opens-start : ∀ {Γ A} p (m : From A 0) → Opens (U.headˢ (U.step (U.startᶜ {Γ} p m)))
  opens-start p (at zero _ b)    = opens-burst (tick p) p 0 b
  opens-start p (at (suc t) _ b) = opens-burst (tick p) _ 0 b
  opens-start p doneᶠ            = opens-++ p last
  opens-start p quietᶠ           = tt

  opens-of : ∀ {Γ A} p i (xs : List A) → Opens (U.headˢ (U.ofˢ {Γ} p i xs))
  opens-of p i []       = opens-++ p last
  opens-of p i (x ∷ xs) = opens-++ p (ix i)

  opens-subscribe : ∀ {Γ A} (o : Obs Timeline Γ A) p → Opens (U.headˢ (U.step (U.subscribe o p)))
  opens-subscribe (T.cold c)          p = opens-start p (timelineAt c p)
  opens-subscribe T.empty             p = opens-++ p last
  opens-subscribe (T.of xs)           p = opens-of p 0 xs
  opens-subscribe (T.map f s)         p = opens-map f _ (opens-subscribe s p)
  opens-subscribe (T.scan f z s)      p = opens-scan f z _ (opens-subscribe s p)
  opens-subscribe (T.takeWhile i q s) p = opens-take i q _ (opens-subscribe s p)
  opens-subscribe (T.flatMap op f s)  p = opens-outer op (λ a q → U.subscribe (f a) q) (U.subscribe s p) _ (opens-subscribe s p)
  opens-subscribe (T.connect s b)     p =
    opens-source (p ++ [ ix 1 ]) (U.subscribe b (p ++ [ ix 0 ])) _ (U.subscribe s (p ++ [ ix 1 ])) (U.step (U.subscribe s (p ++ [ ix 1 ]))) (opens-subscribe b (p ++ [ ix 0 ]))
  opens-subscribe (T.connected i)     p = tt
  opens-subscribe (T.defer l)         p = opens-++ p (ix 0)

  -- The root comes before every position but the empty one.
  root-least : ∀ a q → root ≤ᵖ (a ∷ q)
  root-least (ix zero)    []      = inj₁ refl
  root-least (ix zero)    (_ ∷ _) = inj₂ refl
  root-least (ix (suc n)) q       = inj₂ refl
  root-least (subᴾ x)     q       = inj₂ refl
  root-least last         q       = inj₂ refl

  heads-open : ∀ {k} (h : Maybe Pos) → Opens h → h ≡ just k → root ≤ᵖ k
  heads-open (just (a ∷ q)) _ refl = root-least a q

  -- A program subscribed at the root heads no earlier than it: its
  -- first event under the root, or a timer's tick past it.
  heads-begin : (o : Obs Timeline [] R) → Heads root (U.subscribe o root)
  heads-begin o e = heads-open _ (opens-subscribe o root) e

  strong-begin : (o : Obs Timeline [] R) → Strong (U.subscribe o root) (begin o)
  strong-begin o = carried record
    { sane    = sane-subscribe o root (λ ())
    ; placed  = placed-subscribe o
    ; deep    = deep-subscribe o
    ; tree    = pendingˢ o root
    ; ctlAs   = Against.subAs here ([] , []ᴬ , same , refl , ≗-refl _) Against.bottomAs []ᴬ
    ; meets   = refl
    ; owned′   = Any.here refl ,ᴼ []ᴬ
    ; kernels = record { holds = _ ; gated = _ ; settled = _ }
    ; meaning = record { fed = _ }
    ; queue   = record { timed = []ᴬ , []ᴬ ; joined = []ᴬ , []ᴬ ; ordered = []ᴸ ; ahead = []ᴬ }
    ; books   = record { fresh = []ᴾ ; clocked = refl , tt ; paidUp = refl ; running = refl }
    ; sorted  = root , begin-well o
    ; behind′  = Eaching.eaching (λ { _ refl → heads-begin o })
    ; lingers′ = Lingering.lingering (λ _ → lift tt)
    ; flags   = λ () }
