{-# OPTIONS --guardedness #-}

module adequacy.Every.Gating where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Bool using (true; false; if_then_else_)
open import Data.Nat using (suc)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapMaybe)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Sum using (_⊎_; [_,_]′) renaming (map₁ to sum-map₁; map₂ to sum-map₂)
open import Data.Unit using (⊤; tt)
open import Function using (id)
open import Level using (Lift; lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_; tabulate to tabulateᴬ; lookup to lookupᴬ)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; _∷_)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴸ_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Any.Properties using (++⁺ˡ; ++⁺ʳ)

import Tree as T
open import Tree using (Obs)
open import denotation.MonotonicList.Events using (Timeline)
open import operation.AbstractObservable using (base; maybe; quiet; gate; list; sink; module Heap; module Run) renaming (module Machine to Shared)
open import operation.PureObservable using (Pureᴾ; Out)
import denotation.Unfold as U
open import adequacy.Strong using (module Strongly)
open import adequacy.Strong.Against using (module StrongAgainst)
open import adequacy.Strong.Held using (module StrongHeld)
open import adequacy.Moves using (module Moving)
open import adequacy.Torn using (module Tearing)
open import adequacy.Retag using (Retag; module Retagging)
open import adequacy.Grow using (module Growing)
open import adequacy.Weaken using (module Weakening)
open import adequacy.Weaken.Heaps using (module WeakeningHeaps)
open import adequacy.Alike using (module Aliking)
open import adequacy.Every using (module Everywhere)

module EverywhereGated (R : Set) where
  open Heap using (World; Sink; Handle; Quiet; cell; slot; _⊑_; wk∋)
  open Run (Pureᴾ R) using (Ref; Subject; Env; Observer; _>>ᴬ_; wkR; wkEl; wkEnv; wkObs; wkSubject; module Kit; module FlatKit)
  open Kit using (Cut)
  open FlatKit using (Flat)
  open Shared Timeline (Out R) using (Heapᴹ; look)
  open Strongly R hiding (Alg; SettledAlg; module Fold)
  open StrongAgainst R
  open StrongHeld R
  open Moving R using (pairs-split; pairs-r; plant; plantᴸ; planted; plantedᴸ)
  open Tearing R using (Off; Alike; attached-alike; stashed-alike; names-path; lanes-path; narrow; apart-r; apart-l)
  open Retagging R using (retag; retagᴸ)
  open Growing R using (wkTree; wkLanes; wkFeed)
  open Weakening R using (Grows; module Grown)
  open WeakeningHeaps R using (module GrownHeaps)
  open Aliking R using (ObsRel; scan-wk; take-wk; outer-wk; laneO-wk; feeder-wk; body-wk; refill-wk; joiner-wk)
  open Everywhere R using (module Over; module Spending; Up; cut; cut-m; via)

  ----------------------------------------------------------------------
  -- GATED, over SPENT

  module Gating {h : World} where
    open Over {h}
    open Spending {h} using (Spent′; SpentF; spent≡; cut≡)

    GatedAlg : Alg
    GatedAlg = record
      { Inh = λ _ _ → Lift _ ⊤ ; InhL = λ _ _ → Lift _ (List (Cut h))
      ; pendᶜ = λ _ _ _ → Lift _ ⊤ ; coldᶜ = λ H s hd ph _ → Lift _ (At.spentʰ H hd ≡ false → At.unended H ph ≡ true)
      ; ofᶜ = λ _ _ _ _ → Lift _ ⊤ ; doneᶜ = λ _ → Lift _ ⊤
      ; mapᶜ = λ _ _ _ X → X ; scanᶜ = λ _ _ _ _ X → X
      ; takeᶜ = λ H _ _ c k _ s X i → (At.val H (Kit.live c) ≡ false → cut k (Spent′ H s (lift tt))) × X i
      ; flatᶜ = λ H _ _ fl _ _ _ _ _ _ X L i → X i × L (lift (At.val H (Flat.lanes fl)))
      ; connᶜ = λ H _ c _ _ k _ _ _ _ src _ X Y i → (At.val H (Kit.live c) ≡ false → cut k (Spent′ H src (lift tt))) × X i × Y (lift tt)
      ; joinᶜ = λ _ _ _ _ _ _ _ → Lift _ ⊤ ; deferᶜ = λ _ _ _ X → X
      ; nilᶜ = λ _ → Lift _ ⊤
      ; consᶜ = λ H c k s X L xs → (At.val H (Kit.live c) ≡ false → c ∈ᴸ lower xs ⊎ cut k (Spent′ H s (lift tt))) × X (lift tt) × L xs }

    open Fold GatedAlg renaming (fold to Gated′; foldL to GatedL′) public

    private
      thrown : ∀ {H H′ : Heapᴹ h} (c : Cut h) {X : Set₁} → look H′ (Kit.live c) ≡ look H (Kit.live c) → (At.val H (Kit.live c) ≡ false → X) → At.val H′ (Kit.live c) ≡ false → X
      thrown c eq g e = g (trans (sym (cong lower eq)) e)

    GatedMono : Mono GatedAlg SpentF
    GatedMono = record
      { cold-m  = λ {hd = hd} ag i g → lift (λ e → lower g (trans (sym (cong lower (ag hd (there (here refl))))) e))
      ; map-m   = λ _ x → x
      ; scan-m  = λ _ _ x → x
      ; take-m  = λ {H} {H′} {c = c} {k = k} ag lo x i (g₁ , g₂) →
                    (λ e → cut-m k (proj₂ lo (lift tt)) (thrown {H} {H′} c (ag (Kit.live c) (here refl)) g₁ e)) , x i g₂
      ; flat-m  = λ {H} {H′} {fl = fl} {L′ = L′} ag _ x _ l i (g₁ , g₂) →
                    x i g₁ , subst (λ z → L′ (lift (lower z))) (sym (ag (Flat.lanes fl) (there (there (there (here refl)))))) (l _ g₂)
      ; conn-m  = λ {H} {H′} {S = S} {c = c} {k = k} ag lo x _ y i (g₁ , g₂ , g₃) →
                    (λ e → cut-m k (proj₂ lo (lift tt)) (thrown {H} {H′} c (ag (Kit.live c) (++⁺ʳ (subjectNames S) (here refl))) g₁ e)) , x i g₂ , y (lift tt) g₃
      ; join-m  = λ _ i x → x
      ; defer-m = λ _ _ x → x
      ; cons-m  = λ {H} {H′} {c = c} {k = k} ag lo x l i (g₁ , g₂ , g₃) →
                    (λ e → sum-map₂ (cut-m k (proj₂ lo (lift tt))) (thrown {H} {H′} c (ag (Kit.live c) (here refl)) g₁ e)) , x (lift tt) g₂ , l i g₃ }

    GatedF : Frame
    GatedF = Field.frame GatedAlg SpentF GatedMono

    -- The pair a flatMap's gate unfolds to.
    _ : ∀ {H : Heapᴹ h} {Δ A B op f fl oc k r pl} {so : Sub h Δ A} {ls : List (Lane h Δ B)}
      → Gated′ H (flatMapˢ op f fl oc k r pl so ls) (lift tt) ≡ (Gated′ H so (lift tt) × GatedL′ H ls (lift (At.val H (Flat.lanes fl))))
    _ = refl

    -- Today's `Gated`, exactly.
    mutual
      gated≡ : (H : Heapᴹ h) → ∀ {Δ A} (u : Sub h Δ A) → At.Gated H u ≡ Gated′ H u (lift tt)
      gated≡ H (pendingˢ s q)                          = refl
      gated≡ H (coldˢ s hd ph)                         = refl
      gated≡ H (ofˢ p i xs)                            = refl
      gated≡ H doneˢ                                   = refl
      gated≡ H (mapˢ f s)                              = gated≡ H s
      gated≡ H (scanˢ f r s)                           = gated≡ H s
      gated≡ H (takeWhileˢ i p c k tk s)               = cong₂ _×_ (cong (λ Z → At.val H (Kit.live c) ≡ false → Z) (cut≡ H k s)) (gated≡ H s)
      gated≡ H (flatMapˢ op f fl oc k r pl so ls)      = cong₂ _×_ (gated≡ H so) (gatedL≡ H (At.val H (Flat.lanes fl)) ls)
      gated≡ H (connectˢ S c b kb k fd rp e rt src bd) =
        cong₂ _×_ (cong (λ Z → At.val H (Kit.live c) ≡ false → Z) (cut≡ H k src)) (cong₂ _×_ (gated≡ H src) (gated≡ H bd))
      gated≡ H (joinˢ j sk l x st)                     = refl
      gated≡ H (deferˢ k s)                            = gated≡ H s

      gatedL≡ : (H : Heapᴹ h) (xs : List (Cut h)) → ∀ {Δ B} (ls : List (Lane h Δ B)) → At.GatedLanes H xs ls ≡ GatedL′ H ls (lift xs)
      gatedL≡ H xs []                = refl
      gatedL≡ H xs (lane c k s ∷ ls) =
        cong₂ _×_ (cong (λ Z → At.val H (Kit.live c) ≡ false → c ∈ᴸ xs ⊎ Z) (cut≡ H k s)) (cong₂ _×_ (gated≡ H s) (gatedL≡ H xs ls))

    private module GFr = Frames GatedF

    -- Today's four frames, as instances.
    gated-alike : ∀ {H H′ : Heapᴹ h} {Δ A} (u : Sub h Δ A) → Alike H H′ (names u) → At.Gated H u → At.Gated H′ u
    gated-alike {H} {H′} u ag = via (gated≡ H u) (gated≡ H′ u) (proj₂ (GFr.frame-alike u ag) (lift tt))

    gated-path : ∀ {H H′ : Heapᴹ h} {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (v : Sub h Δ′ A′) → AllPairs _≢_ (names (plant π v)) → Off H H′ (names v)
               → (At.Gated H u → At.Gated H′ v) → (At.Spent H u → At.Spent H′ v) → At.Gated H t → At.Gated H′ (plant π v)
    gated-path {H} {H′} {t = t} {u} π v ps off hg hs =
      via (gated≡ H t) (gated≡ H′ (plant π v))
        (proj₂ (GFr.frame-path π v ps off ((lift tt , λ _ → via (sym (spent≡ H u)) (sym (spent≡ H′ v)) hs) , λ _ → via (sym (gated≡ H u)) (sym (gated≡ H′ v)) hg)) (lift tt))

    gated-plant : ∀ (H : Heapᴹ h) {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (v : Sub h Δ′ A′)
                → (At.Gated H u → At.Gated H v) → (At.Spent H u → At.Spent H v) → At.Gated H t → At.Gated H (plant π v)
    gated-plant H {t = t} {u} π v hg hs =
      via (gated≡ H t) (gated≡ H (plant π v))
        (proj₂ (GFr.frame-plant π v ((lift tt , λ _ → via (sym (spent≡ H u)) (sym (spent≡ H v)) hs) , λ _ → via (sym (gated≡ H u)) (sym (gated≡ H v)) hg)) (lift tt))

    gated-retag : ∀ (H : Heapᴹ h) {Δ A} (g : Retag Δ) (s : Sub h Δ A) → At.Gated H s → At.Gated H (retag g s)
    gated-retag H g s = via (gated≡ H s) (gated≡ H (retag g s)) (proj₂ (GFr.frame-retag {H} ((lift tt , λ _ x → x) , λ _ x → x) g s) (lift tt))

  ----------------------------------------------------------------------
  -- HOLDS, over what unsubscribing does and a flatMap's lanes

  module Holding {h : World} where
    open Over {h}
    open Canon {h}

    -- What unsubscribing does, and a flatMap's live count and switches.
    Lives : Heapᴹ h → Heapᴹ h → ∀ {Δ B} → List (Lane h Δ B) → Set₁
    Lives H H′ ls = ∀ {c} → c ∈ᴸ At.switches H ls → look H′ (Kit.live c) ≡ look H (Kit.live c)

    UnsubCL : Heapᴹ h → Heapᴹ h → ∀ {Δ B} → List (Lane h Δ B) → List (Lane h Δ B) → Set₁
    UnsubCL H H′ ls ls′ = At.count H′ ls′ ≡ At.count H ls × At.switches H′ ls′ ≡ At.switches H ls × Lives H H′ ls

    unsubs : ∀ {H H′ : Heapᴹ h} {Ba : Base} → (∀ {Δ A} {x y : Sub h Δ A} → Ba x y → unsub x ≡ unsub y)
           → ∀ {Δ A} {u u′ : Sub h Δ A} → Sim H H′ Ba u u′ → unsub u ≡ unsub u′
    unsubs b (pin p)                  = b p
    unsubs b ≈pend                    = refl
    unsubs b (≈cold _)                = refl
    unsubs b ≈of                      = refl
    unsubs b ≈done                    = refl
    unsubs b (≈map s)                 = unsubs b s
    unsubs b (≈scan _ s)              = unsubs b s
    unsubs b (≈take _ _)              = refl
    unsubs b (≈flat _ _ _)            = refl
    unsubs b (≈conn {kb = kb} _ s _)  = cong (_>>ᴬ Kit.unsubscribeVia kb) (unsubs b s)
    unsubs b (≈join _)                = refl
    unsubs b (≈defer _ _)             = refl

    unsubsL : ∀ {H H′ : Heapᴹ h} {Ba : Base} {Δ B} {ls ls′ : List (Lane h Δ B)} → SimL H H′ Ba ls ls′ → UnsubCL H H′ ls ls′
    unsubsL ≈nil = refl , refl , λ ()
    unsubsL {H} {H′} (≈cons {c = c} {k = k} {s = s} {ls = l₀} ag _ ls) =
      cong₂ (λ z n → if lower z then suc n else n) e (proj₁ r) , cong (c ∷_) (proj₁ (proj₂ r)) , lv
      where
        r = unsubsL ls
        e = ag (Kit.live c) (here refl)
        lv : Lives H H′ (lane c k s ∷ l₀)
        lv (here refl) = e
        lv (there m)   = proj₂ (proj₂ r) m

    UnsubF : Frame
    UnsubF = record { C = λ _ _ x y → unsub x ≡ unsub y ; CL = UnsubCL ; sim = unsubs ; simL = λ _ → unsubsL }

    -- What a flatMap hands its lanes.
    record Lanes (Δ : List Set) (B : Set) : Set₁ where
      constructor lanesAt
      field
        {A} : Set
        op  : T.FlatOp
        f   : A → Obs Timeline Δ B
        E   : Env Δ h
        o   : Observer B h
        fl  : Flat A h

    holdsFlat : Heapᴹ h → ∀ {Δ A B} → T.FlatOp → (A → Obs Timeline Δ B) → Flat A h → Cut h → Maybe (Quiet h) → Sink h ⊤
              → U.Node Δ B → Sub h Δ A → List (Lane h Δ B) → (Env Δ h × Observer A h → Set₁) → (Lanes Δ B → Set₁) → Env Δ h × Observer B h → Set₁
    holdsFlat H op f fl oc k r pl so ls X L (E , o) =
      At.val H (Flat.refill fl) ≡ just r × At.slotIs H r (Flat′.refillCb op f E o fl)
      × At.Attached H oc k (unsub so) × X (E , Flat′.outerO op f E o fl oc)
      × At.val H (Flat.active fl) ≡ At.count H ls
      × Σ (List (Cut h)) (λ gone → At.val H (Flat.lanes fl) ++ gone ≡ At.switches H ls × All (λ c → At.val H (Kit.live c) ≡ false) gone)
      × L (lanesAt op f E o fl)

    HoldsAlg : Alg
    HoldsAlg = record
      { Inh = λ Δ A → Env Δ h × Observer A h ; InhL = Lanes
      ; pendᶜ = λ _ _ _ → Lift _ ⊤
      ; coldᶜ = λ H s hd ph i → At.slotIs H s (cbOf (proj₂ i))
      ; ofᶜ = λ _ _ _ _ → Lift _ ⊤ ; doneᶜ = λ _ → Lift _ ⊤
      ; mapᶜ = λ H f s X i → X (proj₁ i , mapO f (proj₂ i))
      ; scanᶜ = λ H f r s X i → X (proj₁ i , scanO f r (proj₂ i))
      ; takeᶜ = λ H i′ p c k tk s X i → At.Attached H c k (unsub s) × X (proj₁ i , takeWhileO i′ p c (proj₂ i))
      ; flatᶜ = holdsFlat
      ; connᶜ = λ H S c b kb k fd rp e rt src bd X Y i →
                  At.Attached H c k (unsub src) × At.val H b ≡ kb × At.Stashed H kb (unsub bd)
                  × X (proj₁ i , feeder S) × Y (S ∷ᴬ proj₁ i , bodyO c (proj₂ i))
      ; joinᶜ = λ H j sk l x st i → At.slotIs H sk (joinerCb l (proj₂ i))
      ; deferᶜ = λ H k s X i → At.Stashed H k (unsub s) × X i
      ; nilᶜ = λ _ → Lift _ ⊤
      ; consᶜ = λ H c k s X L ι → At.Attached H c k (unsub s)
                  × X (Lanes.E ι , Flat′.laneO (Lanes.op ι) (Lanes.f ι) (Lanes.E ι) (Lanes.o ι) (Lanes.fl ι) c) × L ι }

    open Fold HoldsAlg renaming (fold to Holds′; foldL to HoldsL′) public

    private
      slot′ : ∀ {H H′ : Heapᴹ h} {A} (s : Sink h A) {cb} → look H′ s ≡ look H s → At.slotIs H s cb → At.slotIs H′ s cb
      slot′ s {cb} e sl = subst (λ z → CbRel z cb) (sym e) sl

      flat-m′ : ∀ {H H′ : Heapᴹ h} {Δ A B op f fl oc k r pl} {so so′ : Sub h Δ A} {ls ls′ : List (Lane h Δ B)} {X X′ L L′}
              → Alike H H′ (flatNames fl ++ cutNames oc ++ quietName k ++ (slot _ , r) ∷ [])
              → unsub so ≡ unsub so′ → Carry X X′ → UnsubCL H H′ ls ls′ → Carry L L′
              → Carry (holdsFlat H op f fl oc k r pl so ls X L) (holdsFlat H′ op f fl oc k r pl so′ ls′ X′ L′)
      flat-m′ {H} {H′} {fl = fl} {oc} {k} {r} ag ue x (cn , sw , lv) l (E , o) (rf , sl , at , hs , ac , (gone , ge , ga) , hl) =
        trans (cong lower (ag (Flat.refill fl) (there (there (there (there (here refl))))))) rf
        , slot′ {H} {H′} r (ag r (++⁺ʳ (flatNames fl) (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (here refl))))) sl
        , subst (At.Attached H′ oc k) ue
            (attached-alike oc k (ag (Kit.held oc) (++⁺ʳ (flatNames fl) (there (here refl))))
                                 (λ j m → ag j (++⁺ʳ (flatNames fl) (++⁺ʳ (cutNames oc) (++⁺ˡ m)))) at)
        , x _ hs
        , trans (cong lower (ag (Flat.active fl) (here refl))) (trans ac (sym cn))
        , (gone , trans (cong (λ z → lower z ++ gone) (ag (Flat.lanes fl) (there (there (there (here refl)))))) (trans ge (sym sw))
                , tabulateᴬ (λ {c} m → trans (cong lower (lv (subst (c ∈ᴸ_) ge (++⁺ʳ (At.val H (Flat.lanes fl)) m)))) (lookupᴬ ga m)))
        , l _ hl

    HoldsMono : Mono HoldsAlg UnsubF
    HoldsMono = record
      { cold-m  = λ {H} {H′} {s = s} ag i hs → slot′ {H} {H′} s (ag s (here refl)) hs
      ; map-m   = λ _ x i → x _
      ; scan-m  = λ _ _ x i → x _
      ; take-m  = λ {H} {H′} {c = c} {k = k} ag ue x i (at , hs) →
                    subst (At.Attached H′ c k) ue (attached-alike c k (ag (Kit.held c) (there (here refl))) (λ j m → ag j (++⁺ʳ (cutNames c) m)) at) , x _ hs
      ; flat-m  = λ {H} {H′} {Δ} {A} {B} {op} {f} {fl} {oc} {k} {r} {pl} {so} {so′} {ls} {ls′} {X} {X′} {L} {L′}
                  → flat-m′ {H} {H′} {Δ} {A} {B} {op} {f} {fl} {oc} {k} {r} {pl} {so} {so′} {ls} {ls′} {X} {X′} {L} {L′}
      ; conn-m  = λ {H} {H′} {S = S} {c = c} {b = b} {kb = kb} {k = k} ag us x ub y i (at , be , st , hs , hb) →
                    subst (At.Attached H′ c k) us
                      (attached-alike c k (ag (Kit.held c) (++⁺ʳ (subjectNames S) (there (here refl))))
                                          (λ j m → ag j (++⁺ʳ (subjectNames S) (++⁺ʳ (cutNames c) (there (++⁺ʳ (quietName kb) m))))) at)
                    , trans (cong lower (ag b (++⁺ʳ (subjectNames S) (++⁺ʳ (cutNames c) (here refl))))) be
                    , subst (At.Stashed H′ kb) ub (stashed-alike kb (λ j m → ag j (++⁺ʳ (subjectNames S) (++⁺ʳ (cutNames c) (there (++⁺ˡ m))))) st)
                    , x _ hs , y _ hb
      ; join-m  = λ {H} {H′} {sk = sk} ag i hs → slot′ {H} {H′} sk (ag sk (here refl)) hs
      ; defer-m = λ {H} {H′} {k = k} ag ue x i (st , hs) → subst (At.Stashed H′ k) ue (stashed-alike k ag st) , x i hs
      ; cons-m  = λ {H} {H′} {c = c} {k = k} ag ue x l i (at , hs , hl) →
                    subst (At.Attached H′ c k) ue (attached-alike c k (ag (Kit.held c) (there (here refl))) (λ j m → ag j (++⁺ʳ (cutNames c) m)) at)
                    , x _ hs , l i hl }

    HoldsF : Frame
    HoldsF = Field.frame HoldsAlg UnsubF HoldsMono

    -- Today's `Holds`, exactly.
    mutual
      holds≡ : (H : Heapᴹ h) → ∀ {Δ A} (u : Sub h Δ A) (E : Env Δ h) (o : Observer A h) → At.Holds H u E o ≡ Holds′ H u (E , o)
      holds≡ H (pendingˢ s q)                          E o = refl
      holds≡ H (coldˢ s hd ph)                         E o = refl
      holds≡ H (ofˢ p i xs)                            E o = refl
      holds≡ H doneˢ                                   E o = refl
      holds≡ H (mapˢ f s)                              E o = holds≡ H s E _
      holds≡ H (scanˢ f r s)                           E o = holds≡ H s E _
      holds≡ H (takeWhileˢ i p c k tk s)               E o = cong₂ _×_ refl (holds≡ H s E _)
      holds≡ H (flatMapˢ op f fl oc k r pl so ls)      E o =
        cong₂ _×_ refl (cong₂ _×_ refl (cong₂ _×_ refl (cong₂ _×_ (holds≡ H so E _) (cong₂ _×_ refl (cong₂ _×_ refl (holdsL≡ H op f E o fl ls))))))
      holds≡ H (connectˢ S c b kb k fd rp e rt src bd) E o =
        cong₂ _×_ refl (cong₂ _×_ refl (cong₂ _×_ refl (cong₂ _×_ (holds≡ H src E _) (holds≡ H bd _ _))))
      holds≡ H (joinˢ j sk l x st)                     E o = refl
      holds≡ H (deferˢ k s)                            E o = cong₂ _×_ refl (holds≡ H s E o)

      holdsL≡ : (H : Heapᴹ h) → ∀ {Δ A B} op (f : A → Obs Timeline Δ B) E o fl (ls : List (Lane h Δ B))
              → At.HoldsLanes H op f E o fl ls ≡ HoldsL′ H ls (lanesAt op f E o fl)
      holdsL≡ H op f E o fl []                = refl
      holdsL≡ H op f E o fl (lane c k s ∷ ls) = cong₂ _×_ refl (cong₂ _×_ (holds≡ H s E _) (holdsL≡ H op f E o fl ls))

    private module HFr = Frames HoldsF

    -- Today's four frames, as instances.
    holds-alike : ∀ {H H′ : Heapᴹ h} {Δ A} (u : Sub h Δ A) → Alike H H′ (names u) → ∀ {E o} → At.Holds H u E o → At.Holds H′ u E o
    holds-alike {H} {H′} u ag {E} {o} = via (holds≡ H u E o) (holds≡ H′ u E o) (proj₂ (HFr.frame-alike u ag) (E , o))

    holds-path : ∀ {H H′ : Heapᴹ h} {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (v : Sub h Δ′ A′) → AllPairs _≢_ (names (plant π v))
               → Off H H′ (names v) → unsub u ≡ unsub v → (∀ {E o} → At.Holds H u E o → At.Holds H′ v E o)
               → ∀ {E o} → At.Holds H t E o → At.Holds H′ (plant π v) E o
    holds-path {H} {H′} {t = t} {u} π v ps off ue hv {E} {o} =
      via (holds≡ H t E o) (holds≡ H′ (plant π v) E o)
        (proj₂ (HFr.frame-path π v ps off (ue , λ { (E′ , o′) → via (sym (holds≡ H u E′ o′)) (sym (holds≡ H′ v E′ o′)) hv })) (E , o))

    holds-plant : ∀ (H : Heapᴹ h) {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (v : Sub h Δ′ A′)
                → unsub u ≡ unsub v → (∀ {E o} → At.Holds H u E o → At.Holds H v E o)
                → ∀ {E o} → At.Holds H t E o → At.Holds H (plant π v) E o
    holds-plant H {t = t} {u} π v ue hv {E} {o} =
      via (holds≡ H t E o) (holds≡ H (plant π v) E o)
        (proj₂ (HFr.frame-plant π v (ue , λ { (E′ , o′) → via (sym (holds≡ H u E′ o′)) (sym (holds≡ H v E′ o′)) hv })) (E , o))

    holds-retag : ∀ (H : Heapᴹ h) {Δ A} (g : Retag Δ) (s : Sub h Δ A) {E o} → At.Holds H s E o → At.Holds H (retag g s) E o
    holds-retag H g s {E} {o} = via (holds≡ H s E o) (holds≡ H (retag g s) E o) (proj₂ (HFr.frame-retag {H} (refl , λ _ x → x) g s) (E , o))

  ----------------------------------------------------------------------
  -- SETTLED, over what a subscription owes

  module Settling {h : World} where
    open Over {h}

    owes : ∀ {H H′ : Heapᴹ h} {Ba : Base} → (∀ {Δ A} {x y : Sub h Δ A} → Ba x y → Up (Owes y → Owes x))
         → ∀ {Δ A} {u u′ : Sub h Δ A} → Sim H H′ Ba u u′ → Owes u′ → Owes u
    owes b (pin p)       = lower (b p)
    owes b ≈pend         = id
    owes b (≈cold _)     = id
    owes b ≈of           = id
    owes b ≈done         = id
    owes b (≈map s)      = owes b s
    owes b (≈scan _ s)   = owes b s
    owes b (≈take _ _)   = id
    owes b (≈flat _ _ _) = id
    owes b (≈conn _ s _) = owes b s
    owes b (≈join _)     = id
    owes b (≈defer _ _)  = id

    OwesF : Frame
    OwesF = record { C = λ _ _ x y → Up (Owes y → Owes x) ; CL = λ _ _ _ _ → Lift _ ⊤ ; sim = λ b s → lift (owes b s) ; simL = λ _ _ → lift tt }

    SettledAlg : Alg
    SettledAlg = record
      { Inh = λ _ _ → Lift _ ⊤ ; InhL = λ _ _ → Lift _ ⊤
      ; pendᶜ = λ _ _ _ → Lift _ ⊤ ; coldᶜ = λ _ _ _ _ _ → Lift _ ⊤ ; ofᶜ = λ _ _ _ _ → Lift _ ⊤ ; doneᶜ = λ _ → Lift _ ⊤
      ; mapᶜ = λ _ _ _ X → X ; scanᶜ = λ _ _ _ _ X → X
      ; takeᶜ = λ _ _ _ _ k _ s X i → Up (Begun k s) × X i
      ; flatᶜ = λ _ _ _ _ _ k _ _ so _ X L i → Up (Begun k so) × X i × L (lift tt)
      ; connᶜ = λ _ _ _ _ kb k _ _ _ _ src bd X Y i → Up (Begun k src) × Up (Begun kb bd) × X i × Y (lift tt)
      ; joinᶜ = λ _ _ _ _ _ _ _ → Lift _ ⊤
      ; deferᶜ = λ _ k s X i → Up (Begun k s) × X i
      ; nilᶜ = λ _ → Lift _ ⊤
      ; consᶜ = λ _ _ k s X L i → Up (Begun k s) × X (lift tt) × L i }

    open Fold SettledAlg renaming (fold to Settled′; foldL to SettledL′) public

    private
      begun-m : ∀ k {Δ A} {s s′ : Sub h Δ A} → Up (Owes s′ → Owes s) → Up (Begun k s) → Up (Begun k s′)
      begun-m nothing  f b = b
      begun-m (just _) f b = lift (λ ow → lower b (lower f ow))

    SettledMono : Mono SettledAlg OwesF
    SettledMono = record
      { cold-m  = λ _ i x → x
      ; map-m   = λ _ x → x
      ; scan-m  = λ _ _ x → x
      ; take-m  = λ {k = k} _ ow x i (b , st) → begun-m k ow b , x i st
      ; flat-m  = λ {k = k} _ ow x _ l i (b , st , sl) → begun-m k ow b , x i st , l (lift tt) sl
      ; conn-m  = λ {kb = kb} {k = k} _ os x ob y i (b₁ , b₂ , s₁ , s₂) → begun-m k os b₁ , begun-m kb ob b₂ , x i s₁ , y (lift tt) s₂
      ; join-m  = λ _ i x → x
      ; defer-m = λ {k = k} _ ow x i (b , st) → begun-m k ow b , x i st
      ; cons-m  = λ {k = k} _ ow x l i (b , st , sl) → begun-m k ow b , x (lift tt) st , l i sl }

    SettledF : Frame
    SettledF = Field.frame SettledAlg OwesF SettledMono

    -- Today's `Settled`, both ways.
    mutual
      settled-to : ∀ {H : Heapᴹ h} {Δ A} (u : Sub h Δ A) → Settled u → Settled′ H u (lift tt)
      settled-to (pendingˢ s q)                          st                    = lift tt
      settled-to (coldˢ s hd ph)                         st                    = lift tt
      settled-to (ofˢ p i xs)                            st                    = lift tt
      settled-to doneˢ                                   st                    = lift tt
      settled-to (mapˢ f s)                              st                    = settled-to s st
      settled-to (scanˢ f r s)                           st                    = settled-to s st
      settled-to (takeWhileˢ i p c k tk s)               (b , st)              = lift b , settled-to s st
      settled-to (flatMapˢ op f fl oc k r pl so ls)      (b , st , sl)         = lift b , settled-to so st , settledL-to ls sl
      settled-to (connectˢ S c b kb k fd rp e rt src bd) (b₁ , b₂ , s₁ , s₂)   = lift b₁ , lift b₂ , settled-to src s₁ , settled-to bd s₂
      settled-to (joinˢ j sk l x st)                     _                     = lift tt
      settled-to (deferˢ k s)                            (b , st)              = lift b , settled-to s st

      settledL-to : ∀ {H : Heapᴹ h} {Δ B} (ls : List (Lane h Δ B)) → SettledLanes ls → SettledL′ H ls (lift tt)
      settledL-to []                _             = lift tt
      settledL-to (lane c k s ∷ ls) (b , st , sl) = lift b , settled-to s st , settledL-to ls sl

    mutual
      settled-from : ∀ {H : Heapᴹ h} {Δ A} (u : Sub h Δ A) → Settled′ H u (lift tt) → Settled u
      settled-from (pendingˢ s q)                          _                     = tt
      settled-from (coldˢ s hd ph)                         _                     = tt
      settled-from (ofˢ p i xs)                            _                     = tt
      settled-from doneˢ                                   _                     = tt
      settled-from (mapˢ f s)                              st                    = settled-from s st
      settled-from (scanˢ f r s)                           st                    = settled-from s st
      settled-from (takeWhileˢ i p c k tk s)               (b , st)              = lower b , settled-from s st
      settled-from (flatMapˢ op f fl oc k r pl so ls)      (b , st , sl)         = lower b , settled-from so st , settledL-from ls sl
      settled-from (connectˢ S c b kb k fd rp e rt src bd) (b₁ , b₂ , s₁ , s₂)   = lower b₁ , lower b₂ , settled-from src s₁ , settled-from bd s₂
      settled-from (joinˢ j sk l x st)                     _                     = tt
      settled-from (deferˢ k s)                            (b , st)              = lower b , settled-from s st

      settledL-from : ∀ {H : Heapᴹ h} {Δ B} (ls : List (Lane h Δ B)) → SettledL′ H ls (lift tt) → SettledLanes ls
      settledL-from []                _             = tt
      settledL-from (lane c k s ∷ ls) (b , st , sl) = lower b , settled-from s st , settledL-from ls sl

    private module StFr = Frames SettledF

    settled-plant : ∀ (H : Heapᴹ h) {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (v : Sub h Δ′ A′)
                  → (Owes v → Owes u) → (Settled u → Settled v) → Settled t → Settled (plant π v)
    settled-plant H {t = t} {u = u} π v ov sv st =
      settled-from {H} (plant π v) (proj₂ (StFr.frame-plant {H} π v (lift ov , λ _ x → settled-to v (sv (settled-from u x)))) (lift tt) (settled-to t st))

    settled-retag : ∀ (H : Heapᴹ h) {Δ A} (g : Retag Δ) (s : Sub h Δ A) → Settled s → Settled (retag g s)
    settled-retag H g s st = settled-from {H} (retag g s) (proj₂ (StFr.frame-retag {H} (lift id , λ _ x → x) g s) (lift tt) (settled-to s st))

  ----------------------------------------------------------------------
  -- GROWN: a part read through a weakening, for every tree, from one
  -- clause per node.  No pins: a world grown by allocation moves no
  -- name a tree holds.

  module Growth {h v : World} (τ : h ⊑ v) (H : Heapᴹ h) (H′ : Heapᴹ v) where
    RCarry : ∀ {I I′ : Set₁} → (I → I′ → Set₁) → (I → Set₁) → (I′ → Set₁) → Set₁
    RCarry Q X X′ = ∀ i i′ → Q i i′ → X i → X′ i′

    cut-g : (k : Maybe (Quiet h)) {X X′ : Set₁} → (X → X′) → cut k X → cut (mapMaybe (wk∋ τ) k) X′
    cut-g nothing  f x = x
    cut-g (just _) f x = f x

    record GFrame : Set₂ where
      field
        G     : ∀ {Δ A} → Sub h Δ A → Set₁
        GL    : ∀ {Δ B} → List (Lane h Δ B) → Set₁
        grow  : ∀ {Δ A} (u : Sub h Δ A) → G u
        growL : ∀ {Δ B} (ls : List (Lane h Δ B)) → GL ls

    -- The conjunction of two grow frames is a grow frame.
    _⊛_ : GFrame → GFrame → GFrame
    F₁ ⊛ F₂ = record
      { G     = λ u → GFrame.G F₁ u × GFrame.G F₂ u
      ; GL    = λ ls → GFrame.GL F₁ ls × GFrame.GL F₂ ls
      ; grow  = λ u → GFrame.grow F₁ u , GFrame.grow F₂ u
      ; growL = λ ls → GFrame.growL F₁ ls , GFrame.growL F₂ ls }

    unitᵍ : GFrame
    unitᵍ = record { G = λ _ → Lift _ ⊤ ; GL = λ _ → Lift _ ⊤ ; grow = λ _ → lift tt ; growL = λ _ → lift tt }

    module Cl (a : Over.Alg {h}) (a′ : Over.Alg {v}) where
      open Over.Alg {h} a public
      open Over.Alg {v} a′ public renaming
        ( Inh to Inh′ ; InhL to InhL′ ; pendᶜ to pendᶜ′ ; coldᶜ to coldᶜ′ ; ofᶜ to ofᶜ′ ; doneᶜ to doneᶜ′ ; mapᶜ to mapᶜ′ ; scanᶜ to scanᶜ′
        ; takeᶜ to takeᶜ′ ; flatᶜ to flatᶜ′ ; connᶜ to connᶜ′ ; joinᶜ to joinᶜ′ ; deferᶜ to deferᶜ′ ; nilᶜ to nilᶜ′ ; consᶜ to consᶜ′ )
      open Over.Fold {h} a public
      open Over.Fold {v} a′ public renaming (fold to fold′; foldL to foldL′)

    -- Each clause read through the weakening, inherited values related
    -- by `IR`, given each child's lower part and part grown.
    record GMono (a : Over.Alg {h}) (a′ : Over.Alg {v}) (lo : GFrame) : Set₂ where
      open Cl a a′
      open GFrame lo using (G; GL)
      field
        IR      : ∀ {Δ X} → Inh Δ X → Inh′ Δ X → Set₁
        IRL     : ∀ {Δ X} → InhL Δ X → InhL′ Δ X → Set₁
        pend-g  : ∀ {Δ X} {s : Obs Timeline Δ X} {q} → RCarry IR (pendᶜ s q) (pendᶜ′ s q)
        cold-g  : ∀ {Δ X} {s : Sink h X} {hd ph} → RCarry (IR {Δ}) (coldᶜ H s hd ph) (coldᶜ′ H′ (wk∋ τ s) (wk∋ τ hd) ph)
        of-g    : ∀ {Δ} {X : Set} {p i} {xs : List X} → RCarry (IR {Δ}) (ofᶜ p i xs) (ofᶜ′ p i xs)
        done-g  : ∀ {Δ X} → RCarry (IR {Δ} {X}) doneᶜ doneᶜ′
        map-g   : ∀ {Δ X} {B : Set} {f : X → B} {s : Sub h Δ X} {Y Y′} → G s → RCarry IR Y Y′
                → RCarry IR (mapᶜ H f s Y) (mapᶜ′ H′ f (wkTree τ s) Y′)
        scan-g  : ∀ {Δ X B} {f : B → X → B} {r} {s : Sub h Δ X} {Y Y′} → G s → RCarry IR Y Y′
                → RCarry IR (scanᶜ H f r s Y) (scanᶜ′ H′ f (wkR τ r) (wkTree τ s) Y′)
        take-g  : ∀ {Δ X i p c k tk} {s : Sub h Δ X} {Y Y′} → G s → RCarry IR Y Y′
                → RCarry IR (takeᶜ H i p c k tk s Y) (takeᶜ′ H′ i p (Kit.wkCut τ c) (mapMaybe (wk∋ τ) k) tk (wkTree τ s) Y′)
        flat-g  : ∀ {Δ X B op f fl oc k r pl} {so : Sub h Δ X} {ls : List (Lane h Δ B)} {Y Y′ L L′}
                → G so → RCarry IR Y Y′ → GL ls → RCarry IRL L L′
                → RCarry IR (flatᶜ H op f fl oc k r pl so ls Y L)
                            (flatᶜ′ H′ op f (FlatKit.wkFlat τ fl) (Kit.wkCut τ oc) (mapMaybe (wk∋ τ) k) (wk∋ τ r) pl (wkTree τ so) (wkLanes τ ls) Y′ L′)
        conn-g  : ∀ {Δ X B S c b kb k fd rp e rt} {src : Sub h Δ X} {bd : Sub h (X ∷ Δ) B} {Y Y′ Z Z′}
                → G src → RCarry IR Y Y′ → G bd → RCarry IR Z Z′
                → RCarry IR (connᶜ H S c b kb k fd rp e rt src bd Y Z)
                            (connᶜ′ H′ (wkSubject τ S) (Kit.wkCut τ c) (wkR τ b) (mapMaybe (wk∋ τ) kb) (mapMaybe (wk∋ τ) k) (wkFeed τ fd) rp e rt
                                    (wkTree τ src) (wkTree τ bd) Y′ Z′)
        join-g  : ∀ {Δ X j sk l} {x : X ∈ᴸ Δ} {st} → RCarry (IR {Δ}) (joinᶜ H j sk l x st) (joinᶜ′ H′ j (wk∋ τ sk) (wkR τ l) x st)
        defer-g : ∀ {Δ X k} {s : Sub h Δ X} {Y Y′} → G s → RCarry IR Y Y′
                → RCarry IR (deferᶜ H k s Y) (deferᶜ′ H′ (mapMaybe (wk∋ τ) k) (wkTree τ s) Y′)
        nil-g   : ∀ {Δ B} → RCarry (IRL {Δ} {B}) nilᶜ nilᶜ′
        cons-g  : ∀ {Δ B c k} {s : Sub h Δ B} {Y Y′ L L′} → G s → RCarry IR Y Y′ → RCarry IRL L L′
                → RCarry IRL (consᶜ H c k s Y L) (consᶜ′ H′ (Kit.wkCut τ c) (mapMaybe (wk∋ τ) k) (wkTree τ s) Y′ L′)

    -- A PART GROWS, over its lower part.
    module GField (a : Over.Alg {h}) (a′ : Over.Alg {v}) (lo : GFrame) (gm : GMono a a′ lo) where
      open Cl a a′
      open GMono gm
      private module L = GFrame lo

      mutual
        carry : ∀ {Δ X} (u : Sub h Δ X) → RCarry IR (fold H u) (fold′ H′ (wkTree τ u))
        carry (pendingˢ s q)                          = pend-g {s = s} {q}
        carry (coldˢ s hd ph)                         = cold-g {s = s} {hd} {ph}
        carry (ofˢ p i xs)                            = of-g {p = p} {i} {xs}
        carry doneˢ                                   = done-g
        carry (mapˢ f s)                              = map-g {f = f} {s} (L.grow s) (carry s)
        carry (scanˢ f r s)                           = scan-g {f = f} {r} {s} (L.grow s) (carry s)
        carry (takeWhileˢ i p c k tk s)               = take-g {i = i} {p} {c} {k} {tk} {s} (L.grow s) (carry s)
        carry (flatMapˢ op f fl oc k r pl so ls)      =
          flat-g {op = op} {f} {fl} {oc} {k} {r} {pl} {so} {ls} (L.grow so) (carry so) (L.growL ls) (carryL ls)
        carry (connectˢ S c b kb k fd rp e rt src bd) =
          conn-g {S = S} {c} {b} {kb} {k} {fd} {rp} {e} {rt} {src} {bd} (L.grow src) (carry src) (L.grow bd) (carry bd)
        carry (joinˢ j sk l x st)                     = join-g {j = j} {sk} {l} {x} {st}
        carry (deferˢ k s)                            = defer-g {k = k} {s} (L.grow s) (carry s)

        carryL : ∀ {Δ B} (ls : List (Lane h Δ B)) → RCarry IRL (foldL H ls) (foldL′ H′ (wkLanes τ ls))
        carryL []                = nil-g
        carryL (lane c k s ∷ ls) = cons-g {c = c} {k} {s} (L.grow s) (carry s) (carryL ls)

      gframe : GFrame
      gframe = record
        { G     = λ u → L.G u × RCarry IR (fold H u) (fold′ H′ (wkTree τ u))
        ; GL    = λ ls → L.GL ls × RCarry IRL (foldL H ls) (foldL′ H′ (wkLanes τ ls))
        ; grow  = λ u → L.grow u , carry u
        ; growL = λ ls → L.growL ls , carryL ls }

  -- Today's grow lemmas, as instances.
  module Growths {h v : World} (τ : h ⊑ v) {H : Heapᴹ h} {H′ : Heapᴹ v} (gr : Grows τ H H′) where
    open Growth τ H H′
    private
      module Gw = Grown τ
      module Gw′ = GrownHeaps τ

      open Grows gr using (cells)

    SpentG : GFrame
    SpentG = GField.gframe (Spending.SpentAlg {h}) (Spending.SpentAlg {v}) unitᵍ record
      { IR = λ _ _ → Lift _ ⊤ ; IRL = λ _ _ → Lift _ ⊤
      ; pend-g  = λ _ _ _ x → x
      ; cold-g  = λ {hd = hd} _ _ _ sp → lift (trans (Grows.handles gr hd) (lower sp))
      ; of-g    = λ _ _ _ x → x
      ; done-g  = λ _ _ _ x → x
      ; map-g   = λ _ y → y
      ; scan-g  = λ _ y → y
      ; take-g  = λ {k = k} _ y ι ι′ w x → cut-g k (y ι ι′ w) x
      ; flat-g  = λ {k = k} _ y _ l ι ι′ w (c₁ , c₂) → cut-g k (y ι ι′ w) c₁ , l _ _ (lift tt) c₂
      ; conn-g  = λ {kb = kb} {k = k} _ y _ z ι ι′ w (c₁ , c₂) → cut-g k (y ι ι′ w) c₁ , cut-g kb (z _ _ (lift tt)) c₂
      ; join-g  = λ _ _ _ x → x
      ; defer-g = λ {k = k} _ y ι ι′ w x → cut-g k (y ι ι′ w) x
      ; nil-g   = λ _ _ _ x → x
      ; cons-g  = λ {k = k} _ y l ι ι′ w (c₁ , c₂) → cut-g k (y _ _ (lift tt)) c₁ , l ι ι′ w c₂ }

    private
      sp : ∀ {Δ X} {s : Sub h Δ X} → GFrame.G SpentG s → Spending.Spent′ H s (lift tt) → Spending.Spent′ H′ (wkTree τ s) (lift tt)
      sp lo = proj₂ lo (lift tt) (lift tt) (lift tt)

    GatedG : GFrame
    GatedG = GField.gframe (Gating.GatedAlg {h}) (Gating.GatedAlg {v}) SpentG record
      { IR = λ _ _ → Lift _ ⊤
      ; IRL = λ xs xs′ → Lift _ (lower xs′ ≡ wkEl (list Kit.cutTy) τ (lower xs))
      ; pend-g  = λ _ _ _ x → x
      ; cold-g  = λ {hd = hd} _ _ _ g → lift (λ e → lower g (trans (sym (Grows.handles gr hd)) e))
      ; of-g    = λ _ _ _ x → x
      ; done-g  = λ _ _ _ x → x
      ; map-g   = λ _ y → y
      ; scan-g  = λ _ y → y
      ; take-g  = λ {c = c} {k = k} {s = s} lo y ι ι′ w (g₁ , g₂) →
                    (λ e → cut-g k (sp {s = s} lo) (g₁ (trans (sym (cells (Kit.live c))) e))) , y ι ι′ w g₂
      ; flat-g  = λ {fl = fl} _ y _ l ι ι′ w (g₁ , g₂) → y ι ι′ w g₁ , l _ _ (lift (cells (FlatKit.Flat.lanes fl))) g₂
      ; conn-g  = λ {c = c} {k = k} {src = src} lo y _ z ι ι′ w (g₁ , g₂ , g₃) →
                    (λ e → cut-g k (sp {s = src} lo) (g₁ (trans (sym (cells (Kit.live c))) e))) , y ι ι′ w g₂ , z _ _ (lift tt) g₃
      ; join-g  = λ _ _ _ x → x
      ; defer-g = λ _ y → y
      ; nil-g   = λ _ _ _ x → x
      ; cons-g  = λ {c = c} {k = k} {s = s} lo y l ι ι′ w (g₁ , g₂ , g₃) →
                    (λ e → sum-map₁ (λ m → subst (Kit.wkCut τ c ∈ᴸ_) (sym (lower w)) (Gw′.listed-wk gr (lower ι) m))
                                    (sum-map₂ (cut-g k (sp {s = s} lo)) (g₁ (trans (sym (cells (Kit.live c))) e))))
                    , y _ _ (lift tt) g₂ , l ι ι′ w g₃ }

    -- What a flatMap hands its lanes, read through the weakening.
    data LanesR {Δ B} : Holding.Lanes {h} Δ B → Holding.Lanes {v} Δ B → Set₁ where
      lanesR : ∀ {X op f E E′ o o′} {fl : Flat X h} → wkEnv τ E ≡ E′ → ObsRel (wkObs τ o) o′
             → LanesR (Holding.lanesAt op f E o fl) (Holding.lanesAt op f E′ o′ (FlatKit.wkFlat τ fl))

    private
      HIR : ∀ {Δ X} → Env Δ h × Observer X h → Env Δ v × Observer X v → Set₁
      HIR i i′ = (wkEnv τ (proj₁ i) ≡ proj₁ i′) × ObsRel (wkObs τ (proj₂ i)) (proj₂ i′)

      flat-hg : ∀ {Δ X B op f fl oc k r pl} {so : Sub h Δ X} {ls : List (Lane h Δ B)} {Y Y′ L L′}
              → RCarry HIR Y Y′ → RCarry LanesR L L′
              → RCarry HIR (Holding.holdsFlat H op f fl oc k r pl so ls Y L)
                           (Holding.holdsFlat H′ op f (FlatKit.wkFlat τ fl) (Kit.wkCut τ oc) (mapMaybe (wk∋ τ) k) (wk∋ τ r) pl (wkTree τ so) (wkLanes τ ls) Y′ L′)
      flat-hg {op = op} {f} {fl} {oc} {k} {r} {so = so} {ls} y l (E , o) (E′ , o′) (e , oR) (rf , rs , a , hs , ac , (gone , sw , dead) , hl) =
          trans (cells (FlatKit.Flat.refill fl)) (cong (wkEl (maybe (sink ⊤)) τ) rf)
        , Gw′.slot-grow gr r rs (refill-wk τ op f fl e oR)
        , Gw′.attached-grow gr oc k so a
        , y _ _ (e , outer-wk τ op f fl oc e oR) hs
        , trans (cells (FlatKit.Flat.active fl)) (trans ac (sym (Gw′.count-grow gr ls)))
        , ( wkEl (list Kit.cutTy) τ gone
          , trans (cong (_++ wkEl (list Kit.cutTy) τ gone) (cells (FlatKit.Flat.lanes fl)))
              (trans (sym (Gw′.wkEl-++ gr {Kit.cutTy} (At.val H (FlatKit.Flat.lanes fl)) gone)) (trans (cong (wkEl (list Kit.cutTy) τ) sw) (sym (Gw′.switches-grow gr ls))))
          , Gw′.dead-grow gr gone dead )
        , l _ _ (lanesR e oR) hl

      conn-hg : ∀ {Δ X B S c b kb k fd rp e rt} {src : Sub h Δ X} {bd : Sub h (X ∷ Δ) B} {Y Y′ Z Z′}
              → RCarry HIR Y Y′ → RCarry HIR Z Z′
              → RCarry HIR (Over.Alg.connᶜ (Holding.HoldsAlg {h}) H S c b kb k fd rp e rt src bd Y Z)
                           (Over.Alg.connᶜ (Holding.HoldsAlg {v}) H′ (wkSubject τ S) (Kit.wkCut τ c) (wkR τ b) (mapMaybe (wk∋ τ) kb) (mapMaybe (wk∋ τ) k) (wkFeed τ fd) rp e rt
                                           (wkTree τ src) (wkTree τ bd) Y′ Z′)
      conn-hg {S = S} {c} {b} {kb} {k} {src = src} {bd} y z (E , o) (E′ , o′) (e , oR) (a , eb , st , hs , hb) =
          Gw′.attached-grow gr c k src a
        , trans (cells b) (trans (cong (wkEl (maybe quiet) τ) eb) (Gw′.quiet-wk gr kb))
        , Gw′.stashed-grow gr kb bd st
        , y _ _ (e , feeder-wk τ S) hs
        , z _ _ (cong (wkSubject τ S ∷ᴬ_) e , body-wk τ c oR) hb

      cons-hg : ∀ {Δ B c k} {s : Sub h Δ B} {Y Y′ L L′} → RCarry HIR Y Y′ → RCarry LanesR L L′
              → RCarry LanesR (Over.Alg.consᶜ (Holding.HoldsAlg {h}) H c k s Y L)
                              (Over.Alg.consᶜ (Holding.HoldsAlg {v}) H′ (Kit.wkCut τ c) (mapMaybe (wk∋ τ) k) (wkTree τ s) Y′ L′)
      cons-hg {c = c} {k} {s} y l _ _ (lanesR {op = op} {f} {fl = fl} e oR) (a , hs , hl) =
        Gw′.attached-grow gr c k s a , y _ _ (e , laneO-wk τ op f fl c e oR) hs , l _ _ (lanesR e oR) hl

    HoldsG : GFrame
    HoldsG = GField.gframe (Holding.HoldsAlg {h}) (Holding.HoldsAlg {v}) unitᵍ record
      { IR = HIR ; IRL = LanesR
      ; pend-g  = λ _ _ _ x → x
      ; cold-g  = λ {s = s} _ _ w hs → Gw′.slot-grow gr s hs (proj₂ w)
      ; of-g    = λ _ _ _ x → x
      ; done-g  = λ _ _ _ x → x
      ; map-g   = λ {f = f} _ y _ _ w → y _ _ (proj₁ w , (λ a → proj₁ (proj₂ w) (f a)) , proj₂ (proj₂ w))
      ; scan-g  = λ {f = f} {r = r} _ y _ _ w → y _ _ (proj₁ w , scan-wk τ f r (proj₂ w))
      ; take-g  = λ {i = b₀} {p = p} {c = c} {k = k} {s = s} _ y _ _ w hs →
                    Gw′.attached-grow gr c k s (proj₁ hs) , y _ _ (proj₁ w , take-wk τ b₀ p c (proj₂ w)) (proj₂ hs)
      ; flat-g  = λ {Δ} {X} {B} {op} {f} {fl} {oc} {k} {r} {pl} {so} {ls} {Y} {Y′} {L} {L′} _ y _ l →
                    flat-hg {Δ} {X} {B} {op} {f} {fl} {oc} {k} {r} {pl} {so} {ls} {Y} {Y′} {L} {L′} y l
      ; conn-g  = λ {Δ} {X} {B} {S} {c} {b} {kb} {k} {fd} {rp} {e} {rt} {src} {bd} {Y} {Y′} {Z} {Z′} _ y _ z →
                    conn-hg {Δ} {X} {B} {S} {c} {b} {kb} {k} {fd} {rp} {e} {rt} {src} {bd} {Y} {Y′} {Z} {Z′} y z
      ; join-g  = λ {sk = sk} {l = l} _ _ w hs → Gw′.slot-grow gr sk hs (joiner-wk τ l (proj₂ w))
      ; defer-g = λ {k = k} {s = s} _ y ι ι′ w hs → Gw′.stashed-grow gr k s (proj₁ hs) , y ι ι′ w (proj₂ hs)
      ; nil-g   = λ _ _ _ x → x
      ; cons-g  = λ {Δ} {B} {c} {k} {s} {Y} {Y′} {L} {L′} _ y l → cons-hg {Δ} {B} {c} {k} {s} {Y} {Y′} {L} {L′} y l }

    SettledG : GFrame
    SettledG = GField.gframe (Settling.SettledAlg {h}) (Settling.SettledAlg {v}) unitᵍ record
      { IR = λ _ _ → Lift _ ⊤ ; IRL = λ _ _ → Lift _ ⊤
      ; pend-g  = λ _ _ _ x → x
      ; cold-g  = λ _ _ _ x → x
      ; of-g    = λ _ _ _ x → x
      ; done-g  = λ _ _ _ x → x
      ; map-g   = λ _ y → y
      ; scan-g  = λ _ y → y
      ; take-g  = λ {k = k} {s = s} _ y ι ι′ w (b , st) → lift (Gw.begun-wk k s (lower b)) , y ι ι′ w st
      ; flat-g  = λ {k = k} {so = so} _ y _ l ι ι′ w (b , st , sl) → lift (Gw.begun-wk k so (lower b)) , y ι ι′ w st , l _ _ (lift tt) sl
      ; conn-g  = λ {kb = kb} {k = k} {src = src} {bd = bd} _ y _ z ι ι′ w (b₁ , b₂ , s₁ , s₂) →
                    lift (Gw.begun-wk k src (lower b₁)) , lift (Gw.begun-wk kb bd (lower b₂)) , y ι ι′ w s₁ , z _ _ (lift tt) s₂
      ; join-g  = λ _ _ _ x → x
      ; defer-g = λ {k = k} {s = s} _ y ι ι′ w (b , st) → lift (Gw.begun-wk k s (lower b)) , y ι ι′ w st
      ; nil-g   = λ _ _ _ x → x
      ; cons-g  = λ {k = k} {s = s} _ y l ι ι′ w (b , st , sl) → lift (Gw.begun-wk k s (lower b)) , y _ _ (lift tt) st , l ι ι′ w sl }

    -- KERNELS, grown once through the conjunction.
    KernelsG : GFrame
    KernelsG = HoldsG ⊛ (GatedG ⊛ SettledG)

    kernels-grow : ∀ {t : Sub h [] R} → Kernels H t → Kernels H′ (wkTree τ t)
    kernels-grow {t} kn = record
      { holds   = via (Holding.holds≡ H t []ᴬ rootObs) (Holding.holds≡ H′ (wkTree τ t) []ᴬ rootObs)
                      (proj₂ hc ([]ᴬ , rootObs) ([]ᴬ , rootObs) (refl , ((λ _ → ≗-refl _) , ≗-refl _ , ≗-refl _))) (Kernels.holds kn)
      ; gated   = via (Gating.gated≡ H t) (Gating.gated≡ H′ (wkTree τ t)) (proj₂ gc (lift tt) (lift tt) (lift tt)) (Kernels.gated kn)
      ; settled = Settling.settled-from {H = H′} (wkTree τ t) (proj₂ sc (lift tt) (lift tt) (lift tt) (Settling.settled-to {H = H} t (Kernels.settled kn))) }
      where
        hc = proj₁ (GFrame.grow KernelsG t)
        gc = proj₁ (proj₂ (GFrame.grow KernelsG t))
        sc = proj₂ (proj₂ (GFrame.grow KernelsG t))
