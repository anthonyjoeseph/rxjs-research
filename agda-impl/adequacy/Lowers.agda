{-# OPTIONS --guardedness #-}

-- LOWERS: a teardown only spends handles, lowers switches and silences
-- joiners, and writes no slot and no subject's subscribers.  So what the
-- queue reads off the heap — handles spent, subscribers, a silenced
-- joiner's switch and slot — holds after it if it held before.
module adequacy.Lowers where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Data.List.Relation.Unary.All using (All) renaming (map to mapᴬ)
open import Data.List.Relation.Unary.Linked using (Linked)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴸ_)

open import denotation.MonotonicList using (Timeline)
open import operation.AbstractObservable using (module Heap; module Run; base; list; joins) renaming (module Machine to Shared)
open import operation.PureObservable using (Pureᴾ; Out)
open import adequacy.Strong using (module Strongly)
open import adequacy.Torn using (module Tearing)

module Lowering (R : Set) where
  open Heap using (Kind; cell; slot; play; _∋_; same) renaming (here to hereʰ; there to thereʰ)
  open Shared Timeline (Out R) using (Heapᴹ; store; look; stored)
  open Strongly R
  open Tearing R using (torn; tornVia; thrown; thrownLanes; look-store; get-put-same; Site; takeSite; bodySite; siteHeap)
  open Run (Pureᴾ R) using (module Kit; module FlatKit; module Subject)

  ----------------------------------------------------------------------
  -- Kinds apart

  three : (x y z : Bool) → x ≡ y ⊎ (y ≡ z ⊎ x ≡ z)
  three false false _     = inj₁ refl
  three true  true  _     = inj₁ refl
  three false true  false = inj₂ (inj₂ refl)
  three false true  true  = inj₂ (inj₁ refl)
  three true  false false = inj₂ (inj₁ refl)
  three true  false true  = inj₂ (inj₂ refl)

  ℕ≢Bool : ℕ ≢ Bool
  ℕ≢Bool e with subst (λ X → (x y z : X) → x ≡ y ⊎ (y ≡ z ⊎ x ≡ z)) (sym e) three 0 1 2
  ... | inj₁ ()
  ... | inj₂ (inj₁ ())
  ... | inj₂ (inj₂ ())

  baseOf : Kind → Set
  baseOf (cell (base X)) = X
  baseOf _               = ⊤

  ----------------------------------------------------------------------
  -- One heap lowered to another

  record Lowers {h} (H H′ : Heapᴹ h) : Set₁ where
    field
      spends : (hd : h ∋ play) → lower (look H hd) ≡ true → lower (look H′ hd) ≡ true
      lowers : (l : h ∋ cell (base Bool)) → lower (look H l) ≡ false → lower (look H′ l) ≡ false
      slots  : ∀ {A} (s : h ∋ slot A) → look H′ s ≡ look H s
      subs   : ∀ {A} (r : h ∋ cell (joins A)) → look H′ r ≡ look H r

  open Lowers

  lowers-refl : ∀ {h} (H : Heapᴹ h) → Lowers H H
  lowers-refl H = record { spends = λ _ e → e ; lowers = λ _ e → e ; slots = λ _ → refl ; subs = λ _ → refl }

  lowers-trans : ∀ {h} {H H₁ H₂ : Heapᴹ h} → Lowers H H₁ → Lowers H₁ H₂ → Lowers H H₂
  lowers-trans a b = record
    { spends = λ hd e → spends b hd (spends a hd e) ; lowers = λ l e → lowers b l (lowers a l e)
    ; slots = λ s → trans (slots b s) (slots a s) ; subs = λ r → trans (subs b r) (subs a r) }

  -- Two names of one kind: the same, or apart.
  decide : ∀ {w k} (i j : w ∋ k) → i ≡ j ⊎ i ≢ j
  decide hereʰ      hereʰ      = inj₁ refl
  decide hereʰ      (thereʰ j) = inj₂ λ ()
  decide (thereʰ i) hereʰ      = inj₂ λ ()
  decide (thereʰ i) (thereʰ j) with decide i j
  ... | inj₁ refl = inj₁ refl
  ... | inj₂ ne   = inj₂ λ { refl → ne refl }

  apart : ∀ {w k} {i j : w ∋ k} → i ≢ j → _≢_ {A = Name w} (k , i) (k , j)
  apart ne refl = ne refl

  -- A store at a kind the queue never reads.
  store-apart : ∀ {h k} (H : Heapᴹ h) (i : h ∋ k) x → k ≢ play → k ≢ cell (base Bool)
              → (∀ {A} → k ≢ slot A) → (∀ {A} → k ≢ cell (joins A)) → Lowers H (store H i x)
  store-apart H i x np nb ns nj = record
    { spends = λ hd e → trans (cong lower (look-store H i hd (λ q → np (cong proj₁ q)))) e
    ; lowers = λ l e → trans (cong lower (look-store H i l (λ q → nb (cong proj₁ q)))) e
    ; slots  = λ s → look-store H i s (λ q → ns (cong proj₁ q))
    ; subs   = λ r → look-store H i r (λ q → nj (cong proj₁ q)) }

  spend-lowers : ∀ {h} (H : Heapᴹ h) (hd : h ∋ play) → Lowers H (store H hd (lift true))
  spend-lowers H hd = record
    { spends = sp
    ; lowers = λ l e → trans (cong lower (look-store H hd l λ ())) e
    ; slots  = λ s → look-store H hd s λ ()
    ; subs   = λ r → look-store H hd r λ () }
    where
      sp : (hd′ : _ ∋ play) → lower (look H hd′) ≡ true → lower (look (store H hd (lift true)) hd′) ≡ true
      sp hd′ e with decide hd hd′
      ... | inj₁ refl rewrite get-put-same H hd {y = stored (lift true) same} = refl
      ... | inj₂ ne   = trans (cong lower (look-store H hd hd′ (apart ne))) e

  drop-lowers : ∀ {h} (H : Heapᴹ h) (l : h ∋ cell (base Bool)) → Lowers H (store H l (lift false))
  drop-lowers H l = record
    { spends = λ hd e → trans (cong lower (look-store H l hd λ ())) e
    ; lowers = lw
    ; slots  = λ s → look-store H l s λ ()
    ; subs   = λ r → look-store H l r λ () }
    where
      lw : (l′ : _ ∋ cell (base Bool)) → lower (look H l′) ≡ false → lower (look (store H l (lift false)) l′) ≡ false
      lw l′ e with decide l l′
      ... | inj₁ refl rewrite get-put-same H l {y = stored (lift false) same} = refl
      ... | inj₂ ne   = trans (cong lower (look-store H l l′ (apart ne))) e

  ----------------------------------------------------------------------
  -- An unsubscribe lowers

  mutual
    torn-lowers : ∀ {h} (H : Heapᴹ h) {Δ A} (s : Sub h Δ A) → Lowers H (torn H s)
    torn-lowers H (pendingˢ s q)                          = lowers-refl H
    torn-lowers H (coldˢ s hd ph)                         = spend-lowers H hd
    torn-lowers H (ofˢ p i xs)                            = lowers-refl H
    torn-lowers H doneˢ                                   = lowers-refl H
    torn-lowers H (mapˢ f s)                              = torn-lowers H s
    torn-lowers H (scanˢ f r s)                           = torn-lowers H s
    torn-lowers H (takeWhileˢ i p c k tk s)               = thrown-lowers H c k s
    torn-lowers H (flatMapˢ op f fl oc k r pl so ls)      =
      let H′ = thrown H oc k so
          H₁ = store H′ (FlatKit.Flat.lanes fl) (lift [])
          H₂ = store H₁ (FlatKit.Flat.active fl) (lift 0) in
      lowers-trans (thrown-lowers H oc k so)
        (lowers-trans (store-apart H′ (FlatKit.Flat.lanes fl) (lift []) (λ ()) (λ ()) (λ ()) (λ ()))
          (lowers-trans (store-apart H₁ (FlatKit.Flat.active fl) (lift 0) (λ ()) (λ e → ℕ≢Bool (cong baseOf e)) (λ ()) (λ ()))
            (lanes-lowers H₂ (length (lower (look H′ (FlatKit.Flat.lanes fl)))) ls)))
    torn-lowers H (connectˢ S c b kb k fd rp e rt src bd) = lowers-trans (torn-lowers H src) (via-lowers (torn H src) kb bd)
    torn-lowers H (joinˢ j sk l x st)                     = drop-lowers H l
    torn-lowers H (deferˢ k s)                            = via-lowers H k s

    via-lowers : ∀ {h} (H : Heapᴹ h) k {Δ A} (s : Sub h Δ A) → Lowers H (tornVia H k s)
    via-lowers H nothing  s = lowers-refl H
    via-lowers H (just _) s = torn-lowers H s

    thrown-lowers : ∀ {h} (H : Heapᴹ h) (c : Kit.Cut h) k {Δ A} (s : Sub h Δ A) → Lowers H (thrown H c k s)
    thrown-lowers H c k s = lowers-trans (drop-lowers H (Kit.live c)) (via-lowers _ k s)

    lanes-lowers : ∀ {h} (H : Heapᴹ h) n {Δ B} (ls : List (Lane h Δ B)) → Lowers H (thrownLanes H n ls)
    lanes-lowers H zero    ls                = lowers-refl H
    lanes-lowers H (suc n) []                = lowers-refl H
    lanes-lowers H (suc n) (lane c k s ∷ ls) = lowers-trans (thrown-lowers H c k s) (lanes-lowers _ n ls)

  site-lowers : ∀ {h} (H : Heapᴹ h) {t : Sub h [] R} (z : Site t) → Lowers H (siteHeap H z)
  site-lowers H (takeSite {c = c} {k} {s} π)         = thrown-lowers H c k s
  site-lowers H (bodySite {c = c} {k = k} {s = s} π) = thrown-lowers H c k s

  ----------------------------------------------------------------------
  -- The queue, lowered

  unspent : ∀ {b b′} → (b ≡ true → b′ ≡ true) → b′ ≡ false → b ≡ false
  unspent {false} f e = refl
  unspent {true}  f e = trans (sym (f refl)) e

  queue-lowers : ∀ {h} {H H′ : Heapᴹ h} → Lowers H H′ → ∀ {p clk ts} {t : Sub h [] R} → Queue H p clk ts t → Queue H′ p clk ts t
  queue-lowers {H = H} {H′} lw q = record
    { timed   = mapᴬ (λ { (inj₁ e) → inj₁ (spends lw _ e) ; (inj₂ m) → inj₂ m }) (proj₁ (Queue.timed q))
              , mapᴬ (λ f e → f (unspent (spends lw _) e)) (proj₂ (Queue.timed q))
    ; joined  = mapᴬ (λ { {A , S} (al , lk) → subst (λ xs → All _ xs × Linked _ xs) (sym (cong lower (subs lw (Subject.subscribers S))))
                                                     (mapᴬ (λ { (inj₁ m) → inj₁ m ; (inj₂ (l , o , e , sl)) → inj₂ (l , o , lowers lw l e , subst (λ z → CbRel z (Canon.joinerCb l o)) (sym (slots lw _)) sl) }) al , lk) })
                     (proj₁ (Queue.joined q))
              , mapᴬ (λ { {joiner S sk j} m → subst ((sk , j) ∈ᴸ_) (sym (cong lower (subs lw (Subject.subscribers S)))) m }) (proj₂ (Queue.joined q))
    ; ordered = Queue.ordered q
    ; ahead   = Queue.ahead q }
