{-# OPTIONS --guardedness #-}

-- LOWERS: a teardown only spends handles, lowers switches and silences
-- joiners, and writes no slot and no subject's subscribers.  So what the
-- queue reads off the heap — handles spent, subscribers, a silenced
-- joiner's switch and slot — holds after it if it held before.
module adequacy.Lowers where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Data.List.Relation.Unary.All using (All) renaming (map to mapᴬ; tail to tailᴬ)
open import Data.List.Relation.Unary.Any using () renaming (here to hereᴬ; there to thereᴬ)
open import Data.Empty using (⊥-elim)
open import Data.List.Relation.Unary.Linked using (Linked)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴸ_)

open import denotation.MonotonicList using (Timeline; Pos)
open import operation.AbstractObservable using (module Heap; module Run; base; list; joins; fifo) renaming (module Machine to Shared)
open import operation.PureObservable using (Pureᴾ; Out)
open import adequacy.Strong using (module Strongly)
open import adequacy.Torn using (module Tearing)
import denotation.Unfold as U

module Lowering (R : Set) where
  open Heap using (Kind; cell; slot; play; _∋_; same) renaming (here to hereʰ; there to thereʰ)
  open Shared Timeline (Out R) using (Heapᴹ; store; look; stored)
  open Strongly R
  open Tearing R using (torn; tornVia; thrown; thrownLanes; look-store; get-put-same; Site; takeSite; bodySite; siteHeap; siteCall)
  open Run (Pureᴾ R) using (Act; module Kit; module FlatKit; module Subject)
  open Heap using (_⊑_)

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
      queues : ∀ {A} (q : h ∋ cell (fifo A)) → look H′ q ≡ look H q

  open Lowers

  lowers-refl : ∀ {h} (H : Heapᴹ h) → Lowers H H
  lowers-refl H = record { spends = λ _ e → e ; lowers = λ _ e → e ; slots = λ _ → refl ; subs = λ _ → refl ; queues = λ _ → refl }

  lowers-trans : ∀ {h} {H H₁ H₂ : Heapᴹ h} → Lowers H H₁ → Lowers H₁ H₂ → Lowers H H₂
  lowers-trans a b = record
    { spends = λ hd e → spends b hd (spends a hd e) ; lowers = λ l e → lowers b l (lowers a l e)
    ; slots = λ s → trans (slots b s) (slots a s) ; subs = λ r → trans (subs b r) (subs a r) ; queues = λ q → trans (queues b q) (queues a q) }

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
              → (∀ {A} → k ≢ slot A) → (∀ {A} → k ≢ cell (joins A)) → (∀ {A} → k ≢ cell (fifo A)) → Lowers H (store H i x)
  store-apart H i x np nb ns nj nq = record
    { spends = λ hd e → trans (cong lower (look-store H i hd (λ q → np (cong proj₁ q)))) e
    ; lowers = λ l e → trans (cong lower (look-store H i l (λ q → nb (cong proj₁ q)))) e
    ; slots  = λ s → look-store H i s (λ q → ns (cong proj₁ q))
    ; subs   = λ r → look-store H i r (λ q → nj (cong proj₁ q))
    ; queues = λ r → look-store H i r (λ q → nq (cong proj₁ q)) }

  spend-lowers : ∀ {h} (H : Heapᴹ h) (hd : h ∋ play) → Lowers H (store H hd (lift true))
  spend-lowers H hd = record
    { spends = sp
    ; lowers = λ l e → trans (cong lower (look-store H hd l λ ())) e
    ; slots  = λ s → look-store H hd s λ ()
    ; subs   = λ r → look-store H hd r λ ()
    ; queues = λ r → look-store H hd r λ () }
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
    ; subs   = λ r → look-store H l r λ ()
    ; queues = λ r → look-store H l r λ () }
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
        (lowers-trans (store-apart H′ (FlatKit.Flat.lanes fl) (lift []) (λ ()) (λ ()) (λ ()) (λ ()) (λ ()))
          (lowers-trans (store-apart H₁ (FlatKit.Flat.active fl) (lift 0) (λ ()) (λ e → ℕ≢Bool (cong baseOf e)) (λ ()) (λ ()) (λ ()))
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

  ----------------------------------------------------------------------
  -- What is owed, a cut run

  false≢true : false ≢ true
  false≢true ()

  dropped : ∀ {h} (H : Heapᴹ h) (l : h ∋ cell (base Bool)) → lower (look (store H l (lift false)) l) ≡ false
  dropped H l rewrite get-put-same H l {y = stored (lift false) same} = refl

  -- A cut's own switch, thrown.
  site-dead : ∀ {h} (H : Heapᴹ h) {t : Sub h [] R} {Δ A i q c k} {s : Sub h Δ A} (π : Path t (takeWhileˢ i q c k taken s))
            → lower (look (siteHeap H (takeSite π)) (Kit.live c)) ≡ false
  site-dead H {c = c} {k} {s} π = lowers (via-lowers _ k s) (Kit.live c) (dropped H (Kit.live c))

  raised : ∀ {h} {H H′ : Heapᴹ h} → Lowers H H′ → (l : h ∋ cell (base Bool)) → lower (look H′ l) ≡ true → lower (look H l) ≡ true
  raised {H = H} lw l e with lower (look H l) in eq
  ... | true  = refl
  ... | false = ⊥-elim (false≢true (trans (sym (lowers lw l eq)) e))

  -- The calls a cut is.
  cutLike : ∀ {h} {t : Sub h [] R} → Call t → Bool
  cutLike (take2C _) = true
  cutLike (bodyC _)  = true
  cutLike _          = false

  cut-like : ∀ {h} {t : Sub h [] R} (z : Site t) → cutLike (siteCall z) ≡ true
  cut-like (takeSite _) = refl
  cut-like (bodySite _) = refl

  past : ∀ {h} {t : Sub h [] R} (z : Site t) {p q : Pos} {c} {js : List (Job t)} → cutLike c ≡ false
       → (q , c) ∈ᴸ (p , siteCall z) ∷ js → (q , c) ∈ᴸ js
  past z f (hereᴬ eq) = ⊥-elim (false≢true (trans (sym f) (trans (cong (λ j → cutLike (proj₂ j)) eq) (cut-like z))))
  past z f (thereᴬ m) = m

  -- The cut run owed no longer: its switch is thrown.
  cut-gone : ∀ {h} (H : Heapᴹ h) {t : Sub h [] R} (z : Site t) {p : Pos} {js Δ A i q c k} {s : Sub h Δ A}
             (π : Path t (takeWhileˢ i q c k taken s)) {r}
           → lower (look (siteHeap H z) (Kit.live c)) ≡ true → (r , take2C π) ∈ᴸ (p , siteCall z) ∷ js → (r , take2C π) ∈ᴸ js
  cut-gone H (takeSite π₀) π l (hereᴬ refl) = ⊥-elim (false≢true (trans (sym (site-dead H π₀)) l))
  cut-gone H (bodySite π₀) π l (hereᴬ ())
  cut-gone H z             π l (thereᴬ m)   = m

  sources-past : ∀ {h} {t : Sub h [] R} (z : Site t) {p : Pos} {js} → Against.sources t ((p , siteCall z) ∷ js) ≡ Against.sources t js
  sources-past (takeSite _) = refl
  sources-past (bodySite _) = refl

  -- A joiner reads only its switch, and only once raised: what a lowered
  -- heap owes it was owed before.
  mutual
    fed-lowers : ∀ {h} {H H′ : Heapᴹ h} → Lowers H H′ → ∀ {Δ A} (s : Sub h Δ A) {ν} → At.Fed H s ν → At.Fed H′ s ν
    fed-lowers lw (pendingˢ s q)  f = f
    fed-lowers lw (coldˢ s hd ph) f = f
    fed-lowers lw (ofˢ p i xs)    f = f
    fed-lowers lw doneˢ           f = f
    fed-lowers lw (mapˢ g s)      f = fed-lowers lw s f
    fed-lowers lw (scanˢ g r s)   f = fed-lowers lw s f
    fed-lowers lw (takeWhileˢ i p c k tk s) f = fed-lowers lw s f
    fed-lowers lw (flatMapˢ op g fl oc k r pl so ls) (f₁ , f₂) = fed-lowers lw so f₁ , fedL-lowers lw ls f₂
    fed-lowers lw (connectˢ S c b kb k fd rp e rt src bd) (f₁ , f₂) = fed-lowers lw src f₁ , fed-lowers lw bd f₂
    fed-lowers lw (joinˢ j sk l x st) f = lift (λ r → lower f (raised lw l r))
    fed-lowers lw (deferˢ k s) f = fed-lowers lw s f

    fedL-lowers : ∀ {h} {H H′ : Heapᴹ h} → Lowers H H′ → ∀ {Δ B} (ls : List (Lane h Δ B)) {ν} → At.FedLanes H ls ν → At.FedLanes H′ ls ν
    fedL-lowers lw []                f          = f
    fedL-lowers lw (lane c k s ∷ ls) (f₁ , f₂) = fed-lowers lw s f₁ , fedL-lowers lw ls f₂

  -- A part gone stays gone once a heap is lowered: every `if` `part`
  -- reads goes to `nothing` or stays, and the one cell it reads past a
  -- switch, a flatMap's queue, is of a kind nothing lowering writes.
  gone-if : ∀ {X : Set₁} {b b′ : Bool} {x x′ : Maybe X} → (b′ ≡ true → b ≡ true) → (x ≡ nothing → x′ ≡ nothing)
          → (if b then x else nothing) ≡ nothing → (if b′ then x′ else nothing) ≡ nothing
  gone-if {b = b}     {false} r g e = refl
  gone-if {b = true}  {true}  r g e = g e
  gone-if {b = false} {true}  r g e = ⊥-elim (false≢true (r refl))

  gone-spent : ∀ {X : Set₁} {b b′ : Bool} {x : X} → (b ≡ true → b′ ≡ true)
             → (if b then nothing else just x) ≡ nothing → (if b′ then nothing else just x) ≡ nothing
  gone-spent {b = true}  r e rewrite r refl = refl
  gone-spent {b = false} r ()

  module _ {h} {H H′ : Heapᴹ h} (lw : Lowers H H′) where
    gone-map : ∀ {X Y : Set₁} {f f′ : X → Y} (m : Maybe X) {m′ : Maybe X} → (m ≡ nothing → m′ ≡ nothing)
             → At.mapᴹ H f m ≡ nothing → At.mapᴹ H′ f′ m′ ≡ nothing
    gone-map nothing  g e rewrite g refl = refl
    gone-map (just _) g ()

    gone-taking : ∀ {Δ A} i p (tk : Taking Δ A) (m : Maybe (U.Node Δ A)) {m′} → (m ≡ nothing → m′ ≡ nothing)
                → At.taking? H i p tk m ≡ nothing → At.taking? H′ i p tk m′ ≡ nothing
    gone-taking i p taking m g e = gone-map m g e
    gone-taking i p taken  m g e = refl
    gone-taking i p (ending _ _) m g ()

    gone-merged : ∀ {Δ A B} op (g : A → Pos → U.Node Δ B) (o : Maybe (U.Node Δ A)) ls qs pl
                → At.merged H op g o ls qs pl ≡ nothing → o ≡ nothing × ls ≡ [] × qs ≡ []
    gone-merged op g nothing  []      []      pl e  = refl , refl , refl
    gone-merged op g nothing  []      (_ ∷ _) pl ()
    gone-merged op g nothing  (_ ∷ _) qs      pl ()
    gone-merged op g (just _) ls      qs      pl ()

    gone-connected : ∀ {Δ A B} r e t (s : Maybe (U.Node Δ A)) (b : Maybe (U.Node (A ∷ Δ) B))
                   → At.connected H r e t s b ≡ nothing → b ≡ nothing ⊎ (s ≡ nothing × e ≡ nothing)
    gone-connected r e       t s       nothing  g = inj₁ refl
    gone-connected r nothing t nothing (just b) g = inj₂ (refl , refl)
    gone-connected r (just _) t nothing (just b) ()
    gone-connected r e       t (just _) (just b) ()

    connected-none : ∀ {Δ A B} r t (b : Maybe (U.Node (A ∷ Δ) B)) → At.connected H′ r nothing t nothing b ≡ nothing
    connected-none r t nothing  = refl
    connected-none r t (just b) = refl

    gone-cons : ∀ {X : Set₁} (x : Maybe X) xs → At.consᴹ H x xs ≡ [] → x ≡ nothing × xs ≡ []
    gone-cons nothing  xs e = refl , e
    gone-cons (just _) xs ()

    gone-lane : ∀ {Δ B} {b b′ : Bool} (x : Maybe (U.Node Δ B)) {x′} xs {xs′} → (b′ ≡ true → b ≡ true) → (x ≡ nothing → x′ ≡ nothing) → (xs ≡ [] → xs′ ≡ [])
              → (if b then At.consᴹ H x xs else xs) ≡ [] → (if b′ then At.consᴹ H′ x′ xs′ else xs′) ≡ []
    gone-lane {b = false} {false} x xs r g gs e = gs e
    gone-lane {b = true}  {false} x xs r g gs e = gs (proj₂ (gone-cons x xs e))
    gone-lane {b = false} {true}  x xs r g gs e = ⊥-elim (false≢true (r refl))
    gone-lane {b = true}  {true}  x xs r g gs e with gone-cons x xs e
    ... | nx , nxs rewrite g nx | gs nxs = refl

    mutual
      part-gone : ∀ {Δ A} (s : Sub h Δ A) → At.part H s ≡ nothing → At.part H′ s ≡ nothing
      part-gone (pendingˢ s q)                          ()
      part-gone (coldˢ s hd ph)                         e = gone-spent (spends lw hd) e
      part-gone (ofˢ p i xs)                            ()
      part-gone doneˢ                                   e = refl
      part-gone (mapˢ f s)                              e = gone-map (At.part H s) (part-gone s) e
      part-gone (scanˢ f r s)                           e = gone-map (At.part H s) (part-gone s) e
      part-gone (takeWhileˢ i p c k tk s)               e =
        gone-if (raised lw (Kit.live c)) (gone-taking i p tk (At.part H s) (part-gone s)) e
      part-gone (flatMapˢ op f fl oc k r pl so ls)      e
        with gone-merged op (λ a q → U.subscribe (f a) q) (At.part H so) (At.partLanes H ls) (At.val H (FlatKit.Flat.queue fl)) pl e
      ... | no , nl , nq rewrite part-gone so no | lanes-gone ls nl | cong lower (queues lw (FlatKit.Flat.queue fl)) | nq = refl
      part-gone (connectˢ S c b kb k fd rp e rt src bd) g with gone-connected rp e rt (At.part H src) (At.part H bd) g
      ... | inj₁ nb         rewrite part-gone bd nb = refl
      ... | inj₂ (ns , refl) rewrite part-gone src ns = connected-none rp rt (At.part H′ bd)
      part-gone (joinˢ j sk l x st)                     e = gone-if (raised lw l) (λ n → n) e
      part-gone (deferˢ k s)                            e = part-gone s e

      lanes-gone : ∀ {Δ B} (ls : List (Lane h Δ B)) → At.partLanes H ls ≡ [] → At.partLanes H′ ls ≡ []
      lanes-gone []                e = refl
      lanes-gone (lane c k s ∷ ls) e =
        gone-lane (At.part H s) (At.partLanes H ls) (raised lw (Kit.live c)) (part-gone s) (lanes-gone ls) e

  -- A body that held no part holds none once a cut has run.
  parted-torn : ∀ {h} (H : Heapᴹ h) {t : Sub h [] R} (z : Site t) {Δ A B S c b kb k fd e rp rt} {s : Sub h Δ A} {bd : Sub h (A ∷ Δ) B}
              → Path t (connectˢ S c b kb k fd rp e rt s bd) → At.part H bd ≡ nothing → At.part (siteHeap H z) bd ≡ nothing
  parted-torn H z {bd = bd} _ = part-gone (site-lowers H z) bd

  -- A teardown only throws switches, spends colds and silences joiners:
  -- what is owed of a live switch or an unspent cold was owed before,
  -- the cut itself is owed no longer.
  torn-owned : ∀ {h} (H : Heapᴹ h) {t : Sub h [] R} (z : Site t)
               {p w bs} {act act′ : Act h ⊤} {σ : w ⊑ h} {K ks} {e : act ≗ ⟦ siteCall z ∷ ks ⟧} {e′ : act′ ≗ ⟦ ks ⟧}
               {Kᴬ : Against.StackAs t p σ K bs} → Owned H t (Against.runAs (siteCall z ∷ ks) e Kᴬ) → Owned (siteHeap H z) t (Against.runAs ks e′ Kᴬ)
  torn-owned H {t} z ow = record
    { ofs    = λ π → past z refl (Owned.ofs ow π)
    ; plays  = λ {hd = hd} π nsp → Owned.plays ow π (unspent (spends lw hd) nsp)
    ; fires  = λ {hd = hd} π nsp → Owned.fires ow π (unspent (spends lw hd) nsp)
    ; begun  = λ π → subst (λ xs → _ ∈ᴸ xs) (sources-past z) (Owned.begun ow π)
    ; ends   = λ {c = c} π l → past z refl (Owned.ends ow π (raised lw (Kit.live c) l))
    ; cuts   = λ {c = c} π l → proj₁ (Owned.cuts ow π (raised lw (Kit.live c) l)) , cut-gone H z π l (proj₂ (Owned.cuts ow π (raised lw (Kit.live c) l)))
    ; feeds  = λ π → past z refl (Owned.feeds ow π)
    ; fins   = λ π → past z refl (Owned.fins ow π)
    ; bodies = λ π m → parted-torn H z π (Owned.bodies ow π (thereᴬ m))
    ; placed = tailᴬ (Owned.placed ow) }
    where lw = site-lowers H z
