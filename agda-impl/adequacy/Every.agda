{-# OPTIONS --guardedness #-}

-- PROBE: every part of the relation as one fold over `Sub`; its frames
-- proven once, for every part and for any conjunction of parts.
--
-- Two subscriptions are SIMILAR (`Sim`) when they agree node for node,
-- each node's own names alike across the two heaps, except at the pairs
-- a base relation pins.  Every frame is a way of building a `Sim`, once,
-- for every part: alike at a subscription's names; a write `Off` its
-- names along a path; a plant; a retag.  A part is a FRAME when it is
-- carried along any `Sim` given it is carried at the pins.  A weakening
-- has no pins, so a part GROWS by one clause per node, read across the
-- two worlds.  Frames of either kind conjoin.
module adequacy.Every where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Bool using (Bool; true)
open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapMaybe)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; [_,_]′) renaming (map₁ to sum-map₁; map₂ to sum-map₂)
open import Data.Unit using (⊤; tt)
open import Level using (Lift; lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; cong; cong₂)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_; tabulate to tabulateᴬ; lookup to lookupᴬ)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; _∷_)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴸ_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Any.Properties using (++⁺ˡ; ++⁺ʳ; ++⁻)

import Tree as T
open import Tree using (Obs)
open import denotation.MonotonicList.Events using (Timeline; Pos)
open import operation.AbstractObservable using (base; maybe; quiet; gate; list; sink; module Heap; module Run) renaming (module Machine to Shared)
open import operation.PureObservable using (Pureᴾ; Out)
import denotation.Unfold as U
open import adequacy.Strong using (module Strongly)
open import adequacy.Strong.Against using (module StrongAgainst)
open import adequacy.Strong.Held using (module StrongHeld)
open import adequacy.Moves using (module Moving)
open import adequacy.Torn using (module Tearing)
open import adequacy.Retag using (Retag; keep; module Retagging)
open import adequacy.Grow using (module Growing)
open import adequacy.Weaken using (module Weakening)
open import adequacy.Weaken.Heaps using (module WeakeningHeaps)
open import adequacy.Alike using (module Aliking)


module Everywhere (R : Set) where
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

  Up : Set → Set₁
  Up X = Lift _ X

  cut : ∀ {h} → Maybe (Quiet h) → Set₁ → Set₁
  cut nothing  X = Lift _ ⊤
  cut (just _) X = X

  cut-m : ∀ {h} (k : Maybe (Quiet h)) {X X′ : Set₁} → (X → X′) → cut k X → cut k X′
  cut-m nothing  f x = x
  cut-m (just _) f x = f x

  via : ∀ {A A′ B B′ : Set₁} → A ≡ A′ → B ≡ B′ → (A′ → B′) → A → B
  via refl refl f = f

  module Over {h : World} where
    Base : Set₂
    Base = ∀ {Δ A} → Sub h Δ A → Sub h Δ A → Set₁

    Carry : ∀ {I : Set₁} → (I → Set₁) → (I → Set₁) → Set₁
    Carry X X′ = ∀ i → X i → X′ i

    ------------------------------------------------------------------
    -- SIMILAR: node for node, own names alike, but at the pins

    mutual
      data Sim (H H′ : Heapᴹ h) (Ba : Base) : ∀ {Δ A} → Sub h Δ A → Sub h Δ A → Set₁ where
        pin    : ∀ {Δ A} {x y : Sub h Δ A} → Ba x y → Sim H H′ Ba x y
        ≈pend  : ∀ {Δ A} {s : Obs Timeline Δ A} {q} → Sim H H′ Ba (pendingˢ s q) (pendingˢ s q)
        ≈cold  : ∀ {Δ A} {s : Sink h A} {hd ph} → Alike H H′ (names (coldˢ {Δ = Δ} s hd ph)) → Sim H H′ Ba (coldˢ {Δ = Δ} s hd ph) (coldˢ s hd ph)
        ≈of    : ∀ {Δ} {A : Set} {p i} {xs : List A} → Sim H H′ Ba (ofˢ {Δ = Δ} p i xs) (ofˢ p i xs)
        ≈done  : ∀ {Δ A} → Sim H H′ Ba (doneˢ {Δ = Δ} {A}) doneˢ
        ≈map   : ∀ {Δ A} {B : Set} {f : A → B} {s s′ : Sub h Δ A} → Sim H H′ Ba s s′ → Sim H H′ Ba (mapˢ f s) (mapˢ f s′)
        ≈scan  : ∀ {Δ A B} {f : B → A → B} {r} {s s′ : Sub h Δ A} → Alike H H′ ((cell _ , r) ∷ [])
               → Sim H H′ Ba s s′ → Sim H H′ Ba (scanˢ f r s) (scanˢ f r s′)
        ≈take  : ∀ {Δ A i p c k tk} {s s′ : Sub h Δ A} → Alike H H′ (cutNames c ++ quietName k)
               → Sim H H′ Ba s s′ → Sim H H′ Ba (takeWhileˢ i p c k tk s) (takeWhileˢ i p c k tk s′)
        ≈flat  : ∀ {Δ A B op f fl oc k r pl} {so so′ : Sub h Δ A} {ls ls′ : List (Lane h Δ B)}
               → Alike H H′ (flatNames fl ++ cutNames oc ++ quietName k ++ (slot _ , r) ∷ [])
               → Sim H H′ Ba so so′ → SimL H H′ Ba ls ls′
               → Sim H H′ Ba (flatMapˢ op f fl oc k r pl so ls) (flatMapˢ op f fl oc k r pl so′ ls′)
        ≈conn  : ∀ {Δ A B S c b kb k fd rp e rt} {src src′ : Sub h Δ A} {bd bd′ : Sub h (A ∷ Δ) B}
               → Alike H H′ (subjectNames S ++ cutNames c ++ (cell _ , b) ∷ quietName kb ++ quietName k)
               → Sim H H′ Ba src src′ → Sim H H′ Ba bd bd′
               → Sim H H′ Ba (connectˢ S c b kb k fd rp e rt src bd) (connectˢ S c b kb k fd rp e rt src′ bd′)
        ≈join  : ∀ {Δ A j sk l} {x : A ∈ᴸ Δ} {st} → Alike H H′ (names (joinˢ j sk l x st)) → Sim H H′ Ba (joinˢ j sk l x st) (joinˢ j sk l x st)
        ≈defer : ∀ {Δ A k} {s s′ : Sub h Δ A} → Alike H H′ (quietName k) → Sim H H′ Ba s s′ → Sim H H′ Ba (deferˢ k s) (deferˢ k s′)

      data SimL (H H′ : Heapᴹ h) (Ba : Base) : ∀ {Δ B} → List (Lane h Δ B) → List (Lane h Δ B) → Set₁ where
        ≈nil  : ∀ {Δ B} → SimL H H′ Ba {Δ} {B} [] []
        ≈cons : ∀ {Δ B c k} {s s′ : Sub h Δ B} {ls ls′} → Alike H H′ (cutNames c ++ quietName k)
              → Sim H H′ Ba s s′ → SimL H H′ Ba ls ls′ → SimL H H′ Ba (lane c k s ∷ ls) (lane c k s′ ∷ ls′)

    -- A FRAME: carried along any similarity, given carried at its pins.
    record Frame : Set₂ where
      field
        C    : Heapᴹ h → Heapᴹ h → ∀ {Δ A} → Sub h Δ A → Sub h Δ A → Set₁
        CL   : Heapᴹ h → Heapᴹ h → ∀ {Δ B} → List (Lane h Δ B) → List (Lane h Δ B) → Set₁
        sim  : ∀ {H H′} {Ba : Base} → (∀ {Δ A} {x y : Sub h Δ A} → Ba x y → C H H′ x y)
             → ∀ {Δ A} {u u′ : Sub h Δ A} → Sim H H′ Ba u u′ → C H H′ u u′
        simL : ∀ {H H′} {Ba : Base} → (∀ {Δ A} {x y : Sub h Δ A} → Ba x y → C H H′ x y)
             → ∀ {Δ B} {ls ls′ : List (Lane h Δ B)} → SimL H H′ Ba ls ls′ → CL H H′ ls ls′

    -- The conjunction of two frames is a frame.
    _⊗_ : Frame → Frame → Frame
    F ⊗ G = record
      { C    = λ H H′ x y → Frame.C F H H′ x y × Frame.C G H H′ x y
      ; CL   = λ H H′ ls ls′ → Frame.CL F H H′ ls ls′ × Frame.CL G H H′ ls ls′
      ; sim  = λ b s → Frame.sim F (λ p → proj₁ (b p)) s , Frame.sim G (λ p → proj₂ (b p)) s
      ; simL = λ b ls → Frame.simL F (λ p → proj₁ (b p)) ls , Frame.simL G (λ p → proj₂ (b p)) ls }

    unit : Frame
    unit = record { C = λ _ _ _ _ → Lift _ ⊤ ; CL = λ _ _ _ _ → Lift _ ⊤ ; sim = λ _ _ → lift tt ; simL = λ _ _ → lift tt }

    ------------------------------------------------------------------
    -- The pins each frame asks for

    data Never : ∀ {Δ A} → Sub h Δ A → Sub h Δ A → Set₁ where

    data Pin {Δ′ A′} (u v : Sub h Δ′ A′) : ∀ {Δ A} → Sub h Δ A → Sub h Δ A → Set₁ where
      pinned : Pin u v u v

    data Retold : ∀ {Δ A} → Sub h Δ A → Sub h Δ A → Set₁ where
      retold : ∀ {Δ A j sk l} {x : A ∈ᴸ Δ} {st st′} → Retold (joinˢ j sk l x st) (joinˢ j sk l x st′)

    ------------------------------------------------------------------
    -- THE SIMILARITIES, once for every part

    module Alikes {H H′ : Heapᴹ h} where
      private
        both : ∀ xs {ys} → Alike H H′ xs → Alike H H′ ys → Alike H H′ (xs ++ ys)
        both xs ga gb j m = [ ga j , gb j ]′ (++⁻ xs m)

        wide : ∀ (xs : List (Name h)) {ys zs} → (∀ {n} → n ∈ᴸ ys → n ∈ᴸ zs) → ∀ {n} → n ∈ᴸ xs ++ ys → n ∈ᴸ xs ++ zs
        wide xs f m = [ ++⁺ˡ , (λ m′ → ++⁺ʳ xs (f m′)) ]′ (++⁻ xs m)

        one : ∀ {x} {ys : List (Name h)} {n} → n ∈ᴸ x ∷ [] → n ∈ᴸ x ∷ ys
        one (here e) = here e

        cons-w : ∀ {x} {ys zs : List (Name h)} → (∀ {n} → n ∈ᴸ ys → n ∈ᴸ zs) → ∀ {n} → n ∈ᴸ x ∷ ys → n ∈ᴸ x ∷ zs
        cons-w f (here e)  = here e
        cons-w f (there m) = there (f m)

        sub : ∀ {xs ys} → Alike H H′ ys → (∀ {n} → n ∈ᴸ xs → n ∈ᴸ ys) → Alike H H′ xs
        sub ag f j m = ag j (f m)

        keeps : ∀ {ns ys ms} → Off H H′ ns → (∀ {y} → y ∈ᴸ ns → y ∈ᴸ ys) → (∀ {x} → x ∈ᴸ ms → All (x ≢_) ys) → Alike H H′ ms
        keeps off f ap j m = off j (narrow f (ap m))

        -- A piece of a node's own names, apart from the names moved.
        piece : ∀ {ns} → Off H H′ ns → ∀ xs {ys} → AllPairs _≢_ (xs ++ ys) → (∀ {y} → y ∈ᴸ ns → y ∈ᴸ ys) → Alike H H′ xs
        piece off xs ps f = keeps off f (apart-r xs ps)

        -- A connect's own names, apart from the names moved below it.
        own : ∀ {A ys} (S : Subject A h) c (b : Ref h (maybe quiet)) kb k → AllPairs _≢_ (subjectNames S ++ cutNames c ++ (cell _ , b) ∷ quietName kb ++ quietName k ++ ys)
            → ∀ {ns} → Off H H′ ns → (∀ {n} → n ∈ᴸ ns → n ∈ᴸ ys) → Alike H H′ (subjectNames S ++ cutNames c ++ (cell _ , b) ∷ quietName kb ++ quietName k)
        own S c b kb k ps off f =
          both (subjectNames S) (piece off (subjectNames S) ps (λ m → ++⁺ʳ (cutNames c) (there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (f m))))))
            (both (cutNames c) (piece off (cutNames c) Q₀ (λ m → there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (f m)))))
              (both ((cell _ , b) ∷ []) (piece off ((cell _ , b) ∷ []) Q₁ (λ m → ++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (f m))))
                (both (quietName kb) (piece off (quietName kb) Q₂ (λ m → ++⁺ʳ (quietName k) (f m))) (piece off (quietName k) Q₃ f))))
          where
            Q₀ = pairs-r (subjectNames S) ps
            Q₁ = pairs-r (cutNames c) Q₀
            Q₂ = pairs-r ((cell _ , b) ∷ []) Q₁
            Q₃ = pairs-r (quietName kb) Q₂

      -- Alike at a subscription's names.
      mutual
        sim-alike : ∀ {Ba : Base} {Δ A} (u : Sub h Δ A) → Alike H H′ (names u) → Sim H H′ Ba u u
        sim-alike (pendingˢ s q)  ag = ≈pend
        sim-alike (coldˢ s hd ph) ag = ≈cold ag
        sim-alike (ofˢ p i xs)    ag = ≈of
        sim-alike doneˢ           ag = ≈done
        sim-alike (mapˢ f s)      ag = ≈map (sim-alike s ag)
        sim-alike (scanˢ f r s)   ag = ≈scan (sub ag one) (sim-alike s (sub ag there))
        sim-alike (takeWhileˢ i p c k tk s) ag =
          ≈take (sub ag (wide (cutNames c) ++⁺ˡ)) (sim-alike s (sub ag (λ m → ++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) m))))
        sim-alike (flatMapˢ op f fl oc k r pl so ls) ag =
          ≈flat (sub ag (wide (flatNames fl) (wide (cutNames oc) (wide (quietName k) one)))) (sim-alike so agS) (simL-alike ls agL)
          where
            agS = sub ag (λ m → ++⁺ʳ (flatNames fl) (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ˡ m)))))
            agL = sub ag (λ m → ++⁺ʳ (flatNames fl) (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ʳ (names so) m)))))
        sim-alike (connectˢ S c b kb k fd rp e rt src bd) ag =
          ≈conn (sub ag (wide (subjectNames S) (wide (cutNames c) (cons-w (wide (quietName kb) ++⁺ˡ))))) (sim-alike src agS) (sim-alike bd agB)
          where
            inner : ∀ {n} → n ∈ᴸ quietName kb ++ quietName k ++ names src ++ names bd → n ∈ᴸ names (connectˢ S c b kb k fd rp e rt src bd)
            inner m = ++⁺ʳ (subjectNames S) (++⁺ʳ (cutNames c) (there m))
            agS = sub ag (λ m → inner (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ˡ m))))
            agB = sub ag (λ m → inner (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ʳ (names src) m))))
        sim-alike (joinˢ j sk l x st) ag = ≈join ag
        sim-alike (deferˢ k s) ag = ≈defer (sub ag ++⁺ˡ) (sim-alike s (sub ag (++⁺ʳ (quietName k))))

        simL-alike : ∀ {Ba : Base} {Δ B} (ls : List (Lane h Δ B)) → Alike H H′ (laneNames ls) → SimL H H′ Ba ls ls
        simL-alike []                ag = ≈nil
        simL-alike (lane c k s ∷ ls) ag =
          ≈cons (sub ag (wide (cutNames c) ++⁺ˡ)) (sim-alike s (sub ag (λ m → ++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) (++⁺ˡ m)))))
                (simL-alike ls (sub ag (λ m → ++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) (++⁺ʳ (names s) m)))))

      -- A WRITE: the heap moved only at the planted node's names.
      mutual
        sim-path : ∀ {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (v : Sub h Δ′ A′) → AllPairs _≢_ (names (plant π v))
                 → Off H H′ (names v) → Sim H H′ (Pin u v) t (plant π v)
        sim-path here v ps off = pin pinned
        sim-path (in-map π) v ps off = ≈map (sim-path π v ps off)
        sim-path (in-scan {r = r} π) v ps off =
          ≈scan (piece off ((cell _ , r) ∷ []) ps (names-path (planted π v))) (sim-path π v (pairs-r ((cell _ , r) ∷ []) ps) off)
        sim-path (in-take {c = c} {k} π) v ps off =
          ≈take (both (cutNames c) (piece off (cutNames c) ps (λ m → ++⁺ʳ (quietName k) (np m))) (piece off (quietName k) P₁ np)) (sim-path π v P off)
          where
            np = names-path (planted π v)
            P₁ = pairs-r (cutNames c) ps
            P = pairs-r (quietName k) P₁
        sim-path (in-outer {fl = fl} {oc} {k} {r} {ls = ls} π) v ps off =
          ≈flat (both (flatNames fl) (piece off (flatNames fl) ps (λ m → ++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (nl m)))))
                  (both (cutNames oc) (piece off (cutNames oc) P₁ (λ m → ++⁺ʳ (quietName k) (there (nl m))))
                    (both (quietName k) (piece off (quietName k) P₂ (λ m → there (nl m))) (piece off ((slot _ , r) ∷ []) P₃ nl))))
                (sim-path π v Ps off) (simL-alike ls (keeps off np (apart-l (names (plant π v)) P₄)))
          where
            np = names-path (planted π v)
            nl : ∀ {n} → n ∈ᴸ names v → n ∈ᴸ names (plant π v) ++ laneNames ls
            nl m = ++⁺ˡ (np m)
            P₁ = pairs-r (flatNames fl) ps
            P₂ = pairs-r (cutNames oc) P₁
            P₃ = pairs-r (quietName k) P₂
            P₄ = pairs-r ((slot _ , r) ∷ []) P₃
            Ps = proj₁ (pairs-split (names (plant π v)) P₄)
        sim-path (in-lanes {fl = fl} {oc} {k} {r} {t = so} π) v ps off =
          ≈flat (both (flatNames fl) (piece off (flatNames fl) ps (λ m → ++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (nl m)))))
                  (both (cutNames oc) (piece off (cutNames oc) P₁ (λ m → ++⁺ʳ (quietName k) (there (nl m))))
                    (both (quietName k) (piece off (quietName k) P₂ (λ m → there (nl m))) (piece off ((slot _ , r) ∷ []) P₃ nl))))
                (sim-alike so (keeps off (lanes-path (plantedᴸ π v)) (apart-r (names so) P₄))) (simL-path π v (pairs-r (names so) P₄) off)
          where
            nl : ∀ {n} → n ∈ᴸ names v → n ∈ᴸ names so ++ laneNames (plantᴸ π v)
            nl m = ++⁺ʳ (names so) (lanes-path (plantedᴸ π v) m)
            P₁ = pairs-r (flatNames fl) ps
            P₂ = pairs-r (cutNames oc) P₁
            P₃ = pairs-r (quietName k) P₂
            P₄ = pairs-r ((slot _ , r) ∷ []) P₃
        sim-path (in-source {S = S} {c} {b} {kb} {k} {bd = bd} π) v ps off =
          ≈conn (own S c b kb k ps off (λ m → ++⁺ˡ (np m))) (sim-path π v Ps off) (sim-alike bd (keeps off np (apart-l (names (plant π v)) Q₄)))
          where
            np = names-path (planted π v)
            Q₄ = pairs-r (quietName k) (pairs-r (quietName kb) (pairs-r ((cell _ , b) ∷ []) (pairs-r (cutNames c) (pairs-r (subjectNames S) ps))))
            Ps = proj₁ (pairs-split (names (plant π v)) Q₄)
        sim-path (in-body {S = S} {c} {b} {kb} {k} {t = src} π) v ps off =
          ≈conn (own S c b kb k ps off (λ m → ++⁺ʳ (names src) (np m))) (sim-alike src (keeps off np (apart-r (names src) Q₄))) (sim-path π v (pairs-r (names src) Q₄) off)
          where
            np = names-path (planted π v)
            Q₄ = pairs-r (quietName k) (pairs-r (quietName kb) (pairs-r ((cell _ , b) ∷ []) (pairs-r (cutNames c) (pairs-r (subjectNames S) ps))))
        sim-path (in-defer {k = k} π) v ps off =
          ≈defer (piece off (quietName k) ps (names-path (planted π v))) (sim-path π v (pairs-r (quietName k) ps) off)

        simL-path : ∀ {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (π : PathLanes ls u) (v : Sub h Δ′ A′) → AllPairs _≢_ (laneNames (plantᴸ π v))
                  → Off H H′ (names v) → SimL H H′ (Pin u v) ls (plantᴸ π v)
        simL-path (this-lane {c = c} {k} {ls = ls} π) v ps off =
          ≈cons (both (cutNames c) (piece off (cutNames c) ps (λ m → ++⁺ʳ (quietName k) (nl m))) (piece off (quietName k) P₁ nl))
                (sim-path π v Ps off) (simL-alike ls (keeps off np (apart-l (names (plant π v)) P)))
          where
            np = names-path (planted π v)
            nl : ∀ {n} → n ∈ᴸ names v → n ∈ᴸ names (plant π v) ++ laneNames ls
            nl m = ++⁺ˡ (np m)
            P₁ = pairs-r (cutNames c) ps
            P = pairs-r (quietName k) P₁
            Ps = proj₁ (pairs-split (names (plant π v)) P)
        simL-path (next-lane {l = lane c k s} π) v ps off =
          ≈cons (both (cutNames c) (piece off (cutNames c) ps (λ m → ++⁺ʳ (quietName k) (nl m))) (piece off (quietName k) P₁ nl))
                (sim-alike s (keeps off (lanes-path (plantedᴸ π v)) (apart-r (names s) P))) (simL-path π v (pairs-r (names s) P) off)
          where
            nl : ∀ {n} → n ∈ᴸ names v → n ∈ᴸ names s ++ laneNames (plantᴸ π v)
            nl m = ++⁺ʳ (names s) (lanes-path (plantedᴸ π v) m)
            P₁ = pairs-r (cutNames c) ps
            P = pairs-r (quietName k) P₁

    module Moved {H : Heapᴹ h} where
      open Alikes {H} {H}

      private
        kept : ∀ {xs} → Alike H H xs
        kept _ _ = refl

      -- A PLANT: one heap, the node at a path replaced.
      mutual
        sim-plant : ∀ {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (v : Sub h Δ′ A′) → Sim H H (Pin u v) t (plant π v)
        sim-plant here v                        = pin pinned
        sim-plant (in-map π) v                  = ≈map (sim-plant π v)
        sim-plant (in-scan π) v                 = ≈scan kept (sim-plant π v)
        sim-plant (in-take π) v                 = ≈take kept (sim-plant π v)
        sim-plant (in-outer {ls = ls} π) v      = ≈flat kept (sim-plant π v) (simL-alike ls kept)
        sim-plant (in-lanes {t = so} π) v       = ≈flat kept (sim-alike so kept) (simL-plant π v)
        sim-plant (in-source {bd = bd} π) v     = ≈conn kept (sim-plant π v) (sim-alike bd kept)
        sim-plant (in-body {t = src} π) v       = ≈conn kept (sim-alike src kept) (sim-plant π v)
        sim-plant (in-defer π) v                = ≈defer kept (sim-plant π v)

        simL-plant : ∀ {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (π : PathLanes ls u) (v : Sub h Δ′ A′) → SimL H H (Pin u v) ls (plantᴸ π v)
        simL-plant (this-lane {ls = ls} π) v        = ≈cons kept (sim-plant π v) (simL-alike ls kept)
        simL-plant (next-lane {l = lane c k s} π) v = ≈cons kept (sim-alike s kept) (simL-plant π v)

      -- A RETAG: one heap, what each joiner holds rewritten.
      mutual
        sim-retag : ∀ {Δ A} (g : Retag Δ) (s : Sub h Δ A) → Sim H H Retold s (retag g s)
        sim-retag g (pendingˢ s q)                          = ≈pend
        sim-retag g (coldˢ s hd ph)                         = ≈cold kept
        sim-retag g (ofˢ p i xs)                            = ≈of
        sim-retag g doneˢ                                   = ≈done
        sim-retag g (mapˢ f s)                              = ≈map (sim-retag g s)
        sim-retag g (scanˢ f r s)                           = ≈scan kept (sim-retag g s)
        sim-retag g (takeWhileˢ i p c k tk s)               = ≈take kept (sim-retag g s)
        sim-retag g (flatMapˢ op f fl oc k r pl so ls)      = ≈flat kept (sim-retag g so) (simL-retag g ls)
        sim-retag g (connectˢ S c b kb k fd rp e rt src bd) = ≈conn kept (sim-retag g src) (sim-retag (keep g) bd)
        sim-retag g (joinˢ j sk l x st)                     = pin retold
        sim-retag g (deferˢ k s)                            = ≈defer kept (sim-retag g s)

        simL-retag : ∀ {Δ B} (g : Retag Δ) (ls : List (Lane h Δ B)) → SimL H H Retold ls (retagᴸ g ls)
        simL-retag g []                = ≈nil
        simL-retag g (lane c k s ∷ ls) = ≈cons kept (sim-retag g s) (simL-retag g ls)

    -- THE FRAMES, for any frame.
    module Frames (F : Frame) where
      open Frame F

      private
        at-never : ∀ {H H′ Δ A} {x y : Sub h Δ A} → Never x y → C H H′ x y
        at-never ()

        at-pin : ∀ {H H′ Δ′ A′} {u v : Sub h Δ′ A′} → C H H′ u v → ∀ {Δ A} {x y : Sub h Δ A} → Pin u v x y → C H H′ x y
        at-pin cv pinned = cv

        at-retold : ∀ {H} → (∀ {Δ A j sk l} {x : A ∈ᴸ Δ} {st st′} → C H H (joinˢ j sk l x st) (joinˢ j sk l x st′))
                  → ∀ {Δ A} {x y : Sub h Δ A} → Retold x y → C H H x y
        at-retold cj retold = cj

      frame-alike : ∀ {H H′ Δ A} (u : Sub h Δ A) → Alike H H′ (names u) → C H H′ u u
      frame-alike {H} {H′} u ag = sim {H} {H′} {Never} (at-never {H} {H′}) (Alikes.sim-alike u ag)

      frame-path : ∀ {H H′ Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (v : Sub h Δ′ A′) → AllPairs _≢_ (names (plant π v))
                 → Off H H′ (names v) → C H H′ u v → C H H′ t (plant π v)
      frame-path {H} {H′} π v ps off cv = sim {H} {H′} (at-pin {H} {H′} cv) (Alikes.sim-path π v ps off)

      frame-plant : ∀ {H Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (v : Sub h Δ′ A′) → C H H u v → C H H t (plant π v)
      frame-plant {H} π v cv = sim {H} {H} (at-pin {H} {H} cv) (Moved.sim-plant π v)

      frame-retag : ∀ {H} → (∀ {Δ A j sk l} {x : A ∈ᴸ Δ} {st st′} → C H H (joinˢ j sk l x st) (joinˢ j sk l x st′))
                  → ∀ {Δ A} (g : Retag Δ) (s : Sub h Δ A) → C H H s (retag g s)
      frame-retag {H} cj g s = sim {H} {H} (at-retold {H} cj) (Moved.sim-retag g s)

    ------------------------------------------------------------------
    -- A PART: one clause per node over its children's parts, each
    -- handed what its parent inherits it.

    record Alg : Set₂ where
      field
        Inh    : List Set → Set → Set₁
        InhL   : List Set → Set → Set₁
        pendᶜ  : ∀ {Δ A} → Obs Timeline Δ A → Pos → Inh Δ A → Set₁
        coldᶜ  : Heapᴹ h → ∀ {Δ A} → Sink h A → Handle h → Phase A → Inh Δ A → Set₁
        ofᶜ    : ∀ {Δ} {A : Set} → Pos → ℕ → List A → Inh Δ A → Set₁
        doneᶜ  : ∀ {Δ A} → Inh Δ A → Set₁
        mapᶜ   : Heapᴹ h → ∀ {Δ A} {B : Set} → (A → B) → Sub h Δ A → (Inh Δ A → Set₁) → Inh Δ B → Set₁
        scanᶜ  : Heapᴹ h → ∀ {Δ A B} → (B → A → B) → Ref h (base B) → Sub h Δ A → (Inh Δ A → Set₁) → Inh Δ B → Set₁
        takeᶜ  : Heapᴹ h → ∀ {Δ A} → Bool → (A → Bool) → Cut h → Maybe (Quiet h) → Taking Δ A → Sub h Δ A → (Inh Δ A → Set₁) → Inh Δ A → Set₁
        flatᶜ  : Heapᴹ h → ∀ {Δ A B} → T.FlatOp → (A → Obs Timeline Δ B) → Flat A h → Cut h → Maybe (Quiet h) → Sink h ⊤
               → U.Node Δ B → Sub h Δ A → List (Lane h Δ B) → (Inh Δ A → Set₁) → (InhL Δ B → Set₁) → Inh Δ B → Set₁
        connᶜ  : Heapᴹ h → ∀ {Δ A B} → Subject A h → Cut h → Ref h (maybe quiet) → Maybe (Quiet h) → Maybe (Quiet h) → Feed A h
               → Pos → Maybe Pos → U.Node Δ A → Sub h Δ A → Sub h (A ∷ Δ) B → (Inh Δ A → Set₁) → (Inh (A ∷ Δ) B → Set₁) → Inh Δ B → Set₁
        joinᶜ  : Heapᴹ h → ∀ {Δ A} → Pos → Sink h A → Ref h gate → A ∈ᴸ Δ → Maybe (List (Pos × Maybe A) × Maybe Pos) → Inh Δ A → Set₁
        deferᶜ : Heapᴹ h → ∀ {Δ A} → Maybe (Quiet h) → Sub h Δ A → (Inh Δ A → Set₁) → Inh Δ A → Set₁
        nilᶜ   : ∀ {Δ B} → InhL Δ B → Set₁
        consᶜ  : Heapᴹ h → ∀ {Δ B} → Cut h → Maybe (Quiet h) → Sub h Δ B → (Inh Δ B → Set₁) → (InhL Δ B → Set₁) → InhL Δ B → Set₁

    module Fold (a : Alg) where
      open Alg a
      mutual
        fold : Heapᴹ h → ∀ {Δ A} → Sub h Δ A → Inh Δ A → Set₁
        fold H (pendingˢ s q)                          = pendᶜ s q
        fold H (coldˢ s hd ph)                         = coldᶜ H s hd ph
        fold H (ofˢ p i xs)                            = ofᶜ p i xs
        fold H doneˢ                                   = doneᶜ
        fold H (mapˢ f s)                              = mapᶜ H f s (fold H s)
        fold H (scanˢ f r s)                           = scanᶜ H f r s (fold H s)
        fold H (takeWhileˢ i p c k tk s)               = takeᶜ H i p c k tk s (fold H s)
        fold H (flatMapˢ op f fl oc k r pl so ls)      = flatᶜ H op f fl oc k r pl so ls (fold H so) (foldL H ls)
        fold H (connectˢ S c b kb k fd rp e rt src bd) = connᶜ H S c b kb k fd rp e rt src bd (fold H src) (fold H bd)
        fold H (joinˢ j sk l x st)                     = joinᶜ H j sk l x st
        fold H (deferˢ k s)                            = deferᶜ H k s (fold H s)

        foldL : Heapᴹ h → ∀ {Δ B} → List (Lane h Δ B) → InhL Δ B → Set₁
        foldL H []                = nilᶜ
        foldL H (lane c k s ∷ ls) = consᶜ H c k s (fold H s) (foldL H ls)

    -- Each clause carried across two heaps alike at the node's own
    -- names, given each child's part and lower part carried.
    record Mono (a : Alg) (lo : Frame) : Set₂ where
      open Alg a
      open Frame lo using (C; CL)
      field
        cold-m  : ∀ {H H′ Δ A} {s : Sink h A} {hd ph} → Alike H H′ (names (coldˢ {Δ = Δ} s hd ph)) → Carry (coldᶜ H {Δ} s hd ph) (coldᶜ H′ s hd ph)
        map-m   : ∀ {H H′ Δ A} {B : Set} {f : A → B} {s s′ : Sub h Δ A} {X X′} → C H H′ s s′ → Carry X X′ → Carry (mapᶜ H f s X) (mapᶜ H′ f s′ X′)
        scan-m  : ∀ {H H′ Δ A B} {f : B → A → B} {r} {s s′ : Sub h Δ A} {X X′} → Alike H H′ ((cell _ , r) ∷ [])
                → C H H′ s s′ → Carry X X′ → Carry (scanᶜ H f r s X) (scanᶜ H′ f r s′ X′)
        take-m  : ∀ {H H′ Δ A i p c k tk} {s s′ : Sub h Δ A} {X X′} → Alike H H′ (cutNames c ++ quietName k)
                → C H H′ s s′ → Carry X X′ → Carry (takeᶜ H i p c k tk s X) (takeᶜ H′ i p c k tk s′ X′)
        flat-m  : ∀ {H H′ Δ A B op f fl oc k r pl} {so so′ : Sub h Δ A} {ls ls′ : List (Lane h Δ B)} {X X′ L L′}
                → Alike H H′ (flatNames fl ++ cutNames oc ++ quietName k ++ (slot _ , r) ∷ [])
                → C H H′ so so′ → Carry X X′ → CL H H′ ls ls′ → Carry L L′
                → Carry (flatᶜ H op f fl oc k r pl so ls X L) (flatᶜ H′ op f fl oc k r pl so′ ls′ X′ L′)
        conn-m  : ∀ {H H′ Δ A B S c b kb k fd rp e rt} {src src′ : Sub h Δ A} {bd bd′ : Sub h (A ∷ Δ) B} {X X′ Y Y′}
                → Alike H H′ (subjectNames S ++ cutNames c ++ (cell _ , b) ∷ quietName kb ++ quietName k)
                → C H H′ src src′ → Carry X X′ → C H H′ bd bd′ → Carry Y Y′
                → Carry (connᶜ H S c b kb k fd rp e rt src bd X Y) (connᶜ H′ S c b kb k fd rp e rt src′ bd′ X′ Y′)
        join-m  : ∀ {H H′ Δ A j sk l} {x : A ∈ᴸ Δ} {st} → Alike H H′ (names (joinˢ j sk l x st)) → Carry (joinᶜ H j sk l x st) (joinᶜ H′ j sk l x st)
        defer-m : ∀ {H H′ Δ A k} {s s′ : Sub h Δ A} {X X′} → Alike H H′ (quietName k)
                → C H H′ s s′ → Carry X X′ → Carry (deferᶜ H k s X) (deferᶜ H′ k s′ X′)
        cons-m  : ∀ {H H′ Δ B c k} {s s′ : Sub h Δ B} {X X′ L L′} → Alike H H′ (cutNames c ++ quietName k)
                → C H H′ s s′ → Carry X X′ → Carry L L′ → Carry (consᶜ H c k s X L) (consᶜ H′ c k s′ X′ L′)

    -- A PART IS A FRAME, over its lower frame.
    module Field (a : Alg) (lo : Frame) (mo : Mono a lo) where
      open Alg a
      open Fold a
      open Mono mo
      private module L = Frame lo

      C : Heapᴹ h → Heapᴹ h → ∀ {Δ A} → Sub h Δ A → Sub h Δ A → Set₁
      C H H′ x y = L.C H H′ x y × Carry (fold H x) (fold H′ y)

      CL : Heapᴹ h → Heapᴹ h → ∀ {Δ B} → List (Lane h Δ B) → List (Lane h Δ B) → Set₁
      CL H H′ ls ls′ = L.CL H H′ ls ls′ × Carry (foldL H ls) (foldL H′ ls′)

      module Carrying {H H′ : Heapᴹ h} {Ba : Base} (b : ∀ {Δ A} {x y : Sub h Δ A} → Ba x y → C H H′ x y) where
        lb : ∀ {Δ A} {x y : Sub h Δ A} → Ba x y → L.C H H′ x y
        lb p = proj₁ (b p)

        mutual
          carry : ∀ {Δ A} {u u′ : Sub h Δ A} → Sim H H′ Ba u u′ → Carry (fold H u) (fold H′ u′)
          carry (pin p)          = proj₂ (b p)
          carry ≈pend            = λ i x → x
          carry (≈cold ag)       = cold-m ag
          carry ≈of              = λ i x → x
          carry ≈done            = λ i x → x
          carry (≈map s)         = map-m (L.sim lb s) (carry s)
          carry (≈scan ag s)     = scan-m ag (L.sim lb s) (carry s)
          carry (≈take ag s)     = take-m ag (L.sim lb s) (carry s)
          carry (≈flat ag s ls)  = flat-m ag (L.sim lb s) (carry s) (L.simL lb ls) (carryL ls)
          carry (≈conn ag s bd)  = conn-m ag (L.sim lb s) (carry s) (L.sim lb bd) (carry bd)
          carry (≈join ag)       = join-m ag
          carry (≈defer ag s)    = defer-m ag (L.sim lb s) (carry s)

          carryL : ∀ {Δ B} {ls ls′ : List (Lane h Δ B)} → SimL H H′ Ba ls ls′ → Carry (foldL H ls) (foldL H′ ls′)
          carryL ≈nil            = λ i x → x
          carryL (≈cons ag s ls) = cons-m ag (L.sim lb s) (carry s) (carryL ls)

      frame : Frame
      frame = record
        { C = C ; CL = CL
        ; sim  = λ b s → L.sim (Carrying.lb b) s , Carrying.carry b s
        ; simL = λ b ls → L.simL (Carrying.lb b) ls , Carrying.carryL b ls }

  ----------------------------------------------------------------------
  -- SPENT

  module Spending {h : World} where
    open Over {h}

    SpentAlg : Alg
    SpentAlg = record
      { Inh = λ _ _ → Lift _ ⊤ ; InhL = λ _ _ → Lift _ ⊤
      ; pendᶜ = λ _ _ _ → Lift _ ⊤ ; coldᶜ = λ H s hd ph _ → Lift _ (At.spentʰ H hd ≡ true) ; ofᶜ = λ _ _ _ _ → Lift _ ⊤ ; doneᶜ = λ _ → Lift _ ⊤
      ; mapᶜ = λ _ _ _ X → X ; scanᶜ = λ _ _ _ _ X → X ; takeᶜ = λ _ _ _ _ k _ _ X i → cut k (X i)
      ; flatᶜ = λ _ _ _ _ _ k _ _ _ _ X L i → cut k (X i) × L (lift tt)
      ; connᶜ = λ _ _ _ _ kb k _ _ _ _ _ _ X Y i → cut k (X i) × cut kb (Y (lift tt))
      ; joinᶜ = λ _ _ _ _ _ _ _ → Lift _ ⊤ ; deferᶜ = λ _ k _ X i → cut k (X i)
      ; nilᶜ = λ _ → Lift _ ⊤ ; consᶜ = λ _ _ k _ X L i → cut k (X (lift tt)) × L i }

    open Fold SpentAlg renaming (fold to Spent′; foldL to SpentL′) public

    SpentMono : Mono SpentAlg unit
    SpentMono = record
      { cold-m  = λ {hd = hd} ag i sp → lift (trans (cong lower (ag hd (there (here refl)))) (lower sp))
      ; map-m   = λ _ x → x
      ; scan-m  = λ _ _ x → x
      ; take-m  = λ {k = k} _ _ x i → cut-m k (x i)
      ; flat-m  = λ {k = k} _ _ x _ l i (c₁ , c₂) → cut-m k (x i) c₁ , l (lift tt) c₂
      ; conn-m  = λ {kb = kb} {k = k} _ _ x _ y i (c₁ , c₂) → cut-m k (x i) c₁ , cut-m kb (y (lift tt)) c₂
      ; join-m  = λ _ i x → x
      ; defer-m = λ {k = k} _ _ x i → cut-m k (x i)
      ; cons-m  = λ {k = k} _ _ x l i (c₁ , c₂) → cut-m k (x (lift tt)) c₁ , l i c₂ }

    SpentF : Frame
    SpentF = Field.frame SpentAlg unit SpentMono

    -- Today's `Spent`, exactly.
    mutual
      spent≡ : (H : Heapᴹ h) → ∀ {Δ A} (u : Sub h Δ A) → At.Spent H u ≡ Spent′ H u (lift tt)
      spent≡ H (pendingˢ s q)                          = refl
      spent≡ H (coldˢ s hd ph)                         = refl
      spent≡ H (ofˢ p i xs)                            = refl
      spent≡ H doneˢ                                   = refl
      spent≡ H (mapˢ f s)                              = spent≡ H s
      spent≡ H (scanˢ f r s)                           = spent≡ H s
      spent≡ H (takeWhileˢ i p c k tk s)               = cut≡ H k s
      spent≡ H (flatMapˢ op f fl oc k r pl so ls)      = cong₂ _×_ (cut≡ H k so) (spentL≡ H ls)
      spent≡ H (connectˢ S c b kb k fd rp e rt src bd) = cong₂ _×_ (cut≡ H k src) (cut≡ H kb bd)
      spent≡ H (joinˢ j sk l x st)                     = refl
      spent≡ H (deferˢ k s)                            = cut≡ H k s

      spentL≡ : (H : Heapᴹ h) → ∀ {Δ B} (ls : List (Lane h Δ B)) → At.SpentLanes H ls ≡ SpentL′ H ls (lift tt)
      spentL≡ H []                = refl
      spentL≡ H (lane c k s ∷ ls) = cong₂ _×_ (cut≡ H k s) (spentL≡ H ls)

      cut≡ : (H : Heapᴹ h) (k : Maybe (Quiet h)) → ∀ {Δ A} (s : Sub h Δ A) → At.Cut↓ H k s ≡ cut k (Spent′ H s (lift tt))
      cut≡ H nothing  s = refl
      cut≡ H (just _) s = spent≡ H s

    private module SFr = Frames SpentF

    -- Today's four frames, as instances.
    spent-alike : ∀ {H H′ : Heapᴹ h} {Δ A} (u : Sub h Δ A) → Alike H H′ (names u) → At.Spent H u → At.Spent H′ u
    spent-alike {H} {H′} u ag = via (spent≡ H u) (spent≡ H′ u) (proj₂ (SFr.frame-alike u ag) (lift tt))

    spent-retag : ∀ (H : Heapᴹ h) {Δ A} (g : Retag Δ) (s : Sub h Δ A) → At.Spent H s → At.Spent H (retag g s)
    spent-retag H g s = via (spent≡ H s) (spent≡ H (retag g s)) (proj₂ (SFr.frame-retag {H} (lift tt , λ _ x → x) g s) (lift tt))
