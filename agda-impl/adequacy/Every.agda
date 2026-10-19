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
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; suc)
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
open import Data.List.Relation.Unary.Any.Properties using (++⁺ˡ; ++⁺ʳ; ++⁻)

import Tree as T
open import Tree using (Obs)
open import denotation.MonotonicList using (Timeline; Pos)
open import operation.AbstractObservable using (base; maybe; quiet; gate; list; sink; module Heap; module Run) renaming (module Machine to Shared)
open import operation.PureObservable using (Pureᴾ; Out)
import denotation.Unfold as U
open import adequacy.Strong using (module Strongly)
open import adequacy.Moves using (module Moving)
open import adequacy.Torn using (module Tearing)
open import adequacy.Retag using (Retag; keep; module Retagging)
open import adequacy.Grow using (module Growing)
open import adequacy.Weaken using (module Weakening)
open import adequacy.Alike using (module Aliking)

module Everywhere (R : Set) where
  open Heap using (World; Sink; Handle; Quiet; cell; slot; _⊑_; wk∋)
  open Run (Pureᴾ R) using (Ref; Subject; Env; Observer; _>>ᴬ_; wkR; wkEl; wkEnv; wkObs; wkSubject; module Kit; module FlatKit)
  open Kit using (Cut)
  open FlatKit using (Flat)
  open Shared Timeline (Out R) using (Heapᴹ; look)
  open Strongly R hiding (Alg; SettledAlg; module Fold)
  open Moving R using (pairs-split; pairs-r; plant; plantᴸ; planted; plantedᴸ)
  open Tearing R using (Off; Alike; attached-alike; stashed-alike; names-path; lanes-path; narrow; apart-r; apart-l)
  open Retagging R using (retag; retagᴸ)
  open Growing R using (wkTree; wkLanes; wkFeed)
  open Weakening R using (Grows; module Grown)
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

      cells : ∀ {t} (x : Ref h t) → At.val H′ (wkR τ x) ≡ wkEl t τ (At.val H x)
      cells = Grows.cells gr

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
                    (λ e → sum-map₁ (λ m → subst (Kit.wkCut τ c ∈ᴸ_) (sym (lower w)) (Gw.listed-wk gr (lower ι) m))
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
        , Gw.slot-grow gr r rs (refill-wk τ op f fl e oR)
        , Gw.attached-grow gr oc k so a
        , y _ _ (e , outer-wk τ op f fl oc e oR) hs
        , trans (cells (FlatKit.Flat.active fl)) (trans ac (sym (Gw.count-grow gr ls)))
        , ( wkEl (list Kit.cutTy) τ gone
          , trans (cong (_++ wkEl (list Kit.cutTy) τ gone) (cells (FlatKit.Flat.lanes fl)))
              (trans (sym (Gw.wkEl-++ gr {Kit.cutTy} (At.val H (FlatKit.Flat.lanes fl)) gone)) (trans (cong (wkEl (list Kit.cutTy) τ) sw) (sym (Gw.switches-grow gr ls))))
          , Gw.dead-grow gr gone dead )
        , l _ _ (lanesR e oR) hl

      conn-hg : ∀ {Δ X B S c b kb k fd rp e rt} {src : Sub h Δ X} {bd : Sub h (X ∷ Δ) B} {Y Y′ Z Z′}
              → RCarry HIR Y Y′ → RCarry HIR Z Z′
              → RCarry HIR (Over.Alg.connᶜ (Holding.HoldsAlg {h}) H S c b kb k fd rp e rt src bd Y Z)
                           (Over.Alg.connᶜ (Holding.HoldsAlg {v}) H′ (wkSubject τ S) (Kit.wkCut τ c) (wkR τ b) (mapMaybe (wk∋ τ) kb) (mapMaybe (wk∋ τ) k) (wkFeed τ fd) rp e rt
                                           (wkTree τ src) (wkTree τ bd) Y′ Z′)
      conn-hg {S = S} {c} {b} {kb} {k} {src = src} {bd} y z (E , o) (E′ , o′) (e , oR) (a , eb , st , hs , hb) =
          Gw.attached-grow gr c k src a
        , trans (cells b) (trans (cong (wkEl (maybe quiet) τ) eb) (Gw.quiet-wk gr kb))
        , Gw.stashed-grow gr kb bd st
        , y _ _ (e , feeder-wk τ S) hs
        , z _ _ (cong (wkSubject τ S ∷ᴬ_) e , body-wk τ c oR) hb

      cons-hg : ∀ {Δ B c k} {s : Sub h Δ B} {Y Y′ L L′} → RCarry HIR Y Y′ → RCarry LanesR L L′
              → RCarry LanesR (Over.Alg.consᶜ (Holding.HoldsAlg {h}) H c k s Y L)
                              (Over.Alg.consᶜ (Holding.HoldsAlg {v}) H′ (Kit.wkCut τ c) (mapMaybe (wk∋ τ) k) (wkTree τ s) Y′ L′)
      cons-hg {c = c} {k} {s} y l _ _ (lanesR {op = op} {f} {fl = fl} e oR) (a , hs , hl) =
        Gw.attached-grow gr c k s a , y _ _ (e , laneO-wk τ op f fl c e oR) hs , l _ _ (lanesR e oR) hl

    HoldsG : GFrame
    HoldsG = GField.gframe (Holding.HoldsAlg {h}) (Holding.HoldsAlg {v}) unitᵍ record
      { IR = HIR ; IRL = LanesR
      ; pend-g  = λ _ _ _ x → x
      ; cold-g  = λ {s = s} _ _ w hs → Gw.slot-grow gr s hs (proj₂ w)
      ; of-g    = λ _ _ _ x → x
      ; done-g  = λ _ _ _ x → x
      ; map-g   = λ {f = f} _ y _ _ w → y _ _ (proj₁ w , (λ a → proj₁ (proj₂ w) (f a)) , proj₂ (proj₂ w))
      ; scan-g  = λ {f = f} {r = r} _ y _ _ w → y _ _ (proj₁ w , scan-wk τ f r (proj₂ w))
      ; take-g  = λ {i = b₀} {p = p} {c = c} {k = k} {s = s} _ y _ _ w hs →
                    Gw.attached-grow gr c k s (proj₁ hs) , y _ _ (proj₁ w , take-wk τ b₀ p c (proj₂ w)) (proj₂ hs)
      ; flat-g  = λ {Δ} {X} {B} {op} {f} {fl} {oc} {k} {r} {pl} {so} {ls} {Y} {Y′} {L} {L′} _ y _ l →
                    flat-hg {Δ} {X} {B} {op} {f} {fl} {oc} {k} {r} {pl} {so} {ls} {Y} {Y′} {L} {L′} y l
      ; conn-g  = λ {Δ} {X} {B} {S} {c} {b} {kb} {k} {fd} {rp} {e} {rt} {src} {bd} {Y} {Y′} {Z} {Z′} _ y _ z →
                    conn-hg {Δ} {X} {B} {S} {c} {b} {kb} {k} {fd} {rp} {e} {rt} {src} {bd} {Y} {Y′} {Z} {Z′} y z
      ; join-g  = λ {sk = sk} {l = l} _ _ w hs → Gw.slot-grow gr sk hs (joiner-wk τ l (proj₂ w))
      ; defer-g = λ {k = k} {s = s} _ y ι ι′ w hs → Gw.stashed-grow gr k s (proj₁ hs) , y ι ι′ w (proj₂ hs)
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
