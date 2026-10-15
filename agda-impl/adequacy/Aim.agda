{-# OPTIONS --guardedness --large-indices #-}

-- A NODE'S PLACE IN THE CONFIGURATION.  A path through the witness tree,
-- every gate it passes open, reads off the open part as a context with
-- the node in its hole: the operators above it, and beside it every
-- sibling the configuration holds.
module adequacy.Aim where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.Any using (here)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Bool.Properties using (_≟_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (_×-dec_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong)

open import denotation.MonotonicList using (Pos)
open import denotation.Unfold using (Node; mapᶜ; scanᶜ; flatMapᶜ; connectᶜ; live; ended; shut; subscribe)
open import operation.AbstractObservable using (module Run)
open import operation.PureObservable using (Pureᴾ; module Pure)
open import adequacy.Carrier using (module Carrying)
open import adequacy.Plug using (Ctx; []; plug; mapF; scanF; takeF; outerF; laneF; bodyF; endedF; srcF; _∷ʳᶜ_; plug-∷ʳᶜ;
  shutC; shut-plug)

module Aiming (R : Set) where
  open Run (Pureᴾ R) using (module Kit; module FlatKit)
  open FlatKit using (Flat)
  open Pure R using (Val)
  open Carrying R using (module At; Sub; Lane; lane; Taking; taking; ending; taken
                        ; Path; PathLanes; here; in-map; in-scan; in-take; in-outer; in-lanes; in-source; in-body; in-defer
                        ; this-lane; next-lane)

  module Open {h} (H : All (Val h) h) where
    open At H using (val; part; partLanes; mapᴹ; merged; connected)

    -- A connect's source beside the body: running, or ended at `c`.
    SrcOpen : ∀ {Δ A} → Maybe Pos → Sub h Δ A → Set₁
    SrcOpen e s = (Σ (Node _ _) λ m → part s ≡ just m) ⊎ (part s ≡ nothing × Σ Pos λ c → e ≡ just c)

    -- EVERY GATE THE PATH PASSES OPEN: each takeWhile live and taking,
    -- the lane taken live, a source's body open, a body's source running
    -- or ended.
    mutual
      OpenPath : ∀ {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} → Path t u → Set₁
      OpenPath here                                = ⊤
      OpenPath (in-map π)                          = OpenPath π
      OpenPath (in-scan π)                         = OpenPath π
      OpenPath (in-take {c = c} {tk = tk} π)       = val (Kit.live c) ≡ true × tk ≡ taking × OpenPath π
      OpenPath (in-outer π)                        = OpenPath π
      OpenPath (in-lanes π)                        = OpenLanes π
      OpenPath (in-source {b = b} π)               = (Σ (Node _ _) λ m → part b ≡ just m) × OpenPath π
      OpenPath (in-body {e = e} {t = s} π)         = SrcOpen e s × OpenPath π
      OpenPath (in-defer π)                        = OpenPath π

      OpenLanes : ∀ {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} → PathLanes ls u → Set₁
      OpenLanes (this-lane {c = c} π) = val (Kit.live c) ≡ true × OpenPath π
      OpenLanes (next-lane π)         = OpenLanes π

    -- WHETHER THE PATH IS OPEN, gate by gate.
    private
      held? : ∀ {Δ A} (x : Maybe (Node Δ A)) → Dec (Σ (Node Δ A) λ m → x ≡ just m)
      held? (just m) = yes (m , refl)
      held? nothing  = no λ { (_ , ()) }

      ran? : ∀ {Δ A} e (x : Maybe (Node Δ A)) → Dec ((Σ (Node Δ A) λ m → x ≡ just m) ⊎ (x ≡ nothing × Σ Pos λ c → e ≡ just c))
      ran? e        (just m) = yes (inj₁ (m , refl))
      ran? (just c) nothing  = yes (inj₂ (refl , c , refl))
      ran? nothing  nothing  = no λ { (inj₁ (_ , ())) ; (inj₂ (_ , _ , ())) }

      taking? : (tk : Taking) → Dec (tk ≡ taking)
      taking? taking     = yes refl
      taking? (ending q) = no λ ()
      taking? taken      = no λ ()

    mutual
      open? : ∀ {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) → Dec (OpenPath π)
      open? here                                = yes tt
      open? (in-map π)                          = open? π
      open? (in-scan π)                         = open? π
      open? (in-take {c = c} {tk = tk} π)       = (val (Kit.live c) ≟ true) ×-dec (taking? tk ×-dec open? π)
      open? (in-outer π)                        = open? π
      open? (in-lanes π)                        = open-lanes? π
      open? (in-source {b = b} π)               = held? (part b) ×-dec open? π
      open? (in-body {e = e} {t = s} π)         = ran? e (part s) ×-dec open? π
      open? (in-defer π)                        = open? π

      open-lanes? : ∀ {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (π : PathLanes ls u) → Dec (OpenLanes π)
      open-lanes? (this-lane {c = c} π) = (val (Kit.live c) ≟ true) ×-dec open? π
      open-lanes? (next-lane π)         = open-lanes? π

    -- Untouched by any connect's end: a cold's node.
    Inert : ∀ {Δ A} → Node Δ A → Set₁
    Inert {Δ} n = ∀ {X} (i : X ∈ Δ) c → shut i c n ≡ n

    private
      merged-in : ∀ {Δ A B} op (g : A → Pos → Node Δ B) o bs (n : Node Δ B) as qs
                → merged op g o (bs ++ n ∷ as) qs ≡ just (flatMapᶜ op g o (bs ++ n ∷ as) qs)
      merged-in op g (just o) bs      n as qs = refl
      merged-in op g nothing  []      n as qs = refl
      merged-in op g nothing  (_ ∷ _) n as qs = refl

      connected-live : ∀ {Δ A B} e (m : Node Δ A) (b : Node (A ∷ Δ) B) → connected e (just m) (just b) ≡ just (connectᶜ b (live m))
      connected-live nothing  m b = refl
      connected-live (just c) m b = refl

    -- THE NODE IN ITS CONTEXT: the open part at the top is the context
    -- plugged with the node.
    mutual
      focus-path : ∀ {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) → OpenPath π
                 → ∀ {n} → Inert n → part u ≡ just n → Σ (Ctx Δ′ A′ Δ A) λ C → part t ≡ just (plug C n)
      focus-path here o in′ e = [] , e
      focus-path (in-map {f = f} π) o {n} in′ e with focus-path π o in′ e
      ... | C , pe = C ∷ʳᶜ mapF f , trans (cong (mapᴹ (mapᶜ f)) pe) (cong just (sym (plug-∷ʳᶜ C (mapF f) n)))
      focus-path (in-scan {f = f} {r} π) o {n} in′ e with focus-path π o in′ e
      ... | C , pe = C ∷ʳᶜ scanF f (val r) , trans (cong (mapᴹ (scanᶜ f (val r))) pe) (cong just (sym (plug-∷ʳᶜ C (scanF f (val r)) n)))
      focus-path (in-take {i = i} {p} {c} π) (lv , refl , o) {n} in′ e with focus-path π o in′ e
      ... | C , pe rewrite lv | pe = C ∷ʳᶜ takeF i p , cong just (sym (plug-∷ʳᶜ C (takeF i p) n))
      focus-path (in-outer {op = op} {f} {fl} {ls = ls} π) o {n} in′ e with focus-path π o in′ e
      ... | C , pe rewrite pe =
        C ∷ʳᶜ outerF op g (partLanes ls) q , cong just (sym (plug-∷ʳᶜ C (outerF op g (partLanes ls) q) n))
        where g = λ a q′ → subscribe (f a) q′
              q = val (Flat.queue fl)
      focus-path (in-lanes {op = op} {f} {fl} {t = so} π) o {n} in′ e with focus-lanes π o in′ e
      ... | bs , as , C , pl rewrite pl =
        C ∷ʳᶜ laneF op g (part so) bs as q
        , trans (merged-in op g (part so) bs (plug C n) as q) (cong just (sym (plug-∷ʳᶜ C (laneF op g (part so) bs as q) n)))
        where g = λ a q′ → subscribe (f a) q′
              q = val (Flat.queue fl)
      focus-path (in-source {e = e} {t = s} {b = b} π) ((m , pb) , o) {n} in′ e′ with focus-path π o in′ e′
      ... | C , pe rewrite pe | pb = C ∷ʳᶜ srcF m , trans (connected-live e (plug C n) m) (cong just (sym (plug-∷ʳᶜ C (srcF m) n)))
      focus-path (in-body {e = e} {t = s} {b = b} π) (inj₁ (m , ps) , o) {n} in′ e′ with focus-path π o in′ e′
      ... | C , pe rewrite pe | ps = C ∷ʳᶜ bodyF m , trans (connected-live e m (plug C n)) (cong just (sym (plug-∷ʳᶜ C (bodyF m) n)))
      focus-path (in-body {t = s} {b = b} π) (inj₂ (ps , c , refl) , o) {n} in′ e′ with focus-path π o in′ e′
      ... | C , pe rewrite pe | ps =
        shutC (here refl) c C ∷ʳᶜ endedF c
        , cong just (trans (cong (λ x → connectᶜ x (ended c)) (trans (shut-plug (here refl) c C n) (cong (plug (shutC (here refl) c C)) (in′ _ c))))
                           (sym (plug-∷ʳᶜ (shutC (here refl) c C) (endedF c) n)))
      focus-path (in-defer π) o in′ e = focus-path π o in′ e

      focus-lanes : ∀ {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (π : PathLanes ls u) → OpenLanes π
                  → ∀ {n} → Inert n → part u ≡ just n
                  → Σ (List (Node Δ B)) λ bs → Σ (List (Node Δ B)) λ as → Σ (Ctx Δ′ A′ Δ B) λ C → partLanes ls ≡ bs ++ plug C n ∷ as
      focus-lanes (this-lane {c = c} {ls = ls} π) (lv , o) in′ e with focus-path π o in′ e
      ... | C , pe rewrite lv | pe = [] , partLanes ls , C , refl
      focus-lanes (next-lane {l = lane c k s} π) o in′ e with focus-lanes π o in′ e
      ... | bs , as , C , pl with val (Kit.live c) | part s
      ...   | true  | just m  rewrite pl = m ∷ bs , as , C , refl
      ...   | true  | nothing rewrite pl = bs , as , C , refl
      ...   | false | _       rewrite pl = bs , as , C , refl
