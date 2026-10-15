{-# OPTIONS --guardedness --large-indices #-}

-- A NODE'S PLACE IN THE CONFIGURATION.  A path through the witness tree,
-- every gate it passes open, reads off the open part as a context with
-- the node in its hole: the operators above it, and beside it every
-- sibling the configuration holds.
module adequacy.Aim where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Bool.Properties using (_≟_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (_×-dec_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; cong₂; subst)
open import Level using (Lift; lift)
open import Data.Maybe.Properties using (just-injective)

open import denotation.MonotonicList using (Pos)
open import denotation.Unfold using (Node; mapᶜ; scanᶜ; flatMapᶜ; connectᶜ; live; ended; shut; subscribe)
open import operation.AbstractObservable using (module Run)
open import operation.PureObservable using (Pureᴾ; module Pure)
open import adequacy.Carrier using (module Carrying)
open import adequacy.Plug using (Ctx; []; plug; mapF; scanF; takeF; outerF; laneF; bodyF; endedF; srcF; _∷ʳᶜ_; plug-∷ʳᶜ
                                ; Clear; clear-∷ʳᶜ; Beyond; Beyondᴺ; OuterB; Opt; Waits; WaitsM; WaitsL)

module Aiming (R : Set) where
  open Run (Pureᴾ R) using (module Kit; module FlatKit)
  open FlatKit using (Flat)
  open Pure R using (Val)
  open Carrying R using (module At; Sub; Lane; lane; Taking; taking; ending; taken
                        ; pendingˢ; coldˢ; ofˢ; doneˢ; mapˢ; scanˢ; takeWhileˢ; flatMapˢ; connectˢ; joinˢ; deferˢ
                        ; Path; PathLanes; here; in-map; in-scan; in-take; in-outer; in-lanes; in-source; in-body; in-defer
                        ; this-lane; next-lane)

  module Open {h} (H : All (Val h) h) where
    open At H using (val; part; partLanes; mapᴹ; consᴹ; merged; connected) renaming (taking? to partTaking)

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

    -- Past a connect's end, its body's every joiner already told so: the
    -- end's `shut` moves nothing.
    Told : ∀ {Δ A B} → Maybe Pos → Sub h Δ A → Sub h (A ∷ Δ) B → Set₁
    Told e s b = ∀ {c} → part s ≡ nothing → e ≡ just c → mapᴹ (shut (here refl) c) (part b) ≡ part b

    -- BELOW EVERY CONNECT WHOSE SOURCE HAS ENDED, its body told so.
    mutual
      Stable : ∀ {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} → Path t u → Set₁
      Stable here                                    = ⊤
      Stable (in-map π)                              = Stable π
      Stable (in-scan π)                             = Stable π
      Stable (in-take π)                             = Stable π
      Stable (in-outer π)                            = Stable π
      Stable (in-lanes π)                            = StableLanes π
      Stable (in-source π)                           = Stable π
      Stable (in-body {e = e} {t = s} {b = b} π)     = Told e s b × Stable π
      Stable (in-defer π)                            = Stable π

      StableLanes : ∀ {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} → PathLanes ls u → Set₁
      StableLanes (this-lane π) = Stable π
      StableLanes (next-lane π) = StableLanes π

    -- EVERY SUB BESIDE THE PATH, its open part as `P` says: a flatMap's
    -- other lanes and its outer, a connect's body beside its source and
    -- its running source beside its body.
    mutual
      Beside : ∀ {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} → (∀ {Γ B} → Node Γ B → Set) → Path t u → Set₁
      Beside P here                       = ⊤
      Beside P (in-map π)                 = Beside P π
      Beside P (in-scan π)                = Beside P π
      Beside P (in-take π)                = Beside P π
      Beside P (in-outer {ls = ls} π)     = All P (partLanes ls) × Beside P π
      Beside P (in-lanes {t = so} π)      = Opt P (part so) × BesideLanes P π
      Beside P (in-source {b = b} π)      = Opt P (part b) × Beside P π
      Beside P (in-body {t = s} π)        = Opt P (part s) × Beside P π
      Beside P (in-defer π)               = Beside P π

      BesideLanes : ∀ {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} → (∀ {Γ B} → Node Γ B → Set) → PathLanes ls u → Set₁
      BesideLanes P (this-lane {ls = ls} π) = All P (partLanes ls) × Beside P π
      BesideLanes P (next-lane {l = l} π)   = All P (partLanes (l ∷ [])) × BesideLanes P π

    private
      opt-map : ∀ {Γ B} {P Q : Node Γ B → Set} → (∀ n → P n → Q n) → ∀ x → Opt P x → Opt Q x
      opt-map f nothing  _ = tt
      opt-map f (just n) p = f n p

      all-map : ∀ {Γ B} {P Q : Node Γ B → Set} → (∀ n → P n → Q n) → ∀ xs → All P xs → All Q xs
      all-map f []       []       = []
      all-map f (x ∷ xs) (p ∷ ps) = f x p ∷ all-map f xs ps

    -- What holds of every sub beside the path, so does what follows.
    mutual
      beside-map : ∀ {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (P Q : ∀ {Γ B} → Node Γ B → Set)
                 → (∀ {Γ B} (n : Node Γ B) → P n → Q n) → (π : Path t u) → Beside P π → Beside Q π
      beside-map P Q f here                     b        = tt
      beside-map P Q f (in-map π)               b        = beside-map P Q f π b
      beside-map P Q f (in-scan π)              b        = beside-map P Q f π b
      beside-map P Q f (in-take π)              b        = beside-map P Q f π b
      beside-map P Q f (in-outer {ls = ls} π)   (al , b) = all-map f (partLanes ls) al , beside-map P Q f π b
      beside-map P Q f (in-lanes {t = so} π)    (ob , b) = opt-map f (part so) ob , lanes-map P Q f π b
      beside-map P Q f (in-source {b = b′} π)   (ob , b) = opt-map f (part b′) ob , beside-map P Q f π b
      beside-map P Q f (in-body {t = s} π)      (ob , b) = opt-map f (part s) ob , beside-map P Q f π b
      beside-map P Q f (in-defer π)             b        = beside-map P Q f π b

      lanes-map : ∀ {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (P Q : ∀ {Γ B} → Node Γ B → Set)
                → (∀ {Γ B} (n : Node Γ B) → P n → Q n) → (π : PathLanes ls u) → BesideLanes P π → BesideLanes Q π
      lanes-map P Q f (this-lane {ls = ls} π) (al , b) = all-map f (partLanes ls) al , beside-map P Q f π b
      lanes-map P Q f (next-lane {l = l} π)   (al , b) = all-map f (partLanes (l ∷ [])) al , lanes-map P Q f π b

    -- A SUB AT REST BEYOND `r`: what it holds open, read through the
    -- heap's flags as `part` reads them, waits beyond `r`, each leaf on
    -- its own; past a connect's end, its body already told so.
    mutual
      Rests : ∀ {Δ A} → Pos → Sub h Δ A → Set₁
      Rests r (mapˢ f s)                          = Rests r s
      Rests r (scanˢ f z s)                       = Rests r s
      Rests r (takeWhileˢ i p c k tk s)           = RestsT r tk s
      Rests r (flatMapˢ op f fl oc k q so ls)     = Rests r so × RestsLanes r ls
      Rests r (connectˢ s₁ q S c k fd e src body) = Rests r src × Rests r body × Told e src body
      Rests r (deferˢ k s)                        = Rests r s
      Rests r t                                   = Lift _ (Opt (Waits r) (part t))

      RestsT : ∀ {Δ A} → Pos → Taking → Sub h Δ A → Set₁
      RestsT r taking     s = Rests r s
      RestsT r (ending q) s = Lift _ (Beyond r (just q))
      RestsT r taken      s = ⊤

      RestsLanes : ∀ {Δ B} → Pos → List (Lane h Δ B) → Set₁
      RestsLanes r []                = ⊤
      RestsLanes r (lane c k s ∷ ls) = Rests r s × RestsLanes r ls

    private
      all-waits : ∀ {Γ B} r (xs : List (Node Γ B)) → All (Waits r) xs → WaitsL r xs
      all-waits r []       []       = tt
      all-waits r (x ∷ xs) (w ∷ ws) = w , all-waits r xs ws

      opt-waits : ∀ {Γ B} r (x : Maybe (Node Γ B)) → Opt (Waits r) x → WaitsM r x
      opt-waits r nothing  _ = tt
      opt-waits r (just n) w = w

      under-waits : ∀ {Γ A B} r {F : Node Γ A → Node Γ B} → (∀ n → Waits r n → Waits r (F n)) → ∀ x → Opt (Waits r) x → Opt (Waits r) (mapᴹ F x)
      under-waits r f nothing  _ = tt
      under-waits r f (just n) w = f n w

      cons-waits : ∀ {Γ B} r (x : Maybe (Node Γ B)) {xs} → Opt (Waits r) x → All (Waits r) xs → All (Waits r) (consᴹ x xs)
      cons-waits r nothing  _ ws = ws
      cons-waits r (just n) w ws = w ∷ ws

      merged-waits : ∀ {Δ A B} r op (g : A → Pos → Node Δ B) o ls qs → WaitsM r o → WaitsL r ls → Opt (Waits r) (merged op g o ls qs)
      merged-waits r op g nothing  []      []      wo wl = tt
      merged-waits r op g nothing  []      (_ ∷ _) wo wl = wo , wl
      merged-waits r op g nothing  (_ ∷ _) qs      wo wl = wo , wl
      merged-waits r op g (just o) ls      qs      wo wl = wo , wl

      connected-waits : ∀ {Δ A B} r e (x : Maybe (Node Δ A)) (y : Maybe (Node (A ∷ Δ) B)) → Opt (Waits r) x → Opt (Waits r) y
                      → (∀ {c} → x ≡ nothing → e ≡ just c → mapᴹ (shut (here refl) c) y ≡ y) → Opt (Waits r) (connected e x y)
      connected-waits r e        x        nothing  wx wy td = tt
      connected-waits r e        (just s) (just b) wx wy td = wy , wx
      connected-waits r (just c) nothing  (just b) wx wy td = subst (Waits r) (sym (just-injective (td refl refl))) wy
      connected-waits r nothing  nothing  (just b) wx wy td = tt

    -- A SUB AT REST BEYOND `r` HOLDS OPEN ONLY WHAT WAITS BEYOND IT.
    mutual
      rests : ∀ {Δ A} r (t : Sub h Δ A) → Rests r t → Opt (Waits r) (part t)
      rests r (pendingˢ s q)                      (lift w)       = w
      rests r (coldˢ s hd ph)                     (lift w)       = w
      rests r (ofˢ p i xs)                        (lift w)       = w
      rests r doneˢ                               (lift w)       = w
      rests r (joinˢ j sk l x st)                 (lift w)       = w
      rests r (mapˢ f s)                          w              = under-waits r (λ n w → w) (part s) (rests r s w)
      rests r (scanˢ f z s)                       w              = under-waits r (λ n w → w) (part s) (rests r s w)
      rests r (takeWhileˢ i p c k tk s)           w with val (Kit.live c)
      ... | true  = rests-taking r i p tk s w
      ... | false = tt
      rests r (flatMapˢ op f fl oc k q so ls)     (wo , wl)      =
        merged-waits r op _ (part so) (partLanes ls) (val (Flat.queue fl)) (opt-waits r (part so) (rests r so wo))
          (all-waits r (partLanes ls) (rests-lanes r ls wl))
      rests r (connectˢ s₁ q S c k fd e src body) (ws , wb , td) = connected-waits r e (part src) (part body) (rests r src ws) (rests r body wb) td
      rests r (deferˢ k s)                        w              = rests r s w

      rests-taking : ∀ {Δ A} r i (p : A → Bool) tk (s : Sub h Δ A) → RestsT r tk s → Opt (Waits r) (partTaking i p tk (part s))
      rests-taking r i p taking     s w        = under-waits r (λ n w → w) (part s) (rests r s w)
      rests-taking r i p (ending q) s (lift b) = b
      rests-taking r i p taken      s _        = tt

      rests-lanes : ∀ {Δ B} r (ls : List (Lane h Δ B)) → RestsLanes r ls → All (Waits r) (partLanes ls)
      rests-lanes r []                _        = []
      rests-lanes r (lane c k s ∷ ls) (w , ws) with val (Kit.live c)
      ... | true  = cons-waits r (part s) (rests r s w) (rests-lanes r ls ws)
      ... | false = rests-lanes r ls ws

    -- EVERY SUB BESIDE THE PATH AT REST BEYOND `r`.
    mutual
      Rested : ∀ {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} → Pos → Path t u → Set₁
      Rested r here                   = ⊤
      Rested r (in-map π)             = Rested r π
      Rested r (in-scan π)            = Rested r π
      Rested r (in-take π)            = Rested r π
      Rested r (in-outer {ls = ls} π) = RestsLanes r ls × Rested r π
      Rested r (in-lanes {t = so} π)  = Rests r so × RestedLanes r π
      Rested r (in-source {b = b} π)  = Rests r b × Rested r π
      Rested r (in-body {t = s} π)    = Rests r s × Rested r π
      Rested r (in-defer π)           = Rested r π

      RestedLanes : ∀ {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} → Pos → PathLanes ls u → Set₁
      RestedLanes r (this-lane {ls = ls} π) = RestsLanes r ls × Rested r π
      RestedLanes r (next-lane {l = l} π)   = RestsLanes r (l ∷ []) × RestedLanes r π

    mutual
      rested : ∀ {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} r (π : Path t u) → Rested r π → Beside (Waits r) π
      rested r here                   _        = tt
      rested r (in-map π)             b        = rested r π b
      rested r (in-scan π)            b        = rested r π b
      rested r (in-take π)            b        = rested r π b
      rested r (in-outer {ls = ls} π) (rl , b) = rests-lanes r ls rl , rested r π b
      rested r (in-lanes {t = so} π)  (rs , b) = rests r so rs , rested-lanes r π b
      rested r (in-source {b = b′} π) (rs , b) = rests r b′ rs , rested r π b
      rested r (in-body {t = s} π)    (rs , b) = rests r s rs , rested r π b
      rested r (in-defer π)           b        = rested r π b

      rested-lanes : ∀ {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} r (π : PathLanes ls u) → RestedLanes r π → BesideLanes (Waits r) π
      rested-lanes r (this-lane {ls = ls} π) (rl , b) = rests-lanes r ls rl , rested r π b
      rested-lanes r (next-lane {l = l} π)   (rl , b) = rests-lanes r (l ∷ []) rl , rested-lanes r π b

    private
      merged-in : ∀ {Δ A B} op (g : A → Pos → Node Δ B) o bs (n : Node Δ B) as qs
                → merged op g o (bs ++ n ∷ as) qs ≡ just (flatMapᶜ op g o (bs ++ n ∷ as) qs)
      merged-in op g (just o) bs      n as qs = refl
      merged-in op g nothing  []      n as qs = refl
      merged-in op g nothing  (_ ∷ _) n as qs = refl

      connected-live : ∀ {Δ A B} e (m : Node Δ A) (b : Node (A ∷ Δ) B) → connected e (just m) (just b) ≡ just (connectᶜ b (live m))
      connected-live nothing  m b = refl
      connected-live (just c) m b = refl

      beyond-at : ∀ {Δ A} {r} {x : Maybe (Node Δ A)} {m} → x ≡ just m → OuterB r x → Beyondᴺ r m
      beyond-at refl b = b

      told-at : ∀ {Δ A B} {c} {x : Maybe (Node (A ∷ Δ) B)} {n} → x ≡ just n → mapᴹ (shut (here refl) c) x ≡ x → shut (here refl) c n ≡ n
      told-at refl e = just-injective e

      cons-beyond : ∀ {Γ A Δ B} {r} {m : Node Δ B} {bs as : List (Node Δ B)} {C : Ctx Γ A Δ B} → Beyondᴺ r m
                  → Clear r C × All (Beyondᴺ r) bs × All (Beyondᴺ r) as → Clear r C × All (Beyondᴺ r) (m ∷ bs) × All (Beyondᴺ r) as
      cons-beyond bm (x , ab , aa) = x , bm ∷ ab , aa

    -- THE NODE IN ITS CONTEXT: the open part at the top is the context
    -- plugged with the node, and the context is clear of `r` wherever
    -- every sub beside the path is.
    mutual
      focus-path : ∀ {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) → OpenPath π → Stable π
                 → ∀ {n} → part u ≡ just n
                 → Σ (Ctx Δ′ A′ Δ A) λ C → part t ≡ just (plug C n) × (∀ r → Beside (Beyondᴺ r) π → Clear r C)
      focus-path here o sb e = [] , e , λ _ _ → tt
      focus-path (in-map {f = f} π) o sb {n} e with focus-path π o sb e
      ... | C , pe , cl =
        C ∷ʳᶜ mapF f , trans (cong (mapᴹ (mapᶜ f)) pe) (cong just (sym (plug-∷ʳᶜ C (mapF f) n)))
        , λ r b → clear-∷ʳᶜ r C (mapF f) (cl r b) tt
      focus-path (in-scan {f = f} {r = z} π) o sb {n} e with focus-path π o sb e
      ... | C , pe , cl =
        C ∷ʳᶜ scanF f (val z) , trans (cong (mapᴹ (scanᶜ f (val z))) pe) (cong just (sym (plug-∷ʳᶜ C (scanF f (val z)) n)))
        , λ r b → clear-∷ʳᶜ r C (scanF f (val z)) (cl r b) tt
      focus-path (in-take {i = i} {p} {c} π) (lv , refl , o) sb {n} e with focus-path π o sb e
      ... | C , pe , cl rewrite lv | pe =
        C ∷ʳᶜ takeF i p , cong just (sym (plug-∷ʳᶜ C (takeF i p) n)) , λ r b → clear-∷ʳᶜ r C (takeF i p) (cl r b) tt
      focus-path (in-outer {op = op} {f} {fl} {ls = ls} π) o sb {n} e with focus-path π o sb e
      ... | C , pe , cl rewrite pe =
        C ∷ʳᶜ outerF op g (partLanes ls) q , cong just (sym (plug-∷ʳᶜ C (outerF op g (partLanes ls) q) n))
        , λ { r (al , b) → clear-∷ʳᶜ r C (outerF op g (partLanes ls) q) (cl r b) al }
        where g = λ a q′ → subscribe (f a) q′
              q = val (Flat.queue fl)
      focus-path (in-lanes {op = op} {f} {fl} {t = so} π) o sb {n} e with focus-lanes π o sb e
      ... | bs , as , C , pl , cl rewrite pl =
        C ∷ʳᶜ laneF op g (part so) bs as q
        , trans (merged-in op g (part so) bs (plug C n) as q) (cong just (sym (plug-∷ʳᶜ C (laneF op g (part so) bs as q) n)))
        , λ { r (ob , b) → clear-lane r (cl r b) ob }
        where g = λ a q′ → subscribe (f a) q′
              q = val (Flat.queue fl)
              clear-lane : ∀ r → Clear r C × All (Beyondᴺ r) bs × All (Beyondᴺ r) as → OuterB r (part so) → Clear r (C ∷ʳᶜ laneF op g (part so) bs as q)
              clear-lane r (c , ab , aa) ob = clear-∷ʳᶜ r C (laneF op g (part so) bs as q) c (ob , ab , aa)
      focus-path (in-source {e = e} {t = s} {b = b} π) ((m , pb) , o) sb {n} e′ with focus-path π o sb e′
      ... | C , pe , cl =
        C ∷ʳᶜ srcF m
        , trans (cong₂ (connected e) pe pb) (trans (connected-live e (plug C n) m) (cong just (sym (plug-∷ʳᶜ C (srcF m) n))))
        , λ { r (ob , b′) → clear-∷ʳᶜ r C (srcF m) (cl r b′) (beyond-at pb ob , tt) }
      focus-path (in-body {e = e} {t = s} {b = b} π) (inj₁ (m , ps) , o) (_ , sb) {n} e′ with focus-path π o sb e′
      ... | C , pe , cl =
        C ∷ʳᶜ bodyF m
        , trans (cong₂ (connected e) ps pe) (trans (connected-live e m (plug C n)) (cong just (sym (plug-∷ʳᶜ C (bodyF m) n))))
        , λ { r (ob , b′) → clear-∷ʳᶜ r C (bodyF m) (cl r b′) (beyond-at ps ob , tt) }
      focus-path (in-body {t = s} {b = b} π) (inj₂ (ps , c , refl) , o) (told , sb) {n} e′ with focus-path π o sb e′
      ... | C , pe , cl =
        C ∷ʳᶜ endedF c
        , trans (cong (connected (just c) (part s)) pe)
            (trans (cong (λ x → connected (just c) x (just (plug C n))) ps)
              (cong just (trans (cong (λ x → connectᶜ x (ended c)) (told-at pe (told ps refl)))
                                (sym (plug-∷ʳᶜ C (endedF c) n)))))
        , λ { r (_ , b′) → clear-∷ʳᶜ r C (endedF c) (cl r b′) tt }
      focus-path (in-defer π) o sb e = focus-path π o sb e

      focus-lanes : ∀ {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (π : PathLanes ls u) → OpenLanes π → StableLanes π
                  → ∀ {n} → part u ≡ just n
                  → Σ (List (Node Δ B)) λ bs → Σ (List (Node Δ B)) λ as → Σ (Ctx Δ′ A′ Δ B) λ C
                  → partLanes ls ≡ bs ++ plug C n ∷ as
                  × (∀ r → BesideLanes (Beyondᴺ r) π → Clear r C × All (Beyondᴺ r) bs × All (Beyondᴺ r) as)
      focus-lanes (this-lane {c = c} {ls = ls} π) (lv , o) sb e with focus-path π o sb e
      ... | C , pe , cl rewrite lv | pe = [] , partLanes ls , C , refl , λ { r (aa , b) → cl r b , [] , aa }
      focus-lanes (next-lane {l = lane c k s} π) o sb e with focus-lanes π o sb e
      ... | bs , as , C , pl , cl with val (Kit.live c) | part s
      ...   | true  | just m  rewrite pl = m ∷ bs , as , C , refl , λ { r (bm ∷ [] , b) → cons-beyond bm (cl r b) }
      ...   | true  | nothing rewrite pl = bs , as , C , refl , λ { r (_ , b) → cl r b }
      ...   | false | _       rewrite pl = bs , as , C , refl , λ { r (_ , b) → cl r b }
