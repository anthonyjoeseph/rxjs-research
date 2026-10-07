------------------------------------------------------------------
-- WHERE A SUBSCRIBE'S EMITS LAND IN TIME.  Everything a subscribe sends
-- is subscribe-kind at its program's frame, and keeps that through
-- every map, scan and cut.  The first flattener up the path whose
-- restamp cell is not subscribe-kind restamps it there, a deferred
-- body's restamp restamps it at the hop's token, and the root takes
-- it at its own instant; a subscribe-kind cell restamps it at the
-- cell's own instant and passes it on.  A share's subject sends a
-- subscribe-kind emit to rows the derivation does not name, so nothing
-- is caught there; any other emit keeps its instant through every frame.
--
-- The catch is read at a node table of its own, not the one the
-- derivation is indexed by, so a walk's derivation can be read at the
-- tables the walk leaves.
------------------------------------------------------------------
module Simulation.Catch where

open import Data.Bool    using (T)
open import Data.Empty   using (⊥)
open import Data.List    using (List; _∷_)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe   using (just)
open import Data.Nat     using (ℕ; _<_; _≤_; _≡ᵇ_)
open import Data.Bool.ListAction using (any)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat.Properties using (≡⇒≡ᵇ; <-irrefl; <-≤-trans)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (inj₁; inj₂)
open import Data.Unit    using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Rx.Exp       using (Ctx; Val; Ty; Closed; FnClo; _×ᵗ_; lookupEnv)
open import Rx.Evaluator using (Path; NodeId; NodeState; Sched; EvalSt; Stream; lookupNode; setNode; cell-st; pathHasNode;
  Frame; frameNodes; map-f; scan-f; thru-outer; share-sink; echoᵗ; _↠[_]_)
import Data.Vec
open import Rx.Evaluator.Freshness using (set-above)
open import Rx.Evaluator.Reducible.Support using (∨-Tˡ; ∨-Tʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import SExp.Syntax  using (Kinds; plainᵏ; emitᵗ)
open import SExp.Elaborate using (FlatSᵗ)
open import Simulation.After using (readᴵ)
open import Simulation.Write using (apart)
open import Simulation.Stores using (PathRel; root~; sink~; map~; scan~; takeWhile~; spentWhile~; outerElem~; outerExplode~;
  inner~; deferInner~)

-- A NODE A PATH NAMES, as a constructor a derivation can be read off
data OnPath {m} {Δ : Ctx m} (k : NodeId) : ∀ {lo s u} → Path Δ lo s u → Set where
  at   : ∀ {lo ℓ s u v} {f : Frame Δ s u} {h : lo ≤ ℓ} {q : Path Δ ℓ u v} → k ∈ frameNodes f → OnPath k (f ↠[ h ] q)
  past : ∀ {lo ℓ s u v} {f : Frame Δ s u} {h : lo ≤ ℓ} {q : Path Δ ℓ u v} → OnPath k q → OnPath k (f ↠[ h ] q)

on-path : ∀ {m} {Δ : Ctx m} {k lo s u} {q : Path Δ lo s u} → OnPath k q → T (pathHasNode k q)
on-path {k = k} (at {f = f} x) = ∨-Tˡ {any (_≡ᵇ k) (frameNodes f)} (in-any x)
  where
  in-any : ∀ {xs} → k ∈ xs → T (any (_≡ᵇ k) xs)
  in-any {x ∷ _} (here refl) = ∨-Tˡ {k ≡ᵇ k} (≡⇒≡ᵇ k k refl)
  in-any {x ∷ _} (there y)   = ∨-Tʳ {x ≡ᵇ k} (in-any y)
on-path {k = k} (past {f = f} o) = ∨-Tʳ {any (_≡ᵇ k) (frameNodes f)} (on-path o)

module _ {n} {Γ : Ctx n} (κ : Kinds n) where

  -- a restamp cell's kind: subscribe-kind passes on at the cell's
  -- instant, any other restamps at it
  ByKind : ∀ {u} → Val (plainᵏ Γ κ) (FlatSᵗ u) → (ℕ → Set) → (ℕ → Set) → Set
  ByKind ((i , inj₁ _) , _) sub other = sub i
  ByKind ((i , inj₂ _) , _) sub other = other i

  by-sub : ∀ {u} {c : Val (plainᵏ Γ κ) (FlatSᵗ u)} {i} {X Y : ℕ → Set} → proj₁ c ≡ (i , inj₁ tt) → X i → ByKind c X Y
  by-sub {c = ((i , inj₁ tt) , _)} refl x = x

  by-sub⁻ : ∀ {u} {c : Val (plainᵏ Γ κ) (FlatSᵗ u)} {i} {X Y : ℕ → Set} → proj₁ c ≡ (i , inj₁ tt) → ByKind c X Y → X i
  by-sub⁻ {c = ((i , inj₁ tt) , _)} refl x = x

  by-const : ∀ {u} (c : Val (plainᵏ Γ κ) (FlatSᵗ u)) {X Y : Set} → X → Y → ByKind c (λ _ → X) (λ _ → Y)
  by-const ((_ , inj₁ _) , _) x y = x
  by-const ((_ , inj₂ _) , _) x y = y

  by-map : ∀ {u} (c : Val (plainᵏ Γ κ) (FlatSᵗ u)) {X X′ Y Y′ : ℕ → Set}
         → (∀ {i} → X i → X′ i) → (∀ {i} → Y i → Y′ i) → ByKind c X Y → ByKind c X′ Y′
  by-map ((_ , inj₁ _) , _) f g x = f x
  by-map ((_ , inj₂ _) , _) f g y = g y

  by-zip : ∀ {u} (c : Val (plainᵏ Γ κ) (FlatSᵗ u)) {X X′ X″ Y Y′ Y″ : ℕ → Set}
         → (∀ {i} → X i → X′ i → X″ i) → (∀ {i} → Y i → Y′ i → Y″ i) → ByKind c X Y → ByKind c X′ Y′ → ByKind c X″ Y″
  by-zip ((_ , inj₁ _) , _) f g x x′ = f x x′
  by-zip ((_ , inj₂ _) , _) f g y y′ = g y y′

  -- two cells at one instant and kind read alike
  by-tr : ∀ {u} (c c′ : Val (plainᵏ Γ κ) (FlatSᵗ u)) {X Y : ℕ → Set} → proj₁ c′ ≡ proj₁ c → ByKind c X Y → ByKind c′ X Y
  by-tr ((_ , inj₁ _) , _) (_ , _) refl b = b
  by-tr ((_ , inj₂ _) , _) (_ , _) refl b = b

  -- AN EMIT AT ITS PROGRAM'S FRAME: subscribe-kind, at `f`
  AtFrame : ∀ {u} → ℕ → Val (plainᵏ Γ κ) (emitᵗ u) → Set
  AtFrame f (_ , (i , (_ , inj₁ _))) = i ≡ f
  AtFrame f (_ , (_ , (_ , inj₂ _))) = ⊥

  -- a write above every node a path names leaves its nodes' reads
  unmoved-set : ∀ {Q : ℕ → Set} {N N′ : List (NodeId × NodeState (plainᵏ Γ κ))} {c m} (x : NodeState (plainᵏ Γ κ))
              → (∀ k → Q k → k < c) → c ≤ m → (∀ k → Q k → lookupNode k N′ ≡ lookupNode k N)
              → ∀ k → Q k → lookupNode k (setNode m x N′) ≡ lookupNode k N
  unmoved-set {N′ = N′} {m = m} x fr le H k h =
    trans (set-above m k x N′ (apart m k (λ e → <-irrefl e (<-≤-trans (fr k h) le)))) (H k h)

  module _ {t : Ty} where

    -- AN EMIT SUBSCRIBE-KIND AT `f` LANDS AT `I`, read at the table `N`
    Catch : ℕ → ℕ → List (NodeId × NodeState (plainᵏ Γ κ))
          → ∀ {π NP NI lo lo′ s} {p : Path Γ lo s t} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t)} → PathRel κ π {t} NP NI {lo} {lo′} {s} p q → Set
    Catch I f N root~                    = f ≡ I
    Catch I f N (sink~ _)                = ⊥
    Catch I f N (map~ _ d)               = Catch I f N d
    Catch I f N (scan~ _ _ _ _ _ d)      = Catch I f N d
    Catch I f N (takeWhile~ _ _ _ _ _ d) = Catch I f N d
    Catch I f N (spentWhile~ _ _ _ d)    = Catch I f N d
    Catch I f N (outerElem~ {u = u} {ks = ks} _ d) =
      Σ (Val (plainᵏ Γ κ) (FlatSᵗ u)) λ c → lookupNode ks N ≡ just (cell-st {t = FlatSᵗ u} c)
        × ByKind c (λ i → Catch I i N d) (λ i → i ≡ I)
    Catch I f N (outerExplode~ {u = u} {ks = ks} _ d) =
      Σ (Val (plainᵏ Γ κ) (FlatSᵗ u)) λ c → lookupNode ks N ≡ just (cell-st {t = FlatSᵗ u} c)
        × ByKind c (λ i → Catch I i N d) (λ i → i ≡ I)
    Catch I f N (inner~ {u = u} {ks = ks} _ _ _ d) =
      Σ (Val (plainᵏ Γ κ) (FlatSᵗ u)) λ c → lookupNode ks N ≡ just (cell-st {t = FlatSᵗ u} c)
        × ByKind c (λ i → Catch I i N d) (λ i → i ≡ I)
    Catch I f N (deferInner~ {ρ₀ = ρ₀} _ _ _ _ _ _ _ d) = lookupEnv ρ₀ (here refl) ≡ I

    -- WHAT A SUBSCRIBE LEAVES OF A CATCH: every restamp cell up to and
    -- including the one that catches holds the instant and kind it held
    Kept : (N N′ : List (NodeId × NodeState (plainᵏ Γ κ)))
         → ∀ {π NP NI lo lo′ s} {p : Path Γ lo s t} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t)} → PathRel κ π {t} NP NI {lo} {lo′} {s} p q → Set
    Kept N N′ root~                    = ⊤
    Kept N N′ (sink~ _)                = ⊤
    Kept N N′ (map~ _ d)               = Kept N N′ d
    Kept N N′ (scan~ _ _ _ _ _ d)      = Kept N N′ d
    Kept N N′ (takeWhile~ _ _ _ _ _ d) = Kept N N′ d
    Kept N N′ (spentWhile~ _ _ _ d)    = Kept N N′ d
    Kept N N′ (outerElem~ {u = u} {ks = ks} _ d) =
      ∀ c → lookupNode ks N ≡ just (cell-st {t = FlatSᵗ u} c)
      → Σ (Val (plainᵏ Γ κ) (FlatSᵗ u)) λ c′ → lookupNode ks N′ ≡ just (cell-st {t = FlatSᵗ u} c′)
          × proj₁ c′ ≡ proj₁ c × ByKind c (λ _ → Kept N N′ d) (λ _ → ⊤)
    Kept N N′ (outerExplode~ {u = u} {ks = ks} _ d) =
      ∀ c → lookupNode ks N ≡ just (cell-st {t = FlatSᵗ u} c)
      → Σ (Val (plainᵏ Γ κ) (FlatSᵗ u)) λ c′ → lookupNode ks N′ ≡ just (cell-st {t = FlatSᵗ u} c′)
          × proj₁ c′ ≡ proj₁ c × ByKind c (λ _ → Kept N N′ d) (λ _ → ⊤)
    Kept N N′ (inner~ {u = u} {ks = ks} _ _ _ d) =
      ∀ c → lookupNode ks N ≡ just (cell-st {t = FlatSᵗ u} c)
      → Σ (Val (plainᵏ Γ κ) (FlatSᵗ u)) λ c′ → lookupNode ks N′ ≡ just (cell-st {t = FlatSᵗ u} c′)
          × proj₁ c′ ≡ proj₁ c × ByKind c (λ _ → Kept N N′ d) (λ _ → ⊤)
    Kept N N′ (deferInner~ _ _ _ _ _ _ _ d) = ⊤

    -- A FLATTENER'S OUTER, TAKEN APART AT ANY OPERATOR: its own frames'
    -- operator is the policy's image, which no pattern can invert
    elem-tail : ∀ {π NP NI lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ u x y o o′ m m′ ks}
                  {G₀ : FnClo (plainᵏ Γ κ) (emitᵗ (echoᵗ u)) (echoᵗ x)} {G₁ : FnClo (plainᵏ Γ κ) (y ×ᵗ x) y}
                  {G₂ : FnClo (plainᵏ Γ κ) y (emitᵗ u)}
                  {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄}
                  {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)}
              → PathRel κ π {t} NP NI (thru-outer o m ↠[ h ] p)
                  (map-f G₀ ↠[ h₁ ] (thru-outer o′ m′ ↠[ h₂ ] (scan-f G₁ ks ↠[ h₃ ] (map-f G₂ ↠[ h₄ ] q))))
              → PathRel κ π NP NI p q
    elem-tail (outerElem~ _ d) = d

    elem-catch : ∀ {I f N π NP NI lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ u x y o o′ m m′ ks}
                   {G₀ : FnClo (plainᵏ Γ κ) (emitᵗ (echoᵗ u)) (echoᵗ x)} {G₁ : FnClo (plainᵏ Γ κ) (y ×ᵗ x) y}
                   {G₂ : FnClo (plainᵏ Γ κ) y (emitᵗ u)}
                   {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄}
                   {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)}
               → (d : PathRel κ π {t} NP NI (thru-outer o m ↠[ h ] p)
                        (map-f G₀ ↠[ h₁ ] (thru-outer o′ m′ ↠[ h₂ ] (scan-f G₁ ks ↠[ h₃ ] (map-f G₂ ↠[ h₄ ] q)))))
               → Σ (Val (plainᵏ Γ κ) (FlatSᵗ u)) (λ c → lookupNode ks N ≡ just (cell-st {t = FlatSᵗ u} c)
                   × ByKind c (λ i → Catch I i N (elem-tail d)) (λ i → i ≡ I))
               → Catch I f N d
    elem-catch (outerElem~ _ d) x = x

    elem-kept : ∀ {N N′ π NP NI lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ u x y o o′ m m′ ks}
                  {G₀ : FnClo (plainᵏ Γ κ) (emitᵗ (echoᵗ u)) (echoᵗ x)} {G₁ : FnClo (plainᵏ Γ κ) (y ×ᵗ x) y}
                  {G₂ : FnClo (plainᵏ Γ κ) y (emitᵗ u)}
                  {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄}
                  {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₄ (emitᵗ u) (emitᵗ t)}
              → (d : PathRel κ π {t} NP NI (thru-outer o m ↠[ h ] p)
                       (map-f G₀ ↠[ h₁ ] (thru-outer o′ m′ ↠[ h₂ ] (scan-f G₁ ks ↠[ h₃ ] (map-f G₂ ↠[ h₄ ] q)))))
              → (∀ c → lookupNode ks N ≡ just (cell-st {t = FlatSᵗ u} c)
                 → Σ (Val (plainᵏ Γ κ) (FlatSᵗ u)) λ c′ → lookupNode ks N′ ≡ just (cell-st {t = FlatSᵗ u} c′)
                     × proj₁ c′ ≡ proj₁ c × ByKind c (λ _ → Kept N N′ (elem-tail d)) (λ _ → ⊤))
              → Kept N N′ d
    elem-kept (outerElem~ _ d) x = x

    -- the same, one element per inner
    explode-tail : ∀ {π NP NI lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ u w x y o o′ o″ m m′ ks mX}
                     {G₀ : FnClo (plainᵏ Γ κ) (emitᵗ (echoᵗ u)) w} {G₅ : FnClo (plainᵏ Γ κ) w (echoᵗ (echoᵗ x))}
                     {G₁ : FnClo (plainᵏ Γ κ) (y ×ᵗ x) y} {G₂ : FnClo (plainᵏ Γ κ) y (emitᵗ u)}
                     {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {h₅ : ℓ₄ ≤ ℓ₅} {h₆ : ℓ₅ ≤ ℓ₆}
                     {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₆ (emitᵗ u) (emitᵗ t)}
                 → PathRel κ π {t} NP NI (thru-outer o m ↠[ h ] p)
                     (map-f G₀ ↠[ h₁ ] (map-f G₅ ↠[ h₂ ] (thru-outer o″ mX ↠[ h₃ ]
                       (thru-outer o′ m′ ↠[ h₄ ] (scan-f G₁ ks ↠[ h₅ ] (map-f G₂ ↠[ h₆ ] q))))))
                 → PathRel κ π NP NI p q
    explode-tail (outerExplode~ _ d) = d

    explode-catch : ∀ {I f N π NP NI lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ u w x y o o′ o″ m m′ ks mX}
                      {G₀ : FnClo (plainᵏ Γ κ) (emitᵗ (echoᵗ u)) w} {G₅ : FnClo (plainᵏ Γ κ) w (echoᵗ (echoᵗ x))}
                      {G₁ : FnClo (plainᵏ Γ κ) (y ×ᵗ x) y} {G₂ : FnClo (plainᵏ Γ κ) y (emitᵗ u)}
                      {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {h₅ : ℓ₄ ≤ ℓ₅} {h₆ : ℓ₅ ≤ ℓ₆}
                      {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₆ (emitᵗ u) (emitᵗ t)}
                  → (d : PathRel κ π {t} NP NI (thru-outer o m ↠[ h ] p)
                           (map-f G₀ ↠[ h₁ ] (map-f G₅ ↠[ h₂ ] (thru-outer o″ mX ↠[ h₃ ]
                             (thru-outer o′ m′ ↠[ h₄ ] (scan-f G₁ ks ↠[ h₅ ] (map-f G₂ ↠[ h₆ ] q)))))))
                  → Σ (Val (plainᵏ Γ κ) (FlatSᵗ u)) (λ c → lookupNode ks N ≡ just (cell-st {t = FlatSᵗ u} c)
                      × ByKind c (λ i → Catch I i N (explode-tail d)) (λ i → i ≡ I))
                  → Catch I f N d
    explode-catch (outerExplode~ _ d) x = x

    explode-kept : ∀ {N N′ π NP NI lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ u w x y o o′ o″ m m′ ks mX}
                     {G₀ : FnClo (plainᵏ Γ κ) (emitᵗ (echoᵗ u)) w} {G₅ : FnClo (plainᵏ Γ κ) w (echoᵗ (echoᵗ x))}
                     {G₁ : FnClo (plainᵏ Γ κ) (y ×ᵗ x) y} {G₂ : FnClo (plainᵏ Γ κ) y (emitᵗ u)}
                     {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃} {h₄ : ℓ₃ ≤ ℓ₄} {h₅ : ℓ₄ ≤ ℓ₅} {h₆ : ℓ₅ ≤ ℓ₆}
                     {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ₆ (emitᵗ u) (emitᵗ t)}
                 → (d : PathRel κ π {t} NP NI (thru-outer o m ↠[ h ] p)
                          (map-f G₀ ↠[ h₁ ] (map-f G₅ ↠[ h₂ ] (thru-outer o″ mX ↠[ h₃ ]
                            (thru-outer o′ m′ ↠[ h₄ ] (scan-f G₁ ks ↠[ h₅ ] (map-f G₂ ↠[ h₆ ] q)))))))
                 → (∀ c → lookupNode ks N ≡ just (cell-st {t = FlatSᵗ u} c)
                    → Σ (Val (plainᵏ Γ κ) (FlatSᵗ u)) λ c′ → lookupNode ks N′ ≡ just (cell-st {t = FlatSᵗ u} c′)
                        × proj₁ c′ ≡ proj₁ c × ByKind c (λ _ → Kept N N′ (explode-tail d)) (λ _ → ⊤))
                 → Kept N N′ d
    explode-kept (outerExplode~ _ d) x = x

    -- a share's subject, at any impl path
    sink-kept : ∀ {N N′ π NP NI lo lo′ i h} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ (Data.Vec.lookup Γ i)) (emitᵗ t)}
                (d : PathRel κ π {t} NP NI {lo} (share-sink i h) q) → Kept N N′ d
    sink-kept (sink~ _) = tt

    -- WHAT A RESTAMP CELL RECORDS IS A FACT ABOUT THE PATHS, so any two
    -- derivations of one pair of paths agree on all three
    record Same {π π′ NP NP′ NI NI′ lo lo′ s} {p : Path Γ lo s t} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t)}
                (d : PathRel κ π {t} NP NI p q) (d′ : PathRel κ π′ {t} NP′ NI′ p q) : Set where
      field
        cat : ∀ {I f N} → Catch I f N d → Catch I f N d′
        kep : ∀ {N N′} → Kept N N′ d → Kept N N′ d′

    same : ∀ {π π′ NP NP′ NI NI′ lo lo′ s} {p : Path Γ lo s t} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t)}
           (d : PathRel κ π {t} NP NI p q) (d′ : PathRel κ π′ {t} NP′ NI′ p q) → Same d d′
    same root~ root~ = record { cat = λ x → x ; kep = λ x → x }
    same (sink~ _) d′ = record { cat = λ () ; kep = λ _ → sink-kept d′ }
    same (map~ _ d) (map~ _ d′) = let S = same d d′ in record { cat = Same.cat S ; kep = Same.kep S }
    same (scan~ _ _ _ _ _ d) (scan~ _ _ _ _ _ d′) =
      let S = same d d′ in record { cat = Same.cat S ; kep = Same.kep S }
    same (takeWhile~ _ _ _ _ _ d) (takeWhile~ _ _ _ _ _ d′) =
      let S = same d d′ in record { cat = Same.cat S ; kep = Same.kep S }
    same (takeWhile~ _ _ _ _ _ d) (spentWhile~ _ _ _ d′) =
      let S = same d d′ in record { cat = Same.cat S ; kep = Same.kep S }
    same (spentWhile~ _ _ _ d) (takeWhile~ _ _ _ _ _ d′) =
      let S = same d d′ in record { cat = Same.cat S ; kep = Same.kep S }
    same (spentWhile~ _ _ _ d) (spentWhile~ _ _ _ d′) =
      let S = same d d′ in record { cat = Same.cat S ; kep = Same.kep S }
    same (outerElem~ _ d) d′ =
      let S = same d (elem-tail d′) in record
        { cat = λ (c , l , b) → elem-catch d′ (c , l , by-map c (λ {i} → Same.cat S {f = i}) (λ e → e) b)
        ; kep = λ k → elem-kept d′ λ c l → let (c′ , l′ , e , b) = k c l in c′ , l′ , e , by-map c (Same.kep S) (λ y → y) b
        }
    same (outerExplode~ _ d) d′ =
      let S = same d (explode-tail d′) in record
        { cat = λ (c , l , b) → explode-catch d′ (c , l , by-map c (λ {i} → Same.cat S {f = i}) (λ e → e) b)
        ; kep = λ k → explode-kept d′ λ c l → let (c′ , l′ , e , b) = k c l in c′ , l′ , e , by-map c (Same.kep S) (λ y → y) b
        }
    same (inner~ _ _ _ d) (inner~ _ _ _ d′) =
      let S = same d d′ in record
        { cat = λ (c , l , b) → c , l , by-map c (λ {i} → Same.cat S {f = i}) (λ e → e) b
        ; kep = λ k c l → let (c′ , l′ , e , b) = k c l in c′ , l′ , e , by-map c (Same.kep S) (λ y → y) b
        }
    same (deferInner~ _ _ _ _ _ _ _ d) (deferInner~ _ _ _ _ _ _ _ d′) =
      let S = same d d′ in record { cat = λ e → e ; kep = λ _ → tt }

    catch-same : ∀ {I f N π π′ NP NP′ NI NI′ lo lo′ s} {p : Path Γ lo s t} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t)}
                 (d : PathRel κ π {t} NP NI p q) (d′ : PathRel κ π′ {t} NP′ NI′ p q) → Catch I f N d → Catch I f N d′
    catch-same d d′ = Same.cat (same d d′)

    kept-same : ∀ {N N′ π π′ NP NP′ NI NI′ lo lo′ s} {p : Path Γ lo s t} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t)}
                (d : PathRel κ π {t} NP NI p q) (d′ : PathRel κ π′ {t} NP′ NI′ p q) → Kept N N′ d → Kept N N′ d′
    kept-same d d′ = Same.kep (same d d′)

    kept-refl : ∀ {N π NP NI lo lo′ s} {p : Path Γ lo s t} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t)}
                (d : PathRel κ π {t} NP NI p q) → Kept N N d
    kept-refl root~                    = tt
    kept-refl (sink~ _)                = tt
    kept-refl (map~ _ d)               = kept-refl d
    kept-refl (scan~ _ _ _ _ _ d)      = kept-refl d
    kept-refl (takeWhile~ _ _ _ _ _ d) = kept-refl d
    kept-refl (spentWhile~ _ _ _ d)    = kept-refl d
    kept-refl (outerElem~ _ d)         = λ c l → c , l , refl , by-const c (kept-refl d) tt
    kept-refl (outerExplode~ _ d)      = λ c l → c , l , refl , by-const c (kept-refl d) tt
    kept-refl (inner~ _ _ _ d)         = λ c l → c , l , refl , by-const c (kept-refl d) tt
    kept-refl (deferInner~ _ _ _ _ _ _ _ d) = tt

    kept-trans : ∀ {N₀ N₁ N₂ π NP NI lo lo′ s} {p : Path Γ lo s t} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t)}
                 (d : PathRel κ π {t} NP NI p q) → Kept N₀ N₁ d → Kept N₁ N₂ d → Kept N₀ N₂ d
    kept-trans root~                    _ _ = tt
    kept-trans (sink~ _)                _ _ = tt
    kept-trans (map~ _ d)               x y = kept-trans d x y
    kept-trans (scan~ _ _ _ _ _ d)      x y = kept-trans d x y
    kept-trans (takeWhile~ _ _ _ _ _ d) x y = kept-trans d x y
    kept-trans (spentWhile~ _ _ _ d)    x y = kept-trans d x y
    kept-trans (outerElem~ _ d)         x y = λ c l →
      let (c′ , l′ , e , b) = x c l ; (c″ , l″ , e′ , b′) = y c′ l′
      in c″ , l″ , trans e′ e , by-zip c (kept-trans d) (λ _ _ → tt) b (by-tr c′ c (sym e) b′)
    kept-trans (outerExplode~ _ d)      x y = λ c l →
      let (c′ , l′ , e , b) = x c l ; (c″ , l″ , e′ , b′) = y c′ l′
      in c″ , l″ , trans e′ e , by-zip c (kept-trans d) (λ _ _ → tt) b (by-tr c′ c (sym e) b′)
    kept-trans (inner~ _ _ _ d)         x y = λ c l →
      let (c′ , l′ , e , b) = x c l ; (c″ , l″ , e′ , b′) = y c′ l′
      in c″ , l″ , trans e′ e , by-zip c (kept-trans d) (λ _ _ → tt) b (by-tr c′ c (sym e) b′)
    kept-trans (deferInner~ _ _ _ _ _ _ _ d) _ _ = tt

    -- A CATCH SURVIVES WHAT KEEPS IT: the cells up to the catch read the
    -- same instants and kinds at the new table
    kept-catch : ∀ {I f N N′ π NP NI lo lo′ s} {p : Path Γ lo s t} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t)}
                 (d : PathRel κ π {t} NP NI p q) → Catch I f N d → Kept N N′ d → Catch I f N′ d
    kept-catch root~                    x _ = x
    kept-catch (sink~ _)                () _
    kept-catch (map~ _ d)               x k = kept-catch d x k
    kept-catch (scan~ _ _ _ _ _ d)      x k = kept-catch d x k
    kept-catch (takeWhile~ _ _ _ _ _ d) x k = kept-catch d x k
    kept-catch (spentWhile~ _ _ _ d)    x k = kept-catch d x k
    kept-catch (outerElem~ _ d) (c , l , b) k =
      let (c′ , l′ , e , kb) = k c l in c′ , l′ , by-tr c c′ e (by-zip c (λ {i} → kept-catch {f = i} d) (λ y _ → y) b kb)
    kept-catch (outerExplode~ _ d) (c , l , b) k =
      let (c′ , l′ , e , kb) = k c l in c′ , l′ , by-tr c c′ e (by-zip c (λ {i} → kept-catch {f = i} d) (λ y _ → y) b kb)
    kept-catch (inner~ _ _ _ d) (c , l , b) k =
      let (c′ , l′ , e , kb) = k c l in c′ , l′ , by-tr c c′ e (by-zip c (λ {i} → kept-catch {f = i} d) (λ y _ → y) b kb)
    kept-catch (deferInner~ _ _ _ _ _ _ _ d) x _ = x

    -- NOTHING WRITTEN AT A NODE THE PATH NAMES KEEPS EVERY CELL
    kept-unmoved : ∀ {N N′ π NP NI lo lo′ s} {p : Path Γ lo s t} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t)}
                   (d : PathRel κ π {t} NP NI p q)
                 → (∀ k → OnPath k q → lookupNode k N′ ≡ lookupNode k N) → Kept N N′ d
    kept-unmoved root~                    H = tt
    kept-unmoved (sink~ _)                H = tt
    kept-unmoved (map~ _ d)               H = kept-unmoved d (λ k h → H k (past h))
    kept-unmoved (scan~ _ _ _ _ _ d)      H = kept-unmoved d (λ k h → H k (past (past h)))
    kept-unmoved (takeWhile~ _ _ _ _ _ d) H = kept-unmoved d (λ k h → H k (past (past (past h))))
    kept-unmoved (spentWhile~ _ _ _ d)    H = kept-unmoved d (λ k h → H k (past (past (past h))))
    kept-unmoved (outerElem~ {ks = ks} _ d) H = λ c l →
      c , trans (H ks (past (past (at (here refl))))) l , refl
        , by-const c (kept-unmoved d (λ k h → H k (past (past (past (past h)))))) tt
    kept-unmoved (outerExplode~ {ks = ks} _ d) H = λ c l →
      c , trans (H ks (past (past (past (past (at (here refl))))))) l , refl
        , by-const c (kept-unmoved d (λ k h → H k (past (past (past (past (past (past h)))))))) tt
    kept-unmoved (inner~ {ks = ks} _ _ _ d) H = λ c l →
      c , trans (H ks (past (at (here refl)))) l , refl
        , by-const c (kept-unmoved d (λ k h → H k (past (past (past h))))) tt
    kept-unmoved (deferInner~ _ _ _ _ _ _ _ d) H = tt

  -- WHAT ONE SUBSCRIBE OWES ITS CATCH: everything it sends to the root
  -- at the instant its path catches its frame, and every restamp cell up
  -- to the catch kept
  Stamps : ∀ {t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)} {π NP NI lo lo′ s}
             {p : Path Γ lo s t} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t)}
         → ℕ → PathRel κ π {t} NP NI p q → EvalSt ei
         → Stream (plainᵏ Γ κ) (emitᵗ t) × Sched (plainᵏ Γ κ) × EvalSt ei → Set
  Stamps f d stI rI =
    ∀ {I} → Catch I f (EvalSt.nodes stI) d
    → All (λ y → proj₁ y ≡ I) (readᴵ (proj₁ rI)) × Kept (EvalSt.nodes stI) (EvalSt.nodes (proj₂ (proj₂ rI))) d
