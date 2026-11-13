{-# OPTIONS --guardedness #-}

-- EVERY VALUE COMES FROM SOMEWHERE.  A predicate holds of every value an
-- observable shows, wherever it is subscribed, once each operator's
-- inputs give it: a map's or scan's function keeps it, an of lists only
-- such values, a joiner's lanes and a connect's body show only such
-- values given such sources.  A skip, a pin or an end shows no value.
module denotation.Laws.Outs where

open import Data.Empty using (⊥)
open import Data.List using (List; _∷_)
open import Data.List.Relation.Unary.All using (All; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ)

open import Tree using (Obs; mergeᶠ; switchᶠ; exhaustᶠ; of; empty; map; scan; takeWhile; flatMap; connect)
open import denotation.Events using (Timeline)
open import denotation.Position using (Pos)
open import denotation.Events using (ofᴱ)
open import denotation.EmissionSet using (out; EmissionSet; Den; DenEnv; approx; hot; enter; Proper; InE; at-out; on-out; map-out;
  body; shown; module Scan; module TakeWhile; module Joining; module Connecting; module Op)

-- Every value `d` shows satisfies `P`.
Outs : ∀ {A} → (A → Set) → Den A → Set
Outs P d = ∀ {p k a} → enter d p k (out a) → P a

------------------------------------------------------------------------
-- Leaves

outs-of : ∀ {A} {P : A → Set} {xs} → All P xs → Outs P (Op.of xs)
outs-of {P = P} ps (r , _) = go ps r
  where
    go : ∀ {xs p i k a} → All P xs → InE (ofᴱ p i xs) k (out a) → P a
    go (px ∷ _)  at-out     = px
    go (_ ∷ pxs) (on-out r) = go pxs r

outs-empty : ∀ {A} {P : A → Set} → Outs P Op.empty
outs-empty (() , _)

outs-⊥ : ∀ {A} {P : A → Set} → Outs P Op.⊥
outs-⊥ (() , _)

------------------------------------------------------------------------
-- One input

outs-map : ∀ {A B} {P : A → Set} {Q : B → Set} {f : A → B} {s} → Outs P s → (∀ {x} → P x → Q (f x)) → Outs Q (Op.map f s)
outs-map hs hf (map-out x , _) = hf (hs x)

-- A scan's accumulators keep `R` from `z` on, each step taking a value
-- satisfying `P`.
outs-scan : ∀ {A B} {P : A → Set} {R : B → Set} {f : B → A → B} {z s} → Outs P s → R z → (∀ {b a} → R b → P a → R (f b a))
          → Outs R (Op.scan f z s)
outs-scan {P = P} {R} {f} {z} {s} hs rz hf {p} (Scan.sval c , _) = go c
  where
    open Scan f z (enter s p) using (Acc; acc₀; acc)
    go : ∀ {q b} → Acc q b → R b
    go (acc₀ x _)    = hf rz (hs x)
    go (acc c x _ _) = hf (go c) (hs x)

outs-take : ∀ {A} {P : A → Set} {i keep s} → Outs P s → Outs P (Op.takeWhile i keep s)
outs-take hs (TakeWhile.pass x _ _ , _)   = hs x
outs-take hs (TakeWhile.fail x _ _ _ , _) = hs x

outs-defer : ∀ {A} {P : A → Set} {s} → Outs P s → Outs P (Op.defer s)
outs-defer hs (body x , _) = hs x

------------------------------------------------------------------------
-- Joiners

module _ {A B : Set} {Lane : Pos → A → EmissionSet B} {o : EmissionSet A} {Bg : EmissionSet B} {Over Runs : Pos → Set}
         {Cut : Pos → Pos → Set} {Hand : Pos → Set} where
  open Joining Lane o Bg Over Runs Cut Hand using (JoinT; lane; run)

  join-outs : ∀ {Q : B → Set} → (∀ {q a k b} → o q (out a) → Lane q a k (out b) → Q b) → (∀ {k b} → Bg k (out b) → Q b)
            → ∀ {k b} → JoinT k (out b) → Q b
  join-outs hl hb (lane x _ l _ _) = hl x l
  join-outs hl hb (run x _)        = hb x

outs-flatMap : ∀ {A B} {P : A → Set} {Q : B → Set} op {F : A → Den B} {s} → Outs P s → (∀ {a} → P a → Outs Q (F a))
             → Outs Q (Op.flatMap op F s)
outs-flatMap (mergeᶠ nothing)  hs hF (j , _) = join-outs (λ x (l , _) → hF (hs x) l) (λ ()) j
outs-flatMap (mergeᶠ (just n)) hs hF (j , _) = join-outs (λ x (_ , _ , _ , l , _) → hF (hs x) l) (λ ()) j
outs-flatMap switchᶠ           hs hF (j , _) = join-outs (λ x (l , _) → hF (hs x) l) (λ ()) j
outs-flatMap exhaustᶠ          hs hF (j , _) = join-outs (λ x (l , _) → hF (hs x) l) (λ ()) j

------------------------------------------------------------------------
-- Connect

-- A source made hot shows the source's values.
outs-hot : ∀ {A} {P : A → Set} {t : EmissionSet A} → (∀ {k a} → t k (out a) → P a) → Outs P (hot (Proper t))
outs-hot ht (shown (x , _) _ _ , _) = ht x

outs-connect : ∀ {A B} {P : A → Set} {Q : B → Set} {s : Den A} {F : Den A → Den B} → Outs P s → (∀ h → Outs P h → Outs Q (F h))
             → Outs Q (Op.connect s F)
outs-connect {P = P} {s = s} hs hF (Connecting.body x , _) = hF _ (outs-hot {P = P} hs) x

------------------------------------------------------------------------
-- Up a tree

-- A tree whose values satisfy `Q`, read former by former: each operator's
-- inputs indexed by its own subtrees, so the operator is read off the
-- tree, and any subtree may be given by what it shows instead.
data Good (n : ℕ) : ∀ {Δ} → DenEnv Δ → ∀ {A} → Obs Timeline Δ A → (A → Set) → Set₁ where
  g-sem   : ∀ {Δ} {env : DenEnv Δ} {A} {s : Obs Timeline Δ A} {Q} → Outs Q (approx n s env) → Good n env s Q
  g-of    : ∀ {Δ} {env : DenEnv Δ} {A} {xs : List A} {Q} → All Q xs → Good n env (of xs) Q
  g-empty : ∀ {Δ} {env : DenEnv Δ} {A} {Q : A → Set} → Good n env empty Q
  g-map   : ∀ {Δ} {env : DenEnv Δ} {A B} {P : A → Set} {Q : B → Set} {f : A → B} {s} → Good n env s P → (∀ {x} → P x → Q (f x))
          → Good n env (map f s) Q
  g-scan  : ∀ {Δ} {env : DenEnv Δ} {A B} {P : A → Set} {R : B → Set} {f : B → A → B} {z s} → Good n env s P → R z
          → (∀ {b a} → R b → P a → R (f b a)) → Good n env (scan f z s) R
  g-take  : ∀ {Δ} {env : DenEnv Δ} {A} {P : A → Set} {i keep s} → Good n env s P → Good n env (takeWhile i keep s) P
  g-flat  : ∀ {Δ} {env : DenEnv Δ} {A B} {P : A → Set} {Q : B → Set} {op f s} → Good n env s P → (∀ {a} → P a → Good n env (f a) Q)
          → Good n env (flatMap op f s) Q
  g-conn  : ∀ {Δ} {env : DenEnv Δ} {A B} {P : A → Set} {Q : B → Set} {s b} → Good n env s P
          → (∀ h → Outs P h → Good n (h ∷ env) b Q) → Good n env (connect s b) Q

sound : ∀ {n Δ} {env : DenEnv Δ} {A} {s : Obs Timeline Δ A} {Q} → Good n env s Q → Outs Q (approx n s env)
sound (g-sem h)  = h
sound {Q = Q} (g-of qs) = outs-of {P = Q} qs
sound {Q = Q} g-empty = outs-empty {P = Q}
sound {n} {env = env} (g-map {P = P} {f = f} {s} g hf) = outs-map {P = P} {f = f} {s = approx n s env} (sound g) hf
sound {n} {env = env} (g-scan {P = P} {f = f} {z} {s} g rz hf) = outs-scan {P = P} {f = f} {z} {approx n s env} (sound g) rz hf
sound {n} {env = env} (g-take {i = i} {keep} {s} g) = outs-take {i = i} {keep} {approx n s env} (sound g)
sound {n} {env = env} (g-flat {P = P} {op = op} {f} {s} g gf) =
  outs-flatMap {P = P} op {λ a → approx n (f a) env} {approx n s env} (sound g) (λ pa → sound (gf pa))
sound {n} {env = env} (g-conn {P = P} {s = s} {b} g gb) =
  outs-connect {P = P} {s = approx n s env} {F = λ h → approx n b (h ∷ env)} (sound g) (λ h hh → sound (gb h hh))

-- Nothing asked of a tree's values.
g-top : ∀ {n Δ} {env : DenEnv Δ} {A} {s : Obs Timeline Δ A} → Good n env s (λ _ → ⊤)
g-top = g-sem (λ _ → tt)

g-map′ : ∀ {n Δ} {env : DenEnv Δ} {A B} {Q : B → Set} {f : A → B} {s} → (∀ {x} → Q (f x)) → Good n env (map f s) Q
g-map′ hf = g-map g-top (λ _ → hf)

g-flat′ : ∀ {n Δ} {env : DenEnv Δ} {A B} {Q : B → Set} {op} {f : A → Obs Timeline Δ B} {s} → (∀ {a} → Good n env (f a) Q)
        → Good n env (flatMap op f s) Q
g-flat′ hf = g-flat g-top (λ _ → hf)
