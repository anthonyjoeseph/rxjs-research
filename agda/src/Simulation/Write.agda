------------------------------------------------------------------
-- A FLATTENER'S NODE PAIR WRITTEN, AND THE ROWS UNMOVED.  Every node
-- fact the rows state is about a node the row's own path names, and a
-- write to the flattener's pair moves none of them but the flattener's
-- own.
--
-- A FACT AT ANOTHER NODE IS APART FROM THE WRITE BY ITS KIND OR BY `π`.
-- A cell or a count never sits where a flattener's state does; a merge
-- that could is a node `π` pairs, and `π`'s keys and values are each
-- unique, so it is the written one only if its entry is the
-- flattener's, which its shape refutes; an impl-only node is
-- `Unpaired`, and the written impl node is paired.
--
-- A FLATTENER FACT AT THE WRITTEN NODE IS THE WRITTEN FLATTENER'S, up
-- to its element type: a switch and an exhaust state carry none, and a
-- merge state carries its own, so the new pair relates at every type
-- the old one did.
------------------------------------------------------------------
module Simulation.Write where

open import Data.Bool    using (true; false)
open import Data.Empty   using (⊥; ⊥-elim)
open import Data.List    using (List; []; _∷_; _++_; map; concatMap)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-map⁺)
open import Data.List.Relation.Unary.All using () renaming (lookup to all-lookup)
open import Data.List.Relation.Unary.All.Properties using (++⁻ˡ)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Maybe   using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat     using (ℕ; _≤_; pred; _≡ᵇ_; _≟_)
open import Data.Nat.Properties using (≤-trans; pred[n]≤n)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Decide       using (≡ᵇ→≡)
open import Rx.Exp       using (Ty; Ctx; Val)
open import Rx.Evaluator using (NodeId; NodeState; Path; cell-st; take-st; mergeAll-st; echoᵗ; lookupNode; setNode)
open import Rx.Evaluator.Freshness using (lookup-set; set-above)
open import SExp.Syntax  using (Kinds; plainᵏ; emitᵗ)
open import SExp.Elaborate using (FlatSᵗ)
open import Simulation.Stores using (Unpaired; FlatNodes; merge~; switch~; exhaust~; Flattener; PathRel; root~; sink~; map~; scan~;
  takeWhile~; spentWhile~; outerElem~; outerExplode~; inner~; deferInner~; InputBlock; block; RowRel; read~; cold~; defer~;
  MachRow; hot~; RegRel; []; _∷_; mach; Partners; ArrRows; Spent; MergeAt)

-- a node read back after a write elsewhere
apart : ∀ m k → (k ≡ m → ⊥) → (m ≡ᵇ k) ≡ false
apart m k ne with m ≡ᵇ k in eq
... | false = refl
... | true  = ⊥-elim (ne (sym (≡ᵇ→≡ m k eq)))

-- two halves of a list without repeats share nothing
apart-++ : ∀ {A : Set} {xs ys : List A} {z} → Unique (xs ++ ys) → z ∈ xs → z ∈ ys → ⊥
apart-++ {xs = _ ∷ xs} (a ∷ _) (here refl) zy = all-lookup a (∈-++⁺ʳ xs zy) refl
apart-++ {xs = _ ∷ _}  (_ ∷ u) (there zx)  zy = apart-++ u zx zy

unique-++ʳ : ∀ {A : Set} (xs : List A) {ys} → Unique (xs ++ ys) → Unique ys
unique-++ʳ []       u       = u
unique-++ʳ (_ ∷ xs) (_ ∷ u) = unique-++ʳ xs u

unique-++ˡ : ∀ {A : Set} (xs : List A) {ys} → Unique (xs ++ ys) → Unique xs
unique-++ˡ []       _       = []
unique-++ˡ (_ ∷ xs) (a ∷ u) = ++⁻ˡ xs a ∷ unique-++ˡ xs u

∈-vals : ∀ {π : List (NodeId × List NodeId)} {a xs z} → (a , xs) ∈ π → z ∈ xs → z ∈ concatMap proj₂ π
∈-vals (here refl) zx = ∈-++⁺ˡ zx
∈-vals {π = (_ , ys) ∷ _} (there e) zx = ∈-++⁺ʳ ys (∈-vals e zx)

-- AN IMPL NODE `π` PAIRS, IT PAIRS ONCE
vals-same : ∀ {π : List (NodeId × List NodeId)} {a b xs ys z} → Unique (concatMap proj₂ π)
          → (a , xs) ∈ π → (b , ys) ∈ π → z ∈ xs → z ∈ ys → (a , xs) ≡ (b , ys)
vals-same _ (here refl) (here refl) _ _ = refl
vals-same u (here refl) (there q) zx zy = ⊥-elim (apart-++ u zx (∈-vals q zy))
vals-same u (there p) (here refl) zx zy = ⊥-elim (apart-++ u zy (∈-vals p zx))
vals-same {π = (_ , zs) ∷ _} u (there p) (there q) zx zy = vals-same (unique-++ʳ zs u) p q zx zy

-- one entry's impl nodes are each other's apart
entry-unique : ∀ {π : List (NodeId × List NodeId)} {a xs} → Unique (concatMap proj₂ π) → (a , xs) ∈ π → Unique xs
entry-unique {π = (_ , ys) ∷ _} u (here refl) = unique-++ˡ ys u
entry-unique {π = (_ , ys) ∷ _} u (there e)   = entry-unique (unique-++ʳ ys u) e

-- so a flattener's merge is neither its node nor its cell
merge-apart : ∀ {π : List (NodeId × List NodeId)} {a m′ ks k} → Unique (concatMap proj₂ π) → (a , m′ ∷ ks ∷ k ∷ []) ∈ π
            → (k ≡ m′ → ⊥) × (k ≡ ks → ⊥)
merge-apart u e with entry-unique u e
... | a ∷ b ∷ _ = (λ eq → all-lookup a (there (here refl)) (sym eq)) , (λ eq → all-lookup b (here refl) (sym eq))

-- and a plain node, once
key-same : ∀ {π : List (NodeId × List NodeId)} {a xs ys} → Unique (map proj₁ π) → (a , xs) ∈ π → (a , ys) ∈ π → xs ≡ ys
key-same _ (here refl) (here refl) = refl
key-same (a ∷ _) (here refl) (there q) = ⊥-elim (all-lookup a (∈-map⁺ proj₁ q) refl)
key-same (a ∷ _) (there p) (here refl) = ⊥-elim (all-lookup a (∈-map⁺ proj₁ p) refl)
key-same (_ ∷ u) (there p) (there q) = key-same u p q

-- a merge's count one lower, every other state as it was
lower : ∀ {n} {Γ : Ctx n} → NodeState Γ → NodeState Γ
lower (mergeAll-st l c q d) = mergeAll-st l (pred c) q d
lower x                     = x

-- a merge is neither a cell nor a count, and a fired merge is no pending one
cell≢merge : ∀ {n} {Γ : Ctx n} {u l c q d s} {v : Val Γ s} → just (mergeAll-st {t = u} l c q d) ≡ just (cell-st v) → ⊥
cell≢merge ()

take≢merge : ∀ {n} {Γ : Ctx n} {u l c q d b} → just (mergeAll-st {Γ = Γ} {t = u} l c q d) ≡ just (take-st b) → ⊥
take≢merge ()

fired≢pending : ∀ {n} {Γ : Ctx n} {u u₀ l l₀ c c₀ q q₀} → just (mergeAll-st {Γ = Γ} {t = u} l c q true) ≡ just (mergeAll-st {t = u₀} l₀ c₀ q₀ false) → ⊥
fired≢pending ()

-- an entry pairing one impl node is no entry pairing more
one-many : ∀ {k′ m′ ks : NodeId} {xs} → k′ ∷ [] ≡ m′ ∷ ks ∷ xs → ⊥
one-many ()

solo-many : ∀ {k k′ m m′ ks : NodeId} {xs : List NodeId} → (k , k′ ∷ []) ≡ (m , m′ ∷ ks ∷ xs) → ⊥
solo-many ()

one-two : ∀ {k k′ m m′ ks : NodeId} → (k , k′ ∷ []) ≡ (m , m′ ∷ ks ∷ []) → ⊥
one-two ()

-- one entry, read at its first impl node
head₂ : ∀ {k m x y : NodeId} {xs ys : List NodeId} → (k , x ∷ xs) ≡ (m , y ∷ ys) → x ≡ y
head₂ refl = refl

one≢zero : ∀ {n} {Γ : Ctx n} → just (take-st {Γ = Γ} 1) ≡ just (take-st 0) → ⊥
one≢zero ()

module _ {n} {Γ : Ctx n} (κ : Kinds n) {π : List (NodeId × List NodeId)} where

  -- the pair's new states relate at every element type the old ones did
  retype : ∀ {u u₂ op op₂ x x′ y y′} → FlatNodes {Γ = Γ} κ π u op x x′ → FlatNodes {Γ = Γ} κ π u₂ op₂ x x′
         → FlatNodes {Γ = Γ} κ π u op y y′ → FlatNodes {Γ = Γ} κ π u₂ op₂ y y′
  retype (merge~ _) (merge~ _) (merge~ ps) = merge~ ps
  retype (switch~ _) (switch~ _) (switch~ c) = switch~ c
  retype exhaust~ exhaust~ exhaust~         = exhaust~

  -- no flattener's state is a cell or a count
  cell-flat : ∀ {u op s w} {a : Val Γ s} → FlatNodes {Γ = Γ} κ π u op (cell-st a) w → ⊥
  cell-flat ()

  take-flat : ∀ {u op w b} → FlatNodes {Γ = Γ} κ π u op (take-st b) w → ⊥
  take-flat ()

  cell-flat′ : ∀ {u op v s} {a : Val (plainᵏ Γ κ) s} → FlatNodes {Γ = Γ} κ π u op v (cell-st a) → ⊥
  cell-flat′ ()

  take-flat′ : ∀ {u op v b} → FlatNodes {Γ = Γ} κ π u op v (take-st b) → ⊥
  take-flat′ ()

  -- a fired hop's three merges, counted as a `deferInner~` row reads them
  Fired : List (NodeId × NodeState Γ) → List (NodeId × NodeState (plainᵏ Γ κ)) → Ty → (nid nid′ m2 : NodeId) → Set
  Fired NP NI u nid nid′ m2 = Σ ℕ λ a → Σ ℕ λ b →
      lookupNode nid NP ≡ just (mergeAll-st {t = u} nothing a [] true)
    × lookupNode nid′ NI ≡ just (mergeAll-st {t = emitᵗ u} nothing a [] true)
    × lookupNode m2 NI ≡ just (mergeAll-st {t = emitᵗ u} nothing b [] true) × a ≤ 1 × b ≤ 1

  -- WHAT A NODE MOVE KEEPS: the rows, their partners, their spending
  -- and the arrival's rows, each read at the new nodes
  record Moved {t : Ty} (NP NP′ : List (NodeId × NodeState Γ)) (NI NI′ : List (NodeId × NodeState (plainᵏ Γ κ))) : Set where
    field
      regW   : ∀ {LP LI rs rs′} → RegRel κ π {t} NP NI LP LI rs rs′ → RegRel κ π NP′ NI′ LP LI rs rs′
      partW  : ∀ {LP LI rs rs′} (q : RegRel κ π {t} NP NI LP LI rs rs′) {r r′} → Partners κ π NP NI LP LI q r r′
             → Partners κ π NP′ NI′ LP LI (regW q) r r′
      spentW : ∀ {LP LI rs rs′} (q : RegRel κ π {t} NP NI LP LI rs rs′) {dP dI} → Spent κ π NP NI LP LI q dP dI
             → Spent κ π NP′ NI′ LP LI (regW q) dP dI
      arrW   : ∀ {LP LI rs rs′} (q : RegRel κ π {t} NP NI LP LI rs rs′) {s s′ w w′} → ArrRows κ π NP NI LP LI q s s′ w w′
             → ArrRows κ π NP′ NI′ LP LI (regW q) s s′ w w′

  -- A WRITE KEEPS EVERY ROW WHEN IT KEEPS EVERY NODE FACT A ROW STATES:
  -- a cell, a count, a flattener's pair, a hop's merges pending or
  -- fired, and an impl node no entry pairs
  module Moves {t : Ty} {NP NP′ : List (NodeId × NodeState Γ)} {NI NI′ : List (NodeId × NodeState (plainᵏ Γ κ))}
    (cellP : ∀ {k s} {a : Val Γ s} → lookupNode k NP ≡ just (cell-st a) → lookupNode k NP′ ≡ just (cell-st a))
    (takeP : ∀ {k b} → lookupNode k NP ≡ just (take-st b) → lookupNode k NP′ ≡ just (take-st b))
    (cellS : ∀ {kp k s} {a : Val (plainᵏ Γ κ) s} → (kp , k ∷ []) ∈ π
           → lookupNode k NI ≡ just (cell-st a) → lookupNode k NI′ ≡ just (cell-st a))
    (cellW : ∀ {kp k k₂ s} {a : Val (plainᵏ Γ κ) s} → (kp , k ∷ k₂ ∷ []) ∈ π → lookupNode kp NP ≡ just (take-st 1)
           → lookupNode k NI ≡ just (cell-st a) → lookupNode k NI′ ≡ just (cell-st a))
    (takeI : ∀ {k b} → lookupNode k NI ≡ just (take-st b) → lookupNode k NI′ ≡ just (take-st b))
    (unpairedI : ∀ {k v} → Unpaired {Γ = Γ} κ π k → lookupNode k NI ≡ just v → lookupNode k NI′ ≡ just v)
    (flatW : ∀ {u op m m′ ks xs} → Flattener κ π {t = t} NP NI u op m m′ ks xs → Flattener κ π {t = t} NP′ NI′ u op m m′ ks xs)
    (pendW : ∀ {u k k′} → (k , k′ ∷ []) ∈ π
           → lookupNode k NP ≡ just (mergeAll-st {t = u} nothing 0 [] false)
           → lookupNode k′ NI ≡ just (mergeAll-st {t = emitᵗ u} nothing 0 [] false)
           → lookupNode k NP′ ≡ just (mergeAll-st {t = u} nothing 0 [] false)
             × lookupNode k′ NI′ ≡ just (mergeAll-st {t = emitᵗ u} nothing 0 [] false))
    (hopW : ∀ {u nid nid′ j j′ m2 j2 a b} → (nid , nid′ ∷ []) ∈ π → (j , j′ ∷ m2 ∷ j2 ∷ []) ∈ π
          → lookupNode nid NP ≡ just (mergeAll-st {t = u} nothing a [] true)
          → lookupNode nid′ NI ≡ just (mergeAll-st {t = emitᵗ u} nothing a [] true)
          → lookupNode m2 NI ≡ just (mergeAll-st {t = emitᵗ u} nothing b [] true) → a ≤ 1 → b ≤ 1
          → Fired NP′ NI′ u nid nid′ m2)
    (mergeW : ∀ {u m m′ ks k} → (m , m′ ∷ ks ∷ k ∷ []) ∈ π → MergeAt {Γ = Γ} κ NI u k → MergeAt {Γ = Γ} κ NI′ u k) where

    pathW : ∀ {lo lo′ s} {p : Path Γ lo s t} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t)}
          → PathRel κ π NP NI p q → PathRel κ π NP′ NI′ p q
    pathW root~                              = root~
    pathW (sink~ sh)                         = sink~ sh
    pathW (map~ L r)                         = map~ L (pathW r)
    pathW (scan~ e l l′ v L r)               = scan~ e (cellP l) (cellS e l′) v L (pathW r)
    pathW (takeWhile~ e l l₁ l₂ L r)         = takeWhile~ e (takeP l) (cellW e l l₁) (takeI l₂) L (pathW r)
    pathW (spentWhile~ e l l₂ r)             = spentWhile~ e (takeP l) (takeI l₂) (pathW r)
    pathW (outerElem~ f r)                   = outerElem~ (flatW f) (pathW r)
    pathW (outerExplode~ f x r)              = outerExplode~ (flatW f) (mergeW (proj₁ f) x) (pathW r)
    pathW (inner~ e f ip r)                  = inner~ e (flatW f) ip (pathW r)
    pathW (deferInner~ e₁ e₂ l l′ l₂ a≤ b≤ r) =
      let (_ , _ , x , y , z , p , q) = hopW e₁ e₂ l l′ l₂ a≤ b≤ in deferInner~ e₁ e₂ x y z p q (pathW r)

    blockW : ∀ {a lo ℓ} {full : Path (plainᵏ Γ κ) lo a (emitᵗ t)} {q}
           → InputBlock κ π NP NI a {lo} {ℓ} full q → InputBlock κ π NP′ NI′ a full q
    blockW (block l₁ a≤ lb l₂ u₁ uj ub u₂) = block (unpairedI u₁ l₁) a≤ (unpairedI ub lb) (unpairedI u₂ l₂) u₁ uj ub u₂

    module _ {LP LI} where

      rowW : ∀ {r r′} → RowRel κ π NP NI LP LI r r′ → RowRel κ π NP′ NI′ LP LI r r′
      rowW (read~ hs r eq)          = read~ hs (pathW r) eq
      rowW (cold~ sp b r eq)        = cold~ sp (blockW b) (pathW r) eq
      rowW (defer~ sp e l l′ r eq)  = let (x , y) = pendW e l l′ in defer~ sp e x y (pathW r) eq

      machW : ∀ {r′} → MachRow κ π {t = t} NP NI LP LI r′ → MachRow κ π NP′ NI′ LP LI r′
      machW (hot~ hot b eq) = hot~ hot (blockW b) eq

      regW : ∀ {rs rs′} → RegRel κ π NP NI LP LI rs rs′ → RegRel κ π NP′ NI′ LP LI rs rs′
      regW []         = []
      regW (r ∷ q)    = rowW r ∷ regW q
      regW (mach r q) = mach (machW r) (regW q)

      -- the registries pair the same rows
      partW : ∀ {rs rs′} (q : RegRel κ π NP NI LP LI rs rs′) {r r′} → Partners κ π NP NI LP LI q r r′
            → Partners κ π NP′ NI′ LP LI (regW q) r r′
      partW (_ ∷ q)    (inj₁ e) = inj₁ e
      partW (_ ∷ q)    (inj₂ p) = inj₂ (partW q p)
      partW (mach _ q) p        = partW q p

      -- and spend them alike
      spentW : ∀ {rs rs′} (q : RegRel κ π NP NI LP LI rs rs′) {dP dI} → Spent κ π NP NI LP LI q dP dI
             → Spent κ π NP′ NI′ LP LI (regW q) dP dI
      spentW []         s       = s
      spentW (_ ∷ q)    (e , s) = e , spentW q s
      spentW (mach _ q) s       = spentW q s

      -- and the same minted sources
      arrW : ∀ {rs rs′} (q : RegRel κ π NP NI LP LI rs rs′) {s s′ w w′} → ArrRows κ π NP NI LP LI q s s′ w w′
           → ArrRows κ π NP′ NI′ LP LI (regW q) s s′ w w′
      arrW []                          _       = _
      arrW (read~ _ _ _ ∷ q)           a       = arrW q a
      arrW (cold~ _ _ _ _ ∷ q)         (r , a) = r , arrW q a
      arrW (defer~ _ _ _ _ _ _ ∷ q)    (r , a) = r , arrW q a
      arrW (mach _ q)                  a       = arrW q a

    moved : Moved {t = t} NP NP′ NI NI′
    moved = record { regW = regW ; partW = partW ; spentW = spentW ; arrW = arrW }

  module Write (keys : Unique (map proj₁ π)) (vals : Unique (concatMap proj₂ π)) {t : Ty}
               {NP : List (NodeId × NodeState Γ)} {NI : List (NodeId × NodeState (plainᵏ Γ κ))}
               {u op m m′ ks xs x x′ y y′ c}
               (pm : (m , m′ ∷ ks ∷ xs) ∈ π) (lP : lookupNode m NP ≡ just x) (lI : lookupNode m′ NI ≡ just x′)
               (fn : FlatNodes {Γ = Γ} κ π u op x x′) (lk : lookupNode ks NI ≡ just (cell-st {t = FlatSᵗ u} c))
               (fn′ : FlatNodes {Γ = Γ} κ π u op y y′) where

    NP′ : List (NodeId × NodeState Γ)
    NP′ = setNode m y NP

    NI′ : List (NodeId × NodeState (plainᵏ Γ κ))
    NI′ = setNode m′ y′ NI

    keepP : ∀ {k v} → (k ≡ m → ⊥) → lookupNode k NP ≡ just v → lookupNode k NP′ ≡ just v
    keepP {k} ne l = trans (set-above m k y NP (apart m k ne)) l

    keepI : ∀ {k v} → (k ≡ m′ → ⊥) → lookupNode k NI ≡ just v → lookupNode k NI′ ≡ just v
    keepI {k} ne l = trans (set-above m′ k y′ NI (apart m′ k ne)) l

    -- what sits at the written nodes is the flattener's
    atP : ∀ {v} → lookupNode m NP ≡ just v → FlatNodes {Γ = Γ} κ π u op v x′
    atP l = subst (λ v → FlatNodes {Γ = Γ} κ π u op v x′) (just-injective (trans (sym lP) l)) fn

    atI : ∀ {v} → lookupNode m′ NI ≡ just v → FlatNodes {Γ = Γ} κ π u op x v
    atI l = subst (FlatNodes {Γ = Γ} κ π u op x) (just-injective (trans (sym lI) l)) fn

    cellP : ∀ {k s} {a : Val Γ s} → lookupNode k NP ≡ just (cell-st a) → lookupNode k NP′ ≡ just (cell-st a)
    cellP {k} l with k ≟ m
    ... | yes refl = ⊥-elim (cell-flat (atP l))
    ... | no ne    = keepP ne l

    takeP : ∀ {k b} → lookupNode k NP ≡ just (take-st b) → lookupNode k NP′ ≡ just (take-st b)
    takeP {k} l with k ≟ m
    ... | yes refl = ⊥-elim (take-flat (atP l))
    ... | no ne    = keepP ne l

    cellI : ∀ {k s} {a : Val (plainᵏ Γ κ) s} → lookupNode k NI ≡ just (cell-st a) → lookupNode k NI′ ≡ just (cell-st a)
    cellI {k} l with k ≟ m′
    ... | yes refl = ⊥-elim (cell-flat′ (atI l))
    ... | no ne    = keepI ne l

    takeI : ∀ {k b} → lookupNode k NI ≡ just (take-st b) → lookupNode k NI′ ≡ just (take-st b)
    takeI {k} l with k ≟ m′
    ... | yes refl = ⊥-elim (take-flat′ (atI l))
    ... | no ne    = keepI ne l

    -- the restamp's cell is not the flattener's node
    ks-apart : ks ≡ m′ → ⊥
    ks-apart refl = cell-flat′ (atI lk)

    -- a plain node `π` pairs with one impl node is not the flattener's
    soloP : ∀ {k k′ v} → (k , k′ ∷ []) ∈ π → lookupNode k NP ≡ just v → lookupNode k NP′ ≡ just v
    soloP {k} e l with k ≟ m
    ... | yes refl = ⊥-elim (solo (key-same keys pm e))
      where solo : ∀ {k′} → m′ ∷ ks ∷ xs ≡ k′ ∷ [] → ⊥
            solo ()
    ... | no ne    = keepP ne l

    -- an impl node `π` pairs is the written one only through the flattener's entry
    pairedI : ∀ {k ys z v} → (k , ys) ∈ π → z ∈ ys → ((k , ys) ≡ (m , m′ ∷ ks ∷ xs) → z ≡ m′ → ⊥)
            → lookupNode z NI ≡ just v → lookupNode z NI′ ≡ just v
    pairedI {z = z} e zy other l with z ≟ m′
    ... | yes refl = ⊥-elim (other (vals-same vals e pm zy (here refl)) refl)
    ... | no ne    = keepI ne l

    unpairedI : ∀ {k v} → Unpaired {Γ = Γ} κ π k → lookupNode k NI ≡ just v → lookupNode k NI′ ≡ just v
    unpairedI {k} un l with k ≟ m′
    ... | yes refl = ⊥-elim (un (∈-vals pm (here refl)))
    ... | no ne    = keepI ne l

    solo-entry : ∀ {k k′} → (k , k′ ∷ []) ≡ (m , m′ ∷ ks ∷ xs) → ⊥
    solo-entry ()

    third-entry : ∀ {j j′ k j₂} → (j , j′ ∷ k ∷ j₂ ∷ []) ≡ (m , m′ ∷ ks ∷ xs) → k ≡ m′ → ⊥
    third-entry refl e = ks-apart e

    -- a flattener fact anywhere stays one
    flatW : ∀ {u₂ op₂ m₂ m′₂ ks₂ xs₂} → Flattener κ π {t = t} NP NI u₂ op₂ m₂ m′₂ ks₂ xs₂
          → Flattener κ π {t = t} NP′ NI′ u₂ op₂ m₂ m′₂ ks₂ xs₂
    flatW {u₂ = u₂} {op₂ = op₂} {m₂ = m₂} (pm₂ , x₂ , x₂′ , l₂ , l₂′ , fn₂ , c₂ , lk₂) with m₂ ≟ m
    ... | yes refl with key-same keys pm pm₂
    ...   | refl = pm₂ , y , y′ , lookup-set m y NP , lookup-set m′ y′ NI
                 , retype fn (subst (λ v → FlatNodes {Γ = Γ} κ π u₂ op₂ v x′) (just-injective (trans (sym l₂) lP))
                                    (subst (FlatNodes {Γ = Γ} κ π u₂ op₂ x₂) (just-injective (trans (sym l₂′) lI)) fn₂)) fn′
                 , c₂ , cellI lk₂
    flatW (pm₂ , x₂ , x₂′ , l₂ , l₂′ , fn₂ , c₂ , lk₂) | no ne =
      pm₂ , x₂ , x₂′ , keepP ne l₂ , pairedI pm₂ (here refl) (λ eq _ → ne (cong proj₁ eq)) l₂′ , fn₂ , c₂ , cellI lk₂

    open Moves {t = t} {NP} {NP′} {NI} {NI′} cellP takeP (λ _ → cellI) (λ _ _ → cellI) takeI unpairedI flatW
      (λ e l l′ → soloP e l , pairedI e (here refl) (λ eq _ → solo-entry eq) l′)
      (λ e₁ e₂ l l′ l₂ a≤ b≤ → _ , _ , soloP e₁ l , pairedI e₁ (here refl) (λ eq _ → solo-entry eq) l′
                                , pairedI e₂ (there (here refl)) third-entry l₂ , a≤ , b≤)
      (λ e (od , l) → od
         , pairedI e (there (there (here refl))) (λ eq k≡ → proj₁ (merge-apart vals e) (trans k≡ (sym (head₂ eq)))) l) public

  -- A FIRED HOP'S END WRITTEN: the plain merge and the impl's hop node
  -- one lower together, and the ending inner's marker merge one lower on
  -- its own.  Every other row reads apart from all three: `π` pairs the
  -- hop's nodes with each other alone, and the marker once, so a row of
  -- another inner of the hop names another marker
  module HopWrite (keys : Unique (map proj₁ π)) (vals : Unique (concatMap proj₂ π)) {t : Ty}
                  {NP : List (NodeId × NodeState Γ)} {NI : List (NodeId × NodeState (plainᵏ Γ κ))}
                  {u nid nid′ j j′ m2 j2 a b}
                  (e₁ : (nid , nid′ ∷ []) ∈ π) (e₂ : (j , j′ ∷ m2 ∷ j2 ∷ []) ∈ π)
                  (lP : lookupNode nid NP ≡ just (mergeAll-st {t = u} nothing a [] true))
                  (lI : lookupNode nid′ NI ≡ just (mergeAll-st {t = emitᵗ u} nothing a [] true))
                  (l2 : lookupNode m2 NI ≡ just (mergeAll-st {t = emitᵗ u} nothing b [] true)) where

    yP : NodeState Γ
    yP = mergeAll-st {t = u} nothing (pred a) [] true

    yI y2 : NodeState (plainᵏ Γ κ)
    yI = mergeAll-st {t = emitᵗ u} nothing (pred a) [] true
    y2 = mergeAll-st {t = emitᵗ u} nothing (pred b) [] true

    NP′ : List (NodeId × NodeState Γ)
    NP′ = setNode nid yP NP

    NI₂ NI′ : List (NodeId × NodeState (plainᵏ Γ κ))
    NI₂ = setNode m2 y2 NI
    NI′ = setNode nid′ yI NI₂

    -- an impl node of a one-node entry is no third of a run's
    solo≢third : ∀ {k k′ i i′ m i2} → (k , k′ ∷ []) ∈ π → (i , i′ ∷ m ∷ i2 ∷ []) ∈ π → k′ ≡ m → ⊥
    solo≢third f g e with vals-same vals f g (here refl) (there (here e))
    ... | ()

    -- and names its own plain node
    hop-key : ∀ {k k′} → (k , k′ ∷ []) ∈ π → k′ ≡ nid′ → k ≡ nid
    hop-key f e = cong proj₁ (vals-same vals f e₁ (here refl) (here e))

    keepP : ∀ {k v} → (k ≡ nid → ⊥) → lookupNode k NP ≡ just v → lookupNode k NP′ ≡ just v
    keepP {k} ne l = trans (set-above nid k yP NP (apart nid k ne)) l

    keepI : ∀ {k v} → (k ≡ nid′ → ⊥) → (k ≡ m2 → ⊥) → lookupNode k NI ≡ just v → lookupNode k NI′ ≡ just v
    keepI {k} n₁ n₂ l = trans (set-above nid′ k yI NI₂ (apart nid′ k n₁)) (trans (set-above m2 k y2 NI (apart m2 k n₂)) l)

    cellP : ∀ {k s} {c : Val Γ s} → lookupNode k NP ≡ just (cell-st c) → lookupNode k NP′ ≡ just (cell-st c)
    cellP {k} l with k ≟ nid
    ... | yes refl = ⊥-elim (cell≢merge (trans (sym lP) l))
    ... | no ne    = keepP ne l

    takeP : ∀ {k c} → lookupNode k NP ≡ just (take-st c) → lookupNode k NP′ ≡ just (take-st c)
    takeP {k} l with k ≟ nid
    ... | yes refl = ⊥-elim (take≢merge (trans (sym lP) l))
    ... | no ne    = keepP ne l

    cellI : ∀ {k s} {c : Val (plainᵏ Γ κ) s} → lookupNode k NI ≡ just (cell-st c) → lookupNode k NI′ ≡ just (cell-st c)
    cellI {k} l with k ≟ nid′ | k ≟ m2
    ... | yes refl | _        = ⊥-elim (cell≢merge (trans (sym lI) l))
    ... | no _     | yes refl = ⊥-elim (cell≢merge (trans (sym l2) l))
    ... | no n₁    | no n₂    = keepI n₁ n₂ l

    takeI : ∀ {k c} → lookupNode k NI ≡ just (take-st c) → lookupNode k NI′ ≡ just (take-st c)
    takeI {k} l with k ≟ nid′ | k ≟ m2
    ... | yes refl | _        = ⊥-elim (take≢merge (trans (sym lI) l))
    ... | no _     | yes refl = ⊥-elim (take≢merge (trans (sym l2) l))
    ... | no n₁    | no n₂    = keepI n₁ n₂ l

    unpairedI : ∀ {k v} → Unpaired {Γ = Γ} κ π k → lookupNode k NI ≡ just v → lookupNode k NI′ ≡ just v
    unpairedI {k} un l with k ≟ nid′ | k ≟ m2
    ... | yes refl | _        = ⊥-elim (un (∈-vals e₁ (here refl)))
    ... | no _     | yes refl = ⊥-elim (un (∈-vals e₂ (there (here refl))))
    ... | no n₁    | no n₂    = keepI n₁ n₂ l

    -- a flattener's entry pairs a run, so neither of the hop's
    flatW : ∀ {u₀ op m m′ ks xs} → Flattener κ π {t = t} NP NI u₀ op m m′ ks xs → Flattener κ π {t = t} NP′ NI′ u₀ op m m′ ks xs
    flatW {m = m} {m′} {ks} {xs} (pm , x , x′ , l , l′ , fn , c , lk) =
      pm , x , x′ , keepP nP l , keepI n₁ n₂ l′ , fn , c , cellI lk
      where
      nP : m ≡ nid → ⊥
      nP refl = one-many (key-same keys e₁ pm)
      n₁ : m′ ≡ nid′ → ⊥
      n₁ refl = solo-many (vals-same vals e₁ pm (here refl) (here refl))
      third : ∀ {i i′ i2} → (i , i′ ∷ m2 ∷ i2 ∷ []) ≡ (m , m′ ∷ ks ∷ xs) → ks ≡ m2
      third refl = refl
      n₂ : m′ ≡ m2 → ⊥
      n₂ refl = cell≢merge (trans (sym l2) (subst (λ k → lookupNode k NI ≡ _) (third (vals-same vals e₂ pm (there (here refl)) (here refl))) lk))

    pendW : ∀ {u₀ k k′} → (k , k′ ∷ []) ∈ π
          → lookupNode k NP ≡ just (mergeAll-st {t = u₀} nothing 0 [] false)
          → lookupNode k′ NI ≡ just (mergeAll-st {t = emitᵗ u₀} nothing 0 [] false)
          → lookupNode k NP′ ≡ just (mergeAll-st {t = u₀} nothing 0 [] false)
            × lookupNode k′ NI′ ≡ just (mergeAll-st {t = emitᵗ u₀} nothing 0 [] false)
    pendW {k = k} f l l′ with k ≟ nid
    ... | yes refl = ⊥-elim (fired≢pending (trans (sym lP) l))
    ... | no ne    = keepP ne l , keepI (λ e → ne (hop-key f e)) (solo≢third f e₂) l′

    -- the hop's pair, written or apart
    pairW : ∀ {u₀ k k′ a₀} → (k , k′ ∷ []) ∈ π
          → lookupNode k NP ≡ just (mergeAll-st {t = u₀} nothing a₀ [] true)
          → lookupNode k′ NI ≡ just (mergeAll-st {t = emitᵗ u₀} nothing a₀ [] true) → a₀ ≤ 1
          → Σ ℕ λ a′ → lookupNode k NP′ ≡ just (mergeAll-st {t = u₀} nothing a′ [] true)
                     × lookupNode k′ NI′ ≡ just (mergeAll-st {t = emitᵗ u₀} nothing a′ [] true) × a′ ≤ 1
    pairW {k = k} {a₀ = a₀} f l l′ a≤ with k ≟ nid
    ... | no ne = a₀ , keepP ne l , keepI (λ e → ne (hop-key f e)) (solo≢third f e₂) l′ , a≤
    ... | yes refl with key-same keys e₁ f
    ...   | refl = pred a₀ , trans (lookup-set nid yP NP) (cong (λ x → just (lower x)) (just-injective (trans (sym lP) l)))
                 , trans (lookup-set nid′ yI NI₂) (cong (λ x → just (lower x)) (just-injective (trans (sym lI) l′)))
                 , ≤-trans pred[n]≤n a≤

    -- a marker, written or apart
    markW : ∀ {u₀ i i′ m i2 b₀} → (i , i′ ∷ m ∷ i2 ∷ []) ∈ π
          → lookupNode m NI ≡ just (mergeAll-st {t = emitᵗ u₀} nothing b₀ [] true) → b₀ ≤ 1
          → Σ ℕ λ b′ → lookupNode m NI′ ≡ just (mergeAll-st {t = emitᵗ u₀} nothing b′ [] true) × b′ ≤ 1
    markW {m = m} {b₀ = b₀} f l b≤ with m ≟ m2
    ... | no ne    = b₀ , keepI (λ e → solo≢third e₁ f (sym e)) ne l , b≤
    ... | yes refl = pred b₀
                   , trans (set-above nid′ m2 yI NI₂ (apart nid′ m2 (λ e → solo≢third e₁ e₂ (sym e))))
                       (trans (lookup-set m2 y2 NI) (cong (λ x → just (lower x)) (just-injective (trans (sym l2) l))))
                   , ≤-trans pred[n]≤n b≤

    hopW : ∀ {u₀ k k′ i i′ m i2 a₀ b₀} → (k , k′ ∷ []) ∈ π → (i , i′ ∷ m ∷ i2 ∷ []) ∈ π
         → lookupNode k NP ≡ just (mergeAll-st {t = u₀} nothing a₀ [] true)
         → lookupNode k′ NI ≡ just (mergeAll-st {t = emitᵗ u₀} nothing a₀ [] true)
         → lookupNode m NI ≡ just (mergeAll-st {t = emitᵗ u₀} nothing b₀ [] true) → a₀ ≤ 1 → b₀ ≤ 1
         → Fired NP′ NI′ u₀ k k′ m
    hopW f g l l′ l₂ a≤ b≤ =
      let (a′ , x , y , p) = pairW f l l′ a≤ ; (b′ , z , q) = markW g l₂ b≤ in a′ , b′ , x , y , z , p , q

    -- an explode's merge is neither the hop's node nor its marker
    third₂ : ∀ {i i′ z i2 k k′ ks₀ k₀ : NodeId} → (i , i′ ∷ z ∷ i2 ∷ []) ≡ (k , k′ ∷ ks₀ ∷ k₀ ∷ []) → z ≡ ks₀
    third₂ refl = refl

    mergeW : ∀ {u₀ k k′ ks₀ k₀} → (k , k′ ∷ ks₀ ∷ k₀ ∷ []) ∈ π → MergeAt {Γ = Γ} κ NI u₀ k₀ → MergeAt {Γ = Γ} κ NI′ u₀ k₀
    mergeW {k₀ = k₀} f (od , l) = od , keepI n₁ n₂ l
      where
      n₁ : k₀ ≡ nid′ → ⊥
      n₁ eq = solo-many (vals-same vals e₁ f (here refl) (there (there (here (sym eq)))))
      n₂ : k₀ ≡ m2 → ⊥
      n₂ eq = proj₂ (merge-apart vals f) (trans eq (third₂ (vals-same vals e₂ f (there (here refl)) (there (there (here (sym eq)))))))

    module M = Moves {t = t} {NP} {NP′} {NI} {NI′} cellP takeP (λ _ → cellI) (λ _ _ → cellI) takeI unpairedI flatW pendW hopW mergeW

  -- AN IMPL CELL WRITTEN UNDER A SPENT TEST, ON THE IMPL SIDE ALONE.
  -- `π` pairs the cell once, in the test's entry, and a row reading a
  -- cell there is an open test, whose plain count is one where this
  -- one's is zero; a cell is no count, merge or flattener's state, and
  -- a flattener's restamp cell is the second of its own entry
  module CellWrite (vals : Unique (concatMap proj₂ π)) {t : Ty}
                   {NP : List (NodeId × NodeState Γ)} {NI : List (NodeId × NodeState (plainᵏ Γ κ))}
                   {k k₁ k₂ w} {a c : Val (plainᵏ Γ κ) w}
                   (e : (k , k₁ ∷ k₂ ∷ []) ∈ π) (lP : lookupNode k NP ≡ just (take-st 0))
                   (l₁ : lookupNode k₁ NI ≡ just (cell-st a)) where

    NI′ : List (NodeId × NodeState (plainᵏ Γ κ))
    NI′ = setNode k₁ (cell-st c) NI

    keepI : ∀ {j v} → (j ≡ k₁ → ⊥) → lookupNode j NI ≡ just v → lookupNode j NI′ ≡ just v
    keepI {j} ne l = trans (set-above k₁ j (cell-st c) NI (apart k₁ j ne)) l

    -- what sits at the written node is the cell
    at : ∀ {v} → lookupNode k₁ NI ≡ just v → cell-st a ≡ v
    at l = just-injective (trans (sym l₁) l)

    cellS : ∀ {kp j s} {b : Val (plainᵏ Γ κ) s} → (kp , j ∷ []) ∈ π
          → lookupNode j NI ≡ just (cell-st b) → lookupNode j NI′ ≡ just (cell-st b)
    cellS {j = j} f l with j ≟ k₁
    ... | yes refl = ⊥-elim (one-two (vals-same vals f e (here refl) (here refl)))
    ... | no ne    = keepI ne l

    cellW : ∀ {kp j j₂ s} {b : Val (plainᵏ Γ κ) s} → (kp , j ∷ j₂ ∷ []) ∈ π → lookupNode kp NP ≡ just (take-st 1)
          → lookupNode j NI ≡ just (cell-st b) → lookupNode j NI′ ≡ just (cell-st b)
    cellW {j = j} f l1 l with j ≟ k₁
    ... | yes refl = ⊥-elim (one≢zero (trans (sym l1) (subst (λ x → lookupNode x NP ≡ just (take-st 0))
                                                               (sym (cong proj₁ (vals-same vals f e (here refl) (here refl)))) lP)))
    ... | no ne    = keepI ne l

    takeI : ∀ {j b} → lookupNode j NI ≡ just (take-st b) → lookupNode j NI′ ≡ just (take-st b)
    takeI {j} l with j ≟ k₁
    ... | no ne    = keepI ne l
    ... | yes refl with at l
    ...   | ()

    unpairedI : ∀ {j v} → Unpaired {Γ = Γ} κ π j → lookupNode j NI ≡ just v → lookupNode j NI′ ≡ just v
    unpairedI {j} un l with j ≟ k₁
    ... | yes refl = ⊥-elim (un (∈-vals e (here refl)))
    ... | no ne    = keepI ne l

    -- a merge's node is not the cell
    apartM : ∀ {j u₀ l₀ c₀ q₀ d₀} → lookupNode j NI ≡ just (mergeAll-st {t = u₀} l₀ c₀ q₀ d₀) → j ≡ k₁ → ⊥
    apartM l refl with at l
    ... | ()

    flatW : ∀ {u₀ op m m′ ks xs} → Flattener κ π {t = t} NP NI u₀ op m m′ ks xs → Flattener κ π {t = t} NP NI′ u₀ op m m′ ks xs
    flatW {u₀ = u₀} {op} {m} {m′} {ks} {xs} (pm , x , x′ , l , l′ , fn , c₂ , lk) =
      pm , x , x′ , l , keepI n₁ l′ , fn , c₂ , keepI n₂ lk
      where
      n₁ : m′ ≡ k₁ → ⊥
      n₁ refl = cell-flat′ (subst (FlatNodes {Γ = Γ} κ π u₀ op x) (sym (at l′)) fn)
      n₂ : ks ≡ k₁ → ⊥
      n₂ refl = n₁ (head₂ (vals-same vals pm e (there (here refl)) (here refl)))

    pendW : ∀ {u₀ j j′} → (j , j′ ∷ []) ∈ π
          → lookupNode j NP ≡ just (mergeAll-st {t = u₀} nothing 0 [] false)
          → lookupNode j′ NI ≡ just (mergeAll-st {t = emitᵗ u₀} nothing 0 [] false)
          → lookupNode j NP ≡ just (mergeAll-st {t = u₀} nothing 0 [] false)
            × lookupNode j′ NI′ ≡ just (mergeAll-st {t = emitᵗ u₀} nothing 0 [] false)
    pendW _ l l′ = l , keepI (apartM l′) l′

    hopW : ∀ {u₀ j j′ i i′ m i2 a₀ b₀} → (j , j′ ∷ []) ∈ π → (i , i′ ∷ m ∷ i2 ∷ []) ∈ π
         → lookupNode j NP ≡ just (mergeAll-st {t = u₀} nothing a₀ [] true)
         → lookupNode j′ NI ≡ just (mergeAll-st {t = emitᵗ u₀} nothing a₀ [] true)
         → lookupNode m NI ≡ just (mergeAll-st {t = emitᵗ u₀} nothing b₀ [] true) → a₀ ≤ 1 → b₀ ≤ 1
         → Fired NP NI′ u₀ j j′ m
    hopW _ _ l l′ l₂ a≤ b≤ = _ , _ , l , keepI (apartM l′) l′ , keepI (apartM l₂) l₂ , a≤ , b≤

    module M = Moves {t = t} {NP} {NP} {NI} {NI′} (λ l → l) (λ l → l) cellS cellW takeI unpairedI flatW pendW hopW
                     (λ _ (od , l) → od , keepI (apartM l) l)

  -- the type a cell holds is the one its lookup says
  cell-ty : ∀ {w w₂} {a : Val (plainᵏ Γ κ) w} {b : Val (plainᵏ Γ κ) w₂} → just (cell-st {t = w} a) ≡ just (cell-st {t = w₂} b) → w ≡ w₂
  cell-ty refl = refl

  cell-subst : ∀ {w w₂} (e : w ≡ w₂) (a : Val (plainᵏ Γ κ) w) → cell-st {t = w} a ≡ cell-st {t = w₂} (subst (Val (plainᵏ Γ κ)) e a)
  cell-subst refl a = refl

  -- A FLATTENER'S RESTAMP CELL WRITTEN, ON THE IMPL SIDE ALONE.  `π`
  -- pairs the cell once, second in the flattener's own entry, so no
  -- scan's, test's or other flattener's row names it, and a row naming
  -- it as its restamp cell reads the new one at the type it already
  -- held there
  module FlatCellWrite (vals : Unique (concatMap proj₂ π)) {t : Ty}
                       {NP : List (NodeId × NodeState Γ)} {NI : List (NodeId × NodeState (plainᵏ Γ κ))}
                       {u op m m′ ks xs x x′} {c : Val (plainᵏ Γ κ) (FlatSᵗ u)}
                       (pm : (m , m′ ∷ ks ∷ xs) ∈ π) (lI : lookupNode m′ NI ≡ just x′)
                       (fn : FlatNodes {Γ = Γ} κ π u op x x′) (lk : lookupNode ks NI ≡ just (cell-st {t = FlatSᵗ u} c))
                       (c′ : Val (plainᵏ Γ κ) (FlatSᵗ u)) where

    NI′ : List (NodeId × NodeState (plainᵏ Γ κ))
    NI′ = setNode ks (cell-st {t = FlatSᵗ u} c′) NI

    keepI : ∀ {j v} → (j ≡ ks → ⊥) → lookupNode j NI ≡ just v → lookupNode j NI′ ≡ just v
    keepI {j} ne l = trans (set-above ks j (cell-st {t = FlatSᵗ u} c′) NI (apart ks j ne)) l

    at : ∀ {v} → lookupNode ks NI ≡ just v → cell-st {t = FlatSᵗ u} c ≡ v
    at l = just-injective (trans (sym lk) l)

    -- the cell is not the flattener's own impl node
    ksm : ks ≡ m′ → ⊥
    ksm refl = cell-flat′ (subst (FlatNodes {Γ = Γ} κ π u op x) (sym (at lI)) fn)

    cellS : ∀ {kp j s} {b : Val (plainᵏ Γ κ) s} → (kp , j ∷ []) ∈ π
          → lookupNode j NI ≡ just (cell-st b) → lookupNode j NI′ ≡ just (cell-st b)
    cellS {j = j} f l with j ≟ ks
    ... | yes refl = ⊥-elim (solo-many (vals-same vals f pm (here refl) (there (here refl))))
    ... | no ne    = keepI ne l

    cellW : ∀ {kp j j₂ s} {b : Val (plainᵏ Γ κ) s} → (kp , j ∷ j₂ ∷ []) ∈ π → lookupNode kp NP ≡ just (take-st 1)
          → lookupNode j NI ≡ just (cell-st b) → lookupNode j NI′ ≡ just (cell-st b)
    cellW {j = j} f _ l with j ≟ ks
    ... | yes refl = ⊥-elim (ksm (head₂ (vals-same vals f pm (here refl) (there (here refl)))))
    ... | no ne    = keepI ne l

    takeI : ∀ {j b} → lookupNode j NI ≡ just (take-st b) → lookupNode j NI′ ≡ just (take-st b)
    takeI {j} l with j ≟ ks
    ... | no ne    = keepI ne l
    ... | yes refl with at l
    ...   | ()

    unpairedI : ∀ {j v} → Unpaired {Γ = Γ} κ π j → lookupNode j NI ≡ just v → lookupNode j NI′ ≡ just v
    unpairedI {j} un l with j ≟ ks
    ... | yes refl = ⊥-elim (un (∈-vals pm (there (here refl))))
    ... | no ne    = keepI ne l

    apartM : ∀ {j u₀ l₀ c₀ q₀ d₀} → lookupNode j NI ≡ just (mergeAll-st {t = u₀} l₀ c₀ q₀ d₀) → j ≡ ks → ⊥
    apartM l refl with at l
    ... | ()

    -- a restamp cell read back, the new one where it was written
    cellK : ∀ {w} {b : Val (plainᵏ Γ κ) w} {j} → lookupNode j NI ≡ just (cell-st {t = w} b)
          → Σ (Val (plainᵏ Γ κ) w) λ b′ → lookupNode j NI′ ≡ just (cell-st {t = w} b′)
    cellK {j = j} l with j ≟ ks
    ... | no ne    = _ , keepI ne l
    ... | yes refl = let e = cell-ty (trans (sym lk) l) in
      subst (Val (plainᵏ Γ κ)) e c′ , trans (lookup-set ks (cell-st {t = FlatSᵗ u} c′) NI) (cong just (cell-subst e c′))

    flatW : ∀ {u₀ op m m′ ks xs} → Flattener κ π {t = t} NP NI u₀ op m m′ ks xs → Flattener κ π {t = t} NP NI′ u₀ op m m′ ks xs
    flatW {m′ = m₂′} (pm₂ , y , y′ , l , l′ , fn₂ , c₂ , lk₂) = pm₂ , y , y′ , l , keepI n₁ l′ , fn₂ , cellK lk₂
      where
      n₁ : m₂′ ≡ ks → ⊥
      n₁ refl = ksm (head₂ (vals-same vals pm₂ pm (here refl) (there (here refl))))

    pendW : ∀ {u₀ j j′} → (j , j′ ∷ []) ∈ π
          → lookupNode j NP ≡ just (mergeAll-st {t = u₀} nothing 0 [] false)
          → lookupNode j′ NI ≡ just (mergeAll-st {t = emitᵗ u₀} nothing 0 [] false)
          → lookupNode j NP ≡ just (mergeAll-st {t = u₀} nothing 0 [] false)
            × lookupNode j′ NI′ ≡ just (mergeAll-st {t = emitᵗ u₀} nothing 0 [] false)
    pendW _ l l′ = l , keepI (apartM l′) l′

    hopW : ∀ {u₀ j j′ i i′ m i2 a₀ b₀} → (j , j′ ∷ []) ∈ π → (i , i′ ∷ m ∷ i2 ∷ []) ∈ π
         → lookupNode j NP ≡ just (mergeAll-st {t = u₀} nothing a₀ [] true)
         → lookupNode j′ NI ≡ just (mergeAll-st {t = emitᵗ u₀} nothing a₀ [] true)
         → lookupNode m NI ≡ just (mergeAll-st {t = emitᵗ u₀} nothing b₀ [] true) → a₀ ≤ 1 → b₀ ≤ 1
         → Fired NP NI′ u₀ j j′ m
    hopW _ _ l l′ l₂ a≤ b≤ = _ , _ , l , keepI (apartM l′) l′ , keepI (apartM l₂) l₂ , a≤ , b≤

    module M = Moves {t = t} {NP} {NP} {NI} {NI′} (λ l → l) (λ l → l) cellS cellW takeI unpairedI flatW pendW hopW
                     (λ _ (od , l) → od , keepI (apartM l) l)

  -- the type a merge holds is the one its lookup says
  merge-ty : ∀ {w w₂ l l₂ c c₂ q q₂ d d₂}
           → just (mergeAll-st {Γ = plainᵏ Γ κ} {t = w} l c q d) ≡ just (mergeAll-st {t = w₂} l₂ c₂ q₂ d₂) → w ≡ w₂
  merge-ty refl = refl

  -- AN EXPLODE'S MERGE TOLD ITS OUTER IS DONE, ON THE IMPL SIDE ALONE.
  -- `π` pairs the merge once, last in the explode's own entry, so no
  -- cell, count, hop or other flattener's row names it, and the only
  -- merge fact at it is the explode's own, which the write keeps idle
  module MergeDone (vals : Unique (concatMap proj₂ π)) {t : Ty}
                   {NP : List (NodeId × NodeState Γ)} {NI : List (NodeId × NodeState (plainᵏ Γ κ))}
                   {u m m′ ks mX od} (pm : (m , m′ ∷ ks ∷ mX ∷ []) ∈ π)
                   (lX : lookupNode mX NI ≡ just (mergeAll-st {t = echoᵗ (emitᵗ u)} nothing 0 [] od)) where

    NI′ : List (NodeId × NodeState (plainᵏ Γ κ))
    NI′ = setNode mX (mergeAll-st {t = echoᵗ (emitᵗ u)} nothing 0 [] true) NI

    keepI : ∀ {j v} → (j ≡ mX → ⊥) → lookupNode j NI ≡ just v → lookupNode j NI′ ≡ just v
    keepI {j} ne l = trans (set-above mX j (mergeAll-st {t = echoᵗ (emitᵗ u)} nothing 0 [] true) NI (apart mX j ne)) l

    cellI : ∀ {j s} {b : Val (plainᵏ Γ κ) s} → lookupNode j NI ≡ just (cell-st b) → lookupNode j NI′ ≡ just (cell-st b)
    cellI {j} l with j ≟ mX
    ... | yes refl = ⊥-elim (cell≢merge (trans (sym lX) l))
    ... | no ne    = keepI ne l

    takeI : ∀ {j b} → lookupNode j NI ≡ just (take-st b) → lookupNode j NI′ ≡ just (take-st b)
    takeI {j} l with j ≟ mX
    ... | yes refl = ⊥-elim (take≢merge (trans (sym lX) l))
    ... | no ne    = keepI ne l

    unpairedI : ∀ {j v} → Unpaired {Γ = Γ} κ π j → lookupNode j NI ≡ just v → lookupNode j NI′ ≡ just v
    unpairedI {j} un l with j ≟ mX
    ... | yes refl = ⊥-elim (un (∈-vals pm (there (there (here refl)))))
    ... | no ne    = keepI ne l

    third₃ : ∀ {i i′ z i2} → (i , i′ ∷ z ∷ i2 ∷ []) ≡ (m , m′ ∷ ks ∷ mX ∷ []) → z ≡ ks
    third₃ refl = refl

    -- a solo entry's impl node is not the merge
    soloX : ∀ {k k′} → (k , k′ ∷ []) ∈ π → k′ ≡ mX → ⊥
    soloX e refl = solo-many (vals-same vals e pm (here refl) (there (there (here refl))))

    flatW : ∀ {u₀ op₀ m₀ m₀′ ks₀ xs₀} → Flattener κ π {t = t} NP NI u₀ op₀ m₀ m₀′ ks₀ xs₀ → Flattener κ π {t = t} NP NI′ u₀ op₀ m₀ m₀′ ks₀ xs₀
    flatW {m₀′ = m₂′} (pm₂ , y , y′ , l , l′ , fn₂ , c₂ , lk₂) = pm₂ , y , y′ , l , keepI n₁ l′ , fn₂ , c₂ , cellI lk₂
      where
      n₁ : m₂′ ≡ mX → ⊥
      n₁ refl = proj₁ (merge-apart vals pm) (head₂ (vals-same vals pm₂ pm (here refl) (there (there (here refl)))))

    pendW : ∀ {u₀ j j′} → (j , j′ ∷ []) ∈ π
          → lookupNode j NP ≡ just (mergeAll-st {t = u₀} nothing 0 [] false)
          → lookupNode j′ NI ≡ just (mergeAll-st {t = emitᵗ u₀} nothing 0 [] false)
          → lookupNode j NP ≡ just (mergeAll-st {t = u₀} nothing 0 [] false)
            × lookupNode j′ NI′ ≡ just (mergeAll-st {t = emitᵗ u₀} nothing 0 [] false)
    pendW e l l′ = l , keepI (soloX e) l′

    hopW : ∀ {u₀ j j′ i i′ m₂ i2 a₀ b₀} → (j , j′ ∷ []) ∈ π → (i , i′ ∷ m₂ ∷ i2 ∷ []) ∈ π
         → lookupNode j NP ≡ just (mergeAll-st {t = u₀} nothing a₀ [] true)
         → lookupNode j′ NI ≡ just (mergeAll-st {t = emitᵗ u₀} nothing a₀ [] true)
         → lookupNode m₂ NI ≡ just (mergeAll-st {t = emitᵗ u₀} nothing b₀ [] true) → a₀ ≤ 1 → b₀ ≤ 1
         → Fired NP NI′ u₀ j j′ m₂
    hopW {m₂ = m₂} e₁ e₂ l l′ l₂ a≤ b≤ = _ , _ , l , keepI (soloX e₁) l′ , keepI n₂ l₂ , a≤ , b≤
      where
      n₂ : m₂ ≡ mX → ⊥
      n₂ refl = proj₂ (merge-apart vals pm) (third₃ (vals-same vals e₂ pm (there (here refl)) (there (there (here refl)))))

    -- every explode's merge kept, this one marked done and still idle
    mergeW : ∀ {u₀ k k′ ks₀ k₀} → (k , k′ ∷ ks₀ ∷ k₀ ∷ []) ∈ π → MergeAt {Γ = Γ} κ NI u₀ k₀ → MergeAt {Γ = Γ} κ NI′ u₀ k₀
    mergeW {k₀ = k₀} _ (od₀ , l) with k₀ ≟ mX
    ... | no ne    = od₀ , keepI ne l
    ... | yes refl = true , trans (lookup-set mX (mergeAll-st {t = echoᵗ (emitᵗ u)} nothing 0 [] true) NI)
                                  (cong (λ w → just (mergeAll-st {Γ = plainᵏ Γ κ} {t = w} nothing 0 [] true)) (merge-ty (trans (sym lX) l)))

    -- and the explode's own, at the write
    mergeX : MergeAt {Γ = Γ} κ NI′ u mX
    mergeX = true , lookup-set mX (mergeAll-st {t = echoᵗ (emitᵗ u)} nothing 0 [] true) NI

    module M = Moves {t = t} {NP} {NP} {NI} {NI′} (λ l → l) (λ l → l) (λ _ → cellI) (λ _ _ → cellI) takeI unpairedI flatW pendW hopW mergeW
