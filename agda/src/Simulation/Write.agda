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
open import Data.List.Relation.Unary.AllPairs using (_∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Maybe   using (just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat     using (_≡ᵇ_; _≟_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum     using (inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Decide       using (≡ᵇ→≡)
open import Rx.Exp       using (Ty; Ctx; Val)
open import Rx.Evaluator using (NodeId; NodeState; Path; cell-st; take-st; lookupNode; setNode)
open import Rx.Evaluator.Freshness using (lookup-set; set-above)
open import SExp.Syntax  using (Kinds; plainᵏ; emitᵗ)
open import SExp.Elaborate using (FlatSᵗ)
open import Simulation.Stores using (Unpaired; FlatNodes; merge~; switch~; exhaust~; Flattener; PathRel; root~; sink~; map~; scan~;
  take~; takeWhile~; outerElem~; outerExplode~; inner~; lane~; deferInner~; InputBlock; block; RowRel; read~; cold~; defer~;
  MachRow; hot~; RegRel; []; _∷_; mach; Partners; ArrRows)

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

-- and a plain node, once
key-same : ∀ {π : List (NodeId × List NodeId)} {a xs ys} → Unique (map proj₁ π) → (a , xs) ∈ π → (a , ys) ∈ π → xs ≡ ys
key-same _ (here refl) (here refl) = refl
key-same (a ∷ _) (here refl) (there q) = ⊥-elim (all-lookup a (∈-map⁺ proj₁ q) refl)
key-same (a ∷ _) (there p) (here refl) = ⊥-elim (all-lookup a (∈-map⁺ proj₁ p) refl)
key-same (_ ∷ u) (there p) (there q) = key-same u p q

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

    take-entry : ∀ {k ys b} → (k , ys) ≡ (m , m′ ∷ ks ∷ xs) → lookupNode k NP ≡ just (take-st b) → ⊥
    take-entry refl l = take-flat (atP l)

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

    pathW : ∀ {lo lo′ s} {p : Path Γ lo s t} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t)}
          → PathRel κ π NP NI p q → PathRel κ π NP′ NI′ p q
    pathW root~                              = root~
    pathW (sink~ sh)                         = sink~ sh
    pathW (map~ L r)                         = map~ L (pathW r)
    pathW (scan~ e l l′ v L r)               = scan~ e (cellP l) (cellI l′) v L (pathW r)
    pathW (take~ e l l₁ l₂ lm a≤ b≡ L r)     =
      take~ e (takeP l) (cellI l₁) (takeI l₂) (pairedI e (there (there (here refl))) (λ eq _ → take-entry eq l) lm)
            a≤ b≡ L (pathW r)
    pathW (takeWhile~ e l l₁ l₂ L r)         = takeWhile~ e (takeP l) (cellI l₁) (takeI l₂) L (pathW r)
    pathW (outerElem~ f r)                   = outerElem~ (flatW f) (pathW r)
    pathW (outerExplode~ f r)                = outerExplode~ (flatW f) (pathW r)
    pathW (inner~ e f ip r)                  = inner~ e (flatW f) ip (pathW r)
    pathW (lane~ l un uj r)                  = lane~ (unpairedI un l) un uj (pathW r)
    pathW (deferInner~ e₁ e₂ l l′ l₂ a≤ r)   =
      deferInner~ e₁ e₂ (soloP e₁ l) (pairedI e₁ (here refl) (λ eq _ → solo-entry eq) l′)
                  (pairedI e₂ (there (here refl)) third-entry l₂) a≤ (pathW r)

    blockW : ∀ {a lo ℓ} {full : Path (plainᵏ Γ κ) lo a (emitᵗ t)} {q}
           → InputBlock κ π NP NI a {lo} {ℓ} full q → InputBlock κ π NP′ NI′ a full q
    blockW (block l₁ a≤ lb l₂ u₁ uj ub u₂) = block (unpairedI u₁ l₁) a≤ (unpairedI ub lb) (unpairedI u₂ l₂) u₁ uj ub u₂

    module _ {LP LI} where

      rowW : ∀ {r r′} → RowRel κ π NP NI LP LI r r′ → RowRel κ π NP′ NI′ LP LI r r′
      rowW (read~ hs r eq)          = read~ hs (pathW r) eq
      rowW (cold~ sp b r eq)        = cold~ sp (blockW b) (pathW r) eq
      rowW (defer~ sp e l l′ r eq)  = defer~ sp e (soloP e l) (pairedI e (here refl) (λ eq _ → solo-entry eq) l′) (pathW r) eq

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

      -- and the same minted sources
      arrW : ∀ {rs rs′} (q : RegRel κ π NP NI LP LI rs rs′) {s s′ w w′} → ArrRows κ π NP NI LP LI q s s′ w w′
           → ArrRows κ π NP′ NI′ LP LI (regW q) s s′ w w′
      arrW []                          _       = _
      arrW (read~ _ _ _ ∷ q)           a       = arrW q a
      arrW (cold~ _ _ _ _ ∷ q)         (r , a) = r , arrW q a
      arrW (defer~ _ _ _ _ _ _ ∷ q)    (r , a) = r , arrW q a
      arrW (mach _ q)                  a       = arrW q a
