------------------------------------------------------------------
-- `π` GROWN, AND THE ROWS STILL RELATED.  Every pairing a relation
-- states is a membership in `π`, kept by any larger `π′`, except an
-- impl-only node's `Unpaired`, which a new pairing could break; it is
-- kept wherever the path naming the node keeps it, and a node below
-- the counter keeps it against a pair the counter hands out.
------------------------------------------------------------------
module Simulation.Grow where

open import Data.Bool    using (T)
open import Data.Bool.ListAction using (any)
open import Data.List    using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; head; tail; tabulate)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat     using (_<_; _≡ᵇ_)
open import Data.Nat.Properties using (≡⇒≡ᵇ; <-irrefl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum     using (inj₁; inj₂)
open import Data.Unit    using (⊤; tt)
open import Data.Maybe   using (just; nothing)
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Exp       using (Ctx; Ty)
open import Rx.Evaluator using (NodeId; NodeState; Path; root; share-sink; _↠[_]_; frameNodes; pathHasNode; RegRow)
open import Rx.Evaluator.Reducible.Support using (rowThrough; ∨-Tˡ; ∨-Tʳ)
open import SExp.Syntax  using (Kinds; plainᵏ; emitᵗ)
open import Simulation.Stores using (Unpaired; CurRel; FlatNodes; merge~; switch~; exhaust~; Flattener; PathRel; root~;
  sink~; map~; scan~; takeWhile~; spentWhile~; outerElem~; outerExplode~; inner~; deferInner~; InputBlock; block; RowRel; read~;
  cold~; defer~; MachRow; hot~; RegRel; []; _∷_; mach; Partners; ArrRows; Spent)

-- a node below the counter is none of the pair it hands out
fresh-unpaired : ∀ {n} {Γ : Ctx n} {κ : Kinds n} {π j j′ k} → k < j′
               → Unpaired {Γ = Γ} κ π k → Unpaired {Γ = Γ} κ ((j , j′ ∷ []) ∷ π) k
fresh-unpaired lt un (here refl) = <-irrefl refl lt
fresh-unpaired lt un (there k∈) = un k∈

mem-any : ∀ {k xs} → k ∈ xs → T (any (_≡ᵇ k) xs)
mem-any {k} (here refl) = ∨-Tˡ (≡⇒≡ᵇ k k refl)
mem-any (there e)       = ∨-Tʳ (mem-any e)

module _ {n} {Γ : Ctx n} (κ : Kinds n) (π π′ : List (NodeId × List NodeId)) where

  Keep : NodeId → Set
  Keep k = Unpaired {Γ = Γ} κ π k → Unpaired {Γ = Γ} κ π′ k

  -- every impl-only node a path names, frame by frame, stays unpaired
  Off : ∀ {lo s w} → Path (plainᵏ Γ κ) lo s w → Set
  Off root             = ⊤
  Off (share-sink _ _) = ⊤
  Off (f ↠[ _ ] q)     = All Keep (frameNodes f) × Off q

  OffRow : ∀ {w} → RegRow (plainᵏ Γ κ) w → Set
  OffRow (_ , _ , (_ , p)) = Off p

-- a path whose nodes are all below the counter is off the pair it hands out
fresh-off : ∀ {n} {Γ : Ctx n} {κ : Kinds n} {π j j′ lo s w} (q : Path (plainᵏ Γ κ) lo s w)
          → (∀ k → T (pathHasNode k q) → k < j′) → Off {Γ = Γ} κ π ((j , j′ ∷ []) ∷ π) q
fresh-off root             _  = tt
fresh-off (share-sink _ _) _  = tt
fresh-off {Γ = Γ} {κ = κ} {π = π} {j = j} (f ↠[ _ ] q) lt =
  tabulate (λ {k} k∈ → fresh-unpaired {Γ = Γ} {κ = κ} {π = π} {j = j} (lt k (∨-Tˡ (mem-any k∈)))) , fresh-off q (λ k h → lt k (∨-Tʳ h))

fresh-off-row : ∀ {n} {Γ : Ctx n} {κ : Kinds n} {π j j′ w} (r : RegRow (plainᵏ Γ κ) w)
              → (∀ k → T (rowThrough k r) → k < j′) → OffRow {Γ = Γ} κ π ((j , j′ ∷ []) ∷ π) r
fresh-off-row (_ , _ , (_ , p)) = fresh-off p

module _ {n} {Γ : Ctx n} (κ : Kinds n) {π π′ : List (NodeId × List NodeId)} (g : ∀ {x} → x ∈ π → x ∈ π′) where

  cur-grow : ∀ {cur cur′} → CurRel {Γ = Γ} κ π cur cur′ → CurRel {Γ = Γ} κ π′ cur cur′
  cur-grow {nothing} {nothing} c = c
  cur-grow {just _}  {just _}  c = g c

  nodes-grow : ∀ {u op x x′} → FlatNodes {Γ = Γ} κ π u op x x′ → FlatNodes {Γ = Γ} κ π′ u op x x′
  nodes-grow (merge~ ps) = merge~ ps
  nodes-grow (switch~ c) = switch~ (cur-grow c)
  nodes-grow exhaust~    = exhaust~

  module _ {t : Ty} {NP : List (NodeId × NodeState Γ)} {NI : List (NodeId × NodeState (plainᵏ Γ κ))} where

    flatG : ∀ {u op m m′ ks xs} → Flattener κ π {t = t} NP NI u op m m′ ks xs → Flattener κ π′ {t = t} NP NI u op m m′ ks xs
    flatG (pm , x , x′ , lP , lI , fn , c , lk) = g pm , x , x′ , lP , lI , nodes-grow fn , c , lk

    pathG : ∀ {lo lo′ s} {p : Path Γ lo s t} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t)}
          → Off {Γ = Γ} κ π π′ q → PathRel κ π NP NI p q → PathRel κ π′ NP NI p q
    pathG o root~                            = root~
    pathG o (sink~ sh)                       = sink~ sh
    pathG o (map~ L r)                       = map~ L (pathG (proj₂ o) r)
    pathG o (scan~ e l l′ v L r)             = scan~ (g e) l l′ v L (pathG (proj₂ (proj₂ o)) r)
    pathG o (takeWhile~ e l l₁ l₂ L r)       = takeWhile~ (g e) l l₁ l₂ L (pathG (proj₂ (proj₂ (proj₂ o))) r)
    pathG o (spentWhile~ e l l₂ r)           = spentWhile~ (g e) l l₂ (pathG (proj₂ (proj₂ (proj₂ o))) r)
    pathG o (outerElem~ f r)                 = outerElem~ (flatG f) (pathG (proj₂ (proj₂ (proj₂ (proj₂ o)))) r)
    pathG o (outerExplode~ f r)              =
      outerExplode~ (flatG f) (pathG (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ o)))))) r)
    pathG o (inner~ e f ip r)                = inner~ e (flatG f) (g ip) (pathG (proj₂ (proj₂ (proj₂ o))) r)
    pathG o (deferInner~ e₁ e₂ l l′ l₂ a≤ b≤ r) = deferInner~ (g e₁) (g e₂) l l′ l₂ a≤ b≤ (pathG (proj₂ (proj₂ (proj₂ o))) r)

    blockG : ∀ {a lo ℓ} {full : Path (plainᵏ Γ κ) lo a (emitᵗ t)} {q}
           → Off {Γ = Γ} κ π π′ full → InputBlock κ π NP NI a {lo} {ℓ} full q → InputBlock κ π′ NP NI a full q
    blockG o (block l₁ a≤ lb l₂ u₁ uj ub u₂) =
      block l₁ a≤ lb l₂ (head (proj₁ (proj₂ o)) u₁) (head (tail (proj₁ (proj₂ o))) uj) (head (proj₁ (proj₂ (proj₂ o))) ub)
            (head (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ o)))))) u₂)

    -- what a block's tail names, its whole path names
    block-tail : ∀ {a lo ℓ} {full : Path (plainᵏ Γ κ) lo a (emitᵗ t)} {q}
               → InputBlock κ π NP NI a {lo} {ℓ} full q → Off {Γ = Γ} κ π π′ full → Off {Γ = Γ} κ π π′ q
    block-tail (block _ _ _ _ _ _ _ _) o = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ o)))))

    module _ {LP LI} where

      rowG : ∀ {r r′} → OffRow {Γ = Γ} κ π π′ {emitᵗ t} r′ → RowRel κ π NP NI LP LI r r′ → RowRel κ π′ NP NI LP LI r r′
      rowG o (read~ hs r refl)          = read~ hs (pathG (proj₂ o) r) refl
      rowG o (cold~ sp b r refl)        = cold~ sp (blockG o b) (pathG (block-tail b o) r) refl
      rowG o (defer~ sp e l l′ r refl)  = defer~ sp (g e) l l′ (pathG (proj₂ o) r) refl

      machG : ∀ {r′} → OffRow {Γ = Γ} κ π π′ {emitᵗ t} r′ → MachRow κ π {t = t} NP NI LP LI r′ → MachRow κ π′ NP NI LP LI r′
      machG o (hot~ hot b refl) = hot~ hot (blockG o b) refl

      regG : ∀ {rs rs′} → (∀ {r′} → r′ ∈ rs′ → OffRow {Γ = Γ} κ π π′ {emitᵗ t} r′) → RegRel κ π NP NI LP LI rs rs′ → RegRel κ π′ NP NI LP LI rs rs′
      regG o []         = []
      regG o (r ∷ q)    = rowG (o (here refl)) r ∷ regG (λ r∈ → o (there r∈)) q
      regG o (mach r q) = mach (machG (o (here refl)) r) (regG (λ r∈ → o (there r∈)) q)

      -- the registries pair the same rows
      partG : ∀ {rs rs′} (o : ∀ {r′} → r′ ∈ rs′ → OffRow {Γ = Γ} κ π π′ {emitᵗ t} r′) (q : RegRel κ π NP NI LP LI rs rs′) {r r′}
            → Partners κ π NP NI LP LI q r r′ → Partners κ π′ NP NI LP LI (regG o q) r r′
      partG o (_ ∷ q)    (inj₁ e) = inj₁ e
      partG o (_ ∷ q)    (inj₂ p) = inj₂ (partG (λ r∈ → o (there r∈)) q p)
      partG o (mach _ q) p        = partG (λ r∈ → o (there r∈)) q p

      -- and spend them alike
      spentG : ∀ {rs rs′} (o : ∀ {r′} → r′ ∈ rs′ → OffRow {Γ = Γ} κ π π′ {emitᵗ t} r′) (q : RegRel κ π NP NI LP LI rs rs′) {dP dI}
             → Spent κ π NP NI LP LI q dP dI → Spent κ π′ NP NI LP LI (regG o q) dP dI
      spentG o []         s       = s
      spentG o (_ ∷ q)    (e , s) = e , spentG (λ r∈ → o (there r∈)) q s
      spentG o (mach _ q) s       = spentG (λ r∈ → o (there r∈)) q s

      -- and the same minted sources
      arrG : ∀ {rs rs′} (o : ∀ {r′} → r′ ∈ rs′ → OffRow {Γ = Γ} κ π π′ {emitᵗ t} r′) (q : RegRel κ π NP NI LP LI rs rs′) {s s′ w w′}
           → ArrRows κ π NP NI LP LI q s s′ w w′ → ArrRows κ π′ NP NI LP LI (regG o q) s s′ w w′
      arrG o []                             _       = _
      arrG o (read~ _ _ refl ∷ q)           a       = arrG (λ r∈ → o (there r∈)) q a
      arrG o (cold~ _ _ _ refl ∷ q)         (r , a) = r , arrG (λ r∈ → o (there r∈)) q a
      arrG o (defer~ _ _ _ _ _ refl ∷ q)    (r , a) = r , arrG (λ r∈ → o (there r∈)) q a
      arrG o (mach _ q)                     a       = arrG (λ r∈ → o (there r∈)) q a
