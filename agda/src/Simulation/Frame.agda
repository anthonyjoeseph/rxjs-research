------------------------------------------------------------------
-- A RELATION READS THE IMPL'S NODES ONLY ON ITS OWN PATH.  Every node
-- fact `PathRel`, `InputBlock`, `RowRel` and `MachRow` state is at a
-- node one of the related path's frames names, so a node table that
-- agrees with another along a path relates whatever the other did.  A
-- step that writes nodes keeps the registries related row by row: each
-- row the write does not reach is kept as it stood, and each it reaches
-- is related anew by whoever wrote it.
------------------------------------------------------------------
module Simulation.Frame where

open import Data.Bool    using (true; _∨_)
open import Data.Bool.Properties using (∨-zeroʳ)
open import Data.Bool.ListAction using (any)
open import Data.List    using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat     using (_≤_; _≡ᵇ_)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Sum     using (inj₁; inj₂)
open import Data.Unit    using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

open import Decide       using (≡ᵇ-refl)
open import Rx.Exp       using (Ctx)
open import Rx.Evaluator using (NodeId; NodeState; Path; Frame; _↠[_]_; frameNodes; pathHasNode; lookupNode; RegRow)
open import SExp.Syntax  using (Kinds; plainᵏ; emitᵗ)
open import Simulation.Stores using (PathRel; root~; sink~; map~; scan~; takeWhile~; spentWhile~; outerElem~; outerExplode~; inner~;
  lane~; deferInner~; InputBlock; block; RowRel; read~; cold~; defer~; MachRow; hot~; RegRel; []; _∷_; mach; Partners; ArrRows)

-- a frame's first node is on it
first : ∀ k (ks : List NodeId) → any (_≡ᵇ k) (k ∷ ks) ≡ true
first k ks = cong (_∨ any (_≡ᵇ k) ks) (≡ᵇ-refl k)

-- a node on a path's head frame, or on the rest of it
on-here : ∀ {m} {Δ : Ctx m} {lo ℓ s u t} (f : Frame Δ s u) {le : lo ≤ ℓ} {p : Path Δ ℓ u t} {k}
        → any (_≡ᵇ k) (frameNodes f) ≡ true → pathHasNode k (f ↠[ le ] p) ≡ true
on-here f {p = p} {k} e = cong (_∨ pathHasNode k p) e

on-there : ∀ {m} {Δ : Ctx m} {lo ℓ s u t} (f : Frame Δ s u) {le : lo ≤ ℓ} {p : Path Δ ℓ u t} {k}
         → pathHasNode k p ≡ true → pathHasNode k (f ↠[ le ] p) ≡ true
on-there f {k = k} e = trans (cong (any (_≡ᵇ k) (frameNodes f) ∨_) e) (∨-zeroʳ (any (_≡ᵇ k) (frameNodes f)))

module _ {n} {Γ : Ctx n} (κ : Kinds n) where

  -- two node tables alike at every node a path names
  -- (a record, so that the path stays an index inference can read)
  record Agree {lo s u} (NI′ NI : List (NodeId × NodeState (plainᵏ Γ κ))) (q : Path (plainᵏ Γ κ) lo s u) : Set where
    constructor agree
    field at : ∀ k → pathHasNode k q ≡ true → lookupNode k NI′ ≡ lookupNode k NI
  open Agree public

  module _ {NI NI′ : List (NodeId × NodeState (plainᵏ Γ κ))} where

    -- the rest of a path agrees where the whole does, and its head frame's nodes
    tail : ∀ {lo ℓ s u v} {f : Frame (plainᵏ Γ κ) s u} {le : lo ≤ ℓ} {p : Path (plainᵏ Γ κ) ℓ u v}
         → Agree NI′ NI (f ↠[ le ] p) → Agree NI′ NI p
    tail {f = f} {le} {p} (agree a) = agree (λ k e → a k (on-there f {le} {p} {k} e))

    hd : ∀ {lo ℓ s u v} {f : Frame (plainᵏ Γ κ) s u} {le : lo ≤ ℓ} {p : Path (plainᵏ Γ κ) ℓ u v}
       → Agree NI′ NI (f ↠[ le ] p) → ∀ {k} → any (_≡ᵇ k) (frameNodes f) ≡ true → lookupNode k NI′ ≡ lookupNode k NI
    hd {f = f} {le} {p} (agree a) {k} e = a k (on-here f {le} {p} {k} e)

  module _ {π t NP} {NI NI′ : List (NodeId × NodeState (plainᵏ Γ κ))} where

    path-frame : ∀ {lo lo′ s} {p} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t)}
               → Agree NI′ NI q → PathRel {Γ = Γ} κ π {t} NP NI {lo} p q → PathRel {Γ = Γ} κ π NP NI′ p q
    path-frame ag root~ = root~
    path-frame ag (sink~ sh) = sink~ sh
    path-frame ag (map~ L r) = map~ L (path-frame (tail ag) r)
    path-frame ag (scan~ {k′ = k′} pk lP lI v sl r) =
      scan~ pk lP (trans (hd ag (first k′ [])) lI) v sl (path-frame (tail (tail ag)) r)
    path-frame ag (takeWhile~ {k₁ = k₁} {k₂} pk lP l₁ l₂ cl r) =
      takeWhile~ pk lP (trans (hd ag (first k₁ [])) l₁)
                       (trans (hd (tail ag) (first k₂ [])) l₂)
                       cl (path-frame (tail (tail (tail ag))) r)
    path-frame ag (spentWhile~ {k₂ = k₂} pk lP l₂ r) =
      spentWhile~ pk lP (trans (hd (tail ag) (first k₂ [])) l₂) (path-frame (tail (tail (tail ag))) r)
    path-frame ag (outerElem~ {m′ = m′} {ks} (pm , x , x′ , lP , lI , fn , c , lk) r) =
      outerElem~ (pm , x , x′ , lP , trans (hd (tail ag) (first m′ [])) lI , fn , c , trans (hd (tail (tail ag)) (first ks [])) lk)
                 (path-frame (tail (tail (tail (tail ag)))) r)
    path-frame ag (outerExplode~ {m′ = m′} {ks} (pm , x , x′ , lP , lI , fn , c , lk) r) =
      outerExplode~ (pm , x , x′ , lP , trans (hd (tail (tail (tail ag))) (first m′ [])) lI , fn
                    , c , trans (hd (tail (tail (tail (tail ag)))) (first ks [])) lk)
                    (path-frame (tail (tail (tail (tail (tail (tail ag)))))) r)
    path-frame ag (inner~ {m′ = m′} {ks} {j′ = j′} e (pm , x , x′ , lP , lI , fn , c , lk) ip r) =
      inner~ e (pm , x , x′ , lP , trans (hd ag (first m′ (j′ ∷ []))) lI , fn , c , trans (hd (tail ag) (first ks [])) lk) ip
             (path-frame (tail (tail (tail ag))) r)
    path-frame ag (lane~ {mL = mL} {jL} lL uL uJ r) =
      lane~ (trans (hd ag (first mL (jL ∷ []))) lL) uL uJ (path-frame (tail ag) r)
    path-frame ag (deferInner~ {nid′ = nid′} {j′ = j′} {m2 = m2} {j2 = j2} p₁ p₂ lP lI lm al r) =
      deferInner~ p₁ p₂ lP (trans (hd (tail (tail ag)) (first nid′ (j′ ∷ []))) lI)
                  (trans (hd ag (first m2 (j2 ∷ []))) lm) al
                  (path-frame (tail (tail (tail ag))) r)

    -- an input block's nodes are its own frames', and its tail is on it
    block-frame : ∀ {a lo ℓ} {full : Path (plainᵏ Γ κ) lo a (emitᵗ t)} {q}
                → Agree NI′ NI full → InputBlock {Γ = Γ} κ π {t} NP NI a {lo} {ℓ} full q → InputBlock {Γ = Γ} κ π NP NI′ a full q
    block-frame ag (block {m1 = m1} {j1} {b} {m2} l₁ a₁ lb l₂ u₁ uj ub u₂) =
      block (trans (hd (tail ag) (first m1 (j1 ∷ []))) l₁) a₁
            (trans (hd (tail (tail ag)) (first b [])) lb)
            (trans (hd (tail (tail (tail (tail (tail ag))))) (first m2 [])) l₂) u₁ uj ub u₂

    block-tail : ∀ {a lo ℓ} {full : Path (plainᵏ Γ κ) lo a (emitᵗ t)} {q}
               → InputBlock {Γ = Γ} κ π {t} NP NI a {lo} {ℓ} full q → Agree NI′ NI full → Agree NI′ NI q
    block-tail (block _ _ _ _ _ _ _ _) ag = tail (tail (tail (tail (tail (tail ag)))))

    module _ {LP LI} where

      row-frame : ∀ {r r′} → Agree NI′ NI (proj₂ (proj₂ (proj₂ r′)))
                → RowRel {Γ = Γ} κ π {t} NP NI LP LI r r′ → RowRel {Γ = Γ} κ π NP NI′ LP LI r r′
      row-frame ag (read~ hk pr refl)            = read~ hk (path-frame (tail ag) pr) refl
      row-frame ag (cold~ sp ib pr refl)         = cold~ sp (block-frame ag ib) (path-frame (block-tail ib ag) pr) refl
      row-frame ag (defer~ {nid′ = nid′} sp pi lP lI pr refl) =
        defer~ sp pi lP (trans (hd ag (first nid′ [])) lI) (path-frame (tail ag) pr) refl

      mach-frame : ∀ {r′} → Agree NI′ NI (proj₂ (proj₂ (proj₂ r′)))
                 → MachRow {Γ = Γ} κ π {t} NP NI LP LI r′ → MachRow {Γ = Γ} κ π NP NI′ LP LI r′
      mach-frame ag (hot~ hot ib refl) = hot~ hot (block-frame ag ib) refl

      -- THE REGISTRIES, ROW BY ROW: a plain row's partner keeps its relation
      -- where its path agrees, and an impl-only row is related anew by the
      -- caller, which is where a write that reaches a row is answered
      module _ {rs₀ : List (RegRow (plainᵏ Γ κ) (emitᵗ t))}
               (rows  : ∀ {r r′} → r′ ∈ rs₀ → RowRel {Γ = Γ} κ π {t} NP NI LP LI r r′ → Agree NI′ NI (proj₂ (proj₂ (proj₂ r′))))
               (machs : ∀ {r′} → r′ ∈ rs₀ → MachRow {Γ = Γ} κ π {t} NP NI LP LI r′ → MachRow {Γ = Γ} κ π NP NI′ LP LI r′) where

        reg-frame : ∀ {rs rs′} → (∀ {r′} → r′ ∈ rs′ → r′ ∈ rs₀)
                  → RegRel {Γ = Γ} κ π {t} NP NI LP LI rs rs′ → RegRel {Γ = Γ} κ π NP NI′ LP LI rs rs′
        reg-frame w []        = []
        reg-frame w (x ∷ q)   = row-frame (rows (w (here refl)) x) x ∷ reg-frame (λ m → w (there m)) q
        reg-frame w (mach x q) = mach (machs (w (here refl)) x) (reg-frame (λ m → w (there m)) q)

        partners-frame : ∀ {rs rs′} (w : ∀ {r′} → r′ ∈ rs′ → r′ ∈ rs₀) (q : RegRel {Γ = Γ} κ π {t} NP NI LP LI rs rs′) {x x′}
                       → Partners {Γ = Γ} κ π NP NI LP LI q x x′ → Partners {Γ = Γ} κ π NP NI′ LP LI (reg-frame w q) x x′
        partners-frame w []         ()
        partners-frame w (x ∷ q)    (inj₁ e) = inj₁ e
        partners-frame w (x ∷ q)    (inj₂ p) = inj₂ (partners-frame (λ m → w (there m)) q p)
        partners-frame w (mach x q) p        = partners-frame (λ m → w (there m)) q p

        arr-frame : ∀ {rs rs′} (w : ∀ {r′} → r′ ∈ rs′ → r′ ∈ rs₀) (q : RegRel {Γ = Γ} κ π {t} NP NI LP LI rs rs′) {s s′ u u′}
                  → ArrRows {Γ = Γ} κ π NP NI LP LI q s s′ u u′ → ArrRows {Γ = Γ} κ π NP NI′ LP LI (reg-frame w q) s s′ u u′
        arr-frame w []                            _       = tt
        arr-frame w (read~ hk pr refl ∷ q)         a       = arr-frame (λ m → w (there m)) q a
        arr-frame w (cold~ sp ib pr refl ∷ q)      (r , a) = r , arr-frame (λ m → w (there m)) q a
        arr-frame w (defer~ sp pi lP lI pr refl ∷ q) (r , a) = r , arr-frame (λ m → w (there m)) q a
        arr-frame w (mach x q)                    a       = arr-frame (λ m → w (there m)) q a
