------------------------------------------------------------------
-- A COLD READ'S ROW REGISTERED ON BOTH SIDES, the impl's over its
-- input block: the plain read mints a source, an ordinal and an id and
-- registers its path; the impl's block installs its nodes at or above
-- the node counter, mints its own source and registers the path
-- through the block.  The two rows relate as `cold~`.
--
-- THE BLOCK'S NODES ARE ITS OWN ROW'S, so `Store.owned` holds of the
-- new registry with no new field.  Every row already registered
-- threads only nodes below the counter, which the block's are not; and
-- the new row threads no node an old row's block names, since past its
-- own block it threads only its tail's, which are `π`'s, and an old
-- block's are none of `π`'s.
------------------------------------------------------------------
module Simulation.Cold where

open import Data.Bool    using (Bool; true; false; T; if_then_else_)
open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Fin     using (Fin; _↑ʳ_)
open import Data.List    using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise) renaming ([] to []ᵖ; _∷_ to _∷ᵖ_)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᵃ; _∷_ to _∷ᵃ_; map to mapᵃ; lookup to lookupᵃ; tabulate to tabulateᵃ)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to ++⁺ᵃ)
open import Data.List.Relation.Unary.AllPairs using () renaming ([] to []ᴾ; _∷_ to _∷ᴾ_)
open import Data.List.Relation.Unary.AllPairs.Properties using () renaming (++⁺ to ++⁺ᴾ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻)
open import Data.Nat     using (ℕ; suc; _+_; _<_; _≤_)
open import Data.Nat.Properties using (≤-refl; n≤1+n; n<1+n; m<n⇒m<1+n; <⇒≢; <⇒≤; <⇒≱; <-≤-trans; ≤-trans; <-irrefl; ≤⇒≤ᵇ; <-trans)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Unit    using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import Rx.Exp       using (Ctx; Ty; Closed; Val)
open import Rx.Mint      using (Mint; counter; setAt; sourceᵏ; ordinalᵏ; regᵏ; nodeᵏ; freshId)
open import Rx.Evaluator using (NodeId; NodeState; Sched; EvalSt; LiveSource; RegRow; regSource; Path; atDyn; atSlot; register;
                                spentOn; pathHasNode; lookupNode; Stream)
open import Rx.Evaluator.Domain using (foldPath⇓)
open import Rx.Evaluator.Freshness using (nodeCt)
open import Rx.Evaluator.Reducible.Support using (Sound; Rule; Distinct; endOf; register-sound; sub-ot; fresh-rows)
open import SExp.Syntax  using (Kinds; plainᵏ; plainᵗ; emitᵗ)
open import Simulation.Schedules using (ticks) renaming (_∷_ to _∷ˢ_)
open import Simulation.Stores using (LiveAt; live; Store; Arr; PathRel; Named; Unpaired; InputBlock; block; RowRel; read~; cold~; defer~; hot~;
                                     RegRel; []; _∷_; mach; Src; blockNodes; dyn~; LiveOn; LiveIf; module LiveIf; LiveRows; live-agree; live-if-agree)
  renaming (here to sp-here)
open import Simulation.Sweep using (same-refl; sameSource-no; T-true; raw<ₙ; stamped<)
open import Simulation.Cut   using (nodesOf; has-node; node-has)
open import Simulation.After using (module Kept; apart; below-vals)
open import Simulation.Arm   using (module Arms)
open import Simulation.Install using (module Move; weak; weak₂; low-row)
open import Simulation.Hop   using (none-below; member-below; ranked-top; guard-none; guard-new; swept-snoc; census-snoc;
                                    reg-cons; part-cons; spent-cons; arr-cons; reg-snoc; part-snoc; spent-snoc; arr-snoc;
                                    reg-unp; rel-vals; path-spent)

-- the counters move past a source, an ordinal and an id handed out at
-- or above them, and the source joins the live list
named-src : ∀ {m} {Δ : Ctx m} {u} {e : Closed Δ u} {f} {sched : Sched Δ} {st : EvalSt e} {mt : Mint} {l : LiveSource Δ} {R N}
          → Named f sched st
          → counter (Sched.mint sched) sourceᵏ ≤ counter mt sourceᵏ → counter (Sched.mint sched) ordinalᵏ ≤ counter mt ordinalᵏ
          → counter (Sched.mint sched) regᵏ ≤ counter mt regᵏ → LiveSource.ordinal l < counter mt ordinalᵏ
          → All (λ r → regSource (proj₁ (proj₂ r)) < counter mt sourceᵏ) R
          → Named f (record sched { mint = mt ; live = l ∷ Sched.live sched }) (record st { registry = R ; nodes = N })
named-src X s≤ o≤ r≤ o rs = record
  { slots-below = <-≤-trans (Named.slots-below X) s≤
  ; ords-below  = o ∷ᵃ weak {f = λ x → x} o≤ (Named.ords-below X)
  ; srcs-below  = rs
  ; cut-below   = weak {f = λ x → x} r≤ (Named.cut-below X)
  ; dlv-below   = weak {f = λ x → x} r≤ (Named.dlv-below X)
  ; dying-below = weak {f = λ x → x} s≤ (Named.dying-below X)
  }

module _ {n} {Γ : Ctx n} (κ : Kinds n) where

  -- an input block's nodes are on its path
  ib-has : ∀ {t π NP NI a lo ℓ} {full : Path (plainᵏ Γ κ) lo a (emitᵗ t)} {q}
         → InputBlock {Γ = Γ} κ π {t} NP NI a {lo} {ℓ} full q → ∀ {j} → j ∈ blockNodes full → j ∈ nodesOf full
  ib-has (block _ _ _ _ _ _ _ _) (here refl)                         = here refl
  ib-has (block _ _ _ _ _ _ _ _) (there (here refl))                 = there (here refl)
  ib-has (block _ _ _ _ _ _ _ _) (there (there (here refl)))         = there (there (here refl))
  ib-has (block _ _ _ _ _ _ _ _) (there (there (there (here refl)))) = there (there (there (here refl)))
  ib-has (block _ _ _ _ _ _ _ _) (there (there (there (there ()))))

  -- and past them, its tail's
  ib-split : ∀ {t π NP NI a lo ℓ} {full : Path (plainᵏ Γ κ) lo a (emitᵗ t)} {q}
           → InputBlock {Γ = Γ} κ π {t} NP NI a {lo} {ℓ} full q → ∀ {j} → j ∈ nodesOf full → j ∈ blockNodes full ⊎ j ∈ nodesOf q
  ib-split (block _ _ _ _ _ _ _ _) (here refl)                         = inj₁ (here refl)
  ib-split (block _ _ _ _ _ _ _ _) (there (here refl))                 = inj₁ (there (here refl))
  ib-split (block _ _ _ _ _ _ _ _) (there (there (here refl)))         = inj₁ (there (there (here refl)))
  ib-split (block _ _ _ _ _ _ _ _) (there (there (there (here refl)))) = inj₁ (there (there (there (here refl))))
  ib-split (block _ _ _ _ _ _ _ _) (there (there (there (there m))))   = inj₂ m

  -- a block's frames take no budget and end where its tail does
  ib-spent : ∀ {t π NP NI a lo ℓ} {full : Path (plainᵏ Γ κ) lo a (emitᵗ t)} {q}
           → InputBlock {Γ = Γ} κ π {t} NP NI a {lo} {ℓ} full q → ∀ N → spentOn full N ≡ spentOn q N
  ib-spent (block _ _ _ _ _ _ _ _) N = refl

  ib-end : ∀ {t π NP NI a lo ℓ} {full : Path (plainᵏ Γ κ) lo a (emitᵗ t)} {q}
         → InputBlock {Γ = Γ} κ π {t} NP NI a {lo} {ℓ} full q → endOf full ≡ endOf q
  ib-end (block _ _ _ _ _ _ _ _) = refl

  -- every node an impl row's block names is on the row's path
  reg-has : ∀ {t π NP NI LP LI rs rs′} → RegRel {Γ = Γ} κ π {t} NP NI LP LI rs rs′
          → ∀ {r′} → r′ ∈ rs′ → (∀ (k : Fin n) → proj₁ (proj₂ r′) ≡ atSlot (n ↑ʳ k) → ⊥)
          → ∀ {j} → j ∈ blockNodes (proj₂ (proj₂ (proj₂ r′))) → j ∈ nodesOf (proj₂ (proj₂ (proj₂ r′)))
  reg-has (read~ {i = i} _ _ _ ∷ q)   (here refl) ns m  = ⊥-elim (ns i refl)
  reg-has (cold~ _ ib _ refl ∷ q)     (here refl) ns m  = ib-has ib m
  reg-has (defer~ _ _ _ _ _ refl ∷ q) (here refl) ns ()
  reg-has (_ ∷ q)                     (there r∈)  ns m  = reg-has q r∈ ns m
  reg-has (mach (hot~ _ ib refl) q)   (here refl) ns m  = ib-has ib m
  reg-has (mach _ q)                  (there r∈)  ns m  = reg-has q r∈ ns m

  -- a block minted above every node `π` pairs is none of them
  block-at : ∀ {t π NP NP₀ NI a lo ℓ c} {full : Path (plainᵏ Γ κ) lo a (emitᵗ t)} {q}
           → All (λ e → All (_< c) (proj₂ e)) π → (∀ {j} → j ∈ blockNodes full → c ≤ j)
           → InputBlock {Γ = Γ} κ [] {t} NP₀ NI a {lo} {ℓ} full q → InputBlock {Γ = Γ} κ π NP NI a full q
  block-at {π = π} {c = c} bI ge (block l₁ a≤ lb l₂ _ _ _ _) =
    block l₁ a≤ lb l₂ (un (ge (here refl))) (un (ge (there (here refl))))
          (un (ge (there (there (here refl))))) (un (ge (there (there (there (here refl))))))
    where
    un : ∀ {j} → c ≤ j → Unpaired {Γ = Γ} κ π j
    un le k∈ = <⇒≱ (lookupᵃ (below-vals bI) k∈) le

module _ {n} {Γ : Ctx n} (κ : Kinds n) {t} {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)} where

  open Kept {Γ = Γ} κ {t} {ep} {ei}
  open Arms {Γ = Γ} κ using (Carries)

  -- the impl's live source a cold read mints
  coldSrc : ∀ (s : Ty) → ℕ → ℕ → List (ℕ × Val (plainᵏ Γ κ) (plainᵗ s)) → LiveSource (plainᵏ Γ κ)
  coldSrc s src ord ps = record { source = src ; ordinal = ord ; elemTy = plainᵗ s ; pending = ps }

  -- WHAT THE IMPL'S BLOCK LEAVES WHERE ITS FLUSH STARTS DOWN THE TAIL:
  -- its nodes installed at or above the node counter and every node
  -- below it as it was; a source, an ordinal and an id minted at or
  -- above the counters, the source live and partnered with the plain
  -- read's; the read's path through the block about to be registered,
  -- whose flattening merge's outer is live while the flush has not run;
  -- and the flush one fold of a group carrying the plain prefix
  record ColdBlock {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei} (S : St sP stP sI stI)
                   {lo s} (q : Path (plainᵏ Γ κ) (n + lo) (emitᵗ s) (emitᵗ t)) (now : ℕ) (lP : LiveSource Γ) (vs : List (Val Γ s))
                   (rI : Stream (plainᵏ Γ κ) (emitᵗ t) × Sched (plainᵏ Γ κ) × EvalSt ei) : Set where
    field
      mI       : Mint
      NI       : List (NodeId × NodeState (plainᵏ Γ κ))
      full     : Path (plainᵏ Γ κ) (n + lo) (plainᵗ s) (emitᵗ t)
      src′     : ℕ
      ordI     : ℕ
      rid′     : ℕ
      pendI    : List (ℕ × Val (plainᵏ Γ κ) (plainᵗ s))
      es       : List (Val (plainᵏ Γ κ) (emitᵗ s))
      blk      : InputBlock {Γ = Γ} κ [] {t} [] NI (plainᵗ s) full q
      nodes-at : ∀ {k} → k ∈ blockNodes full → nodeCt sI ≤ k × k < freshId nodeᵏ mI
      node≤    : nodeCt sI ≤ freshId nodeᵏ mI
      kept     : ∀ k → k < nodeCt sI → lookupNode k NI ≡ lookupNode k (EvalSt.nodes stI)
      dist     : Distinct q → Distinct full
      walks-live : LiveOn q NI → LiveOn full NI
      src≤     : counter (Sched.mint sI) sourceᵏ ≤ src′
      src<     : src′ < counter mI sourceᵏ
      ord≤     : counter (Sched.mint sI) ordinalᵏ ≤ ordI
      ord<     : ordI < counter mI ordinalᵏ
      rid≤     : counter (Sched.mint sI) regᵏ ≤ rid′
      rid<     : rid′ < counter mI regᵏ
      partner  : Src {Γ = Γ} κ lP (coldSrc s src′ ordI pendI)
      ticks≡   : ticks lP ≡ ticks (coldSrc s src′ ordI pendI)
      carries  : Carries {s} es vs
      fold     : foldPath⇓ now q es false (record sI { mint = mI ; live = coldSrc s src′ ordI pendI ∷ Sched.live sI })
                   (register rid′ (atDyn src′ (n + lo)) full (record stI { nodes = NI })) rI

  module Reg {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei} (S : St sP stP sI stI)
             {lo s} {p : Path Γ lo s t} {q : Path (plainᵏ Γ κ) (n + lo) (emitᵗ s) (emitᵗ t)}
             (pr : PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q)
             {now} (pendP : List (ℕ × Val Γ s)) {vs rI}
             (B : ColdBlock S q now (record { source = freshId sourceᵏ (Sched.mint sP) ; ordinal = freshId ordinalᵏ (Sched.mint sP)
                                            ; elemTy = s ; pending = pendP }) vs rI) where

    open Store S
    open ColdBlock B

    src = freshId sourceᵏ (Sched.mint sP) ; ordP = freshId ordinalᵏ (Sched.mint sP) ; rid = freshId regᵏ (Sched.mint sP)

    lP : LiveSource Γ
    lP = record { source = src ; ordinal = ordP ; elemTy = s ; pending = pendP }
    lI = coldSrc s src′ ordI pendI

    sP₂ = record sP { mint = setAt regᵏ (suc rid) (setAt sourceᵏ (suc src) (setAt ordinalᵏ (suc ordP) (Sched.mint sP)))
                    ; live = lP ∷ Sched.live sP }
    sI₁ = record sI { mint = mI ; live = lI ∷ Sched.live sI }

    rowP : RegRow Γ t
    rowP = rid , atDyn src lo , s , p
    rowI : RegRow (plainᵏ Γ κ) (emitᵗ t)
    rowI = rid′ , atDyn src′ (n + lo) , plainᵗ s , full

    KP = EvalSt.registry stP
    KI = EvalSt.registry stI

    stP₂ : List (RegRow Γ t) → EvalSt ep
    stP₂ R = record stP { registry = R }
    stI₂ : List (RegRow (plainᵏ Γ κ) (emitᵗ t)) → EvalSt ei
    stI₂ R = record stI { nodes = NI ; registry = R }

    bP : n < src
    bP = Named.slots-below (proj₁ named)
    bI : n + n < src′
    bI = <-≤-trans (Named.slots-below (proj₂ named)) src≤

    s≤ = ≤-trans src≤ (<⇒≤ src<)
    o≤ = ≤-trans ord≤ (<⇒≤ ord<)
    r≤ = ≤-trans rid≤ (<⇒≤ rid<)

    -- the rows carried to the block's nodes, `π` as it was
    module M = Move {Γ = Γ} κ {π = π} {π′ = π} (λ x → x) (λ _ u → u) (proj₁ pairs-below) (proj₂ pairs-below) {t = t}
                 {NP = EvalSt.nodes stP} {NP′ = EvalSt.nodes stP} {NI = EvalSt.nodes stI} {NI′ = NI} (λ _ _ → refl) kept

    o : ∀ {r′} → r′ ∈ KI → M.Lw r′
    o {r′} r∈ = low-row r′ (fresh-rows ruleI r∈)

    rows₁ = M.regM o rows
    pr₁ = M.pathM pr

    new-row : RowRel {Γ = Γ} κ π {t} (EvalSt.nodes stP) NI (lP ∷ Sched.live sP) (lI ∷ Sched.live sI) rowP rowI
    new-row = cold~ sp-here (block-at {Γ = Γ} κ (proj₂ pairs-below) (λ b → proj₁ (nodes-at b)) blk) pr₁ refl

    -- an old row's nodes are below the counter, which the block wrote above
    old-live : LiveRows (stI₂ KI)
    old-live = live λ {r} r∈ sk → live-agree (proj₂ (proj₂ (proj₂ r))) {EvalSt.nodes stI} {NI} (λ k h → kept k (fresh-rows ruleI r∈ k h)) (LiveRows.rows-live live-outer {r} r∈ sk)

    persist : (R : List (RegRow Γ t)) (R′ : List (RegRow (plainᵏ Γ κ) (emitᵗ t)))
              (S₂ : Store κ sP₂ (stP₂ R) sI₁ (stI₂ R′))
            → (∀ {s s′ w w′} → Arr S s s′ w w′ → _)
            → Persists S S₂
    persist R R′ S₂ ar-rows ar = record
      { boundP = m<n⇒m<1+n (Arr.boundP ar) ; boundI = <-≤-trans (Arr.boundI ar) s≤
      ; rows   = ar-rows ar
      ; lists  = ((λ e → ⊥-elim (<-irrefl (sym e) (Arr.boundP ar))) , (λ e′ → ⊥-elim (<-irrefl (sym e′) (<-≤-trans (Arr.boundI ar) src≤))))
                 ∷ᵖ Arr.lists ar }

    -- SPENT: the path already cut, so neither run registers it
    spent : Rule sP₂ (stP₂ KP) → Rule sI₁ (stI₂ KI)
          → Σ (After S ([] , sP₂ , stP₂ KP) ([] , sI₁ , stI₂ KI)) λ A → PathRel κ (Store.π (After.store A)) (EvalSt.nodes stP) NI p q
    spent rP rI =
      after S₂ (λ { (inj₁ c) → inj₁ c ; (inj₂ (a , b , pp)) → inj₂ (a , b , part-cons {Γ = Γ} κ rows₁ (M.partM o rows pp)) })
               (persist KP KI S₂ (λ ar → arr-cons {Γ = Γ} κ rows₁ (M.arrM o rows (Arr.rows ar)))) []ᵖ (λ m → m)
      , pr₁
      where
      S₂ : Store κ sP₂ (stP₂ KP) sI₁ (stI₂ KI)
      S₂ = record
        { π = π ; π-keys = π-keys ; π-vals = π-vals
        ; pairs-below = proj₁ pairs-below , weak₂ node≤ (proj₂ pairs-below)
        ; sources = partner ∷ᵖ sources
        ; numbers = dyn~ bP bI ∷ᵖ numbers
        ; distinct = apart (proj₁ bounded) ∷ᴾ proj₁ distinct , apart (weak {f = λ x → x} src≤ (proj₂ bounded)) ∷ᴾ proj₂ distinct
        ; sync = (ticks≡ , ranked-top sources (Named.ords-below (proj₁ named)) (weak {f = λ x → x} ord≤ (Named.ords-below (proj₂ named)))) ∷ˢ sync
        ; rows = reg-cons {Γ = Γ} κ rows₁
        ; dlv-alike = spent-cons {Γ = Γ} κ rows₁ (M.spentM o rows dlv-alike)
        ; dying-alike = spent-cons {Γ = Γ} κ rows₁ (M.spentM o rows dying-alike)
        ; latches = latches ; dying-done = dying-done
        ; bounded = n<1+n _ ∷ᵃ mapᵃ m<n⇒m<1+n (proj₁ bounded) , src< ∷ᵃ weak {f = λ x → x} s≤ (proj₂ bounded)
        ; swept = trans (guard-none KP lP bP (Named.srcs-below (proj₁ named)))
                        (sym (guard-none KI lI bI (weak {f = λ r → regSource (proj₁ (proj₂ r))} src≤ (Named.srcs-below (proj₂ named)))))
                  ∷ᵖ swept
        ; uncut = uncut
        ; named = named-src (proj₁ named) (n≤1+n _) (n≤1+n _) (n≤1+n _) (n<1+n _) (mapᵃ m<n⇒m<1+n (Named.srcs-below (proj₁ named)))
                , named-src (proj₂ named) s≤ o≤ r≤ ord< (weak {f = λ r → regSource (proj₁ (proj₂ r))} s≤ (Named.srcs-below (proj₂ named)))
        ; rids = rids
        ; fresh-ids = mapᵃ m<n⇒m<1+n (proj₁ fresh-ids) , weak {f = λ r → proj₁ r} r≤ (proj₂ fresh-ids)
        ; above = above ; census = census ; owned = owned
        ; ruleP = rP ; ruleI = rI ; scripts = scripts ; live-outer = old-live
        }

    -- REGISTERED: the rows join both registries last, paired as `cold~`,
    -- the impl's on a path its walk found live
    registered : LiveOn full NI → Rule sP₂ (stP₂ (KP ++ rowP ∷ [])) → Rule sI₁ (stI₂ (KI ++ rowI ∷ []))
               → Σ (After S ([] , sP₂ , stP₂ (KP ++ rowP ∷ [])) ([] , sI₁ , stI₂ (KI ++ rowI ∷ []))) λ A
                   → PathRel κ (Store.π (After.store A)) (EvalSt.nodes stP) NI p q
    registered cold-live rP rI =
      after S₂ (λ { (inj₁ c) → inj₁ c ; (inj₂ (a , b , pp)) → inj₂ (a , b , part-snoc {Γ = Γ} κ (reg-cons {Γ = Γ} κ rows₁) new-row (part-cons {Γ = Γ} κ rows₁ (M.partM o rows pp))) })
               (persist (KP ++ rowP ∷ []) (KI ++ rowI ∷ []) S₂
                  (λ ar → arr-snoc {Γ = Γ} κ (reg-cons {Γ = Γ} κ rows₁) new-row (arr-cons {Γ = Γ} κ rows₁ (M.arrM o rows (Arr.rows ar)))
                            (((λ e → ⊥-elim (<-irrefl e (Arr.boundP ar))) , (λ e′ → ⊥-elim (<-irrefl e′ (<-≤-trans (Arr.boundI ar) src≤)))) , _)))
               []ᵖ (λ m → m)
      , pr₁
      where
      -- an old row's block node is below the counter and none of `π`'s,
      -- so the new row does not thread it
      off-new : ∀ {r} → r ∈ KI → (∀ (k : Fin n) → proj₁ (proj₂ r) ≡ atSlot (n ↑ʳ k) → ⊥)
              → ∀ {j} → j ∈ blockNodes (proj₂ (proj₂ (proj₂ r))) → pathHasNode j full ≡ true → ⊥
      off-new {r} r∈ ns {j} b h with ib-split {Γ = Γ} κ blk (has-node {k = j} full (subst T (sym h) tt))
      ... | inj₁ b′ = <⇒≱ (fresh-rows ruleI r∈ j (node-has (proj₂ (proj₂ (proj₂ r))) (reg-has {Γ = Γ} κ rows r∈ ns b))) (proj₁ (nodes-at b′))
      ... | inj₂ m  = reg-unp {Γ = Γ} κ rows r∈ ns b (rel-vals {Γ = Γ} κ pr m)

      -- the new row's block node is above every old row's
      new-old : ∀ {j} → j ∈ blockNodes full → ∀ {r′} → r′ ∈ KI → pathHasNode j (proj₂ (proj₂ (proj₂ r′))) ≡ true → ⊥
      new-old b r′∈ h = <⇒≱ (fresh-rows ruleI r′∈ _ (subst T (sym h) tt)) (proj₁ (nodes-at b))

      reg-live : LiveAt (stI₂ (KI ++ rowI ∷ []))
      reg-live {r} r∈ sk with ∈-++⁻ KI r∈
      ... | inj₁ m           = LiveRows.rows-live old-live m sk
      ... | inj₂ (here refl) = cold-live

      S₂ : Store κ sP₂ (stP₂ (KP ++ rowP ∷ [])) sI₁ (stI₂ (KI ++ rowI ∷ []))
      S₂ = record
        { π = π ; π-keys = π-keys ; π-vals = π-vals
        ; pairs-below = proj₁ pairs-below , weak₂ node≤ (proj₂ pairs-below)
        ; sources = partner ∷ᵖ sources
        ; numbers = dyn~ bP bI ∷ᵖ numbers
        ; distinct = apart (proj₁ bounded) ∷ᴾ proj₁ distinct , apart (weak {f = λ x → x} src≤ (proj₂ bounded)) ∷ᴾ proj₂ distinct
        ; sync = (ticks≡ , ranked-top sources (Named.ords-below (proj₁ named)) (weak {f = λ x → x} ord≤ (Named.ords-below (proj₂ named)))) ∷ˢ sync
        ; rows = reg-snoc {Γ = Γ} κ (reg-cons {Γ = Γ} κ rows₁) new-row
        ; dlv-alike = spent-snoc {Γ = Γ} κ (reg-cons {Γ = Γ} κ rows₁) new-row (spent-cons {Γ = Γ} κ rows₁ (M.spentM o rows dlv-alike))
                        (trans (none-below (Named.dlv-below (proj₁ named))) (sym (none-below (weak {f = λ x → x} rid≤ (Named.dlv-below (proj₂ named))))))
        ; dying-alike = spent-snoc {Γ = Γ} κ (reg-cons {Γ = Γ} κ rows₁) new-row (spent-cons {Γ = Γ} κ rows₁ (M.spentM o rows dying-alike))
                        (trans (member-below (Named.dying-below (proj₁ named))) (sym (member-below (weak {f = λ x → x} src≤ (Named.dying-below (proj₂ named))))))
        ; latches = latches ; dying-done = dying-done
        ; bounded = n<1+n _ ∷ᵃ mapᵃ m<n⇒m<1+n (proj₁ bounded) , src< ∷ᵃ weak {f = λ x → x} s≤ (proj₂ bounded)
        ; swept = trans (guard-new KP rowP lP (same-refl src)) (sym (guard-new KI rowI lI (same-refl src′)))
                  ∷ᵖ swept-snoc {K = KP} {KI} {rowP} {rowI} swept (proj₁ bounded) (weak {f = λ x → x} src≤ (proj₂ bounded))
        ; uncut = ++⁺ᵃ (proj₁ uncut) (none-below (Named.cut-below (proj₁ named)) ∷ᵃ []ᵃ)
                , ++⁺ᵃ (proj₂ uncut) (none-below (weak {f = λ x → x} rid≤ (Named.cut-below (proj₂ named))) ∷ᵃ []ᵃ)
        ; named = named-src (proj₁ named) (n≤1+n _) (n≤1+n _) (n≤1+n _) (n<1+n _)
                    (++⁺ᵃ (mapᵃ m<n⇒m<1+n (Named.srcs-below (proj₁ named))) (n<1+n _ ∷ᵃ []ᵃ))
                , named-src (proj₂ named) s≤ o≤ r≤ ord<
                    (++⁺ᵃ (weak {f = λ r → regSource (proj₁ (proj₂ r))} s≤ (Named.srcs-below (proj₂ named))) (src< ∷ᵃ []ᵃ))
        ; rids = ++⁺ᴾ (proj₁ rids) ([]ᵃ ∷ᴾ []ᴾ) (mapᵃ (λ lt → <⇒≢ lt ∷ᵃ []ᵃ) (proj₁ fresh-ids))
               , ++⁺ᴾ (proj₂ rids) ([]ᵃ ∷ᴾ []ᴾ) (mapᵃ (λ lt → <⇒≢ lt ∷ᵃ []ᵃ) (weak {f = λ r → proj₁ r} rid≤ (proj₂ fresh-ids)))
        ; fresh-ids = ++⁺ᵃ (mapᵃ m<n⇒m<1+n (proj₁ fresh-ids)) (n<1+n _ ∷ᵃ []ᵃ)
                    , ++⁺ᵃ (weak {f = λ r → proj₁ r} r≤ (proj₂ fresh-ids)) (rid< ∷ᵃ []ᵃ)
        ; above = ++⁺ᵃ (proj₁ above) (T-true (≤⇒≤ᵇ (<⇒≤ bP)) ∷ᵃ []ᵃ) , ++⁺ᵃ (proj₂ above) (T-true (≤⇒≤ᵇ (<⇒≤ bI)) ∷ᵃ []ᵃ)
        ; census = λ i h → census-snoc {K = KI} rowI (sameSource-no (<⇒≢ (<-trans (raw<ₙ i) bI))) (sameSource-no (<⇒≢ (<-trans (stamped< i) bI)))
                                         (census i h)
        ; owned = ++⁺ᵃ (tabulateᵃ (λ {r} r∈ ns {j} b → ++⁺ᵃ (lookupᵃ owned r∈ ns b) ((λ h → ⊥-elim (off-new r∈ ns b h)) ∷ᵃ []ᵃ)))
                       ((λ _ {j} b → ++⁺ᵃ (tabulateᵃ (λ r′∈ h → ⊥-elim (new-old b r′∈ h))) ((λ _ → refl) ∷ᵃ []ᵃ)) ∷ᵃ []ᵃ)
        ; ruleP = rP ; ruleI = rI ; scripts = scripts ; live-outer = live reg-live
        }

    -- the two registrations agree on whether they are spent
    at : (cP cI : Bool) → cP ≡ cI → (cI ≡ false → LiveOn full NI)
       → Rule sP₂ (stP₂ (if cP then KP else KP ++ rowP ∷ [])) → Rule sI₁ (stI₂ (if cI then KI else KI ++ rowI ∷ []))
       → Σ (After S ([] , sP₂ , stP₂ (if cP then KP else KP ++ rowP ∷ [])) ([] , sI₁ , stI₂ (if cI then KI else KI ++ rowI ∷ []))) λ A
           → PathRel κ (Store.π (After.store A)) (EvalSt.nodes stP) NI p q
    at true  true  refl _  = spent
    at false false refl lq = registered (lq refl)

  -- A COLD READ'S ROWS REGISTERED: the plain row and the impl's through
  -- its block relate as `cold~`, the tails stay related, and both paths
  -- stay sound where the prefix folds down them
  cold-register : ∀ {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei} (S : St sP stP sI stI)
                    {lo s} {p : Path Γ lo s t} {q : Path (plainᵏ Γ κ) (n + lo) (emitᵗ s) (emitᵗ t)}
                → (pr : PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q)
                → Sound p sP stP → Sound q sI stI → LiveIf q (EvalSt.nodes stI)
                → ∀ {now} (pendP : List (ℕ × Val Γ s)) {vs rI}
                → (B : ColdBlock S q now (record { source = freshId sourceᵏ (Sched.mint sP) ; ordinal = freshId ordinalᵏ (Sched.mint sP)
                                                 ; elemTy = s ; pending = pendP }) vs rI)
                → let module R = Reg S pr pendP B
                      stP′ = register R.rid (atDyn R.src lo) p stP
                      stI′ = register (ColdBlock.rid′ B) (atDyn (ColdBlock.src′ B) (n + lo)) (ColdBlock.full B) (record stI { nodes = ColdBlock.NI B })
                  in Σ (After S ([] , R.sP₂ , stP′) ([] , R.sI₁ , stI′)) λ A
                       → PathRel κ (Store.π (After.store A)) (EvalSt.nodes stP) (ColdBlock.NI B) p q
                       × Sound p R.sP₂ stP′ × Sound q R.sI₁ stI′
  cold-register {sP} {stP} {sI} {stI} S {lo} {s} {p} {q} pr soP soI lv pendP B =
    let X = R.at (spentOn p (EvalSt.nodes stP)) (spentOn full NI)
                 (trans (path-spent {Γ = Γ} κ R.pr₁) (sym (ib-spent {Γ = Γ} κ blk NI)))
                 (λ sp → walks-live (LiveIf.run (live-if-agree q {EvalSt.nodes stI} {NI} (λ k h → kept k (Sound.fresh-path soI k h)) lv)
                                       (trans (sym (ib-spent {Γ = Γ} κ blk NI)) sp)))
                 (Sound.ruled soP′) (Sound.ruled soI′)
    in proj₁ X , proj₂ X , soP′ , soI′
    where
    module R = Reg S pr pendP B
    open ColdBlock B
    soP′ : Sound p R.sP₂ (register R.rid (atDyn R.src lo) p stP)
    soP′ = register-sound {κ = p} {sched = R.sP₂} {sched′ = R.sP₂} R.rid (atDyn R.src lo) p ≤-refl refl (λ k h → inj₁ h)
             Sound.distinct (sub-ot (λ r∈ → r∈) ≤-refl soP)
    soI′ : Sound q R.sI₁ (register rid′ (atDyn src′ (n + lo)) full (record stI { nodes = NI }))
    soI′ = register-sound {κ = q} {sched = record sI { live = R.lI ∷ Sched.live sI }} {sched′ = R.sI₁} rid′ (atDyn src′ (n + lo)) full
             node≤ (ib-end {Γ = Γ} κ blk) cls (λ so → dist (Sound.distinct so)) (sub-ot (λ r∈ → r∈) ≤-refl soI)
      where
      cls : ∀ k → T (pathHasNode k full) → T (pathHasNode k q) ⊎ (nodeCt sI ≤ k × k < freshId nodeᵏ mI)
      cls k h with ib-split {Γ = Γ} κ blk (has-node full h)
      ... | inj₁ b = inj₂ (nodes-at b)
      ... | inj₂ m = inj₁ (node-has q m)
