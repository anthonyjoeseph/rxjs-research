------------------------------------------------------------------
-- A POP LEAVES THE LIVE LISTS RELATED.  Both lists give up one value at
-- the same place and every other source stays as it stood, so a relation
-- that holds source for source holds again, a source keeps its number,
-- and a registration that names a pair of sources at a place still names
-- it.
------------------------------------------------------------------
module Simulation.Pop where

open import Data.List    using (List; []; _∷_; map)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List.Relation.Unary.All using (All) renaming (map to mapᵃ)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Nat     using (_<_)
open import Data.Sum     using (inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)

open import Rx.Exp       using (Ctx; Closed)
open import Rx.Mint      using (counter; sourceᵏ)
open import Data.Nat.Properties using (≤-refl)
open import Rx.Evaluator.Reducible.Support using (sub-rule)
open import Rx.Evaluator using (LiveSource; Arrival; Sched; EvalSt; NodeId; NodeState; schedGo; schedHeadOf; cascadeOpen)
open import SExp.Syntax  using (Kinds; plainᵏ; emitᵗ)
open import Simulation.Schedules using (Sync; Popped; pop; sched-pop; PopPair; here; there)
open import Simulation.Stores using (guard-src; guardOf; Src; data~; SrcNum; SrcPair; RowRel; MachRow; hot~; RegRel; []; _∷_; read~; cold~; defer~; mach; Store)
  renaming (here to sp-here; there to sp-there)

-- the rest of two lists a relation holds for, given their first elements
pw-tail : ∀ {A B : Set} {R : A → B → Set} {xs ys x y xs′ ys′} → Pointwise R xs ys → xs ≡ x ∷ xs′ → ys ≡ y ∷ ys′ → Pointwise R xs′ ys′
pw-tail (_ ∷ pw) refl refl = pw

module _ {k} {Δ : Ctx k} where

  -- what the head of a source shows of the rest: its first pending value
  -- gone, everything else as it was
  head-shape : ∀ (l : LiveSource Δ) {a l₂} → schedHeadOf l ≡ inj₂ (a , l₂)
             → Σ _ λ t → Σ _ λ v → Σ _ λ ps → LiveSource.pending l ≡ (t , v) ∷ ps × l₂ ≡ record l { pending = ps }
  head-shape l eq with LiveSource.pending l
  head-shape l refl | (t , v) ∷ ps = t , v , ps , refl , refl

  head-keeps : ∀ (l : LiveSource Δ) {a l₂} → schedHeadOf l ≡ inj₂ (a , l₂) → LiveSource.source l₂ ≡ LiveSource.source l
  head-keeps l eq with head-shape l eq
  ... | _ , _ , _ , _ , refl = refl

  -- the arrival a source offers is numbered and typed as the source
  head-arr : ∀ (l : LiveSource Δ) {a l₂} → schedHeadOf l ≡ inj₂ (a , l₂)
           → Arrival.source a ≡ LiveSource.source l₂ × Arrival.elemTy a ≡ LiveSource.elemTy l₂
  head-arr l eq with LiveSource.pending l
  head-arr l refl | (t , v) ∷ ps = refl , refl

module _ {k} {Δ : Ctx k} {k′} {Δ′ : Ctx k′} where

  -- the sources a pop leaves are numbered as they were
  pp-sources : ∀ {a a′} {ls rs : List (LiveSource Δ)} {ls′ rs′ : List (LiveSource Δ′)} → PopPair a a′ ls rs ls′ rs′
             → map LiveSource.source rs ≡ map LiveSource.source ls × map LiveSource.source rs′ ≡ map LiveSource.source ls′
  pp-sources (here {l} {l₂} {l′} {l₂′} h h′) = cong (_∷ _) (head-keeps l h) , cong (_∷ _) (head-keeps l′ h′)
  pp-sources (there pp) = cong (_ ∷_) (proj₁ (pp-sources pp)) , cong (_ ∷_) (proj₂ (pp-sources pp))

  -- a relation that survives the popped pair surviving, source for source
  pp-pointwise : ∀ {R : LiveSource Δ → LiveSource Δ′ → Set}
                   (step : ∀ {l l′ a a′ l₂ l₂′} → R l l′ → schedHeadOf l ≡ inj₂ (a , l₂) → schedHeadOf l′ ≡ inj₂ (a′ , l₂′) → R l₂ l₂′)
                   {a a′ ls rs ls′ rs′} → PopPair a a′ ls rs ls′ rs′ → Pointwise R ls ls′ → Pointwise R rs rs′
  pp-pointwise step (here h h′) (r ∷ rs) = step r h h′ ∷ rs
  pp-pointwise step (there pp)  (r ∷ rs) = r ∷ pp-pointwise step pp rs

module _ {n} {Γ : Ctx n} (κ : Kinds n) where

  -- two sources at one place in the live lists keep it
  sp-pop : ∀ {a a′} {ls rs : List (LiveSource Γ)} {ls′ rs′ : List (LiveSource (plainᵏ Γ κ))} {s s′ u u′}
         → PopPair a a′ ls rs ls′ rs′ → SrcPair κ ls ls′ s s′ u u′ → SrcPair κ rs rs′ s s′ u u′
  sp-pop (here {l} {l₂} {l′} {l₂′} h h′) sp-here with head-shape l h | head-shape l′ h′
  ... | _ , _ , _ , _ , refl | _ , _ , _ , _ , refl = sp-here
  sp-pop (here h h′) (sp-there q) = sp-there q
  sp-pop (there pp)  sp-here      = sp-here
  sp-pop (there pp)  (sp-there q) = sp-there (sp-pop pp q)

  -- the pair a pop took from stands at one place in the lists it leaves, as the arrivals it offered
  pp-popped : ∀ {a a′} {ls rs : List (LiveSource Γ)} {ls′ rs′ : List (LiveSource (plainᵏ Γ κ))}
            → PopPair a a′ ls rs ls′ rs′ → SrcPair κ rs rs′ (Arrival.source a) (Arrival.source a′) (Arrival.elemTy a) (Arrival.elemTy a′)
  pp-popped (here {l} {l₂} {l′} {l₂′} h h′) with head-arr l h | head-arr l′ h′
  ... | es , et | es′ , et′ rewrite es | et | es′ | et′ = sp-here
  pp-popped (there pp) = sp-there (pp-popped pp)

  -- a source that gave up its first pending value is still related to its partner
  src-pop : ∀ (l : LiveSource Γ) (l′ : LiveSource (plainᵏ Γ κ)) {a a′ l₂ l₂′} → Src κ l l′
          → schedHeadOf l ≡ inj₂ (a , l₂) → schedHeadOf l′ ≡ inj₂ (a′ , l₂′) → Src κ l₂ l₂′
  src-pop l l′ s h h′ with head-shape l h | head-shape l′ h′
  src-pop l l′ (data~ eq pw sty) h h′ | _ , _ , _ , pe , refl | _ , _ , _ , pe′ , refl = data~ eq (pw-tail pw pe′ pe) sty
  src-pop l l′ (defer~ lt pw) h h′ | _ , _ , _ , pe , refl | _ , _ , _ , pe′ , refl = defer~ lt (pw-tail pw pe′ pe)

  num-pop : ∀ (l : LiveSource Γ) (l′ : LiveSource (plainᵏ Γ κ)) {a a′ l₂ l₂′}
          → SrcNum κ (LiveSource.source l) (LiveSource.source l′)
          → schedHeadOf l ≡ inj₂ (a , l₂) → schedHeadOf l′ ≡ inj₂ (a′ , l₂′)
          → SrcNum κ (LiveSource.source l₂) (LiveSource.source l₂′)
  num-pop l l′ nm h h′ = subst₂ (SrcNum κ) (sym (head-keeps l h)) (sym (head-keeps l′ h′)) nm

  module _ {t} (π : List (NodeId × List NodeId)) (NP : List (NodeId × NodeState Γ)) (NI : List (NodeId × NodeState (plainᵏ Γ κ)))
           {a a′} {LP RS : List (LiveSource Γ)} {LI RS′ : List (LiveSource (plainᵏ Γ κ))} (pp : PopPair a a′ LP RS LI RS′) where

    mach-pop : ∀ {r′} → MachRow κ π {t} NP NI LP LI r′ → MachRow κ π {t} NP NI RS RS′ r′
    mach-pop (hot~ hot ib eq) = hot~ hot ib eq

    row-pop : ∀ {r r′} → RowRel κ π {t} NP NI LP LI r r′ → RowRel κ π {t} NP NI RS RS′ r r′
    row-pop (read~ hk pr eq)              = read~ hk pr eq
    row-pop (cold~ sp ib pr eq)           = cold~ (sp-pop pp sp) ib pr eq
    row-pop (defer~ sp pi ln lni pr eq)   = defer~ (sp-pop pp sp) pi ln lni pr eq

    regrel-pop : ∀ {rg rg′} → RegRel κ π {t} NP NI LP LI rg rg′ → RegRel κ π {t} NP NI RS RS′ rg rg′
    regrel-pop []         = []
    regrel-pop (r ∷ q)    = row-pop r ∷ regrel-pop q
    regrel-pop (mach m q) = mach (mach-pop m) (regrel-pop q)

  -- A POP LEAVES THE STORES RELATED: the popped sources keep their
  -- numbers and places, each giving up one pending value, and the
  -- cascade's ledger opens empty on both sides.
  pop-store : ∀ {t} {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)}
                {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei}
    → Store κ sP stP sI stI
    → ∀ {a a′ rs rs′} → schedGo (Sched.live sP) ≡ inj₂ (a , rs) → schedGo (Sched.live sI) ≡ inj₂ (a′ , rs′)
    → Sync rs rs′
    → Store κ (record sP { live = rs }) (cascadeOpen stP) (record sI { live = rs′ }) (cascadeOpen stI)
  pop-store {sP = sP} {stP = stP} {sI = sI} {stI = stI} s ex ex′ sy
    with subst₂ (Popped (Src κ) (Sched.live sP) (Sched.live sI)) ex ex′ (sched-pop (Store.sync s) (Store.sources s))
  ... | pop _ _ _ _ _ _ _ _ pp = record
    { π        = Store.π s
    ; π-keys   = Store.π-keys s
    ; π-vals   = Store.π-vals s
    ; pairs-below = Store.pairs-below s
    ; sources  = pp-pointwise (λ {l} {l′} r h h′ → src-pop l l′ r h h′) pp (Store.sources s)
    ; numbers  = pp-pointwise {R = λ l l′ → SrcNum κ (LiveSource.source l) (LiveSource.source l′)}
                   (λ {l} {l′} r h h′ → num-pop l l′ r h h′) pp (Store.numbers s)
    ; distinct = subst Unique (sym (proj₁ (pp-sources pp))) (proj₁ (Store.distinct s))
               , subst Unique (sym (proj₂ (pp-sources pp))) (proj₂ (Store.distinct s))
    ; sync     = sy
    ; rows     = regrel-pop _ _ _ pp (Store.rows s)
    ; latches  = Store.latches s
    ; bounded  = subst (All (_< counter (Sched.mint sP) sourceᵏ)) (sym (proj₁ (pp-sources pp))) (proj₁ (Store.bounded s))
               , subst (All (_< counter (Sched.mint sI) sourceᵏ)) (sym (proj₂ (pp-sources pp))) (proj₂ (Store.bounded s))
    ; swept    = pp-pointwise {R = λ l l′ → guardOf (EvalSt.registry stP) l ≡ guardOf (EvalSt.registry stI) l′}
                   (λ {l} {l′} {_} {_} {l₂} {l₂′} g h h′ → trans (guard-src (EvalSt.registry stP) {l} {l₂} (head-keeps l h))
                                              (trans g (sym (guard-src (EvalSt.registry stI) {l′} {l₂′} (head-keeps l′ h′)))))
                   pp (Store.swept s)
    ; uncut    = mapᵃ (λ _ → refl) (proj₁ (Store.uncut s)) , mapᵃ (λ _ → refl) (proj₂ (Store.uncut s))
    ; rids     = Store.rids s
    ; fresh-ids = Store.fresh-ids s
    ; above    = Store.above s
    ; census   = Store.census s
    ; owned    = Store.owned s
    ; ruleP    = sub-rule (λ r∈ → r∈) ≤-refl (Store.ruleP s)
    ; ruleI    = sub-rule (λ r∈ → r∈) ≤-refl (Store.ruleI s)
    ; scripts  = Store.scripts s
    }
