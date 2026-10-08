------------------------------------------------------------------
-- WHAT A RUN STEP KEEPS OF THE STORES, A PASS'S AND A SUBSCRIBE'S
-- ALIKE.  A cascade's pass and a subscribe's walk both start from
-- related stores and end in related stores, with the chains they did
-- not reach still paired, the popped arrival's pair against the rows
-- as it was, related values sent rootward, and every node pairing
-- they found kept.  A pass subscribes inners, so the two are one
-- invariant or the pass cannot call the walk.
------------------------------------------------------------------
module Simulation.After where

open import Data.Bool.ListAction using (any)
open import Data.Bool    using (true; false; _∧_; _∨_)
open import Data.Bool.Properties using (∧-zeroʳ)
open import Data.List    using (List; []; _∷_; _++_; concat; map; concatMap)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; ++⁺)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to mapᵃ)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to ++⁺ᵃ)
open import Data.List.Relation.Unary.Any using (there)
open import Data.List.Relation.Unary.AllPairs using (_∷_)
open import Data.Nat     using (ℕ; suc; _<_; _≡ᵇ_)
open import Data.Nat.Properties using (n≤1+n; n<1+n; m<n⇒m<1+n; <-irrefl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Empty   using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans; cong; cong₂; subst₂)

open import Rx.Prim      using (Id)
open import Rx.Exp       using (Ctx; Closed; Val; uniqᵗ)
open import Rx.Mint      using (setAt; nodeᵏ)
open import Rx.Evaluator using (Stream; Sched; EvalSt; RegId; RegRow; NodeId; skipᵇ; regSource; memberSource)
open import Rx.Evaluator.Freshness using (nodeCt)
open import Rx.Evaluator.Reducible.Support using (sub-rule; fresh-rows)
open import SExp.Syntax  using (Kinds; plainᵏ; emitᵗ)
open import SExp.Plain   using (plainValues)
open import SExp.InstEmit using (instEmitᵗ)
open import SExp.InstEmit.Decode using (decodeEmits)
open import Batchable.Inst-Extract using (instExtract)
open import Simulation.Lockstep using (concat-++; values-++; decode-++; extract-++)
open import Simulation.Stores using (V; RegRel; Partners; Store; Arr; spent-partner; named-node)
open import Simulation.Grow using (OffRow; fresh-off-row; regG; partG; arrG; spentG)

-- what a run sends to its root, read as values: the plain run's in
-- order, the impl's decoded and each paired with its instant
readᴾ : ∀ {n} {Γ : Ctx n} {t} → Stream Γ t → List (Val Γ t)
readᴾ s = plainValues (concat s)

readᴵ : ∀ {m} {Γ′ : Ctx m} {t} → Stream Γ′ (instEmitᵗ uniqᵗ t) → List (Id × Val Γ′ t)
readᴵ s = instExtract (decodeEmits (concat s))

readᴾ-++ : ∀ {n} {Γ : Ctx n} {t} (xs ys : Stream Γ t) → readᴾ (xs ++ ys) ≡ readᴾ xs ++ readᴾ ys
readᴾ-++ xs ys = trans (cong plainValues (concat-++ xs ys)) (values-++ (concat xs) (concat ys))

readᴵ-++ : ∀ {m} {Γ′ : Ctx m} {t} (xs ys : Stream Γ′ (instEmitᵗ uniqᵗ t)) → readᴵ (xs ++ ys) ≡ readᴵ xs ++ readᴵ ys
readᴵ-++ xs ys =
  trans (cong (λ z → instExtract (decodeEmits z)) (concat-++ xs ys))
 (trans (cong instExtract (decode-++ (concat xs) (concat ys)))
        (extract-++ (decodeEmits (concat xs)) (decodeEmits (concat ys))))

-- every node a pairing lists, below the counter, apart from it
below-keys : ∀ {π : List (NodeId × List NodeId)} {c} → All (λ e → proj₁ e < c) π → All (_< c) (map proj₁ π)
below-keys []       = []
below-keys (a ∷ as) = a ∷ below-keys as

below-vals : ∀ {π : List (NodeId × List NodeId)} {c} → All (λ e → All (_< c) (proj₂ e)) π → All (_< c) (concatMap proj₂ π)
below-vals []       = []
below-vals (a ∷ as) = ++⁺ᵃ a (below-vals as)

apart : ∀ {c : ℕ} {xs} → All (_< c) xs → All (λ x → c ≡ x → ⊥) xs
apart = mapᵃ (λ lt e → <-irrefl (sym e) lt)

-- A CHAIN PAIR THE PASS HAS NOT REACHED: cut on both sides, or on
-- neither and partnered by the registries' relation
-- a cut chain is skipped; an uncut one, exactly when its source has
-- ended and it took that end
skip-cut : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s rid} {st : EvalSt e}
         → any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ true → skipᵇ s rid st ≡ true
skip-cut {s = s} {rid} {st} c =
  cong (λ b → b ∨ (memberSource s (EvalSt.dying st) ∧ any (_≡ᵇ rid) (EvalSt.delivered st))) c

skip-live : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s rid} {st : EvalSt e}
          → any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ false
          → skipᵇ s rid st ≡ (memberSource s (EvalSt.dying st) ∧ any (_≡ᵇ rid) (EvalSt.delivered st))
skip-live {s = s} {rid} {st} c =
  cong (λ b → b ∨ (memberSource s (EvalSt.dying st) ∧ any (_≡ᵇ rid) (EvalSt.delivered st))) c

skip-quiet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s rid} {st : EvalSt e}
           → any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ false → any (_≡ᵇ rid) (EvalSt.delivered st) ≡ false
           → skipᵇ s rid st ≡ false
skip-quiet {s = s} {rid} {st} c d =
  trans (skip-live {s = s} {rid} {st} c) (trans (cong (memberSource s (EvalSt.dying st) ∧_) d) (∧-zeroʳ _))

PairedR : ∀ {n} {Γ : Ctx n} {t} {κ : Kinds n} {π NP NI LP LI rs rs′}
        → RegRel κ π {t} NP NI LP LI rs rs′ → List RegId → List RegId
        → RegRow Γ t → RegRow (plainᵏ Γ κ) (emitᵗ t) → Set
PairedR {κ = κ} rr CP CI x x′ =
    (any (_≡ᵇ proj₁ x) CP ≡ true × any (_≡ᵇ proj₁ x′) CI ≡ true)
  ⊎ (any (_≡ᵇ proj₁ x) CP ≡ false × any (_≡ᵇ proj₁ x′) CI ≡ false
     × Partners κ _ _ _ _ _ rr x x′)

module Kept {n} {Γ : Ctx n} (κ : Kinds n) {t} {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)} where

  St : Sched Γ → EvalSt ep → Sched (plainᵏ Γ κ) → EvalSt ei → Set
  St = Store κ

  -- the chains not reached stay paired
  Keeps : ∀ {sP stP sI stI sP₁ stP₁ sI₁ stI₁}
        → St sP stP sI stI → St sP₁ stP₁ sI₁ stI₁ → Set
  Keeps {stP = stP} {stI = stI} {stP₁ = stP₁} {stI₁ = stI₁} S S₁ =
    ∀ {x x′}
    → PairedR (Store.rows S) (EvalSt.cancelled stP) (EvalSt.cancelled stI) x x′
    → PairedR (Store.rows S₁) (EvalSt.cancelled stP₁) (EvalSt.cancelled stI₁) x x′

  -- the popped arrival's pair against the rows stays as it was
  Persists : ∀ {sP stP sI stI sP₁ stP₁ sI₁ stI₁}
           → St sP stP sI stI → St sP₁ stP₁ sI₁ stI₁ → Set
  Persists S S₁ = ∀ {s s′ u u′} → Arr S s s′ u u′ → Arr S₁ s s′ u u′

  -- a fan-out's skip test reads paired rows alike: both cut, or neither
  -- and partners, whose ends and deliveries the stores spend alike
  skip-alike : ∀ {sP stP sI stI} (S : St sP stP sI stI) {x x′}
             → PairedR (Store.rows S) (EvalSt.cancelled stP) (EvalSt.cancelled stI) x x′
             → skipᵇ (regSource (proj₁ (proj₂ x))) (proj₁ x) stP ≡ skipᵇ (regSource (proj₁ (proj₂ x′))) (proj₁ x′) stI
  skip-alike {stP = stP} {stI = stI} S {x} {x′} (inj₁ (c , c′)) =
    trans (skip-cut {s = regSource (proj₁ (proj₂ x))} {proj₁ x} {stP} c) (sym (skip-cut {s = regSource (proj₁ (proj₂ x′))} {proj₁ x′} {stI} c′))
  skip-alike {stP = stP} {stI = stI} S {x} {x′} (inj₂ (c , c′ , p)) =
    trans (skip-live {s = regSource (proj₁ (proj₂ x))} {proj₁ x} {stP} c)
          (trans (cong₂ _∧_ (spent-partner κ _ _ _ _ _ (Store.rows S) p (Store.dying-alike S))
                            (spent-partner κ _ _ _ _ _ (Store.rows S) p (Store.dlv-alike S)))
                 (sym (skip-live {s = regSource (proj₁ (proj₂ x′))} {proj₁ x′} {stI} c′)))

  -- WHAT A PASS KEEPS: related stores after, the unreached chains
  -- paired, the arrival's pair against the rows, related values sent
  -- rootward, and every node pairing it found
  record After {sP stP sI stI} (S : St sP stP sI stI)
               (rP : Stream Γ t × Sched Γ × EvalSt ep)
               (rI : Stream (plainᵏ Γ κ) (emitᵗ t) × Sched (plainᵏ Γ κ) × EvalSt ei) : Set where
    constructor after
    field
      store  : Store κ (proj₁ (proj₂ rP)) (proj₂ (proj₂ rP)) (proj₁ (proj₂ rI)) (proj₂ (proj₂ rI))
      keeps  : Keeps S store
      persists : Persists S store
      values : Pointwise (λ x w → V κ t (proj₂ x) w) (readᴵ (proj₁ rI)) (readᴾ (proj₁ rP))
      grows  : ∀ {x} → x ∈ Store.π S → x ∈ Store.π store

  -- one pass, then another from where it left the stores
  _⨾_ : ∀ {sP stP sI stI} {S : St sP stP sI stI} {o₁ sP₁ stP₁ i₁ sI₁ stI₁ rP rI}
      → (A : After S (o₁ , sP₁ , stP₁) (i₁ , sI₁ , stI₁)) → After (After.store A) rP rI
      → After S (o₁ ++ proj₁ rP , proj₂ rP) (i₁ ++ proj₁ rI , proj₂ rI)
  -- by projection, so that the two together leave the second's store
  _⨾_ {o₁ = o₁} {i₁ = i₁} {rP = rP} {rI = rI} A B =
    after (After.store B) (λ {a} {a′} x → After.keeps B {a} {a′} (After.keeps A {a} {a′} x))
      (λ ar → After.persists B (After.persists A ar))
      (subst₂ (Pointwise (λ x w → V κ t (proj₂ x) w)) (sym (readᴵ-++ i₁ (proj₁ rI))) (sym (readᴾ-++ o₁ (proj₁ rP)))
              (++⁺ (After.values A) (After.values B)))
      (λ x → After.grows B (After.grows A x))

  -- AN INNER'S PAIR MINTED ON BOTH SIDES: the node counters move, and
  -- the pair they hand out joins `π`, apart from every node a row names
  Minted : ∀ {sP stP sI stI} → St sP stP sI stI → List (NodeId × List NodeId)
  Minted {sP} {sI = sI} S = (nodeCt sP , nodeCt sI ∷ []) ∷ Store.π S

  mint-off : ∀ {sP stP sI stI} (S : St sP stP sI stI) {r′} → r′ ∈ EvalSt.registry stI
           → OffRow {Γ = Γ} κ (Store.π S) (Minted S) {emitᵗ t} r′
  mint-off {sP} S {r′} r∈ = fresh-off-row {Γ = Γ} {κ = κ} {π = Store.π S} {j = nodeCt sP} r′ (fresh-rows (Store.ruleI S) r∈)

  mint-pair : ∀ {sP stP sI stI} (S : St sP stP sI stI)
            → St (record sP { mint = setAt nodeᵏ (suc (nodeCt sP)) (Sched.mint sP) }) stP
                 (record sI { mint = setAt nodeᵏ (suc (nodeCt sI)) (Sched.mint sI) }) stI
  mint-pair {sP} {sI = sI} S = record
    { π = Minted S
    ; π-keys = apart (below-keys (proj₁ pairs-below)) ∷ π-keys
    ; π-vals = apart (below-vals (proj₂ pairs-below)) ∷ π-vals
    ; pairs-below = n<1+n (nodeCt sP) ∷ mapᵃ m<n⇒m<1+n (proj₁ pairs-below)
                  , (n<1+n (nodeCt sI) ∷ []) ∷ mapᵃ (mapᵃ m<n⇒m<1+n) (proj₂ pairs-below)
    ; sources = sources ; numbers = numbers ; distinct = distinct ; sync = sync
    ; rows = regG κ there (mint-off S) rows
    ; dlv-alike = spentG κ there (mint-off S) rows dlv-alike ; dying-alike = spentG κ there (mint-off S) rows dying-alike
    ; latches = latches ; bounded = bounded ; swept = swept ; uncut = uncut ; named = named-node (proj₁ named) , named-node (proj₂ named) ; rids = rids ; fresh-ids = fresh-ids ; above = above
    ; census = census ; owned = owned
    ; ruleP = sub-rule (λ r∈ → r∈) (n≤1+n (nodeCt sP)) ruleP
    ; ruleI = sub-rule (λ r∈ → r∈) (n≤1+n (nodeCt sI)) ruleI
    ; scripts = scripts
    }
    where open Store S

  -- a step from the minted stores is one from the stores
  unmint : ∀ {sP stP sI stI} {S : St sP stP sI stI} {rP rI} → After (mint-pair S) rP rI → After S rP rI
  unmint {S = S} A =
    after (After.store A)
          (λ { (inj₁ c) → After.keeps A (inj₁ c)
             ; (inj₂ (a , b , pr)) → After.keeps A (inj₂ (a , b , partG κ there (mint-off S) (Store.rows S) pr)) })
          (λ ar → After.persists A (record { boundP = Arr.boundP ar ; boundI = Arr.boundI ar
                                             ; rows = arrG κ there (mint-off S) (Store.rows S) (Arr.rows ar) ; lists = Arr.lists ar }))
          (After.values A) (λ x → After.grows A (there x))
