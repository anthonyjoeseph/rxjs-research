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
open import Data.Bool    using (true; false)
open import Data.List    using (List; _++_; concat)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; ++⁺)
open import Data.List.Relation.Unary.All using () renaming (map to mapᵃ)
open import Data.Nat     using (suc; _≡ᵇ_)
open import Data.Nat.Properties using (n≤1+n; m<n⇒m<1+n)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans; cong; subst₂)

open import Rx.Prim      using (Id)
open import Rx.Exp       using (Ctx; Closed; Val; uniqᵗ)
open import Rx.Mint      using (setAt; nodeᵏ)
open import Rx.Evaluator using (Stream; Sched; EvalSt; RegId; RegRow)
open import Rx.Evaluator.Freshness using (nodeCt)
open import Rx.Evaluator.Reducible.Support using (sub-rule)
open import SExp.Syntax  using (Kinds; plainᵏ; emitᵗ)
open import SExp.Plain   using (plainValues)
open import SExp.InstEmit using (instEmitᵗ)
open import SExp.InstEmit.Decode using (decodeEmits)
open import Batchable.Inst-Extract using (instExtract)
open import Simulation.Lockstep using (concat-++; values-++; decode-++; extract-++)
open import Simulation.Stores using (V; RegRel; Partners; Store; Arr)

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

-- A CHAIN PAIR THE PASS HAS NOT REACHED: cut on both sides, or on
-- neither and partnered by the registries' relation
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

  -- AN INNER'S NODE MINTED ON BOTH SIDES: only the node counters move,
  -- and every node `π` pairs stays below them
  bump : ∀ {sP stP sI stI} → St sP stP sI stI
       → St (record sP { mint = setAt nodeᵏ (suc (nodeCt sP)) (Sched.mint sP) }) stP
            (record sI { mint = setAt nodeᵏ (suc (nodeCt sI)) (Sched.mint sI) }) stI
  bump {sP} {sI = sI} S = record
    { π = π ; π-keys = π-keys ; π-vals = π-vals
    ; pairs-below = mapᵃ m<n⇒m<1+n (proj₁ pairs-below) , mapᵃ (mapᵃ m<n⇒m<1+n) (proj₂ pairs-below)
    ; sources = sources ; numbers = numbers ; distinct = distinct ; sync = sync ; rows = rows
    ; latches = latches ; bounded = bounded ; swept = swept ; uncut = uncut ; above = above
    ; census = census ; owned = owned
    ; ruleP = sub-rule (λ r∈ → r∈) (n≤1+n (nodeCt sP)) ruleP
    ; ruleI = sub-rule (λ r∈ → r∈) (n≤1+n (nodeCt sI)) ruleI
    }
    where open Store S

  -- a step from the bumped stores is one from the stores
  unbump : ∀ {sP stP sI stI} {S : St sP stP sI stI} {rP rI} → After (bump S) rP rI → After S rP rI
  unbump A =
    after (After.store A) (After.keeps A)
          (λ ar → After.persists A (record { boundP = Arr.boundP ar ; boundI = Arr.boundI ar
                                             ; rows = Arr.rows ar ; lists = Arr.lists ar }))
          (After.values A) (After.grows A)
