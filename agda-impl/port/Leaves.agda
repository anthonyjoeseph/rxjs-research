{-# OPTIONS --guardedness #-}

-- WHAT A REST LEAVES RUNNING, AND WHEN TWO LEAVE ALIKE: the next pin a
-- rest steps to, a rest's shape, and two nodes whose rests run alike at
-- every depth.
module port.Leaves where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)

open import denotation.MonotonicList using (Agree; Agreeᵀ; agreeᵀ-refl; agreeᵀ-sym; agreeᵀ-trans;
  stopᵀ; pin⁼; idle⁼; skip⁼; hush⁼; agree-refl; tailᴱ)
open import denotation.MonotonicList.Events using (Pos; Tail; Tail∞; pin; idle; _<ᵖ_; _∪_; first;
  <ᵖ-asym; <ᵖ-split; <ᵖ-irrefl; inside)
open import denotation.NonExpansive using (tailᴱ-ne; ∪-ne)
import denotation.Unfold as U
open import port.Deep using (Deep; DeepR; deepR-rest; deep-cutR)
open import port.Placed.Rising using (AtopT)
open import port.Placed.Trail using (SortedT; sortedᵀ)

open Tail∞

-- Two steps alike as rests: the same pin, or none.
data Pinned {Γ} {B C : Set} : U.Step Γ B → U.Step Γ C → Set₁ where
  pinned   : ∀ {k x y} → Pinned (U.skipˢ k x) (U.skipˢ k y)
  unpinned : Pinned U.hushˢ U.hushˢ

-- A rest's shape, all the way down to its rests: it steps as it rests.
data Restful : ∀ {Γ B} → U.Node Γ B → Set₁ where
  rf-idle  : ∀ {Γ B} → Restful (U.idleᶜ {Γ = Γ} {B = B})
  rf-rest  : ∀ {Γ A B} {n : U.Node Γ A} → Restful (U.restᶜ {B = B} n)
  rf-union : ∀ {Γ B} {x y : U.Node Γ B} → Restful x → Restful y → Restful (U.unionᶜ x y)
  rf-burst : ∀ {Γ A B r} {t : U.Node Γ A} → Restful (U.burstingᶜ {B = B} r t)
  rf-under : ∀ {Γ A C B} {s : U.Source Γ A} {b : U.Node (A ∷ Γ) C} → Restful b → Restful (U.underᶜ {B = B} s b)

-- Two nodes leaving alike: what each still runs past an unsubscribe,
-- under every environment the first is in order at, the same at every
-- depth, the second in order when the first is; their rests' next
-- steps pinned alike.
-- `restˢ` and `cutᴺ` are read apart, so the pin is its own field.
record Leaves {Γ A B} (x : U.Node Γ A) (y : U.Node Γ B) : Set₁ where
  constructor leaves
  field agree : ∀ (ρ : U.NEnv Γ) → Deep (U.restᶜ {B = ⊤} x) ρ → ∀ n → Agree n (U.meaning (U.restᶜ {B = ⊤} x) ρ) (U.meaning (U.restᶜ {B = ⊤} y) ρ)
        deep  : ∀ (ρ : U.NEnv Γ) → Deep (U.restᶜ {B = ⊤} x) ρ → Deep (U.restᶜ {B = ⊤} y) ρ
        pins  : Pinned (U.restˢ {B = ⊤} x) (U.restˢ {B = ⊤} y)

-- The order read back, from the witness's rest to the node's: a
-- flatMap's part is in order by its whole meaning, which no rest
-- below it holds, so only an ended source's rest carries it.
Back : ∀ {Γ A B} → U.Node Γ A → U.Node Γ B → Set₁
Back x y = ∀ (ρ : U.NEnv _) → Deep (U.restᶜ {B = ⊤} y) ρ → Deep (U.restᶜ {B = ⊤} x) ρ

-- Leaving alike both ways.
Twin : ∀ {Γ A B} → U.Node Γ A → U.Node Γ B → Set₁
Twin x y = Leaves x y × Back x y

private
  union-pinned : ∀ {Γ B C} {x y : U.Node Γ B} {sx sy} {x′ y′ : U.Node Γ C} {sx′ sy′}
               → Pinned sx sx′ → Pinned sy sy′ → Pinned (U.unionˢ x sx y sy) (U.unionˢ x′ sx′ y′ sy′)
  union-pinned (pinned {k}) (pinned {k′}) with k <ᵖ k′
  ... | true  = pinned
  ... | false = pinned
  union-pinned pinned   unpinned = pinned
  union-pinned unpinned q        = q

  under-pinned : ∀ {Γ A D B C} (s : U.Source Γ A) (st : U.Step (A ∷ Γ) D) → Pinned (U.underˢ {B = B} s st) (U.underˢ {B = C} s st)
  under-pinned s (U.skipˢ _ _) = pinned
  under-pinned s _              = unpinned

mutual
  rest-pinned : ∀ {Γ A B C} (c : U.Node Γ A) → Pinned (U.restˢ {B = B} c) (U.restˢ {B = C} c)
  rest-pinned (U.framesᶜ _ _ _)               = unpinned
  rest-pinned (U.burstᶜ _ _ _ _)              = unpinned
  rest-pinned (U.ofᶜ _ _ _)                   = unpinned
  rest-pinned (U.mapᶜ _ c)                    = rest-pinned c
  rest-pinned (U.scanᶜ _ _ c)                 = rest-pinned c
  rest-pinned (U.takeWhileᶜ _ _ c)            = rest-pinned c
  rest-pinned (U.flatMapᶜ _ _ o ls _ p)       = union-pinned (restᴹ-pinned o) (union-pinned (rests-pinned ls) (rest-pinned p))
  rest-pinned (U.joinᶜ _ _ _ _)               = unpinned
  rest-pinned {A = A} (U.connectᶜ r b (U.live s))    = union-pinned (bursts-pinned r s (U.step s)) (under-pinned (U.live s) (U.restˢ {B = A} b))
  rest-pinned {A = A} (U.connectᶜ r b (U.ended c t)) = union-pinned (bursts-pinned r t (U.step t)) (under-pinned (U.ended c t) (U.restˢ {B = A} b))
  rest-pinned (U.deferᶜ _ _ _)                = unpinned
  rest-pinned (U.endingᶜ _ n)                 = rest-pinned n
  rest-pinned (U.restᶜ n)                     = rest-pinned n
  rest-pinned U.idleᶜ                         = unpinned
  rest-pinned (U.unionᶜ x y)                  = union-pinned (rest-pinned x) (rest-pinned y)
  rest-pinned (U.burstingᶜ r t)               = bursts-pinned r t (U.step t)
  rest-pinned (U.underᶜ {C = D} s b)          = under-pinned s (U.restˢ {B = D} b)

  private
    bursts-pinned : ∀ {Γ A B C} (r : Pos) (t : U.Node Γ A) (st : U.Step Γ A) → Pinned (U.burstsˢ {B = B} r t st) (U.burstsˢ {B = C} r t st)
    bursts-pinned r t (U.outˢ k _ _) with inside r k
    ... | true  = pinned
    ... | false = rest-pinned t
    bursts-pinned r t (U.skipˢ k _) with inside r k
    ... | true  = pinned
    ... | false = rest-pinned t
    bursts-pinned r t (U.endˢ _) = rest-pinned t
    bursts-pinned r t U.hushˢ    = rest-pinned t

    restᴹ-pinned : ∀ {Γ A B C} (o : Maybe (U.Node Γ A)) → Pinned (U.restᴹ {B = B} o) (U.restᴹ {B = C} o)
    restᴹ-pinned nothing  = unpinned
    restᴹ-pinned (just o) = rest-pinned o

    rests-pinned : ∀ {Γ A B C} (ls : List (U.Node Γ A)) → Pinned (U.restsˢ {B = B} ls) (U.restsˢ {B = C} ls)
    rests-pinned []       = unpinned
    rests-pinned (l ∷ ls) = union-pinned (rest-pinned l) (rests-pinned ls)

lv-refl : ∀ {Γ A} (x : U.Node Γ A) → Leaves x x
lv-refl x = leaves (λ ρ _ n → agree-refl n _) (λ ρ d → d) (rest-pinned x)

private
  contra : ∀ {ℓ} {X : Set ℓ} → true ≡ false → X
  contra ()

  eqᵀ : ∀ {m} {x y : Tail} → x ≡ y → Agreeᵀ m x y
  eqᵀ {m} {x} refl = agreeᵀ-refl m x

  behind : ∀ {m} a (L s : Tail∞) t → AtopT a t → Agreeᵀ m (later L) (t ∪ later s) → Agreeᵀ (suc m) (pin a L) (t ∪ pin a s)
  behind a L s idle      at h = pin⁼ h
  behind a L s (pin b r) at h = subst (λ x → Agreeᵀ _ (pin a L) (first b r (pin a s) x)) (sym at) (pin⁼ h)

∪-unit : ∀ m t → Agreeᵀ m t (t ∪ idle)
∪-unit zero    t         = stopᵀ
∪-unit (suc m) idle      = idle⁼
∪-unit (suc m) (pin k r) = pin⁼ (∪-unit m (later r))

private
  tie : ∀ m a (r s : Tail∞) t → later r ≡ t → ∀ u → later s ≡ u → AtopT a t → AtopT a u → SortedT u
      → Agreeᵀ m (pin a r ∪ u) (t ∪ pin a s)
  tie zero    a r s t er u es at au su = stopᵀ
  tie (suc m) a r s t er idle es at au su =
    behind a _ s t at (eqᵀ (trans (cong (_∪ idle) er) (cong (t ∪_) (sym es))))
  tie (suc m) a r s t er (pin c s′) es at au su with <ᵖ-split a c au
  ... | inj₁ lt   = subst (λ x → Agreeᵀ _ (first a r (pin c s′) x) (t ∪ pin a s)) (sym lt)
                      (behind a _ s t at (eqᵀ (trans (cong (_∪ pin c s′) er) (cong (t ∪_) (sym es)))))
  ... | inj₂ refl = subst (λ x → Agreeᵀ _ (first a r (pin a s′) x) (t ∪ pin a s)) (sym (<ᵖ-irrefl a))
                      (behind a _ s t at (agreeᵀ-trans (tie m a r s′ t er (later s′) refl at (proj₁ (sortedᵀ su)) (proj₂ (sortedᵀ su)))
                                                       (eqᵀ (cong (t ∪_) (sym es)))))

∪-tie : ∀ m a (r s : Tail∞) → AtopT a (later r) → AtopT a (later s) → SortedT (later s)
      → Agreeᵀ m (pin a r ∪ later s) (later r ∪ pin a s)
∪-tie m a r s = tie m a r s (later r) refl (later s) refl

mutual
  ∪-comm : ∀ m t u → SortedT t → SortedT u → Agreeᵀ m (t ∪ u) (u ∪ t)
  ∪-comm zero    t         u         st su = stopᵀ
  ∪-comm (suc m) idle      u         st su = ∪-unit (suc m) u
  ∪-comm (suc m) (pin a r) idle      st su = agreeᵀ-sym (∪-unit (suc m) (pin a r))
  ∪-comm (suc m) (pin a r) (pin b s) st su = comm-pin m a r b s (a <ᵖ b) refl (b <ᵖ a) refl st su

  private
    comm-pin : ∀ m a r b s x → a <ᵖ b ≡ x → ∀ y → b <ᵖ a ≡ y → SortedT (pin a r) → SortedT (pin b s)
             → Agreeᵀ (suc m) (first a r (pin b s) x) (first b s (pin a r) y)
    comm-pin m a r b s true  ex true  ey st su = contra (trans (sym ey) (<ᵖ-asym a b ex))
    comm-pin m a r b s true  ex false ey st su = pin⁼ (∪-comm m (later r) (pin b s) (proj₂ (sortedᵀ st)) su)
    comm-pin m a r b s false ex true  ey st su = pin⁼ (∪-comm m (pin a r) (later s) st (proj₂ (sortedᵀ su)))
    comm-pin m a r b s false ex false ey st su with <ᵖ-split a b ey
    ... | inj₁ lt   = contra (trans (sym lt) ex)
    ... | inj₂ refl = pin⁼ (agreeᵀ-trans (∪-tie m a r s (proj₁ (sortedᵀ st)) (proj₁ (sortedᵀ su)) (proj₂ (sortedᵀ su)))
                                         (∪-comm m (later r) (pin a s) (proj₂ (sortedᵀ st)) su))

private
  tail-agreeᵀ : ∀ {A m} (t t′ : Tail) → Agree {A} m (tailᴱ t) (tailᴱ t′) → Agreeᵀ m t t′
  tail-agreeᵀ {m = zero}  t         t′          _            = stopᵀ
  tail-agreeᵀ {m = suc _} (pin k r) (pin .k r′) (skip⁼ a _) = pin⁼ a
  tail-agreeᵀ {m = suc _} (pin _ _) idle        ()
  tail-agreeᵀ {m = suc _} idle      (pin _ _)   ()
  tail-agreeᵀ {m = suc _} idle      idle        hush⁼        = idle⁼

  union-swap : ∀ {Γ B C} {x y : U.Node Γ B} {sx sy} {x′ y′ : U.Node Γ C} {sx′ sy′}
             → Pinned sx sx′ → Pinned sy sy′ → Pinned (U.unionˢ x sx y sy) (U.unionˢ y′ sy′ x′ sx′)
  union-swap (pinned {k}) (pinned {k′}) with k <ᵖ k′ in e
  ... | true rewrite <ᵖ-asym k k′ e = pinned
  ... | false with k′ <ᵖ k in e′
  ...   | true  = pinned
  ...   | false with <ᵖ-split k′ k e
  ...     | inj₁ lt with () ← trans (sym lt) e′
  ...     | inj₂ refl = pinned
  union-swap pinned   unpinned = pinned
  union-swap unpinned pinned   = pinned
  union-swap unpinned unpinned = unpinned

lv-swap : ∀ {Γ A B} {x y : U.Node Γ A} {x′ y′ : U.Node Γ B} → Leaves x x′ → Leaves y y′ → Leaves (U.unionᶜ x y) (U.unionᶜ y′ x′)
lv-swap {x = x} {y} {x′} {y′} lx@(leaves ax dx px) ly@(leaves ay dy py) = leaves ag dp (union-swap px py)
  where
    dx′ : ∀ ρ → Deep (U.restᶜ {B = ⊤} (U.unionᶜ x y)) ρ → DeepR x′ ρ
    dx′ ρ e = proj₂ (dx ρ (deepR-rest {c = x} (proj₁ (proj₂ e))))
    dy′ : ∀ ρ → Deep (U.restᶜ {B = ⊤} (U.unionᶜ x y)) ρ → DeepR y′ ρ
    dy′ ρ e = proj₂ (dy ρ (deepR-rest {c = y} (proj₂ (proj₂ e))))
    ag : ∀ ρ → Deep (U.restᶜ {B = ⊤} (U.unionᶜ x y)) ρ → ∀ n → Agree n (U.meaning (U.restᶜ {B = ⊤} (U.unionᶜ x y)) ρ) (U.meaning (U.restᶜ {B = ⊤} (U.unionᶜ y′ x′)) ρ)
    ag ρ e n = tailᴱ-ne (agreeᵀ-trans
      (∪-ne (tail-agreeᵀ (U.cutᴺ x ρ) (U.cutᴺ x′ ρ) (ax ρ (deepR-rest {c = x} (proj₁ (proj₂ e))) n))
            (tail-agreeᵀ (U.cutᴺ y ρ) (U.cutᴺ y′ ρ) (ay ρ (deepR-rest {c = y} (proj₂ (proj₂ e))) n)))
      (∪-comm n (U.cutᴺ x′ ρ) (U.cutᴺ y′ ρ) (deep-cutR x′ (dx′ ρ e)) (deep-cutR y′ (dy′ ρ e))))
    dp : ∀ ρ → Deep (U.restᶜ {B = ⊤} (U.unionᶜ x y)) ρ → Deep (U.restᶜ {B = ⊤} (U.unionᶜ y′ x′)) ρ
    dp ρ e = deepR-rest {c = U.unionᶜ y′ x′} (dy′ ρ e , dx′ ρ e)
