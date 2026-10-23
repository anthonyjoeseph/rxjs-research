{-# OPTIONS --guardedness #-}

-- WHAT A REST LEAVES RUNNING, AND WHEN TWO LEAVE ALIKE: the next pin a
-- rest steps to, a rest's shape, and two nodes whose rests run alike at
-- every depth.
module adequacy.Leaves where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using () renaming (_∷_ to _∷ᴬ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import denotation.MonotonicList.Events using (Pos; Tail; Tail∞; pin; idle; end; inside; _<ᵖ_)
open import denotation.MonotonicList using (Agree; Agreeᵀ; tailᴱ; agree-refl; agree-sym; agree-trans; stopᵀ; pin⁼; idle⁼; skip⁼; hush⁼)
open import denotation.NonExpansive using (tailᴱ-ne; ∪-ne; burstOn-ne; _,ˢ_)
import denotation.MonotonicList as M′
import denotation.Unfold as U
open import adequacy.Placed.Order using (Ordered)
open import adequacy.Placed.Burst using (ordered-tail)
open import adequacy.Deep using (Deep; Deeps; DeepR; deep-rest; deepR-rest; deep-cutR; ordered-retyped)
open import adequacy.Env using (cut-ne; nagree-refl; deepR-same)
open import adequacy.Placed.Keys using (ordered-≈)

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

pinned-trans : ∀ {Γ B C D} {a : U.Step Γ B} {b : U.Step Γ C} {c : U.Step Γ D} → Pinned a b → Pinned b c → Pinned a c
pinned-trans pinned   pinned   = pinned
pinned-trans unpinned unpinned = unpinned

union-pinned : ∀ {Γ B C} {x y : U.Node Γ B} {sx sy} {x′ y′ : U.Node Γ C} {sx′ sy′}
             → Pinned sx sx′ → Pinned sy sy′ → Pinned (U.unionˢ x sx y sy) (U.unionˢ x′ sx′ y′ sy′)
union-pinned (pinned {k}) (pinned {k′}) with k <ᵖ k′
... | true  = pinned
... | false = pinned
union-pinned pinned   unpinned = pinned
union-pinned unpinned q        = q

under-pinned : ∀ {Γ A D B C} (s : U.Source Γ A) (st : U.Step (A ∷ Γ) D) → Pinned (U.underˢ {B = B} s st) (U.underˢ {B = C} s st)
under-pinned s (U.skipˢ _ _)  = pinned
under-pinned s (U.outˢ _ _ _) = unpinned
under-pinned s (U.endˢ _)     = unpinned
under-pinned s U.hushˢ        = unpinned

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

restful-pinned : ∀ {Γ B} {c : U.Node Γ B} → Restful c → Pinned (U.step c) (U.restˢ {B = B} c)
restful-pinned rf-idle                    = unpinned
restful-pinned (rf-rest {n = n})          = rest-pinned n
restful-pinned (rf-union {x = x} {y} _ _) = union-pinned (rest-pinned x) (rest-pinned y)
restful-pinned (rf-burst {r = r} {t = t}) = bursts-pinned r t (U.step t)
restful-pinned (rf-under {C = C} {s = s} {b = b} _) = under-pinned s (U.restˢ {B = C} b)

pinned-sym : ∀ {Γ B C} {a : U.Step Γ B} {b : U.Step Γ C} → Pinned a b → Pinned b a
pinned-sym pinned   = pinned
pinned-sym unpinned = unpinned

under-moved : ∀ {Γ A D E B C} (s s′ : U.Source Γ A) {st : U.Step (A ∷ Γ) D} {st′ : U.Step (A ∷ Γ) E}
            → Pinned st st′ → Pinned (U.underˢ {B = B} s st) (U.underˢ {B = C} s′ st′)
under-moved s s′ pinned   = pinned
under-moved s s′ unpinned = unpinned

bursts-moved : ∀ {Γ A A′ B C} r {t : U.Node Γ A} {t′ : U.Node Γ A′} {st : U.Step Γ A} {st′ : U.Step Γ A′}
             → Pinned st st′ → Pinned (U.restˢ {B = B} t) (U.restˢ {B = C} t′) → Pinned (U.burstsˢ {B = B} r t st) (U.burstsˢ {B = C} r t′ st′)
bursts-moved r (pinned {k}) rp with inside r k
... | true  = pinned
... | false = rp
bursts-moved r unpinned rp = rp

tail-agreeᵀ : ∀ {A m} (t t′ : Tail) → Agree {A} m (tailᴱ t) (tailᴱ t′) → Agreeᵀ m t t′
tail-agreeᵀ {m = zero}  t         t′          _           = stopᵀ
tail-agreeᵀ {m = suc _} (pin k r) (pin .k r′) (skip⁼ a _) = pin⁼ a
tail-agreeᵀ {m = suc _} (pin _ _) idle        ()
tail-agreeᵀ {m = suc _} idle      (pin _ _)   ()
tail-agreeᵀ {m = suc _} idle      idle        hush⁼       = idle⁼

restful-meaning : ∀ {Γ A} {t : U.Node Γ A} → Restful t → ∀ ρ → U.meaning t ρ ≡ tailᴱ (U.cutᴺ t ρ)
restful-meaning rf-rest                      ρ = refl
restful-meaning rf-idle                      ρ = refl
restful-meaning (rf-union _ _)               ρ = refl
restful-meaning rf-burst                     ρ = refl
restful-meaning (rf-under {s = U.live _} _)    ρ = refl
restful-meaning (rf-under {s = U.ended _ _} _) ρ = refl

mutual
  restful-deep : ∀ {Γ A} {n : U.Node Γ A} {ρ} → Restful n → DeepR n ρ → Deep n ρ
  restful-deep {n = n} {ρ} rf d = subst Ordered (sym (restful-meaning rf ρ)) (ordered-tail (U.cutᴺ n ρ) (deep-cutR n d)) , restful-deeps rf d

  restful-deeps : ∀ {Γ A} {n : U.Node Γ A} {ρ} → Restful n → DeepR n ρ → Deeps n ρ
  restful-deeps rf-idle                         d         = tt
  restful-deeps rf-rest                         d         = d
  restful-deeps (rf-union rx ry)                (dx , dy) = restful-deep rx dx , restful-deep ry dy
  restful-deeps rf-burst                        (_ , dt)  = dt
  restful-deeps (rf-under {s = U.live _} rb)    (ds , db) = ds , restful-deep rb db
  restful-deeps (rf-under {s = U.ended _ _} rb) (dt , db) = dt , restful-deep rb db

restful-agree : ∀ {Γ A} {n n′ : U.Node Γ A} → Restful n → Restful n′ → Leaves n n′ → ∀ ρ → Deep (U.restᶜ {B = ⊤} n) ρ → ∀ m → Agree m (U.meaning n ρ) (U.meaning n′ ρ)
restful-agree {n = n} {n′} rf rf′ l ρ e m rewrite restful-meaning rf ρ | restful-meaning rf′ ρ =
  tailᴱ-ne (tail-agreeᵀ (U.cutᴺ n ρ) (U.cutᴺ n′ ρ) (Leaves.agree l ρ e m))

restful-step : ∀ {Γ A B} {n : U.Node Γ A} {n′ : U.Node Γ B} → Restful n → Restful n′
             → Pinned (U.restˢ {B = ⊤} n) (U.restˢ {B = ⊤} n′) → Pinned (U.step n) (U.step n′)
restful-step {n = n} {n′} rf rf′ p =
  pinned-trans (restful-pinned rf) (pinned-trans (rest-pinned n) (pinned-trans p (pinned-trans (rest-pinned n′) (pinned-sym (restful-pinned rf′)))))

lv-refl : ∀ {Γ A} (x : U.Node Γ A) → Leaves x x
lv-refl x = leaves (λ ρ _ n → agree-refl n _) (λ ρ d → d) (rest-pinned x)

lv-trans : ∀ {Γ A B C} {x : U.Node Γ A} {y : U.Node Γ B} {z : U.Node Γ C} → Leaves x y → Leaves y z → Leaves x z
lv-trans (leaves a d p) (leaves a′ d′ p′) = leaves (λ ρ e n → agree-trans (a ρ e n) (a′ ρ (d ρ e) n)) (λ ρ e → d′ ρ (d ρ e)) (pinned-trans p p′)

lv-union : ∀ {Γ A B} {x y : U.Node Γ A} {x′ y′ : U.Node Γ B} → Leaves x x′ → Leaves y y′ → Leaves (U.unionᶜ x y) (U.unionᶜ x′ y′)
lv-union {x = x} {y} {x′} {y′} (leaves ax dx px) (leaves ay dy py) =
  leaves (λ ρ e n → tailᴱ-ne (∪-ne (tail-agreeᵀ (U.cutᴺ x ρ) (U.cutᴺ x′ ρ) (ax ρ (deepR-rest {c = x} (proj₁ (proj₂ e))) n))
                                    (tail-agreeᵀ (U.cutᴺ y ρ) (U.cutᴺ y′ ρ) (ay ρ (deepR-rest {c = y} (proj₂ (proj₂ e))) n))))
         (λ ρ d → deepR-rest {c = U.unionᶜ x′ y′} (proj₂ (dx ρ (deepR-rest {c = x} (proj₁ (proj₂ d)))) , proj₂ (dy ρ (deepR-rest {c = y} (proj₂ (proj₂ d))))))
         (union-pinned px py)

lv-under : ∀ {Γ A C D B B′} (s : U.Source Γ A) {b : U.Node (A ∷ Γ) C} {b′ : U.Node (A ∷ Γ) D}
         → Leaves b b′ → Leaves (U.underᶜ {B = B} s b) (U.underᶜ {B = B′} s b′)
lv-under {B = B} {B′} s {b} {b′} (leaves a d p) = leaves (ag s) (dp s) (under-moved s s (pinned-trans (rest-pinned b) (pinned-trans p (rest-pinned b′))))
  where
    env : U.Source _ _ → U.NEnv _ → U.NEnv _
    env (U.live s₀)    ρ = U.meaning s₀ ρ ∷ᴬ ρ
    env (U.ended c _)  ρ = end c ∷ᴬ ρ
    inner : ∀ s₀ ρ → Deep (U.restᶜ {B = ⊤} (U.underᶜ {B = B} s₀ b)) ρ → Deep (U.restᶜ {B = ⊤} b) (env s₀ ρ)
    inner (U.live s₀)  ρ (_ , _ , db) = deepR-rest {c = b} db
    inner (U.ended c t) ρ (_ , _ , db) = deepR-rest {c = b} db
    ag : ∀ s₀ ρ → Deep (U.restᶜ {B = ⊤} (U.underᶜ {B = B} s₀ b)) ρ → ∀ n → Agree n (U.meaning (U.restᶜ {B = ⊤} (U.underᶜ {B = B} s₀ b)) ρ) (U.meaning (U.restᶜ {B = ⊤} (U.underᶜ {B = B′} s₀ b′)) ρ)
    ag (U.live s₀)  ρ e n = a (env (U.live s₀) ρ) (inner (U.live s₀) ρ e) n
    ag (U.ended c t) ρ e n = a (env (U.ended c t) ρ) (inner (U.ended c t) ρ e) n
    dp : ∀ s₀ ρ → Deep (U.restᶜ {B = ⊤} (U.underᶜ {B = B} s₀ b)) ρ → Deep (U.restᶜ {B = ⊤} (U.underᶜ {B = B′} s₀ b′)) ρ
    dp (U.live s₀)  ρ e@(_ , ds , _) = deepR-rest {c = U.underᶜ {B = B′} (U.live s₀) b′} (ds , proj₂ (d _ (inner (U.live s₀) ρ e)))
    dp (U.ended c t) ρ e@(_ , dt , _) = deepR-rest {c = U.underᶜ {B = B′} (U.ended c t) b′} (dt , proj₂ (d _ (inner (U.ended c t) ρ e)))

lv-burst : ∀ {Γ A B B′} r {n n′ : U.Node Γ A} → Restful n → Restful n′ → Leaves n n′ → Leaves (U.burstingᶜ {B = B} r n) (U.burstingᶜ {B = B′} r n′)
lv-burst {B = B} {B′} r {n} {n′} rf rf′ l@(leaves a d p) = leaves (λ ρ e m → tailᴱ-ne (bo ρ (proj₂ (proj₂ e)) m)) dp (bursts-moved r (restful-step rf rf′ p) p)
  where
    bo : ∀ ρ → Deep n ρ → ∀ m → Agreeᵀ m (M′.burstOn r (U.stateᴺ n ρ)) (M′.burstOn r (U.stateᴺ n′ ρ))
    bo ρ dn m = burstOn-ne r {U.stateᴺ n ρ} {U.stateᴺ n′ ρ} (tail-agreeᵀ (U.cutᴺ n ρ) (U.cutᴺ n′ ρ) (a ρ (deep-rest {c = n} dn) m) ,ˢ restful-agree rf rf′ l ρ (deep-rest {c = n} dn) m)
    dp : ∀ ρ → Deep (U.restᶜ {B = ⊤} (U.burstingᶜ {B = B} r n)) ρ → Deep (U.restᶜ {B = ⊤} (U.burstingᶜ {B = B′} r n′)) ρ
    dp ρ (o , _ , dn) = o′ , ordered-retyped (M′.burstOn r (U.stateᴺ n′ ρ)) o′ , restful-deep rf′ (proj₂ (d ρ (deep-rest {c = n} dn)))
      where o′ = ordered-≈ _ _ (λ m → tailᴱ-ne (bo ρ dn m)) o

lv-shift : ∀ {Γ A C B B′} {n n′ : U.Node Γ A} (b : U.Node (A ∷ Γ) C) → Restful n → Restful n′ → Leaves n n′
         → Leaves (U.underᶜ {B = B} (U.live n) b) (U.underᶜ {B = B′} (U.live n′) b)
lv-shift {B = B} {B′} {n} {n′} b rf rf′ l = leaves (λ ρ e m → tailᴱ-ne (cut-ne b (restful-agree rf rf′ l ρ (deep-rest {c = n} (proj₁ (proj₂ e))) m , nagree-refl m ρ))) dp (under-moved (U.live n) (U.live n′) (rest-pinned b))
  where
    dp : ∀ ρ → Deep (U.restᶜ {B = ⊤} (U.underᶜ {B = B} (U.live n) b)) ρ → Deep (U.restᶜ {B = ⊤} (U.underᶜ {B = B′} (U.live n′) b)) ρ
    dp ρ (_ , dn , db) = deepR-rest {c = U.underᶜ {B = B′} (U.live n′) b} (restful-deep rf′ (proj₂ (Leaves.deep l ρ (deep-rest {c = n} dn))) , deepR-same b (λ m → restful-agree rf rf′ l ρ (deep-rest {c = n} dn) m , nagree-refl m ρ) db)

tw-refl : ∀ {Γ A} (x : U.Node Γ A) → Twin x x
tw-refl x = lv-refl x , λ ρ d → d

tw-trans : ∀ {Γ A B C} {x : U.Node Γ A} {y : U.Node Γ B} {z : U.Node Γ C} → Twin x y → Twin y z → Twin x z
tw-trans (l , b) (l′ , b′) = lv-trans l l′ , λ ρ d → b ρ (b′ ρ d)

tw-sym : ∀ {Γ A B} {x : U.Node Γ A} {y : U.Node Γ B} → Twin x y → Twin y x
tw-sym (leaves a d p , b) = leaves (λ ρ e n → agree-sym (a ρ (b ρ e) n)) b (pinned-sym p) , d

tw-union : ∀ {Γ A B} {x y : U.Node Γ A} {x′ y′ : U.Node Γ B} → Twin x x′ → Twin y y′ → Twin (U.unionᶜ x y) (U.unionᶜ x′ y′)
tw-union tx ty = lv-union (proj₁ tx) (proj₁ ty) , Leaves.deep (lv-union (proj₁ (tw-sym tx)) (proj₁ (tw-sym ty)))

tw-under : ∀ {Γ A C D B B′} (s : U.Source Γ A) {b : U.Node (A ∷ Γ) C} {b′ : U.Node (A ∷ Γ) D}
         → Twin b b′ → Twin (U.underᶜ {B = B} s b) (U.underᶜ {B = B′} s b′)
tw-under {B = B} {B′} s t = lv-under s (proj₁ t) , Leaves.deep (lv-under {B = B′} {B′ = B} s (proj₁ (tw-sym t)))

tw-burst : ∀ {Γ A B B′} r {n n′ : U.Node Γ A} → Restful n → Restful n′ → Twin n n′ → Twin (U.burstingᶜ {B = B} r n) (U.burstingᶜ {B = B′} r n′)
tw-burst {B = B} {B′} r rf rf′ t = lv-burst r rf rf′ (proj₁ t) , Leaves.deep (lv-burst {B = B′} {B′ = B} r rf′ rf (proj₁ (tw-sym t)))

tw-shift : ∀ {Γ A C B B′} {n n′ : U.Node Γ A} (b : U.Node (A ∷ Γ) C) → Restful n → Restful n′ → Twin n n′
         → Twin (U.underᶜ {B = B} (U.live n) b) (U.underᶜ {B = B′} (U.live n′) b)
tw-shift {B = B} {B′} b rf rf′ t = lv-shift b rf rf′ (proj₁ t) , Leaves.deep (lv-shift {B = B′} {B′ = B} b rf′ rf (proj₁ (tw-sym t)))

tw-if : ∀ {Γ A B} (c : Bool) {x y : U.Node Γ A} {x′ y′ : U.Node Γ B} → Twin x x′ → Twin y y′ → Twin (if c then x else y) (if c then x′ else y′)
tw-if true  t _ = t
tw-if false _ u = u

lv-tie : ∀ {Γ A B C} {p : U.Node Γ A} {a : U.Node Γ B} {b : U.Node Γ C} → Leaves p a × Restful p → Leaves a b → Leaves p b × Restful p
lv-tie (l , rf) l′ = lv-trans l l′ , rf

tw-tie : ∀ {Γ A B C} {p : U.Node Γ A} {a : U.Node Γ B} {b : U.Node Γ C} → Twin p a × Restful p → Twin a b → Twin p b × Restful p
tw-tie (t , rf) t′ = tw-trans t t′ , rf
