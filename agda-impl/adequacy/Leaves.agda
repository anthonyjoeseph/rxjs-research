{-# OPTIONS --guardedness #-}

-- WHAT A REST LEAVES RUNNING, AND WHEN TWO LEAVE ALIKE: the next pin a
-- rest steps to, a rest's shape, and two nodes whose rests run alike at
-- every depth, composed through the nodes a leftover is built from.
module adequacy.Leaves where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; _∷_)
open import Data.Maybe using (Maybe)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.List.Relation.Unary.All using () renaming (_∷_ to _∷ᴬ_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)

open import denotation.MonotonicList.Events using (Events; Events∞; Pos; Tail; Tail∞; pin; idle; out; skip; end; hush; inside; _<ᵖ_; _∪_; first; <ᵖ-asym; <ᵖ-split; <ᵖ-irrefl)
open import denotation.MonotonicList using (Agree; Agreeᵀ; tailᴱ; agree-refl; agree-sym; agree-trans; agreeᵀ-refl; agreeᵀ-sym; agreeᵀ-trans; stopᵀ; pin⁼; idle⁼; out⁼; skip⁼; end⁼; hush⁼)
open import denotation.NonExpansive using (tailᴱ-ne; ∪-ne; burstOn-ne; _,ˢ_)
import denotation.MonotonicList as M′
import denotation.Unfold as U
open import adequacy.Placed.Order using (Ordered; Atop; ordered)
open import adequacy.Placed.Rising using (AtopT)
open import adequacy.Placed.Trail using (SortedT; sortedᵀ)
open import adequacy.Placed.Burst using (ordered-tail)
open import adequacy.Deep using (Deep; Deeps; DeepR; deep-rest; deepR-rest; deep-∪; deep-cut; deep-cutR; atop-tail; ordered-retyped)

open Events∞
open Tail∞

-- Two steps alike as rests: the same pin, or none.
data Pinned {Γ} {B C : Set} : U.Step Γ B → U.Step Γ C → Set₁ where
  pinned   : ∀ {k x y} → Pinned (U.skipˢ k x) (U.skipˢ k y)
  unpinned : Pinned U.hushˢ U.hushˢ

pinned-trans : ∀ {Γ B C D} {a : U.Step Γ B} {b : U.Step Γ C} {c : U.Step Γ D} → Pinned a b → Pinned b c → Pinned a c
pinned-trans pinned   pinned   = pinned
pinned-trans unpinned unpinned = unpinned

pinned-skip : ∀ {Γ B C} {a : U.Step Γ B} {b : U.Step Γ C} {q y′} → Pinned a b → b ≡ U.skipˢ q y′ → Σ (U.Node Γ B) λ x′ → a ≡ U.skipˢ q x′
pinned-skip pinned refl = _ , refl

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

-- A node's rest pins alike whatever it is read as.
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

-- A rest's shape, all the way down to its rests: it steps as it rests.
data Restful : ∀ {Γ B} → U.Node Γ B → Set₁ where
  rf-idle  : ∀ {Γ B} → Restful (U.idleᶜ {Γ = Γ} {B = B})
  rf-rest  : ∀ {Γ A B} {n : U.Node Γ A} → Restful (U.restᶜ {B = B} n)
  rf-union : ∀ {Γ B} {x y : U.Node Γ B} → Restful x → Restful y → Restful (U.unionᶜ x y)
  rf-burst : ∀ {Γ A B r} {t : U.Node Γ A} → Restful (U.burstingᶜ {B = B} r t)
  rf-under : ∀ {Γ A C B} {s : U.Source Γ A} {b : U.Node (A ∷ Γ) C} → Restful b → Restful (U.underᶜ {B = B} s b)

restful-pinned : ∀ {Γ B} {c : U.Node Γ B} → Restful c → Pinned (U.step c) (U.restˢ {B = B} c)
restful-pinned rf-idle                    = unpinned
restful-pinned (rf-rest {n = n})          = rest-pinned n
restful-pinned (rf-union {x = x} {y} _ _) = union-pinned (rest-pinned x) (rest-pinned y)
restful-pinned (rf-burst {r = r} {t = t}) = bursts-pinned r t (U.step t)
restful-pinned (rf-under {C = C} {s = s} {b = b} _) = under-pinned s (U.restˢ {B = C} b)

pinned-sym : ∀ {Γ B C} {a : U.Step Γ B} {b : U.Step Γ C} → Pinned a b → Pinned b a
pinned-sym pinned   = pinned
pinned-sym unpinned = unpinned

-- A body's rest pins as its own, whatever source it carries.
under-moved : ∀ {Γ A D E B C} (s s′ : U.Source Γ A) {st : U.Step (A ∷ Γ) D} {st′ : U.Step (A ∷ Γ) E}
            → Pinned st st′ → Pinned (U.underˢ {B = B} s st) (U.underˢ {B = C} s′ st′)
under-moved s s′ pinned   = pinned
under-moved s s′ unpinned = unpinned

-- A burst pins as its node's step, and past it as the node's rest.
bursts-moved : ∀ {Γ A A′ B C} r {t : U.Node Γ A} {t′ : U.Node Γ A′} {st : U.Step Γ A} {st′ : U.Step Γ A′}
             → Pinned st st′ → Pinned (U.restˢ {B = B} t) (U.restˢ {B = C} t′) → Pinned (U.burstsˢ {B = B} r t st) (U.burstsˢ {B = C} r t′ st′)
bursts-moved r (pinned {k}) rp with inside r k
... | true  = pinned
... | false = rp
bursts-moved r unpinned rp = rp

-- A node's next pin a rest's: what a held node keeps of its ended
-- parts steps as they would rest.
Tied : ∀ {Γ A B} → U.Node Γ A → U.Node Γ B → Set₁
Tied x y = Pinned (U.step x) (U.restˢ {B = ⊤} y)

-- A restful pool's tie carried along a pin.
tie-trans : ∀ {Γ A C D} {p : U.Node Γ A} {a : U.Step Γ C} {b : U.Step Γ D} → Pinned (U.step p) a × Restful p → Pinned a b → Pinned (U.step p) b × Restful p
tie-trans (t , rf) q = pinned-trans t q , rf

-- Two nodes leaving alike: what each still runs past an unsubscribe,
-- under every environment the first is in order at, the same at every
-- depth, the second in order when the first is; their rests' next
-- steps pinned alike.
-- `restˢ` and `cutᴺ` are read apart, so the pin is its own field.
record Leaves {Γ A B} (x : U.Node Γ A) (y : U.Node Γ B) : Set₁ where
  constructor leaves
  field agree : ∀ (ρ : U.NEnv Γ) → Deep (U.restᶜ {B = ⊤} x) ρ → ∀ n → Agree n (U.meaning (U.restᶜ {B = ⊤} x) ρ) (U.meaning (U.restᶜ {B = ⊤} y) ρ)
        deep  : ∀ (ρ : U.NEnv Γ) → Deep (U.restᶜ {B = ⊤} x) ρ → Deep (U.restᶜ {B = ⊤} y) ρ
        pin   : Pinned (U.restˢ {B = ⊤} x) (U.restˢ {B = ⊤} y)

-- The order read back, from the witness's rest to the node's: a
-- flatMap's part is in order by its whole meaning, which no rest
-- below it holds, so only an ended source's rest carries it.
Back : ∀ {Γ A B} → U.Node Γ A → U.Node Γ B → Set₁
Back x y = ∀ (ρ : U.NEnv _) → Deep (U.restᶜ {B = ⊤} y) ρ → Deep (U.restᶜ {B = ⊤} x) ρ

------------------------------------------------------------------------
-- Tails read alike

-- Two tails run alike are alike.
tail-agreeᵀ : ∀ {A m} (t t′ : Tail) → Agree {A} m (tailᴱ t) (tailᴱ t′) → Agreeᵀ m t t′
tail-agreeᵀ {m = zero}  t         t′          _           = stopᵀ
tail-agreeᵀ {m = suc _} (pin k r) (pin .k r′) (skip⁼ a _) = pin⁼ a
tail-agreeᵀ {m = suc _} (pin _ _) idle        ()
tail-agreeᵀ {m = suc _} idle      (pin _ _)   ()
tail-agreeᵀ {m = suc _} idle      idle        hush⁼       = idle⁼

-- A run alike at every depth is in order when the other is.
atop-agree : ∀ {A k m} {e e′ : Events A} → Agree (suc m) e e′ → Atop k e → Atop k e′
atop-agree (out⁼ _ _)  a = a
atop-agree (skip⁼ _ _) a = a
atop-agree end⁼        a = a
atop-agree hush⁼       a = a

private
  out-next : ∀ {A k x} {l r : Events∞ A} → (∀ m → Agree m (out k x l) (out k x r)) → ∀ m → Agree m (force l) (force r)
  out-next ag m with ag (suc m)
  ... | out⁼ _ a = a

  skip-next : ∀ {A k} {l r : Events∞ A} → (∀ m → Agree m (skip k l) (skip k r)) → ∀ m → Agree m (force l) (force r)
  skip-next ag m with ag (suc m)
  ... | skip⁼ _ a = a

ordered-agree : ∀ {A} {e e′ : Events A} → (∀ m → Agree m e e′) → Ordered e → Ordered e′
ordered-agree ag o .ordered with ag 1 | ordered o
... | out⁼ _ _  | a , o′ = atop-agree (out-next ag 1) a , ordered-agree (out-next ag) o′
... | skip⁼ _ _ | a , o′ = atop-agree (skip-next ag 1) a , ordered-agree (skip-next ag) o′
... | end⁼      | _      = tt
... | hush⁼     | _      = tt

------------------------------------------------------------------------
-- Rests alike, composed

-- A restful node's meaning is its cut's tail.
restful-meaning : ∀ {Γ A} {t : U.Node Γ A} → Restful t → ∀ ρ → U.meaning t ρ ≡ tailᴱ (U.cutᴺ t ρ)
restful-meaning rf-rest                      ρ = refl
restful-meaning rf-idle                      ρ = refl
restful-meaning (rf-union _ _)               ρ = refl
restful-meaning rf-burst                     ρ = refl
restful-meaning (rf-under {s = U.live _} _)    ρ = refl
restful-meaning (rf-under {s = U.ended _ _} _) ρ = refl

-- A restful node runs as it rests, so its rest in order is it in order.
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

-- Two restful nodes leaving alike run alike, and step alike.
restful-agree : ∀ {Γ A} {n n′ : U.Node Γ A} → Restful n → Restful n′ → Leaves n n′ → ∀ ρ → Deep (U.restᶜ {B = ⊤} n) ρ → ∀ m → Agree m (U.meaning n ρ) (U.meaning n′ ρ)
restful-agree {n = n} {n′} rf rf′ l ρ e m rewrite restful-meaning rf ρ | restful-meaning rf′ ρ =
  tailᴱ-ne (tail-agreeᵀ (U.cutᴺ n ρ) (U.cutᴺ n′ ρ) (Leaves.agree l ρ e m))

restful-step : ∀ {Γ A B} {n : U.Node Γ A} {n′ : U.Node Γ B} → Restful n → Restful n′
             → Pinned (U.restˢ {B = ⊤} n) (U.restˢ {B = ⊤} n′) → Pinned (U.step n) (U.step n′)
restful-step {n = n} {n′} rf rf′ p =
  pinned-trans (restful-pinned rf) (pinned-trans (rest-pinned n) (pinned-trans p (pinned-trans (rest-pinned n′) (pinned-sym (restful-pinned rf′)))))

-- A body reads its source's run through the environment, and no
-- further than it has run: two runs alike for `m` steps leave the
-- body's cut alike for as many, and alike at every depth leave it in
-- order alike as a rest.
postulate
  cut-env   : ∀ {Γ A C} (b : U.Node (A ∷ Γ) C) (ρ : U.NEnv Γ) {m} {e e′ : Events A} → Agree m e e′ → Agreeᵀ m (U.cutᴺ b (e ∷ᴬ ρ)) (U.cutᴺ b (e′ ∷ᴬ ρ))
  deepR-env : ∀ {Γ A C} (b : U.Node (A ∷ Γ) C) (ρ : U.NEnv Γ) {e e′ : Events A} → (∀ m → Agree m e e′) → DeepR b (e ∷ᴬ ρ) → DeepR b (e′ ∷ᴬ ρ)

lv-refl : ∀ {Γ A} (x : U.Node Γ A) → Leaves x x
lv-refl x = leaves (λ ρ _ n → agree-refl n _) (λ ρ d → d) (rest-pinned x)

lv-trans : ∀ {Γ A B C} {x : U.Node Γ A} {y : U.Node Γ B} {z : U.Node Γ C} → Leaves x y → Leaves y z → Leaves x z
lv-trans (leaves a d p) (leaves a′ d′ p′) = leaves (λ ρ e n → agree-trans (a ρ e n) (a′ ρ (d ρ e) n)) (λ ρ e → d′ ρ (d ρ e)) (pinned-trans p p′)

lv-union : ∀ {Γ A B} {x y : U.Node Γ A} {x′ y′ : U.Node Γ B} → Leaves x x′ → Leaves y y′ → Leaves (U.unionᶜ x y) (U.unionᶜ x′ y′)
lv-union {x = x} {y} {x′} {y′} (leaves ax dx px) (leaves ay dy py) =
  leaves (λ ρ e n → tailᴱ-ne (∪-ne (tail-agreeᵀ (U.cutᴺ x ρ) (U.cutᴺ x′ ρ) (ax ρ (deepR-rest (proj₁ (proj₂ e))) n))
                                    (tail-agreeᵀ (U.cutᴺ y ρ) (U.cutᴺ y′ ρ) (ay ρ (deepR-rest (proj₂ (proj₂ e))) n))))
         (λ ρ d → deepR-rest (proj₂ (dx ρ (deepR-rest (proj₁ (proj₂ d)))) , proj₂ (dy ρ (deepR-rest (proj₂ (proj₂ d))))))
         (union-pinned px py)

-- A body's rest under one source.
lv-under : ∀ {Γ A C D B B′} (s : U.Source Γ A) {b : U.Node (A ∷ Γ) C} {b′ : U.Node (A ∷ Γ) D}
         → Leaves b b′ → Leaves (U.underᶜ {B = B} s b) (U.underᶜ {B = B′} s b′)
lv-under {B = B} {B′} s {b} {b′} (leaves a d p) = leaves (λ ρ e n → a (env s ρ) (inner s ρ e) n) (dp s) (under-moved s s (pinned-trans (rest-pinned b) (pinned-trans p (rest-pinned b′))))
  where
    env : U.Source _ _ → U.NEnv _ → U.NEnv _
    env (U.live s₀)    ρ = U.meaning s₀ ρ ∷ᴬ ρ
    env (U.ended c _)  ρ = end c ∷ᴬ ρ
    inner : ∀ s₀ ρ → Deep (U.restᶜ {B = ⊤} (U.underᶜ {B = B} s₀ b)) ρ → Deep (U.restᶜ {B = ⊤} b) (env s₀ ρ)
    inner (U.live s₀)  ρ (_ , _ , db) = deepR-rest db
    inner (U.ended c t) ρ (_ , _ , db) = deepR-rest db
    dp : ∀ s₀ ρ → Deep (U.restᶜ {B = ⊤} (U.underᶜ {B = B} s₀ b)) ρ → Deep (U.restᶜ {B = ⊤} (U.underᶜ {B = B′} s₀ b′)) ρ
    dp (U.live s₀)  ρ e@(_ , ds , _) = deepR-rest {c = U.underᶜ (U.live s₀) b′} (ds , proj₂ (d _ (inner (U.live s₀) ρ e)))
    dp (U.ended c t) ρ e@(_ , dt , _) = deepR-rest {c = U.underᶜ (U.ended c t) b′} (dt , proj₂ (d _ (inner (U.ended c t) ρ e)))

-- A restful source's burst.
lv-burst : ∀ {Γ A B B′} r {n n′ : U.Node Γ A} → Restful n → Restful n′ → Leaves n n′ → Leaves (U.burstingᶜ {B = B} r n) (U.burstingᶜ {B = B′} r n′)
lv-burst {B = B} {B′} r {n} {n′} rf rf′ l@(leaves a d p) = leaves (λ ρ e m → tailᴱ-ne (bo ρ (proj₂ (proj₂ e)) m)) dp (bursts-moved r (restful-step rf rf′ p) p)
  where
    bo : ∀ ρ → Deep n ρ → ∀ m → Agreeᵀ m (M′.burstOn r (U.stateᴺ n ρ)) (M′.burstOn r (U.stateᴺ n′ ρ))
    bo ρ dn m = burstOn-ne r (tail-agreeᵀ (U.cutᴺ n ρ) (U.cutᴺ n′ ρ) (a ρ (deep-rest dn) m) ,ˢ restful-agree rf rf′ l ρ (deep-rest dn) m)
    dp : ∀ ρ → Deep (U.restᶜ {B = ⊤} (U.burstingᶜ {B = B} r n)) ρ → Deep (U.restᶜ {B = ⊤} (U.burstingᶜ {B = B′} r n′)) ρ
    dp ρ (o , _ , dn) = o′ , ordered-retyped (M′.burstOn r (U.stateᴺ n′ ρ)) o′ , restful-deep rf′ (proj₂ (d ρ (deep-rest dn)))
      where o′ = ordered-agree (λ m → tailᴱ-ne (bo ρ dn m)) o

-- A body's rest under a restful source moved.
lv-shift : ∀ {Γ A C B B′} {n n′ : U.Node Γ A} (b : U.Node (A ∷ Γ) C) → Restful n → Restful n′ → Leaves n n′
         → Leaves (U.underᶜ {B = B} (U.live n) b) (U.underᶜ {B = B′} (U.live n′) b)
lv-shift {B = B} {B′} {n} {n′} b rf rf′ l = leaves (λ ρ e m → tailᴱ-ne (cut-env b ρ (restful-agree rf rf′ l ρ (deep-rest (proj₁ (proj₂ e))) m))) dp (under-moved (U.live n) (U.live n′) (rest-pinned b))
  where
    dp : ∀ ρ → Deep (U.restᶜ {B = ⊤} (U.underᶜ {B = B} (U.live n) b)) ρ → Deep (U.restᶜ {B = ⊤} (U.underᶜ {B = B′} (U.live n′) b)) ρ
    dp ρ (_ , dn , db) = deepR-rest {c = U.underᶜ (U.live n′) b} (restful-deep rf′ (proj₂ (Leaves.deep l ρ (deep-rest dn))) , deepR-env b ρ (restful-agree rf rf′ l ρ (deep-rest dn)) db)

------------------------------------------------------------------------
-- Twins: leaving alike both ways

Twin : ∀ {Γ A B} → U.Node Γ A → U.Node Γ B → Set₁
Twin x y = Leaves x y × Back x y

tw-refl : ∀ {Γ A} (x : U.Node Γ A) → Twin x x
tw-refl x = lv-refl x , λ ρ d → d

tw-≡ : ∀ {Γ A} {x y : U.Node Γ A} → x ≡ y → Twin x y
tw-≡ {x = x} refl = tw-refl x

tw-trans : ∀ {Γ A B C} {x : U.Node Γ A} {y : U.Node Γ B} {z : U.Node Γ C} → Twin x y → Twin y z → Twin x z
tw-trans (l , b) (l′ , b′) = lv-trans l l′ , λ ρ d → b ρ (b′ ρ d)

tw-sym : ∀ {Γ A B} {x : U.Node Γ A} {y : U.Node Γ B} → Twin x y → Twin y x
tw-sym (leaves a d p , b) = leaves (λ ρ e n → agree-sym (a ρ (b ρ e) n)) b (pinned-sym p) , d

tw-union : ∀ {Γ A B} {x y : U.Node Γ A} {x′ y′ : U.Node Γ B} → Twin x x′ → Twin y y′ → Twin (U.unionᶜ x y) (U.unionᶜ x′ y′)
tw-union tx ty = lv-union (proj₁ tx) (proj₁ ty) , Leaves.deep (lv-union (proj₁ (tw-sym tx)) (proj₁ (tw-sym ty)))

tw-under : ∀ {Γ A C D B B′} (s : U.Source Γ A) {b : U.Node (A ∷ Γ) C} {b′ : U.Node (A ∷ Γ) D}
         → Twin b b′ → Twin (U.underᶜ {B = B} s b) (U.underᶜ {B = B′} s b′)
tw-under s t = lv-under s (proj₁ t) , Leaves.deep (lv-under s (proj₁ (tw-sym t)))

tw-burst : ∀ {Γ A B B′} r {n n′ : U.Node Γ A} → Restful n → Restful n′ → Twin n n′ → Twin (U.burstingᶜ {B = B} r n) (U.burstingᶜ {B = B′} r n′)
tw-burst r rf rf′ t = lv-burst r rf rf′ (proj₁ t) , Leaves.deep (lv-burst r rf′ rf (proj₁ (tw-sym t)))

tw-shift : ∀ {Γ A C B B′} {n n′ : U.Node Γ A} (b : U.Node (A ∷ Γ) C) → Restful n → Restful n′ → Twin n n′
         → Twin (U.underᶜ {B = B} (U.live n) b) (U.underᶜ {B = B′} (U.live n′) b)
tw-shift b rf rf′ t = lv-shift b rf rf′ (proj₁ t) , Leaves.deep (lv-shift b rf′ rf (proj₁ (tw-sym t)))

tw-if : ∀ {Γ A B} (c : Bool) {x y : U.Node Γ A} {x′ y′ : U.Node Γ B} → Twin x x′ → Twin y y′ → Twin (if c then x else y) (if c then x′ else y′)
tw-if true  t _ = t
tw-if false _ u = u

-- A tail is positions alone, so two in order merge alike either way
-- round: on a tie it matters not which side's pin goes first.
private
  contra : ∀ {X : Set} → true ≡ false → X
  contra ()

  eqᵀ : ∀ {m} {x y : Tail} → x ≡ y → Agreeᵀ m x y
  eqᵀ {m} {x} refl = agreeᵀ-refl m x

  -- A tail at or past `a`, merged behind a pin at `a`.
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

------------------------------------------------------------------------
-- Unions moved

private
  ordered-hush : ∀ {A} → Ordered {A} hush
  ordered-hush .ordered = tt

  union-hush : ∀ {Γ A C} {p y : U.Node Γ A} {sp : U.Step Γ A} {s′ : U.Step Γ C} → Pinned sp s′ → Pinned (U.unionˢ p sp y U.hushˢ) s′
  union-hush pinned   = pinned
  union-hush unpinned = unpinned

deep-idle : ∀ {Γ A} {ρ : U.NEnv Γ} → Deep (U.idleᶜ {B = A}) ρ
deep-idle = ordered-hush , tt

-- A rest's rest is the rest.
tw-rest : ∀ {Γ A B} (x : U.Node Γ A) → Twin (U.restᶜ {B = B} x) x
tw-rest x = leaves (λ ρ _ n → agree-refl n _) (λ ρ d → d) (rest-pinned x) , λ ρ d → d

-- A node joined with an idle one, on either side.
tw-idleʳ : ∀ {Γ A} (x : U.Node Γ A) → Twin x (U.unionᶜ x U.idleᶜ)
tw-idleʳ x = leaves (λ ρ _ n → tailᴱ-ne (∪-unit n (U.cutᴺ x ρ))) (λ ρ d → deepR-rest {c = U.unionᶜ x U.idleᶜ} (proj₂ d , tt))
                    (pinned-sym (union-hush (rest-pinned x)))
           , λ ρ d → deepR-rest (proj₁ (proj₂ d))

tw-idleˡ : ∀ {Γ A} (y : U.Node Γ A) → Twin (U.unionᶜ U.idleᶜ y) y
tw-idleˡ y = leaves (λ ρ _ n → agree-refl n _) (λ ρ d → deepR-rest (proj₂ (proj₂ d))) (rest-pinned y)
           , λ ρ d → deepR-rest {c = U.unionᶜ U.idleᶜ y} (tt , proj₂ d)

-- A node read at another type: what it emits differs, never where.
tw-idle : ∀ {Γ B C} → Twin (U.idleᶜ {Γ = Γ} {B = B}) (U.idleᶜ {B = C})
tw-idle = leaves (λ ρ _ n → agree-refl n _) (λ ρ d → d) unpinned , λ ρ d → d

tw-restᵀ : ∀ {Γ A B C} (x : U.Node Γ A) → Twin (U.restᶜ {B = B} x) (U.restᶜ {B = C} x)
tw-restᵀ x = tw-trans (tw-rest x) (tw-sym (tw-rest x))

tw-bursting : ∀ {Γ A B C} r (t : U.Node Γ A) → Twin (U.burstingᶜ {B = B} r t) (U.burstingᶜ {B = C} r t)
tw-bursting r t = leaves (λ ρ _ n → agree-refl n _) (λ ρ d → d) (bursts-pinned r t (U.step t)) , λ ρ d → d

-- A union's next step pins as its halves swapped.
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

-- Two pairs leaving alike, joined each the other way round: a tail is
-- positions alone, so the halves in order merge alike either way.
lv-swap : ∀ {Γ A B} {x y : U.Node Γ A} {x′ y′ : U.Node Γ B} → Leaves x x′ → Leaves y y′ → Leaves (U.unionᶜ x y) (U.unionᶜ y′ x′)
lv-swap {x = x} {y} {x′} {y′} lx@(leaves ax dx px) ly@(leaves ay dy py) = leaves ag dp (union-swap px py)
  where
    dx′ : ∀ ρ → Deep (U.restᶜ {B = ⊤} (U.unionᶜ x y)) ρ → DeepR x′ ρ
    dx′ ρ e = proj₂ (dx ρ (deepR-rest (proj₁ (proj₂ e))))
    dy′ : ∀ ρ → Deep (U.restᶜ {B = ⊤} (U.unionᶜ x y)) ρ → DeepR y′ ρ
    dy′ ρ e = proj₂ (dy ρ (deepR-rest (proj₂ (proj₂ e))))
    ag : ∀ ρ → Deep (U.restᶜ {B = ⊤} (U.unionᶜ x y)) ρ → ∀ n → Agree n (U.meaning (U.restᶜ {B = ⊤} (U.unionᶜ x y)) ρ) (U.meaning (U.restᶜ {B = ⊤} (U.unionᶜ y′ x′)) ρ)
    ag ρ e n = tailᴱ-ne (agreeᵀ-trans
      (∪-ne (tail-agreeᵀ (U.cutᴺ x ρ) (U.cutᴺ x′ ρ) (ax ρ (deepR-rest (proj₁ (proj₂ e))) n))
            (tail-agreeᵀ (U.cutᴺ y ρ) (U.cutᴺ y′ ρ) (ay ρ (deepR-rest (proj₂ (proj₂ e))) n)))
      (∪-comm n (U.cutᴺ x′ ρ) (U.cutᴺ y′ ρ) (deep-cutR x′ (dx′ ρ e)) (deep-cutR y′ (dy′ ρ e))))
    dp : ∀ ρ → Deep (U.restᶜ {B = ⊤} (U.unionᶜ x y)) ρ → Deep (U.restᶜ {B = ⊤} (U.unionᶜ y′ x′)) ρ
    dp ρ e = deepR-rest {c = U.unionᶜ y′ x′} (dy′ ρ e , dx′ ρ e)

tw-swap : ∀ {Γ A B} {x y : U.Node Γ A} {x′ y′ : U.Node Γ B} → Twin x x′ → Twin y y′ → Twin (U.unionᶜ x y) (U.unionᶜ y′ x′)
tw-swap tx ty = lv-swap (proj₁ tx) (proj₁ ty) , Leaves.deep (lv-swap (proj₁ (tw-sym ty)) (proj₁ (tw-sym tx)))

------------------------------------------------------------------------
-- A restful node's leaving, carried along

lv-tie : ∀ {Γ A B C} {p : U.Node Γ A} {a : U.Node Γ B} {b : U.Node Γ C} → Leaves p a × Restful p → Leaves a b → Leaves p b × Restful p
lv-tie (l , rf) l′ = lv-trans l l′ , rf

tw-tie : ∀ {Γ A B C} {p : U.Node Γ A} {a : U.Node Γ B} {b : U.Node Γ C} → Twin p a × Restful p → Twin a b → Twin p b × Restful p
tw-tie (t , rf) t′ = tw-trans t t′ , rf

-- A restful node leaving as another steps as the other rests.
tied-of : ∀ {Γ A B} {x : U.Node Γ A} {y : U.Node Γ B} → Leaves x y × Restful x → Tied x y
tied-of {x = x} (l , rf) = pinned-trans (restful-pinned rf) (pinned-trans (rest-pinned x) (Leaves.pin l))
