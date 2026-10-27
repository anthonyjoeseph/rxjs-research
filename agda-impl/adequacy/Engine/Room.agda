{-# OPTIONS --guardedness #-}

-- A SUBTREE PLANTED IN A CAUSAL TREE (`plant`): a hole's subtree swapped
-- for one whose keys are the old ones plus new ones (`Grow`), the new
-- causal under the hole's context, is causal when every part racing the
-- hole has room for the new keys (`Room`): each of its keys far from
-- every new one, and a body's free of a source's.  Nothing else reads
-- the hole: a node's own condition reads its racing parts, never itself.
module adequacy.Engine.Room where

open import Data.List using (List; []; _∷_; _++_; _ʳ++_; reverse)
open import Data.List.Properties using (ʳ++-defn; ++-identityʳ; reverse-involutive)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym; trans)

open import Tree using (Obs)
open import denotation.MonotonicList.Events using (Timeline)
open import operation.Key using (Key)
open import operation.PureObservable using (module Machine)
open import adequacy.Engine.Causal using (Farᴷ; Freeᴷ; Fut; Every; Keys⁺; KidKeys⁺; LaneKeys⁺; Aloft⁺; CausalW; KidsW; LanesW;
  Causal; walk-at; own-conn; owned)

open Machine using (St; pend; coldS; ofS; doneS; joinS; mapS; scanS; cutS; lnS; takeS; flatS; connS; Ctx; top; inMap; inScan; inCut; inLn; inTake;
  inOuter; inLanes; inSrc; inBody; plug; attached; attAt; free; cpAt; cutAt; overAt)

------------------------------------------------------------------------
-- Room

-- A key far from, or a mark free of, every new key.
Clear : (Key → Set) → Key → Set
Clear N k = ∀ {h} → N h → Farᴷ k h

Clean : (Key → Set) → Key → Set
Clean N k = ∀ {h} → N h → Freeᴷ k h

-- Every part racing the hole has room for the new keys.
Room : ∀ {R Γ A} → (Key → Set) → Ctx R Γ A → Set
Room N top                                = ⊤
Room N (inMap f c)                        = Room N c
Room N (inScan f z c)                     = Room N c
Room N (inCut l a c)                      = Room N c
Room N (inLn b c)                         = Room N c
Room N (inTake i q w c)                   = Room N c
Room N (inOuter op f d n q ls c)          = LaneKeys⁺ (Clear N) ls × Room N c
Room N (inLanes op f d n q o pre post c)  = Keys⁺ (Clear N) o × LaneKeys⁺ (Clear N) pre × LaneKeys⁺ (Clear N) post × Room N c
Room N (inSrc kk b c)                     = Keys⁺ (λ k → Clear N k × Clean N k) b × Room N c
Room N (inBody kk o c)                    = Keys⁺ (Clear N) o × Room N c

-- The new subtree's keys: the old ones, and new ones.
Grow : ∀ {Γ A} → (Key → Set) → St Γ A → St Γ A → Set₁
Grow N t t′ = ∀ {P : Key → Set} → Keys⁺ P t → (∀ {h} → N h → P h) → Keys⁺ P t′

------------------------------------------------------------------------
-- The hole is not read

aloft-hole : ∀ {R Γ A} {k} (c : Ctx R Γ A) {t t′ : St Γ A} → Aloft⁺ k c t → Aloft⁺ k c t′
aloft-hole top                               a                = tt
aloft-hole (inMap f c)                       a                = aloft-hole c a
aloft-hole (inScan f z c)                    a                = aloft-hole c a
aloft-hole (inCut l x c)                     a                = aloft-hole c a
aloft-hole (inLn b c)                        a                = aloft-hole c a
aloft-hole (inTake i q w c)                  a                = aloft-hole c a
aloft-hole (inOuter op f d n q ls c)         (l , a)          = l , aloft-hole c a
aloft-hole (inLanes op f d n q o pre post c) (x , p , r , a)  = x , p , r , aloft-hole c a
aloft-hole (inSrc kk b c) {t} {t′}           (x , m , a)      =
  x , (λ g → m (owned (own-conn kk {t′} {t} {b} {b}) g)) , aloft-hole c a
aloft-hole (inBody kk o c) {t} {t′}          (x , y , m , a)  =
  x , y , (λ g → m (owned (own-conn kk {o} {o} {t′} {t}) g)) , aloft-hole c a

-- A node keyed as before, its children changed: its own condition kept.
up : ∀ {R Γ A} (c : Ctx R Γ A) {t t′ : St Γ A} → (∀ {h} → Fut t′ h → Fut t h) → Every (λ h → Aloft⁺ h c t) t
   → Every (λ h → Aloft⁺ h c t′) t′
up c back e f = aloft-hole c (e (back f))

------------------------------------------------------------------------
-- A context swapped, its every reader satisfied

mutual
  swap-causal : ∀ {R Γ A} {Q : Key → Set} {c c′ : Ctx R Γ A} → (∀ {k t t′} → Q k → Aloft⁺ k c t → Aloft⁺ k c′ t′)
              → (s : St Γ A) → Keys⁺ Q s → CausalW c s → CausalW c′ s
  swap-causal hy s (q , kq) (m , k) = (λ f → hy (q f) (m f)) , swap-kids hy s kq k

  swap-kids : ∀ {R Γ A} {Q : Key → Set} {c c′ : Ctx R Γ A} → (∀ {k t t′} → Q k → Aloft⁺ k c t → Aloft⁺ k c′ t′)
            → (s : St Γ A) → KidKeys⁺ Q s → KidsW c s → KidsW c′ s
  swap-kids hy (pend o)                kq        k         = tt
  swap-kids hy (coldS b l)             kq        k         = tt
  swap-kids hy (ofS i p xs)            kq        k         = tt
  swap-kids hy doneS                   kq        k         = tt
  swap-kids hy (joinS j g x ib)        kq        k         = tt
  swap-kids hy (mapS f s)              kq        k         = swap-causal (λ {k} {t} {t′} → hy {k} {mapS f t} {mapS f t′}) s kq k
  swap-kids hy (scanS f z s)           kq        k         = swap-causal (λ {k} {t} {t′} → hy {k} {scanS f z t} {scanS f z t′}) s kq k
  swap-kids hy (cutS l a s)            kq        k         = swap-causal (λ {k} {t} {t′} → hy {k} {cutS l a t} {cutS l a t′}) s kq k
  swap-kids hy (lnS b s)               kq        k         = swap-causal (λ {k} {t} {t′} → hy {k} {lnS b t} {lnS b t′}) s kq k
  swap-kids hy (takeS i q w s)         kq        k         = swap-causal (λ {k} {t} {t′} → hy {k} {takeS i q w t} {takeS i q w t′}) s kq k
  swap-kids hy (flatS op f d n q o ls) (ko , kl) (co , cl) =
    swap-causal (λ { {k} {t} {t′} qk (l , a) → l , hy {k} {flatS op f d n q t ls} {flatS op f d n q t′ ls} qk a }) o ko co ,
    swap-lanes hy op f d n q o [] ls kl cl
  swap-kids hy (connS kk o b)          (ko , kb) (co , cb) =
    swap-causal (λ { {k} {t} {t′} qk (x , m , a) →
      x , (λ {_} z → m (owned (own-conn kk {t′} {t} {b} {b}) z)) , hy {k} {connS kk t b} {connS kk t′ b} qk a }) o ko co ,
    swap-causal (λ { {k} {t} {t′} qk (x , y , m , a) →
      x , y , (λ {_} z → m (owned (own-conn kk {o} {o} {t′} {t}) z)) , hy {k} {connS kk o t} {connS kk o t′} qk a }) b kb cb

  swap-lanes : ∀ {R Γ A B} {Q : Key → Set} {c c′ : Ctx R Γ B} → (∀ {k t t′} → Q k → Aloft⁺ k c t → Aloft⁺ k c′ t′)
             → ∀ op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) pre ls → LaneKeys⁺ Q ls → LanesW c op f d n q o pre ls
             → LanesW c′ op f d n q o pre ls
  swap-lanes hy op f d n q o pre []       kl        l        = tt
  swap-lanes hy op f d n q o pre (s ∷ ls) (ks , kl) (w , l) =
    swap-causal (λ { {k} {t} {t′} qk (x , p , r , a) →
      x , p , r , hy {k} {flatS op f d n q o (pre ʳ++ t ∷ ls)} {flatS op f d n q o (pre ʳ++ t′ ∷ ls)} qk a }) s ks w ,
    swap-lanes hy op f d n q o (s ∷ pre) ls kl l

------------------------------------------------------------------------
-- Lanes grown

lane-grow : ∀ {Γ A} {P : Key → Set} {t t′ : St Γ A} ys post → (Keys⁺ P t → Keys⁺ P t′)
          → LaneKeys⁺ P (ys ++ t ∷ post) → LaneKeys⁺ P (ys ++ t′ ∷ post)
lane-grow []       post g (kt , kp) = g kt , kp
lane-grow (y ∷ ys) post g (ky , r)  = ky , lane-grow ys post g r

lane-growʳ : ∀ {Γ A} {P : Key → Set} {t t′ : St Γ A} pre post → (Keys⁺ P t → Keys⁺ P t′)
           → LaneKeys⁺ P (pre ʳ++ t ∷ post) → LaneKeys⁺ P (pre ʳ++ t′ ∷ post)
lane-growʳ {P = P} pre post g x =
  subst (LaneKeys⁺ P) (sym (ʳ++-defn pre)) (lane-grow (reverse pre) post g (subst (LaneKeys⁺ P) (ʳ++-defn pre) x))

lanes-ʳ++ : ∀ {Γ A} {P : Key → Set} (xs : List (St Γ A)) {ys} → LaneKeys⁺ P xs → LaneKeys⁺ P ys → LaneKeys⁺ P (xs ʳ++ ys)
lanes-ʳ++ []       kx        ky = ky
lanes-ʳ++ (x ∷ xs) (k , kxs) ky = lanes-ʳ++ xs kxs (k , ky)

lanes-rev : ∀ {Γ A} {P : Key → Set} (xs : List (St Γ A)) → LaneKeys⁺ P xs → LaneKeys⁺ P (reverse xs)
lanes-rev {P = P} xs k = subst (LaneKeys⁺ P) (trans (ʳ++-defn xs) (++-identityʳ _)) (lanes-ʳ++ xs k tt)

-- Every lane beside a grown one, or under a grown outer, kept.
module _ {R Γ A B} {N : Key → Set} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q where

  lanes-outer : ∀ {t t′ : St Γ A} → Grow N t t′ → ∀ pre ls → LaneKeys⁺ (Clear N) ls → LanesW c op f d n q t pre ls
              → LanesW c op f d n q t′ pre ls
  lanes-outer g pre []       kl        l       = tt
  lanes-outer g pre (s ∷ ls) (ks , kl) (w , l) =
    swap-causal (λ { {k} qk (x , p , r , a) → g x qk , p , r , aloft-hole c a }) s ks w , lanes-outer g (s ∷ pre) ls kl l

  module _ (o : St Γ A) {t t′ : St Γ B} (g : Grow N t t′) where

    lanes-after : ∀ zs acc ls → LaneKeys⁺ (Clear N) ls → LanesW c op f d n q o (zs ++ t ∷ acc) ls
                → LanesW c op f d n q o (zs ++ t′ ∷ acc) ls
    lanes-after zs acc []       kl        l       = tt
    lanes-after zs acc (s ∷ ls) (ks , kl) (w , l) =
      swap-causal (λ { {k} qk (x , p , r , a) → x , lane-grow zs acc (λ z → g z qk) p , r , aloft-hole c a }) s ks w ,
      lanes-after (s ∷ zs) acc ls kl l

    lanes-before : ∀ ys acc post → LaneKeys⁺ (Clear N) ys → LaneKeys⁺ (Clear N) post
                 → CausalW (inLanes op f d n q o (ys ʳ++ acc) post c) t′
                 → LanesW c op f d n q o acc (ys ++ t ∷ post) → LanesW c op f d n q o acc (ys ++ t′ ∷ post)
    lanes-before []       acc post ky        kp w (_ , l)  = w , lanes-after [] acc post kp l
    lanes-before (y ∷ ys) acc post (k , kys) kp w (wy , l) =
      swap-causal (λ { {h} qk (x , p , r , a) → x , p , lane-grow ys post (λ z → g z qk) r , aloft-hole c a }) y k wy ,
      lanes-before ys (y ∷ acc) post kys kp w l

    lanes-hole : ∀ pre post → LaneKeys⁺ (Clear N) pre → LaneKeys⁺ (Clear N) post → CausalW (inLanes op f d n q o pre post c) t′
               → LanesW c op f d n q o [] (pre ʳ++ t ∷ post) → LanesW c op f d n q o [] (pre ʳ++ t′ ∷ post)
    lanes-hole pre post kp kq w l =
      subst (LanesW c op f d n q o []) (sym (ʳ++-defn pre))
        (lanes-before (reverse pre) [] post (lanes-rev pre kp) kq (subst (λ a → CausalW (inLanes op f d n q o a post c) t′) (sym eq) w)
          (subst (LanesW c op f d n q o []) (ʳ++-defn pre) l))
      where
        eq : reverse pre ʳ++ [] ≡ pre
        eq = trans (ʳ++-defn (reverse pre)) (trans (++-identityʳ _) (reverse-involutive pre))

------------------------------------------------------------------------
-- Planted

fut-cut : ∀ {Γ A} l a {t t′ : St Γ A} {h} → Fut (cutS l a t′) h → Fut (cutS l a t) h
fut-cut l attached  f = f
fut-cut l (attAt p) f = f

fut-take : ∀ {Γ A} i q w {t t′ : St Γ A} {h} → Fut (takeS i q w t′) h → Fut (takeS i q w t) h
fut-take i q free       f = f
fut-take i q (cpAt p)   f = f
fut-take i q (cutAt p)  f = f
fut-take i q (overAt p) f = f

-- A PLANTED SUBTREE: causal where its hole was, and room for its new keys.
plant : ∀ {R Γ A} {N : Key → Set} (c : Ctx R Γ A) {t t′ : St Γ A}
      → Causal (plug c t) → CausalW c t′ → Grow N t t′ → Room N c → Causal (plug c t′)
plant top ca w g r = w
plant (inMap f c) {t} {t′} ca w g r =
  plant c {mapS f t} {mapS f t′} ca (up c (λ x → x) (proj₁ (walk-at c (mapS f t) ca)) , w) (λ { (e , k) m → e , g k m }) r
plant (inScan f z c) {t} {t′} ca w g r =
  plant c {scanS f z t} {scanS f z t′} ca (up c (λ x → x) (proj₁ (walk-at c (scanS f z t) ca)) , w) (λ { (e , k) m → e , g k m }) r
plant (inCut l a c) {t} {t′} ca w g r =
  plant c {cutS l a t} {cutS l a t′} ca (up c (fut-cut l a) (proj₁ (walk-at c (cutS l a t) ca)) , w)
    (λ { (e , k) m → (λ {_} x → e (fut-cut l a x)) , g k m }) r
plant (inLn b c) {t} {t′} ca w g r =
  plant c {lnS b t} {lnS b t′} ca (up c (λ x → x) (proj₁ (walk-at c (lnS b t) ca)) , w) (λ { (e , k) m → e , g k m }) r
plant (inTake i q w′ c) {t} {t′} ca w g r =
  plant c {takeS i q w′ t} {takeS i q w′ t′} ca (up c (fut-take i q w′) (proj₁ (walk-at c (takeS i q w′ t) ca)) , w)
    (λ { (e , k) m → (λ {_} x → e (fut-take i q w′ x)) , g k m }) r
plant (inOuter op f d n q ls c) {t} {t′} ca w g (rl , r) =
  plant c {flatS op f d n q t ls} {flatS op f d n q t′ ls} ca
    (up c (λ x → x) (proj₁ old) , w , lanes-outer c op f d n q g [] ls rl (proj₂ (proj₂ old)))
    (λ { (e , ko , kl) m → e , g ko m , kl }) r
  where old = walk-at c (flatS op f d n q t ls) ca
plant (inLanes op f d n q o pre post c) {t} {t′} ca w g (ro , rp , rq , r) =
  plant c {flatS op f d n q o (pre ʳ++ t ∷ post)} {flatS op f d n q o (pre ʳ++ t′ ∷ post)} ca
    (up c (λ x → x) (proj₁ old) ,
     swap-causal (λ { {k} qk (l , a) → lane-growʳ pre post (λ z → g z qk) l , aloft-hole c a }) o ro (proj₁ (proj₂ old)) ,
     lanes-hole c op f d n q o g pre post rp rq w (proj₂ (proj₂ old)))
    (λ { (e , ko , kl) m → e , ko , lane-growʳ pre post (λ z → g z m) kl }) r
  where old = walk-at c (flatS op f d n q o (pre ʳ++ t ∷ post)) ca
plant (inSrc kk b c) {t} {t′} ca w g (rb , r) =
  plant c {connS kk t b} {connS kk t′ b} ca
    (up c (owned (own-conn kk {t′} {t} {b} {b})) (proj₁ old) , w ,
     swap-causal (λ { {k} {u} {u′} (cl , cn) (x , y , m , a) →
       g x cl , g y cn , (λ {_} z → m (owned (own-conn kk {t′} {t} {u′} {u}) z)) , aloft-hole c a }) b rb (proj₂ (proj₂ old)))
    (λ { (e , ko , kb) m → (λ {_} z → e (owned (own-conn kk {t′} {t} {b} {b}) z)) , g ko m , kb }) r
  where old = walk-at c (connS kk t b) ca
plant (inBody kk o c) {t} {t′} ca w g (ro , r) =
  plant c {connS kk o t} {connS kk o t′} ca
    (up c (owned (own-conn kk {o} {o} {t′} {t})) (proj₁ old) ,
     swap-causal (λ { {k} {u} {u′} qk (x , m , a) →
       g x qk , (λ {_} z → m (owned (own-conn kk {u′} {u} {t′} {t}) z)) , aloft-hole c a }) o ro (proj₁ (proj₂ old)) ,
     w)
    (λ { (e , ko , kb) m → (λ {_} z → e (owned (own-conn kk {o} {o} {t′} {t}) z)) , ko , g kb m }) r
  where old = walk-at c (connS kk o t) ca
