{-# OPTIONS --guardedness #-}

-- KEYS KEPT BY A STEP.  A `Closed` `Q` is kept one mark on, at
-- a frame tagged with it, and at a fed or told joiner's tag.  A step of
-- a keyed node shows where `Q` holds and leaves a keyed node; a feed
-- whose tag `Q` admits leaves one too.
--
-- A connect's body subscribes where every position it holds is owned by
-- its subscription, and its source where every one is disjoint from it:
-- `Apart`, each key kept by a step and the body's by a feed.
module port.Placed.Heads where

open import Data.Bool using (true; false)
open import Data.Sum using (inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_; [_]; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to All++⁺)
open import Data.Nat using (zero; suc; _+_; _<ᵇ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_)

import Tree as T
open import Tree using (Obs; Later; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.MonotonicList.Events using (timelineAt; Pos; From; Timeline; ix; sub; last; _<ᵖ_; inside)
import denotation.MonotonicList.Events as M
import denotation.Unfold as U
open import port.Placed.Order using (Alienᴱ; Apart; Disjoint; Headed; Owned; Placed;
  Prefix; Sides; Within; every-monoᴱ; prefix-++)
open import port.Placed.Keyed using (Admitted; Fit; Keyed; KeyedEarliest; KeyedOuter; KeyedStep; Keyedᴸ; Keyedᴹ; Keyedˢ; Noted; Qᴹ; keyed-head)
open import denotation.Unfold using (NEnv)
open import port.Placed.Keys using (Mark; ix-mark; last-mark; owned-tagged; owned-trans; prefix-refl; sibling; tagged-sub)
open import port.Placed.Rising using (apart-join; apart-mark)

-- Kept one mark on, at a frame tagged with it, and at a joiner's tag.
record Closed (Q : Pos → Set) : Set where
  field
    mark  : ∀ k l → Mark l → Q k → Q (k ++ [ l ])
    frame : ∀ t r → Q r → Q (ix t ∷ sub r ∷ [])
    tag   : ∀ q j → Q q → Q j → Q (q ++ [ sub j ])
open Closed

keyed-start : ∀ {Q} → Closed Q → ∀ {Γ A} p (m : From A 0) → Q p → Keyed Q (U.startᶜ {Γ} p m)
keyed-start cq p (M.at zero _ b)    qp = qp
keyed-start cq p (M.at (suc t) _ b) qp = mark cq p last last-mark qp
keyed-start cq p M.done             qp = mark cq p last last-mark qp
keyed-start cq p M.quiet            qp = mark cq p last last-mark qp

-- A program subscribed where `Q` holds is keyed.
keyed-sub : ∀ {Q} → Closed Q → ∀ {Γ A} (o : Obs Timeline Γ A) p → Q p → Keyed Q (U.subscribe o p)
keyed-sub cq (cold c)          p qp = keyed-start cq p (timelineAt c p) qp
keyed-sub cq empty             p qp = qp
keyed-sub cq (of xs)           p qp = qp
keyed-sub cq (map f s)         p qp = keyed-sub cq s p qp
keyed-sub cq (scan f z s)      p qp = keyed-sub cq s p qp
keyed-sub cq (takeWhile i f s) p qp = keyed-sub cq s p qp
keyed-sub cq (flatMap op f s)  p qp = (λ a q qq → keyed-sub cq (f a) q qq) , keyed-sub cq s p qp , tt , tt
keyed-sub cq (connect s b)     p qp =
  keyed-sub cq b (p ++ [ ix 0 ]) (mark cq p (ix 0) (ix-mark 0) qp) , keyed-sub cq s (p ++ [ ix 1 ]) (mark cq p (ix 1) (ix-mark 1) qp)
keyed-sub cq (connected i)     p qp = qp , []ᴬ , tt
keyed-sub cq (defer l)         p qp = qp , tt

fit : ∀ {Q} → Closed Q → ∀ q → Q q → Fit Q q
fit cq q qq j qj = tag cq q j qq qj

-- Fed or told, a joiner keeps its key.
fed-keyed : ∀ {Q} → Closed Q → ∀ {Γ A B} (i : A ∈ Γ) q (a : Maybe A) (j : B ∈ Γ) p xs (m : Maybe (A ≡ B))
          → Fit Q q → Q p → All (λ x → Q (proj₁ x)) xs → All (λ x → Q (proj₁ x)) (U.fed i q a j p xs m)
fed-keyed cq i q a j p xs (just refl) fq qp kx with p <ᵖ q
... | true  = All++⁺ kx (fq p qp ∷ᴬ []ᴬ)
... | false = All++⁺ kx (mark cq p (ix 0) (ix-mark 0) qp ∷ᴬ []ᴬ)
fed-keyed cq i q a j p xs nothing     fq qp kx = kx

told-keyed : ∀ {Q} → Closed Q → ∀ {Γ A B} (i : A ∈ Γ) c (j : B ∈ Γ) p e (m : Maybe (A ≡ B))
           → Fit Q c → Q p → Qᴹ Q e → Qᴹ Q (U.told i c j p e m)
told-keyed cq i c j p nothing  (just refl) fc qp _ with p <ᵖ c
... | true  = fc p qp
... | false = mark cq p last last-mark qp
told-keyed cq i c j p (just e) (just refl) fc qp ke = ke
told-keyed cq i c j p nothing  nothing     fc qp ke = ke
told-keyed cq i c j p (just e) nothing     fc qp ke = ke

noted-++ : ∀ {Q Γ A} (ns : List (U.Notice Γ)) (i : A ∈ Γ) q (a : Maybe A) → Noted Q ns → Fit Q q → Noted Q (ns ++ [ U.notice i q a ])
noted-++ []                    i q a _        fq = fq , tt
noted-++ (U.notice _ _ _ ∷ ns) i q a (f , kn) fq = f , noted-++ ns i q a kn fq

-- A keyed node fed a step whose tag `Q` admits is keyed.
mutual
  feed-keyed : ∀ {Q} → Closed Q → ∀ {Γ A B} (i : A ∈ Γ) q (a : Maybe A) (c : U.Node Γ B) → Fit Q q → Keyed Q c
             → Keyed Q (U.feed i q a c)
  feed-keyed cq i q a (U.framesᶜ τ e m)            fq k                 = k
  feed-keyed cq i q a (U.burstᶜ τ r n b)           fq k                 = k
  feed-keyed cq i q a (U.ofᶜ p n xs)               fq k                 = k
  feed-keyed cq i q a (U.mapᶜ f c)                 fq k                 = feed-keyed cq i q a c fq k
  feed-keyed cq i q a (U.scanᶜ f z c)              fq k                 = feed-keyed cq i q a c fq k
  feed-keyed cq i q a (U.takeWhileᶜ b f c)         fq k                 = feed-keyed cq i q a c fq k
  feed-keyed cq i q a (U.flatMapᶜ op g o ls qs pl) fq (kg , ko , kl , kp) =
    (λ x r qr → feed-keyed cq i q a (g x r) fq (kg x r qr)) , feedᴹ-keyed cq i q a o fq ko , feedᴸ-keyed cq i q a ls fq kl , feed-keyed cq i q a pl fq kp
  feed-keyed cq i q a (U.joinᶜ j p xs e)           fq (qp , kx , ke)    = qp , fed-keyed cq i q a j p xs (U.same? i j) fq qp kx , ke
  feed-keyed cq i q a (U.connectᶜ r b s)           fq (kb , ks)         = feed-keyed cq (there i) q a b fq kb , feedˢ-keyed cq i q a s fq ks
  feed-keyed cq i q a (U.deferᶜ l p ns)            fq (qp , kn)         = qp , noted-++ ns i q a kn fq
  feed-keyed cq i q a (U.endingᶜ p n)              fq (qp , kn)         = qp , feed-keyed cq i q a n fq kn
  feed-keyed cq i q a (U.restᶜ n)                  fq k                 = feed-keyed cq i q a n fq k
  feed-keyed cq i q a U.idleᶜ                      fq k                 = k
  feed-keyed cq i q a (U.unionᶜ x y)               fq (kx , ky)         = feed-keyed cq i q a x fq kx , feed-keyed cq i q a y fq ky
  feed-keyed cq i q a (U.burstingᶜ r t)            fq k                 = feed-keyed cq i q a t fq k
  feed-keyed cq i q a (U.underᶜ s b)               fq (ks , kb)         = feedˢ-keyed cq i q a s fq ks , feed-keyed cq (there i) q a b fq kb

  feedᴹ-keyed : ∀ {Q} → Closed Q → ∀ {Γ A B} (i : A ∈ Γ) q (a : Maybe A) (o : Maybe (U.Node Γ B)) → Fit Q q → Keyedᴹ Q o
              → Keyedᴹ Q (U.feedᴹ i q a o)
  feedᴹ-keyed cq i q a nothing  fq k = k
  feedᴹ-keyed cq i q a (just c) fq k = feed-keyed cq i q a c fq k

  feedᴸ-keyed : ∀ {Q} → Closed Q → ∀ {Γ A B} (i : A ∈ Γ) q (a : Maybe A) (cs : List (U.Node Γ B)) → Fit Q q → Keyedᴸ Q cs
              → Keyedᴸ Q (U.feedᴸ i q a cs)
  feedᴸ-keyed cq i q a []       fq k          = k
  feedᴸ-keyed cq i q a (c ∷ cs) fq (kc , kcs) = feed-keyed cq i q a c fq kc , feedᴸ-keyed cq i q a cs fq kcs

  feedˢ-keyed : ∀ {Q} → Closed Q → ∀ {Γ A B} (i : A ∈ Γ) q (a : Maybe A) (s : U.Source Γ B) → Fit Q q → Keyedˢ Q s
              → Keyedˢ Q (U.feedˢ i q a s)
  feedˢ-keyed cq i q a (U.live s)    fq k         = feed-keyed cq i q a s fq k
  feedˢ-keyed cq i q a (U.ended c t) fq (qc , kt) = qc , feed-keyed cq i q a t fq kt

feeds-keyed : ∀ {Q} → Closed Q → ∀ {Γ B} (ns : List (U.Notice Γ)) (c : U.Node Γ B) → Noted Q ns → Keyed Q c → Keyed Q (U.feeds ns c)
feeds-keyed cq []                    c _         kc = kc
feeds-keyed cq (U.notice i q a ∷ ns) c (fq , kn) kc = feeds-keyed cq ns (U.feed i q a c) kn (feed-keyed cq i q a c fq kc)

-- A keyed node told its source's end, where `Q` admits its tag, is keyed.
mutual
  shut-keyed : ∀ {Q} → Closed Q → ∀ {Γ A B} (i : A ∈ Γ) c (n : U.Node Γ B) → Fit Q c → Keyed Q n → Keyed Q (U.shut i c n)
  shut-keyed cq i c (U.framesᶜ τ e m)            fc k                   = k
  shut-keyed cq i c (U.burstᶜ τ r n b)           fc k                   = k
  shut-keyed cq i c (U.ofᶜ p n xs)               fc k                   = k
  shut-keyed cq i c (U.mapᶜ f n)                 fc k                   = shut-keyed cq i c n fc k
  shut-keyed cq i c (U.scanᶜ f z n)              fc k                   = shut-keyed cq i c n fc k
  shut-keyed cq i c (U.takeWhileᶜ b f n)         fc k                   = shut-keyed cq i c n fc k
  shut-keyed cq i c (U.flatMapᶜ op g o ls qs pl) fc (kg , ko , kl , kp) =
    kg , shutᴹ-keyed cq i c o fc ko , shutᴸ-keyed cq i c ls fc kl , shut-keyed cq i c pl fc kp
  shut-keyed cq i c (U.joinᶜ j p xs e)           fc (qp , kx , ke)      = qp , kx , told-keyed cq i c j p e (U.same? i j) fc qp ke
  shut-keyed cq i c (U.connectᶜ r b s)           fc (kb , ks)           = shut-keyed cq (there i) c b fc kb , shutˢ-keyed cq i c s fc ks
  shut-keyed cq i c (U.deferᶜ l p ns)            fc k                   = k
  shut-keyed cq i c (U.endingᶜ p n)              fc (qp , kn)           = qp , shut-keyed cq i c n fc kn
  shut-keyed cq i c (U.restᶜ n)                  fc k                   = shut-keyed cq i c n fc k
  shut-keyed cq i c U.idleᶜ                      fc k                   = k
  shut-keyed cq i c (U.unionᶜ x y)               fc (kx , ky)           = shut-keyed cq i c x fc kx , shut-keyed cq i c y fc ky
  shut-keyed cq i c (U.burstingᶜ r t)            fc k                   = shut-keyed cq i c t fc k
  shut-keyed cq i c (U.underᶜ s b)               fc (ks , kb)           = shutˢ-keyed cq i c s fc ks , shut-keyed cq (there i) c b fc kb

  shutᴹ-keyed : ∀ {Q} → Closed Q → ∀ {Γ A B} (i : A ∈ Γ) c (o : Maybe (U.Node Γ B)) → Fit Q c → Keyedᴹ Q o → Keyedᴹ Q (U.shutᴹ i c o)
  shutᴹ-keyed cq i c nothing  fc k = k
  shutᴹ-keyed cq i c (just n) fc k = shut-keyed cq i c n fc k

  shutᴸ-keyed : ∀ {Q} → Closed Q → ∀ {Γ A B} (i : A ∈ Γ) c (ns : List (U.Node Γ B)) → Fit Q c → Keyedᴸ Q ns → Keyedᴸ Q (U.shutᴸ i c ns)
  shutᴸ-keyed cq i c []       fc k          = k
  shutᴸ-keyed cq i c (n ∷ ns) fc (kn , kns) = shut-keyed cq i c n fc kn , shutᴸ-keyed cq i c ns fc kns

  shutˢ-keyed : ∀ {Q} → Closed Q → ∀ {Γ A B} (i : A ∈ Γ) c (s : U.Source Γ B) → Fit Q c → Keyedˢ Q s → Keyedˢ Q (U.shutˢ i c s)
  shutˢ-keyed cq i c (U.live s)    fc k         = shut-keyed cq i c s fc k
  shutˢ-keyed cq i c (U.ended e t) fc (qe , kt) = qe , shut-keyed cq i c t fc kt

------------------------------------------------------------------------
-- A step, operator by operator

burst-keyed : ∀ {Q} → Closed Q → ∀ {Γ A t} τ r i (b : M.Frame A t) → Q r → KeyedStep Q (U.burstˢ {Γ} τ r i b)
burst-keyed cq τ r i (M.emit a k) qr = mark cq r (ix i) (ix-mark i) qr , qr
burst-keyed cq τ r i (M.stall k)  qr = mark cq r (ix i) (ix-mark i) qr , qr
burst-keyed cq τ r i (M.close k)  qr = mark cq r (ix i) (ix-mark i) qr , mark cq r last last-mark qr

frames-keyed : ∀ {Q} → Closed Q → ∀ {Γ A t} τ e (m : From A t) → Q e → KeyedStep Q (U.framesˢ {Γ} τ e m)
frames-keyed cq τ e M.done       qe = qe
frames-keyed cq τ e M.quiet      qe = tt
frames-keyed cq τ e (M.at t _ b) qe = burst-keyed cq τ (ix (τ + t) ∷ sub e ∷ []) 0 b (frame cq (τ + t) e qe)

of-keyed : ∀ {Q} → Closed Q → ∀ {Γ A} p i (xs : List A) → Q p → KeyedStep Q (U.ofˢ {Γ} p i xs)
of-keyed cq p i []       qp = mark cq p last last-mark qp
of-keyed cq p i (x ∷ xs) qp = mark cq p (ix i) (ix-mark i) qp , qp

map-keyed : ∀ {Q} → Closed Q → ∀ {Γ A B} (f : A → B) (t : U.Step Γ A) → KeyedStep Q t → KeyedStep Q (U.mapˢ f t)
map-keyed cq f (U.outˢ k a c) kt = kt
map-keyed cq f (U.skipˢ k c)  kt = kt
map-keyed cq f (U.endˢ k)     kt = kt
map-keyed cq f U.hushˢ        kt = kt

scan-keyed : ∀ {Q} → Closed Q → ∀ {Γ A B} (f : B → A → B) z (t : U.Step Γ A) → KeyedStep Q t → KeyedStep Q (U.scanˢ f z t)
scan-keyed cq f z (U.outˢ k a c) kt = kt
scan-keyed cq f z (U.skipˢ k c)  kt = kt
scan-keyed cq f z (U.endˢ k)     kt = kt
scan-keyed cq f z U.hushˢ        kt = kt

take-keyed : ∀ {Q} → Closed Q → ∀ {Γ A} i f (t : U.Step Γ A) → KeyedStep Q t → KeyedStep Q (U.takeWhileˢ i f t)
take-keyed cq i f (U.outˢ k a c) (qk , kc) with f a
take-keyed cq i     f (U.outˢ k a c) (qk , kc) | true  = qk , kc
take-keyed cq true  f (U.outˢ k a c) (qk , kc) | false = mark cq k (ix 0) (ix-mark 0) qk , mark cq k last last-mark qk , kc
take-keyed cq false f (U.outˢ k a c) (qk , kc) | false = mark cq k last last-mark qk
take-keyed cq i f (U.skipˢ k c) kt = kt
take-keyed cq i f (U.endˢ k)    kt = kt
take-keyed cq i f U.hushˢ       kt = kt

join-keyed : ∀ {Q} → Closed Q → ∀ {Γ A} (i : A ∈ Γ) p xs e → Q p → All (λ x → Q (proj₁ x)) xs → Qᴹ Q e → KeyedStep Q (U.joinˢ i p xs e)
join-keyed cq i p ((q , just a) ∷ xs) e        qp (qq ∷ᴬ kx) ke = qq , qp , kx , ke
join-keyed cq i p ((q , nothing) ∷ xs) e       qp (qq ∷ᴬ kx) ke = qq , qp , kx , ke
join-keyed cq i p []                  (just c) qp _          ke = ke
join-keyed cq i p []                  nothing  qp _          ke = tt

body-keyed : ∀ {Q} → Closed Q → ∀ {Γ A B} r (s : U.Source Γ A) (sb : U.Step (A ∷ Γ) B) → Keyedˢ Q s → KeyedStep Q sb
           → KeyedStep Q (U.bodyˢ r s sb)
body-keyed cq r s (U.outˢ k a b) ks (qk , kb) = qk , kb , ks
body-keyed cq r s (U.skipˢ k b)  ks (qk , kb) = qk , kb , ks
body-keyed cq r s (U.endˢ c)     ks kb        = kb
body-keyed cq r s U.hushˢ        ks kb        = tt

shutᵗ-keyed : ∀ {Q} → Closed Q → ∀ {Γ A B} r c (t : U.Node Γ A) (sb : U.Step (A ∷ Γ) B) → Q c → Keyed Q t → KeyedStep Q sb
            → KeyedStep Q (U.shutˢᵗ r c t sb)
shutᵗ-keyed cq r c t (U.outˢ k a b) qc kt (qk , kb) = qk , shut-keyed cq (here refl) c b (fit cq c qc) kb , qc , kt
shutᵗ-keyed cq r c t (U.skipˢ k b)  qc kt (qk , kb) = qk , shut-keyed cq (here refl) c b (fit cq c qc) kb , qc , kt
shutᵗ-keyed cq r c t (U.endˢ e)     qc kt ke        = ke
shutᵗ-keyed cq r c t U.hushˢ        qc kt _         = tt

source-keyed : ∀ {Q} → Closed Q → ∀ {Γ A B} r (b : U.Node (A ∷ Γ) B) (sb : U.Step (A ∷ Γ) B) (s : U.Node Γ A) (ss : U.Step Γ A)
             → Keyed Q b → KeyedStep Q sb → Keyed Q s → KeyedStep Q ss → KeyedStep Q (U.sourceˢ r b sb s ss)
source-keyed cq r b sb s (U.outˢ q a s′) kb ksb ks (qq , ks′) with U.beforeˢ (q ++ [ ix 0 ]) sb
... | true  = mark cq q (ix 0) (ix-mark 0) qq , feed-keyed cq (here refl) q (just a) b (fit cq q qq) kb , ks′
... | false = body-keyed cq r (U.live s) sb ks ksb
source-keyed cq r b sb s (U.skipˢ q s′) kb ksb ks (qq , ks′) with U.beforeˢ (q ++ [ ix 0 ]) sb
... | true  = mark cq q (ix 0) (ix-mark 0) qq , feed-keyed cq (here refl) q nothing b (fit cq q qq) kb , ks′
... | false = body-keyed cq r (U.live s) sb ks ksb
source-keyed cq r b sb s (U.endˢ c) kb ksb ks qc with U.beforeˢ (c ++ [ ix 0 ]) sb
... | true  = mark cq c (ix 0) (ix-mark 0) qc , shut-keyed cq (here refl) c b (fit cq c qc) kb , qc , ks
... | false = body-keyed cq r (U.live s) sb ks ksb
source-keyed cq r b sb s U.hushˢ kb ksb ks _ = body-keyed cq r (U.live s) sb ks ksb

ended-keyed : ∀ {Q} → Closed Q → ∀ {Γ A B} r (b : U.Node (A ∷ Γ) B) (sb : U.Step (A ∷ Γ) B) c (t : U.Node Γ A) (st : U.Step Γ A)
            → Keyed Q b → KeyedStep Q sb → Q c → Keyed Q t → KeyedStep Q st → KeyedStep Q (U.endedˢ r b sb c t st)
ended-keyed cq r b sb c t (U.skipˢ k t′) kb ksb qc kt (qk , kt′) with U.beforeˢ (k ++ [ ix 0 ]) sb
... | true  = mark cq k (ix 0) (ix-mark 0) qk , kb , qc , kt′
... | false = shutᵗ-keyed cq r c t sb qc kt ksb
ended-keyed cq r b sb c t (U.outˢ k a t′) kb ksb qc kt _ = shutᵗ-keyed cq r c t sb qc kt ksb
ended-keyed cq r b sb c t (U.endˢ k)      kb ksb qc kt _ = shutᵗ-keyed cq r c t sb qc kt ksb
ended-keyed cq r b sb c t U.hushˢ         kb ksb qc kt _ = shutᵗ-keyed cq r c t sb qc kt ksb

union-keyed : ∀ {Q} → Closed Q → ∀ {Γ B} (x : U.Node Γ B) (sx : U.Step Γ B) (y : U.Node Γ B) (sy : U.Step Γ B)
            → Keyed Q x → KeyedStep Q sx → Keyed Q y → KeyedStep Q sy → KeyedStep Q (U.unionˢ x sx y sy)
union-keyed cq x (U.skipˢ k x′) y (U.skipˢ k′ y′) kx (qk , kx′) ky (qk′ , ky′) with k <ᵖ k′
... | true  = qk , kx′ , ky
... | false = qk′ , kx , ky′
union-keyed cq x (U.skipˢ k x′) y (U.outˢ k′ a y′) kx (qk , kx′) ky _ = qk , kx′ , ky
union-keyed cq x (U.skipˢ k x′) y (U.endˢ k′)      kx (qk , kx′) ky _ = qk , kx′ , ky
union-keyed cq x (U.skipˢ k x′) y U.hushˢ          kx (qk , kx′) ky _ = qk , kx′ , ky
union-keyed cq x (U.outˢ k a x′) y sy kx _ ky ksy = ksy
union-keyed cq x (U.endˢ k)      y sy kx _ ky ksy = ksy
union-keyed cq x U.hushˢ         y sy kx _ ky ksy = ksy

under-keyed : ∀ {Q} → Closed Q → ∀ {Γ A B C} (s : U.Source Γ A) (st : U.Step (A ∷ Γ) C) → Keyedˢ Q s → KeyedStep Q st
            → KeyedStep Q (U.underˢ {B = B} s st)
under-keyed cq s (U.skipˢ k b)  ks (qk , kb) = qk , ks , kb
under-keyed cq s (U.outˢ k a b) ks _         = tt
under-keyed cq s (U.endˢ k)     ks _         = tt
under-keyed cq s U.hushˢ        ks _         = tt

keyedᴸ-++ : ∀ {Q Γ B} (bs cs : List (U.Node Γ B)) → Keyedᴸ Q bs → Keyedᴸ Q cs → Keyedᴸ Q (bs ++ cs)
keyedᴸ-++ []       cs _          kcs = kcs
keyedᴸ-++ (b ∷ bs) cs (kb , kbs) kcs = kb , keyedᴸ-++ bs cs kbs kcs

restsᶜ-keyed : ∀ {Q} → Closed Q → ∀ {Γ A B} (ls : List (U.Node Γ A)) → Keyedᴸ Q ls → Keyed Q (U.restsᶜ {B = B} ls)
restsᶜ-keyed cq []       _          = tt
restsᶜ-keyed cq (l ∷ ls) (kl , kls) = kl , restsᶜ-keyed cq ls kls

outerᶜ-keyed : ∀ {Q} → Closed Q → ∀ {Γ A B} (o : Maybe (U.Node Γ A)) → Keyedᴹ Q o → Keyed Q (U.outerᶜ {B = B} o)
outerᶜ-keyed cq nothing  _  = tt
outerᶜ-keyed cq (just o) ko = ko

nodeᵒ-keyed : ∀ {Q Γ A} (o : U.Outer Γ A) → KeyedOuter Q o → Keyedᴹ Q (U.nodeᵒ o)
nodeᵒ-keyed U.doneᵒ       _        = tt
nodeᵒ-keyed (U.runᵒ o so) (ko , _) = ko

pick-keyed : ∀ {Q} → Closed Q → ∀ {Γ B} (l : U.Node Γ B) (s : U.Step Γ B) ls mk (e : U.Earliest Γ B)
           → Keyed Q l → KeyedStep Q s → Keyedᴸ Q ls → KeyedEarliest Q e → KeyedEarliest Q (U.pick l s ls mk e)
pick-keyed cq l s ls nothing  U.none                 kl ks kls ke                     = tt
pick-keyed cq l s ls nothing  (U.found k bs c sc as) kl ks kls (kbs , kc , ksc , kas) = (kl , kbs) , kc , ksc , kas
pick-keyed cq l s ls (just k) U.none                 kl ks kls ke                     = tt , kl , ks , kls
pick-keyed cq l s ls (just k) (U.found k′ bs c sc as) kl ks kls (kbs , kc , ksc , kas) with k <ᵖ k′
... | true  = tt , kl , ks , kls
... | false = (kl , kbs) , kc , ksc , kas

admit-keyed : ∀ {Q} → Closed Q → ∀ {Γ} {A B : Set} op (g : A → Pos → U.Node Γ B) q a ls qs d
            → (∀ a q → Q q → Keyed Q (g a q)) → Q q → Keyedᴸ Q ls → Keyed Q d → Admitted Q (U.admit op g q a ls qs d)
admit-keyed cq (T.mergeᶠ nothing)  g q a ls       qs d kg qq kl kd = (kg a q qq , kl) , tt
admit-keyed cq (T.mergeᶠ (just n)) g q a ls       qs d kg qq kl kd with length ls <ᵇ n
... | true  = (kg a q qq , kl) , tt
... | false = kl , tt
admit-keyed cq T.switchᶠ           g q a ls       qs d kg qq kl kd = (kg a q qq , tt) , kd
admit-keyed cq T.exhaustᶠ          g q a []       qs d kg qq kl kd = (kg a q qq , tt) , tt
admit-keyed cq T.exhaustᶠ          g q a (l ∷ ls) qs d kg qq kl kd = kl , tt

outer-keyed : ∀ {Q} → Closed Q → ∀ {Γ A B} op (g : A → Pos → U.Node Γ B) (o : U.Node Γ A) (so : U.Step Γ A) ls qs p
            → (∀ a q → Q q → Keyed Q (g a q)) → Keyed Q o → KeyedStep Q so → Keyedᴸ Q ls → Keyed Q p
            → KeyedStep Q (U.outerˢ op g o so ls qs p)
outer-keyed cq op g o (U.outˢ q a o′) ls qs p kg ko (qq , ko′) kl kp
  with U.admit op g (q ++ [ ix 1 ]) a ls qs (U.restsᶜ ls)
     | admit-keyed cq op g (q ++ [ ix 1 ]) a ls qs (U.restsᶜ ls) kg (mark cq q (ix 1) (ix-mark 1) qq) kl (restsᶜ-keyed cq ls kl)
... | ls′ , qs′ , d | kl′ , kd = mark cq q (ix 0) (ix-mark 0) qq , kg , ko′ , kl′ , kp , kd
outer-keyed cq op g o (U.skipˢ q o′) ls       qs       p kg ko (qq , ko′) kl kp = qq , kg , ko′ , kl , kp
outer-keyed cq op g o (U.endˢ c)     []       []       p kg ko qc         kl kp = qc
outer-keyed cq op g o (U.endˢ c)     []       (x ∷ qs) p kg ko qc         kl kp = qc , kg , tt , kl , kp , ko
outer-keyed cq op g o (U.endˢ c)     (l ∷ ls) qs       p kg ko qc         kl kp = qc , kg , tt , kl , kp , ko
outer-keyed cq op g o U.hushˢ        ls       qs       p kg ko _          kl kp = tt

lane-keyed : ∀ {Q} → Closed Q → ∀ {Γ A B} op (g : A → Pos → U.Node Γ B) (o : Maybe (U.Node Γ A)) bs (l : U.Node Γ B) (s : U.Step Γ B) as qs p
           → (∀ a q → Q q → Keyed Q (g a q)) → Keyedᴹ Q o → Keyedᴸ Q bs → Keyed Q l → KeyedStep Q s → Keyedᴸ Q as → Keyed Q p
           → KeyedStep Q (U.laneˢ op g o bs l s as qs p)
lane-keyed cq op g o bs l (U.outˢ k b c) as qs p kg ko kbs kl (qk , kc) kas kp = qk , kg , ko , keyedᴸ-++ bs (c ∷ as) kbs (kc , kas) , kp
lane-keyed cq op g o bs l (U.skipˢ k c)  as qs p kg ko kbs kl (qk , kc) kas kp = qk , kg , ko , keyedᴸ-++ bs (c ∷ as) kbs (kc , kas) , kp
lane-keyed cq op g o bs l (U.endˢ c) as (a ∷ qs) p kg ko kbs kl qc kas kp =
  mark cq c (ix 0) (ix-mark 0) qc , kg , ko , (kg a (c ++ [ ix 1 ]) (mark cq c (ix 1) (ix-mark 1) qc) , keyedᴸ-++ bs as kbs kas) , kp , kl
lane-keyed cq op g nothing  []       l (U.endˢ c) []       [] p kg ko kbs kl qc kas kp = qc
lane-keyed cq op g nothing  []       l (U.endˢ c) (x ∷ as) [] p kg ko kbs kl qc kas kp = qc , kg , ko , kas , kp , kl
lane-keyed cq op g nothing  (b ∷ bs) l (U.endˢ c) as       [] p kg ko kbs kl qc kas kp = qc , kg , ko , keyedᴸ-++ (b ∷ bs) as kbs kas , kp , kl
lane-keyed cq op g (just o) bs       l (U.endˢ c) as       [] p kg ko kbs kl qc kas kp = qc , kg , ko , keyedᴸ-++ bs as kbs kas , kp , kl
lane-keyed cq op g o bs l U.hushˢ as qs p kg ko kbs kl _ kas kp = tt

race-keyed : ∀ {Q} → Closed Q → ∀ {Γ A B} op (g : A → Pos → U.Node Γ B) (o : U.Node Γ A) (so : U.Step Γ A) mk k bs (l : U.Node Γ B) (s : U.Step Γ B) as qs p
           → (∀ a q → Q q → Keyed Q (g a q)) → Keyed Q o → KeyedStep Q so → Keyedᴸ Q bs → Keyed Q l → KeyedStep Q s → Keyedᴸ Q as → Keyed Q p
           → KeyedStep Q (U.raceˢ op g o so mk k bs l s as qs p)
race-keyed cq op g o so nothing   k bs l s as qs p kg ko kso kbs kl ks kas kp = lane-keyed cq op g (just o) bs l s as qs p kg ko kbs kl ks kas kp
race-keyed cq op g o so (just k′) k bs l s as qs p kg ko kso kbs kl ks kas kp with k′ <ᵖ k
... | true  = outer-keyed cq op g o so (bs ++ l ∷ as) qs p kg ko kso (keyedᴸ-++ bs (l ∷ as) kbs (kl , kas)) kp
... | false = lane-keyed cq op g (just o) bs l s as qs p kg ko kbs kl ks kas kp

go-keyed : ∀ {Q} → Closed Q → ∀ {Γ A B} op (g : A → Pos → U.Node Γ B) (o : U.Outer Γ A) ls qs p (e : U.Earliest Γ B)
         → (∀ a q → Q q → Keyed Q (g a q)) → KeyedOuter Q o → Keyedᴸ Q ls → Keyed Q p → KeyedEarliest Q e
         → KeyedStep Q (U.goˢ op g o ls qs p e)
go-keyed cq op g U.doneᵒ       ls qs p U.none                kg _          kl kp _ = tt
go-keyed cq op g (U.runᵒ o so) ls qs p U.none                kg (ko , kso) kl kp _ = outer-keyed cq op g o so ls qs p kg ko kso kl kp
go-keyed cq op g U.doneᵒ       ls qs p (U.found k bs l s as) kg _          kl kp (kbs , kl′ , ks , kas) =
  lane-keyed cq op g nothing bs l s as qs p kg tt kbs kl′ ks kas kp
go-keyed cq op g (U.runᵒ o so) ls qs p (U.found k bs l s as) kg (ko , kso) kl kp (kbs , kl′ , ks , kas) =
  race-keyed cq op g o so (U.headˢ so) k bs l s as qs p kg ko kso kbs kl′ ks kas kp

flat-keyed : ∀ {Q} → Closed Q → ∀ {Γ A B} op (g : A → Pos → U.Node Γ B) (o : U.Outer Γ A) ls qs p (sp : U.Step Γ B) (e : U.Earliest Γ B)
           → (∀ a q → Q q → Keyed Q (g a q)) → KeyedOuter Q o → Keyedᴸ Q ls → Keyed Q p → KeyedStep Q sp → KeyedEarliest Q e
           → KeyedStep Q (U.flatˢ op g o ls qs p sp e)
flat-keyed cq op g o ls qs p (U.skipˢ k p′) e kg ko kl kp (qk , kp′) ke with U.aheadˢ k o e
... | true  = qk , kg , nodeᵒ-keyed o ko , kl , kp′
... | false = go-keyed cq op g o ls qs p e kg ko kl kp ke
flat-keyed cq op g o ls qs p (U.outˢ k b p′) e kg ko kl kp _ ke = go-keyed cq op g o ls qs p e kg ko kl kp ke
flat-keyed cq op g o ls qs p (U.endˢ k)      e kg ko kl kp _ ke = go-keyed cq op g o ls qs p e kg ko kl kp ke
flat-keyed cq op g o ls qs p U.hushˢ         e kg ko kl kp _ ke = go-keyed cq op g o ls qs p e kg ko kl kp ke

-- A keyed node steps where `Q` holds, leaving a keyed node; and so does
-- what it leaves running.
mutual
  step-keyed : ∀ {Q} → Closed Q → ∀ {Γ A} (c : U.Node Γ A) → Keyed Q c → KeyedStep Q (U.step c)
  step-keyed cq (U.framesᶜ τ e m)           qe = frames-keyed cq τ e m qe
  step-keyed cq (U.burstᶜ τ r i b)          qr = burst-keyed cq τ r i b qr
  step-keyed cq (U.ofᶜ p i xs)              qp = of-keyed cq p i xs qp
  step-keyed cq (U.mapᶜ f c)                k  = map-keyed cq f (U.step c) (step-keyed cq c k)
  step-keyed cq (U.scanᶜ f z c)             k  = scan-keyed cq f z (U.step c) (step-keyed cq c k)
  step-keyed cq (U.takeWhileᶜ i f c)        k  = take-keyed cq i f (U.step c) (step-keyed cq c k)
  step-keyed cq (U.flatMapᶜ op g o ls qs p) (kg , ko , kl , kp) =
    flat-keyed cq op g (U.outerOf o) ls qs p (U.step p) (U.earliest ls) kg (outerOf-keyed cq o ko) kl kp (step-keyed cq p kp) (earliest-keyed cq ls kl)
  step-keyed cq (U.joinᶜ i p xs e)          (qp , kx , ke) = join-keyed cq i p xs e qp kx ke
  step-keyed cq (U.connectᶜ r b (U.live s)) (kb , ks) =
    source-keyed cq r b (U.step b) s (U.step s) kb (step-keyed cq b kb) ks (step-keyed cq s ks)
  step-keyed cq (U.connectᶜ r b (U.ended c t)) (kb , qc , kt) =
    ended-keyed cq r b (U.step b) c t (U.step t) kb (step-keyed cq b kb) qc kt (step-keyed cq t kt)
  step-keyed cq (U.deferᶜ l p ns)           (qp , kn) =
    mark cq p (ix 0) (ix-mark 0) qp , feeds-keyed cq ns (U.subscribe (Later.force l) (p ++ [ ix 1 ])) kn (keyed-sub cq (Later.force l) (p ++ [ ix 1 ]) (mark cq p (ix 1) (ix-mark 1) qp))
  step-keyed cq (U.endingᶜ p n)             (qp , _) = qp
  step-keyed cq (U.restᶜ n)                 k  = rest-keyed cq n k
  step-keyed cq U.idleᶜ                     k  = tt
  step-keyed cq (U.unionᶜ x y)              (kx , ky) = union-keyed cq x (U.restˢ x) y (U.restˢ y) kx (rest-keyed cq x kx) ky (rest-keyed cq y ky)
  step-keyed cq (U.burstingᶜ r t)           kt = bursts-keyed cq r t (U.step t) kt (step-keyed cq t kt)
  step-keyed cq (U.underᶜ {C = C} s b)      (ks , kb) = under-keyed cq s (U.restˢ {B = C} b) ks (rest-keyed cq b kb)

  outerOf-keyed : ∀ {Q} → Closed Q → ∀ {Γ A} (o : Maybe (U.Node Γ A)) → Keyedᴹ Q o → KeyedOuter Q (U.outerOf o)
  outerOf-keyed cq nothing  _  = tt
  outerOf-keyed cq (just o) ko = ko , step-keyed cq o ko

  earliest-keyed : ∀ {Q} → Closed Q → ∀ {Γ B} (ls : List (U.Node Γ B)) → Keyedᴸ Q ls → KeyedEarliest Q (U.earliest ls)
  earliest-keyed cq []       _          = tt
  earliest-keyed cq (l ∷ ls) (kl , kls) =
    pick-keyed cq l (U.step l) ls (U.headˢ (U.step l)) (U.earliest ls) kl (step-keyed cq l kl) kls (earliest-keyed cq ls kls)

  bursts-keyed : ∀ {Q} → Closed Q → ∀ {Γ A B} r (t : U.Node Γ A) (st : U.Step Γ A) → Keyed Q t → KeyedStep Q st
               → KeyedStep Q (U.burstsˢ {B = B} r t st)
  bursts-keyed cq r t (U.outˢ k a t′) kt (qk , kt′) with inside r k
  ... | true  = qk , kt′
  ... | false = rest-keyed cq t kt
  bursts-keyed cq r t (U.skipˢ k t′) kt (qk , kt′) with inside r k
  ... | true  = qk , kt′
  ... | false = rest-keyed cq t kt
  bursts-keyed cq r t (U.endˢ k) kt _ = rest-keyed cq t kt
  bursts-keyed cq r t U.hushˢ    kt _ = rest-keyed cq t kt

  rest-keyed : ∀ {Q} → Closed Q → ∀ {Γ A B} (n : U.Node Γ A) → Keyed Q n → KeyedStep Q (U.restˢ {B = B} n)
  rest-keyed cq (U.framesᶜ τ e m)    _ = tt
  rest-keyed cq (U.burstᶜ τ r i b)   _ = tt
  rest-keyed cq (U.ofᶜ p i xs)       _ = tt
  rest-keyed cq (U.mapᶜ f c)         k = rest-keyed cq c k
  rest-keyed cq (U.scanᶜ f z c)      k = rest-keyed cq c k
  rest-keyed cq (U.takeWhileᶜ i f c) k = rest-keyed cq c k
  rest-keyed cq (U.flatMapᶜ op g o ls qs p) (kg , ko , kl , kp) =
    union-keyed cq (U.outerᶜ o) (U.restᴹ o) (U.unionᶜ (U.restsᶜ ls) (U.restᶜ p)) (U.unionˢ (U.restsᶜ ls) (U.restsˢ ls) (U.restᶜ p) (U.restˢ p))
      (outerᶜ-keyed cq o ko) (restᴹ-keyed cq o ko) (restsᶜ-keyed cq ls kl , kp)
      (union-keyed cq (U.restsᶜ ls) (U.restsˢ ls) (U.restᶜ p) (U.restˢ p) (restsᶜ-keyed cq ls kl) (restsˢ-keyed cq ls kl) kp (rest-keyed cq p kp))
  rest-keyed cq (U.joinᶜ i p xs e)   _ = tt
  rest-keyed cq (U.connectᶜ {B = C} r b (U.live s)) (kb , ks) =
    union-keyed cq (U.burstingᶜ r s) (U.burstsˢ r s (U.step s)) (U.underᶜ (U.live s) b) (U.underˢ (U.live s) (U.restˢ {B = C} b))
      ks (bursts-keyed cq r s (U.step s) ks (step-keyed cq s ks)) (ks , kb) (under-keyed cq (U.live s) (U.restˢ {B = C} b) ks (rest-keyed cq b kb))
  rest-keyed cq (U.connectᶜ {B = C} r b (U.ended c t)) (kb , qc , kt) =
    union-keyed cq (U.burstingᶜ r t) (U.burstsˢ r t (U.step t)) (U.underᶜ (U.ended c t) b) (U.underˢ (U.ended c t) (U.restˢ {B = C} b))
      kt (bursts-keyed cq r t (U.step t) kt (step-keyed cq t kt)) ((qc , kt) , kb) (under-keyed cq (U.ended c t) (U.restˢ {B = C} b) (qc , kt) (rest-keyed cq b kb))
  rest-keyed cq (U.deferᶜ l p ns)    _ = tt
  rest-keyed cq (U.endingᶜ p n)      (_ , kn) = rest-keyed cq n kn
  rest-keyed cq (U.restᶜ n)          k = rest-keyed cq n k
  rest-keyed cq U.idleᶜ              _ = tt
  rest-keyed cq (U.unionᶜ x y)       (kx , ky) =
    union-keyed cq (U.restᶜ x) (U.restˢ x) (U.restᶜ y) (U.restˢ y) kx (rest-keyed cq x kx) ky (rest-keyed cq y ky)
  rest-keyed cq (U.burstingᶜ r t)    kt = bursts-keyed cq r t (U.step t) kt (step-keyed cq t kt)
  rest-keyed cq (U.underᶜ {C = C} s b) (ks , kb) = under-keyed cq s (U.restˢ {B = C} b) ks (rest-keyed cq b kb)

  restᴹ-keyed : ∀ {Q} → Closed Q → ∀ {Γ A B} (o : Maybe (U.Node Γ A)) → Keyedᴹ Q o → KeyedStep Q (U.restᴹ {B = B} o)
  restᴹ-keyed cq nothing  _  = tt
  restᴹ-keyed cq (just o) ko = rest-keyed cq o ko

  restsˢ-keyed : ∀ {Q} → Closed Q → ∀ {Γ A B} (ls : List (U.Node Γ A)) → Keyedᴸ Q ls → KeyedStep Q (U.restsˢ {B = B} ls)
  restsˢ-keyed cq []       _          = tt
  restsˢ-keyed cq (l ∷ ls) (kl , kls) =
    union-keyed cq (U.restᶜ l) (U.restˢ l) (U.restsᶜ ls) (U.restsˢ ls) kl (rest-keyed cq l kl) (restsᶜ-keyed cq ls kls) (restsˢ-keyed cq ls kls)

-- Owned by `P`: whatever a joiner owned by it is fed is too.
owned-fit : ∀ P q → Fit (Owned P) q
owned-fit P q j o = inj₂ (owned-tagged P j (q ++ [ sub j ]) o (tagged-sub q j))

owned-closed : ∀ P → Closed (Owned P)
mark  (owned-closed P) k l _ o = owned-trans P k (k ++ [ l ]) o (inj₁ (prefix-++ k [ l ]))
frame (owned-closed P) t r o   = inj₂ (inj₁ o)
tag   (owned-closed P) q j _   = owned-fit P q j

-- A first child of a position a tick heads is no prefix of a frame.
frame-prefix : ∀ p → Headed p → ∀ t r → ¬ Prefix (p ++ [ ix 0 ]) (ix t ∷ sub r ∷ [])
frame-prefix (ix _ ∷ [])        _ t r (_ , () , _)
frame-prefix (ix _ ∷ _ ∷ [])    _ t r (_ , _ , ())
frame-prefix (ix _ ∷ _ ∷ _ ∷ _) _ t r (_ , _ , ())

-- A frame tagged with what lies apart from a first child lies apart from
-- it too.
frame-apart : ∀ p → Headed p → ∀ t r → Disjoint (p ++ [ ix 0 ]) r → Disjoint (p ++ [ ix 0 ]) (ix t ∷ sub r ∷ [])
frame-apart p hp t r d =
    (λ { (inj₁ q) → frame-prefix p hp t r q ; (inj₂ (inj₁ o)) → proj₁ d o ; (inj₂ (inj₂ ())) })
  , (λ o → proj₂ d (owned-trans r (ix t ∷ sub r ∷ []) (p ++ [ ix 0 ]) (inj₂ (inj₁ (inj₁ (prefix-refl r)))) o))

-- Apart from the first child of a position a tick heads.
apart-closed : ∀ p → Headed p → Closed (Disjoint (p ++ [ ix 0 ]))
mark  (apart-closed p hp)           = apart-mark (p ++ [ ix 0 ])
frame (apart-closed p hp)           = frame-apart p hp
tag   (apart-closed p hp) q j dq dj = apart-join (p ++ [ ix 0 ]) q j (proj₁ dq) dj

-- Under a region, apart from what lies apart from it and from just past
-- that.
sides-of : ∀ P k q → Owned P k → Disjoint P q → k ≢ q × k ≢ q ++ [ ix 0 ]
sides-of P k q o d = (λ { refl → proj₁ d o }) , (λ { refl → proj₁ (apart-mark P q (ix 0) (ix-mark 0) d) o })

-- Apart, the two step apart now.
apart-sides : ∀ {Γ A B} r (b : U.Node (A ∷ Γ) B) (s : U.Node Γ A) (ρ : NEnv Γ) → Apart r b s ρ → Sides (U.step b) (U.step s)
apart-sides r b s ρ (p , _ , hp , kb , ks , _) k q hk hq =
  sides-of (p ++ [ ix 0 ]) k q (keyed-head (Owned (p ++ [ ix 0 ])) (U.step b) (step-keyed (owned-closed (p ++ [ ix 0 ])) b kb) k hk)
                               (keyed-head (Disjoint (p ++ [ ix 0 ])) (U.step s) (step-keyed (apart-closed p hp) s ks) q hq)

-- Within the start of a cold observable is trivially satisfied.
start-within : ∀ {Γ A} p (m : From A 0) (ρ : NEnv Γ) → Within (U.startᶜ {Γ} p m) ρ
start-within p (M.at zero _ _)    ρ = tt
start-within p (M.at (suc _) _ _) ρ = tt
start-within p M.done             ρ = tt
start-within p M.quiet            ρ = tt

-- A sibling of a headed position is also headed.
headed-lane : ∀ x → Headed (x ++ [ ix 0 ]) → Headed (x ++ [ ix 1 ])
headed-lane []          _ = tt
headed-lane (ix _ ∷ _)  _ = tt
headed-lane (sub _ ∷ _) ()
headed-lane (last ∷ _)  ()

-- A subscribe is apart: the body is owned and the source is disjoint.
apart-sub : ∀ {Γ A B} (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) p (ρ : NEnv Γ) → Headed p → Alienᴱ p ρ
          → Apart (p ++ [ ix 1 ]) (U.subscribe b (p ++ [ ix 0 ])) (U.subscribe s (p ++ [ ix 1 ])) ρ
apart-sub s b p ρ hp al =
    p , refl , hp
  , keyed-sub (owned-closed (p ++ [ ix 0 ])) b (p ++ [ ix 0 ]) (inj₁ (prefix-refl (p ++ [ ix 0 ])))
  , keyed-sub (apart-closed p hp) s (p ++ [ ix 1 ]) (sibling p (ix-mark 1) (λ ()) , sibling p (ix-mark 0) (λ ()))
  , every-monoᴱ (λ h n o → n (owned-trans p (p ++ [ ix 0 ]) h (inj₁ (prefix-++ p [ ix 0 ])) o)) ρ al


ApartNext : ∀ {Γ A B} → Pos → U.Step (A ∷ Γ) B → U.Node Γ A → NEnv Γ → Set
ApartNext r (U.outˢ k a b′) s ρ = Apart r b′ s ρ
ApartNext r (U.skipˢ k b′)  s ρ = Apart r b′ s ρ
ApartNext r (U.endˢ k)      s ρ = ⊤
ApartNext r U.hushˢ         s ρ = ⊤

apart-next : ∀ {Γ A B} r (b : U.Node (A ∷ Γ) B) (s : U.Node Γ A) (ρ : NEnv Γ) → Apart r b s ρ → ApartNext r (U.step b) s ρ
apart-next r b s ρ (p , er , hp , kb , ks , al) with U.step b | step-keyed (owned-closed (p ++ [ ix 0 ])) b kb
... | U.outˢ k a b′ | _ , kb′ = p , er , hp , kb′ , ks , al
... | U.skipˢ k b′  | _ , kb′ = p , er , hp , kb′ , ks , al
... | U.endˢ k      | _       = tt
... | U.hushˢ       | _       = tt

ApartFed : ∀ {Γ A B} → Pos → U.Node (A ∷ Γ) B → U.Step Γ A → NEnv Γ → Set
ApartFed r b (U.outˢ q a s′) ρ = Apart r (U.feed (here refl) q (just a) b) s′ ρ
ApartFed r b (U.skipˢ q s′)  ρ = Apart r (U.feed (here refl) q nothing b) s′ ρ
ApartFed r b (U.endˢ c)      ρ = ⊤
ApartFed r b U.hushˢ         ρ = ⊤

apart-fed : ∀ {Γ A B} r (b : U.Node (A ∷ Γ) B) (s : U.Node Γ A) (ρ : NEnv Γ) → Apart r b s ρ → ApartFed r b (U.step s) ρ
apart-fed r b s ρ (p , er , hp , kb , ks , al) with U.step s | step-keyed (apart-closed p hp) s ks
... | U.outˢ q a s′ | _ , ks′ =
  p , er , hp , feed-keyed (owned-closed (p ++ [ ix 0 ])) (here refl) q (just a) b (owned-fit (p ++ [ ix 0 ]) q) kb , ks′ , al
... | U.skipˢ q s′  | _ , ks′ =
  p , er , hp , feed-keyed (owned-closed (p ++ [ ix 0 ])) (here refl) q nothing b (owned-fit (p ++ [ ix 0 ]) q) kb , ks′ , al
... | U.endˢ c      | _       = tt
... | U.hushˢ       | _       = tt
