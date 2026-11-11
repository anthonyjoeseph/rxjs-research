{-# OPTIONS --guardedness #-}

-- A BODY KEEPS ITS HANDLE'S SILENCE (`Hushes`): subscribed under no
-- silent hot row, a reading shows nothing loud under one.  Causality does
-- not say so: a body showing each skip of its handle as a value reads
-- causally and keeps the invariant, yet under its source's cut it spins
-- loud.  Every program's body hushes, by structure (`hush-at`): a row
-- lies under a hot row only where a joined hot shows it, or below an
-- outer row that does.
module denotation.Laws.Hush where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (_∷_; lookup)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; Later; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ; cold; empty; of; map; scan; takeWhile; flatMap; connect;
  connected; defer)
open import denotation.Position using (Pos; ix; _⊕_)
open import denotation.Events using (Timeline)
open import denotation.EmissionSet using (Ev; out; end; Silent; hush; held; EmissionSet; Den; hot; enter; Rejoin; shown; heard;
  ended; late; Proper; LaneOf; Ended; map-out; map-skip; map-pin; map-end; guard; body; DenEnv; approx; module Scan; module TakeWhile;
  module Joining; module Switch; module Exhaust; module Bounded; module Connect; module Op)
open import denotation.Laws.Worlds using (W; W⁼; step; timer; join; here; inW; plain-ix; plain-last; Plain; Ok; Lawful; InvAt; InvD;
  Hots; GoodEnv; _∪ʰ_; _⊑_; ⊑-refl; ⊑-snoc; ⊑-inside; ⊕-identityʳ; ⊕-injʳ; ok-step; ok-in;
  real-snoc; widen; sib; l-root; l-in; l-hot; lead)
open import denotation.Laws.Worlds.Leaves using (empty-inv; of-inv; spin-inv)
open import denotation.Laws.ColdInv using (cold-inv)
open import denotation.Laws.BoundedInv using (module BoundedI)
open import denotation.Laws.Nth using (module Nths)
import denotation.Laws.Connect as LC
open import denotation.Laws using (inv-approx; good-cons)

-- A hot's silent rows.
Quiet : ∀ {A} → EmissionSet A → Pos → Set
Quiet {A} t h = Σ (Ev A) λ e → t h e × Silent e

-- HUSHED by `S`: subscribed under no row of `S`, a reading shows nothing
-- loud under one.
Hush : ∀ {A} → (Pos → Set) → (Pos → Set) → Den A → Set
Hush H S d = ∀ p → Ok H p → (∀ {h} → S h → ¬ h ⊑ p) → ∀ {y e h} → enter d p y e → S h → h ⊑ y → Silent e

-- A body hushed by each lawful handle's silence, the handle leading no
-- row of `H`.
Hushes : ∀ {A B} → (Pos → Set) → (Den A → Den B) → Set₁
Hushes {A} H F = ∀ {t : EmissionSet A} → Lawful t → (∀ {h e q} → t h e → H q → ¬ h ⊑ q) → Hush (H ∪ʰ t) (Quiet t) (F (hot t))

private
  out-loud : ∀ {A} {a : A} → Silent (out a) → ⊥
  out-loud ()

  end-loud : ∀ {A} → Silent {A} end → ⊥
  end-loud ()

  -- No row of `S` is a world position.
  free-w : ∀ {H p x} → Ok H p → W H p x → H x → ⊥
  free-w {x = x} (_ , dj) w hx = dj hx w (⊑-inside (⊑-refl x))

  -- One plain label below a world position, or the subscription, led by
  -- no row of `S`: led by none.
  free-kid : ∀ {H p x l h} → Ok H p → W⁼ H p x → Plain l → H h → ¬ h ⊑ x → ¬ h ⊑ (x ⊕ [ l ])
  free-kid {x = x} ok w pl hh fr le with ⊑-snoc x le
  ... | inj₁ hx   = fr hx
  ... | inj₂ refl = free-w ok (step w pl) hh

  mutual
    mono : ∀ {H p w} → W (λ _ → ⊥) p w → W H p w
    mono (step w l)              = step (mono⁼ w) l
    mono (timer i w lt pl)       = timer i (mono⁼ w) lt pl
    mono (join (inj₁ ()) _ _)
    mono (join (inj₂ v) w eh)    = join (inj₂ (mono v)) (mono⁼ w) eh

    mono⁼ : ∀ {H p w} → W⁼ (λ _ → ⊥) p w → W⁼ H p w
    mono⁼ here    = here
    mono⁼ (inW w) = inW (mono w)

-- A LEAF HUSHES: it joins no hot, so a row of `S` leading one of its rows
-- would lie in its world.
leaf-hush : ∀ {A H S} {d : Den A} → (∀ {H′} → InvD H′ d) → (∀ {h} → S h → H h) → Hush H S d
leaf-hush inv sh p ok fr x s le with lead (inW (InvAt.world (inv {λ _ → ⊥} p (proj₁ ok , λ ())) x)) le
... | l-root r = ⊥-elim (fr s r)
... | l-in v   = ⊥-elim (free-w ok (mono v) (sh s))
... | l-hot () _

-- A JOINED HOT hushes where its own rows do.
hot-hush : ∀ {A H S} {t : EmissionSet A} → (∀ {h} → S h → H h) → (∀ {q e} → t q e → H q)
         → (∀ {q e h} → t q e → S h → h ⊑ q → Silent e) → Hush H S (hot t)
hot-hush {H = H} {S} {t} sh th tq p ok fr {h = h} (x , _) s = go x
  where
    go : ∀ {y e} → Rejoin p t y e → h ⊑ y → Silent e
    go (shown {q} y _ pq) le with ⊑-snoc q le
    ... | inj₁ hq   = tq y s hq
    ... | inj₂ refl = ⊥-elim (free-w ok (join (inj₁ (th y)) here pq) (sh s))
    go (heard _ _) _ = hush
    go (ended {c} y pc) le with ⊑-snoc c le
    ... | inj₁ hc   = ⊥-elim (end-loud (tq y s hc))
    ... | inj₂ refl = ⊥-elim (free-w ok (join (inj₁ (th y)) here pc) (sh s))
    go (late _ _) le with ⊑-snoc p le
    ... | inj₁ hp   = ⊥-elim (fr s hp)
    ... | inj₂ refl = ⊥-elim (free-w ok (step here plain-last) (sh s))

-- A LAWFUL HOT's rows under its own silent rows are those rows.
own-quiet : ∀ {A} {t : EmissionSet A} → Lawful t → ∀ {q e h} → t q e → Quiet t h → h ⊑ q → Silent e
own-quiet {t = t} L {e = e} {h} x (e₀ , th , sl) ([] , refl) =
  subst Silent (Lawful.func L th (subst (λ z → t z e) (⊕-identityʳ h) x)) sl
own-quiet L x (_ , th , _) ((_ ∷ _) , refl) = ⊥-elim (Lawful.flat L th x)

-- A READING KEEPS A FRESH HOT'S SILENCE where the hot leads no row of
-- `H`: no row of the hot leads a row of the reading.
fresh-hush : ∀ {A B H} {d : Den A} {t : EmissionSet B} → InvD H d → (∀ {h e q} → t h e → H q → ¬ h ⊑ q) → Hush (H ∪ʰ t) (Quiet t) d
fresh-hush {H = H} {t = t} inv ap p (r , dj) fr {h = h} x (e₀ , th , sl) le
  with lead (inW (InvAt.world (inv p (r , λ hh w ins → dj (inj₂ hh) (widen t w) ins)) x)) le
... | l-root rt   = ⊥-elim (fr (e₀ , th , sl) rt)
... | l-in v      = ⊥-elim (dj (inj₁ (e₀ , th)) (widen t v) (⊑-inside (⊑-refl h)))
... | l-hot hq hl = ⊥-elim (ap th hq hl)

-- Hushed by `S`, hushed by `S` and a fresh hot's silence.
widen-hush : ∀ {A B H S} {d : Den A} {t : EmissionSet B} → InvD H d → (∀ {h e q} → t h e → H q → ¬ h ⊑ q)
           → Hush H S d → Hush (H ∪ʰ t) (λ h → S h ⊎ Quiet t h) d
widen-hush {t = t} inv ap hs p (r , dj) fr x (inj₁ s) le =
  hs p (r , λ hh w ins → dj (inj₂ hh) (widen t w) ins) (λ s′ → fr (inj₁ s′)) x s le
widen-hush {d = d} inv ap hs p ok fr x (inj₂ q) le = fresh-hush {d = d} inv ap p ok (λ q′ → fr (inj₂ q′)) x q le

------------------------------------------------------------------------
-- One input

map-hush : ∀ {A B H S} (f : A → B) {s : Den A} → Hush H S s → Hush H S (Op.map f s)
map-hush f hs p ok fr (map-out y , _)  sx le = ⊥-elim (out-loud (hs p ok fr y sx le))
map-hush f hs p ok fr (map-skip _ , _) _  _  = hush
map-hush f hs p ok fr (map-pin _ , _)  _  _  = held
map-hush f hs p ok fr (map-end y , _)  sx le = ⊥-elim (end-loud (hs p ok fr y sx le))

scan-hush : ∀ {A B H S} (f : B → A → B) z {s : Den A} → Hush H S s → Hush H S (Op.scan f z s)
scan-hush f z {s} hs p ok fr {h = h} (x , _) sx = go x
  where
    go : ∀ {y e} → Scan.ScanT f z (enter s p) y e → h ⊑ y → Silent e
    go (Scan.sval (Scan.acc₀ y _))     le = ⊥-elim (out-loud (hs p ok fr y sx le))
    go (Scan.sval (Scan.acc _ y _ _))  le = ⊥-elim (out-loud (hs p ok fr y sx le))
    go (Scan.sstep _)                  _  = hush
    go (Scan.spin _)                   _  = held
    go (Scan.send y)                   le = ⊥-elim (end-loud (hs p ok fr y sx le))

take-hush : ∀ {A H S} i k {s : Den A} → (∀ {h} → S h → H h) → InvD H s → Hush H S s → Hush H S (Op.takeWhile i k s)
take-hush i k {s} sh Is hs p ok fr {h = h} (x , _) sx = go x
  where
    kid : ∀ {q a l} → enter s p q (out a) → Plain l → h ⊑ (q ⊕ [ l ]) → ⊥
    kid y pl = free-kid ok (inW (InvAt.world (Is p ok) y)) pl (sh sx) (λ le → out-loud (hs p ok fr y sx le))

    go : ∀ {y e} → TakeWhile.TakeT i k (enter s p) y e → h ⊑ y → Silent e
    go (TakeWhile.pass y _ _)   le = ⊥-elim (out-loud (hs p ok fr y sx le))
    go (TakeWhile.fail y _ _ _) le = ⊥-elim (kid y plain-ix le)
    go (TakeWhile.stop y _ _)   le = ⊥-elim (kid y plain-last le)
    go (TakeWhile.step _ _)     _  = hush
    go (TakeWhile.tend y _)     le = ⊥-elim (end-loud (hs p ok fr y sx le))
    go (TakeWhile.left _ _ _)   _  = held

defer-hush : ∀ {A H S} {s : Den A} → (∀ {h} → S h → H h) → Hush H S s → Hush H S (Op.defer s)
defer-hush sh hs p ok fr (guard , _)  _  _  = hush
defer-hush sh hs p ok fr (body x , _) sx le = hs (p ⊕ [ ix 1 ]) (ok-step p ok) (λ s′ → free-kid ok here plain-ix (sh s′) (fr s′)) x sx le

------------------------------------------------------------------------
-- Joiners

-- A JOINER hushes where its outer and its lanes do.
module JoinHush {A B : Set} (Lane : Pos → A → EmissionSet B) (o : EmissionSet A) (Over Runs : Pos → Set)
                (Cut : Pos → Pos → Set) (Hand : Pos → Set) {h : Pos}
                (oh : ∀ {q e} → o q e → h ⊑ q → Silent e)
                (lh : ∀ {q a k e} → o q (out a) → Runs q → Lane q a k e → h ⊑ k → Silent e) where
  open Joining Lane o (λ _ _ → ⊥) Over Runs Cut Hand

  jh : ∀ {y e} → JoinT y e → h ⊑ y → Silent e
  jh (val _)                _  = hush
  jh (step _)               _  = hush
  jh (opin _)               _  = held
  jh (oend x _)             le = ⊥-elim (end-loud (oh x le))
  jh (opass _ _)            _  = hush
  jh (lane x r l _ _)       le = lh x r l le
  jh (lend x r l _ _ _)     le = ⊥-elim (end-loud (lh x r l le))
  jh (lpass _ _ _ _ _ _)    _  = hush
  jh (hand _ _ _ _ _)       _  = hush
  jh (left _ _ _ _ _)       _  = held
  jh (run () _)
  jh (rend () _ _)
  jh (rpass () _ _)
  jh (rhand () _)

flat-hush : ∀ {A B H S} (op : FlatOp) {f : A → Den B} {s : Den A} → (∀ {h} → S h → H h) → InvD H s → (∀ a → InvD H (f a))
          → Hush H S s → (∀ a → Hush H S (f a)) → Hush H S (Op.flatMap op f s)
flat-hush {A} {B} {H} {S} op {f} {s} sh Is If hs hf p ok fr {h = h} x sx = by op x
  where
    o : EmissionSet A
    o = enter s p

    Io : InvAt H p o
    Io = Is p ok

    oh : ∀ {q e} → o q e → h ⊑ q → Silent e
    oh y = hs p ok fr y sx

    -- Below an outer value, led by no row of `S`.
    kid : ∀ {q a} → o q (out a) → ∀ {h′} → S h′ → ¬ h′ ⊑ (q ⊕ [ ix 1 ])
    kid y s′ = free-kid ok (inW (InvAt.world Io y)) plain-ix (sh s′) (λ le → out-loud (hs p ok fr y s′ le))

    lane-h : ∀ {q a k e} → o q (out a) → LaneOf f q a k e → h ⊑ k → Silent e
    lane-h {q} {a} y (l , _) =
      hf a (q ⊕ [ ix 1 ]) (ok-in ok (step (inW (InvAt.world Io y)) plain-ix) (real-snoc q plain-ix (InvAt.real Io y))) (kid y) l sx

    module BI (n : ℕ) = BoundedI ok n f If Io
    open Nths o using (nth-val)

    -- A bounded lane's subscription, led by no row of `S`: a value's
    -- second child, or an earlier lane's end's.
    bfree : ∀ n {i q s′ a} → Acc _<_ i → Bounded.Sub n f o i q s′ a → ∀ {h′} → S h′ → ¬ h′ ⊑ s′
    bfree n _ (nq , Bounded.room _)    = kid (nth-val nq)
    bfree n _ (nq , Bounded.freed _ _) = kid (nth-val nq)
    bfree n {i} (acc rs) sb@(nq , Bounded.queued {c} _ _ kc _ _) {h′} s′ le with BI.kth-lane n i kc
    ... | BI.ending j<i (_ , a′ , s₀ , nj , stj , ac) refl with ⊑-snoc c le
    ...   | inj₁ hc   = end-loud (hf a′ s₀ (BI.okS n (nj , stj)) (bfree n (rs j<i) (nj , stj)) (proj₁ ac) s′ hc)
    ...   | inj₂ refl = free-w ok (BI.s-w n sb) (sh s′)

    bnd-h : ∀ n {q a k e} → Bounded.Lane n f o q a k e → h ⊑ k → Silent e
    bnd-h n {a = a} (i , s′ , sb , (l , _)) = hf a s′ (BI.okS n sb) (bfree n (<-wellFounded i) sb) l sx

    by : (op : FlatOp) → ∀ {y e} → enter (Op.flatMap op f s) p y e → h ⊑ y → Silent e
    by (mergeᶠ nothing)  (j , _) =
      JoinHush.jh (LaneOf f) o (Ended o) (λ _ → ⊤) (λ _ _ → ⊥) (λ _ → ⊥) oh (λ y _ l → lane-h y l) j
    by (mergeᶠ (just n)) (j , _) =
      JoinHush.jh (Bounded.Lane n f o) o (Ended o) (Bounded.Indexed n f o) (λ _ _ → ⊥) (Bounded.Queued n f o) oh (λ _ _ l → bnd-h n l) j
    by switchᶠ           (j , _) =
      JoinHush.jh (LaneOf f) o (Ended o) (λ _ → ⊤) (Switch.Cut f o) (λ _ → ⊥) oh (λ y _ l → lane-h y l) j
    by exhaustᶠ          (j , _) =
      JoinHush.jh (LaneOf f) o (Ended o) (Exhaust.Run f o) (λ _ _ → ⊥) (λ _ → ⊥) oh (λ y _ l → lane-h y l) j

------------------------------------------------------------------------
-- A connect

-- A CONNECT hushes where its source and its body do, the body read over
-- the source's silence too.  What the source shows is silent.
connect-hush : ∀ {Γ A B} {ρ : DenEnv Γ} {S : Pos → Set} {s : Den A} {F : Den A → Den B}
             → (∀ {h} → S h → Hots ρ h) → (∀ {C} (i : C ∈ Γ) → Hush (Hots ρ) S (lookup ρ i)) → GoodEnv ρ
             → InvD (Hots ρ) s → (∀ {t} → Lawful t → InvD (Hots ρ ∪ʰ t) (F (hot t))) → Hush (Hots ρ) S s
             → (∀ {t} {S′ : Pos → Set} → Lawful t → (∀ {h} → S′ h → (Hots ρ ∪ʰ t) h)
                → (∀ {C} (i : C ∈ A ∷ Γ) → Hush (Hots ρ ∪ʰ t) S′ (lookup (hot t ∷ ρ) i)) → Hush (Hots ρ ∪ʰ t) S′ (F (hot t)))
             → Hush (Hots ρ) S (Op.connect s F)
connect-hush {Γ} {A} {B} {ρ} {S} {s} {F} sh env g Is IF hs hb p ok fr {h = h} (x , _) sx = go x
  where
    H : Pos → Set
    H = Hots ρ

    r : Pos
    r = p ⊕ [ ix 1 ]

    σ′ : EmissionSet A
    σ′ = Proper (enter s r)

    S′ : Pos → Set
    S′ h′ = S h′ ⊎ Quiet σ′ h′

    L : Lawful σ′
    L = LC.lawful {A} {B} {H} {s} {F} Is IF p ok

    sh′ : ∀ {h′} → S′ h′ → (H ∪ʰ σ′) h′
    sh′ (inj₁ s′)          = inj₂ (sh s′)
    sh′ (inj₂ (e , y , _)) = inj₁ (e , y)

    -- No row of the source leads a hot row: it would lie in the source's world.
    ap : ∀ {h′ e q} → σ′ h′ e → H q → ¬ h′ ⊑ q
    ap y hq le = proj₂ (ok-step p ok) hq (InvAt.world (LC.Iσ {A} {B} {H} {s} {F} Is IF p ok) (proj₁ y)) (⊑-inside le)

    σ-h : ∀ {q e h′} → σ′ q e → S′ h′ → h′ ⊑ q → Silent e
    σ-h y (inj₁ s′) le = hs r (ok-step p ok) (λ s″ → free-kid ok here plain-ix (sh s″) (fr s″)) (proj₁ y) s′ le
    σ-h y (inj₂ qt) le = own-quiet L y qt le

    env′ : ∀ {C} (i : C ∈ A ∷ Γ) → Hush (H ∪ʰ σ′) S′ (lookup (hot σ′ ∷ ρ) i)
    env′ (here refl) = hot-hush sh′ (λ y → inj₁ (_ , y)) σ-h
    env′ (there i)   = widen-hush {d = lookup ρ i} (proj₁ (g i)) ap (env i)

    -- The body's subscription, led by no row of `S` nor of the source.
    fr₀ : ∀ {h′} → S′ h′ → ¬ h′ ⊑ (p ⊕ [ ix 0 ])
    fr₀ (inj₁ s′)              = free-kid ok here plain-ix (sh s′) (fr s′)
    fr₀ (inj₂ (_ , (y , _) , _)) = sib (proj₁ ok) plain-ix (⊑-refl p) (λ e → ix≢ (⊕-injʳ p p e)) (LC.sw {A} {B} {H} {s} {F} Is IF p ok y)
      where
        ix≢ : ix 0 ≡ ix 1 → ⊥
        ix≢ ()

    go : ∀ {y e} → Connect.ConnT s F p y e → h ⊑ y → Silent e
    go (Connect.body y)         le = hb L sh′ env′ (p ⊕ [ ix 0 ]) (LC.ok₀ {A} {B} {H} {s} {F} Is IF p ok) fr₀ y (inj₁ sx) le
    go (Connect.burst _ _)      _  = held
    go (Connect.echo _ _ _ _)   _  = hush
    go (Connect.kept _ _ _ _)   _  = held

------------------------------------------------------------------------
-- By structure

-- EVERY APPROXIMANT HUSHES by the silence of rows its environment hushes by.
hush-approx : ∀ {Γ A} n (o : Obs Timeline Γ A) (ρ : DenEnv Γ) {S : Pos → Set} → GoodEnv ρ → (∀ {h} → S h → Hots ρ h)
            → (∀ {C} (i : C ∈ Γ) → Hush (Hots ρ) S (lookup ρ i)) → Hush (Hots ρ) S (approx n o ρ)
hush-approx n       (cold c)          ρ g sh e = leaf-hush {d = Op.cold c} (λ {H′} → cold-inv {H = H′} c) sh
hush-approx n       empty             ρ g sh e = leaf-hush {d = Op.empty} (λ {H′} → empty-inv {H = H′}) sh
hush-approx n       (of xs)           ρ g sh e = leaf-hush {d = Op.of xs} (λ {H′} → of-inv {H = H′} xs) sh
hush-approx n       (map f s)         ρ g sh e = map-hush f {s = approx n s ρ} (hush-approx n s ρ g sh e)
hush-approx n       (scan f z s)      ρ g sh e = scan-hush f z {s = approx n s ρ} (hush-approx n s ρ g sh e)
hush-approx n       (takeWhile i k s) ρ g sh e = take-hush i k {s = approx n s ρ} sh (inv-approx n s ρ g) (hush-approx n s ρ g sh e)
hush-approx n       (flatMap op f s)  ρ g sh e =
  flat-hush op {f = λ a → approx n (f a) ρ} {s = approx n s ρ} sh (inv-approx n s ρ g) (λ a → inv-approx n (f a) ρ g) (hush-approx n s ρ g sh e) (λ a → hush-approx n (f a) ρ g sh e)
hush-approx n       (connect s b)     ρ g sh e =
  connect-hush {ρ = ρ} {s = approx n s ρ} {F = λ h → approx n b (h ∷ ρ)} sh e g (inv-approx n s ρ g)
    (λ {t} L → inv-approx n b (hot t ∷ ρ) (good-cons L g)) (hush-approx n s ρ g sh e)
    (λ {t} L sh′ e′ → hush-approx n b (hot t ∷ ρ) (good-cons L g) sh′ e′)
hush-approx n       (connected i)     ρ g sh e = e i
hush-approx zero    (defer l)         ρ g sh e = leaf-hush {d = Op.⊥} (λ {H′} → spin-inv {H = H′}) sh
hush-approx (suc n) (defer l)         ρ g sh e = defer-hush {s = approx n (Later.force l) ρ} sh (hush-approx n (Later.force l) ρ g sh e)

-- AN APPROXIMANT'S BODY HUSHES by its handle's silence.
hush-at : ∀ {Γ A B} n (b : Obs Timeline (A ∷ Γ) B) (ρ : DenEnv Γ) → GoodEnv ρ → Hushes (Hots ρ) (λ h → approx n b (h ∷ ρ))
hush-at {Γ} {A} n b ρ g {t} L ap = hush-approx n b (hot t ∷ ρ) (good-cons L g) sh env
  where
    sh : ∀ {h} → Quiet t h → (Hots ρ ∪ʰ t) h
    sh (e , y , _) = inj₁ (e , y)

    env : ∀ {C} (i : C ∈ A ∷ Γ) → Hush (Hots ρ ∪ʰ t) (Quiet t) (lookup (hot t ∷ ρ) i)
    env (here refl) = hot-hush sh (λ y → inj₁ (_ , y)) (λ y q le → own-quiet L y q le)
    env (there i)   = fresh-hush {d = lookup ρ i} (proj₁ (g i)) ap
