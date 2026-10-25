{-# OPTIONS --guardedness #-}

-- A run with skips erased need not trail: `_⊒_` is checked a depth at a
-- time, and an erased step spends depth, so infinitely many erased
-- steps before the next kept one satisfy every depth while whatever
-- follows them is unconstrained.  So a connect fed one needs it to.
module adequacy.Refute-Trail where

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (refl)
open import denotation.MonotonicList.Events using (Events∞; Tail; Tail∞; Pos; ix; skip; out; end; hush; idle; pin)
open import adequacy.Engine.Erase using (_⊒_; Eraseˢ; _,ᵉ_; cutᵉ; Eraseᵀ; Erase; stopᵉ; idleᵉ; pinᵉ; unpin; skipᵉ; erased; skipᴸ; hushᴸ; eraseᵀ-agree)
open import adequacy.Engine.Meaning using (bodyConn)
open import adequacy.Engine.Beside using (Sourced; sourced)
open import denotation.MonotonicList using (agreeᵀ-refl)
open import adequacy.Placed.Order using (EveryT; everyᵀ; everyT-idle; Ext; Ordered; ordered)
open import adequacy.Placed.Trail using (Trailing; TrailE; trail; trailᶠ; trail-idle; SortedT; sortedᵀ; sortedT-idle; FlatT; flatᵀ; flatT-idle; shown; reshown)
open Events∞
open Tail∞
open EveryT
open SortedT
open FlatT

-- The left: `skip [0]` forever, leaving `[0]` pinned forever.
z one two : Pos
z   = ix 0 ∷ []
one = ix 1 ∷ []
two = ix 2 ∷ []

mutual
  zeros∞ : Tail∞
  later zeros∞ = zeros

  zeros : Tail
  zeros = pin z zeros∞

left : Events∞ ℕ
left .force = skip z left
left .cut   = zeros

-- The right: its first `skip [0]` kept, then `out [2]` leaving `[1]`
-- pinned, before it.
fin : Events∞ ℕ
fin .force = end two
fin .cut   = idle

pin-one : Tail
pin-one = pin one λ where .later → idle

after : Events∞ ℕ
after .force = out two 0 fin
after .cut   = pin-one

right : Events∞ ℕ
right .force = skip z after
right .cut   = idle

-- The left trails.
sorted : SortedT zeros
sorted .sortedᵀ = refl , sorted

marked : EveryT (TrailE (skip z left)) zeros
marked .everyᵀ = inj₁ refl , marked

flat : EveryT (λ h → ¬ Ext z h) zeros
flat .everyᵀ = (λ ()) , flat

flatT : FlatT zeros
flatT .flatᵀ = flat , flatT

trails : Trailing left
trails .trail  = sorted , marked , trails
trails .trailᶠ = flatT

-- And erases to the right at every depth.
gone₀ : ∀ n → Eraseᵀ n zeros idle
gone₀ zero    = stopᵉ
gone₀ (suc n) = unpin tt (gone₀ n)

gone₁ : ∀ n → Eraseᵀ n zeros pin-one
gone₁ zero    = stopᵉ
gone₁ (suc n) = unpin refl (gone₁ n)

erasing : ∀ n → Erase n (skip z left) pin-one (out two 0 fin)
erasing zero    = stopᵉ
erasing (suc n) = erased refl (gone₁ n) (erasing n)

erase : ∀ n → Eraseˢ n left right
erase zero    = stopᵉ ,ᵉ stopᵉ
erase (suc n) = gone₀ (suc n) ,ᵉ skipᵉ (gone₁ n) (erasing n)

-- The right does not trail: `[1]` is pinned before its `out [2]`.
erase-untrailed : (∀ {X} {σ σ′ : Events∞ X} → Trailing σ → σ ⊒ σ′ → Trailing σ′) → ⊥
erase-untrailed f with proj₁ (everyᵀ (proj₁ (proj₂ (trail (proj₂ (proj₂ (trail (f trails (skipᴸ , (λ ()) , erase)))))))))
... | () , _

------------------------------------------------------------------------
-- At a connect subscribed at `[0,0]`: a source `skip [0,0]`, then
-- `skip [0,0,0]` forever, each past the first leaving `[0]` pinned
-- (`[0]` marks `[0,0,0]`), erased past its first to `skip [1]`, outside
-- the subscription, with `[0]` pinned, beside a hushed body.  The burst
-- pins `[0,0]` then `[0,0,0]` on the left, `[0,0]` then `[0]` on the
-- right: `[0,0,0]` is neither kept nor erased before `[0]`.

zz zzz : Pos
zz  = ix 0 ∷ ix 0 ∷ []
zzz = ix 0 ∷ ix 0 ∷ ix 0 ∷ []

pin-z : Tail
pin-z = pin z λ where .later → idle

loop : Events∞ ℕ
loop .force = skip zzz loop
loop .cut   = pin-z

src : Events∞ ℕ
src .force = skip zz loop
src .cut   = idle

away : Events∞ ℕ
away .force = skip one fin
away .cut   = pin-z

src′ : Events∞ ℕ
src′ .force = skip zz away
src′ .cut   = idle

loop-trail : Trailing loop
loop-trail .trail  = record { sortedᵀ = tt , sortedT-idle } , record { everyᵀ = inj₂ (reshown shown) , everyT-idle } , loop-trail
loop-trail .trailᶠ = record { flatᵀ = everyT-idle , flatT-idle }

loop-ord : Ordered (force loop)
loop-ord .ordered = refl , loop-ord

src-ord : Ordered (force src)
src-ord .ordered = refl , loop-ord

same-z : ∀ n → Eraseᵀ n pin-z pin-z
same-z n = eraseᵀ-agree (agreeᵀ-refl n pin-z)

chain : ∀ n → Erase n (skip zzz loop) pin-z (skip one fin)
chain zero    = stopᵉ
chain (suc n) = erased refl (same-z n) (chain n)

src-erase : ∀ n → Eraseˢ n src src′
src-erase zero    = stopᵉ ,ᵉ stopᵉ
src-erase (suc n) = idleᵉ ,ᵉ skipᵉ (same-z n) (chain n)

hushed : Events∞ ℕ
hushed .force = hush
hushed .cut   = idle

hush-refl : hushed ⊒ hushed
hush-refl = hushᴸ , (λ _ d → agreeᵀ-refl d idle) , λ n → eraseᵀ-agree (agreeᵀ-refl n idle) ,ᵉ hush-erase n
  where
    hush-erase : ∀ n → Erase n hush idle (hush {A = ℕ})
    hush-erase zero    = stopᵉ
    hush-erase (suc n) = Erase.hushᵉ

body-untrailed : (∀ {X B} r {σ σ′ : Events∞ X} {β β′ : Events∞ B} → Sourced r σ → σ ⊒ σ′ → β ⊒ β′ → bodyConn r σ β ⊒ bodyConn r σ′ β′) → ⊥
body-untrailed f with cutᵉ (proj₂ (proj₂ (f zz (sourced refl src-ord (trail-idle _ loop-trail)) (skipᴸ , (λ ()) , src-erase) hush-refl)) 3)
... | pinᵉ (unpin () _)
... | unpin _ (unpin () _)
