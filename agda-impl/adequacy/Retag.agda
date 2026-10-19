{-# OPTIONS --guardedness #-}

-- RETAG: what each joiner holds of its feed, rewritten through a
-- subtree.  Only a joiner's part and its `Fed` clause read what it
-- holds, so every other part of the relation is kept as it stands; a
-- feed restaged at a connect is a retag of that connect's body.
module adequacy.Retag where

open import Data.List using (List; []; _∷_)
import Data.Sum as Sum
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Any.Properties using (++⁺ˡ; ++⁺ʳ)
open import Data.List.Relation.Unary.All using (lookup) renaming (_∷_ to _∷ᴬ_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥-elim)
open import Level using (lift)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import denotation.MonotonicList using (Timeline; Pos)
import denotation.Unfold as U
open import operation.AbstractObservable using (module Run; module Heap; maybe; quiet) renaming (module Machine to Shared)
open import operation.PureObservable using (Pureᴾ; Out)
open import adequacy.Strong using (module Strongly)

-- What a joiner at `x`, joined at `j`, holds, rewritten.
Retag : List Set → Set₁
Retag Δ = ∀ {B} → B ∈ Δ → Pos → Maybe (List (Pos × Maybe B) × Maybe Pos) → Maybe (List (Pos × Maybe B) × Maybe Pos)

-- Under a connect: its own joiners kept.
keep : ∀ {A Δ} → Retag Δ → Retag (A ∷ Δ)
keep g (here _)  j st = st
keep g (there x) j st = g x j st

-- A connect's own joiners told what is owed at their positions, the
-- rest kept.
at-here : ∀ {A Δ} → (Pos → Maybe (List (Pos × Maybe A) × Maybe Pos)) → Retag (A ∷ Δ)
at-here o (here refl) j st = o j
at-here o (there x)   j st = st

module Retagging (R : Set) where
  open Shared Timeline (Out R) using (Heapᴹ)
  open Strongly R
  open Heap using (Quiet)
  open Run (Pureᴾ R) using (Env; Ref; Subject; module Kit)

  mutual
    retag : ∀ {h Δ A} → Retag Δ → Sub h Δ A → Sub h Δ A
    retag g (pendingˢ s q)                          = pendingˢ s q
    retag g (coldˢ s hd ph)                         = coldˢ s hd ph
    retag g (ofˢ p i xs)                            = ofˢ p i xs
    retag g doneˢ                                   = doneˢ
    retag g (mapˢ f s)                              = mapˢ f (retag g s)
    retag g (scanˢ f r s)                           = scanˢ f r (retag g s)
    retag g (takeWhileˢ i p c k tk s)               = takeWhileˢ i p c k tk (retag g s)
    retag g (flatMapˢ op f fl oc k r pl so ls)      = flatMapˢ op f fl oc k r pl (retag g so) (retagᴸ g ls)
    retag g (connectˢ S c b kb k fd rp e rt src bd) = connectˢ S c b kb k fd rp e rt (retag g src) (retag (keep g) bd)
    retag g (joinˢ j sk l x st)                     = joinˢ j sk l x (g x j st)
    retag g (deferˢ k s)                            = deferˢ k (retag g s)

    retagᴸ : ∀ {h Δ B} → Retag Δ → List (Lane h Δ B) → List (Lane h Δ B)
    retagᴸ g []                = []
    retagᴸ g (lane c k s ∷ ls) = lane c k (retag g s) ∷ retagᴸ g ls

  ----------------------------------------------------------------------
  -- What reads no joiner's feed

  mutual
    names-retag : ∀ {h Δ A} (g : Retag Δ) (s : Sub h Δ A) → names (retag g s) ≡ names s
    names-retag g (pendingˢ s q)                          = refl
    names-retag g (coldˢ s hd ph)                         = refl
    names-retag g (ofˢ p i xs)                            = refl
    names-retag g doneˢ                                   = refl
    names-retag g (mapˢ f s)                              = names-retag g s
    names-retag g (scanˢ f r s)                           rewrite names-retag g s = refl
    names-retag g (takeWhileˢ i p c k tk s)               rewrite names-retag g s = refl
    names-retag g (flatMapˢ op f fl oc k r pl so ls)      rewrite names-retag g so | names-retagᴸ g ls = refl
    names-retag g (connectˢ S c b kb k fd rp e rt src bd) rewrite names-retag g src | names-retag (keep g) bd = refl
    names-retag g (joinˢ j sk l x st)                     = refl
    names-retag g (deferˢ k s)                            rewrite names-retag g s = refl

    names-retagᴸ : ∀ {h Δ B} (g : Retag Δ) (ls : List (Lane h Δ B)) → laneNames (retagᴸ g ls) ≡ laneNames ls
    names-retagᴸ g []                = refl
    names-retagᴸ g (lane c k s ∷ ls) rewrite names-retag g s | names-retagᴸ g ls = refl

  mutual
    subjects-retag : ∀ {h Δ A} (g : Retag Δ) (s : Sub h Δ A) → subjects (retag g s) ≡ subjects s
    subjects-retag g (pendingˢ s q)                          = refl
    subjects-retag g (coldˢ s hd ph)                         = refl
    subjects-retag g (ofˢ p i xs)                            = refl
    subjects-retag g doneˢ                                   = refl
    subjects-retag g (mapˢ f s)                              = subjects-retag g s
    subjects-retag g (scanˢ f r s)                           = subjects-retag g s
    subjects-retag g (takeWhileˢ i p c k tk s)               = subjects-retag g s
    subjects-retag g (flatMapˢ op f fl oc k r pl so ls)      rewrite subjects-retag g so | subjects-retagᴸ g ls = refl
    subjects-retag g (connectˢ S c b kb k fd rp e rt src bd) rewrite subjects-retag g src | subjects-retag (keep g) bd = refl
    subjects-retag g (joinˢ j sk l x st)                     = refl
    subjects-retag g (deferˢ k s)                            = subjects-retag g s

    subjects-retagᴸ : ∀ {h Δ B} (g : Retag Δ) (ls : List (Lane h Δ B)) → laneSubjects (retagᴸ g ls) ≡ laneSubjects ls
    subjects-retagᴸ g []                = refl
    subjects-retagᴸ g (lane c k s ∷ ls) rewrite subjects-retag g s | subjects-retagᴸ g ls = refl

  mutual
    joiners-retag : ∀ {h Δ A} (g : Retag Δ) (s : Sub h Δ A) E → joiners (retag g s) E ≡ joiners s E
    joiners-retag g (pendingˢ s q)                          E = refl
    joiners-retag g (coldˢ s hd ph)                         E = refl
    joiners-retag g (ofˢ p i xs)                            E = refl
    joiners-retag g doneˢ                                   E = refl
    joiners-retag g (mapˢ f s)                              E = joiners-retag g s E
    joiners-retag g (scanˢ f r s)                           E = joiners-retag g s E
    joiners-retag g (takeWhileˢ i p c k tk s)               E = joiners-retag g s E
    joiners-retag g (flatMapˢ op f fl oc k r pl so ls)      E rewrite joiners-retag g so E | joiners-retagᴸ g ls E = refl
    joiners-retag g (connectˢ S c b kb k fd rp e rt src bd) E rewrite joiners-retag g src E | joiners-retag (keep g) bd (S ∷ᴬ E) = refl
    joiners-retag g (joinˢ j sk l x st)                     E = refl
    joiners-retag g (deferˢ k s)                            E = joiners-retag g s E

    joiners-retagᴸ : ∀ {h Δ B} (g : Retag Δ) (ls : List (Lane h Δ B)) E → laneJoiners (retagᴸ g ls) E ≡ laneJoiners ls E
    joiners-retagᴸ g []                E = refl
    joiners-retagᴸ g (lane c k s ∷ ls) E rewrite joiners-retag g s E | joiners-retagᴸ g ls E = refl

  mutual
    pendings-retag : ∀ {h Δ A} (g : Retag Δ) (s : Sub h Δ A) → pendings (retag g s) ≡ pendings s
    pendings-retag g (pendingˢ s q)                          = refl
    pendings-retag g (coldˢ s hd ph)                         = refl
    pendings-retag g (ofˢ p i xs)                            = refl
    pendings-retag g doneˢ                                   = refl
    pendings-retag g (mapˢ f s)                              = pendings-retag g s
    pendings-retag g (scanˢ f r s)                           = pendings-retag g s
    pendings-retag g (takeWhileˢ i p c k tk s)               = pendings-retag g s
    pendings-retag g (flatMapˢ op f fl oc k r pl so ls)      rewrite pendings-retag g so | pendings-retagᴸ g ls = refl
    pendings-retag g (connectˢ S c b kb k fd rp e rt src bd) rewrite pendings-retag g src | pendings-retag (keep g) bd = refl
    pendings-retag g (joinˢ j sk l x st)                     = refl
    pendings-retag g (deferˢ k s)                            = pendings-retag g s

    pendings-retagᴸ : ∀ {h Δ B} (g : Retag Δ) (ls : List (Lane h Δ B)) → lanePendings (retagᴸ g ls) ≡ lanePendings ls
    pendings-retagᴸ g []                = refl
    pendings-retagᴸ g (lane c k s ∷ ls) rewrite pendings-retag g s | pendings-retagᴸ g ls = refl

  unsub-retag : ∀ {h Δ A} (g : Retag Δ) (s : Sub h Δ A) → unsub (retag g s) ≡ unsub s
  unsub-retag g (pendingˢ s q)                          = refl
  unsub-retag g (coldˢ s hd ph)                         = refl
  unsub-retag g (ofˢ p i xs)                            = refl
  unsub-retag g doneˢ                                   = refl
  unsub-retag g (mapˢ f s)                              = unsub-retag g s
  unsub-retag g (scanˢ f r s)                           = unsub-retag g s
  unsub-retag g (takeWhileˢ i p c k tk s)               = refl
  unsub-retag g (flatMapˢ op f fl oc k r pl so ls)      = refl
  unsub-retag g (connectˢ S c b kb k fd rp e rt src bd) rewrite unsub-retag g src = refl
  unsub-retag g (joinˢ j sk l x st)                     = refl
  unsub-retag g (deferˢ k s)                            = refl

  owes-retag : ∀ {h Δ A} (g : Retag Δ) (s : Sub h Δ A) → Owes (retag g s) → Owes s
  owes-retag g (pendingˢ s q)                          ow = ow
  owes-retag g (coldˢ s hd ph)                         ow = ow
  owes-retag g (ofˢ p i xs)                            ow = ow
  owes-retag g doneˢ                                   ow = ow
  owes-retag g (mapˢ f s)                              ow = owes-retag g s ow
  owes-retag g (scanˢ f r s)                           ow = owes-retag g s ow
  owes-retag g (takeWhileˢ i p c k tk s)               ow = ow
  owes-retag g (flatMapˢ op f fl oc k r pl so ls)      ow = ow
  owes-retag g (connectˢ S c b kb k fd rp e rt src bd) ow = owes-retag g src ow
  owes-retag g (joinˢ j sk l x st)                     ow = ow
  owes-retag g (deferˢ k s)                            ow = ow

  begun-retag : ∀ {h Δ A} (g : Retag Δ) k (s : Sub h Δ A) → Begun k s → Begun k (retag g s)
  begun-retag g nothing  s b = b
  begun-retag g (just _) s b = λ ow → b (owes-retag g s ow)

  ----------------------------------------------------------------------
  -- The feed: each joiner the retag moves, fed as its `Fed` clause asks

  module _ {h} (H : Heapᴹ h) where
    open At H using (Fed; FedLanes; Now)

    mutual
      fed-retag : ∀ {Δ A} (g : Retag Δ) (s : Sub h Δ A) (E : Env Δ h) {ν ν′ : Now Δ}
                → (∀ {B} (x : B ∈ Δ) {j sk l st} → joiner (lookup E x) sk j ∈ joiners s E
                   → Fed (joinˢ j sk l x st) ν → Fed (joinˢ j sk l x (g x j st)) ν′)
                → Fed s ν → Fed (retag g s) ν′
      fed-retag g (pendingˢ s q)                          E hy f = f
      fed-retag g (coldˢ s hd ph)                         E hy f = f
      fed-retag g (ofˢ p i xs)                            E hy f = f
      fed-retag g doneˢ                                   E hy f = f
      fed-retag g (mapˢ f₀ s)                             E hy f = fed-retag g s E hy f
      fed-retag g (scanˢ f₀ r s)                          E hy f = fed-retag g s E hy f
      fed-retag g (takeWhileˢ i p c k tk s)               E hy f = fed-retag g s E hy f
      fed-retag g (flatMapˢ op f₀ fl oc k r pl so ls)     E hy (fs , fl′) =
        fed-retag g so E (λ x {j} {sk} {l} {st} m → hy x {j} {sk} {l} {st} (++⁺ˡ m)) fs
        , fed-retagᴸ g ls E (λ x {j} {sk} {l} {st} m → hy x {j} {sk} {l} {st} (++⁺ʳ (joiners so E) m)) fl′
      fed-retag {Δ₀} g (connectˢ {A = A₀} S c b kb k fd rp e rt src bd) E {ν} {ν′} hy (fs , fb) =
        fed-retag g src E (λ x {j} {sk} {l} {st} m → hy x {j} {sk} {l} {st} (++⁺ˡ m)) fs
        , fed-retag (keep g) bd (S ∷ᴬ E) hb fb
        where
          hb : ∀ {B} (x : B ∈ A₀ ∷ Δ₀) {j sk l st} → joiner (lookup (S ∷ᴬ E) x) sk j ∈ joiners bd (S ∷ᴬ E)
             → Fed (joinˢ j sk l x st) ((fd , e) ∷ᴬ ν) → Fed (joinˢ j sk l x (keep g x j st)) ((fd , e) ∷ᴬ ν′)
          hb (here refl) m f′ = f′
          hb (there x) {j} {sk} {l} {st} m f′ = hy x {j} {sk} {l} {st} (++⁺ʳ (joiners src E) m) f′
      fed-retag g (joinˢ j sk l x st)                     E hy f = hy x {j} {sk} {l} {st} (here refl) f
      fed-retag g (deferˢ k s)                            E hy f = fed-retag g s E hy f

      fed-retagᴸ : ∀ {Δ B} (g : Retag Δ) (ls : List (Lane h Δ B)) (E : Env Δ h) {ν ν′ : Now Δ}
                 → (∀ {C} (x : C ∈ Δ) {j sk l st} → joiner (lookup E x) sk j ∈ laneJoiners ls E
                    → Fed (joinˢ {A = C} j sk l x st) ν → Fed (joinˢ j sk l x (g x j st)) ν′)
                 → FedLanes ls ν → FedLanes (retagᴸ g ls) ν′
      fed-retagᴸ g []                E hy fl′       = fl′
      fed-retagᴸ g (lane c k s ∷ ls) E hy (fs , fl′) =
        fed-retag g s E (λ x {j} {sk} {l} {st} m → hy x {j} {sk} {l} {st} (++⁺ˡ m)) fs
        , fed-retagᴸ g ls E (λ x {j} {sk} {l} {st} m → hy x {j} {sk} {l} {st} (++⁺ʳ (joiners s E) m)) fl′

  ----------------------------------------------------------------------
  -- A connect's body retagged, its feed restaged: what reads neither
  -- kept; the feed read by its own joiners alone.

  module Body {h} (H : Heapᴹ h) {Δ A B} (S : Subject A h) (c : Kit.Cut h) (b : Ref h (maybe quiet)) (kb k : Maybe (Quiet h))
              (fd₁ fd₂ : Feed A h) (rp : Pos) (e : Maybe Pos) (rt : U.Node Δ A) (src : Sub h Δ A) (g : Retag (A ∷ Δ)) (bd : Sub h (A ∷ Δ) B) where
    w₁ w₂ : Sub h Δ B
    w₁ = connectˢ S c b kb k fd₁ rp e rt src bd
    w₂ = connectˢ S c b kb k fd₂ rp e rt src (retag g bd)

    body-names : names w₁ ≡ names w₂
    body-names rewrite names-retag g bd = refl

    body-subjects : subjects w₁ ≡ subjects w₂
    body-subjects rewrite subjects-retag g bd = refl

    body-joiners : ∀ E → joiners w₁ E ≡ joiners w₂ E
    body-joiners E rewrite joiners-retag g bd (S ∷ᴬ E) = refl

    body-pendings : pendings w₁ ≡ pendings w₂
    body-pendings rewrite pendings-retag g bd = refl

    body-owes : Owes w₂ → Owes w₁
    body-owes ow = ow

  -- A feed restaged from `idle`: each of the connect's own joiners owed
  -- it is told what it is owed.
  fed-owed : ∀ {h} (H : Heapᴹ h) {Δ A B} (S : Subject A h) c b kb k (fd : Feed A h) rp e rt (src : Sub h Δ A) (bd : Sub h (A ∷ Δ) B) (E : Env Δ h)
           → (∀ {sk j} → joiner S sk j ∈ joiners bd (S ∷ᴬ E) → At.Owed H fd sk j)
           → ∀ ν → At.Fed H (Body.w₁ H S c b kb k idle fd rp e rt src (at-here (At.owing H fd)) bd) ν
                 → At.Fed H (Body.w₂ H S c b kb k idle fd rp e rt src (at-here (At.owing H fd)) bd) ν
  fed-owed H {Δ} {A} S c b kb k fd rp e rt src bd E ow ν (fs , fb) = fs , fed-retag H (at-here (At.owing H fd)) bd (S ∷ᴬ E) hy fb
    where
      hy : ∀ {C} (x : C ∈ A ∷ Δ) {j sk l st} → joiner (lookup (S ∷ᴬ E) x) sk j ∈ joiners bd (S ∷ᴬ E)
         → At.Fed H (joinˢ j sk l x st) ((idle , e) ∷ᴬ ν) → At.Fed H (joinˢ j sk l x (at-here (At.owing H fd) x j st)) ((fd , e) ∷ᴬ ν)
      hy (here refl) m _ = lift λ _ → (λ _ → refl) , λ no → ⊥-elim (no (ow m))
      hy (there x)   m f = f

  ----------------------------------------------------------------------
  -- The subjects in scope along a path, and the joiners met there

  mutual
    envP : ∀ {h Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} → Path t u → Env Δ h → Env Δ′ h
    envP here               E = E
    envP (in-map π)         E = envP π E
    envP (in-scan π)        E = envP π E
    envP (in-take π)        E = envP π E
    envP (in-outer π)       E = envP π E
    envP (in-lanes π)       E = envPᴸ π E
    envP (in-source π)      E = envP π E
    envP (in-body {S = S} π) E = envP π (S ∷ᴬ E)
    envP (in-defer π)       E = envP π E

    envPᴸ : ∀ {h Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} → PathLanes ls u → Env Δ h → Env Δ′ h
    envPᴸ (this-lane π) E = envP π E
    envPᴸ (next-lane π) E = envPᴸ π E

  mutual
    joiners-path : ∀ {h Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (E : Env Δ h) {y}
                 → y ∈ joiners u (envP π E) → y ∈ joiners t E
    joiners-path here                          E m = m
    joiners-path (in-map π)                    E m = joiners-path π E m
    joiners-path (in-scan π)                   E m = joiners-path π E m
    joiners-path (in-take π)                   E m = joiners-path π E m
    joiners-path (in-outer π)                  E m = ++⁺ˡ (joiners-path π E m)
    joiners-path (in-lanes {t = so} π)         E m = ++⁺ʳ (joiners so E) (joiners-pathᴸ π E m)
    joiners-path (in-source π)                 E m = ++⁺ˡ (joiners-path π E m)
    joiners-path (in-body {S = S} {t = s} π)   E m = ++⁺ʳ (joiners s E) (joiners-path π (S ∷ᴬ E) m)
    joiners-path (in-defer π)                  E m = joiners-path π E m

    joiners-pathᴸ : ∀ {h Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (π : PathLanes ls u) (E : Env Δ h) {y}
                  → y ∈ joiners u (envPᴸ π E) → y ∈ laneJoiners ls E
    joiners-pathᴸ (this-lane π)                    E m = ++⁺ˡ (joiners-path π E m)
    joiners-pathᴸ (next-lane {l = lane c k s} π)   E m = ++⁺ʳ (joiners s E) (joiners-pathᴸ π E m)
