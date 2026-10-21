{-# OPTIONS --guardedness #-}

-- A RETAG UNDER A SHUT: a retag that leaves every joiner it touches
-- holding what a shut at `i` would tell it moves no part the shut can
-- see.  Two shuts at distinct connects commute.
module adequacy.Retag.Shut where

open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Any.Properties using (++⁺ˡ; ++⁺ʳ)
open import Data.List.Relation.Unary.All using (lookup) renaming (_∷_ to _∷ᴬ_)
open import Data.Maybe using (Maybe; nothing; just) renaming (map to mapMaybe)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

open import denotation.MonotonicList.Events using (Timeline; Pos)
import denotation.Unfold as U
open import operation.AbstractObservable using (module Run) renaming (module Machine to Shared)
open import operation.PureObservable using (Pureᴾ; Out)
open import adequacy.Strong using (module Strongly)
open import adequacy.Retag using (Retag; keep; module Retagging)
open import adequacy.Frame using (module Framing)

-- What a shut at `i` tells a joiner at `x`, joined at `j`, of what it
-- holds.
tells : ∀ {Δ A B} → A ∈ Δ → Pos → B ∈ Δ → Pos → Maybe (List (Pos × Maybe B) × Maybe Pos) → Maybe (List (Pos × Maybe B) × Maybe Pos)
tells i c x j = mapMaybe λ { (xs , e) → xs , U.told i c x j e (U.same? i x) }

told-there : ∀ {Γ A B C} (i : A ∈ Γ) c (x : B ∈ Γ) p e m → U.told {C ∷ Γ} (there i) c (there x) p e m ≡ U.told i c x p e m
told-there i c x p nothing  (just refl) = refl
told-there i c x p nothing  nothing     = refl
told-there i c x p (just _) m           = refl

tells-there : ∀ {Γ A B C} (i : A ∈ Γ) c (x : B ∈ Γ) j st → tells {C ∷ Γ} (there i) c (there x) j st ≡ tells i c x j st
tells-there         i c x j nothing         = refl
tells-there {C = C} i c x j (just (xs , e)) = cong (λ z → just (xs , z)) (told-there {C = C} i c x j e (U.same? i x))

module RetagShut (R : Set) where
  open Shared Timeline (Out R) using (Heapᴹ)
  open Strongly R
  open Retagging R using (retag; retagᴸ)
  open Framing R using (Apart; here-there; there-here; there-there)
  open Run (Pureᴾ R) using (Env; module Kit; module FlatKit)

  ----------------------------------------------------------------------
  -- Two shuts at distinct connects commute

  apart-same : ∀ {Γ A C B} {k : A ∈ Γ} {i : C ∈ Γ} → Apart k i → (j : B ∈ Γ) → ∀ {e₁ e₂} → U.same? k j ≡ just e₁ → U.same? i j ≡ just e₂ → ⊥
  apart-same here-there      (here refl) _  ()
  apart-same here-there      (there j)   () _
  apart-same there-here      (here refl) () _
  apart-same there-here      (there j)   _  ()
  apart-same (there-there a) (here refl) () _
  apart-same (there-there a) (there j)   ek ei = apart-same a j ek ei

  told-comm : ∀ {Γ A C B} {k : A ∈ Γ} {i : C ∈ Γ} → Apart k i → ∀ c c′ (j : B ∈ Γ) p e
            → U.told k c j p (U.told i c′ j p e (U.same? i j)) (U.same? k j) ≡ U.told i c′ j p (U.told k c j p e (U.same? k j)) (U.same? i j)
  told-comm {k = k} {i} a c c′ j p e with U.same? k j in ek | U.same? i j in ei | e
  ... | nothing   | nothing   | nothing = refl
  ... | nothing   | nothing   | just _  = refl
  ... | just refl | nothing   | nothing = refl
  ... | just refl | nothing   | just _  = refl
  ... | nothing   | just refl | nothing = refl
  ... | nothing   | just refl | just _  = refl
  ... | just _    | just _    | _       = ⊥-elim (apart-same a j ek ei)

  mutual
    shut-comm : ∀ {Γ A C B} {k : A ∈ Γ} {i : C ∈ Γ} → Apart k i → ∀ c c′ (n : U.Node Γ B)
              → U.shut k c (U.shut i c′ n) ≡ U.shut i c′ (U.shut k c n)
    shut-comm a c c′ (U.framesᶜ _ _ _)          = refl
    shut-comm a c c′ (U.burstᶜ _ _ _ _)         = refl
    shut-comm a c c′ (U.ofᶜ _ _ _)              = refl
    shut-comm a c c′ (U.mapᶜ f n)               = cong (U.mapᶜ f) (shut-comm a c c′ n)
    shut-comm a c c′ (U.scanᶜ f z n)            = cong (U.scanᶜ f z) (shut-comm a c c′ n)
    shut-comm a c c′ (U.takeWhileᶜ b p n)       = cong (U.takeWhileᶜ b p) (shut-comm a c c′ n)
    shut-comm a c c′ (U.flatMapᶜ op g o ls qs pl)
      rewrite shut-commᴹ a c c′ o | shut-commᴸ a c c′ ls | shut-comm a c c′ pl = refl
    shut-comm a c c′ (U.joinᶜ j p xs e)         = cong (U.joinᶜ j p xs) (told-comm a c c′ j p e)
    shut-comm a c c′ (U.connectᶜ r b s)         = cong₂ (U.connectᶜ r) (shut-comm (there-there a) c c′ b) (shut-commˢ a c c′ s)
    shut-comm a c c′ (U.deferᶜ _ _ _)           = refl
    shut-comm a c c′ (U.endingᶜ p n)            = cong (U.endingᶜ p) (shut-comm a c c′ n)
    shut-comm a c c′ (U.restᶜ n)                = cong U.restᶜ (shut-comm a c c′ n)
    shut-comm a c c′ U.idleᶜ                    = refl
    shut-comm a c c′ (U.unionᶜ x y)             = cong₂ U.unionᶜ (shut-comm a c c′ x) (shut-comm a c c′ y)
    shut-comm a c c′ (U.burstingᶜ r t)          = cong (U.burstingᶜ r) (shut-comm a c c′ t)
    shut-comm a c c′ (U.underᶜ s b)             = cong₂ U.underᶜ (shut-commˢ a c c′ s) (shut-comm (there-there a) c c′ b)

    shut-commᴹ : ∀ {Γ A C B} {k : A ∈ Γ} {i : C ∈ Γ} → Apart k i → ∀ c c′ (o : Maybe (U.Node Γ B))
               → U.shutᴹ k c (U.shutᴹ i c′ o) ≡ U.shutᴹ i c′ (U.shutᴹ k c o)
    shut-commᴹ a c c′ nothing  = refl
    shut-commᴹ a c c′ (just n) = cong just (shut-comm a c c′ n)

    shut-commᴸ : ∀ {Γ A C B} {k : A ∈ Γ} {i : C ∈ Γ} → Apart k i → ∀ c c′ (ns : List (U.Node Γ B))
               → U.shutᴸ k c (U.shutᴸ i c′ ns) ≡ U.shutᴸ i c′ (U.shutᴸ k c ns)
    shut-commᴸ a c c′ []       = refl
    shut-commᴸ a c c′ (n ∷ ns) = cong₂ _∷_ (shut-comm a c c′ n) (shut-commᴸ a c c′ ns)

    shut-commˢ : ∀ {Γ A C B} {k : A ∈ Γ} {i : C ∈ Γ} → Apart k i → ∀ c c′ (s : U.Source Γ B)
               → U.shutˢ k c (U.shutˢ i c′ s) ≡ U.shutˢ i c′ (U.shutˢ k c s)
    shut-commˢ a c c′ (U.live s)    = cong U.live (shut-comm a c c′ s)
    shut-commˢ a c c′ (U.ended e t) = cong (U.ended e) (shut-comm a c c′ t)

  ----------------------------------------------------------------------
  -- A retag the shut cannot see

  module _ {h} (H : Heapᴹ h) where
    open At H using (Fed; FedLanes; Now; part; partLanes; joinedᶜ; merged; connected; consᴹ; taking?; val; mapᴹ)

    -- Each piece of a part, shut alike before and after.
    mapᴹ-shut : ∀ {Δ A B C} (i : C ∈ Δ) c (F : U.Node Δ A → U.Node Δ B) → (∀ n → U.shut i c (F n) ≡ F (U.shut i c n))
              → ∀ {m m′} → U.shutᴹ i c m ≡ U.shutᴹ i c m′ → U.shutᴹ i c (mapᴹ F m) ≡ U.shutᴹ i c (mapᴹ F m′)
    mapᴹ-shut i c F cm {nothing} {nothing} eq = refl
    mapᴹ-shut i c F cm {just n}  {just n′} eq =
      cong just (trans (cm n) (trans (cong F (just-injective eq)) (sym (cm n′))))
    mapᴹ-shut i c F cm {nothing} {just _}  ()
    mapᴹ-shut i c F cm {just _}  {nothing} ()

    joined-shut : ∀ {Δ A C} (i : C ∈ Δ) c (x : A ∈ Δ) j st → U.shutᴹ i c (joinedᶜ x j st) ≡ joinedᶜ x j (tells i c x j st)
    joined-shut i c x j nothing         = refl
    joined-shut i c x j (just (xs , e)) = refl

    if-joined : ∀ {Δ A C} (i : C ∈ Δ) c (x : A ∈ Δ) j {st st′} (b : Bool) → (b ≡ true → tells i c x j st′ ≡ tells i c x j st)
              → U.shutᴹ i c (if b then joinedᶜ x j st′ else nothing) ≡ U.shutᴹ i c (if b then joinedᶜ x j st else nothing)
    if-joined i c x j false hy = refl
    if-joined i c x j {st} {st′} true hy =
      trans (joined-shut i c x j st′) (trans (cong (joinedᶜ x j) (hy refl)) (sym (joined-shut i c x j st)))

    if-take : ∀ {Δ A C} (i : C ∈ Δ) c ib (p : A → Bool) (b : Bool) (tk : Taking Δ A) {m m′}
            → U.shutᴹ i c m ≡ U.shutᴹ i c m′
            → U.shutᴹ i c (if b then taking? ib p tk m else nothing) ≡ U.shutᴹ i c (if b then taking? ib p tk m′ else nothing)
    if-take i c ib p false tk         eq = refl
    if-take i c ib p true  taking     eq = mapᴹ-shut i c (U.takeWhileᶜ ib p) (λ _ → refl) eq
    if-take i c ib p true  (ending k n) eq = refl
    if-take i c ib p true  taken      eq = refl

    merged-shut : ∀ {Δ A B C} (i : C ∈ Δ) c op (g : A → Pos → U.Node Δ B) {o o′ ls ls′} qs pl
                → U.shutᴹ i c o ≡ U.shutᴹ i c o′ → U.shutᴸ i c ls ≡ U.shutᴸ i c ls′
                → U.shutᴹ i c (merged op g o ls qs pl) ≡ U.shutᴹ i c (merged op g o′ ls′ qs pl)
    merged-shut i c op g {nothing} {nothing} {[]}    {[]}    []      pl eo el = refl
    merged-shut i c op g {nothing} {nothing} {[]}    {[]}    (_ ∷ _) pl eo el = refl
    merged-shut i c op g {nothing} {nothing} {_ ∷ _} {_ ∷ _} qs      pl eo el =
      cong (λ z → just (U.flatMapᶜ op g nothing z qs (U.shut i c pl))) el
    merged-shut i c op g {just _}  {just _}  {ls} {ls′} qs pl eo el =
      cong₂ (λ y z → just (U.flatMapᶜ op g y z qs (U.shut i c pl))) eo el
    merged-shut i c op g {nothing} {just _}  qs pl () el
    merged-shut i c op g {just _}  {nothing} qs pl () el
    merged-shut i c op g {nothing} {nothing} {[]}    {_ ∷ _} qs pl eo ()
    merged-shut i c op g {nothing} {nothing} {_ ∷ _} {[]}    qs pl eo ()

    if-cons : ∀ {Δ B C} (i : C ∈ Δ) c (b : Bool) {m m′ : Maybe (U.Node Δ B)} {xs xs′}
            → U.shutᴹ i c m ≡ U.shutᴹ i c m′ → U.shutᴸ i c xs ≡ U.shutᴸ i c xs′
            → U.shutᴸ i c (if b then consᴹ m xs else xs) ≡ U.shutᴸ i c (if b then consᴹ m′ xs′ else xs′)
    if-cons i c false                         em el = el
    if-cons i c true {nothing} {nothing}      em el = el
    if-cons i c true {just n}  {just n′}      em el = cong₂ _∷_ (just-injective em) el
    if-cons i c true {nothing} {just _}       () el
    if-cons i c true {just _}  {nothing}      () el

    connected-shut : ∀ {Δ A B C} (i : C ∈ Δ) c r e (t : U.Node Δ A) {s s′ : Maybe (U.Node Δ A)} {b b′ : Maybe (U.Node (A ∷ Δ) B)}
                   → U.shutᴹ i c s ≡ U.shutᴹ i c s′ → U.shutᴹ (there i) c b ≡ U.shutᴹ (there i) c b′
                   → U.shutᴹ i c (connected r e t s b) ≡ U.shutᴹ i c (connected r e t s′ b′)
    connected-shut i c r e t {b = nothing} {nothing} es eb = refl
    connected-shut i c r e t {b = nothing} {just _}  es ()
    connected-shut i c r e t {b = just _}  {nothing} es ()
    connected-shut i c r e t {just s} {just s′} {just b} {just b′} es eb =
      cong₂ (λ y z → just (U.connectᶜ r y (U.live z))) (just-injective eb) (just-injective es)
    connected-shut i c r e t {nothing} {just _}  {just _} {just _} () eb
    connected-shut i c r e t {just _}  {nothing} {just _} {just _} () eb
    connected-shut i c r nothing   t {nothing} {nothing} {just b} {just b′} es eb = refl
    connected-shut i c r (just c₀) t {nothing} {nothing} {just b} {just b′} es eb =
      cong (λ y → just (U.connectᶜ r y (U.ended c₀ (U.shut i c t))))
        (trans (shut-comm there-here c c₀ b)
               (trans (cong (U.shut (here refl) c₀) (just-injective eb)) (sym (shut-comm there-here c c₀ b′))))

    -- A retag whose every live joiner of `s` holds what the shut tells
    -- it, before and after, leaves `s`'s part as the shut sees it.
    mutual
      part-shut : ∀ {Δ A C} (i : C ∈ Δ) c (g : Retag Δ) (s : Sub h Δ A) (E : Env Δ h) {ν : Now Δ}
                → (∀ {B} (x : B ∈ Δ) {j sk l st} → joiner (lookup E x) sk j ∈ joiners s E
                   → Fed (joinˢ j sk l x st) ν → val l ≡ true → tells i c x j (g x j st) ≡ tells i c x j st)
                → Fed s ν → U.shutᴹ i c (part (retag g s)) ≡ U.shutᴹ i c (part s)
      part-shut i c g (pendingˢ s q)                       E hy f = refl
      part-shut i c g (coldˢ s hd ph)                      E hy f = refl
      part-shut i c g (ofˢ p ix xs)                        E hy f = refl
      part-shut i c g doneˢ                                E hy f = refl
      part-shut i c g (mapˢ f₀ s)                          E hy f = mapᴹ-shut i c (U.mapᶜ f₀) (λ _ → refl) (part-shut i c g s E hy f)
      part-shut i c g (scanˢ f₀ r s)                       E hy f = mapᴹ-shut i c (U.scanᶜ f₀ (val r)) (λ _ → refl) (part-shut i c g s E hy f)
      part-shut i c g (takeWhileˢ ib p cu k tk s)          E hy f = if-take i c ib p (val (Kit.live cu)) tk (part-shut i c g s E hy f)
      part-shut i c g (flatMapˢ op f₀ fl oc k r pl so ls)  E hy (fs , fl′) =
        merged-shut i c op (λ a q → U.subscribe (f₀ a) q) (val (FlatKit.Flat.queue fl)) pl
          (part-shut i c g so E (λ x {j} {sk} {l} {st} m → hy x {j} {sk} {l} {st} (++⁺ˡ m)) fs)
          (part-shutᴸ i c g ls E (λ x {j} {sk} {l} {st} m → hy x {j} {sk} {l} {st} (++⁺ʳ (joiners so E) m)) fl′)
      part-shut {Δ₀} i c g (connectˢ {A = A₀} S cu b kb k fd rp e rt src bd) E {ν} hy (fs , fb) =
        connected-shut i c rp e rt
          (part-shut i c g src E (λ x {j} {sk} {l} {st} m → hy x {j} {sk} {l} {st} (++⁺ˡ m)) fs)
          (part-shut (there i) c (keep g) bd (S ∷ᴬ E) hb fb)
        where
          hb : ∀ {B} (x : B ∈ A₀ ∷ Δ₀) {j sk l st} → joiner (lookup (S ∷ᴬ E) x) sk j ∈ joiners bd (S ∷ᴬ E)
             → Fed (joinˢ j sk l x st) ((fd , At.told H S e) ∷ᴬ ν) → val l ≡ true
             → tells (there i) c x j (keep g x j st) ≡ tells (there i) c x j st
          hb (here refl) m f′ lv = refl
          hb (there x) {j} {sk} {l} {st} m f′ lv =
            trans (tells-there {C = A₀} i c x j (g x j st))
                  (trans (hy x {j} {sk} {l} {st} (++⁺ʳ (joiners src E) m) f′ lv) (sym (tells-there {C = A₀} i c x j st)))
      part-shut i c g (joinˢ j sk l x st)                  E hy f = if-joined i c x j (val l) (hy x {j} {sk} {l} {st} (here refl) f)
      part-shut i c g (deferˢ k s)                         E hy f = part-shut i c g s E hy f

      part-shutᴸ : ∀ {Δ B C} (i : C ∈ Δ) c (g : Retag Δ) (ls : List (Lane h Δ B)) (E : Env Δ h) {ν : Now Δ}
                 → (∀ {D} (x : D ∈ Δ) {j sk l st} → joiner (lookup E x) sk j ∈ laneJoiners ls E
                    → Fed (joinˢ {A = D} j sk l x st) ν → val l ≡ true → tells i c x j (g x j st) ≡ tells i c x j st)
                 → FedLanes ls ν → U.shutᴸ i c (partLanes (retagᴸ g ls)) ≡ U.shutᴸ i c (partLanes ls)
      part-shutᴸ i c g []                 E hy fl′       = refl
      part-shutᴸ i c g (lane cu k s ∷ ls) E hy (fs , fl′) =
        if-cons i c (val (Kit.live cu))
          (part-shut i c g s E (λ x {j} {sk} {l} {st} m → hy x {j} {sk} {l} {st} (++⁺ˡ m)) fs)
          (part-shutᴸ i c g ls E (λ x {j} {sk} {l} {st} m → hy x {j} {sk} {l} {st} (++⁺ʳ (joiners s E) m)) fl′)
