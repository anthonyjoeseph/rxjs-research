{-# OPTIONS --guardedness --large-indices #-}

-- THE BUDGET ONLY CUTS.  A run on a bigger budget, of a deeper
-- approximant of the compiler, shows everything the smaller one does:
-- the two go in lockstep until the smaller one reaches a `diverge`,
-- which aborts it whole, and the record it leaves behind only ever
-- grows after that.
--
-- So it is a simulation, generic in the program: `_≼_` relates two
-- `Act`s alike but where the left one diverges, every kernel and the
-- compiler preserve it, and the pure runtime turns it into a run that is
-- the same, or cut short of the other.
module operation.Budget where

open import Data.Bool using (Bool; true; false; if_then_else_; not; _∧_)
open import Data.List using (List; []; _∷_; _++_; [_]; null)
open import Data.Nat using (ℕ; zero; suc; pred; _<ᵇ_; _≡ᵇ_)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Data.List.Relation.Unary.All using (lookup) renaming (_∷_ to _∷ᴬ_)

open import denotation.MonotonicList using (Timeline)
open import Tree using (Obs; Later; mergeᶠ; switchᶠ; exhaustᶠ; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import operation.AbstractObservable using (Ty; base; module Prims; module Run)
open import operation.PureObservable using (Pureᴾ; Sink; Handle; Out; same; module Pure) renaming (_⊑_ to _≤ʷ_; _⨾_ to _⨾ʷ_)

module Approx (R : Set) where
  open Prims (Pureᴾ R) using (wkSink)
  open Run (Pureᴾ R)
  open Kit
  open FlatKit
  open Pure R using (deferredᴺ; compileᴺ)

  ------------------------------------------------------------------------
  -- Alike, but where the left diverges

  infix 4 _≼_
  data _≼_ {w B} : Act w B → Act w B → Set₁ where
    ⊥≼         : ∀ {a} → diverge ≼ a
    done≼      : ∀ {b} → done b ≼ done b
    newRef≼    : ∀ {t a} {k k′ : ∀ {v} → w ≤ʷ v → Ref v t → Act v B} → (∀ {v} (σ : w ≤ʷ v) r → k σ r ≼ k′ σ r) → newRef t a k ≼ newRef t a k′
    readRef≼   : ∀ {t} {r : Ref w t} {k k′ : ∀ {v} → w ≤ʷ v → El v t → Act v B} → (∀ {v} (σ : w ≤ʷ v) x → k σ x ≼ k′ σ x) → readRef r k ≼ readRef r k′
    writeRef≼  : ∀ {t} {r : Ref w t} {a k k′} → k ≼ k′ → writeRef r a k ≼ writeRef r a k′
    register≼  : ∀ {A} {n n′ : A → Act w ⊤} {c c′ x x′} {k k′ : ∀ {v} → w ≤ʷ v → Sink v A → Act v B} → (∀ a → n a ≼ n′ a) → c ≼ c′ → x ≼ x′
               → (∀ {v} (σ : w ≤ʷ v) s → k σ s ≼ k′ σ s) → register n c x k ≼ register n′ c′ x′ k′
    send≼      : ∀ {A} {s : Sink w A} {a k k′} → k ≼ k′ → send s a k ≼ send s a k′
    finish≼    : ∀ {A} {s : Sink w A} {k k′} → k ≼ k′ → finish s k ≼ finish s k′
    startCold≼ : ∀ {A} {c : Timeline A} {s} {k k′ : ∀ {v} → w ≤ʷ v → Handle v → Act v B} → (∀ {v} (σ : w ≤ʷ v) h → k σ h ≼ k′ σ h) → startCold c s k ≼ startCold c s k′
    stop≼      : ∀ {h k k′} → k ≼ k′ → stop h k ≼ stop h k′
    eff≼       : ∀ {A} {e : Out R A} {k k′} → (∀ a → k a ≼ k′ a) → eff e k ≼ eff e k′
    unfold≼    : ∀ {Γ A} {l : Later Timeline Γ A} {e} {n n′ : A → Act w ⊤} {c c′ x x′ m m′} {k k′ : ∀ {v} → w ≤ʷ v → Sink v ⊤ → Act v ⊤}
               → (∀ a → n a ≼ n′ a) → c ≼ c′ → x ≼ x′ → (∀ {v} (σ : w ≤ʷ v) s → k σ s ≼ k′ σ s) → m ≼ m′
               → unfold l e n c x k m ≼ unfold l e n′ c′ x′ k′ m′

  ≼-refl : ∀ {w B} (a : Act w B) → a ≼ a
  ≼-refl (done b)               = done≼
  ≼-refl (newRef t a k)         = newRef≼ λ σ r → ≼-refl (k σ r)
  ≼-refl (readRef r k)          = readRef≼ λ σ x → ≼-refl (k σ x)
  ≼-refl (writeRef r a k)       = writeRef≼ (≼-refl k)
  ≼-refl (register n c x k)     = register≼ (λ a → ≼-refl (n a)) (≼-refl c) (≼-refl x) λ σ s → ≼-refl (k σ s)
  ≼-refl (send s a k)           = send≼ (≼-refl k)
  ≼-refl (finish s k)           = finish≼ (≼-refl k)
  ≼-refl (startCold c s k)      = startCold≼ λ σ h → ≼-refl (k σ h)
  ≼-refl (stop h k)             = stop≼ (≼-refl k)
  ≼-refl (eff e k)              = eff≼ λ a → ≼-refl (k a)
  ≼-refl diverge                = ⊥≼
  ≼-refl (unfold l e n c x k m) = unfold≼ (λ a → ≼-refl (n a)) (≼-refl c) (≼-refl x) (λ σ s → ≼-refl (k σ s)) (≼-refl m)

  ≼-wk : ∀ {w v B} {a a′ : Act w B} (ρ : w ≤ʷ v) → a ≼ a′ → wkAct ρ a ≼ wkAct ρ a′
  ≼-wk ρ ⊥≼                       = ⊥≼
  ≼-wk ρ done≼                    = done≼
  ≼-wk ρ (newRef≼ p)              = newRef≼ λ σ r → p (ρ ⨾ʷ σ) r
  ≼-wk ρ (readRef≼ p)             = readRef≼ λ σ x → p (ρ ⨾ʷ σ) x
  ≼-wk ρ (writeRef≼ p)            = writeRef≼ (≼-wk ρ p)
  ≼-wk ρ (register≼ pn pc px pk)  = register≼ (λ a → ≼-wk ρ (pn a)) (≼-wk ρ pc) (≼-wk ρ px) λ σ s → pk (ρ ⨾ʷ σ) s
  ≼-wk ρ (send≼ p)                = send≼ (≼-wk ρ p)
  ≼-wk ρ (finish≼ p)              = finish≼ (≼-wk ρ p)
  ≼-wk ρ (startCold≼ p)           = startCold≼ λ σ h → p (ρ ⨾ʷ σ) h
  ≼-wk ρ (stop≼ p)                = stop≼ (≼-wk ρ p)
  ≼-wk ρ (eff≼ p)                 = eff≼ λ a → ≼-wk ρ (p a)
  ≼-wk ρ (unfold≼ pn pc px pk pm) = unfold≼ (λ a → ≼-wk ρ (pn a)) (≼-wk ρ pc) (≼-wk ρ px) (λ σ s → pk (ρ ⨾ʷ σ) s) (≼-wk ρ pm)

  ≼-bind : ∀ {w A B} {m m′ : Act w A} {f f′ : A → Act w B} → m ≼ m′ → (∀ x → f x ≼ f′ x) → (m >>=ᴬ f) ≼ (m′ >>=ᴬ f′)
  ≼-bind ⊥≼                       q = ⊥≼
  ≼-bind done≼                    q = q _
  ≼-bind (newRef≼ p)              q = newRef≼ λ σ r → ≼-bind (p σ r) λ x → ≼-wk σ (q x)
  ≼-bind (readRef≼ p)             q = readRef≼ λ σ a → ≼-bind (p σ a) λ x → ≼-wk σ (q x)
  ≼-bind (writeRef≼ p)            q = writeRef≼ (≼-bind p q)
  ≼-bind (register≼ pn pc px pk)  q = register≼ pn pc px λ σ s → ≼-bind (pk σ s) λ x → ≼-wk σ (q x)
  ≼-bind (send≼ p)                q = send≼ (≼-bind p q)
  ≼-bind (finish≼ p)              q = finish≼ (≼-bind p q)
  ≼-bind (startCold≼ p)           q = startCold≼ λ σ h → ≼-bind (p σ h) λ x → ≼-wk σ (q x)
  ≼-bind (stop≼ p)                q = stop≼ (≼-bind p q)
  ≼-bind (eff≼ p)                 q = eff≼ λ a → ≼-bind (p a) q
  ≼-bind (unfold≼ pn pc px pk pm) q = unfold≼ pn pc px pk (≼-bind pm q)

  ≼-then : ∀ {w B} {m m′ : Act w ⊤} {n n′ : Act w B} → m ≼ m′ → n ≼ n′ → (m >>ᴬ n) ≼ (m′ >>ᴬ n′)
  ≼-then p q = ≼-bind p λ _ → q

  ≼-pre : ∀ {w B} (m : Act w ⊤) {n n′ : Act w B} → n ≼ n′ → (m >>ᴬ n) ≼ (m >>ᴬ n′)
  ≼-pre m = ≼-then (≼-refl m)

  ≼-if : ∀ {w B} (b : Bool) {m m′ n n′ : Act w B} → m ≼ m′ → n ≼ n′ → (if b then m else n) ≼ (if b then m′ else n′)
  ≼-if true  p q = p
  ≼-if false p q = q

  ------------------------------------------------------------------------
  -- Observers, continuations, subscribers

  record _≼ᴼ_ {A w} (o o′ : Observer A w) : Set₁ where
    field
      next≼     : ∀ a → Observer.next o a ≼ Observer.next o′ a
      complete≼ : Observer.complete o ≼ Observer.complete o′
      closed≼   : Observer.closed o ≼ Observer.closed o′
  open _≼ᴼ_

  ≼ᴼ-wk : ∀ {A w v} {o o′ : Observer A w} (ρ : w ≤ʷ v) → o ≼ᴼ o′ → wkObs ρ o ≼ᴼ wkObs ρ o′
  ≼ᴼ-wk ρ p = record { next≼ = λ a → ≼-wk ρ (next≼ p a) ; complete≼ = ≼-wk ρ (complete≼ p) ; closed≼ = ≼-wk ρ (closed≼ p) }

  _≼ᴷ_ : ∀ {w} → Kont w → Kont w → Set₁
  _≼ᴷ_ {w} k k′ = ∀ {v} (σ : w ≤ʷ v) {u u′ : Subscription v}
                → Subscription.unsubscribe u ≼ Subscription.unsubscribe u′ → k σ u ≼ k′ σ u′

  ≼ᴷ-wk : ∀ {w v} {k k′ : Kont w} (ρ : w ≤ʷ v) → k ≼ᴷ k′ → wkKont ρ k ≼ᴷ wkKont ρ k′
  ≼ᴷ-wk ρ p σ = p (ρ ⨾ʷ σ)

  _≼ˢ_ : ∀ {A w} → Subscribe A w → Subscribe A w → Set₁
  _≼ˢ_ {A} {w} s s′ = ∀ {v} (σ : w ≤ʷ v) {o o′ : Observer A v} {k k′ : Kont v} → o ≼ᴼ o′ → k ≼ᴷ k′ → s σ o k ≼ s′ σ o′ k′

  ≼ˢ-wk : ∀ {A w v} {s s′ : Subscribe A w} (ρ : w ≤ʷ v) → s ≼ˢ s′ → wkSub ρ s ≼ˢ wkSub ρ s′
  ≼ˢ-wk ρ p σ = p (ρ ⨾ʷ σ)

  ------------------------------------------------------------------------
  -- The kit

  each-≼ : ∀ {w} {A : Set} (xs : List A) {f f′ : A → Act w ⊤} → (∀ x → f x ≼ f′ x) → each xs f ≼ each xs f′
  each-≼ []       p = done≼
  each-≼ (x ∷ xs) p = ≼-then (p x) (each-≼ xs p)

  readB-≼ : ∀ {w B X} {r : Ref w (base X)} {k k′ : X → Act w B} → (∀ x → k x ≼ k′ x) → readB r k ≼ readB r k′
  readB-≼ p = readRef≼ λ σ x → ≼-wk σ (p x)

  when-≼ : ∀ {w} (b : Bool) {m m′ : Act w ⊤} → m ≼ m′ → when b m ≼ when b m′
  when-≼ b p = ≼-if b p done≼

  guard-≼ : ∀ {w} (c : Cut w) {m m′} → m ≼ m′ → guard c m ≼ guard c m′
  guard-≼ c p = readB-≼ λ b → when-≼ b p

  attach-≼ : ∀ {w} (c : Cut w) {u u′ : Subscription w} → Subscription.unsubscribe u ≼ Subscription.unsubscribe u′
           → attach c u ≼ attach c u′
  attach-≼ c p = register≼ (λ _ → p) done≼ done≼ λ σ sk → writeRef≼ (readB-≼ λ b → ≼-if b done≼ (≼-wk σ p))

  guarded-≼ : ∀ {A w} (c : Cut w) {o o′ : Observer A w} → o ≼ᴼ o′ → guarded c o ≼ᴼ guarded c o′
  guarded-≼ c p = record { next≼ = λ a → guard-≼ c (next≼ p a) ; complete≼ = guard-≼ c (complete≼ p)
                         ; closed≼ = readB-≼ λ b → ≼-if b (closed≼ p) done≼ }

  newCut-≼ : ∀ {w B} {k k′ : ∀ {v} → w ≤ʷ v → Cut v → Act v B} → (∀ {v} (σ : w ≤ʷ v) c → k σ c ≼ k′ σ c) → newCut k ≼ newCut k′
  newCut-≼ p = newRef≼ λ σ l → newRef≼ λ τ h → p (σ ⨾ʷ τ) _

  ------------------------------------------------------------------------
  -- Every kernel is monotone

  ⊥-≼ : ∀ {A w} {s : Subscribe A w} → ⊥ᴷ ≼ˢ s
  ⊥-≼ σ p q = ⊥≼

  via-≼ : ∀ {A w} (c : Timeline A) → via {A} {w} (startCold c) ≼ˢ via (startCold c)
  via-≼ c σ p q = register≼ (next≼ p) (complete≼ p) (closed≼ p) λ τ s → startCold≼ λ υ h → q (τ ⨾ʷ υ) (stop≼ done≼)

  empty-≼ : ∀ {A w} → emptyᴷ {A} {w} ≼ˢ emptyᴷ
  empty-≼ σ p q = ≼-then (complete≼ p) (q same done≼)

  emitAll-≼ : ∀ {A w} {o o′ : Observer A w} → o ≼ᴼ o′ → ∀ xs → emitAll o xs ≼ emitAll o′ xs
  emitAll-≼ p []       = complete≼ p
  emitAll-≼ p (x ∷ xs) = ≼-bind (closed≼ p) λ c → when-≼ (not c) (≼-then (next≼ p x) (emitAll-≼ p xs))

  of-≼ : ∀ {A w} (xs : List A) → ofᴷ {w = w} xs ≼ˢ ofᴷ xs
  of-≼ xs σ p q = ≼-then (emitAll-≼ p xs) (q same done≼)

  map-≼ : ∀ {A B w} (f : A → B) {s s′ : Subscribe A w} → s ≼ˢ s′ → mapᴷ f s ≼ˢ mapᴷ f s′
  map-≼ f ps σ p q = ps σ (record { next≼ = λ a → next≼ p (f a) ; complete≼ = complete≼ p ; closed≼ = closed≼ p }) q

  scan-≼ : ∀ {A B w} (f : B → A → B) z {s s′ : Subscribe A w} → s ≼ˢ s′ → scanᴷ f z s ≼ˢ scanᴷ f z s′
  scan-≼ f z ps σ p q = newRef≼ λ τ r →
    ps (σ ⨾ʷ τ) (record { next≼ = λ a → readB-≼ λ b → writeRef≼ (next≼ (≼ᴼ-wk τ p) (f b a))
                        ; complete≼ = complete≼ (≼ᴼ-wk τ p) ; closed≼ = closed≼ (≼ᴼ-wk τ p) }) (≼ᴷ-wk τ q)

  takeWhile-≼ : ∀ {A w} i (f : A → Bool) {s s′ : Subscribe A w} → s ≼ˢ s′ → takeWhileᴷ i f s ≼ˢ takeWhileᴷ i f s′
  takeWhile-≼ i f ps σ p q = newCut-≼ λ τ c →
    ps (σ ⨾ʷ τ) (guarded-≼ c (record
      { next≼ = λ a → ≼-if (f a) (next≼ (≼ᴼ-wk τ p) a)
                        (≼-then (≼-then (when-≼ i (next≼ (≼ᴼ-wk τ p) a)) (complete≼ (≼ᴼ-wk τ p))) (≼-refl (cut c)))
      ; complete≼ = complete≼ (≼ᴼ-wk τ p) ; closed≼ = closed≼ (≼ᴼ-wk τ p) }))
      λ υ u → ≼-then (attach-≼ (wkCut υ c) u) (q (τ ⨾ʷ υ) (≼-refl (cut (wkCut υ c))))

  module FlatMap-≼ {A B : Set} {w} op {f f′ : A → Subscribe B w} (pf : ∀ a → f a ≼ˢ f′ a)
                   {o o′ : Observer B w} (p : o ≼ᴼ o′) (st : Flat A w) where
    private
      module L = FlatMap op f o st
      module L′ = FlatMap op f′ o′ st

    settle-≼ : L.settle ≼ L′.settle
    settle-≼ = readB-≼ λ d → readB-≼ λ n → readB-≼ λ q → when-≼ (d ∧ (n ≡ᵇ 0) ∧ null q) (complete≼ p)

    handOn-≼ : ∀ {v} (σ : w ≤ʷ v) r → L.handOn σ r ≼ L′.handOn σ r
    handOn-≼ σ nothing  = ≼-wk σ settle-≼
    handOn-≼ σ (just r) = ≼-refl (send r tt skipᴬ)

    lane-≼ : ∀ {v} (σ : w ≤ʷ v) c → L.lane σ c ≼ᴼ L′.lane σ c
    lane-≼ σ c = record
      { next≼ = next≼ (≼ᴼ-wk σ p)
      ; complete≼ = writeRef≼ (≼-pre (modifyB (Flat.active (wkFlat σ st)) pred) (readRef≼ {k = λ τ → L.handOn (σ ⨾ʷ τ)} {k′ = λ τ → L′.handOn (σ ⨾ʷ τ)} λ τ → handOn-≼ (σ ⨾ʷ τ)))
      ; closed≼ = closed≼ (≼ᴼ-wk σ p) }

    start-≼ : ∀ {l l′ : Subscribe B w} → l ≼ˢ l′ → L.start l ≼ L′.start l′
    start-≼ pl = ≼-bind (closed≼ p) λ cl → when-≼ (not cl) (≼-pre (modifyB (Flat.active st) suc) (newCut-≼ λ σ c →
      ≼-pre (modify (Flat.lanes (wkFlat σ st)) (λ τ cs → wkCut τ c ∷ cs)) (pl σ (guarded-≼ c (lane-≼ σ c)) λ τ u → attach-≼ (wkCut τ c) u)))

    dequeue-≼ : L.dequeue ≼ L′.dequeue
    dequeue-≼ = readB-≼ λ where
      []       → settle-≼
      (a ∷ as) → writeRef≼ (start-≼ (pf a))

    admit-≼ : ∀ op′ a → L.admit op′ a ≼ L′.admit op′ a
    admit-≼ (mergeᶠ nothing)  a = start-≼ (pf a)
    admit-≼ (mergeᶠ (just n)) a = readB-≼ λ c → ≼-if (c <ᵇ n) (start-≼ (pf a)) (≼-refl (modifyB (Flat.queue st) (_++ [ a ])))
    admit-≼ switchᶠ           a = ≼-pre L.killAll (start-≼ (pf a))
    admit-≼ exhaustᶠ          a = readB-≼ λ c → when-≼ (c ≡ᵇ 0) (start-≼ (pf a))

    run-≼ : ∀ (oc : Cut w) {s s′ : Subscribe A w} {k k′ : Kont w} → s ≼ˢ s′ → k ≼ᴷ k′ → L.run oc s k ≼ L′.run oc s′ k′
    run-≼ oc ps q = register≼ (λ _ → dequeue-≼) done≼ done≼ λ σ r → writeRef≼
      (ps σ (guarded-≼ (wkCut σ oc) (record
        { next≼ = λ a → ≼-wk σ (admit-≼ op a)
        ; complete≼ = writeRef≼ {r = Flat.outerDone (wkFlat σ st)} {a = true} (≼-wk σ settle-≼)
        ; closed≼ = closed≼ (≼ᴼ-wk σ p) }))
        λ τ u → ≼-then (attach-≼ (wkCut (σ ⨾ʷ τ) oc) u) (q (σ ⨾ʷ τ) (≼-refl (cut (wkCut (σ ⨾ʷ τ) oc) >>ᴬ wkAct (σ ⨾ʷ τ) L.killAll))))

  newFlat-≼ : ∀ {A w B} {k k′ : ∀ {v} → w ≤ʷ v → Flat A v → Act v B} → (∀ {v} (σ : w ≤ʷ v) st → k σ st ≼ k′ σ st) → newFlat k ≼ newFlat k′
  newFlat-≼ p = newRef≼ λ σ₁ a → newRef≼ λ σ₂ d → newRef≼ λ σ₃ q → newRef≼ λ σ₄ ls → newRef≼ λ σ₅ r → p _ _

  flatMap-≼ : ∀ {A B w} op {f f′ : A → Subscribe B w} {s s′ : Subscribe A w} → (∀ a → f a ≼ˢ f′ a) → s ≼ˢ s′
            → flatMapᴷ op f s ≼ˢ flatMapᴷ op f′ s′
  flatMap-≼ op {f} {f′} {s} {s′} pf ps ρ {o} {o′} p q = newFlat-≼ λ σ st → newCut-≼ λ τ oc →
    FlatMap-≼.run-≼ op {f = λ a → wkSub (ρ ⨾ʷ σ ⨾ʷ τ) (f a)} {f′ = λ a → wkSub (ρ ⨾ʷ σ ⨾ʷ τ) (f′ a)} (λ a → ≼ˢ-wk (ρ ⨾ʷ σ ⨾ʷ τ) (pf a))
      (≼ᴼ-wk (σ ⨾ʷ τ) p) (wkFlat τ st) oc (≼ˢ-wk (ρ ⨾ʷ σ ⨾ʷ τ) ps) (≼ᴷ-wk (σ ⨾ʷ τ) q)

  connect-≼ : ∀ {A B w} {s s′ : Subscribe A w} {b b′ : ∀ {v} → w ≤ʷ v → Subject A v → Subscribe B v}
            → s ≼ˢ s′ → (∀ {v} (σ : w ≤ʷ v) st → b σ st ≼ˢ b′ σ st) → connectᴷ s b ≼ˢ connectᴷ s′ b′
  connect-≼ ps pb ρ p q = newRef≼ λ σ subs → newRef≼ λ τ cl →
    pb (ρ ⨾ʷ σ ⨾ʷ τ) _ same (≼ᴼ-wk (σ ⨾ʷ τ) p) λ π {body} {body′} pbody →
      ps (ρ ⨾ʷ σ ⨾ʷ τ ⨾ʷ π) (record { next≼ = λ a → ≼-refl _ ; complete≼ = ≼-refl _ ; closed≼ = ≼-refl _ })
        λ υ u → q (σ ⨾ʷ τ ⨾ʷ π ⨾ʷ υ) (≼-then u (≼-wk υ pbody))

  join-≼ : ∀ {A w} (st : Subject A w) → joinᴷ st ≼ˢ joinᴷ st
  join-≼ st ρ p q = readB-≼ λ where
    true  → ≼-then (complete≼ p) (q same done≼)
    false → newRef≼ λ σ l → register≼ (λ a → readB-≼ λ b → when-≼ b (next≼ (≼ᴼ-wk σ p) a))
                                      (readB-≼ λ b → when-≼ b (complete≼ (≼ᴼ-wk σ p)))
                                      (readB-≼ λ b → ≼-if b (closed≼ (≼ᴼ-wk σ p)) done≼)
                                      λ τ sk → ≼-pre (modify (Subject.subscribers (wkSubject (ρ ⨾ʷ σ ⨾ʷ τ) st)) (λ π ss → ss ++ [ wkSink π sk ]))
                                                 (q (σ ⨾ʷ τ) (≼-refl (writeRef (wkR τ l) false skipᴬ)))

  defer-≼ : ∀ {Γ A w} (l : Later Timeline Γ A) (ρ : Env Γ w) → deferᴷ l ρ ≼ˢ deferᴷ l ρ
  defer-≼ l ρ σ p q = unfold≼ (next≼ p) (complete≼ p) (closed≼ p) (λ τ sk → q τ (send≼ done≼)) done≼

  ------------------------------------------------------------------------
  -- So is the compiler

  _≼ᵈ_ : Deferred → Deferred → Set₁
  d ≼ᵈ d′ = ∀ {Γ A w} (l : Later Timeline Γ A) (ρ : Env Γ w) → d l ρ ≼ˢ d′ l ρ

  compile-≼ : ∀ {d d′ : Deferred} → d ≼ᵈ d′ → ∀ {Γ A w} (o : Obs Timeline Γ A) (ρ : Env Γ w) → compileWith d o ρ ≼ˢ compileWith d′ o ρ
  compile-≼ pd (cold c)          ρ = via-≼ c
  compile-≼ pd empty             ρ = empty-≼
  compile-≼ pd (of xs)           ρ = of-≼ xs
  compile-≼ pd (map f s)         ρ = map-≼ f (compile-≼ pd s ρ)
  compile-≼ pd (scan f z s)      ρ = scan-≼ f z (compile-≼ pd s ρ)
  compile-≼ pd (takeWhile i p s) ρ = takeWhile-≼ i p (compile-≼ pd s ρ)
  compile-≼ pd (flatMap op f s)  ρ = flatMap-≼ op (λ a → compile-≼ pd (f a) ρ) (compile-≼ pd s ρ)
  compile-≼ pd (connect s b)     ρ = connect-≼ (compile-≼ pd s ρ) λ σ st → compile-≼ pd b (st ∷ᴬ wkEnv σ ρ)
  compile-≼ pd (connected i)     ρ = join-≼ (lookup ρ i)
  compile-≼ pd (defer l)         ρ = pd l ρ

  deferred-≼ : ∀ {n n′} → n Data.Nat.≤ n′ → deferredᴺ n ≼ᵈ deferredᴺ n′
  deferred-≼ Data.Nat.z≤n     l ρ σ p q = ⊥≼
  deferred-≼ (Data.Nat.s≤s p) l ρ = compile-≼ (deferred-≼ p) (Later.force l) ρ

  -- A deeper approximant of the compiler.
  compileᴺ-≼ : ∀ {n n′} → n Data.Nat.≤ n′ → ∀ {Γ A w} (o : Obs Timeline Γ A) (ρ : Env Γ w) → compileᴺ n o ρ ≼ˢ compileᴺ n′ o ρ
  compileᴺ-≼ p = compile-≼ (deferred-≼ p)

  -- The interpreter's own `defer`.
  compile-refl : ∀ {Γ A w} (o : Obs Timeline Γ A) (ρ : Env Γ w) → compile o ρ ≼ˢ compile o ρ
  compile-refl = compile-≼ defer-≼
