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
open import Data.List using (List; []; _∷_; _++_; [_]; null; length)
open import Data.List.Properties using (++-assoc; ++-identityʳ; length-++)
open import Data.Nat using (ℕ; zero; suc; pred; _<ᵇ_; _≡ᵇ_; _+_; _∸_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-suc)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_; _×_)
open import Data.List.Relation.Unary.All using (All; []; lookup) renaming (_∷_ to _∷ᴬ_)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import denotation.MonotonicList using (Timeline; ML; Burst∞; ML∞; Time; at; emit; stall; close; done; quiet; Pos; ix; last) renaming (sub to subᴾ)
open import denotation.Order using (Shows; ShowsIn; nil; at⁺; emit⁺; stall⁺; close⁺; _⊑_)
open import Tree using (Obs; Later; mergeᶠ; switchᶠ; exhaustᶠ; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import operation.AbstractObservable using (base; module Prims; module Run)
open import operation.PureObservable using (Pureᴾ; PureObs; Sink; Handle; Out; note; fin; same; new; _∋_; here; there; wk∋; cell; slot; play; module Pure)
  renaming (_⊑_ to _≤ʷ_; _⨾_ to _⨾ʷ_)

module Approx (R : Set) where
  open Prims (Pureᴾ R) using (wkSink)
  open Run (Pureᴾ R)
  open Kit
  open FlatKit
  open Pure R using (deferredᴺ; compileᴺ; Callbacks; Val; get; put; wkVal; wkAll; State; extend; Timer; wkTimer; mapList; insert; Res; res;
                     M; ret; then; bind; shift; spent; spend; unlessSpent; hereᴾ; gotoᴾ; cascade; module Play; Pureᴿ; runᴺ; loopᴺ; start; recorder; observe;
                     frames; within; inFrame; later; ending; stalls; sameFrame; endOf; runPure; cutOff)

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
    here≼      : ∀ {k k′ : Pos → Act w B} → (∀ p → k p ≼ k′ p) → here k ≼ here k′
    goto≼      : ∀ {p k k′} → k ≼ k′ → goto p k ≼ goto p k′
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
  ≼-refl (here k)               = here≼ λ p → ≼-refl (k p)
  ≼-refl (goto p k)             = goto≼ (≼-refl k)
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
  ≼-wk ρ (here≼ p)                = here≼ λ q → ≼-wk ρ (p q)
  ≼-wk ρ (goto≼ p)                = goto≼ (≼-wk ρ p)
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
  ≼-bind (here≼ p)                q = here≼ λ x → ≼-bind (p x) q
  ≼-bind (goto≼ p)                q = goto≼ (≼-bind p q)
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
  empty-≼ σ p q = ≼-then (here≼ λ r → goto≼ {p = r ++ [ last ]} (complete≼ p)) (q same done≼)

  emitAll-≼ : ∀ {A w} {o o′ : Observer A w} → o ≼ᴼ o′ → ∀ r i xs → emitAll o r i xs ≼ emitAll o′ r i xs
  emitAll-≼ p r i []       = goto≼ (complete≼ p)
  emitAll-≼ p r i (x ∷ xs) = ≼-bind (closed≼ p) λ c → when-≼ (not c) (≼-then (goto≼ (next≼ p x)) (emitAll-≼ p r (suc i) xs))

  of-≼ : ∀ {A w} (xs : List A) → ofᴷ {w = w} xs ≼ˢ ofᴷ xs
  of-≼ xs σ p q = ≼-then (here≼ λ r → emitAll-≼ p r 0 xs) (q same done≼)

  map-≼ : ∀ {A B w} (f : A → B) {s s′ : Subscribe A w} → s ≼ˢ s′ → mapᴷ f s ≼ˢ mapᴷ f s′
  map-≼ f ps σ p q = ps σ (record { next≼ = λ a → next≼ p (f a) ; complete≼ = complete≼ p ; closed≼ = closed≼ p }) q

  scan-≼ : ∀ {A B w} (f : B → A → B) z {s s′ : Subscribe A w} → s ≼ˢ s′ → scanᴷ f z s ≼ˢ scanᴷ f z s′
  scan-≼ f z ps σ p q = newRef≼ λ τ r →
    ps (σ ⨾ʷ τ) (record { next≼ = λ a → readB-≼ λ b → writeRef≼ (next≼ (≼ᴼ-wk τ p) (f b a))
                        ; complete≼ = complete≼ (≼ᴼ-wk τ p) ; closed≼ = closed≼ (≼ᴼ-wk τ p) }) (≼ᴷ-wk τ q)

  takeWhile-≼ : ∀ {A w} i (f : A → Bool) {s s′ : Subscribe A w} → s ≼ˢ s′ → takeWhileᴷ i f s ≼ˢ takeWhileᴷ i f s′
  takeWhile-≼ i f ps σ p q = newCut-≼ λ τ c →
    ps (σ ⨾ʷ τ) (guarded-≼ c (record
      { next≼ = λ a → here≼ λ r → ≼-if (f a) (next≼ (≼ᴼ-wk τ p) a)
                        (≼-then (≼-then (when-≼ i (next≼ (≼ᴼ-wk τ p) a)) (goto≼ {p = r ++ [ last ]} (complete≼ (≼ᴼ-wk τ p)))) (≼-refl (cut c)))
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
    start-≼ pl = here≼ λ r → ≼-bind (closed≼ p) λ cl → when-≼ (not cl) (≼-pre (modifyB (Flat.active st) suc) (newCut-≼ λ σ c →
      ≼-pre (modify (Flat.lanes (wkFlat σ st)) (λ τ cs → wkCut τ c ∷ cs)) (goto≼ {p = r ++ [ ix 1 ]} (pl σ (guarded-≼ c (lane-≼ σ c)) λ τ u → attach-≼ (wkCut τ c) u))))

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
  connect-≼ ps pb ρ p q = here≼ λ r → newRef≼ λ σ subs → newRef≼ λ τ cl →
    goto≼ {p = r ++ [ ix 0 ]} (pb (ρ ⨾ʷ σ ⨾ʷ τ) _ same (≼ᴼ-wk (σ ⨾ʷ τ) p) λ π {body} {body′} pbody →
      goto≼ {p = r ++ [ ix 1 ]} (ps (ρ ⨾ʷ σ ⨾ʷ τ ⨾ʷ π) (record { next≼ = λ a → ≼-refl _ ; complete≼ = ≼-refl _ ; closed≼ = ≼-refl _ })
        λ υ u → q (σ ⨾ʷ τ ⨾ʷ π ⨾ʷ υ) (≼-then u (≼-wk υ pbody))))

  join-≼ : ∀ {A w} (st : Subject A w) → joinᴷ st ≼ˢ joinᴷ st
  join-≼ st ρ p q = here≼ λ j → readB-≼ λ where
    true  → ≼-then (goto≼ {p = j ++ [ last ]} (complete≼ p)) (q same done≼)
    false → newRef≼ λ σ l → register≼ (λ a → readB-≼ λ b → when-≼ b (next≼ (≼ᴼ-wk σ p) a))
                                      (readB-≼ λ b → when-≼ b (complete≼ (≼ᴼ-wk σ p)))
                                      (readB-≼ λ b → ≼-if b (closed≼ (≼ᴼ-wk σ p)) done≼)
                                      λ τ sk → ≼-pre (modify (Subject.subscribers (wkSubject (ρ ⨾ʷ σ ⨾ʷ τ) st)) (λ π ss → ss ++ [ (wkSink π sk , j) ]))
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
  deferred-≼ {n′ = n′} Data.Nat.z≤n l ρ = ⊥-≼ {s = deferredᴺ n′ l ρ}
  deferred-≼ (Data.Nat.s≤s p) l ρ σ po pk = here≼ λ r → goto≼ {p = r ++ [ ix 1 ]} (compile-≼ (deferred-≼ p) (Later.force l) ρ σ po pk)

  -- A deeper approximant of the compiler.
  compileᴺ-≼ : ∀ {n n′} → n Data.Nat.≤ n′ → ∀ {Γ A w} (o : Obs Timeline Γ A) (ρ : Env Γ w) → compileᴺ n o ρ ≼ˢ compileᴺ n′ o ρ
  compileᴺ-≼ p = compile-≼ (deferred-≼ p)

  -- The interpreter's own `defer`.
  compile-refl : ∀ {Γ A w} (o : Obs Timeline Γ A) (ρ : Env Γ w) → compile o ρ ≼ˢ compile o ρ
  compile-refl = compile-≼ defer-≼

  ------------------------------------------------------------------------
  -- The root's record only grows, and is frozen once the root has ended

  -- A mark per value, and one more for the completion.
  extra : Bool → ℕ → ℕ
  extra false m = m
  extra true  m = suc m

  -- The marks and the values grow together.
  data GrowsAt : Bool → List Pos → List (Time × R) → Bool → List Pos → List (Time × R) → Set where
    open≈ : ∀ {ms xs ns ys e} ps zs → ns ≡ ms ++ ps → ys ≡ xs ++ zs → length ps ≡ extra e (length zs) → GrowsAt false ms xs e ns ys
    shut≈ : ∀ {ms xs} → GrowsAt true ms xs true ms xs

  Grows : ∀ {h v} → State h → State v → Set
  Grows s s′ = GrowsAt (State.ended s) (State.marks s) (State.log s) (State.ended s′) (State.marks s′) (State.log s′)

  growsAt-refl : ∀ e ms xs → GrowsAt e ms xs e ms xs
  growsAt-refl false ms xs = open≈ [] [] (sym (++-identityʳ ms)) (sym (++-identityʳ xs)) refl
  growsAt-refl true  ms xs = shut≈

  extra-+ : ∀ e a b → a + extra e b ≡ extra e (a + b)
  extra-+ false a b = refl
  extra-+ true  a b = +-suc a b

  growsAt-trans : ∀ {a b c ms xs ns ys os zs} → GrowsAt a ms xs b ns ys → GrowsAt b ns ys c os zs → GrowsAt a ms xs c os zs
  growsAt-trans {c = c} (open≈ ps zs refl refl l) (open≈ ps′ zs′ refl refl l′) =
    open≈ (ps ++ ps′) (zs ++ zs′) (++-assoc _ ps ps′) (++-assoc _ zs zs′)
      (trans (length-++ ps) (trans (cong₂ _+_ l l′) (trans (extra-+ c (length zs) (length zs′)) (cong (extra c) (sym (length-++ zs))))))
  growsAt-trans (open≈ ps zs p q l) shut≈ = open≈ ps zs p q l
  growsAt-trans shut≈               shut≈ = shut≈

  ------------------------------------------------------------------------
  -- Two heaps alike, but where the left's callbacks diverge

  record CbRel {A h} (c c′ : Callbacks A h) : Set₁ where
    field
      onNext≼     : ∀ a → Callbacks.onNext c a ≼ Callbacks.onNext c′ a
      onComplete≼ : Callbacks.onComplete c ≼ Callbacks.onComplete c′
      isClosed≼   : Callbacks.isClosed c ≼ Callbacks.isClosed c′

  ValRel : ∀ {h} k → Val h k → Val h k → Set₁
  ValRel (cell t) x y   = x ≡ y
  ValRel (slot A) c c′  = CbRel c c′
  ValRel play     x y   = x ≡ y

  valRel-refl : ∀ {h} k (x : Val h k) → ValRel k x x
  valRel-refl (cell t) x = refl
  valRel-refl (slot A) c = record { onNext≼ = λ a → ≼-refl _ ; onComplete≼ = ≼-refl _ ; isClosed≼ = ≼-refl _ }
  valRel-refl play     x = refl

  valRel-wk : ∀ {h v} k (ρ : h ≤ʷ v) {x y : Val h k} → ValRel k x y → ValRel k (wkVal k ρ x) (wkVal k ρ y)
  valRel-wk (cell t) ρ refl = refl
  valRel-wk (slot A) ρ q    = record { onNext≼ = λ a → ≼-wk ρ (CbRel.onNext≼ q a) ; onComplete≼ = ≼-wk ρ (CbRel.onComplete≼ q)
                                     ; isClosed≼ = ≼-wk ρ (CbRel.isClosed≼ q) }
  valRel-wk play     ρ q    = q

  data HeapRel {h} : ∀ {w} → All (Val h) w → All (Val h) w → Set₁ where
    []  : HeapRel [] []
    _∷_ : ∀ {k w x y} {xs ys : All (Val h) w} → ValRel k x y → HeapRel xs ys → HeapRel (x ∷ᴬ xs) (y ∷ᴬ ys)

  heapRel-refl : ∀ {h w} (xs : All (Val h) w) → HeapRel xs xs
  heapRel-refl []                  = []
  heapRel-refl (_∷ᴬ_ {x = k} x xs) = valRel-refl k x ∷ heapRel-refl xs

  get-rel : ∀ {h w k} {xs ys : All (Val h) w} → HeapRel xs ys → (i : w ∋ k) → ValRel k (get xs i) (get ys i)
  get-rel (q ∷ qs) here      = q
  get-rel (q ∷ qs) (there i) = get-rel qs i

  put-rel : ∀ {h w k} {xs ys : All (Val h) w} → HeapRel xs ys → (i : w ∋ k) {y y′ : Val h k} → ValRel k y y′
          → HeapRel (put xs i y) (put ys i y′)
  put-rel (q ∷ qs) here      p = p ∷ qs
  put-rel (q ∷ qs) (there i) p = q ∷ put-rel qs i p

  wkAll-rel : ∀ {h v w} {xs ys : All (Val h) w} (ρ : h ≤ʷ v) → HeapRel xs ys → HeapRel (wkAll ρ xs) (wkAll ρ ys)
  wkAll-rel ρ []                 = []
  wkAll-rel ρ (_∷_ {k = k} q qs) = valRel-wk k ρ q ∷ wkAll-rel ρ qs

  record StRel {h} (s s′ : State h) : Set₁ where
    constructor stRel
    field
      heap≈   : HeapRel (State.heap s) (State.heap s′)
      clock≡  : State.clock s ≡ State.clock s′
      timers≡ : State.timers s ≡ State.timers s′
      log≡    : State.log s ≡ State.log s′
      ended≡  : State.ended s ≡ State.ended s′
      pos≡    : State.pos s ≡ State.pos s′
      marks≡  : State.marks s ≡ State.marks s′
  open StRel

  stRel-refl : ∀ {h} (s : State h) → StRel s s
  stRel-refl s = record { heap≈ = heapRel-refl (State.heap s) ; clock≡ = refl ; timers≡ = refl ; log≡ = refl ; ended≡ = refl ; pos≡ = refl ; marks≡ = refl }

  extend-rel : ∀ {h k} {s s′ : State h} {x y : Val (k ∷ h) k} → StRel s s′ → ValRel k x y → StRel (extend s x) (extend s′ y)
  extend-rel q p = record { heap≈ = p ∷ wkAll-rel new (heap≈ q) ; clock≡ = clock≡ q ; timers≡ = cong (mapList (wkTimer new)) (timers≡ q)
                          ; log≡ = log≡ q ; ended≡ = ended≡ q ; pos≡ = pos≡ q ; marks≡ = marks≡ q }

  grows-from : ∀ {h v} {s s′ : State h} {s″ : State v} → StRel s s′ → Grows s′ s″ → Grows s s″
  grows-from {s″ = s″} q g =
    subst (λ e → GrowsAt e _ _ (State.ended s″) (State.marks s″) (State.log s″)) (sym (ended≡ q))
      (subst₂ (λ m l → GrowsAt _ m l (State.ended s″) (State.marks s″) (State.log s″)) (sym (marks≡ q)) (sym (log≡ q)) g)

  private
    cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} (f : A → B → C → D) {x x′ y y′ z z′}
          → x ≡ x′ → y ≡ y′ → z ≡ z′ → f x y z ≡ f x′ y′ z′
    cong₃ f refl refl refl = refl

  ------------------------------------------------------------------------
  -- Two runs alike, or the left cut short where the right goes on

  data ResRel {h B} : Res h B → Res h B → Set₁ where
    lock  : ∀ {v} {σ : h ≤ʷ v} {s s′ : State v} {b} → StRel s s′ → ResRel (res σ s b) (res σ s′ b)
    short : ∀ {v v′} {σ : h ≤ʷ v} {σ′ : h ≤ʷ v′} {s : State v} {s′ : State v′} {b′}
          → Grows s s′ → ResRel (res σ s nothing) (res σ′ s′ b′)

  Sim : ∀ {w B} → M w B → M w B → Set₁
  Sim {w} m m′ = ∀ {h} (σ : w ≤ʷ h) {s s′ : State h} → StRel s s′ → ResRel (m σ s) (m′ σ s′)

  -- A record, so that a `Grower m` names its `m`.
  record Grower {w B} (m : M w B) : Set₁ where
    constructor grows
    field grow : ∀ {h} (σ : w ≤ʷ h) (s : State h) → Grows s (Res.state (m σ s))
  open Grower

  RunM : Set₁
  RunM = ∀ {w B} → Act w B → M w B

  SimRun : RunM → RunM → Set₁
  SimRun run run′ = ∀ {w B} {a a′ : Act w B} → a ≼ a′ → Sim (run a) (run′ a′)

  GrowRun : RunM → Set₁
  GrowRun run = ∀ {w B} (a : Act w B) → Grower (run a)

  shift-rel : ∀ {h v B} (ρ : h ≤ʷ v) {x x′ : Res v B} → ResRel x x′ → ResRel (shift ρ x) (shift ρ x′)
  shift-rel ρ (lock q)  = lock q
  shift-rel ρ (short g) = short g

  then-grow : ∀ {h A B} {g : A → M h B} (s : State h) (x : Res h A) → Grows s (Res.state x) → (∀ a → Grower (g a))
            → Grows s (Res.state (then g x))
  then-grow s (res σ t (just a)) p gg = growsAt-trans p (grow (gg a) σ t)
  then-grow s (res σ t nothing)  p gg = p

  then-rel : ∀ {h A B} {g g′ : A → M h B} {x x′ : Res h A} → ResRel x x′ → (∀ a → Sim (g a) (g′ a)) → (∀ a → Grower (g′ a))
           → ResRel (then g x) (then g′ x′)
  then-rel (lock {σ = σ} {b = just a} q)                   pg gg = shift-rel σ (pg a σ q)
  then-rel (lock {b = nothing} q)                          pg gg = lock q
  then-rel (short {σ′ = σ′} {s′ = s′} {b′ = just a} p) pg gg = short (growsAt-trans p (grow (gg a) σ′ s′))
  then-rel (short {b′ = nothing} p)                        pg gg = short p

  bind-sim : ∀ {w A B} {m m′ : M w A} {f f′ : A → M w B} → Sim m m′ → (∀ a → Sim (f a) (f′ a)) → (∀ a → Grower (f′ a))
           → Sim (bind m f) (bind m′ f′)
  bind-sim {f = f} {f′} pm pf gf σ q = then-rel {g = λ a τ → f a (σ ⨾ʷ τ)} {g′ = λ a τ → f′ a (σ ⨾ʷ τ)} (pm σ q)
                                         (λ a τ → pf a (σ ⨾ʷ τ)) (λ a → grows λ τ → grow (gf a) (σ ⨾ʷ τ))

  bind-grow : ∀ {w A B} {m : M w A} {f : A → M w B} → Grower m → (∀ a → Grower (f a)) → Grower (bind m f)
  bind-grow {m = m} {f} gm gf = grows λ σ s → then-grow {g = λ a τ → f a (σ ⨾ʷ τ)} s (m σ s) (grow gm σ s) (λ a → grows λ τ → grow (gf a) (σ ⨾ʷ τ))

  ret-sim : ∀ {w B} (b : B) → Sim {w} (ret b) (ret b)
  ret-sim b σ q = lock q

  ret-grow : ∀ {w B} (b : B) → Grower {w} (ret b)
  ret-grow b = grows λ σ s → growsAt-refl _ _ _

  diverge-sim : ∀ {w B} {m′ : M w B} → Grower m′ → Sim (λ σ s → res same s nothing) m′
  diverge-sim {m′ = m′} g σ {s} {s′} q = short (grows-from {s = s} {s′} {Res.state (m′ σ s′)} q (grow g σ s′))

  ------------------------------------------------------------------------
  -- The runtime's own steps

  spent-sim : ∀ {w} (hd : Handle w) → Sim (spent hd) (spent hd)
  spent-sim hd σ {s} {s′} q = subst (λ y → ResRel (res same s (just (lower (get (State.heap s) (wk∋ σ hd))))) (res same s′ (just (lower y))))
                                    (get-rel (heap≈ q) (wk∋ σ hd)) (lock q)

  spent-grow : ∀ {w} (hd : Handle w) → Grower (spent hd)
  spent-grow hd = grows λ σ s → growsAt-refl _ _ _

  spend-sim : ∀ {w} (hd : Handle w) → Sim (spend hd) (spend hd)
  spend-sim hd σ q = lock (stRel (put-rel (heap≈ q) (wk∋ σ hd) refl) (clock≡ q) (timers≡ q) (log≡ q) (ended≡ q) (pos≡ q) (marks≡ q))

  spend-grow : ∀ {w} (hd : Handle w) → Grower (spend hd)
  spend-grow hd = grows λ σ s → growsAt-refl _ _ _

  unless-sim : ∀ {w} (hd : Handle w) {m m′ : M w ⊤} → Sim m m′ → Grower m′ → Sim (unlessSpent hd m) (unlessSpent hd m′)
  unless-sim hd {m} {m′} pm gm = bind-sim {f = λ b → if b then ret tt else m} {f′ = λ b → if b then ret tt else m′} (spent-sim hd) (λ { true → ret-sim tt ; false → pm }) (λ { true → ret-grow tt ; false → gm })

  unless-grow : ∀ {w} (hd : Handle w) {m : M w ⊤} → Grower m → Grower (unlessSpent hd m)
  unless-grow hd {m} gm = bind-grow {f = λ b → if b then ret tt else m} (spent-grow hd) (λ { true → ret-grow tt ; false → gm })

  here-sim : ∀ {w B} {k k′ : Pos → M w B} → (∀ p → Sim (k p) (k′ p)) → Sim (hereᴾ k) (hereᴾ k′)
  here-sim {k = k} {k′} pk σ {s} {s′} q = subst (λ x → ResRel (k (State.pos s) σ s) (k′ x σ s′)) (pos≡ q) (pk (State.pos s) σ q)

  here-grow : ∀ {w B} {k : Pos → M w B} → (∀ p → Grower (k p)) → Grower (hereᴾ k)
  here-grow gk = grows λ σ st → grow (gk (State.pos st)) σ st

  goto-sim : ∀ {w} p → Sim {w} (gotoᴾ p) (gotoᴾ p)
  goto-sim p σ q = lock (stRel (heap≈ q) (clock≡ q) (timers≡ q) (log≡ q) (ended≡ q) refl (marks≡ q))

  goto-grow : ∀ {w} p → Grower {w} (gotoᴾ p)
  goto-grow p = grows λ σ st → growsAt-refl _ _ _

  note-grows : ∀ e ms xs p y → GrowsAt e ms xs e (if e then ms else ms ++ [ p ]) (if e then xs else xs ++ [ y ])
  note-grows true  ms xs p y = shut≈
  note-grows false ms xs p y = open≈ [ p ] [ y ] refl refl refl

  fin-grows : ∀ e ms xs p → GrowsAt e ms xs true (if e then ms else ms ++ [ p ]) xs
  fin-grows true  ms xs p = shut≈
  fin-grows false ms xs p = open≈ [ p ] [] refl (sym (++-identityʳ xs)) refl

  -- Playing colds, on any budget, over any runner of stored callbacks.
  module Grow (n : ℕ) {run : RunM} (gr : GrowRun run) where
    open Play n run

    runCb-grow : ∀ {w A B} (s : Sink w A) (f : ∀ {h} → Callbacks A h → Act h B) → Grower (runCb s f)
    runCb-grow s f = grows λ σ st → grow (gr _) same st

    closed-grow : ∀ {w A} (s : Sink w A) (hd : Handle w) → Grower (closedᴾ s hd)
    closed-grow s hd = bind-grow {f = λ b → if b then ret true else runCb s Callbacks.isClosed} (spent-grow hd) λ { true → ret-grow true ; false → runCb-grow s Callbacks.isClosed }

    send-grow : ∀ {w A} (s : Sink w A) a → Grower (sendᴾ s a)
    send-grow s a = runCb-grow s λ cb → Callbacks.onNext cb a

    finish-grow : ∀ {w A} (s : Sink w A) → Grower (finishᴾ s)
    finish-grow s = runCb-grow s Callbacks.onComplete

    schedule-grow : ∀ {w A} (s : Sink w A) (hd : Handle w) now e m → Grower (schedule s hd now e m)
    schedule-grow s hd now e done     = unless-grow hd (bind-grow (spend-grow hd) λ _ → bind-grow (goto-grow e) λ _ → finish-grow s)
    schedule-grow s hd now e quiet    = ret-grow tt
    schedule-grow s hd now e (at t b) = grows λ σ st → growsAt-refl _ _ _

    mutual
      burst-grow : ∀ f {w A} (s : Sink w A) (hd : Handle w) t r i b → Grower (burst f s hd t r i b)
      burst-grow zero    s hd t r i b = grows λ σ st → growsAt-refl _ _ _
      burst-grow (suc f) s hd t r i b = bind-grow {f = λ c → if c then ret tt else stepᴾ f s hd t r i b} (closed-grow s hd) λ { true → ret-grow tt ; false → step-grow f s hd t r i b }

      step-grow : ∀ f {w A} (s : Sink w A) (hd : Handle w) t r i b → Grower (stepᴾ f s hd t r i b)
      step-grow f s hd t r i (emit a k) = bind-grow (unless-grow hd (bind-grow (goto-grow (r ++ [ ix i ])) λ _ → send-grow s a)) λ _ →
                                            unless-grow hd (burst-grow f s hd t r (suc i) (Burst∞.force k))
      step-grow f s hd t r i (stall k)  = burst-grow f s hd t r (suc i) (Burst∞.force k)
      step-grow f s hd t r i (close k)  = schedule-grow s hd t (r ++ [ last ]) (ML∞.force k)

    first-grow : ∀ {w A} (s : Sink w A) (hd : Handle w) m → Grower (first s hd m)
    first-grow s hd (at zero b)    = here-grow λ r → burst-grow n s hd 0 r 0 b
    first-grow s hd (at (suc t) b) = here-grow λ r → schedule-grow s hd 0 (r ++ [ last ]) (at (suc t) b)
    first-grow s hd done           = here-grow λ r → schedule-grow s hd 0 (r ++ [ last ]) done
    first-grow s hd quiet          = here-grow λ r → schedule-grow s hd 0 (r ++ [ last ]) quiet

    fire-grow : ∀ {h} ts (st : State h) → Grows st (Res.state (fire ts st))
    fire-grow []        st = growsAt-refl _ _ _
    fire-grow (tm ∷ ts) st = then-grow {g = λ _ _ st′ → res same st′ (just true)} st
      (unlessSpent (Timer.handle tm) (burst n (Timer.sink tm) (Timer.handle tm) (Timer.at′ tm) (cascade tm) 0 (Timer.frame tm)) same
        (record st { clock = Timer.due tm ; timers = ts ; pos = cascade tm }))
      (grow (unless-grow (Timer.handle tm) (burst-grow n (Timer.sink tm) (Timer.handle tm) (Timer.at′ tm) (cascade tm) 0 (Timer.frame tm))) same
        (record st { clock = Timer.due tm ; timers = ts ; pos = cascade tm }))
      (λ _ → grows λ _ _ → growsAt-refl _ _ _)

    next-grow : ∀ {w} → Grower {w} (nextᴾ {w})
    next-grow = grows λ σ st → fire-grow (State.timers st) st

    interpret-grow : ∀ {w B} (a : Act w B) → Grower (Engine.interpret (Pureᴿ n) run a)
    interpret-grow (done b)               = ret-grow b
    interpret-grow (newRef t a k)        = grows λ σ st → grow (interpret-grow (k (σ ⨾ʷ new) here)) same (extend st (lift (wkEl t (σ ⨾ʷ new) a)))
    interpret-grow (readRef r k)         = grows λ σ st → grow (interpret-grow (k σ (lower (get (State.heap st) (wk∋ σ r))))) same st
    interpret-grow (writeRef r a k)       = bind-grow {m = Runtime.writeRefᴿ (Pureᴿ n) r a} (grows λ σ st → growsAt-refl _ _ _) λ _ → interpret-grow k
    interpret-grow (register nx c x k)   = grows λ σ st → grow (interpret-grow (k (σ ⨾ʷ new) here)) same (extend st _)
    interpret-grow (send s a k)           = bind-grow (send-grow s a) λ _ → interpret-grow k
    interpret-grow (finish s k)           = bind-grow (finish-grow s) λ _ → interpret-grow k
    interpret-grow (startCold c s k) = grows λ σ st →
      grow (bind-grow (first-grow (wk∋ new (wk∋ σ s)) here (lower c)) (λ _ → interpret-grow (k (σ ⨾ʷ new) here))) same (extend st (lift false))
    interpret-grow (stop h k)             = bind-grow (spend-grow h) λ _ → interpret-grow k
    interpret-grow (eff (note a) k)       = bind-grow {m = Runtime.effᴿ (Pureᴿ n) (note a)} (grows λ σ st → note-grows (State.ended st) (State.marks st) (State.log st) (State.pos st) (State.clock st , a)) λ x → interpret-grow (k x)
    interpret-grow (eff fin k)            = bind-grow {m = Runtime.effᴿ (Pureᴿ n) fin} (grows λ σ st → fin-grows (State.ended st) (State.marks st) (State.log st) (State.pos st)) λ x → interpret-grow (k x)
    interpret-grow (here k)               = here-grow λ p → interpret-grow (k p)
    interpret-grow (goto p k)             = bind-grow {m = Runtime.gotoᴿ (Pureᴿ n) p} (goto-grow p) λ _ → interpret-grow k
    interpret-grow diverge                = grows λ σ st → growsAt-refl _ _ _
    interpret-grow (unfold l e nx c x k m) = bind-grow (gr _) λ _ → interpret-grow m

  -- Two budgets, two runners of stored callbacks, in lockstep.
  module Lockstep {n n′ : ℕ} (n≤ : n ≤ n′) {run run′ : RunM} (sr : SimRun run run′) (gr′ : GrowRun run′) where
    private
      module L  = Play n run
      module L′ = Play n′ run′
      module G  = Grow n′ gr′

    runCb-sim : ∀ {w A B} (s : Sink w A) {f f′ : ∀ {h} → Callbacks A h → Act h B}
              → (∀ {h} {c c′ : Callbacks A h} → CbRel c c′ → f c ≼ f′ c′) → Sim (L.runCb s f) (L′.runCb s f′)
    runCb-sim s pf σ q = sr (pf (get-rel (heap≈ q) (wk∋ σ s))) same q

    closed-sim : ∀ {w A} (s : Sink w A) (hd : Handle w) → Sim (L.closedᴾ s hd) (L′.closedᴾ s hd)
    closed-sim s hd = bind-sim {f = λ b → if b then ret true else L.runCb s Callbacks.isClosed} {f′ = λ b → if b then ret true else L′.runCb s Callbacks.isClosed} (spent-sim hd) (λ { true → ret-sim true ; false → runCb-sim s λ p → CbRel.isClosed≼ p })
                        (λ { true → ret-grow true ; false → G.runCb-grow s Callbacks.isClosed })

    send-sim : ∀ {w A} (s : Sink w A) a → Sim (L.sendᴾ s a) (L′.sendᴾ s a)
    send-sim s a = runCb-sim s λ p → CbRel.onNext≼ p a

    finish-sim : ∀ {w A} (s : Sink w A) → Sim (L.finishᴾ s) (L′.finishᴾ s)
    finish-sim s = runCb-sim s λ p → CbRel.onComplete≼ p

    schedule-sim : ∀ {w A} (s : Sink w A) (hd : Handle w) now e m → Sim (L.schedule s hd now e m) (L′.schedule s hd now e m)
    schedule-sim s hd now e done     = unless-sim hd (bind-sim (spend-sim hd) (λ _ → bind-sim (goto-sim e) (λ _ → finish-sim s) (λ _ → G.finish-grow s))
                                                               (λ _ → bind-grow (goto-grow e) λ _ → G.finish-grow s))
                                         (bind-grow (spend-grow hd) λ _ → bind-grow (goto-grow e) λ _ → G.finish-grow s)
    schedule-sim s hd now e quiet    = ret-sim tt
    schedule-sim s hd now e (at t b) = λ σ q → lock (stRel (heap≈ q) (clock≡ q) (cong₂ (λ c ts → insert (record
      { due = c + (t ∸ now) ; sink = wk∋ σ s ; handle = wk∋ σ hd ; at′ = t ; from = e ; frame = b }) ts) (clock≡ q) (timers≡ q)) (log≡ q) (ended≡ q) (pos≡ q) (marks≡ q))

    mutual
      burst-sim : ∀ {f f′} → f ≤ f′ → ∀ {w A} (s : Sink w A) (hd : Handle w) t r i b → Sim (L.burst f s hd t r i b) (L′.burst f′ s hd t r i b)
      burst-sim {f′ = f′} z≤n s hd t r i b = diverge-sim (G.burst-grow f′ s hd t r i b)
      burst-sim {f′ = suc f′} (s≤s p) s hd t r i b =
        bind-sim {f = λ c → if c then ret tt else L.stepᴾ _ s hd t r i b} {f′ = λ c → if c then ret tt else L′.stepᴾ f′ s hd t r i b}
                 (closed-sim s hd) (λ { true → ret-sim tt ; false → step-sim p s hd t r i b })
                 (λ { true → ret-grow tt ; false → G.step-grow f′ s hd t r i b })

      step-sim : ∀ {f f′} → f ≤ f′ → ∀ {w A} (s : Sink w A) (hd : Handle w) t r i b → Sim (L.stepᴾ f s hd t r i b) (L′.stepᴾ f′ s hd t r i b)
      step-sim {f′ = f′} p s hd t r i (emit a k) =
        bind-sim (unless-sim hd (bind-sim (goto-sim (r ++ [ ix i ])) (λ _ → send-sim s a) (λ _ → G.send-grow s a))
                                (bind-grow (goto-grow (r ++ [ ix i ])) λ _ → G.send-grow s a))
                 (λ _ → unless-sim hd (burst-sim p s hd t r (suc i) (Burst∞.force k)) (G.burst-grow f′ s hd t r (suc i) (Burst∞.force k)))
                 (λ _ → unless-grow hd (G.burst-grow f′ s hd t r (suc i) (Burst∞.force k)))
      step-sim p s hd t r i (stall k) = burst-sim p s hd t r (suc i) (Burst∞.force k)
      step-sim p s hd t r i (close k) = schedule-sim s hd t (r ++ [ last ]) (ML∞.force k)

    first-sim : ∀ {w A} (s : Sink w A) (hd : Handle w) m → Sim (L.first s hd m) (L′.first s hd m)
    first-sim s hd (at zero b)    = here-sim λ r → burst-sim n≤ s hd 0 r 0 b
    first-sim s hd (at (suc t) b) = here-sim λ r → schedule-sim s hd 0 (r ++ [ last ]) (at (suc t) b)
    first-sim s hd done           = here-sim λ r → schedule-sim s hd 0 (r ++ [ last ]) done
    first-sim s hd quiet          = here-sim λ r → schedule-sim s hd 0 (r ++ [ last ]) quiet

    fire-sim : ∀ {h} ts {s s′ : State h} → StRel s s′ → ResRel (L.fire ts s) (L′.fire ts s′)
    fire-sim []        q = lock q
    fire-sim (tm ∷ ts) q = then-rel {g = λ _ _ st′ → res same st′ (just true)} {g′ = λ _ _ st′ → res same st′ (just true)}
      (unless-sim (Timer.handle tm) (burst-sim n≤ (Timer.sink tm) (Timer.handle tm) (Timer.at′ tm) (cascade tm) 0 (Timer.frame tm))
                  (G.burst-grow n′ (Timer.sink tm) (Timer.handle tm) (Timer.at′ tm) (cascade tm) 0 (Timer.frame tm))
                  same (stRel (heap≈ q) refl refl (log≡ q) (ended≡ q) refl (marks≡ q)))
      (λ _ _ q′ → lock q′) (λ _ → grows λ _ _ → growsAt-refl _ _ _)

    next-sim : ∀ {w} → Sim {w} (L.nextᴾ {w}) (L′.nextᴾ {w})
    next-sim σ {s} {s′} q = subst (λ ts → ResRel (L.fire (State.timers s) s) (L′.fire ts s′)) (timers≡ q) (fire-sim (State.timers s) q)

    private
      I  = Engine.interpret (Pureᴿ n) run
      I′ = Engine.interpret (Pureᴿ n′) run′

    interpret-sim : ∀ {w B} {a a′ : Act w B} → a ≼ a′ → Sim (I a) (I′ a′)
    interpret-sim {a′ = a′} ⊥≼ = diverge-sim (Grow.interpret-grow n′ gr′ a′)
    interpret-sim done≼ = ret-sim _
    interpret-sim (newRef≼ p) σ q = shift-rel new (interpret-sim (p (σ ⨾ʷ new) here) same (extend-rel q refl))
    interpret-sim (readRef≼ {r = r} {k = k} {k′ = k′} p) σ {s} {s′} q =
      subst (λ y → ResRel (I (k σ (lower (get (State.heap s) (wk∋ σ r)))) same s) (I′ (k′ σ (lower y)) same s′))
            (get-rel (heap≈ q) (wk∋ σ r)) (interpret-sim (p σ _) same q)
    interpret-sim (writeRef≼ {r = r} {a = a} {k′ = k′} p) =
      bind-sim {m = Runtime.writeRefᴿ (Pureᴿ n) r a} {m′ = Runtime.writeRefᴿ (Pureᴿ n′) r a} (λ σ q → lock (stRel (put-rel (heap≈ q) (wk∋ σ r) refl) (clock≡ q) (timers≡ q) (log≡ q) (ended≡ q) (pos≡ q) (marks≡ q))) (λ _ → interpret-sim p)
               (λ _ → Grow.interpret-grow n′ gr′ k′)
    interpret-sim (register≼ pn pc px pk) σ q = shift-rel new (interpret-sim (pk (σ ⨾ʷ new) here) same (extend-rel q (record
      { onNext≼ = λ a → ≼-wk (σ ⨾ʷ new) (pn a) ; onComplete≼ = ≼-wk (σ ⨾ʷ new) pc ; isClosed≼ = ≼-wk (σ ⨾ʷ new) px })))
    interpret-sim (send≼ {s = s} {a = a} {k′ = k′} p) = bind-sim (send-sim s a) (λ _ → interpret-sim p) (λ _ → Grow.interpret-grow n′ gr′ k′)
    interpret-sim (finish≼ {s = s} {k′ = k′} p) = bind-sim (finish-sim s) (λ _ → interpret-sim p) (λ _ → Grow.interpret-grow n′ gr′ k′)
    interpret-sim (startCold≼ {c = c} {s = s} {k′ = k′} p) σ q = shift-rel new
      (bind-sim (first-sim (wk∋ new (wk∋ σ s)) here (lower c)) (λ _ → interpret-sim (p (σ ⨾ʷ new) here))
                (λ _ → Grow.interpret-grow n′ gr′ (k′ (σ ⨾ʷ new) here)) same (extend-rel q refl))
    interpret-sim (stop≼ {h = h} {k′ = k′} p) = bind-sim (spend-sim h) (λ _ → interpret-sim p) (λ _ → Grow.interpret-grow n′ gr′ k′)
    interpret-sim (eff≼ {e = note a} {k′ = k′} p) =
      bind-sim {m = Runtime.effᴿ (Pureᴿ n) (note a)} {m′ = Runtime.effᴿ (Pureᴿ n′) (note a)} (λ σ q → lock (stRel (heap≈ q) (clock≡ q) (timers≡ q) (cong₃ (λ e l c → if e then l else l ++ [ (c , a) ]) (ended≡ q) (log≡ q) (clock≡ q)) (ended≡ q) (pos≡ q)
        (cong₃ (λ e m p → if e then m else m ++ [ p ]) (ended≡ q) (marks≡ q) (pos≡ q))))
               (λ x → interpret-sim (p x)) (λ x → Grow.interpret-grow n′ gr′ (k′ x))
    interpret-sim (eff≼ {e = fin} {k′ = k′} p) =
      bind-sim {m = Runtime.effᴿ (Pureᴿ n) fin} {m′ = Runtime.effᴿ (Pureᴿ n′) fin} (λ σ q → lock (stRel (heap≈ q) (clock≡ q) (timers≡ q) (log≡ q) refl (pos≡ q)
        (cong₃ (λ e m p → if e then m else m ++ [ p ]) (ended≡ q) (marks≡ q) (pos≡ q)))) (λ x → interpret-sim (p x)) (λ x → Grow.interpret-grow n′ gr′ (k′ x))
    interpret-sim (here≼ p) = here-sim λ x → interpret-sim (p x)
    interpret-sim (goto≼ {p = p} {k′ = k′} q) =
      bind-sim {m = Runtime.gotoᴿ (Pureᴿ n) p} {m′ = Runtime.gotoᴿ (Pureᴿ n′) p} (goto-sim p) (λ _ → interpret-sim q) (λ _ → Grow.interpret-grow n′ gr′ k′)
    interpret-sim (unfold≼ {l = l} {e = e} {m′ = m′} pn pc px pk pm) =
      bind-sim (sr (compile-refl (Later.force l) e same (record { next≼ = pn ; complete≼ = pc ; closed≼ = px })
                      λ σ pu → register≼ (λ _ → pu) done≼ done≼ λ τ sk → pk (σ ⨾ʷ τ) sk))
               (λ _ → interpret-sim pm) (λ _ → Grow.interpret-grow n′ gr′ m′)

  ------------------------------------------------------------------------
  -- The engine's approximants

  runᴺ-grow : ∀ n k → GrowRun (runᴺ n k)
  runᴺ-grow n zero    a = grows λ σ st → growsAt-refl _ _ _
  runᴺ-grow n (suc k) a      = Grow.interpret-grow n (runᴺ-grow n k) a

  runᴺ-sim : ∀ {n n′ k k′} → n ≤ n′ → k ≤ k′ → SimRun (runᴺ n k) (runᴺ n′ k′)
  runᴺ-sim {n′ = n′} {k′ = k′} n≤ z≤n {a′ = a′} p = diverge-sim (runᴺ-grow n′ k′ a′)
  runᴺ-sim {n′ = n′} {k′ = suc k′} n≤ (s≤s q) p = Lockstep.interpret-sim n≤ (runᴺ-sim n≤ q) (runᴺ-grow n′ k′) p

  loopStep-grow : ∀ n {run : RunM} → GrowRun run → {again : M [] ⊤} → Grower again → Grower {[]} {⊤} (Engine.loopStep (Pureᴿ n) run again)
  loopStep-grow n {run} gr {again} ga = bind-grow {m = Runtime.nextᴿ (Pureᴿ n) run {[]}} {f = λ more → if_then_else_ {A = M [] ⊤} more again (Runtime.return (Pureᴿ n) tt)} (Grow.next-grow n gr) λ { true → ga ; false → ret-grow tt }

  loopStep-sim : ∀ {n n′} → n ≤ n′ → {run run′ : RunM} → SimRun run run′ → GrowRun run′ → {again again′ : M [] ⊤}
               → Sim again again′ → Grower again′ → Sim {[]} {⊤} (Engine.loopStep (Pureᴿ n) run again) (Engine.loopStep (Pureᴿ n′) run′ again′)
  loopStep-sim {n} {n′} n≤ {run} {run′} sr gr′ {again} {again′} pa ga = bind-sim {m = Runtime.nextᴿ (Pureᴿ n) run {[]}} {m′ = Runtime.nextᴿ (Pureᴿ n′) run′ {[]}} {f = λ more → if_then_else_ {A = M [] ⊤} more again (Runtime.return (Pureᴿ n) tt)} {f′ = λ more → if_then_else_ {A = M [] ⊤} more again′ (Runtime.return (Pureᴿ n′) tt)} (Lockstep.next-sim n≤ sr gr′) (λ { true → pa ; false → ret-sim tt })
                                             (λ { true → ga ; false → ret-grow tt })

  loopᴺ-grow : ∀ n k → Grower {[]} {⊤} (loopᴺ n k)
  loopᴺ-grow n zero    = grows λ σ st → growsAt-refl _ _ _
  loopᴺ-grow n (suc k) = loopStep-grow n (runᴺ-grow n (suc k)) (loopᴺ-grow n k)

  loopᴺ-sim : ∀ {n n′ k k′} → n ≤ n′ → k ≤ k′ → Sim {[]} {⊤} (loopᴺ n k) (loopᴺ n′ k′)
  loopᴺ-sim {n′ = n′} {k′ = k′} n≤ z≤n = diverge-sim (loopᴺ-grow n′ k′)
  loopᴺ-sim {n′ = n′} {k′ = suc k′} n≤ (s≤s q) =
    loopStep-sim n≤ (runᴺ-sim n≤ (s≤s q)) (runᴺ-grow n′ (suc k′)) (loopᴺ-sim n≤ q) (loopᴺ-grow n′ k′)

  ------------------------------------------------------------------------
  -- What a reader sees of a run cut short

  private
    ≡-nil : ∀ {A : Set} {x : ML A} {is} → is ≡ [] → Shows x is
    ≡-nil refl = nil

    ≡-nilIn : ∀ {A : Set} {t} {b} {is} → is ≡ [] → ShowsIn {A} t b is
    ≡-nilIn refl = nil

    stalls-nil : ∀ {A : Set} {t is} → ShowsIn {A} t (stall stalls) is → is ≡ []
    stalls-nil nil        = refl
    stalls-nil (stall⁺ s) = stalls-nil s

    ending-nil : ∀ {A : Set} {c is} → Shows {A} (ending (cutOff c)) is → is ≡ []
    ending-nil nil     = refl
    ending-nil (at⁺ s) = stalls-nil s

    sameFrame-nil : ∀ {A : Set} b c t {is} → ShowsIn {A} t (sameFrame b (stall stalls) (close (later (ending (cutOff c))))) is → is ≡ []
    sameFrame-nil true  c t s          = stalls-nil s
    sameFrame-nil false c t nil        = refl
    sameFrame-nil false c t (close⁺ s) = ending-nil s

  mutual
    -- A run cut short shows a prefix of any run whose record extends it.
    frames-cut : ∀ {A : Set} (xs ys : List (Time × A)) c e → frames xs (cutOff c) ⊑ frames (xs ++ ys) e
    frames-cut []             ys c e s                 = ≡-nil (ending-nil s)
    frames-cut ((t , a) ∷ xs) ys c e nil               = nil
    frames-cut ((t , a) ∷ xs) ys c e (at⁺ nil)         = at⁺ nil
    frames-cut ((t , a) ∷ xs) ys c e (at⁺ (emit⁺ s))   = at⁺ (emit⁺ (inFrame-cut t xs ys c e s))

    inFrame-cut : ∀ {A : Set} t (xs ys : List (Time × A)) c e {is} → ShowsIn t (inFrame t xs (cutOff c)) is → ShowsIn t (inFrame t (xs ++ ys) e) is
    inFrame-cut t []              ys c e s = ≡-nilIn (sameFrame-nil (c ≡ᵇ t) c t s)
    inFrame-cut t ((t′ , a) ∷ xs) ys c e s = sameFrame-cut (t′ ≡ᵇ t) t t′ a xs ys c e s

    sameFrame-cut : ∀ {A : Set} b t t′ (a : A) xs ys c e {is}
                  → ShowsIn t (sameFrame b (emit a (within t xs (cutOff c))) (close (later (frames ((t′ , a) ∷ xs) (cutOff c))))) is
                  → ShowsIn t (sameFrame b (emit a (within t (xs ++ ys) e)) (close (later (frames ((t′ , a) ∷ xs ++ ys) e)))) is
    sameFrame-cut true  t t′ a xs ys c e nil        = nil
    sameFrame-cut true  t t′ a xs ys c e (emit⁺ s)  = emit⁺ (inFrame-cut t xs ys c e s)
    sameFrame-cut false t t′ a xs ys c e nil        = nil
    sameFrame-cut false t t′ a xs ys c e (close⁺ s) = close⁺ (frames-cut ((t′ , a) ∷ xs) ys c e s)

  private
    cut-obs : ∀ {e ms xs e′ ns ys} c b′ c′ → GrowsAt e ms xs e′ ns ys → frames xs (endOf e nothing c) ⊑ frames ys (endOf e′ b′ c′)
    cut-obs {xs = xs} {e′ = e′} c b′ c′ (open≈ ps zs _ refl _) = frames-cut xs zs c (endOf e′ b′ c′)
    cut-obs c b′ c′ shut≈ s = s

  observe-mono : ∀ {x x′ : Res [] ⊤} → ResRel x x′ → observe x ⊑ observe x′
  observe-mono (lock {s = s} {s′} {b} q) sh =
    subst (λ y → Shows y _) (cong₃ (λ l e c → frames l (endOf e b c)) (log≡ q) (ended≡ q) (clock≡ q)) sh
  observe-mono (short {s = s} {s′ = s′} {b′ = b′} g) = cut-obs (State.clock s) b′ (State.clock s′) g

  ------------------------------------------------------------------------
  -- THE BUDGET ONLY CUTS

  ≼ᴼ-refl : ∀ {A w} (o : Observer A w) → o ≼ᴼ o
  ≼ᴼ-refl o = record { next≼ = λ a → ≼-refl _ ; complete≼ = ≼-refl _ ; closed≼ = ≼-refl _ }

  runPure-mono : ∀ {m m′ n n′} (o : PureObs [] R) → m ≤ m′ → n ≤ n′ → runPure m (compileᴺ n o []) ⊑ runPure m′ (compileᴺ n′ o [])
  runPure-mono {m′ = m′} o m≤ n≤ = observe-mono
    (bind-sim (runᴺ-sim m≤ m≤ (compileᴺ-≼ n≤ o [] same (≼ᴼ-refl recorder) λ σ p → done≼))
              (λ _ → loopᴺ-sim m≤ m≤) (λ _ → loopᴺ-grow m′ m′) same (stRel-refl start))
