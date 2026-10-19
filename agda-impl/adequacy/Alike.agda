{-# OPTIONS --guardedness #-}

-- OBSERVERS READ ALIKE, part for part: a compiled subscription over alike
-- observers, continuations and subjects, and a walk along a weakened
-- path handing what the walk along the path handed, weakened.
module adequacy.Alike where

open import Data.List using (List; []; _∷_; _++_; [_]; length; null) renaming (map to mapᴸ)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (tabulate to tabulateᴬ; lookup to lookupᴬ; map to all-map)
open import Data.List.Relation.Unary.Any using () renaming (here to hereᴬ; there to thereᴬ)
open import Data.List.Relation.Unary.Any.Properties using () renaming (++⁻ to any-++⁻; ++⁺ˡ to any-++⁺ˡ; ++⁺ʳ to any-++⁺ʳ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁻ to all-++⁻)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_) renaming (map to pairs-map)
open import Data.List.Relation.Unary.Linked using ([]; _∷_)
open import Data.List.Relation.Unary.AllPairs.Properties using () renaming (map⁺ to pairs-map⁺; ++⁺ to pairs-++⁺)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_; ↭-sym; ↭-trans; ↭-reflexive) renaming (refl to ↭-refl′; prep to ↭-prep′; swap to ↭-swap′; trans to ↭-trans′)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (All-resp-↭; shifts) renaming (++⁺ˡ to ↭-++⁺ˡ; ++⁺ʳ to ↭-++⁺ʳ)
open import Data.List.Properties using (map-++; ++-assoc) renaming (++-identityʳ to ++-idʳ)
open import Data.Maybe using (Maybe; just; nothing; is-just) renaming (map to mapMaybe)
open import Data.Nat using (ℕ; suc; pred; _≡ᵇ_; _<ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤₁; tt to tt₁)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; not)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)

open import denotation.MonotonicList.Events using (Timeline; Frame; From; Pos; ix; last; tick; at; _<ᵖ_; <ᵖ-below) renaming (done to doneᶠᵐ; quiet to quietᶠᵐ)
open import denotation.MonotonicList.Events using () renaming (sub to subᴾ)
import Tree as T
import denotation.Unfold as U
open import operation.PureObservable using (Out; Pureᴾ)
open import operation.AbstractObservable using (module Heap; module Run; Prims) renaming (module Machine to Shared)
open import adequacy.Strong using (module Strongly)
open import adequacy.Unsub using (module Unsubbing)
open import adequacy.Grow using (module Growing)
open import adequacy.Seq using (module Sequencing)
open import operation.AbstractObservable using (base; maybe; sink; list; fifo; quiet; gate)

module Aliking (R : Set) where
  open Unsubbing R using (≗-trans; wk≗; bind≗; wk-same; same-⨾)
  open Growing R using (wkPath; wkPathᴸ)
  open Sequencing R using (wk-wk; wk∋-wk; wkEl-wk; wkEnv-wk; seq-wk; ⨾-assoc)
  open Shared Timeline (Out R) using (wkVal)
  open Heap using (_⊑_; _⨾_; _∋_; there; new; grow; wk∋; cell; slot; Quiet) renaming (here to hereʳ; same to same⊑)
  open Run (Pureᴾ R) using (Act; done; compile; Env; wkEnv; wkAct; module Kit; module FlatKit; Ref; Observer; Kont; wkObs; wkKont; Subscription; Subscribe; emitAll; Subject; wkSubject; wkR; wkSubn; readRef; writeRef; stash; cancel; _>>ᴬ_; _>>=ᴬ_; newRef; register; send; finish; startCold; stop; eff; under; diverge; unfold) renaming (here to atᴬ)
  open Strongly R using (Sub; Lane; Path; PathLanes; here; in-map; in-scan; in-take; in-outer; in-lanes; in-source; in-body; in-defer; this-lane; next-lane; Here; ctx; walk; walkLanes; top; rootObs; takeK; flatK; laneK; bodyK; srcK; deferK; unsubscribing; _≗_; CbRel; killAllᶜ; ≗-refl; newRef≗; done≗; register≗; send≗; finish≗; startCold≗; stop≗; stash≗; cancel≗; eff≗; here≗; under≗; diverge≗; unfold≗; readRef≗; writeRef≗; module Canon)

  -- Two observers, part for part; two continuations, pointwise.
  ObsRel : ∀ {A w} → Observer A w → Observer A w → Set₁
  ObsRel o o′ = (∀ a → Observer.next o a ≗ Observer.next o′ a) × Observer.complete o ≗ Observer.complete o′ × Observer.closed o ≗ Observer.closed o′

  KontRel : ∀ {w} → Kont w → Kont w → Set₁
  KontRel {w} k k′ = ∀ {v} (σ : w ⊑ v) sub → k σ sub ≗ k′ σ sub

  -- A scan's observer over alike observers.
  scanO-cong : ∀ {h A B} (f : B → A → B) (r : Ref h (base B)) {o o′ : Observer B h} → ObsRel o o′ → ObsRel (Canon.scanO f r o) (Canon.scanO f r o′)
  scanO-cong f r (n , c , x) = (λ a → readRef≗ refl λ σ b → wk≗ σ (writeRef≗ refl refl (n (f b a)))) , c , x

  ≗-sym : ∀ {w B} {m m′ : Act w B} → m ≗ m′ → m′ ≗ m
  ≗-sym (done≗ e)                = done≗ (sym e)
  ≗-sym (newRef≗ e f)            = newRef≗ (sym e) λ σ r → ≗-sym (f σ r)
  ≗-sym (readRef≗ refl f)        = readRef≗ refl λ σ x → ≗-sym (f σ x)
  ≗-sym (writeRef≗ refl e k)     = writeRef≗ refl (sym e) (≗-sym k)
  ≗-sym (register≗ n c x k)      = register≗ (λ a → ≗-sym (n a)) (≗-sym c) (≗-sym x) λ σ s → ≗-sym (k σ s)
  ≗-sym (send≗ refl k)           = send≗ refl (≗-sym k)
  ≗-sym (finish≗ refl k)         = finish≗ refl (≗-sym k)
  ≗-sym (startCold≗ refl f)      = startCold≗ refl λ σ hd → ≗-sym (f σ hd)
  ≗-sym (stop≗ refl k)           = stop≗ refl (≗-sym k)
  ≗-sym (stash≗ m f)             = stash≗ (≗-sym m) λ σ q → ≗-sym (f σ q)
  ≗-sym (cancel≗ refl k)         = cancel≗ refl (≗-sym k)
  ≗-sym (eff≗ f)                 = eff≗ λ a → ≗-sym (f a)
  ≗-sym (here≗ f)                = here≗ λ p → ≗-sym (f p)
  ≗-sym (under≗ m k)             = under≗ (≗-sym m) (≗-sym k)
  ≗-sym diverge≗                 = diverge≗
  ≗-sym (unfold≗ refl n c x k m) = unfold≗ refl (λ a → ≗-sym (n a)) (≗-sym c) (≗-sym x) (λ σ q → ≗-sym (k σ q)) (≗-sym m)

  obs-trans : ∀ {A w} {o₁ o₂ o₃ : Observer A w} → ObsRel o₁ o₂ → ObsRel o₂ o₃ → ObsRel o₁ o₃
  obs-trans (n , c , x) (n′ , c′ , x′) = (λ a → ≗-trans (n a) (n′ a)) , ≗-trans c c′ , ≗-trans x x′

  obs-wk : ∀ {A w v} (ρ : w ⊑ v) {o o′ : Observer A w} → ObsRel o o′ → ObsRel (wkObs ρ o) (wkObs ρ o′)
  obs-wk ρ (n , c , x) = (λ a → wk≗ ρ (n a)) , wk≗ ρ c , wk≗ ρ x

  -- An observer weakened along a composite, as weakened twice.
  obs-⨾ : ∀ {A u v w} (σ : u ⊑ v) (τ : v ⊑ w) (o : Observer A u) → ObsRel (wkObs (σ ⨾ τ) o) (wkObs τ (wkObs σ o))
  obs-⨾ σ τ o = (λ a → ≗-sym (wk-wk σ τ _)) , ≗-sym (wk-wk σ τ _) , ≗-sym (wk-wk σ τ _)

  if≗ : ∀ {w B} b {x x′ y y′ : Act w B} → x ≗ x′ → y ≗ y′ → (if b then x else y) ≗ (if b then x′ else y′)
  if≗ true  e _ = e
  if≗ false _ e = e

  -- A takeWhile's observer over alike observers.
  takeO-cong : ∀ {h A} i (p : A → Bool) (c : Kit.Cut h) {o o′ : Observer A h} → ObsRel o o′ → ObsRel (Canon.takeWhileO i p c o) (Canon.takeWhileO i p c o′)
  takeO-cong i p c (n , cm , x) =
      (λ a → guard≗ (if≗ (p a) (n a) (bind≗ (if≗ i (under≗ (n a) (≗-refl _)) (≗-refl _)) λ _ → under≗ cm (≗-refl _))))
    , guard≗ cm
    , readRef≗ refl λ σ b → wk≗ σ (if≗ b x (≗-refl _))
    where guard≗ : ∀ {m m′} → m ≗ m′ → Kit.guard c m ≗ Kit.guard c m′
          guard≗ e = readRef≗ refl λ σ b → wk≗ σ (if≗ b e (≗-refl _))

  obs-sym : ∀ {A w} {o o′ : Observer A w} → ObsRel o o′ → ObsRel o′ o
  obs-sym (n , c , x) = (λ a → ≗-sym (n a)) , ≗-sym c , ≗-sym x

  -- A guarded observer over alike observers.
  guarded-cong : ∀ {h A} (c : Kit.Cut h) {o o′ : Observer A h} → ObsRel o o′ → ObsRel (Kit.guarded c o) (Kit.guarded c o′)
  guarded-cong c (n , cm , x) = (λ a → gd (n a)) , gd cm , readRef≗ refl λ σ b → wk≗ σ (if≗ b x (≗-refl _))
    where gd : ∀ {m m′} → m ≗ m′ → Kit.guard c m ≗ Kit.guard c m′
          gd e = readRef≗ refl λ σ b → wk≗ σ (if≗ b e (≗-refl _))

  -- A pool weakened twice, as weakened once.
  wkFlat-wk : ∀ {A u v w} (σ : u ⊑ v) (τ : v ⊑ w) (st : FlatKit.Flat A u) → FlatKit.wkFlat τ (FlatKit.wkFlat σ st) ≡ FlatKit.wkFlat (σ ⨾ τ) st
  wkFlat-wk σ τ st = flat≡ (wk∋-wk σ τ _) (wk∋-wk σ τ _) (wk∋-wk σ τ _) (wk∋-wk σ τ _) (wk∋-wk σ τ _)
    where flat≡ : ∀ {A w} {a a′ : Ref w (base ℕ)} {d d′ : Ref w (base Bool)} {q q′ : Ref w (fifo A)} {l l′ : Ref w (list Kit.cutTy)} {r r′ : Ref w (maybe (sink ⊤))}
                → a ≡ a′ → d ≡ d′ → q ≡ q′ → l ≡ l′ → r ≡ r′
                → _≡_ {A = FlatKit.Flat A w} (record { active = a ; outerDone = d ; queue = q ; lanes = l ; refill = r })
                                             (record { active = a′ ; outerDone = d′ ; queue = q′ ; lanes = l′ ; refill = r′ })
          flat≡ refl refl refl refl refl = refl

  -- Cutting every lane, weakened, cuts every lane of the weakened pool.
  killAll-wk : ∀ {A w v} (ρ : w ⊑ v) (st : FlatKit.Flat A w) → wkAct ρ (killAllᶜ st) ≗ killAllᶜ (FlatKit.wkFlat ρ st)
  killAll-wk ρ st = readRef≗ refl λ σ cs → writeRef≗ (sym (wk∋-wk ρ σ (FlatKit.Flat.lanes st))) refl
                      (writeRef≗ (sym (wk∋-wk ρ σ (FlatKit.Flat.active st))) refl (≗-refl _))

  ----------------------------------------------------------------------
  -- A compiled subscription over alike observers and continuations

  when≗ : ∀ {w} b {m m′ : Act w ⊤} → m ≗ m′ → Kit.when b m ≗ Kit.when b m′
  when≗ b e = if≗ b e (≗-refl _)

  obs-refl : ∀ {A w} (o : Observer A w) → ObsRel o o
  obs-refl o = (λ _ → ≗-refl _) , ≗-refl _ , ≗-refl _

  newCut≗ : ∀ {w B} {k k′ : ∀ {v} → w ⊑ v → Kit.Cut v → Act v B} → (∀ {v} (σ : w ⊑ v) c → k σ c ≗ k′ σ c) → Kit.newCut k ≗ Kit.newCut k′
  newCut≗ f = newRef≗ refl λ σ _ → newRef≗ refl λ τ _ → f (σ ⨾ τ) _

  newFlat≗ : ∀ {A w B} {k k′ : ∀ {v} → w ⊑ v → FlatKit.Flat A v → Act v B} → (∀ {v} (σ : w ⊑ v) st → k σ st ≗ k′ σ st)
           → FlatKit.newFlat k ≗ FlatKit.newFlat k′
  newFlat≗ f = newRef≗ refl λ _ _ → newRef≗ refl λ _ _ → newRef≗ refl λ _ _ → newRef≗ refl λ _ _ → newRef≗ refl λ _ _ → f _ _

  emit≗ : ∀ {A w} {o o′ : Observer A w} → ObsRel o o′ → ∀ i xs → emitAll o i xs ≗ emitAll o′ i xs
  emit≗ (n , cm , x) i []       = under≗ cm (≗-refl _)
  emit≗ oR           i (y ∷ ys) = bind≗ (proj₂ (proj₂ oR)) λ c → when≗ (not c) (under≗ (proj₁ oR y) (emit≗ oR (suc i) ys))

  -- Inners alike at every world and alike observers.
  SubRel : ∀ {A w} → Subscribe A w → Subscribe A w → Set₁
  SubRel {A} {w} s s′ = ∀ {v} (σ : w ⊑ v) {p p′ : Observer A v} {k k′ : Kont v} → ObsRel p p′ → KontRel k k′ → s σ p k ≗ s′ σ p′ k′

  -- A flatMap's pool over alike observers, its inners alike.
  module FlatCong {A B w} (op : T.FlatOp) (f f′ : A → Subscribe B w) (o o′ : Observer B w) (st : FlatKit.Flat A w)
                  (fR : ∀ a → SubRel (f a) (f′ a)) (oR : ObsRel o o′) where
    private
      module M  = FlatKit.FlatMap op f o st
      module M′ = FlatKit.FlatMap op f′ o′ st

    settle≗ : M.settle ≗ M′.settle
    settle≗ = readRef≗ refl λ σ d → wk≗ σ (readRef≗ refl λ σ′ n → wk≗ σ′ (readRef≗ refl λ σ″ q → wk≗ σ″ (when≗ (d ∧ (n ≡ᵇ 0) ∧ null q) (proj₁ (proj₂ oR)))))

    handOn≗ : ∀ {v} (σ : w ⊑ v) mr → M.handOn σ mr ≗ M′.handOn σ mr
    handOn≗ σ nothing  = wk≗ σ settle≗
    handOn≗ σ (just r) = ≗-refl _

    laneO≗ : ∀ {v} (σ : w ⊑ v) c → ObsRel (M.lane σ c) (M′.lane σ c)
    laneO≗ σ c = (λ a → wk≗ σ (proj₁ oR a)) , writeRef≗ refl refl (bind≗ (≗-refl (Kit.modifyB (FlatKit.Flat.active (FlatKit.wkFlat σ st)) pred)) λ _ → readRef≗ refl λ τ r → handOn≗ (σ ⨾ τ) r) , wk≗ σ (proj₂ (proj₂ oR))

    start≗ : ∀ {l l′ : Subscribe B w} → SubRel l l′ → M.start l ≗ M′.start l′
    start≗ lR = bind≗ (proj₂ (proj₂ oR)) λ cl → when≗ (not cl) (bind≗ (≗-refl (Kit.modifyB (FlatKit.Flat.active st) suc)) λ _ → newCut≗ λ σ c →
      bind≗ (≗-refl (Kit.modify (FlatKit.Flat.lanes (FlatKit.wkFlat σ st)) (λ τ cs → Kit.wkCut τ c ∷ cs))) λ _ →
        under≗ {l = ix 1} (lR σ (guarded-cong c (laneO≗ σ c)) (λ τ sub → ≗-refl (Kit.attach (Kit.wkCut τ c) sub))) (≗-refl Kit.skipᴬ))

    dequeue≗ : M.dequeue ≗ M′.dequeue
    dequeue≗ = readRef≗ refl λ { σ [] → wk≗ σ settle≗ ; σ (a ∷ _) → wk≗ σ (writeRef≗ refl refl (start≗ (fR a))) }

    admit≗ : ∀ op′ a → M.admit op′ a ≗ M′.admit op′ a
    admit≗ (T.mergeᶠ nothing)  a = start≗ (fR a)
    admit≗ (T.mergeᶠ (just n)) a = readRef≗ refl λ σ c → wk≗ σ (if≗ (c <ᵇ n) (start≗ (fR a)) (≗-refl _))
    admit≗ T.switchᶠ           a = bind≗ (≗-refl M.killAll) λ _ → start≗ (fR a)
    admit≗ T.exhaustᶠ          a = readRef≗ refl λ σ c → wk≗ σ (when≗ (c ≡ᵇ 0) (start≗ (fR a)))

    run≗ : ∀ oc {s s′ : Subscribe A w} {k k′ : Kont w} → SubRel s s′ → KontRel k k′ → M.run oc s k ≗ M′.run oc s′ k′
    run≗ oc sR kR = register≗ (λ _ → dequeue≗) (≗-refl _) (≗-refl _) λ σ r → writeRef≗ refl refl
      (sR σ (guarded-cong (Kit.wkCut σ oc) ((λ a → wk≗ σ (admit≗ op a)) , writeRef≗ refl refl (wk≗ σ settle≗) , wk≗ σ (proj₂ (proj₂ oR))))
            (λ τ sub → bind≗ (≗-refl (Kit.attach (Kit.wkCut (σ ⨾ τ) oc) sub)) λ _ →
              kR (σ ⨾ τ) (record { unsubscribe = Kit.cut (Kit.wkCut (σ ⨾ τ) oc) >>ᴬ wkAct (σ ⨾ τ) M.killAll })))

  -- A compiled subscription read alike under alike observers and
  -- continuations.
  compile-cong : ∀ {Γ A u w} (s : T.Obs Timeline Γ A) (E : Env Γ u) (υ : u ⊑ w) {o o′ : Observer A w} {k k′ : Kont w}
               → ObsRel o o′ → KontRel k k′ → compile s E υ o k ≗ compile s E υ o′ k′
  compile-cong (T.cold c)          E υ (n , cm , x) kR = register≗ n cm x λ σ _ → startCold≗ refl λ τ _ → kR (σ ⨾ τ) _
  compile-cong T.empty             E υ (n , cm , x) kR = under≗ cm (kR _ _)
  compile-cong (T.of xs)           E υ oR kR = bind≗ (emit≗ oR 0 xs) λ _ → kR _ _
  compile-cong (T.map f s)         E υ (n , cm , x) kR = compile-cong s E υ ((λ a → n (f a)) , cm , x) kR
  compile-cong (T.scan f z s)      E υ (n , cm , x) kR = newRef≗ refl λ σ r →
    compile-cong s E (υ ⨾ σ) ((λ a → readRef≗ refl λ τ b → wk≗ τ (writeRef≗ refl refl (wk≗ σ (n (f b a))))) , wk≗ σ cm , wk≗ σ x) λ τ sub → kR (σ ⨾ τ) sub
  compile-cong (T.takeWhile i p s) E υ oR kR = newCut≗ λ σ c →
    compile-cong s E (υ ⨾ σ) (takeO-cong i p c (obs-wk σ oR)) λ τ sub → bind≗ (≗-refl (Kit.attach (Kit.wkCut τ c) sub)) λ _ →
      kR (σ ⨾ τ) (record { unsubscribe = Kit.cut (Kit.wkCut τ c) })
  compile-cong (T.flatMap op f s)  E υ {o} {o′} oR kR = newFlat≗ λ σ st → newCut≗ λ τ oc →
    FlatCong.run≗ op (λ a σ′ → compile (f a) E ((υ ⨾ σ ⨾ τ) ⨾ σ′)) (λ a σ′ → compile (f a) E ((υ ⨾ σ ⨾ τ) ⨾ σ′))
                  (wkObs (σ ⨾ τ) o) (wkObs (σ ⨾ τ) o′) (FlatKit.wkFlat τ st)
                  (λ a σ′ pR kR′ → compile-cong (f a) E ((υ ⨾ σ ⨾ τ) ⨾ σ′) pR kR′) (obs-wk (σ ⨾ τ) oR)
                  oc (λ σ′ pR kR′ → compile-cong s E ((υ ⨾ σ ⨾ τ) ⨾ σ′) pR kR′) λ σ′ sub → kR ((σ ⨾ τ) ⨾ σ′) sub
  compile-cong (T.connect s b)     E υ (n , cm , x) kR = newRef≗ refl λ σ _ → newRef≗ refl λ τ _ → newRef≗ refl λ σ₁ l → newRef≗ refl λ τ₁ h → newRef≗ refl λ υ′ bodyRef →
    under≗ (compile-cong b _ _ ((λ a → wk≗ (σ ⨾ τ ⨾ (σ₁ ⨾ τ₁) ⨾ υ′) (n a)) , bind≗ (wk≗ (σ ⨾ τ ⨾ (σ₁ ⨾ τ₁) ⨾ υ′) cm) (λ _ → ≗-refl (Kit.cut (Kit.wkCut υ′ (wkR τ₁ l , h))))
                                 , wk≗ (σ ⨾ τ ⨾ (σ₁ ⨾ τ₁) ⨾ υ′) x) λ _ _ → ≗-refl _)
           (under≗ (compile-cong s _ _ (obs-refl _) λ ψ src → bind≗ (≗-refl (Kit.attach (Kit.wkCut ψ (Kit.wkCut υ′ (wkR τ₁ l , h))) src)) λ _ →
                      readRef≗ {r = wkR ψ bodyRef} refl λ ψ′ mb →
                        kR (σ ⨾ τ ⨾ (σ₁ ⨾ τ₁) ⨾ υ′ ⨾ ψ ⨾ ψ′) (record { unsubscribe = Subscription.unsubscribe (wkSubn ψ′ src) >>ᴬ Kit.unsubscribeVia mb }))
                   (≗-refl Kit.skipᴬ))
  compile-cong (T.connected i)     E υ (n , cm , x) kR = here≗ λ j → readRef≗ refl λ
    { σ true  → under≗ (wk≗ σ cm) (wk≗ σ (kR _ _))
    ; σ false → newRef≗ refl λ σ′ l →
        register≗ (λ a → readRef≗ refl λ τ g → wk≗ τ (when≗ g (wk≗ (σ ⨾ σ′) (n a)))) (readRef≗ refl λ τ g → wk≗ τ (when≗ g (wk≗ (σ ⨾ σ′) cm)))
                  (readRef≗ refl λ τ g → wk≗ τ (if≗ g (wk≗ (σ ⨾ σ′) x) (≗-refl (done true)))) λ τ sk →
        bind≗ (≗-refl (Kit.modify (Subject.subscribers (wkSubject (υ ⨾ (σ ⨾ σ′) ⨾ τ) (lookupᴬ E i))) (λ π ss → ss ++ [ (Prims.wkSink (Pureᴾ R) π sk , j) ])))
          λ _ → kR ((σ ⨾ σ′) ⨾ τ) (record { unsubscribe = writeRef (wkR τ l) false Kit.skipᴬ }) }
  compile-cong (T.defer l)         E υ (n , cm , x) kR = unfold≗ refl n cm x (λ τ _ → kR τ _) (≗-refl _)

  ----------------------------------------------------------------------
  -- A compiled subscription reads its subjects only as weakened to the
  -- world it runs at

  env-ext : ∀ {Γ u u′ w x} (υ : u ⊑ w) (υ′ : u′ ⊑ w) {E : Env Γ u} {E′ : Env Γ u′} (σ : w ⊑ x)
          → wkEnv υ E ≡ wkEnv υ′ E′ → wkEnv (υ ⨾ σ) E ≡ wkEnv (υ′ ⨾ σ) E′
  env-ext υ υ′ {E} {E′} σ e = trans (sym (wkEnv-wk υ σ E)) (trans (cong (wkEnv σ) e) (wkEnv-wk υ′ σ E′))

  lookup-wkEnv : ∀ {Γ A u v} (υ : u ⊑ v) (E : Env Γ u) (i : A ∈ Γ) → lookupᴬ (wkEnv υ E) i ≡ wkSubject υ (lookupᴬ E i)
  lookup-wkEnv υ (st ∷ E) (hereᴬ refl) = refl
  lookup-wkEnv υ (st ∷ E) (thereᴬ i)   = lookup-wkEnv υ E i

  compile-at : ∀ {Γ A u u′ w} (s : T.Obs Timeline Γ A) (E : Env Γ u) (E′ : Env Γ u′) (υ : u ⊑ w) (υ′ : u′ ⊑ w) {o : Observer A w} {k : Kont w}
             → wkEnv υ E ≡ wkEnv υ′ E′ → compile s E υ o k ≗ compile s E′ υ′ o k
  compile-at (T.cold c)          E E′ υ υ′ e = ≗-refl _
  compile-at T.empty             E E′ υ υ′ e = ≗-refl _
  compile-at (T.of xs)           E E′ υ υ′ e = ≗-refl _
  compile-at (T.map f s)         E E′ υ υ′ e = compile-at s E E′ υ υ′ e
  compile-at (T.scan f z s)      E E′ υ υ′ e = newRef≗ refl λ σ _ → compile-at s E E′ (υ ⨾ σ) (υ′ ⨾ σ) (env-ext υ υ′ σ e)
  compile-at (T.takeWhile i p s) E E′ υ υ′ {o} {k} e = newCut≗ λ σ c →
    compile-at s E E′ (υ ⨾ σ) (υ′ ⨾ σ) {o = Canon.takeWhileO i p c (wkObs σ o)} {k = takeK c (wkKont σ k)} (env-ext υ υ′ σ e)
  compile-at (T.flatMap op f s)  E E′ υ υ′ {o} {k} e = newFlat≗ λ σ st → newCut≗ λ τ oc →
    FlatCong.run≗ op (λ a σ′ → compile (f a) E ((υ ⨾ σ ⨾ τ) ⨾ σ′)) (λ a σ′ → compile (f a) E′ ((υ′ ⨾ σ ⨾ τ) ⨾ σ′))
                  (wkObs (σ ⨾ τ) o) (wkObs (σ ⨾ τ) o) (FlatKit.wkFlat τ st)
                  (λ a σ′ pR kR′ → ≗-trans (compile-at (f a) E E′ ((υ ⨾ σ ⨾ τ) ⨾ σ′) ((υ′ ⨾ σ ⨾ τ) ⨾ σ′) (ee σ τ σ′)) (compile-cong (f a) E′ _ pR kR′))
                  (obs-refl (wkObs (σ ⨾ τ) o))
                  oc (λ σ′ pR kR′ → ≗-trans (compile-at s E E′ ((υ ⨾ σ ⨾ τ) ⨾ σ′) ((υ′ ⨾ σ ⨾ τ) ⨾ σ′) (ee σ τ σ′)) (compile-cong s E′ _ pR kR′))
                  λ σ′ sub → ≗-refl (k ((σ ⨾ τ) ⨾ σ′) sub)
    where ee : ∀ {x y z} (σ : _ ⊑ x) (τ : x ⊑ y) (σ′ : y ⊑ z) → wkEnv ((υ ⨾ σ ⨾ τ) ⨾ σ′) E ≡ wkEnv ((υ′ ⨾ σ ⨾ τ) ⨾ σ′) E′
          ee σ τ σ′ = env-ext (υ ⨾ σ ⨾ τ) (υ′ ⨾ σ ⨾ τ) σ′ (env-ext υ υ′ (σ ⨾ τ) e)
  compile-at (T.connect s b)     E E′ υ υ′ e = newRef≗ refl λ σ _ → newRef≗ refl λ τ _ → newRef≗ refl λ σ₁ _ → newRef≗ refl λ τ₁ _ → newRef≗ refl λ υ″ _ →
    under≗ (compile-at b _ _ same⊑ same⊑ (cong (wkEnv same⊑) (cong (_ ∷_) (env-ext υ υ′ (σ ⨾ τ ⨾ (σ₁ ⨾ τ₁) ⨾ υ″) e))))
           (under≗ (compile-at s E E′ (υ ⨾ σ ⨾ τ ⨾ (σ₁ ⨾ τ₁) ⨾ υ″) (υ′ ⨾ σ ⨾ τ ⨾ (σ₁ ⨾ τ₁) ⨾ υ″) (env-ext υ υ′ (σ ⨾ τ ⨾ (σ₁ ⨾ τ₁) ⨾ υ″) e))
                   (≗-refl Kit.skipᴬ))
  compile-at (T.connected i)     E E′ υ υ′ {o} {k} e = here≗ λ j → readRef≗ (cong Subject.closed hs) λ
    { σ true  → ≗-refl _
    ; σ false → newRef≗ refl λ σ′ l → register≗ (λ _ → ≗-refl _) (≗-refl _) (≗-refl _) λ τ sk →
        bind≗ (subst (λ r → Kit.modify (Subject.subscribers (wkSubject (υ ⨾ (σ ⨾ σ′) ⨾ τ) (lookupᴬ E i))) (λ π ss → ss ++ [ (Prims.wkSink (Pureᴾ R) π sk , j) ])
                          ≗ Kit.modify r (λ π ss → ss ++ [ (Prims.wkSink (Pureᴾ R) π sk , j) ]))
                     (subs-eq ((σ ⨾ σ′) ⨾ τ)) (≗-refl _))
          λ _ → ≗-refl (k ((σ ⨾ σ′) ⨾ τ) (record { unsubscribe = writeRef (wkR τ l) false Kit.skipᴬ })) }
    where hs : wkSubject υ (lookupᴬ E i) ≡ wkSubject υ′ (lookupᴬ E′ i)
          hs = trans (sym (lookup-wkEnv υ E i)) (trans (cong (λ x → lookupᴬ x i) e) (lookup-wkEnv υ′ E′ i))
          subs-eq : ∀ {x} (Y : _ ⊑ x) → wkR (υ ⨾ Y) (Subject.subscribers (lookupᴬ E i)) ≡ wkR (υ′ ⨾ Y) (Subject.subscribers (lookupᴬ E′ i))
          subs-eq Y = trans (sym (wk∋-wk υ Y _)) (trans (cong (λ S → wkR Y (Subject.subscribers S)) hs) (wk∋-wk υ′ Y _))
  compile-at (T.defer l)         E E′ υ υ′ e = unfold≗ e (λ _ → ≗-refl _) (≗-refl _) (≗-refl _) (λ _ _ → ≗-refl _) (≗-refl _)

  compile-env : ∀ {Γ A u v w} (s : T.Obs Timeline Γ A) (E : Env Γ u) (υ : u ⊑ v) (ρ : v ⊑ w) {o : Observer A w} {k : Kont w}
              → compile s E (υ ⨾ ρ) o k ≗ compile s (wkEnv υ E) ρ o k
  compile-env s E υ ρ = compile-at s E (wkEnv υ E) (υ ⨾ ρ) ρ (sym (wkEnv-wk υ ρ E))

  ----------------------------------------------------------------------
  -- Weakening read through the kernels' toolkit

  bind-wk : ∀ {u v A B} (σ : u ⊑ v) (m : Act u A) (f : A → Act u B) → wkAct σ (m >>=ᴬ f) ≗ (wkAct σ m >>=ᴬ λ a → wkAct σ (f a))
  bind-wk σ (done b)              f = ≗-refl _
  bind-wk σ (newRef t a k)        f = newRef≗ refl λ υ r → bind≗ (≗-refl (k (σ ⨾ υ) r)) λ x → ≗-sym (wk-wk σ υ (f x))
  bind-wk σ (readRef r k)         f = readRef≗ refl λ υ x → bind≗ (≗-refl (k (σ ⨾ υ) x)) λ y → ≗-sym (wk-wk σ υ (f y))
  bind-wk σ (writeRef r a k)      f = writeRef≗ refl refl (bind-wk σ k f)
  bind-wk σ (register n c x k)    f = register≗ (λ _ → ≗-refl _) (≗-refl _) (≗-refl _) λ υ s → bind≗ (≗-refl (k (σ ⨾ υ) s)) λ y → ≗-sym (wk-wk σ υ (f y))
  bind-wk σ (send s a k)          f = send≗ refl (bind-wk σ k f)
  bind-wk σ (finish s k)          f = finish≗ refl (bind-wk σ k f)
  bind-wk σ (startCold c s k)     f = startCold≗ refl λ υ h → bind≗ (≗-refl (k (σ ⨾ υ) h)) λ y → ≗-sym (wk-wk σ υ (f y))
  bind-wk σ (stop h k)            f = stop≗ refl (bind-wk σ k f)
  bind-wk σ (stash m k)           f = stash≗ (≗-refl _) λ υ q → bind≗ (≗-refl (k (σ ⨾ υ) q)) λ y → ≗-sym (wk-wk σ υ (f y))
  bind-wk σ (cancel q k)          f = cancel≗ refl (bind-wk σ k f)
  bind-wk σ (eff e k)             f = eff≗ λ a → bind-wk σ (k a) f
  bind-wk σ (atᴬ k)               f = here≗ λ p → bind-wk σ (k p) f
  bind-wk σ (under l m k)         f = under≗ (≗-refl _) (bind-wk σ k f)
  bind-wk σ diverge               f = diverge≗
  bind-wk σ (unfold l e n c x k m) f = unfold≗ refl (λ _ → ≗-refl _) (≗-refl _) (≗-refl _) (λ _ _ → ≗-refl _) (bind-wk σ m f)

  seq≗ : ∀ {w B} (m : Act w ⊤) (n : Act w B) {m′ n′} → m ≗ m′ → n ≗ n′ → (m >>ᴬ n) ≗ (m′ >>ᴬ n′)
  seq≗ m n p q = bind≗ {m = m} {f = λ _ → n} p λ _ → q

  seq-wk≗ : ∀ {w v B} (τ : w ⊑ v) (m : Act w ⊤) (n : Act w B) {m′ n′} → wkAct τ m ≗ m′ → wkAct τ n ≗ n′ → wkAct τ (m >>ᴬ n) ≗ (m′ >>ᴬ n′)
  seq-wk≗ τ m n p q = ≗-trans (≗-sym (seq-wk τ m n)) (seq≗ (wkAct τ m) (wkAct τ n) p q)

  when-wk : ∀ {w v} (τ : w ⊑ v) b {m : Act w ⊤} {m′} → wkAct τ m ≗ m′ → wkAct τ (Kit.when b m) ≗ Kit.when b m′
  when-wk τ true  e = e
  when-wk τ false e = ≗-refl _

  emit-wk : ∀ {w v A} (τ : w ⊑ v) (o : Observer A w) (o′ : Observer A v) → ObsRel (wkObs τ o) o′ → ∀ i xs → wkAct τ (emitAll o i xs) ≗ emitAll o′ i xs
  emit-wk τ o o′ (n , cm , x) i []       = under≗ cm (≗-refl _)
  emit-wk τ o o′ oR@(n , cm , x) i (y ∷ ys) =
    ≗-trans (bind-wk τ (Observer.closed o) (λ c → Kit.when (not c) (under (ix i) (Observer.next o y) (emitAll o (suc i) ys))))
      (bind≗ {m = wkAct τ (Observer.closed o)} {f = λ c → wkAct τ (Kit.when (not c) (under (ix i) (Observer.next o y) (emitAll o (suc i) ys)))} x λ c →
        when-wk τ (not c) (under≗ (n y) (emit-wk τ o o′ oR (suc i) ys)))

  if-wk : ∀ {w v B} (τ : w ⊑ v) b {x y : Act w B} {x′ y′} → wkAct τ x ≗ x′ → wkAct τ y ≗ y′ → wkAct τ (if b then x else y) ≗ (if b then x′ else y′)
  if-wk τ true  e _ = e
  if-wk τ false _ e = e

  readB-wk : ∀ {w v B X} (τ : w ⊑ v) (r : Ref w (base X)) {k : X → Act w B} {k′ : X → Act v B} → (∀ x → wkAct τ (k x) ≗ k′ x)
           → wkAct τ (Kit.readB r k) ≗ Kit.readB (wkR τ r) k′
  readB-wk τ r {k} f = readRef≗ refl λ σ x → ≗-trans (≗-sym (wk-wk τ σ (k x))) (wk≗ σ (f x))

  readF-wk : ∀ {w v B X} (τ : w ⊑ v) (r : Ref w (fifo X)) {k : List X → Act w B} {k′ : List X → Act v B} → (∀ x → wkAct τ (k x) ≗ k′ x)
           → wkAct τ (Kit.readF r k) ≗ Kit.readF (wkR τ r) k′
  readF-wk τ r {k} f = readRef≗ refl λ σ x → ≗-trans (≗-sym (wk-wk τ σ (k x))) (wk≗ σ (f x))

  modifyB-wk : ∀ {w v X} (τ : w ⊑ v) (r : Ref w (base X)) (g : X → X) → wkAct τ (Kit.modifyB r g) ≗ Kit.modifyB (wkR τ r) g
  modifyB-wk τ r g = readRef≗ refl λ σ x → writeRef≗ (sym (wk∋-wk τ σ r)) refl (≗-refl _)

  modifyF-wk : ∀ {w v X} (τ : w ⊑ v) (r : Ref w (fifo X)) (g : List X → List X) → wkAct τ (Kit.modifyF r g) ≗ Kit.modifyF (wkR τ r) g
  modifyF-wk τ r g = readRef≗ refl λ σ x → writeRef≗ (sym (wk∋-wk τ σ r)) refl (≗-refl _)

  cut-wk : ∀ {w v} (τ : w ⊑ v) (c : Kit.Cut w) → wkAct τ (Kit.cut c) ≗ Kit.cut (Kit.wkCut τ c)
  cut-wk τ c = writeRef≗ refl refl (readRef≗ refl λ { σ nothing → ≗-refl _ ; σ (just t) → ≗-refl _ })

  cut-eq : ∀ {u v w} (τ : u ⊑ v) (σ : v ⊑ w) (c : Kit.Cut u) → Kit.wkCut σ (Kit.wkCut τ c) ≡ Kit.wkCut (τ ⨾ σ) c
  cut-eq τ σ c = wkEl-wk Kit.cutTy τ σ c

  guard-wk : ∀ {w v} (τ : w ⊑ v) (c : Kit.Cut w) {m : Act w ⊤} {m′} → wkAct τ m ≗ m′ → wkAct τ (Kit.guard c m) ≗ Kit.guard (Kit.wkCut τ c) m′
  guard-wk τ c e = readB-wk τ (Kit.live c) λ b → when-wk τ b e

  guarded-wk : ∀ {w v A} (τ : w ⊑ v) (c : Kit.Cut w) {o : Observer A w} {o′} → ObsRel (wkObs τ o) o′
             → ObsRel (wkObs τ (Kit.guarded c o)) (Kit.guarded (Kit.wkCut τ c) o′)
  guarded-wk τ c (n , cm , x) = (λ a → guard-wk τ c (n a)) , guard-wk τ c cm , readB-wk τ (Kit.live c) λ b → if-wk τ b x (≗-refl _)

  ----------------------------------------------------------------------
  -- A flatMap's pool, weakened: the pool over the weakened cells, its
  -- inners read further along the weakening

  SubWk : ∀ {A w v} → w ⊑ v → Subscribe A w → Subscribe A v → Set₁
  SubWk {A} {w} {v} τ s s′ = ∀ {x} (σ : v ⊑ x) {p p′ : Observer A x} {k k′ : Kont x} → ObsRel p p′ → KontRel k k′ → s (τ ⨾ σ) p k ≗ s′ σ p′ k′

  module FlatWk {A B w v} (τ : w ⊑ v) (op : T.FlatOp) (f : A → Subscribe B w) (f′ : A → Subscribe B v) (o : Observer B w) (o′ : Observer B v)
                (st : FlatKit.Flat A w) (fW : ∀ a → SubWk τ (f a) (f′ a)) (oW : ObsRel (wkObs τ o) o′) where
    private
      module M  = FlatKit.FlatMap op f o st
      module M′ = FlatKit.FlatMap op f′ o′ (FlatKit.wkFlat τ st)

    settle-wk : wkAct τ M.settle ≗ M′.settle
    settle-wk = readB-wk τ (FlatKit.Flat.outerDone st) {k = K₁ st o} {k′ = K₁ (FlatKit.wkFlat τ st) o′} λ d →
      readB-wk τ (FlatKit.Flat.active st) {k = K₂ st o d} {k′ = K₂ (FlatKit.wkFlat τ st) o′ d} λ n →
      readF-wk τ (FlatKit.Flat.queue st) λ q → when-wk τ (d ∧ (n ≡ᵇ 0) ∧ null q) (proj₁ (proj₂ oW))
      where
        K₂ : ∀ {x} → FlatKit.Flat A x → Observer B x → Bool → ℕ → Act x ⊤
        K₂ fl p d n = Kit.readF (FlatKit.Flat.queue fl) λ q → Kit.when (d ∧ (n ≡ᵇ 0) ∧ null q) (Observer.complete p)
        K₁ : ∀ {x} → FlatKit.Flat A x → Observer B x → Bool → Act x ⊤
        K₁ fl p d = Kit.readB (FlatKit.Flat.active fl) (K₂ fl p d)

    handOn-wk : ∀ {x} (σ : v ⊑ x) mr → M.handOn (τ ⨾ σ) mr ≗ M′.handOn σ mr
    handOn-wk σ nothing  = ≗-trans (≗-sym (wk-wk τ σ M.settle)) (wk≗ σ settle-wk)
    handOn-wk σ (just r) = ≗-refl _

    lane-wk : ∀ {x} (σ : v ⊑ x) c → ObsRel (M.lane (τ ⨾ σ) c) (M′.lane σ c)
    lane-wk σ c =
        (λ a → ≗-trans (≗-sym (wk-wk τ σ (Observer.next o a))) (wk≗ σ (proj₁ oW a)))
      , subst (λ fl → Observer.complete (M.lane (τ ⨾ σ) c)
                      ≗ writeRef (Kit.live c) false (Kit.modifyB (FlatKit.Flat.active fl) pred >>ᴬ readRef (FlatKit.Flat.refill fl) λ τ′ → M′.handOn (σ ⨾ τ′)))
              (sym (wkFlat-wk τ σ st))
              (writeRef≗ refl refl (seq≗ (Kit.modifyB (FlatKit.Flat.active (FlatKit.wkFlat (τ ⨾ σ) st)) pred)
                                         (readRef (FlatKit.Flat.refill (FlatKit.wkFlat (τ ⨾ σ) st)) λ τ′ → M.handOn ((τ ⨾ σ) ⨾ τ′))
                (≗-refl _)
                (readRef≗ refl λ τ′ r → subst (λ ζ → M.handOn ζ r ≗ M′.handOn (σ ⨾ τ′) r) (⨾-assoc τ σ τ′) (handOn-wk (σ ⨾ τ′) r))))
      , ≗-trans (≗-sym (wk-wk τ σ (Observer.closed o))) (wk≗ σ (proj₂ (proj₂ oW)))

    start-wk : ∀ {l : Subscribe B w} {l′ : Subscribe B v} → SubWk τ l l′ → wkAct τ (M.start l) ≗ M′.start l′
    start-wk {l} {l′} lW =
      ≗-trans (bind-wk τ (Observer.closed o) body)
        (bind≗ {m = wkAct τ (Observer.closed o)} {f = λ cl → wkAct τ (body cl)} (proj₂ (proj₂ oW)) λ cl →
          when-wk τ (not cl) (seq-wk≗ τ (Kit.modifyB (FlatKit.Flat.active st) suc) (Kit.newCut cutK) (modifyB-wk τ (FlatKit.Flat.active st) suc)
            (newRef≗ refl λ σ l₀ → newRef≗ refl λ σ′ h₀ →
              subst (λ ζ → cutK ζ (wkR σ′ l₀ , h₀) ≗ cutK′ (σ ⨾ σ′) (wkR σ′ l₀ , h₀)) (⨾-assoc τ σ σ′) (cut-step (σ ⨾ σ′) (wkR σ′ l₀ , h₀)))))
      where
        cutK : ∀ {x} → w ⊑ x → Kit.Cut x → Act x ⊤
        cutK σ c = Kit.modify (FlatKit.Flat.lanes (FlatKit.wkFlat σ st)) (λ τ′ cs → Kit.wkCut τ′ c ∷ cs)
                   >>ᴬ under (ix 1) (l σ (Kit.guarded c (M.lane σ c)) λ τ′ → Kit.attach (Kit.wkCut τ′ c)) Kit.skipᴬ
        cutK′ : ∀ {x} → v ⊑ x → Kit.Cut x → Act x ⊤
        cutK′ σ c = Kit.modify (FlatKit.Flat.lanes (FlatKit.wkFlat σ (FlatKit.wkFlat τ st))) (λ τ′ cs → Kit.wkCut τ′ c ∷ cs)
                    >>ᴬ under (ix 1) (l′ σ (Kit.guarded c (M′.lane σ c)) λ τ′ → Kit.attach (Kit.wkCut τ′ c)) Kit.skipᴬ
        body : Bool → Act w ⊤
        body cl = Kit.when (not cl) (Kit.modifyB (FlatKit.Flat.active st) suc >>ᴬ Kit.newCut cutK)
        cut-step : ∀ {x} (σ : v ⊑ x) c → cutK (τ ⨾ σ) c ≗ cutK′ σ c
        cut-step σ c =
          seq≗ (Kit.modify (FlatKit.Flat.lanes (FlatKit.wkFlat (τ ⨾ σ) st)) (λ τ′ cs → Kit.wkCut τ′ c ∷ cs))
               (under (ix 1) (l (τ ⨾ σ) (Kit.guarded c (M.lane (τ ⨾ σ) c)) λ τ′ → Kit.attach (Kit.wkCut τ′ c)) Kit.skipᴬ)
            (subst (λ r → Kit.modify (FlatKit.Flat.lanes (FlatKit.wkFlat (τ ⨾ σ) st)) (λ τ′ cs → Kit.wkCut τ′ c ∷ cs) ≗ Kit.modify r (λ τ′ cs → Kit.wkCut τ′ c ∷ cs))
                   (sym (wk∋-wk τ σ (FlatKit.Flat.lanes st))) (≗-refl _))
            (under≗ (lW σ (guarded-cong c (lane-wk σ c)) λ τ′ sub → ≗-refl _) (≗-refl _))

    admit-wk : ∀ op′ a → wkAct τ (M.admit op′ a) ≗ M′.admit op′ a
    admit-wk (T.mergeᶠ nothing)  a = start-wk {f a} {f′ a} (fW a)
    admit-wk (T.mergeᶠ (just n)) a = readB-wk τ (FlatKit.Flat.active st) λ c →
      if-wk τ (c <ᵇ n) (start-wk {f a} {f′ a} (fW a)) (modifyF-wk τ (FlatKit.Flat.queue st) (_++ [ a ]))
    admit-wk T.switchᶠ           a = seq-wk≗ τ M.killAll (M.start (f a)) (killAll-wk τ st) (start-wk {f a} {f′ a} (fW a))
    admit-wk T.exhaustᶠ          a = readB-wk τ (FlatKit.Flat.active st) λ c → when-wk τ (c ≡ᵇ 0) (start-wk {f a} {f′ a} (fW a))

    dequeue-wk : wkAct τ M.dequeue ≗ M′.dequeue
    dequeue-wk = readRef≗ refl λ where
      σ []       → ≗-trans (≗-sym (wk-wk τ σ M.settle)) (wk≗ σ settle-wk)
      σ (a ∷ as) → writeRef≗ (sym (wk∋-wk τ σ (FlatKit.Flat.queue st))) refl
                     (≗-trans (≗-sym (wk-wk τ σ (M.start (f a)))) (wk≗ σ (start-wk {f a} {f′ a} (fW a))))

  ----------------------------------------------------------------------
  -- The observers and continuations a walk builds, weakened

  scan-wk : ∀ {w v A B} (τ : w ⊑ v) (f : B → A → B) (r : Ref w (base B)) {o : Observer B w} {o′} → ObsRel (wkObs τ o) o′
          → ObsRel (wkObs τ (Canon.scanO f r o)) (Canon.scanO f (wkR τ r) o′)
  scan-wk τ f r (n , cm , x) = (λ a → readB-wk τ r λ b → writeRef≗ refl refl (n (f b a))) , cm , x

  take-wk : ∀ {w v A} (τ : w ⊑ v) i (p : A → Bool) (c : Kit.Cut w) {o : Observer A w} {o′} → ObsRel (wkObs τ o) o′
          → ObsRel (wkObs τ (Canon.takeWhileO i p c o)) (Canon.takeWhileO i p (Kit.wkCut τ c) o′)
  take-wk τ i p c {o} (n , cm , x) = guarded-wk τ c
    ( (λ a → if-wk τ (p a) (n a)
               (seq-wk≗ τ (Kit.when i (under (ix 0) (Observer.next o a) Kit.skipᴬ)) (under last (Observer.complete o) (Kit.cut c))
                  (when-wk τ i (under≗ (n a) (≗-refl _))) (under≗ cm (cut-wk τ c))))
    , cm , x )

  body-wk : ∀ {w v B} (τ : w ⊑ v) (c : Kit.Cut w) {o : Observer B w} {o′} → ObsRel (wkObs τ o) o′
          → ObsRel (wkObs τ (Canon.bodyO c o)) (Canon.bodyO (Kit.wkCut τ c) o′)
  body-wk τ c {o} (n , cm , x) = n , seq-wk≗ τ (Observer.complete o) (Kit.cut c) cm (cut-wk τ c) , x

  feeder-wk : ∀ {w v A} (τ : w ⊑ v) (S : Subject A w) → ObsRel (wkObs τ (Canon.feeder S)) (Canon.feeder (wkSubject τ S))
  feeder-wk τ S = (λ a → readRef≗ refl λ _ _ → ≗-refl _) , writeRef≗ refl refl (readRef≗ refl λ _ _ → ≗-refl _) , readRef≗ refl λ _ _ → ≗-refl _

  outer-wk : ∀ {w v Δ A B} (τ : w ⊑ v) (op : T.FlatOp) (f : A → T.Obs Timeline Δ B) {E : Env Δ w} {E′} {o : Observer B w} {o′}
             (fl : FlatKit.Flat A w) (oc : Kit.Cut w) → wkEnv τ E ≡ E′ → ObsRel (wkObs τ o) o′
           → ObsRel (wkObs τ (Canon.Flat′.outerO op f E o fl oc)) (Canon.Flat′.outerO op f E′ o′ (FlatKit.wkFlat τ fl) (Kit.wkCut τ oc))
  outer-wk τ op f {E} {E′} {o} {o′} fl oc e oR = guarded-wk τ oc ((λ a → F.admit-wk op a) , writeRef≗ refl refl F.settle-wk , proj₂ (proj₂ oR))
    where
      env-step : ∀ {x} (σ : _ ⊑ x) → wkEnv (τ ⨾ σ) E ≡ wkEnv σ E′
      env-step σ = trans (sym (wkEnv-wk τ σ E)) (cong (wkEnv σ) e)
      module F = FlatWk τ op (λ a → compile (f a) E) (λ a → compile (f a) E′) o o′ fl
                   (λ a σ pR kR → ≗-trans (compile-at (f a) E E′ (τ ⨾ σ) σ (env-step σ)) (compile-cong (f a) E′ σ pR kR)) oR

  laneO-wk : ∀ {w v Δ A B} (τ : w ⊑ v) (op : T.FlatOp) (f : A → T.Obs Timeline Δ B) {E : Env Δ w} {E′} {o : Observer B w} {o′}
             (fl : FlatKit.Flat A w) (c : Kit.Cut w) → wkEnv τ E ≡ E′ → ObsRel (wkObs τ o) o′
           → ObsRel (wkObs τ (Canon.Flat′.laneO op f E o fl c)) (Canon.Flat′.laneO op f E′ o′ (FlatKit.wkFlat τ fl) (Kit.wkCut τ c))
  laneO-wk τ op f {E} {E′} {o} {o′} fl c e oR = guarded-wk τ c
    ( (λ a → ≗-trans (wk≗ τ (wk-same (Observer.next o a))) (≗-trans (proj₁ oR a) (≗-sym (wk-same _))))
    , writeRef≗ refl refl
        (seq-wk≗ τ (Kit.modifyB (FlatKit.Flat.active fl) pred) (readRef (FlatKit.Flat.refill fl) λ τ′ → M.handOn (same⊑ ⨾ τ′))
          (modifyB-wk τ (FlatKit.Flat.active fl) pred)
          (readRef≗ refl λ τ′ r → subst (λ ζ → M.handOn ζ r ≗ M′.handOn (same⊑ ⨾ τ′) r) (trans (cong (τ ⨾_) (same-⨾ τ′)) (sym (same-⨾ (τ ⨾ τ′))))
                                    (F.handOn-wk (same⊑ ⨾ τ′) r)))
    , ≗-trans (wk≗ τ (wk-same (Observer.closed o))) (≗-trans (proj₂ (proj₂ oR)) (≗-sym (wk-same _))) )
    where
      env-step : ∀ {x} (σ : _ ⊑ x) → wkEnv (τ ⨾ σ) E ≡ wkEnv σ E′
      env-step σ = trans (sym (wkEnv-wk τ σ E)) (cong (wkEnv σ) e)
      module M  = FlatKit.FlatMap op (λ a → compile (f a) E) o fl
      module M′ = FlatKit.FlatMap op (λ a → compile (f a) E′) o′ (FlatKit.wkFlat τ fl)
      module F = FlatWk τ op (λ a → compile (f a) E) (λ a → compile (f a) E′) o o′ fl
                   (λ a σ pR kR → ≗-trans (compile-at (f a) E E′ (τ ⨾ σ) σ (env-step σ)) (compile-cong (f a) E′ σ pR kR)) oR

  -- A lane begun past a growth: its observer read at the growth over the
  -- old cells, or in the grown world over the weakened ones.
  laneAt-wk : ∀ {w v Δ A B} (τ : w ⊑ v) (op : T.FlatOp) (f : A → T.Obs Timeline Δ B) {E : Env Δ w} {E′} {o : Observer B w} {o′}
              (fl : FlatKit.Flat A w) (c : Kit.Cut v) → wkEnv τ E ≡ E′ → ObsRel (wkObs τ o) o′
            → ObsRel (Kit.guarded c (Canon.Flat′.lane op f E o fl τ c)) (Canon.Flat′.laneO op f E′ o′ (FlatKit.wkFlat τ fl) c)
  laneAt-wk τ op f {E} {E′} {o} {o′} fl c e oR = guarded-cong c (F.lane-wk same⊑ c)
    where
      env-step : ∀ {x} (σ : _ ⊑ x) → wkEnv (τ ⨾ σ) E ≡ wkEnv σ E′
      env-step σ = trans (sym (wkEnv-wk τ σ E)) (cong (wkEnv σ) e)
      module F = FlatWk τ op (λ a → compile (f a) E) (λ a → compile (f a) E′) o o′ fl
                   (λ a σ pR kR → ≗-trans (compile-at (f a) E E′ (τ ⨾ σ) σ (env-step σ)) (compile-cong (f a) E′ σ pR kR)) oR

  refill-wk : ∀ {w v Δ A B} (τ : w ⊑ v) (op : T.FlatOp) (f : A → T.Obs Timeline Δ B) {E : Env Δ w} {E′} {o : Observer B w} {o′}
              (fl : FlatKit.Flat A w) → wkEnv τ E ≡ E′ → ObsRel (wkObs τ o) o′
            → CbRel (wkVal (slot ⊤) τ (Canon.Flat′.refillCb op f E o fl)) (Canon.Flat′.refillCb op f E′ o′ (FlatKit.wkFlat τ fl))
  refill-wk τ op f {E} {E′} {o} {o′} fl e oR = (λ _ → F.dequeue-wk) , ≗-refl _ , ≗-refl _
    where
      env-step : ∀ {x} (σ : _ ⊑ x) → wkEnv (τ ⨾ σ) E ≡ wkEnv σ E′
      env-step σ = trans (sym (wkEnv-wk τ σ E)) (cong (wkEnv σ) e)
      module F = FlatWk τ op (λ a → compile (f a) E) (λ a → compile (f a) E′) o o′ fl
                   (λ a σ pR kR → ≗-trans (compile-at (f a) E E′ (τ ⨾ σ) σ (env-step σ)) (compile-cong (f a) E′ σ pR kR)) oR

  readG-wk : ∀ {w v B} (τ : w ⊑ v) (r : Ref w gate) {k : Bool → Act w B} {k′ : Bool → Act v B} → (∀ x → wkAct τ (k x) ≗ k′ x)
           → wkAct τ (Kit.readG r k) ≗ Kit.readG (wkR τ r) k′
  readG-wk τ r {k} f = readRef≗ refl λ σ x → ≗-trans (≗-sym (wk-wk τ σ (k x))) (wk≗ σ (f x))

  joiner-wk : ∀ {w v A} (τ : w ⊑ v) (l : Ref w gate) {o : Observer A w} {o′} → ObsRel (wkObs τ o) o′
            → CbRel (wkVal (slot A) τ (Canon.joinerCb l o)) (Canon.joinerCb (wkR τ l) o′)
  joiner-wk τ l (n , cm , x) =
    (λ a → readG-wk τ l λ b → when-wk τ b (n a)) , readG-wk τ l (λ b → when-wk τ b cm) , readG-wk τ l (λ b → if-wk τ b x (≗-refl _))

  take-k : ∀ {w v} (τ : w ⊑ v) (c : Kit.Cut w) {k : Kont w} {k′ : Kont v} → KontRel (wkKont τ k) k′ → KontRel (wkKont τ (takeK c k)) (takeK (Kit.wkCut τ c) k′)
  take-k τ c {k} {k′} kR σ sub =
    subst (λ c′ → wkKont τ (takeK c k) σ sub ≗ (Kit.attach c′ sub >>ᴬ k′ σ (unsubscribing (Kit.cut c′)))) (sym (cut-eq τ σ c))
      (seq≗ (Kit.attach (Kit.wkCut (τ ⨾ σ) c) sub) (k (τ ⨾ σ) (unsubscribing (Kit.cut (Kit.wkCut (τ ⨾ σ) c)))) (≗-refl _) (kR σ _))

  flat-k : ∀ {w v A} (τ : w ⊑ v) (oc : Kit.Cut w) (fl : FlatKit.Flat A w) {k : Kont w} {k′ : Kont v} → KontRel (wkKont τ k) k′
         → KontRel (wkKont τ (flatK oc fl k)) (flatK (Kit.wkCut τ oc) (FlatKit.wkFlat τ fl) k′)
  flat-k τ oc fl {k} {k′} kR σ sub =
    subst₂ (λ c′ fl′ → wkKont τ (flatK oc fl k) σ sub ≗ (Kit.attach c′ sub >>ᴬ k′ σ (unsubscribing (Kit.cut c′ >>ᴬ killAllᶜ fl′))))
           (sym (cut-eq τ σ oc)) (sym (wkFlat-wk τ σ fl))
      (seq≗ (Kit.attach (Kit.wkCut (τ ⨾ σ) oc) sub) (k (τ ⨾ σ) (unsubscribing (Kit.cut (Kit.wkCut (τ ⨾ σ) oc) >>ᴬ killAllᶜ (FlatKit.wkFlat (τ ⨾ σ) fl))))
            (≗-refl _) (kR σ _))

  lane-k : ∀ {w v} (τ : w ⊑ v) (c : Kit.Cut w) → KontRel (wkKont τ (laneK c)) (laneK (Kit.wkCut τ c))
  lane-k τ c σ sub = subst (λ c′ → Kit.attach (Kit.wkCut (τ ⨾ σ) c) sub ≗ Kit.attach c′ sub) (sym (cut-eq τ σ c)) (≗-refl _)

  body-k : ∀ {w v} (τ : w ⊑ v) (b : Ref w (maybe quiet)) → KontRel (wkKont τ (bodyK b)) (bodyK (wkR τ b))
  body-k τ b σ U = stash≗ (≗-refl _) λ π′ t →
    writeRef≗ (trans (cong (λ ζ → wkR ζ b) (sym (⨾-assoc τ σ π′))) (sym (wk∋-wk τ (σ ⨾ π′) b))) refl (≗-refl _)

  src-k : ∀ {w v} (τ : w ⊑ v) (c : Kit.Cut w) (b : Ref w (maybe quiet)) {k : Kont w} {k′ : Kont v} → KontRel (wkKont τ k) k′
        → KontRel (wkKont τ (srcK c b k)) (srcK (Kit.wkCut τ c) (wkR τ b) k′)
  src-k τ c b {k} {k′} kR σ src =
    subst (λ c′ → wkKont τ (srcK c b k) σ src ≗ (Kit.attach c′ src >>ᴬ readRef (wkR σ (wkR τ b)) λ ψ′ mb → k′ (σ ⨾ ψ′) (U ψ′ mb))) (sym (cut-eq τ σ c))
      (seq≗ (Kit.attach (Kit.wkCut (τ ⨾ σ) c) src) (readRef (wkR (τ ⨾ σ) b) λ ψ′ mb → k ((τ ⨾ σ) ⨾ ψ′) (U ψ′ mb)) (≗-refl _)
        (readRef≗ (sym (wk∋-wk τ σ b)) λ ψ′ mb → subst (λ ζ → k ζ (U ψ′ mb) ≗ k′ (σ ⨾ ψ′) (U ψ′ mb)) (⨾-assoc τ σ ψ′) (kR (σ ⨾ ψ′) (U ψ′ mb))))
    where
      U : ∀ {y} (ψ′ : _ ⊑ y) → Maybe (Quiet y) → Subscription y
      U ψ′ mb = unsubscribing (Subscription.unsubscribe (wkSubn ψ′ src) >>ᴬ Kit.unsubscribeVia mb)

  defer-k : ∀ {w v} (τ : w ⊑ v) {k : Kont w} {k′ : Kont v} → KontRel (wkKont τ k) k′ → KontRel (wkKont τ (deferK k)) (deferK k′)
  defer-k τ {k} {k′} kR σ sub = stash≗ (≗-refl _) λ τ′ t →
    subst (λ ζ → k ζ (unsubscribing (cancel t (done tt))) ≗ k′ (σ ⨾ τ′) (unsubscribing (cancel t (done tt)))) (⨾-assoc τ σ τ′)
      (kR (σ ⨾ τ′) (unsubscribing (cancel t (done tt))))

  ----------------------------------------------------------------------
  -- A walk along a weakened path

  -- What a walk hands, weakened: its observer and continuation up to
  -- `_≗_`, its subjects exactly.
  HereRel : ∀ {h v Δ A} → h ⊑ v → Here h Δ A → Here v Δ A → Set₁
  HereRel τ H H′ = ObsRel (wkObs τ (Here.obs H)) (Here.obs H′) × KontRel (wkKont τ (Here.kont H)) (Here.kont H′) × wkEnv τ (Here.env H) ≡ Here.env H′

  mutual
    walk-rel : ∀ {h v Δ A Δ′ A′} (τ : h ⊑ v) {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (H : Here h Δ A) (H′ : Here v Δ A)
             → HereRel τ H H′ → HereRel τ (walk π H) (walk (wkPath τ π) H′)
    walk-rel τ here H H′ r = r
    walk-rel τ (in-map {f = f} p) (ctx o k E) (ctx o′ k′ E′) ((n , cm , x) , kR , e) =
      walk-rel τ p (ctx (Canon.mapO f o) k E) (ctx (Canon.mapO f o′) k′ E′) (((λ a → n (f a)) , cm , x) , kR , e)
    walk-rel τ (in-scan {f = f} {r} p) (ctx o k E) (ctx o′ k′ E′) (oR , kR , e) =
      walk-rel τ p (ctx (Canon.scanO f r o) k E) (ctx (Canon.scanO f (wkR τ r) o′) k′ E′) (scan-wk τ f r oR , kR , e)
    walk-rel τ (in-take {i = i} {q} {c} p) (ctx o k E) (ctx o′ k′ E′) (oR , kR , e) =
      walk-rel τ p (ctx (Canon.takeWhileO i q c o) (takeK c k) E) (ctx (Canon.takeWhileO i q (Kit.wkCut τ c) o′) (takeK (Kit.wkCut τ c) k′) E′)
        (take-wk τ i q c oR , take-k τ c {k} {k′} kR , e)
    walk-rel τ (in-outer {op = op} {f} {fl} {oc} p) (ctx o k E) (ctx o′ k′ E′) (oR , kR , e) =
      walk-rel τ p (ctx (Canon.Flat′.outerO op f E o fl oc) (flatK oc fl k) E)
                   (ctx (Canon.Flat′.outerO op f E′ o′ (FlatKit.wkFlat τ fl) (Kit.wkCut τ oc)) (flatK (Kit.wkCut τ oc) (FlatKit.wkFlat τ fl) k′) E′)
        (outer-wk τ op f fl oc e oR , flat-k τ oc fl {k} {k′} kR , e)
    walk-rel τ (in-lanes {op = op} {f} {fl} p) H H′ r = walkLanes-rel τ op f fl p H H′ r
    walk-rel τ (in-source {S = S} {c} {b} p) (ctx o k E) (ctx o′ k′ E′) (oR , kR , e) =
      walk-rel τ p (ctx (Canon.feeder S) (srcK c b k) E) (ctx (Canon.feeder (wkSubject τ S)) (srcK (Kit.wkCut τ c) (wkR τ b) k′) E′)
        (feeder-wk τ S , src-k τ c b {k} {k′} kR , e)
    walk-rel τ (in-body {S = S} {c} {b} p) (ctx o k E) (ctx o′ k′ E′) (oR , kR , e) =
      walk-rel τ p (ctx (Canon.bodyO c o) (bodyK b) (S ∷ E)) (ctx (Canon.bodyO (Kit.wkCut τ c) o′) (bodyK (wkR τ b)) (wkSubject τ S ∷ E′))
        (body-wk τ c oR , body-k τ b , cong (wkSubject τ S ∷_) e)
    walk-rel τ (in-defer p) (ctx o k E) (ctx o′ k′ E′) (oR , kR , e) =
      walk-rel τ p (ctx o (deferK k) E) (ctx o′ (deferK k′) E′) (oR , defer-k τ {k} {k′} kR , e)

    walkLanes-rel : ∀ {h v Δ A B Δ′ C} (τ : h ⊑ v) (op : T.FlatOp) (f : A → T.Obs Timeline Δ B) (fl : FlatKit.Flat A h)
                    {ls : List (Lane h Δ B)} {u : Sub h Δ′ C} (π : PathLanes ls u) (H : Here h Δ B) (H′ : Here v Δ B)
                  → HereRel τ H H′ → HereRel τ (walkLanes op f fl H π) (walkLanes op f (FlatKit.wkFlat τ fl) H′ (wkPathᴸ τ π))
    walkLanes-rel τ op f fl (this-lane {c = c} p) (ctx o k E) (ctx o′ k′ E′) (oR , kR , e) =
      walk-rel τ p (ctx (Canon.Flat′.laneO op f E o fl c) (laneK c) E)
                   (ctx (Canon.Flat′.laneO op f E′ o′ (FlatKit.wkFlat τ fl) (Kit.wkCut τ c)) (laneK (Kit.wkCut τ c)) E′)
        (laneO-wk τ op f fl c e oR , lane-k τ c , e)
    walkLanes-rel τ op f fl (next-lane p) H H′ r = walkLanes-rel τ op f fl p H H′ r

  -- A walk along the weakened path hands the weakened observer and
  -- continuation, up to `_≗_`, and the weakened subjects.
  walk-grow : ∀ {h v Δ A} (τ : h ⊑ v) {t : Sub h [] R} {u : Sub h Δ A} (π : Path t u) → HereRel τ (walk π top) (walk (wkPath τ π) top)
  walk-grow τ π = walk-rel τ π top top (((λ _ → ≗-refl _) , ≗-refl _ , ≗-refl _) , (λ _ _ → ≗-refl _) , refl)

