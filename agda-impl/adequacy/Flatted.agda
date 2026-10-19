{-# OPTIONS --guardedness #-}

-- A FLATMAP RESTAGED in the world grown by its kit.
module adequacy.Flatted where

open import Data.List using (List; []; _∷_; _++_; [_]; length) renaming (map to mapᴸ)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (tabulate to tabulateᴬ; lookup to lookupᴬ; map to all-map)
open import Data.List.Relation.Unary.Any using () renaming (here to hereᴬ; there to thereᴬ)
open import Data.List.Relation.Unary.Any.Properties using () renaming (++⁻ to any-++⁻; ++⁺ˡ to any-++⁺ˡ; ++⁺ʳ to any-++⁺ʳ)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁻ to all-++⁻)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_) renaming (map to pairs-map)
open import Data.List.Relation.Unary.Linked using ([]; _∷_)
open import Data.List.Relation.Unary.AllPairs.Properties using () renaming (map⁺ to pairs-map⁺; ++⁺ to pairs-++⁺)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_; ↭-sym; ↭-trans; ↭-reflexive) renaming (refl to ↭-refl′; prep to ↭-prep′; swap to ↭-swap′; trans to ↭-trans′)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (All-resp-↭; shifts) renaming (++⁺ˡ to ↭-++⁺ˡ; ++⁺ʳ to ↭-++⁺ʳ)
open import Data.List.Properties using (map-++; ++-assoc) renaming (++-identityʳ to ++-idʳ)
open import Data.Maybe using (Maybe; just; nothing; is-just) renaming (map to mapMaybe)
open import Data.Nat using (ℕ; _<_; s≤s)
open import Data.Nat.Properties using (≤-reflexive; +-identityʳ)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Sum using (inj₁)
open import Data.Unit using (⊤)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤₁; tt to tt₁)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Relation.Nullary using (¬_)
open import Level using (lift)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst; subst₂)

open import denotation.MonotonicList using (Timeline; Frame; From; Pos; ix; last; tick; at; _<ᵖ_; <ᵖ-below) renaming (done to doneᶠᵐ; quiet to quietᶠᵐ)
open import denotation.MonotonicList using () renaming (sub to subᴾ)
import Tree as T
import denotation.Unfold as U
open import operation.Machine using (module Machine)
open import operation.PureObservable using (Out; Pureᴾ)
open import operation.AbstractObservable using (module Heap; module Run) renaming (module Machine to Shared)
open import adequacy.Strong using (module Strongly)
open import adequacy.Moves using (module Moving)
open import adequacy.Every using (module Everywhere)
open import adequacy.Ghost using (module Ghosting)
open import adequacy.Unsub using (module Unsubbing)
open import adequacy.Seq using (module Sequencing)
open import operation.AbstractObservable using (base; maybe; quiet; sink; list; fifo)
open import operation.PureObservable using (module Pure)
open import adequacy.Fork using (module Forking)
open import adequacy.Kept using (module Keeping)
open import adequacy.Moved using (module Planting)
open import adequacy.Restages using (module Staging)
open import adequacy.Names using (module Naming)
open import adequacy.Alike using (module Aliking)
open import adequacy.Taken using (module Taking)
open import adequacy.Connected using (module Connecting)

module Flatting (R : Set) where
  open Machine R using (Mach; mach; step; wkPlaying; wkTodo)
  open Unsubbing R using (now; then; ≗-trans; wk≗; bind≗; wk-same; from-same)
  open Sequencing R using (wkEl-wk)
  open Pure R using (wkTimer; mapList)
  open Shared Timeline (Out R) using (Heapᴹ; ⟨_,_,_⟩; Stack; run; extend; look; store; Callbacks)
  open Heap using (World; _⊑_; _⨾_; there; new; grow; cell; slot; Sink) renaming (here to hereʳ; same to same⊑)
  open Run (Pureᴾ R) using (Act; done; writeRef; register; _>>ᴬ_; compile; Env; wkEnv; wkAct; module Kit; module FlatKit; Ref; wkR; Observer; Kont; wkObs; Subscription; Subscribe; wkSub)
  open Run.Kit (Pureᴾ R) using (skipᴬ)
  open Strongly R using (Carried; Books; Sub; pendingˢ; Path; here; in-outer; in-lanes; _⊕_; Here; walk; top; Job; _≗_; module At; Owned; Kernels; Meaning; Queue; Each; Heads; Lingers; names; pendings; Phase; unpinned; union-pinned; rest-pinned; seen; flatMapˢ; killAllᶜ; flatK; CbRel; ≗-refl; newRef≗; unsubscribing; register≗; writeRef≗; module Canon; owned-to; module Eaching; module Lingering)
  open Strongly.Against R using (subAs; SrcOf; src-of)
  open Moving R using (planted; pend; part-plant; holds-owed; fed-plant; pendings-plant; subjects-plant; joiners-plant)
  open Everywhere.Settling R using (settled-plant)
  open Everywhere.Gating R using (gated-plant)
  open Ghosting R using (walk-⊕; sorted-⇝)
  open Forking R using (pend-less; subOf; walk-planted)
  open Keeping R using (each-plant; lingers-plant; pooled-fresh)
  open Planting R using (module Moved)
  open Staging R using (Restages; not-src; wrap-outer)
  open Naming R using (fresh-new; fresh-plant; pending-↭; walk-kont-sub)
  open Aliking R using (KontRel; ObsRel; compile-cong; guarded-cong; killAll-wk; obs-sym; obs-trans; obs-⨾; wkFlat-wk)
  open Taking R using (allocates; recode; ⊑≗)
  open Connecting R using (Grew; grew-step; grew-store)

  -- The world a flatMap's kernel allocates: its count, outer flag, queue,
  -- lanes and refill cell, its outer's cut, the refill's slot.
  flatWorld : World → Set → World
  flatWorld h A = slot ⊤ ∷ cell (maybe quiet) ∷ cell (base Bool) ∷ cell (maybe (sink ⊤)) ∷ cell (list Kit.cutTy) ∷ cell (fifo A)
                ∷ cell (base Bool) ∷ cell (base ℕ) ∷ h

  flatGrown : ∀ {h A} → h ⊑ flatWorld h A
  flatGrown = grow (grow (grow (grow (grow (grow (grow (grow same⊑)))))))

  -- A register's parts, as functions.
  registers : ∀ {w B A} {n′ : A → Act w ⊤} {c′ : Act w ⊤} {x′ : Act w Bool} {k′ : ∀ {v} → w ⊑ v → Sink v A → Act v B} {m : Act w B}
            → m ≗ register n′ c′ x′ k′
            → Σ (A → Act w ⊤) λ n → Σ (Act w ⊤) λ c → Σ (Act w Bool) λ x → Σ (∀ {v} → w ⊑ v → Sink v A → Act v B) λ k
              → m ≡ register n c x k × (∀ a → n a ≗ n′ a) × c ≗ c′ × x ≗ x′ × (∀ {v} (σ : w ⊑ v) r → k σ r ≗ k′ σ r)
  registers (register≗ en ec ex ek) = _ , _ , _ , _ , refl , en , ec , ex , ek

  -- A write's continuation.
  writes : ∀ {w B t} {r : Ref w t} {a} {k′ : Act w B} {m : Act w B} → m ≗ writeRef r a k′ → Σ (Act w B) λ k → m ≡ writeRef r a k × k ≗ k′
  writes (writeRef≗ refl refl ek) = _ , refl , ek

  -- A FLATMAP RESTAGED IN THE WORLD ITS KERNEL GREW: its pool, its
  -- outer's cut and its refill slot the newest entries, the refill cell
  -- holding the slot, its outer pending beneath it, no lane begun.
  module Flatted {h₀} {H₀ : Heapᴹ h₀} {T₀ : Sub h₀ [] R} {Δ A B} {op : T.FlatOp} {f : A → T.Obs Timeline Δ B} {s : T.Obs Timeline Δ A} {q}
                 {π₀ : Path T₀ (pendingˢ (T.flatMap op f s) q)} {u} {E′ : Env Δ u} {υ : u ⊑ h₀} {w} {σ : w ⊑ h₀} {K : Stack w ⊤} {clk}
                 {H₉ : Heapᴹ (flatWorld h₀ A)} {bs ts}
                 (G₉ : Grew H₀ π₀ E′ υ σ K clk flatGrown H₉ bs ts) where
    h₇ h₈ : World
    h₇ = cell (maybe quiet) ∷ cell (base Bool) ∷ cell (maybe (sink ⊤)) ∷ cell (list Kit.cutTy) ∷ cell (fifo A) ∷ cell (base Bool) ∷ cell (base ℕ) ∷ h₀
    h₈ = flatWorld h₀ A

    ν₇ : h₀ ⊑ h₇
    ν₇ = grow (grow (grow (grow (grow (grow (grow same⊑))))))

    ν₈ : h₀ ⊑ h₈
    ν₈ = flatGrown

    O : Observer B h₀
    O = Here.obs (walk π₀ top)

    Kt : Kont h₀
    Kt = Here.kont (walk π₀ top)

    -- The kernel's pool and outer cut, as it allocated them.
    st₇ : FlatKit.Flat A h₇
    st₇ = record { active = wkR (grow (grow (grow (grow (grow (grow same⊑)))))) hereʳ ; outerDone = wkR (grow (grow (grow (grow (grow same⊑))))) hereʳ
                 ; queue = wkR (grow (grow (grow (grow same⊑)))) hereʳ ; lanes = wkR (grow (grow (grow same⊑))) hereʳ ; refill = wkR (grow (grow same⊑)) hereʳ }

    oc₇ : Kit.Cut h₇
    oc₇ = wkR new hereʳ , hereʳ

    f₇ : A → Subscribe B h₇
    f₇ a = wkSub (υ ⨾ ν₇) (compile (f a) E′)

    O₇ : Observer B h₇
    O₇ = wkObs ν₇ O

    module FM₇ = FlatKit.FlatMap op f₇ O₇ st₇

    -- What the kernel hands its outer once the refill slot is stored.
    KO : Observer A h₈
    KO = Kit.guarded (Kit.wkCut new oc₇) (record { next = λ a → wkAct new (FM₇.admit op a)
                                                 ; complete = writeRef (FlatKit.Flat.outerDone (FlatKit.wkFlat new st₇)) true (wkAct new FM₇.settle)
                                                 ; closed = Observer.closed (wkObs new O₇) })

    KK : Kont h₈
    KK τ sub = Kit.attach (Kit.wkCut (new ⨾ τ) oc₇) sub
               >>ᴬ Kt (ν₇ ⨾ (new ⨾ τ)) (unsubscribing (Kit.cut (Kit.wkCut (new ⨾ τ) oc₇) >>ᴬ wkAct (new ⨾ τ) FM₇.killAll))

    -- The refill slot's callbacks as the kernel registered them.
    kcb : Callbacks ⊤ h₈
    kcb = record { onNext = λ _ → wkAct new FM₇.dequeue ; onComplete = skipᴬ ; isClosed = done false }

    fl₈ : FlatKit.Flat A h₈
    fl₈ = FlatKit.wkFlat new st₇

    oc₈ : Kit.Cut h₈
    oc₈ = Kit.wkCut new oc₇

    T₈ : Sub h₈ [] R
    T₈ = Grew.tree G₉

    π₈ : Path T₈ (pendingˢ (T.flatMap op f s) q)
    π₈ = Grew.path G₉

    W₈ : Here h₈ Δ B
    W₈ = walk π₈ top

    E₈ : Env Δ h₈
    E₈ = Here.env W₈

    O₈ : Observer B h₈
    O₈ = Here.obs W₈

    K₈ : Kont h₈
    K₈ = Here.kont W₈

    v : Sub h₈ Δ B
    v = flatMapˢ op f fl₈ oc₈ nothing hereʳ U.idleᶜ (pendingˢ s q) []

    open Moved π₈ v using (t′; restack; reticked) public

    ρf : Path t′ v
    ρf = planted π₈ v

    ιo : Path v (pendingˢ s q)
    ιo = in-outer here

    π′ : Path t′ (pendingˢ s q)
    π′ = ρf ⊕ ιo

    walk′ : walk π′ top ≡ walk ιo W₈
    walk′ = trans (walk-⊕ ρf ιo top) (cong (walk ιo) (walk-planted π₈ v top))

    o-rel : ObsRel (wkObs new O₇) O₈
    o-rel = obs-trans (obs-sym (obs-⨾ ν₇ new O)) (Grew.obsR G₉)

    -- The flatMap's kernel, weakened, read as the node's: its admit,
    -- settle and dequeue over the inner programs as the node compiles
    -- them and its observer.
    --
    -- RECOVERY: git show 188b9050f2 restores the inner programs as the kernel subscribes them related to the node's, and the kernel's weakening generic over related inners.
    postulate
      flat-wk-here : (∀ b a → wkAct new (FlatKit.FlatMap.admit op f₇ O₇ st₇ b a) ≗ FlatKit.FlatMap.admit op (λ a → compile (f a) E₈) O₈ (FlatKit.wkFlat new st₇) b a)
                   × wkAct new (FlatKit.FlatMap.settle op f₇ O₇ st₇) ≗ FlatKit.FlatMap.settle op (λ a → compile (f a) E₈) O₈ (FlatKit.wkFlat new st₇)
                   × wkAct new (FlatKit.FlatMap.dequeue op f₇ O₇ st₇) ≗ FlatKit.FlatMap.dequeue op (λ a → compile (f a) E₈) O₈ (FlatKit.wkFlat new st₇)

    outer-rel : ObsRel KO (Canon.Flat′.outerO op f E₈ O₈ fl₈ oc₈)
    outer-rel = guarded-cong oc₈ ((λ a → proj₁ flat-wk-here op a) , writeRef≗ refl refl (proj₁ (proj₂ flat-wk-here)) , proj₂ (proj₂ o-rel))

    kont-rel : KontRel KK (flatK oc₈ fl₈ K₈)
    kont-rel τ sub = bind≗ att λ _ → ≗-trans (⊑≗ (λ z → Kt z U₁) (ν₇ ⨾ (new ⨾ τ)) (ν₈ ⨾ τ)) (≗-trans (Grew.kontR G₉ τ U₁) (walk-kont-sub π₈ τ ue))
      where
        U₁ = unsubscribing (Kit.cut (Kit.wkCut (new ⨾ τ) oc₇) >>ᴬ wkAct (new ⨾ τ) FM₇.killAll)
        cw : Kit.wkCut (new ⨾ τ) oc₇ ≡ Kit.wkCut τ oc₈
        cw = sym (wkEl-wk Kit.cutTy new τ oc₇)
        att : Kit.attach (Kit.wkCut (new ⨾ τ) oc₇) sub ≗ Kit.attach (Kit.wkCut τ oc₈) sub
        att = subst (λ c → Kit.attach (Kit.wkCut (new ⨾ τ) oc₇) sub ≗ Kit.attach c sub) cw (≗-refl _)
        ue : Subscription.unsubscribe U₁ ≗ (Kit.cut (Kit.wkCut τ oc₈) >>ᴬ killAllᶜ (FlatKit.wkFlat τ fl₈))
        ue = bind≗ (subst (λ c → Kit.cut (Kit.wkCut (new ⨾ τ) oc₇) ≗ Kit.cut c) cw (≗-refl _)) λ _ →
             subst (λ st → wkAct (new ⨾ τ) FM₇.killAll ≗ killAllᶜ st) (sym (wkFlat-wk new τ st₇)) (killAll-wk (new ⨾ τ) st₇)

    -- The outer compiles as the kernel began it, under the flatMap's
    -- outer observer and continuation over the grown walk.
    code′ : ∀ {act} → act ≗ compile s E′ (υ ⨾ ν₈) KO KK
          → Σ World λ u′ → Σ (Env Δ u′) λ E″ → Σ (u′ ⊑ h₈) λ υ′ → wkEnv υ′ E″ ≡ Here.env (walk π′ top)
                         × act ≗ compile s E″ υ′ (Here.obs (walk π′ top)) (Here.kont (walk π′ top))
    code′ {act} c = u , E′ , υ ⨾ ν₈
      , subst (λ W → wkEnv (υ ⨾ ν₈) E′ ≡ Here.env W) (sym walk′) (Grew.envR G₉)
      , subst (λ W → act ≗ compile s E′ (υ ⨾ ν₈) (Here.obs W) (Here.kont W)) (sym walk′)
          (≗-trans c (compile-cong s E′ (υ ⨾ ν₈) outer-rel kont-rel))

    alone : ∀ {k} → ¬ SrcOf t′ π′ k
    alone (src-of ρ e) = not-src wrap-outer ρf ρ e

    alones : ∀ (js : List (Job t′)) → All (λ j → ¬ SrcOf t′ π′ (proj₂ j)) js
    alones _ = tabulateᴬ (λ _ → alone)

    less : pend t′ < pend T₈
    less = pend-less π₈ v (s≤s (≤-reflexive (+-identityʳ _)))

    -- A flatMap over a pending outer and no lane holds nothing a call is
    -- owed at, and one pending node: its outer.
    inner : Moved.Inner π₈ v ιo
    inner = record { no-of = λ { (in-outer ()) ; (in-lanes ()) } ; no-cold = λ { (in-outer ()) ; (in-lanes ()) }
                   ; one-pend = λ { (in-outer here) → refl ; (in-lanes ()) }
                   ; no-end = λ { (in-outer ()) ; (in-lanes ()) } ; no-cut = λ { (in-outer ()) ; (in-lanes ()) }
                   ; no-feed = λ { (in-outer ()) ; (in-lanes ()) } ; no-fin = λ { (in-outer ()) ; (in-lanes ()) }
                   ; not-self = λ _ () }

    -- The pool's, cut's and slot's names are names the tree did not hold.
    flat-fresh : AllPairs _≢_ (names T₀) → AllPairs _≢_ (names t′)
    flat-fresh fs = fresh-plant π₈ v (pending-↭ v) (((λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ []) ∷ ((λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ []) ∷ ((λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ []) ∷ ((λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ []) ∷ ((λ ()) ∷ (λ ()) ∷ (λ ()) ∷ []) ∷ ((λ ()) ∷ (λ ()) ∷ []) ∷ ((λ ()) ∷ []) ∷ ([]) ∷ [])
      (Grew.distinct G₉ fs) (fresh-new ν₈ (λ { {_ , _} m∈ → Grew.named G₉ m∈ }) ((λ { {_ , _} (_ , refl) () }) ∷ (λ { {_ , _} (_ , refl) () }) ∷ (λ { {_ , _} (_ , refl) () }) ∷ (λ { {_ , _} (_ , refl) () }) ∷ (λ { {_ , _} (_ , refl) () }) ∷ (λ { {_ , _} (_ , refl) () }) ∷ (λ { {_ , _} (_ , refl) () }) ∷ (λ { {_ , _} (_ , refl) () }) ∷ []))

    postulate
      -- The outer heads no earlier than the flatMap over it, no lane begun.
      unflat     : ∀ {k} {c : U.Node Δ A} → Heads k (U.flatMapᶜ op (λ a p → U.subscribe (f a) p) (just c) [] [] U.idleᶜ) → Heads k c

    module _ (eqv : At.part H₉ (pendingˢ (T.flatMap op f s) q) ≡ At.part H₉ v)
             (refill₉ : At.val H₉ (FlatKit.Flat.refill fl₈) ≡ just hereʳ) (slot₉ : CbRel (look H₉ hereʳ) kcb)
             (held₉ : At.val H₉ (Kit.held oc₈) ≡ nothing) (active₉ : At.val H₉ (FlatKit.Flat.active fl₈) ≡ 0)
             (lanes₉ : At.val H₉ (FlatKit.Flat.lanes fl₈) ≡ []) (done₉ : At.val H₉ (FlatKit.Flat.outerDone fl₈) ≡ false) where

      slotR : CbRel (look H₉ hereʳ) (Canon.Flat′.refillCb op f E₈ O₈ fl₈)
      slotR = (λ a → ≗-trans (proj₁ slot₉ a) (proj₂ (proj₂ flat-wk-here))) , proj₁ (proj₂ slot₉) , proj₂ (proj₂ slot₉)

      rf-kernels : Kernels H₉ T₈ → Kernels H₉ t′
      rf-kernels kn = record { holds = holds-owed H₉ π₈ v tt (Here.kont top)
                                         (λ _ → refill₉ , slotR , lift held₉ , lift tt , active₉ , ([] , cong (_++ []) lanes₉ , []) , lift tt)
                                         (Kernels.settled kn) (Kernels.holds kn)
                             ; gated = gated-plant H₉ π₈ v (λ _ → lift tt , lift tt) (λ _ → lift tt , lift tt) (Kernels.gated kn)
                             ; settled = settled-plant H₉ π₈ v (λ _ → tt) (λ _ → tt , tt , tt) (Kernels.settled kn) }

      rf-meaning : Meaning H₉ T₈ → Meaning H₉ t′
      rf-meaning mn = record { fed = fed-plant H₉ π₈ v (λ _ _ → lift tt , lift tt) _ (Meaning.fed mn) }

      pendings′ : pendings t′ ≡ pendings T₈
      pendings′ with pendings-plant π₈ v
      ... | _ , _ , e , e′ = trans e′ (sym e)

      rf-queue : ∀ {k clk′ ts′} → Queue H₉ k clk′ ts′ T₈ → Queue H₉ k clk′ ts′ t′
      rf-queue {ts′ = ts′} qu =
        record { timed   = subst (At.Timed H₉ ts′) (sym pendings′) (Queue.timed qu)
               ; joined  = subst₂ (At.Joined H₉) (sym (subjects-plant π₈ v refl)) (sym (joiners-plant π₈ v (λ _ → refl) [])) (Queue.joined qu)
               ; ordered = Queue.ordered qu ; ahead = Queue.ahead qu }

      rf-behind : ∀ {k} → Each H₉ (Heads k) T₈ → Each H₉ (Heads k) t′
      rf-behind {k} = each-plant H₉ π₈ v eqv tr
        where
          pa : ∀ {Δ′ A′} {x : Sub h₈ Δ′ A′} → Each H₉ (Heads k) (pendingˢ (T.flatMap op f s) q) → (ψ : Path v x) → seen H₉ ψ ≡ true
             → ∀ {c} → At.part H₉ x ≡ just c → Heads k c
          pa eu here             _ pw   = Each.parts eu here refl (trans eqv pw)
          pa eu (in-outer here)  _ refl = unflat {c = U.subscribe s q} (Each.parts eu here refl refl)
          pa eu (in-lanes ())

          tr : Each H₉ (Heads k) (pendingˢ (T.flatMap op f s) q) → Each H₉ (Heads k) v
          tr eu = record { parts = pa eu ; pools = λ { here _ _ () ; (in-outer ()) ; (in-lanes ()) } ; rests = λ { (in-outer ()) ; (in-lanes ()) } }

      rf-owned : ∀ {act act′} {cd cd′} {a′} → Owned H₉ T₈ (subAs {act = act} π₈ cd (Grew.stack G₉) (Grew.alone G₉))
               → Owned H₉ t′ (subAs {act = act′} π′ cd′ (restack (Grew.stack G₉) (Grew.alone G₉)) a′)
      rf-owned = Moved.Owning.reowned π₈ v H₉ eqv ιo inner (Grew.stack G₉) (Grew.alone G₉)

      -- A flatMap pending its outer, its pool idle and no lane, runs what
      -- it was pending to.
      rf-lingers : Lingers H₉ T₈ → Lingers H₉ t′
      rf-lingers = lingers-plant H₉ π₈ v eqv (union-pinned (rest-pinned (U.subscribe s q)) unpinned)
        (record { pools = λ { here _ _ → pooled-fresh H₉ {fl = fl₈} {so = pendingˢ s q} done₉ ; (in-outer ()) ; (in-lanes ()) } ; rests = λ { (in-outer ()) ; (in-lanes ()) } })

  -- A flatMap begun allocates its pool and its outer's cut, registers its
  -- refill slot and stores it, and begins its outer under the flatMap's
  -- observer, one subscription fewer owed.
  flat-restage : ∀ {g m} (cr : Carried g m) {Δ A B op} {f : A → T.Obs Timeline Δ B} {s : T.Obs Timeline Δ A}
               → subOf (Carried.ctlAs cr) ≡ just (Δ , B , T.flatMap op f s) → Restages cr s
  flat-restage {m = m₀@(mach ⟨ H , q₀ , run _ σ K ⟩ _ _ _ _ _ _ _)} cr@record { ctlAs = subAs {s = T.flatMap {A = A} op f s} π (u , E′ , υ , e , newRef≗ refl kk) sk a } refl refl =
    _ , path
    , record { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = F.t′
             ; ctlAs = subAs F.π′ (F.code′ ex₉) (F.restack sk₉ a₉) (F.alones _)
             ; meets = trans (part-plant H₉ F.π₈ F.v refl) (trans (Grew.meets G₉) (Carried.meets cr))
             ; owned′ = owned-to (F.rf-owned refl refl slot₉ refl refl refl refl (Grew.owned G₉))
             ; kernels = F.rf-kernels refl refl slot₉ refl refl refl refl (Grew.kernels G₉)
             ; meaning = F.rf-meaning refl refl slot₉ refl refl refl refl (Grew.meaning G₉)
             ; queue = F.rf-queue refl refl slot₉ refl refl refl refl (Grew.queue G₉)
             ; books = record { fresh = F.flat-fresh (Books.fresh bk)
                              ; clocked = proj₁ (Books.clocked bk) , F.reticked sk₉ a₉ (Grew.ticked G₉)
                              ; paidUp = cong wd (cong wd (cong wd (cong wd (cong wd (cong wd (cong wd (cong wd (Books.paidUp bk))))))))
                              ; running = Books.running bk }
             ; sorted = sorted-⇝ (Carried.sorted cr) (then refl path) ; behind′ = Eaching.each-to _ _ (F.rf-behind refl refl slot₉ refl refl refl refl (Grew.behind G₉))
             ; lingers′ = Lingering.lingers-to _ (F.rf-lingers refl refl slot₉ refl refl refl refl (Grew.lingers G₉)) }
    , refl , inj₁ (inj₁ (subst (pend F.t′ <_) (Grew.pends G₉) F.less))
    where bk = Carried.books cr
          -- The kernel's allocations after its first, its registration and
          -- its store, peeled by projection: the goal mentions none of them.
          A₁ = allocates (kk new hereʳ)
          A₂ = allocates (proj₂ (proj₂ A₁) new hereʳ)
          A₃ = allocates (proj₂ (proj₂ A₂) new hereʳ)
          A₄ = allocates (proj₂ (proj₂ A₃) new hereʳ)
          A₅ = allocates (proj₂ (proj₂ A₄) new hereʳ)
          A₆ = allocates (proj₂ (proj₂ A₅) new hereʳ)
          R₇ = registers (proj₂ (proj₂ A₆) new hereʳ)
          n₇ = proj₁ R₇
          c₇ = proj₁ (proj₂ R₇)
          x₇ = proj₁ (proj₂ (proj₂ R₇))
          P₇ = proj₂ (proj₂ (proj₂ (proj₂ R₇)))
          en = proj₁ (proj₂ P₇)
          ec = proj₁ (proj₂ (proj₂ P₇))
          ex = proj₁ (proj₂ (proj₂ (proj₂ P₇)))
          W₈ = writes (proj₂ (proj₂ (proj₂ (proj₂ P₇))) new hereʳ)
          ex₉ = proj₂ (proj₂ W₈)
          e₁ = proj₁ (proj₂ A₁)
          e₂ = proj₁ (proj₂ A₂)
          e₃ = proj₁ (proj₂ A₃)
          e₄ = proj₁ (proj₂ A₄)
          e₅ = proj₁ (proj₂ A₅)
          e₆ = proj₁ (proj₂ A₆)
          e₇ = proj₁ P₇
          e₈ = proj₁ (proj₂ W₈)
          wd : ∀ {k w′} → List (Machine.Todo R w′) → List (Machine.Todo R (k ∷ w′))
          wd = mapList (wkTodo new)
          H₁ : Heapᴹ (cell (base ℕ) ∷ _)
          H₁ = extend H (lift 0)
          H₂ : Heapᴹ (cell (base Bool) ∷ _)
          H₂ = extend H₁ (lift false)
          H₃ : Heapᴹ (cell (fifo A) ∷ _)
          H₃ = extend H₂ (lift [])
          H₄ : Heapᴹ (cell (list Kit.cutTy) ∷ _)
          H₄ = extend H₃ (lift [])
          H₅ : Heapᴹ (cell (maybe (sink ⊤)) ∷ _)
          H₅ = extend H₄ (lift nothing)
          H₆ : Heapᴹ (cell (base Bool) ∷ _)
          H₆ = extend H₅ (lift true)
          H₇ : Heapᴹ (cell (maybe quiet) ∷ _)
          H₇ = extend H₆ (lift nothing)
          H₈ : Heapᴹ (slot ⊤ ∷ _)
          H₈ = extend H₇ (record { onNext = λ a → wkAct new (n₇ a) ; onComplete = wkAct new c₇ ; isClosed = wkAct new x₇ })
          H₉ = store H₈ (wkR (grow (grow (grow same⊑))) hereʳ) (lift (just hereʳ))
          G₀ : Grew H π E′ υ σ K (Mach.clock m₀) same⊑ H (Mach.bursts m₀) (Mach.timers m₀)
          G₀ = record { tree = Carried.tree cr ; path = π ; stack = sk ; alone = a ; ticked = proj₂ (Books.clocked bk)
                      ; obsR = (λ _ → wk-same _) , wk-same _ , wk-same _ ; kontR = λ τ sub → from-same (λ ζ → Here.kont (walk π top) ζ sub) τ
                      ; envR = e ; meets = refl ; owned = recode (Carried.owned cr) ; kernels = Carried.kernels cr
                      ; meaning = Carried.meaning cr ; queue = Carried.queue cr ; behind = Carried.behind cr ; lingers = Carried.lingers cr ; pends = refl
                      ; named = λ {_} {j} _ → j , refl ; distinct = λ fs → fs }
          G₈ = grew-step {k = slot ⊤} (record { onNext = λ a → wkAct new (n₇ a) ; onComplete = wkAct new c₇ ; isClosed = wkAct new x₇ })
                 (grew-step {k = cell (maybe quiet)} (lift nothing) (grew-step {k = cell (base Bool)} (lift true)
                 (grew-step {k = cell (maybe (sink ⊤))} (lift nothing) (grew-step {k = cell (list Kit.cutTy)} (lift [])
                 (grew-step {k = cell (fifo A)} (lift []) (grew-step {k = cell (base Bool)} (lift false) (grew-step {k = cell (base ℕ)} (lift 0) G₀)))))))
          G₉ = grew-store (wkR (grow (grow (grow same⊑))) hereʳ) (just hereʳ) (λ _ ()) G₈
          module F = Flatted G₉
          sk₉ = Grew.stack G₉
          a₉ = Grew.alone G₉
          slot₉ : CbRel (look H₉ hereʳ) F.kcb
          slot₉ = (λ a → ≗-trans (wk-same _) (wk≗ new (en a))) , ≗-trans (wk-same _) (wk≗ new ec) , ≗-trans (wk-same _) (wk≗ new ex)
          M₁ : Act (cell (base ℕ) ∷ _) ⊤ → Mach
          M₁ x = record m₀ { conf = ⟨ H₁ , q₀ , run x (σ ⨾ new) K ⟩ ; timers = mapList (wkTimer new) (Mach.timers m₀)
                           ; bursts = mapList (mapMaybe (wkPlaying new)) (Mach.bursts m₀) ; todo = wd (Mach.todo m₀) }
          M₂ : Act (cell (base Bool) ∷ _) ⊤ → Mach
          M₂ x = record m₀ { conf = ⟨ H₂ , q₀ , run x ((σ ⨾ new) ⨾ new) K ⟩ ; timers = mapList (wkTimer new) (Mach.timers (M₁ skipᴬ))
                           ; bursts = mapList (mapMaybe (wkPlaying new)) (Mach.bursts (M₁ skipᴬ)) ; todo = wd (Mach.todo (M₁ skipᴬ)) }
          M₃ : Act (cell (fifo A) ∷ _) ⊤ → Mach
          M₃ x = record m₀ { conf = ⟨ H₃ , q₀ , run x (((σ ⨾ new) ⨾ new) ⨾ new) K ⟩ ; timers = mapList (wkTimer new) (Mach.timers (M₂ skipᴬ))
                           ; bursts = mapList (mapMaybe (wkPlaying new)) (Mach.bursts (M₂ skipᴬ)) ; todo = wd (Mach.todo (M₂ skipᴬ)) }
          M₄ : Act (cell (list Kit.cutTy) ∷ _) ⊤ → Mach
          M₄ x = record m₀ { conf = ⟨ H₄ , q₀ , run x ((((σ ⨾ new) ⨾ new) ⨾ new) ⨾ new) K ⟩ ; timers = mapList (wkTimer new) (Mach.timers (M₃ skipᴬ))
                           ; bursts = mapList (mapMaybe (wkPlaying new)) (Mach.bursts (M₃ skipᴬ)) ; todo = wd (Mach.todo (M₃ skipᴬ)) }
          M₅ : Act (cell (maybe (sink ⊤)) ∷ _) ⊤ → Mach
          M₅ x = record m₀ { conf = ⟨ H₅ , q₀ , run x (((((σ ⨾ new) ⨾ new) ⨾ new) ⨾ new) ⨾ new) K ⟩ ; timers = mapList (wkTimer new) (Mach.timers (M₄ skipᴬ))
                           ; bursts = mapList (mapMaybe (wkPlaying new)) (Mach.bursts (M₄ skipᴬ)) ; todo = wd (Mach.todo (M₄ skipᴬ)) }
          M₆ : Act (cell (base Bool) ∷ _) ⊤ → Mach
          M₆ x = record m₀ { conf = ⟨ H₆ , q₀ , run x ((((((σ ⨾ new) ⨾ new) ⨾ new) ⨾ new) ⨾ new) ⨾ new) K ⟩ ; timers = mapList (wkTimer new) (Mach.timers (M₅ skipᴬ))
                           ; bursts = mapList (mapMaybe (wkPlaying new)) (Mach.bursts (M₅ skipᴬ)) ; todo = wd (Mach.todo (M₅ skipᴬ)) }
          M₇ : Act (cell (maybe quiet) ∷ _) ⊤ → Mach
          M₇ x = record m₀ { conf = ⟨ H₇ , q₀ , run x (((((((σ ⨾ new) ⨾ new) ⨾ new) ⨾ new) ⨾ new) ⨾ new) ⨾ new) K ⟩ ; timers = mapList (wkTimer new) (Mach.timers (M₆ skipᴬ))
                           ; bursts = mapList (mapMaybe (wkPlaying new)) (Mach.bursts (M₆ skipᴬ)) ; todo = wd (Mach.todo (M₆ skipᴬ)) }
          M₈ : Act (slot ⊤ ∷ _) ⊤ → Mach
          M₈ x = record m₀ { conf = ⟨ H₈ , q₀ , run x ((((((((σ ⨾ new) ⨾ new) ⨾ new) ⨾ new) ⨾ new) ⨾ new) ⨾ new) ⨾ new) K ⟩ ; timers = mapList (wkTimer new) (Mach.timers (M₇ skipᴬ))
                           ; bursts = mapList (mapMaybe (wkPlaying new)) (Mach.bursts (M₇ skipᴬ)) ; todo = wd (Mach.todo (M₇ skipᴬ)) }
          path = then (cong (λ x → step (M₁ x)) e₁) (then (cong (λ x → step (M₂ x)) e₂) (then (cong (λ x → step (M₃ x)) e₃) (then (cong (λ x → step (M₄ x)) e₄) (then (cong (λ x → step (M₅ x)) e₅) (then (cong (λ x → step (M₆ x)) e₆) (then (cong (λ x → step (M₇ x)) e₇) (then (cong (λ x → step (M₈ x)) e₈) now)))))))
