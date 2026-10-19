{-# OPTIONS --guardedness #-}

-- A CONNECT RESTAGED in the world grown by its subject and cuts.
module adequacy.Connected where

open import Data.List using (List; []; _∷_; _++_; [_]; length) renaming (map to mapᴸ)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (tabulate to tabulateᴬ; lookup to lookupᴬ; map to all-map)
open import Data.List.Relation.Unary.Any using () renaming (here to hereᴬ; there to thereᴬ)
open import Data.List.Relation.Unary.Any.Properties using () renaming (++⁻ to any-++⁻; ++⁺ˡ to any-++⁺ˡ; ++⁺ʳ to any-++⁺ʳ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁻ to all-++⁻; ++⁺ to all-++⁺)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_) renaming (map to pairs-map)
open import Data.List.Relation.Unary.Linked using (Linked; []; _∷_)
open import Data.List.Relation.Unary.AllPairs.Properties using () renaming (map⁺ to pairs-map⁺; ++⁺ to pairs-++⁺)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_; ↭-sym; ↭-trans; ↭-reflexive) renaming (refl to ↭-refl′; prep to ↭-prep′; swap to ↭-swap′; trans to ↭-trans′)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (All-resp-↭; shifts) renaming (++⁺ˡ to ↭-++⁺ˡ; ++⁺ʳ to ↭-++⁺ʳ)
open import Data.List.Properties using (map-++; ++-assoc) renaming (++-identityʳ to ++-idʳ)
open import Data.Maybe using (Maybe; just; nothing; is-just) renaming (map to mapMaybe)
open import Data.Nat using (ℕ; _<_; z≤n)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Sum using (inj₁)
open import Data.Unit using (⊤)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤₁; tt to tt₁)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Relation.Nullary using (¬_)
open import Level using (lift)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import denotation.MonotonicList.Events using (Timeline; Frame; From; Pos; ix; last; tick; at; _<ᵖ_; <ᵖ-below) renaming (done to doneᶠᵐ; quiet to quietᶠᵐ)
open import denotation.MonotonicList.Events using () renaming (sub to subᴾ)
import Tree as T
import denotation.Unfold as U
open import operation.Machine using (module Machine)
open import operation.PureObservable using (Out; Pureᴾ)
open import operation.AbstractObservable using (module Heap; module Run) renaming (module Machine to Shared)
open import adequacy.Strong using (module Strongly)
open import adequacy.Strong.Against using (module StrongAgainst)
open import adequacy.Strong.Held using (module StrongHeld)
open import adequacy.Moves using (module Moving)
open import adequacy.Ghost using (module Ghosting)
open import adequacy.Ghost.Paths using (module GhostingPaths)
open import adequacy.Unsub using (module Unsubbing)
open import adequacy.Grow using (module Growing)
open import adequacy.Seq using (module Sequencing)
open import operation.AbstractObservable using (base; maybe; quiet; joins)
open import operation.PureObservable using (module Pure)
open import adequacy.Fork using (module Forking)
open import adequacy.Kept using (module Keeping)
open import adequacy.Moved using (module Planting)
open import adequacy.Restages using (module Staging)
open import adequacy.Weaken using (module Weakening)
open import adequacy.Weaken.Heaps using (module WeakeningHeaps)
open import adequacy.Every.Gating using (module EverywhereGated)
open import adequacy.Names using (module Naming)
open import adequacy.Alike using (module Aliking)
open import adequacy.Taken using (module Taking)
open import adequacy.Replant using (module Replanting)
open import adequacy.Torn using (module Tearing)
open import adequacy.Local using (module Locality)
open import adequacy.Shift using (module Shifting)
open import Data.Empty using (⊥)

module Connecting (R : Set) where
  open Machine R using (Mach; mach; step; Playing; wkPlaying; wkTodo)
  open Unsubbing R using (now; then; ≗-trans; bind≗; wk-same; wkEnv-same; from-same)
  open Growing R using (wkTree; wkPath)
  open Sequencing R using (from-⨾; seq-done; wk∋-wk)
  open Pure R using (Timer; wkTimer; mapList)
  open Shared Timeline (Out R) using (Heapᴹ; ⟨_,_,_⟩; Stack; run; Val; extend; store)
  open Heap using (World; _⊑_; _⨾_; _∋_; there; new; grow; wk∋; cell) renaming (here to hereʳ; same to same⊑)
  open Run (Pureᴾ R) using (Act; done; under; _>>ᴬ_; compile; Env; wkEnv; wkAct; module Kit; Ref; wkR; Observer; Kont; wkObs; wkKont; Subject; Subscription; wkSubn)
  open Run.Kit (Pureᴾ R) using (skipᴬ)
  open Strongly R using (Sub; pendingˢ; connectˢ; idle; bodyK; srcK; Path; here; in-source; in-body; _⊕_; Here; walk; top; srcC; _≗_; module At; Name; PathLanes; this-lane; next-lane; in-map; in-scan; in-take; in-outer; in-lanes; in-defer; subjects; laneSubjects; Lane; lane; names; Phase; ≗-refl; newRef≗; unsubscribing; under≗; readRef≗; module Canon) renaming (⟦_⟧ to ⟦_⟧ᶜ)
  open StrongAgainst R using (Leaving; Books; Job; Owned; Kernels; Meaning; Queue; Each; Lingers; union-pinned; under-moved; bursts-pinned; rest-pinned; owned-to) renaming (at⟦_⟧ to at⟦_⟧ᶜ)
  open StrongHeld R using (Carried; Heads; DoneBy; module Eaching; module Lingering)
  open StrongAgainst.Against R using (StackAs; CtlAs; subAs; backAs; stackJobs; SrcOf; src-of; Ticked)
  open Moving R using (planted; pend; part-plant; holds-owed; fed-plant; plant; plantᴸ; Splice; spliced-l; spliced-r; pendings-plant; joiners-plant)
  open EverywhereGated.Settling R using (settled-plant)
  open EverywhereGated.Gating R using (gated-plant; gated-alike)
  open Ghosting R using (sorted-⇝)
  open GhostingPaths R using (walk-⊕)
  open Forking R using (pend-less; subOf; walk-planted)
  open Keeping R using (lingers-plant; flags-plant)
  open Planting R using (module Moved)
  open Staging R using (Restages; not-src; wrap-body)
  open Weakening R using (module Grown; pend-grow)
  open WeakeningHeaps R using (module GrownHeaps)
  open EverywhereGated R using (module Growths)
  open Naming R using (fresh-new; fresh-plant; grows-extend; names-wk; pending-↭; wk-pairs)
  open Aliking R using (KontRel; ObsRel; compile-cong; compile-env; obs-trans; obs-wk; obs-⨾; walk-grow; ≗-sym)
  open Taking R using (allocates; recode; tick-ix0; unders; ⊑≗)
  open Replanting R using (ahead-under)
  open Tearing R using (Alike; part-alike; look-store)
  open Locality R using (module Heaps)
  open EverywhereGated.Holding R using (holds-alike)
  open Shifting R using (each-alike; lingers-alike; leaving-alike; flags-alike)

  -- A RUN AT A PENDING NODE, THE WORLD GROWN: what the relation reads of
  -- the run at its subscription, along the weakened tree and against the
  -- grown heap, the walk to it handing what it handed, weakened.
  record Grew {h₀} (H₀ : Heapᴹ h₀) {T₀ : Sub h₀ [] R} {Δ A} {s : T.Obs Timeline Δ A} {q} (π₀ : Path T₀ (pendingˢ s q))
              {u} (E′ : Env Δ u) (υ : u ⊑ h₀) {w} (σ : w ⊑ h₀) (K : Stack w ⊤) (clk : ℕ)
              {h} (ν : h₀ ⊑ h) (H : Heapᴹ h) (bs : List (Maybe (Playing h))) (ts : List (Timer h)) : Set₁ where
    field
      tree    : Sub h [] R
      path    : Path tree (pendingˢ s q)
      stack   : StackAs tree q (σ ⨾ ν) K bs
      alone   : All (λ j → ¬ SrcOf tree path (proj₂ j)) (stackJobs tree stack)
      ticked  : Ticked tree clk stack
      obsR    : ObsRel (wkObs ν (Here.obs (walk π₀ top))) (Here.obs (walk path top))
      kontR   : KontRel (wkKont ν (Here.kont (walk π₀ top))) (Here.kont (walk path top))
      envR    : wkEnv (υ ⨾ ν) E′ ≡ Here.env (walk path top)
      meets   : At.part H tree ≡ At.part H₀ T₀
      owned   : Owned H tree (subAs path (_ , E′ , υ ⨾ ν , envR , ≗-refl _) stack alone)
      kernels : Kernels H tree
      meaning : Meaning H tree
      queue   : Queue H q clk ts tree
      behind  : Each H (Heads q) tree
      lingers : Lingers H tree
      leaving : Leaving H tree
      flags   : DoneBy H tree []
      pends   : pend tree ≡ pend T₀
      named   : ∀ {k} {j : h ∋ k} → (k , j) ∈ names tree → Σ (h₀ ∋ k) λ i → wk∋ ν i ≡ j
      distinct : AllPairs _≢_ (names T₀) → AllPairs _≢_ (names tree)

  -- One cell more.
  grew-step : ∀ {h₀} {H₀ : Heapᴹ h₀} {T₀ : Sub h₀ [] R} {Δ A} {s : T.Obs Timeline Δ A} {q} {π₀ : Path T₀ (pendingˢ s q)}
                {u} {E′ : Env Δ u} {υ : u ⊑ h₀} {w} {σ : w ⊑ h₀} {K : Stack w ⊤} {clk}
                {h} {ν : h₀ ⊑ h} {H : Heapᴹ h} {bs ts} {k} (x : Val (k ∷ h) k)
            → Grew H₀ π₀ E′ υ σ K clk ν H bs ts
            → Grew H₀ π₀ E′ υ σ K clk (ν ⨾ new) (extend H x) (mapList (mapMaybe (wkPlaying new)) bs) (mapList (wkTimer new) ts)
  grew-step {π₀ = π₀} {E′ = E′} {υ = υ} {h = h} {ν = ν} {H = H} {k = k} x G = record
    { tree = wkTree new (tree G) ; path = wkPath new (path G) ; stack = Gw.grow-stack (stack G)
    ; alone = Gw.grow-alone (path G) (stack G) (alone G) ; ticked = Gw.grow-ticked (stack G) (ticked G)
    ; obsR = obs-trans (obs-trans (obs-⨾ ν new _) (obs-wk new (obsR G))) (proj₁ wg)
    ; kontR = λ τ sub → ≗-trans (≗-sym (from-⨾ (λ ζ → Here.kont (walk π₀ top) ζ sub) ν new τ)) (≗-trans (kontR G (new ⨾ τ) sub) (proj₁ (proj₂ wg) τ sub))
    ; envR = Gw.env-grow (path G) E′ (υ ⨾ ν) (envR G)
    ; meets = trans (Gw′.grow-part gr (tree G)) (meets G)
    ; owned = Gw′.grow-owned gr (stack G) (owned G)
    ; kernels = Growths.kernels-grow (new {k} {h}) gr (kernels G) ; meaning = Gw′.grow-meaning gr (meaning G) ; queue = Gw′.grow-queue gr (queue G)
    ; behind = Gw′.grow-each gr (behind G) ; lingers = Gw′.grow-lingers gr (lingers G) ; leaving = Gw′.grow-leaving gr (leaving G) ; flags = Gw′.grow-flags gr (flags G) ; pends = trans (pend-grow new (tree G)) (pends G)
    ; named = λ {_} {j} m → let (i′ , e′ , m′) = names-wk new (tree G) j m ; (i , e) = named G m′
                            in i , trans (sym (wk∋-wk ν new i)) (trans (cong (wk∋ new) e) e′)
    ; distinct = λ fs → wk-pairs new (tree G) (distinct G fs) }
    where open Grew
          module Gw = Grown (new {k} {h})
          module Gw′ = GrownHeaps (new {k} {h})
          gr = grows-extend H x
          wg = walk-grow new (path G)

  -- The subjects, the node's own replaced in place.
  mutual
    subjects-splice : ∀ {h Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (v : Sub h Δ′ A′)
                    → Splice (subjects t) (subjects u) (subjects (plant π v)) (subjects v)
    subjects-splice {u = u} here v                     = [] , [] , sym (++-idʳ (subjects u)) , sym (++-idʳ (subjects v))
    subjects-splice (in-map π) v                       = subjects-splice π v
    subjects-splice (in-scan π) v                      = subjects-splice π v
    subjects-splice (in-take π) v                      = subjects-splice π v
    subjects-splice (in-outer {ls = ls} π) v           = spliced-r (laneSubjects ls) (subjects-splice π v)
    subjects-splice (in-lanes {t = so} π) v            = spliced-l (subjects so) (subjects-spliceᴸ π v)
    subjects-splice (in-source {S = S} {bd = bd} π) v  = spliced-l ((_ , S) ∷ []) (spliced-r (subjects bd) (subjects-splice π v))
    subjects-splice (in-body {S = S} {t = src} π) v    = spliced-l ((_ , S) ∷ subjects src) (subjects-splice π v)
    subjects-splice (in-defer π) v                     = subjects-splice π v

    subjects-spliceᴸ : ∀ {h Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (π : PathLanes ls u) (v : Sub h Δ′ A′)
                     → Splice (laneSubjects ls) (subjects u) (laneSubjects (plantᴸ π v)) (subjects v)
    subjects-spliceᴸ (this-lane {ls = ls} π) v        = spliced-r (laneSubjects ls) (subjects-splice π v)
    subjects-spliceᴸ (next-lane {l = lane c k s} π) v = spliced-l (subjects s) (subjects-spliceᴸ π v)

  -- The world a connect's kernel allocates: its subject's joiners and
  -- closed flag, its cut's flag and stash, the stash of its body's
  -- subscription.
  connectWorld : World → Set → World
  connectWorld h A = cell (maybe quiet) ∷ cell (maybe quiet) ∷ cell (base Bool) ∷ cell (base Bool) ∷ cell (joins A) ∷ h

  connectGrown : ∀ {h A} → h ⊑ connectWorld h A
  connectGrown = grow (grow (grow (grow (grow same⊑))))

  -- A CONNECT RESTAGED IN THE WORLD ITS KERNEL GREW: its subject, flag,
  -- cut and stash the newest cells, its body pending under `ix 0`, its
  -- source pending under `ix 1` and owed back where the connect began.
  module Connected {h₀} {H₀ : Heapᴹ h₀} {T₀ : Sub h₀ [] R} {Δ A B} {s : T.Obs Timeline Δ A} {b : T.Obs Timeline (A ∷ Δ) B} {q}
                   {π₀ : Path T₀ (pendingˢ (T.connect s b) q)} {u} {E′ : Env Δ u} {υ : u ⊑ h₀} {w} {σ : w ⊑ h₀} {K : Stack w ⊤} {clk}
                   {H₅ : Heapᴹ (connectWorld h₀ A)} {bs ts}
                   (G₅ : Grew H₀ π₀ E′ υ σ K clk connectGrown H₅ bs ts)
                   (held₅ : At.val H₅ (Kit.held (Kit.wkCut new (wkR new hereʳ , hereʳ))) ≡ nothing) (body₅ : At.val H₅ hereʳ ≡ nothing)
                   (joins₅ : At.val H₅ (wkR (grow (grow (grow (grow same⊑)))) hereʳ) ≡ []) where
    h₅ : World
    h₅ = connectWorld h₀ A

    ν₅ : h₀ ⊑ h₅
    ν₅ = connectGrown

    T₅ : Sub h₅ [] R
    T₅ = Grew.tree G₅

    π₅ : Path T₅ (pendingˢ (T.connect s b) q)
    π₅ = Grew.path G₅

    O : Observer B h₀
    O = Here.obs (walk π₀ top)

    Kt : Kont h₀
    Kt = Here.kont (walk π₀ top)

    S₅ : Subject A h₅
    S₅ = record { subscribers = wkR (grow (grow (grow (grow same⊑)))) hereʳ ; closed = wkR (grow (grow (grow same⊑))) hereʳ }

    c₅ : Kit.Cut h₅
    c₅ = Kit.wkCut new (wkR new hereʳ , hereʳ)

    v : Sub h₅ Δ B
    v = connectˢ S₅ c₅ hereʳ nothing nothing idle (q ++ [ ix 1 ]) nothing (U.subscribe s (q ++ [ ix 1 ])) (pendingˢ s (q ++ [ ix 1 ])) (pendingˢ b (q ++ [ ix 0 ]))

    open Moved π₅ v using (t′; restack; Alone; reticked) public

    ρc : Path t′ v
    ρc = planted π₅ v

    ιb : Path v (pendingˢ b (q ++ [ ix 0 ]))
    ιb = in-body here

    ιs : Path v (pendingˢ s (q ++ [ ix 1 ]))
    ιs = in-source here

    π′ : Path t′ (pendingˢ b (q ++ [ ix 0 ]))
    π′ = ρc ⊕ ιb

    W₅ : Here h₅ Δ B
    W₅ = walk π₅ top

    walkB : walk π′ top ≡ walk ιb W₅
    walkB = trans (walk-⊕ ρc ιb top) (cong (walk ιb) (walk-planted π₅ v top))

    walkS : walk (ρc ⊕ ιs) top ≡ walk ιs W₅
    walkS = trans (walk-⊕ ρc ιs top) (cong (walk ιs) (walk-planted π₅ v top))

    consE : Subject A h₅ → Env Δ h₅ → Env (A ∷ Δ) h₅
    consE = _∷_

    -- The body compiles as the kernel began it, under the body's observer
    -- over the grown walk.
    body-code : ∀ {x} → x ≗ compile b (consE S₅ (wkEnv (υ ⨾ ν₅) E′)) same⊑ (Canon.bodyO c₅ (wkObs ν₅ O)) (bodyK hereʳ)
              → Σ World λ u′ → Σ (Env (A ∷ Δ) u′) λ E″ → Σ (u′ ⊑ h₅) λ υ′ → wkEnv υ′ E″ ≡ Here.env (walk π′ top)
                  × x ≗ compile b E″ υ′ (Here.obs (walk π′ top)) (Here.kont (walk π′ top))
    body-code {x} c = _ , consE S₅ (wkEnv (υ ⨾ ν₅) E′) , same⊑
      , subst (λ W → wkEnv same⊑ (consE S₅ (wkEnv (υ ⨾ ν₅) E′)) ≡ Here.env W) (sym walkB) (trans (wkEnv-same _) (cong (consE S₅) (Grew.envR G₅)))
      , subst (λ W → x ≗ compile b (consE S₅ (wkEnv (υ ⨾ ν₅) E′)) same⊑ (Here.obs W) (Here.kont W)) (sym walkB)
          (≗-trans c (compile-cong b _ same⊑ (proj₁ oR , bind≗ (proj₁ (proj₂ oR)) (λ _ → ≗-refl _) , proj₂ (proj₂ oR)) (λ _ _ → ≗-refl _)))
      where oR = Grew.obsR G₅

    -- What the run owes the source, at a walk handing it.
    owedSrc : Here h₅ Δ A → Act h₅ ⊤
    owedSrc W = under (ix 1) (compile s (Here.env W) same⊑ (Here.obs W) (Here.kont W)) skipᴬ

    -- The source compiles as the kernel left it owed, under the subject's
    -- feeder and the source's continuation over the grown walk.
    src-owed : (N : ∀ {v} → h₅ ⊑ v → h₀ ⊑ v) → ∀ {y}
             → y ≗ under (ix 1) (compile s E′ (υ ⨾ ν₅) (Canon.feeder S₅) (srcK c₅ hereʳ (λ ζ → Kt (N ζ)))) skipᴬ
             → wkAct same⊑ y ≗ ⟦ srcC ρc ∷ [] ⟧ᶜ
    src-owed N {y} c =
      ≗-trans (wk-same y) (≗-trans c (≗-trans
        (subst (λ E → under (ix 1) (compile s E′ (υ ⨾ ν₅) (Canon.feeder S₅) (srcK c₅ hereʳ (λ ζ → Kt (N ζ)))) skipᴬ
                    ≗ under (ix 1) (compile s E same⊑ (Canon.feeder S₅) (srcK c₅ hereʳ (Here.kont W₅))) skipᴬ)
               (Grew.envR G₅)
               (under≗ (≗-trans (compile-env s E′ (υ ⨾ ν₅) same⊑) (compile-cong s _ same⊑ fR kR)) (≗-refl skipᴬ)))
        (subst (λ W → owedSrc (walk ιs W₅) ≗ (owedSrc W >>ᴬ skipᴬ)) (sym walkS) (seq-done (owedSrc (walk ιs W₅))))))
      where
        fR : ObsRel (Canon.feeder S₅) (Canon.feeder S₅)
        fR = (λ _ → ≗-refl _) , ≗-refl _ , ≗-refl _

        kr : ∀ {v} (ζ : h₅ ⊑ v) sub → Kt (N ζ) sub ≗ Here.kont W₅ ζ sub
        kr ζ sub = ≗-trans (⊑≗ (λ z → Kt z sub) (N ζ) (ν₅ ⨾ ζ)) (Grew.kontR G₅ ζ sub)

        kR : KontRel (srcK c₅ hereʳ (λ ζ → Kt (N ζ))) (srcK c₅ hereʳ (Here.kont W₅))
        kR ψ sub = bind≗ (≗-refl (Kit.attach (Kit.wkCut ψ c₅) sub)) λ _ → readRef≗ refl λ ψ′ mb → kr (ψ ⨾ ψ′) (unsubscribing (Subscription.unsubscribe (wkSubn ψ′ sub) >>ᴬ Kit.unsubscribeVia mb))

    alone : ∀ {k} → ¬ SrcOf t′ π′ k
    alone (src-of ρ e) = not-src wrap-body ρc ρ e

    alones : ∀ (js : List (Job t′)) → All (λ j → ¬ SrcOf t′ π′ (proj₂ j)) js
    alones _ = tabulateᴬ (λ _ → alone)

    less : pend t′ < pend T₅
    less = pend-less π₅ v ≤-refl

    -- A connect over its pending source and body registers nothing, is
    -- owed nothing and holds nothing a feed is owed.
    rc-kernels : Kernels H₅ T₅ → Kernels H₅ t′
    rc-kernels kn = record { holds = holds-owed H₅ π₅ v tt (Here.kont top) (λ _ → lift held₅ , body₅ , lift tt , lift tt , lift tt) (Kernels.settled kn) (Kernels.holds kn)
                           ; gated = gated-plant H₅ π₅ v (λ _ → (λ _ → lift tt) , lift tt , lift tt) (λ _ → lift tt , lift tt) (Kernels.gated kn)
                           ; settled = settled-plant H₅ π₅ v (λ _ → tt) (λ _ → tt , tt , tt , tt) (Kernels.settled kn) }

    rc-meaning : Meaning H₅ T₅ → Meaning H₅ t′
    rc-meaning mn = record { fed = fed-plant H₅ π₅ v (λ _ _ → lift tt , lift tt) _ (Meaning.fed mn) }

    -- The subject's, flag's, cut's and stash's cells are names the tree
    -- did not hold.
    connect-fresh : AllPairs _≢_ (names T₀) → AllPairs _≢_ (names t′)
    connect-fresh fs = fresh-plant π₅ v (pending-↭ v) (((λ ()) ∷ (λ ()) ∷ (λ ()) ∷ (λ ()) ∷ []) ∷ ((λ ()) ∷ (λ ()) ∷ (λ ()) ∷ []) ∷ ((λ ()) ∷ (λ ()) ∷ []) ∷ ((λ ()) ∷ []) ∷ ([]) ∷ []) (Grew.distinct G₅ fs)
      (fresh-new ν₅ (λ { {_ , _} m∈ → Grew.named G₅ m∈ }) ((λ { {_ , _} (_ , refl) () }) ∷ (λ { {_ , _} (_ , refl) () }) ∷ (λ { {_ , _} (_ , refl) () }) ∷ (λ { {_ , _} (_ , refl) () }) ∷ (λ { {_ , _} (_ , refl) () }) ∷ []))

    postulate
      -- Owed across the restage: each node beside the connect or above it
      -- owed as it was, the body the subscription the run begins, the
      -- source the call owed back where the connect began.
      connect-owned  : ∀ {w′ bs′ act act′} {σ′ : w′ ⊑ h₅} {K′} {cd cd′} {m : Act h₅ ⊤} (sk : StackAs T₅ q σ′ K′ bs′) (a : Alone sk) {a′}
                       (e : wkAct same⊑ m ≗ ⟦ srcC ρc ∷ [] ⟧ᶜ)
                     → Owned H₅ T₅ (subAs {act = act} π₅ cd sk a)
                     → Owned H₅ t′ (subAs {act = act′} π′ cd′ (backAs q {ρ = σ′} {σ = same⊑} (srcC ρc ∷ []) (<ᵖ-below q []) e (restack sk a)) a′)
      -- Every head no earlier than the run one level down.
      connect-behind : Each H₅ (Heads q) T₅ → Each H₅ (Heads (q ++ [ ix 0 ])) t′

    -- The queue, the run one level down, a new subject joined by none.
    connect-queue : Queue H₅ q clk ts T₅ → Queue H₅ (q ++ [ ix 0 ]) clk ts t′
    connect-queue qu = record
      { timed   = subst (At.Timed H₅ ts) (sym pnd) (Queue.timed qu)
      ; joined  = subst (λ ss → At.Joined H₅ ss (Strongly.joiners R t′ [])) (sym (proj₂ (proj₂ (proj₂ sj))))
                    (all-++⁺ (proj₁ al) (nil joins₅ ∷ proj₂ al) , proj₂ jd)
      ; ordered = Queue.ordered qu ; ahead = ahead-under q 0 (λ _ → z≤n) (Queue.ahead qu) }
      where
        pnd : Strongly.pendings R t′ ≡ Strongly.pendings R T₅
        pnd with pendings-plant π₅ v
        ... | _ , _ , e , e′ = trans e′ (sym e)
        sj = subjects-splice π₅ v
        jd = subst (At.Joined H₅ (subjects T₅)) (sym (joiners-plant π₅ v (λ _ → refl) [])) (Queue.joined qu)
        al = all-++⁻ (proj₁ sj) (subst (All _) (proj₁ (proj₂ (proj₂ sj))) (proj₁ jd))
        nil : ∀ {X : Set} {Q : X → Set₁} {L : X → X → Set} {xs : List X} → xs ≡ [] → All Q xs × Linked L xs
        nil refl = [] , []

    -- A connect pending its source runs what it was pending to, its
    -- source not yet ended.
    connect-lingers : Lingers H₅ T₅ → Lingers H₅ t′
    connect-lingers = lingers-plant H₅ π₅ v refl
      (union-pinned (bursts-pinned (q ++ [ ix 1 ]) (U.subscribe s (q ++ [ ix 1 ])) (U.step (U.subscribe s (q ++ [ ix 1 ]))))
                    (under-moved (U.live (U.subscribe s (q ++ [ ix 1 ]))) (U.live (U.subscribe s (q ++ [ ix 1 ]))) (rest-pinned (U.subscribe b (q ++ [ ix 0 ])))))
      (record { pools = λ { (in-source ()) ; (in-body ()) } ; rests = λ { here _ _ _ () ; (in-source ()) ; (in-body ()) } })

    postulate
      connect-leaving : Leaving H₅ T₅ → Leaving H₅ t′

    connect-flags : DoneBy H₅ T₅ [] → DoneBy H₅ t′ []
    connect-flags = flags-plant H₅ π₅ v refl (λ { (in-source ()) ; (in-body ()) })

  -- A connect begun allocates its subject, flag, cut and stash, begins
  -- its body under `ix 0` and owes its source back where it began, one
  -- subscription fewer owed.
  connect-restage : ∀ {g m} (cr : Carried g m) {Δ A B} {s : T.Obs Timeline Δ A} {b : T.Obs Timeline (A ∷ Δ) B}
                  → subOf (Carried.ctlAs cr) ≡ just (Δ , B , T.connect s b) → Restages cr b
  connect-restage {m = m₀@(mach ⟨ H , q₀ , run _ σ K ⟩ _ _ _ _ _ _ _)} cr@record { ctlAs = subAs {s = T.connect {A = A} s b} π (u , E′ , υ , e , newRef≗ refl kk) sk a } refl refl
    with allocates (kk new hereʳ)
  ... | k₁ , e₁ , kk₁ with allocates (kk₁ new hereʳ)
  ... | k₂ , e₂ , kk₂ with allocates (kk₂ new hereʳ)
  ... | k₃ , e₃ , kk₃ with allocates (kk₃ new hereʳ)
  ... | k₄ , e₄ , kk₄ with unders (kk₄ new hereʳ)
  ... | x′ , y′ , e₅ , ex , ey =
    _ , path
    , record { sane = Carried.sane cr ; placed = Carried.placed cr ; deep = Carried.deep cr ; tree = C.t′
             ; ctlAs = subAs C.π′ (C.body-code ex) (backAs q₀ (srcC C.ρc ∷ []) (<ᵖ-below q₀ []) eY (C.restack sk₅ a₅)) (C.alones _)
             ; meets = trans (part-plant H₅ C.π₅ C.v refl) (trans (Grew.meets G₅) (Carried.meets cr))
             ; owned′ = owned-to (C.connect-owned sk₅ a₅ eY (Grew.owned G₅))
             ; kernels = C.rc-kernels (Grew.kernels G₅) ; meaning = C.rc-meaning (Grew.meaning G₅) ; queue = C.connect-queue (Grew.queue G₅)
             ; books = record { fresh = C.connect-fresh (Books.fresh bk)
                              ; clocked = trans ck (sym (tick-ix0 q₀)) , ck , C.reticked sk₅ a₅ (Grew.ticked G₅)
                              ; paidUp = cong wd (cong wd (cong wd (cong wd (cong wd (Books.paidUp bk))))) ; running = Books.running bk }
             ; sorted = sorted-⇝ (Carried.sorted cr) (then refl path) ; behind′ = Eaching.each-to _ _ (C.connect-behind (Grew.behind G₅)) ; lingers′ = Lingering.lingers-to _ (C.connect-lingers (Grew.lingers G₅)) ; leaving = C.connect-leaving (Grew.leaving G₅)
             ; flags = C.connect-flags (Grew.flags G₅) }
    , refl , inj₁ (inj₁ (subst (pend C.t′ <_) (Grew.pends G₅) C.less))
    where bk = Carried.books cr
          ck = proj₁ (Books.clocked bk)
          wd : ∀ {k w′} → List (Machine.Todo R w′) → List (Machine.Todo R (k ∷ w′))
          wd = mapList (wkTodo new)
          H₁ : Heapᴹ (cell (joins A) ∷ _)
          H₁ = extend H (lift [])
          H₂ : Heapᴹ (cell (base Bool) ∷ _)
          H₂ = extend H₁ (lift false)
          H₃ : Heapᴹ (cell (base Bool) ∷ _)
          H₃ = extend H₂ (lift true)
          H₄ : Heapᴹ (cell (maybe quiet) ∷ _)
          H₄ = extend H₃ (lift nothing)
          H₅ : Heapᴹ (cell (maybe quiet) ∷ _)
          H₅ = extend H₄ (lift nothing)
          G₀ : Grew H π E′ υ σ K (Mach.clock m₀) same⊑ H (Mach.bursts m₀) (Mach.timers m₀)
          G₀ = record { tree = Carried.tree cr ; path = π ; stack = sk ; alone = a ; ticked = proj₂ (Books.clocked bk)
                      ; obsR = (λ _ → wk-same _) , wk-same _ , wk-same _ ; kontR = λ τ sub → from-same (λ ζ → Here.kont (walk π top) ζ sub) τ
                      ; envR = e ; meets = refl ; owned = recode (Carried.owned cr) ; kernels = Carried.kernels cr
                      ; meaning = Carried.meaning cr ; queue = Carried.queue cr ; behind = Carried.behind cr ; lingers = Carried.lingers cr ; leaving = Carried.leaving cr ; flags = Carried.flags cr ; pends = refl
                      ; named = λ {_} {j} _ → j , refl ; distinct = λ fs → fs }
          G₅ = grew-step {k = cell (maybe quiet)} (lift nothing) (grew-step {k = cell (maybe quiet)} (lift nothing)
                 (grew-step {k = cell (base Bool)} (lift true) (grew-step {k = cell (base Bool)} (lift false) (grew-step {k = cell (joins A)} (lift []) G₀))))
          module C = Connected G₅ refl refl refl
          sk₅ = Grew.stack G₅
          a₅ = Grew.alone G₅
          eY = C.src-owed (λ ζ → new ⨾ (new ⨾ ((new ⨾ new) ⨾ (new ⨾ ζ)))) ey
          M₁ : Act (cell (joins A) ∷ _) ⊤ → Mach
          M₁ x = record m₀ { conf = ⟨ H₁ , q₀ , run x (σ ⨾ new) K ⟩ ; timers = mapList (wkTimer new) (Mach.timers m₀)
                           ; bursts = mapList (mapMaybe (wkPlaying new)) (Mach.bursts m₀) ; todo = wd (Mach.todo m₀) }
          M₂ : Act (cell (base Bool) ∷ _) ⊤ → Mach
          M₂ x = record m₀ { conf = ⟨ H₂ , q₀ , run x ((σ ⨾ new) ⨾ new) K ⟩ ; timers = mapList (wkTimer new) (Mach.timers (M₁ skipᴬ))
                           ; bursts = mapList (mapMaybe (wkPlaying new)) (Mach.bursts (M₁ skipᴬ)) ; todo = wd (Mach.todo (M₁ skipᴬ)) }
          M₃ : Act (cell (base Bool) ∷ _) ⊤ → Mach
          M₃ x = record m₀ { conf = ⟨ H₃ , q₀ , run x (((σ ⨾ new) ⨾ new) ⨾ new) K ⟩ ; timers = mapList (wkTimer new) (Mach.timers (M₂ skipᴬ))
                           ; bursts = mapList (mapMaybe (wkPlaying new)) (Mach.bursts (M₂ skipᴬ)) ; todo = wd (Mach.todo (M₂ skipᴬ)) }
          M₄ : Act (cell (maybe quiet) ∷ _) ⊤ → Mach
          M₄ x = record m₀ { conf = ⟨ H₄ , q₀ , run x ((((σ ⨾ new) ⨾ new) ⨾ new) ⨾ new) K ⟩ ; timers = mapList (wkTimer new) (Mach.timers (M₃ skipᴬ))
                           ; bursts = mapList (mapMaybe (wkPlaying new)) (Mach.bursts (M₃ skipᴬ)) ; todo = wd (Mach.todo (M₃ skipᴬ)) }
          M₅ : Act (cell (maybe quiet) ∷ _) ⊤ → Mach
          M₅ x = record m₀ { conf = ⟨ H₅ , q₀ , run x (((((σ ⨾ new) ⨾ new) ⨾ new) ⨾ new) ⨾ new) K ⟩ ; timers = mapList (wkTimer new) (Mach.timers (M₄ skipᴬ))
                           ; bursts = mapList (mapMaybe (wkPlaying new)) (Mach.bursts (M₄ skipᴬ)) ; todo = wd (Mach.todo (M₄ skipᴬ)) }
          path = then (cong (λ x → step (M₁ x)) e₁) (then (cong (λ x → step (M₂ x)) e₂) (then (cong (λ x → step (M₃ x)) e₃)
                   (then (cong (λ x → step (M₄ x)) e₄) (then (cong (λ x → step (M₅ x)) e₅) now))))

  -- A cell the grown world made past its old names, stored to: the run
  -- reads as it did, the tree naming only what the world held before.
  module Stored {h} (H : Heapᴹ h) {t} (i : Ref h t) (x : Run.El (Pureᴾ R) h t) where
    H′ : Heapᴹ h
    H′ = store H i (lift x)

    postulate
      -- The queue and what the run is owed read no cell outside the tree's names.
      store-queue : ∀ {T : Sub h [] R} {q clk ts} → Alike H H′ (names T) → Queue H q clk ts T → Queue H′ q clk ts T
      store-owned : ∀ {T : Sub h [] R} {q ctl bs} {ca : CtlAs T q ctl bs} → Alike H H′ (names T) → Owned H T ca → Owned H′ T ca

  grew-store : ∀ {h₀} {H₀ : Heapᴹ h₀} {T₀ : Sub h₀ [] R} {Δ A} {s : T.Obs Timeline Δ A} {q} {π₀ : Path T₀ (pendingˢ s q)}
                 {u} {E′ : Env Δ u} {υ : u ⊑ h₀} {w} {σ : w ⊑ h₀} {K : Stack w ⊤} {clk}
                 {h} {ν : h₀ ⊑ h} {H : Heapᴹ h} {bs ts} {t} (i : Ref h t) (x : Run.El (Pureᴾ R) h t)
             → (∀ (j : Ref h₀ t) → wkR ν j ≢ i)
             → Grew H₀ π₀ E′ υ σ K clk ν H bs ts → Grew H₀ π₀ E′ υ σ K clk ν (store H i (lift x)) bs ts
  grew-store {ν = ν} {H = H} i x ap G = record
    { tree = tree G ; path = path G ; stack = stack G ; alone = alone G ; ticked = ticked G
    ; obsR = obsR G ; kontR = kontR G ; envR = envR G ; pends = pends G ; named = named G ; distinct = distinct G
    ; meets   = trans (part-alike H S.H′ (tree G) al) (meets G)
    ; owned   = S.store-owned al (owned G)
    ; kernels = record { holds   = holds-alike (tree G) al (Kernels.holds (kernels G))
                       ; gated   = gated-alike (tree G) al (Kernels.gated (kernels G))
                       ; settled = Kernels.settled (kernels G) }
    ; meaning = record { fed = Heaps.fed-alike H S.H′ (tree G) al _ (Meaning.fed (meaning G)) }
    ; queue   = S.store-queue al (queue G)
    ; behind  = each-alike H S.H′ al (behind G)
    ; lingers = lingers-alike H S.H′ al (lingers G) ; leaving = leaving-alike H S.H′ al (leaving G)
    ; flags   = flags-alike H S.H′ al (flags G) }
    where
      open Grew
      module S = Stored H i x
      al : Alike H S.H′ (names (tree G))
      al j m = look-store H i j (λ e → apart e m)
        where apart : ∀ {k} {j′ : _ ∋ k} → _≡_ {A = Name _} (cell _ , i) (k , j′) → (k , j′) ∈ names (tree G) → ⊥
              apart refl m′ = ap (proj₁ (named G m′)) (proj₂ (named G m′))
