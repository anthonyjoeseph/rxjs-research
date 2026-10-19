{-# OPTIONS --guardedness #-}

-- A WORLD GROWN BY ALLOCATION: a tree weakened along it owes, holds and
-- reads what it did.
module adequacy.Weaken where

open import Data.List using (List; []; _∷_; _++_; [_]; length) renaming (map to mapᴸ)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (tabulate to tabulateᴬ; lookup to lookupᴬ; map to all-map)
open import Data.List.Relation.Unary.Any using () renaming (here to hereᴬ; there to thereᴬ)
open import Data.List.Relation.Unary.Any.Properties using () renaming (++⁻ to any-++⁻; ++⁺ˡ to any-++⁺ˡ; ++⁺ʳ to any-++⁺ʳ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁻ to all-++⁻; ++⁺ to all-++⁺)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_) renaming (map to pairs-map)
open import Data.List.Relation.Unary.Linked using (Linked; []; [-]; _∷_)
open import Data.List.Relation.Unary.AllPairs.Properties using () renaming (map⁺ to pairs-map⁺; ++⁺ to pairs-++⁺)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_; ↭-sym; ↭-trans; ↭-reflexive) renaming (refl to ↭-refl′; prep to ↭-prep′; swap to ↭-swap′; trans to ↭-trans′)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (All-resp-↭; shifts) renaming (++⁺ˡ to ↭-++⁺ˡ; ++⁺ʳ to ↭-++⁺ʳ)
open import Data.List.Properties using (map-++; ++-assoc) renaming (++-identityʳ to ++-idʳ)
open import Data.Maybe using (Maybe; just; nothing; is-just; is-nothing) renaming (map to mapMaybe)
open import Data.Nat using (_+_)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Unit using (⊤)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤₁; tt to tt₁)
open import Data.Bool using (true; if_then_else_)
open import Relation.Nullary using (¬_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import denotation.MonotonicList.Events using (Timeline; Frame; From; Pos; ix; last; tick; at; _<ᵖ_; <ᵖ-below) renaming (done to doneᶠᵐ; quiet to quietᶠᵐ)
open import denotation.MonotonicList.Events using () renaming (sub to subᴾ)
import Tree as T
import denotation.Unfold as U
open import operation.Machine using (module Machine)
open import operation.PureObservable using (Out; Pureᴾ)
open import operation.AbstractObservable using (module Heap; module Run; maybe; sink; list; quiet; joins) renaming (module Machine to Shared)
open import adequacy.Strong using (module Strongly)
open import adequacy.Strong.Against using (module StrongAgainst)
open import adequacy.Strong.Held using (module StrongHeld)
open import adequacy.Moves using (module Moving)
open import adequacy.Unsub using (module Unsubbing)
open import adequacy.Grow using (module Growing)
open import adequacy.Seq using (module Sequencing)
open import adequacy.Alike using (module Aliking)
open import operation.PureObservable using (module Pure)


module Weakening (R : Set) where
  open Machine R using (wkPlaying)
  open Unsubbing R using (then; ≗-trans; wk≗; same-⨾; wkEnv-same)
  open Growing R using (wkTree; wkLanes; wkPath; wkPathᴸ; wkFeed; wkPair)
  open Sequencing R using (wkEnv-wk; wk-wk; ⨾-assoc)
  open Aliking R using (obs-refl; lookup-wkEnv; walk-grow; emit-wk; cut-wk; seq-wk≗; ObsRel; KontRel; compile-at; ≗-sym; killAll-wk; scan-wk; take-wk; outer-wk; laneO-wk; feeder-wk; body-wk; refill-wk; joiner-wk)
  open Pure R using (Timer; wkTimer; mapList; cascade)
  open Shared Timeline (Out R) using (Heapᴹ; ⟨_,_,_⟩; look; cbs; wkVal; Callbacks)
  open Heap using (World; _⊑_; _⨾_; _∋_; there; grow; wk∋; slot; Sink; Quiet; Handle) renaming (same to same⊑)
  open Run (Pureᴾ R) using (Act; El; Subject; wkSubject; send; finish; under; done; compile; Env; wkEnv; wkAct; module Kit; module FlatKit; Ref; wkR; wkEl; Observer; Kont; wkObs; wkKont)
  open Strongly R using (Sub; pendingˢ; ofˢ; mapˢ; takeWhileˢ; connectˢ; Lane; ending; taken; idle; feeding; finishing; Path; PathLanes; here; in-map; in-scan; in-take; in-outer; in-lanes; in-source; in-body; in-defer; this-lane; next-lane; Here; walk; top; coldˢ; _≗_; module At; pendings; rootObs; Owes; Begun; Settled; SettledLanes; Feed; Phase; timerOf; lanePendings; subjects; joiners; flatMapˢ; scanˢ; joinˢ; doneˢ; deferˢ; lane; CbRel; ≗-refl; taking; Call; emitC; kontC; take1C; take2C; bodyC; feedC; finC; srcC; code; ⟦_⟧; Leaf; of-leaf; cold-leaf; done-leaf; join-leaf; _⊕_; _⊕ᴸ_; under≗; unsub; killAllᶜ; Joiner; joiner; laneSubjects; laneJoiners)
  open StrongAgainst R using (Owned; Kernels; Meaning; Queue; Each; Lingers; Tied; seen; seenL; isTaking; at⟦_⟧; Spot; spot; Job)
  open StrongHeld R using (DoneBy)
  open StrongAgainst.Against R using (StackAs; subAs; runAs; CtlAs; agenda; bursts; begins; stackJobs; SrcOf; Ticked; stackBursts; sources; Placed; restAs; backAs; reholdAs; bottomAs; BurstAs; playsAs; firesAs; overAs; Held; bottomᴴ; restᴴ; BurstClocked; src-of)
  open Strongly.Phase R using (waiting; playing; fired)
  open Moving R using (pend; pendᴸ)

  -- The runtime's own map is the library's.
  pure-map : ∀ {a b} {X : Set a} {Y : Set b} (f : X → Y) (xs : List X) → mapList f xs ≡ mapᴸ f xs
  pure-map f []       = refl
  pure-map f (x ∷ xs) = cong (f x ∷_) (pure-map f xs)

  -- A WORLD GROWN BY ALLOCATION: every name the old heap held reads as it
  -- did, weakened.
  record Grows {h v} (τ : h ⊑ v) (H : Heapᴹ h) (H′ : Heapᴹ v) : Set₁ where
    field
      cells   : ∀ {t} (x : Ref h t) → At.val H′ (wkR τ x) ≡ wkEl t τ (At.val H x)
      slots   : ∀ {X} (s : Sink h X) → CbRel (cbs H′ (wk∋ τ s)) (wkVal (slot X) τ (cbs H s))
      stashes : ∀ (u : Quiet h) → look H′ (wk∋ τ u) ≗ wkAct τ (look H u)
      handles : ∀ (hd : Handle h) → At.spentʰ H′ (wk∋ τ hd) ≡ At.spentʰ H hd

  -- A tree weakened owes what it did.
  mutual
    pend-grow : ∀ {h v Δ A} (τ : h ⊑ v) (t : Sub h Δ A) → pend (wkTree τ t) ≡ pend t
    pend-grow τ (pendingˢ s q)                       = refl
    pend-grow τ (coldˢ s hd ph)                      = refl
    pend-grow τ (ofˢ p i xs)                         = refl
    pend-grow τ doneˢ                                = refl
    pend-grow τ (mapˢ f t)                           = pend-grow τ t
    pend-grow τ (scanˢ f r t)                        = pend-grow τ t
    pend-grow τ (takeWhileˢ i p c k tk t)            = pend-grow τ t
    pend-grow τ (flatMapˢ op f fl oc k r pl t ls)    = cong₂ _+_ (pend-grow τ t) (pend-growᴸ τ ls)
    pend-grow τ (connectˢ S c b kb k fd q e rt s bd) = cong₂ _+_ (pend-grow τ s) (pend-grow τ bd)
    pend-grow τ (joinˢ j s fl x m)                   = refl
    pend-grow τ (deferˢ k t)                         = pend-grow τ t

    pend-growᴸ : ∀ {h v Δ B} (τ : h ⊑ v) (ls : List (Lane h Δ B)) → pendᴸ (wkLanes τ ls) ≡ pendᴸ ls
    pend-growᴸ τ []                 = refl
    pend-growᴸ τ (lane c k t ∷ ls) = cong₂ _+_ (pend-grow τ t) (pend-growᴸ τ ls)

  module Grown {h v} (τ : h ⊑ v) where
    -- A path joined, weakened, is the weakened paths joined.
    mutual
      wkPath-⊕ : ∀ {Δ A Δ′ A′ Δ″ A″} {t : Sub h Δ A} {u : Sub h Δ′ A′} {x : Sub h Δ″ A″} (p : Path t u) (q : Path u x)
               → wkPath τ (p ⊕ q) ≡ wkPath τ p ⊕ wkPath τ q
      wkPath-⊕ here          q = refl
      wkPath-⊕ (in-map p)    q = cong in-map (wkPath-⊕ p q)
      wkPath-⊕ (in-scan p)   q = cong in-scan (wkPath-⊕ p q)
      wkPath-⊕ (in-take p)   q = cong in-take (wkPath-⊕ p q)
      wkPath-⊕ (in-outer p)  q = cong in-outer (wkPath-⊕ p q)
      wkPath-⊕ (in-lanes p)  q = cong in-lanes (wkPathᴸ-⊕ p q)
      wkPath-⊕ (in-source p) q = cong in-source (wkPath-⊕ p q)
      wkPath-⊕ (in-body p)   q = cong in-body (wkPath-⊕ p q)
      wkPath-⊕ (in-defer p)  q = cong in-defer (wkPath-⊕ p q)

      wkPathᴸ-⊕ : ∀ {Δ B Δ′ A′ Δ″ A″} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} {x : Sub h Δ″ A″} (p : PathLanes ls u) (q : Path u x)
                → wkPathᴸ τ (p ⊕ᴸ q) ≡ wkPathᴸ τ p ⊕ᴸ wkPath τ q
      wkPathᴸ-⊕ (this-lane p) q = cong this-lane (wkPath-⊕ p q)
      wkPathᴸ-⊕ (next-lane p) q = cong next-lane (wkPathᴸ-⊕ p q)

    -- Two paths alike once weakened were alike.
    private
      map-inj : ∀ {Δ A Δ′ A′ B} {f : A → B} {s : Sub v Δ A} {u : Sub v Δ′ A′} {x y : Path s u} → in-map {f = f} x ≡ in-map y → x ≡ y
      map-inj refl = refl
      scan-inj : ∀ {Δ A Δ′ A′ B} {f : B → A → B} {r} {s : Sub v Δ A} {u : Sub v Δ′ A′} {x y : Path s u} → in-scan {f = f} {r = r} x ≡ in-scan y → x ≡ y
      scan-inj refl = refl
      take-inj : ∀ {Δ A Δ′ A′} {i p c k tk} {s : Sub v Δ A} {u : Sub v Δ′ A′} {x y : Path s u} → in-take {i = i} {p} {c} {k} {tk} x ≡ in-take y → x ≡ y
      take-inj refl = refl
      outer-inj : ∀ {Δ A B Δ′ C} {op f fl oc k r pl} {s : Sub v Δ A} {ls : List (Lane v Δ B)} {u : Sub v Δ′ C} {x y : Path s u}
                → in-outer {op = op} {f} {fl} {oc} {k} {r} {pl} {ls = ls} x ≡ in-outer y → x ≡ y
      outer-inj refl = refl
      lanes-inj : ∀ {Δ A B Δ′ C} {op f fl oc k r pl} {s : Sub v Δ A} {ls : List (Lane v Δ B)} {u : Sub v Δ′ C} {x y : PathLanes ls u}
                → in-lanes {op = op} {f} {fl} {oc} {k} {r} {pl} {t = s} x ≡ in-lanes y → x ≡ y
      lanes-inj refl = refl
      source-inj : ∀ {Δ A B Δ′ C} {S c b kb k fd e rp rt} {s : Sub v Δ A} {bd : Sub v (A ∷ Δ) B} {u : Sub v Δ′ C} {x y : Path s u}
                 → in-source {S = S} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {bd = bd} x ≡ in-source y → x ≡ y
      source-inj refl = refl
      body-inj : ∀ {Δ A B Δ′ C} {S c b kb k fd e rp rt} {s : Sub v Δ A} {bd : Sub v (A ∷ Δ) B} {u : Sub v Δ′ C} {x y : Path bd u}
               → in-body {S = S} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {t = s} x ≡ in-body y → x ≡ y
      body-inj refl = refl
      defer-inj : ∀ {Δ A Δ′ C} {k} {s : Sub v Δ A} {u : Sub v Δ′ C} {x y : Path s u} → in-defer {k = k} x ≡ in-defer y → x ≡ y
      defer-inj refl = refl
      this-inj : ∀ {Δ B Δ′ C} {c k} {s : Sub v Δ B} {ls} {u : Sub v Δ′ C} {x y : Path s u} → this-lane {c = c} {k} {ls = ls} x ≡ this-lane y → x ≡ y
      this-inj refl = refl
      next-inj : ∀ {Δ B Δ′ C} {l} {ls : List (Lane v Δ B)} {u : Sub v Δ′ C} {x y : PathLanes ls u} → next-lane {l = l} x ≡ next-lane y → x ≡ y
      next-inj refl = refl

    mutual
      wkPath-inj : ∀ {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π π′ : Path t u) → wkPath τ π ≡ wkPath τ π′ → π ≡ π′
      wkPath-inj here          here           _ = refl
      wkPath-inj here          (in-map _)     ()
      wkPath-inj here          (in-scan _)    ()
      wkPath-inj here          (in-take _)    ()
      wkPath-inj here          (in-outer _)   ()
      wkPath-inj here          (in-lanes _)   ()
      wkPath-inj here          (in-source _)  ()
      wkPath-inj here          (in-body _)    ()
      wkPath-inj here          (in-defer _)   ()
      wkPath-inj (in-map _)    here           ()
      wkPath-inj (in-scan _)   here           ()
      wkPath-inj (in-take _)   here           ()
      wkPath-inj (in-outer _)  here           ()
      wkPath-inj (in-lanes _)  here           ()
      wkPath-inj (in-source _) here           ()
      wkPath-inj (in-body _)   here           ()
      wkPath-inj (in-defer _)  here           ()
      wkPath-inj (in-map p)    (in-map p′)    e = cong in-map (wkPath-inj p p′ (map-inj e))
      wkPath-inj (in-scan p)   (in-scan p′)   e = cong in-scan (wkPath-inj p p′ (scan-inj e))
      wkPath-inj (in-take p)   (in-take p′)   e = cong in-take (wkPath-inj p p′ (take-inj e))
      wkPath-inj (in-outer p)  (in-outer p′)  e = cong in-outer (wkPath-inj p p′ (outer-inj e))
      wkPath-inj (in-outer _)  (in-lanes _)   ()
      wkPath-inj (in-lanes _)  (in-outer _)   ()
      wkPath-inj (in-lanes p)  (in-lanes p′)  e = cong in-lanes (wkPathᴸ-inj p p′ (lanes-inj e))
      wkPath-inj (in-source p) (in-source p′) e = cong in-source (wkPath-inj p p′ (source-inj e))
      wkPath-inj (in-source _) (in-body _)    ()
      wkPath-inj (in-body _)   (in-source _)  ()
      wkPath-inj (in-body p)   (in-body p′)   e = cong in-body (wkPath-inj p p′ (body-inj e))
      wkPath-inj (in-defer p)  (in-defer p′)  e = cong in-defer (wkPath-inj p p′ (defer-inj e))

      wkPathᴸ-inj : ∀ {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (π π′ : PathLanes ls u) → wkPathᴸ τ π ≡ wkPathᴸ τ π′ → π ≡ π′
      wkPathᴸ-inj (this-lane p) (this-lane p′) e = cong this-lane (wkPath-inj p p′ (this-inj e))
      wkPathᴸ-inj (this-lane _) (next-lane _)  ()
      wkPathᴸ-inj (next-lane _) (this-lane _)  ()
      wkPathᴸ-inj (next-lane p) (next-lane p′) e = cong next-lane (wkPathᴸ-inj p p′ (next-inj e))

    -- A leaf weakened is a leaf; a call, aimed along the weakened tree.
    leaf-grow : ∀ {Δ A} {u : Sub h Δ A} → Leaf u → Leaf (wkTree τ u)
    leaf-grow of-leaf   = of-leaf
    leaf-grow cold-leaf = cold-leaf
    leaf-grow done-leaf = done-leaf
    leaf-grow join-leaf = join-leaf

    wkCall : ∀ {t : Sub h [] R} → Call t → Call (wkTree τ t)
    wkCall (emitC π)   = emitC (wkPath τ π)
    wkCall (kontC l π) = kontC (leaf-grow l) (wkPath τ π)
    wkCall (take1C π)  = take1C (wkPath τ π)
    wkCall (take2C π)  = take2C (wkPath τ π)
    wkCall (bodyC π)   = bodyC (wkPath τ π)
    wkCall (feedC π)   = feedC (wkPath τ π)
    wkCall (finC π)    = finC (wkPath τ π)
    wkCall (srcC π)    = srcC (wkPath τ π)

    postulate
      -- A leaf's continuation, handed what unsubscribes it, reads alike
      -- along the growth: the continuation's own naturality.
      kont-grow    : ∀ {t : Sub h [] R} {Δ A} {u : Sub h Δ A} (l : Leaf u) (π : Path t u)
                   → wkAct τ (code (kontC l π)) ≗ code (kontC (leaf-grow l) (wkPath τ π))
      -- A compiled subscription reads alike along the growth: the code's
      -- own naturality.
      compile-grow : ∀ {Γ A u} (s : T.Obs Timeline Γ A) (E : Env Γ u) (υ : u ⊑ h) {o : Observer A h} {o′ : Observer A v} {k : Kont h} {k′ : Kont v}
                   → ObsRel (wkObs τ o) o′ → KontRel (wkKont τ k) k′ → wkAct τ (compile s E υ o k) ≗ compile s E (υ ⨾ τ) o′ k′

    -- Each call's code, weakened, is the weakened call's.
    call-grow : ∀ {t : Sub h [] R} (c : Call t) → wkAct τ (code c) ≗ code (wkCall c)
    call-grow (emitC {i = i} {xs} π) = emit-wk τ (Here.obs (walk π top)) (Here.obs (walk (wkPath τ π) top)) (proj₁ (walk-grow τ π)) i xs
    call-grow (kontC l π)            = kont-grow l π
    call-grow (take1C {c = c} π)     = under≗ (proj₁ (proj₂ (proj₁ (walk-grow τ π)))) (cut-wk τ c)
    call-grow (take2C {c = c} π)     = cut-wk τ c
    call-grow (bodyC {c = c} π)      = cut-wk τ c
    call-grow (feedC {x = x} {ss = ss} π) = sends-wk ss
      where
        sends-wk : ∀ ss → wkAct τ (Kit.each ss λ j → under (subᴾ (proj₂ j)) (send (proj₁ j) x Kit.skipᴬ) Kit.skipᴬ)
                        ≗ Kit.each (mapᴸ (wkPair τ) ss) λ j → under (subᴾ (proj₂ j)) (send (proj₁ j) x Kit.skipᴬ) Kit.skipᴬ
        sends-wk []             = ≗-refl _
        sends-wk ((s , j) ∷ ss) = seq-wk≗ τ (under (subᴾ j) (send s x Kit.skipᴬ) Kit.skipᴬ) _ (≗-refl _) (sends-wk ss)
    call-grow (finC {ss = ss} π)      = fins-wk ss
      where
        fins-wk : ∀ ss → wkAct τ (Kit.each ss λ j → under (subᴾ (proj₂ j)) (finish (proj₁ j) Kit.skipᴬ) Kit.skipᴬ)
                       ≗ Kit.each (mapᴸ (wkPair τ) ss) λ j → under (subᴾ (proj₂ j)) (finish (proj₁ j) Kit.skipᴬ) Kit.skipᴬ
        fins-wk []             = ≗-refl _
        fins-wk ((s , j) ∷ ss) = seq-wk≗ τ (under (subᴾ j) (finish s Kit.skipᴬ) Kit.skipᴬ) _ (≗-refl _) (fins-wk ss)
    call-grow (srcC {s₁ = s₁} π) =
      under≗ (subst (λ ψ → wkAct τ (compile s₁ (Here.env H) same⊑ (Here.obs H) (Here.kont H))
                           ≗ compile s₁ (Here.env (walk ψ top)) same⊑ (Here.obs (walk ψ top)) (Here.kont (walk ψ top)))
                    (wkPath-⊕ π (in-source here))
                    (≗-trans (compile-grow s₁ (Here.env H) same⊑ {o = Here.obs H} {o′ = Here.obs H′} {k = Here.kont H} {k′ = Here.kont H′} oR kR)
                             (compile-at s₁ (Here.env H) (Here.env H′) (same⊑ ⨾ τ) same⊑
                                (trans (cong (λ ζ → wkEnv ζ (Here.env H)) (same-⨾ τ)) (trans eR (sym (wkEnv-same (Here.env H′))))))))
             (≗-refl _)
      where
        H  = walk (π ⊕ in-source here) top
        H′ = walk (wkPath τ (π ⊕ in-source here)) top
        oR = proj₁ (walk-grow τ (π ⊕ in-source here))
        kR = proj₁ (proj₂ (walk-grow τ (π ⊕ in-source here)))
        eR = proj₂ (proj₂ (walk-grow τ (π ⊕ in-source here)))

    calls-grow : ∀ {t : Sub h [] R} (ks : List (Call t)) → wkAct τ ⟦ ks ⟧ ≗ ⟦ mapList wkCall ks ⟧
    calls-grow []       = ≗-refl _
    calls-grow (c ∷ ks) = seq-wk≗ τ (code c) ⟦ ks ⟧ (call-grow c) (calls-grow ks)

    burst-grow : ∀ {t : Sub h [] R} {b} → BurstAs t b → BurstAs (wkTree τ t) (mapMaybe (wkPlaying τ) b)
    burst-grow (playsAs π) = playsAs (wkPath τ π)
    burst-grow (firesAs π) = firesAs (wkPath τ π)
    burst-grow overAs      = overAs

    held-grow : ∀ {t : Sub h [] R} {w} {K} → Held t {w} K → Held (wkTree τ t) {w} K
    held-grow bottomᴴ = bottomᴴ
    held-grow restᴴ   = restᴴ

    act-grow : ∀ {t : Sub h [] R} {w} (σ : w ⊑ h) {σ′ : w ⊑ v} → σ ⨾ τ ≡ σ′ → (m : Act w ⊤) (ks : List (Call t))
             → wkAct σ m ≗ ⟦ ks ⟧ → wkAct σ′ m ≗ ⟦ mapList wkCall ks ⟧
    act-grow σ refl m ks r = ≗-trans (≗-sym (wk-wk σ τ m)) (≗-trans (wk≗ τ r) (calls-grow ks))

    assoc-step : ∀ {u w} (ρ : u ⊑ w) (σ : w ⊑ h) {σ′ : w ⊑ v} → σ ⨾ τ ≡ σ′ → (ρ ⨾ σ) ⨾ τ ≡ ρ ⨾ σ′
    assoc-step ρ σ e = trans (sym (⨾-assoc ρ σ τ)) (cong (ρ ⨾_) e)

    -- The stack, its calls aimed along the weakened tree, read from any
    -- world the weakening reaches.
    stack-grow : ∀ {t : Sub h [] R} {p w} {σ : w ⊑ h} {σ′ : w ⊑ v} {K bs} → σ ⨾ τ ≡ σ′ → StackAs t p σ K bs
               → StackAs (wkTree τ t) p σ′ K (mapList (mapMaybe (wkPlaying τ)) bs)
    stack-grow e bottomAs = bottomAs
    stack-grow {σ = σ} e (restAs {m = m} {ρ = ρ} ks r K) = restAs (mapList wkCall ks) (act-grow σ e m ks r) (stack-grow (assoc-step ρ σ e) K)
    stack-grow {σ = σ} e (backAs q {m = m} {ρ = ρ} ks lt r K) = backAs q (mapList wkCall ks) lt (act-grow σ e m ks r) (stack-grow (assoc-step ρ σ e) K)
    stack-grow {σ = σ} e (reholdAs {ρ = ρ} b hd K) = reholdAs (burst-grow b) (held-grow hd) (stack-grow (assoc-step ρ σ e) K)

    grow-stack : ∀ {t : Sub h [] R} {p w} {σ : w ⊑ h} {K bs} → StackAs t p σ K bs
               → StackAs (wkTree τ t) p (σ ⨾ τ) K (mapList (mapMaybe (wkPlaying τ)) bs)
    grow-stack = stack-grow refl

    -- A call owing a pending node's subscription, aimed along the
    -- weakened tree, owed it before.
    src-back : ∀ {t : Sub h [] R} {Δ A s q} (π : Path t (pendingˢ {Δ = Δ} {A} s q)) (c : Call t)
             → SrcOf (wkTree τ t) (wkPath τ π) (wkCall c) → SrcOf t π c
    src-back π (srcC ρ)    (src-of _ e) = src-of ρ (wkPath-inj π (ρ ⊕ in-source here) (trans e (sym (wkPath-⊕ ρ (in-source here)))))
    src-back π (emitC _)   ()
    src-back π (kontC _ _) ()
    src-back π (take1C _)  ()
    src-back π (take2C _)  ()
    src-back π (bodyC _)   ()
    src-back π (feedC _)   ()
    src-back π (finC _)    ()

    grow-alone : ∀ {t : Sub h [] R} {p w} {σ : w ⊑ h} {K bs} {Δ A s q} (π : Path t (pendingˢ {Δ = Δ} {A} s q)) (sk : StackAs t p σ K bs)
               → All (λ j → ¬ SrcOf t π (proj₂ j)) (stackJobs t sk) → All (λ j → ¬ SrcOf (wkTree τ t) (wkPath τ π) (proj₂ j)) (stackJobs (wkTree τ t) (grow-stack sk))
    grow-alone π sk = alone-at π refl sk
      where
        at-alone : ∀ {t : Sub h [] R} {Δ A s q} (π : Path t (pendingˢ {Δ = Δ} {A} s q)) p (ks : List (Call t))
                 → All (λ j → ¬ SrcOf t π (proj₂ j)) (at⟦ p ⟧ ks) → All (λ j → ¬ SrcOf (wkTree τ t) (wkPath τ π) (proj₂ j)) (at⟦ p ⟧ (mapList wkCall ks))
        at-alone π p []       []       = []
        at-alone π p (c ∷ ks) (n ∷ ns) = (λ x → n (src-back π c x)) ∷ at-alone π p ks ns
        alone-at : ∀ {t : Sub h [] R} {p w} {σ : w ⊑ h} {σ′ : w ⊑ v} {K bs} {Δ A s q} (π : Path t (pendingˢ {Δ = Δ} {A} s q)) (e : σ ⨾ τ ≡ σ′) (sk : StackAs t p σ K bs)
                 → All (λ j → ¬ SrcOf t π (proj₂ j)) (stackJobs t sk) → All (λ j → ¬ SrcOf (wkTree τ t) (wkPath τ π) (proj₂ j)) (stackJobs (wkTree τ t) (stack-grow e sk))
        alone-at π e bottomAs                      al = []
        alone-at {σ = σ} π e (restAs {p = p} {ρ = ρ} ks r K)     al =
          all-++⁺ (at-alone π p ks (proj₁ (all-++⁻ (at⟦ p ⟧ ks) al))) (alone-at π (assoc-step ρ σ e) K (proj₂ (all-++⁻ (at⟦ p ⟧ ks) al)))
        alone-at {σ = σ} π e (backAs q {ρ = ρ} ks lt r K) al =
          all-++⁺ (at-alone π q ks (proj₁ (all-++⁻ (at⟦ q ⟧ ks) al))) (alone-at π (assoc-step ρ σ e) K (proj₂ (all-++⁻ (at⟦ q ⟧ ks) al)))
        alone-at {σ = σ} π e (reholdAs {ρ = ρ} b hd K) al = alone-at π (assoc-step ρ σ e) K al

    grow-ticked : ∀ {t : Sub h [] R} {n p w} {σ : w ⊑ h} {K bs} (sk : StackAs t p σ K bs) → Ticked t n sk → Ticked (wkTree τ t) n (grow-stack sk)
    grow-ticked = ticked-at refl
      where
        clocked-grow : ∀ {t : Sub h [] R} {n b} (x : BurstAs t b) → BurstClocked t n x → BurstClocked (wkTree τ t) n (burst-grow x)
        clocked-grow (playsAs _) c = c
        clocked-grow (firesAs _) c = c
        clocked-grow overAs      c = c
        ticked-at : ∀ {t : Sub h [] R} {n p w} {σ : w ⊑ h} {σ′ : w ⊑ v} {K bs} (e : σ ⨾ τ ≡ σ′) (sk : StackAs t p σ K bs)
                  → Ticked t n sk → Ticked (wkTree τ t) n (stack-grow e sk)
        ticked-at e bottomAs _ = tt
        ticked-at {σ = σ} e (restAs {ρ = ρ} ks r K)     (x , y) = x , ticked-at (assoc-step ρ σ e) K y
        ticked-at {σ = σ} e (backAs q {ρ = ρ} ks lt r K) (x , y) = x , ticked-at (assoc-step ρ σ e) K y
        ticked-at {σ = σ} e (reholdAs {ρ = ρ} b hd K)   (x , y) = clocked-grow b x , ticked-at (assoc-step ρ σ e) K y


    -- What unsubscribing a node runs, weakened, is the weakened node's.
    private
      via-wk : ∀ (k : Maybe (Quiet h)) → wkAct τ (Kit.unsubscribeVia k) ≗ Kit.unsubscribeVia (mapMaybe (wk∋ τ) k)
      via-wk nothing  = ≗-refl _
      via-wk (just q) = ≗-refl _

    unsub-wk : ∀ {Δ A} (u : Sub h Δ A) → wkAct τ (unsub u) ≗ unsub (wkTree τ u)
    unsub-wk (pendingˢ s q)                          = ≗-refl _
    unsub-wk (coldˢ s hd ph)                         = ≗-refl _
    unsub-wk (ofˢ p i xs)                            = ≗-refl _
    unsub-wk doneˢ                                   = ≗-refl _
    unsub-wk (mapˢ f s)                              = unsub-wk s
    unsub-wk (scanˢ f r s)                           = unsub-wk s
    unsub-wk (takeWhileˢ i p c k tk s)               = cut-wk τ c
    unsub-wk (flatMapˢ op f fl oc k r pl so ls)      = seq-wk≗ τ (Kit.cut oc) (killAllᶜ fl) (cut-wk τ oc) (killAll-wk τ fl)
    unsub-wk (connectˢ S c b kb k fd rp e rt src bd) = seq-wk≗ τ (unsub src) (Kit.unsubscribeVia kb) (unsub-wk src) (via-wk kb)
    unsub-wk (joinˢ j sk l x st)                     = ≗-refl _
    unsub-wk (deferˢ k s)                            = via-wk k

    env-grow : ∀ {t : Sub h [] R} {Δ A} {u′ : Sub h Δ A} (π : Path t u′) {u} (E′ : Env Δ u) (υ : u ⊑ h)
             → wkEnv υ E′ ≡ Here.env (walk π top) → wkEnv (υ ⨾ τ) E′ ≡ Here.env (walk (wkPath τ π) top)
    env-grow π E′ υ e = trans (sym (wkEnv-wk υ τ E′)) (trans (cong (wkEnv τ) e) (proj₂ (proj₂ (walk-grow τ π))))

    -- A subscription still pending, along the weakened path.
    code-grow : ∀ {t : Sub h [] R} {Δ A} {s : T.Obs Timeline Δ A} {q} (π : Path t (pendingˢ s q)) {u} (E′ : Env Δ u) (υ : u ⊑ h)
              → wkEnv υ E′ ≡ Here.env (walk π top)
              → Σ World λ u′ → Σ (Env Δ u′) λ E″ → Σ (u′ ⊑ v) λ υ′ → wkEnv υ′ E″ ≡ Here.env (walk (wkPath τ π) top)
                  × compile s E′ (υ ⨾ τ) (Here.obs (walk (wkPath τ π) top)) (Here.kont (walk (wkPath τ π) top))
                    ≗ compile s E″ υ′ (Here.obs (walk (wkPath τ π) top)) (Here.kont (walk (wkPath τ π) top))
    code-grow π {u} E′ υ e = u , E′ , υ ⨾ τ , env-grow π E′ υ e , ≗-refl _

    -- A node of the grown tree held where it is a flatMap, or a
    -- connect: the weakening of one, which the old tree held.
    data FlatBack {Δ′ B′} : Sub v Δ′ B′ → Sub h Δ′ B′ → Set₁ where
      flat-back : ∀ {A′} {op f fl oc k r pl} {so : Sub h Δ′ A′} {ls : List (Lane h Δ′ B′)}
                → FlatBack (wkTree τ (flatMapˢ op f fl oc k r pl so ls)) (flatMapˢ op f fl oc k r pl so ls)

    data ConnBack {Δ′ B′} : Sub v Δ′ B′ → Sub h Δ′ B′ → Set₁ where
      conn-back : ∀ {A′} {S c b kb k fd rp e rt} {src : Sub h Δ′ A′} {bd : Sub h (A′ ∷ Δ′) B′}
                → ConnBack (wkTree τ (connectˢ S c b kb k fd rp e rt src bd)) (connectˢ S c b kb k fd rp e rt src bd)

    flat-inv : ∀ {Δ′ A′ B′} {op f fl′ oc′ k′ r′ pl} {so′ : Sub v Δ′ A′} {ls′ : List (Lane v Δ′ B′)} (x : Sub h Δ′ B′)
             → flatMapˢ op f fl′ oc′ k′ r′ pl so′ ls′ ≡ wkTree τ x → FlatBack (flatMapˢ op f fl′ oc′ k′ r′ pl so′ ls′) x
    flat-inv (flatMapˢ op f fl oc k r pl so ls)     refl = flat-back
    flat-inv (pendingˢ s q)                         ()
    flat-inv (coldˢ s hd ph)                        ()
    flat-inv (ofˢ p i xs)                           ()
    flat-inv doneˢ                                  ()
    flat-inv (mapˢ f s)                             ()
    flat-inv (scanˢ f r s)                          ()
    flat-inv (takeWhileˢ i p c k tk s)              ()
    flat-inv (connectˢ S c b kb k fd rp e rt src bd) ()
    flat-inv (joinˢ j sk l x st)                    ()
    flat-inv (deferˢ k s)                           ()

    conn-inv : ∀ {Δ′ A′ B′} {S′ c′ b′ kb′ k′ fd′ rp e rt} {src′ : Sub v Δ′ A′} {bd′ : Sub v (A′ ∷ Δ′) B′} (x : Sub h Δ′ B′)
             → connectˢ S′ c′ b′ kb′ k′ fd′ rp e rt src′ bd′ ≡ wkTree τ x → ConnBack (connectˢ S′ c′ b′ kb′ k′ fd′ rp e rt src′ bd′) x
    conn-inv (connectˢ S c b kb k fd rp e rt src bd) refl = conn-back
    conn-inv (pendingˢ s q)                         ()
    conn-inv (coldˢ s hd ph)                        ()
    conn-inv (ofˢ p i xs)                           ()
    conn-inv doneˢ                                  ()
    conn-inv (mapˢ f s)                             ()
    conn-inv (scanˢ f r s)                          ()
    conn-inv (takeWhileˢ i p c k tk s)              ()
    conn-inv (flatMapˢ op f fl oc k r pl so ls)     ()
    conn-inv (joinˢ j sk l x st)                    ()
    conn-inv (deferˢ k s)                           ()

    -- What a weakened tree owes, and what it has begun.
    owes-wk : ∀ {Δ A} (u : Sub h Δ A) → Owes (wkTree τ u) → Owes u
    owes-wk (pendingˢ s q)                          o = o
    owes-wk (mapˢ f s)                              o = owes-wk s o
    owes-wk (scanˢ f r s)                           o = owes-wk s o
    owes-wk (connectˢ S c b kb k fd rp e rt src bd) o = owes-wk src o
    owes-wk (coldˢ s hd ph)                         ()
    owes-wk (ofˢ p i xs)                            ()
    owes-wk doneˢ                                   ()
    owes-wk (takeWhileˢ i p c k tk s)               ()
    owes-wk (flatMapˢ op f fl oc k r pl so ls)      ()
    owes-wk (joinˢ j sk l x st)                     ()
    owes-wk (deferˢ k s)                            ()

    begun-wk : ∀ {Δ A} (k : Maybe (Quiet h)) (u : Sub h Δ A) → Begun k u → Begun (mapMaybe (wk∋ τ) k) (wkTree τ u)
    begun-wk nothing  u _ = tt
    begun-wk (just _) u b = λ o → b (owes-wk u o)

    -- The pending frames' timers, weakened.
    timerOf-wk : ∀ {A} (s : Sink h A) (hd : Handle h) (ph : Phase A) → timerOf (wk∋ τ s) (wk∋ τ hd) ph ≡ mapList (wkTimer τ) (timerOf s hd ph)
    timerOf-wk s hd (waiting τ′ e (at t le b)) = refl
    timerOf-wk s hd (waiting τ′ e doneᶠᵐ)      = refl
    timerOf-wk s hd (waiting τ′ e quietᶠᵐ)     = refl
    timerOf-wk s hd (fired _ _ _)              = refl
    timerOf-wk s hd (playing _ _ _ _)          = refl

    mapL-++ : ∀ {a b} {X : Set a} {Y : Set b} (f : X → Y) (xs ys : List X) → mapList f (xs ++ ys) ≡ mapList f xs ++ mapList f ys
    mapL-++ f []       ys = refl
    mapL-++ f (x ∷ xs) ys = cong (f x ∷_) (mapL-++ f xs ys)

    ∈-mapL : ∀ {a b} {X : Set a} {Y : Set b} (f : X → Y) {x xs} → x ∈ xs → f x ∈ mapList f xs
    ∈-mapL f (hereᴬ refl) = hereᴬ refl
    ∈-mapL f (thereᴬ m)   = thereᴬ (∈-mapL f m)

    all-mapL : ∀ {a b p q} {X : Set a} {Y : Set b} {P : X → Set p} {Q : Y → Set q} (f : X → Y) → (∀ {x} → P x → Q (f x))
             → ∀ {xs} → All P xs → All Q (mapList f xs)
    all-mapL f g []         = []
    all-mapL f g (px ∷ pxs) = g px ∷ all-mapL f g pxs

    linked-mapL : ∀ {ts : List (Timer h)} → Linked (λ x y → cascade x <ᵖ cascade y ≡ true) ts
                → Linked (λ x y → cascade x <ᵖ cascade y ≡ true) (mapList (wkTimer τ) ts)
    linked-mapL []      = []
    linked-mapL [-]     = [-]
    linked-mapL (r ∷ l) = r ∷ linked-mapL l

    mutual
      pendings-wk : ∀ {Δ A} (u : Sub h Δ A) → pendings (wkTree τ u) ≡ mapList (wkTimer τ) (pendings u)
      pendings-wk (pendingˢ s q)                          = refl
      pendings-wk (coldˢ s hd ph)                         = timerOf-wk s hd ph
      pendings-wk (ofˢ p i xs)                            = refl
      pendings-wk doneˢ                                   = refl
      pendings-wk (mapˢ f s)                              = pendings-wk s
      pendings-wk (scanˢ f r s)                           = pendings-wk s
      pendings-wk (takeWhileˢ i p c k tk s)               = pendings-wk s
      pendings-wk (flatMapˢ op f fl oc k r pl so ls)      =
        trans (cong₂ _++_ (pendings-wk so) (pendings-wkᴸ ls)) (sym (mapL-++ (wkTimer τ) (pendings so) (lanePendings ls)))
      pendings-wk (connectˢ S c b kb k fd rp e rt src bd) =
        trans (cong₂ _++_ (pendings-wk src) (pendings-wk bd)) (sym (mapL-++ (wkTimer τ) (pendings src) (pendings bd)))
      pendings-wk (joinˢ j sk l x st)                     = refl
      pendings-wk (deferˢ k s)                            = pendings-wk s

      pendings-wkᴸ : ∀ {Δ B} (ls : List (Lane h Δ B)) → lanePendings (wkLanes τ ls) ≡ mapList (wkTimer τ) (lanePendings ls)
      pendings-wkᴸ []                = refl
      pendings-wkᴸ (lane c k s ∷ ls) =
        trans (cong₂ _++_ (pendings-wk s) (pendings-wkᴸ ls)) (sym (mapL-++ (wkTimer τ) (pendings s) (lanePendings ls)))

    wkSubj : Σ Set (λ A → Subject A h) → Σ Set (λ A → Subject A v)
    wkSubj (A , S) = A , wkSubject τ S

    wkJoiner : Joiner h → Joiner v
    wkJoiner (joiner S sk j) = joiner (wkSubject τ S) (wk∋ τ sk) j

    mutual
      subjects-wk : ∀ {Δ A} (u : Sub h Δ A) → subjects (wkTree τ u) ≡ mapList wkSubj (subjects u)
      subjects-wk (pendingˢ s q)                          = refl
      subjects-wk (coldˢ s hd ph)                         = refl
      subjects-wk (ofˢ p i xs)                            = refl
      subjects-wk doneˢ                                   = refl
      subjects-wk (mapˢ f s)                              = subjects-wk s
      subjects-wk (scanˢ f r s)                           = subjects-wk s
      subjects-wk (takeWhileˢ i p c k tk s)               = subjects-wk s
      subjects-wk (flatMapˢ op f fl oc k r pl so ls)      =
        trans (cong₂ _++_ (subjects-wk so) (subjects-wkᴸ ls)) (sym (mapL-++ wkSubj (subjects so) (laneSubjects ls)))
      subjects-wk (connectˢ S c b kb k fd rp e rt src bd) =
        cong (wkSubj (_ , S) ∷_) (trans (cong₂ _++_ (subjects-wk src) (subjects-wk bd)) (sym (mapL-++ wkSubj (subjects src) (subjects bd))))
      subjects-wk (joinˢ j sk l x st)                     = refl
      subjects-wk (deferˢ k s)                            = subjects-wk s

      subjects-wkᴸ : ∀ {Δ B} (ls : List (Lane h Δ B)) → laneSubjects (wkLanes τ ls) ≡ mapList wkSubj (laneSubjects ls)
      subjects-wkᴸ []                = refl
      subjects-wkᴸ (lane c k s ∷ ls) =
        trans (cong₂ _++_ (subjects-wk s) (subjects-wkᴸ ls)) (sym (mapL-++ wkSubj (subjects s) (laneSubjects ls)))

    mutual
      joiners-wk : ∀ {Δ A} (u : Sub h Δ A) (E : Env Δ h) → joiners (wkTree τ u) (wkEnv τ E) ≡ mapList wkJoiner (joiners u E)
      joiners-wk (pendingˢ s q)                          E = refl
      joiners-wk (coldˢ s hd ph)                         E = refl
      joiners-wk (ofˢ p i xs)                            E = refl
      joiners-wk doneˢ                                   E = refl
      joiners-wk (mapˢ f s)                              E = joiners-wk s E
      joiners-wk (scanˢ f r s)                           E = joiners-wk s E
      joiners-wk (takeWhileˢ i p c k tk s)               E = joiners-wk s E
      joiners-wk (flatMapˢ op f fl oc k r pl so ls)      E =
        trans (cong₂ _++_ (joiners-wk so E) (joiners-wkᴸ ls E)) (sym (mapL-++ wkJoiner (joiners so E) (laneJoiners ls E)))
      joiners-wk (connectˢ S c b kb k fd rp e rt src bd) E =
        trans (cong₂ _++_ (joiners-wk src E) (joiners-wk bd (S ∷ E))) (sym (mapL-++ wkJoiner (joiners src E) (joiners bd (S ∷ E))))
      joiners-wk (joinˢ j sk l x st)                     E = cong (λ S → joiner S (wk∋ τ sk) j ∷ []) (lookup-wkEnv τ E x)
      joiners-wk (deferˢ k s)                            E = joiners-wk s E

      joiners-wkᴸ : ∀ {Δ B} (ls : List (Lane h Δ B)) (E : Env Δ h) → laneJoiners (wkLanes τ ls) (wkEnv τ E) ≡ mapList wkJoiner (laneJoiners ls E)
      joiners-wkᴸ []                E = refl
      joiners-wkᴸ (lane c k s ∷ ls) E =
        trans (cong₂ _++_ (joiners-wk s E) (joiners-wkᴸ ls E)) (sym (mapL-++ wkJoiner (joiners s E) (laneJoiners ls E)))

    -- Every path of the grown tree, the weakening of one the old tree held.
    data Pulled {Δ₀ A₀} (t : Sub h Δ₀ A₀) : ∀ {Δ A} {x′ : Sub v Δ A} → Path (wkTree τ t) x′ → Set₁ where
      pulled : ∀ {Δ A} {x : Sub h Δ A} (π : Path t x) → Pulled t (wkPath τ π)

    data PulledL {Δ₀ B} (ls : List (Lane h Δ₀ B)) : ∀ {Δ A} {x′ : Sub v Δ A} → PathLanes (wkLanes τ ls) x′ → Set₁ where
      pulledL : ∀ {Δ A} {x : Sub h Δ A} (π : PathLanes ls x) → PulledL ls (wkPathᴸ τ π)

    mutual
      pull : ∀ {Δ₀ A₀ Δ A} (t : Sub h Δ₀ A₀) {x′ : Sub v Δ A} (ψ′ : Path (wkTree τ t) x′) → Pulled t ψ′
      pull (pendingˢ s q)                          here = pulled here
      pull (coldˢ s hd ph)                         here = pulled here
      pull (ofˢ p i xs)                            here = pulled here
      pull doneˢ                                   here = pulled here
      pull (mapˢ f s)                              here = pulled here
      pull (mapˢ f s)                              (in-map ψ′) with pull s ψ′
      ... | pulled π = pulled (in-map π)
      pull (scanˢ f r s)                           here = pulled here
      pull (scanˢ f r s)                           (in-scan ψ′) with pull s ψ′
      ... | pulled π = pulled (in-scan π)
      pull (takeWhileˢ i p c k tk s)               here = pulled here
      pull (takeWhileˢ i p c k tk s)               (in-take ψ′) with pull s ψ′
      ... | pulled π = pulled (in-take π)
      pull (flatMapˢ op f fl oc k r pl so ls)      here = pulled here
      pull (flatMapˢ op f fl oc k r pl so ls)      (in-outer ψ′) with pull so ψ′
      ... | pulled π = pulled (in-outer π)
      pull (flatMapˢ op f fl oc k r pl so ls)      (in-lanes ψ′) with pullL ls ψ′
      ... | pulledL π = pulled (in-lanes π)
      pull (connectˢ S c b kb k fd rp e rt src bd) here = pulled here
      pull (connectˢ S c b kb k fd rp e rt src bd) (in-source ψ′) with pull src ψ′
      ... | pulled π = pulled (in-source π)
      pull (connectˢ S c b kb k fd rp e rt src bd) (in-body ψ′) with pull bd ψ′
      ... | pulled π = pulled (in-body π)
      pull (joinˢ j sk l x st)                     here = pulled here
      pull (deferˢ k s)                            here = pulled here
      pull (deferˢ k s)                            (in-defer ψ′) with pull s ψ′
      ... | pulled π = pulled (in-defer π)

      pullL : ∀ {Δ₀ B Δ A} (ls : List (Lane h Δ₀ B)) {x′ : Sub v Δ A} (ψ′ : PathLanes (wkLanes τ ls) x′) → PulledL ls ψ′
      pullL (lane c k s ∷ ls) (this-lane ψ′) with pull s ψ′
      ... | pulled π = pulledL (this-lane π)
      pullL (lane c k s ∷ ls) (next-lane ψ′) with pullL ls ψ′
      ... | pulledL π = pulledL (next-lane π)

    -- The node a pulled path reaches, by the shape its weakening has.
    data OfAt {Δ A} : (x : Sub h Δ A) {x′ : Sub v Δ A} → wkTree τ x ≡ x′ → Set₁ where
      of-at : ∀ {p i xs} → OfAt (ofˢ p i xs) refl

    of-at? : ∀ {Δ A p i xs} (x : Sub h Δ A) (e : wkTree τ x ≡ ofˢ p i xs) → OfAt x e
    of-at? (ofˢ _ _ _)                       refl = of-at
    of-at? (pendingˢ _ _)                    ()
    of-at? (coldˢ _ _ _)                     ()
    of-at? doneˢ                             ()
    of-at? (mapˢ _ _)                        ()
    of-at? (scanˢ _ _ _)                     ()
    of-at? (takeWhileˢ _ _ _ _ _ _)          ()
    of-at? (flatMapˢ _ _ _ _ _ _ _ _ _)      ()
    of-at? (connectˢ _ _ _ _ _ _ _ _ _ _ _)  ()
    of-at? (joinˢ _ _ _ _ _)                 ()
    of-at? (deferˢ _ _)                      ()

    data ColdAt {Δ A} : (x : Sub h Δ A) {x′ : Sub v Δ A} → wkTree τ x ≡ x′ → Set₁ where
      cold-at : ∀ {s hd ph} → ColdAt (coldˢ s hd ph) refl

    cold-at? : ∀ {Δ A s hd ph} (x : Sub h Δ A) (e : wkTree τ x ≡ coldˢ s hd ph) → ColdAt x e
    cold-at? (coldˢ _ _ _)                     refl = cold-at
    cold-at? (pendingˢ _ _)                    ()
    cold-at? (ofˢ _ _ _)                       ()
    cold-at? doneˢ                             ()
    cold-at? (mapˢ _ _)                        ()
    cold-at? (scanˢ _ _ _)                     ()
    cold-at? (takeWhileˢ _ _ _ _ _ _)          ()
    cold-at? (flatMapˢ _ _ _ _ _ _ _ _ _)      ()
    cold-at? (connectˢ _ _ _ _ _ _ _ _ _ _ _)  ()
    cold-at? (joinˢ _ _ _ _ _)                 ()
    cold-at? (deferˢ _ _)                      ()

    data PendAt {Δ A} : (x : Sub h Δ A) {x′ : Sub v Δ A} → wkTree τ x ≡ x′ → Set₁ where
      pend-at : ∀ {s q} → PendAt (pendingˢ s q) refl

    pend-at? : ∀ {Δ A s q} (x : Sub h Δ A) (e : wkTree τ x ≡ pendingˢ s q) → PendAt x e
    pend-at? (pendingˢ _ _)                    refl = pend-at
    pend-at? (coldˢ _ _ _)                     ()
    pend-at? (ofˢ _ _ _)                       ()
    pend-at? doneˢ                             ()
    pend-at? (mapˢ _ _)                        ()
    pend-at? (scanˢ _ _ _)                     ()
    pend-at? (takeWhileˢ _ _ _ _ _ _)          ()
    pend-at? (flatMapˢ _ _ _ _ _ _ _ _ _)      ()
    pend-at? (connectˢ _ _ _ _ _ _ _ _ _ _ _)  ()
    pend-at? (joinˢ _ _ _ _ _)                 ()
    pend-at? (deferˢ _ _)                      ()

    data TakeAt {Δ A} : (x : Sub h Δ A) {x′ : Sub v Δ A} → wkTree τ x ≡ x′ → Set₁ where
      take-at : ∀ {i p c k tk s} → TakeAt (takeWhileˢ i p c k tk s) refl

    take-at? : ∀ {Δ A i p c k tk s} (x : Sub h Δ A) (e : wkTree τ x ≡ takeWhileˢ i p c k tk s) → TakeAt x e
    take-at? (takeWhileˢ _ _ _ _ _ _)          refl = take-at
    take-at? (pendingˢ _ _)                    ()
    take-at? (coldˢ _ _ _)                     ()
    take-at? (ofˢ _ _ _)                       ()
    take-at? doneˢ                             ()
    take-at? (mapˢ _ _)                        ()
    take-at? (scanˢ _ _ _)                     ()
    take-at? (flatMapˢ _ _ _ _ _ _ _ _ _)      ()
    take-at? (connectˢ _ _ _ _ _ _ _ _ _ _ _)  ()
    take-at? (joinˢ _ _ _ _ _)                 ()
    take-at? (deferˢ _ _)                      ()

    data FeedAt {Δ A} : (x : Sub h Δ A) {x′ : Sub v Δ A} → wkTree τ x ≡ x′ → Set₁ where
      feed-at : ∀ {B} {S c b kb k a q ss rp e rt s} {bd : Sub h (B ∷ Δ) A} → FeedAt (connectˢ S c b kb k (feeding a q ss) rp e rt s bd) refl

    feed-at? : ∀ {Δ A B S c b kb k a q ss rp e rt s} {bd : Sub v (B ∷ Δ) A} (x : Sub h Δ A)
               (e′ : wkTree τ x ≡ connectˢ S c b kb k (feeding a q ss) rp e rt s bd) → FeedAt x e′
    feed-at? (connectˢ _ _ _ _ _ (feeding _ _ _) _ _ _ _ _) refl = feed-at
    feed-at? (connectˢ _ _ _ _ _ idle _ _ _ _ _)            ()
    feed-at? (connectˢ _ _ _ _ _ (finishing _ _) _ _ _ _ _) ()
    feed-at? (pendingˢ _ _)                    ()
    feed-at? (coldˢ _ _ _)                     ()
    feed-at? (ofˢ _ _ _)                       ()
    feed-at? doneˢ                             ()
    feed-at? (mapˢ _ _)                        ()
    feed-at? (scanˢ _ _ _)                     ()
    feed-at? (takeWhileˢ _ _ _ _ _ _)          ()
    feed-at? (flatMapˢ _ _ _ _ _ _ _ _ _)      ()
    feed-at? (joinˢ _ _ _ _ _)                 ()
    feed-at? (deferˢ _ _)                      ()

    data FinAt {Δ A} : (x : Sub h Δ A) {x′ : Sub v Δ A} → wkTree τ x ≡ x′ → Set₁ where
      fin-at : ∀ {B} {S c b kb k q ss rp e rt s} {bd : Sub h (B ∷ Δ) A} → FinAt (connectˢ S c b kb k (finishing q ss) rp e rt s bd) refl

    fin-at? : ∀ {Δ A B S c b kb k q ss rp e rt s} {bd : Sub v (B ∷ Δ) A} (x : Sub h Δ A)
              (e′ : wkTree τ x ≡ connectˢ S c b kb k (finishing q ss) rp e rt s bd) → FinAt x e′
    fin-at? (connectˢ _ _ _ _ _ (finishing _ _) _ _ _ _ _) refl = fin-at
    fin-at? (connectˢ _ _ _ _ _ idle _ _ _ _ _)            ()
    fin-at? (connectˢ _ _ _ _ _ (feeding _ _ _) _ _ _ _ _) ()
    fin-at? (pendingˢ _ _)                    ()
    fin-at? (coldˢ _ _ _)                     ()
    fin-at? (ofˢ _ _ _)                       ()
    fin-at? doneˢ                             ()
    fin-at? (mapˢ _ _)                        ()
    fin-at? (scanˢ _ _ _)                     ()
    fin-at? (takeWhileˢ _ _ _ _ _ _)          ()
    fin-at? (flatMapˢ _ _ _ _ _ _ _ _ _)      ()
    fin-at? (joinˢ _ _ _ _ _)                 ()
    fin-at? (deferˢ _ _)                      ()

    -- What the stack owes, along the weakened tree.
    wkJob : ∀ {t : Sub h [] R} → Job t → Job (wkTree τ t)
    wkJob (p , c) = p , wkCall c

    wkSpot : ∀ {Δ A} {t : Sub h Δ A} → Spot t → Spot (wkTree τ t)
    wkSpot (spot π) = spot (wkPath τ π)

    at-grow : ∀ {t : Sub h [] R} p (ks : List (Call t)) → at⟦ p ⟧ (mapList wkCall ks) ≡ mapList wkJob (at⟦ p ⟧ ks)
    at-grow p []       = refl
    at-grow p (c ∷ ks) = cong ((p , wkCall c) ∷_) (at-grow p ks)

    jobs-grow : ∀ {t : Sub h [] R} {p w} {σ : w ⊑ h} {σ′ : w ⊑ v} {K bs} (e : σ ⨾ τ ≡ σ′) (sk : StackAs t p σ K bs)
              → stackJobs (wkTree τ t) (stack-grow e sk) ≡ mapList wkJob (stackJobs t sk)
    jobs-grow e bottomAs = refl
    jobs-grow {σ = σ} e (restAs {p = p} {ρ = ρ} ks r K) =
      trans (cong₂ _++_ (at-grow p ks) (jobs-grow (assoc-step ρ σ e) K)) (sym (mapL-++ wkJob (at⟦ p ⟧ ks) (stackJobs _ K)))
    jobs-grow {σ = σ} e (backAs q {ρ = ρ} ks lt r K) =
      trans (cong₂ _++_ (at-grow q ks) (jobs-grow (assoc-step ρ σ e) K)) (sym (mapL-++ wkJob (at⟦ q ⟧ ks) (stackJobs _ K)))
    jobs-grow {σ = σ} e (reholdAs {ρ = ρ} b hd K) = jobs-grow (assoc-step ρ σ e) K

    bursts-grow : ∀ {t : Sub h [] R} {p w} {σ : w ⊑ h} {σ′ : w ⊑ v} {K bs} (e : σ ⨾ τ ≡ σ′) (sk : StackAs t p σ K bs)
                → stackBursts (wkTree τ t) (stack-grow e sk) ≡ mapList wkSpot (stackBursts t sk)
    bursts-grow e bottomAs = refl
    bursts-grow {σ = σ} e (restAs {ρ = ρ} ks r K)      = bursts-grow (assoc-step ρ σ e) K
    bursts-grow {σ = σ} e (backAs q {ρ = ρ} ks lt r K) = bursts-grow (assoc-step ρ σ e) K
    bursts-grow {σ = σ} e (reholdAs {ρ = ρ} (playsAs π) hd K) = cong (spot (wkPath τ π) ∷_) (bursts-grow (assoc-step ρ σ e) K)
    bursts-grow {σ = σ} e (reholdAs {ρ = ρ} (firesAs π) hd K) = cong (spot (wkPath τ π) ∷_) (bursts-grow (assoc-step ρ σ e) K)
    bursts-grow {σ = σ} e (reholdAs {ρ = ρ} overAs hd K)      = bursts-grow (assoc-step ρ σ e) K

    sources-grow : ∀ {t : Sub h [] R} (js : List (Job t)) → sources (wkTree τ t) (mapList wkJob js) ≡ mapList wkSpot (sources t js)
    sources-grow []                    = refl
    sources-grow ((_ , srcC π) ∷ js)   = cong₂ _∷_ (cong spot (sym (wkPath-⊕ π (in-source here)))) (sources-grow js)
    sources-grow ((_ , emitC _) ∷ js)  = sources-grow js
    sources-grow ((_ , kontC _ _) ∷ js) = sources-grow js
    sources-grow ((_ , take1C _) ∷ js) = sources-grow js
    sources-grow ((_ , take2C _) ∷ js) = sources-grow js
    sources-grow ((_ , bodyC _) ∷ js)  = sources-grow js
    sources-grow ((_ , feedC _) ∷ js)  = sources-grow js
    sources-grow ((_ , finC _) ∷ js)   = sources-grow js

    placed-grow : ∀ {t : Sub h [] R} (j : Job t) → Placed t j → Placed (wkTree τ t) (wkJob j)
    placed-grow (_ , emitC _)   x = x
    placed-grow (_ , kontC _ _) x = x
    placed-grow (_ , take1C _)  x = x
    placed-grow (_ , take2C _)  x = x
    placed-grow (_ , bodyC _)   x = x
    placed-grow (_ , feedC _)   x = x
    placed-grow (_ , finC _)    x = x
    placed-grow (_ , srcC _)    x = x
