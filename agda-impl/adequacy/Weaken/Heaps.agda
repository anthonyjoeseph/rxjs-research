{-# OPTIONS --guardedness #-}

module adequacy.Weaken.Heaps where

open import Data.List using (List; []; _∷_; _++_; [_]; length) renaming (map to mapᴸ)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (tabulate to tabulateᴬ; lookup to lookupᴬ; map to all-map)
open import Data.List.Relation.Unary.Any using () renaming (here to hereᴬ; there to thereᴬ)
open import Data.List.Relation.Unary.Any.Properties using () renaming (++⁻ to any-++⁻; ++⁺ˡ to any-++⁺ˡ; ++⁺ʳ to any-++⁺ʳ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁻ to all-++⁻; ++⁺ to all-++⁺)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_) renaming (map to pairs-map)
open import Data.List.Relation.Unary.Linked using (Linked; []; [-]; _∷_)
open import Data.List.Relation.Unary.AllPairs.Properties using () renaming (map⁺ to pairs-map⁺; ++⁺ to pairs-++⁺)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_; ↭-sym; ↭-trans; ↭-reflexive) renaming (refl to ↭-refl′; prep to ↭-prep′; swap to ↭-swap′; trans to ↭-trans′)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (All-resp-↭; shifts) renaming (++⁺ˡ to ↭-++⁺ˡ; ++⁺ʳ to ↭-++⁺ʳ)
open import Data.List.Properties using (map-++; ++-assoc) renaming (++-identityʳ to ++-idʳ)
open import Data.Maybe using (Maybe; just; nothing; is-just; is-nothing) renaming (map to mapMaybe)
open import Data.Nat using (suc)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤₁; tt to tt₁)
open import Data.Bool using (_∧_; _∨_; true; false; if_then_else_)
open import Relation.Nullary using (¬_)
open import Level using (Lift; lift)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

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
open import adequacy.Weaken using (module Weakening)

module WeakeningHeaps (R : Set) where
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
  open StrongAgainst R using (Owned; Kernels; Meaning; Queue; Each; Leaves; Back; Leaving; Lingers; Restful; Tied; seen; seenL; isTaking; at⟦_⟧; Spot; spot; Job)
  open StrongHeld R using (DoneBy)
  open StrongAgainst.Against R using (StackAs; subAs; runAs; CtlAs; agenda; bursts; begins; stackJobs; SrcOf; Ticked; stackBursts; sources; Placed; restAs; backAs; reholdAs; bottomAs; BurstAs; playsAs; firesAs; overAs; Held; bottomᴴ; restᴴ; BurstClocked; src-of)
  open Strongly.Phase R using (waiting; playing; fired)
  open Moving R using (pend; pendᴸ)
  open Weakening R using (module Grown; Grows; pure-map)

  module GrownHeaps {h v} (τ : h ⊑ v) where
    open Grown τ

    module _ {H : Heapᴹ h} {H′ : Heapᴹ v} (gr : Grows τ H H′) where
      private
        open Grows gr using (cells)

        -- The heap-free combinators read alike from either heap.
        mapᴹ-≡ : ∀ {X Y : Set₁} (f : X → Y) m → At.mapᴹ H′ f m ≡ At.mapᴹ H f m
        mapᴹ-≡ f nothing  = refl
        mapᴹ-≡ f (just _) = refl

        consᴹ-≡ : ∀ {X : Set₁} (m : Maybe X) xs → At.consᴹ H′ m xs ≡ At.consᴹ H m xs
        consᴹ-≡ nothing  xs = refl
        consᴹ-≡ (just _) xs = refl

        merged-≡ : ∀ {Δ A B} op (g : A → Pos → U.Node Δ B) o L Q pl → At.merged H′ op g o L Q pl ≡ At.merged H op g o L Q pl
        merged-≡ op g nothing  []      []      pl = refl
        merged-≡ op g nothing  []      (_ ∷ _) pl = refl
        merged-≡ op g nothing  (_ ∷ _) Q       pl = refl
        merged-≡ op g (just _) L       Q       pl = refl

        connected-≡ : ∀ {Δ A B} r (e : Maybe Pos) (t : U.Node Δ A) s (mb : Maybe (U.Node (A ∷ Δ) B))
                    → At.connected H′ r e t s mb ≡ At.connected H r e t s mb
        connected-≡ r e        t s        nothing  = refl
        connected-≡ r e        t (just _) (just _) = refl
        connected-≡ r (just _) t nothing  (just _) = refl
        connected-≡ r nothing  t nothing  (just _) = refl

        joinedᶜ-≡ : ∀ {Δ A} (x : A ∈ Δ) j st → At.joinedᶜ H′ x j st ≡ At.joinedᶜ H x j st
        joinedᶜ-≡ x j nothing  = refl
        joinedᶜ-≡ x j (just _) = refl

        taking?-≡ : ∀ {Δ A} i p tk (s : Maybe (U.Node Δ A)) → At.taking? H′ i p tk s ≡ At.taking? H i p tk s
        taking?-≡ i p taking       s = mapᴹ-≡ (U.takeWhileᶜ i p) s
        taking?-≡ i p (ending k c) s = refl
        taking?-≡ i p taken        s = refl

        sourced-≡ : ∀ {Δ A} (s : Maybe (U.Node Δ A)) t → At.sourced H′ s t ≡ At.sourced H s t
        sourced-≡ (just _) t = refl
        sourced-≡ nothing  t = refl

      -- The open part, read through the weakening.
      mutual
        grow-part : ∀ {Δ A} (u : Sub h Δ A) → At.part H′ (wkTree τ u) ≡ At.part H u
        grow-part (pendingˢ s q)                 = refl
        grow-part (coldˢ s hd ph)                = cong (λ b → if b then nothing else _) (Grows.handles gr hd)
        grow-part (ofˢ p i xs)                   = refl
        grow-part doneˢ                          = refl
        grow-part (mapˢ f s)                     = trans (cong (At.mapᴹ H′ (U.mapᶜ f)) (grow-part s)) (mapᴹ-≡ (U.mapᶜ f) (At.part H s))
        grow-part (scanˢ f r s)                  =
          trans (cong₂ (λ a m → At.mapᴹ H′ (U.scanᶜ f a) m) (cells r) (grow-part s)) (mapᴹ-≡ (U.scanᶜ f (At.val H r)) (At.part H s))
        grow-part (takeWhileˢ i p c k tk s)      =
          trans (cong₂ (λ b m → if b then At.taking? H′ i p tk m else nothing) (cells (Kit.live c)) (grow-part s))
                (cong (λ m → if At.val H (Kit.live c) then m else nothing) (taking?-≡ i p tk (At.part H s)))
        grow-part (flatMapˢ op f fl oc k r pl so ls) =
          trans (cong₂ (λ o L → At.merged H′ op (λ a q → U.subscribe (f a) q) o L (At.val H′ (wkR τ (FlatKit.Flat.queue fl))) pl) (grow-part so) (grow-partᴸ ls))
                (trans (cong (λ Q → At.merged H′ op (λ a q → U.subscribe (f a) q) (At.part H so) (At.partLanes H ls) Q pl) (cells (FlatKit.Flat.queue fl)))
                       (merged-≡ op (λ a q → U.subscribe (f a) q) (At.part H so) (At.partLanes H ls) (At.val H (FlatKit.Flat.queue fl)) pl))
        grow-part (connectˢ S c b kb k fd rp e rt src bd) =
          trans (cong₂ (At.connected H′ rp e rt) (grow-part src) (grow-part bd)) (connected-≡ rp e rt (At.part H src) (At.part H bd))
        grow-part (joinˢ j sk l x st)            =
          trans (cong (λ b → if b then At.joinedᶜ H′ x j st else nothing) (cells l)) (cong (λ m → if At.val H l then m else nothing) (joinedᶜ-≡ x j st))
        grow-part (deferˢ k s)                   = grow-part s

        grow-partᴸ : ∀ {Δ B} (ls : List (Lane h Δ B)) → At.partLanes H′ (wkLanes τ ls) ≡ At.partLanes H ls
        grow-partᴸ []                = refl
        grow-partᴸ (lane c k s ∷ ls) =
          trans (cong₂ (λ b L → if b then At.consᴹ H′ (At.part H′ (wkTree τ s)) L else L) (cells (Kit.live c)) (grow-partᴸ ls))
                (cong (λ m → if At.val H (Kit.live c) then m else At.partLanes H ls)
                      (trans (cong (λ m → At.consᴹ H′ m (At.partLanes H ls)) (grow-part s)) (consᴹ-≡ (At.part H s) (At.partLanes H ls))))

      -- What the weakened tree leaves running, and what its pools run.
      mutual
        leftover-wk : ∀ {Δ A B} (u : Sub h Δ A) → At.leftover H′ {B = B} (wkTree τ u) ≡ At.leftover H {B = B} u
        leftover-wk (pendingˢ s q)                     = refl
        leftover-wk (coldˢ s hd ph)                    = refl
        leftover-wk (ofˢ p i xs)                       = refl
        leftover-wk doneˢ                              = refl
        leftover-wk (mapˢ f s)                         = leftover-wk s
        leftover-wk (scanˢ f r s)                      = leftover-wk s
        leftover-wk (takeWhileˢ i p c k tk s)          = leftover-wk s
        leftover-wk (flatMapˢ op f fl oc k r pl so ls) = cong₂ U.unionᶜ (leftover-wk so) (leftover-wkᴸ ls)
        leftover-wk (connectˢ S c b kb k fd rp e rt src bd) =
          cong₂ (λ n l → U.unionᶜ (U.burstingᶜ rp n) (U.underᶜ (U.live n) l))
                (trans (cong₂ (At.sourced H′) (grow-part src) (leftover-wk src)) (sourced-≡ (At.part H src) (At.leftover H src)))
                (leftover-wk {B = ⊤} bd)
        leftover-wk (joinˢ j sk l x st)                = refl
        leftover-wk (deferˢ k s)                       = leftover-wk s

        leftover-wkᴸ : ∀ {Δ A B} (ls : List (Lane h Δ A)) → At.leftoverL H′ {B = B} (wkLanes τ ls) ≡ At.leftoverL H {B = B} ls
        leftover-wkᴸ []                = refl
        leftover-wkᴸ (lane c k s ∷ ls) = cong₂ U.unionᶜ (leftover-wk s) (leftover-wkᴸ ls)

      mutual
        kept-wk : ∀ {Δ A B} (u : Sub h Δ A) → At.kept H′ {B = B} (wkTree τ u) ≡ At.kept H {B = B} u
        kept-wk (pendingˢ s q)                     = refl
        kept-wk (coldˢ s hd ph)                    = refl
        kept-wk (ofˢ p i xs)                       = refl
        kept-wk doneˢ                              = refl
        kept-wk (mapˢ f s)                         = kept-wk s
        kept-wk (scanˢ f r s)                      = kept-wk s
        kept-wk (takeWhileˢ i p c k tk s)          = kept-wk s
        kept-wk {B = B} (flatMapˢ op f fl oc k r pl so ls)
          rewrite cells (FlatKit.Flat.outerDone fl) | leftover-wk {B = B} so | grow-part so | kept-wk {B = B} so | kept-wkᴸ {B = B} ls = refl
        kept-wk (connectˢ S c b kb k fd rp e rt src bd) =
          cong₂ (λ n l → U.unionᶜ (U.burstingᶜ rp n) (U.underᶜ (U.live n) l))
                (trans (cong₂ (At.sourced H′) (grow-part src) (leftover-wk src)) (sourced-≡ (At.part H src) (At.leftover H src)))
                (kept-wk {B = ⊤} bd)
        kept-wk (joinˢ j sk l x st)                = refl
        kept-wk (deferˢ k s)                       = kept-wk s

        kept-wkᴸ : ∀ {Δ A B} (ls : List (Lane h Δ A)) → At.keptL H′ {B = B} (wkLanes τ ls) ≡ At.keptL H {B = B} ls
        kept-wkᴸ []                = refl
        kept-wkᴸ {B = B} (lane c k s ∷ ls)
          rewrite cells (Kit.live c) | grow-part s | kept-wk {B = B} s | leftover-wk {B = B} s | kept-wkᴸ {B = B} ls = refl

      pooled-wkᴸ : ∀ {Δ A B} (ls : List (Lane h Δ A)) → At.pooledL H′ {B = B} (wkLanes τ ls) ≡ At.pooledL H {B = B} ls
      pooled-wkᴸ []                = refl
      pooled-wkᴸ (lane c k s ∷ ls) =
        trans (cong₂ (λ b P → if b then P else U.unionᶜ (At.leftover H′ (wkTree τ s)) P) (cells (Kit.live c)) (pooled-wkᴸ ls))
              (cong (λ x → if At.val H (Kit.live c) then At.pooledL H ls else U.unionᶜ x (At.pooledL H ls)) (leftover-wk s))

      pooled-wk : ∀ {Δ A B} (fl : FlatKit.Flat A h) (so : Sub h Δ A) (ls : List (Lane h Δ B))
                → At.pooled H′ (FlatKit.wkFlat τ fl) (wkTree τ so) (wkLanes τ ls) ≡ At.pooled H fl so ls
      pooled-wk fl so ls =
        cong₂ U.unionᶜ (trans (cong (λ b → if b then At.leftover H′ (wkTree τ so) else U.idleᶜ) (cells (FlatKit.Flat.outerDone fl)))
                              (cong (λ x → if At.val H (FlatKit.Flat.outerDone fl) then x else U.idleᶜ) (leftover-wk so)))
                       (pooled-wkᴸ ls)

      -- A path through the weakened tree is the weakening of one through
      -- the old, seen alike.
      mutual
        unwk : ∀ {Δ A Δ′ A′} (t : Sub h Δ A) {x′ : Sub v Δ′ A′} (ψ′ : Path (wkTree τ t) x′)
             → Σ (Sub h Δ′ A′) λ x → Σ (Path t x) λ ψ → x′ ≡ wkTree τ x × seen H′ ψ′ ≡ seen H ψ
        unwk (pendingˢ s q)                     here = _ , here , refl , refl
        unwk (coldˢ s hd ph)                    here = _ , here , refl , refl
        unwk (ofˢ p i xs)                       here = _ , here , refl , refl
        unwk doneˢ                              here = _ , here , refl , refl
        unwk (joinˢ j sk l x st)                here = _ , here , refl , refl
        unwk (mapˢ f s)                         here = _ , here , refl , refl
        unwk (mapˢ f s)                         (in-map ψ′) = let x , ψ , e , sn = unwk s ψ′ in x , in-map ψ , e , sn
        unwk (scanˢ f r s)                      here = _ , here , refl , refl
        unwk (scanˢ f r s)                      (in-scan ψ′) = let x , ψ , e , sn = unwk s ψ′ in x , in-scan ψ , e , sn
        unwk (takeWhileˢ i p c k tk s)          here = _ , here , refl , refl
        unwk (takeWhileˢ i p c k tk s)          (in-take ψ′) =
          let x , ψ , e , sn = unwk s ψ′ in x , in-take ψ , e , cong₂ _∧_ (cells (Kit.live c)) (cong (isTaking tk ∧_) sn)
        unwk (flatMapˢ op f fl oc k r pl so ls) here = _ , here , refl , refl
        unwk (flatMapˢ op f fl oc k r pl so ls) (in-outer ψ′) = let x , ψ , e , sn = unwk so ψ′ in x , in-outer ψ , e , sn
        unwk (flatMapˢ op f fl oc k r pl so ls) (in-lanes ψ′) = let x , ψ , e , sn = unwkᴸ ls ψ′ in x , in-lanes ψ , e , sn
        unwk (connectˢ S c b kb k fd rp e rt src bd) here = _ , here , refl , refl
        unwk (connectˢ S c b kb k fd rp e rt src bd) (in-source ψ′) =
          let x , ψ , eq , sn = unwk src ψ′ in x , in-source ψ , eq , cong₂ _∧_ (cong is-just (grow-part bd)) sn
        unwk (connectˢ S c b kb k fd rp e rt src bd) (in-body ψ′) =
          let x , ψ , eq , sn = unwk bd ψ′ in x , in-body ψ , eq , cong₂ _∧_ (cong (λ z → is-just z ∨ is-just e) (grow-part src)) sn
        unwk (deferˢ k s)                       here = _ , here , refl , refl
        unwk (deferˢ k s)                       (in-defer ψ′) = let x , ψ , e , sn = unwk s ψ′ in x , in-defer ψ , e , sn

        unwkᴸ : ∀ {Δ B Δ′ A′} (ls : List (Lane h Δ B)) {x′ : Sub v Δ′ A′} (ψ′ : PathLanes (wkLanes τ ls) x′)
              → Σ (Sub h Δ′ A′) λ x → Σ (PathLanes ls x) λ ψ → x′ ≡ wkTree τ x × seenL H′ ψ′ ≡ seenL H ψ
        unwkᴸ (lane c k s ∷ ls) (this-lane ψ′) = let x , ψ , e , sn = unwk s ψ′ in x , this-lane ψ , e , cong₂ _∧_ (cells (Kit.live c)) sn
        unwkᴸ (lane c k s ∷ ls) (next-lane ψ′) = let x , ψ , e , sn = unwkᴸ ls ψ′ in x , next-lane ψ , e , sn

      grow-each : ∀ {t : Sub h [] R} {P : ∀ {Γ A} → U.Node Γ A → Set} → Each H P t → Each H′ P (wkTree τ t)
      Each.parts (grow-each {t = t} E) ψ′ sn {c} eq =
        let x , ψ , e , s = unwk t ψ′ in
        Each.parts E ψ (trans (sym s) sn) (trans (sym (grow-part x)) (subst (λ z → At.part H′ z ≡ just c) e eq))
      Each.pools (grow-each {t = t} E) {op = op} {f = f} {pl = pl} ψ′ sn eq with unwk t ψ′
      ... | x , ψ , e , s with flat-inv x e
      ... | flat-back {fl = fl} {oc = oc} {k = k} {r = r} {so = so} {ls = ls} =
        Each.pools E ψ (trans (sym s) sn) (trans (sym (grow-part (flatMapˢ op f fl oc k r pl so ls))) eq)
      Each.rests (grow-each {t = t} E) {rp = rp} {e = e₀} {rt = rt} ψ′ sn eq pn ec with unwk t ψ′
      ... | x , ψ , e , s with conn-inv x e
      ... | conn-back {S = S} {c = c} {b = b} {kb = kb} {k = k} {fd = fd} {src = src} {bd = bd} =
        Each.rests E ψ (trans (sym s) sn) (trans (sym (grow-part (connectˢ S c b kb k fd rp e₀ rt src bd))) eq) (trans (sym (grow-part src)) pn) ec

      -- What the ghost holds leaves, grown as the witness grows: the
      -- leftover read off a grown tree is the old one's.
      grow-leaving : ∀ {t : Sub h [] R} → Leaving H t → Leaving H′ (wkTree τ t)
      Leaving.parts (grow-leaving {t = t} L) ψ′ sn {c} eq =
        let x , ψ , e , s = unwk t ψ′ in
        subst (λ z → Leaves c (At.kept H′ {B = ⊤} z)) (sym e)
          (subst (Leaves c) (sym (kept-wk {B = ⊤} x))
            (Leaving.parts L ψ (trans (sym s) sn) (trans (sym (grow-part x)) (subst (λ z → At.part H′ z ≡ just c) e eq))))
      Leaving.pools (grow-leaving {t = t} L) {op = op} {f = f} {pl = pl} ψ′ sn eq with unwk t ψ′
      ... | x , ψ , e , s with flat-inv x e
      ... | flat-back {fl = fl} {oc = oc} {k = k} {r = r} {so = so} {ls = ls} =
        subst (Leaves pl) (sym (pooled-wk fl so ls)) (Leaving.pools L ψ (trans (sym s) sn) (trans (sym (grow-part (flatMapˢ op f fl oc k r pl so ls))) eq))
      Leaving.rests (grow-leaving {t = t} L) {rp = rp} {e = e₀} {rt = rt} ψ′ sn eq pn ec with unwk t ψ′
      ... | x , ψ , e , s with conn-inv x e
      ... | conn-back {S = S} {c = c} {b = b} {kb = kb} {k = k} {fd = fd} {src = src} {bd = bd} =
        let lv , bk , rf = Leaving.rests L ψ (trans (sym s) sn) (trans (sym (grow-part (connectˢ S c b kb k fd rp e₀ rt src bd))) eq) (trans (sym (grow-part src)) pn) ec
        in subst (Leaves rt) (sym (leftover-wk {B = ⊤} src)) lv , subst (Back rt) (sym (leftover-wk {B = ⊤} src)) bk , rf

      grow-lingers : ∀ {t : Sub h [] R} → Lingers H t → Lingers H′ (wkTree τ t)
      Lingers.pools (grow-lingers {t = t} L) {op = op} {f = f} {pl = pl} ψ′ sn eq with unwk t ψ′
      ... | x , ψ , e , s with flat-inv x e
      ... | flat-back {fl = fl} {oc = oc} {k = k} {r = r} {so = so} {ls = ls} =
        subst (λ x → Tied pl x × Restful pl) (sym (pooled-wk fl so ls)) (Lingers.pools L ψ (trans (sym s) sn) (trans (sym (grow-part (flatMapˢ op f fl oc k r pl so ls))) eq))
      Lingers.rests (grow-lingers {t = t} L) {rp = rp} {e = e₀} {rt = rt} ψ′ sn eq pn ec with unwk t ψ′
      ... | x , ψ , e , s with conn-inv x e
      ... | conn-back {S = S} {c = c} {b = b} {kb = kb} {k = k} {fd = fd} {src = src} {bd = bd} =
        subst (Tied rt) (sym (leftover-wk {B = ⊤} src))
              (Lingers.rests L ψ (trans (sym s) sn) (trans (sym (grow-part (connectˢ S c b kb k fd rp e₀ rt src bd))) eq) (trans (sym (grow-part src)) pn) ec)

      grow-flags : ∀ {Δ A} {t : Sub h Δ A} → DoneBy H t [] → DoneBy H′ (wkTree τ t) []
      grow-flags {t = t} d ψ′ sn with unwk t ψ′
      ... | x , ψ , e , s with flat-inv x e
      ... | flat-back {fl = fl} {so = so} =
        (λ ()) , λ _ → trans (cells (FlatKit.Flat.outerDone fl)) (trans (proj₂ (d ψ (trans (sym s) sn)) (λ ())) (cong is-nothing (sym (grow-part so))))

      -- A switch listed is listed weakened.
      listed-wk : ∀ {c} (xs : List (Kit.Cut h)) → c ∈ xs → Kit.wkCut τ c ∈ wkEl (list Kit.cutTy) τ xs
      listed-wk (x ∷ xs) (hereᴬ refl) = hereᴬ refl
      listed-wk (x ∷ xs) (thereᴬ m)   = thereᴬ (listed-wk xs m)

      -- Every registered callback reads, along the growth, as the
      -- weakened kernel registered it.
      cb-trans : ∀ {A} {c₁ c₂ c₃ : Callbacks A v} → CbRel c₁ c₂ → CbRel c₂ c₃ → CbRel c₁ c₃
      cb-trans (n , c , x) (n′ , c′ , x′) = (λ a → ≗-trans (n a) (n′ a)) , ≗-trans c c′ , ≗-trans x x′

      slot-grow : ∀ {X} (s : Sink h X) {c : Callbacks X h} {c′ : Callbacks X v} → At.slotIs H s c → CbRel (wkVal (slot X) τ c) c′
                → At.slotIs H′ (wk∋ τ s) c′
      slot-grow s (n , c , x) r = cb-trans (Grows.slots gr s) (cb-trans ((λ a → wk≗ τ (n a)) , wk≗ τ c , wk≗ τ x) r)

      quiet-wk : (m : Maybe (Quiet h)) → wkEl (maybe quiet) τ m ≡ mapMaybe (wk∋ τ) m
      quiet-wk nothing  = refl
      quiet-wk (just q) = refl

      stash-grow : (q : Quiet h) {u : Act h ⊤} {u′ : Act v ⊤} → At.stashIs H q u → wkAct τ u ≗ u′ → At.stashIs H′ (wk∋ τ q) u′
      stash-grow q st r = ≗-trans (Grows.stashes gr q) (≗-trans (wk≗ τ st) r)

      attached-grow : ∀ (c : Kit.Cut h) k {Δ A} (s : Sub h Δ A) → At.Attached H c k (unsub s)
                    → At.Attached H′ (Kit.wkCut τ c) (mapMaybe (wk∋ τ) k) (unsub (wkTree τ s))
      attached-grow c nothing  s (lift e) = lift (trans (cells (Kit.held c)) (cong (wkEl (maybe quiet) τ) e))
      attached-grow c (just q) s (e , st) = trans (cells (Kit.held c)) (cong (wkEl (maybe quiet) τ) e) , stash-grow q st (unsub-wk s)

      stashed-grow : ∀ k {Δ A} (s : Sub h Δ A) → At.Stashed H k (unsub s) → At.Stashed H′ (mapMaybe (wk∋ τ) k) (unsub (wkTree τ s))
      stashed-grow nothing  s _  = lift tt
      stashed-grow (just q) s st = stash-grow q st (unsub-wk s)

      count-grow : ∀ {Δ B} (ls : List (Lane h Δ B)) → At.count H′ (wkLanes τ ls) ≡ At.count H ls
      count-grow []                = refl
      count-grow (lane c k s ∷ ls) = cong₂ (λ b n → if b then suc n else n) (cells (Kit.live c)) (count-grow ls)

      switches-grow : ∀ {Δ B} (ls : List (Lane h Δ B)) → At.switches H′ (wkLanes τ ls) ≡ wkEl (list Kit.cutTy) τ (At.switches H ls)
      switches-grow []                = refl
      switches-grow (lane c k s ∷ ls) = cong (Kit.wkCut τ c ∷_) (switches-grow ls)

      wkEl-++ : ∀ {t} (xs ys : List (El h t)) → wkEl (list t) τ (xs ++ ys) ≡ wkEl (list t) τ xs ++ wkEl (list t) τ ys
      wkEl-++ []       ys = refl
      wkEl-++ {t} (x ∷ xs) ys = cong (wkEl t τ x ∷_) (wkEl-++ {t} xs ys)

      dead-grow : ∀ (cs : List (Kit.Cut h)) → All (λ c → At.val H (Kit.live c) ≡ false) cs
                → All (λ c → At.val H′ (Kit.live c) ≡ false) (wkEl (list Kit.cutTy) τ cs)
      dead-grow []       []       = []
      dead-grow (c ∷ cs) (d ∷ ds) = trans (cells (Kit.live c)) d ∷ dead-grow cs ds

      -- A feed weakened owes whom it owed, and what.
      private
        ∋-inj : ∀ {u w k} (ρ : u ⊑ w) {i j : u ∋ k} → wk∋ ρ i ≡ wk∋ ρ j → i ≡ j
        ∋-inj same⊑    e = e
        ∋-inj (grow ρ) e = ∋-inj ρ (there-inj′ e)
          where
            there-inj′ : ∀ {j w k} {a b : w ∋ k} → _≡_ {A = (j ∷ w) ∋ k} (there a) (there b) → a ≡ b
            there-inj′ refl = refl

        pair-back : ∀ {A} {sk s : Sink h A} {j i : Pos} → _≡_ {A = Sink v A × Pos} (wk∋ τ sk , j) (wk∋ τ s , i) → (sk , j) ≡ (s , i)
        pair-back e with ∋-inj τ (cong proj₁ e) | cong proj₂ e
        ... | refl | refl = refl

      owed-back : ∀ {A} (fd : Feed A h) {sk : Sink h A} {j} → At.Owed H′ (wkFeed τ fd) (wk∋ τ sk) j → At.Owed H fd sk j
      owed-back idle                           ()
      owed-back (feeding a q [])               ()
      owed-back (feeding a q ((s , i) ∷ ss))   (hereᴬ e)  = hereᴬ (pair-back e)
      owed-back (feeding a q (_ ∷ ss))         (thereᴬ m) = thereᴬ (owed-back (feeding a q ss) m)
      owed-back (finishing q [])               ()
      owed-back (finishing q ((s , i) ∷ ss))   (hereᴬ e)  = hereᴬ (pair-back e)
      owed-back (finishing q (_ ∷ ss))         (thereᴬ m) = thereᴬ (owed-back (finishing q ss) m)

      owed-fwd : ∀ {A} (fd : Feed A h) {sk : Sink h A} {j} → At.Owed H fd sk j → At.Owed H′ (wkFeed τ fd) (wk∋ τ sk) j
      owed-fwd idle                   ()
      owed-fwd (feeding a q [])       ()
      owed-fwd (feeding a q (_ ∷ ss)) (hereᴬ refl) = hereᴬ refl
      owed-fwd (feeding a q (_ ∷ ss)) (thereᴬ m)   = thereᴬ (owed-fwd (feeding a q ss) m)
      owed-fwd (finishing q [])       ()
      owed-fwd (finishing q (_ ∷ ss)) (hereᴬ refl) = hereᴬ refl
      owed-fwd (finishing q (_ ∷ ss)) (thereᴬ m)   = thereᴬ (owed-fwd (finishing q ss) m)

      owing-wk : ∀ {A} (fd : Feed A h) j → At.owing H′ (wkFeed τ fd) j ≡ At.owing H fd j
      owing-wk idle             j = refl
      owing-wk (feeding a q ss) j = refl
      owing-wk (finishing q ss) j = refl

      owingNone-≡ : ∀ {A : Set} (e : Maybe Pos) → At.owingNone H′ {A} e ≡ At.owingNone H e
      owingNone-≡ nothing  = refl
      owingNone-≡ (just _) = refl

      wkNow : ∀ {Δ} → At.Now H Δ → At.Now H′ Δ
      wkNow []             = []
      wkNow ((fd , e) ∷ ν) = (wkFeed τ fd , e) ∷ wkNow ν

      lookup-wk : ∀ {Δ A} (ν : At.Now H Δ) (x : A ∈ Δ) → lookupᴬ (wkNow ν) x ≡ (wkFeed τ (proj₁ (lookupᴬ ν x)) , proj₂ (lookupᴬ ν x))
      lookup-wk (_ ∷ ν) (hereᴬ refl) = refl
      lookup-wk (_ ∷ ν) (thereᴬ x)   = lookup-wk ν x

      -- Every live joiner held what its feed owed it, read through the
      -- weakening.
      mutual
        fed-wk : ∀ {Δ A} (u : Sub h Δ A) (ν : At.Now H Δ) → At.Fed H u ν → At.Fed H′ (wkTree τ u) (wkNow ν)
        fed-wk (pendingˢ s q)                          ν _       = lift tt
        fed-wk (coldˢ s hd ph)                         ν _       = lift tt
        fed-wk (ofˢ p i xs)                            ν _       = lift tt
        fed-wk doneˢ                                   ν _       = lift tt
        fed-wk (mapˢ f s)                              ν x       = fed-wk s ν x
        fed-wk (scanˢ f r s)                           ν x       = fed-wk s ν x
        fed-wk (takeWhileˢ i p c k tk s)               ν x       = fed-wk s ν x
        fed-wk (flatMapˢ op f fl oc k r pl so ls)      ν (x , y) = fed-wk so ν x , fed-wkᴸ ls ν y
        fed-wk (connectˢ S c b kb k fd rp e rt src bd) ν (x , y) =
          fed-wk src ν x , subst (λ z → At.Fed H′ (wkTree τ bd) ((wkFeed τ fd , (if z then e else nothing)) ∷ wkNow ν)) (sym (cells (Subject.closed S))) (fed-wk bd ((fd , At.told H S e) ∷ ν) y)
        fed-wk (joinˢ j sk l x st)                     ν (lift f) =
          subst (λ p → Lift _ (At.val H′ (wkR τ l) ≡ true → (At.Owed H′ (proj₁ p) (wk∋ τ sk) j → st ≡ At.owing H′ (proj₁ p) j)
                                                         × (¬ At.Owed H′ (proj₁ p) (wk∋ τ sk) j → st ≡ At.owingNone H′ (proj₂ p))))
                (sym (lookup-wk ν x))
                (lift λ on → let (o , n) = f (trans (sym (cells l)) on) in
                  (λ m → trans (o (owed-back (proj₁ (lookupᴬ ν x)) m)) (sym (owing-wk (proj₁ (lookupᴬ ν x)) j)))
                  , (λ ¬m → trans (n (λ m → ¬m (owed-fwd (proj₁ (lookupᴬ ν x)) m))) (sym (owingNone-≡ (proj₂ (lookupᴬ ν x))))))
        fed-wk (deferˢ k s)                            ν x       = fed-wk s ν x

        fed-wkᴸ : ∀ {Δ B} (ls : List (Lane h Δ B)) (ν : At.Now H Δ) → At.FedLanes H ls ν → At.FedLanes H′ (wkLanes τ ls) (wkNow ν)
        fed-wkᴸ []                ν _       = lift tt
        fed-wkᴸ (lane c k s ∷ ls) ν (x , y) = fed-wk s ν x , fed-wkᴸ ls ν y

      grow-meaning : ∀ {t : Sub h [] R} → Meaning H t → Meaning H′ (wkTree τ t)
      grow-meaning {t} mn = record { fed = fed-wk t [] (Meaning.fed mn) }

      -- Every live timer a pending frame's, read through the weakening.
      grow-timed : ∀ {ts : List (Timer h)} (t : Sub h [] R) → At.Timed H ts (pendings t) → At.Timed H′ (mapList (wkTimer τ) ts) (pendings (wkTree τ t))
      grow-timed {ts} t (a , b) =
        all-mapL (wkTimer τ) one a , subst (All (λ tm → At.spentʰ H′ (Timer.handle tm) ≡ false → tm ∈ mapList (wkTimer τ) ts)) (sym (pendings-wk t)) (all-mapL (wkTimer τ) two b)
        where
          one : ∀ {tm} → At.spentʰ H (Timer.handle tm) ≡ true ⊎ tm ∈ pendings t
              → At.spentʰ H′ (Timer.handle (wkTimer τ tm)) ≡ true ⊎ wkTimer τ tm ∈ pendings (wkTree τ t)
          one {tm} (inj₁ e) = inj₁ (trans (Grows.handles gr (Timer.handle tm)) e)
          one      (inj₂ m) = inj₂ (subst (_ ∈_) (sym (pendings-wk t)) (∈-mapL (wkTimer τ) m))

          two : ∀ {tm} → (At.spentʰ H (Timer.handle tm) ≡ false → tm ∈ ts)
              → At.spentʰ H′ (Timer.handle (wkTimer τ tm)) ≡ false → wkTimer τ tm ∈ mapList (wkTimer τ) ts
          two {tm} g e = ∈-mapL (wkTimer τ) (g (trans (sym (Grows.handles gr (Timer.handle tm))) e))

      -- Every subject's subscribers its joiners, or silenced, read
      -- through the weakening.
      private
        all-joins : ∀ {A p q} {P : Sink h A × Pos → Set p} {Q : Sink v A × Pos → Set q} → (∀ {s j} → P (s , j) → Q (wk∋ τ s , j))
                  → ∀ xs → All P xs → All Q (wkEl (joins A) τ xs)
        all-joins g []             []       = []
        all-joins g ((s , j) ∷ xs) (p ∷ ps) = g p ∷ all-joins g xs ps

        linked-joins : ∀ {A} (xs : List (Sink h A × Pos)) → Linked (λ x y → proj₂ x <ᵖ proj₂ y ≡ true) xs
                     → Linked (λ x y → proj₂ x <ᵖ proj₂ y ≡ true) (wkEl (joins A) τ xs)
        linked-joins []                          []      = []
        linked-joins ((s , j) ∷ [])              [-]     = [-]
        linked-joins ((s , j) ∷ (s′ , j′) ∷ xs) (r ∷ l) = r ∷ linked-joins ((s′ , j′) ∷ xs) l

        ∈-joins : ∀ {A} {s : Sink h A} {j} xs → (s , j) ∈ xs → (wk∋ τ s , j) ∈ wkEl (joins A) τ xs
        ∈-joins (_ ∷ xs) (hereᴬ refl) = hereᴬ refl
        ∈-joins (_ ∷ xs) (thereᴬ m)   = thereᴬ (∈-joins xs m)

        silent-grow : ∀ {A} {sk : Sink h A} {j} → At.Silenced H (sk , j) → At.Silenced H′ (wk∋ τ sk , j)
        silent-grow {sk = sk} (l , o , e , sl) = wkR τ l , wkObs τ o , trans (cells l) e , slot-grow sk sl (joiner-wk τ l (obs-refl (wkObs τ o)))

      grow-joined : ∀ (t : Sub h [] R) → At.Joined H (subjects t) (joiners t []) → At.Joined H′ (subjects (wkTree τ t)) (joiners (wkTree τ t) [])
      grow-joined t (a , b) =
        subst₂ (At.Joined H′) (sym (subjects-wk t)) (sym (joiners-wk t []))
          ( all-mapL wkSubj (λ { {_ , S} (al , ln) →
                subst (All _) (sym (cells (Subject.subscribers S)))
                  (all-joins (λ { {s} {j} (inj₁ m) → inj₁ (∈-mapL wkJoiner m) ; {s} {j} (inj₂ sl) → inj₂ (silent-grow {sk = s} {j = j} sl) })
                             (At.val H (Subject.subscribers S)) al)
              , subst (Linked _) (sym (cells (Subject.subscribers S))) (linked-joins (At.val H (Subject.subscribers S)) ln) }) a
          , all-mapL wkJoiner (λ { {joiner S _ _} m → subst (_ ∈_) (sym (cells (Subject.subscribers S))) (∈-joins _ m) }) b )

      grow-queue : ∀ {t : Sub h [] R} {p clk ts} → Queue H p clk ts t → Queue H′ p clk (mapList (wkTimer τ) ts) (wkTree τ t)
      grow-queue {t} qu = record { timed = grow-timed t (Queue.timed qu) ; joined = grow-joined t (Queue.joined qu)
                                 ; ordered = linked-mapL (Queue.ordered qu) ; ahead = all-mapL (wkTimer τ) (λ x → x) (Queue.ahead qu) }

      -- Everything owed before the growth is owed after it, aimed along
      -- the weakened tree.
      grow-owned-at : ∀ {t : Sub h [] R} {p p′ c c′ bs bs′} (ca : CtlAs t p c bs) (ca′ : CtlAs (wkTree τ t) p′ c′ bs′)
                    → agenda (wkTree τ t) ca′ ≡ mapList wkJob (agenda t ca) → bursts (wkTree τ t) ca′ ≡ mapList wkSpot (bursts t ca)
                    → (∀ {x} → x ∈ begins t ca → wkSpot x ∈ begins (wkTree τ t) ca′)
                    → Owned H t ca → Owned H′ (wkTree τ t) ca′
      grow-owned-at {t} ca ca′ je be bg∈ ow = record
        { ofs    = λ ψ′ → ofs-g ψ′ (pull t ψ′) refl
        ; plays  = λ ψ′ → plays-g ψ′ (pull t ψ′) refl
        ; fires  = λ ψ′ → fires-g ψ′ (pull t ψ′) refl
        ; begun  = λ ψ′ → begun-g ψ′ (pull t ψ′) refl
        ; ends   = λ ψ′ → ends-g ψ′ (pull t ψ′) refl
        ; cuts   = λ ψ′ → cuts-g ψ′ (pull t ψ′) refl
        ; feeds  = λ ψ′ → feeds-g ψ′ (pull t ψ′) refl
        ; fins   = λ ψ′ → fins-g ψ′ (pull t ψ′) refl
        ; bodies = bodies-g
        ; placed = subst (All (Placed (wkTree τ t))) (sym je) (all-mapL wkJob (λ {j} → placed-grow j) (Owned.placed ow)) }
        where
          T = wkTree τ t

          job∈ : ∀ {j} → j ∈ agenda t ca → wkJob j ∈ agenda T ca′
          job∈ {j} m = subst (wkJob j ∈_) (sym je) (∈-mapL wkJob m)

          burst∈ : ∀ {x} → x ∈ bursts t ca → wkSpot x ∈ bursts T ca′
          burst∈ {x} m = subst (wkSpot x ∈_) (sym be) (∈-mapL wkSpot m)

          ofs-g : ∀ {Δ A p i xs} {x′ : Sub v Δ A} (ψ′ : Path T x′) → Pulled t ψ′ → (e : x′ ≡ ofˢ p i xs)
                → (p , emitC (subst (Path T) e ψ′)) ∈ agenda T ca′
          ofs-g _ (pulled {x = x} π) e with of-at? x e
          ... | of-at = job∈ (Owned.ofs ow π)

          plays-g : ∀ {Δ A s hd τ′ r i u} {b : Frame A u} {x′ : Sub v Δ A} (ψ′ : Path T x′) → Pulled t ψ′
                  → (e : x′ ≡ coldˢ s hd (playing τ′ r i b)) → At.spentʰ H′ hd ≡ false → spot (subst (Path T) e ψ′) ∈ bursts T ca′
          plays-g _ (pulled {x = x} π) e sp with cold-at? x e
          ... | cold-at {hd = hd₀} = burst∈ (Owned.plays ow π (trans (sym (Grows.handles gr hd₀)) sp))

          fires-g : ∀ {Δ A s hd τ′ e′ u} {m : From A u} {x′ : Sub v Δ A} (ψ′ : Path T x′) → Pulled t ψ′
                  → (e : x′ ≡ coldˢ s hd (fired τ′ e′ m)) → At.spentʰ H′ hd ≡ false → spot (subst (Path T) e ψ′) ∈ bursts T ca′
          fires-g _ (pulled {x = x} π) e sp with cold-at? x e
          ... | cold-at {hd = hd₀} = burst∈ (Owned.fires ow π (trans (sym (Grows.handles gr hd₀)) sp))

          begun-g : ∀ {Δ A s q} {x′ : Sub v Δ A} (ψ′ : Path T x′) → Pulled t ψ′ → (e : x′ ≡ pendingˢ s q)
                  → spot (subst (Path T) e ψ′) ∈ begins T ca′
          begun-g _ (pulled {x = x} π) e with pend-at? x e
          ... | pend-at = bg∈ (Owned.begun ow π)

          ends-g : ∀ {Δ A i p c k q n} {s : Sub v Δ A} {x′ : Sub v Δ A} (ψ′ : Path T x′) → Pulled t ψ′
                 → (e : x′ ≡ takeWhileˢ i p c k (ending q n) s) → At.val H′ (Kit.live c) ≡ true
                 → (q , take1C (subst (Path T) e ψ′)) ∈ agenda T ca′
          ends-g _ (pulled {x = x} π) e lv with take-at? x e
          ... | take-at {c = c₀} = job∈ (Owned.ends ow π (trans (sym (cells (Kit.live c₀))) lv))

          cuts-g : ∀ {Δ A i p c k} {s : Sub v Δ A} {x′ : Sub v Δ A} (ψ′ : Path T x′) → Pulled t ψ′
                 → (e : x′ ≡ takeWhileˢ i p c k taken s) → At.val H′ (Kit.live c) ≡ true
                 → Σ Pos λ q → (q , take2C (subst (Path T) e ψ′)) ∈ agenda T ca′
          cuts-g _ (pulled {x = x} π) e lv with take-at? x e
          ... | take-at {c = c₀} with Owned.cuts ow π (trans (sym (cells (Kit.live c₀))) lv)
          ...   | q , m = q , job∈ m

          feeds-g : ∀ {Δ A B S c b kb k a q ss e₁ rp rt} {s : Sub v Δ A} {bd : Sub v (A ∷ Δ) B} {x′ : Sub v Δ B} (ψ′ : Path T x′) → Pulled t ψ′
                  → (e : x′ ≡ connectˢ S c b kb k (feeding a q ss) rp e₁ rt s bd) → (q , feedC (subst (Path T) e ψ′)) ∈ agenda T ca′
          feeds-g _ (pulled {x = x} π) e with feed-at? x e
          ... | feed-at = job∈ (Owned.feeds ow π)

          fins-g : ∀ {Δ A B S c b kb k q ss e₁ rp rt} {s : Sub v Δ A} {bd : Sub v (A ∷ Δ) B} {x′ : Sub v Δ B} (ψ′ : Path T x′) → Pulled t ψ′
                 → (e : x′ ≡ connectˢ S c b kb k (finishing q ss) rp e₁ rt s bd) → (q , finC (subst (Path T) e ψ′)) ∈ agenda T ca′
          fins-g _ (pulled {x = x} π) e with fin-at? x e
          ... | fin-at = job∈ (Owned.fins ow π)

          bodies-g : ∀ {Δ A B S c b kb k fd e₁ rp rt q} {s : Sub v Δ A} {bd : Sub v (A ∷ Δ) B}
                   → (ψ′ : Path T (connectˢ S c b kb k fd rp e₁ rt s bd)) → (q , bodyC ψ′) ∈ agenda T ca′ → At.part H′ bd ≡ nothing
          bodies-g ψ′ m with ∈-map⁻ wkJob (subst ((_ , bodyC ψ′) ∈_) (trans je (pure-map wkJob _)) m)
          ... | (_ , bodyC {bd = bd₀} π) , m₀ , refl = trans (grow-part bd₀) (Owned.bodies ow π m₀)
          ... | (_ , emitC _)   , _  , ()
          ... | (_ , kontC _ _) , _  , ()
          ... | (_ , take1C _)  , _  , ()
          ... | (_ , take2C _)  , _  , ()
          ... | (_ , feedC _)   , _  , ()
          ... | (_ , finC _)    , _  , ()
          ... | (_ , srcC _)    , _  , ()

      grow-owned   : ∀ {t : Sub h [] R} {w} {σ : w ⊑ h} {K bs} {Δ A s q} {π : Path t (pendingˢ {Δ = Δ} {A} s q)} {act act′ cd cd′}
                       (sk : StackAs t q σ K bs) {a a′}
                   → Owned H t (subAs {act = act} π cd sk a) → Owned H′ (wkTree τ t) (subAs {act = act′} (wkPath τ π) cd′ (grow-stack sk) a′)
      grow-owned {t} {π = π₀} sk {a} {a′} = grow-owned-at (subAs π₀ _ sk a) (subAs (wkPath τ π₀) _ (grow-stack sk) a′) (jobs-grow refl sk) (bursts-grow refl sk)
        λ {x} m → subst (λ L → wkSpot x ∈ spot (wkPath τ π₀) ∷ L)
                        (sym (trans (cong (sources (wkTree τ t)) (jobs-grow refl sk)) (sources-grow (stackJobs t sk)))) (∈-mapL wkSpot m)

      grow-run : ∀ {t : Sub h [] R} {w} {σ : w ⊑ h} {K bs p} (sk : StackAs t p σ K bs)
               → Owned H t (runAs [] (≗-refl _) sk) → Owned H′ (wkTree τ t) (runAs [] (≗-refl _) (grow-stack sk))
      grow-run {t} sk = grow-owned-at _ _ (jobs-grow refl sk) (bursts-grow refl sk)
        λ {x} m → subst (wkSpot x ∈_) (sym (trans (cong (sources (wkTree τ t)) (jobs-grow refl sk)) (sources-grow (stackJobs t sk)))) (∈-mapL wkSpot m)
