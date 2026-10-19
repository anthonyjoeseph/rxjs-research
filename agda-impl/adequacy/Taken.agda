{-# OPTIONS --guardedness #-}

-- A TAKEWHILE RESTAGED in the world grown by its cut.
module adequacy.Taken where

open import Data.List using (List; []; _∷_; _++_; [_]; length) renaming (map to mapᴸ)
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
open import Data.Empty using (⊥-elim)
open import Data.Maybe using (Maybe; just; nothing; is-just) renaming (map to mapMaybe)
open import Data.Nat using (_<_; _≤_)
open import Data.Nat.Properties using (≤-refl; m≤n⇒m≤1+n; <-irrefl)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Sum using (inj₁)
open import Data.Unit using (⊤)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤₁; tt to tt₁)
open import Data.Bool using (Bool; true; if_then_else_)
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
open import adequacy.Ghost using (module Ghosting)
open import adequacy.Unsub using (module Unsubbing)
open import adequacy.Grow using (module Growing)
open import adequacy.Seq using (module Sequencing)
open import operation.AbstractObservable using (base; maybe; quiet)
open import operation.PureObservable using (module Pure)
open import adequacy.Fork using (module Forking)
open import adequacy.Kept using (module Keeping)
open import adequacy.Moved using (module Planting)
open import adequacy.Restages using (module Staging)
open import adequacy.Weaken using (module Weakening)
open import adequacy.Every using (module Everywhere)
open import adequacy.Names using (module Naming)
open import adequacy.Alike using (module Aliking)

module Taking (R : Set) where
  open Machine R using (Mach; mach; step; wkPlaying; wkTodo)
  open Unsubbing R using (now; then; ≗-trans; bind≗)
  open Growing R using (wkTree; wkPath)
  open Sequencing R using (wkEnv-wk; from-⨾)
  open Pure R using (wkTimer; mapList)
  open Shared Timeline (Out R) using (Heapᴹ; ⟨_,_,_⟩; run; extend)
  open Heap using (World; _⊑_; _⨾_; there; new; grow; cell) renaming (here to hereʳ; same to same⊑)
  open Run (Pureᴾ R) using (Act; done; newRef; under; _>>ᴬ_; compile; Env; wkEnv; module Kit; Ref; wkR; Kont; wkObs)
  open Strongly R using (Carried; Books; Sub; pendingˢ; takeWhileˢ; Path; here; in-take; _⊕_; Here; walk; top; Job; _≗_; module At; Owned; Kernels; Meaning; Queue; Each; Heads; Lingers; names; pendings; Phase; rest-pinned; seen; ≗-refl; newRef≗; taking; takeK; unsubscribing; under≗; module Canon; owned-to; module Eaching; module Lingering)
  open Strongly.Against R using (StackAs; subAs; SrcOf; src-of)
  open Moving R using (planted; pend; part-plant; holds-owed; fed-plant; pendings-plant; subjects-plant; joiners-plant)
  open Everywhere.Settling R using (settled-plant)
  open Everywhere.Gating R using (gated-plant)
  open Ghosting R using (walk-⊕; sorted-⇝)
  open Forking R using (pend-less; subOf; walk-planted)
  open Keeping R using (each-plant; lingers-plant)
  open Planting R using (module Moved)
  open Staging R using (Restages; not-src; wrap-take)
  open Weakening R using (module Grown; pend-grow)
  open Everywhere R using (module Growths)
  open Naming R using (Img; fresh-new; fresh-plant; grows-extend; pending-↭; to-img; wk-img; wk-pairs; wkN)
  open Aliking R using (KontRel; ObsRel; compile-cong; obs-trans; obs-wk; obs-⨾; takeO-cong; walk-grow; ≗-sym)

  -- A TAKEWHILE RESTAGED IN THE WORLD GROWN TWICE: its cut the two
  -- newest cells, live and holding nothing, its source pending beneath
  -- it.
  module Taken {h} {T₀ : Sub h [] R} {Δ A} {i} {p : A → Bool} {s : T.Obs Timeline Δ A} {q} (π : Path T₀ (pendingˢ (T.takeWhile i p s) q)) where
    h₁ h₂ : World
    h₁ = cell (base Bool) ∷ h
    h₂ = cell (maybe quiet) ∷ h₁

    ν₁ : h ⊑ h₁
    ν₁ = new

    ν₂ : h₁ ⊑ h₂
    ν₂ = new

    T₁ : Sub h₁ [] R
    T₁ = wkTree ν₁ T₀

    π₁ : Path T₁ (pendingˢ (T.takeWhile i p s) q)
    π₁ = wkPath ν₁ π

    T₂ : Sub h₂ [] R
    T₂ = wkTree ν₂ T₁

    π₂ : Path T₂ (pendingˢ (T.takeWhile i p s) q)
    π₂ = wkPath ν₂ π₁

    c₂ : Kit.Cut h₂
    c₂ = wkR ν₂ hereʳ , hereʳ

    v : Sub h₂ Δ A
    v = takeWhileˢ i p c₂ nothing taking (pendingˢ s q)

    open Moved π₂ v using (t′; restack; reticked) public

    π′ : Path t′ (pendingˢ s q)
    π′ = planted π₂ v ⊕ in-take here

    walk′ : walk π′ top ≡ walk (in-take {i = i} {p} {c₂} {nothing} {taking} {t = pendingˢ s q} here) (walk π₂ top)
    walk′ = trans (walk-⊕ (planted π₂ v) (in-take here) top)
                  (cong (λ W → walk (in-take {i = i} {p} {c₂} {nothing} {taking} {t = pendingˢ s q} {u = pendingˢ s q} here) W) (walk-planted π₂ v top))

    wg₁ = walk-grow ν₁ π
    wg₂ = walk-grow ν₂ π₁

    obs₂ : ObsRel (wkObs (ν₁ ⨾ ν₂) (Here.obs (walk π top))) (Here.obs (walk π₂ top))
    obs₂ = obs-trans (obs-trans (obs-⨾ ν₁ ν₂ _) (obs-wk ν₂ (proj₁ wg₁))) (proj₁ wg₂)

    -- The kernel's continuation, the take's over the twice-grown walk.
    kontₖ : Kont h₂
    kontₖ τ sub = Kit.attach (Kit.wkCut τ c₂) sub >>ᴬ Here.kont (walk π top) ((ν₁ ⨾ ν₂) ⨾ τ) (unsubscribing (Kit.cut (Kit.wkCut τ c₂)))

    kont₂ : KontRel kontₖ (takeK c₂ (Here.kont (walk π₂ top)))
    kont₂ τ sub = bind≗ (≗-refl (Kit.attach (Kit.wkCut τ c₂) sub)) λ _ →
      ≗-trans (≗-sym (from-⨾ (λ ζ → Here.kont (walk π top) ζ R′) ν₁ ν₂ τ)) (≗-trans (proj₁ (proj₂ wg₁) (ν₂ ⨾ τ) R′) (proj₁ (proj₂ wg₂) τ R′))
      where R′ = unsubscribing (Kit.cut (Kit.wkCut τ c₂))

    env₂ : ∀ {u} (E′ : Env Δ u) (υ : u ⊑ h) → wkEnv υ E′ ≡ Here.env (walk π top) → wkEnv (υ ⨾ (ν₁ ⨾ ν₂)) E′ ≡ Here.env (walk π₂ top)
    env₂ E′ υ e = trans (sym (wkEnv-wk υ (ν₁ ⨾ ν₂) E′)) (trans (cong (wkEnv (ν₁ ⨾ ν₂)) e) (trans (sym (wkEnv-wk ν₁ ν₂ _))
                    (trans (cong (wkEnv ν₂) (proj₂ (proj₂ wg₁))) (proj₂ (proj₂ wg₂)))))

    -- The source compiles as the take's body did, under the take's
    -- observer and continuation over the twice-grown walk.
    code′ : ∀ {u} (E′ : Env Δ u) (υ : u ⊑ h) {act} → wkEnv υ E′ ≡ Here.env (walk π top)
          → act ≗ compile s E′ (υ ⨾ (ν₁ ⨾ ν₂)) (Canon.takeWhileO i p c₂ (wkObs (ν₁ ⨾ ν₂) (Here.obs (walk π top)))) kontₖ
          → Σ World λ u′ → Σ (Env Δ u′) λ E″ → Σ (u′ ⊑ h₂) λ υ′ → wkEnv υ′ E″ ≡ Here.env (walk π′ top)
                         × act ≗ compile s E″ υ′ (Here.obs (walk π′ top)) (Here.kont (walk π′ top))
    code′ {u} E′ υ {act} e c = u , E′ , υ ⨾ (ν₁ ⨾ ν₂)
      , subst (λ W → wkEnv (υ ⨾ (ν₁ ⨾ ν₂)) E′ ≡ Here.env W) (sym walk′) (env₂ E′ υ e)
      , subst (λ W → act ≗ compile s E′ (υ ⨾ (ν₁ ⨾ ν₂)) (Here.obs W) (Here.kont W)) (sym walk′)
          (≗-trans c (compile-cong s E′ (υ ⨾ (ν₁ ⨾ ν₂)) (takeO-cong i p c₂ obs₂) kont₂))

    alone : ∀ {k} → ¬ SrcOf t′ π′ k
    alone (src-of ρ e) = not-src wrap-take (planted π₂ v) ρ e

    alones : ∀ (js : List (Job t′)) → All (λ j → ¬ SrcOf t′ π′ (proj₂ j)) js
    alones _ = tabulateᴬ (λ _ → alone)

    less : pend t′ < pend T₀
    less = subst (pend t′ <_) (trans (pend-grow ν₂ T₁) (pend-grow ν₁ T₀)) (pend-less π₂ v ≤-refl)

    -- A live take over a pending source holds nothing a call is owed
    -- at, and one pending node: its source.
    inner : Moved.Inner π₂ v (in-take here)
    inner = record { no-of = λ { (in-take ()) } ; no-cold = λ { (in-take ()) } ; one-pend = λ { (in-take here) → refl }
                   ; no-end = λ { (in-take ()) } ; no-cut = λ { (in-take ()) } ; no-feed = λ { (in-take ()) } ; no-fin = λ { (in-take ()) }
                   ; not-self = λ _ () }

    -- The cut's cells are names the tree did not hold.
    take-fresh : AllPairs _≢_ (names T₀) → AllPairs _≢_ (names t′)
    take-fresh fs = fresh-plant π₂ v (pending-↭ v) (((λ ()) ∷ []) ∷ [] ∷ []) (wk-pairs ν₂ T₁ (wk-pairs ν₁ T₀ fs))
      (fresh-new (ν₁ ⨾ ν₂) im ((λ { {_ , _} (_ , refl) () }) ∷ (λ { {_ , _} (_ , refl) () }) ∷ []))
      where
        im : ∀ {m} → m ∈ names T₂ → Img (ν₁ ⨾ ν₂) m
        im m∈ = let (_ , x∈ , e₁) = wk-img ν₂ T₁ m∈ ; (_ , _ , e₀) = wk-img ν₁ T₀ x∈ in to-img (ν₁ ⨾ ν₂) (trans (cong (wkN ν₂) e₀) e₁)

    postulate
      -- The source heads no earlier than the take over it.
      untake     : ∀ {k} {c : U.Node Δ A} → Heads k (U.takeWhileᶜ i p c) → Heads k c

    module _ (H′ : Heapᴹ h₂) (eqv : At.part H′ (pendingˢ (T.takeWhile i p s) q) ≡ At.part H′ v)
             (held : At.val H′ (Kit.held c₂) ≡ nothing) where

      rt-behind : ∀ {k} → Each H′ (Heads k) T₂ → Each H′ (Heads k) t′
      rt-behind {k} = each-plant H′ π₂ v eqv tr
        where
          pa : ∀ {Δ′ A′} {w : Sub h₂ Δ′ A′} → Each H′ (Heads k) (pendingˢ (T.takeWhile i p s) q) → (ψ : Path v w) → seen H′ ψ ≡ true
             → ∀ {c} → At.part H′ w ≡ just c → Heads k c
          pa eu here            _ pw   = Each.parts eu here refl (trans eqv pw)
          pa eu (in-take here)  _ refl = untake {c = U.subscribe s q} (Each.parts eu here refl refl)

          tr : Each H′ (Heads k) (pendingˢ (T.takeWhile i p s) q) → Each H′ (Heads k) v
          tr eu = record { parts = pa eu ; pools = λ { (in-take ()) } ; rests = λ { (in-take ()) } }

      rt-kernels : Kernels H′ T₂ → Kernels H′ t′
      rt-kernels kn = record { holds = holds-owed H′ π₂ v tt (Here.kont top) (λ _ → lift held , lift tt) (Kernels.settled kn) (Kernels.holds kn)
                             ; gated = gated-plant H′ π₂ v (λ g → (λ _ → lift tt) , g) (λ _ → lift tt) (Kernels.gated kn)
                             ; settled = settled-plant H′ π₂ v (λ _ → tt) (λ _ → tt , tt) (Kernels.settled kn) }

      -- A take runs what its source runs.
      rt-lingers : Lingers H′ T₂ → Lingers H′ t′
      rt-lingers = lingers-plant H′ π₂ v eqv (λ {C} → rest-pinned (U.restᶜ {B = C} (U.subscribe s q))) (record { pools = λ { (in-take ()) } ; rests = λ { (in-take ()) } })

      rt-meaning : Meaning H′ T₂ → Meaning H′ t′
      rt-meaning mn = record { fed = fed-plant H′ π₂ v (λ _ fd → fd) _ (Meaning.fed mn) }

      pendings′ : pendings t′ ≡ pendings T₂
      pendings′ with pendings-plant π₂ v
      ... | _ , _ , e , e′ = trans e′ (sym e)

      rt-queue : ∀ {k clk ts} → Queue H′ k clk ts T₂ → Queue H′ k clk ts t′
      rt-queue {ts = ts} qu =
        record { timed   = subst (At.Timed H′ ts) (sym pendings′) (Queue.timed qu)
               ; joined  = subst₂ (At.Joined H′) (sym (subjects-plant π₂ v refl)) (sym (joiners-plant π₂ v (λ _ → refl) [])) (Queue.joined qu)
               ; ordered = Queue.ordered qu ; ahead = Queue.ahead qu }

  -- An allocation's continuation, as a function.
  allocates : ∀ {w B t a} {k′ : ∀ {v} → w ⊑ v → Ref v t → Act v B} {m : Act w B} → m ≗ newRef t a k′
            → Σ (∀ {v} → w ⊑ v → Ref v t → Act v B) λ k₁ → m ≡ newRef t a k₁ × (∀ {v} (σ : w ⊑ v) r → k₁ σ r ≗ k′ σ r)
  allocates (newRef≗ refl f) = _ , refl , f

  -- A takeWhile begun allocates its cut, live and holding nothing, and
  -- begins its source under the take's observer, one subscription fewer
  -- owed.
  take-restage : ∀ {g m} (cr : Carried g m) {Δ A i} {p : A → Bool} {s : T.Obs Timeline Δ A}
               → subOf (Carried.ctlAs cr) ≡ just (Δ , A , T.takeWhile i p s) → Restages cr s
  take-restage {m = m₀@(mach ⟨ H , q₀ , run _ σ K ⟩ _ _ _ _ _ _ _)} cr@record { ctlAs = subAs {s = T.takeWhile i p s} π (u , E′ , υ , e , newRef≗ refl kk) sk a } refl refl
    with allocates (kk new hereʳ)
  ... | k₁ , e₁ , kk₂ =
    _ , then (cong (λ x → step (Mx x)) e₁) now
    , record { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = S.t′
             ; ctlAs = subAs S.π′ (S.code′ E′ υ e (kk₂ new hereʳ)) (S.restack sk₂ a₂) (S.alones _)
             ; meets = trans (part-plant H₂ S.π₂ S.v eqv) (trans (G₂.grow-part gr₂ S.T₁) (trans (G₁.grow-part gr₁ (Carried.tree cr)) (Carried.meets cr)))
             ; owned′ = owned-to (Moved.Owning.reowned S.π₂ S.v H₂ eqv (in-take here) S.inner sk₂ a₂
                         (G₂.grow-owned gr₂ {cd′ = cd₂} sk₁ {a′ = a₂} (G₁.grow-owned gr₁ {cd′ = cd₁} sk {a′ = a₁} (Carried.owned cr))))
             ; kernels = S.rt-kernels H₂ eqv refl (Growths.kernels-grow S.ν₂ gr₂ (Growths.kernels-grow S.ν₁ gr₁ (Carried.kernels cr)))
             ; meaning = S.rt-meaning H₂ eqv refl (G₂.grow-meaning gr₂ (G₁.grow-meaning gr₁ (Carried.meaning cr)))
             ; queue = S.rt-queue H₂ eqv refl (G₂.grow-queue gr₂ (G₁.grow-queue gr₁ (Carried.queue cr)))
             ; books = record { fresh = S.take-fresh (Books.fresh bk)
                              ; clocked = proj₁ (Books.clocked bk) , S.reticked sk₂ a₂ (G₂.grow-ticked sk₁ (G₁.grow-ticked sk (proj₂ (Books.clocked bk))))
                              ; paidUp = cong (mapList (wkTodo new)) (cong (mapList (wkTodo new)) (Books.paidUp bk)) ; running = Books.running bk }
             ; sorted = sorted-⇝ (Carried.sorted cr) (then refl (then (cong (λ x → step (Mx x)) e₁) now))
             ; behind′ = Eaching.each-to _ _ (S.rt-behind H₂ eqv refl (G₂.grow-each gr₂ (G₁.grow-each gr₁ (Carried.behind cr))))
             ; lingers′ = Lingering.lingers-to _ (S.rt-lingers H₂ eqv refl (G₂.grow-lingers gr₂ (G₁.grow-lingers gr₁ (Carried.lingers cr)))) }
    , refl , inj₁ (inj₁ S.less)
    where module S = Taken {i = i} {p = p} {s = s} π
          module G₁ = Grown S.ν₁
          module G₂ = Grown S.ν₂
          H₁ = extend H (lift true)
          H₂ = extend H₁ (lift nothing)
          Mx : Act (cell (base Bool) ∷ _) ⊤ → Mach
          Mx x = record m₀ { conf = ⟨ H₁ , q₀ , run x (σ ⨾ new) K ⟩ ; timers = mapList (wkTimer new) (Mach.timers m₀)
                           ; bursts = mapList (mapMaybe (wkPlaying new)) (Mach.bursts m₀) ; todo = mapList (wkTodo new) (Mach.todo m₀) }
          gr₁ = grows-extend H (lift true)
          gr₂ = grows-extend H₁ (lift nothing)
          sk₁ = G₁.grow-stack sk
          sk₂ = G₂.grow-stack sk₁
          a₁ = G₁.grow-alone π sk a
          a₂ = G₂.grow-alone S.π₁ sk₁ a₁
          cd₁ = Grown.code-grow S.ν₁ π E′ υ e
          cd₂ = Grown.code-grow S.ν₂ S.π₁ E′ (υ ⨾ S.ν₁) (Grown.env-grow S.ν₁ π E′ υ e)
          eqv : At.part H₂ (pendingˢ (T.takeWhile i p s) _) ≡ At.part H₂ S.v
          eqv = refl
          bk = Carried.books cr

  -- A value under a position keeps its tick.
  tick-ix0 : ∀ r → tick (r ++ [ ix 0 ]) ≡ tick r
  tick-ix0 []           = refl
  tick-ix0 (ix _ ∷ _)   = refl
  tick-ix0 (subᴾ _ ∷ _) = refl
  tick-ix0 (last ∷ _)   = refl

  -- A world grows only longer, so it reaches a larger one one way.
  ⊑-len : ∀ {w v} → w ⊑ v → length w ≤ length v
  ⊑-len same⊑    = ≤-refl
  ⊑-len (grow σ) = m≤n⇒m≤1+n (⊑-len σ)

  ⊑-irrel : ∀ {w v} (σ τ : w ⊑ v) → σ ≡ τ
  ⊑-irrel same⊑    same⊑    = refl
  ⊑-irrel same⊑    (grow τ) = ⊥-elim (<-irrefl refl (⊑-len τ))
  ⊑-irrel (grow σ) same⊑    = ⊥-elim (<-irrefl refl (⊑-len σ))
  ⊑-irrel (grow σ) (grow τ) = cong grow (⊑-irrel σ τ)

  ⊑≗ : ∀ {w v B} (F : w ⊑ v → Act v B) (σ τ : w ⊑ v) → F σ ≗ F τ
  ⊑≗ F σ τ = subst (λ ζ → F σ ≗ F ζ) (⊑-irrel σ τ) (≗-refl (F σ))

  -- A scope, as its two halves.
  unders : ∀ {w B l} {n : Act w B} {x : Act w ⊤} {y : Act w B} → n ≗ under l x y
         → Σ (Act w ⊤) λ x′ → Σ (Act w B) λ y′ → n ≡ under l x′ y′ × x′ ≗ x × y′ ≗ y
  unders (under≗ ex ey) = _ , _ , refl , ex , ey

  -- What is owed reads neither the act a subscription begins with nor how
  -- it was compiled.
  recode : ∀ {h} {H : Heapᴹ h} {t : Sub h [] R} {w Δ A bs} {s : T.Obs Timeline Δ A} {q} {act act′ : Act h ⊤} {σ : w ⊑ h} {K}
             {π : Path t (pendingˢ s q)} {cd cd′} {sk : StackAs t q σ K bs} {a a′}
         → Owned H t (subAs {act = act} π cd sk a) → Owned H t (subAs {act = act′} π cd′ sk a′)
  recode ow = record { ofs = Owned.ofs ow ; plays = Owned.plays ow ; fires = Owned.fires ow ; begun = Owned.begun ow ; ends = Owned.ends ow
                     ; cuts = Owned.cuts ow ; feeds = Owned.feeds ow ; fins = Owned.fins ow ; bodies = Owned.bodies ow ; placed = Owned.placed ow }
