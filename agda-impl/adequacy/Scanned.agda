{-# OPTIONS --guardedness #-}

-- A SCAN RESTAGED in the world grown by its accumulator.
module adequacy.Scanned where

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
open import Data.Nat using (_<_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Sum using (inj₁)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤₁; tt to tt₁)
open import Data.Bool using (true; if_then_else_)
open import Relation.Nullary using (¬_)
open import Level using (lift)
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
open import operation.AbstractObservable using (base)
open import operation.PureObservable using (module Pure)
open import adequacy.Fork using (module Forking)
open import adequacy.Kept using (module Keeping)
open import adequacy.Moved using (module Planting)
open import adequacy.Restages using (module Staging)
open import adequacy.Weaken using (module Weakening)
open import adequacy.Names using (module Naming)
open import adequacy.Alike using (module Aliking)

module Scanning (R : Set) where
  open Machine R using (mach; step; wkTodo)
  open Unsubbing R using (now; then; ≗-trans)
  open Growing R using (wkTree; wkPath)
  open Pure R using (mapList)
  open Shared Timeline (Out R) using (Heapᴹ; ⟨_,_,_⟩; run; extend)
  open Heap using (World; _⊑_; _⨾_; there; new; cell) renaming (here to hereʳ)
  open Run (Pureᴾ R) using (done; compile; Env; wkEnv; wkObs; wkKont)
  open Strongly R using (Carried; Books; Sub; pendingˢ; Path; here; in-scan; _⊕_; Here; walk; top; Job; _≗_; module At; Kernels; Meaning; Queue; Each; Heads; Lingers; names; pendings; Phase; rest-pinned; seen; scanˢ; newRef≗; module Canon; owned-to; module Eaching; module Lingering)
  open Strongly.Against R using (subAs; SrcOf; src-of)
  open Moving R using (planted; pend; part-plant; holds-plant; settled-plant; gated-plant; fed-plant; pendings-plant; subjects-plant; joiners-plant; head-scan)
  open Ghosting R using (walk-⊕; sorted-⇝)
  open Forking R using (pend-less; subOf; walk-planted)
  open Keeping R using (each-plant; lingers-plant)
  open Planting R using (module Moved)
  open Staging R using (Restages; not-src; wrap-scan)
  open Weakening R using (module Grown; pend-grow)
  open Naming R using (fresh-new; fresh-plant; grows-extend; pending-↭; to-img; wk-img; wk-pairs)
  open Aliking R using (compile-cong; scanO-cong; walk-grow)

  -- A SCAN RESTAGED IN THE GROWN WORLD: its accumulator the newest cell,
  -- its source pending beneath it.
  module Scanned {h} {T₀ : Sub h [] R} {Δ A B} {f : B → A → B} {z : B} {s : T.Obs Timeline Δ A} {q} (π : Path T₀ (pendingˢ (T.scan f z s) q)) where
    h′ : World
    h′ = cell (base B) ∷ h

    T₁ : Sub h′ [] R
    T₁ = wkTree new T₀

    π₁ : Path T₁ (pendingˢ (T.scan f z s) q)
    π₁ = wkPath new π

    v : Sub h′ Δ B
    v = scanˢ f hereʳ (pendingˢ s q)

    open Moved π₁ v using (t′; restack; reticked) public

    π′ : Path t′ (pendingˢ s q)
    π′ = planted π₁ v ⊕ in-scan here

    walk′ : walk π′ top ≡ walk (in-scan {f = f} {r = hereʳ} {t = pendingˢ s q} here) (walk π₁ top)
    walk′ = trans (walk-⊕ (planted π₁ v) (in-scan here) top) (cong (λ W → walk (in-scan {f = f} {r = hereʳ} {t = pendingˢ s q} {u = pendingˢ s q} here) W) (walk-planted π₁ v top))

    ν : h ⊑ h′
    ν = new

    wg = walk-grow ν π


    -- The source compiles as the scan's body did, under the scan's
    -- observer over the grown walk.
    code′ : ∀ {u} (E′ : Env Δ u) (υ : u ⊑ h) {act} → wkEnv υ E′ ≡ Here.env (walk π top)
          → act ≗ compile s E′ (υ ⨾ new) (Canon.scanO f hereʳ (wkObs new (Here.obs (walk π top)))) (wkKont new (Here.kont (walk π top)))
          → Σ World λ u′ → Σ (Env Δ u′) λ E″ → Σ (u′ ⊑ h′) λ υ′ → wkEnv υ′ E″ ≡ Here.env (walk π′ top)
                         × act ≗ compile s E″ υ′ (Here.obs (walk π′ top)) (Here.kont (walk π′ top))
    code′ {u} E′ υ {act} e c = u , E′ , υ ⨾ new
      , subst (λ W → wkEnv (υ ⨾ new) E′ ≡ Here.env W) (sym walk′) (Grown.env-grow ν π E′ υ e)
      , subst (λ W → act ≗ compile s E′ (υ ⨾ new) (Here.obs W) (Here.kont W)) (sym walk′)
          (≗-trans c (compile-cong s E′ (υ ⨾ new) (scanO-cong f hereʳ (proj₁ wg)) (proj₁ (proj₂ wg))))

    alone : ∀ {k} → ¬ SrcOf t′ π′ k
    alone (src-of ρ e) = not-src wrap-scan (planted π₁ v) ρ e

    alones : ∀ (js : List (Job t′)) → All (λ j → ¬ SrcOf t′ π′ (proj₂ j)) js
    alones _ = tabulateᴬ (λ _ → alone)

    less : pend t′ < pend T₀
    less = subst (pend t′ <_) (pend-grow new T₀) (pend-less π₁ v ≤-refl)

    -- A scan over a pending source holds nothing a call is owed at, and
    -- one pending node: its source.
    inner : Moved.Inner π₁ v (in-scan here)
    inner = record { no-of = λ { (in-scan ()) } ; no-cold = λ { (in-scan ()) } ; one-pend = λ { (in-scan here) → refl }
                   ; no-end = λ { (in-scan ()) } ; no-cut = λ { (in-scan ()) } ; no-feed = λ { (in-scan ()) } ; no-fin = λ { (in-scan ()) }
                   ; not-self = λ _ () }

    -- The accumulator is a name the tree did not hold.
    scan-fresh : AllPairs _≢_ (names T₀) → AllPairs _≢_ (names t′)
    scan-fresh fs = fresh-plant π₁ v (pending-↭ v) ([] ∷ []) (wk-pairs new T₀ fs)
      (fresh-new new (λ m∈ → let (_ , _ , e) = wk-img new T₀ m∈ in to-img new e) ((λ { {_ , _} (_ , refl) () }) ∷ []))

    module _ (H′ : Heapᴹ h′) (eqv : At.part H′ (pendingˢ (T.scan f z s) q) ≡ At.part H′ v) where
      -- The scan's heads are its source's.
      rs-behind : ∀ {p} → Each H′ (Heads p) T₁ → Each H′ (Heads p) t′
      rs-behind {p} = each-plant H′ π₁ v eqv tr
        where
          unscan : ∀ {c : U.Node Δ A} {z′} → Heads p (U.scanᶜ f z′ c) → Heads p c
          unscan {c} {z′} hd e = hd (trans (head-scan f z′ (U.step c)) e)

          pa : ∀ {Δ′ A′} {w : Sub h′ Δ′ A′} → Each H′ (Heads p) (pendingˢ (T.scan f z s) q) → (ψ : Path v w) → seen H′ ψ ≡ true
             → ∀ {c} → At.part H′ w ≡ just c → Heads p c
          pa eu here            _ pw   = Each.parts eu here refl (trans eqv pw)
          pa eu (in-scan here)  _ refl = unscan {U.subscribe s q} (Each.parts eu here refl refl)

          tr : Each H′ (Heads p) (pendingˢ (T.scan f z s) q) → Each H′ (Heads p) v
          tr eu = record { parts = pa eu ; pools = λ { (in-scan ()) } ; rests = λ { (in-scan ()) } }

      -- A scan runs what its source runs.
      rs-lingers : Lingers H′ T₁ → Lingers H′ t′
      rs-lingers = lingers-plant H′ π₁ v eqv (λ {C} → rest-pinned (U.restᶜ {B = C} (U.subscribe s q))) (record { pools = λ { (in-scan ()) } ; rests = λ { (in-scan ()) } })

      rs-kernels : Kernels H′ T₁ → Kernels H′ t′
      rs-kernels kn = record { holds = holds-plant H′ π₁ v refl (λ hs → hs) (Kernels.holds kn)
                             ; gated = gated-plant H′ π₁ v (λ g → g) (λ d → d) (Kernels.gated kn)
                             ; settled = settled-plant π₁ v (λ ow → ow) (λ st → st) (Kernels.settled kn) }

      rs-meaning : Meaning H′ T₁ → Meaning H′ t′
      rs-meaning mn = record { fed = fed-plant H′ π₁ v (λ _ fd → fd) _ (Meaning.fed mn) }

      pendings′ : pendings t′ ≡ pendings T₁
      pendings′ with pendings-plant π₁ v
      ... | _ , _ , e , e′ = trans e′ (sym e)

      rs-queue : ∀ {p clk ts} → Queue H′ p clk ts T₁ → Queue H′ p clk ts t′
      rs-queue {ts = ts} qu =
        record { timed   = subst (At.Timed H′ ts) (sym pendings′) (Queue.timed qu)
               ; joined  = subst₂ (At.Joined H′) (sym (subjects-plant π₁ v refl)) (sym (joiners-plant π₁ v (λ _ → refl) [])) (Queue.joined qu)
               ; ordered = Queue.ordered qu ; ahead = Queue.ahead qu }

  -- A scan begun allocates its accumulator, holding the seed, and begins
  -- its source under the scan's observer, one subscription fewer owed.
  scan-restage : ∀ {g m} (cr : Carried g m) {Δ A B} {f : B → A → B} {z : B} {s : T.Obs Timeline Δ A}
               → subOf (Carried.ctlAs cr) ≡ just (Δ , B , T.scan f z s) → Restages cr s
  scan-restage {m = mach ⟨ H , _ , run _ _ _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = subAs {s = T.scan f z s} π (u , E′ , υ , e , newRef≗ refl kk) sk a } refl refl =
    _ , now
    , record { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = S.t′
             ; ctlAs = subAs S.π′ (S.code′ E′ υ e (kk new hereʳ)) (S.restack sk₁ a₁) (S.alones _)
             ; meets = trans (part-plant H′ S.π₁ S.v eqv) (trans (G.grow-part gr (Carried.tree cr)) (Carried.meets cr))
             ; owned′ = owned-to (Moved.Owning.reowned S.π₁ S.v H′ eqv (in-scan here) S.inner {cd = Grown.code-grow S.ν π E′ υ e} sk₁ a₁ (G.grow-owned gr sk (Carried.owned cr)))
             ; kernels = S.rs-kernels H′ eqv (G.grow-kernels gr (Carried.kernels cr))
             ; meaning = S.rs-meaning H′ eqv (G.grow-meaning gr (Carried.meaning cr))
             ; queue = S.rs-queue H′ eqv (G.grow-queue gr (Carried.queue cr))
             ; books = record { fresh = S.scan-fresh (Books.fresh bk)
                              ; clocked = proj₁ (Books.clocked bk) , S.reticked sk₁ a₁ (G.grow-ticked sk (proj₂ (Books.clocked bk)))
                              ; paidUp = cong (mapList (wkTodo new)) (Books.paidUp bk) ; running = Books.running bk }
             ; sorted = sorted-⇝ (Carried.sorted cr) (then refl now) ; behind′ = Eaching.each-to _ _ (S.rs-behind H′ eqv (G.grow-each gr (Carried.behind cr)))
             ; lingers′ = Lingering.lingers-to _ (S.rs-lingers H′ eqv (G.grow-lingers gr (Carried.lingers cr))) }
    , refl , inj₁ (inj₁ S.less)
    where module S = Scanned {f = f} {z = z} {s = s} π
          module G = Grown S.ν
          H′ = extend H (lift z)
          gr = grows-extend H (lift z)
          sk₁ = G.grow-stack sk
          a₁ = G.grow-alone π sk a
          eqv : At.part H′ (pendingˢ (T.scan f z s) _) ≡ At.part H′ S.v
          eqv = refl
          bk = Carried.books cr
