{-# OPTIONS --guardedness #-}

-- The restages that allocate nothing: a `map` and an `of` begun where
-- they were pending, and what a restage owes the measure.
module adequacy.Restages where

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
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing; is-just) renaming (map to mapMaybe)
open import Data.Nat using (_<_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Sum using (inj₁)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤₁; tt to tt₁)
open import Data.Bool using (true; if_then_else_)
open import Relation.Nullary using (¬_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst; subst₂)

open import denotation.MonotonicList.Events using (Timeline; Frame; From; Pos; ix; last; tick; at; _<ᵖ_; <ᵖ-below) renaming (done to doneᶠᵐ; quiet to quietᶠᵐ)
open import denotation.MonotonicList.Events using () renaming (sub to subᴾ)
import Tree as T
import denotation.Unfold as U
open import operation.Machine using (module Machine)
open import operation.PureObservable using (Out; Pureᴾ)
open import operation.AbstractObservable using (module Heap; module Run) renaming (module Machine to Shared)
open import denotation.MonotonicList using (agree-refl)
open import adequacy.Strong using (module Strongly)
open import adequacy.Strong.Against using (module StrongAgainst)
open import adequacy.Strong.Held using (module StrongHeld)
open import adequacy.Moves using (module Moving)
open import adequacy.Every.Gating using (module EverywhereGated)
open import adequacy.Ghost using (module Ghosting)
open import adequacy.Ghost.Paths using (module GhostingPaths)
open import adequacy.Unsub using (module Unsubbing)
open import adequacy.Seq using (module Sequencing)
open import adequacy.Fork using (module Forking)
open import adequacy.Kept using (module Keeping)
open import adequacy.Moved using (module Planting)

module Staging (R : Set) where
  open Machine R using (Mach; mach; step; silent)
  open Unsubbing R using (_⇝_; then; ≗-trans; bind≗)
  open Sequencing R using (seq-done)
  open Shared Timeline (Out R) using (Heapᴹ; ⟨_,_,_⟩)
  open Heap using (World; _⊑_; there) renaming (same to same⊑)
  open Run (Pureᴾ R) using (emitAll; done; _>>ᴬ_; compile; Env; wkEnv; module Kit)
  open Run.Kit (Pureᴾ R) using (skipᴬ)
  open Strongly R using (Sub; pendingˢ; ofˢ; mapˢ; connectˢ; Lane; Path; PathLanes; here; in-map; in-scan; in-take; in-outer; in-lanes; in-source; in-body; in-defer; this-lane; next-lane; _⊕_; _⊕ᴸ_; Here; walk; top; of-leaf; Call; emitC; kontC; _≗_; module At; names; pendings; Phase; ≗-refl; unsubscribing; under≗) renaming (⟦_⟧ to ⟦_⟧ᶜ)
  open StrongAgainst R using (Twin; tw-refl; leaves; Books; Job; Owned; Kernels; Meaning; Queue; Each; Lingers; Pinned; unpinned; rest-pinned; seen; owned-to) renaming (at⟦_⟧ to at⟦_⟧ᶜ)
  open StrongHeld R using (Carried; carried; Heads; module Eaching; module Lingering; Untold; Ended)
  open StrongAgainst.Against R using (StackAs; subAs; runAs; SrcOf; src-of)
  open Moving R using (planted; pend; syn-pos; part-plant; names-plant; fed-plant; pendings-plant; subjects-plant; joiners-plant; head-map)
  open EverywhereGated.Holding R using (holds-plant)
  open EverywhereGated.Settling R using (settled-plant)
  open EverywhereGated.Gating R using (gated-plant)
  open Ghosting R using (_≺_; measure; firstCall)
  open GhostingPaths R using (walk-⊕)
  open Forking R using (pend-less; subOf; walk-planted)
  open Keeping R using (each-plant; lingers-plant; flags-plant)
  open Planting R using (module Moved)

  ------------------------------------------------------------------------
  -- A map restaged: its source pending beneath it

  -- A source wrapped one step by a node that is no connect, or a
  -- connect's body.
  data Wrap {h} : ∀ {Δ A} {s : T.Obs Timeline Δ A} {q} {Δ′ B} {u : Sub h Δ′ B} → Path u (pendingˢ s q) → Set₁ where
    wrap-map  : ∀ {Δ A B} {s : T.Obs Timeline Δ A} {q} {f : A → B} → Wrap (in-map {f = f} {t = pendingˢ s q} here)
    wrap-scan : ∀ {Δ A B} {s : T.Obs Timeline Δ A} {q} {f : B → A → B} {r} → Wrap (in-scan {f = f} {r} {t = pendingˢ s q} here)
    wrap-take : ∀ {Δ A} {s : T.Obs Timeline Δ A} {q} {i p c k tk} → Wrap (in-take {i = i} {p} {c} {k} {tk} {t = pendingˢ s q} here)
    wrap-outer : ∀ {Δ A B} {s : T.Obs Timeline Δ A} {q} {op} {f : A → T.Obs Timeline Δ B} {fl oc k r pl} {ls : List (Lane h Δ B)}
               → Wrap (in-outer {op = op} {f} {fl} {oc} {k} {r} {pl} {t = pendingˢ s q} {ls} here)
    wrap-body : ∀ {Δ A B} {s : T.Obs Timeline (A ∷ Δ) B} {q} {S c b kb k fd e rp rt} {src : Sub h Δ A}
              → Wrap (in-body {S = S} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {t = src} {bd = pendingˢ s q} here)
    wrap-lane : ∀ {Δ A B} {s : T.Obs Timeline Δ B} {q} {op fl oc k r pl c kl} {f : A → T.Obs Timeline Δ B} {t : Sub h Δ A} {ls : List (Lane h Δ B)}
              → Wrap (in-lanes {op = op} {f} {fl} {oc} {k} {r} {pl} {t = t} (this-lane {c = c} {kl} {t = pendingˢ s q} {ls} here))

  wrap-here : ∀ {h Δ A Δ₁ B C} {s : T.Obs Timeline Δ A} {q} {u : Sub h Δ₁ B} {ι : Path u (pendingˢ s q)} → Wrap ι
            → ∀ {S c b kb k fd e rp rt} {bd : Sub h (A ∷ Δ) C} (β : Path u (connectˢ S c b kb k fd rp e rt (pendingˢ s q) bd)) → ι ≢ β ⊕ in-source here
  wrap-here wrap-map  (in-map ())
  wrap-here wrap-scan (in-scan ())
  wrap-here wrap-take (in-take ())
  wrap-here wrap-outer (in-outer ())
  wrap-here wrap-outer (in-lanes _) ()
  wrap-here wrap-body (in-source _) ()
  wrap-here wrap-body (in-body ())
  wrap-here wrap-lane (in-outer _) ()
  wrap-here wrap-lane (in-lanes (this-lane ()))
  wrap-here wrap-lane (in-lanes (next-lane _)) ()

  wrap-src : ∀ {h Δ A Δ₁ B} {s : T.Obs Timeline Δ A} {q} {u : Sub h Δ₁ B} {ι : Path u (pendingˢ s q)} → Wrap ι → Path (pendingˢ s q) u → ⊥
  wrap-src wrap-map  ()
  wrap-src wrap-scan ()
  wrap-src wrap-take ()
  wrap-src wrap-outer ()
  wrap-src wrap-body ()
  wrap-src wrap-lane ()

  -- A path ending under a wrapped source ends under no connect's source.
  mutual
    not-src : ∀ {h Δ A Δ₀ A₀ Δ₁ B₀ C₀} {t : Sub h Δ A} {s : T.Obs Timeline Δ₀ A₀} {q} {u : Sub h Δ₁ B₀} {ι : Path u (pendingˢ s q)} → Wrap ι
            → ∀ {S c b kb k fd e rp rt} {bd : Sub h (A₀ ∷ Δ₀) C₀}
              (α : Path t u) (β : Path t (connectˢ S c b kb k fd rp e rt (pendingˢ s q) bd))
            → α ⊕ ι ≢ β ⊕ in-source here
    not-src w here         β             eq = wrap-here w β eq
    not-src w (in-map α)   (in-map β)    eq = not-src w α β (in-map-inj eq)
      where in-map-inj : ∀ {x y} → in-map x ≡ in-map y → x ≡ y
            in-map-inj refl = refl
    not-src w (in-scan α)  (in-scan β)   eq = not-src w α β (in-scan-inj eq)
      where in-scan-inj : ∀ {x y} → in-scan x ≡ in-scan y → x ≡ y
            in-scan-inj refl = refl
    not-src w (in-take α)  (in-take β)   eq = not-src w α β (in-take-inj eq)
      where in-take-inj : ∀ {x y} → in-take x ≡ in-take y → x ≡ y
            in-take-inj refl = refl
    not-src w (in-outer α) (in-outer β)  eq = not-src w α β (in-outer-inj eq)
      where in-outer-inj : ∀ {x y} → in-outer x ≡ in-outer y → x ≡ y
            in-outer-inj refl = refl
    not-src w (in-outer α) (in-lanes β)  ()
    not-src w (in-lanes α) (in-outer β)  ()
    not-src w (in-lanes α) (in-lanes β)  eq = not-srcᴸ w α β (in-lanes-inj eq)
      where in-lanes-inj : ∀ {x y} → in-lanes x ≡ in-lanes y → x ≡ y
            in-lanes-inj refl = refl
    not-src w (in-source α) here         _  = wrap-src w α
    not-src w (in-source α) (in-source β) eq = not-src w α β (in-source-inj eq)
      where in-source-inj : ∀ {x y} → in-source x ≡ in-source y → x ≡ y
            in-source-inj refl = refl
    not-src w (in-source α) (in-body β)  ()
    not-src w (in-body α)  here          ()
    not-src w (in-body α)  (in-source β) ()
    not-src w (in-body α)  (in-body β)   eq = not-src w α β (in-body-inj eq)
      where in-body-inj : ∀ {x y} → in-body x ≡ in-body y → x ≡ y
            in-body-inj refl = refl
    not-src w (in-defer α) (in-defer β)  eq = not-src w α β (in-defer-inj eq)
      where in-defer-inj : ∀ {x y} → in-defer x ≡ in-defer y → x ≡ y
            in-defer-inj refl = refl

    not-srcᴸ : ∀ {h Δ B Δ₀ A₀ Δ₁ B₀ C₀} {ls : List (Lane h Δ B)} {s : T.Obs Timeline Δ₀ A₀} {q} {u : Sub h Δ₁ B₀} {ι : Path u (pendingˢ s q)} → Wrap ι
             → ∀ {S c b kb k fd e rp rt} {bd : Sub h (A₀ ∷ Δ₀) C₀}
               (α : PathLanes ls u) (β : PathLanes ls (connectˢ S c b kb k fd rp e rt (pendingˢ s q) bd))
             → α ⊕ᴸ ι ≢ β ⊕ᴸ in-source here
    not-srcᴸ w (this-lane α) (this-lane β) eq = not-src w α β (this-inj eq)
      where this-inj : ∀ {x y} → this-lane x ≡ this-lane y → x ≡ y
            this-inj refl = refl
    not-srcᴸ w (this-lane α) (next-lane β) ()
    not-srcᴸ w (next-lane α) (this-lane β) ()
    not-srcᴸ w (next-lane α) (next-lane β) eq = not-srcᴸ w α β (next-inj eq)
      where next-inj : ∀ {x y} → next-lane x ≡ next-lane y → x ≡ y
            next-inj refl = refl

  module Mapped {h} {T₀ : Sub h [] R} {Δ A B} {f : A → B} {s : T.Obs Timeline Δ A} {q} (π : Path T₀ (pendingˢ (T.map f s) q)) where
    v : Sub h Δ B
    v = mapˢ f (pendingˢ s q)

    open Moved π v using (t′; restack; Alone)

    π′ : Path t′ (pendingˢ s q)
    π′ = planted π v ⊕ in-map here

    walk′ : walk π′ top ≡ walk (in-map {f = f} {t = pendingˢ s q} here) (walk π top)
    walk′ = trans (walk-⊕ (planted π v) (in-map here) top) (cong (λ W → walk (in-map {f = f} {t = pendingˢ s q} {u = pendingˢ s q} here) W) (walk-planted π v top))

    -- The source compiles as the map did, under the map's observer.
    code′ : ∀ {act} → (Σ World λ u → Σ (Env Δ u) λ E′ → Σ (u ⊑ h) λ υ → wkEnv υ E′ ≡ Here.env (walk π top)
                         × act ≗ compile (T.map f s) E′ υ (Here.obs (walk π top)) (Here.kont (walk π top)))
          → (Σ World λ u → Σ (Env Δ u) λ E′ → Σ (u ⊑ h) λ υ → wkEnv υ E′ ≡ Here.env (walk π′ top)
                         × act ≗ compile s E′ υ (Here.obs (walk π′ top)) (Here.kont (walk π′ top)))
    code′ {act} (u , E′ , υ , e , c) =
      u , E′ , υ , subst (λ W → wkEnv υ E′ ≡ Here.env W) (sym walk′) e , subst (λ W → act ≗ compile s E′ υ (Here.obs W) (Here.kont W)) (sym walk′) c

    alone : ∀ {k} → ¬ SrcOf t′ π′ k
    alone (src-of ρ e) = not-src wrap-map (planted π v) ρ e

    alones : ∀ (js : List (Job t′)) → All (λ j → ¬ SrcOf t′ π′ (proj₂ j)) js
    alones _ = tabulateᴬ (λ _ → alone)

    part′ : ∀ (H : Heapᴹ h) → At.part H t′ ≡ At.part H T₀
    part′ H = part-plant H π v refl

    names′ : names t′ ≡ names T₀
    names′ = names-plant π v refl

    less : pend t′ < pend T₀
    less = pend-less π v ≤-refl

    -- A map over a pending source holds nothing a call is owed at, and
    -- one pending node: its source.
    inner : Moved.Inner π v (in-map here)
    inner = record { no-of = λ { (in-map ()) } ; no-cold = λ { (in-map ()) } ; one-pend = λ { (in-map here) → refl }
                   ; no-end = λ { (in-map ()) } ; no-cut = λ { (in-map ()) } ; no-feed = λ { (in-map ()) } ; no-fin = λ { (in-map ()) }
                   ; not-self = λ _ () }

    -- What the relation reads of a pending map it reads alike of the
    -- map over its pending source.
    rm-owned   : ∀ {w bs act} {σ : w ⊑ h} {K} {cd cd′} (H : Heapᴹ h) (sk : StackAs T₀ q σ K bs) (a : Alone sk) {a′}
               → Owned H T₀ (subAs {act = act} π cd sk a) → Owned H t′ (subAs {act = act} π′ cd′ (restack sk a) a′)
    rm-owned H sk a ow = Moved.Owning.reowned π v H refl (in-map here) inner sk a ow

    -- The untold and ended invariants persist across a map restage.
    postulate
      rm-told : ∀ (H : Heapᴹ h) {p} → Untold H p T₀ → Untold H p t′
      rm-ended : ∀ (H : Heapᴹ h) → Ended H T₀ → Ended H t′

    -- The map's heads are its source's.
    rm-behind : ∀ (H : Heapᴹ h) {p} → Each H (Heads p) T₀ → Each H (Heads p) t′
    rm-behind H {p} = each-plant H π v refl tr
      where
        unmap : ∀ {c : U.Node Δ A} → Heads p (U.mapᶜ f c) → Heads p c
        unmap {c} hd e = hd (trans (head-map f (U.step c)) e)

        pa : ∀ {Δ′ A′} {w : Sub h Δ′ A′} → Each H (Heads p) (pendingˢ (T.map f s) q) → (ψ : Path v w) → seen H ψ ≡ true
           → ∀ {c} → At.part H w ≡ just c → Heads p c
        pa eu here           _ pw   = Each.parts eu here refl pw
        pa eu (in-map here)  _ refl = unmap {U.subscribe s q} (Each.parts eu here refl refl)

        tr : Each H (Heads p) (pendingˢ (T.map f s) q) → Each H (Heads p) v
        tr eu = record { parts = pa eu ; pools = λ { (in-map ()) } ; rests = λ { (in-map ()) } }

    -- A map runs what its source runs, and its source what it was
    -- pending to.
    rm-lingers : ∀ (H : Heapᴹ h) → Lingers H T₀ → Lingers H t′
    rm-lingers H = lingers-plant H π v refl (λ {C} → leaves (λ ρ _ k → agree-refl k _) (λ ρ d → d) (rest-pinned (U.subscribe s q)) , λ ρ d → d) (record { pools = λ { (in-map ()) } ; rests = λ { (in-map ()) } })

    -- A pending node and a map over one register nothing, queue nothing
    -- and are owed nothing.
    rm-kernels : (H : Heapᴹ h) → Kernels H T₀ → Kernels H t′
    rm-kernels H kn = record { holds = holds-plant H π v refl (λ hs → hs) (Kernels.holds kn)
                             ; gated = gated-plant H π v (λ g → g) (λ d → d) (Kernels.gated kn)
                             ; settled = settled-plant H π v (λ ow → ow) (λ st → st) (Kernels.settled kn) }

    rm-meaning : (H : Heapᴹ h) → Meaning H T₀ → Meaning H t′
    rm-meaning H mn = record { fed = fed-plant H π v (λ _ fd → fd) _ (Meaning.fed mn) }

    pendings′ : pendings t′ ≡ pendings T₀
    pendings′ with pendings-plant π v
    ... | _ , _ , e , e′ = trans e′ (sym e)

    rm-queue : ∀ (H : Heapᴹ h) {p clk ts} → Queue H p clk ts T₀ → Queue H p clk ts t′
    rm-queue H {ts = ts} qu =
      record { timed   = subst (At.Timed H ts) (sym pendings′) (Queue.timed qu)
             ; joined  = subst₂ (At.Joined H) (sym (subjects-plant π v refl)) (sym (joiners-plant π v (λ _ → refl) [])) (Queue.joined qu)
             ; ordered = Queue.ordered qu ; ahead = Queue.ahead qu }

  -- A map begun runs nothing of its own: its source begins under the
  -- map's observer, one subscription fewer owed.
  map-restage : ∀ {g m} (cr : Carried g m) {Δ A B} {f : A → B} {s : T.Obs Timeline Δ A} → subOf (Carried.ctlAs cr) ≡ just (Δ , B , T.map f s)
              → Σ (Carried g m) λ cr′ → subOf (Carried.ctlAs cr′) ≡ just (Δ , A , s) × measure (carried cr′) ≺ measure (carried cr)
  map-restage {m = mach ⟨ H , _ , _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = subAs π cd sk a } refl =
    record { sane = Carried.sane cr ; placed = Carried.placed cr ; deep = Carried.deep cr ; tree = N.t′ ; ctlAs = subAs M.π′ (M.code′ cd) (N.restack sk a) (M.alones _)
           ; meets = trans (M.part′ H) (Carried.meets cr) ; owned′ = owned-to (M.rm-owned H sk a (Carried.owned cr))
           ; kernels = M.rm-kernels H (Carried.kernels cr) ; meaning = M.rm-meaning H (Carried.meaning cr) ; queue = M.rm-queue H (Carried.queue cr)
           ; books = record { fresh = subst (AllPairs _≢_) (sym M.names′) (Books.fresh bk)
                            ; clocked = proj₁ (Books.clocked bk) , N.reticked sk a (proj₂ (Books.clocked bk))
                            ; paidUp = Books.paidUp bk ; running = Books.running bk }
           ; sorted = Carried.sorted cr ; behind′ = Eaching.each-to _ _ (M.rm-behind H (Carried.behind cr)) ; told = M.rm-told H (Carried.told cr) ; ended = M.rm-ended H (Carried.ended cr) ; lingers′ = Lingering.lingers-to _ (M.rm-lingers H (Carried.lingers cr)) ; flags = flags-plant H π M.v refl (λ { (in-map ()) }) (Carried.flags cr) }
    , refl , inj₁ (inj₁ M.less)
    where module M = Mapped π
          module N = Moved π M.v
          bk = Carried.books cr

  -- WHAT AN `of` RUNS: its values, then its continuation.
  Offering : ∀ {Δ A} → T.Obs Timeline Δ A → List A → Set₁
  Offering {Δ} {A} s xs = ∀ {w u} (E′ : Env Δ u) (υ : u ⊑ w) (W : Here w Δ A)
                        → compile s E′ υ (Here.obs W) (Here.kont W) ≗ (emitAll (Here.obs W) 0 xs >>ᴬ (Here.kont W same⊑ (unsubscribing skipᴬ) >>ᴬ done tt))

  -- AN `of` BEGUN: planted where it was pending, its values and then its
  -- continuation the agenda's calls, one subscription fewer owed.  An
  -- `empty` begins as a spent one.
  module Offered {h} {T₀ : Sub h [] R} {Δ A} {s : T.Obs Timeline Δ A} {xs : List A} {q} (π : Path T₀ (pendingˢ s q))
                 (sp : U.subscribe s q ≡ U.ofᶜ q 0 xs) (cs : Offering s xs) where
    v : Sub h Δ A
    v = ofˢ q 0 xs

    open Moved π v using (t′; restack; Alone; reticked)

    π′ : Path t′ v
    π′ = planted π v

    ks : List (Call t′)
    ks = emitC π′ ∷ kontC of-leaf π′ ∷ []

    -- The `of`'s code its values then its continuation, the two calls.
    code′ : ∀ {act} → (Σ World λ u → Σ (Env Δ u) λ E′ → Σ (u ⊑ h) λ υ → wkEnv υ E′ ≡ Here.env (walk π top)
                         × act ≗ compile s E′ υ (Here.obs (walk π top)) (Here.kont (walk π top)))
          → act ≗ ⟦ ks ⟧ᶜ
    code′ (_ , E′ , υ , _ , c) =
      ≗-trans c (subst (λ W → _ ≗ (emitAll (Here.obs W) 0 xs >>ᴬ (Here.kont W same⊑ (unsubscribing skipᴬ) >>ᴬ done tt)))
                       (sym (walk-planted π v top)) (cs E′ υ (walk π top)))

    eqp : ∀ (H : Heapᴹ h) → At.part H (pendingˢ s q) ≡ At.part H v
    eqp H = cong just sp

    less : pend t′ < pend T₀
    less = pend-less π v (syn-pos s)

    postulate
      of-owned : ∀ {w bs act} {σ : w ⊑ h} {K} {cd} (H : Heapᴹ h) (sk : StackAs T₀ q σ K bs) (a : Alone sk) (e : act ≗ ⟦ ks ⟧ᶜ)
               → Owned H T₀ (subAs {act = act} π cd sk a) → Owned H t′ (runAs ks e (restack sk a))

    -- An `of` registers nothing, queues nothing and is owed nothing.
    of-kernels : (H : Heapᴹ h) → Kernels H T₀ → Kernels H t′
    of-kernels H kn = record { holds = holds-plant H π v refl (λ hs → hs) (Kernels.holds kn)
                             ; gated = gated-plant H π v (λ g → g) (λ d → d) (Kernels.gated kn)
                             ; settled = settled-plant H π v (λ ()) (λ st → st) (Kernels.settled kn) }

    of-meaning : (H : Heapᴹ h) → Meaning H T₀ → Meaning H t′
    of-meaning H mn = record { fed = fed-plant H π v (λ _ fd → fd) _ (Meaning.fed mn) }

    pendings′ : pendings t′ ≡ pendings T₀
    pendings′ with pendings-plant π v
    ... | _ , _ , e , e′ = trans e′ (sym e)

    of-queue : ∀ (H : Heapᴹ h) {p clk ts} → Queue H p clk ts T₀ → Queue H p clk ts t′
    of-queue H {ts = ts} qu =
      record { timed   = subst (At.Timed H ts) (sym pendings′) (Queue.timed qu)
             ; joined  = subst₂ (At.Joined H) (sym (subjects-plant π v refl)) (sym (joiners-plant π v (λ _ → refl) [])) (Queue.joined qu)
             ; ordered = Queue.ordered qu ; ahead = Queue.ahead qu }

    -- The untold and ended invariants persist across an of restage.
    postulate
      of-told : ∀ (H : Heapᴹ h) {p} → Untold H p T₀ → Untold H p t′
      of-ended : ∀ (H : Heapᴹ h) → Ended H T₀ → Ended H t′

    -- The `of`'s heads are the subscription's.
    of-behind : ∀ (H : Heapᴹ h) {p} → Each H (Heads p) T₀ → Each H (Heads p) t′
    of-behind H {p} = each-plant H π v (eqp H) tr
      where
        tr : Each H (Heads p) (pendingˢ s q) → Each H (Heads p) v
        tr eu = record { parts = λ { here _ pw → Each.parts eu here refl (trans (eqp H) pw) } ; pools = λ () ; rests = λ () }

    -- An `of` runs nothing past its end, nor did it pending.
    of-lingers : ∀ (H : Heapᴹ h) → Lingers H T₀ → Lingers H t′
    of-lingers H = lingers-plant H π v (eqp H) (λ {C} → subst (λ c → Twin (U.restᶜ {B = C} c) U.idleᶜ) (sym sp) of-idle) (record { pools = λ () ; rests = λ () })
      where
        of-idle : ∀ {C} → Twin (U.restᶜ {B = C} (U.ofᶜ q 0 xs)) U.idleᶜ
        of-idle = leaves (λ ρ _ n → agree-refl n _) (λ ρ d → d) unpinned , λ ρ d → d

  -- The configuration an `of` planted makes: its first call its values.
  Offers : ∀ {g m} → Carried g m → ∀ {Δ A} → List A → Set₁
  Offers {g} {m} cr {Δ} {A} xs = Σ (Carried g m) λ cr′ → Σ Pos λ p → Σ (Path (Carried.tree cr′) (ofˢ {Δ = Δ} {A} p 0 xs)) λ π′
                                 → firstCall (Carried.ctlAs cr′) ≡ just (emitC π′) × measure (carried cr′) ≺ measure (carried cr)

  offer-restage : ∀ {g m} (cr : Carried g m) {Δ A} {s : T.Obs Timeline Δ A} {xs : List A} → subOf (Carried.ctlAs cr) ≡ just (Δ , A , s)
                → (∀ q → U.subscribe s q ≡ U.ofᶜ q 0 xs) → Offering s xs → Offers cr {Δ} {A} xs
  offer-restage {m = mach ⟨ H , _ , _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = subAs {q = q} π cd sk a } refl sp cs =
    record { sane = Carried.sane cr ; placed = Carried.placed cr ; deep = Carried.deep cr ; tree = N.t′ ; ctlAs = runAs O.ks (O.code′ cd) (N.restack sk a)
           ; meets = trans (part-plant H π O.v (O.eqp H)) (Carried.meets cr) ; owned′ = owned-to (O.of-owned H sk a (O.code′ cd) (Carried.owned cr))
           ; kernels = O.of-kernels H (Carried.kernels cr) ; meaning = O.of-meaning H (Carried.meaning cr) ; queue = O.of-queue H (Carried.queue cr)
           ; books = record { fresh = subst (AllPairs _≢_) (sym (names-plant π O.v refl)) (Books.fresh bk)
                            ; clocked = proj₁ (Books.clocked bk) , N.reticked sk a (proj₂ (Books.clocked bk))
                            ; paidUp = Books.paidUp bk ; running = Books.running bk }
           ; sorted = Carried.sorted cr ; behind′ = Eaching.each-to _ _ (O.of-behind H (Carried.behind cr)) ; told = O.of-told H (Carried.told cr) ; ended = O.of-ended H (Carried.ended cr) ; lingers′ = Lingering.lingers-to _ (O.of-lingers H (Carried.lingers cr)) ; flags = flags-plant H π O.v (O.eqp H) (λ ()) (Carried.flags cr) }
    , q , O.π′ , refl , inj₁ (inj₁ O.less)
    where module O = Offered π (sp q) cs
          module N = Moved π O.v
          bk = Carried.books cr

  of-restage : ∀ {g m} (cr : Carried g m) {Δ A} {xs : List A} → subOf (Carried.ctlAs cr) ≡ just (Δ , A , T.of xs) → Offers cr {Δ} {A} xs
  of-restage cr {xs = xs} e = offer-restage cr e (λ _ → refl) (λ _ _ W → bind≗ (≗-refl (emitAll (Here.obs W) 0 xs)) λ _ → seq-done _)

  empty-restage : ∀ {g m} (cr : Carried g m) {Δ A} → subOf (Carried.ctlAs cr) ≡ just (Δ , A , T.empty) → Offers cr {Δ} {A} []
  empty-restage cr e = offer-restage cr e (λ _ → refl) (λ _ _ _ → under≗ (≗-refl _) (seq-done _))

  -- A KERNEL BEGUN BY ALLOCATING: its cells allocated, its node planted
  -- in the grown world, the run at the subscription the kernel begins
  -- next, carried, one subscription fewer owed.
  Restages : ∀ {g m} → Carried g m → ∀ {Δ A} → T.Obs Timeline Δ A → Set₁
  Restages {g} {m} cr {Δ} {A} s = ∀ {m′} → step m ≡ silent m′ → Σ Mach λ m₀ → m′ ⇝ m₀ × Σ (Carried g m₀) λ cr′
                                  → subOf (Carried.ctlAs cr′) ≡ just (Δ , A , s) × measure (carried cr′) ≺ measure (carried cr)
