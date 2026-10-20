{-# OPTIONS --guardedness #-}

-- What a plant keeps: the paths below it, what is seen along them, what
-- the planted tree leaves running and lingers on, read against one heap.
module adequacy.Kept where

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
open import Data.Maybe using (Maybe; just; nothing; is-just; is-nothing) renaming (map to mapMaybe)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤₁; tt to tt₁)
open import Data.Bool using (_∧_; _∨_; true; false; if_then_else_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

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
open import adequacy.Ghost.Paths using (module GhostingPaths)
open import adequacy.Unsub using (module Unsubbing)
open import adequacy.Fork using (module Forking)

module Keeping (R : Set) where
  open Machine R using (step)
  open Unsubbing R using (then)
  open Shared Timeline (Out R) using (Heapᴹ; ⟨_,_,_⟩)
  open Heap using (there)
  open Run (Pureᴾ R) using (done; module Kit; module FlatKit)
  open Strongly R using (Sub; pendingˢ; ofˢ; mapˢ; takeWhileˢ; connectˢ; Lane; Path; PathLanes; here; in-map; in-scan; in-take; in-outer; in-lanes; in-source; in-body; in-defer; this-lane; next-lane; _⊕_; _⊕ᴸ_; coldˢ; module At; Phase; flatMapˢ; scanˢ; joinˢ; doneˢ; deferˢ; lane)
  open StrongAgainst R using (Each; Lingers; Leaves; Twin; tw-refl; tw-union; tw-under; tw-burst; tw-shift; tw-if; tw-idleʳ; lv-tie; tw-tie; Pinned; unpinned; pinned-trans; pinned-sym; union-pinned; under-pinned; under-moved; bursts-pinned; bursts-moved; rest-pinned; Restful; rf-idle; rf-rest; rf-union; rf-burst; rf-under; restful-pinned; Tied; tie-trans; seen; seenL; seen-⊕; isTaking; ∧-split)
  open StrongHeld R using (DoneBy)
  open Moving R using (plant; plantᴸ; planted; plantedᴸ; part-plant; Same; same; same-map; same-scan; same-take; same-flat; same-connect; same-defer)
  open GhostingPaths R using (each-sub)
  open Forking R using (Lands; LandsL; apart; below; fork; forkᴸ; land-body; land-defer; land-lanes; land-map; land-next; land-outer; land-scan; land-source; land-take; land-this; lands-apart; lands-below; landsᴸ-apart)

  ------------------------------------------------------------------------
  -- What the ghost holds, carried across

  -- What a connect owes its source, alike in the two trees.
  Sourced : ∀ {h} (H : Heapᴹ h) {Δ A} {w₀ w : Sub h Δ A} → Same w₀ w → Set₁
  Sourced H (same-connect {s = s} {s′}) = At.part H s ≡ At.part H s′
  Sourced H _                           = ⊤₁

  -- A node of the rewritten tree: at or below the planted node, or one of
  -- the old tree's, held alike and with the same part.
  Kept : ∀ {h} (H : Heapᴹ h) {Δ A Δ₀ A₀ s₀ q₀ Δ″ A″} {t : Sub h Δ A} (π : Path t (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)) (v : Sub h Δ₀ A₀) {w : Sub h Δ″ A″}
       → Path (plant π v) w → Set₁
  Kept H {t = t} π v {w} π′ = (Σ (Path v w) λ ρ → π′ ≡ planted π v ⊕ ρ)
                            ⊎ (Σ _ λ w₀ → Σ (Path t w₀) λ ψ₀ → Σ (Same w₀ w) λ sm → seen H ψ₀ ≡ seen H π′ × At.part H w₀ ≡ At.part H w × Sourced H sm
                                                                × Lands (fork π v ψ₀) π′)

  KeptL : ∀ {h} (H : Heapᴹ h) {Δ B Δ₀ A₀ s₀ q₀ Δ″ A″} {ls : List (Lane h Δ B)} (π : PathLanes ls (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)) (v : Sub h Δ₀ A₀) {w : Sub h Δ″ A″}
        → PathLanes (plantᴸ π v) w → Set₁
  KeptL H {ls = ls} π v {w} π′ = (Σ (Path v w) λ ρ → π′ ≡ plantedᴸ π v ⊕ᴸ ρ)
                               ⊎ (Σ _ λ w₀ → Σ (PathLanes ls w₀) λ ψ₀ → Σ (Same w₀ w) λ sm → seenL H ψ₀ ≡ seenL H π′ × At.part H w₀ ≡ At.part H w × Sourced H sm
                                                                     × LandsL (forkᴸ π v ψ₀) π′)

  module _ {h} (H : Heapᴹ h) where
    mutual
      keep : ∀ {Δ A Δ₀ A₀ s₀ q₀ Δ″ A″} {t : Sub h Δ A} (π : Path t (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)) (v : Sub h Δ₀ A₀) → At.part H (pendingˢ s₀ q₀) ≡ At.part H v
           → {w : Sub h Δ″ A″} (π′ : Path (plant π v) w) → Kept H π v π′
      keep here v eq π′ = inj₁ (π′ , refl)
      keep π₁@(in-map π) v eq here = inj₂ (_ , here , same-map , refl , sym (part-plant H π₁ v eq) , tt₁ , lands-below)
      keep (in-map π) v eq (in-map π′) with keep π v eq π′
      ... | inj₁ (ρ , e)                    = inj₁ (ρ , cong in-map e)
      ... | inj₂ (_ , q , sm , se , pe , so , ld) = inj₂ (_ , in-map q , sm , se , pe , so , land-map ld)
      keep π₁@(in-scan π) v eq here = inj₂ (_ , here , same-scan , refl , sym (part-plant H π₁ v eq) , tt₁ , lands-below)
      keep (in-scan π) v eq (in-scan π′) with keep π v eq π′
      ... | inj₁ (ρ , e)                    = inj₁ (ρ , cong in-scan e)
      ... | inj₂ (_ , q , sm , se , pe , so , ld) = inj₂ (_ , in-scan q , sm , se , pe , so , land-scan ld)
      keep π₁@(in-take π) v eq here = inj₂ (_ , here , same-take , refl , sym (part-plant H π₁ v eq) , tt₁ , lands-below)
      keep (in-take {c = c} {tk = tk} π) v eq (in-take π′) with keep π v eq π′
      ... | inj₁ (ρ , e)                    = inj₁ (ρ , cong in-take e)
      ... | inj₂ (_ , q , sm , se , pe , so , ld) = inj₂ (_ , in-take q , sm , cong (λ z → At.val H (Kit.live c) ∧ isTaking tk ∧ z) se , pe , so , land-take ld)
      keep π₁@(in-outer π) v eq here = inj₂ (_ , here , same-flat , refl , sym (part-plant H π₁ v eq) , tt₁ , lands-below)
      keep (in-outer π) v eq (in-outer π′) with keep π v eq π′
      ... | inj₁ (ρ , e)                    = inj₁ (ρ , cong in-outer e)
      ... | inj₂ (_ , q , sm , se , pe , so , ld) = inj₂ (_ , in-outer q , sm , se , pe , so , land-outer ld)
      keep (in-outer π) v eq (in-lanes π′) = inj₂ (_ , in-lanes π′ , same , refl , refl , tt₁ , lands-apart)
      keep π₁@(in-lanes π) v eq here = inj₂ (_ , here , same-flat , refl , sym (part-plant H π₁ v eq) , tt₁ , lands-below)
      keep (in-lanes π) v eq (in-outer π′) = inj₂ (_ , in-outer π′ , same , refl , refl , tt₁ , lands-apart)
      keep (in-lanes π) v eq (in-lanes π′) with keepᴸ π v eq π′
      ... | inj₁ (ρ , e)                    = inj₁ (ρ , cong in-lanes e)
      ... | inj₂ (_ , q , sm , se , pe , so , ld) = inj₂ (_ , in-lanes q , sm , se , pe , so , land-lanes ld)
      keep π₁@(in-source π) v eq here = inj₂ (_ , here , same-connect , refl , sym (part-plant H π₁ v eq) , sym (part-plant H π v eq) , lands-below)
      keep (in-source {bd = bd} π) v eq (in-source π′) with keep π v eq π′
      ... | inj₁ (ρ , e)                    = inj₁ (ρ , cong in-source e)
      ... | inj₂ (_ , q , sm , se , pe , so , ld) = inj₂ (_ , in-source q , sm , cong (is-just (At.part H bd) ∧_) se , pe , so , land-source ld)
      keep (in-source {e = e} π) v eq (in-body π′) =
        inj₂ (_ , in-body π′ , same , cong (λ z → (is-just z ∨ is-just e) ∧ seen H π′) (sym (part-plant H π v eq)) , refl , tt₁ , lands-apart)
      keep π₁@(in-body π) v eq here = inj₂ (_ , here , same-connect , refl , sym (part-plant H π₁ v eq) , refl , lands-below)
      keep (in-body π) v eq (in-source π′) = inj₂ (_ , in-source π′ , same , cong (λ z → is-just z ∧ seen H π′) (sym (part-plant H π v eq)) , refl , tt₁ , lands-apart)
      keep (in-body {e = e} {t = src} π) v eq (in-body π′) with keep π v eq π′
      ... | inj₁ (ρ , e′)                   = inj₁ (ρ , cong in-body e′)
      ... | inj₂ (_ , q , sm , se , pe , so , ld) = inj₂ (_ , in-body q , sm , cong ((is-just (At.part H src) ∨ is-just e) ∧_) se , pe , so , land-body ld)
      keep π₁@(in-defer π) v eq here = inj₂ (_ , here , same-defer , refl , sym (part-plant H π₁ v eq) , tt₁ , lands-below)
      keep (in-defer π) v eq (in-defer π′) with keep π v eq π′
      ... | inj₁ (ρ , e)                    = inj₁ (ρ , cong in-defer e)
      ... | inj₂ (_ , q , sm , se , pe , so , ld) = inj₂ (_ , in-defer q , sm , se , pe , so , land-defer ld)

      keepᴸ : ∀ {Δ B Δ₀ A₀ s₀ q₀ Δ″ A″} {ls : List (Lane h Δ B)} (π : PathLanes ls (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)) (v : Sub h Δ₀ A₀) → At.part H (pendingˢ s₀ q₀) ≡ At.part H v
            → {w : Sub h Δ″ A″} (π′ : PathLanes (plantᴸ π v) w) → KeptL H π v π′
      keepᴸ (this-lane {c = c} π) v eq (this-lane π′) with keep π v eq π′
      ... | inj₁ (ρ , e)                    = inj₁ (ρ , cong this-lane e)
      ... | inj₂ (_ , q , sm , se , pe , so , ld) = inj₂ (_ , this-lane q , sm , cong (At.val H (Kit.live c) ∧_) se , pe , so , land-this ld)
      keepᴸ (this-lane π) v eq (next-lane π′) = inj₂ (_ , next-lane π′ , same , refl , refl , tt₁ , landsᴸ-apart)
      keepᴸ (next-lane π) v eq (this-lane π′) = inj₂ (_ , this-lane π′ , same , refl , refl , tt₁ , landsᴸ-apart)
      keepᴸ (next-lane π) v eq (next-lane π′) with keepᴸ π v eq π′
      ... | inj₁ (ρ , e)                    = inj₁ (ρ , cong next-lane e)
      ... | inj₂ (_ , q , sm , se , pe , so , ld) = inj₂ (_ , next-lane q , sm , se , pe , so , land-next ld)

    -- The path to the planted node is held as the path it replaced: what
    -- a path's hold reads lies beside it.
    mutual
      seen-planted : ∀ {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (v : Sub h Δ′ A′) → seen H (planted π v) ≡ seen H π
      seen-planted here v                            = refl
      seen-planted (in-map π) v                      = seen-planted π v
      seen-planted (in-scan π) v                     = seen-planted π v
      seen-planted (in-take {c = c} {tk = tk} π) v   = cong (λ z → At.val H (Kit.live c) ∧ isTaking tk ∧ z) (seen-planted π v)
      seen-planted (in-outer π) v                    = seen-planted π v
      seen-planted (in-lanes π) v                    = seen-plantedᴸ π v
      seen-planted (in-source {bd = bd} π) v         = cong (is-just (At.part H bd) ∧_) (seen-planted π v)
      seen-planted (in-body {e = e} {t = src} π) v   = cong ((is-just (At.part H src) ∨ is-just e) ∧_) (seen-planted π v)
      seen-planted (in-defer π) v                    = seen-planted π v

      seen-plantedᴸ : ∀ {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (π : PathLanes ls u) (v : Sub h Δ′ A′) → seenL H (plantedᴸ π v) ≡ seenL H π
      seen-plantedᴸ (this-lane {c = c} π) v = cong (At.val H (Kit.live c) ∧_) (seen-planted π v)
      seen-plantedᴸ (next-lane π) v         = seen-plantedᴸ π v

    -- What the ghost holds of a node planted with the same part, it holds
    -- of the tree.
    each-plant : ∀ {P : ∀ {Γ A} → U.Node Γ A → Set} {Δ A Δ₀ A₀ s₀ q₀} {t : Sub h Δ A} (π : Path t (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)) (v : Sub h Δ₀ A₀)
               → At.part H (pendingˢ s₀ q₀) ≡ At.part H v → (Each H P (pendingˢ s₀ q₀) → Each H P v) → Each H P t → Each H P (plant π v)
    each-plant {P} {t = t} π v eq tr ev = record { parts = pa ; pools = po ; rests = re }
      where
        inside : ∀ {Δ″ A″} {w : Sub h Δ″ A″} {ψ : Path (plant π v) w} (ρ : Path v w) → ψ ≡ planted π v ⊕ ρ → seen H ψ ≡ true
               → Each H P v × seen H ρ ≡ true
        inside ρ refl s with ∧-split (seen H (planted π v)) (trans (sym (seen-⊕ H (planted π v) ρ)) s)
        ... | sp , sρ = tr (each-sub ev π (trans (sym (seen-planted π v)) sp)) , sρ

        pa : ∀ {Δ′ A′} {w : Sub h Δ′ A′} (ψ : Path (plant π v) w) → seen H ψ ≡ true → ∀ {c} → At.part H w ≡ just c → P c
        pa ψ s pw with keep π v eq ψ
        ... | inj₁ (ρ , e) with inside ρ e s
        ...   | ev′ , sρ = Each.parts ev′ ρ sρ pw
        pa ψ s pw | inj₂ (_ , ψ₀ , _ , se , pe , _ , _) = Each.parts ev ψ₀ (trans se s) (trans pe pw)

        po : ∀ {Δ′ A′ B′} {op f fl oc k r pl} {so : Sub h Δ′ A′} {ls : List (Lane h Δ′ B′)}
           → (ψ : Path (plant π v) (flatMapˢ op f fl oc k r pl so ls)) → seen H ψ ≡ true
           → ∀ {c} → At.part H (flatMapˢ op f fl oc k r pl so ls) ≡ just c → P pl
        po ψ s pw with keep π v eq ψ
        ... | inj₁ (ρ , e) with inside ρ e s
        ...   | ev′ , sρ = Each.pools ev′ ρ sρ pw
        po ψ s pw | inj₂ (_ , ψ₀ , same , se , pe , _ , _)      = Each.pools ev ψ₀ (trans se s) (trans pe pw)
        po ψ s pw | inj₂ (_ , ψ₀ , same-flat , se , pe , _ , _) = Each.pools ev ψ₀ (trans se s) (trans pe pw)

        re : ∀ {Δ′ A′ B′} {S c b kb k fd rp e rt} {src : Sub h Δ′ A′} {bd : Sub h (A′ ∷ Δ′) B′}
           → (ψ : Path (plant π v) (connectˢ S c b kb k fd rp e rt src bd)) → seen H ψ ≡ true
           → ∀ {n} → At.part H (connectˢ S c b kb k fd rp e rt src bd) ≡ just n
           → At.part H src ≡ nothing → ∀ {c₀} → e ≡ just c₀ → P rt
        re ψ s pn ps pe′ with keep π v eq ψ
        ... | inj₁ (ρ , e) with inside ρ e s
        ...   | ev′ , sρ = Each.rests ev′ ρ sρ pn ps pe′
        re ψ s pn ps pe′ | inj₂ (_ , ψ₀ , same , se , pe , _ , _)          = Each.rests ev ψ₀ (trans se s) (trans pe pn) ps pe′
        re ψ s pn ps pe′ | inj₂ (_ , ψ₀ , same-connect , se , pe , so , _) = Each.rests ev ψ₀ (trans se s) (trans pe pn) (trans so ps) pe′

    -- What a node leaves running steps as it rests.
    mutual
      leftover-restful : ∀ {Δ A B} (s : Sub h Δ A) → Restful (At.leftover H {B = B} s)
      leftover-restful (pendingˢ s q)                          = rf-rest
      leftover-restful (coldˢ s hd ph)                         = rf-idle
      leftover-restful (ofˢ p i xs)                            = rf-idle
      leftover-restful doneˢ                                   = rf-idle
      leftover-restful (mapˢ f s)                              = leftover-restful s
      leftover-restful (scanˢ f r s)                           = leftover-restful s
      leftover-restful (takeWhileˢ i p c k tk s)               = leftover-restful s
      leftover-restful (flatMapˢ op f fl oc k r pl so ls)      = rf-union (leftover-restful so) (leftoverL-restful ls)
      leftover-restful (connectˢ S c b kb k fd rp e rt src bd) = rf-union rf-burst (rf-under (leftover-restful bd))
      leftover-restful (joinˢ j sk l x st)                     = rf-idle
      leftover-restful (deferˢ k s)                            = leftover-restful s

      leftoverL-restful : ∀ {Δ A B} (ls : List (Lane h Δ A)) → Restful (At.leftoverL H {B = B} ls)
      leftoverL-restful []                = rf-idle
      leftoverL-restful (lane c k s ∷ ls) = rf-union (leftover-restful s) (leftoverL-restful ls)

    -- A node planted whose leftover twins the pending one's: every
    -- leftover above it twins alike.
    mutual
      leftover-plant : ∀ {Δ A Δ₀ A₀ s₀ q₀ B} {t : Sub h Δ A} (π : Path t (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)) (v : Sub h Δ₀ A₀) → At.part H (pendingˢ s₀ q₀) ≡ At.part H v
                     → (∀ {C} → Twin (At.leftover H {B = C} (pendingˢ s₀ q₀)) (At.leftover H {B = C} v))
                     → Twin (At.leftover H {B = B} t) (At.leftover H {B = B} (plant π v))
      leftover-plant here v eq lv                            = lv
      leftover-plant (in-map π) v eq lv                      = leftover-plant π v eq lv
      leftover-plant (in-scan π) v eq lv                     = leftover-plant π v eq lv
      leftover-plant (in-take π) v eq lv                     = leftover-plant π v eq lv
      leftover-plant (in-defer π) v eq lv                    = leftover-plant π v eq lv
      leftover-plant (in-outer {ls = ls} π) v eq lv          = tw-union (leftover-plant π v eq lv) (tw-refl (At.leftoverL H ls))
      leftover-plant (in-lanes {t = so} π) v eq lv           = tw-union (tw-refl (At.leftover H so)) (leftoverL-plant π v eq lv)
      leftover-plant (in-body {rp = rp} {t = src} π) v eq lv =
        tw-union (tw-refl (U.burstingᶜ rp n)) (tw-under (U.live n) (leftover-plant π v eq lv))
        where n = At.sourced H (At.part H src) (At.leftover H src)
      leftover-plant (in-source {rp = rp} {t = src} {bd = bd} π) v eq lv rewrite part-plant H π v eq with At.part H src
      ... | just s  = tw-refl _
      ... | nothing =
        tw-union (tw-burst rp (leftover-restful src) (leftover-restful (plant π v)) (leftover-plant π v eq lv))
                 (tw-shift (At.leftover H {B = ⊤} bd) (leftover-restful src) (leftover-restful (plant π v)) (leftover-plant π v eq lv))

      leftoverL-plant : ∀ {Δ A Δ₀ A₀ s₀ q₀ B} {ls : List (Lane h Δ A)} (π : PathLanes ls (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)) (v : Sub h Δ₀ A₀) → At.part H (pendingˢ s₀ q₀) ≡ At.part H v
                      → (∀ {C} → Twin (At.leftover H {B = C} (pendingˢ s₀ q₀)) (At.leftover H {B = C} v))
                      → Twin (At.leftoverL H {B = B} ls) (At.leftoverL H {B = B} (plantᴸ π v))
      leftoverL-plant (this-lane {ls = ls} π) v eq lv          = tw-union (leftover-plant π v eq lv) (tw-refl (At.leftoverL H ls))
      leftoverL-plant (next-lane {l = lane c k s} π) v eq lv   = tw-union (tw-refl (At.leftover H s)) (leftoverL-plant π v eq lv)

    -- A pool over a planted outer or lane: what its ended parts left
    -- twins alike.
    pooled-outer : ∀ {Δ A B Δ₀ A₀ s₀ q₀} {fl} {so : Sub h Δ A} {ls : List (Lane h Δ B)} (π : Path so (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)) (v : Sub h Δ₀ A₀)
                 → At.part H (pendingˢ s₀ q₀) ≡ At.part H v
                 → (∀ {C} → Twin (At.leftover H {B = C} (pendingˢ s₀ q₀)) (At.leftover H {B = C} v))
                 → Twin (At.pooled H fl so ls) (At.pooled H fl (plant π v) ls)
    pooled-outer {fl = fl} {ls = ls} π v eq lv =
      tw-union (tw-if (At.val H (FlatKit.Flat.outerDone fl)) (leftover-plant π v eq lv) (tw-refl U.idleᶜ)) (tw-refl (At.pooledL H ls))

    pooled-lanes : ∀ {Δ B Δ₀ A₀ s₀ q₀} {ls : List (Lane h Δ B)} (π : PathLanes ls (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)) (v : Sub h Δ₀ A₀)
                 → At.part H (pendingˢ s₀ q₀) ≡ At.part H v
                 → (∀ {C} → Twin (At.leftover H {B = C} (pendingˢ s₀ q₀)) (At.leftover H {B = C} v))
                 → Twin (At.pooledL H {B = B} ls) (At.pooledL H {B = B} (plantᴸ π v))
    pooled-lanes (this-lane {c = c} {ls = ls} π) v eq lv =
      tw-if (At.val H (Kit.live c)) (tw-refl (At.pooledL H ls)) (tw-union (leftover-plant π v eq lv) (tw-refl (At.pooledL H ls)))
    pooled-lanes (next-lane {l = lane c k s} π) v eq lv =
      tw-if (At.val H (Kit.live c)) (pooled-lanes π v eq lv) (tw-union (tw-refl (At.leftover H s)) (pooled-lanes π v eq lv))

    -- A pool whose outer has not ended and holds no lane runs nothing.
    pooled-fresh : ∀ {Δ A B} {fl : FlatKit.Flat A h} {so : Sub h Δ A} → At.val H (FlatKit.Flat.outerDone fl) ≡ false → Leaves (U.idleᶜ {B = B}) (At.pooled H {B = B} fl so [])
    pooled-fresh d rewrite d = proj₁ (tw-idleʳ U.idleᶜ)

    -- A node planted reading as the pending node did: every flatMap above
    -- it reads its outer as before.
    flags-plant : ∀ {Δ A Δ₀ A₀ s₀ q₀} {t : Sub h Δ A} (π : Path t (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)) (v : Sub h Δ₀ A₀) → At.part H (pendingˢ s₀ q₀) ≡ At.part H v
                → DoneBy H v [] → DoneBy H t [] → DoneBy H (plant π v) []
    flags-plant {t = t} π v eq dv d = fg
      where
        inside : ∀ {Δ″ A″} {w : Sub h Δ″ A″} {ψ : Path (plant π v) w} (ρ : Path v w) → ψ ≡ planted π v ⊕ ρ → seen H ψ ≡ true → seen H ρ ≡ true
        inside ρ refl s = proj₂ (∧-split (seen H (planted π v)) (trans (sym (seen-⊕ H (planted π v) ρ)) s))

        outer-lands : ∀ {Δ′ A′ B′} {op f fl oc k r pl} {so so′ : Sub h Δ′ A′} {ls ls′ : List (Lane h Δ′ B′)}
                        {ψ₀ : Path t (flatMapˢ op f fl oc k r pl so ls)} {ψ′ : Path (plant π v) (flatMapˢ op f fl oc k r pl so′ ls′)}
                    → Lands (fork π v ψ₀) ψ′ → At.part H so ≡ At.part H so′
        outer-lands {ψ₀ = ψ₀} ld with fork π v ψ₀ | ld
        ... | apart _ _                | lands-apart = refl
        ... | below (in-outer ρ) _ _ _ | lands-below = sym (part-plant H ρ v eq)
        ... | below (in-lanes ρ) _ _ _ | lands-below = refl

        fg : DoneBy H (plant π v) []
        fg ψ s with keep π v eq ψ
        ... | inj₁ (ρ , e)                                 = dv ρ (inside ρ e s)
        ... | inj₂ (_ , ψ₀ , same , se , _ , _ , _)        = d ψ₀ (trans se s)
        ... | inj₂ (_ , ψ₀ , same-flat , se , _ , _ , ld)  =
          proj₁ (d ψ₀ (trans se s)) , λ m̸ → trans (proj₂ (d ψ₀ (trans se s)) m̸) (cong is-nothing (outer-lands ld))

    -- What a node planted leaves running twins the pending node's: each
    -- held pool and ended source above it keeps its tie.
    lingers-plant : ∀ {Δ A Δ₀ A₀ s₀ q₀} {t : Sub h Δ A} (π : Path t (pendingˢ {Δ = Δ₀} {A₀} s₀ q₀)) (v : Sub h Δ₀ A₀) → At.part H (pendingˢ s₀ q₀) ≡ At.part H v
                  → (∀ {C} → Twin (At.leftover H {B = C} (pendingˢ s₀ q₀)) (At.leftover H {B = C} v))
                  → Lingers H v → Lingers H t → Lingers H (plant π v)
    lingers-plant {t = t} π v eq lv lgv lg = record { pools = po ; rests = re }
      where
        inside : ∀ {Δ″ A″} {w : Sub h Δ″ A″} {ψ : Path (plant π v) w} (ρ : Path v w) → ψ ≡ planted π v ⊕ ρ → seen H ψ ≡ true → seen H ρ ≡ true
        inside ρ refl s = proj₂ (∧-split (seen H (planted π v)) (trans (sym (seen-⊕ H (planted π v) ρ)) s))

        pool-lands : ∀ {Δ′ A′ B′} {op f fl oc k r pl} {so so′ : Sub h Δ′ A′} {ls ls′ : List (Lane h Δ′ B′)}
                       {ψ₀ : Path t (flatMapˢ op f fl oc k r pl so ls)} {ψ′ : Path (plant π v) (flatMapˢ op f fl oc k r pl so′ ls′)}
                   → Lands (fork π v ψ₀) ψ′ → Twin (At.pooled H fl so ls) (At.pooled H fl so′ ls′)
        pool-lands {fl = fl} {so = so} {ls = ls} {ψ₀ = ψ₀} ld with fork π v ψ₀ | ld
        ... | apart _ _                | lands-apart = tw-refl (At.pooled H fl so ls)
        ... | below (in-outer ρ) _ _ _ | lands-below = pooled-outer {fl = fl} {ls = ls} ρ v eq lv
        ... | below (in-lanes ρ) _ _ _ | lands-below = tw-union (tw-refl (if At.val H (FlatKit.Flat.outerDone fl) then At.leftover H so else U.idleᶜ)) (pooled-lanes ρ v eq lv)

        rest-lands : ∀ {Δ′ A′ B′} {S c b kb k fd rp e rt} {src src′ : Sub h Δ′ A′} {bd bd′ : Sub h (A′ ∷ Δ′) B′}
                       {ψ₀ : Path t (connectˢ S c b kb k fd rp e rt src bd)} {ψ′ : Path (plant π v) (connectˢ S c b kb k fd rp e rt src′ bd′)}
                   → Lands (fork π v ψ₀) ψ′ → Twin (At.leftover H {B = ⊤} src) (At.leftover H {B = ⊤} src′)
        rest-lands {src = src} {ψ₀ = ψ₀} ld with fork π v ψ₀ | ld
        ... | apart _ _                 | lands-apart = tw-refl (At.leftover H {B = ⊤} src)
        ... | below (in-source ρ) _ _ _ | lands-below = leftover-plant ρ v eq lv
        ... | below (in-body ρ) _ _ _   | lands-below = tw-refl (At.leftover H {B = ⊤} src)

        po : ∀ {Δ′ A′ B′} {op f fl oc k r pl} {so : Sub h Δ′ A′} {ls : List (Lane h Δ′ B′)}
           → (ψ : Path (plant π v) (flatMapˢ op f fl oc k r pl so ls)) → seen H ψ ≡ true
           → ∀ {c} → At.part H (flatMapˢ op f fl oc k r pl so ls) ≡ just c → Leaves pl (At.pooled H fl so ls) × Restful pl
        po ψ s pw with keep π v eq ψ
        ... | inj₁ (ρ , e)                                  = Lingers.pools lgv ρ (inside ρ e s) pw
        ... | inj₂ (_ , ψ₀ , same , se , pe , _ , _)        = Lingers.pools lg ψ₀ (trans se s) (trans pe pw)
        ... | inj₂ (_ , ψ₀ , same-flat , se , pe , _ , ld)  = lv-tie (Lingers.pools lg ψ₀ (trans se s) (trans pe pw)) (proj₁ (pool-lands ld))

        re : ∀ {Δ′ A′ B′} {S c b kb k fd rp e rt} {src : Sub h Δ′ A′} {bd : Sub h (A′ ∷ Δ′) B′}
           → (ψ : Path (plant π v) (connectˢ S c b kb k fd rp e rt src bd)) → seen H ψ ≡ true
           → ∀ {n} → At.part H (connectˢ S c b kb k fd rp e rt src bd) ≡ just n
           → At.part H src ≡ nothing → ∀ {c₀} → e ≡ just c₀ → Twin rt (At.leftover H {B = ⊤} src) × Restful rt
        re ψ s pn ps pe′ with keep π v eq ψ
        ... | inj₁ (ρ , e)                                     = Lingers.rests lgv ρ (inside ρ e s) pn ps pe′
        ... | inj₂ (_ , ψ₀ , same , se , pe , _ , _)           = Lingers.rests lg ψ₀ (trans se s) (trans pe pn) ps pe′
        ... | inj₂ (_ , ψ₀ , same-connect , se , pe , so , ld) =
          tw-tie (Lingers.rests lg ψ₀ (trans se s) (trans pe pn) (trans so ps) pe′) (rest-lands ld)
