{-# OPTIONS --guardedness #-}

-- THE SCANNED STREAM HOLDS WHAT ITS SOURCE PROMISES (`simultaneous.Routed.Held`),
-- given a run's facts of its source: each, decidable, holds if not refuted.
module simultaneous.HeldScanned where

open import Data.List using (List; []; _∷_)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (lookup; _∷_) renaming ([] to []ᵉ)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)

open import Tree using (Obs; scan)
open import denotation.Position using (Pos; root; _≟ᵖ_; ix; sub; last; _∙_; frame; cascade)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (enter; DenEnv; Ev; out; end)
open import simultaneous.SObs using (ext; lone; module Elaborate)
open import simultaneous.Relations using (Met)
open import simultaneous.Routed using (Held; Early; valued; Idle; Rest; Routing; r-begin; r-stop; r-over; r-subscribed; r-completed;
  nameOf; nm; Valued; opos; cnt)
open import denotation.Laws.Worlds using (Hots; GoodEnv; Ok; inside-⊑; ⊑-inside; _⊑_)
open import simultaneous.LaneLocal using (inv-ev; late-ext)
open import simultaneous.CombRun using (comb-run)
open import simultaneous.CombSent using (src-op; own-op; cat-op; tag-op; no-track; no-close; tag-branch; Cat-of; Tag; sent-branch; Closing; closing-mark; closing-value; closer-marks; closer-good; src-where; Where) renaming (under to w-under; past to w-past)
open import denotation.EmissionSet using (map-end) renaming (ended to r-ended; late to r-late; shown to r-shown)
open import simultaneous.HeldConnect using (early-inst; rootOf-ext)
open import denotation.Laws.Connect using () renaming (lawful to src-lawful; ok₀ to body-ok)
open import Data.Empty using (⊥-elim)
open import Data.List.Relation.Unary.Any using (here)
open import simultaneous.InstEmit using (begin; stop; subscribed; completed; laneStart; carry; laneDone; burstEnd; instEmit; value; mark; over; outerOpen; outerClose; outerDone)
open import Data.Product using (_×_; _,_; proj₁; Σ; proj₂)
open import Data.Unit using (tt)
import denotation.Laws.ShowsJoin as SJ
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; Routes; count; elab; srcLane; laneSrc; annotate; marked; trackers; closer; combined; laneˢ; each; coldˢ;
  Input; react; going; fed; opening; anyHolds; branch; restamp; wrapped)
open import simultaneous.HeldComb using (ev; CombIn; RunHeld; init; past; run-row; Laid; laid; ended; laid-in; runs-prefix; held-runs)
open import simultaneous.FlatSim using (react-sent; passed; routed; minted)
open import simultaneous.HeldComb using (RunHeld; ev; run-row; held-runs)
open import simultaneous.Reach using (module Reached)
open import Relation.Nullary.Decidable using (decidable-stable)
open import Data.Bool.Properties using (T?)
open import Relation.Nullary using (¬_)
import Relation.Nullary as Nl
open import Data.Sum using ([_,_]′)
open import simultaneous.Layers using (run-tail) renaming (run-row to run-row∈)
open import simultaneous.Readings using (rootOf)
open import denotation.Read using (Visible; Run)
import denotation.Read as Run
import Data.Nat as ℕ
import Data.Nat.Properties as ℕP
import denotation.EmissionSet as ES

open import Tree using (Obs; scan)

-- A run's facts, each decidable from the run, hold if not refuted.
runheld-stable : ∀ {A cs} {rs : List (Pos × Ev (IE A))} → ¬ ¬ RunHeld cs rs → RunHeld cs rs
runheld-stable h = record
  { covered = λ r₁ r₂ eq c ne → routes-stable (cnt r₁) _ λ k → h λ R → k (RunHeld.covered R r₁ r₂ eq c ne)
  ; exact   = λ r₁ r₂ eq → suc-stable _ λ k → h λ R → k (RunHeld.exact R r₁ r₂ eq)
  ; shut    = λ r₁ r₂ eq z bq vy iq → h λ R → RunHeld.shut R r₁ r₂ eq z bq vy iq }
  where
    suc-stable : ∀ n → ¬ ¬ (Σ ℕ λ k → n ≡ suc k) → Σ ℕ λ k → n ≡ suc k
    suc-stable zero    h′ = ⊥-elim (h′ λ { (_ , ()) })
    suc-stable (suc k) _  = k , refl
    routes-stable : ∀ (r : Pos × ℕ) y → ¬ ¬ (Σ ℕ λ k → r ≡ (y , suc k)) → Σ ℕ λ k → r ≡ (y , suc k)
    routes-stable (x , zero)  y h′ = ⊥-elim (h′ λ { (_ , ()) })
    routes-stable (x , suc k) y h′ with x ≟ᵖ y
    ... | Nl.yes refl = k , refl
    ... | Nl.no ne    = ⊥-elim (h′ λ { (_ , refl) → ne refl })

-- What a row shows, it shows whether or not a run is found to meet it.
early-stable : ∀ {y} → ¬ ¬ Early y → Early y
early-stable h v = decidable-stable (T? _) (λ k → h λ e → k (proj₁ (e v))) , λ s → h λ e → proj₂ (e v) s

valued-stable : ∀ {I} → ¬ ¬ Valued I → Valued I
valued-stable {cascade _ _ (ix _) ∙ []}      h = valued
valued-stable {frame ∙ _}                    h = ⊥-elim (h λ ())
valued-stable {cascade _ _ (ix _) ∙ (_ ∷ _)} h = ⊥-elim (h λ ())
valued-stable {cascade _ _ (sub _) ∙ _}      h = ⊥-elim (h λ ())
valued-stable {cascade _ _ last ∙ _}         h = ⊥-elim (h λ ())

late-stable : ∀ {y} → ¬ ¬ (Valued (rootOf y) × opos (rootOf y) ⊑ y) → Valued (rootOf y) × opos (rootOf y) ⊑ y
late-stable {y} h =
  valued-stable (λ k → h λ l → k (proj₁ l)) , inside-⊑ _ y (decidable-stable (T? _) λ k → h λ l → k (⊑-inside (proj₂ l)))

routing-stable : ∀ {m} → ¬ ¬ Routing m → Routing m
routing-stable {begin}      _ = r-begin
routing-stable {stop}       _ = r-stop
routing-stable {over}       _ = r-over
routing-stable {subscribed} _ = r-subscribed
routing-stable {completed}  _ = r-completed
routing-stable {outerOpen}  h = ⊥-elim (h λ ())
routing-stable {outerClose} h = ⊥-elim (h λ ())
routing-stable {laneStart}  h = ⊥-elim (h λ ())
routing-stable {carry}      h = ⊥-elim (h λ ())
routing-stable {laneDone}   h = ⊥-elim (h λ ())
routing-stable {burstEnd}   h = ⊥-elim (h λ ())
routing-stable {outerDone}  h = ⊥-elim (h λ ())

-- THE SCANNED STREAM HOLDS WHAT ITS SOURCE PROMISES: a row it shows is
-- one a run met of the source lays out, a step's output, which is what
-- the step read or a stop, or the source's end.
module Scanned (m : Maybe ℕ) {Γ B} op (s : Obs Timeline Γ (Maybe (Input B))) (ρ : DenEnv Γ) P cs (g : GoodEnv ρ) (ok : Ok (Hots ρ) P)
               (ci : CombIn op (enter (ev m s ρ) P) cs) where
  M = enter (ev m s ρ) P
  S = enter (ev m (each proj₂ (scan (react op) init s)) ρ) P

  open Reached (ev m (each proj₂ (scan (react op) init s)) ρ) P (inv-ev m (each proj₂ (scan (react op) init s)) ρ g P ok) using (reach)

  -- A row shown is laid out by a run met of the source, classically.
  met-laid : ∀ {y e} → S y e → Visible e → ¬ ¬ Σ _ λ rx → Met M rx × Laid op init rx y e
  met-laid {y} {e} x vi k = reach x vi λ (rs , mt) → comb-run m op s ρ P g ok mt λ (rx , mx , ext , eq) →
    k (rx , mx , laid-in op init rx (subst ((y , e) ∈_) eq (∈-++⁺ˡ (∈-++⁺ʳ rs (here refl)))))

  named-laid : ∀ {rx y n} → Met M rx → Laid op init rx y (out (instEmit (mark begin) n)) → n ≡ nameOf y
  named-laid mx (laid rx₁ {q = c} {x = x} rx₂ {j = j} refl vi) with react-sent op (past op init rx₁) x vi
  ... | routed _ refl = trans (CombIn.named ci mq) (cong nm (sym (rootOf-ext c (ix 1 ∷ ix j ∷ []))))
    where mq = proj₁ (run-row rx₁ mx)

  routing-laid : ∀ {rx y m n} → Met M rx → Laid op init rx y (out (instEmit (mark m) n)) → Routing m
  routing-laid mx (laid rx₁ {x = x} rx₂ refl vi) with react-sent op (past op init rx₁) x vi
  ... | routed r refl = r
  ... | minted        = r-stop

  early-laid : ∀ {rx y a n} → Met M rx → Laid op init rx y (out (instEmit (value a) n)) → Early y
  early-laid mx (laid rx₁ {x = x} rx₂ {j = j} refl vi) with react-sent op (past op init rx₁) x vi
  ... | passed refl = early-inst (ix 1 ∷ ix j ∷ []) (CombIn.early ci mq)
    where mq = proj₁ (run-row rx₁ mx)

  ends-laid : ∀ {rx y} → Met M rx → Laid op init rx y end → Early y
  ends-laid mx (ended rx₁ rx₂ refl) = CombIn.ends ci (proj₁ (run-row rx₁ mx))

  late-laid : ∀ {rx y n} → Met M rx → Laid op init rx y (out (instEmit (mark over) n)) → Valued (rootOf y) × opos (rootOf y) ⊑ y
  late-laid mx (laid rx₁ {x = x} rx₂ {j = j} refl vi) with react-sent op (past op init rx₁) x vi
  ... | routed _ refl = late-ext (ix 1 ∷ ix j ∷ []) (CombIn.late ci mq)
    where mq = proj₁ (run-row rx₁ mx)

  done-laid : ∀ {rx y n} → Met M rx → Laid op init rx y (out (instEmit (mark completed) n)) → Early y
  done-laid mx (laid rx₁ {x = x} rx₂ {j = j} refl vi) with react-sent op (past op init rx₁) x vi
  ... | routed _ refl = early-inst (ix 1 ∷ ix j ∷ []) (CombIn.done ci mq)
    where mq = proj₁ (run-row rx₁ mx)

  named : ∀ {y n} → S y (out (instEmit (mark begin) n)) → n ≡ nameOf y
  named x = decidable-stable (_ ≟ᵖ _) λ ng → met-laid x tt λ (_ , mx , l) → ng (named-laid mx l)

  routing : ∀ {y m n} → S y (out (instEmit (mark m) n)) → Routing m
  routing x = routing-stable λ ng → met-laid x tt λ (_ , mx , l) → ng (routing-laid mx l)

  early : ∀ {y a n} → S y (out (instEmit (value a) n)) → Early y
  early x = early-stable λ ng → met-laid x tt λ (_ , mx , l) → ng (early-laid mx l)

  ends : ∀ {y} → S y end → Early y
  ends x = early-stable λ ng → met-laid x tt λ (_ , mx , l) → ng (ends-laid mx l)

  late : ∀ {y n} → S y (out (instEmit (mark over) n)) → Valued (rootOf y) × opos (rootOf y) ⊑ y
  late x = late-stable λ ng → met-laid x tt λ (_ , mx , l) → ng (late-laid mx l)

  done : ∀ {y n} → S y (out (instEmit (mark completed) n)) → Early y
  done x = early-stable λ ng → met-laid x tt λ (_ , mx , l) → ng (done-laid mx l)

  runs : ∀ {rs} → Met S rs → RunHeld cs rs
  runs mt = runheld-stable λ k → comb-run m op s ρ P g ok mt λ (rx , mx , ext , eq) →
    k (runs-prefix ext (subst (RunHeld cs) (sym eq) (CombIn.runs ci mx)))

comb-held : ∀ m {Γ B} op (s : Obs Timeline Γ (Maybe (Input B))) (ρ : DenEnv Γ) P cs → GoodEnv ρ → Ok (Hots ρ) P
          → CombIn op (enter (ev m s ρ) P) cs → Idle (enter (ev m (each proj₂ (scan (react op) init s)) ρ) P)
          → Rest (enter (ev m (each proj₂ (scan (react op) init s)) ρ) P)
          → Held (enter (ev m (each proj₂ (scan (react op) init s)) ρ) P) cs
comb-held m op s ρ P cs g ok ci id re = held-runs named routing early ends done late id re runs
  where open Scanned m op s ρ P cs g ok ci
