{-# OPTIONS --guardedness #-}

-- EVERY ELABORATED STREAM HOLDS (`simultaneous.Routed.Held`), former by
-- former, and so the batcher's source keeps its dead instants dead.
--
-- A `defer` is reached through its approximants: each is a finite tree,
-- so the formers' leaves hold of it by induction on the bound, and the
-- meaning is their limit.
module simultaneous.Held where

open import Data.List using ([]; _∷_; [_])
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (lookup; _∷_) renaming ([] to []ᵉ)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (refl)

open import Tree using (Obs; Later; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer; mergeᶠ)
open import denotation.Position using (root; _≟ᵖ_; ix; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (hot; enter; ⟦_⟧; DenEnv; approx; spin; Few)
open import simultaneous.SObs using (SObs; plain; lone; module Elaborate)
open import simultaneous.Relations using (elaborated)
open import simultaneous.Shut using (Shut)
open import simultaneous.Routed using (Held; Early; Rest)
open import denotation.Laws.Worlds using (Hots; GoodEnv; Ok; Lawful; ok-step)
open import simultaneous.Relabel using (same-mark; same-value)
open import simultaneous.HeldWrap using (held-wrapped)
open import simultaneous.HeldScan using (held-scan-at; Relabels)
open import simultaneous.HeldDefer using (held-defer; placed-defer)
open import simultaneous.LaneLocal using (inv-ev)
open import simultaneous.HeldTrigger using (held-trigger)
open import simultaneous.CombSent using (src-op; own-op; cat-op; tag-op; no-track; no-close; tag-branch; Cat-of; Tag; sent-branch; Closing; closing-mark; closing-value; closer-marks; closer-good; src-where; Where) renaming (under to w-under; past to w-past)
open import denotation.EmissionSet using (map-end) renaming (ended to r-ended; late to r-late; shown to r-shown)
open import simultaneous.HeldConnect using (early-inst; tracks-fin)
open import denotation.Laws using (good-cons)
open import denotation.Laws.Connect using () renaming (lawful to src-lawful; ok₀ to body-ok)
open import Data.List.Relation.Unary.Any using (there)
open import simultaneous.InstEmit using (begin; stop; subscribed; completed; laneStart; carry; laneDone; burstEnd; instEmit; value; mark; over; outerOpen; outerClose; outerDone)
open import Data.Product using (Σ; _,_)
open import Data.Unit using (⊤; tt)
import denotation.Laws.ShowsJoin as SJ
open import simultaneous.HeldBase using (EnvHeld; Fresh; fresh-adm; module FlatHots; IH; module Quiet; conn-ev; empty-few; held-cold; held-connect;
  held-empty; held-map; held-of; held-scan; held-takeWhile; ih)
open import simultaneous.Routed using (Adm; PlacedD; Placed; adm-∪)
open import denotation.Laws.Worlds using (plain-ix)
open import simultaneous.LaneLocal using (Fit; FitD; held-fit; flatE; blockE; of-outer; empty-ends)
open import denotation.EmissionSet using (EmissionSet; Proper)
open import Data.Bool using (true; false)
open import Data.Product using (proj₁; proj₂)
open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; Routes; count; elab; srcLane; laneSrc; annotate; marked; trackers; closer; combined; laneˢ; each; coldˢ;
  Input; react; going; fed; opening; anyHolds; branch; restamp; wrapped; Out; cut; left)
open import simultaneous.HeldComb using (ev; from)
open import simultaneous.HeldRead using (held-connected)
open import simultaneous.HeldComb using (ev)
import Relation.Nullary as Nl
open import Data.Sum using ([_,_]′)
open import simultaneous.Layers using (run-tail; run-after) renaming (run-row to run-row∈)
open import denotation.Read using (Visible; After; cursor; Run; loud) renaming (_∷_ to _∷ᴿ_)
import denotation.Read as Run
import Data.Nat as ℕ
import Data.Nat.Properties as ℕP
import denotation.EmissionSet as ES
open import denotation.Laws.Truthful using (reached)
open import simultaneous.HeldLim using (module LimHeld)
open import simultaneous.HeldScanned using (comb-held)
open import simultaneous.HeldSrc using (module CombSrc)
open import simultaneous.HeldReal using (module CombReal)
open import simultaneous.HeldIn using (HeldIn; held-in)
open import denotation.Laws.Shows using (few-down)

held-comb : ∀ m {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) op (f : A → Obs Timeline Γ B) s
            (env : DenEnv Δ) cs → GoodEnv env → (eh : EnvHeld ρ env cs)
          → (∀ a {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ′) → IH m ρ′ (f a))
          → ∀ p → Ok (Hots env) p → Fresh eh p → Early p
          → let open FlatHots m ρ op f s env p in
            Held (enter (ev m trig env₀) (c ⊕ [ ix 1 ])) ((c ⊕ [ ix 1 ]) ∷ p ∷ cs) → Placed (Fresh eh) σ₁
          → Lawful σ₁ → Lawful σ₂ → Lawful σ₃ → Ok (Hots (hot σ₁ ∷ env₀)) p₀ → Ok (Hots (hot σ₂ ∷ hot σ₁ ∷ env₀)) p₀₀
          → Ok (Hots env′) P → Early P
          → HeldIn (Few R) scanned (P ∷ p₀₀ ∷ p₀ ∷ c ∷ p ∷ cs)
held-comb m ρ op f s env cs gd eh hf p ok fr ep H₁ tp L₁ L₂ L₃ ok₁ ok₂ ok₃ ep₃ =
  comb-held m op src env′ P _ (good-cons L₃ (good-cons L₂ (good-cons L₁ (good-cons L₀ gd)))) ok₃ (λ kw F → few-down F kw)
    (CombReal.comb m ρ op f s env cs gd eh hf p ok fr ep H₁ tp L₁ L₂ L₃ ok₁ ok₂ ok₃ ep₃)
    (CombSrc.scan-idle m ρ op f s env cs gd eh hf p ok fr ep H₁ tp L₁ L₂ L₃ ok₁ ok₂ ok₃ ep₃)
    (CombSrc.scan-rest m ρ op f s env cs gd eh hf p ok fr ep H₁ tp L₁ L₂ L₃ ok₁ ok₂ ok₃ ep₃)
  where
    open FlatHots m ρ op f s env p using (src; env′; P)
    L₀ = src-lawful {A = ⊤} {B = ⊤} {s = ev m empty env} {F = λ h → ev m empty (h ∷ env)} (inv-ev m empty env gd) (λ L → inv-ev m empty (hot _ ∷ env) (good-cons L gd)) p ok

-- THE TRIGGER FITS: its blocker's end is admissible, and the source below
-- is held and placed where the bounded merge subscribes it.
trig-fit : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (s : Obs Timeline Γ A) (env : DenEnv Δ) cs → GoodEnv env
         → (eh : EnvHeld ρ env cs) → (∀ {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ′) → IH m ρ′ s)
         → ∀ p → Ok (Hots env) p → Fresh eh p → Early p
         → (L₀ : Lawful (Proper (enter (ev m empty env) (p ⊕ [ ix 1 ]))))
         → FitD (Hots (hot (Proper (enter (ev m empty env) (p ⊕ [ ix 1 ]))) ∷ env)) (Fresh eh)
                (ev m (flatMap (mergeᶠ (just 1)) (λ c → srcLane ρ s c) (of (true ∷ false ∷ []))) (hot (Proper (enter (ev m empty env) (p ⊕ [ ix 1 ]))) ∷ env))
trig-fit m {A = A} ρ s env cs g eh hs p ok fr ep L₀ =
  flatE m (mergeᶠ (just 1)) (λ c → srcLane ρ s c) (of (true ∷ false ∷ [])) (hot σ₀ ∷ env) g₀ ad₀ lane (of-outer m _ _ ad₀)
  where
    σ₀ : EmissionSet ⊤
    σ₀ = Proper (enter (ev m empty env) (p ⊕ [ ix 1 ]))
    g₀ : GoodEnv (hot σ₀ ∷ env)
    g₀ = good-cons L₀ g
    ad₀ : Adm (Hots (hot σ₀ ∷ env)) (Fresh eh)
    ad₀ = adm-∪ {t = σ₀} (fresh-adm eh)
    eh₀ : EnvHeld (λ i → there (ρ i)) (hot σ₀ ∷ env) cs
    eh₀ = record { bound = EnvHeld.bound eh ; apart = EnvHeld.apart eh }
    E = empty-ends m env (fresh-adm eh) (p ⊕ [ ix 1 ]) (early-inst [ ix 1 ] ep) (Adm.step (fresh-adm eh) ok fr plain-ix)
    lane : ∀ c → FitD (Hots (hot σ₀ ∷ env)) (Fresh eh) (ev m (srcLane ρ s c) (hot σ₀ ∷ env))
    lane true  = blockE m σ₀ env ad₀ L₀ (proj₁ E) (proj₂ E)
    lane false q okq fq eq = held-fit (IH.holds (hs (λ i → there (ρ i))) (hot σ₀ ∷ env) cs g₀ eh₀ q okq fq eq)
                                      (IH.placed (hs (λ i → there (ρ i))) (hot σ₀ ∷ env) cs g₀ eh₀ q okq fq eq)

-- A FLATMAP HANGS ITS LANES ON ADMISSIBLE ROWS: the trigger's, the
-- closer's and every inner's, each placed by its own child.
postulate
  placed-flatMap : ∀ m {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) op (f : A → Obs Timeline Γ B) s
                 → (∀ {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ′) → IH m ρ′ s)
                 → (∀ a {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ′) → IH m ρ′ (f a))
                 → ∀ env cs → GoodEnv env → (eh : EnvHeld ρ env cs) → PlacedD (Hots env) (Fresh eh) (ev m (elab ρ (flatMap op f s)) env)

held-flatMap : ∀ m {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) op (f : A → Obs Timeline Γ B) s
             → (∀ {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ′) → IH m ρ′ s)
             → (∀ a {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ′) → IH m ρ′ (f a)) → IH m ρ (flatMap op f s)
held-flatMap m ρ op f s hs hf = ih (λ env cs g eh p ok fr ep →
  let open FlatHots m ρ op f s env p using (trig; real; c; p₀; p₀₀; tracks-trig; tracks-closer; tracks-real; σ₀) in
  conn-ev m empty _ env cs g p ok ep (tracks-fin (empty-few m env (p ⊕ [ ix 1 ]))) λ L₀ ok₀ ep₀ → held-in (
    conn-ev m trig _ _ (p ∷ cs) (good-cons L₀ g) c ok₀ ep₀ tracks-trig λ L₁ ok₁ ep₁ → held-in (
      conn-ev m closer _ _ (c ∷ p ∷ cs) (good-cons L₁ (good-cons L₀ g)) p₀ ok₁ ep₁ tracks-closer λ L₂ ok₂ ep₂ → held-in (
        conn-ev m real _ _ (p₀ ∷ c ∷ p ∷ cs) (good-cons L₂ (good-cons L₁ (good-cons L₀ g))) p₀₀ ok₂ ep₂ tracks-real λ L₃ ok₃ ep₃ →
          held-comb m ρ op f s env cs g eh hf p ok fr ep
            (held-trigger m ρ s env cs p g ok ep (fresh-adm eh) fr
              (IH.holds (hs (λ i → there (ρ i))) _ cs (good-cons L₀ g) record { bound = EnvHeld.bound eh ; apart = EnvHeld.apart eh }))
            (λ r sh → Fit.placed (trig-fit m ρ s env cs g eh hs p ok fr ep L₀ (c ⊕ [ ix 1 ]) (ok-step c ok₀)
                                    (Adm.step (adm-∪ {t = σ₀} (fresh-adm eh)) ok₀ (Adm.bare (fresh-adm eh) fr λ ()) plain-ix) (early-inst [ ix 1 ] ep₀))
                                  (proj₁ r) sh)
            L₁ L₂ L₃ ok₁ ok₂ ok₃ ep₃))))
  (placed-flatMap m ρ op f s hs hf)

-- A DEFER'S LIMIT KEEPS ITS INSTANTS FINITE: past a zero count, finitely
-- many rows of the instant last begun.  Each approximant's rest bounds only
-- its own rows, and the limit's rows of an instant are those of every
-- approximant together, which no one approximant's list bounds.
postulate
  lim-rest : ∀ {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (l : Later Timeline Γ A)
           → (∀ n → IH (just n) ρ (defer l))
           → ∀ env cs → GoodEnv env → EnvHeld ρ env cs → ∀ p → Ok (Hots env) p → Early p
           → Rest (enter (⟦ elab ρ (defer l) ⟧ env) p)

-- THE BOTTOM APPROXIMANT shows only skips; each further one is the body
-- under a `defer`'s guard; the meaning is the approximants' limit, held
-- wherever the approximants agree with it.
-- Every row of the limit is some approximant's.
lim-row : ∀ {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (l : Later Timeline Γ A) (env : DenEnv Δ) p {y e}
        → enter (⟦ elab ρ (defer l) ⟧ env) p y e → Σ ℕ λ N → enter (approx N (elab ρ (defer l)) env) p y e
lim-row ρ l env p (ES.from N h , _) = N , h N ℕP.≤-refl

held-lim : ∀ {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (l : Later Timeline Γ A)
         → (∀ n → IH (just n) ρ (defer l)) → IH nothing ρ (defer l)
held-lim ρ l hs = ih (λ env cs g eh p ok fr ep →
  LimHeld.held (enter (⟦ elab ρ (defer l) ⟧ env) p) (λ n → enter (approx n (elab ρ (defer l)) env) p) (p ∷ cs)
    (lim-row ρ l env p)
    (λ fw → let (N , ag) = reached (elab ρ (defer l)) env g p ok fw in N , ag N ℕP.≤-refl)
    (λ n → IH.holds (hs n) env cs g eh p ok fr ep) (lim-rest ρ l hs env cs g eh p ok ep))
  λ env cs g eh p ok fr ep x sh → let (N , h) = lim-row ρ l env p x in IH.placed (hs N) env cs g eh p ok fr ep h sh

held-⊥ : ∀ {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (l : Later Timeline Γ A) → IH (just zero) ρ (defer l)
held-⊥ ρ l = ih (λ env cs g eh p ok fr ep → Quiet.held _ p cs ep (λ { (spin _ , _) () }) λ { (() , _) })
  λ { env cs g eh p ok fr ep (spin _ , _) () }

held-next : ∀ n {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (l : Later Timeline Γ A)
          → IH (just n) ρ (Later.force l) → IH (just (suc n)) ρ (defer l)
held-next n ρ l (ih h pl) = ih
  (λ env cs g eh p ok fr ep →
    held-defer (approx n (elab ρ (Later.force l)) env) p cs (h env cs g eh (p ⊕ [ ix 1 ]) (ok-step p ok) (Adm.step (fresh-adm eh) ok fr plain-ix) (early-inst [ ix 1 ] ep)))
  λ env cs g eh p ok fr ep →
    placed-defer (approx n (elab ρ (Later.force l)) env) p (pl env cs g eh (p ⊕ [ ix 1 ]) (ok-step p ok) (Adm.step (fresh-adm eh) ok fr plain-ix) (early-inst [ ix 1 ] ep))

held-approx : ∀ n {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (o : Obs Timeline Γ A) → IH (just n) ρ o
held-approx n       ρ (cold c)          = held-cold (just n) ρ c
held-approx n       ρ empty             = held-empty (just n) ρ
held-approx n       ρ (of xs)           = held-of (just n) ρ xs
held-approx n       ρ (map f s)         = held-map (just n) ρ f s (held-approx n ρ s)
held-approx n       ρ (scan f z s)      = held-scan (just n) ρ f z s (held-approx n ρ s)
held-approx n       ρ (takeWhile i p s) = held-takeWhile (just n) ρ i p s (held-approx n ρ s)
held-approx n       ρ (flatMap op f s)  = held-flatMap (just n) ρ op f s (λ ρ′ → held-approx n ρ′ s) λ a ρ′ → held-approx n ρ′ (f a)
held-approx n       ρ (connect s b)     = held-connect (just n) ρ s b (held-approx n ρ s) λ ρ′ → held-approx n ρ′ b
held-approx n       ρ (connected i)     = held-connected (just n) ρ i
held-approx zero    ρ (defer l)         = held-⊥ ρ l
held-approx (suc n) ρ (defer l)         = held-next n ρ l (held-approx n ρ (Later.force l))

held-⟦⟧ : ∀ {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (o : Obs Timeline Γ A) → IH nothing ρ o
held-⟦⟧ ρ (cold c)          = held-cold nothing ρ c
held-⟦⟧ ρ empty             = held-empty nothing ρ
held-⟦⟧ ρ (of xs)           = held-of nothing ρ xs
held-⟦⟧ ρ (map f s)         = held-map nothing ρ f s (held-⟦⟧ ρ s)
held-⟦⟧ ρ (scan f z s)      = held-scan nothing ρ f z s (held-⟦⟧ ρ s)
held-⟦⟧ ρ (takeWhile i p s) = held-takeWhile nothing ρ i p s (held-⟦⟧ ρ s)
held-⟦⟧ ρ (flatMap op f s)  = held-flatMap nothing ρ op f s (λ ρ′ → held-⟦⟧ ρ′ s) λ a ρ′ → held-⟦⟧ ρ′ (f a)
held-⟦⟧ ρ (connect s b)     = held-connect nothing ρ s b (held-⟦⟧ ρ s) λ ρ′ → held-⟦⟧ ρ′ b
held-⟦⟧ ρ (connected i)     = held-connected nothing ρ i
held-⟦⟧ ρ (defer l)         = held-lim ρ l λ n → held-approx n ρ (defer l)

------------------------------------------------------------------------
-- The top

-- The restamp renames only what no count reads: a begin keeps its own.
same-restamp : ∀ {A} → Relabels (restamp {A})
same-restamp st (instEmit (value _) _)        = same-value
same-restamp st (instEmit (mark begin) _)      = same-mark (λ _ → refl)
same-restamp st (instEmit (mark stop) _)       = same-mark λ ()
same-restamp st (instEmit (mark over) _)       = same-mark λ ()
same-restamp st (instEmit (mark outerOpen) _)  = same-mark λ ()
same-restamp st (instEmit (mark outerClose) _) = same-mark λ ()
same-restamp st (instEmit (mark laneStart) _)  = same-mark λ ()
same-restamp st (instEmit (mark carry) _)      = same-mark λ ()
same-restamp st (instEmit (mark laneDone) _)   = same-mark λ ()
same-restamp st (instEmit (mark burstEnd) _)   = same-mark λ ()
same-restamp st (instEmit (mark outerDone) _)  = same-mark λ ()
same-restamp st (instEmit (mark subscribed) _) = same-mark λ ()
same-restamp st (instEmit (mark completed) _)  = same-mark λ ()

-- THE BATCHER'S SOURCE HOLDS: the wrapped program, restamped.
held-top : ∀ {A} (o : SObs [] A) → IH nothing (λ i → i) (plain o) → Held (elaborated o) (root ∷ [])
held-top o hy = held-scan-at restamp same-restamp (root , marked begin) (⟦ wrapped s ⟧ []ᵉ) root
  (held-wrapped s tt (IH.holds hy []ᵉ [] (λ ()) record { bound = λ () ; apart = λ () }))
  where
    s = elab (λ i → i) (plain o)

-- Opaque: a consumer projects its fields, and a `with` on one would
-- otherwise unfold the whole induction.
opaque
  held : ∀ {A} (o : SObs [] A) → Held (elaborated o) (root ∷ [])
  held o = held-top o (held-⟦⟧ (λ i → i) (plain o))

-- The elaborated program's instants stay dead.
shut : ∀ {A : Set} (o : SObs [] A) → Shut (elaborated o)
shut o = Held.shut (held o)
