{-# OPTIONS --guardedness #-}

-- THE MACHINE'S RECORD: honest to the meaning's events, so every
-- prefix's record alike them as a set.  Each step's showing is
-- `adequacy.Content`'s.
module adequacy.Content.Log where

open import Data.Bool using (true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; [_]; length; map)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.Any.Properties using (++⁺ʳ; ++⁻)
open import Data.List.Relation.Unary.All using ([]; _∷_)
import Data.List.Relation.Unary.Any as Any
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Nat using (ℕ; zero; suc; _<ᵇ_)
open import Data.Nat.Properties using (suc-injective)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import denotation.MonotonicList.Events using (Timeline; Events; Events∞; Pos; Time; tick; root; out; end; hush; ix; _<ᵖ_; <ᵖ-irrefl;
  <ᵖ-asym; emit; stall; close; last; Frame∞; From; From∞; idle; done; at; _∪_) renaming (quiet to silentᶠ)
open import denotation.MonotonicList using (observe; _≈[_]_)
open import adequacy.Record using (Ahead; outᵃ; skipᵃ; endᵃ; hushᵃ) renaming (none to noneᵃ)
import denotation.Unfold as U
open import denotation.Denote using (⟦_⟧)
open import operation.PureObservable using (PureObs; module Driver; module Machine; module Pure; play; ending; over) renaming (rest to restᵀ)
open import adequacy.Sorted using (_≤ᵖ_)
open import adequacy.Unsub using (module Unsubbing)
open import adequacy.Ghost using (module Ghosting)
open import adequacy.Engine.Meaning using (Has)
open import adequacy.Engine.Spent using (module Spending)
open import adequacy.Engine.Kept using (KeptFrom; refocus-agree; rests-++; lanes-runs; pool-runs; dead-hole) renaming (kept to engine-kept)
open import adequacy.Engine.Head using (Frag; Lane) renaming (Lanes to Lanesᴴ)
open import adequacy.Engine.Ahead using (Sides; shows; shows-open; ahead-mono) renaming (Ahead to Aheadᶠ)
open import adequacy.Strong using (module Strongly)
open import adequacy.Content using (module Honesty)
open Events∞ using (force)

module HonestLog (R : Set) where
  open Driver R using (Step; silent; value; complete; drained; step; reading; Read; read; later; played; took)
  open Machine using (Conf; ⟨_,_,_,_⟩; load; moved; starting; turn; quiet; gone; leaf; nx; cp; St; pend; coldS; Ctx; top; inOuter; inLanes;
    plug; closed; alive; search; found; leafM; still; subscribing; absorbed; rising; _⊕_; inCut; inLn; attAt; flatS; killAll; lnS; cutS) renaming (step to stepᴹ; ended to endedˢ)
  open Spending R using (Skipped; outerᵏ; laneᵏ; deferᵏ; stallᵏ; closeᵏ; silent-spent)
  open Pure R using (End; finished; dry; cutOff)
  open Unsubbing R using (_⇝_; now; then)
  open Ghosting R using (Sent; sentHere; sentLater; Alike; residual; Reached; launchedʰ; silentʰ; valueʰ;
    Stands; cutʰ; finʰ; dryʰ; Mirror; Inner; Logged; Shows; silentˢ; valueˢ; completeˢ; drainedˢ; inner-launch;
    Steps; after; steps-after; Hopped; onward; Past; past-same; agrees; skipped; lowered; Lowers; depth; ahead-agree; work; _≺_)
  open Strongly R using (Strong; Carried; module Carried; Agrees; module Agrees; Leads; shown; skips; carried; carried-sane)
  open Honesty R using (inner-next)

  -- THE MACHINE HONEST TO `e`: what its record has is among `e`, and
  -- what of `e` it has not lies in `rest`, past every mark, which the
  -- configuration will deliver.
  record HonMach (e : Events R) (qs : List Pos) (xs : List (Time × R)) (m : Conf R) : Set₁ where
    field
      rest   : Events R
      logged : ∀ {k a} → Sent qs xs k a → Has e k (just a)
      split  : ∀ {k b} → Has e k b → Logged qs xs k b ⊎ Has rest k b
      past   : ∀ {k b} → Has rest k b → Any (k ≤ᵖ_) qs → ⊥
      paired : length qs ≡ length xs
      within : ∀ {k b} → Has rest k b → Has e k b
      inner  : Inner rest m

  -- A completion is the events' end, the residual holding no value.
  ends : ∀ {e qs xs m p} (h : HonMach e qs xs m) → step m ≡ complete p → Has e p nothing × (∀ {k a} → Has (HonMach.rest h) k (just a) → ⊥)
  ends h eq with subst (Shows (HonMach.rest h)) eq (inner-next (HonMach.inner h))
  ... | completeˢ x none = HonMach.within h x , none

  -- A drained run has delivered all of it.
  dries : ∀ {e qs xs m} (h : HonMach e qs xs m) → step m ≡ drained → ∀ {k b} → Has (HonMach.rest h) k b → ⊥
  dries h eq with subst (Shows (HonMach.rest h)) eq (inner-next (HonMach.inner h))
  ... | drainedˢ none = none

  -- A launch is honest to the meaning's events at the root, all of them
  -- still owed.
  honest-launch : (o : PureObs [] R) → HonMach (observe (⟦ o ⟧ []) root) [] [] (load o)
  honest-launch o = record
    { rest = observe (⟦ o ⟧ []) root ; logged = λ () ; split = inj₂ ; past = λ _ () ; paired = refl ; within = λ x → x ; inner = inner-launch o }

  -- A value sent is at one of the record's marks.
  sent-mark : ∀ {qs xs k a} → Sent qs xs k a → Any (k ≡_) qs
  sent-mark sentHere      = here refl
  sent-mark (sentLater s) = there (sent-mark s)

  -- Marks past the record's end send nothing more, and lose nothing.
  sent-++ : ∀ {qs xs k a} ys → Sent qs xs k a → Sent (qs ++ ys) xs k a
  sent-++ ys sentHere      = sentHere
  sent-++ ys (sentLater s) = sentLater (sent-++ ys s)

  sent-cut : ∀ {qs xs ys k a} → length qs ≡ length xs → Sent (qs ++ ys) xs k a → Sent qs xs k a
  sent-cut {[]}    {[]}    eq ()
  sent-cut {_ ∷ _} {_ ∷ _} eq sentHere      = sentHere
  sent-cut {_ ∷ qs} {_ ∷ xs} eq (sentLater s) = sentLater (sent-cut {qs} {xs} (suc-injective eq) s)

  -- An honest machine's record is alike its events, however it stands.
  honest-alike : ∀ {e qs xs m en qs′} → HonMach e qs xs m → Stands m qs en qs′ → Alike en qs′ xs e
  honest-alike h cutʰ = record
    { sound = logged
    ; whole = λ x ow → [ (λ s → s) , (λ r → ⊥-elim (past r ow)) ]′ (split x)
    ; ended = tt
    }
    where open HonMach h
  honest-alike {qs = qs} {xs} h (finʰ {p} eq) = record
    { sound = λ s → logged (sent-cut {qs} {xs} paired s)
    ; whole = λ x _ → [ sent-++ [ p ] , (λ r → ⊥-elim (proj₂ (ends h eq) r)) ]′ (split x)
    ; ended = p , proj₁ (ends h eq) , ++⁺ʳ qs (here refl)
    }
    where open HonMach h
  honest-alike h (dryʰ eq) = record
    { sound = logged
    ; whole = λ x _ → [ (λ s → s) , (λ r → ⊥-elim (dries h eq r)) ]′ (split x)
    ; ended = ended
    }
    where
    open HonMach h
    ended : ∀ {k b} → Has _ k b → Any (k ≤ᵖ_) _
    ended {b = just a}  x with split x
    ... | inj₁ s = Any.map inj₁ (sent-mark s)
    ... | inj₂ r = ⊥-elim (dries h eq r)
    ended {b = nothing} x with split x
    ... | inj₁ ()
    ... | inj₂ r = ⊥-elim (dries h eq r)

  -- The record grown by one entry keeps what it sent, and sends the new
  -- entry at its mark.
  sent-snoc-keep : ∀ {qs xs ys zs k a} → Sent qs xs k a → Sent (qs ++ ys) (xs ++ zs) k a
  sent-snoc-keep sentHere      = sentHere
  sent-snoc-keep (sentLater s) = sentLater (sent-snoc-keep s)

  logged-snoc : ∀ {qs xs ys zs k b} → Logged qs xs k b → Logged (qs ++ ys) (xs ++ zs) k b
  logged-snoc {b = just a} s = sent-snoc-keep s

  sent-last : ∀ {qs xs q a} → length qs ≡ length xs → Sent (qs ++ [ q ]) (xs ++ [ (tick q , a) ]) q a
  sent-last {[]}     {[]}     eq = sentHere
  sent-last {_ ∷ qs} {_ ∷ xs} eq = sentLater (sent-last {qs} {xs} (suc-injective eq))

  sent-snoc : ∀ {qs xs q x k a} → length qs ≡ length xs → Sent (qs ++ [ q ]) (xs ++ [ x ]) k a → Sent qs xs k a ⊎ (k ≡ q × x ≡ (tick k , a))
  sent-snoc {[]}    {[]}    eq sentHere      = inj₂ (refl , refl)
  sent-snoc {[]}    {[]}    eq (sentLater ())
  sent-snoc {_ ∷ _} {_ ∷ _} eq sentHere      = inj₁ sentHere
  sent-snoc {_ ∷ qs} {_ ∷ xs} eq (sentLater s) = [ (λ s′ → inj₁ (sentLater s′)) , inj₂ ]′ (sent-snoc {qs} {xs} (suc-injective eq) s)

  snoc-length : ∀ {A B : Set} {qs : List A} {xs : List B} {q x} → length qs ≡ length xs → length (qs ++ [ q ]) ≡ length (xs ++ [ x ])
  snoc-length {qs = []}    {[]}    eq = refl
  snoc-length {qs = _ ∷ qs} {_ ∷ xs} eq = cong suc (snoc-length {qs = qs} {xs} (suc-injective eq))

  -- One step keeps the machine honest: a silent one keeps its record
  -- and its residual; a value moves the residual's lead into the record.
  honest-step : ∀ {e qs xs m t m′} → HonMach e qs xs m → step m ≡ silent t m′ → HonMach e qs xs m′
  honest-step h eq with subst (Shows (HonMach.rest h)) eq (inner-next (HonMach.inner h))
  ... | silentˢ i = record { rest = rest ; logged = logged ; split = split ; past = past ; paired = paired ; within = within ; inner = i }
    where open HonMach h

  private
    honest-value : ∀ {e qs xs m t p a m′} → HonMach e qs xs m → step m ≡ value t p a m′ → HonMach e (qs ++ [ p ]) (xs ++ [ (t , a) ]) m′
    honest-value {e} {qs} {xs} {m} {t} {p} {a} h eq with subst (Shows (HonMach.rest h)) eq (inner-next (HonMach.inner h))
    ... | valueˢ {r = r′} tp x₀ sub sp beyond i = record
      { rest   = r′
      ; logged = logged′
      ; split  = split′
      ; past   = past′
      ; paired = snoc-length {qs = qs} {xs} paired
      ; within = λ x → within (sub x)
      ; inner  = i
      }
      where
      open HonMach h
      logged′ : ∀ {k a′} → Sent (qs ++ [ p ]) (xs ++ [ (t , a) ]) k a′ → Has e k (just a′)
      logged′ s with sent-snoc {qs} {xs} paired s
      ... | inj₁ s′       = logged s′
      ... | inj₂ (kp , x) = subst₂ (λ k a′ → Has e k (just a′)) (sym kp) (cong proj₂ x) (within x₀)
      split′ : ∀ {k b} → Has e k b → Logged (qs ++ [ p ]) (xs ++ [ (t , a) ]) k b ⊎ Has r′ k b
      split′ x with split x
      ... | inj₁ lg = inj₁ (logged-snoc lg)
      ... | inj₂ y with sp y
      ...   | inj₂ y′       = inj₂ y′
      ...   | inj₁ (kp , ba) = inj₁ (subst₂ (λ k b → Logged (qs ++ [ p ]) (xs ++ [ (t , a) ]) k b) (sym kp) (sym ba)
                                      (subst (λ t′ → Sent (qs ++ [ p ]) (xs ++ [ (t′ , a) ]) p a) (sym tp) (sent-last {qs} {xs} paired)))
      past′ : ∀ {k b} → Has r′ k b → Any (k ≤ᵖ_) (qs ++ [ p ]) → ⊥
      past′ x ow with ++⁻ qs ow
      ... | inj₁ o          = past (sub x) o
      ... | inj₂ (here kp)  = beyond x kp
      ... | inj₂ (there ())

  -- Every configuration reached from a launch is honest.
  honest : ∀ {e qs xs m} → Reached e qs xs m → HonMach e qs xs m
  honest (launchedʰ o refl) = honest-launch o
  honest (silentʰ r eq)     = honest-step (honest r) eq
  honest (valueʰ r eq)      = honest-value (honest r) eq

  -- THE MACHINE'S CONTENT: a configuration reached from a launch keeps
  -- a record alike its meaning's events, however it stands.
  kept : ∀ {e qs xs m en qs′} → Reached e qs xs m → Stands m qs en qs′ → Alike en qs′ xs e
  kept r = honest-alike (honest r)

  -- What a reader of the run from a reached configuration has, put after
  -- that configuration's record, is the record of one reached from it,
  -- standing as the reader's run stands.
  Onward : Events R → List Pos → List (Time × R) → Read → Set₁
  Onward e qs xs x = Σ (Conf R) λ m′ → Σ (List Pos) λ qs₁ → Σ (List (Time × R)) λ xs′ → Σ (Reached e qs₁ xs′ m′) λ _ → Σ End λ en
                   → Σ (List Pos) λ qs′ → Stands m′ qs₁ en qs′ × read (qs ++ Read.marks x) (xs ++ Read.log x) (Read.endedAs x) ≡ read qs′ xs′ en

  -- Read to tick `h`: a step past it cuts the record where it stands.
  read-on : ∀ {e qs xs m} → Reached e qs xs m → ∀ h n c → Onward e qs xs (reading h n c m)
  read-on {qs = qs} {xs} {m} r h zero    c = m , qs , xs , r , _ , _ , cutʰ , cong₂ (λ ms ls → read ms ls _) (++-identityʳ qs) (++-identityʳ xs)
  read-on {qs = qs} {xs} {m} r h (suc n) c with step m in eq
  ... | silent t m₁ with h <ᵇ t
  ...   | true  = m , qs , xs , r , _ , _ , cutʰ , cong₂ (λ ms ls → read ms ls _) (++-identityʳ qs) (++-identityʳ xs)
  ...   | false = read-on (silentʰ r eq) h n _
  read-on {qs = qs} {xs} {m} r h (suc n) c | value t p a m₁ with h <ᵇ t
  ...   | true  = m , qs , xs , r , _ , _ , cutʰ , cong₂ (λ ms ls → read ms ls _) (++-identityʳ qs) (++-identityʳ xs)
  ...   | false with read-on (valueʰ r eq) h n t
  ...     | m′ , qs₁ , xs′ , r′ , en , qs′ , st , x = m′ , qs₁ , xs′ , r′ , en , qs′ , st ,
              trans (cong₂ (λ ms ls → read ms ls _) (sym (++-assoc qs [ p ] _)) (sym (++-assoc xs [ (t , a) ] _))) x
  read-on {qs = qs} {xs} {m} r h (suc n) c | complete p = m , qs , xs , r , finished , _ , finʰ eq , cong (λ ls → read _ ls finished) (++-identityʳ xs)
  read-on {qs = qs} {xs} {m} r h (suc n) c | drained    = m , qs , xs , r , dry , _ , dryʰ eq , cong₂ (λ ms ls → read ms ls dry) (++-identityʳ qs) (++-identityʳ xs)

  -- The launch's first n steps, read to tick h, are the record of a
  -- configuration reached from it.
  read-is-kept : (o : PureObs [] R) (n h : ℕ) → Σ (Conf R) λ m′ → Σ (List Pos) λ qs₁ → Σ (List (Time × R)) λ xs′
               → Σ (Reached (observe (⟦ o ⟧ []) root) qs₁ xs′ m′) λ _ → Σ End λ en
               → Σ (List Pos) λ qs → Stands m′ qs₁ en qs × reading h n 0 (load o) ≡ read qs xs′ en
  read-is-kept o n h = read-on (launchedʰ o refl) h n 0

  -- CONTENT: every prefix's record alike the meaning's events as a set.
  content : (o : PureObs [] R) (n h : ℕ) → let x = reading h n 0 (load o) in Alike (Read.endedAs x) (Read.marks x) (Read.log x) (observe (⟦ o ⟧ []) root)
  content o n h with read-is-kept o n h
  ... | m′ , qs₁ , xs′ , r′ , en , qs , st , eq rewrite eq = kept r′ st
