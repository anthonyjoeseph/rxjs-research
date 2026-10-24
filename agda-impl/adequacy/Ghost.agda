{-# OPTIONS --guardedness #-}

-- THE GHOST: the meaning's configuration a machine's run carries
-- (`Strong`), what is left of it to deliver (`residual`), and the
-- work a silent run between two such configurations lowers (`Lowers`).
--
-- The machine keeps no record: a configuration reached from a launch is
-- reached WITH the record its steps showed (`Reached`).
module adequacy.Ghost where

open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Relation.Unary.Any using (Any)
open import Data.List.Relation.Unary.All using ([])
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat.Properties using (≤-reflexive; ≤-trans; m≤n⇒m≤1+n; <-trans)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _<_; _≤_; z≤n)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (WellFounded)
open import Data.Product.Relation.Binary.Lex.Strict using (×-Lex; ×-wellFounded)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import denotation.MonotonicList.Events using (Events; Events∞; Pos; Time; tick; out; skip; end; hush; root)
open import denotation.MonotonicList using (observe; Agree; out⁼; skip⁼; end⁼; hush⁼; agree; agree-sym)
import denotation.Unfold as U
open import adequacy.Record using (Ahead; none; outᵃ; skipᵃ; endᵃ; hushᵃ)
open import denotation.Compositional using ([]ᵉ)
open import adequacy.Sorted using (_≤ᵖ_)
open import adequacy.Unsub using (module Unsubbing)
open import adequacy.Strong using (module Strongly)
open import adequacy.Stepper.Past using (afterᴱ)
open import adequacy.Engine.Work using (owedᶜ; calmᶜ; flightᶜ; tornᶜ)
open import adequacy.Engine.Meaning using (M; Has; atOut; atEnd; pastOut; pastSkip; _≅_; ≅-trans; agree-≅)
open import denotation.Denote using (⟦_⟧)
open import operation.PureObservable using (PureObs; module Driver; module Machine; module Pure)
open Events∞

module Ghosting (R : Set) where
  open Driver R using (Step; silent; value; complete; drained; step)
  open Machine using (Conf; load)
  open Pure R using (End; finished; dry; cutOff)
  open Unsubbing R using (_⇝_; now)
  open Strongly R using (Strong; strong-begin)

  ----------------------------------------------------------------------
  -- Alike as sets

  -- The record has sent `a` at `k`, on `k`'s tick.
  data Sent : List Pos → List (Time × R) → Pos → R → Set where
    sentHere  : ∀ {k a qs xs} → Sent (k ∷ qs) ((tick k , a) ∷ xs) k a
    sentLater : ∀ {k a q x qs xs} → Sent qs xs k a → Sent (q ∷ qs) (x ∷ xs) k a

  -- What the record owes: a cut record only what lies at or before one
  -- of its marks; an ended or silent one everything.
  Owed : End → List Pos → Pos → Set
  Owed (cutOff _) qs k = Any (k ≤ᵖ_) qs
  Owed _          qs k = ⊤

  -- How each end is matched: finished at the events' `end`, its mark
  -- among the record's; dry over events with nothing past the marks;
  -- cut owes nothing.
  Ending : End → List Pos → Events R → Set
  Ending finished   qs e = Σ Pos λ q → Has e q nothing × Any (q ≡_) qs
  Ending dry        qs e = ∀ {k b} → Has e k b → Any (k ≤ᵖ_) qs
  Ending (cutOff _) qs e = ⊤

  -- The record and the events alike as sets: every value sent is an
  -- event at its mark; every event owed was sent; the record ends as the
  -- events do.
  record Alike (en : End) (qs : List Pos) (xs : List (Time × R)) (e : Events R) : Set where
    field
      sound : ∀ {k a} → Sent qs xs k a → Has e k (just a)
      whole : ∀ {k a} → Has e k (just a) → Owed en qs k → Sent qs xs k a
      ended : Ending en qs e

  -- Alike at every depth.
  tail-out : ∀ {n k} {a : R} {l r} → Agree (suc n) (out k a l) (out k a r) → Agree n (force l) (force r)
  tail-out (out⁼ _ x) = x

  tail-skip : ∀ {n k} {l r : Events∞ R} → Agree (suc n) (skip k l) (skip k r) → Agree n (force l) (force r)
  tail-skip (skip⁼ _ x) = x

  ----------------------------------------------------------------------
  -- THE GHOST

  -- What a configuration of the meaning will show.
  residual : U.Node [] R → Events R
  residual g = U.meaning g []

  -- The program subscribed at the root shows the meaning's events.
  begun : (o : PureObs [] R) → ∀ n → Agree n (observe (⟦ o ⟧ []) root) (residual (U.subscribe o root))
  begun o n = agree-sym (agree (U.subscribed {k = n} o []ᵉ) root)

  ----------------------------------------------------------------------
  -- THE ASSEMBLY: from a launch to an alike record

  -- A configuration reached from a program's launch by the machine's own
  -- steps, with the record they showed: each value at its mark.
  data Reached (e : Events R) : List Pos → List (Time × R) → Conf R → Set₁ where
    launchedʰ : (o : PureObs [] R) → e ≡ observe (⟦ o ⟧ []) root → Reached e [] [] (load o)
    silentʰ   : ∀ {qs xs m m′ t} → Reached e qs xs m → step m ≡ silent t m′ → Reached e qs xs m′
    valueʰ    : ∀ {qs xs m m′ t p a} → Reached e qs xs m → step m ≡ value t p a m′ → Reached e (qs ++ [ p ]) (xs ++ [ (t , a) ]) m′

  -- How a configuration's record, marked `qs`, stands: cut, at whatever
  -- clock, or the run drained there; or complete there, its completion
  -- marked last.
  data Stands (m : Conf R) (qs : List Pos) : End → List Pos → Set₁ where
    cutʰ  : ∀ {c} → Stands m qs (cutOff c) qs
    finʰ  : ∀ {p} → step m ≡ complete p → Stands m qs finished (qs ++ [ p ])
    dryʰ  : step m ≡ drained → Stands m qs dry qs

  -- THE CONFIGURATION RUNS THE GHOST: it runs silently to a re-entry
  -- configuration against it.  No intermediate configuration is related
  -- to the ghost but by the steps the machine takes from it.
  Mirror : U.Node [] R → Conf R → Set₁
  Mirror g m = Σ (Conf R) λ m₀ → m ⇝ m₀ × Strong g m₀

  -- THE CONFIGURATION WILL DELIVER `rest`: it runs a ghost whose
  -- residual `rest` is, as a set.
  record Inner (rest : Events R) (m : Conf R) : Set₁ where
    field
      ghost  : U.Node [] R
      same   : rest ≅ residual ghost
      mirror : Mirror ghost m

  -- The record holds a value at `k`; it never holds an end.
  Logged : List Pos → List (Time × R) → Pos → Maybe R → Set
  Logged qs xs k (just a) = Sent qs xs k a
  Logged qs xs k nothing  = ⊥

  -- What a step shows of the residual, as a set: a silent step keeps
  -- it; a value at its tick is in it, and leaves the rest of it, all past
  -- the value; a completion is its end, no value left in it; a drained
  -- run leaves nothing of it.
  data Shows (rest : Events R) : Step → Set₁ where
    silentˢ   : ∀ {t m′} → Inner rest m′ → Shows rest (silent t m′)
    valueˢ    : ∀ {t p a m′ r} → t ≡ tick p → Has rest p (just a)
              → (∀ {k b} → Has r k b → Has rest k b) → (∀ {k b} → Has rest k b → (k ≡ p × b ≡ just a) ⊎ Has r k b)
              → (∀ {k b} → Has r k b → k ≤ᵖ p → ⊥) → Inner r m′
              → Shows rest (value t p a m′)
    completeˢ : ∀ {p} → Has rest p nothing → (∀ {k a} → Has rest k (just a) → ⊥) → Shows rest (complete p)
    drainedˢ  : (∀ {k b} → Has rest k b → ⊥) → Shows rest drained

  -- The launch will deliver the meaning's events.
  inner-launch : (o : PureObs [] R) → Inner (observe (⟦ o ⟧ []) root) (load o)
  inner-launch o = record { ghost = U.subscribe o root ; same = agree-≅ (begun o) ; mirror = load o , now , strong-begin o }

  -- WHAT THE GHOST'S STEP SAYS OF ITS RESIDUAL, as a set: a value is in
  -- it, and the rest is what the stepped ghost shows; a skip keeps it; an
  -- end is all of it but the end; a hush leaves nothing.
  Steps : Events R → U.Step [] R → Set
  Steps e (U.outˢ k a g′) = Has e k (just a) × (∀ {q b} → Has (residual g′) q b → Has e q b)
                          × (∀ {q b} → Has e q b → (q ≡ k × b ≡ just a) ⊎ Has (residual g′) q b)
  Steps e (U.skipˢ k g′)  = e ≅ residual g′
  Steps e (U.endˢ k)      = Has e k nothing × (∀ {q a} → Has e q (just a) → ⊥)
  Steps e U.hushˢ         = ∀ {q b} → Has e q b → ⊥

  -- What a step shows, then the residual of the ghost it leaves.
  after : U.Step [] R → Events R
  after = afterᴱ []

  -- Events alike, as a set, with what a step shows are what it says.
  steps-after : ∀ {e} s → e ≅ after s → Steps e s
  steps-after (U.outˢ k a g′) eq = proj₂ eq atOut , (λ h → proj₂ eq (pastOut h)) , λ h → split (proj₁ eq h)
    where split : ∀ {q b} → Has (after (U.outˢ k a g′)) q b → (q ≡ k × b ≡ just a) ⊎ Has (residual g′) q b
          split atOut       = inj₁ (refl , refl)
          split (pastOut h) = inj₂ h
  steps-after (U.skipˢ k g′)  eq = (λ h → past (proj₁ eq h)) , λ h → proj₂ eq (pastSkip h)
    where past : ∀ {q b} → Has (after (U.skipˢ k g′)) q b → Has (residual g′) q b
          past (pastSkip h) = h
  steps-after (U.endˢ k)      eq = proj₂ eq atEnd , λ h → no (proj₁ eq h)
    where no : ∀ {q a} → Has (end k) q (just a) → ⊥
          no ()
  steps-after U.hushˢ         eq = λ h → no (proj₁ eq h)
    where no : ∀ {q b} → Has hush q b → ⊥
          no ()

  -- How far into the events an item lies.
  depth : ∀ {e : Events R} {k} → Ahead e k → ℕ
  depth none      = 0
  depth (outᵃ a)  = suc (depth a)
  depth (skipᵃ a) = suc (depth a)
  depth endᵃ      = 0
  depth hushᵃ     = 0

  ahead-agree : ∀ {x y k} → (∀ n → Agree n x y) → (a : Ahead x k) → Σ (Ahead y k) λ b → depth b ≡ depth a
  ahead-agree ag none = none , refl
  ahead-agree ag (outᵃ a) with ag 1
  ... | out⁼ _ _ with ahead-agree (λ n → tail-out (ag (suc n))) a
  ...   | b , eq = outᵃ b , cong suc eq
  ahead-agree ag (skipᵃ a) with ag 1
  ... | skip⁼ _ _ with ahead-agree (λ n → tail-skip (ag (suc n))) a
  ...   | b , eq = skipᵃ b , cong suc eq
  ahead-agree ag endᵃ with ag 1
  ... | end⁼ = endᵃ , refl
  ahead-agree ag hushᵃ with ag 1
  ... | hush⁼ = hushᵃ , refl

  -- Every item `x` reaches, `y` reaches no deeper.
  Fewer : Events R → Events R → Set
  Fewer x y = ∀ {k} (a : Ahead x k) → Σ (Ahead y k) λ b → depth b ≤ depth a

  -- `y` is `x` with none or more of its skips gone.  As sets the two are
  -- the same; as a measure a skip dropped is progress, which `≅` cannot
  -- see.
  record Past (x y : Events R) : Set where
    field
      same  : x ≅ y
      fewer : Fewer x y

  skip-same : ∀ {k} {r : Events∞ R} → skip k r ≅ force r
  skip-same = (λ { (pastSkip h) → h }) , pastSkip

  past-same : ∀ {x y} → Past x y → x ≅ y
  past-same = Past.same

  agrees : ∀ {x y} → (∀ n → Agree n x y) → Past x y
  agrees ag = record { same = agree-≅ ag ; fewer = λ a → proj₁ (ahead-agree ag a) , ≤-reflexive (proj₂ (ahead-agree ag a)) }

  skipped : ∀ {x y k r} → (∀ n → Agree n x (skip k r)) → Past (force r) y → Past x y
  skipped {x} {y} {k} {r} ag p = record { same = ≅-trans (agree-≅ ag) (≅-trans skip-same (Past.same p)) ; fewer = fewer }
    where fewer : Fewer x y
          fewer a with ahead-agree ag a
          ... | none     , _  = none , z≤n
          ... | skipᵃ a′ , de with Past.fewer p a′
          ...   | b , le = b , ≤-trans (m≤n⇒m≤1+n le) (≤-reflexive de)

  past-pre : ∀ {x y z} → (∀ n → Agree n x y) → Past y z → Past x z
  past-pre {x} {y} {z} ag p = record { same = ≅-trans (agree-≅ ag) (Past.same p) ; fewer = fewer }
    where fewer : Fewer x z
          fewer a with ahead-agree ag a
          ... | b , de with Past.fewer p b
          ...   | c , le = c , ≤-trans le (≤-reflexive de)

  ----------------------------------------------------------------------
  -- WHAT IS LEFT BEFORE THE GHOST MOVES

  -- The work left at a re-entry configuration, five counts in order of
  -- precedence, then the control's own.
  Load : Set
  Load = ℕ × ℕ × ℕ × ℕ × ℕ

  _⊏_ : Load → Load → Set
  _⊏_ = ×-Lex _≡_ _<_ (×-Lex _≡_ _<_ (×-Lex _≡_ _<_ (×-Lex _≡_ _<_ _<_)))

  _≼_ : Load → Load → Set
  a ≼ b = a ≡ b ⊎ a ⊏ b

  lex-trans : ∀ {B : Set} {_<₂_ : B → B → Set} → (∀ {x y z} → x <₂ y → y <₂ z → x <₂ z)
            → ∀ {a b c : ℕ × B} → ×-Lex _≡_ _<_ _<₂_ a b → ×-Lex _≡_ _<_ _<₂_ b c → ×-Lex _≡_ _<_ _<₂_ a c
  lex-trans t (inj₁ ab)          (inj₁ bc)          = inj₁ (<-trans ab bc)
  lex-trans t (inj₁ ab)          (inj₂ (refl , _))  = inj₁ ab
  lex-trans t (inj₂ (refl , _))  (inj₁ bc)          = inj₁ bc
  lex-trans t (inj₂ (refl , ab)) (inj₂ (refl , bc)) = inj₂ (refl , t ab bc)

  ⊏-trans : ∀ {a b c} → a ⊏ b → b ⊏ c → a ⊏ c
  ⊏-trans = lex-trans {_<₂_ = ×-Lex _≡_ _<_ (×-Lex _≡_ _<_ (×-Lex _≡_ _<_ _<_))}
              (lex-trans {_<₂_ = ×-Lex _≡_ _<_ (×-Lex _≡_ _<_ _<_)}
                (lex-trans {_<₂_ = ×-Lex _≡_ _<_ _<_} (lex-trans {_<₂_ = _<_} <-trans)))

  ≼-trans : ∀ {a b c} → a ≼ b → b ≼ c → a ≼ c
  ≼-trans (inj₁ refl) bc          = bc
  ≼-trans (inj₂ ab)   (inj₁ refl) = inj₂ ab
  ≼-trans (inj₂ ab)   (inj₂ bc)   = inj₂ (⊏-trans ab bc)

  Measure : Set
  Measure = Load × ℕ

  _≺_ : Measure → Measure → Set
  _≺_ = ×-Lex _≡_ _⊏_ _<_

  ≺-wf : WellFounded _≺_
  ≺-wf = ×-wellFounded (×-wellFounded <-wellFounded (×-wellFounded <-wellFounded (×-wellFounded <-wellFounded
           (×-wellFounded <-wellFounded <-wellFounded)))) <-wellFounded

  -- The work a configuration has left in its own control: what its tree
  -- owes, an event in flight included; then whether it is calm; then how
  -- far its event in flight has to rise; then the teardowns it owes.
  work : Conf R → Measure
  work m = (owedᶜ m , calmᶜ m , flightᶜ m , tornᶜ m , 0) , 0

  -- Toward an item: the item's depth, then the configuration's work.
  _⋖_ : ℕ × Measure → ℕ × Measure → Set
  _⋖_ = ×-Lex _≡_ _<_ _≺_

  ⋖-wf : WellFounded _⋖_
  ⋖-wf = ×-wellFounded <-wellFounded ≺-wf

  -- `m₀` is nearer than `m` to every item `m`'s meaning reaches.
  Lowers : Conf R → Conf R → Set
  Lowers m m₀ = ∀ {k} (c : Ahead (M m) (suc k)) → Σ (Ahead (M m₀) (suc k)) λ c₀ → (depth c₀ , work m₀) ⋖ (depth c , work m)

  -- WHAT A SILENT RUN BETWEEN RE-ENTRY CONFIGURATIONS GAINS: the ghost
  -- alike, every item its configuration reaches nearer.
  data Gain {g m g″ m₀} (st : Strong g m) (st₀ : Strong g″ m₀) : Set₁ where
    lowered : (∀ n → Agree n (residual g) (residual g″)) → Lowers m m₀ → Gain st st₀

  gain-past : ∀ {g m g″ m₀} {st : Strong g m} {st₀ : Strong g″ m₀} → Gain st st₀ → Past (residual g) (residual g″)
  gain-past (lowered ag _) = agrees ag

  -- `m′` runs silently to a re-entry configuration, which `st` gains.
  Hopped : ∀ {g m} → Strong g m → Conf R → Set₁
  Hopped st m′ = Σ (U.Node [] R) λ g″ → Σ (Conf R) λ m₀ → m′ ⇝ m₀ × Σ (Strong g″ m₀) λ st₀ → Gain st st₀

  onward : ∀ {rest g m m′} {st : Strong g m} → rest ≅ residual g → Hopped st m′ → Inner rest m′
  onward e (g″ , m₀ , path , st₀ , gn) = record { ghost = g″ ; same = ≅-trans e (past-same (gain-past gn)) ; mirror = m₀ , path , st₀ }
