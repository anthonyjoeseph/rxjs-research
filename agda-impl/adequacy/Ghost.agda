{-# OPTIONS --guardedness #-}

-- THE GHOST: the meaning's configuration a machine's runs, the measure
-- a climb lowers, and the side conditions `Lifts` reads at each
-- ancestor of a path.
module adequacy.Ghost where

open import Data.List using (List; []; _∷_; _++_; [_]; length)
open import Data.List.Properties using (++-identityʳ)
open import Data.List.Relation.Unary.Any using (Any; here)
import Data.List.Relation.Unary.Any as Any
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Nat.Properties using (≤-refl; m<m+n; <-trans; ≤-reflexive; ≤-trans; m≤n⇒m≤1+n)
open import Data.List.Relation.Unary.All using (All; []; _∷_; map) renaming (lookup to lookupᴬ)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to all-++⁺)
open import Data.List.Relation.Unary.AllPairs using (_∷_)
open import Data.List.Relation.Unary.Linked using (_∷_)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴸ_)
open import Level using (Lift; lift)
open import Data.Maybe using (Maybe; just; nothing; is-just)
open import Data.Nat using (ℕ; suc; _<_; _+_; _≤_; z≤n)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (WellFounded)
open import Data.Product.Relation.Binary.Lex.Strict using (×-Lex; ×-wellFounded)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import denotation.MonotonicList using (Events; Events∞; Pos; Time; Timeline; tick; out; skip; end; hush; observe; root; Agree; out⁼;
  skip⁼; end⁼; hush⁼; agree; agree-sym; ix; _<ᵖ_; <ᵖ-trans; <ᵖ-apart)
import denotation.Unfold as U
open import operation.Placed using (Ahead; none; outᵃ; skipᵃ; endᵃ; hushᵃ)
open import denotation.MonotonicList using () renaming (sub to subᴾ)
open import denotation.Compositional using ([]ᵉ)
open import adequacy.Sorted using (_≤ᵖ_; Under; module Sorting)
open import operation.Machine using (module Machine)
open import adequacy.Strong using (module Strongly)
open import adequacy.Moves using (module Moving)
open import adequacy.Unsub using (module Unsubbing)
open import adequacy.Sane using (Sane)
open import adequacy.Placed using (Placed)
open import adequacy.Stepper using (afterᴱ)
open import denotation.Denote using (⟦_⟧)
import Tree as T
open import operation.PureObservable using (PureObs; Out; Pureᴾ; module Pure)
open import operation.AbstractObservable using (module Heap; module Run) renaming (module Machine to Shared)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_; not)

open Events∞

module Ghosting (R : Set) where
  open Machine R using (Mach; Step; silent; value; complete; drained; step; begin; Read)
  open Shared Timeline (Out R) using (Conf; Heapᴹ; Stack; run)
  open Heap using (World; _⊑_)
  open Sorting R using (WellMach; WellStep; silentʷ; valueʷ; preserve; Beyond)
  open Run (Pureᴾ R) using (Act; Observer; _>>ᴬ_; Subject; module Kit; module FlatKit)
  open Strongly R using (Strong; strong-begin; Carried; Books; carried; closing; Sub; ofˢ; mapˢ; scanˢ; takeWhileˢ; flatMapˢ; connectˢ; deferˢ; Lane; lane; here; module At; Queue; Kernels; Meaning; Owned; Path; done≗; Call; taking; PathLanes; this-lane; next-lane; in-map; in-scan; in-take; in-outer; in-lanes; in-source; in-body; in-defer; _⊕_; _⊕ᴸ_; Here; walk; walkLanes; top; _≗_; Each; Heads; Lingers; DoneBy; outers; outers-⊕; seen; seenL; isTaking; seen-up; seen-join; ∧-split; ∧-join; ≗-refl) renaming (⟦_⟧ to ⟦_⟧ᶜ)
  open Strongly.Against R using (calmAs; noteAs; runAs; subAs; burstAs; bottomAs; restAs; backAs; reholdAs; StackAs; CtlAs; agenda; bursts; begins) renaming (Placed to Placedᴬ)
  open Pure R using (End; finished; dry; cutOff)
  open Moving R using (pend; takes)
  open Unsubbing R using (_⇝_; now; then; ⇝-trans)
  open Read


  ----------------------------------------------------------------------
  -- Alike as sets

  -- The events hold a value (`just`) or their end (`nothing`) at `k`.
  data Has : Events R → Pos → Maybe R → Set where
    atOut    : ∀ {k a r} → Has (out k a r) k (just a)
    atEnd    : ∀ {k} → Has (end k) k nothing
    pastOut  : ∀ {k a r q b} → Has (force r) q b → Has (out k a r) q b
    pastSkip : ∀ {k r q b} → Has (force r) q b → Has (skip k r) q b

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

  -- Events alike at every depth hold the same events.
  has-agree : ∀ {x y k b} → (∀ n → Agree n x y) → Has x k b → Has y k b
  has-agree ag h with ag 1
  has-agree ag atOut        | out⁼ _ _ = atOut
  has-agree ag atEnd        | end⁼    = atEnd
  has-agree ag (pastOut h)  | out⁼ _ _ = pastOut (has-agree (λ n → tail-out (ag (suc n))) h)
  has-agree ag (pastSkip h) | skip⁼ _ _ = pastSkip (has-agree (λ n → tail-skip (ag (suc n))) h)

  -- The same events, as a set.
  _≋_ : Events R → Events R → Set
  x ≋ y = ∀ {k b} → (Has x k b → Has y k b) × (Has y k b → Has x k b)

  same-agree : ∀ {x y} → (∀ n → Agree n x y) → x ≋ y
  same-agree ag = has-agree ag , has-agree (λ n → agree-sym (ag n))


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

  -- A configuration reached from a program's launch, by the machine's own
  -- steps.
  data Reached (e : Events R) : Mach → Set₁ where
    launchedʰ : (o : PureObs [] R) → e ≡ observe (⟦ o ⟧ []) root → Reached e (begin o)
    silentʰ   : ∀ {m m′} → Reached e m → step m ≡ silent m′ → Reached e m′
    valueʰ    : ∀ {m m′ t p a} → Reached e m → step m ≡ value t p a m′ → Reached e m′

  -- One step of the machine that leaves a configuration behind.
  data _↦_ (m : Mach) : Mach → Set₁ where
    silentᵗ : ∀ {m′} → step m ≡ silent m′ → m ↦ m′
    valueᵗ  : ∀ {t p a m′} → step m ≡ value t p a m′ → m ↦ m′

  -- How a configuration's record stands, and where its entries were
  -- made: cut at its clock, or the run drained there, the record's marks
  -- the machine's own; or complete there, its completion marked last.
  data Stands (m : Mach) : End → List Pos → Set₁ where
    cutʰ  : Stands m (cutOff (Mach.clock m)) (Mach.marks m)
    finʰ  : ∀ {p} → step m ≡ complete p → Stands m finished (Mach.marks m ++ [ p ])
    dryʰ  : step m ≡ drained → Stands m dry (Mach.marks m)

  -- A silent step, and a value shown, keep the machine sorted.
  sorted-step : ∀ {m m′} → Σ Pos (λ lo → WellMach lo m) → step m ≡ silent m′ → Σ Pos λ lo → WellMach lo m′
  sorted-step (lo , w) e with subst (WellStep lo) e (preserve w)
  ... | silentʷ _ w′ = _ , w′

  sorted-⇝ : ∀ {m m′} → Σ Pos (λ lo → WellMach lo m) → m ⇝ m′ → Σ Pos λ lo → WellMach lo m′
  sorted-⇝ w now        = w
  sorted-⇝ w (then e p) = sorted-⇝ (sorted-step w e) p

  sorted-value : ∀ {m t q a m′} → Σ Pos (λ lo → WellMach lo m) → step m ≡ value t q a m′ → Σ Pos λ lo → WellMach lo m′
  sorted-value (lo , w) e with subst (WellStep lo) e (preserve w)
  ... | valueʷ _ w′ = _ , w′

  -- THE CONFIGURATION RUNS THE GHOST: it runs silently to a re-entry
  -- configuration against it.  No intermediate configuration is related
  -- to the ghost but by the steps the machine takes from it.
  Mirror : U.Node [] R → Mach → Set₁
  Mirror g m = Σ Mach λ m₀ → m ⇝ m₀ × Strong g m₀

  -- THE CONFIGURATION WILL DELIVER `rest`: it runs a ghost whose
  -- residual `rest` is, as a set.
  record Inner (rest : Events R) (m : Mach) : Set₁ where
    field
      ghost  : U.Node [] R
      same   : rest ≋ residual ghost
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
    silentˢ   : ∀ {m′} → Inner rest m′ → Shows rest (silent m′)
    valueˢ    : ∀ {t p a m′ r} → t ≡ tick p → Has rest p (just a)
              → (∀ {k b} → Has r k b → Has rest k b) → (∀ {k b} → Has rest k b → (k ≡ p × b ≡ just a) ⊎ Has r k b)
              → (∀ {k b} → Has r k b → k ≤ᵖ p → ⊥) → Inner r m′
              → Shows rest (value t p a m′)
    completeˢ : ∀ {p} → Has rest p nothing → (∀ {k a} → Has rest k (just a) → ⊥) → Shows rest (complete p)
    drainedˢ  : (∀ {k b} → Has rest k b → ⊥) → Shows rest drained

  -- The launch will deliver the meaning's events.
  inner-launch : (o : PureObs [] R) → Inner (observe (⟦ o ⟧ []) root) (begin o)
  inner-launch o = record { ghost = U.subscribe o root ; same = same-agree (begun o) ; mirror = begin o , now , strong-begin o }

  ≋-refl : ∀ {x} → x ≋ x
  ≋-refl = (λ h → h) , (λ h → h)

  ≋-trans : ∀ {x y z} → x ≋ y → y ≋ z → x ≋ z
  ≋-trans xy yz = (λ h → proj₁ yz (proj₁ xy h)) , (λ h → proj₂ xy (proj₂ yz h))

  -- WHAT THE GHOST'S STEP SAYS OF ITS RESIDUAL, as a set: a value is in
  -- it, and the rest is what the stepped ghost shows; a skip keeps it; an
  -- end is all of it but the end; a hush leaves nothing.
  Steps : Events R → U.Step [] R → Set
  Steps e (U.outˢ k a g′) = Has e k (just a) × (∀ {q b} → Has (residual g′) q b → Has e q b)
                          × (∀ {q b} → Has e q b → (q ≡ k × b ≡ just a) ⊎ Has (residual g′) q b)
  Steps e (U.skipˢ k g′)  = e ≋ residual g′
  Steps e (U.endˢ k)      = Has e k nothing × (∀ {q a} → Has e q (just a) → ⊥)
  Steps e U.hushˢ         = ∀ {q b} → Has e q b → ⊥

  -- What a step shows, then the residual of the ghost it leaves.
  after : U.Step [] R → Events R
  after = afterᴱ []

  -- Events alike, as a set, with what a step shows are what it says.
  steps-after : ∀ {e} s → e ≋ after s → Steps e s
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
  -- the same; as a measure a skip dropped is progress, which `≋` cannot
  -- see.
  record Past (x y : Events R) : Set where
    field
      same  : x ≋ y
      fewer : Fewer x y

  skip-same : ∀ {k r} → skip k r ≋ force r
  skip-same = (λ { (pastSkip h) → h }) , pastSkip

  past-same : ∀ {x y} → Past x y → x ≋ y
  past-same = Past.same

  agrees : ∀ {x y} → (∀ n → Agree n x y) → Past x y
  agrees ag = record { same = same-agree ag ; fewer = λ a → proj₁ (ahead-agree ag a) , ≤-reflexive (proj₂ (ahead-agree ag a)) }

  skipped : ∀ {x y k r} → (∀ n → Agree n x (skip k r)) → Past (force r) y → Past x y
  skipped {x} {y} {k} {r} ag p = record { same = ≋-trans (same-agree ag) (≋-trans skip-same (Past.same p)) ; fewer = fewer }
    where fewer : Fewer x y
          fewer a with ahead-agree ag a
          ... | none     , _  = none , z≤n
          ... | skipᵃ a′ , de with Past.fewer p a′
          ...   | b , le = b , ≤-trans (m≤n⇒m≤1+n le) (≤-reflexive de)

  past-pre : ∀ {x y z} → (∀ n → Agree n x y) → Past y z → Past x z
  past-pre {x} {y} {z} ag p = record { same = ≋-trans (same-agree ag) (Past.same p) ; fewer = fewer }
    where fewer : Fewer x z
          fewer a with ahead-agree ag a
          ... | b , de with Past.fewer p b
          ...   | c , le = c , ≤-trans le (≤-reflexive de)

  ----------------------------------------------------------------------
  -- WHAT IS LEFT BEFORE THE GHOST MOVES

  -- The control's own work: the calls owed and the frames they wait in,
  -- code about to run counted once.  What the ghost never sees: a
  -- continuation handed its unsubscribe, a cut, a frame resumed.
  work : ∀ {h} {t : Sub h [] R} {w p} {σ : w ⊑ h} {K bs} → StackAs t p σ K bs → ℕ
  work bottomAs             = 0
  work (restAs ks _ K)      = suc (length ks + work K)
  work (backAs _ ks _ _ K)  = suc (length ks + work K)
  work (reholdAs _ _ K)     = suc (work K)

  weight : ∀ {h} {t : Sub h [] R} {p c bs} → CtlAs t p c bs → ℕ
  weight calmAs          = 0
  weight (noteAs ks _ K) = suc (length ks + work K)
  weight (runAs ks _ K)  = suc (length ks + work K)
  weight (subAs _ _ K _) = suc (work K)
  weight (burstAs _ _ K) = work K

  -- The values the tree's `of`s have still to emit.  A connect's source
  -- runs its subscribe burst out into a subject nobody reads once what
  -- held it has ended, as rxjs does: no ghost holds those values and no
  -- other count moves, so only this one sees them go.
  mutual
    left : ∀ {h Δ A} → Sub h Δ A → ℕ
    left (ofˢ _ _ xs)                      = length xs
    left (mapˢ f s)                        = left s
    left (scanˢ f r s)                     = left s
    left (takeWhileˢ i q c k tk s)         = left s
    left (flatMapˢ op f fl oc k r pl s ls) = left s + leftᴸ ls
    left (connectˢ S c b kb k fd rp e rt src bd) = left src + left bd
    left (deferˢ k s)                      = left s
    left _                                 = 0

    leftᴸ : ∀ {h Δ B} → List (Lane h Δ B) → ℕ
    leftᴸ []                = 0
    leftᴸ (lane c k s ∷ ls) = left s + leftᴸ ls

  -- THE WORK LEFT AT A RE-ENTRY CONFIGURATION, in order: subscriptions
  -- owed, takeWhiles' stages, timers queued, bursts held, values the
  -- `of`s owe (the tree's load), then the control's own.
  Load : Set
  Load = ℕ × ℕ × ℕ × ℕ × ℕ

  _⊏_ : Load → Load → Set
  _⊏_ = ×-Lex _≡_ _<_ (×-Lex _≡_ _<_ (×-Lex _≡_ _<_ (×-Lex _≡_ _<_ _<_)))

  _≼_ : Load → Load → Set
  a ≼ b = a ≡ b ⊎ a ⊏ b

  load : (m : Mach) → Sub (Conf.world (Mach.conf m)) [] R → Load
  load m t = pend t , takes t , length (Mach.timers m) , length (Mach.bursts m) , left t

  lex-trans : ∀ {B : Set} {_<₂_ : B → B → Set} → (∀ {x y z} → x <₂ y → y <₂ z → x <₂ z)
            → ∀ {a b c : ℕ × B} → ×-Lex _≡_ _<_ _<₂_ a b → ×-Lex _≡_ _<_ _<₂_ b c → ×-Lex _≡_ _<_ _<₂_ a c
  lex-trans t (inj₁ ab)        (inj₁ bc)        = inj₁ (<-trans ab bc)
  lex-trans t (inj₁ ab)        (inj₂ (refl , _)) = inj₁ ab
  lex-trans t (inj₂ (refl , _)) (inj₁ bc)        = inj₁ bc
  lex-trans t (inj₂ (refl , ab)) (inj₂ (refl , bc)) = inj₂ (refl , t ab bc)

  ⊏-trans : ∀ {a b c} → a ⊏ b → b ⊏ c → a ⊏ c
  ⊏-trans = lex-trans {_<₂_ = ×-Lex _≡_ _<_ (×-Lex _≡_ _<_ (×-Lex _≡_ _<_ _<_))}
              (lex-trans {_<₂_ = ×-Lex _≡_ _<_ (×-Lex _≡_ _<_ _<_)}
                (lex-trans {_<₂_ = ×-Lex _≡_ _<_ _<_} (lex-trans {_<₂_ = _<_} <-trans)))

  ≼-trans : ∀ {a b c} → a ≼ b → b ≼ c → a ≼ c
  ≼-trans (inj₁ refl) bc          = bc
  ≼-trans (inj₂ ab)   (inj₁ refl) = inj₂ ab
  ≼-trans (inj₂ ab)   (inj₂ bc)   = inj₂ (⊏-trans ab bc)

  ⊏-≼ : ∀ {a b c} → a ⊏ b → b ≼ c → a ⊏ c
  ⊏-≼ ab (inj₁ refl) = ab
  ⊏-≼ ab (inj₂ bc)   = ⊏-trans ab bc

  Measure : Set
  Measure = Load × ℕ

  _≺_ : Measure → Measure → Set
  _≺_ = ×-Lex _≡_ _⊏_ _<_

  ≺-wf : WellFounded _≺_
  ≺-wf = ×-wellFounded (×-wellFounded <-wellFounded (×-wellFounded <-wellFounded (×-wellFounded <-wellFounded
           (×-wellFounded <-wellFounded <-wellFounded)))) <-wellFounded

  measure : ∀ {g m} → Strong g m → Measure
  measure {m = m} (carried cr) = load m (Carried.tree cr) , weight (Carried.ctlAs cr)
  measure (closing _ _ _ _ _)  = (0 , 0 , 0 , 0 , 0) , 0

  loadOf : ∀ {g m} → Strong g m → Load
  loadOf st = proj₁ (measure st)

  -- WHAT A SILENT RUN BETWEEN RE-ENTRY CONFIGURATIONS GAINS: the ghost
  -- past a skip of its residual; or the ghost alike, less work left; or
  -- a configuration whose next step shows something.
  data Gain {g m g″ m₀} (st : Strong g m) (st₀ : Strong g″ m₀) : Set₁ where
    passed  : ∀ {k r} → (∀ n → Agree n (residual g) (skip k r)) → Past (force r) (residual g″) → Gain st st₀
    lowered : (∀ n → Agree n (residual g) (residual g″)) → measure st₀ ≺ measure st → Gain st st₀
    showing : Past (residual g) (residual g″) → (∀ {m″} → step m₀ ≢ silent m″) → Gain st st₀

  gain-past : ∀ {g m g″ m₀} {st : Strong g m} {st₀ : Strong g″ m₀} → Gain st st₀ → Past (residual g) (residual g″)
  gain-past (passed ag p)  = skipped ag p
  gain-past (lowered ag _) = agrees ag
  gain-past (showing p _)  = p

  -- `m′` runs silently to a re-entry configuration, which `st` gains.
  Hopped : ∀ {g m} → Strong g m → Mach → Set₁
  Hopped st m′ = Σ (U.Node [] R) λ g″ → Σ Mach λ m₀ → m′ ⇝ m₀ × Σ (Strong g″ m₀) λ st₀ → Gain st st₀

  onward : ∀ {rest g m m′} {st : Strong g m} → rest ≋ residual g → Hopped st m′ → Inner rest m′
  onward e (g″ , m₀ , path , st₀ , gn) = record { ghost = g″ ; same = ≋-trans e (past-same (gain-past gn)) ; mirror = m₀ , path , st₀ }

  -- The driver's turn with a burst held is silent, whatever the burst.
  if-silent : ∀ (x y : Bool) {A B C} → Σ Mach λ m′ → (if x then silent A else if y then silent B else silent C) ≡ silent m′
  if-silent true  _     = _ , refl
  if-silent false true  = _ , refl
  if-silent false false = _ , refl


  -- `m`, carried, runs silently on to a re-entry configuration it gains.
  Hops : ∀ {g m} → Carried g m → Set₁
  Hops {m = m} cr = ∀ {m′} → step m ≡ silent m′ → Hopped (carried cr) m′

  -- What the control is about to run: a subscription begun, or the
  -- agenda's first call.
  opening : ∀ {h} {t : Sub h [] R} {p c bs} → CtlAs t p c bs → Bool
  opening (subAs _ _ _ _) = true
  opening _             = false

  firstCall : ∀ {h} {t : Sub h [] R} {p c bs} → CtlAs t p c bs → Maybe (Call t)
  firstCall (runAs (k ∷ _) _ _) = just k
  firstCall _                   = nothing

  -- The control moved, owing what it owed.
  owned-move : ∀ {h} (H : Heapᴹ h) {t : Sub h [] R} {p c bs p₀ c₀ bs₀} {ca : CtlAs t p c bs} (ca₀ : CtlAs t p₀ c₀ bs₀)
             → agenda t ca₀ ≡ agenda t ca → bursts t ca₀ ≡ bursts t ca → begins t ca₀ ≡ begins t ca
             → Owned H t ca → Owned H t ca₀
  owned-move H {t} ca₀ ag bu be ow = record
    { ofs    = λ π → subst (λ z → _ ∈ᴸ z) (sym ag) (Owned.ofs ow π)
    ; plays  = λ π nsp → subst (λ z → _ ∈ᴸ z) (sym bu) (Owned.plays ow π nsp)
    ; fires  = λ π nsp → subst (λ z → _ ∈ᴸ z) (sym bu) (Owned.fires ow π nsp)
    ; begun  = λ π → subst (λ z → _ ∈ᴸ z) (sym be) (Owned.begun ow π)
    ; ends   = λ π l → subst (λ z → _ ∈ᴸ z) (sym ag) (Owned.ends ow π l)
    ; cuts   = λ π l → proj₁ (Owned.cuts ow π l) , subst (λ z → _ ∈ᴸ z) (sym ag) (proj₂ (Owned.cuts ow π l))
    ; feeds  = λ π → subst (λ z → _ ∈ᴸ z) (sym ag) (Owned.feeds ow π)
    ; fins   = λ π → subst (λ z → _ ∈ᴸ z) (sym ag) (Owned.fins ow π)
    ; bodies = λ π i → Owned.bodies ow π (subst (λ z → _ ∈ᴸ z) ag i)
    ; placed = subst (All (Placedᴬ t)) (sym ag) (Owned.placed ow) }

  ----------------------------------------------------------------------
  -- AN `of`'S VALUE CLIMBS ITS PATH

  -- The source's next event before the body's: its own skip, the body's
  -- step left for later.  A hushed source never is.
  SourceFirst : ∀ {Γ A B} → U.Step Γ A → U.Step (A ∷ Γ) B → Set
  SourceFirst (U.outˢ q _ _) sb = U.beforeˢ (q ++ [ ix 0 ]) sb ≡ true
  SourceFirst (U.skipˢ q _)  sb = U.beforeˢ (q ++ [ ix 0 ]) sb ≡ true
  SourceFirst (U.endˢ c)     sb = U.beforeˢ (c ++ [ ix 0 ]) sb ≡ true
  SourceFirst U.hushˢ        sb = ⊥

  BodyFirst : ∀ {Γ A B} → U.Step Γ A → U.Step (A ∷ Γ) B → Set
  BodyFirst (U.outˢ q _ _) sb = U.beforeˢ (q ++ [ ix 0 ]) sb ≡ false
  BodyFirst (U.skipˢ q _)  sb = U.beforeˢ (q ++ [ ix 0 ]) sb ≡ false
  BodyFirst (U.endˢ c)     sb = U.beforeˢ (c ++ [ ix 0 ]) sb ≡ false
  BodyFirst U.hushˢ        sb = ⊤

  -- A flatMap's outer step ahead of every lane's.
  OuterFirst : ∀ {Γ A B} → U.Step Γ A → List (U.Node Γ B) → Set₁
  OuterFirst S ls = ∀ {k bs l s as} → U.earliest ls ≡ U.found k bs l s as → Σ Pos λ k′ → U.headˢ S ≡ just k′ × k′ <ᵖ k ≡ true

  -- What a flatMap's ended parts left running steps no sooner than its
  -- outer and lanes.
  PoolBehind : ∀ {Γ A B} → U.Node Γ B → U.Outer Γ A → U.Earliest Γ B → Set₁
  PoolBehind p o e = ∀ {k p′} → U.step p ≡ U.skipˢ k p′ → U.aheadˢ k o e ≡ false

  -- What an ended source left running steps no sooner than the body.
  RestBehind : ∀ {Γ A B} → U.Node Γ A → U.Step (A ∷ Γ) B → Set₁
  RestBehind t sb = ∀ {k t′} → U.step t ≡ U.skipˢ k t′ → U.beforeˢ (k ++ [ ix 0 ]) sb ≡ false

  -- The earliest lane's step, at `k`, ahead of the outer's.
  LaneFirst : ∀ {Γ A} → Maybe (U.Node Γ A) → Pos → Set
  LaneFirst nothing  k = ⊤
  LaneFirst (just o) k = ∀ {k′} → U.headˢ (U.step o) ≡ just k′ → k′ <ᵖ k ≡ false

  -- THE GHOST'S STEP, FROM A STEP AT THE PATH'S END: `s` at the node the
  -- path reaches, `S` at the node it starts from, each operator on the
  -- way the meaning's own step, its order said by the side condition
  -- that picks it.  A lane's step comes with the lanes before and after
  -- it.  No ancestor reads its path child's part, only the child's
  -- step, so a write inside a node leaves every lift above it.
  mutual
    data Lifts {h} (H : Heapᴹ h) : ∀ {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} → Path t u → U.Step Δ′ A′ → U.Step Δ A → Set₁ where
      lifts-here   : ∀ {Δ A} {t : Sub h Δ A} {s} → Lifts H (here {t = t}) s s
      lifts-map    : ∀ {Δ A B Δ′ C} {f : A → B} {t : Sub h Δ A} {u : Sub h Δ′ C} {ρ : Path t u} {s S}
                   → Lifts H ρ s S → Lifts H (in-map {f = f} ρ) s (U.mapˢ f S)
      lifts-scan   : ∀ {Δ A B Δ′ C} {f : B → A → B} {r} {t : Sub h Δ A} {u : Sub h Δ′ C} {ρ : Path t u} {s S}
                   → Lifts H ρ s S → Lifts H (in-scan {f = f} {r} ρ) s (U.scanˢ f (At.val H r) S)
      lifts-take   : ∀ {Δ A Δ′ C} {i p c k} {t : Sub h Δ A} {u : Sub h Δ′ C} {ρ : Path t u} {s S}
                   → At.val H (Kit.live c) ≡ true → Lifts H ρ s S → Lifts H (in-take {i = i} {p} {c} {k} {taking} ρ) s (U.takeWhileˢ i p S)
      lifts-outer  : ∀ {Δ A B Δ′ C} {op f fl oc k r pl} {t : Sub h Δ A} {ls : List (Lane h Δ B)} {u : Sub h Δ′ C} {ρ : Path t u} {s S o₀}
                   → OuterFirst S (At.partLanes H ls)
                   → PoolBehind pl (U.outerOf (just o₀)) (U.earliest (At.partLanes H ls)) → Lifts H ρ s S
                   → Lifts H (in-outer {op = op} {f} {fl} {oc} {k} {r} {pl} {ls = ls} ρ) s
                       (U.outerˢ op (λ a q → U.subscribe (f a) q) o₀ S (At.partLanes H ls) (At.val H (FlatKit.Flat.queue fl)) pl)
      lifts-lanes  : ∀ {Δ A B Δ′ C} {op f fl oc k r pl} {t : Sub h Δ A} {ls : List (Lane h Δ B)} {u : Sub h Δ′ C} {πL : PathLanes ls u}
                       {s bs l S as q}
                   → LiftsLane H πL s bs S as → U.earliest (bs ++ l ∷ as) ≡ U.found q bs l S as → LaneFirst (At.part H t) q
                   → PoolBehind pl (U.outerOf (At.part H t)) (U.found q bs l S as)
                   → Lifts H (in-lanes {op = op} {f} {fl} {oc} {k} {r} {pl} {t = t} πL) s
                       (U.laneˢ op (λ a q → U.subscribe (f a) q) (At.part H t) bs l S as (At.val H (FlatKit.Flat.queue fl)) pl)
      lifts-source : ∀ {Δ A B Δ′ C} {Sj c b kb k fd e rp rt} {t : Sub h Δ A} {bd : Sub h (A ∷ Δ) B} {u : Sub h Δ′ C} {ρ : Path t u} {s S c₀ b₀}
                   → At.part H bd ≡ just b₀ → SourceFirst S (U.step b₀) → Lifts H ρ s S
                   → Lifts H (in-source {S = Sj} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {bd = bd} ρ) s (U.sourceˢ rp b₀ (U.step b₀) c₀ S)
      lifts-body   : ∀ {Δ A B Δ′ C} {Sj c b kb k fd e rp rt} {t : Sub h Δ A} {bd : Sub h (A ∷ Δ) B} {u : Sub h Δ′ C} {ρ : Path bd u} {s S c₀}
                   → At.part H t ≡ just c₀ → BodyFirst (U.step c₀) S → Lifts H ρ s S
                   → Lifts H (in-body {S = Sj} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {t = t} ρ) s (U.bodyˢ rp (U.live c₀) S)
      lifts-shut   : ∀ {Δ A B Δ′ C} {Sj c b kb k fd e rp rt} {t : Sub h Δ A} {bd : Sub h (A ∷ Δ) B} {u : Sub h Δ′ C} {ρ : Path bd u} {s S c₀}
                   → At.part H t ≡ nothing → e ≡ just c₀ → RestBehind rt S → Lifts H ρ s S
                   → Lifts H (in-body {S = Sj} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {t = t} ρ) s (U.shutˢᵗ rp c₀ rt S)
      lifts-defer  : ∀ {Δ A Δ′ C} {k} {t : Sub h Δ A} {u : Sub h Δ′ C} {ρ : Path t u} {s S}
                   → Lifts H ρ s S → Lifts H (in-defer {k = k} ρ) s S

    data LiftsLane {h} (H : Heapᴹ h) : ∀ {Δ B Δ′ C} {ls : List (Lane h Δ B)} {u : Sub h Δ′ C} → PathLanes ls u → U.Step Δ′ C
                                     → List (U.Node Δ B) → U.Step Δ B → List (U.Node Δ B) → Set₁ where
      lifts-this : ∀ {Δ B Δ′ C} {c k} {t : Sub h Δ B} {ls} {u : Sub h Δ′ C} {ρ : Path t u} {s S}
                 → At.val H (Kit.live c) ≡ true → Lifts H ρ s S → LiftsLane H (this-lane {c = c} {k} {ls = ls} ρ) s [] S (At.partLanes H ls)
      lifts-next : ∀ {Δ B Δ′ C} {l} {ls : List (Lane h Δ B)} {u : Sub h Δ′ C} {πL : PathLanes ls u} {s bs S as}
                 → LiftsLane H πL s bs S as → LiftsLane H (next-lane {l = l} πL) s (At.partLanes H (l ∷ []) ++ bs) S as

  -- Lifting along two paths is lifting along each.
  mutual
    lifts-split : ∀ {h} {H : Heapᴹ h} {Δ A Δ′ A′ Δ″ A″} {t : Sub h Δ A} {u : Sub h Δ′ A′} {v : Sub h Δ″ A″} (ρ : Path t u) (τ : Path u v) {s S}
                → Lifts H (ρ ⊕ τ) s S → Σ (U.Step Δ′ A′) λ S′ → Lifts H τ s S′ × Lifts H ρ S′ S
    lifts-split here          τ L                          = _ , L , lifts-here
    lifts-split (in-map ρ)    τ (lifts-map L)              with lifts-split ρ τ L
    ... | S′ , Lτ , Lρ = S′ , Lτ , lifts-map Lρ
    lifts-split (in-scan ρ)   τ (lifts-scan L)             with lifts-split ρ τ L
    ... | S′ , Lτ , Lρ = S′ , Lτ , lifts-scan Lρ
    lifts-split (in-take ρ)   τ (lifts-take lv L)          with lifts-split ρ τ L
    ... | S′ , Lτ , Lρ = S′ , Lτ , lifts-take lv Lρ
    lifts-split (in-outer ρ)  τ (lifts-outer of pb L)      with lifts-split ρ τ L
    ... | S′ , Lτ , Lρ = S′ , Lτ , lifts-outer of pb Lρ
    lifts-split (in-lanes πL) τ (lifts-lanes L ea lf pb)   with liftsL-split πL τ L
    ... | S′ , Lτ , Lρ = S′ , Lτ , lifts-lanes Lρ ea lf pb
    lifts-split (in-source ρ) τ (lifts-source pb sf L)     with lifts-split ρ τ L
    ... | S′ , Lτ , Lρ = S′ , Lτ , lifts-source pb sf Lρ
    lifts-split (in-body ρ)   τ (lifts-body pt bf L)       with lifts-split ρ τ L
    ... | S′ , Lτ , Lρ = S′ , Lτ , lifts-body pt bf Lρ
    lifts-split (in-body ρ)   τ (lifts-shut pt e rb L)     with lifts-split ρ τ L
    ... | S′ , Lτ , Lρ = S′ , Lτ , lifts-shut pt e rb Lρ
    lifts-split (in-defer ρ)  τ (lifts-defer L)            with lifts-split ρ τ L
    ... | S′ , Lτ , Lρ = S′ , Lτ , lifts-defer Lρ

    liftsL-split : ∀ {h} {H : Heapᴹ h} {Δ B Δ′ A′ Δ″ A″} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} {v : Sub h Δ″ A″}
                   (πL : PathLanes ls u) (τ : Path u v) {s bs S as}
                 → LiftsLane H (πL ⊕ᴸ τ) s bs S as → Σ (U.Step Δ′ A′) λ S′ → Lifts H τ s S′ × LiftsLane H πL S′ bs S as
    liftsL-split (this-lane ρ)  τ (lifts-this lv L) with lifts-split ρ τ L
    ... | S′ , Lτ , Lρ = S′ , Lτ , lifts-this lv Lρ
    liftsL-split (next-lane πL) τ (lifts-next L)    with liftsL-split πL τ L
    ... | S′ , Lτ , Lρ = S′ , Lτ , lifts-next Lρ

  -- A node whose next event is past `p` and everything under it.
  record Far {Γ A} (p : Pos) (c : U.Node Γ A) : Set where
    constructor far
    field far-at : ∀ {k} → U.headˢ (U.step c) ≡ just k → Beyond p k

  -- A node whose next event is not under `p`.
  Off : ∀ {Γ A} → Pos → U.Node Γ A → Set
  Off p c = ∀ {k} → U.headˢ (U.step c) ≡ just k → Under p k → ⊥

  -- No earlier than `p` and not under it: past all of it.
  beyond-apart : ∀ {p k} → p ≤ᵖ k → (Under p k → ⊥) → Beyond p k
  beyond-apart {p} (inj₁ refl) nu = ⊥-elim (nu ([] , sym (++-identityʳ p)))
  beyond-apart {p} {k} (inj₂ lt) nu = record { past = λ y → <ᵖ-apart p k y lt (λ ys e → nu (ys , e)) }

  far-apart : ∀ {p Γ A} {c : U.Node Γ A} → Heads p c → Off p c → Far p c
  far-apart hd off = far λ e → beyond-apart (hd e) (off e)

  Opt : (∀ {Γ A} → U.Node Γ A → Set) → ∀ {Γ A} → Maybe (U.Node Γ A) → Set
  Opt P nothing  = ⊤
  Opt P (just c) = P c

  -- What a held node's ended parts left running passes `P`: a flatMap's
  -- pool, a connect's ended source's rest.
  Pooled : ∀ {h} (H : Heapᴹ h) (P : ∀ {Γ A} → U.Node Γ A → Set) {Δ B Δ′ B′} → U.Node Δ B → Sub h Δ′ B′ → Set₁
  Pooled H P pl u = ∀ {c} → At.part H u ≡ just c → P pl

  Rested : ∀ {h} (H : Heapᴹ h) (P : ∀ {Γ A} → U.Node Γ A → Set) {Δ A Δ′ B′} → U.Node Δ A → Sub h Δ A → Maybe Pos → Sub h Δ′ B′ → Set₁
  Rested H P rt src e u = ∀ {n} → At.part H u ≡ just n → At.part H src ≡ nothing → ∀ {c₀} → e ≡ just c₀ → P rt

  -- EVERY SIBLING THE PATH PASSES PASSES `P`: a flatMap's other lanes,
  -- its outer and its pool, a connect's source or body and an ended
  -- source's rest.  At `Far p`, what each side condition of `Lifts` asks,
  -- given the step at the path's end is under `p`.
  mutual
    Clear : ∀ {h} (H : Heapᴹ h) (P : ∀ {Γ A} → U.Node Γ A → Set) {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} → Path t u → Set₁
    Clear H P here                    = Lift _ ⊤
    Clear H P (in-map ρ)              = Clear H P ρ
    Clear H P (in-scan ρ)             = Clear H P ρ
    Clear H P (in-take ρ)             = Clear H P ρ
    Clear H P (in-outer {op = op} {f} {fl} {oc} {k} {r} {pl} {t} {ls} ρ) =
      All P (At.partLanes H ls) × Pooled H P pl (flatMapˢ op f fl oc k r pl t ls) × Clear H P ρ
    Clear H P (in-lanes {op = op} {f} {fl} {oc} {k} {r} {pl} {t} {ls} πL) =
      Opt P (At.part H t) × Pooled H P pl (flatMapˢ op f fl oc k r pl t ls) × ClearL H P πL
    Clear H P (in-source {bd = bd} ρ) = Opt P (At.part H bd) × Clear H P ρ
    Clear H P (in-body {S = Sj} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {t} {bd} ρ) =
      Opt P (At.part H t) × Rested H P rt t e (connectˢ Sj c b kb k fd rp e rt t bd) × Clear H P ρ
    Clear H P (in-defer ρ)            = Clear H P ρ

    ClearL : ∀ {h} (H : Heapᴹ h) (P : ∀ {Γ A} → U.Node Γ A → Set) {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′}
           → PathLanes ls u → Set₁
    ClearL H P (this-lane {ls = ls} ρ) = All P (At.partLanes H ls) × Clear H P ρ
    ClearL H P (next-lane {l = l} πL)  = All P (At.partLanes H (l ∷ [])) × ClearL H P πL

  -- Two facts of every sibling, one.
  module _ {P Q R′ : ∀ {Γ A} → U.Node Γ A → Set} (f : ∀ {Γ A} {c : U.Node Γ A} → P c → Q c → R′ c) where
    all-zip : ∀ {Γ A} {cs : List (U.Node Γ A)} → All P cs → All Q cs → All R′ cs
    all-zip []       []       = []
    all-zip (a ∷ as) (b ∷ bs) = f a b ∷ all-zip as bs

    opt-zip : ∀ {Γ A} (o : Maybe (U.Node Γ A)) → Opt P o → Opt Q o → Opt R′ o
    opt-zip nothing  _ _ = tt
    opt-zip (just c) a b = f a b

    mutual
      clear-zip : ∀ {h} {H : Heapᴹ h} {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) → Clear H P π → Clear H Q π → Clear H R′ π
      clear-zip here          _         _         = lift tt
      clear-zip (in-map ρ)    a         b         = clear-zip ρ a b
      clear-zip (in-scan ρ)   a         b         = clear-zip ρ a b
      clear-zip (in-take ρ)   a         b         = clear-zip ρ a b
      clear-zip (in-outer ρ)  (a , pa , a′)  (b , pb , b′)  = all-zip a b , (λ e → f (pa e) (pb e)) , clear-zip ρ a′ b′
      clear-zip {H = H} (in-lanes {t = t} πL) (a , pa , a′) (b , pb , b′) =
        opt-zip (At.part H t) a b , (λ e → f (pa e) (pb e)) , clearL-zip πL a′ b′
      clear-zip {H = H} (in-source {bd = bd} ρ) (a , a′) (b , b′) = opt-zip (At.part H bd) a b , clear-zip ρ a′ b′
      clear-zip {H = H} (in-body {t = t} ρ) (a , ra , a′) (b , rb , b′) =
        opt-zip (At.part H t) a b , (λ e n j → f (ra e n j) (rb e n j)) , clear-zip ρ a′ b′
      clear-zip (in-defer ρ)  a         b         = clear-zip ρ a b

      clearL-zip : ∀ {h} {H : Heapᴹ h} {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (πL : PathLanes ls u)
                 → ClearL H P πL → ClearL H Q πL → ClearL H R′ πL
      clearL-zip (this-lane ρ)  (a , a′) (b , b′) = all-zip a b , clear-zip ρ a′ b′
      clearL-zip (next-lane πL) (a , a′) (b , b′) = all-zip a b , clearL-zip πL a′ b′

  -- What every node below passes, every sibling along a path does.
  module _ {h} {H : Heapᴹ h} {P : ∀ {Γ A} → U.Node Γ A → Set} where
    opt-each : ∀ {Γ A} (o : Maybe (U.Node Γ A)) → (∀ {c} → o ≡ just c → P c) → Opt P o
    opt-each nothing  f = tt
    opt-each (just c) f = f refl

    lane-only : ∀ {Δ B Δ′ A′} {l : Lane h Δ B} {ls} {u : Sub h Δ′ A′} → PathLanes (l ∷ []) u → PathLanes (l ∷ ls) u
    lane-only (this-lane ρ)  = this-lane ρ
    lane-only (next-lane ())

    seenL-only : ∀ {Δ B Δ′ A′} {l : Lane h Δ B} {ls} {u : Sub h Δ′ A′} (πL : PathLanes (l ∷ []) u) → seenL H (lane-only {ls = ls} πL) ≡ seenL H πL
    seenL-only (this-lane ρ)  = refl
    seenL-only (next-lane ())

    ∨-true : ∀ {x y} → x ≡ true → x ∨ y ≡ true
    ∨-true refl = refl

    each-lanes : ∀ {Δ B} (ls : List (Lane h Δ B))
               → (∀ {Δ′ A′} {u : Sub h Δ′ A′} (πL : PathLanes ls u) → seenL H πL ≡ true → ∀ {c} → At.part H u ≡ just c → P c)
               → All P (At.partLanes H ls)
    each-lanes []                f = []
    each-lanes (lane c k s ∷ ls) f with At.val H (Kit.live c) in lv
    ... | false = each-lanes ls (λ πL → f (next-lane πL))
    ... | true with At.part H s in e
    ...   | nothing = each-lanes ls (λ πL → f (next-lane πL))
    ...   | just x  = f (this-lane here) (∧-join lv refl) e ∷ each-lanes ls (λ πL → f (next-lane πL))

    each-sub : ∀ {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} → Each H P t → (ρ : Path t u) → seen H ρ ≡ true → Each H P u
    each-sub ev ρ sρ = record
      { parts = λ ψ sψ → Each.parts ev (ρ ⊕ ψ) (seen-join H ρ ψ sρ sψ)
      ; pools = λ ψ sψ → Each.pools ev (ρ ⊕ ψ) (seen-join H ρ ψ sρ sψ)
      ; rests = λ ψ sψ → Each.rests ev (ρ ⊕ ψ) (seen-join H ρ ψ sρ sψ) }

    -- Along a path the ghost holds to a part it holds.
    mutual
      clear-each : ∀ {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} → Each H P t → (π : Path t u) → seen H π ≡ true
                 → is-just (At.part H u) ≡ true → Clear H P π
      clear-each ev here                    _  _ = lift tt
      clear-each ev (in-map ρ)              sn j = clear-each (each-sub ev (in-map here) refl) ρ sn j
      clear-each ev (in-scan ρ)             sn j = clear-each (each-sub ev (in-scan here) refl) ρ sn j
      clear-each ev (in-take {c = c} {tk = tk} ρ) sn j with ∧-split (At.val H (Kit.live c)) sn
      ... | lv , r with ∧-split (isTaking tk) r
      ... | tg , sρ = clear-each (each-sub ev (in-take here) (∧-join lv (∧-join tg refl))) ρ sρ j
      clear-each ev (in-outer {ls = ls} ρ)  sn j =
        each-lanes ls (λ πL sL → Each.parts ev (in-lanes πL) sL) , Each.pools ev here refl , clear-each (each-sub ev (in-outer here) refl) ρ sn j
      clear-each ev (in-lanes {t = t} πL)   sn j =
        opt-each (At.part H t) (Each.parts ev (in-outer here) refl) , Each.pools ev here refl
        , clearL-each (λ πL′ sL → each-sub ev (in-lanes πL′) sL) πL sn j
      clear-each ev (in-source {bd = bd} ρ) sn j with ∧-split (is-just (At.part H bd)) sn
      ... | jb , sρ = opt-each (At.part H bd) (Each.parts ev (in-body here) (∧-join (∨-true (seen-up H ρ sρ j)) refl))
                    , clear-each (each-sub ev (in-source here) (∧-join jb refl)) ρ sρ j
      clear-each ev (in-body {e = e} {t = t} ρ) sn j with ∧-split (is-just (At.part H t) ∨ is-just e) sn
      ... | js , sρ = opt-each (At.part H t) (Each.parts ev (in-source here) (∧-join (seen-up H ρ sρ j) refl)) , Each.rests ev here refl
                    , clear-each (each-sub ev (in-body here) (∧-join js refl)) ρ sρ j
      clear-each ev (in-defer ρ)            sn j = clear-each (each-sub ev (in-defer here) refl) ρ sn j

      clearL-each : ∀ {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′}
                  → (∀ {Δ″ A″} {w : Sub h Δ″ A″} (πL : PathLanes ls w) → seenL H πL ≡ true → Each H P w)
                  → (πL : PathLanes ls u) → seenL H πL ≡ true → is-just (At.part H u) ≡ true → ClearL H P πL
      clearL-each f (this-lane {c = c} {ls = ls} ρ) sn j with ∧-split (At.val H (Kit.live c)) sn
      ... | lv , sρ = each-lanes ls (λ πL sL → Each.parts (f (next-lane πL) sL) here refl) , clear-each (f (this-lane here) (∧-join lv refl)) ρ sρ j
      clearL-each f (next-lane {l = l} πL)  sn j =
        each-lanes (l ∷ []) (λ πL′ sL → Each.parts (f (lane-only πL′) (trans (seenL-only πL′) sL)) here refl)
        , clearL-each (λ πL′ → f (next-lane πL′)) πL sn j

  -- Walking two paths is walking each.
  mutual
    walk-⊕ : ∀ {h Δ A Δ′ A′ Δ″ A″} {t : Sub h Δ A} {u : Sub h Δ′ A′} {v : Sub h Δ″ A″} (ρ : Path t u) (τ : Path u v) (W : Here h Δ A)
           → walk (ρ ⊕ τ) W ≡ walk τ (walk ρ W)
    walk-⊕ here          τ W = refl
    walk-⊕ (in-map ρ)    τ W = walk-⊕ ρ τ _
    walk-⊕ (in-scan ρ)   τ W = walk-⊕ ρ τ _
    walk-⊕ (in-take ρ)   τ W = walk-⊕ ρ τ _
    walk-⊕ (in-outer ρ)  τ W = walk-⊕ ρ τ _
    walk-⊕ (in-lanes {op = op} {f} {fl} πL) τ W = walkL-⊕ op f fl W πL τ
    walk-⊕ (in-source ρ) τ W = walk-⊕ ρ τ _
    walk-⊕ (in-body ρ)   τ W = walk-⊕ ρ τ _
    walk-⊕ (in-defer ρ)  τ W = walk-⊕ ρ τ _

    walkL-⊕ : ∀ {h Δ A B Δ′ A′ Δ″ A″} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} {v : Sub h Δ″ A″} (op : T.FlatOp)
              (f : A → T.Obs Timeline Δ B) (fl : FlatKit.Flat A h) (W : Here h Δ B) (πL : PathLanes ls u) (τ : Path u v)
            → walkLanes op f fl W (πL ⊕ᴸ τ) ≡ walk τ (walkLanes op f fl W πL)
    walkL-⊕ op f fl W (this-lane ρ)  τ = walk-⊕ ρ τ _
    walkL-⊕ op f fl W (next-lane πL) τ = walkL-⊕ op f fl W πL τ

  -- A path one operator long.
  mutual
    data One {h} : ∀ {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} → Path t u → Set₁ where
      one-map    : ∀ {Δ A B} {f : A → B} {t : Sub h Δ A} → One (in-map {f = f} {t = t} here)
      one-scan   : ∀ {Δ A B} {f : B → A → B} {r} {t : Sub h Δ A} → One (in-scan {f = f} {r} {t = t} here)
      one-take   : ∀ {Δ A} {i p c k tk} {t : Sub h Δ A} → One (in-take {i = i} {p} {c} {k} {tk} {t = t} here)
      one-outer  : ∀ {Δ A B} {op f fl oc k r pl} {t : Sub h Δ A} {ls : List (Lane h Δ B)} → One (in-outer {op = op} {f} {fl} {oc} {k} {r} {pl} {t = t} {ls} here)
      one-lanes  : ∀ {Δ A B} {op f fl oc k r pl} {t : Sub h Δ A} {ls : List (Lane h Δ B)} {u : Sub h Δ B} {πL : PathLanes ls u}
                 → OneLane πL → One (in-lanes {op = op} {f} {fl} {oc} {k} {r} {pl} {t = t} πL)
      one-source : ∀ {Δ A B} {Sj c b kb k fd e rp rt} {t : Sub h Δ A} {bd : Sub h (A ∷ Δ) B} → One (in-source {S = Sj} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {t = t} {bd} here)
      one-body   : ∀ {Δ A B} {Sj c b kb k fd e rp rt} {t : Sub h Δ A} {bd : Sub h (A ∷ Δ) B} → One (in-body {S = Sj} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {t = t} {bd} here)
      one-defer  : ∀ {Δ A} {k} {t : Sub h Δ A} → One (in-defer {k = k} {t = t} here)

    data OneLane {h} : ∀ {Δ B} {ls : List (Lane h Δ B)} {u : Sub h Δ B} → PathLanes ls u → Set₁ where
      one-this : ∀ {Δ B} {c k} {t : Sub h Δ B} {ls} → OneLane (this-lane {c = c} {k} {t = t} {ls} here)
      one-next : ∀ {Δ B} {l} {ls : List (Lane h Δ B)} {u : Sub h Δ B} {πL : PathLanes ls u} → OneLane πL → OneLane (next-lane {l = l} πL)

  -- A path read from its far end: none, or a path and one operator more.
  data Last {h Δ A} {t : Sub h Δ A} : ∀ {Δ′ A′} {v : Sub h Δ′ A′} → Path t v → Set₁ where
    whole : Last here
    snoc  : ∀ {Δ′ A′ Δ″ A″} {u : Sub h Δ′ A′} {v : Sub h Δ″ A″} (ρ : Path t u) (s : Path u v) → One s → Last (ρ ⊕ s)

  data LastL {h Δ B} {ls : List (Lane h Δ B)} : ∀ {Δ′ A′} {v : Sub h Δ′ A′} → PathLanes ls v → Set₁ where
    oneL  : ∀ {v : Sub h Δ B} {πL : PathLanes ls v} → OneLane πL → LastL πL
    snocL : ∀ {Δ′ A′ Δ″ A″} {u : Sub h Δ′ A′} {v : Sub h Δ″ A″} (πL : PathLanes ls u) (s : Path u v) → One s → LastL (πL ⊕ᴸ s)

  mutual
    view : ∀ {h Δ A Δ′ A′} {t : Sub h Δ A} {v : Sub h Δ′ A′} (σ : Path t v) → Last σ
    view here = whole
    view (in-map p) with view p
    ... | whole      = snoc here (in-map here) one-map
    ... | snoc ρ s o = snoc (in-map ρ) s o
    view (in-scan p) with view p
    ... | whole      = snoc here (in-scan here) one-scan
    ... | snoc ρ s o = snoc (in-scan ρ) s o
    view (in-take p) with view p
    ... | whole      = snoc here (in-take here) one-take
    ... | snoc ρ s o = snoc (in-take ρ) s o
    view (in-outer p) with view p
    ... | whole      = snoc here (in-outer here) one-outer
    ... | snoc ρ s o = snoc (in-outer ρ) s o
    view (in-lanes p) with viewL p
    ... | oneL o      = snoc here (in-lanes p) (one-lanes o)
    ... | snocL ρ s o = snoc (in-lanes ρ) s o
    view (in-source p) with view p
    ... | whole      = snoc here (in-source here) one-source
    ... | snoc ρ s o = snoc (in-source ρ) s o
    view (in-body p) with view p
    ... | whole      = snoc here (in-body here) one-body
    ... | snoc ρ s o = snoc (in-body ρ) s o
    view (in-defer p) with view p
    ... | whole      = snoc here (in-defer here) one-defer
    ... | snoc ρ s o = snoc (in-defer ρ) s o

    viewL : ∀ {h Δ B Δ′ A′} {ls : List (Lane h Δ B)} {v : Sub h Δ′ A′} (πL : PathLanes ls v) → LastL πL
    viewL (this-lane p) with view p
    ... | whole      = oneL one-this
    ... | snoc ρ s o = snocL (this-lane ρ) s o
    viewL (next-lane p) with viewL p
    ... | oneL o      = oneL (one-next o)
    ... | snocL ρ s o = snocL (next-lane ρ) s o

  -- How many operators a path passes.
  mutual
    height : ∀ {h Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} → Path t u → ℕ
    height here          = 0
    height (in-map p)    = suc (height p)
    height (in-scan p)   = suc (height p)
    height (in-take p)   = suc (height p)
    height (in-outer p)  = suc (height p)
    height (in-lanes p)  = heightL p
    height (in-source p) = suc (height p)
    height (in-body p)   = suc (height p)
    height (in-defer p)  = suc (height p)

    heightL : ∀ {h Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} → PathLanes ls u → ℕ
    heightL (this-lane p) = suc (height p)
    heightL (next-lane p) = heightL p

  mutual
    height-⊕ : ∀ {h Δ A Δ′ A′ Δ″ A″} {t : Sub h Δ A} {u : Sub h Δ′ A′} {v : Sub h Δ″ A″} (ρ : Path t u) (τ : Path u v)
             → height (ρ ⊕ τ) ≡ height ρ + height τ
    height-⊕ here          τ = refl
    height-⊕ (in-map ρ)    τ = cong suc (height-⊕ ρ τ)
    height-⊕ (in-scan ρ)   τ = cong suc (height-⊕ ρ τ)
    height-⊕ (in-take ρ)   τ = cong suc (height-⊕ ρ τ)
    height-⊕ (in-outer ρ)  τ = cong suc (height-⊕ ρ τ)
    height-⊕ (in-lanes πL) τ = heightL-⊕ πL τ
    height-⊕ (in-source ρ) τ = cong suc (height-⊕ ρ τ)
    height-⊕ (in-body ρ)   τ = cong suc (height-⊕ ρ τ)
    height-⊕ (in-defer ρ)  τ = cong suc (height-⊕ ρ τ)

    heightL-⊕ : ∀ {h Δ B Δ′ A′ Δ″ A″} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} {v : Sub h Δ″ A″} (πL : PathLanes ls u) (τ : Path u v)
              → heightL (πL ⊕ᴸ τ) ≡ heightL πL + height τ
    heightL-⊕ (this-lane ρ)  τ = cong suc (height-⊕ ρ τ)
    heightL-⊕ (next-lane πL) τ = heightL-⊕ πL τ

  mutual
    height-one : ∀ {h Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} {s : Path t u} → One s → height s ≡ 1
    height-one one-map       = refl
    height-one one-scan      = refl
    height-one one-take      = refl
    height-one one-outer     = refl
    height-one (one-lanes o) = heightL-one o
    height-one one-source    = refl
    height-one one-body      = refl
    height-one one-defer     = refl

    heightL-one : ∀ {h Δ B} {ls : List (Lane h Δ B)} {u : Sub h Δ B} {πL : PathLanes ls u} → OneLane πL → heightL πL ≡ 1
    heightL-one one-this     = refl
    heightL-one (one-next o) = heightL-one o

  one-lower : ∀ {h Δ A Δ′ A′ Δ″ A″} {t : Sub h Δ A} {u : Sub h Δ′ A′} {v : Sub h Δ″ A″} (ρ : Path t u) {s : Path u v} → One s
            → height ρ < height (ρ ⊕ s)
  one-lower ρ {s} o = subst (height ρ <_) (sym (trans (height-⊕ ρ s) (cong (height ρ +_) (height-one o)))) (m<m+n (height ρ) ≤-refl)

  -- Whether the observer an `of` at the path's end emits to reads open,
  -- from the root's open record down: a kill switch or a lane's cut
  -- closes it, a connect's subject reads afresh.
  mutual
    opened : ∀ {h} (H : Heapᴹ h) {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} → Bool → Path t u → Bool
    opened H o here                       = o
    opened H o (in-map p)                 = opened H o p
    opened H o (in-scan p)                = opened H o p
    opened H o (in-take {c = c} p)        = opened H (At.val H (Kit.live c) ∧ o) p
    opened H o (in-outer {oc = oc} p)     = opened H (At.val H (Kit.live oc) ∧ o) p
    opened H o (in-lanes p)               = openedL H o p
    opened H o (in-source {S = Sj} p)     = opened H (not (At.val H (Subject.closed Sj))) p
    opened H o (in-body p)                = opened H o p
    opened H o (in-defer p)               = opened H o p

    openedL : ∀ {h} (H : Heapᴹ h) {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} → Bool → PathLanes ls u → Bool
    openedL H o (this-lane {c = c} p) = opened H (At.val H (Kit.live c) ∧ o) p
    openedL H o (next-lane p)         = openedL H o p

  -- What climbs a path: a value, or an end with the calls `ks` owed
  -- after it.
  data Signal {h} (T : Sub h [] R) (A : Set) : Set₁ where
    sends  : A → Signal T A
    closes : List (Call T) → Signal T A

  -- The calls owed past a signal.
  owed : ∀ {h} {T : Sub h [] R} {A} → Signal T A → List (Call T)
  owed (sends _)   = []
  owed (closes ks) = ks

  -- What a signal makes of the observer it is told to.
  said : ∀ {h} {T : Sub h [] R} {A} → Observer A h → Signal T A → Act h ⊤
  said o (sends y)   = Observer.next o y
  said o (closes ks) = Observer.complete o >>ᴬ ⟦ ks ⟧ᶜ

  -- The node a signal reaches already past it, and the ghost's step the
  -- signal lifted along the path: a value leaves the node standing, an
  -- end leaves it gone.
  Passed : ∀ {h} (H : Heapᴹ h) (q : Pos) (g : U.Node [] R) {T : Sub h [] R} {Δ A} {v : Sub h Δ A} → Path T v → Signal T A → Set₁
  Passed H q g {Δ = Δ} {A} {v} σ (sends y) =
    Σ (U.Node Δ A) λ c′ → At.part H v ≡ just c′ × Σ (U.Step [] R) λ S → Lifts H σ (U.outˢ q y c′) S × U.step g ≡ S
  Passed H q g {v = v} σ (closes _) =
    At.part H v ≡ nothing × Σ (U.Step [] R) λ S → Lifts H σ (U.endˢ q) S × U.step g ≡ S

  -- A SIGNAL ON ITS WAY UP: `sg` about to be told to the observer the
  -- path walks to, the agenda empty above the stack but for the calls
  -- the signal owes.
  record Calling (g : U.Node [] R) (ℓ : Load) (m₁ : Mach) {Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {v : Sub (Conf.world (Mach.conf m₁)) Δ A}
                 (σ : Path T v) (sg : Signal T A) : Set₁ where
    field
      sane    : Sane [] g
      placed  : Placed g []
      {w}     : World
      {ϑ}     : w ⊑ Conf.world (Mach.conf m₁)
      {act}   : Act (Conf.world (Mach.conf m₁)) ⊤
      {K}     : Stack w ⊤
      ctl     : Conf.ctl (Mach.conf m₁) ≡ run act ϑ K
      code    : act ≗ said (Here.obs (walk σ top)) sg
      stack   : StackAs T (Conf.pos (Mach.conf m₁)) ϑ K (Mach.bursts m₁)
      lifted  : Passed (Conf.heap (Mach.conf m₁)) (Conf.pos (Mach.conf m₁)) g σ sg
      owned   : Owned (Conf.heap (Mach.conf m₁)) T (runAs (owed sg) (≗-refl _) stack)
      kernels : Kernels (Conf.heap (Mach.conf m₁)) T
      meaning : Meaning (Conf.heap (Mach.conf m₁)) T
      queue   : Queue (Conf.heap (Mach.conf m₁)) (Conf.pos (Mach.conf m₁)) (Mach.clock m₁) (Mach.timers m₁) T
      books   : Books T (runAs (owed sg) (≗-refl _) stack) m₁
      sorted  : Σ Pos λ lo → WellMach lo m₁
      behind  : Each (Conf.heap (Mach.conf m₁)) (Heads (Conf.pos (Mach.conf m₁))) T
      lingers : Lingers (Conf.heap (Mach.conf m₁)) T
      flags   : DoneBy (Conf.heap (Mach.conf m₁)) T (outers σ)
      kept    : load m₁ T ≼ ℓ

  -- Done flags read as they were, one step up a path entering no outer.
  done-up : ∀ {h} {H : Heapᴹ h} {T : Sub h [] R} {Δ A Δ′ A′} {x : Sub h Δ A} {v : Sub h Δ′ A′} (ρ : Path T x) (c : Path x v)
          → outers c ≡ [] → DoneBy H T (outers (ρ ⊕ c)) → DoneBy H T (outers ρ)
  done-up {H = H} {T = T} ρ c e d = subst (DoneBy H T) (trans (outers-⊕ ρ c) (trans (cong (outers ρ ++_) e) (++-identityʳ (outers ρ)))) d

  -- The same call, the signal restated at another path, owing as much.
  recall : ∀ {g ℓ m₁ Δ A Δ′ A′} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {v : Sub (Conf.world (Mach.conf m₁)) Δ A}
             {v′ : Sub (Conf.world (Mach.conf m₁)) Δ′ A′} {σ : Path T v} {sg : Signal T A} (cl : Calling g ℓ m₁ σ sg) {σ′ : Path T v′} {sg′ : Signal T A′}
         → owed sg′ ≡ owed sg
         → Calling.act cl ≗ said (Here.obs (walk σ′ top)) sg′
         → Passed (Conf.heap (Mach.conf m₁)) (Conf.pos (Mach.conf m₁)) g σ′ sg′
         → DoneBy (Conf.heap (Mach.conf m₁)) T (outers σ′)
         → Calling g ℓ m₁ σ′ sg′
  recall {m₁ = m₁} {T = T} cl ow cd lf dn = record
    { sane = Calling.sane cl ; placed = Calling.placed cl ; ctl = Calling.ctl cl ; code = cd ; stack = Calling.stack cl ; lifted = lf
    ; owned = subst (λ ks → Owned (Conf.heap (Mach.conf m₁)) T (runAs ks (≗-refl _) (Calling.stack cl))) (sym ow) (Calling.owned cl)
    ; kernels = Calling.kernels cl ; meaning = Calling.meaning cl ; queue = Calling.queue cl
    ; books = subst (λ ks → Books T (runAs ks (≗-refl _) (Calling.stack cl)) m₁) (sym ow) (Calling.books cl)
    ; sorted = Calling.sorted cl ; behind = Calling.behind cl ; lingers = Calling.lingers cl ; flags = dn ; kept = Calling.kept cl }

  -- The same call, held to a load no lighter.
  relevel : ∀ {g ℓ ℓ′ m₁ Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {v : Sub (Conf.world (Mach.conf m₁)) Δ A} {σ : Path T v} {sg : Signal T A}
          → Calling g ℓ′ m₁ σ sg → ℓ′ ≼ ℓ → Calling g ℓ m₁ σ sg
  relevel cl le = record
    { sane = Calling.sane cl ; placed = Calling.placed cl ; ctl = Calling.ctl cl ; code = Calling.code cl ; stack = Calling.stack cl
    ; lifted = Calling.lifted cl ; owned = Calling.owned cl ; kernels = Calling.kernels cl ; meaning = Calling.meaning cl
    ; queue = Calling.queue cl ; books = Calling.books cl ; sorted = Calling.sorted cl ; behind = Calling.behind cl ; lingers = Calling.lingers cl
    ; flags = Calling.flags cl
    ; kept = ≼-trans (Calling.kept cl) le }

  -- A signal one operator higher, the path shorter, the load at most `ℓ`.
  data Rises (g : U.Node [] R) (ℓ : Load) (m₁ : Mach) {Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {v : Sub (Conf.world (Mach.conf m₁)) Δ A}
             (σ : Path T v) : Set₁ where
    rises : ∀ {m₂ Δ′ A′} {T′ : Sub (Conf.world (Mach.conf m₂)) [] R} {v′ : Sub (Conf.world (Mach.conf m₂)) Δ′ A′} {σ′ : Path T′ v′} {sg′ : Signal T′ A′}
          → m₁ ⇝ m₂ → height σ′ < height σ → Calling g ℓ m₂ σ′ sg′ → Rises g ℓ m₁ σ

  -- One operator called: a re-entry configuration reached, or a signal
  -- one operator higher, the path shorter.
  data Called {g m} (st : Strong g m) (m₁ : Mach) {Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {v : Sub (Conf.world (Mach.conf m₁)) Δ A}
              (σ : Path T v) : Set₁ where
    landed : Hopped st m₁ → Called st m₁ σ
    rose   : ∀ {m₂ Δ′ A′} {T′ : Sub (Conf.world (Mach.conf m₂)) [] R} {v′ : Sub (Conf.world (Mach.conf m₂)) Δ′ A′} {σ′ : Path T′ v′} {sg′ : Signal T′ A′}
           → m₁ ⇝ m₂ → height σ′ < height σ → Calling g (loadOf st) m₂ σ′ sg′ → Called st m₁ σ

  -- Some signal on its way up.
  data Aloft (g : U.Node [] R) (ℓ : Load) (m₁ : Mach) : Set₁ where
    aloft : ∀ {Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {v : Sub (Conf.world (Mach.conf m₁)) Δ A} {σ : Path T v} {sg : Signal T A}
          → Calling g ℓ m₁ σ sg → Aloft g ℓ m₁

  -- A hop's machine sorted.
  hop-sorted : ∀ {g m m′ m₀} → Carried g m → step m ≡ silent m′ → m′ ⇝ m₀ → Σ Pos λ lo → WellMach lo m₀
  hop-sorted cr e p = sorted-⇝ (Carried.sorted cr) (then e p)

  -- The run moved back: every node still heads no earlier.
  heads-back : ∀ {q p Γ A} {c : U.Node Γ A} → q <ᵖ p ≡ true → Heads p c → Heads q c
  heads-back {q} {p} qp hd hk with hd hk
  ... | inj₁ refl = inj₂ qp
  ... | inj₂ pk   = inj₂ (<ᵖ-trans q p _ qp pk)

  each-back : ∀ {h} {H : Heapᴹ h} {t : Sub h [] R} {q p} → q <ᵖ p ≡ true → Each H (Heads p) t → Each H (Heads q) t
  each-back qp ev = record
    { parts = λ ψ sψ {c} e → heads-back {c = c} qp (Each.parts ev ψ sψ e)
    ; pools = λ {pl = pl} ψ sψ e → heads-back {c = pl} qp (Each.pools ev ψ sψ e)
    ; rests = λ {rt = rt} ψ sψ e n j → heads-back {c = rt} qp (Each.rests ev ψ sψ e n j) }

  hopped-pre : ∀ {g m m′ m₁} {st : Strong g m} → m′ ⇝ m₁ → Hopped st m₁ → Hopped st m′
  hopped-pre path (g″ , m₀ , path′ , st₀ , gn) = g″ , m₀ , ⇝-trans path path′ , st₀ , gn
