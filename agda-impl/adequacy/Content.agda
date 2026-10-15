{-# OPTIONS --guardedness #-}

-- CONTENT: the root's record is the meaning's events, as a set.
-- Sortedness (`adequacy.Sorted`) says nothing of WHAT arrives; this says
-- nothing of the ORDER, so neither proof reads the other.
--
-- A GHOST: the meaning's own configuration (`denotation.Unfold`'s
-- `Node`), which the machine's configuration runs.  What is still to be
-- delivered is the ghost's residual, its meaning (`U.meaning`); at the
-- launch the ghost is the program subscribed there, so the
-- residual is the meaning's events (`begun`, by `subscribed`).  Each step
-- keeps the residual or delivers a least event of it (`Shows`).  No step
-- of the machine is matched to a step of a stepper.  Only the run's
-- re-entry configurations are related to the ghost (`Strong`); every
-- other is reached from one by its own silent steps.
module adequacy.Content where

open import Data.List using (List; []; _∷_; _++_; [_]; length)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.Any.Properties using (++⁺ʳ; ++⁻)
import Data.List.Relation.Unary.Any as Any
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Nat.Properties using (suc-injective; ≤-refl; ≤-trans; ≤-pred; m<n⇒m<1+n; m<m+n)
open import Data.List.Relation.Unary.All using (All; []; _∷_; map)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Data.List.Relation.Unary.Linked using (Linked; _∷_; tail)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴸ_)
open import Level using (lift)
open import Data.Maybe using (Maybe; just; nothing; is-just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _+_)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (WellFounded)
open import Data.Product.Relation.Binary.Lex.Strict using (×-Lex; ×-wellFounded)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import denotation.MonotonicList using (Events; Events∞; Pos; Time; Timeline; tick; out; skip; end; hush; observe; root; Agree; out⁼;
  skip⁼; end⁼; agree; agree-sym; agree-trans; agree-refl; at; ix; _<ᵖ_; <ᵖ-tick; <ᵖ-trans)
import denotation.Unfold as U
open import denotation.MonotonicList using () renaming (sub to subᴾ)
open import denotation.Compositional using ([]ᵉ)
open import adequacy.Sorted using (_≤ᵖ_; module Sorting)
open import operation.Machine using (module Machine)
open import adequacy.Record using (module Recording)
open import adequacy.Strong using (module Strongly)
open import adequacy.Moves using (module Moving)
open import adequacy.Sane using (Sane)
open import adequacy.Placed using (Placed)
open import adequacy.Stepper using (_≃_; []; os; afterᴱ; placed-after; Placedˢ)
open import denotation.Denote using (⟦_⟧)
import Tree as T
open import operation.PureObservable using (PureObs; Out; note; Pureᴾ; module Pure)
open import operation.AbstractObservable using (module Heap; module Run) renaming (module Machine to Shared)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_; not)

open Events∞

module Honesty (R : Set) where
  open Machine R using (Mach; mach; Playing; Step; silent; value; complete; drained; step; trace; shown; reading; begin; launch; Read; read; feed)
  open Shared Timeline (Out R) using (Conf; Heapᴹ; Stack; ⟨_,_,_⟩; held; run; asking; bottom; spent?) renaming (go to goᴵ)
  open Heap using (World; _⊑_; Handle)
  open Sorting R using (WellMach; WellStep; silentʷ; valueʷ; preserve)
  open Run (Pureᴾ R) using (Act; Observer; Subject; module Kit; module FlatKit)
  open Recording R using (silent-keeps; value-notes)
  open Strongly R using (Strong; strong-begin; Carried; Books; carried; closing; Sub; pendingˢ; coldˢ; ofˢ; doneˢ; mapˢ; scanˢ; takeWhileˢ;
    flatMapˢ; connectˢ; joinˢ; deferˢ; Lane; lane; here; module At; Queue; Kernels; Meaning; fired; Owned; Path; Spot; spot; done≗;
    Call; emitC; kontC; take1C; take2C; bodyC; feedC; finC; srcC; Taking; taking; taken; feeding; finishing; PathLanes; this-lane; next-lane;
    in-map; in-scan; in-take; in-outer; in-lanes; in-source; in-body; in-defer; _⊕_; _⊕ᴸ_; Here; walk; walkLanes; top; _≗_; eff≗)
  open Strongly.Against R using (calmAs; noteAs; runAs; subAs; burstAs; firesAs; playsAs; overAs; bottomAs; restAs; backAs; reholdAs; bottomᴴ; restᴴ; BurstAs;
    StackAs; CtlAs; agenda; bursts; begins; sources; stackJobs; stackBursts; burstSpots) renaming (Placed to Placedᴬ)
  open Pure R using (End; finished; dry; cutOff; recorder; Timer; cascade)
  open Moving R using (pend; plant; planted; Waits; waits; pendings-path; part-plant; pend-plant; names-plant; subjects-plant;
    joiners-plant; holds-plant; gated-plant; fed-plant; timed-pop; owned-pop; later; true≢false)
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
  tail-out (out⁼ x) = x

  tail-skip : ∀ {n k} {l r : Events∞ R} → Agree (suc n) (skip k l) (skip k r) → Agree n (force l) (force r)
  tail-skip (skip⁼ x) = x

  -- Events alike at every depth hold the same events.
  has-agree : ∀ {x y k b} → (∀ n → Agree n x y) → Has x k b → Has y k b
  has-agree ag h with ag 1
  has-agree ag atOut        | out⁼ _  = atOut
  has-agree ag atEnd        | end⁼    = atEnd
  has-agree ag (pastOut h)  | out⁼ _  = pastOut (has-agree (λ n → tail-out (ag (suc n))) h)
  has-agree ag (pastSkip h) | skip⁼ _ = pastSkip (has-agree (λ n → tail-skip (ag (suc n))) h)

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

  -- `m` runs silently to `m′`.
  data _⇝_ (m : Mach) : Mach → Set₁ where
    now  : m ⇝ m
    then : ∀ {m₁ m′} → step m ≡ silent m₁ → m₁ ⇝ m′ → m ⇝ m′

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

  -- `y` is `x` past none or more of its leading skips, alike at every
  -- depth at each stage.  As sets the two are the same; as a measure a
  -- skip dropped is progress, which `≋` cannot see.
  data Past : Events R → Events R → Set where
    agrees  : ∀ {x y} → (∀ n → Agree n x y) → Past x y
    skipped : ∀ {x y k r} → (∀ n → Agree n x (skip k r)) → Past (force r) y → Past x y

  skip-same : ∀ {k r} → skip k r ≋ force r
  skip-same = (λ { (pastSkip h) → h }) , pastSkip

  past-same : ∀ {x y} → Past x y → x ≋ y
  past-same (agrees ag)    = same-agree ag
  past-same (skipped ag p) = ≋-trans (same-agree ag) (≋-trans skip-same (past-same p))

  past-pre : ∀ {x y z} → (∀ n → Agree n x y) → Past y z → Past x z
  past-pre ag (agrees ag′)    = agrees λ n → agree-trans (ag n) (ag′ n)
  past-pre ag (skipped ag′ p) = skipped (λ n → agree-trans (ag n) (ag′ n)) p

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
  weight (subAs _ _ K)   = suc (work K)
  weight (burstAs _ _ K) = work K

  -- THE WORK LEFT AT A RE-ENTRY CONFIGURATION, in order: subscriptions
  -- owed, timers queued, bursts held, the control's own.
  Measure : Set
  Measure = ℕ × ℕ × ℕ × ℕ

  _≺_ : Measure → Measure → Set
  _≺_ = ×-Lex _≡_ _<_ (×-Lex _≡_ _<_ (×-Lex _≡_ _<_ _<_))

  ≺-wf : WellFounded _≺_
  ≺-wf = ×-wellFounded <-wellFounded (×-wellFounded <-wellFounded (×-wellFounded <-wellFounded <-wellFounded))

  measure : ∀ {g m} → Strong g m → Measure
  measure {m = m} (carried cr) = pend (Carried.tree cr) , length (Mach.timers m) , length (Mach.bursts m) , weight (Carried.ctlAs cr)
  measure (closing _ _ _ _ _)  = 0 , 0 , 0 , 0

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

  -- THE STEPPER IS THE MEANING, skips included, of a run's configuration
  -- (`Sane`): what the ghost's step shows, then the meaning of the ghost
  -- it leaves.  A joiner told its end while its source runs is fed the
  -- source's values by the stepper and shows them, where the meaning
  -- reads it as its end alone.
  --
  -- REFUTED: 3e2af71f stated of every node, by a told joiner under a live source
  step-skips : ∀ g → Sane [] g → Placed g [] → residual g ≃ after (U.step g)
  step-skips g sn pl = os g [] tt sn pl tt

  -- `m`, carried, runs silently on to a re-entry configuration it gains.
  Hops : ∀ {g m} → Carried g m → Set₁
  Hops {m = m} cr = ∀ {m′} → step m ≡ silent m′ → Hopped (carried cr) m′

  -- What the control is about to run: a subscription begun, or the
  -- agenda's first call.
  opening : ∀ {h} {t : Sub h [] R} {p c bs} → CtlAs t p c bs → Bool
  opening (subAs _ _ _) = true
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

  -- The earliest lane's step, at `k`, ahead of the outer's.
  LaneFirst : ∀ {Γ A} → Maybe (U.Node Γ A) → Pos → Set
  LaneFirst nothing  k = ⊤
  LaneFirst (just o) k = ∀ {k′} → U.headˢ (U.step o) ≡ just k′ → k′ <ᵖ k ≡ false

  -- THE GHOST'S STEP, FROM A STEP AT THE PATH'S END: `s` at the node the
  -- path reaches, `S` at the node it starts from, each operator on the
  -- way the meaning's own step, its order said by the side condition
  -- that picks it.  A lane's step comes with the lanes before and after
  -- it.
  mutual
    data Lifts {h} (H : Heapᴹ h) : ∀ {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} → Path t u → U.Step Δ′ A′ → U.Step Δ A → Set₁ where
      lifts-here   : ∀ {Δ A} {t : Sub h Δ A} {s} → Lifts H (here {t = t}) s s
      lifts-map    : ∀ {Δ A B Δ′ C} {f : A → B} {t : Sub h Δ A} {u : Sub h Δ′ C} {ρ : Path t u} {s S}
                   → Lifts H ρ s S → Lifts H (in-map {f = f} ρ) s (U.mapˢ f S)
      lifts-scan   : ∀ {Δ A B Δ′ C} {f : B → A → B} {r} {t : Sub h Δ A} {u : Sub h Δ′ C} {ρ : Path t u} {s S}
                   → Lifts H ρ s S → Lifts H (in-scan {f = f} {r} ρ) s (U.scanˢ f (At.val H r) S)
      lifts-take   : ∀ {Δ A Δ′ C} {i p c k} {t : Sub h Δ A} {u : Sub h Δ′ C} {ρ : Path t u} {s S}
                   → At.val H (Kit.live c) ≡ true → Lifts H ρ s S → Lifts H (in-take {i = i} {p} {c} {k} {taking} ρ) s (U.takeWhileˢ i p S)
      lifts-outer  : ∀ {Δ A B Δ′ C} {op f fl oc k r} {t : Sub h Δ A} {ls : List (Lane h Δ B)} {u : Sub h Δ′ C} {ρ : Path t u} {s S}
                   → OuterFirst S (At.partLanes H ls) → Lifts H ρ s S
                   → Lifts H (in-outer {op = op} {f} {fl} {oc} {k} {r} {ls = ls} ρ) s
                       (U.outerˢ op (λ a q → U.subscribe (f a) q) S (At.partLanes H ls) (At.val H (FlatKit.Flat.queue fl)))
      lifts-lanes  : ∀ {Δ A B Δ′ C} {op f fl oc k r} {t : Sub h Δ A} {ls : List (Lane h Δ B)} {u : Sub h Δ′ C} {πL : PathLanes ls u}
                       {s bs l S as q}
                   → LiftsLane H πL s bs S as → U.earliest (At.partLanes H ls) ≡ U.found q bs l S as → LaneFirst (At.part H t) q
                   → Lifts H (in-lanes {op = op} {f} {fl} {oc} {k} {r} {t = t} πL) s
                       (U.laneˢ op (λ a q → U.subscribe (f a) q) (At.part H t) bs S as (At.val H (FlatKit.Flat.queue fl)))
      lifts-source : ∀ {Δ A B Δ′ C} {Sj c b kb k fd e} {t : Sub h Δ A} {bd : Sub h (A ∷ Δ) B} {u : Sub h Δ′ C} {ρ : Path t u} {s S c₀ b₀}
                   → At.part H t ≡ just c₀ → At.part H bd ≡ just b₀ → SourceFirst S (U.step b₀) → Lifts H ρ s S
                   → Lifts H (in-source {S = Sj} {c} {b} {kb} {k} {fd} {e} {bd = bd} ρ) s (U.sourceˢ b₀ (U.step b₀) c₀ S)
      lifts-body   : ∀ {Δ A B Δ′ C} {Sj c b kb k fd e} {t : Sub h Δ A} {bd : Sub h (A ∷ Δ) B} {u : Sub h Δ′ C} {ρ : Path bd u} {s S c₀}
                   → At.part H t ≡ just c₀ → BodyFirst (U.step c₀) S → Lifts H ρ s S
                   → Lifts H (in-body {S = Sj} {c} {b} {kb} {k} {fd} {e} {t = t} ρ) s (U.bodyˢ (U.live c₀) S)
      lifts-shut   : ∀ {Δ A B Δ′ C} {Sj c b kb k fd e} {t : Sub h Δ A} {bd : Sub h (A ∷ Δ) B} {u : Sub h Δ′ C} {ρ : Path bd u} {s S c₀}
                   → At.part H t ≡ nothing → e ≡ just c₀ → Lifts H ρ s S
                   → Lifts H (in-body {S = Sj} {c} {b} {kb} {k} {fd} {e} {t = t} ρ) s (U.shutˢᵗ c₀ S)
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
    lifts-split (in-outer ρ)  τ (lifts-outer of L)         with lifts-split ρ τ L
    ... | S′ , Lτ , Lρ = S′ , Lτ , lifts-outer of Lρ
    lifts-split (in-lanes πL) τ (lifts-lanes L ea lf)      with liftsL-split πL τ L
    ... | S′ , Lτ , Lρ = S′ , Lτ , lifts-lanes Lρ ea lf
    lifts-split (in-source ρ) τ (lifts-source pt pb sf L)  with lifts-split ρ τ L
    ... | S′ , Lτ , Lρ = S′ , Lτ , lifts-source pt pb sf Lρ
    lifts-split (in-body ρ)   τ (lifts-body pt bf L)       with lifts-split ρ τ L
    ... | S′ , Lτ , Lρ = S′ , Lτ , lifts-body pt bf Lρ
    lifts-split (in-body ρ)   τ (lifts-shut pt e L)        with lifts-split ρ τ L
    ... | S′ , Lτ , Lρ = S′ , Lτ , lifts-shut pt e Lρ
    lifts-split (in-defer ρ)  τ (lifts-defer L)            with lifts-split ρ τ L
    ... | S′ , Lτ , Lρ = S′ , Lτ , lifts-defer Lρ

    liftsL-split : ∀ {h} {H : Heapᴹ h} {Δ B Δ′ A′ Δ″ A″} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} {v : Sub h Δ″ A″}
                   (πL : PathLanes ls u) (τ : Path u v) {s bs S as}
                 → LiftsLane H (πL ⊕ᴸ τ) s bs S as → Σ (U.Step Δ′ A′) λ S′ → Lifts H τ s S′ × LiftsLane H πL S′ bs S as
    liftsL-split (this-lane ρ)  τ (lifts-this lv L) with lifts-split ρ τ L
    ... | S′ , Lτ , Lρ = S′ , Lτ , lifts-this lv Lρ
    liftsL-split (next-lane πL) τ (lifts-next L)    with liftsL-split πL τ L
    ... | S′ , Lτ , Lρ = S′ , Lτ , lifts-next Lρ

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
      one-outer  : ∀ {Δ A B} {op f fl oc k r} {t : Sub h Δ A} {ls : List (Lane h Δ B)} → One (in-outer {op = op} {f} {fl} {oc} {k} {r} {t = t} {ls} here)
      one-lanes  : ∀ {Δ A B Δ′ C} {op f fl oc k r} {t : Sub h Δ A} {ls : List (Lane h Δ B)} {u : Sub h Δ′ C} {πL : PathLanes ls u}
                 → OneLane πL → One (in-lanes {op = op} {f} {fl} {oc} {k} {r} {t = t} πL)
      one-source : ∀ {Δ A B} {Sj c b kb k fd e} {t : Sub h Δ A} {bd : Sub h (A ∷ Δ) B} → One (in-source {S = Sj} {c} {b} {kb} {k} {fd} {e} {t = t} {bd} here)
      one-body   : ∀ {Δ A B} {Sj c b kb k fd e} {t : Sub h Δ A} {bd : Sub h (A ∷ Δ) B} → One (in-body {S = Sj} {c} {b} {kb} {k} {fd} {e} {t = t} {bd} here)
      one-defer  : ∀ {Δ A} {k} {t : Sub h Δ A} → One (in-defer {k = k} {t = t} here)

    data OneLane {h} : ∀ {Δ B Δ′ C} {ls : List (Lane h Δ B)} {u : Sub h Δ′ C} → PathLanes ls u → Set₁ where
      one-this : ∀ {Δ B} {c k} {t : Sub h Δ B} {ls} → OneLane (this-lane {c = c} {k} {t = t} {ls} here)
      one-next : ∀ {Δ B Δ′ C} {l} {ls : List (Lane h Δ B)} {u : Sub h Δ′ C} {πL : PathLanes ls u} → OneLane πL → OneLane (next-lane {l = l} πL)

  -- A path read from its far end: none, or a path and one operator more.
  data Last {h Δ A} {t : Sub h Δ A} : ∀ {Δ′ A′} {v : Sub h Δ′ A′} → Path t v → Set₁ where
    whole : Last here
    snoc  : ∀ {Δ′ A′ Δ″ A″} {u : Sub h Δ′ A′} {v : Sub h Δ″ A″} (ρ : Path t u) (s : Path u v) → One s → Last (ρ ⊕ s)

  data LastL {h Δ B} {ls : List (Lane h Δ B)} : ∀ {Δ′ A′} {v : Sub h Δ′ A′} → PathLanes ls v → Set₁ where
    oneL  : ∀ {Δ′ A′} {v : Sub h Δ′ A′} {πL : PathLanes ls v} → OneLane πL → LastL πL
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

    heightL-one : ∀ {h Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} {πL : PathLanes ls u} → OneLane πL → heightL πL ≡ 1
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

  isTaking : Taking → Bool
  isTaking taking = true
  isTaking _      = false

  -- Whether the ghost holds the path's end: every takeWhile live and
  -- taking, every lane live, every connect open.
  mutual
    seen : ∀ {h} (H : Heapᴹ h) {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} → Path t u → Bool
    seen H here                              = true
    seen H (in-map p)                        = seen H p
    seen H (in-scan p)                       = seen H p
    seen H (in-take {c = c} {tk = tk} p)     = At.val H (Kit.live c) ∧ isTaking tk ∧ seen H p
    seen H (in-outer p)                      = seen H p
    seen H (in-lanes p)                      = seenL H p
    seen H (in-source {bd = bd} p)           = is-just (At.part H bd) ∧ seen H p
    seen H (in-body {e = e} {t = t} p)       = (is-just (At.part H t) ∨ is-just e) ∧ seen H p
    seen H (in-defer p)                      = seen H p

    seenL : ∀ {h} (H : Heapᴹ h) {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} → PathLanes ls u → Bool
    seenL H (this-lane {c = c} p) = At.val H (Kit.live c) ∧ seen H p
    seenL H (next-lane p)         = seenL H p

  -- A VALUE ON ITS WAY UP: `y` about to be delivered to the observer
  -- the path walks to, the agenda empty above the stack.  The node it
  -- reaches already past the value, and the ghost's step the value
  -- lifted along the path.
  record Climbing (g : U.Node [] R) (m₁ : Mach) {Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {v : Sub (Conf.world (Mach.conf m₁)) Δ A}
                  (σ : Path T v) (y : A) : Set₁ where
    field
      sane    : Sane [] g
      placed  : Placed g []
      {w}     : World
      {ϑ}     : w ⊑ Conf.world (Mach.conf m₁)
      {act}   : Act (Conf.world (Mach.conf m₁)) ⊤
      {K}     : Stack w ⊤
      ctl     : Conf.ctl (Mach.conf m₁) ≡ run act ϑ K
      code    : act ≗ Observer.next (Here.obs (walk σ top)) y
      stack   : StackAs T (Conf.pos (Mach.conf m₁)) ϑ K (Mach.bursts m₁)
      lifted  : Σ (U.Node Δ A) λ c′ → At.part (Conf.heap (Mach.conf m₁)) v ≡ just c′
                × Σ (U.Step [] R) λ S → Lifts (Conf.heap (Mach.conf m₁)) σ (U.outˢ (Conf.pos (Mach.conf m₁)) y c′) S × U.step g ≡ S
      owned   : Owned (Conf.heap (Mach.conf m₁)) T (runAs [] (done≗ refl) stack)
      kernels : Kernels (Conf.heap (Mach.conf m₁)) T
      meaning : Meaning (Conf.heap (Mach.conf m₁)) T
      queue   : Queue (Conf.heap (Mach.conf m₁)) (Conf.pos (Mach.conf m₁)) (Mach.clock m₁) (Mach.timers m₁) T
      books   : Books T (runAs [] (done≗ refl) stack) m₁
      sorted  : Σ Pos λ lo → WellMach lo m₁

  -- The same climb, the value restated at another path.
  reclimb : ∀ {g m₁ Δ A Δ′ A′} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {v : Sub (Conf.world (Mach.conf m₁)) Δ A}
              {v′ : Sub (Conf.world (Mach.conf m₁)) Δ′ A′} {σ : Path T v} {y : A} (cl : Climbing g m₁ σ y) {σ′ : Path T v′} {y′ : A′}
          → Climbing.act cl ≗ Observer.next (Here.obs (walk σ′ top)) y′
          → Σ (U.Node Δ′ A′) (λ c′ → At.part (Conf.heap (Mach.conf m₁)) v′ ≡ just c′
              × Σ (U.Step [] R) λ S → Lifts (Conf.heap (Mach.conf m₁)) σ′ (U.outˢ (Conf.pos (Mach.conf m₁)) y′ c′) S × U.step g ≡ S)
          → Climbing g m₁ σ′ y′
  reclimb cl cd lf = record
    { sane = Climbing.sane cl ; placed = Climbing.placed cl ; ctl = Climbing.ctl cl ; code = cd ; stack = Climbing.stack cl ; lifted = lf
    ; owned = Climbing.owned cl ; kernels = Climbing.kernels cl ; meaning = Climbing.meaning cl ; queue = Climbing.queue cl
    ; books = Climbing.books cl ; sorted = Climbing.sorted cl }

  -- One operator climbed: a re-entry configuration reached, or the
  -- value one operator higher, the path shorter.
  data Climbed {g m} (st : Strong g m) (m₁ : Mach) {Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {v : Sub (Conf.world (Mach.conf m₁)) Δ A}
               (σ : Path T v) : Set₁ where
    landed : Hopped st m₁ → Climbed st m₁ σ
    rose   : ∀ {m₂ Δ′ A′} {T′ : Sub (Conf.world (Mach.conf m₂)) [] R} {v′ : Sub (Conf.world (Mach.conf m₂)) Δ′ A′} {σ′ : Path T′ v′} {y′ : A′}
           → m₁ ⇝ m₂ → height σ′ < height σ → Climbing g m₂ σ′ y′ → Climbed st m₁ σ

  -- Some value on its way up.
  data Aloft (g : U.Node [] R) (m₁ : Mach) : Set₁ where
    aloft : ∀ {Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {v : Sub (Conf.world (Mach.conf m₁)) Δ A} {σ : Path T v} {y : A}
          → Climbing g m₁ σ y → Aloft g m₁

  ⇝-trans : ∀ {m m₁ m₂} → m ⇝ m₁ → m₁ ⇝ m₂ → m ⇝ m₂
  ⇝-trans now          q = q
  ⇝-trans (then e p)   q = then e (⇝-trans p q)

  -- A hop's machine sorted.
  hop-sorted : ∀ {g m m′ m₀} → Carried g m → step m ≡ silent m′ → m′ ⇝ m₀ → Σ Pos λ lo → WellMach lo m₀
  hop-sorted cr e p = sorted-⇝ (Carried.sorted cr) (then e p)

  hopped-pre : ∀ {g m m′ m₁} {st : Strong g m} → m′ ⇝ m₁ → Hopped st m₁ → Hopped st m′
  hopped-pre path (g″ , m₀ , path′ , st₀ , gn) = g″ , m₀ , ⇝-trans path path′ , st₀ , gn

  postulate
    -- The turn, nothing held and no timer queued: the ghost shows
    -- nothing.
    turn-dry : ∀ {g m w} {σ : w ⊑ Conf.world (Mach.conf m)} → Carried g m → Conf.ctl (Mach.conf m) ≡ held σ bottom
             → Mach.bursts m ≡ [] → Mach.timers m ≡ [] → ∀ {k b} → Has (residual g) k b → ⊥

    -- A subscription begun at its pending node, its kernel run to the
    -- next re-entry state: its program smaller by what was begun, or
    -- past a defer's skip.
    sub-onward : ∀ {g m} (cr : Carried g m) → opening (Carried.ctlAs cr) ≡ true → Hops cr

    -- A spent `of`'s completion delivered at its end.
    emit-last : ∀ {g m} (cr : Carried g m) {Δ A p i} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i []))
              → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → Hops cr

    -- An `of` reading its observer closed: its burst over, nothing
    -- delivered.  The ghost must hold nothing of it.
    emit-shut : ∀ {g m} (cr : Carried g m) {Δ A p i x xs} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i (x ∷ xs)))
              → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → opened (Conf.heap (Mach.conf m)) true π ≡ false → Hops cr

    -- An `of` reading its observer open where the ghost does not hold it:
    -- a connect's source fed on past its body's end.
    emit-unseen : ∀ {g m} (cr : Carried g m) {Δ A p i x xs} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i (x ∷ xs)))
                → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → opened (Conf.heap (Mach.conf m)) true π ≡ true
                → seen (Conf.heap (Mach.conf m)) π ≡ false → Hops cr

    -- An `of` reading its observer open, its value handed on under the
    -- `of`'s scope: the `of` past it, the value on its way up, the
    -- ghost's step the value lifted.
    emit-run : ∀ {g m} (cr : Carried g m) {Δ A p i x xs} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i (x ∷ xs)))
             → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → opened (Conf.heap (Mach.conf m)) true π ≡ true
             → Lifts (Conf.heap (Mach.conf m)) π (U.step (U.ofᶜ p i (x ∷ xs))) (U.step g)
             → ∀ {m′} → step m ≡ silent m′ → Σ Mach λ m₁ → m′ ⇝ m₁ × Aloft g m₁

    -- The agenda's first call an open `of` the ghost holds: the ghost's
    -- step is that `of`'s, lifted.  Every side condition `Lifts` asks is
    -- an ordering claim: the value first among a connect's source and
    -- body, a flatMap's outer and lanes.  So the claim is that nothing
    -- else the ghost holds comes first: no call further down the agenda,
    -- no burst held or timer queued, no subscription owed.  The order
    -- the machine keeps is `Carried.sorted`'s: every frame `Under` the
    -- run, every timer past its epoch.
    -- DEAD ROUTE: from the record as it stands.  A stack frame's calls
    --   are ordered against the current position only by `backAs`'s
    --   `q <ᵖ p`, which does not make `q` a prefix of `p`: a frame at `q`
    --   beside `p` holding an `of` has its next value ahead of this one.
    --   The record admits that configuration; `under`'s scoping never
    --   builds it, every call a frame keeps landing past all of `p`.
    emit-lifts : ∀ {g m} (cr : Carried g m) {Δ A p i x xs} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i (x ∷ xs)))
               → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → opened (Conf.heap (Mach.conf m)) true π ≡ true
               → seen (Conf.heap (Mach.conf m)) π ≡ true → Lifts (Conf.heap (Mach.conf m)) π (U.step (U.ofᶜ p i (x ∷ xs))) (U.step g)

    -- A value through a scan: its cell read and written, the
    -- accumulated value one operator up.  The ghost's lift read the cell
    -- before the write; the path above it does not read it.
    climb-scan : ∀ {g m} (st : Strong g m) {m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {f : B → A → B} {r}
                 {u : Sub (Conf.world (Mach.conf m₁)) Δ A} (ρ : Path T (scanˢ f r u)) {y : A}
               → Climbing g m₁ (ρ ⊕ in-scan here) y → Climbed st m₁ (ρ ⊕ in-scan here)

    -- A value through a takeWhile: passed one operator up; or failing,
    -- delivered first when inclusive, then the completion climbs, then
    -- the cut.  The failing value cannot stop at the completion owed: the
    -- ghost alike, the control's work would rise.
    climb-take : ∀ {g m} (st : Strong g m) {m₁ Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {i p c k tk}
                 {u : Sub (Conf.world (Mach.conf m₁)) Δ A} (ρ : Path T (takeWhileˢ i p c k tk u)) {y : A}
               → Climbing g m₁ (ρ ⊕ in-take here) y → Climbed st m₁ (ρ ⊕ in-take here)

    -- A value reaching a flatMap's outer: admitted, a lane begun or
    -- queued, the ghost past the outer's skip.
    climb-outer : ∀ {g m} (st : Strong g m) {m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {op f fl oc k r}
                  {u : Sub (Conf.world (Mach.conf m₁)) Δ A} {ls : List (Lane (Conf.world (Mach.conf m₁)) Δ B)}
                  (ρ : Path T (flatMapˢ op f fl oc k r u ls)) {y : A}
                → Climbing g m₁ (ρ ⊕ in-outer here) y → Climbed st m₁ (ρ ⊕ in-outer here)

    -- A value out of a lane: guarded by its cut, one operator up, its
    -- observer the flatMap's weakened through `same`.
    climb-lanes : ∀ {g m} (st : Strong g m) {m₁ Δ A B Δ′ C} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {op f fl oc k r}
                  {t : Sub (Conf.world (Mach.conf m₁)) Δ A} {ls : List (Lane (Conf.world (Mach.conf m₁)) Δ B)} {u : Sub (Conf.world (Mach.conf m₁)) Δ′ C}
                  (ρ : Path T (flatMapˢ op f fl oc k r t ls)) (πL : PathLanes ls u) → OneLane πL → ∀ {y : C}
                → Climbing g m₁ (ρ ⊕ in-lanes πL) y → Climbed st m₁ (ρ ⊕ in-lanes πL)

    -- A value reaching a connect's subject: the feed of its subscribers
    -- owed, the ghost past the source's skip.
    climb-source : ∀ {g m} (st : Strong g m) {m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {Sj c b kb k fd e}
                   {u : Sub (Conf.world (Mach.conf m₁)) Δ A} {bd : Sub (Conf.world (Mach.conf m₁)) (A ∷ Δ) B}
                   (ρ : Path T (connectˢ Sj c b kb k fd e u bd)) {y : A}
                 → Climbing g m₁ (ρ ⊕ in-source here) y → Climbed st m₁ (ρ ⊕ in-source here)

    -- A subscription's continuation handed its unsubscribe, which it
    -- stashes: the ghost alike, a call fewer.
    kont-onward : ∀ {g m} (cr : Carried g m) {Δ A} {u : Sub _ Δ A} (π : Path (Carried.tree cr) u)
                → firstCall (Carried.ctlAs cr) ≡ just (kontC π) → Hops cr

    -- A takeWhile's completion delivered under its failing value, then
    -- its cut.
    take1-onward : ∀ {g m} (cr : Carried g m) {Δ A i p c k q} {s : Sub _ Δ A} (π : Path (Carried.tree cr) (takeWhileˢ i p c k (Strongly.ending q) s))
                 → firstCall (Carried.ctlAs cr) ≡ just (take1C π) → Hops cr

    -- A completed takeWhile's cut: its kill switch thrown, its source's
    -- unsubscribe run; the ghost alike, a call fewer.
    take2-onward : ∀ {g m} (cr : Carried g m) {Δ A i p c k} {s : Sub _ Δ A} (π : Path (Carried.tree cr) (takeWhileˢ i p c k taken s))
                 → firstCall (Carried.ctlAs cr) ≡ just (take2C π) → Hops cr

    -- A connect's cut once its body completes: the ghost alike, a call
    -- fewer.
    body-onward : ∀ {g m} (cr : Carried g m) {Δ A B S c b kb k fd e} {s : Sub _ Δ A} {bd : Sub _ (A ∷ Δ) B}
                  (π : Path (Carried.tree cr) (connectˢ S c b kb k fd e s bd))
                → firstCall (Carried.ctlAs cr) ≡ just (bodyC π) → Hops cr

    -- The rest of a connect's feed of a value: each subscriber left
    -- shows it or skips it.
    feed-onward : ∀ {g m} (cr : Carried g m) {Δ A B S c b kb k x r ss e} {s : Sub _ Δ A} {bd : Sub _ (A ∷ Δ) B}
                  (π : Path (Carried.tree cr) (connectˢ S c b kb k (feeding x r ss) e s bd))
                → firstCall (Carried.ctlAs cr) ≡ just (feedC π) → Hops cr

    -- The rest of a connect's feed of its source's end.
    fin-onward : ∀ {g m} (cr : Carried g m) {Δ A B S c b kb k r ss e} {s : Sub _ Δ A} {bd : Sub _ (A ∷ Δ) B}
                 (π : Path (Carried.tree cr) (connectˢ S c b kb k (finishing r ss) e s bd))
               → firstCall (Carried.ctlAs cr) ≡ just (finC π) → Hops cr

    -- A connect's source subscribed once its body is: its program begun.
    src-onward : ∀ {g m} (cr : Carried g m) {Δ A B S c b kb k fd e s₁ q} {bd : Sub _ (A ∷ Δ) B}
                 (π : Path (Carried.tree cr) (connectˢ S c b kb k fd e (pendingˢ {Δ = Δ} s₁ q) bd))
               → firstCall (Carried.ctlAs cr) ≡ just (srcC π) → Hops cr

    -- A live burst's sink polled: open, the frame to play; closed, the
    -- burst dropped and the stack resumed.
    burst-poll : ∀ {g m w K b bs} {σ : w ⊑ Conf.world (Mach.conf m)} (cr : Carried g m) → Conf.ctl (Mach.conf m) ≡ held σ K
               → Mach.bursts m ≡ just b ∷ bs → spent? (Conf.heap (Mach.conf m)) (Playing.handle b) ≡ false → Playing.polled b ≡ false
               → ∀ {m′} → step m ≡ silent m′ → Hopped (carried cr) m′

    -- A polled burst's frame played: a value delivered and run to the
    -- next re-entry state, a stall's skip passed, or a close scheduling
    -- the rest.
    burst-play : ∀ {g m w K b bs} {σ : w ⊑ Conf.world (Mach.conf m)} (cr : Carried g m) → Conf.ctl (Mach.conf m) ≡ held σ K
               → Mach.bursts m ≡ just b ∷ bs → spent? (Conf.heap (Mach.conf m)) (Playing.handle b) ≡ false → Playing.polled b ≡ true
               → ∀ {m′} → step m ≡ silent m′ → Hopped (carried cr) m′

    -- A ghost's value shown, the ghost it leaves still sane.
    sane-out : ∀ {g : U.Node [] R} {k a g′} → Sane [] g → U.step g ≡ U.outˢ k a g′ → Sane [] g′

    -- A value recorded is the least the ghost still holds.
    note-least : ∀ {g g′ m w a k K} {σ : w ⊑ Conf.world (Mach.conf m)} → Carried g m
               → Conf.ctl (Mach.conf m) ≡ asking {B = ⊤} (note a) k σ K → U.step g ≡ U.outˢ (Conf.pos (Mach.conf m)) a g′
               → ∀ {q b} → Has (residual g′) q b → q ≤ᵖ Conf.pos (Mach.conf m) → ⊥

  -- A spot's handle, where its node is a cold.
  handleOf : ∀ {h} {t : Sub h [] R} → Spot t → Maybe (Handle h)
  handleOf (spot {u = coldˢ _ hd _} _) = just hd
  handleOf _                           = nothing

  -- A spent burst owes nothing: no live cold is its spot.
  spent-spot : ∀ {h} (H : Heapᴹ h) {t : Sub h [] R} {b} (x : BurstAs t (just b)) {S} → spent? H (Playing.handle b) ≡ true
             → ∀ {Δ A s hd v} (π : Path t (coldˢ {Δ = Δ} {A} s hd v)) → spent? H hd ≡ false → spot π ∈ᴸ burstSpots t x ++ S → spot π ∈ᴸ S
  spent-spot H (playsAs _) sp π nsp (here e) = ⊥-elim (true≢false (trans (sym sp) (subst (λ z → spent? H z ≡ false) (just-injective (cong handleOf e)) nsp)))
  spent-spot H (firesAs _) sp π nsp (here e) = ⊥-elim (true≢false (trans (sym sp) (subst (λ z → spent? H z ≡ false) (just-injective (cong handleOf e)) nsp)))
  spent-spot H (playsAs _) sp π nsp (there i) = i
  spent-spot H (firesAs _) sp π nsp (there i) = i

  -- A spent burst dropped: what the stack under it owes is all that is
  -- owed.
  owned-spent : ∀ {h} (H : Heapᴹ h) {t : Sub h [] R} {p₀ c₀ bs₀ b w p} {σ : w ⊑ h} {K bs} {x : BurstAs t (just b)} {hᴷ} {K′ : StackAs t p σ K bs}
                (ca₀ : CtlAs t p₀ c₀ bs₀) → spent? H (Playing.handle b) ≡ true
              → agenda t ca₀ ≡ stackJobs t K′ → bursts t ca₀ ≡ stackBursts t K′ → begins t ca₀ ≡ sources t (stackJobs t K′)
              → Owned H t (burstAs x hᴷ K′) → Owned H t ca₀
  owned-spent H {t} {x = x} ca₀ sp ag bu be ow = record
    { ofs    = λ π → subst (λ z → _ ∈ᴸ z) (sym ag) (Owned.ofs ow π)
    ; plays  = λ π nsp → subst (λ z → _ ∈ᴸ z) (sym bu) (spent-spot H x sp π nsp (Owned.plays ow π nsp))
    ; fires  = λ π nsp → subst (λ z → _ ∈ᴸ z) (sym bu) (spent-spot H x sp π nsp (Owned.fires ow π nsp))
    ; begun  = λ π → subst (λ z → _ ∈ᴸ z) (sym be) (Owned.begun ow π)
    ; ends   = λ π l → subst (λ z → _ ∈ᴸ z) (sym ag) (Owned.ends ow π l)
    ; cuts   = λ π l → proj₁ (Owned.cuts ow π l) , subst (λ z → _ ∈ᴸ z) (sym ag) (proj₂ (Owned.cuts ow π l))
    ; feeds  = λ π → subst (λ z → _ ∈ᴸ z) (sym ag) (Owned.feeds ow π)
    ; fins   = λ π → subst (λ z → _ ∈ᴸ z) (sym ag) (Owned.fins ow π)
    ; placed = subst (All (Placedᴬ t)) (sym ag) (Owned.placed ow) }

  -- A spent burst dropped, the stack it holds over resumed.
  drop-held : ∀ {h} {hp : Heapᴹ h} {p w} {σ : w ⊑ h} {K clk ts b bs lg en mk} → spent? hp (Playing.handle b) ≡ true
            → step (mach ⟨ hp , p , held σ K ⟩ clk ts (just b ∷ bs) [] lg en mk) ≡ silent (feed (mach ⟨ hp , p , held σ K ⟩ clk ts bs [] lg en mk) goᴵ)
  drop-held sp rewrite sp = refl

  -- A spent burst dropped, the stack resumed: the turn over nothing, or
  -- what follows the cold's start, about to run.  The ghost alike, a
  -- burst fewer.
  burst-spent : ∀ {g m w K b bs} {σ : w ⊑ Conf.world (Mach.conf m)} (cr : Carried g m) → Conf.ctl (Mach.conf m) ≡ held σ K
              → Mach.bursts m ≡ just b ∷ bs → spent? (Conf.heap (Mach.conf m)) (Playing.handle b) ≡ true
              → ∀ {m′} → step m ≡ silent m′ → Hopped (carried cr) m′
  burst-spent {g} {mach ⟨ hp , p , _ ⟩ clk ts _ _ lg en mk} {K = K} {b = b} {bs = bs} {σ = σ}
    cr@record { tree = t ; ctlAs = burstAs x bottomᴴ bottomAs ; meets = mt ; owned = ow ; kernels = kn ; meaning = mn ; queue = q
              ; books = record { fresh = fs ; paidUp = refl ; running = rn } } refl refl sp eq
    with trans (sym eq) (drop-held {hp = hp} {p = p} {σ = σ} {K = K} {clk = clk} {ts = ts} {b = b} {bs = bs} {lg = lg} {en = en} {mk = mk} sp)
  ... | refl =
    g , _ , now
    , carried (record
        { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = t ; ctlAs = calmAs ; meets = mt
        ; owned = owned-spent hp calmAs sp refl refl refl ow ; kernels = kn ; meaning = mn ; queue = q
        ; books = record { fresh = fs ; clocked = tt ; paidUp = refl ; running = rn } 
        ; sorted = hop-sorted cr eq now })
    , lowered (λ n → agree-refl n _) (inj₂ (refl , inj₂ (refl , inj₁ ≤-refl)))
  burst-spent {g} {mach ⟨ hp , p , _ ⟩ clk ts _ _ lg en mk} {K = K} {b = b} {bs = bs} {σ = σ}
    cr@record { tree = t ; ctlAs = burstAs x restᴴ (restAs ks e K″) ; meets = mt ; owned = ow ; kernels = kn ; meaning = mn ; queue = q
              ; books = record { fresh = fs ; clocked = ck ; paidUp = refl ; running = rn } } refl refl sp eq
    with trans (sym eq) (drop-held {hp = hp} {p = p} {σ = σ} {K = K} {clk = clk} {ts = ts} {b = b} {bs = bs} {lg = lg} {en = en} {mk = mk} sp)
  ... | refl =
    g , _ , now
    , carried (record
        { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = t ; ctlAs = runAs ks e K″ ; meets = mt
        ; owned = owned-spent hp (runAs ks e K″) sp refl refl refl ow ; kernels = kn ; meaning = mn ; queue = q
        ; books = record { fresh = fs ; clocked = proj₂ ck ; paidUp = refl ; running = rn } 
        ; sorted = hop-sorted cr eq now })
    , lowered (λ n → agree-refl n _) (inj₂ (refl , inj₂ (refl , inj₁ ≤-refl)))

  -- A burst's frame stepped: found spent, polled, or played.
  burst-onward : ∀ {g m w K b bs} {σ : w ⊑ Conf.world (Mach.conf m)} (cr : Carried g m) → Conf.ctl (Mach.conf m) ≡ held σ K
               → Mach.bursts m ≡ just b ∷ bs → ∀ {m′} → step m ≡ silent m′ → Hopped (carried cr) m′
  burst-onward {m = m} {b = b} cr c bq eq with spent? (Conf.heap (Mach.conf m)) (Playing.handle b) in sp | Playing.polled b in pl
  ... | true  | _     = burst-spent cr c bq sp eq
  ... | false | false = burst-poll cr c bq sp pl eq
  ... | false | true  = burst-play cr c bq sp pl eq

  -- A value through a map: mapped, one operator up.
  climb-map : ∀ {g m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {f : A → B} {u : Sub (Conf.world (Mach.conf m₁)) Δ A}
              (ρ : Path T (mapˢ f u)) {y : A} → Climbing g m₁ (ρ ⊕ in-map here) y → Climbing g m₁ ρ (f y)
  climb-map {m₁ = m₁} {f = f} ρ {y} cl with Climbing.lifted cl
  ... | c′ , pv , S , L , sg with lifts-split ρ (in-map here) L
  ...   | _ , lifts-map lifts-here , Lρ = reclimb cl
    (subst (λ W → Climbing.act cl ≗ Observer.next (Here.obs W) y) (walk-⊕ ρ (in-map here) top) (Climbing.code cl))
    (U.mapᶜ f c′ , cong (At.mapᴹ (Conf.heap (Mach.conf m₁)) (U.mapᶜ f)) pv , S , Lρ , sg)

  -- A value through a defer, as it is.
  climb-defer : ∀ {g m₁ Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {k} {u : Sub (Conf.world (Mach.conf m₁)) Δ A}
                (ρ : Path T (deferˢ k u)) {y : A} → Climbing g m₁ (ρ ⊕ in-defer here) y → Climbing g m₁ ρ y
  climb-defer ρ {y} cl with Climbing.lifted cl
  ... | c′ , pv , S , L , sg with lifts-split ρ (in-defer here) L
  ...   | _ , lifts-defer lifts-here , Lρ = reclimb cl
    (subst (λ W → Climbing.act cl ≗ Observer.next (Here.obs W) y) (walk-⊕ ρ (in-defer here) top) (Climbing.code cl))
    (c′ , pv , S , Lρ , sg)

  -- A value out of a connect's body, as it is: beside its source, or
  -- past its source's end.
  climb-body : ∀ {g m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {Sj c b kb k fd e} {t : Sub (Conf.world (Mach.conf m₁)) Δ A}
               {u : Sub (Conf.world (Mach.conf m₁)) (A ∷ Δ) B} (ρ : Path T (connectˢ Sj c b kb k fd e t u)) {y : B}
             → Climbing g m₁ (ρ ⊕ in-body here) y → Climbing g m₁ ρ y
  climb-body {m₁ = m₁} {e = e} ρ {y} cl with Climbing.lifted cl
  ... | c′ , pv , S , L , sg with lifts-split ρ (in-body here) L
  ...   | _ , lifts-body pt _ lifts-here , Lρ = reclimb cl
    (subst (λ W → Climbing.act cl ≗ Observer.next (Here.obs W) y) (walk-⊕ ρ (in-body here) top) (Climbing.code cl))
    (_ , cong₂ (At.connected (Conf.heap (Mach.conf m₁)) e) pt pv , S , Lρ , sg)
  ...   | _ , lifts-shut pt refl lifts-here , Lρ = reclimb cl
    (subst (λ W → Climbing.act cl ≗ Observer.next (Here.obs W) y) (walk-⊕ ρ (in-body here) top) (Climbing.code cl))
    (_ , cong₂ (At.connected (Conf.heap (Mach.conf m₁)) e) pt pv , S , Lρ , sg)

  -- A value at the root: recorded next, the ghost's step showing it.
  climb-root : ∀ {g m} (st : Strong g m) {m₁} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {y : R} → Climbing g m₁ {T = T} here y → Hopped st m₁
  climb-root {g} st {mach ⟨ hp , p , _ ⟩ clk ts bs td lg en mk} {T}
    record { sane = sn ; placed = pl ; ctl = refl ; code = eff≗ ke ; stack = sk ; lifted = c′ , pv , _ , lifts-here , sg ; owned = ow
           ; kernels = kn ; meaning = mn ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = refl } ; sorted = so } =
    g , _ , then refl now
    , carried (record
        { sane = sn ; placed = pl ; tree = T ; ctlAs = noteAs [] (ke tt) sk ; meets = c′ , pv , sg
        ; owned = owned-move hp (noteAs [] (ke tt) sk) refl refl refl ow ; kernels = kn ; meaning = mn ; queue = qu
        ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = refl } 
        ; sorted = sorted-⇝ so (then refl now) })
    , showing (agrees (λ n → agree-refl n _)) (λ ())

  -- One operator climbed, by the operator.
  climb-step : ∀ {g m} (st : Strong g m) {m₁ Δ A Δ′ A′} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {u : Sub (Conf.world (Mach.conf m₁)) Δ A}
               {v : Sub (Conf.world (Mach.conf m₁)) Δ′ A′} (ρ : Path T u) {s : Path u v} → One s → ∀ {y} → Climbing g m₁ (ρ ⊕ s) y → Climbed st m₁ (ρ ⊕ s)
  climb-step st ρ one-map       cl = rose now (one-lower ρ one-map) (climb-map ρ cl)
  climb-step st ρ one-scan      cl = climb-scan st ρ cl
  climb-step st ρ one-take      cl = climb-take st ρ cl
  climb-step st ρ one-outer     cl = climb-outer st ρ cl
  climb-step st ρ (one-lanes o) cl = climb-lanes st ρ _ o cl
  climb-step st ρ one-source    cl = climb-source st ρ cl
  climb-step st ρ one-body      cl = rose now (one-lower ρ one-body) (climb-body ρ cl)
  climb-step st ρ one-defer     cl = rose now (one-lower ρ one-defer) (climb-defer ρ cl)

  -- A VALUE CLIMBS TO A RE-ENTRY CONFIGURATION: one operator at a time,
  -- from the path's far end, each step to a shorter path.
  climb : ∀ {g m} (st : Strong g m) (n : ℕ) {m₁ Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {v : Sub (Conf.world (Mach.conf m₁)) Δ A}
          (σ : Path T v) {y : A} → height σ < n → Climbing g m₁ σ y → Hopped st m₁
  climb st zero    σ () cl
  climb st (suc n) σ lt cl with view σ
  ... | whole      = climb-root st cl
  ... | snoc ρ s o with climb-step st ρ o cl
  ...   | landed hp         = hp
  ...   | rose path lt′ cl′ = hopped-pre path (climb st n _ (≤-trans lt′ (≤-pred lt)) cl′)

  soar : ∀ {g m m′} (st : Strong g m) → Σ Mach (λ m₁ → m′ ⇝ m₁ × Aloft g m₁) → Hopped st m′
  soar st (m₁ , path , aloft {σ = σ} cl) = hopped-pre path (climb st (suc (height σ)) σ ≤-refl cl)

  -- An open `of` the ghost holds: its value on its way up, the ghost's
  -- step that value lifted.
  emit-open : ∀ {g m} (cr : Carried g m) {Δ A p i x xs} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i (x ∷ xs)))
            → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → opened (Conf.heap (Mach.conf m)) true π ≡ true
            → seen (Conf.heap (Mach.conf m)) π ≡ true → ∀ {m′} → step m ≡ silent m′ → Σ Mach λ m₁ → m′ ⇝ m₁ × Aloft g m₁
  emit-open cr π fc op sn = emit-run cr π fc op (emit-lifts cr π fc op sn)

  -- An `of`'s next value climbs the observers above it: to the root's
  -- note, past a skip (a connect's feed, a lane admitted), or to a
  -- takeWhile's end.
  emit-onward : ∀ {g m} (cr : Carried g m) {Δ A p i xs} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i xs))
              → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → Hops cr
  emit-onward cr {xs = []} π fc = emit-last cr π fc
  emit-onward {m = m} cr {xs = x ∷ xs} π fc with opened (Conf.heap (Mach.conf m)) true π in op | seen (Conf.heap (Mach.conf m)) π in sn
  ... | false | _     = emit-shut cr π fc op
  ... | true  | false = emit-unseen cr π fc op sn
  ... | true  | true  = λ eq → soar (carried cr) (emit-open cr π fc op sn eq)

  -- CODE RUNS SILENTLY ON TO A RE-ENTRY STATE: a subscription begun, the
  -- agenda's first call, or the agenda done and its stack resumed: a
  -- frame's rest, a scope's continuation at the position it puts back, a
  -- burst held, the turn.  The ghost alike, the control's work less.
  run-onward : ∀ {g m w act K} {σ : w ⊑ Conf.world (Mach.conf m)} (cr : Carried g m) → Conf.ctl (Mach.conf m) ≡ run {B = ⊤} act σ K
             → Hops cr
  run-onward {m = mach ⟨ _ , _ , _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = subAs _ _ _ } refl eq = sub-onward cr refl eq
  run-onward {m = mach ⟨ _ , _ , _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = runAs (emitC π ∷ _) _ _ } refl eq = emit-onward cr π refl eq
  run-onward {m = mach ⟨ _ , _ , _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = runAs (kontC π ∷ _) _ _ } refl eq = kont-onward cr π refl eq
  run-onward {m = mach ⟨ _ , _ , _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = runAs (take1C π ∷ _) _ _ } refl eq = take1-onward cr π refl eq
  run-onward {m = mach ⟨ _ , _ , _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = runAs (take2C π ∷ _) _ _ } refl eq = take2-onward cr π refl eq
  run-onward {m = mach ⟨ _ , _ , _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = runAs (bodyC π ∷ _) _ _ } refl eq = body-onward cr π refl eq
  run-onward {m = mach ⟨ _ , _ , _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = runAs (feedC π ∷ _) _ _ } refl eq = feed-onward cr π refl eq
  run-onward {m = mach ⟨ _ , _ , _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = runAs (finC π ∷ _) _ _ } refl eq = fin-onward cr π refl eq
  run-onward {m = mach ⟨ _ , _ , _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = runAs (srcC π ∷ _) _ _ } refl eq = src-onward cr π refl eq
  run-onward {g} {mach ⟨ hp , p , _ ⟩ clk ts _ _ lg en mk}
    cr@record { tree = t ; ctlAs = runAs [] (done≗ refl) bottomAs ; meets = mt ; owned = ow ; kernels = kn ; meaning = mn ; queue = qu
              ; books = record { fresh = fs ; paidUp = refl ; running = rn } } refl refl =
    g , _ , then refl now
    , carried (record
        { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = t ; ctlAs = calmAs ; meets = mt
        ; owned = owned-move hp calmAs refl refl refl ow ; kernels = kn ; meaning = mn ; queue = qu
        ; books = record { fresh = fs ; clocked = tt ; paidUp = refl ; running = rn } 
        ; sorted = hop-sorted cr refl (then refl now) })
    , lowered (λ n → agree-refl n _) (inj₂ (refl , inj₂ (refl , inj₂ (refl , ≤-refl))))
  run-onward {g} {mach ⟨ hp , p , _ ⟩ clk ts _ _ lg en mk}
    cr@record { tree = t ; ctlAs = runAs [] (done≗ refl) (restAs ks e K″) ; meets = mt ; owned = ow ; kernels = kn ; meaning = mn ; queue = qu
              ; books = record { fresh = fs ; clocked = ck ; paidUp = refl ; running = rn } } refl refl =
    g , _ , then refl now
    , carried (record
        { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = t ; ctlAs = runAs ks e K″ ; meets = mt
        ; owned = owned-move hp (runAs ks e K″) refl refl refl ow ; kernels = kn ; meaning = mn ; queue = qu
        ; books = record { fresh = fs ; clocked = proj₂ ck ; paidUp = refl ; running = rn } 
        ; sorted = hop-sorted cr refl (then refl now) })
    , lowered (λ n → agree-refl n _) (inj₂ (refl , inj₂ (refl , inj₂ (refl , ≤-refl))))
  run-onward {g} {mach ⟨ hp , p , _ ⟩ clk ts _ _ lg en mk}
    cr@record { tree = t ; ctlAs = runAs [] (done≗ refl) (backAs q ks qp e K″) ; meets = mt ; owned = ow ; kernels = kn ; meaning = mn ; queue = qu
              ; books = record { fresh = fs ; clocked = ck ; paidUp = refl ; running = rn } } refl refl =
    g , _ , then refl now
    , carried (record
        { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = t ; ctlAs = runAs ks e K″ ; meets = mt
        ; owned = owned-move hp (runAs ks e K″) refl refl refl ow ; kernels = kn ; meaning = mn
        ; queue = record { timed = Queue.timed qu ; joined = Queue.joined qu ; ordered = Queue.ordered qu
                         ; ahead = map (λ { (c , a) → c , <ᵖ-trans q p _ qp a }) (Queue.ahead qu) }
        ; books = record { fresh = fs ; clocked = proj₂ ck ; paidUp = refl ; running = rn } 
        ; sorted = hop-sorted cr refl (then refl now) })
    , lowered (λ n → agree-refl n _) (inj₂ (refl , inj₂ (refl , inj₂ (refl , ≤-refl))))
  run-onward {g} {mach ⟨ hp , p , _ ⟩ clk ts _ _ lg en mk}
    cr@record { tree = t ; ctlAs = runAs [] (done≗ refl) (reholdAs (playsAs π) hᴷ K″) ; meets = mt ; owned = ow ; kernels = kn ; meaning = mn ; queue = qu
              ; books = record { fresh = fs ; clocked = ck ; paidUp = refl ; running = rn } } refl refl =
    g , _ , then refl now
    , carried (record
        { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = t ; ctlAs = burstAs (playsAs π) hᴷ K″ ; meets = mt
        ; owned = owned-move hp (burstAs (playsAs π) hᴷ K″) refl refl refl ow ; kernels = kn ; meaning = mn ; queue = qu
        ; books = record { fresh = fs ; clocked = proj₂ ck ; paidUp = refl ; running = rn } 
        ; sorted = hop-sorted cr refl (then refl now) })
    , lowered (λ n → agree-refl n _) (inj₂ (refl , inj₂ (refl , inj₂ (refl , m<n⇒m<1+n ≤-refl))))
  run-onward {g} {mach ⟨ hp , p , _ ⟩ clk ts _ _ lg en mk}
    cr@record { tree = t ; ctlAs = runAs [] (done≗ refl) (reholdAs (firesAs π) hᴷ K″) ; meets = mt ; owned = ow ; kernels = kn ; meaning = mn ; queue = qu
              ; books = record { fresh = fs ; clocked = ck ; paidUp = refl ; running = rn } } refl refl =
    g , _ , then refl now
    , carried (record
        { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = t ; ctlAs = burstAs (firesAs π) hᴷ K″ ; meets = mt
        ; owned = owned-move hp (burstAs (firesAs π) hᴷ K″) refl refl refl ow ; kernels = kn ; meaning = mn ; queue = qu
        ; books = record { fresh = fs ; clocked = proj₂ ck ; paidUp = refl ; running = rn } 
        ; sorted = hop-sorted cr refl (then refl now) })
    , lowered (λ n → agree-refl n _) (inj₂ (refl , inj₂ (refl , inj₂ (refl , m<n⇒m<1+n ≤-refl))))
  run-onward {g} {mach ⟨ hp , p , _ ⟩ clk ts _ _ lg en mk}
    cr@record { tree = t ; ctlAs = runAs [] (done≗ refl) (reholdAs overAs bottomᴴ bottomAs) ; meets = mt ; owned = ow ; kernels = kn ; meaning = mn ; queue = qu
              ; books = record { fresh = fs ; paidUp = refl ; running = rn } } refl refl =
    g , _ , then refl (then refl now)
    , carried (record
        { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = t ; ctlAs = calmAs ; meets = mt
        ; owned = owned-move hp calmAs refl refl refl ow ; kernels = kn ; meaning = mn ; queue = qu
        ; books = record { fresh = fs ; clocked = tt ; paidUp = refl ; running = rn } 
        ; sorted = hop-sorted cr refl (then refl (then refl now)) })
    , lowered (λ n → agree-refl n _) (inj₂ (refl , inj₂ (refl , inj₁ ≤-refl)))
  run-onward {g} {mach ⟨ hp , p , _ ⟩ clk ts _ _ lg en mk}
    cr@record { tree = t ; ctlAs = runAs [] (done≗ refl) (reholdAs overAs restᴴ (restAs ks e K‴)) ; meets = mt ; owned = ow ; kernels = kn ; meaning = mn
              ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = refl ; running = rn } } refl refl =
    g , _ , then refl (then refl now)
    , carried (record
        { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = t ; ctlAs = runAs ks e K‴ ; meets = mt
        ; owned = owned-move hp (runAs ks e K‴) refl refl refl ow ; kernels = kn ; meaning = mn ; queue = qu
        ; books = record { fresh = fs ; clocked = proj₂ (proj₂ ck) ; paidUp = refl ; running = rn } 
        ; sorted = hop-sorted cr refl (then refl (then refl now)) })
    , lowered (λ n → agree-refl n _) (inj₂ (refl , inj₂ (refl , inj₁ ≤-refl)))

  -- Past a value recorded, the run runs the stepped ghost: the record's
  -- continuation is the agenda, about to run.
  note-onward : ∀ {g g′ m w a k K} {σ : w ⊑ Conf.world (Mach.conf m)} → Carried g m
              → Conf.ctl (Mach.conf m) ≡ asking {B = ⊤} (note a) k σ K → U.step g ≡ U.outˢ (Conf.pos (Mach.conf m)) a g′
              → ∀ {t q a′ m′} → step m ≡ value t q a′ m′ → Mirror g′ m′
  note-onward {g} {m = mach ⟨ hp , p , _ ⟩ clk ts bs td lg en mk}
    cr@record { tree = t ; ctlAs = noteAs ks ke K ; meets = g″ , pe , st″ ; owned = ow ; books = record { running = refl } } refl stp refl
    with trans (sym st″) stp
  ... | refl = _ , now , carried (record
        { sane = sane-out {g = g} (Carried.sane cr) stp
        ; placed = proj₂ (subst (Placedˢ []) stp (placed-after g [] tt (Carried.sane cr) (Carried.placed cr) tt))
        ; tree = t ; ctlAs = runAs ks ke K ; meets = pe
        ; owned = record { ofs = Owned.ofs ow ; plays = Owned.plays ow ; fires = Owned.fires ow ; begun = Owned.begun ow
                         ; ends = Owned.ends ow ; cuts = Owned.cuts ow ; feeds = Owned.feeds ow ; fins = Owned.fins ow
                         ; placed = Owned.placed ow }
        ; kernels = Carried.kernels cr ; meaning = Carried.meaning cr ; queue = Carried.queue cr
        ; books = record { fresh = Books.fresh (Carried.books cr) ; clocked = Books.clocked (Carried.books cr)
                         ; paidUp = Books.paidUp (Carried.books cr) ; running = refl } 
        ; sorted = sorted-value (Carried.sorted cr) refl })

  -- A popped timer's burst, spent, dropped: the turn again.
  drop-spent : ∀ {h} {hp : Heapᴹ h} {p w} {σ : w ⊑ h} {ts lg en mk} (tm : Timer h)
             → spent? hp (Timer.handle tm) ≡ true
             → step (mach ⟨ hp , p , held σ bottom ⟩ (Timer.due tm) ts
                       (just (record { sink = Timer.sink tm ; handle = Timer.handle tm ; at′ = Timer.at′ tm
                                     ; under′ = cascade tm ; index = 0 ; frame = Timer.frame tm ; polled = false }) ∷ []) [] lg en mk)
               ≡ silent (mach ⟨ hp , p , held σ bottom ⟩ (Timer.due tm) ts [] [] lg en mk)
  drop-spent _ sp rewrite sp = refl

  -- The queue's head spent: the rest of the queue still every live
  -- pending frame.
  timed-spent : ∀ {h} {H : Heapᴹ h} {tm ts ps} → At.spentʰ H (Timer.handle tm) ≡ true → At.Timed H (tm ∷ ts) ps → At.Timed H ts ps
  timed-spent {H = H} {tm} {ts} sp (_ ∷ as , bs) = as , map keep bs
    where
      keep : ∀ {x} → (At.spentʰ H (Timer.handle x) ≡ false → x ∈ᴸ tm ∷ ts) → At.spentʰ H (Timer.handle x) ≡ false → x ∈ᴸ ts
      keep f nsp with f nsp
      ... | here refl = ⊥-elim (true≢false (trans (sym sp) nsp))
      ... | there i   = i

  -- The queue's head popped: the rest due no earlier than it.
  ahead-pop : ∀ {h} {p : Pos} {clk} {tm : Timer h} {ts}
            → Linked (λ x y → cascade x <ᵖ cascade y ≡ true) (tm ∷ ts)
            → All (λ x → clk ≤ Timer.due x × p <ᵖ cascade x ≡ true) (tm ∷ ts)
            → All (λ x → Timer.due tm ≤ Timer.due x × p <ᵖ cascade x ≡ true) ts
  ahead-pop {p = p} {tm = tm} lk (_ ∷ ah) = go (later lk) ah
    where
      go : ∀ {clk xs} → All (λ x → cascade tm <ᵖ cascade x ≡ true) xs → All (λ x → clk ≤ Timer.due x × p <ᵖ cascade x ≡ true) xs
         → All (λ x → Timer.due tm ≤ Timer.due x × p <ᵖ cascade x ≡ true) xs
      go []       []             = []
      go {xs = x ∷ _} (c ∷ cs) ((_ , a) ∷ as) = (<ᵖ-tick (Timer.due tm) (Timer.due x) (subᴾ (Timer.from tm) ∷ []) (subᴾ (Timer.from x) ∷ []) c , a) ∷ go cs as

  -- THE TURN POPPING A TIMER: a spent one's burst dropped a step later,
  -- the ghost alike, a timer fewer; a live one's cold fired, the same
  -- meaning node with its burst held, a timer fewer.
  turn-pops : ∀ {g m w} {σ : w ⊑ Conf.world (Mach.conf m)} (cr : Carried g m) → Conf.ctl (Mach.conf m) ≡ held σ bottom
            → Mach.bursts m ≡ [] → ∀ {m′} → step m ≡ silent m′ → Hopped (carried cr) m′
  turn-pops {m = mach ⟨ _ , _ , _ ⟩ _ [] _ _ _ _ _} record { books = record { paidUp = refl } } refl refl ()
  turn-pops {g} {mach ⟨ hp , p , _ ⟩ _ (tm ∷ ts) _ _ lg en mk} {σ = σ}
    cr@record { tree = t ; ctlAs = calmAs ; meets = mt ; owned = ow ; kernels = kn ; meaning = mn ; queue = q
              ; books = record { fresh = fs ; paidUp = refl ; running = rn } } refl refl refl
    with spent? hp (Timer.handle tm) in sp
  ... | true =
    g , mach ⟨ hp , p , held σ bottom ⟩ (Timer.due tm) ts [] [] lg en mk , then (drop-spent tm sp) now
    , carried (record
        { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = t ; ctlAs = calmAs ; meets = mt ; owned = ow
        ; kernels = kn ; meaning = mn
        ; queue = record { timed = timed-spent {H = hp} sp (Queue.timed q) ; joined = Queue.joined q
                         ; ordered = tail (Queue.ordered q) ; ahead = ahead-pop {p = p} (Queue.ordered q) (Queue.ahead q) }
        ; books = record { fresh = fs ; clocked = tt ; paidUp = refl ; running = rn } 
        ; sorted = hop-sorted cr refl (then (drop-spent tm sp) now) })
    , lowered (λ n → agree-refl n _) (inj₂ (refl , inj₁ ≤-refl))
  ... | false with proj₁ (Queue.timed q)
  ...   | inj₁ s ∷ _ = ⊥-elim (true≢false (trans (sym s) sp))
  ...   | inj₂ i ∷ _ with pendings-path {t = t} i
  ...     | waits {τ = τ} {e = e} {u = u} {x = x} {sk = sk} {hd = hd} {fr = fr} π =
    g , _ , now
    , carried (record
        { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = plant π v
        ; ctlAs = burstAs (firesAs (planted π v)) bottomᴴ bottomAs
        ; meets = trans (part-plant hp {t = t} π v refl) mt
        ; owned = owned-pop hp {t = t} π ow
        ; kernels = record { holds = holds-plant hp {t = t} π v refl (λ h → h) (Kernels.holds kn)
                           ; gated = gated-plant hp {t = t} π v refl (λ _ → lift (λ _ → refl)) (λ d → λ { here → d here }) (Kernels.gated kn) }
        ; meaning = record { fed = fed-plant hp {t = t} π v (λ _ f → f) _ (Meaning.fed mn) }
        ; queue = record { timed = timed-pop hp {t = t} π (Queue.timed q) (Queue.ordered q) fs
                         ; joined = subst₂ (At.Joined hp) (sym (subjects-plant {t = t} π v refl)) (sym (joiners-plant {t = t} π v (λ _ → refl) _)) (Queue.joined q)
                         ; ordered = tail (Queue.ordered q) ; ahead = ahead-pop {p = p} (Queue.ordered q) (Queue.ahead q) }
        ; books = record { fresh = subst (AllPairs _≢_) (sym (names-plant {t = t} π v refl)) fs ; clocked = refl , tt ; paidUp = refl ; running = rn } 
        ; sorted = hop-sorted cr refl now })
    , lowered (λ n → agree-refl n _) (inj₂ (pend-plant {t = t} π v refl , inj₁ ≤-refl))
    where v = coldˢ sk hd (fired τ e (at u x fr))

  -- The stepper is the meaning, as sets.
  step-alike : ∀ g → Sane [] g → Placed g [] → residual g ≋ after (U.step g)
  step-alike g sn pl = same-agree (_≃_.agreeing (step-skips g sn pl))

  residual-steps : ∀ g → Sane [] g → Placed g [] → Steps (residual g) (U.step g)
  residual-steps g sn pl = steps-after (U.step g) (step-alike g sn pl)

  -- What a re-entry configuration's ghost is held to.
  strong-sane : ∀ {g m} → Strong g m → Sane [] g × Placed g []
  strong-sane (carried cr)          = Carried.sane cr , Carried.placed cr
  strong-sane (closing _ _ _ sn pl) = sn , pl

  -- The ghost's residual is what its step shows, at every depth.
  strong-agrees : ∀ {g m} → Strong g m → ∀ n → Agree n (residual g) (after (U.step g))
  strong-agrees {g} st = _≃_.agreeing (step-skips g (proj₁ (strong-sane st)) (proj₂ (strong-sane st)))

  -- THE STRONG STEP: from a re-entry configuration the machine records
  -- the value the ghost's step shows, a least of what it leaves, and runs
  -- the stepped ghost; or ends with the ghost; or drains over a ghost
  -- showing nothing; or runs silently to a ghost past this one's skips.
  data Hop {g m} (st : Strong g m) : Set₁ where
    valueᴴ    : ∀ {t p a m′ g′} → step m ≡ value t p a m′ → U.step g ≡ U.outˢ p a g′ → t ≡ tick p
              → (∀ {q b} → Has (residual g′) q b → q ≤ᵖ p → ⊥) → Mirror g′ m′ → Hop st
    completeᴴ : ∀ {p} → step m ≡ complete p → U.step g ≡ U.endˢ p → Hop st
    drainedᴴ  : step m ≡ drained → (∀ {k b} → Has (residual g) k b → ⊥) → Hop st
    silentᴴ   : ∀ {m′} → step m ≡ silent m′ → Hopped st m′ → Hop st

  -- By the re-entry state.
  strong-hop : ∀ {g m} (st : Strong g m) → Hop st
  strong-hop {g = g} {m = mach ⟨ hp , p , c ⟩ clk ts bs td lg en mk} (closing refl refl st sn pl) = completeᴴ refl st
  strong-hop {g = g} {m = mach ⟨ hp , p , c ⟩ clk ts bs td lg en mk} (carried cr)
    with Carried.ctlAs cr | Carried.meets cr | Books.paidUp (Carried.books cr) | Books.clocked (Carried.books cr)
       | Books.running (Carried.books cr)
  ... | subAs π x K | _ | refl | _ | _ = silentᴴ refl (run-onward {g = g} cr refl refl)
  ... | runAs ks x K | _ | refl | _ | _ = silentᴴ refl (run-onward {g = g} cr refl refl)
  strong-hop {g = g} {m = mach ⟨ hp , p , c ⟩ clk ts bs td lg en mk} (carried cr)
    | noteAs ks x K | g′ , _ , st | refl | ck | refl =
    valueᴴ refl st (proj₁ ck) (note-least {g = g} cr refl st) (note-onward {g = g} cr refl st refl)
  strong-hop {g = g} {m = mach ⟨ hp , p , c ⟩ clk ts bs td lg en mk} (carried cr)
    | calmAs | _ | refl | _ | refl with ts
  ... | []    = drainedᴴ refl (turn-dry {g = g} cr refl refl refl)
  ... | _ ∷ _ = silentᴴ refl (turn-pops {g = g} cr refl refl refl)
  strong-hop {g = g} {m = mach ⟨ hp , p , c ⟩ clk ts bs td lg en mk} (carried cr)
    | burstAs {b = b} x _ K | _ | refl | _ | _ with if-silent (spent? hp (Playing.handle b)) (Playing.polled b)
  ... | m′ , eq = silentᴴ eq (burst-onward {g = g} cr refl refl eq)

  strong-shows : ∀ {rest g m} → Strong g m → rest ≋ residual g → Shows rest (step m)
  strong-shows {rest} {g} st e with strong-hop st
  ... | valueᴴ {g′ = g′} eq stp ck least mi = subst (Shows rest) (sym eq)
    (valueˢ ck (proj₂ e (proj₁ rs)) (λ h → proj₂ e (proj₁ (proj₂ rs) h)) (λ h → proj₂ (proj₂ rs) (proj₁ e h)) least
      (record { ghost = g′ ; same = ≋-refl ; mirror = mi }))
    where rs = subst (Steps (residual g)) stp (residual-steps g (proj₁ (strong-sane st)) (proj₂ (strong-sane st)))
  ... | completeᴴ eq stp = subst (Shows rest) (sym eq) (completeˢ (proj₂ e (proj₁ rs)) λ h → proj₂ rs (proj₁ e h))
    where rs = subst (Steps (residual g)) stp (residual-steps g (proj₁ (strong-sane st)) (proj₂ (strong-sane st)))
  ... | drainedᴴ eq no = subst (Shows rest) (sym eq) (drainedˢ λ h → no (proj₁ e h))
  ... | silentᴴ eq h = subst (Shows rest) (sym eq) (silentˢ (onward {g = g} e h))

  -- Every step shows the residual: on the way to a re-entry
  -- configuration a silent step keeps the ghost.
  inner-next : ∀ {rest m} → Inner rest m → Shows rest (step m)
  inner-next i with Inner.mirror i
  ... | m₀ , now , st          = strong-shows st (Inner.same i)
  ... | m₀ , then eq path , st =
    subst (Shows _) (sym eq) (silentˢ (record { ghost = Inner.ghost i ; same = Inner.same i ; mirror = m₀ , path , st }))

  -- THE MACHINE HONEST TO `e`: what it has recorded is among `e`, and
  -- what of `e` it has not lies in `rest`, past every mark, which the
  -- configuration will deliver.
  record HonMach (e : Events R) (m : Mach) : Set₁ where
    field
      rest   : Events R
      logged : ∀ {k a} → Sent (Mach.marks m) (Mach.log m) k a → Has e k (just a)
      split  : ∀ {k b} → Has e k b → Logged (Mach.marks m) (Mach.log m) k b ⊎ Has rest k b
      past   : ∀ {k b} → Has rest k b → Any (k ≤ᵖ_) (Mach.marks m) → ⊥
      paired : length (Mach.marks m) ≡ length (Mach.log m)
      within : ∀ {k b} → Has rest k b → Has e k b
      inner  : Inner rest m

  -- A completion is the events' end, the residual holding no value.
  ends : ∀ {e m p} (h : HonMach e m) → step m ≡ complete p → Has e p nothing × (∀ {k a} → Has (HonMach.rest h) k (just a) → ⊥)
  ends h eq with subst (Shows (HonMach.rest h)) eq (inner-next (HonMach.inner h))
  ... | completeˢ x none = HonMach.within h x , none

  -- A drained run has delivered all of it.
  dries : ∀ {e m} (h : HonMach e m) → step m ≡ drained → ∀ {k b} → Has (HonMach.rest h) k b → ⊥
  dries h eq with subst (Shows (HonMach.rest h)) eq (inner-next (HonMach.inner h))
  ... | drainedˢ none = none

  -- A launch is honest to the meaning's events at the root, all of them
  -- still owed.
  honest-launch : (o : PureObs [] R) → HonMach (observe (⟦ o ⟧ []) root) (begin o)
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
  honest-alike : ∀ {e m en qs} → HonMach e m → Stands m en qs → Alike en qs (Mach.log m) e
  honest-alike h cutʰ = record
    { sound = logged
    ; whole = λ x ow → [ (λ s → s) , (λ r → ⊥-elim (past r ow)) ]′ (split x)
    ; ended = tt
    }
    where open HonMach h
  honest-alike {m = m} h (finʰ {p} eq) = record
    { sound = λ s → logged (sent-cut {Mach.marks m} {Mach.log m} paired s)
    ; whole = λ x _ → [ sent-++ [ p ] , (λ r → ⊥-elim (proj₂ (ends h eq) r)) ]′ (split x)
    ; ended = p , proj₁ (ends h eq) , ++⁺ʳ (Mach.marks m) (here refl)
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
  honest-step : ∀ {e m m′} → HonMach e m → m ↦ m′ → HonMach e m′
  honest-step {m = m} h (silentᵗ eq) with subst (Shows (HonMach.rest h)) eq (inner-next (HonMach.inner h)) | silent-keeps m eq
  ... | silentˢ i | kl , km = record
    { rest   = rest
    ; logged = λ s → logged (subst₂ (λ qs xs → Sent qs xs _ _) km kl s)
    ; split  = λ x → [ (λ l → inj₁ (subst₂ (λ qs xs → Logged qs xs _ _) (sym km) (sym kl) l)) , inj₂ ]′ (split x)
    ; past   = λ r ow → past r (subst (Any (_ ≤ᵖ_)) km ow)
    ; paired = subst₂ (λ qs xs → length qs ≡ length xs) (sym km) (sym kl) paired
    ; within = within
    ; inner  = i
    }
    where open HonMach h
  honest-step {e} {m} h (valueᵗ {t} {p} {a} eq) with subst (Shows (HonMach.rest h)) eq (inner-next (HonMach.inner h)) | value-notes m eq
  ... | valueˢ {r = r} tp x₀ sub sp beyond i | (kl , km) , _ = record
    { rest   = r
    ; logged = λ s → logged′ (subst₂ (λ qs xs → Sent qs xs _ _) km kl s)
    ; split  = λ x → [ (λ l′ → inj₁ (subst₂ (λ qs xs → Logged qs xs _ _) (sym km) (sym kl) l′)) , inj₂ ]′ (split′ x)
    ; past   = λ x ow → past′ x (subst (Any (_ ≤ᵖ_)) km ow)
    ; paired = subst₂ (λ qs xs → length qs ≡ length xs) (sym km) (sym kl) (snoc-length {qs = Mach.marks m} {Mach.log m} paired)
    ; within = λ x → within (sub x)
    ; inner  = i
    }
    where
    open HonMach h
    logged′ : ∀ {k a′} → Sent (Mach.marks m ++ [ p ]) (Mach.log m ++ [ (t , a) ]) k a′ → Has e k (just a′)
    logged′ s with sent-snoc {Mach.marks m} {Mach.log m} paired s
    ... | inj₁ s′       = logged s′
    ... | inj₂ (kp , x) = subst₂ (λ k a′ → Has e k (just a′)) (sym kp) (cong proj₂ x) (within x₀)
    split′ : ∀ {k b} → Has e k b → Logged (Mach.marks m ++ [ p ]) (Mach.log m ++ [ (t , a) ]) k b ⊎ Has r k b
    split′ x with split x
    ... | inj₁ lg = inj₁ (logged-snoc lg)
    ... | inj₂ y with sp y
    ...   | inj₂ y′       = inj₂ y′
    ...   | inj₁ (kp , ba) = inj₁ (subst₂ (λ k b → Logged (Mach.marks m ++ [ p ]) (Mach.log m ++ [ (t , a) ]) k b) (sym kp) (sym ba)
                                    (subst (λ t′ → Sent (Mach.marks m ++ [ p ]) (Mach.log m ++ [ (t′ , a) ]) p a) (sym tp) (sent-last {Mach.marks m} {Mach.log m} paired)))
    past′ : ∀ {k b} → Has r k b → Any (k ≤ᵖ_) (Mach.marks m ++ [ p ]) → ⊥
    past′ x ow with ++⁻ (Mach.marks m) ow
    ... | inj₁ o          = past (sub x) o
    ... | inj₂ (here kp)  = beyond x kp
    ... | inj₂ (there ())

  -- Every configuration reached from a launch is honest.
  honest : ∀ {e m} → Reached e m → HonMach e m
  honest (launchedʰ o refl) = honest-launch o
  honest (silentʰ r eq)     = honest-step (honest r) (silentᵗ eq)
  honest (valueʰ r eq)      = honest-step (honest r) (valueᵗ eq)

  -- THE MACHINE'S CONTENT: a configuration reached from a launch keeps
  -- a record alike its meaning's events, however it stands.
  kept : ∀ {e m en qs} → Reached e m → Stands m en qs → Alike en qs (Mach.log m) e
  kept r = honest-alike (honest r)

  -- What a reader of the run from a reached configuration has, put after
  -- that configuration's record, is the record of one reached from it,
  -- standing as the reader's run stands.
  Onward : Events R → Mach → Read → Set₁
  Onward e m x = Σ Mach λ m′ → Σ (Reached e m′) λ _ → Σ End λ en → Σ (List Pos) λ qs
               → Stands m′ en qs × read (Mach.marks m ++ marks x) (Mach.log m ++ log x) (ending x) ≡ read qs (Mach.log m′) en

  mutual
    read-on : ∀ {e m} → Reached e m → ∀ n → Onward e m (reading n (Mach.clock m) (trace m))
    read-on {m = m} r zero    = m , r , _ , _ , cutʰ , cong₂ (λ qs xs → read qs xs _) (++-identityʳ _) (++-identityʳ _)
    read-on {m = m} r (suc n) = read-step r n (step m) refl

    read-step : ∀ {e m} → Reached e m → ∀ n s → step m ≡ s → Onward e m (reading (suc n) (Mach.clock m) (shown s))
    read-step {m = m} r n (silent m₁) eq with read-on (silentʰ r eq) n | silent-keeps m eq
    ... | m′ , r′ , en , qs , st , x | kl , km = m′ , r′ , en , qs , st , subst₂ (λ ms ls → read (ms ++ _) (ls ++ _) _ ≡ _) km kl x
    read-step {m = m} r n (value t p a m₁) eq with value-notes m eq
    ... | (kl , km) , refl with read-on (valueʰ r eq) n
    ...   | m′ , r′ , en , qs , st , x = m′ , r′ , en , qs , st ,
              trans (cong₂ (λ ms ls → read ms ls _) (sym (++-assoc (Mach.marks m) [ p ] _)) (sym (++-assoc (Mach.log m) [ (t , a) ] _)))
                    (subst₂ (λ ms ls → read (ms ++ _) (ls ++ _) _ ≡ _) km kl x)
    read-step {m = m} r n (complete p) eq = m , r , finished , _ , finʰ eq , cong (λ ls → read _ ls finished) (++-identityʳ _)
    read-step {m = m} r n drained      eq = m , r , dry , _ , dryʰ eq , cong₂ (λ qs xs → read qs xs dry) (++-identityʳ _) (++-identityʳ _)

  -- The launch's first n steps, read, are the record of a configuration
  -- reached from it.
  read-is-kept : (o : PureObs [] R) (n : ℕ) → Σ Mach λ m′ → Σ (Reached (observe (⟦ o ⟧ []) root) m′) λ _ → Σ End λ en
               → Σ (List Pos) λ qs → Stands m′ en qs × reading n 0 (trace (begin o)) ≡ read qs (Mach.log m′) en
  read-is-kept o n = read-on (launchedʰ o refl) n

  -- CONTENT: every prefix's record alike the meaning's events as a set.
  content : (o : PureObs [] R) (n : ℕ) → let x = reading n 0 (trace (begin o)) in Alike (ending x) (marks x) (log x) (observe (⟦ o ⟧ []) root)
  content o n with read-is-kept o n
  ... | m′ , r′ , en , qs , st , eq rewrite eq = kept r′ st
