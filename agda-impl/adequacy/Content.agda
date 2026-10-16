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
open import Data.Nat.Properties using (suc-injective; ≤-refl; ≤-trans; ≤-pred; m<n⇒m<1+n; m<m+n; <-trans)
open import Data.List.Relation.Unary.All using (All; []; _∷_; map)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to all-++⁺)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Data.List.Relation.Unary.Linked using (Linked; _∷_; tail)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴸ_)
open import Level using (Lift; lift)
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
  skip⁼; end⁼; agree; agree-sym; agree-trans; agree-refl; at; ix; _<ᵖ_; <ᵖ-tick; <ᵖ-trans;
  <ᵖ-apart; <ᵖ-asym; <ᵖ-below)
import denotation.Unfold as U
open import denotation.MonotonicList using () renaming (sub to subᴾ)
open import denotation.Compositional using ([]ᵉ)
open import adequacy.Sorted using (_≤ᵖ_; Under; module Sorting)
open import operation.Machine using (module Machine)
open import adequacy.Record using (module Recording)
open import adequacy.Strong using (module Strongly)
open import adequacy.Moves using (module Moving)
open import adequacy.Torn using (module Tearing)
open import adequacy.Unsub using (module Unsubbing)
open import adequacy.Local using (module Locality)
open import adequacy.Lowers using (module Lowering)
open import adequacy.Seq using (module Sequencing)
open import adequacy.Sane using (Sane; sane-out)
open import adequacy.Placed using (Placed)
open import adequacy.Stepper using (_≃_; afterᴱ; placed-after; Placedˢ; step-skips)
open import denotation.Denote using (⟦_⟧)
import Tree as T
open import operation.PureObservable using (PureObs; Out; note; Pureᴾ; module Pure)
open import operation.AbstractObservable using (module Heap; module Run) renaming (module Machine to Shared)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_; not)
open import Data.Bool.Properties using (∧-zeroʳ)

open Events∞

module Honesty (R : Set) where
  open Machine R using (Mach; mach; Playing; Step; silent; value; complete; drained; step; trace; shown; reading; begin; launch; Read; read; feed)
  open Shared Timeline (Out R) using (Conf; Heapᴹ; Stack; ⟨_,_,_⟩; held; run; asking; bottom; spent?; store; look) renaming (go to goᴵ)
  open Heap using (World; _⊑_; Handle; Quiet) renaming (same to same⊑)
  open Sorting R using (WellMach; WellStep; silentʷ; valueʷ; preserve; Beyond)
  open Run (Pureᴾ R) using (Act; Observer; Subject; _>>ᴬ_; module Kit; module FlatKit)
  open Recording R using (silent-keeps; value-notes)
  open Strongly R using (Strong; strong-begin; Carried; Books; carried; closing; Sub; pendingˢ; coldˢ; ofˢ; doneˢ; mapˢ; scanˢ; takeWhileˢ;
    flatMapˢ; connectˢ; joinˢ; deferˢ; Lane; lane; here; module At; Queue; Kernels; Meaning; fired; waiting; Owned; Path; Spot; spot; done≗;
    Call; emitC; kontC; take1C; take2C; bodyC; feedC; finC; srcC; Taking; taking; taken; feeding; finishing; PathLanes; this-lane; next-lane;
    in-map; in-scan; in-take; in-outer; in-lanes; in-source; in-body; in-defer; _⊕_; _⊕ᴸ_; Here; walk; walkLanes; top; _≗_; eff≗; readRef≗; ≗-refl; Meets; Each; Heads; rootObs;
    seen; seenL; isTaking; seen-up; seen-join; ∧-split; ∧-join) renaming (ending to endingᵗ; ⟦_⟧ to ⟦_⟧ᶜ)
  open Strongly.Against R using (calmAs; noteAs; runAs; subAs; burstAs; firesAs; playsAs; overAs; bottomAs; restAs; backAs; reholdAs; bottomᴴ; restᴴ; BurstAs;
    StackAs; CtlAs; agenda; bursts; begins; sources; stackJobs; stackBursts; burstSpots) renaming (Placed to Placedᴬ)
  open Pure R using (End; finished; dry; cutOff; recorder; Timer; cascade)
  open Moving R using (pend; takes; takes-plant; plant; planted; Waits; waits; pendings-path; part-plant; pend-plant; names-plant; subjects-plant;
    joiners-plant; holds-plant; gated-plant; fed-plant; timed-pop; owned-pop; later; true≢false)
  open Tearing R using (Site; takeSite; bodySite; siteCall; siteHeap; torn-take-part; torn-body-part; torn-take-each; torn-body-each)
  open Unsubbing R using (_⇝_; now; then; ⇝-trans; site-tears; ≗-trans; wk-same; bind≗)
  open Locality R using (site-holds; site-gated)
  open Lowering R using (site-lowers; queue-lowers; torn-owned; fed-lowers)
  open Sequencing R using (seq-assoc)
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

  -- An outer or a source as the ghost steps it: the node the heap holds,
  -- or, once it has ended, gone from the heap and the node it was, which
  -- the ghost's own step pins.
  data Was {h} (H : Heapᴹ h) {Δ A} (t : Sub h Δ A) (o : U.Node Δ A) : Set₁ where
    still : At.part H t ≡ just o → Was H t o
    was   : At.part H t ≡ nothing → Was H t o

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
      lifts-outer  : ∀ {Δ A B Δ′ C} {op f fl oc k r pl} {t : Sub h Δ A} {ls : List (Lane h Δ B)} {u : Sub h Δ′ C} {ρ : Path t u} {s S o₀}
                   → Was H t o₀ → OuterFirst S (At.partLanes H ls)
                   → PoolBehind pl (U.outerOf (just o₀)) (U.earliest (At.partLanes H ls)) → Lifts H ρ s S
                   → Lifts H (in-outer {op = op} {f} {fl} {oc} {k} {r} {pl} {ls = ls} ρ) s
                       (U.outerˢ op (λ a q → U.subscribe (f a) q) o₀ S (At.partLanes H ls) (At.val H (FlatKit.Flat.queue fl)) pl)
      lifts-lanes  : ∀ {Δ A B Δ′ C} {op f fl oc k r pl} {t : Sub h Δ A} {ls : List (Lane h Δ B)} {u : Sub h Δ′ C} {πL : PathLanes ls u}
                       {s bs l S as q}
                   → LiftsLane H πL s bs S as → U.earliest (At.partLanes H ls) ≡ U.found q bs l S as → LaneFirst (At.part H t) q
                   → PoolBehind pl (U.outerOf (At.part H t)) (U.found q bs l S as)
                   → Lifts H (in-lanes {op = op} {f} {fl} {oc} {k} {r} {pl} {t = t} πL) s
                       (U.laneˢ op (λ a q → U.subscribe (f a) q) (At.part H t) bs l S as (At.val H (FlatKit.Flat.queue fl)) pl)
      lifts-source : ∀ {Δ A B Δ′ C} {Sj c b kb k fd e rp rt} {t : Sub h Δ A} {bd : Sub h (A ∷ Δ) B} {u : Sub h Δ′ C} {ρ : Path t u} {s S c₀ b₀}
                   → Was H t c₀ → At.part H bd ≡ just b₀ → SourceFirst S (U.step b₀) → Lifts H ρ s S
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
    lifts-split (in-outer ρ)  τ (lifts-outer po of pb L)   with lifts-split ρ τ L
    ... | S′ , Lτ , Lρ = S′ , Lτ , lifts-outer po of pb Lρ
    lifts-split (in-lanes πL) τ (lifts-lanes L ea lf pb)   with liftsL-split πL τ L
    ... | S′ , Lτ , Lρ = S′ , Lτ , lifts-lanes Lρ ea lf pb
    lifts-split (in-source ρ) τ (lifts-source pt pb sf L)  with lifts-split ρ τ L
    ... | S′ , Lτ , Lρ = S′ , Lτ , lifts-source pt pb sf Lρ
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
      one-lanes  : ∀ {Δ A B Δ′ C} {op f fl oc k r pl} {t : Sub h Δ A} {ls : List (Lane h Δ B)} {u : Sub h Δ′ C} {πL : PathLanes ls u}
                 → OneLane πL → One (in-lanes {op = op} {f} {fl} {oc} {k} {r} {pl} {t = t} πL)
      one-source : ∀ {Δ A B} {Sj c b kb k fd e rp rt} {t : Sub h Δ A} {bd : Sub h (A ∷ Δ) B} → One (in-source {S = Sj} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {t = t} {bd} here)
      one-body   : ∀ {Δ A B} {Sj c b kb k fd e rp rt} {t : Sub h Δ A} {bd : Sub h (A ∷ Δ) B} → One (in-body {S = Sj} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {t = t} {bd} here)
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

  -- A VALUE ON ITS WAY UP: `y` about to be delivered to the observer
  -- the path walks to, the agenda empty above the stack.  The node it
  -- reaches already past the value, and the ghost's step the value
  -- lifted along the path.
  record Climbing (g : U.Node [] R) (ℓ : Load) (m₁ : Mach) {Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {v : Sub (Conf.world (Mach.conf m₁)) Δ A}
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
      behind  : Each (Conf.heap (Mach.conf m₁)) (Heads (Conf.pos (Mach.conf m₁))) T
      kept    : load m₁ T ≼ ℓ

  -- The same climb, the value restated at another path.
  reclimb : ∀ {g ℓ m₁ Δ A Δ′ A′} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {v : Sub (Conf.world (Mach.conf m₁)) Δ A}
              {v′ : Sub (Conf.world (Mach.conf m₁)) Δ′ A′} {σ : Path T v} {y : A} (cl : Climbing g ℓ m₁ σ y) {σ′ : Path T v′} {y′ : A′}
          → Climbing.act cl ≗ Observer.next (Here.obs (walk σ′ top)) y′
          → Σ (U.Node Δ′ A′) (λ c′ → At.part (Conf.heap (Mach.conf m₁)) v′ ≡ just c′
              × Σ (U.Step [] R) λ S → Lifts (Conf.heap (Mach.conf m₁)) σ′ (U.outˢ (Conf.pos (Mach.conf m₁)) y′ c′) S × U.step g ≡ S)
          → Climbing g ℓ m₁ σ′ y′
  reclimb cl cd lf = record
    { sane = Climbing.sane cl ; placed = Climbing.placed cl ; ctl = Climbing.ctl cl ; code = cd ; stack = Climbing.stack cl ; lifted = lf
    ; owned = Climbing.owned cl ; kernels = Climbing.kernels cl ; meaning = Climbing.meaning cl ; queue = Climbing.queue cl
    ; books = Climbing.books cl ; sorted = Climbing.sorted cl ; behind = Climbing.behind cl ; kept = Climbing.kept cl }

  -- The same climb, held to a load no lighter.
  relevel : ∀ {g ℓ ℓ′ m₁ Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {v : Sub (Conf.world (Mach.conf m₁)) Δ A} {σ : Path T v} {y : A}
          → Climbing g ℓ′ m₁ σ y → ℓ′ ≼ ℓ → Climbing g ℓ m₁ σ y
  relevel cl le = record
    { sane = Climbing.sane cl ; placed = Climbing.placed cl ; ctl = Climbing.ctl cl ; code = Climbing.code cl ; stack = Climbing.stack cl
    ; lifted = Climbing.lifted cl ; owned = Climbing.owned cl ; kernels = Climbing.kernels cl ; meaning = Climbing.meaning cl
    ; queue = Climbing.queue cl ; books = Climbing.books cl ; sorted = Climbing.sorted cl ; behind = Climbing.behind cl
    ; kept = ≼-trans (Climbing.kept cl) le }

  -- The value one operator higher, the path shorter, the load at most `ℓ`.
  data Rises (g : U.Node [] R) (ℓ : Load) (m₁ : Mach) {Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {v : Sub (Conf.world (Mach.conf m₁)) Δ A}
             (σ : Path T v) : Set₁ where
    rises : ∀ {m₂ Δ′ A′} {T′ : Sub (Conf.world (Mach.conf m₂)) [] R} {v′ : Sub (Conf.world (Mach.conf m₂)) Δ′ A′} {σ′ : Path T′ v′} {y′ : A′}
          → m₁ ⇝ m₂ → height σ′ < height σ → Climbing g ℓ m₂ σ′ y′ → Rises g ℓ m₁ σ

  -- One operator climbed: a re-entry configuration reached, or the
  -- value one operator higher, the path shorter.
  data Climbed {g m} (st : Strong g m) (m₁ : Mach) {Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {v : Sub (Conf.world (Mach.conf m₁)) Δ A}
               (σ : Path T v) : Set₁ where
    landed : Hopped st m₁ → Climbed st m₁ σ
    rose   : ∀ {m₂ Δ′ A′} {T′ : Sub (Conf.world (Mach.conf m₂)) [] R} {v′ : Sub (Conf.world (Mach.conf m₂)) Δ′ A′} {σ′ : Path T′ v′} {y′ : A′}
           → m₁ ⇝ m₂ → height σ′ < height σ → Climbing g (loadOf st) m₂ σ′ y′ → Climbed st m₁ σ

  -- Some value on its way up.
  data Aloft (g : U.Node [] R) (ℓ : Load) (m₁ : Mach) : Set₁ where
    aloft : ∀ {Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {v : Sub (Conf.world (Mach.conf m₁)) Δ A} {σ : Path T v} {y : A}
          → Climbing g ℓ m₁ σ y → Aloft g ℓ m₁

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

  postulate
    -- The turn, nothing held and no timer queued: the ghost shows
    -- nothing.
    turn-dry : ∀ {g m w} {σ : w ⊑ Conf.world (Mach.conf m)} → Carried g m → Conf.ctl (Mach.conf m) ≡ held σ bottom
             → Mach.bursts m ≡ [] → Mach.timers m ≡ [] → ∀ {k b} → Has (residual g) k b → ⊥

    -- A subscription begun at its pending node, its kernel run to the
    -- next re-entry state: its program smaller by what was begun, or
    -- past a defer's skip.
    sub-onward : ∀ {g m} (cr : Carried g m) → opening (Carried.ctlAs cr) ≡ true → Hops cr

    -- An `of` reading its observer closed: its burst over, nothing
    -- delivered.  The ghost must hold nothing of it.
    emit-shut : ∀ {g m} (cr : Carried g m) {Δ A p i x xs} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i (x ∷ xs)))
              → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → opened (Conf.heap (Mach.conf m)) true π ≡ false → Hops cr

    -- An `of` reading its observer open where the ghost does not hold it:
    -- a connect's source fed on past what held it.  The source is
    -- subscribed after the body and its cut attached only once its
    -- subscribe returns, and it reads its subject, not its connect's
    -- observer; so a body, or a takeWhile or lane above the connect,
    -- ending inside that burst leaves the rest of the burst to run into a
    -- subject nobody reads, as rxjs does.  The value climbs to the node
    -- that hides it (a takeWhile or lane cut, a connect whose body has
    -- ended) and dies at a guard; that node's part ignores everything
    -- under it, so the ghost is alike, and the `of` owes a value fewer.
    -- Nothing under a part that has ended reads open, so no lane is
    -- admitted, no subscription begun on the way.
    -- DEAD ROUTE: the ghost past the burst's skip (`U.burstingᶜ`).  A
    --   part past its end shows nothing under it: a cut takeWhile and a
    --   connect with no body have no part, and an `ending` take's rest
    --   stops at its end, which sits before every later value of the
    --   burst.  No skip of the ghost's is this value.
    emit-void : ∀ {g m} (cr : Carried g m) {Δ A p i x xs} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i (x ∷ xs)))
              → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → opened (Conf.heap (Mach.conf m)) true π ≡ true
              → seen (Conf.heap (Mach.conf m)) π ≡ false → ∀ {m′} → step m ≡ silent m′
              → Σ (U.Node [] R) λ g″ → Σ Mach λ m₀ → m′ ⇝ m₀ × Σ (Carried g″ m₀) λ cr₀
                → (∀ n → Agree n (residual g) (residual g″)) × load m₀ (Carried.tree cr₀) ⊏ load m (Carried.tree cr)

    -- An `of` reading its observer open, its value handed on under the
    -- `of`'s scope: the `of` past it, the value on its way up, the
    -- ghost's step the value lifted.
    emit-run : ∀ {g m} (cr : Carried g m) {Δ A p i x xs} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i (x ∷ xs)))
             → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → opened (Conf.heap (Mach.conf m)) true π ≡ true
             → Lifts (Conf.heap (Mach.conf m)) π (U.step (U.ofᶜ p i (x ∷ xs))) (U.step g)
             → ∀ {m′} → step m ≡ silent m′ → Σ Mach λ m₁ → m′ ⇝ m₁ × Aloft g (load m (Carried.tree cr)) m₁

    -- A connect whose source has ended, holding an `of` in its body: the
    -- body shut steps as the body does, shut after.  What the body holds
    -- the shut can tell is a joiner owed a value (a feed under way past
    -- the source's end, `Fed`'s `feeding` beside an `e`), or a joiner
    -- not yet subscribed (a pending `connected`, its end told where it
    -- would subscribe).  The first must not exist, the second must end
    -- past every event the body steps to first.
    shut-step : ∀ {g m} (cr : Carried g m) {Δ A B Sj c b kb k fd rp e rt} {src : Sub (Conf.world (Mach.conf m)) Δ A}
                {bd : Sub (Conf.world (Mach.conf m)) (A ∷ Δ) B} (ρ : Path (Carried.tree cr) (connectˢ Sj c b kb k fd rp e rt src bd))
                {Δ′ A′ p i x xs} (π : Path bd (ofˢ {Δ = Δ′} {A′} p i (x ∷ xs)))
              → At.part (Conf.heap (Mach.conf m)) src ≡ nothing → ∀ {c₁} → e ≡ just c₁ → ∀ {b₀} → At.part (Conf.heap (Mach.conf m)) bd ≡ just b₀
              → U.shutˢᵗ rp c₁ rt (U.step (U.shut (Any.here refl) c₁ b₀)) ≡ U.shutˢᵗ rp c₁ rt (U.step b₀)

    -- The agenda's first call an open `of` the ghost holds: no sibling
    -- its path passes heads under the `of`'s base.  A value under it the
    -- ghost still holds is the `of`'s own; what a connect's source fed
    -- the body's joiners under its earlier values, they have taken.
    spread-past : ∀ {g m} (cr : Carried g m) {Δ A p i x xs} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i (x ∷ xs)))
                → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → opened (Conf.heap (Mach.conf m)) true π ≡ true
                → seen (Conf.heap (Mach.conf m)) π ≡ true → Clear (Conf.heap (Mach.conf m)) (Off p) π

    -- A live timer popped at the turn: its cold, fired, heads past where
    -- the run is, the queue's timers being past it.
    behind-fire : ∀ {g m} (cr : Carried g m) {Δ A τ e v u x sk hd fr}
                  (π : Path (Carried.tree cr) (coldˢ {Δ = Δ} {A} sk hd (waiting {u = v} τ e (at u x fr))))
                → Each (Conf.heap (Mach.conf m)) (Heads (Conf.pos (Mach.conf m))) (plant π (coldˢ sk hd (fired τ e (at u x fr))))

    -- A value through a scan: its cell read and written, the
    -- accumulated value one operator up.  The ghost's lift read the cell
    -- before the write; the path above it does not read it.
    climb-scan : ∀ {g m} (st : Strong g m) {m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {f : B → A → B} {r}
                 {u : Sub (Conf.world (Mach.conf m₁)) Δ A} (ρ : Path T (scanˢ f r u)) {y : A}
               → Climbing g (loadOf st) m₁ (ρ ⊕ in-scan here) y → Climbed st m₁ (ρ ⊕ in-scan here)

    -- A value an inclusive takeWhile fails on: delivered under `ix 0`,
    -- the take `ending` where the run is, its completion a call owed.
    take-out : ∀ {g ℓ m₁ Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {p c k}
               {u : Sub (Conf.world (Mach.conf m₁)) Δ A} (ρ : Path T (takeWhileˢ true p c k taking u)) {y : A} → p y ≡ false
             → Climbing g ℓ m₁ (ρ ⊕ in-take here) y → Rises g (load m₁ T) m₁ (ρ ⊕ in-take here)

    -- A value an exclusive takeWhile fails on: the take `ending` where
    -- the run is, its completion the agenda's call.  The ghost alike,
    -- the take a stage on.
    take-end : ∀ {g ℓ m₁ Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {p c k}
               {u : Sub (Conf.world (Mach.conf m₁)) Δ A} (ρ : Path T (takeWhileˢ false p c k taking u)) {y : A} → p y ≡ false
             → Climbing g ℓ m₁ (ρ ⊕ in-take here) y
             → Σ (U.Node [] R) λ g″ → Σ Mach λ m₀ → m₁ ⇝ m₀ × Σ (Carried g″ m₀) λ cr
               → (∀ n → Agree n (residual g) (residual g″)) × load m₀ (Carried.tree cr) ⊏ load m₁ T

    -- A value reaching a flatMap's outer: admitted, a lane begun or
    -- queued, the ghost past the outer's skip.
    climb-outer : ∀ {g m} (st : Strong g m) {m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {op f fl oc k r pl}
                  {u : Sub (Conf.world (Mach.conf m₁)) Δ A} {ls : List (Lane (Conf.world (Mach.conf m₁)) Δ B)}
                  (ρ : Path T (flatMapˢ op f fl oc k r pl u ls)) {y : A}
                → Climbing g (loadOf st) m₁ (ρ ⊕ in-outer here) y → Climbed st m₁ (ρ ⊕ in-outer here)

    -- A value out of a lane: guarded by its cut, one operator up, its
    -- observer the flatMap's weakened through `same`.
    climb-lanes : ∀ {g m} (st : Strong g m) {m₁ Δ A B Δ′ C} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {op f fl oc k r pl}
                  {t : Sub (Conf.world (Mach.conf m₁)) Δ A} {ls : List (Lane (Conf.world (Mach.conf m₁)) Δ B)} {u : Sub (Conf.world (Mach.conf m₁)) Δ′ C}
                  (ρ : Path T (flatMapˢ op f fl oc k r pl t ls)) (πL : PathLanes ls u) → OneLane πL → ∀ {y : C}
                → Climbing g (loadOf st) m₁ (ρ ⊕ in-lanes πL) y → Climbed st m₁ (ρ ⊕ in-lanes πL)

    -- A value reaching a connect's subject: the feed of its subscribers
    -- owed, the ghost past the source's skip.
    climb-source : ∀ {g m} (st : Strong g m) {m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {Sj c b kb k fd e rp rt}
                   {u : Sub (Conf.world (Mach.conf m₁)) Δ A} {bd : Sub (Conf.world (Mach.conf m₁)) (A ∷ Δ) B}
                   (ρ : Path T (connectˢ Sj c b kb k fd rp e rt u bd)) {y : A}
                 → Climbing g (loadOf st) m₁ (ρ ⊕ in-source here) y → Climbed st m₁ (ρ ⊕ in-source here)

    -- A subscription's continuation handed its unsubscribe, which it
    -- stashes: the ghost alike, a call fewer.
    kont-onward : ∀ {g m} (cr : Carried g m) {Δ A} {u : Sub _ Δ A} (π : Path (Carried.tree cr) u)
                → firstCall (Carried.ctlAs cr) ≡ just (kontC π) → Hops cr

    -- The rest of a connect's feed of a value: each subscriber left
    -- shows it or skips it.
    feed-onward : ∀ {g m} (cr : Carried g m) {Δ A B S c b kb k x r ss e rp rt} {s : Sub _ Δ A} {bd : Sub _ (A ∷ Δ) B}
                  (π : Path (Carried.tree cr) (connectˢ S c b kb k (feeding x r ss) rp e rt s bd))
                → firstCall (Carried.ctlAs cr) ≡ just (feedC π) → Hops cr

    -- A connect's source subscribed once its body is: its program begun.
    src-onward : ∀ {g m} (cr : Carried g m) {Δ A B S c b kb k fd e s₁ q rp rt} {bd : Sub _ (A ∷ Δ) B}
                 (π : Path (Carried.tree cr) (connectˢ S c b kb k fd rp e rt (pendingˢ {Δ = Δ} s₁ q) bd))
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

    -- A value recorded is the least the ghost still holds.
    note-least : ∀ {g g′ m w a k K} {σ : w ⊑ Conf.world (Mach.conf m)} → Carried g m
               → Conf.ctl (Mach.conf m) ≡ asking {B = ⊤} (note a) k σ K → U.step g ≡ U.outˢ (Conf.pos (Mach.conf m)) a g′
               → ∀ {q b} → Has (residual g′) q b → q ≤ᵖ Conf.pos (Mach.conf m) → ⊥

  ----------------------------------------------------------------------
  -- THE TEARDOWN: what unsubscribing leaves, in the order `unsub` runs

  -- A cut from the agenda's head runs silently to the rest of the
  -- agenda, over the heap its switch thrown leaves.
  tear-cut : ∀ {g h hp p w σ K act clk ts bs td lg en mk}
             (cr : Carried g (mach (⟨_,_,_⟩ {h} hp p (run {w = w} act σ K)) clk ts bs td lg en mk))
             (z : Site (Carried.tree cr)) {ks}
           → act ≗ ⟦ siteCall z ∷ ks ⟧ᶜ → ∀ {m′} → step (mach ⟨ hp , p , run act σ K ⟩ clk ts bs td lg en mk) ≡ silent m′
           → Σ (Act h ⊤) λ act′ → act′ ≗ ⟦ ks ⟧ᶜ × m′ ⇝ mach ⟨ siteHeap hp z , p , run act′ σ K ⟩ clk ts bs td lg en mk
  tear-cut {hp = hp} cr z {ks} e eq = site-tears hp (Kernels.holds (Carried.kernels cr)) (Books.fresh (Carried.books cr)) z {ks} e eq

  -- A joiner silenced owes nothing; every other as it was.
  torn-fed : ∀ {g m} (cr : Carried g m) (z : Site (Carried.tree cr))
           → At.Fed (siteHeap (Conf.heap (Mach.conf m)) z) (Carried.tree cr) []
  torn-fed cr z = fed-lowers (site-lowers _ z) (Carried.tree cr) (Meaning.fed (Carried.meaning cr))

  -- Every subscription still against its kernel, and every gate: the
  -- cut moves only the node it runs from.
  torn-holds : ∀ {g m} (cr : Carried g m) (z : Site (Carried.tree cr))
             → At.Holds (siteHeap (Conf.heap (Mach.conf m)) z) (Carried.tree cr) [] rootObs
  torn-holds cr z = site-holds _ (Books.fresh (Carried.books cr)) z (Kernels.holds (Carried.kernels cr))

  torn-gated : ∀ {g m} (cr : Carried g m) (z : Site (Carried.tree cr))
             → At.Gated (siteHeap (Conf.heap (Mach.conf m)) z) (Carried.tree cr)
  torn-gated cr z = site-gated _ (Books.fresh (Carried.books cr)) z (Kernels.holds (Carried.kernels cr)) (Kernels.gated (Carried.kernels cr))

  -- The queue as it was: a teardown only spends, lowers and silences.
  torn-queue : ∀ {g m} (cr : Carried g m) (z : Site (Carried.tree cr))
             → Queue (siteHeap (Conf.heap (Mach.conf m)) z) (Conf.pos (Mach.conf m)) (Mach.clock m) (Mach.timers m) (Carried.tree cr)
  torn-queue cr z = queue-lowers (site-lowers _ z) (Carried.queue cr)

  -- A site holds no part, a body's by `Owned.bodies`, so the tree's
  -- part is the same once its switch is thrown.
  torn-part : ∀ {g m} (cr : Carried g m) (z : Site (Carried.tree cr))
            → firstCall (Carried.ctlAs cr) ≡ just (siteCall z)
            → At.part (siteHeap (Conf.heap (Mach.conf m)) z) (Carried.tree cr) ≡ At.part (Conf.heap (Mach.conf m)) (Carried.tree cr)
  torn-part cr (takeSite π) _ = torn-take-part _ π (Books.fresh (Carried.books cr))
  torn-part {m = mach ⟨ _ , _ , _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = runAs (_ ∷ _) _ _ } (bodySite π) refl =
    torn-body-part _ π (Books.fresh (Carried.books cr)) (Owned.bodies (Carried.owned cr) π (here refl))

  -- Every part the ghost holds still heads no earlier than the run:
  -- what the teardown reached it holds no longer, the rest reads alike.
  torn-behind : ∀ {g m} (cr : Carried g m) (z : Site (Carried.tree cr))
              → firstCall (Carried.ctlAs cr) ≡ just (siteCall z)
              → Each (siteHeap (Conf.heap (Mach.conf m)) z) (Heads (Conf.pos (Mach.conf m))) (Carried.tree cr)
  torn-behind cr (takeSite π) _ = torn-take-each _ π (Books.fresh (Carried.books cr)) (Carried.behind cr)
  torn-behind {m = mach ⟨ _ , _ , _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = runAs (_ ∷ _) _ _ } (bodySite π) refl =
    torn-body-each _ π (Books.fresh (Carried.books cr)) (Owned.bodies (Carried.owned cr) π (here refl)) (Carried.behind cr)

  -- A cut: its kill switch thrown, what it holds unsubscribed; the ghost
  -- alike, a call fewer.
  cut-onward : ∀ {g m} (cr : Carried g m) (z : Site (Carried.tree cr))
             → firstCall (Carried.ctlAs cr) ≡ just (siteCall z) → Hops cr
  cut-onward {g} {mach ⟨ hp , p , _ ⟩ clk ts bs td lg en mk} cr@record { ctlAs = runAs (_ ∷ ks) e Kᴬ } z refl eq
    with tear-cut cr z {ks} e eq
  ... | act′ , e′ , path = g , _ , path
    , carried (record
        { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = Carried.tree cr ; ctlAs = runAs ks e′ Kᴬ
        ; meets = trans (torn-part cr z refl) (Carried.meets cr)
        ; owned = torn-owned hp z (Carried.owned cr)
        ; kernels = record { holds = torn-holds cr z ; gated = torn-gated cr z }
        ; meaning = record { fed = torn-fed cr z }
        ; queue = torn-queue cr z
        ; books = record { fresh = Books.fresh (Carried.books cr) ; clocked = Books.clocked (Carried.books cr)
                         ; paidUp = Books.paidUp (Carried.books cr) ; running = Books.running (Carried.books cr) }
        ; sorted = hop-sorted cr eq path ; behind = torn-behind cr z refl })
    , lowered (λ n → agree-refl n _) (inj₂ (refl , ≤-refl))

  ----------------------------------------------------------------------
  -- THE GHOST'S STEP, FROM A PATH EVERY SIBLING OF WHICH WAITS

  -- A step whose next event is under `p`.
  data Below (p : Pos) {Γ A} (S : U.Step Γ A) : Set where
    below : ∀ {k} → U.headˢ S ≡ just k → Under p k → Below p S

  under-++ : ∀ {p k} z → Under p k → Under p (k ++ z)
  under-++ {p} z (y , refl) = y ++ z , ++-assoc p y z

  far-lt : ∀ {p k k′} → Beyond p k′ → Under p k → k <ᵖ k′ ≡ true
  far-lt record { past = f } (y , refl) = f y

  far-gt : ∀ {p k k′} → Beyond p k′ → Under p k → k′ <ᵖ k ≡ false
  far-gt {k = k} {k′} bk uk = <ᵖ-asym k k′ (far-lt bk uk)

  -- Each operator keeps the next event under `p`.
  below-map : ∀ {p Γ A B} {f : A → B} {S : U.Step Γ A} → Below p S → Below p (U.mapˢ f S)
  below-map {S = U.outˢ _ _ _} (below h u) = below h u
  below-map {S = U.skipˢ _ _}  (below h u) = below h u
  below-map {S = U.endˢ _}     (below h u) = below h u
  below-map {S = U.hushˢ} (below () _)

  below-scan : ∀ {p Γ A B} {f : B → A → B} {z} {S : U.Step Γ A} → Below p S → Below p (U.scanˢ f z S)
  below-scan {S = U.outˢ _ _ _} (below h u) = below h u
  below-scan {S = U.skipˢ _ _}  (below h u) = below h u
  below-scan {S = U.endˢ _}     (below h u) = below h u
  below-scan {S = U.hushˢ} (below () _)

  below-take : ∀ {p Γ A} i (q : A → Bool) {S : U.Step Γ A} → Below p S → Below p (U.takeWhileˢ i q S)
  below-take true  q {U.outˢ k a c} (below refl u) with q a
  ... | true  = below refl u
  ... | false = below refl (under-++ _ u)
  below-take false q {U.outˢ k a c} (below refl u) with q a
  ... | true  = below refl u
  ... | false = below refl (under-++ _ u)
  below-take i q {U.skipˢ _ _} (below h u) = below h u
  below-take i q {U.endˢ _}    (below h u) = below h u
  below-take i q {U.hushˢ} (below () _)

  below-outer : ∀ {p Γ A B} {op} {g : A → Pos → U.Node Γ B} {o : U.Node Γ A} {S ls qs pl} → Below p S → Below p (U.outerˢ op g o S ls qs pl)
  below-outer {S = U.outˢ q _ _} (below refl u) = below refl (under-++ _ u)
  below-outer {S = U.skipˢ _ _} (below h u) = below h u
  below-outer {S = U.endˢ _} {[]} {[]} (below h u) = below h u
  below-outer {S = U.endˢ _} {[]} {_ ∷ _} (below h u) = below h u
  below-outer {S = U.endˢ _} {_ ∷ _} (below h u) = below h u
  below-outer {S = U.hushˢ} (below () _)

  below-lane : ∀ {p Γ A B} {op} {g : A → Pos → U.Node Γ B} {o : Maybe (U.Node Γ A)} {bs l S as qs pl}
             → Below p S → Below p (U.laneˢ op g o bs l S as qs pl)
  below-lane {S = U.outˢ _ _ _} (below h u) = below h u
  below-lane {S = U.skipˢ _ _} (below h u) = below h u
  below-lane {S = U.endˢ c} {qs = _ ∷ _} (below refl u) = below refl (under-++ _ u)
  below-lane {o = nothing} {[]} {S = U.endˢ _} {[]} {[]} (below h u) = below h u
  below-lane {o = nothing} {[]} {S = U.endˢ _} {_ ∷ _} {[]} (below h u) = below h u
  below-lane {o = nothing} {_ ∷ _} {S = U.endˢ _} {qs = []} (below h u) = below h u
  below-lane {o = just _} {S = U.endˢ _} {qs = []} (below h u) = below h u
  below-lane {S = U.hushˢ} (below () _)

  below-source : ∀ {p Γ A B} {r} {b : U.Node (A ∷ Γ) B} {sb} {s : U.Node Γ A} {S} → SourceFirst S sb → Below p S → Below p (U.sourceˢ r b sb s S)
  below-source {S = U.outˢ q _ _} sf (below refl u) rewrite sf = below refl (under-++ _ u)
  below-source {S = U.skipˢ q _}  sf (below refl u) rewrite sf = below refl (under-++ _ u)
  below-source {S = U.endˢ c}     sf (below refl u) rewrite sf = below refl (under-++ _ u)
  below-source {S = U.hushˢ} () _

  below-body : ∀ {p Γ A B} {r} {s : U.Source Γ A} {S : U.Step (A ∷ Γ) B} → Below p S → Below p (U.bodyˢ r s S)
  below-body {S = U.outˢ _ _ _} (below h u) = below h u
  below-body {S = U.skipˢ _ _}  (below h u) = below h u
  below-body {S = U.endˢ _}     (below h u) = below h u
  below-body {S = U.hushˢ} (below () _)

  below-shut : ∀ {p Γ A B} {r c} {t : U.Node Γ A} {S : U.Step (A ∷ Γ) B} → Below p S → Below p (U.shutˢᵗ r c t S)
  below-shut {S = U.outˢ _ _ _} (below h u) = below h u
  below-shut {S = U.skipˢ _ _}  (below h u) = below h u
  below-shut {S = U.endˢ _}     (below h u) = below h u
  below-shut {S = U.hushˢ} (below () _)

  -- A step's order against a position is its next event's.
  beforeᴹ : Pos → Maybe Pos → Bool
  beforeᴹ q nothing  = true
  beforeᴹ q (just k) = q <ᵖ k

  before-head : ∀ {Γ B} q (S : U.Step Γ B) → U.beforeˢ q S ≡ beforeᴹ q (U.headˢ S)
  before-head q (U.outˢ _ _ _) = refl
  before-head q (U.skipˢ _ _)  = refl
  before-head q (U.endˢ _)     = refl
  before-head q U.hushˢ        = refl

  shut-head : ∀ {Γ A B} {r c} {t : U.Node Γ A} (S : U.Step (A ∷ Γ) B) → U.headˢ (U.shutˢᵗ r c t S) ≡ U.headˢ S
  shut-head (U.outˢ _ _ _) = refl
  shut-head (U.skipˢ _ _)  = refl
  shut-head (U.endˢ _)     = refl
  shut-head U.hushˢ        = refl

  -- A sibling past `p` steps after the step under `p`.
  before-far : ∀ {p q Γ B} {b : U.Node Γ B} → Far p b → Under p q → U.beforeˢ q (U.step b) ≡ true
  before-far {b = b} fb u with U.step b in eb
  ... | U.outˢ _ _ _ = far-lt (Far.far-at fb (cong U.headˢ eb)) u
  ... | U.skipˢ _ _  = far-lt (Far.far-at fb (cong U.headˢ eb)) u
  ... | U.endˢ _     = far-lt (Far.far-at fb (cong U.headˢ eb)) u
  ... | U.hushˢ      = refl

  before-not : ∀ {p q Γ B} {S : U.Step Γ B} → Beyond p q → Below p S → U.beforeˢ (q ++ [ ix 0 ]) S ≡ false
  before-not {q = q} {S = U.outˢ k _ _} bq (below refl u) = <ᵖ-asym k (q ++ [ ix 0 ]) (<ᵖ-trans k q (q ++ [ ix 0 ]) (far-lt bq u) (<ᵖ-below q []))
  before-not {q = q} {S = U.skipˢ k _}  bq (below refl u) = <ᵖ-asym k (q ++ [ ix 0 ]) (<ᵖ-trans k q (q ++ [ ix 0 ]) (far-lt bq u) (<ᵖ-below q []))
  before-not {q = q} {S = U.endˢ k}     bq (below refl u) = <ᵖ-asym k (q ++ [ ix 0 ]) (<ᵖ-trans k q (q ++ [ ix 0 ]) (far-lt bq u) (<ᵖ-below q []))
  before-not {S = U.hushˢ} bq (below () _)

  source-first : ∀ {p Γ A B} {b : U.Node (A ∷ Γ) B} {S : U.Step Γ A} → Far p b → Below p S → SourceFirst S (U.step b)
  source-first {S = U.outˢ _ _ _} fb (below refl u) = before-far fb (under-++ [ ix 0 ] u)
  source-first {S = U.skipˢ _ _}  fb (below refl u) = before-far fb (under-++ [ ix 0 ] u)
  source-first {S = U.endˢ _}     fb (below refl u) = before-far fb (under-++ [ ix 0 ] u)
  source-first {S = U.hushˢ} fb (below () _)

  body-first : ∀ {p Γ A B} {c : U.Node Γ A} {S : U.Step (A ∷ Γ) B} → Far p c → Below p S → BodyFirst (U.step c) S
  body-first {c = c} fc b with U.step c in ec
  ... | U.outˢ _ _ _ = before-not (Far.far-at fc (cong U.headˢ ec)) b
  ... | U.skipˢ _ _  = before-not (Far.far-at fc (cong U.headˢ ec)) b
  ... | U.endˢ _     = before-not (Far.far-at fc (cong U.headˢ ec)) b
  ... | U.hushˢ      = tt

  body-step : ∀ {Γ A B} {r} {b : U.Node (A ∷ Γ) B} {sb} {s : U.Node Γ A} sc → BodyFirst sc sb → U.sourceˢ r b sb s sc ≡ U.bodyˢ r (U.live s) sb
  body-step (U.outˢ _ _ _) bf rewrite bf = refl
  body-step (U.skipˢ _ _)  bf rewrite bf = refl
  body-step (U.endˢ _)     bf rewrite bf = refl
  body-step U.hushˢ        _  = refl

  rest-behind : ∀ {p Γ A B} {t : U.Node Γ A} {S : U.Step (A ∷ Γ) B} → Far p t → Below p S → RestBehind t S
  rest-behind ft b et = before-not (Far.far-at ft (cong U.headˢ et)) b

  ended-shut : ∀ {Γ A B} {r c} {b : U.Node (A ∷ Γ) B} {t : U.Node Γ A} {X S : U.Step (A ∷ Γ) B} → RestBehind t S → U.headˢ X ≡ U.headˢ S
             → U.endedˢ r b X c t (U.step t) ≡ U.shutˢᵗ r c t X
  ended-shut {t = t} {X} {S} rb hx with U.step t in et
  ... | U.skipˢ k _ rewrite before-head (k ++ [ ix 0 ]) X | hx | sym (before-head (k ++ [ ix 0 ]) S) | rb refl = refl
  ... | U.outˢ _ _ _ = refl
  ... | U.endˢ _     = refl
  ... | U.hushˢ      = refl

  -- The earliest lane, read off the lanes.
  FarE : Pos → ∀ {Γ B} → U.Earliest Γ B → Set
  FarE p U.none                = ⊤
  FarE p (U.found k _ _ _ _)   = Beyond p k

  earliest-far : ∀ {p Γ B} (ls : List (U.Node Γ B)) → All (Far p) ls → FarE p (U.earliest ls)
  earliest-far []       []        = tt
  earliest-far (c ∷ ls) (fc ∷ fs) with U.headˢ (U.step c) in hc | U.earliest ls | earliest-far ls fs
  ... | nothing | U.none               | _ = tt
  ... | nothing | U.found _ _ _ _ _    | f = f
  ... | just k  | U.none               | _ = Far.far-at fc hc
  ... | just k  | U.found k′ _ _ _ _   | f with k <ᵖ k′
  ...   | true  = Far.far-at fc hc
  ...   | false = f

  earliest-split : ∀ {Γ B} (ls : List (U.Node Γ B)) {k bs l s as} → U.earliest ls ≡ U.found k bs l s as → bs ++ l ∷ as ≡ ls
  earliest-split []       ()
  earliest-split (c ∷ ls) e with U.headˢ (U.step c) | U.earliest ls in ee
  ... | nothing | U.none = ⊥-elim (none≢ e)
    where none≢ : ∀ {Γ B} {k bs l s as} → U.none {Γ} {B} ≡ U.found k bs l s as → ⊥
          none≢ ()
  ... | nothing | U.found _ _ _ _ _ with e
  ...   | refl = cong (c ∷_) (earliest-split ls ee)
  earliest-split (c ∷ ls) refl | just k | U.none = refl
  earliest-split (c ∷ ls) e | just k | U.found k′ _ _ _ _ with k <ᵖ k′ | e
  ...   | true  | refl = refl
  ...   | false | refl = cong (c ∷_) (earliest-split ls ee)

  earliest-found : ∀ {p Γ B} {bs : List (U.Node Γ B)} {l as k} → All (Far p) bs → All (Far p) as → U.headˢ (U.step l) ≡ just k → Under p k
                 → U.earliest (bs ++ l ∷ as) ≡ U.found k bs l (U.step l) as
  earliest-found {as = as} [] fas hl u rewrite hl with U.earliest as | earliest-far as fas
  ... | U.none                | _  = refl
  ... | U.found k′ _ _ _ _    | bk rewrite far-lt bk u = refl
  earliest-found {bs = b ∷ bs} {l} {as} (fb ∷ fbs) fas hl u with U.headˢ (U.step b) in hb
  ... | nothing = cong (U.pick b (U.step b) (bs ++ l ∷ as) nothing) (earliest-found fbs fas hl u)
  ... | just kb = trans (cong (U.pick b (U.step b) (bs ++ l ∷ as) (just kb)) (earliest-found fbs fas hl u)) (pick-past (far-gt (Far.far-at fb hb) u))
    where pick-past : ∀ {k} → kb <ᵖ k ≡ false → U.pick b (U.step b) (bs ++ l ∷ as) (just kb) (U.found k bs l (U.step l) as) ≡ U.found k (b ∷ bs) l (U.step l) as
          pick-past e rewrite e = refl

  outer-first : ∀ {p Γ A B} {S : U.Step Γ A} {ls : List (U.Node Γ B)} → Below p S → All (Far p) ls → OuterFirst S ls
  outer-first {p} {ls = ls} (below {k′} hk u) fs ee = k′ , hk , far-lt (subst (FarE p) ee (earliest-far ls fs)) u

  lane-first : ∀ {p Γ A} {o : Maybe (U.Node Γ A)} {q} → Opt (Far p) o → Under p q → LaneFirst o q
  lane-first {o = nothing} _  _ = tt
  lane-first {o = just o}  fo u ho = far-gt (Far.far-at fo ho) u

  pool-outer : ∀ {p Γ A B} {pl : U.Node Γ B} {o₀ : U.Node Γ A} {S} {E : U.Earliest Γ B} → Far p pl → Below p S → PoolBehind pl (U.runᵒ o₀ S) E
  pool-outer {E = U.none}              fp (below hS u) ep rewrite hS = far-gt (Far.far-at fp (cong U.headˢ ep)) u
  pool-outer {E = U.found _ _ _ _ _}   fp (below hS u) ep rewrite hS | far-gt (Far.far-at fp (cong U.headˢ ep)) u = refl

  pool-lane : ∀ {p Γ A B} {pl : U.Node Γ B} {o : Maybe (U.Node Γ A)} {q bs l S as} → Far p pl → Under p q
            → PoolBehind pl (U.outerOf o) (U.found q bs l S as)
  pool-lane {o = nothing} fp u ep = far-gt (Far.far-at fp (cong U.headˢ ep)) u
  pool-lane {o = just _}  fp u ep rewrite far-gt (Far.far-at fp (cong U.headˢ ep)) u = ∧-zeroʳ _

  -- A flatMap's step is its outer's, or a lane's, by the side conditions.
  flat-outer : ∀ {Γ A B} {op} {g : A → Pos → U.Node Γ B} {o₀ : U.Node Γ A} {S} {LS qs pl}
             → PoolBehind pl (U.runᵒ o₀ S) (U.earliest LS) → OuterFirst S LS
             → U.flatˢ op g (U.runᵒ o₀ S) LS qs pl (U.step pl) (U.earliest LS) ≡ U.outerˢ op g o₀ S LS qs pl
  flat-outer {op = op} {g} {o₀} {S} {LS} {qs} {pl} pb of with U.step pl in ep
  ... | U.skipˢ _ _  rewrite pb refl = go
    where go : U.goˢ op g (U.runᵒ o₀ S) LS qs pl (U.earliest LS) ≡ U.outerˢ op g o₀ S LS qs pl
          go with U.earliest LS in ee
          ... | U.none = refl
          ... | U.found k bs l s as with of refl
          ...   | k′ , hk , lt rewrite hk | lt | earliest-split LS ee = refl
  ... | U.outˢ _ _ _ = go
    where go : U.goˢ op g (U.runᵒ o₀ S) LS qs pl (U.earliest LS) ≡ U.outerˢ op g o₀ S LS qs pl
          go with U.earliest LS in ee
          ... | U.none = refl
          ... | U.found k bs l s as with of refl
          ...   | k′ , hk , lt rewrite hk | lt | earliest-split LS ee = refl
  ... | U.endˢ _     = go
    where go : U.goˢ op g (U.runᵒ o₀ S) LS qs pl (U.earliest LS) ≡ U.outerˢ op g o₀ S LS qs pl
          go with U.earliest LS in ee
          ... | U.none = refl
          ... | U.found k bs l s as with of refl
          ...   | k′ , hk , lt rewrite hk | lt | earliest-split LS ee = refl
  ... | U.hushˢ      = go
    where go : U.goˢ op g (U.runᵒ o₀ S) LS qs pl (U.earliest LS) ≡ U.outerˢ op g o₀ S LS qs pl
          go with U.earliest LS in ee
          ... | U.none = refl
          ... | U.found k bs l s as with of refl
          ...   | k′ , hk , lt rewrite hk | lt | earliest-split LS ee = refl

  go-lane : ∀ {Γ A B} {op} {g : A → Pos → U.Node Γ B} (o : Maybe (U.Node Γ A)) {LS qs pl k bs l S as} → LaneFirst o k
          → U.goˢ op g (U.outerOf o) LS qs pl (U.found k bs l S as) ≡ U.laneˢ op g o bs l S as qs pl
  go-lane nothing  _ = refl
  go-lane (just o) lf with U.headˢ (U.step o) in ho
  ... | nothing = refl
  ... | just k′ rewrite lf refl = refl

  flat-lane : ∀ {Γ A B} {op} {g : A → Pos → U.Node Γ B} {o : Maybe (U.Node Γ A)} {LS qs pl k bs l S as}
            → U.earliest LS ≡ U.found k bs l S as → PoolBehind pl (U.outerOf o) (U.found k bs l S as) → LaneFirst o k
            → U.flatˢ op g (U.outerOf o) LS qs pl (U.step pl) (U.earliest LS) ≡ U.laneˢ op g o bs l S as qs pl
  flat-lane {o = o} {pl = pl} ea pb lf rewrite ea with U.step pl in ep
  ... | U.skipˢ _ _  rewrite pb refl = go-lane o lf
  ... | U.outˢ _ _ _ = go-lane o lf
  ... | U.endˢ _     = go-lane o lf
  ... | U.hushˢ      = go-lane o lf

  -- A maybe, split without abstracting it from the goal.
  data Peek {ℓ} {X : Set ℓ} (x : Maybe X) : Set ℓ where
    peek-nothing : x ≡ nothing → Peek x
    peek-just    : ∀ {y} → x ≡ just y → Peek x

  peek : ∀ {ℓ} {X : Set ℓ} (x : Maybe X) → Peek x
  peek nothing  = peek-nothing refl
  peek (just _) = peek-just refl

  module _ {g m} (cr : Carried g m) where
    private
      W = Conf.world (Mach.conf m)
      H = Conf.heap (Mach.conf m)

    lanes-cons : ∀ {Δ B} (l : Lane W Δ B) (ls : List (Lane W Δ B)) → At.partLanes H (l ∷ ls) ≡ At.partLanes H (l ∷ []) ++ At.partLanes H ls
    lanes-cons (lane c k s) ls with At.val H (Kit.live c)
    ... | false = refl
    ... | true with At.part H s
    ...   | nothing = refl
    ...   | just _  = refl

    held-flat : ∀ {Δ A B} {op f fl oc k r pl} {so : Sub W Δ A} {ls : List (Lane W Δ B)} {o₀}
              → At.part H so ≡ just o₀
              → At.part H (flatMapˢ op f fl oc k r pl so ls)
                ≡ just (U.flatMapᶜ op (λ a q → U.subscribe (f a) q) (just o₀) (At.partLanes H ls) (At.val H (FlatKit.Flat.queue fl)) pl)
    held-flat po rewrite po = refl

    held-lanes : ∀ {Δ A B} {op f fl oc k r pl} {so : Sub W Δ A} {ls : List (Lane W Δ B)} {bs l as}
               → At.partLanes H ls ≡ bs ++ l ∷ as
               → At.part H (flatMapˢ op f fl oc k r pl so ls)
                 ≡ just (U.flatMapᶜ op (λ a q → U.subscribe (f a) q) (At.part H so) (At.partLanes H ls) (At.val H (FlatKit.Flat.queue fl)) pl)
    held-lanes {so = so} {bs = bs} eq rewrite eq with At.part H so
    ... | just _ = refl
    ... | nothing with bs
    ...   | []    = refl
    ...   | _ ∷ _ = refl

    held-src : ∀ {Δ A B Sj c b kb k fd rp e rt} {src : Sub W Δ A} {bd : Sub W (A ∷ Δ) B} {c₀ b₀}
             → At.part H src ≡ just c₀ → At.part H bd ≡ just b₀
             → At.part H (connectˢ Sj c b kb k fd rp e rt src bd) ≡ just (U.connectᶜ rp b₀ (U.live c₀))
    held-src ps pb rewrite ps | pb = refl

    held-shut : ∀ {Δ A B Sj c b kb k fd rp c₁ rt} {src : Sub W Δ A} {bd : Sub W (A ∷ Δ) B} {b₀}
              → At.part H src ≡ nothing → At.part H bd ≡ just b₀
              → At.part H (connectˢ Sj c b kb k fd rp (just c₁) rt src bd) ≡ just (U.connectᶜ rp (U.shut (Any.here refl) c₁ b₀) (U.ended c₁ rt))
    held-shut ps pb rewrite ps | pb = refl

    -- The value an `of` the ghost holds emits, lifted up a path every
    -- sibling of which waits: the ghost's part there, its step the `of`'s
    -- lifted, and its next event under the `of`'s base.
    mutual
      lift-up : ∀ {Δ A} {t : Sub W Δ A} (ρ₀ : Path (Carried.tree cr) t) {Δ′ A′ p i x xs} (π : Path t (ofˢ {Δ = Δ′} {A′} p i (x ∷ xs)))
              → seen H π ≡ true → Clear H (Far p) π
              → Σ (U.Node Δ A) λ c → At.part H t ≡ just c × Lifts H π (U.step (U.ofᶜ p i (x ∷ xs))) (U.step c) × Below p (U.step c)
      lift-up ρ₀ {p = p} {i} {x} {xs} here sn cl = U.ofᶜ p i (x ∷ xs) , refl , lifts-here , below refl ([ ix i ] , refl)
      lift-up ρ₀ (in-map {f = f} ρ) sn cl with lift-up (ρ₀ ⊕ in-map here) ρ sn cl
      ... | c , pc , L , b rewrite pc = U.mapᶜ f c , refl , lifts-map L , below-map b
      lift-up ρ₀ (in-scan {f = f} {r} ρ) sn cl with lift-up (ρ₀ ⊕ in-scan here) ρ sn cl
      ... | c , pc , L , b rewrite pc = U.scanᶜ f (At.val H r) c , refl , lifts-scan L , below-scan b
      lift-up ρ₀ (in-take {i = i} {q} {c} {tk = taking} ρ) sn cl with At.val H (Kit.live c) in lv
      lift-up ρ₀ (in-take {tk = taking} ρ) () cl | false
      ... | true with lift-up (ρ₀ ⊕ in-take here) ρ sn cl
      ...   | c′ , pc , L , b rewrite pc = U.takeWhileᶜ i q c′ , refl , lifts-take lv L , below-take i q b
      lift-up ρ₀ (in-take {c = c} {tk = endingᵗ _ _} ρ) sn cl with At.val H (Kit.live c)
      lift-up ρ₀ (in-take {tk = endingᵗ _ _} ρ) () cl | false
      lift-up ρ₀ (in-take {tk = endingᵗ _ _} ρ) () cl | true
      lift-up ρ₀ (in-take {c = c} {tk = taken} ρ) sn cl with At.val H (Kit.live c)
      lift-up ρ₀ (in-take {tk = taken} ρ) () cl | false
      lift-up ρ₀ (in-take {tk = taken} ρ) () cl | true
      lift-up ρ₀ (in-outer {Δ = Δf} {A = Af} {B = Bf} {op = op} {f = f} {fl = fl} {oc = oc} {k = k} {r = r} {pl = pl} {t = so} {ls = ls} ρ) sn (fl′ , pd , cl) with lift-up (ρ₀ ⊕ in-outer here) ρ sn cl
      ... | o₀ , po , L , b =
        _ , hp , subst (Lifts H (in-outer {op = op} {f = f} {fl = fl} {oc = oc} {k = k} {r = r} {pl = pl} {t = so} {ls = ls} ρ) _) (sym st) (lifts-outer (still po) (outer-first b fl′) (pool-outer {o₀ = o₀} {E = U.earliest (At.partLanes H ls)} fp b) L) ,
        subst (Below _) (sym st) (below-outer b)
        where hp = held-flat {Δ = Δf} {A = Af} {B = Bf} {op = op} {f = f} {fl = fl} {oc = oc} {k = k} {r = r} {pl = pl} {so = so} {ls = ls} po
              fp = pd hp
              st = flat-outer {op = op} {LS = At.partLanes H ls} {qs = At.val H (FlatKit.Flat.queue fl)} {pl = pl} (pool-outer {o₀ = o₀} {E = U.earliest (At.partLanes H ls)} fp b) (outer-first b fl′)
      lift-up ρ₀ (in-lanes {Δ = Δf} {A = Af} {B = Bf} {op = op} {f = f} {fl = fl} {oc = oc} {k = k} {r = r} {pl = pl} {t = so} {ls = ls} πL) sn (fo , pd , cl) with lift-up-lanes (λ πL′ → ρ₀ ⊕ in-lanes πL′) πL sn cl
      ... | bs , l , as , eq , LL , fbs , fas , below {q} hq u =
        _ , hp , subst (Lifts H (in-lanes {op = op} {f = f} {fl = fl} {oc = oc} {k = k} {r = r} {pl = pl} {t = so} {ls = ls} πL) _) (sym st) (lifts-lanes LL ea (lane-first fo u) (pool-lane {o = At.part H so} {bs = bs} {l = l} {S = U.step l} {as = as} fp u)) ,
        subst (Below _) (sym st) (below-lane (below hq u))
        where hp = held-lanes {Δ = Δf} {A = Af} {B = Bf} {op = op} {f = f} {fl = fl} {oc = oc} {k = k} {r = r} {pl = pl} {so = so} {ls = ls} eq
              fp = pd hp
              ea : U.earliest (At.partLanes H ls) ≡ U.found q bs l (U.step l) as
              ea = trans (cong U.earliest eq) (earliest-found fbs fas hq u)
              st = flat-lane {op = op} {o = At.part H so} {LS = At.partLanes H ls} {qs = At.val H (FlatKit.Flat.queue fl)} ea (pool-lane {o = At.part H so} {bs = bs} {l = l} {S = U.step l} {as = as} fp u) (lane-first fo u)
      lift-up ρ₀ (in-source {S = Sj} {c = cj} {b = bj} {kb = kbj} {k = kj} {fd = fdj} {e = ej} {rp = rpj} {rt = rtj} {t = src} {bd = bd} ρ) sn (fb , cl) with peek (At.part H bd)
      ... | peek-nothing pb = ⊥-elim (true≢false (sym (subst (λ z → is-just z ∧ seen H ρ ≡ true) pb sn)))
      ... | peek-just pb with lift-up (ρ₀ ⊕ in-source here) ρ (subst (λ z → is-just z ∧ seen H ρ ≡ true) pb sn) cl
      ...   | c₀ , pc , L , b = _ , held-src {Sj = Sj} {c = cj} {b = bj} {kb = kbj} {k = kj} {fd = fdj} {rp = rpj} {e = ej} {rt = rtj} {src = src} {bd = bd} pc pb , lifts-source (still pc) pb (source-first fb′ b) L , below-source (source-first fb′ b) b
        where fb′ = subst (Opt (Far _)) pb fb
      lift-up ρ₀ (in-body {S = Sj} {c = cj} {b = bj} {kb = kbj} {k = kj} {fd = fdj} {e = nothing} {rp = rpj} {rt = rtj} {t = src} {bd = bd} ρ) sn (fc , rd , cl) with peek (At.part H src)
      ... | peek-nothing ps = ⊥-elim (true≢false (sym (subst (λ z → (is-just z ∨ false) ∧ seen H ρ ≡ true) ps sn)))
      ... | peek-just {c₀} ps with lift-up (ρ₀ ⊕ in-body here) ρ (subst (λ z → (is-just z ∨ false) ∧ seen H ρ ≡ true) ps sn) cl
      ...   | b₀ , pb , L , b =
        _ , held-src {Sj = Sj} {c = cj} {b = bj} {kb = kbj} {k = kj} {fd = fdj} {rp = rpj} {rt = rtj} {src = src} {bd = bd} ps pb , subst (Lifts H _ _) (sym st) (lifts-body ps (body-first fc′ b) L) , subst (Below _) (sym st) (below-body b)
        where fc′ = subst (Opt (Far _)) ps fc
              st = body-step (U.step c₀) (body-first fc′ b)
      lift-up ρ₀ (in-body {S = Sj} {c = cj} {b = bj} {kb = kbj} {k = kj} {fd = fdj} {e = just c₁} {rp = rpj} {rt = rtj} {t = src} {bd = bd} ρ) sn (fc , rd , cl) with peek (At.part H src)
      ... | peek-just {c₀} ps with lift-up (ρ₀ ⊕ in-body here) ρ (subst (λ z → (is-just z ∨ true) ∧ seen H ρ ≡ true) ps sn) cl
      ...   | b₀ , pb , L , b =
        _ , held-src {Sj = Sj} {c = cj} {b = bj} {kb = kbj} {k = kj} {fd = fdj} {rp = rpj} {rt = rtj} {src = src} {bd = bd} ps pb , subst (Lifts H _ _) (sym st) (lifts-body ps (body-first fc′ b) L) , subst (Below _) (sym st) (below-body b)
        where fc′ = subst (Opt (Far _)) ps fc
              st = body-step (U.step c₀) (body-first fc′ b)
      lift-up ρ₀ (in-body {S = Sj} {c = cj} {b = bj} {kb = kbj} {k = kj} {fd = fdj} {e = just c₁} {rp = rpj} {rt = rtj} {t = src} {bd = bd} ρ) sn (fc , rd , cl) | peek-nothing ps
        with lift-up (ρ₀ ⊕ in-body here) ρ (subst (λ z → (is-just z ∨ true) ∧ seen H ρ ≡ true) ps sn) cl
      ...   | b₀ , pb , L , b =
        _ , held-shut {Sj = Sj} {c = cj} {b = bj} {kb = kbj} {k = kj} {fd = fdj} {rp = rpj} {rt = rtj} {src = src} {bd = bd} ps pb , subst (Lifts H _ _) (sym st) (lifts-shut ps refl rb L) , subst (Below _) (sym st) (below-shut b)
        where fr = rd (held-shut {Sj = Sj} {c = cj} {b = bj} {kb = kbj} {k = kj} {fd = fdj} {rp = rpj} {rt = rtj} {src = src} {bd = bd} ps pb) ps refl
              rb = rest-behind fr b
              sh = shut-step cr ρ₀ ρ ps refl pb
              hx = trans (sym (shut-head (U.step (U.shut (Any.here refl) c₁ b₀)))) (trans (cong U.headˢ sh) (shut-head (U.step b₀)))
              st = trans (ended-shut rb hx) sh
      lift-up ρ₀ (in-defer ρ) sn cl with lift-up (ρ₀ ⊕ in-defer here) ρ sn cl
      ... | c , pc , L , b = c , pc , lifts-defer L , b

      lift-up-lanes : ∀ {Δ B} {ls : List (Lane W Δ B)} (κ : ∀ {Δ″ A″} {w : Sub W Δ″ A″} → PathLanes ls w → Path (Carried.tree cr) w)
                      {Δ′ A′ p i x xs} (πL : PathLanes ls (ofˢ {Δ = Δ′} {A′} p i (x ∷ xs)))
                    → seenL H πL ≡ true → ClearL H (Far p) πL
                    → Σ (List (U.Node Δ B)) λ bs → Σ (U.Node Δ B) λ l → Σ (List (U.Node Δ B)) λ as
                      → At.partLanes H ls ≡ bs ++ l ∷ as × LiftsLane H πL (U.step (U.ofᶜ p i (x ∷ xs))) bs (U.step l) as
                        × All (Far p) bs × All (Far p) as × Below p (U.step l)
      lift-up-lanes κ (this-lane {c = c} {ls = ls} ρ) sn (fas , cl) with At.val H (Kit.live c) in lv
      lift-up-lanes κ (this-lane ρ) () (fas , cl) | false
      ... | true with lift-up (κ (this-lane here)) ρ sn cl
      ...   | c′ , pc , L , b rewrite pc = [] , c′ , At.partLanes H ls , refl , lifts-this lv L , [] , fas , b
      lift-up-lanes κ (next-lane {l = l} {ls} πL) sn (fl , cl) with lift-up-lanes (λ πL′ → κ (next-lane πL′)) πL sn cl
      ... | bs , l′ , as , eq , LL , fbs , fas , b =
        At.partLanes H (l ∷ []) ++ bs , l′ , as ,
        trans (lanes-cons l ls) (trans (cong (At.partLanes H (l ∷ []) ++_) eq) (sym (++-assoc (At.partLanes H (l ∷ [])) bs (l′ ∷ as)))) ,
        lifts-next LL , all-++⁺ fl fbs , fas , b

  -- The ghost's step, from a path every sibling of which waits: the
  -- `of`'s step lifted, each operator's side condition read off `Clear`.
  heads-lift : ∀ {g m} (cr : Carried g m) {Δ A p i x xs} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i (x ∷ xs)))
             → seen (Conf.heap (Mach.conf m)) π ≡ true → Clear (Conf.heap (Mach.conf m)) (Far p) π
             → Σ (U.Node [] R) λ c → At.part (Conf.heap (Mach.conf m)) (Carried.tree cr) ≡ just c
               × Lifts (Conf.heap (Mach.conf m)) π (U.step (U.ofᶜ p i (x ∷ xs))) (U.step c)
  heads-lift cr π sn cl with lift-up cr here π sn cl
  ... | c , pc , L , _ = c , pc , L

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
    ; bodies = λ π i → Owned.bodies ow π (subst (λ z → _ ∈ᴸ z) ag i)
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
        ; sorted = hop-sorted cr eq now ; behind = Carried.behind cr })
    , lowered (λ n → agree-refl n _) (inj₁ (inj₂ (refl , inj₂ (refl , inj₂ (refl , inj₁ ≤-refl)))))
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
        ; sorted = hop-sorted cr eq now ; behind = Carried.behind cr })
    , lowered (λ n → agree-refl n _) (inj₁ (inj₂ (refl , inj₂ (refl , inj₂ (refl , inj₁ ≤-refl)))))

  -- A burst's frame stepped: found spent, polled, or played.
  burst-onward : ∀ {g m w K b bs} {σ : w ⊑ Conf.world (Mach.conf m)} (cr : Carried g m) → Conf.ctl (Mach.conf m) ≡ held σ K
               → Mach.bursts m ≡ just b ∷ bs → ∀ {m′} → step m ≡ silent m′ → Hopped (carried cr) m′
  burst-onward {m = m} {b = b} cr c bq eq with spent? (Conf.heap (Mach.conf m)) (Playing.handle b) in sp | Playing.polled b in pl
  ... | true  | _     = burst-spent cr c bq sp eq
  ... | false | false = burst-poll cr c bq sp pl eq
  ... | false | true  = burst-play cr c bq sp pl eq

  -- A value through a map: mapped, one operator up.
  climb-map : ∀ {g ℓ m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {f : A → B} {u : Sub (Conf.world (Mach.conf m₁)) Δ A}
              (ρ : Path T (mapˢ f u)) {y : A} → Climbing g ℓ m₁ (ρ ⊕ in-map here) y → Climbing g ℓ m₁ ρ (f y)
  climb-map {m₁ = m₁} {f = f} ρ {y} cl with Climbing.lifted cl
  ... | c′ , pv , S , L , sg with lifts-split ρ (in-map here) L
  ...   | _ , lifts-map lifts-here , Lρ = reclimb cl
    (subst (λ W → Climbing.act cl ≗ Observer.next (Here.obs W) y) (walk-⊕ ρ (in-map here) top) (Climbing.code cl))
    (U.mapᶜ f c′ , cong (At.mapᴹ (Conf.heap (Mach.conf m₁)) (U.mapᶜ f)) pv , S , Lρ , sg)

  -- A value through a defer, as it is.
  climb-defer : ∀ {g ℓ m₁ Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {k} {u : Sub (Conf.world (Mach.conf m₁)) Δ A}
                (ρ : Path T (deferˢ k u)) {y : A} → Climbing g ℓ m₁ (ρ ⊕ in-defer here) y → Climbing g ℓ m₁ ρ y
  climb-defer ρ {y} cl with Climbing.lifted cl
  ... | c′ , pv , S , L , sg with lifts-split ρ (in-defer here) L
  ...   | _ , lifts-defer lifts-here , Lρ = reclimb cl
    (subst (λ W → Climbing.act cl ≗ Observer.next (Here.obs W) y) (walk-⊕ ρ (in-defer here) top) (Climbing.code cl))
    (c′ , pv , S , Lρ , sg)

  -- A value out of a connect's body, as it is: beside its source, or
  -- past its source's end.
  climb-body : ∀ {g ℓ m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {Sj c b kb k fd e rp rt} {t : Sub (Conf.world (Mach.conf m₁)) Δ A}
               {u : Sub (Conf.world (Mach.conf m₁)) (A ∷ Δ) B} (ρ : Path T (connectˢ Sj c b kb k fd rp e rt t u)) {y : B}
             → Climbing g ℓ m₁ (ρ ⊕ in-body here) y → Climbing g ℓ m₁ ρ y
  climb-body {m₁ = m₁} {e = e} {rp} {rt} ρ {y} cl with Climbing.lifted cl
  ... | c′ , pv , S , L , sg with lifts-split ρ (in-body here) L
  ...   | _ , lifts-body pt _ lifts-here , Lρ = reclimb cl
    (subst (λ W → Climbing.act cl ≗ Observer.next (Here.obs W) y) (walk-⊕ ρ (in-body here) top) (Climbing.code cl))
    (_ , cong₂ (At.connected (Conf.heap (Mach.conf m₁)) rp e rt) pt pv , S , Lρ , sg)
  ...   | _ , lifts-shut pt refl _ lifts-here , Lρ = reclimb cl
    (subst (λ W → Climbing.act cl ≗ Observer.next (Here.obs W) y) (walk-⊕ ρ (in-body here) top) (Climbing.code cl))
    (_ , cong₂ (At.connected (Conf.heap (Mach.conf m₁)) rp e rt) pt pv , S , Lρ , sg)

  -- A live take's part, its source's lifted.
  take-part : ∀ {h} (H : Heapᴹ h) {Δ A} {i p c k} {u : Sub h Δ A} {c′} → At.val H (Kit.live c) ≡ true → At.part H u ≡ just c′
            → At.part H (takeWhileˢ i p c k taking u) ≡ just (U.takeWhileᶜ i p c′)
  take-part H lv pv rewrite lv | pv = refl

  -- A guard read open over a predicate holding: what it guards.
  pass-code : ∀ {w} {b q : Bool} {m n : Act w ⊤} → b ≡ true → q ≡ true → Kit.when b (if q then m else n) ≗ m
  pass-code refl refl = ≗-refl _

  -- A value a live takeWhile passes: its guard read, one operator up,
  -- the tree's load as it was.
  take-pass : ∀ {g ℓ m₁ Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {i p c k}
              {u : Sub (Conf.world (Mach.conf m₁)) Δ A} (ρ : Path T (takeWhileˢ i p c k taking u)) {y : A} → p y ≡ true
            → Climbing g ℓ m₁ (ρ ⊕ in-take here) y → Rises g (load m₁ T) m₁ (ρ ⊕ in-take here)
  take-pass {g} {m₁ = mach ⟨ hp , q , _ ⟩ clk ts bs td lg en mk} {T = T} {i = i} {p = p} {c = c} {k = k} {u = u} ρ {y} py
    record { sane = sn ; placed = pl ; ctl = refl ; code = cd ; stack = sk ; lifted = c′ , pv , S , L , sg ; owned = ow
           ; kernels = kn ; meaning = mn ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn } ; sorted = so
           ; behind = bh ; kept = kp }
    with lifts-split ρ (in-take here) L | subst (λ W → _ ≗ Observer.next (Here.obs W) y) (walk-⊕ ρ (in-take here) top) cd
  ... | _ , lifts-take lv lifts-here , Lρ | readRef≗ refl f =
    rises (then refl now) (one-lower ρ one-take) (record
      { sane = sn ; placed = pl ; ctl = refl
      ; code = ≗-trans (f same⊑ _) (≗-trans (wk-same _) (pass-code lv py))
      ; stack = sk
      ; lifted = U.takeWhileᶜ i p c′ , take-part hp {i = i} {p = p} {c = c} {k = k} {u = u} lv pv , S , subst (λ s → Lifts hp ρ s S) (cong (U.taking i p q y c′) py) Lρ , sg
      ; owned = ow ; kernels = kn ; meaning = mn ; queue = qu
      ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn }
      ; sorted = sorted-⇝ so (then refl now) ; behind = bh ; kept = inj₁ refl })

  -- The value risen, held to the climb's load.
  rise : ∀ {g m} {st : Strong g m} {m₁ Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {v : Sub (Conf.world (Mach.conf m₁)) Δ A} {σ : Path T v}
       → load m₁ T ≼ loadOf st → Rises g (load m₁ T) m₁ σ → Climbed st m₁ σ
  rise le (rises path lt cl) = rose path lt (relevel cl le)

  -- A value through a takeWhile: passed one operator up; or failing,
  -- delivered first when inclusive, then the completion climbs, then
  -- the cut.  The failing value cannot stop at the completion owed with
  -- the ghost alike unless the take's stage counts: the control's work
  -- rises.
  climb-take : ∀ {g m} (st : Strong g m) {m₁ Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {i p c k tk}
               {u : Sub (Conf.world (Mach.conf m₁)) Δ A} (ρ : Path T (takeWhileˢ i p c k tk u)) {y : A}
             → Climbing g (loadOf st) m₁ (ρ ⊕ in-take here) y → Climbed st m₁ (ρ ⊕ in-take here)
  climb-take st {i = i} {p} ρ {y} cl with Climbing.lifted cl
  ... | c′ , pv , S , L , sg with lifts-split ρ (in-take here) L
  ...   | _ , lifts-take lv lifts-here , Lρ with p y in py | i
  ...     | true  | _     = rise (Climbing.kept cl) (take-pass ρ py cl)
  ...     | false | true  = rise (Climbing.kept cl) (take-out ρ py cl)
  ...     | false | false with take-end ρ py cl
  ...       | g″ , m₀ , path , cr , ag , lt = landed (g″ , m₀ , path , carried cr , lowered ag (inj₁ (⊏-≼ lt (Climbing.kept cl))))

  -- A value at the root: recorded next, the ghost's step showing it.
  climb-root : ∀ {g m} (st : Strong g m) {ℓ m₁} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {y : R} → Climbing g ℓ m₁ {T = T} here y → Hopped st m₁
  climb-root {g} st {m₁ = mach ⟨ hp , p , _ ⟩ clk ts bs td lg en mk} {T}
    record { sane = sn ; placed = pl ; ctl = refl ; code = eff≗ ke ; stack = sk ; lifted = c′ , pv , _ , lifts-here , sg ; owned = ow
           ; kernels = kn ; meaning = mn ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = refl } ; sorted = so ; behind = bh } =
    g , _ , then refl now
    , carried (record
        { sane = sn ; placed = pl ; tree = T ; ctlAs = noteAs [] (ke tt) sk ; meets = c′ , pv , sg
        ; owned = owned-move hp (noteAs [] (ke tt) sk) refl refl refl ow ; kernels = kn ; meaning = mn ; queue = qu
        ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = refl } 
        ; sorted = sorted-⇝ so (then refl now) ; behind = bh })
    , showing (agrees (λ n → agree-refl n _)) (λ ())

  -- One operator climbed, by the operator.
  climb-step : ∀ {g m} (st : Strong g m) {m₁ Δ A Δ′ A′} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {u : Sub (Conf.world (Mach.conf m₁)) Δ A}
               {v : Sub (Conf.world (Mach.conf m₁)) Δ′ A′} (ρ : Path T u) {s : Path u v} → One s → ∀ {y} → Climbing g (loadOf st) m₁ (ρ ⊕ s) y → Climbed st m₁ (ρ ⊕ s)
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
          (σ : Path T v) {y : A} → height σ < n → Climbing g (loadOf st) m₁ σ y → Hopped st m₁
  climb st zero    σ () cl
  climb st (suc n) σ lt cl with view σ
  ... | whole      = climb-root st cl
  ... | snoc ρ s o with climb-step st ρ o cl
  ...   | landed hp         = hp
  ...   | rose path lt′ cl′ = hopped-pre path (climb st n _ (≤-trans lt′ (≤-pred lt)) cl′)

  soar : ∀ {g m m′} (st : Strong g m) → Σ Mach (λ m₁ → m′ ⇝ m₁ × Aloft g (loadOf st) m₁) → Hopped st m′
  soar st (m₁ , path , aloft {σ = σ} cl) = hopped-pre path (climb st (suc (height σ)) σ ≤-refl cl)

  -- A COMPLETION ON ITS WAY UP: the observer the path walks to about
  -- to be told its source has ended, the calls `ks` owed after it.  The
  -- node it leaves is gone: the call that owed the end is spent, so the
  -- `of` is done, the take taken, the joiner told.  The ghost's step is
  -- that end lifted along the path.
  record Closing (g : U.Node [] R) (ℓ : Load) (m₁ : Mach) {Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {v : Sub (Conf.world (Mach.conf m₁)) Δ A}
                 (σ : Path T v) : Set₁ where
    field
      sane    : Sane [] g
      placed  : Placed g []
      {w}     : World
      {ϑ}     : w ⊑ Conf.world (Mach.conf m₁)
      {act}   : Act (Conf.world (Mach.conf m₁)) ⊤
      {K}     : Stack w ⊤
      {ks}    : List (Call T)
      ctl     : Conf.ctl (Mach.conf m₁) ≡ run act ϑ K
      code    : act ≗ (Observer.complete (Here.obs (walk σ top)) >>ᴬ ⟦ ks ⟧ᶜ)
      stack   : StackAs T (Conf.pos (Mach.conf m₁)) ϑ K (Mach.bursts m₁)
      gone    : At.part (Conf.heap (Mach.conf m₁)) v ≡ nothing
      lifted  : Σ (U.Step [] R) λ S → Lifts (Conf.heap (Mach.conf m₁)) σ (U.endˢ (Conf.pos (Mach.conf m₁))) S × U.step g ≡ S
      owned   : Owned (Conf.heap (Mach.conf m₁)) T (runAs ks (≗-refl _) stack)
      kernels : Kernels (Conf.heap (Mach.conf m₁)) T
      meaning : Meaning (Conf.heap (Mach.conf m₁)) T
      queue   : Queue (Conf.heap (Mach.conf m₁)) (Conf.pos (Mach.conf m₁)) (Mach.clock m₁) (Mach.timers m₁) T
      books   : Books T (runAs ks (≗-refl _) stack) m₁
      sorted  : Σ Pos λ lo → WellMach lo m₁
      behind  : Each (Conf.heap (Mach.conf m₁)) (Heads (Conf.pos (Mach.conf m₁))) T
      kept    : load m₁ T ≼ ℓ

  -- The same completion, restated at another path.
  reclose : ∀ {g ℓ m₁ Δ A Δ′ A′} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {v : Sub (Conf.world (Mach.conf m₁)) Δ A}
              {v′ : Sub (Conf.world (Mach.conf m₁)) Δ′ A′} {σ : Path T v} (cl : Closing g ℓ m₁ σ) {σ′ : Path T v′}
          → Closing.act cl ≗ (Observer.complete (Here.obs (walk σ′ top)) >>ᴬ ⟦ Closing.ks cl ⟧ᶜ)
          → At.part (Conf.heap (Mach.conf m₁)) v′ ≡ nothing
          → Σ (U.Step [] R) (λ S → Lifts (Conf.heap (Mach.conf m₁)) σ′ (U.endˢ (Conf.pos (Mach.conf m₁))) S × U.step g ≡ S)
          → Closing g ℓ m₁ σ′
  reclose cl cd gn lf = record
    { sane = Closing.sane cl ; placed = Closing.placed cl ; ctl = Closing.ctl cl ; code = cd ; stack = Closing.stack cl ; gone = gn
    ; lifted = lf ; owned = Closing.owned cl ; kernels = Closing.kernels cl ; meaning = Closing.meaning cl ; queue = Closing.queue cl
    ; books = Closing.books cl ; sorted = Closing.sorted cl ; behind = Closing.behind cl ; kept = Closing.kept cl }

  -- One operator closed: a re-entry configuration reached, or the
  -- completion one operator higher, the path shorter.
  data Closed {g m} (st : Strong g m) (m₁ : Mach) {Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {v : Sub (Conf.world (Mach.conf m₁)) Δ A}
              (σ : Path T v) : Set₁ where
    landed : Hopped st m₁ → Closed st m₁ σ
    rose   : ∀ {m₂ Δ′ A′} {T′ : Sub (Conf.world (Mach.conf m₂)) [] R} {v′ : Sub (Conf.world (Mach.conf m₂)) Δ′ A′} {σ′ : Path T′ v′}
           → m₁ ⇝ m₂ → height σ′ < height σ → Closing g (loadOf st) m₂ σ′ → Closed st m₁ σ

  -- Some completion on its way up.
  data Afloat (g : U.Node [] R) (ℓ : Load) (m₁ : Mach) : Set₁ where
    afloat : ∀ {Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {v : Sub (Conf.world (Mach.conf m₁)) Δ A} {σ : Path T v}
           → Closing g ℓ m₁ σ → Afloat g ℓ m₁

  -- A completion through a map, as it is.
  close-map : ∀ {g ℓ m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {f : A → B} {u : Sub (Conf.world (Mach.conf m₁)) Δ A}
              (ρ : Path T (mapˢ f u)) → Closing g ℓ m₁ (ρ ⊕ in-map here) → Closing g ℓ m₁ ρ
  close-map {m₁ = m₁} {f = f} {u} ρ cl with Closing.lifted cl
  ... | S , L , sg with lifts-split ρ (in-map here) L
  ...   | _ , lifts-map lifts-here , Lρ = reclose cl
    (subst (λ W → Closing.act cl ≗ (Observer.complete (Here.obs W) >>ᴬ ⟦ Closing.ks cl ⟧ᶜ)) (walk-⊕ ρ (in-map here) top) (Closing.code cl))
    (cong (At.mapᴹ (Conf.heap (Mach.conf m₁)) (U.mapᶜ f)) (Closing.gone cl))
    (S , Lρ , sg)

  -- A completion through a scan, as it is: the scan's cell unread.
  close-scan : ∀ {g ℓ m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {f : B → A → B} {r} {u : Sub (Conf.world (Mach.conf m₁)) Δ A}
               (ρ : Path T (scanˢ f r u)) → Closing g ℓ m₁ (ρ ⊕ in-scan here) → Closing g ℓ m₁ ρ
  close-scan {m₁ = m₁} {f = f} {r} {u} ρ cl with Closing.lifted cl
  ... | S , L , sg with lifts-split ρ (in-scan here) L
  ...   | _ , lifts-scan lifts-here , Lρ = reclose cl
    (subst (λ W → Closing.act cl ≗ (Observer.complete (Here.obs W) >>ᴬ ⟦ Closing.ks cl ⟧ᶜ)) (walk-⊕ ρ (in-scan here) top) (Closing.code cl))
    (cong (At.mapᴹ (Conf.heap (Mach.conf m₁)) (U.scanᶜ f (At.val (Conf.heap (Mach.conf m₁)) r))) (Closing.gone cl))
    (S , Lρ , sg)

  -- A completion through a defer, as it is.
  close-defer : ∀ {g ℓ m₁ Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {k} {u : Sub (Conf.world (Mach.conf m₁)) Δ A}
                (ρ : Path T (deferˢ k u)) → Closing g ℓ m₁ (ρ ⊕ in-defer here) → Closing g ℓ m₁ ρ
  close-defer ρ cl with Closing.lifted cl
  ... | S , L , sg with lifts-split ρ (in-defer here) L
  ...   | _ , lifts-defer lifts-here , Lρ = reclose cl
    (subst (λ W → Closing.act cl ≗ (Observer.complete (Here.obs W) >>ᴬ ⟦ Closing.ks cl ⟧ᶜ)) (walk-⊕ ρ (in-defer here) top) (Closing.code cl))
    (Closing.gone cl) (S , Lρ , sg)

  -- A guard read open: what it guards.
  open-code : ∀ {w} {b : Bool} {m : Act w ⊤} → b ≡ true → Kit.when b m ≗ m
  open-code refl = ≗-refl _

  -- A live take over a gone source is gone.
  gone-take : ∀ {h} (H : Heapᴹ h) {Δ A} {i p c k} {u : Sub h Δ A} → At.val H (Kit.live c) ≡ true
            → At.part H u ≡ nothing → At.part H (takeWhileˢ i p c k taking u) ≡ nothing
  gone-take H lv gn rewrite lv | gn = refl

  -- A completion through a live takeWhile: its guard read open, one
  -- operator up, the take showing its source's end.
  close-take : ∀ {g m} (st : Strong g m) {m₁ Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {i p c k tk}
               {u : Sub (Conf.world (Mach.conf m₁)) Δ A} (ρ : Path T (takeWhileˢ i p c k tk u))
             → Closing g (loadOf st) m₁ (ρ ⊕ in-take here) → Closed st m₁ (ρ ⊕ in-take here)
  close-take st {m₁ = mach ⟨ hp , q , _ ⟩ clk ts bs td lg en mk} {T = T} {i = i} {p = p} {c = c} {k = k} {u = u} ρ
    record { sane = sn ; placed = pl ; ks = ks ; ctl = refl ; code = cd ; stack = sk ; gone = gn ; lifted = S , L , sg ; owned = ow
           ; kernels = kn ; meaning = mn ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn } ; sorted = so
           ; behind = bh ; kept = kp }
    with lifts-split ρ (in-take here) L | subst (λ W → _ ≗ (Observer.complete (Here.obs W) >>ᴬ ⟦ ks ⟧ᶜ)) (walk-⊕ ρ (in-take here) top) cd
  ... | _ , lifts-take lv lifts-here , Lρ | readRef≗ refl f =
    rose (then refl now) (one-lower ρ one-take) (record
      { sane = sn ; placed = pl ; ctl = refl
      ; code = ≗-trans (f same⊑ _) (bind≗ (≗-trans (wk-same _) (open-code lv)) λ _ → wk-same _)
      ; stack = sk
      ; gone = gone-take hp {i = i} {p = p} {c = c} {k = k} {u = u} lv gn
      ; lifted = S , Lρ , sg
      ; owned = ow ; kernels = kn ; meaning = mn ; queue = qu
      ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn }
      ; sorted = sorted-⇝ so (then refl now) ; behind = bh ; kept = kp })

  -- A body's cut owed ahead of the agenda, its body gone.
  owned-body : ∀ {h} (H : Heapᴹ h) {t : Sub h [] R} {p c bs p₀ c₀ bs₀} {ca : CtlAs t p c bs} (ca₀ : CtlAs t p₀ c₀ bs₀)
               {Δ A B Sj cc b kb k fd e rp rt q} {s : Sub h Δ A} {bd : Sub h (A ∷ Δ) B} (ρ : Path t (connectˢ Sj cc b kb k fd rp e rt s bd))
             → agenda t ca₀ ≡ (q , bodyC ρ) ∷ agenda t ca → bursts t ca₀ ≡ bursts t ca → begins t ca₀ ≡ begins t ca
             → At.part H bd ≡ nothing → Owned H t ca → Owned H t ca₀
  owned-body H {t} {ca = ca} ca₀ {q = q} ρ ag bu be gn ow = record
    { ofs    = λ π → subst (λ z → _ ∈ᴸ z) (sym ag) (there (Owned.ofs ow π))
    ; plays  = λ π nsp → subst (λ z → _ ∈ᴸ z) (sym bu) (Owned.plays ow π nsp)
    ; fires  = λ π nsp → subst (λ z → _ ∈ᴸ z) (sym bu) (Owned.fires ow π nsp)
    ; begun  = λ π → subst (λ z → _ ∈ᴸ z) (sym be) (Owned.begun ow π)
    ; ends   = λ π l → subst (λ z → _ ∈ᴸ z) (sym ag) (there (Owned.ends ow π l))
    ; cuts   = λ π l → proj₁ (Owned.cuts ow π l) , subst (λ z → _ ∈ᴸ z) (sym ag) (there (proj₂ (Owned.cuts ow π l)))
    ; feeds  = λ π → subst (λ z → _ ∈ᴸ z) (sym ag) (there (Owned.feeds ow π))
    ; fins   = λ π → subst (λ z → _ ∈ᴸ z) (sym ag) (there (Owned.fins ow π))
    ; bodies = λ π i → bodied π (subst (λ z → _ ∈ᴸ z) ag i)
    ; placed = subst (All (Placedᴬ t)) (sym ag) (tt ∷ Owned.placed ow) }
    where
      bodied : ∀ {Δ′ A′ B′ Sj′ c′ b′ kb′ k′ fd′ e′ rp′ rt′ q′} {s′ : Sub _ Δ′ A′} {bd′ : Sub _ (A′ ∷ Δ′) B′}
               (π : Path t (connectˢ Sj′ c′ b′ kb′ k′ fd′ rp′ e′ rt′ s′ bd′)) → (q′ , bodyC π) ∈ᴸ (q , bodyC ρ) ∷ agenda t ca → At.part H bd′ ≡ nothing
      bodied π (here refl) = gn
      bodied π (there i)   = Owned.bodies ow π i

  -- A connect over a gone body is gone.
  gone-connect : ∀ {h} (H : Heapᴹ h) {Δ A B Sj c b kb k fd e rp rt} {t : Sub h Δ A} {u : Sub h (A ∷ Δ) B}
               → At.part H u ≡ nothing → At.part H (connectˢ Sj c b kb k fd rp e rt t u) ≡ nothing
  gone-connect H {t = t} gn rewrite gn with At.part H t
  ... | just _  = refl
  ... | nothing = refl

  -- An end lifted out of a body is the connect's end.
  body-end : ∀ {h} {H : Heapᴹ h} {Δ A B Sj c b kb k fd e rp rt} {t : Sub h Δ A} {u : Sub h (A ∷ Δ) B} {q S}
           → Lifts H (in-body {S = Sj} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {t = t} (here {t = u})) (U.endˢ q) S → S ≡ U.endˢ q
  body-end (lifts-body _ _ lifts-here)   = refl
  body-end (lifts-shut _ _ _ lifts-here) = refl

  -- A connect's body ended: the connect's completion delivered, its
  -- cut owed after it, the body gone as a `bodyC` owed asks.
  close-body : ∀ {g m} (st : Strong g m) {m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {Sj c b kb k fd e rp rt}
               {t : Sub (Conf.world (Mach.conf m₁)) Δ A} {u : Sub (Conf.world (Mach.conf m₁)) (A ∷ Δ) B}
               (ρ : Path T (connectˢ Sj c b kb k fd rp e rt t u))
             → Closing g (loadOf st) m₁ (ρ ⊕ in-body here) → Closed st m₁ (ρ ⊕ in-body here)
  close-body st {m₁ = m₁} {T = T} {Sj} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {t = t} {u} ρ
    record { sane = sn ; placed = pl ; ks = ks ; ctl = cx ; code = cd ; stack = sk ; gone = gn ; lifted = S , L , sg ; owned = ow
           ; kernels = kn ; meaning = mn ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn } ; sorted = so
           ; behind = bh ; kept = kp }
    with lifts-split ρ (in-body here) L
  ... | _ , Lb , Lρ = rose now (one-lower ρ one-body) (record
      { sane = sn ; placed = pl ; ks = bodyC ρ ∷ ks ; ctl = cx
      ; code = ≗-trans (subst (λ W → _ ≗ (Observer.complete (Here.obs W) >>ᴬ ⟦ ks ⟧ᶜ)) (walk-⊕ ρ (in-body here) top) cd) (seq-assoc (Observer.complete (Here.obs (walk ρ top))) (Kit.cut c) ⟦ ks ⟧ᶜ)
      ; stack = sk
      ; gone = gone-connect (Conf.heap (Mach.conf m₁)) {Sj = Sj} {c = c} {b = b} {kb = kb} {k = k} {fd = fd} {e = e} {rp = rp} {rt = rt} {t = t} {u = u} gn
      ; lifted = S , subst (λ s → Lifts (Conf.heap (Mach.conf m₁)) ρ s S) (body-end Lb) Lρ , sg
      ; owned = owned-body (Conf.heap (Mach.conf m₁)) (runAs (bodyC ρ ∷ ks) (≗-refl ⟦ bodyC ρ ∷ ks ⟧ᶜ) sk) ρ refl refl refl gn ow
      ; kernels = kn ; meaning = mn ; queue = qu
      ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn }
      ; sorted = so ; behind = bh ; kept = kp })

  postulate
    -- A flatMap's outer ended: its done flag written, settled: the
    -- flatMap ends if no lane is left, or the lanes run on.
    close-outer : ∀ {g m} (st : Strong g m) {m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {op f fl oc k r pl}
                  {u : Sub (Conf.world (Mach.conf m₁)) Δ A} {ls : List (Lane (Conf.world (Mach.conf m₁)) Δ B)}
                  (ρ : Path T (flatMapˢ op f fl oc k r pl u ls))
                → Closing g (loadOf st) m₁ (ρ ⊕ in-outer here) → Closed st m₁ (ρ ⊕ in-outer here)

    -- A lane ended: shut, the active count down, the next queued value
    -- begun or the flatMap ended past its outer's end.
    close-lanes : ∀ {g m} (st : Strong g m) {m₁ Δ A B Δ′ C} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {op f fl oc k r pl}
                  {t : Sub (Conf.world (Mach.conf m₁)) Δ A} {ls : List (Lane (Conf.world (Mach.conf m₁)) Δ B)} {u : Sub (Conf.world (Mach.conf m₁)) Δ′ C}
                  (ρ : Path T (flatMapˢ op f fl oc k r pl t ls)) (πL : PathLanes ls u) → OneLane πL
                → Closing g (loadOf st) m₁ (ρ ⊕ in-lanes πL) → Closed st m₁ (ρ ⊕ in-lanes πL)

    -- A connect's source ended: its subject closed, the finish of its
    -- subscribers owed.
    close-source : ∀ {g m} (st : Strong g m) {m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {Sj c b kb k fd e rp rt}
                   {u : Sub (Conf.world (Mach.conf m₁)) Δ A} {bd : Sub (Conf.world (Mach.conf m₁)) (A ∷ Δ) B}
                   (ρ : Path T (connectˢ Sj c b kb k fd rp e rt u bd))
                 → Closing g (loadOf st) m₁ (ρ ⊕ in-source here) → Closed st m₁ (ρ ⊕ in-source here)

  -- A completion at the root: the run's end asked of the record, the
  -- ghost's step its end.
  close-root : ∀ {g m} (st : Strong g m) {ℓ m₁} {T : Sub (Conf.world (Mach.conf m₁)) [] R} → Closing g ℓ m₁ {T = T} here → Hopped st m₁
  close-root {g} st {m₁ = mach ⟨ hp , p , _ ⟩ clk ts bs td lg en mk}
    record { sane = sn ; placed = pl ; ctl = refl ; code = eff≗ _ ; lifted = _ , lifts-here , sg ; books = record { running = refl } } =
    g , _ , then refl now , closing refl refl sg sn pl , showing (agrees (λ n → agree-refl n _)) (λ ())

  -- One operator closed, by the operator.
  close-step : ∀ {g m} (st : Strong g m) {m₁ Δ A Δ′ A′} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {u : Sub (Conf.world (Mach.conf m₁)) Δ A}
               {v : Sub (Conf.world (Mach.conf m₁)) Δ′ A′} (ρ : Path T u) {s : Path u v} → One s → Closing g (loadOf st) m₁ (ρ ⊕ s) → Closed st m₁ (ρ ⊕ s)
  close-step st ρ one-map       cl = rose now (one-lower ρ one-map) (close-map ρ cl)
  close-step st ρ one-scan      cl = rose now (one-lower ρ one-scan) (close-scan ρ cl)
  close-step st ρ one-take      cl = close-take st ρ cl
  close-step st ρ one-outer     cl = close-outer st ρ cl
  close-step st ρ (one-lanes o) cl = close-lanes st ρ _ o cl
  close-step st ρ one-source    cl = close-source st ρ cl
  close-step st ρ one-body      cl = close-body st ρ cl
  close-step st ρ one-defer     cl = rose now (one-lower ρ one-defer) (close-defer ρ cl)

  -- A COMPLETION CLIMBS TO A RE-ENTRY CONFIGURATION, as a value does.
  close : ∀ {g m} (st : Strong g m) (n : ℕ) {m₁ Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {v : Sub (Conf.world (Mach.conf m₁)) Δ A}
          (σ : Path T v) → height σ < n → Closing g (loadOf st) m₁ σ → Hopped st m₁
  close st zero    σ () cl
  close st (suc n) σ lt cl with view σ
  ... | whole      = close-root st cl
  ... | snoc ρ s o with close-step st ρ o cl
  ...   | landed hp         = hp
  ...   | rose path lt′ cl′ = hopped-pre path (close st n _ (≤-trans lt′ (≤-pred lt)) cl′)

  float : ∀ {g m m′} (st : Strong g m) → Σ Mach (λ m₁ → m′ ⇝ m₁ × Afloat g (loadOf st) m₁) → Hopped st m′
  float st (m₁ , path , afloat {σ = σ} cl) = hopped-pre path (close st (suc (height σ)) σ ≤-refl cl)

  postulate
    -- A takeWhile's completion begun under its failing value, its cut
    -- the frame's rest.
    take1-enter : ∀ {g m} (cr : Carried g m) {Δ A i p c k q n} {s : Sub _ Δ A} (π : Path (Carried.tree cr) (takeWhileˢ i p c k (Strongly.ending q n) s))
                → firstCall (Carried.ctlAs cr) ≡ just (take1C π) → ∀ {m′} → step m ≡ silent m′
                → Σ Mach λ m₁ → m′ ⇝ m₁ × Afloat g (load m (Carried.tree cr)) m₁

    -- A spent `of`'s completion begun at its end.
    last-enter : ∀ {g m} (cr : Carried g m) {Δ A p i} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i []))
               → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → ∀ {m′} → step m ≡ silent m′
               → Σ Mach λ m₁ → m′ ⇝ m₁ × Afloat g (load m (Carried.tree cr)) m₁

    -- A connect's feed of its source's end: no subscriber left, the
    -- agenda on; or the next subscriber's completion begun.
    fin-enter : ∀ {g m} (cr : Carried g m) {Δ A B S c b kb k r ss e rp rt} {s : Sub _ Δ A} {bd : Sub _ (A ∷ Δ) B}
                (π : Path (Carried.tree cr) (connectˢ S c b kb k (finishing r ss) rp e rt s bd))
              → firstCall (Carried.ctlAs cr) ≡ just (finC π) → ∀ {m′} → step m ≡ silent m′
              → Σ Mach λ m₁ → m′ ⇝ m₁ × (Hopped (carried cr) m₁ ⊎ Afloat g (load m (Carried.tree cr)) m₁)

  -- A takeWhile's completion delivered under its failing value, then
  -- its cut.
  take1-onward : ∀ {g m} (cr : Carried g m) {Δ A i p c k q n} {s : Sub _ Δ A} (π : Path (Carried.tree cr) (takeWhileˢ i p c k (Strongly.ending q n) s))
               → firstCall (Carried.ctlAs cr) ≡ just (take1C π) → Hops cr
  take1-onward cr π fc eq = float (carried cr) (take1-enter cr π fc eq)

  -- A spent `of`'s completion delivered at its end.
  emit-last : ∀ {g m} (cr : Carried g m) {Δ A p i} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i []))
            → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → Hops cr
  emit-last cr π fc eq = float (carried cr) (last-enter cr π fc eq)

  -- The rest of a connect's feed of its source's end.
  fin-onward : ∀ {g m} (cr : Carried g m) {Δ A B S c b kb k r ss e rp rt} {s : Sub _ Δ A} {bd : Sub _ (A ∷ Δ) B}
               (π : Path (Carried.tree cr) (connectˢ S c b kb k (finishing r ss) rp e rt s bd))
             → firstCall (Carried.ctlAs cr) ≡ just (finC π) → Hops cr
  fin-onward cr π fc eq with fin-enter cr π fc eq
  ... | m₁ , path , inj₁ hp = hopped-pre path hp
  ... | m₁ , path , inj₂ af = float (carried cr) (m₁ , path , af)

  -- An agenda under way: the ghost is the tree's part.
  run-meets : ∀ {h} {t : Sub h [] R} {p c bs} (ca : CtlAs t p c bs) {n g k} → firstCall ca ≡ just k → Meets ca n g → n ≡ just g
  run-meets (runAs (_ ∷ _) _ _) refl mt = mt
  run-meets (runAs [] _ _)      ()
  run-meets calmAs              ()
  run-meets (noteAs _ _ _)      ()
  run-meets (subAs _ _ _)       ()
  run-meets (burstAs _ _ _)     ()

  -- The agenda's first call an `of` at `p`: the run is at `p`.
  run-at : ∀ {h} {t : Sub h [] R} {q c bs} (ca : CtlAs t q c bs) {Δ A p i xs} {π : Path t (ofˢ {Δ = Δ} {A} p i xs)}
         → firstCall ca ≡ just (emitC π) → All (Placedᴬ t) (agenda t ca) → q ≡ p
  run-at (runAs (_ ∷ _) _ _) refl (pl ∷ _) = pl
  run-at (runAs [] _ _)      ()
  run-at calmAs              ()
  run-at (noteAs _ _ _)      ()
  run-at (subAs _ _ _)       ()
  run-at (burstAs _ _ _)     ()

  -- The agenda's first call an open `of` the ghost holds: every sibling
  -- its path passes heads past the `of`'s base, no earlier than the run
  -- (`Carried.behind`) and not under it.
  -- DEAD ROUTE: a per-frame order.  A stack frame's calls are ordered
  --   against the current position only by `backAs`'s `q <ᵖ p`, which
  --   does not make `q` a prefix of `p`: a frame at `q` beside `p`
  --   holding an `of` has its next value ahead of this one.
  others-past : ∀ {g m} (cr : Carried g m) {Δ A p i x xs} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i (x ∷ xs)))
              → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → opened (Conf.heap (Mach.conf m)) true π ≡ true
              → seen (Conf.heap (Mach.conf m)) π ≡ true → Clear (Conf.heap (Mach.conf m)) (Far p) π
  others-past {m = m} cr {p = p} π fc op sn =
    clear-zip {P = Heads p} {Q = Off p} {R′ = Far p} (λ {Γ} {A} {c} → far-apart {p} {Γ} {A} {c}) π
      (clear-each (subst (λ q → Each (Conf.heap (Mach.conf m)) (Heads q) (Carried.tree cr))
                         (run-at (Carried.ctlAs cr) fc (Owned.placed (Carried.owned cr))) (Carried.behind cr)) π sn refl)
      (spread-past cr π fc op sn)

  -- The agenda's first call an open `of` the ghost holds: the ghost's
  -- step is that `of`'s, lifted.
  emit-lifts : ∀ {g m} (cr : Carried g m) {Δ A p i x xs} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i (x ∷ xs)))
             → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → opened (Conf.heap (Mach.conf m)) true π ≡ true
             → seen (Conf.heap (Mach.conf m)) π ≡ true → Lifts (Conf.heap (Mach.conf m)) π (U.step (U.ofᶜ p i (x ∷ xs))) (U.step g)
  emit-lifts cr π fc op sn with heads-lift cr π sn (others-past cr π fc op sn)
  ... | c , pc , L = subst (λ c′ → Lifts _ π _ (U.step c′)) (just-injective (trans (sym pc) (run-meets (Carried.ctlAs cr) fc (Carried.meets cr)))) L

  -- An open `of` the ghost holds: its value on its way up, the ghost's
  -- step that value lifted.
  emit-open : ∀ {g m} (cr : Carried g m) {Δ A p i x xs} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i (x ∷ xs)))
            → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → opened (Conf.heap (Mach.conf m)) true π ≡ true
            → seen (Conf.heap (Mach.conf m)) π ≡ true → ∀ {m′} → step m ≡ silent m′ → Σ Mach λ m₁ → m′ ⇝ m₁ × Aloft g (load m (Carried.tree cr)) m₁
  emit-open cr π fc op sn = emit-run cr π fc op (emit-lifts cr π fc op sn)

  -- An `of` the ghost does not hold: the ghost alike, the load lighter.
  emit-unseen : ∀ {g m} (cr : Carried g m) {Δ A p i x xs} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i (x ∷ xs)))
              → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → opened (Conf.heap (Mach.conf m)) true π ≡ true
              → seen (Conf.heap (Mach.conf m)) π ≡ false → Hops cr
  emit-unseen cr π fc op sn eq with emit-void cr π fc op sn eq
  ... | g″ , m₀ , path , cr₀ , ag , lt = g″ , m₀ , path , carried cr₀ , lowered ag (inj₁ lt)

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
  run-onward {m = mach ⟨ _ , _ , _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = runAs (take2C π ∷ _) _ _ } refl eq = cut-onward cr (takeSite π) refl eq
  run-onward {m = mach ⟨ _ , _ , _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = runAs (bodyC π ∷ _) _ _ } refl eq = cut-onward cr (bodySite π) refl eq
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
        ; sorted = hop-sorted cr refl (then refl now) ; behind = Carried.behind cr })
    , lowered (λ n → agree-refl n _) (inj₂ (refl , ≤-refl))
  run-onward {g} {mach ⟨ hp , p , _ ⟩ clk ts _ _ lg en mk}
    cr@record { tree = t ; ctlAs = runAs [] (done≗ refl) (restAs ks e K″) ; meets = mt ; owned = ow ; kernels = kn ; meaning = mn ; queue = qu
              ; books = record { fresh = fs ; clocked = ck ; paidUp = refl ; running = rn } } refl refl =
    g , _ , then refl now
    , carried (record
        { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = t ; ctlAs = runAs ks e K″ ; meets = mt
        ; owned = owned-move hp (runAs ks e K″) refl refl refl ow ; kernels = kn ; meaning = mn ; queue = qu
        ; books = record { fresh = fs ; clocked = proj₂ ck ; paidUp = refl ; running = rn } 
        ; sorted = hop-sorted cr refl (then refl now) ; behind = Carried.behind cr })
    , lowered (λ n → agree-refl n _) (inj₂ (refl , ≤-refl))
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
        ; sorted = hop-sorted cr refl (then refl now) ; behind = each-back qp (Carried.behind cr) })
    , lowered (λ n → agree-refl n _) (inj₂ (refl , ≤-refl))
  run-onward {g} {mach ⟨ hp , p , _ ⟩ clk ts _ _ lg en mk}
    cr@record { tree = t ; ctlAs = runAs [] (done≗ refl) (reholdAs (playsAs π) hᴷ K″) ; meets = mt ; owned = ow ; kernels = kn ; meaning = mn ; queue = qu
              ; books = record { fresh = fs ; clocked = ck ; paidUp = refl ; running = rn } } refl refl =
    g , _ , then refl now
    , carried (record
        { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = t ; ctlAs = burstAs (playsAs π) hᴷ K″ ; meets = mt
        ; owned = owned-move hp (burstAs (playsAs π) hᴷ K″) refl refl refl ow ; kernels = kn ; meaning = mn ; queue = qu
        ; books = record { fresh = fs ; clocked = proj₂ ck ; paidUp = refl ; running = rn } 
        ; sorted = hop-sorted cr refl (then refl now) ; behind = Carried.behind cr })
    , lowered (λ n → agree-refl n _) (inj₂ (refl , m<n⇒m<1+n ≤-refl))
  run-onward {g} {mach ⟨ hp , p , _ ⟩ clk ts _ _ lg en mk}
    cr@record { tree = t ; ctlAs = runAs [] (done≗ refl) (reholdAs (firesAs π) hᴷ K″) ; meets = mt ; owned = ow ; kernels = kn ; meaning = mn ; queue = qu
              ; books = record { fresh = fs ; clocked = ck ; paidUp = refl ; running = rn } } refl refl =
    g , _ , then refl now
    , carried (record
        { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = t ; ctlAs = burstAs (firesAs π) hᴷ K″ ; meets = mt
        ; owned = owned-move hp (burstAs (firesAs π) hᴷ K″) refl refl refl ow ; kernels = kn ; meaning = mn ; queue = qu
        ; books = record { fresh = fs ; clocked = proj₂ ck ; paidUp = refl ; running = rn } 
        ; sorted = hop-sorted cr refl (then refl now) ; behind = Carried.behind cr })
    , lowered (λ n → agree-refl n _) (inj₂ (refl , m<n⇒m<1+n ≤-refl))
  run-onward {g} {mach ⟨ hp , p , _ ⟩ clk ts _ _ lg en mk}
    cr@record { tree = t ; ctlAs = runAs [] (done≗ refl) (reholdAs overAs bottomᴴ bottomAs) ; meets = mt ; owned = ow ; kernels = kn ; meaning = mn ; queue = qu
              ; books = record { fresh = fs ; paidUp = refl ; running = rn } } refl refl =
    g , _ , then refl (then refl now)
    , carried (record
        { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = t ; ctlAs = calmAs ; meets = mt
        ; owned = owned-move hp calmAs refl refl refl ow ; kernels = kn ; meaning = mn ; queue = qu
        ; books = record { fresh = fs ; clocked = tt ; paidUp = refl ; running = rn } 
        ; sorted = hop-sorted cr refl (then refl (then refl now)) ; behind = Carried.behind cr })
    , lowered (λ n → agree-refl n _) (inj₁ (inj₂ (refl , inj₂ (refl , inj₂ (refl , inj₁ ≤-refl)))))
  run-onward {g} {mach ⟨ hp , p , _ ⟩ clk ts _ _ lg en mk}
    cr@record { tree = t ; ctlAs = runAs [] (done≗ refl) (reholdAs overAs restᴴ (restAs ks e K‴)) ; meets = mt ; owned = ow ; kernels = kn ; meaning = mn
              ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = refl ; running = rn } } refl refl =
    g , _ , then refl (then refl now)
    , carried (record
        { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = t ; ctlAs = runAs ks e K‴ ; meets = mt
        ; owned = owned-move hp (runAs ks e K‴) refl refl refl ow ; kernels = kn ; meaning = mn ; queue = qu
        ; books = record { fresh = fs ; clocked = proj₂ (proj₂ ck) ; paidUp = refl ; running = rn } 
        ; sorted = hop-sorted cr refl (then refl (then refl now)) ; behind = Carried.behind cr })
    , lowered (λ n → agree-refl n _) (inj₁ (inj₂ (refl , inj₂ (refl , inj₂ (refl , inj₁ ≤-refl)))))

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
        ; placed = proj₂ (subst (Placedˢ []) stp (placed-after g (Carried.sane cr) (Carried.placed cr)))
        ; tree = t ; ctlAs = runAs ks ke K ; meets = pe
        ; owned = record { ofs = Owned.ofs ow ; plays = Owned.plays ow ; fires = Owned.fires ow ; begun = Owned.begun ow
                         ; ends = Owned.ends ow ; cuts = Owned.cuts ow ; feeds = Owned.feeds ow ; fins = Owned.fins ow ; bodies = Owned.bodies ow
                         ; placed = Owned.placed ow }
        ; kernels = Carried.kernels cr ; meaning = Carried.meaning cr ; queue = Carried.queue cr
        ; books = record { fresh = Books.fresh (Carried.books cr) ; clocked = Books.clocked (Carried.books cr)
                         ; paidUp = Books.paidUp (Carried.books cr) ; running = refl } 
        ; sorted = sorted-value (Carried.sorted cr) refl ; behind = Carried.behind cr })

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
        ; sorted = hop-sorted cr refl (then (drop-spent tm sp) now) ; behind = Carried.behind cr })
    , lowered (λ n → agree-refl n _) (inj₁ (inj₂ (refl , inj₂ (refl , inj₁ ≤-refl))))
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
                           ; gated = gated-plant hp {t = t} π v (λ _ → lift (λ _ → refl)) (λ s → s) (Kernels.gated kn) }
        ; meaning = record { fed = fed-plant hp {t = t} π v (λ _ f → f) _ (Meaning.fed mn) }
        ; queue = record { timed = timed-pop hp {t = t} π (Queue.timed q) (Queue.ordered q) fs
                         ; joined = subst₂ (At.Joined hp) (sym (subjects-plant {t = t} π v refl)) (sym (joiners-plant {t = t} π v (λ _ → refl) _)) (Queue.joined q)
                         ; ordered = tail (Queue.ordered q) ; ahead = ahead-pop {p = p} (Queue.ordered q) (Queue.ahead q) }
        ; books = record { fresh = subst (AllPairs _≢_) (sym (names-plant {t = t} π v refl)) fs ; clocked = refl , tt ; paidUp = refl ; running = rn } 
        ; sorted = hop-sorted cr refl now ; behind = behind-fire cr π })
    , lowered (λ n → agree-refl n _) (inj₁ (inj₂ (pend-plant {t = t} π v refl , inj₂ (takes-plant {t = t} π v refl , inj₁ ≤-refl))))
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
