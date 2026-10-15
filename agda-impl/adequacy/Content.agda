{-# OPTIONS --guardedness #-}

-- CONTENT: the root's record is the meaning's events, as a set.
-- Sortedness (`adequacy.Sorted`) says nothing of WHAT arrives; this says
-- nothing of the ORDER, so neither proof reads the other.
--
-- A GHOST: the meaning's own configuration (`denotation.Unfold`'s
-- `Node`), which the machine's configuration runs.  What is still to be
-- delivered is the ghost's residual, the limit of its approximants at the
-- root; at the launch the ghost is the program subscribed there, so the
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
open import Data.Nat.Properties using (suc-injective)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import denotation.MonotonicList using (Events; Events∞; Pos; Time; Timeline; tick; out; skip; end; hush; observe; root; Agree; out⁼; skip⁼; end⁼;
  agree; agree-sym; agree-trans; lub; lub-limit; Settling; agrees) renaming (cold to coldᴹ)
import denotation.Unfold as U
open import denotation.Compositional using (from; settle; []ᵉ)
open import adequacy.Sorted using (_≤ᵖ_)
open import operation.Machine using (module Machine)
open import adequacy.Record using (module Recording)
open import adequacy.Strong using (module Strongly)
open import denotation.Denote using (⟦_⟧)
open import operation.PureObservable using (PureObs; Out; note; module Pure)
open import operation.AbstractObservable using (module Heap) renaming (module Machine to Shared)
open import Data.Bool using (Bool; true; false; if_then_else_)

open Events∞

module Honesty (R : Set) where
  open Machine R using (Mach; mach; Playing; Step; silent; value; complete; drained; step; trace; shown; reading; begin; launch; Read; read)
  open Shared Timeline (Out R) using (Conf; ⟨_,_,_⟩; held; run; asking; bottom; spent?)
  open Heap using (_⊑_)
  open Recording R using (silent-keeps; value-notes)
  open Strongly R using (Strong; strong-begin; Carried; Books; carried; closing; Sane)
  open Strongly.Against R using (calmAs; noteAs; subAs; burstAs)
  open Pure R using (End; finished; dry; cutOff; recorder)
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

  -- What a configuration of the meaning will show: its approximants'
  -- limit, at the root.
  residual : U.Node [] R → Events R
  residual g = observe (lub λ n → coldᴹ λ _ → U.meaning n g []) root

  -- The program subscribed at the root shows the meaning's events: each
  -- approximant of its configuration is the fold's, so they settle as the
  -- fold's do, and their limit is the fold's limit.
  begun : (o : PureObs [] R) → ∀ n → Agree n (observe (⟦ o ⟧ []) root) (residual (U.subscribe o root))
  begun o n = agree-trans (agree (from n o []) root)
                (agree-trans (agree-sym (agree (U.subscribed n o []ᵉ) root)) (agree (lub-limit settling n) root))
    where
    settling : Settling (λ n → coldᴹ λ _ → U.meaning n (U.subscribe o root) [])
    settling n = agrees λ _ → agree-trans (agree (U.subscribed n o []ᵉ) root)
                   (agree-trans (agree (settle n o []) root) (agree-sym (agree (U.subscribed {k = n} (suc n) o []ᵉ) root)))

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
  after (U.outˢ k a g′) = out k a λ where .force → residual g′
  after (U.skipˢ k g′)  = skip k λ where .force → residual g′
  after (U.endˢ k)      = end k
  after U.hushˢ         = hush

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

  -- A ghost whose residual is `g`'s, which `m′` runs.
  Ahead : U.Node [] R → Mach → Set₁
  Ahead g m′ = Σ (U.Node [] R) λ g″ → residual g ≋ residual g″ × Mirror g″ m′

  onward : ∀ {rest g m′} → rest ≋ residual g → Ahead g m′ → Inner rest m′
  onward e (g″ , s , mi) = record { ghost = g″ ; same = ≋-trans e s ; mirror = mi }

  -- The driver's turn with a burst held is silent, whatever the burst.
  if-silent : ∀ (x y : Bool) {A B C} → Σ Mach λ m′ → (if x then silent A else if y then silent B else silent C) ≡ silent m′
  if-silent true  _     = _ , refl
  if-silent false true  = _ , refl
  if-silent false false = _ , refl

  postulate
    -- THE STEPPER IS THE MEANING, as sets, of a run's configuration
    -- (`Sane`): what the ghost's step shows, then the residual of the
    -- ghost it leaves.  A joiner told its end while its source runs is
    -- fed the source's values by the stepper and shows them, where the
    -- meaning reads it as its end alone.
    --
    -- So the proof runs modulo skips, and the source's skips are unbounded,
    -- so the relation must survive a merge (`M.beside`, `M.go`) whose
    -- order a skip's position steers.
    --
    -- REFUTED: 3e2af71f stated of every node, by a told joiner under a live source
    -- DEAD ROUTE: exact agreement per approximant (`same-agree`).  The
    --   meaning's joiner shows each of its source's skips, at `q ++ [ sub p ]`
    --   (`M.rejoin`), and a value from before its join as a skip; the
    --   stepper feeds a joiner values only, and only those after it joined.
    -- DEAD ROUTE: exact agreement per approximant with the stepper's joiner
    --   shown every source step as `M.rejoin` shows it.  A lane a flatMap
    --   has yet to subscribe reads its connect's source from where the
    --   ghost's source stands, so the meaning shows it one pre-join skip at
    --   `p ++ [ ix i ]` per source step before its join, and a source step
    --   leaves one fewer.  Witness 950a4208.
    -- RECOVERY: git show 950a4208 restores the joiner shown every source step, and step-alike over step-agrees
    step-alike : ∀ g → Sane [] g → residual g ≋ after (U.step g)

    -- The turn, nothing held and no timer queued: the ghost shows
    -- nothing.
    turn-dry : ∀ {g m w} {σ : w ⊑ Conf.world (Mach.conf m)} → Carried g m → Conf.ctl (Mach.conf m) ≡ held σ bottom
             → Mach.bursts m ≡ [] → Mach.timers m ≡ [] → ∀ {k b} → Has (residual g) k b → ⊥

    -- The turn popping a timer: its frame is the ghost's frames node at
    -- its tick.
    turn-pops : ∀ {g m w} {σ : w ⊑ Conf.world (Mach.conf m)} → Carried g m → Conf.ctl (Mach.conf m) ≡ held σ bottom
              → Mach.bursts m ≡ [] → ∀ {m′} → step m ≡ silent m′ → Ahead g m′

    -- A subscription begun runs its kernel's code silently to the next
    -- re-entry state.
    sub-onward : ∀ {g m w act K} {σ : w ⊑ Conf.world (Mach.conf m)} → Carried g m → Conf.ctl (Mach.conf m) ≡ run {B = ⊤} act σ K
               → ∀ {m′} → step m ≡ silent m′ → Ahead g m′

    -- A burst's frame stepped: polled, played, or found spent.
    burst-onward : ∀ {g m w K b bs} {σ : w ⊑ Conf.world (Mach.conf m)} → Carried g m → Conf.ctl (Mach.conf m) ≡ held σ K
                 → Mach.bursts m ≡ just b ∷ bs → ∀ {m′} → step m ≡ silent m′ → Ahead g m′

    -- A value recorded is the least the ghost still holds.
    note-least : ∀ {g g′ m w a k K} {σ : w ⊑ Conf.world (Mach.conf m)} → Carried g m
               → Conf.ctl (Mach.conf m) ≡ asking {B = ⊤} (note a) k σ K → U.step g ≡ U.outˢ (Conf.pos (Mach.conf m)) a g′
               → ∀ {q b} → Has (residual g′) q b → q ≤ᵖ Conf.pos (Mach.conf m) → ⊥

    -- Past a value recorded, the run runs the stepped ghost.
    note-onward : ∀ {g g′ m w a k K} {σ : w ⊑ Conf.world (Mach.conf m)} → Carried g m
                → Conf.ctl (Mach.conf m) ≡ asking {B = ⊤} (note a) k σ K → U.step g ≡ U.outˢ (Conf.pos (Mach.conf m)) a g′
                → ∀ {t q a′ m′} → step m ≡ value t q a′ m′ → Mirror g′ m′

  -- THE STRONG STEP: from a re-entry configuration the machine runs
  -- silently to the next, or records a least value of the residual, or
  -- ends it.  By the re-entry state.
  residual-steps : ∀ g → Sane [] g → Steps (residual g) (U.step g)
  residual-steps g sn = steps-after (U.step g) (step-alike g sn)

  strong-shows : ∀ {rest g m} → Strong g m → rest ≋ residual g → Shows rest (step m)
  strong-shows {g = g} {m = mach ⟨ hp , p , c ⟩ clk ts bs td lg en mk} (closing refl refl st sn) e =
    completeˢ (proj₂ e (proj₁ rs)) λ h → proj₂ rs (proj₁ e h)
    where rs = subst (Steps (residual g)) st (residual-steps g sn)
  strong-shows {g = g} {m = mach ⟨ hp , p , c ⟩ clk ts bs td lg en mk} (carried cr) e
    with Carried.ctlAs cr | Carried.meets cr | Books.paidUp (Carried.books cr) | Books.clocked (Carried.books cr)
       | Books.running (Carried.books cr)
  ... | subAs π x K | _ | refl | _ | _ = silentˢ (onward {g = g} e (sub-onward {g = g} cr refl refl))
  strong-shows {g = g} {m = mach ⟨ hp , p , c ⟩ clk ts bs td lg en mk} (carried cr) e
    | noteAs ks x K | g′ , _ , st | refl | ck | refl =
    valueˢ ck (proj₂ e (proj₁ rs)) (λ h → proj₂ e (proj₁ (proj₂ rs) h)) (λ h → proj₂ (proj₂ rs) (proj₁ e h))
      (note-least {g = g} cr refl st) (record { ghost = g′ ; same = ≋-refl ; mirror = note-onward {g = g} cr refl st refl })
    where rs = subst (Steps (residual g)) st (residual-steps g (Carried.sane cr))
  strong-shows {g = g} {m = mach ⟨ hp , p , c ⟩ clk ts bs td lg en mk} (carried cr) e
    | calmAs | _ | refl | _ | refl with ts
  ... | []    = drainedˢ λ h → turn-dry {g = g} cr refl refl refl (proj₁ e h)
  ... | _ ∷ _ = silentˢ (onward {g = g} e (turn-pops {g = g} cr refl refl refl))
  strong-shows {g = g} {m = mach ⟨ hp , p , c ⟩ clk ts bs td lg en mk} (carried cr) e
    | burstAs {b = b} x K | _ | refl | _ | _ with if-silent (spent? hp (Playing.handle b)) (Playing.polled b)
  ... | m′ , eq = subst (Shows _) (sym eq) (silentˢ (onward {g = g} e (burst-onward {g = g} cr refl refl eq)))

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
