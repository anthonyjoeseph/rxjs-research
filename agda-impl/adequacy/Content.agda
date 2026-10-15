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
-- of the machine is matched to a step of a stepper.
module adequacy.Content where

open import Data.List using (List; []; _∷_; _++_; [_]; length)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.Any.Properties using (++⁺ʳ; ++⁻)
import Data.List.Relation.Unary.Any as Any
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Nat.Properties using (suc-injective)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Bool using (true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst; subst₂)

open import denotation.MonotonicList using (Events; Events∞; Pos; Time; tick; out; skip; end; observe; root; Agree; out⁼; skip⁼; end⁼;
  agree; agree-sym; agree-trans; lub; lub-limit; Settling; agrees) renaming (cold to coldᴹ)
import denotation.Unfold as U
open import denotation.Compositional using (from; settle; []ᵉ)
open import adequacy.Sorted using (_≤ᵖ_; module Sorting)
open import operation.Machine using (module Machine)
open import adequacy.Record using (module Recording)
open import denotation.Denote using (⟦_⟧)
open import operation.PureObservable using (PureObs; module Pure)

open Events∞

module Honesty (R : Set) where
  open Machine R using (Mach; Step; silent; value; complete; drained; step; trace; reading; begin; launch; Read; read)
  open Sorting R using (idle)
  open Recording R using (silent-keeps; value-notes)
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

  postulate
    -- THE CONFIGURATION RUNS THE GHOST: ONE relation over the whole
    -- configuration, as `WellMach` is, never one per observer.  A
    -- postulated TYPE: each kernel the run still reaches a node of the
    -- ghost, its cells what the node keeps, each frame on the stack a
    -- value on its way up the ghost's tree.
    --
    -- The ghost's `Node` has no node for a value in flight: a scope's
    -- frame between an input's delivery and its output's is owed one.
    --
    -- DEAD ROUTE: a contract per kernel over the histories its observer is
    --   delivered, composed by `compile`.  The contract must hold under
    --   every context the subscription runs in, and a `Ref` is a
    --   membership proof into the world, forgeable by any computation at a
    --   larger world, so some context writes `scan`'s accumulator; only
    --   the compiled program's own configuration is honest.
    -- DEAD ROUTE: a relation over `Act` blind to the heap.  `scanᴷ`'s
    --   `next` reads its accumulator from a cell and delivers `f b a`; a
    --   relation whose `readRef` case quantifies over every content must
    --   accept every `b`.
    -- DEAD ROUTE: the owed bound at the run's position.  A scope returning
    --   puts the position back above what it just delivered, so a cut
    --   record owes the events up to its last mark, which lie past it.
    -- DEAD ROUTE: a spec per observer, its triples quantifying over the
    --   frame around it.  A cut flows ownership upstream: `takeWhile`'s
    --   completion cancels its source from inside the source's own
    --   callback, so the source's cells are written within its call and
    --   cannot be framed out of it.  And a frame naming other observers'
    --   specs sits a universe above them, so no heap can store it.
    Mirror : U.Node [] R → Mach → Set₁

    -- The launch runs the program subscribed at the root.
    mirror-begin : (o : PureObs [] R) → Mirror (U.subscribe o root) (begin o)

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
  inner-launch o = record { ghost = U.subscribe o root ; same = same-agree (begun o) ; mirror = mirror-begin o }

  postulate
    -- THE TREE WALK: a step that is not the loop's turn shows the
    -- residual.
    inner-walk : ∀ {rest m} → Inner rest m → idle m ≡ false → Shows rest (step m)

    -- THE LOOP'S TURN: popping a timer shows the residual.
    inner-turn : ∀ {rest m} → Inner rest m → idle m ≡ true → Shows rest (step m)

  -- Every step shows the residual.
  inner-next : ∀ {rest m} → Inner rest m → Shows rest (step m)
  inner-next {m = m} i with idle m in eq
  ... | true  = inner-turn i eq
  ... | false = inner-walk i eq

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
  ... | valueˢ {r = r} tp x₀ sub sp beyond i | kl , km = record
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

  postulate
    -- The launch's first n steps, read, are the record of the
    -- configuration n steps on.
    --
    -- REFUTED: 48b1b730 with the read from any reached configuration, its record the machine's marks alone
    read-is-kept : (o : PureObs [] R) (n : ℕ) → Σ Mach λ m′ → Σ (Reached (observe (⟦ o ⟧ []) root) m′) λ _ → Σ End λ en
                 → Σ (List Pos) λ qs → Stands m′ en qs × reading n 0 (trace (begin o)) ≡ read qs (Mach.log m′) en

  -- CONTENT: every prefix's record alike the meaning's events as a set.
  content : (o : PureObs [] R) (n : ℕ) → let x = reading n 0 (trace (begin o)) in Alike (ending x) (marks x) (log x) (observe (⟦ o ⟧ []) root)
  content o n with read-is-kept o n
  ... | m′ , r′ , en , qs , st , eq rewrite eq = kept r′ st
