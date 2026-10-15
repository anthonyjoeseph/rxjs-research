{-# OPTIONS --guardedness #-}

-- CONTENT: every observer is delivered its subtree's meaning, as a set.
-- Sortedness (`adequacy.Sorted`) says nothing of WHAT arrives; this says
-- nothing of the ORDER, so neither proof reads the other.
--
-- The PER-KERNEL CONTRACT: a kernel handed an input honest to a meaning
-- is honest to its operator's meaning over it.  Each contract reads one
-- kernel and one operator's `MonotonicList` function; the tree's honesty
-- is their composition (`compile-honest`), a body.
--
-- HISTORIES, NOT STEPS: honesty compares what an observer has been
-- delivered, as a whole, with the meaning observed where it subscribed.
-- No step of the machine is matched to a step of anything.
module adequacy.Content where

open import Level using (lift)
open import Data.List using (List; []; _∷_; _++_; [_]; length)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.Any.Properties using (++⁺ʳ; ++⁻)
import Data.List.Relation.Unary.Any as Any
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Nat.Properties using (suc-injective)
open import Data.List.Relation.Unary.All using ([]; _∷_; lookup)
open import Data.Bool using (true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst; subst₂)

import Tree as T
open import denotation.MonotonicList using (MonotonicList; Events; Events∞; Pos; Time; tick; out; skip; end; hush; observe; root)
open import adequacy.Sorted using (_≤ᵖ_; module Sorting)
open import operation.Machine using (module Machine)
open import adequacy.Record using (module Recording)
open import denotation.Denote using (⟦_⟧; DenEnv)
open import operation.AbstractObservable using (module Run; module Heap)
open Heap using (_⊑_)
open import operation.PureObservable using (PureObs; Pureᴾ; module Pure)

open Events∞

module Honesty (R : Set) where
  open Run (Pureᴾ R) using (Subscribe; Subject; Env; wkEnv; compile; emptyᴷ; ofᴷ; mapᴷ; scanᴷ; takeWhileᴷ; flatMapᴷ; connectᴷ; joinᴷ; via; startCold)
  open Machine R using (Mach; Step; silent; value; complete; drained; step; trace; reading; begin; launch; Read; read)
  open Sorting R using (WellSub; compile-well; idle)
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


  postulate
    -- A subscription honest to a meaning: whatever observer it is handed,
    -- subscribed at whatever position `p`, the machine's deliveries to it
    -- are alike `observe m p` as a set, owed up to the position the run
    -- has shown unless its subscriber left.  A postulated TYPE.
    --
    -- A kernel that reads its input's ORDER (`scan`, `takeWhile`, a
    -- flattening, `connect`) is owed its input's sortedness as well, as a
    -- `WellSub`: alike as a set and delivered in ascending position is
    -- the meaning's events in order.
    --
    -- What a callback may deliver depends on the cells its kernel keeps,
    -- and what it is owed on the run's position.  So honesty speaks of a
    -- configuration, its position and its heap's cells, the subscription
    -- open within it.
    --
    -- DEAD ROUTE: honesty as a set alone, for an order-reading kernel.  An
    --   input delivering at `p ++ [ ix 1 ]` before `p ++ [ ix 0 ]` is alike
    --   as a set a meaning with those events ascending, and `scan` over it
    --   shows partial sums the meaning has not, so `scanᴷ-honest` from a
    --   set-honest input alone is false.
    -- DEAD ROUTE: a unary relation over `Act` blind to the heap, each
    --   delivery checked against the meaning alone.  `scanᴷ`'s `next` reads
    --   its accumulator from a cell and delivers `f b a`; a relation whose
    --   `readRef` case quantifies over every content must accept every `b`.
    -- DEAD ROUTE: a sound half (each delivery an event) proven apart from a
    --   whole half (each owed event delivered).  `scanᴷ`'s delivery at `q`
    --   is an event only if its input delivered every event below `q`
    --   first: the output's soundness is the input's wholeness.
    -- DEAD ROUTE: an observer owed only what lies below its own marks.  A
    --   merge's output owes an inner's event below the output's last mark
    --   though that inner has delivered nothing near it, so
    --   `flatMapᴷ-honest` from inners each cut at their own marks is false.
    Honest : ∀ {A w} → Subscribe A w → MonotonicList A → Set₁

    -- An environment honest to a denotational one: each `connect` in
    -- scope's joiners fed the hot run its source's meaning names.
    HonestEnv : ∀ {Γ w} → Env Γ w → DenEnv Γ → Set₁

  postulate
    -- THE PER-KERNEL CONTRACT, one kernel at a time.
    coldᴷ-honest      : ∀ {Γ A w} c (δ : DenEnv Γ) → Honest {A} {w} (via (startCold c)) (⟦ T.cold c ⟧ δ)
    emptyᴷ-honest     : ∀ {Γ A w} (δ : DenEnv Γ) → Honest {A} {w} emptyᴷ (⟦ T.empty ⟧ δ)
    ofᴷ-honest        : ∀ {Γ A w} xs (δ : DenEnv Γ) → Honest {A} {w} (ofᴷ xs) (⟦ T.of xs ⟧ δ)
    mapᴷ-honest       : ∀ {Γ A B w} f {s : Subscribe A w} (o : PureObs Γ A) δ → Honest {A} {w} s (⟦ o ⟧ δ) → Honest {B} (mapᴷ f s) (⟦ T.map f o ⟧ δ)
    scanᴷ-honest      : ∀ {Γ A B w} f z {s : Subscribe A w} (o : PureObs Γ A) δ → WellSub s → Honest {A} {w} s (⟦ o ⟧ δ) → Honest {B} (scanᴷ f z s) (⟦ T.scan f z o ⟧ δ)
    -- The contract's risk: `takeWhile` completes at the value that fails,
    -- and rxjs delivers that completion before the source's next value.
    takeWhileᴷ-honest : ∀ {Γ A w} i p {s : Subscribe A w} (o : PureObs Γ A) δ → WellSub s → Honest {A} {w} s (⟦ o ⟧ δ) → Honest (takeWhileᴷ i p s) (⟦ T.takeWhile i p o ⟧ δ)
    flatMapᴷ-honest   : ∀ {Γ A B w} op {f : A → Subscribe B w} {s : Subscribe A w} (g : A → PureObs Γ B) (o : PureObs Γ A) δ
                      → (∀ a → WellSub (f a)) → WellSub s
                      → (∀ a → Honest {B} {w} (f a) (⟦ g a ⟧ δ)) → Honest {A} {w} s (⟦ o ⟧ δ)
                      → Honest (flatMapᴷ op f s) (⟦ T.flatMap op g o ⟧ δ)
    -- `connect`: its joiners fed one hot run, the source's, from where
    -- the body subscribed it.
    connectᴷ-honest   : ∀ {Γ A B w} {s : Subscribe A w} {b : ∀ {v} → w ⊑ v → Subject A v → Subscribe B v} (o : PureObs Γ A) (c : PureObs (A ∷ Γ) B)
                        (e : Env Γ w) δ
                      → WellSub s → (∀ {v} (σ : w ⊑ v) st → WellSub (b σ st))
                      → Honest {A} {w} s (⟦ o ⟧ δ)
                      → (∀ {v} (σ : w ⊑ v) st r → HonestEnv (st ∷ wkEnv σ e) (r ∷ δ) → Honest {B} {v} (b σ st) (⟦ c ⟧ (r ∷ δ)))
                      → Honest (connectᴷ s b) (⟦ T.connect o c ⟧ δ)
    joinᴷ-honest      : ∀ {Γ A w} i (e : Env Γ w) δ → HonestEnv e δ → Honest {A} {w} (joinᴷ (lookup e i)) (⟦ T.connected i ⟧ δ)
    deferᴷ-honest     : ∀ {Γ A w} l (e : Env Γ w) δ → HonestEnv e δ → Honest {A} (compile (T.defer l) e) (⟦ T.defer l ⟧ δ)

  -- THE ASSEMBLY: every compiled tree honest to its meaning, kernel by
  -- kernel.
  compile-honest : ∀ {Γ A w} (o : PureObs Γ A) (e : Env Γ w) δ → HonestEnv e δ → Honest (compile o e) (⟦ o ⟧ δ)
  compile-honest (T.cold c)          e δ he = coldᴷ-honest c δ
  compile-honest T.empty             e δ he = emptyᴷ-honest δ
  compile-honest (T.of xs)           e δ he = ofᴷ-honest xs δ
  compile-honest (T.map f s)         e δ he = mapᴷ-honest f s δ (compile-honest s e δ he)
  compile-honest (T.scan f z s)      e δ he = scanᴷ-honest f z s δ (compile-well s e (lift tt)) (compile-honest s e δ he)
  compile-honest (T.takeWhile i p s) e δ he = takeWhileᴷ-honest i p s δ (compile-well s e (lift tt)) (compile-honest s e δ he)
  compile-honest (T.flatMap op f s)  e δ he = flatMapᴷ-honest op f s δ (λ a → compile-well (f a) e (lift tt)) (compile-well s e (lift tt))
                                                 (λ a → compile-honest (f a) e δ he) (compile-honest s e δ he)
  compile-honest (T.connect s b)     e δ he = connectᴷ-honest s b e δ (compile-well s e (lift tt)) (λ σ st → compile-well b (st ∷ wkEnv σ e) (lift tt)) (compile-honest s e δ he) λ σ st r he′ → compile-honest b (st ∷ wkEnv σ e) (r ∷ δ) he′
  compile-honest (T.connected i)     e δ he = joinᴷ-honest i e δ he
  compile-honest (T.defer l)         e δ he = deferᴷ-honest l e δ he

  postulate
    -- The empty environments are honest to each other.
    honest-[] : ∀ {w} → HonestEnv {[]} {w} [] []

  ----------------------------------------------------------------------
  -- THE ASSEMBLY: from an honest launch to an alike record

  -- A configuration reached from an honest launch, by the machine's own
  -- steps.
  data Reached (e : Events R) : Mach → Set₁ where
    launchedʰ : ∀ {s : Subscribe R []} {M} → Honest {R} s M → e ≡ observe M root → Reached e (launch s recorder)
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
    -- THE CONFIGURATION WILL DELIVER `rest`: ONE relation over the whole
    -- configuration, as `WellMach` is, never one per observer.  A
    -- postulated TYPE: each live observer owed its meaning's events past
    -- the last delivery, every kernel's cells holding what it has
    -- consumed, every frame on the stack what it has yet to deliver.
    --
    -- DEAD ROUTE: the owed bound at the run's position.  A scope returning
    --   puts the position back above what it just delivered, so a cut
    --   record owes the events up to its last mark, which lie past it.
    -- DEAD ROUTE: a spec per observer, its triples quantifying over the
    --   frame around it.  A cut flows ownership upstream: `takeWhile`'s
    --   completion cancels its source from inside the source's own
    --   callback, so the source's cells are written within its call and
    --   cannot be framed out of it.  And a frame naming other observers'
    --   specs sits a universe above them, so no heap can store it.
    -- DEAD ROUTE: honesty under every context the subscription runs in.
    --   A `Ref` is a membership proof into the world, forgeable by any
    --   computation at a larger world, so some context writes `scan`'s
    --   accumulator; only the compiled program's own context is honest.
    Inner : Events R → Mach → Set₁

  -- The record holds a value at `k`; it never holds an end.
  Logged : List Pos → List (Time × R) → Pos → Maybe R → Set
  Logged qs xs k (just a) = Sent qs xs k a
  Logged qs xs k nothing  = ⊥

  -- What leads the events: skips, then a value or the end at `p`, `r`
  -- what follows it.
  data Lead : Events R → Pos → Maybe R → Events R → Set where
    leadOut  : ∀ {p a r} → Lead (out p a r) p (just a) (force r)
    leadEnd  : ∀ {p} → Lead (end p) p nothing hush
    leadSkip : ∀ {q r p b r′} → Lead (force r) p b r′ → Lead (skip q r) p b r′

  lead-has : ∀ {e p b r} → Lead e p b r → Has e p b
  lead-has leadOut      = atOut
  lead-has leadEnd      = atEnd
  lead-has (leadSkip l) = pastSkip (lead-has l)

  lead-rest : ∀ {e p b r k c} → Lead e p b r → Has r k c → Has e k c
  lead-rest leadOut      x = pastOut x
  lead-rest leadEnd      ()
  lead-rest (leadSkip l) x = pastSkip (lead-rest l x)

  lead-split : ∀ {e p b r k c} → Lead e p b r → Has e k c → (k ≡ p × c ≡ b) ⊎ Has r k c
  lead-split leadOut      atOut        = inj₁ (refl , refl)
  lead-split leadOut      (pastOut x)  = inj₂ x
  lead-split leadEnd      atEnd        = inj₁ (refl , refl)
  lead-split (leadSkip l) (pastSkip x) = lead-split l x

  -- Events led by their end hold no value.
  lead-ended : ∀ {e p r k a} → Lead e p nothing r → Has e k (just a) → ⊥
  lead-ended leadEnd      ()
  lead-ended (leadSkip l) (pastSkip x) = lead-ended l x

  -- What a step shows of the residual: a silent step keeps it; a value
  -- at its tick leads it, what follows lying past the value; a
  -- completion is its end; a drained run leaves nothing of it.
  data Shows (rest : Events R) : Step → Set₁ where
    silentˢ   : ∀ {m′} → Inner rest m′ → Shows rest (silent m′)
    valueˢ    : ∀ {t p a m′ r} → t ≡ tick p → Lead rest p (just a) r → (∀ {k b} → Has r k b → k ≤ᵖ p → ⊥) → Inner r m′
              → Shows rest (value t p a m′)
    completeˢ : ∀ {p r} → Lead rest p nothing r → Shows rest (complete p)
    drainedˢ  : (∀ {k b} → Has rest k b → ⊥) → Shows rest drained

  postulate
    -- An honest subscription launched under the recorder will deliver
    -- the events its meaning shows at the root.
    inner-launch : ∀ {s : Subscribe R []} {M} → Honest {R} s M → Inner (observe M root) (launch s recorder)

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
  ... | completeˢ l = HonMach.within h (lead-has l) , lead-ended l

  -- A drained run has delivered all of it.
  dries : ∀ {e m} (h : HonMach e m) → step m ≡ drained → ∀ {k b} → Has (HonMach.rest h) k b → ⊥
  dries h eq with subst (Shows (HonMach.rest h)) eq (inner-next (HonMach.inner h))
  ... | drainedˢ none = none

  -- An honest subscription launched under the recorder is honest to
  -- the events its meaning shows at the root, all of them still owed.
  honest-launch : ∀ {s : Subscribe R []} {M} → Honest {R} s M → HonMach (observe M root) (launch s recorder)
  honest-launch {M = M} h = record
    { rest = observe M root ; logged = λ () ; split = inj₂ ; past = λ _ () ; paired = refl ; within = λ x → x ; inner = inner-launch h }

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
  ... | valueˢ {r = r} tp l beyond i | kl , km = record
    { rest   = r
    ; logged = λ s → logged′ (subst₂ (λ qs xs → Sent qs xs _ _) km kl s)
    ; split  = λ x → [ (λ l′ → inj₁ (subst₂ (λ qs xs → Logged qs xs _ _) (sym km) (sym kl) l′)) , inj₂ ]′ (split′ x)
    ; past   = λ x ow → past′ x (subst (Any (_ ≤ᵖ_)) km ow)
    ; paired = subst₂ (λ qs xs → length qs ≡ length xs) (sym km) (sym kl) (snoc-length {qs = Mach.marks m} {Mach.log m} paired)
    ; within = λ x → within (lead-rest l x)
    ; inner  = i
    }
    where
    open HonMach h
    logged′ : ∀ {k a′} → Sent (Mach.marks m ++ [ p ]) (Mach.log m ++ [ (t , a) ]) k a′ → Has e k (just a′)
    logged′ s with sent-snoc {Mach.marks m} {Mach.log m} paired s
    ... | inj₁ s′       = logged s′
    ... | inj₂ (kp , x) = subst₂ (λ k a′ → Has e k (just a′)) (sym kp) (cong proj₂ x) (within (lead-has l))
    split′ : ∀ {k b} → Has e k b → Logged (Mach.marks m ++ [ p ]) (Mach.log m ++ [ (t , a) ]) k b ⊎ Has r k b
    split′ x with split x
    ... | inj₁ lg = inj₁ (logged-snoc lg)
    ... | inj₂ y with lead-split l y
    ...   | inj₂ y′       = inj₂ y′
    ...   | inj₁ (kp , ba) = inj₁ (subst₂ (λ k b → Logged (Mach.marks m ++ [ p ]) (Mach.log m ++ [ (t , a) ]) k b) (sym kp) (sym ba)
                                    (subst (λ t′ → Sent (Mach.marks m ++ [ p ]) (Mach.log m ++ [ (t′ , a) ]) p a) (sym tp) (sent-last {Mach.marks m} {Mach.log m} paired)))
    past′ : ∀ {k b} → Has r k b → Any (k ≤ᵖ_) (Mach.marks m ++ [ p ]) → ⊥
    past′ x ow with ++⁻ (Mach.marks m) ow
    ... | inj₁ o          = past (lead-rest l x) o
    ... | inj₂ (here kp)  = beyond x kp
    ... | inj₂ (there ())

  -- Every configuration reached from an honest launch is honest.
  honest : ∀ {e m} → Reached e m → HonMach e m
  honest (launchedʰ h refl) = honest-launch h
  honest (silentʰ r eq)     = honest-step (honest r) (silentᵗ eq)
  honest (valueʰ r eq)      = honest-step (honest r) (valueᵗ eq)

  -- THE MACHINE'S CONTENT: a configuration reached from an honest
  -- launch keeps a record alike its meaning's events, however it stands.
  kept : ∀ {e m en qs} → Reached e m → Stands m en qs → Alike en qs (Mach.log m) e
  kept r = honest-alike (honest r)

  postulate
    -- The launch's first n steps, read, are the record of the
    -- configuration n steps on.
    --
    -- REFUTED: 48b1b730 with the read from any reached configuration, its record the machine's marks alone
    read-is-kept : ∀ {s : Subscribe R []} {M} (h : Honest {R} s M) n → Σ Mach λ m′ → Σ (Reached (observe M root) m′) λ _ → Σ End λ en
                 → Σ (List Pos) λ qs → Stands m′ en qs × reading n 0 (trace (launch s recorder)) ≡ read qs (Mach.log m′) en

  -- The launch's record, read.
  alike-read : ∀ {s : Subscribe R []} {M} (h : Honest {R} s M) n → let x = reading n 0 (trace (launch s recorder)) in Alike (ending x) (marks x) (log x) (observe M root)
  alike-read h n with read-is-kept h n
  ... | m′ , r′ , en , qs , st , eq rewrite eq = kept r′ st

  -- CONTENT: every prefix's record alike the meaning's events as a set:
  -- the compiled tree honest to its meaning, kernel by kernel, launched.
  content : (o : PureObs [] R) (n : ℕ) → let x = reading n 0 (trace (begin o)) in Alike (ending x) (marks x) (log x) (observe (⟦ o ⟧ []) root)
  content o n = alike-read (compile-honest o [] [] honest-[]) n
