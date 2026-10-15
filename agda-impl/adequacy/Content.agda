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
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any)
open import Data.List.Relation.Unary.All using ([]; _∷_; lookup)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Tree as T
open import denotation.MonotonicList using (MonotonicList; Events; Events∞; Pos; Time; tick; out; skip; end; observe; root)
open import adequacy.Sorted using (_≤ᵖ_; module Sorting)
open import operation.Machine using (module Machine)
open import denotation.Denote using (⟦_⟧; DenEnv)
open import operation.AbstractObservable using (module Run; module Heap)
open Heap using (_⊑_)
open import operation.PureObservable using (PureObs; Pureᴾ; module Pure)

open Events∞

module Honesty (R : Set) where
  open Run (Pureᴾ R) using (Subscribe; Subject; Env; wkEnv; compile; emptyᴷ; ofᴷ; mapᴷ; scanᴷ; takeWhileᴷ; flatMapᴷ; connectᴷ; joinᴷ; via; startCold)
  open Machine R using (Mach; Step; silent; value; complete; drained; step; trace; reading; begin; launch; Read; read)
  open Sorting R using (WellSub; compile-well)
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

  -- How a configuration's record stands: cut at its clock, or the run
  -- complete or drained there.
  data Stands (m : Mach) : End → Set₁ where
    cutʰ  : Stands m (cutOff (Mach.clock m))
    finʰ  : ∀ {p} → step m ≡ complete p → Stands m finished
    dryʰ  : step m ≡ drained → Stands m dry

  postulate
    -- THE MACHINE'S CONTENT: a configuration reached from an honest
    -- launch keeps a record alike its meaning's events, however it stands.
    kept : ∀ {e m en} → Reached e m → Stands m en → Alike en (Mach.marks m) (Mach.log m) e

    -- The first n steps, read, are the record of the configuration n
    -- steps on.
    read-is-kept : ∀ {e m} (r : Reached e m) n → Σ Mach λ m′ → Σ (Reached e m′) λ _ → Σ End λ en → Stands m′ en
                 × reading n 0 (trace m) ≡ read (Mach.marks m′) (Mach.log m′) en

  -- The configuration's record, read.
  alike-read : ∀ {e m} (r : Reached e m) n → let x = reading n 0 (trace m) in Alike (ending x) (marks x) (log x) e
  alike-read r n with read-is-kept r n
  ... | m′ , r′ , en , st , eq rewrite eq = kept r′ st

  -- CONTENT: every prefix's record alike the meaning's events as a set:
  -- the compiled tree honest to its meaning, kernel by kernel, launched.
  content : (o : PureObs [] R) (n : ℕ) → let x = reading n 0 (trace (begin o)) in Alike (ending x) (marks x) (log x) (observe (⟦ o ⟧ []) root)
  content o n = alike-read (launchedʰ (compile-honest o [] [] honest-[]) refl) n
