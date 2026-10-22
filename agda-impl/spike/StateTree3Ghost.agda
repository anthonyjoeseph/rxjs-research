{-# OPTIONS --guardedness #-}

-- SPIKE 5: THE GHOST AS A FUNCTION.  Today a configuration is related to
-- `denotation.Unfold`'s ghost by a carried witness (`adequacy.Strong`'s
-- `Sub`).  Here the ghost is COMPUTED from a quiet configuration of the
-- state-tree machine: its tree, and the positions its jobs saved.  The
-- residual is the ghost's `meaning`, so the content obligation becomes:
-- from one quiet configuration to the next, the residual is kept, less
-- whatever the root was shown.
--
-- A quiet configuration is one whose mode is `absorbed`: nothing is in
-- flight, so every position a node still needs sits on a job.  An `of`
-- finds its count and subscription on its `next` job; a takeWhile its
-- owed completion on `owedCp`; a connect its source's subscription on
-- `attBody`, and each feed under way on a `feeding` job, zipped with its
-- subject's stack of values.  A joiner keeps where it joined.
--
-- Only values and ends are compared (`adequacy.Ghost`'s `Has` skips
-- skips), so whatever a node leaves running, which `Unfold` runs as
-- skips, is ghosted as `idleᶜ`: a dead switch, an ended lane, a body
-- ended or a take that has shown its end.  The connect's source
-- subscription `r` reaches only its tail, so it is not kept.
module spike.StateTree3Ghost where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; [_]; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; lookup) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (does)

open import Tree using (FlatOp)
open import denotation.MonotonicList.Events using (Pos; ix; last; root; Events; out; skip; end; hush; _≟ᵖ_) renaming (sub to subᴾ)
open import denotation.MonotonicList.Events using (module Events∞)
import denotation.Unfold as U
open import spike.StateTree3 using (PObs; Ev; nx; cp; CS; St; pend; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
  Ctx; plug; dirs; Tag; next; owedCp; owedCut; attBody; owed; feeding; Job; Mode; absorbed; subscribing; Conf; ⟨_,_,_,_,_⟩; Shown;
  step; load; _⊕_)

------------------------------------------------------------------------
-- Reading the jobs

_≟ᴸ_ : List ℕ → List ℕ → Bool
[]       ≟ᴸ []       = true
(a ∷ as) ≟ᴸ (b ∷ bs) = (a ≡ᵇ b) ∧ (as ≟ᴸ bs)
_        ≟ᴸ _        = false

-- The jobs owed at a node, by its path, newest first.
jobsAt : List ℕ → List Job → List (Tag × Pos)
jobsAt π []                 = []
jobsAt π ((q , t , p) ∷ rs) = if π ≟ᴸ q then (t , p) ∷ jobsAt π rs else jobsAt π rs

-- An of's next value and where it was subscribed.
ofAt : List (Tag × Pos) → Maybe (ℕ × Pos)
ofAt []                 = nothing
ofAt ((next i , p) ∷ _) = just (i , p)
ofAt (_ ∷ ts)           = ofAt ts

-- A take still running, owing its end after the value at `k`, or past it.
data Owing : Set where
  free   : Owing
  endsAt : Pos → Owing
  over   : Owing

takeAt : List (Tag × Pos) → Owing
takeAt []                  = free
takeAt ((owedCp , k) ∷ _)  = endsAt k
takeAt ((owedCut , _) ∷ _) = over
takeAt (_ ∷ ts)            = takeAt ts

owedAt : List (Tag × Pos) → Bool
owedAt []              = false
owedAt ((owed , _) ∷ _) = true
owedAt (_ ∷ ts)        = owedAt ts

-- Each feed under way: who is still to be fed, and where the value was.
feedingsAt : List (Tag × Pos) → List (List (List ℕ × Pos) × Pos)
feedingsAt []                     = []
feedingsAt ((feeding js , p) ∷ ts) = (js , p) ∷ feedingsAt ts
feedingsAt (_ ∷ ts)               = feedingsAt ts

-- Where a pending subscription will be made: a connect's source under
-- `ix 1` of its attBody job; the focus, while subscribing.
attached : List Job → List (List ℕ × Pos)
attached []                       = []
attached ((π , attBody , p) ∷ rs) = (π ++ [ 0 ] , p ⊕ [ ix 1 ]) ∷ attached rs
attached (_ ∷ rs)                 = attached rs

pendAt : List ℕ → List (List ℕ × Pos) → Maybe Pos
pendAt π []             = nothing
pendAt π ((q , p) ∷ ps) = if π ≟ᴸ q then just p else pendAt π ps

------------------------------------------------------------------------
-- What a joiner reads of its binder

-- Each feed under way, newest first: the value, where it was, who is
-- still to be fed.
Level : Set → Set
Level X = Ev X × Pos × List (List ℕ × Pos)

record Bind (X : Set) : Set where
  constructor bind
  field
    closed : Bool
    levels : List (Level X)

zipF : ∀ {X} → List (Ev X) → List (List (List ℕ × Pos) × Pos) → List (Level X)
zipF (e ∷ es) ((js , p) ∷ fs) = (e , p , js) ∷ zipF es fs
zipF _        _               = []

member : List ℕ → List (List ℕ × Pos) → Bool
member π []             = false
member π ((q , _) ∷ js) = (π ≟ᴸ q) ∨ member π js

-- The values a joiner at `π`, joined at `j`, is still owed, oldest first.
owedTo : ∀ {X} → List ℕ → Pos → List (Level X) → List (Pos × Maybe X)
owedTo π j []                     = []
owedTo π j ((nx v , p , js) ∷ ls) = owedTo π j ls ++ (if member π js then [ (p ⊕ [ subᴾ j ] , just v) ] else [])
owedTo π j ((cp , p , js) ∷ ls)   = owedTo π j ls

endOwed : ∀ {X} → List ℕ → List (Level X) → Bool
endOwed π []                   = false
endOwed π ((nx _ , _ , _) ∷ ls) = endOwed π ls
endOwed π ((cp , _ , js) ∷ ls)  = member π js ∨ endOwed π ls

-- Where the subject ended, while its end is fed.
endedAt : ∀ {X} → List (Level X) → Pos
endedAt []                    = root
endedAt ((nx _ , _ , _) ∷ ls) = endedAt ls
endedAt ((cp , c , _) ∷ ls)   = c

------------------------------------------------------------------------
-- The ghost

record Book : Set where
  constructor book
  field
    rets  : List Job
    pends : List (List ℕ × Pos)

flatᶜ : ∀ {Γ A B} → FlatOp → (A → PObs Γ B) → Maybe (U.Node Γ A) → List (U.Node Γ B) → U.Node Γ B
flatᶜ op f nothing [] = U.idleᶜ
flatᶜ op f o       ls = U.flatMapᶜ op (λ a q → U.subscribe (f a) q) o ls [] U.idleᶜ

joinᶜ : ∀ {Γ X} → List ℕ → Pos → X ∈ Γ → Bind X → U.Node Γ X
joinᶜ π j x (bind true ls)  = if endOwed π ls then U.joinᶜ x j (owedTo π j ls) nothing else U.idleᶜ
joinᶜ π j x (bind false ls) = U.joinᶜ x j (owedTo π j ls) nothing

mutual
  gh : ∀ {Γ A} → Book → List ℕ → All Bind Γ → St Γ A → U.Node Γ A
  gh b π β (pend o) with pendAt π (Book.pends b)
  ... | just p  = U.subscribe o p
  ... | nothing = U.idleᶜ
  gh b π β (ofS xs) with ofAt (jobsAt π (Book.rets b))
  ... | just (i , p) = U.ofᶜ p i xs
  ... | nothing      = U.idleᶜ
  gh b π β doneS              = U.idleᶜ
  gh b π β (mapS f s)         = U.mapᶜ f (gh b (π ++ [ 0 ]) β s)
  gh b π β (scanS f z s)      = U.scanᶜ f z (gh b (π ++ [ 0 ]) β s)
  gh b π β (cutS true a s)    = gh b (π ++ [ 0 ]) β s
  gh b π β (cutS false a s)   = U.idleᶜ
  gh b π β (lnS l s)          = gh b (π ++ [ 0 ]) β s
  gh b π β (takeS i q s) with takeAt (jobsAt π (Book.rets b))
  ... | free     = U.takeWhileᶜ i q (gh b (π ++ [ 0 ]) β s)
  ... | endsAt k = U.endingᶜ (k ⊕ [ last ]) U.idleᶜ
  ... | over     = U.idleᶜ
  gh b π β (flatS op f d n o ls) = flatᶜ op f (if d then nothing else just (gh b (π ++ [ 0 ]) β o)) (lanes b π 0 β ls)
  gh b π β (connS k o bd) with jobsAt π (Book.rets b)
  ... | ts = if owedAt ts ∨ not (CS.srcLive k) then U.idleᶜ
             else U.connectᶜ root (gh b (π ++ [ 1 ]) (bind (CS.closed k) lv ∷ᴬ β) bd) (source (CS.closed k))
    where
      lv = zipF (CS.feeds k) (feedingsAt ts)
      source : Bool → U.Source _ _
      source true  = U.ended (endedAt lv) U.idleᶜ
      source false = U.live (gh b (π ++ [ 0 ]) β o)
  gh b π β (joinS j true x)   = joinᶜ π j x (lookup β x)
  gh b π β (joinS j false x)  = U.idleᶜ

  -- The lanes still running, each under `suc` of its index.
  lanes : ∀ {Γ B} → Book → List ℕ → ℕ → All Bind Γ → List (St Γ B) → List (U.Node Γ B)
  lanes b π i β []                        = []
  lanes b π i β (lnS l (cutS true a s) ∷ ls) = gh b (π ++ [ suc i ] ++ [ 0 ] ++ [ 0 ]) β s ∷ lanes b π (suc i) β ls
  lanes b π i β (_ ∷ ls)                  = lanes b π (suc i) β ls

focusing : ∀ {R Γ A} → Ctx R Γ A → Mode A → Pos → List (List ℕ × Pos)
focusing c subscribing p = [ (dirs c , p) ]
focusing c _           p = []

-- The ghost of a configuration, read off its tree and its jobs.
ghost : ∀ {R} → Conf R → U.Node [] R
ghost ⟨ c , s , m , p , rs ⟩ = gh (book rs (focusing c m p ++ attached rs)) [] []ᴬ (plug c s)

-- What the ghost will show.
residual : ∀ {R} → Conf R → Events R
residual k = U.meaning (ghost k) []ᴬ

-- Loaded, the ghost is the program subscribed at the root, which
-- `adequacy.Ghost`'s `begun` ties to the denotation.
ghost-load : ∀ {R} (o : PObs [] R) → ghost (load o) ≡ U.subscribe o root
ghost-load o = refl

------------------------------------------------------------------------
-- Checking it by running

-- The values and the end the events hold, in order, within `n` events.
seen : ∀ {R} → ℕ → Events R → Shown R
seen zero    e           = []
seen (suc n) (out k a r) = (k , nx a) ∷ seen n (Events∞.force r)
seen (suc n) (skip k r)  = seen n (Events∞.force r)
seen (suc n) (end k)     = [ (k , cp) ]
seen (suc n) hush        = []

quiet : ∀ {R} → Conf R → Bool
quiet ⟨ c , s , absorbed , p , rs ⟩ = true
quiet _                             = false

-- Each quiet configuration the run passes, with what the root was shown
-- before it.
quiets : ∀ {R} → ℕ → Conf R → Shown R → List (Shown R × Conf R)
quiets zero    k sh = []
quiets (suc n) k sh with step k
... | k′ , out′ = (if quiet k′ then [ (sh ++ out′ , k′) ] else []) ++ quiets n k′ (sh ++ out′)

------------------------------------------------------------------------
-- The obligation the check samples

-- The events hold a value (`just`) or their end (`nothing`) at `k`.
data Has {R : Set} : Events R → Pos → Maybe R → Set where
  atOut    : ∀ {k a r} → Has (out k a r) k (just a)
  atEnd    : ∀ {k} → Has (end k) k nothing
  pastOut  : ∀ {k a r q b} → Has (Events∞.force r) q b → Has (out k a r) q b
  pastSkip : ∀ {k r q b} → Has (Events∞.force r) q b → Has (skip k r) q b

data In {R : Set} : Shown R → Pos → Maybe R → Set where
  inValue : ∀ {k a sh} → In ((k , nx a) ∷ sh) k (just a)
  inEnd   : ∀ {k sh} → In ((k , cp) ∷ sh) k nothing
  inLater : ∀ {x sh k b} → In sh k b → In (x ∷ sh) k b

-- A configuration reached from a program's load, and what the root was
-- shown on the way.
data From {R} (o : PObs [] R) : Conf R → Shown R → Set₁ where
  loaded  : From o (load o) []
  stepped : ∀ {k sh k′ sh′} → From o k sh → step k ≡ (k′ , sh′) → From o k′ (sh ++ sh′)

-- At every quiet configuration, the program's meaning is what the root
-- was shown together with the ghost's, as sets.  Order is spike 4's
-- (`spike.StateTree3Order`'s `ascends`), so a set suffices.
Kept : ∀ {R} → PObs [] R → Conf R → Shown R → Set
Kept o k sh = ∀ {q b} → (Has (residual (load o)) q b → In sh q b ⊎ Has (residual k) q b)
                      × (In sh q b ⊎ Has (residual k) q b → Has (residual (load o)) q b)

postulate
  kept : ∀ {R} {o : PObs [] R} {k sh} → From o k sh → quiet k ≡ true → Kept o k sh
