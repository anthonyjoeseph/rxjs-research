-- WHERE AN EVENT SITS IN THE WHOLE RUN: the instant it runs in, and a
-- path within it.  A tick says when; it does not say which of two
-- simultaneous events comes first, and rxjs always does.  A path is the
-- route through the run's call tree — an event's effects are its
-- children — read in pre-order, which is execution order.  So a merge is
-- a sorted merge, and nothing coordinates it.
--
-- THE INSTANT IS A DATUM, NOT A DECODING.  Every event lies in exactly
-- one instant: the subscribe frame, or one step of a timer's frame —
-- each async emission its own instant, shared with what it synchronously
-- causes — named by the tick the timer fires at, the position it was
-- created at, and the step.  Two events are simultaneous exactly when
-- their instants are equal, and nothing has to be proven about a
-- position for that reading to be right.  A cascade is not inside its
-- creator: its path starts afresh.
--
-- THE ORDER: instant first, then path.  Instants by tick, then by
-- creator, so same-tick timers fire in creation order, as in rxjs, then
-- by step; the subscribe frame before every cascade.  Paths
-- lexicographically, with three kinds of step: `ix i`, an operator's i-th effect; `sub p`, a
-- subject delivering to the subscriber that joined at `p`, so a
-- subject's subscribers come in the order they joined; `last`, after
-- every other effect — where a burst ends and its completion sits.
--
-- A BURST'S ROOT is where its steps go: `nested p`, below `p` in its
-- instant, or `fired t e`, a timer's frame, each step its own instant.
--
-- THE MINT: `fired` is the one way a cascade is made, by the
-- denotation and by both runtimes.  Only the clock differs between
-- them: the denotation and the pure runtime know a cascade's tick from
-- the cold's timeline; the IO runtime learns the order of arrivals, so
-- its clock is a counter.  That one argument is the whole of what IO
-- cannot know.
module denotation.Position where

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Nat using (ℕ; _<ᵇ_)
import Data.Nat as ℕ
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (yes; no)

Time : Set
Time = ℕ

------------------------------------------------------------------------
-- The type

data Label   : Set
data Instant : Set
data Pos     : Set

data Label where
  ix   : ℕ → Label
  sub  : Pos → Label
  last : Label

data Instant where
  frame   : Instant                         -- the subscribe frame, tick 0
  cascade : Time → Pos → Label → Instant    -- a step of a timer created at the position, firing at the tick

data Pos where
  _∙_ : Instant → List Label → Pos

infixr 4 _∙_

Path : Set
Path = List Label

instant : Pos → Instant
instant (i ∙ _) = i

path : Pos → Path
path (_ ∙ p) = p

-- The root subscription: the subscribe frame, before any step.
root : Pos
root = frame ∙ []

-- When an instant runs.
tick : Pos → Time
tick (frame ∙ _)         = 0
tick (cascade t _ _ ∙ _) = t

-- A step below a position stays in its instant.
infixl 5 _⊕_
_⊕_ : Pos → Path → Pos
(i ∙ p) ⊕ q = i ∙ (p ++ q)

-- Where a burst's steps go.
data Root : Set where
  nested : Pos → Root            -- below a position, in its instant
  fired  : Time → Pos → Root     -- THE MINT: a timer created at the position, firing at the tick

-- A burst's step.
infixl 5 _▸_
_▸_ : Root → Label → Pos
nested p  ▸ l = p ⊕ (l ∷ [])
fired t e ▸ l = cascade t e l ∙ []

-- When a burst runs.
tickᴿ : Root → Time
tickᴿ (nested p)  = tick p
tickᴿ (fired t _) = t

------------------------------------------------------------------------
-- Equality: all a name is read for

mutual
  _≟ˡ_ : DecidableEquality Label
  ix m  ≟ˡ ix n  with m ℕ.≟ n
  ... | yes refl = yes refl
  ... | no ne    = no λ { refl → ne refl }
  sub p ≟ˡ sub q with p ≟ᵖ q
  ... | yes refl = yes refl
  ... | no ne    = no λ { refl → ne refl }
  last  ≟ˡ last  = yes refl
  ix _  ≟ˡ sub _ = no λ ()
  ix _  ≟ˡ last  = no λ ()
  sub _ ≟ˡ ix _  = no λ ()
  sub _ ≟ˡ last  = no λ ()
  last  ≟ˡ ix _  = no λ ()
  last  ≟ˡ sub _ = no λ ()

  _≟ⁱ_ : DecidableEquality Instant
  frame         ≟ⁱ frame         = yes refl
  frame         ≟ⁱ cascade _ _ _ = no λ ()
  cascade _ _ _ ≟ⁱ frame         = no λ ()
  cascade t e a ≟ⁱ cascade u d b with t ℕ.≟ u | e ≟ᵖ d | a ≟ˡ b
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ne    | _        | _        = no λ { refl → ne refl }
  ... | yes _    | no ne    | _        = no λ { refl → ne refl }
  ... | yes _    | yes _    | no ne    = no λ { refl → ne refl }

  _≟ᵗ_ : DecidableEquality Path
  []      ≟ᵗ []      = yes refl
  []      ≟ᵗ (_ ∷ _) = no λ ()
  (_ ∷ _) ≟ᵗ []      = no λ ()
  (a ∷ p) ≟ᵗ (b ∷ q) with a ≟ˡ b | p ≟ᵗ q
  ... | yes refl | yes refl = yes refl
  ... | no ne    | _        = no λ { refl → ne refl }
  ... | yes _    | no ne    = no λ { refl → ne refl }

  _≟ᵖ_ : DecidableEquality Pos
  (i ∙ p) ≟ᵖ (j ∙ q) with i ≟ⁱ j | p ≟ᵗ q
  ... | yes refl | yes refl = yes refl
  ... | no ne    | _        = no λ { refl → ne refl }
  ... | yes _    | no ne    = no λ { refl → ne refl }

------------------------------------------------------------------------
-- The order

data Cmp : Set where
  lt eq gt : Cmp

cmpℕ : ℕ → ℕ → Cmp
cmpℕ m n = if m <ᵇ n then lt else if n <ᵇ m then gt else eq

lexi : Cmp → Cmp → Cmp
lexi eq r = r
lexi lt _ = lt
lexi gt _ = gt

mutual
  cmpLabel : Label → Label → Cmp
  cmpLabel (ix m)  (ix n)  = cmpℕ m n
  cmpLabel (ix _)  (sub _) = lt
  cmpLabel (ix _)  last    = lt
  cmpLabel (sub _) (ix _)  = gt
  cmpLabel (sub p) (sub q) = cmpPos p q
  cmpLabel (sub _) last    = lt
  cmpLabel last    (ix _)  = gt
  cmpLabel last    (sub _) = gt
  cmpLabel last    last    = eq

  cmpInstant : Instant → Instant → Cmp
  cmpInstant frame           frame           = eq
  cmpInstant frame           (cascade _ _ _) = lt
  cmpInstant (cascade _ _ _) frame           = gt
  cmpInstant (cascade t e a) (cascade u d b) = lexi (cmpℕ t u) (lexi (cmpPos e d) (cmpLabel a b))

  cmpPath : Path → Path → Cmp
  cmpPath []      []      = eq
  cmpPath []      (_ ∷ _) = lt
  cmpPath (_ ∷ _) []      = gt
  cmpPath (a ∷ p) (b ∷ q) = lexi (cmpLabel a b) (cmpPath p q)

  cmpPos : Pos → Pos → Cmp
  cmpPos (i ∙ p) (j ∙ q) = lexi (cmpInstant i j) (cmpPath p q)

isLt : Cmp → Bool
isLt lt = true
isLt eq = false
isLt gt = false

isEq : Cmp → Bool
isEq eq = true
isEq lt = false
isEq gt = false

_<ˡ_ : Label → Label → Bool
a <ˡ b = isLt (cmpLabel a b)

_<ⁱ_ : Instant → Instant → Bool
i <ⁱ j = isLt (cmpInstant i j)

_<ᵖ_ : Pos → Pos → Bool
p <ᵖ q = isLt (cmpPos p q)

-- `k` lies under `r`: an effect, however deep, of what sits at `r`.  In
-- `r`'s instant, and below it on the path.
insideᵗ : Path → Path → Bool
insideᵗ []      k       = true
insideᵗ (_ ∷ _) []      = false
insideᵗ (a ∷ r) (b ∷ k) = isEq (cmpLabel a b) ∧ insideᵗ r k

inside : Pos → Pos → Bool
inside (i ∙ r) (j ∙ k) = isEq (cmpInstant i j) ∧ insideᵗ r k
