-- A FRAME WHOSE FUNCTION READS ITS ARGUMENT'S SYNTAX, which is the
-- one axis every earlier chain-door sweep held fixed.  Seven series
-- now cover the door's re-entries -- depth, the share telescope, fan
-- width, both cutting arms, the second arrival, the arrival that
-- comes from an inner, and an inner carrying operators -- and in
-- every one of them each operator is an IDENTITY MAP, so no value a
-- frame passes on carries syntax of its own.  That matters because
-- the size ledger inflates a value a level per frame while what a
-- subscribe registers is the DERIVED value's operators: a function
-- that duplicates its argument makes those two quantities diverge,
-- and nothing had instantiated one.

-- THE DUPLICATOR, and it is the established shape rather than a new
-- one: a map function that merges its own argument with itself
-- returns a value of about twice the argument's syntax, so k stacked
-- copies multiply the size by 2^k while the path they sit on grows
-- by k.  `Refuted.Subscribe-Caps-Nest` moves exactly this quantity to
-- break a nest-depth cap.  Here it is put on a REGISTERED CHAIN and
-- the reading is taken in the length currency the fold's leaf is
-- stated in.

-- WHAT IS UNDER TEST, and it is the doubling itself.  The leaf
-- charges a fold's output registry at `B + B` where `B` covers the
-- arriving value, the walked path and the registry standing before
-- the step.  So the rows below compute the LEAST `B` at which all
-- three premises hold, run the door, and compute the least budget the
-- output registry needs.  A statement of this shape can only die one
-- way -- the second number passing twice the first -- and the sweep
-- is over the count of duplicating frames, which is the only axis
-- that moves the two apart.

-- WHICH ROWS BEAR WEIGHT.  `duplicates` is LOAD-BEARING and is what
-- makes the rest a reading rather than a tautology: the chains
-- standing after the step run 3, 9, 33, 129 across the four heights,
-- so the value the door subscribed really did double per frame.
-- `fits` is LOAD-BEARING and is the sweep -- a `≤ᵇ` between two
-- numbers each found by an independent search, so a height at which
-- the derived value's spine outran the walked path would read false.
-- `budgets` is LOAD-BEARING for a third reason: it pins both columns,
-- so a `fits` that passed because the premises had gone unsatisfiable
-- -- a least-budget search running off its fuel and reporting zero --
-- shows up as a wrong figure instead of as a green.  `reaches` is
-- DEGENERATE and is the guard that stops all of it reading green on a
-- run that never got to the door.

-- AND THE ANSWER IS THAT THE CHARGE DOES NOT SEE THE DUPLICATION AT
-- ALL.  The exit budget equals the entry budget at every height, so
-- the doubling the leaf grants is spent nowhere: what grows with the
-- stack is the NUMBER of registered chains, and `regsSz?` is an `all`
-- over entries, which charges each on its own.  Exponential width
-- against a per-entry price is free, and the per-entry price moves by
-- one frame per frame added.

-- WHAT THESE ROWS DO NOT BUY, AND THE SIBLING SHAPE THAT DOES.  The
-- duplication is in the VALUE and the reading is of the PATH, so what
-- these rows show is that the two do not move together on THIS
-- family.  Every copy a duplicator makes is a SIBLING, and siblings
-- register as separate chains, which is why the growth reads additive
-- here and why no amount of width can break an `all`.  A function
-- that wraps its argument in flatten levels instead composes down ONE
-- spine, and that shape breaks the doubling outright --
-- `Refuted.Fold-Path-Regs-Len`.

-- TARGET: foldPath-regsLen @d58775
module Probed.Chain-Step-Regs-Read where

open import Data.Bool using (Bool; true; if_then_else_; _∧_)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.List using ([]; _∷_; length)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx; Closed; Exp; Fn; natᵗ; obs; ofᵉ; mapᵉ;
  mergeAllᵉ; strmᵗ; varᵗ; input; syncSizeᵉ)
open import Rx.Prim using (gasPad; g0; cold; after_,_)
open import Rx.Slots using (Slots; scripted)
open import Rx.Evaluator using (Sched; EvalSt; subscribeE; sched-init;
  st-init; root; sched-next; cascade; cascadeLatch; chainStep; chainsOf;
  arrVal; sizeStep)
open import Rx.Hop-Depth using (hopDᵉ)
open import Rx.Slot-Hop using (slotHop)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (pathSz?; regsSz?)
open import Verify-Budget-Sufficient.Regs-Nest-Walk using (valsSz?)

Γ₃ : Ctx 3
Γ₃ = natᵗ ∷ⱽ natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

outer : Closed Γ₃ natᵗ
outer = input fzero

-- polymorphic in the local contexts: it is checked under a `mapᵉ`, in
-- the function's own value context
inner : ∀ {Δᵍ Δ Θ} → Exp Γ₃ Δᵍ Δ Θ natᵗ
inner = input (fsuc fzero)

-- THE DUPLICATOR.  Its argument is an observable, and the body merges
-- that argument with itself -- so the returned value mentions the
-- incoming syntax twice, and the type is unchanged, which is what
-- lets the frames stack to any height without the program's type
-- growing with them
dup : Fn Γ₃ [] [] [] (obs natᵗ) (obs natᵗ)
dup = strmᵗ (mergeAllᵉ nothing
       (ofᵉ (varᵗ (here refl) ∷ varᵗ (here refl) ∷ [])))

-- each outer value becomes a stream, so there is observable syntax
-- for the duplicator above to read
lifted : Closed Γ₃ (obs natᵗ)
lifted = mapᵉ (strmᵗ inner) outer

stack : ℕ → Closed Γ₃ (obs natᵗ) → Closed Γ₃ (obs natᵗ)
stack zero    s = s
stack (suc k) s = mapᵉ dup (stack k s)

prog : ℕ → Closed Γ₃ natᵗ
prog k = mergeAllᵉ nothing (stack k lifted)

-- the second-arrival timing: the outer fires three times and the
-- inner is due past all of them, so the arrival the door is run on is
-- the outer's own next value and the source is not spent when it
-- lands
slots : Slots Γ₃
slots fzero               = scripted (cold [] ((after 0 , 7) ∷ (after 2 , 8) ∷ (after 0 , 9) ∷ []))
slots (fsuc fzero)        = scripted (cold [] ((after 9 , 1) ∷ []))
slots (fsuc (fsuc fzero)) = scripted (cold [] ((after 9 , 2) ∷ []))

sucG : Closed Γ₃ natᵗ → ℕ
sucG e = suc (syncSizeᵉ e + hopDᵉ 0 (slotHop 0 slots) e)

sub : (e : Closed Γ₃ natᵗ) → Sched Γ₃ × EvalSt e
sub e = let r = subscribeE (gasPad (sucG e) g0) e root 0 0
                           (sched-init e slots) (st-init e)
        in proj₁ (proj₂ r) , proj₂ (proj₂ r)

-- the least budget at which a Boolean reading holds, searched upward
-- from zero.  Running off the fuel reports zero, which is the value a
-- satisfied search can never return here -- so an exhausted search is
-- visible in the figures rather than silent
least : (ℕ → Bool) → ℕ → ℕ → ℕ
least p zero    b = 0
least p (suc f) b = if p b then b else least p f (suc b)

fuel : ℕ
fuel = 400

-- THE READING.  Both budgets are computed at the SAME reached door:
-- the entry budget covers the three premises together, and the exit
-- budget is the least the output registry satisfies
budgetsOf : (e : Closed Γ₃ natᵗ) → ℕ × ℕ
budgetsOf e with sched-next (proj₁ (sub e))
... | inj₁ _         = 0 , 0
... | inj₂ (a₁ , s₁) with cascade a₁ 1 s₁ (proj₂ (sub e))
...   | (_ , s₂ , st₁) with sched-next s₂
...     | inj₁ _         = 0 , 0
...     | inj₂ (a₂ , s₃) with chainsOf a₂ st₁
...       | []            = 0 , 0
...       | (rid , c) ∷ _ =
            let st₀ = record (cascadeLatch a₂ st₁) { delivered = rid ∷ [] }
                r   = chainStep 2 a₂ c s₃ st₀
                pre = λ b → valsSz? b (arrVal a₂ ∷ [])
                          ∧ (pathSz? b c
                          ∧ regsSz? b (EvalSt.registry st₀))
                post = λ b → regsSz? b (EvalSt.registry (proj₂ (proj₂ r)))
            in least pre fuel 0 , least post fuel 0

entryB exitB : Closed Γ₃ natᵗ → ℕ
entryB e = proj₁ (budgetsOf e)
exitB  e = proj₂ (budgetsOf e)

-- how many chains stand once the step has run.  This is what says the
-- duplicator DUPLICATED: every copy it makes is subscribed on its own,
-- so a count that doubled with the stack height is the growth the
-- budgets above decline to see
countAfter : (e : Closed Γ₃ natᵗ) → ℕ
countAfter e with sched-next (proj₁ (sub e))
... | inj₁ _         = 0
... | inj₂ (a₁ , s₁) with cascade a₁ 1 s₁ (proj₂ (sub e))
...   | (_ , s₂ , st₁) with sched-next s₂
...     | inj₁ _         = 0
...     | inj₂ (a₂ , s₃) with chainsOf a₂ st₁
...       | []            = 0
...       | (rid , c) ∷ _ =
            let st₀ = record (cascadeLatch a₂ st₁) { delivered = rid ∷ [] }
                r   = chainStep 2 a₂ c s₃ st₀
            in length (EvalSt.registry (proj₂ (proj₂ r)))

stage : Closed Γ₃ natᵗ → ℕ
stage e with sched-next (proj₁ (sub e))
... | inj₁ _         = 1
... | inj₂ (a₁ , s₁) with cascade a₁ 1 s₁ (proj₂ (sub e))
...   | (_ , s₂ , st₁) with sched-next s₂
...     | inj₁ _         = 2
...     | inj₂ (a₂ , _) with chainsOf a₂ st₁
...       | []          = 3
...       | _ ∷ _       = 4

p0 p1 p2 p3 : Closed Γ₃ natᵗ
p0 = prog 0
p1 = prog 2
p2 = prog 4
p3 = prog 6

-- the door is reached on every stack height, so nothing below reads
-- green over a run that stopped early
reaches : stage p0 + stage p1 + stage p2 + stage p3 ≡ 16
reaches = refl

-- both numbers, pinned.  Below the fourth height the entry budget is
-- the duplicator's own term size and the path is shorter than it; at
-- the fourth the length conjunct takes over and the figure moves with
-- the stack.  The exit column equals the entry column throughout
budgets : entryB p0 + 100 * exitB p0
        + 10000 * entryB p1 + 1000000 * exitB p1
        ≡ 6060202
budgets = refl

budgets′ : entryB p2 + 100 * exitB p2
         + 10000 * entryB p3 + 1000000 * exitB p3
         ≡ 8080606
budgets′ = refl

-- AND THE DUPLICATION LANDED.  The chains standing after the step
-- double with every frame added, so the value the door subscribed
-- really was twice the size one frame down -- which is what makes the
-- two flat budget columns above a reading about the charge rather
-- than about a program that never grew
duplicates : countAfter p0 + 1000 * countAfter p1
           + 1000000 * countAfter p2 + 1000000000 * countAfter p3
           ≡ 129033009003
duplicates = refl

-- THE SWEEP.  At four stack heights the exit budget sits under one
-- FRAME STEP of the entry budget -- with the whole of it to spare,
-- since the two columns are equal -- so a frame that reads its
-- argument's syntax does not make a registration track the size
-- inflation.  The step is taken at `S = B`, which is the joint search
-- above read as the leaf's two caps at once: the same number prices
-- the walked path and the standing registry, so the premises are the
-- three the search already pinned and the pair is ordered by `refl`.
-- Each column is at least two, so the positivity premise is met on
-- every row rather than assumed.
fits : (exitB p0 ≤ᵇ sizeStep (entryB p0) (entryB p0))
     ∧ (exitB p1 ≤ᵇ sizeStep (entryB p1) (entryB p1))
     ∧ (exitB p2 ≤ᵇ sizeStep (entryB p2) (entryB p2))
     ∧ (exitB p3 ≤ᵇ sizeStep (entryB p3) (entryB p3))
     ≡ true
fits = refl
