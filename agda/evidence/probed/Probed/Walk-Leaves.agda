-- THE WALK'S LEAVES THAT COMPUTE ON A CONCRETE FORMER: an `of`'s emits
-- against its plain values, at concrete lists under a binder, and a
-- flattener's, a scan's and a test's nodes installed on both sides, at
-- the opening stores; the scan's and the test's elaborated steps against
-- the author's under a binder; the opening stores' numbering.
-- TARGET: of-carries @3bec3d
-- TARGET: lifts-scan @caa990
-- TARGET: lifts-while @305435
-- TARGET: scan-install @df7775
-- TARGET: while-install @5f8b17
-- TARGET: init-numbers @517377
-- TARGET: init-distinct @da0497
-- TARGET: flat-install @41fd76
-- TARGET: flat-install-explode @bbb192
module Probed.Walk-Leaves where

open import Data.List using ([]; _∷_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Bool using (false)
open import Data.List.Relation.Unary.Any using (there)
open import Data.Maybe using (nothing)
open import Data.Fin using (zero; suc)
open import Data.Nat using (suc; _<?_)
open import Data.Nat.Properties using (<-trans; n<1+n; m<n⇒m<1+n)
open import Relation.Nullary.Decidable using (toWitness)
open import Data.List.Relation.Unary.All using ([]; _∷_; all?)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.List.Relation.Binary.Pointwise using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (refl)
open import Rx.Exp using (add; ltᵖ; natᵗ; uniqᵗ; ofᵉ; []ᵉ; _∷ᵉ_; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ)
open import SExp.Syntax using (varˢᵗ; natˢ; primˢ; pairˢ; inputˢ)
open import Rx.Evaluator using (root; Sched; sched-init)
open import Rx.Mint using (setAt; sourceᵏ)
open import SExp.Impl-Slots using (elaborateImpl; embedSlotsImpl)
open import Rx.Evaluator.Reducible.Support using (rule)

open import Simulation.Walk using (of-carries; flat-install; flat-install-explode; init-store; minted; lifts-scan; lifts-while; scan-install; while-install; init-numbers; init-distinct)
open import Simulation.Arm using (module Arms)
open import Simulation.After using (module Kept)
open import Simulation.Schedules using ([]; _∷_)
open import Simulation.Stores using (Arr; data~; slot~; root~; []; _∷_)
open import CLI.Unit-Test.Prelude using (Γ₂)
open import Probed.Apparatus using (Confirms; Point; κᵖ; insᵖ; two-arrivals)

open Kept using (module After; after)

open Arms {Γ = Γ₂} (κᵖ two-arrivals) using (Carries)

-- LOAD-BEARING: two values, the first read off the binder, under a
-- mint; fails if the impl's list splits them other than one per emit,
-- puts a value on the closing emit's own, reorders them, or reads the
-- binder through the mint at the wrong index
_ : Confirms (of-carries {Γ = Γ₂} (κᵖ two-arrivals) {natᵗ} {ofᵉ []} {ofᵉ []}
                         (varˢᵗ (here refl) ∷ natˢ 7 ∷ []) {Θ′ = natᵗ ∷ uniqᵗ ∷ []} (λ x → x)
                         {ρ′ = 4 ∷ᵉ 0 ∷ᵉ []ᵉ} {ρ = 4 ∷ᵉ []ᵉ} (λ { (here refl) → refl }) refl 3)
_ = Carries.one _ (refl ∷ []) (Carries.one _ (refl ∷ []) Carries.[])

-- LOAD-BEARING: no values, so the one emit carries only the frame and
-- the end; fails if the impl's empty `of` emits a value or nothing
_ : Confirms (of-carries {Γ = Γ₂} (κᵖ two-arrivals) {natᵗ} {ofᵉ []} {ofᵉ []}
                         {u = natᵗ} [] {Θ′ = natᵗ ∷ uniqᵗ ∷ []} (λ x → x)
                         {ρ′ = 4 ∷ᵉ 0 ∷ᵉ []ᵉ} {ρ = 4 ∷ᵉ []ᵉ} (λ { (here refl) → refl }) refl 3)
_ = Carries.quiet _ [] Carries.[]

-- the opening stores of a hot read, at the impl's mint past the root's
S₀ = init-store (κᵖ two-arrivals) (Point.prog two-arrivals) (insᵖ two-arrivals)
       (setAt sourceᵏ (suc (proj₁ (minted (κᵖ two-arrivals) (Point.prog two-arrivals) (insᵖ two-arrivals))))
          (Sched.mint (sched-init (elaborateImpl (κᵖ two-arrivals) (Point.prog two-arrivals)) (embedSlotsImpl (insᵖ two-arrivals)))))
       (<-trans (proj₁ (proj₂ (minted (κᵖ two-arrivals) (Point.prog two-arrivals) (insᵖ two-arrivals)))) (n<1+n _))

-- LOAD-BEARING: a flattener's pair minted at the opening stores, root
-- paths on both sides; fails if the impl's two nodes collide, either
-- side's new node is not below its moved counter, or the rule does not
-- survive the counters' move.  DEGENERATE on the rows: none is registered
-- yet, so no row runs through a paired node -- not a flattener under a
-- live subscription, not below a frame.
installed : (op : FlatOp) → Confirms (flat-install (κᵖ two-arrivals) S₀ {lo = 0} {lo′ = 0} {p = root} {q = root} op ((0 , inj₁ tt) , ([] , 0 , 0 , inj₁ tt)) root~ refl refl refl)
installed op = after record
  { π       = (_ , _ ∷ _ ∷ []) ∷ []
  ; π-keys  = [] ∷ []
  ; π-vals  = ((λ ()) ∷ []) ∷ [] ∷ []
  ; pairs-below = toWitness {a? = all? (λ _ → _ <? _) _} tt , toWitness {a? = all? (λ _ → all? (_<? _) _) _} tt
  ; sources = data~ refl (refl ∷ refl ∷ []) (λ { zero refl → refl ; (suc zero) () }) ∷ []
  ; numbers = slot~ zero refl ∷ []
  ; distinct = ([] ∷ []) , ([] ∷ [])
  ; sync    = (refl , []) ∷ []
  ; rows    = []
  ; dlv-alike = tt
  ; dying-alike = tt
  ; latches = λ _ → (λ _ → refl , refl) , (λ _ → refl , refl)
  ; bounded = toWitness {a? = all? (_<? _) _} tt , toWitness {a? = all? (_<? _) _} tt
  ; swept   = refl ∷ []
  ; uncut   = [] , []
  ; rids    = [] , []
  ; fresh-ids = [] , []
  ; above   = [] , []
  ; census  = λ _ _ → inj₂ (refl , refl , λ ())
  ; owned   = []
  ; ruleP   = rule (λ k ()) (λ ()) (λ ())
  ; ruleI   = rule (λ k ()) (λ ()) (λ ())
  ; scripts = insᵖ two-arrivals , refl , refl
  } (λ { (inj₁ (() , _)) ; (inj₂ (_ , _ , ())) }) (λ a → record { boundP = Arr.boundP a ; boundI = Arr.boundI a ; rows = tt ; lists = Arr.lists a }) [] (λ ())
  , here refl , root~

_ : Confirms (flat-install (κᵖ two-arrivals) S₀ {lo = 0} {lo′ = 0} {p = root} {q = root} (mergeᶠ nothing) ((0 , inj₁ tt) , ([] , 0 , 0 , inj₁ tt)) root~ refl refl refl)
_ = installed (mergeᶠ nothing)

_ : Confirms (flat-install (κᵖ two-arrivals) S₀ {lo = 0} {lo′ = 0} {p = root} {q = root} switchᶠ ((0 , inj₁ tt) , ([] , 0 , 0 , inj₁ tt)) root~ refl refl refl)
_ = installed switchᶠ

_ : Confirms (flat-install (κᵖ two-arrivals) S₀ {lo = 0} {lo′ = 0} {p = root} {q = root} exhaustᶠ ((0 , inj₁ tt) , ([] , 0 , 0 , inj₁ tt)) root~ refl refl refl)
_ = installed exhaustᶠ

-- LOAD-BEARING: the same with the per-inner merge's node riding the
-- quadruple; fails if the merge's node collides with the flattener's or
-- its cell's.  DEGENERATE on the rows, as above.
exploded : (op : FlatOp) → Confirms (flat-install-explode (κᵖ two-arrivals) S₀ {lo = 0} {lo′ = 0} {p = root} {q = root} op ((0 , inj₁ tt) , ([] , 0 , 0 , inj₁ tt)) root~ refl refl refl refl)
exploded op = after record
  { π       = (_ , _ ∷ _ ∷ _ ∷ []) ∷ []
  ; π-keys  = [] ∷ []
  ; π-vals  = ((λ ()) ∷ (λ ()) ∷ []) ∷ ((λ ()) ∷ []) ∷ [] ∷ []
  ; pairs-below = toWitness {a? = all? (λ _ → _ <? _) _} tt , toWitness {a? = all? (λ _ → all? (_<? _) _) _} tt
  ; sources = data~ refl (refl ∷ refl ∷ []) (λ { zero refl → refl ; (suc zero) () }) ∷ []
  ; numbers = slot~ zero refl ∷ []
  ; distinct = ([] ∷ []) , ([] ∷ [])
  ; sync    = (refl , []) ∷ []
  ; rows    = []
  ; dlv-alike = tt
  ; dying-alike = tt
  ; latches = λ _ → (λ _ → refl , refl) , (λ _ → refl , refl)
  ; bounded = toWitness {a? = all? (_<? _) _} tt , toWitness {a? = all? (_<? _) _} tt
  ; swept   = refl ∷ []
  ; uncut   = [] , []
  ; rids    = [] , []
  ; fresh-ids = [] , []
  ; above   = [] , []
  ; census  = λ _ _ → inj₂ (refl , refl , λ ())
  ; owned   = []
  ; ruleP   = rule (λ k ()) (λ ()) (λ ())
  ; ruleI   = rule (λ k ()) (λ ()) (λ ())
  ; scripts = insᵖ two-arrivals , refl , refl
  } (λ { (inj₁ (() , _)) ; (inj₂ (_ , _ , ())) }) (λ a → record { boundP = Arr.boundP a ; boundI = Arr.boundI a ; rows = tt ; lists = Arr.lists a }) [] (λ ())
  , here refl , root~

_ : Confirms (flat-install-explode (κᵖ two-arrivals) S₀ {lo = 0} {lo′ = 0} {p = root} {q = root} (mergeᶠ nothing) ((0 , inj₁ tt) , ([] , 0 , 0 , inj₁ tt)) root~ refl refl refl refl)
_ = exploded (mergeᶠ nothing)

_ : Confirms (flat-install-explode (κᵖ two-arrivals) S₀ {lo = 0} {lo′ = 0} {p = root} {q = root} switchᶠ ((0 , inj₁ tt) , ([] , 0 , 0 , inj₁ tt)) root~ refl refl refl refl)
_ = exploded switchᶠ

_ : Confirms (flat-install-explode (κᵖ two-arrivals) S₀ {lo = 0} {lo′ = 0} {p = root} {q = root} exhaustᶠ ((0 , inj₁ tt) , ([] , 0 , 0 , inj₁ tt)) root~ refl refl refl refl)
_ = exploded exhaustᶠ

-- LOAD-BEARING: a running sum plus the author's variable, seeded by it,
-- over an emit of one payload; fails if the step or the seed reads the
-- author's variable at the slot the mint's binder took, the carried
-- value drifts from the plain accumulator, an output is dropped, or the
-- stamp moves
_ : Confirms (proj₁ (lifts-scan {Γ = Γ₂} (κᵖ two-arrivals)
                       (primˢ add (pairˢ (primˢ add (varˢᵗ (here refl))) (varˢᵗ (there (here refl)))))
                       (varˢᵗ (here refl)) (inputˢ zero) {Θ′ = natᵗ ∷ uniqᵗ ∷ []} (λ x → x)
                       {ρ′ = 4 ∷ᵉ 0 ∷ᵉ []ᵉ} {ρ = 4 ∷ᵉ []ᵉ} 3 (λ { (here refl) → refl }) refl)
               4 ([] , 0 , 0 , inj₁ tt) 4 (inj₂ (inj₁ 3) ∷ [] , 5 , 9 , inj₂ (inj₁ tt))
               (3 ∷ []) refl (refl ∷ []))
_ = refl , (refl ∷ []) , refl

-- LOAD-BEARING: the seed, read off the author's variable
_ : Confirms (proj₂ (lifts-scan {Γ = Γ₂} (κᵖ two-arrivals)
                       (primˢ add (pairˢ (primˢ add (varˢᵗ (here refl))) (varˢᵗ (there (here refl)))))
                       (varˢᵗ (here refl)) (inputˢ zero) {Θ′ = natᵗ ∷ uniqᵗ ∷ []} (λ x → x)
                       {ρ′ = 4 ∷ᵉ 0 ∷ᵉ []ᵉ} {ρ = 4 ∷ᵉ []ᵉ} 3 (λ { (here refl) → refl }) refl))
_ = refl

-- LOAD-BEARING: a test below the author's variable, over a payload it
-- fails, then one it passes; fails if the cutter decides the cut apart from
-- the plain test, keeps a value the plain prefix drops or drops one it
-- keeps, leaves its budget unrelated when it does not cut, or moves the
-- stamp
_ : Confirms (lifts-while {Γ = Γ₂} (κᵖ two-arrivals)
                (primˢ ltᵖ (pairˢ (varˢᵗ (here refl)) (varˢᵗ (there (here refl))))) (inputˢ zero)
                {Θ′ = natᵗ ∷ uniqᵗ ∷ []} (λ x → x) {ρ′ = 4 ∷ᵉ 0 ∷ᵉ []ᵉ} {ρ = 4 ∷ᵉ []ᵉ} 3 (λ { (here refl) → refl }) refl
                tt 1 [] ([] , 0 , 0 , inj₁ tt) (inj₂ (inj₁ 5) ∷ [] , 5 , 9 , inj₂ (inj₁ tt))
                (5 ∷ []) refl (refl ∷ []))
_ = (λ ()) , refl , (refl ∷ []) , refl

_ : Confirms (lifts-while {Γ = Γ₂} (κᵖ two-arrivals)
                (primˢ ltᵖ (pairˢ (varˢᵗ (here refl)) (varˢᵗ (there (here refl))))) (inputˢ zero)
                {Θ′ = natᵗ ∷ uniqᵗ ∷ []} (λ x → x) {ρ′ = 4 ∷ᵉ 0 ∷ᵉ []ᵉ} {ρ = 4 ∷ᵉ []ᵉ} 3 (λ { (here refl) → refl }) refl
                tt 1 [] ([] , 0 , 0 , inj₁ tt) (inj₂ (inj₁ 3) ∷ [] , 5 , 9 , inj₂ (inj₁ tt))
                (3 ∷ []) refl (refl ∷ []))
_ = (λ _ → refl) , refl , (refl ∷ []) , refl

-- LOAD-BEARING: one hot script live at the opening, numbered by its
-- slot and alone on each side; fails if the impl numbers it apart from
-- its slot or lists it twice
_ : Confirms (init-numbers (κᵖ two-arrivals) (Point.prog two-arrivals) (insᵖ two-arrivals))
_ = slot~ zero refl ∷ []

_ : Confirms (init-distinct (κᵖ two-arrivals) (Point.prog two-arrivals) (insᵖ two-arrivals))
_ = ([] ∷ []) , ([] ∷ [])

-- LOAD-BEARING: a scan's cell pair minted at the opening stores, root
-- paths; fails if the impl's cell is not below its moved counter or the
-- rule does not survive the counters' move.  DEGENERATE on the rows, as
-- the flattener's.
_ : Confirms (scan-install (κᵖ two-arrivals) S₀ {lo = 0} {lo′ = 0} {p = root} {q = root} 4 (4 , ([] , 0 , 0 , inj₁ tt)) root~ refl refl refl)
_ = after record
  { π       = (_ , _ ∷ []) ∷ []
  ; π-keys  = [] ∷ []
  ; π-vals  = [] ∷ []
  ; pairs-below = toWitness {a? = all? (λ _ → _ <? _) _} tt , toWitness {a? = all? (λ _ → all? (_<? _) _) _} tt
  ; sources = data~ refl (refl ∷ refl ∷ []) (λ { zero refl → refl ; (suc zero) () }) ∷ []
  ; numbers = slot~ zero refl ∷ []
  ; distinct = ([] ∷ []) , ([] ∷ [])
  ; sync    = (refl , []) ∷ []
  ; rows    = []
  ; dlv-alike = tt
  ; dying-alike = tt
  ; latches = λ _ → (λ _ → refl , refl) , (λ _ → refl , refl)
  ; bounded = toWitness {a? = all? (_<? _) _} tt , toWitness {a? = all? (_<? _) _} tt
  ; swept   = refl ∷ []
  ; uncut   = [] , []
  ; rids    = [] , []
  ; fresh-ids = [] , []
  ; above   = [] , []
  ; census  = λ _ _ → inj₂ (refl , refl , λ ())
  ; owned   = []
  ; ruleP   = rule (λ k ()) (λ ()) (λ ())
  ; ruleI   = rule (λ k ()) (λ ()) (λ ())
  ; scripts = insᵖ two-arrivals , refl , refl
  } (λ { (inj₁ (() , _)) ; (inj₂ (_ , _ , ())) }) (λ a → record { boundP = Arr.boundP a ; boundI = m<n⇒m<1+n (Arr.boundI a) ; rows = tt ; lists = Arr.lists a }) [] (λ ())
  , here refl , root~

-- LOAD-BEARING: a test's pair and its cell minted at the opening
-- stores, root paths; fails if the impl's test and cell collide or
-- either is not below its moved counter.  DEGENERATE on the rows.
_ : Confirms (while-install (κᵖ two-arrivals) S₀ {lo = 0} {lo′ = 0} {p = root} {q = root} (tt , (false , ([] , ([] , 0 , 0 , inj₁ tt)))) root~ refl refl refl refl)
_ = after record
  { π       = (_ , _ ∷ _ ∷ []) ∷ []
  ; π-keys  = [] ∷ []
  ; π-vals  = ((λ ()) ∷ []) ∷ [] ∷ []
  ; pairs-below = toWitness {a? = all? (λ _ → _ <? _) _} tt , toWitness {a? = all? (λ _ → all? (_<? _) _) _} tt
  ; sources = data~ refl (refl ∷ refl ∷ []) (λ { zero refl → refl ; (suc zero) () }) ∷ []
  ; numbers = slot~ zero refl ∷ []
  ; distinct = ([] ∷ []) , ([] ∷ [])
  ; sync    = (refl , []) ∷ []
  ; rows    = []
  ; dlv-alike = tt
  ; dying-alike = tt
  ; latches = λ _ → (λ _ → refl , refl) , (λ _ → refl , refl)
  ; bounded = toWitness {a? = all? (_<? _) _} tt , toWitness {a? = all? (_<? _) _} tt
  ; swept   = refl ∷ []
  ; uncut   = [] , []
  ; rids    = [] , []
  ; fresh-ids = [] , []
  ; above   = [] , []
  ; census  = λ _ _ → inj₂ (refl , refl , λ ())
  ; owned   = []
  ; ruleP   = rule (λ k ()) (λ ()) (λ ())
  ; ruleI   = rule (λ k ()) (λ ()) (λ ())
  ; scripts = insᵖ two-arrivals , refl , refl
  } (λ { (inj₁ (() , _)) ; (inj₂ (_ , _ , ())) }) (λ a → record { boundP = Arr.boundP a ; boundI = m<n⇒m<1+n (Arr.boundI a) ; rows = tt ; lists = Arr.lists a }) [] (λ ())
  , here refl , root~
