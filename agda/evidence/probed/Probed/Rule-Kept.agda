-- EVERY RUN KEEPS THE RULE, INSTANTIATED AT STATES THE BUILDER REACHES.
-- The builder's own `reducible` is a real body for every former these
-- programs use, so a row's derivation is the one the run computes, not
-- one assembled from constructors, and the state before and after it is
-- the one the run leaves.  The rule's conclusion is decided at that
-- store: `sound?` reads every row's nodes and terminus off the concrete
-- registry, and `toSound` turns the decision into the record, so a row
-- whose store broke the rule would leave `from-yes` at `⊤` and fail.
--
-- Two programs.  `prog` merges two deferred inners, so the store holds
-- two rows through the merge's node, each through its own inner's.
-- `prog₁` merges a read of a shared slot, whose def is a deferred inner,
-- beside a deferred inner of its own: the store then holds rows ending
-- at the root and a row through a node ending at the share's sink, which
-- is the only shape in which one terminus per node can fail.  Both
-- stores are pinned by the rows that read their nodes and termini.
--
-- LOAD-BEARING: each row at the run's own path -- the root subscribe,
-- the merge's outer fold and its head step, in both programs.  Each
-- decides one terminus per node and node freshness over a store of two
-- or three rows sharing a node, and the continuation's own ends and
-- freshness; it fails if a run registers a row through a node another
-- row ends elsewhere from, a node at or past the counter, or a row
-- through the folded path's node ending off it.
-- LOAD-BEARING: the rows asking the share program's subscribe and fold
-- for a second continuation ending at the sink.  Their own clauses are
-- vacuous, since the sink carries no node, so what they decide is the
-- rule itself at a store with two termini.
-- DEGENERATE: the first program's fold asked for the root.  The root
-- carries no node, so it re-decides the fold's rule and nothing else.
--
-- NOT COVERED: a second continuation that carries a node, which the
-- statements' `Agree` is the whole content of -- every κ₂ here is the
-- run's own path or node-free; `Probed.Base-Leaves` reaches one.  Nor a
-- share whose def FLATTENS: its def runs on fallen ground, the inner it
-- subscribes is `rawInner`'s, and a postulate does not compute, so no
-- run through one reaches a store.  Nor a cut, a switch, an exhaust, a
-- take, a scan, a batchSync or a scripted slot.
module Probed.Rule-Kept where

-- TARGET: step-kept @152c13
-- TARGET: subscribe-kept @93c511
-- TARGET: fold-kept @8401d5

open import Data.Bool using (true; T)
open import Data.Bool.ListAction using (any)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.Nat using () renaming (_≟_ to _≟ⁿ_)
open import Data.List.Relation.Unary.All using (All; all?; lookup)
open import Data.List.Relation.Unary.Any using (here; there; any?)
open import Data.Maybe using (nothing; just)
open import Data.Maybe.Properties using (≡-dec)
open import Data.Nat using (ℕ; _<_; _≤_; _<?_; _≡ᵇ_; z≤n)
open import Data.Nat.Properties using (≤-refl; ≡ᵇ⇒≡)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Vec using () renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Fin using (zero)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (Dec; yes; from-yes; _×-dec_; _→-dec_; ¬?)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Probed.Apparatus using (Confirms)
open import Rx.Exp using (Ctx; Closed; Env; Tm; natᵗ; obs; ofᵉ; deferᵉ; mergeAllᵉ; input; strmᵗ; nat̂; []ᵉ; evalWith)
open import Rx.Slots using (Slots; shared)
open import Rx.Evaluator using (Sched; EvalSt; RegRow; Path; Frame; root; share-sink; _↠[_]_; frameNodes; pathHasNode;
  thru-outer; mergeAllᵒ; sched-init; st-init)
open import Rx.Evaluator.Freshness using (nodeCt)
open import Rx.Evaluator.Domain using (subscribeE⇓; foldPath⇓; stepFrame⇓; fold-step; subs-merge-all; sub-all; subs-of)
open import Rx.Evaluator.Reducible using (reducible; red-env)
open import Rx.Evaluator.Reducible.Support using (rootRP; standing; rule; Sound; sound; grounded; rowEnd; endOf; ∨-T; Distinct; rowDistinct; step-kept; subscribe-kept; fold-kept)

------------------------------------------------------------------
-- THE RULE, DECIDED AT A CONCRETE STORE.
------------------------------------------------------------------

_∈?_ : ∀ (k : ℕ) xs → Dec (k ∈ xs)
k ∈? xs = any? (k ≟ⁿ_) xs

pathNodes : ∀ {n} {Γ : Ctx n} {lo s t} → Path Γ lo s t → List ℕ
pathNodes root             = []
pathNodes (share-sink _ _) = []
pathNodes (f ↠[ _ ] p)     = frameNodes f ++ pathNodes p

rowNodes : ∀ {n} {Γ : Ctx n} {t} → RegRow Γ t → List ℕ
rowNodes (_ , _ , (_ , p)) = pathNodes p

anyᵇ→∈ : ∀ {k} (xs : List ℕ) → T (any (_≡ᵇ k) xs) → k ∈ xs
anyᵇ→∈ {k} (x ∷ xs) h with ∨-T {x ≡ᵇ k} h
... | inj₁ a = here (sym (≡ᵇ⇒≡ x k a))
... | inj₂ b = there (anyᵇ→∈ xs b)

has→∈ : ∀ {n} {Γ : Ctx n} {lo s t} k (p : Path Γ lo s t) → T (pathHasNode k p) → k ∈ pathNodes p
has→∈ k (f ↠[ _ ] p) h with ∨-T {any (_≡ᵇ k) (frameNodes f)} h
... | inj₁ a = ∈-++⁺ˡ (anyᵇ→∈ (frameNodes f) a)
... | inj₂ b = ∈-++⁺ʳ (frameNodes f) (has→∈ k p b)

module _ {n} {Γ : Ctx n} {t} where

  Fresh Tied : ℕ → List (RegRow Γ t) → Set
  Fresh ct reg = All (λ r → All (_< ct) (rowNodes r)) reg
  Tied  ct reg = All (λ r → All (λ r′ → All (λ k → k ∈ rowNodes r′ → rowEnd r ≡ rowEnd r′) (rowNodes r)) reg) reg

  Ends : ∀ {lo s} → Path Γ lo s t → List (RegRow Γ t) → Set
  Ends κ reg = All (λ k → All (λ r → k ∈ rowNodes r → rowEnd r ≡ endOf κ) reg) (pathNodes κ)

  DistinctD : ∀ {lo s} → Path Γ lo s t → Set
  DistinctD root             = ⊤
  DistinctD (share-sink _ _) = ⊤
  DistinctD (f ↠[ _ ] κ)     = All (λ k → ¬ (k ∈ pathNodes κ)) (frameNodes f) × DistinctD κ

  distinct? : ∀ {lo s} (κ : Path Γ lo s t) → Dec (DistinctD κ)
  distinct? root             = yes tt
  distinct? (share-sink _ _) = yes tt
  distinct? (f ↠[ _ ] κ)     = all? (λ k → ¬? (k ∈? pathNodes κ)) (frameNodes f) ×-dec distinct? κ

  toDistinct : ∀ {lo s} (κ : Path Γ lo s t) → DistinctD κ → Distinct κ
  toDistinct root             _        = tt
  toDistinct (share-sink _ _) _        = tt
  toDistinct (f ↠[ _ ] κ)     (ap , d) = (λ k a h → lookup ap (anyᵇ→∈ (frameNodes f) a) (has→∈ k κ h)) , toDistinct κ d

  RowD : RegRow Γ t → Set
  RowD (_ , _ , (_ , p)) = DistinctD p

  rowD? : ∀ r → Dec (RowD r)
  rowD? (_ , _ , (_ , p)) = distinct? p

  toRowD : ∀ r → RowD r → rowDistinct r
  toRowD (_ , _ , (_ , p)) = toDistinct p

  SoundD : ∀ {lo s} → Path Γ lo s t → ℕ → List (RegRow Γ t) → Set
  SoundD κ ct reg = (Fresh ct reg × Tied ct reg × All RowD reg) × Ends κ reg × All (_< ct) (pathNodes κ) × DistinctD κ

  sound? : ∀ {lo s} (κ : Path Γ lo s t) ct reg → Dec (SoundD κ ct reg)
  sound? κ ct reg =
    (all? (λ r → all? (_<? ct) (rowNodes r)) reg
     ×-dec all? (λ r → all? (λ r′ → all? (λ k → (k ∈? rowNodes r′) →-dec ≡-dec _≟ᶠ_ (rowEnd r) (rowEnd r′))
                                           (rowNodes r)) reg) reg
     ×-dec all? rowD? reg)
    ×-dec all? (λ k → all? (λ r → (k ∈? rowNodes r) →-dec ≡-dec _≟ᶠ_ (rowEnd r) (endOf κ)) reg) (pathNodes κ)
    ×-dec all? (_<? ct) (pathNodes κ)
    ×-dec distinct? κ

  toSound : ∀ {e : Closed Γ t} {lo s} {κ : Path Γ lo s t} {sched : Sched Γ} {st : EvalSt e}
          → SoundD κ (nodeCt sched) (EvalSt.registry st) → Sound κ sched st
  toSound {κ = κ} ((fr , ti , rd) , en , fp , dκ) =
    sound (rule (λ k {r} {r′} r∈ r′∈ th th′ →
                   lookup (lookup (lookup ti r∈) r′∈) (has→∈ k (proj₂ (proj₂ (proj₂ r))) th) (has→∈ k (proj₂ (proj₂ (proj₂ r′))) th′))
                (λ {r} r∈ k th → lookup (lookup fr r∈) (has→∈ k (proj₂ (proj₂ (proj₂ r))) th))
                (λ {r} r∈ → toRowD r (lookup rd r∈)))
          (λ k th {r} r∈ th′ → lookup (lookup en (has→∈ k κ th)) r∈ (has→∈ k (proj₂ (proj₂ (proj₂ r))) th′))
          (λ k th → lookup fp (has→∈ k κ th))
          (toDistinct κ dκ)

------------------------------------------------------------------
-- THE OUTER FOLD A MERGE OF A LITERAL RUNS, read off its subscribe.
------------------------------------------------------------------

outer-fold : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {Θ u lo} {ρ : Env Γ Θ} {lim}
               {ts : List (Tm Γ [] [] Θ (obs u))} {κ : Path Γ lo u t} {now sched st r}
           → subscribeE⇓ {e = e} (Θ , mergeAllᵉ lim (ofᵉ ts) , ρ) κ now sched st r
           → Σ (Sched Γ) λ sc → Σ (EvalSt e) λ st′ →
               foldPath⇓ {e = e} now (thru-outer mergeAllᵒ (nodeCt sched) ↠[ ≤-refl ] κ)
                 (map (λ tm → evalWith tm ρ) ts) true sc st′ r
outer-fold (subs-merge-all (sub-all refl (subs-of fd))) = _ , _ , fd

------------------------------------------------------------------
-- THE PROGRAM: a merge of two deferred inners, so two rows run through
-- the merge's node and each through its own inner's.
------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ᵛ

prog : Closed Γ₀ natᵗ
prog = mergeAllᵉ nothing (ofᵉ (strmᵗ (deferᵉ (ofᵉ (nat̂ 5 ∷ []))) ∷ strmᵗ (deferᵉ (ofᵉ (nat̂ 6 ∷ []))) ∷ []))

noSlots : Slots Γ₀
noSlots ()

sched₀ : Sched Γ₀
sched₀ = sched-init prog noSlots

st₀ : EvalSt prog
st₀ = st-init prog

so₀ : Sound {e = prog} (root {lo = 0}) sched₀ st₀
so₀ = sound (rule (λ k ()) (λ ()) (λ ())) (λ k ()) (λ k ()) tt

run = let aM = <-wellFounded _ in
      reducible aM prog []ᵉ (red-env {Γ = Γ₀} aM []ᵉ) (root {lo = 0}) (standing tt) rootRP tt 0
        sched₀ st₀ ≤-refl (grounded tt so₀)

d = proj₁ (proj₂ run)

sched₁ : Sched Γ₀
sched₁ = proj₁ (proj₂ (proj₁ run))

st₁ : EvalSt prog
st₁ = proj₂ (proj₂ (proj₁ run))

-- LOAD-BEARING
_ : Confirms (subscribe-kept d so₀ (root {lo = 0}) so₀ (λ _ _ _ → refl))
_ = toSound {sched = sched₁} {st = st₁} (from-yes (sound? (root {lo = 0}) (nodeCt sched₁) (EvalSt.registry st₁)))

_ : map (λ r → rowNodes r , rowEnd r) (EvalSt.registry st₁)
      ≡ ((2 ∷ 0 ∷ 1 ∷ []) , nothing) ∷ ((4 ∷ 0 ∷ 3 ∷ []) , nothing) ∷ []
_ = refl

-- the merge's outer fold, and the state it starts from
of₀ = outer-fold d

κo : Path Γ₀ 0 (obs natᵗ) natᵗ
κo = thru-outer mergeAllᵒ (nodeCt sched₀) ↠[ ≤-refl ] root

fd = proj₂ (proj₂ of₀)

sof : Sound κo (proj₁ of₀) (proj₁ (proj₂ of₀))
sof = toSound (from-yes (sound? κo (nodeCt (proj₁ of₀)) (EvalSt.registry (proj₁ (proj₂ of₀)))))

sor : Sound (root {lo = 0}) (proj₁ of₀) (proj₁ (proj₂ of₀))
sor = toSound (from-yes (sound? (root {lo = 0}) (nodeCt (proj₁ of₀)) (EvalSt.registry (proj₁ (proj₂ of₀)))))

-- LOAD-BEARING
_ : Confirms (fold-kept fd sof κo sof (λ _ _ _ → refl))
_ = toSound {sched = sched₁} {st = st₁} (from-yes (sound? κo (nodeCt sched₁) (EvalSt.registry st₁)))

-- DEGENERATE
_ : Confirms (fold-kept fd sof (root {lo = 0}) sor (λ k _ ()))
_ = toSound {sched = sched₁} {st = st₁} (from-yes (sound? (root {lo = 0}) (nodeCt sched₁) (EvalSt.registry st₁)))

------------------------------------------------------------------
-- THE SHARE: slot 0 is a shared merge of a deferred inner, and the
-- root merges a read of it beside a deferred inner of its own.  The
-- store then holds rows ending at the root and rows ending at the
-- share's sink, through different nodes.
------------------------------------------------------------------

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ᵛ []ᵛ

def₁ : Closed Γ₁ natᵗ
def₁ = deferᵉ (ofᵉ (nat̂ 7 ∷ []))

slots₁ : Slots Γ₁
slots₁ zero = shared def₁

prog₁ : Closed Γ₁ natᵗ
prog₁ = mergeAllᵉ nothing (ofᵉ (strmᵗ (input zero) ∷ strmᵗ (deferᵉ (ofᵉ (nat̂ 5 ∷ []))) ∷ []))

schedS : Sched Γ₁
schedS = sched-init prog₁ slots₁

stS : EvalSt prog₁
stS = st-init prog₁

soS : Sound {e = prog₁} (root {lo = 1}) schedS stS
soS = sound (rule (λ k ()) (λ ()) (λ ())) (λ k ()) (λ k ()) tt

runS = let aM = <-wellFounded _ in
       reducible aM prog₁ []ᵉ (red-env {Γ = Γ₁} aM []ᵉ) (root {lo = 1}) (standing tt) rootRP tt 0
         schedS stS ≤-refl (grounded tt soS)

dS = proj₁ (proj₂ runS)

schedS₁ : Sched Γ₁
schedS₁ = proj₁ (proj₂ (proj₁ runS))

stS₁ : EvalSt prog₁
stS₁ = proj₂ (proj₂ (proj₁ runS))


_ : map (λ r → rowNodes r , rowEnd r) (EvalSt.registry stS₁)
      ≡ ((0 ∷ 1 ∷ []) , nothing) ∷ ((2 ∷ []) , just zero) ∷ ((4 ∷ 0 ∷ 3 ∷ []) , nothing) ∷ []
_ = refl

sink₀ : Path Γ₁ 0 natᵗ natᵗ
sink₀ = share-sink zero z≤n

soSk : Sound {e = prog₁} sink₀ schedS stS
soSk = sound (rule (λ k ()) (λ ()) (λ ())) (λ k ()) (λ k ()) tt

-- LOAD-BEARING
_ : Confirms (subscribe-kept dS soS (root {lo = 1}) soS (λ _ _ _ → refl))
_ = toSound {sched = schedS₁} {st = stS₁} (from-yes (sound? (root {lo = 1}) (nodeCt schedS₁) (EvalSt.registry stS₁)))

-- LOAD-BEARING
_ : Confirms (subscribe-kept dS soS sink₀ soSk (λ k ()))
_ = toSound {sched = schedS₁} {st = stS₁} (from-yes (sound? sink₀ (nodeCt schedS₁) (EvalSt.registry stS₁)))

ofS = outer-fold dS

κS : Path Γ₁ 1 (obs natᵗ) natᵗ
κS = thru-outer mergeAllᵒ (nodeCt schedS) ↠[ ≤-refl ] root

fdS = proj₂ (proj₂ ofS)

pre? : ∀ {lo s} (κ : Path Γ₁ lo s natᵗ) → Set
pre? κ = Sound κ (proj₁ ofS) (proj₁ (proj₂ ofS))

soκS : pre? κS
soκS = toSound (from-yes (sound? κS (nodeCt (proj₁ ofS)) (EvalSt.registry (proj₁ (proj₂ ofS)))))

soSkS : pre? sink₀
soSkS = toSound (from-yes (sound? sink₀ (nodeCt (proj₁ ofS)) (EvalSt.registry (proj₁ (proj₂ ofS)))))

-- LOAD-BEARING
_ : Confirms (fold-kept fdS soκS κS soκS (λ _ _ _ → refl))
_ = toSound {sched = schedS₁} {st = stS₁} (from-yes (sound? κS (nodeCt schedS₁) (EvalSt.registry stS₁)))

-- LOAD-BEARING
_ : Confirms (fold-kept fdS soκS sink₀ soSkS (λ k _ ()))
_ = toSound {sched = schedS₁} {st = stS₁} (from-yes (sound? sink₀ (nodeCt schedS₁) (EvalSt.registry stS₁)))

-- the outer fold's head step: the thru-outer frame consuming the literal
step-of : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo ℓ} {f : Frame Γ s u} {le : lo ≤ ℓ}
            {κ : Path Γ ℓ u t} {now vals fin sched st r}
        → foldPath⇓ {e = e} now (f ↠[ le ] κ) vals fin sched st r
        → Σ _ (stepFrame⇓ {e = e} now f κ vals fin sched st)
step-of (fold-step sd _) = _ , sd

stp = step-of fd
stpS = step-of fdS

-- LOAD-BEARING
_ : Confirms (step-kept ≤-refl (proj₂ stp) sof)
_ = toSound (from-yes (sound? κo (nodeCt (proj₁ (proj₂ (proj₂ (proj₂ (proj₁ stp))))))
                                        (EvalSt.registry (proj₂ (proj₂ (proj₂ (proj₂ (proj₁ stp))))))))

-- LOAD-BEARING
_ : Confirms (step-kept ≤-refl (proj₂ stpS) soκS)
_ = toSound (from-yes (sound? κS (nodeCt (proj₁ (proj₂ (proj₂ (proj₂ (proj₁ stpS))))))
                                         (EvalSt.registry (proj₂ (proj₂ (proj₂ (proj₂ (proj₁ stpS))))))))
