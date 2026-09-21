-- WHICH PLAIN TREES A SHARE MAY BE DEFINED BY, stated as a predicate on
-- the plain tree rather than as a second grammar.
--
-- THE HOLE THIS CLOSES.  `subs-shared` subscribes a slot's definition
-- STRAIGHT DOWN the consumer's path -- no `inputᵖ`, no `stamp` -- so a
-- definition's emissions reach the wire exactly as written.  At an
-- observable-typed slot that is a forgery channel, and a machine-checked
-- table walked through it: a `delivery` whose source no `init` ever
-- enlisted, under an ordinary `mergeAllˢ`, with the author having
-- written nothing unusual.
--
-- WHERE THE BAR GOES, AND IT IS ONE PLACE.  Six readings in
-- Probed.Share-Channel locate the channel exactly:
--
--   * a DATA-typed slot cannot forge at all, and not because `isData`
--     forbids a closure -- because the reference site elaborates to
--     `inputᵖ i`, whose deliveries arm is `mergeAllᵉ (mapᵉ stamp
--     (batchSyncᵉ (input i)))`, and `subs-shared` fires at that INNER
--     `input i`.  The definition is substituted UNDER `stamp` and is
--     wrapped on its way out.  A definition that is a raw `input`
--     beneath a flattener -- the very shape Refuted.Flattened-Input
--     refutes in an ELABORATED tree -- is accepted here.
--
--   * an OBSERVABLE-typed slot stands at `plainᵗ (obs u) = obs (emitᵗ u)`,
--     so its VALUES are observables of envelopes, and a `mergeAllˢ` on
--     the reference flattens them via `laneᵛ` -- subscribing them
--     directly, so what they emit reaches the wire having never passed
--     `stamp`.
--
-- So the whole channel is a value at an ENVELOPE-CARRYING observable
-- type, and `strmᵗ` is the only INTRODUCTION form for an
-- observable-typed value -- every other `Tm` at `obs _` is a
-- projection, a variable or a branch, and destructs one introduced
-- somewhere.  One rule at `strmᵗ` therefore catches observables buried
-- in products and lists without this family ever recursing into the
-- slot's TYPE.
--
-- WHY IT IS NOT INDEXED BY THE AUTHOR'S TYPE, which would have been the
-- tidier shape.  A definition may flatten an `obs natᵗ` of its own
-- making, and `obs natᵗ` is outside the image of `plainᵗ` entirely --
-- `plainᵗ (obs u)` is always `obs (emitᵗ u)`.  An author-type-indexed
-- family would have excluded a definition the machine accepts, which is
-- a narrowing and not a repair.
--
-- WHY THE DEFINITION LANGUAGE STAYS THE PLAIN ONE.  The obvious move is
-- to make a definition BE an `SExp` and read it back protocol-blind.
-- No such reading exists: at `mergeAllˢ` it would have to flatten a
-- stream whose values are elaborations and hand back a plain value,
-- and the types say `emitᵗ t` where a raw reading needs `plainᵗ t`.  A
-- flattener merges envelope streams; there is no protocol-blind flatten
-- to read it as.
--
-- AND WHY `embed` IS NOT THE FLATTENER'S OWN LANE EXTRACTION.  Making
-- `embed` be `mapᵉ laneᵛ ∘ elaborate` typechecks exactly at the slot
-- type and is wrong: the reference's `mergeAllᵖ` already applies
-- `laneᵛ`, so such a definition is laned twice.  Probed.Share-Channel
-- reads it rejected over an EMPTY inner, so the fault is structural and
-- not a matter of what the definition carries.
module Rx.Authored where

open import Data.Bool using (Bool; true; false; T; not)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Product using (Σ; _,_; proj₁)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Rx.Exp using (Ty; Ctx; Exp; Tm; Fn; Closed; PrimOp;
  unitᵗ; boolᵗ; natᵗ; uniqᵗ; listᵗ; obs; _×ᵗ_; _+ᵗ_; _≟ᵗ_;
  input; ofᵉ; emptyᵉ; takeᵉ; batchSyncᵉ; mapᵉ; scanᵉ; mergeAllᵉ;
  switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ; mintᵉ; Ren∈; renExp;
  varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ; nilᵗ; consᵗ; inlᵗ; inrᵗ;
  caseᵗ; foldᵗ; ifᵗ; primᵗ; strmᵗ)
open import Rx.Envelope using (emitKindᵗ)
open import Rx.SExp using (SExp)
open import Rx.Elaborate using (toPlain)

------------------------------------------------------------------
-- The one type test.
------------------------------------------------------------------

-- DOES A VALUE AT THIS TYPE CARRY AN ENVELOPE THE MACHINE WILL READ?
-- `emitᵗ u` is `listᵗ (instEventᵗ uniqᵗ (plainᵗ u)) ×ᵗ (uniqᵗ ×ᵗ (uniqᵗ
-- ×ᵗ emitKindᵗ))`, and its RIGHT component is a fixed closed type that
-- says nothing about the payload.  Matching on that header recognises
-- every envelope at once, at every payload type, without this test
-- having to know `plainᵗ`.
--
-- THE TEST IS EXACT RATHER THAN CONSERVATIVE, which is worth saying
-- since it looks like a shape coincidence.  Anything carrying that
-- header IS read as an envelope by `Rx.Envelope.Decode`, whatever it
-- was built to mean, so a tree handing one over is handing over an
-- envelope whether or not it meant to.
isEnvᵗ : Ty → Bool
isEnvᵗ (_ ×ᵗ hdr) = ⌊ hdr ≟ᵗ (uniqᵗ ×ᵗ (uniqᵗ ×ᵗ emitKindᵗ)) ⌋
isEnvᵗ _          = false

------------------------------------------------------------------
-- Elaboration-derived trees.
------------------------------------------------------------------

-- A TREE THE ELABORATION BUILT, up to the two operations that move a
-- tree without touching what it emits.  `mintᵉ` because `elaborate` is
-- `mintᵉ ∘ toPlain` and a closed definition arrives already minted;
-- renaming because a definition written under a `mapᵉ` binder stands in
-- a wider term telescope than the elaboration it carries, which is what
-- an author's `source$.pipe(map(x => inner$))` produces.
data Elabᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Exp Γ Δᵍ Δ Θ t → Set where
  elab-toPlain : ∀ {n} {Γ₀ : Ctx n} {Δᵍ₀ Δ₀ Θ₀ u} (s : SExp Γ₀ Δᵍ₀ Δ₀ Θ₀ u)
               → Elabᵉ (toPlain s)
  elab-mint    : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} {e : Exp Γ Δᵍ Δ (uniqᵗ ∷ Θ) t}
               → Elabᵉ e → Elabᵉ (mintᵉ e)
  elab-ren     : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} {e : Exp Γ Δᵍ Δ Θ t}
                 (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′)
               → Elabᵉ e → Elabᵉ (renExp ρg ρd ρt e)

------------------------------------------------------------------
-- Authored trees.
------------------------------------------------------------------

-- EVERY CLAUSE BUT ONE IS "RECURSE", and the family mirrors the grammar
-- one former at a time so that it can be checked against `Rx.Exp` by
-- eye.  The clause that is not is `auth-strm`, whose side condition
-- `T (not (isEnvᵗ t))` discharges by unification at every concrete
-- type, exactly as `isData` and `inputsBelowᵉ` already do in `Slot`.
mutual

  data Authᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Exp Γ Δᵍ Δ Θ t → Set where
    auth-elab   : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} {e : Exp Γ Δᵍ Δ Θ t}
                → Elabᵉ e → Authᵉ e
    auth-input  : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ} (i : Fin n)
                → Authᵉ {Γ = Γ} {Δᵍ} {Δ} {Θ} (input i)
    auth-of     : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} {ts : List (Tm Γ Δᵍ Δ Θ t)}
                → Authᵗs ts → Authᵉ (ofᵉ ts)
    auth-empty  : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Authᵉ {Γ = Γ} {Δᵍ} {Δ} {Θ} {t} emptyᵉ
    auth-take   : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} {k : Tm Γ Δᵍ Δ Θ natᵗ}
                  {e : Exp Γ Δᵍ Δ Θ t}
                → Authᵗ k → Authᵉ e → Authᵉ (takeᵉ k e)
    auth-batch  : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} {e : Exp Γ Δᵍ Δ Θ t}
                → Authᵉ e → Authᵉ (batchSyncᵉ e)
    auth-map    : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s t} {f : Fn Γ Δᵍ Δ Θ s t}
                  {e : Exp Γ Δᵍ Δ Θ s}
                → Authᵗ f → Authᵉ e → Authᵉ (mapᵉ f e)
    auth-scan   : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s t} {f : Fn Γ Δᵍ Δ Θ (t ×ᵗ s) t}
                  {z : Tm Γ Δᵍ Δ Θ t} {e : Exp Γ Δᵍ Δ Θ s}
                → Authᵗ f → Authᵗ z → Authᵉ e → Authᵉ (scanᵉ f z e)
    auth-merge  : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} {k : Maybe ℕ}
                  {e : Exp Γ Δᵍ Δ Θ (obs t)}
                → Authᵉ e → Authᵉ (mergeAllᵉ k e)
    auth-switch : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} {e : Exp Γ Δᵍ Δ Θ (obs t)}
                → Authᵉ e → Authᵉ (switchAllᵉ e)
    auth-exhaust : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} {e : Exp Γ Δᵍ Δ Θ (obs t)}
                → Authᵉ e → Authᵉ (exhaustAllᵉ e)
    auth-μ      : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} {e : Exp Γ (t ∷ Δᵍ) Δ Θ t}
                → Authᵉ e → Authᵉ (μᵉ e)
    auth-var    : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (x : t ∈ Δ)
                → Authᵉ {Γ = Γ} {Δᵍ} {Δ} {Θ} (varᵉ x)
    auth-defer  : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} {e : Exp Γ [] (Δᵍ ++ Δ) Θ t}
                → Authᵉ {Γ = Γ} {Δᵍ = []} {Δ = Δᵍ ++ Δ} {Θ = Θ} {t = t} e
                → Authᵉ (deferᵉ {Γ = Γ} {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} e)
    auth-mint   : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} {e : Exp Γ Δᵍ Δ (uniqᵗ ∷ Θ) t}
                → Authᵉ e → Authᵉ (mintᵉ e)

  data Authᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Tm Γ Δᵍ Δ Θ t → Set where
    auth-varᵗ  : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (x : t ∈ Θ)
               → Authᵗ {Γ = Γ} {Δᵍ} {Δ} {Θ} (varᵗ x)
    auth-unit  : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ} → Authᵗ {Γ = Γ} {Δᵍ} {Δ} {Θ} unit̂
    auth-bool  : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ} (b : Bool)
               → Authᵗ {Γ = Γ} {Δᵍ} {Δ} {Θ} (bool̂ b)
    auth-nat   : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ} (k : ℕ)
               → Authᵗ {Γ = Γ} {Δᵍ} {Δ} {Θ} (nat̂ k)
    auth-pair  : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s t} {a : Tm Γ Δᵍ Δ Θ s} {b : Tm Γ Δᵍ Δ Θ t}
               → Authᵗ a → Authᵗ b → Authᵗ (pairᵗ a b)
    auth-fst   : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s t} {p : Tm Γ Δᵍ Δ Θ (s ×ᵗ t)}
               → Authᵗ p → Authᵗ (fstᵗ p)
    auth-snd   : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s t} {p : Tm Γ Δᵍ Δ Θ (s ×ᵗ t)}
               → Authᵗ p → Authᵗ (sndᵗ p)
    auth-nil   : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Authᵗ {Γ = Γ} {Δᵍ} {Δ} {Θ} {listᵗ t} nilᵗ
    auth-cons  : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} {h : Tm Γ Δᵍ Δ Θ t} {r : Tm Γ Δᵍ Δ Θ (listᵗ t)}
               → Authᵗ h → Authᵗ r → Authᵗ (consᵗ h r)
    auth-inl   : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s t} {a : Tm Γ Δᵍ Δ Θ s}
               → Authᵗ a → Authᵗ {t = s +ᵗ t} (inlᵗ a)
    auth-inr   : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s t} {b : Tm Γ Δᵍ Δ Θ t}
               → Authᵗ b → Authᵗ {t = s +ᵗ t} (inrᵗ b)
    auth-case  : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s t u} {p : Tm Γ Δᵍ Δ Θ (s +ᵗ t)}
                 {l : Tm Γ Δᵍ Δ (s ∷ Θ) u} {r : Tm Γ Δᵍ Δ (t ∷ Θ) u}
               → Authᵗ p → Authᵗ l → Authᵗ r → Authᵗ (caseᵗ p l r)
    auth-fold  : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s u} {l : Tm Γ Δᵍ Δ Θ (listᵗ s)}
                 {z : Tm Γ Δᵍ Δ Θ u} {f : Tm Γ Δᵍ Δ (s ∷ u ∷ Θ) u}
               → Authᵗ l → Authᵗ z → Authᵗ f → Authᵗ (foldᵗ l z f)
    auth-if    : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} {c : Tm Γ Δᵍ Δ Θ boolᵗ}
                 {a b : Tm Γ Δᵍ Δ Θ t}
               → Authᵗ c → Authᵗ a → Authᵗ b → Authᵗ (ifᵗ c a b)
    auth-prim  : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s t} (op : PrimOp s t) {a : Tm Γ Δᵍ Δ Θ s}
               → Authᵗ a → Authᵗ (primᵗ op a)

    -- THE ONE CLAUSE THAT BARS ANYTHING.  A stream carried as a VALUE
    -- is what the consumer's flattener subscribes, so at an envelope
    -- type it must be an elaboration and nowhere else does the family
    -- ask.
    auth-strm  : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} {e : Exp Γ Δᵍ Δ Θ t}
                 {ok : T (not (isEnvᵗ t))}
               → Authᵉ e → Authᵗ (strmᵗ e)
    auth-strmᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} {e : Exp Γ Δᵍ Δ Θ t}
               → Elabᵉ e → Authᵗ (strmᵗ e)

  data Authᵗs : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → List (Tm Γ Δᵍ Δ Θ t) → Set where
    auth-[]  : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t}
             → Authᵗs {Γ = Γ} {Δᵍ} {Δ} {Θ} {t} []
    auth-∷   : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} {x : Tm Γ Δᵍ Δ Θ t} {xs : List (Tm Γ Δᵍ Δ Θ t)}
             → Authᵗ x → Authᵗs xs → Authᵗs (x ∷ xs)

------------------------------------------------------------------
-- The family a share may be defined by.
------------------------------------------------------------------

-- A DEFINITION IS A PLAIN TREE CARRYING ITS OWN AUTHORSHIP, so `embed`
-- is the first projection and the evaluator reads exactly the tree it
-- would have read at `plainPalette`.
Authored : ∀ {n} → Ctx n → Ty → Set
Authored Γ t = Σ (Closed Γ t) Authᵉ

authoredTree : ∀ {n} {Γ : Ctx n} {t} → Authored Γ t → Closed Γ t
authoredTree = proj₁
