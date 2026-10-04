------------------------------------------------------------------
-- A CASCADE'S VALUE PASS, ONE PATH CONSTRUCTOR AT A TIME.  A related
-- chain hands its values down two related paths, and the fold reads
-- both derivations together: one `PathRel` constructor's frames per
-- step, the stores kept related, the values each sends rootward
-- related, and the chains the pass has not reached kept paired.
--
-- A STEP'S ARM SEES THE PLAIN FRAME'S STEP AND THE IMPL'S WHOLE FOLD.
-- The impl runs a former's frames where the plain run steps once, so an
-- arm takes the impl fold from the top of that run and hands back what
-- is left of it below the run: the tail the plain path continues on,
-- related again, and the group that reaches it.  The plain fold is the
-- descent; an impl-only lane is the one step that moves the impl alone.
------------------------------------------------------------------
module Simulation.Pass where

open import Data.Bool    using (Bool; true; false; if_then_else_)
open import Data.Fin     using (Fin; toℕ; _↑ʳ_)
open import Data.Bool.ListAction using (any)
open import Data.List    using (List; []; _∷_; _++_; map; concat)
open import Data.List.Properties using (map-++)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_; ++⁺)
open import Data.Maybe   using (nothing; just)
open import Data.Nat     using (ℕ; _≤_; _≡ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_)
open import Data.Vec     using (lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)

open import Rx.Prim      using (Tick; valueᵖ; completeᵖ)
open import Rx.Exp       using (Ctx; Closed; Val; uniqᵗ; _×ᵗ_; FnClo)
open import Rx.Evaluator using (Stream; Sched; EvalSt; Arrival; arrVal; arrTy; arrTick; Path; Frame; share-sink;
  _↠[_]_; scan-f; take-f; thru-outer; from-inner; mergeAllᵒ; lookupNode; mergeAll-st; echoᵗ; RegId; RegRow; AtFloor; atDyn)
open import Rx.Evaluator.Domain using (foldPath⇓; fold-root; fold-step; stepFrame⇓; step-map; chainStep⇓; chain-step)
open import SExp.Syntax  using (Kinds; plainᵏ; plainᵗ; emitᵗ; sharedᵏ)
open import SExp.InstEmit using (instEmitᵗ)
open import SExp.InstEmit.Decode using (decodeEmits)
open import SExp.Plain   using (plainValues)
open import Batchable.Inst-Extract using (instExtract)
open import Simulation.Lockstep using (concat-++; values-++; decode-++; extract-++)
open import Simulation.Schedules using (HeadOf)
open import Simulation.Stores using (V; EmitRel; Lifts; Src; SrcPair; sharedEq; PathRel; root~; sink~; map~; scan~; take~; takeWhile~;
  outerElem~; outerExplode~; inner~; lane~; deferInner~; InputBlock; RowRel; cold~; defer~; RegRel; Partners; Store)
open import Simulation.Walk using (readᴾ; readᴵ)

readᴾ-++ : ∀ {n} {Γ : Ctx n} {t} (xs ys : Stream Γ t) → readᴾ (xs ++ ys) ≡ readᴾ xs ++ readᴾ ys
readᴾ-++ xs ys = trans (cong plainValues (concat-++ xs ys)) (values-++ (concat xs) (concat ys))

readᴵ-++ : ∀ {m} {Γ′ : Ctx m} {t} (xs ys : Stream Γ′ (instEmitᵗ uniqᵗ t)) → readᴵ (xs ++ ys) ≡ readᴵ xs ++ readᴵ ys
readᴵ-++ xs ys =
  trans (cong (λ z → instExtract (decodeEmits z)) (concat-++ xs ys))
 (trans (cong instExtract (decode-++ (concat xs) (concat ys)))
        (extract-++ (decodeEmits (concat xs)) (decodeEmits (concat ys))))

-- a minted source's chain, as the registration it was read from
dynRow : ∀ {n} {Γ : Ctx n} {t} (a : Arrival Γ) → RegId × AtFloor Γ (arrTy a) t → RegRow Γ t
dynRow a (rid , lo , p) = rid , atDyn (Arrival.source a) lo , (arrTy a , p)

-- A CHAIN PAIR THE PASS HAS NOT REACHED: cut on both sides, or on
-- neither and partnered by the registries' relation
Paired : ∀ {n} {Γ : Ctx n} {t} {κ : Kinds n} {π NP NI LP LI rs rs′}
       → RegRel κ π {t} NP NI LP LI rs rs′ → List RegId → List RegId → (a : Arrival Γ) (a′ : Arrival (plainᵏ Γ κ))
       → RegId × AtFloor Γ (arrTy a) t → RegId × AtFloor (plainᵏ Γ κ) (arrTy a′) (emitᵗ t) → Set
Paired {κ = κ} rr CP CI a a′ c c′ =
    (any (_≡ᵇ proj₁ c) CP ≡ true × any (_≡ᵇ proj₁ c′) CI ≡ true)
  ⊎ (any (_≡ᵇ proj₁ c) CP ≡ false × any (_≡ᵇ proj₁ c′) CI ≡ false
     × Partners κ _ _ _ _ _ rr (dynRow a c) (dynRow a′ c′))

-- the fold a chain step runs
unchain : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {a : Arrival Γ} {vs fin x sched st r}
        → chainStep⇓ {e = e} a vs fin x sched st r → foldPath⇓ (arrTick a) (proj₂ x) vs fin sched st r
unchain (chain-step d) = d

module _ {n} {Γ : Ctx n} (κ : Kinds n) where

  -- WHAT A GROUP OF EMITS CARRIES: each emit's values in turn, the
  -- plain group they make joined
  data Carries {s} : List (Val (plainᵏ Γ κ) (emitᵗ s)) → List (Val Γ s) → Set where
    []  : Carries [] []
    _∷_ : ∀ {e′ es′ ws vs} → EmitRel κ s e′ ws → Carries es′ vs → Carries (e′ ∷ es′) (ws ++ vs)

  carries-map : ∀ {s u} {G′ : Val (plainᵏ Γ κ) (emitᵗ s) → Val (plainᵏ Γ κ) (emitᵗ u)} {f : Val Γ s → Val Γ u}
              → Lifts κ s u G′ (map f) → ∀ {es vs} → Carries es vs → Carries (map G′ es) (map f vs)
  carries-map L []                        = []
  carries-map {f = f} L (_∷_ {e′ = e′} {ws = ws} {vs = vs} r b) =
    subst (Carries _) (sym (map-++ f ws vs)) (proj₁ (L e′ ws r) ∷ carries-map L b)

  -- THE VALUE A POPPED SOURCE HANDS ITS CHAINS, on both sides: the head
  -- of each partnered source's pending list, at the row's source
  data Head (src src′ : ℕ) : ∀ {u u′} → List (Val Γ u) → List (Val (plainᵏ Γ κ) u′) → Set where
    head : ∀ {l l′ a a′} → Src κ l l′ → HeadOf l a → HeadOf l′ a′
         → Arrival.source a ≡ src → Arrival.source a′ ≡ src′
         → Head src src′ (arrVal a ∷ []) (arrVal a′ ∷ [])

  -- the related values at the root: the emits' payloads in order
  postulate
    root-values : ∀ {t es vs} → Carries {t} es vs → ∀ fin
      → Pointwise (λ x w → V κ t (proj₂ x) w)
          (readᴵ ((map valueᵖ es ++ (if fin then completeᵖ ∷ [] else [])) ∷ []))
          (readᴾ ((map valueᵖ vs ++ (if fin then completeᵖ ∷ [] else [])) ∷ []))

  module _ {t} {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)} where

    St : Sched Γ → EvalSt ep → Sched (plainᵏ Γ κ) → EvalSt ei → Set
    St = Store κ

    -- the chains not reached stay paired
    Keeps : ∀ {sP stP sI stI sP₁ stP₁ sI₁ stI₁}
          → St sP stP sI stI → St sP₁ stP₁ sI₁ stI₁ → Set
    Keeps {stP = stP} {stI = stI} {stP₁ = stP₁} {stI₁ = stI₁} S S₁ =
      ∀ {a a′ chs chs′}
      → Pointwise (Paired (Store.rows S) (EvalSt.cancelled stP) (EvalSt.cancelled stI) a a′) chs chs′
      → Pointwise (Paired (Store.rows S₁) (EvalSt.cancelled stP₁) (EvalSt.cancelled stI₁) a a′) chs chs′

    -- WHAT A PASS KEEPS: related stores after, the unreached chains
    -- paired, and related values sent rootward
    record After {sP stP sI stI} (S : St sP stP sI stI)
                 (rP : Stream Γ t × Sched Γ × EvalSt ep)
                 (rI : Stream (plainᵏ Γ κ) (emitᵗ t) × Sched (plainᵏ Γ κ) × EvalSt ei) : Set where
      constructor after
      field
        store  : Store κ (proj₁ (proj₂ rP)) (proj₂ (proj₂ rP)) (proj₁ (proj₂ rI)) (proj₂ (proj₂ rI))
        keeps  : Keeps S store
        values : Pointwise (λ x w → V κ t (proj₂ x) w) (readᴵ (proj₁ rI)) (readᴾ (proj₁ rP))

    -- one pass, then another from where it left the stores
    _⨾_ : ∀ {sP stP sI stI} {S : St sP stP sI stI} {o₁ sP₁ stP₁ i₁ sI₁ stI₁ rP rI}
        → (A : After S (o₁ , sP₁ , stP₁) (i₁ , sI₁ , stI₁)) → After (After.store A) rP rI
        → After S (o₁ ++ proj₁ rP , proj₂ rP) (i₁ ++ proj₁ rI , proj₂ rI)
    _⨾_ {o₁ = o₁} {i₁ = i₁} {rP = rP} {rI = rI} (after _ k₁ v₁) (after s₂ k₂ v₂) =
      after s₂ (λ {a} {a′} x → k₂ {a} {a′} (k₁ {a} {a′} x))
        (subst₂ (Pointwise (λ x w → V κ t (proj₂ x) w)) (sym (readᴵ-++ i₁ (proj₁ rI))) (sym (readᴾ-++ o₁ (proj₁ rP)))
                (++⁺ v₁ v₂))

    -- WHAT AN ARM HANDS BACK: the pass so far, and the rest of the impl
    -- fold standing on a tail related to the plain one's
    data Arm {sP stP sI stI} (S : St sP stP sI stI) (now : Tick) (oP : Stream Γ t) (sP₁ : Sched Γ) (stP₁ : EvalSt ep)
             {ℓ u} (p : Path Γ ℓ u t) (vs : List (Val Γ u)) (fin : Bool)
           : Stream (plainᵏ Γ κ) (emitᵗ t) × Sched (plainᵏ Γ κ) × EvalSt ei → Set where
      arm : ∀ {ℓ′} {q : Path (plainᵏ Γ κ) ℓ′ (emitᵗ u) (emitᵗ t)} {oI es sI₁ stI₁ rI}
          → (A : After S (oP , sP₁ , stP₁) (oI , sI₁ , stI₁))
          → PathRel κ (Store.π (After.store A)) (EvalSt.nodes stP₁) (EvalSt.nodes stI₁) p q
          → Carries es vs
          → foldPath⇓ now q es fin sI₁ stI₁ rI
          → Arm S now oP sP₁ stP₁ p vs fin (oI ++ proj₁ rI , proj₂ rI)

    -- two related paths keep the pass
    Pass : ∀ {lo lo′ s} → Path Γ lo s t → Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t) → Set
    Pass p q =
      ∀ {now vs es fin sP stP sI stI rP rI} (S : St sP stP sI stI)
      → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q → Carries es vs
      → foldPath⇓ now p vs fin sP stP rP → foldPath⇓ now q es fin sI stI rI
      → After S rP rI

    -- one plain frame and the impl run its constructor pairs it with
    Steps : ∀ {lo lo′ ℓ s u} → Frame Γ s u → lo ≤ ℓ → Path Γ ℓ u t → Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t) → Set
    Steps f h p Q =
      ∀ {now vs es fin sP stP sI stI oP vs₁ fin₁ sP₁ stP₁ rI} (S : St sP stP sI stI)
      → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (f ↠[ h ] p) Q → Carries es vs
      → stepFrame⇓ now f p vs fin sP stP (oP , vs₁ , fin₁ , sP₁ , stP₁)
      → foldPath⇓ now Q es fin sI stI rI
      → Arm S now oP sP₁ stP₁ p vs₁ fin₁ rI

    -- ONE LEAF PER PLAIN FRAME A CONSTRUCTOR STARTS WITH.  A count and a
    -- test are one frame apart in what they cut on; an outer's two
    -- constructors and an inner's three are split once their arm is the
    -- riskiest.
    postulate
      -- a share's subject, fanning the group out to every reader
      sink-pass     : ∀ {lo lo′} {i : Fin n} {h : lo ≤ toℕ i} {h′ : lo′ ≤ toℕ (n ↑ʳ i)} (sh : lookup κ i ≡ sharedᵏ)
                    → Pass (share-sink i h)
                           (subst (λ u → Path (plainᵏ Γ κ) lo′ u (emitᵗ t)) (sharedEq {Γ = Γ} κ i sh) (share-sink (n ↑ʳ i) h′))
      scan-arm      : ∀ {lo lo′ ℓ s u} {F : FnClo Γ (u ×ᵗ s) u} {k} {h : lo ≤ ℓ} {p : Path Γ ℓ u t} {Q : Path (plainᵏ Γ κ) lo′ _ _}
                    → Steps (scan-f F k) h p Q
      take-arm      : ∀ {lo lo′ ℓ s} {k} {h : lo ≤ ℓ} {p : Path Γ ℓ s t} {Q : Path (plainᵏ Γ κ) lo′ _ _}
                    → Steps (take-f nothing k) h p Q
      takeWhile-arm : ∀ {lo lo′ ℓ s} {P k} {h : lo ≤ ℓ} {p : Path Γ ℓ s t} {Q : Path (plainᵏ Γ κ) lo′ _ _}
                    → Steps (take-f (just P) k) h p Q
      -- an outer's elements, each inner a sync outer hands the flattener
      -- subscribed before the step returns: the walk, reached from a pass
      outer-arm     : ∀ {lo lo′ ℓ u} {op m} {h : lo ≤ ℓ} {p : Path Γ ℓ u t} {Q : Path (plainᵏ Γ κ) lo′ _ _}
                    → Steps (thru-outer op m) h p Q
      inner-arm     : ∀ {lo lo′ ℓ u} {op m j} {h : lo ≤ ℓ} {p : Path Γ ℓ u t} {Q : Path (plainᵏ Γ κ) lo′ (emitᵗ u) _}
                    → Steps (from-inner op m j) h p Q

    mutual
      path-pass : ∀ {lo lo′ s} {p : Path Γ lo s t} {q : Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t)} → Pass p q
      path-pass S root~ b (fold-root {fin = fin}) fold-root = after S (λ x → x) (root-values b fin)
      path-pass S r@(sink~ sh) b dP dI = sink-pass sh S r b dP dI
      path-pass S (map~ L r) b (fold-step step-map dP) (fold-step step-map dI) = path-pass S r (carries-map L b) dP dI
      path-pass S r@(scan~ _ _ _ _ _ _) b (fold-step d dP) dI = resume (scan-arm S r b d dI) dP
      path-pass S r@(take~ _ _ _ _ _ _ _ _) b (fold-step d dP) dI = resume (take-arm S r b d dI) dP
      path-pass S r@(takeWhile~ _ _ _ _ _ _) b (fold-step d dP) dI = resume (takeWhile-arm S r b d dI) dP
      path-pass S r@(outerElem~ _ _) b (fold-step d dP) dI = resume (outer-arm S r b d dI) dP
      path-pass S r@(outerExplode~ _ _) b (fold-step d dP) dI = resume (outer-arm S r b d dI) dP
      path-pass S r@(inner~ _ _ _) b (fold-step d dP) dI = resume (inner-arm S r b d dI) dP
      path-pass S r@(lane~ _ _) b (fold-step d dP) dI = resume (inner-arm S r b d dI) dP
      path-pass S r@(deferInner~ _ _ _ _ _ _) b (fold-step d dP) dI = resume (inner-arm S r b d dI) dP

      resume : ∀ {sP stP sI stI} {S : St sP stP sI stI} {now oP sP₁ stP₁ ℓ u} {p : Path Γ ℓ u t} {vs fin rP rI}
             → Arm S now oP sP₁ stP₁ p vs fin rI → foldPath⇓ now p vs fin sP₁ stP₁ rP
             → After S (oP ++ proj₁ rP , proj₂ rP) rI
      resume (arm A r b dI) dP = A ⨾ path-pass (After.store A) r b dP dI

    -- THE TWO ROWS A MINTED SOURCE'S CHAINS CAN BE.  A cold read's impl
    -- chain runs its input block before the path its partner runs; a
    -- deferred hop's subscribes the body on both sides.
    postulate
      block-arm : ∀ {sP stP sI stI} (S : St sP stP sI stI) {src src′ s} {vs : List (Val Γ s)} {vs′ : List (Val (plainᵏ Γ κ) (plainᵗ s))}
                → Head src src′ {s} {plainᵗ s} vs vs′ → SrcPair κ (Sched.live sP) (Sched.live sI) src src′
                → ∀ {lo′ ℓ ℓ′} {p : Path Γ ℓ s t} {full : Path (plainᵏ Γ κ) lo′ (plainᵗ s) (emitᵗ t)}
                    {q : Path (plainᵏ Γ κ) ℓ′ (emitᵗ s) (emitᵗ t)}
                → InputBlock κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (plainᵗ s) full q
                → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                → ∀ {now fin rI} → foldPath⇓ now full vs′ fin sI stI rI
                → Arm S now [] sP stP p vs fin rI
      hop-arm   : ∀ {sP stP sI stI} (S : St sP stP sI stI) {src src′ u} {vs : List (Val Γ (echoᵗ u))} {vs′ : List (Val (plainᵏ Γ κ) (echoᵗ (emitᵗ u)))}
                → Head src src′ {echoᵗ u} {echoᵗ (emitᵗ u)} vs vs′ → SrcPair κ (Sched.live sP) (Sched.live sI) src src′
                → ∀ {nid nid′} → (nid , nid′ ∷ []) ∈ Store.π S
                → lookupNode nid (EvalSt.nodes stP) ≡ just (mergeAll-st {t = u} nothing 0 [] false)
                → lookupNode nid′ (EvalSt.nodes stI) ≡ just (mergeAll-st {t = emitᵗ u} nothing 0 [] false)
                → ∀ {ℓ ℓ′ lo′} {h′ : lo′ ≤ ℓ′} {p : Path Γ ℓ u t} {q : Path (plainᵏ Γ κ) ℓ′ (emitᵗ u) (emitᵗ t)}
                → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q
                → ∀ {now fin oP vs₁ fin₁ sP₁ stP₁ rI}
                → stepFrame⇓ now (thru-outer mergeAllᵒ nid) p vs fin sP stP (oP , vs₁ , fin₁ , sP₁ , stP₁)
                → foldPath⇓ now (thru-outer mergeAllᵒ nid′ ↠[ h′ ] q) vs′ fin sI stI rI
                → Arm S now oP sP₁ stP₁ p vs₁ fin₁ rI

    -- a minted source's partnered chain, by the row the store pairs it with
    row-pass : ∀ {sP stP sI stI} (S : St sP stP sI stI) {src src′ u u′} {vs : List (Val Γ u)} {vs′ : List (Val (plainᵏ Γ κ) u′)}
             → Head src src′ {u} {u′} vs vs′
             → ∀ {rid rid′ lo lo′} {p : Path Γ lo u t} {p′ : Path (plainᵏ Γ κ) lo′ u′ (emitᵗ t)}
             → RowRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (Sched.live sP) (Sched.live sI)
                 (rid , atDyn src lo , (u , p)) (rid′ , atDyn src′ lo′ , (u′ , p′))
             → ∀ {now fin rP rI} → foldPath⇓ now p vs fin sP stP rP → foldPath⇓ now p′ vs′ fin sI stI rI
             → After S rP rI
    row-pass S hd (cold~ sp blk r refl) dP dI = resume (block-arm S hd sp blk r dI) dP
    row-pass S hd (defer~ sp k nP nI r refl) (fold-step d dP) dI = resume (hop-arm S hd sp k nP nI r d dI) dP
