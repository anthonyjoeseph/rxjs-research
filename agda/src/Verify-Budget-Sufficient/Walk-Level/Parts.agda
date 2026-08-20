-- THE WALK'S SHELF — the proven lemmas its clauses spend, none of them
-- mutual with the dispatch.  They consume the dispatch's vocabulary as
-- finished facts and hand back finished facts, which is an import
-- relation and not a cycle; the checker agrees, and that is what lets
-- them sit below the block instead of inside it.
--
-- The split is the same cost argument the statement module's header
-- makes: a focused check of one dispatch member should not re-pay for
-- eight hundred lines of lemma it merely calls.  Nothing here changes,
-- and every name is re-exported `public` upward, so the move is
-- invisible to every consumer.
--
-- WHAT BELONGS HERE: a lemma with a body that the dispatch (or a
-- sibling on this shelf) applies.  A CLAUSE LEAF does not — it is a
-- postulate, its home is the statement module, and putting one here
-- would only mean the statement module's postulate block no longer
-- reads as the complete leaf inventory.

module Verify-Budget-Sufficient.Walk-Level.Parts where

open import Data.Bool    using (Bool; T; true; false; _∨_; _∧_; not; if_then_else_)
open import Data.Nat     using (ℕ; zero; suc; _+_; _*_; _^_; _≤_; _<_;
                                _≤ᵇ_; _<ᵇ_; _≡ᵇ_; z≤n; s≤s)
open import Data.List    using (List; []; _∷_; _++_; length; map)
open import Data.Unit    using (⊤; tt)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; ≤-pred;
                                       m≤m+n; m≤n+m; n≤1+n;
                                       +-suc; +-assoc; +-comm;
                                       +-mono-≤; +-monoʳ-≤; +-monoˡ-≤;
                                       *-mono-≤; *-monoʳ-≤;
                                       +-identityʳ;
                                       m≤m⊔n; m≤n⊔m; ≤⇒≤ᵇ; ≤ᵇ⇒≤)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Bool.ListAction using (all; any)
open import Data.Fin     using (Fin; toℕ)
open import Data.Vec     using (Vec; lookup)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Relation.Nullary using (yes; no)

open import Rx.Prim      using (Tick; Id; Source; init; value; close;
                                complete; handoff; exhausted; dried;
                                cut; cutPending; subscribe;
                                InstEmit; InstEvent; _at_from_as_;
                                Gas; g0; gs; gasPad; ObservableInput; hot; cold)
open import Rx.Exp       using (Ty; obs; natᵗ; _×ᵗ_; Ctx; Closed; Val; Exp; Tm; Fn;
                                inputsBelowᵉ; isData;
                                _≟ᵗ_;
                                sizeᵉ; sizeᵗ; sizeᵛ; syncSizeᵉ;
                                shellSizeᵉ; innerᵉ;
                                input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ;
                                mergeAllᵉ; concatAllᵉ; switchAllᵉ; exhaustAllᵉ;
                                μᵉ; varᵉ; deferᵉ; unfoldμ; applyFn; evalTm)
open import Rx.Frame-Width using (dWᵉ; pWᵉ; pWᵛ)
open import Rx.Hop-Depth using (hopDᵉ; hopDᵗ; hopDᵛ; pmᵗ; hopD-unfoldμ)
open import Rx.Slot-Hop  using (slotHop; slotHop-fix)
open import Rx.Evaluator using (Sched; EvalSt; Slots; Slot; shared; scripted;
                                RegId; Chain;
                                memberSource; Path; root; share-sink; _↠_;
                                Stream; subscribeE; sharedConnect;
                                subscribeAll; AllOp;
                                mergeᵒ; concatᵒ; switchᵒ; exhaustᵒ;
                                NodeState; merge-st; concat-st;
                                switch-st; exhaust-st; scan-st; take-st; scan-f;
                                splitBurst; hasDry; dryEvent;
                                burstCompleted; sharedPlumb; dropSource;
                                sched-init; st-init; budgetAt; slotsSize;
                                opIterD; fIterD; fLvlD; sLvlD; sIterD; sizeAt;
                                sLvlD-suc; opIterD-suc; sIterD-suc; fLvlD-suc; fLvl; widAt;
                                Frame; thru-outer; from-inner;
                                pushBurst; stepFrame;
                                subscribeInner; splitEvents; retagEvents;
                                thruConsume; thruWalk; thruWrap;
                                mergeBump; switchKill; cutThrough; sweepLive;
                                lookupNode; setNode; pathHasNode; LiveSource;
                                sameSource; installNode; NodeId; register; mintNode)

-- the wet stratum: INV?, dBound, hasAtLeast, regsLen?, pathLen, the gas
-- edges, sizeCapAt, capsAt/capsH/frameStep/Caps (via .Caps), the
-- Keeps ring, and every companion the core is narrowed over
open import Verify-Budget-Sufficient.Wet
-- the caps face: only the five predicates the statement reads there
open import Verify-Budget-Sufficient.Caps-Face
  using (capsOK?; burstCaps?; burstCount?; pathSz?; slotsCaps?; nest;
         widNode; merge-step; concat-step; switch-step; exhaust-step;
         frameSz?; capsOK?-mono; capsOK?-setNode; capsOK?-nextNode;
         pathSz?-⊑; frameStep-chain-suc; frameStep-⊑-+;
         valCaps?; valsCaps?; eventCaps?; valCountᵉ; frameBud;
         mapValue-caps; valsCaps?-widen; finList-caps;
         splitEvents-valsCaps; splitEvents-bk-caps; burstCaps?-widen;
         capsOK?-mergeBump; switchKill-caps; switchKill-closes-caps;
         lookupNode-caps; capsOK?-nodeSz; capsOK?-nodeWid;
         thruWrap-caps; mList?; mList?-head; mList?-tail; mList?-keeps;
         valsCaps→mList-strict; splitBurst-vals-caps; splitBurst-bk-caps;
         widNode-push; valCaps?-size; valCaps?-wid; eventsCaps?-widen;
         frameStep-size-strict-suc;
         capsOK?-regs; pathSz?-len;
         slotsCaps?-capsAt; capsOK?-parts)
open import Verify-Budget-Sufficient.Psi-Split
-- the chain-charge algebra subscribeE-caps' own *All head spends
open import Verify-Budget-Sufficient.Caps-Chain
  using (chain-desc; op-step; burst-index; burst-nil; burst-step;
         op-step-mu; quad-arith;
         op-desc; push-desc; frame-desc; tail-desc;
         walk-desc; inner-desc;
         inner-nil; inner-step; walk-nil;
         frame-step; walk-index; queue-push)
open import Verify-Budget-Sufficient.Caps-Sadd
  using (walk-step-suc)
-- the transformer monotonicity/inflation family, cited directly by the
-- loop faces' ceiling conversions
open import Verify-Budget-Sufficient.Caps
  using (opIterD-mono; sIterD-mono; sLvlD-infl; sIterD-infl;
         sLvlD-mono; opIterD-infl; fIterD-infl;
         B2-cReg≤cSize; frameStep-reg≤size;
         capsAt-base-size)
-- proven projections and per-emit plumbing off the caps push face —
-- pieces, never the face itself (the wet twin re-walks its skeleton
-- so both halves share one witness)
open import Verify-Budget-Sufficient.Subscribe-Face
  using (unfoldμ-caps; subscribeE-caps; countLen; countVals; countIn; valsOf; pushEmit-count;
         pushBurst-len; retagEvents-caps;
         burstCount?-widen; burstCount?-tail;
         thruWrap-vals; splitBurst-len; mul-fits; valsIn; valsLen;
         lenWiden; frameStep-+suc; concat-fits)
open import Verify-Budget-Sufficient.Hop-Spine-Face
  using (burstHopSpn?; burstHopSpn-cap; burstHopSpnH?; burstHopSpnH-headline;
         burstHopSpnH-intro; scanSeed-hopSpn)
open import Verify-Budget-Sufficient.Hop-Spine-Push
  using (scanAccSpn?; nodeAccSpn?; nodeAccSpn?-scan; pushBurst-scan-hopSpn)
open import Verify-Budget-Sufficient.Caps-Depth
  using (depthE; depthAll; depthBurst; depthFrame; depthInner;
         depthConsume; depthWalk; depthSlot; depthConn)
open import Verify-Budget-Sufficient.Caps-Nest
  using (nest-keeps; mu-step)
open import Verify-Budget-Sufficient.Op-Budget
  using (opIterD-dominated)
open import Verify-Budget-Sufficient.Node-Fresh
  using (mint-install-survives)
open import Verify-Budget-Sufficient.Walk-Level.Statement public


any-++-false : ∀ {A : Set} (p : A → Bool) (xs ys : List A) →
  any p xs ≡ false → any p ys ≡ false → any p (xs ++ ys) ≡ false
any-++-false p []       ys hx hy = hy
any-++-false p (x ∷ xs) ys hx hy with ∨-false (p x) (any p xs) hx
... | px , pxs = cong₂ _∨_ px (any-++-false p xs ys pxs hy)

-- and the hop tests weaken upward in the hop index, F fixed
hopDev?-widen : ∀ {n} {Γ : Ctx n} {u} (F : ℕ) (η : Fin n → ℕ) (r r′ : ℕ) (ev : InstEvent (Val Γ u)) →
  r ≤ r′ → hopDev? F η r ev ≡ true → hopDev? F η r′ ev ≡ true
hopDev?-widen {u = u} F η r r′ (value v) le h = ≤ᵇ-widen (hopDᵛ F η u v) le h
hopDev?-widen F η r r′ (init _)    le h = refl
hopDev?-widen F η r r′ (close _ _) le h = refl
hopDev?-widen F η r r′ (handoff _) le h = refl
hopDev?-widen F η r r′ complete    le h = refl

burstHopD?-widen : ∀ {n} {Γ : Ctx n} {u} (F : ℕ) (η : Fin n → ℕ) (r r′ : ℕ) (str : Stream Γ u) →
  r ≤ r′ → burstHopD? F η r str ≡ true → burstHopD? F η r′ str ≡ true
burstHopD?-widen F η r r′ str le h =
  all-impl (λ em → all (hopDev? F η r)  (InstEmit.events em))
           (λ em → all (hopDev? F η r′) (InstEmit.events em))
           (λ em hem → all-impl (hopDev? F η r) (hopDev? F η r′)
                         (λ ev hev → hopDev?-widen F η r r′ ev le hev)
                         (InstEmit.events em) hem)
           str h

splitEvents-vals-hop : ∀ {n} {Γ : Ctx n} {s u} (F : ℕ) (η : Fin n → ℕ) (r : ℕ)
  (es : List (InstEvent (Val Γ s))) →
  all (hopDev? F η r) es ≡ true →
  all (λ v → hopDᵛ F η s v ≤ᵇ r) (proj₁ (splitEvents {A = Val Γ u} es)) ≡ true
splitEvents-vals-hop F η r [] h = refl
splitEvents-vals-hop {s = s} {u = u} F η r (value v ∷ es) h
  with ∧-true (hopDᵛ F η s v ≤ᵇ r) (all (hopDev? F η r) es) h
... | hv , hes = ∧-intro hv (splitEvents-vals-hop {u = u} F η r es hes)
splitEvents-vals-hop {u = u} F η r (init _ ∷ es) h =
  splitEvents-vals-hop {u = u} F η r es (proj₂ (∧-true _ _ h))
splitEvents-vals-hop {u = u} F η r (close _ _ ∷ es) h =
  splitEvents-vals-hop {u = u} F η r es (proj₂ (∧-true _ _ h))
splitEvents-vals-hop {u = u} F η r (handoff _ ∷ es) h =
  splitEvents-vals-hop {u = u} F η r es (proj₂ (∧-true _ _ h))
splitEvents-vals-hop {u = u} F η r (complete ∷ es) h =
  splitEvents-vals-hop {u = u} F η r es (proj₂ (∧-true _ _ h))

splitEvents-bk-hop : ∀ {n} {Γ : Ctx n} {s u} (F : ℕ) (η : Fin n → ℕ) (r : ℕ)
  (es : List (InstEvent (Val Γ s))) →
  all (hopDev? F η r) (proj₁ (proj₂ (splitEvents {A = Val Γ u} es))) ≡ true
splitEvents-bk-hop F η r []                    = refl
splitEvents-bk-hop {u = u} F η r (value _   ∷ es) = splitEvents-bk-hop {u = u} F η r es
splitEvents-bk-hop {u = u} F η r (init _    ∷ es) = ∧-intro refl (splitEvents-bk-hop {u = u} F η r es)
splitEvents-bk-hop {u = u} F η r (close _ _ ∷ es) = ∧-intro refl (splitEvents-bk-hop {u = u} F η r es)
splitEvents-bk-hop {u = u} F η r (handoff _ ∷ es) = ∧-intro refl (splitEvents-bk-hop {u = u} F η r es)
splitEvents-bk-hop {u = u} F η r (complete  ∷ es) = splitEvents-bk-hop {u = u} F η r es

-- dryness DOES cross the split (close events survive it), so this one
-- is conditional, and the `dried` reason is matched absurd
splitEvents-bk-dry : ∀ {n} {Γ : Ctx n} {s u}
  (es : List (InstEvent (Val Γ s))) →
  any dryEvent es ≡ false →
  any dryEvent (proj₁ (proj₂ (splitEvents {A = Val Γ u} es))) ≡ false
splitEvents-bk-dry []                          h = refl
splitEvents-bk-dry {u = u} (value _          ∷ es) h = splitEvents-bk-dry {u = u} es h
splitEvents-bk-dry {u = u} (init _           ∷ es) h = splitEvents-bk-dry {u = u} es h
splitEvents-bk-dry {u = u} (close _ cut        ∷ es) h = splitEvents-bk-dry {u = u} es h
splitEvents-bk-dry {u = u} (close _ cutPending ∷ es) h = splitEvents-bk-dry {u = u} es h
splitEvents-bk-dry {u = u} (close _ exhausted  ∷ es) h = splitEvents-bk-dry {u = u} es h
splitEvents-bk-dry {u = u} (close _ dried      ∷ es) ()
splitEvents-bk-dry {u = u} (handoff _        ∷ es) h = splitEvents-bk-dry {u = u} es h
splitEvents-bk-dry {u = u} (complete         ∷ es) h = splitEvents-bk-dry {u = u} es h

-- a retagged list is value-free, so the wet tests are unconditional —
-- retagEvents-caps' twins — while dryness again crosses
retagEvents-B : ∀ {n} {Γ : Ctx n} {u} {A : Set} (B Ψ : ℕ)
  (es : List (InstEvent A)) →
  all (eventB? {u = u} B Ψ) (retagEvents {A = A} {B = Val Γ u} es) ≡ true
retagEvents-B B Ψ []               = refl
retagEvents-B B Ψ (value _   ∷ es) = retagEvents-B B Ψ es
retagEvents-B B Ψ (init _    ∷ es) = ∧-intro refl (retagEvents-B B Ψ es)
retagEvents-B B Ψ (close _ _ ∷ es) = ∧-intro refl (retagEvents-B B Ψ es)
retagEvents-B B Ψ (handoff _ ∷ es) = ∧-intro refl (retagEvents-B B Ψ es)
retagEvents-B B Ψ (complete  ∷ es) = ∧-intro refl (retagEvents-B B Ψ es)

retagEvents-hop : ∀ {n} {Γ : Ctx n} {u} {A : Set} (F : ℕ) (η : Fin n → ℕ) (r : ℕ)
  (es : List (InstEvent A)) →
  all (hopDev? {u = u} F η r) (retagEvents {A = A} {B = Val Γ u} es) ≡ true
retagEvents-hop F η r []               = refl
retagEvents-hop F η r (value _   ∷ es) = retagEvents-hop F η r es
retagEvents-hop F η r (init _    ∷ es) = ∧-intro refl (retagEvents-hop F η r es)
retagEvents-hop F η r (close _ _ ∷ es) = ∧-intro refl (retagEvents-hop F η r es)
retagEvents-hop F η r (handoff _ ∷ es) = ∧-intro refl (retagEvents-hop F η r es)
retagEvents-hop F η r (complete  ∷ es) = ∧-intro refl (retagEvents-hop F η r es)

retagEvents-dry : ∀ {A B : Set} (es : List (InstEvent A)) →
  any dryEvent es ≡ false →
  any dryEvent (retagEvents {A = A} {B = B} es) ≡ false
retagEvents-dry []                          h = refl
retagEvents-dry (value _          ∷ es) h = retagEvents-dry es h
retagEvents-dry (init _           ∷ es) h = retagEvents-dry es h
retagEvents-dry (close _ cut        ∷ es) h = retagEvents-dry es h
retagEvents-dry (close _ cutPending ∷ es) h = retagEvents-dry es h
retagEvents-dry (close _ exhausted  ∷ es) h = retagEvents-dry es h
retagEvents-dry (close _ dried      ∷ es) ()
retagEvents-dry (handoff _        ∷ es) h = retagEvents-dry es h
retagEvents-dry (complete         ∷ es) h = retagEvents-dry es h

mapValue-hop : ∀ {n} {Γ : Ctx n} {u} (F : ℕ) (η : Fin n → ℕ) (r : ℕ) (vs : List (Val Γ u)) →
  all (λ v → hopDᵛ F η u v ≤ᵇ r) vs ≡ true →
  all (hopDev? F η r) (map value vs) ≡ true
mapValue-hop F η r [] h = refl
mapValue-hop {u = u} F η r (v ∷ vs) h
  with ∧-true (hopDᵛ F η u v ≤ᵇ r) (all (λ w → hopDᵛ F η u w ≤ᵇ r) vs) h
... | hv , hvs = ∧-intro hv (mapValue-hop F η r vs hvs)

mapValue-dry : ∀ {n} {Γ : Ctx n} {u} (vs : List (Val Γ u)) →
  any dryEvent (map value vs) ≡ false
mapValue-dry []       = refl
mapValue-dry (v ∷ vs) = mapValue-dry vs

finList-hop : ∀ {n} {Γ : Ctx n} {u} (F : ℕ) (η : Fin n → ℕ) (r : ℕ) (b : Bool) →
  all (hopDev? {n = n} {Γ = Γ} {u = u} F η r)
      (if b then complete ∷ [] else []) ≡ true
finList-hop F η r true  = refl
finList-hop F η r false = refl

finList-dry : ∀ {A : Set} (b : Bool) →
  any (dryEvent {A = A}) (if b then complete ∷ [] else []) ≡ false
finList-dry true  = refl
finList-dry false = refl

------------------------------------------------------------------
-- THE LEAF-AND-LOOP KIT — the plumbing the subscribeInner/thruWalk
-- tower's wet conjuncts ride on.  Everything here is a mirror of a
-- proven caps sibling or plain algebra on a definition; none of it is
-- research.  The dry trio (any-dry-++ / splitEvents-nodry /
-- splitBurst-nodry) and the fnCap node lookup moved DOWN from
-- .Burst-Walk (2026-08-14): the leaf's body consumes them and
-- .Burst-Walk sits above this module, so this is their home now —
-- .Burst-Walk imports them back from here.
------------------------------------------------------------------

-- one gas peel at a known gs — hasAtLeast-peel's Σ, specialised to the
-- constructor the leaf's clause has already matched
hasAtLeast-peel-gs : ∀ {g : Gas} {m : ℕ} →
  gs g hasAtLeast suc m → g hasAtLeast m
hasAtLeast-peel-gs (hs h) = h

-- dBound is monotone in the unconnected count and the hop rank —
-- plain algebra on `s + suc V * (r + suc R * U)`
dBound-mono-U : ∀ (V R : ℕ) {U U′} (r s : ℕ) → U ≤ U′ →
  dBound V R U r s ≤ dBound V R U′ r s
dBound-mono-U V R r s hU =
  +-monoʳ-≤ s (*-monoʳ-≤ (suc V) (+-monoʳ-≤ r (*-monoʳ-≤ (suc R) hU)))

-- BOTH POSITIONS AT ONCE, WEAKLY — dBound-mono-r's shape with the summand
-- moving too.  dBound-struct covers this only when s moves STRICTLY, and
-- walk-take-zero needs it at s = 1 against a `suc`, where weak is what
-- holds.  V R U EXPLICIT for the reason dBound-struct's header gives:
-- dBound unfolds through _*_, which matches on its first argument, so
-- implicits in these positions get stuck.
-- EVERY position explicit, r and s included, and that is not tidiness:
-- with them implicit the conclusion has to be unified against an already
-- reduced `dBound`, where `0 + x` has collapsed to `x` and `r := 0` is no
-- longer recoverable — UnsolvedMetaVariables at the call site.
dBound-mono-rs : ∀ (V R U r r′ s s′ : ℕ) → r ≤ r′ → s ≤ s′ →
  dBound V R U r s ≤ dBound V R U r′ s′
dBound-mono-rs V R U r r′ s s′ hr hsz =
  +-mono-≤ hsz (*-monoʳ-≤ (suc V) (+-monoˡ-≤ (suc R * U) hr))

dBound-mono-r : ∀ (V R U : ℕ) {r r′} (s : ℕ) → r ≤ r′ →
  dBound V R U r s ≤ dBound V R U r′ s
dBound-mono-r V R U {r} {r′} s hr =
  +-monoʳ-≤ s (*-monoʳ-≤ (suc V) (+-monoˡ-≤ (suc R * U) hr))

-- the hop face of the splitBurst square, vals half — mirror of
-- splitBurst-vals-B (.Wet/Part1) at the level-free hop predicate
splitBurst-vals-hop : ∀ {n} {Γ : Ctx n} {s u : Ty} (F : ℕ) (η : Fin n → ℕ) (r : ℕ)
  (str : Stream Γ s) → burstHopD? F η r str ≡ true →
  all (λ v → hopDᵛ F η s v ≤ᵇ r) (proj₁ (splitBurst {A = Val Γ u} str)) ≡ true
splitBurst-vals-hop F η r [] h = refl
splitBurst-vals-hop {Γ = Γ} {s = s} {u = u} F η r (em ∷ ems) h =
  all-++-intro _ (proj₁ (splitEvents {A = Val Γ u} (InstEmit.events em))) _
    (splitEvents-vals-hop {u = u} F η r (InstEmit.events em)
       (proj₁ (∧-true (all (hopDev? F η r) (InstEmit.events em))
                      (burstHopD? F η r ems) h)))
    (splitBurst-vals-hop {u = u} F η r ems
       (proj₂ (∧-true (all (hopDev? F η r) (InstEmit.events em))
                      (burstHopD? F η r ems) h)))

-- the dry trio, ex-.Burst-Walk (see the section header)
any-dry-++ : ∀ {A : Set} (xs ys : List (InstEvent A)) →
  any dryEvent xs ≡ false → any dryEvent ys ≡ false →
  any dryEvent (xs ++ ys) ≡ false
any-dry-++ []       ys h₁ h₂ = h₂
any-dry-++ (x ∷ xs) ys h₁ h₂
  with ∨-false (dryEvent x) (any dryEvent xs) h₁
... | e₁ , h₁′ rewrite e₁ = any-dry-++ xs ys h₁′ h₂

splitEvents-nodry : ∀ {n} {Γ : Ctx n} {u} {A : Set}
  (es : List (InstEvent (Val Γ u))) → any dryEvent es ≡ false →
  any (dryEvent {A}) (proj₁ (proj₂ (splitEvents {A = A} es))) ≡ false
splitEvents-nodry []                h = refl
splitEvents-nodry (value v   ∷ es)  h = splitEvents-nodry es h
splitEvents-nodry (init s    ∷ es)  h = splitEvents-nodry es h
splitEvents-nodry (handoff s ∷ es)  h = splitEvents-nodry es h
splitEvents-nodry (complete  ∷ es)  h = splitEvents-nodry es h
-- the reason is CASE-SPLIT rather than rewritten: the hypothesis lives
-- at `Val Γ u` and the goal at `A`, so `dryEvent`'s implicit differs on
-- the two sides and a rewrite cannot bridge them.  Split, and both
-- sides compute; the `dried` arm is absurd, which is the real content
splitEvents-nodry (close s cut        ∷ es) h = splitEvents-nodry es h
splitEvents-nodry (close s cutPending ∷ es) h = splitEvents-nodry es h
splitEvents-nodry (close s exhausted  ∷ es) h = splitEvents-nodry es h
splitEvents-nodry (close s dried      ∷ es) ()

splitBurst-nodry : ∀ {n} {Γ : Ctx n} {u} {A : Set}
  (str : Stream Γ u) → hasDry str ≡ false →
  any (dryEvent {A}) (proj₁ (proj₂ (splitBurst {A = A} str))) ≡ false
splitBurst-nodry []         h = refl
splitBurst-nodry (em ∷ ems) h
  with ∨-false (any dryEvent (InstEmit.events em)) (hasDry ems) h
... | hd , tl =
      any-dry-++ (proj₁ (proj₂ (splitEvents (InstEmit.events em))))
                 (proj₁ (proj₂ (splitBurst ems)))
                 (splitEvents-nodry (InstEmit.events em) hd)
                 (splitBurst-nodry ems tl)

-- a setNode write preserves an `all` whose new entry passes the test —
-- the shared engine of every INV?-through-node-write step below
all-setNode : ∀ {n} {Γ : Ctx n} (P : NodeState Γ → Bool)
  (nid : NodeId) (ns : NodeState Γ) (nodes : List (NodeId × NodeState Γ)) →
  all (λ kv → P (proj₂ kv)) nodes ≡ true → P ns ≡ true →
  all (λ kv → P (proj₂ kv)) (setNode nid ns nodes) ≡ true
all-setNode P nid ns [] h hp = ∧-intro hp refl
all-setNode P nid ns ((k , s) ∷ r) h hp with k ≡ᵇ nid
... | true  = ∧-intro hp (proj₂ (∧-true (P s) (all (λ kv → P (proj₂ kv)) r) h))
... | false = ∧-intro (proj₁ (∧-true (P s) (all (λ kv → P (proj₂ kv)) r) h))
                      (all-setNode P nid ns r
                         (proj₂ (∧-true (P s) (all (λ kv → P (proj₂ kv)) r) h)) hp)

-- INV? through a node write — capsOK?-setNode's wet twin.  Only the
-- two node-reading conjuncts move; registry and slots pass untouched
-- (the record update leaves both fields definitionally in place)
INV?-setNode : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (Ψ B : ℕ) (nid : NodeId) (ns : NodeState Γ)
  (sched : Sched Γ) (st : EvalSt e) →
  boundedNode B ns ≡ true → fnCapNode Ψ ns ≡ true →
  INV? Ψ B sched st ≡ true →
  INV? Ψ B sched (record st { nodes = setNode nid ns (EvalSt.nodes st) }) ≡ true
INV?-setNode Ψ B nid ns sched st bn fn inv =
  ∧-intro (∧-intro liveB
             (all-setNode (boundedNode B) nid ns (EvalSt.nodes st) nodesB bn))
    (∧-intro (∧-intro liveΨ
                (all-setNode (fnCapNode Ψ) nid ns (EvalSt.nodes st) nodesΨ fn))
      (∧-intro (proj₁ (proj₂ (proj₂ parts)))
        (∧-intro (proj₁ (proj₂ (proj₂ (proj₂ parts))))
          (∧-intro (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ parts)))))
                   (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ parts)))))))))
  where
  parts  = INV-parts Ψ B sched st inv
  liveB  = proj₁ (∧-true (all (boundedLive B) (Sched.live sched))
                         (all (λ kv → boundedNode B (proj₂ kv)) (EvalSt.nodes st))
                         (proj₁ parts))
  nodesB = proj₂ (∧-true (all (boundedLive B) (Sched.live sched))
                         (all (λ kv → boundedNode B (proj₂ kv)) (EvalSt.nodes st))
                         (proj₁ parts))
  liveΨ  = proj₁ (∧-true (all (fnCapLive Ψ) (Sched.live sched))
                         (all (λ kv → fnCapNode Ψ (proj₂ kv)) (EvalSt.nodes st))
                         (proj₁ (proj₂ parts)))
  nodesΨ = proj₂ (∧-true (all (fnCapLive Ψ) (Sched.live sched))
                         (all (λ kv → fnCapNode Ψ (proj₂ kv)) (EvalSt.nodes st))
                         (proj₁ (proj₂ parts)))

-- INV? across a node install plus a nextNode mint, lifted one level.
-- Conjunct by conjunct: stBounded?'s live entry transports via liveEq,
-- new-node entry uses boundedNode-widen + all-setNode; fnCapBounded?'s
-- live transports via liveEq, new-node uses all-setNode; the registry
-- conjuncts don't see nodes; the slot conjuncts transport along slotsEq;
-- every B test is ≤ᵇ, upward in B.  The nextNode field is read by NO
-- conjunct (slots and live are the only sched fields INV? touches).
INV?-install : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (Ψ B B′ : ℕ) (nid : NodeId) (ns : NodeState Γ)
  (sched sched′ : Sched Γ) (st : EvalSt e) →
  B ≤ B′ →
  Sched.slots sched′ ≡ Sched.slots sched →
  Sched.live sched′ ≡ Sched.live sched →
  boundedNode B′ ns ≡ true →
  fnCapNode Ψ ns ≡ true →
  INV? Ψ B sched st ≡ true →
  INV? Ψ B′ sched′ (installNode nid ns st) ≡ true
INV?-install Ψ B B′ nid ns sched sched′ st B≤ slotsEq liveEq bn fn inv =
  let parts   = INV-parts Ψ B sched st inv
      stBound = proj₁ parts
      fnCap   = proj₁ (proj₂ parts)
      rl      = proj₁ (proj₂ (proj₂ parts))
      rb      = proj₁ (proj₂ (proj₂ (proj₂ parts)))
      ss      = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ parts))))
      sf      = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ parts))))
      stLive  = proj₁ (∧-true _ _ stBound)
      stNodes = proj₂ (∧-true _ _ stBound)
      fcLive  = proj₁ (∧-true _ _ fnCap)
      fcNodes = proj₂ (∧-true _ _ fnCap)
      liveB′  = subst (λ li → all (boundedLive B′) li ≡ true) (sym liveEq)
                  (all-impl _ _ (λ l → boundedLive-widen B≤ l) (Sched.live sched) stLive)
      nodesB′ = all-setNode (boundedNode B′) nid ns (EvalSt.nodes st)
                  (all-impl _ _ (λ kv → boundedNode-widen B≤ (proj₂ kv))
                             (EvalSt.nodes st) stNodes) bn
      liveΨ′  = subst (λ li → all (fnCapLive Ψ) li ≡ true) (sym liveEq) fcLive
      nodesΨ′ = all-setNode (fnCapNode Ψ) nid ns (EvalSt.nodes st) fcNodes fn
      ss′     = subst (λ sl → (slotsSize sl ≤ᵇ B′) ≡ true) (sym slotsEq)
                  (≤ᵇ-widen (slotsSize (Sched.slots sched)) B≤ ss)
      sf′     = subst (λ sl → (slotsFnCap sl ≤ᵇ Ψ) ≡ true) (sym slotsEq) sf
  in ∧-intro (∧-intro liveB′ nodesB′)
       (∧-intro (∧-intro liveΨ′ nodesΨ′)
         (∧-intro (≤ᵇ-widen (length (EvalSt.registry st)) B≤ rl)
           (∧-intro (regsB?-widen (EvalSt.registry st) B≤ rb)
             (∧-intro ss′ sf′))))

-- merge's counter bump — capsOK?-mergeBump's wet twin, and the same
-- shape: both bounds on a merge-st are `true` outright

-- cutThrough keeps a sublist of the registry, entries verbatim — so
-- every `all` over the registry survives it, and so does its length
-- bound.  cutThrough-regsSz's (.Caps-Face/Part4) generic form
all-cutThrough : ∀ {n} {Γ : Ctx n} {t}
  (P : (RegId × Source × Chain Γ t) → Bool)
  (nid : NodeId) (d : List RegId) (wm : RegId) (dy : List Source)
  (reg : List (RegId × Source × Chain Γ t)) →
  all P reg ≡ true → all P (proj₁ (cutThrough nid d wm dy reg)) ≡ true
all-cutThrough P nid d wm dy [] h = refl
all-cutThrough P nid d wm dy ((rid , src , c) ∷ r) h
  with pathHasNode nid (proj₂ c)
     | all-cutThrough P nid d wm dy r
         (proj₂ (∧-true (P (rid , src , c)) (all P r) h))
... | true  | ih = ih
... | false | ih = ∧-intro (proj₁ (∧-true (P (rid , src , c)) (all P r) h)) ih

-- and its closes carry only cut/cutPending reasons — never `dried` —
-- so the cut is dry-free by construction
cutThrough-closes-nodry : ∀ {n} {Γ : Ctx n} {t}
  (nid : NodeId) (d : List RegId) (wm : RegId) (dy : List Source)
  (reg : List (RegId × Source × Chain Γ t)) →
  any dryEvent (proj₁ (proj₂ (cutThrough {t = t} nid d wm dy reg))) ≡ false
cutThrough-closes-nodry nid d wm dy [] = refl
cutThrough-closes-nodry nid d wm dy ((rid , src , c) ∷ r)
  with pathHasNode nid (proj₂ c) | cutThrough-closes-nodry nid d wm dy r
... | false | ih = ih
... | true  | ih with any (_≡ᵇ rid) d ∧ memberSource src dy
...   | true  = ih
...   | false with any (_≡ᵇ rid) d ∨ (wm ≤ᵇ rid)
...     | true  = ih
...     | false = ih

-- sweepLive keeps a sublist of the live ring, entries verbatim

-- switchAll's cut, wet side: registry filtered (every `all` and the
-- length bound survive), live swept (a sublist), slots and nodes
-- untouched, cancelled unread — switchKill-caps' twin
INV?-switchKill : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (Ψ B : ℕ) (cur : Maybe NodeId) (sched : Sched Γ) (st : EvalSt e) →
  INV? Ψ B sched st ≡ true →
  INV? Ψ B (proj₁ (proj₂ (switchKill cur sched st)))
           (proj₂ (proj₂ (switchKill cur sched st))) ≡ true
INV?-switchKill Ψ B nothing  sched st inv = inv
INV?-switchKill Ψ B (just v) sched st inv =
  ∧-intro (∧-intro (sweepLive-all (boundedLive B) kept (Sched.live sched) liveB)
                   nodesB)
    (∧-intro (∧-intro (sweepLive-all (fnCapLive Ψ) kept (Sched.live sched) liveΨ)
                      nodesΨ)
      (∧-intro lenOK
        (∧-intro (all-cutThrough (λ en → pathB? B Ψ (proj₂ (proj₂ (proj₂ en)))) v
                    (EvalSt.delivered st) (EvalSt.regWatermark st)
                    (EvalSt.dying st) (EvalSt.registry st)
                    (proj₁ (proj₂ (proj₂ (proj₂ parts)))))
          (∧-intro (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ parts)))))
                   (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ parts)))))))))
  where
  parts  = INV-parts Ψ B sched st inv
  kept   = proj₁ (cutThrough v (EvalSt.delivered st) (EvalSt.regWatermark st)
                    (EvalSt.dying st) (EvalSt.registry st))
  liveB  = proj₁ (∧-true (all (boundedLive B) (Sched.live sched))
                         (all (λ kv → boundedNode B (proj₂ kv)) (EvalSt.nodes st))
                         (proj₁ parts))
  nodesB = proj₂ (∧-true (all (boundedLive B) (Sched.live sched))
                         (all (λ kv → boundedNode B (proj₂ kv)) (EvalSt.nodes st))
                         (proj₁ parts))
  liveΨ  = proj₁ (∧-true (all (fnCapLive Ψ) (Sched.live sched))
                         (all (λ kv → fnCapNode Ψ (proj₂ kv)) (EvalSt.nodes st))
                         (proj₁ (proj₂ parts)))
  nodesΨ = proj₂ (∧-true (all (fnCapLive Ψ) (Sched.live sched))
                         (all (λ kv → fnCapNode Ψ (proj₂ kv)) (EvalSt.nodes st))
                         (proj₁ (proj₂ parts)))
  lenOK : (length kept ≤ᵇ B) ≡ true
  lenOK = T⇒≡true (length kept ≤ᵇ B)
            (≤⇒≤ᵇ (≤-trans (cutThrough-len v (EvalSt.delivered st)
                              (EvalSt.regWatermark st) (EvalSt.dying st)
                              (EvalSt.registry st))
                           (≤ᵇ⇒≤ (length (EvalSt.registry st)) B
                              (T-to (proj₁ (proj₂ (proj₂ parts)))))))

switchKill-regsLen : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (ℓ : ℕ) (cur : Maybe NodeId) (sched : Sched Γ) (st : EvalSt e) →
  regsLen? ℓ (EvalSt.registry st) ≡ true →
  regsLen? ℓ (EvalSt.registry (proj₂ (proj₂ (switchKill cur sched st)))) ≡ true
switchKill-regsLen ℓ nothing  sched st h = h
switchKill-regsLen ℓ (just v) sched st h =
  all-cutThrough (λ en → pathLen (proj₂ (proj₂ (proj₂ en))) ≤ᵇ ℓ) v
    (EvalSt.delivered st) (EvalSt.regWatermark st)
    (EvalSt.dying st) (EvalSt.registry st) h

-- REGISTERING KEEPS THE LENGTH LEDGER, given the new path fits.  The
-- sibling of switchKill-regsLen above.
--
-- `register` APPENDS rather than prepends (Evaluator:319 — `registry st
-- ++ (nextReg , src , u , path) ∷ []`), so this is all-++-intro over the
-- old registry and a SINGLETON, not a cons.  Worth saying because the
-- cons reading typechecks nowhere and the shape is invisible from the name.
register-regsLen : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (ℓ : ℕ) (src : Source) (κ : Path Γ u t) (st : EvalSt e) →
  pathLen κ ≤ ℓ →
  regsLen? ℓ (EvalSt.registry st) ≡ true →
  regsLen? ℓ (EvalSt.registry (register src κ st)) ≡ true
register-regsLen ℓ src κ st pℓ h =
  all-++-intro (λ en → pathLen (proj₂ (proj₂ (proj₂ en))) ≤ᵇ ℓ)
    (EvalSt.registry st) _ h
    (∧-intro (T⇒≡true (pathLen κ ≤ᵇ ℓ) (≤⇒≤ᵇ pℓ)) refl)

-- THE regsLen? CONJUNCT AT A SCRIPTED SLOT, for all four shapes.  Split
-- out of input-wet-scripted because it is the one conjunct of the wet
-- five that closes today, and factoring it is what gives register-regsLen
-- a consumer: the other four are still owed by a leaf.
--
-- Two of the four shapes leave the registry alone and spend the
-- hypothesis; the two that REGISTER (hot with an unspent source, and cold
-- with an async tail) are register-regsLen at the source each mints —
-- `toℕ i` for hot, `Sched.nextSource sched` for cold.
input-wet-scripted-regs : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (ℓ : ℕ) (g : Gas) (i : Fin n) (b : Closed Γ (lookup Γ i))
  (κ : Path Γ (lookup Γ i) t) (bid : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e)
  {ok : T (isData (lookup Γ i))}
  (src : ObservableInput (Val Γ (lookup Γ i))) →
  Sched.slots sched i ≡ scripted {ok = ok} src →
  b ≡ inputᶜ i →
  pathLen κ ≤ ℓ →
  regsLen? ℓ (EvalSt.registry st) ≡ true →
  regsLen? ℓ (EvalSt.registry
                (proj₂ (proj₂ (subscribeE g b κ bid now sched st)))) ≡ true
input-wet-scripted-regs ℓ g i b κ bid now sched st (hot asy) slotEq refl pℓ rgs
  with Sched.slots sched i | slotEq
... | .(scripted (hot asy)) | refl
  with memberSource (toℕ i) (EvalSt.completedSources st)
...   | true  = rgs
...   | false = register-regsLen ℓ (toℕ i) κ st pℓ rgs
input-wet-scripted-regs ℓ g i b κ bid now sched st (cold sync []) slotEq refl pℓ rgs
  with Sched.slots sched i | slotEq
... | .(scripted (cold sync [])) | refl = rgs
input-wet-scripted-regs ℓ g i b κ bid now sched st (cold sync (d ∷ ds)) slotEq refl pℓ rgs
  with Sched.slots sched i | slotEq
... | .(scripted (cold sync (d ∷ ds))) | refl =
  register-regsLen ℓ (Sched.nextSource sched) κ st pℓ rgs

-- THE defer CLAUSE, ASSEMBLED.  The leaf owes the eight conjuncts that need
-- the caps twin and the wet predicates; the ninth is register-regsLen at the
-- path the clause actually registers.
--
-- The length arithmetic is the whole content and it is three steps:
-- `syncSizeᵉ (deferᵉ body) = 1` (Rx.Exp) sits in dBound's summand position,
-- so `1 ≤ dBound … ≤ G` by s≤s z≤n; that funds `pathLen κ + 1 ≤ pathLen κ + G
-- ≤ ℓ`; and +-comm turns it into the `suc (pathLen κ) ≤ ℓ` the extended path
-- needs.  installNode touches `nodes` alone (Evaluator:326), so the registry
-- hypothesis passes through unchanged.
walk-defer : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (body : Closed Γ u) → WalkStmt {e = e} (deferᵉ body)
walk-defer body c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j g κ bid now sl sched st
  2≤S 1≤R hCR slEq slC slSz inv szb wdb pC lC nst hidx dpt invW fnC pB
  s2 fS rS ceil lb dmd gas lℓ rgs =
  let (j′ , a₁ , a₂ , a₃ , a₄ , a₅ , a₆ , a₇ , a₈) =
        walk-defer-eight body c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j g κ bid now sl sched st
          2≤S 1≤R hCR slEq slC slSz inv szb wdb pC lC nst hidx dpt invW fnC pB
          s2 fS rS ceil lb dmd gas lℓ rgs
  in j′ , a₁ , a₂ , a₃ , a₄ , a₅ , a₆ , a₇ , a₈
   , register-regsLen ℓ _ (thru-outer mergeᵒ (proj₁ (mintNode sched)) ↠ κ)
       (installNode (proj₁ (mintNode sched)) (merge-st 0 false) st)
       (subst (_≤ ℓ) (+-comm (pathLen κ) 1)
              (≤-trans (+-monoʳ-≤ (pathLen κ) (≤-trans (s≤s z≤n) dmd)) lℓ))
       rgs

-- THE take CLAUSE, ASSEMBLED — and the `zero` arm is PROVEN, not a leaf.
--
-- `subscribeE fuel (takeᵉ count b)` at `evalTm count ≡ zero` is
-- `let (burst , sched₁) = oneShotBurst [] id sched in burst , sched₁ , st`
-- (Evaluator:1441-44), the SAME TERM symbol for symbol as the emptyᵉ clause
-- at Evaluator:1432-34.  So the arm IS walk-empty at a different subscribed
-- expression, and every hypothesis transports the easy way because every
-- measure is SMALLER at emptyᵉ:
--
--   sizeᵉ emptyᵉ = 1 ≤ suc (sizeᵗ cnt + sizeᵉ b)     (Rx.Exp:461,463)
--   syncSizeᵉ likewise                               (Rx.Exp:514,516)
--   dWⱽ … emptyᵉ = 0                                 (Rx.Frame-Width:347)
--   depthE fuel emptyᵉ … = 0                         (.Caps-Depth:219)
--   fnCapᵉ emptyᵉ = 0                                (.Measures:3771)
--   nest e sl cs = syncSizeᵉ e + resid sl cs         (.Caps-Nest:134)
--
-- and `dBound V R U r s = s + suc V * (r + suc R * U)` (.Measures:1936) is
-- monotone in both moving positions by inspection, so the demand hypothesis
-- needs no lemma — `1 ≤ syncSizeᵉ (takeᵉ …)` is `s≤s z≤n` because that clause
-- is literally a `suc`.
--
-- `rewrite ecEq` IS WHAT LETS IT REDUCE, and it is not optional: the
-- evaluator's takeᵉ clause opens `with evalTm count`, so the goal is stuck on
-- that scrutinee until it is known.  Precedent, same evaluator clause and same
-- move: `subscribeE-take0-wf` (.Verify-Well-Formed/Part8:272).
--
-- THE ONE CONJUNCT THAT IS NOT A TRANSPORT is burstHopD?: walk-empty reports
-- it at `hopDᵉ F η emptyᵉ = 0` and this clause is asked for it at
-- `hopDᵉ F η (takeᵉ cnt b) = hopDᵉ F η b` (Rx.Hop-Depth:198,203).  Widening
-- upward is exactly burstHopD?-widen above.
walk-take-zero : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (cnt : Tm Γ [] [] [] natᵗ) (b : Closed Γ u) →
  evalTm cnt ≡ zero → WalkStmt {e = e} (takeᵉ cnt b)
walk-take-zero {u = u} cnt b ecEq c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j g κ bid now sl sched st
  2≤S 1≤R hCR slEq slC slSz inv szb wdb pC lC nst hidx dpt invW fnC pB
  s2 fS rS ceil lb dmd gas lℓ rgs
  rewrite ecEq =
  let (j′ , a₁ , a₂ , a₃ , a₄ , a₅ , a₆ , a₇ , a₈ , a₉) =
        walk-empty c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j g κ bid now sl sched st
          2≤S 1≤R hCR slEq slC slSz inv
          (≤-trans (s≤s z≤n) szb) z≤n pC lC
          (≤-trans (+-monoˡ-≤ _ (s≤s z≤n)) nst)
          (≤-trans (s≤s (s≤s z≤n)) hidx) z≤n
          invW z≤n pB s2 fS rS ceil lb
          (≤-trans (dBound-mono-rs Ŝ R̂ (unconn sl (EvalSt.connectedShares st))
                                   0 (hopDᵉ F (slotHop F sl) b)
                                   1 (syncSizeᵉ (takeᵉ cnt b))
                                   z≤n (s≤s z≤n)) dmd)
          gas lℓ rgs
  in j′ , a₁ , a₂ , a₃ , a₄ , a₅ , a₆
     -- the stream is given EXPLICITLY: left as `_` it is a meta Agda tries
     -- to solve by inverting burstHopD?'s foldr, which hits the inversion
     -- depth limit and (under -W error) fails the build.
     , burstHopD?-widen F (slotHop F sl) 0 (hopDᵉ F (slotHop F sl) b)
         (proj₁ (subscribeE g (emptyᵉ {t = u}) κ bid now sched st)) z≤n a₇
     , a₈ , a₉

-- THE DISPATCH.  Two arms, and the split is the point: the `zero` arm never
-- subscribes, so it owes no push face, while the `suc k` arm mints a node,
-- recurses and pushes.  Keeping them in one postulate hid the free case —
-- "a postulate hides not just unpaid premises but whole free cases"
-- (subscribeE-take0-wf's own header, on this same clause).
walk-take : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (cnt : Tm Γ [] [] [] natᵗ) (b : Closed Γ u) →
  WalkStmt {e = e} (takeᵉ cnt b)
-- NOT a `with`, and the reason is worth keeping: `with evalTm cnt in ecEq`
-- ABSTRACTS the scrutinee out of the goal, so the branch is asked for
-- `subscribeE … | evalWith cnt []` while each leaf's type still says
-- `subscribeE …` — UnequalTerms on `Sched.live`, which reads as a proof
-- error and is really the with-abstraction.  Matching on a FRESH variable
-- inside `go` leaves the goal untouched and needs no telescope spelled out,
-- since the whole statement is `WalkStmt`.  It is also the cheaper shape:
-- a `with` here would abstract over a fully-applied closed goal, which is
-- what the Typing.With cost note warns about.
walk-take {Γ = Γ} {e = e} cnt b = go (evalTm cnt) refl
  where
  go : (m : Val Γ natᵗ) → evalTm cnt ≡ m → WalkStmt {e = e} (takeᵉ cnt b)
  go zero    eq = walk-take-zero cnt b eq
  go (suc k) eq = walk-take-suc  cnt b k eq

-- THE SOURCE HALF, ASSEMBLED.  Both conjuncts are the frame leaf's,
-- lifted from headline to hereditary — free, per `valHopSpn?-intro`.
walk-scan-source : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (f : Fn Γ [] [] [] (u ×ᵗ s) u) (z : Tm Γ [] [] [] u)
  (b : Closed Γ s) → WalkStmtᴴˢ⁰ {e = e} f z b
walk-scan-source f z b c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j g κ bid now sl sched st
  2≤S 1≤R hCR slEq slC slSz inv szb wdb pC lC nst hidx dpt invW fnC pB
  s2 fS rS ceil lb dmd gas lℓ rgs =
  burstHopSpnH-intro F (slotHop F sl) (pmᵗ F 0 f) BND
    (hopDᵉ F (slotHop F sl) b) (proj₁ r)
    (m≤n+m (hopDᵉ F (slotHop F sl) b)
           (hopDᵗ F (slotHop F sl) f + hopDᵗ F (slotHop F sl) z))
    frB
  , accOK
  where
  BND = hopDᵗ F (slotHop F sl) f + hopDᵗ F (slotHop F sl) z
          + hopDᵉ F (slotHop F sl) b
  r = subscribeE g b (scan-f f (proj₁ (mintNode sched)) ↠ κ) bid now
        (proj₂ (mintNode sched))
        (installNode (proj₁ (mintNode sched)) (scan-st (evalTm z)) st)
  frB = walk-scan-source-burst f z b c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j g κ bid now sl sched st
          2≤S 1≤R hCR slEq slC slSz inv szb wdb pC lC nst hidx dpt invW fnC pB
          s2 fS rS ceil lb dmd gas lℓ rgs
  -- THE NODE HALF, no longer a leaf.  `mint-install-survives` (.Node-Fresh)
  -- is exactly this shape — mint, install, subscribe under a frame naming the
  -- minted nid, read the node back — and it holds because a subscribe writes
  -- nothing below the `nextNode` watermark it was handed.  Its own leaf is
  -- the single remaining gap, shared with `scan-node` / `take-node` (.Part3).
  frN = mint-install-survives g b (scan-f f (proj₁ (mintNode sched)) ↠ κ) bid now
          (scan-st (evalTm z)) sched st
  accOK : nodeAccSpn? F (slotHop F sl) (pmᵗ F 0 f) BND _
            (lookupNode (proj₁ (mintNode sched)) (EvalSt.nodes (proj₂ (proj₂ r)))) ≡ true
  accOK rewrite frN =
    trans (nodeAccSpn?-scan F (slotHop F sl) (pmᵗ F 0 f) BND _ (evalTm z))
          (scanSeed-hopSpn F (slotHop F sl) (pmᵗ F 0 f) BND z
            (≤-trans (m≤n+m (hopDᵗ F (slotHop F sl) z) (hopDᵗ F (slotHop F sl) f))
                     (m≤m+n _ (hopDᵉ F (slotHop F sl) b))))

-- THE HOP RECEIPT FOR A SCAN SUBSCRIPTION, ASSEMBLED.  `subscribeE` at a
-- `scanᵉ` is a subscribe followed by a push, and this is that sentence in
-- Agda: `walk-scan-source` above gives the source burst and the freshly
-- installed accumulator, and `pushBurst-scan-hopSpn` (.Hop-Spine-Push,
-- PROVEN) walks the burst through the frame, running `scanVals` per emit
-- and carrying the accumulator across.  The two numeric side conditions
-- are the identity on the multiplier and the first summand of the bound.
walk-scan-hop-spn : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (f : Fn Γ [] [] [] (u ×ᵗ s) u) (z : Tm Γ [] [] [] u)
  (b : Closed Γ s) → WalkStmtᴴˢ {e = e} f z b
walk-scan-hop-spn f z b c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j g κ bid now sl sched st
  2≤S 1≤R hCR slEq slC slSz inv szb wdb pC lC nst hidx dpt invW fnC pB
  s2 fS rS ceil lb dmd gas lℓ rgs =
  proj₁ (pushBurst-scan-hopSpn F (slotHop F sl) (pmᵗ F 0 f) BND
           g bid now f (proj₁ (mintNode sched)) κ
           (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
           ≤-refl (≤-trans (m≤m+n _ _) (m≤m+n _ _))
           (proj₂ src) (proj₁ src))
  where
  BND = hopDᵗ F (slotHop F sl) f + hopDᵗ F (slotHop F sl) z
          + hopDᵉ F (slotHop F sl) b
  r = subscribeE g b (scan-f f (proj₁ (mintNode sched)) ↠ κ) bid now
        (proj₂ (mintNode sched))
        (installNode (proj₁ (mintNode sched)) (scan-st (evalTm z)) st)
  src = walk-scan-source f z b c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j g κ bid now sl sched st
          2≤S 1≤R hCR slEq slC slSz inv szb wdb pC lC nst hidx dpt invW fnC pB
          s2 fS rS ceil lb dmd gas lℓ rgs

-- THE scan CLAUSE, ASSEMBLED.  Nothing is proven here that the two leaves
-- do not already say; the point of the assembly is that it puts the row's
-- risk in ONE of them.  See walk-scan-hop's header for what that one owes.
walk-scan : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (f : Fn Γ [] [] [] (u ×ᵗ s) u) (z : Tm Γ [] [] [] u)
  (b : Closed Γ s) → WalkStmt {e = e} (scanᵉ f z b)
walk-scan f z b c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j g κ bid now sl sched st
  2≤S 1≤R hCR slEq slC slSz inv szb wdb pC lC nst hidx dpt invW fnC pB
  s2 fS rS ceil lb dmd gas lℓ rgs =
  let (j′ , a₁ , a₂ , a₃ , a₄ , a₅ , a₆ , a₇ , a₈) =
        walk-scan-rest f z b c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j g κ bid now sl sched st
          2≤S 1≤R hCR slEq slC slSz inv szb wdb pC lC nst hidx dpt invW fnC pB
          s2 fS rS ceil lb dmd gas lℓ rgs
      -- the frame the burst's SIZE receipt is stated at sits under Ŝ:
      -- a₄ puts j + j′ under opIterD, `lb` puts that under L̂, and
      -- frameStep is monotone in its index, so `ceil` closes it
      Bsz≤F : Caps.cSize (frameStep (j + j′) c) ≤ F
      Bsz≤F = subst (Caps.cSize (frameStep (j + j′) c) ≤_) (sym fS)
                (≤-trans (proj₁ (frameStep-mono-j c 2≤S (≤-trans a₄ lb))) ceil)
  in j′ , a₁ , a₂ , a₃ , a₄ , a₅ , a₆
   , burstHopSpn-cap F Ψ (2 + pmᵗ F 0 f)
       (hopDᵗ F (slotHop F sl) f + hopDᵗ F (slotHop F sl) z
          + hopDᵉ F (slotHop F sl) b)
       (Caps.cSize (frameStep (j + j′) c)) (slotHop F sl)
       (proj₁ (subscribeE g (scanᵉ f z b) κ bid now sched st))
       (s≤s z≤n) Bsz≤F a₆
       (burstHopSpnH-headline F (pmᵗ F 0 f)
          (hopDᵗ F (slotHop F sl) f + hopDᵗ F (slotHop F sl) z
             + hopDᵉ F (slotHop F sl) b)
          (slotHop F sl)
          (proj₁ (subscribeE g (scanᵉ f z b) κ bid now sched st))
          (walk-scan-hop-spn f z b c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j g κ bid now sl sched st
             2≤S 1≤R hCR slEq slC slSz inv szb wdb pC lC nst hidx dpt invW fnC pB
             s2 fS rS ceil lb dmd gas lℓ rgs))
   , a₇ , a₈

switchKill-closes-nodry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (cur : Maybe NodeId) (sched : Sched Γ) (st : EvalSt e) →
  any dryEvent (proj₁ (switchKill {t = t} {e = e} cur sched st)) ≡ false
switchKill-closes-nodry nothing  sched st = refl
switchKill-closes-nodry (just v) sched st =
  cutThrough-closes-nodry v (EvalSt.delivered st) (EvalSt.regWatermark st)
    (EvalSt.dying st) (EvalSt.registry st)

-- the thru-outer wrap passes events and registry through verbatim in
-- every branch — thruWrap-vals' two remaining projections, one lemma
thruWrap-pass : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (op : AllOp) (nid : NodeId) (fin : Bool)
  (r : List (Val Γ u) × List (InstEvent (Val Γ t)) × Sched Γ × EvalSt e) →
  (proj₁ (proj₂ (thruWrap op nid fin r)) ≡ proj₁ (proj₂ r))
  × (EvalSt.registry (proj₂ (proj₂ (proj₂ (proj₂ (thruWrap op nid fin r)))))
       ≡ EvalSt.registry (proj₂ (proj₂ (proj₂ r))))
thruWrap-pass op nid false (vs , bs , sd , st′) = refl , refl
thruWrap-pass mergeᵒ nid true (vs , bs , sd , st′)
  with lookupNode nid (EvalSt.nodes st′)
... | nothing                = refl , refl
... | just (scan-st _)       = refl , refl
... | just (take-st _)       = refl , refl
... | just (merge-st _ _)    = refl , refl
... | just (concat-st _ _ _) = refl , refl
... | just (switch-st _ _)   = refl , refl
... | just (exhaust-st _ _)  = refl , refl
thruWrap-pass concatᵒ nid true (vs , bs , sd , st′)
  with lookupNode nid (EvalSt.nodes st′)
... | nothing                = refl , refl
... | just (scan-st _)       = refl , refl
... | just (take-st _)       = refl , refl
... | just (merge-st _ _)    = refl , refl
... | just (concat-st _ _ _) = refl , refl
... | just (switch-st _ _)   = refl , refl
... | just (exhaust-st _ _)  = refl , refl
thruWrap-pass switchᵒ nid true (vs , bs , sd , st′)
  with lookupNode nid (EvalSt.nodes st′)
... | nothing                = refl , refl
... | just (scan-st _)       = refl , refl
... | just (take-st _)       = refl , refl
... | just (merge-st _ _)    = refl , refl
... | just (concat-st _ _ _) = refl , refl
... | just (switch-st _ _)   = refl , refl
... | just (exhaust-st _ _)  = refl , refl
thruWrap-pass exhaustᵒ nid true (vs , bs , sd , st′)
  with lookupNode nid (EvalSt.nodes st′)
... | nothing                = refl , refl
... | just (scan-st _)       = refl , refl
... | just (take-st _)       = refl , refl
... | just (merge-st _ _)    = refl , refl
... | just (concat-st _ _ _) = refl , refl
... | just (switch-st _ _)   = refl , refl
... | just (exhaust-st _ _)  = refl , refl

-- INV? through the wrap — thruWrap-caps' wet twin.  Every node write
-- re-installs the looked-up payload with only its done-flag moved, and
-- neither wet node bound reads the flags, so each write's bounds are
-- the lookup's own
thruWrap-INV : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (Ψ B : ℕ) (op : AllOp) (nid : NodeId) (fin : Bool)
  (r : List (Val Γ u) × List (InstEvent (Val Γ t)) × Sched Γ × EvalSt e) →
  INV? Ψ B (proj₁ (proj₂ (proj₂ r))) (proj₂ (proj₂ (proj₂ r))) ≡ true →
  INV? Ψ B (proj₁ (proj₂ (proj₂ (proj₂ (thruWrap op nid fin r)))))
           (proj₂ (proj₂ (proj₂ (proj₂ (thruWrap op nid fin r))))) ≡ true
thruWrap-INV Ψ B op nid false (vs , bs , sd , st′) inv = inv
thruWrap-INV Ψ B mergeᵒ nid true (vs , bs , sd , st′) inv
  with lookupNode nid (EvalSt.nodes st′)
... | just (merge-st k od)   =
      INV?-setNode Ψ B nid (merge-st k true) sd st′ refl refl inv
... | nothing                = inv
... | just (scan-st _)       = inv
... | just (take-st _)       = inv
... | just (concat-st _ _ _) = inv
... | just (switch-st _ _)   = inv
... | just (exhaust-st _ _)  = inv
thruWrap-INV Ψ B concatᵒ nid true (vs , bs , sd , st′) inv
  with lookupNode nid (EvalSt.nodes st′)
     | lookupNode-B B Ψ nid (EvalSt.nodes st′)
         (proj₂ (∧-true (all (boundedLive B) (Sched.live sd))
                        (all (λ kv → boundedNode B (proj₂ kv)) (EvalSt.nodes st′))
                        (proj₁ (INV-parts Ψ B sd st′ inv))))
         (proj₂ (∧-true (all (fnCapLive Ψ) (Sched.live sd))
                        (all (λ kv → fnCapNode Ψ (proj₂ kv)) (EvalSt.nodes st′))
                        (proj₁ (proj₂ (INV-parts Ψ B sd st′ inv)))))
... | just (concat-st q act od) | (bn , fn) =
      INV?-setNode Ψ B nid (concat-st q act true) sd st′ bn fn inv
... | nothing                | _ = inv
... | just (scan-st _)       | _ = inv
... | just (take-st _)       | _ = inv
... | just (merge-st _ _)    | _ = inv
... | just (switch-st _ _)   | _ = inv
... | just (exhaust-st _ _)  | _ = inv
thruWrap-INV Ψ B switchᵒ nid true (vs , bs , sd , st′) inv
  with lookupNode nid (EvalSt.nodes st′)
... | just (switch-st cur od) =
      INV?-setNode Ψ B nid (switch-st cur true) sd st′ refl refl inv
... | nothing                = inv
... | just (scan-st _)       = inv
... | just (take-st _)       = inv
... | just (merge-st _ _)    = inv
... | just (concat-st _ _ _) = inv
... | just (exhaust-st _ _)  = inv
thruWrap-INV Ψ B exhaustᵒ nid true (vs , bs , sd , st′) inv
  with lookupNode nid (EvalSt.nodes st′)
... | just (exhaust-st act od) =
      INV?-setNode Ψ B nid (exhaust-st act true) sd st′ refl refl inv
... | nothing                = inv
... | just (scan-st _)       = inv
... | just (take-st _)       = inv
... | just (merge-st _ _)    = inv
... | just (concat-st _ _ _) = inv
... | just (switch-st _ _)   = inv

