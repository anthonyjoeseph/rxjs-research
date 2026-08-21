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
open import Data.Nat     using (ℕ; zero; suc; _+_; _*_; _^_; _⊔_; _≤_; _<_;
                                _≤ᵇ_; _<ᵇ_; _≡ᵇ_; z≤n; s≤s)
open import Data.List    using (List; []; _∷_; _++_; length; map)
open import Data.Unit    using (⊤; tt)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; ≤-pred;
                                       m≤m+n; m≤n+m; n≤1+n;
                                       +-suc; +-assoc; +-comm;
                                       +-mono-≤; +-monoʳ-≤; +-monoˡ-≤;
                                       *-mono-≤; *-monoʳ-≤; *-monoˡ-≤;
                                       *-identityˡ;
                                       +-identityʳ;
                                       m≤m⊔n; m≤n⊔m; ≤⇒≤ᵇ; ≤ᵇ⇒≤)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᵃ)
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
                                sizeᵉ; sizeᵗ; sizeᵛ; syncSizeᵉ; syncSizeᵗ;
                                shellSizeᵉ; innerᵉ;
                                input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ;
                                mergeAllᵉ; concatAllᵉ; switchAllᵉ; exhaustAllᵉ;
                                μᵉ; varᵉ; deferᵉ; unfoldμ; applyFn; evalTm)
open import Rx.Frame-Width using (dWᵉ; dWᵗ; pWᵉ; pWᵛ)
open import Rx.Hop-Depth using (hopDᵉ; hopDᵗ; hopDᵛ; pmᵗ; hopD-unfoldμ)
open import Rx.Slot-Hop  using (slotHop; slotHop-fix)
open import Rx.Evaluator using (Sched; EvalSt; Slots; Slot; shared; scripted;
                                RegId; Chain;
                                memberSource; Path; root; share-sink; _↠_;
                                Stream; subscribeE; sharedConnect;
                                subscribeAll; AllOp;
                                mergeᵒ; concatᵒ; switchᵒ; exhaustᵒ;
                                NodeState; merge-st; concat-st;
                                switch-st; exhaust-st; scan-st; take-st;
                                map-f; scan-f; take-f;
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
                                takeVals;
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
         slotsCaps?-capsAt; capsOK?-parts;
         -- the scan frame's install: the seed is BUILT, so its two node
         -- bounds cost an eval receipt and a level step of their own
         evalSeed-caps; valCaps?-widen; frameStep-mono-j; ⊑ᶜ-trans;
         frameSz?-widen;
         frameStep-+assoc-caps; frameStep-+assoc-burst)
open import Verify-Budget-Sufficient.Psi-Split
-- the chain-charge algebra subscribeE-caps' own *All head spends
open import Verify-Budget-Sufficient.Caps-Chain
  using (chain-desc; op-step; burst-index; burst-nil; burst-step;
         op-step-mu; quad-arith;
         op-desc; op-desc-eval; push-desc; frame-desc; tail-desc;
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
         capsAt-base-size; 1≤pow≤)
-- proven projections and per-emit plumbing off the caps push face —
-- pieces, never the face itself (the wet twin re-walks its skeleton
-- so both halves share one witness)
open import Verify-Budget-Sufficient.Subscribe-Face
  using (unfoldμ-caps; subscribeE-caps; countLen; countVals; countIn; valsOf; pushEmit-count;
         pushBurst-len; retagEvents-caps;
         burstCount?-widen; burstCount?-tail;
         thruWrap-vals; splitBurst-len; mul-fits; valsIn; valsLen;
         lenWiden; frameStep-+suc; concat-fits;
         frameStep-+assoc-count; pushBurst-caps)
open import Verify-Budget-Sufficient.Hop-Spine-Face
  using (burstHopSpn?; burstHopSpn-cap; burstHopSpnH?; burstHopSpnH-headline;
         burstHopSpnH-intro; scanSeed-hopSpn)
open import Verify-Budget-Sufficient.Hop-Spine-Push
  using (scanAccSpn?; nodeAccSpn?; nodeAccSpn?-scan; pushBurst-scan-hopSpn)
open import Verify-Budget-Sufficient.Caps-Depth
  using (depthE; depthAll; depthBurst; depthFrame; depthInner;
         depthConsume; depthWalk; depthSlot; depthConn)
open import Verify-Budget-Sufficient.Caps-Nest
  using (nest-keeps; mu-step; map-step; scan-step; take-step)
open import Verify-Budget-Sufficient.Op-Budget
  using (opIterD-dominated)
open import Verify-Budget-Sufficient.Node-Fresh
  using (mint-install-survives)
-- take's push costs no depth at all: takeDispatch subscribes nothing
open import Verify-Budget-Sufficient.Depth-Compositional
  using (burst-takef-zero)
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
  (g : Gas) (cnt : Tm Γ [] [] [] natᵗ) (b : Closed Γ u) →
  evalTm cnt ≡ zero → WalkStmtAt {e = e} g (takeᵉ cnt b)
walk-take-zero {u = u} g cnt b ecEq c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j κ bid now sl sched st
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

-- THE PER-EMIT WET STEP AT take-f.  `stepFrame … (take-f nid) …` is
-- `takeDispatch nid vals fin sched st (lookupNode nid (EvalSt.nodes st))`
-- (Rx.Evaluator) and NOTHING ELSE: it subscribes nothing, so it spends no
-- gas, no caps level and no depth, which is why B is a parameter here
-- rather than a column.
--
-- The node lookup is pinned by no hypothesis, so the six mismatch arms
-- are discharged from takeDispatch's own catch-all clause — it returns
-- sched and st verbatim and emits nothing, so the invariant IS the
-- hypothesis and the three emission conjuncts are `refl`.  On a
-- `take-st`, both arms hand on `takeVals`' PREFIX; the cutting arm
-- additionally severs the registry through `cutThrough`, sweeps the live
-- ring against what survived, and writes `take-st zero` back, whose two
-- node bounds are `true` outright.
stepTake-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (Ψ B F ℓ r̂ : ℕ) (η : Fin n → ℕ) (g : Gas) (bid : Id) (now : Tick)
  (nid : NodeId) (κ : Path Γ s t) (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  INV? Ψ B sched st ≡ true →
  all (valB? B Ψ s) vals ≡ true →
  all (λ v → hopDᵛ F η s v ≤ᵇ r̂) vals ≡ true →
  regsLen? ℓ (EvalSt.registry st) ≡ true →
  let r = stepFrame g bid now (take-f nid) κ vals fin sched st
  in (INV? Ψ B (proj₁ (proj₂ (proj₂ (proj₂ r))))
            (proj₂ (proj₂ (proj₂ (proj₂ r)))) ≡ true)
   × (all (valB? B Ψ s) (proj₁ r) ≡ true)
   × (all (λ v → hopDᵛ F η s v ≤ᵇ r̂) (proj₁ r) ≡ true)
   × (any dryEvent (proj₁ (proj₂ r)) ≡ false)
   × (regsLen? ℓ (EvalSt.registry (proj₂ (proj₂ (proj₂ (proj₂ r))))) ≡ true)
stepTake-wet {s = s} Ψ B F ℓ r̂ η g bid now nid κ vals fin sched st invW vB vH rgs
  with lookupNode nid (EvalSt.nodes st)
... | nothing                = invW , refl , refl , refl , rgs
... | just (scan-st _)       = invW , refl , refl , refl , rgs
... | just (merge-st _ _)    = invW , refl , refl , refl , rgs
... | just (concat-st _ _ _) = invW , refl , refl , refl , rgs
... | just (switch-st _ _)   = invW , refl , refl , refl , rgs
... | just (exhaust-st _ _)  = invW , refl , refl , refl , rgs
... | just (take-st k) with proj₂ (proj₂ (takeVals k vals))
...   | false =
  INV?-setNode Ψ B nid (take-st (proj₁ (proj₂ (takeVals k vals))))
    sched st refl refl invW
  , takeVals-B B Ψ k vals vB
  , takeVals-all (λ v → hopDᵛ F η s v ≤ᵇ r̂) k vals vH
  , refl
  , rgs
...   | true =
  ∧-intro (∧-intro (sweepLive-all (boundedLive B) kept (Sched.live sched) liveB)
                   (all-setNode (boundedNode B) nid (take-st zero)
                      (EvalSt.nodes st) nodesB refl))
    (∧-intro (∧-intro (sweepLive-all (fnCapLive Ψ) kept (Sched.live sched) liveΨ)
                      (all-setNode (fnCapNode Ψ) nid (take-st zero)
                         (EvalSt.nodes st) nodesΨ refl))
      (∧-intro lenOK
        (∧-intro (all-cutThrough (λ en → pathB? B Ψ (proj₂ (proj₂ (proj₂ en))))
                    nid del wm dy (EvalSt.registry st)
                    (proj₁ (proj₂ (proj₂ (proj₂ parts)))))
          (∧-intro (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ parts)))))
                   (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ parts)))))))))
  , takeVals-B B Ψ k vals vB
  , takeVals-all (λ v → hopDᵛ F η s v ≤ᵇ r̂) k vals vH
  , cutThrough-closes-nodry nid del wm dy (EvalSt.registry st)
  , all-cutThrough (λ en → pathLen (proj₂ (proj₂ (proj₂ en))) ≤ᵇ ℓ)
      nid del wm dy (EvalSt.registry st) rgs
  where
  del    = EvalSt.delivered st
  wm     = EvalSt.regWatermark st
  dy     = EvalSt.dying st
  kept   = proj₁ (cutThrough nid del wm dy (EvalSt.registry st))
  parts  = INV-parts Ψ B sched st invW
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
            (≤⇒≤ᵇ (≤-trans (cutThrough-len nid del wm dy (EvalSt.registry st))
                           (≤ᵇ⇒≤ (length (EvalSt.registry st)) B
                              (T-to (proj₁ (proj₂ (proj₂ parts)))))))

-- THE BURST INDUCTION AT take-f, WET HALF, AND B IS FIXED THROUGHOUT —
-- which is the finding this body encodes rather than describes.
-- `stepFrame … (take-f nid) …` is `takeDispatch` (Rx.Evaluator), and
-- neither of its arms subscribes anything, so the push spends NO caps
-- level: the take clause's four caps conjuncts come off the
-- frame-generic `pushBurst-caps` (PROVEN, .Subscribe-Face) at its own
-- witness, and what is left for a re-walk is exactly the five wet
-- conjuncts at ONE unmoving B.  That is why this is a plain induction
-- and not `pushThru-walk`'s two-hundred-line twin: no widening column.
--
-- The DEAD ROUTE beside `pushBurst-walk` rules that a frame-generic WET
-- push face is FALSE (the hop ledger is frame-specific) and that the
-- repair is one face per frame kind.  This is take's, and take's own
-- output hop index is the IDENTITY — `hopDᵉ V η (takeᵉ c e) = hopDᵉ V η e`
-- (Rx.Hop-Depth) — so r̂ goes in and r̂ comes out, with no factor to pay.
--
-- The per-emit reassembly is `pushBurst`'s own emit shape: back events ++
-- retagged step events ++ mapped values ++ an optional `complete`, so
-- each conjunct is four `all`/`any` facts joined by all-++-intro /
-- any-++-false.  Same skeleton as pushThru-walk's, minus the caps column.
pushTake-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (Ψ B F ℓ r̂ : ℕ) (η : Fin n → ℕ) (g : Gas) (bid : Id) (now : Tick)
  (nid : NodeId) (κ : Path Γ s t) (str : Stream Γ s)
  (sched : Sched Γ) (st : EvalSt e) →
  INV? Ψ B sched st ≡ true →
  burstB? B Ψ str ≡ true →
  burstHopD? F η r̂ str ≡ true →
  hasDry str ≡ false →
  regsLen? ℓ (EvalSt.registry st) ≡ true →
  let r = pushBurst g bid now (take-f nid) κ str sched st
  in (INV? Ψ B (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
   × (burstB? B Ψ (proj₁ r) ≡ true)
   × (burstHopD? F η r̂ (proj₁ r) ≡ true)
   × (hasDry (proj₁ r) ≡ false)
   × (regsLen? ℓ (EvalSt.registry (proj₂ (proj₂ r))) ≡ true)
pushTake-wet Ψ B F ℓ r̂ η g bid now nid κ [] sched st invW bB bH hDry rgs =
  invW , refl , refl , refl , rgs
pushTake-wet {n = n} {Γ = Γ} {s = s} Ψ B F ℓ r̂ η g bid now nid κ (em ∷ ems) sched st
  invW bB bH hDry rgs =
  W1 , ∧-intro EMITB W2 , ∧-intro EMITH W3 , cong₂ _∨_ EMITD W4 , W5
  where
  E    = InstEmit.events em
  sp   = splitEvents {A = Val Γ s} E
  step = stepFrame g bid now (take-f nid) κ (proj₁ sp) (proj₂ (proj₂ sp)) sched st
  sd₁  = proj₁ (proj₂ (proj₂ (proj₂ step)))
  st₁  = proj₂ (proj₂ (proj₂ (proj₂ step)))
  eB   = proj₁ (∧-true _ _ bB)
  eH   = proj₁ (∧-true _ _ bH)
  dSp  = ∨-false (any dryEvent E) (hasDry ems) hDry
  SF   = stepTake-wet Ψ B F ℓ r̂ η g bid now nid κ
           (proj₁ sp) (proj₂ (proj₂ sp)) sched st
           invW
           (splitEvents-vals-B {u = s} B Ψ E eB)
           (splitEvents-vals-hop {u = s} F η r̂ E eH)
           rgs
  S1   = proj₁ SF
  S2   = proj₁ (proj₂ SF)
  S3   = proj₁ (proj₂ (proj₂ SF))
  S4   = proj₁ (proj₂ (proj₂ (proj₂ SF)))
  S5   = proj₂ (proj₂ (proj₂ (proj₂ SF)))
  IH   = pushTake-wet Ψ B F ℓ r̂ η g bid now nid κ ems sd₁ st₁
           S1 (proj₂ (∧-true _ _ bB)) (proj₂ (∧-true _ _ bH)) (proj₂ dSp) S5
  W1   = proj₁ IH
  W2   = proj₁ (proj₂ IH)
  W3   = proj₁ (proj₂ (proj₂ IH))
  W4   = proj₁ (proj₂ (proj₂ (proj₂ IH)))
  W5   = proj₂ (proj₂ (proj₂ (proj₂ IH)))
  EMITB : all (eventB? B Ψ)
              (proj₁ (proj₂ sp) ++ retagEvents (proj₁ (proj₂ step))
                 ++ map value (proj₁ step)
                 ++ (if proj₁ (proj₂ (proj₂ step)) then complete ∷ [] else []))
            ≡ true
  EMITB = all-++-intro (eventB? B Ψ) (proj₁ (proj₂ sp)) _
            (splitEvents-bk-B {u = s} B Ψ E)
            (all-++-intro (eventB? B Ψ) (retagEvents (proj₁ (proj₂ step))) _
               (retagEvents-B B Ψ (proj₁ (proj₂ step)))
               (all-++-intro (eventB? B Ψ) (map value (proj₁ step)) _
                  (mapValue-B B Ψ s (proj₁ step) S2)
                  (finList-B {u = s} B Ψ (proj₁ (proj₂ (proj₂ step))))))
  EMITH : all (hopDev? F η r̂)
              (proj₁ (proj₂ sp) ++ retagEvents (proj₁ (proj₂ step))
                 ++ map value (proj₁ step)
                 ++ (if proj₁ (proj₂ (proj₂ step)) then complete ∷ [] else []))
            ≡ true
  EMITH = all-++-intro (hopDev? F η r̂) (proj₁ (proj₂ sp)) _
            (splitEvents-bk-hop {u = s} F η r̂ E)
            (all-++-intro (hopDev? F η r̂) (retagEvents (proj₁ (proj₂ step))) _
               (retagEvents-hop F η r̂ (proj₁ (proj₂ step)))
               (all-++-intro (hopDev? F η r̂) (map value (proj₁ step)) _
                  (mapValue-hop F η r̂ (proj₁ step) S3)
                  (finList-hop {n = n} {Γ = Γ} {u = s} F η r̂
                     (proj₁ (proj₂ (proj₂ step))))))
  EMITD : any dryEvent
              (proj₁ (proj₂ sp) ++ retagEvents (proj₁ (proj₂ step))
                 ++ map value (proj₁ step)
                 ++ (if proj₁ (proj₂ (proj₂ step)) then complete ∷ [] else []))
            ≡ false
  EMITD = any-++-false dryEvent (proj₁ (proj₂ sp)) _
            (splitEvents-bk-dry {u = s} E (proj₁ dSp))
            (any-++-false dryEvent (retagEvents (proj₁ (proj₂ step))) _
               (retagEvents-dry (proj₁ (proj₂ step)) S4)
               (any-++-false dryEvent (map value (proj₁ step)) _
                  (mapValue-dry (proj₁ step))
                  (finList-dry {A = Val Γ s} (proj₁ (proj₂ (proj₂ step))))))

-- ─── THE map FRAME'S TWO VALUE LEDGERS ──────────────────────────────
-- `stepFrame … (map-f fn) …` applies the fn ONCE per payload and
-- touches nothing else (Rx.Evaluator), so everything the map push face
-- owes about VALUES is these two pointwise liftings over
-- `map (applyFn fn)`.  They are separate on purpose, and the SIZE half
-- is in neither: it never rides this face at all — it is re-supplied at
-- the caller's level from the caps receipt and zipped back through
-- `burstB?-halves` (.Psi-Split).  That is why `applyFn-size`'s
-- capᴱ-shaped exponential never has to be fitted under the level cap.
--
-- map-Ψ moved DOWN from .Burst-Walk, whose `wet-map` was its first
-- consumer and which sits ABOVE this module; the emit-reassembly
-- flavours it rides beside went one further, to .Psi-Split.

map-Ψ : ∀ {n} {Γ : Ctx n} {s u} (Ψ : ℕ) (fn : Fn Γ [] [] [] s u)
  (vs : List (Val Γ s)) →
  caseWᵗ fn ⊔ fnCapᵗ fn ≤ Ψ →
  valsΨ? Ψ vs ≡ true →
  valsΨ? Ψ (map (applyFn fn) vs) ≡ true
map-Ψ Ψ fn []       hfn h = refl
map-Ψ {s = s} Ψ fn (v ∷ vs) hfn h
  with ∧-true (valΨ? Ψ s v) (valsΨ? Ψ vs) h
... | hv , hvs =
  ∧-intro (T⇒≡true _ (≤⇒≤ᵇ (applyFn-fnCap Ψ fn v
             (≤ᵇ⇒≤ (fnCapᵛ s v) Ψ (T-to hv)) hfn)))
          (map-Ψ Ψ fn vs hfn hvs)

-- the hop ledger's lifting.  The per-value STEP is a hypothesis rather
-- than arithmetic here, which keeps the face frame-local: the output
-- index is whatever `hopDᵉ`'s mapᵉ clause says, and the caller is the
-- one holding the source expression that clause mentions.  Its supplier
-- is `hopD-map-emit` (.Measures, PROVEN), whose header calls itself
-- "burstHopD? at the mapᵉ clause, with the arithmetic already done" —
-- this is the consumer it was proven for.
map-hop : ∀ {n} {Γ : Ctx n} {s u} (F r̂ r̂′ : ℕ) (η : Fin n → ℕ)
  (fn : Fn Γ [] [] [] s u) →
  (∀ v → hopDᵛ F η s v ≤ r̂ → hopDᵛ F η u (applyFn fn v) ≤ r̂′) →
  (vs : List (Val Γ s)) →
  all (λ v → hopDᵛ F η s v ≤ᵇ r̂) vs ≡ true →
  all (λ v → hopDᵛ F η u v ≤ᵇ r̂′) (map (applyFn fn) vs) ≡ true
map-hop F r̂ r̂′ η fn tr []       h = refl
map-hop {s = s} F r̂ r̂′ η fn tr (v ∷ vs) h
  with ∧-true (hopDᵛ F η s v ≤ᵇ r̂) (all (λ w → hopDᵛ F η s w ≤ᵇ r̂) vs) h
... | hv , hvs =
  ∧-intro (T⇒≡true _ (≤⇒≤ᵇ (tr v (≤ᵇ⇒≤ (hopDᵛ F η s v) r̂ (T-to hv)))))
          (map-hop F r̂ r̂′ η fn tr vs hvs)

-- THE BURST INDUCTION AT map-f, WET HALF — pushTake-wet's sibling, and
-- the DEAD ROUTE beside `pushBurst-walk` is exactly why there are two of
-- them instead of one generic face: caps measures are frame-generic and
-- THE HOP LEDGER IS NOT.  map is where that shows.  take's output hop
-- index IS its input's, so r̂ goes in and r̂ comes out; map's is
-- `hopDᵗ f + (pmᵗ F 0 f ⊔ 1) * r̂`, the growing shape the frame-generic
-- route's counterexample exploits at `f := map-f`.
--
-- WHAT map COSTS THAT take DOES NOT — nothing on the state side, and
-- that is most of the face.  `stepFrame … (map-f fn) …` returns `sched`
-- and `st` VERBATIM and emits no bookkeeping at all, so INV? and
-- regsLen? are the hypotheses unchanged, the retagged slot is always
-- `[]`, and the dry conjunct's step half is `refl`.  What take does not
-- pay and map does is the two value ledgers directly above.
--
-- CONCLUDES burstΨ?, NOT burstB?, and that is the Psi-Split design
-- rather than a weakening: the size half of the wet predicate mentions
-- the level, so transporting it across a frame that GROWS values would
-- need a size-growth theorem; re-supplying it from the caps receipt the
-- level already produced needs none.  The caller zips the two.
pushMap-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (Ψ B F ℓ r̂ r̂′ : ℕ) (η : Fin n → ℕ) (g : Gas) (bid : Id) (now : Tick)
  (fn : Fn Γ [] [] [] s u) (κ : Path Γ u t) (str : Stream Γ s)
  (sched : Sched Γ) (st : EvalSt e) →
  caseWᵗ fn ⊔ fnCapᵗ fn ≤ Ψ →
  (∀ v → hopDᵛ F η s v ≤ r̂ → hopDᵛ F η u (applyFn fn v) ≤ r̂′) →
  INV? Ψ B sched st ≡ true →
  burstΨ? Ψ str ≡ true →
  burstHopD? F η r̂ str ≡ true →
  hasDry str ≡ false →
  regsLen? ℓ (EvalSt.registry st) ≡ true →
  let r = pushBurst g bid now (map-f fn) κ str sched st
  in (INV? Ψ B (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
   × (burstΨ? Ψ (proj₁ r) ≡ true)
   × (burstHopD? F η r̂′ (proj₁ r) ≡ true)
   × (hasDry (proj₁ r) ≡ false)
   × (regsLen? ℓ (EvalSt.registry (proj₂ (proj₂ r))) ≡ true)
pushMap-wet Ψ B F ℓ r̂ r̂′ η g bid now fn κ [] sched st hfn tr invW bΨ bH hDry rgs =
  invW , refl , refl , refl , rgs
pushMap-wet {n = n} {Γ = Γ} {s = s} {u = u} Ψ B F ℓ r̂ r̂′ η g bid now fn κ
  (em ∷ ems) sched st hfn tr invW bΨ bH hDry rgs =
  W1 , ∧-intro EMITΨ W2 , ∧-intro EMITH W3 , cong₂ _∨_ EMITD W4 , W5
  where
  E    = InstEmit.events em
  sp   = splitEvents {A = Val Γ u} E
  step = stepFrame g bid now (map-f fn) κ (proj₁ sp) (proj₂ (proj₂ sp)) sched st
  eΨ   = proj₁ (∧-true _ _ bΨ)
  eH   = proj₁ (∧-true _ _ bH)
  dSp  = ∨-false (any dryEvent E) (hasDry ems) hDry
  S2   : valsΨ? Ψ (proj₁ step) ≡ true
  S2   = map-Ψ Ψ fn (proj₁ sp) hfn (splitEvents-vals-Ψ {A = Val Γ u} Ψ E eΨ)
  S3   : all (λ v → hopDᵛ F η u v ≤ᵇ r̂′) (proj₁ step) ≡ true
  S3   = map-hop F r̂ r̂′ η fn tr (proj₁ sp)
           (splitEvents-vals-hop {u = u} F η r̂ E eH)
  IH   = pushMap-wet Ψ B F ℓ r̂ r̂′ η g bid now fn κ ems sched st hfn tr
           invW (proj₂ (∧-true _ _ bΨ)) (proj₂ (∧-true _ _ bH)) (proj₂ dSp) rgs
  W1   = proj₁ IH
  W2   = proj₁ (proj₂ IH)
  W3   = proj₁ (proj₂ (proj₂ IH))
  W4   = proj₁ (proj₂ (proj₂ (proj₂ IH)))
  W5   = proj₂ (proj₂ (proj₂ (proj₂ IH)))
  -- THE RETAG LAYER IS ABSENT, and pinning it would have been WRONG.
  -- map's stepFrame emits `[]` LITERALLY, so `retagEvents (proj₁ (proj₂
  -- step))` reduces to `[]` and its target payload type is left
  -- unconstrained by the goal — an unsolved meta at a term that
  -- contributes nothing.  take's stays stuck behind `lookupNode`, which
  -- is why pushTake-wet has three ++ layers here and this face has two.
  EMITΨ : all (eventΨ? Ψ)
              (proj₁ (proj₂ sp) ++ map value (proj₁ step)
                 ++ (if proj₁ (proj₂ (proj₂ step)) then complete ∷ [] else []))
            ≡ true
  EMITΨ = all-++-intro (eventΨ? Ψ) (proj₁ (proj₂ sp)) _
            (splitEvents-bk-Ψ {t = u} Ψ E)
            (all-++-intro (eventΨ? Ψ) (map value (proj₁ step)) _
               (mapValue-Ψ Ψ (proj₁ step) S2)
               (finList-Ψ {n = n} {Γ = Γ} {u = u} Ψ
                  (proj₁ (proj₂ (proj₂ step)))))
  EMITH : all (hopDev? F η r̂′)
              (proj₁ (proj₂ sp) ++ map value (proj₁ step)
                 ++ (if proj₁ (proj₂ (proj₂ step)) then complete ∷ [] else []))
            ≡ true
  EMITH = all-++-intro (hopDev? F η r̂′) (proj₁ (proj₂ sp)) _
            (splitEvents-bk-hop {u = u} F η r̂′ E)
            (all-++-intro (hopDev? F η r̂′) (map value (proj₁ step)) _
               (mapValue-hop F η r̂′ (proj₁ step) S3)
               (finList-hop {n = n} {Γ = Γ} {u = u} F η r̂′
                  (proj₁ (proj₂ (proj₂ step)))))
  EMITD : any dryEvent
              (proj₁ (proj₂ sp) ++ map value (proj₁ step)
                 ++ (if proj₁ (proj₂ (proj₂ step)) then complete ∷ [] else []))
            ≡ false
  EMITD = any-++-false dryEvent (proj₁ (proj₂ sp)) _
            (splitEvents-bk-dry {u = u} E (proj₁ dSp))
            (any-++-false dryEvent (map value (proj₁ step)) _
               (mapValue-dry (proj₁ step))
               (finList-dry {A = Val Γ u} (proj₁ (proj₂ (proj₂ step)))))
-- THE take CLAUSE'S RECURSING ARM, ASSEMBLED — mintNode, installNode,
-- the source walk under `take-f nid ↠ κ`, then the push.  It is
-- `subscribeE-caps`'s own takeᵉ clause (.Subscribe-Face, PROVEN, at
-- THESE indices) for the four caps conjuncts, verbatim down to the
-- transports, ⊗ pushTake-wet above for the five wet ones.
--
-- WHAT THE TAKE CLAUSE COSTS THAT THE SCAN CLAUSE DOES NOT: nothing.
-- The node payload is `take-st (suc k)`, a numeral, so both of its wet
-- bounds and both of its caps bounds are `true` OUTRIGHT (boundedNode,
-- fnCapNode, widNode all ignore a take-st) — where the scan clause has
-- to build its seed with evalTm and pay `evalSeed-caps`' own level step
-- j₀ first.  So the callee runs at `suc j`, the level descent is plain
-- `op-desc` rather than the eval-shaped `op-desc-eval`, and the two path
-- predicates' frame conjuncts are `refl`.
--
-- THE DEMAND DROP is `dBound-μ` and not `dBound-struct`: take's hop
-- index is the identity, so r is FIXED across the edge and only the
-- syncSize axis moves — `syncSizeᵉ (takeᵉ c e) = suc (syncSizeᵗ c +
-- syncSizeᵉ e)` (Rx.Exp) is a `suc`, which is the whole of the strictness
-- that funds the ℓ ledger's charge for the one longer path.
--
-- `wb` IS THE RECURSION, PINNED AT THE CALLER'S GAS, for the reason
-- WalkStmtᴴˢᶠ's header gives: a bare `walkFace b` at the gas-polymorphic
-- type is a partial application whose fuel the termination checker reads
-- as unknown, and it rejects the whole walk group.
walk-take-suc : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (g : Gas) (cnt : Tm Γ [] [] [] natᵗ) (b : Closed Γ u) (k : ℕ) →
  evalTm cnt ≡ suc k → (wb : WalkStmtAt {e = e} g b) →
  WalkStmtAt {e = e} g (takeᵉ cnt b)
walk-take-suc g cnt b k ecEq wb c Ψ F Ŝ R̂ G ℓ L̂ dep bud zero j κ bid now sl sched st
  2≤S 1≤R hCR slEq slC slSz inv szb wdb pC lC nst () dpt
walk-take-suc {n = n} {u = u} g cnt b k ecEq wb c Ψ F Ŝ R̂ G ℓ L̂ dep bud (suc ops′) j
  κ bid now sl sched st
  2≤S 1≤R hCR slEq slC slSz inv szb wdb pC lC nst hidx dpt invW fnC pB
  s2 fS rS ceil lb dmd gas lℓ rgs
  rewrite ecEq =
  suc (j₁ + j₂)
    , subst (λ x → capsOK? (frameStep x c)
                     (proj₁ (proj₂ PB)) (proj₂ (proj₂ PB)) ≡ true)
            (sym (+-suc j (j₁ + j₂)))
            (frameStep-+assoc-caps c (suc j) j₁ j₂
               (proj₁ (proj₂ PB)) (proj₂ (proj₂ PB)) (proj₁ (proj₂ PBc)))
    , subst (λ x → burstCaps? (frameStep x c) sl (proj₁ PB) ≡ true)
            (sym (+-suc j (j₁ + j₂)))
            (frameStep-+assoc-burst c (suc j) j₁ j₂ sl (proj₁ PB)
               (proj₁ (proj₂ (proj₂ PBc))))
    , subst (λ x → burstCount? (frameStep x c) (proj₁ PB) ≡ true)
            (sym (+-suc j (j₁ + j₂)))
            (frameStep-+assoc-count c (suc j) j₁ j₂ (proj₁ PB)
               (proj₁ (proj₂ (proj₂ (proj₂ PBc)))))
    , op-step (Caps.cSize c) (Caps.cWid c) dep bud ops′ j j₁ j₂ 2≤S a₄
        (≤-trans (proj₂ (proj₂ (proj₂ (proj₂ PBc))))
                 (burst-index (Caps.cSize c) (Caps.cWid c) dep bud
                    (length (proj₁ res)) (suc j + j₁) (suc j + j₁) 2≤S
                    (countLen (frameStep (suc j + j₁) c) (proj₁ res) a₃)))
    , subst (λ x → INV? Ψ (Caps.cSize (frameStep x c))
                     (proj₁ (proj₂ PB)) (proj₂ (proj₂ PB)) ≡ true)
            (sym EQ)
            (INV?-widen (proj₁ (proj₂ PB)) (proj₂ (proj₂ PB)) (proj₁ ⊑₂) V1)
    , subst (λ x → burstB? (Caps.cSize (frameStep x c)) Ψ (proj₁ PB) ≡ true)
            (sym EQ)
            (burstB?-widen (proj₁ PB) (proj₁ ⊑₂) V2)
    , V3 , V4 , V5
  where
  nid    = Sched.nextNode sched
  sched₀ = record sched { nextNode = suc (Sched.nextNode sched) }
  ns     = take-st {Γ = _} (suc k)
  st₀    = installNode nid ns st
  step⊑  = frameStep-mono-j c 2≤S (n≤1+n j)
  B′     = Caps.cSize (frameStep (suc j) c)
  szsum : sizeᵗ cnt + sizeᵉ b ≤ Caps.cSize (frameStep j c)
  szsum  = ≤-trans (n≤1+n (sizeᵗ cnt + sizeᵉ b)) szb
  szb′   = ≤-trans (m≤n+m (sizeᵉ b) (sizeᵗ cnt)) szsum
  fcb    = ≤-trans (m≤n⊔m (caseWᵗ cnt ⊔ fnCapᵗ cnt) (fnCapᵉ b)) fnC
  U      = unconn sl (EvalSt.connectedShares st)
  G′     = dBound Ŝ R̂ U (hopDᵉ F (slotHop F sl) b) (syncSizeᵉ b)
  -- BOTH moving positions named, r′ = r included: dBound-struct's own
  -- header says its indices get stuck once `dBound` has unfolded through
  -- _*_, and an unannotated `≤-refl` in the r slot leaves r itself a meta
  rFix : hopDᵉ F (slotHop F sl) b ≤ hopDᵉ F (slotHop F sl) b
  rFix = ≤-refl
  sLt : syncSizeᵉ b < suc (syncSizeᵗ cnt + syncSizeᵉ b)
  sLt = s≤s (m≤n+m (syncSizeᵉ b) (syncSizeᵗ cnt))
  sucG′≤G : suc G′ ≤ G
  sucG′≤G = ≤-trans (dBound-struct Ŝ R̂ U rFix sLt) dmd
  pC′ : pathSz? B′ (take-f nid ↠ κ) ≡ true
  pC′ = ∧-intro refl
          (∧-intro (T⇒≡true (suc (pathLen κ) ≤ᵇ B′)
                     (≤⇒≤ᵇ (≤-trans lC (proj₁ step⊑))))
                   (pathSz?-⊑ κ step⊑ pC))
  pB′ : pathB? B′ Ψ (take-f nid ↠ κ) ≡ true
  pB′ = ∧-intro refl (pathB?-widen κ (proj₁ step⊑) pB)
  inv₀ : capsOK? (frameStep (suc j) c) sched₀ st₀ ≡ true
  inv₀ = capsOK?-setNode (frameStep (suc j) c) nid ns sched₀ st refl refl
           (capsOK?-mono (frameStep j c) (frameStep (suc j) c) sched₀ st step⊑
              (capsOK?-nextNode (frameStep j c) (suc (Sched.nextNode sched))
                                sched st inv))
  invW′ : INV? Ψ B′ sched₀ st₀ ≡ true
  invW′ = INV?-install Ψ (Caps.cSize (frameStep j c)) B′ nid ns sched sched₀ st
            (proj₁ step⊑) refl refl refl refl invW
  SUB = wb c Ψ F Ŝ R̂ G′ ℓ L̂ dep bud ops′ (suc j)
          (take-f nid ↠ κ) bid now sl sched₀ st₀
          2≤S 1≤R hCR slEq slC slSz inv₀
          (≤-trans szb′ (proj₁ step⊑))
          (≤-trans (m≤n⊔m (dWᵗ n sl cnt) (dWᵉ n sl b))
                   (≤-trans wdb (proj₁ (proj₂ step⊑))))
          pC′
          (frameStep-chain-suc c j (pathLen κ) 2≤S lC)
          (take-step cnt b sl _ bud nst)
          (chain-desc (sizeᵗ cnt) (sizeᵉ b) ops′ hidx)
          (≤-trans (m≤m⊔n _ _) dpt)
          invW′ fcb pB′
          s2 fS rS ceil
          (≤-trans (op-desc (Caps.cSize c) (Caps.cWid c) dep bud ops′ j 2≤S) lb)
          ≤-refl
          (hasAtLeast-mono (≤-trans sucG′≤G (n≤1+n G)) gas)
          (≤-trans (≤-reflexive (sym (+-suc (pathLen κ) G′)))
                   (≤-trans (+-monoʳ-≤ (pathLen κ) sucG′≤G) lℓ))
          rgs
  j₁  = proj₁ SUB
  a₁  = proj₁ (proj₂ SUB)
  a₂  = proj₁ (proj₂ (proj₂ SUB))
  a₃  = proj₁ (proj₂ (proj₂ (proj₂ SUB)))
  a₄  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ SUB))))
  a₅  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SUB)))))
  a₆  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SUB))))))
  a₇  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SUB)))))))
  a₈  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SUB))))))))
  a₉  = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SUB))))))))
  res = subscribeE g b (take-f nid ↠ κ) bid now sched₀ st₀
  ⊑₁  = frameStep-⊑-+ c 2≤S (suc j) j₁
  PBc = pushBurst-caps c dep bud (suc j + j₁) g bid now (take-f nid) κ (proj₁ res)
          sl (proj₁ (proj₂ res)) (proj₂ (proj₂ res)) 2≤S 1≤R
          (trans (KeepsC.slotsEq
                   (subscribeE-keeps g b (take-f nid ↠ κ) bid now sched₀ st₀)) slEq)
          slC slSz a₁ refl
          (pathSz?-⊑ κ ⊑₁ (pathSz?-⊑ κ step⊑ pC))
          (≤-trans (≤-trans lC (proj₁ step⊑)) (proj₁ ⊑₁))
          a₂ a₃
          (≤-trans (burst-takef-zero g bid now nid κ (proj₁ res)
                      (proj₁ (proj₂ res)) (proj₂ (proj₂ res))) z≤n)
  j₂  = proj₁ PBc
  PB  = pushBurst g bid now (take-f nid) κ (proj₁ res)
          (proj₁ (proj₂ res)) (proj₂ (proj₂ res))
  WET = pushTake-wet Ψ (Caps.cSize (frameStep (suc j + j₁) c)) F ℓ
          (hopDᵉ F (slotHop F sl) b) (slotHop F sl)
          g bid now nid κ (proj₁ res)
          (proj₁ (proj₂ res)) (proj₂ (proj₂ res))
          a₅ a₆ a₇ a₈ a₉
  V1  = proj₁ WET
  V2  = proj₁ (proj₂ WET)
  V3  = proj₁ (proj₂ (proj₂ WET))
  V4  = proj₁ (proj₂ (proj₂ (proj₂ WET)))
  V5  = proj₂ (proj₂ (proj₂ (proj₂ WET)))
  EQ : j + suc (j₁ + j₂) ≡ (suc j + j₁) + j₂
  EQ = trans (+-suc j (j₁ + j₂)) (cong suc (sym (+-assoc j j₁ j₂)))
  ⊑₂  = frameStep-⊑-+ c 2≤S (suc j + j₁) j₂
-- THE DISPATCH.  Two arms, and the split is the point: the `zero` arm never
-- subscribes, so it owes no push face, while the `suc k` arm mints a node,
-- recurses and pushes.  Keeping them in one postulate hid the free case —
-- "a postulate hides not just unpaid premises but whole free cases"
-- (subscribeE-take0-wf's own header, on this same clause).
walk-take : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (g : Gas) (cnt : Tm Γ [] [] [] natᵗ) (b : Closed Γ u)
  (wb : WalkStmtAt {e = e} g b) → WalkStmtAt {e = e} g (takeᵉ cnt b)
-- NOT a `with`, and the reason is worth keeping: `with evalTm cnt in ecEq`
-- ABSTRACTS the scrutinee out of the goal, so the branch is asked for
-- `subscribeE … | evalWith cnt []` while each leaf's type still says
-- `subscribeE …` — UnequalTerms on `Sched.live`, which reads as a proof
-- error and is really the with-abstraction.  Matching on a FRESH variable
-- inside `go` leaves the goal untouched and needs no telescope spelled out,
-- since the whole statement is `WalkStmt`.  It is also the cheaper shape:
-- a `with` here would abstract over a fully-applied closed goal, which is
-- what the Typing.With cost note warns about.
walk-take {Γ = Γ} {e = e} g cnt b wb = go (evalTm cnt) refl
  where
  go : (m : Val Γ natᵗ) → evalTm cnt ≡ m → WalkStmtAt {e = e} g (takeᵉ cnt b)
  go zero    eq = walk-take-zero g cnt b eq
  go (suc k) eq = walk-take-suc  g cnt b k eq wb

-- THE map CLAUSE, ASSEMBLED — and it is the SHORTEST of the chain
-- frames, because mapᵉ mints nothing: subscribeE's clause hands `sched`
-- and `st` straight to the source walk under `map-f f ↠ κ` and then
-- pushes (Rx.Evaluator), so there is no node install, no nextNode bump
-- and no transport of the invariant across one.  It is
-- `subscribeE-caps`'s own mapᵉ clause (.Subscribe-Face, PROVEN, at THESE
-- indices) for the four caps conjuncts, verbatim, ⊗ pushMap-wet above.
--
-- THE FIFTH AND SIXTH CONJUNCTS ARE WHERE map DIFFERS FROM take, and it
-- is one line: take's burstB? is its callee's WIDENED, because take
-- transforms no value; map's is BUILT — the caps receipt this clause
-- already reports as conjunct two, zipped against pushMap-wet's Ψ half
-- by `burstB?-halves`.  Nothing is widened and no size-growth theorem is
-- spent, which is the Psi-Split mechanism doing the job it was split out
-- to do.
--
-- THE DEMAND DROP is `dBound-struct` on BOTH axes, where take moved only
-- one: `hopDᵉ (mapᵉ f b)` is `hopDᵗ f + (pmᵗ F 0 f ⊔ 1) * hopDᵉ b`, weakly
-- above the source's since the coefficient is at least 1, and
-- `syncSizeᵉ (mapᵉ f b)` is a `suc` (Rx.Exp) — that `suc` is the whole of
-- the strictness that funds the gas peel and the ℓ ledger's charge for
-- the one longer path.
--
-- `wb` IS THE RECURSION, PINNED AT THE CALLER'S GAS, for the reason
-- WalkStmtᴴˢᶠ's header gives: a bare `walkFace b` at the gas-polymorphic
-- type is a partial application whose fuel the termination checker reads
-- as unknown, and it rejects the whole walk group.
walk-map : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (g : Gas) (f : Fn Γ [] [] [] s u) (b : Closed Γ s)
  (wb : WalkStmtAt {e = e} g b) → WalkStmtAt {e = e} g (mapᵉ f b)
walk-map g f b wb c Ψ F Ŝ R̂ G ℓ L̂ dep bud zero j κ bid now sl sched st
  2≤S 1≤R hCR slEq slC slSz inv szb wdb pC lC nst () dpt
walk-map {n = n} {u = u} g f b wb c Ψ F Ŝ R̂ G ℓ L̂ dep bud (suc ops′) j
  κ bid now sl sched st
  2≤S 1≤R hCR slEq slC slSz inv szb wdb pC lC nst hidx dpt invW fnC pB
  s2 fS rS ceil lb dmd gas lℓ rgs =
  suc (j₁ + j₂)
    , subst (λ x → capsOK? (frameStep x c)
                     (proj₁ (proj₂ PB)) (proj₂ (proj₂ PB)) ≡ true)
            (sym (+-suc j (j₁ + j₂)))
            (frameStep-+assoc-caps c (suc j) j₁ j₂
               (proj₁ (proj₂ PB)) (proj₂ (proj₂ PB)) (proj₁ (proj₂ PBc)))
    , CAPSB
    , subst (λ x → burstCount? (frameStep x c) (proj₁ PB) ≡ true)
            (sym (+-suc j (j₁ + j₂)))
            (frameStep-+assoc-count c (suc j) j₁ j₂ (proj₁ PB)
               (proj₁ (proj₂ (proj₂ (proj₂ PBc)))))
    , op-step (Caps.cSize c) (Caps.cWid c) dep bud ops′ j j₁ j₂ 2≤S a₄
        (≤-trans (proj₂ (proj₂ (proj₂ (proj₂ PBc))))
                 (burst-index (Caps.cSize c) (Caps.cWid c) dep bud
                    (length (proj₁ res)) (suc j + j₁) (suc j + j₁) 2≤S
                    (countLen (frameStep (suc j + j₁) c) (proj₁ res) a₃)))
    , subst (λ x → INV? Ψ (Caps.cSize (frameStep x c))
                     (proj₁ (proj₂ PB)) (proj₂ (proj₂ PB)) ≡ true)
            (sym EQ)
            (INV?-widen (proj₁ (proj₂ PB)) (proj₂ (proj₂ PB)) (proj₁ ⊑₂) V1)
    , burstB?-halves (frameStep (j + suc (j₁ + j₂)) c) sl Ψ (proj₁ PB) CAPSB V2
    , V3 , V4 , V5
  where
  step⊑ = frameStep-mono-j c 2≤S (n≤1+n j)
  B′    = Caps.cSize (frameStep (suc j) c)
  η     = slotHop F sl
  szsum : sizeᵗ f + sizeᵉ b ≤ Caps.cSize (frameStep j c)
  szsum = ≤-trans (n≤1+n (sizeᵗ f + sizeᵉ b)) szb
  szf   = ≤-trans (m≤m+n (sizeᵗ f) (sizeᵉ b)) szsum
  szb′  = ≤-trans (m≤n+m (sizeᵉ b) (sizeᵗ f)) szsum
  fΨ≤   = ≤-trans (m≤m⊔n (caseWᵗ f ⊔ fnCapᵗ f) (fnCapᵉ b)) fnC
  fcb   = ≤-trans (m≤n⊔m (caseWᵗ f ⊔ fnCapᵗ f) (fnCapᵉ b)) fnC
  fS′ : frameSz? B′ (map-f f) ≡ true
  fS′ = T⇒≡true (sizeᵗ f ≤ᵇ B′) (≤⇒≤ᵇ (≤-trans szf (proj₁ step⊑)))
  fΨ′ : frameBΨ? Ψ (map-f f) ≡ true
  fΨ′ = T⇒≡true ((caseWᵗ f ⊔ fnCapᵗ f) ≤ᵇ Ψ) (≤⇒≤ᵇ fΨ≤)
  pC′ : pathSz? B′ (map-f f ↠ κ) ≡ true
  pC′ = ∧-intro fS′
          (∧-intro (T⇒≡true (suc (pathLen κ) ≤ᵇ B′)
                     (≤⇒≤ᵇ (≤-trans lC (proj₁ step⊑))))
                   (pathSz?-⊑ κ step⊑ pC))
  pB′ : pathB? B′ Ψ (map-f f ↠ κ) ≡ true
  pB′ = ∧-intro (frameB?-of-parts (map-f f) fS′ fΨ′)
                (pathB?-widen κ (proj₁ step⊑) pB)
  U     = unconn sl (EvalSt.connectedShares st)
  G′    = dBound Ŝ R̂ U (hopDᵉ F η b) (syncSizeᵉ b)
  -- BOTH moving positions named, as dBound-struct's header requires:
  -- an unannotated ≤-refl in the r slot leaves r itself a meta once
  -- dBound has unfolded through _*_
  rGrow : hopDᵉ F η b ≤ hopDᵗ F η f + (pmᵗ F 0 f ⊔ 1) * hopDᵉ F η b
  rGrow = ≤-trans (≤-trans (≤-reflexive (sym (*-identityˡ (hopDᵉ F η b))))
                           (*-monoˡ-≤ (hopDᵉ F η b) (m≤n⊔m (pmᵗ F 0 f) 1)))
                  (m≤n+m ((pmᵗ F 0 f ⊔ 1) * hopDᵉ F η b) (hopDᵗ F η f))
  sLt : syncSizeᵉ b < suc (syncSizeᵗ f + syncSizeᵉ b)
  sLt = s≤s (m≤n+m (syncSizeᵉ b) (syncSizeᵗ f))
  sucG′≤G : suc G′ ≤ G
  sucG′≤G = ≤-trans (dBound-struct Ŝ R̂ U rGrow sLt) dmd
  SUB = wb c Ψ F Ŝ R̂ G′ ℓ L̂ dep bud ops′ (suc j)
          (map-f f ↠ κ) bid now sl sched st
          2≤S 1≤R hCR slEq slC slSz
          (capsOK?-mono (frameStep j c) (frameStep (suc j) c) sched st step⊑ inv)
          (≤-trans szb′ (proj₁ step⊑))
          (≤-trans (m≤n⊔m (dWᵗ n sl f) (dWᵉ n sl b))
                   (≤-trans wdb (proj₁ (proj₂ step⊑))))
          pC′
          (frameStep-chain-suc c j (pathLen κ) 2≤S lC)
          (map-step f b sl _ bud nst)
          (chain-desc (sizeᵗ f) (sizeᵉ b) ops′ hidx)
          (≤-trans (m≤m⊔n _ _) dpt)
          (INV?-widen sched st (proj₁ step⊑) invW) fcb pB′
          s2 fS rS ceil
          (≤-trans (op-desc (Caps.cSize c) (Caps.cWid c) dep bud ops′ j 2≤S) lb)
          ≤-refl
          (hasAtLeast-mono (≤-trans sucG′≤G (n≤1+n G)) gas)
          (≤-trans (≤-reflexive (sym (+-suc (pathLen κ) G′)))
                   (≤-trans (+-monoʳ-≤ (pathLen κ) sucG′≤G) lℓ))
          rgs
  j₁  = proj₁ SUB
  a₁  = proj₁ (proj₂ SUB)
  a₂  = proj₁ (proj₂ (proj₂ SUB))
  a₃  = proj₁ (proj₂ (proj₂ (proj₂ SUB)))
  a₄  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ SUB))))
  a₅  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SUB)))))
  a₆  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SUB))))))
  a₇  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SUB)))))))
  a₈  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SUB))))))))
  a₉  = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SUB))))))))
  res = subscribeE g b (map-f f ↠ κ) bid now sched st
  ⊑₁  = frameStep-⊑-+ c 2≤S (suc j) j₁
  PBc = pushBurst-caps c dep bud (suc j + j₁) g bid now (map-f f) κ (proj₁ res)
          sl (proj₁ (proj₂ res)) (proj₂ (proj₂ res)) 2≤S 1≤R
          (trans (KeepsC.slotsEq
                   (subscribeE-keeps g b (map-f f ↠ κ) bid now sched st)) slEq)
          slC slSz a₁
          (frameSz?-widen (map-f f) (proj₁ ⊑₁) fS′)
          (pathSz?-⊑ κ ⊑₁ (pathSz?-⊑ κ step⊑ pC))
          (≤-trans (≤-trans lC (proj₁ step⊑)) (proj₁ ⊑₁))
          a₂ a₃
          (≤-trans (m≤n⊔m _ _) dpt)
  j₂  = proj₁ PBc
  PB  = pushBurst g bid now (map-f f) κ (proj₁ res)
          (proj₁ (proj₂ res)) (proj₂ (proj₂ res))
  WET = pushMap-wet Ψ (Caps.cSize (frameStep (suc j + j₁) c)) F ℓ
          (hopDᵉ F η b) (hopDᵗ F η f + (pmᵗ F 0 f ⊔ 1) * hopDᵉ F η b) η
          g bid now f κ (proj₁ res)
          (proj₁ (proj₂ res)) (proj₂ (proj₂ res))
          fΨ≤
          (λ v hv → hopD-map-emit F η f b v f ≤-refl ≤-refl hv)
          a₅
          (burstΨ?-of (Caps.cSize (frameStep (suc j + j₁) c)) Ψ (proj₁ res) a₆)
          a₇ a₈ a₉
  V1  = proj₁ WET
  V2  = proj₁ (proj₂ WET)
  V3  = proj₁ (proj₂ (proj₂ WET))
  V4  = proj₁ (proj₂ (proj₂ (proj₂ WET)))
  V5  = proj₂ (proj₂ (proj₂ (proj₂ WET)))
  EQ : j + suc (j₁ + j₂) ≡ (suc j + j₁) + j₂
  EQ = trans (+-suc j (j₁ + j₂)) (cong suc (sym (+-assoc j j₁ j₂)))
  ⊑₂  = frameStep-⊑-+ c 2≤S (suc j + j₁) j₂
  CAPSB : burstCaps? (frameStep (j + suc (j₁ + j₂)) c) sl (proj₁ PB) ≡ true
  CAPSB = subst (λ x → burstCaps? (frameStep x c) sl (proj₁ PB) ≡ true)
                (sym (+-suc j (j₁ + j₂)))
                (frameStep-+assoc-burst c (suc j) j₁ j₂ sl (proj₁ PB)
                   (proj₁ (proj₂ (proj₂ PBc))))

-- THE SOURCE BURST'S HOP RECEIPT, AND IT IS NO LONGER A LEAF.  The
-- conjunct is `burstHopD?` about the SOURCE's OWN burst — `proj₁ r` for
-- `r = subscribeE g b (scan-f f nid ↠ κ) …` — so no part of the scan push
-- face enters it.  It is the walk face's own eighth conjunct AT `b`, and
-- everything this body does is discharge the walk face's hypotheses at the
-- minted-and-installed state.
--
-- `wb` IS THAT RECURSION, APPLIED TO `b` AND PINNED AT THE CALLER'S GAS —
-- and the pinning is load-bearing, not tidiness: passing the bare
-- `walkFace b` at the gas-POLYMORPHIC type is a PARTIAL application, whose
-- fuel the termination checker reads as unknown, and it rejects the whole
-- walk group (walk-mu with it).  Why, and the shape that works, is in
-- WalkStmtᴴˢᶠ's header, beside the type that carries the pin.
--
-- THE TEMPLATE IS `subscribeE-caps`'s OWN scanᵉ CLAUSE (.Subscribe-Face),
-- PROVEN, AT THESE VERY INDICES, and the one thing to carry from it is
-- that the callee runs at `suc (j + j₀)` and NOT at `suc j`: the seed is
-- BUILT by evalTm, which can grow it, so `evalSeed-caps` steps the level
-- by its own `j₀` before the source is subscribed.  The wet half's splits
-- are `subscribeE-walkS`'s scan clause (.Wet/Part2) on the capᴱ axis.
--
-- THE DEMAND DROP IS THE ONE THING NEITHER TWIN HAS, because a chain frame
-- has no hop edge to spend — `hopDᵉ` at a scan MULTIPLIES rather than
-- adding one.  It comes off `dBound-struct`, which is strict on the
-- syncSize axis, and `syncSizeᵉ (scanᵉ f z b)` is a `suc`: the source's
-- demand is therefore strictly below the frame's whatever the hops do,
-- which is what funds the ℓ ledger's charge for the longer path.
walk-scan-source-burst : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (g : Gas) (f : Fn Γ [] [] [] (u ×ᵗ s) u) (z : Tm Γ [] [] [] u)
  (b : Closed Γ s) (wb : WalkStmtAt {e = e} g b) → WalkStmtᴴˢᶠ {e = e} g f z b
walk-scan-source-burst g f z b wb c Ψ F Ŝ R̂ G ℓ L̂ dep bud zero j κ bid now sl sched st
  2≤S 1≤R hCR slEq slC slSz inv szb wdb pC lC nst () dpt
walk-scan-source-burst {n = n} {u = u} g f z b wb c Ψ F Ŝ R̂ G ℓ L̂ dep bud (suc ops′) j
  κ bid now sl sched st
  2≤S 1≤R hCR slEq slC slSz inv szb wdb pC lC nst hidx dpt invW fnC pB
  s2 fS rS ceil lb dmd gas lℓ rgs =
  proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SUB)))))))
  where
  -- the size splits, verbatim from the caps twin
  szsum : sizeᵗ f + sizeᵗ z + sizeᵉ b ≤ Caps.cSize (frameStep j c)
  szsum = ≤-trans (n≤1+n (sizeᵗ f + sizeᵗ z + sizeᵉ b)) szb
  szfz  = ≤-trans (m≤m+n (sizeᵗ f + sizeᵗ z) (sizeᵉ b)) szsum
  szf   = ≤-trans (m≤m+n (sizeᵗ f) (sizeᵗ z)) szfz
  szz   = ≤-trans (m≤n+m (sizeᵗ z) (sizeᵗ f)) szfz
  szb′  = ≤-trans (m≤n+m (sizeᵉ b) (sizeᵗ f + sizeᵗ z)) szsum
  -- the Ψ splits, verbatim from the wet twin
  capf  = ≤-trans (m≤m⊔n (caseWᵗ f ⊔ fnCapᵗ f) _) fnC
  capz  : caseWᵗ z ⊔ fnCapᵗ z ≤ Ψ
  capz  = ≤-trans (m≤m⊔n (caseWᵗ z ⊔ fnCapᵗ z) (fnCapᵉ b))
            (≤-trans (m≤n⊔m (caseWᵗ f ⊔ fnCapᵗ f) _) fnC)
  fcb   = ≤-trans (m≤n⊔m (caseWᵗ z ⊔ fnCapᵗ z) (fnCapᵉ b))
            (≤-trans (m≤n⊔m (caseWᵗ f ⊔ fnCapᵗ f) _) fnC)
  SD    = evalSeed-caps c j sl z 2≤S slC szz
            (≤-trans (m≤n⊔m (dWᵗ n sl f) (dWᵗ n sl z))
              (≤-trans (m≤m⊔n (dWᵗ n sl f ⊔ dWᵗ n sl z) (dWᵉ n sl b)) wdb))
  j₀     = proj₁ SD
  ⊑₀     = frameStep-⊑-+ c 2≤S j j₀
  nid    = Sched.nextNode sched
  sched₀ = record sched { nextNode = suc (Sched.nextNode sched) }
  ns     = scan-st (evalTm z)
  st₀    = installNode nid ns st
  step⊑  = frameStep-mono-j c 2≤S (n≤1+n (j + j₀))
  B′     = Caps.cSize (frameStep (suc (j + j₀)) c)
  ⊑both  = ⊑ᶜ-trans ⊑₀ step⊑
  VW     = valCaps?-widen sl _ (evalTm z) step⊑ (proj₂ SD)
  bnd    = valCaps?-size (frameStep (suc (j + j₀)) c) sl _ (evalTm z) VW
  fnN    = T⇒≡true _ (≤⇒≤ᵇ (fnCap-evalWith Ψ z []ᵃ tt capz))
  U      = unconn sl (EvalSt.connectedShares st)
  G′     = dBound Ŝ R̂ U (hopDᵉ F (slotHop F sl) b) (syncSizeᵉ b)
  -- the source's hop sits under the frame's: `hopDᵉ` at a scan MULTIPLIES
  -- by a positive power (Rx.Hop-Depth, the refold bound), so the ≤ is the
  -- summand's, widened by a factor of at least one
  hop≤ : hopDᵉ F (slotHop F sl) b
           ≤ (2 + pmᵗ F 0 f) ^ F
             * (hopDᵗ F (slotHop F sl) f + hopDᵗ F (slotHop F sl) z
                + hopDᵉ F (slotHop F sl) b)
  hop≤ = ≤-trans (m≤n+m (hopDᵉ F (slotHop F sl) b)
                    (hopDᵗ F (slotHop F sl) f + hopDᵗ F (slotHop F sl) z))
           (≤-trans (≤-reflexive (sym (*-identityˡ _)))
                    (*-monoˡ-≤ _ (1≤pow≤ (2 + pmᵗ F 0 f) F (s≤s z≤n))))
  sucG′≤G : suc G′ ≤ G
  sucG′≤G =
    ≤-trans (dBound-struct Ŝ R̂ U hop≤
               (s≤s (m≤n+m (syncSizeᵉ b) (syncSizeᵗ f + syncSizeᵗ z))))
            dmd
  pC′ : pathSz? B′ (scan-f f nid ↠ κ) ≡ true
  pC′ = ∧-intro (T⇒≡true (sizeᵗ f ≤ᵇ B′)
                  (≤⇒≤ᵇ (≤-trans szf (proj₁ ⊑both))))
          (∧-intro (T⇒≡true (suc (pathLen κ) ≤ᵇ B′)
                     (≤⇒≤ᵇ (≤-trans lC (proj₁ ⊑both))))
                   (pathSz?-⊑ κ step⊑ (pathSz?-⊑ κ ⊑₀ pC)))
  pB′ : pathB? B′ Ψ (scan-f f nid ↠ κ) ≡ true
  pB′ = ∧-intro (∧-intro (T⇒≡true _ (≤⇒≤ᵇ (≤-trans szf (proj₁ ⊑both))))
                         (T⇒≡true _ (≤⇒≤ᵇ capf)))
                (pathB?-widen κ (proj₁ ⊑both) pB)
  inv₀ : capsOK? (frameStep (suc (j + j₀)) c) sched₀ st₀ ≡ true
  inv₀ = capsOK?-setNode (frameStep (suc (j + j₀)) c) nid ns sched₀ st bnd
           (subst (λ y → widNode (Caps.cWid (frameStep (suc (j + j₀)) c)) y ns ≡ true)
                  (sym slEq)
                  (valCaps?-wid (frameStep (suc (j + j₀)) c) sl _ (evalTm z) VW))
           (capsOK?-mono (frameStep j c) (frameStep (suc (j + j₀)) c) sched₀ st ⊑both
              (capsOK?-nextNode (frameStep j c) (suc (Sched.nextNode sched))
                                sched st inv))
  invW′ : INV? Ψ B′ sched₀ st₀ ≡ true
  invW′ = INV?-install Ψ (Caps.cSize (frameStep j c)) B′ nid ns sched sched₀ st
            (proj₁ ⊑both) refl refl bnd fnN invW
  SUB = wb c Ψ F Ŝ R̂ G′ ℓ L̂ dep bud ops′ (suc (j + j₀))
          (scan-f f nid ↠ κ) bid now sl sched₀ st₀
          2≤S 1≤R hCR slEq slC slSz inv₀
          (≤-trans szb′ (proj₁ ⊑both))
          (≤-trans (m≤n⊔m (dWᵗ n sl f ⊔ dWᵗ n sl z) (dWᵉ n sl b))
             (≤-trans wdb (proj₁ (proj₂ ⊑both))))
          pC′
          (frameStep-chain-suc c (j + j₀) (pathLen κ) 2≤S
             (≤-trans lC (proj₁ ⊑₀)))
          (scan-step f z b sl _ bud nst)
          (chain-desc (sizeᵗ f + sizeᵗ z) (sizeᵉ b) ops′ hidx)
          (≤-trans (m≤m⊔n _ _) dpt)
          invW′ fcb pB′
          s2 fS rS ceil
          (≤-trans (op-desc-eval (Caps.cSize c) (Caps.cWid c) dep bud ops′ j j₀
                      2≤S (s≤s szz)) lb)
          ≤-refl
          (hasAtLeast-mono (≤-trans sucG′≤G (n≤1+n G)) gas)
          (≤-trans (≤-reflexive (sym (+-suc (pathLen κ) G′)))
                   (≤-trans (+-monoʳ-≤ (pathLen κ) sucG′≤G) lℓ))
          rgs

-- THE SOURCE HALF, ASSEMBLED.  Both conjuncts are the frame leaf's,
-- lifted from headline to hereditary — free, per `valHopSpn?-intro`.
walk-scan-source : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (g : Gas) (f : Fn Γ [] [] [] (u ×ᵗ s) u) (z : Tm Γ [] [] [] u)
  (b : Closed Γ s) (wb : WalkStmtAt {e = e} g b) → WalkStmtᴴˢ⁰ {e = e} g f z b
walk-scan-source g f z b wb c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j κ bid now sl sched st
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
  frB = walk-scan-source-burst g f z b wb c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j κ bid now sl sched st
          2≤S 1≤R hCR slEq slC slSz inv szb wdb pC lC nst hidx dpt invW fnC pB
          s2 fS rS ceil lb dmd gas lℓ rgs
  -- THE NODE HALF, AND IT IS NOW GAPLESS.  `mint-install-survives`
  -- (.Node-Fresh) is exactly this shape — mint, install, subscribe under a
  -- frame naming the minted nid, read the node back — and it is PROVEN there
  -- off a ring over the whole of `subscribeE`.  `scan-node` / `take-node`
  -- (.Part3) spend the same lemma.
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
  (g : Gas) (f : Fn Γ [] [] [] (u ×ᵗ s) u) (z : Tm Γ [] [] [] u)
  (b : Closed Γ s) (wb : WalkStmtAt {e = e} g b) → WalkStmtᴴˢ {e = e} g f z b
walk-scan-hop-spn g f z b wb c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j κ bid now sl sched st
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
  src = walk-scan-source g f z b wb c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j κ bid now sl sched st
          2≤S 1≤R hCR slEq slC slSz inv szb wdb pC lC nst hidx dpt invW fnC pB
          s2 fS rS ceil lb dmd gas lℓ rgs

-- THE scan CLAUSE, ASSEMBLED.  Nothing is proven here that the two leaves
-- do not already say; the point of the assembly is that it puts the row's
-- risk in ONE of them.  See walk-scan-hop's header for what that one owes.
walk-scan : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (g : Gas) (f : Fn Γ [] [] [] (u ×ᵗ s) u) (z : Tm Γ [] [] [] u)
  (b : Closed Γ s) (wb : WalkStmtAt {e = e} g b) →
  WalkStmtAt {e = e} g (scanᵉ f z b)
walk-scan g f z b wb c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j κ bid now sl sched st
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
          (walk-scan-hop-spn g f z b wb c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j κ bid now sl sched st
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

