{-# OPTIONS --guardedness #-}

-- EVERY STEP KEEPS THE INVARIANT (`inv-next`): its fold part
-- (`Base`, kept by `base-next`) and its order part (`adequacy.Engine.Pick.Order`,
-- kept by `ord-next`).  The fold part is dispatched as the
-- step is: by mode, then by the one frame a rise passes, the one former
-- a subscribe begins, or the one node a mark runs.  The invariant is a
-- fold over the tree (`Wf`), split at the focus into the context's share
-- (`WfC`) and the focus's own; each case rebuilds only the node the step
-- rewrites, and the context's share rides along.
module adequacy.Engine.Inv where

open import Data.Bool using (Bool; true; false; not; if_then_else_; _∧_)
open import Data.Bool.Properties using (∧-identityʳ)
open import Level using (lift; lower)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _ʳ++_; null; [_]; reverse)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (zero; suc; pred; _<ᵇ_; _≡ᵇ_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Properties using (++-identityʳ)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.List.Relation.Unary.Any using (here)
import Data.List.Relation.Unary.All
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; subst₂; sym; trans; cong)

open import Tree using (Obs; Later; mergeᶠ; switchᶠ; exhaustᶠ; cold; empty; of; map; scan; takeWhile; flatMap;
  connect; connected; defer)
open import denotation.MonotonicList.Events using (Pos; Timeline; emit; stall; close; Events∞; hush; idle; ix; last; From; timelineAt; done)
  renaming (at to atᶠ; quiet to silentᶠ)
open import denotation.MonotonicList using (Agreeᵀ)
open import operation.Key using (at)
open import denotation.Unfold using (NEnv; stateᴺ; cutᴺ; states; outerᴺ; subscribe; startᶜ; idleᶜ; flatMapᶜ)
open import adequacy.Engine.Head using (Frag)
open import adequacy.Engine.Keys using (Keys; Keyed; Held; FlatAt; FlatKeys; []ᴷ)
open import adequacy.Placed.Order using (Headed; Alienᴱ; Owned; every-lookup; everyT-idle)
open import adequacy.Engine.Trails using (shape-≋)
open import adequacy.Placed.Trail using (sortedT-idle; flatT-idle)
open import adequacy.Engine.Above using (Above; Flight; above-≋; take-excl; take-here; conn-drop; flat-drop; keyedL-ʳ++; toʳ; lanes-runs; lanes-P; rested-risen; ending-risen; takeAt-risen)
open import adequacy.Engine.Ahead using (Under; shown; ahead-mono; under-sub; Sides; Ahead; Aloof; ahead-over) renaming (shows to showsᶜ)
open import adequacy.Engine.Race using (NotBefore)
open import adequacy.Engine.Meaning using (_≋_; ≋-by; flagOf; envAt; gh; risen; lane; lanesL; laneRuns; poolRuns; outerT; outerG; poolG; deadL)
open import adequacy.Engine.Flown using (Owed; NextOwed; rise-owed; sub-owed)
open import adequacy.Engine.Plug using (flight-held; keys-above; keys-swap)
open import adequacy.Engine.Pick using (Order; order; module Order; Heard; whole; KeysAt; Shaped; Lead; Snap; ⊤₁; tt; Won; lane-on; pooled-live; search-won; causal-aloft; Caught; caught-sub; Within)
open import adequacy.Engine.Pick.Lead using (lead-clear; lead-ends; lane-off)
open import adequacy.Engine.Causal using (Causal; causal-run; cold-≼; cold-over; done-≼; of-≼; att-≼; cp-≼; over-≼; join-≼; conn-≼; body-conn; src-conn; owed-conn; ≼-refl; unsubIf-≼; cut-≼)
open import adequacy.Engine.Ghosted using (NextTold; told-next)
open import adequacy.Engine.Scope using (Gh)
open import adequacy.Engine.Firmed using (gh-firm)
open import adequacy.Engine.Shuts using (Toldˢ; none)
open import operation.PureObservable using (Tape; play; ending; over; opening; module Machine; module Driver)
open import adequacy.Engine.Fold using (Base; Owns; Unpended; Wf; WfC; Wfs; attO; base-at; bodyO; cpO; cutO; if-inv; inv; joinO; leafO; ofO; opened-move; opened-none; owedO; owned; pend-unsubIf; search-hit; found-own; settle-settled; srcAttO; wf-cut; wf-ended; wf-feed; wf-killAll; wf-split; wf-unsubIf; wfI; wfs-++; wfs-ʳ++)

open Machine using (St; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
  Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody; plug; closed; closedUp;
  CS; cs; shows; still; outOf; attAt; attached; free; cpAt; cutAt; overAt; nx; cp;
  Conf; ⟨_,_,_,_⟩; Mode; subscribing; absorbed; rising;
  Mark; ofM; attM; bodyM; srcAttM; owedM; cpM; cutM; joinM; leafM; search; found; leaf;
  rise; run; begin; start; admit; dequeue; settle; ended; alive; feed; feedL; unsub; killAll; unsubIf; _⊕_)
  renaming (cut to cutᴹ)

------------------------------------------------------------------------
-- The step, case by case

module _ {R : Set} where
  open Driver R using (Step; silent; value; complete; drained; step; played; took)

  NextBase : Step → Set
  NextBase (silent t k)    = Base k
  NextBase (value t p a k) = Base k
  NextBase (complete p)    = ⊤
  NextBase drained         = ⊤

  -- A leaf's turn: whatever the runtime plays, the leaf is all that moves.
  played-inv : ∀ {A} b (l : Tape A) cl dv st → (∀ e l′ b′ p′ → Base (dv e l′ b′ p′)) → (∀ l′ → Base (st l′))
             → NextBase (played (leaf b l cl dv st))
  played-inv b     (ending e)                  cl    dv st d s = d cp over false e
  played-inv false (play τ u i t fr)           cl    dv st d s = s over
  played-inv false over                        cl    dv st d s = s over
  played-inv true  (play τ u i t fr)           true  dv st d s = s over
  played-inv true  over                        true  dv st d s = s over
  played-inv true  (play τ u i t (emit a k))   false dv st d s = d _ _ _ _
  played-inv true  (play τ u i t (stall k))    false dv st d s = s _
  played-inv true  (play τ u i t (close k))    false dv st d s = s _
  played-inv true  over                        false dv st d s = s over

  start-inv : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) ls a p → WfC c → Wf o → Wfs ls
            → Base (start c op f d n q o ls a p)
  start-inv c op f d n q o ls a p v wo ws with closed c
  ... | true  = inv tt v (wo , ws)
  ... | false = inv tt (wo , wfs-ʳ++ ls ws tt , tt , v) tt

  dequeue-inv : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) ls p → WfC c → Wf o → Wfs ls
              → Base (dequeue c op f d n q o ls p)
  dequeue-inv c op f d n []      o ls p v wo ws = inv (settle-settled d n true tt) v (wo , ws)
  dequeue-inv c op f d n (a ∷ q) o ls p v wo ws = start-inv c op f d n q o ls a p v wo ws

  admit-inv : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) ls a p → WfC c → Wf o → Wfs ls
            → NextBase (took (admit c op f d n q o ls a p))
  admit-inv c (mergeᶠ nothing)  f d n q o ls a p v wo ws = start-inv c (mergeᶠ nothing) f d n q o ls a p v wo ws
  admit-inv c (mergeᶠ (just m)) f d n q o ls a p v wo ws =
    if-inv Base (n <ᵇ m) (start-inv c (mergeᶠ (just m)) f d n q o ls a p v wo ws) (inv tt v (wo , ws))
  admit-inv c switchᶠ           f d n q o ls a p v wo ws with killAll ls | wf-killAll ls ws
  ... | ls′ , t | ws′ = start-inv c switchᶠ f d 0 q o ls′ a p v wo ws′
  admit-inv c exhaustᶠ          f d n q o ls a p v wo ws with n ≡ᵇ 0
  ... | true  = start-inv c exhaustᶠ f d n q o ls a p v wo ws
  ... | false = inv tt v (wo , ws)

  -- A rise, by the frame it passes.
  rise-inv : ∀ {Γ A} (c : Ctx R Γ A) (s : St Γ A) e p → Base ⟨ c , s , rising e , p ⟩ → NextBase (took (rise c s e p))
  rise-inv top                               s (nx a) p (inv u v w) = inv u v w
  rise-inv top                               s cp     p (inv u v w) = tt
  rise-inv (inMap f c)                       s e      p (inv u v w) = inv tt v w
  rise-inv (inScan f z c)                    s (nx a) p (inv u v w) = inv tt v w
  rise-inv (inScan f z c)                    s cp     p (inv u v w) = inv tt v w
  rise-inv (inCut true a c)                  s e      p (inv u v w) = inv tt v w
  rise-inv (inCut false a c)                 s e      p (inv u v w) = inv tt v w
  rise-inv (inLn b c)                        s e      p (inv u v w) = inv tt v w
  rise-inv (inTake i q free c)               s (nx a) p (inv u v w) with q a | i
  ... | true  | _     = inv tt v w
  ... | false | true  = inv tt v w
  ... | false | false = inv tt v w
  rise-inv (inTake i q free c)               s cp     p (inv u v w) = inv tt v w
  rise-inv (inTake i q (cpAt r) c)           s e      p (inv u v w) = inv tt v w
  rise-inv (inTake i q (cutAt r) c)          s e      p (inv u v w) = inv tt v w
  rise-inv (inTake i q (overAt r) c)         s e      p (inv u v w) = inv tt v w
  rise-inv (inOuter op f d n q ls c)         s (nx a) p (inv u (ws , v) w) = admit-inv c op f d n q s ls a p v w ws
  rise-inv (inOuter op f true n q ls c)      s cp     p (inv u (ws , v) w) = inv tt v (w , ws)
  rise-inv (inOuter op f false n q ls c)     s cp     p (inv u (ws , v) w) =
    inv (settle-settled true n (Data.List.null q) tt) v (w , ws)
  rise-inv (inLanes op f d n q o pre post c) s (nx b) p (inv u (wo , wp , wq , v) w) =
    if-inv Base (alive s) (inv tt v (wo , wfs-++ pre wp w wq)) (inv tt v (wo , wfs-++ pre wp w wq))
  rise-inv (inLanes op f d n q o pre post c) s cp     p (inv u (wo , wp , wq , v) w) =
    if-inv Base (alive s) (dequeue-inv c op f d _ q o (pre ʳ++ ended s ∷ post) p v wo (wfs-++ pre wp (wf-ended s w) wq)) (inv tt v (wo , wfs-++ pre wp w wq))
  rise-inv (inSrc k b c)                     s (nx a) p (inv u (e , wb , v) w) =
    inv tt v (opened-none k s e , w , wf-feed (here refl) p (nx a) b wb)
  rise-inv (inSrc k b c)                     s cp     p (inv u (e , wb , v) w) =
    inv tt v (opened-none (record k { closed = true ; endAt = p }) s e , w , wf-feed (here refl) p cp b wb)
  rise-inv (inBody k o c)                    s (nx b) p (inv u (op , wo , v) w) = inv tt v (op , wo , w)
  rise-inv (inBody (cs cl sl sa ba as ow r e) o c) s cp p (inv u (op , wo , v) w) =
    inv tt v (opened-move cl sl sa ba as ow r e sl sa as (just p) r e (λ ip → ip) op , wo , w)

  -- A subscribe, by the former it begins.
  begin-inv : ∀ {Γ A} (c : Ctx R Γ A) (o : Obs Timeline Γ A) p → Base ⟨ c , pend o , subscribing , p ⟩ → NextBase (took (begin c o p))
  begin-inv c (cold x)          p (inv u v w) = inv tt v tt
  begin-inv c empty             p (inv u v w) = inv tt v tt
  begin-inv c (of xs)           p (inv u v w) = inv tt v tt
  begin-inv c (map f s)         p (inv u v w) = inv tt v tt
  begin-inv c (scan f z s)      p (inv u v w) = inv tt v tt
  begin-inv c (takeWhile i q s) p (inv u v w) = inv tt v tt
  begin-inv c (flatMap op f s)  p (inv u v w) = inv tt (tt , v) tt
  begin-inv c (connect s b)     p (inv u v w) = inv tt ((refl , tt) , tt , v) tt
  begin-inv c (connected x)     p (inv u v w) with closedUp c x
  ... | true  = inv tt v tt
  ... | false = inv tt v tt
  begin-inv c (defer l)         p (inv u v w) = inv tt v tt

  -- A mark run, by the node that owns it.
  run-inv : ∀ {Γ A} (c : Ctx R Γ A) {s : St Γ A} {m} p → Owns s m → WfC c → Wf s → NextBase (took (run c s m p))
  run-inv c p (ofO {xs = xs}) v w with closed c | xs
  ... | true  | _       = inv tt v tt
  ... | false | []      = inv tt v tt
  ... | false | x ∷ xs′ = inv tt v tt
  run-inv c p (attO {l = l} {s = s}) v w with unsubIf (not l) s | wf-unsubIf (not l) s w
  ... | s′ , t | w′ = inv tt v w′
  run-inv c p cpO v w with closed c
  ... | true  = inv tt v w
  ... | false = inv tt v w
  run-inv c p (cutO {s = s}) v w with cutᴹ s | wf-cut s w
  ... | s′ , t | w′ = inv tt v w′
  run-inv c p (bodyO {k = cs cl sl sa (just q) as ow r e} _) v (op , wo , wb) = inv (proj₂ op) (refl , wb , v) wo
  run-inv c p (bodyO {k = cs cl sl sa nothing as ow r e} ()) v w
  run-inv c p (srcAttO {k = cs cl sl sa ba (just q) ow r e} {o = o} _) v (op , wo , wb)
    with unsubIf (not sl) o | wf-unsubIf (not sl) o wo | pend-unsubIf (not sl) o
  ... | o′ , t | wo′ | pu = inv tt v (opened-move cl sl sa ba (just q) ow r e sl true nothing ow r e pu op , wo′ , wb)
  run-inv c p (srcAttO {k = cs cl sl sa ba nothing ow r e} ()) v w
  run-inv c p (owedO {k = cs cl sl sa ba as (just q) r e} {o = o} _) v (op , wo , wb)
    with unsubIf sa o | wf-unsubIf sa o wo | pend-unsubIf sa o
  ... | o′ , t | wo′ | pu = inv tt v (opened-move cl sl sa ba as (just q) r e false sa as nothing r e pu op , wo′ , wb)
  run-inv c p (owedO {k = cs cl sl sa ba as nothing r e} ()) v w
  run-inv c p (joinO {g = true}  {e = nx a}) v w with closed c
  ... | true  = inv tt v tt
  ... | false = inv tt v tt
  run-inv c p (joinO {g = true}  {e = cp})   v w with closed c
  ... | true  = inv tt v tt
  ... | false = inv tt v tt
  run-inv c p (joinO {g = false} {e = nx a}) v w = inv tt v tt
  run-inv c p (joinO {g = false} {e = cp})   v w = inv tt v tt
  run-inv c p (leafO {b = b} {l = l} _) v w =
    played-inv b l (closed c) (λ e l′ b′ p′ → ⟨ c , coldS b′ l′ , (if not (closed c) then rising e else absorbed) , p′ ⟩) (λ l′ → ⟨ c , coldS b l′ , absorbed , p ⟩)
      (λ e l′ b′ p′ → cold-inv (closed c) e l′ b′ p′) (λ l′ → inv tt v tt)
    where
      cold-inv : ∀ cl e l′ b′ p′ → Base ⟨ c , coldS b′ l′ , (if not cl then rising e else absorbed) , p′ ⟩
      cold-inv true  e l′ b′ p′ = inv tt v tt
      cold-inv false e l′ b′ p′ = inv tt v tt

  -- EVERY STEP KEEPS THE INVARIANT.
  base-next : ∀ k → Base k → NextBase (step k)
  base-next ⟨ c , s , rising e , p ⟩     v = rise-inv c s e p v
  base-next ⟨ c , pend o , subscribing , p ⟩ v = begin-inv c o p v

  base-next ⟨ c , (coldS xb xl) , subscribing , p ⟩ v = v
  base-next ⟨ c , (ofS xi xp xxs) , subscribing , p ⟩ v = v
  base-next ⟨ c , doneS , subscribing , p ⟩ v = v
  base-next ⟨ c , (mapS xf xs) , subscribing , p ⟩ v = v
  base-next ⟨ c , (scanS xf xz xs) , subscribing , p ⟩ v = v
  base-next ⟨ c , (cutS xl xa xs) , subscribing , p ⟩ v = v
  base-next ⟨ c , (lnS xb xs) , subscribing , p ⟩ v = v
  base-next ⟨ c , (takeS xi xq xw xs) , subscribing , p ⟩ v = v
  base-next ⟨ c , (flatS xop xf xd xn xq xo xls) , subscribing , p ⟩ v = v
  base-next ⟨ c , (connS xk xo xb) , subscribing , p ⟩ v = v
  base-next ⟨ c , (joinS xj xg xx xib) , subscribing , p ⟩ v = v
  base-next ⟨ c , s , absorbed , p ⟩ v with search top (plug c s) in e
  ... | nothing = tt
  ... | just (found (_ , _ , c′ , s′) m key) with search-hit (plug c s) e
  ...   | pl , own with wf-split c′ s′ (owned own) (subst Wf (sym pl) (wfI v))
  ...     | v′ , w′ = run-inv c′ p own v′ w′

  base-load : (o : Obs Timeline [] R) → Base (Machine.load o)
  base-load o = inv tt tt tt

  ----------------------------------------------------------------------
  -- EVERY RISE IS READ BY AN OPEN OBSERVER

  NextHeard : Step → Set
  NextHeard (silent t k)    = Heard k
  NextHeard (value t p a k) = Heard k
  NextHeard (complete p)    = ⊤
  NextHeard drained         = ⊤

  start-heard : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) ls a p → Heard (start c op f d n q o ls a p)
  start-heard c op f d n q o ls a p with closed c
  ... | true  = tt
  ... | false = tt

  settle-heard : ∀ {Γ B} (c : Ctx R Γ B) (s : St Γ B) d n e p → closed c ≡ false → Heard ⟨ c , s , settle d n e , p ⟩
  settle-heard c s d n e p ce with d ∧ (n ≡ᵇ 0) ∧ e
  ... | true  = ce
  ... | false = tt

  dequeue-heard : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) ls p → closed c ≡ false
                 → Heard (dequeue c op f d n q o ls p)
  dequeue-heard c op f d n []      o ls p ce = settle-heard c (flatS op f d n [] o ls) d n true p ce
  dequeue-heard c op f d n (a ∷ q) o ls p ce = start-heard c op f d n q o ls a p

  admit-heard : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) ls a p
               → NextHeard (took (admit c op f d n q o ls a p))
  admit-heard c (mergeᶠ nothing)  f d n q o ls a p = start-heard c (mergeᶠ nothing) f d n q o ls a p
  admit-heard c (mergeᶠ (just m)) f d n q o ls a p = if-inv Heard (n <ᵇ m) (start-heard c (mergeᶠ (just m)) f d n q o ls a p) tt
  admit-heard c switchᶠ           f d n q o ls a p with killAll ls
  ... | ls′ , t = start-heard c switchᶠ f d 0 q o ls′ a p
  admit-heard c exhaustᶠ          f d n q o ls a p with n ≡ᵇ 0
  ... | true  = start-heard c exhaustᶠ f d n q o ls a p
  ... | false = tt

  -- A rise passes to a frame no more closed than the one it leaves.
  rise-heard : ∀ {Γ A} (c : Ctx R Γ A) (s : St Γ A) e p → closed c ≡ false → NextHeard (took (rise c s e p))
  rise-heard top                               s (nx a) p ce = tt
  rise-heard top                               s cp     p ce = tt
  rise-heard (inMap f c)                       s e      p ce = ce
  rise-heard (inScan f z c)                    s (nx a) p ce = ce
  rise-heard (inScan f z c)                    s cp     p ce = ce
  rise-heard (inCut true a c)                  s e      p ce = ce
  rise-heard (inCut false a c)                 s e      p ce = tt
  rise-heard (inLn b c)                        s e      p ce = ce
  rise-heard (inTake i q free c)               s (nx a) p ce with q a | i
  ... | true  | _     = ce
  ... | false | true  = ce
  ... | false | false = tt
  rise-heard (inTake i q free c)               s cp     p ce = ce
  rise-heard (inTake i q (cpAt r) c)           s e      p ce = tt
  rise-heard (inTake i q (cutAt r) c)          s e      p ce = tt
  rise-heard (inTake i q (overAt r) c)         s e      p ce = tt
  rise-heard (inOuter op f d n q ls c)         s (nx a) p ce = admit-heard c op f d n q s ls a p
  rise-heard (inOuter op f true n q ls c)      s cp     p ce = tt
  rise-heard (inOuter op f false n q ls c)     s cp     p ce = settle-heard c (flatS op f true n q s ls) true n (Data.List.null q) p ce
  rise-heard (inLanes op f d n q o pre post c) s (nx b) p ce = if-inv Heard (alive s) ce tt
  rise-heard (inLanes op f d n q o pre post c) s cp     p ce =
    if-inv Heard (alive s) (dequeue-heard c op f d (pred n) q o (pre ʳ++ ended s ∷ post) p ce) tt
  rise-heard (inSrc k b c)                     s (nx a) p ce = tt
  rise-heard (inSrc k b c)                     s cp     p ce = tt
  rise-heard (inBody k o c)                    s (nx b) p ce = ce
  rise-heard (inBody k o c)                    s cp     p ce = ce

  begin-heard : ∀ {Γ A} (c : Ctx R Γ A) (o : Obs Timeline Γ A) p → NextHeard (took (begin c o p))
  begin-heard c (cold x)          p = tt
  begin-heard c empty             p = tt
  begin-heard c (of xs)           p = tt
  begin-heard c (map f s)         p = tt
  begin-heard c (scan f z s)      p = tt
  begin-heard c (takeWhile i q s) p = tt
  begin-heard c (flatMap op f s)  p = tt
  begin-heard c (connect s b)     p = tt
  begin-heard c (connected x)     p with closedUp c x
  ... | true  = tt
  ... | false = tt
  begin-heard c (defer l)         p = tt

  played-heard : ∀ {A} b (l : Tape A) cl dv st → (∀ e l′ b′ p′ → Heard (dv e l′ b′ p′)) → (∀ l′ → Heard (st l′))
                → NextHeard (played (leaf b l cl dv st))
  played-heard b     (ending e)                  cl    dv st d s = d cp over false e
  played-heard false (play τ u i t fr)           cl    dv st d s = s over
  played-heard false over                        cl    dv st d s = s over
  played-heard true  (play τ u i t fr)           true  dv st d s = s over
  played-heard true  over                        true  dv st d s = s over
  played-heard true  (play τ u i t (emit a k))   false dv st d s = d _ _ _ _
  played-heard true  (play τ u i t (stall k))    false dv st d s = s _
  played-heard true  (play τ u i t (close k))    false dv st d s = s _
  played-heard true  over                        false dv st d s = s over

  -- A mark run rises only what its node shows, and asks first.
  run-heard : ∀ {Γ A} (c : Ctx R Γ A) {s : St Γ A} {m} p → Owns s m → NextHeard (took (run c s m p))
  run-heard c p (ofO {xs = xs}) with closed c in ce | xs
  ... | true  | _       = tt
  ... | false | []      = ce
  ... | false | x ∷ xs′ = ce
  run-heard c p (attO {l = l} {s = s}) with unsubIf (not l) s
  ... | s′ , t = tt
  run-heard c p cpO with closed c in ce
  ... | true  = tt
  ... | false = ce
  run-heard c p (cutO {s = s}) with cutᴹ s
  ... | s′ , t = tt
  run-heard c p (bodyO {k = cs cl sl sa (just q) as ow r e} _) = tt
  run-heard c p (bodyO {k = cs cl sl sa nothing as ow r e} ())
  run-heard c p (srcAttO {k = cs cl sl sa ba (just q) ow r e} {o = o} _) with unsubIf (not sl) o
  ... | o′ , t = tt
  run-heard c p (srcAttO {k = cs cl sl sa ba nothing ow r e} ())
  run-heard c p (owedO {k = cs cl sl sa ba as (just q) r e} {o = o} _) with unsubIf sa o
  ... | o′ , t = tt
  run-heard c p (owedO {k = cs cl sl sa ba as nothing r e} ())
  run-heard c p (joinO {g = true}  {e = nx a}) with closed c in ce
  ... | true  = tt
  ... | false = ce
  run-heard c p (joinO {g = true}  {e = cp})   with closed c in ce
  ... | true  = tt
  ... | false = ce
  run-heard c p (joinO {g = false} {e = nx a}) = tt
  run-heard c p (joinO {g = false} {e = cp})   = tt
  run-heard c p (leafO {b = b} {l = l} _) = played-heard b l (closed c) _ _ delivered (λ l′ → tt)
    where
      delivered : ∀ e l′ b′ p′ → Heard ⟨ c , coldS b′ l′ , (if not (closed c) then rising e else absorbed) , p′ ⟩
      delivered e l′ b′ p′ with closed c in ce
      ... | true  = tt
      ... | false = ce

  ----------------------------------------------------------------------
  -- The whole invariant: the fold and the order

  record Inv (k : Conf R) : Set₁ where
    constructor _&_
    field
      base : Base k
      ord  : Order k

  NextOrd : Step → Set₁
  NextOrd (silent t k)    = Order k
  NextOrd (value t p a k) = Order k
  NextOrd (complete p)    = ⊤₁
  NextOrd drained         = ⊤₁

  NextInv : Step → Set₁
  NextInv (silent t k)    = Inv k
  NextInv (value t p a k) = Inv k
  NextInv (complete p)    = ⊤₁
  NextInv drained         = ⊤₁

  NextFrag NextKeys NextShape NextFlight NextCaused : Step → Set
  NextLead : Step → Set₁
  NextFrag (silent t k)    = Frag (whole k)
  NextFrag (value t p a k) = Frag (whole k)
  NextFrag (complete p)    = ⊤
  NextFrag drained         = ⊤
  NextKeys (silent t k)    = KeysAt k
  NextKeys (value t p a k) = KeysAt k
  NextKeys (complete p)    = ⊤
  NextKeys drained         = ⊤
  NextShape (silent t k)    = Shaped k
  NextShape (value t p a k) = Shaped k
  NextShape (complete p)    = ⊤
  NextShape drained         = ⊤
  NextFlight (silent t k)    = Flight k
  NextFlight (value t p a k) = Flight k
  NextFlight (complete p)    = ⊤
  NextFlight drained         = ⊤
  NextLead (silent t k)    = Lead k
  NextLead (value t p a k) = Lead k
  NextLead (complete p)    = ⊤₁
  NextLead drained         = ⊤₁
  NextCaused (silent t k)    = Causal (whole k)
  NextCaused (value t p a k) = Causal (whole k)
  NextCaused (complete p)    = ⊤
  NextCaused drained         = ⊤

  postulate
    -- THE SHAPE: a step keeps the whole tree in the fragment.
    frag-next : ∀ k → Base k → Frag (whole k) → NextFrag (step k)
    -- THE KEYS KEPT: every node's own positional facts, each in the
    -- environment its connects give it, kept by a rise through a frame
    -- that rewrites its node: an outer's value or end, a lane's end, a
    -- source's value or end, a body's end; by a subscribe beginning a
    -- former; and by a mark run.
    rise-admit-keys : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q ls (s : St Γ A) a p
                    → Inv ⟨ inOuter op f d n q ls c , s , rising (nx a) , p ⟩ → NextKeys (step ⟨ inOuter op f d n q ls c , s , rising (nx a) , p ⟩)
    rise-outer-end-keys : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q ls (s : St Γ A) p
                        → Inv ⟨ inOuter op f d n q ls c , s , rising cp , p ⟩ → NextKeys (step ⟨ inOuter op f d n q ls c , s , rising cp , p ⟩)
    rise-lane-end-keys : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) pre post (s : St Γ B) p
                       → Inv ⟨ inLanes op f d n q o pre post c , s , rising cp , p ⟩
                       → KeysAt (dequeue c op f d (pred n) q o (pre ʳ++ ended s ∷ post) p)
    rise-src-keys : ∀ {Γ X B} (c : Ctx R Γ B) k (b : St (X ∷ Γ) B) (s : St Γ X) e p → Inv ⟨ inSrc k b c , s , rising e , p ⟩
                  → NextKeys (step ⟨ inSrc k b c , s , rising e , p ⟩)
    rise-body-end-keys : ∀ {Γ X B} (c : Ctx R Γ B) k (o : St Γ X) (s : St (X ∷ Γ) B) p → Inv ⟨ inBody k o c , s , rising cp , p ⟩
                       → Keyed (connS (record k { owedAt = just p }) o s) (envAt c)
    -- THE FLIGHT, READ: a lane already over absorbing what reaches it
    -- leaves the whole tree keyed.
    rise-dead-keys : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) pre post (s : St Γ B) e p
                   → Inv ⟨ inLanes op f d n q o pre post c , s , rising e , p ⟩ → alive s ≡ false
                   → Keys (plug c (flatS op f d n q o (pre ʳ++ s ∷ post)))
    -- A joiner of a subject already over runs as an empty `of` at its
    -- position: the subject ended before the joiner's position, so its
    -- rejoin owes the end at the joiner's `last`.
    joined-over : ∀ {Γ A} (c : Ctx R Γ A) (x : A ∈ Γ) p → Inv ⟨ c , pend (connected x) , subscribing , p ⟩ → closedUp c x ≡ true
                → stateᴺ (subscribe (connected x) p) (envAt c) ≋ stateᴺ (gh (ofS 0 p [])) (envAt c)
    -- A connect begun leaves the tree keyed.
    begin-conn-keys : ∀ {Γ X A} (c : Ctx R Γ A) (s : Obs Timeline Γ X) (b : Obs Timeline (X ∷ Γ) A) p
                    → Inv ⟨ c , pend (connect s b) , subscribing , p ⟩ → NextKeys (step ⟨ c , pend (connect s b) , subscribing , p ⟩)
    -- THE STILL'S SUBTREE: a subscription heads its position, where no
    -- source of its environment has been.
    sub-fresh : ∀ {Γ A} (c : Ctx R Γ A) (o : Obs Timeline Γ A) p → Inv ⟨ c , pend o , subscribing , p ⟩ → Headed p × Alienᴱ p (envAt c)
    run-keys : ∀ {Γ A} (c : Ctx R Γ A) (s : St Γ A) p → Inv ⟨ c , s , absorbed , p ⟩ → NextKeys (step ⟨ c , s , absorbed , p ⟩)
    -- THE FLIGHT KEPT: a mark run rising or subscribing what it ran
    -- leaves its hole's run in shape, and every frame above keeping its
    -- share.
    run-flight : ∀ {Γ A} (c : Ctx R Γ A) (s : St Γ A) p → Inv ⟨ c , s , absorbed , p ⟩ → NextOwed (step ⟨ c , s , absorbed , p ⟩)
    -- A tree's first subscription is in shape.
    flight-load : (o : Obs Timeline [] R) → Flight (Machine.load o)
    -- THE STILL'S SUBTREE: after a step every node's every key to come
    -- is aloft, nothing keyed under a skip not yet run: kept by a rise and
    -- a subscription begun.
    rise-causal : ∀ {Γ A} (c : Ctx R Γ A) (s : St Γ A) e p → Inv ⟨ c , s , rising e , p ⟩ → NextCaused (step ⟨ c , s , rising e , p ⟩)
    sub-causal : ∀ {Γ A} (c : Ctx R Γ A) (s : St Γ A) p → Inv ⟨ c , s , subscribing , p ⟩ → NextCaused (step ⟨ c , s , subscribing , p ⟩)
    -- A mark run rises, if at all, the event it showed, at its own key,
    -- leaving a node as live as the one it ran.
    run-lead : ∀ (t : St [] R) {Γ A} {c : Ctx R Γ A} {s m key} p → search top t ≡ just (found (Γ , A , c , s) m key)
             → (∀ q e (s′ : St Γ A) → key ≡ at q → outOf c s m ≡ shows e → alive s ≡ alive s′ → Snap q e c s′)
             → NextLead (took (run c s m p))

  -- Where a lane begins, every frame above it, its flatMap's other parts
  -- among them, passes every skip under it.
  Begun : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) ls a p → Set₁
  Begun c op f d n q o ls a p =
    closed c ≡ false → Lead ⟨ inCut true (attAt (p ⊕ [ ix 1 ])) (inLn true (inLanes op f d (suc n) q o (reverse ls) [] c)) , pend (f a) , subscribing , p ⊕ [ ix 1 ] ⟩

  -- A lane begun under `p`, as its flatMap's other parts lead it.
  BegunSides : ∀ {Γ A B} (f : A → Obs Timeline Γ B) → Bool → St Γ A → List (St Γ B) → Pos → NEnv Γ → Set
  BegunSides f d o ls p ρ = ∀ j → Under (_≡ p ⊕ [ ix 1 ]) j → Sides j f d o (reverse (reverse ls)) [] ρ

  -- What the frames above lead at the skip just past `p`, they lead under
  -- the lane `p` begins, none of their heads being below `p`.
  begun : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) ls a p
        → (showsᶜ c true ≡ true → Ahead (_≡ p ⊕ [ ix 0 ]) c true) → (showsᶜ c true ≡ true → BegunSides f d o ls p (envAt c))
        → (showsᶜ c true ≡ true → Aloof p c true) → Begun c op f d n q o ls a p
  begun c op f d n q o ls a p ah sd al cl = lift λ sh →
    sd sh , ahead-over p (λ j u → under-sub p [ ix 1 ] j u) c true (ah sh) (al sh)

  postulate
    -- A LANE BEGUN IS CLEAR BESIDE: an admitted value's or a lane's end's
    -- flatMap's other parts come after every position under the lane it
    -- begins.
    outer-begun-sides : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) n q (o : St Γ A) ls a p
                      → Inv ⟨ inOuter op f false n q ls c , o , rising (nx a) , p ⟩ → showsᶜ c true ≡ true → BegunSides f false o ls p (envAt c)
    switch-begun-sides : ∀ {Γ A B} (c : Ctx R Γ B) (f : A → Obs Timeline Γ B) n q (o : St Γ A) ls a p
                       → Inv ⟨ inOuter switchᶠ f false n q ls c , o , rising (nx a) , p ⟩ → showsᶜ c true ≡ true
                       → BegunSides f false o (proj₁ (killAll ls)) p (envAt c)
    lane-begun-sides : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n a q (o : St Γ A) pre post (s : St Γ B) p
                     → alive s ≡ true → Inv ⟨ inLanes op f d n (a ∷ q) o pre post c , s , rising cp , p ⟩ → showsᶜ c true ≡ true
                     → BegunSides f d o (pre ʳ++ ended s ∷ post) p (envAt c)
    -- A SOURCE ABOUT TO BE SUBSCRIBED shows no earlier than its body's
    -- subscription and, hushed, leaves nothing running.
    fresh-src : ∀ {Γ X} (o : Obs Timeline Γ X) p (ρ : NEnv Γ)
              → (Events∞.force (stateᴺ (subscribe o (p ⊕ [ ix 1 ])) ρ) ≡ hush
                   → ∀ d → Agreeᵀ d (Events∞.cut (stateᴺ (subscribe o (p ⊕ [ ix 1 ])) ρ)) idle)
              × (∀ k → Under (_≡ p ⊕ [ ix 0 ]) k → NotBefore k (shown (Events∞.force (stateᴺ (subscribe o (p ⊕ [ ix 1 ])) ρ))))

  -- A LANE BEGUN IS CLEAR BENEATH: what an admitted value or a lane's end
  -- leaves the frames above, it leaves under the lane it begins.
  outer-begun : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) ls a p
              → Inv ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩ → Begun c op f d n q o ls a p
  outer-begun c op f true  n q o ls a p iv = ⊥-elim (lead-clear (Inv.ord iv))
  outer-begun c op f false n q o ls a p iv =
    begun c op f false n q o ls a p (proj₁ (proj₂ (proj₂ (proj₂ (lead-clear (Inv.ord iv)))))) (outer-begun-sides c op f n q o ls a p iv)
      (proj₂ (proj₂ (proj₂ (proj₂ (lead-clear (Inv.ord iv))))))

  switch-begun : ∀ {Γ A B} (c : Ctx R Γ B) (f : A → Obs Timeline Γ B) d n q (o : St Γ A) ls a p
               → Inv ⟨ inOuter switchᶠ f d n q ls c , o , rising (nx a) , p ⟩ → Begun c switchᶠ f d 0 q o (proj₁ (killAll ls)) a p
  switch-begun c f true  n q o ls a p iv = ⊥-elim (lead-clear (Inv.ord iv))
  switch-begun c f false n q o ls a p iv =
    begun c switchᶠ f false 0 q o (proj₁ (killAll ls)) a p (proj₁ (proj₂ (proj₂ (proj₂ (lead-clear (Inv.ord iv))))))
      (switch-begun-sides c f n q o ls a p iv) (proj₂ (proj₂ (proj₂ (proj₂ (lead-clear (Inv.ord iv))))))

  lane-begun : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n a q (o : St Γ A) pre post (s : St Γ B) p
             → alive s ≡ true → Inv ⟨ inLanes op f d n (a ∷ q) o pre post c , s , rising cp , p ⟩
             → Begun c op f d (pred n) q o (pre ʳ++ ended s ∷ post) a p
  lane-begun c op f d n a q o pre post s p al iv =
    begun c op f d (pred n) q o (pre ʳ++ ended s ∷ post) a p (λ sh → proj₁ (proj₂ (proj₂ (proj₂ (lead-ends (Inv.ord iv)))) sh))
      (lane-begun-sides c op f d n a q o pre post s p al iv) (λ sh → proj₂ (proj₂ (proj₂ (proj₂ (lead-ends (Inv.ord iv)))) sh))

  -- Nothing a subscription starts or a slot frees rises a value; an
  -- outer completing rises its flatMap's end with the end's lead.
  start-lead : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) ls a p → Begun c op f d n q o ls a p
             → Lead (start c op f d n q o ls a p)
  start-lead c op f d n q o ls a p b with closed c
  ... | true  = tt
  ... | false = b refl

  -- A completion the flatMap passes on keeps the snapshot it rose with.
  lead-if : ∀ {Γ A} (c : Ctx R Γ A) (s t : St Γ A) p b → alive t ≡ alive s → Won (at p , (if b then shows cp else still)) c t
          → Frag (plug c t) → Gh top (plug c t) → Keys (plug c t) → Caught p c t → Lead ⟨ c , s , (if b then rising cp else absorbed) , p ⟩
  lead-if c s t p true  al w ft gt kt cg = t , al , w , ft , gt , kt , cg
  lead-if c s t p false al w ft gt kt cg = tt

  admit-lead : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) ls a p → Inv ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩
             → NextLead (took (admit c op f d n q o ls a p))
  admit-lead c (mergeᶠ nothing)  f d n q o ls a p iv = start-lead c (mergeᶠ nothing) f d n q o ls a p (outer-begun c (mergeᶠ nothing) f d n q o ls a p iv)
  admit-lead c (mergeᶠ (just m)) f d n q o ls a p iv with n <ᵇ m
  ... | true  = start-lead c (mergeᶠ (just m)) f d n q o ls a p (outer-begun c (mergeᶠ (just m)) f d n q o ls a p iv)
  ... | false = tt
  admit-lead c switchᶠ           f d n q o ls a p iv with killAll ls | switch-begun c f d n q o ls a p iv
  ... | ls′ , t | b = start-lead c switchᶠ f d 0 q o ls′ a p b
  admit-lead c exhaustᶠ          f d n q o ls a p iv with n ≡ᵇ 0
  ... | true  = start-lead c exhaustᶠ f d n q o ls a p (outer-begun c exhaustᶠ f d n q o ls a p iv)
  ... | false = tt

  -- A rise carries its lead: the snapshot, read at the frame above.
  rise-lead : ∀ {Γ A} (c : Ctx R Γ A) (s : St Γ A) e p → Lead ⟨ c , s , rising e , p ⟩ → Inv ⟨ c , s , rising e , p ⟩
            → NextLead (took (rise c s e p))
  rise-lead top                               s (nx a) p l iv = tt
  rise-lead top                               s cp     p l iv = tt
  rise-lead (inMap f c)                       s e      p (t , al , w , ft , gt , kt , cg) iv = mapS f t , refl , w , ft , gt , kt , cg
  rise-lead (inScan f z c)                    s (nx a) p (t , al , w , ft , gt , kt , cg) iv = scanS f z t , refl , w , ft , gt , kt , cg
  rise-lead (inScan f z c)                    s cp     p (t , al , w , ft , gt , kt , cg) iv = scanS f z t , refl , w , ft , gt , kt , cg
  rise-lead (inCut true x c)                  s e      p (t , al , w , ft , gt , kt , cg) iv = cutS true x t , refl , w , ft , gt , kt , cg
  rise-lead (inCut false x c)                 s (nx a) p l iv = tt
  rise-lead (inCut false x c)                 s cp     p l iv = tt
  rise-lead (inLn b c)                        s e      p (t , al , w , ft , gt , kt , cg) iv = lnS b t , refl , w , ft , gt , kt , cg
  rise-lead (inTake i q free c)               s (nx a) p (t , al , w , ft , gt , kt , cg) iv with q a | i
  ... | true  | _     = takeS _ q free t , refl , w , ft , gt , kt , cg
  ... | false | true  = takeS true q free t , refl , w , ft , gt , kt , caught-sub {c = c} {t = takeS true q free t} [ ix 0 ] cg
  ... | false | false = tt
  rise-lead (inTake i q free c)               s cp     p (t , al , w , ft , gt , kt , cg) iv = takeS i q free t , refl , w , ft , gt , kt , cg
  rise-lead (inTake i q (cpAt r) c)           s (nx a) p l iv = tt
  rise-lead (inTake i q (cpAt r) c)           s cp     p l iv = tt
  rise-lead (inTake i q (cutAt r) c)          s (nx a) p l iv = tt
  rise-lead (inTake i q (cutAt r) c)          s cp     p l iv = tt
  rise-lead (inTake i q (overAt r) c)         s (nx a) p l iv = tt
  rise-lead (inTake i q (overAt r) c)         s cp     p l iv = tt
  rise-lead (inOuter op f d n q ls c)         s (nx a) p l iv = admit-lead c op f d n q s ls a p iv
  rise-lead (inOuter op f true n q ls c)      s cp     p l iv = tt
  rise-lead (inOuter op f false n q ls c)     s cp     p (t , al , (r , w , u) , ft , gt , kt , (k₀ , wi , _ , af)) iv =
    lead-if c (flatS op f true n q s ls) (flatS op f false n q t ls) p ((n ≡ᵇ 0) ∧ null q) refl w ft gt kt (k₀ , wi , af)
  rise-lead (inLanes op f d n q o pre post c) s (nx b) p (t , al , (l , u , w) , ft , gt , kt , (k₀ , wi , _ , _ , _ , af)) iv with alive s
  ... | true  = flatS op f d n q o (pre ʳ++ t ∷ post) , refl , lane-on d n q {alive t} {at p} b {c} (pooled-live (alive t) u) w , ft , gt , kt , (k₀ , wi , af)
  ... | false = tt
  rise-lead (inLanes op f d n [] o pre post c) s cp    p (t , al , (l , u , w) , ft , gt , kt , (k₀ , wi , _ , _ , _ , af)) iv with alive s
  ... | true  = lead-if c (flatS op f d (pred n) [] o (pre ʳ++ ended s ∷ post)) (flatS op f d n [] o (pre ʳ++ t ∷ post)) p (d ∧ (pred n ≡ᵇ 0) ∧ true) refl
                  (subst (λ x → Won (at p , (if d ∧ x then shows cp else still)) c (flatS op f d n [] o (pre ʳ++ t ∷ post))) (sym (∧-identityʳ (pred n ≡ᵇ 0)))
                     (lane-off d n [] {alive t} {at p} {c} (pooled-live (alive t) u) w)) ft gt kt (k₀ , wi , af)
  ... | false = tt
  rise-lead (inLanes op f d n (a ∷ q) o pre post c) s cp p l iv with alive s in al
  ... | true  = start-lead c op f d (pred n) q o (pre ʳ++ ended s ∷ post) a p (lane-begun c op f d n a q o pre post s p al iv)
  ... | false = tt
  rise-lead (inSrc k b c)                     s (nx a) p l iv = tt
  rise-lead (inSrc k b c)                     s cp     p l iv = tt
  rise-lead (inBody (cs cl true sa ba as nothing r en) o c) s (nx b) p (t , al , (_ , _ , _ , w) , ft , gt , kt , (k₀ , wi , _ , _ , _ , af)) iv =
    connS (cs cl true sa ba as nothing r en) o t , refl , w , ft , gt , kt , (k₀ , wi , af)
  rise-lead (inBody (cs cl true sa ba as (just _) r en) o c)  s (nx b) p (t , al , (() , _) , ft , gt , kt , _) iv
  rise-lead (inBody (cs cl false sa ba as (just _) r en) o c) s (nx b) p (t , al , (() , _) , ft , gt , kt , _) iv
  rise-lead (inBody (cs cl false sa ba as nothing r en) o c)  s (nx b) p (t , al , (() , _) , ft , gt , kt , _) iv
  rise-lead (inBody (cs cl true sa ba as nothing r en) o c) s cp p (t , al , (_ , _ , _ , w) , ft , gt , kt , (k₀ , wi , _ , _ , _ , af)) iv =
    connS (cs cl true sa ba as nothing r en) o t , refl , w , ft , gt , kt , (k₀ , wi , af)
  rise-lead (inBody (cs cl true sa ba as (just _) r en) o c)  s cp p (t , al , (() , _) , ft , gt , kt , _) iv
  rise-lead (inBody (cs cl false sa ba as (just _) r en) o c) s cp p (t , al , (() , _) , ft , gt , kt , _) iv
  rise-lead (inBody (cs cl false sa ba as nothing r en) o c)  s cp p (t , al , (() , _) , ft , gt , kt , _) iv

  -- A subscribe rises nothing, and carries its lead down.
  sub-lead : ∀ {Γ A} (c : Ctx R Γ A) (s : St Γ A) p → Lead ⟨ c , s , subscribing , p ⟩ → NextLead (step ⟨ c , s , subscribing , p ⟩)
  sub-lead c (pend (cold x))          p l = tt
  sub-lead c (pend empty)             p l = tt
  sub-lead c (pend (of xs))           p l = tt
  sub-lead c (pend (map f o))         p l = l
  sub-lead c (pend (scan f z o))      p l = l
  sub-lead c (pend (takeWhile i q o)) p l = l
  sub-lead c (pend (flatMap op f o))  p l = lift λ sh → (λ k _ → Data.List.Relation.Unary.All.[] , tt) , lower l sh
  sub-lead c (pend (connect o b))     p l =
    lift λ sh → proj₁ (fresh-src o p (envAt c)) , proj₂ (fresh-src o p (envAt c)) , ahead-mono (under-sub p [ ix 0 ]) c true (lower l sh)
  sub-lead c (pend (connected x))     p l with closedUp c x
  ... | true  = tt
  ... | false = tt
  sub-lead c (pend (defer d))         p l = lift λ sh → ahead-mono (under-sub p [ ix 1 ]) c true (lower l sh)
  sub-lead c (coldS b l′)             p l = l
  sub-lead c (ofS i q xs)             p l = l
  sub-lead c doneS                    p l = l
  sub-lead c (mapS f s)               p l = l
  sub-lead c (scanS f z s)            p l = l
  sub-lead c (cutS l′ a s)            p l = l
  sub-lead c (lnS b s)                p l = l
  sub-lead c (takeS i q w s)          p l = l
  sub-lead c (flatS op f d n q o ls)  p l = l
  sub-lead c (connS k o b)            p l = l
  sub-lead c (joinS j g x ib)         p l = l

  -- THE PICK: the run of the least mark leads every frame above it.
  lead-next : ∀ k → Base k → Order k → NextLead (step k)
  lead-next ⟨ c , s , rising e , p ⟩    b o = rise-lead c s e p (Order.lead o) (b & o)
  lead-next ⟨ c , s , subscribing , p ⟩ b o = sub-lead c s p (Order.lead o)
  lead-next ⟨ c , s , absorbed , p ⟩    b o with search top (plug c s) in e
  ... | nothing = tt
  ... | just (found (_ , _ , c′ , s′) m key) with search-hit (plug c s) e
  ...   | pl , _ = run-lead (plug c s) p e
                     (λ q e′ s″ kq oe al → s′ , al , subst₂ (λ k x → Won (k , x) c′ s′) kq oe (search-won (plug c s) (proj₁ (Order.shape o)) e)
                        , subst Frag (sym pl) (proj₁ (Order.shape o)) , subst (Gh top) (sym pl) (gh-firm (plug c s) (proj₂ (Order.shape o)) (Order.told o))
                        , subst Keys (sym pl) (proj₂ (Order.shape o))
                        , key , subst (λ k → Within k q) (sym kq) ([] , sym (++-identityʳ q)) , causal-aloft (Order.causal o) c′ s′ pl (found-own (plug c s) e))

  -- A takeWhile failing a value ends one past it, what the frames above
  -- saw of the value's run.
  rise-take-keys : ∀ {Γ A} (c : Ctx R Γ A) i q (s : St Γ A) a p → Inv ⟨ inTake i q free c , s , rising (nx a) , p ⟩
                 → NextKeys (step ⟨ inTake i q free c , s , rising (nx a) , p ⟩)
  rise-take-keys c i q s a p v with q a in e | i
  ... | true  | _     = tt , proj₂ (Order.shape (Inv.ord v))
  ... | false | true  = take-here p a (stateᴺ (gh s) (envAt c)) (proj₁ (Order.flight (Inv.ord v))) , proj₂ (Order.shape (Inv.ord v))
  ... | false | false = keys-above c (takeS false q (cpAt p) s) (Base.ctxWf (Inv.base v))
                          (above-≋ c true (take-excl q (gh s) (envAt c) a p e) (proj₂ (proj₂ (Order.flight (Inv.ord v)))))
                          (take-here p a (stateᴺ (gh s) (envAt c)) (proj₁ (Order.flight (Inv.ord v))) , proj₂ (Order.shape (Inv.ord v)))

  -- A value a lane passes on leaves its merge keyed without it.
  rise-lane-keys : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) pre post (s : St Γ B) b p
                 → Inv ⟨ inLanes op f d n q o pre post c , s , rising (nx b) , p ⟩ → alive s ≡ true
                 → Keyed (flatS op f d n q o (pre ʳ++ s ∷ post)) (envAt c)
  rise-lane-keys c op f d n q o pre post s b p v a =
    subst₂ (FlatAt ρ O) (sym L) P (flat-drop (states (lanesL post) ρ) (gh s) ρ b p fa)
    , proj₁ (proj₂ (proj₁ (proj₂ fl)))
    , keyedL-ʳ++ pre (proj₁ (proj₂ (proj₂ (proj₁ (proj₂ fl))))) (proj₂ (Order.shape (Inv.ord v)) , proj₁ (proj₂ (proj₂ (proj₂ (proj₁ (proj₂ fl))))))
    where
      ρ  = envAt c
      O  = outerᴺ (lane f) (outerG d (gh o)) ρ
      h  = risen (gh s) ρ (nx b) p
      fl = Order.flight (Inv.ord v)
      fa : FlatAt ρ O (laneRuns (reverse pre) post true ρ h) (outerT d (gh o) ρ (poolRuns (reverse pre) post true ρ h))
      fa = subst (λ x → FlatAt ρ O (laneRuns (reverse pre) post x ρ h) (outerT d (gh o) ρ (poolRuns (reverse pre) post x ρ h))) a
             (proj₁ (proj₁ (proj₂ fl)))
      L : states (lanesL (pre ʳ++ s ∷ post)) ρ ≡ laneRuns (reverse pre) post true ρ (stateᴺ (gh s) ρ)
      L = toʳ (λ ls → states (lanesL ls) ρ ≡ laneRuns (reverse pre) post true ρ (stateᴺ (gh s) ρ)) pre
            (trans (lanes-runs (reverse pre) s post ρ) (cong (λ x → laneRuns (reverse pre) post x ρ (stateᴺ (gh s) ρ)) a))
      P : outerT d (gh o) ρ (poolRuns (reverse pre) post true ρ (stateᴺ (gh s) ρ)) ≡ cutᴺ (poolG d (gh o) (deadL (pre ʳ++ s ∷ post))) ρ
      P = toʳ (λ ls → outerT d (gh o) ρ (poolRuns (reverse pre) post true ρ (stateᴺ (gh s) ρ)) ≡ cutᴺ (poolG d (gh o) (deadL ls)) ρ) pre
            (lanes-P d o (reverse pre) s post ρ a)

  -- A value a body passes on leaves its connect keyed without it.
  rise-body-keys : ∀ {Γ X B} (c : Ctx R Γ B) k (o : St Γ X) (s : St (X ∷ Γ) B) b p → Inv ⟨ inBody k o c , s , rising (nx b) , p ⟩
                 → Keyed (connS k o s) (envAt c)
  rise-body-keys c k o s b p v =
    conn-drop k (gh s) (envAt (inBody k o c)) b p (proj₁ (proj₁ (proj₂ (Order.flight (Inv.ord v)))))
    , proj₁ (proj₂ (proj₁ (proj₂ (Order.flight (Inv.ord v))))) , proj₂ (Order.shape (Inv.ord v))

  -- A rise through any other frame keeps its node's own; one absorbed
  -- leaves the frames above keyed of what it leaves running.
  rise-keys : ∀ {Γ A} (c : Ctx R Γ A) (s : St Γ A) e p → Inv ⟨ c , s , rising e , p ⟩ → NextKeys (step ⟨ c , s , rising e , p ⟩)
  rise-keys top                               s (nx a) p v = proj₂ (Order.shape (Inv.ord v))
  rise-keys top                               s cp     p v = tt
  rise-keys (inMap f c)                       s e      p v = tt , proj₂ (Order.shape (Inv.ord v))
  rise-keys (inScan f z c)                    s (nx a) p v = tt , proj₂ (Order.shape (Inv.ord v))
  rise-keys (inScan f z c)                    s cp     p v = tt , proj₂ (Order.shape (Inv.ord v))
  rise-keys (inCut true a c)                  s e      p v = tt , proj₂ (Order.shape (Inv.ord v))
  rise-keys (inCut false a c)                 s e      p v =
    keys-above c (cutS false a s) (Base.ctxWf (Inv.base v)) (above-≋ c true (rested-risen (gh s) (envAt c) e p) (proj₂ (Order.flight (Inv.ord v)))) (tt , proj₂ (Order.shape (Inv.ord v)))
  rise-keys (inLn b c)                        s e      p v = tt , proj₂ (Order.shape (Inv.ord v))
  rise-keys (inTake i q free c)               s (nx a) p v = rise-take-keys c i q s a p v
  rise-keys (inTake i q free c)               s cp     p v = tt , proj₂ (Order.shape (Inv.ord v))
  -- a takeWhile already over absorbs what reaches it: the frames above
  -- saw only what it leaves running
  rise-keys (inTake i q (cpAt r) c)           s e      p v =
    keys-above c (takeS i q (cpAt r) s) (Base.ctxWf (Inv.base v)) (above-≋ c true (ending-risen (r ⊕ [ last ]) (gh s) (envAt c) e p) (proj₂ (proj₂ (Order.flight (Inv.ord v)))))
      (takeAt-risen (cpAt r) (gh s) (envAt c) e p (proj₁ (proj₂ (Order.flight (Inv.ord v)))) , proj₂ (Order.shape (Inv.ord v)))
  rise-keys (inTake i q (cutAt r) c)          s e      p v =
    keys-above c (takeS i q (cutAt r) s) (Base.ctxWf (Inv.base v)) (above-≋ c true (rested-risen (gh s) (envAt c) e p) (proj₂ (proj₂ (Order.flight (Inv.ord v))))) (tt , proj₂ (Order.shape (Inv.ord v)))
  rise-keys (inTake i q (overAt r) c)         s e      p v =
    keys-above c (takeS i q (overAt r) s) (Base.ctxWf (Inv.base v)) (above-≋ c true (rested-risen (gh s) (envAt c) e p) (proj₂ (proj₂ (Order.flight (Inv.ord v))))) (tt , proj₂ (Order.shape (Inv.ord v)))
  rise-keys (inOuter op f d n q ls c)         s (nx a) p v = rise-admit-keys c op f d n q ls s a p v
  rise-keys (inOuter op f d n q ls c)         s cp     p v = rise-outer-end-keys c op f d n q ls s p v
  rise-keys (inLanes op f d n q o pre post c) s (nx b) p v with alive s in a
  ... | true  = rise-lane-keys c op f d n q o pre post s b p v a
  ... | false = rise-dead-keys c op f d n q o pre post s (nx b) p v a
  rise-keys (inLanes op f d n q o pre post c) s cp     p v with alive s in a
  ... | true  = rise-lane-end-keys c op f d n q o pre post s p v
  ... | false = rise-dead-keys c op f d n q o pre post s cp p v a
  rise-keys (inSrc k b c)                     s e      p v = rise-src-keys c k b s e p v
  rise-keys (inBody k o c)                    s (nx b) p v = rise-body-keys c k o s b p v
  rise-keys (inBody k o c)                    s cp     p v = rise-body-end-keys c k o s p v

  -- A subscribe begun: a former wrapping an idle node keeps the tree's
  -- run where it was (`keys-swap`); a generator's ghost is its
  -- subscription's run, which the flight already keys (`sub-swap`).
  sub-swap : ∀ {Γ A} (c : Ctx R Γ A) (o : Obs Timeline Γ A) p (t : St Γ A) → Inv ⟨ c , pend o , subscribing , p ⟩ → flagOf t ≡ true
           → stateᴺ (subscribe o p) (envAt c) ≋ stateᴺ (gh t) (envAt c) → Keyed t (envAt c) → Keys (plug c t)
  sub-swap c o p t v e x k =
    keys-above c t (Base.ctxWf (Inv.base v)) (subst (λ f → Above c f (stateᴺ (gh t) (envAt c))) (sym e) (above-≋ c true x (proj₂ (Order.flight (Inv.ord v))))) k

  cold-≋ : ∀ {Γ A} p (m : From A 0) (ρ : NEnv Γ) → stateᴺ (startᶜ p m) ρ ≋ stateᴺ (gh (coldS true (opening p m))) ρ
  cold-≋ p (atᶠ zero _ b)    ρ = ≋-by refl refl
  cold-≋ p (atᶠ (suc t) _ b) ρ = ≋-by refl refl
  cold-≋ p done             ρ = ≋-by refl refl
  cold-≋ p silentᶠ          ρ = ≋-by refl refl

  -- A merge of an idle outer and no lanes is idle, and keys nothing yet
  -- under its mark.
  flat-idle : ∀ {Γ A B} op (f : A → Obs Timeline Γ B) (ρ : NEnv Γ) → stateᴺ idleᶜ ρ ≋ stateᴺ (flatMapᶜ op (lane f) (just idleᶜ) [] [] idleᶜ) ρ
  flat-idle op f ρ = ≋-by refl refl

  fresh-flat : ∀ {Γ A B} p (f : A → Obs Timeline Γ B) (ρ : NEnv Γ) → FlatKeys p (outerᴺ (lane f) (just idleᶜ) ρ) [] (cutᴺ (idleᶜ {B = B}) ρ) []
  fresh-flat p f ρ = []ᴷ , tt , Data.List.Relation.Unary.All.[] , (record { spread = tt } , record { every = tt } , everyT-idle) , sortedT-idle , everyT-idle , everyT-idle , flatT-idle

  begin-keys : ∀ {Γ A} (c : Ctx R Γ A) (o : Obs Timeline Γ A) p → Inv ⟨ c , pend o , subscribing , p ⟩
             → NextKeys (step ⟨ c , pend o , subscribing , p ⟩)
  begin-keys c (cold x) p v = sub-swap c (cold x) p _ v refl e (shape-≋ e (proj₁ (Order.flight (Inv.ord v))) , tt)
    where e = cold-≋ p (timelineAt x p) (envAt c)
  begin-keys c empty             p v = sub-swap c empty p (ofS 0 p []) v refl (≋-by refl refl) (proj₁ (Order.flight (Inv.ord v)) , tt)
  begin-keys c (of xs)           p v = sub-swap c (of xs) p (ofS 0 p xs) v refl (≋-by refl refl) (proj₁ (Order.flight (Inv.ord v)) , tt)
  begin-keys c (map f s)         p v =
    keys-swap c (pend (map f s)) (mapS f (pend s)) (Base.ctxWf (Inv.base v)) (Order.shape (Inv.ord v)) refl (≋-by refl refl) (tt , tt , tt)
  begin-keys c (scan f z s)      p v =
    keys-swap c (pend (scan f z s)) (scanS f z (pend s)) (Base.ctxWf (Inv.base v)) (Order.shape (Inv.ord v)) refl (≋-by refl refl) (tt , tt , tt)
  begin-keys c (takeWhile i q s) p v =
    keys-swap c (pend (takeWhile i q s)) (takeS i q free (cutS true (attAt p) (pend s))) (Base.ctxWf (Inv.base v)) (Order.shape (Inv.ord v)) refl
      (≋-by refl refl) (tt , tt , tt , tt)
  begin-keys c (flatMap op f s)  p v =
    keys-swap c (pend (flatMap op f s)) (flatS op f false 0 [] (cutS true (attAt p) (pend s)) []) (Base.ctxWf (Inv.base v)) (Order.shape (Inv.ord v)) refl
      (flat-idle op f (envAt c)) ((p , proj₁ fr , proj₂ fr , [] , fresh-flat p f (envAt c)) , (tt , tt , tt) , tt)
    where fr = sub-fresh c (flatMap op f s) p v
  begin-keys c (connect s b)     p v = begin-conn-keys c s b p v
  begin-keys c (connected x)     p v with closedUp c x in ce
  ... | true  = sub-swap c (connected x) p (ofS 0 p []) v refl e (shape-≋ e (proj₁ (Order.flight (Inv.ord v))) , tt)
    where e = joined-over c x p v ce
  ... | false = sub-swap c (connected x) p (joinS p true x []) v refl (≋-by refl refl)
                  (((proj₁ fr , every-lookup (λ h → ¬ Owned p h) (envAt c) (proj₂ fr) x) , tt) , tt)
    where fr = sub-fresh c (connected x) p v
  begin-keys c (defer l)         p v =
    keys-swap c (pend (defer l)) (pend (Later.force l)) (Base.ctxWf (Inv.base v)) (Order.shape (Inv.ord v)) refl (≋-by refl refl) (tt , tt)

  -- A subscribe of a settled node leaves the tree as it was.
  sub-keys : ∀ {Γ A} (c : Ctx R Γ A) (s : St Γ A) p → Inv ⟨ c , s , subscribing , p ⟩ → NextKeys (step ⟨ c , s , subscribing , p ⟩)
  sub-keys c (pend x)                p v = begin-keys c x p v
  sub-keys c (coldS b l)             p v = proj₂ (Order.shape (Inv.ord v))
  sub-keys c (ofS i q xs)            p v = proj₂ (Order.shape (Inv.ord v))
  sub-keys c doneS                   p v = proj₂ (Order.shape (Inv.ord v))
  sub-keys c (mapS f s)              p v = proj₂ (Order.shape (Inv.ord v))
  sub-keys c (scanS f z s)           p v = proj₂ (Order.shape (Inv.ord v))
  sub-keys c (cutS l a s)            p v = proj₂ (Order.shape (Inv.ord v))
  sub-keys c (lnS b s)               p v = proj₂ (Order.shape (Inv.ord v))
  sub-keys c (takeS i q w s)         p v = proj₂ (Order.shape (Inv.ord v))
  sub-keys c (flatS op f d n q o ls) p v = proj₂ (Order.shape (Inv.ord v))
  sub-keys c (connS k o b)           p v = proj₂ (Order.shape (Inv.ord v))
  sub-keys c (joinS j g x ib)        p v = proj₂ (Order.shape (Inv.ord v))

  -- A step keeps every node's own positional facts.
  keys-next : ∀ k → Base k → Order k → NextKeys (step k)
  keys-next ⟨ c , s , rising e , p ⟩    b o = rise-keys c s e p (b & o)
  keys-next ⟨ c , s , subscribing , p ⟩ b o = sub-keys c s p (b & o)
  keys-next ⟨ c , s , absorbed , p ⟩    b o = run-keys c s p (b & o)

  -- A mark run leaves its node weaker: a cold leaf's, its tape moved on
  -- or over.
  run-at : ∀ {Γ A} (c : Ctx R Γ A) {s : St Γ A} {m} p → Owns s m → Causal (plug c s) → NextCaused (took (run c s m p))
  run-at c p (ofO {i = i} {p = q} {xs = xs}) ca with closed c | xs
  ... | true  | _       = causal-run c (done-≼ _) ca
  ... | false | []      = causal-run c (done-≼ _) ca
  ... | false | x ∷ xs′ = causal-run c (of-≼ i q x xs′) ca
  run-at c p (attO {l = l} {p = q} {s = s}) ca with unsubIf (not l) s | unsubIf-≼ (not l) s
  ... | s′ , t | r = causal-run c (att-≼ l q r) ca
  run-at c p (cpO {i = i} {q = q} {p = w} {s = s}) ca = causal-run c (cp-≼ i q w s) ca
  run-at c p (cutO {i = i} {q = q} {p = w} {s = s}) ca with cutᴹ s | cut-≼ s
  ... | s′ , t | r = causal-run c (over-≼ i q w r) ca
  run-at c p (bodyO {k = cs cl sl sa (just q) as ow r e} {o = o} {b = b} _) ca =
    causal-run c (conn-≼ (body-conn cl sl sa q as ow r e) (≼-refl o) (≼-refl b)) ca
  run-at c p (bodyO {k = cs cl sl sa nothing as ow r e} ())
  run-at c p (srcAttO {k = cs cl sl sa ba (just q) ow r e} {o = o} {b = b} _) ca with unsubIf (not sl) o | unsubIf-≼ (not sl) o
  ... | o′ , t | ro = causal-run c (conn-≼ (src-conn cl sl sa ba q ow r e) ro (≼-refl b)) ca
  run-at c p (srcAttO {k = cs cl sl sa ba nothing ow r e} ())
  run-at c p (owedO {k = cs cl sl sa ba as (just q) r e} {o = o} {b = b} _) ca with unsubIf sa o | unsubIf-≼ sa o
  ... | o′ , t | ro = causal-run c (conn-≼ (owed-conn cl sl sa ba as q r e) ro (≼-refl b)) ca
  run-at c p (owedO {k = cs cl sl sa ba as nothing r e} ())
  run-at c p (joinO {j = j} {g = g} {x = x} {q = q} {e = nx a} {ib = ib}) ca = causal-run c (join-≼ j g g x (q , nx a) ib) ca
  run-at c p (joinO {j = j} {g = g} {x = x} {q = q} {e = cp} {ib = ib})   ca = causal-run c (join-≼ j g false x (q , cp) ib) ca
  run-at c p (leafO {b = b} {l = ending e} d)                      ca = causal-run c (cold-over b false (ending e)) ca
  run-at c p (leafO {l = over} ())
  run-at c p (leafO {b = false} {l = play τ u i t fr} d)            ca = causal-run c (cold-over false false (play τ u i t fr)) ca
  run-at c p (leafO {b = true} {l = play τ u i t (emit a k)} d)     ca with closed c
  ... | true  = causal-run c (cold-over true true (play τ u i t (emit a k))) ca
  ... | false = causal-run c (cold-≼ (play τ u i t (emit a k))) ca
  run-at c p (leafO {b = true} {l = play τ u i t (stall k)} d)      ca with closed c
  ... | true  = causal-run c (cold-over true true (play τ u i t (stall k))) ca
  ... | false = causal-run c (cold-≼ (play τ u i t (stall k))) ca
  run-at c p (leafO {b = true} {l = play τ u i t (close k)} d)      ca with closed c
  ... | true  = causal-run c (cold-over true true (play τ u i t (close k))) ca
  ... | false = causal-run c (cold-≼ (play τ u i t (close k))) ca

  -- THE STILL'S SUBTREE, RUN: a mark run keeps the tree causal.
  run-causal : ∀ {Γ A} (c : Ctx R Γ A) (s : St Γ A) p → Inv ⟨ c , s , absorbed , p ⟩ → NextCaused (step ⟨ c , s , absorbed , p ⟩)
  run-causal c s p iv with search top (plug c s) in e
  ... | nothing = tt
  ... | just (found (_ , _ , c′ , s′) m key) with search-hit (plug c s) e
  ...   | pl , own = run-at c′ p own (subst Causal (sym pl) (Order.causal (Inv.ord iv)))

  causal-next : ∀ k → Base k → Order k → NextCaused (step k)
  causal-next ⟨ c , s , rising e , p ⟩    b o = rise-causal c s e p (b & o)
  causal-next ⟨ c , s , subscribing , p ⟩ b o = sub-causal c s p (b & o)
  causal-next ⟨ c , s , absorbed , p ⟩    b o = run-causal c s p (b & o)

  held : ∀ x → NextFrag x → NextKeys x → NextShape x
  held (silent t k)    f h = f , h
  held (value t p a k) f h = f , h
  held (complete p)    f h = tt
  held drained         f h = tt

  shape-next : ∀ k → Base k → Order k → NextShape (step k)
  shape-next k b o = held (step k) (frag-next k b (proj₁ (Order.shape o))) (keys-next k b o)

  -- A step to a value in flight or a subscription keeps its hole's run
  -- in shape, and what every frame above keeps of it.
  flight-owed : ∀ k → Base k → Order k → NextOwed (step k)
  flight-owed ⟨ c , s , rising e , p ⟩    b o = rise-owed c s e p o
  flight-owed ⟨ c , s , subscribing , p ⟩ b o = sub-owed c s p o
  flight-owed ⟨ c , s , absorbed , p ⟩    b o = run-flight c s p (b & o)

  flight-of : ∀ (k : Conf R) → Base k → Shaped k → Owed k → Flight k
  flight-of ⟨ c , s , absorbed , p ⟩    b h _ = flight-held c s p (Base.ctxWf b) h
  flight-of ⟨ c , s , subscribing , p ⟩ _ _ f = f
  flight-of ⟨ c , s , rising e , p ⟩    _ _ f = f

  flown : ∀ x → NextBase x → NextShape x → NextOwed x → NextFlight x
  flown (silent t k)    b h f = flight-of k b h f
  flown (value t p a k) b h f = flight-of k b h f
  flown (complete p)    b h f = tt
  flown drained         b h f = tt

  -- A step keeps its hole's run in shape, and what every frame above
  -- keeps of it.
  flight-next : ∀ k → Base k → Order k → NextFlight (step k)
  flight-next k b o = flown (step k) (base-next k b) (shape-next k b o) (flight-owed k b o)

  joined : ∀ x → NextShape x → NextFlight x → NextLead x → NextCaused x → NextHeard x → NextTold x → NextOrd x
  joined (silent t k)    f g l u e h = order f g l u e h
  joined (value t p a k) f g l u e h = order f g l u e h
  joined (complete p)    f g l u e h = tt
  joined drained         f g l u e h = tt

  -- EVERY STEP KEEPS THE ORDER.
  heard-next : ∀ k → Order k → NextHeard (step k)
  heard-next ⟨ c , s , rising e , p ⟩ o = rise-heard c s e p (Order.heard o)
  heard-next ⟨ c , pend o′ , subscribing , p ⟩ o = begin-heard c o′ p
  heard-next ⟨ c , (coldS xb xl) , subscribing , p ⟩ o = tt
  heard-next ⟨ c , (ofS xi xp xxs) , subscribing , p ⟩ o = tt
  heard-next ⟨ c , doneS , subscribing , p ⟩ o = tt
  heard-next ⟨ c , (mapS xf xs) , subscribing , p ⟩ o = tt
  heard-next ⟨ c , (scanS xf xz xs) , subscribing , p ⟩ o = tt
  heard-next ⟨ c , (cutS xl xa xs) , subscribing , p ⟩ o = tt
  heard-next ⟨ c , (lnS xb xs) , subscribing , p ⟩ o = tt
  heard-next ⟨ c , (takeS xi xq xw xs) , subscribing , p ⟩ o = tt
  heard-next ⟨ c , (flatS xop xf xd xn xq xo xls) , subscribing , p ⟩ o = tt
  heard-next ⟨ c , (connS xk xo xb) , subscribing , p ⟩ o = tt
  heard-next ⟨ c , (joinS xj xg xx xib) , subscribing , p ⟩ o = tt
  heard-next ⟨ c , s , absorbed , p ⟩ o with search top (plug c s) in e
  ... | nothing = tt
  ... | just (found (_ , _ , c′ , s′) m key) = run-heard c′ p (proj₂ (search-hit (plug c s) e))

  ord-next : ∀ k → Base k → Order k → NextOrd (step k)
  ord-next k b o = joined (step k) (shape-next k b o) (flight-next k b o) (lead-next k b o) (causal-next k b o) (heard-next k o) (told-next k b o)

  both : ∀ x → NextBase x → NextOrd x → NextInv x
  both (silent t k)    b o = b & o
  both (value t p a k) b o = b & o
  both (complete p)    b o = tt
  both drained         b o = tt

  inv-next : ∀ k → Inv k → NextInv (step k)
  inv-next k (b & o) = both (step k) (base-next k b) (ord-next k b o)

  -- A tree's first subscription owns nothing: causal.
  load-causal : (o : Obs Timeline [] R) → Causal (whole (Machine.load o))
  load-causal o = (λ { (_ , ()) }) , tt

  inv-load : (o : Obs Timeline [] R) → Inv (Machine.load o)
  inv-load o = base-load o & order (tt , tt , tt) (flight-load o) (lift (λ _ → tt)) (load-causal o) tt tt

  -- A settled node anywhere in a tree the invariant holds of, absorbed at
  -- the same position: the invariant at it.
  inv-at : ∀ {Γ A} (c : Ctx R Γ A) (s : St Γ A) p → Unpended s → Wf (plug c s) → Held (plug c s) → Causal (plug c s)
         → Toldˢ none (plug c s) → Inv ⟨ c , s , absorbed , p ⟩
  inv-at c s p u w f t g = base-at c s p u w & order f (flight-held c s p (proj₁ (wf-split c s u w)) f) tt t tt g
