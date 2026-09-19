------------------------------------------------------------------
-- THE BUILDER AT ONE BOUND.
------------------------------------------------------------------

-- WHY THE BOUND IS A MODULE PARAMETER.  What a connect spends is the
-- general walk at the floor directly above the slot it is connecting;
-- the walk is written at the foot of this module, and it reaches the
-- term face back HERE -- a frame's function is handed to the walk with
-- a fresh accessibility, so nothing around that loop shrinks.  What
-- does shrink is the BOUND, and a parameter is how a module says so:
-- everything below is the builder AT `m`, written over the levels
-- beneath `m` it was handed.
--
-- THE MEASURE IS A COUNT THE STORE CARRIES, AND IT ORDERS THE ROUND
-- TRIP THE FLOOR CANNOT.  What a connect consumes is a share that has
-- not been connected yet -- the arm is guarded by the slot's absence
-- from the connected list and adds it on the way out -- so the number
-- of slots that are shared and unconnected strictly drops across
-- exactly the call that raises the floor measure.  Nothing anywhere
-- puts a slot back, so every other arm leaves that number alone or
-- lowers it.
--
-- AND IT IS A COUNT RATHER THAN AN INVARIANT, WHICH IS WHY THE ROUTE
-- BELOW DOES NOT REACH IT.  That route dies because the candidate
-- cannot be a premise of a statement about the store; a natural number
-- is not the candidate, so the bound rides as an inert index and the
-- type descent is untouched.
--
-- SO THE CONNECT ARM IS THE ONLY ARM THAT READS `beneath`.  Its guard
-- holds a slot that is shared and unconnected, which is exactly the
-- witness that the count drops, so the level it descends to is strictly
-- below this one -- and the pair it needs there, the walk together with
-- the term face, arrives from the parameter rather than from a forward
-- reference.  A zero bound needs no arm of its own: the witness IS the
-- proof that one does not arise.
--
-- DEAD ROUTE: merging the term face and the walk into one block puts
--   both recursions under one measure, and the two move in OPPOSITE
--   directions: a connect drops to the floor `toℕ i` its own slot names,
--   while a fan-out only ever rises to `suc (toℕ i)`, so neither `n ∸ lo`
--   nor the input ceiling orders the pair.  What does order it is that a
--   share connects AT MOST ONCE EVER, which is a fact about the store --
--   and `Rx.Evaluator.Reducible`'s own dead route records why a store
--   invariant cannot be a premise of the candidate.

open import Data.Bool using (true; false; T; _∧_)
open import Data.Fin using (Fin; toℕ)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; s≤s; _+_; _∸_; _<ᵇ_)
open import Data.Nat.Induction using (<-wellFounded-fast)
open import Data.Nat.Properties using (_<?_; ≮⇒≥; ≤-refl; ≤-trans; m≤n+m; m≤m+n; <ᵇ⇒<)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Vec using (lookup)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary using (yes; no)

open import Rx.Prim using (Tick; hot; cold)
open import Rx.Exp using (Ty; unitᵗ; boolᵗ; natᵗ; uniqᵗ; _×ᵗ_; _+ᵗ_; obs; listᵗ; Ctx; Closed; Val; Exp; Tm; Fn; FnClo;
  Env; []ᵉ; _∷ᵉ_; evalWith; unfoldμ; input; ofᵉ; emptyᵉ; takeᵉ; batchSyncᵉ; mapᵉ; scanᵉ;
  mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ; mintᵉ; varᵗ; unit̂; bool̂; nat̂; pairᵗ;
  fstᵗ; sndᵗ; inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ; nilᵗ; consᵗ; foldᵗ; add; sub; mul; eqᵖ;
  ltᵖ; eqᵘ; notᵖ; inputsBelowᵉ; inputsBelowᵗ; inputsBelowᵗˢ)
open import Rx.Exp.Guarded using (gsizeᵉ; gsizeᵗ; gsizeᵗˢ; gsize-unfoldμ)
open import Rx.Inputs-Below using (ib-unfoldμ; ib-topᵉ; ib-topᵗ)
open import Decide using (∧ˡ; ∧ʳ)
open import Rx.Mint using (nodeᵏ; regᵏ; sourceᵏ; ordinalᵏ; freshId; setAt)
open import Rx.Slots using (scripted; shared)
open import Rx.Evaluator using (Sched; EvalSt; Path; root; share-sink; _↠_; map-f; scan-f; take-f; batchSync-f; from-inner;
  thru-outer; mergeAllᵒ; switchᵒ; exhaustᵒ; cell-st; take-st; batchSync-st; mergeAll-st;
  switch-st; exhaust-st; installNode; memberSource; register; atSlot; atDyn; lowerFloor;
  resolve)
open import Rx.Evaluator.Domain using (subscribeE⇓; subs-floor; subs-shared; subs-hot-done; subs-hot-live; subs-cold-sync;
  subs-cold-async; subs-of; subs-empty; subs-take-zero; subs-take-suc; subs-map; subs-scan;
  subs-merge-all; subs-switch-all; subs-exhaust-all; subs-μ; subs-defer; subs-mint; connect;
  slot-spent; slot-join; slot-connect)
open import Rx.Evaluator.Reducible using (Out; Red; Handles; RedFn; RedEnv; redDatas; redLookup; redFoldVals; unconnected; unconn-connect)
open import Rx.Evaluator.Unconnected using (unconn-emits)
open import Rx.Evaluator.Builder.Frames using (Walk; monus-sink; handles-share; emits!; handles-root; handles-map; handles-scan;
  handles-take; handles-batchSync; handles-from-inner; handles-thru-outer; subsAll!;
  subsBatchSync!; Below)

module Rx.Evaluator.Builder.Level
  (m : ℕ)
  (beneath : ∀ {m′} → m′ < m → Below m′)
  where

------------------------------------------------------------------
-- THE FUNDAMENTAL THEOREM AT TERMS.
------------------------------------------------------------------

-- THE CEILING IS A MEASURE COMPONENT, NOT A HYPOTHESIS.  The walk
-- carries a stratum `k` with the guard `T (inputsBelowᵉ k b)` and an
-- `Acc` on it, ordered ABOVE the g-size accessibility.  A term step
-- holds the ceiling and shrinks the size; the SHARED-SLOT step drops
-- the ceiling to the slot's own index -- which its `ok` field licenses
-- -- and lets the size go free.  That is what funds the descent into a
-- definition drawn from the slot table rather than from the term, and
-- an input's g-size being zero is why nothing smaller could.
--
-- AND THE PATH IS THREADED, NEVER WALKED.  Every arm that pushes a
-- frame builds the longer path's `Handles` from the one it was handed,
-- so nothing here reaches the general walk -- which is what keeps this
-- block mutual with itself alone.
mutual
  redExpAcc : ∀ {n} {Γ : Ctx n} {Θ t} (b : Exp Γ [] [] Θ t)
              (σ : Env Γ Θ) → RedEnv m σ
            → (k : ℕ) → T (inputsBelowᵉ k b) → Acc _<_ k
            → Acc _<_ (gsizeᵉ b) → Red {Γ = Γ} m (obs t) (Θ , b , σ)
  redExpAcc (input i) σ rσ k ok aK a κ hκ now sched st le =
    red-input i σ k ok aK κ hκ now sched st le
  redExpAcc (ofᵉ ts) σ rσ k ok aK (acc rs) κ hκ now sched st le =
    let ((out , sched₁ , st₁) , d) =
          emits! κ (proj₁ hκ) now (map (λ tm → evalWith tm σ) ts)
            (redTmsAcc ts σ rσ k ok aK (rs ≤-refl)) sched st le
        (r , c) = proj₂ hκ now sched₁ st₁ (≤-trans (unconn-emits d) le)
    in _ , subs-of d c
  redExpAcc emptyᵉ σ rσ k ok aK a κ hκ now sched st le =
    let (r , c) = proj₂ hκ now sched st le in r , subs-empty c
  redExpAcc (takeᵉ c b) σ rσ k ok aK (acc rs) κ hκ now sched st le
    with evalWith c σ in ceq
  ... | zero  = let (r , cl) = proj₂ hκ now sched st le in r , subs-take-zero ceq cl
  ... | suc j =
        let nid = freshId nodeᵏ (Sched.mint sched)
            okb = ∧ʳ (inputsBelowᵗ k c) (inputsBelowᵉ k b) ok
            (r , d) =
              redExpAcc b σ rσ k okb aK
                (rs (s≤s (m≤n+m (gsizeᵉ b) (gsizeᵗ c))))
                (take-f nid ↠ κ) (handles-take nid κ hκ) now
                (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) })
                (installNode nid (take-st (suc j)) st) le
        in r , subs-take-suc ceq refl d
  redExpAcc (batchSyncᵉ {t = u} b) σ rσ k ok aK (acc rs) κ hκ now sched st le =
    let nid = freshId nodeᵏ (Sched.mint sched)
        ((out , sched₁ , st₁) , d) =
          redExpAcc b σ rσ k ok aK (rs ≤-refl)
            (batchSync-f nid ↠ κ) (handles-batchSync nid κ hκ) now
            (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) })
            (installNode nid (batchSync-st {t = u} true []) st) le
    in subsBatchSync! κ (proj₁ hκ) nid now sched st out sched₁ st₁ le refl d
  redExpAcc (mapᵉ f b) σ rσ k ok aK (acc rs) κ hκ now sched st le =
    let fn  = _ , f , σ
        okf = ∧ˡ (inputsBelowᵗ k f) (inputsBelowᵉ k b) ok
        okb = ∧ʳ (inputsBelowᵗ k f) (inputsBelowᵉ k b) ok
        rf  = redFnAcc f σ rσ k okf aK (rs (s≤s (m≤m+n (gsizeᵗ f) (gsizeᵉ b))))
        (r , d) =
          redExpAcc b σ rσ k okb aK
            (rs (s≤s (m≤n+m (gsizeᵉ b) (gsizeᵗ f))))
            (map-f fn ↠ κ) (handles-map fn κ rf hκ) now sched st le
    in r , subs-map d
  redExpAcc (scanᵉ f z b) σ rσ k ok aK (acc rs) κ hκ now sched st le =
    let nid  = freshId nodeᵏ (Sched.mint sched)
        fn   = _ , f , σ
        rest = ∧ʳ (inputsBelowᵗ k f) (inputsBelowᵗ k z ∧ inputsBelowᵉ k b) ok
        okb  = ∧ʳ (inputsBelowᵗ k z) (inputsBelowᵉ k b) rest
        (r , d) =
          redExpAcc b σ rσ k okb aK
            (rs (s≤s (≤-trans (m≤n+m (gsizeᵉ b) (gsizeᵗ z))
                              (m≤n+m (gsizeᵗ z + gsizeᵉ b) (gsizeᵗ f)))))
            (scan-f fn nid ↠ κ) (handles-scan fn nid κ hκ) now
            (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) })
            (installNode nid (cell-st (evalWith z σ)) st) le
    in r , subs-scan refl d
  redExpAcc (mergeAllᵉ {t = u} lim b) σ rσ k ok aK (acc rs) κ hκ now sched st le =
    let (r , d) = subsAll! mergeAllᵒ (mergeAll-st {t = u} lim 0 [] false)
                    (redExpAcc b σ rσ k ok aK (rs ≤-refl)) κ hκ now sched st le
    in r , subs-merge-all d
  redExpAcc (switchAllᵉ b) σ rσ k ok aK (acc rs) κ hκ now sched st le =
    let (r , d) = subsAll! switchᵒ (switch-st nothing false)
                    (redExpAcc b σ rσ k ok aK (rs ≤-refl)) κ hκ now sched st le
    in r , subs-switch-all d
  redExpAcc (exhaustAllᵉ b) σ rσ k ok aK (acc rs) κ hκ now sched st le =
    let (r , d) = subsAll! exhaustᵒ (exhaust-st false false)
                    (redExpAcc b σ rσ k ok aK (rs ≤-refl)) κ hκ now sched st le
    in r , subs-exhaust-all d
  redExpAcc (μᵉ body) σ rσ k ok aK (acc rs) κ hκ now sched st le =
    let ih = redExpAcc (unfoldμ body) σ rσ k (ib-unfoldμ k body ok) aK
               (rs (subst (_< suc (gsizeᵉ body))
                          (sym (gsize-unfoldμ body)) ≤-refl))
        (r , d) = ih κ hκ now sched st le
    in r , subs-μ d
  redExpAcc (varᵉ ()) σ rσ k ok aK a
  redExpAcc (deferᵉ body) σ rσ k ok aK a κ hκ now sched st le =
    _ , subs-defer refl refl refl refl
  redExpAcc (mintᵉ body) σ rσ k ok aK (acc rs) κ hκ now sched st le =
    let src     = freshId sourceᵏ (Sched.mint sched)
        sched′  = record sched { mint = setAt sourceᵏ (suc src) (Sched.mint sched) }
        (r , d) = redExpAcc body (src ∷ᵉ σ) (tt , rσ) k ok aK (rs ≤-refl)
                    κ hκ now sched′ st le
    in r , subs-mint refl d

  -- THE SLOT ARM, WHICH IS FIVE SUB-ARMS OF PROTOCOL AND ONE THAT
  -- SPENDS THE CEILING.  A scripted slot's values are DATA by the
  -- slot's own side condition, so `redDatas` closes them outright; the
  -- ceiling's accessibility is taken apart here rather than passed on,
  -- since `toℕ i < k` is exactly what the guard reduces to at this
  -- former.
  red-input : ∀ {n} {Γ : Ctx n} {Θ} (i : Fin n) (σ : Env Γ Θ) (k : ℕ)
            → T (toℕ i <ᵇ k) → Acc _<_ k
            → Red {Γ = Γ} m (obs (lookup Γ i)) (Θ , input i , σ)
  red-input {Γ = Γ} i σ k ok (acc rsK) {lo = lo} κ hκ now sched st le
      with toℕ i <? lo
  ... | no  ¬below = let (r , c) = proj₂ hκ now sched st le
                     in r , subs-floor (≮⇒≥ ¬below) c
  ... | yes below  with Sched.slots sched i in slEq
  ...   | scripted {ok = okD} (hot async)
          with memberSource (toℕ i) (EvalSt.completedSources st) in doneEq
  ...     | true  = let (r , c) = proj₂ hκ now sched st le
                    in r , subs-hot-done below slEq doneEq c
  ...     | false = _ , subs-hot-live below slEq doneEq refl
  red-input {Γ = Γ} i σ k ok (acc rsK) {lo = lo} κ hκ now sched st le
      | yes below | scripted {ok = okD} (cold sync []) =
        let ((out , sched₁ , st₁) , d) =
              emits! κ (proj₁ hκ) now sync (redDatas _ okD sync) sched st le
            (r , c) = proj₂ hκ now sched₁ st₁ (≤-trans (unconn-emits d) le)
        in _ , subs-cold-sync below slEq d c
  red-input {Γ = Γ} i σ k ok (acc rsK) {lo = lo} κ hκ now sched st le
      | yes below | scripted {ok = okD} (cold sync (dv ∷ ds)) =
        let src   = freshId sourceᵏ (Sched.mint sched)
            ord   = freshId ordinalᵏ (Sched.mint sched)
            rid   = freshId regᵏ (Sched.mint sched)
            sched′ = record sched
                       { mint = setAt regᵏ (suc rid)
                                  (setAt sourceᵏ (suc src)
                                    (setAt ordinalᵏ (suc ord) (Sched.mint sched)))
                       ; live = record { source = src ; ordinal = ord
                                       ; elemTy = lookup Γ i
                                       ; pending = resolve now (dv ∷ ds) }
                                ∷ Sched.live sched }
            (r , d) = emits! κ (proj₁ hκ) now sync (redDatas _ okD sync)
                        sched′ (register rid (atDyn src lo) κ st) le
        in r , subs-cold-async below slEq refl refl refl d
  red-input {Γ = Γ} i σ k ok (acc rsK) {lo = lo} κ hκ now sched st le
      | yes below | shared d {ok = okd} =
        red-input-shared i σ d (rsK (<ᵇ⇒< (toℕ i) k ok))
          κ below now sched slEq st hκ le

  -- THE SIXTH SLOT SUB-ARM, WHICH IS THE ONE THE OTHER FIVE ARE NOT.
  -- A share's definition is an arbitrary term standing in no relation
  -- to `input i`, so it cannot be reached by any descent on the TERM.
  -- The telescope's own side condition is what reaches it instead: a
  -- slot's definition may reference only inputs STRICTLY BELOW that
  -- slot, so the definition is charged against the ceiling `toℕ i`,
  -- which the caller's accessibility has just been taken apart to
  -- supply.
  red-input-shared : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo Θ}
      (i : Fin n) (σ : Env Γ Θ) (d : Closed Γ (lookup Γ i))
      {okd : T (inputsBelowᵉ (toℕ i) d)}
    → Acc _<_ (toℕ i)
    → (κ : Path Γ lo (lookup Γ i) t) (below : toℕ i < lo)
      (now : Tick) (sched : Sched Γ)
    → Sched.slots sched i ≡ shared d {ok = okd}
    → (st : EvalSt e) → Handles {m = m} (lookup Γ i) κ → unconnected sched st ≤ m
    → Σ (Out e) λ r → subscribeE⇓ {e = e} (Θ , input i , σ) κ now sched st r
  red-input-shared {Γ = Γ} i σ d {okd} aI κ below now sched slEq st hκ le
      with memberSource (toℕ i) (EvalSt.completedSources st) in doneEq
  ... | true  = let (r , c) = proj₂ hκ now sched st le
                in r , subs-shared {κ = κ} {below = below} slEq
                         (slot-spent {κ = κ} {below = below} doneEq c)
  ... | false with memberSource (toℕ i) (EvalSt.connectedShares st) in connEq
  ...   | true  = _ , subs-shared {κ = κ} {below = below} slEq
                        (slot-join {κ = κ} {below = below} doneEq connEq refl)
  ...   | false =
          let B   = beneath (≤-trans (unconn-connect i sched st slEq connEq) le)
              rid = freshId regᵏ (Sched.mint sched)
              (r , dv) =
                Below.term B d []ᵉ tt (toℕ i) okd aI
                  (<-wellFounded-fast (gsizeᵉ d))
                  (share-sink i ≤-refl)
                  (handles-share i ≤-refl (Below.walk B)) now
                  (record sched { mint = setAt regᵏ (suc rid) (Sched.mint sched) })
                  (register rid (atSlot i) (lowerFloor below κ)
                    (record st
                      { connectedShares = toℕ i ∷ EvalSt.connectedShares st }))
                  ≤-refl
          in r , subs-shared {κ = κ} {below = below} slEq
                   (slot-connect doneEq connEq (connect refl dv))

  -- THE FUNDAMENTAL THEOREM AT TERMS, which is where the embedding
  -- former hands the recursion back to the expression face.
  redTmAcc : ∀ {n} {Γ : Ctx n} {Θ u} (tm : Tm Γ [] [] Θ u)
             (σ : Env Γ Θ) → RedEnv m σ
           → (k : ℕ) → T (inputsBelowᵗ k tm) → Acc _<_ k
           → Acc _<_ (gsizeᵗ tm) → Red m u (evalWith tm σ)
  redTmAcc (varᵗ x) σ rσ k ok aK a = redLookup σ rσ x
  redTmAcc unit̂     σ rσ k ok aK a = tt
  redTmAcc (bool̂ b) σ rσ k ok aK a = tt
  redTmAcc (nat̂ j)  σ rσ k ok aK a = tt
  redTmAcc (pairᵗ x y) σ rσ k ok aK (acc rs) =
      redTmAcc x σ rσ k (∧ˡ (inputsBelowᵗ k x) (inputsBelowᵗ k y) ok) aK
        (rs (s≤s (m≤m+n (gsizeᵗ x) (gsizeᵗ y))))
    , redTmAcc y σ rσ k (∧ʳ (inputsBelowᵗ k x) (inputsBelowᵗ k y) ok) aK
        (rs (s≤s (m≤n+m (gsizeᵗ y) (gsizeᵗ x))))
  redTmAcc nilᵗ σ rσ k ok aK a = []ᵃ
  redTmAcc (consᵗ x xs) σ rσ k ok aK (acc rs) =
      redTmAcc x σ rσ k (∧ˡ (inputsBelowᵗ k x) (inputsBelowᵗ k xs) ok) aK
        (rs (s≤s (m≤m+n (gsizeᵗ x) (gsizeᵗ xs))))
    ∷ᵃ redTmAcc xs σ rσ k (∧ʳ (inputsBelowᵗ k x) (inputsBelowᵗ k xs) ok) aK
        (rs (s≤s (m≤n+m (gsizeᵗ xs) (gsizeᵗ x))))
  redTmAcc (foldᵗ l z f) σ rσ k ok aK (acc rs) =
    redFoldVals f σ
      (λ rx ra →
        redTmAcc f (_ ∷ᵉ _ ∷ᵉ σ) (rx , ra , rσ) k
          (∧ʳ (inputsBelowᵗ k z) (inputsBelowᵗ k f)
            (∧ʳ (inputsBelowᵗ k l) (inputsBelowᵗ k z ∧ inputsBelowᵗ k f) ok)) aK
          (rs (s≤s (≤-trans (m≤n+m (gsizeᵗ f) (gsizeᵗ z))
                            (m≤n+m (gsizeᵗ z + gsizeᵗ f) (gsizeᵗ l))))))
      (redTmAcc l σ rσ k
        (∧ˡ (inputsBelowᵗ k l) (inputsBelowᵗ k z ∧ inputsBelowᵗ k f) ok) aK
        (rs (s≤s (m≤m+n (gsizeᵗ l) (gsizeᵗ z + gsizeᵗ f)))))
      (redTmAcc z σ rσ k
        (∧ˡ (inputsBelowᵗ k z) (inputsBelowᵗ k f)
          (∧ʳ (inputsBelowᵗ k l) (inputsBelowᵗ k z ∧ inputsBelowᵗ k f) ok)) aK
        (rs (s≤s (≤-trans (m≤m+n (gsizeᵗ z) (gsizeᵗ f))
                          (m≤n+m (gsizeᵗ z + gsizeᵗ f) (gsizeᵗ l))))))
  redTmAcc (fstᵗ q) σ rσ k ok aK (acc rs) =
    proj₁ (redTmAcc q σ rσ k ok aK (rs ≤-refl))
  redTmAcc (sndᵗ q) σ rσ k ok aK (acc rs) =
    proj₂ (redTmAcc q σ rσ k ok aK (rs ≤-refl))
  redTmAcc (inlᵗ x) σ rσ k ok aK (acc rs) = redTmAcc x σ rσ k ok aK (rs ≤-refl)
  redTmAcc (inrᵗ x) σ rσ k ok aK (acc rs) = redTmAcc x σ rσ k ok aK (rs ≤-refl)
  redTmAcc (caseᵗ sc l r) σ rσ k ok aK (acc rs)
    with ∧ˡ (inputsBelowᵗ k sc) (inputsBelowᵗ k l ∧ inputsBelowᵗ k r) ok
       | ∧ʳ (inputsBelowᵗ k sc) (inputsBelowᵗ k l ∧ inputsBelowᵗ k r) ok
  ... | oksc | rest
    with evalWith sc σ
       | redTmAcc sc σ rσ k oksc aK
           (rs (s≤s (m≤m+n (gsizeᵗ sc) (gsizeᵗ l + gsizeᵗ r))))
  ... | inj₁ x | q =
    redTmAcc l (x ∷ᵉ σ) (q , rσ) k
      (∧ˡ (inputsBelowᵗ k l) (inputsBelowᵗ k r) rest) aK
      (rs (s≤s (≤-trans (m≤m+n (gsizeᵗ l) (gsizeᵗ r))
                        (m≤n+m (gsizeᵗ l + gsizeᵗ r) (gsizeᵗ sc)))))
  ... | inj₂ y | q =
    redTmAcc r (y ∷ᵉ σ) (q , rσ) k
      (∧ʳ (inputsBelowᵗ k l) (inputsBelowᵗ k r) rest) aK
      (rs (s≤s (≤-trans (m≤n+m (gsizeᵗ r) (gsizeᵗ l))
                        (m≤n+m (gsizeᵗ l + gsizeᵗ r) (gsizeᵗ sc)))))
  redTmAcc (ifᵗ c x y) σ rσ k ok aK (acc rs)
    with ∧ʳ (inputsBelowᵗ k c) (inputsBelowᵗ k x ∧ inputsBelowᵗ k y) ok
  ... | rest with evalWith c σ
  ... | true  =
    redTmAcc x σ rσ k (∧ˡ (inputsBelowᵗ k x) (inputsBelowᵗ k y) rest) aK
      (rs (s≤s (≤-trans (m≤m+n (gsizeᵗ x) (gsizeᵗ y))
                        (m≤n+m (gsizeᵗ x + gsizeᵗ y) (gsizeᵗ c)))))
  ... | false =
    redTmAcc y σ rσ k (∧ʳ (inputsBelowᵗ k x) (inputsBelowᵗ k y) rest) aK
      (rs (s≤s (≤-trans (m≤n+m (gsizeᵗ y) (gsizeᵗ x))
                        (m≤n+m (gsizeᵗ x + gsizeᵗ y) (gsizeᵗ c)))))
  redTmAcc (primᵗ add x) σ rσ k ok aK a  = tt
  redTmAcc (primᵗ sub x) σ rσ k ok aK a  = tt
  redTmAcc (primᵗ mul x) σ rσ k ok aK a  = tt
  redTmAcc (primᵗ eqᵖ x) σ rσ k ok aK a  = tt
  redTmAcc (primᵗ ltᵖ x) σ rσ k ok aK a  = tt
  redTmAcc (primᵗ eqᵘ x) σ rσ k ok aK a  = tt
  redTmAcc (primᵗ notᵖ x) σ rσ k ok aK a = tt
  redTmAcc (strmᵗ e) σ rσ k ok aK (acc rs) =
    redExpAcc e σ rσ k ok aK (rs ≤-refl)

  redTmsAcc : ∀ {n} {Γ : Ctx n} {Θ u} (ts : List (Tm Γ [] [] Θ u))
              (σ : Env Γ Θ) → RedEnv m σ
            → (k : ℕ) → T (inputsBelowᵗˢ k ts) → Acc _<_ k
            → Acc _<_ (gsizeᵗˢ ts)
            → All (Red m u) (map (λ tm → evalWith tm σ) ts)
  redTmsAcc []       σ rσ k ok aK a = []ᵃ
  redTmsAcc (x ∷ xs) σ rσ k ok aK (acc rs) =
      redTmAcc x σ rσ k (∧ˡ (inputsBelowᵗ k x) (inputsBelowᵗˢ k xs) ok) aK
        (rs (s≤s (m≤m+n (gsizeᵗ x) (gsizeᵗˢ xs))))
    ∷ᵃ redTmsAcc xs σ rσ k (∧ʳ (inputsBelowᵗ k x) (inputsBelowᵗˢ k xs) ok) aK
        (rs (s≤s (m≤n+m (gsizeᵗˢ xs) (gsizeᵗ x))))

  -- A FRAME'S FUNCTION, PAIRED WITH THE AMBIENT ENVIRONMENT AND THEN
  -- APPLIED, is the term face at one more entry.
  redFnAcc : ∀ {n} {Γ : Ctx n} {Θ s u} (f : Fn Γ [] [] Θ s u)
             (σ : Env Γ Θ) → RedEnv m σ
           → (k : ℕ) → T (inputsBelowᵗ k f) → Acc _<_ k
           → Acc _<_ (gsizeᵗ f) → RedFn {Γ = Γ} m (Θ , f , σ)
  redFnAcc f σ rσ k ok aK a {v} p = redTmAcc f (v ∷ᵉ σ) (p , rσ) k ok aK a

------------------------------------------------------------------
-- THE TOP LINE, AND THE SAME CLAIM WITH NO OBLIGATION LEFT.
------------------------------------------------------------------

-- A value at observable type IS a body paired with an environment, and
-- an entry of that environment at observable type is another such
-- value, so nothing could be claimed about the pair that was not
-- already claimed of its entries.  That is what a runtime value costs
-- now that a value is a CLOSURE: the environment's entries are where
-- the claim is re-established, once, rather than threaded through every
-- site that meets a stored value.
reducible : ∀ {n} {Γ : Ctx n} {Θ t} (b : Exp Γ [] [] Θ t) (σ : Env Γ Θ) → RedEnv m σ
          → Red {Γ = Γ} m (obs t) (Θ , b , σ)
reducible b σ rσ =
  redExpAcc b σ rσ _ (ib-topᵉ b) (<-wellFounded-fast _) (<-wellFounded-fast (gsizeᵉ b))

mutual
  red-val : ∀ {n} {Γ : Ctx n} (t : Ty) (v : Val Γ t) → Red m t v
  red-val unitᵗ     v           = tt
  red-val boolᵗ     v           = tt
  red-val natᵗ      v           = tt
  red-val uniqᵗ     v           = tt
  red-val (s ×ᵗ u)  (a , b)     = red-val s a , red-val u b
  red-val (s +ᵗ u)  (inj₁ a)    = red-val s a
  red-val (s +ᵗ u)  (inj₂ b)    = red-val u b
  red-val (listᵗ s) []          = []ᵃ
  red-val (listᵗ s) (x ∷ xs)    = red-val s x ∷ᵃ red-val (listᵗ s) xs
  red-val (obs u)   (Θ , b , σ) = reducible b σ (red-env σ)

  red-env : ∀ {n} {Γ : Ctx n} {Θ : List Ty} (σ : Env Γ Θ) → RedEnv m σ
  red-env []ᵉ                 = tt
  red-env (_∷ᵉ_ {s = s} v vs) = red-val s v , red-env vs

redFn : ∀ {n} {Γ : Ctx n} {s u} (fn : FnClo Γ s u) → RedFn m fn
redFn (Θ , f , σ) =
  redFnAcc f σ (red-env σ) _ (ib-topᵗ f)
    (<-wellFounded-fast _) (<-wellFounded-fast (gsizeᵗ f))

------------------------------------------------------------------
-- THE GENERAL PATH WALK, which is what the arrival spine spends and
-- the one place a path is taken apart rather than extended.
------------------------------------------------------------------

-- THE SINK ARM IS THE ONLY ONE THAT IS NOT STRUCTURAL, and what pays
-- for it is the floor: `shareAdmit` hands back chains at `suc (toℕ i)`,
-- strictly above the floor this path sinks at, so `n ∸ lo` drops.  Every
-- other arm peels a frame.
handlesAcc : ∀ {n} {Γ : Ctx n} {t lo} → Acc _<_ (n ∸ lo) → Walk Γ t m lo
handlesAcc ac       root                    = handles-root
handlesAcc (acc rec) (share-sink i below)   =
  handles-share i below (λ {u} κ → handlesAcc (rec (monus-sink i below)) {u} κ)
handlesAcc ac (map-f fn ↠ κ)          = handles-map fn κ (redFn fn) (handlesAcc ac κ)
handlesAcc ac (scan-f fn nid ↠ κ)     = handles-scan fn nid κ (handlesAcc ac κ)
handlesAcc ac (take-f nid ↠ κ)        = handles-take nid κ (handlesAcc ac κ)
handlesAcc ac (batchSync-f nid ↠ κ)   = handles-batchSync nid κ (handlesAcc ac κ)
handlesAcc ac (from-inner op a i ↠ κ) = handles-from-inner op a i κ (handlesAcc ac κ)
handlesAcc ac (thru-outer op nid ↠ κ) = handles-thru-outer op nid κ (handlesAcc ac κ)

handles! : ∀ {n} {Γ : Ctx n} {t u lo} (κ : Path Γ lo u t) → Handles {m = m} u κ
handles! {n = n} {lo = lo} = handlesAcc (<-wellFounded-fast (n ∸ lo))
