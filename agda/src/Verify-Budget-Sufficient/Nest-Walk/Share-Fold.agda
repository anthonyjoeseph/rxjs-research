-- THE SHARE FAN-OUT'S NODE ARITHMETIC, cut off the walk face because a
-- FOCUS CHECK PAYS FOR THE WHOLE FILE.  These four are one genuine cycle
-- -- `foldPath` and `dispatchShare` are mutually recursive, so nothing here
-- may be split further -- and the loop stubs a block's siblings, never the
-- 126 single-member blocks around it.  Left where they were, each of their
-- four focus checks re-proved a seven-thousand-line module, which is what
-- put the walk face over the dev budget while every individual member was
-- comfortably inside it.
module Verify-Budget-Sufficient.Nest-Walk.Share-Fold where


open import Data.Bool using (Bool; true; false; if_then_else_; _∧_)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Bool.ListAction using (any)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _⊔_; _≤_; z≤n; s≤s; _≡ᵇ_; _≤ᵇ_)
open import Data.Nat.Properties using
  (≤-trans; ≤-reflexive; ≤ᵇ⇒≤; n≤1+n; +-assoc; +-comm; +-monoˡ-≤; +-monoʳ-≤; *-assoc; *-comm;
  m^n>0; *-identityˡ; *-mono-≤; *-monoˡ-≤; *-monoʳ-≤; *-distribˡ-+; m≤m+n; m≤m⊔n; m≤n⊔m; ⊔-lub;
  ^-monoˡ-≤)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Vec using (lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans; cong; cong₂)
open import Data.Fin using (toℕ)

open import Rx.Prim using (Tick; Id; Source; Gas; InstEvent; close; exhausted)
open import Rx.Exp using (Ctx; Closed; Val)
open import Rx.Slots using (Slots)
open import Rx.Evaluator using
  (Sched; EvalSt; Path; root; share-sink; _↠_; foldPath; dispatchShare; stepFrame; shareGo;
  shareAdmit; shareLatch; RegId)
open import Verify-Budget-Sufficient.Keeps-Ring using
  (KeepsC; stepFrame-keeps)
open import Verify-Budget-Sufficient.Caps using
  (_⊑ᶜ_; 1≤pow≤; Caps; frameStep; frameStep-reg-mono; iterSize-infl; iterSize-mono-count)
open import Verify-Budget-Sufficient.Caps using (sizeCount)
open import Verify-Budget-Sufficient.Caps-Depth using
  (depthDisp; depthFold; depthShareGo; lub3-m; lub3-r)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (pathSz?; frameSz?)
open import Verify-Budget-Sufficient.Caps-Face.Part4 using (foldPath-slots)
open import Decide using (T-to)
open import Verify-Budget-Sufficient.Measures using (∧-true; pathLen)
open import Verify-Budget-Sufficient.Nest-Store using
  (frameNestF; 1≤frameNestF; nest-telescope; nestUnit; pow-distrib-*)
open import Verify-Budget-Sufficient.Fan-Caps using (fanLen; fanSq; delSq; delSq-monoᶜ; cSize≤delSq; fanLen-zero; fanSq-zero; fanLen-suc;
  fanSq-suc)
open import Verify-Budget-Sufficient.Deliver-Measure using
  (deliverLen; deliverNestF; deliverNestD; admSz?)
open import Verify-Budget-Sufficient.Nest-Subst using (applyFn-nest; applyFn-nest-sync; evalTm-nest-sync; nestD-unfoldμ)
  renaming (pow-grow to pow-grow-both)
open import Verify-Budget-Sufficient.Nest-Cap using
  (nestFac; 1≤nestFac; nestU; nestU-mono; nestFac-monoS)

open import Verify-Budget-Sufficient.Nest-Walk using
  (burstsDrain; burstsHead; burstsOK; capsWalkOK; c⊑step; deliverNestD-cons; dispatchBurstsOK;
  dispatchCapsOK; fac-hoist; FaceOK; faceHere; frameNestD; nestDᵛˢ; nodesMax; one-pow;
  shareBurstsOK; shareCapsOK; shareFold-tele; shareFold-unit; stepFrame-nodes)

shareGoFold-nodes : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (c ac : Caps) (d : ℕ) (W : ℕ) (sl : Slots Γ) (Lv : ℕ) (sf : Gas) (gas : ℕ)
    (id : Id) (now : Tick) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (ps : List (RegId × Path Γ (lookup Γ i) t)) (k : ℕ)
    (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl → 1 ≤ W → 1 ≤ Caps.cSize c → c ⊑ᶜ ac →
    admSz? (Caps.cSize ac) ps ≡ true →
    length ps ≤ k →
    shareBurstsOK W sf gas id now i vals fin ps sched st →
    shareCapsOK c ac sl d Lv sf gas id now i vals fin ps sched st →
    depthShareGo sf gas id now i vals fin ps sched st ≤ d →
    Lv ≤ sizeCount c d ⊔ Caps.cSize c →
  ⦃ _ : FaceOK c sl ⦄ →
    Σ ℕ λ j →
    let c′ = frameStep j c in
    (j ≤ sizeCount c d ⊔ Caps.cSize c)
    × (nodesMax (proj₂ (proj₂ (shareGo sf gas id now i vals fin ps sched st)))
      ≤ nestFac (Caps.cSize c′) W ^ (k * suc (Caps.cSize ac + fanLen gas ac))
        * ((2 ^ (k * (Caps.cSize ac * Caps.cSize ac + fanSq gas ac))) ^ W
           * ((nodesMax st ⊔ nestDᵛˢ vals)
              + W * (k * (Caps.cSize ac * Caps.cSize ac + fanSq gas ac)
                     + suc (k * suc (Caps.cSize ac + fanLen gas ac))
                       * nestU (delSq (suc gas) c′) (nestUnit e sl)))))

-- The whole-list statement is the budgeted fold spent at the registry
-- cap: the allowances' own step equations convert the spent budget
-- into the sealed recurrences, and nothing else moves.
shareGo-nodes : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c ac : Caps) (d : ℕ) (W : ℕ) (sl : Slots Γ) (Lv : ℕ) (sf : Gas) (gas : ℕ)
  (id : Id) (now : Tick) (i : Fin n)
  (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
  (ps : List (RegId × Path Γ (lookup Γ i) t))
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl → 1 ≤ W → 1 ≤ Caps.cSize c → c ⊑ᶜ ac →
  admSz? (Caps.cSize ac) ps ≡ true →
  length ps ≤ Caps.cReg ac →
  shareBurstsOK W sf gas id now i vals fin ps sched st →
  shareCapsOK c ac sl d Lv sf gas id now i vals fin ps sched st →
  depthShareGo sf gas id now i vals fin ps sched st ≤ d →
  Lv ≤ sizeCount c d ⊔ Caps.cSize c →
  ⦃ _ : FaceOK c sl ⦄ →
  Σ ℕ λ j →
  let c′ = frameStep j c in
  (j ≤ sizeCount c d ⊔ Caps.cSize c)
  × (nodesMax (proj₂ (proj₂ (shareGo sf gas id now i vals fin ps sched st)))
    ≤ nestFac (Caps.cSize c′) W ^ fanLen (suc gas) ac
      * ((2 ^ fanSq (suc gas) ac) ^ W
         * ((nodesMax st ⊔ nestDᵛˢ vals)
            + W * (fanSq (suc gas) ac
                   + suc (fanLen (suc gas) ac) * nestU (delSq (suc gas) c′) (nestUnit e sl)))))
shareGo-nodes {e = e} c ac d W sl Lv sf gas id now i vals fin ps sched st
  hsl 1≤W 1≤S hac hadm hlen hb hc hdp hlv =
  proj₁ FOLD ,
  proj₁ (proj₂ FOLD) ,
  ≤-trans (proj₂ (proj₂ FOLD))
          (≤-reflexive (cong₂ (λ a b →
              nestFac (Caps.cSize (frameStep (proj₁ FOLD) c)) W ^ a
                * ((2 ^ b) ^ W
                   * ((nodesMax st ⊔ nestDᵛˢ vals)
                      + W * (b + suc a
                             * nestU (delSq (suc gas) (frameStep (proj₁ FOLD) c))
                                     (nestUnit e sl)))))
            (sym (fanLen-suc gas ac)) (sym (fanSq-suc gas ac))))
  where
  FOLD = shareGoFold-nodes c ac d W sl Lv sf gas id now i vals fin ps (Caps.cReg ac)
           sched st hsl 1≤W 1≤S hac hadm hlen hb hc hdp hlv

-- AND THE SINK ITSELF IS THREE ARMS OVER THAT FOLD, none of which
-- touches the nodes map: out of dispatch gas the state is returned
-- untouched, and the finishing arm latches the share's source into the
-- dying and completed ledgers, which are not the map.  So the whole of
-- the sink's growth is the fold's, and the leaf is the fold.  The
-- admitted list's own pricing is read off `capsOK?` here — the admitted
-- registrations are a sublist of the registry, so they inherit its
-- `regsSz?` receipt and its count bound.
dispatchShare-nodes : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c ac : Caps) (d : ℕ) (W : ℕ) (sl : Slots Γ) (Lv : ℕ) (sf : Gas) (gas : ℕ)
  (id : Id) (now : Tick) (i : Fin n)
  (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl → 1 ≤ W → 1 ≤ Caps.cSize c → c ⊑ᶜ ac →
  dispatchBurstsOK W sf gas id now i vals fin sched st →
  dispatchCapsOK c ac sl d Lv sf gas id now i vals fin sched st →
  depthDisp sf gas id now i vals fin sched st ≤ d →
  Lv ≤ sizeCount c d ⊔ Caps.cSize c →
  ⦃ _ : FaceOK c sl ⦄ →
  Σ ℕ λ j →
  let c′ = frameStep j c in
  (j ≤ sizeCount c d ⊔ Caps.cSize c)
  × (nodesMax (proj₂ (proj₂ (dispatchShare {t = t} sf gas id now i vals fin sched st)))
    ≤ nestFac (Caps.cSize c′) W ^ fanLen gas ac
      * ((2 ^ fanSq gas ac) ^ W
         * ((nodesMax st ⊔ nestDᵛˢ vals)
            + W * (fanSq gas ac
                   + suc (fanLen gas ac) * nestU (delSq gas c′) (nestUnit e sl)))))
dispatchShare-nodes c ac d W sl Lv sf zero id now i vals fin sched st hsl 1≤W 1≤S hac hdb hdc hdp hlv
  rewrite fanLen-zero ac | fanSq-zero ac =
  0 , z≤n ,
  ≤-trans (≤-trans (≤-trans (m≤m⊔n (nodesMax st) (nestDᵛˢ vals)) (m≤m+n _ _))
                   (one-pow W _))
          (≤-reflexive (sym (*-identityˡ _)))
dispatchShare-nodes c ac d W sl Lv sf (suc gas) id now i vals false sched st hsl 1≤W 1≤S hac hdb hdc hdp hlv =
  shareGo-nodes c ac d W sl Lv sf gas id now i vals false
    (shareAdmit i (EvalSt.registry st)) sched st hsl 1≤W 1≤S hac
    (proj₁ hdc) (proj₁ (proj₂ hdc))
    hdb (proj₂ (proj₂ hdc)) hdp hlv
dispatchShare-nodes c ac d W sl Lv sf (suc gas) id now i vals true sched st hsl 1≤W 1≤S hac hdb hdc hdp hlv =
  shareGo-nodes c ac d W sl Lv sf gas id now i vals true
    (shareAdmit i (EvalSt.registry st)) sched (shareLatch i true st) hsl 1≤W 1≤S hac
    (proj₁ hdc) (proj₁ (proj₂ hdc))
    hdb (proj₂ (proj₂ hdc)) hdp hlv

foldPath-nodes : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c ac : Caps) (d : ℕ) (W : ℕ) (sl : Slots Γ) (Lv : ℕ)
  (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
  (path : Path Γ u t) (vals : List (Val Γ u))
  (evs : List (InstEvent (Val Γ t))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  ⦃ _ : FaceOK c sl ⦄ →
  Sched.slots sched ≡ sl → 1 ≤ W → 1 ≤ Caps.cSize c → c ⊑ᶜ ac →
  burstsOK W sf gas id now path vals fin sched st →
  capsWalkOK c ac sl d Lv sf gas id now path vals fin sched st →
  depthFold sf gas id now envSrc path vals evs fin sched st ≤ d →
  pathSz? (Caps.cSize ac) path ≡ true →
  Lv ≤ sizeCount c d ⊔ Caps.cSize c →
  Σ ℕ λ j →
  let c′ = frameStep j c in
  (j ≤ sizeCount c d ⊔ Caps.cSize c)
  × (nodesMax (proj₂ (proj₂ (foldPath sf gas id now envSrc path vals evs fin sched st)))
    ≤ (nestFac (Caps.cSize c′) W) ^ deliverLen gas ac path
      * (deliverNestF gas ac path ^ W
         * ((nodesMax st ⊔ nestDᵛˢ vals)
            + W * (deliverNestD gas ac path
                   + suc (deliverLen gas ac path) * nestU (delSq gas c′) (nestUnit e sl)))))
foldPath-nodes c ac d W sl Lv sf gas id now envSrc root vals evs fin sched st hsl 1≤W 1≤S hac hb hc hdp hpk hlv =
  0 , z≤n ,
  ≤-trans (≤-trans (≤-trans (m≤m⊔n (nodesMax st) (nestDᵛˢ vals)) (m≤m+n _ _))
                   (one-pow W _))
          (≤-reflexive (sym (*-identityˡ _)))
foldPath-nodes {e = e} c ac d W sl Lv sf gas id now envSrc (share-sink i) vals evs fin sched st hsl 1≤W 1≤S hac hb hc hdp hpk hlv =
  -- the sink arm IS the dispatch, level and all: every deliver measure
  -- at a `share-sink` reduces to the fan allowance the dispatch is
  -- already stated over, so the two conclusions are the same statement
  dispatchShare-nodes c ac d W sl Lv sf gas id now i vals fin sched st hsl 1≤W 1≤S hac
    (proj₂ hb) (proj₂ hc) hdp hlv
foldPath-nodes {e = e} c ac d W sl Lv sf gas id now envSrc (f ↠ p) vals evs fin sched st hsl 1≤W 1≤S hac hb hc hdp hpk hlv =
  jt ,
  ⊔-lub (proj₁ (proj₂ IHr)) (proj₁ (proj₂ SFr)) ,
  ≤-trans IHw
    (≤-trans (*-monoʳ-≤ (Q ^ deliverLen gas ac p)
                (*-monoʳ-≤ (deliverNestF gas ac p ^ W)
                  (+-monoˡ-≤ (W * (deliverNestD gas ac p + L * U))
                             (≤-trans SFw
                               (*-monoʳ-≤ Q (+-monoʳ-≤ A unit≤))))))
    (≤-trans (*-monoʳ-≤ (Q ^ deliverLen gas ac p)
                (fac-hoist Q (deliverNestF gas ac p ^ W) (A + U) (W * (deliverNestD gas ac p + L * U))
                           1≤Q))
    (≤-trans (≤-reflexive (sym (*-assoc (Q ^ deliverLen gas ac p) Q Inner)))
    (≤-trans (≤-reflexive (cong (_* Inner) (*-comm (Q ^ deliverLen gas ac p) Q)))
             (*-monoʳ-≤ (Q ^ suc (deliverLen gas ac p))
    (≤-trans (*-monoʳ-≤ (deliverNestF gas ac p ^ W)
               (≤-trans (≤-reflexive (+-assoc A U (W * (deliverNestD gas ac p + L * U))))
                        (+-monoʳ-≤ A widen)))
    (≤-trans (nest-telescope (frameNestF f ^ W) (deliverNestF gas ac p ^ W) B
                             (W * frameNestD f) (W * (deliverNestD gas ac p + L * U) + W * U)
                             (1≤pow≤ (frameNestF f) W (1≤frameNestF f)))
             (≤-reflexive
               (cong₂ _*_ (sym (pow-distrib-* W (frameNestF f) (deliverNestF gas ac p)))
                          (cong (B +_) charge))))))))))
  where
  Bₗ = Caps.cSize ac
  K1 = ∧-true (frameSz? Bₗ f) ((suc (pathLen p) ≤ᵇ Bₗ) ∧ pathSz? Bₗ p) hpk
  K2 = ∧-true (suc (pathLen p) ≤ᵇ Bₗ) (pathSz? Bₗ p) (proj₂ K1)
  hpkp = proj₂ K2
  hplp = ≤ᵇ⇒≤ (suc (pathLen p)) Bₗ (T-to (proj₁ K2))

  step   = stepFrame sf id now f p vals fin sched st
  vals′  = proj₁ step
  evs′   = proj₁ (proj₂ step)
  fin′   = proj₁ (proj₂ (proj₂ step))
  sched₁ = proj₁ (proj₂ (proj₂ (proj₂ step)))
  st₁    = proj₂ (proj₂ (proj₂ (proj₂ step)))

  -- THE WALK HANDS ITS OWN NEXT LEVEL, and the two are independent:
  -- the level the tail is asserted at comes from the predicate, the
  -- level the bound is read at comes from the frame receipt, and the
  -- join below is what puts them back together.
  Bᴸ    = Caps.cSize (frameStep Lv c)
  HPL   = proj₁ (proj₂ (proj₂ (proj₂ hc)))
  HPL2  = ∧-true (suc (pathLen p) ≤ᵇ Bᴸ) (pathSz? Bᴸ p)
            (proj₂ (∧-true (frameSz? Bᴸ f)
                     ((suc (pathLen p) ≤ᵇ Bᴸ) ∧ pathSz? Bᴸ p) HPL))
  tail  = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ hc)))))
  L′    = proj₁ tail
  hL′   = proj₁ (proj₂ tail)
  hstep = c⊑step c Lv (FaceOK.fSize faceHere)

  IHr = foldPath-nodes c ac d W sl (Lv + L′) sf gas id now envSrc p vals′ (evs ++ evs′) fin′ sched₁ st₁
          (trans (KeepsC.slotsEq (stepFrame-keeps sf id now f p vals fin sched st)) hsl)
          1≤W 1≤S hac (proj₂ (proj₂ hb)) (proj₂ (proj₂ tail))
          (≤-trans (m≤n⊔m _ _) hdp) hpkp hL′
  SFr = stepFrame-nodes c d W sl Lv sf id now f p vals fin sched st
          hsl 1≤W (proj₁ hb) (proj₁ hc) (proj₁ (proj₂ hc))
          (≤-trans (proj₁ (proj₂ (proj₂ hc))) (proj₁ hstep))
          (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ hc)))))
          (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ hc))))))
          (burstsDrain W sf gas id now f p vals fin sched st hb)
          1≤S
          (≤-trans (m≤m⊔n _ _) hdp)
          (proj₂ HPL2) (≤ᵇ⇒≤ (suc (pathLen p)) Bᴸ (T-to (proj₁ HPL2))) hlv
          (burstsHead W sf gas id now p vals′ fin′ sched₁ st₁ (proj₂ (proj₂ hb)))
  jᵢ = proj₁ IHr
  jₛ = proj₁ SFr
  jt = jᵢ ⊔ jₛ
  c′ = frameStep jt c

  -- THE LEVEL IS A JOIN, and nothing more, because both sub-results
  -- report their own and the whole conclusion is increasing in it.  The
  -- size cap climbs with the count and the registry cap climbs
  -- linearly, so the delivery square climbs with both -- which is what
  -- the two widenings below spend, one per sub-result.
  sizeᵢ : Caps.cSize (frameStep jᵢ c) ≤ Caps.cSize c′
  sizeᵢ = iterSize-mono-count (Caps.cSize c) (Caps.cSize c) 1≤S (m≤m⊔n jᵢ jₛ)

  sizeₛ : Caps.cSize (frameStep jₛ c) ≤ Caps.cSize c′
  sizeₛ = iterSize-mono-count (Caps.cSize c) (Caps.cSize c) 1≤S (m≤n⊔m jᵢ jₛ)

  regᵢ : Caps.cReg (frameStep jᵢ c) ≤ Caps.cReg c′
  regᵢ = frameStep-reg-mono c (m≤m⊔n jᵢ jₛ)

  S      = Caps.cSize c′
  Q      = nestFac S W
  1≤Q    = 1≤nestFac S W
  A      = frameNestF f ^ W * ((nodesMax st ⊔ nestDᵛˢ vals) + W * frameNestD f)
  Inner  = deliverNestF gas ac p ^ W * ((A + nestU (delSq gas c′) (nestUnit e sl))
                              + W * (deliverNestD gas ac p + suc (deliverLen gas ac p) * nestU (delSq gas c′) (nestUnit e sl)))
  B      = nodesMax st ⊔ nestDᵛˢ vals
  U      = nestU (delSq gas c′) (nestUnit e sl)
  L      = suc (deliverLen gas ac p)

  Uᵢ≤ : nestU (delSq gas (frameStep jᵢ c)) (nestUnit e sl) ≤ U
  Uᵢ≤ = nestU-mono (delSq gas (frameStep jᵢ c)) (delSq gas c′) (nestUnit e sl)
                   (delSq-monoᶜ gas (frameStep jᵢ c) c′ sizeᵢ regᵢ)

  IHw = ≤-trans (proj₂ (proj₂ IHr))
          (*-mono-≤ (^-monoˡ-≤ (deliverLen gas ac p)
                       (nestFac-monoS sizeᵢ W))
            (*-monoʳ-≤ (deliverNestF gas ac p ^ W)
              (+-monoʳ-≤ (nodesMax st₁ ⊔ nestDᵛˢ vals′)
                (*-monoʳ-≤ W
                  (+-monoʳ-≤ (deliverNestD gas ac p)
                    (*-monoʳ-≤ (suc (deliverLen gas ac p)) Uᵢ≤))))))

  SFw = ≤-trans (proj₂ (proj₂ SFr))
          (*-mono-≤ (nestFac-monoS sizeₛ W)
            (+-monoʳ-≤ (frameNestF f ^ W
                          * ((nodesMax st ⊔ nestDᵛˢ vals) + W * frameNestD f))
              (nestU-mono (Caps.cSize (frameStep jₛ c)) S (nestUnit e sl) sizeₛ)))

  -- the frame face prices its unit at the bare size cap; the walk
  -- prices it at the delivery square, which is the wider of the two --
  -- and both are read at the LEVEL, which is what makes the square
  -- contain the cap it is a square of
  unit≤ : nestU S (nestUnit e sl) ≤ U
  unit≤ = nestU-mono S (delSq gas c′) (nestUnit e sl)
                     (cSize≤delSq gas c′ (≤-trans 1≤S (iterSize-infl (Caps.cSize c) 1≤S jt (Caps.cSize c))))

  -- the frame's own summand is paid out of the extra `W * U` the path's
  -- coefficient gains at this level, and `1 ≤ W` is what makes it fit
  widen : U + W * (deliverNestD gas ac p + L * U) ≤ W * (deliverNestD gas ac p + L * U) + W * U
  widen = ≤-trans (≤-reflexive (+-comm U (W * (deliverNestD gas ac p + L * U))))
                  (+-monoʳ-≤ (W * (deliverNestD gas ac p + L * U))
                    (≤-trans (≤-reflexive (sym (*-identityˡ U)))
                             (*-monoˡ-≤ U 1≤W)))
  charge : W * frameNestD f + (W * (deliverNestD gas ac p + L * U) + W * U)
             ≡ W * (deliverNestD gas ac (f ↠ p) + suc L * U)
  charge =
    trans (cong (W * frameNestD f +_)
            (sym (*-distribˡ-+ W (deliverNestD gas ac p + L * U) U)))
    (trans (sym (*-distribˡ-+ W (frameNestD f) ((deliverNestD gas ac p + L * U) + U)))
           (cong (W *_) inner))
    where
    inner : frameNestD f + ((deliverNestD gas ac p + L * U) + U)
              ≡ deliverNestD gas ac (f ↠ p) + (U + L * U)
    inner =
      trans (cong (frameNestD f +_)
              (trans (+-assoc (deliverNestD gas ac p) (L * U) U)
                     (cong (deliverNestD gas ac p +_) (+-comm (L * U) U))))
      (trans (sym (+-assoc (frameNestD f) (deliverNestD gas ac p) (U + L * U)))
             (cong (_+ (U + L * U)) (sym (deliverNestD-cons gas ac f p))))

-- The fold's own three arms, which are `shareGo`'s: an empty list
-- returns the state it was handed, a cancelled registration is skipped
-- without spending any of the budget, and a delivered one spends
-- exactly one unit of it.  Only the last arm is an induction, and its
-- two halves are the walk that runs the entry and the fold that runs
-- the rest -- so the budget decrements where the list does.
shareGoFold-nodes {e = e} c ac d W sl Lv sf gas id now i vals fin [] k sched st
                  hsl 1≤W 1≤S hac hadm hlen hb hc hdp hlv =
  0 , z≤n ,
  ≤-trans (m≤m⊔n (nodesMax st) (nestDᵛˢ vals))
  (≤-trans (m≤m+n _ _)
  (≤-trans (grow ((2 ^ (k * (Caps.cSize ac * Caps.cSize ac + fanSq gas ac))) ^ W) _
             (1≤pow≤ (2 ^ (k * (Caps.cSize ac * Caps.cSize ac + fanSq gas ac))) W
               (m^n>0 2 (k * (Caps.cSize ac * Caps.cSize ac + fanSq gas ac)))))
           (grow (nestFac (Caps.cSize c) W ^ (k * suc (Caps.cSize ac + fanLen gas ac))) _
             (1≤pow≤ (nestFac (Caps.cSize c) W)
               (k * suc (Caps.cSize ac + fanLen gas ac))
               (1≤nestFac (Caps.cSize c) W)))))
  where
  grow : ∀ (F Y : ℕ) → 1 ≤ F → Y ≤ F * Y
  grow F Y 1≤F = ≤-trans (≤-reflexive (sym (*-identityˡ Y))) (*-monoˡ-≤ Y 1≤F)
shareGoFold-nodes {e = e} c ac d W sl Lv sf gas id now i vals fin ((rid , p) ∷ ps) (suc k)
                  sched st hsl 1≤W 1≤S hac hadm (s≤s hlen) hb hc hdp hlv
  with any (_≡ᵇ rid) (EvalSt.cancelled st) | hb | hc
... | true  | hb′ | hc′ =
  shareGoFold-nodes c ac d W sl Lv sf gas id now i vals fin ps (suc k) sched st hsl 1≤W 1≤S hac
    (proj₂ (∧-true _ _ hadm)) (≤-trans hlen (n≤1+n k)) hb′ hc′
    (≤-trans (m≤m⊔n _ _) hdp) hlv
... | false | hb′ | hc′ =
  jt ,
  ⊔-lub (proj₁ (proj₂ TAILr)) (proj₁ (proj₂ HEADr)) ,
  ≤-trans TAILw
          (shareFold-tele Q W Lu Sq U k X (nodesMax st₁ ⊔ nestDᵛˢ vals)
             (1≤nestFac (Caps.cSize c′) W) fit)
  where
  st′  = record st { delivered = rid ∷ EvalSt.delivered st }
  evs  = if fin then close (toℕ i) exhausted ∷ [] else []
  r    = foldPath sf gas id now (toℕ i) p vals evs fin sched st′
  sched₁ = proj₁ (proj₂ r)
  st₁    = proj₂ (proj₂ r)

  -- THE FOLD'S LEVEL IS THE JOIN OF ITS TWO HALVES, exactly as the path
  -- fold's is: this entry's own walk reports one and the rest of the
  -- ring reports another, and neither half can be asked to have used
  -- the other's.  Both are widened to the join before they meet, which
  -- is the only place the ordering is spent.
  HEADr = foldPath-nodes c ac d W sl Lv sf gas id now (toℕ i) p vals evs fin sched st′
            hsl 1≤W 1≤S hac (proj₁ hb′) (proj₁ hc′)
            (lub3-m (depthShareGo sf gas id now i vals fin ps sched st)
                    (depthFold sf gas id now (toℕ i) p vals evs fin sched st′)
                    (depthShareGo sf gas id now i vals fin ps sched₁ st₁) hdp)
            (proj₁ (∧-true _ _ hadm)) hlv
  TAILr = shareGoFold-nodes c ac d W sl (Lv + proj₁ (proj₂ hc′)) sf gas id now i vals fin ps k sched₁ st₁
            (trans (foldPath-slots sf gas id now (toℕ i) p vals evs fin sched st′) hsl)
            1≤W 1≤S hac (proj₂ (∧-true _ _ hadm)) hlen
            (proj₂ hb′) (proj₂ (proj₂ (proj₂ hc′)))
            (lub3-r (depthShareGo sf gas id now i vals fin ps sched st)
                    (depthFold sf gas id now (toℕ i) p vals evs fin sched st′)
                    (depthShareGo sf gas id now i vals fin ps sched₁ st₁) hdp)
            (proj₁ (proj₂ (proj₂ hc′)))
  jt = proj₁ TAILr ⊔ proj₁ HEADr
  c′ = frameStep jt c

  Q  = nestFac (Caps.cSize c′) W
  Lu = suc (Caps.cSize ac + fanLen gas ac)
  Sq = Caps.cSize ac * Caps.cSize ac + fanSq gas ac
  U  = nestU (delSq (suc gas) c′) (nestUnit e sl)
  X  = nodesMax st ⊔ nestDᵛˢ vals

  grow : ∀ (F Y : ℕ) → 1 ≤ F → Y ≤ F * Y
  grow F Y 1≤F = ≤-trans (≤-reflexive (sym (*-identityˡ Y))) (*-monoˡ-≤ Y 1≤F)

  sizeₕ : Caps.cSize (frameStep (proj₁ HEADr) c) ≤ Caps.cSize c′
  sizeₕ = iterSize-mono-count (Caps.cSize c) (Caps.cSize c) 1≤S
            (m≤n⊔m (proj₁ TAILr) (proj₁ HEADr))

  regₕ : Caps.cReg (frameStep (proj₁ HEADr) c) ≤ Caps.cReg c′
  regₕ = frameStep-reg-mono c (m≤n⊔m (proj₁ TAILr) (proj₁ HEADr))

  sizeₜ : Caps.cSize (frameStep (proj₁ TAILr) c) ≤ Caps.cSize c′
  sizeₜ = iterSize-mono-count (Caps.cSize c) (Caps.cSize c) 1≤S
            (m≤m⊔n (proj₁ TAILr) (proj₁ HEADr))

  regₜ : Caps.cReg (frameStep (proj₁ TAILr) c) ≤ Caps.cReg c′
  regₜ = frameStep-reg-mono c (m≤m⊔n (proj₁ TAILr) (proj₁ HEADr))

  HEADw = ≤-trans (proj₂ (proj₂ HEADr))
            (*-mono-≤ (^-monoˡ-≤ (deliverLen gas ac p) (nestFac-monoS sizeₕ W))
              (*-monoʳ-≤ (deliverNestF gas ac p ^ W)
                (+-monoʳ-≤ (nodesMax st′ ⊔ nestDᵛˢ vals)
                  (*-monoʳ-≤ W
                    (+-monoʳ-≤ (deliverNestD gas ac p)
                      (*-monoʳ-≤ (suc (deliverLen gas ac p))
                        (nestU-mono (delSq gas (frameStep (proj₁ HEADr) c))
                                    (delSq gas c′) (nestUnit e sl)
                          (delSq-monoᶜ gas (frameStep (proj₁ HEADr) c) c′ sizeₕ regₕ))))))))

  TAILw = ≤-trans (proj₂ (proj₂ TAILr))
            (*-mono-≤ (^-monoˡ-≤ (k * Lu) (nestFac-monoS sizeₜ W))
              (*-monoʳ-≤ ((2 ^ (k * Sq)) ^ W)
                (+-monoʳ-≤ (nodesMax st₁ ⊔ nestDᵛˢ vals)
                  (*-monoʳ-≤ W
                    (+-monoʳ-≤ (k * Sq)
                      (*-monoʳ-≤ (suc (k * Lu))
                        (nestU-mono (delSq (suc gas) (frameStep (proj₁ TAILr) c))
                                    (delSq (suc gas) c′) (nestUnit e sl)
                          (delSq-monoᶜ (suc gas) (frameStep (proj₁ TAILr) c) c′
                                       sizeₜ regₜ))))))))

  unit : ℕ
  unit = Q ^ Lu * ((2 ^ Sq) ^ W * (X + W * (Sq + Lu * U)))

  Inner : ℕ
  Inner = X + W * (Sq + Lu * U)

  X≤unit : X ≤ unit
  X≤unit =
    ≤-trans (m≤m+n X (W * (Sq + Lu * U)))
    (≤-trans (grow ((2 ^ Sq) ^ W) Inner (1≤pow≤ (2 ^ Sq) W (m^n>0 2 Sq)))
             (grow (Q ^ Lu) ((2 ^ Sq) ^ W * Inner)
                   (1≤pow≤ Q Lu (1≤nestFac (Caps.cSize c′) W))))

  fit : (nodesMax st₁ ⊔ nestDᵛˢ vals) ≤ unit
  fit = ⊔-lub
    (≤-trans HEADw
             (shareFold-unit {e = e} ac c′ W sl gas p X (≤-trans 1≤S (proj₁ hac))
               (proj₁ (∧-true (pathSz? (Caps.cSize ac) p)
                              (admSz? (Caps.cSize ac) ps) hadm))))
    (≤-trans (m≤n⊔m (nodesMax st) (nestDᵛˢ vals)) X≤unit)
