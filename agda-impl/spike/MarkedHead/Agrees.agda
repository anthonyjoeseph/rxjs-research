{-# OPTIONS --guardedness #-}

module spike.MarkedHead.Agrees where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Properties using (++-identityʳ)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapᴹ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)

open import Tree using (Obs; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.MonotonicList.Events using (Pos; Timeline)
open import denotation.Unfold using (Node; Step; outˢ; skipˢ; endˢ; hushˢ; headˢ; step; restˢ; restsˢ; restᴹ; restsᶜ; restᶜ; unionˢ;
  Earliest; found; earliest; pick; Outer; doneᵒ; runᵒ; outerOf; goˢ; outerˢ; laneˢ; flatˢ;
  Source; live; ended; connectᶜ; burstingᶜ; underᶜ; subscribe; sourceˢ; bodyˢ; shutˢᵗ; burstsˢ; beforeˢ) renaming (none to noneᴱ)
open import operation.Key using (at; after)
open import operation.MarkedPure using (module Machine)
open Machine using (St; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS; Ctx; closed; inMap; inCut;
  Out; still; shows; Cand; seek; first; retag; mapT; cutT; nx; cp; attached; attAt; raceT; outerT; laneT; lanes; inOuter; inLanes; inLn;
  CS; cs; inSrc; inBody; own; ownBest; shift; over; sourceT; bodyM; owedM) renaming (found to foundᴹ)
open import spike.MarkedGhost using (gh; lane; lanesL; deadL; outerG; poolG)
open import spike.MarkedHead using (Agrees; Conn; Done; Frag; Head; HeadAt; Lanes; NoConn; Quiet; []; _∷_; att-head; calm; cand; done-head; done-step; early; exact; hush-quiet; map-head; none; of-head; off-head; off-quiet; on-head; pool-step; quiet-first; quiet-hush; rest-hush)
open import spike.MarkedHead.Race using (WA; calm-first; ended-shut; first-l; len-earliest; min-wa; on-true; outer-at; over-ended; over-src; over-step; own-calm; own-first; p1-live; p3-live; quiet-race; quiet-wa; race; shut-via; src-calm; src-quiet; sub-bursts; sub-head; under-hush; union-upto; win; win-snoc)

------------------------------------------------------------------------
-- Every state of the fragment

mutual
  head-agrees : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) → Frag s → Head c s
  head-agrees c (ofS i p xs) _ = of-head c i p xs
  head-agrees c doneS        _ = done-head c
  head-agrees c (mapS f s) fs = map-head (closed c) f (seek (inMap f c) s) s (head-agrees (inMap f c) s fs)
  head-agrees c (cutS true attached s) fs = on-head (closed c) attached (seek (inCut true attached c) s) s (head-agrees (inCut true attached c) s fs)
  head-agrees c (cutS true (attAt p) s) fs = att-head (closed c) _ p (seek (inCut true (attAt p) c) s) s (head-agrees (inCut true (attAt p) c) s fs)
  head-agrees c (cutS false attached s) (fs , ns) =
    off-head (closed c) attached _ s fs ns (off-quiet (seek (inCut false attached c) s))
  head-agrees c (cutS false (attAt p) s) (fs , ns) =
    off-head (closed c) (attAt p) _ s fs ns (quiet-first (just (_ , after p , still)) (retag (cutT false) (seek (inCut false (attAt p) c) s)) calm (off-quiet (seek (inCut false (attAt p) c) s)))
  head-agrees c (flatS (mergeᶠ nothing) f d n [] o ls) fs = flat-at (closed c) c f d n o ls refl fs
  head-agrees c (connS k o b)    fs = conn-at (closed c) c k o b refl fs
  head-agrees c (joinS j g x ib) _  = join-head c j g x ib
  head-agrees c (pend o)        ()
  head-agrees c (coldS b l)     ()
  head-agrees c (scanS f z s)   ()
  head-agrees c (lnS b s)       ()
  head-agrees c (takeS i q w s) ()
  head-agrees c (flatS (mergeᶠ nothing) f d n (_ ∷ _) o ls) ()
  head-agrees c (flatS (mergeᶠ (just m)) f d n q o ls) ()
  head-agrees c (flatS switchᶠ f d n q o ls) ()
  head-agrees c (flatS exhaustᶠ f d n q o ls) ()

  -- A merge: the outer against its lanes, as the stepper races them.
  flat-at : ∀ {R Γ A B} b (c : Ctx R Γ B) (f : A → Obs Timeline Γ B) d n (o : St Γ A) ls → closed c ≡ b
          → Frag (flatS (mergeᶠ nothing) f d n [] o ls) → HeadAt b (cand c (flatS (mergeᶠ nothing) f d n [] o ls)) (flatS (mergeᶠ nothing) f d n [] o ls)
  flat-at true c f d n o ls cl (fo , fl , en , dd) =
    quiet-race d n (seek (inOuter (mergeᶠ nothing) f d n [] ls c) o) (lanes c (mergeᶠ nothing) f d n [] o [] ls)
      (subst (λ b → HeadAt b (cand (inOuter (mergeᶠ nothing) f d n [] ls c) o) o) cl (head-agrees (inOuter (mergeᶠ nothing) f d n [] ls c) o fo))
      (lanes-quiet c f d n o [] ls cl fl)
  flat-at false c f d n o ls cl (fo , fl , en , dd) =
    subst (λ st → Agrees (cand c (flatS (mergeᶠ nothing) f d n [] o ls))
                         (flatˢ (mergeᶠ nothing) (lane f) (outerOf (outerG d (gh o))) (lanesL ls) [] (poolG d (gh o) (deadL ls)) st (earliest (lanesL ls))))
      (sym (pool-step d o ls fo fl (λ e → proj₂ (dd e))))
      (race (lane f) d n (outerOf (outerG d (gh o))) (lanesL ls) (poolG d (gh o) (deadL ls)) (earliest (lanesL ls))
        (seek (inOuter (mergeᶠ nothing) f d n [] ls c) o) (lanes c (mergeᶠ nothing) f d n [] o [] ls)
        (outer-at d o (seek (inOuter (mergeᶠ nothing) f d n [] ls c) o) fo dd
          (subst (λ b → HeadAt b (cand (inOuter (mergeᶠ nothing) f d n [] ls c) o) o) cl (head-agrees (inOuter (mergeᶠ nothing) f d n [] ls c) o fo)))
        (lanes-wa c f d n o [] ls cl fl) en (len-earliest (lanesL ls)))

  -- The engine's lanes, oldest first, against the stepper's earliest.
  lanes-wa : ∀ {R Γ A B} (c : Ctx R Γ B) (f : A → Obs Timeline Γ B) d n (o : St Γ A) pre ls → closed c ≡ false → Lanes ls
           → WA (mapᴹ proj₂ (lanes c (mergeᶠ nothing) f d n [] o pre ls)) (win (earliest (lanesL ls)))
  lanes-wa c f d n o pre [] cl _ = exact refl , tt
  lanes-wa c f d n o pre (lnS true (cutS true a s) ∷ post) cl (fs , fl) =
    subst (WA (mapᴹ proj₂ (lanes c (mergeᶠ nothing) f d n [] o pre (lnS true (cutS true a s) ∷ post)))) (sym (win-snoc (lanesL post) (gh s)))
      (min-wa (retag (cutT true) (seek C (cutS true a s))) (lanes c (mergeᶠ nothing) f d n [] o (pre ++ [ lnS true (cutS true a s) ]) post)
              (step (gh s)) (win (earliest (lanesL post)))
        (subst (λ z → Agrees z (step (gh s))) (sym (on-true (seek C (cutS true a s))))
          (subst (λ b → HeadAt b (cand C (cutS true a s)) (cutS true a s)) cl (head-agrees C (cutS true a s) fs)))
        (lanes-wa c f d n o (pre ++ [ lnS true (cutS true a s) ]) post cl fl))
    where C = inLn true (inLanes (mergeᶠ nothing) f d n [] o pre post c)
  lanes-wa c f d n o pre (lnS false (cutS false a s) ∷ post) cl (fs , fl) =
    subst (WA (mapᴹ proj₂ (lanes c (mergeᶠ nothing) f d n [] o pre (lnS false (cutS false a s) ∷ post))))
          (sym (cong (λ L → win (earliest L)) (++-identityʳ (lanesL post))))
      (quiet-wa (retag (cutT false) (seek C (cutS false a s))) (lanes c (mergeᶠ nothing) f d n [] o (pre ++ [ lnS false (cutS false a s) ]) post)
                (win (earliest (lanesL post))) (off-quiet (seek C (cutS false a s)))
        (lanes-wa c f d n o (pre ++ [ lnS false (cutS false a s) ]) post cl fl))
    where C = inLn false (inLanes (mergeᶠ nothing) f d n [] o pre post c)

  lanes-quiet : ∀ {R Γ A B} (c : Ctx R Γ B) (f : A → Obs Timeline Γ B) d n (o : St Γ A) pre ls → closed c ≡ true → Lanes ls
              → Quiet (mapᴹ proj₂ (lanes c (mergeᶠ nothing) f d n [] o pre ls))
  lanes-quiet c f d n o pre [] cl _ = none
  lanes-quiet c f d n o pre (lnS true (cutS true a s) ∷ post) cl (fs , fl) =
    quiet-first (retag (cutT true) (seek C (cutS true a s))) (lanes c (mergeᶠ nothing) f d n [] o (pre ++ [ lnS true (cutS true a s) ]) post)
      (subst Quiet (sym (on-true (seek C (cutS true a s))))
        (subst (λ b → HeadAt b (cand C (cutS true a s)) (cutS true a s)) cl (head-agrees C (cutS true a s) fs)))
      (lanes-quiet c f d n o (pre ++ [ lnS true (cutS true a s) ]) post cl fl)
    where C = inLn true (inLanes (mergeᶠ nothing) f d n [] o pre post c)
  lanes-quiet c f d n o pre (lnS false (cutS false a s) ∷ post) cl (fs , fl) =
    quiet-first (retag (cutT false) (seek C (cutS false a s))) (lanes c (mergeᶠ nothing) f d n [] o (pre ++ [ lnS false (cutS false a s) ]) post)
      (off-quiet (seek C (cutS false a s)))
      (lanes-quiet c f d n o (pre ++ [ lnS false (cutS false a s) ]) post cl fl)
    where C = inLn false (inLanes (mergeᶠ nothing) f d n [] o pre post c)

  -- A joiner: what it was fed, in order, while live.
  join-head : ∀ {R Γ A} (c : Ctx R Γ A) j g x (ib : List (Pos × Machine.Ev A)) → Head c (joinS j g x ib)
  join-head c j false x [] with closed c
  ... | true  = none
  ... | false = exact refl
  join-head c j true x [] with closed c
  ... | true  = none
  ... | false = exact refl
  join-head c j false x ((q , e) ∷ ib) with closed c
  ... | true  = calm
  ... | false = early tt
  join-head c j true x ((q , nx a) ∷ ib) with closed c
  ... | true  = calm
  ... | false = exact refl
  join-head c j true x ((q , cp) ∷ ib) with closed c
  ... | true  = calm
  ... | false = exact refl

  -- A done node under an open observer shows nothing.
  done-quiet : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) → closed c ≡ false → Frag s → Done s → Quiet (cand c s)
  done-quiet c s cc fs ds =
    hush-quiet (subst (Agrees (cand c s)) (done-step s fs ds) (subst (λ b → HeadAt b (cand c s) s) cc (head-agrees c s fs)))

  conn-body : ∀ {Γ X B} k (o : St Γ X) (b : St (X ∷ Γ) B) → Conn k o b → Frag b
  conn-body (cs cl sl sa (just p) nothing ow r e) (pend s) b (fb , _) = fb
  conn-body (cs cl sl sa nothing as ow r e) o b (_ , fb , _) = fb

  -- A connect: its source's skip against its body's mark, as the stepper
  -- races them.
  conn-at : ∀ {R Γ X B} bb (c : Ctx R Γ B) k (o : St Γ X) (b : St (X ∷ Γ) B) → closed c ≡ bb → Conn k o b
          → HeadAt bb (cand c (connS k o b)) (connS k o b)
  conn-at true c k o b cc fk =
    quiet-first (ownBest c (connS k o b) (own (connS k o b))) (sourceT (over k) (seek (inSrc k b c) o) (seek (inBody k o c) b))
      (own-calm c k o b (own (connS k o b)))
      (src-quiet (over k) (seek (inSrc k b c) o) (seek (inBody k o c) b)
        (subst (λ x → HeadAt x (cand (inBody k o c) b) b) cc (head-agrees (inBody k o c) b (conn-body k o b fk))))
  -- Not yet subscribed, over.
  conn-at {B = B} false c (cs cl sl sa (just p) nothing (just q) r e) (pend s) b cc (fb , refl , ov) =
    subst (Agrees (cand c (connS K (pend s) b))) (sym (under-hush r S (gh b) (rest-hush {B = B} b fb (proj₂ (ov refl)))))
      (first-l (ownBest c (connS K (pend s) b) (own (connS K (pend s) b))) (seek (inBody K (pend s) c) b) _
        (done-quiet (inBody K (pend s) c) b cc fb (proj₁ (ov refl)))
        (own-first c K (pend s) b bodyM (at r) ((owedM , after q) ∷ []) _
          (union-upto (at r) _ _ (burstsˢ r S (step S)) (sub-bursts s r))))
    where K = cs cl sl sa (just p) nothing (just q) r e
          S = subscribe s r
  conn-at {B = B} false c (cs cl false sa (just p) nothing nothing r e) (pend s) b cc (fb , refl , ov) =
    subst (Agrees (cand c (connS K (pend s) b))) (sym (under-hush r S (gh b) (rest-hush {B = B} b fb (proj₂ (ov refl)))))
      (first-l (ownBest c (connS K (pend s) b) (own (connS K (pend s) b))) (seek (inBody K (pend s) c) b) _
        (done-quiet (inBody K (pend s) c) b cc fb (proj₁ (ov refl)))
        (own-first c K (pend s) b bodyM (at r) [] _
          (union-upto (at r) _ _ (burstsˢ r S (step S)) (sub-bursts s r))))
    where K = cs cl false sa (just p) nothing nothing r e
          S = subscribe s r
  -- Not yet subscribed, live.
  conn-at false c (cs cl true sa (just p) nothing nothing r e) (pend s) b cc (fb , refl , ov) =
    p1-live (foundᴹ (_ , _ , c , connS K (pend s) b) bodyM (at r)) r (seek (inBody K (pend s) c) b) r (gh b) (step (gh b)) S (step S)
      (sub-head s r) (subst (λ x → HeadAt x (cand (inBody K (pend s) c) b) b) cc (head-agrees (inBody K (pend s) c) b fb))
    where K = cs cl true sa (just p) nothing nothing r e
          S = subscribe s r
  -- Subscribed: over, the source live or ended.
  conn-at false c (cs false sl sa nothing as (just q) r e) o b cc (fo , fb , cn , ov) =
    conn-live-over c (cs false sl sa nothing as (just q) r e) o b cc refl fo fb (ov refl)
  conn-at false c (cs true sl sa nothing as (just q) r e) o b cc (fo , fb , cn , ov) =
    conn-ended-over c (cs true sl sa nothing as (just q) r e) o b cc fo fb (ov refl)
  conn-at false c (cs false false sa nothing as nothing r e) o b cc (fo , fb , cn , ov) =
    conn-live-over c (cs false false sa nothing as nothing r e) o b cc refl fo fb (ov refl)
  conn-at false c (cs true false sa nothing as nothing r e) o b cc (fo , fb , cn , ov) =
    conn-ended-over c (cs true false sa nothing as nothing r e) o b cc fo fb (ov refl)
  -- Subscribed and live.
  conn-at false c (cs false true sa nothing as nothing r e) o b cc (fo , fb , cn , ov) =
    calm-first (ownBest c (connS K o b) (own (connS K o b))) (sourceT false X Y) _ (own-calm c K o b (own (connS K o b)))
      (p3-live X Y r (gh b) (step (gh b)) (gh o) (step (gh o))
        (head-agrees (inSrc K b c) o fo) (subst (λ x → HeadAt x (cand (inBody K o c) b) b) cc (head-agrees (inBody K o c) b fb)))
    where K = cs false true sa nothing as nothing r e
          X = seek (inSrc K b c) o
          Y = seek (inBody K o c) b
  -- Subscribed, ended, not over.
  conn-at {X = X₀} false c (cs true true sa nothing as nothing r e) o b cc (fo , fb , cn , ov) =
    subst (Agrees (cand c (connS K o b))) (sym (ended-shut r e (gh o) (gh b) (rest-hush {B = X₀} o fo (cn refl))))
      (calm-first (ownBest c (connS K o b) (own (connS K o b))) (sourceT false X Y) _ (own-calm c K o b (own (connS K o b)))
        (shut-via r e (restᶜ (gh o)) (step (gh b))
          (src-calm false X Y (step (gh b)) (subst (λ x → HeadAt x (cand (inBody K o c) b) b) cc (head-agrees (inBody K o c) b fb)))))
    where K = cs true true sa nothing as nothing r e
          X = seek (inSrc K b c) o
          Y = seek (inBody K o c) b

  -- Over, the source live: its event's place unmoved.
  conn-live-over : ∀ {R Γ X B} (c : Ctx R Γ B) k (o : St Γ X) (b : St (X ∷ Γ) B) → closed c ≡ false → closed (inSrc k b c) ≡ false
                 → Frag o → Frag b → NoConn o × Done b × NoConn b
                 → Agrees (mapᴹ proj₂ (first (ownBest c (connS k o b) (own (connS k o b))) (sourceT true (seek (inSrc k b c) o) (seek (inBody k o c) b))))
                          (restˢ {B = B} (connectᶜ (CS.srcAt k) (gh b) (live (gh o))))
  conn-live-over {B = B} c k o b cc cs′ fo fb (no , db , nb) =
    subst (Agrees (mapᴹ proj₂ (first OWN (sourceT true X Y)))) (sym (under-hush (CS.srcAt k) (gh o) (gh b) (rest-hush {B = B} b fb nb)))
      (calm-first OWN (sourceT true X Y) _ (own-calm c k o b (own (connS k o b)))
        (over-src X Y (step (gh o)) _
          (subst (λ x → HeadAt x (cand (inSrc k b c) o) o) cs′ (head-agrees (inSrc k b c) o fo))
          (done-quiet (inBody k o c) b cc fb db)
          (over-step (CS.srcAt k) _ _ (gh o) (step (gh o)) (rest-hush {B = B} o fo no))))
    where OWN = ownBest c (connS k o b) (own (connS k o b))
          X = seek (inSrc k b c) o
          Y = seek (inBody k o c) b

  -- Over, the source ended: nothing rests, and nothing shows.
  conn-ended-over : ∀ {R Γ X B} (c : Ctx R Γ B) k (o : St Γ X) (b : St (X ∷ Γ) B) → closed c ≡ false
                  → Frag o → Frag b → NoConn o × Done b × NoConn b
                  → Agrees (mapᴹ proj₂ (first (ownBest c (connS k o b) (own (connS k o b))) (sourceT true (seek (inSrc k b c) o) (seek (inBody k o c) b))))
                           (restˢ {B = B} (connectᶜ (CS.srcAt k) (gh b) (ended (CS.endAt k) (restᶜ (gh o)))))
  conn-ended-over {X = X₀} {B = B} c k o b cc fo fb (no , db , nb) =
    subst (Agrees (mapᴹ proj₂ (first OWN (sourceT true X Y))))
      (sym (over-ended (CS.srcAt k) (CS.endAt k) (gh o) (gh b) (rest-hush {B = B} o fo no) (rest-hush {B = X₀} o fo no) (rest-hush {B = B} b fb nb)))
      (quiet-hush (quiet-first OWN (sourceT true X Y) (own-calm c k o b (own (connS k o b)))
        (src-quiet true X Y (done-quiet (inBody k o c) b cc fb db))))
    where OWN = ownBest c (connS k o b) (own (connS k o b))
          X = seek (inSrc k b c) o
          Y = seek (inBody k o c) b
