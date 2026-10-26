{-# OPTIONS --guardedness #-}

module adequacy.Engine.Head.Agrees where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; [_]; map)
open import Data.List.Properties using (++-identityʳ; map-++; length-map)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapᴹ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; trans; subst)

open import Tree using (Obs; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.MonotonicList.Events using (Pos; Timeline)
open import denotation.Unfold using (Node; Step; outˢ; skipˢ; endˢ; hushˢ; headˢ; step; restˢ; restsˢ; restᴹ; restsᶜ; restᶜ; unionˢ;
  Earliest; found; earliest; pick; Outer; doneᵒ; runᵒ; outerOf; goˢ; outerˢ; laneˢ; flatˢ;
  Source; live; ended; connectᶜ; burstingᶜ; underᶜ; subscribe; sourceˢ; bodyˢ; shutˢᵗ; burstsˢ; beforeˢ; idleᶜ; mapᶜ; scanᶜ) renaming (none to noneᴱ)
open import operation.Key using (at; after)
open import operation.PureObservable using (module Machine)
open Machine using (St; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS; Ctx; closed; inMap; inCut;
  Out; still; shows; Cand; seek; first; retag; mapT; cutT; nx; cp; attached; attAt; raceT; outerT; laneT; lanes; inOuter; inLanes; inLn; inScan; inTake;
  CS; cs; inSrc; inBody; own; ownBest; shift; over; sourceT; bodyM; owedM) renaming (found to foundᴹ)
open import adequacy.Engine.Meaning using (gh; lane; lanesL; deadL; outerG; poolG; doneG; srcG; vals; endOf)
open import adequacy.Engine.Shuts using (Shuts; none; upˢ; shutAll; shutAllˢ; Toldˢ; Toldᴸ; told-none; told-shut; shut-still; shut-comm; shut-flat; shut-conn; shut-done; shut-taken)
open import adequacy.Engine.Head using (cold-head; pend-head; scanS-head; takeS-head; limit-head; switch-head; exhaust-head; Agrees; Conn; Done; Frag; Head; HeadAt; Lanes; NoConn; Quiet; []; _∷_; att-head; calm; cand; done-head; done-step; early; exact; hush-quiet; map-head; none; of-head; off-head; off-quiet; on-head; pool-step; quiet-first; quiet-hush; rest-hush; HeadAtⁿ; shut-fixed; shut-pool; rest-hushⱽ; tape-still)
open import adequacy.Engine.Head.Race using (WA; calm-first; ended-shut; first-l; len-earliest; min-wa; on-true; outer-at; over-ended; over-src; over-step; own-calm; own-first; p1-live; p3-live; quiet-race; quiet-wa; race; shut-via; src-calm; src-quiet; sub-bursts; sub-head; under-hush; union-upto; win; win-snoc)

------------------------------------------------------------------------
-- Every state of the fragment, read through shuts that told it

-- A state the shuts leave as it is.
fixed : ∀ {Γ A} b x (s : St Γ A) (V : Shuts Γ) → shutAll V (gh s) ≡ gh s → HeadAtⁿ b x (gh s) → HeadAtⁿ b x (shutAll V (gh s))
fixed b x s V e h = subst (HeadAtⁿ b x) (sym e) h

-- A connect read through shuts: its body through the same shuts one
-- frame down, its source through them.
shut-gh-conn : ∀ {Γ X B} (V : Shuts Γ) k (o : St Γ X) (b : St (X ∷ Γ) B)
             → shutAll V (gh (connS k o b)) ≡ doneG (CS.owedAt k) (CS.srcLive k) (connectᶜ (CS.srcAt k) (shutAll (upˢ V) (gh b)) (shutAllˢ V (srcG k o)))
shut-gh-conn V k o b = trans (shut-done V (CS.owedAt k) (CS.srcLive k) _) (cong (doneG (CS.owedAt k) (CS.srcLive k)) (shut-conn V (CS.srcAt k) (gh b) (srcG k o)))

-- A subscribed connect with nothing connected below.
conn-fixed : ∀ {Γ X B} (V : Shuts Γ) cl sl sa as ow r e (o : St Γ X) (b : St (X ∷ Γ) B) → Toldˢ V o → Toldˢ (upˢ V) b
           → Frag o → Frag b → NoConn o → NoConn b
           → shutAll V (gh (connS (cs cl sl sa nothing as ow r e) o b)) ≡ gh (connS (cs cl sl sa nothing as ow r e) o b)
conn-fixed V false sl sa as ow r e o b to tb fo fb no nb =
  trans (shut-gh-conn V (cs false sl sa nothing as ow r e) o b)
    (cong₂ (λ N M → doneG ow sl (connectᶜ r N (live M))) (shut-fixed (upˢ V) b tb fb nb) (shut-fixed V o to fo no))
conn-fixed V true sl sa as ow r e o b to tb fo fb no nb =
  trans (shut-gh-conn V (cs true sl sa nothing as ow r e) o b)
    (cong₂ (λ N M → doneG ow sl (connectᶜ r N (ended e M))) (shut-fixed (upˢ V) b tb fb nb) (shut-fixed V (cutS false attached o) to (fo , no) no))

mutual
  head-agreesⱽ : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) (V : Shuts Γ) → Toldˢ V s → Frag s → HeadAtⁿ (closed c) (cand c s) (shutAll V (gh s))
  head-agreesⱽ c (ofS i p xs) V t _ = fixed (closed c) _ (ofS i p xs) V (shut-still V _ (λ _ _ → refl)) (of-head c i p xs)
  head-agreesⱽ c doneS        V t _ = fixed (closed c) _ doneS V (shut-still V idleᶜ (λ _ _ → refl)) (done-head c)
  head-agreesⱽ c (mapS f s) V t fs =
    subst (HeadAtⁿ (closed c) (cand c (mapS f s))) (sym (shut-comm (mapᶜ f) (λ _ _ _ → refl) V (gh s)))
      (map-head (closed c) f (seek (inMap f c) s) (shutAll V (gh s)) (head-agreesⱽ (inMap f c) s V t fs))
  head-agreesⱽ c (cutS true attached s) V t fs =
    on-head (closed c) (seek (inCut true attached c) s) (shutAll V (gh s)) (head-agreesⱽ (inCut true attached c) s V t fs)
  head-agreesⱽ c (cutS true (attAt p) s) V t fs =
    att-head (closed c) _ p (seek (inCut true (attAt p) c) s) (shutAll V (gh s)) (head-agreesⱽ (inCut true (attAt p) c) s V t fs)
  head-agreesⱽ c (cutS false attached s) V t (fs , ns) =
    fixed (closed c) _ (cutS false attached s) V (shut-fixed V (cutS false attached s) t (fs , ns) ns)
      (off-head (closed c) attached _ s fs ns (off-quiet (seek (inCut false attached c) s)))
  head-agreesⱽ c (cutS false (attAt p) s) V t (fs , ns) =
    fixed (closed c) _ (cutS false (attAt p) s) V (shut-fixed V (cutS false (attAt p) s) t (fs , ns) ns)
      (off-head (closed c) (attAt p) _ s fs ns (quiet-first (just (_ , after p , still)) (retag (cutT false) (seek (inCut false (attAt p) c) s)) calm (off-quiet (seek (inCut false (attAt p) c) s))))
  head-agreesⱽ c (flatS (mergeᶠ nothing) f d n [] o ls) V t fs = flat-at (closed c) c f d n o ls V t refl fs
  head-agreesⱽ c (connS k o b)    V (to , tb) fs = conn-at (closed c) c k o b V to tb refl fs
  head-agreesⱽ c (joinS j true x ib)  V t _ = fixed (closed c) _ (joinS j true x ib) V (told-shut V x j (vals ib) (endOf ib) t) (join-head c j true x ib)
  head-agreesⱽ c (joinS j false x ib) V t _ = fixed (closed c) _ (joinS j false x ib) V (shut-still V idleᶜ (λ _ _ → refl)) (join-head c j false x ib)
  head-agreesⱽ c (pend o)        V t _  = fixed (closed c) _ (pend o) V (shut-still V idleᶜ (λ _ _ → refl)) (pend-head c o)
  head-agreesⱽ c (coldS b l)     V t _  = fixed (closed c) _ (coldS b l) V (shut-still V _ (λ i e → tape-still b l i e)) (cold-head c b l)
  head-agreesⱽ c (scanS f z s)   V t fs =
    subst (HeadAtⁿ (closed c) (cand c (scanS f z s))) (sym (shut-comm (scanᶜ f z) (λ _ _ _ → refl) V (gh s)))
      (scanS-head c f z s V (head-agreesⱽ (inScan f z c) s V t fs))
  head-agreesⱽ c (lnS b s)       V t ()
  head-agreesⱽ c (takeS i q w s) V t fs =
    subst (HeadAtⁿ (closed c) (cand c (takeS i q w s))) (sym (shut-taken V i q w (gh s)))
      (takeS-head c i q w s V (head-agreesⱽ (inTake i q w c) s V t fs))
  head-agreesⱽ c (flatS (mergeᶠ nothing) f d n (_ ∷ _) o ls) V t ()
  head-agreesⱽ c (flatS (mergeᶠ (just m)) f d n q o ls) V t (fo , fl , _ , dd) = limit-head c m f d n q o ls V t fo fl dd
  head-agreesⱽ c (flatS switchᶠ f d n q o ls) V t (fo , fl , _ , dd) = switch-head c f d n q o ls V t fo fl dd
  head-agreesⱽ c (flatS exhaustᶠ f d n q o ls) V t (fo , fl , _ , dd) = exhaust-head c f d n q o ls V t fo fl dd

  -- A merge: the outer against its lanes, as the stepper races them.
  flat-at : ∀ {R Γ A B} b (c : Ctx R Γ B) (f : A → Obs Timeline Γ B) d n (o : St Γ A) ls (V : Shuts Γ) → Toldˢ V (flatS (mergeᶠ nothing) f d n [] o ls)
          → closed c ≡ b → Frag (flatS (mergeᶠ nothing) f d n [] o ls)
          → HeadAtⁿ b (cand c (flatS (mergeᶠ nothing) f d n [] o ls)) (shutAll V (gh (flatS (mergeᶠ nothing) f d n [] o ls)))
  flat-at true c f d n o ls V t cl (fo , fl , en , dd) =
    quiet-race d n (seek (inOuter (mergeᶠ nothing) f d n [] ls c) o) (lanes c (mergeᶠ nothing) f d n [] o [] ls)
      (subst (λ b → HeadAtⁿ b (cand (inOuter (mergeᶠ nothing) f d n [] ls c) o) (gh o)) cl (head-agreesⱽ (inOuter (mergeᶠ nothing) f d n [] ls c) o none (told-none o) fo))
      (lanes-quiet c f d n o [] ls cl fl)
  flat-at false c f d n o ls V (to , tl) cl (fo , fl , en , dd) =
    subst (λ m → Agrees (cand c FL) (step m)) (sym (shut-flat V (mergeᶠ nothing) (lane f) (outerG d (gh o)) (lanesL ls) [] (poolG d (gh o) (deadL ls))))
      (subst (λ st → Agrees (cand c FL) (flatˢ (mergeᶠ nothing) (lane f) OUT LS [] P st (earliest LS)))
        (sym (trans (cong step (shut-pool V d o ls to tl fo fl (λ e → proj₂ (dd e)))) (pool-step d o ls fo fl (λ e → proj₂ (dd e)))))
        (race (lane f) d n OUT LS P (earliest LS) (seek Cᵒ o) (lanes c (mergeᶠ nothing) f d n [] o [] ls)
          (outer-at d o V (seek Cᵒ o) fo to dd (subst (λ b → HeadAtⁿ b (cand Cᵒ o) (shutAll V (gh o))) cl (head-agreesⱽ Cᵒ o V to fo)))
          (lanes-wa c f d n o V [] ls cl fl tl) (trans en (sym (length-map (shutAll V) (lanesL ls)))) (len-earliest LS)))
    where FL  = flatS (mergeᶠ nothing) f d n [] o ls
          Cᵒ  = inOuter (mergeᶠ nothing) f d n [] ls c
          OUT = outerOf (mapᴹ (shutAll V) (outerG d (gh o)))
          LS  = map (shutAll V) (lanesL ls)
          P   = shutAll V (poolG d (gh o) (deadL ls))

  -- The engine's lanes, oldest first, against the stepper's earliest;
  -- `pre` the lanes walked, nearest first.
  lanes-wa : ∀ {R Γ A B} (c : Ctx R Γ B) (f : A → Obs Timeline Γ B) d n (o : St Γ A) (V : Shuts Γ) pre ls → closed c ≡ false → Lanes ls → Toldᴸ V ls
           → WA (mapᴹ proj₂ (lanes c (mergeᶠ nothing) f d n [] o pre ls)) (win (earliest (map (shutAll V) (lanesL ls))))
  lanes-wa c f d n o V pre [] cl _ _ = exact refl , tt
  lanes-wa c f d n o V pre (lnS true (cutS true a s) ∷ post) cl (fs , fl) (ts , tl) =
    subst (WA (mapᴹ proj₂ (lanes c (mergeᶠ nothing) f d n [] o pre (lnS true (cutS true a s) ∷ post))))
          (sym (trans (cong (λ L → win (earliest L)) (map-++ (shutAll V) (lanesL post) [ gh s ])) (win-snoc (map (shutAll V) (lanesL post)) (shutAll V (gh s)))))
      (min-wa (retag (cutT true) (seek C (cutS true a s))) (lanes c (mergeᶠ nothing) f d n [] o (lnS true (cutS true a s) ∷ pre) post)
              (step (shutAll V (gh s))) (win (earliest (map (shutAll V) (lanesL post))))
        (subst (λ z → Agrees z (step (shutAll V (gh s)))) (sym (on-true (seek C (cutS true a s))))
          (subst (λ b → HeadAtⁿ b (cand C (cutS true a s)) (shutAll V (gh s))) cl (head-agreesⱽ C (cutS true a s) V ts fs)))
        (lanes-wa c f d n o V (lnS true (cutS true a s) ∷ pre) post cl fl tl))
    where C = inLn true (inLanes (mergeᶠ nothing) f d n [] o pre post c)
  lanes-wa c f d n o V pre (lnS false (cutS false a s) ∷ post) cl (fs , fl) (_ , tl) =
    subst (WA (mapᴹ proj₂ (lanes c (mergeᶠ nothing) f d n [] o pre (lnS false (cutS false a s) ∷ post))))
          (sym (cong (λ L → win (earliest L)) (trans (map-++ (shutAll V) (lanesL post) []) (++-identityʳ (map (shutAll V) (lanesL post))))))
      (quiet-wa (retag (cutT false) (seek C (cutS false a s))) (lanes c (mergeᶠ nothing) f d n [] o (lnS false (cutS false a s) ∷ pre) post)
                (win (earliest (map (shutAll V) (lanesL post)))) (off-quiet (seek C (cutS false a s)))
        (lanes-wa c f d n o V (lnS false (cutS false a s) ∷ pre) post cl fl tl))
    where C = inLn false (inLanes (mergeᶠ nothing) f d n [] o pre post c)

  lanes-quiet : ∀ {R Γ A B} (c : Ctx R Γ B) (f : A → Obs Timeline Γ B) d n (o : St Γ A) pre ls → closed c ≡ true → Lanes ls
              → Quiet (mapᴹ proj₂ (lanes c (mergeᶠ nothing) f d n [] o pre ls))
  lanes-quiet c f d n o pre [] cl _ = none
  lanes-quiet c f d n o pre (lnS true (cutS true a s) ∷ post) cl (fs , fl) =
    quiet-first (retag (cutT true) (seek C (cutS true a s))) (lanes c (mergeᶠ nothing) f d n [] o (lnS true (cutS true a s) ∷ pre) post)
      (subst Quiet (sym (on-true (seek C (cutS true a s))))
        (subst (λ b → HeadAtⁿ b (cand C (cutS true a s)) (gh s)) cl (head-agreesⱽ C (cutS true a s) none (told-none s) fs)))
      (lanes-quiet c f d n o (lnS true (cutS true a s) ∷ pre) post cl fl)
    where C = inLn true (inLanes (mergeᶠ nothing) f d n [] o pre post c)
  lanes-quiet c f d n o pre (lnS false (cutS false a s) ∷ post) cl (fs , fl) =
    quiet-first (retag (cutT false) (seek C (cutS false a s))) (lanes c (mergeᶠ nothing) f d n [] o (lnS false (cutS false a s) ∷ pre) post)
      (off-quiet (seek C (cutS false a s)))
      (lanes-quiet c f d n o (lnS false (cutS false a s) ∷ pre) post cl fl)
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
    hush-quiet (subst (Agrees (cand c s)) (done-step s fs ds) (subst (λ b → HeadAtⁿ b (cand c s) (gh s)) cc (head-agreesⱽ c s none (told-none s) fs)))

  conn-body : ∀ {Γ X B} k (o : St Γ X) (b : St (X ∷ Γ) B) → Conn k o b → Frag b
  conn-body (cs cl sl sa (just p) nothing ow r e) (pend s) b (fb , _) = fb
  conn-body (cs cl sl sa nothing as ow r e) o b (_ , fb , _) = fb

  -- A connect: its source's skip against its body's mark, as the stepper
  -- races them.
  conn-at : ∀ {R Γ X B} bb (c : Ctx R Γ B) k (o : St Γ X) (b : St (X ∷ Γ) B) (V : Shuts Γ) → Toldˢ V o → Toldˢ (upˢ V) b → closed c ≡ bb → Conn k o b
          → HeadAtⁿ bb (cand c (connS k o b)) (shutAll V (gh (connS k o b)))
  conn-at true c k o b V to tb cc fk =
    quiet-first (ownBest c (connS k o b) (own (connS k o b))) (sourceT (over k) (seek (inSrc k b c) o) (seek (inBody k o c) b))
      (own-calm c k o b (own (connS k o b)))
      (src-quiet (over k) (seek (inSrc k b c) o) (seek (inBody k o c) b)
        (subst (λ x → HeadAtⁿ x (cand (inBody k o c) b) (gh b)) cc (head-agreesⱽ (inBody k o c) b none (told-none b) (conn-body k o b fk))))
  -- Not yet subscribed, over.
  conn-at {B = B} false c (cs cl sl sa (just p) nothing (just q) r e) (pend s) b V to tb cc (fb , refl , ov) =
    subst (λ m → Agrees (cand c (connS K (pend s) b)) (step m)) (sym (shut-gh-conn V K (pend s) b))
      (subst (Agrees (cand c (connS K (pend s) b))) (sym (under-hush r S N (rest-hushⱽ {B = B} (upˢ V) b tb fb (proj₂ (ov refl)))))
        (first-l (ownBest c (connS K (pend s) b) (own (connS K (pend s) b))) (seek (inBody K (pend s) c) b) _
          (done-quiet (inBody K (pend s) c) b cc fb (proj₁ (ov refl)))
          (own-first c K (pend s) b bodyM (at r) ((owedM , after q) ∷ []) _
            (union-upto (at r) _ _ (burstsˢ r S (step S)) (sub-bursts V s r)))))
    where K = cs cl sl sa (just p) nothing (just q) r e
          S = shutAll V (subscribe s r)
          N = shutAll (upˢ V) (gh b)
  conn-at {B = B} false c (cs cl false sa (just p) nothing nothing r e) (pend s) b V to tb cc (fb , refl , ov) =
    subst (λ m → Agrees (cand c (connS K (pend s) b)) (step m)) (sym (shut-gh-conn V K (pend s) b))
      (subst (Agrees (cand c (connS K (pend s) b))) (sym (under-hush r S N (rest-hushⱽ {B = B} (upˢ V) b tb fb (proj₂ (ov refl)))))
        (first-l (ownBest c (connS K (pend s) b) (own (connS K (pend s) b))) (seek (inBody K (pend s) c) b) _
          (done-quiet (inBody K (pend s) c) b cc fb (proj₁ (ov refl)))
          (own-first c K (pend s) b bodyM (at r) [] _
            (union-upto (at r) _ _ (burstsˢ r S (step S)) (sub-bursts V s r)))))
    where K = cs cl false sa (just p) nothing nothing r e
          S = shutAll V (subscribe s r)
          N = shutAll (upˢ V) (gh b)
  -- Not yet subscribed, live.
  conn-at false c (cs cl true sa (just p) nothing nothing r e) (pend s) b V to tb cc (fb , refl , ov) =
    subst (λ m → Agrees (cand c (connS K (pend s) b)) (step m)) (sym (shut-gh-conn V K (pend s) b))
      (p1-live (foundᴹ (_ , _ , c , connS K (pend s) b) bodyM (at r)) r (seek (inBody K (pend s) c) b) r N (step N) S (step S)
        (sub-head V s r) (subst (λ x → HeadAtⁿ x (cand (inBody K (pend s) c) b) N) cc (head-agreesⱽ (inBody K (pend s) c) b (upˢ V) tb fb)))
    where K = cs cl true sa (just p) nothing nothing r e
          S = shutAll V (subscribe s r)
          N = shutAll (upˢ V) (gh b)
  -- Subscribed: over, the source live or ended.
  conn-at false c (cs false sl sa nothing as (just q) r e) o b V to tb cc (fo , fb , cn , ov) =
    fixed false _ (connS K o b) V (conn-fixed V false sl sa as (just q) r e o b to tb fo fb (proj₁ (ov refl)) (proj₂ (proj₂ (ov refl))))
      (conn-live-over c K o b cc refl fo fb (ov refl))
    where K = cs false sl sa nothing as (just q) r e
  conn-at false c (cs true sl sa nothing as (just q) r e) o b V to tb cc (fo , fb , cn , ov) =
    fixed false _ (connS K o b) V (conn-fixed V true sl sa as (just q) r e o b to tb fo fb (proj₁ (ov refl)) (proj₂ (proj₂ (ov refl))))
      (conn-ended-over c K o b cc fo fb (ov refl))
    where K = cs true sl sa nothing as (just q) r e
  conn-at false c (cs false false sa nothing as nothing r e) o b V to tb cc (fo , fb , cn , ov) =
    fixed false _ (connS K o b) V (conn-fixed V false false sa as nothing r e o b to tb fo fb (proj₁ (ov refl)) (proj₂ (proj₂ (ov refl))))
      (conn-live-over c K o b cc refl fo fb (ov refl))
    where K = cs false false sa nothing as nothing r e
  conn-at false c (cs true false sa nothing as nothing r e) o b V to tb cc (fo , fb , cn , ov) =
    fixed false _ (connS K o b) V (conn-fixed V true false sa as nothing r e o b to tb fo fb (proj₁ (ov refl)) (proj₂ (proj₂ (ov refl))))
      (conn-ended-over c K o b cc fo fb (ov refl))
    where K = cs true false sa nothing as nothing r e
  -- Subscribed and live.
  conn-at false c (cs false true sa nothing as nothing r e) o b V to tb cc (fo , fb , cn , ov) =
    subst (λ m → Agrees (cand c (connS K o b)) (step m)) (sym (shut-gh-conn V K o b))
      (calm-first (ownBest c (connS K o b) (own (connS K o b))) (sourceT false X Y) _ (own-calm c K o b (own (connS K o b)))
        (p3-live X Y r N (step N) M (step M)
          (head-agreesⱽ (inSrc K b c) o V to fo) (subst (λ x → HeadAtⁿ x (cand (inBody K o c) b) N) cc (head-agreesⱽ (inBody K o c) b (upˢ V) tb fb))))
    where K = cs false true sa nothing as nothing r e
          X = seek (inSrc K b c) o
          Y = seek (inBody K o c) b
          N = shutAll (upˢ V) (gh b)
          M = shutAll V (gh o)
  -- Subscribed, ended, not over.
  conn-at {X = X₀} false c (cs true true sa nothing as nothing r e) o b V to tb cc (fo , fb , cn , ov) =
    subst (λ m → Agrees (cand c (connS K o b)) (step m)) (sym (shut-gh-conn V K o b))
      (subst (λ m → Agrees (cand c (connS K o b)) (step (connectᶜ r N (ended e m)))) (sym (shut-fixed V (cutS false attached o) to (fo , cn refl) (cn refl)))
        (subst (Agrees (cand c (connS K o b))) (sym (ended-shut r e (gh o) N (rest-hush {B = X₀} o fo (cn refl))))
          (calm-first (ownBest c (connS K o b) (own (connS K o b))) (sourceT false X Y) _ (own-calm c K o b (own (connS K o b)))
            (shut-via r e (restᶜ (gh o)) (step N)
              (src-calm false X Y (step N) (subst (λ x → HeadAtⁿ x (cand (inBody K o c) b) N) cc (head-agreesⱽ (inBody K o c) b (upˢ V) tb fb)))))))
    where K = cs true true sa nothing as nothing r e
          X = seek (inSrc K b c) o
          Y = seek (inBody K o c) b
          N = shutAll (upˢ V) (gh b)

  -- Over, the source live: its event's place unmoved.
  conn-live-over : ∀ {R Γ X B} (c : Ctx R Γ B) k (o : St Γ X) (b : St (X ∷ Γ) B) → closed c ≡ false → closed (inSrc k b c) ≡ false
                 → Frag o → Frag b → NoConn o × Done b × NoConn b
                 → Agrees (mapᴹ proj₂ (first (ownBest c (connS k o b) (own (connS k o b))) (sourceT true (seek (inSrc k b c) o) (seek (inBody k o c) b))))
                          (restˢ {B = B} (connectᶜ (CS.srcAt k) (gh b) (live (gh o))))
  conn-live-over {B = B} c k o b cc cs′ fo fb (no , db , nb) =
    subst (Agrees (mapᴹ proj₂ (first OWN (sourceT true X Y)))) (sym (under-hush (CS.srcAt k) (gh o) (gh b) (rest-hush {B = B} b fb nb)))
      (calm-first OWN (sourceT true X Y) _ (own-calm c k o b (own (connS k o b)))
        (over-src X Y (step (gh o)) _
          (subst (λ x → HeadAt x (cand (inSrc k b c) o) o) cs′ (head-agreesⱽ (inSrc k b c) o none (told-none o) fo))
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

head-agrees : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) → Frag s → Head c s
head-agrees c s fs = head-agreesⱽ c s none (told-none s) fs
