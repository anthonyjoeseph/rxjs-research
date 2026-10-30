{-# OPTIONS --guardedness #-}

-- THE DIRECT LINK: the engine run against the emission set's rows, with
-- no stepper and no tower between them.  A step keeps the visible rows or
-- shows the least and drops it, by mode: a subscription entered as the
-- rows of what it begins, a rise read up one frame, a mark run where the
-- search's bound says it leads.
--
-- The link is grown one former at a time.  Subscribing to a former not
-- yet grown hands the rest of the run to that former's own leaf
-- (`beyond-take` and its siblings), so `reach` is total by pattern
-- matching: growing a former turns its leaf into the arms the link needs
-- for it, and the coverage checker names every former still owed.
module adequacy.Sim where

open import Data.Bool using (true; false; if_then_else_; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (_≡ᵇ_)
open import Data.List using (List; []; _∷_; [_]; null)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Data.List.Relation.Unary.Any using () renaming (here to hd)
open import Data.Sum using (_⊎_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _,_; proj₁)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to tt₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.List using (_ʳ++_)

open import Tree using (Obs; Later; mergeᶠ; switchᶠ; exhaustᶠ; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.Events using (Timeline; root; ix; timelineAt; emit; stall; close)
open import denotation.EmissionSet using (DenEnv; EmissionSet; out; end; MapT; map-out; map-skip; map-pin; map-end; module Scan; _≼_; enter; ⟦_⟧; Proper)
open import denotation.Laws.Modulus using (≺-irrefl; ≺-absurd)
open import denotation.Laws.Worlds using (GoodEnv; Lawful)
open import denotation.Laws using (inv-⟦⟧; good-cons)
open import operation.PureObservable using (PureObs; module Machine; module Driver; Tape; play; ending; over; opening)
open Machine using (St; Ctx; Conf; ⟨_,_,_,_⟩; subscribing; absorbed; rising; load; moved; plug; search; found; Mark; ofM; attM;
                    rise; run; start; dequeue; settle; alive; ended; mapEv; nx; cp; attAt; attached; Torn;
                    Stepped; quiet; begin; admit; closed; killAll; unsubIf; free; cpAt; cutAt; overAt; CS; cs; feed; closedUp; _⊕_;
                    bodyM; srcAttM; owedM; joinM; leafM; Poke; gone; leaf;
                    pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
                    top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody)
                    renaming (Ev to Evᴹ; Shown to Shownᴹ; step to stepᴹ)
open import adequacy.Rows using (env; rows; Closed; here; RT; toEv; Visible; Vis; Past; Plus; old; new; _≃_; _⇄_; silent; shown; Steps;
  Shows*; Shows*-≃; ≃-sym; conv; []; _∷_; tau; val; fin)
open import adequacy.Bound using (Good; G; Rooted; mergeG₀)
open import adequacy.Up using (up-≃; ≃-refl; vis-≃)
open import adequacy.Skip using (After)
open import adequacy.Inv using (Inv; inv; good; Sim; Ends; GoodC; good-split; open-alive)
open import adequacy.Owes using (srcO-≃)
open import adequacy.LaneCp using (rise-lane-cp)
open import adequacy.AbsOf using (abs-of)
open import denotation.Read using (Meets)
open import adequacy.Owes using (Swap; good-swap)
open import adequacy.Enter using (enter-map; enter-scan; enter-merge; flat-∅)

postulate
  -- A GOOD TREE'S CONNECT SOURCE READS LAWFULLY: its rows reachable, one
  -- event at a position, none below another, as the binder its body reads.
  src-lawful : ∀ {R Γ X B} (k : CS) (o : St Γ X) (b : St (X ∷ Γ) B) (c : Ctx R Γ B) → Good []ᴬ (plug c (connS k o b))
             → Lawful (Proper (λ q e → rows (env c) o q e ⊎ Closed k q e))

-- A good tree's environment keeps the invariant: each binder a
-- connect's source.
env-good : ∀ {R Γ A} (c : Ctx R Γ A) {s} → GoodC c → Good []ᴬ (plug c s) → GoodEnv (env c)
env-good top                                         _  _ ()
env-good (inMap f c)                                 gc g = env-good c gc g
env-good (inScan f z c)                              gc g = env-good c gc g
env-good (inCut l a c)                               gc g = env-good c gc g
env-good (inLn b c)                                  gc g = env-good c gc g
env-good (inOuter (mergeᶠ nothing) f d n q ls c)     gc g = env-good c gc g
env-good (inLanes (mergeᶠ nothing) f d n q o pre post c) gc g = env-good c gc g
env-good (inOuter (mergeᶠ (just _)) f d n q ls c)    ()
env-good (inOuter switchᶠ f d n q ls c)              ()
env-good (inOuter exhaustᶠ f d n q ls c)             ()
env-good (inLanes (mergeᶠ (just _)) f d n q o pre post c) ()
env-good (inLanes switchᶠ f d n q o pre post c)      ()
env-good (inLanes exhaustᶠ f d n q o pre post c)     ()
env-good (inTake i q w c)                            ()
env-good (inSrc k b c)                               gc g = env-good c gc g
env-good (inBody k o c) {s}                          gc g = good-cons (src-lawful k o s c g) (env-good c gc g)

------------------------------------------------------------------------
-- Subscribing

postulate
  sub-empty : ∀ {R Γ A} (c : Ctx R Γ A) q p → Sim ⟨ c , pend empty q , subscribing , p ⟩ [] ⟨ c , ofS 0 q [] , absorbed , q ⟩
  sub-of    : ∀ {R Γ A} (c : Ctx R Γ A) xs q p → Sim ⟨ c , pend (of xs) q , subscribing , p ⟩ [] ⟨ c , ofS 0 q xs , absorbed , q ⟩

-- A map entered: its source pending under it.
sub-map : ∀ {R Γ A B} (c : Ctx R Γ B) (f : A → B) s q p → Sim ⟨ c , pend (map f s) q , subscribing , p ⟩ [] ⟨ inMap f c , pend s q , subscribing , q ⟩
sub-map c f s q p (inv g (uc , _ , ok , so)) = inv (good-swap c sw g) (uc , tt , ok , srcO-≃ c (enter-map (env c) f s q) so) , silent (vis-≃ (up-≃ c (enter-map (env c) f s q)))
  where
    sw : Swap (env c) doneS (mapS f doneS)
    sw = record { same = (λ ()) ⇄ (λ { (map-out ()) ; (map-skip ()) ; (map-pin ()) ; (map-end ()) }) ; live≡ = refl ; node = λ _ x → x ; lane = λ _ () ; body = λ _ _ () ; held = λ () }

-- A scan entered: its source pending under it.
sub-scan : ∀ {R Γ A B} (c : Ctx R Γ B) (f : B → A → B) z s q p → Sim ⟨ c , pend (scan f z s) q , subscribing , p ⟩ [] ⟨ inScan f z c , pend s q , subscribing , q ⟩
sub-scan c f z s q p (inv g (uc , _ , ok , so)) = inv (good-swap c sw g) (uc , tt , ok , srcO-≃ c (enter-scan (env c) f z s q) so) , silent (vis-≃ (up-≃ c (enter-scan (env c) f z s q)))
  where
    sw : Swap (env c) doneS (scanS f z doneS)
    sw = record { same = (λ ()) ⇄ (λ { (Scan.sval (Scan.acc₀ () _)) ; (Scan.sval (Scan.acc _ () _ _)) ; (Scan.sstep ()) ; (Scan.spin ()) ; (Scan.send ()) }) ; live≡ = refl ; node = λ _ x → x ; lane = λ _ () ; body = λ _ _ () ; held = λ () }

-- A merge entered: its outer pending under it, attached at `p`, nothing begun.
sub-merge : ∀ {R Γ A B} (c : Ctx R Γ B) f (s : Obs Timeline Γ A) q p
          → Sim ⟨ c , pend (flatMap (mergeᶠ nothing) f s) q , subscribing , p ⟩ [] ⟨ inCut true (attAt q) (inOuter (mergeᶠ nothing) f false 0 [] [] c) , pend s q , subscribing , q ⟩
sub-merge {A = A} {B} c f s q p (inv g (uc , _ , ok , so)) = inv (good-swap c sw g) ((tt , uc) , tt , ok , srcO-≃ c (enter-merge (env c) f s q) so) , silent (vis-≃ (up-≃ c (enter-merge (env c) f s q)))
  where
    -- The outer about to enter at `p`: inside its own entry, nothing begun.
    rt : Rooted (env c) (rows (env c) (cutS true (attAt q) doneS)) []
    rt = record { o₀ = s ; p₀ = q ; inv = inv-⟦⟧ s (env c) (env-good c (proj₁ (good-split c _ g)) g) q ok ; sub = λ () ; qs = [] ; roots = tt }
    node′ : ∀ v → G (env c) v (doneS {A = B}) → G (env c) v (flatS (mergeᶠ nothing) f false 0 [] (cutS true (attAt q) (doneS {A = A})) [])
    node′ true  _ = record { outer = tt₁ ; lanesG = tt₁ ; fresh = refl ; count = refl ; spent = λ () ; rooted = rt }
    node′ false _ = mergeG₀ tt₁ tt₁ refl
    sw : Swap (env c) doneS (flatS (mergeᶠ nothing) f false 0 [] (cutS true (attAt q) doneS) [])
    sw = record { same = ≃-sym (flat-∅ _ false) ; live≡ = refl ; node = node′ ; lane = λ _ () ; body = λ _ _ () ; held = λ () }

postulate
  -- A CONNECT ENTERED: its body pending under `ix 0`, its source pending
  -- under `ix 1` until the body's subscription exists.
  sub-connect : ∀ {R Γ A B} (c : Ctx R Γ B) (s : Obs Timeline Γ A) b q p
              → Sim ⟨ c , pend (connect s b) q , subscribing , p ⟩ []
                    ⟨ inBody (cs false true false (just q) nothing nothing q root) (pend s (q ⊕ [ ix 1 ])) c , pend b (q ⊕ [ ix 0 ]) , subscribing , q ⊕ [ ix 0 ] ⟩
  -- A COLD ENTERED: its timeline read at the subscription, its tape
  -- begun there.
  sub-cold : ∀ {R Γ A} (c : Ctx R Γ A) (x : Timeline A) q p
           → Sim ⟨ c , pend (cold x) q , subscribing , p ⟩ [] ⟨ c , coldS true (opening q (timelineAt x q)) , absorbed , q ⟩
  -- A DEFER ENTERED: its body pending one level down, its rows those the
  -- defer begins with there.
  sub-defer : ∀ {R Γ A} (c : Ctx R Γ A) l q p
            → Sim ⟨ c , pend (defer l) q , subscribing , p ⟩ [] ⟨ c , pend (Later.force l) (q ⊕ [ ix 1 ]) , subscribing , q ⊕ [ ix 1 ] ⟩
  -- A JOINER OF A COMPLETED SUBJECT: its end owed, under `last`.
  sub-joined : ∀ {R Γ A} (c : Ctx R Γ A) (x : A ∈ Γ) q p → closedUp c x ≡ true
             → Sim ⟨ c , pend (connected x) q , subscribing , p ⟩ [] ⟨ c , ofS 0 q [] , absorbed , q ⟩
  -- A JOINER OF A LIVE SUBJECT: joined where it subscribed, nothing queued.
  sub-join : ∀ {R Γ A} (c : Ctx R Γ A) (x : A ∈ Γ) q p → closedUp c x ≡ false
           → Sim ⟨ c , pend (connected x) q , subscribing , p ⟩ [] ⟨ c , joinS q true x [] , absorbed , q ⟩

stay : ∀ {R} {k : Conf R} → Sim k [] k
stay i = i , silent ((λ x → x) ⇄ (λ x → x))

-- A node already running, not a pending program.
Running : ∀ {Γ A} → St Γ A → Set
Running (pend _ _) = ⊥
Running _        = ⊤

-- Subscribing to a node already running: nothing to do.
sub-sim : ∀ {R Γ A} {k′ : Conf R} {sh t} (c : Ctx R Γ A) (s : St Γ A) p → Running s → stepᴹ ⟨ c , s , subscribing , p ⟩ ≡ moved k′ sh t → Sim ⟨ c , s , subscribing , p ⟩ sh k′
sub-sim c (pend _ _)        p () _
sub-sim c (coldS b l)       p _ refl = stay
sub-sim c (ofS i q xs)      p _ refl = stay
sub-sim c doneS             p _ refl = stay
sub-sim c (mapS f s)        p _ refl = stay
sub-sim c (scanS f z s)     p _ refl = stay
sub-sim c (cutS l a s)      p _ refl = stay
sub-sim c (lnS b s)         p _ refl = stay
sub-sim c (takeS i q w s)   p _ refl = stay
sub-sim c (flatS op f d n q o ls) p _ refl = stay
sub-sim c (connS k o b)     p _ refl = stay
sub-sim c (joinS j g x ib)  p _ refl = stay

------------------------------------------------------------------------
-- Rising

-- At the root: the event shown, the least row, and dropped.
rise-top : ∀ {R} (s : St [] R) e p → Sim ⟨ top , s , rising e , p ⟩ [ (p , e) ] ⟨ top , s , absorbed , p ⟩
rise-top s e p i with alive s in al
rise-top s e p (inv g (_ , _ , _ , op , _)) | false = ⊥-elim (open-alive s op al)
rise-top s e p (inv g (_ , _ , os , _ , ld , _)) | true = inv g os , shown (new , vis e) least (to′ ⇄ from′)
  where
    vis : ∀ e → Visible (toEv e)
    vis (nx _) = tt
    vis cp     = tt
    least : ∀ {q e′} → Vis (Plus (rows []ᴬ s) p (toEv e)) q e′ → p ≼ q
    least {q} (old r , v) qp = ≺-absurd {q} {p} qp (ld r)
    least (new , v)       qp = ≺-irrefl {p} qp
    to′ : ∀ {q e′} → Vis (Past p (Plus (rows []ᴬ s) p (toEv e))) q e′ → Vis (rows []ᴬ s) q e′
    to′ ((old r , _) , v) = r , v
    to′ ((new , pp) , v)  = ⊥-elim (≺-irrefl {p} pp)
    from′ : ∀ {q e′} → Vis (rows []ᴬ s) q e′ → Vis (Past p (Plus (rows []ᴬ s) p (toEv e))) q e′
    from′ (r , v) = (old r , ld r) , v

after-map : ∀ {A B} (f : A → B) {t : EmissionSet A} {p} → After p t → After p (MapT f t)
after-map f a (map-out r)  = a r
after-map f a (map-skip r) = a r
after-map f a (map-pin r)  = a r
after-map f a (map-end r)  = a r

ends-map : ∀ {A B} (f : A → B) {t : EmissionSet A} e → Ends e t → Ends (mapEv f e) (MapT f t)
ends-map f (nx _) _  = tt
ends-map f cp     em (map-out r)  = em r
ends-map f cp     em (map-skip r) = em r
ends-map f cp     em (map-pin r)  = em r
ends-map f cp     em (map-end r)  = em r

map-plus : ∀ {A B} (f : A → B) (t : EmissionSet A) p e → MapT f (Plus t p (toEv e)) ≃ Plus (MapT f t) p (toEv (mapEv f e))
map-plus f t p (nx a) = to′ ⇄ from′
  where
    to′ : ∀ {q e′} → MapT f (Plus t p (out a)) q e′ → Plus (MapT f t) p (out (f a)) q e′
    to′ (map-out (old r))  = old (map-out r)
    to′ (map-out new)      = new
    to′ (map-skip (old r)) = old (map-skip r)
    to′ (map-pin (old r))  = old (map-pin r)
    to′ (map-end (old r))  = old (map-end r)
    from′ : ∀ {q e′} → Plus (MapT f t) p (out (f a)) q e′ → MapT f (Plus t p (out a)) q e′
    from′ (old (map-out r))  = map-out (old r)
    from′ (old (map-skip r)) = map-skip (old r)
    from′ (old (map-pin r))  = map-pin (old r)
    from′ (old (map-end r))  = map-end (old r)
    from′ new                = map-out new
map-plus f t p cp = to′ ⇄ from′
  where
    to′ : ∀ {q e′} → MapT f (Plus t p end) q e′ → Plus (MapT f t) p end q e′
    to′ (map-out (old r))  = old (map-out r)
    to′ (map-skip (old r)) = old (map-skip r)
    to′ (map-pin (old r))  = old (map-pin r)
    to′ (map-end (old r))  = old (map-end r)
    to′ (map-end new)      = new
    from′ : ∀ {q e′} → Plus (MapT f t) p end q e′ → MapT f (Plus t p end) q e′
    from′ (old (map-out r))  = map-out (old r)
    from′ (old (map-skip r)) = map-skip (old r)
    from′ (old (map-pin r))  = map-pin (old r)
    from′ (old (map-end r))  = map-end (old r)
    from′ new                = map-end new

-- A live node's rising row: its rows and the event.
risen : ∀ {Γ A} (ρ : DenEnv Γ) (s : St Γ A) e p → alive s ≡ true → here ρ s (rising e) p ≃ Plus (rows ρ s) p (toEv e)
risen ρ s e p al with alive s
risen ρ s e p refl | true = ≃-refl

rise-map : ∀ {R Γ A B} (f : A → B) (c : Ctx R Γ B) s e p → Sim ⟨ inMap f c , s , rising e , p ⟩ [] ⟨ c , mapS f s , rising (mapEv f e) , p ⟩
rise-map f c s e p i with alive s in al
rise-map f c s e p (inv g (_ , _ , _ , op , _)) | false = ⊥-elim (open-alive s op al)
rise-map f c s e p (inv g (uc , lc , os , _ , af , en , so)) | true =
  inv g (uc , lc , os , tt , after-map f {p = p} af , ends-map f e en , srcO-≃ c (map-plus f (rows (env c) s) p e) (srcO-≃ (inMap f c) (risen (env c) s e p al) so)) , silent (vis-≃ (up-≃ c (map-plus f (rows (env c) s) p e)))

rise-cut : ∀ {R Γ A} l a (c : Ctx R Γ A) s e p → Sim ⟨ inCut l a c , s , rising e , p ⟩ [] ⟨ c , cutS l a s , (if l then rising e else absorbed) , p ⟩
rise-cut false a c s e p (inv g (() , _))
rise-cut true  a c s e p i with alive s in al
rise-cut true  a c s e p (inv g (_ , _ , _ , op , _)) | false = ⊥-elim (open-alive s op al)
rise-cut true  a c s e p (inv g (uc , lc , os , _ , af , en , so)) | true = inv g (uc , lc , os , tt , af , en , srcO-≃ c (risen (env c) s e p al) so) , silent ≃-refl

rise-ln : ∀ {R Γ A} b (c : Ctx R Γ A) s e p → Sim ⟨ inLn b c , s , rising e , p ⟩ [] ⟨ c , lnS b s , rising e , p ⟩
rise-ln false c s e p (inv g (() , _))
rise-ln true  c s e p i with alive s in al
rise-ln true  c s e p (inv g (_ , _ , _ , op , _)) | false = ⊥-elim (open-alive s op al)
rise-ln true  c s e p (inv g (uc , lc , os , _ , af , en , so)) | true = inv g (uc , lc , os , tt , af , en , srcO-≃ c (risen (env c) s e p al) so) , silent ≃-refl

-- A SCAN'S VALUE FOLDED: the source's least value leaves as the fold of
-- it, and the rest of the source's rows fold from there.
postulate
  rise-scan-nx : ∀ {R Γ A B} (f : B → A → B) z (c : Ctx R Γ B) s a p → Sim ⟨ inScan f z c , s , rising (nx a) , p ⟩ [] ⟨ c , scanS f (f z a) s , rising (nx (f z a)) , p ⟩
  rise-scan-cp : ∀ {R Γ A B} (f : B → A → B) z (c : Ctx R Γ B) s p → Sim ⟨ inScan f z c , s , rising cp , p ⟩ [] ⟨ c , scanS f z s , rising cp , p ⟩

postulate
  -- AN OUTER'S VALUE BEGINS ITS LANE.
  rise-outer-nx : ∀ {R Γ A B} f d n q ls (c : Ctx R Γ B) (o : St Γ A) a p
                → Sim ⟨ inOuter (mergeᶠ nothing) f d n q ls c , o , rising (nx a) , p ⟩ [] (start c (mergeᶠ nothing) f d n q o ls a p)
  -- AN OUTER'S END, SHOWN ONLY WITH NO LANE RUNNING.
  rise-outer-cp : ∀ {R Γ A B} f d n q ls (c : Ctx R Γ B) (o : St Γ A) p
                → Sim ⟨ inOuter (mergeᶠ nothing) f d n q ls c , o , rising cp , p ⟩ [] ⟨ c , flatS (mergeᶠ nothing) f true n q o ls , (if d then absorbed else settle true n (null q)) , p ⟩
  -- A LANE'S VALUE PASSES, UNLESS THE LANE IS OVER.
  rise-lane-nx : ∀ {R Γ A B} f d n q (o : St Γ A) pre post (c : Ctx R Γ B) s b p
               → Sim ⟨ inLanes (mergeᶠ nothing) f d n q o pre post c , s , rising (nx b) , p ⟩ []
                     (if alive s then ⟨ c , flatS (mergeᶠ nothing) f d n q o (pre Data.List.ʳ++ s ∷ post) , rising (nx b) , p ⟩
                                 else ⟨ c , flatS (mergeᶠ nothing) f d n q o (pre Data.List.ʳ++ s ∷ post) , absorbed , p ⟩)

  -- A SOURCE'S VALUE FEEDS ITS BODY.
  rise-src-nx : ∀ {R Γ X B} (k : CS) (b : St (X ∷ Γ) B) (c : Ctx R Γ B) s a p
              → Sim ⟨ inSrc k b c , s , rising (nx a) , p ⟩ [] ⟨ c , connS k s (feed (hd refl) p (nx a) b) , absorbed , p ⟩
  -- A SOURCE'S END FEEDS ITS BODY AND CLOSES ITS CONNECT.
  rise-src-cp : ∀ {R Γ X B} (k : CS) (b : St (X ∷ Γ) B) (c : Ctx R Γ B) s p
              → Sim ⟨ inSrc k b c , s , rising cp , p ⟩ [] ⟨ c , connS (record k { closed = true ; endAt = p }) s (feed (hd refl) p cp b) , absorbed , p ⟩
  -- A BODY'S VALUE IS ITS CONNECT'S.
  rise-body-nx : ∀ {R Γ X B} (k : CS) (o : St Γ X) (c : Ctx R Γ B) s x p
               → Sim ⟨ inBody k o c , s , rising (nx x) , p ⟩ [] ⟨ c , connS k o s , rising (nx x) , p ⟩
  -- A BODY'S END IS ITS CONNECT'S, ITS SOURCE OWED A TEARDOWN THERE.
  rise-body-cp : ∀ {R Γ X B} (k : CS) (o : St Γ X) (c : Ctx R Γ B) s p
               → Sim ⟨ inBody k o c , s , rising cp , p ⟩ [] ⟨ c , connS (record k { owedAt = just p }) o s , rising cp , p ⟩

rise-sim : ∀ {R Γ A} {k′ : Conf R} {sh t} (c : Ctx R Γ A) (s : St Γ A) e p → stepᴹ ⟨ c , s , rising e , p ⟩ ≡ moved k′ sh t → Sim ⟨ c , s , rising e , p ⟩ sh k′
rise-sim top            s e p refl = rise-top s e p
rise-sim (inMap f c)    s e p refl = rise-map f c s e p
rise-sim (inScan f z c) s (nx a) p refl = rise-scan-nx f z c s a p
rise-sim (inScan f z c) s cp     p refl = rise-scan-cp f z c s p
rise-sim (inCut l a c)  s e p refl = rise-cut l a c s e p
rise-sim (inLn b c)     s e p refl = rise-ln b c s e p
rise-sim (inOuter (mergeᶠ nothing) f d n q ls c) o (nx a) p refl = rise-outer-nx f d n q ls c o a p
rise-sim (inOuter (mergeᶠ nothing) f d n q ls c) o cp     p refl = rise-outer-cp f d n q ls c o p
rise-sim (inLanes (mergeᶠ nothing) f d n q o pre post c) s (nx b) p refl = rise-lane-nx f d n q o pre post c s b p
rise-sim (inLanes (mergeᶠ nothing) f d n q o pre post c) s cp     p refl = rise-lane-cp f d n q o pre post c s p
rise-sim c@(inTake _ _ _ _)                    s e p eq i = ⊥-elim (proj₁ (good-split c s (good i)))
rise-sim c@(inOuter (mergeᶠ (just _)) _ _ _ _ _ _) s e p eq i = ⊥-elim (proj₁ (good-split c s (good i)))
rise-sim c@(inOuter switchᶠ _ _ _ _ _ _)       s e p eq i = ⊥-elim (proj₁ (good-split c s (good i)))
rise-sim c@(inOuter exhaustᶠ _ _ _ _ _ _)      s e p eq i = ⊥-elim (proj₁ (good-split c s (good i)))
rise-sim c@(inLanes (mergeᶠ (just _)) _ _ _ _ _ _ _ _) s e p eq i = ⊥-elim (proj₁ (good-split c s (good i)))
rise-sim c@(inLanes switchᶠ _ _ _ _ _ _ _ _)   s e p eq i = ⊥-elim (proj₁ (good-split c s (good i)))
rise-sim c@(inLanes exhaustᶠ _ _ _ _ _ _ _ _)  s e p eq i = ⊥-elim (proj₁ (good-split c s (good i)))
rise-sim (inSrc k b c)  s (nx a) p refl = rise-src-nx k b c s a p
rise-sim (inSrc k b c)  s cp     p refl = rise-src-cp k b c s p
rise-sim (inBody k o c) s (nx x) p refl = rise-body-nx k o c s x p
rise-sim (inBody k o c) s cp     p refl = rise-body-cp k o c s p

------------------------------------------------------------------------
-- A mark run

-- The marks a good tree's nodes own.
data Marked {Γ : List Set} : ∀ {A} → St Γ A → Mark → Set₁ where
  ofK  : ∀ {A} i p (xs : List A) → Marked (ofS i p xs) ofM
  attK : ∀ {A} l p (s : St Γ A) → Marked (cutS l (attAt p) s) attM
  conK : ∀ {X A} k (o : St Γ X) (b : St (X ∷ Γ) A) m → m ≡ bodyM ⊎ (m ≡ srcAttM ⊎ m ≡ owedM) → Marked (connS k o b) m
  joinK : ∀ {A} j g (x : A ∈ Γ) ib → Marked (joinS j g x ib) joinM
  leafK : ∀ {A} b (l : Tape A) → Marked (coldS b l) leafM

postulate
  -- WHAT A GOOD TREE'S SEARCH FINDS: an of's next, a switch's attach, a
  -- connect's own, a joiner's next, or a cold's turn.
  found-mark : ∀ {R Γ′ A′} (c : Ctx R Γ′ A′) s {Γ A c′ s′ m κ} → Good []ᴬ (plug c s) → search top (plug c s) ≡ just (found (Γ , A , c′ , s′) m κ) → Marked s′ m

  -- A SWITCH ATTACHED: nothing owed changes.
  abs-att : ∀ {R Γ′ A′ Γ A} {c : Ctx R Γ′ A′} {s} {c′ : Ctx R Γ A} {l p₀ s₀ κ k′ sh t} p
          → search top (plug c s) ≡ just (found (Γ , A , c′ , cutS l (attAt p₀) s₀) attM κ) → run c′ (cutS l (attAt p₀) s₀) attM p ≡ moved k′ sh t
          → Sim ⟨ c , s , absorbed , p ⟩ sh k′

  -- A CONNECT'S OWN MARK RUN: its source subscribed, attached or torn
  -- down; nothing owed changes.
  abs-con : ∀ {R Γ′ A′ Γ A X} {c : Ctx R Γ′ A′} {s} {c′ : Ctx R Γ A} {k o} {b : St (X ∷ Γ) A} {m κ k′ sh t} p
          → search top (plug c s) ≡ just (found (Γ , A , c′ , connS k o b) m κ) → run c′ (connS k o b) m p ≡ moved k′ sh t
          → Sim ⟨ c , s , absorbed , p ⟩ sh k′

  -- A COLD'S TURN: its tape played one step, a value or its end rising,
  -- a stall or a frame's close moving nothing owed.
  abs-leaf : ∀ {R Γ′ A′ Γ A} {c : Ctx R Γ′ A′} {s} {c′ : Ctx R Γ A} {b} {l : Tape A} {κ t k′} p
           → search top (plug c s) ≡ just (found (Γ , A , c′ , coldS b l) leafM κ) → Driver.took R (run c′ (coldS b l) leafM p) ≡ Driver.silent t k′
           → Sim ⟨ c , s , absorbed , p ⟩ [] k′

  -- A JOINER'S NEXT RISES.
  abs-join : ∀ {R Γ′ A′ Γ A} {c : Ctx R Γ′ A′} {s} {c′ : Ctx R Γ A} {j g} {x : A ∈ Γ} {ib κ k′ sh t} p
           → search top (plug c s) ≡ just (found (Γ , A , c′ , joinS j g x ib) joinM κ) → run c′ (joinS j g x ib) joinM p ≡ moved k′ sh t
           → Sim ⟨ c , s , absorbed , p ⟩ sh k′

------------------------------------------------------------------------
-- Within what is grown, every step moves or finds nothing to do

Mv : ∀ {R} → Stepped R → Set
Mv (moved _ _ _) = ⊤
Mv quiet         = ⊤
Mv _             = ⊥

admit-mv : ∀ {R Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q o ls a p → Mv (admit c op f d n q o ls a p)
admit-mv c (mergeᶠ nothing)  f d n q o ls a p = tt
admit-mv c (mergeᶠ (just m)) f d n q o ls a p = tt
admit-mv c switchᶠ           f d n q o ls a p with killAll ls
... | _ = tt
admit-mv c exhaustᶠ          f d n q o ls a p with n ≡ᵇ 0
... | true  = tt
... | false = tt

rise-mv : ∀ {R Γ A} (c : Ctx R Γ A) s e p → Mv (rise c s e p)
rise-mv top                       s e      p = tt
rise-mv (inMap f c)               s e      p = tt
rise-mv (inScan f z c)            s (nx a) p = tt
rise-mv (inScan f z c)            s cp     p = tt
rise-mv (inCut l a c)             s e      p = tt
rise-mv (inLn b c)                s e      p = tt
rise-mv (inTake i q free c)       s (nx a) p with q a | i
... | true  | _     = tt
... | false | true  = tt
... | false | false = tt
rise-mv (inTake i q free c)       s cp     p = tt
rise-mv (inTake i q (cpAt r) c)   s e      p = tt
rise-mv (inTake i q (cutAt r) c)  s e      p = tt
rise-mv (inTake i q (overAt r) c) s e      p = tt
rise-mv (inOuter op f d n q ls c) o (nx a) p = admit-mv c op f d n q o ls a p
rise-mv (inOuter op f d n q ls c) o cp     p = tt
rise-mv (inLanes op f d n q o pre post c) s (nx b) p = tt
rise-mv (inLanes op f d n q o pre post c) s cp     p = tt
rise-mv (inSrc k b c)             s (nx a) p = tt
rise-mv (inSrc k b c)             s cp     p = tt
rise-mv (inBody k o c)            s (nx b) p = tt
rise-mv (inBody k o c)            s cp     p = tt

run-of-mv : ∀ {R Γ A} (c : Ctx R Γ A) i q (xs : List A) p → Mv (run c (ofS i q xs) ofM p)
run-of-mv c i q xs p with closed c | xs
... | true  | _     = tt
... | false | []    = tt
... | false | _ ∷ _ = tt

run-att-mv : ∀ {R Γ A} (c : Ctx R Γ A) l q (s : St Γ A) p → Mv (run c (cutS l (attAt q) s) attM p)
run-att-mv c l q s p with unsubIf (not l) s
... | _ = tt

run-con-mv : ∀ {R Γ A X} (c : Ctx R Γ A) k (o : St Γ X) b m p → m ≡ bodyM ⊎ (m ≡ srcAttM ⊎ m ≡ owedM) → Mv (run c (connS k o b) m p)
run-con-mv c k o b .bodyM p (Data.Sum.inj₁ refl) with CS.bodyAt k
... | just _  = tt
... | nothing = tt
run-con-mv c k o b .srcAttM p (Data.Sum.inj₂ (Data.Sum.inj₁ refl)) with CS.attSrc k | unsubIf (not (CS.srcLive k)) o
... | just _  | _ = tt
... | nothing | _ = tt
run-con-mv c k o b .owedM p (Data.Sum.inj₂ (Data.Sum.inj₂ refl)) with CS.owedAt k | unsubIf (CS.srcAtt k) o
... | just _  | _ = tt
... | nothing | _ = tt

run-join-mv : ∀ {R Γ A} (c : Ctx R Γ A) j g (x : A ∈ Γ) ib p → Mv (run c (joinS j g x ib) joinM p)
run-join-mv c j g x []              p = tt
run-join-mv c j g x ((q , nx a) ∷ ib) p = tt
run-join-mv c j g x ((q , cp) ∷ ib)   p = tt

-- The driver's steps read back as the engine's.
module _ {R : Set} where
  open Driver R using (took; value; complete) renaming (silent to τ)

  τ-moved : (x : Stepped R) → Mv x → ∀ {t k′} → took x ≡ τ t k′ → Σ Torn λ tr → x ≡ moved k′ [] tr
  τ-moved (moved k [] tr) _ refl = tr , refl
  τ-moved (moved k ((_ , nx _) ∷ _) tr) _ ()
  τ-moved (moved k ((_ , cp) ∷ _) tr)   _ ()
  τ-moved quiet _ ()

  val-moved : (x : Stepped R) → Mv x → ∀ {t p a k′} → took x ≡ value t p a k′ → Σ (Shownᴹ R) λ rest → Σ Torn λ tr → x ≡ moved k′ ((p , nx a) ∷ rest) tr
  val-moved (moved k [] tr) _ ()
  val-moved (moved k ((_ , nx _) ∷ rest) tr) _ refl = rest , tr , refl
  val-moved (moved k ((_ , cp) ∷ _) tr)      _ ()
  val-moved quiet _ ()

  fin-moved : (x : Stepped R) → Mv x → ∀ {p} → took x ≡ complete p → Σ (Conf R) λ k′ → Σ (Shownᴹ R) λ rest → Σ Torn λ tr → x ≡ moved k′ ((p , cp) ∷ rest) tr
  fin-moved (moved k [] tr) _ ()
  fin-moved (moved k ((_ , nx _) ∷ _) tr)    _ ()
  fin-moved (moved k ((_ , cp) ∷ rest) tr)   _ refl = k , rest , tr , refl
  fin-moved quiet _ ()

-- A driver step that shows nothing: a cold's subscription or turn.
module _ {R : Set} where
  open Driver R using (Step; played; value; complete; drained) renaming (silent to τ)

  Hush : Step → Set
  Hush (τ _ _) = ⊤
  Hush drained = ⊤
  Hush _       = ⊥

  played-hush : ∀ pk → Hush (played pk)
  played-hush gone                                         = tt
  played-hush (leaf b (ending e) cl dv st)                 = tt
  played-hush (leaf false (play τ′ u i t fr) cl dv st)     = tt
  played-hush (leaf false over cl dv st)                   = tt
  played-hush (leaf true (play τ′ u i t fr) true dv st)    = tt
  played-hush (leaf true over true dv st)                  = tt
  played-hush (leaf true (play τ′ u i t (emit a k)) false dv st) = tt
  played-hush (leaf true (play τ′ u i t (stall k)) false dv st)  = tt
  played-hush (leaf true (play τ′ u i t (close k)) false dv st)  = tt
  played-hush (leaf true over false dv st)                 = tt

  hush-val : ∀ {x t p a k′} → Hush x → x ≡ value t p a k′ → ⊥
  hush-val h refl = h

  hush-fin : ∀ {x p} → Hush x → x ≡ complete p → ⊥
  hush-fin h refl = h

------------------------------------------------------------------------
-- The run

-- Whatever a run from `k` shows, a reader of its rows is shown.
Runs : ∀ {R} → Conf R → Set₁
Runs k = ∀ {rs} → Steps k rs → Shows* (RT k) (conv rs)

-- SUBSCRIBING TO A FORMER NOT YET GROWN: the run from there, its own leaf.
-- Each owes what growing it would: its node's place in `adequacy.Bound.G`,
-- its rows and what it owes, and the step arms of the nodes it builds.
postulate
  beyond-take    : ∀ {R Γ A} (c : Ctx R Γ A) b q (s : Obs Timeline Γ A) q′ p
                 → Inv ⟨ c , pend (takeWhile b q s) q′ , subscribing , p ⟩ → Runs ⟨ c , pend (takeWhile b q s) q′ , subscribing , p ⟩
  beyond-bounded : ∀ {R Γ A B} (c : Ctx R Γ B) m (f : A → Obs Timeline Γ B) s q′ p
                 → Inv ⟨ c , pend (flatMap (mergeᶠ (just m)) f s) q′ , subscribing , p ⟩ → Runs ⟨ c , pend (flatMap (mergeᶠ (just m)) f s) q′ , subscribing , p ⟩
  beyond-switch  : ∀ {R Γ A B} (c : Ctx R Γ B) (f : A → Obs Timeline Γ B) s q′ p
                 → Inv ⟨ c , pend (flatMap switchᶠ f s) q′ , subscribing , p ⟩ → Runs ⟨ c , pend (flatMap switchᶠ f s) q′ , subscribing , p ⟩
  beyond-exhaust : ∀ {R Γ A B} (c : Ctx R Γ B) (f : A → Obs Timeline Γ B) s q′ p
                 → Inv ⟨ c , pend (flatMap exhaustᶠ f s) q′ , subscribing , p ⟩ → Runs ⟨ c , pend (flatMap exhaustᶠ f s) q′ , subscribing , p ⟩

join-mv : ∀ {R Γ A} (c : Ctx R Γ A) (x : A ∈ Γ) q {p} → Mv (stepᴹ ⟨ c , pend (connected x) q , subscribing , p ⟩)
join-mv c x q with closedUp c x
... | true  = tt
... | false = tt

join-sim : ∀ {R Γ A} {k′ : Conf R} {sh t} (c : Ctx R Γ A) (x : A ∈ Γ) q p
         → stepᴹ ⟨ c , pend (connected x) q , subscribing , p ⟩ ≡ moved k′ sh t → Sim ⟨ c , pend (connected x) q , subscribing , p ⟩ sh k′
join-sim c x q p eq with closedUp c x in cu
join-sim c x q p refl | true  = sub-joined c x q p cu
join-sim c x q p refl | false = sub-join c x q p cu

-- Where a step goes: on, linked a step at a time, engine or driver, or
-- into a former's leaf.
data Reach {R} (k : Conf R) : Set₁ where
  within : Mv (stepᴹ k) → (∀ {k′ sh t} → stepᴹ k ≡ moved k′ sh t → Sim k sh k′) → Reach k
  driven : Hush (Driver.step R k) → (∀ {t k′} → Driver.step R k ≡ Driver.silent t k′ → Sim k [] k′) → Reach k
  beyond : Runs k → Reach k

-- A step linked, read off the step itself, so a search's outcome can be
-- abstracted in it.
data Link {R} (k : Conf R) : Stepped R → Set₁ where
  mvL   : ∀ {x} → Mv x → (∀ {k′ sh t} → x ≡ moved k′ sh t → Sim k sh k′) → Link k x
  hushL : ∀ {x} → Hush (Driver.took R x) → (∀ {t k′} → Driver.took R x ≡ Driver.silent t k′ → Sim k [] k′) → Link k x

linked : ∀ {R} {k : Conf R} → Link k (stepᴹ k) → Reach k
linked (mvL mv sim)  = within mv sim
linked (hushL h sim) = driven h sim

-- A mark run, by what the search found.
abs-link : ∀ {R Γ A} (c : Ctx R Γ A) s p → Inv ⟨ c , s , absorbed , p ⟩ → Link ⟨ c , s , absorbed , p ⟩ (stepᴹ ⟨ c , s , absorbed , p ⟩)
abs-link c s p i with search top (plug c s) in fd
... | nothing = mvL tt λ ()
... | just (found (_ , _ , c′ , s′) m κ) with found-mark c s (good i) fd
...   | ofK j q xs     = mvL (run-of-mv c′ j q xs p) (λ eq → abs-of p fd eq)
...   | attK l q s₀    = mvL (run-att-mv c′ l q s₀ p) (λ eq → abs-att p fd eq)
...   | conK k o b m w = mvL (run-con-mv c′ k o b m p w) (λ eq → abs-con p fd eq)
...   | joinK j g x ib = mvL (run-join-mv c′ j g x ib p) (λ eq → abs-join p fd eq)
...   | leafK b l      = hushL (played-hush (leaf b l (closed c′) (λ e l′ b′ p′ → ⟨ c′ , coldS b′ l′ , (if not (closed c′) then rising e else absorbed) , p′ ⟩) (λ l′ → ⟨ c′ , coldS b l′ , absorbed , p ⟩))) (λ eq → abs-leaf p fd eq)

reach-pend : ∀ {R Γ A} (c : Ctx R Γ A) (o : Obs Timeline Γ A) q p → Inv ⟨ c , pend o q , subscribing , p ⟩ → Reach ⟨ c , pend o q , subscribing , p ⟩
reach-pend c empty                           q p i = within tt λ { refl → sub-empty c q p }
reach-pend c (of xs)                         q p i = within tt λ { refl → sub-of c xs q p }
reach-pend c (map f s)                       q p i = within tt λ { refl → sub-map c f s q p }
reach-pend c (flatMap (mergeᶠ nothing) f s)  q p i = within tt λ { refl → sub-merge c f s q p }
reach-pend c (connected x)                   q p i = within (join-mv c x q {p}) (join-sim c x q p)
reach-pend c (cold x)                        q p i = driven tt λ { refl → sub-cold c x q p }
reach-pend c (scan f z s)                    q p i = within tt λ { refl → sub-scan c f z s q p }
reach-pend c (takeWhile b w s)               q p i = beyond (beyond-take c b w s q p i)
reach-pend c (flatMap (mergeᶠ (just m)) f s) q p i = beyond (beyond-bounded c m f s q p i)
reach-pend c (flatMap switchᶠ f s)           q p i = beyond (beyond-switch c f s q p i)
reach-pend c (flatMap exhaustᶠ f s)          q p i = beyond (beyond-exhaust c f s q p i)
reach-pend c (connect s b)                   q p i = within tt λ { refl → sub-connect c s b q p }
reach-pend c (defer l)                       q p i = within tt λ { refl → sub-defer c l q p }

reach : ∀ {R} (k : Conf R) → Inv k → Reach k
reach ⟨ c , s , rising e , p ⟩                        i = within (rise-mv c s e p) (rise-sim c s e p)
reach ⟨ c , pend o q , subscribing , p ⟩              i = reach-pend c o q p i
reach ⟨ c , coldS b l , subscribing , p ⟩             i = within tt (sub-sim c (coldS b l) p tt)
reach ⟨ c , ofS j q xs , subscribing , p ⟩            i = within tt (sub-sim c (ofS j q xs) p tt)
reach ⟨ c , doneS , subscribing , p ⟩                 i = within tt (sub-sim c doneS p tt)
reach ⟨ c , mapS f s , subscribing , p ⟩              i = within tt (sub-sim c (mapS f s) p tt)
reach ⟨ c , scanS f z s , subscribing , p ⟩           i = within tt (sub-sim c (scanS f z s) p tt)
reach ⟨ c , cutS l a s , subscribing , p ⟩            i = within tt (sub-sim c (cutS l a s) p tt)
reach ⟨ c , lnS b s , subscribing , p ⟩               i = within tt (sub-sim c (lnS b s) p tt)
reach ⟨ c , takeS j q w s , subscribing , p ⟩         i = within tt (sub-sim c (takeS j q w s) p tt)
reach ⟨ c , flatS op f d n q o ls , subscribing , p ⟩ i = within tt (sub-sim c (flatS op f d n q o ls) p tt)
reach ⟨ c , connS k o b , subscribing , p ⟩           i = within tt (sub-sim c (connS k o b) p tt)
reach ⟨ c , joinS j g x ib , subscribing , p ⟩        i = within tt (sub-sim c (joinS j g x ib) p tt)
reach ⟨ c , s , absorbed , p ⟩                        i = linked (abs-link c s p i)

sound-from : ∀ {R} {k : Conf R} → Inv k → Runs k
sound-from {k = k} i st with reach k i
... | beyond b      = b st
... | driven h sim  = go st
  where
    go : ∀ {rs} → Steps k rs → Shows* (RT k) (conv rs)
    go [] = []
    go (tau e st′) with sim e i
    ... | i′ , silent q = Shows*-≃ (≃-sym q) (sound-from i′ st′)
    go (val e _) = ⊥-elim (hush-val h e)
    go (fin e)   = ⊥-elim (hush-fin h e)
... | within mv sim = go st
  where
    go : ∀ {rs} → Steps k rs → Shows* (RT k) (conv rs)
    go [] = []
    go (tau e st′) with τ-moved (stepᴹ k) mv e
    ... | _ , eq with sim eq i
    ...   | i′ , silent q = Shows*-≃ (≃-sym q) (sound-from i′ st′)
    go (val e st′) with val-moved (stepᴹ k) mv e
    ... | _ , _ , eq with sim eq i
    ...   | i′ , shown v lt q = (v , lt) ∷ Shows*-≃ (≃-sym q) (sound-from i′ st′)
    go (fin e) with fin-moved (stepᴹ k) mv e
    ... | _ , _ , _ , eq with sim eq i
    ...   | _ , shown v lt _ = (v , lt) ∷ []

postulate
  -- THE SKIPS BETWEEN: a program's least visible rows, shown in
  -- turn, are the shown rows of a reader's run, the skips before each met
  -- on the way.  Finitely many rows lie before each (`adequacy.Enter`),
  -- and none visible past the end; the run lists them in position order.
  --
  -- DEAD ROUTE: reading the rows off the oracle's listing
  --   (`quickcheck.Tabled.Exact.tabled-exact`): it is exact only uncut, and
  --   its horizon is a fixed time, so a cold source ticking past it, or an
  --   infinite one, cuts the listing and it claims nothing.  The horizon a
  --   run needs is the position of its last shown row, which the listing
  --   does not take.
  met-of-shown : ∀ {R} {o : PureObs [] R} {vs} → Shows* (enter (⟦ o ⟧ []ᴬ) root) vs → Meets (enter (⟦ o ⟧ []ᴬ) root) vs

-- THE SOUND HALF: what the engine shows, a subscriber to the program's
-- rows is shown.
sound : ∀ {R} {o : PureObs [] R} {rs} → Steps (load o) rs → Meets (enter (⟦ o ⟧ []ᴬ) root) (conv rs)
sound {o = o} st = met-of-shown {o = o} (sound-from (inv tt₁ (tt , tt , (tt , λ ()) , tt)) st)
