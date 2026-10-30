{-# OPTIONS --guardedness #-}

-- THE DIRECT LINK: the engine run against the emission set's rows, with
-- no stepper and no tower between them.  A step keeps the visible rows or
-- shows the least and drops it, by mode: a subscription entered as the
-- rows of what it begins, a rise read up one frame, a mark run where the
-- search's bound says it leads.
module adequacy.Sim where

open import Data.Bool using (Bool; true; false; if_then_else_; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (_≡ᵇ_; _<ᵇ_; pred)
open import Data.List using (List; []; _∷_; [_]; null; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Data.List.Relation.Unary.Any using () renaming (here to hd)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (just; nothing) renaming (map to mapᴹ)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to tt₁)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.List using (_ʳ++_)

open import Tree using (Obs; Later; mergeᶠ; switchᶠ; exhaustᶠ; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.Events using (Timeline; root; Pos; ix; timelineAt; emit; stall; close)
open import denotation.EmissionSet using (EmissionSet; Ev; out; end; MapT; map-out; map-skip; map-pin; map-end; module Scan;
  module TakeWhile; module Connecting; _≼_; _≺_; enter; ⟦_⟧; Proper; Den; Silent; Dep)
open import denotation.Laws.Modulus using (≺-irrefl; ≺-absurd; ≼-or-≻; entered-few)
open import denotation.Laws.Worlds using (GoodEnv; Lawful; Hots; InvAt)
open import denotation.Laws using (inv-⟦⟧; good-cons)
open import operation.PureObservable using (PureObs; module Machine; module Driver; Tape; play; ending; over; opening)
open Machine using (St; Ctx; Conf; ⟨_,_,_,_⟩; subscribing; absorbed; rising; load; moved; plug; search; seek; found; Mark; ofM; attM;
                    rise; run; start; dequeue; settle; alive; ended; mapEv; nx; cp; attAt; attached; Torn;
                    Stepped; quiet; begin; admit; closed; killAll; unsubIf; free; cpAt; cutAt; overAt; cut; cpM; cutM; CS; cs; feed; closedUp; _⊕_;
                    bodyM; srcAttM; owedM; joinM; leafM; Poke; gone; leaf; starting; turn;
                    pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
                    top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody)
                    renaming (Ev to Evᴹ; Shown to Shownᴹ; step to stepᴹ)
open import adequacy.Rows using (env; rows; pendRows; Closed; RT; toEv; Vis; Past; Lowest; Beyond; into; back; narrow; Plus; old; new; _≃_; _⇄_; silent; shown;
  Steps; Shows*; Shows*-≃; ≃-sym; conv; []; _∷_; tau; val; fin)
open import adequacy.Bound using (Good; G; Rooted; mergeG₀; OK)
open import adequacy.Search using (seek-ok)
open import adequacy.Up using (up-≃; ≃-refl; vis-≃)
open import adequacy.Skip using (After; after-conn)
open import adequacy.Inv using (Inv; inv; good; Sim; Ends; open-alive)
open import adequacy.LaneCp using (rise-lane-cp)
open import adequacy.AbsOf using (abs-of; up-plug)
open import denotation.Read using (Meets; Run; Visible; loud; []; _∷_)
open import adequacy.Swap using (Swap; good-swap)
open import adequacy.Enter using (enter-map; enter-scan; enter-merge; flat-∅; enter-bounded; enter-switch; enter-exhaust; bounded-∅; switch-∅; exhaust-∅)

postulate
  -- A GOOD TREE'S CONNECT SOURCE READS LAWFULLY: its rows reachable, one
  -- event at a position, none below another, as the binder its body reads.
  src-lawful : ∀ {R Γ X B} (k : CS) (o : St Γ X) (b : St (X ∷ Γ) B) (c : Ctx R Γ B) → Good []ᴬ (plug c (connS k o b))
             → Lawful (Proper (λ q e → rows (env c) o q e ⊎ Closed k q e))

-- A good tree's environment keeps the invariant: each binder a
-- connect's source.
env-good : ∀ {R Γ A} (c : Ctx R Γ A) {s} → Good []ᴬ (plug c s) → GoodEnv (env c)
env-good top                                         _ ()
env-good (inMap f c)                                 g = env-good c g
env-good (inScan f z c)                              g = env-good c g
env-good (inCut l a c)                               g = env-good c g
env-good (inLn b c)                                  g = env-good c g
env-good (inOuter op f d n q ls c)                   g = env-good c g
env-good (inLanes op f d n q o pre post c)           g = env-good c g
env-good (inTake i q w c)                            g = env-good c g
env-good (inSrc k b c)                               g = env-good c g
env-good (inBody k o c) {s}                          g = good-cons (src-lawful k o s c g) (env-good c g)

------------------------------------------------------------------------
-- Subscribing

postulate
  sub-empty : ∀ {R Γ A} (c : Ctx R Γ A) q p → Sim ⟨ c , pend empty q , subscribing , p ⟩ [] ⟨ c , ofS 0 q [] , absorbed , q ⟩
  sub-of    : ∀ {R Γ A} (c : Ctx R Γ A) xs q p → Sim ⟨ c , pend (of xs) q , subscribing , p ⟩ [] ⟨ c , ofS 0 q xs , absorbed , q ⟩

-- A map entered: its source pending under it.
sub-map : ∀ {R Γ A B} (c : Ctx R Γ B) (f : A → B) s q p → Sim ⟨ c , pend (map f s) q , subscribing , p ⟩ [] ⟨ inMap f c , pend s q , subscribing , q ⟩
sub-map c f s q p (inv g (uc , ok)) = inv (good-swap c sw g) (uc , ok) , silent (vis-≃ (up-≃ c (enter-map (env c) f s q)))
  where
    sw : Swap (env c) doneS (mapS f doneS)
    sw = record { same = (λ ()) ⇄ (λ { (map-out ()) ; (map-skip ()) ; (map-pin ()) ; (map-end ()) }) ; live≡ = refl ; node = λ _ x → x ; lane = λ _ () ; body = λ _ _ () ; held = λ () ; told = λ _ _ → tt }

-- A scan entered: its source pending under it.
sub-scan : ∀ {R Γ A B} (c : Ctx R Γ B) (f : B → A → B) z s q p → Sim ⟨ c , pend (scan f z s) q , subscribing , p ⟩ [] ⟨ inScan f z c , pend s q , subscribing , q ⟩
sub-scan c f z s q p (inv g (uc , ok)) = inv (good-swap c sw g) (uc , ok) , silent (vis-≃ (up-≃ c (enter-scan (env c) f z s q)))
  where
    sw : Swap (env c) doneS (scanS f z doneS)
    sw = record { same = (λ ()) ⇄ (λ { (Scan.sval (Scan.acc₀ () _)) ; (Scan.sval (Scan.acc _ () _ _)) ; (Scan.sstep ()) ; (Scan.spin ()) ; (Scan.send ()) }) ; live≡ = refl ; node = λ _ x → x ; lane = λ _ () ; body = λ _ _ () ; held = λ () ; told = λ _ _ → tt }

-- A take entered: its source pending under it, attached at `p`, unfailed.
sub-take : ∀ {R Γ A} (c : Ctx R Γ A) i (w : A → Bool) s q p
         → Sim ⟨ c , pend (takeWhile i w s) q , subscribing , p ⟩ [] ⟨ inCut true (attAt q) (inTake i w free c) , pend s q , subscribing , q ⟩
sub-take c i w s q p (inv g (uc , ok)) = inv (good-swap c sw g) (uc , ok) , silent ((λ x → x) ⇄ (λ x → x))
  where
    sw : Swap (env c) doneS (takeS i w free (cutS true (attAt q) doneS))
    sw = record { same = (λ ()) ⇄ (λ { (TakeWhile.pass () _ _ , _) ; (TakeWhile.fail () _ _ _ , _) ; (TakeWhile.stop () _ _ , _)
                                      ; (TakeWhile.step () _ , _) ; (TakeWhile.tend () _ , _) ; (TakeWhile.left () _ _ , _) })
                ; live≡ = refl ; node = λ _ x → x ; lane = λ _ () ; body = λ _ _ () ; held = λ () ; told = λ _ _ → tt }

-- A merge entered: its outer pending under it, attached at `p`, nothing begun.
sub-merge : ∀ {R Γ A B} (c : Ctx R Γ B) f (s : Obs Timeline Γ A) q p
          → Sim ⟨ c , pend (flatMap (mergeᶠ nothing) f s) q , subscribing , p ⟩ [] ⟨ inCut true (attAt q) (inOuter (mergeᶠ nothing) f false 0 [] [] c) , pend s q , subscribing , q ⟩
sub-merge {A = A} {B} c f s q p (inv g (uc , ok)) = inv (good-swap c sw g) (uc , ok) , silent (vis-≃ (up-≃ c (enter-merge (env c) f s q)))
  where
    -- The outer about to enter at `p`: inside its own entry, nothing begun.
    rt : Rooted (rows (env c) (cutS true (attAt q) doneS)) []
    rt = record { H = Hots (env c) ; X = pendRows (env c) s q ; p₀ = q ; inv = inv-⟦⟧ s (env c) (env-good c g) q ok ; sub = λ () ; qs = [] ; roots = tt }
    node′ : ∀ v → G (env c) v (doneS {A = B}) → G (env c) v (flatS (mergeᶠ nothing) f false 0 [] (cutS true (attAt q) (doneS {A = A})) [])
    node′ true  _ = record { outer = tt₁ ; lanesG = tt₁ ; fresh = refl ; count = refl ; spent = λ () ; rooted = rt }
    node′ false _ = mergeG₀ tt₁ tt₁ refl
    sw : Swap (env c) doneS (flatS (mergeᶠ nothing) f false 0 [] (cutS true (attAt q) doneS) [])
    sw = record { same = ≃-sym (flat-∅ _ false 0) ; live≡ = refl ; node = node′ ; lane = λ _ () ; body = λ _ _ () ; held = λ () ; told = λ _ _ → tt , tt }

-- A BOUNDED MERGE ENTERED: its outer pending under it, nothing begun or queued.
sub-bounded : ∀ {R Γ A B} (c : Ctx R Γ B) m (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) q p
          → Sim ⟨ c , pend (flatMap (mergeᶠ (just m)) f s) q , subscribing , p ⟩ [] ⟨ inCut true (attAt q) (inOuter (mergeᶠ (just m)) f false 0 [] [] c) , pend s q , subscribing , q ⟩
sub-bounded {A = A} {B} c m f s q p (inv g (uc , ok)) = inv (good-swap c sw g) (uc , ok) , silent (vis-≃ (up-≃ c (enter-bounded (env c) m f s q)))
  where
    rt : Rooted (rows (env c) (cutS true (attAt q) doneS)) []
    rt = record { H = Hots (env c) ; X = pendRows (env c) s q ; p₀ = q ; inv = inv-⟦⟧ s (env c) (env-good c g) q ok ; sub = λ () ; qs = [] ; roots = tt }
    node′ : ∀ v → G (env c) v (doneS {A = B}) → G (env c) v (flatS (mergeᶠ (just m)) f false 0 [] (cutS true (attAt q) (doneS {A = A})) [])
    node′ true  _ = (record { outer = tt₁ ; lanesG = tt₁ ; fresh = refl ; count = refl ; spent = λ () ; rooted = rt } , inj₁ refl)
    node′ false _ = (mergeG₀ tt₁ tt₁ refl , tt)
    sw : Swap (env c) doneS (flatS (mergeᶠ (just m)) f false 0 [] (cutS true (attAt q) doneS) [])
    sw = record { same = ≃-sym (bounded-∅ m _ false 0) ; live≡ = refl ; node = node′ ; lane = λ _ () ; body = λ _ _ () ; held = λ () ; told = λ _ _ → tt , tt }

-- A SWITCH ENTERED: its outer pending under it, nothing begun.
sub-switch : ∀ {R Γ A B} (c : Ctx R Γ B) (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) q p
          → Sim ⟨ c , pend (flatMap switchᶠ f s) q , subscribing , p ⟩ [] ⟨ inCut true (attAt q) (inOuter switchᶠ f false 0 [] [] c) , pend s q , subscribing , q ⟩
sub-switch {A = A} {B} c f s q p (inv g (uc , ok)) = inv (good-swap c sw g) (uc , ok) , silent (vis-≃ (up-≃ c (enter-switch (env c) f s q)))
  where
    rt : Rooted (rows (env c) (cutS true (attAt q) doneS)) []
    rt = record { H = Hots (env c) ; X = pendRows (env c) s q ; p₀ = q ; inv = inv-⟦⟧ s (env c) (env-good c g) q ok ; sub = λ () ; qs = [] ; roots = tt }
    node′ : ∀ v → G (env c) v (doneS {A = B}) → G (env c) v (flatS switchᶠ f false 0 [] (cutS true (attAt q) (doneS {A = A})) [])
    node′ true  _ = record { outer = tt₁ ; lanesG = tt₁ ; fresh = refl ; count = refl ; spent = λ () ; rooted = rt }
    node′ false _ = mergeG₀ tt₁ tt₁ refl
    sw : Swap (env c) doneS (flatS switchᶠ f false 0 [] (cutS true (attAt q) doneS) [])
    sw = record { same = ≃-sym (switch-∅ _ false 0) ; live≡ = refl ; node = node′ ; lane = λ _ () ; body = λ _ _ () ; held = λ () ; told = λ _ _ → tt , tt }

-- AN EXHAUST ENTERED: its outer pending under it, nothing begun.
sub-exhaust : ∀ {R Γ A B} (c : Ctx R Γ B) (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) q p
          → Sim ⟨ c , pend (flatMap exhaustᶠ f s) q , subscribing , p ⟩ [] ⟨ inCut true (attAt q) (inOuter exhaustᶠ f false 0 [] [] c) , pend s q , subscribing , q ⟩
sub-exhaust {A = A} {B} c f s q p (inv g (uc , ok)) = inv (good-swap c sw g) (uc , ok) , silent (vis-≃ (up-≃ c (enter-exhaust (env c) f s q)))
  where
    rt : Rooted (rows (env c) (cutS true (attAt q) doneS)) []
    rt = record { H = Hots (env c) ; X = pendRows (env c) s q ; p₀ = q ; inv = inv-⟦⟧ s (env c) (env-good c g) q ok ; sub = λ () ; qs = [] ; roots = tt }
    node′ : ∀ v → G (env c) v (doneS {A = B}) → G (env c) v (flatS exhaustᶠ f false 0 [] (cutS true (attAt q) (doneS {A = A})) [])
    node′ true  _ = record { outer = tt₁ ; lanesG = tt₁ ; fresh = refl ; count = refl ; spent = λ () ; rooted = rt }
    node′ false _ = mergeG₀ tt₁ tt₁ refl
    sw : Swap (env c) doneS (flatS exhaustᶠ f false 0 [] (cutS true (attAt q) doneS) [])
    sw = record { same = ≃-sym (exhaust-∅ _ false 0) ; live≡ = refl ; node = node′ ; lane = λ _ () ; body = λ _ _ () ; held = λ () ; told = λ _ _ → tt , tt }

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
rise-top s e p (inv g (_ , _ , op , _)) | false = ⊥-elim (open-alive s op al)
rise-top s e p (inv g (_ , _ , _ , ld , _)) | true = inv g tt , shown (new , vis e) least (to′ ⇄ from′)
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


-- A BODY VALUE PASSES THROUGH ITS CONNECT: a value adds no end, so the
-- body's liveness is unchanged.
conn-plus-nx : ∀ {A B} r (σ : EmissionSet A) (β : EmissionSet B) p (v : B)
             → Connecting.ConnT r σ (Plus β p (out v)) ≃ Plus (Connecting.ConnT r σ β) p (out v)
conn-plus-nx r σ β p v = to′ ⇄ from′
  where
    live : ∀ {q} → (∀ {c} → Plus β p (out v) c end → q ≺ c) → ∀ {c} → β c end → q ≺ c
    live al x = al (old x)

    unlive : ∀ {q} → (∀ {c} → β c end → q ≺ c) → ∀ {c} → Plus β p (out v) c end → q ≺ c
    unlive al (old x) = al x

    to′ : ∀ {q e} → Connecting.ConnT r σ (Plus β p (out v)) q e → Plus (Connecting.ConnT r σ β) p (out v) q e
    to′ (Connecting.body (old x))     = old (Connecting.body x)
    to′ (Connecting.body new)         = new
    to′ (Connecting.burst x i)        = old (Connecting.burst x i)
    to′ (Connecting.echo {k} x al u ni) = old (Connecting.echo x (live {k} al) u ni)
    to′ (Connecting.kept {_} {p′} x al ni i) = old (Connecting.kept x (live {p′} al) ni i)

    from′ : ∀ {q e} → Plus (Connecting.ConnT r σ β) p (out v) q e → Connecting.ConnT r σ (Plus β p (out v)) q e
    from′ (old (Connecting.body x))         = Connecting.body (old x)
    from′ (old (Connecting.burst x i))      = Connecting.burst x i
    from′ (old (Connecting.echo {k} x al u ni)) = Connecting.echo x (unlive {k} al) u ni
    from′ (old (Connecting.kept {_} {p′} x al ni i)) = Connecting.kept x (unlive {p′} al) ni i
    from′ new                               = Connecting.body new

rise-map : ∀ {R Γ A B} (f : A → B) (c : Ctx R Γ B) s e p → Sim ⟨ inMap f c , s , rising e , p ⟩ [] ⟨ c , mapS f s , rising (mapEv f e) , p ⟩
rise-map f c s e p i with alive s in al
rise-map f c s e p (inv g (_ , _ , op , _)) | false = ⊥-elim (open-alive s op al)
rise-map f c s e p (inv g (uc , lc , _ , af , en)) | true =
  inv g (uc , lc , tt , after-map f {p = p} af , ends-map f e en) , silent (vis-≃ (up-≃ c (map-plus f (rows (env c) s) p e)))

rise-cut : ∀ {R Γ A} l a (c : Ctx R Γ A) s e p → Sim ⟨ inCut l a c , s , rising e , p ⟩ [] ⟨ c , cutS l a s , (if l then rising e else absorbed) , p ⟩
rise-cut false a c s e p (inv g (() , _))
rise-cut true  a c s e p i with alive s in al
rise-cut true  a c s e p (inv g (_ , _ , op , _)) | false = ⊥-elim (open-alive s op al)
rise-cut true  a c s e p (inv g (uc , lc , _ , af , en)) | true = inv g (uc , lc , tt , af , en) , silent ≃-refl

rise-ln : ∀ {R Γ A} b (c : Ctx R Γ A) s e p → Sim ⟨ inLn b c , s , rising e , p ⟩ [] ⟨ c , lnS b s , rising e , p ⟩
rise-ln false c s e p (inv g (() , _))
rise-ln true  c s e p i with alive s in al
rise-ln true  c s e p (inv g (_ , _ , op , _)) | false = ⊥-elim (open-alive s op al)
rise-ln true  c s e p (inv g (uc , lc , _ , af , en)) | true = inv g (uc , lc , tt , af , en) , silent ≃-refl

-- A SCAN'S VALUE FOLDED: the source's least value leaves as the fold of
-- it, and the rest of the source's rows fold from there.
postulate
  rise-scan-nx : ∀ {R Γ A B} (f : B → A → B) z (c : Ctx R Γ B) s a p → Sim ⟨ inScan f z c , s , rising (nx a) , p ⟩ [] ⟨ c , scanS f (f z a) s , rising (nx (f z a)) , p ⟩
  rise-scan-cp : ∀ {R Γ A B} (f : B → A → B) z (c : Ctx R Γ B) s p → Sim ⟨ inScan f z c , s , rising cp , p ⟩ [] ⟨ c , scanS f z s , rising cp , p ⟩

-- A TAKE'S VALUE: kept while it passes, the source's rows past it taken
-- likewise; a failing value shown or not as the take is inclusive, its
-- completion owed after it; its source's end its own.  Once failed, the
-- take absorbs whatever still reaches it.
postulate
  rise-take-nx   : ∀ {R Γ A} i (w : A → Bool) (c : Ctx R Γ A) s a p → w a ≡ true
                 → Sim ⟨ inTake i w free c , s , rising (nx a) , p ⟩ [] ⟨ c , takeS i w free s , rising (nx a) , p ⟩
  rise-take-fail : ∀ {R Γ A} i (w : A → Bool) (c : Ctx R Γ A) s a p → w a ≡ false
                 → Sim ⟨ inTake i w free c , s , rising (nx a) , p ⟩ []
                       (if i then ⟨ c , takeS i w (cpAt p) s , rising (nx a) , p ⊕ [ ix 0 ] ⟩ else ⟨ c , takeS i w (cpAt p) s , absorbed , p ⟩)
  rise-take-cp   : ∀ {R Γ A} i (w : A → Bool) (c : Ctx R Γ A) s p
                 → Sim ⟨ inTake i w free c , s , rising cp , p ⟩ [] ⟨ c , takeS i w free s , rising cp , p ⟩
  rise-take-owed : ∀ {R Γ A} i (w : A → Bool) o (c : Ctx R Γ A) s e p → (o ≡ free → ⊥)
                 → Sim ⟨ inTake i w o c , s , rising e , p ⟩ [] ⟨ c , takeS i w o s , absorbed , p ⟩

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

  -- A BOUNDED MERGE'S OUTER VALUE BEGINS ITS LANE WITH ROOM, ELSE WAITS.
  rise-bounded-nx : ∀ {R Γ A B} m f d n q ls (c : Ctx R Γ B) (o : St Γ A) a p
                  → Sim ⟨ inOuter (mergeᶠ (just m)) f d n q ls c , o , rising (nx a) , p ⟩ []
                        (if n <ᵇ m then start c (mergeᶠ (just m)) f d n q o ls a p
                                   else ⟨ c , flatS (mergeᶠ (just m)) f d n (q ++ [ a ]) o ls , absorbed , p ⟩)
  -- A BOUNDED MERGE'S OUTER END, SHOWN ONLY WITH NO LANE RUNNING OR WAITING.
  rise-bounded-cp : ∀ {R Γ A B} m f d n q ls (c : Ctx R Γ B) (o : St Γ A) p
                 → Sim ⟨ inOuter (mergeᶠ (just m)) f d n q ls c , o , rising cp , p ⟩ [] ⟨ c , flatS (mergeᶠ (just m)) f true n q o ls , (if d then absorbed else settle true n (null q)) , p ⟩
  -- A BOUNDED MERGE'S LANE VALUE PASSES, UNLESS THE LANE IS OVER.
  rise-bounded-lane-nx : ∀ {R Γ A B} m f d n q (o : St Γ A) pre post (c : Ctx R Γ B) s b p
                      → Sim ⟨ inLanes (mergeᶠ (just m)) f d n q o pre post c , s , rising (nx b) , p ⟩ []
                            (if alive s then ⟨ c , flatS (mergeᶠ (just m)) f d n q o (pre ʳ++ s ∷ post) , rising (nx b) , p ⟩
                                        else ⟨ c , flatS (mergeᶠ (just m)) f d n q o (pre ʳ++ s ∷ post) , absorbed , p ⟩)
  -- A BOUNDED MERGE'S LANE END FREES ITS SLOT FOR THE FIRST WAITING VALUE.
  rise-bounded-lane-cp : ∀ {R Γ A B} m f d n q (o : St Γ A) pre post (c : Ctx R Γ B) s p
                      → Sim ⟨ inLanes (mergeᶠ (just m)) f d n q o pre post c , s , rising cp , p ⟩ []
                            (if alive s then dequeue c (mergeᶠ (just m)) f d (pred n) q o (pre ʳ++ ended s ∷ post) p
                                        else ⟨ c , flatS (mergeᶠ (just m)) f d n q o (pre ʳ++ s ∷ post) , absorbed , p ⟩)
  -- A SWITCH'S OUTER VALUE CUTS EVERY RUNNING LANE AND BEGINS ITS OWN.
  rise-switch-nx : ∀ {R Γ A B} f d n q ls (c : Ctx R Γ B) (o : St Γ A) a p ls′ (t : Torn) → killAll ls ≡ (ls′ , t)
                 → Sim ⟨ inOuter switchᶠ f d n q ls c , o , rising (nx a) , p ⟩ [] (start c switchᶠ f d 0 q o ls′ a p)
  -- A SWITCH'S OUTER END, SHOWN ONLY WITH NO LANE RUNNING.
  rise-switch-cp : ∀ {R Γ A B} f d n q ls (c : Ctx R Γ B) (o : St Γ A) p
                → Sim ⟨ inOuter switchᶠ f d n q ls c , o , rising cp , p ⟩ [] ⟨ c , flatS switchᶠ f true n q o ls , (if d then absorbed else settle true n (null q)) , p ⟩
  -- A SWITCH'S LANE VALUE PASSES, UNLESS THE LANE IS OVER.
  rise-switch-lane-nx : ∀ {R Γ A B} f d n q (o : St Γ A) pre post (c : Ctx R Γ B) s b p
                     → Sim ⟨ inLanes switchᶠ f d n q o pre post c , s , rising (nx b) , p ⟩ []
                           (if alive s then ⟨ c , flatS switchᶠ f d n q o (pre ʳ++ s ∷ post) , rising (nx b) , p ⟩
                                       else ⟨ c , flatS switchᶠ f d n q o (pre ʳ++ s ∷ post) , absorbed , p ⟩)
  -- A SWITCH'S LANE END.
  rise-switch-lane-cp : ∀ {R Γ A B} f d n q (o : St Γ A) pre post (c : Ctx R Γ B) s p
                     → Sim ⟨ inLanes switchᶠ f d n q o pre post c , s , rising cp , p ⟩ []
                           (if alive s then dequeue c switchᶠ f d (pred n) q o (pre ʳ++ ended s ∷ post) p
                                       else ⟨ c , flatS switchᶠ f d n q o (pre ʳ++ s ∷ post) , absorbed , p ⟩)
  -- AN EXHAUST'S OUTER VALUE BEGINS ITS LANE WITH NONE RUNNING.
  rise-exhaust-run : ∀ {R Γ A B} f d n q ls (c : Ctx R Γ B) (o : St Γ A) a p → (n ≡ᵇ 0) ≡ true
                   → Sim ⟨ inOuter exhaustᶠ f d n q ls c , o , rising (nx a) , p ⟩ [] (start c exhaustᶠ f d n q o ls a p)
  -- AN EXHAUST'S OUTER VALUE, A LANE RUNNING, IS DROPPED.
  rise-exhaust-drop : ∀ {R Γ A B} f d n q ls (c : Ctx R Γ B) (o : St Γ A) a p → (n ≡ᵇ 0) ≡ false
                    → Sim ⟨ inOuter exhaustᶠ f d n q ls c , o , rising (nx a) , p ⟩ [] ⟨ c , flatS exhaustᶠ f d n q o ls , absorbed , p ⟩
  -- AN EXHAUST'S OUTER END, SHOWN ONLY WITH NO LANE RUNNING.
  rise-exhaust-cp : ∀ {R Γ A B} f d n q ls (c : Ctx R Γ B) (o : St Γ A) p
                 → Sim ⟨ inOuter exhaustᶠ f d n q ls c , o , rising cp , p ⟩ [] ⟨ c , flatS exhaustᶠ f true n q o ls , (if d then absorbed else settle true n (null q)) , p ⟩
  -- AN EXHAUST'S LANE VALUE PASSES, UNLESS THE LANE IS OVER.
  rise-exhaust-lane-nx : ∀ {R Γ A B} f d n q (o : St Γ A) pre post (c : Ctx R Γ B) s b p
                      → Sim ⟨ inLanes exhaustᶠ f d n q o pre post c , s , rising (nx b) , p ⟩ []
                            (if alive s then ⟨ c , flatS exhaustᶠ f d n q o (pre ʳ++ s ∷ post) , rising (nx b) , p ⟩
                                        else ⟨ c , flatS exhaustᶠ f d n q o (pre ʳ++ s ∷ post) , absorbed , p ⟩)
  -- AN EXHAUST'S LANE END.
  rise-exhaust-lane-cp : ∀ {R Γ A B} f d n q (o : St Γ A) pre post (c : Ctx R Γ B) s p
                      → Sim ⟨ inLanes exhaustᶠ f d n q o pre post c , s , rising cp , p ⟩ []
                            (if alive s then dequeue c exhaustᶠ f d (pred n) q o (pre ʳ++ ended s ∷ post) p
                                        else ⟨ c , flatS exhaustᶠ f d n q o (pre ʳ++ s ∷ post) , absorbed , p ⟩)

  -- A SOURCE'S VALUE FEEDS ITS BODY.
  rise-src-nx : ∀ {R Γ X B} (k : CS) (b : St (X ∷ Γ) B) (c : Ctx R Γ B) s a p
              → Sim ⟨ inSrc k b c , s , rising (nx a) , p ⟩ [] ⟨ c , connS k s (feed (hd refl) p (nx a) b) , absorbed , p ⟩
  -- A SOURCE'S END FEEDS ITS BODY AND CLOSES ITS CONNECT.
  rise-src-cp : ∀ {R Γ X B} (k : CS) (b : St (X ∷ Γ) B) (c : Ctx R Γ B) s p
              → Sim ⟨ inSrc k b c , s , rising cp , p ⟩ [] ⟨ c , connS (record k { closed = true ; endAt = p }) s (feed (hd refl) p cp b) , absorbed , p ⟩
  -- A BODY'S END IS ITS CONNECT'S, ITS SOURCE OWED A TEARDOWN THERE.
  -- False against `Inv` as it stands: `connect(of(1,2), h => empty)` ends
  -- its body while subscribing it, its source's burst still owed, and
  -- those rows are `ConnT`'s silent `burst` pins past the end, so the
  -- target's `Ends cp` (`Empty`) fails while the source's holds.  Every
  -- row a connect owes past its body's end is silent, so the step keeps
  -- the visible rows; what moves is `Ends cp`, to visible rows only.  A
  -- lane ending with silent pins owed then reaches `LaneEnd`, whose `≈`
  -- slack is one skip at `p`, and `reach-≈` counts that slack as one row.
  -- DEAD ROUTE: a `G` invariant emptying the source at a body's end: the
  --   source is still owed its whole subscription there.
  -- DEAD ROUTE: `ConnT` dropping its `burst` pins past the body's end.
  --   rxjs subscribes the source after a body that has already ended, so
  --   an endless synchronous source still blocks a sibling; the pins
  --   carry that.  And a pin's `Dep` reaches only rows before its
  --   connect, so no row of the body's end can decide it.
  rise-body-cp : ∀ {R Γ X B} (k : CS) (o : St Γ X) (c : Ctx R Γ B) s p
               → Sim ⟨ inBody k o c , s , rising cp , p ⟩ [] ⟨ c , connS (record k { owedAt = just p }) o s , rising cp , p ⟩

-- A BODY'S VALUE IS ITS CONNECT'S.
rise-body-nx : ∀ {R Γ X B} (k : CS) (o : St Γ X) (c : Ctx R Γ B) s x p
             → Sim ⟨ inBody k o c , s , rising (nx x) , p ⟩ [] ⟨ c , connS k o s , rising (nx x) , p ⟩
rise-body-nx k o c s x p i with alive s in al
rise-body-nx k o c s x p (inv g (_ , _ , op , _)) | false = ⊥-elim (open-alive s op al)
rise-body-nx k o c s x p (inv g (uc , (afs , lc) , _ , af , _)) | true =
  inv g (uc , lc , tt , after-conn (CS.connAt k) (rows (env c) o) (rows (env (inBody k o c)) s) {p} afs af , tt)
  , silent (vis-≃ (up-≃ c (conn-plus-nx (CS.connAt k) _ _ p x)))

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
rise-sim (inTake true w free c) s (nx a) p eq with w a in wa
rise-sim (inTake true w free c) s (nx a) p refl | true  = rise-take-nx true w c s a p wa
rise-sim (inTake true w free c) s (nx a) p refl | false = rise-take-fail true w c s a p wa
rise-sim (inTake false w free c) s (nx a) p eq with w a in wa
rise-sim (inTake false w free c) s (nx a) p refl | true  = rise-take-nx false w c s a p wa
rise-sim (inTake false w free c) s (nx a) p refl | false = rise-take-fail false w c s a p wa
rise-sim (inTake i w free c)       s cp p refl = rise-take-cp i w c s p
rise-sim (inTake i w (cpAt r) c)   s e  p refl = rise-take-owed i w (cpAt r) c s e p (λ ())
rise-sim (inTake i w (cutAt r) c)  s e  p refl = rise-take-owed i w (cutAt r) c s e p (λ ())
rise-sim (inTake i w (overAt r) c) s e  p refl = rise-take-owed i w (overAt r) c s e p (λ ())
rise-sim (inOuter (mergeᶠ (just m)) f d n q ls c) o (nx a) p refl = rise-bounded-nx m f d n q ls c o a p
rise-sim (inOuter (mergeᶠ (just m)) f d n q ls c) o cp     p refl = rise-bounded-cp m f d n q ls c o p
rise-sim (inLanes (mergeᶠ (just m)) f d n q o pre post c) s (nx b) p refl = rise-bounded-lane-nx m f d n q o pre post c s b p
rise-sim (inLanes (mergeᶠ (just m)) f d n q o pre post c) s cp     p refl = rise-bounded-lane-cp m f d n q o pre post c s p
rise-sim (inOuter switchᶠ f d n q ls c) o (nx a) p eq with killAll ls in kl
rise-sim (inOuter switchᶠ f d n q ls c) o (nx a) p refl | ls′ , t = rise-switch-nx f d n q ls c o a p ls′ t kl
rise-sim (inOuter switchᶠ f d n q ls c) o cp     p refl = rise-switch-cp f d n q ls c o p
rise-sim (inLanes switchᶠ f d n q o pre post c) s (nx b) p refl = rise-switch-lane-nx f d n q o pre post c s b p
rise-sim (inLanes switchᶠ f d n q o pre post c) s cp     p refl = rise-switch-lane-cp f d n q o pre post c s p
rise-sim (inOuter exhaustᶠ f d n q ls c) o (nx a) p eq with n ≡ᵇ 0 in z
rise-sim (inOuter exhaustᶠ f d n q ls c) o (nx a) p refl | true  = rise-exhaust-run f d n q ls c o a p z
rise-sim (inOuter exhaustᶠ f d n q ls c) o (nx a) p refl | false = rise-exhaust-drop f d n q ls c o a p z
rise-sim (inOuter exhaustᶠ f d n q ls c) o cp     p refl = rise-exhaust-cp f d n q ls c o p
rise-sim (inLanes exhaustᶠ f d n q o pre post c) s (nx b) p refl = rise-exhaust-lane-nx f d n q o pre post c s b p
rise-sim (inLanes exhaustᶠ f d n q o pre post c) s cp     p refl = rise-exhaust-lane-cp f d n q o pre post c s p
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
  stopK : ∀ {A} i (q : A → Bool) r (s : St Γ A) → Marked (takeS i q (cpAt r) s) cpM
  cutK  : ∀ {A} i (q : A → Bool) r (s : St Γ A) → Marked (takeS i q (cutAt r) s) cutM

postulate
  -- WHAT A GOOD TREE'S SEARCH FINDS: an of's next, a switch's attach, a
  -- connect's own, a joiner's next, a cold's turn, or a failed take's
  -- stop or cut.
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

  -- A FAILED TAKE'S COMPLETION: shown at its stop unless closed above.
  abs-stop : ∀ {R Γ′ A′ Γ A} {c : Ctx R Γ′ A′} {s} {c′ : Ctx R Γ A} {i} {q : A → Bool} {r s₀ κ k′ sh t} p
           → search top (plug c s) ≡ just (found (Γ , A , c′ , takeS i q (cpAt r) s₀) cpM κ) → run c′ (takeS i q (cpAt r) s₀) cpM p ≡ moved k′ sh t
           → Sim ⟨ c , s , absorbed , p ⟩ sh k′

  -- A FAILED TAKE PAST ITS STOP CUTS ITS SOURCE: nothing owed changes.
  abs-cut : ∀ {R Γ′ A′ Γ A} {c : Ctx R Γ′ A′} {s} {c′ : Ctx R Γ A} {i} {q : A → Bool} {r s₀ κ k′ sh t} p
          → search top (plug c s) ≡ just (found (Γ , A , c′ , takeS i q (cutAt r) s₀) cutM κ) → run c′ (takeS i q (cutAt r) s₀) cutM p ≡ moved k′ sh t
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

run-cut-mv : ∀ {R Γ A} (c : Ctx R Γ A) i (q : A → Bool) r (s : St Γ A) p → Mv (run c (takeS i q (cutAt r) s) cutM p)
run-cut-mv c i q r s p with cut s
... | _ = tt

run-join-mv : ∀ {R Γ A} (c : Ctx R Γ A) j g (x : A ∈ Γ) ib p → Mv (run c (joinS j g x ib) joinM p)
run-join-mv c j g x []              p = tt
run-join-mv c j g x ((q , nx a) ∷ ib) p = tt
run-join-mv c j g x ((q , cp) ∷ ib)   p = tt

-- The driver's steps read back as the engine's.
module _ {R : Set} where
  open Driver R using (took; value; complete; drained) renaming (silent to τ)

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

  mv-drained : (x : Stepped R) → Mv x → took x ≢ drained
  mv-drained (moved k [] tr)                _ ()
  mv-drained (moved k ((_ , nx _) ∷ _) tr) _ ()
  mv-drained (moved k ((_ , cp) ∷ _) tr)   _ ()
  mv-drained quiet                          () _
  mv-drained (starting _ _ _)               () _
  mv-drained (turn _)                       () _

  quiet-τ : ∀ {x t k′} → x ≡ quiet → took x ≢ τ t k′
  quiet-τ refl ()

  quiet-val : ∀ {x t p a k′} → x ≡ quiet → took x ≢ value t p a k′
  quiet-val refl ()

  quiet-fin : ∀ {x p} → x ≡ quiet → took x ≢ complete p
  quiet-fin refl ()

-- A driver step that shows nothing: a cold's subscription or turn.
module _ {R : Set} where
  open Driver R using (Step; played; value; complete; drained) renaming (silent to τ)

  Hush : Step → Set
  Hush (τ _ _) = ⊤
  Hush _       = ⊥

  played-hush : ∀ {A} b l cl dv st → Hush (played (leaf {A = A} b l cl dv st))
  played-hush true (ending e) cl dv st              = tt
  played-hush false l cl dv st                      = tt
  played-hush true (play τ′ u i t fr) true dv st    = tt
  played-hush true over true dv st                  = tt
  played-hush true (play τ′ u i t (emit a k)) false dv st = tt
  played-hush true (play τ′ u i t (stall k)) false dv st  = tt
  played-hush true (play τ′ u i t (close k)) false dv st  = tt
  played-hush true over false dv st                 = tt

  hush-val : ∀ {x t p a k′} → Hush x → x ≡ value t p a k′ → ⊥
  hush-val h refl = h

  hush-fin : ∀ {x p} → Hush x → x ≡ complete p → ⊥
  hush-fin h refl = h

  hush-drained : ∀ {x} → Hush x → x ≢ drained
  hush-drained h refl = h

------------------------------------------------------------------------
-- The run

join-mv : ∀ {R Γ A} (c : Ctx R Γ A) (x : A ∈ Γ) q {p} → Mv (stepᴹ ⟨ c , pend (connected x) q , subscribing , p ⟩)
join-mv c x q with closedUp c x
... | true  = tt
... | false = tt

join-sim : ∀ {R Γ A} {k′ : Conf R} {sh t} (c : Ctx R Γ A) (x : A ∈ Γ) q p
         → stepᴹ ⟨ c , pend (connected x) q , subscribing , p ⟩ ≡ moved k′ sh t → Sim ⟨ c , pend (connected x) q , subscribing , p ⟩ sh k′
join-sim c x q p eq with closedUp c x in cu
join-sim c x q p refl | true  = sub-joined c x q p cu
join-sim c x q p refl | false = sub-join c x q p cu

-- Where a step goes: on, linked a step at a time, engine or driver.
data Reach {R} (k : Conf R) : Set₁ where
  within : Mv (stepᴹ k) → (∀ {k′ sh t} → stepᴹ k ≡ moved k′ sh t → Sim k sh k′) → Reach k
  driven : Hush (Driver.step R k) → (∀ {t k′} → Driver.step R k ≡ Driver.silent t k′ → Sim k [] k′) → Reach k
  stills : stepᴹ k ≡ quiet → (∀ {q e} → Vis (RT k) q e → ⊥) → Reach k

-- A step linked, read off the step itself, so a search's outcome can be
-- abstracted in it.
data Link {R} (k : Conf R) : Stepped R → Set₁ where
  mvL   : ∀ {x} → Mv x → (∀ {k′ sh t} → x ≡ moved k′ sh t → Sim k sh k′) → Link k x
  hushL : ∀ {x} → Hush (Driver.took R x) → (∀ {t k′} → Driver.took R x ≡ Driver.silent t k′ → Sim k [] k′) → Link k x
  stillL : (∀ {q e} → Vis (RT k) q e → ⊥) → Link k quiet

linked : ∀ {R} {k : Conf R} → Link k (stepᴹ k) → Reach k
linked {k = k} = go refl
  where
    go : ∀ {x} → stepᴹ k ≡ x → Link k x → Reach k
    go eq   (stillL v)    = stills eq v
    go refl (mvL mv sim)  = within mv sim
    go refl (hushL h sim) = driven h sim

-- A good tree whose search finds nothing has no rows.
search-none : ∀ {R} (t : St [] R) → Good []ᴬ t → search top t ≡ nothing → ∀ {q e} → rows []ᴬ t q e → ⊥
search-none t g = go (seek top t) (seek-ok top t g)
  where
    go : ∀ y → OK (rows []ᴬ t) y → mapᴹ proj₁ y ≡ nothing → ∀ {q e} → rows []ᴬ t q e → ⊥
    go nothing  e _ = e
    go (just _) _ ()

-- A mark run, by what the search found.
abs-link : ∀ {R Γ A} (c : Ctx R Γ A) s p → Inv ⟨ c , s , absorbed , p ⟩ → Link ⟨ c , s , absorbed , p ⟩ (stepᴹ ⟨ c , s , absorbed , p ⟩)
abs-link c s p i with search top (plug c s) in fd
... | nothing = stillL λ v → search-none (plug c s) (good i) fd (_≃_.to (up-plug c s) (proj₁ v))
... | just (found (_ , _ , c′ , s′) m κ) with found-mark c s (good i) fd
...   | ofK j q xs     = mvL (run-of-mv c′ j q xs p) (λ eq → abs-of p fd eq)
...   | attK l q s₀    = mvL (run-att-mv c′ l q s₀ p) (λ eq → abs-att p fd eq)
...   | conK k o b m w = mvL (run-con-mv c′ k o b m p w) (λ eq → abs-con p fd eq)
...   | joinK j g x ib = mvL (run-join-mv c′ j g x ib p) (λ eq → abs-join p fd eq)
...   | stopK j q r s₀ = mvL tt (λ eq → abs-stop p fd eq)
...   | cutK j q r s₀  = mvL (run-cut-mv c′ j q r s₀ p) (λ eq → abs-cut p fd eq)
...   | leafK b l      = hushL (played-hush b l (closed c′) (λ e l′ b′ p′ → ⟨ c′ , coldS b′ l′ , (if not (closed c′) then rising e else absorbed) , p′ ⟩) (λ l′ → ⟨ c′ , coldS b l′ , absorbed , p ⟩)) (λ eq → abs-leaf p fd eq)

reach-pend : ∀ {R Γ A} (c : Ctx R Γ A) (o : Obs Timeline Γ A) q p → Inv ⟨ c , pend o q , subscribing , p ⟩ → Reach ⟨ c , pend o q , subscribing , p ⟩
reach-pend c empty                           q p i = within tt λ { refl → sub-empty c q p }
reach-pend c (of xs)                         q p i = within tt λ { refl → sub-of c xs q p }
reach-pend c (map f s)                       q p i = within tt λ { refl → sub-map c f s q p }
reach-pend c (flatMap (mergeᶠ nothing) f s)  q p i = within tt λ { refl → sub-merge c f s q p }
reach-pend c (connected x)                   q p i = within (join-mv c x q {p}) (join-sim c x q p)
reach-pend c (cold x)                        q p i = driven tt λ { refl → sub-cold c x q p }
reach-pend c (scan f z s)                    q p i = within tt λ { refl → sub-scan c f z s q p }
reach-pend c (takeWhile b w s)               q p i = within tt λ { refl → sub-take c b w s q p }
reach-pend c (flatMap (mergeᶠ (just m)) f s) q p i = within tt λ { refl → sub-bounded c m f s q p }
reach-pend c (flatMap switchᶠ f s)           q p i = within tt λ { refl → sub-switch c f s q p }
reach-pend c (flatMap exhaustᶠ f s)          q p i = within tt λ { refl → sub-exhaust c f s q p }
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

-- A silent step keeps the visible rows.
sim-tau : ∀ {R} {k k′ : Conf R} {t} → Inv k → Driver.step R k ≡ Driver.silent t k′ → Inv k′ × Vis (RT k) ≃ Vis (RT k′)
sim-tau {k = k} i e = go (reach k i)
  where
    go : Reach k → _
    go (driven h sim) with sim e i
    ... | i′ , silent q = i′ , q
    go (within mv sim) with τ-moved (stepᴹ k) mv e
    ... | _ , eq with sim eq i
    ...   | i′ , silent q = i′ , q
    go (stills eq _) = ⊥-elim (quiet-τ eq e)

-- A value shows the least visible row and drops it.
sim-val : ∀ {R} {k k′ : Conf R} {t p a} → Inv k → Driver.step R k ≡ Driver.value t p a k′
        → Inv k′ × Lowest (RT k) p (out a) × Vis (Past p (RT k)) ≃ Vis (RT k′)
sim-val {k = k} i e = go (reach k i)
  where
    go : Reach k → _
    go (driven h sim) = ⊥-elim (hush-val h e)
    go (stills eq _)  = ⊥-elim (quiet-val eq e)
    go (within mv sim) with val-moved (stepᴹ k) mv e
    ... | _ , _ , eq with sim eq i
    ...   | i′ , shown v lt q = i′ , (v , λ {q} {e′} → lt {q} {e′}) , q

-- The end shows the least visible row.
sim-fin : ∀ {R} {k : Conf R} {p} → Inv k → Driver.step R k ≡ Driver.complete p → Lowest (RT k) p end
sim-fin {k = k} i e = go (reach k i)
  where
    go : Reach k → _
    go (driven h sim) = ⊥-elim (hush-fin h e)
    go (stills eq _)  = ⊥-elim (quiet-fin eq e)
    go (within mv sim) with fin-moved (stepᴹ k) mv e
    ... | _ , _ , _ , eq with sim eq i
    ...   | _ , shown v lt _ = v , λ {q} {e′} → lt {q} {e′}

-- A drained engine owes nothing visible.
drained-quiet : ∀ {R} {k : Conf R} → Inv k → Driver.step R k ≡ Driver.drained → ∀ {q e} → Vis (RT k) q e → ⊥
drained-quiet {k = k} i e = go (reach k i)
  where
    go : Reach k → ∀ {q e} → Vis (RT k) q e → ⊥
    go (within mv sim) _ = mv-drained (stepᴹ k) mv e
    go (driven h sim)  _ = hush-drained h e
    go (stills _ v)      = v

-- Whatever a run from `k` shows, a reader of its rows is shown.
sound-from : ∀ {R} {k : Conf R} → Inv k → ∀ {rs} → Steps k rs → Shows* (RT k) (conv rs)
sound-from i []          = []
sound-from i (tau e st)  = let (i′ , q) = sim-tau i e in Shows*-≃ (≃-sym q) (sound-from i′ st)
sound-from i (val e st)  = let (i′ , l , q) = sim-val i e in l ∷ Shows*-≃ (≃-sym q) (sound-from i′ st)
sound-from i (fin e)     = sim-fin i e ∷ []

-- THE SKIPS BETWEEN: least visible rows shown in turn are a reader's run.
-- Each has few rows before it, as it is entered, and no end before it,
-- since only silent rows follow an end.
module _ {A} (d : Den A) (p₀ : Pos) (quiet : ∀ {c y e} → enter d p₀ c end → enter d p₀ y e → c ≺ y → Silent e) where
  private
    t : EmissionSet A
    t = enter d p₀

    dep : ∀ {q} {e : Ev A} {k e′} → Visible e → Dep q e k e′
    dep {e = out _} _ = tt
    dep {e = end}   _ = tt

  run-of : ∀ c {vs} → Shows* (Beyond t c) vs → Run t c vs
  run-of c [] = []
  run-of c (_∷_ {p = p} ((x , vi) , lt) rest) =
    (((tp , proper) , entered-few d p₀ (λ {k} {e′} → dep {p} {_} {k} {e′} vi) tp) , vi , cq , λ tk vk ck → lt (back c tk ck , vk))
    ∷ run-of (just p) (Shows*-≃ (narrow c cq) rest)
    where
      tp = proj₁ (into c x)
      cq = proj₂ (into c x)
      proper : ∀ {k} → t k end → p ≼ k
      proper {k} tk with ≼-or-≻ p k
      ... | inj₁ le = le
      ... | inj₂ kp = ⊥-elim (loud vi (quiet tk tp kp))

-- Only silent rows follow a program's end.
quiet-root : ∀ {R} (o : PureObs [] R) {c y e} → enter (⟦ o ⟧ []ᴬ) root c end → enter (⟦ o ⟧ []ᴬ) root y e → c ≺ y → Silent e
quiet-root o = InvAt.quiet (inv-⟦⟧ o []ᴬ (λ ()) root (tt , λ ()))

met-of-shown : ∀ {R} {o : PureObs [] R} {vs} → Shows* (enter (⟦ o ⟧ []ᴬ) root) vs → Meets (enter (⟦ o ⟧ []ᴬ) root) vs
met-of-shown {o = o} = run-of (⟦ o ⟧ []ᴬ) root (quiet-root o) nothing

-- THE SOUND HALF: what the engine shows, a subscriber to the program's
-- rows is shown.
sound : ∀ {R} {o : PureObs [] R} {rs} → Steps (load o) rs → Meets (enter (⟦ o ⟧ []ᴬ) root) (conv rs)
sound {o = o} st = met-of-shown {o = o} (sound-from (inv tt₁ (tt , (tt , λ ()))) st)
