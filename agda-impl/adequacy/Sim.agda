{-# OPTIONS --guardedness #-}

-- THE DIRECT LINK: the engine run against the emission set's rows, with
-- no stepper and no tower between them.  A step keeps the visible rows or
-- shows the least and drops it, by mode: a subscription entered as the
-- rows of what it begins, a rise read up one frame, a mark run where the
-- search's bound says it leads.
--
-- The link is grown one former at a time.  Subscribing to a former not
-- yet grown hands the rest of the run to that former's own leaf
-- (`beyond-scan` and its siblings), so `reach` is total by pattern
-- matching: growing a former turns its leaf into the arms the link needs
-- for it, and the coverage checker names every former still owed.
module adequacy.Sim where

open import Data.Bool using (true; false; if_then_else_; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (_≡ᵇ_)
open import Data.List using (List; []; _∷_; [_]; null)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _,_; proj₁)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to tt₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Tree using (Obs; mergeᶠ; switchᶠ; exhaustᶠ; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.Events using (Timeline; root)
open import denotation.EmissionSet using (EmissionSet; out; end; MapT; map-out; map-skip; map-pin; map-end; _≼_; enter; ⟦_⟧)
open import denotation.Laws.Modulus using (≺-irrefl; ≺-absurd)
open import denotation.Laws.Worlds using (GoodEnv)
open import denotation.Laws using (inv-⟦⟧)
open import operation.PureObservable using (PureObs; module Machine; module Driver)
open Machine using (St; Ctx; Conf; ⟨_,_,_,_⟩; subscribing; absorbed; rising; load; moved; plug; search; found; Mark; ofM; attM;
                    rise; run; start; dequeue; settle; alive; ended; mapEv; nx; cp; attAt; attached; Torn;
                    Stepped; quiet; begin; admit; closed; killAll; unsubIf; free; cpAt; cutAt; overAt;
                    pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
                    top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody)
                    renaming (Ev to Evᴹ; Shown to Shownᴹ; step to stepᴹ)
open import adequacy.Rows using (env; rows; RT; toEv; Visible; Vis; Past; Plus; old; new; _≃_; _⇄_; silent; shown; Steps;
  Shows*; Shows*-≃; ≃-sym; conv; []; _∷_; tau; val; fin)
open import adequacy.Bound using (Good; G; Rooted; mergeG₀)
open import adequacy.Up using (up-≃; ≃-refl; vis-≃)
open import adequacy.Skip using (After)
open import adequacy.Inv using (Inv; inv; good; Sim; Ends; GoodC; good-split; open-alive)
open import adequacy.LaneCp using (rise-lane-cp)
open import adequacy.AbsOf using (abs-of)
open import denotation.Read using (Meets)
open import adequacy.Owes using (Swap; good-swap)
open import adequacy.Enter using (enter-map; enter-merge; flat-∅)

-- A good context binds nothing, so its environment keeps the invariant.
env-good : ∀ {R Γ A} (c : Ctx R Γ A) → GoodC c → GoodEnv (env c)
env-good top                                         _  ()
env-good (inMap f c)                                 gc = env-good c gc
env-good (inCut l a c)                               gc = env-good c gc
env-good (inLn b c)                                  gc = env-good c gc
env-good (inOuter (mergeᶠ nothing) f d n q ls c)     gc = env-good c gc
env-good (inLanes (mergeᶠ nothing) f d n q o pre post c) gc = env-good c gc
env-good (inOuter (mergeᶠ (just _)) f d n q ls c)    ()
env-good (inOuter switchᶠ f d n q ls c)              ()
env-good (inOuter exhaustᶠ f d n q ls c)             ()
env-good (inLanes (mergeᶠ (just _)) f d n q o pre post c) ()
env-good (inLanes switchᶠ f d n q o pre post c)      ()
env-good (inLanes exhaustᶠ f d n q o pre post c)     ()
env-good (inScan f z c)                              ()
env-good (inTake i q w c)                            ()
env-good (inSrc k b c)                               ()
env-good (inBody k o c)                              ()

-- Nor does it bind anything to read.
unbound : ∀ {R Γ A X} (c : Ctx R Γ A) → GoodC c → X ∈ Γ → ⊥
unbound top                                         _  ()
unbound (inMap f c)                                 gc x = unbound c gc x
unbound (inCut l a c)                               gc x = unbound c gc x
unbound (inLn b c)                                  gc x = unbound c gc x
unbound (inOuter (mergeᶠ nothing) f d n q ls c)     gc x = unbound c gc x
unbound (inLanes (mergeᶠ nothing) f d n q o pre post c) gc x = unbound c gc x
unbound (inOuter (mergeᶠ (just _)) f d n q ls c)    ()
unbound (inOuter switchᶠ f d n q ls c)              ()
unbound (inOuter exhaustᶠ f d n q ls c)             ()
unbound (inLanes (mergeᶠ (just _)) f d n q o pre post c) ()
unbound (inLanes switchᶠ f d n q o pre post c)      ()
unbound (inLanes exhaustᶠ f d n q o pre post c)     ()
unbound (inScan f z c)                              ()
unbound (inTake i q w c)                            ()
unbound (inSrc k b c)                               ()
unbound (inBody k o c)                              ()

------------------------------------------------------------------------
-- Subscribing

postulate
  sub-empty : ∀ {R Γ A} (c : Ctx R Γ A) p → Sim ⟨ c , pend empty , subscribing , p ⟩ [] ⟨ c , ofS 0 p [] , absorbed , p ⟩
  sub-of    : ∀ {R Γ A} (c : Ctx R Γ A) xs p → Sim ⟨ c , pend (of xs) , subscribing , p ⟩ [] ⟨ c , ofS 0 p xs , absorbed , p ⟩

-- A map entered: its source pending under it.
sub-map : ∀ {R Γ A B} (c : Ctx R Γ B) (f : A → B) s p → Sim ⟨ c , pend (map f s) , subscribing , p ⟩ [] ⟨ inMap f c , pend s , subscribing , p ⟩
sub-map c f s p (inv g (uc , _ , ok)) = inv (good-swap c sw g) (uc , tt , ok) , silent (vis-≃ (up-≃ c (enter-map (env c) f s p)))
  where
    sw : Swap (env c) (pend (map f s)) (mapS f (pend s))
    sw = record { same = (λ ()) ⇄ (λ { (map-out ()) ; (map-skip ()) ; (map-pin ()) ; (map-end ()) }) ; live≡ = refl ; node = λ _ x → x ; lane = λ _ () ; body = λ _ _ () }

-- A merge entered: its outer pending under it, attached at `p`, nothing begun.
sub-merge : ∀ {R Γ A B} (c : Ctx R Γ B) f (s : Obs Timeline Γ A) p
          → Sim ⟨ c , pend (flatMap (mergeᶠ nothing) f s) , subscribing , p ⟩ [] ⟨ inCut true (attAt p) (inOuter (mergeᶠ nothing) f false 0 [] [] c) , pend s , subscribing , p ⟩
sub-merge c f s p (inv g (uc , _ , ok)) = inv (good-swap c sw g) ((tt , uc) , tt , ok) , silent (vis-≃ (up-≃ c (enter-merge (env c) f s p)))
  where
    -- The outer about to enter at `p`: inside its own entry, nothing begun.
    rt : Rooted (env c) (rows (env c) (cutS true (attAt p) (pend s))) []
    rt = record { o₀ = s ; p₀ = p ; inv = inv-⟦⟧ s (env c) (env-good c (proj₁ (good-split c _ g))) p ok ; sub = λ () ; qs = [] ; roots = tt }
    node′ : ∀ v → G (env c) v (pend (flatMap (mergeᶠ nothing) f s)) → G (env c) v (flatS (mergeᶠ nothing) f false 0 [] (cutS true (attAt p) (pend s)) [])
    node′ true  _ = record { outer = tt₁ ; lanesG = tt₁ ; fresh = refl ; count = refl ; spent = λ () ; rooted = rt }
    node′ false _ = mergeG₀ tt₁ tt₁ refl
    sw : Swap (env c) (pend (flatMap (mergeᶠ nothing) f s)) (flatS (mergeᶠ nothing) f false 0 [] (cutS true (attAt p) (pend s)) [])
    sw = record { same = ≃-sym (flat-∅ _ false) ; live≡ = refl ; node = node′ ; lane = λ _ () ; body = λ _ _ () }

stay : ∀ {R} {k : Conf R} → Sim k [] k
stay i = i , silent ((λ x → x) ⇄ (λ x → x))

-- A node already running, not a pending program.
Running : ∀ {Γ A} → St Γ A → Set
Running (pend _) = ⊥
Running _        = ⊤

-- Subscribing to a node already running: nothing to do.
sub-sim : ∀ {R Γ A} {k′ : Conf R} {sh t} (c : Ctx R Γ A) (s : St Γ A) p → Running s → stepᴹ ⟨ c , s , subscribing , p ⟩ ≡ moved k′ sh t → Sim ⟨ c , s , subscribing , p ⟩ sh k′
sub-sim c (pend _)          p () _
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

rise-map : ∀ {R Γ A B} (f : A → B) (c : Ctx R Γ B) s e p → Sim ⟨ inMap f c , s , rising e , p ⟩ [] ⟨ c , mapS f s , rising (mapEv f e) , p ⟩
rise-map f c s e p i with alive s in al
rise-map f c s e p (inv g (_ , _ , _ , op , _)) | false = ⊥-elim (open-alive s op al)
rise-map f c s e p (inv g (uc , lc , os , _ , af , en)) | true =
  inv g (uc , lc , os , tt , after-map f {p = p} af , ends-map f e en) , silent (vis-≃ (up-≃ c (map-plus f (rows (env c) s) p e)))

rise-cut : ∀ {R Γ A} l a (c : Ctx R Γ A) s e p → Sim ⟨ inCut l a c , s , rising e , p ⟩ [] ⟨ c , cutS l a s , (if l then rising e else absorbed) , p ⟩
rise-cut false a c s e p (inv g (() , _))
rise-cut true  a c s e p i with alive s in al
rise-cut true  a c s e p (inv g (_ , _ , _ , op , _)) | false = ⊥-elim (open-alive s op al)
rise-cut true  a c s e p (inv g (uc , lc , os , _ , af , en)) | true = inv g (uc , lc , os , tt , af , en) , silent ≃-refl

rise-ln : ∀ {R Γ A} b (c : Ctx R Γ A) s e p → Sim ⟨ inLn b c , s , rising e , p ⟩ [] ⟨ c , lnS b s , rising e , p ⟩
rise-ln false c s e p (inv g (() , _))
rise-ln true  c s e p i with alive s in al
rise-ln true  c s e p (inv g (_ , _ , _ , op , _)) | false = ⊥-elim (open-alive s op al)
rise-ln true  c s e p (inv g (uc , lc , os , _ , af , en)) | true = inv g (uc , lc , os , tt , af , en) , silent ≃-refl

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

rise-sim : ∀ {R Γ A} {k′ : Conf R} {sh t} (c : Ctx R Γ A) (s : St Γ A) e p → stepᴹ ⟨ c , s , rising e , p ⟩ ≡ moved k′ sh t → Sim ⟨ c , s , rising e , p ⟩ sh k′
rise-sim top            s e p refl = rise-top s e p
rise-sim (inMap f c)    s e p refl = rise-map f c s e p
rise-sim (inCut l a c)  s e p refl = rise-cut l a c s e p
rise-sim (inLn b c)     s e p refl = rise-ln b c s e p
rise-sim (inOuter (mergeᶠ nothing) f d n q ls c) o (nx a) p refl = rise-outer-nx f d n q ls c o a p
rise-sim (inOuter (mergeᶠ nothing) f d n q ls c) o cp     p refl = rise-outer-cp f d n q ls c o p
rise-sim (inLanes (mergeᶠ nothing) f d n q o pre post c) s (nx b) p refl = rise-lane-nx f d n q o pre post c s b p
rise-sim (inLanes (mergeᶠ nothing) f d n q o pre post c) s cp     p refl = rise-lane-cp f d n q o pre post c s p
rise-sim c@(inScan _ _ _)                      s e p eq i = ⊥-elim (proj₁ (good-split c s (good i)))
rise-sim c@(inTake _ _ _ _)                    s e p eq i = ⊥-elim (proj₁ (good-split c s (good i)))
rise-sim c@(inOuter (mergeᶠ (just _)) _ _ _ _ _ _) s e p eq i = ⊥-elim (proj₁ (good-split c s (good i)))
rise-sim c@(inOuter switchᶠ _ _ _ _ _ _)       s e p eq i = ⊥-elim (proj₁ (good-split c s (good i)))
rise-sim c@(inOuter exhaustᶠ _ _ _ _ _ _)      s e p eq i = ⊥-elim (proj₁ (good-split c s (good i)))
rise-sim c@(inLanes (mergeᶠ (just _)) _ _ _ _ _ _ _ _) s e p eq i = ⊥-elim (proj₁ (good-split c s (good i)))
rise-sim c@(inLanes switchᶠ _ _ _ _ _ _ _ _)   s e p eq i = ⊥-elim (proj₁ (good-split c s (good i)))
rise-sim c@(inLanes exhaustᶠ _ _ _ _ _ _ _ _)  s e p eq i = ⊥-elim (proj₁ (good-split c s (good i)))
rise-sim c@(inSrc _ _ _)                       s e p eq i = ⊥-elim (proj₁ (good-split c s (good i)))
rise-sim c@(inBody _ _ _)                      s e p eq i = ⊥-elim (proj₁ (good-split c s (good i)))

------------------------------------------------------------------------
-- A mark run

-- The marks a good tree's nodes own.
data Marked {Γ : List Set} : ∀ {A} → St Γ A → Mark → Set₁ where
  ofK  : ∀ {A} i p (xs : List A) → Marked (ofS i p xs) ofM
  attK : ∀ {A} l p (s : St Γ A) → Marked (cutS l (attAt p) s) attM

postulate
  -- WHAT A GOOD TREE'S SEARCH FINDS: an of's next, or a switch's attach.
  found-mark : ∀ {R Γ′ A′} (c : Ctx R Γ′ A′) s {Γ A c′ s′ m κ} → Good []ᴬ (plug c s) → search top (plug c s) ≡ just (found (Γ , A , c′ , s′) m κ) → Marked s′ m

  -- A SWITCH ATTACHED: nothing owed changes.
  abs-att : ∀ {R Γ′ A′ Γ A} {c : Ctx R Γ′ A′} {s} {c′ : Ctx R Γ A} {l p₀ s₀ κ k′ sh t} p
          → search top (plug c s) ≡ just (found (Γ , A , c′ , cutS l (attAt p₀) s₀) attM κ) → run c′ (cutS l (attAt p₀) s₀) attM p ≡ moved k′ sh t
          → Sim ⟨ c , s , absorbed , p ⟩ sh k′

abs-sim : ∀ {R Γ A} {k′ : Conf R} {sh t} (c : Ctx R Γ A) (s : St Γ A) p → stepᴹ ⟨ c , s , absorbed , p ⟩ ≡ moved k′ sh t → Sim ⟨ c , s , absorbed , p ⟩ sh k′
abs-sim c s p eq i with search top (plug c s) in fd
abs-sim c s p ()  i | nothing
abs-sim c s p eq  i | just (found (_ , _ , c′ , s′) m κ) with found-mark c s (good i) fd
... | ofK _ _ _  = abs-of p fd eq i
... | attK _ _ _ = abs-att p fd eq i

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

abs-mv : ∀ {R Γ A} (c : Ctx R Γ A) s p → Inv ⟨ c , s , absorbed , p ⟩ → Mv (stepᴹ ⟨ c , s , absorbed , p ⟩)
abs-mv c s p i with search top (plug c s) in fd
... | nothing = tt
... | just (found (_ , _ , c′ , s′) m κ) with found-mark c s (good i) fd
...   | ofK j q xs  = run-of-mv c′ j q xs p
...   | attK l q s₀ = run-att-mv c′ l q s₀ p

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

------------------------------------------------------------------------
-- The run

-- Whatever a run from `k` shows, a reader of its rows is shown.
Runs : ∀ {R} → Conf R → Set₁
Runs k = ∀ {rs} → Steps k rs → Shows* (RT k) (conv rs)

-- SUBSCRIBING TO A FORMER NOT YET GROWN: the run from there, its own leaf.
-- Each owes what growing it would: its node's place in `adequacy.Bound.G`,
-- its rows and what it owes, and the step arms of the nodes it builds.
postulate
  beyond-cold    : ∀ {R Γ A} (c : Ctx R Γ A) x p → Inv ⟨ c , pend (cold x) , subscribing , p ⟩ → Runs ⟨ c , pend (cold x) , subscribing , p ⟩
  beyond-scan    : ∀ {R Γ A B} (c : Ctx R Γ B) (f : B → A → B) z (s : Obs Timeline Γ A) p
                 → Inv ⟨ c , pend (scan f z s) , subscribing , p ⟩ → Runs ⟨ c , pend (scan f z s) , subscribing , p ⟩
  beyond-take    : ∀ {R Γ A} (c : Ctx R Γ A) b q (s : Obs Timeline Γ A) p
                 → Inv ⟨ c , pend (takeWhile b q s) , subscribing , p ⟩ → Runs ⟨ c , pend (takeWhile b q s) , subscribing , p ⟩
  beyond-bounded : ∀ {R Γ A B} (c : Ctx R Γ B) m (f : A → Obs Timeline Γ B) s p
                 → Inv ⟨ c , pend (flatMap (mergeᶠ (just m)) f s) , subscribing , p ⟩ → Runs ⟨ c , pend (flatMap (mergeᶠ (just m)) f s) , subscribing , p ⟩
  beyond-switch  : ∀ {R Γ A B} (c : Ctx R Γ B) (f : A → Obs Timeline Γ B) s p
                 → Inv ⟨ c , pend (flatMap switchᶠ f s) , subscribing , p ⟩ → Runs ⟨ c , pend (flatMap switchᶠ f s) , subscribing , p ⟩
  beyond-exhaust : ∀ {R Γ A B} (c : Ctx R Γ B) (f : A → Obs Timeline Γ B) s p
                 → Inv ⟨ c , pend (flatMap exhaustᶠ f s) , subscribing , p ⟩ → Runs ⟨ c , pend (flatMap exhaustᶠ f s) , subscribing , p ⟩
  beyond-connect : ∀ {R Γ A B} (c : Ctx R Γ B) (s : Obs Timeline Γ A) b p
                 → Inv ⟨ c , pend (connect s b) , subscribing , p ⟩ → Runs ⟨ c , pend (connect s b) , subscribing , p ⟩
  beyond-defer   : ∀ {R Γ A} (c : Ctx R Γ A) l p → Inv ⟨ c , pend (defer l) , subscribing , p ⟩ → Runs ⟨ c , pend (defer l) , subscribing , p ⟩

-- Where a step goes: on, linked a step at a time, or into a former's leaf.
data Reach {R} (k : Conf R) : Set₁ where
  within : Mv (stepᴹ k) → (∀ {k′ sh t} → stepᴹ k ≡ moved k′ sh t → Sim k sh k′) → Reach k
  beyond : Runs k → Reach k

reach-pend : ∀ {R Γ A} (c : Ctx R Γ A) (o : Obs Timeline Γ A) p → Inv ⟨ c , pend o , subscribing , p ⟩ → Reach ⟨ c , pend o , subscribing , p ⟩
reach-pend c empty                           p i = within tt λ { refl → sub-empty c p }
reach-pend c (of xs)                         p i = within tt λ { refl → sub-of c xs p }
reach-pend c (map f s)                       p i = within tt λ { refl → sub-map c f s p }
reach-pend c (flatMap (mergeᶠ nothing) f s)  p i = within tt λ { refl → sub-merge c f s p }
reach-pend c (connected x)                   p i = ⊥-elim (unbound c (proj₁ (good-split c _ (good i))) x)
reach-pend c (cold x)                        p i = beyond (beyond-cold c x p i)
reach-pend c (scan f z s)                    p i = beyond (beyond-scan c f z s p i)
reach-pend c (takeWhile b q s)               p i = beyond (beyond-take c b q s p i)
reach-pend c (flatMap (mergeᶠ (just m)) f s) p i = beyond (beyond-bounded c m f s p i)
reach-pend c (flatMap switchᶠ f s)           p i = beyond (beyond-switch c f s p i)
reach-pend c (flatMap exhaustᶠ f s)          p i = beyond (beyond-exhaust c f s p i)
reach-pend c (connect s b)                   p i = beyond (beyond-connect c s b p i)
reach-pend c (defer l)                       p i = beyond (beyond-defer c l p i)

reach : ∀ {R} (k : Conf R) → Inv k → Reach k
reach ⟨ c , s , rising e , p ⟩                        i = within (rise-mv c s e p) (rise-sim c s e p)
reach ⟨ c , pend o , subscribing , p ⟩                i = reach-pend c o p i
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
reach ⟨ c , s , absorbed , p ⟩                        i = within (abs-mv c s p i) (abs-sim c s p)

sound-from : ∀ {R} {k : Conf R} → Inv k → Runs k
sound-from {k = k} i st with reach k i
... | beyond b      = b st
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
sound {o = o} st = met-of-shown {o = o} (sound-from (inv tt₁ (tt , tt , tt , λ ())) st)
