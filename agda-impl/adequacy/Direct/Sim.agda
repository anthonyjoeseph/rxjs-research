{-# OPTIONS --guardedness #-}

-- THE DIRECT LINK, FOR A FRAGMENT WITHOUT `defer`: the engine run against
-- the emission set's rows, with no stepper and no tower between them.  A
-- step keeps the visible rows or shows the least and drops it, by mode: a
-- subscription entered as the rows of what it begins, a rise read up one
-- frame, a mark run where the search's bound says it leads.
module adequacy.Direct.Sim where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; null)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Tree using (Obs; mergeᶠ; switchᶠ; exhaustᶠ; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.MonotonicList.Events using (Pos; Timeline; root)
open import denotation.EmissionSet using (EmissionSet; out; end; MapT; map-out; map-skip; map-end; _≺_; _≼_; enter; ⟦_⟧ᵀ)
open import denotation.EmissionSet.Laws.Modulus using (≺-irrefl; ≺-absurd)
open import operation.Key using (Key)
open import operation.PureObservable using (PureObs; module Machine)
open Machine using (St; Ctx; Conf; ⟨_,_,_,_⟩; subscribing; absorbed; rising; load; moved; plug; search; found; Mark; ofM; attM;
                    rise; run; start; dequeue; settle; alive; ended; mapEv; nx; cp; attAt; attached; Torn;
                    pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
                    top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody)
                    renaming (Ev to Evᴹ; Shown to Shownᴹ; step to stepᴹ)
open import adequacy.Direct using (Frag; rows; up; RT; here; pendRows; toEv; Visible; Vis; Past; Plus; old; new; _≃_; _⇄_; Moves; silent; shown;
                                   Steps; Shows*; Shows*-≃; ≃-sym; conv; []; _∷_)
open import adequacy.Direct.Bound using (Good; GoodLn)
open import adequacy.Direct.Up using (up-≃; ≃-refl)

------------------------------------------------------------------------
-- The invariant

-- A rising event leads: everything else still owed lies strictly past it.
Lead : ∀ {R} → Conf R → Set
Lead ⟨ c , s , rising e , p ⟩ = ∀ {q e′} → Vis (up c (rows s)) q e′ → p ≺ q
Lead _                         = ⊤

record Inv {R} (k : Conf R) : Set where
  constructor inv
  field
    good : Good (plug (Conf.ctx k) (Conf.foc k))
    lead : Lead k
open Inv

-- The frames the fragment builds.
GoodC : ∀ {R Γ A} → Ctx R Γ A → Set
GoodC top                                          = ⊤
GoodC (inMap f c)                                  = GoodC c
GoodC (inCut l a c)                                = GoodC c
GoodC (inLn b c)                                   = GoodC c
GoodC (inOuter (mergeᶠ nothing) f d n q ls c)      = GoodC c
GoodC (inLanes (mergeᶠ nothing) f d n q o pre post c) = GoodC c
GoodC _                                            = ⊥

-- One step against the rows, the invariant kept.
Sim : ∀ {R} → Conf R → Shownᴹ R → Conf R → Set₁
Sim k sh k′ = Inv k → Inv k′ × Moves (RT k) sh (RT k′)

-- What a frame's hole must be: under a merge's lanes, a lane.
GoodF : ∀ {R Γ A} → Ctx R Γ A → St Γ A → Set
GoodF (inLanes op f d n q o pre post c) s = GoodLn s
GoodF top                s = Good s
GoodF (inMap f c)        s = Good s
GoodF (inScan f z c)     s = Good s
GoodF (inCut l a c)      s = Good s
GoodF (inLn b c)         s = Good s
GoodF (inTake i q w c)   s = Good s
GoodF (inOuter op f d n q ls c) s = Good s
GoodF (inSrc k b c)      s = Good s
GoodF (inBody k o c)     s = Good s

pend-good : ∀ {R Γ A} (c : Ctx R Γ A) o → GoodF c (pend o) → Frag o
pend-good (inLanes op f d n q o′ pre post c) o ()
pend-good top                o g = g
pend-good (inMap f c)        o g = g
pend-good (inScan f z c)     o g = g
pend-good (inCut l a c)      o g = g
pend-good (inLn b c)         o g = g
pend-good (inTake i q w c)   o g = g
pend-good (inOuter op f d n q ls c) o g = g
pend-good (inSrc k b c)      o g = g
pend-good (inBody k o′ c)    o g = g

-- Only a lane is ever out of its list.
dead-bad : ∀ {Γ A} (s : St Γ A) → alive s ≡ false → Good s → ⊥
dead-bad (lnS b s) _ ()

postulate
  -- A GOOD TREE, CUT AT A HOLE: good frames, a good focus.
  good-split : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) → Good (plug c s) → GoodC c × GoodF c s

------------------------------------------------------------------------
-- Subscribing

postulate
  sub-empty : ∀ {R Γ A} (c : Ctx R Γ A) p → Sim ⟨ c , pend empty , subscribing , p ⟩ [] ⟨ c , ofS 0 p [] , absorbed , p ⟩
  sub-of    : ∀ {R Γ A} (c : Ctx R Γ A) xs p → Sim ⟨ c , pend (of xs) , subscribing , p ⟩ [] ⟨ c , ofS 0 p xs , absorbed , p ⟩
  sub-map   : ∀ {R Γ A B} (c : Ctx R Γ B) (f : A → B) s p → Sim ⟨ c , pend (map f s) , subscribing , p ⟩ [] ⟨ inMap f c , pend s , subscribing , p ⟩
  sub-merge : ∀ {R Γ A B} (c : Ctx R Γ B) f (s : Obs Timeline Γ A) p
            → Sim ⟨ c , pend (flatMap (mergeᶠ nothing) f s) , subscribing , p ⟩ [] ⟨ inCut true (attAt p) (inOuter (mergeᶠ nothing) f false 0 [] [] c) , pend s , subscribing , p ⟩

stay : ∀ {R} {k : Conf R} → Sim k [] k
stay i = i , silent ((λ x → x) ⇄ (λ x → x))

sub-sim : ∀ {R Γ A} {k′ : Conf R} {sh t} (c : Ctx R Γ A) (s : St Γ A) p → stepᴹ ⟨ c , s , subscribing , p ⟩ ≡ moved k′ sh t → Sim ⟨ c , s , subscribing , p ⟩ sh k′
sub-sim c (pend empty)                          p refl = sub-empty c p
sub-sim c (pend (of xs))                        p refl = sub-of c xs p
sub-sim c (pend (map f s))                      p refl = sub-map c f s p
sub-sim c (pend (flatMap (mergeᶠ nothing) f s)) p refl = sub-merge c f s p
sub-sim c (pend (cold x))                       p eq i = ⊥-elim (pend-good c _ (proj₂ (good-split c _ (good i))))
sub-sim c (pend (scan f z s))                   p eq i = ⊥-elim (pend-good c _ (proj₂ (good-split c _ (good i))))
sub-sim c (pend (takeWhile b q s))              p eq i = ⊥-elim (pend-good c _ (proj₂ (good-split c _ (good i))))
sub-sim c (pend (flatMap (mergeᶠ (just m)) f s)) p eq i = ⊥-elim (pend-good c _ (proj₂ (good-split c _ (good i))))
sub-sim c (pend (flatMap switchᶠ f s))          p eq i = ⊥-elim (pend-good c _ (proj₂ (good-split c _ (good i))))
sub-sim c (pend (flatMap exhaustᶠ f s))         p eq i = ⊥-elim (pend-good c _ (proj₂ (good-split c _ (good i))))
sub-sim c (pend (connect s b))                  p eq i = ⊥-elim (pend-good c _ (proj₂ (good-split c _ (good i))))
sub-sim c (pend (connected x))                  p eq i = ⊥-elim (pend-good c _ (proj₂ (good-split c _ (good i))))
sub-sim c (pend (defer l))                      p eq i = ⊥-elim (pend-good c _ (proj₂ (good-split c _ (good i))))
sub-sim c (coldS b l)       p refl = stay
sub-sim c (ofS i q xs)      p refl = stay
sub-sim c doneS             p refl = stay
sub-sim c (mapS f s)        p refl = stay
sub-sim c (scanS f z s)     p refl = stay
sub-sim c (cutS l a s)      p refl = stay
sub-sim c (lnS b s)         p refl = stay
sub-sim c (takeS i q w s)   p refl = stay
sub-sim c (flatS op f d n q o ls) p refl = stay
sub-sim c (connS k o b)     p refl = stay
sub-sim c (joinS j g x ib)  p refl = stay

------------------------------------------------------------------------
-- Rising

-- At the root: the event shown, the least row, and dropped.
rise-top : ∀ {R} (s : St [] R) e p → Sim ⟨ top , s , rising e , p ⟩ [ (p , e) ] ⟨ top , s , absorbed , p ⟩
rise-top s e p i with alive s in al
rise-top s e p (inv g ld) | false = ⊥-elim (dead-bad s al g)
rise-top s e p (inv g ld) | true = inv g tt , shown (new , vis e) least (to′ ⇄ from′)
  where
    vis : ∀ e → Visible (toEv e)
    vis (nx _) = tt
    vis cp     = tt
    least : ∀ {q e′} → Vis (Plus (rows s) p (toEv e)) q e′ → p ≼ q
    least {q} (old r , v) qp = ≺-absurd {q} {p} qp (ld (r , v))
    least (new , v)       qp = ≺-irrefl {p} qp
    to′ : ∀ {q e′} → Vis (Past p (Plus (rows s) p (toEv e))) q e′ → Vis (rows s) q e′
    to′ ((old r , _) , v) = r , v
    to′ ((new , pp) , v)  = ⊥-elim (≺-irrefl {p} pp)
    from′ : ∀ {q e′} → Vis (rows s) q e′ → Vis (Past p (Plus (rows s) p (toEv e))) q e′
    from′ (r , v) = (old r , ld (r , v)) , v

-- A hole's rows, good either way.
unF : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) → GoodF c s → Good s ⊎ GoodLn s
unF (inLanes op f d n q o pre post c) s g = inj₂ g
unF top                s g = inj₁ g
unF (inMap f c)        s g = inj₁ g
unF (inScan f z c)     s g = inj₁ g
unF (inCut l a c)      s g = inj₁ g
unF (inLn b c)         s g = inj₁ g
unF (inTake i q w c)   s g = inj₁ g
unF (inOuter op f d n q ls c) s g = inj₁ g
unF (inSrc k b c)      s g = inj₁ g
unF (inBody k o c)     s g = inj₁ g

vis-≃ : ∀ {A} {t u : EmissionSet A} → t ≃ u → Vis t ≃ Vis u
vis-≃ eq = (λ { (r , v) → to eq r , v }) ⇄ (λ { (r , v) → from eq r , v })
  where open _≃_

map-plus : ∀ {A B} (f : A → B) (t : EmissionSet A) p e → MapT f (Plus t p (toEv e)) ≃ Plus (MapT f t) p (toEv (mapEv f e))
map-plus f t p (nx a) = to′ ⇄ from′
  where
    to′ : ∀ {q e′} → MapT f (Plus t p (out a)) q e′ → Plus (MapT f t) p (out (f a)) q e′
    to′ (map-out (old r))  = old (map-out r)
    to′ (map-out new)      = new
    to′ (map-skip (old r)) = old (map-skip r)
    to′ (map-end (old r))  = old (map-end r)
    from′ : ∀ {q e′} → Plus (MapT f t) p (out (f a)) q e′ → MapT f (Plus t p (out a)) q e′
    from′ (old (map-out r))  = map-out (old r)
    from′ (old (map-skip r)) = map-skip (old r)
    from′ (old (map-end r))  = map-end (old r)
    from′ new                = map-out new
map-plus f t p cp = to′ ⇄ from′
  where
    to′ : ∀ {q e′} → MapT f (Plus t p end) q e′ → Plus (MapT f t) p end q e′
    to′ (map-out (old r))  = old (map-out r)
    to′ (map-skip (old r)) = old (map-skip r)
    to′ (map-end (old r))  = old (map-end r)
    to′ (map-end new)      = new
    from′ : ∀ {q e′} → Plus (MapT f t) p end q e′ → MapT f (Plus t p end) q e′
    from′ (old (map-out r))  = map-out (old r)
    from′ (old (map-skip r)) = map-skip (old r)
    from′ (old (map-end r))  = map-end (old r)
    from′ new                = map-end new

rise-map : ∀ {R Γ A B} (f : A → B) (c : Ctx R Γ B) s e p → Sim ⟨ inMap f c , s , rising e , p ⟩ [] ⟨ c , mapS f s , rising (mapEv f e) , p ⟩
rise-map f c s e p i with alive s in al
rise-map f c s e p (inv g ld) | false with unF c (mapS f s) (proj₂ (good-split c (mapS f s) g))
... | inj₁ gs = ⊥-elim (dead-bad s al gs)
rise-map f c s e p (inv g ld) | true = inv g ld , silent (vis-≃ (up-≃ c (map-plus f (rows s) p e)))

rise-cut : ∀ {R Γ A} l a (c : Ctx R Γ A) s e p → Sim ⟨ inCut l a c , s , rising e , p ⟩ [] ⟨ c , cutS l a s , (if l then rising e else absorbed) , p ⟩
rise-cut false a c s e p (inv g ld) = inv g tt , silent ≃-refl
rise-cut true  a c s e p i with alive s in al
rise-cut true  a c s e p (inv g ld) | false = ⊥-elim (dead-bad s al (proj₂ (good-split (inCut true a c) s g)))
rise-cut true  a c s e p (inv g ld) | true  = inv g ld , silent ≃-refl

rise-ln : ∀ {R Γ A} b (c : Ctx R Γ A) s e p → Sim ⟨ inLn b c , s , rising e , p ⟩ [] ⟨ c , lnS b s , rising e , p ⟩
rise-ln false c s e p (inv g ld) = inv g ld , silent ≃-refl
rise-ln true  c s e p i with alive s in al
rise-ln true  c s e p (inv g ld) | false = ⊥-elim (dead-bad s al (proj₂ (good-split (inLn true c) s g)))
rise-ln true  c s e p (inv g ld) | true  = inv g ld , silent ≃-refl

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
  -- A LANE'S END, SHOWN ONLY AS THE LAST WITH THE OUTER DONE.
  rise-lane-cp : ∀ {R Γ A B} f d n q (o : St Γ A) pre post (c : Ctx R Γ B) s p
               → Sim ⟨ inLanes (mergeᶠ nothing) f d n q o pre post c , s , rising cp , p ⟩ []
                     (if alive s then dequeue c (mergeᶠ nothing) f d (Data.Nat.pred n) q o (pre Data.List.ʳ++ ended s ∷ post) p
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

-- The marks the fragment's nodes own.
data Marked {Γ : List Set} : ∀ {A} → St Γ A → Mark → Set₁ where
  ofK  : ∀ {A} i p (xs : List A) → Marked (ofS i p xs) ofM
  attK : ∀ {A} l p (s : St Γ A) → Marked (cutS l (attAt p) s) attM

postulate
  -- WHAT A GOOD TREE'S SEARCH FINDS: an of's next, or a switch's attach.
  found-mark : ∀ {R Γ′ A′} (c : Ctx R Γ′ A′) s {Γ A c′ s′ m κ} → Good (plug c s) → search top (plug c s) ≡ just (found (Γ , A , c′ , s′) m κ) → Marked s′ m

  -- AN OF'S NEXT RUN: the least row, risen.
  abs-of : ∀ {R Γ′ A′ Γ A} {c : Ctx R Γ′ A′} {s} {c′ : Ctx R Γ A} {i p₀ xs κ k′ sh t} p
         → search top (plug c s) ≡ just (found (Γ , A , c′ , ofS i p₀ xs) ofM κ) → run c′ (ofS i p₀ xs) ofM p ≡ moved k′ sh t
         → Sim ⟨ c , s , absorbed , p ⟩ sh k′
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
-- The run

step-sim : ∀ {R} {k k′ : Conf R} {sh t} → stepᴹ k ≡ moved k′ sh t → Sim k sh k′
step-sim {k = ⟨ c , s , rising e , p ⟩}   eq = rise-sim c s e p eq
step-sim {k = ⟨ c , s , subscribing , p ⟩} eq = sub-sim c s p eq
step-sim {k = ⟨ c , s , absorbed , p ⟩}    eq = abs-sim c s p eq

sound-from : ∀ {R} {k k′ : Conf R} {rs} → Inv k → Steps k rs k′ → Shows* (RT k) (conv rs)
sound-from i [] = []
sound-from i (e ∷ st) with step-sim e i
... | i′ , silent eq        = Shows*-≃ (≃-sym eq) (sound-from i′ st)
... | i′ , shown v lt eq    = (v , lt) ∷ Shows*-≃ (≃-sym eq) (sound-from i′ st)

-- THE SOUND HALF: what the engine shows, a reader of the program's rows
-- is shown.
sound : ∀ {R} {o : PureObs [] R} → Frag o → ∀ {rs k} → Steps (load o) rs k → Shows* (enter (⟦ o ⟧ᵀ []ᴬ) root) (conv rs)
sound fo st = sound-from (inv fo tt) st
