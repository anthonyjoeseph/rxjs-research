{-# OPTIONS --guardedness #-}

-- EVERY STEP KEEPS THE GHOST'S SCOPE (`ghost-next`): each subscribed
-- source's and each lane's shut view `Sane`/`Placed`, each live joiner
-- told (`adequacy.Engine.Scope.Gh`).  Dispatched as the step is: by
-- mode, then by the frame a rise passes or the node a mark runs.  A step
-- that rewrites no node leaves the tree as it was.
module adequacy.Engine.Ghosted where

open import Data.Bool using (true; false)
open import Data.List using (_∷_; _ʳ++_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (pred)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Unit using (⊤; tt)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import Tree using (Obs)
open import denotation.MonotonicList.Events using (Timeline)
open import adequacy.Engine.Head using (Frag)
open import adequacy.Engine.Pick using (Order; module Order; whole)
open import adequacy.Engine.Scope using (Gh)
open import adequacy.Engine.Fold using (Base; Owns; Wf; WfC; wfI; wf-split; owned; search-hit;
  ofO; attO; cpO; cutO; bodyO; srcAttO; owedO; joinO; leafO)
open import operation.PureObservable using (module Machine; module Driver)
open Machine using (St; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
  Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody; plug;
  CS; free; cpAt; cutAt; overAt; nx; cp; Ev;
  Conf; ⟨_,_,_,_⟩; subscribing; absorbed; rising;
  Mark; ofM; attM; bodyM; srcAttM; owedM; cpM; cutM; joinM; leafM; search; found;
  rise; run; begin; admit; dequeue; ended; alive; feed)

module _ {R : Set} where
  open Driver R using (Step; silent; value; complete; drained; step; took)

  NextGhost : Step → Set
  NextGhost (silent t k)    = Gh top (whole k)
  NextGhost (value t p a k) = Gh top (whole k)
  NextGhost (complete p)    = ⊤
  NextGhost drained         = ⊤

  -- What a mark run reads of the tree it runs in.
  Ghostly : ∀ {Γ A} → Ctx R Γ A → St Γ A → Set
  Ghostly c s = Frag (plug c s) × Gh top (plug c s) × WfC c × Wf s

  postulate
    -- THE SCOPE: a rise through a frame that rewrites its node keeps the
    -- ghost's scope: a scan's running total, a takeWhile failing a value,
    -- an outer's value admitted or its end, a lane's end, a source's
    -- value or end fed its body, a body's end owed.
    scan-ghost : ∀ {Γ A B} (c : Ctx R Γ B) (f : B → A → B) z (s : St Γ A) a p
               → Base ⟨ inScan f z c , s , rising (nx a) , p ⟩ → Order ⟨ inScan f z c , s , rising (nx a) , p ⟩
               → Gh top (plug c (scanS f (f z a) s))
    take-fail-ghost : ∀ {Γ A} (c : Ctx R Γ A) i q (s : St Γ A) a p → q a ≡ false
                    → Base ⟨ inTake i q free c , s , rising (nx a) , p ⟩ → Order ⟨ inTake i q free c , s , rising (nx a) , p ⟩
                    → Gh top (plug c (takeS i q (cpAt p) s))
    admit-ghost : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q ls (o : St Γ A) a p
                → Base ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩ → Order ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩
                → NextGhost (took (admit c op f d n q o ls a p))
    outer-end-ghost : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) n q ls (o : St Γ A) p
                    → Base ⟨ inOuter op f false n q ls c , o , rising cp , p ⟩ → Order ⟨ inOuter op f false n q ls c , o , rising cp , p ⟩
                    → Gh top (plug c (flatS op f true n q o ls))
    lane-end-ghost : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) pre post (s : St Γ B) p → alive s ≡ true
                   → Base ⟨ inLanes op f d n q o pre post c , s , rising cp , p ⟩ → Order ⟨ inLanes op f d n q o pre post c , s , rising cp , p ⟩
                   → Gh top (whole (dequeue c op f d (pred n) q o (pre ʳ++ ended s ∷ post) p))
    src-value-ghost : ∀ {Γ X B} (c : Ctx R Γ B) k (b : St (X ∷ Γ) B) (s : St Γ X) a p
                    → Base ⟨ inSrc k b c , s , rising (nx a) , p ⟩ → Order ⟨ inSrc k b c , s , rising (nx a) , p ⟩
                    → Gh top (plug c (connS k s (feed (here refl) p (nx a) b)))
    src-end-ghost : ∀ {Γ X B} (c : Ctx R Γ B) k (b : St (X ∷ Γ) B) (s : St Γ X) p
                  → Base ⟨ inSrc k b c , s , rising cp , p ⟩ → Order ⟨ inSrc k b c , s , rising cp , p ⟩
                  → Gh top (plug c (connS (record k { closed = true ; endAt = p }) s (feed (here refl) p cp b)))
    body-end-ghost : ∀ {Γ X B} (c : Ctx R Γ B) k (o : St Γ X) (s : St (X ∷ Γ) B) p
                   → Base ⟨ inBody k o c , s , rising cp , p ⟩ → Order ⟨ inBody k o c , s , rising cp , p ⟩
                   → Gh top (plug c (connS (record k { owedAt = just p }) o s))
    -- THE SCOPE: a subscribe keeps the ghost's scope.
    begin-ghost : ∀ {Γ A} (c : Ctx R Γ A) (o : Obs Timeline Γ A) p
                → Base ⟨ c , pend o , subscribing , p ⟩ → Order ⟨ c , pend o , subscribing , p ⟩
                → NextGhost (took (begin c o p))
    -- THE SCOPE: a mark run keeps the ghost's scope, by the mark.
    of-ghost      : ∀ {Γ A} (c : Ctx R Γ A) {s : St Γ A} p → Owns s ofM    → Ghostly c s → NextGhost (took (run c s ofM p))
    att-ghost     : ∀ {Γ A} (c : Ctx R Γ A) {s : St Γ A} p → Owns s attM   → Ghostly c s → NextGhost (took (run c s attM p))
    cp-ghost      : ∀ {Γ A} (c : Ctx R Γ A) {s : St Γ A} p → Owns s cpM    → Ghostly c s → NextGhost (took (run c s cpM p))
    cut-ghost     : ∀ {Γ A} (c : Ctx R Γ A) {s : St Γ A} p → Owns s cutM   → Ghostly c s → NextGhost (took (run c s cutM p))
    body-ghost    : ∀ {Γ A} (c : Ctx R Γ A) {s : St Γ A} p → Owns s bodyM  → Ghostly c s → NextGhost (took (run c s bodyM p))
    srcAtt-ghost  : ∀ {Γ A} (c : Ctx R Γ A) {s : St Γ A} p → Owns s srcAttM → Ghostly c s → NextGhost (took (run c s srcAttM p))
    owed-ghost    : ∀ {Γ A} (c : Ctx R Γ A) {s : St Γ A} p → Owns s owedM  → Ghostly c s → NextGhost (took (run c s owedM p))
    join-ghost    : ∀ {Γ A} (c : Ctx R Γ A) {s : St Γ A} p → Owns s joinM  → Ghostly c s → NextGhost (took (run c s joinM p))
    leaf-ghost    : ∀ {Γ A} (c : Ctx R Γ A) {s : St Γ A} p → Owns s leafM  → Ghostly c s → NextGhost (took (run c s leafM p))

  -- A rise, by the frame it passes; one rewriting no node keeps the tree.
  rise-ghost : ∀ {Γ A} (c : Ctx R Γ A) (s : St Γ A) e p → Base ⟨ c , s , rising e , p ⟩ → Order ⟨ c , s , rising e , p ⟩
             → NextGhost (took (rise c s e p))
  rise-ghost top                               s (nx a) p b o = Order.ghosted o
  rise-ghost top                               s cp     p b o = tt
  rise-ghost (inMap f c)                       s e      p b o = Order.ghosted o
  rise-ghost (inScan f z c)                    s (nx a) p b o = scan-ghost c f z s a p b o
  rise-ghost (inScan f z c)                    s cp     p b o = Order.ghosted o
  rise-ghost (inCut true a c)                  s e      p b o = Order.ghosted o
  rise-ghost (inCut false a c)                 s e      p b o = Order.ghosted o
  rise-ghost (inLn l c)                        s e      p b o = Order.ghosted o
  rise-ghost (inTake i q free c)               s (nx a) p b o with q a in e | i
  ... | true  | _     = Order.ghosted o
  ... | false | true  = take-fail-ghost c true q s a p e b o
  ... | false | false = take-fail-ghost c false q s a p e b o
  rise-ghost (inTake i q free c)               s cp     p b o = Order.ghosted o
  rise-ghost (inTake i q (cpAt r) c)           s e      p b o = Order.ghosted o
  rise-ghost (inTake i q (cutAt r) c)          s e      p b o = Order.ghosted o
  rise-ghost (inTake i q (overAt r) c)         s e      p b o = Order.ghosted o
  rise-ghost (inOuter op f d n q ls c)         s (nx a) p b o = admit-ghost c op f d n q ls s a p b o
  rise-ghost (inOuter op f true n q ls c)      s cp     p b o = Order.ghosted o
  rise-ghost (inOuter op f false n q ls c)     s cp     p b o = outer-end-ghost c op f n q ls s p b o
  rise-ghost (inLanes op f d n q o′ pre post c) s (nx x) p b o with alive s
  ... | true  = Order.ghosted o
  ... | false = Order.ghosted o
  rise-ghost (inLanes op f d n q o′ pre post c) s cp     p b o with alive s in al
  ... | true  = lane-end-ghost c op f d n q o′ pre post s p al b o
  ... | false = Order.ghosted o
  rise-ghost (inSrc k b′ c)                    s (nx a) p b o = src-value-ghost c k b′ s a p b o
  rise-ghost (inSrc k b′ c)                    s cp     p b o = src-end-ghost c k b′ s p b o
  rise-ghost (inBody k o′ c)                   s (nx x) p b o = Order.ghosted o
  rise-ghost (inBody k o′ c)                   s cp     p b o = body-end-ghost c k o′ s p b o

  -- A subscribe of a settled node leaves the tree as it was.
  sub-ghost : ∀ {Γ A} (c : Ctx R Γ A) (s : St Γ A) p → Base ⟨ c , s , subscribing , p ⟩ → Order ⟨ c , s , subscribing , p ⟩
            → NextGhost (step ⟨ c , s , subscribing , p ⟩)
  sub-ghost c (pend x)                p b o = begin-ghost c x p b o
  sub-ghost c (coldS x y)             p b o = Order.ghosted o
  sub-ghost c (ofS x y z)             p b o = Order.ghosted o
  sub-ghost c doneS                   p b o = Order.ghosted o
  sub-ghost c (mapS x y)              p b o = Order.ghosted o
  sub-ghost c (scanS x y z)           p b o = Order.ghosted o
  sub-ghost c (cutS x y z)            p b o = Order.ghosted o
  sub-ghost c (lnS x y)               p b o = Order.ghosted o
  sub-ghost c (takeS x y z w)         p b o = Order.ghosted o
  sub-ghost c (flatS x y z w u v t)   p b o = Order.ghosted o
  sub-ghost c (connS x y z)           p b o = Order.ghosted o
  sub-ghost c (joinS x y z w)         p b o = Order.ghosted o

  -- A mark run, by the node that owns it.
  run-ghost : ∀ {Γ A} (c : Ctx R Γ A) {s : St Γ A} {m} p → Owns s m → Ghostly c s → NextGhost (took (run c s m p))
  run-ghost c p w@ofO         g = of-ghost c p w g
  run-ghost c p w@attO        g = att-ghost c p w g
  run-ghost c p w@cpO         g = cp-ghost c p w g
  run-ghost c p w@cutO        g = cut-ghost c p w g
  run-ghost c p w@(bodyO _)   g = body-ghost c p w g
  run-ghost c p w@(srcAttO _) g = srcAtt-ghost c p w g
  run-ghost c p w@(owedO _)   g = owed-ghost c p w g
  run-ghost c p w@joinO       g = join-ghost c p w g
  run-ghost c p w@(leafO _)   g = leaf-ghost c p w g

  -- THE SOURCES KEPT: a step keeps every subscribed connect's source and
  -- every lane, read through the ended connects in scope, placed in the
  -- environment its frame reads, and every live joiner told.
  ghost-next : ∀ k → Base k → Order k → NextGhost (step k)
  ghost-next ⟨ c , s , rising e , p ⟩    b o = rise-ghost c s e p b o
  ghost-next ⟨ c , s , subscribing , p ⟩ b o = sub-ghost c s p b o
  ghost-next ⟨ c , s , absorbed , p ⟩    b o with search top (plug c s) in e
  ... | nothing = tt
  ... | just (found (_ , _ , c′ , s′) m key) with search-hit (plug c s) e
  ...   | pl , own with wf-split c′ s′ (owned own) (subst Wf (sym pl) (wfI b))
  ...     | v′ , w′ = run-ghost c′ p own
                        (subst Frag (sym pl) (proj₁ (Order.shape o)) , subst (Gh top) (sym pl) (Order.ghosted o) , v′ , w′)
