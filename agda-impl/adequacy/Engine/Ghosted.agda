{-# OPTIONS --guardedness #-}

-- EVERY STEP KEEPS THE TOLD FACT (`told-next`): every joiner the shut
-- view sees is told of its source's end (`Toldˢ none`).  The ghost's
-- scope is derived from it where the tree is keyed
-- (`adequacy.Engine.Firmed.gh-firm`).  Dispatched as the step is: by
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
open import adequacy.Engine.Shuts using (Toldˢ; none)
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

  NextTold : Step → Set
  NextTold (silent t k)    = Toldˢ none (whole k)
  NextTold (value t p a k) = Toldˢ none (whole k)
  NextTold (complete p)    = ⊤
  NextTold drained         = ⊤

  -- What a mark run reads of the tree it runs in.
  Tolds : ∀ {Γ A} → Ctx R Γ A → St Γ A → Set
  Tolds c s = Frag (plug c s) × Toldˢ none (plug c s) × WfC c × Wf s

  postulate
    -- THE SCOPE: a rise through a frame that rewrites its node keeps the
    -- ghost's scope: a scan's running total, a takeWhile failing a value,
    -- an outer's value admitted or its end, a lane's end, a source's
    -- value or end fed its body, a body's end owed.
    scan-told : ∀ {Γ A B} (c : Ctx R Γ B) (f : B → A → B) z (s : St Γ A) a p
               → Base ⟨ inScan f z c , s , rising (nx a) , p ⟩ → Order ⟨ inScan f z c , s , rising (nx a) , p ⟩
               → Toldˢ none (plug c (scanS f (f z a) s))
    take-fail-told : ∀ {Γ A} (c : Ctx R Γ A) i q (s : St Γ A) a p → q a ≡ false
                    → Base ⟨ inTake i q free c , s , rising (nx a) , p ⟩ → Order ⟨ inTake i q free c , s , rising (nx a) , p ⟩
                    → Toldˢ none (plug c (takeS i q (cpAt p) s))
    admit-told : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q ls (o : St Γ A) a p
                → Base ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩ → Order ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩
                → NextTold (took (admit c op f d n q o ls a p))
    outer-end-told : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) n q ls (o : St Γ A) p
                    → Base ⟨ inOuter op f false n q ls c , o , rising cp , p ⟩ → Order ⟨ inOuter op f false n q ls c , o , rising cp , p ⟩
                    → Toldˢ none (plug c (flatS op f true n q o ls))
    lane-end-told : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) pre post (s : St Γ B) p → alive s ≡ true
                   → Base ⟨ inLanes op f d n q o pre post c , s , rising cp , p ⟩ → Order ⟨ inLanes op f d n q o pre post c , s , rising cp , p ⟩
                   → Toldˢ none (whole (dequeue c op f d (pred n) q o (pre ʳ++ ended s ∷ post) p))
    src-value-told : ∀ {Γ X B} (c : Ctx R Γ B) k (b : St (X ∷ Γ) B) (s : St Γ X) a p
                    → Base ⟨ inSrc k b c , s , rising (nx a) , p ⟩ → Order ⟨ inSrc k b c , s , rising (nx a) , p ⟩
                    → Toldˢ none (plug c (connS k s (feed (here refl) p (nx a) b)))
    src-end-told : ∀ {Γ X B} (c : Ctx R Γ B) k (b : St (X ∷ Γ) B) (s : St Γ X) p
                  → Base ⟨ inSrc k b c , s , rising cp , p ⟩ → Order ⟨ inSrc k b c , s , rising cp , p ⟩
                  → Toldˢ none (plug c (connS (record k { closed = true ; endAt = p }) s (feed (here refl) p cp b)))
    body-end-told : ∀ {Γ X B} (c : Ctx R Γ B) k (o : St Γ X) (s : St (X ∷ Γ) B) p
                   → Base ⟨ inBody k o c , s , rising cp , p ⟩ → Order ⟨ inBody k o c , s , rising cp , p ⟩
                   → Toldˢ none (plug c (connS (record k { owedAt = just p }) o s))
    -- THE SCOPE: a subscribe keeps the ghost's scope.
    begin-told : ∀ {Γ A} (c : Ctx R Γ A) (o : Obs Timeline Γ A) p
                → Base ⟨ c , pend o , subscribing , p ⟩ → Order ⟨ c , pend o , subscribing , p ⟩
                → NextTold (took (begin c o p))
    -- THE SCOPE: a mark run keeps the ghost's scope, by the mark.
    of-told      : ∀ {Γ A} (c : Ctx R Γ A) {s : St Γ A} p → Owns s ofM    → Tolds c s → NextTold (took (run c s ofM p))
    att-told     : ∀ {Γ A} (c : Ctx R Γ A) {s : St Γ A} p → Owns s attM   → Tolds c s → NextTold (took (run c s attM p))
    cp-told      : ∀ {Γ A} (c : Ctx R Γ A) {s : St Γ A} p → Owns s cpM    → Tolds c s → NextTold (took (run c s cpM p))
    cut-told     : ∀ {Γ A} (c : Ctx R Γ A) {s : St Γ A} p → Owns s cutM   → Tolds c s → NextTold (took (run c s cutM p))
    body-told    : ∀ {Γ A} (c : Ctx R Γ A) {s : St Γ A} p → Owns s bodyM  → Tolds c s → NextTold (took (run c s bodyM p))
    srcAtt-told  : ∀ {Γ A} (c : Ctx R Γ A) {s : St Γ A} p → Owns s srcAttM → Tolds c s → NextTold (took (run c s srcAttM p))
    owed-told    : ∀ {Γ A} (c : Ctx R Γ A) {s : St Γ A} p → Owns s owedM  → Tolds c s → NextTold (took (run c s owedM p))
    join-told    : ∀ {Γ A} (c : Ctx R Γ A) {s : St Γ A} p → Owns s joinM  → Tolds c s → NextTold (took (run c s joinM p))
    leaf-told    : ∀ {Γ A} (c : Ctx R Γ A) {s : St Γ A} p → Owns s leafM  → Tolds c s → NextTold (took (run c s leafM p))

  -- A rise, by the frame it passes; one rewriting no node keeps the tree.
  rise-told : ∀ {Γ A} (c : Ctx R Γ A) (s : St Γ A) e p → Base ⟨ c , s , rising e , p ⟩ → Order ⟨ c , s , rising e , p ⟩
             → NextTold (took (rise c s e p))
  rise-told top                               s (nx a) p b o = Order.told o
  rise-told top                               s cp     p b o = tt
  rise-told (inMap f c)                       s e      p b o = Order.told o
  rise-told (inScan f z c)                    s (nx a) p b o = scan-told c f z s a p b o
  rise-told (inScan f z c)                    s cp     p b o = Order.told o
  rise-told (inCut true a c)                  s e      p b o = Order.told o
  rise-told (inCut false a c)                 s e      p b o = Order.told o
  rise-told (inLn l c)                        s e      p b o = Order.told o
  rise-told (inTake i q free c)               s (nx a) p b o with q a in e | i
  ... | true  | _     = Order.told o
  ... | false | true  = take-fail-told c true q s a p e b o
  ... | false | false = take-fail-told c false q s a p e b o
  rise-told (inTake i q free c)               s cp     p b o = Order.told o
  rise-told (inTake i q (cpAt r) c)           s e      p b o = Order.told o
  rise-told (inTake i q (cutAt r) c)          s e      p b o = Order.told o
  rise-told (inTake i q (overAt r) c)         s e      p b o = Order.told o
  rise-told (inOuter op f d n q ls c)         s (nx a) p b o = admit-told c op f d n q ls s a p b o
  rise-told (inOuter op f true n q ls c)      s cp     p b o = Order.told o
  rise-told (inOuter op f false n q ls c)     s cp     p b o = outer-end-told c op f n q ls s p b o
  rise-told (inLanes op f d n q o′ pre post c) s (nx x) p b o with alive s
  ... | true  = Order.told o
  ... | false = Order.told o
  rise-told (inLanes op f d n q o′ pre post c) s cp     p b o with alive s in al
  ... | true  = lane-end-told c op f d n q o′ pre post s p al b o
  ... | false = Order.told o
  rise-told (inSrc k b′ c)                    s (nx a) p b o = src-value-told c k b′ s a p b o
  rise-told (inSrc k b′ c)                    s cp     p b o = src-end-told c k b′ s p b o
  rise-told (inBody k o′ c)                   s (nx x) p b o = Order.told o
  rise-told (inBody k o′ c)                   s cp     p b o = body-end-told c k o′ s p b o

  -- A subscribe of a settled node leaves the tree as it was.
  sub-told : ∀ {Γ A} (c : Ctx R Γ A) (s : St Γ A) p → Base ⟨ c , s , subscribing , p ⟩ → Order ⟨ c , s , subscribing , p ⟩
            → NextTold (step ⟨ c , s , subscribing , p ⟩)
  sub-told c (pend x)                p b o = begin-told c x p b o
  sub-told c (coldS x y)             p b o = Order.told o
  sub-told c (ofS x y z)             p b o = Order.told o
  sub-told c doneS                   p b o = Order.told o
  sub-told c (mapS x y)              p b o = Order.told o
  sub-told c (scanS x y z)           p b o = Order.told o
  sub-told c (cutS x y z)            p b o = Order.told o
  sub-told c (lnS x y)               p b o = Order.told o
  sub-told c (takeS x y z w)         p b o = Order.told o
  sub-told c (flatS x y z w u v t)   p b o = Order.told o
  sub-told c (connS x y z)           p b o = Order.told o
  sub-told c (joinS x y z w)         p b o = Order.told o

  -- A mark run, by the node that owns it.
  run-told : ∀ {Γ A} (c : Ctx R Γ A) {s : St Γ A} {m} p → Owns s m → Tolds c s → NextTold (took (run c s m p))
  run-told c p w@ofO         g = of-told c p w g
  run-told c p w@attO        g = att-told c p w g
  run-told c p w@cpO         g = cp-told c p w g
  run-told c p w@cutO        g = cut-told c p w g
  run-told c p w@(bodyO _)   g = body-told c p w g
  run-told c p w@(srcAttO _) g = srcAtt-told c p w g
  run-told c p w@(owedO _)   g = owed-told c p w g
  run-told c p w@joinO       g = join-told c p w g
  run-told c p w@(leafO _)   g = leaf-told c p w g

  -- THE SOURCES KEPT: a step keeps every subscribed connect's source and
  -- every lane, read through the ended connects in scope, placed in the
  -- environment its frame reads, and every live joiner told.
  told-next : ∀ k → Base k → Order k → NextTold (step k)
  told-next ⟨ c , s , rising e , p ⟩    b o = rise-told c s e p b o
  told-next ⟨ c , s , subscribing , p ⟩ b o = sub-told c s p b o
  told-next ⟨ c , s , absorbed , p ⟩    b o with search top (plug c s) in e
  ... | nothing = tt
  ... | just (found (_ , _ , c′ , s′) m key) with search-hit (plug c s) e
  ...   | pl , own with wf-split c′ s′ (owned own) (subst Wf (sym pl) (wfI b))
  ...     | v′ , w′ = run-told c′ p own
                        (subst Frag (sym pl) (proj₁ (Order.shape o)) , subst (Toldˢ none) (sym pl) (Order.told o) , v′ , w′)
