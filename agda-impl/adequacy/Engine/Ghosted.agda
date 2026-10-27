{-# OPTIONS --guardedness #-}

-- EVERY STEP KEEPS THE TOLD FACT (`told-next`): every joiner the shut
-- view sees is told of its source's end (`Toldˢ none`).  The ghost's
-- scope is derived from it where the tree is keyed
-- (`adequacy.Engine.Firmed.gh-firm`).  Dispatched as the step is: by
-- mode, then by the frame a rise passes or the node a mark runs.  A step
-- that rewrites no node leaves the tree as it was.
module adequacy.Engine.Ghosted where

open import Data.Bool using (true; false; not)
open import Data.List using ([]; _∷_; _ʳ++_; _++_; [_]; reverse)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (pred; suc; _<ᵇ_; _≡ᵇ_)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Unit using (⊤; tt)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong)

open import Tree using (Obs; Later; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer; mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.MonotonicList.Events using (Timeline; ix; root; last; emit; stall; close; Frame∞; From∞)
open import adequacy.Engine.Head using (Frag)
open import adequacy.Engine.Pick using (Order; module Order; whole)
open import adequacy.Engine.Shuts using (Toldˢ; Toldᴸ; none; upˢ; closeOf)
open import adequacy.Engine.Meaning using (srcG)
open import adequacy.Engine.Scope using (closures)
open import adequacy.Engine.Toldc using (told-swap; told-feed-nx; told-feed-cp; moves-end; close-src; closeK;
  toldᴸ-join; toldᴸ-split; told-ended; told-killAll; told-cut; told-unsubIf; reclose; untold-closed)
open import adequacy.Engine.Fold using (Base; Owns; Wf; WfC; wfI; wf-split; owned; search-hit;
  ofO; attO; cpO; cutO; bodyO; srcAttO; owedO; joinO; leafO)
open import operation.PureObservable using (module Machine; module Driver; Tape; play; ending; over; rest)
open Machine using (St; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
  Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody; plug;
  CS; free; cpAt; cutAt; overAt; attached; nx; cp; Ev; unsubIf; cut;
  Conf; ⟨_,_,_,_⟩; subscribing; absorbed; rising;
  Mark; ofM; attM; bodyM; srcAttM; owedM; cpM; cutM; joinM; leafM; search; found;
  rise; run; begin; admit; dequeue; ended; alive; feed; start; closed; closedUp; killAll; attAt; cs; _⊕_)

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

  -- A mark run rewriting only its node: every joiner kept told, by the
  -- mark.  A body's mark runs only on an open connect, so it leaves its
  -- body's shuts as they were.
  of-told : ∀ {Γ A} (c : Ctx R Γ A) {s : St Γ A} p → Owns s ofM → Tolds c s → NextTold (took (run c s ofM p))
  of-told c r (ofO {i = i} {p = p} {xs = xs}) (_ , t , _) with closed c | xs
  ... | true  | ys      = told-swap c (ofS i p ys) doneS (λ _ → tt) t
  ... | false | []      = told-swap c (ofS i p []) doneS (λ _ → tt) t
  ... | false | x ∷ xs′ = told-swap c (ofS i p (x ∷ xs′)) (ofS (suc i) p xs′) (λ _ → tt) t

  att-told : ∀ {Γ A} (c : Ctx R Γ A) {s : St Γ A} p → Owns s attM → Tolds c s → NextTold (took (run c s attM p))
  att-told c r (attO {l = l} {p = p} {s = s}) (_ , t , _) with unsubIf (not l) s in e
  ... | s′ , _ = told-swap c (cutS l (attAt p) s) (cutS l attached s′)
                   (λ ts → subst (Toldˢ (closures c)) (cong proj₁ e) (told-unsubIf (not l) (closures c) s ts)) t

  cp-told : ∀ {Γ A} (c : Ctx R Γ A) {s : St Γ A} p → Owns s cpM → Tolds c s → NextTold (took (run c s cpM p))
  cp-told c r (cpO {i = i} {q = q} {p = p} {s = s}) (_ , t , _) = told-swap c (takeS i q (cpAt p) s) (takeS i q (cutAt p) s) (λ ts → ts) t

  cut-told : ∀ {Γ A} (c : Ctx R Γ A) {s : St Γ A} p → Owns s cutM → Tolds c s → NextTold (took (run c s cutM p))
  cut-told c r (cutO {i = i} {q = q} {p = p} {s = s}) (_ , t , _) with cut s in e
  ... | s′ , _ = told-swap c (takeS i q (cutAt p) s) (takeS i q (overAt p) s′)
                   (λ ts → subst (Toldˢ (closures c)) (cong proj₁ e) (told-cut (closures c) s ts)) t

  body-told : ∀ {Γ A} (c : Ctx R Γ A) {s : St Γ A} p → Owns s bodyM → Tolds c s → NextTold (took (run c s bodyM p))
  body-told c r (bodyO {k = cs cl sl sa (just p) as ow sr ea} {o = o} {b = b} refl) (_ , t , _ , ((refl , _) , _ , _)) =
    told-swap c (connS (cs false sl sa (just p) as ow sr ea) o b) (connS (cs false sl sa nothing (just (p ⊕ [ ix 1 ])) ow sr ea) o b) (λ ts → ts) t

  srcAtt-told : ∀ {Γ A} (c : Ctx R Γ A) {s : St Γ A} p → Owns s srcAttM → Tolds c s → NextTold (took (run c s srcAttM p))
  srcAtt-told c r (srcAttO {k = cs cl sl sa ba (just p) ow sr ea} {o = o} {b = b} refl) (_ , t , _) with unsubIf (not sl) o in e
  ... | o′ , _ = told-swap c (connS (cs cl sl sa ba (just p) ow sr ea) o b) (connS (cs cl sl true ba nothing ow sr ea) o′ b)
                   (λ { (to , tb) → subst (Toldˢ (closures c)) (cong proj₁ e) (told-unsubIf (not sl) (closures c) o to)
                                  , reclose (cs cl sl sa ba (just p) ow sr ea) o o′ (upˢ (closures c)) b tb }) t

  owed-told : ∀ {Γ A} (c : Ctx R Γ A) {s : St Γ A} p → Owns s owedM → Tolds c s → NextTold (took (run c s owedM p))
  owed-told c r (owedO {k = cs cl sl sa ba as (just p) sr ea} {o = o} {b = b} refl) (_ , t , _) with unsubIf sa o in e
  ... | o′ , _ = told-swap c (connS (cs cl sl sa ba as (just p) sr ea) o b) (connS (cs cl false sa ba as nothing sr ea) o′ b)
                   (λ { (to , tb) → subst (Toldˢ (closures c)) (cong proj₁ e) (told-unsubIf sa (closures c) o to)
                                  , reclose (cs cl sl sa ba as (just p) sr ea) o o′ (upˢ (closures c)) b tb }) t

  join-told : ∀ {Γ A} (c : Ctx R Γ A) {s : St Γ A} p → Owns s joinM → Tolds c s → NextTold (took (run c s joinM p))
  join-told c r (joinO {j = j} {g = true}  {x = x} {q = q} {e = nx a} {ib = ib}) (_ , t , _) =
    told-swap c (joinS j true x ((q , nx a) ∷ ib)) (joinS j true x ib) (λ ts → ts) t
  join-told c r (joinO {j = j} {g = false} {x = x} {q = q} {e = nx a} {ib = ib}) (_ , t , _) =
    told-swap c (joinS j false x ((q , nx a) ∷ ib)) (joinS j false x ib) (λ _ → tt) t
  join-told c r (joinO {j = j} {g = g}     {x = x} {q = q} {e = cp}   {ib = ib}) (_ , t , _) =
    told-swap c (joinS j g x ((q , cp) ∷ ib)) (joinS j false x ib) (λ _ → tt) t

  -- A leaf's turn leaves a leaf, which tells nothing.
  played-told : ∀ {Γ A} (c : Ctx R Γ A) r b (l : Tape A) → Toldˢ none (plug c (coldS b l)) → NextTold (took (run c (coldS b l) leafM r))
  played-told c r b     (ending e) t = told-swap c (coldS b (ending e)) (coldS false over) (λ _ → tt) t
  played-told c r false (play τ u i t′ fr) t = told-swap c (coldS false (play τ u i t′ fr)) (coldS false over) (λ _ → tt) t
  played-told c r false over t = told-swap c (coldS false over) (coldS false over) (λ _ → tt) t
  played-told c r true  over t with closed c
  ... | true  = told-swap c (coldS true over) (coldS true over) (λ _ → tt) t
  ... | false = told-swap c (coldS true over) (coldS true over) (λ _ → tt) t
  played-told c r true  (play τ u i t′ fr) t with closed c
  ... | true  = told-swap c (coldS true (play τ u i t′ fr)) (coldS true over) (λ _ → tt) t
  played-told c r true  (play τ u i t′ (emit a k)) t | false =
    told-swap c (coldS true (play τ u i t′ (emit a k))) (coldS true (play τ u (suc i) t′ k)) (λ _ → tt) t
  played-told c r true  (play τ u i t′ (stall k)) t | false =
    told-swap c (coldS true (play τ u i t′ (stall k))) (coldS true (play τ u (suc i) t′ (Frame∞.force k))) (λ _ → tt) t
  played-told c r true  (play τ u i t′ (close k)) t | false =
    told-swap c (coldS true (play τ u i t′ (close k))) (coldS true (rest τ (u ++ [ last ]) (From∞.force k))) (λ _ → tt) t

  leaf-told : ∀ {Γ A} (c : Ctx R Γ A) {s : St Γ A} p → Owns s leafM → Tolds c s → NextTold (took (run c s leafM p))
  leaf-told c r (leafO {b = b} {l = l} _) (_ , t , _) = played-told c r b l t

  -- A lane begun, or the flatMap left as it was: the lanes kept told.
  start-told : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q₀ q (o : St Γ A) ls a p
             → Toldˢ none (plug c (flatS op f d n q₀ o ls)) → Toldˢ none (whole (start c op f d n q o ls a p))
  start-told c op f d n q₀ q o ls a p t with closed c
  ... | true  = told-swap c (flatS op f d n q₀ o ls) (flatS op f d n q o ls) (λ t → t) t
  ... | false = told-swap c (flatS op f d n q₀ o ls) (flatS op f d (suc n) q o (reverse ls ʳ++ (lnS true (cutS true (attAt (p ⊕ [ ix 1 ])) (pend (f a))) ∷ [])))
                  (λ { (to , tl) → to , toldᴸ-join (closures c) (reverse ls) _ (toldᴸ-join (closures c) ls [] tl tt) (tt , tt) }) t

  dequeue-told : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) ls p
               → Toldˢ none (plug c (flatS op f d n q o ls)) → Toldˢ none (whole (dequeue c op f d n q o ls p))
  dequeue-told c op f d n []      o ls p t = t
  dequeue-told c op f d n (a ∷ q) o ls p t = start-told c op f d n (a ∷ q) q o ls a p t

  admit-told : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q ls (o : St Γ A) a p
              → Base ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩ → Order ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩
              → NextTold (took (admit c op f d n q o ls a p))
  lane-end-told : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) d n q (o : St Γ A) pre post (s : St Γ B) p → alive s ≡ true
                 → Base ⟨ inLanes op f d n q o pre post c , s , rising cp , p ⟩ → Order ⟨ inLanes op f d n q o pre post c , s , rising cp , p ⟩
                 → Toldˢ none (whole (dequeue c op f d (pred n) q o (pre ʳ++ ended s ∷ post) p))
  begin-told : ∀ {Γ A} (c : Ctx R Γ A) (o : Obs Timeline Γ A) p
              → Base ⟨ c , pend o , subscribing , p ⟩ → Order ⟨ c , pend o , subscribing , p ⟩
              → NextTold (took (begin c o p))
  admit-told c (mergeᶠ nothing)  f d n q ls o a p b ord = start-told c (mergeᶠ nothing) f d n q q o ls a p (Order.told ord)
  admit-told c (mergeᶠ (just m)) f d n q ls o a p b ord with n <ᵇ m
  ... | true  = start-told c (mergeᶠ (just m)) f d n q q o ls a p (Order.told ord)
  ... | false = told-swap c (flatS (mergeᶠ (just m)) f d n q o ls) (flatS (mergeᶠ (just m)) f d n (q ++ [ a ]) o ls) (λ t → t) (Order.told ord)
  admit-told c switchᶠ           f d n q ls o a p b ord with killAll ls in e
  ... | ls′ , tr = start-told c switchᶠ f d 0 q q o ls′ a p
                     (told-swap c (flatS switchᶠ f d n q o ls) (flatS switchᶠ f d 0 q o ls′)
                       (λ { (to , tl) → to , subst (Toldᴸ (closures c)) (cong proj₁ e) (told-killAll (closures c) ls tl) }) (Order.told ord))
  admit-told c exhaustᶠ          f d n q ls o a p b ord with n ≡ᵇ 0
  ... | true  = start-told c exhaustᶠ f d n q q o ls a p (Order.told ord)
  ... | false = Order.told ord
  lane-end-told c op f d n q o pre post s p al b ord =
    dequeue-told c op f d (pred n) q o (pre ʳ++ ended s ∷ post) p
      (told-swap c (flatS op f d n q o (pre ʳ++ s ∷ post)) (flatS op f d (pred n) q o (pre ʳ++ ended s ∷ post))
        (λ { (to , tl) → to , relane (toldᴸ-split (closures c) pre (s ∷ post) tl) }) (Order.told ord))
    where
    relane : Toldᴸ (closures c) pre × Toldᴸ (closures c) (s ∷ post) → Toldᴸ (closures c) (pre ʳ++ ended s ∷ post)
    relane (tp , (ts , tq)) = toldᴸ-join (closures c) pre (ended s ∷ post) tp (told-ended (closures c) s ts , tq)
  begin-told c (cold x)          p b ord = told-swap c (pend (cold x)) (coldS true _) (λ _ → tt) (Order.told ord)
  begin-told c empty             p b ord = told-swap c (pend empty) (ofS 0 p []) (λ _ → tt) (Order.told ord)
  begin-told c (of xs)           p b ord = told-swap c (pend (of xs)) (ofS 0 p xs) (λ _ → tt) (Order.told ord)
  begin-told c (map f s)         p b ord = told-swap c (pend (map f s)) (mapS f (pend s)) (λ _ → tt) (Order.told ord)
  begin-told c (scan f z s)      p b ord = told-swap c (pend (scan f z s)) (scanS f z (pend s)) (λ _ → tt) (Order.told ord)
  begin-told c (takeWhile i q s) p b ord = told-swap c (pend (takeWhile i q s)) (takeS i q free (cutS true (attAt p) (pend s))) (λ _ → tt) (Order.told ord)
  begin-told c (flatMap op f s)  p b ord = told-swap c (pend (flatMap op f s)) (flatS op f false 0 [] (cutS true (attAt p) (pend s)) []) (λ _ → tt , tt) (Order.told ord)
  begin-told c (connect s b′)    p b ord =
    told-swap c (pend (connect s b′)) (connS (cs false true false (just p) nothing nothing (p ⊕ [ ix 1 ]) root) (pend s) (pend b′)) (λ _ → tt , tt) (Order.told ord)
  begin-told c (connected x)     p b ord with closedUp c x in e
  ... | true  = told-swap c (pend (connected x)) (ofS 0 p []) (λ _ → tt) (Order.told ord)
  ... | false = told-swap c (pend (connected x)) (joinS p true x []) (λ _ → untold-closed c x e) (Order.told ord)
  begin-told c (defer l)         p b ord = told-swap c (pend (defer l)) (pend (Later.force l)) (λ _ → tt) (Order.told ord)

  -- A rise rewriting only its frame's node: the node's own told fact kept.
  scan-told : ∀ {Γ A B} (c : Ctx R Γ B) (f : B → A → B) z (s : St Γ A) a p
             → Base ⟨ inScan f z c , s , rising (nx a) , p ⟩ → Order ⟨ inScan f z c , s , rising (nx a) , p ⟩
             → Toldˢ none (plug c (scanS f (f z a) s))
  take-fail-told : ∀ {Γ A} (c : Ctx R Γ A) i q (s : St Γ A) a p → q a ≡ false
                  → Base ⟨ inTake i q free c , s , rising (nx a) , p ⟩ → Order ⟨ inTake i q free c , s , rising (nx a) , p ⟩
                  → Toldˢ none (plug c (takeS i q (cpAt p) s))
  outer-end-told : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → Obs Timeline Γ B) n q ls (o : St Γ A) p
                  → Base ⟨ inOuter op f false n q ls c , o , rising cp , p ⟩ → Order ⟨ inOuter op f false n q ls c , o , rising cp , p ⟩
                  → Toldˢ none (plug c (flatS op f true n q o ls))
  src-value-told : ∀ {Γ X B} (c : Ctx R Γ B) k (b : St (X ∷ Γ) B) (s : St Γ X) a p
                  → Base ⟨ inSrc k b c , s , rising (nx a) , p ⟩ → Order ⟨ inSrc k b c , s , rising (nx a) , p ⟩
                  → Toldˢ none (plug c (connS k s (feed (here refl) p (nx a) b)))
  src-end-told : ∀ {Γ X B} (c : Ctx R Γ B) k (b : St (X ∷ Γ) B) (s : St Γ X) p
                → Base ⟨ inSrc k b c , s , rising cp , p ⟩ → Order ⟨ inSrc k b c , s , rising cp , p ⟩
                → Toldˢ none (plug c (connS (record k { closed = true ; endAt = p }) s (feed (here refl) p cp b)))
  body-end-told : ∀ {Γ X B} (c : Ctx R Γ B) k (o : St Γ X) (s : St (X ∷ Γ) B) p
                 → Base ⟨ inBody k o c , s , rising cp , p ⟩ → Order ⟨ inBody k o c , s , rising cp , p ⟩
                 → Toldˢ none (plug c (connS (record k { owedAt = just p }) o s))
  scan-told c f z s a p b o = told-swap c (scanS f z s) (scanS f (f z a) s) (λ t → t) (Order.told o)
  take-fail-told c i q s a p e b o = told-swap c (takeS i q free s) (takeS i q (cpAt p) s) (λ t → t) (Order.told o)
  outer-end-told c op f n q ls o p b ord = told-swap c (flatS op f false n q o ls) (flatS op f true n q o ls) (λ t → t) (Order.told ord)
  src-value-told c k b s a p bs o =
    told-swap c (connS k s b) (connS k s (feed (here refl) p (nx a) b))
      (λ { (ts , tb) → ts , told-feed-nx (closeOf (srcG k s) (upˢ (closures c))) (here refl) p a b tb }) (Order.told o)
  src-end-told c k b s p bs o =
    told-swap c (connS k s b) (connS (record k { closed = true ; endAt = p }) s (feed (here refl) p cp b))
      (λ { (ts , tb) → ts ,
        subst (λ W → Toldˢ W (feed (here refl) p cp b)) (sym (close-src (record k { closed = true ; endAt = p }) s (upˢ (closures c))))
          (told-feed-cp (closeK k (upˢ (closures c))) (closeK (record k { closed = true ; endAt = p }) (upˢ (closures c))) (here refl) p
            (moves-end (CS.bodyAt k) (CS.closed k) (CS.endAt k) p (upˢ (closures c))) b
            (subst (λ W → Toldˢ W b) (close-src k s (upˢ (closures c))) tb)) }) (Order.told o)
  body-end-told c k o s p b ord = told-swap c (connS k o s) (connS (record k { owedAt = just p }) o s) (λ t → t) (Order.told ord)

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
