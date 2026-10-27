{-# OPTIONS --guardedness #-}

-- THE TOLD FACT FACTORS ALONG THE CONTEXT: a whole tree's joiners told
-- (`Toldˢ none (plug c s)`) is its frames' (`ToldC c`) beside the hole's,
-- read through the ended connects in scope (`Scope.closures`).  A
-- connect's source decides its body's shuts by the connect's flags alone
-- (`close-src`), so a frame over a source never reads the hole.  A step
-- rewriting only its hole keeps the fact when the hole's own is kept
-- (`told-swap`).  A value fed keeps every joiner as told as it was
-- (`told-feed-nx`); an end fed tells every joiner of its binder, so the
-- fact survives that binder's shut (`told-feed-cp`).  Unsubscribing
-- keeps it (`told-unsub`), and so does a joiner subscribed while its
-- binder is open (`untold-closed`).
module adequacy.Engine.Toldc where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _ʳ++_; _++_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing; is-just)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

open import denotation.MonotonicList.Events using (Pos; _<ᵖ_)
open import denotation.Unfold using (same?)
open import operation.PureObservable using (module Machine)
open Machine using (St; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
  CS; Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody; plug;
  Ev; nx; cp; feed; feedL; queued; unsub; unsubIf; cut; killAll; ended; closedUp; attached; attAt)
open import adequacy.Engine.Meaning using (srcOf; srcG; endOf)
open import adequacy.Engine.Shuts using (Shuts; none; shutAt; upˢ; snocˢ; closeOf; Untold; Told; Toldˢ; Toldᴸ)
open import adequacy.Engine.Scope using (closures)

-- A body's shuts, by its connect's flags.
closeB : ∀ {Γ X} → Maybe Pos → Bool → Pos → Shuts (X ∷ Γ) → Shuts (X ∷ Γ)
closeB (just q) c     e V = V
closeB nothing  false e V = V
closeB nothing  true  e V = snocˢ V (here refl) e

closeK : ∀ {Γ X} → CS → Shuts (X ∷ Γ) → Shuts (X ∷ Γ)
closeK k = closeB (CS.bodyAt k) (CS.closed k) (CS.endAt k)

close-srcOf : ∀ {Γ X} b c e (o : St Γ X) (V : Shuts (X ∷ Γ)) → closeOf (srcOf b c e o) V ≡ closeB b c e V
close-srcOf (just q) c     e o V = refl
close-srcOf nothing  false e o V = refl
close-srcOf nothing  true  e o V = refl

close-src : ∀ {Γ X} k (o : St Γ X) (V : Shuts (X ∷ Γ)) → closeOf (srcG k o) V ≡ closeK k V
close-src k o V = close-srcOf (CS.bodyAt k) (CS.closed k) (CS.endAt k) o V

-- A lane list read around its hole.
toldᴸ-split : ∀ {Γ A} (V : Shuts Γ) (pre ls : List (St Γ A)) → Toldᴸ V (pre ʳ++ ls) → Toldᴸ V pre × Toldᴸ V ls
toldᴸ-split V []       ls t = tt , t
toldᴸ-split V (x ∷ xs) ls t with toldᴸ-split V xs (x ∷ ls) t
... | tp , (tx , tl) = (tx , tp) , tl

toldᴸ-join : ∀ {Γ A} (V : Shuts Γ) (pre ls : List (St Γ A)) → Toldᴸ V pre → Toldᴸ V ls → Toldᴸ V (pre ʳ++ ls)
toldᴸ-join V []       ls tp       tl = tl
toldᴸ-join V (x ∷ xs) ls (tx , tp) tl = toldᴸ-join V xs (x ∷ ls) tp (tx , tl)

-- The frames' share of the told fact.
ToldC : ∀ {R Γ A} → Ctx R Γ A → Set
ToldC top                               = ⊤
ToldC (inMap f c)                       = ToldC c
ToldC (inScan f z c)                    = ToldC c
ToldC (inCut l a c)                     = ToldC c
ToldC (inLn b c)                        = ToldC c
ToldC (inTake i q w c)                  = ToldC c
ToldC (inOuter op f d n q ls c)         = ToldC c × Toldᴸ (closures c) ls
ToldC (inLanes op f d n q o pre post c) = ToldC c × Toldˢ (closures c) o × Toldᴸ (closures c) pre × Toldᴸ (closures c) post
ToldC (inSrc k b c)                     = ToldC c × Toldˢ (closeK k (upˢ (closures c))) b
ToldC (inBody k o c)                    = ToldC c × Toldˢ (closures c) o

told-split : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) → Toldˢ none (plug c s) → ToldC c × Toldˢ (closures c) s
told-split top                               s t = tt , t
told-split (inMap f c)                       s t = told-split c (mapS f s) t
told-split (inScan f z c)                    s t = told-split c (scanS f z s) t
told-split (inCut l a c)                     s t = told-split c (cutS l a s) t
told-split (inLn b c)                        s t = told-split c (lnS b s) t
told-split (inTake i q w c)                  s t = told-split c (takeS i q w s) t
told-split (inOuter op f d n q ls c)         s t with told-split c (flatS op f d n q s ls) t
... | tc , (ts , tl) = (tc , tl) , ts
told-split (inLanes op f d n q o pre post c) s t with told-split c (flatS op f d n q o (pre ʳ++ s ∷ post)) t
... | tc , (to , tl) with toldᴸ-split (closures c) pre (s ∷ post) tl
...   | tp , (ts , tq) = (tc , to , tp , tq) , ts
told-split (inSrc k b c)                     s t with told-split c (connS k s b) t
... | tc , (ts , tb) = (tc , subst (λ W → Toldˢ W b) (close-src k s (upˢ (closures c))) tb) , ts
told-split (inBody k o c)                    s t with told-split c (connS k o s) t
... | tc , (to , ts) = (tc , to) , ts

told-join : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) → ToldC c → Toldˢ (closures c) s → Toldˢ none (plug c s)
told-join top                               s tc                ts = ts
told-join (inMap f c)                       s tc                ts = told-join c (mapS f s) tc ts
told-join (inScan f z c)                    s tc                ts = told-join c (scanS f z s) tc ts
told-join (inCut l a c)                     s tc                ts = told-join c (cutS l a s) tc ts
told-join (inLn b c)                        s tc                ts = told-join c (lnS b s) tc ts
told-join (inTake i q w c)                  s tc                ts = told-join c (takeS i q w s) tc ts
told-join (inOuter op f d n q ls c)         s (tc , tl)         ts = told-join c (flatS op f d n q s ls) tc (ts , tl)
told-join (inLanes op f d n q o pre post c) s (tc , to , tp , tq) ts =
  told-join c (flatS op f d n q o (pre ʳ++ s ∷ post)) tc (to , toldᴸ-join (closures c) pre (s ∷ post) tp (ts , tq))
told-join (inSrc k b c)                     s (tc , tb)         ts =
  told-join c (connS k s b) tc (ts , subst (λ W → Toldˢ W b) (sym (close-src k s (upˢ (closures c)))) tb)
told-join (inBody k o c)                    s (tc , to)         ts = told-join c (connS k o s) tc (to , ts)

-- A step rewriting only the hole keeps the fact when it keeps the hole's.
told-swap : ∀ {R Γ A} (c : Ctx R Γ A) (s s′ : St Γ A) → (Toldˢ (closures c) s → Toldˢ (closures c) s′)
          → Toldˢ none (plug c s) → Toldˢ none (plug c s′)
told-swap c s s′ h t with told-split c s t
... | tc , ts = told-join c s′ tc (h ts)

reclose : ∀ {Γ X B} k (o o′ : St Γ X) (U : Shuts (X ∷ Γ)) (b : St (X ∷ Γ) B) → Toldˢ (closeOf (srcG k o) U) b → Toldˢ (closeOf (srcG k o′) U) b
reclose k o o′ U b = subst (λ W → Toldˢ W b) (trans (close-src k o U) (sym (close-src k o′ U)))

-- Untold through the scope's moves.
untold-up⁺ : ∀ {Γ X Y} (V : Shuts Γ) (x : Y ∈ Γ) → Untold V x → Untold (upˢ {X = X} V) (there x)
untold-up⁺ none           x u       = tt
untold-up⁺ (shutAt i c V) x (n , u) = n , untold-up⁺ V x u

untold-down : ∀ {Γ X Y} (V : Shuts Γ) (x : Y ∈ Γ) → Untold (upˢ {X = X} V) (there x) → Untold V x
untold-down none           x u       = tt
untold-down (shutAt i c V) x (n , u) = n , untold-down V x u

untold-here : ∀ {Γ X} (V : Shuts Γ) → Untold (upˢ {X = X} V) (here refl)
untold-here none           = tt
untold-here (shutAt i c V) = refl , untold-here V

untold-snoc⁺ : ∀ {Γ X Y} (V : Shuts Γ) (i : X ∈ Γ) c (x : Y ∈ Γ) → Untold V x → is-just (same? i x) ≡ false → Untold (snocˢ V i c) x
untold-snoc⁺ none           i c x u       n = n , tt
untold-snoc⁺ (shutAt j d V) i c x (m , u) n = m , untold-snoc⁺ V i c x u n

untold-snoc⁻ : ∀ {Γ X Y} (V : Shuts Γ) (i : X ∈ Γ) c (x : Y ∈ Γ) → Untold (snocˢ V i c) x → Untold V x
untold-snoc⁻ none           i c x u       = tt
untold-snoc⁻ (shutAt j d V) i c x (m , u) = m , untold-snoc⁻ V i c x u

untold-snoc-at : ∀ {Γ X Y} (V : Shuts Γ) (i : X ∈ Γ) c (x : Y ∈ Γ) → Untold (snocˢ V i c) x → is-just (same? i x) ≡ false
untold-snoc-at none           i c x (n , _) = n
untold-snoc-at (shutAt j d V) i c x (_ , u) = untold-snoc-at V i c x u

-- Every joiner but binder `i`'s untold under `V` is untold under `V′`.
Moves : ∀ {Γ X} → Shuts Γ → Shuts Γ → X ∈ Γ → Set₁
Moves {Γ} V V′ i = ∀ {Y} (x : Y ∈ Γ) → is-just (same? i x) ≡ false → Untold V x → Untold V′ x

moves-up : ∀ {Γ X Y} (V V′ : Shuts Γ) (i : Y ∈ Γ) → Moves V V′ i → Moves (upˢ {X = X} V) (upˢ V′) (there i)
moves-up V V′ i h (here refl) n u = untold-here V′
moves-up V V′ i h (there x)   n u = untold-up⁺ V′ x (h x n (untold-down V x u))

moves-close : ∀ {Γ X Y} b c e (V V′ : Shuts Γ) (i : Y ∈ Γ) → Moves V V′ i → Moves (closeB {X = X} b c e (upˢ V)) (closeB b c e (upˢ V′)) (there i)
moves-close (just q) c     e V V′ i h = moves-up V V′ i h
moves-close nothing  false e V V′ i h = moves-up V V′ i h
moves-close nothing  true  e V V′ i h x n u =
  untold-snoc⁺ (upˢ V′) (here refl) e x (moves-up V V′ i h x n (untold-snoc⁻ (upˢ V) (here refl) e x u)) (untold-snoc-at (upˢ V) (here refl) e x u)

-- A source's end shuts its body, wherever it already stood.
moves-end : ∀ {Γ X} b c e p (U : Shuts (X ∷ Γ)) → Moves (closeB b c e U) (closeB b true p U) (here refl)
moves-end (just q) c     e p U x n u = u
moves-end nothing  false e p U x n u = untold-snoc⁺ U (here refl) p x u n
moves-end nothing  true  e p U x n u = untold-snoc⁺ U (here refl) p x (untold-snoc⁻ U (here refl) e x u) n

-- What a feed leaves of a joiner's end.
endOf-nx : ∀ {A} (ib : List (Pos × Ev A)) q a → endOf (ib ++ [ (q , nx a) ]) ≡ endOf ib
endOf-nx []                 q a = refl
endOf-nx ((r , nx b) ∷ ib)  q a = endOf-nx ib q a
endOf-nx ((r , cp) ∷ ib)    q a = refl

endOf-queued-nx : ∀ {A} j p (a : A) (ib : List (Pos × Ev A)) → endOf (queued j p (nx a) ib) ≡ endOf ib
endOf-queued-nx j p a ib with j <ᵖ p
... | true  = endOf-nx ib _ a
... | false = refl

endOf-cp : ∀ {Γ A X} (V : Shuts Γ) (x : X ∈ Γ) (ib : List (Pos × Ev A)) q → Told V x (endOf (ib ++ [ (q , cp) ]))
endOf-cp V x []                q = tt
endOf-cp V x ((r , nx b) ∷ ib) q = endOf-cp V x ib q
endOf-cp V x ((r , cp) ∷ ib)   q = tt

told-move : ∀ {Γ X} (V V′ : Shuts Γ) (x : X ∈ Γ) m → (Untold V x → Untold V′ x) → Told V x m → Told V′ x m
told-move V V′ x (just q) h t = tt
told-move V V′ x nothing  h t = h t

mutual
  told-feed-nx : ∀ {Γ X A} (V : Shuts Γ) (i : X ∈ Γ) p a (s : St Γ A) → Toldˢ V s → Toldˢ V (feed i p (nx a) s)
  told-feed-nx V i p a (pend o)                t = t
  told-feed-nx V i p a (coldS b l)             t = t
  told-feed-nx V i p a (ofS j q xs)            t = t
  told-feed-nx V i p a doneS                   t = t
  told-feed-nx V i p a (mapS f s)              t = told-feed-nx V i p a s t
  told-feed-nx V i p a (scanS f z s)           t = told-feed-nx V i p a s t
  told-feed-nx V i p a (cutS l b s)            t = told-feed-nx V i p a s t
  told-feed-nx V i p a (lnS b s)               t = told-feed-nx V i p a s t
  told-feed-nx V i p a (takeS v q w s)         t = told-feed-nx V i p a s t
  told-feed-nx V i p a (flatS op f d n q o ls) (to , tl) = told-feed-nx V i p a o to , told-feed-nxᴸ V i p a ls tl
  told-feed-nx V i p a (connS k o b)           (to , tb) =
    told-feed-nx V i p a o to ,
    reclose k o (feed i p (nx a) o) (upˢ V) (feed (there i) p (nx a) b) (told-feed-nx (closeOf (srcG k o) (upˢ V)) (there i) p a b tb)
  told-feed-nx V i p a (joinS j false x ib)    t = t
  told-feed-nx V i p a (joinS j true x ib)     t with same? i x
  ... | just refl = subst (Told V x) (sym (endOf-queued-nx j p a ib)) t
  ... | nothing   = t

  told-feed-nxᴸ : ∀ {Γ X A} (V : Shuts Γ) (i : X ∈ Γ) p a (ls : List (St Γ A)) → Toldᴸ V ls → Toldᴸ V (feedL i p (nx a) ls)
  told-feed-nxᴸ V i p a []       t        = tt
  told-feed-nxᴸ V i p a (s ∷ ls) (ts , tl) = told-feed-nx V i p a s ts , told-feed-nxᴸ V i p a ls tl

mutual
  told-feed-cp : ∀ {Γ X A} (V V′ : Shuts Γ) (i : X ∈ Γ) p → Moves V V′ i → (s : St Γ A) → Toldˢ V s → Toldˢ V′ (feed i p cp s)
  told-feed-cp V V′ i p h (pend o)                t = t
  told-feed-cp V V′ i p h (coldS b l)             t = t
  told-feed-cp V V′ i p h (ofS j q xs)            t = t
  told-feed-cp V V′ i p h doneS                   t = t
  told-feed-cp V V′ i p h (mapS f s)              t = told-feed-cp V V′ i p h s t
  told-feed-cp V V′ i p h (scanS f z s)           t = told-feed-cp V V′ i p h s t
  told-feed-cp V V′ i p h (cutS l b s)            t = told-feed-cp V V′ i p h s t
  told-feed-cp V V′ i p h (lnS b s)               t = told-feed-cp V V′ i p h s t
  told-feed-cp V V′ i p h (takeS v q w s)         t = told-feed-cp V V′ i p h s t
  told-feed-cp V V′ i p h (flatS op f d n q o ls) (to , tl) = told-feed-cp V V′ i p h o to , told-feed-cpᴸ V V′ i p h ls tl
  told-feed-cp V V′ i p h (connS k o b)           (to , tb) =
    told-feed-cp V V′ i p h o to ,
    subst (λ W → Toldˢ W (feed (there i) p cp b)) (sym (close-src k (feed i p cp o) (upˢ V′)))
      (told-feed-cp (closeK k (upˢ V)) (closeK k (upˢ V′)) (there i) p
        (moves-close (CS.bodyAt k) (CS.closed k) (CS.endAt k) V V′ i h) b
        (subst (λ W → Toldˢ W b) (close-src k o (upˢ V)) tb))
  told-feed-cp V V′ i p h (joinS j false x ib)    t = t
  told-feed-cp V V′ i p h (joinS j true x ib)     t with same? i x in e
  ... | just refl = endOf-cp V′ x ib _
  ... | nothing   = told-move V V′ x (endOf ib) (h x (cong is-just e)) t

  told-feed-cpᴸ : ∀ {Γ X A} (V V′ : Shuts Γ) (i : X ∈ Γ) p → Moves V V′ i → (ls : List (St Γ A)) → Toldᴸ V ls → Toldᴸ V′ (feedL i p cp ls)
  told-feed-cpᴸ V V′ i p h []       t         = tt
  told-feed-cpᴸ V V′ i p h (s ∷ ls) (ts , tl) = told-feed-cp V V′ i p h s ts , told-feed-cpᴸ V V′ i p h ls tl

-- A lane's end keeps its joiners.
told-endedₗ : ∀ {Γ A} (V : Shuts Γ) b (s : St Γ A) → Toldˢ V s → Toldˢ V (ended (lnS b s))
told-endedₗ V b′ (pend o) t = t
told-endedₗ V b′ (coldS b l) t = t
told-endedₗ V b′ (ofS j q xs) t = t
told-endedₗ V b′ doneS t = t
told-endedₗ V b′ (mapS f s) t = t
told-endedₗ V b′ (scanS f z s) t = t
told-endedₗ V b′ (cutS l a s) t = t
told-endedₗ V b′ (lnS b s) t = t
told-endedₗ V b′ (takeS v q w s) t = t
told-endedₗ V b′ (flatS op f d n q o ls) t = t
told-endedₗ V b′ (connS k o b) t = t
told-endedₗ V b′ (joinS j g x ib) t = t

told-ended : ∀ {Γ A} (V : Shuts Γ) (s : St Γ A) → Toldˢ V s → Toldˢ V (ended s)
told-ended V (lnS b s) t = told-endedₗ V b s t
told-ended V (pend o) t = t
told-ended V (coldS b l) t = t
told-ended V (ofS j q xs) t = t
told-ended V doneS t = t
told-ended V (mapS f s) t = t
told-ended V (scanS f z s) t = t
told-ended V (cutS l a s) t = t
told-ended V (takeS v q w s) t = t
told-ended V (flatS op f d n q o ls) t = t
told-ended V (connS k o b) t = t
told-ended V (joinS j g x ib) t = t


-- Unsubscribing keeps every joiner told: a joiner it reaches is dropped.
mutual
  told-unsub : ∀ {Γ A} (V : Shuts Γ) (s : St Γ A) → Toldˢ V s → Toldˢ V (proj₁ (unsub s))
  told-unsub V (pend o)                t         = t
  told-unsub V (coldS true l)          t         = tt
  told-unsub V (coldS false l)         t         = t
  told-unsub V (ofS j q xs)            t         = t
  told-unsub V doneS                   t         = t
  told-unsub V (mapS f s)              t         = told-unsub V s t
  told-unsub V (scanS f z s)           t         = told-unsub V s t
  told-unsub V (cutS l a s)            t         = t
  told-unsub V (lnS b s)               t         = t
  told-unsub V (takeS v q w s)         t         = told-cut V s t
  told-unsub V (flatS op f d n q o ls) (to , tl) = told-cut V o to , told-killAll V ls tl
  told-unsub V (connS k o b)           (to , tb) =
    told-unsub V o to , reclose k o (proj₁ (unsub o)) (upˢ V) (proj₁ (unsub b)) (told-unsub (closeOf (srcG k o) (upˢ V)) b tb)
  told-unsub V (joinS j g x ib)        t         = tt

  told-cut : ∀ {Γ A} (V : Shuts Γ) (s : St Γ A) → Toldˢ V s → Toldˢ V (proj₁ (cut s))
  told-cut V (pend o) t = t
  told-cut V (coldS b l) t = t
  told-cut V (ofS j q xs) t = t
  told-cut V doneS t = t
  told-cut V (mapS f s) t = t
  told-cut V (scanS f z s) t = t
  told-cut V (cutS l attached s) t = told-unsub V s t
  told-cut V (cutS l (attAt p) s) t = t
  told-cut V (lnS b s) t = t
  told-cut V (takeS v q w s) t = t
  told-cut V (flatS op f d n q o ls) t = t
  told-cut V (connS k o b) t = t
  told-cut V (joinS j g x ib) t = t

  told-killAll : ∀ {Γ A} (V : Shuts Γ) (ls : List (St Γ A)) → Toldᴸ V ls → Toldᴸ V (proj₁ (killAll ls))
  told-killAll V [] t = tt
  told-killAll V (lnS true s ∷ ls)  (ts , tl) = told-cut V s ts , told-killAll V ls tl
  told-killAll V (lnS false s ∷ ls) (ts , tl) = ts , told-killAll V ls tl
  told-killAll V (pend o ∷ ls) (ts , tl) = ts , told-killAll V ls tl
  told-killAll V (coldS b l ∷ ls) (ts , tl) = ts , told-killAll V ls tl
  told-killAll V (ofS j q xs ∷ ls) (ts , tl) = ts , told-killAll V ls tl
  told-killAll V (doneS ∷ ls) (ts , tl) = ts , told-killAll V ls tl
  told-killAll V (mapS f s ∷ ls) (ts , tl) = ts , told-killAll V ls tl
  told-killAll V (scanS f z s ∷ ls) (ts , tl) = ts , told-killAll V ls tl
  told-killAll V (cutS l a s ∷ ls) (ts , tl) = ts , told-killAll V ls tl
  told-killAll V (takeS v q w s ∷ ls) (ts , tl) = ts , told-killAll V ls tl
  told-killAll V (flatS op f d n q o ms ∷ ls) (ts , tl) = ts , told-killAll V ls tl
  told-killAll V (connS k o b ∷ ls) (ts , tl) = ts , told-killAll V ls tl
  told-killAll V (joinS j g x ib ∷ ls) (ts , tl) = ts , told-killAll V ls tl

told-unsubIf : ∀ {Γ A} b (V : Shuts Γ) (s : St Γ A) → Toldˢ V s → Toldˢ V (proj₁ (unsubIf b s))
told-unsubIf true  V s t = told-unsub V s t
told-unsubIf false V s t = t

-- A joiner subscribed while its binder is open is untold up its scope.
closeB-here : ∀ {Γ X} b c e (V : Shuts Γ) → c ≡ false → Untold (closeB {X = X} b c e (upˢ V)) (here refl)
closeB-here (just q) c     e V n = untold-here V
closeB-here nothing  false e V n = untold-here V
closeB-here nothing  true  e V ()

closeB-there : ∀ {Γ X Y} b c e (V : Shuts Γ) (x : Y ∈ Γ) → Untold V x → Untold (closeB {X = X} b c e (upˢ V)) (there x)
closeB-there (just q) c     e V x u = untold-up⁺ V x u
closeB-there nothing  false e V x u = untold-up⁺ V x u
closeB-there nothing  true  e V x u = untold-snoc⁺ (upˢ V) (here refl) e (there x) (untold-up⁺ V x u) refl

untold-closed : ∀ {R Γ A X} (c : Ctx R Γ A) (x : X ∈ Γ) → closedUp c x ≡ false → Untold (closures c) x
untold-closed top                               ()          e
untold-closed (inMap f c)                       x           e = untold-closed c x e
untold-closed (inScan f z c)                    x           e = untold-closed c x e
untold-closed (inCut l a c)                     x           e = untold-closed c x e
untold-closed (inLn b c)                        x           e = untold-closed c x e
untold-closed (inTake i q w c)                  x           e = untold-closed c x e
untold-closed (inOuter op f d n q ls c)         x           e = untold-closed c x e
untold-closed (inLanes op f d n q o pre post c) x           e = untold-closed c x e
untold-closed (inSrc k b c)                     x           e = untold-closed c x e
untold-closed (inBody k o c)                    (here refl) e =
  subst (λ W → Untold W (here refl)) (sym (close-src k o (upˢ (closures c)))) (closeB-here (CS.bodyAt k) (CS.closed k) (CS.endAt k) (closures c) e)
untold-closed (inBody k o c)                    (there x)   e =
  subst (λ W → Untold W (there x)) (sym (close-src k o (upˢ (closures c)))) (closeB-there (CS.bodyAt k) (CS.closed k) (CS.endAt k) (closures c) x (untold-closed c x e))
