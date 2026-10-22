{-# OPTIONS --guardedness #-}

-- SPIKE 4: THE ORDER.  The positions the spike-3 machine shows only move
-- forward, however far it is run.
--
-- The invariant is today's `WellStack` (in `adequacy.Sorted`), read off a
-- job stack instead of a heap of continuations: the run is at a SCOPE
-- (the configuration's position); everything delivered from here until
-- the job on top resumes is `Settled` in that scope; each job on the
-- stack is a scope enclosing the one above it, and is `Ready` from
-- wherever the scopes above may leave the last delivery.
--
-- `Ready` reads the job's TAG and position alone, never the tree: what
-- a kernel keeps in its continuation (an `of`'s count, a takeWhile's
-- owed completion, a feed's joiners still to feed) rides on the tag.  So
-- a step that rewrites the tree moves no job's bound, and the chain is
-- untouched by everything but the stack.
--
-- The one fact the tree carries: every binder's joiners joined in
-- ascending position, all no later than the last event, so a feed's
-- joiners are fed in ascending position.  A join is an event: the
-- watermark `lo` is the last delivery OR join, a delivery at no less, a
-- join strictly past it.
module spike.StateTree3Order where

open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Nat using (ℕ; zero; suc; pred; _≡ᵇ_)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import denotation.MonotonicList.Events using (Pos; ix; last; root; _<ᵖ_; <ᵖ-trans; <ᵖ-below; <ᵖ-part; <ᵖ-sub; <ᵖ-ix) renaming (sub to subᴾ)
open import adequacy.Sorted using (_≤ᵖ_; Under; Settled; settled-refl; settled-trans; settled-next; ≤ᵖ-child; ≤ᵖ-trans)
open import Tree using (Later; mergeᶠ; switchᶠ; exhaustᶠ; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import spike.StateTree3
open import spike.StateTree3Valid using (Valid; V; modeJobs; tag-of; TagR; downs-lands; step-ok; load-ok)

------------------------------------------------------------------------
-- Positions

≤-< : ∀ {a b c} → a ≤ᵖ b → b <ᵖ c ≡ true → a <ᵖ c ≡ true
≤-< (inj₁ refl) h = h
≤-< {a} {b} {c} (inj₂ h₁) h = <ᵖ-trans a b c h₁ h

-- Before a scope, strictly before each of its children.
<-child : ∀ p {l lo} → lo ≤ᵖ p → lo <ᵖ (p ++ [ l ]) ≡ true
<-child p le = ≤-< le (<ᵖ-below p [])

under-refl : ∀ p → Under p p
under-refl p = [] , sym (++-identityʳ p)

under-child : ∀ p l → Under p (p ++ [ l ])
under-child p l = [ l ] , refl

under-trans : ∀ {a b c} → Under a b → Under b c → Under a c
under-trans {a} (x , refl) (y , refl) = x ++ y , ++-assoc a x y

-- Settled in a scope is settled in any scope enclosing it.
settled-up : ∀ {S S′ lo lo′} → Under S S′ → Settled S′ lo lo′ → Settled S lo lo′
settled-up u (a , inj₁ e) = a , inj₁ e
settled-up {S} (x , refl) (a , inj₂ (y , refl)) = a , inj₂ (x ++ y , ++-assoc S x y)

-- An event at the scope itself.
settled-at : ∀ {p lo} → lo ≤ᵖ p → Settled p lo p
settled-at {p} le = le , inj₂ (under-refl p)

-- Wherever a child left the last, strictly before a later sibling.
settled-next< : ∀ q {a b lo lo′} → (a ∷ []) <ᵖ (b ∷ []) ≡ true → lo <ᵖ (q ++ [ b ]) ≡ true → Settled (q ++ [ a ]) lo lo′ → lo′ <ᵖ (q ++ [ b ]) ≡ true
settled-next< q     h lt (_ , inj₁ refl)       = lt
settled-next< q {a} h lt (_ , inj₂ (y , refl)) rewrite ++-assoc q [ a ] y = <ᵖ-part q y [] h

-- A later sibling, after its elder's scope.
sib : ∀ p {a b lo} → (a ∷ []) <ᵖ (b ∷ []) ≡ true → lo ≤ᵖ (p ++ [ a ]) → lo ≤ᵖ (p ++ [ b ])
sib p h le = ≤ᵖ-trans le (inj₂ (<ᵖ-part p [] [] h))

------------------------------------------------------------------------
-- Joiners in ascending position

Asc : Pos → List (List ℕ × Pos) → Set
Asc j []              = ⊤
Asc j ((q , j′) ∷ js) = j <ᵖ j′ ≡ true × Asc j′ js

Up : List (List ℕ × Pos) → Set
Up []             = ⊤
Up ((q , j) ∷ js) = Asc j js

Below : Pos → List (List ℕ × Pos) → Set
Below lo js = All (λ j → proj₂ j ≤ᵖ lo) js

asc-snoc : ∀ j js {q p} → Asc j js → j <ᵖ p ≡ true → All (λ x → proj₂ x <ᵖ p ≡ true) js → Asc j (js ++ [ (q , p) ])
asc-snoc j []               a        h []        = h , tt
asc-snoc j ((q′ , j′) ∷ js) (h₁ , a) h (h′ ∷ al) = h₁ , asc-snoc j′ js a h′ al

up-snoc : ∀ js {q p} → Up js → All (λ x → proj₂ x <ᵖ p ≡ true) js → Up (js ++ [ (q , p) ])
up-snoc []             u []        = tt
up-snoc ((q , j) ∷ js) u (h ∷ al) = asc-snoc j js u h al

below-< : ∀ {lo p} js → Below lo js → lo <ᵖ p ≡ true → All (λ x → proj₂ x <ᵖ p ≡ true) js
below-< []       []       h = []
below-< (_ ∷ js) (b ∷ bl) h = ≤-< b h ∷ below-< js bl h

below-mono : ∀ {lo lo′} {js} → lo ≤ᵖ lo′ → Below lo js → Below lo′ js
below-mono le bl = mapᴬ (λ b → ≤ᵖ-trans b le) bl

asc-rooted : ∀ {R Γ A} (c : Ctx R Γ A) j js → Asc j js → Asc j (rooted c js)
asc-rooted c j []              a        = tt
asc-rooted c j ((q , j′) ∷ js) (h , a) = h , asc-rooted c j′ js a

------------------------------------------------------------------------
-- Every binder's joiners: ascending, and no later than `lo`

Bound : ∀ {X} → Pos → CS X → Set
Bound lo k = Below lo (CS.subs k) × Up (CS.subs k)

mutual
  JT : ∀ {Γ A} → Pos → St Γ A → Set
  JT lo (pend o)              = ⊤
  JT lo (ofS xs)              = ⊤
  JT lo doneS                 = ⊤
  JT lo (joinS j g x)         = ⊤
  JT lo (mapS f s)            = JT lo s
  JT lo (scanS f z s)         = JT lo s
  JT lo (cutS l a s)          = JT lo s
  JT lo (lnS b s)             = JT lo s
  JT lo (takeS i q s)         = JT lo s
  JT lo (flatS op f d n o ls) = JT lo o × JTL lo ls
  JT lo (connS k o b)         = JT lo o × JT lo b × Bound lo k

  JTL : ∀ {Γ B} → Pos → List (St Γ B) → Set
  JTL lo []       = ⊤
  JTL lo (s ∷ ls) = JT lo s × JTL lo ls

mutual
  jt-mono : ∀ {Γ A lo lo′} (s : St Γ A) → lo ≤ᵖ lo′ → JT lo s → JT lo′ s
  jt-mono (pend o)              le t = tt
  jt-mono (ofS xs)              le t = tt
  jt-mono doneS                 le t = tt
  jt-mono (joinS j g x)         le t = tt
  jt-mono (mapS f s)            le t = jt-mono s le t
  jt-mono (scanS f z s)         le t = jt-mono s le t
  jt-mono (cutS l a s)          le t = jt-mono s le t
  jt-mono (lnS b s)             le t = jt-mono s le t
  jt-mono (takeS i q s)         le t = jt-mono s le t
  jt-mono (flatS op f d n o ls) le (t , tl) = jt-mono o le t , jtL-mono ls le tl
  jt-mono (connS k o b)         le (t , tb , bl , u) = jt-mono o le t , jt-mono b le tb , below-mono le bl , u

  jtL-mono : ∀ {Γ B lo lo′} (ls : List (St Γ B)) → lo ≤ᵖ lo′ → JTL lo ls → JTL lo′ ls
  jtL-mono []       le t        = tt
  jtL-mono (s ∷ ls) le (t , tl) = jt-mono s le t , jtL-mono ls le tl

jtL-mid : ∀ {Γ B lo lo′} (pre : List (St Γ B)) {s s′ : St Γ B} post → lo ≤ᵖ lo′ → (JT lo s → JT lo′ s′) → JTL lo (pre ++ s ∷ post) → JTL lo′ (pre ++ s′ ∷ post)
jtL-mid []        post le h (t , tl) = h t , jtL-mono post le tl
jtL-mid (x ∷ pre) post le h (t , tl) = jt-mono x le t , jtL-mid pre post le h tl

jtL-at : ∀ {Γ B lo} (pre : List (St Γ B)) {s : St Γ B} post → JTL lo (pre ++ s ∷ post) → JT lo s
jtL-at []        post (t , tl) = t
jtL-at (x ∷ pre) post (t , tl) = jtL-at pre post tl

jtL-snoc : ∀ {Γ B lo} (ls : List (St Γ B)) {x : St Γ B} → JTL lo ls → JT lo x → JTL lo (ls ++ [ x ])
jtL-snoc []       tl tx = tx , tt
jtL-snoc (s ∷ ls) (t , tl) tx = t , jtL-snoc ls tl tx

-- Through a context, from `lo` to a later `lo′`.
jt-lift : ∀ {R Γ A lo lo′} (c : Ctx R Γ A) {s s′ : St Γ A} → lo ≤ᵖ lo′ → (JT lo s → JT lo′ s′) → JT lo (plug c s) → JT lo′ (plug c s′)
jt-lift top                             le h = h
jt-lift (inMap f c)                     {s} {s′} le h = jt-lift c {mapS f s} {mapS f s′} le h
jt-lift (inScan f z c)                  {s} {s′} le h = jt-lift c {scanS f z s} {scanS f z s′} le h
jt-lift (inCut l a c)                   {s} {s′} le h = jt-lift c {cutS l a s} {cutS l a s′} le h
jt-lift (inLn b c)                      {s} {s′} le h = jt-lift c {lnS b s} {lnS b s′} le h
jt-lift (inTake i q c)                  {s} {s′} le h = jt-lift c {takeS i q s} {takeS i q s′} le h
jt-lift (inOuter op f d n ls c)         {s} {s′} le h =
  jt-lift c {flatS op f d n s ls} {flatS op f d n s′ ls} le λ (t , tl) → h t , jtL-mono ls le tl
jt-lift (inLanes op f d n o pre post c) {s} {s′} le h =
  jt-lift c {flatS op f d n o (pre ++ s ∷ post)} {flatS op f d n o (pre ++ s′ ∷ post)} le
    λ (t , tl) → jt-mono o le t , jtL-mid pre post le h tl
jt-lift (inSrc k b c)                   {s} {s′} le h =
  jt-lift c {connS k s b} {connS k s′ b} le λ (t , tb , bl , u) → h t , jt-mono b le tb , below-mono le bl , u
jt-lift (inBody k o c)                  {s} {s′} le h =
  jt-lift c {connS k o s} {connS k o s′} le λ (t , tb , bl , u) → jt-mono o le t , h tb , below-mono le bl , u

jt-plug : ∀ {R Γ A lo} (c : Ctx R Γ A) {s s′ : St Γ A} → (JT lo s → JT lo s′) → JT lo (plug c s) → JT lo (plug c s′)
jt-plug c {s} {s′} h = jt-lift c {s} {s′} (inj₁ refl) h

jt-hole : ∀ {R Γ A lo} (c : Ctx R Γ A) (s : St Γ A) → JT lo (plug c s) → JT lo s
jt-hole top                             s t = t
jt-hole (inMap f c)                     s t = jt-hole c (mapS f s) t
jt-hole (inScan f z c)                  s t = jt-hole c (scanS f z s) t
jt-hole (inCut l a c)                   s t = jt-hole c (cutS l a s) t
jt-hole (inLn b c)                      s t = jt-hole c (lnS b s) t
jt-hole (inTake i q c)                  s t = jt-hole c (takeS i q s) t
jt-hole (inOuter op f d n ls c)         s t = proj₁ (jt-hole c (flatS op f d n s ls) t)
jt-hole (inLanes op f d n o pre post c) s t = jtL-at pre post (proj₂ (jt-hole c (flatS op f d n o (pre ++ s ∷ post)) t))
jt-hole (inSrc k b c)                   s t = proj₁ (jt-hole c (connS k s b) t)
jt-hole (inBody k o c)                  s t = proj₁ (proj₂ (jt-hole c (connS k o s) t))

------------------------------------------------------------------------
-- Unsubscribing and ending a lane touch no binder's record

mutual
  unsub-jt : ∀ {Γ A lo} (s : St Γ A) → JT lo s → JT lo (unsub s)
  unsub-jt (pend o)              t = t
  unsub-jt (ofS xs)              t = t
  unsub-jt doneS                 t = t
  unsub-jt (cutS l a s)          t = t
  unsub-jt (lnS b s)             t = t
  unsub-jt (joinS j g x)         t = t
  unsub-jt (mapS f s)            t = unsub-jt s t
  unsub-jt (scanS f z s)         t = unsub-jt s t
  unsub-jt (takeS i q s)         t = cut-jt s t
  unsub-jt (flatS op f d n o ls) (t , tl) = cut-jt o t , killAll-jt ls tl
  unsub-jt (connS k o b)         (t , tb , bd) = unsub-jt o t , unsub-jt b tb , bd

  cut-jt : ∀ {Γ A lo} (s : St Γ A) → JT lo s → JT lo (cut s)
  cut-jt (cutS l true s)       t = unsub-jt s t
  cut-jt (cutS l false s)      t = t
  cut-jt (pend o)              t = t
  cut-jt (ofS xs)              t = t
  cut-jt doneS                 t = t
  cut-jt (joinS j g x)         t = t
  cut-jt (mapS f s)            t = t
  cut-jt (scanS f z s)         t = t
  cut-jt (lnS b s)             t = t
  cut-jt (takeS i q s)         t = t
  cut-jt (flatS op f d n o ls) t = t
  cut-jt (connS k o b)         t = t

  killAll-jt : ∀ {Γ B lo} (ls : List (St Γ B)) → JTL lo ls → JTL lo (killAll ls)
  killAll-jt []                        t        = tt
  killAll-jt (lnS true s ∷ ls)         (t , tl) = cut-jt s t , killAll-jt ls tl
  killAll-jt (lnS false s ∷ ls)        (t , tl) = t , killAll-jt ls tl
  killAll-jt (pend o ∷ ls)             (t , tl) = t , killAll-jt ls tl
  killAll-jt (ofS xs ∷ ls)             (t , tl) = t , killAll-jt ls tl
  killAll-jt (doneS ∷ ls)              (t , tl) = t , killAll-jt ls tl
  killAll-jt (joinS j g x ∷ ls)        (t , tl) = t , killAll-jt ls tl
  killAll-jt (mapS f s ∷ ls)           (t , tl) = t , killAll-jt ls tl
  killAll-jt (scanS f z s ∷ ls)        (t , tl) = t , killAll-jt ls tl
  killAll-jt (cutS l a s ∷ ls)         (t , tl) = t , killAll-jt ls tl
  killAll-jt (takeS i q s ∷ ls)        (t , tl) = t , killAll-jt ls tl
  killAll-jt (flatS op f d n o l ∷ ls) (t , tl) = t , killAll-jt ls tl
  killAll-jt (connS k o b ∷ ls)        (t , tl) = t , killAll-jt ls tl

ended-jt : ∀ {Γ B lo} (s : St Γ B) → JT lo s → JT lo (ended s)
ended-jt (lnS b (cutS l a s))          t = t
ended-jt (lnS b (pend o))              t = t
ended-jt (lnS b (ofS xs))              t = t
ended-jt (lnS b doneS)                 t = t
ended-jt (lnS b (joinS j g x))         t = t
ended-jt (lnS b (mapS f s))            t = t
ended-jt (lnS b (scanS f z s))         t = t
ended-jt (lnS b (lnS b′ s))            t = t
ended-jt (lnS b (takeS i q s))         t = t
ended-jt (lnS b (flatS op f d n o ls)) t = t
ended-jt (lnS b (connS k o b′))        t = t
ended-jt (pend o)                      t = t
ended-jt (ofS xs)                      t = t
ended-jt doneS                         t = t
ended-jt (joinS j g x)                 t = t
ended-jt (mapS f s)                    t = t
ended-jt (scanS f z s)                 t = t
ended-jt (cutS l a s)                  t = t
ended-jt (takeS i q s)                 t = t
ended-jt (flatS op f d n o ls)         t = t
ended-jt (connS k o b)                 t = t

-- A join: strictly past the last event, it becomes the last.
joinUp-jt : ∀ {R Γ A X lo} j (c : Ctx R Γ A) (x : X ∈ Γ) acc (s : St Γ A) → lo <ᵖ j ≡ true → JT lo (plug c s) → JT j (plug (proj₂ (joinUp j c x acc)) s)
joinUp-jt j top                             () acc s h t
joinUp-jt j (inMap f c)                     x acc s h t with joinUp j c x (0 ∷ acc) | joinUp-jt j c x (0 ∷ acc) (mapS f s) h t
... | b , c″ | w = w
joinUp-jt j (inScan f z c)                  x acc s h t with joinUp j c x (0 ∷ acc) | joinUp-jt j c x (0 ∷ acc) (scanS f z s) h t
... | b , c″ | w = w
joinUp-jt j (inCut l a c)                   x acc s h t with joinUp j c x (0 ∷ acc) | joinUp-jt j c x (0 ∷ acc) (cutS l a s) h t
... | b , c″ | w = w
joinUp-jt j (inLn l c)                      x acc s h t with joinUp j c x (0 ∷ acc) | joinUp-jt j c x (0 ∷ acc) (lnS l s) h t
... | b , c″ | w = w
joinUp-jt j (inTake i p c)                  x acc s h t with joinUp j c x (0 ∷ acc) | joinUp-jt j c x (0 ∷ acc) (takeS i p s) h t
... | b , c″ | w = w
joinUp-jt j (inOuter op f d n ls c)         x acc s h t with joinUp j c x (0 ∷ acc) | joinUp-jt j c x (0 ∷ acc) (flatS op f d n s ls) h t
... | b , c″ | w = w
joinUp-jt j c@(inLanes op f d n o pre post c′) x acc s h t
  with joinUp j c′ x (dir c ∷ acc) | joinUp-jt j c′ x (dir c ∷ acc) (flatS op f d n o (pre ++ s ∷ post)) h t
... | b , c″ | w = w
joinUp-jt j (inSrc k b′ c)                  x acc s h t with joinUp j c x (0 ∷ acc) | joinUp-jt j c x (0 ∷ acc) (connS k s b′) h t
... | b , c″ | w = w
joinUp-jt j (inBody k o c)            (there x) acc s h t with joinUp j c x (1 ∷ acc) | joinUp-jt j c x (1 ∷ acc) (connS k o s) h t
... | b , c″ | w = w
joinUp-jt {lo = lo} j (inBody k o c) (here refl) acc s h t with CS.closed k
... | true  = jt-lift c {connS k o s} {connS k o s} (inj₂ h) (jt-mono (connS k o s) (inj₂ h)) t
... | false = jt-lift c {connS k o s} {connS (record k { subs = CS.subs k ++ [ (1 ∷ acc , j) ] }) o s} (inj₂ h)
  (λ (t₀ , tb , bl , u) → jt-mono o (inj₂ h) t₀ , jt-mono s (inj₂ h) tb
                        , ++⁺ (below-mono (inj₂ h) bl) (inj₁ refl ∷ []) , up-snoc (CS.subs k) u (below-< (CS.subs k) bl h)) t

------------------------------------------------------------------------
-- THE CHAIN

-- What a feed's next joiner needs: the last no later than where it is
-- fed, and the rest joined after it.
Feed : Pos → List (List ℕ × Pos) → Pos → Set
Feed p []             lo = ⊤
Feed p ((q , j) ∷ js) lo = lo ≤ᵖ (p ++ [ subᴾ j ]) × Asc j js

-- What a job resumed at `p` needs of the last event before it: read off
-- its tag alone.
Ready : Tag → Pos → Pos → Set
Ready go           p lo = lo ≤ᵖ p
Ready att          p lo = ⊤
Ready attBody      p lo = lo <ᵖ (p ++ [ ix 1 ]) ≡ true
Ready owed         p lo = ⊤
Ready (next i)     p lo = lo ≤ᵖ (p ++ [ ix i ])
Ready owedCp       p lo = lo ≤ᵖ (p ++ [ last ])
Ready owedCut      p lo = ⊤
Ready (feeding js) p lo = Feed p js lo

-- The stack, from the scope `S` the run is in: each job a scope
-- enclosing the one above it, ready from wherever that one leaves the
-- last.
data Chain (lo S : Pos) : List Job → Set where
  stop : Chain lo S []
  link : ∀ {π t p′ rs} → Under p′ S → (∀ lo′ → Settled S lo lo′ → Ready t p′ lo′ × Chain lo′ p′ rs) → Chain lo S ((π , t , p′) ∷ rs)

chain-adv : ∀ {lo lo′ S} rs → Settled S lo lo′ → Chain lo S rs → Chain lo′ S rs
chain-adv []      st ch      = stop
chain-adv (_ ∷ _) st (link u f) = link u λ lo″ st′ → f lo″ (settled-trans st st′)

chain-in : ∀ {lo S S′} rs → Under S S′ → Chain lo S rs → Chain lo S′ rs
chain-in []               u ch       = stop
chain-in ((π , t , p′) ∷ rs) u (link u′ f) = link (under-trans u′ u) λ lo′ st → f lo′ (settled-up u st)

-- A job pushed at the scope the run leaves for a deeper one.
frame : ∀ {lo S S′ π t} rs → Under S S′ → (∀ lo′ → Settled S′ lo lo′ → Ready t S lo′) → Chain lo S rs → Chain lo S′ ((π , t , S) ∷ rs)
frame rs u r ch = link u λ lo′ st → r lo′ st , chain-adv rs (settled-up u st) ch

-- A job pushed at the deeper scope itself.
frame-at : ∀ {lo S S′ π t} rs → Under S S′ → (∀ lo′ → Settled S′ lo lo′ → Ready t S′ lo′) → Chain lo S rs → Chain lo S′ ((π , t , S′) ∷ rs)
frame-at {S′ = S′} rs u r ch = link (under-refl S′) λ lo′ st → r lo′ st , chain-adv rs st (chain-in rs u ch)

------------------------------------------------------------------------
-- THE INVARIANT

Cur : ∀ {A} → Mode A → Pos → Pos → Set
Cur subscribing  p lo = lo <ᵖ p ≡ true
Cur absorbed     p lo = ⊤
Cur (resuming t) p lo = Ready t p lo
Cur (rising e)   p lo = lo ≤ᵖ p

Fwd : ∀ {R} → Pos → Conf R → Set
Fwd lo k = Cur (Conf.mode k) (Conf.pos k) lo × Chain lo (Conf.pos k) (Conf.rets k) × JT lo (plug (Conf.ctx k) (Conf.foc k))

-- What a step shows: nothing, the last event moving no earlier; or one
-- delivery, no earlier than the last, which becomes the last.
data Shows {R : Set} (lo : Pos) : Shown R → Pos → Set where
  quiet : ∀ {lo′} → lo ≤ᵖ lo′ → Shows lo [] lo′
  shown : ∀ {x e} → lo ≤ᵖ x → Shows lo ((x , e) ∷ []) x

-- Boxed, so that the configuration is read back off the type.
record At {R} (lo : Pos) (k : Conf R) : Set where
  constructor ⟪_⟫
  field un : Fwd lo k

Next : ∀ {R} → Pos → Conf R × Shown R → Set
Next lo (k′ , sh) = Σ Pos λ lo′ → Shows lo sh lo′ × At lo′ k′

stay : ∀ {R} {lo} {k : Conf R} → Fwd lo k → Next lo (k , [])
stay {lo = lo} f = lo , quiet (inj₁ refl) , ⟪ f ⟫

settle-cur : ∀ {B} d n {p lo} → lo ≤ᵖ p → Cur {B} (settle d n) p lo
settle-cur false n       le = tt
settle-cur true  zero    le = le
settle-cur true  (suc n) le = tt

------------------------------------------------------------------------
-- Each part of a step

feed-start : ∀ {R Γ A} (c : Ctx R Γ A) js {p lo} → lo ≤ᵖ p → Up js → Feed p (rooted c js) lo
feed-start c []             {p} le u = tt
feed-start c ((q , j) ∷ js) {p} le u = ≤ᵖ-child p le , asc-rooted c j js u

feed-next : ∀ p j js {lo lo′} → lo ≤ᵖ (p ++ [ subᴾ j ]) → Asc j js → Settled (p ++ [ subᴾ j ]) lo lo′ → Feed p js lo′
feed-next p j []               le a        st = tt
feed-next p j ((q , j₂) ∷ js) le (h , a) st = settled-next p (<ᵖ-sub j j₂ h) (sib p (<ᵖ-sub j j₂ h) le) st , a

begin-fwd : ∀ {R Γ A} (c : Ctx R Γ A) (o : PObs Γ A) p rs {lo} → lo <ᵖ p ≡ true → Chain lo p rs → JT lo (plug c (pend o))
          → Σ Pos λ lo′ → lo ≤ᵖ lo′ × Fwd lo′ (begin c o p rs)
begin-fwd c (cold x)          p rs {lo} lt ch t = lo , inj₁ refl , tt , ch , jt-plug c (λ _ → tt) t
begin-fwd c empty             p rs {lo} lt ch t =
  lo , inj₁ refl , ≤ᵖ-child p (inj₂ lt) , chain-in rs (under-child p last) ch , jt-plug c (λ _ → tt) t
begin-fwd c (of xs)           p rs {lo} lt ch t = lo , inj₁ refl , ≤ᵖ-child p (inj₂ lt) , ch , jt-plug c (λ _ → tt) t
begin-fwd c (map f s)         p rs {lo} lt ch t = lo , inj₁ refl , lt , ch , jt-plug c (λ _ → tt) t
begin-fwd c (scan f z s)      p rs {lo} lt ch t = lo , inj₁ refl , lt , ch , jt-plug c (λ _ → tt) t
begin-fwd c (takeWhile i q s) p rs {lo} lt ch t =
  lo , inj₁ refl , lt , frame-at rs (under-refl p) (λ _ _ → tt) ch , jt-plug c (λ _ → tt) t
begin-fwd c (flatMap op f s)  p rs {lo} lt ch t =
  lo , inj₁ refl , lt , frame-at rs (under-refl p) (λ _ _ → tt) ch , jt-plug c (λ _ → tt , tt) t
begin-fwd c (connect s b)     p rs {lo} lt ch t =
  lo , inj₁ refl , <-child p {ix 0} {lo} (inj₂ lt)
     , frame rs (under-child p (ix 0)) (λ lo′ st → settled-next< p {ix 0} {ix 1} refl (<-child p {ix 1} {lo} (inj₂ lt)) st) ch
     , jt-plug c (λ _ → tt , tt , [] , tt) t
begin-fwd c (connected x)     p rs {lo} lt ch t
  with joinUp p c x [] | joinUp-jt p c x [] doneS lt (jt-plug c (λ _ → tt) t) | joinUp-jt p c x [] (joinS p true x) lt (jt-plug c (λ _ → tt) t)
... | true  , c′ | w | _ = p , inj₂ lt , ≤ᵖ-child p (inj₁ refl) , chain-in rs (under-child p last) (chain-adv rs (settled-at (inj₂ lt)) ch) , w
... | false , c′ | _ | w = p , inj₂ lt , tt , chain-adv rs (settled-at (inj₂ lt)) ch , w
begin-fwd c (defer l)         p rs {lo} lt ch t =
  lo , inj₁ refl , <-child p {ix 1} {lo} (inj₂ lt) , chain-in rs (under-child p (ix 1)) ch , jt-plug c (λ _ → tt) t

start-fwd : ∀ {R Γ A B} (c : Ctx R Γ B) op (f : A → PObs Γ B) d n o ls a p rs {lo}
          → lo ≤ᵖ p → Chain lo p rs → JT lo (plug c (flatS op f d n o ls)) → Fwd lo (start c op f d n o ls a p rs)
start-fwd c op f d n o ls a p rs {lo} le ch t with closed c
... | true  = tt , ch , t
... | false =
  <-child p {ix 1} {lo} le , frame-at rs (under-child p (ix 1)) (λ _ _ → tt) ch
  , jt-plug c (λ (t₀ , tl) → t₀ , jtL-snoc ls tl tt) t

admit-fwd : ∀ {R Γ A B} (c : Ctx R Γ B) op (f : A → PObs Γ B) d n o ls a p rs {lo}
          → lo ≤ᵖ p → Chain lo p rs → JT lo (plug c (flatS op f d n o ls)) → Fwd lo (admit c op f d n o ls a p rs)
admit-fwd c (mergeᶠ nothing)  f d n o ls a p rs le ch t = start-fwd c _ f d n o ls a p rs le ch t
admit-fwd c (mergeᶠ (just m)) f d n o ls a p rs le ch t = tt , ch , t
admit-fwd c switchᶠ           f d n o ls a p rs le ch t =
  start-fwd c switchᶠ f d 0 o (killAll ls) a p rs le ch
    (jt-plug c {flatS switchᶠ f d n o ls} {flatS switchᶠ f d 0 o (killAll ls)} (λ (t₀ , tl) → t₀ , killAll-jt ls tl) t)
admit-fwd c exhaustᶠ          f d n o ls a p rs le ch t with n ≡ᵇ 0
... | true  = start-fwd c exhaustᶠ f d n o ls a p rs le ch t
... | false = tt , ch , t

rise-fwd : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) e p rs {lo} → lo ≤ᵖ p → Chain lo p rs → JT lo (plug c s) → Next lo (rise c s e p rs)
rise-fwd top                             s e      p rs le ch t = p , shown le , ⟪ tt , chain-adv rs (settled-at le) ch , jt-mono s le t ⟫
rise-fwd (inMap f c)                     s e      p rs le ch t = stay (le , ch , t)
rise-fwd (inScan f z c)                  s (nx a) p rs le ch t = stay (le , ch , jt-plug c {scanS f z s} {scanS f (f z a) s} (λ x → x) t)
rise-fwd (inScan f z c)                  s cp     p rs le ch t = stay (le , ch , t)
rise-fwd (inCut true a c)                s e      p rs le ch t = stay (le , ch , t)
rise-fwd (inCut false a c)               s e      p rs le ch t = stay (tt , ch , t)
rise-fwd (inLn b c)                      s e      p rs le ch t = stay (le , ch , t)
rise-fwd (inTake i q c)                  s (nx a) p rs le ch t with q a | i
... | true  | _     = stay (le , ch , t)
... | false | true  = stay (≤ᵖ-child p le , frame rs (under-child p (ix 0)) (λ lo′ st → settled-next p refl (≤ᵖ-child p le) st) ch , t)
... | false | false = stay (≤ᵖ-child p le , frame rs (under-child p last) (λ _ _ → tt) ch , t)
rise-fwd (inTake i q c)                  s cp     p rs le ch t = stay (le , ch , t)
rise-fwd (inOuter op f d n ls c)         s (nx a) p rs le ch t = stay (admit-fwd c op f d n s ls a p rs le ch t)
rise-fwd (inOuter op f d n ls c)         s cp     p rs le ch t =
  stay (settle-cur true n le , ch , jt-plug c {flatS op f d n s ls} {flatS op f true n s ls} (λ x → x) t)
rise-fwd (inLanes op f d n o pre post c) s (nx b) p rs le ch t = stay (le , ch , t)
rise-fwd (inLanes op f d n o pre post c) s cp     p rs le ch t =
  stay (settle-cur d (pred n) le , ch
       , jt-plug c {flatS op f d n o (pre ++ s ∷ post)} {flatS op f d (pred n) o (pre ++ ended s ∷ post)} (λ (t₀ , tl) → t₀ , jtL-mid pre post (inj₁ refl) (ended-jt s) tl) t)
rise-fwd (inSrc k b c)                   s (nx a) p rs le ch t =
  stay (feed-start c (CS.subs k) le (proj₂ (proj₂ (proj₂ (jt-hole c (connS k s b) t))))
       , ch , jt-plug c {connS k s b} {connS (record k { feeds = nx a ∷ CS.feeds k }) s b} (λ x → x) t)
rise-fwd (inSrc k b c)                   s cp     p rs le ch t =
  stay (feed-start c (CS.subs k) le (proj₂ (proj₂ (proj₂ (jt-hole c (connS k s b) t))))
       , ch , jt-plug c {connS k s b} {connS (record k { closed = true ; feeds = cp ∷ CS.feeds k }) s b} (λ x → x) t)
rise-fwd (inBody k o c)                  s (nx b) p rs le ch t = stay (le , ch , t)
rise-fwd (inBody k o c)                  s cp     p rs le ch t = stay (le , frame rs (under-refl p) (λ _ _ → tt) ch , t)

feedOn-fwd : ∀ {R Γ X B} (c : Ctx R Γ B) (k : CS X) o b js p rs {lo} → TagR (plug c (connS k o b)) (feeding js)
           → Feed p js lo → Chain lo p rs → JT lo (plug c (connS k o b)) → Fwd lo (feedOn c k o b js p rs)
feedOn-fwd c k o b []             p rs tr fd ch t =
  tt , ch , jt-plug c {connS k o b} {connS (record k { feeds = drop₁ (CS.feeds k) }) o b} (λ x → x) t
feedOn-fwd c k o b ((q , j) ∷ js) p rs (r ∷ tr) (le , a) ch t
  with downs q top (plug c (connS k o b)) | downs-lands q top (plug c (connS k o b)) r
... | just (_ , _ , c′ , s′) | e =
  le , frame rs (under-child p (subᴾ j)) (λ lo′ st → feed-next p j js le a st) ch , subst (JT _) (sym e) t
... | nothing | ()

resumeR-fwd : ∀ {R Γ A} (c : Ctx R Γ A) {s : St Γ A} {t} (r : Res s t) p rs {lo} → TagR (plug c s) t
            → Ready t p lo → Chain lo p rs → JT lo (plug c s) → Fwd lo (resumeR c r p rs)
resumeR-fwd c (ofR xs i) p rs tr rd ch t with closed c | xs
... | true  | _       = tt , ch , jt-plug c (λ _ → tt) t
... | false | []      = sib p refl rd , chain-in rs (under-child p last) ch , jt-plug c (λ _ → tt) t
... | false | x ∷ xs′ =
  rd , frame rs (under-child p (ix i)) (λ lo′ st → settled-next p (<ᵖ-ix i) (sib p (<ᵖ-ix i) rd) st) ch , jt-plug c (λ _ → tt) t
resumeR-fwd c (attR true a s)  p rs tr rd ch t = tt , ch , jt-plug c {cutS true a s} {cutS true true s} (λ x → x) t
resumeR-fwd c (attR false a s) p rs tr rd ch t = tt , ch , jt-plug c {cutS false a s} {cutS false true (unsub s)} (unsub-jt s) t
resumeR-fwd c (cpR i q s)      p rs tr rd ch t = rd , frame rs (under-child p last) (λ _ _ → tt) ch , t
resumeR-fwd c (cutR i q s)     p rs tr rd ch t = tt , ch , jt-plug c {takeS i q s} {takeS i q (cut s)} (cut-jt s) t
resumeR-fwd c (feedR k o b js) p rs tr rd ch t = feedOn-fwd c k o b js p rs tr rd ch t
resumeR-fwd c (bodyR k o b)    p rs tr rd ch t =
  rd , frame-at rs (under-child p (ix 1)) (λ _ _ → tt) ch , jt-plug c {connS k o b} {connS (record k { bodyAtt = true }) o b} (λ x → x) t
resumeR-fwd c (srcR k o b)     p rs tr rd ch t with CS.srcLive k
... | true  = tt , ch , jt-plug c (λ x → x) t
... | false = tt , ch , jt-plug c (λ (t₀ , tb , bd) → unsub-jt o t₀ , tb , bd) t
resumeR-fwd c (endR k o b)     p rs tr rd ch t with CS.srcAtt k
... | true  = tt , ch , jt-plug c (λ (t₀ , tb , bd) → unsub-jt o t₀ , tb , bd) t
... | false = tt , ch , jt-plug c (λ x → x) t
resumeR-fwd c (joinR j x)      p rs tr rd ch t with fedUp c x
... | just e  = rd , ch , t
... | nothing = tt , ch , t
resumeR-fwd c idle             p rs tr rd ch t = tt , ch , t

------------------------------------------------------------------------
-- THE ORDER, ACROSS EVERY STEP

stepAt-fwd : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) m p rs {lo} → V c s (modeJobs m ++ rs)
           → Cur m p lo → Chain lo p rs → JT lo (plug c s) → Next lo (stepAt c s m p rs)
stepAt-fwd c s (resuming t) p rs (a , g) cu ch jt =
  stay (resumeR-fwd c (res s t) p rs (proj₁ (tag-of t {rs} a)) cu ch jt)
stepAt-fwd c s (rising e)   p rs v cu ch jt = rise-fwd c s e p rs cu ch jt
stepAt-fwd c (pend o) subscribing p rs v cu ch jt with begin-fwd c o p rs cu ch jt
... | lo′ , le , f = lo′ , quiet le , ⟪ f ⟫
stepAt-fwd c (ofS xs)              subscribing p rs v cu ch jt = stay (cu , ch , jt)
stepAt-fwd c doneS                 subscribing p rs v cu ch jt = stay (cu , ch , jt)
stepAt-fwd c (joinS j g x)         subscribing p rs v cu ch jt = stay (cu , ch , jt)
stepAt-fwd c (mapS f s)            subscribing p rs v cu ch jt = stay (cu , ch , jt)
stepAt-fwd c (scanS f z s)         subscribing p rs v cu ch jt = stay (cu , ch , jt)
stepAt-fwd c (cutS l a s)          subscribing p rs v cu ch jt = stay (cu , ch , jt)
stepAt-fwd c (lnS b s)             subscribing p rs v cu ch jt = stay (cu , ch , jt)
stepAt-fwd c (takeS i q s)         subscribing p rs v cu ch jt = stay (cu , ch , jt)
stepAt-fwd c (flatS op f d n o ls) subscribing p rs v cu ch jt = stay (cu , ch , jt)
stepAt-fwd c (connS k o b)         subscribing p rs v cu ch jt = stay (cu , ch , jt)
stepAt-fwd c s absorbed p [] v cu ch jt = stay (cu , ch , jt)
stepAt-fwd c s absorbed p ((q , t , p′) ∷ rs) {lo} (r ∷ a , g) cu (link u f) jt
  with downs q top (plug c s) | downs-lands q top (plug c s) (proj₁ r)
... | just (_ , _ , c′ , s′) | e = stay (proj₁ (f lo settled-refl) , proj₂ (f lo settled-refl) , subst (JT lo) (sym e) jt)
... | nothing | ()

step-fwd : ∀ {R} (k : Conf R) {lo} → Valid k → Fwd lo k → Next lo (step k)
step-fwd ⟨ c , s , m , p , rs ⟩ v (cu , ch , jt) = stepAt-fwd c s m p rs v cu ch jt

-- The shown positions, rising from `lo`.
Rises : Pos → List Pos → Set
Rises lo []       = ⊤
Rises lo (x ∷ xs) = lo ≤ᵖ x × Rises x xs

marks : ∀ {R} → Shown R → List Pos
marks []             = []
marks ((x , _) ∷ sh) = x ∷ marks sh

rises-from : ∀ {lo lo′} xs → lo ≤ᵖ lo′ → Rises lo′ xs → Rises lo xs
rises-from []       le r        = tt
rises-from (x ∷ xs) le (h , r) = ≤ᵖ-trans le h , r

run-rises : ∀ {R} n (k : Conf R) {lo} → Valid k → Fwd lo k → Rises lo (marks (runN n k))
run-rises zero    k v f = tt
run-rises (suc n) k v f with step k | step-ok k v | step-fwd k v f
... | k′ , []                | v′ | lo′ , quiet le , ⟪ f′ ⟫ = rises-from (marks (runN n k′)) le (run-rises n k′ v′ f′)
... | k′ , (p , cp) ∷ []     | v′ | lo′ , shown le , _      = le , tt
... | k′ , (p , nx a) ∷ []   | v′ | lo′ , shown le , ⟪ f′ ⟫ = le , run-rises n k′ v′ f′
... | k′ , _ ∷ _ ∷ _         | v′ | lo′ , () , _

-- THE ORDER: however far the machine is run, what it shows moves forward.
ascends : ∀ {R} (o : PObs [] R) n → Rises [] (marks (runN n (load o)))
ascends o n = run-rises n (load o) (load-ok o) (refl , stop , tt)
