{-# OPTIONS --guardedness #-}

-- WHAT A SILENT STEP SPENDS.  Every silent step lowers the work its
-- configuration has left (`adequacy.Ghost`'s `work`), or is one of the
-- steps whose work may grow (`Skipped`): an outer's value or a source's
-- event absorbed, a lane's end starting a waiting value's lane, a defer
-- begun, a cold's stall or close.  Each of those drops a leading skip of
-- what the configuration means (`adequacy.Content`).
--
-- No bound holds on a step keeping its meaning alone: a cold whose frames
-- are all empty, one per tick forever, means skips only, so each close
-- keeps its meaning at every depth and leaves what it owes one stop.
module adequacy.Engine.Spent where

open import Data.Bool using (true; false; not; _∧_; if_then_else_)
open import Data.List using (List; []; _∷_; _ʳ++_; [_]; length; null)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; z≤n; s≤s; pred; _≡ᵇ_)
open import Data.Nat.Properties using (≤-refl; n≤1+n; n<1+n; m≤n⇒m<n∨m≡n; +-suc; +-assoc; +-monoʳ-<; +-monoˡ-<; +-monoʳ-≤;
  +-monoˡ-≤; +-mono-≤)
open import Data.Nat.Tactic.RingSolver using (solve-∀)
open import Data.Product using (_,_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)

open import Tree using (Obs; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.MonotonicList.Events using (Timeline; fixed; fresh; timelineAt; done; quiet; at; emit; stall; close; ix; root)
open import operation.PureObservable using (play; ending; over; opening; module Machine; module Driver)
open import adequacy.Engine.Work using (run; tapeW; coldW; size; one; attW; oweW; just?; csW; owed; owedL; tornC; torn; tornL; height)
open import adequacy.Engine.Inv using (Inv; module Inv; module Base; Owns; ofO; attO; cpO; cutO; bodyO; srcAttO; owedO; joinO;
  leafO; search-hit)
open import adequacy.Ghost using (module Ghosting)
open Machine using (St; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
  Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody; plug; closed; closedUp;
  cs; attached; attAt; free; cpAt; cutAt; overAt; nx; cp; _⊕_;
  Conf; ⟨_,_,_,_⟩; subscribing; absorbed; rising; Mark; ofM; attM; bodyM; srcAttM; owedM; cpM; cutM; joinM; leafM;
  search; found; ended; alive; unsub; killAll; unsubIf)
  renaming (cut to cutᴹ; run to runᴹ)

------------------------------------------------------------------------
-- What a tree owes, split at a hole

private
  a+[b+c]+d : ∀ a b c d → a + (b + (c + d)) ≡ (a + (b + c)) + d
  a+[b+c]+d = solve-∀

  a+1+[b+c]+d : ∀ a b c d → a + (1 + (b + (c + d))) ≡ (a + (1 + (b + c))) + d
  a+1+[b+c]+d = solve-∀

  lanes-split : ∀ a p s q l o → a + ((p + (s + q)) + (l + o)) ≡ (a + ((p + q) + (l + o))) + s
  lanes-split = solve-∀

  lanes-split₁ : ∀ a p s q l o → a + (1 + ((p + (s + q)) + (l + o))) ≡ (a + (1 + ((p + q) + (l + o)))) + s
  lanes-split₁ = solve-∀

  src-split : ∀ a k s b → a + ((k + s) + b) ≡ (a + (k + b)) + s
  src-split = solve-∀

  rev-split : ∀ p x y → p + (x + y) ≡ (x + p) + y
  rev-split = solve-∀

  att-split : ∀ x y a b → ((x + 1) + y) + a + b ≡ 1 + (((x + 0) + y) + a + b)
  att-split = solve-∀

-- A lane list read back to front, as a lane's context keeps it.
owedL-ʳ++ : ∀ {Γ A} (pre ys : List (St Γ A)) → owedL (pre ʳ++ ys) ≡ owedL pre + owedL ys
owedL-ʳ++ []        ys = refl
owedL-ʳ++ (x ∷ pre) ys = trans (owedL-ʳ++ pre (x ∷ ys)) (rev-split (owedL pre) (owed x) (owedL ys))

-- What a context owes beside its hole.
ctxW : ∀ {R Γ A} → Ctx R Γ A → ℕ
ctxW top                                   = 0
ctxW (inMap f c)                           = ctxW c
ctxW (inScan f z c)                        = ctxW c
ctxW (inCut l a c)                         = ctxW c + attW a
ctxW (inLn b c)                            = ctxW c + one b
ctxW (inTake i q w c)                      = ctxW c + oweW w
ctxW (inOuter op f true n q ls c)          = ctxW c + (owedL ls + length q)
ctxW (inOuter op f false n q ls c)         = ctxW c + (1 + (owedL ls + length q))
ctxW (inLanes op f true n q o pre post c)  = ctxW c + ((owedL pre + owedL post) + (length q + owed o))
ctxW (inLanes op f false n q o pre post c) = ctxW c + (1 + ((owedL pre + owedL post) + (length q + owed o)))
ctxW (inSrc k b c)                         = ctxW c + (csW k + owed b)
ctxW (inBody k o c)                        = ctxW c + (csW k + owed o)

plug-owed : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) → owed (plug c s) ≡ ctxW c + owed s
plug-owed top                                   s = refl
plug-owed (inMap f c)                           s = plug-owed c (mapS f s)
plug-owed (inScan f z c)                        s = plug-owed c (scanS f z s)
plug-owed (inCut l a c)                         s = trans (plug-owed c (cutS l a s)) (sym (+-assoc (ctxW c) (attW a) (owed s)))
plug-owed (inLn b c)                            s = trans (plug-owed c (lnS b s)) (sym (+-assoc (ctxW c) (one b) (owed s)))
plug-owed (inTake i q w c)                      s = trans (plug-owed c (takeS i q w s)) (sym (+-assoc (ctxW c) (oweW w) (owed s)))
plug-owed (inOuter op f true n q ls c)          s =
  trans (plug-owed c (flatS op f true n q s ls)) (a+[b+c]+d (ctxW c) (owedL ls) (length q) (owed s))
plug-owed (inOuter op f false n q ls c)         s =
  trans (plug-owed c (flatS op f false n q s ls)) (a+1+[b+c]+d (ctxW c) (owedL ls) (length q) (owed s))
plug-owed (inLanes op f true n q o pre post c)  s =
  trans (plug-owed c (flatS op f true n q o (pre ʳ++ s ∷ post)))
    (trans (cong (λ x → ctxW c + (x + (length q + owed o))) (owedL-ʳ++ pre (s ∷ post)))
      (lanes-split (ctxW c) (owedL pre) (owed s) (owedL post) (length q) (owed o)))
plug-owed (inLanes op f false n q o pre post c) s =
  trans (plug-owed c (flatS op f false n q o (pre ʳ++ s ∷ post)))
    (trans (cong (λ x → ctxW c + (1 + (x + (length q + owed o)))) (owedL-ʳ++ pre (s ∷ post)))
      (lanes-split₁ (ctxW c) (owedL pre) (owed s) (owedL post) (length q) (owed o)))
plug-owed (inSrc k b c)                         s = trans (plug-owed c (connS k s b)) (src-split (ctxW c) (csW k) (owed s) (owed b))
plug-owed (inBody k o c)                        s = trans (plug-owed c (connS k o s)) (sym (+-assoc (ctxW c) (csW k + owed o) (owed s)))

-- What a tree owes moves with what its hole owes.
plug-≤ : ∀ {R Γ A} (c : Ctx R Γ A) (s s′ : St Γ A) → owed s′ ≤ owed s → owed (plug c s′) ≤ owed (plug c s)
plug-≤ c s s′ le rewrite plug-owed c s | plug-owed c s′ = +-monoʳ-≤ (ctxW c) le

plug-< : ∀ {R Γ A} (c : Ctx R Γ A) (s s′ : St Γ A) → suc (owed s′) ≤ owed s → suc (owed (plug c s′)) ≤ owed (plug c s)
plug-< c s s′ le rewrite plug-owed c s | plug-owed c s′ = subst (_≤ ctxW c + owed s) (+-suc (ctxW c) (owed s′)) (+-monoʳ-≤ (ctxW c) le)

------------------------------------------------------------------------
-- The teardowns a tree owes, monotone in its hole

tornL-ʳ++ : ∀ {Γ A} (pre : List (St Γ A)) {ys ys′} → tornL ys′ < tornL ys → tornL (pre ʳ++ ys′) < tornL (pre ʳ++ ys)
tornL-ʳ++ []        lt = lt
tornL-ʳ++ (x ∷ pre) lt = tornL-ʳ++ pre (+-monoʳ-< (torn x) lt)

plug-torn : ∀ {R Γ A} (c : Ctx R Γ A) (s s′ : St Γ A) → torn s′ < torn s → torn (plug c s′) < torn (plug c s)
plug-torn top                               s s′ lt = lt
plug-torn (inMap f c)                       s s′ lt = plug-torn c (mapS f s) (mapS f s′) lt
plug-torn (inScan f z c)                    s s′ lt = plug-torn c (scanS f z s) (scanS f z s′) lt
plug-torn (inCut l a c)                     s s′ lt = plug-torn c (cutS l a s) (cutS l a s′) lt
plug-torn (inLn b c)                        s s′ lt = plug-torn c (lnS b s) (lnS b s′) lt
plug-torn (inTake i q w c)                  s s′ lt = plug-torn c (takeS i q w s) (takeS i q w s′) lt
plug-torn (inOuter op f d n q ls c)         s s′ lt =
  plug-torn c (flatS op f d n q s ls) (flatS op f d n q s′ ls) (+-monoʳ-< (tornL ls) lt)
plug-torn (inLanes op f d n q o pre post c) s s′ lt =
  plug-torn c (flatS op f d n q o (pre ʳ++ s ∷ post)) (flatS op f d n q o (pre ʳ++ s′ ∷ post))
    (+-monoˡ-< (torn o) (tornL-ʳ++ pre (+-monoˡ-< (tornL post) lt)))
plug-torn (inSrc k b c)                     s s′ lt =
  plug-torn c (connS k s b) (connS k s′ b) (+-monoˡ-< (torn b) (+-monoʳ-< (tornC k) lt))
plug-torn (inBody k o c)                    s s′ lt = plug-torn c (connS k o s) (connS k o s′) (+-monoʳ-< (tornC k + torn o) lt)

------------------------------------------------------------------------
-- An unsubscribe owes no more, and adds no teardown owed

mutual
  unsub-≤ : ∀ {Γ A} (s : St Γ A) → owed (proj₁ (unsub s)) ≤ owed s
  unsub-≤ (pend o)                    = ≤-refl
  unsub-≤ (coldS true l)              = ≤-refl
  unsub-≤ (coldS false l)             = ≤-refl
  unsub-≤ (ofS i p xs)                = ≤-refl
  unsub-≤ doneS                       = ≤-refl
  unsub-≤ (mapS f s)                  = unsub-≤ s
  unsub-≤ (scanS f z s)               = unsub-≤ s
  unsub-≤ (cutS l a s)                = ≤-refl
  unsub-≤ (lnS b s)                   = ≤-refl
  unsub-≤ (takeS i q w s)             = +-monoʳ-≤ (oweW w) (cut-≤ s)
  unsub-≤ (flatS op f true n q o ls)  = +-mono-≤ (killAll-≤ ls) (+-monoʳ-≤ (length q) (cut-≤ o))
  unsub-≤ (flatS op f false n q o ls) = s≤s (+-mono-≤ (killAll-≤ ls) (+-monoʳ-≤ (length q) (cut-≤ o)))
  unsub-≤ (connS k o b)               = +-mono-≤ (+-monoʳ-≤ (csW k) (unsub-≤ o)) (unsub-≤ b)
  unsub-≤ (joinS j g x ib)            = z≤n

  cut-≤ : ∀ {Γ A} (s : St Γ A) → owed (proj₁ (cutᴹ s)) ≤ owed s
  cut-≤ (cutS l attached s)     = unsub-≤ s
  cut-≤ (cutS l (attAt p) s)    = ≤-refl
  cut-≤ (pend o)                = ≤-refl
  cut-≤ (coldS b l)             = ≤-refl
  cut-≤ (ofS i p xs)            = ≤-refl
  cut-≤ doneS                   = ≤-refl
  cut-≤ (mapS f s)              = ≤-refl
  cut-≤ (scanS f z s)           = ≤-refl
  cut-≤ (lnS b s)               = ≤-refl
  cut-≤ (takeS i q w s)         = ≤-refl
  cut-≤ (flatS op f d n q o ls) = ≤-refl
  cut-≤ (connS k o b)           = ≤-refl
  cut-≤ (joinS j g x ib)        = ≤-refl

  killAll-≤ : ∀ {Γ B} (ls : List (St Γ B)) → owedL (proj₁ (killAll ls)) ≤ owedL ls
  killAll-≤ []                            = ≤-refl
  killAll-≤ (lnS true s ∷ ls)             = +-mono-≤ (≤-step (cut-≤ s)) (killAll-≤ ls)
  killAll-≤ (lnS false s ∷ ls)            = +-monoʳ-≤ (owed s) (killAll-≤ ls)
  killAll-≤ (pend o ∷ ls)                 = +-monoʳ-≤ (size o) (killAll-≤ ls)
  killAll-≤ (coldS b l ∷ ls)              = +-monoʳ-≤ (tapeW l) (killAll-≤ ls)
  killAll-≤ (ofS i p xs ∷ ls)             = +-monoʳ-≤ (suc (length xs)) (killAll-≤ ls)
  killAll-≤ (doneS ∷ ls)                  = killAll-≤ ls
  killAll-≤ (mapS f s ∷ ls)               = +-monoʳ-≤ (owed s) (killAll-≤ ls)
  killAll-≤ (scanS f z s ∷ ls)            = +-monoʳ-≤ (owed s) (killAll-≤ ls)
  killAll-≤ (cutS l a s ∷ ls)             = +-monoʳ-≤ (owed (cutS l a s)) (killAll-≤ ls)
  killAll-≤ (takeS i q w s ∷ ls)          = +-monoʳ-≤ (owed (takeS i q w s)) (killAll-≤ ls)
  killAll-≤ (flatS op f d n q o ls′ ∷ ls) = +-monoʳ-≤ (owed (flatS op f d n q o ls′)) (killAll-≤ ls)
  killAll-≤ (connS k o b ∷ ls)            = +-monoʳ-≤ (owed (connS k o b)) (killAll-≤ ls)
  killAll-≤ (joinS j g x ib ∷ ls)         = +-monoʳ-≤ (length ib) (killAll-≤ ls)

  ≤-step : ∀ {m n} → m ≤ n → m ≤ suc n
  ≤-step z≤n      = z≤n
  ≤-step (s≤s le) = s≤s (≤-step le)

unsubIf-≤ : ∀ {Γ A} b (s : St Γ A) → owed (proj₁ (unsubIf b s)) ≤ owed s
unsubIf-≤ true  s = unsub-≤ s
unsubIf-≤ false s = ≤-refl

mutual
  unsub-torn : ∀ {Γ A} (s : St Γ A) → torn (proj₁ (unsub s)) ≤ torn s
  unsub-torn (pend o)                = ≤-refl
  unsub-torn (coldS true l)          = ≤-refl
  unsub-torn (coldS false l)         = ≤-refl
  unsub-torn (ofS i p xs)            = ≤-refl
  unsub-torn doneS                   = ≤-refl
  unsub-torn (mapS f s)              = unsub-torn s
  unsub-torn (scanS f z s)           = unsub-torn s
  unsub-torn (cutS l a s)            = ≤-refl
  unsub-torn (lnS b s)               = ≤-refl
  unsub-torn (takeS i q w s)         = cut-torn s
  unsub-torn (flatS op f d n q o ls) = +-mono-≤ (killAll-torn ls) (cut-torn o)
  unsub-torn (connS k o b)           = +-mono-≤ (+-monoʳ-≤ (tornC k) (unsub-torn o)) (unsub-torn b)
  unsub-torn (joinS j g x ib)        = ≤-refl

  cut-torn : ∀ {Γ A} (s : St Γ A) → torn (proj₁ (cutᴹ s)) ≤ torn s
  cut-torn (cutS l attached s)     = unsub-torn s
  cut-torn (cutS l (attAt p) s)    = ≤-refl
  cut-torn (pend o)                = ≤-refl
  cut-torn (coldS b l)             = ≤-refl
  cut-torn (ofS i p xs)            = ≤-refl
  cut-torn doneS                   = ≤-refl
  cut-torn (mapS f s)              = ≤-refl
  cut-torn (scanS f z s)           = ≤-refl
  cut-torn (lnS b s)               = ≤-refl
  cut-torn (takeS i q w s)         = ≤-refl
  cut-torn (flatS op f d n q o ls) = ≤-refl
  cut-torn (connS k o b)           = ≤-refl
  cut-torn (joinS j g x ib)        = ≤-refl

  killAll-torn : ∀ {Γ B} (ls : List (St Γ B)) → tornL (proj₁ (killAll ls)) ≤ tornL ls
  killAll-torn []                            = ≤-refl
  killAll-torn (lnS true s ∷ ls)             = +-mono-≤ (cut-torn s) (killAll-torn ls)
  killAll-torn (lnS false s ∷ ls)            = +-monoʳ-≤ (torn s) (killAll-torn ls)
  killAll-torn (pend o ∷ ls)                 = killAll-torn ls
  killAll-torn (coldS b l ∷ ls)              = killAll-torn ls
  killAll-torn (ofS i p xs ∷ ls)             = killAll-torn ls
  killAll-torn (doneS ∷ ls)                  = killAll-torn ls
  killAll-torn (mapS f s ∷ ls)               = +-monoʳ-≤ (torn s) (killAll-torn ls)
  killAll-torn (scanS f z s ∷ ls)            = +-monoʳ-≤ (torn s) (killAll-torn ls)
  killAll-torn (cutS l a s ∷ ls)             = +-monoʳ-≤ (torn s) (killAll-torn ls)
  killAll-torn (takeS i q w s ∷ ls)          = +-monoʳ-≤ (torn s) (killAll-torn ls)
  killAll-torn (flatS op f d n q o ls′ ∷ ls) = +-monoʳ-≤ (torn (flatS op f d n q o ls′)) (killAll-torn ls)
  killAll-torn (connS k o b ∷ ls)            = +-monoʳ-≤ (torn (connS k o b)) (killAll-torn ls)
  killAll-torn (joinS j g x ib ∷ ls)         = killAll-torn ls

unsubIf-torn : ∀ {Γ A} b (s : St Γ A) → torn (proj₁ (unsubIf b s)) ≤ torn s
unsubIf-torn true  s = unsub-torn s
unsubIf-torn false s = ≤-refl

-- A lane's end retires it.
ended-≤ : ∀ {Γ B} (s : St Γ B) → owed (ended s) ≤ owed s
ended-≤ (lnS true (cutS l a s))         = n≤1+n _
ended-≤ (lnS false (cutS l a s))        = ≤-refl
ended-≤ (lnS b (pend o))                = ≤-refl
ended-≤ (lnS b (coldS b′ l))            = ≤-refl
ended-≤ (lnS b (ofS i p xs))            = ≤-refl
ended-≤ (lnS b doneS)                   = ≤-refl
ended-≤ (lnS b (mapS f s))              = ≤-refl
ended-≤ (lnS b (scanS f z s))           = ≤-refl
ended-≤ (lnS b (lnS b′ s))              = ≤-refl
ended-≤ (lnS b (takeS i q w s))         = ≤-refl
ended-≤ (lnS b (flatS op f d n q o ls)) = ≤-refl
ended-≤ (lnS b (connS k o b′))          = ≤-refl
ended-≤ (lnS b (joinS j g x ib))        = ≤-refl
ended-≤ (pend o)                        = ≤-refl
ended-≤ (coldS b l)                     = ≤-refl
ended-≤ (ofS i p xs)                    = ≤-refl
ended-≤ doneS                           = ≤-refl
ended-≤ (mapS f s)                      = ≤-refl
ended-≤ (scanS f z s)                   = ≤-refl
ended-≤ (cutS l a s)                    = ≤-refl
ended-≤ (takeS i q w s)                 = ≤-refl
ended-≤ (flatS op f d n q o ls)         = ≤-refl
ended-≤ (connS k o b)                   = ≤-refl
ended-≤ (joinS j g x ib)                = ≤-refl

-- A lane, in place, owing no more.
lanes-≤ : ∀ {Γ A B} op (f : A → Obs Timeline Γ B) d n n′ q (o : St Γ A) pre post (s s′ : St Γ B) → owed s′ ≤ owed s
        → owed (flatS op f d n′ q o (pre ʳ++ s′ ∷ post)) ≤ owed (flatS op f d n q o (pre ʳ++ s ∷ post))
lanes-≤ op f true n n′ q o pre post s s′ le rewrite owedL-ʳ++ pre (s ∷ post) | owedL-ʳ++ pre (s′ ∷ post) =
  +-monoˡ-≤ (length q + owed o) (+-monoʳ-≤ (owedL pre) (+-monoˡ-≤ (owedL post) le))
lanes-≤ op f false n n′ q o pre post s s′ le rewrite owedL-ʳ++ pre (s ∷ post) | owedL-ʳ++ pre (s′ ∷ post) =
  s≤s (+-monoˡ-≤ (length q + owed o) (+-monoʳ-≤ (owedL pre) (+-monoˡ-≤ (owedL post) le)))

-- A cold, subscribed, owes less than its program did.
opening-< : ∀ {A} (x : Timeline A) p → tapeW (opening p (timelineAt x p)) < 2 + coldW x
opening-< (fixed (at zero le b))    p = ≤-refl
opening-< (fixed (at (suc t) le b)) p = ≤-refl
opening-< (fixed done)              p = s≤s (s≤s z≤n)
opening-< (fixed quiet)             p = s≤s z≤n
opening-< fresh                     p = ≤-refl

------------------------------------------------------------------------
-- The silent steps

module Spending (R : Set) where
  open Driver R using (Step; silent; step; took; played)
  open Ghosting R using (Measure; work; _≺_)

  -- The silent steps whose work may grow.
  data Skipped : Conf R → Set₁ where
    outerᵏ : ∀ {Γ A B op d n q ls} {f : A → Obs Timeline Γ B} {c : Ctx R Γ B} {o : St Γ A} {a p}
           → Skipped ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩
    laneᵏ  : ∀ {Γ A B op d n a q pre post} {f : A → Obs Timeline Γ B} {c : Ctx R Γ B} {o : St Γ A} {s : St Γ B} {p}
           → alive s ≡ true → Skipped ⟨ inLanes op f d n (a ∷ q) o pre post c , s , rising cp , p ⟩
    srcᵏ   : ∀ {Γ X B k} {b : St (X ∷ Γ) B} {c : Ctx R Γ B} {s : St Γ X} {e p}
           → Skipped ⟨ inSrc k b c , s , rising e , p ⟩
    deferᵏ : ∀ {Γ A} {c : Ctx R Γ A} {l p} → Skipped ⟨ c , pend (defer l) , subscribing , p ⟩
    stallᵏ : ∀ {Γ A Γ′ A′} {c : Ctx R Γ A} {s : St Γ A} {c′ : Ctx R Γ′ A′} {τ u i t k key p}
           → search top (plug c s) ≡ just (found (Γ′ , A′ , c′ , coldS true (play τ u i t (stall k))) leafM key)
           → closed c′ ≡ false → Skipped ⟨ c , s , absorbed , p ⟩
    closeᵏ : ∀ {Γ A Γ′ A′} {c : Ctx R Γ A} {s : St Γ A} {c′ : Ctx R Γ′ A′} {τ u i t k key p}
           → search top (plug c s) ≡ just (found (Γ′ , A′ , c′ , coldS true (play τ u i t (close k))) leafM key)
           → closed c′ ≡ false → Skipped ⟨ c , s , absorbed , p ⟩

  -- What a step spends, if it is silent: work, or a skip.
  record Spends (m : Conf R) (st : Step) : Set₁ where
    constructor spent
    field spend : ∀ {t m′} → st ≡ silent t m′ → work m′ ≺ work m ⊎ Skipped m

  -- `work` held shut, so a bound below unifies the confs it names.
  opaque
    W : Conf R → Measure
    W = work

  private
    opaque
      unfolding W

      lowers : ∀ {m t m′} → W m′ ≺ W m → Spends m (silent t m′)
      lowers lt = spent λ { refl → inj₁ lt }

      skips : ∀ {m st} → Skipped m → Spends m st
      skips sk = spent λ _ → inj₂ sk

      ----------------------------------------------------------------------
      -- The order, count by count

      by-owed : ∀ {a a′ b b′ c c′ d d′ : ℕ} → a′ < a → ((a′ , b′ , c′ , d′ , 0) , 0) ≺ ((a , b , c , d , 0) , 0)
      by-owed lt = inj₁ (inj₁ lt)

      by-calm : ∀ {a a′ b b′ c c′ d d′ : ℕ} → a′ ≡ a → b′ < b → ((a′ , b′ , c′ , d′ , 0) , 0) ≺ ((a , b , c , d , 0) , 0)
      by-calm e lt = inj₁ (inj₂ (e , inj₁ lt))

      by-flight : ∀ {a a′ b b′ c c′ d d′ : ℕ} → a′ ≡ a → b′ ≡ b → c′ < c → ((a′ , b′ , c′ , d′ , 0) , 0) ≺ ((a , b , c , d , 0) , 0)
      by-flight e f lt = inj₁ (inj₂ (e , inj₂ (f , inj₁ lt)))

      by-torn : ∀ {a a′ b b′ c c′ d d′ : ℕ} → a′ ≡ a → b′ ≡ b → c′ ≡ c → d′ < d
              → ((a′ , b′ , c′ , d′ , 0) , 0) ≺ ((a , b , c , d , 0) , 0)
      by-torn e f g lt = inj₁ (inj₂ (e , inj₂ (f , inj₂ (g , inj₁ lt))))

      ----------------------------------------------------------------------
      -- A rise, one frame up: the parent's node `s₀`, left as `s′`

      up-rise : ∀ {Γ A Γ₁ A₁} (c : Ctx R Γ A) (s₀ s′ : St Γ A) (c₁ : Ctx R Γ₁ A₁) (s : St Γ₁ A₁) {e e′ p p′}
              → plug c₁ s ≡ plug c s₀ → height c₁ ≡ suc (height c) → owed s′ ≤ owed s₀
              → W ⟨ c , s′ , rising e′ , p′ ⟩ ≺ W ⟨ c₁ , s , rising e , p ⟩
      up-rise c s₀ s′ c₁ s pl h le with m≤n⇒m<n∨m≡n (subst (λ t → owed (plug c s′) ≤ owed t) (sym pl) (plug-≤ c s₀ s′ le))
      ... | inj₁ lt = by-owed (s≤s lt)
      ... | inj₂ eq = by-flight (cong suc eq) refl (subst (height c <_) (sym h) (n<1+n _))

      up-abs : ∀ {Γ A Γ₁ A₁} (c : Ctx R Γ A) (s₀ s′ : St Γ A) (c₁ : Ctx R Γ₁ A₁) (s : St Γ₁ A₁) {e p p′}
             → plug c₁ s ≡ plug c s₀ → owed s′ ≤ owed s₀
             → W ⟨ c , s′ , absorbed , p′ ⟩ ≺ W ⟨ c₁ , s , rising e , p ⟩
      up-abs c s₀ s′ c₁ s pl le = by-owed (s≤s (subst (λ t → owed (plug c s′) ≤ owed t) (sym pl) (plug-≤ c s₀ s′ le)))

      up-if : ∀ {Γ A Γ₁ A₁} (c : Ctx R Γ A) (s₀ s′ : St Γ A) (c₁ : Ctx R Γ₁ A₁) (s : St Γ₁ A₁) b {e e′ p p′}
            → plug c₁ s ≡ plug c s₀ → height c₁ ≡ suc (height c) → owed s′ ≤ owed s₀
            → W ⟨ c , s′ , (if b then rising e′ else absorbed) , p′ ⟩ ≺ W ⟨ c₁ , s , rising e , p ⟩
      up-if c s₀ s′ c₁ s true  {e} {e′} {p} {p′} pl h le = up-rise c s₀ s′ c₁ s {e} {e′} {p} {p′} pl h le
      up-if c s₀ s′ c₁ s false {e} {e′} {p} {p′} pl h le = up-abs c s₀ s′ c₁ s {e} {p} {p′} pl le

      ----------------------------------------------------------------------
      -- A subscription begun: the node `s″` in place of `s`

      sub-sub : ∀ {Γ A Γ₁ A₁} (c : Ctx R Γ A) (s s″ : St Γ A) (c₁ : Ctx R Γ₁ A₁) (s₁ : St Γ₁ A₁) {p p′}
              → plug c₁ s₁ ≡ plug c s″ → suc (owed s″) ≤ owed s
              → W ⟨ c₁ , s₁ , subscribing , p′ ⟩ ≺ W ⟨ c , s , subscribing , p ⟩
      sub-sub c s s″ c₁ s₁ pl lt = by-owed (subst (λ t → suc (owed t) ≤ owed (plug c s)) (sym pl) (plug-< c s s″ lt))

      sub-abs : ∀ {Γ A} (c : Ctx R Γ A) (s s″ : St Γ A) {p p′} → suc (owed s″) ≤ owed s
              → W ⟨ c , s″ , absorbed , p′ ⟩ ≺ W ⟨ c , s , subscribing , p ⟩
      sub-abs c s s″ lt = by-owed (plug-< c s s″ lt)

      ----------------------------------------------------------------------
      -- A mark run at the node `s′` the search found, left as `s″`

      at-abs : ∀ {Γ A Γ′ A′} (c : Ctx R Γ A) (s : St Γ A) (c′ : Ctx R Γ′ A′) (s′ s″ : St Γ′ A′) {p p′}
             → plug c′ s′ ≡ plug c s → suc (owed s″) ≤ owed s′
             → W ⟨ c′ , s″ , absorbed , p′ ⟩ ≺ W ⟨ c , s , absorbed , p ⟩
      at-abs c s c′ s′ s″ pl lt = by-owed (subst (λ t → suc (owed (plug c′ s″)) ≤ owed t) pl (plug-< c′ s′ s″ lt))

      at-rise : ∀ {Γ A Γ′ A′} (c : Ctx R Γ A) (s : St Γ A) (c′ : Ctx R Γ′ A′) (s′ s″ : St Γ′ A′) {e p p′}
              → plug c′ s′ ≡ plug c s → suc (owed s″) ≤ owed s′
              → W ⟨ c′ , s″ , rising e , p′ ⟩ ≺ W ⟨ c , s , absorbed , p ⟩
      at-rise c s c′ s′ s″ pl lt with m≤n⇒m<n∨m≡n (subst (λ t → suc (owed (plug c′ s″)) ≤ owed t) pl (plug-< c′ s′ s″ lt))
      ... | inj₁ l  = by-owed l
      ... | inj₂ eq = by-calm eq (s≤s z≤n)

      at-if : ∀ {Γ A Γ′ A′} (c : Ctx R Γ A) (s : St Γ A) (c′ : Ctx R Γ′ A′) (s′ s″ : St Γ′ A′) b {e p p′}
            → plug c′ s′ ≡ plug c s → suc (owed s″) ≤ owed s′
            → W ⟨ c′ , s″ , (if b then rising e else absorbed) , p′ ⟩ ≺ W ⟨ c , s , absorbed , p ⟩
      at-if c s c′ s′ s″ true  {e} {p} {p′} pl lt = at-rise c s c′ s′ s″ {e} {p} {p′} pl lt
      at-if c s c′ s′ s″ false {e} {p} {p′} pl lt = at-abs c s c′ s′ s″ {p} {p′} pl lt

      at-sub : ∀ {Γ A Γ′ A′ Γ₁ A₁} (c : Ctx R Γ A) (s : St Γ A) (c′ : Ctx R Γ′ A′) (s′ s″ : St Γ′ A′)
               (c₁ : Ctx R Γ₁ A₁) (s₁ : St Γ₁ A₁) {p p′}
             → plug c′ s′ ≡ plug c s → plug c₁ s₁ ≡ plug c′ s″ → suc (owed s″) ≤ owed s′
             → W ⟨ c₁ , s₁ , subscribing , p′ ⟩ ≺ W ⟨ c , s , absorbed , p ⟩
      at-sub c s c′ s′ s″ c₁ s₁ pl pl₁ lt =
        by-owed (subst₂ (λ x t → suc (owed x) ≤ owed t) (sym pl₁) pl (plug-< c′ s′ s″ lt))

      -- A teardown run: no more owed, one teardown fewer.
      at-torn : ∀ {Γ A Γ′ A′} (c : Ctx R Γ A) (s : St Γ A) (c′ : Ctx R Γ′ A′) (s′ s″ : St Γ′ A′) {p p′}
              → plug c′ s′ ≡ plug c s → owed s″ ≤ owed s′ → torn s″ < torn s′
              → W ⟨ c′ , s″ , absorbed , p′ ⟩ ≺ W ⟨ c , s , absorbed , p ⟩
      at-torn c s c′ s′ s″ pl le tl with m≤n⇒m<n∨m≡n (subst (λ t → owed (plug c′ s″) ≤ owed t) pl (plug-≤ c′ s′ s″ le))
      ... | inj₁ l  = by-owed l
      ... | inj₂ eq = by-torn eq refl refl (subst (λ t → torn (plug c′ s″) < torn t) pl (plug-torn c′ s′ s″ tl))

      att-≤ : ∀ x y a a′ b → a′ ≤ a → suc ((((x + 0) + y) + a′) + b) ≤ (((x + 1) + y) + a) + b
      att-≤ x y a a′ b le = subst (_≤ (((x + 1) + y) + a) + b) (att-split x y a′ b) (+-monoˡ-≤ b (+-monoʳ-≤ ((x + 1) + y) le))

  ----------------------------------------------------------------------
  -- The mark the search found, run

  ran : ∀ {Γ A Γ′ A′} (c : Ctx R Γ A) (s : St Γ A) (c′ : Ctx R Γ′ A′) (s′ : St Γ′ A′) (m : Mark) key p
      → search top (plug c s) ≡ just (found (Γ′ , A′ , c′ , s′) m key) → plug c′ s′ ≡ plug c s → Owns s′ m
      → Spends ⟨ c , s , absorbed , p ⟩ (took (runᴹ c′ s′ m p))
  ran c s c′ (ofS i p₀ []) _ key p eq pl ofO with closed c′
  ... | true  = lowers (at-abs c s c′ (ofS i p₀ []) doneS pl ≤-refl)
  ... | false = lowers (at-rise c s c′ (ofS i p₀ []) doneS pl ≤-refl)
  ran c s c′ (ofS i p₀ (x ∷ xs)) _ key p eq pl ofO with closed c′
  ... | true  = lowers (at-abs c s c′ (ofS i p₀ (x ∷ xs)) doneS pl (s≤s z≤n))
  ... | false = lowers (at-rise c s c′ (ofS i p₀ (x ∷ xs)) (ofS (suc i) p₀ xs) pl ≤-refl)
  ran c s c′ (cutS l (attAt p₀) s₁) _ key p eq pl attO with unsubIf (not l) s₁ | unsubIf-≤ (not l) s₁
  ... | s₂ , t | le = lowers (at-abs c s c′ (cutS l (attAt p₀) s₁) (cutS l attached s₂) pl (s≤s le))
  ran c s c′ (takeS i q (cpAt p₀) s₁) _ key p eq pl cpO =
    lowers (at-rise c s c′ (takeS i q (cpAt p₀) s₁) (takeS i q (cutAt p₀) s₁) pl ≤-refl)
  ran c s c′ (takeS i q (cutAt p₀) s₁) _ key p eq pl cutO with cutᴹ s₁ | cut-≤ s₁
  ... | s₂ , t | le = lowers (at-abs c s c′ (takeS i q (cutAt p₀) s₁) (takeS i q (overAt p₀) s₂) pl (s≤s le))
  ran c s c′ (connS (cs cl sl sa (just q) nothing ow r e) o b) _ key p eq pl (bodyO _) =
    lowers (at-sub c s c′ (connS (cs cl sl sa (just q) nothing ow r e) o b) (connS (cs cl sl sa nothing (just (q ⊕ [ ix 1 ])) ow r e) o b)
              (inSrc (cs cl sl sa nothing (just (q ⊕ [ ix 1 ])) ow r e) b c′) o pl refl ≤-refl)
  ran c s c′ (connS (cs cl sl sa (just q) (just a) ow r e) o b) _ key p eq pl (bodyO _) =
    lowers (at-sub c s c′ (connS (cs cl sl sa (just q) (just a) ow r e) o b) (connS (cs cl sl sa nothing (just (q ⊕ [ ix 1 ])) ow r e) o b)
              (inSrc (cs cl sl sa nothing (just (q ⊕ [ ix 1 ])) ow r e) b c′) o pl refl (n≤1+n _))
  ran c s c′ (connS (cs cl sl sa nothing as ow r e) o b) _ key p eq pl (bodyO ())
  ran c s c′ (connS (cs cl sl sa ba (just q) ow r e) o b) _ key p eq pl (srcAttO _) with unsubIf (not sl) o | unsubIf-≤ (not sl) o
  ... | o′ , t | le = lowers (at-abs c s c′ (connS (cs cl sl sa ba (just q) ow r e) o b) (connS (cs cl sl true ba nothing ow r e) o′ b) pl
                        (att-≤ (just? 2 ba) (one sl) (owed o) (owed o′) (owed b) le))
  ran c s c′ (connS (cs cl sl sa ba nothing ow r e) o b) _ key p eq pl (srcAttO ())
  ran c s c′ (connS (cs cl sl sa ba as (just q) r e) o b) _ key p eq pl (owedO _)
    with unsubIf sa o | unsubIf-≤ sa o | unsubIf-torn sa o
  ... | o′ , t | le | tl = lowers (at-torn c s c′ (connS (cs cl sl sa ba as (just q) r e) o b) (connS (cs cl false sa ba as nothing r e) o′ b) pl
                             (+-mono-≤ (+-mono-≤ (+-monoʳ-≤ (just? 2 ba + just? 1 as) z≤n) le) (≤-refl {owed b}))
                             (s≤s (+-monoˡ-≤ (torn b) tl)))
  ran c s c′ (connS (cs cl sl sa ba as nothing r e) o b) _ key p eq pl (owedO ())
  ran c s c′ (joinS j g x ((q , nx a) ∷ ib)) _ key p eq pl joinO =
    lowers (at-if c s c′ (joinS j g x ((q , nx a) ∷ ib)) (joinS j g x ib) (g ∧ not (closed c′)) pl ≤-refl)
  ran c s c′ (joinS j g x ((q , cp) ∷ ib)) _ key p eq pl joinO =
    lowers (at-if c s c′ (joinS j g x ((q , cp) ∷ ib)) (joinS j false x ib) (g ∧ not (closed c′)) pl ≤-refl)
  ran c s c′ (coldS b (ending e₀)) _ key p eq pl (leafO _) = lowers (at-rise c s c′ (coldS b (ending e₀)) (coldS false over) pl ≤-refl)
  ran c s c′ (coldS b over) _ key p eq pl (leafO ())
  ran c s c′ (coldS false (play τ u i t fr)) _ key p eq pl (leafO _) =
    lowers (at-abs c s c′ (coldS false (play τ u i t fr)) (coldS false over) pl (s≤s z≤n))
  ran c s c′ (coldS true (play τ u i t fr)) _ key p eq pl (leafO _) with closed c′ in ce
  ... | true = lowers (at-abs c s c′ (coldS true (play τ u i t fr)) (coldS true over) pl (s≤s z≤n))
  ran c s c′ (coldS true (play τ u i t (emit a k))) _ key p eq pl (leafO _) | false =
    lowers (at-rise c s c′ (coldS true (play τ u i t (emit a k))) (coldS true (play τ u (suc i) t k)) pl ≤-refl)
  ran c s c′ (coldS true (play τ u i t (stall k))) _ key p eq pl (leafO _) | false = skips (stallᵏ eq ce)
  ran c s c′ (coldS true (play τ u i t (close k))) _ key p eq pl (leafO _) | false = skips (closeᵏ eq ce)

  ----------------------------------------------------------------------
  -- Every step, by its mode

  spends : ∀ m → Inv m → Spends m (step m)
  spends ⟨ top , s , rising (nx a) , p ⟩ iv = spent λ ()
  spends ⟨ top , s , rising cp , p ⟩ iv = spent λ ()
  spends ⟨ inMap f c , s , rising e , p ⟩ iv = lowers (up-rise c (mapS f s) (mapS f s) (inMap f c) s refl refl ≤-refl)
  spends ⟨ inScan f z c , s , rising (nx a) , p ⟩ iv =
    lowers (up-rise c (scanS f z s) (scanS f (f z a) s) (inScan f z c) s refl refl ≤-refl)
  spends ⟨ inScan f z c , s , rising cp , p ⟩ iv = lowers (up-rise c (scanS f z s) (scanS f z s) (inScan f z c) s refl refl ≤-refl)
  spends ⟨ inCut l a c , s , rising e , p ⟩ iv = lowers (up-if c (cutS l a s) (cutS l a s) (inCut l a c) s l refl refl ≤-refl)
  spends ⟨ inLn b c , s , rising e , p ⟩ iv = lowers (up-rise c (lnS b s) (lnS b s) (inLn b c) s refl refl ≤-refl)
  spends ⟨ inTake true q free c , s , rising (nx a) , p ⟩ iv with q a
  ... | true  = lowers (up-rise c (takeS true q free s) (takeS true q free s) (inTake true q free c) s refl refl ≤-refl)
  ... | false = lowers (up-rise c (takeS true q free s) (takeS true q (cpAt p) s) (inTake true q free c) s refl refl (n≤1+n _))
  spends ⟨ inTake false q free c , s , rising (nx a) , p ⟩ iv with q a
  ... | true  = lowers (up-rise c (takeS false q free s) (takeS false q free s) (inTake false q free c) s refl refl ≤-refl)
  ... | false = lowers (up-abs c (takeS false q free s) (takeS false q (cpAt p) s) (inTake false q free c) s refl (n≤1+n _))
  spends ⟨ inTake i q free c , s , rising cp , p ⟩ iv =
    lowers (up-rise c (takeS i q free s) (takeS i q free s) (inTake i q free c) s refl refl ≤-refl)
  spends ⟨ inTake i q (cpAt r) c , s , rising e , p ⟩ iv =
    lowers (up-abs c (takeS i q (cpAt r) s) (takeS i q (cpAt r) s) (inTake i q (cpAt r) c) s refl ≤-refl)
  spends ⟨ inTake i q (cutAt r) c , s , rising e , p ⟩ iv =
    lowers (up-abs c (takeS i q (cutAt r) s) (takeS i q (cutAt r) s) (inTake i q (cutAt r) c) s refl ≤-refl)
  spends ⟨ inTake i q (overAt r) c , s , rising e , p ⟩ iv =
    lowers (up-abs c (takeS i q (overAt r) s) (takeS i q (overAt r) s) (inTake i q (overAt r) c) s refl ≤-refl)
  spends ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩ iv = skips outerᵏ
  spends ⟨ inOuter op f true n q ls c , o , rising cp , p ⟩ iv =
    lowers (up-if c (flatS op f true n q o ls) (flatS op f true n q o ls) (inOuter op f true n q ls c) o
              ((n ≡ᵇ 0) ∧ null q) refl refl ≤-refl)
  spends ⟨ inOuter op f false n q ls c , o , rising cp , p ⟩ iv =
    lowers (up-if c (flatS op f false n q o ls) (flatS op f true n q o ls) (inOuter op f false n q ls c) o
              ((n ≡ᵇ 0) ∧ null q) refl refl (n≤1+n _))
  spends ⟨ inLanes op f d n q o pre post c , s , rising (nx b) , p ⟩ iv with alive s
  ... | true  = lowers (up-rise c (flatS op f d n q o (pre ʳ++ s ∷ post)) (flatS op f d n q o (pre ʳ++ s ∷ post))
                          (inLanes op f d n q o pre post c) s refl refl ≤-refl)
  ... | false = lowers (up-abs c (flatS op f d n q o (pre ʳ++ s ∷ post)) (flatS op f d n q o (pre ʳ++ s ∷ post))
                          (inLanes op f d n q o pre post c) s refl ≤-refl)
  spends ⟨ inLanes op f d n [] o pre post c , s , rising cp , p ⟩ iv with alive s
  ... | true  = lowers (up-if c (flatS op f d n [] o (pre ʳ++ s ∷ post)) (flatS op f d (pred n) [] o (pre ʳ++ ended s ∷ post))
                          (inLanes op f d n [] o pre post c) s (d ∧ ((pred n ≡ᵇ 0) ∧ true)) refl refl
                          (lanes-≤ op f d n (pred n) [] o pre post s (ended s) (ended-≤ s)))
  ... | false = lowers (up-abs c (flatS op f d n [] o (pre ʳ++ s ∷ post)) (flatS op f d n [] o (pre ʳ++ s ∷ post))
                          (inLanes op f d n [] o pre post c) s refl ≤-refl)
  spends ⟨ inLanes op f d n (a ∷ q) o pre post c , s , rising cp , p ⟩ iv with alive s in al
  ... | true  = skips (laneᵏ al)
  ... | false = lowers (up-abs c (flatS op f d n (a ∷ q) o (pre ʳ++ s ∷ post)) (flatS op f d n (a ∷ q) o (pre ʳ++ s ∷ post))
                          (inLanes op f d n (a ∷ q) o pre post c) s refl ≤-refl)
  spends ⟨ inSrc k b c , s , rising e , p ⟩ iv = skips srcᵏ
  spends ⟨ inBody k o c , s , rising (nx b) , p ⟩ iv =
    lowers (up-rise c (connS k o s) (connS k o s) (inBody k o c) s refl refl ≤-refl)
  spends ⟨ inBody k o c , s , rising cp , p ⟩ iv =
    lowers (up-rise c (connS k o s) (connS (record k { owedAt = just p }) o s) (inBody k o c) s refl refl ≤-refl)
  spends ⟨ c , pend (cold x) , subscribing , p ⟩ iv =
    lowers (sub-abs c (pend (cold x)) (coldS true (opening p (timelineAt x p))) (opening-< x p))
  spends ⟨ c , pend empty , subscribing , p ⟩ iv = lowers (sub-abs c (pend empty) (ofS 0 p []) ≤-refl)
  spends ⟨ c , pend (of xs) , subscribing , p ⟩ iv = lowers (sub-abs c (pend (of xs)) (ofS 0 p xs) ≤-refl)
  spends ⟨ c , pend (map f s) , subscribing , p ⟩ iv = lowers (sub-sub c (pend (map f s)) (mapS f (pend s)) (inMap f c) (pend s) refl ≤-refl)
  spends ⟨ c , pend (scan f z s) , subscribing , p ⟩ iv =
    lowers (sub-sub c (pend (scan f z s)) (scanS f z (pend s)) (inScan f z c) (pend s) refl ≤-refl)
  spends ⟨ c , pend (takeWhile i q s) , subscribing , p ⟩ iv =
    lowers (sub-sub c (pend (takeWhile i q s)) (takeS i q free (cutS true (attAt p) (pend s)))
              (inCut true (attAt p) (inTake i q free c)) (pend s) refl ≤-refl)
  spends ⟨ c , pend (flatMap op f s) , subscribing , p ⟩ iv =
    lowers (sub-sub c (pend (flatMap op f s)) (flatS op f false 0 [] (cutS true (attAt p) (pend s)) [])
              (inCut true (attAt p) (inOuter op f false 0 [] [] c)) (pend s) refl ≤-refl)
  spends ⟨ c , pend (connect s b) , subscribing , p ⟩ iv =
    lowers (sub-sub c (pend (connect s b)) (connS k (pend s) (pend b)) (inBody k (pend s) c) (pend b) refl ≤-refl)
    where
    k = cs false true false (just p) nothing nothing (p ⊕ [ ix 1 ]) root
  spends ⟨ c , pend (connected x) , subscribing , p ⟩ iv with closedUp c x
  ... | true  = lowers (sub-abs c (pend (connected x)) (ofS 0 p []) ≤-refl)
  ... | false = lowers (sub-abs c (pend (connected x)) (joinS p true x []) (s≤s z≤n))
  spends ⟨ c , pend (defer l) , subscribing , p ⟩ iv = skips deferᵏ
  spends ⟨ c , coldS b l , subscribing , p ⟩ iv             = ⊥-elim (Base.settled (Inv.base iv))
  spends ⟨ c , ofS i q xs , subscribing , p ⟩ iv            = ⊥-elim (Base.settled (Inv.base iv))
  spends ⟨ c , doneS , subscribing , p ⟩ iv                 = ⊥-elim (Base.settled (Inv.base iv))
  spends ⟨ c , mapS f s , subscribing , p ⟩ iv              = ⊥-elim (Base.settled (Inv.base iv))
  spends ⟨ c , scanS f z s , subscribing , p ⟩ iv           = ⊥-elim (Base.settled (Inv.base iv))
  spends ⟨ c , cutS l a s , subscribing , p ⟩ iv            = ⊥-elim (Base.settled (Inv.base iv))
  spends ⟨ c , lnS b s , subscribing , p ⟩ iv               = ⊥-elim (Base.settled (Inv.base iv))
  spends ⟨ c , takeS i q w s , subscribing , p ⟩ iv         = ⊥-elim (Base.settled (Inv.base iv))
  spends ⟨ c , flatS op f d n q o ls , subscribing , p ⟩ iv = ⊥-elim (Base.settled (Inv.base iv))
  spends ⟨ c , connS k o b , subscribing , p ⟩ iv           = ⊥-elim (Base.settled (Inv.base iv))
  spends ⟨ c , joinS j g x ib , subscribing , p ⟩ iv        = ⊥-elim (Base.settled (Inv.base iv))
  spends ⟨ c , s , absorbed , p ⟩ iv with search top (plug c s) in eq
  ... | nothing = spent λ ()
  ... | just (found (Γ′ , A′ , c′ , s′) m key) with search-hit (plug c s) eq
  ...   | pl , own = ran c s c′ s′ m key p eq pl own

  -- A silent step spends work, or drops a skip.
  silent-spent : ∀ {m t m′} → Inv m → step m ≡ silent t m′ → work m′ ≺ work m ⊎ Skipped m
  silent-spent {m} iv e = Spends.spend (spends m iv) e
