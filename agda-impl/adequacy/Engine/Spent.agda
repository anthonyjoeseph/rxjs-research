{-# OPTIONS --guardedness #-}

-- WHAT A SILENT STEP SPENDS.  Every silent step lowers the work its
-- configuration has left (`adequacy.Ghost`'s `work`), or is one of the
-- steps whose work may grow (`Skipped`): an outer's value absorbed, a
-- lane's end starting a waiting value's lane, a defer begun, a cold's
-- stall or close.  Each of those drops a leading skip of
-- what the configuration means (`adequacy.Content`).
--
-- No bound holds on a step keeping its meaning alone: a cold whose frames
-- are all empty, one per tick forever, means skips only, so each close
-- keeps its meaning at every depth and leaves what it owes one stop.
module adequacy.Engine.Spent where

open import Data.Bool using (true; false; not; _∧_; if_then_else_)
open import Data.List using (List; []; _∷_; _ʳ++_; [_]; length; null)
open import Data.List.Properties using (length-++)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _<_; _≤_; z≤n; s≤s; pred; _≡ᵇ_)
open import Data.Nat.Properties using (≤-refl; n≤1+n; n<1+n; m≤n⇒m<n∨m≡n; +-assoc; +-monoʳ-<; +-monoˡ-<; +-monoʳ-≤; +-monoˡ-≤;
  +-mono-≤; *-monoʳ-≤; *-monoˡ-≤; *-mono-≤; +-cancelʳ-≤; ≤-trans; ≤-reflexive; m≤m+n; m≤n+m;
  +-identityʳ; +-comm)
open import Data.Nat.Tactic.RingSolver using (solve-∀)
open import Data.Product using (_,_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import Tree using (Obs; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.Unfold using (same?)
open import denotation.MonotonicList.Events using (Timeline; fixed; fresh; timelineAt; done; quiet; at; emit; stall; close; ix; root; _<ᵖ_)
open import operation.PureObservable using (play; ending; over; opening; module Machine; module Driver)
open import adequacy.Engine.Work using (run; tapeW; coldW; size; one; attW; oweW; just?; csW; fedO; fed; fedL; fan; wt; owed; owedL; tornC; torn; tornL; height)
open import adequacy.Engine.Inv using (Inv; module Inv; module Base; Owns; ofO; attO; cpO; cutO; bodyO; srcAttO; owedO; joinO;
  leafO; search-hit)
open import adequacy.Ghost using (module Ghosting)
open Machine using (St; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
  Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody; plug; closed; closedUp;
  cs; attached; attAt; free; cpAt; cutAt; overAt; nx; cp; _⊕_;
  Conf; ⟨_,_,_,_⟩; subscribing; absorbed; rising; Mark; ofM; attM; bodyM; srcAttM; owedM; cpM; cutM; joinM; leafM;
  search; found; ended; alive; unsub; killAll; unsubIf; feed; feedL; queued; Ev)
  renaming (cut to cutᴹ; run to runᴹ)

------------------------------------------------------------------------
-- What a tree owes, moved at a hole

private
  rev-split : ∀ p x y → p + (x + y) ≡ (x + p) + y
  rev-split = solve-∀

  att-split : ∀ x y a b → ((x + 1) + y) + a + b ≡ 1 + (((x + 0) + y) + a + b)
  att-split = solve-∀

  fr : ∀ P w a K y → P + w * y + (w * a + w * K) ≡ P + w * (a + K + y)
  fr = solve-∀

  lanes-eq : ∀ p s q r → (p + (s + q)) + r ≡ 0 + ((p + q) + r) + s
  lanes-eq = solve-∀

  src-eq : ∀ C f X B → C + f * X + B ≡ 0 + (C + B) + f * X
  src-eq = solve-∀

  body-eq : ∀ C a X → C + a + X ≡ a + C + X
  body-eq = solve-∀

  mul-eq : ∀ w f y → w * (f * y) ≡ (f * w) * y
  mul-eq = solve-∀

  top-eq : ∀ a b → a + 1 * b ≡ b + 1 * a
  top-eq = solve-∀

  lt-eq : ∀ w P X → (w + P) + w * X ≡ P + w * (1 + X)
  lt-eq = solve-∀

  grow-eq : ∀ Q w Y d → Q + w * (Y + d) ≡ (Q + w * d) + w * Y
  grow-eq = solve-∀

  low-eq : ∀ Q w f → w + (Q + w * f) ≡ (1 + f) * w + Q
  low-eq = solve-∀

  shift-eq : ∀ k f o → k + (f + o) ≡ f + (k + o)
  shift-eq = solve-∀

  four : ∀ a b c d → (a + c) + (b + d) ≡ (a + b) + (c + d)
  four = solve-∀

  flat-eq : ∀ fo fl L q O → (fl + L) + (q + (fo + O)) ≡ (fo + fl) + (L + (q + O))
  flat-eq = solve-∀

  flat-eq₁ : ∀ fo fl L q O → 1 + ((fl + L) + (q + (fo + O))) ≡ (fo + fl) + (1 + (L + (q + O)))
  flat-eq₁ = solve-∀

  conn-eq : ∀ C F fo O fb B → C + F * (fo + O) + (fb + B) ≡ (F * fo + fb) + (C + F * O + B)
  conn-eq = solve-∀

  feed-eq : ∀ C F O → C + (F + O) ≡ (C + O) + F
  feed-eq = solve-∀

  shift : ∀ k f o {o′} → o′ ≤ f + o → k + o′ ≤ f + (k + o)
  shift k f o h = ≤-trans (+-monoʳ-≤ k h) (≤-reflexive (shift-eq k f o))

-- A lane list read back to front, as a lane's context keeps it.
owedL-ʳ++ : ∀ {Γ A} (pre ys : List (St Γ A)) → owedL (pre ʳ++ ys) ≡ owedL pre + owedL ys
owedL-ʳ++ []        ys = refl
owedL-ʳ++ (x ∷ pre) ys = trans (owedL-ʳ++ pre (x ∷ ys)) (rev-split (owedL pre) (owed x) (owedL ys))

fedL-ʳ++ : ∀ {Γ X A} (i : X ∈ Γ) (pre ys : List (St Γ A)) → fedL i (pre ʳ++ ys) ≡ fedL i pre + fedL i ys
fedL-ʳ++ i []        ys = refl
fedL-ʳ++ i (x ∷ pre) ys = trans (fedL-ʳ++ i pre (x ∷ ys)) (rev-split (fedL i pre) (fed i x) (fedL i ys))

-- A node feeding no joiner more than another.
Fed≤ : ∀ {Γ A} → St Γ A → St Γ A → Set₁
Fed≤ {Γ} x y = ∀ {X} (i : X ∈ Γ) → fed i x ≤ fed i y

wt-pos : ∀ {R Γ A} (c : Ctx R Γ A) → 1 ≤ wt c
wt-pos top                               = s≤s z≤n
wt-pos (inMap f c)                       = wt-pos c
wt-pos (inScan f z c)                    = wt-pos c
wt-pos (inCut l a c)                     = wt-pos c
wt-pos (inLn b c)                        = wt-pos c
wt-pos (inTake i q w c)                  = wt-pos c
wt-pos (inOuter op f d n q ls c)         = wt-pos c
wt-pos (inLanes op f d n q o pre post c) = wt-pos c
wt-pos (inSrc k b c)                     = ≤-trans (wt-pos c) (m≤m+n (wt c) _)
wt-pos (inBody k o c)                    = wt-pos c

-- A lane, in place, feeding no more.
lanes-F : ∀ {Γ A B} (o : St Γ A) pre post (s s′ : St Γ B) → Fed≤ s s′
        → ∀ {X} (i : X ∈ Γ) → fed i o + fedL i (pre ʳ++ s ∷ post) ≤ fed i o + fedL i (pre ʳ++ s′ ∷ post)
lanes-F o pre post s s′ F i =
  +-monoʳ-≤ (fed i o) (subst₂ _≤_ (sym (fedL-ʳ++ i pre (s ∷ post))) (sym (fedL-ʳ++ i pre (s′ ∷ post)))
    (+-monoʳ-≤ (fedL i pre) (+-monoˡ-≤ (fedL i post) (F i))))

-- One frame: what it owes beside its hole cancels.
frame : ∀ P Q w K a a′ x y {ox oy} → ox ≡ a + K + x → oy ≡ a′ + K + y → a ≤ a′
      → P + w * oy ≤ Q + w * ox → P + w * y ≤ Q + w * x
frame P Q w K a a′ x y refl refl le h =
  +-cancelʳ-≤ (w * a + w * K) (P + w * y) (Q + w * x)
    (≤-trans (+-monoʳ-≤ (P + w * y) (+-monoˡ-≤ (w * K) (*-monoʳ-≤ w le)))
      (≤-trans (≤-reflexive (fr P w a′ K y)) (≤-trans h (≤-reflexive (sym (fr Q w a K x))))))

-- What a tree owes moves with what its hole owes, at the hole's weight,
-- so long as the hole feeds no joiner more.
plug-lin : ∀ {R Γ A} (c : Ctx R Γ A) (x y : St Γ A) → Fed≤ x y
         → owed (plug c x) + wt c * owed y ≤ owed (plug c y) + wt c * owed x
plug-lin top x y F = ≤-reflexive (top-eq (owed x) (owed y))
plug-lin (inMap f c) x y F =
  frame _ _ (wt c) 0 0 0 (owed x) (owed y) refl refl ≤-refl (plug-lin c (mapS f x) (mapS f y) F)
plug-lin (inScan f z c) x y F =
  frame _ _ (wt c) 0 0 0 (owed x) (owed y) refl refl ≤-refl (plug-lin c (scanS f z x) (scanS f z y) F)
plug-lin (inCut l a c) x y F =
  frame _ _ (wt c) (attW a) 0 0 (owed x) (owed y) refl refl ≤-refl (plug-lin c (cutS l a x) (cutS l a y) F)
plug-lin (inLn b c) x y F =
  frame _ _ (wt c) (one b) 0 0 (owed x) (owed y) refl refl ≤-refl (plug-lin c (lnS b x) (lnS b y) F)
plug-lin (inTake i q w c) x y F =
  frame _ _ (wt c) (oweW w) 0 0 (owed x) (owed y) refl refl ≤-refl (plug-lin c (takeS i q w x) (takeS i q w y) F)
plug-lin (inOuter op f true n q ls c) x y F =
  frame _ _ (wt c) (owedL ls + length q) 0 0 (owed x) (owed y)
    (sym (+-assoc (owedL ls) (length q) (owed x))) (sym (+-assoc (owedL ls) (length q) (owed y))) ≤-refl
    (plug-lin c (flatS op f true n q x ls) (flatS op f true n q y ls) (λ i → +-monoˡ-≤ (fedL i ls) (F i)))
plug-lin (inOuter op f false n q ls c) x y F =
  frame _ _ (wt c) (suc (owedL ls + length q)) 0 0 (owed x) (owed y)
    (cong suc (sym (+-assoc (owedL ls) (length q) (owed x)))) (cong suc (sym (+-assoc (owedL ls) (length q) (owed y)))) ≤-refl
    (plug-lin c (flatS op f false n q x ls) (flatS op f false n q y ls) (λ i → +-monoˡ-≤ (fedL i ls) (F i)))
plug-lin (inLanes op f true n q o pre post c) x y F =
  frame _ _ (wt c) ((owedL pre + owedL post) + (length q + owed o)) 0 0 (owed x) (owed y)
    (trans (cong (_+ (length q + owed o)) (owedL-ʳ++ pre (x ∷ post))) (lanes-eq (owedL pre) (owed x) (owedL post) (length q + owed o)))
    (trans (cong (_+ (length q + owed o)) (owedL-ʳ++ pre (y ∷ post))) (lanes-eq (owedL pre) (owed y) (owedL post) (length q + owed o)))
    ≤-refl
    (plug-lin c (flatS op f true n q o (pre ʳ++ x ∷ post)) (flatS op f true n q o (pre ʳ++ y ∷ post)) (lanes-F o pre post x y F))
plug-lin (inLanes op f false n q o pre post c) x y F =
  frame _ _ (wt c) (suc ((owedL pre + owedL post) + (length q + owed o))) 0 0 (owed x) (owed y)
    (cong suc (trans (cong (_+ (length q + owed o)) (owedL-ʳ++ pre (x ∷ post)))
                (lanes-eq (owedL pre) (owed x) (owedL post) (length q + owed o))))
    (cong suc (trans (cong (_+ (length q + owed o)) (owedL-ʳ++ pre (y ∷ post)))
                (lanes-eq (owedL pre) (owed y) (owedL post) (length q + owed o))))
    ≤-refl
    (plug-lin c (flatS op f false n q o (pre ʳ++ x ∷ post)) (flatS op f false n q o (pre ʳ++ y ∷ post)) (lanes-F o pre post x y F))
plug-lin (inSrc k b c) x y F =
  subst₂ (λ u v → owed (plug c (connS k x b)) + u ≤ owed (plug c (connS k y b)) + v)
    (mul-eq (wt c) (fan b) (owed y)) (mul-eq (wt c) (fan b) (owed x))
    (frame _ _ (wt c) (csW k + owed b) 0 0 (fan b * owed x) (fan b * owed y)
      (src-eq (csW k) (fan b) (owed x) (owed b)) (src-eq (csW k) (fan b) (owed y) (owed b)) ≤-refl
      (plug-lin c (connS k x b) (connS k y b) (λ i → +-monoˡ-≤ (fed (there i) b) (*-monoʳ-≤ (fan b) (F i)))))
plug-lin (inBody k o c) x y F =
  frame _ _ (wt c) (csW k) (fan x * owed o) (fan y * owed o) (owed x) (owed y)
    (body-eq (csW k) (fan x * owed o) (owed x)) (body-eq (csW k) (fan y * owed o) (owed y))
    (*-monoˡ-≤ (owed o) (s≤s (F (here refl))))
    (plug-lin c (connS k o x) (connS k o y) (λ i → +-mono-≤ (*-monoˡ-≤ (fed i o) (s≤s (F (here refl)))) (F (there i))))

plug-≤ : ∀ {R Γ A} (c : Ctx R Γ A) (x y : St Γ A) → Fed≤ x y → owed x ≤ owed y → owed (plug c x) ≤ owed (plug c y)
plug-≤ c x y F le =
  +-cancelʳ-≤ (wt c * owed y) (owed (plug c x)) (owed (plug c y))
    (≤-trans (plug-lin c x y F) (+-monoʳ-≤ (owed (plug c y)) (*-monoʳ-≤ (wt c) le)))

-- A hole owing less leaves a tree owing less by the hole's weight.
plug-< : ∀ {R Γ A} (c : Ctx R Γ A) (x y : St Γ A) → Fed≤ x y → suc (owed x) ≤ owed y
       → wt c + owed (plug c x) ≤ owed (plug c y)
plug-< c x y F lt =
  +-cancelʳ-≤ (wt c * owed x) (wt c + owed (plug c x)) (owed (plug c y))
    (≤-trans (≤-reflexive (lt-eq (wt c) (owed (plug c x)) (owed x)))
      (≤-trans (+-monoʳ-≤ (owed (plug c x)) (*-monoʳ-≤ (wt c) lt)) (plug-lin c x y F)))

plug-<′ : ∀ {R Γ A} (c : Ctx R Γ A) (x y : St Γ A) → Fed≤ x y → suc (owed x) ≤ owed y → suc (owed (plug c x)) ≤ owed (plug c y)
plug-<′ c x y F lt = ≤-trans (+-monoˡ-≤ (owed (plug c x)) (wt-pos c)) (plug-< c x y F lt)

-- A hole owing `d` more leaves a tree owing at most `d` more at its weight.
plug-grow : ∀ {R Γ A} (c : Ctx R Γ A) (x y : St Γ A) d → Fed≤ x y → owed x ≤ owed y + d
          → owed (plug c x) ≤ owed (plug c y) + wt c * d
plug-grow c x y d F le =
  +-cancelʳ-≤ (wt c * owed y) (owed (plug c x)) (owed (plug c y) + wt c * d)
    (≤-trans (plug-lin c x y F)
      (≤-trans (+-monoʳ-≤ (owed (plug c y)) (*-monoʳ-≤ (wt c) le)) (≤-reflexive (grow-eq (owed (plug c y)) (wt c) (owed y) d))))

src-low : ∀ P Q w f → 1 ≤ w → P ≤ Q + w * f → suc P ≤ suc f * w + Q
src-low P Q w f pos h = ≤-trans (s≤s h) (≤-trans (+-monoˡ-≤ (Q + w * f) pos) (≤-reflexive (low-eq Q w f)))

------------------------------------------------------------------------
-- A feed: each live joiner one entry more, every joiner as before

queued-len : ∀ {A} j p (e : Ev A) ib → length (queued j p e ib) ≤ 1 + length ib
queued-len j p (nx a) ib with j <ᵖ p
... | true  = ≤-reflexive (trans (length-++ ib) (+-comm (length ib) 1))
... | false = n≤1+n _
queued-len j p cp ib = ≤-reflexive (trans (length-++ ib) (+-comm (length ib) 1))

mutual
  feed-fed : ∀ {Γ X Y A} (j : Y ∈ Γ) (i : X ∈ Γ) p e (s : St Γ A) → fed j (feed i p e s) ≡ fed j s
  feed-fed j i p e (joinS j′ true x ib) with same? i x
  ... | just refl = refl
  ... | nothing   = refl
  feed-fed j i p e (joinS j′ false x ib)    = refl
  feed-fed j i p e (pend o)                 = refl
  feed-fed j i p e (coldS b l)              = refl
  feed-fed j i p e (ofS n q xs)             = refl
  feed-fed j i p e doneS                    = refl
  feed-fed j i p e (mapS f s)               = feed-fed j i p e s
  feed-fed j i p e (scanS f z s)            = feed-fed j i p e s
  feed-fed j i p e (cutS l a s)             = feed-fed j i p e s
  feed-fed j i p e (lnS b s)                = feed-fed j i p e s
  feed-fed j i p e (takeS v q w s)          = feed-fed j i p e s
  feed-fed j i p e (flatS op f d n q o ls)  = cong₂ _+_ (feed-fed j i p e o) (feedL-fed j i p e ls)
  feed-fed j i p e (connS k o b) =
    cong₂ _+_ (cong₂ _*_ (cong suc (feed-fed (here refl) (there i) p e b)) (feed-fed j i p e o)) (feed-fed (there j) (there i) p e b)

  feedL-fed : ∀ {Γ X Y A} (j : Y ∈ Γ) (i : X ∈ Γ) p e (ls : List (St Γ A)) → fedL j (feedL i p e ls) ≡ fedL j ls
  feedL-fed j i p e []       = refl
  feedL-fed j i p e (s ∷ ls) = cong₂ _+_ (feed-fed j i p e s) (feedL-fed j i p e ls)

mutual
  feed-owed : ∀ {Γ X A} (i : X ∈ Γ) p e (s : St Γ A) → owed (feed i p e s) ≤ fed i s + owed s
  feed-owed i p e (joinS j true x ib) with same? i x
  ... | just refl = queued-len j p e ib
  ... | nothing   = ≤-refl
  feed-owed i p e (joinS j false x ib)      = ≤-refl
  feed-owed i p e (pend o)                  = m≤n+m (size o) (fedO i o)
  feed-owed i p e (coldS b l)               = ≤-refl
  feed-owed i p e (ofS n q xs)              = ≤-refl
  feed-owed i p e doneS                     = ≤-refl
  feed-owed i p e (mapS f s)                = feed-owed i p e s
  feed-owed i p e (scanS f z s)             = feed-owed i p e s
  feed-owed i p e (cutS l a s)              = shift (attW a) (fed i s) (owed s) (feed-owed i p e s)
  feed-owed i p e (lnS b s)                 = shift (one b) (fed i s) (owed s) (feed-owed i p e s)
  feed-owed i p e (takeS v q w s)           = shift (oweW w) (fed i s) (owed s) (feed-owed i p e s)
  feed-owed i p e (flatS op f true n q o ls) =
    ≤-trans (+-mono-≤ (feedL-owed i p e ls) (+-monoʳ-≤ (length q) (feed-owed i p e o)))
      (≤-reflexive (flat-eq (fed i o) (fedL i ls) (owedL ls) (length q) (owed o)))
  feed-owed i p e (flatS op f false n q o ls) =
    ≤-trans (s≤s (+-mono-≤ (feedL-owed i p e ls) (+-monoʳ-≤ (length q) (feed-owed i p e o))))
      (≤-reflexive (flat-eq₁ (fed i o) (fedL i ls) (owedL ls) (length q) (owed o)))
  feed-owed i p e (connS k o b) =
    subst (λ u → csW k + suc u * owed (feed i p e o) + owed (feed (there i) p e b) ≤ fed i (connS k o b) + owed (connS k o b))
      (sym (feed-fed (here refl) (there i) p e b))
    (≤-trans (+-mono-≤ (+-monoʳ-≤ (csW k) (*-monoʳ-≤ (fan b) (feed-owed i p e o))) (feed-owed (there i) p e b))
      (≤-reflexive (conn-eq (csW k) (fan b) (fed i o) (owed o) (fed (there i) b) (owed b))))

  feedL-owed : ∀ {Γ X A} (i : X ∈ Γ) p e (ls : List (St Γ A)) → owedL (feedL i p e ls) ≤ fedL i ls + owedL ls
  feedL-owed i p e []       = ≤-refl
  feedL-owed i p e (s ∷ ls) =
    ≤-trans (+-mono-≤ (feed-owed i p e s) (feedL-owed i p e ls)) (≤-reflexive (four (fed i s) (fedL i ls) (owed s) (owedL ls)))

-- A source's step fed to its connect's body: no joiner fed more, and
-- what the connect owes grows by one entry per joiner.
src-fed : ∀ {Γ X B} k k′ (s : St Γ X) (b : St (X ∷ Γ) B) p e → Fed≤ (connS k′ s (feed (here refl) p e b)) (connS k s b)
src-fed k k′ s b p e i =
  ≤-reflexive (cong₂ (λ u v → suc u * fed i s + v) (feed-fed (here refl) (here refl) p e b) (feed-fed (there i) (here refl) p e b))

src-owed : ∀ {Γ X B} k k′ (s : St Γ X) (b : St (X ∷ Γ) B) p e → csW k′ ≡ csW k
         → owed (connS k′ s (feed (here refl) p e b)) ≤ owed (connS k s b) + fed (here refl) b
src-owed k k′ s b p e ck =
  subst₂ (λ C u → C + suc u * owed s + owed (feed (here refl) p e b) ≤ owed (connS k s b) + fed (here refl) b)
    (sym ck) (sym (feed-fed (here refl) (here refl) p e b))
    (≤-trans (+-monoʳ-≤ (csW k + fan b * owed s) (feed-owed (here refl) p e b))
      (≤-reflexive (feed-eq (csW k + fan b * owed s) (fed (here refl) b) (owed b))))

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
-- An unsubscribe feeds no joiner more

mutual
  unsub-fed : ∀ {Γ X A} (i : X ∈ Γ) (s : St Γ A) → fed i (proj₁ (unsub s)) ≤ fed i s
  unsub-fed i (pend o)                = ≤-refl
  unsub-fed i (coldS true l)          = ≤-refl
  unsub-fed i (coldS false l)         = ≤-refl
  unsub-fed i (ofS n p xs)            = ≤-refl
  unsub-fed i doneS                   = ≤-refl
  unsub-fed i (mapS f s)              = unsub-fed i s
  unsub-fed i (scanS f z s)           = unsub-fed i s
  unsub-fed i (cutS l a s)            = ≤-refl
  unsub-fed i (lnS b s)               = ≤-refl
  unsub-fed i (takeS v q w s)         = cut-fed i s
  unsub-fed i (flatS op f d n q o ls) = +-mono-≤ (cut-fed i o) (killAll-fed i ls)
  unsub-fed i (connS k o b)           =
    +-mono-≤ (*-mono-≤ (s≤s (unsub-fed (here refl) b)) (unsub-fed i o)) (unsub-fed (there i) b)
  unsub-fed i (joinS j g x ib)        = z≤n

  cut-fed : ∀ {Γ X A} (i : X ∈ Γ) (s : St Γ A) → fed i (proj₁ (cutᴹ s)) ≤ fed i s
  cut-fed i (cutS l attached s)     = unsub-fed i s
  cut-fed i (cutS l (attAt p) s)    = ≤-refl
  cut-fed i (pend o)                = ≤-refl
  cut-fed i (coldS b l)             = ≤-refl
  cut-fed i (ofS n p xs)            = ≤-refl
  cut-fed i doneS                   = ≤-refl
  cut-fed i (mapS f s)              = ≤-refl
  cut-fed i (scanS f z s)           = ≤-refl
  cut-fed i (lnS b s)               = ≤-refl
  cut-fed i (takeS v q w s)         = ≤-refl
  cut-fed i (flatS op f d n q o ls) = ≤-refl
  cut-fed i (connS k o b)           = ≤-refl
  cut-fed i (joinS j g x ib)        = ≤-refl

  killAll-fed : ∀ {Γ X B} (i : X ∈ Γ) (ls : List (St Γ B)) → fedL i (proj₁ (killAll ls)) ≤ fedL i ls
  killAll-fed i []                            = ≤-refl
  killAll-fed i (lnS true s ∷ ls)             = +-mono-≤ (cut-fed i s) (killAll-fed i ls)
  killAll-fed i (lnS false s ∷ ls)            = +-monoʳ-≤ (fed i s) (killAll-fed i ls)
  killAll-fed i (pend o ∷ ls)                 = +-monoʳ-≤ (fedO i o) (killAll-fed i ls)
  killAll-fed i (coldS b l ∷ ls)              = killAll-fed i ls
  killAll-fed i (ofS n p xs ∷ ls)             = killAll-fed i ls
  killAll-fed i (doneS ∷ ls)                  = killAll-fed i ls
  killAll-fed i (mapS f s ∷ ls)               = +-monoʳ-≤ (fed i s) (killAll-fed i ls)
  killAll-fed i (scanS f z s ∷ ls)            = +-monoʳ-≤ (fed i s) (killAll-fed i ls)
  killAll-fed i (cutS l a s ∷ ls)             = +-monoʳ-≤ (fed i s) (killAll-fed i ls)
  killAll-fed i (takeS v q w s ∷ ls)          = +-monoʳ-≤ (fed i s) (killAll-fed i ls)
  killAll-fed i (flatS op f d n q o ls′ ∷ ls) = +-monoʳ-≤ (fed i (flatS op f d n q o ls′)) (killAll-fed i ls)
  killAll-fed i (connS k o b ∷ ls)            = +-monoʳ-≤ (fed i (connS k o b)) (killAll-fed i ls)
  killAll-fed i (joinS j g x ib ∷ ls)         = +-monoʳ-≤ (fed i (joinS j g x ib)) (killAll-fed i ls)

unsubIf-F : ∀ {Γ A} b (s : St Γ A) → Fed≤ (proj₁ (unsubIf b s)) s
unsubIf-F true  s i = unsub-fed i s
unsubIf-F false s i = ≤-refl

cut-F : ∀ {Γ A} (s : St Γ A) → Fed≤ (proj₁ (cutᴹ s)) s
cut-F s i = cut-fed i s

-- A lane's end feeds as it did.
ended-F : ∀ {Γ B} (s : St Γ B) → Fed≤ (ended s) s
ended-F (lnS b (cutS l a s))         i = ≤-refl
ended-F (lnS b (pend o))             i = ≤-refl
ended-F (lnS b (coldS b′ l))         i = ≤-refl
ended-F (lnS b (ofS n p xs))         i = ≤-refl
ended-F (lnS b doneS)                i = ≤-refl
ended-F (lnS b (mapS f s))           i = ≤-refl
ended-F (lnS b (scanS f z s))        i = ≤-refl
ended-F (lnS b (lnS b′ s))           i = ≤-refl
ended-F (lnS b (takeS v q w s))      i = ≤-refl
ended-F (lnS b (flatS op f d n q o ls)) i = ≤-refl
ended-F (lnS b (connS k o b′))       i = ≤-refl
ended-F (lnS b (joinS j g x ib))     i = ≤-refl
ended-F (pend o)                     i = ≤-refl
ended-F (coldS b l)                  i = ≤-refl
ended-F (ofS n p xs)                 i = ≤-refl
ended-F doneS                        i = ≤-refl
ended-F (mapS f s)                   i = ≤-refl
ended-F (scanS f z s)                i = ≤-refl
ended-F (cutS l a s)                 i = ≤-refl
ended-F (takeS v q w s)              i = ≤-refl
ended-F (flatS op f d n q o ls)      i = ≤-refl
ended-F (connS k o b)                i = ≤-refl
ended-F (joinS j g x ib)             i = ≤-refl

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
  unsub-≤ (connS k o b)               =
    +-mono-≤ (+-monoʳ-≤ (csW k) (*-mono-≤ (s≤s (unsub-fed (here refl) b)) (unsub-≤ o))) (unsub-≤ b)
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
              → plug c₁ s ≡ plug c s₀ → height c₁ ≡ suc (height c) → wt c₁ ≡ wt c → owed s′ ≤ owed s₀ → Fed≤ s′ s₀
              → W ⟨ c , s′ , rising e′ , p′ ⟩ ≺ W ⟨ c₁ , s , rising e , p ⟩
      up-rise c s₀ s′ c₁ s pl h wq le F with m≤n⇒m<n∨m≡n (subst (λ t → owed (plug c s′) ≤ owed t) (sym pl) (plug-≤ c s′ s₀ F le))
      ... | inj₁ lt = by-owed (subst (λ w → wt c + owed (plug c s′) < w + owed (plug c₁ s)) (sym wq) (+-monoʳ-< (wt c) lt))
      ... | inj₂ eq = by-flight (cong₂ _+_ (sym wq) eq) refl (subst (height c <_) (sym h) (n<1+n _))

      up-abs : ∀ {Γ A Γ₁ A₁} (c : Ctx R Γ A) (s₀ s′ : St Γ A) (c₁ : Ctx R Γ₁ A₁) (s : St Γ₁ A₁) {e p p′}
             → plug c₁ s ≡ plug c s₀ → owed s′ ≤ owed s₀ → Fed≤ s′ s₀
             → W ⟨ c , s′ , absorbed , p′ ⟩ ≺ W ⟨ c₁ , s , rising e , p ⟩
      up-abs c s₀ s′ c₁ s pl le F =
        by-owed (≤-trans (s≤s (subst (λ t → owed (plug c s′) ≤ owed t) (sym pl) (plug-≤ c s′ s₀ F le)))
                  (+-monoˡ-≤ (owed (plug c₁ s)) (wt-pos c₁)))

      up-if : ∀ {Γ A Γ₁ A₁} (c : Ctx R Γ A) (s₀ s′ : St Γ A) (c₁ : Ctx R Γ₁ A₁) (s : St Γ₁ A₁) b {e e′ p p′}
            → plug c₁ s ≡ plug c s₀ → height c₁ ≡ suc (height c) → wt c₁ ≡ wt c → owed s′ ≤ owed s₀ → Fed≤ s′ s₀
            → W ⟨ c , s′ , (if b then rising e′ else absorbed) , p′ ⟩ ≺ W ⟨ c₁ , s , rising e , p ⟩
      up-if c s₀ s′ c₁ s true  {e} {e′} {p} {p′} pl h wq le F = up-rise c s₀ s′ c₁ s {e} {e′} {p} {p′} pl h wq le F
      up-if c s₀ s′ c₁ s false {e} {e′} {p} {p′} pl h wq le F = up-abs c s₀ s′ c₁ s {e} {p} {p′} pl le F

      -- A source's step fed to its connect's body, absorbed there: each
      -- joiner's entry is paid out of the weight the event carried.
      at-src : ∀ {Γ X B} (c : Ctx R Γ B) k k′ (b : St (X ∷ Γ) B) (s : St Γ X) {e e′ p p′} → csW k′ ≡ csW k
             → W ⟨ c , connS k′ s (feed (here refl) p′ e′ b) , absorbed , p ⟩ ≺ W ⟨ inSrc k b c , s , rising e , p ⟩
      at-src c k k′ b s {e} {e′} {p} {p′} ck =
        by-owed (src-low (owed (plug c (connS k′ s (feed (here refl) p′ e′ b)))) (owed (plug c (connS k s b))) (wt c) (fed (here refl) b)
                  (wt-pos c)
                  (plug-grow c (connS k′ s (feed (here refl) p′ e′ b)) (connS k s b) (fed (here refl) b)
                    (src-fed k k′ s b p′ e′) (src-owed k k′ s b p′ e′ ck)))

      ----------------------------------------------------------------------
      -- A subscription begun: the node `s″` in place of `s`

      sub-sub : ∀ {Γ A Γ₁ A₁} (c : Ctx R Γ A) (s s″ : St Γ A) (c₁ : Ctx R Γ₁ A₁) (s₁ : St Γ₁ A₁) {p p′}
              → plug c₁ s₁ ≡ plug c s″ → suc (owed s″) ≤ owed s → Fed≤ s″ s
              → W ⟨ c₁ , s₁ , subscribing , p′ ⟩ ≺ W ⟨ c , s , subscribing , p ⟩
      sub-sub c s s″ c₁ s₁ pl lt F = by-owed (subst (λ t → suc (owed t) ≤ owed (plug c s)) (sym pl) (plug-<′ c s″ s F lt))

      sub-abs : ∀ {Γ A} (c : Ctx R Γ A) (s s″ : St Γ A) {p p′} → suc (owed s″) ≤ owed s → Fed≤ s″ s
              → W ⟨ c , s″ , absorbed , p′ ⟩ ≺ W ⟨ c , s , subscribing , p ⟩
      sub-abs c s s″ lt F = by-owed (plug-<′ c s″ s F lt)

      ----------------------------------------------------------------------
      -- A mark run at the node `s′` the search found, left as `s″`

      at-abs : ∀ {Γ A Γ′ A′} (c : Ctx R Γ A) (s : St Γ A) (c′ : Ctx R Γ′ A′) (s′ s″ : St Γ′ A′) {p p′}
             → plug c′ s′ ≡ plug c s → suc (owed s″) ≤ owed s′ → Fed≤ s″ s′
             → W ⟨ c′ , s″ , absorbed , p′ ⟩ ≺ W ⟨ c , s , absorbed , p ⟩
      at-abs c s c′ s′ s″ pl lt F = by-owed (subst (λ t → suc (owed (plug c′ s″)) ≤ owed t) pl (plug-<′ c′ s″ s′ F lt))

      at-rise : ∀ {Γ A Γ′ A′} (c : Ctx R Γ A) (s : St Γ A) (c′ : Ctx R Γ′ A′) (s′ s″ : St Γ′ A′) {e p p′}
              → plug c′ s′ ≡ plug c s → suc (owed s″) ≤ owed s′ → Fed≤ s″ s′
              → W ⟨ c′ , s″ , rising e , p′ ⟩ ≺ W ⟨ c , s , absorbed , p ⟩
      at-rise c s c′ s′ s″ pl lt F with m≤n⇒m<n∨m≡n (subst (λ t → wt c′ + owed (plug c′ s″) ≤ owed t) pl (plug-< c′ s″ s′ F lt))
      ... | inj₁ l  = by-owed l
      ... | inj₂ eq = by-calm eq (s≤s z≤n)

      at-if : ∀ {Γ A Γ′ A′} (c : Ctx R Γ A) (s : St Γ A) (c′ : Ctx R Γ′ A′) (s′ s″ : St Γ′ A′) b {e p p′}
            → plug c′ s′ ≡ plug c s → suc (owed s″) ≤ owed s′ → Fed≤ s″ s′
            → W ⟨ c′ , s″ , (if b then rising e else absorbed) , p′ ⟩ ≺ W ⟨ c , s , absorbed , p ⟩
      at-if c s c′ s′ s″ true  {e} {p} {p′} pl lt F = at-rise c s c′ s′ s″ {e} {p} {p′} pl lt F
      at-if c s c′ s′ s″ false {e} {p} {p′} pl lt F = at-abs c s c′ s′ s″ {p} {p′} pl lt F

      at-sub : ∀ {Γ A Γ′ A′ Γ₁ A₁} (c : Ctx R Γ A) (s : St Γ A) (c′ : Ctx R Γ′ A′) (s′ s″ : St Γ′ A′)
               (c₁ : Ctx R Γ₁ A₁) (s₁ : St Γ₁ A₁) {p p′}
             → plug c′ s′ ≡ plug c s → plug c₁ s₁ ≡ plug c′ s″ → suc (owed s″) ≤ owed s′ → Fed≤ s″ s′
             → W ⟨ c₁ , s₁ , subscribing , p′ ⟩ ≺ W ⟨ c , s , absorbed , p ⟩
      at-sub c s c′ s′ s″ c₁ s₁ pl pl₁ lt F =
        by-owed (subst₂ (λ x t → suc (owed x) ≤ owed t) (sym pl₁) pl (plug-<′ c′ s″ s′ F lt))

      -- A teardown run: no more owed, one teardown fewer.
      at-torn : ∀ {Γ A Γ′ A′} (c : Ctx R Γ A) (s : St Γ A) (c′ : Ctx R Γ′ A′) (s′ s″ : St Γ′ A′) {p p′}
              → plug c′ s′ ≡ plug c s → owed s″ ≤ owed s′ → torn s″ < torn s′ → Fed≤ s″ s′
              → W ⟨ c′ , s″ , absorbed , p′ ⟩ ≺ W ⟨ c , s , absorbed , p ⟩
      at-torn c s c′ s′ s″ pl le tl F with m≤n⇒m<n∨m≡n (subst (λ t → owed (plug c′ s″) ≤ owed t) pl (plug-≤ c′ s″ s′ F le))
      ... | inj₁ l  = by-owed l
      ... | inj₂ eq = by-torn eq refl refl (subst (λ t → torn (plug c′ s″) < torn t) pl (plug-torn c′ s′ s″ tl))

      att-≤ : ∀ x y f a a′ b → a′ ≤ a → suc ((((x + 0) + y) + f * a′) + b) ≤ (((x + 1) + y) + f * a) + b
      att-≤ x y f a a′ b le =
        subst (_≤ (((x + 1) + y) + f * a) + b) (att-split x y (f * a′) b) (+-monoˡ-≤ b (+-monoʳ-≤ ((x + 1) + y) (*-monoʳ-≤ f le)))

  ----------------------------------------------------------------------
  -- The mark the search found, run

  ran : ∀ {Γ A Γ′ A′} (c : Ctx R Γ A) (s : St Γ A) (c′ : Ctx R Γ′ A′) (s′ : St Γ′ A′) (m : Mark) key p
      → search top (plug c s) ≡ just (found (Γ′ , A′ , c′ , s′) m key) → plug c′ s′ ≡ plug c s → Owns s′ m
      → Spends ⟨ c , s , absorbed , p ⟩ (took (runᴹ c′ s′ m p))
  ran c s c′ (ofS i p₀ []) _ key p eq pl ofO with closed c′
  ... | true  = lowers (at-abs c s c′ (ofS i p₀ []) doneS pl ≤-refl (λ _ → ≤-refl))
  ... | false = lowers (at-rise c s c′ (ofS i p₀ []) doneS pl ≤-refl (λ _ → ≤-refl))
  ran c s c′ (ofS i p₀ (x ∷ xs)) _ key p eq pl ofO with closed c′
  ... | true  = lowers (at-abs c s c′ (ofS i p₀ (x ∷ xs)) doneS pl (s≤s z≤n) (λ _ → ≤-refl))
  ... | false = lowers (at-rise c s c′ (ofS i p₀ (x ∷ xs)) (ofS (suc i) p₀ xs) pl ≤-refl (λ _ → ≤-refl))
  ran c s c′ (cutS l (attAt p₀) s₁) _ key p eq pl attO with unsubIf (not l) s₁ | unsubIf-≤ (not l) s₁ | unsubIf-F (not l) s₁
  ... | s₂ , t | le | F = lowers (at-abs c s c′ (cutS l (attAt p₀) s₁) (cutS l attached s₂) pl (s≤s le) F)
  ran c s c′ (takeS i q (cpAt p₀) s₁) _ key p eq pl cpO =
    lowers (at-if c s c′ (takeS i q (cpAt p₀) s₁) (takeS i q (cutAt p₀) s₁) (not (closed c′)) pl ≤-refl (λ _ → ≤-refl))
  ran c s c′ (takeS i q (cutAt p₀) s₁) _ key p eq pl cutO with cutᴹ s₁ | cut-≤ s₁ | cut-F s₁
  ... | s₂ , t | le | F = lowers (at-abs c s c′ (takeS i q (cutAt p₀) s₁) (takeS i q (overAt p₀) s₂) pl (s≤s le) F)
  ran c s c′ (connS (cs cl sl sa (just q) nothing ow r e) o b) _ key p eq pl (bodyO _) =
    lowers (at-sub c s c′ (connS (cs cl sl sa (just q) nothing ow r e) o b) (connS (cs cl sl sa nothing (just (q ⊕ [ ix 1 ])) ow r e) o b)
              (inSrc (cs cl sl sa nothing (just (q ⊕ [ ix 1 ])) ow r e) b c′) o pl refl ≤-refl (λ _ → ≤-refl))
  ran c s c′ (connS (cs cl sl sa (just q) (just a) ow r e) o b) _ key p eq pl (bodyO _) =
    lowers (at-sub c s c′ (connS (cs cl sl sa (just q) (just a) ow r e) o b) (connS (cs cl sl sa nothing (just (q ⊕ [ ix 1 ])) ow r e) o b)
              (inSrc (cs cl sl sa nothing (just (q ⊕ [ ix 1 ])) ow r e) b c′) o pl refl (n≤1+n _) (λ _ → ≤-refl))
  ran c s c′ (connS (cs cl sl sa nothing as ow r e) o b) _ key p eq pl (bodyO ())
  ran c s c′ (connS (cs cl sl sa ba (just q) ow r e) o b) _ key p eq pl (srcAttO _)
    with unsubIf (not sl) o | unsubIf-≤ (not sl) o | unsubIf-F (not sl) o
  ... | o′ , t | le | F = lowers (at-abs c s c′ (connS (cs cl sl sa ba (just q) ow r e) o b) (connS (cs cl sl true ba nothing ow r e) o′ b) pl
                            (att-≤ (just? 2 ba) (one sl) (fan b) (owed o) (owed o′) (owed b) le)
                            (λ i → +-monoˡ-≤ (fed (there i) b) (*-monoʳ-≤ (fan b) (F i))))
  ran c s c′ (connS (cs cl sl sa ba nothing ow r e) o b) _ key p eq pl (srcAttO ())
  ran c s c′ (connS (cs cl sl sa ba as (just q) r e) o b) _ key p eq pl (owedO _)
    with unsubIf sa o | unsubIf-≤ sa o | unsubIf-torn sa o | unsubIf-F sa o
  ... | o′ , t | le | tl | F = lowers (at-torn c s c′ (connS (cs cl sl sa ba as (just q) r e) o b) (connS (cs cl false sa ba as nothing r e) o′ b) pl
                                 (+-mono-≤ (+-mono-≤ (+-monoʳ-≤ (just? 2 ba + just? 1 as) z≤n) (*-monoʳ-≤ (fan b) le)) (≤-refl {owed b}))
                                 (s≤s (+-monoˡ-≤ (torn b) tl))
                                 (λ i → +-monoˡ-≤ (fed (there i) b) (*-monoʳ-≤ (fan b) (F i))))
  ran c s c′ (connS (cs cl sl sa ba as nothing r e) o b) _ key p eq pl (owedO ())
  ran c s c′ (joinS j g x ((q , nx a) ∷ ib)) _ key p eq pl joinO =
    lowers (at-if c s c′ (joinS j g x ((q , nx a) ∷ ib)) (joinS j g x ib) (g ∧ not (closed c′)) pl ≤-refl (λ _ → ≤-refl))
  ran c s c′ (joinS j g x ((q , cp) ∷ ib)) _ key p eq pl joinO =
    lowers (at-if c s c′ (joinS j g x ((q , cp) ∷ ib)) (joinS j false x ib) (g ∧ not (closed c′)) pl ≤-refl (λ _ → z≤n))
  ran c s c′ (coldS b (ending e₀)) _ key p eq pl (leafO _) =
    lowers (at-if c s c′ (coldS b (ending e₀)) (coldS false over) (not (closed c′)) pl ≤-refl (λ _ → ≤-refl))
  ran c s c′ (coldS b over) _ key p eq pl (leafO ())
  ran c s c′ (coldS false (play τ u i t fr)) _ key p eq pl (leafO _) =
    lowers (at-abs c s c′ (coldS false (play τ u i t fr)) (coldS false over) pl (s≤s z≤n) (λ _ → ≤-refl))
  ran c s c′ (coldS true (play τ u i t fr)) _ key p eq pl (leafO _) with closed c′ in ce
  ... | true = lowers (at-abs c s c′ (coldS true (play τ u i t fr)) (coldS true over) pl (s≤s z≤n) (λ _ → ≤-refl))
  ran c s c′ (coldS true (play τ u i t (emit a k))) _ key p eq pl (leafO _) | false =
    lowers (at-rise c s c′ (coldS true (play τ u i t (emit a k))) (coldS true (play τ u (suc i) t k)) pl ≤-refl (λ _ → ≤-refl))
  ran c s c′ (coldS true (play τ u i t (stall k))) _ key p eq pl (leafO _) | false = skips (stallᵏ eq ce)
  ran c s c′ (coldS true (play τ u i t (close k))) _ key p eq pl (leafO _) | false = skips (closeᵏ eq ce)

  ----------------------------------------------------------------------
  -- Every step, by its mode

  spends : ∀ m → Inv m → Spends m (step m)
  spends ⟨ top , s , rising (nx a) , p ⟩ iv = spent λ ()
  spends ⟨ top , s , rising cp , p ⟩ iv = spent λ ()
  spends ⟨ inMap f c , s , rising e , p ⟩ iv =
    lowers (up-rise c (mapS f s) (mapS f s) (inMap f c) s refl refl refl ≤-refl (λ _ → ≤-refl))
  spends ⟨ inScan f z c , s , rising (nx a) , p ⟩ iv =
    lowers (up-rise c (scanS f z s) (scanS f (f z a) s) (inScan f z c) s refl refl refl ≤-refl (λ _ → ≤-refl))
  spends ⟨ inScan f z c , s , rising cp , p ⟩ iv =
    lowers (up-rise c (scanS f z s) (scanS f z s) (inScan f z c) s refl refl refl ≤-refl (λ _ → ≤-refl))
  spends ⟨ inCut l a c , s , rising e , p ⟩ iv =
    lowers (up-if c (cutS l a s) (cutS l a s) (inCut l a c) s l refl refl refl ≤-refl (λ _ → ≤-refl))
  spends ⟨ inLn b c , s , rising e , p ⟩ iv = lowers (up-rise c (lnS b s) (lnS b s) (inLn b c) s refl refl refl ≤-refl (λ _ → ≤-refl))
  spends ⟨ inTake true q free c , s , rising (nx a) , p ⟩ iv with q a
  ... | true  = lowers (up-rise c (takeS true q free s) (takeS true q free s) (inTake true q free c) s refl refl refl ≤-refl (λ _ → ≤-refl))
  ... | false = lowers (up-rise c (takeS true q free s) (takeS true q (cpAt p) s) (inTake true q free c) s refl refl refl (n≤1+n _)
                          (λ _ → ≤-refl))
  spends ⟨ inTake false q free c , s , rising (nx a) , p ⟩ iv with q a
  ... | true  = lowers (up-rise c (takeS false q free s) (takeS false q free s) (inTake false q free c) s refl refl refl ≤-refl
                          (λ _ → ≤-refl))
  ... | false = lowers (up-abs c (takeS false q free s) (takeS false q (cpAt p) s) (inTake false q free c) s refl (n≤1+n _) (λ _ → ≤-refl))
  spends ⟨ inTake i q free c , s , rising cp , p ⟩ iv =
    lowers (up-rise c (takeS i q free s) (takeS i q free s) (inTake i q free c) s refl refl refl ≤-refl (λ _ → ≤-refl))
  spends ⟨ inTake i q (cpAt r) c , s , rising e , p ⟩ iv =
    lowers (up-abs c (takeS i q (cpAt r) s) (takeS i q (cpAt r) s) (inTake i q (cpAt r) c) s refl ≤-refl (λ _ → ≤-refl))
  spends ⟨ inTake i q (cutAt r) c , s , rising e , p ⟩ iv =
    lowers (up-abs c (takeS i q (cutAt r) s) (takeS i q (cutAt r) s) (inTake i q (cutAt r) c) s refl ≤-refl (λ _ → ≤-refl))
  spends ⟨ inTake i q (overAt r) c , s , rising e , p ⟩ iv =
    lowers (up-abs c (takeS i q (overAt r) s) (takeS i q (overAt r) s) (inTake i q (overAt r) c) s refl ≤-refl (λ _ → ≤-refl))
  spends ⟨ inOuter op f d n q ls c , o , rising (nx a) , p ⟩ iv = skips outerᵏ
  spends ⟨ inOuter op f true n q ls c , o , rising cp , p ⟩ iv =
    lowers (up-abs c (flatS op f true n q o ls) (flatS op f true n q o ls) (inOuter op f true n q ls c) o refl ≤-refl (λ _ → ≤-refl))
  spends ⟨ inOuter op f false n q ls c , o , rising cp , p ⟩ iv =
    lowers (up-if c (flatS op f false n q o ls) (flatS op f true n q o ls) (inOuter op f false n q ls c) o
              ((n ≡ᵇ 0) ∧ null q) refl refl refl (n≤1+n _) (λ _ → ≤-refl))
  spends ⟨ inLanes op f d n q o pre post c , s , rising (nx b) , p ⟩ iv with alive s
  ... | true  = lowers (up-rise c (flatS op f d n q o (pre ʳ++ s ∷ post)) (flatS op f d n q o (pre ʳ++ s ∷ post))
                          (inLanes op f d n q o pre post c) s refl refl refl ≤-refl (λ _ → ≤-refl))
  ... | false = lowers (up-abs c (flatS op f d n q o (pre ʳ++ s ∷ post)) (flatS op f d n q o (pre ʳ++ s ∷ post))
                          (inLanes op f d n q o pre post c) s refl ≤-refl (λ _ → ≤-refl))
  spends ⟨ inLanes op f d n [] o pre post c , s , rising cp , p ⟩ iv with alive s
  ... | true  = lowers (up-if c (flatS op f d n [] o (pre ʳ++ s ∷ post)) (flatS op f d (pred n) [] o (pre ʳ++ ended s ∷ post))
                          (inLanes op f d n [] o pre post c) s (d ∧ ((pred n ≡ᵇ 0) ∧ true)) refl refl refl
                          (lanes-≤ op f d n (pred n) [] o pre post s (ended s) (ended-≤ s))
                          (lanes-F o pre post (ended s) s (ended-F s)))
  ... | false = lowers (up-abs c (flatS op f d n [] o (pre ʳ++ s ∷ post)) (flatS op f d n [] o (pre ʳ++ s ∷ post))
                          (inLanes op f d n [] o pre post c) s refl ≤-refl (λ _ → ≤-refl))
  spends ⟨ inLanes op f d n (a ∷ q) o pre post c , s , rising cp , p ⟩ iv with alive s in al
  ... | true  = skips (laneᵏ al)
  ... | false = lowers (up-abs c (flatS op f d n (a ∷ q) o (pre ʳ++ s ∷ post)) (flatS op f d n (a ∷ q) o (pre ʳ++ s ∷ post))
                          (inLanes op f d n (a ∷ q) o pre post c) s refl ≤-refl (λ _ → ≤-refl))
  spends ⟨ inSrc k b c , s , rising (nx a) , p ⟩ iv = lowers (at-src c k k b s refl)
  spends ⟨ inSrc k b c , s , rising cp , p ⟩ iv = lowers (at-src c k (record k { closed = true ; endAt = p }) b s refl)
  spends ⟨ inBody k o c , s , rising (nx b) , p ⟩ iv =
    lowers (up-rise c (connS k o s) (connS k o s) (inBody k o c) s refl refl refl ≤-refl (λ _ → ≤-refl))
  spends ⟨ inBody k o c , s , rising cp , p ⟩ iv =
    lowers (up-rise c (connS k o s) (connS (record k { owedAt = just p }) o s) (inBody k o c) s refl refl refl ≤-refl (λ _ → ≤-refl))
  spends ⟨ c , pend (cold x) , subscribing , p ⟩ iv =
    lowers (sub-abs c (pend (cold x)) (coldS true (opening p (timelineAt x p))) (opening-< x p) (λ _ → z≤n))
  spends ⟨ c , pend empty , subscribing , p ⟩ iv = lowers (sub-abs c (pend empty) (ofS 0 p []) ≤-refl (λ _ → z≤n))
  spends ⟨ c , pend (of xs) , subscribing , p ⟩ iv = lowers (sub-abs c (pend (of xs)) (ofS 0 p xs) ≤-refl (λ _ → z≤n))
  spends ⟨ c , pend (map f s) , subscribing , p ⟩ iv =
    lowers (sub-sub c (pend (map f s)) (mapS f (pend s)) (inMap f c) (pend s) refl ≤-refl (λ _ → ≤-refl))
  spends ⟨ c , pend (scan f z s) , subscribing , p ⟩ iv =
    lowers (sub-sub c (pend (scan f z s)) (scanS f z (pend s)) (inScan f z c) (pend s) refl ≤-refl (λ _ → ≤-refl))
  spends ⟨ c , pend (takeWhile i q s) , subscribing , p ⟩ iv =
    lowers (sub-sub c (pend (takeWhile i q s)) (takeS i q free (cutS true (attAt p) (pend s)))
              (inCut true (attAt p) (inTake i q free c)) (pend s) refl ≤-refl (λ _ → ≤-refl))
  spends ⟨ c , pend (flatMap op f s) , subscribing , p ⟩ iv =
    lowers (sub-sub c (pend (flatMap op f s)) (flatS op f false 0 [] (cutS true (attAt p) (pend s)) [])
              (inCut true (attAt p) (inOuter op f false 0 [] [] c)) (pend s) refl ≤-refl (λ i → ≤-reflexive (+-identityʳ (fedO i s))))
  spends ⟨ c , pend (connect s b) , subscribing , p ⟩ iv =
    lowers (sub-sub c (pend (connect s b)) (connS k (pend s) (pend b)) (inBody k (pend s) c) (pend b) refl ≤-refl (λ _ → ≤-refl))
    where
    k = cs false true false (just p) nothing nothing (p ⊕ [ ix 1 ]) root
  spends ⟨ c , pend (connected x) , subscribing , p ⟩ iv with closedUp c x
  ... | true  = lowers (sub-abs c (pend (connected x)) (ofS 0 p []) ≤-refl (λ _ → z≤n))
  ... | false = lowers (sub-abs c (pend (connected x)) (joinS p true x []) (s≤s z≤n) (λ _ → ≤-refl))
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
