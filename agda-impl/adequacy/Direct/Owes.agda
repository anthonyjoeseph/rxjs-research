{-# OPTIONS --guardedness #-}

-- WHAT A LIVE PART STILL OWES: an outer not yet over, and a lane still in
-- its list, each owe some row, if only their end.  A merge reads its
-- other parts' rows to decide whether it is over, so a part that owed
-- nothing while still live would end the merge early.
module adequacy.Direct.Owes where

open import Data.Bool using (true; false; T; _∧_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _ʳ++_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (suc; _+_)
open import Data.Nat.Properties using (+-suc)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)

open import Tree using (mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.MonotonicList.Events using (Pos)
open import denotation.EmissionSet using (EmissionSet; out; skip; end; MapT; map-out; map-skip; map-end)
open import operation.PureObservable using (module Machine)
open Machine using (St; Ctx; plug; alive; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
                    top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody)
open import adequacy.Direct using (∅; rows; rowsL; Lanes; Each; module Flat; _≃_)
open import adequacy.Direct.Up using (any-ʳ++ʳ; any-≈; _≈ᴸ_; []; _∷_; ≈ᴸ-refl; ≈ᴸ-sym; flat-≃; map-≃; ≃-refl)
open import adequacy.Direct.Bound using (Empty; empty-any; Single; EndLast; Spread; Parts; Live; G; GL; GLn; LnBody; live)

open _≃_

Owing : ∀ {A} → EmissionSet A → Set
Owing t = ¬ Empty t

mutual
  Owes : ∀ {Γ A} → St Γ A → Set
  Owes (mapS f s)                              = Owes s
  Owes (cutS true a s)                         = Owes s
  Owes (lnS b s)                               = Owes s
  Owes (flatS (mergeᶠ nothing) f d n q o ls)   = (¬ T d → Owing (rows o)) × Owes o × OwesL ls
  Owes _                                       = ⊤

  OwesL : ∀ {Γ A} → List (St Γ A) → Set
  OwesL []       = ⊤
  OwesL (s ∷ ls) = (T (alive s) → Owing (rows s)) × Owes s × OwesL ls

-- The frames a rising or subscribing event climbs, open, with what every
-- other part of a merge owes.
UpO : ∀ {R Γ A} → Ctx R Γ A → Set
UpO top                                           = ⊤
UpO (inMap f c)                                   = UpO c
UpO (inCut true a c)                              = UpO c
UpO (inLn true c)                                 = UpO c
UpO (inOuter (mergeᶠ nothing) f d n q ls c)       = OwesL ls × UpO c
UpO (inLanes (mergeᶠ nothing) f d n q o pre post c) =
  (¬ T d → Owing (rows o)) × Owes o × OwesL pre × OwesL post × UpO c
UpO _                                             = ⊥

-- What each frame asks of what its hole owes.
Need : ∀ {R Γ A} → Ctx R Γ A → St Γ A → Set
Need top                                           s = ⊤
Need (inMap f c)                                   s = Need c (mapS f s)
Need (inCut true a c)                              s = Need c (cutS true a s)
Need (inLn true c)                                 s = Need c (lnS true s)
Need (inOuter (mergeᶠ nothing) f d n q ls c)       s = (¬ T d → Owing (rows s)) × Need c (flatS (mergeᶠ nothing) f d n q s ls)
Need (inLanes (mergeᶠ nothing) f d n q o pre post c) s =
  (T (alive s) → Owing (rows s)) × Need c (flatS (mergeᶠ nothing) f d n q o (pre ʳ++ s ∷ post))
Need _                                             s = ⊤

owesL-ʳ++ : ∀ {Γ A} (xs : List (St Γ A)) {ys} → OwesL xs → OwesL ys → OwesL (xs ʳ++ ys)
owesL-ʳ++ []       _            b = b
owesL-ʳ++ (x ∷ xs) (a , o , os) b = owesL-ʳ++ xs os (a , o , b)

owesL-ʳ++⁻ : ∀ {Γ A} (xs : List (St Γ A)) {ys} → OwesL (xs ʳ++ ys) → OwesL xs × OwesL ys
owesL-ʳ++⁻ []       b = tt , b
owesL-ʳ++⁻ (x ∷ xs) b with owesL-ʳ++⁻ xs b
... | a , (h , o , c) = (h , o , a) , c

owes-join : ∀ {R Γ A} (c : Ctx R Γ A) {s : St Γ A} → UpO c → Owes s → Need c s → Owes (plug c s)
owes-join top                                     u          o n         = o
owes-join (inMap f c)                             u          o n         = owes-join c u o n
owes-join (inCut true a c)                        u          o n         = owes-join c u o n
owes-join (inLn true c)                           u          o n         = owes-join c u o n
owes-join (inOuter (mergeᶠ nothing) f d n q ls c) (ol , u)   o (h , nd)  = owes-join c u (h , o , ol) nd
owes-join (inLanes (mergeᶠ nothing) f d n q o′ pre post c) {s} (ho , oo , op , oq , u) o (h , nd) =
  owes-join c u (ho , oo , owesL-ʳ++ pre op (h , o , oq)) nd

------------------------------------------------------------------------
-- Rows owed up a frame

rowsL-ʳ++ : ∀ {Γ A} (xs : List (St Γ A)) {ys} → rowsL (xs ʳ++ ys) ≡ rowsL xs ʳ++ rowsL ys
rowsL-ʳ++ []       = refl
rowsL-ʳ++ (x ∷ xs) = rowsL-ʳ++ xs

≡→≃ : ∀ {A} {t u : EmissionSet A} → t ≡ u → t ≃ u
≡→≃ refl = ≃-refl

owing-≃ : ∀ {A} {t u : EmissionSet A} → t ≃ u → Owing t → Owing u
owing-≃ eq ow em = ow λ r → em (to eq r)

map-owing : ∀ {A B} (f : A → B) {t : EmissionSet A} → Owing t → Owing (MapT f t)
map-owing f {t} ow em = ow go
  where
    go : Empty t
    go {e = out _} r = em (map-out r)
    go {e = skip}  r = em (map-skip r)
    go {e = end}   r = em (map-end r)

module _ {A B : Set} (L : A → Pos → EmissionSet B) {O : EmissionSet A} {Ls : List (EmissionSet B)} where
  -- An outer owing a row: the merge owes one for it.
  flat-owing-o : Owing O → Owing (Flat.FlatR L O Ls)
  flat-owing-o ow em = ow go
    where
      go : Empty O
      go {e = out _} r = em (Flat.val r)
      go {e = skip}  r = em (Flat.step r)
      go {e = end}   r = em (Flat.opass r λ d → em (Flat.oend r d))

  flat-owing-l : Owing (Lanes Ls) → Owing (Flat.FlatR L O Ls)
  flat-owing-l ow em = ow go
    where
      go : Empty (Lanes Ls)
      go {e = out _} x = em (Flat.run x _)
      go {e = skip}  x = em (Flat.run x _)
      go {e = end}   x = em (Flat.rpass x λ d → em (Flat.rend x d))

  flat-empty : Empty O → Each Empty Ls → Empty (Flat.FlatR L O Ls)
  flat-empty eo el (Flat.val r)       = eo r
  flat-empty eo el (Flat.step r)      = eo r
  flat-empty eo el (Flat.oend r _)    = eo r
  flat-empty eo el (Flat.opass r _)   = eo r
  flat-empty eo el (Flat.lane r _ _)  = eo r
  flat-empty eo el (Flat.lend r _ _)  = eo r
  flat-empty eo el (Flat.lpass r _ _) = eo r
  flat-empty eo el (Flat.run x _)     = empty-any Ls el x
  flat-empty eo el (Flat.rend x _)    = empty-any Ls el x
  flat-empty eo el (Flat.rpass x _)   = empty-any Ls el x

-- A part owing a row: its frame's node owes one.
need-of : ∀ {R Γ A} (c : Ctx R Γ A) {s : St Γ A} → Owing (rows s) → Need c s
need-of top                                     ow = tt
need-of (inMap f c)                             ow = need-of c (map-owing f ow)
need-of (inCut true a c)                        ow = need-of c ow
need-of (inCut false a c)                       ow = tt
need-of (inLn true c)                           ow = need-of c ow
need-of (inLn false c)                          ow = tt
need-of (inScan f z c)                          ow = tt
need-of (inTake i q w c)                        ow = tt
need-of (inOuter (mergeᶠ nothing) f d n q ls c) ow = (λ _ → ow) , need-of c (flat-owing-o _ ow)
need-of (inOuter (mergeᶠ (just _)) f d n q ls c) ow = tt
need-of (inOuter switchᶠ f d n q ls c)          ow = tt
need-of (inOuter exhaustᶠ f d n q ls c)         ow = tt
need-of (inLanes (mergeᶠ nothing) f d n q o pre post c) {s} ow =
  (λ _ → ow) , need-of c (owing-≃ (≡→≃ (cong (Flat.FlatR _ (rows o)) (sym (rowsL-ʳ++ pre))))
                                  (flat-owing-l _ λ em → ow λ r → em (any-ʳ++ʳ (rowsL pre) (inj₁ r))))
need-of (inLanes (mergeᶠ (just _)) f d n q o pre post c) ow = tt
need-of (inLanes switchᶠ f d n q o pre post c)  ow = tt
need-of (inLanes exhaustᶠ f d n q o pre post c) ow = tt
need-of (inSrc k b c)                           ow = tt
need-of (inBody k o c)                          ow = tt

------------------------------------------------------------------------
-- Lanes still in their list

live-ʳ++ : ∀ {Γ A} (xs : List (St Γ A)) {ys} → live (xs ʳ++ ys) ≡ live xs + live ys
live-ʳ++ []       = refl
live-ʳ++ (x ∷ xs) {ys} rewrite live-ʳ++ xs {x ∷ ys} with alive x
... | true  = +-suc (live xs) (live ys)
... | false = refl

-- A lane still in its list owes a row.
live-owing : ∀ {Γ A} (xs : List (St Γ A)) {m} → OwesL xs → live xs ≡ suc m → Owing (Lanes (rowsL xs))
live-owing (x ∷ xs) (h , _ , os) eq with alive x
... | true  = λ em → h tt λ r → em (inj₁ r)
... | false = λ em → live-owing xs os eq λ y → em (inj₂ y)

goodL-ʳ++ : ∀ {Γ A} {v} (xs : List (St Γ A)) {ys} → GL v xs → GL v ys → GL v (xs ʳ++ ys)
goodL-ʳ++ []       _        b = b
goodL-ʳ++ (x ∷ xs) (g , gs) b = goodL-ʳ++ xs gs (g , b)

goodL-ʳ++⁻ : ∀ {Γ A} {v} (xs : List (St Γ A)) {ys} → GL v (xs ʳ++ ys) → GL v xs × GL v ys
goodL-ʳ++⁻ []       b = tt , b
goodL-ʳ++⁻ (x ∷ xs) b with goodL-ʳ++⁻ xs b
... | a , (g , c) = (g , a) , c

------------------------------------------------------------------------
-- A node swapped for one owing the same rows

single-≃ : ∀ {A} {t u : EmissionSet A} → t ≃ u → Single t → Single u
single-≃ eq s r r′ = s (from eq r) (from eq r′)

endlast-≃ : ∀ {A} {t u : EmissionSet A} → t ≃ u → EndLast t → EndLast u
endlast-≃ eq el r r′ = el (from eq r) (from eq r′)

empty-≃ : ∀ {A} {t u : EmissionSet A} → t ≃ u → Empty t → Empty u
empty-≃ eq em r = em (from eq r)

live-endlast : ∀ {A} v {t u : EmissionSet A} → t ≃ u → Live v (EndLast t) → Live v (EndLast u)
live-endlast true  eq el = endlast-≃ eq el
live-endlast false eq el = tt

-- The same rows, the same liveness, a good node and lane for a good one:
-- the same good tree.
record Swap {Γ A} (s s′ : St Γ A) : Set where
  field
    same : rows s ≃ rows s′
    live≡ : alive s ≡ alive s′
    node : ∀ v → G v s → G v s′
    lane : ∀ v → GLn v s → GLn v s′
    body : ∀ v b → LnBody v b s → LnBody v b s′
open Swap

live-swap : ∀ {Γ A} (xs : List (St Γ A)) {s s′ ys} → alive s ≡ alive s′ → live (xs ʳ++ s ∷ ys) ≡ live (xs ʳ++ s′ ∷ ys)
live-swap xs {s} {s′} {ys} eq rewrite live-ʳ++ xs {s ∷ ys} | live-ʳ++ xs {s′ ∷ ys} | eq = refl

goodL-swap : ∀ {Γ A} {v} (xs : List (St Γ A)) {s s′ ys} → (GLn v s → GLn v s′) → GL v (xs ʳ++ s ∷ ys) → GL v (xs ʳ++ s′ ∷ ys)
goodL-swap xs h g with goodL-ʳ++⁻ xs g
... | gx , (gs , gy) = goodL-ʳ++ xs gx (h gs , gy)

lanes-≃ : ∀ {Γ A} (xs : List (St Γ A)) {ys ys′} → rowsL ys ≈ᴸ rowsL ys′ → rowsL (xs ʳ++ ys) ≈ᴸ rowsL (xs ʳ++ ys′)
lanes-≃ []       h = h
lanes-≃ (x ∷ xs) h = lanes-≃ xs (≃-refl ∷ h)

spread-≈ : ∀ {B} {Ls Ls′ : List (EmissionSet B)} → Ls ≈ᴸ Ls′ → Spread Ls → Spread Ls′
spread-≈ []       _       = tt
spread-≈ (e ∷ es) (a , s) = (λ r x → a (from e r) (any-≈ (≈ᴸ-sym es) x)) , spread-≈ es s

parts-≃ : ∀ {A B} {O O′ : EmissionSet A} {Ls Ls′ : List (EmissionSet B)} → O ≃ O′ → Ls ≈ᴸ Ls′ → Parts O Ls → Parts O′ Ls′
parts-≃ eo es (a , s) = (λ r x → a (from eo r) (any-≈ (≈ᴸ-sym es) x)) , spread-≈ es s

-- A node owing nothing and never good.
void : ∀ {Γ A} {s s′ : St Γ A} → rows s ≡ ∅ → rows s′ ≡ ∅ → alive s ≡ alive s′ → (∀ v → G v s → ⊥) → (∀ v → GLn v s → ⊥) → (∀ v b → LnBody v b s → ⊥) → Swap s s′
void e e′ al ng nl nb = record { same = ≡→≃ (trans e (sym e′)) ; live≡ = al ; node = λ v g → ⊥-elim (ng v g) ; lane = λ v g → ⊥-elim (nl v g) ; body = λ v b g → ⊥-elim (nb v b g) }

good-swap : ∀ {R Γ A} (c : Ctx R Γ A) {s s′ : St Γ A} → Swap s s′ → ∀ {v} → G v (plug c s) → G v (plug c s′)
good-swap top              sw {v} g = node sw v g
good-swap (inMap f c)      sw g = good-swap c (record { same = map-≃ f (same sw) ; live≡ = refl ; node = node sw ; lane = λ _ () ; body = λ _ _ () }) g
good-swap (inScan f z c)   sw g = good-swap c (void refl refl refl (λ _ ()) (λ _ ()) (λ _ _ ())) g
good-swap (inCut true a c) sw g = good-swap c (record { same = same sw ; live≡ = refl ; node = λ v → node sw (v ∧ true) ; lane = λ _ () ; body = λ { v b (eq , gs , el) → eq , node sw (v ∧ b) gs , live-endlast (v ∧ b) (same sw) el } }) g
good-swap (inCut false a c) sw g = good-swap c (record { same = ≃-refl ; live≡ = refl ; node = λ v → node sw (v ∧ false) ; lane = λ _ () ; body = λ { v b (eq , gs , el) → eq , node sw (v ∧ b) gs , live-endlast (v ∧ b) (same sw) el } }) g
good-swap (inLn true c)    sw g = good-swap c (record { same = same sw ; live≡ = refl ; node = λ _ () ; lane = λ v → body sw v true ; body = λ _ _ () }) g
good-swap (inLn false c)   sw g = good-swap c (record { same = ≃-refl ; live≡ = refl ; node = λ _ () ; lane = λ v → body sw v false ; body = λ _ _ () }) g
good-swap (inTake i q w c) sw g = good-swap c (void refl refl refl (λ _ ()) (λ _ ()) (λ _ _ ())) g
good-swap (inOuter (mergeᶠ nothing) f d n q ls c) {s} {s′} sw g =
  good-swap c {s = flatS (mergeᶠ nothing) f d n q s ls} {s′ = flatS (mergeᶠ nothing) f d n q s′ ls} (record { same = flat-≃ _ (same sw) (≈ᴸ-refl (rowsL ls)) ; live≡ = refl ; lane = λ _ () ; body = λ _ _ ()
                      ; node = λ { true (go , gl , qe , si , el , nl , ov , pa) → node sw true go , gl , qe , (λ {q} {e} {e′} → single-≃ (same sw) si {q} {e} {e′}) , (λ {c} {q} {e} → endlast-≃ (same sw) el {c} {q} {e}) , nl , (λ t {q} {e} → empty-≃ (same sw) (ov t) {q} {e}) , parts-≃ (same sw) (≈ᴸ-refl (rowsL ls)) pa
                                 ; false (go , gl , qe , _) → node sw false go , gl , qe , tt } }) g
good-swap (inOuter (mergeᶠ (just _)) f d n q ls c) sw g = good-swap c (void refl refl refl (λ _ ()) (λ _ ()) (λ _ _ ())) g
good-swap (inOuter switchᶠ f d n q ls c)  sw g = good-swap c (void refl refl refl (λ _ ()) (λ _ ()) (λ _ _ ())) g
good-swap (inOuter exhaustᶠ f d n q ls c) sw g = good-swap c (void refl refl refl (λ _ ()) (λ _ ()) (λ _ _ ())) g
good-swap (inLanes (mergeᶠ nothing) f d n q o pre post c) {s} {s′} sw g =
  good-swap c {s = flatS (mergeᶠ nothing) f d n q o (pre ʳ++ s ∷ post)} {s′ = flatS (mergeᶠ nothing) f d n q o (pre ʳ++ s′ ∷ post)} (record { same = flat-≃ _ ≃-refl (lanes-≃ pre (same sw ∷ ≈ᴸ-refl (rowsL post))) ; live≡ = refl ; lane = λ _ () ; body = λ _ _ ()
                      ; node = λ { true (go , gl , qe , si , el , nl , ov , pa) → go , goodL-swap pre (lane sw true) gl , qe , si , el , trans nl (live-swap pre (live≡ sw)) , ov , parts-≃ ≃-refl (lanes-≃ pre (same sw ∷ ≈ᴸ-refl (rowsL post))) pa
                                 ; false (go , gl , qe , _) → go , goodL-swap pre (lane sw false) gl , qe , tt } }) g
good-swap (inLanes (mergeᶠ (just _)) f d n q o pre post c) sw g = good-swap c (void refl refl refl (λ _ ()) (λ _ ()) (λ _ _ ())) g
good-swap (inLanes switchᶠ f d n q o pre post c)  sw g = good-swap c (void refl refl refl (λ _ ()) (λ _ ()) (λ _ _ ())) g
good-swap (inLanes exhaustᶠ f d n q o pre post c) sw g = good-swap c (void refl refl refl (λ _ ()) (λ _ ()) (λ _ _ ())) g
good-swap (inSrc k b c)    sw g = good-swap c (void refl refl refl (λ _ ()) (λ _ ()) (λ _ _ ())) g
good-swap (inBody k o c)   sw g = good-swap c (void refl refl refl (λ _ ()) (λ _ ()) (λ _ _ ())) g
