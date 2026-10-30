{-# OPTIONS --guardedness #-}

-- WHAT A LIVE PART STILL OWES: an outer not yet over, and a lane still in
-- its list, each owe some row, if only their end.  A merge reads its
-- other parts' rows to decide whether it is over, so a part that owed
-- nothing while still live would end the merge early.
module adequacy.Owes where

open import Data.Bool using (Bool; true; false; T; _∧_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _ʳ++_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (suc; _+_)
open import Data.Nat.Properties using (+-suc)
open import Data.Product using (_×_; _,_)
open import Data.List.Relation.Unary.All using ([]) renaming (_∷_ to _∷ᴬ_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to tt₁)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym)

open import Tree using (mergeᶠ; switchᶠ; exhaustᶠ)
open import denotation.Events using (Pos)
open import denotation.EmissionSet using (EmissionSet; out; skip; pin; end; module Connecting; module Scan; MapT; map-out; map-skip; map-pin; map-end; DenEnv)
open import operation.PureObservable using (module Machine)
open Machine using (St; Ctx; CS; plug; alive; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
                    top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody)
open import adequacy.Rows using (∅; env; rows; rowsL; pendRows; Lanes; Each; module Flat; _≃_; Hot)
open import adequacy.Up using (_≈ᴸ_; []; _∷_; ≈ᴸ-refl; row-≃; map-≃; scan-≃; ≃-refl; conn-≃; rows-hot; ʳ++-≈)
open import adequacy.Bound using (Empty; empty-any; EndLast; Roots; Rooted; Live; G; GL; GLn; LnBody; SrcG; Held; live;
  mergeG-map)

open _≃_

Owing : ∀ {A} → EmissionSet A → Set
Owing t = ¬ Empty t

mutual
  Owes : ∀ {Γ A} → DenEnv Γ → St Γ A → Set
  Owes ρ (mapS f s)                              = Owes ρ s
  Owes ρ (scanS f z s)                           = Owes ρ s
  Owes ρ (cutS true a s)                         = Owes ρ s
  Owes ρ (lnS b s)                               = Owes ρ s
  Owes ρ (flatS (mergeᶠ nothing) f d n q o ls)   = (¬ T d → Owing (rows ρ o)) × Owes ρ o × OwesL ρ ls
  Owes ρ (connS k o b)                           = Owes ρ o × Owes (Hot (rows ρ o) k ∷ᴬ ρ) b
  Owes ρ _                                       = ⊤

  OwesL : ∀ {Γ A} → DenEnv Γ → List (St Γ A) → Set
  OwesL ρ []       = ⊤
  OwesL ρ (s ∷ ls) = (T (alive s) → Owing (rows ρ s)) × Owes ρ s × OwesL ρ ls

-- The frames a rising or subscribing event climbs, open, with what every
-- other part of a merge owes.
UpO : ∀ {R Γ A} → Ctx R Γ A → Set
UpO top                                           = ⊤
UpO (inMap f c)                                   = UpO c
UpO (inScan f z c)                                = UpO c
UpO (inCut true a c)                              = UpO c
UpO (inLn true c)                                 = UpO c
UpO (inOuter (mergeᶠ nothing) f d n q ls c)       = OwesL (env c) ls × UpO c
UpO (inLanes (mergeᶠ nothing) f d n q o pre post c) =
  (¬ T d → Owing (rows (env c) o)) × Owes (env c) o × OwesL (env c) pre × OwesL (env c) post × UpO c
UpO (inSrc k b c)                                 = UpO c
UpO (inBody k o c)                                = Owes (env c) o × UpO c
UpO _                                             = ⊥

-- What each frame asks of what its hole owes.
Need : ∀ {R Γ A} → Ctx R Γ A → St Γ A → Set
Need top                                           s = ⊤
Need (inMap f c)                                   s = Need c (mapS f s)
Need (inScan f z c)                                s = Need c (scanS f z s)
Need (inCut true a c)                              s = Need c (cutS true a s)
Need (inLn true c)                                 s = Need c (lnS true s)
Need (inOuter (mergeᶠ nothing) f d n q ls c)       s = (¬ T d → Owing (rows (env c) s)) × Need c (flatS (mergeᶠ nothing) f d n q s ls)
Need (inLanes (mergeᶠ nothing) f d n q o pre post c) s =
  (T (alive s) → Owing (rows (env c) s)) × Need c (flatS (mergeᶠ nothing) f d n q o (pre ʳ++ s ∷ post))
Need (inSrc k b c)                                s = Owes (Hot (rows (env c) s) k ∷ᴬ env c) b × Need c (connS k s b)
Need (inBody k o c)                               s = Need c (connS k o s)
Need _                                             s = ⊤

owesL-ʳ++ : ∀ {Γ A} {ρ : DenEnv Γ} (xs : List (St Γ A)) {ys} → OwesL ρ xs → OwesL ρ ys → OwesL ρ (xs ʳ++ ys)
owesL-ʳ++ []       _            b = b
owesL-ʳ++ (x ∷ xs) (a , o , os) b = owesL-ʳ++ xs os (a , o , b)

owesL-ʳ++⁻ : ∀ {Γ A} {ρ : DenEnv Γ} (xs : List (St Γ A)) {ys} → OwesL ρ (xs ʳ++ ys) → OwesL ρ xs × OwesL ρ ys
owesL-ʳ++⁻ []       b = tt , b
owesL-ʳ++⁻ (x ∷ xs) b with owesL-ʳ++⁻ xs b
... | a , (h , o , c) = (h , o , a) , c

owes-join : ∀ {R Γ A} (c : Ctx R Γ A) {s : St Γ A} → UpO c → Owes (env c) s → Need c s → Owes [] (plug c s)
owes-join top                                     u          o n         = o
owes-join (inMap f c)                             u          o n         = owes-join c u o n
owes-join (inScan f z c)                          u          o n         = owes-join c u o n
owes-join (inCut true a c)                        u          o n         = owes-join c u o n
owes-join (inLn true c)                           u          o n         = owes-join c u o n
owes-join (inOuter (mergeᶠ nothing) f d n q ls c) (ol , u)   o (h , nd)  = owes-join c u (h , o , ol) nd
owes-join (inLanes (mergeᶠ nothing) f d n q o′ pre post c) {s} (ho , oo , op , oq , u) o (h , nd) =
  owes-join c u (ho , oo , owesL-ʳ++ pre op (h , o , oq)) nd
owes-join (inSrc k b c)                           u          o (ob , n)  = owes-join c u (o , ob) n
owes-join (inBody k o′ c)                         (oo , u)   o n         = owes-join c u (oo , o) n

------------------------------------------------------------------------
-- Rows owed up a frame

rowsL-ʳ++ : ∀ {Γ A} {ρ : DenEnv Γ} (xs : List (St Γ A)) {ys} → rowsL ρ (xs ʳ++ ys) ≡ rowsL ρ xs ʳ++ rowsL ρ ys
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
    go {e = pin _} r = em (map-pin r)
    go {e = end}   r = em (map-end r)

module _ {A B : Set} (L : A → Pos → EmissionSet B) {O : EmissionSet A} {d : Bool} {Ls : List (EmissionSet B)} where
  -- An outer owing a row: the merge owes one for it.
  flat-owing-o : Owing O → Owing (Flat.JoinT L O d Ls)
  flat-owing-o ow em = ow go
    where
      go : Empty O
      go {e = out _} r = em (Flat.val r)
      go {e = skip}  r = em (Flat.step r)
      go {e = pin _} r = em (Flat.opin r)
      go {e = end}   r = em (Flat.opass r λ d → em (Flat.oend r d))

  flat-owing-l : Owing (Lanes Ls) → Owing (Flat.JoinT L O d Ls)
  flat-owing-l ow em = ow go
    where
      go : Empty (Lanes Ls)
      go {e = out _} x = em (Flat.run x _)
      go {e = skip}  x = em (Flat.run x _)
      go {e = pin _} x = em (Flat.run x _)
      go {e = end}   x = em (Flat.rpass x (λ ()) λ d → em (Flat.rend x (λ ()) d))

  flat-empty : Empty O → Each Empty Ls → Empty (Flat.JoinT L O d Ls)
  flat-empty eo el (Flat.val r)       = eo r
  flat-empty eo el (Flat.step r)      = eo r
  flat-empty eo el (Flat.opin r)      = eo r
  flat-empty eo el (Flat.oend r _)    = eo r
  flat-empty eo el (Flat.opass r _)   = eo r
  flat-empty eo el (Flat.lane r _ _ _ _)  = eo r
  flat-empty eo el (Flat.lend r _ _ _ _ _)  = eo r
  flat-empty eo el (Flat.lpass r _ _ _ _ _) = eo r
  flat-empty eo el (Flat.hand _ _ _ _ ())
  flat-empty eo el (Flat.left r _ _ _ _) = eo r
  flat-empty eo el (Flat.run x _)     = empty-any Ls el x
  flat-empty eo el (Flat.rend x _ _)  = empty-any Ls el x
  flat-empty eo el (Flat.rpass x _ _) = empty-any Ls el x
  flat-empty eo el (Flat.rhand _ ())

------------------------------------------------------------------------
-- Lanes still in their list

live-ʳ++ : ∀ {Γ A} (xs : List (St Γ A)) {ys} → live (xs ʳ++ ys) ≡ live xs + live ys
live-ʳ++ []       = refl
live-ʳ++ (x ∷ xs) {ys} rewrite live-ʳ++ xs {x ∷ ys} with alive x
... | true  = +-suc (live xs) (live ys)
... | false = refl

-- A lane still in its list owes a row.
live-owing : ∀ {Γ A} {ρ : DenEnv Γ} (xs : List (St Γ A)) {m} → OwesL ρ xs → live xs ≡ suc m → Owing (Lanes (rowsL ρ xs))
live-owing (x ∷ xs) (h , _ , os) eq with alive x
... | true  = λ em → h tt λ r → em (inj₁ r)
... | false = λ em → live-owing xs os eq λ y → em (inj₂ y)

goodL-ʳ++ : ∀ {Γ A} {ρ : DenEnv Γ} {v} (xs : List (St Γ A)) {ys} → GL ρ v xs → GL ρ v ys → GL ρ v (xs ʳ++ ys)
goodL-ʳ++ []       _        b = b
goodL-ʳ++ (x ∷ xs) (g , gs) b = goodL-ʳ++ xs gs (g , b)

goodL-ʳ++⁻ : ∀ {Γ A} {ρ : DenEnv Γ} {v} (xs : List (St Γ A)) {ys} → GL ρ v (xs ʳ++ ys) → GL ρ v xs × GL ρ v ys
goodL-ʳ++⁻ []       b = tt₁ , b
goodL-ʳ++⁻ (x ∷ xs) b with goodL-ʳ++⁻ xs b
... | a , (g , c) = (g , a) , c

------------------------------------------------------------------------
-- A node swapped for one owing the same rows

endlast-≃ : ∀ {A} {t u : EmissionSet A} → t ≃ u → EndLast t → EndLast u
endlast-≃ eq el r r′ = el (from eq r) (from eq r′)

empty-≃ : ∀ {A} {t u : EmissionSet A} → t ≃ u → Empty t → Empty u
empty-≃ eq em r = em (from eq r)

live-endlast : ∀ {A} v {t u : EmissionSet A} → t ≃ u → Live v (EndLast t) → Live v (EndLast u)
live-endlast true  eq el = endlast-≃ eq el
live-endlast false eq el = tt

-- The same rows, the same liveness, a good node and lane for a good one:
-- the same good tree.
record Swap {Γ A} (ρ : DenEnv Γ) (s s′ : St Γ A) : Set₁ where
  field
    same : rows ρ s ≃ rows ρ s′
    live≡ : alive s ≡ alive s′
    node : ∀ v → G ρ v s → G ρ v s′
    lane : ∀ v → GLn ρ v s → GLn ρ v s′
    body : ∀ v b → LnBody ρ v b s → LnBody ρ v b s′
    held : Held s → Held s′
open Swap

live-swap : ∀ {Γ A} (xs : List (St Γ A)) {s s′ ys} → alive s ≡ alive s′ → live (xs ʳ++ s ∷ ys) ≡ live (xs ʳ++ s′ ∷ ys)
live-swap xs {s} {s′} {ys} eq rewrite live-ʳ++ xs {s ∷ ys} | live-ʳ++ xs {s′ ∷ ys} | eq = refl

goodL-swap : ∀ {Γ A} {ρ : DenEnv Γ} {v} (xs : List (St Γ A)) {s s′ ys} → (GLn ρ v s → GLn ρ v s′) → GL ρ v (xs ʳ++ s ∷ ys) → GL ρ v (xs ʳ++ s′ ∷ ys)
goodL-swap xs h g with goodL-ʳ++⁻ xs g
... | gx , (gs , gy) = goodL-ʳ++ xs gx (h gs , gy)

lanes-≃ : ∀ {Γ A} {ρ : DenEnv Γ} (xs : List (St Γ A)) {ys ys′} → rowsL ρ ys ≈ᴸ rowsL ρ ys′ → rowsL ρ (xs ʳ++ ys) ≈ᴸ rowsL ρ (xs ʳ++ ys′)
lanes-≃ []       h = h
lanes-≃ (x ∷ xs) h = lanes-≃ xs (≃-refl ∷ h)

roots-≈ : ∀ {A B} {H : Pos → Set} {X : EmissionSet A} qs {Ls Ls′ : List (EmissionSet B)} → Ls ≈ᴸ Ls′ → Roots H X qs Ls → Roots H X qs Ls′
roots-≈ []       []       _                         = tt
roots-≈ (q ∷ qs) (e ∷ es) ((a , x , w) , nq , rs) = (a , x , λ l → w (from e l)) , nq , roots-≈ qs es rs
roots-≈ []       (_ ∷ _)  ()
roots-≈ (_ ∷ _)  []       ()

rooted-≃ : ∀ {Γ A B} {ρ : DenEnv Γ} {O O′ : EmissionSet A} {Ls Ls′ : List (EmissionSet B)} → O ≃ O′ → Ls ≈ᴸ Ls′ → Rooted ρ O Ls → Rooted ρ O′ Ls′
rooted-≃ eo es r = record { o₀ = o₀ ; p₀ = p₀ ; inv = inv ; sub = λ x → sub (from eo x) ; qs = qs ; roots = roots-≈ qs es roots }
  where open Rooted r

-- A source swapped: the same source to its connect.
src-swap : ∀ {Γ A} {ρ : DenEnv Γ} {s s′ : St Γ A} → Swap ρ s s′ → ∀ v m → SrcG ρ v m s → SrcG ρ v m s′
src-swap sw v nothing  g = node sw v g
src-swap sw v (just _) g = held sw g

postulate
  -- A BINDER'S GOOD BODY, UP TO THE SAME ROWS: a body reads its binder
  -- only through the rows it holds, as `rows-hot` has it of its rows.
  good-hot : ∀ {Γ X B} {t u : EmissionSet X} (k : CS) (ρ : DenEnv Γ) (b : St (X ∷ Γ) B) → t ≃ u → ∀ v → G (Hot t k ∷ᴬ ρ) v b → G (Hot u k ∷ᴬ ρ) v b
  -- A BINDER'S BODY OWES, UP TO THE SAME ROWS: as `good-hot`, of what
  -- the body owes.
  owes-hot : ∀ {Γ X B} {t u : EmissionSet X} (k : CS) (ρ : DenEnv Γ) (b : St (X ∷ Γ) B) → t ≃ u → Owes (Hot t k ∷ᴬ ρ) b → Owes (Hot u k ∷ᴬ ρ) b

-- What each connect a focus sits in the source of owes in its body,
-- read against the hole's rows `H` as `up` reads them.
SrcO : ∀ {R Γ A} → Ctx R Γ A → EmissionSet A → Set
SrcO top                                             H = ⊤
SrcO (inMap f c)                                     H = SrcO c (MapT f H)
SrcO (inScan f z c)                                  H = SrcO c (Scan.ScanT f z H)
SrcO (inCut true a c)                                H = SrcO c H
SrcO (inLn true c)                                   H = SrcO c H
SrcO (inOuter (mergeᶠ nothing) f d n q ls c)         H = SrcO c (Flat.RowT (λ a → pendRows (env c) (f a)) H d (rowsL (env c) ls))
SrcO (inLanes (mergeᶠ nothing) f d n q o pre post c) H =
  SrcO c (Flat.RowT (λ a → pendRows (env c) (f a)) (rows (env c) o) d (rowsL (env c) pre ʳ++ (H ∷ rowsL (env c) post)))
SrcO (inSrc k b c)                                   H = Owes (Hot H k ∷ᴬ env c) b × SrcO c (Connecting.ConnT (CS.connAt k) H (rows (Hot H k ∷ᴬ env c) b))
SrcO (inBody k o c)                                  H = SrcO c (Connecting.ConnT (CS.connAt k) (rows (env c) o) H)
SrcO _                                               H = ⊤

srcO-≃ : ∀ {R Γ A} (c : Ctx R Γ A) {t u : EmissionSet A} → t ≃ u → SrcO c t → SrcO c u
srcO-≃ top                                              eq so = tt
srcO-≃ (inMap f c)                                      eq so = srcO-≃ c (map-≃ f eq) so
srcO-≃ (inScan f z c)                                   eq so = srcO-≃ c (scan-≃ f z eq) so
srcO-≃ (inCut true a c)                                 eq so = srcO-≃ c eq so
srcO-≃ (inCut false a c)                                eq so = tt
srcO-≃ (inLn true c)                                    eq so = srcO-≃ c eq so
srcO-≃ (inLn false c)                                   eq so = tt
srcO-≃ (inTake i p w c)                                 eq so = tt
srcO-≃ (inOuter (mergeᶠ nothing) f d n q ls c)          eq so = srcO-≃ c (row-≃ (λ a → pendRows (env c) (f a)) eq (≈ᴸ-refl (rowsL (env c) ls))) so
srcO-≃ (inOuter (mergeᶠ (just _)) f d n q ls c)         eq so = tt
srcO-≃ (inOuter switchᶠ f d n q ls c)                   eq so = tt
srcO-≃ (inOuter exhaustᶠ f d n q ls c)                  eq so = tt
srcO-≃ (inLanes (mergeᶠ nothing) f d n q o pre post c)  eq so =
  srcO-≃ c (row-≃ (λ a → pendRows (env c) (f a)) ≃-refl (ʳ++-≈ (rowsL (env c) pre) (eq ∷ ≈ᴸ-refl (rowsL (env c) post)))) so
srcO-≃ (inLanes (mergeᶠ (just _)) f d n q o pre post c) eq so = tt
srcO-≃ (inLanes switchᶠ f d n q o pre post c)           eq so = tt
srcO-≃ (inLanes exhaustᶠ f d n q o pre post c)          eq so = tt
srcO-≃ (inSrc k b c)                                    eq (ob , so) = owes-hot k (env c) b eq ob , srcO-≃ c (conn-≃ _ eq (rows-hot k (env c) b eq)) so
srcO-≃ (inBody k o c)                                   eq so = srcO-≃ c (conn-≃ _ ≃-refl eq) so

-- A completed source owing nothing, up to the same rows.
spent-≃ : ∀ {A} {t u : EmissionSet A} {P : Set} v → t ≃ u → Live v (P → Empty t) → Live v (P → Empty u)
spent-≃ true  eq sp h = empty-≃ eq (sp h)
spent-≃ false eq sp   = tt

-- A node owing nothing and never good.
void : ∀ {Γ A} {ρ : DenEnv Γ} {s s′ : St Γ A} → rows ρ s ≡ ∅ → rows ρ s′ ≡ ∅ → alive s ≡ alive s′ → (∀ v → G ρ v s → ⊥) → (∀ v → GLn ρ v s → ⊥) → (∀ v b → LnBody ρ v b s → ⊥) → (Held s → ⊥) → Swap ρ s s′
void e e′ al ng nl nb nh = record { same = ≡→≃ (trans e (sym e′)) ; live≡ = al ; node = λ v g → ⊥-elim (ng v g) ; lane = λ v g → ⊥-elim (nl v g) ; body = λ v b g → ⊥-elim (nb v b g) ; held = λ h → ⊥-elim (nh h) }

good-swap : ∀ {R Γ A} (c : Ctx R Γ A) {s s′ : St Γ A} → Swap (env c) s s′ → ∀ {v} → G [] v (plug c s) → G [] v (plug c s′)
good-swap top              sw {v} g = node sw v g
good-swap (inMap f c)      sw g = good-swap c (record { same = map-≃ f (same sw) ; live≡ = refl ; node = node sw ; lane = λ _ () ; body = λ _ _ () ; held = λ () }) g
good-swap (inScan f z c)   sw g = good-swap c (record { same = scan-≃ f z (same sw) ; live≡ = refl ; node = node sw ; lane = λ _ () ; body = λ _ _ () ; held = λ () }) g
good-swap (inCut true a c) sw g = good-swap c (record { same = same sw ; live≡ = refl ; node = λ v → node sw (v ∧ true) ; lane = λ _ () ; body = λ { v b (eq , gs , el) → eq , node sw (v ∧ b) gs , live-endlast (v ∧ b) (same sw) el } ; held = λ () }) g
good-swap (inCut false a c) sw g = good-swap c (record { same = ≃-refl ; live≡ = refl ; node = λ v → node sw (v ∧ false) ; lane = λ _ () ; body = λ { v b (eq , gs , el) → eq , node sw (v ∧ b) gs , live-endlast (v ∧ b) (same sw) el } ; held = λ () }) g
good-swap (inLn true c)    sw g = good-swap c (record { same = same sw ; live≡ = refl ; node = λ _ () ; lane = λ v → body sw v true ; body = λ _ _ () ; held = λ () }) g
good-swap (inLn false c)   sw g = good-swap c (record { same = ≃-refl ; live≡ = refl ; node = λ _ () ; lane = λ v → body sw v false ; body = λ _ _ () ; held = λ () }) g
good-swap (inTake i q w c) sw g = good-swap c (void refl refl refl (λ _ ()) (λ _ ()) (λ _ _ ()) (λ ())) g
good-swap (inOuter (mergeᶠ nothing) f d n q ls c) {s} {s′} sw g =
  good-swap c {s = flatS (mergeᶠ nothing) f d n q s ls} {s′ = flatS (mergeᶠ nothing) f d n q s′ ls} (record { same = row-≃ _ (same sw) (≈ᴸ-refl (rowsL (env c) ls)) ; live≡ = refl ; lane = λ _ () ; body = λ _ _ () ; held = λ ()
                      ; node = λ { true m → mergeG-map (node sw true) (λ x → x) (λ x → x) (λ ov t {q} {e} → empty-≃ (same sw) (ov t) {q} {e}) (rooted-≃ (same sw) (≈ᴸ-refl (rowsL (env c) ls))) m
                                 ; false m → mergeG-map (node sw false) (λ x → x) (λ x → x) (λ x → x) (λ x → x) m } }) g
good-swap (inOuter (mergeᶠ (just _)) f d n q ls c) sw g = good-swap c (void refl refl refl (λ _ ()) (λ _ ()) (λ _ _ ()) (λ ())) g
good-swap (inOuter switchᶠ f d n q ls c)  sw g = good-swap c (void refl refl refl (λ _ ()) (λ _ ()) (λ _ _ ()) (λ ())) g
good-swap (inOuter exhaustᶠ f d n q ls c) sw g = good-swap c (void refl refl refl (λ _ ()) (λ _ ()) (λ _ _ ()) (λ ())) g
good-swap (inLanes (mergeᶠ nothing) f d n q o pre post c) {s} {s′} sw g =
  good-swap c {s = flatS (mergeᶠ nothing) f d n q o (pre ʳ++ s ∷ post)} {s′ = flatS (mergeᶠ nothing) f d n q o (pre ʳ++ s′ ∷ post)} (record { same = row-≃ _ ≃-refl (lanes-≃ pre (same sw ∷ ≈ᴸ-refl (rowsL (env c) post))) ; live≡ = refl ; lane = λ _ () ; body = λ _ _ () ; held = λ ()
                      ; node = λ { true m → mergeG-map (λ x → x) (goodL-swap pre (lane sw true)) (λ nl → trans nl (live-swap pre (live≡ sw))) (λ x → x) (rooted-≃ ≃-refl (lanes-≃ pre (same sw ∷ ≈ᴸ-refl (rowsL (env c) post)))) m
                                 ; false m → mergeG-map (λ x → x) (goodL-swap pre (lane sw false)) (λ x → x) (λ x → x) (λ x → x) m } }) g
good-swap (inLanes (mergeᶠ (just _)) f d n q o pre post c) sw g = good-swap c (void refl refl refl (λ _ ()) (λ _ ()) (λ _ _ ()) (λ ())) g
good-swap (inLanes switchᶠ f d n q o pre post c)  sw g = good-swap c (void refl refl refl (λ _ ()) (λ _ ()) (λ _ _ ()) (λ ())) g
good-swap (inLanes exhaustᶠ f d n q o pre post c) sw g = good-swap c (void refl refl refl (λ _ ()) (λ _ ()) (λ _ _ ()) (λ ())) g
good-swap (inSrc k b c) {s} {s′} sw g =
  good-swap c {s = connS k s b} {s′ = connS k s′ b} (record { same = conn-≃ _ (same sw) (rows-hot k (env c) b (same sw)) ; live≡ = refl ; lane = λ _ () ; body = λ _ _ () ; held = λ ()
                      ; node = λ { v (gs , gb , sp) → src-swap sw v (CS.bodyAt k) gs , good-hot k (env c) b (same sw) v gb , spent-≃ v (same sw) sp } }) g
good-swap (inBody k o c) {s} {s′} sw g =
  good-swap c {s = connS k o s} {s′ = connS k o s′} (record { same = conn-≃ _ ≃-refl (same sw) ; live≡ = refl ; lane = λ _ () ; body = λ _ _ () ; held = λ ()
                      ; node = λ { v (gs , gb , sp) → gs , node sw v gb , sp } }) g
