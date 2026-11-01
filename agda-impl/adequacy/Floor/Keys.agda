{-# OPTIONS --guardedness #-}

-- A TREE'S KEYS, MOVED: where a step's new keys come from, a node's own
-- or a context's, and the bounds they keep.
module adequacy.Floor.Keys where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_; _ʳ++_; reverse)
open import Data.List.Properties using (ʳ++-defn; ++-identityʳ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; subst)
open import Relation.Nullary using (yes; no)

open import denotation.Events using (Pos; ix; last; _≟ˡ_; <ᵖ-below; <ᵖ-part; <ᵖ-ix; <ᵖ-irrefl; <ᵖ-asym; <ᵖ-split; <ᵖ-next; From∞; Frame; Frame∞; emit; stall; close; timelineAt)
  renaming (sub to subᴾ)
open import denotation.Events using (_<ᵖ_)
open import operation.PureObservable using (PureObs; module Machine; module Driver; Tape; play; ending; rest; due; opening) renaming (over to overT)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)

open Machine using (Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody; St; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS;
                    CS; cs; Mode; Conf; ⟨_,_,_,_⟩; plug; load; subscribing; absorbed; rising; nx; cp; closed; closedUp; alive; unsub; cut; killAll; ended; settle; shutAt;
                    attAt; attached; free; cpAt; cutAt; overAt; search; found; own; run; unsubIf; feed; feedL; queued; inbox; Mark; ofM; attM; cpM; cutM; bodyM; srcAttM; owedM; joinM; leafM; Ev)
open import operation.Key using (Key; at; after; _<ᴷ_; at-<ᴷ; <ᴷ-trans; ≮ᴷ-trans; <ᴷ-irrefl; clash)
open import adequacy.Least using (KeyIn; k-own; k-kid; k-map; k-scan; k-cut; k-ln; k-take; k-outer; k-lane; k-src; k-body; Lo)
open import adequacy.Path using (_⊑_; ⊑i)

------------------------------------------------------------------------
-- Keys

-- Strictly earlier one way, not the other.
asym : ∀ a b → a <ᴷ b ≡ true → b <ᴷ a ≡ false
asym a b h with b <ᴷ a in e
... | true  = ⊥-elim (clash (<ᴷ-trans a b a h e) (<ᴷ-irrefl a))
... | false = refl

-- No key past the last.
top-max : ∀ κ → after [] <ᴷ κ ≡ false
top-max (at [])        = refl
top-max (at (_ ∷ _))   = refl
top-max (after [])     = refl
top-max (after (_ ∷ _)) = refl

-- A position and all below it, before the position's after.
at-after : ∀ p ys → at (p ++ ys) <ᴷ after p ≡ true
at-after []      []      = refl
at-after []      (_ ∷ _) = refl
at-after (a ∷ p) ys with a ≟ˡ a
... | yes _ rewrite <ᵖ-irrefl [ a ] = at-after p ys
... | no ¬e = ⊥-elim (¬e refl)

at-after₀ : ∀ p → at p <ᴷ after p ≡ true
at-after₀ []      = refl
at-after₀ (a ∷ p) with a ≟ˡ a
... | yes _ rewrite <ᵖ-irrefl [ a ] = at-after₀ p
... | no ¬e = ⊥-elim (¬e refl)

-- A position below another, not before it.
ext-le : ∀ p ys → at (p ++ ys) <ᴷ at p ≡ false
ext-le p []       rewrite ++-identityʳ p = <ᴷ-irrefl (at p)
ext-le p (l ∷ ys) = trans (at-<ᴷ (p ++ l ∷ ys) p) (<ᵖ-asym p (p ++ l ∷ ys) (<ᵖ-below p ys))

ext-⊑ : ∀ p ys → at p ⊑ at (p ++ ys)
ext-⊑ p ys = ⊑i (ext-le p ys)

⊑-refl : ∀ {κ} → κ ⊑ κ
⊑-refl {κ} = ⊑i (<ᴷ-irrefl κ)

-- A child below its position.
below : ∀ q {l} → at q <ᴷ at (q ++ [ l ]) ≡ true
below q = trans (at-<ᴷ q _) (<ᵖ-below q [])

------------------------------------------------------------------------
-- Keys held, moved

-- What a tree's keys are bounded below by, kept.
lo-weaken : ∀ {Γ A} {t : St Γ A} X Y → Lo t Y → X <ᴷ Y ≡ true → Lo t X
lo-weaken X Y lo h {κ} ki = ≮ᴷ-trans κ Y X (lo ki) (asym X Y h)

-- A node's new keys: old ones, or none before `X`.
Into : ∀ {Γ A} → Key → St Γ A → St Γ A → Set₁
Into X t t′ = ∀ {κ} → KeyIn t′ κ → KeyIn t κ ⊎ κ <ᴷ X ≡ false

-- A lane among its siblings.
mem-self : ∀ {a} {S : Set a} (pre : List S) {s post} → s ∈ pre ʳ++ s ∷ post
mem-self pre {s} {post} rewrite ʳ++-defn pre {s ∷ post} = ∈-++⁺ʳ (reverse pre) (here refl)

mem-swap : ∀ {a} {S : Set a} (pre : List S) {s s′ x post} → x ∈ pre ʳ++ s′ ∷ post → x ≡ s′ ⊎ x ∈ pre ʳ++ s ∷ post
mem-swap pre {s} {s′} {post = post} m rewrite ʳ++-defn pre {s′ ∷ post} | ʳ++-defn pre {s ∷ post} with ∈-++⁻ (reverse pre) m
... | inj₁ m′         = inj₂ (∈-++⁺ˡ m′)
... | inj₂ (here e)   = inj₁ e
... | inj₂ (there m′) = inj₂ (∈-++⁺ʳ (reverse pre) (there m′))

-- A kill switch's or a takeWhile's own marks read only its flag.
own-cut : ∀ {Γ A} {l l′} a {s s′ : St Γ A} → own (cutS l a s) ≡ own (cutS l′ a s′)
own-cut attached  = refl
own-cut (attAt p) = refl

own-take : ∀ {Γ A} {i q} w {s s′ : St Γ A} → own (takeS i q w s) ≡ own (takeS i q w s′)
own-take free       = refl
own-take (cpAt p)   = refl
own-take (cutAt p)  = refl
own-take (overAt p) = refl

-- A connect's own marks, by kind.
data OwnOf {Γ X} (k : CS Γ X) : Mark → Key → Set where
  ob : ∀ {p} → CS.bodyAt k ≡ just p → OwnOf k bodyM (at (p ++ [ ix 1 ]))
  os : ∀ {p} → CS.attSrc k ≡ just p → OwnOf k srcAttM (after p)
  oo : ∀ {p} → CS.owedAt k ≡ just p → OwnOf k owedM (after p)

own-cls : ∀ {Γ X B} (k : CS Γ X) {o : St Γ X} {b : St (X ∷ Γ) B} {m κ} → (m , κ) ∈ own (connS k o b) → OwnOf k m κ
own-cls (cs _ _ _ (just p) _ _ _ _ _ _) (here refl) = ob refl
own-cls (cs _ _ _ nothing  (just p) _ _ _ _ _) (here refl) = os refl
own-cls (cs _ _ _ nothing  nothing  (just p) _ _ _ _) (here refl) = oo refl
own-cls (cs _ _ _ nothing  nothing  nothing  _ _ _ _) ()
own-cls (cs _ _ _ nothing  nothing  (just p) _ _ _ _) (there ())
own-cls (cs _ _ _ nothing  (just _) nothing  _ _ _ _) (there ())
own-cls (cs _ _ _ nothing  (just _) (just p) _ _ _ _) (there (here refl)) = oo refl
own-cls (cs _ _ _ nothing  (just _) (just p) _ _ _ _) (there (there ()))
own-cls (cs _ _ _ (just _) nothing  nothing  _ _ _ _) (there ())
own-cls (cs _ _ _ (just _) nothing  (just p) _ _ _ _) (there (here refl)) = oo refl
own-cls (cs _ _ _ (just _) nothing  (just p) _ _ _ _) (there (there ()))
own-cls (cs _ _ _ (just _) (just p) nothing  _ _ _ _) (there (here refl)) = os refl
own-cls (cs _ _ _ (just _) (just p) nothing  _ _ _ _) (there (there ()))
own-cls (cs _ _ _ (just _) (just p) (just _) _ _ _ _) (there (here refl)) = os refl
own-cls (cs _ _ _ (just _) (just _) (just p) _ _ _ _) (there (there (here refl))) = oo refl
own-cls (cs _ _ _ (just _) (just _) (just _) _ _ _ _) (there (there (there ())))

own-bld : ∀ {Γ X B} (k : CS Γ X) {o : St Γ X} {b : St (X ∷ Γ) B} {m κ} → OwnOf k m κ → (m , κ) ∈ own (connS k o b)
own-bld (cs _ _ _ (just p) _ _ _ _ _ _) (ob refl) = here refl
own-bld (cs _ _ _ nothing  (just p) _ _ _ _ _) (os refl) = here refl
own-bld (cs _ _ _ (just _) (just p) _ _ _ _ _) (os refl) = there (here refl)
own-bld (cs _ _ _ nothing  nothing  (just p) _ _ _ _) (oo refl) = here refl
own-bld (cs _ _ _ nothing  (just _) (just p) _ _ _ _) (oo refl) = there (here refl)
own-bld (cs _ _ _ (just _) nothing  (just p) _ _ _ _) (oo refl) = there (here refl)
own-bld (cs _ _ _ (just _) (just _) (just p) _ _ _ _) (oo refl) = there (there (here refl))

-- A connect's own marks, kept or dropped field by field.
Fewer : ∀ {Γ X} → CS Γ X → CS Γ X → Set
Fewer k′ k = (∀ {p} → CS.bodyAt k′ ≡ just p → CS.bodyAt k ≡ just p)
           × (∀ {p} → CS.attSrc k′ ≡ just p → CS.attSrc k ≡ just p)
           × (∀ {p} → CS.owedAt k′ ≡ just p → CS.owedAt k ≡ just p)

fewer-same : ∀ {Γ X} {k : CS Γ X} → Fewer k k
fewer-same = (λ e → e) , (λ e → e) , (λ e → e)

fewer-cls : ∀ {Γ X} {k k′ : CS Γ X} {m κ} → Fewer k′ k → OwnOf k′ m κ → OwnOf k m κ
fewer-cls (hb , _ , _) (ob e) = ob (hb e)
fewer-cls (_ , hs , _) (os e) = os (hs e)
fewer-cls (_ , _ , ho) (oo e) = oo (ho e)

own-fewer : ∀ {Γ X B} (k k′ : CS Γ X) {o o′ : St Γ X} {b b′ : St (X ∷ Γ) B} {m κ} → Fewer k′ k
          → (m , κ) ∈ own (connS k′ o′ b′) → (m , κ) ∈ own (connS k o b)
own-fewer k k′ {o} {o′} {b} {b′} h mi = own-bld k {o} {b} (fewer-cls h (own-cls k′ {o′} {b′} mi))

own-same : ∀ {Γ X B} (k : CS Γ X) {o o′ : St Γ X} {b b′ : St (X ∷ Γ) B} {m κ}
         → (m , κ) ∈ own (connS k o′ b′) → (m , κ) ∈ own (connS k o b)
own-same k {o} {o′} {b} {b′} = own-fewer k k {o} {o′} {b} {b′} (fewer-same {k = k})

shut-fewer : ∀ {Γ X} p (k : CS Γ X) → Fewer (shutAt p k) k
shut-fewer p k with CS.srcLive k
... | true  = (λ e → e) , (λ e → e) , (λ e → e)
... | false = (λ e → e) , (λ e → e) , (λ e → e)

-- A tree's keys, its hole's or its context's.
plug-in : ∀ {R Γ A} (c : Ctx R Γ A) {s κ} → KeyIn s κ → KeyIn (plug c s) κ
plug-in top                               h = h
plug-in (inMap f c)                       h = plug-in c (k-kid (k-map h))
plug-in (inScan f z c)                    h = plug-in c (k-kid (k-scan h))
plug-in (inCut l a c)                     h = plug-in c (k-kid (k-cut h))
plug-in (inLn b c)                        h = plug-in c (k-kid (k-ln h))
plug-in (inTake i q w c)                  h = plug-in c (k-kid (k-take h))
plug-in (inOuter op f d n q ls c)         h = plug-in c (k-kid (k-outer h))
plug-in (inLanes op f d n q o pre post c) h = plug-in c (k-kid (k-lane (mem-self pre) h))
plug-in (inSrc k b c)                     h = plug-in c (k-kid (k-src h))
plug-in (inBody k o c)                    h = plug-in c (k-kid (k-body h))

plug-swap : ∀ {R Γ A} (c : Ctx R Γ A) {s s′ κ} → KeyIn (plug c s′) κ → KeyIn s′ κ ⊎ KeyIn (plug c s) κ
plug-swap top h = inj₁ h
plug-swap (inMap f c) {s} h with plug-swap c {s = mapS f s} h
... | inj₁ (k-kid (k-map h′)) = inj₁ h′
... | inj₂ h′                 = inj₂ h′
plug-swap (inScan f z c) {s} h with plug-swap c {s = scanS f z s} h
... | inj₁ (k-kid (k-scan h′)) = inj₁ h′
... | inj₂ h′                  = inj₂ h′
plug-swap (inCut l a c) {s} {s′} h with plug-swap c {s = cutS l a s} h
... | inj₁ (k-own m)           = inj₂ (plug-in c (k-own (subst (_ ∈_) (own-cut a {s′} {s}) m)))
... | inj₁ (k-kid (k-cut h′))  = inj₁ h′
... | inj₂ h′                  = inj₂ h′
plug-swap (inLn b c) {s} h with plug-swap c {s = lnS b s} h
... | inj₁ (k-kid (k-ln h′)) = inj₁ h′
... | inj₂ h′                = inj₂ h′
plug-swap (inTake i q w c) {s} {s′} h with plug-swap c {s = takeS i q w s} h
... | inj₁ (k-own m)           = inj₂ (plug-in c (k-own (subst (_ ∈_) (own-take w {s′} {s}) m)))
... | inj₁ (k-kid (k-take h′)) = inj₁ h′
... | inj₂ h′                  = inj₂ h′
plug-swap (inOuter op f d n q ls c) {s} h with plug-swap c {s = flatS op f d n q s ls} h
... | inj₁ (k-kid (k-outer h′))  = inj₁ h′
... | inj₁ (k-kid (k-lane m h′)) = inj₂ (plug-in c (k-kid (k-lane m h′)))
... | inj₂ h′                    = inj₂ h′
plug-swap (inLanes op f d n q o pre post c) {s} h with plug-swap c {s = flatS op f d n q o (pre ʳ++ s ∷ post)} h
... | inj₁ (k-kid (k-outer h′))  = inj₂ (plug-in c (k-kid (k-outer h′)))
... | inj₁ (k-kid (k-lane m h′)) with mem-swap pre {s = s} m
...   | inj₁ refl = inj₁ h′
...   | inj₂ m′   = inj₂ (plug-in c (k-kid (k-lane m′ h′)))
plug-swap (inLanes op f d n q o pre post c) {s} h | inj₂ h′ = inj₂ h′
plug-swap (inSrc k b c) {s} {s′} h with plug-swap c {s = connS k s b} h
... | inj₁ (k-own m)          = inj₂ (plug-in c (k-own (own-same k {s} {s′} {b} {b} m)))
... | inj₁ (k-kid (k-src h′))  = inj₁ h′
... | inj₁ (k-kid (k-body h′)) = inj₂ (plug-in c (k-kid (k-body h′)))
... | inj₂ h′                  = inj₂ h′
plug-swap (inBody k o c) {s} {s′} h with plug-swap c {s = connS k o s} h
... | inj₁ (k-own m)          = inj₂ (plug-in c (k-own (own-same k {o} {o} {s} {s′} m)))
... | inj₁ (k-kid (k-src h′))  = inj₂ (plug-in c (k-kid (k-src h′)))
... | inj₁ (k-kid (k-body h′)) = inj₁ h′
... | inj₂ h′                  = inj₂ h′

-- A hole's new keys, none before `X`: the tree's, none before `X`.
sub-at : ∀ {R Γ A} (c : Ctx R Γ A) {t t′ : St Γ A} {X} → Into X t t′ → Lo (plug c t) X → Lo (plug c t′) X
sub-at c {t} h lo ki with plug-swap c {s = t} ki
... | inj₂ hc = lo hc
... | inj₁ ht with h ht
...   | inj₁ h′ = lo (plug-in c h′)
...   | inj₂ ge = ge

-- No new keys.

------------------------------------------------------------------------
-- Teardown and feed keep keys

cold-key : ∀ {Γ A} {b} {l : Tape A} {κ} → KeyIn {Γ} (coldS b l) κ → due l ≡ just κ
cold-key {l = l} (k-own m) with due l | m
... | just _  | here refl = refl
... | just _  | there ()
... | nothing | ()
cold-key (k-kid ())

cold-in : ∀ {Γ A} {b} {l : Tape A} {κ} → due l ≡ just κ → KeyIn {Γ} (coldS b l) κ
cold-in {l = play τ u i t fr} refl = k-own (here refl)
cold-in {l = ending e}        refl = k-own (here refl)
cold-in {l = overT}           ()

mutual
  unsub-in : ∀ {Γ A} (s : St Γ A) {κ} → KeyIn (proj₁ (unsub s)) κ → KeyIn s κ
  unsub-in (pend o q)              h = h
  unsub-in (coldS true l)          h = cold-in (cold-key h)
  unsub-in (coldS false l)         h = h
  unsub-in (ofS i q xs)            h = h
  unsub-in doneS                   h = h
  unsub-in (mapS f s)              (k-kid (k-map h)) = k-kid (k-map (unsub-in s h))
  unsub-in (scanS f z s)           (k-kid (k-scan h)) = k-kid (k-scan (unsub-in s h))
  unsub-in (cutS l a s)            h = h
  unsub-in (lnS b s)               h = h
  unsub-in (takeS i q w s)         (k-own m) = k-own (subst (_ ∈_) (own-take w) m)
  unsub-in (takeS i q w s)         (k-kid (k-take h)) = k-kid (k-take (cut-in s h))
  unsub-in (flatS op f d n q o ls) (k-kid (k-outer h)) = k-kid (k-outer (cut-in o h))
  unsub-in (flatS op f d n q o ls) (k-kid (k-lane m h)) with kill-in ls m h
  ... | _ , m′ , h′ = k-kid (k-lane m′ h′)
  unsub-in (connS k o b)           (k-own m) = k-own (own-same k {o} {proj₁ (unsub o)} {b} {proj₁ (unsub b)} m)
  unsub-in (connS k o b)           (k-kid (k-src h)) = k-kid (k-src (unsub-in o h))
  unsub-in (connS k o b)           (k-kid (k-body h)) = k-kid (k-body (unsub-in b h))
  unsub-in (joinS j g x ib)        (k-own ())
  unsub-in (joinS j g x ib)        (k-kid ())

  cut-in : ∀ {Γ A} (s : St Γ A) {κ} → KeyIn (proj₁ (cut s)) κ → KeyIn s κ
  cut-in (cutS l attached s)  (k-own ())
  cut-in (cutS l attached s)  (k-kid (k-cut h)) = k-kid (k-cut (unsub-in s h))
  cut-in (cutS l (attAt p) s) (k-own m) = k-own m
  cut-in (cutS l (attAt p) s) (k-kid (k-cut h)) = k-kid (k-cut h)
  cut-in (pend o q)              h = h
  cut-in (coldS b l)             h = h
  cut-in (ofS i q xs)            h = h
  cut-in doneS                   h = h
  cut-in (mapS f s)              h = h
  cut-in (scanS f z s)           h = h
  cut-in (lnS b s)               h = h
  cut-in (takeS i q w s)         h = h
  cut-in (flatS op f d n q o ls) h = h
  cut-in (connS k o b)           h = h
  cut-in (joinS j g x ib)        h = h

  kill-in : ∀ {Γ B} (ls : List (St Γ B)) {x κ} → x ∈ proj₁ (killAll ls) → KeyIn x κ → Σ _ λ y → y ∈ ls × KeyIn y κ
  kill-in []                (()) h
  kill-in (lnS true s ∷ ls) (here refl) (k-kid (k-ln h)) = _ , here refl , k-kid (k-ln (cut-in s h))
  kill-in (lnS true s ∷ ls) (there m) h = kept-tail (lnS true s) ls m h
  kill-in (lnS false s ∷ ls)          m h = keep-l (lnS false s) ls m h
  kill-in (pend o q ∷ ls)             m h = keep-l (pend o q) ls m h
  kill-in (coldS b l ∷ ls)            m h = keep-l (coldS b l) ls m h
  kill-in (ofS i q xs ∷ ls)           m h = keep-l (ofS i q xs) ls m h
  kill-in (doneS ∷ ls)                m h = keep-l doneS ls m h
  kill-in (mapS f s ∷ ls)             m h = keep-l (mapS f s) ls m h
  kill-in (scanS f z s ∷ ls)          m h = keep-l (scanS f z s) ls m h
  kill-in (cutS l a s ∷ ls)           m h = keep-l (cutS l a s) ls m h
  kill-in (takeS i q w s ∷ ls)        m h = keep-l (takeS i q w s) ls m h
  kill-in (flatS op f d n q o ms ∷ ls) m h = keep-l (flatS op f d n q o ms) ls m h
  kill-in (connS k o b ∷ ls)          m h = keep-l (connS k o b) ls m h
  kill-in (joinS j g x ib ∷ ls)       m h = keep-l (joinS j g x ib) ls m h

  kept-tail : ∀ {Γ B} (l : St Γ B) (ls : List (St Γ B)) {x κ} → x ∈ proj₁ (killAll ls) → KeyIn x κ → Σ _ λ y → y ∈ l ∷ ls × KeyIn y κ
  kept-tail l ls m h with kill-in ls m h
  ... | y , m′ , h′ = y , there m′ , h′

  keep-l : ∀ {Γ B} (l : St Γ B) (ls : List (St Γ B)) {x κ} → x ∈ l ∷ proj₁ (killAll ls) → KeyIn x κ → Σ _ λ y → y ∈ l ∷ ls × KeyIn y κ
  keep-l l ls (here refl) h = l , here refl , h
  keep-l l ls (there m)   h = kept-tail l ls m h

unsubIf-in : ∀ {Γ A} b (s : St Γ A) {κ} → KeyIn (proj₁ (unsubIf b s)) κ → KeyIn s κ
unsubIf-in true  s h = unsub-in s h
unsubIf-in false s h = h

ended-in : ∀ {Γ B} (s : St Γ B) {κ} → KeyIn (ended s) κ → KeyIn s κ
ended-in (lnS b (cutS l a s)) (k-kid (k-ln (k-own m))) = k-kid (k-ln (k-own (subst (_ ∈_) (own-cut a) m)))
ended-in (lnS b (cutS l a s)) (k-kid (k-ln (k-kid (k-cut h)))) = k-kid (k-ln (k-kid (k-cut h)))
ended-in (lnS b (pend o q))           h = h
ended-in (lnS b (coldS b′ l))         h = h
ended-in (lnS b (ofS i q xs))         h = h
ended-in (lnS b doneS)                h = h
ended-in (lnS b (mapS f s))           h = h
ended-in (lnS b (scanS f z s))        h = h
ended-in (lnS b (lnS b′ s))           h = h
ended-in (lnS b (takeS i q w s))      h = h
ended-in (lnS b (flatS op f b′ n q o ls)) h = h
ended-in (lnS b (connS k o s))        h = h
ended-in (lnS b (joinS j g x ib))     h = h
ended-in (pend o q)                   h = h
ended-in (coldS b l)                  h = h
ended-in (ofS i q xs)                 h = h
ended-in doneS                        h = h
ended-in (mapS f s)                   h = h
ended-in (scanS f z s)                h = h
ended-in (cutS l a s)                 h = h
ended-in (takeS i q w s)              h = h
ended-in (flatS op f b n q o ls)      h = h
ended-in (connS k o s)                h = h
ended-in (joinS j g x ib)             h = h

-- A lane replaced by one holding fewer keys.
lanes-in : ∀ {Γ B} (pre post : List (St Γ B)) {s s′ x κ} → (∀ {κ} → KeyIn s′ κ → KeyIn s κ)
         → x ∈ pre ʳ++ s′ ∷ post → KeyIn x κ → Σ _ λ y → y ∈ pre ʳ++ s ∷ post × KeyIn y κ
lanes-in pre post {s} h m hx with mem-swap pre {s = s} m
... | inj₁ refl = s , mem-self pre , h hx
... | inj₂ m′   = _ , m′ , hx

-- A flatMap keeps no keys of its own.
flat-in : ∀ {Γ A B} {op f d n q d′ n′ q′} {o o′ : St Γ A} {ls ls′ : List (St Γ B)} {κ}
        → (∀ {κ} → KeyIn o′ κ → KeyIn o κ) → (∀ {x κ} → x ∈ ls′ → KeyIn x κ → Σ _ λ y → y ∈ ls × KeyIn y κ)
        → KeyIn (flatS op f d′ n′ q′ o′ ls′) κ → KeyIn (flatS op f d n q o ls) κ
flat-in ho hl (k-kid (k-outer h)) = k-kid (k-outer (ho h))
flat-in ho hl (k-kid (k-lane m h)) with hl m h
... | _ , m′ , h′ = k-kid (k-lane m′ h′)

same-l : ∀ {Γ B} {ls : List (St Γ B)} {x κ} → x ∈ ls → KeyIn x κ → Σ _ λ y → y ∈ ls × KeyIn y κ
same-l m h = _ , m , h

-- A joiner's inbox fed: its head kept, or one strictly past where the
-- feed falls, a level down.
-- The head of an inbox an entry joins: the old head, or the entry.
inbox-key : ∀ {Γ A} j {g} {x : A ∈ Γ} (v : Pos × Ev A) ib {κ} → KeyIn (joinS j g x (inbox v ib)) κ
          → KeyIn (joinS j g x ib) κ ⊎ κ ≡ at (proj₁ v)
inbox-key j v [] (k-own (here refl)) = inj₂ refl
inbox-key j v [] (k-own (there ()))
inbox-key j v [] (k-kid ())
inbox-key j (q , e) ((r , e′) ∷ ib) h with r <ᵖ q
inbox-key j (q , e) ((r , e′) ∷ ib) (k-own (here refl)) | true  = inj₁ (k-own (here refl))
inbox-key j (q , e) ((r , e′) ∷ ib) (k-own (there ()))  | true
inbox-key j (q , e) ((r , e′) ∷ ib) (k-kid ())          | true
inbox-key j (q , e) ((r , e′) ∷ ib) (k-own (here refl)) | false = inj₂ refl
inbox-key j (q , e) ((r , e′) ∷ ib) (k-own (there ()))  | false
inbox-key j (q , e) ((r , e′) ∷ ib) (k-kid ())          | false

queued-key : ∀ {Γ A} j p (e : Ev A) {g} {x : A ∈ Γ} ib {κ} → KeyIn (joinS j g x (queued j p e ib)) κ
           → KeyIn (joinS j g x ib) κ ⊎ at (p ++ [ ix 0 ]) <ᴷ κ ≡ true
queued-key j p (nx a) ib h with j <ᵖ p
... | false = inj₁ h
... | true with inbox-key j _ ib h
...   | inj₁ h′   = inj₁ h′
...   | inj₂ refl = inj₂ (trans (at-<ᴷ (p ++ [ ix 0 ]) _) (<ᵖ-part p [] [] refl))
queued-key j p cp ib h with j <ᵖ p in e | inbox-key j _ ib h
... | _     | inj₁ h′   = inj₁ h′
... | true  | inj₂ refl = inj₂ (trans (at-<ᴷ (p ++ [ ix 0 ]) _) (<ᵖ-part p [] [] refl))
... | false | inj₂ refl with <ᵖ-split p j e
...   | inj₁ lt   = inj₂ (trans (at-<ᴷ (p ++ [ ix 0 ]) _) (<ᵖ-next p j last lt))
...   | inj₂ refl = inj₂ (trans (at-<ᴷ (p ++ [ ix 0 ]) _) (<ᵖ-part p [] [] refl))

mutual
  feed-key : ∀ {Γ X A} (i : X ∈ Γ) p (e : Ev X) (s : St Γ A) {κ} → KeyIn (feed i p e s) κ → KeyIn s κ ⊎ at (p ++ [ ix 0 ]) <ᴷ κ ≡ true
  feed-key i p e (joinS j true x ib) h with Machine.same? i x
  ... | just refl = queued-key j p e ib h
  ... | nothing   = inj₁ h
  feed-key i p e (joinS j false x ib) h = inj₁ h
  feed-key i p e (mapS f s) (k-kid (k-map h)) with feed-key i p e s h
  ... | inj₁ h′ = inj₁ (k-kid (k-map h′))
  ... | inj₂ lt = inj₂ lt
  feed-key i p e (scanS f z s) (k-kid (k-scan h)) with feed-key i p e s h
  ... | inj₁ h′ = inj₁ (k-kid (k-scan h′))
  ... | inj₂ lt = inj₂ lt
  feed-key i p e (cutS l a s) (k-own m) = inj₁ (k-own (subst (_ ∈_) (own-cut a) m))
  feed-key i p e (cutS l a s) (k-kid (k-cut h)) with feed-key i p e s h
  ... | inj₁ h′ = inj₁ (k-kid (k-cut h′))
  ... | inj₂ lt = inj₂ lt
  feed-key i p e (lnS b s) (k-kid (k-ln h)) with feed-key i p e s h
  ... | inj₁ h′ = inj₁ (k-kid (k-ln h′))
  ... | inj₂ lt = inj₂ lt
  feed-key i p e (takeS v q w s) (k-own m) = inj₁ (k-own (subst (_ ∈_) (own-take w) m))
  feed-key i p e (takeS v q w s) (k-kid (k-take h)) with feed-key i p e s h
  ... | inj₁ h′ = inj₁ (k-kid (k-take h′))
  ... | inj₂ lt = inj₂ lt
  feed-key i p e (flatS op f d n q o ls) (k-kid (k-outer h)) with feed-key i p e o h
  ... | inj₁ h′ = inj₁ (k-kid (k-outer h′))
  ... | inj₂ lt = inj₂ lt
  feed-key i p e (flatS op f d n q o ls) (k-kid (k-lane m h)) with feedL-key i p e ls m h
  ... | inj₁ (_ , m′ , h′) = inj₁ (k-kid (k-lane m′ h′))
  ... | inj₂ lt            = inj₂ lt
  feed-key i p e (connS k o b) (k-own m) = inj₁ (k-own (own-same k {o} {feed i p e o} {b} {feed (there i) p e b} m))
  feed-key i p e (connS k o b) (k-kid (k-src h)) with feed-key i p e o h
  ... | inj₁ h′ = inj₁ (k-kid (k-src h′))
  ... | inj₂ lt = inj₂ lt
  feed-key i p e (connS k o b) (k-kid (k-body h)) with feed-key (there i) p e b h
  ... | inj₁ h′ = inj₁ (k-kid (k-body h′))
  ... | inj₂ lt = inj₂ lt
  feed-key i p e (pend o q)   h = inj₁ h
  feed-key i p e (coldS b l)  h = inj₁ h
  feed-key i p e (ofS j q xs) h = inj₁ h
  feed-key i p e doneS        h = inj₁ h

  feedL-key : ∀ {Γ X A} (i : X ∈ Γ) p (e : Ev X) (ls : List (St Γ A)) {x κ} → x ∈ feedL i p e ls → KeyIn x κ
            → (Σ _ λ y → y ∈ ls × KeyIn y κ) ⊎ at (p ++ [ ix 0 ]) <ᴷ κ ≡ true
  feedL-key i p e (s ∷ ls) (here refl) h with feed-key i p e s h
  ... | inj₁ h′ = inj₁ (s , here refl , h′)
  ... | inj₂ lt = inj₂ lt
  feedL-key i p e (s ∷ ls) (there m) h with feedL-key i p e ls m h
  ... | inj₁ (y , m′ , h′) = inj₁ (y , there m′ , h′)
  ... | inj₂ lt            = inj₂ lt

------------------------------------------------------------------------
-- The clock, read off the keys
