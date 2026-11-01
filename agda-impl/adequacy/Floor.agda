{-# OPTIONS --guardedness #-}

-- THE CLOCK NEVER RUNS BACK: a silent step's clock is no earlier than the
-- one it starts from.  Mid-run the clock is where the run is, and no mark
-- is keyed before that position's whole subtree is past; once everything
-- is absorbed it is the least mark due.  A step either moves the run to
-- where it was or below, or absorbs it, keeping every mark it had but
-- those it spends, and owing new ones only at or past its clock.
module adequacy.Floor where

open import Data.Bool using (true; false; not; if_then_else_; _∧_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_; _ʳ++_; reverse; null)
open import Data.List.Properties using (ʳ++-defn; ++-identityʳ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (suc; pred; _<ᵇ_; _≡ᵇ_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst; cong)
open import Relation.Nullary using (yes; no)

open import Tree using (mergeᶠ; switchᶠ; exhaustᶠ; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
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
open import adequacy.Dispatch using (Marked; ofK; attK; conK; joinK; leafK; stopK; cutK; found-mark; found-least; found-plug)
open import adequacy.Stamped using (frame-ahead; opening-ahead; pend-focus; inbox-asc)
open import adequacy.Weight using (Clock)
open import adequacy.Path using (_⊑_; ⊑i; ⊑-trans; Path; _⇜_)

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

-- Once absorbed, the clock is no earlier than a bound on every key.
clock-abs : ∀ {R Γ A} (c : Ctx R Γ A) s r {X} → Lo (plug c s) X → X ⊑ Clock ⟨ c , s , absorbed , r ⟩
clock-abs c s r {X} lo with search top (plug c s) in fd
... | nothing = ⊑i (top-max X)
... | just (found (_ , _ , c′ , s′) m κ) =
  ⊑i (lo (subst (λ t → KeyIn t κ) (found-plug c s fd) (plug-in c′ (k-own (proj₁ (found-least {t = plug c s} fd))))))

-- Where the run is, in any mode, its keys none before it.
here-ok : ∀ {R Γ A} (md : Mode A) (c : Ctx R Γ A) s r → Lo (plug c s) (at r) → at r ⊑ Clock ⟨ c , s , md , r ⟩
here-ok absorbed    c s r lo = clock-abs c s r lo
here-ok subscribing c s r lo = ⊑-refl
here-ok (rising e)  c s r lo = ⊑-refl

------------------------------------------------------------------------
-- The engine's leaves

-- Mid-run.
Busy : ∀ {A} → Mode A → Set
Busy absorbed    = ⊥
Busy subscribing = ⊤
Busy (rising _)  = ⊤

postulate
  -- THE FLOOR: mid-run at `p`, no mark is keyed before `p`'s whole
  -- subtree is past.  Every mark a run owes lies in a region of its own,
  -- apart from where the run now is.
  floor : ∀ {R} (o : PureObs [] R) {rs Γ A} {c : Ctx R Γ A} {s m p}
        → Path (load o) rs ⟨ c , s , m , p ⟩ → Busy m → Lo (plug c s) (after p)

------------------------------------------------------------------------
-- A step, by mode

-- Absorbed over new keys none before `X`, at any position.
absorb : ∀ {R Γ A} (c : Ctx R Γ A) (t t′ : St Γ A) r {X} → Into X t t′ → Lo (plug c t) X → X ⊑ Clock ⟨ c , t′ , absorbed , r ⟩
absorb c t t′ r {X} h lo = clock-abs c t′ r {X} (sub-at c {t} {t′} {X} h lo)

-- At `r`, in any mode, over new keys none before it.
md-at : ∀ {R Γ A} (md : Mode A) (c : Ctx R Γ A) (t t′ : St Γ A) r → Into (at r) t t′ → Lo (plug c t) (at r) → at r ⊑ Clock ⟨ c , t′ , md , r ⟩
md-at md c t t′ r h lo = here-ok md c t′ r (sub-at c {t} {t′} {at r} h lo)

-- An of's marks lie below where it was subscribed.
of-key : ∀ {Γ A} i p (xs : List A) {κ} → KeyIn {Γ} (ofS i p xs) κ → κ <ᴷ at p ≡ false
of-key i p []       (k-own (here refl)) = ext-le p [ last ]
of-key i p []       (k-own (there ()))
of-key i p (x ∷ xs) (k-own (here refl)) = ext-le p [ ix i ]
of-key i p (x ∷ xs) (k-own (there ()))
of-key i p xs       (k-kid ())

-- A source's feed: every new key past the row a level down.
fed-lo : ∀ {R Γ X B} (c : Ctx R Γ B) (k k′ : CS Γ X) (s : St Γ X) (b : St (X ∷ Γ) B) q (e : Ev X) → Fewer k′ k
       → Lo (plug c (connS k s b)) (after q) → Lo (plug c (connS k′ s (feed (here refl) q e b))) (at (q ++ [ ix 0 ]))
fed-lo c k k′ s b q e fw fl = sub-at c {connS k s b} {connS k′ s (feed (here refl) q e b)} {at (q ++ [ ix 0 ])} into (lo-weaken (at (q ++ [ ix 0 ])) (after q) fl (at-after q [ ix 0 ]))
  where
    into : Into (at (q ++ [ ix 0 ])) (connS k s b) (connS k′ s (feed (here refl) q e b))
    into (k-own m) = inj₁ (k-own (own-fewer k k′ {s} {s} {b} {feed (here refl) q e b} fw m))
    into (k-kid (k-src h)) = inj₁ (k-kid (k-src h))
    into {κ} (k-kid (k-body h)) with feed-key (here refl) q e b h
    ... | inj₁ h′ = inj₁ (k-kid (k-body h′))
    ... | inj₂ lt = inj₂ (asym (at (q ++ [ ix 0 ])) κ lt)

-- A takeWhile's failing value: its end owed below where it fell.
take-owe : ∀ {Γ A} {i f} (s : St Γ A) q → Into (at q) (takeS i f free s) (takeS i f (cpAt q) s)
take-owe s q (k-own (here refl)) = inj₂ (ext-le q [ last ])
take-owe s q (k-own (there ()))
take-owe s q (k-kid (k-take h)) = inj₁ (k-kid (k-take h))

module _ {R : Set} where
  -- A RISE: on where it was, a level down, or absorbed keeping its keys,
  -- a feed's or a failed take's only past it.
  rises : ∀ {Γ A} (c : Ctx R Γ A) s ε q {τ k′} → Lo (plug c s) (after q)
        → Driver.step R ⟨ c , s , rising ε , q ⟩ ≡ Driver.silent τ k′ → at q ⊑ Clock k′
  rises top s (nx a) q fl ()
  rises top s cp     q fl ()
  rises (inMap f c) s ε q fl refl = ⊑-refl
  rises (inScan f z c) s (nx a) q fl refl = ⊑-refl
  rises (inScan f z c) s cp     q fl refl = ⊑-refl
  rises (inCut l a c) s ε q fl refl = here-ok (if l then rising ε else absorbed) c (cutS l a s) q (lo-weaken (at q) (after q) fl (at-after₀ q))
  rises (inLn b c) s ε q fl refl = ⊑-refl
  rises (inTake i f free c) s (nx a) q fl eq with f a | i
  rises (inTake i f free c) s (nx a) q fl refl | true  | _     = ⊑-refl
  rises (inTake i f free c) s (nx a) q fl refl | false | true  = ext-⊑ q [ ix 0 ]
  rises (inTake i f free c) s (nx a) q fl refl | false | false =
    absorb c (takeS false f free s) (takeS false f (cpAt q) s) q (take-owe {i = false} {f} s q) (lo-weaken (at q) (after q) fl (at-after₀ q))
  rises (inTake i f free c) s cp q fl refl = ⊑-refl
  rises (inTake i f (cpAt r) c)  s ε q fl refl = clock-abs c (takeS i f (cpAt r) s) q (lo-weaken (at q) (after q) fl (at-after₀ q))
  rises (inTake i f (cutAt r) c) s ε q fl refl = clock-abs c (takeS i f (cutAt r) s) q (lo-weaken (at q) (after q) fl (at-after₀ q))
  rises (inTake i f (overAt r) c) s ε q fl refl = clock-abs c (takeS i f (overAt r) s) q (lo-weaken (at q) (after q) fl (at-after₀ q))
  rises (inOuter (mergeᶠ nothing) f d n qs ls c) s (nx a) q fl eq with closed c
  rises (inOuter (mergeᶠ nothing) f d n qs ls c) s (nx a) q fl refl | true  =
    clock-abs c (flatS (mergeᶠ nothing) f d n qs s ls) q (lo-weaken (at q) (after q) fl (at-after₀ q))
  rises (inOuter (mergeᶠ nothing) f d n qs ls c) s (nx a) q fl refl | false = ext-⊑ q [ ix 1 ]
  rises (inOuter (mergeᶠ (just mx)) f d n qs ls c) s (nx a) q fl eq with n <ᵇ mx
  rises (inOuter (mergeᶠ (just mx)) f d n qs ls c) s (nx a) q fl refl | false =
    absorb c (flatS (mergeᶠ (just mx)) f d n qs s ls) (flatS (mergeᶠ (just mx)) f d n (qs ++ [ a ]) s ls) q
           (λ ki → inj₁ (flat-in (λ h → h) same-l ki)) (lo-weaken (at q) (after q) fl (at-after₀ q))
  rises (inOuter (mergeᶠ (just mx)) f d n qs ls c) s (nx a) q fl eq | true with closed c
  rises (inOuter (mergeᶠ (just mx)) f d n qs ls c) s (nx a) q fl refl | true | true  =
    clock-abs c (flatS (mergeᶠ (just mx)) f d n qs s ls) q (lo-weaken (at q) (after q) fl (at-after₀ q))
  rises (inOuter (mergeᶠ (just mx)) f d n qs ls c) s (nx a) q fl refl | true | false = ext-⊑ q [ ix 1 ]
  rises (inOuter switchᶠ f d n qs ls c) s (nx a) q fl eq with killAll ls | (λ {x} {κ} → kill-in ls {x} {κ})
  rises (inOuter switchᶠ f d n qs ls c) s (nx a) q fl eq | ls′ , t | kl with closed c
  rises (inOuter switchᶠ f d n qs ls c) s (nx a) q fl refl | ls′ , t | kl | true  =
    absorb c (flatS switchᶠ f d n qs s ls) (flatS switchᶠ f d 0 qs s ls′) q (λ ki → inj₁ (flat-in (λ h → h) kl ki)) (lo-weaken (at q) (after q) fl (at-after₀ q))
  rises (inOuter switchᶠ f d n qs ls c) s (nx a) q fl refl | ls′ , t | kl | false = ext-⊑ q [ ix 1 ]
  rises (inOuter exhaustᶠ f d n qs ls c) s (nx a) q fl eq with n ≡ᵇ 0
  rises (inOuter exhaustᶠ f d n qs ls c) s (nx a) q fl refl | false =
    clock-abs c (flatS exhaustᶠ f d n qs s ls) q (lo-weaken (at q) (after q) fl (at-after₀ q))
  rises (inOuter exhaustᶠ f d n qs ls c) s (nx a) q fl eq | true with closed c
  rises (inOuter exhaustᶠ f d n qs ls c) s (nx a) q fl refl | true | true  =
    clock-abs c (flatS exhaustᶠ f d n qs s ls) q (lo-weaken (at q) (after q) fl (at-after₀ q))
  rises (inOuter exhaustᶠ f d n qs ls c) s (nx a) q fl refl | true | false = ext-⊑ q [ ix 1 ]
  rises (inOuter op f d n qs ls c) s cp q fl refl =
    md-at (if d then absorbed else settle true n (null qs)) c (flatS op f d n qs s ls) (flatS op f true n qs s ls) q
          (λ ki → inj₁ (flat-in (λ h → h) same-l ki)) (lo-weaken (at q) (after q) fl (at-after₀ q))
  rises (inLanes op f d n qs o′ pre post c) s (nx b) q fl eq with alive s
  rises (inLanes op f d n qs o′ pre post c) s (nx b) q fl refl | true  = ⊑-refl
  rises (inLanes op f d n qs o′ pre post c) s (nx b) q fl refl | false =
    clock-abs c (flatS op f d n qs o′ (pre ʳ++ s ∷ post)) q (lo-weaken (at q) (after q) fl (at-after₀ q))
  rises (inLanes op f d n qs o′ pre post c) s cp q fl eq with alive s
  rises (inLanes op f d n qs o′ pre post c) s cp q fl refl | false =
    clock-abs c (flatS op f d n qs o′ (pre ʳ++ s ∷ post)) q (lo-weaken (at q) (after q) fl (at-after₀ q))
  rises (inLanes op f d n [] o′ pre post c) s cp q fl refl | true =
    md-at (settle d (pred n) true) c (flatS op f d n [] o′ (pre ʳ++ s ∷ post)) (flatS op f d (pred n) [] o′ (pre ʳ++ ended s ∷ post)) q
          (λ ki → inj₁ (flat-in (λ h → h) (lanes-in pre post (ended-in s)) ki)) (lo-weaken (at q) (after q) fl (at-after₀ q))
  rises (inLanes op f d n (a ∷ qs) o′ pre post c) s cp q fl eq | true with closed c
  rises (inLanes op f d n (a ∷ qs) o′ pre post c) s cp q fl refl | true | true  =
    absorb c (flatS op f d n (a ∷ qs) o′ (pre ʳ++ s ∷ post)) (flatS op f d (pred n) qs o′ (pre ʳ++ ended s ∷ post)) q
           (λ ki → inj₁ (flat-in (λ h → h) (lanes-in pre post (ended-in s)) ki)) (lo-weaken (at q) (after q) fl (at-after₀ q))
  rises (inLanes op f d n (a ∷ qs) o′ pre post c) s cp q fl refl | true | false = ext-⊑ q [ ix 1 ]
  rises (inSrc k b c) s (nx a) q fl refl =
    ⊑-trans (ext-⊑ q [ ix 0 ]) (clock-abs c (connS k s (feed (here refl) q (nx a) b)) q {at (q ++ [ ix 0 ])} (fed-lo c k k s b q (nx a) (fewer-same {k = k}) fl))
  rises (inSrc k b c) s cp q fl refl =
    ⊑-trans (ext-⊑ q [ ix 0 ]) (clock-abs c (connS (shutAt q k) s (feed (here refl) q cp b)) q {at (q ++ [ ix 0 ])} (fed-lo c k (shutAt q k) s b q cp (shut-fewer q k) fl))
  rises (inBody k o′ c) s (nx b) q fl eq with CS.srcLive k
  rises (inBody k o′ c) s (nx b) q fl refl | true  = ⊑-refl
  rises (inBody k o′ c) s (nx b) q fl refl | false = clock-abs c (connS k o′ s) q (lo-weaken (at q) (after q) fl (at-after₀ q))
  rises (inBody k o′ c) s cp q fl eq with CS.srcLive k
  rises (inBody k o′ c) s cp q fl refl | true  = ⊑-refl
  rises (inBody k o′ c) s cp q fl refl | false = clock-abs c (connS k o′ s) q (lo-weaken (at q) (after q) fl (at-after₀ q))

  -- A SUBSCRIBE: on where it was or a level down, or absorbed over marks
  -- owed below where it was made.
  begins : ∀ (o : PureObs [] R) {rs Γ A} (c : Ctx R Γ A) (o′ : PureObs Γ A) q {τ k′}
         → Path (load o) rs ⟨ c , pend o′ q , subscribing , q ⟩ → Lo (plug c (pend o′ q)) (at q)
         → Driver.step R ⟨ c , pend o′ q , subscribing , q ⟩ ≡ Driver.silent τ k′ → at q ⊑ Clock k′
  begins o c (map f s′)         q pth lo refl = ⊑-refl
  begins o c (scan f z s′)      q pth lo refl = ⊑-refl
  begins o c (takeWhile i f s′) q pth lo refl = ⊑-refl
  begins o c (flatMap op f s′)  q pth lo refl = ⊑-refl
  begins o c (connect s′ b)     q pth lo refl = ext-⊑ q [ ix 0 ]
  begins o c (defer l)          q pth lo refl = ext-⊑ q [ ix 1 ]
  begins o c (cold x)           q pth lo refl =
    absorb c (pend (cold x) q) (coldS true (opening q (timelineAt x q))) q (λ {κ} h → inj₂ (asym (at q) κ (opening-ahead o pth (cold-key h)))) lo
  begins o c empty              q pth lo refl = absorb c (pend empty q) (ofS 0 q []) q (λ h → inj₂ (of-key 0 q [] h)) lo
  begins o c (of xs)            q pth lo refl = absorb c (pend (of xs) q) (ofS 0 q xs) q (λ h → inj₂ (of-key 0 q xs h)) lo
  begins o c (connected x)      q pth lo eq with closedUp c x
  begins o c (connected x)      q pth lo refl | true  = absorb c (pend (connected x) q) (ofS 0 q []) q (λ h → inj₂ (of-key 0 q [] h)) lo
  begins o c (connected x)      q pth lo refl | false = absorb c (pend (connected x) q) (joinS q true x []) q (λ { (k-own ()) ; (k-kid ()) }) lo

  -- A joiner's next entry: none before the one it ran.
  inbox-into : ∀ {Γ A} {t : St Γ A} {j g x} q₀ (ib : List (Pos × Ev A))
             → (∀ {q₁ e₁ ib′} → ib ≡ (q₁ , e₁) ∷ ib′ → at q₁ <ᴷ at q₀ ≡ false) → Into (at q₀) t (joinS j g x ib)
  inbox-into q₀ []              h (k-own ())
  inbox-into q₀ []              h (k-kid ())
  inbox-into q₀ ((q₁ , e₁) ∷ ib) h (k-own (here refl)) = inj₂ (h refl)
  inbox-into q₀ ((q₁ , e₁) ∷ ib) h (k-own (there ()))
  inbox-into q₀ ((q₁ , e₁) ∷ ib) h (k-kid ())

  -- A cold's turn: on at its tick, or absorbed with its next due past it.
  leafs : ∀ {Γ A} (c : Ctx R Γ A) q b (l : Tape A) {κ} → (leafM , κ) ∈ own {Γ} (coldS b l) → Lo (plug c (coldS b l)) κ
        → (∀ {τ u i t f κ′} → l ≡ play τ u i t (close f) → due (rest τ (u ++ [ last ]) (From∞.force f)) ≡ just κ′ → κ <ᴷ κ′ ≡ true)
        → ∀ {τ k′} → Driver.took R (run c (coldS b l) leafM q) ≡ Driver.silent τ k′ → κ ⊑ Clock k′
  leafs c q b     overT              () lo ah eq
  leafs c q false (ending e₀)        (here refl) lo ah refl = absorb c (coldS false (ending e₀)) (coldS false overT) q (λ { (k-own ()) ; (k-kid ()) }) lo
  leafs c q false (play τ u i t fr)  (here refl) lo ah refl = absorb c (coldS false (play τ u i t fr)) (coldS false overT) q (λ { (k-own ()) ; (k-kid ()) }) lo
  leafs c q true  (ending e₀)        (here refl) lo ah refl =
    md-at (if not (closed c) then rising cp else absorbed) c (coldS true (ending e₀)) (coldS false overT) e₀ (λ { (k-own ()) ; (k-kid ()) }) lo
  leafs c q true  (play τ u i t fr)  (here refl) lo ah eq with closed c
  leafs c q true  (play τ u i t fr)  (here refl) lo ah refl | true =
    absorb c (coldS true (play τ u i t fr)) (coldS true overT) q (λ { (k-own ()) ; (k-kid ()) }) lo
  leafs c q true  (play τ u i t (emit a f))  (here refl) lo ah refl | false = ⊑-refl
  leafs c q true  (play τ u i t (stall f)) {κ} (here refl) lo ah refl | false =
    absorb c (coldS true (play τ u i t (stall f))) (coldS true (play τ u (suc i) t (Frame∞.force f))) q
      (λ { (k-own (here refl)) → inj₂ (asym κ (at (u ++ [ ix (suc i) ])) (trans (at-<ᴷ (u ++ [ ix i ]) (u ++ [ ix (suc i) ])) (<ᵖ-part u [] [] (<ᵖ-ix i))))
         ; (k-own (there ())) ; (k-kid ()) }) lo
  leafs c q true  (play τ u i t (close f)) {κ} (here refl) lo ah refl | false =
    absorb c (coldS true (play τ u i t (close f))) (coldS true (rest τ (u ++ [ last ]) (From∞.force f))) q
      (λ {κ′} h → inj₂ (asym κ κ′ (ah refl (cold-key h)))) lo

  -- A connect's admin mark: its body subscribed where it was keyed, or
  -- absorbed keeping fewer keys.
  conns : ∀ {Γ A X} (c : Ctx R Γ A) q (k : CS Γ X) (o′ : St Γ X) b mk → mk ≡ bodyM ⊎ (mk ≡ srcAttM ⊎ mk ≡ owedM)
        → ∀ {κ} → (mk , κ) ∈ own (connS k o′ b) → Lo (plug c (connS k o′ b)) κ
        → ∀ {τ k′} → Driver.took R (run c (connS k o′ b) mk q) ≡ Driver.silent τ k′ → κ ⊑ Clock k′
  conns c q k@(cs cl sl sa (just p₀) as ow ca ea sr sc) o′ b .bodyM (inj₁ refl) mi lo refl = ⊑i (lo (plug-in c (k-own (here refl))))
  conns c q k@(cs cl sl sa nothing as ow ca ea sr sc) o′ b .bodyM (inj₁ refl) mi lo refl = clock-abs c (connS k o′ b) q lo
  conns c q k@(cs cl sl sa ba (just p₀) ow ca ea sr sc) o′ b .srcAttM (inj₂ (inj₁ refl)) {κ} mi lo refl =
    absorb c (connS k o′ b) (connS (cs cl sl true ba nothing ow ca ea sr sc) (proj₁ (unsubIf (not sl) o′)) b) p₀ into lo
    where
      into : Into κ (connS k o′ b) (connS (cs cl sl true ba nothing ow ca ea sr sc) (proj₁ (unsubIf (not sl) o′)) b)
      into (k-own m) = inj₁ (k-own (own-fewer k (cs cl sl true ba nothing ow ca ea sr sc) {o′} {proj₁ (unsubIf (not sl) o′)} {b} {b}
                                       ((λ e → e) , (λ ()) , (λ e → e)) m))
      into (k-kid (k-src h))  = inj₁ (k-kid (k-src (unsubIf-in (not sl) o′ h)))
      into (k-kid (k-body h)) = inj₁ (k-kid (k-body h))
  conns c q k@(cs cl sl sa ba nothing ow ca ea sr sc) o′ b .srcAttM (inj₂ (inj₁ refl)) mi lo refl = clock-abs c (connS k o′ b) q lo
  conns c q k@(cs cl sl sa ba as (just p₀) ca ea sr sc) o′ b .owedM (inj₂ (inj₂ refl)) {κ} mi lo refl =
    absorb c (connS k o′ b) (connS (cs cl false sa ba as nothing ca ea sr sc) (proj₁ (unsubIf sa o′)) b) p₀ into lo
    where
      into : Into κ (connS k o′ b) (connS (cs cl false sa ba as nothing ca ea sr sc) (proj₁ (unsubIf sa o′)) b)
      into (k-own m) = inj₁ (k-own (own-fewer k (cs cl false sa ba as nothing ca ea sr sc) {o′} {proj₁ (unsubIf sa o′)} {b} {b}
                                       ((λ e → e) , (λ e → e) , (λ ())) m))
      into (k-kid (k-src h))  = inj₁ (k-kid (k-src (unsubIf-in sa o′ h)))
      into (k-kid (k-body h)) = inj₁ (k-kid (k-body h))
  conns c q k@(cs cl sl sa ba as nothing ca ea sr sc) o′ b .owedM (inj₂ (inj₂ refl)) mi lo refl = clock-abs c (connS k o′ b) q lo

  -- A MARK RUN: on at the mark's own key, or absorbed with what it owes
  -- next no earlier.
  runs : ∀ {Γ A} (c : Ctx R Γ A) q {s : St Γ A} {mk κ} → Marked s mk → (mk , κ) ∈ own s → Lo (plug c s) κ
       → (∀ {b τ u i t f κ′} → s ≡ coldS b (play τ u i t (close f)) → mk ≡ leafM → due (rest τ (u ++ [ last ]) (From∞.force f)) ≡ just κ′ → κ <ᴷ κ′ ≡ true)
       → (∀ {j g x q₀ e q₁ e₁ ib} → s ≡ joinS j g x ((q₀ , e) ∷ (q₁ , e₁) ∷ ib) → mk ≡ joinM → at q₁ <ᴷ at q₀ ≡ false)
       → ∀ {τ k′} → Driver.took R (run c s mk q) ≡ Driver.silent τ k′ → κ ⊑ Clock k′
  runs c q (ofK i p₀ []) (here refl) lo ah asc eq with closed c
  runs c q (ofK i p₀ []) (here refl) lo ah asc refl | true  = absorb c (ofS i p₀ []) doneS p₀ (λ { (k-own ()) ; (k-kid ()) }) lo
  runs c q (ofK i p₀ []) (here refl) lo ah asc refl | false = ⊑-refl
  runs c q (ofK i p₀ []) (there ()) lo ah asc eq
  runs c q (ofK i p₀ (x ∷ xs)) (here refl) lo ah asc eq with closed c
  runs c q (ofK i p₀ (x ∷ xs)) (here refl) lo ah asc refl | true  = absorb c (ofS i p₀ (x ∷ xs)) doneS p₀ (λ { (k-own ()) ; (k-kid ()) }) lo
  runs c q (ofK i p₀ (x ∷ xs)) (here refl) lo ah asc refl | false = ⊑-refl
  runs c q (ofK i p₀ (x ∷ xs)) (there ()) lo ah asc eq
  runs c q (attK l p₀ s₀) mi lo ah asc refl =
    absorb c (cutS l (attAt p₀) s₀) (cutS l attached (proj₁ (unsubIf (not l) s₀))) p₀
      (λ { (k-own ()) ; (k-kid (k-cut h)) → inj₁ (k-kid (k-cut (unsubIf-in (not l) s₀ h))) }) lo
  runs c q (conK k o′ b mk w) mi lo ah asc eq = conns c q k o′ b mk w mi lo eq
  runs c q (joinK j g x q₀ (nx a) ib) (here refl) lo ah asc refl =
    md-at (if g ∧ not (closed c) then rising (nx a) else absorbed) c (joinS j g x ((q₀ , nx a) ∷ ib)) (joinS j g x ib) q₀
      (inbox-into q₀ ib (λ { refl → asc refl refl })) lo
  runs c q (joinK j g x q₀ cp ib) (here refl) lo ah asc refl =
    md-at (if g ∧ not (closed c) then rising cp else absorbed) c (joinS j g x ((q₀ , cp) ∷ ib)) (joinS j false x ib) q₀
      (inbox-into q₀ ib (λ { refl → asc refl refl })) lo
  runs c q (joinK j g x q₀ e ib) (there ()) lo ah asc eq
  runs c q (leafK b l) mi lo ah asc eq = leafs c q b l mi lo (λ e → ah (cong (coldS b) e) refl) eq
  runs c q (stopK i f r s₀) (here refl) lo ah asc refl =
    md-at (if not (closed c) then rising cp else absorbed) c (takeS i f (cpAt r) s₀) (takeS i f (cutAt r) s₀) (r ++ [ last ])
      (λ { (k-own (here refl)) → inj₂ (asym (at (r ++ [ last ])) (after r) (at-after r [ last ])) ; (k-own (there ())) ; (k-kid (k-take h)) → inj₁ (k-kid (k-take h)) }) lo
  runs c q (stopK i f r s₀) (there ()) lo ah asc eq
  runs c q (cutK i f r s₀) mi lo ah asc refl =
    absorb c (takeS i f (cutAt r) s₀) (takeS i f (overAt r) (proj₁ (cut s₀))) r
      (λ { (k-own ()) ; (k-kid (k-take h)) → inj₁ (k-kid (k-take (cut-in s₀ h))) }) lo

  absorbs : ∀ (o : PureObs [] R) {rs Γ A} (c : Ctx R Γ A) s q → Path (load o) rs ⟨ c , s , absorbed , q ⟩
          → ∀ {τ k′} → Driver.step R ⟨ c , s , absorbed , q ⟩ ≡ Driver.silent τ k′ → Clock ⟨ c , s , absorbed , q ⟩ ⊑ Clock k′
  absorbs o c s q pth with search top (plug c s) in fd
  ... | nothing = λ ()
  ... | just (found (_ , _ , c′ , s′) mk κ) = λ eq →
    runs c′ q (found-mark c s fd) (proj₁ (found-least {t = plug c s} fd))
      (subst (λ t → Lo t κ) (sym (found-plug c s fd)) (proj₂ (found-least {t = plug c s} fd)))
      (λ { refl refl dr → frame-ahead o pth fd dr })
      (λ { refl refl → inbox-asc o pth fd })
      eq

------------------------------------------------------------------------
-- The clock ahead

-- THE CLOCK NEVER RUNS BACK: a silent step's clock is no earlier.
-- DEAD ROUTE: the least mark due as the clock throughout.  A lane begun
--   by an outer's value makes marks under that value, before the outer's
--   next mark, so mid-run the least key falls.
clock-mono : ∀ {R} (o : PureObs [] R) {rs k k′} → Path (load o) rs k → k′ ⇜ k → Clock k ⊑ Clock k′
clock-mono o {k = ⟨ c , s , rising ε , q ⟩}  pth (_ , eq) = rises c s ε q (floor o pth tt) eq
clock-mono o {k = ⟨ c , s , subscribing , q ⟩} pth (_ , eq) with pend-focus o pth
... | o′ , refl = begins o c o′ q pth (lo-weaken (at q) (after q) (floor o pth tt) (at-after₀ q)) eq
clock-mono o {k = ⟨ c , s , absorbed , q ⟩}  pth (_ , eq) = absorbs o c s q pth eq

-- A SOURCE'S FEED COMES DUE NO SOONER: once a source has risen, every
-- mark is due no earlier than the row a level down.
fed-ahead : ∀ {R} (o : PureObs [] R) {rs Γ X B} {k : CS Γ X} {b : St (X ∷ Γ) B} {c : Ctx R Γ B} {s ε q k′}
          → Path (load o) rs ⟨ inSrc k b c , s , rising ε , q ⟩ → k′ ⇜ ⟨ inSrc k b c , s , rising ε , q ⟩
          → Clock k′ <ᴷ at (q ++ [ ix 0 ]) ≡ false
fed-ahead o {k = k} {b} {c} {s} {nx a} {q} pth (_ , refl) =
  _⊑_.un (clock-abs c (connS k s (feed (here refl) q (nx a) b)) q {at (q ++ [ ix 0 ])} (fed-lo c k k s b q (nx a) (fewer-same {k = k}) (floor o pth tt)))
fed-ahead o {k = k} {b} {c} {s} {cp} {q} pth (_ , refl) =
  _⊑_.un (clock-abs c (connS (shutAt q k) s (feed (here refl) q cp b)) q {at (q ++ [ ix 0 ])} (fed-lo c k (shutAt q k) s b q cp (shut-fewer q k) (floor o pth tt)))
