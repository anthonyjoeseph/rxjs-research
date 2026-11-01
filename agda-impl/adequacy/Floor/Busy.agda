{-# OPTIONS --guardedness #-}

-- THE FLOOR: mid-run at `p`, no mark is keyed before `p`'s whole subtree
-- is past.  A run begun keeps it to its end: a rise climbs at `p` or
-- moves a level down, a subscribe moves at most a level down, and every
-- mark either owes is keyed past where it then is.  What is left is the
-- phase start: the least mark run from rest, every other mark clear of
-- the subtree it opens.
module adequacy.Floor.Busy where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_; _ʳ++_; reverse)
open import Data.List.Properties using (ʳ++-defn; reverse-involutive)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (_<ᵇ_; _≡ᵇ_; pred)
open import Data.Product using (Σ; _,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Level using (Lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

open import Tree using (mergeᶠ; switchᶠ; exhaustᶠ; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer; Later)
open import denotation.Events using (ix; last; root; _≟ˡ_; _<ᵖ_; <ᵖ-irrefl; <ᵖ-ix)
open import operation.PureObservable using (PureObs; module Machine; module Driver)
open Machine using (Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody; St; pend; mapS; scanS; cutS; lnS; takeS; flatS; connS;
                    CS; cs; Mode; Conf; ⟨_,_,_,_⟩; plug; load; subscribing; absorbed; rising; nx; cp; closed; closedUp; alive; killAll; ended; scopeOf;
                    attAt; free; cpAt; cutAt; overAt; Stepped; moved; starting; turn; quiet; Poke; rise; begin; start; dequeue; admit; Ev)
open import operation.Key using (at; after; _<ᴷ_; <ᴷ-irrefl)
open import adequacy.Least using (KeyIn; k-own; k-kid; k-map; k-scan; k-cut; k-ln; k-take; k-outer; k-lane; k-src; k-body; Lo)
open import adequacy.Stamped using (pend-focus; played-val)
open import adequacy.Path using (Path; []; tau; val; _▸_)
open import adequacy.Floor.Keys using (Into; asym; sub-at; lo-weaken; flat-in; same-l; kill-in; lanes-in; ended-in; ob; os; oo;
  own-cls; own-bld)

------------------------------------------------------------------------
-- Keys under a position

-- Below a position, its after is earlier.
after-in : ∀ p l ys → after (p ++ l ∷ ys) <ᴷ after p ≡ true
after-in []      l ys = refl
after-in (a ∷ p) l ys with a ≟ˡ a
... | yes _ rewrite <ᵖ-irrefl [ a ] = after-in p l ys
... | no ¬e = ⊥-elim (¬e refl)

-- A subtree before a later sibling.
after-part : ∀ p {a b} ys zs → [ a ] <ᵖ [ b ] ≡ true → after (p ++ a ∷ ys) <ᴷ at (p ++ b ∷ zs) ≡ true
after-part []      ys zs h rewrite h = refl
after-part (a ∷ p) ys zs h with a ≟ˡ a
... | yes _ rewrite <ᵖ-irrefl [ a ] = after-part p ys zs h
... | no ¬e = ⊥-elim (¬e refl)

-- A subscription not yet made keeps no keys.
none-pend : ∀ {Γ A} {o : PureObs Γ A} {q κ} → KeyIn (pend o q) κ → ⊥
none-pend (k-own ())
none-pend (k-kid ())

-- A lane begun after the rest.
mem-snoc : ∀ {a} {S : Set a} (ls : List S) {y x} → x ∈ reverse ls ʳ++ y ∷ [] → x ≡ y ⊎ x ∈ ls
mem-snoc ls {y} m rewrite ʳ++-defn (reverse ls) {y ∷ []} | reverse-involutive ls with ∈-++⁻ ls m
... | inj₁ m′         = inj₂ m′
... | inj₂ (here e)   = inj₁ e
... | inj₂ (there ())

------------------------------------------------------------------------
-- The floor

-- Mid-run.
Busy : ∀ {A} → Mode A → Set
Busy absorbed    = ⊥
Busy subscribing = ⊤
Busy (rising _)  = ⊤

-- Mid-run at `p`, every mark past `p`'s subtree.
Floored : ∀ {R} → Conf R → Set₁
Floored ⟨ c , s , m , p ⟩ = Busy m → Lo (plug c s) (after p)

module _ {R : Set} where
  open Driver R using (Step; took; played; silent; value)

  -- What a step hands on keeps the floor.
  FlS : Stepped R → Set₁
  FlS (moved k _ _)    = Floored k
  FlS (starting x p k) = ∀ l → Floored (k l)
  FlS (turn pk)        = ∀ {τ k′} → played pk ≡ silent τ k′ → Floored k′
  FlS quiet            = Lift (lsuc lzero) ⊤

  -- One step on to `k′`, silent or showing a value.
  data Onto (st : Step) (k′ : Conf R) : Set₁ where
    onS : ∀ {τ} → st ≡ silent τ k′ → Onto st k′
    onV : ∀ {τ p a} → st ≡ value τ p a k′ → Onto st k′

  took-fl : (x : Stepped R) → FlS x → ∀ {k′} → Onto (took x) k′ → Floored k′
  took-fl (moved k [] _)               h (onS refl) = h
  took-fl (moved k [] _)               h (onV ())
  took-fl (moved k ((p , nx a) ∷ _) _) h (onS ())
  took-fl (moved k ((p , nx a) ∷ _) _) h (onV refl) = h
  took-fl (moved k ((p , cp) ∷ _) _)   h (onS ())
  took-fl (moved k ((p , cp) ∷ _) _)   h (onV ())
  took-fl (starting x p k)             h (onS refl) = h _
  took-fl (starting x p k)             h (onV ())
  took-fl (turn pk)                    h (onS e) = h e
  took-fl (turn pk)                    h (onV e) = ⊥-elim (played-val pk e)
  took-fl quiet                        h (onS ())
  took-fl quiet                        h (onV ())

  -- A lane's begun: every key the flatMap had, and the lane's cut past it.
  start-fl : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → PureObs Γ B) d n q o ls a p {t : St Γ B}
           → (∀ {x κ} → x ∈ ls → KeyIn x κ → KeyIn t κ) → (∀ {κ} → KeyIn o κ → KeyIn t κ)
           → Lo (plug c t) (after p) → Floored (start c op f d n q o ls a p)
  start-fl c op f d n q o ls a p {t} hl ho fl with closed c
  ... | true  = λ ()
  ... | false = λ _ → sub-at c {t} {flatS op f d _ q o (reverse ls ʳ++ lnS true (cutS true (attAt (p ++ [ ix 1 ])) (pend (f a) (p ++ [ ix 1 ]))) ∷ [])} {after (p ++ [ ix 1 ])}
                  into (lo-weaken (after (p ++ [ ix 1 ])) (after p) fl (after-in p (ix 1) []))
    where
      into : Into (after (p ++ [ ix 1 ])) t (flatS op f d _ q o (reverse ls ʳ++ lnS true (cutS true (attAt (p ++ [ ix 1 ])) (pend (f a) (p ++ [ ix 1 ]))) ∷ []))
      into (k-own ())
      into (k-kid (k-outer h)) = inj₁ (ho h)
      into (k-kid (k-lane m h)) with mem-snoc ls m
      into (k-kid (k-lane m h)) | inj₂ m′ = inj₁ (hl m′ h)
      into (k-kid (k-lane m (k-own ()))) | inj₁ refl
      into (k-kid (k-lane m (k-kid (k-ln (k-own (here refl)))))) | inj₁ refl = inj₂ (<ᴷ-irrefl (after (p ++ [ ix 1 ])))
      into (k-kid (k-lane m (k-kid (k-ln (k-own (there ())))))) | inj₁ refl
      into (k-kid (k-lane m (k-kid (k-ln (k-kid (k-cut h)))))) | inj₁ refl = ⊥-elim (none-pend h)

  -- A slot freed: the next lane begun, or the flatMap settled keeping its keys.
  dequeue-fl : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → PureObs Γ B) d n q o ls p {t : St Γ B}
             → (∀ {x κ} → x ∈ ls → KeyIn x κ → KeyIn t κ) → (∀ {κ} → KeyIn o κ → KeyIn t κ)
             → Lo (plug c t) (after p) → Floored (dequeue c op f d n q o ls p)
  dequeue-fl c op f d n []      o ls p {t} hl ho fl = λ _ → sub-at c {t} {flatS op f d n [] o ls} {after p} into fl
    where
      into : Into (after p) t (flatS op f d n [] o ls)
      into (k-own ())
      into (k-kid (k-outer h))  = inj₁ (ho h)
      into (k-kid (k-lane m h)) = inj₁ (hl m h)
  dequeue-fl c op f d n (a ∷ q) o ls p hl ho fl = start-fl c op f d n q o ls a p hl ho fl

  -- An outer's value admitted.
  admit-fl : ∀ {Γ A B} (c : Ctx R Γ B) op (f : A → PureObs Γ B) d n q o ls a p
           → Lo (plug c (flatS op f d n q o ls)) (after p) → FlS (admit c op f d n q o ls a p)
  admit-fl c (mergeᶠ nothing)  f d n q o ls a p fl = start-fl c _ f d n q o ls a p (λ m h → k-kid (k-lane m h)) (λ h → k-kid (k-outer h)) fl
  admit-fl c (mergeᶠ (just m)) f d n q o ls a p fl with n <ᵇ m
  ... | true  = start-fl c _ f d n q o ls a p (λ m h → k-kid (k-lane m h)) (λ h → k-kid (k-outer h)) fl
  ... | false = λ ()
  admit-fl c switchᶠ           f d n q o ls a p fl with killAll ls | (λ {x} {κ} → kill-in ls {x} {κ})
  ... | ls′ , _ | kl = start-fl c switchᶠ f d 0 q o ls′ a p (λ m h → lane (kl m h)) (λ h → k-kid (k-outer h)) fl
    where
      lane : ∀ {κ} → Σ _ (λ y → y ∈ ls × KeyIn y κ) → KeyIn (flatS switchᶠ f d n q o ls) κ
      lane (_ , m′ , h′) = k-kid (k-lane m′ h′)
  admit-fl c exhaustᶠ          f d n q o ls a p fl with n ≡ᵇ 0
  ... | true  = start-fl c _ f d n q o ls a p (λ m h → k-kid (k-lane m h)) (λ h → k-kid (k-outer h)) fl
  ... | false = λ ()

  -- A RISE KEEPS THE FLOOR: on at `p` keeping its keys, a level down
  -- owing only past it, or absorbed.
  rise-fl : ∀ {Γ A} (c : Ctx R Γ A) s (e : Ev A) p → Lo (plug c s) (after p) → FlS (rise c s e p)
  rise-fl top            s e      p fl = λ ()
  rise-fl (inMap f c)    s e      p fl = λ _ → fl
  rise-fl (inScan f z c) s (nx a) p fl =
    λ _ → sub-at c {scanS f z s} {scanS f (f z a) s} {after p} (λ { (k-own ()) ; (k-kid (k-scan h)) → inj₁ (k-kid (k-scan h)) }) fl
  rise-fl (inScan f z c) s cp     p fl = λ _ → fl
  rise-fl (inCut l a c)  s e      p fl = λ _ → fl
  rise-fl (inLn b c)     s e      p fl = λ _ → fl
  rise-fl (inTake i q free c) s (nx a) p fl with q a | i
  ... | true  | _     = λ _ → fl
  ... | false | true  = λ _ → sub-at c {takeS true q free s} {takeS true q (cpAt p) s} {after (p ++ [ ix 0 ])} into (lo-weaken (after (p ++ [ ix 0 ])) (after p) fl (after-in p (ix 0) []))
    where
      into : Into (after (p ++ [ ix 0 ])) (takeS true q free s) (takeS true q (cpAt p) s)
      into (k-own (here refl)) = inj₂ (asym (after (p ++ [ ix 0 ])) (at (p ++ [ last ])) (after-part p [] [] refl))
      into (k-own (there ()))
      into (k-kid (k-take h)) = inj₁ (k-kid (k-take h))
  ... | false | false = λ ()
  rise-fl (inTake i q free c)     s cp p fl = λ _ → fl
  rise-fl (inTake i q (cpAt r) c)  s e p fl = λ ()
  rise-fl (inTake i q (cutAt r) c) s e p fl = λ ()
  rise-fl (inTake i q (overAt r) c) s e p fl = λ ()
  rise-fl (inOuter op f d n q ls c) o (nx a) p fl = admit-fl c op f d n q o ls a p fl
  rise-fl (inOuter op f d n q ls c) o cp     p fl =
    λ _ → sub-at c {flatS op f d n q o ls} {flatS op f true n q o ls} {after p} (λ ki → inj₁ (flat-in (λ h → h) same-l ki)) fl
  rise-fl (inLanes op f d n q o pre post c) s (nx b) p fl with alive s
  ... | true  = λ _ → fl
  ... | false = λ ()
  rise-fl (inLanes op f d n q o pre post c) s cp p fl with alive s
  ... | true  = dequeue-fl c op f d (pred n) q o (pre ʳ++ ended s ∷ post) p {flatS op f d n q o (pre ʳ++ s ∷ post)} (λ m h → lane (lanes-in pre post (ended-in s) m h)) (λ h → k-kid (k-outer h)) fl
    where
      lane : ∀ {κ} → Σ _ (λ y → y ∈ pre ʳ++ s ∷ post × KeyIn y κ) → KeyIn (flatS op f d n q o (pre ʳ++ s ∷ post)) κ
      lane (_ , m′ , h′) = k-kid (k-lane m′ h′)
  ... | false = λ ()
  rise-fl (inSrc k b c) s (nx a) p fl = λ ()
  rise-fl (inSrc k b c) s cp     p fl = λ ()
  rise-fl (inBody k o c) s (nx b) p fl with CS.srcLive k
  ... | true  = λ _ → fl
  ... | false = λ ()
  rise-fl (inBody (cs a false b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈) o c) s cp p fl = λ ()
  rise-fl (inBody k@(cs a true b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈) o c) s cp p fl = λ _ → sub-at c {connS k o s} {connS (record k { owedAt = just p }) o s} {after p} into fl
    where
      into : Into (after p) (connS k o s) (connS (record k { owedAt = just p }) o s)
      into (k-own m) with own-cls (record k { owedAt = just p }) {o} {s} m
      ... | ob e    = inj₁ (k-own (own-bld k {o} {s} (ob e)))
      ... | os e    = inj₁ (k-own (own-bld k {o} {s} (os e)))
      ... | oo refl = inj₂ (<ᴷ-irrefl (after p))
      into (k-kid (k-src h))  = inj₁ (k-kid (k-src h))
      into (k-kid (k-body h)) = inj₁ (k-kid (k-body h))

  -- A SUBSCRIBE KEEPS THE FLOOR: on where it was or a level down, its
  -- own cut past it, or absorbed.
  begin-fl : ∀ {Γ A} (c : Ctx R Γ A) (o : PureObs Γ A) p → Lo (plug c (pend o p)) (after p) → FlS (begin c o p)
  begin-fl c (cold x)          p fl = λ l ()
  begin-fl c empty             p fl = λ ()
  begin-fl c (of xs)           p fl = λ ()
  begin-fl c (map f s)         p fl = λ _ → sub-at c {pend (map f s) p} {mapS f (pend s p)} {after p} (λ { (k-own ()) ; (k-kid (k-map h)) → ⊥-elim (none-pend h) }) fl
  begin-fl c (scan f z s)      p fl = λ _ → sub-at c {pend (scan f z s) p} {scanS f z (pend s p)} {after p} (λ { (k-own ()) ; (k-kid (k-scan h)) → ⊥-elim (none-pend h) }) fl
  begin-fl c (takeWhile i q s) p fl = λ _ → sub-at c {pend (takeWhile i q s) p} {takeS i q free (cutS true (attAt p) (pend s p))} {after p} into fl
    where
      into : Into (after p) (pend (takeWhile i q s) p) (takeS i q free (cutS true (attAt p) (pend s p)))
      into (k-own ())
      into (k-kid (k-take (k-own (here refl)))) = inj₂ (<ᴷ-irrefl (after p))
      into (k-kid (k-take (k-own (there ()))))
      into (k-kid (k-take (k-kid (k-cut h)))) = ⊥-elim (none-pend h)
  begin-fl c (flatMap op f s)  p fl = λ _ → sub-at c {pend (flatMap op f s) p} {flatS op f false 0 [] (cutS true (attAt p) (pend s p)) []} {after p} into fl
    where
      into : Into (after p) (pend (flatMap op f s) p) (flatS op f false 0 [] (cutS true (attAt p) (pend s p)) [])
      into (k-own ())
      into (k-kid (k-outer (k-own (here refl)))) = inj₂ (<ᴷ-irrefl (after p))
      into (k-kid (k-outer (k-own (there ()))))
      into (k-kid (k-outer (k-kid (k-cut h)))) = ⊥-elim (none-pend h)
      into (k-kid (k-lane () h))
  begin-fl c (connect s b)     p fl =
    λ _ → sub-at c {pend (connect s b) p} {connS k (pend s (p ++ [ ix 1 ])) (pend b (p ++ [ ix 0 ]))} {after (p ++ [ ix 0 ])} into
                   (lo-weaken (after (p ++ [ ix 0 ])) (after p) fl (after-in p (ix 0) []))
    where
      k = cs false true false (just p) nothing nothing p root s (scopeOf c)
      into : Into (after (p ++ [ ix 0 ])) (pend (connect s b) p) (connS k (pend s (p ++ [ ix 1 ])) (pend b (p ++ [ ix 0 ])))
      into (k-own (here refl)) = inj₂ (asym (after (p ++ [ ix 0 ])) (at (p ++ [ ix 1 ])) (after-part p [] [] (<ᵖ-ix 0)))
      into (k-own (there ()))
      into (k-kid (k-src h))  = ⊥-elim (none-pend h)
      into (k-kid (k-body h)) = ⊥-elim (none-pend h)
  begin-fl c (connected x)     p fl with closedUp c x
  ... | true  = λ ()
  ... | false = λ ()
  begin-fl c (defer l)         p fl =
    λ _ → sub-at c {pend (defer l) p} {pend (Later.force l) (p ++ [ ix 1 ])} {after (p ++ [ ix 1 ])} (λ h → ⊥-elim (none-pend h))
                   (lo-weaken (after (p ++ [ ix 1 ])) (after p) fl (after-in p (ix 1) []))

postulate
  -- THE PHASE START: the least mark run from rest leaves every other
  -- mark past the subtree the run opens.
  floor-run : ∀ {R} (o : PureObs [] R) {rs Γ A} {c : Ctx R Γ A} {s q k′}
            → Path (load o) rs ⟨ c , s , absorbed , q ⟩ → Onto (Driver.step R ⟨ c , s , absorbed , q ⟩) k′ → Floored k′

module _ {R : Set} where
  -- A step on keeps the floor.
  floored-step : ∀ (o : PureObs [] R) {rs k k′} → Path (load o) rs k → Floored k → Onto (Driver.step R k) k′ → Floored k′
  floored-step o {k = ⟨ c , s , rising e , p ⟩} pth fl st = took-fl (rise c s e p) (rise-fl c s e p (fl tt)) st
  floored-step o {k = ⟨ c , s , subscribing , p ⟩} pth fl st with pend-focus o pth
  ... | o′ , refl = took-fl (begin c o′ p) (begin-fl c o′ p (fl tt)) st
  floored-step o {k = ⟨ c , s , absorbed , p ⟩} pth fl st = floor-run o pth st

  floored-path : ∀ (o : PureObs [] R) {rs rs′ k k″} → Path (load o) rs k → Floored k → Path k rs′ k″ → Floored k″
  floored-path o pre fl []          = fl
  floored-path o pre fl (tau e pth) = floored-path o (pre ▸ tau e []) (floored-step o pre fl (onS e)) pth
  floored-path o pre fl (val e pth) = floored-path o (pre ▸ val e []) (floored-step o pre fl (onV e)) pth

-- THE FLOOR, everywhere a run reaches.
floor : ∀ {R} (o : PureObs [] R) {rs Γ A} {c : Ctx R Γ A} {s m p}
      → Path (load o) rs ⟨ c , s , m , p ⟩ → Busy m → Lo (plug c s) (after p)
floor o pth = floored-path o [] (λ _ h → ⊥-elim (none-pend h)) pth
