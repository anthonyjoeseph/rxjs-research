{-# OPTIONS --guardedness #-}

-- A NODE'S RUN IN ORDER, WHAT IT LEAVES RUNNING TRAILING IT, node by
-- node, in the environment its connects give it or in one thinned from
-- it: each source's run with skips erased, or past its leading skips.  A
-- frame of one child passes its child's shape as it is; a tape, an of, a
-- joiner, a take, a merge, a connect and a run read through its tail are
-- the leaves.
--
-- The stepped environment is sorted because each source in it runs in
-- order (`envAt-sorted`), so one walk serves a source in its own
-- environment and a source fed the rest past an outer source's skips.
module adequacy.Engine.Trails where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _ʳ++_)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Unit using (tt)

open import denotation.MonotonicList.Events using (Events; Events∞; ix; end)
open import denotation.Unfold using (NEnv; stateᴺ; idleᶜ; restᶜ)
open import operation.PureObservable using (module Machine)
open Machine using (St; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS; Ctx; top; inMap; inScan; inCut; inLn;
  inTake; inOuter; inLanes; inSrc; inBody; plug; cs; CS; _⊕_)
open import adequacy.Engine.Meaning using (gh; envAt; srcRun; srcG; srcState; subOr)
open import adequacy.Engine.Head using (Frag)
open import adequacy.Engine.Thin using (Thin; Thinᴱ; thinᴱ-refl)
open import adequacy.Placed.Order using (Ordered; Steady; Every; Headed; Sorted; ordered-map; ordered-scan; steady-map; steady-scan)
open import adequacy.Placed.Keys using (every-map; every-scan)
open import adequacy.Placed.Trail using (Trailing; trail-idle; trail-map; trail-scan)
open Events∞

------------------------------------------------------------------------
-- Shapes and thinned environments

-- A run in order, steady and headed, what it leaves running trailing it.
Shape : ∀ {A} → Events∞ A → Set
Shape σ = ((Ordered (force σ) × Steady (force σ)) × Every Headed (force σ)) × Trailing σ

-- Nothing running.
shape-idle : ∀ {Γ A} (ρ : NEnv Γ) → Shape {A} (stateᴺ idleᶜ ρ)
shape-idle ρ = ((record { ordered = tt } , record { steady = tt }) , record { every = tt }) , trail-idle _ tt

-- A sorted environment, a run in order on top.
sorted-cons : ∀ {Γ X} {e : Events X} {ρ : NEnv Γ} → (Ordered e × Steady e) × Every Headed e → Sorted ρ → Sorted (e ∷ᴬ ρ)
sorted-cons (os , ev) so = os , ev , so

postulate
  -- A SORTED ENVIRONMENT THINNED is sorted.
  sorted-thin : ∀ {Γ} {ρ ρ′ : NEnv Γ} → Sorted ρ → Thinᴱ ρ ρ′ → Sorted ρ′
  -- A SOURCE'S RUN IN A THINNED ENVIRONMENT is its run there thinned.
  thin-src : ∀ {R Γ X B} (e : Ctx R Γ B) k (o : St Γ X) (b : St (X ∷ Γ) B) → Frag (plug e (connS k o b))
           → ∀ {ρ} → Thinᴱ (envAt e) ρ → Thin (srcRun (srcG k o) (envAt e)) (srcRun (srcG k o) ρ)
  -- A SOURCE ENDED has run in order, its end headed.
  ended-sorted : ∀ {R Γ X B} (e : Ctx R Γ B) sl sa as ow r en (o : St Γ X) (b : St (X ∷ Γ) B)
               → Frag (plug e (connS (cs true sl sa nothing as ow r en) o b))
               → (Ordered (end {X} en) × Steady (end {X} en)) × Every Headed (end {X} en)
  -- A SOURCE SUBSCRIBED AT ITS BODY'S MARK, fresh.
  shape-sub : ∀ {R Γ X B} (e : Ctx R Γ B) cl sl sa p as ow r en (o : St Γ X) (b : St (X ∷ Γ) B)
            → Frag (plug e (connS (cs cl sl sa (just p) as ow r en) o b))
            → ∀ {ρ} → Thinᴱ (envAt e) ρ → Sorted ρ → Shape (stateᴺ (subOr (p ⊕ (ix 1 ∷ [])) o) ρ)
  -- A RUN READ THROUGH ITS TAIL keeps its shape.
  shape-rest : ∀ {Γ A} (s : St Γ A) (ρ : NEnv Γ) → Shape (stateᴺ (gh s) ρ) → Shape (stateᴺ (restᶜ {B = A} (gh s)) ρ)
  -- A TAPE MID-PLAY, an of part-way through.
  shape-cold : ∀ {R Γ A} (e : Ctx R Γ A) b l → Frag (plug e (coldS b l)) → ∀ (ρ : NEnv Γ) → Shape (stateᴺ (gh (coldS b l)) ρ)
  shape-of   : ∀ {R Γ A} (e : Ctx R Γ A) i p xs → Frag (plug e (ofS i p xs)) → ∀ (ρ : NEnv Γ) → Shape (stateᴺ (gh (ofS i p xs)) ρ)
  -- A JOINER, its feed then its source's run rejoined.
  shape-join : ∀ {R Γ A} (e : Ctx R Γ A) j g y ib → Frag (plug e (joinS j g y ib))
             → ∀ {ρ} → Thinᴱ (envAt e) ρ → Sorted ρ → Shape (stateᴺ (gh (joinS j g y ib)) ρ)
  -- A TAKEWHILE, owing or not.
  shape-take : ∀ {R Γ A} (e : Ctx R Γ A) i p w (s : St Γ A) → Frag (plug e (takeS i p w s))
             → ∀ {ρ} → Thinᴱ (envAt e) ρ → Sorted ρ → Shape (stateᴺ (gh s) ρ) → Shape (stateᴺ (gh (takeS i p w s)) ρ)
  -- A MERGE of its outer's run and its lanes'.
  shape-flat : ∀ {R Γ A C} (e : Ctx R Γ C) op (f : A → _) dn n qs (s : St Γ A) (ls : List (St Γ C))
             → Frag (plug e (flatS op f dn n qs s ls))
             → ∀ {ρ} → Thinᴱ (envAt e) ρ → Sorted ρ → Shape (stateᴺ (gh s) ρ) → All (λ l → Shape (stateᴺ (gh l) ρ)) ls
             → Shape (stateᴺ (gh (flatS op f dn n qs s ls)) ρ)
  -- A CONNECT, its body beside its source.
  shape-conn : ∀ {R Γ X B} (e : Ctx R Γ B) k (o : St Γ X) (b : St (X ∷ Γ) B) → Frag (plug e (connS k o b))
             → ∀ {ρ} → Thinᴱ (envAt e) ρ → Sorted ρ → Shape (srcState (srcG k o) ρ) → Shape (stateᴺ (gh b) (srcRun (srcG k o) ρ ∷ᴬ ρ))
             → Shape (stateᴺ (gh (connS k o b)) ρ)

------------------------------------------------------------------------
-- The walk

mutual
  shape-st : ∀ {R Γ A} (e : Ctx R Γ A) (s : St Γ A) → Frag (plug e s) → ∀ {ρ} → Thinᴱ (envAt e) ρ → Sorted ρ → Shape (stateᴺ (gh s) ρ)
  shape-st e (pend o)        fs {ρ} th so = shape-idle ρ
  shape-st e (coldS b l)     fs {ρ} th so = shape-cold e b l fs ρ
  shape-st e (ofS i p xs)    fs {ρ} th so = shape-of e i p xs fs ρ
  shape-st e doneS           fs {ρ} th so = shape-idle ρ
  shape-st e (mapS f s)      fs th so with shape-st (inMap f e) s fs th so
  ... | ((o , st) , ev) , tr = ((ordered-map f _ o , steady-map f _ st) , every-map f _ ev) , trail-map f _ _ tr
  shape-st e (scanS f z s)   fs th so with shape-st (inScan f z e) s fs th so
  ... | ((o , st) , ev) , tr = ((ordered-scan f z _ o , steady-scan f z _ st) , every-scan f z _ ev) , trail-scan f z _ _ tr
  shape-st e (cutS true a s)  fs th so = shape-st (inCut true a e) s fs th so
  shape-st e (cutS false a s) fs {ρ} th so = shape-rest s ρ (shape-st (inCut false a e) s fs th so)
  shape-st e (lnS b s)       fs th so = shape-st (inLn b e) s fs th so
  shape-st e (takeS i p w s) fs th so = shape-take e i p w s fs th so (shape-st (inTake i p w e) s fs th so)
  shape-st e (flatS op f dn n qs s ls) fs th so =
    shape-flat e op f dn n qs s ls fs th so (shape-st (inOuter op f dn n qs ls e) s fs th so) (shape-lanes e op f dn n qs s [] ls fs th so)
  shape-st e (connS k o b)   fs {ρ} th so =
    shape-conn e k o b fs th so (shape-src e k o b fs th so)
      (shape-st (inBody k o e) b fs (thin-src e k o b fs th , th) (sorted-cons (srcRun-sorted e k o b fs th so) so))
  shape-st e (joinS j g y ib) fs th so = shape-join e j g y ib fs th so

  -- Each lane of a merge, those before it passed.
  shape-lanes : ∀ {R Γ A C} (e : Ctx R Γ C) op (f : A → _) dn n qs (s : St Γ A) (pre post : List (St Γ C))
              → Frag (plug e (flatS op f dn n qs s (pre ʳ++ post)))
              → ∀ {ρ} → Thinᴱ (envAt e) ρ → Sorted ρ → All (λ l → Shape (stateᴺ (gh l) ρ)) post
  shape-lanes e op f dn n qs s pre []         fs th so = []ᴬ
  shape-lanes e op f dn n qs s pre (l ∷ post) fs th so =
    shape-st (inLanes op f dn n qs s pre post e) l fs th so ∷ᴬ shape-lanes e op f dn n qs s (l ∷ pre) post fs th so

  -- A connect's source, subscribed at its body's mark, running, or ended.
  shape-src : ∀ {R Γ X B} (e : Ctx R Γ B) k (o : St Γ X) (b : St (X ∷ Γ) B) → Frag (plug e (connS k o b))
            → ∀ {ρ} → Thinᴱ (envAt e) ρ → Sorted ρ → Shape (srcState (srcG k o) ρ)
  shape-src e (cs cl sl sa (just p) as ow r en) o b fs th so = shape-sub e cl sl sa p as ow r en o b fs th so
  shape-src e (cs false sl sa nothing as ow r en) o b fs th so = shape-st (inSrc (cs false sl sa nothing as ow r en) b e) o fs th so
  shape-src e (cs true sl sa nothing as ow r en) o b fs {ρ} th so =
    shape-rest o ρ (shape-st (inSrc (cs true sl sa nothing as ow r en) b e) o fs th so)

  -- What a connect's body is fed: its source's run, in order.
  srcRun-sorted : ∀ {R Γ X B} (e : Ctx R Γ B) k (o : St Γ X) (b : St (X ∷ Γ) B) → Frag (plug e (connS k o b))
                → ∀ {ρ} → Thinᴱ (envAt e) ρ → Sorted ρ → (Ordered (srcRun (srcG k o) ρ) × Steady (srcRun (srcG k o) ρ)) × Every Headed (srcRun (srcG k o) ρ)
  srcRun-sorted e k@(cs cl sl sa (just p) as ow r en) o b fs th so = proj₁ (shape-src e k o b fs th so)
  srcRun-sorted e k@(cs false sl sa nothing as ow r en) o b fs th so = proj₁ (shape-src e k o b fs th so)
  srcRun-sorted e (cs true sl sa nothing as ow r en) o b fs th so = ended-sorted e sl sa as ow r en o b fs

-- The environment a hole's connects give it is sorted.
envAt-sorted : ∀ {R Γ A} (c : Ctx R Γ A) (s : St Γ A) → Frag (plug c s) → Sorted (envAt c)
envAt-sorted top                               s fs = tt
envAt-sorted (inMap f c)                       s fs = envAt-sorted c (mapS f s) fs
envAt-sorted (inScan f z c)                    s fs = envAt-sorted c (scanS f z s) fs
envAt-sorted (inCut l a c)                     s fs = envAt-sorted c (cutS l a s) fs
envAt-sorted (inLn b c)                        s fs = envAt-sorted c (lnS b s) fs
envAt-sorted (inTake i p w c)                  s fs = envAt-sorted c (takeS i p w s) fs
envAt-sorted (inOuter op f d n q ls c)         s fs = envAt-sorted c (flatS op f d n q s ls) fs
envAt-sorted (inLanes op f d n q o pre post c) s fs = envAt-sorted c (flatS op f d n q o (pre ʳ++ s ∷ post)) fs
envAt-sorted (inSrc k b c)                     s fs = envAt-sorted c (connS k s b) fs
envAt-sorted (inBody k o c)                    s fs =
  sorted-cons (srcRun-sorted c k o s fs (thinᴱ-refl (envAt c)) so) so
  where so = envAt-sorted c (connS k o s) fs
