{-# OPTIONS --guardedness #-}

-- A NODE'S RUN IN ORDER, WHAT IT LEAVES RUNNING TRAILING IT, node by
-- node, in the environment its connects give it.  A frame of one child
-- passes its child's shape as it is; a tape, an of, a joiner, a take, a
-- merge, a connect and a run read through its tail are the leaves.
--
-- A body fed the rest past a source's skips is a body of the stepped
-- tree, read in its own environment (`adequacy.Engine.FedWalk.fed-trail`).
module adequacy.Engine.Trails where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _ʳ++_)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (tt)

open import denotation.MonotonicList.Events using (Events∞; ix)
open import denotation.Unfold using (NEnv; stateᴺ; idleᶜ; restᶜ)
open import operation.PureObservable using (module Machine)
open Machine using (St; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS; Ctx; top; inMap; inScan; inCut; inLn;
  inTake; inOuter; inLanes; inSrc; inBody; plug; cs; CS; _⊕_)
open import adequacy.Engine.Meaning using (gh; envAt; srcG; srcState; subOr)
open import adequacy.Engine.Head using (Frag)
open import adequacy.Placed.Order using (Ordered; Steady; Every; Headed; ordered-map; ordered-scan; steady-map; steady-scan)
open import adequacy.Placed.Keys using (every-map; every-scan)
open import adequacy.Placed.Trail using (Trailing; trail-idle; trail-map; trail-scan)
open Events∞

------------------------------------------------------------------------
-- Shapes

-- A run in order, steady and headed, what it leaves running trailing it.
Shape : ∀ {A} → Events∞ A → Set
Shape σ = ((Ordered (force σ) × Steady (force σ)) × Every Headed (force σ)) × Trailing σ

-- Nothing running.
shape-idle : ∀ {Γ A} (ρ : NEnv Γ) → Shape {A} (stateᴺ idleᶜ ρ)
shape-idle ρ = ((record { ordered = tt } , record { steady = tt }) , record { every = tt }) , trail-idle _ tt

postulate
  -- A SOURCE SUBSCRIBED AT ITS BODY'S MARK, fresh.
  shape-sub : ∀ {R Γ X B} (e : Ctx R Γ B) cl sl sa p as ow r en (o : St Γ X) (b : St (X ∷ Γ) B)
            → Frag (plug e (connS (cs cl sl sa (just p) as ow r en) o b))
            → Shape (stateᴺ (subOr (p ⊕ (ix 1 ∷ [])) o) (envAt e))
  -- A RUN READ THROUGH ITS TAIL keeps its shape.
  shape-rest : ∀ {Γ A} (s : St Γ A) (ρ : NEnv Γ) → Shape (stateᴺ (gh s) ρ) → Shape (stateᴺ (restᶜ {B = A} (gh s)) ρ)
  -- A TAPE MID-PLAY, an of part-way through.
  shape-cold : ∀ {R Γ A} (e : Ctx R Γ A) b l → Frag (plug e (coldS b l)) → ∀ (ρ : NEnv Γ) → Shape (stateᴺ (gh (coldS b l)) ρ)
  shape-of   : ∀ {R Γ A} (e : Ctx R Γ A) i p xs → Frag (plug e (ofS i p xs)) → ∀ (ρ : NEnv Γ) → Shape (stateᴺ (gh (ofS i p xs)) ρ)
  -- A JOINER, its feed then its source's run rejoined.
  --
  -- RECOVERY: git show 74865a1a:agda-impl/adequacy/Engine/Trails.agda restores `envAt-sorted`, each source of a hole's environment in order, over a leaf for an ended source's end
  shape-join : ∀ {R Γ A} (e : Ctx R Γ A) j g y ib → Frag (plug e (joinS j g y ib))
             → Shape (stateᴺ (gh (joinS j g y ib)) (envAt e))
  -- A TAKEWHILE, owing or not.
  shape-take : ∀ {R Γ A} (e : Ctx R Γ A) i p w (s : St Γ A) → Frag (plug e (takeS i p w s))
             → Shape (stateᴺ (gh s) (envAt e)) → Shape (stateᴺ (gh (takeS i p w s)) (envAt e))
  -- A MERGE of its outer's run and its lanes'.
  shape-flat : ∀ {R Γ A C} (e : Ctx R Γ C) op (f : A → _) dn n qs (s : St Γ A) (ls : List (St Γ C))
             → Frag (plug e (flatS op f dn n qs s ls))
             → Shape (stateᴺ (gh s) (envAt e)) → All (λ l → Shape (stateᴺ (gh l) (envAt e))) ls
             → Shape (stateᴺ (gh (flatS op f dn n qs s ls)) (envAt e))
  -- A CONNECT, its body beside its source.
  shape-conn : ∀ {R Γ X B} (e : Ctx R Γ B) k (o : St Γ X) (b : St (X ∷ Γ) B) → Frag (plug e (connS k o b))
             → Shape (srcState (srcG k o) (envAt e)) → Shape (stateᴺ (gh b) (envAt (inBody k o e)))
             → Shape (stateᴺ (gh (connS k o b)) (envAt e))

------------------------------------------------------------------------
-- The walk

mutual
  shape-st : ∀ {R Γ A} (e : Ctx R Γ A) (s : St Γ A) → Frag (plug e s) → Shape (stateᴺ (gh s) (envAt e))
  shape-st e (pend o)        fs = shape-idle (envAt e)
  shape-st e (coldS b l)     fs = shape-cold e b l fs (envAt e)
  shape-st e (ofS i p xs)    fs = shape-of e i p xs fs (envAt e)
  shape-st e doneS           fs = shape-idle (envAt e)
  shape-st e (mapS f s)      fs with shape-st (inMap f e) s fs
  ... | ((o , st) , ev) , tr = ((ordered-map f _ o , steady-map f _ st) , every-map f _ ev) , trail-map f _ _ tr
  shape-st e (scanS f z s)   fs with shape-st (inScan f z e) s fs
  ... | ((o , st) , ev) , tr = ((ordered-scan f z _ o , steady-scan f z _ st) , every-scan f z _ ev) , trail-scan f z _ _ tr
  shape-st e (cutS true a s)  fs = shape-st (inCut true a e) s fs
  shape-st e (cutS false a s) fs = shape-rest s (envAt e) (shape-st (inCut false a e) s fs)
  shape-st e (lnS b s)       fs = shape-st (inLn b e) s fs
  shape-st e (takeS i p w s) fs = shape-take e i p w s fs (shape-st (inTake i p w e) s fs)
  shape-st e (flatS op f dn n qs s ls) fs =
    shape-flat e op f dn n qs s ls fs (shape-st (inOuter op f dn n qs ls e) s fs) (shape-lanes e op f dn n qs s [] ls fs)
  shape-st e (connS k o b)   fs = shape-conn e k o b fs (shape-src e k o b fs) (shape-st (inBody k o e) b fs)
  shape-st e (joinS j g y ib) fs = shape-join e j g y ib fs

  -- Each lane of a merge, those before it passed.
  shape-lanes : ∀ {R Γ A C} (e : Ctx R Γ C) op (f : A → _) dn n qs (s : St Γ A) (pre post : List (St Γ C))
              → Frag (plug e (flatS op f dn n qs s (pre ʳ++ post))) → All (λ l → Shape (stateᴺ (gh l) (envAt e))) post
  shape-lanes e op f dn n qs s pre []         fs = []ᴬ
  shape-lanes e op f dn n qs s pre (l ∷ post) fs =
    shape-st (inLanes op f dn n qs s pre post e) l fs ∷ᴬ shape-lanes e op f dn n qs s (l ∷ pre) post fs

  -- A connect's source, subscribed at its body's mark, running, or ended.
  shape-src : ∀ {R Γ X B} (e : Ctx R Γ B) k (o : St Γ X) (b : St (X ∷ Γ) B) → Frag (plug e (connS k o b))
            → Shape (srcState (srcG k o) (envAt e))
  shape-src e (cs cl sl sa (just p) as ow r en) o b fs = shape-sub e cl sl sa p as ow r en o b fs
  shape-src e (cs false sl sa nothing as ow r en) o b fs = shape-st (inSrc (cs false sl sa nothing as ow r en) b e) o fs
  shape-src e (cs true sl sa nothing as ow r en) o b fs =
    shape-rest o (envAt e) (shape-st (inSrc (cs true sl sa nothing as ow r en) b e) o fs)
