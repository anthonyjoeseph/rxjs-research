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
open import Data.Product using (_×_; _,_; proj₁)
open import Tree using (Obs)
open import denotation.MonotonicList.Events using (Events; Timeline)
open import Data.Unit using (tt)

open import denotation.MonotonicList.Events using (Events∞; ix)
open import denotation.Unfold using (NEnv; stateᴺ; idleᶜ; restᶜ; subscribe)
open import operation.PureObservable using (module Machine)
open Machine using (St; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS; Ctx; top; inMap; inScan; inCut; inLn;
  inTake; inOuter; inLanes; inSrc; inBody; plug; cs; CS; _⊕_)
open import adequacy.Engine.Meaning using (gh; envAt; srcG; srcRun; srcState; subOr)
open import adequacy.Engine.Head using (Frag)
open import adequacy.Placed.Order using (Alienᴱ; Ordered; Sorted; Steady; Every; Headed; ordered-map; ordered-scan; steady-map; steady-scan)
open import adequacy.Placed using (ordered-sub; steady-sub)
open import adequacy.Placed.Keys using (every-map; every-scan)
open import adequacy.Placed.Trail using (Trailing; trail-idle; trail-map; trail-scan)
open import adequacy.Placed.Rising using (module Reach; headed-sub; headedRules; ordered-take; steady-take)
open import adequacy.Placed.FlatAfter using (trail-take)
open import operation.AbstractObservable using (free; cpAt; cutAt; overAt)
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
  -- A SOURCE SUBSCRIBED AT ITS BODY'S MARK is subscribed under a head,
  -- where no source of its environment has been.
  sub-headed : ∀ {R Γ X B} (e : Ctx R Γ B) cl sl sa p as ow r en (o : St Γ X) (b : St (X ∷ Γ) B)
             → Frag (plug e (connS (cs cl sl sa (just p) as ow r en) o b)) → Headed (p ⊕ (ix 1 ∷ []))
  sub-alien  : ∀ {R Γ X B} (e : Ctx R Γ B) cl sl sa p as ow r en (o : St Γ X) (b : St (X ∷ Γ) B)
             → Frag (plug e (connS (cs cl sl sa (just p) as ow r en) o b)) → Alienᴱ (p ⊕ (ix 1 ∷ [])) (envAt e)
  -- A SUBSCRIPTION'S CUTS TRAIL ITS RUN, finite or not: a limit over
  -- `adequacy.Placed.trailing-subᶠ` once a truncation's cut agrees as its
  -- run does (`adequacy.Finite.trunc-agree`).
  trailing-sub : ∀ {Γ A} (o : Obs Timeline Γ A) p (ρ : NEnv Γ) → Headed p → Sorted ρ → Alienᴱ p ρ
               → Trailing (stateᴺ (subscribe o p) ρ)
  -- AN ENDED SOURCE ended under a head.
  ended-headed : ∀ {R Γ X B} (e : Ctx R Γ B) sl sa as ow r en (o : St Γ X) (b : St (X ∷ Γ) B)
               → Frag (plug e (connS (cs true sl sa nothing as ow r en) o b)) → Headed en
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
  -- A TAKEWHILE OWING ITS COMPLETION, its end past its source's.
  shape-ending : ∀ {R Γ A} (e : Ctx R Γ A) i p k (s : St Γ A) → Frag (plug e (takeS i p (cpAt k) s))
               → Shape (stateᴺ (gh s) (envAt e)) → Shape (stateᴺ (gh (takeS i p (cpAt k) s)) (envAt e))
  -- A MERGE of its outer's run and its lanes'.
  shape-flat : ∀ {R Γ A C} (e : Ctx R Γ C) op (f : A → _) dn n qs (s : St Γ A) (ls : List (St Γ C))
             → Frag (plug e (flatS op f dn n qs s ls))
             → Shape (stateᴺ (gh s) (envAt e)) → All (λ l → Shape (stateᴺ (gh l) (envAt e))) ls
             → Shape (stateᴺ (gh (flatS op f dn n qs s ls)) (envAt e))
  -- A CONNECT, its body beside its source.
  shape-conn : ∀ {R Γ X B} (e : Ctx R Γ B) k (o : St Γ X) (b : St (X ∷ Γ) B) → Frag (plug e (connS k o b))
             → Shape (srcState (srcG k o) (envAt e)) → Shape (stateᴺ (gh b) (envAt (inBody k o e)))
             → Shape (stateᴺ (gh (connS k o b)) (envAt e))

-- A TAKEWHILE: owing nothing, its source's run cut at the first value
-- failing; cut or over, its source's tail.
shape-take : ∀ {R Γ A} (e : Ctx R Γ A) i p w (s : St Γ A) → Frag (plug e (takeS i p w s))
           → Shape (stateᴺ (gh s) (envAt e)) → Shape (stateᴺ (gh (takeS i p w s)) (envAt e))
shape-take e i p free       s fs (((o , st) , ev) , tr) =
  ((ordered-take i p _ o , steady-take i p _ st) , Reach.every-take headedRules i p _ ev) , trail-take i p _ _ o st tr
shape-take e i p (cpAt k)   s fs sh = shape-ending e i p k s fs sh
shape-take e i p (cutAt k)  s fs sh = shape-rest s (envAt e) sh
shape-take e i p (overAt k) s fs sh = shape-rest s (envAt e) sh

------------------------------------------------------------------------
-- The walk

sorted-cons : ∀ {Γ X} {e : Events X} {ρ : NEnv Γ} → (Ordered e × Steady e) × Every Headed e → Sorted ρ → Sorted (e ∷ᴬ ρ)
sorted-cons (os , ev) so = os , ev , so

-- Read in an environment in order.
private module Walk where
 mutual
  shape-st : ∀ {R Γ A} (e : Ctx R Γ A) (s : St Γ A) → Frag (plug e s) → Sorted (envAt e) → Shape (stateᴺ (gh s) (envAt e))
  shape-st e (pend o)        fs so = shape-idle (envAt e)
  shape-st e (coldS b l)     fs so = shape-cold e b l fs (envAt e)
  shape-st e (ofS i p xs)    fs so = shape-of e i p xs fs (envAt e)
  shape-st e doneS           fs so = shape-idle (envAt e)
  shape-st e (mapS f s)      fs so with shape-st (inMap f e) s fs so
  ... | ((o , st) , ev) , tr = ((ordered-map f _ o , steady-map f _ st) , every-map f _ ev) , trail-map f _ _ tr
  shape-st e (scanS f z s)   fs so with shape-st (inScan f z e) s fs so
  ... | ((o , st) , ev) , tr = ((ordered-scan f z _ o , steady-scan f z _ st) , every-scan f z _ ev) , trail-scan f z _ _ tr
  shape-st e (cutS true a s)  fs so = shape-st (inCut true a e) s fs so
  shape-st e (cutS false a s) fs so = shape-rest s (envAt e) (shape-st (inCut false a e) s fs so)
  shape-st e (lnS b s)       fs so = shape-st (inLn b e) s fs so
  shape-st e (takeS i p w s) fs so = shape-take e i p w s fs (shape-st (inTake i p w e) s fs so)
  shape-st e (flatS op f dn n qs s ls) fs so =
    shape-flat e op f dn n qs s ls fs (shape-st (inOuter op f dn n qs ls e) s fs so) (shape-lanes e op f dn n qs s [] ls fs so)
  shape-st e (connS k o b)   fs so =
    shape-conn e k o b fs (shape-src e k o b fs so) (shape-st (inBody k o e) b fs (sorted-cons (src-sorted e k o b fs (shape-src e k o b fs so)) so))
  shape-st e (joinS j g y ib) fs so = shape-join e j g y ib fs

  -- Each lane of a merge, those before it passed.
  shape-lanes : ∀ {R Γ A C} (e : Ctx R Γ C) op (f : A → _) dn n qs (s : St Γ A) (pre post : List (St Γ C))
              → Frag (plug e (flatS op f dn n qs s (pre ʳ++ post))) → Sorted (envAt e) → All (λ l → Shape (stateᴺ (gh l) (envAt e))) post
  shape-lanes e op f dn n qs s pre []         fs so = []ᴬ
  shape-lanes e op f dn n qs s pre (l ∷ post) fs so =
    shape-st (inLanes op f dn n qs s pre post e) l fs so ∷ᴬ shape-lanes e op f dn n qs s (l ∷ pre) post fs so

  -- A connect's source, subscribed at its body's mark, running, or ended.
  shape-src : ∀ {R Γ X B} (e : Ctx R Γ B) k (o : St Γ X) (b : St (X ∷ Γ) B) → Frag (plug e (connS k o b)) → Sorted (envAt e)
            → Shape (srcState (srcG k o) (envAt e))
  shape-src e (cs cl sl sa (just p) as ow r en) o b fs so = shape-sub e cl sl sa p as ow r en o b fs so
  shape-src e (cs false sl sa nothing as ow r en) o b fs so = shape-st (inSrc (cs false sl sa nothing as ow r en) b e) o fs so
  shape-src e (cs true sl sa nothing as ow r en) o b fs so =
    shape-rest o (envAt e) (shape-st (inSrc (cs true sl sa nothing as ow r en) b e) o fs so)

  -- A source subscribed at its body's mark: fresh, by the subscription's
  -- own order; else as it runs.
  shape-sub : ∀ {R Γ X B} (e : Ctx R Γ B) cl sl sa p as ow r en (o : St Γ X) (b : St (X ∷ Γ) B)
            → Frag (plug e (connS (cs cl sl sa (just p) as ow r en) o b)) → Sorted (envAt e)
            → Shape (stateᴺ (subOr (p ⊕ (ix 1 ∷ [])) o) (envAt e))
  shape-sub e cl sl sa p as ow r en (pend o) b fs so =
    ((ordered-sub o q (envAt e) hq so al , steady-sub o q (envAt e) hq so al) , headed-sub o q (envAt e) hq so) , trailing-sub o q (envAt e) hq so al
    where q  = p ⊕ (ix 1 ∷ [])
          hq = sub-headed e cl sl sa p as ow r en (pend o) b fs
          al = sub-alien e cl sl sa p as ow r en (pend o) b fs
  shape-sub e cl sl sa p as ow r en o@(coldS _ _)   b fs so = shape-st (inSrc (cs cl sl sa (just p) as ow r en) b e) o fs so
  shape-sub e cl sl sa p as ow r en o@(ofS _ _ _)   b fs so = shape-st (inSrc (cs cl sl sa (just p) as ow r en) b e) o fs so
  shape-sub e cl sl sa p as ow r en o@doneS         b fs so = shape-st (inSrc (cs cl sl sa (just p) as ow r en) b e) o fs so
  shape-sub e cl sl sa p as ow r en o@(mapS _ _)    b fs so = shape-st (inSrc (cs cl sl sa (just p) as ow r en) b e) o fs so
  shape-sub e cl sl sa p as ow r en o@(scanS _ _ _) b fs so = shape-st (inSrc (cs cl sl sa (just p) as ow r en) b e) o fs so
  shape-sub e cl sl sa p as ow r en o@(cutS _ _ _)  b fs so = shape-st (inSrc (cs cl sl sa (just p) as ow r en) b e) o fs so
  shape-sub e cl sl sa p as ow r en o@(lnS _ _)     b fs so = shape-st (inSrc (cs cl sl sa (just p) as ow r en) b e) o fs so
  shape-sub e cl sl sa p as ow r en o@(takeS _ _ _ _) b fs so = shape-st (inSrc (cs cl sl sa (just p) as ow r en) b e) o fs so
  shape-sub e cl sl sa p as ow r en o@(flatS _ _ _ _ _ _ _) b fs so = shape-st (inSrc (cs cl sl sa (just p) as ow r en) b e) o fs so
  shape-sub e cl sl sa p as ow r en o@(connS _ _ _) b fs so = shape-st (inSrc (cs cl sl sa (just p) as ow r en) b e) o fs so
  shape-sub e cl sl sa p as ow r en o@(joinS _ _ _ _) b fs so = shape-st (inSrc (cs cl sl sa (just p) as ow r en) b e) o fs so

  -- What a connect's source has run, in order and headed.
  src-sorted : ∀ {R Γ X B} (e : Ctx R Γ B) k (o : St Γ X) (b : St (X ∷ Γ) B) → Frag (plug e (connS k o b))
             → Shape (srcState (srcG k o) (envAt e))
             → (Ordered (srcRun (srcG k o) (envAt e)) × Steady (srcRun (srcG k o) (envAt e))) × Every Headed (srcRun (srcG k o) (envAt e))
  src-sorted e (cs cl sl sa (just p) as ow r en) o b fs sh = proj₁ sh
  src-sorted e (cs false sl sa nothing as ow r en) o b fs sh = proj₁ sh
  src-sorted e (cs true sl sa nothing as ow r en) o b fs sh =
    (record { ordered = tt } , record { steady = tt }) , record { every = ended-headed e sl sa as ow r en o b fs }

-- The environment a hole's connects give it is in order.
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
  sorted-cons (Walk.src-sorted c k o s fs (Walk.shape-src c k o s fs so)) so
  where so = envAt-sorted c (connS k o s) fs

-- A node, in the environment its connects give it.
shape-st : ∀ {R Γ A} (e : Ctx R Γ A) (s : St Γ A) → Frag (plug e s) → Shape (stateᴺ (gh s) (envAt e))
shape-st e s fs = Walk.shape-st e s fs (envAt-sorted e s fs)

-- A connect's source, likewise.
shape-src : ∀ {R Γ X B} (e : Ctx R Γ B) k (o : St Γ X) (b : St (X ∷ Γ) B) → Frag (plug e (connS k o b))
          → Shape (srcState (srcG k o) (envAt e))
shape-src e k o b fs = Walk.shape-src e k o b fs (envAt-sorted e (connS k o b) fs)
