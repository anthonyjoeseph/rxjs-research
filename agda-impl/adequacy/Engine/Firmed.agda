{-# OPTIONS --guardedness #-}

-- THE GHOST IS FIRM WHERE IT IS KEYED: of a tree whose positions are
-- kept (`Keys`) and each of whose live joiners an ended connect told
-- (`Toldˢ`), the scope (`Gh`).  A ghost read through the ended connects
-- in scope is firm (`firm-gh`): every joiner left untold joins a source
-- still running (`Unshut`), alien to it as its keys say; every pool
-- rests; a source yet to subscribe is placed, by its subscription's own
-- keys, and stays placed told its sources' ends (`firm-sub`).  A body
-- reads its source's run where the keys read the unshut one: alike, its
-- sources having ended where the shuts say (`Scene`).
module adequacy.Engine.Firmed where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_]; map)
open import Data.List.Properties using (map-++)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; lookup) renaming (_∷_ to _∷ᴬ_; [] to []ᴬ)
open import Data.Maybe using (Maybe; just; nothing; is-just) renaming (map to mapᴹ)
open import Data.Nat using (zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym; trans)

import Tree as T
open import Tree using (Obs)
open import denotation.MonotonicList using (Agree; agree-refl; agree-sym; agree-trans)
open import denotation.MonotonicList.Events using (Pos; Timeline; From; done; quiet; at; end; ix; timelineAt)
open import denotation.NonExpansive using (Agreeˢ)
open import denotation.Unfold using (NEnv; Node; meaning; subscribe; startᶜ; idleᶜ; ofᶜ; mapᶜ; scanᶜ; restᶜ; restsᶜ; joinᶜ;
  connectᶜ; deferᶜ; takeWhileᶜ; Source; live; ended; shut; told; same?)
open import operation.PureObservable using (Tape; play; ending; over; module Machine)
open Machine using (St; CS; cs; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS; top; _⊕_)
open import operation.AbstractObservable using (free; cpAt; cutAt; overAt)
open import adequacy.Sane using (Mode; runs; Rested) renaming (over to overᵐ; Told to Toldᵐ)
open import adequacy.Stepper using (Firm; Firmᴸ; Firmᴹ)
open import adequacy.Stepper.Past using (Joined; _≃_; alike)
open import adequacy.Stepper.Parts using (shut-alikeⁱ)
open import adequacy.Stepper.Fed using (placed-shut)
open import adequacy.Env using (Same; same-cons; meaning-same; nagree-refl; lookup-ne; sorted-agree; everyᴱ-agree)
open import adequacy.Placed using (placed-sub)
open import adequacy.Placed.Order using (Placed; Sorted)
open import adequacy.Placed.Keys using (every-≈)
open import adequacy.Engine.Meaning using (gh; tape; taken; doneG; outerG; poolG; lanesL; liveL; deadL; lane; subOr; bodyG; vals; endOf; srcG; srcRun)
open import adequacy.Engine.Head using (tape-still)
open import adequacy.Engine.Shuts using (Shuts; none; shutAt; upˢ; snocˢ; closeOf; shutAll; shutAllˢ; Untold; Told; Toldˢ; Toldᴸ;
  shut-still; shut-comm; shut-union; shut-flat; shut-rest; shut-rests; shut-taken; shut-done; shut-conn; shut-snoc; told-shut; untold)
open import adequacy.Engine.Keys using (Keys; Keyed; KeyedL; Joins; ConnAt; SubKeys)
open import adequacy.Engine.Trails using (sorted-cons; src-sorted; src-shape)
open import adequacy.Engine.Scope using (Ended; ended-up; ended-snoc; ended-close; modeᴳ; GhE; GhEᴸ; Gh; Src; Outs)

open _≃_
open Agreeˢ using (nowˢ)

------------------------------------------------------------------------
-- The scope a ghost is read in

-- Every joiner the shuts leave untold joins a connect still running.
Unshut : ∀ {Γ} → All (λ _ → Mode) Γ → Shuts Γ → Set₁
Unshut {Γ} ν V = ∀ {X} (x : X ∈ Γ) → Untold V x → Toldᵐ (lookup ν x) nothing

untold-up : ∀ {Γ X Y} (V : Shuts Γ) (x : Y ∈ Γ) → Untold (upˢ {X = X} V) (there x) → Untold V x
untold-up none           x u       = tt
untold-up (shutAt i c V) x (n , u) = n , untold-up V x u

untold-snoc : ∀ {Γ X Y} (V : Shuts Γ) (i : X ∈ Γ) c (x : Y ∈ Γ) → Untold (snocˢ V i c) x → Untold V x
untold-snoc none           i c x u       = tt
untold-snoc (shutAt j d V) i c x (n , u) = n , untold-snoc V i c x u

told-snoc : ∀ {Γ X} (V : Shuts (X ∷ Γ)) c → Untold (snocˢ V (here refl) c) (here refl) → ⊥
told-snoc none           c (() , _)
told-snoc (shutAt j d V) c (_ , u) = told-snoc V c u

unshut-up : ∀ {Γ X} {ν : All (λ _ → Mode) Γ} (V : Shuts Γ) → Unshut ν V → Unshut (runs ∷ᴬ ν) (upˢ {X = X} V)
unshut-up V h (here refl) u = tt
unshut-up V h (there x)   u = h x (untold-up V x u)

unshut-shut : ∀ {Γ X} {ν : All (λ _ → Mode) Γ} (V : Shuts Γ) c → Unshut ν V → Unshut (overᵐ ∷ᴬ ν) (snocˢ (upˢ {X = X} V) (here refl) c)
unshut-shut V c h (here refl) u = ⊥-elim (told-snoc (upˢ V) c u)
unshut-shut V c h (there x)   u = h x (untold-up V x (untold-snoc (upˢ V) (here refl) c (there x) u))

unshut-src : ∀ {Γ X} {ν : All (λ _ → Mode) Γ} (V : Shuts Γ) (g : Source Γ X) → Unshut ν V → Unshut (modeᴳ g ∷ᴬ ν) (closeOf g (upˢ V))
unshut-src V (live n)                    h = unshut-up V h
unshut-src V (ended e t)                   h = unshut-shut V e h

ended-same : ∀ {Γ} (V : Shuts Γ) {ρ ρ′ : NEnv Γ} → Same ρ ρ′ → Ended V ρ → Ended V ρ′
ended-same none           S t       = tt
ended-same (shutAt i c V) S (a , t) = alike (λ d → agree-trans (agree-sym (lookup-ne (S d) i)) (agreeing a d)) , ended-same V S t

-- A node read through ended connects runs as it does.
meaning-shut : ∀ {Γ B} (V : Shuts Γ) (n : Node Γ B) {ρ ρ′ : NEnv Γ} → Ended V ρ → Same ρ ρ′ → ∀ m → Agree m (meaning n ρ) (meaning (shutAll V n) ρ′)
meaning-shut none           n     t       S   = meaning-same n S
meaning-shut (shutAt i c V) n {ρ} (a , t) S m =
  agree-trans (meaning-shut V n t (λ d → nagree-refl d ρ) m) (nowˢ (shut-alikeⁱ i c (shutAll V n) a S m))

placed-shuts : ∀ {Γ B} (V : Shuts Γ) (n : Node Γ B) {ρ : NEnv Γ} → Ended V ρ → Placed n ρ → Placed (shutAll V n) ρ
placed-shuts none           n     t       pl = pl
placed-shuts (shutAt i c V) n {ρ} (a , t) pl = placed-shut i c (shutAll V n) a (λ d → nagree-refl d ρ) (placed-shuts V n t pl)

-- The modes, the shuts, the environment the keys read and the one the
-- ghost reads.
record Scene {Γ} (ν : All (λ _ → Mode) Γ) (V : Shuts Γ) (ρ ρ′ : NEnv Γ) : Set₁ where
  constructor scene
  field
    unshut : Unshut ν V
    ends  : Ended V ρ
    alikeᴱ : Same ρ ρ′
    sorted : Sorted ρ
open Scene

scene-live : ∀ {Γ X} {ν : All (λ _ → Mode) Γ} {V : Shuts Γ} {ρ ρ′ : NEnv Γ} (n : Node Γ X) → Scene ν V ρ ρ′ → Sorted (meaning n ρ ∷ᴬ ρ)
           → Scene (runs ∷ᴬ ν) (upˢ V) (meaning n ρ ∷ᴬ ρ) (meaning (shutAll V n) ρ′ ∷ᴬ ρ′)
scene-live {V = V} {ρ} n (scene h t S _) so = scene (unshut-up V h) (ended-up V (meaning n ρ) ρ t) (same-cons (meaning-shut V n t S) S) so

scene-end : ∀ {Γ X} {ν : All (λ _ → Mode) Γ} {V : Shuts Γ} {ρ ρ′ : NEnv Γ} c → Scene ν V ρ ρ′ → Sorted (end {X} c ∷ᴬ ρ)
          → Scene (overᵐ ∷ᴬ ν) (snocˢ (upˢ V) (here refl) c) (end c ∷ᴬ ρ) (end c ∷ᴬ ρ′)
scene-end {V = V} {ρ} c (scene h t S _) so =
  scene (unshut-shut V c h)
        (ended-snoc (upˢ V) (here refl) c (end c ∷ᴬ ρ) (ended-up V (end c) ρ t) (alike (λ d → agree-refl d (end c))))
        (same-cons (λ d → agree-refl d (end c)) S) so

-- A body's scope, read where its source runs.
scene-src : ∀ {Γ X B} {ν : All (λ _ → Mode) Γ} {V : Shuts Γ} {ρ : NEnv Γ} k (o : St Γ X) (b : St (X ∷ Γ) B) → Scene ν V ρ ρ
          → ConnAt k _ _ ρ → Keyed o ρ
          → Scene (modeᴳ (srcG k o) ∷ᴬ ν) (closeOf (srcG k o) (upˢ V)) (srcRun (srcG k o) ρ ∷ᴬ ρ) (srcRun (srcG k o) ρ ∷ᴬ ρ)
scene-src {V = V} {ρ} k o b (scene h t S so) m ko =
  scene (unshut-src V (srcG k o) h)
        (ended-close (srcG k o) ρ (upˢ V) (ended-up V (srcRun (srcG k o) ρ) ρ t))
        (λ d → nagree-refl d _)
        (sorted-cons (src-sorted k o ρ (ConnAt.ends m) (src-shape k o b ρ m ko so)) so)

------------------------------------------------------------------------
-- Nodes the shuts leave firm

firm-still : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} (V : Shuts Γ) (n : Node Γ A) {ρ : NEnv Γ}
           → (∀ {X} (i : X ∈ Γ) c → shut i c n ≡ n) → Firm ν n ρ → Firm ν (shutAll V n) ρ
firm-still {ν = ν} V n {ρ} h f = subst (λ m → Firm ν m ρ) (sym (shut-still V n h)) f

firm-done : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} {ρ : NEnv Γ} m l (n : Node Γ A) → Firm ν n ρ → Firm ν (doneG m l n) ρ
firm-done (just _) l     n f = tt
firm-done nothing  false n f = tt
firm-done nothing  true  n f = f

firm-taken : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} {ρ : NEnv Γ} i q w (n : Node Γ A) → Firm ν n ρ → Firm ν (taken i q w n) ρ
firm-taken i q free       n f = f
firm-taken i q (cpAt p)   n f = tt
firm-taken i q (cutAt p)  n f = tt
firm-taken i q (overAt p) n f = tt

firm-tape : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} {ρ : NEnv Γ} b (l : Tape A) → Firm ν (tape b l) ρ
firm-tape b     (ending e)        = tt
firm-tape true  (play τ u k t fr) = tt
firm-tape false (play τ u k t fr) = tt
firm-tape b     over              = tt

start-shut : ∀ {Γ A X} p (m : From A 0) (i : X ∈ Γ) c → shut i c (startᶜ {Γ} p m) ≡ startᶜ p m
start-shut p done              i c = refl
start-shut p quiet             i c = refl
start-shut p (at zero    le b) i c = refl
start-shut p (at (suc t) le b) i c = refl

firm-start : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} {ρ : NEnv Γ} p (m : From A 0) → Firm ν (startᶜ p m) ρ
firm-start p done              = tt
firm-start p quiet             = tt
firm-start p (at zero    le b) = tt
firm-start p (at (suc t) le b) = tt

rested-rests : ∀ {Γ A B} (ds : List (Node Γ A)) → Rested (restsᶜ {B = B} ds)
rested-rests []       = tt
rested-rests (d ∷ ds) = tt

rested-pool : ∀ {Γ A B} (V : Shuts Γ) d (n : Node Γ A) (ds : List (Node Γ B)) → Rested (shutAll V (poolG d n ds))
rested-pool V false n ds = subst Rested (sym (shut-rests V ds)) (rested-rests (map (shutAll V) ds))
rested-pool V true  n ds = subst Rested (sym (shut-union V (restᶜ n) (restsᶜ ds))) tt

firmᴸ-++ : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} {ρ : NEnv Γ} (xs ys : List (Node Γ A)) → Firmᴸ ν xs ρ → Firmᴸ ν ys ρ → Firmᴸ ν (xs ++ ys) ρ
firmᴸ-++ []       ys fx       fy = fy
firmᴸ-++ (x ∷ xs) ys (f , fx) fy = f , firmᴸ-++ xs ys fx fy

------------------------------------------------------------------------
-- A joiner

-- One shut either leaves a fresh joiner untold or tells it.
shut-one : ∀ {Γ X Y} (i : X ∈ Γ) c (x : Y ∈ Γ) p (m : Maybe (X ≡ Y)) → same? i x ≡ m
         → (is-just (same? i x) ≡ false) ⊎ Σ Pos (λ d → shut i c (joinᶜ x p [] nothing) ≡ joinᶜ x p [] (just d))
shut-one i c x p nothing     w = inj₁ (cong is-just w)
shut-one i c x p (just refl) w = inj₂ (_ , cong (λ k → joinᶜ x p [] (told i c x p nothing k)) w)

shut-join : ∀ {Γ Y} (V : Shuts Γ) (x : Y ∈ Γ) p
          → (Untold V x × shutAll V (joinᶜ x p [] nothing) ≡ joinᶜ x p [] nothing)
          ⊎ Σ Pos (λ d → shutAll V (joinᶜ x p [] nothing) ≡ joinᶜ x p [] (just d))
shut-join none           x p = inj₁ (tt , refl)
shut-join (shutAt i c V) x p with shut-join V x p
... | inj₂ (d , eq) = inj₂ (d , cong (shut i c) eq)
... | inj₁ (u , eq) with shut-one i c x p (same? i x) refl
...   | inj₁ n       = inj₁ ((n , u) , trans (cong (shut i c) eq) (untold i c x p [] n))
...   | inj₂ (d , e) = inj₂ (d , trans (cong (shut i c) eq) e)

joined-at : ∀ {Γ Y} {ν : All (λ _ → Mode) Γ} (V : Shuts Γ) {ρ ρ′ : NEnv Γ} (x : Y ∈ Γ) p xs e → Unshut ν V → Same ρ ρ′
          → Joins x p e ρ → Told V x e → Joined (lookup ν x) p xs e (lookup ρ′ x)
joined-at V x p []      nothing  h S (_ , al) t = h x t , every-≈ _ _ (λ m → lookup-ne (S m) x) al
joined-at V x p []      (just c) h S j        t = tt
joined-at V x p (_ ∷ _) e        h S j        t = tt

firm-join : ∀ {Γ Y} {ν : All (λ _ → Mode) Γ} (V : Shuts Γ) {ρ ρ′ : NEnv Γ} (x : Y ∈ Γ) p xs e → Unshut ν V → Same ρ ρ′
          → Joins x p e ρ → Told V x e → Firm ν (shutAll V (joinᶜ x p xs e)) ρ′
firm-join {ν = ν} V {ρ′ = ρ′} x p xs e h S j t =
  subst (λ m → Firm ν m ρ′) (sym (told-shut V x p xs e t)) (joined-at {ν = ν} V {ρ′ = ρ′} x p xs e h S j t)

------------------------------------------------------------------------
-- A source yet to subscribe

via : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} {ρ : NEnv Γ} {a b : Node Γ A} → a ≡ b → (Placed b ρ → Firm ν b ρ) → Placed a ρ → Firm ν a ρ
via refl f = f

firm-sub : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} (V : Shuts Γ) {ρ : NEnv Γ} (o : Obs Timeline Γ A) p → Unshut ν V
         → Placed (shutAll V (subscribe o p)) ρ → Firm ν (shutAll V (subscribe o p)) ρ
firm-sub {ν = ν} V {ρ} (T.cold c) p h pl = firm-still V _ (start-shut p (timelineAt c p)) (firm-start {ν = ν} {ρ} p (timelineAt c p))
firm-sub V T.empty             p h pl = firm-still V _ (λ i c → refl) tt
firm-sub V (T.of xs)           p h pl = firm-still V _ (λ i c → refl) tt
firm-sub V (T.map f s)         p h pl = via (shut-comm (mapᶜ f) (λ i c n → refl) V (subscribe s p)) (λ q → firm-sub V s p h (proj₂ q)) pl
firm-sub V (T.scan f z s)      p h pl = via (shut-comm (scanᶜ f z) (λ i c n → refl) V (subscribe s p)) (λ q → firm-sub V s p h (proj₂ q)) pl
firm-sub V (T.takeWhile i q s) p h pl =
  via (shut-comm (takeWhileᶜ i q) (λ j c n → refl) V (subscribe s p)) (λ r → firm-sub V s p h (proj₂ r)) pl
firm-sub V (T.flatMap op f s)  p h pl =
  via (shut-flat V op _ (just (subscribe s p)) [] [] idleᶜ)
      (λ q → firm-sub V s p h (proj₁ (proj₂ q)) , tt , subst Rested (sym (shut-still V idleᶜ (λ i c → refl))) tt) pl
firm-sub V (T.connect s b)     p h pl =
  via (shut-conn V _ (subscribe b _) (live (subscribe s _)))
      (λ q → firm-sub (upˢ V) b _ (unshut-up V h) (proj₁ (proj₂ q)) , firm-sub V s _ h (proj₁ (proj₂ (proj₂ q)))) pl
firm-sub V (T.connected x)     p h pl with shut-join V x p
... | inj₁ (u , eq) = via eq (λ q → h x u , proj₂ q) pl
... | inj₂ (d , eq) = via eq (λ _ → tt) pl
firm-sub V (T.defer l)         p h pl = via (shut-still V (deferᶜ l p []) (λ i c → refl)) (λ q → q) pl

------------------------------------------------------------------------
-- The ghost

mutual
  firm-gh : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} {V : Shuts Γ} {ρ ρ′ : NEnv Γ} (s : St Γ A) → Scene ν V ρ ρ′ → Keyed s ρ → Toldˢ V s
          → Firm ν (shutAll V (gh s)) ρ′
  firm-gh {V = V} (pend o)       sc ky t = firm-still V idleᶜ (λ i c → refl) tt
  firm-gh {ν = ν} {V} {ρ′ = ρ′} (coldS b l) sc ky t = firm-still V (tape b l) (tape-still b l) (firm-tape {ν = ν} {ρ′} b l)
  firm-gh {V = V} (ofS i p xs)   sc ky t = firm-still V (ofᶜ p i xs) (λ j c → refl) tt
  firm-gh {V = V} doneS          sc ky t = firm-still V idleᶜ (λ i c → refl) tt
  firm-gh {ν = ν} {V} {ρ′ = ρ′} (mapS f s) sc ky t =
    subst (λ m → Firm ν m ρ′) (sym (shut-comm (mapᶜ f) (λ i c n → refl) V (gh s))) (firm-gh s sc (proj₂ ky) t)
  firm-gh {ν = ν} {V} {ρ′ = ρ′} (scanS f z s) sc ky t =
    subst (λ m → Firm ν m ρ′) (sym (shut-comm (scanᶜ f z) (λ i c n → refl) V (gh s))) (firm-gh s sc (proj₂ ky) t)
  firm-gh (cutS true a s) sc ky t = firm-gh s sc (proj₂ ky) t
  firm-gh {ν = ν} {V} {ρ′ = ρ′} (cutS false a s) sc ky t = subst (λ m → Firm ν m ρ′) (sym (shut-rest V (gh s))) tt
  firm-gh (lnS b s) sc ky t = firm-gh s sc (proj₂ ky) t
  firm-gh {ν = ν} {V} {ρ′ = ρ′} (takeS i q w s) sc ky t =
    subst (λ m → Firm ν m ρ′) (sym (shut-taken V i q w (gh s))) (firm-taken {ν = ν} {ρ′} i q w _ (firm-gh s sc (proj₂ ky) t))
  firm-gh {ν = ν} {V} {ρ′ = ρ′} (flatS op f d n q o ls) sc ky (to , tl) =
    subst (λ m → Firm ν m ρ′) (sym (shut-flat V op (lane f) (outerG d (gh o)) (lanesL ls) q (poolG d (gh o) (deadL ls))))
      (firm-outer d o sc (proj₁ (proj₂ ky)) to , firm-lanes ls sc (proj₂ (proj₂ ky)) tl , rested-pool V d (gh o) (deadL ls))
  firm-gh {ν = ν} {V} {ρ′ = ρ′} (connS (cs cl sl sa ba as ow r en) o b) sc ky t =
    subst (λ m → Firm ν m ρ′) (sym (shut-done V ow sl _))
      (firm-done {ν = ν} {ρ′} ow sl _ (subst (λ m → Firm ν m ρ′) (sym (shut-conn V r _ _)) (firm-conn cl sl sa ba as ow r en o b sc ky t)))
  firm-gh {V = V} (joinS j true x ib) sc ky t =
    firm-join V x j (vals ib) (endOf ib) (unshut sc) (alikeᴱ sc) (proj₁ (proj₁ ky)) t
  firm-gh {V = V} (joinS j false x ib) sc ky t = firm-still V idleᶜ (λ i c → refl) tt

  firm-outer : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} {V : Shuts Γ} {ρ ρ′ : NEnv Γ} d (o : St Γ A) → Scene ν V ρ ρ′ → Keyed o ρ → Toldˢ V o
             → Firmᴹ ν (mapᴹ (shutAll V) (outerG d (gh o))) ρ′
  firm-outer true  o sc ky t = tt
  firm-outer false o sc ky t = firm-gh o sc ky t

  firm-lanes : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} {V : Shuts Γ} {ρ ρ′ : NEnv Γ} (ls : List (St Γ A)) → Scene ν V ρ ρ′ → KeyedL ls ρ → Toldᴸ V ls
             → Firmᴸ ν (map (shutAll V) (lanesL ls)) ρ′
  firm-lanes []       sc ky t = tt
  firm-lanes {ν = ν} {V} {ρ′ = ρ′} (s ∷ ls) sc (ks , kls) (ts , tls) =
    subst (λ zs → Firmᴸ ν zs ρ′) (sym (map-++ (shutAll V) (lanesL ls) (liveL s)))
      (firmᴸ-++ {ν = ν} {ρ′} _ _ (firm-lanes ls sc kls tls) (firm-live s sc ks ts))

  firm-live : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} {V : Shuts Γ} {ρ ρ′ : NEnv Γ} (s : St Γ A) → Scene ν V ρ ρ′ → Keyed s ρ → Toldˢ V s
            → Firmᴸ ν (map (shutAll V) (liveL s)) ρ′
  firm-live (lnS false s)           sc ky t = tt
  firm-live s@(lnS true _)          sc ky t = firm-gh s sc ky t , tt
  firm-live s@(pend _)              sc ky t = firm-gh s sc ky t , tt
  firm-live s@(coldS _ _)           sc ky t = firm-gh s sc ky t , tt
  firm-live s@(ofS _ _ _)           sc ky t = firm-gh s sc ky t , tt
  firm-live s@doneS                 sc ky t = firm-gh s sc ky t , tt
  firm-live s@(mapS _ _)            sc ky t = firm-gh s sc ky t , tt
  firm-live s@(scanS _ _ _)         sc ky t = firm-gh s sc ky t , tt
  firm-live s@(cutS _ _ _)          sc ky t = firm-gh s sc ky t , tt
  firm-live s@(takeS _ _ _ _)       sc ky t = firm-gh s sc ky t , tt
  firm-live s@(flatS _ _ _ _ _ _ _) sc ky t = firm-gh s sc ky t , tt
  firm-live s@(connS _ _ _)         sc ky t = firm-gh s sc ky t , tt
  firm-live s@(joinS _ _ _ _)       sc ky t = firm-gh s sc ky t , tt

  -- A connect, its source running, ended, or yet to subscribe.
  firm-conn : ∀ {Γ X B} {ν : All (λ _ → Mode) Γ} {V : Shuts Γ} {ρ ρ′ : NEnv Γ} cl sl sa ba as ow r en (o : St Γ X) (b : St (X ∷ Γ) B)
            → Scene ν V ρ ρ′ → Keyed (connS (cs cl sl sa ba as ow r en) o b) ρ → Toldˢ V (connS (cs cl sl sa ba as ow r en) o b)
            → Firm ν (connectᶜ r (shutAll (upˢ V) (bodyG (cs cl sl sa ba as ow r en) (gh b))) (shutAllˢ V (srcG (cs cl sl sa ba as ow r en) o))) ρ′
  firm-conn false sl sa nothing as ow r en o b sc (m , ko , kb) (to , tb) =
    firm-gh b (scene-live (gh o) sc (sorted-cons (src-sorted k o _ (ConnAt.ends m) (src-shape k o b _ m ko (sorted sc))) (sorted sc))) kb tb
    , firm-gh o sc ko to
    where k = cs false sl sa nothing as ow r en
  firm-conn {ν = ν} {V} {ρ′ = ρ′} true sl sa nothing as ow r en o b sc (m , ko , kb) (to , tb) =
    subst (λ n → Firm (overᵐ ∷ᴬ ν) n (end en ∷ᴬ ρ′)) (shut-snoc (upˢ V) (here refl) en (gh b))
      (firm-gh b (scene-end en sc (sorted-cons (src-sorted k o _ (ConnAt.ends m) (src-shape k o b _ m ko (sorted sc))) (sorted sc))) kb tb)
    , subst Rested (sym (shut-rest V (gh o))) tt
    where k = cs true sl sa nothing as ow r en
  firm-conn false sl sa (just p) as ow r en o b sc (m , ko , kb) (to , tb) =
    firm-gh b (scene-live (subOr (p ⊕ [ ix 1 ]) o) sc (sorted-cons (src-sorted k o _ (ConnAt.ends m) (src-shape k o b _ m ko (sorted sc))) (sorted sc))) kb tb
    , firm-src p o sc (ConnAt.sub m) ko to
    where k = cs false sl sa (just p) as ow r en
  firm-conn true sl sa (just p) as ow r en o b sc (m , ko , kb) (to , tb) =
    firm-gh b (scene-live (subOr (p ⊕ [ ix 1 ]) o) sc (sorted-cons (src-sorted k o _ (ConnAt.ends m) (src-shape k o b _ m ko (sorted sc))) (sorted sc))) kb tb
    , firm-src p o sc (ConnAt.sub m) ko to
    where k = cs true sl sa (just p) as ow r en

  firm-src : ∀ {Γ X} {ν : All (λ _ → Mode) Γ} {V : Shuts Γ} {ρ ρ′ : NEnv Γ} p (o : St Γ X) → Scene ν V ρ ρ′ → SubKeys (just p) ρ → Keyed o ρ → Toldˢ V o
           → Firm ν (shutAll V (subOr (p ⊕ [ ix 1 ]) o)) ρ′
  firm-src {V = V} {ρ′ = ρ′} p (pend s) (scene h t S so) (hq , al) ky to =
    firm-sub V s (p ⊕ [ ix 1 ]) h
      (placed-shuts V (subscribe s (p ⊕ [ ix 1 ])) (ended-same V S t) (placed-sub s (p ⊕ [ ix 1 ]) ρ′ hq (sorted-agree S so) (everyᴱ-agree S al)))
  firm-src p o@(coldS _ _)           sc sk ky t = firm-gh o sc ky t
  firm-src p o@(ofS _ _ _)           sc sk ky t = firm-gh o sc ky t
  firm-src p o@doneS                 sc sk ky t = firm-gh o sc ky t
  firm-src p o@(mapS _ _)            sc sk ky t = firm-gh o sc ky t
  firm-src p o@(scanS _ _ _)         sc sk ky t = firm-gh o sc ky t
  firm-src p o@(cutS _ _ _)          sc sk ky t = firm-gh o sc ky t
  firm-src p o@(lnS _ _)             sc sk ky t = firm-gh o sc ky t
  firm-src p o@(takeS _ _ _ _)       sc sk ky t = firm-gh o sc ky t
  firm-src p o@(flatS _ _ _ _ _ _ _) sc sk ky t = firm-gh o sc ky t
  firm-src p o@(connS _ _ _)         sc sk ky t = firm-gh o sc ky t
  firm-src p o@(joinS _ _ _ _)       sc sk ky t = firm-gh o sc ky t

------------------------------------------------------------------------
-- The scope

mutual
  ghE-firm : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} {V : Shuts Γ} {ρ : NEnv Γ} (s : St Γ A) → Scene ν V ρ ρ → Keyed s ρ → Toldˢ V s → GhE ν V ρ s
  ghE-firm (pend o)                sc ky t         = tt
  ghE-firm (coldS b l)             sc ky t         = tt
  ghE-firm (ofS i p xs)            sc ky t         = tt
  ghE-firm doneS                   sc ky t         = tt
  ghE-firm (mapS f s)              sc ky t         = ghE-firm s sc (proj₂ ky) t
  ghE-firm (scanS f z s)           sc ky t         = ghE-firm s sc (proj₂ ky) t
  ghE-firm (cutS l a s)            sc ky t         = ghE-firm s sc (proj₂ ky) t
  ghE-firm (lnS b s)               sc ky t         = ghE-firm s sc (proj₂ ky) t
  ghE-firm (takeS i q w s)         sc ky t         = ghE-firm s sc (proj₂ ky) t
  ghE-firm (flatS op f d n q o ls) sc ky (to , tl) =
    (firm-lanes ls sc (proj₂ (proj₂ ky)) tl , outs-firm d o sc (proj₁ (proj₂ ky)) to)
    , ghE-firm o sc (proj₁ (proj₂ ky)) to , ghE-firmᴸ ls sc (proj₂ (proj₂ ky)) tl
  ghE-firm (connS k o b)           sc (m , ko , kb) (to , tb) =
    src-firm k o sc ko to , ghE-firm o sc ko to , ghE-firm b (scene-src k o b sc m ko) kb tb
  ghE-firm (joinS j true x ib)     sc ky t         = t
  ghE-firm (joinS j false x ib)    sc ky t         = tt

  ghE-firmᴸ : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} {V : Shuts Γ} {ρ : NEnv Γ} (ls : List (St Γ A)) → Scene ν V ρ ρ → KeyedL ls ρ → Toldᴸ V ls → GhEᴸ ν V ρ ls
  ghE-firmᴸ []       sc ky       t         = tt
  ghE-firmᴸ (s ∷ ls) sc (ks , kl) (ts , tl) = ghE-firm s sc ks ts , ghE-firmᴸ ls sc kl tl

  outs-firm : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} {V : Shuts Γ} {ρ : NEnv Γ} d (o : St Γ A) → Scene ν V ρ ρ → Keyed o ρ → Toldˢ V o
            → Outs ν V ρ d (gh o)
  outs-firm false o sc ky t = firm-gh o sc ky t
  outs-firm true  o sc ky t = tt

  src-firm : ∀ {Γ X} {ν : All (λ _ → Mode) Γ} {V : Shuts Γ} {ρ : NEnv Γ} k (o : St Γ X) → Scene ν V ρ ρ → Keyed o ρ → Toldˢ V o
           → Src ν V ρ k o
  src-firm (cs false sl sa nothing as ow r en)  o sc ky t = firm-gh o sc ky t
  src-firm (cs false sl sa (just p) as ow r en) o sc ky t = tt
  src-firm (cs true sl sa ba as ow r en)        o sc ky t = tt

-- Of a tree keyed and told, the scope at the root.
gh-firm : ∀ {R} (t : St [] R) → Keys t → Toldˢ none t → Gh top t
gh-firm t ky tl = ghE-firm t (scene (λ ()) tt (λ d → tt) tt) ky tl
