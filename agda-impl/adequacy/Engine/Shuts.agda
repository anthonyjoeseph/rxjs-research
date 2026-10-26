{-# OPTIONS --guardedness #-}

-- ENDED CONNECTS, EACH WITH WHERE IT ENDED: `Unfold.shut` tells every
-- joiner of one its end, unless it was told already.  Read through a
-- list of them (`shutAll`), a node's formers pass the shuts through to
-- their parts (`shut-comm`, `shut-flat`, `shut-conn`), and a joiner
-- already told is left as it is (`told-shut`).  Of a state: each live
-- joiner of a shut connect told (`Toldˢ`), the machine feeding every live
-- joiner its connect's end when the connect's source ends.
module adequacy.Engine.Shuts where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Properties using () renaming (map-id to map-idᴸ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (there)
open import Data.Maybe using (Maybe; just; nothing; is-just) renaming (map to mapᴹ)
open import Data.Maybe.Properties using () renaming (map-id to map-idᴹ)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym)

open import denotation.MonotonicList.Events using (Pos)
open import denotation.Unfold using (Node; Source; live; ended; joinᶜ; flatMapᶜ; connectᶜ; unionᶜ; restᶜ; idleᶜ; restsᶜ; shut; shutᴹ; shutᴸ; same?)
open import operation.PureObservable using (module Machine)
open Machine using (St; pend; coldS; ofS; doneS; mapS; scanS; cutS; lnS; takeS; flatS; connS; joinS; free; cpAt; cutAt; overAt)
open import adequacy.Engine.Meaning using (endOf; taken; doneG)

data Shuts : List Set → Set₁ where
  none   : ∀ {Γ} → Shuts Γ
  shutAt : ∀ {Γ X} → X ∈ Γ → Pos → Shuts Γ → Shuts Γ

upˢ : ∀ {Γ X} → Shuts Γ → Shuts (X ∷ Γ)
upˢ none           = none
upˢ (shutAt i c s) = shutAt (there i) c (upˢ s)

shutAll : ∀ {Γ B} → Shuts Γ → Node Γ B → Node Γ B
shutAll none           n = n
shutAll (shutAt i c s) n = shut i c (shutAll s n)

shutAllˢ : ∀ {Γ B} → Shuts Γ → Source Γ B → Source Γ B
shutAllˢ s (live n)    = live (shutAll s n)
shutAllˢ s (ended e t) = ended e (shutAll s t)

------------------------------------------------------------------------
-- Formers

-- A node every shut leaves as it is.
shut-still : ∀ {Γ A} (s : Shuts Γ) (n : Node Γ A) → (∀ {X} (i : X ∈ Γ) c → shut i c n ≡ n) → shutAll s n ≡ n
shut-still none           n h = refl
shut-still (shutAt i c s) n h = trans (cong (shut i c) (shut-still s n h)) (h i c)

-- A former every shut passes through to its part.
shut-comm : ∀ {Γ A B} (F : Node Γ A → Node Γ B) → (∀ {X} (i : X ∈ Γ) c n → shut i c (F n) ≡ F (shut i c n))
          → ∀ (s : Shuts Γ) n → shutAll s (F n) ≡ F (shutAll s n)
shut-comm F h none           n = refl
shut-comm F h (shutAt i c s) n = trans (cong (shut i c) (shut-comm F h s n)) (h i c (shutAll s n))

shut-union : ∀ {Γ B} (s : Shuts Γ) (x y : Node Γ B) → shutAll s (unionᶜ x y) ≡ unionᶜ (shutAll s x) (shutAll s y)
shut-union none           x y = refl
shut-union (shutAt i c s) x y = cong (shut i c) (shut-union s x y)

shutᴹ-map : ∀ {Γ A X} (i : X ∈ Γ) c (h : Node Γ A → Node Γ A) (mo : Maybe (Node Γ A)) → shutᴹ i c (mapᴹ h mo) ≡ mapᴹ (λ n → shut i c (h n)) mo
shutᴹ-map i c h nothing  = refl
shutᴹ-map i c h (just n) = refl

shutᴸ-map : ∀ {Γ A X} (i : X ∈ Γ) c (h : Node Γ A → Node Γ A) (ls : List (Node Γ A)) → shutᴸ i c (map h ls) ≡ map (λ n → shut i c (h n)) ls
shutᴸ-map i c h []       = refl
shutᴸ-map i c h (n ∷ ls) = cong (shut i c (h n) ∷_) (shutᴸ-map i c h ls)

shut-flat : ∀ {Γ A B} (s : Shuts Γ) op (g : A → Pos → Node Γ B) (mo : Maybe (Node Γ A)) ls qs pl
          → shutAll s (flatMapᶜ op g mo ls qs pl) ≡ flatMapᶜ op g (mapᴹ (shutAll s) mo) (map (shutAll s) ls) qs (shutAll s pl)
shut-flat none op g mo ls qs pl = sym (cong₂ (λ m l → flatMapᶜ op g m l qs pl) (map-idᴹ mo) (map-idᴸ ls))
shut-flat (shutAt i c s) op g mo ls qs pl =
  trans (cong (shut i c) (shut-flat s op g mo ls qs pl))
        (cong₂ (λ m l → flatMapᶜ op g m l qs (shut i c (shutAll s pl))) (shutᴹ-map i c (shutAll s) mo) (shutᴸ-map i c (shutAll s) ls))

shut-rest : ∀ {Γ A B} (s : Shuts Γ) (n : Node Γ A) → shutAll s (restᶜ {B = B} n) ≡ restᶜ (shutAll s n)
shut-rest = shut-comm restᶜ (λ i c n → refl)

shut-rests : ∀ {Γ A B} (s : Shuts Γ) (ds : List (Node Γ A)) → shutAll s (restsᶜ {B = B} ds) ≡ restsᶜ (map (shutAll s) ds)
shut-rests s []       = shut-still s idleᶜ (λ i c → refl)
shut-rests s (d ∷ ds) = trans (shut-union s (restᶜ d) (restsᶜ ds)) (cong₂ unionᶜ (shut-rest s d) (shut-rests s ds))

shut-taken : ∀ {Γ A} (s : Shuts Γ) i q w (n : Node Γ A) → shutAll s (taken i q w n) ≡ taken i q w (shutAll s n)
shut-taken s i q free       n = shut-comm (taken i q free) (λ j c n → refl) s n
shut-taken s i q (cpAt p)   n = shut-comm (taken i q (cpAt p)) (λ j c n → refl) s n
shut-taken s i q (cutAt p)  n = shut-rest s n
shut-taken s i q (overAt p) n = shut-rest s n

shut-done : ∀ {Γ A} (s : Shuts Γ) m (l : Bool) (n : Node Γ A) → shutAll s (doneG m l n) ≡ doneG m l (shutAll s n)
shut-done s (just p) l     n = shut-rest s n
shut-done s nothing  false n = shut-rest s n
shut-done s nothing  true  n = refl

shut-conn : ∀ {Γ X B} (s : Shuts Γ) r (b : Node (X ∷ Γ) B) (src : Source Γ X)
          → shutAll s (connectᶜ r b src) ≡ connectᶜ r (shutAll (upˢ s) b) (shutAllˢ s src)
shut-conn none           r b (live n)    = refl
shut-conn none           r b (ended e t) = refl
shut-conn (shutAt i c s) r b (live n)    = cong (shut i c) (shut-conn s r b (live n))
shut-conn (shutAt i c s) r b (ended e t) = cong (shut i c) (shut-conn s r b (ended e t))

------------------------------------------------------------------------
-- Joiners told

Untold : ∀ {Γ X} → Shuts Γ → X ∈ Γ → Set
Untold none           x = ⊤
Untold (shutAt i c s) x = is-just (same? i x) ≡ false × Untold s x

Told : ∀ {Γ X} → Shuts Γ → X ∈ Γ → Maybe Pos → Set
Told s x (just _) = ⊤
Told s x nothing  = Untold s x

untold : ∀ {Γ X Y} (i : X ∈ Γ) c (x : Y ∈ Γ) j xs → is-just (same? i x) ≡ false → shut i c (joinᶜ x j xs nothing) ≡ joinᶜ x j xs nothing
untold i c x j xs u with same? i x | u
... | nothing   | _  = refl
... | just refl | ()

-- A joiner a shut has nothing to tell.
told-shut : ∀ {Γ X} (s : Shuts Γ) (x : X ∈ Γ) j xs e → Told s x e → shutAll s (joinᶜ x j xs e) ≡ joinᶜ x j xs e
told-shut none           x j xs e        t       = refl
told-shut (shutAt i c s) x j xs (just p) t       = cong (shut i c) (told-shut s x j xs (just p) tt)
told-shut (shutAt i c s) x j xs nothing  (u , t) = trans (cong (shut i c) (told-shut s x j xs nothing t)) (untold i c x j xs u)

mutual
  Toldˢ : ∀ {Γ A} → Shuts Γ → St Γ A → Set
  Toldˢ V (mapS f s)              = Toldˢ V s
  Toldˢ V (scanS f z s)           = Toldˢ V s
  Toldˢ V (cutS l a s)            = Toldˢ V s
  Toldˢ V (lnS b s)               = Toldˢ V s
  Toldˢ V (takeS i q w s)         = Toldˢ V s
  Toldˢ V (flatS op f d n q o ls) = Toldˢ V o × Toldᴸ V ls
  Toldˢ V (connS k o b)           = Toldˢ V o × Toldˢ (upˢ V) b
  Toldˢ V (joinS j true x ib)     = Told V x (endOf ib)
  Toldˢ V _                       = ⊤

  Toldᴸ : ∀ {Γ A} → Shuts Γ → List (St Γ A) → Set
  Toldᴸ V []       = ⊤
  Toldᴸ V (s ∷ ls) = Toldˢ V s × Toldᴸ V ls

told-∅ : ∀ {Γ X} (x : X ∈ Γ) e → Told none x e
told-∅ x (just _) = tt
told-∅ x nothing  = tt

-- With nothing shut, every joiner is told.
mutual
  told-none : ∀ {Γ A} (s : St Γ A) → Toldˢ none s
  told-none (pend o)                = tt
  told-none (coldS b l)             = tt
  told-none (ofS i p xs)            = tt
  told-none doneS                   = tt
  told-none (mapS f s)              = told-none s
  told-none (scanS f z s)           = told-none s
  told-none (cutS l a s)            = told-none s
  told-none (lnS b s)               = told-none s
  told-none (takeS i q w s)         = told-none s
  told-none (flatS op f d n q o ls) = told-none o , told-noneᴸ ls
  told-none (connS k o b)           = told-none o , told-none b
  told-none (joinS j true x ib)     = told-∅ x (endOf ib)
  told-none (joinS j false x ib)    = tt

  told-noneᴸ : ∀ {Γ A} (ls : List (St Γ A)) → Toldᴸ none ls
  told-noneᴸ []       = tt
  told-noneᴸ (s ∷ ls) = told-none s , told-noneᴸ ls

told-drop₀ : ∀ {Γ X Y} (i : X ∈ Γ) e (V : Shuts Γ) (x : Y ∈ Γ) m → Told (shutAt i e V) x m → Told V x m
told-drop₀ i e V x (just _) t       = tt
told-drop₀ i e V x nothing  (_ , u) = u

-- Told of more shuts, told of fewer.
mutual
  told-drop : ∀ {Γ A X} (i : X ∈ Γ) e (V : Shuts Γ) (s : St Γ A) → Toldˢ (shutAt i e V) s → Toldˢ V s
  told-drop i e V (pend o)                t         = tt
  told-drop i e V (coldS b l)             t         = tt
  told-drop i e V (ofS j p xs)            t         = tt
  told-drop i e V doneS                   t         = tt
  told-drop i e V (mapS f s)              t         = told-drop i e V s t
  told-drop i e V (scanS f z s)           t         = told-drop i e V s t
  told-drop i e V (cutS l a s)            t         = told-drop i e V s t
  told-drop i e V (lnS b s)               t         = told-drop i e V s t
  told-drop i e V (takeS j q w s)         t         = told-drop i e V s t
  told-drop i e V (flatS op f d n q o ls) (to , tl) = told-drop i e V o to , told-dropᴸ i e V ls tl
  told-drop i e V (connS k o b)           (to , tb) = told-drop i e V o to , told-drop (there i) e (upˢ V) b tb
  told-drop i e V (joinS j true x ib)     t         = told-drop₀ i e V x (endOf ib) t
  told-drop i e V (joinS j false x ib)    t         = tt

  told-dropᴸ : ∀ {Γ A X} (i : X ∈ Γ) e (V : Shuts Γ) (ls : List (St Γ A)) → Toldᴸ (shutAt i e V) ls → Toldᴸ V ls
  told-dropᴸ i e V []       t         = tt
  told-dropᴸ i e V (s ∷ ls) (ts , tl) = told-drop i e V s ts , told-dropᴸ i e V ls tl
