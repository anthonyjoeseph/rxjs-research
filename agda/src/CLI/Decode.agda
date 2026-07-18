-- Decode a serialized TestCase (JSON) into an intrinsically-typed program
-- and run it: ctx → Γ, exp → Closed Γ t (checked against each node's ty
-- annotation), slots → Slots Γ, fuel → ℕ; then evaluate and encode. This
-- is the elaborator the CLI's decode→evaluate→encode middle was owed.
module CLI.Decode where

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_)
open import Data.Char using () renaming (toℕ to charToℕ)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; map; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; toList)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (Vec; lookup; fromList)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Timed; after_,_; ObservableInput; hot; cold; InstEmit)
open import Rx.Exp using (Ty; unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_; obs; _≟ᵗ_;
                          Ctx; Val; Closed; Exp; Tm; Fn;
                          input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ;
                          mergeAllᵉ; concatAllᵉ; switchAllᵉ; exhaustAllᵉ;
                          μᵉ; varᵉ; deferᵉ;
                          varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ;
                          inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ;
                          add; sub; mul; eqᵖ; ltᵖ; notᵖ)
open import Rx.Evaluator using (Slot; scripted; shared; Slots; evaluate)
open import CLI.JSON
open import CLI.Encode using (encodeStream)

------------------------------------------------------------------------
-- JSON accessors and Maybe plumbing

infixl 1 _>>=?_
_>>=?_ : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
nothing >>=? _ = nothing
just x  >>=? f = f x

mapMaybe : {A B : Set} → (A → Maybe B) → List A → Maybe (List B)
mapMaybe f []       = just []
mapMaybe f (x ∷ xs) = f x >>=? λ y → mapMaybe f xs >>=? λ ys → just (y ∷ ys)

listEqℕ : List ℕ → List ℕ → Bool
listEqℕ []       []       = true
listEqℕ (x ∷ xs) (y ∷ ys) = (x ≡ᵇ y) ∧ listEqℕ xs ys
listEqℕ _        _        = false

_is_ : List ℕ → String → Bool
cs is s = listEqℕ cs (map charToℕ (toList s))

getField : String → JSON → Maybe JSON
getField name (jobj ms) = find ms
  where find : List (List ℕ × JSON) → Maybe JSON
        find []            = nothing
        find ((k , v) ∷ r) = if k is name then just v else find r
getField _ _ = nothing

asNum : JSON → Maybe ℕ
asNum (jnum n) = just n
asNum _        = nothing

asStr : JSON → Maybe (List ℕ)
asStr (jstr s) = just s
asStr _        = nothing

asArr : JSON → Maybe (List JSON)
asArr (jarr xs) = just xs
asArr _         = nothing

asBool : JSON → Maybe Bool
asBool (jbool b) = just b
asBool _         = nothing

------------------------------------------------------------------------
-- typed plumbing: casts, projections, indices

whenTy : (s t : Ty) → Maybe (s ≡ t)
whenTy s t with s ≟ᵗ t
... | yes p = just p
... | no _  = nothing

asProd asSum : Ty → Maybe (Ty × Ty)
asProd (s ×ᵗ u) = just (s , u)
asProd _        = nothing
asSum  (s +ᵗ u) = just (s , u)
asSum  _        = nothing

asObs : Ty → Maybe Ty
asObs (obs u) = just u
asObs _       = nothing

natToFin : (n : ℕ) → ℕ → Maybe (Fin n)
natToFin zero    _       = nothing
natToFin (suc n) zero    = just zero
natToFin (suc n) (suc k) = natToFin n k >>=? λ i → just (suc i)

-- the k-th entry of a context, if it has the wanted type
nthMember : (Θ : List Ty) (t : Ty) → ℕ → Maybe (t ∈ Θ)
nthMember []      t k       = nothing
nthMember (u ∷ Θ) t zero    with u ≟ᵗ t
... | yes refl = just (here refl)
... | no _     = nothing
nthMember (u ∷ Θ) t (suc k) = nthMember Θ t k >>=? λ x → just (there x)

nth : {A : Set} → List A → ℕ → Maybe A
nth []       _       = nothing
nth (x ∷ _)  zero    = just x
nth (_ ∷ xs) (suc k) = nth xs k

-- sequence a dependent Fin-indexed family of Maybes into a Maybe function
seqFin : ∀ {n} {P : Fin n → Set} → ((i : Fin n) → Maybe (P i)) → Maybe ((i : Fin n) → P i)
seqFin {zero}  f = just (λ ())
seqFin {suc n} f with f zero | seqFin {n} (λ i → f (suc i))
... | just x | just g = just (λ { zero → x ; (suc i) → g i })
... | _      | _      = nothing

------------------------------------------------------------------------
-- types

decodeTy : ℕ → JSON → Maybe Ty
decodeTy zero       _ = nothing
decodeTy (suc fuel) j = getField "type" j >>=? asStr >>=? λ tag →
  if tag is "unit" then just unitᵗ
  else if tag is "bool" then just boolᵗ
  else if tag is "nat" then just natᵗ
  else if tag is "prod" then
    (getField "fst" j >>=? decodeTy fuel >>=? λ s →
     getField "snd" j >>=? decodeTy fuel >>=? λ u → just (s ×ᵗ u))
  else if tag is "sum" then
    (getField "left" j >>=? decodeTy fuel >>=? λ s →
     getField "right" j >>=? decodeTy fuel >>=? λ u → just (s +ᵗ u))
  else if tag is "obs" then
    (getField "elem" j >>=? decodeTy fuel >>=? λ u → just (obs u))
  else nothing

-- the type annotation of a named child node
childTy : ℕ → String → JSON → Maybe Ty
childTy fuel name j = getField name j >>=? λ c → getField "ty" c >>=? decodeTy fuel

------------------------------------------------------------------------
-- expressions and terms (checking mode: expected type in, typed term out)

mutual
  decodeExp : ℕ → ∀ {n} (Γ : Ctx n) (Δᵍ Δ Θ : List Ty) (t : Ty)
            → JSON → Maybe (Exp Γ Δᵍ Δ Θ t)
  decodeExp zero       Γ Δᵍ Δ Θ t _ = nothing
  decodeExp (suc fuel) Γ Δᵍ Δ Θ t j = getField "type" j >>=? asStr >>=? λ tag →
    if tag is "input" then
      (getField "index" j >>=? asNum >>=? λ k → natToFin _ k >>=? λ i →
       whenTy (lookup Γ i) t >>=? λ { refl → just (input i) })
    else if tag is "empty" then just emptyᵉ
    else if tag is "of" then
      (getField "items" j >>=? asArr >>=? λ its →
       decodeTms fuel Γ Δᵍ Δ Θ t its >>=? λ ts → just (ofᵉ ts))
    else if tag is "map" then
      (childTy fuel "src" j >>=? λ s →
       getField "src" j >>=? decodeExp fuel Γ Δᵍ Δ Θ s >>=? λ src →
       getField "fn" j >>=? decodeTm fuel Γ Δᵍ Δ (s ∷ Θ) t >>=? λ fn →
       just (mapᵉ fn src))
    else if tag is "take" then
      (getField "count" j >>=? decodeTm fuel Γ Δᵍ Δ Θ natᵗ >>=? λ c →
       getField "src" j >>=? decodeExp fuel Γ Δᵍ Δ Θ t >>=? λ src →
       just (takeᵉ c src))
    else if tag is "scan" then
      (childTy fuel "src" j >>=? λ s →
       getField "fn" j >>=? decodeTm fuel Γ Δᵍ Δ ((t ×ᵗ s) ∷ Θ) t >>=? λ fn →
       getField "init" j >>=? decodeTm fuel Γ Δᵍ Δ Θ t >>=? λ ini →
       getField "src" j >>=? decodeExp fuel Γ Δᵍ Δ Θ s >>=? λ src →
       just (scanᵉ fn ini src))
    else if tag is "mergeAll" then
      (getField "src" j >>=? decodeExp fuel Γ Δᵍ Δ Θ (obs t) >>=? λ src → just (mergeAllᵉ src))
    else if tag is "concatAll" then
      (getField "src" j >>=? decodeExp fuel Γ Δᵍ Δ Θ (obs t) >>=? λ src → just (concatAllᵉ src))
    else if tag is "switchAll" then
      (getField "src" j >>=? decodeExp fuel Γ Δᵍ Δ Θ (obs t) >>=? λ src → just (switchAllᵉ src))
    else if tag is "exhaustAll" then
      (getField "src" j >>=? decodeExp fuel Γ Δᵍ Δ Θ (obs t) >>=? λ src → just (exhaustAllᵉ src))
    else if tag is "mu" then
      (getField "body" j >>=? decodeExp fuel Γ (t ∷ Δᵍ) Δ Θ t >>=? λ b → just (μᵉ b))
    else if tag is "varE" then
      (getField "index" j >>=? asNum >>=? λ k → nthMember Δ t k >>=? λ x → just (varᵉ x))
    else if tag is "defer" then
      (getField "body" j >>=? decodeExp fuel Γ [] (Δᵍ ++ Δ) Θ t >>=? λ b → just (deferᵉ b))
    else nothing
    where open import Data.List using (_++_)

  decodeTm : ℕ → ∀ {n} (Γ : Ctx n) (Δᵍ Δ Θ : List Ty) (t : Ty)
           → JSON → Maybe (Tm Γ Δᵍ Δ Θ t)
  decodeTm zero       Γ Δᵍ Δ Θ t _ = nothing
  decodeTm (suc fuel) Γ Δᵍ Δ Θ t j = getField "type" j >>=? asStr >>=? λ tag →
    if tag is "varT" then
      (getField "index" j >>=? asNum >>=? λ k → nthMember Θ t k >>=? λ x → just (varᵗ x))
    else if tag is "unitT" then (whenTy unitᵗ t >>=? λ { refl → just unit̂ })
    else if tag is "boolT" then
      (whenTy boolᵗ t >>=? λ { refl → getField "val" j >>=? asBool >>=? λ b → just (bool̂ b) })
    else if tag is "natT" then
      (whenTy natᵗ t >>=? λ { refl → getField "val" j >>=? asNum >>=? λ v → just (nat̂ v) })
    else if tag is "pairT" then
      (childTy fuel "fst" j >>=? λ s → childTy fuel "snd" j >>=? λ u →
       whenTy (s ×ᵗ u) t >>=? λ { refl →
         getField "fst" j >>=? decodeTm fuel Γ Δᵍ Δ Θ s >>=? λ a →
         getField "snd" j >>=? decodeTm fuel Γ Δᵍ Δ Θ u >>=? λ b → just (pairᵗ a b) })
    else if tag is "fstT" then
      (childTy fuel "pair" j >>=? asProd >>=? λ { (s , u) →
       whenTy s t >>=? λ { refl →
         getField "pair" j >>=? decodeTm fuel Γ Δᵍ Δ Θ (s ×ᵗ u) >>=? λ p → just (fstᵗ p) } })
    else if tag is "sndT" then
      (childTy fuel "pair" j >>=? asProd >>=? λ { (s , u) →
       whenTy u t >>=? λ { refl →
         getField "pair" j >>=? decodeTm fuel Γ Δᵍ Δ Θ (s ×ᵗ u) >>=? λ p → just (sndᵗ p) } })
    else if tag is "inlT" then
      (getField "ty" j >>=? decodeTy fuel >>=? asSum >>=? λ { (s , u) →
       whenTy (s +ᵗ u) t >>=? λ { refl →
         getField "val" j >>=? decodeTm fuel Γ Δᵍ Δ Θ s >>=? λ a → just (inlᵗ a) } })
    else if tag is "inrT" then
      (getField "ty" j >>=? decodeTy fuel >>=? asSum >>=? λ { (s , u) →
       whenTy (s +ᵗ u) t >>=? λ { refl →
         getField "val" j >>=? decodeTm fuel Γ Δᵍ Δ Θ u >>=? λ a → just (inrᵗ a) } })
    else if tag is "caseT" then
      (childTy fuel "scrut" j >>=? asSum >>=? λ { (s , u) →
       getField "scrut" j >>=? decodeTm fuel Γ Δᵍ Δ Θ (s +ᵗ u) >>=? λ sc →
       getField "onInl" j >>=? decodeTm fuel Γ Δᵍ Δ (s ∷ Θ) t >>=? λ l →
       getField "onInr" j >>=? decodeTm fuel Γ Δᵍ Δ (u ∷ Θ) t >>=? λ r → just (caseᵗ sc l r) })
    else if tag is "ifT" then
      (getField "cond" j >>=? decodeTm fuel Γ Δᵍ Δ Θ boolᵗ >>=? λ c →
       getField "then" j >>=? decodeTm fuel Γ Δᵍ Δ Θ t >>=? λ a →
       getField "else" j >>=? decodeTm fuel Γ Δᵍ Δ Θ t >>=? λ b → just (ifᵗ c a b))
    else if tag is "primT" then
      (getField "op" j >>=? asStr >>=? λ op → getField "arg" j >>=? λ argJ →
       if op is "add" then (whenTy natᵗ t >>=? λ { refl → decodeTm fuel Γ Δᵍ Δ Θ (natᵗ ×ᵗ natᵗ) argJ >>=? λ a → just (primᵗ add a) })
       else if op is "sub" then (whenTy natᵗ t >>=? λ { refl → decodeTm fuel Γ Δᵍ Δ Θ (natᵗ ×ᵗ natᵗ) argJ >>=? λ a → just (primᵗ sub a) })
       else if op is "mul" then (whenTy natᵗ t >>=? λ { refl → decodeTm fuel Γ Δᵍ Δ Θ (natᵗ ×ᵗ natᵗ) argJ >>=? λ a → just (primᵗ mul a) })
       else if op is "eq" then (whenTy boolᵗ t >>=? λ { refl → decodeTm fuel Γ Δᵍ Δ Θ (natᵗ ×ᵗ natᵗ) argJ >>=? λ a → just (primᵗ eqᵖ a) })
       else if op is "lt" then (whenTy boolᵗ t >>=? λ { refl → decodeTm fuel Γ Δᵍ Δ Θ (natᵗ ×ᵗ natᵗ) argJ >>=? λ a → just (primᵗ ltᵖ a) })
       else if op is "not" then (whenTy boolᵗ t >>=? λ { refl → decodeTm fuel Γ Δᵍ Δ Θ boolᵗ argJ >>=? λ a → just (primᵗ notᵖ a) })
       else nothing)
    else if tag is "strmT" then
      (getField "ty" j >>=? decodeTy fuel >>=? asObs >>=? λ u →
       whenTy (obs u) t >>=? λ { refl →
         getField "exp" j >>=? decodeExp fuel Γ Δᵍ Δ Θ u >>=? λ e → just (strmᵗ e) })
    else nothing

  decodeTms : ℕ → ∀ {n} (Γ : Ctx n) (Δᵍ Δ Θ : List Ty) (t : Ty)
            → List JSON → Maybe (List (Tm Γ Δᵍ Δ Θ t))
  decodeTms fuel Γ Δᵍ Δ Θ t []       = just []
  decodeTms fuel Γ Δᵍ Δ Θ t (j ∷ js) =
    decodeTm fuel Γ Δᵍ Δ Θ t j >>=? λ x → decodeTms fuel Γ Δᵍ Δ Θ t js >>=? λ xs → just (x ∷ xs)

------------------------------------------------------------------------
-- values (for scripted inputs), structural on the type

decodeVal : ℕ → ∀ {n} (Γ : Ctx n) (t : Ty) → JSON → Maybe (Val Γ t)
decodeVal fuel Γ unitᵗ    j = just tt
decodeVal fuel Γ boolᵗ    j = asBool j
decodeVal fuel Γ natᵗ     j = asNum j
decodeVal fuel Γ (s ×ᵗ u) j = asArr j >>=? λ
  { (a ∷ b ∷ []) → decodeVal fuel Γ s a >>=? λ va → decodeVal fuel Γ u b >>=? λ vb → just (va , vb)
  ; _            → nothing }
decodeVal fuel Γ (s +ᵗ u) j =
  getField "type" j >>=? asStr >>=? λ tag → getField "val" j >>=? λ vj →
  if tag is "inl" then (decodeVal fuel Γ s vj >>=? λ v → just (inj₁ v))
  else if tag is "inr" then (decodeVal fuel Γ u vj >>=? λ v → just (inj₂ v))
  else nothing
decodeVal fuel Γ (obs u)  j = decodeExp fuel Γ [] [] [] u j

------------------------------------------------------------------------
-- scripted inputs and the slot telescope

decodeTimed : ℕ → ∀ {n} (Γ : Ctx n) (t : Ty) → JSON → Maybe (Timed (Val Γ t))
decodeTimed fuel Γ t j =
  getField "wait" j >>=? asNum >>=? λ w →
  getField "val" j >>=? decodeVal fuel Γ t >>=? λ v → just (after w , v)

decodeInput : ℕ → ∀ {n} (Γ : Ctx n) (t : Ty) → JSON → Maybe (ObservableInput (Val Γ t))
decodeInput fuel Γ t j = getField "type" j >>=? asStr >>=? λ tag →
  if tag is "hot" then
    (getField "async" j >>=? asArr >>=? mapMaybe (decodeTimed fuel Γ t) >>=? λ a → just (hot a))
  else if tag is "cold" then
    (getField "sync" j >>=? asArr >>=? mapMaybe (decodeVal fuel Γ t) >>=? λ s →
     getField "async" j >>=? asArr >>=? mapMaybe (decodeTimed fuel Γ t) >>=? λ a → just (cold s a))
  else nothing

decodeSlotAt : ℕ → ∀ {n} (Γ : Ctx n) → List JSON → (i : Fin n) → Maybe (Slot Γ (lookup Γ i))
decodeSlotAt fuel Γ slotsJ i = nth slotsJ (Data.Fin.toℕ i) >>=? λ j →
  getField "type" j >>=? asStr >>=? λ tag →
  if tag is "scripted" then
    (getField "input" j >>=? decodeInput fuel Γ (lookup Γ i) >>=? λ inp → just (scripted inp))
  else if tag is "shared" then
    (getField "def" j >>=? decodeExp fuel Γ [] [] [] (lookup Γ i) >>=? λ d → just (shared d))
  else nothing
  where open import Data.Fin using (toℕ)

decodeSlots : ℕ → ∀ {n} (Γ : Ctx n) → List JSON → Maybe (Slots Γ)
decodeSlots fuel Γ slotsJ = seqFin (decodeSlotAt fuel Γ slotsJ)

------------------------------------------------------------------------
-- a whole case: decode, evaluate, encode. `nothing` ⇒ the CLI prints null.

BIG : ℕ
BIG = 100000

decodeCase : JSON → Maybe String
decodeCase j =
  getField "ctx" j >>=? asArr >>=? mapMaybe (decodeTy BIG) >>=? λ tys →
  getField "exp" j >>=? λ expJ →
  getField "ty" expJ >>=? decodeTy BIG >>=? λ t →
  decodeExp BIG (fromList tys) [] [] [] t expJ >>=? λ e →
  getField "slots" j >>=? asArr >>=? decodeSlots BIG (fromList tys) >>=? λ ins →
  getField "fuel" j >>=? asNum >>=? λ f →
  just (encodeStream t (evaluate f e ins))
