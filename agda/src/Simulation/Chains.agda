------------------------------------------------------------------
-- A MINTED SOURCE'S CHAINS PAIR UP, in order, as registrations the store
-- relation partners.  Every plain row is partnered, and a row at a source
-- numbered above the slots is a cold or deferred read whose partner sits
-- at the partnered source.  The live sources being distinct on each side
-- makes that partner the popped one, and the element types the pair of
-- sources holds make each side's type test agree with the other's.
------------------------------------------------------------------
module Simulation.Chains where

open import Data.Bool    using (true; false; T; if_then_else_)
open import Data.Bool.ListAction using (any)
open import Data.Empty   using (⊥-elim)
open import Data.List    using (List; []; _∷_; map)
open import Data.List.Properties using (++-identityʳ)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_) renaming (map to pw-map)
open import Data.List.Relation.Unary.All using (All; _∷_; [])
open import Data.List.Relation.Unary.AllPairs using (_∷_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Nat     using (zero; suc; _+_; _<_; _≤_; _≡ᵇ_; _≟_)
open import Data.Fin     using (Fin; toℕ; _↑ʳ_; _↑ˡ_)
open import Data.Fin.Properties using (toℕ<n; toℕ-↑ˡ; toℕ-↑ʳ; toℕ-injective; ↑ʳ-injective) renaming (_≟_ to _≟ᶠ_)
open import Data.Nat.Properties using (≡ᵇ⇒≡; ≡⇒≡ᵇ; <⇒≢; <-trans; <-≤-trans; <-asym; +-monoʳ-<; m≤m+n; 1+n≢0; suc-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (inj₁; inj₂; [_,_])
open import Data.Vec     using (lookup)
open import Data.Unit    using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Relation.Nullary using (yes; no)

open import Rx.Exp       using (Ty; unitᵗ; boolᵗ; natᵗ; uniqᵗ; _×ᵗ_; _+ᵗ_; listᵗ; obs; Ctx; Closed; _≟ᵗ_)
open import Rx.Evaluator using (LiveSource; Arrival; Sched; EvalSt; RegId; RegRow; RegSrc; atDyn; atSlot; shareAdmit; regSource; regFloor; Path;
  arrSource; arrTy; arrVal; schedHeadOf; chainsGo; chainsOf; sameSource; schedGo; cascadeOpen; share-sink)
open import Rx.Evaluator.Domain using (cascadeGo⇓; casc-nil; casc-cut; casc-live)
open import SExp.Syntax  using (Kinds; plainᵏ; plainᵗ; emitᵗ; hotᵏ)
open import Simulation.Pass using (dynRow; clash; Paired; SlotPair; slotpair; head; HotStart; hot-idle; hot-block)
open import Simulation.Pop using (pp-popped)
open import Simulation.Schedules using (Popped; pop; sched-pop; HeadOf)
open import Simulation.Stores using (srcCount; InputBlock; Src; data~; SrcPair; RowRel; MachRow; hot~; RegRel; []; _∷_; read~; cold~; defer~; mach; Partners; ArrRel; ArrRows; Store; Arr; SameAt;
  hotEq; sharedEq; aboveᵇ; above-≤)
  renaming (here to sp-here; there to sp-there)

-- a source number that sits under another is not it
sameSource-lt : ∀ {m k} → k < m → sameSource m k ≡ false
sameSource-lt {m} {k} lt with m ≡ᵇ k in e
... | false = refl
... | true  = ⊥-elim (<⇒≢ lt (sym (≡ᵇ⇒≡ m k (subst T (sym e) tt))))

sameSource-no : ∀ {m k} → m ≢ k → sameSource m k ≡ false
sameSource-no {m} {k} ne with m ≡ᵇ k in e
... | false = refl
... | true  = ⊥-elim (ne (≡ᵇ⇒≡ m k (subst T (sym e) tt)))

module _ {n} {Δ : Ctx n} {t} where

  -- a row at another source contributes no chain
  chains-skip : ∀ (a : Arrival Δ) {rid} {s : RegSrc Δ} {u} {p : Path Δ (regFloor s) u t} {rest}
              → sameSource (arrSource a) (regSource s) ≡ false
              → chainsGo a ((rid , s , (u , p)) ∷ rest) ≡ chainsGo a rest
  chains-skip a {s = s} {u} eq with sameSource (arrSource a) (regSource s) | u ≟ᵗ arrTy a
  ... | false | _ = refl
  ... | true  | _ = ⊥-elim (clash eq)

  -- a row at the arrival's source and type is its next chain
  chains-take : ∀ (a : Arrival Δ) {rid lo} {src u} {p : Path Δ lo u t} {rest}
              → (e : src ≡ arrSource a) → (e′ : u ≡ arrTy a)
              → Σ _ λ c → chainsGo a ((rid , atDyn src lo , (u , p)) ∷ rest) ≡ c ∷ chainsGo a rest
                          × dynRow a c ≡ (rid , atDyn src lo , (u , p))
  chains-take a {rid} {lo} {p = p} {rest} refl refl
    with sameSource (arrSource a) (arrSource a) in e₁ | arrTy a ≟ᵗ arrTy a
  ... | true  | yes refl = (rid , lo , p) , refl , refl
  ... | true  | no ¬p    = ⊥-elim (¬p refl)
  ... | false | _        = ⊥-elim (subst T e₁ (≡⇒≡ᵇ (arrSource a) (arrSource a) refl))

-- two pointwise lists, one pair apart from a common tail
cons-skip : ∀ {A B : Set} {P : A → B → Set} {xs ys xs′ ys′} → xs ≡ xs′ → ys ≡ ys′ → Pointwise P xs′ ys′ → Pointwise P xs ys
cons-skip refl refl pw = pw

-- the same, for a pair that does contribute one chain on each side
cons-take : ∀ {A B : Set} {P : A → B → Set} {xs ys x y xs₁ ys₁} → xs ≡ x ∷ xs₁ → ys ≡ y ∷ ys₁ → P x y → Pointwise P xs₁ ys₁ → Pointwise P xs ys
cons-take refl refl p pw = p ∷ pw

module _ {n} {Γ : Ctx n} (κ : Kinds n) where

  -- a source the head of a list does not number is apart from the one a pair puts after it
  sp-apart : ∀ {x} {LP : List (LiveSource Γ)} {LI : List (LiveSource (plainᵏ Γ κ))} {s s′ u u′}
           → All (x ≢_) (map LiveSource.source LP) → SrcPair κ LP LI s s′ u u′ → x ≢ s
  sp-apart (x≢ ∷ _) sp-here      = x≢
  sp-apart (_ ∷ ap) (sp-there q) = sp-apart ap q

  sp-apart′ : ∀ {x} {LP : List (LiveSource Γ)} {LI : List (LiveSource (plainᵏ Γ κ))} {s s′ u u′}
            → All (x ≢_) (map LiveSource.source LI) → SrcPair κ LP LI s s′ u u′ → x ≢ s′
  sp-apart′ (x≢ ∷ _) sp-here      = x≢
  sp-apart′ (_ ∷ ap) (sp-there q) = sp-apart′ ap q

  -- with the sources on each side distinct, two pairs at one source on one side are at the other's
  sp-fun : ∀ {LP : List (LiveSource Γ)} {LI : List (LiveSource (plainᵏ Γ κ))} {s s′ u u′ t t′ w w′}
         → Unique (map LiveSource.source LP) → Unique (map LiveSource.source LI)
         → SrcPair κ LP LI s s′ u u′ → SrcPair κ LP LI t t′ w w′
         → (s ≡ t → s′ ≡ t′ × u ≡ w × u′ ≡ w′) × (s′ ≡ t′ → s ≡ t)
  sp-fun (_ ∷ _) (_ ∷ _) sp-here sp-here = (λ _ → refl , refl , refl) , λ _ → refl
  sp-fun (a ∷ _) (a′ ∷ _) sp-here (sp-there q) = (λ e → ⊥-elim (sp-apart a q e)) , λ e′ → ⊥-elim (sp-apart′ a′ q e′)
  sp-fun (a ∷ _) (a′ ∷ _) (sp-there p) sp-here = (λ e → ⊥-elim (sp-apart a p (sym e))) , λ e′ → ⊥-elim (sp-apart′ a′ p (sym e′))
  sp-fun (_ ∷ ul) (_ ∷ ul′) (sp-there p) (sp-there q) = sp-fun ul ul′ p q

  -- WHAT A PAIR OF REGISTRATIONS DOES TO THE TWO CHAIN LISTS OF ONE ARRIVAL PAIR
  data RowChain {t} (a : Arrival Γ) (a′ : Arrival (plainᵏ Γ κ)) (r : RegRow Γ t) (r′ : RegRow (plainᵏ Γ κ) (emitᵗ t))
                (rest : List (RegRow Γ t)) (rest′ : List (RegRow (plainᵏ Γ κ) (emitᵗ t))) : Set where
    skip : chainsGo a (r ∷ rest) ≡ chainsGo a rest → chainsGo a′ (r′ ∷ rest′) ≡ chainsGo a′ rest′ → RowChain a a′ r r′ rest rest′
    take : ∀ c c′ → chainsGo a (r ∷ rest) ≡ c ∷ chainsGo a rest → chainsGo a′ (r′ ∷ rest′) ≡ c′ ∷ chainsGo a′ rest′
         → dynRow a c ≡ r → dynRow a′ c′ ≡ r′ → RowChain a a′ r r′ rest rest′

  module _ {a a′} where

    -- two rows at partnered sources: both are the popped source's, or neither
    dyn-row : ∀ {t rid rid′ src src′ lo lo′ u u′} {p : Path Γ lo u t} {p′ : Path (plainᵏ Γ κ) lo′ u′ (emitᵗ t)} {rest rest′}
            → ArrRel (arrSource a) (arrSource a′) (arrTy a) (arrTy a′) src src′ u u′
            → RowChain a a′ (rid , atDyn src lo , (u , p)) (rid′ , atDyn src′ lo′ , (u′ , p′)) rest rest′
    dyn-row {src = src} ar with arrSource a ≟ src | ar
    ... | yes eq | f , g with f eq
    ...   | eq′ , et , et′ with chains-take a (sym eq) (sym et) | chains-take a′ (sym eq′) (sym et′)
    ...     | c , h , d | c′ , h′ , d′ = take c c′ h h′ d d′
    dyn-row sp | no ne | f , g = skip (chains-skip a (sameSource-no ne)) (chains-skip a′ (sameSource-no (λ e′ → ne (g e′))))

    chains-rows : ∀ {t π NP NI RS RS′ rg rg′} → n < arrSource a → n + n < arrSource a′
                → (rr : RegRel κ π {t} NP NI RS RS′ rg rg′)
                → ArrRows κ _ _ _ _ _ rr (arrSource a) (arrSource a′) (arrTy a) (arrTy a′)
                → Pointwise (λ c c′ → Partners κ π NP NI RS RS′ rr (dynRow a c) (dynRow a′ c′)) (chainsGo a rg) (chainsGo a′ rg′)
    chains-rows na na′ [] _ = []
    chains-rows na na′ (read~ {i = i} hk pr refl ∷ q) ars =
      cons-skip (chains-skip a (sameSource-lt (<-trans (toℕ<n i) na)))
                (chains-skip a′ (sameSource-lt (<-trans (subst (_< n + n) (sym (toℕ-↑ʳ n i)) (+-monoʳ-< n (toℕ<n i))) na′)))
                (pw-map inj₂ (chains-rows na na′ q ars))
    chains-rows na na′ (cold~ sp ib pr refl ∷ q) (ar , ars) with dyn-row ar
    ... | skip e e′ = cons-skip e e′ (pw-map inj₂ (chains-rows na na′ q ars))
    ... | take c c′ e e′ d d′ = cons-take e e′ (inj₁ (d , d′)) (pw-map inj₂ (chains-rows na na′ q ars))
    chains-rows na na′ (defer~ sp pi lnP lnI pr refl ∷ q) (ar , ars) with dyn-row ar
    ... | skip e e′ = cons-skip e e′ (pw-map inj₂ (chains-rows na na′ q ars))
    ... | take c c′ e e′ d d′ = cons-take e e′ (inj₁ (d , d′)) (pw-map inj₂ (chains-rows na na′ q ars))
    chains-rows na na′ (mach (hot~ {i = i} hot ib refl) q) ars =
      cons-skip refl
                (chains-skip a′ (sameSource-lt (<-trans (subst (_< n + n) (sym (toℕ-↑ˡ i n)) (<-≤-trans (toℕ<n i) (m≤m+n n n))) na′)))
                (chains-rows na na′ q ars)

  -- what a registry's rows say of a popped pair of sources, from the pair's place in the live lists
  arr-rows : ∀ {RS : List (LiveSource Γ)} {RS′ : List (LiveSource (plainᵏ Γ κ))} {s s′ u u′}
           → Unique (map LiveSource.source RS) → Unique (map LiveSource.source RS′) → SrcPair κ RS RS′ s s′ u u′
           → ∀ {t π NP NI rg rg′} (rr : RegRel κ π {t} NP NI RS RS′ rg rg′) → ArrRows κ _ _ _ _ _ rr s s′ u u′
  arr-rows ua ua′ pk []                    = tt
  arr-rows ua ua′ pk (read~ _ _ _ ∷ q)     = arr-rows ua ua′ pk q
  arr-rows ua ua′ pk (cold~ sp _ _ _ ∷ q)  = sp-fun ua ua′ pk sp , arr-rows ua ua′ pk q
  arr-rows ua ua′ pk (defer~ sp _ _ _ _ _ ∷ q) = sp-fun ua ua′ pk sp , arr-rows ua ua′ pk q
  arr-rows ua ua′ pk (mach _ q)            = arr-rows ua ua′ pk q

-- the popped pair's place in the live lists bounds both numbers by the counters
sp-bound : ∀ {n} {Γ : Ctx n} {κ : Kinds n} {LP : List (LiveSource Γ)} {LI : List (LiveSource (plainᵏ Γ κ))} {s s′ u u′ c}
         → All (_< c) (map LiveSource.source LP) → SrcPair κ LP LI s s′ u u′ → s < c
sp-bound (x ∷ _)  sp-here      = x
sp-bound (_ ∷ ab) (sp-there q) = sp-bound ab q

sp-bound′ : ∀ {n} {Γ : Ctx n} {κ : Kinds n} {LP : List (LiveSource Γ)} {LI : List (LiveSource (plainᵏ Γ κ))} {s s′ u u′ c}
          → All (_< c) (map LiveSource.source LI) → SrcPair κ LP LI s s′ u u′ → s′ < c
sp-bound′ (x ∷ _)  sp-here      = x
sp-bound′ (_ ∷ ab) (sp-there q) = sp-bound′ ab q

-- a number the lists give a source before the popped pair's place is not the pair's
sp-ne : ∀ {n} {Γ : Ctx n} {κ : Kinds n} {LP : List (LiveSource Γ)} {LI : List (LiveSource (plainᵏ Γ κ))} {s s′ u u′ x}
      → SrcPair κ LP LI s s′ u u′ → All (x ≢_) (map LiveSource.source LP) → x ≢ s
sp-ne sp-here      (ne ∷ _) = ne
sp-ne (sp-there q) (_ ∷ ne) = sp-ne q ne

sp-ne′ : ∀ {n} {Γ : Ctx n} {κ : Kinds n} {LP : List (LiveSource Γ)} {LI : List (LiveSource (plainᵏ Γ κ))} {s s′ u u′ x}
       → SrcPair κ LP LI s s′ u u′ → All (x ≢_) (map LiveSource.source LI) → x ≢ s′
sp-ne′ sp-here      (ne ∷ _) = ne
sp-ne′ (sp-there q) (_ ∷ ne) = sp-ne′ q ne

-- after the pair's place, no source carries either number
tail-same : ∀ {n} {Γ : Ctx n} {κ : Kinds n} {s s′} {ls : List (LiveSource Γ)} {ls′ : List (LiveSource (plainᵏ Γ κ))}
          → Pointwise (Src κ) ls ls′ → All (s ≢_) (map LiveSource.source ls) → All (s′ ≢_) (map LiveSource.source ls′)
          → Pointwise (λ l l′ → SameAt s s′ (LiveSource.source l) (LiveSource.source l′)) ls ls′
tail-same []       []        []         = []
tail-same (_ ∷ rs) (ne ∷ nl) (ne′ ∷ nl′) = ((λ e → ⊥-elim (ne (sym e))) , (λ e → ⊥-elim (ne′ (sym e)))) ∷ tail-same rs nl nl′

-- the popped pair is the only pair of sources carrying its numbers
arr-lists : ∀ {n} {Γ : Ctx n} {κ : Kinds n} {s s′ u u′} {ls : List (LiveSource Γ)} {ls′ : List (LiveSource (plainᵏ Γ κ))}
          → Pointwise (Src κ) ls ls′ → SrcPair κ ls ls′ s s′ u u′
          → Unique (map LiveSource.source ls) → Unique (map LiveSource.source ls′)
          → Pointwise (λ l l′ → SameAt s s′ (LiveSource.source l) (LiveSource.source l′)) ls ls′
arr-lists (_ ∷ rs) sp-here      (nl ∷ _) (nl′ ∷ _)  = ((λ _ → refl) , (λ _ → refl)) ∷ tail-same rs nl nl′
arr-lists (_ ∷ rs) (sp-there q) (nl ∷ ul) (nl′ ∷ ul′) =
  ((λ e → ⊥-elim (sp-ne q nl e)) , (λ e → ⊥-elim (sp-ne′ q nl′ e))) ∷ arr-lists rs q ul ul′

-- THE PAIR A POP TOOK FROM IS PARTNERED AT THE STORE IT LEAVES
arr-pop : ∀ {n} {Γ : Ctx n} {t} (κ : Kinds n) {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)}
            {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei} {s s′ u u′}
        → (S : Store κ sP stP sI stI) → SrcPair κ (Sched.live sP) (Sched.live sI) s s′ u u′ → Arr S s s′ u u′
arr-pop κ S pk = record
  { boundP = sp-bound (proj₁ (Store.bounded S)) pk
  ; boundI = sp-bound′ (proj₂ (Store.bounded S)) pk
  ; rows   = arr-rows κ (proj₁ (Store.distinct S)) (proj₂ (Store.distinct S)) pk (Store.rows S)
  ; lists  = arr-lists (Store.sources S) pk (proj₁ (Store.distinct S)) (proj₂ (Store.distinct S)) }

-- the chains of a registry none of whose rows a list of ids has: none of the ids
chains-rids : ∀ {n} {Δ : Ctx n} {t} (a : Arrival Δ) {P : RegId → Set} {rg : List (RegRow Δ t)}
            → All (λ r → P (proj₁ r)) rg → All (λ c → P (proj₁ c)) (chainsGo a rg)
chains-rids a [] = []
chains-rids a {rg = (rid , s , (u , p)) ∷ r} (px ∷ q) with sameSource (arrSource a) (regSource s) | u ≟ᵗ arrTy a
... | false | _        = chains-rids a q
... | true  | no  _    = chains-rids a q
... | true  | yes refl = px ∷ chains-rids a q

-- chains partnered and cut on neither side stand paired
paired-zip : ∀ {n} {Γ : Ctx n} {t} {κ : Kinds n} {π NP NI LP LI rs rs′} (rr : RegRel κ π {t} NP NI LP LI rs rs′)
               (CP CI : List RegId) (a : Arrival Γ) (a′ : Arrival (plainᵏ Γ κ)) {cs cs′}
           → Pointwise (λ c c′ → Partners κ π NP NI LP LI rr (dynRow a c) (dynRow a′ c′)) cs cs′
           → All (λ c → any (_≡ᵇ proj₁ c) CP ≡ false) cs → All (λ c → any (_≡ᵇ proj₁ c) CI ≡ false) cs′
           → Pointwise (Paired rr CP CI a a′) cs cs′
paired-zip rr CP CI a a′ [] [] [] = []
paired-zip rr CP CI a a′ (p ∷ ps) (u ∷ us) (u′ ∷ us′) = inj₂ (u , u′ , p) ∷ paired-zip rr CP CI a a′ ps us us′

-- A MINTED SOURCE'S CHAINS PAIR UP, in order, as registrations the store
-- relation partners
dyn-chains : ∀ {n} {Γ : Ctx n} {t} (κ : Kinds n) {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)}
               {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei}
  → Store κ sP stP sI stI
  → ∀ {a a′ rs rs′} → schedGo (Sched.live sP) ≡ inj₂ (a , rs) → schedGo (Sched.live sI) ≡ inj₂ (a′ , rs′)
  → n < arrSource a → n + n < arrSource a′
  → (s₀ : Store κ (record sP { live = rs }) (cascadeOpen stP) (record sI { live = rs′ }) (cascadeOpen stI))
  → Pointwise (λ c c′ → Partners κ _ _ _ _ _ (Store.rows s₀) (dynRow a c) (dynRow a′ c′))
              (chainsOf a stP) (chainsOf a′ stI)
dyn-chains κ {sP = sP} {sI = sI} s ex ex′ na na′ s₀
  with subst₂ (Popped (Src κ) (Sched.live sP) (Sched.live sI)) ex ex′ (sched-pop (Store.sync s) (Store.sources s))
... | pop _ _ _ _ _ _ _ _ pp =
  chains-rows κ na na′ (Store.rows s₀)
    (arr-rows κ (proj₁ (Store.distinct s₀)) (proj₂ (Store.distinct s₀)) (pp-popped κ pp) (Store.rows s₀))

-- A MINTED SOURCE'S END WALKS THE CHAINS THAT ARE LEFT, which pair up as
-- the value pass's did.  The rows the registries still hold are cut on
-- neither side, and the popped pair's place against the rows is what the
-- pass handed on.
dyn-chains-end : ∀ {n} {Γ : Ctx n} {t} (κ : Kinds n) {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)}
                   {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei} {a a′}
  → (s : Store κ sP stP sI stI)
  → n < arrSource a → n + n < arrSource a′
  → Arr s (arrSource a) (arrSource a′) (arrTy a) (arrTy a′)
  → Pointwise (Paired (Store.rows s) (EvalSt.cancelled stP) (EvalSt.cancelled stI) a a′) (chainsOf a stP) (chainsOf a′ stI)
dyn-chains-end κ {stP = stP} {stI = stI} {a = a} {a′} s na na′ ar =
  paired-zip (Store.rows s) (EvalSt.cancelled stP) (EvalSt.cancelled stI) a a′ (chains-rows κ na na′ (Store.rows s) (Arr.rows ar))
    (chains-rids a (proj₁ (Store.uncut s))) (chains-rids a′ (proj₂ (Store.uncut s)))

-- a row at the arrival's slot and type is its next chain
chains-slot : ∀ {n} {Δ : Ctx n} {t} (a : Arrival Δ) {rid} {i : Fin n} {u} {p : Path Δ (suc (toℕ i)) u t} {rest}
            → arrSource a ≡ toℕ i → (e′ : u ≡ arrTy a)
            → Σ _ λ q → chainsGo a ((rid , atSlot i , (u , p)) ∷ rest) ≡ (rid , suc (toℕ i) , q) ∷ chainsGo a rest
                        × _≡_ {A = RegRow Δ t} (rid , atSlot i , (arrTy a , q)) (rid , atSlot i , (u , p))
chains-slot a {rid} {i} {p = p} e refl with sameSource (arrSource a) (toℕ i) in e₁ | arrTy a ≟ᵗ arrTy a
... | true  | yes refl = p , refl , refl
... | true  | no ¬p    = ⊥-elim (¬p refl)
... | false | _        = ⊥-elim (subst T e₁ (≡⇒≡ᵇ (arrSource a) (toℕ i) e))

-- a row at the share's own slot and type is admitted next
admit-slot : ∀ {m} {Δ : Ctx m} {t} {k : Fin m} {rid u} {p : Path Δ (suc (toℕ k)) u t} {rest}
           → (e′ : u ≡ lookup Δ k)
           → Σ _ λ q → shareAdmit k ((rid , atSlot k , (u , p)) ∷ rest) ≡ (rid , q) ∷ shareAdmit k rest
                       × _≡_ {A = RegRow Δ t} (rid , atSlot k , (lookup Δ k , q)) (rid , atSlot k , (u , p))
admit-slot {Δ = Δ} {k = k} {rid} {p = p} refl with k ≟ᶠ k | lookup Δ k ≟ᵗ lookup Δ k
... | yes refl | yes refl = p , refl , refl
... | yes refl | no ¬p    = ⊥-elim (¬p refl)
... | no ¬e    | _        = ⊥-elim (¬e refl)

-- a row at another slot is not admitted
admit-skip : ∀ {m} {Δ : Ctx m} {t} {k j : Fin m} {rid u} {p : Path Δ (suc (toℕ j)) u t} {rest}
           → k ≢ j → shareAdmit k ((rid , atSlot j , (u , p)) ∷ rest) ≡ shareAdmit k rest
admit-skip {Δ = Δ} {k = k} {j} {u = u} ne with k ≟ᶠ j | u ≟ᵗ lookup Δ k
... | no _  | _ = refl
... | yes e | _ = ⊥-elim (ne e)

module _ {n} {Γ : Ctx n} (κ : Kinds n) where

  -- a pair the tail of a relation partners, the whole relation does
  slot-there : ∀ {t π NP NI LP LI r r′ rs rs′} (x : RowRel {Γ = Γ} κ π {t} NP NI LP LI r r′) {q : RegRel {Γ = Γ} κ π NP NI LP LI rs rs′}
                 {CP CI i u c d}
             → SlotPair q CP CI i {u} c d → SlotPair (x ∷ q) CP CI i c d
  slot-there x (slotpair (inj₁ c))           = slotpair (inj₁ c)
  slot-there x (slotpair (inj₂ (a , b , p))) = slotpair (inj₂ (a , b , inj₂ p))

  slot-mach : ∀ {t π NP NI LP LI r′ rs rs′} (x : MachRow {Γ = Γ} κ π {t} NP NI LP LI r′) {q : RegRel {Γ = Γ} κ π NP NI LP LI rs rs′}
                {CP CI i u c d}
            → SlotPair q CP CI i {u} c d → SlotPair (mach x q) CP CI i c d
  slot-mach x (slotpair p) = slotpair p

  -- A HOT SLOT'S READERS PAIR UP, in order, with the rows its share
  -- admits: a minted source's row sits above every slot, and the impl's
  -- raw slot is below every stamped one
  slot-rows : ∀ {t π NP NI LP LI rg rg′} {a : Arrival Γ} {i : Fin n} {CP CI}
            → arrSource a ≡ toℕ i → arrTy a ≡ lookup Γ i
            → (rr : RegRel {Γ = Γ} κ π {t} NP NI LP LI rg rg′)
            → All (λ r → aboveᵇ (proj₁ (proj₂ r)) ≡ true) rg
            → All (λ r → any (_≡ᵇ proj₁ r) CP ≡ false) rg → All (λ r → any (_≡ᵇ proj₁ r) CI ≡ false) rg′
            → Pointwise (SlotPair rr CP CI i) (chainsGo a rg) (shareAdmit (n ↑ʳ i) rg′)
  slot-rows e ty [] _ _ _ = []
  slot-rows {a = a} {i} e ty (read~ {i = j} hk pr refl ∷ q) (_ ∷ ab) (uP ∷ usP) (uI ∷ usI) with i ≟ᶠ j
  ... | no ne =
    cons-skip (chains-skip a (sameSource-no (λ x → ne (toℕ-injective (trans (sym e) x)))))
              (admit-skip (λ x → ne (↑ʳ-injective n i j x)))
              (pw-map (slot-there _) (slot-rows e ty q ab usP usI))
  ... | yes refl with chains-slot a {i = i} e (sym ty) | admit-slot {k = n ↑ʳ i} (sym ([ hotEq {Γ = Γ} κ i , sharedEq {Γ = Γ} κ i ] hk))
  ...   | c , h , d | c′ , h′ , d′ =
    cons-take h h′ (slotpair (inj₂ (uP , uI , inj₁ (d , d′)))) (pw-map (slot-there _) (slot-rows e ty q ab usP usI))
  slot-rows {a = a} {i} e ty (cold~ {src = src} sp ib pr refl ∷ q) (ab₀ ∷ ab) (_ ∷ usP) (_ ∷ usI) =
    cons-skip (chains-skip a (sameSource-no (λ x → <⇒≢ (<-≤-trans (toℕ<n i) (above-≤ ab₀)) (trans (sym e) x))))
              refl
              (pw-map (slot-there _) (slot-rows e ty q ab usP usI))
  slot-rows {a = a} {i} e ty (defer~ {src = src} sp pi lnP lnI pr refl ∷ q) (ab₀ ∷ ab) (_ ∷ usP) (_ ∷ usI) =
    cons-skip (chains-skip a (sameSource-no (λ x → <⇒≢ (<-≤-trans (toℕ<n i) (above-≤ ab₀)) (trans (sym e) x))))
              refl
              (pw-map (slot-there _) (slot-rows e ty q ab usP usI))
  slot-rows {i = i} e ty (mach x@(hot~ {i = j} hot ib refl) q) ab usP (_ ∷ usI) =
    cons-skip refl
              (admit-skip (λ y → <⇒≢ (<-≤-trans (toℕ<n j) (m≤m+n n (toℕ i)))
                                     (sym (trans (sym (toℕ-↑ʳ n i)) (trans (cong toℕ y) (toℕ-↑ˡ j n))))))
              (pw-map (slot-mach x) (slot-rows e ty q ab usP usI))

-- A HOT SLOT'S CHAINS PAIR UP with the rows its share admits, as
-- registrations the store relation partners, cut on neither side
slot-chains : ∀ {n} {Γ : Ctx n} {t} (κ : Kinds n) {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)}
                {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei}
            → (S : Store κ sP stP sI stI) {a : Arrival Γ} {i : Fin n}
            → arrSource a ≡ toℕ i → arrTy a ≡ lookup Γ i
            → Pointwise (SlotPair (Store.rows S) (EvalSt.cancelled stP) (EvalSt.cancelled stI) i)
                (chainsOf a stP) (shareAdmit (n ↑ʳ i) (EvalSt.registry stI))
slot-chains κ S e ty = slot-rows κ e ty (Store.rows S) (proj₁ (Store.above S)) (proj₁ (Store.uncut S)) (proj₂ (Store.uncut S))

------------------------------------------------------------------
-- A HOT ARRIVAL'S RAW CHAIN
------------------------------------------------------------------

-- a source number against itself
same-refl : ∀ x → sameSource x x ≡ true
same-refl zero    = refl
same-refl (suc x) = same-refl x

module _ {m} {Δ : Ctx m} {t} where

  -- a row elsewhere leaves a count alone, a row there raises it
  count-hit : ∀ k (r : RegRow Δ t) K → sameSource k (regSource (proj₁ (proj₂ r))) ≡ true → srcCount k (r ∷ K) ≡ suc (srcCount k K)
  count-hit k (rid , x , c) K e = cong (λ b → if b then suc (srcCount k K) else srcCount k K) e

  count-pass : ∀ k (r : RegRow Δ t) K → sameSource k (regSource (proj₁ (proj₂ r))) ≡ false → srcCount k (r ∷ K) ≡ srcCount k K
  count-pass k (rid , x , c) K e = cong (λ b → if b then suc (srcCount k K) else srcCount k K) e

  -- none at a source, none behind the head either
  count-tail : ∀ {k} (r : RegRow Δ t) K → srcCount k (r ∷ K) ≡ 0 → srcCount k K ≡ 0
  count-tail {k} (rid , s , c) K z = go _ refl
    where
    go : ∀ b → sameSource k (regSource s) ≡ b → srcCount k K ≡ 0
    go true  e = ⊥-elim (1+n≢0 (trans (sym (count-hit k (rid , s , c) K e)) z))
    go false e = trans (sym (count-pass k (rid , s , c) K e)) z

  -- no row at the arrival's source, no chain
  raw-none : ∀ (a : Arrival Δ) (K : List (RegRow Δ t)) → srcCount (arrSource a) K ≡ 0 → chainsGo a K ≡ []
  raw-none a [] _ = refl
  raw-none a ((rid , s , (u , p)) ∷ K) z = go _ refl
    where
    go : ∀ b → sameSource (arrSource a) (regSource s) ≡ b → chainsGo a ((rid , s , (u , p)) ∷ K) ≡ []
    go true  e = ⊥-elim (1+n≢0 (trans (sym (count-hit (arrSource a) (rid , s , (u , p)) K e)) z))
    go false e = trans (chains-skip a e) (raw-none a K (trans (sym (count-pass (arrSource a) (rid , s , (u , p)) K e)) z))

  -- a row at the arrival's source but not its type contributes no chain
  chains-mistyped : ∀ (a : Arrival Δ) {rid} {s : RegSrc Δ} {u} {p : Path Δ (regFloor s) u t} {rest}
                  → u ≢ arrTy a → chainsGo a ((rid , s , (u , p)) ∷ rest) ≡ chainsGo a rest
  chains-mistyped a {s = s} {u} ne with sameSource (arrSource a) (regSource s) | u ≟ᵗ arrTy a
  ... | false | _      = refl
  ... | true  | no _   = refl
  ... | true  | yes e  = ⊥-elim (ne e)

module _ {n} {Γ : Ctx n} (κ : Kinds n) where

  -- A HOT SLOT NO STAMPED ROW READS HAS NO PLAIN READER: every plain
  -- reader of the slot is partnered with a row at its share
  plain-none : ∀ {t π NP NI LP LI rg rg′} {a : Arrival Γ} {i : Fin n}
             → arrSource a ≡ toℕ i
             → (rr : RegRel {Γ = Γ} κ π {t} NP NI LP LI rg rg′)
             → All (λ r → aboveᵇ (proj₁ (proj₂ r)) ≡ true) rg
             → srcCount (toℕ (n ↑ʳ i)) rg′ ≡ 0
             → chainsGo a rg ≡ []
  plain-none e [] _ _ = refl
  plain-none {a = a} {i} e (_∷_ {r′ = r′} {rs′ = rs′} (read~ {i = j} hk pr refl) q) (_ ∷ ab) z with i ≟ᶠ j
  ... | yes refl = ⊥-elim (1+n≢0 (trans (sym (count-hit (toℕ (n ↑ʳ i)) r′ rs′ (same-refl (toℕ (n ↑ʳ i))))) z))
  ... | no ne    = trans (chains-skip a (sameSource-no (λ x → ne (toℕ-injective (trans (sym e) x)))))
                         (plain-none e q ab (count-tail r′ rs′ z))
  plain-none {a = a} {i} e (_∷_ {r′ = r′} {rs′ = rs′} (cold~ sp ib pr refl) q) (ab₀ ∷ ab) z =
    trans (chains-skip a (sameSource-no (λ x → <⇒≢ (<-≤-trans (toℕ<n i) (above-≤ ab₀)) (trans (sym e) x))))
          (plain-none e q ab (count-tail r′ rs′ z))
  plain-none {a = a} {i} e (_∷_ {r′ = r′} {rs′ = rs′} (defer~ sp pi lnP lnI pr refl) q) (ab₀ ∷ ab) z =
    trans (chains-skip a (sameSource-no (λ x → <⇒≢ (<-≤-trans (toℕ<n i) (above-≤ ab₀)) (trans (sym e) x))))
          (plain-none e q ab (count-tail r′ rs′ z))
  plain-none e (mach {r′ = r′} {rs′ = rs′} x q) ab z = plain-none e q ab (count-tail r′ rs′ z)

  -- an arrival not at its slot's type has no plain reader either
  plain-mistyped : ∀ {t π NP NI LP LI rg rg′} {a : Arrival Γ} {i : Fin n}
                 → arrSource a ≡ toℕ i → arrTy a ≢ lookup Γ i
                 → (rr : RegRel {Γ = Γ} κ π {t} NP NI LP LI rg rg′)
                 → All (λ r → aboveᵇ (proj₁ (proj₂ r)) ≡ true) rg
                 → chainsGo a rg ≡ []
  plain-mistyped e ne [] _ = refl
  plain-mistyped {a = a} {i} e ne (read~ {i = j} hk pr refl ∷ q) (_ ∷ ab) with i ≟ᶠ j
  ... | yes refl = trans (chains-mistyped a (λ x → ne (sym x))) (plain-mistyped e ne q ab)
  ... | no ne′   = trans (chains-skip a (sameSource-no (λ x → ne′ (toℕ-injective (trans (sym e) x)))))
                         (plain-mistyped e ne q ab)
  plain-mistyped {a = a} {i} e ne (cold~ sp ib pr refl ∷ q) (ab₀ ∷ ab) =
    trans (chains-skip a (sameSource-no (λ x → <⇒≢ (<-≤-trans (toℕ<n i) (above-≤ ab₀)) (trans (sym e) x))))
          (plain-mistyped e ne q ab)
  plain-mistyped {a = a} {i} e ne (defer~ sp pi lnP lnI pr refl ∷ q) (ab₀ ∷ ab) =
    trans (chains-skip a (sameSource-no (λ x → <⇒≢ (<-≤-trans (toℕ<n i) (above-≤ ab₀)) (trans (sym e) x))))
          (plain-mistyped e ne q ab)
  plain-mistyped e ne (mach x q) ab = plain-mistyped e ne q ab

  -- a raw slot's number is no stamped slot's
  raw≢stamped : ∀ (i j : Fin n) → toℕ (i ↑ˡ n) ≢ toℕ (n ↑ʳ j)
  raw≢stamped i j eq = <⇒≢ (<-≤-trans (toℕ<n i) (m≤m+n n (toℕ j))) (trans (sym (toℕ-↑ˡ i n)) (trans eq (toℕ-↑ʳ n j)))

  raw<ₙ : ∀ (i : Fin n) → toℕ (i ↑ˡ n) < n + n
  raw<ₙ i = subst (_< n + n) (sym (toℕ-↑ˡ i n)) (<-≤-trans (toℕ<n i) (m≤m+n n n))

  -- THE IMPL'S CHAINS AT A HOT ARRIVAL ONCE ITS SHARE HAS CONNECTED: the
  -- one raw row's, or none if the arrival is not at the slot's type
  data RawOne {t π NP NI} (a′ : Arrival (plainᵏ Γ κ)) (i : Fin n) (CI : List RegId)
              (rg′ : List (RegRow (plainᵏ Γ κ) (emitᵗ t))) : Set where
    raw-mistyped : arrTy a′ ≢ plainᵗ (lookup Γ i) → chainsGo a′ rg′ ≡ [] → RawOne a′ i CI rg′
    raw-at : ∀ {rid q ℓ full} {h : ℓ ≤ toℕ (n ↑ʳ i)} (hot : lookup κ i ≡ hotᵏ)
           → chainsGo a′ rg′ ≡ (rid , suc (toℕ (i ↑ˡ n)) , q) ∷ []
           → _≡_ {A = RegRow (plainᵏ Γ κ) (emitᵗ t)} (rid , atSlot (i ↑ˡ n) , (arrTy a′ , q)) (rid , atSlot (i ↑ˡ n) , (plainᵗ (lookup Γ i) , full))
           → InputBlock {Γ = Γ} κ π {t} NP NI (plainᵗ (lookup Γ i)) full
               (subst (λ u → Path (plainᵏ Γ κ) ℓ u (emitᵗ t)) (hotEq {Γ = Γ} κ i hot) (share-sink (n ↑ʳ i) h))
           → any (_≡ᵇ rid) CI ≡ false
           → RawOne a′ i CI rg′

  raw-cons : ∀ {t π NP NI} {a′ : Arrival (plainᵏ Γ κ)} {i CI r′ rest}
           → chainsGo a′ (r′ ∷ rest) ≡ chainsGo a′ rest
           → RawOne {t} {π} {NP} {NI} a′ i CI rest → RawOne {t} {π} {NP} {NI} a′ i CI (r′ ∷ rest)
  raw-cons e (raw-mistyped ne c)  = raw-mistyped ne (trans e c)
  raw-cons e (raw-at hot c d ib u) = raw-at hot (trans e c) d ib u

  raw-one : ∀ {t π NP NI LP LI rg rg′} {a′ : Arrival (plainᵏ Γ κ)} {i : Fin n} {CI}
          → arrSource a′ ≡ toℕ (i ↑ˡ n)
          → (rr : RegRel {Γ = Γ} κ π {t} NP NI LP LI rg rg′)
          → All (λ r → aboveᵇ (proj₁ (proj₂ r)) ≡ true) rg′
          → All (λ r → any (_≡ᵇ proj₁ r) CI ≡ false) rg′
          → srcCount (toℕ (i ↑ˡ n)) rg′ ≡ 1
          → RawOne {t} {π} {NP} {NI} a′ i CI rg′
  raw-one e [] _ _ ()
  raw-one {a′ = a′} {i} e (_∷_ {r′ = r′} {rs′ = rs′} (read~ {i = j} hk pr refl) q) (_ ∷ ab) (_ ∷ us) z =
    raw-cons (chains-skip a′ (sameSource-no (λ x → raw≢stamped i j (trans (sym e) x))))
             (raw-one e q ab us (trans (sym (count-pass _ r′ rs′ (sameSource-no (raw≢stamped i j)))) z))
  raw-one {a′ = a′} {i} e (_∷_ {r′ = r′} {rs′ = rs′} (cold~ sp ib pr refl) q) (ab₀ ∷ ab) (_ ∷ us) z =
    raw-cons (chains-skip a′ (sameSource-no (λ x → <⇒≢ (<-≤-trans (raw<ₙ i) (above-≤ ab₀)) (trans (sym e) x))))
             (raw-one e q ab us (trans (sym (count-pass _ r′ rs′ (sameSource-no (<⇒≢ (<-≤-trans (raw<ₙ i) (above-≤ ab₀)))))) z))
  raw-one {a′ = a′} {i} e (_∷_ {r′ = r′} {rs′ = rs′} (defer~ sp pi lnP lnI pr refl) q) (ab₀ ∷ ab) (_ ∷ us) z =
    raw-cons (chains-skip a′ (sameSource-no (λ x → <⇒≢ (<-≤-trans (raw<ₙ i) (above-≤ ab₀)) (trans (sym e) x))))
             (raw-one e q ab us (trans (sym (count-pass _ r′ rs′ (sameSource-no (<⇒≢ (<-≤-trans (raw<ₙ i) (above-≤ ab₀)))))) z))
  raw-one {a′ = a′} {i} e (mach {r′ = r′} {rs′ = rs′} (hot~ {i = j} hot ib refl) q) (_ ∷ ab) (u₀ ∷ us) z with j ≟ᶠ i
  ... | no ne =
    raw-cons (chains-skip a′ (sameSource-no (λ x → ne′ (trans (sym e) x))))
             (raw-one e q ab us (trans (sym (count-pass _ r′ rs′ (sameSource-no ne′))) z))
    where
      ne′ : toℕ (i ↑ˡ n) ≢ toℕ (j ↑ˡ n)
      ne′ x = ne (toℕ-injective (trans (sym (toℕ-↑ˡ j n)) (trans (sym x) (toℕ-↑ˡ i n))))
  ... | yes refl with plainᵗ (lookup Γ i) ≟ᵗ arrTy a′
  ...   | yes ety with chains-slot a′ {i = i ↑ˡ n} e ety
  ...     | c , h , d = raw-at hot (trans h (cong (_ ∷_) none)) d ib u₀
    where
      none = raw-none a′ rs′ (subst (λ k → srcCount k rs′ ≡ 0) (sym e) (suc-injective (trans (sym (count-hit (toℕ (i ↑ˡ n)) r′ rs′ (same-refl (toℕ (i ↑ˡ n))))) z)))
  raw-one {a′ = a′} {i} e (mach {r′ = r′} {rs′ = rs′} (hot~ {i = j} hot ib refl) q) (_ ∷ ab) (u₀ ∷ us) z | yes refl | no ¬e =
    raw-mistyped (λ x → ¬e (sym x)) (trans (chains-mistyped a′ ¬e) none)
    where
      none = raw-none a′ rs′ (subst (λ k → srcCount k rs′ ≡ 0) (sym e) (suc-injective (trans (sym (count-hit (toℕ (i ↑ˡ n)) r′ rs′ (same-refl (toℕ (i ↑ˡ n))))) z)))

-- a type is read back off its plain translation
unplainᵗ : Ty → Ty
unplainᵗ unitᵗ     = unitᵗ
unplainᵗ boolᵗ     = boolᵗ
unplainᵗ natᵗ      = natᵗ
unplainᵗ uniqᵗ     = uniqᵗ
unplainᵗ (s ×ᵗ t)  = unplainᵗ s ×ᵗ unplainᵗ t
unplainᵗ (s +ᵗ t)  = unplainᵗ s +ᵗ unplainᵗ t
unplainᵗ (listᵗ t) = listᵗ (unplainᵗ t)
unplainᵗ (obs (listᵗ (_ +ᵗ (a +ᵗ _)) ×ᵗ _)) = obs (unplainᵗ a)
unplainᵗ (obs x)   = obs x

unplain-plain : ∀ t → unplainᵗ (plainᵗ t) ≡ t
unplain-plain unitᵗ     = refl
unplain-plain boolᵗ     = refl
unplain-plain natᵗ      = refl
unplain-plain uniqᵗ     = refl
unplain-plain (s ×ᵗ t)  = cong₂ _×ᵗ_ (unplain-plain s) (unplain-plain t)
unplain-plain (s +ᵗ t)  = cong₂ _+ᵗ_ (unplain-plain s) (unplain-plain t)
unplain-plain (listᵗ t) = cong listᵗ (unplain-plain t)
unplain-plain (obs t)   = cong obs (unplain-plain t)

plainᵗ-inj : ∀ {s t} → plainᵗ s ≡ plainᵗ t → s ≡ t
plainᵗ-inj {s} {t} e = trans (sym (unplain-plain s)) (trans (cong unplainᵗ e) (unplain-plain t))

-- a popped arrival carries its source's number and type
head-source : ∀ {k} {Δ : Ctx k} (l : LiveSource Δ) {a l₂} → schedHeadOf l ≡ inj₂ (a , l₂)
            → Arrival.source a ≡ LiveSource.source l
head-source l eq with LiveSource.pending l
head-source l refl | _ ∷ _ = refl

head-elem : ∀ {k} {Δ : Ctx k} (l : LiveSource Δ) {a l₂} → schedHeadOf l ≡ inj₂ (a , l₂)
          → arrTy a ≡ LiveSource.elemTy l
head-elem l eq with LiveSource.pending l
head-elem l refl | _ ∷ _ = refl

-- no chain, no step
casc-empty : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {a vs fin s} {st : EvalSt e} {r}
           → cascadeGo⇓ a vs fin [] s st r → r ≡ ([] , s , st)
casc-empty casc-nil = refl

module _ {n} {Γ : Ctx n} (κ : Kinds n) where

  -- a slot's source holds its script's values, at the plain type
  src-plain : ∀ {l l′} → Src {Γ = Γ} κ l l′ → LiveSource.source l < n → LiveSource.elemTy l′ ≡ plainᵗ (LiveSource.elemTy l)
  src-plain (data~ eq _) _   = eq
  src-plain (defer~ lt _) lt′ = ⊥-elim (<-asym lt lt′)

  -- so a slot's arrival on the impl side is at the plain type of the plain one's
  head-ety : ∀ {l l′ a a′} {i : Fin n} → Src {Γ = Γ} κ l l′ → HeadOf l a → HeadOf l′ a′
           → Arrival.source a ≡ toℕ i → arrTy a′ ≡ plainᵗ (arrTy a)
  head-ety {l} {l′} {i = i} src (_ , h) (_ , h′) e =
    trans (head-elem l′ h′)
          (trans (src-plain src (subst (_< n) (trans (sym e) (head-source l h)) (toℕ<n i)))
                 (cong plainᵗ (sym (head-elem l h))))

-- A HOT ARRIVAL'S IMPL CHAINS: none, and no plain reader either, until
-- the share has connected; then the one raw row's, whose step is the
-- input block's run
hot-start : ∀ {n} {Γ : Ctx n} {t} (κ : Kinds n) {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)}
              {sP : Sched Γ} {stP : EvalSt ep} {sI : Sched (plainᵏ Γ κ)} {stI : EvalSt ei}
          → (S : Store κ sP stP sI stI) {a : Arrival Γ} {a′ : Arrival (plainᵏ Γ κ)} {i : Fin n}
          → lookup κ i ≡ hotᵏ
          → ∀ {l l′} → Src κ l l′ → HeadOf l a → HeadOf l′ a′
          → Arrival.source a ≡ toℕ i → Arrival.source a′ ≡ toℕ (i ↑ˡ n)
          → ∀ {oI sI₁ stI₁}
          → cascadeGo⇓ a′ (arrVal a′ ∷ []) false (chainsOf a′ stI) sI stI (oI , sI₁ , stI₁)
          → HotStart κ S a a′ i oI sI₁ stI₁
hot-start {n} {Γ} κ {stP = stP} {sI = sI} {stI = stI} S {a} {a′} {i} hk src h h′ e₁ e₂ {oI} {sI₁} {stI₁} go
  with Store.census S i hk
... | inj₂ (z₁ , z₂) =
  hot-idle (plain-none {Γ = Γ} κ e₁ (Store.rows S) (proj₁ (Store.above S)) z₂)
           (casc-empty (subst (λ c → cascadeGo⇓ a′ (arrVal a′ ∷ []) false c sI stI (oI , sI₁ , stI₁))
                              (raw-none a′ (EvalSt.registry stI) (subst (λ k → srcCount k (EvalSt.registry stI) ≡ 0) (sym e₂) z₁)) go))
... | inj₁ c with raw-one {Γ = Γ} κ {CI = EvalSt.cancelled stI} e₂ (Store.rows S) (proj₂ (Store.above S)) (proj₂ (Store.uncut S)) c
...   | raw-mistyped ne none =
  hot-idle (plain-mistyped {Γ = Γ} κ e₁ (λ x → ne (trans (head-ety {Γ = Γ} κ src h h′ e₁) (cong plainᵗ x))) (Store.rows S) (proj₁ (Store.above S)))
           (casc-empty (subst (λ c → cascadeGo⇓ a′ (arrVal a′ ∷ []) false c sI stI (oI , sI₁ , stI₁)) none go))
...   | raw-at hot ch d ib u
  with subst (λ c → cascadeGo⇓ a′ (arrVal a′ ∷ []) false c sI stI (oI , sI₁ , stI₁)) ch go
...     | casc-cut y _ = ⊥-elim (clash (trans (sym y) u))
...     | casc-live _ d′ casc-nil =
  subst (λ o → HotStart κ S a a′ i o sI₁ stI₁) (sym (++-identityʳ _))
        (hot-block κ S hot (head src h h′ e₁ e₂)
                   (plainᵗ-inj (trans (sym (head-ety {Γ = Γ} κ src h h′ e₁)) (cong (λ r → proj₁ (proj₂ (proj₂ r))) d)))
                   d ib d′)
