------------------------------------------------------------------
-- A MINTED SOURCE'S CHAINS PAIR UP, in order, as registrations the store
-- relation partners.  Every plain row is partnered, and a row at a source
-- numbered above the slots is a cold or deferred read whose partner sits
-- at the partnered source.  The live sources being distinct on each side
-- makes that partner the popped one, and the element types the pair of
-- sources holds make each side's type test agree with the other's.
------------------------------------------------------------------
module Simulation.Chains where

open import Data.Bool    using (true; false; T)
open import Data.Bool.ListAction using (any)
open import Data.Empty   using (⊥-elim)
open import Data.List    using (List; []; _∷_; map)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_) renaming (map to pw-map)
open import Data.List.Relation.Unary.All using (All; _∷_; [])
open import Data.List.Relation.Unary.AllPairs using (_∷_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Nat     using (_+_; _<_; _≡ᵇ_; _≟_)
open import Data.Fin.Properties using (toℕ<n; toℕ-↑ˡ; toℕ-↑ʳ)
open import Data.Nat.Properties using (≡ᵇ⇒≡; ≡⇒≡ᵇ; <⇒≢; <-trans; <-≤-trans; +-monoʳ-<; m≤m+n)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (inj₁; inj₂)
open import Data.Unit    using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; subst; subst₂)
open import Relation.Nullary using (yes; no)

open import Rx.Exp       using (Ctx; Closed; _≟ᵗ_)
open import Rx.Evaluator using (LiveSource; Arrival; Sched; EvalSt; RegId; RegRow; RegSrc; atDyn; regSource; regFloor; Path;
  arrSource; arrTy; chainsGo; chainsOf; sameSource; schedGo; cascadeOpen)
open import SExp.Syntax  using (Kinds; plainᵏ; emitᵗ)
open import Simulation.Pass using (dynRow; clash; Paired)
open import Simulation.Pop using (pp-popped)
open import Simulation.Schedules using (Popped; pop; sched-pop)
open import Simulation.Stores using (Src; SrcPair; RowRel; MachRow; hot~; RegRel; []; _∷_; read~; cold~; defer~; mach; Partners; ArrRel; ArrRows; Store; Arr; SameAt)
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
