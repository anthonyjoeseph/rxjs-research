{-# OPTIONS --guardedness #-}

-- A HOT REJOINED: a reader's rows, each named by the hot row it hangs
-- under, few and listed where the hot's are; and how a joined row
-- matches its hot row.
module simultaneous.Rejoined where

open import Data.Bool.Properties using (T?)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_]; filter)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻; ∈-filter⁺; ∈-filter⁻; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.All using (lookup; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import denotation.Position using (Pos; Path; sub; last; _⊕_; _<ᵖ_; root; _≟ᵖ_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Unpinned; EmissionSet; hot; coldAt; Proper; DenEnv; Few; Reach;
  Truncate; Rejoin; shown; heard; ended; late; _≺_; _≼_)
open import denotation.Laws.Modulus using (≺-irrefl; ≺-trans; ≺-≼-≺; ≺→≼; ≼-split)
open import denotation.Laws.Worlds using (_⊑_; ⊑-snoc; ⊕-assoc; ⊕-identityʳ; ⊕-injˡ; ⊕-injʳ; here)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Attribution using (Shown; Match; Every; One; Reads)
open import simultaneous.Listing using (Listed)
open import simultaneous.CarryBase using (apart)
open import simultaneous.Carry using (HotsListed; Apart; annValues; hots-at)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; elab; annotate; joinStep)

-- No row of `S` lies strictly under another.
Flat : ∀ {A} → EmissionSet A → Set
Flat S = ∀ {y e l ys e′} → S y e → S (y ⊕ (l ∷ ys)) e′ → ⊥

-- A point one label under `z`, read under `q`: `z` is `q`, or lies
-- under `q`'s step.
split-at : ∀ q {a σ} z {b} → z ⊕ [ b ] ≡ q ⊕ (a ∷ σ) → (q ≡ z × a ≡ b) ⊎ Σ Path λ zs → z ≡ q ⊕ (a ∷ zs)
split-at q {a} {σ} z eq with ⊑-snoc {q ⊕ [ a ]} z (σ , trans eq (sym (⊕-assoc q [ a ] σ)))
... | inj₂ e        = inj₁ (⊕-injˡ q z e , ⊕-injʳ q z e)
... | inj₁ (zs , e) = inj₂ (zs , trans e (⊕-assoc q [ a ] zs))

-- A position holding rows of two hots of an apart environment: one
-- handle.
same-hot : ∀ {Γ} (env : DenEnv Γ) → Apart env → ∀ {X Y} (i : X ∈ Γ) (j : Y ∈ Γ) {t : EmissionSet X} {t′ : EmissionSet Y}
         → lookup env i ≡ hot t → lookup env j ≡ hot t′ → ∀ {q} → ¬ ¬ Σ (Ev X) (t q) → ¬ ¬ Σ (Ev Y) (t′ q)
         → (P : ∀ {Z} → Z ∈ Γ → Set) → P i → P j
same-hot (hot _ ∷ _)    _        (here refl) (here refl) _    _    _  _   _ x = x
same-hot (hot _ ∷ ρ)    (a , _)  (here refl) (there j)   refl e′   tq tq′ _ _ = ⊥-elim (tq λ r → tq′ λ r′ → a (proj₂ r) (hots-at ρ j e′ (proj₂ r′)))
same-hot (hot _ ∷ ρ)    (a , _)  (there i)   (here refl) e    refl tq tq′ _ _ = ⊥-elim (tq λ r → tq′ λ r′ → a (proj₂ r′) (hots-at ρ i e (proj₂ r)))
same-hot (hot _ ∷ ρ)    (_ , ap) (there i)   (there j)   e    e′   tq tq′ P x = same-hot ρ ap i j e e′ tq tq′ (λ k → P (there k)) x
same-hot (coldAt _ ∷ _) _        (here refl) _           ()   _    _  _   _ _
same-hot (coldAt _ ∷ _) _        (there _)   (here refl) _    ()   _  _   _ _
same-hot (coldAt _ ∷ ρ) ap       (there i)   (there j)   e    e′   tq tq′ P x = same-hot ρ ap i j e e′ tq tq′ (λ k → P (there k)) x

-- Two rows of a flat set, one before the other, are apart.
nest : ∀ {A} {S : EmissionSet A} → Flat S → ∀ {x y e e′} → S x e → S y e′ → x ≺ y → ¬ (x ⊑ y)
nest fl {x} sx sy xy ([] , refl) = ≺-irrefl {x} (subst (x ≺_) (⊕-identityʳ x) xy)
nest fl sx sy xy (l ∷ ys , refl) = fl sx sy

-- Joined at one label, the order read back.
joined-back : ∀ x y {a} → (x ⊕ [ a ]) ≺ (y ⊕ [ a ]) → (y ≺ x → ¬ (y ⊑ x)) → x ≺ y
joined-back x y {a} h ny with T? (x <ᵖ y)
... | yes xy = xy
... | no nxy with ≼-split {y} {x} nxy
...   | inj₂ refl = ⊥-elim (≺-irrefl {x ⊕ [ a ]} h)
...   | inj₁ yx = ⊥-elim (≺-irrefl {x ⊕ [ a ]} (≺-trans {x ⊕ [ a ]} {y ⊕ [ a ]} {x ⊕ [ a ]} h (apart yx (ny yx) [ a ] [ a ])))

few-reach : ∀ {A} {S : EmissionSet A} {q e} → Few S q → Reach S q e
few-reach (ks , F) = ks , λ r h _ → F r h

-- What a joiner hears of a row: a pin as a skip.
rjEv : ∀ {A} → Ev A → Ev A
rjEv (out x) = out x
rjEv skip    = skip
rjEv end     = end
rjEv (pin _) = skip

rjUnp : ∀ {A} (e : Ev A) → Unpinned (rjEv e)
rjUnp (out _) = tt
rjUnp skip    = tt
rjUnp end     = tt
rjUnp (pin _) = tt

rjRow : ∀ {A} {S : EmissionSet A} {j q e} → Proper S q e → j ≺ q → Rejoin j (Proper S) (q ⊕ [ sub j ]) (rjEv e)
rjRow {e = out _} r h = shown r tt h
rjRow {e = skip}  r h = shown r tt h
rjRow {e = end}   r h = ended r h
rjRow {e = pin _} r h = heard r h

-- Before a joined row, the joined rows before its row, and the late end.
-- The row's own presence is read only to set it apart, so held classically.
rejoin-few¬¬ : ∀ {A} {S : EmissionSet A} {j q} → Flat S → ¬ ¬ Σ (Ev A) (S q) → Few S q → Few (Rejoin j (Proper S)) (q ⊕ [ sub j ])
rejoin-few¬¬ {S = S} {j} {q} fl sq (ks , F) = L.map (_⊕ [ sub j ]) ks ++ [ j ⊕ [ last ] ] , pick
  where
    apt : ∀ {q′ e′} → S q′ e′ → q ≺ q′ → ¬ (q ⊑ q′)
    apt r qq le = sq λ s → nest {S = S} fl (proj₂ s) r qq le

    pick : ∀ {k e′} → Rejoin j (Proper S) k e′ → k ≺ (q ⊕ [ sub j ]) → k ∈ L.map (_⊕ [ sub j ]) ks ++ [ j ⊕ [ last ] ]
    pick (shown {q′} r _ _) h = ∈-++⁺ˡ (∈-map⁺ (_⊕ [ sub j ]) (F (proj₁ r) (joined-back q′ q h (apt (proj₁ r)))))
    pick (heard {q′} r _)   h = ∈-++⁺ˡ (∈-map⁺ (_⊕ [ sub j ]) (F (proj₁ r) (joined-back q′ q h (apt (proj₁ r)))))
    pick (ended {q′} r _)   h = ∈-++⁺ˡ (∈-map⁺ (_⊕ [ sub j ]) (F (proj₁ r) (joined-back q′ q h (apt (proj₁ r)))))
    pick (late _ _)         _ = ∈-++⁺ʳ (L.map (_⊕ [ sub j ]) ks) (here refl)

rejoin-few : ∀ {A} {S : EmissionSet A} {j q e} → Flat S → S q e → Few S q → Few (Rejoin j (Proper S)) (q ⊕ [ sub j ])
rejoin-few {S = S} {j} fl sq = rejoin-few¬¬ {S = S} {j} fl (λ n → n (_ , sq))

-- Past an end at or before the subscription, nothing before the late end.
late-none : ∀ {A} {S : EmissionSet A} {j c r e} → Proper S c end → c ≼ j → Rejoin j (Proper S) r e → r ≺ (j ⊕ [ last ]) → ⊥
late-none {j = j} {c} (sc , _) cj (shown {q} (_ , lv) _ jq) _ = cj (≺-≼-≺ {j} {q} {c} jq (lv sc))
late-none {j = j} {c} (sc , _) cj (heard {q} (_ , lv) jq)   _ = cj (≺-≼-≺ {j} {q} {c} jq (lv sc))
late-none {j = j} {c} (sc , _) cj (ended {q} (_ , lv) jq)   _ = cj (≺-≼-≺ {j} {q} {c} jq (lv sc))
late-none {j = j} _ _ (late _ _) h = ≺-irrefl {j ⊕ [ last ]} h

-- A proper row listed, joined past the subscription: its joined rows listed.
rejoin-listed : ∀ {A} {S : EmissionSet A} {j l₀ e₀} → Flat S → Proper S l₀ e₀ → j ≺ l₀ → Listed S l₀
              → Listed (Truncate (Rejoin j (Proper S))) (l₀ ⊕ [ sub j ])
rejoin-listed {S = S} {j} {l₀} fl (sl , lv) jl (ks , F , B) = cand , (λ r h → pick (proj₁ r) h) , out′
  where
    cand : List Pos
    cand = L.map (_⊕ [ sub j ]) (filter (λ k → T? (j <ᵖ k)) ks)

    at : ∀ {q e′} → S q e′ → j ≺ q → (q ⊕ [ sub j ]) ≺ (l₀ ⊕ [ sub j ]) → q ⊕ [ sub j ] ∈ cand
    at {q} sq jq h = ∈-map⁺ (_⊕ [ sub j ]) (∈-filter⁺ (λ k → T? (j <ᵖ k)) (F sq (joined-back q l₀ h (nest {S = S} fl sl sq))) jq)

    pick : ∀ {k e′} → Rejoin j (Proper S) k e′ → k ≺ (l₀ ⊕ [ sub j ]) → k ∈ cand
    pick (shown r _ jq) h = at (proj₁ r) jq h
    pick (heard r jq)   h = at (proj₁ r) jq h
    pick (ended r jq)   h = at (proj₁ r) jq h
    pick (late {c} r cj) _ = ⊥-elim (cj (≺-≼-≺ {j} {l₀} {c} jl (lv (proj₁ r))))

    out′ : ∀ {x} → x ∈ cand → x ≺ (l₀ ⊕ [ sub j ]) × Σ _ (Truncate (Rejoin j (Proper S)) x)
    out′ m with ∈-map⁻ (_⊕ [ sub j ]) m
    ... | k , mk , refl with ∈-filter⁻ (λ k → T? (j <ᵖ k)) mk
    ...   | mk′ , jk with B mk′
    ...     | kl , e , sk =
      kx , rjEv e , rjRow (sk , λ {c} tc → ≺→≼ {k} {c} (≺-≼-≺ {k} {l₀} {c} kl (lv tc))) jk , cand , λ {y} r h _ → pick r (≺-trans {y} {k ⊕ [ sub j ]} {l₀ ⊕ [ sub j ]} h kx)
      where
        kx : (k ⊕ [ sub j ]) ≺ (l₀ ⊕ [ sub j ])
        kx = apart {k} {l₀} kl (nest {S = S} fl sk sl kl) [ sub j ] [ sub j ]

-- Every hot of an environment listed: the one at a handle.
listed-at : ∀ {Γ} (env : DenEnv Γ) {Y} (j : Y ∈ Γ) {t : EmissionSet Y} → lookup env j ≡ hot t → ∀ {q} → HotsListed env q → Listed t q
listed-at (hot _ ∷ _)    (here refl) refl (L , _) = L
listed-at (coldAt _ ∷ _) (here refl) ()   _
listed-at (hot _ ∷ ρ)    (there j)   e    (_ , R) = listed-at ρ j e R
listed-at (coldAt _ ∷ ρ) (there j)   e    R       = listed-at ρ j e R

-- Listed proper up to a proper row: listed.
proper-listed : ∀ {A} {S : EmissionSet A} {q} → Listed (Proper S) q → (∀ {c} → S c end → q ≼ c) → Listed S q
proper-listed {q = q} (ks , F , B) lv =
  ks , (λ {k} r kq → F (r , λ {c} tc → ≺→≼ {k} {c} (≺-≼-≺ {k} {q} {c} kq (lv tc))) kq) , λ m → let (kq , e , r) = B m in kq , e , proj₁ r

-- The rows of a reading, each named by its hot row.
one : ∀ {A} {S : EmissionSet A} {j y e} → Rejoin j S y e → List Pos
one (shown {q} _ _ _) = [ q ]
one (heard {q} _ _)   = [ q ]
one (ended {c} _ _)   = [ c ]
one (late _ _)        = []

last-sub : ∀ {x} → last ≡ sub x → ⊥
last-sub ()

one-in : ∀ {A} {S : EmissionSet A} {j y e q} (r : Rejoin j S y e) → y ≡ q ⊕ [ sub j ] → q ∈ one r
one-in {q = q} (shown {q′} _ _ _) eq = here (⊕-injˡ q q′ (sym eq))
one-in {q = q} (heard {q′} _ _)   eq = here (⊕-injˡ q q′ (sym eq))
one-in {q = q} (ended {q′} _ _)   eq = here (⊕-injˡ q q′ (sym eq))
one-in {j = j} {q = q} (late _ _) eq = ⊥-elim (last-sub (⊕-injʳ j q eq))

one-out : ∀ {A} {S : EmissionSet A} {j y e q} (r : Rejoin j S y e) → q ∈ one r → Σ _ (S q)
one-out (shown r _ _) (here refl) = _ , r
one-out (heard r _)   (here refl) = _ , r
one-out (ended r _)   (here refl) = _ , r
one-out (late _ _)    ()

djs : ∀ {A} {S : EmissionSet A} {j} (xs : List Pos) → (∀ {x} → x ∈ xs → Σ _ (Truncate (Rejoin j S) x)) → List Pos
djs []       g = []
djs (x ∷ xs) g = one (proj₁ (proj₂ (g (here refl)))) ++ djs xs (λ m → g (there m))

djs-in : ∀ {A} {S : EmissionSet A} {j q} (xs : List Pos) (g : ∀ {x} → x ∈ xs → Σ _ (Truncate (Rejoin j S) x))
       → q ⊕ [ sub j ] ∈ xs → q ∈ djs xs g
djs-in (x ∷ xs) g (here refl) = ∈-++⁺ˡ (one-in (proj₁ (proj₂ (g (here refl)))) refl)
djs-in (x ∷ xs) g (there m)   = ∈-++⁺ʳ (one (proj₁ (proj₂ (g (here refl))))) (djs-in xs (λ m′ → g (there m′)) m)

djs-out : ∀ {A} {S : EmissionSet A} {j q} (xs : List Pos) (g : ∀ {x} → x ∈ xs → Σ _ (Truncate (Rejoin j S) x))
        → q ∈ djs xs g → Σ _ (S q)
djs-out (x ∷ xs) g m with ∈-++⁻ (one (proj₁ (proj₂ (g (here refl))))) m
... | inj₁ m′ = one-out (proj₁ (proj₂ (g (here refl)))) m′
... | inj₂ m′ = djs-out xs (λ m″ → g (there m″)) m′

-- A shown row is shown on the other side; a skip is not.
mt-rj : ∀ {X} {e : Ev X} {e′ : Ev (AIE X)} → Unpinned e → Match Every (One annValues) (Reads annValues) e e′
      → Match Every (One annValues) (Reads annValues) e (rjEv e′)
mt-rj {e′ = out _} _ m = m
mt-rj {e′ = skip}  _ m = m
mt-rj {e′ = end}   _ m = m
mt-rj {e = out _} {e′ = pin _} _ (c , _) with c tt
... | _ , () , _
mt-rj {e = skip}  {e′ = pin _} _ _ = (λ ()) , λ _ ()
mt-rj {e = end}   {e′ = pin _} _ (c , _) with c tt
... | ()
mt-rj {e = pin _} {e′ = pin _} () _

shown-unp : ∀ {X} {e : Ev X} {e′ : Ev (AIE X)} → Shown Every e → Match Every (One annValues) (Reads annValues) e e′ → Unpinned e′
shown-unp {e = out _} _ (c , _) with c tt
... | _ , refl , _ = tt
shown-unp {e = end}   _ (c , _) with c tt
... | refl = tt
shown-unp {e = skip}  () _
shown-unp {e = pin _} () _

out-of : ∀ {X} {e₀ : Ev X} {x} → Match Every (One annValues) (Reads annValues) e₀ (out x) → One annValues x → Σ X λ a → e₀ ≡ out a
out-of {e₀ = out a} _ _ = a , refl
out-of {e₀ = skip}  (_ , n) sh = ⊥-elim (n (λ ()) sh)
out-of {e₀ = pin _} (_ , n) sh = ⊥-elim (n (λ ()) sh)
out-of {e₀ = end}   (c , _) _ with c tt
... | ()

end-of : ∀ {X} {e₀ : Ev X} → Match Every (One annValues) (Reads annValues) e₀ (end {A = AIE X}) → e₀ ≡ end
end-of {e₀ = out _} (c , _) with c tt
... | _ , () , _
end-of {e₀ = end}   _ = refl
end-of {e₀ = skip}  (_ , n) = ⊥-elim (n (λ ()) tt)
end-of {e₀ = pin _} (_ , n) = ⊥-elim (n (λ ()) tt)
