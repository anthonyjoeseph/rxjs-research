{-# OPTIONS --guardedness #-}

-- A COLD LEAF.  Subscribed, its tape is its timeline's stream from the
-- subscription, and owes every row of it.  A value or its end delivered
-- moves the cursor past it, owing the tape's rest, whose rows the frame's
-- next slot leads; a stall or a frame's close drops a skip, which no
-- cursor owes, so the tape's rest owes what the tape owed.  The next
-- frame's timer lies past the closed frame's end at a later tick, so its
-- root is reachable.
module adequacy.Cold where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; [_]; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (zero; suc; _+_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; +-suc; +-monoʳ-≤; m≤m+n; m<m+n)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Tree using (cold)
open import denotation.Events using (Pos; ix; last; tick; Timeline; timelineAt; From; Frame; done; quiet; at; emit; stall; close;
  Frame∞; From∞; module Frame∞; module From∞; frames; burst; start)
open import denotation.EmissionSet using (EmissionSet; out; skip; end; _≺_; InE; at-out; at-skip; at-end; on-out; on-skip)
open import denotation.Read using (Visible)
open import denotation.Laws.Modulus using (≺-irrefl; ≺→≼; ≺-≼-≺)
open import denotation.Laws.Worlds using (Ok; Hots; InvAt; Real)
open import denotation.Laws.ColdInv using (slot; burst-lb; cold-reach; next-real)
open import operation.PureObservable using (module Machine; Tape; play; ending; opening; rest) renaming (over to tapeOver)
open Machine using (Scope; coldS)
open import adequacy.Rows using (_≃_; _⇄_; ≃-sym; ≃-trans; full; pendRows; tapeE)
open import adequacy.Cursor using (origin; bef; aft; Owes; Due; Sync; s-cold; s-coldx; Ticked; Within; Adm; _≈_; voc; tail-≈)
open import adequacy.Walk using (due-≈)
open import adequacy.SubOne using (module Entry)

open _≃_

------------------------------------------------------------------------
-- A tape's stream

open-tape : ∀ {A} q (m : From A 0) → tapeE (opening q m) ≡ start q m
open-tape q (at zero _ b)    = refl
open-tape q (at (suc _) _ b) = refl
open-tape q done             = refl
open-tape q quiet            = refl

rest-frames : ∀ {A t} τ e (m : From A t) → tapeE (rest τ e m) ≡ frames τ e m
rest-frames τ e done        = refl
rest-frames τ e quiet       = refl
rest-frames τ e (at _ _ _)  = refl

-- Subscribed at a reachable position: its frame played at or after it.
open-ticked : ∀ {A} q (m : From A 0) → Real q → Ticked (opening q m)
open-ticked q (at zero _ b)    rq = rq , m≤m+n (tick q) 0
open-ticked q (at (suc n) _ b) rq = next-real (tick q) q rq (m<m+n (tick q) (s≤s z≤n)) , ≤-refl
open-ticked q done             rq = tt
open-ticked q quiet            rq = tt

-- A frame closed: the next one played past its end.
rest-ticked : ∀ {A} τ u {t} → Real u → tick u ≤ τ + t → (m : From A (suc t)) → Ticked (rest τ (u ++ [ last ]) m)
rest-ticked τ u     ru le done             = tt
rest-ticked τ u     ru le quiet            = tt
rest-ticked τ u {t} ru le (at t′ le′ _)    =
  next-real τ u ru (≤-trans (s≤s le) (subst (_≤ τ + t′) (+-suc τ t) (+-monoʳ-≤ τ le′))) , ≤-refl

------------------------------------------------------------------------
-- Subscribed

-- A tape read off its entry: owing every row the entry has.
settle-cold : ∀ {Γ} {sc : Scope Γ} {Rg} {C} {A} {l : Tape A} {P E : EmissionSet A}
            → Ticked l → P ≈ E → (∀ {r e} → P r e → InE (tapeE l) r e) → (∀ {r e} → InE (tapeE l) r e → P r e)
            → (∀ {r e} → InE (tapeE l) r e → Owes C r × Rg r) → Sync sc Rg C (coldS true l) E
settle-cold {C = C} tk m to′ from′ ow =
  s-cold tk (≃-trans (≃-sym (due-≈ {C = C} m)) ((λ (r , v , _) → to′ r , v , tt) ⇄ (λ (r , v , _) → from′ r , v , proj₁ (ow r))))
         (tail-≈ {C = C} m ([] , λ r _ → inj₁ (to′ r)))
         (λ r → proj₁ (ow r) , voc m (from′ r) , proj₂ (ow r))

cold-sync : ∀ {Γ} {sc : Scope Γ} {Rg} {C} {A} (x : Timeline A) q (ok : Ok (Hots (full sc)) q) (ad : Adm sc) → Owes C q
          → ∀ {E} → pendRows (full sc) (cold x) q ≈ E → Within Rg sc q (pendRows (full sc) (cold x) q)
          → Sync sc Rg C (coldS true (opening q (timelineAt x q))) E
cold-sync {sc = sc} {Rg} {C} x q ok ad ow eq wi = settle-cold (open-ticked q m (proj₁ ok)) eq to′ from′ owr
  where
    open Entry sc (cold x) q ok ad

    m = timelineAt x q

    to′ : ∀ {r e} → S r e → InE (tapeE (opening q m)) r e
    to′ y = subst (λ ev → InE ev _ _) (sym (open-tape q m)) (proj₁ y)

    from′ : ∀ {r e} → InE (tapeE (opening q m)) r e → S r e
    from′ y = let y′ = subst (λ ev → InE ev _ _) (open-tape q m) y in y′ , cold-reach q m (proj₁ ok) y′

    owr : ∀ {r e} → InE (tapeE (opening q m)) r e → Owes C r × Rg r
    owr y = owed {C = C} ow (from′ y) , proj₂ wi (InvAt.world Io (from′ y)) (λ y₁ pl w le → InvAt.under Io y₁ (from′ y) pl w le)

------------------------------------------------------------------------
-- A step played

-- A value delivered: the cursor past it owes the frame's rest.
cold-nx : ∀ {Γ} {sc : Scope Γ} {Rg} {A} {τ u i t a} {k : Frame A t} {E : EmissionSet A}
        → Sync sc Rg (bef (u ++ [ ix i ])) (coldS true (play τ u i t (emit a k))) E
        → Sync sc Rg (aft (u ++ [ ix i ])) (coldS true (play τ u (suc i) t k)) E × E (u ++ [ ix i ]) (out a)
cold-nx {Rg = Rg} {τ = τ} {u} {i} {t} {a} {k} {E} (s-cold tk@(ru , le) du (ks , tl) tw) =
  s-cold tk du′ (ks , tl′) tw′ , proj₁ (from du (at-out , tt , tt))
  where
    p = u ++ [ ix i ]

    past : ∀ {y e} → InE (burst τ u (suc i) k) y e → p ≺ y
    past {y} r = ≺-≼-≺ {p} {u ++ [ ix (suc i) ]} {y} (slot u i) (burst-lb τ u (suc i) k ru le r)

    peel : ∀ {y e} → InE (burst τ u i (emit a k)) y e → p ≺ y → InE (burst τ u (suc i) k) y e
    peel at-out     pp = ⊥-elim (≺-irrefl {p} pp)
    peel (on-out r) _  = r

    du′ : Due (aft p) E ≃ Due origin (InE (burst τ u (suc i) k))
    du′ = (λ (r , v , pk) → peel (proj₁ (to du (r , v , ≺→≼ {p} pk))) pk , v , tt)
        ⇄ (λ (r , v , _) → proj₁ (from du (on-out r , v , tt)) , proj₁ (proj₂ (from du (on-out r , v , tt))) , past r)

    tl′ : ∀ {y e} → E y e → p ≺ y → InE (burst τ u (suc i) k) y e ⊎ y ∈ ks
    tl′ r pk with tl r (≺→≼ {p} pk)
    ... | inj₁ r′ = inj₁ (peel r′ pk)
    ... | inj₂ m  = inj₂ m

    tw′ : ∀ {y e} → InE (burst τ u (suc i) k) y e → p ≺ y × E y e × Rg y
    tw′ r = let (_ , ey , g) = tw (on-out r) in past r , ey , g

-- Its end delivered: the cursor past it owes nothing.
cold-cp : ∀ {Γ} {sc : Scope Γ} {Rg} {A} {e} {E : EmissionSet A}
        → Sync sc Rg (bef e) (coldS true (ending e)) E
        → Sync sc Rg (aft e) (coldS false tapeOver) E × E e end
cold-cp {A = A} {e} {E} (s-cold _ du (ks , tl) _) = s-coldx sp (ks , fn) , proj₁ (from du (at-end , tt , tt))
  where
    gone : ∀ {y ev} → InE (tapeE {A} (ending e)) y ev → e ≺ y → ⊥
    gone at-end pp = ≺-irrefl {e} pp

    sp : ∀ {y ev} → Due (aft e) E y ev → ⊥
    sp (r , v , pk) = gone (proj₁ (to du (r , v , ≺→≼ {e} pk))) pk

    fn : ∀ {y ev} → E y ev → e ≺ y → y ∈ ks
    fn r pk with tl r (≺→≼ {e} pk)
    ... | inj₁ r′ = ⊥-elim (gone r′ pk)
    ... | inj₂ m  = m

-- A skip dropped: what the tape owed, its rest owes.
cold-drop : ∀ {Γ} {sc : Scope Γ} {Rg} {C} {A} {l l′ : Tape A} {E} (y₀ : Pos) → (Ticked l → Ticked l′)
          → (∀ {y e} → InE (tapeE l′) y e → InE (tapeE l) y e)
          → (∀ {y e} → InE (tapeE l) y e → InE (tapeE l′) y e ⊎ (y ≡ y₀ × e ≡ skip))
          → Sync sc Rg C (coldS true l) E → Sync sc Rg C (coldS true l′) E
cold-drop {C = C} {l′ = l′} {E} y₀ tk′ into back (s-cold tk du (ks , tl) tw) = s-cold (tk′ tk) du′ (y₀ ∷ ks , tl′) (λ r → tw (into r))
  where
    vis : ∀ {y e} → InE (tapeE l′) y e ⊎ (y ≡ y₀ × e ≡ skip) → Visible e → InE (tapeE l′) y e
    vis (inj₁ r)          _ = r
    vis (inj₂ (_ , refl)) ()

    du′ = (λ d → let (r , v , o) = to du d in vis (back r) v , v , o) ⇄ (λ (r , v , o) → from du (into r , v , o))

    tl′ : ∀ {y e} → E y e → Owes C y → InE (tapeE l′) y e ⊎ y ∈ (y₀ ∷ ks)
    tl′ r o with tl r o
    ... | inj₂ m = inj₂ (there m)
    ... | inj₁ x with back x
    ...   | inj₁ x′          = inj₁ x′
    ...   | inj₂ (refl , _)  = inj₂ (here refl)

-- A stall: its skip dropped.
stall-into : ∀ {A τ u i t} {k : Frame∞ A t} {y e}
           → InE (tapeE (play τ u (suc i) t (Frame∞.force k))) y e → InE (tapeE (play τ u i t (stall k))) y e
stall-into r = on-skip r

stall-back : ∀ {A τ u i t} {k : Frame∞ A t} {y e}
           → InE (tapeE (play τ u i t (stall k))) y e → InE (tapeE (play τ u (suc i) t (Frame∞.force k))) y e ⊎ (y ≡ u ++ [ ix i ] × e ≡ skip)
stall-back at-skip     = inj₂ (refl , refl)
stall-back (on-skip r) = inj₁ r

-- A close: its skip dropped, the next frame on.
close-into : ∀ {A τ u i t} {k : From∞ A (suc t)} {y e}
           → InE (tapeE (rest τ (u ++ [ last ]) (From∞.force k))) y e → InE (tapeE (play τ u i t (close k))) y e
close-into {τ = τ} {u} {k = k} r = on-skip (subst (λ ev → InE ev _ _) (rest-frames τ (u ++ [ last ]) (From∞.force k)) r)

close-back : ∀ {A τ u i t} {k : From∞ A (suc t)} {y e}
           → InE (tapeE (play τ u i t (close k))) y e → InE (tapeE (rest τ (u ++ [ last ]) (From∞.force k))) y e ⊎ (y ≡ u ++ [ ix i ] × e ≡ skip)
close-back                 at-skip     = inj₂ (refl , refl)
close-back {τ = τ} {u} {k = k} (on-skip r) = inj₁ (subst (λ ev → InE ev _ _) (sym (rest-frames τ (u ++ [ last ]) (From∞.force k))) r)
