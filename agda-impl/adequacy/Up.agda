{-# OPTIONS --guardedness #-}

-- THE CURSOR MOVED PAST A ROW A NODE CANNOT HAVE.  A node whose region
-- misses `p`, under binders none of which has a visible row at `p`, owes
-- the same past `p` as from `p`: its rows, its children's, its lanes',
-- and what its joiners are still to be fed all lie elsewhere.  So when a
-- connect's body rises at `p`, its source, apart from it, moves past `p`
-- with nothing delivered.
module adequacy.Up where

open import Data.Bool using (T; true; false; _∧_)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (lookup) renaming (_∷_ to _∷ᴬ_; [] to []ᴬ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Relation.Nullary using (¬_)
open import Data.Maybe using (just)

open import denotation.Events using (Pos)
open import denotation.Read using (Visible)
open import denotation.EmissionSet using (EmissionSet; Ev; out; _≺_; Den; hot; coldAt; DenEnv; shown; heard; ended; late;
  module TakeWhile; module Connecting)
open import denotation.Laws.Modulus using (≺→≼; ≺-trans)
open import denotation.Laws.Worlds using (Hots)
open import operation.PureObservable using (module Machine)
open Machine using (St; Ctx; Conf; ⟨_,_,_,_⟩; Scope; binds; CS; scopeOf; connS; rising; nx; cp; inBody) renaming (Ev to Evᴹ)
open import adequacy.Rows using (_≃_; _⇄_; ≃-sym; ≃-trans; ≼-≢; full)
open _≃_
open import adequacy.Cursor using (bef; aft; Pol; Runs; Start; Ahead; Whole; OuterDone; owes; Owes; Due; Spent; Unfed; Rgn;
  Sound; vis; h-live; h-end; h-kill; LaneSt; l-live; l-dead; Begun; none; more; Folded;
  fd-none; fd-last; Joined; joined; Flags; Src; src-pend; src-on; src-shut; Parts; OweAt; o-cp;
  o-cut; o-over; Sync; s-cold; s-of; s-done; s-map; s-scan; s-cut; s-take; s-took; s-flat;
  s-conn; s-join; s-joinx; Fr; f-off; f-body; u-body; settled; flying; adrift; SimC; keeps)

-- A visible row of a binder in scope at `p`.
VHot : ∀ {Γ} → DenEnv Γ → Pos → Set
VHot []ᴬ             _ = ⊥
VHot (hot t ∷ᴬ ρ)    p = (Σ (Ev _) λ e → t p e × Visible e) ⊎ VHot ρ p
VHot (coldAt _ ∷ᴬ ρ) p = VHot ρ p

vhot-hots : ∀ {Γ} (ρ : DenEnv Γ) {p} → VHot ρ p → Hots ρ p
vhot-hots (hot t ∷ᴬ ρ)    (inj₁ (e , y , _)) = inj₁ (e , y)
vhot-hots (hot t ∷ᴬ ρ)    (inj₂ h)           = inj₂ (vhot-hots ρ h)
vhot-hots (coldAt _ ∷ᴬ ρ) h                  = vhot-hots ρ h

module Past (p : Pos) where

  -- Owed from `p` and not at it.
  owes-up : ∀ {q} → (p ≡ q → ⊥) → Owes (bef p) q → Owes (aft p) q
  owes-up {q} ne o = ≼-≢ {p} {q} o ne

  dn : ∀ {q} → Owes (aft p) q → Owes (bef p) q
  dn {q} = ≺→≼ {p} {q}

  nm : ∀ {q} → ¬ Owes (bef p) q → ¬ Owes (aft p) q
  nm n o = n (dn o)

  -- A row in a region missing `p` is not at `p`.
  off : ∀ {Rg : Rgn} {q} → ¬ Rg p → Rg q → p ≡ q → ⊥
  off nr r refl = nr r

  in-rg : ∀ {Rg : Rgn} {A} {E : EmissionSet A} {q e} → Sound Rg E → ¬ Rg p → E q e → Visible e → Owes (bef p) q → Owes (aft p) q
  in-rg sd nr y v = owes-up (off nr (Sound.rg sd y v))

  due-up : ∀ {Rg : Rgn} {A} {E : EmissionSet A} → Sound Rg E → ¬ Rg p → Due (bef p) E ≃ Due (aft p) E
  due-up sd nr = (λ (y , v , o) → y , v , in-rg sd nr y v o) ⇄ (λ (y , v , o) → y , v , dn o)

  spent-up : ∀ {A} {E : EmissionSet A} → Spent (bef p) E → Spent (aft p) E
  spent-up sp (y , v , o) = sp (y , v , dn o)

  -- A joiner's unfed rows: its binder has no visible row at `p`.
  unfed-aft : ∀ {Γ A} (ρ : DenEnv Γ) (x : A ∈ Γ) {j q e} → ¬ VHot ρ p → p ≺ q
            → Due (bef p) (Unfed (bef p) (lookup ρ x) j) q e → Due (aft p) (Unfed (aft p) (lookup ρ x) j) q e
  unfed-aft (hot t ∷ᴬ ρ) (here refl) nh pq (shown (y , o) b jq , v , _) =
    shown (y , owes-up (λ { refl → nh (inj₁ (_ , y , v)) }) o) b jq , v , pq
  unfed-aft (hot t ∷ᴬ ρ) (here refl) nh pq (heard _ _ , () , _)
  unfed-aft (hot t ∷ᴬ ρ) (here refl) nh pq (ended (y , o) jc , v , _) =
    ended (y , owes-up (λ { refl → nh (inj₁ (_ , y , _)) }) o) jc , v , pq
  unfed-aft (hot t ∷ᴬ ρ) (here refl) nh pq (late (y , o) cj , v , _) =
    late (y , owes-up (λ { refl → nh (inj₁ (_ , y , _)) }) o) cj , v , pq
  unfed-aft (coldAt _ ∷ᴬ ρ) (here refl) nh pq (() , _ , _)
  unfed-aft (hot t ∷ᴬ ρ)    (there x) nh pq u = unfed-aft ρ x (λ h → nh (inj₂ h)) pq u
  unfed-aft (coldAt _ ∷ᴬ ρ) (there x) nh pq u = unfed-aft ρ x nh pq u

  unfed-bef : ∀ {A j} (d : Den A) → ∀ {q e} → Due (aft p) (Unfed (aft p) d j) q e → Due (bef p) (Unfed (bef p) d j) q e
  unfed-bef (hot t) (shown (y , o) b jq , v , w) = shown (y , dn o) b jq , v , dn w
  unfed-bef (hot t) (heard (y , o) jq , v , w)   = heard (y , dn o) jq , v , dn w
  unfed-bef (hot t) (ended (y , o) jc , v , w)   = ended (y , dn o) jc , v , dn w
  unfed-bef (hot t) (late (y , o) cj , v , w)    = late (y , dn o) cj , v , dn w
  unfed-bef (coldAt _) (() , _ , _)

  fold-up : ∀ {Rg : Rgn} {A B} {f : B → A → B} {z₀ z} {Es} → Sound Rg Es → ¬ Rg p
          → Folded (bef p) f z₀ Es z → Folded (aft p) f z₀ Es z
  fold-up sd nr (fd-none h)       = fd-none λ y → in-rg sd nr y _ (h y)
  fold-up sd nr (fd-last ac nq h) = fd-last ac (nm nq) λ y qk → in-rg sd nr y _ (h y qk)

  -- The binder a connect adds has its rows in its source's region.
  bind-nh : ∀ {Γ X} {k : CS Γ X} {Rs : Rgn} → Sound Rs (adequacy.Rows.Frozen k) → ¬ Rs p → ¬ VHot (full (CS.scope k)) p
          → ¬ VHot (full (binds (CS.src k) (CS.connAt k) (CS.scope k))) p
  bind-nh ss nr nh (inj₁ (_ , (y , _) , v)) = nr (Sound.rg ss y v)
  bind-nh ss nr nh (inj₂ h)                 = nh h

  flags-up : ∀ {Γ X B} {k : CS Γ X} {β : EmissionSet B} {Rs : Rgn} → Sound Rs (adequacy.Rows.Frozen k) → ¬ Rs p
           → Flags (bef p) k β → Flags (aft p) k β
  flags-up {β = β} ss nr fl = record
    { shut   = λ c → proj₁ (Flags.shut fl c) , nm (proj₂ (Flags.shut fl c))
    ; unshut = λ t y n → Flags.unshut fl t y λ o → n (in-rg ss nr y _ o)
    ; torn   = λ nt → spent-up {E = β} (Flags.torn fl nt) }

  mutual
    up : ∀ {Γ} {sc : Scope Γ} {Rg A} {s : St Γ A} {E} → Sync sc Rg (bef p) s E → Sound Rg E → ¬ Rg p → ¬ VHot (full sc) p
       → Sync sc Rg (aft p) s E
    up (s-cold tk d)           sd nr nh = s-cold tk (≃-trans (≃-sym (due-up sd nr)) d)
    up (s-of d)                sd nr nh = s-of (≃-trans (≃-sym (due-up sd nr)) d)
    up {E = E} (s-done sp)     sd nr nh = s-done (spent-up {E = E} sp)
    up (s-map sy m sm)         sd nr nh = s-map (up sy sm nr nh) m sm
    up (s-scan sy fd m sm)     sd nr nh = s-scan (up sy sm nr nh) (fold-up sm nr fd) m sm
    up (s-cut sy)              sd nr nh = s-cut (up sy sd nr nh)
    up (s-take sy nf m sm)     sd nr nh = s-take (up sy sm nr nh) (λ y nk → in-rg sm nr y _ (nf y nk)) m sm
    up {A = A} (s-took {i = i} {keep = keep} {Es = Es} {r = r} fl@(a , y , nk , nf) g ni oa m sm) sd nr nh =
      s-took fl (λ {q} o → g {q} (dn o)) (λ t → nm (ni t)) (owe-up oa) m sm
      where
        -- its completion is one of its rows
        owe-up : ∀ {w} → OweAt (bef p) w r → OweAt (aft p) w r
        owe-up (o-cp o)   = o-cp (in-rg sd nr (proj₁ (to m (TakeWhile.stop y nk nf , vis {A = A} cp))) (vis {A = A} cp) o)
        owe-up (o-cut n)  = o-cut (nm n)
        owe-up (o-over n) = o-over (nm n)
    up (s-flat sy jn m so)     sd nr nh = s-flat (up sy so nr nh) (joined-up so nr nh jn) m so
    up (s-conn {k = k} refl pt bs ss fl m) sd nr nh =
      s-conn refl pt (λ t → up (bs t) (Parts.sb pt) nb (bind-nh {k = k} (Parts.ss pt) ns nh))
             (λ t → src-up (ss t) (Parts.ss pt) ns nh) (flags-up {k = k} (Parts.ss pt) ns fl) m
      where
        nb = λ r → nr (Parts.b⊆ pt r)
        ns = λ r → nr (Parts.s⊆ pt r)
    up {sc = sc} (s-join {x = x} {E = E} en d ap hd adm) sd nr nh =
      s-join en d′ ap (λ i u → hd i (unfed-bef (lookup (full sc) x) u)) adm
      where
        d′ = (λ (y , v , o) → [ inj₁ , (λ u → inj₂ (unfed-aft (full sc) x nh o u)) ]′ (to d (y , v , dn o)))
           ⇄ λ { (inj₁ i) → let (y , v , o) = from d (inj₁ i) in y , v , in-rg sd nr y v o
               ; (inj₂ u) → let (y , v , _) = from d (inj₂ (unfed-bef (lookup (full sc) x) u)) in y , v , proj₂ (proj₂ u) }
    up {E = E} (s-joinx sp)    sd nr nh = s-joinx (spent-up {E = E} sp)

    src-up : ∀ {Γ X} {sc : Scope Γ} {Rs : Rgn} {k : CS Γ X} {o}
           → Src sc Rs (bef p) k o → Sound Rs (adequacy.Rows.Frozen k) → ¬ Rs p → ¬ VHot (full sc) p → Src sc Rs (aft p) k o
    src-up (src-pend be adm pr wn) ss nr nh = src-pend be adm pr wn
    src-up (src-on nc sy)          ss nr nh = src-on nc (up sy ss nr nh)
    src-up {k = k} (src-shut cl sp) ss nr nh = src-shut cl (spent-up {E = adequacy.Rows.Frozen k} sp)

    joined-up : ∀ {Γ} {sc : Scope Γ} {Rg A B} {P : Pol A B} {O : EmissionSet A} {d n qu ls}
              → Sound Rg O → ¬ Rg p → ¬ VHot (full sc) p → Joined sc Rg (bef p) P O d n qu ls → Joined sc Rg (aft p) P O d n qu ls
    joined-up {P = P} {O} so nr nh (joined {vs = vs} {ws = ws} bg (eq , ap , wf) wh od ah en li) =
      joined (begun-up bg) (eq , ap , wait) whole od′ ahead en li
      where
        lane-up : ∀ {q a l b} → LaneSt _ _ (bef p) P q a l b → LaneSt _ _ (aft p) P q a l b
        lane-up (l-live (h-live st ns e) sy sd) = l-live (h-live st (nm ns) e) (up sy sd nr nh) sd
        lane-up (l-dead {E = E} (h-end lc nc))  = l-dead {E = E} (h-end lc (nm nc))
        lane-up (l-dead {E = E} (h-kill kq nq)) = l-dead {E = E} (h-kill kq (nm nq))

        begun-up : ∀ {vs ls n} → Begun _ _ (bef p) P O vs ls n → Begun _ _ (aft p) P O vs ls n
        begun-up none                = none
        begun-up (more y nq r ln bg) = more y (nm nq) r (lane-up ln) (begun-up bg)

        begun-out : ∀ {vs ls n q a} → Begun _ _ (bef p) P O vs ls n → (q , a) ∈ vs → O q (out a)
        begun-out (more y _ _ _ _) (here refl) = y
        begun-out (more _ _ _ _ bg) (there i)  = begun-out bg i

        ahead : Ahead (aft p) P vs ws
        ahead iw st with ah iw st
        ... | q′ , a′ , c , iv , lc , kc , oc , cz =
          q′ , a′ , c , iv , lc , kc , owes-up (off nr (li (begun-out bg iv) lc _)) oc , cz

        wait : ∀ {q a} → (q , a) ∈ ws → O q (out a) × ¬ Owes (aft p) q × Runs P q × (∀ {s} → Start P q a s → Owes (aft p) s)
        wait iw with wf iw
        ... | y , nq , r , _ = y , nm nq , r , λ {s} st → let (_ , _ , c , _ , _ , _ , oc , cz) = ahead iw st in ≺-trans {p} {c} {s} oc cz

        whole : Whole (aft p) P O vs ws
        whole y nq r = wh y (λ o → nq (in-rg so nr y _ o)) r

        od′ : OuterDone (aft p) O _
        od′ = (λ t → let (c , y , n) = proj₁ od t in c , y , nm n)
            , (λ y n → proj₂ od y λ o → n (in-rg so nr y _ o))

------------------------------------------------------------------------
-- A BODY'S RISE while its source runs: the row is the connect's, and
-- the source, apart from the body, moves past it.

-- Where a connect owes its own end is no part of what it owes.
src-owe : ∀ {Γ X} {sc : Scope Γ} {Rs : Rgn} {C} {k : CS Γ X} {o x} → Src sc Rs C k o → Src sc Rs C (record k { owedAt = x }) o
src-owe (src-pend be adm pr wn) = src-pend be adm pr wn
src-owe (src-on nc sy)          = src-on nc sy
src-owe (src-shut cl sp)        = src-shut cl sp

re-owe : ∀ {Γ X B} {sc : Scope Γ} {Rg : Rgn} {C} {k : CS Γ X} {o} {b : St (X ∷ Γ) B} {E x}
       → Sync sc Rg C (connS k o b) E → Sync sc Rg C (connS (record k { owedAt = x }) o b) E
re-owe (s-conn sc pt bs ss fl m) =
  s-conn sc (record { Rb = Parts.Rb pt ; Rs = Parts.Rs pt ; b⊆ = Parts.b⊆ pt ; s⊆ = Parts.s⊆ pt ; apart = Parts.apart pt
                    ; clear = Parts.clear pt ; sb = Parts.sb pt ; ss = Parts.ss pt })
         bs (λ t → src-owe (ss t)) (record { shut = Flags.shut fl ; unshut = Flags.unshut fl ; torn = Flags.torn fl }) m

wl : ∀ w {b} → b ≡ true → T w → T (w ∧ b)
wl true  refl _ = _
wl false _    ()

wf : ∀ w {b} → b ≡ true → false ≡ w ∧ b → w ≡ false
wf true  refl ()
wf false _    _ = refl

module _ {R : Set} (Rt : EmissionSet R) where

  rise-body : ∀ {Γ X B} {k : CS Γ X} {o} {c : Ctx R Γ B} {s e p} {k′ : CS Γ X} → CS.srcLive k ≡ true
            → (∀ {Rg C E} → Sync (scopeOf c) Rg C (connS k o s) E → Sync (scopeOf c) Rg C (connS k′ o s) E)
            → SimC Rt ⟨ inBody k o c , s , rising e , p ⟩ [] ⟨ c , connS k′ o s , rising e , p ⟩
  rise-body {k = k} {c = c} {e = e} {p = p} lv fix = keeps Rt λ
    { (flying (f-body {w = w} fr sc pt v src fl eq) h) → flying fr λ t →
        let (sy , row) = h (subst T (sym v) (wl w lv t))
            rb = Sound.rg (Parts.sb pt) row (vis e)
            ns = λ r → Parts.apart pt rb r
            nh = λ hv → Parts.clear pt (vhot-hots (full (scopeOf c)) hv) (Parts.b⊆ pt rb)
        in fix (s-conn sc pt (λ _ → subst (λ x → Sync (binds (CS.src k) (CS.connAt k) x) _ _ _ _) sc sy)
                      (λ t′ → Past.src-up p (src t′) (Parts.ss pt) ns nh) (Past.flags-up p {k = k} (Parts.ss pt) ns fl) eq)
           , proj₁ (to eq (Connecting.body row , vis e))
    ; (flying (f-off u-body fr) _)             → flying fr λ ()
    ; (adrift (f-body {w = w} fr _ _ v _ _ _)) → adrift (subst (λ x → Fr Rt _ _ _ (owes x) _) (wf w lv v) fr)
    ; (adrift (f-off u-body fr))               → adrift fr
    ; (settled () _ _) }

  rise-body-nx : ∀ {Γ X B} {k : CS Γ X} {o} {c : Ctx R Γ B} {s b p} → CS.srcLive k ≡ true
               → SimC Rt ⟨ inBody k o c , s , rising (nx b) , p ⟩ [] ⟨ c , connS k o s , rising (nx b) , p ⟩
  rise-body-nx lv = rise-body lv λ sy → sy

  rise-body-cp : ∀ {Γ X B} {k : CS Γ X} {o} {c : Ctx R Γ B} {s p} → CS.srcLive k ≡ true
               → SimC Rt ⟨ inBody k o c , s , rising cp , p ⟩ [] ⟨ c , connS (record k { owedAt = just p }) o s , rising cp , p ⟩
  rise-body-cp lv = rise-body lv re-owe
