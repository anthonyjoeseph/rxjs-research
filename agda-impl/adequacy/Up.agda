{-# OPTIONS --guardedness #-}

-- THE CURSOR MOVED PAST A ROW A NODE CANNOT HAVE.  A node whose region
-- misses `p`, under binders none of which has a visible row at `p`, owes
-- the same past `p` as from `p`: its rows, its children's, its lanes',
-- and what its joiners are still to be fed all lie elsewhere.  So when a
-- connect's body rises at `p`, its source, apart from it, moves past `p`
-- with nothing delivered.
module adequacy.Up where

open import Data.Bool using (Bool; T; true; false; not; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; []; _∷_; [_]; _++_; map)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ʳ; ∈-++⁺ˡ; ∈-map⁺)
open import Data.List.Relation.Unary.AllPairs using () renaming (_∷_ to _∷ᴾ_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (lookup) renaming (_∷_ to _∷ᴬ_; [] to []ᴬ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Relation.Nullary using (¬_)
open import Data.Maybe using (just)

open import denotation.Events using (Pos; ix; Timeline)
open import Tree using (Obs)
open import denotation.Read using (Visible)
open import denotation.EmissionSet using (EmissionSet; Ev; out; end; Proper; ⟦_⟧; MapT; map-out; map-end; map-skip; map-pin; module Scan; _≺_; Den; hot; coldAt; DenEnv; shown; heard; ended; late;
  module TakeWhile; module Connecting; Reach; Truncate)
open import denotation.Laws.Modulus using (≺→≼; ≺-trans; ≺-irrefl; ≺-ext; ≼-antisym)
open import denotation.Laws.Worlds using (Hots; W⁼)
open import operation.PureObservable using (module Machine)
open Machine using (St; Ctx; Conf; ⟨_,_,_,_⟩; Scope; binds; CS; scopeOf; connS; rising; nx; cp; inBody; inSrc; feed; feedL; rise; moved; shutAt; absorbed) renaming (Ev to Evᴹ)
open import adequacy.Rows using (_≃_; _⇄_; ≃-sym; ≃-trans; ≃-refl; ≼-≢; full; Frozen; pendRows; Moves; silent; toEv)
open _≃_
open import adequacy.Walk using (sync-≈)
open import adequacy.Cursor using (Cur; bef; aft; Behind; Fin; Tail; fin-dn; tail-dn; alike; ≈-sym; FewBefore; ConnE; Need; owes; dead; lane; lanecut; pnd; _≈_; c-abs; Pol; Ahead; Whole; OuterDone; Owes; Due; Spent; Unfed; Rgn; Sound; vis; h-live; h-end; h-kill; LaneSt; l-live; l-dead; Begun; none; more; Folded; fd-none; fd-last; Joined; joined; Flags; Src; src-pend; src-on; src-shut; Parts; OweAt; o-cp; o-cut; o-over; Sync; s-cold; s-of; s-done; s-map; s-scan; s-cut; s-take; s-took; s-flat; s-conn; s-join; s-joinx; Fr; Waiting; Lane; JRl; JRo; JInv; Asc; f-top; f-map; f-scan; f-cut; f-take; f-took; f-outer; f-lanes; f-lane; f-lnct; f-src; f-srcc; f-srcp; f-body; d-map; d-scan; d-cut; d-ln; d-take; d-outer; d-lanes; d-src; d-body; f-isle; f-islec; f-islep; polF; JoinF; LanesIn; NoFail; TailP; tailp-dn; Subd; SubdAt; subd; Torn; Unread; un-dead; un-torn; notT; by; Husk; HuskL; h-blank; h-map; h-scan; h-cut; h-ln; h-take; h-flat; h-conn; hl-none; hl-more; SrcH; sh-dead; sh-isle; sh-islec; sh-pend; husk-of; ⊑-trans; ∪-⊑; ⊑-refl; under-⊑; NoIsle; NoIsleL; Settles; sync-pend)
open import adequacy.Cursor.Rise using (Inv; RT; settled; flying; adrift; SimC; keeps; unread-at)
open import adequacy.Bound using (join-row; owes?; few-src)
open import adequacy.Regions using (lane-sole)

-- A visible row of a binder in scope at `p`.
VHot : ∀ {Γ} → DenEnv Γ → Pos → Set
VHot []ᴬ             _ = ⊥
VHot (hot t ∷ᴬ ρ)    p = (Σ (Ev _) λ e → t p e × Visible e) ⊎ VHot ρ p
VHot (coldAt _ ∷ᴬ ρ) p = VHot ρ p

vhot-hots : ∀ {Γ} (ρ : DenEnv Γ) {p} → VHot ρ p → Hots ρ p
vhot-hots (hot t ∷ᴬ ρ)    (inj₁ (e , y , _)) = inj₁ (e , y)
vhot-hots (hot t ∷ᴬ ρ)    (inj₂ h)           = inj₂ (vhot-hots ρ h)
vhot-hots (coldAt _ ∷ᴬ ρ) h                  = vhot-hots ρ h

-- A begun lane's value.
begun-out : ∀ {Γ} {sc : Scope Γ} {Rl C A B} {P : Pol A B} {O : EmissionSet A} {vs ls n q a}
          → Begun sc Rl C P O vs ls n → (q , a) ∈ vs → O q (out a)
begun-out (more y _ _ _ _) (here refl) = y
begun-out (more _ _ _ _ bg) (there i)  = begun-out bg i

module Past (p : Pos) where

  -- Owed from `p` and not at it.
  owes-up : ∀ {q} → (p ≡ q → ⊥) → Owes (bef p) q → Owes (aft p) q
  owes-up {q} ne o = ≼-≢ {p} {q} o ne

  dn : ∀ {q} → Owes (aft p) q → Owes (bef p) q
  dn {q} = ≺→≼ {p} {q}

  nm : ∀ {q} → ¬ Owes (bef p) q → ¬ Owes (aft p) q
  nm n o = n (dn o)

  -- Passed once the row at `p` is: one more row.
  behind-up : ∀ {A} {E : EmissionSet A} → Behind (bef p) E → Behind (aft p) E
  behind-up (ks , f) = p ∷ ks , λ {y} r n → [ (λ o → here (sym (≼-antisym {p} {y} o n))) , (λ no → there (f r no)) ]′ (owes? (bef p) y)

  -- A row in a region missing `p` is not at `p`.
  off : ∀ {Rg : Rgn} {q} → ¬ Rg p → Rg q → p ≡ q → ⊥
  off nr r refl = nr r

  -- No visible row at `p`.
  Off : ∀ {A} → EmissionSet A → Set
  Off E = ∀ {q e} → E q e → Visible e → p ≡ q → ⊥

  off-rg : ∀ {Rg : Rgn} {A} {E : EmissionSet A} → Sound Rg E → ¬ Rg p → Off E
  off-rg sd nr y v = off nr (Sound.rg sd y v)

  in-off : ∀ {A} {E : EmissionSet A} {q e} → Off E → E q e → Visible e → Owes (bef p) q → Owes (aft p) q
  in-off of y v = owes-up (of y v)

  in-rg : ∀ {Rg : Rgn} {A} {E : EmissionSet A} {q e} → Sound Rg E → ¬ Rg p → E q e → Visible e → Owes (bef p) q → Owes (aft p) q
  in-rg sd nr = in-off (off-rg sd nr)

  due-up : ∀ {Rg : Rgn} {A} {E : EmissionSet A} → Sound Rg E → ¬ Rg p → Due (bef p) E ≃ Due (aft p) E
  due-up sd nr = (λ (y , v , o) → y , v , in-rg sd nr y v o) ⇄ (λ (y , v , o) → y , v , dn o)

  spent-up : ∀ {A} {E : EmissionSet A} → Spent (bef p) E → Spent (aft p) E
  spent-up sp (y , v , o) = sp (y , v , dn o)

  fin-up : ∀ {A} {E : EmissionSet A} → Fin (bef p) E → Fin (aft p) E
  fin-up = fin-dn {C = bef p} {C′ = aft p} (λ {y} → dn {y})

  tail-up : ∀ {A} {E T : EmissionSet A} → Tail (bef p) E T → Tail (aft p) E T
  tail-up = tail-dn {C = bef p} {C′ = aft p} (λ {y} → dn {y})

  tailp-up : ∀ {A} {E : EmissionSet A} {P} → TailP (bef p) E P → TailP (aft p) E P
  tailp-up = tailp-dn {C = bef p} {C′ = aft p} (λ {y} → dn {y})

  subd-up : ∀ {Γ} {sc : Scope Γ} {r} → SubdAt sc (bef p) r → SubdAt sc (aft p) r
  subd-up (subd f ok) = subd (λ {y} o → f {y} (dn {y} o)) ok

  torn-up : ∀ {Γ X B} {sc : Scope Γ} {k : CS Γ X} {o} {b : St (X ∷ Γ) B} {β} → Torn sc (bef p) k o b β → Torn sc (aft p) k o b β
  torn-up t = record { Ps = Torn.Ps t ; Pb = Torn.Pb t ; sh = Torn.sh t ; bh = Torn.bh t ; tl = tailp-up (Torn.tl t) }

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

  fold-up : ∀ {A B} {f : B → A → B} {z₀ z} {Es} → Off Es → Folded (bef p) f z₀ Es z → Folded (aft p) f z₀ Es z
  fold-up of (fd-none h)       = fd-none λ y → in-off of y _ (h y)
  fold-up of (fd-last ac nq h) = fd-last ac (nm nq) λ y qk → in-off of y _ (h y qk)

  -- The binder a connect adds has its rows in its source's region.
  bind-nh : ∀ {Γ X} {k : CS Γ X} → Off (Frozen k) → ¬ VHot (full (CS.scope k)) p
          → ¬ VHot (full (binds (CS.src k) (CS.connAt k) (CS.scope k))) p
  bind-nh of nh (inj₁ (_ , (y , _) , v)) = of y v refl
  bind-nh of nh (inj₂ h)                 = nh h

  flags-up : ∀ {Γ X B} {k : CS Γ X} {β : EmissionSet B} → Off (Frozen k) → Flags (bef p) k β → Flags (aft p) k β
  flags-up {β = β} of fl = record
    { shut   = λ c → proj₁ (Flags.shut fl c) , nm (proj₂ (Flags.shut fl c))
    ; unshut = λ t y n → Flags.unshut fl t y λ o → n (in-off of y _ o)
    ; torn   = λ nt → spent-up {E = β} (Flags.torn fl nt) }

  -- A joiner's bookkeeping past `p`: its outer's rows and its lanes'
  -- ends not at `p`.
  module Book {A B} {P : Pol A B} {O : EmissionSet A} (oo : Off O) where
    whole-up : ∀ {vs ws} → Whole (bef p) P O vs ws → Whole (aft p) P O vs ws
    whole-up wh y nq r = wh y (λ o → nq (in-off oo y _ o)) r

    od-up : ∀ {d} → OuterDone (bef p) O d → OuterDone (aft p) O d
    od-up od = (λ t → let (c , y , n) = proj₁ od t in c , y , nm n)
             , (λ y n → proj₂ od y λ o → n (in-off oo y _ o))

    ahead-up : ∀ {vs ws} → (∀ {q a c} → (q , a) ∈ vs → Lane P q a c end → p ≡ c → ⊥) → Ahead (bef p) P vs ws → Ahead (aft p) P vs ws
    ahead-up le ah iw st with ah iw st
    ... | q′ , a′ , c , iv , lc , kc , oc , cz = q′ , a′ , c , iv , lc , kc , owes-up (le iv lc) oc , cz

    wait-up : ∀ {vs ws qu} → Ahead (aft p) P vs ws → Waiting (bef p) P O ws qu → Waiting (aft p) P O ws qu
    wait-up ah (eq , ap , wf) = eq , ap , λ iw → let (y , nq , r , _) = wf iw in
      y , nm nq , r , λ {s} st → let (_ , _ , c , _ , _ , _ , oc , cz) = ah iw st in ≺-trans {p} {c} {s} oc cz

  mutual
    up : ∀ {Γ} {sc : Scope Γ} {Rg A} {s : St Γ A} {E} → Sync sc Rg (bef p) s E → Sound Rg E → ¬ Rg p → ¬ VHot (full sc) p
       → Sync sc Rg (aft p) s E
    up (s-cold tk d tl)        sd nr nh = s-cold tk (≃-trans (≃-sym (due-up sd nr)) d) (tail-up tl)
    up (s-of d tl)             sd nr nh = s-of (≃-trans (≃-sym (due-up sd nr)) d) (tail-up tl)
    up {E = E} (s-done sp fn)  sd nr nh = s-done (spent-up {E = E} sp) (fin-up fn)
    up (s-map sy m sm)         sd nr nh = s-map (up sy sm nr nh) m sm
    up (s-scan sy fd m sm)     sd nr nh = s-scan (up sy sm nr nh) (fold-up (off-rg sm nr) fd) m sm
    up (s-cut sy)              sd nr nh = s-cut (up sy sd nr nh)
    up (s-take sy nf m sm)     sd nr nh = s-take (up sy sm nr nh) (λ y nk → in-rg sm nr y _ (nf y nk)) m sm
    up {A = A} (s-took {i = i} {keep = keep} {Es = Es} {r = r} fl@(a , y , nk , nf) g ni oa tp hk m sm) sd nr nh =
      s-took fl (λ {q} o → g {q} (dn o)) (λ t → nm (ni t)) (owe-up oa) (tailp-up tp) hk m sm
      where
        -- its completion is one of its rows
        owe-up : ∀ {w} → OweAt (bef p) w r → OweAt (aft p) w r
        owe-up (o-cp o)   = o-cp (in-rg sd nr (proj₁ (to (alike m) (TakeWhile.stop y nk nf , vis {A = A} cp))) (vis {A = A} cp) o)
        owe-up (o-cut n)  = o-cut (nm n)
        owe-up (o-over n) = o-over (nm n)
    up (s-flat ji sy jn m so bh) sd nr nh =
      s-flat ji (up sy so no nh) (joined-up (off-rg so no) (λ r → nr (proj₁ r)) nh jn) m so (behind-up bh)
      where no = λ r → nr (proj₁ r)
    up (s-conn {k = k} refl pt bs ss tn fl m) sd nr nh =
      s-conn refl pt (λ t → up (bs t) (Parts.sb pt) nb (bind-nh {k = k} (off-rg (Parts.ss pt) ns) nh))
             (λ t → src-up (ss t) (Parts.ss pt) ns nh) (λ nt → torn-up (tn nt)) (flags-up {k = k} (off-rg (Parts.ss pt) ns) fl) m
      where
        nb = λ r → nr (Parts.b⊆ pt r)
        ns = λ r → nr (Parts.s⊆ pt r)
    up {sc = sc} (s-join {x = x} {E = E} en d ap hd adm) sd nr nh =
      s-join en d′ ap (λ i u → hd i (unfed-bef (lookup (full sc) x) u)) adm
      where
        d′ = (λ (y , v , o) → [ inj₁ , (λ u → inj₂ (unfed-aft (full sc) x nh o u)) ]′ (to d (y , v , dn o)))
           ⇄ λ { (inj₁ i) → let (y , v , o) = from d (inj₁ i) in y , v , in-rg sd nr y v o
               ; (inj₂ u) → let (y , v , _) = from d (inj₂ (unfed-bef (lookup (full sc) x) u)) in y , v , proj₂ (proj₂ u) }
    up {E = E} (s-joinx sp fn) sd nr nh = s-joinx (spent-up {E = E} sp) (fin-up fn)

    src-up : ∀ {Γ X} {sc : Scope Γ} {Rs : Rgn} {k : CS Γ X} {o}
           → Src sc Rs (bef p) k o → Sound Rs (adequacy.Rows.Frozen k) → ¬ Rs p → ¬ VHot (full sc) p → Src sc Rs (aft p) k o
    src-up (src-pend na nc be adm pr wn ow) ss nr nh = src-pend na nc be adm pr wn (owes-up (off nr (wn W⁼.here)) ow)
    src-up (src-on nc sy bh sd af ao)    ss nr nh = src-on nc (up sy ss nr nh) (behind-up bh) (subd-up sd) af ao
    src-up {k = k} (src-shut cl sp tp hk bh sd) ss nr nh =
      src-shut cl (spent-up {E = adequacy.Rows.Frozen k} sp) (tailp-up tp) hk (behind-up bh) (subd-up sd)

    lane-up : ∀ {Γ} {sc : Scope Γ} {Rg : Rgn} {A B} {P : Pol A B} {q a l b} → ¬ Rg p → ¬ VHot (full sc) p
            → LaneSt sc Rg (bef p) P q a l b → LaneSt sc Rg (aft p) P q a l b
    lane-up nr nh (l-live (h-live st ns e) sy sd) = l-live (h-live st (nm ns) e) (up sy sd nr nh) sd
    lane-up nr nh (l-dead {E = E} (h-end {c = c} lc nc tp) hk)    = l-dead {E = E} (h-end lc (nm {c} nc) (tailp-up tp)) hk
    lane-up nr nh (l-dead {E = E} (h-kill {q′ = q′} kq nq tp) hk) = l-dead {E = E} (h-kill kq (nm {q′} nq) (tailp-up tp)) hk

    begun-up : ∀ {Γ} {sc : Scope Γ} {Rl : Pos → Rgn} {A B} {P : Pol A B} {O : EmissionSet A} {vs ls n}
             → (∀ {q a} → (q , a) ∈ vs → ¬ Rl q p) → ¬ VHot (full sc) p
             → Begun sc Rl (bef p) P O vs ls n → Begun sc Rl (aft p) P O vs ls n
    begun-up nl nh none                = none
    begun-up nl nh (more y nq r ln bg) = more y (nm nq) r (lane-up (nl (here refl)) nh ln) (begun-up (λ i → nl (there i)) nh bg)

    joined-up : ∀ {Γ} {sc : Scope Γ} {Rl : Pos → Rgn} {A B} {P : Pol A B} {O : EmissionSet A} {d n qu ls}
              → Off O → (∀ {q} → ¬ Rl q p) → ¬ VHot (full sc) p → Joined sc Rl (bef p) P O d n qu ls → Joined sc Rl (aft p) P O d n qu ls
    joined-up {P = P} oo nl nh (joined bg wt wh od ah ao en li) =
      joined (begun-up (λ _ → nl) nh bg) (wait-up ah′ wt) (whole-up wh) (od-up od) ah′ ao en li
      where
        open Book {P = P} oo
        ah′ = ahead-up (λ iv lc → λ { refl → nl (li (begun-out bg iv) lc _) }) ah

------------------------------------------------------------------------
-- A BODY'S RISE while its source runs: the row is the connect's, and
-- the source, apart from the body, moves past it.

-- Where a connect owes its own end is no part of what it owes.
src-owe : ∀ {Γ X} {sc : Scope Γ} {Rs : Rgn} {C} {k : CS Γ X} {o x} → Src sc Rs C k o → Src sc Rs C (record k { owedAt = x }) o
src-owe (src-pend na nc be adm pr wn ow) = src-pend na nc be adm pr wn ow
src-owe (src-on nc sy bh sd af ao)     = src-on nc sy bh sd af ao
src-owe (src-shut cl sp tp hk bh sd)   = src-shut cl sp tp hk bh sd

srch-owe : ∀ {Γ X} {sc : Scope Γ} {k : CS Γ X} {o P x} → SrcH sc k o P → SrcH sc (record k { owedAt = x }) o P
srch-owe (sh-dead hk)                    = sh-dead hk
srch-owe (sh-isle na nc sy bh sd ss ao)  = sh-isle na nc sy bh sd ss ao
srch-owe (sh-islec na cl sp tp hk bh sd) = sh-islec na cl sp tp hk bh sd
srch-owe (sh-pend na nc ba sc adm pe wn ss) = sh-pend na nc ba sc adm pe wn ss

husk-owe : ∀ {Γ X B} {sc : Scope Γ} {k : CS Γ X} {o} {b : St (X ∷ Γ) B} {P x}
         → Husk sc (connS k o b) P → Husk sc (connS (record k { owedAt = x }) o b) P
husk-owe h-blank        = h-blank
husk-owe (h-conn sh hb) = h-conn (srch-owe sh) hb

torn-owe : ∀ {Γ X B} {sc : Scope Γ} {C} {k : CS Γ X} {o} {b : St (X ∷ Γ) B} {β x}
         → Torn sc C k o b β → Torn sc C (record k { owedAt = x }) o b β
torn-owe t = record { Ps = Torn.Ps t ; Pb = Torn.Pb t ; sh = srch-owe (Torn.sh t) ; bh = Torn.bh t ; tl = Torn.tl t }

re-owe : ∀ {Γ X B} {sc : Scope Γ} {Rg : Rgn} {C} {k : CS Γ X} {o} {b : St (X ∷ Γ) B} {E x}
       → Sync sc Rg C (connS k o b) E → Sync sc Rg C (connS (record k { owedAt = x }) o b) E
re-owe (s-conn sc pt bs ss tn fl m) =
  s-conn sc (record { Rb = Parts.Rb pt ; Rs = Parts.Rs pt ; b⊆ = Parts.b⊆ pt ; s⊆ = Parts.s⊆ pt ; apart = Parts.apart pt
                    ; clear = Parts.clear pt ; sb = Parts.sb pt ; ss = Parts.ss pt })
         bs (λ t → src-owe (ss t)) (λ nt → torn-owe (tn nt)) (record { shut = Flags.shut fl ; unshut = Flags.unshut fl ; torn = Flags.torn fl }) m

-- A connect's rows before a body row: its body's before it, and its
-- source's before it.
conn-reach : ∀ {A B} {r p : Pos} {σ : EmissionSet A} {β : EmissionSet B} {e} → FewBefore σ p → Reach β p e → Reach (Connecting.ConnT r σ β) p e
conn-reach (ks , fs) (bs , fb) = map (_++ [ ix 0 ]) ks ++ bs , λ
  { (Connecting.body x)       lt d → ∈-++⁺ʳ (map (_++ [ ix 0 ]) ks) (fb x lt d)
  ; (Connecting.burst x _)    lt _ → ∈-++⁺ˡ (∈-map⁺ (_++ [ ix 0 ]) (fs x lt))
  ; (Connecting.echo x _ _ _) lt _ → ∈-++⁺ˡ (∈-map⁺ (_++ [ ix 0 ]) (fs x lt))
  ; (Connecting.kept x _ _ _) lt _ → ∈-++⁺ˡ (∈-map⁺ (_++ [ ix 0 ]) (fs x lt)) }

-- A source closed at `p` owes, but for finitely many rows, what its
-- isles still run.  Every row past the end is invisible (`Sound.ends`),
-- so a skip or a pin.  A pin whose connect lies before the end is a pin
-- of a burst the cursor passed, and `pin-tail` places it.  What stays
-- open: the skips past the end, and a pin of a connect past it.  Each
-- former's rows past its end are of its parts' past theirs, and a
-- connect's burst pins and kept pins name connects before its body's end
-- (`Connecting.kept` asks `Alive`), so both reduce to the leaves: a
-- tape's rows past its entry's end, which `s-cold`'s `Tail` does not
-- tie to the entry.
-- DEAD ROUTE: `pin-tail` alone — it asks the pin's connect passed, which
--   an end at `p` does not give, and it says nothing of skips.
postulate
  shut-tail : ∀ {Γ X} {sc : Scope Γ} {Rs} {k : CS Γ X} {o : St Γ X} {p}
            → (sy : Sync sc Rs (aft p) o (Frozen k)) → Sound Rs (Frozen k) → Frozen k p end
            → TailP (aft p) (Frozen k) (proj₁ (husk-of sy))

-- A ROW FED TO A PART NO LIVE NODE READS, with no isle in it, keeps
-- what it still runs: a feed reaches joiners only.
mutual
  feed-husk : ∀ {Γ} {sc : Scope Γ} {X A} {i : X ∈ Γ} {p e} {s : St Γ A} {P} → Husk sc s P → NoIsle s → Husk sc (feed i p e s) P
  feed-husk h-blank        _              = h-blank
  feed-husk (h-map hk)     ni             = h-map (feed-husk hk ni)
  feed-husk (h-scan hk)    ni             = h-scan (feed-husk hk ni)
  feed-husk (h-cut hk)     ni             = h-cut (feed-husk hk ni)
  feed-husk (h-ln hk)      ni             = h-ln (feed-husk hk ni)
  feed-husk (h-take hk)    ni             = h-take (feed-husk hk ni)
  feed-husk (h-flat ho hl) (no , nl)      = h-flat (feed-husk ho no) (feedL-husk hl nl)
  feed-husk (h-conn sh hb) (st , no , nb) = h-conn (srch-feed sh st no) (feed-husk hb nb)

  feedL-husk : ∀ {Γ} {sc : Scope Γ} {X A} {i : X ∈ Γ} {p e} {ls : List (St Γ A)} {P} → HuskL sc ls P → NoIsleL ls → HuskL sc (feedL i p e ls) P
  feedL-husk hl-none         _         = hl-none
  feedL-husk (hl-more hk hl) (ni , nl) = hl-more (feed-husk hk ni) (feedL-husk hl nl)

  srch-feed : ∀ {Γ} {sc : Scope Γ} {X Y} {i : X ∈ Γ} {p e} {k : CS Γ Y} {o P} → SrcH sc k o P → Settles k o → NoIsle o
            → SrcH sc k (feed i p e o) P
  srch-feed (sh-dead hk)                    _                 no = sh-dead (feed-husk hk no)
  srch-feed (sh-isle na _ _ _ _ _ _)        (inj₁ t)          _  = ⊥-elim (notT _ na t)
  srch-feed (sh-isle _ nc _ _ _ _ _)        (inj₂ (inj₁ t))   _  = ⊥-elim (notT _ nc t)
  srch-feed (sh-isle _ _ sy _ _ _ _)        (inj₂ (inj₂ pe))  _  = ⊥-elim (sync-pend pe sy)
  srch-feed (sh-islec na cl sp tp hk bh sd) _                 no = sh-islec na cl sp tp (feed-husk hk no) bh sd
  srch-feed sh@(sh-pend _ _ _ _ _ _ _ _)    _                 _  = sh

-- A shut flag set where its source runs; kept where it is torn down.
shut-live : ∀ {Γ X} {k : CS Γ X} {p} → T (CS.srcLive k) → shutAt p k ≡ record k { closed = true ; endAt = p }
shut-live {k = k} t with CS.srcLive k | t
... | true  | _ = refl
... | false | ()

shut-torn : ∀ {Γ X} {k : CS Γ X} {p} → T (not (CS.srcLive k)) → shutAt p k ≡ k
shut-torn {k = k} t with CS.srcLive k | t
... | true  | ()
... | false | _ = refl

shut-by : ∀ {Γ X} {k : CS Γ X} {p} (F : CS Γ X → Set₁)
        → (T (CS.srcLive k) → F (record k { closed = true ; endAt = p })) → (T (not (CS.srcLive k)) → F k) → F (shutAt p k)
shut-by {k = k} {p} F l t =
  by (CS.srcLive k) (λ lt → subst F (sym (shut-live {k = k} {p} lt)) (l lt)) (λ nt → subst F (sym (shut-torn {k = k} {p} nt)) (t nt))

module _ {R : Set} (Rt : EmissionSet R) where

  -- A connect read where its source runs is no torn one.
  unread-live : ∀ {Cr C Γ X B} {c : Ctx R Γ B} {k k″ : CS Γ X} {P} → T (CS.srcLive k) → Unread Rt Cr C c k P → Unread Rt Cr C c k″ P
  unread-live _  (un-dead fr)              = un-dead fr
  unread-live lv (un-torn _ _ _ nl _ _ _) = ⊥-elim (notT _ nl lv)

  rise-body : ∀ {Γ X B} {k : CS Γ X} {o} {c : Ctx R Γ B} {s e p} {k′ : CS Γ X} → CS.srcLive k ≡ true
            → (∀ {Rg C E} → Sync (scopeOf c) Rg C (connS k o s) E → Sync (scopeOf c) Rg C (connS k′ o s) E)
            → (∀ {P} → Husk (scopeOf c) (connS k o s) P → Husk (scopeOf c) (connS k′ o s) P)
            → SimC Rt ⟨ inBody k o c , s , rising e , p ⟩ [] ⟨ c , connS k′ o s , rising e , p ⟩
  rise-body {k = k} {c = c} {e = e} {p = p} lv fix fixc = keeps Rt λ
    { (flying (f-body fr sc pt _ src fl eq) cl (sy , row)) → flying fr cl
        (let rb = Sound.rg (Parts.sb pt) row (vis e)
             ns = λ r → Parts.apart pt rb r
             nh = λ hv → Parts.clear pt (vhot-hots (full (scopeOf c)) hv) (Parts.b⊆ pt rb)
         in fix (s-conn sc pt (λ _ → subst (λ x → Sync (binds (CS.src k) (CS.connAt k) x) _ _ _ _) sc sy)
                        (λ _ → Past.src-up p src (Parts.ss pt) ns nh) (λ nl → ⊥-elim (notT _ nl lt))
                        (Past.flags-up p {k = k} (Past.off-rg p (Parts.ss pt) ns) fl) eq)
          , proj₁ (to (alike (proj₁ eq)) ((Connecting.body row , conn-reach (few-src sc src) (proj₂ eq row)) , vis e)))
    ; (flying (d-body _ _ _) _ ())
    ; (adrift (d-body (un-dead fr) sh le) cl (Q , hk , le′)) → adrift fr cl (_ , fixc (h-conn sh hk) , ⊑-trans le (∪-⊑ ⊑-refl le′))
    ; (adrift (d-body (un-torn _ _ _ nl _ _ _) _ _) _ _) → ⊥-elim (notT _ nl lt)
    ; (settled () _ _) }
    where
      lt : T (CS.srcLive k)
      lt = subst T (sym lv) tt

  rise-body-nx : ∀ {Γ X B} {k : CS Γ X} {o} {c : Ctx R Γ B} {s b p} → CS.srcLive k ≡ true
               → SimC Rt ⟨ inBody k o c , s , rising (nx b) , p ⟩ [] ⟨ c , connS k o s , rising (nx b) , p ⟩
  rise-body-nx lv = rise-body lv (λ sy → sy) (λ h → h)

  rise-body-cp : ∀ {Γ X B} {k : CS Γ X} {o} {c : Ctx R Γ B} {s p} → CS.srcLive k ≡ true
               → SimC Rt ⟨ inBody k o c , s , rising cp , p ⟩ [] ⟨ c , connS (record k { owedAt = just p }) o s , rising cp , p ⟩
  rise-body-cp lv = rise-body lv re-owe husk-owe


------------------------------------------------------------------------
-- A SOURCE'S RISE: fed at once to its body's joiners.  Nothing leaves:
-- a connect shows its body's rows only, so the connect and every frame
-- above it move past `p`.

-- No visible row at `p`.
NoRow : ∀ {A} → EmissionSet A → Pos → Set
NoRow E p = ∀ {e} → E p e → Visible e → ⊥

-- A hole some live node reads.
Live : Need → Set
Live owes          = ⊤
Live (dead _)      = ⊥
Live (lane b _)    = T b
Live (lanecut b _) = T b
Live (pnd _)       = ⊥

-- Nothing at `p`: owed past it as from it.
due-nr : ∀ {A} {E : EmissionSet A} {p} → NoRow E p → Due (bef p) E ≃ Due (aft p) E
due-nr {p = p} nr = (λ (y , v , o) → y , v , Past.owes-up p (λ { refl → nr y v }) o) ⇄ (λ (y , v , o) → y , v , Past.dn p o)

-- Alike rows, alike at `p`.
nr-≈ : ∀ {A} {E E′ : EmissionSet A} {p} → E ≈ E′ → NoRow E p → NoRow E′ p
nr-≈ eq nr y v = let (y′ , v′) = from (alike eq) (y , v) in nr y′ v′

-- Truncated, still none at `p`.
nr-tr : ∀ {A} {E : EmissionSet A} {p} → NoRow E p → NoRow (Truncate E) p
nr-tr nr (y , _) v = nr y v

nr-off : ∀ {A} {E : EmissionSet A} {p} → NoRow E p → Past.Off p E
nr-off nr y v refl = nr y v

-- A frame shows at `p` only what its hole shows there.
map-nr : ∀ {A B} {f : A → B} {E p} → NoRow E p → NoRow (MapT f E) p
map-nr nr (map-out y)  v = nr y v
map-nr nr (map-end y)  v = nr y v
map-nr nr (map-skip _) ()
map-nr nr (map-pin _)  ()

scan-nr : ∀ {A B} {f : B → A → B} {z} {E : EmissionSet A} {p} → NoRow E p → NoRow (Scan.ScanT f z E) p
scan-nr nr (Scan.sval (Scan.acc₀ y _))    v = nr y v
scan-nr nr (Scan.sval (Scan.acc _ y _ _)) v = nr y v
scan-nr nr (Scan.send y)                  v = nr y v
scan-nr nr (Scan.sstep _)                 ()
scan-nr nr (Scan.spin _)                  ()

-- A failure's rows lie past its value, which the cursor has not passed.
take-nr : ∀ {A} {i} {keep : A → Bool} {E p} → NoRow E p → NoFail (bef p) keep E → NoRow (TakeWhile.TakeT i keep E) p
take-nr nr nf (TakeWhile.pass y _ _)       v = nr y v
take-nr nr nf (TakeWhile.fail {q} y nk _ _) _ = nf y nk (≺-ext q [])
take-nr nr nf (TakeWhile.stop {q} y nk _)  _ = nf y nk (≺-ext q [])
take-nr nr nf (TakeWhile.step _ _)         ()
take-nr nr nf (TakeWhile.tend y _)         v = nr y v
take-nr nr nf (TakeWhile.left _ _ _)       ()

-- A joiner's row at `p`: its outer's end, or a lane's, in that lane's
-- region.
join-nr : ∀ {A B} op (F : A → Den B) {O : EmissionSet A} {Rl : Pos → Rgn} {p}
        → LanesIn Rl (polF op F O) O → (O p end → ⊥)
        → (∀ {q a e} → O q (out a) → Lane (polF op F O) q a p e → Visible e → Rl q p → ⊥)
        → NoRow (JoinF op F O) p
join-nr op F {O} li ne nl r v with join-row op F O r v
... | inj₁ y                       = ne y
... | inj₂ (_ , _ , y , _ , ln , _) = nl y ln v (li y ln v)

joined-li : ∀ {Γ} {sc : Scope Γ} {Rl C A B} {P : Pol A B} {O d n qu ls} → Joined sc Rl C P O d n qu ls → LanesIn Rl P O
joined-li (joined _ _ _ _ _ _ _ li) = li

-- Begun lanes in order: those before a lane began before it, those
-- after, after.
asc-pre : ∀ {A} (xs : List (Pos × A)) {y ys x} → Asc (xs ++ y ∷ ys) → x ∈ xs → proj₁ x ≺ proj₁ y
asc-pre (_ ∷ xs) (h ∷ᴾ _) (here refl) = lookup h (∈-++⁺ʳ xs (here refl))
asc-pre (_ ∷ xs) (_ ∷ᴾ t) (there i)   = asc-pre xs t i

asc-post : ∀ {A} (xs : List (Pos × A)) {y ys x} → Asc (xs ++ y ∷ ys) → x ∈ ys → proj₁ y ≺ proj₁ x
asc-post []       (h ∷ᴾ _) i = lookup h i
asc-post (_ ∷ xs) (_ ∷ᴾ t) i = asc-post xs t i

conn-vis : ∀ {A B} {r : Pos} {σ : EmissionSet A} {β : EmissionSet B} {y e} → Truncate (Connecting.ConnT r σ β) y e → Visible e → β y e
conn-vis (Connecting.body x , _) _ = x
conn-vis (Connecting.burst _ _ , _) ()
conn-vis (Connecting.echo _ _ _ _ , _) ()
conn-vis (Connecting.kept _ _ _ _ , _) ()

or-shut : ∀ {x y} → T x → x ∨ y ≡ false → ⊥
or-shut {true} _ ()

torn : ∀ {ℓ} {b} {X : Set ℓ} → T (not b) → T b → X
torn {b = true}  () _
torn {b = false} _  ()

-- A connect's parts, its flags moved.
re-parts : ∀ {Γ X B} {sc : Scope Γ} {Rg} {k : CS Γ X} {β : EmissionSet B} {p}
         → Parts sc Rg k β → Parts sc Rg (record k { closed = true ; endAt = p }) β
re-parts pt = record { Rb = Parts.Rb pt ; Rs = Parts.Rs pt ; b⊆ = Parts.b⊆ pt ; s⊆ = Parts.s⊆ pt ; apart = Parts.apart pt
                     ; clear = Parts.clear pt ; sb = Parts.sb pt ; ss = Parts.ss pt }

module _ {R : Set} (Rt : EmissionSet R) where

  -- Nothing the root owes at `p`: it owes the same past it.
  nr-moves : ∀ {p} → NoRow Rt p → Moves (RT Rt (bef p)) [] (RT Rt (aft p))
  nr-moves nr = silent ((λ (x , v) → to d x , v) ⇄ (λ (x , v) → from d x , v))
    where d = due-nr {E = Rt} nr

  -- THE FRAMES ABOVE A ROW THEY DO NOT SHOW: a hole whose region holds
  -- `p` and whose entry has no visible row there, under binders none of
  -- which has one, moves every frame above it past `p`.  Every sibling's
  -- region is apart from the hole's, so it moves by `Past.up`.  The
  -- frames up to an isle are its world's: the root's cursor stays.
  fr-up : ∀ {Cr Γ A} {c : Ctx R Γ A} {Rg w E p} → Fr Rt Cr (bef p) Rg c w E → Live w → Rg p → NoRow E p
        → ¬ VHot (full (scopeOf c)) p → Σ Cur λ Cr′ → Fr Rt Cr′ (aft p) Rg c w E × Moves (RT Rt Cr) [] (RT Rt Cr′)
  fr-up {p = p} (f-top eq) _ _ nr _ = aft p , f-top eq , nr-moves (nr-≈ eq nr)
  fr-up (f-map fr m sd) _ rp nr nh =
    let (Cr′ , fr′ , mv) = fr-up fr tt rp (nr-≈ m (map-nr nr)) nh in Cr′ , f-map fr′ m sd , mv
  fr-up {p = p} (f-scan fr fd m sd) _ rp nr nh =
    let (Cr′ , fr′ , mv) = fr-up fr tt rp (nr-≈ m (scan-nr nr)) nh in Cr′ , f-scan fr′ (Past.fold-up p (nr-off nr) fd) m sd , mv
  fr-up (f-cut fr) _ rp nr nh = let (Cr′ , fr′ , mv) = fr-up fr tt rp nr nh in Cr′ , f-cut fr′ , mv
  fr-up {E = E} {p = p} (f-take fr nf m sd) _ rp nr nh =
    let (Cr′ , fr′ , mv) = fr-up fr tt rp (nr-≈ m (take-nr nr nf)) nh
    in Cr′ , f-take fr′ (λ y nk → Past.in-off p (nr-off {E = E} nr) y _ (nf y nk)) m sd , mv
  fr-up {p = p} (f-outer {op = op} {f = f} {c = c} {Rg = Rg₀} {E = E} fr ji jn m so bh) _ rp nr nh =
    let (Cr′ , fr′ , mv) = fr-up fr tt (proj₁ rp)
                             (nr-≈ (proj₂ m) (nr-tr (join-nr op (λ a → ⟦ f a ⟧ (full (scopeOf c))) (joined-li jn) (λ y → nr y _) (λ _ _ _ → nl)))) nh
    in Cr′ , f-outer fr′ ji (Past.joined-up p (nr-off nr) nl nh jn) m so (Past.behind-up p bh) , mv
    where
      nl : ∀ {q} → ¬ JRl (scopeOf c) Rg₀ op f E q p
      nl r = proj₂ rp (proj₂ r)
  fr-up {p = p} (f-lanes {op = op} {f = f} {c = c} {Rg = Rg₀} {O = O} {vs₁ = vs₁} {vs₂ = vs₂} {q = q₀} {a = a₀}
                   fr ji sy lf y₀ nq ru (h-live st ns le) rt cnt wt wh od ah ao en li m so sd bh) _ rp nr nh =
    let (Cr′ , fr′ , mv) = fr-up fr tt (proj₁ rp)
                             (nr-≈ (proj₂ m) (nr-tr (join-nr op (λ a → ⟦ f a ⟧ (full (scopeOf c))) li (λ y → no (Sound.rg so y _)) (λ y ln v _ → hole y ln v)))) nh
    in Cr′ , f-lanes fr′ ji (up sy so no nh) (begun-up nb₁ nh lf) y₀ (nm nq) ru (h-live st (nm ns) le) (begun-up nb₂ nh rt) cnt
                     (wait-up ah′ wt) (whole-up wh) (od-up od) ah′ ao en li m so sd (behind-up bh) , mv
    where
      open Past p using (up; begun-up; nm; off-rg; behind-up; module Book)
      no : ¬ JRo (scopeOf c) Rg₀ op f O p
      no r = proj₂ r (proj₂ rp)
      open Book {P = polF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) O} (off-rg so no)
      sole : ∀ {q q′} → JRl (scopeOf c) Rg₀ op f O q p → JRl (scopeOf c) Rg₀ op f O q′ p → q ≡ q′
      sole r r′ = lane-sole (JInv.ok ji) (λ a → ⟦ f a ⟧ (full (scopeOf c))) (JInv.fi ji) (JInv.io ji) op (proj₂ r) (proj₂ r′)
      -- a lane's row at `p` is the hole's
      hole : ∀ {q a e} → O q (out a) → Lane (polF op (λ a → ⟦ f a ⟧ (full (scopeOf c))) O) q a p e → Visible e → ⊥
      hole y ln v with sole (li y ln v) rp
      ... | refl with Sound.fn so y y₀ _ _
      ...   | refl = nr (proj₁ (to (alike le) (ln , v))) v
      nb₁ : ∀ {q a} → (q , a) ∈ vs₁ → ¬ JRl (scopeOf c) Rg₀ op f O q p
      nb₁ i r = ≺-irrefl {q₀} (subst (λ x → x ≺ q₀) (sole r rp) (asc-pre vs₁ ao i))
      nb₂ : ∀ {q a} → (q , a) ∈ vs₂ → ¬ JRl (scopeOf c) Rg₀ op f O q p
      nb₂ i r = ≺-irrefl {q₀} (subst (λ x → q₀ ≺ x) (sole r rp) (asc-post vs₁ ao i))
      val : ∀ {q a} → (q , a) ∈ vs₁ ++ (q₀ , a₀) ∷ vs₂ → O q (out a)
      val i with ∈-++⁻ vs₁ i
      ... | inj₁ i′          = begun-out lf i′
      ... | inj₂ (here refl) = y₀
      ... | inj₂ (there i′)  = begun-out rt i′
      ah′ = ahead-up (λ i lc → λ { refl → hole (val i) lc _ }) ah
  fr-up (f-lanes _ _ _ _ _ _ _ (h-end _ _ _) _ _ _ _ _ _ _ _ _ _ _ _ _) ()
  fr-up (f-lanes _ _ _ _ _ _ _ (h-kill _ _ _) _ _ _ _ _ _ _ _ _ _ _ _ _) ()
  fr-up (f-lane fr) lv rp nr nh = let (Cr′ , fr′ , mv) = fr-up fr lv rp nr nh in Cr′ , f-lane fr′ , mv
  fr-up (f-lnct {b = true} fr) _ rp nr nh = let (Cr′ , fr′ , mv) = fr-up fr tt rp nr nh in Cr′ , f-lnct fr′ , mv
  fr-up (f-lnct {b = false} _) ()
  fr-up {p = p} (f-src {k = k} {c = c} {E′ = E′} fr sc pt lv nc sb fl fz eq bh sd af ao ni) _ rp nr nh =
    let (Cr′ , fr′ , mv) = fr-up fr tt (Parts.s⊆ pt rp) nr′ nh
    in Cr′ , f-src fr′ sc pt lv nc (Past.up p sb (Parts.sb pt) nb nhb) (Past.flags-up p {k = k} of fl) fz eq (Past.behind-up p bh) (Past.subd-up p sd) af ao ni , mv
    where
      nb : ¬ Parts.Rb pt p
      nb r = Parts.apart pt r rp
      of : Past.Off p (Frozen k)
      of y v refl = nr (proj₁ (to (alike fz) (y , v))) v
      nhb : ¬ VHot (full (binds (CS.src k) (CS.connAt k) (scopeOf c))) p
      nhb (inj₁ (_ , (y , _) , v)) = of (subst (λ x → pendRows (full x) (CS.src k) (CS.connAt k ++ [ ix 1 ]) p _) (sym sc) y) v refl
      nhb (inj₂ h)                 = nh h
      nr′ : NoRow E′ p
      nr′ y v = let (cy , v′) = from (alike (proj₁ eq)) (y , v) in nb (Sound.rg (Parts.sb pt) (conn-vis cy v′) v′)
  fr-up {p = p} (f-body {k = k} {c = c} {E′ = E′} fr sc pt lv os fl eq) _ rp nr nh =
    let (Cr′ , fr′ , mv) = fr-up fr tt (Parts.b⊆ pt rp) nr′ nhc
    in Cr′ , f-body fr′ sc pt lv (Past.src-up p os (Parts.ss pt) ns nhc) (Past.flags-up p {k = k} (Past.off-rg p (Parts.ss pt) ns) fl) eq , mv
    where
      ns : ¬ Parts.Rs pt p
      ns r = Parts.apart pt rp r
      nhc : ¬ VHot (full (scopeOf c)) p
      nhc = subst (λ x → ¬ VHot (full x) p) sc (λ h → nh (inj₂ h))
      nr′ : NoRow E′ p
      nr′ y v = let (cy , v′) = from (alike (proj₁ eq)) (y , v) in nr (conn-vis cy v′) v′
  fr-up {Cr = Cr} {p = p} (f-isle u hb le na nc bh sd ss ao ni) _ _ _ _ =
    Cr , f-isle u hb le na nc (Past.behind-up p bh) (Past.subd-up p sd) ss ao ni , silent ≃-refl
  fr-up (f-took _ _ _ _ _ _ _ _) ()
  fr-up (f-srcc _ _ _ _ _ _ _ _ _ _ _ _) ()
  fr-up (f-srcp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ()
  fr-up (f-islec _ _ _ _ _ _ _ _ _) ()
  fr-up (f-islep _ _ _ _ _ _ _ _ _ _) ()
  fr-up (d-map _) ()
  fr-up (d-scan _) ()
  fr-up (d-cut _) ()
  fr-up (d-ln _) ()
  fr-up (d-take _) ()
  fr-up (d-outer _ _ _) ()
  fr-up (d-lanes _ _ _ _ _) ()
  fr-up (d-src _ _ _ _) ()
  fr-up (d-body _ _ _) ()

  postulate
    -- A BINDER'S ROW FED: the joiners of the innermost binder take its
    -- row at `p` into their inboxes; the body, apart from `p`, owes the
    -- same past it.
    -- A feed appends at `p ⊕ [ sub j ]` and the inbox stays ascending:
    -- the source's row is a lawful hot, none below another.
    -- RECOVERY: git show 1745f869 restores rejoin-mono, good-full and lawful-at.
    feed-up : ∀ {Γ X B} {sc : Scope Γ} {o : Obs Timeline Γ X} {q Rb} {b : St (X ∷ Γ) B} {β e p}
            → Sync (binds o q sc) Rb (bef p) b β → Sound Rb β → ¬ Rb p
            → Proper (pendRows (full sc) o (q ++ [ ix 1 ])) p (toEv e) → ¬ VHot (full sc) p
            → Sync (binds o q sc) Rb (aft p) (feed (here refl) p e b) β

  -- What a running source's row at `p` leaves of its connect.
  module Fed {Cr Γ X B} {k : CS Γ X} {c : Ctx R Γ B} {Rg E E′ β} {e : Evᴹ X} {p}
             (fr : Fr Rt Cr (bef p) Rg c owes E′) (sc : CS.scope k ≡ scopeOf c) (pt : Parts (scopeOf c) Rg k β)
             (lv : T (CS.srcLive k)) (fz : Frozen k ≈ E) (eq : ConnE (CS.connAt k) (Frozen k) β E′)
             (row : E p (toEv e)) where

    fk : Frozen k p (toEv e)
    fk = proj₁ (from (alike fz) (row , vis e))

    rs : Parts.Rs pt p
    rs = Sound.rg (Parts.ss pt) fk (vis e)

    nr : NoRow E′ p
    nr y v = let (cy , v′) = from (alike (proj₁ eq)) (y , v) in Parts.apart pt (Sound.rg (Parts.sb pt) (conn-vis cy v′) v′) rs

    nh : ¬ VHot (full (scopeOf c)) p
    nh hv = Parts.clear pt (vhot-hots (full (scopeOf c)) hv) (Parts.s⊆ pt rs)

    -- the frames above, past `p`
    lifted : Σ Cur λ Cr′ → Fr Rt Cr′ (aft p) Rg c owes E′ × Moves (RT Rt Cr) [] (RT Rt Cr′)
    lifted = fr-up fr tt (Parts.s⊆ pt rs) nr nh

    Cr↑ : Cur
    Cr↑ = proj₁ lifted

    fr↑ : Fr Rt Cr↑ (aft p) Rg c owes E′
    fr↑ = proj₁ (proj₂ lifted)

    moves : Moves (RT Rt Cr) [] (RT Rt Cr↑)
    moves = proj₂ (proj₂ lifted)

    -- the body, fed
    body : ∀ {b} → Sync (binds (CS.src k) (CS.connAt k) (scopeOf c)) (Parts.Rb pt) (bef p) b β
         → Sync (binds (CS.src k) (CS.connAt k) (scopeOf c)) (Parts.Rb pt) (aft p) (feed (here refl) p e b) β
    body sy = feed-up sy (Parts.sb pt) (λ r → Parts.apart pt r rs)
                (subst (λ x → pendRows (full x) (CS.src k) (CS.connAt k ++ [ ix 1 ]) p (toEv e)) sc fk
                , λ ce → Sound.ends (Parts.ss pt) (subst (λ x → pendRows (full x) (CS.src k) (CS.connAt k ++ [ ix 1 ]) _ end) (sym sc) ce) fk (vis e))
                nh

    -- a value: the source runs on, unclosed
    flags-on : T (not (CS.closed k)) → (toEv e ≡ end → ⊥) → Flags (bef p) k β → Flags (aft p) k β
    flags-on nc ne fl = record
      { shut   = λ t → torn nc t
      ; unshut = λ t {c} y n → Flags.unshut fl t y λ pc → n (≼-≢ {p} {c} pc λ { refl → ne (Sound.fn (Parts.ss pt) fk y (vis e) _) })
      ; torn   = λ nt → torn nt lv }

    -- its end: closed where it fell, owing nothing past it
    flags-shut : toEv e ≡ end → Flags (aft p) (record k { closed = true ; endAt = p }) β
    flags-shut ee = record { shut = λ _ → subst (Frozen k p) ee fk , ≺-irrefl {p} ; unshut = λ _ _ _ → _ ; torn = λ nt → torn nt lv }

    src-done : ∀ {s P} → toEv e ≡ end → TailP (aft p) (Frozen k) P → Husk (scopeOf c) s P → Behind (bef p) (Frozen k)
             → Subd (scopeOf c) (bef p) k → Src (scopeOf c) (Parts.Rs pt) (aft p) (record k { closed = true ; endAt = p }) s
    src-done ee tp hk bh sd =
      src-shut _ (λ (y , v , py) → Sound.ends (Parts.ss pt) (subst (Frozen k p) ee fk) y v py) tp hk (Past.behind-up p bh) (Past.subd-up p sd)

  -- What a step leaves, at the root's cursor `Cr` before it.
  After : Cur → Conf R → Set₁
  After Cr k = Σ Cur λ Cr′ → Σ Cur λ C′ → Inv Rt Cr′ C′ k × Moves (RT Rt Cr) [] (RT Rt Cr′)

  rise-src-nx : ∀ {Γ X B} {k : CS Γ X} {b} {c : Ctx R Γ B} {s a p k′ sh t}
              → rise (inSrc k b c) s (nx a) p ≡ moved k′ sh t → SimC Rt ⟨ inSrc k b c , s , rising (nx a) , p ⟩ sh k′
  rise-src-nx {a = a} {p = p} refl (flying (f-src fr sc pt lv nc bs fl fz eq bh sd af ao _) cl (sy , row)) =
    let open Fed {e = nx a} fr sc pt lv fz eq row
    in Cr↑ , aft p , settled c-abs fr↑ (s-conn sc pt (λ _ → body bs)
                                              (λ _ → src-on nc (sync-≈ sy (≈-sym fz)) (Past.behind-up p bh) (Past.subd-up p sd) af ao)
                                              (λ nl → ⊥-elim (notT _ nl lv)) (flags-on nc (λ ()) fl) eq)
     , moves
  -- an isle's source runs on, its body read by none
  rise-src-nx {a = a} {p = p} refl (flying (f-isle u hb le na nc bh sd ss ao ni) _ (sy , _)) =
    _ , _ , unread-at Rt u (sh-isle na nc sy (Past.behind-up p bh) (Past.subd-up p sd) ss ao) (feed-husk {i = here refl} {p = p} {e = nx a} hb ni) le
    , silent ≃-refl
  rise-src-nx refl (flying (f-srcc _ _ _ _ _ _ _ _ _ _ _ _) _ ())
  rise-src-nx refl (flying (f-srcp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ ())
  rise-src-nx refl (flying (d-src _ _ _ _) _ ())
  rise-src-nx refl (flying (f-islec _ _ _ _ _ _ _ _ _) _ ())
  rise-src-nx refl (flying (f-islep _ _ _ _ _ _ _ _ _ _) _ ())
  rise-src-nx refl (adrift (f-srcc _ _ _ _ cl _ _ _ _ _ _ _) cl′ _)  = ⊥-elim (or-shut cl cl′)
  rise-src-nx refl (adrift (f-islec _ _ _ _ cl _ _ _ _) cl′ _)       = ⊥-elim (or-shut cl cl′)
  rise-src-nx {a = a} {p = p} refl (adrift (d-src u hb le ni) _ (Q , hk , le′)) =
    _ , _ , unread-at Rt u (sh-dead hk) (feed-husk {i = here refl} {p = p} {e = nx a} hb ni) (⊑-trans le (∪-⊑ (under-⊑ le′) ⊑-refl))
    , silent ≃-refl
  rise-src-nx refl (settled () _ _)

  -- Its end: the connect closed where it fell, while it runs.
  rise-src-cp : ∀ {Γ X B} {k : CS Γ X} {b} {c : Ctx R Γ B} {s p k′ sh t}
              → rise (inSrc k b c) s cp p ≡ moved k′ sh t → SimC Rt ⟨ inSrc k b c , s , rising cp , p ⟩ sh k′
  rise-src-cp {k = k} {b} {c} {s} {p} refl (flying (f-src fr sc pt lv nc bs fl fz eq bh sd _ _ _) cl (sy , row)) =
    let open Fed {e = cp} fr sc pt lv fz eq row
        sy′ = sync-≈ sy (≈-sym fz)
    in Cr↑ , aft p
     , subst (λ k″ → Inv Rt Cr↑ (aft p) ⟨ c , connS k″ s (feed (here refl) p cp b) , absorbed , p ⟩) (sym (shut-live {k = k} {p} lv))
             (settled c-abs fr↑ (s-conn sc (re-parts pt) (λ _ → body bs)
                                        (λ _ → src-done refl (shut-tail {k = k} sy′ (Parts.ss pt) fk) (proj₂ (husk-of sy′)) bh sd)
                                        (λ nl → ⊥-elim (notT _ nl lv)) (flags-shut refl) eq))
     , moves
  -- an isle's source ends inside its subscribe call: still an isle
  rise-src-cp {k = k} {b} {c} {s} {p} refl {Cr = Cr} (flying (f-isle u hb le na nc bh sd ss ao ni) _ (sy , row)) =
    shut-by {k = k} {p} (λ k″ → After Cr ⟨ c , connS k″ s (feed (here refl) p cp b) , absorbed , p ⟩)
      (λ lt → _ , _ , unread-at Rt (unread-live Rt lt u)
                        (sh-islec na tt (λ (y , v , py) → Sound.ends ss row y v py) (shut-tail {k = k} sy ss row) (proj₂ (husk-of sy))
                                  (Past.behind-up p bh) (Past.subd-up p sd))
                        fed le , silent ≃-refl)
      (λ _ → _ , _ , unread-at Rt u (sh-isle na nc sy (Past.behind-up p bh) (Past.subd-up p sd) ss ao) fed le , silent ≃-refl)
    where fed = feed-husk {i = here refl} {p = p} {e = cp} hb ni
  rise-src-cp refl (flying (f-srcc _ _ _ _ _ _ _ _ _ _ _ _) _ ())
  rise-src-cp refl (flying (f-srcp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ ())
  rise-src-cp refl (flying (d-src _ _ _ _) _ ())
  rise-src-cp refl (flying (f-islec _ _ _ _ _ _ _ _ _) _ ())
  rise-src-cp refl (flying (f-islep _ _ _ _ _ _ _ _ _ _) _ ())
  rise-src-cp refl (adrift (f-srcc _ _ _ _ cl _ _ _ _ _ _ _) cl′ _)  = ⊥-elim (or-shut cl cl′)
  rise-src-cp refl (adrift (f-islec _ _ _ _ cl _ _ _ _) cl′ _)       = ⊥-elim (or-shut cl cl′)
  rise-src-cp {k = k} {b} {c} {s} {p} refl {Cr = Cr} (adrift (d-src u hb le ni) _ (Q , hk , le′)) =
    shut-by {k = k} {p} (λ k″ → After Cr ⟨ c , connS k″ s (feed (here refl) p cp b) , absorbed , p ⟩)
      (λ lt → _ , _ , unread-at Rt (unread-live Rt lt u) (sh-dead hk) fed le″ , silent ≃-refl)
      (λ _ → _ , _ , unread-at Rt u (sh-dead hk) fed le″ , silent ≃-refl)
    where
      fed = feed-husk {i = here refl} {p = p} {e = cp} hb ni
      le″ = ⊑-trans le (∪-⊑ (under-⊑ le′) ⊑-refl)
  rise-src-cp refl (settled () _ _)
