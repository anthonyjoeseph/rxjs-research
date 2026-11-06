{-# OPTIONS --guardedness #-}

-- A BINDER'S ROW FED.  A connect's source rises at `p` while its body
-- runs: every joiner of that binder takes the row into its inbox, keyed
-- where the joiner's entry rejoins it; the body, apart from `p`, owes the
-- same past it.  The key leads nothing still unfed: the binder is a
-- lawful hot, so no row of it lies below its row at `p`, and an end has
-- none after it.
module adequacy.FeedUp where

open import Data.Bool using (T; true; false; not)
open import Data.Bool.Properties using (T-≡)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; []; _∷_; [_]; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; lookup) renaming (_∷_ to _∷ᴬ_; [] to []ᴬ)
open import Data.List.Relation.Unary.AllPairs using (AllPairs) renaming (_∷_ to _∷ᴾ_; [] to []ᴾ)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function using (Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; subst₂; sym; cong)
open import Relation.Nullary using (¬_)

open import denotation.Events using (Pos; ix; sub; last; Timeline; _<ᵖ_; <ᵖ-down)
open import Tree using (Obs)
open import denotation.Read using (Visible)
open import denotation.EmissionSet using (EmissionSet; Ev; out; end; pin; skip; Bare; Proper; ⟦_⟧; _≺_; _≼_; Den; hot; coldAt; DenEnv; enter; module TakeWhile;
  Rejoin; shown; heard; ended; late)
open import denotation.Laws.Modulus using (≺→≼; ≺-trans; ≺-irrefl; ≺-ext; ≼-antisym; ≼-≺-≺; ≼-or-≻)
open import denotation.Laws.Worlds using (Lawful)
open import denotation.Laws using (inv-⟦⟧)
open import denotation.Laws.HotInv using (lawful-hot)
open import denotation.Laws.JoinInv using (end≢out)
import denotation.Laws.Connect as LC
open import operation.PureObservable using (module Machine)
open Machine using (St; Ctx; ⟨_,_,_,_⟩; Scope; unbound; binds; CS; scopeOf; connS; rising; nx; cp; inSrc; feed; rise; moved; shutAt; absorbed; same?; joinS; feedL;
  inbox; queued) renaming (Ev to Evᴹ)
open import adequacy.Rows using (_≃_; _⇄_; ≼-≢; full; Frozen; pendRows; Inbox; this; that; Moves; silent; toEv; ≃-refl; ≃-trans; ≃-sym)
open _≃_
open import adequacy.Walk using (sync-≈)
open import adequacy.Enter using (module Lanes)
open import adequacy.Cursor using (Cur; Dom; bef; aft; Behind; ConnE; _≈_; Kill; Owes; Due; Unfed; Rgn; Sound; vis; LaneSt;
  l-live; l-dead; h-live; h-end; h-kill; Begun; none; more; Lane; Joined; joined; Flags; Src;
  src-pend; src-on; src-shut; Parts; re-parts; Sync; s-cold; s-of; s-done; s-map; s-scan;
  s-cut; s-take; s-took; s-flat; s-conn; s-join; s-joinx; Pol; SlotsMv; slots-mv; Subd; Torn;
  notT; Husk; sh-dead; sh-isle; sh-islec; o-cp; o-cut; o-over; OweAt; Adm; TailP; AttOwed;
  InCall; AttFin; alike; voc; ⊑-trans; ∪-⊑; ⊑-refl; under-⊑; burst-dn)
open import adequacy.Cursor.Tear using (c-abs; husk-of; NoIsle; NoIsleL; Settles)
open import adequacy.Cursor.Frame using (Fr; owes; f-src; f-srcc; f-srcp; d-src; f-isle; f-islec; f-islep)
open import adequacy.Cursor.Rise using (Inv; RT; settled; flying; adrift; SimC; unread-at)
open import adequacy.Bound using (good-full)
open import adequacy.PinTail using (end-tail)
open import adequacy.Up using (module Past; VHot; vhot-hots; joined-li; begun-out; NoRow; conn-vis; or-shut; torn; feed-husk; srch-feed; shut-live; shut-by;
  unread-live; fr-up; After)

------------------------------------------------------------------------
-- The binder fed, and the rest in scope.

-- No visible row at `p`.
NoVis : ∀ {A} → Den A → Pos → Set
NoVis (hot t)    p = ∀ {e} → t p e → Visible e → ⊥
NoVis (coldAt _) p = ⊤

-- Binder `i` has a row at `p`; no other binder in scope has a visible
-- one there.
record FedAt {Γ X} (sc : Scope Γ) (i : X ∈ Γ) (p : Pos) (e : Evᴹ X) : Set₁ where
  field
    t    : EmissionSet X
    at   : lookup (full sc) i ≡ hot t
    row  : t p (toEv e)
    only : ∀ {A} (x : A ∈ Γ) → same? i x ≡ nothing → NoVis (lookup (full sc) x) p

vhot-at : ∀ {Γ A} (ρ : DenEnv Γ) (x : A ∈ Γ) {p} → ¬ VHot ρ p → NoVis (lookup ρ x) p
vhot-at (hot t ∷ᴬ ρ)    (here refl) nh = λ y v → nh (inj₁ (_ , y , v))
vhot-at (coldAt _ ∷ᴬ ρ) (here refl) nh = tt
vhot-at (hot t ∷ᴬ ρ)    (there x)   nh = vhot-at ρ x (λ h → nh (inj₂ h))
vhot-at (coldAt _ ∷ᴬ ρ) (there x)   nh = vhot-at ρ x nh

same-eq : ∀ {Γ X} (i x : X ∈ Γ) → same? i x ≡ just refl → i ≡ x
same-eq (here refl) (here refl) _  = refl
same-eq (here refl) (there x)   ()
same-eq (there i)   (here refl) ()
same-eq (there i)   (there x)   eq = cong there (same-eq i x eq)

-- An admissible scope's binders are lawful hots.
adm-lawful : ∀ {Γ X} (sc : Scope Γ) → Adm sc → (i : X ∈ Γ) → ∀ {t} → lookup (full sc) i ≡ hot t → Lawful t
adm-lawful unbound        _        ()
adm-lawful (binds o q sc) (ok , a) (here refl) refl = LC.lawful {s = ⟦ o ⟧ (full sc)} {F = λ h → h} (inv-⟦⟧ o (full sc) (good-full sc a)) (λ L → lawful-hot L) q ok
adm-lawful (binds o q sc) (_ , a)  (there i)   eq   = adm-lawful sc a i eq

-- Into a connect's body: its own binder has no row at `p`.
fed-bind : ∀ {Γ X Y} {i : X ∈ Γ} {p e} {k : CS Γ Y} → NoRow (Frozen k) p → FedAt (CS.scope k) i p e
         → FedAt (binds (CS.src k) (CS.connAt k) (CS.scope k)) (there i) p e
fed-bind {i = i} {p} {k = k} nr fa = record { t = FedAt.t fa ; at = FedAt.at fa ; row = FedAt.row fa ; only = only }
  where
    only : ∀ {A} (x : A ∈ _) → same? (there i) x ≡ nothing → NoVis (lookup (full (binds (CS.src k) (CS.connAt k) (CS.scope k))) x) p
    only (here refl) _  = λ y v → nr (proj₁ y) v
    only (there x)   eq = FedAt.only fa x eq

------------------------------------------------------------------------
-- An inbox every entry of which lies before the new one: appended.

inbox-snoc : ∀ {A} (ib : List (Pos × Evᴹ A)) {r v} → (∀ {u} → u ∈ ib → proj₁ u ≺ r) → inbox (r , v) ib ≡ ib ++ [ (r , v) ]
inbox-snoc []               _  = refl
inbox-snoc ((r′ , e′) ∷ ib) {r} lt with r′ <ᵖ r in h
... | true  = cong ((r′ , e′) ∷_) (inbox-snoc ib (λ m → lt (there m)))
... | false = ⊥-elim (subst T h (lt (here refl)))

all-snoc : ∀ {A : Set} {P : A → Set} {xs x} → All P xs → P x → All P (xs ++ [ x ])
all-snoc []ᴬ        px = px ∷ᴬ []ᴬ
all-snoc (py ∷ᴬ ps) px = py ∷ᴬ all-snoc ps px

asc-snoc : ∀ {A} (ib : List (Pos × Evᴹ A)) {x} → (∀ {u} → u ∈ ib → proj₁ u ≺ proj₁ x)
         → AllPairs (λ u v → proj₁ u ≺ proj₁ v) ib → AllPairs (λ u v → proj₁ u ≺ proj₁ v) (ib ++ [ x ])
asc-snoc []       _  []ᴾ      = []ᴬ ∷ᴾ []ᴾ
asc-snoc (_ ∷ ib) lt (h ∷ᴾ t) = all-snoc h (lt (here refl)) ∷ᴾ asc-snoc ib (λ m → lt (there m)) t

snoc-l : ∀ {A} {ib : List (Pos × Evᴹ A)} {x q e} → Inbox ib q e → Inbox (ib ++ [ x ]) q e
snoc-l this     = this
snoc-l (that i) = that (snoc-l i)

snoc-r : ∀ {A} (ib : List (Pos × Evᴹ A)) {r v} → Inbox (ib ++ [ (r , v) ]) r (toEv v)
snoc-r []       = this
snoc-r (_ ∷ ib) = that (snoc-r ib)

snoc-⁻ : ∀ {A} (ib : List (Pos × Evᴹ A)) {r v q e} → Inbox (ib ++ [ (r , v) ]) q e → Inbox ib q e ⊎ (q ≡ r × e ≡ toEv v)
snoc-⁻ []       this     = inj₂ (refl , refl)
snoc-⁻ []       (that ())
snoc-⁻ (_ ∷ ib) this     = inj₁ this
snoc-⁻ (_ ∷ ib) (that i) = [ (λ i′ → inj₁ (that i′)) , inj₂ ]′ (snoc-⁻ ib i)

pin-out : ∀ {A} {r} {a : A} → pin r ≡ out a → ⊥
pin-out ()

pin-end : ∀ {A} {r} → pin {A} r ≡ end → ⊥
pin-end ()

bare-end : ∀ {A} {e : Ev A} → Bare e → e ≡ end → ⊥
bare-end {e = out _} _ ()
bare-end {e = skip}  _ ()

-- A Torn connect fed: what nothing reads takes it as it runs.
torn-feed : ∀ {Γ X Y B} {sc : Scope Γ} {C} {i : X ∈ Γ} {p e} {k : CS Γ Y} {o} {b : St (Y ∷ Γ) B} {β E}
          → Torn sc C k o b β E → Settles k o → NoIsle o → NoIsle b → Torn sc C k (feed i p e o) (feed (there i) p e b) β E
torn-feed tn st no nb = record { D = Torn.D tn ; Db = Torn.Db tn ; dom = Torn.dom tn ; Ps = Torn.Ps tn ; Pb = Torn.Pb tn
                               ; sh = srch-feed (Torn.sh tn) st no ; bh = feed-husk (Torn.bh tn) nb ; bu = Torn.bu tn ; tl = Torn.tl tn ; opn = Torn.opn tn }

------------------------------------------------------------------------
-- THE WALK: every node past `p`, its joiners of the fed binder taking
-- the row.

module Walk (p : Pos) where
  open Past p

  -- A rejoined row whose source row is at `p`.
  AtP : ∀ {A} → EmissionSet A → Pos → EmissionSet A
  AtP t j = Rejoin j (λ k e → t k e × p ≡ k)

  -- An unfed row still owed past `p`: its source row past `p`, or at it.
  split : ∀ {A} {d : Den A} {t j q e′} → d ≡ hot t → Owes (aft p) q → Due (bef p) (Unfed (bef p) d j) q e′
        → Due (aft p) (Unfed (aft p) d j) q e′ ⊎ (AtP t j q e′ × Visible e′)
  split refl o (shown {k} (y , ok) b jk , v , _) =
    [ (λ kp → inj₂ (shown (y , ≼-antisym {p} {k} ok kp) b jk , v)) , (λ pk → inj₁ (shown (y , pk) b jk , v , o)) ]′ (≼-or-≻ k p)
  split refl o (heard _ _ , () , _)
  split refl o (ended {c} (y , ok) jc , v , _) =
    [ (λ cp′ → inj₂ (ended (y , ≼-antisym {p} {c} ok cp′) jc , v)) , (λ pc → inj₁ (ended (y , pc) jc , v , o)) ]′ (≼-or-≻ c p)
  split refl o (late {c} (y , ok) cj , v , _) =
    [ (λ cp′ → inj₂ (late (y , ≼-antisym {p} {c} ok cp′) cj , v)) , (λ pc → inj₁ (late (y , pc) cj , v , o)) ]′ (≼-or-≻ c p)

  at-vis : ∀ {A} {t : EmissionSet A} {j q e′} → (∀ {e} → t p e → Visible e → ⊥) → AtP t j q e′ → Visible e′ → ⊥
  at-vis nv (shown (y , refl) _ _) v = nv y v
  at-vis nv (heard _ _)            ()
  at-vis nv (ended (y , refl) _)   v = nv y v
  at-vis nv (late (y , refl) _)    v = nv y v

  -- A binder with no visible row at `p`: its unfed rows all past it.
  keep-cls : ∀ {A} {d : Den A} {j q e′} → NoVis d p → Owes (aft p) q → Due (bef p) (Unfed (bef p) d j) q e′ → Due (aft p) (Unfed (aft p) d j) q e′
  keep-cls {d = hot t}    nv o u = [ (λ u′ → u′) , (λ (a , v) → ⊥-elim (at-vis nv a v)) ]′ (split refl o u)
  keep-cls {d = coldAt _} _  _ (() , _ , _)

  -- The fed row's rejoined place: a value under `p` where the joiner
  -- joined before; an end there too, or else at once.
  at-nx : ∀ {A} {t : EmissionSet A} {j q e′ a} → Lawful t → t p (out a) → AtP t j q e′ → j ≺ p × q ≡ p ++ [ sub j ] × e′ ≡ out a
  at-nx L row (shown (y , refl) _ jk) = jk , refl , Lawful.func L y row
  at-nx L row (heard (y , refl) _)    = ⊥-elim (pin-out (Lawful.func L y row))
  at-nx L row (ended (y , refl) _)    = ⊥-elim (end≢out (Lawful.func L y row))
  at-nx L row (late (y , refl) _)     = ⊥-elim (end≢out (Lawful.func L y row))

  at-cp : ∀ {A} {t : EmissionSet A} {j q e′} → Lawful t → t p end → AtP t j q e′
        → (j ≺ p × q ≡ p ++ [ sub j ] × e′ ≡ end) ⊎ (p ≼ j × q ≡ j ++ [ last ] × e′ ≡ end)
  at-cp L row (shown (y , refl) b _) = ⊥-elim (bare-end b (Lawful.func L y row))
  at-cp L row (heard (y , refl) _)   = ⊥-elim (pin-end (Lawful.func L y row))
  at-cp L row (ended (y , refl) jc)  = inj₁ (jc , refl , refl)
  at-cp L row (late (y , refl) cj)   = inj₂ (cj , refl , refl)

  -- The fed row is one still unfed before `p`.
  new-nx : ∀ {A} {d : Den A} {t j a} → d ≡ hot t → t p (out a) → j ≺ p → Due (bef p) (Unfed (bef p) d j) (p ++ [ sub j ]) (out a)
  new-nx refl row jk = shown (row , ≺-irrefl {p}) tt jk , tt , ≺→≼ {p} (≺-ext p [])

  new-in : ∀ {A} {d : Den A} {t j} → d ≡ hot t → t p end → j ≺ p → Due (bef p) (Unfed (bef p) d j) (p ++ [ sub j ]) end
  new-in refl row jk = ended (row , ≺-irrefl {p}) jk , tt , ≺→≼ {p} (≺-ext p [])

  new-late : ∀ {A} {d : Den A} {t j} → d ≡ hot t → t p end → p ≼ j → Due (bef p) (Unfed (bef p) d j) (j ++ [ last ]) end
  new-late {j = j} refl row pj = late (row , ≺-irrefl {p}) pj , tt , ≺→≼ {p} (≼-≺-≺ {p} {j} pj (≺-ext j []))

  -- Under `p`, before what lies under a later row: none lies below `p`.
  down : ∀ {A} {t : EmissionSet A} {k e₀ e₁ j} → Lawful t → t p e₀ → t k e₁ → p ≺ k → (p ++ [ sub j ]) ≺ (k ++ [ sub j ])
  down {t = t} {k} {e₁ = e₁} {j} L row y pk =
    Equivalence.from T-≡ (<ᵖ-down p k (sub j) (sub j) (Equivalence.to T-≡ pk) (λ l ls eq → Lawful.flat L row (subst (λ z → t z e₁) eq y)))

  -- A value's key leads every row still unfed past `p`.
  lead-nx : ∀ {A} {d : Den A} {t j q e′ a} → d ≡ hot t → Lawful t → t p (out a) → j ≺ p
          → Due (aft p) (Unfed (aft p) d j) q e′ → (p ++ [ sub j ]) ≺ q
  lead-nx refl L row jk (shown (y , pk) _ _ , _)      = down L row y pk
  lead-nx refl L row jk (heard _ _ , () , _)
  lead-nx refl L row jk (ended (y , pc) _ , _)        = down L row y pc
  lead-nx {j = j} refl L row jk (late {c} (y , pc) cj , _) = ⊥-elim (≺-irrefl {p} (≺-trans {p} {c} {p} pc (≼-≺-≺ {c} {j} {p} cj jk)))

  -- An end has no row past it: nothing is still unfed past `p`.
  lead-end : ∀ {A} {d : Den A} {t j q e′} → d ≡ hot t → Lawful t → t p end → Due (aft p) (Unfed (aft p) d j) q e′ → ⊥
  lead-end refl L row (shown (y , pk) _ _ , _) = Lawful.proper L row y pk
  lead-end refl L row (heard (y , pk) _ , _)   = Lawful.proper L row y pk
  lead-end refl L row (ended (y , pk) _ , _)   = Lawful.proper L row y pk
  lead-end refl L row (late (y , pk) _ , _)    = Lawful.proper L row y pk

  -- A joiner's inbox kept: its unfed rows owed past `p` as before it.
  join-keep : ∀ {Γ} {sc : Scope Γ} {Rg} {A} {j} {x : A ∈ Γ} {ib E}
            → Sound Rg E → ¬ Rg p
            → (∀ {q e′} → Owes (aft p) q → Due (bef p) (Unfed (bef p) (lookup (full sc) x) j) q e′ → Due (aft p) (Unfed (aft p) (lookup (full sc) x) j) q e′)
            → enter (lookup (full sc) x) j ≈ E
            → Due (bef p) E ≃ (λ q e → Inbox ib q e ⊎ Due (bef p) (Unfed (bef p) (lookup (full sc) x) j) q e)
            → AllPairs (λ u v → proj₁ u ≺ proj₁ v) ib
            → (∀ {u q e} → u ∈ ib → Due (bef p) (Unfed (bef p) (lookup (full sc) x) j) q e → proj₁ u ≺ q)
            → Adm sc → Sync sc Rg (aft p) (joinS j true x ib) E
  join-keep {sc = sc} {x = x} sd nr cl en d ap hd adm =
    s-join en d′ ap (λ i u → hd i (unfed-bef (lookup (full sc) x) u)) adm
    where
      d′ = (λ (y , v , o) → [ inj₁ , (λ u → inj₂ (cl o u)) ]′ (to d (y , v , dn o)))
         ⇄ λ { (inj₁ i) → let (y , v , o) = from d (inj₁ i) in y , v , in-rg sd nr y v o
             ; (inj₂ u) → let (y , v , _) = from d (inj₂ (unfed-bef (lookup (full sc) x) u)) in y , v , proj₂ (proj₂ u) }

  -- A joiner's inbox fed at `r`: the row moves from its unfed rows to
  -- the inbox's back.
  fed-join : ∀ {Γ} {sc : Scope Γ} {Rg} {A} {j} {x : A ∈ Γ} {ib E} {r} {v : Evᴹ A}
           → Sound Rg E → ¬ Rg p
           → (∀ {q e′} → Owes (aft p) q → Due (bef p) (Unfed (bef p) (lookup (full sc) x) j) q e′
                → Due (aft p) (Unfed (aft p) (lookup (full sc) x) j) q e′ ⊎ (q ≡ r × e′ ≡ toEv v))
           → (∀ {q e′} → Due (aft p) (Unfed (aft p) (lookup (full sc) x) j) q e′ → r ≺ q)
           → Due (bef p) (Unfed (bef p) (lookup (full sc) x) j) r (toEv v) → p ≺ r
           → enter (lookup (full sc) x) j ≈ E
           → Due (bef p) E ≃ (λ q e → Inbox ib q e ⊎ Due (bef p) (Unfed (bef p) (lookup (full sc) x) j) q e)
           → AllPairs (λ u v → proj₁ u ≺ proj₁ v) ib
           → (∀ {u q e} → u ∈ ib → Due (bef p) (Unfed (bef p) (lookup (full sc) x) j) q e → proj₁ u ≺ q)
           → Adm sc → Sync sc Rg (aft p) (joinS j true x (inbox (r , v) ib)) E
  fed-join {sc = sc} {Rg} {j = j} {x = x} {ib} {E} {r} {v} sd nr cl ld nw pr en d ap hd adm =
    subst (λ l → Sync sc Rg (aft p) (joinS j true x l) E) (sym (inbox-snoc ib (λ i → hd i nw)))
      (s-join en d′ (asc-snoc ib (λ i → hd i nw) ap) hd′ adm)
    where
      d′ : Due (aft p) E ≃ (λ q e → Inbox (ib ++ [ (r , v) ]) q e ⊎ Due (aft p) (Unfed (aft p) (lookup (full sc) x) j) q e)
      d′ = (λ (y , w , o) → [ (λ i → inj₁ (snoc-l i))
                            , (λ u → [ inj₂ , (λ (qr , ev) → inj₁ (subst₂ (Inbox (ib ++ [ (r , v) ])) (sym qr) (sym ev) (snoc-r ib))) ]′ (cl o u)) ]′
                            (to d (y , w , dn o)))
         ⇄ λ { (inj₁ i) → [ (λ i₀ → let (y , w , o) = from d (inj₁ i₀) in y , w , in-rg sd nr y w o)
                          , (λ (qr , ev) → let (y , w , _) = from d (inj₂ nw) in subst₂ (Due (aft p) E) (sym qr) (sym ev) (y , w , pr)) ]′ (snoc-⁻ ib i)
             ; (inj₂ u) → let (y , w , _) = from d (inj₂ (unfed-bef (lookup (full sc) x) u)) in y , w , proj₂ (proj₂ u) }
      hd′ : ∀ {u q e} → u ∈ ib ++ [ (r , v) ] → Due (aft p) (Unfed (aft p) (lookup (full sc) x) j) q e → proj₁ u ≺ q
      hd′ m u with ∈-++⁻ ib m
      ... | inj₁ m′          = hd m′ (unfed-bef (lookup (full sc) x) u)
      ... | inj₂ (here refl) = ld u

  -- The fed binder's joiner, by the step and where it joined.
  fed-at : ∀ {Γ} {sc : Scope Γ} {Rg} {A} {j} {x : A ∈ Γ} {ib E} {e : Evᴹ A}
         → Sound Rg E → ¬ Rg p → FedAt sc x p e
         → enter (lookup (full sc) x) j ≈ E
         → Due (bef p) E ≃ (λ q e → Inbox ib q e ⊎ Due (bef p) (Unfed (bef p) (lookup (full sc) x) j) q e)
         → AllPairs (λ u v → proj₁ u ≺ proj₁ v) ib
         → (∀ {u q e} → u ∈ ib → Due (bef p) (Unfed (bef p) (lookup (full sc) x) j) q e → proj₁ u ≺ q)
         → Adm sc → Sync sc Rg (aft p) (joinS j true x (queued j p e ib)) E
  fed-at {sc = sc} {j = j} {x = x} {e = nx a} sd nr fa en d ap hd adm with j <ᵖ p in jp
  ... | true  = fed-join sd nr (λ o u → [ inj₁ , (λ (atp , _) → let (_ , qr , ev) = at-nx L (FedAt.row fa) atp in inj₂ (qr , ev)) ]′ (split (FedAt.at fa) o u) ) (lead-nx (FedAt.at fa) L (FedAt.row fa) jk) (new-nx (FedAt.at fa) (FedAt.row fa) jk) (≺-ext p []) en d ap hd adm
    where
      L  = adm-lawful sc adm x (FedAt.at fa)
      jk : j ≺ p
      jk = subst T (sym jp) tt
  ... | false = join-keep sd nr (λ o u → [ (λ u′ → u′) , (λ (atp , _) → ⊥-elim (subst T jp (proj₁ (at-nx L (FedAt.row fa) atp)))) ]′ (split (FedAt.at fa) o u)) en d ap hd adm
    where
      L  = adm-lawful sc adm x (FedAt.at fa)

  fed-at {sc = sc} {j = j} {x = x} {e = cp} sd nr fa en d ap hd adm with j <ᵖ p in jp
  ... | true  = fed-join sd nr (λ o u → [ inj₁ , (λ (atp , _) → [ (λ (_ , qr , ev) → inj₂ (qr , ev)) , (λ (pj , _) → ⊥-elim (pj jk)) ]′ (at-cp L (FedAt.row fa) atp)) ]′ (split (FedAt.at fa) o u) ) (λ u → ⊥-elim (lead-end (FedAt.at fa) L (FedAt.row fa) u)) (new-in (FedAt.at fa) (FedAt.row fa) jk) (≺-ext p []) en d ap hd adm
    where
      L  = adm-lawful sc adm x (FedAt.at fa)
      jk : j ≺ p
      jk = subst T (sym jp) tt
  ... | false = fed-join sd nr (λ o u → [ inj₁ , (λ (atp , _) → [ (λ (jk , _) → ⊥-elim (subst T jp jk)) , (λ (_ , qr , ev) → inj₂ (qr , ev)) ]′ (at-cp L (FedAt.row fa) atp)) ]′ (split (FedAt.at fa) o u)) (λ u → ⊥-elim (lead-end (FedAt.at fa) L (FedAt.row fa) u)) (new-late (FedAt.at fa) (FedAt.row fa) pj)
                  (≼-≺-≺ {p} {j} pj (≺-ext j [])) en d ap hd adm
    where
      L  = adm-lawful sc adm x (FedAt.at fa)
      pj : p ≼ j
      pj jk = subst T jp jk

  mutual
    fup : ∀ {Γ X} {sc : Scope Γ} {Rg A} {i : X ∈ Γ} {e : Evᴹ X} {s : St Γ A} {E}
        → Sync sc Rg (bef p) s E → Sound Rg E → ¬ Rg p → FedAt sc i p e → NoIsle s
        → Sync sc Rg (aft p) (feed i p e s) E
    fup (s-cold tk d tl tw)     sd nr fa ni = s-cold tk (≃-trans (≃-sym (due-up sd nr)) d) (tail-up tl)
      λ t → let (o , r , g) = tw t in owes-up (λ { refl → nr g }) o , r , g
    fup (s-of d tl)             sd nr fa ni = s-of (≃-trans (≃-sym (due-up sd nr)) d) (tail-up tl)
    fup {E = E} (s-done sp fn)  sd nr fa ni = s-done (spent-up {E = E} sp) (fin-up fn)
    fup (s-map sy m sm)         sd nr fa ni = s-map (fup sy sm nr fa ni) m sm
    fup (s-scan sy fd m sm)     sd nr fa ni = s-scan (fup sy sm nr fa ni) (fold-up (off-rg sm nr) fd) m sm
    fup (s-cut sy)              sd nr fa ni = s-cut (fup sy sd nr fa ni)
    fup (s-take sy nf m sm)     sd nr fa ni = s-take (fup sy sm nr fa ni) (λ y nk → in-rg sm nr y _ (nf y nk)) m sm
    fup {A = A} (s-took {r = r} fl@(a , y , nk , nf) g ni′ oa tp hk dm nf′ m sm) sd nr fa ni =
      s-took fl (λ {q} o → g {q} (dn o)) (λ t → nm (ni′ t)) (owe-up oa) (tailp-up tp) (feed-husk hk ni) dm nf′ m sm
      where
        -- its completion is one of its rows
        owe-up : ∀ {w} → OweAt (bef p) w r → OweAt (aft p) w r
        owe-up (o-cp o)   = o-cp (in-rg sd nr (proj₁ (to (alike m) (TakeWhile.stop y nk nf , vis {A = A} cp))) (vis {A = A} cp) o)
        owe-up (o-cut n)  = o-cut (nm n)
        owe-up (o-over n) = o-over (nm n)
    fup (s-flat {sc = sc} {op = op} {f = f} ji sy jn m so bh) sd nr fa (nio , nil) =
      s-flat ji (fup sy so no fa nio) (fjoined (off-rg so no) (kill-up op (off-rg so no)) (λ r → nr (proj₁ r)) fa (Lanes.lane-rows sc f ji op (joined-li jn)) (slots-mv op) jn nil)
             m so (behind-up bh)
      where no = λ r → nr (proj₁ r)
    fup (s-conn {k = k} refl pt bs bb ss tn fl m) sd nr fa (st , nio , nib) =
      s-conn refl pt (λ t → fup (bs t) (Parts.sb pt) nb (fed-bind {k = k} (λ y v → off-rg (Parts.ss pt) ns y v refl) fa) nib) (λ t → behind-up (bb t))
             (λ t → fsrc (ss t) (Parts.ss pt) ns fa nio) (λ nt → torn-feed (torn-up (tn nt)) st nio nib)
             (flags-up {k = k} (off-rg (Parts.ss pt) ns) (λ y → off-rg (Parts.sb pt) nb y tt) fl) m
      where
        nb = λ r → nr (Parts.b⊆ pt r)
        ns = λ r → nr (Parts.s⊆ pt r)
    fup {sc = sc} {i = i} (s-join {x = x} en d ap hd adm) sd nr fa ni with same? i x in sx
    ... | nothing   = join-keep sd nr (keep-cls (FedAt.only fa x sx)) en d ap hd adm
    ... | just refl = fed-at sd nr (subst (λ y → FedAt sc y p _) (same-eq i x sx) fa) en d ap hd adm
    fup {E = E} (s-joinx sp fn) sd nr fa ni = s-joinx (spent-up {E = E} sp) (fin-up fn)

    fsrc : ∀ {Γ X Y} {sc : Scope Γ} {Rs : Rgn} {i : X ∈ Γ} {e : Evᴹ X} {k : CS Γ Y} {o}
         → Src sc Rs (bef p) k o → Sound Rs (Frozen k) → ¬ Rs p → FedAt sc i p e → NoIsle o → Src sc Rs (aft p) k (feed i p e o)
    fsrc (src-pend na nc be an adm pr wn ow ng) ss nr fa ni = src-pend na nc be an adm pr wn (owes-up (off nr (proj₁ wn)) ow) ng
    fsrc (src-on nc sy bh sd af ao ic lv)       ss nr fa ni = src-on nc (fup sy ss nr fa ni) (behind-up bh) (subd-up sd) af ao ic lv
    fsrc {k = k} (src-shut cl sp tp hk dm bh sd ic af lv) ss nr fa ni =
      src-shut cl (spent-up {E = Frozen k} sp) (tailp-up tp) (feed-husk hk ni) dm (behind-up bh) (subd-up sd) ic af lv

    flane : ∀ {Γ X} {sc : Scope Γ} {Rg : Rgn} {A B} {P : Pol A B} {q a l b} {i : X ∈ Γ} {e : Evᴹ X}
          → (∀ {q′} → Kill P q q′ → Owes (bef p) q′ → Owes (aft p) q′)
          → ¬ Rg p → FedAt sc i p e → LaneSt sc Rg (bef p) P q a l b → NoIsle l → LaneSt sc Rg (aft p) P q a (feed i p e l) b
    flane ku nr fa (l-live (h-live st al uk ue) sy sd) ni =
      l-live (h-live st al (λ k → ku k (uk k)) (λ l nk → in-rg sd nr (proj₁ (from (alike al) (l , tt))) tt (ue l nk))) (fup sy sd nr fa ni) sd
    flane ku nr fa (l-dead {E = E} (h-end {c = c} lc nc tp) hk dm nk) ni =
      l-dead {E = E} (h-end lc (nm {c} nc) (tailp-up tp)) (feed-husk hk ni) dm nk
    flane ku nr fa (l-dead {E = E} (h-kill {q′ = q′} kq nq tp) hk dm nk) ni =
      l-dead {E = E} (h-kill kq (nm {q′} nq) (tailp-up tp)) (feed-husk hk ni) dm nk

    fbegun : ∀ {Γ X} {sc : Scope Γ} {Rl : Pos → Rgn} {A B} {P : Pol A B} {O : EmissionSet A} {vs ls n} {i : X ∈ Γ} {e : Evᴹ X}
           → (∀ {q q′} → Kill P q q′ → Owes (bef p) q′ → Owes (aft p) q′)
           → (∀ {q a} → (q , a) ∈ vs → ¬ Rl q p) → FedAt sc i p e
           → Begun sc Rl (bef p) P O vs ls n → NoIsleL ls → Begun sc Rl (aft p) P O vs (feedL i p e ls) n
    fbegun ku nl fa none                _          = none
    fbegun ku nl fa (more y nq r ln bg) (ni , nis) = more y (nm nq) r (flane ku (nl (here refl)) fa ln ni) (fbegun ku (λ i → nl (there i)) fa bg nis)

    fjoined : ∀ {Γ X} {sc : Scope Γ} {Rl : Pos → Rgn} {A B} {P : Pol A B} {O : EmissionSet A} {d n qu ls} {i : X ∈ Γ} {e : Evᴹ X}
            → Off O → (∀ {q q′} → Kill P q q′ → Owes (bef p) q′ → Owes (aft p) q′) → (∀ {q} → ¬ Rl q p) → FedAt sc i p e
            → (∀ {q a k e} → O q (out a) → Lane P q a k e → Rl q k) → SlotsMv P O
            → Joined sc Rl (bef p) P O d n qu ls → NoIsleL ls → Joined sc Rl (aft p) P O d n qu (feedL i p e ls)
    fjoined {P = P} {O = O} oo ku nl fa rl mv (joined bg wt wh od ah ao en li sl) nis =
      joined (fbegun ku (λ _ → nl) fa bg nis) (wait-up (λ iv lc → λ { refl → nl (rl (begun-out bg iv) lc) }) ah′ wt) (whole-up oo wh) (od-up oo od) ah′ ao en li
             (mv (λ {y} t → ≺→≼ {p} {y} t) (λ x o → in-off oo x tt o) sl)
      where
        open Book {P = P} {O = O}
        ah′ = ahead-up (λ iv lc → λ { refl → nl (rl (begun-out bg iv) lc) }) ah

-- THE BODY FED: the joiners of the innermost binder take its row at `p`;
-- the body, apart from `p`, owes the same past it.
feed-up : ∀ {Γ X B} {sc : Scope Γ} {o : Obs Timeline Γ X} {q Rb} {b : St (X ∷ Γ) B} {β e p}
        → Sync (binds o q sc) Rb (bef p) b β → Sound Rb β → ¬ Rb p
        → Proper (pendRows (full sc) o (q ++ [ ix 1 ])) p (toEv e) → ¬ VHot (full sc) p → NoIsle b
        → Sync (binds o q sc) Rb (aft p) (feed (here refl) p e b) β
feed-up {sc = sc} {o} {q} {e = e} {p} sy sd nr row nh ni = Walk.fup p sy sd nr fa ni
  where
    only : ∀ {A} (x : A ∈ _) → same? (here refl) x ≡ nothing → NoVis (lookup (full (binds o q sc)) x) p
    only (here refl) ()
    only (there x)   _ = vhot-at (full sc) x nh
    fa : FedAt (binds o q sc) (here refl) p e
    fa = record { t = Proper (pendRows (full sc) o (q ++ [ ix 1 ])) ; at = refl ; row = row ; only = only }

module _ {R : Set} (Rt : EmissionSet R) where

  -- What a running source's row at `p` leaves of its connect.
  module Fed {Cr Γ X B} {k : CS Γ X} {c : Ctx R Γ B} {Rg E E′ β} {e : Evᴹ X} {p}
             (fr : Fr Rt Cr (bef p) Rg c owes E′) (sc : CS.scope k ≡ scopeOf c) (pt : Parts (scopeOf c) Rg k β)
             (lv : T (CS.srcLive k)) (fz : E ≈ Frozen k) (eq : ConnE (CS.connAt k) (Frozen k) β E′)
             (row : E p (toEv e)) where

    fk : Frozen k p (toEv e)
    fk = voc fz row

    rs : Parts.Rs pt p
    rs = Sound.rg (Parts.ss pt) fk (vis e)

    nr : NoRow E′ p
    nr y v = let (cy , v′) = from (alike (proj₁ eq)) (y , v) in Parts.apart pt (Sound.rg (Parts.sb pt) (conn-vis cy v′) v′) rs

    nh : ¬ VHot (full (scopeOf c)) p
    nh hv = Parts.clear-s pt (vhot-hots (full (scopeOf c)) hv) rs

    -- the frames above, past `p`
    lifted : Σ Cur λ Cr′ → Fr Rt Cr′ (aft p) Rg c owes E′ × Moves (RT Rt Cr) [] (RT Rt Cr′)
    lifted = fr-up Rt fr tt (Parts.s⊆ pt rs) nr nh

    Cr↑ : Cur
    Cr↑ = proj₁ lifted

    fr↑ : Fr Rt Cr↑ (aft p) Rg c owes E′
    fr↑ = proj₁ (proj₂ lifted)

    moves : Moves (RT Rt Cr) [] (RT Rt Cr↑)
    moves = proj₂ (proj₂ lifted)

    -- the body, fed
    body : ∀ {b} → Sync (binds (CS.src k) (CS.connAt k) (scopeOf c)) (Parts.Rb pt) (bef p) b β → NoIsle b
         → Sync (binds (CS.src k) (CS.connAt k) (scopeOf c)) (Parts.Rb pt) (aft p) (feed (here refl) p e b) β
    body sy ni = feed-up sy (Parts.sb pt) (λ r → Parts.apart pt r rs)
                (subst (λ x → pendRows (full x) (CS.src k) (CS.connAt k ++ [ ix 1 ]) p (toEv e)) sc fk
                , λ ce → Sound.ends (Parts.ss pt) (subst (λ x → pendRows (full x) (CS.src k) (CS.connAt k ++ [ ix 1 ]) _ end) (sym sc) ce) fk (vis e))
                nh ni

    -- the body's end not at `p`, passed past it, passed before it
    bend : ∀ {c} → β c end → ¬ Owes (aft p) c → ¬ Owes (bef p) c
    bend {c} y n o = n (Past.owes-up p (λ { refl → Parts.apart pt (Sound.rg (Parts.sb pt) y tt) rs }) o)

    -- a value: the source runs on, unclosed
    flags-on : T (not (CS.closed k)) → (toEv e ≡ end → ⊥) → Flags (bef p) k β → Flags (aft p) k β
    flags-on nc ne fl = record
      { shut   = λ t → torn nc t
      ; unshut = λ t {c} y n → Flags.unshut fl t y λ pc → n (≼-≢ {p} {c} pc λ { refl → ne (Sound.fn (Parts.ss pt) fk y (vis e) _) })
      ; torn   = λ nt → torn nt lv
      ; owed   = λ x → proj₁ (Flags.owed fl x) , Past.nm p (proj₂ (Flags.owed fl x))
      ; ended  = λ t y n → Flags.ended fl t y (bend y n)
      ; owing  = Flags.owing fl }

    -- its end: closed where it fell, owing nothing past it
    flags-shut : toEv e ≡ end → Flags (bef p) k β → Flags (aft p) (record k { closed = true ; endAt = p }) β
    flags-shut ee fl = record { shut = λ _ → subst (Frozen k p) ee fk , ≺-irrefl {p} ; unshut = λ _ _ _ → _ ; torn = λ nt → torn nt lv
                              ; owed = λ x → proj₁ (Flags.owed fl x) , Past.nm p (proj₂ (Flags.owed fl x))
                              ; ended = λ t y n → Flags.ended fl t y (bend y n) ; owing = Flags.owing fl }

    src-done : ∀ {s P D} → toEv e ≡ end → TailP (aft p) (Frozen k) P → Husk (scopeOf c) D s (Frozen k) P → Dom (aft p) D → Behind (bef p) (Frozen k)
             → Subd (scopeOf c) (bef p) k → (T (not (CS.srcAtt k)) → AttOwed k × InCall (bef p) k) → AttFin k
             → Src (scopeOf c) (Parts.Rs pt) (aft p) (record k { closed = true ; endAt = p }) s
    src-done ee tp hk dm bh sd ic af =
      src-shut _ (λ (y , v , py) → Sound.ends (Parts.ss pt) (subst (Frozen k p) ee fk) y v py) tp hk dm (Past.behind-up p bh) (Past.subd-up p sd) ic af lv


  rise-src-nx : ∀ {Γ X B} {k : CS Γ X} {b} {c : Ctx R Γ B} {s a p k′ sh t}
              → rise (inSrc k b c) s (nx a) p ≡ moved k′ sh t → SimC Rt ⟨ inSrc k b c , s , rising (nx a) , p ⟩ sh k′
  rise-src-nx {a = a} {p = p} refl (flying (f-src fr sc pt lv nc bs bb fl fz eq bh sd af ao ic ni) cl (sy , row)) =
    let open Fed {e = nx a} fr sc pt lv fz eq row
    in Cr↑ , aft p , settled c-abs fr↑ (s-conn sc pt (λ _ → body bs ni) (λ _ → Past.behind-up p bb)
                                              (λ _ → src-on nc (sync-≈ sy fz) (Past.behind-up p bh) (Past.subd-up p sd) af ao ic lv)
                                              (λ nl → ⊥-elim (notT _ nl lv)) (flags-on nc (λ ()) fl) eq)
     , moves
  -- an isle's source runs on, its body read by none
  rise-src-nx {k = k} {a = a} {p = p} refl (flying (f-isle u hb ub le na nc bh sd ss ao ic bu nr ni oz iz) _ (sy , _)) =
    _ , _ , unread-at Rt u (sh-isle na nc sy (Past.behind-up p bh) (Past.subd-up p sd) ss ao ic bu nr) (feed-husk {i = here refl} {p = p} {e = nx a} hb ni) ub (burst-dn {C = bef p} {C′ = aft p} {k = k} (λ {y} → Past.dn p {y}) le) oz iz
    , silent ≃-refl
  rise-src-nx refl (flying (f-srcc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ ())
  rise-src-nx refl (flying (f-srcp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ ())
  rise-src-nx refl (flying (d-src _ _ _ _ _ _ _ pz oz iz) _ ())
  rise-src-nx refl (flying (f-islec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ oz iz) _ ())
  rise-src-nx refl (flying (f-islep _ _ _ _ _ _ _ _ _ _ _ _ _ _ oz iz) _ ())
  rise-src-nx refl (adrift (f-srcc _ _ _ _ cl _ _ _ _ _ _ _ _ _ _ _) cl′ _)  = ⊥-elim (or-shut cl cl′)
  rise-src-nx refl (adrift (f-islec _ _ _ _ _ cl _ _ _ _ _ _ _ _ _ oz iz) cl′ _) = ⊥-elim (or-shut cl cl′)
  rise-src-nx {a = a} {p = p} refl (adrift (d-src u hb ub ud le ni f pz oz iz) _ (Q , hk , le′)) =
    _ , _ , unread-at Rt u (sh-dead hk ud f pz) (feed-husk {i = here refl} {p = p} {e = nx a} hb ni) ub (⊑-trans le (∪-⊑ (under-⊑ le′) ⊑-refl)) oz iz
    , silent ≃-refl
  rise-src-nx refl (settled () _ _)

  -- Its end: the connect closed where it fell, while it runs.
  rise-src-cp : ∀ {Γ X B} {k : CS Γ X} {b} {c : Ctx R Γ B} {s p k′ sh t}
              → rise (inSrc k b c) s cp p ≡ moved k′ sh t → SimC Rt ⟨ inSrc k b c , s , rising cp , p ⟩ sh k′
  rise-src-cp {k = k} {b} {c} {s} {p} refl (flying (f-src fr sc pt lv nc bs bb fl fz eq bh sd af ao ic ni) cl (sy , row)) =
    let open Fed {e = cp} fr sc pt lv fz eq row
        sy′ = sync-≈ sy fz
    in Cr↑ , aft p
     , subst (λ k″ → Inv Rt Cr↑ (aft p) ⟨ c , connS k″ s (feed (here refl) p cp b) , absorbed , p ⟩) (sym (shut-live {k = k} {p} lv))
             (settled c-abs fr↑ (s-conn sc (re-parts refl refl pt) (λ _ → body bs ni) (λ _ → Past.behind-up p bb)
                                        (λ _ → src-done refl (end-tail sy′ (Parts.ss pt) fk (≺-irrefl {p})) (proj₂ (husk-of sy′)) (λ t → t) bh sd (λ na → ao na , ic na) af)
                                        (λ nl → ⊥-elim (notT _ nl lv)) (flags-shut refl fl) eq))
     , moves
  -- an isle's source ends inside its subscribe call: still an isle
  rise-src-cp {k = k} {b} {c} {s} {p} refl {Cr = Cr} (flying (f-isle u hb ub le na nc bh sd ss ao ic bu nr ni oz iz) _ (sy , row)) =
    shut-by {k = k} {p} (λ k″ → After Rt Cr ⟨ c , connS k″ s (feed (here refl) p cp b) , absorbed , p ⟩)
      (λ lt → _ , _ , unread-at Rt (unread-live Rt lt u)
                        (sh-islec na tt (λ (y , v , py) → Sound.ends ss row y v py) (end-tail sy ss row (≺-irrefl {p})) (proj₂ (husk-of sy)) (λ t → t)
                                  (Past.behind-up p bh) (Past.subd-up p sd) ao ic bu nr)
                        fed ub (burst-dn {C = bef p} {C′ = aft p} {k = k} (λ {y} → Past.dn p {y}) le) (λ ()) iz , silent ≃-refl)
      (λ _ → _ , _ , unread-at Rt u (sh-isle na nc sy (Past.behind-up p bh) (Past.subd-up p sd) ss ao ic bu nr) fed ub (burst-dn {C = bef p} {C′ = aft p} {k = k} (λ {y} → Past.dn p {y}) le) oz iz , silent ≃-refl)
    where fed = feed-husk {i = here refl} {p = p} {e = cp} hb ni
  rise-src-cp refl (flying (f-srcc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ ())
  rise-src-cp refl (flying (f-srcp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ ())
  rise-src-cp refl (flying (d-src _ _ _ _ _ _ _ pz oz iz) _ ())
  rise-src-cp refl (flying (f-islec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ oz iz) _ ())
  rise-src-cp refl (flying (f-islep _ _ _ _ _ _ _ _ _ _ _ _ _ _ oz iz) _ ())
  rise-src-cp refl (adrift (f-srcc _ _ _ _ cl _ _ _ _ _ _ _ _ _ _ _) cl′ _)  = ⊥-elim (or-shut cl cl′)
  rise-src-cp refl (adrift (f-islec _ _ _ _ _ cl _ _ _ _ _ _ _ _ _ oz iz) cl′ _) = ⊥-elim (or-shut cl cl′)
  rise-src-cp {k = k} {b} {c} {s} {p} refl {Cr = Cr} (adrift (d-src u hb ub ud le ni f pz oz iz) _ (Q , hk , le′)) =
    shut-by {k = k} {p} (λ k″ → After Rt Cr ⟨ c , connS k″ s (feed (here refl) p cp b) , absorbed , p ⟩)
      (λ lt → _ , _ , unread-at Rt (unread-live Rt lt u) (sh-dead hk ud (inj₂ tt) pz) fed ub le″ (λ ()) iz , silent ≃-refl)
      (λ _ → _ , _ , unread-at Rt u (sh-dead hk ud f pz) fed ub le″ oz iz , silent ≃-refl)
    where
      fed = feed-husk {i = here refl} {p = p} {e = cp} hb ni
      le″ = ⊑-trans le (∪-⊑ (under-⊑ le′) ⊑-refl)
  rise-src-cp refl (settled () _ _)
