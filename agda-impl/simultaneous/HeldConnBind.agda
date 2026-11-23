{-# OPTIONS --guardedness #-}

-- A CONNECT'S BINDER HELD: its annotated source made a binder at the
-- connect's subscription, kept apart from every binder in scope, and the
-- body subscribed outside every binder's last gap.
module simultaneous.HeldConnBind where

open import Data.List using (List; _∷_; [_])
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.List.Relation.Unary.All using (lookup; _∷_) renaming ([] to []ᵉ)
open import Data.Maybe using (Maybe; nothing)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import Tree using (Obs; map; connect)
open import denotation.Position using (Pos; root; _≟ᵖ_; ix; last; _⊕_; sub)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (EmissionSet; Den; hot; enter; Proper; DenEnv)
open import simultaneous.SObs using (lone; ext; module Elaborate)
open import simultaneous.Routed using (Early; Placed; PlacedD; Adm; Shown; s-value; s-end)
open import simultaneous.LaneLocal using (inv-ev)
open import simultaneous.CombSent using (hots-at)
open import simultaneous.Layers using (pinby-vis)
open import denotation.Laws.Worlds using (InvAt; W; step; here; inW; plain-ix; ⊑-snoc⁺; ⊑-trans; ⊕-injˡ; ⊕-injʳ)
open import denotation.EmissionSet using (Ev)
open import Data.Sum using (inj₂; _⊎_)
open import simultaneous.HeldIn using (held-in)
open import denotation.Laws.Worlds using (Hots; GoodEnv)
open import simultaneous.CombSent using (src-op; own-op; cat-op; tag-op; no-track; no-close; tag-branch; Cat-of; Tag; sent-branch; Closing; closing-mark; closing-value; closer-marks; closer-good; src-where; Where) renaming (under to w-under; past to w-past)
open import denotation.EmissionSet using (map-end) renaming (ended to r-ended; late to r-late; shown to r-shown)
open import simultaneous.HeldConnect using (early-inst)
open import denotation.Laws using (good-cons)
open import denotation.Laws.Worlds using (Ok)
open import denotation.Laws.Connect using () renaming (lawful to src-lawful; ok₀ to body-ok)
open import Data.Empty using (⊥)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Unit using (tt)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; Routes; count; elab; srcLane; laneSrc; annotate; marked; trackers; closer; combined; laneˢ; each; coldˢ;
  Input; react; going; fed; opening; anyHolds; branch; restamp; wrapped; mapIE; scanIE; passes)
open import simultaneous.HeldComb using (ev)
open import denotation.Laws.Worlds using (⊑-inside)
import Relation.Nullary as Nl
open import Data.Product using (Σ; proj₂)
open import simultaneous.Layers using (run-tail) renaming (run-row to run-row∈)
open import denotation.Read using (Visible)
open import denotation.EmissionSet using (out; end)
open import denotation.Laws.Worlds using (ok-step; _⊑_)
open import denotation.Laws.Worlds using (Anc; anc-lead; anc-view; parent-fun; step-parent; world-anc; real-snoc)
open import denotation.Laws.Modulus using (ticks)
open import denotation.Laws.Worlds using (w-up; shrink⁼)
open import denotation.Read using (Visible)
open import Data.Sum using (inj₁)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (sym; subst)
open import denotation.Read using (Run)
import denotation.Read as Run

open import simultaneous.HeldBase using (AShown; a-value; a-end; GapIn; Gap; Ann; Bound; EnvHeld; Fresh; IH; ih; fresh-adm; widen; ev-undone; eh-u;
  conn-ev; connect-tracks; placed-conn; apart-at; gap-hot)
open import simultaneous.HeldRead using (s₀; Src; ann-row; ann-end; module AnnConn; ann-just; ann-none)
open import simultaneous.HeldBack using (ann-last; src-ann-end)
open import simultaneous.HeldComb using () renaming (run-row to run-row⁺)
open import denotation.Laws.Worlds using (⊑-cmp; ⊑-refl; same-lead)
open import denotation.Laws.Modulus using (≼-split)

-- A connect's annotated source, read at its own subscription.
AnnAt : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (s : Obs Timeline Γ A) (env : DenEnv Δ) → Pos → EmissionSet (AIE A)
AnnAt m ρ s env p = enter (ev m (annotate (elab ρ s)) env) (p ⊕ [ ix 1 ])

-- A BINDER'S OWN ROWS LIE OUTSIDE ITS LAST GAP.  The gap's lane is the
-- one its source's end opens, its nothing the annotation's only one: a
-- value lies under a source row, which neither leads the source's end nor
-- lies under it, and the end lies past the gap's lane.
own-apart : ∀ {X} {d : Den (AIE X)} {cs} (b : Bound d cs) → ∀ {y e} → Ann b y e → AShown e → Nl.¬ Gap b y
own-apart b {y} a sh (c , r , an , h , nl) with ann-row b an
... | pre , we , _ , run , _ , _ , ann-none = src-ann-end b swe λ (_ , am′ , ae′) → go a sh (gl am′) ae′
  where
    open Bound b using (m; src; env; good; at; ok)
    IA = inv-ev m (annotate src) env good (at ⊕ [ ix 1 ]) (ok-step at ok)
    IS = inv-ev m src env good (s₀ b) (ok-step (at ⊕ [ ix 1 ]) (ok-step at ok))
    swe = proj₁ (run-row⁺ pre run)
    G = (we ⊕ [ sub (AnnConn.sb b) ]) ⊕ [ ix 1 ]
    gl : ∀ {r′} → Ann b (G ⊕ [ ix 0 ]) (out (r′ , nothing)) → G ≡ c ⊕ [ ix 1 ]
    gl am′ with ≼-split {G ⊕ [ ix 0 ]} {(c ⊕ [ ix 1 ]) ⊕ [ ix 0 ]} (ann-last b an am′)
    ... | inj₁ lt = ⊥-elim (ann-last b am′ an lt)
    ... | inj₂ eq = ⊕-injˡ G (c ⊕ [ ix 1 ]) eq
    clash : ∀ {k k′ x} → Src b k (out x) → Src b k′ end → k ⊑ k′ ⊎ k′ ⊑ k → ⊥
    clash sk sk′ (inj₁ le) with same-lead IS sk sk′ le
    ... | refl with InvAt.func IS sk sk′
    ...   | ()
    clash sk sk′ (inj₂ le) with same-lead IS sk′ sk le
    ... | refl with InvAt.func IS sk sk′
    ...   | ()
    go : ∀ {e} → Ann b y e → AShown e → G ≡ c ⊕ [ ix 1 ] → Ann b (G ⊕ [ last ]) end → ⊥
    go av a-value eg _ with ann-row b av
    ... | pre′ , w , _ , run′ , _ , rl , ann-just = clash (proj₁ (run-row⁺ pre′ run′)) swe lead
      where
        weG : we ⊑ (c ⊕ [ ix 1 ])
        weG = subst (we ⊑_) eg (⊑-trans (⊑-snoc⁺ we) (⊑-snoc⁺ (we ⊕ [ sub (AnnConn.sb b) ])))
        lead : w ⊑ we ⊎ we ⊑ w
        lead with ⊑-cmp w (c ⊕ [ ix 1 ]) rl h
        ... | inj₂ cw = inj₂ (⊑-trans weG cw)
        ... | inj₁ wc = ⊑-cmp w we wc weG
    go ae a-end eg ae′ with ≼-split {y} {G ⊕ [ last ]} (λ lt → pinby-vis tt (InvAt.quiet IA ae′ ae lt))
    ... | inj₁ lt = pinby-vis tt (InvAt.quiet IA ae ae′ lt)
    ... | inj₂ eq = nl (subst (λ z → ((c ⊕ [ ix 1 ]) ⊕ [ last ]) ⊑ z) (sym eq) (subst (λ z → (z ⊕ [ last ]) ⊑ (G ⊕ [ last ])) eg (⊑-refl _)))

-- AN OLDER BINDER'S ROWS ARE HOT, AND NONE IN THE NEW BINDER'S WORLD:
-- a value or end is a hot row, and a gap's lane lies in the world of `p`.
apart-old : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (s : Obs Timeline Γ A) (env : DenEnv Δ) cs → GoodEnv env
          → (eh : EnvHeld ρ env cs) → ∀ p → Ok (Hots env) p
          → ∀ {Y} (j : Y ∈ Γ) {y e} → Ann (EnvHeld.bound eh j) y e → AShown e → Nl.¬ GapIn (AnnAt m ρ s env p) y
apart-old m ρ s env cs g eh p ok j {y} a sh (c , r , a′ , h , _) = proj₂ ok hy lane (⊑-inside h)
  where
    b  = EnvHeld.bound eh j
    IB = inv-ev (Bound.m b) (annotate (Bound.src b)) (Bound.env b) (Bound.good b) (Bound.at b ⊕ [ ix 1 ]) (ok-step (Bound.at b) (Bound.ok b))
    IA = inv-ev m (annotate (elab ρ s)) env g (p ⊕ [ ix 1 ]) (ok-step p ok)
    vis : ∀ {X} {e : Ev (AIE X)} → AShown e → Visible e
    vis a-value = tt
    vis a-end   = tt
    hy : Hots env y
    hy = hots-at env (ρ (∈-map⁺ AIE j)) (Bound.is b) (a , λ ce cq → pinby-vis (vis sh) (InvAt.quiet IB ce a cq))
    lane : W (Hots env) p (c ⊕ [ ix 1 ])
    lane with w-up plain-ix (inW (InvAt.world IA a′))
    ... | inj₂ v = shrink⁼ v
    ... | inj₁ eq with ⊕-injʳ p (c ⊕ [ ix 1 ]) eq
    ...   | ()

-- THE BODY IS SUBSCRIBED OUTSIDE ITS SOURCE'S GAPS: a gap's lane descends
-- from the source's subscription at `p ⊕ [ ix 1 ]`, and nothing that does
-- leads `p ⊕ [ ix 0 ]`, reachable before it.
body-fresh : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (s : Obs Timeline Γ A) (env : DenEnv Δ) → GoodEnv env
           → ∀ p → Ok (Hots env) p → Nl.¬ GapIn (AnnAt m ρ s env p) (p ⊕ [ ix 0 ])
body-fresh m ρ s env g p ok (c , r , a , h , _) =
  anc-lead (lane (world-anc (InvAt.world IA a))) h (real-snoc p plain-ix (proj₁ ok)) (ticks p 0)
  where
    IA = inv-ev m (annotate (elab ρ s)) env g (p ⊕ [ ix 1 ]) (ok-step p ok)
    lane : Anc (p ⊕ [ ix 1 ]) ((c ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) → Anc (p ⊕ [ ix 1 ]) (c ⊕ [ ix 1 ])
    lane x with anc-view x
    ... | inj₁ eq with ⊕-injʳ p (c ⊕ [ ix 1 ]) eq
    ...   | ()
    lane x | inj₂ (_ , y , pb) with parent-fun pb (step-parent (c ⊕ [ ix 1 ]) plain-ix)
    ...   | refl = y

-- A CONNECT'S BINDER, made at `p`: its source held below the annotation,
-- and the binders in scope widened past it.
module ConnBind (m : Maybe ℕ) {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (s : Obs Timeline Γ A) (hs : IH m ρ s)
                (env : DenEnv Δ) (cs : List Pos) (g : GoodEnv env) (eh : EnvHeld ρ env cs)
                (p : Pos) (ok : Ok (Hots env) p) (fr : Fresh eh p) (ep : Early p) where

  ad = fresh-adm eh

  σ : EmissionSet (AIE A)
  σ = Proper (AnnAt m ρ s env p)

  nb : Bound (hot σ) (p ∷ cs)
  nb = record
    { m = m ; src = elab ρ s ; env = env ; at = p ; outer = cs
    ; held = IH.holds hs env cs g eh ((p ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) (ok-step _ (ok-step p ok))
               (Adm.step ad (ok-step p ok) (Adm.step ad ok fr plain-ix) plain-ix) (early-inst [ ix 1 ] (early-inst [ ix 1 ] ep))
    ; good = g ; undone = ev-undone m ρ s env (eh-u eh) ; ok = ok ; ep = ep ; under = λ i → i ; is = refl }

  bd : ∀ {X} (i : X ∈ A ∷ Γ) → Bound (lookup (hot σ ∷ env) (ext ρ (∈-map⁺ AIE i))) (p ∷ cs)
  bd (here refl) = nb
  bd (there i)   = widen (EnvHeld.bound eh i)

  pl = IH.placed hs env cs g eh

  -- A NEW BINDER'S ROWS LIE OUTSIDE EVERY OLDER BINDER'S GAP: each lies
  -- under a source row, admissible where the source is placed, and an
  -- older gap's nothing is a hot row no source row leads.
  new-apart : ∀ {Y} (j : Y ∈ Γ) {y e} → AnnAt m ρ s env p y e → AShown e → Nl.¬ Gap (EnvHeld.bound eh j) y
  new-apart j {y} a sh (c , r , an , h , nl) = from (src-of sh a)
    where
      ok₂ = ok-step (p ⊕ [ ix 1 ]) (ok-step p ok)
      IS = inv-ev m (elab ρ s) env g (s₀ nb) ok₂
      at₂ : PlacedD (Hots env) (Fresh eh) (ev m (elab ρ s) env) → Placed (Fresh eh) (Src nb)
      at₂ pd = pd (s₀ nb) ok₂ (Adm.step ad (ok-step p ok) (Adm.step ad ok fr plain-ix) plain-ix) (early-inst [ ix 1 ] (early-inst [ ix 1 ] ep))
      Row : Set
      Row = Σ Pos λ w → Σ _ λ e₀ → Src nb w e₀ × Shown e₀ × w ⊑ y
      src-of : ∀ {e} → AShown e → AnnAt m ρ s env p y e → Row
      src-of a-value a′ with ann-row nb a′
      ... | pre , w , _ , run , _ , rl , ann-just = w , _ , proj₁ (run-row⁺ pre run) , s-value , rl
      src-of a-end a′ with ann-end nb a′
      ... | w , rl , se = w , end , se , s-end , rl
      from : Row → ⊥
      from (w , _ , sw , shw , rl) with ⊑-cmp w (c ⊕ [ ix 1 ]) rl h
      ... | inj₁ wc = proj₂ ok₂ (gap-hot eh j an) (InvAt.world IS sw) (⊑-inside (⊑-trans wc (⊑-snoc⁺ (c ⊕ [ ix 1 ]))))
      ... | inj₂ cw = apart-at (at₂ pl sw shw) j (c , r , an , cw , λ lw → nl (⊑-trans lw rl))

  ap : ∀ {X Y} (i : X ∈ A ∷ Γ) (j : Y ∈ A ∷ Γ) {y e} → Ann (bd i) y e → AShown e → Nl.¬ Gap (bd j) y
  ap (here refl) (here refl) = own-apart nb
  ap (here refl) (there j)   = new-apart j
  ap (there i)   (here refl) = apart-old m ρ s env cs g eh p ok i
  ap (there i)   (there j)   = EnvHeld.apart eh i j

  eh′ : EnvHeld (ext ρ) (hot σ ∷ env) (p ∷ cs)
  eh′ = record { bound = bd ; apart = ap }

  fr′ : Fresh eh′ (p ⊕ [ ix 0 ])
  fr′ = body-fresh m ρ s env g p ok , Adm.bare ad fr (λ ())

held-connect : ∀ m {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B)
             → IH m ρ s → (∀ {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE (A ∷ Γ) → X ∈ Δ′) → IH m ρ′ b) → IH m ρ (connect s b)
held-connect m ρ s b hs hb = ih
  (λ env cs g eh p ok fr ep → let open ConnBind m ρ s hs env cs g eh p ok fr ep in
    conn-ev m (annotate (elab ρ s)) _ env cs g p ok ep (connect-tracks m ρ s b env cs g eh p ok ep) λ L ok₀ ep₀ →
      held-in (IH.holds (hb _) _ (p ∷ cs) (good-cons L g) eh′ (p ⊕ [ ix 0 ]) ok₀ fr′ ep₀))
  λ env cs g eh p ok fr ep → let open ConnBind m ρ s hs env cs g eh p ok fr ep in
    placed-conn m (annotate (elab ρ s)) _ env g proj₂ p ok λ L ok₀ →
      IH.placed (hb _) _ (p ∷ cs) (good-cons L g) eh′ (p ⊕ [ ix 0 ]) ok₀ fr′ (early-inst [ ix 0 ] ep)
