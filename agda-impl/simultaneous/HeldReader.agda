{-# OPTIONS --guardedness #-}

-- A BOUND BINDER'S READER HOLDS, from the rows `HeldRead` places: every
-- row lies under a source row, is the reader's own end, or lies under
-- the annotation's connect body, before the source; so the reader's
-- marks route and its counts are the source's (`HeldJoin`).
module simultaneous.HeldReader where

open import Data.List using (List; []; _∷_; [_]; _++_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ʳ)
open import Data.Bool using (true; false; T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong)
open import Tree using (mergeᶠ)
open import denotation.Position using (sub)
open import denotation.EmissionSet using (Ev; hot; Proper; module Op)
open import denotation.Laws.Worlds using (⊕-assoc)
open import denotation.Read using (_∷_; [])
open import simultaneous.Routed using (cnt)
open import simultaneous.DenRows using (hot-out; scan-out)
open import simultaneous.Layers using (run-row)
open import simultaneous.HeldJoin using (jl; zero-suc)
open import Tree using (map)
open import simultaneous.Relations using (values)
open import denotation.Position using (last)
open import denotation.EmissionSet using (module Merge; module Scan; Ended; _≺_; _≼_) renaming (ended to r-ended; late to r-late; shown to r-shown)
open import denotation.Laws.Worlds using (InvAt; Hots; ⊕-identityʳ)
open import denotation.Laws.Modulus using (≼-split; ≺-irrefl; ≺-≼-≺; ≼-trans)
open import simultaneous.Layers using (from≺)
open import simultaneous.LaneLocal using (inv-ev)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (lookup) renaming ([] to []ᵉ; _∷_ to _∷ᵉ_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Data.List using (List; []; _∷_; [_])
open import Data.Bool using (true; false)
open import Data.Empty using (⊥-elim)
open import Data.Maybe using (nothing)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl)
import Relation.Nullary as Nl
open import Tree using (mergeᶠ)
open import denotation.Position using (Pos; ix; _⊕_; sub)
open import denotation.EmissionSet using (EmissionSet; Den; enter; hot; Proper; module Op; module Merge; module Scan; heard; out; LaneOf) renaming (shown to r-shown; ended to r-ended; late to r-late)
open import denotation.Read using (Visible)
open import simultaneous.HeldBase using (Bound)
open import simultaneous.HeldRead using (JS; Fl; lane-in)
open import simultaneous.DenRows using (scan-out; hot-out)
open import denotation.EmissionSet using (Ended; _≺_; end)
open import denotation.Position using (last)
open import denotation.Laws.Modulus using (≼-refl; ≺-irrefl; ≺-≼-≺; ≼-trans)

open import Tree using (connected)
open import denotation.Position using (Pos; ix; _⊕_)
open import denotation.EmissionSet using (EmissionSet; Den; enter; out; end)
open import denotation.Laws.Worlds using (ok-step; ⊑-inside; inside-⊑; ⊑-trans; _⊑_)
open import simultaneous.InstEmit using (instEmit; value; mark; begin; over; completed)
open import simultaneous.Relations using (Met)
open import simultaneous.Routed using (Held; Early; Ex; Sync; Rest; nameOf; r-begin; Routing; Valued; opos)
open import simultaneous.Readings using (rootOf)
open import simultaneous.Relabel using (same-mark; same-value)
open import simultaneous.HeldConnect using (rootOf-ext; early-inst)
open import simultaneous.HeldTake using (name-ext; ex-ext)
open import simultaneous.HeldComb using (ev)
open import simultaneous.HeldBase using (Bound; IH; ih; Ann; Gap; EnvHeld; Fresh; apart-at)
open import simultaneous.Routed using (PlacedD)
import Relation.Nullary as Nl
open import simultaneous.HeldJoin using (module Join)

open import Data.Unit using (tt)
open import denotation.EmissionSet using (DenEnv; skip; pin)
open import denotation.Laws.Worlds using (world-after; GoodEnv)
open import denotation.Read using (Visible; After; cursor)
open import denotation.Laws.Modulus using (≺-trans)
open import denotation.Laws.Worlds using (⊑-≼)
open import denotation.Events using (<ᵖ-apart)
open import denotation.Position using (_<ᵖ_)
open import simultaneous.Layers using (to≺; cursor-++)
open import simultaneous.Relabel using (RowsAt; []ᵃ; _∷ᵃ_)
open import simultaneous.HeldJoin using (j-late; j-part; j-read; module Past; begins-held; out-in; is-begin; Sim)
open import Data.List.Properties using (++-identityʳ)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ)
open import simultaneous.HeldTrigger using (≺-part)
open import denotation.EmissionSet using (heard; LaneOf; Ended)
open import denotation.Laws.Modulus using (≼-refl)
open import simultaneous.HeldRead using (RD; Rl; Src; Under; body; held-src; read-end; read-row; s₀; z₀; pre-noend)
open import simultaneous.HeldShow using (read-shows)
open import simultaneous.HeldReadBack using (read-back; read-part; Part; Further; further)
open import simultaneous.HeldJoin using (begin-name; cnt-++; mem-of; jl-in; Begins)
open import simultaneous.HeldHot using (em)
open import simultaneous.HeldBase using (shows-ev)
open import simultaneous.Layers using (pinby-vis; snoc-view; run-tail; cursor-snoc; cursor-in; pre-∈)
open import simultaneous.Project using (run-prefix)
open import simultaneous.Routed using (Idle)
open import denotation.Read using (Run; Least; loud)
open import denotation.EmissionSet using (Few; Silent)
open import denotation.Position using (Path; Label)
open import denotation.Events using (<ᵖ-between)
open import denotation.Laws.Modulus using (≺-ext; ≼-or-≻; entered-few; ≺→≼)
open import denotation.Laws.Worlds using (full; Shows)
open import denotation.Laws.Shows using (cover; cov-∈; few-down)
open import Data.List.Properties using (++-assoc)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻)
open import Data.List.Relation.Unary.Any using (any?) renaming (map to any-map)
open import Data.Nat using (_≟_)
open import Data.Sum using ([_,_]′)
open import Relation.Nullary.Decidable using (decidable-stable; _⊎-dec_)
open import simultaneous.Relabel using (endAt)
open import simultaneous.HeldRead using (Rl-trans; under-ext; rd-mg; module AnnConn; ev-ann; ev-cn; CnO; Cn; Fm)
open import simultaneous.HeldMap using (module MapRun)
open import simultaneous.HeldFan using (read-fan)
open import denotation.EmissionSet using (module Connecting)
open import denotation.Events using (Timeline; fresh)
open import denotation.Position using (_≟ᵖ_; root)
open import simultaneous.SObs using (lone; module Elaborate)

open import denotation.Laws using (inv-⟦⟧; good-cons)
open import denotation.Laws.Worlds using (Ok)
open import denotation.Laws.Worlds.Leaves using (ine-pin)
open import denotation.EmissionSet using (coldAt)
open import simultaneous.TableEnv using (ok-mono)
open import simultaneous.CombSent using (hots-at)
open import simultaneous.HeldReadBack using (read-joined; module Back)
open import simultaneous.Layers using (run-past-end)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.Bool using (if_then_else_)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; Routes; count; reader; annotate; annStep; joinStep; concatˢ; elab)

-- A position past one below a row is past the row.
below-≺ : ∀ y xs {w} → (y ⊕ xs) ≺ w → y ≺ w
below-≺ y []       {w} h = subst (_≺ w) (⊕-identityʳ y) h
below-≺ y (l ∷ xs) {w} h = ≺-trans {y} {y ⊕ (l ∷ xs)} {w} (≺-ext y xs) h

-- Past one position below a row and not past another, a position lies below the row.
sandwich : ∀ y zs zs′ {w} → (y ⊕ zs) ≺ w → w ≼ (y ⊕ zs′) → Σ Path λ ys → w ≡ y ⊕ ys
sandwich y zs zs′ {w} a b =
  [ (λ lt → <ᵖ-between y w zs′ (from≺ y w (below-≺ y zs a)) (from≺ w (y ⊕ zs′) lt)) , (λ eq → zs′ , eq) ]′ (≼-split {w} {y ⊕ zs′} b)

-- The first row of a run has few rows before it and is the least past its cursor.
run-head : ∀ {A} {t : EmissionSet A} {c q e rs} → Run t c ((q , e) ∷ rs) → Few t q × Least t c q
run-head ((((_ , _) , fk) , _ , lst) ∷ _) = fk , lst

-- EVERY ROW OF THE ANNOTATION LIES UNDER A SOURCE ROW, or under its
-- connect body: the body's own steps, the concat's, lie under no source
-- row.  Its scan and map keep their source's positions; the connect's
-- subject rows lie under the source's, its body's under the concat's
-- outer, or under the hot reading of the source and that reading's ends.
module AnnUnder {X} {d : Den (AIE X)} {cs} (b : Bound d cs) where
  module A = AnnConn b

  rl0 : ∀ {k} → Rl k k
  rl0 {k} = [] , sym (⊕-identityʳ k)

  σ-u : ∀ {k e} → A.σ k e → Under b k
  σ-u {k} x with A.MR.unmap x
  ... | e₀ , sk , _ = inj₁ (k , e₀ , rl0 , sk)

  hr-u : ∀ {k e} → A.HR.Rd k e → Under b k
  hr-u (r-shown (x , _) _ _ , _) = under-ext b ([ sub A.sb ] , refl) (σ-u x)
  hr-u (heard (x , _) _ , _)    = under-ext b ([ sub A.sb ] , refl) (σ-u x)
  hr-u (r-ended (x , _) _ , _)  = under-ext b ([ sub A.sb ] , refl) (σ-u x)
  hr-u (r-late _ _ , _)         = inj₂ (Rl-trans ([ last ] , refl) (Rl-trans ([ ix 1 ] , refl) ([ ix 0 ] , refl)))

  u-u : ∀ {k e} → A.CT.U k e → Under b k
  u-u (A.CT.src y _) = hr-u (A.to y)
  u-u (A.CT.hnd y)   = under-ext b ([ ix 0 ] , refl) (hr-u (A.to y))
  u-u (A.CT.mk y)    = under-ext b (Rl-trans ([ ix 0 ] , refl) ([ ix 1 ] , refl)) (hr-u (A.to y))
  u-u (A.CT.fin y)   = under-ext b (Rl-trans ([ last ] , refl) ([ ix 1 ] , refl)) (hr-u (A.to y))

  base-u : ∀ {k} → k ∈ A.CT.base → Rl k (body b)
  base-u (here refl)                 = Rl-trans ([ ix 0 ] , refl) ([ ix 0 ] , refl)
  base-u (there (here refl))         = Rl-trans ([ ix 0 ] , refl) ([ ix 1 ] , refl)
  base-u (there (there (here refl))) = [ last ] , refl

  c-u : ∀ {k e} → A.CT.C k e → Under b k
  c-u y with A.CT.classify (proj₁ y)
  ... | inj₁ i      = inj₂ (base-u i)
  ... | inj₂ (_ , u) = u-u u

  module Cc = Connecting A.a₁ A.σ (enter (Fm (Bound.m b) (Bound.env b) (hot (Proper A.σ))) A.P₀)

  cc-u : ∀ {k e} → enter (Op.connect (Op.map just A.D) (Fm (Bound.m b) (Bound.env b))) A.a₁ k e → Under b k
  cc-u (Cc.body y , _)         = c-u y
  cc-u (Cc.burst y _ , _)      = under-ext b ([ ix 0 ] , refl) (σ-u y)
  cc-u (Cc.echo y _ _ _ , _)   = under-ext b ([ ix 0 ] , refl) (σ-u y)
  cc-u (Cc.kept y _ _ _ , _)   = under-ext b ([ ix 0 ] , refl) (σ-u y)

  cn-u : ∀ {k e} → Cn b k e → Under b k
  cn-u {k} {e} x = cc-u (subst (λ D′ → enter D′ A.a₁ k e) (ev-cn (Bound.m b) (Bound.src b) (Bound.env b)) x)

  Sa : Den (Routes × AIE X)
  Sa = Op.scan annStep z₀ (ev (Bound.m b) (CnO (Bound.src b)) (Bound.env b))

  sc-u : ∀ {k e} → enter Sa A.a₁ k e → Under b k
  sc-u (Scan.sval (Scan.acc₀ t _) , _)   = cn-u t
  sc-u (Scan.sval (Scan.acc _ t _ _) , _) = cn-u t
  sc-u (Scan.sstep t , _)                = cn-u t
  sc-u (Scan.spin t , _)                 = cn-u t
  sc-u (Scan.send t , _)                 = cn-u t

  module MA = MapRun proj₂ Sa A.a₁

  ann-u : ∀ {y e} → Ann b y e → Under b y
  ann-u {y} {e} aq with MA.unmap (subst (λ D′ → enter D′ A.a₁ y e) (ev-ann (Bound.m b) (Bound.src b) (Bound.env b)) aq)
  ... | _ , s , _ = sc-u s

ann-under : ∀ {X} {d : Den (AIE X)} {cs} (b : Bound d cs) {y e} → Ann b y e → Under b y
ann-under b = AnnUnder.ann-u b

-- A READER SHOWS NO PIN: its scan's pins are the hot's, and a hot joined
-- shows none; its lanes are `of`s.
module NoPin {X} (A : EmissionSet (AIE X)) (p : Pos) where
  D : Den (AIE X)
  D = hot (Proper A)

  Sc : Den (JS X)
  Sc = Op.scan joinStep (true , ([] , [])) D

  hot-nopin : ∀ {k r} → enter D p k (pin r) → ⊥
  hot-nopin (r-shown _ () _ , _)

  sc-nopin : ∀ {k r} → enter Sc p k (pin r) → ⊥
  sc-nopin (Scan.spin h , _) = hot-nopin h

  fl-nopin : ∀ (st : JS X) s {k r} → enter (Fl st) s k (pin r) → ⊥
  fl-nopin st s x = go x
    where
      module Mg = Merge (λ c → Op.of (if c then proj₁ (proj₂ st) else proj₂ (proj₂ st))) (enter (Op.of (true ∷ false ∷ [])) s)
      go : ∀ {k r} → enter (Fl st) s k (pin r) → ⊥
      go (Mg.opin (o , _) , _)                = ine-pin o
      go (Mg.lane _ _ ((l , _) , _) _ _ , _)  = ine-pin l
      go (Mg.left _ _ ((l , _) , _) _ _ , _)  = ine-pin l
      go (Mg.run () _ , _)

  module Mg = Merge Fl (enter Sc p)

  rd-nopin : ∀ {k r} → enter (RD D) p k (pin r) → ⊥
  rd-nopin x with rd-mg D p x
  ... | (Mg.opin y , _)               = sc-nopin y
  ... | (Mg.lane {q = q} {a = a} _ _ (l , _) _ _ , _) = fl-nopin a (q ⊕ [ ix 1 ]) l
  ... | (Mg.left {q = q} {a = a} _ _ (l , _) _ _ , _) = fl-nopin a (q ⊕ [ ix 1 ]) l
  ... | (Mg.run () _ , _)

-- A binder's hot rows are the scope's.
hots-one : ∀ {Δ X} (env : DenEnv Δ) (j : X ∈ Δ) {c} → Hots (lookup env j ∷ᵉ []ᵉ) c → Hots env c
hots-one env j {c} h with lookup env j in eq
... | hot t    = [ (λ { (_ , x) → hots-at env j eq x }) , (λ ()) ]′ h
... | coldAt _ = ⊥-elim h

-- A silent row of a reader of a hot whose rows lie under the source.
module Quiet {X} {d : Den (AIE X)} {cs} (b : Bound d cs) (t : EmissionSet (AIE X)) (u : ∀ {y e} → t y e → Under b y) (p : Pos) where
  D : Den (AIE X)
  D = hot (Proper t)

  hot-q : ∀ {k e′} → enter D p k e′ → Nl.¬ Visible e′ → Under b k
  hot-q (r-shown (aq , _) _ _ , _) _ = under-ext b ([ sub p ] , refl) (u aq)
  hot-q (heard (aq , _) _ , _)    _ = under-ext b ([ sub p ] , refl) (u aq)
  hot-q (r-ended _ _ , _)        nv′ = ⊥-elim (nv′ tt)
  hot-q (r-late _ _ , _)         nv′ = ⊥-elim (nv′ tt)

  Sc : Den (JS X)
  Sc = Op.scan joinStep (true , ([] , [])) D

  F : JS X → Den (IE X)
  F = Fl

  module Mg = Merge F (enter Sc p)

  sc-q : ∀ {k e′} → enter Sc p k e′ → Nl.¬ Visible e′ → Under b k
  sc-q (Scan.sstep h , _) nv′ = hot-q h nv′
  sc-q (Scan.spin h , _)  nv′ = hot-q h nv′
  sc-q (Scan.sval _ , _)  nv′ = ⊥-elim (nv′ tt)
  sc-q (Scan.send _ , _)  nv′ = ⊥-elim (nv′ tt)

  sc-v : ∀ {k st} → enter Sc p k (out st) → Under b k
  sc-v x with scan-out joinStep (true , ([] , [])) D p x
  ... | _ , _ , hq , _ with hot-out hq
  ...   | q₁ , (aq , _) , _ , refl = under-ext b ([ sub p ] , refl) (u aq)

  viaL : ∀ {q st k e′} → enter Sc p q (out st) → LaneOf F q st k e′ → Under b k
  viaL {q} {st} x (l , _) = under-ext b (Rl-trans (lane-in st (q ⊕ [ ix 1 ]) l) ([ ix 1 ] , refl)) (sc-v x)

  -- The reader's own end passes silent only with a lane running: none
  -- runs past a late join.
  sc-end : ∀ {c} → enter Sc p c end → Nl.¬ Mg.Done c → Under b c
  sc-end (Scan.send (r-ended (ce , _) _ , _) , _) nd = under-ext b ([ sub p ] , refl) (u ce)
  sc-end x@(Scan.send (r-late {c₀} (ce , _) cp , _) , _) nd = ⊥-elim (nd ((_ , x , ≼-refl {p ⊕ [ last ]}) , none))
    where
      none : ∀ {q a} → enter Sc p q (out a) → _ → q ≺ (p ⊕ [ last ]) → _ → Ended (LaneOf F q a) (p ⊕ [ last ])
      none xq _ _ _ with scan-out joinStep (true , ([] , [])) D p xq
      ... | _ , _ , hq , _ with hot-out hq
      ...   | q₁ , (_ , prop) , pq , refl = ⊥-elim (≺-irrefl {p} (≺-≼-≺ {p} {q₁} {p} pq (≼-trans {q₁} {c₀} {p} (prop ce) cp)))

  quiet : ∀ {k e′} → enter (Op.flatMap (mergeᶠ nothing) F Sc) p k e′ → Nl.¬ Visible e′ → Under b k
  quiet (Mg.val x , _)               _   = under-ext b ([ ix 0 ] , refl) (sc-v x)
  quiet (Mg.step x , _)              nv′ = sc-q x nv′
  quiet (Mg.opin x , _)              nv′ = sc-q x nv′
  quiet (Mg.oend _ _ , _)            nv′ = ⊥-elim (nv′ tt)
  quiet (Mg.opass x nd , _)          _   = sc-end x nd
  quiet (Mg.lane x _ L _ _ , _)      _   = viaL x L
  quiet (Mg.lend _ _ _ _ _ _ , _)    nv′ = ⊥-elim (nv′ tt)
  quiet (Mg.lpass x _ L _ _ _ , _)   _   = viaL x L
  quiet (Mg.hand _ _ _ _ () , _)
  quiet (Mg.left x _ L _ _ , _)      _   = viaL x L
  quiet (Mg.run () _ , _)
  quiet (Mg.rend () _ _ , _)
  quiet (Mg.rpass () _ _ , _)
  quiet (Mg.rhand () _ , _)

-- A SILENT ROW OF THE READER lies under a source row, or under the
-- annotation's connect body: the hot shows the body's own steps.
read-quiet : ∀ {X} {d : Den (AIE X)} {cs} (b : Bound d cs) p {y e} → enter (RD d) p y e → Nl.¬ Visible e → Under b y
read-quiet {X} b p {y} {e} r nv = Quiet.quiet b (Ann b) (ann-under b) p (rd-mg (hot (Proper (Ann b))) p (subst (λ D′ → enter (RD D′) p y e) (Bound.is b) r)) nv


sync-up : ∀ {c y} zs → Sync (c ⊕ zs) y → Sync c y
sync-up {c} {y} zs (ins , rt) =
  ⊑-inside {c} {y} (⊑-trans {c} {c ⊕ zs} {y} (zs , refl) (inside-⊑ (c ⊕ zs) y ins)) , trans rt (rootOf-ext c zs)

∈-ex : ∀ {cs c y} → c ∈ cs → Sync c y → Ex cs y
∈-ex (here refl) s = here s
∈-ex (there i)   s = there (∈-ex i s)

sub-ex : ∀ {os cs y} → (∀ {c} → c ∈ os → c ∈ cs) → Ex os y → Ex cs y
sub-ex f (here s)  = ∈-ex (f (here refl)) s
sub-ex f (there e) = sub-ex (λ i → f (there i)) e

-- Two runs a row apart move their cursors alike, onto a row met.
cur-just : ∀ {A B} {R : Pos → Pos → Set} {y′ y} {e : Ev (IE A)} {rs′ : List (Pos × Ev (IE B))} {rs} → R y′ y → RowsAt R rs′ rs
         → Σ Pos λ c′ → Σ Pos λ c → cursor (just y′) rs′ ≡ just c′ × cursor (just y) rs ≡ just c × R c′ c
           × Σ (Ev (IE A)) λ e₁ → (c , e₁) ∈ (y , e) ∷ rs
cur-just {e = e} r []ᵃ = _ , _ , refl , refl , r , e , here refl
cur-just r ((r′ , _) ∷ᵃ ra) with cur-just r′ ra
... | c′ , c , e₁ , e₂ , rc , ev , i = c′ , c , e₁ , e₂ , rc , ev , there i

cur-run : ∀ {A B} {R : Pos → Pos → Set} (js : List (Pos × Ev (IE B))) (pre : List (Pos × Ev (IE A))) {y e rs rs′}
        → RowsAt R rs′ ((y , e) ∷ rs)
        → Σ Pos λ c′ → Σ Pos λ c → cursor nothing (js ++ rs′) ≡ just c′ × cursor nothing (pre ++ (y , e) ∷ rs) ≡ just c × R c′ c
          × Σ (Ev (IE A)) λ e₁ → (c , e₁) ∈ (y , e) ∷ rs
cur-run js pre {y} {e} {rs} {(y′ , e′) ∷ rsᵗ′} ((r , _) ∷ᵃ ra) with cur-just {e = e} r ra
... | c′ , c , e₁ , e₂ , rc , ev , i =
  c′ , c , trans (cursor-++ nothing js ((y′ , e′) ∷ rsᵗ′)) e₁ , trans (cursor-++ nothing pre ((y , e) ∷ rs)) e₂ , rc , ev , i

module Reader {X} {d : Den (AIE X)} {cs} (b : Bound d cs) (p : Pos) (ng : Nl.¬ Gap b p) (ep : Early p) (okr : Ok (Hots (d ∷ᵉ []ᵉ)) p) where

  HS : Held (Src b) (s₀ b ∷ Bound.outer b)
  HS = held-src b

  T′ : EmissionSet (IE X)
  T′ = enter (RD d) p

  rt : ∀ {y′ y} → Rl y′ y → rootOf y′ ≡ rootOf y
  rt {y = y} (zs , refl) = rootOf-ext y zs

  lift : ∀ {y} → Ex (s₀ b ∷ Bound.outer b) y → Ex (p ∷ cs) y
  lift {y} (here s) = there (∈-ex (Bound.under b (here refl))
    (sync-up {Bound.at b} {y} [ ix 1 ] (sync-up {Bound.at b ⊕ [ ix 1 ]} {y} [ ix 1 ] s)))
  lift (there e) = there (sub-ex (λ i → Bound.under b (there i)) e)

  exR : ∀ {y′ y} → Rl y′ y → Ex (s₀ b ∷ Bound.outer b) y → Ex (p ∷ cs) y′
  exR (zs , refl) e = lift (ex-ext zs e)

  named : ∀ {y n} → T′ y (out (instEmit (mark begin) n)) → n ≡ nameOf y
  named x with read-row b p x
  ... | inj₁ (y₀ , _ , (zs , refl) , s , same-mark e) = trans (e refl) (trans (Held.named HS s) (sym (name-ext y₀ zs)))
  ... | inj₂ (refl , _) = refl

  ends : ∀ {y} → T′ y end → Early y
  ends x with read-end b p x
  ... | inj₁ (_ , (zs , refl) , s) = early-inst zs (Held.ends HS s)
  ... | inj₂ refl                  = early-inst [ last ] ep

  module J = Join Rl rt exR named (read-joined b p ng) HS

  -- The reader is lawful where it is subscribed.
  IT : InvAt (Hots (d ∷ᵉ []ᵉ)) p T′
  IT = inv-⟦⟧ (reader (connected (here refl))) (d ∷ᵉ []ᵉ) gd p okr
    where
      gd : GoodEnv (d ∷ᵉ []ᵉ)
      gd = subst (λ D′ → GoodEnv (D′ ∷ᵉ []ᵉ)) (sym (Bound.is b)) (good-cons (Back.LA b p ng) (λ ()))

  t-nopin : ∀ {k r} → T′ k (pin r) → ⊥
  t-nopin {k} {r} x = NoPin.rd-nopin (Ann b) p (subst (λ D′ → enter (RD D′) p k (pin r)) (Bound.is b) x)

  -- The source is lawful where the binder subscribes it.
  IS : InvAt (Hots (Bound.env b)) (s₀ b) (Src b)
  IS = inv-ev (Bound.m b) (Bound.src b) (Bound.env b) (Bound.good b) (s₀ b)
         (ok-step (Bound.at b ⊕ [ ix 1 ]) (ok-step (Bound.at b) (Bound.ok b)))

  -- Below a row of the source, before a later one.
  past : ∀ {k y e e′} zs → Src b k e → Src b y e′ → k ≺ y → (k ⊕ zs) ≺ y
  past {k} {y} zs sk sy ky = to≺ (k ⊕ zs) y (<ᵖ-apart k y zs (from≺ k y ky) apart)
    where
      apart : ∀ ys → y ≡ k ⊕ ys → ⊥
      apart []       eq = ≺-irrefl {k} (subst (k ≺_) (trans eq (⊕-identityʳ k)) ky)
      apart (l ∷ ls) eq = InvAt.flat IS sk (subst (λ z → Src b z _) eq sy)

  quiet : ∀ {y} → Under b y
        → (Σ Pos λ y₀ → Σ (Ev (IE X)) λ e₀ → Rl y y₀ × Src b y₀ e₀) ⊎ y ≡ p ⊕ [ last ] ⊎ Rl y (body b)
  quiet (inj₁ s) = inj₁ s
  quiet (inj₂ r) = inj₂ (inj₂ r)

  -- Every row of the reader lies under a row of the source, is its own
  -- end, or lies under the annotation's connect body.
  under : ∀ {y e} → T′ y e → (Σ Pos λ y₀ → Σ (Ev (IE X)) λ e₀ → Rl y y₀ × Src b y₀ e₀) ⊎ y ≡ p ⊕ [ last ] ⊎ Rl y (body b)
  under {e = out x} r with read-row b p r
  ... | inj₁ (y₀ , x₀ , ry , s , _)  = inj₁ (y₀ , out x₀ , ry , s)
  ... | inj₂ (_ , y₀ , e₀ , ry , s) = inj₁ (y₀ , e₀ , ry , s)
  under {e = end} r with read-end b p r
  ... | inj₁ (y₀ , ry , s) = inj₁ (y₀ , end , ry , s)
  ... | inj₂ eq            = inj₂ (inj₁ eq)
  under {e = skip}  r = quiet (read-quiet b p r (λ ()))
  under {e = pin _} r = quiet (read-quiet b p r (λ ()))

  -- A row under the connect body lies before the source's subscribe.
  body-before : ∀ xs → (body b ⊕ xs) ≺ s₀ b
  body-before xs = subst (_≺ s₀ b) (sym (⊕-assoc (Bound.at b ⊕ [ ix 1 ]) [ ix 0 ] xs)) (≺-part (Bound.at b ⊕ [ ix 1 ]) xs [] refl)

  module Fan {w x} (rw : T′ w (out x)) where
    fan : Pos → List Pos
    fan y₀ = proj₁ (read-fan b p rw y₀)

    fans : List Pos → List Pos
    fans []       = []
    fans (k ∷ ks) = fan k ++ fans ks

    fans-in : ∀ {k ks y} → k ∈ ks → y ∈ fan k → y ∈ fans ks
    fans-in {ks = k ∷ ks} (here refl) i = ∈-++⁺ˡ i
    fans-in {ks = k ∷ ks} (there j)   i = ∈-++⁺ʳ (fan k) (fans-in j i)

  RestAt : List (Pos × Ev (IE X)) → Pos → Set
  RestAt rs′ q = Σ (List Pos) λ ks → ∀ {y e} → T′ y e → After (cursor nothing rs′) y → rootOf y ≡ rootOf q → y ∈ ks

  -- The reader's rows past its cursor lie under the source's rows past
  -- the source's cursor, under the cursor's row, or are its end.
  lift-rest : ∀ {w x} → T′ w (out x) → ∀ {rs′ q q₀ c₀ ws e₁} → cursor nothing rs′ ≡ just (c₀ ⊕ ws) → Src b c₀ e₁ → rootOf q₀ ≡ rootOf q
            → (ks : List Pos) → (∀ {y e} → Src b y e → c₀ ≺ y → rootOf y ≡ rootOf q₀ → y ∈ ks)
            → RestAt rs′ q
  lift-rest rw {rs′} {q} {q₀} {c₀} {ws} cur′ sc₀ iq₀ ks h = (p ⊕ [ last ]) ∷ fan c₀ ++ fans ks , pick-row
    where
      open Fan rw
      pick-row : ∀ {y e} → T′ y e → After (cursor nothing rs′) y → rootOf y ≡ rootOf q → y ∈ (p ⊕ [ last ]) ∷ fan c₀ ++ fans ks
      pick-row r a iq with under r
      ... | inj₂ (inj₁ refl) = here refl
      ... | inj₂ (inj₂ (xs , refl)) =
        ⊥-elim (≺-irrefl {body b ⊕ xs} (≺-trans {body b ⊕ xs} {c₀ ⊕ ws} {body b ⊕ xs}
          (≺-≼-≺ {body b ⊕ xs} {c₀} {c₀ ⊕ ws}
            (≺-trans {body b ⊕ xs} {s₀ b} {c₀} (body-before xs) (world-after (InvAt.world IS sc₀) (InvAt.real IS sc₀)))
            (⊑-≼ {c₀} {c₀ ⊕ ws} (ws , refl)))
          (subst (λ c → After c (body b ⊕ xs)) cur′ a)))
      ... | inj₁ (y₁ , e₁′ , (zs , refl) , s₁) with c₀ <ᵖ y₁ in e
      ...   | true = there (∈-++⁺ʳ (fan c₀) (fans-in k∈ (proj₂ (read-fan b p rw y₁) r s₁ (zs , refl))))
        where
          k∈ : y₁ ∈ ks
          k∈ = h s₁ (to≺ c₀ y₁ e) (trans (sym (rootOf-ext y₁ zs)) (trans iq (sym iq₀)))
      ...   | false with ≼-split {y₁} {c₀} (λ h′ → subst T e h′)
      ...     | inj₂ refl = there (∈-++⁺ˡ (proj₂ (read-fan b p rw c₀) r s₁ (zs , refl)))
      ...     | inj₁ lt   = ⊥-elim (≺-irrefl {y₁ ⊕ zs} (≺-trans {y₁ ⊕ zs} {c₀ ⊕ ws} {y₁ ⊕ zs} below a′))
        where
          a′ : (c₀ ⊕ ws) ≺ (y₁ ⊕ zs)
          a′ = subst (λ c → After c (y₁ ⊕ zs)) cur′ a
          below : (y₁ ⊕ zs) ≺ (c₀ ⊕ ws)
          below = ≺-≼-≺ {y₁ ⊕ zs} {c₀} {c₀ ⊕ ws} (past zs s₁ sc₀ lt) (⊑-≼ {c₀} {c₀ ⊕ ws} (ws , refl))

  -- A run read past the joins: the source's count is the reader's, and
  -- holds nothing with a begin of the instant met.
  rest-read : ∀ {pre y₀ e₀ rs js rs₁′} → Met T′ (js ++ rs₁′) → proj₂ (cnt (js ++ rs₁′)) ≡ 0
            → ∀ {q} → (q , out (instEmit (mark begin) (proj₁ (cnt (js ++ rs₁′))))) ∈ js ++ rs₁′
            → Met (Src b) (pre ++ (y₀ , e₀) ∷ rs) → L.map proj₂ js ≡ L.map out (jl (cnt pre) e₀)
            → RowsAt Rl rs₁′ ((y₀ , e₀) ∷ rs) → RestAt (js ++ rs₁′) q
  rest-read {pre} {y₀} {e₀} {rs} {js} {rs₁′} m z {q} bq run jeq ra =
    sim-case (Past.sim-split Rl (Src b) {pre} jeq {r₂ = []} (sym (++-identityʳ ((y₀ , e₀) ∷ rs))) ra (λ ()))
    where
      S : List (Pos × Ev (IE X))
      S = pre ++ (y₀ , e₀) ∷ rs

      Cur : Set
      Cur = Σ Pos λ c′ → Σ Pos λ c → cursor nothing (js ++ rs₁′) ≡ just c′ × cursor nothing S ≡ just c × Rl c′ c
            × Σ (Ev (IE X)) λ e₁ → (c , e₁) ∈ (y₀ , e₀) ∷ rs

      SrcRest : Pos → Set
      SrcRest q₀ = Σ (List Pos) λ ks → ∀ {y e} → Src b y e → After (cursor nothing S) y → rootOf y ≡ rootOf q₀ → y ∈ ks

      from-cur : ∀ {q₀} → rootOf q₀ ≡ rootOf q → SrcRest q₀ → Cur → RestAt (js ++ rs₁′) q
      from-cur {q₀} iq₀ (ks , h) (c′ , c₀ , ec′ , ec₀ , (ws , refl) , e₁ , i₁) =
        lift-rest (proj₁ (run-row m bq)) {rs′ = js ++ rs₁′} {q = q} {q₀ = q₀} {c₀ = c₀} {ws = ws} ec′ (proj₁ (run-row run (∈-++⁺ʳ pre i₁))) iq₀ ks
          (λ {y} {e} s a r → h {y} {e} s (subst (λ c → After c y) (sym ec₀) a) r)

      Begun : Set
      Begun = Σ Pos λ q₀ → (q₀ , out (instEmit (mark begin) (proj₁ (cnt S)))) ∈ S × rootOf q₀ ≡ rootOf q

      from-begin : proj₂ (cnt S) ≡ 0 → Begun → RestAt (js ++ rs₁′) q
      from-begin z₀ (q₀ , bq₀ , iq₀) = from-cur {q₀} iq₀ (Held.rest HS run z₀ bq₀) (cur-run js pre ra)

      sim-case : Sim (cnt (js ++ rs₁′)) (cnt S) (values (js ++ rs₁′)) → RestAt (js ++ rs₁′) q
      sim-case (inj₁ ceq)          = from-begin (trans (sym (cong proj₂ ceq)) z) (J.src-begin run jeq ra m (λ i → i) bq (cong proj₁ ceq))
      sim-case (inj₂ (_ , _ , nb)) = ⊥-elim (lookup nb (out-in bq) is-begin)

  -- A RUN HOLDING THE READER'S END has its cursor there, and nothing follows.
  end-cursor : ∀ {c rs q′} → Run T′ c rs → (q′ , end) ∈ rs → cursor c rs ≡ just q′
  end-cursor ((((x , _) , _) , _) ∷ run) (here refl) with run-past-end x run
  ... | refl = refl
  end-cursor (_ ∷ run) (there i) = end-cursor run i

  rest-end : ∀ {rs′ q′} → Met T′ rs′ → (q′ , end) ∈ rs′ → ∀ q → RestAt rs′ q
  rest-end {rs′} {q′} m ei q = [] , λ {y} r a _ → ⊥-elim (after r (subst (λ c → After c y) (end-cursor m ei) a))
    where
      after : ∀ {y e} → T′ y e → q′ ≺ y → ⊥
      after r lt with InvAt.quiet IT (proj₁ (run-row m ei)) r lt
      ... | _ , refl , _ = t-nopin r

  -- PAST A ZERO COUNT THE READER FINISHES THE INSTANT, as its source does.
  rest : Rest T′
  rest {rs′} m z {q} bq with read-back b p ng m
  ... | inj₂ ((_ , ei) , _) = rest-end m ei q
  ... | inj₁ (j-late h) = ⊥-elim (out-end (proj₁ (h bq)))
    where out-end : ∀ {x : IE X} → out x ≡ end → ⊥
          out-end ()
  ... | inj₁ (j-part h) = ⊥-elim (zero-suc (trans (sym z) (proj₂ (begins-held h bq))))
  ... | inj₁ (j-read run jeq ra) = rest-read m z bq run jeq ra

  ----------------------------------------------------------------------
  -- Idle

  Goal : List (Pos × Ev (IE X)) → Pos → Set
  Goal rs w = proj₂ (cnt rs) ≡ 0 ⊎ proj₁ (cnt rs) ≡ nameOf w

  -- A visible row of the source has few rows before it, and lies before every end.
  few-vis : ∀ {k e} → Src b k e → Visible e → Few (Src b) k
  few-vis {k} {out x} sk _ = entered-few (ev (Bound.m b) (Bound.src b) (Bound.env b)) (s₀ b) (λ {k′} {e′} → full {q = k} {e = out x} tt {k′} {e′}) sk
  few-vis {k} {end}   sk _ = entered-few (ev (Bound.m b) (Bound.src b) (Bound.env b)) (s₀ b) (λ {k′} {e′} → full {q = k} {e = end} tt {k′} {e′}) sk

  live : ∀ {k e} → Src b k e → Visible e → ∀ {c} → Src b c end → k ≼ c
  live sk v sc ck = pinby-vis v (InvAt.quiet IS sc sk ck)

  shS : Shows (Src b)
  shS = shows-ev (Bound.m b) (Bound.src b) (Bound.env b) (Bound.good b) (s₀ b)
          (ok-step (Bound.at b ⊕ [ ix 1 ]) (ok-step (Bound.at b) (Bound.ok b)))

  -- PAST THE JOINS THE READER IDLES WHERE ITS SOURCE DOES: a position
  -- below a source row past the cursor takes that row's route; one below
  -- none has few source rows before it, each shown below itself, and is
  -- past none of the source's rows the reader is not past.
  module IdleRead {pre y₀ e₀ rs js rs₁′} (run : Met (Src b) (pre ++ (y₀ , e₀) ∷ rs)) (ra : RowsAt Rl rs₁′ ((y₀ , e₀) ∷ rs))
                  (m : Met T′ (js ++ rs₁′)) (ne′ : ∀ {c} → (c , end) ∈ js ++ rs₁′ → ⊥) {w} (F : Few T′ w)
                  (aw : After (cursor nothing (js ++ rs₁′)) w)
                  (lw : ∀ {y e} → T′ y e → Visible e → After (cursor nothing (js ++ rs₁′)) y → w ≼ y) where

    S : List (Pos × Ev (IE X))
    S = pre ++ (y₀ , e₀) ∷ rs

    ne : ∀ {c} → (c , end) ∈ S → ⊥
    ne i = [ pre-noend pre (run-prefix (pre ++ [ (y₀ , e₀) ]) (subst (Met (Src b)) (sym (++-assoc pre [ (y₀ , e₀) ] rs)) run))
           , (λ j → ne′ (∈-++⁺ʳ js (proj₁ (proj₂ (endAt ra j))))) ]′ (∈-++⁻ pre i)

    I : Idle (Src b)
    I = Held.idle HS

    module At {c ws e₁} (ec′ : cursor nothing (js ++ rs₁′) ≡ just (c ⊕ ws)) (ec : cursor nothing S ≡ just c)
              (i₁ : (c , e₁) ∈ (y₀ , e₀) ∷ rs) where

      sc : Src b c e₁
      sc = proj₁ (run-row run (∈-++⁺ʳ pre i₁))

      vc : Visible e₁
      vc = proj₂ (run-row run (∈-++⁺ʳ pre i₁))

      -- The reader's row at its cursor.
      rc-of : nothing ≡ just (c ⊕ ws) ⊎ Σ (Ev (IE X)) (λ e → (c ⊕ ws , e) ∈ js ++ rs₁′) → Σ (Ev (IE X)) λ e → T′ (c ⊕ ws) e
      rc-of (inj₁ ())
      rc-of (inj₂ (e , i)) = e , proj₁ (run-row m i)

      rc : Σ (Ev (IE X)) λ e → T′ (c ⊕ ws) e
      rc = rc-of (cursor-in nothing (js ++ rs₁′) ec′)

      a-of : ∀ {y} → c ≺ y → After (cursor nothing S) y
      a-of {y} cy = subst (λ x → After x y) (sym ec) cy

      c-of : ∀ {y} → After (cursor nothing S) y → c ≺ y
      c-of {y} a = subst (λ x → After x y) ec a

      cw : c ≺ w
      cw = below-≺ c ws (subst (λ x → After x w) ec′ aw)

      -- Past the cursor, a source row and every row below it are past the reader's.
      aft : ∀ {k e} zs → Src b k e → c ≺ k → After (cursor nothing (js ++ rs₁′)) (k ⊕ zs)
      aft {k} zs sk ck = subst (λ x → After x (k ⊕ zs)) (sym ec′)
        (≺-≼-≺ {c ⊕ ws} {k} {k ⊕ zs} (past ws sc sk ck) (⊑-≼ {k} {k ⊕ zs} (zs , refl)))

      Shown : Pos → Ev (IE X) → Set
      Shown k e = Σ Path λ zs → Σ (Ev (IE X)) λ e′ → T′ (k ⊕ zs) e′ × (Visible e → Visible e′) × After (cursor nothing (js ++ rs₁′)) (k ⊕ zs)

      shown : ∀ {k e} → Src b k e → c ≺ k → Few (Src b) k → (∀ {c₁} → Src b c₁ end → k ≼ c₁)
            → (Silent e → ∀ {y} → Rl y k → Few T′ y) → Nl.¬ Nl.¬ (Shown k e)
      shown {k} {e} sk ck fk lv fz h = read-shows b p ng (proj₂ rc) (past ws sc sk ck) sk fk lv fz λ x → h (with-aft x)
        where
          with-aft : Σ Path (λ zs → Σ (Ev (IE X)) λ e′ → T′ (k ⊕ zs) e′ × (Visible e → Visible e′)) → Shown k e
          with-aft (zs , e′ , r , v) = zs , e′ , r , v , aft zs sk ck

      Beneath : Set
      Beneath = Σ Pos λ y → Σ (Ev (IE X)) λ e → Src b y e × Visible e × c ≺ y × Σ Label λ l → Σ Path λ zs → w ≡ y ⊕ (l ∷ zs)

      -- Below a source row past the cursor: that row's route.
      beneath : Beneath → Goal S w
      beneath (y , e , sy , vy , cy , l , zs , eq) =
        [ inj₁ , (λ nq → inj₂ (trans nq (sym (trans (cong nameOf eq) (name-ext y (l ∷ zs)))))) ]′ (I run ne (few-vis sy vy) (a-of cy) least)
        where
          least : ∀ {y₂ e₂} → Src b y₂ e₂ → Visible e₂ → After (cursor nothing S) y₂ → y ≼ y₂
          least {y₂} {e₂} s₂ v₂ a₂ lt = shown s₂ (c-of a₂) (few-vis s₂ v₂) (live s₂ v₂) (λ sl → ⊥-elim (loud v₂ sl)) blocked
            where
              blocked : Shown y₂ e₂ → ⊥
              blocked (zs₂ , e′ , r , vv , a) =
                lw r (vv v₂) a (subst ((y₂ ⊕ zs₂) ≺_) (sym eq) (≺-trans {y₂ ⊕ zs₂} {y} {y ⊕ (l ∷ zs)} (past zs₂ s₂ sy lt) (≺-ext y zs)))

      -- Below no source row past the cursor: the source's own route.
      clear : (Beneath → ⊥) → Few (Src b) w → Goal S w
      clear nu fw = I run ne fw (a-of cw) not-past
        where
          not-past : ∀ {y e} → Src b y e → Visible e → After (cursor nothing S) y → w ≼ y
          not-past {y} {e} sy vy ay yw = em {Σ Path λ ys → w ≡ y ⊕ ys} λ
            { (inj₁ ([] , eq))     → ≺-irrefl {y} (subst (y ≺_) (trans eq (⊕-identityʳ y)) yw)
            ; (inj₁ (l ∷ zs , eq)) → nu (y , e , sy , vy , c-of ay , l , zs , eq)
            ; (inj₂ np)            → shown sy (c-of ay) (few-vis sy vy) (live sy vy) (λ sl → ⊥-elim (loud vy sl)) (blocked np) }
            where
              blocked : (Σ Path (λ ys → w ≡ y ⊕ ys) → ⊥) → Shown y e → ⊥
              blocked np (zs , e′ , r , vv , a) =
                lw r (vv vy) a (to≺ (y ⊕ zs) w (<ᵖ-apart y w zs (from≺ y w yw) λ ys eq → np (ys , eq)))

      fc : Few (Src b) c
      fc = few-vis sc vc

      ls : List Pos
      ls = c ∷ proj₁ fc ++ cover w (proj₁ F)

      -- A row past the cursor and before the position lies before every end:
      -- an end past the cursor is shown, and the position lies below it.
      live-past : ∀ {k e} → Src b k e → c ≺ k → k ≺ w → ∀ {c₁} → Src b c₁ end → k ≼ c₁
      live-past {k} {e} sk ck kw {c₁} se c₁k = [ before , after ]′ (≼-or-≻ c₁ c)
        where
          before : c₁ ≼ c → ⊥
          before c₁c =
            [ (λ lt → pinby-vis vc (InvAt.quiet IS se sc lt))
            , (λ eq → ne (∈-++⁺ʳ pre (subst (λ e′ → (c , e′) ∈ (y₀ , e₀) ∷ rs)
                                       (InvAt.func IS sc (subst (λ z → Src b z end) eq se)) i₁))) ]′ (≼-split {c₁} {c} c₁c)

          flat-k : Σ Path (λ zs′ → k ≡ c₁ ⊕ zs′) → ⊥
          flat-k ([] , eq)      = ≺-irrefl {c₁} (subst (c₁ ≺_) (trans eq (⊕-identityʳ c₁)) c₁k)
          flat-k (l ∷ zs′ , eq) = InvAt.flat IS se (subst (λ z → Src b z e) eq sk)

          blocked : Shown c₁ end → ⊥
          blocked (zs , e′ , r , vv , a) = em {Σ Path λ ys → w ≡ c₁ ⊕ ys} λ
            { (inj₁ (ys , eq)) → flat-k (<ᵖ-between c₁ k ys (from≺ c₁ k c₁k) (from≺ k (c₁ ⊕ ys) (subst (k ≺_) eq kw)))
            ; (inj₂ np) → lw r (vv tt) a (to≺ (c₁ ⊕ zs) w (<ᵖ-apart c₁ w zs (from≺ c₁ w (≺-trans {c₁} {k} {w} c₁k kw)) λ ys eq → np (ys , eq))) }

          after : c ≺ c₁ → ⊥
          after cc₁ = shown se cc₁ (few-vis se tt) (live se tt) (λ ()) blocked

      -- A source row with few rows before it, before the position, is listed:
      -- at or before the cursor, or shown, below a row of the reader's or above the position.
      listed : ∀ {k e} → Src b k e → Few (Src b) k → k ≺ w → k ∈ ls
      listed {k} {e} sk fk kw = decidable-stable (any? (k ≟ᵖ_) ls) λ nin →
        [ (λ kc → [ (λ lt → nin (there (∈-++⁺ˡ (proj₂ fc sk lt)))) , (λ eq → nin (here eq)) ]′ (≼-split {k} {c} kc))
        , past-c nin ]′ (≼-or-≻ k c)
        where
          past-c : (k ∈ ls → ⊥) → c ≺ k → ⊥
          past-c nin ck = em {Σ Path λ ys → w ≡ k ⊕ ys} λ
            { (inj₁ (ys , eq)) → nin (there (∈-++⁺ʳ (proj₁ fc) (cov-∈ {w} {proj₁ F} (inj₁ (ys , eq)))))
            ; (inj₂ np)        → shown sk ck fk (live-past sk ck kw) (λ _ → few-below np) (into np) }
            where
              -- Below `k`, before the position: the reader has few rows there.
              few-below : (Σ Path (λ ys → w ≡ k ⊕ ys) → ⊥) → ∀ {y} → Rl y k → Few T′ y
              few-below np (zs , refl) = few-down F (≺→≼ {k ⊕ zs} {w} (to≺ (k ⊕ zs) w (<ᵖ-apart k w zs (from≺ k w kw) λ ys eq → np (ys , eq))))

              into : (Σ Path (λ ys → w ≡ k ⊕ ys) → ⊥) → Shown k e → ⊥
              into np (zs , e′ , r , _ , _) =
                nin (there (∈-++⁺ʳ (proj₁ fc) (cov-∈ {w} {proj₁ F} (inj₂ (any-map (λ eq → subst (k ⊑_) eq (zs , refl))
                  (proj₂ F r (to≺ (k ⊕ zs) w (<ᵖ-apart k w zs (from≺ k w kw) λ ys eq → np (ys , eq)))))))))

      goal : Goal S w
      goal = decidable-stable ((proj₂ (cnt S) ≟ 0) ⊎-dec (proj₁ (cnt S) ≟ᵖ nameOf w)) λ ng → em {Beneath} λ
        { (inj₁ u)  → ng (beneath u)
        ; (inj₂ nu) → shS (ls , listed) λ fw → ng (clear nu fw) }

    goal : Goal S w
    goal = at (cur-run js pre ra)
      where
        at : Σ Pos (λ c′ → Σ Pos λ c → cursor nothing (js ++ rs₁′) ≡ just c′ × cursor nothing S ≡ just c × Rl c′ c
                    × Σ (Ev (IE X)) λ e₁ → (c , e₁) ∈ (y₀ , e₀) ∷ rs) → Goal S w
        at (_ , c , ec′ , ec , (ws , refl) , e₁ , i₁) = At.goal {c} {ws} {e₁} ec′ ec i₁

  -- PAST THE JOINS, the source's route; holding nothing, a count of none.
  read-goal : ∀ {rs′ pre y₀ e₀ rs js rs₁′ w} → rs′ ≡ js ++ rs₁′ → Met (Src b) (pre ++ (y₀ , e₀) ∷ rs)
            → L.map proj₂ js ≡ L.map out (jl (cnt pre) e₀) → RowsAt Rl rs₁′ ((y₀ , e₀) ∷ rs)
            → Met T′ rs′ → (∀ {c} → (c , end) ∈ rs′ → ⊥) → Few T′ w → After (cursor nothing rs′) w
            → (∀ {y e} → T′ y e → Visible e → After (cursor nothing rs′) y → w ≼ y) → Goal rs′ w
  read-goal {pre = pre} {y₀} {e₀} {rs} {js} {rs₁′} {w} refl run jeq ra m ne′ F aw lw =
    sim-case (Past.sim-split Rl (Src b) {pre} jeq {r₂ = []} (sym (++-identityʳ _)) ra (λ ()))
    where
      sim-case : Sim (cnt (js ++ rs₁′)) (cnt (pre ++ (y₀ , e₀) ∷ rs)) (values (js ++ rs₁′)) → Goal (js ++ rs₁′) w
      sim-case (inj₁ ceq)         = subst (λ r → proj₂ r ≡ 0 ⊎ proj₁ r ≡ nameOf w) (sym ceq) (IdleRead.goal run ra m ne′ F aw lw)
      sim-case (inj₂ (z , _ , _)) = inj₁ z

  -- A run of joins alone names the source's route at the row they join,
  -- which the source's idle names: the position lies below that row.
  name-of : ∀ (ys : List (Pos × Ev (IE X))) q {e} x n → e ≡ out x → x ≡ instEmit (mark begin) n → proj₁ (cnt (ys ++ [ (q , e) ])) ≡ n
  name-of ys q _ n refl refl = trans (cong proj₁ (cnt-++ ys [ (q , out (instEmit (mark begin) n)) ])) (begin-name {A = X} (cnt ys) n)

  part-goal : ∀ {rs′ ys q e w} → rs′ ≡ ys ++ [ (q , e) ] → Met T′ rs′ → Begins rs′ → (∀ {c} → (c , end) ∈ rs′ → ⊥) → Few T′ w
            → After (cursor nothing rs′) w → (∀ {y e′} → T′ y e′ → Visible e′ → After (cursor nothing rs′) y → w ≼ y) → Goal rs′ w
  part-goal {rs′} {ys} {q} {e} {w} eq m bs ne′ F aw lw = [ from-part , from-further ]′ (read-part b p ng m bs qi)
    where
      qi : (q , e) ∈ rs′
      qi = subst ((q , e) ∈_) (sym eq) (∈-++⁺ʳ ys (here refl))

      from-further : Further b rs′ → Goal rs′ w
      from-further (further eq′ run jeq ra) = read-goal eq′ run jeq ra m ne′ F aw lw

      from-part : Part b p rs′ → Goal rs′ w
      from-part (sc₁ , w₁ , e₁ , S₀ , js , mS , jeq , pr , rl , u , e′ , ru , vu , au , rlu) =
        [ (λ z → ⊥-elim (zero-suc (trans (sym z) (proj₂ (proj₂ ji)))))
        , (λ nq → inj₂ (trans nm (trans nq (sym nw)))) ]′
          (Held.idle HS (run-prefix sc₁ mS) ne₁ (proj₁ hd) (proj₁ (proj₂ hd)) (proj₂ (proj₂ hd)))
        where
          hd = run-head (run-tail sc₁ mS)

          ne₁ : ∀ {c} → (c , end) ∈ sc₁ → ⊥
          ne₁ = pre-noend sc₁ (run-prefix (sc₁ ++ [ (w₁ , e₁) ]) (subst (Met (Src b)) (sym (++-assoc sc₁ [ (w₁ , e₁) ] S₀)) mS))

          mo = mem-of jeq (pre-∈ pr qi)
          ji = jl-in (cnt sc₁) e₁ (proj₂ (proj₂ mo))

          nm : proj₁ (cnt rs′) ≡ proj₁ (cnt sc₁)
          nm = subst (λ r → proj₁ (cnt r) ≡ proj₁ (cnt sc₁)) (sym eq) (name-of ys q (proj₁ mo) (proj₁ (cnt sc₁)) (proj₁ (proj₂ mo)) (proj₁ ji))

          rq = rl qi
          sw = sandwich w₁ (proj₁ rq) (proj₁ rlu)
                 (subst (_≺ w) (proj₂ rq) (subst (λ x → After x w) (trans (cong (cursor nothing) eq) (cursor-snoc nothing ys)) aw))
                 (subst (w ≼_) (proj₂ rlu) (lw ru vu au))

          nw : nameOf w ≡ nameOf w₁
          nw = trans (cong nameOf (proj₂ sw)) (name-ext w₁ (proj₁ sw))

  part-any : ∀ {rs′ w} → (rs′ ≡ [] ⊎ Σ _ λ ys → Σ _ λ y → rs′ ≡ ys ++ [ y ]) → Met T′ rs′ → Begins rs′ → (∀ {c} → (c , end) ∈ rs′ → ⊥)
           → Few T′ w → After (cursor nothing rs′) w → (∀ {y e} → T′ y e → Visible e → After (cursor nothing rs′) y → w ≼ y) → Goal rs′ w
  part-any {w = w} (inj₁ eq)                  _ _ _   _ _  _  = subst (λ r → Goal r w) (sym eq) (inj₁ refl)
  part-any         (inj₂ (ys , (q , e) , eq)) m h ne′ F aw lw = part-goal eq m h ne′ F aw lw

  late-goal : ∀ {rs′ w} → (∀ {y e} → (y , e) ∈ rs′ → e ≡ end × Ex (p ∷ cs) y) → (∀ {c} → (c , end) ∈ rs′ → ⊥) → Goal rs′ w
  late-goal {[]}           _ _  = inj₁ refl
  late-goal {(y , e) ∷ _} h ne′ = ⊥-elim (ne′ (here (cong (y ,_) (sym (proj₁ (h (here refl)))))))

  -- THE READER IDLES AS ITS SOURCE DOES: past its joins on the source's
  -- route, and on joins alone on the route the source idles at the row
  -- they join.
  idle : Idle T′
  idle {rs′} m ne′ {w} F aw lw with read-back b p ng m
  ... | inj₂ ((_ , ei) , _)     = ⊥-elim (ne′ ei)
  ... | inj₁ (j-late h)          = late-goal {rs′} {w} h ne′
  ... | inj₁ (j-part h)          = part-any (snoc-view rs′) m h ne′ F aw lw
  ... | inj₁ (j-read run jeq ra) = read-goal refl run jeq ra m ne′ F aw lw

  held : Held T′ (p ∷ cs)
  held = record
    { named   = named
    ; covered = J.covered′
    ; exact   = J.exact′
    ; routing = routing
    ; shut    = J.shut′
    ; early   = early
    ; ends    = ends
    ; done    = done
    ; late    = late
    ; idle    = idle
    ; rest    = rest }
    where
      routing : ∀ {y m n} → T′ y (out (instEmit (mark m) n)) → Routing m
      routing x with read-row b p x
      ... | inj₁ (_ , _ , _ , s , same-mark _) = Held.routing HS s
      ... | inj₂ (refl , _) = r-begin
      early : ∀ {y a n} → T′ y (out (instEmit (value a) n)) → Early y
      early x with read-row b p x
      ... | inj₁ (_ , _ , (zs , refl) , s , same-value) = early-inst zs (Held.early HS s)
      ... | inj₂ (() , _)
      done : ∀ {y n} → T′ y (out (instEmit (mark completed) n)) → Early y
      done x with read-row b p x
      ... | inj₁ (_ , _ , (zs , refl) , s , same-mark _) = early-inst zs (Held.done HS s)
      ... | inj₂ (() , _)
      late : ∀ {y n} → T′ y (out (instEmit (mark over) n)) → Valued (rootOf y) × opos (rootOf y) ⊑ y
      late x with read-row b p x
      ... | inj₁ (y₀ , _ , (zs , refl) , s , same-mark _) =
        let (v , o) = Held.late HS s
        in subst (λ r → Valued r × opos r ⊑ (y₀ ⊕ zs)) (sym (rootOf-ext y₀ zs)) (v , ⊑-trans o (zs , refl))
      ... | inj₂ (() , _)

-- A READER'S ROWS A LANE CAN HANG ON ARE ADMISSIBLE: each lies below a
-- binder's row a lane can hang on, outside every binder's last gap.
postulate
  placed-connected : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (i : A ∈ Γ) (env : DenEnv Δ) cs → GoodEnv env
                   → (eh : EnvHeld ρ env cs) → PlacedD (Hots env) (Fresh eh) (ev m (elab ρ (connected i)) env)

held-connected : ∀ m {Γ Δ A} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (i : A ∈ Γ) → IH m ρ (connected i)
held-connected nothing  ρ i = ih (λ env cs g eh p ok fr ep → Reader.held (EnvHeld.bound eh i) p (apart-at (proj₁ fr) i) ep
                                 (ok-mono (hots-one env (ρ (∈-map⁺ AIE i))) ok)) (placed-connected nothing ρ i)
held-connected (just n) ρ i = ih (λ env cs g eh p ok fr ep → Reader.held (EnvHeld.bound eh i) p (apart-at (proj₁ fr) i) ep
                                 (ok-mono (hots-one env (ρ (∈-map⁺ AIE i))) ok)) (placed-connected (just n) ρ i)
