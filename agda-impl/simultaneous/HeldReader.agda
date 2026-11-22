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
open import simultaneous.HeldRead using (Under; under-ext; JS; Fl; lane-in; Rl-trans)
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
open import simultaneous.HeldRead using (RD; Rl; Src; Under; body; held-src; read-back; read-end; read-fan; read-idle; read-row; s₀; z₀)
open import simultaneous.HeldRead using (ann-under; rd-mg)
open import denotation.Events using (Timeline; fresh)
open import denotation.Position using (_≟ᵖ_; root)
open import simultaneous.SObs using (lone; module Elaborate)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; Routes; count; reader; annotate; annStep; joinStep; concatˢ; elab)

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

module Reader {X} {d : Den (AIE X)} {cs} (b : Bound d cs) (p : Pos) (ng : Nl.¬ Gap b p) (ep : Early p) where

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

  module J = Join Rl rt exR named (read-back b p ng) HS

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

  fan : Pos → List Pos
  fan y₀ = proj₁ (read-fan b p y₀)

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
  lift-rest : ∀ {rs′ q q₀ c₀ ws e₁} → cursor nothing rs′ ≡ just (c₀ ⊕ ws) → Src b c₀ e₁ → rootOf q₀ ≡ rootOf q
            → (ks : List Pos) → (∀ {y e} → Src b y e → c₀ ≺ y → rootOf y ≡ rootOf q₀ → y ∈ ks)
            → RestAt rs′ q
  lift-rest {rs′} {q} {q₀} {c₀} {ws} cur′ sc₀ iq₀ ks h = (p ⊕ [ last ]) ∷ fan c₀ ++ fans ks , pick-row
    where
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
      ...   | true = there (∈-++⁺ʳ (fan c₀) (fans-in k∈ (proj₂ (read-fan b p y₁) r s₁ (zs , refl))))
        where
          k∈ : y₁ ∈ ks
          k∈ = h s₁ (to≺ c₀ y₁ e) (trans (sym (rootOf-ext y₁ zs)) (trans iq (sym iq₀)))
      ...   | false with ≼-split {y₁} {c₀} (λ h′ → subst T e h′)
      ...     | inj₂ refl = there (∈-++⁺ˡ (proj₂ (read-fan b p c₀) r s₁ (zs , refl)))
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
        lift-rest {rs′ = js ++ rs₁′} {q = q} {q₀ = q₀} {c₀ = c₀} {ws = ws} ec′ (proj₁ (run-row run (∈-++⁺ʳ pre i₁))) iq₀ ks
          (λ {y} {e} s a r → h {y} {e} s (subst (λ c → After c y) (sym ec₀) a) r)

      Begun : Set
      Begun = Σ Pos λ q₀ → (q₀ , out (instEmit (mark begin) (proj₁ (cnt S)))) ∈ S × rootOf q₀ ≡ rootOf q

      from-begin : proj₂ (cnt S) ≡ 0 → Begun → RestAt (js ++ rs₁′) q
      from-begin z₀ (q₀ , bq₀ , iq₀) = from-cur {q₀} iq₀ (Held.rest HS run z₀ bq₀) (cur-run js pre ra)

      sim-case : Sim (cnt (js ++ rs₁′)) (cnt S) (values (js ++ rs₁′)) → RestAt (js ++ rs₁′) q
      sim-case (inj₁ ceq)          = from-begin (trans (sym (cong proj₂ ceq)) z) (J.src-begin run jeq ra m (λ i → i) bq (cong proj₁ ceq))
      sim-case (inj₂ (_ , _ , nb)) = ⊥-elim (lookup nb (out-in bq) is-begin)

  -- PAST A ZERO COUNT THE READER FINISHES THE INSTANT, as its source does.
  rest : Rest T′
  rest {rs′} m z {q} bq with read-back b p ng m
  ... | j-late h = ⊥-elim (out-end (proj₁ (h bq)))
    where out-end : ∀ {x : IE X} → out x ≡ end → ⊥
          out-end ()
  ... | j-part h = ⊥-elim (zero-suc (trans (sym z) (proj₂ (begins-held h bq))))
  ... | j-read run jeq ra = rest-read m z bq run jeq ra

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
    ; idle    = read-idle b p ng
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
held-connected nothing  ρ i = ih (λ env cs g eh p ok fr ep → Reader.held (EnvHeld.bound eh i) p (apart-at fr i) ep) (placed-connected nothing ρ i)
held-connected (just n) ρ i = ih (λ env cs g eh p ok fr ep → Reader.held (EnvHeld.bound eh i) p (apart-at fr i) ep) (placed-connected (just n) ρ i)
