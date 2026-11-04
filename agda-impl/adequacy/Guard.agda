{-# OPTIONS --guardedness #-}

-- A GUARD ROW, LIFTED: a row a step leaves at the first child of where it
-- begins work, carried up through the frames above it to a row of the
-- root's entry under that first child, at or before the row met next.
module adequacy.Guard where

open import Data.Bool using (T)
open import Data.Bool.Properties using (T-≡)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; [_]; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-map⁺)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function using (Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import denotation.Events using (Pos; ix; <ᵖ-split; <ᵖ-between)
open import denotation.EmissionSet using (EmissionSet; Ev; _≺_; _≼_; Truncate)
open import denotation.Read using (Visible)
open import denotation.Laws.Modulus using (≼-false; ≼-or-≻; ≼-refl)
open import denotation.Laws.BoundedInv using (first-child)
open import adequacy.Weight using (prefixes)
open import adequacy.Cursor using (Cur; bef; Behind; _≈_; alike; voc; NoFail; Rgn; Sound; Lane; Runs; Start; Kill; kill-out; polF; JoinF; LaneRg; LanesIn; JRl; JInv; joined; h-live; h-end; h-kill; Ze; e₀; e+)
open import adequacy.Cursor.Frame using (Need; owes; dead; lane; lanecut; pnd; Fr; f-top; f-map; f-scan; f-cut; f-take; f-took; f-outer; f-lanes; f-lane; f-lnct; f-src; f-srcc; f-srcp; f-body; d-map; d-scan; d-cut; d-ln; d-take; d-outer; d-lanes; d-src; d-body; f-isle; f-islec; f-islep)
open import adequacy.Rows using (module _≃_)
open _≃_ using (from)
open import operation.PureObservable using (module Machine)
open Machine using (Ctx; Scope; scopeOf)
open import Tree using (Obs; mergeᶠ; switchᶠ; exhaustᶠ)
open import Data.Maybe using (just; nothing)
open import Data.List.Properties using (∷ʳ-injectiveʳ)
open import denotation.Events using (Timeline)
open import denotation.EmissionSet using (Den; ⟦_⟧; Work; module Joining; module Merge; module Bounded; module Switch; module Exhaust)
open import denotation.Laws.Worlds using (here; step; ⊑-trans; ⊑-snoc⁺)
open import adequacy.Rows using (full)
open import denotation.Laws.Worlds using (Hots)
open import adequacy.Enter using (module Lanes; w-down)
open import adequacy.Regions using (lane-sole)
open import denotation.EmissionSet using (out; skip; end; MapT; map-out; map-skip; map-pin; map-end; module Scan; module TakeWhile)
open import denotation.Laws.Modulus using (≺-ext; ≺-trans)
open import Relation.Nullary using (¬_)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import denotation.Events using (last; root)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)
open import denotation.EmissionSet using (enter)
open import denotation.Read using (Meets) renaming (cursor to cursorᴿ)
open import operation.PureObservable using (PureObs)
open Machine using (⟨_,_,_,_⟩; rising; nx; cp; St; load; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody)
open import adequacy.Rows using (conv; back)
open import adequacy.Simulated using (cursor)
open import adequacy.Simulation using (Simulation; module Along)
open import adequacy.Path using (Path)
open import adequacy.Cursor using (Due)
open import adequacy.Cursor.Frame using (Fly)
open import adequacy.Cursor.Rise using (flying; adrift)
open import adequacy.Walk using (dead-closed)
open import Data.List using (map)
open import denotation.EmissionSet using (Reach; Dep; module Connecting)
open import adequacy.Cursor using (Src; src-pend; src-on; src-shut; Parts)
open import adequacy.Rows using (Frozen)
open Machine using (CS) renaming (Ev to Evᴹ)
open import adequacy.Bound using (behind-pend; lo-p)
open import adequacy.Floor.Keys using (lo-weaken; at-after)
open import adequacy.FrameBound using (fb-u)
open import Data.Bool using (not)
open import Data.List using (_ʳ++_)
open import Relation.Binary.PropositionalEquality using (trans)
open import denotation.Events using (inside)
open import denotation.EmissionSet using (pin; Unpinned)
open import adequacy.Cursor using (vis)
open import adequacy.Rows using (toEv)
open import denotation.Laws.Worlds using (⊑-inside; inside-⊑; ⊑-≼)
open import denotation.Laws.Modulus using (≼-≺-≺; ≺-≼-≺)
open import adequacy.Cursor using (notT; SubdAt; Flags; module Flags)
open import adequacy.Cursor.Frame using (Unread)
open import operation.Key using (at; after; _<ᴷ_; <ᴷ-trans; after-lt)
open import adequacy.Floor.Keys using (plug-in; own-bld; oo; at-after₀)
open import adequacy.Least using (Lo; k-own)
open import adequacy.Apart.Floor using (floor)
open Machine using (plug; mapS; scanS; cutS; lnS; takeS; flatS; connS)
open Machine using (binds; free)
open import adequacy.Cursor using (Husk; Burst; Subd; AttOwed; _⊑_; _∪ᵖ_; Up; InCall; Bursts; Thru)
open import adequacy.Cursor.Tear using (NoIsle)
open import adequacy.Cursor using (Adm; cov; Owes)
open import adequacy.Rows using (pendRows)
open import adequacy.Dispatch using (module Over)
open import adequacy.FrShift using (rc; hr; HR)
open import adequacy.Few using (lag)
open import adequacy.Apart.Floor using (Busy)
open import adequacy.Bound using (good-full; pend-past)
open Machine using (pend; subscribing)
open import Tree using (Later; defer)
open import denotation.EmissionSet using (approx; DeferT; Lim) renaming (from to limᶠ; guard to dg; body to db)
open import denotation.Laws using (inv-approx)
open import denotation.Laws.Worlds using (Ok; InvAt; world-after; ok-step)
open import denotation.Laws.Modulus using (ticks; ≺-irrefl; ≺→≼)
open import Data.Nat using (zero; suc; _≤_)
open import Data.Nat.Properties using (n≤1+n)

open import adequacy.IsleLift using (Zs; z₁; z+; zs-past; zl; zs-btw; zs-under; isle-pin; pn)

-- A position under the first child has it among its ancestors.
under-∈ : ∀ q xs → (q ++ [ ix 0 ]) ∈ prefixes ((q ++ [ ix 0 ]) ++ xs)
under-∈ []      xs = here refl
under-∈ (a ∷ q) xs = there (∈-map⁺ (a ∷_) (under-∈ q xs))

-- A row at a chain's foot, of an entry with few rows behind `q`, reaches
-- what it depends on: those behind and the chain.
zs-reach : ∀ {A} {t : EmissionSet A} {q y e} → Behind (bef q) t → Zs q y → Reach t y e
zs-reach {t = t} {q} {y} (ks , f) z = ks ++ zl z , λ {k} {e′} tk ky _ → go tk ky (≼-or-≻ q k)
  where go : ∀ {k e′} → t k e′ → k ≺ y → q ≼ k ⊎ k ≺ q → k ∈ ks ++ zl z
        go tk ky (inj₁ qk) = ∈-++⁺ʳ ks (zs-btw z qk ky)
        go tk ky (inj₂ kq) = ∈-++⁺ˡ (f tk λ qk → qk kq)

reach-zs : ∀ {A} {t : EmissionSet A} {q y e} → Behind (bef q) t → Zs q y → t y e → Truncate t y e
reach-zs bh z r = r , zs-reach bh z

-- Nothing visible from `q` up to, not including, `y`.
record Clr {A} (q y : Pos) (E : EmissionSet A) : Set where
  constructor clr
  field clear : ∀ {w e} → E w e → Visible e → q ≼ w → w ≺ y → ⊥
open Clr

-- A row under the first child, and a row at or past the first child: a
-- row under it at or before the latter.
cap : ∀ {A} {t : EmissionSet A} {q r e′ p e} → t r e′ → (Σ Pos λ xs → r ≡ (q ++ [ ix 0 ]) ++ xs)
    → t p e → (q ++ [ ix 0 ]) ≼ p
    → Σ Pos λ r′ → Σ (Ev A) λ e″ → t r′ e″ × r′ ≼ p × (q ++ [ ix 0 ]) ∈ prefixes r′
cap {q = q} {r} {e′} {p} tr (xs , refl) tp zp with ≼-or-≻ r p
... | inj₁ rp = r , e′ , tr , rp , under-∈ q xs
... | inj₂ pr with <ᵖ-split (q ++ [ ix 0 ]) p (≼-false {q ++ [ ix 0 ]} {p} zp)
...   | inj₂ refl = p , _ , tp , ≼-refl {p} , subst (λ u → (q ++ [ ix 0 ]) ∈ prefixes u) (++-identityʳ _) (under-∈ q [])
...   | inj₁ zp′ with <ᵖ-between (q ++ [ ix 0 ]) p xs zp′ (Equivalence.to T-≡ pr)
...     | zs , refl = _ , _ , tp , ≼-refl {(q ++ [ ix 0 ]) ++ zs} , under-∈ q zs

-- Clear at `q`, a row under its first child: a row under it at or before
-- any visible row at or past `q`.
pick : ∀ {A} {t : EmissionSet A} {q r e′ p e} → t r e′ → (Σ Pos λ xs → r ≡ (q ++ [ ix 0 ]) ++ xs)
     → (∀ {e″} → t q e″ → Visible e″ → ⊥) → t p e → Visible e → q ≼ p
     → Σ Pos λ r′ → Σ (Ev A) λ e″ → t r′ e″ × r′ ≼ p × (q ++ [ ix 0 ]) ∈ prefixes r′
pick {q = q} {p = p} tr u cq tp vp qp with <ᵖ-split q p (≼-false {q} {p} qp)
... | inj₂ refl = ⊥-elim (cq tp vp)
... | inj₁ qp′ with ≼-or-≻ (q ++ [ ix 0 ]) p
...   | inj₂ pz = ⊥-elim (first-child q (Equivalence.from T-≡ qp′) pz)
...   | inj₁ zp = cap tr u tp zp

------------------------------------------------------------------------
-- THE LIFT: a skip at a chain's foot, nothing visible on the chain,
-- carried up through every live frame to the root's entry.

-- A hole whose frame still reads it: owed, or a running lane.
LiveN : Need → Set
LiveN owes          = ⊤
LiveN (dead _ _)      = ⊥
LiveN (lane b _ _)    = T b
LiveN (lanecut b _ _) = T b
LiveN (pnd _)       = ⊥

-- Clear row for row: clear above.
clr-≈ : ∀ {A} {E E′ : EmissionSet A} {q y} → E ≈ E′ → Clr q y E → Clr q y E′
clr-≈ m (clr c) = clr λ r v → c (proj₁ (from (alike m) (r , v))) v

clr-map : ∀ {A B} {f : A → B} {E q y} → Clr q y E → Clr q y (MapT f E)
clr-map (clr c) = clr go
  where go : ∀ {w e} → MapT _ _ w e → Visible e → _
        go (map-out r) _ = c r _
        go (map-end r) _ = c r _
        go (map-skip _) ()
        go (map-pin _) ()

clr-scan : ∀ {A B} {f : B → A → B} {z E q y} → Clr q y E → Clr q y (Scan.ScanT f z E)
clr-scan {f = f} {z} {E} {q} {y} (clr c) = clr go
  where go : ∀ {w e} → Scan.ScanT f z E w e → Visible e → q ≼ w → w ≺ y → ⊥
        go (Scan.sval (Scan.acc₀ r _))    _ = c r _
        go (Scan.sval (Scan.acc _ r _ _)) _ = c r _
        go (Scan.send r)                  _ = c r _
        go (Scan.sstep _) ()
        go (Scan.spin _) ()

clr-take : ∀ {A} {i} {keep : A → Bool} {E q y} → NoFail (bef q) keep E → Clr q y E → Clr q y (TakeWhile.TakeT i keep E)
clr-take {i = i} {keep} {E} {q} {y} nf (clr c) = clr go
  where go : ∀ {w e} → TakeWhile.TakeT i keep E w e → Visible e → q ≼ w → w ≺ y → ⊥
        go (TakeWhile.pass r _ _) _ = c r _
        go (TakeWhile.tend r _)   _ = c r _
        go (TakeWhile.fail {q′} r k _ _) _ _ wy = c r _ (nf r k) (≺-trans {q′} {q′ ++ [ ix 0 ]} {y} (≺-ext q′ []) wy)
        go (TakeWhile.stop {q′} r k _)   _ _ wy = c r _ (nf r k) (≺-trans {q′} {q′ ++ [ last ]} {y} (≺-ext q′ []) wy)
        go (TakeWhile.step _ _) ()
        go (TakeWhile.left _ _ _) ()

-- Nothing failed short of the foot.
unfailed : ∀ {A} {i} {keep : A → Bool} {E q y} → NoFail (bef q) keep E → Clr q y E → ¬ TakeWhile.Failed i keep E y
unfailed nf (clr c) (_ , _ , r , k , lt) = c r _ (nf r k) lt

clr-tr : ∀ {A} {t : EmissionSet A} {q y} → Clr q y t → Clr q y (Truncate t)
clr-tr (clr c) = clr λ r v → c (proj₁ r) v

zs-ze : ∀ {q y} → Zs q y → Ze q y
zs-ze z₁     = e+ e₀
zs-ze (z+ z) = e+ (zs-ze z)

zl-ze : ∀ {q y w} (z : Zs q y) → w ∈ zl z → Ze q w
zl-ze z₁     (here refl) = e₀
zl-ze (z+ z) (here refl) = zs-ze z
zl-ze (z+ z) (there m)   = zl-ze z m

-- On the chain, the rest of it below.
zl-zs : ∀ {q y w} (z : Zs q y) → w ∈ zl z → Zs w y
zl-zs z₁     (here refl) = z₁
zl-zs (z+ z) (here refl) = z₁
zl-zs (z+ z) (there m)   = z+ (zl-zs z m)

-- A lane subscribes at a second child.
st1 : ∀ op {A B} {F : A → Den B} {O q a s} → Start (polF op F O) q a s → Σ Pos λ s′ → s ≡ s′ ++ [ ix 1 ]
st1 (mergeᶠ nothing) {q = q} refl                        = q , refl
st1 (mergeᶠ (just m)) (_ , _ , Bounded.room _)           = _ , refl
st1 (mergeᶠ (just m)) (_ , _ , Bounded.freed _ _)        = _ , refl
st1 (mergeᶠ (just m)) (_ , _ , Bounded.queued _ _ _ _ _) = _ , refl
st1 switchᶠ {q = q} refl                                 = q , refl
st1 exhaustᶠ {q = q} refl                                = q , refl

-- A lane's region holds a first-child chain's head where it holds a
-- point of the chain.
rg-down : ∀ {A B} {H : Pos → Set} op {F : A → Den B} {O : EmissionSet A} {q w q′}
        → Ze q w → LaneRg H (polF op F O) O q′ w → LaneRg H (polF op F O) O q′ q
rg-down op e₀ r = r
rg-down op (e+ {w} e) (a , s , x , st , ws , ex) =
  rg-down op e (a , s , x , st , w-down ws refl ne , λ r pl v le → ex r pl v (⊑-trans le (⊑-snoc⁺ w)))
  where ne : s ≡ w ++ [ ix 0 ] → ⊥
        ne eq with st1 op st
        ... | s′ , refl with ∷ʳ-injectiveʳ s′ w eq
        ...   | ()

-- A joiner's visible rows, no lane begun before it: its outer's end, or a
-- lane's row.
module JV {A B : Set} {Ln : Pos → A → EmissionSet B} {o : EmissionSet A} {Bg : EmissionSet B} {Over Rn : Pos → Set}
          {Ct : Pos → Pos → Set} {Hd : Pos → Set} where
  open Joining Ln o Bg Over Rn Ct Hd

  jvis : (∀ {k e} → Bg k e → ⊥) → ∀ {k e} → JoinT k e → Visible e → o k end ⊎ Σ Pos λ q → Σ A λ a → o q (out a) × Ln q a k e
  jvis nb (oend r _)            _ = inj₁ r
  jvis nb (lane x _ l _ _)      _ = inj₂ (_ , _ , x , l)
  jvis nb (lend x _ l _ _ _)    _ = inj₂ (_ , _ , x , l)
  jvis nb (run b _)             _ = ⊥-elim (nb b)
  jvis nb (rend b _ _)          _ = ⊥-elim (nb b)
  jvis nb (val _)               ()
  jvis nb (step _)              ()
  jvis nb (opin _)              ()
  jvis nb (opass _ _)           ()
  jvis nb (lpass _ _ _ _ _ _)   ()
  jvis nb (hand _ _ _ _ _)      ()
  jvis nb (left _ _ _ _ _)      ()
  jvis nb (rpass _ _ _)         ()
  jvis nb (rhand _ _)           ()

jv : ∀ op {A B} {F : A → Den B} {O k e} → JoinF op F O k e → Visible e
   → O k end ⊎ Σ Pos λ q → Σ A λ a → O q (out a) × Lane (polF op F O) q a k e
jv (mergeᶠ nothing)  r v = JV.jvis (λ ()) r v
jv (mergeᶠ (just m)) r v = JV.jvis (λ ()) r v
jv switchᶠ           r v = JV.jvis (λ ()) r v
jv exhaustᶠ          r v = JV.jvis (λ ()) r v

jstep : ∀ op {A B} {F : A → Den B} {O q} → O q skip → JoinF op F O q skip
jstep (mergeᶠ nothing) {F = F} {O} r = Merge.step {f = F} {o = O} r
jstep (mergeᶠ (just m)) {F = F} {O} r = Bounded.step {n = m} {f = F} {o = O} r
jstep switchᶠ {F = F} {O} r = Switch.step {f = F} {o = O} r
jstep exhaustᶠ {F = F} {O} r = Exhaust.step {f = F} {o = O} r

jval : ∀ op {A B} {F : A → Den B} {O q a} → O q (out a) → JoinF op F O (q ++ [ ix 0 ]) skip
jval (mergeᶠ nothing) {F = F} {O} x = Merge.val {f = F} {o = O} x
jval (mergeᶠ (just m)) {F = F} {O} x = Bounded.val {n = m} {f = F} {o = O} x
jval switchᶠ {F = F} {O} x = Switch.val {f = F} {o = O} x
jval exhaustᶠ {F = F} {O} x = Exhaust.val {f = F} {o = O} x

jlane : ∀ op {A B} {F : A → Den B} {O q a k e} → O q (out a) → Runs (polF op F O) q → Lane (polF op F O) q a k e
      → (∀ {q′} → Kill (polF op F O) q q′ → q′ ≺ k → ⊥) → Work e → JoinF op F O k e
jlane (mergeᶠ nothing) {F = F} {O} x rn l nk w = Merge.lane {f = F} {o = O} x rn l (λ ()) w
jlane (mergeᶠ (just m)) {F = F} {O} x rn l nk w = Bounded.lane {n = m} {f = F} {o = O} x rn l (λ ()) w
jlane switchᶠ {F = F} {O} x rn l nk w = Switch.lane {f = F} {o = O} x rn l (λ { (_ , a′ , x′ , lt , lt′) → nk (a′ , x′ , lt) lt′ }) w
jlane exhaustᶠ {F = F} {O} x rn l nk w = Exhaust.lane {f = F} {o = O} x rn l (λ ()) w

-- A joiner clear on the chain: its outer, and every lane.
clr-join : ∀ op {A B} {F : A → Den B} {O q y} → (∀ {w} → O w end → q ≼ w → w ≺ y → ⊥)
         → (∀ {q′ a w e} → O q′ (out a) → Lane (polF op F O) q′ a w e → Visible e → q ≼ w → w ≺ y → ⊥)
         → Clr q y (JoinF op F O)
clr-join op c nl = clr λ r v qw wy → [ (λ e → c e qw wy) , (λ { (_ , _ , x , l) → nl x l v qw wy }) ]′ (jv op r v)

-- A lane's row on the chain: the chain's head in the lane's region.
on-chain : ∀ {Γ A B} (sc : Scope Γ) (f : A → Obs Timeline Γ B) {O : EmissionSet A} (ji : JInv sc f O) op {Rg : Rgn}
         → LanesIn (Hots (full sc)) (JRl sc Rg op f O) (polF op (λ a → ⟦ f a ⟧ (full sc)) O) O
         → ∀ {q y q′ a w e} (z : Zs q y) → O q′ (out a) → Lane (polF op (λ a → ⟦ f a ⟧ (full sc)) O) q′ a w e → q ≼ w → w ≺ y
         → LaneRg (Hots (full sc)) (polF op (λ a → ⟦ f a ⟧ (full sc)) O) O q′ q
on-chain sc f {O} ji op li z x l qw wy =
  rg-down op {F = λ a → ⟦ f a ⟧ (full sc)} {O} (zl-ze z (zs-btw z qw wy)) (proj₂ (Lanes.lane-rows sc f ji op li x l))

-- A source's rows behind the cursor, few, however it stands.
src-behind : ∀ {Γ X} {sc : Scope Γ} {Rg C} {k : CS Γ X} {o} → CS.scope k ≡ sc → Src sc Rg C k o → Behind C (Frozen k)
src-behind {C = C} {k = k} eq (src-pend _ _ _ _ adm _ _ ow _) = behind-pend {C = C} {k = k} eq adm ow
src-behind _  (src-on _ _ bh _ _ _ _ _)       = bh
src-behind _  (src-shut _ _ _ _ _ bh _ _ _ _)   = bh

-- A body's row at a chain's foot reaches within the connect: the body's
-- reach, and the source's rows behind or on the chain, one level down.
conn-reach : ∀ {A B} {p} {σ : EmissionSet A} {β : EmissionSet B} {q y e} → Behind (bef q) σ → Zs q y → Reach β y e
           → Reach (Connecting.ConnT p σ β) y e
conn-reach {p = p} {σ} {β} {q} {y} {e} (ks , f) z (ls , g) = ls ++ map (_++ [ ix 0 ]) (ks ++ zl z) , go
  where
    on : ∀ {k e′} → σ k e′ → k ≺ y → q ≼ k ⊎ k ≺ q → k ∈ ks ++ zl z
    on r ky (inj₁ qk) = ∈-++⁺ʳ ks (zs-btw z qk ky)
    on r ky (inj₂ kq) = ∈-++⁺ˡ (f r λ qk → qk kq)
    sl : ∀ {k e′} → σ k e′ → (k ++ [ ix 0 ]) ≺ y → (k ++ [ ix 0 ]) ∈ (ls ++ map (_++ [ ix 0 ]) (ks ++ zl z))
    sl {k} r lt = ∈-++⁺ʳ ls (∈-map⁺ (_++ [ ix 0 ]) (on r ky (≼-or-≻ q k)))
      where ky = ≺-trans {k} {k ++ [ ix 0 ]} {y} (≺-ext k []) lt
    go : ∀ {k e′} → Connecting.ConnT p σ β k e′ → k ≺ y → Dep y e k e′ → k ∈ (ls ++ map (_++ [ ix 0 ]) (ks ++ zl z))
    go (Connecting.body r)        lt d = ∈-++⁺ˡ (g r lt d)
    go (Connecting.burst r _)     lt _ = sl r lt
    go (Connecting.echo r _ _ _)  lt _ = sl r lt
    go (Connecting.kept r _ _ _)  lt _ = sl r lt

-- A connect clear where its body is: its burst, echoes and kept pins are
-- silent.
clr-conn : ∀ {A B} {p} {σ : EmissionSet A} {β : EmissionSet B} {q y} → Clr q y β → Clr q y (Connecting.ConnT p σ β)
clr-conn {p = p} {σ} {β} {q} {y} (clr c) = clr go
  where go : ∀ {w e} → Connecting.ConnT p σ β w e → Visible e → q ≼ w → w ≺ y → ⊥
        go (Connecting.body r)       = c r
        go (Connecting.burst _ _)    ()
        go (Connecting.echo _ _ _ _) ()
        go (Connecting.kept _ _ _ _) ()

-- A flag, true or false.
bool? : ∀ b → T b ⊎ b ≡ false
bool? true  = inj₁ tt
bool? false = inj₂ refl

nT : ∀ {b} → b ≡ false → T (not b)
nT refl = tt

-- A silent row a lift carries: a skip, or a pin of a connect at or above it.
data Mute {A : Set} (y : Pos) : Ev A → Set where
  m-skip : Mute y skip
  m-pin  : ∀ {r} → T (inside r y) → Mute y (pin r)

mute-work : ∀ {A y} {e : Ev A} → Mute y e → Work e
mute-work m-skip    = tt
mute-work (m-pin _) = tt

mute-z : ∀ {A y} {e : Ev A} → Mute y e → Mute (y ++ [ ix 0 ]) e
mute-z m-skip          = m-skip
mute-z {y = y} (m-pin {r} i) = m-pin (⊑-inside (⊑-trans (inside-⊑ r y i) (⊑-snoc⁺ y)))

map-m : ∀ {A B} {f : A → B} {t : EmissionSet A} {y e} → Mute y e → t y e → Σ (Ev B) λ e′ → MapT f t y e′ × Mute y e′
map-m m-skip    r = skip , map-skip r , m-skip
map-m (m-pin i) r = pin _ , map-pin r , m-pin i

scan-m : ∀ {A B} {f : B → A → B} {z} {t : EmissionSet A} {y e} → Mute y e → t y e → Σ (Ev B) λ e′ → Scan.ScanT f z t y e′ × Mute y e′
scan-m m-skip    r = skip , Scan.sstep r , m-skip
scan-m (m-pin i) r = pin _ , Scan.spin r , m-pin i

-- A takeWhile keeps a silent row short of its failure: a pin, since its
-- connect lies at or above it.
take-m : ∀ {A} {i} {keep : A → Bool} {t : EmissionSet A} {y e} → Mute y e → t y e → ¬ TakeWhile.Failed i keep t y → TakeWhile.TakeT i keep t y e
take-m m-skip r nf = TakeWhile.step r nf
take-m {y = y} (m-pin {p′} i) r nf =
  TakeWhile.left r (λ { (q′ , a , x , k , lt) → nf (q′ , a , x , k , ≺-≼-≺ {q′} {p′} {y} lt (⊑-≼ (inside-⊑ p′ y i))) }) i

jpin : ∀ op {A B} {F : A → Den B} {O q r} → O q (pin r) → JoinF op F O q (pin r)
jpin (mergeᶠ nothing) {F = F} {O} x = Merge.opin {f = F} {o = O} x
jpin (mergeᶠ (just m)) {F = F} {O} x = Bounded.opin {n = m} {f = F} {o = O} x
jpin switchᶠ {F = F} {O} x = Switch.opin {f = F} {o = O} x
jpin exhaustᶠ {F = F} {O} x = Exhaust.opin {f = F} {o = O} x

jrow : ∀ op {A B} {F : A → Den B} {O : EmissionSet A} {y e} → Mute y e → O y e → Σ (Ev B) λ e′ → JoinF op F O y e′ × Mute y e′
jrow op {F = F} {O} m-skip    r = skip , jstep op {F = F} {O} r , m-skip
jrow op {F = F} {O} (m-pin i) r = pin _ , jpin op {F = F} {O} r , m-pin i

-- A source's silent row, a level down in its connect: a pin inside the
-- subscribe burst, an echo past it while the body runs, a kept pin.
src-row : ∀ {A B} {p} {σ : EmissionSet A} {β : EmissionSet B} {y e} → σ y e → Mute y e → Connecting.Alive p σ β y
        → Σ (Ev B) λ e′ → Connecting.ConnT p σ β (y ++ [ ix 0 ]) e′ × Mute (y ++ [ ix 0 ]) e′
src-row {p = p} {y = y} r mu al with bool? (inside (p ++ [ ix 1 ]) y)
... | inj₁ i = pin p , Connecting.burst r i , m-pin (⊑-inside (⊑-trans (⊑-trans (⊑-snoc⁺ p) (inside-⊑ (p ++ [ ix 1 ]) y i)) (⊑-snoc⁺ y)))
... | inj₂ ni with mu
...   | m-skip = skip , Connecting.echo r al tt (nT ni) , m-skip
...   | m-pin {p′} i = pin p′ , Connecting.kept r (λ be → ≼-≺-≺ {p′} {y} (⊑-≼ (inside-⊑ p′ y i)) (al be)) (nT ni) i , mute-z (m-pin i)

-- A source's row of its own, a level down in its connect: a pin inside
-- the subscribe burst, an echo past it while the body runs.
src-out : ∀ {A B} {p} {σ : EmissionSet A} {β : EmissionSet B} {y e} → σ y e → Unpinned e → Connecting.Alive p σ β y
        → Σ (Ev B) λ e′ → Connecting.ConnT p σ β (y ++ [ ix 0 ]) e′ × Mute (y ++ [ ix 0 ]) e′
src-out {p = p} {y = y} r up al with bool? (inside (p ++ [ ix 1 ]) y)
... | inj₁ i  = pin p , Connecting.burst r i , m-pin (⊑-inside (⊑-trans (⊑-trans (⊑-snoc⁺ p) (inside-⊑ (p ++ [ ix 1 ]) y i)) (⊑-snoc⁺ y)))
... | inj₂ ni = skip , Connecting.echo r al up (nT ni) , m-skip

unp : ∀ {A} (e : Evᴹ A) → Unpinned (toEv e)
unp (nx _) = tt
unp cp     = tt

-- THE FLOOR, frame by frame: every connect a source frame reads owes its
-- body's end no sooner than the clock.
Lo₀ : ∀ {R Γ A} → Pos → Ctx R Γ A → Set
Lo₀ q top                               = ⊤
Lo₀ q (inMap f c)                       = Lo₀ q c
Lo₀ q (inScan f z c)                    = Lo₀ q c
Lo₀ q (inCut l a c)                     = Lo₀ q c
Lo₀ q (inLn b c)                        = Lo₀ q c
Lo₀ q (inTake i p w c)                  = Lo₀ q c
Lo₀ q (inOuter op f ω d n qu ls c)      = Lo₀ q c
Lo₀ q (inLanes op f ω d n qu o pre post c) = Lo₀ q c
Lo₀ q (inSrc k b c)                     = (∀ {c₀} → CS.owedAt k ≡ just c₀ → after c₀ <ᴷ after q ≡ false) × Lo₀ q c
Lo₀ q (inBody k o c)                    = Lo₀ q c

lo₀ : ∀ {R Γ A} (c : Ctx R Γ A) {s : St Γ A} {q} → Lo (plug c s) (after q) → Lo₀ q c
lo₀ top                                lo = tt
lo₀ (inMap f c) {s}                    lo = lo₀ c {mapS f s} lo
lo₀ (inScan f z c) {s}                 lo = lo₀ c {scanS f z s} lo
lo₀ (inCut l a c) {s}                  lo = lo₀ c {cutS l a s} lo
lo₀ (inLn b c) {s}                     lo = lo₀ c {lnS b s} lo
lo₀ (inTake i p w c) {s}               lo = lo₀ c {takeS i p w s} lo
lo₀ (inOuter op f ω d n qu ls c) {s}   lo = lo₀ c {flatS op f ω d n qu s ls} lo
lo₀ (inLanes op f ω d n qu o pre post c) {s} lo = lo₀ c {flatS op f ω d n qu o (pre ʳ++ s ∷ post)} lo
lo₀ (inSrc k b c) {s}                  lo = (λ eq → lo (plug-in c (k-own (own-bld k {s} {b} (oo eq))))) , lo₀ c {connS k s b} lo
lo₀ (inBody k o c) {s}                 lo = lo₀ c {connS k o s} lo

tf : true ≡ false → ⊥
tf ()

-- A live source's connect has its body alive at `y`, every point from the
-- source's hole `q` to `y` on its first-child chain: its body's end at or
-- past `q` would lie in the source's part, and one before `q` would be
-- owed behind the floor.
conn-alive : ∀ {Γ X B} {sc : Scope Γ} {Rg} {k : CS Γ X} {β : EmissionSet B} {q y} (pt : Parts sc Rg k β)
           → Flags (bef q) k β → T (CS.srcLive k) → (∀ {c₀} → CS.owedAt k ≡ just c₀ → after c₀ <ᴷ after q ≡ false)
           → (CS.connAt k ++ [ ix 1 ]) ≼ q → Parts.Rs pt q → (∀ {c₀} → q ≼ c₀ → c₀ ≼ y → Ze q c₀)
           → Connecting.Alive (CS.connAt k) (Frozen k) β y
conn-alive {q = q} {y} pt fl lv lof past g on {c₀} be with ≼-or-≻ q c₀
... | inj₁ qc with ≼-or-≻ c₀ y
...   | inj₁ cy = ⊥-elim (Parts.b-chain pt past g (on qc cy) (Sound.rg (Parts.sb pt) be tt))
...   | inj₂ yc = yc
conn-alive {q = q} pt fl lv lof past g on {c₀} be | inj₂ cq with bool? (inside c₀ q)
... | inj₁ i  = ⊥-elim (Parts.b-lead pt (Sound.rg (Parts.sb pt) be tt) g (inside-⊑ c₀ q i))
... | inj₂ ni = ⊥-elim (tf (trans (sym (<ᴷ-trans (after c₀) (at q) (after q) (after-lt c₀ q (Equivalence.to T-≡ cq) ne) (at-after₀ q)))
                                  (lof (Flags.ended fl lv be λ qc → qc cq))))
  where ne : ∀ z′ → q ≡ c₀ ++ z′ → ⊥
        ne z′ eq = notT (inside c₀ q) (nT ni) (⊑-inside (z′ , eq))

module Lift {R : Set} (Rt : EmissionSet R) where

  -- A row of the root's at a chain's foot, the chain clear.
  Lifted : Cur → Pos → Set
  Lifted Cr q = Σ Pos λ r → Σ (Ev R) λ e → Rt r e × Zs q r × Clr q r Rt × Cr ≡ bef q

  -- The lift met a source in its subscribe burst under a connect no live
  -- node reads: the isle's frame, where it sits in the root's state, and
  -- the isle's row the lift carried, at the step or on its chain.
  data Isled (Cr : Cur) (q : Pos) (S : St [] R) : Set₁ where
    isled : ∀ {Γ X B} {c : Ctx R Γ B} {k : CS Γ X} {b : St (X ∷ Γ) B} {o C D Db P Qb Ri β E′ y e}
          → Unread Rt Cr C D E′ β c k P → Husk (binds (CS.src k) (CS.connAt k) (CS.scope k)) Db b β Qb → Up Db β D E′
          → P ⊑ (Burst (bef q) k ∪ᵖ Qb)
          → T (not (CS.srcAtt k)) → T (not (CS.closed k)) → Behind (bef q) (Frozen k) → Subd (scopeOf c) (bef q) k
          → Sound Ri (Frozen k) → AttOwed k → InCall (bef q) k → Bursts k E′ → Thru D (CS.connAt k) → NoIsle b
          → S ≡ plug c (connS k o b) → Frozen k y e → y ≡ q ⊎ Zs q y → Isled Cr q S

  lift : ∀ {Cr Γ A} {c : Ctx R Γ A} {s : St Γ A} {Rg N E q y e} → Fr Rt Cr (bef q) Rg c N E → Lo₀ q c → LiveN N
       → E y e → Mute y e → Zs q y → Clr q y E → Rg q → Lifted Cr q ⊎ Isled Cr q (plug c s)
  lift {y = y} (f-top m) lo _ r mu z cl g = inj₁ (y , _ , voc m r , z , clr-≈ m cl , refl)
  lift {s = s} (f-map {f = f} fr m _) lo _ r mu z cl g =
    let (_ , r′ , mu′) = map-m mu r in lift {s = mapS f s} fr lo _ (voc m r′) mu′ z (clr-≈ m (clr-map cl)) g
  lift {s = s} (f-scan {f = f} {z = z₀} fr _ m _) lo _ r mu z cl g =
    let (_ , r′ , mu′) = scan-m mu r in lift {s = scanS f z₀ s} fr lo _ (voc m r′) mu′ z (clr-≈ m (clr-scan cl)) g
  lift {s = s} (f-cut {a = a} fr) lo _ r mu z cl g = lift {s = cutS true a s} fr lo _ r mu z cl g
  lift {s = s} {q = q} {y} (f-take {i = i} {keep = keep} fr nf m _) lo _ r mu z cl g =
    lift {s = takeS i keep free s} fr lo _ (voc m (take-m mu r (unfailed {i = i} {q = q} {y} nf cl))) mu z (clr-≈ m (clr-take {q = q} {y} nf cl)) g
  lift {s = s} (f-lane {b = b} fr) lo l r mu z cl g = lift {s = lnS b s} fr lo l r mu z cl g
  lift {s = s} (f-lnct {a = a} {b = true} fr) lo _ r mu z cl g = lift {s = cutS true a s} fr lo _ r mu z cl g
  lift (f-lnct {b = false} fr) _ ()
  lift {s = s} {q = q} {y} (f-outer {op = op} {f = f} {ω = ω} {d = d} {n = n} {qu = qu} {ls = ls} {c = c} {E = O} fr ji (joined _ _ _ _ _ _ _ li) je _ bh) lo _ r mu z cl g =
    let (_ , r′ , mu′) = jrow op {F = F′} {O} mu r in
    lift {s = flatS op f ω d n qu s ls} fr lo _ (voc (proj₂ je) (reach-zs bh z r′)) mu′ z
      (clr-≈ (proj₂ je) (clr-tr (clr-join op {F = F′} {O} (λ e qw wy → clear cl e tt qw wy) λ x l _ qw wy → proj₂ g (on-chain (scopeOf c) f ji op li z x l qw wy)))) (proj₁ g)
    where F′ = λ a → ⟦ f a ⟧ (full (scopeOf c))
  lift {s = s} {q = q} {y} (f-lanes {op = op} {f = f} {ω = ω} {d = d} {n = n} {qu = qu} {o = o′} {pre = pre} {post = post} {c = c} {O = O} {q = q₀} {a} fr ji _ _ x _ rn (h-live _ le uk) _ _ _ _ _ _ _ _ li je so _ bh _) lo _ r mu z cl g =
    lift {s = flatS op f ω d n qu o′ (pre ʳ++ s ∷ post)} fr lo _ (voc (proj₂ je) (reach-zs bh z (jlane op {F = F′} {O} x rn ly nk (mute-work mu)))) mu z (clr-≈ (proj₂ je) (clr-tr (clr-join op {F = F′} {O} oc lc))) (proj₁ g)
    where
      F′ = λ a → ⟦ f a ⟧ (full (scopeOf c))
      ly = voc le r
      ry : LaneRg (Hots (full (scopeOf c))) (polF op F′ O) O q₀ y
      ry = proj₂ (Lanes.lane-rows (scopeOf c) f ji op li x ly)
      down : ∀ {w} → q ≼ w → w ≺ y → LaneRg (Hots (full (scopeOf c))) (polF op F′ O) O q₀ w
      down qw wy = rg-down op {F = F′} {O} (zs-ze (zl-zs z (zs-btw z qw wy))) ry
      nk : ∀ {q′} → Kill (polF op F′ O) q₀ q′ → q′ ≺ y → ⊥
      nk k lt = proj₂ (Sound.rg so (proj₁ (proj₂ (kill-out op k))) tt) (down (uk k) lt)
      oc : ∀ {w} → O w end → q ≼ w → w ≺ y → ⊥
      oc e qw wy = proj₂ (Sound.rg so e tt) (down qw wy)
      lc : ∀ {q′ a′ w e} → O q′ (out a′) → Lane (polF op F′ O) q′ a′ w e → Visible e → q ≼ w → w ≺ y → ⊥
      lc x′ l v qw wy with lane-sole (JInv.ok ji) F′ (JInv.fi ji) (JInv.io ji) op (proj₂ (Lanes.lane-rows (scopeOf c) f ji op li x′ l)) (down qw wy)
      ... | refl with Sound.fn so x x′ tt tt
      ...   | refl = clear cl (proj₁ (from (alike le) (l , v))) v qw wy
  lift (f-lanes _ _ _ _ _ _ _ (h-end _ _ _) _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ ()
  lift (f-lanes _ _ _ _ _ _ _ (h-kill _ _ _) _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ ()
  lift {s = s} {q = q} {y} (f-src {k = k} {b = b} {β = β} fr _ pt lv _ _ bβ fl fz ce bσ sd _ _ _ _) (lof , lo) _ r mu z cl g =
    let (_ , row , mu′) = src-row (voc fz r) mu alive in
    lift {s = connS k s b} fr lo tt (voc (proj₁ ce) (row , conn-reach bσ (z+ z) (zs-reach bβ (z+ z)))) mu′ (z+ z)
      (clr-≈ (proj₁ ce) (clr-tr (clr-conn clb))) (Parts.s⊆ pt g)
    where
      past : (CS.connAt k ++ [ ix 1 ]) ≼ q
      past = SubdAt.past sd {q} (≼-refl {q})
      clb : Clr q (y ++ [ ix 0 ]) β
      clb = clr λ b v qw wy → Parts.b-chain pt past g (zl-ze (z+ z) (zs-btw (z+ z) qw wy)) (Sound.rg (Parts.sb pt) b v)
      on : ∀ {c₀} → q ≼ c₀ → c₀ ≼ y → Ze q c₀
      on {c₀} qc cy with <ᵖ-split c₀ y (≼-false {c₀} {y} cy)
      ... | inj₁ lt   = zl-ze z (zs-btw z qc (Equivalence.from T-≡ lt))
      ... | inj₂ refl = zs-ze z
      alive : Connecting.Alive (CS.connAt k) (Frozen k) β y
      alive = conn-alive {q = q} {y} pt fl lv lof past g on
  lift {s = s} (f-body {k = k} {o = o′} fr sc pt _ sr _ _ ce) lo _ r mu z cl g =
    lift {s = connS k o′ s} fr lo _ (voc (proj₁ ce) (Connecting.body r , conn-reach (src-behind sc sr) z (proj₂ ce r))) mu z
      (clr-≈ (proj₁ ce) (clr-tr (clr-conn cl))) (Parts.b⊆ pt g)
  lift (f-isle u hb ub le na nc bh sd ss ao ic bu nr ni) _ _ r _ z _ _ = inj₂ (isled u hb ub le na nc bh sd ss ao ic bu nr ni refl r (inj₂ z))
  lift (f-took _ _ _ _ _ _ _ _ _ _) _ ()
  lift (f-srcc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ ()
  lift (f-srcp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ ()
  lift (d-map _ _) _ ()
  lift (d-scan _ _) _ ()
  lift (d-cut _ _) _ ()
  lift (d-ln _ _) _ ()
  lift (d-take _ _) _ ()
  lift (d-outer _ _ _ _) _ ()
  lift (d-lanes _ _ _ _ _ _ _) _ ()
  lift (d-src _ _ _ _ _ _ _) _ ()
  lift (d-body _ _ _ _) _ ()
  lift (f-islec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ ()
  lift (f-islep _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ ()

-- A ROW AT OR UNDER `y`: a row of the root's entry at or before `p`, with
-- `y` itself or one of its ancestors.  A connect shows its source's rows a
-- level down, so a row made inside a source is met only under it.
RowUnder : ∀ {R} → PureObs [] R → Pos → Pos → Set
RowUnder o y p = Σ Pos λ r → Σ _ λ e′ → enter (⟦ o ⟧ []ᴬ) root r e′ × r ≼ p × y ∈ prefixes r

module Outer {R} (o : PureObs [] R) where
  private
    Rt = enter (⟦ o ⟧ []ᴬ) root
  open Lift Rt

  -- An outer's value in flight: its first child a skip of the joiner's,
  -- nothing visible at the value, carried up.
  outer-row : ∀ {Cr Γ A B} {op} {f : A → Obs Timeline Γ B} {ω d n qu ls} {c : Ctx R Γ B} {s a q Rg N E}
            → Fr Rt Cr (bef q) Rg (inOuter op f ω d n qu ls c) N E → Lo₀ q c → Fly (scopeOf c) Rg q N s E (nx a)
            → Lifted Cr q ⊎ Isled Cr q (plug c (flatS op f ω d n qu s ls))
  outer-row {s = s} {q = q} (f-outer {op = op} {f = f} {ω = ω} {d = d} {n = n} {qu = qu} {ls = ls} {c = c} {E = O} fr ji (joined _ _ _ _ _ _ _ li) je sd bh) lo (_ , x) =
    lift {s = flatS op f ω d n qu s ls} fr lo tt (voc (proj₂ je) (reach-zs bh z₁ (jval op {F = F′} {O} x))) m-skip z₁
      (clr-≈ (proj₂ je) (clr-tr (clr-join op {F = F′} {O} oc lc))) (proj₁ (Sound.rg sd x tt))
    where
      F′ = λ a → ⟦ f a ⟧ (full (scopeOf c))
      oc : ∀ {w} → O w end → q ≼ w → w ≺ (q ++ [ ix 0 ]) → ⊥
      oc {w} e qw wy with zs-btw {q} {q ++ [ ix 0 ]} {w} z₁ qw wy
      ... | here refl with Sound.fn sd x e tt tt
      ...   | ()
      lc : ∀ {q′ a′ w e} → O q′ (out a′) → Lane (polF op F′ O) q′ a′ w e → Visible e → q ≼ w → w ≺ (q ++ [ ix 0 ]) → ⊥
      lc x′ l _ qw wy = proj₂ (Sound.rg sd x tt) (on-chain (scopeOf c) f ji op li z₁ x′ l qw wy)
  outer-row (d-outer _ _ _ _) _ ()

  -- A source's step in flight: its row a level down, carried up.
  src-step : ∀ {Cr Γ X B} {k : CS Γ X} {b} {c : Ctx R Γ B} {s ε q Rg N E}
           → Fr Rt Cr (bef q) Rg (inSrc k b c) N E → Lo₀ q (inSrc k b c) → Fly (scopeOf c) Rg q N s E ε
           → Lifted Cr q ⊎ Isled Cr q (plug c (connS k s b))
  src-step {s = s} {ε = ε} {q} (f-src {k = k} {b = b} {β = β} fr _ pt lv _ _ bβ fl fz ce bσ sd _ _ _ _) (lof , lo) (_ , row) =
    let (_ , cr , mu) = src-out fk (unp ε) alive in
    lift {s = connS k s b} fr lo tt (voc (proj₁ ce) (cr , conn-reach bσ z₁ (zs-reach bβ z₁))) mu z₁
      (clr-≈ (proj₁ ce) (clr-tr (clr-conn clb))) (Parts.s⊆ pt rs)
    where
      fk = voc fz row
      rs : Parts.Rs pt q
      rs = Sound.rg (Parts.ss pt) fk (vis ε)
      past : (CS.connAt k ++ [ ix 1 ]) ≼ q
      past = SubdAt.past sd {q} (≼-refl {q})
      clb : Clr q (q ++ [ ix 0 ]) β
      clb = clr λ b v qw wy → Parts.b-chain pt past rs (zl-ze z₁ (zs-btw z₁ qw wy)) (Sound.rg (Parts.sb pt) b v)
      on : ∀ {c₀} → q ≼ c₀ → c₀ ≼ q → Ze q c₀
      on {c₀} qc cq with <ᵖ-split c₀ q (≼-false {c₀} {q} cq)
      ... | inj₁ lt   = ⊥-elim (qc (Equivalence.from T-≡ lt))
      ... | inj₂ refl = e₀
      alive : Connecting.Alive (CS.connAt k) (Frozen k) β q
      alive = conn-alive {q = q} {q} pt fl lv lof past rs on
  src-step (f-isle u hb ub le na nc bh sd ss ao ic bu nr ni) _ (_ , row) = inj₂ (isled u hb ub le na nc bh sd ss ao ic bu nr ni refl row (inj₁ refl))
  src-step (f-srcc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ ()
  src-step (f-srcp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ ()
  src-step (d-src _ _ _ _ _ _ _) _ ()
  src-step (f-islec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ ()
  src-step (f-islep _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ ()

  -- Lifted, clear at `q`, the cursor short of the row met next: a row
  -- under the first child at or before it.
  under : ∀ {Cr q p e} → Lifted Cr q → Due Cr Rt p e → RowUnder o (q ++ [ ix 0 ]) p
  under {q = q} (r , _ , tr , z , cl , refl) (tp , vp , ow) = pick tr (zs-under z) (λ t v → clear cl t v (≼-refl {q}) (zs-past z)) tp vp ow

  -- The row met next, owed at the cursor the run reaches.
  met : ∀ {rs k p e} (pth : Path (load o) rs k) → Meets Rt (conv rs ++ [ (p , e) ])
      → Due (proj₁ (proj₁ (Along.along (cursor o) nothing pth (Simulation.i₀ (cursor o)) (Simulation.t₀ (cursor o))))) Rt p e
  met {rs} pth m with Along.along (cursor o) nothing pth (Simulation.i₀ (cursor o)) (Simulation.t₀ (cursor o))
                    | Along.met-next (cursor o) {c = nothing} (conv rs) m
  ... | (Cr , _) , r | ((tp , _) , _) , vi , ap , _ = proj₁ (from r (back (cursorᴿ nothing (conv rs)) tp ap , vi))

-- AN ISLE SHOWS UNDER ITS STEP: a step rising whose lift meets a source
-- in its subscribe burst under a connect no live node reads has a row of
-- the root's entry under its first child.
isle-row : ∀ {R} (o : PureObs [] R) {rs Γ A} {c : Ctx R Γ A} {s m q Cr}
         → Path (load o) rs ⟨ c , s , m , q ⟩ → Busy m
         → Lift.Isled (enter (⟦ o ⟧ []ᴬ) root) Cr q (plug c s)
         → Σ Pos λ r → Σ (Ev R) λ e′ → enter (⟦ o ⟧ []ᴬ) root r e′ × Σ Pos λ xs → r ≡ (q ++ [ ix 0 ]) ++ xs
isle-row o {q = q} pth bz (Lift.isled {c = c} {k = k} {b = b} {o = o′} u hb _ le _ _ bh sd _ ao _ bu nr _ eq row yq)
  with isle-pin (enter (⟦ o ⟧ []ᴬ) root) {c = c} {k = k} {o = o′} {b = b} u hb le bh sd ao bu nr (subst (λ S → Lo S (after q)) eq (floor o pth bz)) row yq
... | pn {y} _ _ x _ z with zs-under z
...   | xs , refl = y , _ , x , xs , refl

-- A GUARD IN AN ISLE: a row under the step's first child, at or before
-- the row met next, which the connect's frames bound past it.
guard-src : ∀ {R} (o : PureObs [] R) {rs Γ A} {c : Ctx R Γ A} {s m q p e Cr}
          → Path (load o) rs ⟨ c , s , m , q ⟩ → Busy m → Due Cr (enter (⟦ o ⟧ []ᴬ) root) p e
          → Lift.Isled (enter (⟦ o ⟧ []ᴬ) root) Cr q (plug c s)
          → RowUnder o (q ++ [ ix 0 ]) p
guard-src o {q = q} pth bz du il@(Lift.isled u _ _ _ _ _ _ _ _ _ _ _ _ _ eq _ _) with isle-row o pth bz il
... | _ , _ , tr , un = cap tr un (proj₁ du) (fb-u (enter (⟦ o ⟧ []ᴬ) root) u lo du)
  where lo = lo-p (lo-weaken (at (q ++ [ ix 0 ])) (after q) (subst (λ S → Lo S (after q)) eq (floor o pth bz)) (at-after q [ ix 0 ]))

-- AN OUTER'S GUARD IS MET: an outer's value rising has a row under its
-- first child, at or before the row met next.
outer-guard : ∀ {R} (o : PureObs [] R) {rs Γ A B} {op} {f : A → Obs Timeline Γ B} {ω d n qu ls} {c : Ctx R Γ B} {s a q p e}
            → Path (load o) rs ⟨ inOuter op f ω d n qu ls c , s , rising (nx a) , q ⟩
            → Meets (enter (⟦ o ⟧ []ᴬ) root) (conv rs ++ [ (p , e) ])
            → RowUnder o (q ++ [ ix 0 ]) p
outer-guard o {op = op} {f} {ω} {d} {n} {qu} {ls} {c} {s} pth m
  with Along.along (cursor o) nothing pth (Simulation.i₀ (cursor o)) (Simulation.t₀ (cursor o)) | Outer.met o pth m
... | (_ , _ , flying fr _ fy , _) , _ | du with Outer.outer-row o fr (lo₀ c {flatS op f ω d n qu s ls} (floor o pth tt)) fy
...   | inj₁ lf = Outer.under o lf du
...   | inj₂ il = guard-src o pth tt du il
outer-guard o pth m | (_ , _ , adrift fr cl _ , _) , _ | _ = ⊥-elim (subst T cl (dead-closed (enter (⟦ o ⟧ []ᴬ) root) fr refl))

-- A SOURCE'S STEP IS ECHOED: a source rising under its connect leaves a
-- row a level down, under it, at or before the row met next.
echo-guard : ∀ {R} (o : PureObs [] R) {rs Γ X B} {k : CS Γ X} {b : St (X ∷ Γ) B} {c : Ctx R Γ B} {s ε q p e}
           → Path (load o) rs ⟨ inSrc k b c , s , rising ε , q ⟩
           → Meets (enter (⟦ o ⟧ []ᴬ) root) (conv rs ++ [ (p , e) ])
           → RowUnder o (q ++ [ ix 0 ]) p
echo-guard o {k = k} {b} {c} {s} pth m
  with Along.along (cursor o) nothing pth (Simulation.i₀ (cursor o)) (Simulation.t₀ (cursor o)) | Outer.met o pth m
... | (_ , _ , flying fr _ fy , _) , _ | du with Outer.src-step o fr (lo₀ (inSrc k b c) {s} (floor o pth tt)) fy
...   | inj₁ lf = Outer.under o lf du
...   | inj₂ il = guard-src o pth tt du il
echo-guard o pth m | (_ , _ , adrift fr cl _ , _) , _ | _ = ⊥-elim (subst T cl (dead-closed (enter (⟦ o ⟧ []ᴬ) root) fr refl))

-- A DEFER'S GUARD: its skip at its first child, a row of its entry.  Its
-- body's rows all lie past its second child.
defer-row : ∀ {Γ A} (sc : Scope Γ) (l : Later Timeline Γ A) {q} → Adm sc → Ok (Hots (full sc)) q
          → pendRows (full sc) (defer l) q (q ++ [ ix 0 ]) skip
defer-row sc l {q} a ok = limᶠ 1 row , [] , λ { (limᶠ N h) lt _ → ⊥-elim (before N (proj₁ (h (suc N) (n≤1+n N))) lt) }
  where
    before : ∀ m {k e} → DeferT (approx m (Later.force l) (full sc)) q k e → k ≺ (q ++ [ ix 0 ]) → ⊥
    before m dg lt = ≺-irrefl {q ++ [ ix 0 ]} lt
    before m {k} (db x) lt =
      ≺-irrefl {q ++ [ ix 0 ]} (≺-trans {q ++ [ ix 0 ]} {q ++ [ ix 1 ]} {q ++ [ ix 0 ]} (ticks q 0)
        (≺-trans {q ++ [ ix 1 ]} {k} {q ++ [ ix 0 ]} (world-after (InvAt.world I x) (InvAt.real I x)) lt))
      where I = inv-approx m (Later.force l) (full sc) (good-full sc a) (q ++ [ ix 1 ]) (ok-step q ok)
    row : ∀ n → 1 ≤ n → enter (approx n (defer l) (full sc)) q (q ++ [ ix 0 ]) skip
    row zero ()
    row (suc m) _ = dg , [] , λ x lt _ → ⊥-elim (before m x lt)

-- A DEFER'S GUARD, LIFTED: the frames re-cursored to the defer's own
-- position, its guard carried up.
defer-lift : ∀ {R} (o : PureObs [] R) {rs Γ A} {c : Ctx R Γ A} {l q p e Cr C Rg E}
           → Path (load o) rs ⟨ c , pend (defer l) q , subscribing , q ⟩
           → Due Cr (enter (⟦ o ⟧ []ᴬ) root) p e
           → Fr (enter (⟦ o ⟧ []ᴬ) root) Cr C Rg c owes E → Owes C q → HR C q (scopeOf c) E
           → E (q ++ [ ix 0 ]) skip → Clr q (q ++ [ ix 0 ]) E → Rg q
           → RowUnder o (q ++ [ ix 0 ]) p
defer-lift o {c = c} {l} {q} pth du fr ow h g cl rg
  with rc (enter (⟦ o ⟧ []ᴬ) root) {s = pend (defer l) q} fr h ow (lo-weaken (at q) (after q) (floor o pth tt) (at-after₀ q))
... | _ , fr′ , _ , _ , d
  with Lift.lift (enter (⟦ o ⟧ []ᴬ) root) {s = pend (defer l) q} fr′ (lo₀ c {pend (defer l) q} (floor o pth tt)) tt g m-skip z₁ cl rg
...   | inj₁ lf = Outer.under o lf (_≃_.to d du)
...   | inj₂ il = guard-src o pth tt (_≃_.to d du) il

-- A pending defer: its rows past it, so none owed before it, and none at
-- it.
defer-pend : ∀ {R} (o : PureObs [] R) {rs Γ A} {c : Ctx R Γ A} {l q p e Cr C}
           → Path (load o) rs ⟨ c , pend (defer l) q , subscribing , q ⟩
           → Due Cr (enter (⟦ o ⟧ []ᴬ) root) p e
           → Over.PendV (enter (⟦ o ⟧ []ᴬ) root) Cr C c (defer l) q
           → RowUnder o (q ++ [ ix 0 ]) p
defer-pend o {c = c} {l} {q} {C = C} pth du (Rg , E , fr , ow , ok , ad , pe , wi) =
  defer-lift o pth du fr ow (hr λ _ _ → lag (proj₁ (cov pe)) has , bd) (voc pe (defer-row sc l ad ok)) cl (proj₁ wi)
  where
    sc = scopeOf c
    past : ∀ {y e′} → pendRows (full sc) (defer l) q y e′ → q ≺ y
    past = pend-past sc (defer l) ad ok
    has : ∀ {y e′} → E y e′ → Owes C y → y ≺ q → y ∈ proj₁ (cov pe)
    has x _ yq with proj₂ (cov pe) x
    ... | inj₁ r = ⊥-elim (≺-irrefl {q} (≺-trans {q} {_} {q} (past r) yq))
    ... | inj₂ i = i
    bd : ∀ {y e′} → Due C E y e′ → q ≼ y
    bd {y} (x , v , _) = ≺→≼ {q} {y} (past (proj₁ (from (alike pe) (x , v))))
    go : ∀ {w e′} → w ∈ [ q ] → E w e′ → Visible e′ → ⊥
    go (here refl) r v = ≺-irrefl {q} (past (proj₁ (from (alike pe) (r , v))))
    cl : Clr q (q ++ [ ix 0 ]) E
    cl = clr λ {w} r v qw wy → go (zs-btw {q} {q ++ [ ix 0 ]} {w} z₁ qw wy) r v

-- A DEFER'S GUARD IS MET: short of a row a reader meets next, a defer a
-- run subscribes has a row under its guard, at or before the row met next.
defer-guard : ∀ {R} (o : PureObs [] R) {rs Γ A} {c : Ctx R Γ A} {l q p e}
            → Path (load o) rs ⟨ c , pend (defer l) q , subscribing , q ⟩
            → Meets (enter (⟦ o ⟧ []ᴬ) root) (conv rs ++ [ (p , e) ])
            → RowUnder o (q ++ [ ix 0 ]) p
defer-guard o pth m
  with Along.along (cursor o) nothing pth (Simulation.i₀ (cursor o)) (Simulation.t₀ (cursor o)) | Outer.met o pth m
... | (_ , _ , iv , _) , _ | du = defer-pend o pth du (Over.pend-view (enter (⟦ o ⟧ []ᴬ) root) iv)

postulate
  -- A LANE'S HAND-OFF PASSES ITS GUARD: a lane ending with values queued
  -- has a row under its first child, at or before the row met next.
  lanes-guard : ∀ {R} (o : PureObs [] R) {rs Γ A B} {op} {f : A → Obs Timeline Γ B} {ω d n a qu} {o′ : St Γ A} {pre post} {c : Ctx R Γ B} {s q p e}
              → Path (load o) rs ⟨ inLanes op f ω d n (a ∷ qu) o′ pre post c , s , rising cp , q ⟩
              → Meets (enter (⟦ o ⟧ []ᴬ) root) (conv rs ++ [ (p , e) ])
              → RowUnder o (q ++ [ ix 0 ]) p

-- WHERE A RISE SUBSCRIBES, ITS GUARD: an outer's value, or a lane's end
-- handing off to a queued value.
Gd : ∀ {R} → PureObs [] R → Pos → ∀ {Γ A} → Ctx R Γ A → Evᴹ A → Pos → Set
Gd o q (inOuter op f ω d n qu ls c)                 (nx a) p = RowUnder o (q ++ [ ix 0 ]) p
Gd o q (inLanes op f ω d n (a ∷ qu) o′ pre post c) cp     p = RowUnder o (q ++ [ ix 0 ]) p
Gd o q _                                            _      p = ⊤

gd : ∀ {R} (o : PureObs [] R) {rs Γ A} {c : Ctx R Γ A} {s ε q p e}
   → Path (load o) rs ⟨ c , s , rising ε , q ⟩ → Meets (enter (⟦ o ⟧ []ᴬ) root) (conv rs ++ [ (p , e) ])
   → Gd o q c ε p
gd o {c = top}                                   pth m = tt
gd o {c = inMap _ _}                             pth m = tt
gd o {c = inScan _ _ _}                          pth m = tt
gd o {c = inCut _ _ _}                           pth m = tt
gd o {c = inLn _ _}                              pth m = tt
gd o {c = inTake _ _ _ _}                        pth m = tt
gd o {c = inOuter _ _ _ _ _ _ _ _} {ε = nx _}    pth m = outer-guard o pth m
gd o {c = inOuter _ _ _ _ _ _ _ _} {ε = cp}      pth m = tt
gd o {c = inLanes _ _ _ _ _ [] _ _ _ _} {ε = nx _} pth m = tt
gd o {c = inLanes _ _ _ _ _ (_ ∷ _) _ _ _ _} {ε = nx _} pth m = tt
gd o {c = inLanes _ _ _ _ _ [] _ _ _ _} {ε = cp}  pth m = tt
gd o {c = inLanes _ _ _ _ _ (_ ∷ _) _ _ _ _} {ε = cp} pth m = lanes-guard o pth m
gd o {c = inSrc _ _ _}                           pth m = tt
gd o {c = inBody _ _ _}                          pth m = tt
