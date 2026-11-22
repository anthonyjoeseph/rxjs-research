{-# OPTIONS --guardedness #-}

-- THE READER SHOWS EACH SOURCE ROW IT IS SUBSCRIBED BEFORE.  A value or
-- the end is read forward: annotated below itself (`src-ann`,
-- `src-ann-end`), the annotation's run to it read by the hot past the
-- subscribe (`late-in`), scanned and flattened, where the value is its
-- lane's emit and the end the reader's.
module simultaneous.HeldShow where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ʳ; ∈-++⁺ˡ; ∈-++⁻)
open import Data.List.Properties using (++-assoc; map-++)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
import Relation.Nullary as Nl

open import denotation.Position using (Pos; Path; ix; last; sub; _⊕_; _≟ᵖ_; root)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Den; Ev; out; end; skip; pin; enter; hot; Proper; Silent; hush; held; module Merge; _≺_; _≼_; Few)
  renaming (ended to r-ended; late to r-late; shown to r-shown; heard to r-heard)
open import denotation.Read using (Run; []; _∷_; Visible; loud)
open import denotation.Laws.Worlds using (InvAt)
open import denotation.Laws.Modulus using (≼-split; ≺-irrefl; ≺-≼-≺; ≺-trans; ≺-ext; entered-few)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Relations using (Met)
open import simultaneous.HeldBase using (Bound; Ann; Gap)
open import simultaneous.HeldComb using (ev)
open import simultaneous.HeldRead using (RD; Rl; Src; Rl-trans; pre-noend; JS; module AnnConn)
open import simultaneous.CombSent using (assoc³)
open import simultaneous.Layers using (module ScanLayer; scanRows; run-row; run-++; cursor-snoc; pinby-vis)
open import simultaneous.Project using (run-prefix)
open import simultaneous.FlatLayer using (ofVals)
open import simultaneous.HeldBack using (NoEnd; ann-last; ann-run; cut; mvh; scan-++; scan-noend; late-in; src-ann; src-ann-end)
open import simultaneous.HeldReadBack using (module Back)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; Routes; annotate; joinStep)

module Show {X} {d : Den (AIE X)} {cs} (b : Bound d cs) (p : Pos) (ng : Nl.¬ Gap b p) where
  open Back b p ng using (A; D; z; Sc; IA; LA; fuD; module SO; module O; lr; rl-lane; flat-snoc)

  -- The hot's rows lie past the subscribe.
  d-after : ∀ {y e} → enter D p y e → p ≺ y
  d-after (r-shown {q} _ _ pq , _) = ≺-trans {p} {q} {q ⊕ [ sub p ]} pq (≺-ext q [])
  d-after (r-heard {q} _ pq , _)   = ≺-trans {p} {q} {q ⊕ [ sub p ]} pq (≺-ext q [])
  d-after (r-ended {c} _ pc , _)   = ≺-trans {p} {c} {c ⊕ [ sub p ]} pc (≺-ext c [])
  d-after (r-late _ _ , _)         = ≺-ext p []

  s-after : ∀ {y e} → enter Sc p y e → p ≺ y
  s-after s = d-after (proj₂ (SO.bk s))

  -- THE READER'S ROWS LIE PAST THE SUBSCRIBE: each is its scan's, or under one.
  e-after : ∀ {y e} → O.E y e → p ≺ y
  e-after (Merge.val {q} x , _)              = ≺-trans {p} {q} {q ⊕ [ ix 0 ]} (s-after x) (≺-ext q [])
  e-after (Merge.step x , _)                 = s-after x
  e-after (Merge.opin x , _)                 = s-after x
  e-after (Merge.oend x _ , _)               = s-after x
  e-after (Merge.opass x _ , _)              = s-after x
  e-after (Merge.lane {q} x _ L _ _ , _)     = ≺-≼-≺ {p} {q} (s-after x) (O.lane-≼ (proj₁ L))
  e-after (Merge.lend {q} x _ L _ _ _ , _)   = ≺-≼-≺ {p} {q} (s-after x) (O.lane-≼ (proj₁ L))
  e-after (Merge.lpass {q} x _ L _ _ _ , _)  = ≺-≼-≺ {p} {q} (s-after x) (O.lane-≼ (proj₁ L))
  e-after (Merge.hand _ _ _ _ () , _)
  e-after (Merge.left {q} x _ L _ _ , _)     = ≺-≼-≺ {p} {q} (s-after x) (O.lane-≼ (proj₁ L))
  e-after (Merge.run () _ , _)
  e-after (Merge.rend () _ _ , _)
  e-after (Merge.rpass () _ _ , _)
  e-after (Merge.rhand () _ , _)

  -- A row of the scan's last block, past rows that never end, is the flat run's.
  flat-mem : ∀ xs {ys k e} → NoEnd xs → (k , e) ∈ O.flatRows ys → (k , e) ∈ O.flatRows (xs ++ ys)
  flat-mem []                  _  i = i
  flat-mem ((y , out st) ∷ xs) ne i = ∈-++⁺ʳ (lr st (y ⊕ [ ix 1 ])) (flat-mem xs (λ j → ne (there j)) i)
  flat-mem ((y , end) ∷ xs)    ne _ = ⊥-elim (ne (here refl))
  flat-mem ((y , skip) ∷ xs)   ne i = flat-mem xs (λ j → ne (there j)) i
  flat-mem ((y , pin _) ∷ xs)  ne i = flat-mem xs (λ j → ne (there j)) i

  -- A value's block holds its emit.
  emit-in : ∀ (st₀ : JS X) r x Y → ((((Y ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ] , out x) ∈ O.flatRows ((Y , out (joinStep st₀ (r , just x))) ∷ [])
  emit-in (true , _)  r x Y = ∈-++⁺ˡ (∈-++⁺ʳ (ofVals (((Y ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) 0 _) (here refl))
  emit-in (false , _) r x Y = ∈-++⁺ˡ (∈-++⁺ʳ (ofVals (((Y ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) 0 _) (here refl))

  -- The annotation's run past the subscribe, read by the hot.
  hot-run : ∀ {ra₁ ra₂ q a} → (∀ {y e} → (y , e) ∈ ra₁ → y ≼ p) → (∀ {y e} → (y , e) ∈ ra₂ → p ≺ y) → p ≺ q
          → Met A ((ra₁ ++ ra₂) ++ [ (q , out a) ]) → Met (enter D p) (L.map (mvh p) ra₂ ++ [ (q ⊕ [ sub p ] , out a) ])
  hot-run {ra₁} {ra₂} {q} {a} b₁ b₂ pq mA =
    subst (Met (enter D p)) (map-++ (mvh p) ra₂ [ (q , out a) ])
      (late-in LA p (subst (Met A) (++-assoc ra₁ ra₂ [ (q , out a) ]) mA) b₁ (λ i → [ b₂ , last-q ]′ (∈-++⁻ ra₂ i)))
    where
      last-q : ∀ {y e} → (y , e) ∈ [ (q , out a) ] → p ≺ y
      last-q (here refl) = pq
      last-q (there ())

  -- The hot's run, scanned.
  scan-run : ∀ {H} → Met (enter D p) H → Met (enter Sc p) (scanRows joinStep z H)
  scan-run mD = subst (Met (enter Sc p)) (proj₂ (proj₂ (proj₂ (proj₂ ig)))) (proj₁ (proj₂ ig))
    where
      ig = ScanLayer.in-go joinStep z D p fuD ScanLayer.none mD

  -- AN ANNOTATED VALUE PAST THE SUBSCRIBE is its lane's emit.
  val-row : ∀ {q r x} → p ≺ q → A q (out (r , just x)) → O.E (((((q ⊕ [ sub p ]) ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) (out x)
  val-row {q} {r} {x} pq aq = go (ann-run b aq)
    where
      Y = q ⊕ [ sub p ]

      go : (Σ _ λ ra → Met A (ra ++ [ (q , out (r , just x)) ])) → O.E ((((Y ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) (out x)
      go (ra , mA) = at (cut p ra (run-prefix ra mA))
        where
          at : (Σ _ λ ra₁ → Σ _ λ ra₂ → ra ≡ ra₁ ++ ra₂ × (∀ {y e} → (y , e) ∈ ra₁ → y ≼ p) × (∀ {y e} → (y , e) ∈ ra₂ → p ≺ y))
             → O.E ((((Y ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) (out x)
          at (ra₁ , ra₂ , refl , b₁ , b₂) = proj₁ (run-row mE mem)
            where
              H = L.map (mvh p) ra₂

              mD : Met (enter D p) (H ++ [ (Y , out (r , just x)) ])
              mD = hot-run b₁ b₂ pq mA

              sp = scan-++ joinStep z H [ (Y , out (r , just x)) ] (pre-noend H mD)

              mE : Met O.E (O.flatRows (scanRows joinStep z H ++ scanRows joinStep (proj₁ sp) [ (Y , out (r , just x)) ]))
              mE = subst (λ R → Met O.E (O.flatRows R)) (proj₂ sp) (O.flat-in (scan-run mD))

              mem : ((((Y ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ] , out x)
                    ∈ O.flatRows (scanRows joinStep z H ++ scanRows joinStep (proj₁ sp) [ (Y , out (r , just x)) ])
              mem = flat-mem (scanRows joinStep z H) (scan-noend joinStep z H (pre-noend H mD)) (emit-in (proj₁ sp) r x Y)

  -- THE ANNOTATION'S NOTHING, THEN ITS END, PAST THE SUBSCRIBE: the
  -- reader ends below the end.
  end-row : ∀ {m r c} → p ≺ m → A m (out (r , nothing)) → A c end → m ≺ c → O.E (c ⊕ [ sub p ]) end
  end-row {m} {r} {c} pm am ce mc = go (ann-run b am)
    where
      xm = (m , out (r , nothing))

      least : ∀ {k′ e′} → A k′ e′ → Visible e′ → m ≺ k′ → c ≼ k′
      least {e′ = out _} ak _ mk = ⊥-elim (ann-last b am ak mk)
      least {e′ = end}   ak _ _  = λ lt → pinby-vis tt (InvAt.quiet IA ak ce lt)
      least {e′ = skip}  _ () _
      least {e′ = pin _} _ () _

      pc′ : ∀ {c′} → A c′ end → c ≼ c′
      pc′ ce′ lt = pinby-vis tt (InvAt.quiet IA ce′ ce lt)

      endrow : Run A (just m) ((c , end) ∷ [])
      endrow = (((ce , pc′) , entered-few (ev (Bound.m b) (annotate (Bound.src b)) (Bound.env b)) (Bound.at b ⊕ [ ix 1 ]) (λ {k′} {e′} → tt) ce) , tt , mc , least) ∷ []

      go : (Σ _ λ ra → Met A (ra ++ [ xm ])) → O.E (c ⊕ [ sub p ]) end
      go (ra , mA) = at (cut p ra (run-prefix ra mA))
        where
          at : (Σ _ λ ra₁ → Σ _ λ ra₂ → ra ≡ ra₁ ++ ra₂ × (∀ {y e} → (y , e) ∈ ra₁ → y ≼ p) × (∀ {y e} → (y , e) ∈ ra₂ → p ≺ y))
             → O.E (c ⊕ [ sub p ]) end
          at (ra₁ , ra₂ , refl , b₁ , b₂) = proj₁ (run-row mE (∈-++⁺ʳ (O.flatRows (scanRows joinStep z H)) (here refl)))
            where
              H = L.map (mvh p) (ra₂ ++ [ xm ])

              mA⁺ : Met A (ra₁ ++ ((ra₂ ++ [ xm ]) ++ [ (c , end) ]))
              mA⁺ = subst (Met A) (trans (cong (_++ [ (c , end) ]) (++-assoc ra₁ ra₂ [ xm ])) (++-assoc ra₁ (ra₂ ++ [ xm ]) [ (c , end) ]))
                      (run-++ mA (subst (λ c′ → Run A c′ ((c , end) ∷ [])) (sym (cursor-snoc nothing (ra₁ ++ ra₂))) endrow))

              one : ∀ {q′} → p ≺ q′ → ∀ {y e′} {x : Ev (AIE X)} → (y , e′) ∈ [ (q′ , x) ] → p ≺ y
              one pq (here refl) = pq
              one pq (there ())

              past : ∀ {y e′} → (y , e′) ∈ (ra₂ ++ [ xm ]) ++ [ (c , end) ] → p ≺ y
              past i = [ (λ j → [ b₂ , one pm ]′ (∈-++⁻ ra₂ j)) , one (≺-trans {p} {m} {c} pm mc) ]′ (∈-++⁻ (ra₂ ++ [ xm ]) i)

              mD : Met (enter D p) (H ++ [ (c ⊕ [ sub p ] , end) ])
              mD = subst (Met (enter D p)) (map-++ (mvh p) (ra₂ ++ [ xm ]) [ (c , end) ]) (late-in LA p mA⁺ b₁ past)

              mE : Met O.E (O.flatRows (scanRows joinStep z H) ++ (c ⊕ [ sub p ] , end) ∷ [])
              mE = subst (Met O.E) (flat-snoc H mD) (O.flat-in (scan-run mD))

-- Back to the binder's reader.
to-rd : ∀ {X} {d : Den (AIE X)} {cs} (b : Bound d cs) p (ng : Nl.¬ Gap b p) {y e} → Back.O.E b p ng y e → enter (RD d) p y e
to-rd b p ng {y} {e} r = subst (λ D′ → enter (RD D′) p y e) (sym (Bound.is b)) r

-- THE READER SHOWS A SILENT SOURCE ROW past its subscribe: silent at
-- each layer, the annotation's connect, its hot, its scan and the merge's
-- step.  Untried: each layer's row reaches few rows, the source's being
-- few before it.
postulate
  read-silent : ∀ {X} {d : Den (AIE X)} {cs} (b : Bound d cs) p → Nl.¬ Gap b p
              → ∀ {k e} → p ≺ k → Src b k e → Silent e → Few (Src b) k → (∀ {c} → Src b c end → k ≼ c)
              → Σ Path λ zs → Σ (Ev (IE X)) λ e′ → enter (RD d) p (k ⊕ zs) e′

read-shows : ∀ {X} {d : Den (AIE X)} {cs} (b : Bound d cs) p → Nl.¬ Gap b p
           → ∀ {q e₀ k e} → enter (RD d) p q e₀ → q ≺ k → Src b k e → Few (Src b) k → (∀ {c} → Src b c end → k ≼ c)
           → Σ Path λ zs → Σ (Ev (IE X)) λ e′ → enter (RD d) p (k ⊕ zs) e′ × (Visible e → Visible e′)
read-shows {X} {d} b p ng {q} {e₀} {k} {e} rq qk sk fk lv = go e sk
  where
    module S = Show b p ng

    pk : p ≺ k
    pk = ≺-trans {p} {q} {k} (S.e-after (subst (λ D′ → enter (RD D′) p q e₀) (Bound.is b) rq)) qk

    sb = AnnConn.sb b
    w = k ⊕ [ sub sb ]

    pw : p ≺ w
    pw = ≺-trans {p} {k} {w} pk (≺-ext k [])

    at : ∀ {u e′} → Rl u k → enter (RD d) p u e′ → Σ Path λ zs → enter (RD d) p (k ⊕ zs) e′
    at (zs , refl) r = zs , r

    pm : p ≺ ((w ⊕ [ ix 1 ]) ⊕ [ ix 0 ])
    pm = ≺-trans {p} {w} {(w ⊕ [ ix 1 ]) ⊕ [ ix 0 ]} pw
           (≺-trans {w} {w ⊕ [ ix 1 ]} {(w ⊕ [ ix 1 ]) ⊕ [ ix 0 ]} (≺-ext w []) (≺-ext (w ⊕ [ ix 1 ]) []))

    silent : ∀ {e′} → Silent {IE X} e′ → (Σ Path λ zs → Σ (Ev (IE X)) λ e″ → enter (RD d) p (k ⊕ zs) e″) → Σ Path λ zs → Σ (Ev (IE X)) λ e″ → enter (RD d) p (k ⊕ zs) e″ × (Visible {IE X} e′ → Visible e″)
    silent sl (zs , e″ , row) = zs , e″ , row , λ v → ⊥-elim (loud v sl)

    go : ∀ e′ → Src b k e′ → Σ Path λ zs → Σ (Ev (IE X)) λ e″ → enter (RD d) p (k ⊕ zs) e″ × (Visible e′ → Visible e″)
    go (out x) sk′ with src-ann b sk′
    ... | r , aw with at (Back.rl-lane b p ng ([ sub sb ] , refl)) (to-rd b p ng (S.val-row pw aw))
    ...   | zs , row = zs , out x , row , λ _ → tt
    go end sk′ with src-ann-end b sk′
    ... | r , am , ae with at (Rl-trans ([ sub p ] , refl) (_ , assoc³ k (sub sb) (ix 1) last))
                              (to-rd b p ng (S.end-row pm am ae (AnnConn.CT.m≺f b w)))
    ...   | zs , row = zs , end , row , λ _ → tt
    go skip    sk′ = silent hush (read-silent b p ng pk sk′ hush fk lv)
    go (pin r) sk′ = silent held (read-silent b p ng pk sk′ held fk lv)
