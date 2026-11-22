{-# OPTIONS --guardedness #-}

-- THE READER SHOWS EACH SOURCE ROW IT IS SUBSCRIBED BEFORE.  A value or
-- the end is read forward: annotated below itself (`src-ann`,
-- `src-ann-end`), the annotation's run to it read by the hot past the
-- subscribe (`late-in`), scanned and flattened, where the value is its
-- lane's emit and the end the reader's.
--
-- A silent row is read upward instead, each layer's row reaching few: the
-- source's few rows reach the annotation's, the annotation's the hot's and
-- the scan's.  The merge's step reaches the rows before it only through
-- the reader's own few rows there, which its one caller holds below a
-- position the row's column misses; the raw merge shows its hangs, so
-- each of its rows before the step is the reader's (`few-join`).
module simultaneous.HeldShow where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; [_]; _++_)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ʳ; ∈-++⁺ˡ; ∈-++⁻)
open import Data.List.Properties using (++-assoc; map-++)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using ([_,_]′)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
import Relation.Nullary as Nl

open import denotation.Position using (Pos; Path; ix; last; sub; _⊕_; _≟ᵖ_; root)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Den; Ev; out; end; skip; pin; enter; hot; Proper; Silent; hush; held; module Merge; module Scan; _≺_; _≼_; Few; Reach; Rejoin; LaneOf)
  renaming (ended to r-ended; late to r-late; shown to r-shown; heard to r-heard)
open import denotation.Read using (Run; []; _∷_; Visible; loud)
open import denotation.Laws.Worlds using (InvAt; Shows; hot-shows; ⊕-assoc; ⊑-≼)
open import denotation.Laws.Shows using (ShowsK; k-shows; shows-k; sk-few; few-via; few-reach; ∈-stable)
open import denotation.Laws.ShowsJoin using (module Fanned)
open import denotation.Laws.ShowsOps using (sk-scan)
open import denotation.Laws.Lift using (few-lift)
open import denotation.Laws.Rejoined using (row-reach)
open import denotation.Laws.Modulus using (≼-split; ≺-≼-≺; ≺-trans; ≺-ext; ≺→≼; entered-few; entered-reach)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Relations using (Met)
open import simultaneous.HeldBase using (Bound; Ann; Gap)
open import simultaneous.HeldComb using (ev)
open import simultaneous.HeldRead using (RD; Rl; Src; Rl-trans; pre-noend; JS; module AnnConn; conn-end; Cn)
open import simultaneous.HeldMap using (mapEv)
open import simultaneous.CombSent using (assoc³)
open import simultaneous.Layers using (module ScanLayer; scanRows; run-row; run-++; cursor-snoc; pinby-vis)
open import simultaneous.Project using (run-prefix)
open import simultaneous.FlatLayer using (ofVals; module Each₂)
open import simultaneous.HeldBack using (NoEnd; ann-last; ann-run; cut; mvh; scan-++; scan-noend; late-in; src-ann; src-ann-end; module AnnRun; module AnnVals)
open import simultaneous.HeldReadBack using (module Back)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; Routes; annotate; joinStep; joins)

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
  e-after (Merge.lane {q} {a} x _ L _ _ , _) = ≺-≼-≺ {p} {q} (s-after x) (O.lane-≼ {q} {a} (proj₁ L))
  e-after (Merge.lend {q} {a} x _ L _ _ _ , _) = ≺-≼-≺ {p} {q} (s-after x) (O.lane-≼ {q} {a} (proj₁ L))
  e-after (Merge.lpass {q} {a} x _ L _ _ _ , _) = ≺-≼-≺ {p} {q} (s-after x) (O.lane-≼ {q} {a} (proj₁ L))
  e-after (Merge.hand _ _ _ _ () , _)
  e-after (Merge.left {q} {a} x _ L _ _ , _) = ≺-≼-≺ {p} {q} (s-after x) (O.lane-≼ {q} {a} (proj₁ L))
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
  emit-in (true , _)  r x Y = ∈-++⁺ˡ (∈-++⁺ʳ (ofVals (((Y ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) 0 (joins r x)) (here refl))
  emit-in (false , _) r x Y = here refl

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

  -- THE READER'S MERGE, RAW, SHOWS ITS HANGS: each lane lists its rows.
  open Each₂ (Back.f₂ b p ng) (Back.g₂ b p ng) using (Inner; lall₂; lall-in₂)

  o-func : ∀ {q a a′} → enter Sc p q (out a) → enter Sc p q (out a′) → a ≡ a′
  o-func x x′ = cong unOut (SO.sc-fu x x′)
    where
      unOut : Ev (JS X) → JS X
      unOut (out a) = a
      unOut _       = z

  lane-past : ∀ {q a k e} → enter Sc p q (out a) → ⊤ → LaneOf Inner q a k e → q ≺ k
  lane-past {q} {k = k} _ _ (_ , lt) = ≺-trans {q} {q ⊕ [ ix 1 ]} {k} (≺-ext q []) lt

  lane-reach : ∀ {q a k e} → enter Sc p q (out a) → ⊤ → LaneOf Inner q a k e → Reach (LaneOf Inner q a) k e
  lane-reach {q} {a} _ _ (y , _) = proj₁ r , λ y′ lt dp → proj₂ r (proj₁ y′) lt dp
    where r = entered-reach (Inner a) (q ⊕ [ ix 1 ]) y

  lane-sk : ∀ {n q a} → enter Sc p q (out a) → ⊤ → ShowsK n (LaneOf Inner q a)
  lane-sk {q = q} {a} _ _ = sk-few λ _ → lall₂ a (q ⊕ [ ix 1 ]) , λ y′ _ → lall-in₂ a (q ⊕ [ ix 1 ]) (proj₁ y′)

  sh-join : Shows O.M.JoinT
  sh-join = k-shows λ n → Fanned.sk-join {n = n} (LaneOf Inner) (enter Sc p) (λ _ → ⊤) (λ _ _ → ⊥) (λ _ → ⊥) (λ _ _ → ⊥)
    (λ ()) (λ ()) (λ ()) o-func lane-past lane-reach (sk-scan joinStep z D p (shows-k (hot-shows (Proper A) p))) lane-sk

  -- Where the reader has few rows, so has its merge.
  few-join : ∀ {Y} → Few O.E Y → Few O.M.JoinT Y
  few-join {Y} (ks , h) = ks , λ {k} x lt → ∈-stable λ ¬i → few-lift sh-join (ks , h) x (≺→≼ {k} {Y} lt) λ t → ¬i (h t lt)

  -- A SILENT ANNOTATED ROW PAST THE SUBSCRIBE is the hot's, scanned, then
  -- the merge's step, wherever the reader has few rows before it.
  silent-row : ∀ {w} → p ≺ w → A w skip → (∀ {c} → A c end → w ≼ c) → Few O.E (w ⊕ [ sub p ]) → O.E (w ⊕ [ sub p ]) skip
  silent-row {w} pw aw pr F = O.M.step sc , few-reach {e = skip} (few-join F)
    where
      fA : Few A w
      fA = entered-few (ev (Bound.m b) (annotate (Bound.src b)) (Bound.env b)) (Bound.at b ⊕ [ ix 1 ]) (λ {k′} {e′} → tt) aw

      dr : enter D p (w ⊕ [ sub p ]) skip
      dr = r-shown (aw , pr) tt pw , row-reach LA (aw , pr) (proj₁ fA , λ x lt → proj₂ fA (proj₁ x) lt) pw {skip}

      sc : enter Sc p (w ⊕ [ sub p ]) skip
      sc = ScanLayer.toSc joinStep z D p fuD (Scan.sstep dr)

-- Back to the binder's reader.
to-rd : ∀ {X} {d : Den (AIE X)} {cs} (b : Bound d cs) p (ng : Nl.¬ Gap b p) {y e} → Back.O.E b p ng y e → enter (RD d) p y e
to-rd b p ng {y} {e} r = subst (λ D′ → enter (RD D′) p y e) (sym (Bound.is b)) r

-- A SILENT SOURCE ROW IS ANNOTATED SILENT below itself: the hot's, the
-- closed body's, the connect's, scanned.
module AnnSilent {X} {d : Den (AIE X)} {cs} (b : Bound d cs) where
  open AnnRun b using (a₁; eqA)
  module V = AnnVals b
  module AC = AnnConn b

  σ-src : ∀ {y e} → AC.σ y e → Σ _ (Src b y)
  σ-src y = _ , proj₁ (proj₂ (AC.MR.unmap y))

  end-of : ∀ {c} → Σ (Ev (IE X)) (λ e → Src b c e × end ≡ mapEv just e) → Src b c end
  end-of (end , sc , refl) = sc
  end-of (out _ , _ , ())
  end-of (skip , _ , ())
  end-of (pin _ , _ , ())

  up : ∀ {k e} → Src b k e → Few (Src b) k → (∀ {c} → Src b c end → k ≼ c)
     → (AC.σ k (mapEv just e) → (∀ {c} → AC.σ c end → k ≼ c) → AC.sb ≺ k → Rejoin AC.sb (Proper AC.σ) (AC.HR.shift k) skip)
     → Ann b (k ⊕ [ sub AC.sb ]) skip
  up {k} sk fk lv rj = subst (λ D′ → enter D′ a₁ (k ⊕ [ sub AC.sb ]) skip) (sym eqA) (V.MS.lift (V.SL.toSc (Scan.sstep cw)))
    where
      σk = AC.MR.lift sk

      fσ : Few AC.σ k
      fσ = few-via (λ y _ ¬z → ¬z (σ-src y)) fk

      pr : ∀ {c} → AC.σ c end → k ≼ c
      pr y = lv (end-of (AC.MR.unmap y))

      rd : AC.HR.Rd (AC.HR.shift k) skip
      rd = rj σk pr (≺-trans {AC.sb} {AC.r₁} {k} AC.sb≺r (AC.aft σk)) , AC.HR.reach-from (proj₁ fσ) (proj₂ fσ) σk {skip}

      cw : Cn b (k ⊕ [ sub AC.sb ]) skip
      cw = V.body-cnᶠ σk fσ ([ sub AC.sb ] , refl) (AC.CT.lift (AC.CT.src (V.rd-r rd) (λ ())))

  show-silent : ∀ {k e} → Src b k e → Silent e → Few (Src b) k → (∀ {c} → Src b c end → k ≼ c) → Ann b (k ⊕ [ sub AC.sb ]) skip
  show-silent sk hush fk lv = up sk fk lv λ σk pr af → r-shown (σk , pr) tt af
  show-silent sk held fk lv = up sk fk lv λ σk pr af → r-heard (σk , pr) af

-- A SILENT SOURCE ROW PAST THE SUBSCRIBE is read, where the reader has few
-- rows below it: annotated silent below itself, the merge's step there.
read-silent : ∀ {X} {d : Den (AIE X)} {cs} (b : Bound d cs) p (ng : Nl.¬ Gap b p)
            → ∀ {k e} → p ≺ k → Src b k e → Silent e → Few (Src b) k → (∀ {c} → Src b c end → k ≼ c)
            → (∀ {y} → Rl y k → Few (enter (RD d) p) y)
            → Σ Path λ zs → Σ (Ev (IE X)) λ e′ → enter (RD d) p (k ⊕ zs) e′
read-silent {X} {d} b p ng {k} {e} pk sk sl fk lv fr =
  (sub sb ∷ sub p ∷ []) , skip , subst (λ y → enter (RD d) p y skip) (⊕-assoc k [ sub sb ] [ sub p ]) (to-rd b p ng (S.silent-row pw aw pr F))
  where
    module S = Show b p ng

    sb = AnnConn.sb b
    w = k ⊕ [ sub sb ]

    pw : p ≺ w
    pw = ≺-trans {p} {k} {w} pk (≺-ext k [])

    aw : Ann b w skip
    aw = AnnSilent.show-silent b sk sl fk lv

    F : Few (Back.O.E b p ng) (w ⊕ [ sub p ])
    F = subst (λ D′ → Few (enter (RD D′) p) (w ⊕ [ sub p ])) (Bound.is b) (fr (Rl-trans ([ sub p ] , refl) ([ sub sb ] , refl)))

    silent-end : ∀ {e′ : Ev (IE X)} → Silent e′ → e′ ≡ end → ⊥
    silent-end hush ()
    silent-end held ()

    via : ∀ {c} → Σ Pos (λ w′ → Rl c w′ × Src b w′ end) → w ≼ c
    via (w′ , (zs , refl) , se) = [ lt , eq ]′ (≼-split {k} {w′} (lv se))
      where
        lt : k ≺ w′ → w ≼ (w′ ⊕ zs)
        lt kw = ≺→≼ {w} {w′ ⊕ zs} (≺-≼-≺ {w} {w′} {w′ ⊕ zs}
                  (AnnConn.HR.past b [ sub sb ] (AnnConn.MR.lift b sk) (AnnConn.MR.lift b se) kw) (⊑-≼ {w′} {w′ ⊕ zs} (zs , refl)))

        eq : k ≡ w′ → w ≼ (w′ ⊕ zs)
        eq refl = ⊥-elim (silent-end sl (InvAt.func (Back.IS b p ng) sk se))

    pr : ∀ {c} → Ann b c end → w ≼ c
    pr ce = via (conn-end b (proj₁ (proj₂ (proj₂ (AnnVals.cn-end b ce)))))

read-shows : ∀ {X} {d : Den (AIE X)} {cs} (b : Bound d cs) p → Nl.¬ Gap b p
           → ∀ {q e₀ k e} → enter (RD d) p q e₀ → q ≺ k → Src b k e → Few (Src b) k → (∀ {c} → Src b c end → k ≼ c)
           → (Silent e → ∀ {y} → Rl y k → Few (enter (RD d) p) y)
           → Σ Path λ zs → Σ (Ev (IE X)) λ e′ → enter (RD d) p (k ⊕ zs) e′ × (Visible e → Visible e′)
read-shows {X} {d} b p ng {q} {e₀} {k} {e} rq qk sk fk lv fz = go e sk fz
  where
    module S = Show b p ng

    pk : p ≺ k
    pk = ≺-trans {p} {q} {k} (S.e-after (subst (λ D′ → enter (RD D′) p q e₀) (Bound.is b) rq)) qk

    sb = AnnConn.sb b
    w = k ⊕ [ sub sb ]

    pw : p ≺ w
    pw = ≺-trans {p} {k} {w} pk (≺-ext k [])

    pm : p ≺ ((w ⊕ [ ix 1 ]) ⊕ [ ix 0 ])
    pm = ≺-trans {p} {w} {(w ⊕ [ ix 1 ]) ⊕ [ ix 0 ]} pw
           (≺-trans {w} {w ⊕ [ ix 1 ]} {(w ⊕ [ ix 1 ]) ⊕ [ ix 0 ]} (≺-ext w []) (≺-ext (w ⊕ [ ix 1 ]) []))

    Out : Ev (IE X) → Set
    Out e′ = Σ Path λ zs → Σ (Ev (IE X)) λ e″ → enter (RD d) p (k ⊕ zs) e″ × (Visible e′ → Visible e″)

    shown′ : ∀ {u e′ e″} → Visible e″ → Rl u k → enter (RD d) p u e″ → Out e′
    shown′ v (zs , refl) r = zs , _ , r , λ _ → v

    silent : ∀ {e′} → Silent {IE X} e′ → (Σ Path λ zs → Σ (Ev (IE X)) λ e″ → enter (RD d) p (k ⊕ zs) e″) → Out e′
    silent sl (zs , e″ , row) = zs , e″ , row , λ v → ⊥-elim (loud v sl)

    val : ∀ {x} → Σ Routes (λ r → Ann b w (out (r , just x))) → Out (out x)
    val {x} (r , aw) = shown′ {e′ = out x} tt (Back.rl-lane b p ng ([ sub sb ] , refl)) (to-rd b p ng (S.val-row pw aw))

    fin : Σ Routes (λ r → Ann b ((w ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) (out (r , nothing)) × Ann b ((w ⊕ [ ix 1 ]) ⊕ [ last ]) end) → Out end
    fin (r , am , ae) = shown′ {e′ = end} tt (Rl-trans ([ sub p ] , refl) (_ , assoc³ k (sub sb) (ix 1) last))
                          (to-rd b p ng (S.end-row pm am ae (AnnConn.CT.m≺f b w)))

    go : ∀ e′ → Src b k e′ → (Silent e′ → ∀ {y} → Rl y k → Few (enter (RD d) p) y) → Out e′
    go (out x) sk′ _   = val (src-ann b sk′)
    go end     sk′ _   = fin (src-ann-end b sk′)
    go skip    sk′ fz′ = silent {e′ = skip} hush (read-silent b p ng pk sk′ hush fk lv (fz′ hush))
    go (pin r) sk′ fz′ = silent {e′ = pin r} held (read-silent b p ng pk sk′ held fk lv (fz′ held))
