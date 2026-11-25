-- A CONNECT IN SCOPE REPORTING A ROUTE HELD IDLES IN THAT ROUTE'S
-- INSTANT: the tracker's report is its binder's annotated row, the routes
-- its source held through a row met, and that source idles at the scan's
-- next row, every source row between shown by the same tracker.

module simultaneous.TrackHeld where

open import Data.List using (List; _∷_; _++_; [_])
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (_∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
import Relation.Nullary as Nl

open import Tree using (Obs; FlatOp)
open import denotation.Position using (Pos; Path; root; _≟ᵖ_; ix; sub; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (hot; enter; DenEnv; Ev; out; end; Few; Silent; _≺_; _≼_)
open import denotation.Read using (Visible; After; cursor)
open import denotation.Laws.Modulus using (≺-irrefl; ≺-≼-≺; ≺-trans; ≼-or-≻; ≼-≺-≺)
open import denotation.Laws.Worlds using (Hots; GoodEnv; Ok; Lawful; InvAt; ⊑-≼; ⊕-assoc)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Relations using (Met)
open import simultaneous.Routed using (Held; Early; Placed; cnt; nameOf)
open import simultaneous.HeldComb using (ev)
open import simultaneous.HeldBase using (Ann; EnvHeld; module FlatHots; IH; Fresh)
open import simultaneous.HeldRead using (Rl; Src; ann-row; ann-just; ann-none; AnnEv)
open import simultaneous.LiveRuns using (pre-noend)
open import simultaneous.HeldJoin using (cnt-++)
open import simultaneous.HeldScanned using (run-before)
open import simultaneous.HeldReader using (run-head)
open import simultaneous.HeldSrc using (module CombSrc)
open import simultaneous.IdleAt using (module SrcLaws; module IdleAt)
open import simultaneous.Layers using (run-tail; cursor-snoc; cursor-in; run-has; run-row)
open import simultaneous.Project using (run-prefix)
open import simultaneous.ScanLive using (LastIn)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; Routes; count; Input) renaming (past to routes-past)

-- Where a binder stands among the binders: the index its tracker reports.
pos : ∀ {X : Set} {Γ : List Set} → X ∈ Γ → ℕ
pos (here _)  = zero
pos (there j) = suc (pos j)

module CombTrack (m : Maybe ℕ) {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (op : FlatOp) (f : A → Obs Timeline Γ B)
               (s : Obs Timeline Γ A) (env : DenEnv Δ) (cs : List Pos) (gd : GoodEnv env) (eh : EnvHeld ρ env cs)
               (hf : ∀ a {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ′) → IH m ρ′ (f a))
               (p : Pos) (ok : Ok (Hots env) p) (fr : Fresh eh p) (ep : Early p)
               (H₁ : Held (enter (ev m (FlatHots.trig m ρ op f s env p) (FlatHots.env₀ m ρ op f s env p)) (FlatHots.c m ρ op f s env p ⊕ [ ix 1 ]))
                          ((FlatHots.c m ρ op f s env p ⊕ [ ix 1 ]) ∷ p ∷ cs))
               (tp : Placed (Fresh eh) (FlatHots.σ₁ m ρ op f s env p))
               (L₁ : Lawful (FlatHots.σ₁ m ρ op f s env p)) (L₂ : Lawful (FlatHots.σ₂ m ρ op f s env p))
               (L₃ : Lawful (FlatHots.σ₃ m ρ op f s env p))
               (ok₁ : Ok (Hots (hot (FlatHots.σ₁ m ρ op f s env p) ∷ FlatHots.env₀ m ρ op f s env p)) (FlatHots.p₀ m ρ op f s env p))
               (ok₂ : Ok (Hots (hot (FlatHots.σ₂ m ρ op f s env p) ∷ hot (FlatHots.σ₁ m ρ op f s env p) ∷ FlatHots.env₀ m ρ op f s env p))
                         (FlatHots.p₀₀ m ρ op f s env p))
               (ok₃ : Ok (Hots (FlatHots.env′ m ρ op f s env p)) (FlatHots.P m ρ op f s env p))
               (ep₃ : Early (FlatHots.P m ρ op f s env p)) where
  open FlatHots m ρ op f s env p
  open CombSrc m ρ op f s env cs gd eh hf p ok fr ep H₁ tp L₁ L₂ L₃ ok₁ ok₂ ok₃ ep₃ using (I-M)

  -- A tracker's row in the scan's source.
  Tr : ℕ → Routes → Ev (Maybe (Input B))
  Tr i r = out (just (inj₂ (i , r)))

  -- WHAT A TRACKER REPORTS: its binder's annotated row, one `sub` below it,
  -- the routes held past that row.
  record Report (y : Pos) (i : ℕ) (r : Routes) : Set₁ where
    field
      {X}  : Set
      j    : X ∈ Γ
      idx  : pos j ≡ i
      ya   : Pos
      a    : AIE X
      ann  : Ann (EnvHeld.bound eh j) ya (out a)
      held : r ≡ routes-past a
      J    : Pos
      sits : y ≡ ya ⊕ [ sub J ]

  postulate
    -- A tracker's row is its binder's annotated row, re-keyed.
    track-row   : ∀ {y i r} → M y (Tr i r) → Report y i r
    -- PAST THE ROW REPORTED, THE SAME TRACKER SHOWS EACH SOURCE ROW the
    -- binder's source has few rows before and that lies before a visible
    -- row of the scan's source, not above it.
    track-shows : ∀ {y i r} (R : Report y i r) {pre w e} → Met (Src (EnvHeld.bound eh (Report.j R))) (pre ++ [ (w , e) ])
                → Rl (Report.ya R) w → ∀ {k eₖ} → Src (EnvHeld.bound eh (Report.j R)) k eₖ → w ≺ k
                → Few (Src (EnvHeld.bound eh (Report.j R))) k → (∀ {c₁} → Src (EnvHeld.bound eh (Report.j R)) c₁ end → k ≼ c₁)
                → ∀ {q eq} → M q eq → Visible eq → k ≺ q → (Σ Path (λ ys → q ≡ k ⊕ ys) → ⊥)
                → (Silent eₖ → ∀ {y′} → Rl y′ k → Few M y′)
                → Nl.¬ Nl.¬ (Σ Path λ zs → Σ (Ev (Maybe (Input B))) λ e′ → M (k ⊕ zs) e′ × (Visible eₖ → Visible e′)
                             × (Visible e′ → Σ Routes λ r′ → e′ ≡ Tr i r′))

  -- THE REPORT, AT THE SCAN'S NEXT ROW: the last report of tracker `i`
  -- before the row `q` met past `rx₁`.
  module At rx₁ {q e rx₂} (mt : Met M (rx₁ ++ (q , e) ∷ rx₂)) (v : Visible e) {i r} (li : LastIn i r rx₁) where

    xs = proj₁ li
    ys = proj₁ (proj₂ li)
    y  = proj₁ (proj₂ (proj₂ li))

    rx≡ : rx₁ ≡ xs ++ (y , Tr i r) ∷ ys
    rx≡ = proj₁ (proj₂ (proj₂ (proj₂ li)))

    m₁ : Met M rx₁
    m₁ = run-prefix rx₁ mt

    m₁′ : Met M (xs ++ (y , Tr i r) ∷ ys)
    m₁′ = subst (Met M) rx≡ m₁

    y∈ : (y , Tr i r) ∈ rx₁
    y∈ = subst ((y , Tr i r) ∈_) (sym rx≡) (∈-++⁺ʳ xs (here refl))

    -- The tracker's later rows lie past every row met before `q`.
    past-last : ∀ {z e′} → M z e′ → Σ Routes (λ r′ → e′ ≡ Tr i r′) → y ≺ z → After (cursor nothing rx₁) z
    past-last {z} mz (r′ , refl) yz = at (cursor nothing rx₁) refl
      where
        absurd : (z , Tr i r′) ∈ rx₁ → ⊥
        absurd k with ∈-++⁻ xs (subst ((z , Tr i r′) ∈_) rx≡ k)
        ... | inj₁ kx        = ≺-irrefl {y} (≺-trans {y} {z} {y} yz (run-before xs m₁′ kx))
        ... | inj₂ (here refl) = ≺-irrefl {y} yz
        ... | inj₂ (there ky)  = proj₂ (proj₂ (proj₂ (proj₂ li))) ky

        at : ∀ c → cursor nothing rx₁ ≡ c → After c z
        at nothing  _  = tt
        at (just ℓ) ec with ≼-or-≻ z ℓ
        ... | inj₂ ℓz = ℓz
        ... | inj₁ zℓ with cursor-in nothing rx₁ ec
        ...   | inj₁ ()
        ...   | inj₂ (_ , ℓ∈) = ⊥-elim (absurd (run-has (InvAt.func I-M) m₁ mz tt tt zℓ ℓ∈))

    Rp : Report y i r
    Rp = track-row (proj₁ (run-row m₁ y∈))

    open Report Rp using (j; ya; a; ann; held; J; sits)

    b = EnvHeld.bound eh j

    nx = run-head (run-tail rx₁ mt)

    -- The scan's next row lies past the tracker's.
    yq : y ≺ q
    yq = run-before rx₁ mt y∈

    -- A REPORT OF A ROW MET: the source idles at `q` past it.
    module Met′ {pre w vᵥ} (srun : Met (Src b) (pre ++ [ (w , out vᵥ) ])) (zs₀ : Path) (ya≡ : ya ≡ w ⊕ zs₀) where
      open SrcLaws b using (past)

      S = pre ++ [ (w , out vᵥ) ]

      ne : ∀ {c} → (c , end) ∈ S → ⊥
      ne i′ with ∈-++⁻ pre i′
      ... | inj₁ ip = pre-noend pre srun ip
      ... | inj₂ (here ())
      ... | inj₂ (there ())

      sw : Src b w (out vᵥ)
      sw = proj₁ (run-row srun (∈-++⁺ʳ pre (here refl)))

      y≡ : y ≡ w ⊕ (zs₀ ++ [ sub J ])
      y≡ = trans sits (trans (cong (_⊕ [ sub J ]) ya≡) (⊕-assoc w zs₀ [ sub J ]))

      -- Past the reported row, below a later source row: past the tracker's row.
      y≺ : ∀ {k eₖ} zs → Src b k eₖ → w ≺ k → y ≺ (k ⊕ zs)
      y≺ {k} zs sk wk = subst (_≺ (k ⊕ zs)) (sym y≡) (≺-≼-≺ {w ⊕ (zs₀ ++ [ sub J ])} {k} {k ⊕ zs} (past (zs₀ ++ [ sub J ]) sw sk wk) (⊑-≼ {k} {k ⊕ zs} (zs , refl)))

      wq : w ≺ q
      wq = ≼-≺-≺ {w} {y} {q} (⊑-≼ {w} {y} (zs₀ ++ [ sub J ] , y≡)) yq

      shown : ∀ {k eₖ} → Src b k eₖ → w ≺ k → Few (Src b) k → (∀ {c₁} → Src b c₁ end → k ≼ c₁) → k ≺ q
            → (Σ Path (λ ys′ → q ≡ k ⊕ ys′) → ⊥) → (Silent eₖ → ∀ {y′} → Rl y′ k → Few M y′)
            → Nl.¬ Nl.¬ (Σ Path λ zs → Σ (Ev (Maybe (Input B))) λ e′ → M (k ⊕ zs) e′ × (Visible eₖ → Visible e′)
                         × (Visible e′ → After (cursor nothing rx₁) (k ⊕ zs)))
      shown {k} sk wk fk lv kq nu sf h =
        track-shows Rp srun (zs₀ , ya≡) sk wk fk lv (proj₁ (run-row mt (∈-++⁺ʳ rx₁ (here refl)))) v kq nu sf
          λ (zs , e′ , mz , vv , tr) → h (zs , e′ , mz , vv , λ v′ → past-last mz (tr v′) (y≺ zs sk wk))

      open IdleAt b srun ne (cursor-snoc nothing pre) (∈-++⁺ʳ pre (here refl)) M (λ z e′ → Visible e′ → After (cursor nothing rx₁) z)
                  (proj₁ nx) wq (λ r′ v′ a′ → proj₂ (proj₂ nx) r′ v′ (a′ v′)) shown using (goal) public

    -- The annotation's row, taken apart as an argument.
    from-row : ∀ {r′ me} → r ≡ routes-past (r′ , me)
             → (Σ (List (Pos × Ev (IE (Report.X Rp)))) λ pre → Σ Pos λ w → Σ (Ev (IE (Report.X Rp))) λ e
                  → Met (Src b) (pre ++ [ (w , e) ]) × r′ ≡ cnt pre × Rl ya w × AnnEv me e)
             → proj₂ r ≡ 0 ⊎ proj₁ r ≡ nameOf q
    from-row hl (_ , _ , _ , _ , _ , _ , ann-none) = inj₁ (cong proj₂ hl)
    from-row hl (pre , w , _ , srun , r′≡ , (zs₀ , ya≡) , ann-just {v′}) =
      subst (λ x → proj₂ x ≡ 0 ⊎ proj₁ x ≡ nameOf q)
            (trans (cnt-++ pre [ (w , out v′) ]) (trans (cong (λ x → count x v′) (sym r′≡)) (sym hl)))
            (Met′.goal srun zs₀ ya≡)

    held-at : ∀ (a′ : AIE (Report.X Rp)) → Ann b ya (out a′) → r ≡ routes-past a′ → proj₂ r ≡ 0 ⊎ proj₁ r ≡ nameOf q
    held-at (r′ , me) an hl = from-row hl (ann-row b an)

    held′ : proj₂ r ≡ 0 ⊎ proj₁ r ≡ nameOf q
    held′ = held-at a ann held

  track-held : ∀ rx₁ {q e rx₂} → Met M (rx₁ ++ (q , e) ∷ rx₂) → Visible e → ∀ {i r} → LastIn i r rx₁
             → proj₂ r ≡ 0 ⊎ proj₁ r ≡ nameOf q
  track-held rx₁ mt v li = At.held′ rx₁ mt v li
