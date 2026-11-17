{-# OPTIONS --guardedness #-}

-- THE SCAN'S ROWS (`scan-rows`).  The elaboration's merge, subscribed at
-- `P`, runs the concat as its first lane and the tick as its second; its
-- rows are the concat's and the tick's (`MRow`).  The concat's own end
-- is silent unless the cold ended later, past the outer: the merge ends
-- with the outer's end only if the cold ended in the subscribe burst.
--
-- The scan flags a value late exactly where it lies at or past the tick
-- (`Flag`): every value is either before the tick or past it, and the
-- tick is a value, so the flag is decided by the order alone and the
-- fold up to a value needs nothing else about the values before it.
module simultaneous.ColdScan where

open import Data.Bool using (Bool; true; false; if_then_else_; not; _∨_)
open import Data.Bool.Properties using (∨-zeroʳ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; mergeᶠ; flatMap; of; scan)
open import denotation.Position using (Pos; _≟ᵖ_; root; ix; last; _⊕_)
open import denotation.Events using (Timeline; From; fresh)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; EmissionSet; Den; Ended; Work; LaneOf; _≺_; _≼_;
  module Merge; module Scan; module Values)
open import denotation.Laws.Modulus using (≼-refl; ≺→≼; ≺-trans; ≺-irrefl; ≺-absurd)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (Row)
open import quickcheck.Tabled.Exact.Base using (Exact)
open import simultaneous.SObs using (Tag; val; cdone; tick; lone; module Elaborate)
open import simultaneous.Listing using (listC; listC-ok; UncutEnv)
open import simultaneous.TableCorr using (TR)
open import simultaneous.Readings using (instantOf)
open import simultaneous.ListTR using (laneD; ent; merge-tr; scan-tr; self-exact; Of1; Of2; o₀; o₁; oₑ; of1; of2;
  module NthAny; module AccOf)
open import simultaneous.ColdOrder using (down; part; module Ord)
open import simultaneous.ColdRows using (module At)
open import simultaneous.ColdCat using (module Cat)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (phase)

module Phase {A : Set} (K n : ℕ) {Δ : List Set} (ρ : All Tb.Listed Δ) (uρ : UncutEnv ρ) (m : From A 0) (P : Pos) where
  open At {A} P using (C₀; c₀; sync; SRow; mv₀; mv₁; cv₀; cv₁; tk; tke; ce; cval; cskp; se-c; se-d; se-k; se-e; ae-h; ae-d; ae-e; me-p)
  open Ord {A} P K m using (J; T₀; inP; sync-or; past; early; late; T₀-in; C₀≺c₀; C1-T; C110-T; CL-PL; TL-PL; dn2; dn3)
  open Cat K n ρ uρ m P using (CatRow; k-v₀; k-v₁; k-val; k-skp; ks-c; ks-d; ks-k; ks-e; ka-h; ka-d; ka-e; ka-p; catted; cat-rows)

  ------------------------------------------------------------------------
  -- The merge's rows

  data MRow : Pos → Ev (Tag A) → Set where
    g-mv₀ : MRow (P ⊕ [ ix 0 ] ⊕ [ ix 0 ]) skip
    g-mv₁ : MRow (P ⊕ [ ix 1 ] ⊕ [ ix 0 ]) skip
    g-cv₀ : MRow (C₀ ⊕ [ ix 0 ] ⊕ [ ix 0 ]) skip
    g-cv₁ : MRow (C₀ ⊕ [ ix 1 ] ⊕ [ ix 0 ]) skip
    g-tk  : MRow T₀ (out tick)
    g-tke : MRow (P ⊕ [ ix 1 ] ⊕ [ ix 1 ] ⊕ [ last ]) skip
    g-ce  : MRow (C₀ ⊕ [ last ]) skip
    g-val : ∀ {y a} → (y , out a) ∈ J → MRow y (out (val a))
    g-skp : ∀ {y} → (y , skip) ∈ J → MRow y skip
    g-sc  : ∀ {c} → (c , end) ∈ J → sync c ≡ true → MRow c skip
    g-sd  : ∀ {c} → (c , end) ∈ J → sync c ≡ true → MRow (C₀ ⊕ [ ix 1 ] ⊕ [ ix 1 ] ⊕ [ ix 0 ]) (out cdone)
    g-sk  : ∀ {c} → (c , end) ∈ J → sync c ≡ true → MRow (C₀ ⊕ [ ix 1 ] ⊕ [ ix 1 ] ⊕ [ last ]) skip
    g-se  : ∀ {c} → (c , end) ∈ J → sync c ≡ true → MRow (P ⊕ [ last ]) end
    g-ah  : ∀ {c} → (c , end) ∈ J → sync c ≡ false → MRow (c ⊕ [ ix 0 ]) skip
    g-ad  : ∀ {c} → (c , end) ∈ J → sync c ≡ false → MRow (c ⊕ [ ix 1 ] ⊕ [ ix 0 ]) (out cdone)
    g-ae  : ∀ {c} → (c , end) ∈ J → sync c ≡ false → MRow (c ⊕ [ ix 1 ] ⊕ [ last ]) end
    g-mp  : (∀ {c} → (c , end) ∈ J → sync c ≡ false) → MRow (P ⊕ [ last ]) skip

  ------------------------------------------------------------------------
  -- The merge

  fM : Bool → Obs Timeline Δ (Tag A)
  fM b = if b then catted else of (tick ∷ [])

  merged : Obs Timeline Δ (Tag A)
  merged = flatMap (mergeᶠ nothing) fM (of (true ∷ false ∷ []))

  scanned : Obs Timeline Δ (Bool × Tag A)
  scanned = scan phase (false , tick) merged

  fM′ : Bool → Den (Tag A)
  fM′ = laneD K n fM ρ

  O′ : EmissionSet Bool
  O′ = TR (listC K n (of (true ∷ false ∷ [])) ρ P)

  open Merge fM′ O′ using (JoinT; Done; val; step; opin; oend; opass; lane; lend; lpass; hand; left; run; rend; rpass; rhand)

  private
    TL : Pos
    TL = P ⊕ [ ix 1 ] ⊕ [ ix 1 ] ⊕ [ last ]

    o-to : ∀ {k e} → O′ k e → Of2 P true false k e
    o-to = Equivalence.to (of2 K n true false {ρ = ρ} P)

    o-fr : ∀ {k e} → Of2 P true false k e → O′ k e
    o-fr = Equivalence.from (of2 K n true false {ρ = ρ} P)

    c-to : ∀ {k e} → TR (listC K n catted ρ C₀) k e → CatRow k e
    c-to = Equivalence.to cat-rows

    c-fr : ∀ {k e} → CatRow k e → TR (listC K n catted ρ C₀) k e
    c-fr = Equivalence.from cat-rows

    t-to : ∀ {s k e} → TR (listC K n (of (tick {A} ∷ [])) ρ s) k e → Of1 s (tick {A}) k e
    t-to {s} = Equivalence.to (of1 K n (tick {A}) {ρ = ρ} s)

    t-fr : ∀ {s k e} → Of1 s (tick {A}) k e → TR (listC K n (of (tick {A} ∷ [])) ρ s) k e
    t-fr {s} = Equivalence.from (of1 K n (tick {A}) {ρ = ρ} s)

    tf : true ≡ false → ⊥
    tf ()

    lateP : ∀ {c e} → (c , e) ∈ J → sync c ≡ false → (P ⊕ [ last ]) ≺ c
    lateP y s = late y s (P ⊕ [ last ]) (inP P last refl)

    TL-in : instantOf TL ≡ instantOf P
    TL-in = inP (P ⊕ [ ix 1 ] ⊕ [ ix 1 ]) last (inP (P ⊕ [ ix 1 ]) (ix 1) (inP P (ix 1) refl))

    Cc : ∀ {c e} → (c , e) ∈ J → C₀ ≺ c
    Cc {c} y = ≺-trans {C₀} {c₀} {c} C₀≺c₀ (past y)

    -- The concat's rows lie under its subscription.
    cat-past : ∀ {k e} → CatRow k e → C₀ ≺ k
    cat-past k-v₀        = dn2 C₀ (ix 0) (ix 0)
    cat-past k-v₁        = dn2 C₀ (ix 1) (ix 0)
    cat-past (k-val y)   = Cc y
    cat-past (k-skp y)   = Cc y
    cat-past (ks-c y _)  = Cc y
    cat-past (ks-d _ _)  = dn3 C₀ (ix 1) (ix 1) (ix 0)
    cat-past (ks-k _ _)  = dn3 C₀ (ix 1) (ix 1) last
    cat-past (ks-e _ _)  = down C₀ last
    cat-past (ka-h {c} y _) = ≺-trans {C₀} {c} {c ⊕ [ ix 0 ]} (Cc y) (down c (ix 0))
    cat-past (ka-d {c} y _) = ≺-trans {C₀} {c} {c ⊕ [ ix 1 ] ⊕ [ ix 0 ]} (Cc y) (dn2 c (ix 1) (ix 0))
    cat-past (ka-e {c} y _) = ≺-trans {C₀} {c} {c ⊕ [ ix 1 ] ⊕ [ last ]} (Cc y) (dn2 c (ix 1) last)
    cat-past (ka-p _)    = down C₀ last

    lane0 : ∀ {k e} → CatRow k e → LaneOf fM′ (P ⊕ [ ix 0 ]) true k e
    lane0 r = ent K n catted uρ C₀ (c-fr r) , cat-past r

    lane1 : ∀ {k e} → Of1 (P ⊕ [ ix 1 ] ⊕ [ ix 1 ]) (tick {A}) k e → LaneOf fM′ (P ⊕ [ ix 1 ]) false k e
    lane1 o₀ = ent K n (of (tick {A} ∷ [])) uρ (P ⊕ [ ix 1 ] ⊕ [ ix 1 ]) (t-fr o₀) , down (P ⊕ [ ix 1 ] ⊕ [ ix 1 ]) (ix 0)
    lane1 oₑ = ent K n (of (tick {A} ∷ [])) uρ (P ⊕ [ ix 1 ] ⊕ [ ix 1 ]) (t-fr oₑ) , down (P ⊕ [ ix 1 ] ⊕ [ ix 1 ]) last

    over-at : ∀ {c} → Ended O′ c → (P ⊕ [ last ]) ≼ c
    over-at (c₁ , x , le) with o-to x
    ... | oₑ = le

    -- Ended in the burst: every part is over by the outer's end.
    doneS : ∀ {c} → (c , end) ∈ J → sync c ≡ true → Done (P ⊕ [ last ])
    doneS y s = (P ⊕ [ last ] , o-fr oₑ , ≼-refl {P ⊕ [ last ]}) , ends
      where
        ends : ∀ {q a} → O′ q (out a) → ⊤ → q ≺ (P ⊕ [ last ]) → ¬ ⊥ → Ended (LaneOf fM′ q a) (P ⊕ [ last ])
        ends x _ _ _ with o-to x
        ... | o₀ = C₀ ⊕ [ last ] , lane0 (ks-e y s) , ≺→≼ {C₀ ⊕ [ last ]} {P ⊕ [ last ]} CL-PL
        ... | o₁ = TL , lane1 oₑ , ≺→≼ {TL} {P ⊕ [ last ]} TL-PL

    -- Ended later: every part is over by the concat's end.
    doneA : ∀ {c} → (c , end) ∈ J → sync c ≡ false → Done (c ⊕ [ ix 1 ] ⊕ [ last ])
    doneA {c} y s = (P ⊕ [ last ] , o-fr oₑ , ≺→≼ {P ⊕ [ last ]} {c ⊕ [ ix 1 ] ⊕ [ last ]}
                       (≺-trans {P ⊕ [ last ]} {c} {c ⊕ [ ix 1 ] ⊕ [ last ]} (lateP y s) (dn2 c (ix 1) last))) , ends
      where
        ends : ∀ {q a} → O′ q (out a) → ⊤ → q ≺ (c ⊕ [ ix 1 ] ⊕ [ last ]) → ¬ ⊥ → Ended (LaneOf fM′ q a) (c ⊕ [ ix 1 ] ⊕ [ last ])
        ends x _ _ _ with o-to x
        ... | o₀ = c ⊕ [ ix 1 ] ⊕ [ last ] , lane0 (ka-e y s) , ≼-refl {c ⊕ [ ix 1 ] ⊕ [ last ]}
        ... | o₁ = TL , lane1 oₑ , ≺→≼ {TL} {c ⊕ [ ix 1 ] ⊕ [ last ]}
                     (≺-trans {TL} {c} {c ⊕ [ ix 1 ] ⊕ [ last ]} (late y s TL TL-in) (dn2 c (ix 1) last))

    -- The outer's end, given the concat is over by it.
    out-end : Done (P ⊕ [ last ]) → Σ Pos λ c → (c , end) ∈ J × sync c ≡ true
    out-end D with proj₂ D (o-fr o₀) tt (part P [] [] refl) (λ ())
    ... | _ , l , le with c-to (proj₁ (proj₁ l))
    ...   | ks-e y s = _ , y , s
    ...   | ka-e {c} y s = ⊥-elim (le (≺-trans {P ⊕ [ last ]} {c} {c ⊕ [ ix 1 ] ⊕ [ last ]} (lateP y s) (dn2 c (ix 1) last)))

    all-late : ¬ Done (P ⊕ [ last ]) → ∀ {c} → (c , end) ∈ J → sync c ≡ false
    all-late nD {c} y with sync-or c
    ... | inj₂ s = s
    ... | inj₁ s = ⊥-elim (nD (doneS y s))

    -- The cold ended in the burst, or it did not.
    any-sync : ∀ (xs : List (Row A)) → (Σ Pos λ c → (c , end) ∈ xs × sync c ≡ true) ⊎ (∀ {c} → (c , end) ∈ xs → sync c ≡ false)
    any-sync [] = inj₂ λ ()
    any-sync ((k , end) ∷ xs) with sync-or k | any-sync xs
    ... | inj₁ s | _                 = inj₁ (k , here refl , s)
    ... | inj₂ _ | inj₁ (c , x , s′) = inj₁ (c , there x , s′)
    ... | inj₂ s | inj₂ al           = inj₂ λ { (here refl) → s ; (there x) → al x }
    any-sync ((k , out _) ∷ xs) with any-sync xs
    ... | inj₁ (c , x , s′) = inj₁ (c , there x , s′)
    ... | inj₂ al           = inj₂ λ { (here ()) ; (there x) → al x }
    any-sync ((k , skip) ∷ xs) with any-sync xs
    ... | inj₁ (c , x , s′) = inj₁ (c , there x , s′)
    ... | inj₂ al           = inj₂ λ { (here ()) ; (there x) → al x }
    any-sync ((k , pin _) ∷ xs) with any-sync xs
    ... | inj₁ (c , x , s′) = inj₁ (c , there x , s′)
    ... | inj₂ al           = inj₂ λ { (here ()) ; (there x) → al x }

    cat-lane : ∀ {k e} → CatRow k e → Work e → MRow k e
    cat-lane k-v₀ _         = g-cv₀
    cat-lane k-v₁ _         = g-cv₁
    cat-lane (k-val y) _    = g-val y
    cat-lane (k-skp y) _    = g-skp y
    cat-lane (ks-c y s) _   = g-sc y s
    cat-lane (ks-d y s) _   = g-sd y s
    cat-lane (ks-k y s) _   = g-sk y s
    cat-lane (ks-e _ _) ()
    cat-lane (ka-h y s) _   = g-ah y s
    cat-lane (ka-d y s) _   = g-ad y s
    cat-lane (ka-e _ _) ()
    cat-lane (ka-p _) _     = g-ce

    tick-lane : ∀ {k e} → Of1 (P ⊕ [ ix 1 ] ⊕ [ ix 1 ]) (tick {A}) k e → Work e → MRow k e
    tick-lane o₀ _ = g-tk
    tick-lane oₑ ()

    cat-lend : ∀ {c} → CatRow c end → Done c → MRow c end
    cat-lend (ks-e _ _) D = ⊥-elim (over-at {C₀ ⊕ [ last ]} (proj₁ D) CL-PL)
    cat-lend (ka-e y s) _ = g-ae y s

    cat-lpass : ∀ {c} → CatRow c end → ¬ Done c → MRow c skip
    cat-lpass (ks-e _ _) _  = g-ce
    cat-lpass (ka-e y s) nD = ⊥-elim (nD (doneA y s))

    tick-lend : ∀ {c} → Of1 (P ⊕ [ ix 1 ] ⊕ [ ix 1 ]) (tick {A}) c end → Done c → MRow c end
    tick-lend oₑ D = ⊥-elim (over-at {TL} (proj₁ D) TL-PL)

    tick-lpass : ∀ {c} → Of1 (P ⊕ [ ix 1 ] ⊕ [ ix 1 ]) (tick {A}) c end → MRow c skip
    tick-lpass oₑ = g-tke

    cat-pin : ∀ {k r} → CatRow k (pin r) → ⊥
    cat-pin ()

    tick-pin : ∀ {s k r} → Of1 s (tick {A}) k (pin r) → ⊥
    tick-pin ()

    of2-skip : ∀ {k} → Of2 P true false k skip → ⊥
    of2-skip ()

    of2-pin : ∀ {k r} → Of2 P true false k (pin r) → ⊥
    of2-pin ()

  mrg-to : ∀ {k e} → JoinT k e → MRow k e
  mrg-to (val x) with o-to x
  ... | o₀ = g-mv₀
  ... | o₁ = g-mv₁
  mrg-to (step x) = ⊥-elim (of2-skip (o-to x))
  mrg-to (opin x) = ⊥-elim (of2-pin (o-to x))
  mrg-to (oend x D) with o-to x
  ... | oₑ with out-end D
  ...   | _ , y , s = g-se y s
  mrg-to (opass x nD) with o-to x
  ... | oₑ = g-mp (all-late nD)
  mrg-to (lane x _ l _ w) with o-to x
  ... | o₀ = cat-lane (c-to (proj₁ (proj₁ l))) w
  ... | o₁ = tick-lane (t-to (proj₁ (proj₁ l))) w
  mrg-to (lend x _ l _ _ D) with o-to x
  ... | o₀ = cat-lend (c-to (proj₁ (proj₁ l))) D
  ... | o₁ = tick-lend (t-to (proj₁ (proj₁ l))) D
  mrg-to (lpass x _ l _ _ nD) with o-to x
  ... | o₀ = cat-lpass (c-to (proj₁ (proj₁ l))) nD
  ... | o₁ = tick-lpass (t-to (proj₁ (proj₁ l)))
  mrg-to (hand _ _ _ _ ())
  mrg-to (left x _ l _ _) with o-to x
  ... | o₀ = ⊥-elim (cat-pin (c-to (proj₁ (proj₁ l))))
  ... | o₁ = ⊥-elim (tick-pin (t-to (proj₁ (proj₁ l))))
  mrg-to (run () _)
  mrg-to (rend () _ _)
  mrg-to (rpass () _ _)
  mrg-to (rhand () _)

  mrg-fr : ∀ {k e} → MRow k e → JoinT k e
  mrg-fr g-mv₀       = val (o-fr o₀)
  mrg-fr g-mv₁       = val (o-fr o₁)
  mrg-fr g-cv₀       = lane (o-fr o₀) tt (lane0 k-v₀) (λ ()) tt
  mrg-fr g-cv₁       = lane (o-fr o₀) tt (lane0 k-v₁) (λ ()) tt
  mrg-fr g-tk        = lane (o-fr o₁) tt (lane1 o₀) (λ ()) tt
  mrg-fr g-tke       = lpass (o-fr o₁) tt (lane1 oₑ) (λ ()) (λ ()) (λ D → over-at {TL} (proj₁ D) TL-PL)
  mrg-fr g-ce with any-sync J
  ... | inj₁ (c , y , s) = lpass (o-fr o₀) tt (lane0 (ks-e y s)) (λ ()) (λ ()) (λ D → over-at {C₀ ⊕ [ last ]} (proj₁ D) CL-PL)
  ... | inj₂ al          = lane (o-fr o₀) tt (lane0 (ka-p al)) (λ ()) tt
  mrg-fr (g-val y)   = lane (o-fr o₀) tt (lane0 (k-val y)) (λ ()) tt
  mrg-fr (g-skp y)   = lane (o-fr o₀) tt (lane0 (k-skp y)) (λ ()) tt
  mrg-fr (g-sc y s)  = lane (o-fr o₀) tt (lane0 (ks-c y s)) (λ ()) tt
  mrg-fr (g-sd y s)  = lane (o-fr o₀) tt (lane0 (ks-d y s)) (λ ()) tt
  mrg-fr (g-sk y s)  = lane (o-fr o₀) tt (lane0 (ks-k y s)) (λ ()) tt
  mrg-fr (g-se y s)  = oend (o-fr oₑ) (doneS y s)
  mrg-fr (g-ah y s)  = lane (o-fr o₀) tt (lane0 (ka-h y s)) (λ ()) tt
  mrg-fr (g-ad y s)  = lane (o-fr o₀) tt (lane0 (ka-d y s)) (λ ()) tt
  mrg-fr (g-ae y s)  = lend (o-fr o₀) tt (lane0 (ka-e y s)) (λ ()) (λ ()) (doneA y s)
  mrg-fr (g-mp al)   = opass (o-fr oₑ) (λ D → let (_ , y , s) = out-end D in tf (trans (sym s) (al y)))

  ------------------------------------------------------------------------
  -- The scan

  Mt : EmissionSet (Tag A)
  Mt = TR (listC K n merged ρ P)

  open Scan phase (false , tick) Mt using (Acc; acc₀; acc; ScanT; sval; sstep; spin; send)
  open Values Mt using (Next)

  private
    mt-to : ∀ {k e} → Mt k e → MRow k e
    mt-to x = mrg-to (Equivalence.to (merge-tr K n fM (of (true ∷ false ∷ [])) uρ P) x)

    mt-fr : ∀ {k e} → MRow k e → Mt k e
    mt-fr r = Equivalence.from (merge-tr K n fM (of (true ∷ false ∷ [])) uρ P) (mrg-fr r)

    okM = listC-ok K n merged uρ P

    exM : Exact (proj₁ okM) Mt
    exM = self-exact (proj₁ (proj₂ okM)) (proj₂ (proj₂ okM))

  open NthAny exM using (nth-any)
  open AccOf phase (false , tick) Mt using (acc-of)

  -- Late exactly at or past the tick.
  Flag : Pos → Bool → Set
  Flag q f = (f ≡ true × T₀ ≼ q) ⊎ (f ≡ false × q ≺ T₀)

  private
    tkMt : Mt T₀ (out tick)
    tkMt = mt-fr g-tk

    lateT : ∀ {c} → (c , end) ∈ J → sync c ≡ false → T₀ ≺ (c ⊕ [ ix 1 ] ⊕ [ ix 0 ])
    lateT {c} y s = ≺-trans {T₀} {c} {c ⊕ [ ix 1 ] ⊕ [ ix 0 ]} (late y s T₀ T₀-in) (dn2 c (ix 1) (ix 0))

    flag-uniq : ∀ {q f g} → Flag q f → Flag q g → f ≡ g
    flag-uniq (inj₁ (refl , _))  (inj₁ (refl , _))  = refl
    flag-uniq (inj₁ (_ , le))    (inj₂ (_ , lt))     = ⊥-elim (le lt)
    flag-uniq (inj₂ (_ , lt))    (inj₁ (_ , le))     = ⊥-elim (le lt)
    flag-uniq (inj₂ (refl , _))  (inj₂ (refl , _))   = refl

    -- The first value.
    inv₀ : ∀ {q a} → MRow q (out a) → (∀ {k b} → Mt k (out b) → q ≼ k) → Flag q (proj₁ (phase (false , tick) a))
    inv₀ g-tk _ = inj₁ (refl , ≼-refl {T₀})
    inv₀ (g-val {y} x) mn with sync-or y
    ... | inj₁ s = inj₂ (refl , ≺-trans {y} {C₀ ⊕ [ ix 1 ]} {T₀} (early x s) C1-T)
    ... | inj₂ s = ⊥-elim (mn tkMt (late x s T₀ T₀-in))
    inv₀ (g-sd _ _) _ = inj₂ (refl , C110-T)
    inv₀ (g-ad x s) mn = ⊥-elim (mn tkMt (lateT x s))

    -- A value that is not the tick, before or past it.
    st-val : ∀ {q q′} f → Flag q f → q ≺ q′ → Next q q′ → q′ ≺ T₀ ⊎ T₀ ≺ q′ → Flag q′ (f ∨ false)
    st-val {q} {q′} f (inj₁ (refl , le)) lt _ (inj₁ e) = ⊥-elim (le (≺-trans {q} {q′} {T₀} lt e))
    st-val {q} {q′} f (inj₁ (refl , _))  _  _ (inj₂ g) = inj₁ (refl , ≺→≼ {T₀} {q′} g)
    st-val f (inj₂ (refl , _))  _  _  (inj₁ e) = inj₂ (refl , e)
    st-val {q} {q′} f (inj₂ (refl , l))  _  nx (inj₂ g) = ⊥-elim (nx {T₀} {tick} tkMt l g)

    -- The next value.
    invN : ∀ {q q′ a′} f t → Flag q f → MRow q′ (out a′) → q ≺ q′ → Next q q′ → Flag q′ (proj₁ (phase (f , t) a′))
    invN f _ _ g-tk _ _ = inj₁ (∨-zeroʳ f , ≼-refl {T₀})
    invN {q} f _ fl (g-val {y} x) lt nx with sync-or y
    ... | inj₁ s = st-val {q} {y} f fl lt nx (inj₁ (≺-trans {y} {C₀ ⊕ [ ix 1 ]} {T₀} (early x s) C1-T))
    ... | inj₂ s = st-val {q} {y} f fl lt nx (inj₂ (late x s T₀ T₀-in))
    invN {q} f _ fl (g-sd _ _) lt nx = st-val {q} {C₀ ⊕ [ ix 1 ] ⊕ [ ix 1 ] ⊕ [ ix 0 ]} f fl lt nx (inj₁ C110-T)
    invN {q} f _ fl (g-ad {c} x s) lt nx = st-val {q} {c ⊕ [ ix 1 ] ⊕ [ ix 0 ]} f fl lt nx (inj₂ (lateT x s))

  acc-inv : ∀ {q b} → Acc q b → Flag q (proj₁ b)
  acc-inv (acc₀ x mn) = inv₀ (mt-to x) mn
  acc-inv (acc {q = q} {b = f , t} {q′ = q′} A x lt nx) = invN {q} {q′} f t (acc-inv A) (mt-to x) lt nx

  private
    acc-row : ∀ {q b} → Acc q b → Mt q (out (proj₂ b))
    acc-row (acc₀ x _)    = x
    acc-row (acc _ x _ _) = x

    srow-of : ∀ {q a f} → MRow q (out a) → Flag q f → SRow J q (out (f , a))
    srow-of g-tk (inj₁ (refl , _)) = tk
    srow-of g-tk (inj₂ (_ , lt))   = ⊥-elim (≺-irrefl {T₀} lt)
    srow-of (g-val {y} x) fl with sync-or y | fl
    ... | inj₁ s | inj₂ (refl , _) = cval x (cong not s)
    ... | inj₁ s | inj₁ (_ , le)   = ⊥-elim (le (≺-trans {y} {C₀ ⊕ [ ix 1 ]} {T₀} (early x s) C1-T))
    ... | inj₂ s | inj₁ (refl , _) = cval x (cong not s)
    ... | inj₂ s | inj₂ (_ , lt)   = ⊥-elim (≺-absurd {y} {T₀} lt (late x s T₀ T₀-in))
    srow-of (g-sd x s) (inj₂ (refl , _)) = se-d x s
    srow-of (g-sd x s) (inj₁ (_ , le))   = ⊥-elim (le C110-T)
    srow-of (g-ad x s) (inj₁ (refl , _)) = ae-d x s
    srow-of (g-ad {c} x s) (inj₂ (_ , lt)) = ⊥-elim (≺-absurd {c ⊕ [ ix 1 ] ⊕ [ ix 0 ]} {T₀} lt (lateT x s))

    of-srow : ∀ {q f a} → SRow J q (out (f , a)) → MRow q (out a) × Flag q f
    of-srow tk = g-tk , inj₁ (refl , ≼-refl {T₀})
    of-srow (cval {y} x e) with sync-or y
    ... | inj₁ s = g-val x , inj₂ (trans (sym e) (cong not s) , ≺-trans {y} {C₀ ⊕ [ ix 1 ]} {T₀} (early x s) C1-T)
    ... | inj₂ s = g-val x , inj₁ (trans (sym e) (cong not s) , ≺→≼ {T₀} {y} (late x s T₀ T₀-in))
    of-srow (se-d x s) = g-sd x s , inj₂ (refl , C110-T)
    of-srow (ae-d {c} x s) = g-ad x s , inj₁ (refl , ≺→≼ {T₀} {c ⊕ [ ix 1 ] ⊕ [ ix 0 ]} (lateT x s))

    acc-at : ∀ {q f a} → SRow J q (out (f , a)) → Acc q (f , a)
    acc-at {q} {f} {a} s with of-srow s
    ... | r , fl with nth-any (mt-fr r)
    ... | _ , N with acc-of N
    ... | _ , A′ = subst (λ g → Acc q (g , a)) (flag-uniq {q} (acc-inv A′) fl) A′

    skip-s : ∀ {k} → MRow k skip → SRow J k skip
    skip-s g-mv₀      = mv₀
    skip-s g-mv₁      = mv₁
    skip-s g-cv₀      = cv₀
    skip-s g-cv₁      = cv₁
    skip-s g-tke      = tke
    skip-s g-ce       = ce
    skip-s (g-skp y)  = cskp y
    skip-s (g-sc y s) = se-c y s
    skip-s (g-sk y s) = se-k y s
    skip-s (g-ah y s) = ae-h y s
    skip-s (g-mp al)  = me-p al

    end-s : ∀ {k} → MRow k end → SRow J k end
    end-s (g-se y s) = se-e y s
    end-s (g-ae y s) = ae-e y s

    pin-s : ∀ {k r} → MRow k (pin r) → ⊥
    pin-s ()

  scan-to : ∀ {k e} → ScanT k e → SRow J k e
  scan-to (sval A)  = srow-of (mt-to (acc-row A)) (acc-inv A)
  scan-to (sstep x) = skip-s (mt-to x)
  scan-to (spin x)  = ⊥-elim (pin-s (mt-to x))
  scan-to (send x)  = end-s (mt-to x)

  scan-fr : ∀ {k e} → SRow J k e → ScanT k e
  scan-fr mv₀          = sstep (mt-fr g-mv₀)
  scan-fr mv₁          = sstep (mt-fr g-mv₁)
  scan-fr cv₀          = sstep (mt-fr g-cv₀)
  scan-fr cv₁          = sstep (mt-fr g-cv₁)
  scan-fr tk           = sval (acc-at tk)
  scan-fr tke          = sstep (mt-fr g-tke)
  scan-fr ce           = sstep (mt-fr g-ce)
  scan-fr (cval x e)   = sval (acc-at (cval x e))
  scan-fr (cskp y)     = sstep (mt-fr (g-skp y))
  scan-fr (se-c y s)   = sstep (mt-fr (g-sc y s))
  scan-fr (se-d y s)   = sval (acc-at (se-d y s))
  scan-fr (se-k y s)   = sstep (mt-fr (g-sk y s))
  scan-fr (se-e y s)   = send (mt-fr (g-se y s))
  scan-fr (ae-h y s)   = sstep (mt-fr (g-ah y s))
  scan-fr (ae-d y s)   = sval (acc-at (ae-d y s))
  scan-fr (ae-e y s)   = send (mt-fr (g-ae y s))
  scan-fr (me-p al)    = sstep (mt-fr (g-mp al))

  scan-rows : ∀ {k e} → TR (listC K n scanned ρ P) k e ⇔ SRow J k e
  scan-rows = mk⇔ (λ x → scan-to (Equivalence.to (scan-tr K n phase (false , tick) merged uρ P) x))
                  (λ x → Equivalence.from (scan-tr K n phase (false , tick) merged uρ P) (scan-fr x))
