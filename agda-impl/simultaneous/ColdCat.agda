{-# OPTIONS --guardedness #-}

-- THE CONCAT'S ROWS (`cat-rows`).  The elaboration's concat, subscribed
-- at `C₀`, runs the cold as its first lane, at once, and the completion
-- tag as its second.  Where the second starts turns on the cold's end
-- `c`: in the subscribe burst, `c` is before the second value arrives,
-- so the tag starts on arrival and is over before the outer is; the
-- cold's end is a skip, the outer's end the concat's.  Later, the tag
-- waits for `c` and starts one step under it: the cold's end hands it
-- its place, and the tag's end is the concat's.  With no end at all, the
-- outer's end is a skip and nothing ends.
module simultaneous.ColdCat where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; s≤s; z≤n)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Function using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; mergeᶠ; flatMap; cold; of; map)
open import denotation.Position using (Pos; ix; last; _⊕_)
open import denotation.Events using (Timeline; From; fixed; start)
open import denotation.EmissionSet using (Ev; out; skip; end; EmissionSet; Den; Ended; Work; After; MapT; _≺_; _≼_; map-out; map-skip;
  map-pin; map-end; module Values; module Bounded)
open import denotation.Laws.Modulus using (≼-refl; ≺→≼; ≺-trans; ≺-irrefl; ≺-absurd)
import quickcheck.Tabled as Tb
open import simultaneous.SObs using (Tag; val; cdone)
open import simultaneous.Listing using (listC; UncutEnv)
open import simultaneous.TableCorr using (TR)
open import simultaneous.ListTR using (laneD; ent; cold-tr; map-tr; bounded-tr; Of1; Of2; o₀; o₁; oₑ; of1; of2)
open import simultaneous.ColdOrder using (dn2; walk-end; walk-nopin; ≺-≢; ⊕1-inj; down; module Ord)
open import simultaneous.ColdRows using (module At)

module Cat {A : Set} (K n : ℕ) {Δ : List Set} (ρ : All Tb.Listed Δ) (uρ : UncutEnv ρ) (m : From A 0) (P : Pos) where
  open At {A} P using (C₀; c₀; sync)
  open Ord {A} P K m using (J; sync-or; sync-at; early; late; past; inP; C₀-in; lt01; lt0L; lt1L; lt11L; C0c₀)

  ------------------------------------------------------------------------
  -- The rows

  data CatRow : Pos → Ev (Tag A) → Set where
    k-v₀  : CatRow (C₀ ⊕ [ ix 0 ] ⊕ [ ix 0 ]) skip
    k-v₁  : CatRow (C₀ ⊕ [ ix 1 ] ⊕ [ ix 0 ]) skip
    k-val : ∀ {y a} → (y , out a) ∈ J → CatRow y (out (val a))
    k-skp : ∀ {y} → (y , skip) ∈ J → CatRow y skip
    ks-c  : ∀ {c} → (c , end) ∈ J → sync c ≡ true → CatRow c skip
    ks-d  : ∀ {c} → (c , end) ∈ J → sync c ≡ true → CatRow (C₀ ⊕ [ ix 1 ] ⊕ [ ix 1 ] ⊕ [ ix 0 ]) (out cdone)
    ks-k  : ∀ {c} → (c , end) ∈ J → sync c ≡ true → CatRow (C₀ ⊕ [ ix 1 ] ⊕ [ ix 1 ] ⊕ [ last ]) skip
    ks-e  : ∀ {c} → (c , end) ∈ J → sync c ≡ true → CatRow (C₀ ⊕ [ last ]) end
    ka-h  : ∀ {c} → (c , end) ∈ J → sync c ≡ false → CatRow (c ⊕ [ ix 0 ]) skip
    ka-d  : ∀ {c} → (c , end) ∈ J → sync c ≡ false → CatRow (c ⊕ [ ix 1 ] ⊕ [ ix 0 ]) (out cdone)
    ka-e  : ∀ {c} → (c , end) ∈ J → sync c ≡ false → CatRow (c ⊕ [ ix 1 ] ⊕ [ last ]) end
    ka-p  : (∀ {c} → (c , end) ∈ J → sync c ≡ false) → CatRow (C₀ ⊕ [ last ]) skip

  ------------------------------------------------------------------------
  -- The concat

  fC : Bool → Obs Timeline Δ (Tag A)
  fC b = if b then map val (cold (fixed m)) else of (cdone ∷ [])

  catted : Obs Timeline Δ (Tag A)
  catted = flatMap (mergeᶠ (just 1)) fC (of (true ∷ false ∷ []))

  fD : Bool → Den (Tag A)
  fD = laneD K n fC ρ

  O : EmissionSet Bool
  O = TR (listC K n (of (true ∷ false ∷ [])) ρ C₀)

  open Values O using (Nth; first; next; Next)
  open Bounded 1 fD O using (Kth; Starts; room; freed; queued; Ends; Sched; Sub; Queued; Lane; Indexed;
    JoinT; Done; val; step; opin; oend; opass; lane; lend; lpass; hand; left; run; rend; rpass; rhand)

  private
    o-to : ∀ {k e} → O k e → Of2 C₀ true false k e
    o-to = Equivalence.to (of2 K n true false {ρ = ρ} C₀)

    o-fr : ∀ {k e} → Of2 C₀ true false k e → O k e
    o-fr = Equivalence.from (of2 K n true false {ρ = ρ} C₀)

    -- The cold's own rows, read where its lane is subscribed.
    cold-to : ∀ {k e} → TR (listC K n (cold (fixed m)) ρ c₀) k e → (k , e) ∈ J
    cold-to = Equivalence.to (cold-tr K n m {ρ = ρ} c₀)

    cold-fr : ∀ {k e} → (k , e) ∈ J → TR (listC K n (cold (fixed m)) ρ c₀) k e
    cold-fr = Equivalence.from (cold-tr K n m {ρ = ρ} c₀)

    L₀ : EmissionSet (Tag A)
    L₀ = TR (listC K n (map val (cold (fixed m))) ρ c₀)

    l₀-to : ∀ {k e} → L₀ k e → MapT val (TR (listC K n (cold (fixed m)) ρ c₀)) k e
    l₀-to = Equivalence.to (map-tr K n val (cold (fixed m)) uρ c₀)

    l₀-fr : ∀ {k e} → MapT val (TR (listC K n (cold (fixed m)) ρ c₀)) k e → L₀ k e
    l₀-fr = Equivalence.from (map-tr K n val (cold (fixed m)) uρ c₀)

    o1-to : ∀ {s k e} → TR (listC K n (of (cdone {A} ∷ [])) ρ s) k e → Of1 s (cdone {A}) k e
    o1-to {s} = Equivalence.to (of1 K n (cdone {A}) {ρ = ρ} s)

    o1-fr : ∀ {s k e} → Of1 s (cdone {A}) k e → TR (listC K n (of (cdone {A} ∷ [])) ρ s) k e
    o1-fr {s} = Equivalence.from (of1 K n (cdone {A}) {ρ = ρ} s)

    late-C1 : ∀ {c e} → (c , e) ∈ J → sync c ≡ false → (C₀ ⊕ [ ix 1 ]) ≺ c
    late-C1 y s = late y s (C₀ ⊕ [ ix 1 ]) (inP C₀ (ix 1) C₀-in)

    late-CL : ∀ {c e} → (c , e) ∈ J → sync c ≡ false → (C₀ ⊕ [ last ]) ≺ c
    late-CL y s = late y s (C₀ ⊕ [ last ]) (inP C₀ last C₀-in)

    sync-lt : ∀ {c e} → (c , e) ∈ J → c ≺ (C₀ ⊕ [ ix 1 ]) → sync c ≡ true
    sync-lt {c} y lt with sync-or c
    ... | inj₁ s = s
    ... | inj₂ s = ⊥-elim (≺-absurd {c} {C₀ ⊕ [ ix 1 ]} lt (late-C1 y s))

    sync-gt : ∀ {c e} → (c , e) ∈ J → (C₀ ⊕ [ ix 1 ]) ≺ c → sync c ≡ false
    sync-gt {c} y lt with sync-or c
    ... | inj₂ s = s
    ... | inj₁ s = ⊥-elim (≺-absurd {c} {C₀ ⊕ [ ix 1 ]} (early y s) lt)

    tf : true ≡ false → ⊥
    tf ()

  ------------------------------------------------------------------------
  -- The outer's two values

  data NthV : ℕ → Pos → Bool → Set where
    nv₀ : NthV 0 (C₀ ⊕ [ ix 0 ]) true
    nv₁ : NthV 1 (C₀ ⊕ [ ix 1 ]) false

  private
    nth-inv : ∀ {i q a} → Nth i q a → NthV i q a
    nth-inv (first x mn) with o-to x
    ... | o₀ = nv₀
    ... | o₁ = ⊥-elim (mn (o-fr o₀) lt01)
    nth-inv (next N x lt _) with nth-inv N | o-to x
    ... | nv₀ | o₀ = ⊥-elim (≺-irrefl {C₀ ⊕ [ ix 0 ]} lt)
    ... | nv₀ | o₁ = nv₁
    ... | nv₁ | o₀ = ⊥-elim (≺-absurd {C₀ ⊕ [ ix 0 ]} {C₀ ⊕ [ ix 1 ]} lt01 lt)
    ... | nv₁ | o₁ = ⊥-elim (≺-irrefl {C₀ ⊕ [ ix 1 ]} lt)

    min₀ : ∀ {k b} → O k (out b) → (C₀ ⊕ [ ix 0 ]) ≼ k
    min₀ x with o-to x
    ... | o₀ = ≼-refl {C₀ ⊕ [ ix 0 ]}
    ... | o₁ = ≺→≼ {C₀ ⊕ [ ix 0 ]} {C₀ ⊕ [ ix 1 ]} lt01

    nx₁ : Next (C₀ ⊕ [ ix 0 ]) (C₀ ⊕ [ ix 1 ])
    nx₁ x lt with o-to x
    ... | o₀ = ⊥-elim (≺-irrefl {C₀ ⊕ [ ix 0 ]} lt)
    ... | o₁ = ≼-refl {C₀ ⊕ [ ix 1 ]}

    nth₀ : Nth 0 (C₀ ⊕ [ ix 0 ]) true
    nth₀ = first (o-fr o₀) min₀

    nth₁ : Nth 1 (C₀ ⊕ [ ix 1 ]) false
    nth₁ = next nth₀ (o-fr o₁) lt01 nx₁

    idx₀ : Indexed (C₀ ⊕ [ ix 0 ])
    idx₀ = 0 , true , nth₀

    idx₁ : Indexed (C₀ ⊕ [ ix 1 ])
    idx₁ = 1 , false , nth₁

  ------------------------------------------------------------------------
  -- The schedule

  private
    -- The cold's lane, subscribed at once.
    aft₀ : ∀ {k e} → L₀ k e → c₀ ≺ k → After (fD true) c₀ k e
    aft₀ x lt = ent K n (map val (cold (fixed m))) uρ c₀ x , lt

    -- The tag's lane, wherever it starts.
    aft₁ : ∀ {s k e} → TR (listC K n (of (cdone {A} ∷ [])) ρ s) k e → s ≺ k → After (fD false) s k e
    aft₁ {s} x lt = ent K n (of (cdone {A} ∷ [])) uρ s x , lt

    st0 : ∀ {q s} → Starts 0 q [] s → s ≡ q ⊕ [ ix 1 ]
    st0 (room _)            = refl
    st0 (freed () _)
    st0 (queued () _ _ _ _)

    ends0-inv : ∀ {c} → Ends 0 [] c → (c , end) ∈ J
    ends0-inv (q , a , s , nt , st , aft) = go (nth-inv nt) st aft
      where
        go : ∀ {q a s c} → NthV 0 q a → Starts 0 q [] s → After (fD a) s c end → (c , end) ∈ J
        go nv₀ (room _) ((x , _) , _) with l₀-to x
        ... | map-end y = cold-to y
        go nv₀ (freed () _) _
        go nv₀ (queued () _ _ _ _) _

    e0 : ∀ {c} → (c , end) ∈ J → Ends 0 [] c
    e0 y = C₀ ⊕ [ ix 0 ] , true , c₀ , nth₀ , room (s≤s z≤n) , aft₀ (l₀-fr (map-end (cold-fr y))) (past y)

    -- Where the tag's lane starts: on arrival, the cold ended in the
    -- burst; or one step under the cold's later end.
    st1 : ∀ {s} → Starts 1 (C₀ ⊕ [ ix 1 ]) (Sched 1) s
        → (Σ Pos λ c → (c , end) ∈ J × sync c ≡ true × s ≡ C₀ ⊕ [ ix 1 ] ⊕ [ ix 1 ])
        ⊎ (Σ Pos λ c → (c , end) ∈ J × sync c ≡ false × s ≡ c ⊕ [ ix 1 ])
    st1 (room (s≤s ()))
    st1 (freed _ (inj₁ (c , e , lt))) = inj₁ (c , ends0-inv e , sync-lt (ends0-inv e) lt , refl)
    st1 (freed _ (inj₂ ()))
    st1 (queued _ lt (inj₁ (c , e , refl)) _ _) = inj₂ (c , ends0-inv e , sync-gt (ends0-inv e) lt , refl)
    st1 (queued _ _ (inj₂ ()) _ _)

    -- No end before the cold's own.
    notK : ∀ {c} → (c , end) ∈ J → ¬ Kth (_≺ c) (Sched 1) 0
    notK {c} y (inj₁ (c′ , e , lt)) = ≺-≢ {c′} {c} lt (walk-end K c₀ m (ends0-inv e) y)
    notK y (inj₂ ())

    fr-s : ∀ {c} → (c , end) ∈ J → sync c ≡ true → Starts 1 (C₀ ⊕ [ ix 1 ]) (Sched 1) (C₀ ⊕ [ ix 1 ] ⊕ [ ix 1 ])
    fr-s {c} y s = freed (s≤s z≤n) (inj₁ (c , e0 y , early y s))

    qu-s : ∀ {c} → (c , end) ∈ J → sync c ≡ false → Starts 1 (C₀ ⊕ [ ix 1 ]) (Sched 1) (c ⊕ [ ix 1 ])
    qu-s {c} y s = queued (s≤s z≤n) (late-C1 y s) (inj₁ (c , e0 y , refl)) (inj₁ (c , e0 y , ≼-refl {c})) (notK y)

  ------------------------------------------------------------------------
  -- Each lane's rows

  data LV : Pos → Bool → Pos → Ev (Tag A) → Set where
    v-val : ∀ {y a} → (y , out a) ∈ J → LV (C₀ ⊕ [ ix 0 ]) true y (out (val a))
    v-skp : ∀ {y} → (y , skip) ∈ J → LV (C₀ ⊕ [ ix 0 ]) true y skip
    v-end : ∀ {c} → (c , end) ∈ J → LV (C₀ ⊕ [ ix 0 ]) true c end
    f-d   : ∀ {c} → (c , end) ∈ J → sync c ≡ true → LV (C₀ ⊕ [ ix 1 ]) false (C₀ ⊕ [ ix 1 ] ⊕ [ ix 1 ] ⊕ [ ix 0 ]) (out cdone)
    f-e   : ∀ {c} → (c , end) ∈ J → sync c ≡ true → LV (C₀ ⊕ [ ix 1 ]) false (C₀ ⊕ [ ix 1 ] ⊕ [ ix 1 ] ⊕ [ last ]) end
    q-d   : ∀ {c} → (c , end) ∈ J → sync c ≡ false → LV (C₀ ⊕ [ ix 1 ]) false (c ⊕ [ ix 1 ] ⊕ [ ix 0 ]) (out cdone)
    q-e   : ∀ {c} → (c , end) ∈ J → sync c ≡ false → LV (C₀ ⊕ [ ix 1 ]) false (c ⊕ [ ix 1 ] ⊕ [ last ]) end

  private
    l0v : ∀ {k e} → MapT val (TR (listC K n (cold (fixed m)) ρ c₀)) k e → LV (C₀ ⊕ [ ix 0 ]) true k e
    l0v (map-out y)  = v-val (cold-to y)
    l0v (map-skip y) = v-skp (cold-to y)
    l0v (map-end y)  = v-end (cold-to y)
    l0v (map-pin y)  = ⊥-elim (walk-nopin K (start c₀ m) (cold-to y))

    l1f : ∀ {c k e} → (c , end) ∈ J → sync c ≡ true → Of1 (C₀ ⊕ [ ix 1 ] ⊕ [ ix 1 ]) (cdone {A}) k e → LV (C₀ ⊕ [ ix 1 ]) false k e
    l1f y s o₀ = f-d y s
    l1f y s oₑ = f-e y s

    l1q : ∀ {c k e} → (c , end) ∈ J → sync c ≡ false → Of1 (c ⊕ [ ix 1 ]) (cdone {A}) k e → LV (C₀ ⊕ [ ix 1 ]) false k e
    l1q y s o₀ = q-d y s
    l1q y s oₑ = q-e y s

    lv′ : ∀ {i q a s k e} → NthV i q a → Starts i q (Sched i) s → After (fD a) s k e → LV q a k e
    lv′ nv₀ (room _) ((x , _) , _) = l0v (l₀-to x)
    lv′ nv₀ (freed () _) _
    lv′ nv₀ (queued () _ _ _ _) _
    lv′ nv₁ st ((x , _) , _) with st1 st
    ... | inj₁ (c , y , s , refl) = l1f y s (o1-to x)
    ... | inj₂ (c , y , s , refl) = l1q y s (o1-to x)

  lv : ∀ {q a k e} → Lane q a k e → LV q a k e
  lv (i , s , (nt , st) , aft) = lv′ (nth-inv nt) st aft

  vl : ∀ {q a k e} → LV q a k e → Lane q a k e
  vl (v-val y)       = 0 , c₀ , (nth₀ , room (s≤s z≤n)) , aft₀ (l₀-fr (map-out (cold-fr y))) (past y)
  vl (v-skp y)       = 0 , c₀ , (nth₀ , room (s≤s z≤n)) , aft₀ (l₀-fr (map-skip (cold-fr y))) (past y)
  vl (v-end y)       = 0 , c₀ , (nth₀ , room (s≤s z≤n)) , aft₀ (l₀-fr (map-end (cold-fr y))) (past y)
  vl (f-d y s)       = 1 , _ , (nth₁ , fr-s y s) , aft₁ {C₀ ⊕ [ ix 1 ] ⊕ [ ix 1 ]} (o1-fr o₀) (down (C₀ ⊕ [ ix 1 ] ⊕ [ ix 1 ]) (ix 0))
  vl (f-e y s)       = 1 , _ , (nth₁ , fr-s y s) , aft₁ {C₀ ⊕ [ ix 1 ] ⊕ [ ix 1 ]} (o1-fr oₑ) (down (C₀ ⊕ [ ix 1 ] ⊕ [ ix 1 ]) last)
  vl (q-d {c} y s)   = 1 , _ , (nth₁ , qu-s y s) , aft₁ {c ⊕ [ ix 1 ]} (o1-fr o₀) (down (c ⊕ [ ix 1 ]) (ix 0))
  vl (q-e {c} y s)   = 1 , _ , (nth₁ , qu-s y s) , aft₁ {c ⊕ [ ix 1 ]} (o1-fr oₑ) (down (c ⊕ [ ix 1 ]) last)

  ------------------------------------------------------------------------
  -- Hand-offs and ends

  private
    -- Where a lane is queued past: the cold's later end, nowhere else
    -- one could end.
    queued-inv : ∀ {c} → Queued c → c ≡ C₀ ⊕ [ ix 0 ] ⊎ c ≡ C₀ ⊕ [ ix 1 ] ⊎ ((c , end) ∈ J × sync c ≡ false)
    queued-inv (i , q , a , nt , st) = go (nth-inv nt) st
      where
        go : ∀ {i q a c} → NthV i q a → Starts i q (Sched i) (c ⊕ [ ix 1 ]) → _
        go nv₀ st = inj₁ (⊕1-inj (st0 st))
        go nv₁ st with st1 st
        ... | inj₁ (_ , _ , _ , e) = inj₂ (inj₁ (⊕1-inj e))
        ... | inj₂ (c′ , y , s , e) with ⊕1-inj e
        ...   | refl = inj₂ (inj₂ (y , s))

    queuedAt : ∀ {c} → (c , end) ∈ J → sync c ≡ false → Queued c
    queuedAt y s = 1 , C₀ ⊕ [ ix 1 ] , false , nth₁ , qu-s y s

    C0≺ : ∀ {c e} → (c , e) ∈ J → (C₀ ⊕ [ ix 0 ]) ≺ c
    C0≺ {c} y = ≺-trans {C₀ ⊕ [ ix 0 ]} {c₀} {c} C0c₀ (past y)

    noQ-s : ∀ {c} → (c , end) ∈ J → sync c ≡ true → ¬ Queued c
    noQ-s {c} y s qd with queued-inv qd
    ... | inj₁ e           = ≺-≢ (C0≺ y) (sym e)
    ... | inj₂ (inj₁ e)    = ≺-≢ (early y s) e
    ... | inj₂ (inj₂ (_ , s′)) = tf (trans (sym s) s′)

    noQ-f : ∀ {c} → (c , end) ∈ J → sync c ≡ true → ¬ Queued (C₀ ⊕ [ ix 1 ] ⊕ [ ix 1 ] ⊕ [ last ])
    noQ-f y s qd with queued-inv qd
    ... | inj₁ e           = ≺-≢ (≺-trans {C₀ ⊕ [ ix 0 ]} {C₀ ⊕ [ ix 1 ]} {C₀ ⊕ [ ix 1 ] ⊕ [ ix 1 ] ⊕ [ last ]} lt01 (dn2 (C₀ ⊕ [ ix 1 ]) (ix 1) last)) (sym e)
    ... | inj₂ (inj₁ e)    = ≺-≢ (dn2 (C₀ ⊕ [ ix 1 ]) (ix 1) last) (sym e)
    ... | inj₂ (inj₂ (_ , s′)) = tf (trans (sym (sync-at {C₀ ⊕ [ ix 1 ] ⊕ [ ix 1 ] ⊕ [ last ]} (inP (C₀ ⊕ [ ix 1 ] ⊕ [ ix 1 ]) last (inP (C₀ ⊕ [ ix 1 ]) (ix 1) (inP C₀ (ix 1) C₀-in))))) s′)

    noQ-q : ∀ {c} → (c , end) ∈ J → sync c ≡ false → ¬ Queued (c ⊕ [ ix 1 ] ⊕ [ last ])
    noQ-q {c} y s qd with queued-inv qd
    ... | inj₁ e           = ≺-≢ (≺-trans {C₀ ⊕ [ ix 0 ]} {c} {c ⊕ [ ix 1 ] ⊕ [ last ]} (C0≺ y) (dn2 c (ix 1) last)) (sym e)
    ... | inj₂ (inj₁ e)    = ≺-≢ (≺-trans {C₀ ⊕ [ ix 1 ]} {c} {c ⊕ [ ix 1 ] ⊕ [ last ]} (late-C1 y s) (dn2 c (ix 1) last)) (sym e)
    ... | inj₂ (inj₂ (y′ , _)) = ≺-≢ (dn2 c (ix 1) last) (walk-end K c₀ m y y′)

    over-at : ∀ {c} → Ended O c → (C₀ ⊕ [ last ]) ≼ c
    over-at (c₁ , x , le) with o-to x
    ... | oₑ = le

    -- Ended in the burst: every part is over by the outer's end.
    doneL : ∀ {c} → (c , end) ∈ J → sync c ≡ true → Done (C₀ ⊕ [ last ])
    doneL {c} y s = (C₀ ⊕ [ last ] , o-fr oₑ , ≼-refl {C₀ ⊕ [ last ]}) , ends
      where
        ends : ∀ {q a} → O q (out a) → Indexed q → q ≺ (C₀ ⊕ [ last ]) → ¬ ⊥ → Ended (Lane q a) (C₀ ⊕ [ last ])
        ends x _ _ _ with o-to x
        ... | o₀ = c , vl (v-end y) , ≺→≼ {c} {C₀ ⊕ [ last ]} (≺-trans {c} {C₀ ⊕ [ ix 1 ]} {C₀ ⊕ [ last ]} (early y s) lt1L)
        ... | o₁ = _ , vl (f-e y s) , ≺→≼ {C₀ ⊕ [ ix 1 ] ⊕ [ ix 1 ] ⊕ [ last ]} {C₀ ⊕ [ last ]} lt11L

    -- Ended later: every part is over by the tag's end.
    doneQ : ∀ {c} → (c , end) ∈ J → sync c ≡ false → Done (c ⊕ [ ix 1 ] ⊕ [ last ])
    doneQ {c} y s = (C₀ ⊕ [ last ] , o-fr oₑ , ≺→≼ {C₀ ⊕ [ last ]} {c ⊕ [ ix 1 ] ⊕ [ last ]}
                       (≺-trans {C₀ ⊕ [ last ]} {c} {c ⊕ [ ix 1 ] ⊕ [ last ]} (late-CL y s) (dn2 c (ix 1) last))) , ends
      where
        ends : ∀ {q a} → O q (out a) → Indexed q → q ≺ (c ⊕ [ ix 1 ] ⊕ [ last ]) → ¬ ⊥ → Ended (Lane q a) (c ⊕ [ ix 1 ] ⊕ [ last ])
        ends x _ _ _ with o-to x
        ... | o₀ = c , vl (v-end y) , ≺→≼ {c} {c ⊕ [ ix 1 ] ⊕ [ last ]} (dn2 c (ix 1) last)
        ... | o₁ = _ , vl (q-e y s) , ≼-refl {c ⊕ [ ix 1 ] ⊕ [ last ]}

    -- The outer's end, given the cold's lane is over by it.
    out-end : Done (C₀ ⊕ [ last ]) → Σ Pos λ c → (c , end) ∈ J × sync c ≡ true
    out-end D with proj₂ D (o-fr o₀) idx₀ lt0L (λ ())
    ... | c , l , le with lv l
    ...   | v-end y with sync-or c
    ...     | inj₁ s = c , y , s
    ...     | inj₂ s = ⊥-elim (le (late-CL y s))

    all-late : ¬ Done (C₀ ⊕ [ last ]) → ∀ {c} → (c , end) ∈ J → sync c ≡ false
    all-late nD {c} y with sync-or c
    ... | inj₂ s = s
    ... | inj₁ s = ⊥-elim (nD (doneL y s))

    lane-to : ∀ {q a k e} → LV q a k e → Work e → CatRow k e
    lane-to (v-val y) _ = k-val y
    lane-to (v-skp y) _ = k-skp y
    lane-to (v-end _) ()
    lane-to (f-d y s) _ = ks-d y s
    lane-to (f-e _ _) ()
    lane-to (q-d y s) _ = ka-d y s
    lane-to (q-e _ _) ()

    lend-to : ∀ {q a c} → LV q a c end → ¬ Queued c → Done c → CatRow c end
    lend-to (v-end {c} y) nH D with sync-or c
    ... | inj₁ s = ⊥-elim (over-at {c} (proj₁ D) (≺-trans {c} {C₀ ⊕ [ ix 1 ]} {C₀ ⊕ [ last ]} (early y s) lt1L))
    ... | inj₂ s = ⊥-elim (nH (queuedAt y s))
    lend-to (f-e y s) _ D = ⊥-elim (over-at {C₀ ⊕ [ ix 1 ] ⊕ [ ix 1 ] ⊕ [ last ]} (proj₁ D) lt11L)
    lend-to (q-e y s) _ _ = ka-e y s

    lpass-to : ∀ {q a c} → LV q a c end → ¬ Queued c → ¬ Done c → CatRow c skip
    lpass-to (v-end {c} y) nH _ with sync-or c
    ... | inj₁ s = ks-c y s
    ... | inj₂ s = ⊥-elim (nH (queuedAt y s))
    lpass-to (f-e y s) _ _  = ks-k y s
    lpass-to (q-e y s) _ nD = ⊥-elim (nD (doneQ y s))

    hand-to : ∀ {q a c} → LV q a c end → Queued c → CatRow (c ⊕ [ ix 0 ]) skip
    hand-to (v-end {c} y) H with sync-or c
    ... | inj₂ s = ka-h y s
    ... | inj₁ s = ⊥-elim (noQ-s y s H)
    hand-to (f-e y s) H = ⊥-elim (noQ-f y s H)
    hand-to (q-e y s) H = ⊥-elim (noQ-q y s H)

  ------------------------------------------------------------------------
  -- The concat's rows are `CatRow`'s

  cat-to : ∀ {k e} → JoinT k e → CatRow k e
  cat-to (val x) with o-to x
  ... | o₀ = k-v₀
  ... | o₁ = k-v₁
  cat-to (step x) with o-to x
  ... | ()
  cat-to (opin x) with o-to x
  ... | ()
  cat-to (oend x D) with o-to x
  ... | oₑ with out-end D
  ...   | _ , y , s = ks-e y s
  cat-to (opass x nD) with o-to x
  ... | oₑ = ka-p (all-late nD)
  cat-to (lane x _ l _ w)       = lane-to (lv l) w
  cat-to (lend x _ l _ nH D)    = lend-to (lv l) nH D
  cat-to (lpass x _ l _ nH nD)  = lpass-to (lv l) nH nD
  cat-to (hand x _ l _ H)       = hand-to (lv l) H
  cat-to (left x _ l _ _) with lv l
  ... | ()
  cat-to (run () _)
  cat-to (rend () _ _)
  cat-to (rpass () _ _)
  cat-to (rhand () _)

  cat-fr : ∀ {k e} → CatRow k e → JoinT k e
  cat-fr k-v₀        = val (o-fr o₀)
  cat-fr k-v₁        = val (o-fr o₁)
  cat-fr (k-val y)   = lane (o-fr o₀) idx₀ (vl (v-val y)) (λ ()) tt
  cat-fr (k-skp y)   = lane (o-fr o₀) idx₀ (vl (v-skp y)) (λ ()) tt
  cat-fr (ks-c {c} y s) = lpass (o-fr o₀) idx₀ (vl (v-end y)) (λ ()) (noQ-s y s)
                            (λ D → over-at {c} (proj₁ D) (≺-trans {c} {C₀ ⊕ [ ix 1 ]} {C₀ ⊕ [ last ]} (early y s) lt1L))
  cat-fr (ks-d y s)  = lane (o-fr o₁) idx₁ (vl (f-d y s)) (λ ()) tt
  cat-fr (ks-k y s)  = lpass (o-fr o₁) idx₁ (vl (f-e y s)) (λ ()) (noQ-f y s) (λ D → over-at {C₀ ⊕ [ ix 1 ] ⊕ [ ix 1 ] ⊕ [ last ]} (proj₁ D) lt11L)
  cat-fr (ks-e y s)  = oend (o-fr oₑ) (doneL y s)
  cat-fr (ka-h y s)  = hand (o-fr o₀) idx₀ (vl (v-end y)) (λ ()) (queuedAt y s)
  cat-fr (ka-d y s)  = lane (o-fr o₁) idx₁ (vl (q-d y s)) (λ ()) tt
  cat-fr (ka-e y s)  = lend (o-fr o₁) idx₁ (vl (q-e y s)) (λ ()) (noQ-q y s) (doneQ y s)
  cat-fr (ka-p al)   = opass (o-fr oₑ) (λ D → let (_ , y , s) = out-end D in tf (trans (sym s) (al y)))

  cat-rows : ∀ {k e} → TR (listC K n catted ρ C₀) k e ⇔ CatRow k e
  cat-rows = mk⇔ (λ x → cat-to (Equivalence.to (bounded-tr K n 1 fC (of (true ∷ false ∷ [])) uρ C₀) x))
                 (λ x → Equivalence.from (bounded-tr K n 1 fC (of (true ∷ false ∷ [])) uρ C₀) (cat-fr x))
