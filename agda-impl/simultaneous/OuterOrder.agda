{-# OPTIONS --guardedness #-}

-- THE ELABORATED OUTER READ AGAINST THE PLAIN: a flatMap's elaborated
-- joiner reads its outer's values off a hot of the elaborated source, one
-- reading lane per emit, each value on its lane's first row.  So every
-- elaborated value is a source value read at `Q l`, which the source's
-- carry reads back to a plain value in the same order; and a value read
-- before a carrier on a map embedding the source's carriers came before
-- the row carried there, unless that row lies over the value.
module simultaneous.OuterOrder where

open import Data.Bool.Properties using (T?)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; _∷_; []; [_]; _++_)
import Data.List as L
open import Data.List.Properties using (∷-injectiveˡ)
open import Data.List.Relation.Unary.Any using (Any; here; there)
import Data.List.Relation.Unary.Any as Any
open import Data.List.Relation.Unary.Any.Properties using (++⁺ˡ; ++⁺ʳ; concatMap⁺)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (decidable-stable)

open import denotation.Position using (Pos; ix; sub; last; _⊕_; _<ᵖ_)
open import denotation.Events using (ofᴱ)
open import denotation.EmissionSet using (out; end; skip; pin; EmissionSet; Truncate; Proper; Reach; Few; hot; enter; _≺_; InE; at-out;
  at-end; on-out; Rejoin; LaneOf; module Merge; module Op; module Values)
open import denotation.Laws.Worlds using (InvAt; Ok; W; W⁼; inW; step; plain-ix; ok-in; real-snoc; leads; same-lead; _⊑_; ⊑-refl;
  ⊑-snoc; ⊑-snoc⁺; ⊑-trans; ⊕-assoc; ⊕-identityʳ; ⊕-injˡ) renaming (here to here⁼)
open import denotation.Laws.Worlds.Leaves using (of-reach; ine-pin)
open import denotation.Laws.Modulus using (≺-irrefl; ≺-absurd; ≼-split; ≼-or-≻; ≼-antisym; ≺-ext; reach-few)
open import denotation.Laws.Count using (⊑?; Cov)
open import denotation.Laws.Shows using (cov-few; few-reach; lead-∈)
open import simultaneous.InstEmit using (InstEmit; instEmit; value; mark; valuesOf)
open import simultaneous.Attribution using (Live)
open import simultaneous.Listing using (Listed)
open import simultaneous.CarryBase using (PMap; _⊆ᴹ_; Emb; CarryAt; apart; module Mono)
open import simultaneous.JoinCarry using (unpin-few)
open import simultaneous.Rejoined using (rejoin-few; nest)

-- A value's second child is subscribed admissibly.
val-ok : ∀ {A H p} {o : EmissionSet A} → Ok H p → InvAt H p o → ∀ {q a} → o q (out a) → Ok H (q ⊕ [ ix 1 ])
val-ok okp Io {q} x = ok-in okp (step (inW (InvAt.world Io x)) plain-ix) (real-snoc q plain-ix (InvAt.real Io x))

-- NO LATER VALUE LEADS A ROW OF AN EARLIER VALUE'S CHILD'S WORLD: the
-- value lies in neither that world nor over the child.
value-off-lane : ∀ {A H p} {o : EmissionSet A} → Ok H p → InvAt H p o → ∀ {q a q′ a′ k}
               → o q (out a) → o q′ (out a′) → q ≺ q′ → W H (q ⊕ [ ix 1 ]) k → q′ ⊑ k → ⊥
value-off-lane okp Io {q} {q′ = q′} x x′ qq w le =
  leads (proj₂ okp) (InvAt.world Io x′) (λ w⁼ → InvAt.under Io x x′ plain-ix w⁼ (⊑-refl q′)) over (inW w) le
  where
    over : q′ ⊑ (q ⊕ [ ix 1 ]) → ⊥
    over le′ with ⊑-snoc q le′
    ... | inj₁ lq   = ≺-irrefl {q} (subst (q ≺_) (same-lead Io x′ x lq) qq)
    ... | inj₂ refl = InvAt.under Io x x′ plain-ix here⁼ (⊑-refl q′)

module Read {N A : Set} {HP HE LP : Pos → Set} (q₁ : Pos) {p s′ : Pos} {o : EmissionSet A} (Io : InvAt HP p o)
            {σ : EmissionSet (InstEmit N A)} (Iσ : InvAt HE s′ σ) (reachσ : ∀ {l e} → σ l e → Reach σ l e)
            (reacho : ∀ {l e} → o l e → Reach o l e) (q₁σ : ∀ {l e} → σ l e → q₁ ≺ l)
            (M_s : PMap) (hm_s : Emb M_s) (c_s : CarryAt valuesOf M_s HP HE LP o σ p s′) where
  module S = CarryAt c_s

  -- Where the elaborated outer shows a value read at `l`.
  Q : Pos → Pos
  Q l = ((l ⊕ [ sub q₁ ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ]

  Q-eq : ∀ l → Q l ≡ l ⊕ (sub q₁ ∷ ix 1 ∷ ix 0 ∷ [])
  Q-eq l = trans (⊕-assoc (l ⊕ [ sub q₁ ]) [ ix 1 ] [ ix 0 ]) (⊕-assoc l [ sub q₁ ] (ix 1 ∷ ix 0 ∷ []))

  Q-path : ∀ l zs → Q (l ⊕ zs) ≡ l ⊕ (zs ++ sub q₁ ∷ ix 1 ∷ ix 0 ∷ [])
  Q-path l zs = trans (Q-eq (l ⊕ zs)) (⊕-assoc l zs (sub q₁ ∷ ix 1 ∷ ix 0 ∷ []))

  Q-inj : ∀ {l l′} → Q l ≡ Q l′ → l ≡ l′
  Q-inj {l} {l′} e = ⊕-injˡ l l′ (⊕-injˡ (l ⊕ [ sub q₁ ]) (l′ ⊕ [ sub q₁ ]) (⊕-injˡ ((l ⊕ [ sub q₁ ]) ⊕ [ ix 1 ]) ((l′ ⊕ [ sub q₁ ]) ⊕ [ ix 1 ]) e))

  -- Two of the source's rows, one before the other, are read in order.
  Q-mono : ∀ {l l′ e e′} → σ l e → σ l′ e′ → l ≺ l′ → Q l ≺ Q l′
  Q-mono {l} {l′} y y′ lt = subst₂ _≺_ (sym (Q-eq l)) (sym (Q-eq l′)) (apart lt nu (sub q₁ ∷ ix 1 ∷ ix 0 ∷ []) (sub q₁ ∷ ix 1 ∷ ix 0 ∷ []))
    where
      nu : ¬ (l ⊑ l′)
      nu ([] , refl)    = ≺-irrefl {l} (subst (l ≺_) (⊕-identityʳ l) lt)
      nu (_ ∷ _ , refl) = InvAt.flat Iσ y y′

  -- THE ELABORATED OUTER'S VALUES are its source's, each read on its
  -- reading lane's first row.
  module MJ = Merge (λ (x : InstEmit N A) → Op.of (valuesOf x)) (enter (hot (Proper σ)) q₁)

  O* : EmissionSet A
  O* = Truncate MJ.JoinT

  of-one : ∀ {s k a} (x : InstEmit N A) → InE (ofᴱ s 0 (valuesOf x)) k (out a) → valuesOf x ≡ a ∷ [] × k ≡ s ⊕ [ ix 0 ]
  of-one (instEmit (value _) _) at-out      = refl , refl
  of-one (instEmit (value _) _) (on-out ())
  of-one (instEmit (mark _) _) ()

  star-read : ∀ {q* a} → O* q* (out a) → Σ Pos λ l → Σ (InstEmit N A) λ x → Proper σ l (out x) × valuesOf x ≡ a ∷ [] × q* ≡ Q l
  star-read ((MJ.lane {a = x} (Rejoin.shown y _ _ , _) _ ((r , _) , _) _ _) , _) with of-one x r
  ... | vx , refl = _ , x , y , vx , refl
  star-read ((MJ.run () _) , _)

  -- Read back through the source's carry: few of its rows lie before
  -- any.
  read-back : ∀ {l x a} → Proper σ l (out x) → valuesOf x ≡ a ∷ [] → Σ Pos λ q′ → S.Img q′ l × o q′ (out a)
  read-back {l} {x} {a} y vx with S.shown (proj₁ y) (a , vx) tt (proj₂ y) (unpin-few {e = out x} tt (reachσ (proj₁ y)))
  ... | q′ , i′ , out b , x′ , m with proj₁ m tt
  ...   | _ , refl , vb = q′ , i′ , subst (λ z → o q′ (out z)) (∷-injectiveˡ (trans (sym vb) vx)) x′
  read-back y vx | q′ , i′ , end , x′ , m with proj₁ m tt
  ... | ()
  read-back y vx | q′ , i′ , skip , x′ , m  = ⊥-elim (proj₂ m (λ ()) (_ , vx))
  read-back y vx | q′ , i′ , pin _ , x′ , m = ⊥-elim (proj₂ m (λ ()) (_ , vx))

  module MS = Mono hm_s (λ {y} {e} {l} {ys} {e′} → InvAt.flat Io {y} {e} {l} {ys} {e′}) c_s

  -- Two values read in order were the outer's in order.
  value-order : ∀ {q q′ l₀ l′ e₀ e′} → S.Img q l₀ → S.Img q′ l′ → σ l₀ e₀ → σ l′ e′ → Q l₀ ≺ Q l′ → q ≺ q′
  value-order {q} {q′} {l₀} {l′} i₀ i′ y₀ y′ qq = decidable-stable (T? (q <ᵖ q′)) λ nq → go (≼-split {q′} {q} nq)
    where
      go : q′ ≺ q ⊎ q′ ≡ q → ⊥
      go (inj₂ e)  = ≺-irrefl {Q l₀} (subst (λ z → Q l₀ ≺ Q z) (sym (S.img-fun i₀ (subst (λ z → S.Img z l′) e i′))) qq)
      go (inj₁ lt) = ≺-absurd {Q l′} {Q l₀} (Q-mono y′ y₀ (MS.img-mono i′ i₀ lt)) qq

  -- A VALUE READ BEFORE A CARRIER came before the row carried there: on a
  -- map embedding the source's carriers, unless the row lies over the
  -- value.
  past-row : ∀ {M : PMap} → Emb M → M_s ⊆ᴹ M → ∀ {k y l q′ l′} → M k y → y ⊑ l → (k ⊑ q′ → ⊥) → S.Img q′ l′ → Q l′ ≺ l → q′ ≺ k
  past-row {M} hm ms {k} {y} {l} {q′} {l′} my (σ₀ , eq) off i′ lt = decidable-stable (T? (q′ <ᵖ k)) λ nk → over (≼-split {k} {q′} nk)
    where
      over : k ≺ q′ ⊎ k ≡ q′ → ⊥
      over (inj₂ e) = off (subst (k ⊑_) e ([] , sym (⊕-identityʳ k)))
      over (inj₁ kq) with S.ext i′
      ... | y′ , my′ , σ′ , eq′ with ⊑? y y′
      ...   | yes yy = off (Emb.reflect hm my (ms my′) yy)
      ...   | no ny  = ≺-absurd {l} {Q l′}
                         (subst₂ _≺_ (sym eq) (trans (sym (Q-path y′ σ′)) (cong Q (sym eq′)))
                           (apart (Emb.mono hm my (ms my′) kq) ny σ₀ (σ′ ++ sub q₁ ∷ ix 1 ∷ ix 0 ∷ []))) lt

  -- A SWITCH'S LANE IS CUT WHERE ITS PARTNER IS, read back: the elaborated
  -- value cutting it reads a plain one, in order.
  switch-read : ∀ {q l₀ a k l} → S.Img q l₀ → O* (Q l₀) (out a)
              → (Σ Pos λ q*′ → Σ A λ a′ → O* q*′ (out a′) × Q l₀ ≺ q*′ × q*′ ≺ l)
              → (∀ {q′ a′ l′} → o q′ (out a′) → S.Img q′ l′ → Q l′ ≺ l → q′ ≺ k)
              → Σ Pos λ q′ → Σ A λ a′ → o q′ (out a′) × q ≺ q′ × q′ ≺ k
  switch-read i₀ x* (q*′ , a′ , x*′ , qq , ql) past with star-read x*′ | star-read x*
  ... | l′ , _ , y′ , vx , refl | l₁ , _ , y₁ , _ , e₁ with read-back y′ vx
  ...   | q′ , i′ , x′ = q′ , a′ , x′ , value-order i₀ i′ (subst (λ z → σ z _) (Q-inj (sym e₁)) (proj₁ y₁)) (proj₁ y′) qq , past x′ i′ ql

  -- WHERE THE MERGED OUTER'S ROWS LIE: each over a source row, one
  -- reading lane under it, its value first and its end last; or the late
  -- end.
  w : Pos → Pos
  w y = y ⊕ [ sub q₁ ]

  D : Pos → List Pos
  D y = (w y ⊕ [ ix 0 ]) ∷ ((w y ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) ∷ ((w y ⊕ [ ix 1 ]) ⊕ [ last ]) ∷ []

  KS : List Pos → List Pos
  KS ys = L.concatMap D ys ++ [ q₁ ⊕ [ last ] ]

  in-KS : ∀ {y ys k d} → y ∈ ys → d ∈ D y → k ⊑ d → Any (k ⊑_) (KS ys)
  in-KS m dm kd = ++⁺ˡ (concatMap⁺ D (Any.map (λ { refl → lead-∈ kd dm }) m))

  of-pos : ∀ {s k e} (x : InstEmit N A) → InE (ofᴱ s 0 (valuesOf x)) k e → k ≡ s ⊕ [ ix 0 ] ⊎ k ≡ s ⊕ [ last ]
  of-pos (instEmit (value _) _) at-out          = inj₁ refl
  of-pos (instEmit (value _) _) (on-out at-end) = inj₂ refl
  of-pos (instEmit (mark _) _)  at-end          = inj₂ refl

  -- A row over a source row before `Q l` is over one at or before `l`.
  before-l : ∀ {l e₀ y e k} → σ l e₀ → σ y e → w y ⊑ k → k ≺ Q l → y ≺ l ⊎ y ≡ l
  before-l {l} {y = y} y₀ yr (τ , refl) lt with ≼-or-≻ y l
  ... | inj₁ yl = ≼-split {y} {l} yl
  ... | inj₂ ly = ⊥-elim (≺-absurd {(y ⊕ [ sub q₁ ]) ⊕ τ} {Q l} lt
                    (subst₂ _≺_ (sym (Q-eq l)) (sym (⊕-assoc y [ sub q₁ ] τ))
                      (apart ly (nest (λ {y} {e} {l} {ys} {e′} → InvAt.flat Iσ {y} {e} {l} {ys} {e′}) y₀ yr ly) (sub q₁ ∷ ix 1 ∷ ix 0 ∷ []) (sub q₁ ∷ τ))))

  module Few* {l e₀} (y₀ : σ l e₀) (fσ : Few σ l) where
    ys : List Pos
    ys = l ∷ proj₁ fσ

    at-y : ∀ {y e k d} → σ y e → w y ⊑ k → k ≺ Q l → d ∈ D y → k ⊑ d → Any (k ⊑_) (KS ys)
    at-y yr wk lt dm kd with before-l y₀ yr wk lt
    ... | inj₁ yl   = in-KS {ys = ys} (there (proj₂ fσ yr yl)) dm kd
    ... | inj₂ refl = in-KS {ys = ys} (here refl) dm kd

    outer-cov : ∀ {k e} → Rejoin q₁ (Proper σ) k e → k ≺ Q l → Any (k ⊑_) (KS ys)
    outer-cov (Rejoin.shown yr _ _) lt = at-y (proj₁ yr) (⊑-refl _) lt (here refl) (⊑-snoc⁺ _)
    outer-cov (Rejoin.heard yr _)   lt = at-y (proj₁ yr) (⊑-refl _) lt (here refl) (⊑-snoc⁺ _)
    outer-cov (Rejoin.ended yr _)   lt = at-y (proj₁ yr) (⊑-refl _) lt (here refl) (⊑-snoc⁺ _)
    outer-cov (Rejoin.late _ _)     _  = ++⁺ʳ (L.concatMap D ys) (here (⊑-refl _))

    lane-cov : ∀ {y e k} → σ y e → k ≺ Q l → k ≡ (w y ⊕ [ ix 1 ]) ⊕ [ ix 0 ] ⊎ k ≡ (w y ⊕ [ ix 1 ]) ⊕ [ last ] → Any (k ⊑_) (KS ys)
    lane-cov {y} yr lt (inj₁ refl) = at-y yr (⊑-trans (⊑-snoc⁺ (w y)) (⊑-snoc⁺ (w y ⊕ [ ix 1 ]))) lt (there (here refl)) (⊑-refl _)
    lane-cov {y} yr lt (inj₂ refl) = at-y yr (⊑-trans (⊑-snoc⁺ (w y)) (⊑-snoc⁺ (w y ⊕ [ ix 1 ]))) lt (there (there (here refl))) (⊑-refl _)

    cov-J : ∀ {k e} → MJ.JoinT k e → k ≺ Q l → Cov (Q l) (KS ys) k
    cov-J (MJ.val (Rejoin.shown yr _ _ , _)) lt = inj₂ (at-y (proj₁ yr) (⊑-snoc⁺ _) lt (here refl) (⊑-refl _))
    cov-J (MJ.step (r , _)) lt                  = inj₂ (outer-cov r lt)
    cov-J (MJ.opin (r , _)) lt                  = inj₂ (outer-cov r lt)
    cov-J (MJ.oend (r , _) _) lt                = inj₂ (outer-cov r lt)
    cov-J (MJ.opass (r , _) _) lt               = inj₂ (outer-cov r lt)
    cov-J (MJ.lane {a = x} (Rejoin.shown yr _ _ , _) _ ((r , _) , _) _ _) lt    = inj₂ (lane-cov (proj₁ yr) lt (of-pos x r))
    cov-J (MJ.lend {a = x} (Rejoin.shown yr _ _ , _) _ ((r , _) , _) _ _ _) lt  = inj₂ (lane-cov (proj₁ yr) lt (of-pos x r))
    cov-J (MJ.lpass {a = x} (Rejoin.shown yr _ _ , _) _ ((r , _) , _) _ _ _) lt = inj₂ (lane-cov (proj₁ yr) lt (of-pos x r))
    cov-J (MJ.hand _ _ _ _ ()) _
    cov-J (MJ.left _ _ ((r , _) , _) _ _) _     = ⊥-elim (ine-pin r)
    cov-J (MJ.run () _) _
    cov-J (MJ.rend () _ _) _
    cov-J (MJ.rpass () _ _) _
    cov-J (MJ.rhand () _) _

    few-J : Few MJ.JoinT (Q l)
    few-J = cov-few {X = MJ.JoinT} {v = Q l} {ks = KS ys} cov-J

  -- THE ELABORATED OUTER SHOWS EVERY SOURCE VALUE, at `Q l`.
  star-row : ∀ {l x a} → Proper σ l (out x) → valuesOf x ≡ a ∷ [] → O* (Q l) (out a)
  star-row {l} {x} {a} y vx = MJ.lane ox tt ln (λ ()) tt , few-reach {e = out a} (Few*.few-J (proj₁ y) fσ)
    where
      fσ : Few σ l
      fσ = reach-few {e = out x} (λ {_} {_} → tt) (reachσ (proj₁ y))

      ox : Truncate (Rejoin q₁ (Proper σ)) (w l) (out x)
      ox = Rejoin.shown y tt (q₁σ (proj₁ y)) , few-reach {e = out x} (rejoin-few (λ {y} {e} {l} {ys} {e′} → InvAt.flat Iσ {y} {e} {l} {ys} {e′}) (proj₁ y) fσ)

      s : Pos
      s = w l ⊕ [ ix 1 ]

      ln : LaneOf (λ (z : InstEmit N A) → Op.of (valuesOf z)) (w l) x (s ⊕ [ ix 0 ]) (out a)
      ln = (subst (λ xs → InE (ofᴱ s 0 xs) (s ⊕ [ ix 0 ]) (out a)) (sym vx) at-out , of-reach s 0 (valuesOf x) {e = out a}) , ≺-ext s []

  live-o : ∀ {q a} → o q (out a) → Live o q
  live-o x tc cq with InvAt.quiet Io tc x cq
  ... | _ , () , _

  -- Read forward through the source's carry, classically: a plain value is
  -- a source value carried there.
  read-fwd : ∀ {q a} → o q (out a) → ¬ ¬ Σ Pos λ l → S.Img q l × Σ (InstEmit N A) λ x → Proper σ l (out x) × valuesOf x ≡ a ∷ []
  read-fwd {q} {a} x n = S.img¬¬ x tt (live-o x) (reach-few {e = out a} (λ {_} {_} → tt) (reacho x)) λ
    { (inj₁ (l , i , _ , y , m)) → go i y (proj₁ m tt)
    ; (inj₂ ()) }
    where
      go : ∀ {l e′} → S.Img q l → σ l e′ → Σ (InstEmit N A) (λ b → e′ ≡ out b × valuesOf b ≡ a ∷ []) → ⊥
      go i y (b , refl , vb) = n (_ , i , b , (y , S.live i (live-o x)) , vb)

  -- A LISTED VALUE IS SHOWN by the elaborated outer, where its carrier
  -- reads it.
  read-val : ∀ {q a} → o q (out a) → Listed o q → LP q → Σ Pos λ l → S.Img q l × O* (Q l) (out a)
  read-val x ls lp with S.img x tt (live-o x) ls lp
  ... | inj₁ (l , i , _ , y , _ , m) with proj₁ m tt
  ...   | _ , refl , vb = l , i , star-row (y , S.live i (live-o x)) vb
  read-val x ls lp | inj₂ (() , _)

  -- A VALUE BEFORE A CARRIER was read before the row carried there: on a
  -- map embedding the source's carriers, unless the value lies over the
  -- row.
  row-past : ∀ {M : PMap} → Emb M → M_s ⊆ᴹ M → ∀ {k y l q′ l′} → M k y → y ⊑ l → (q′ ⊑ k → ⊥) → S.Img q′ l′ → q′ ≺ k → Q l′ ≺ l
  row-past {M} hm ms {k} {y} {l} {q′} {l′} my (σ₀ , eq) off i′ qk with S.ext i′
  ... | y′ , my′ , σ′ , eq′ with ⊑? y′ y
  ...   | yes yy = ⊥-elim (off (Emb.reflect hm (ms my′) my yy))
  ...   | no ny  = subst₂ _≺_ (trans (sym (Q-path y′ σ′)) (cong Q (sym eq′))) (sym eq)
                     (apart (Emb.mono hm (ms my′) my qk) ny (σ′ ++ sub q₁ ∷ ix 1 ∷ ix 0 ∷ []) σ₀)

  -- A SWITCH'S LANE IS CUT WHERE ITS PARTNER IS, read forward: the plain
  -- value cutting it is carried to an elaborated one, in order.
  switch-fwd : ∀ {q l₀ a k l} → S.Img q l₀ → O* (Q l₀) (out a)
             → (Σ Pos λ q′ → Σ A λ a′ → o q′ (out a′) × q ≺ q′ × q′ ≺ k)
             → (∀ {q′ a′ l′} → o q′ (out a′) → q ≺ q′ → S.Img q′ l′ → q′ ≺ k → Q l′ ≺ l)
             → ¬ ¬ (Σ Pos λ q*′ → Σ A λ a′ → O* q*′ (out a′) × Q l₀ ≺ q*′ × q*′ ≺ l)
  switch-fwd i₀ x* (q′ , a′ , x′ , qq , qk) fwd n with star-read x*
  ... | l₁ , _ , y₁ , _ , e₁ = read-fwd x′ λ (l′ , i′ , _ , y′ , vx) →
        n (Q l′ , a′ , star-row y′ vx , Q-mono (subst (λ z → σ z _) (Q-inj (sym e₁)) (proj₁ y₁)) (proj₁ y′) (MS.img-mono i₀ i′ qq)
          , fwd x′ qq i′ qk)

  -- ONE VALUE PER CARRIER: the carry's image is injective.
  img-inj : ∀ {q q′ l} → S.Img q l → S.Img q′ l → q ≡ q′
  img-inj {q} {q′} {l} i i′ = ≼-antisym {q} {q′} (λ lt → ≺-irrefl {l} (MS.img-mono i′ i lt)) (λ lt → ≺-irrefl {l} (MS.img-mono i i′ lt))

  -- AN ELABORATED VALUE READS BACK a plain one, at its carrier.
  value-back : ∀ {q* a} → O* q* (out a) → Σ Pos λ q → Σ Pos λ l → o q (out a) × S.Img q l × q* ≡ Q l
  value-back x* with star-read x*
  ... | l , _ , y , vx , e with read-back y vx
  ...   | q , i , x = q , l , x , i , e

  module VO = Values o
  module V* = Values O*

  -- THE I-TH ELABORATED VALUE READS BACK THE I-TH PLAIN ONE: each value
  -- before or between is read forward classically, under the negation
  -- the order is.
  nth-back : ∀ {i q* a} → V*.Nth i q* a → Σ Pos λ l → q* ≡ Q l × Σ (InstEmit N A) (λ x → σ l (out x)) × Σ Pos λ q → S.Img q l × VO.Nth i q a
  nth-back (V*.first x* min*) with star-read x*
  ... | l , _ , y , vx , refl with read-back y vx
  ...   | q , i , x = l , refl , (_ , proj₁ y) , q , i , VO.first x λ xk kq → read-fwd xk λ (lk , ik , _ , yk , vk) →
          min* (star-row yk vk) (Q-mono (proj₁ yk) (proj₁ y) (MS.img-mono ik i kq))
  nth-back (V*.next n* x*′ lt nx*) with nth-back n* | star-read x*′
  ... | l , refl , (_ , y) , q , i , n | l′ , _ , y′ , vx′ , refl with read-back y′ vx′
  ...   | q′ , i′ , x′ = l′ , refl , (_ , proj₁ y′) , q′ , i′ ,
          VO.next n x′ (value-order i i′ y (proj₁ y′) lt) λ xk qk kq′ → read-fwd xk λ (lk , ik , _ , yk , vk) →
            nx* (star-row yk vk) (Q-mono y (proj₁ yk) (MS.img-mono i ik qk)) (Q-mono (proj₁ yk) (proj₁ y′) (MS.img-mono ik i′ kq′))

  nth-at : ∀ {j q l q* b} → S.Img q l → q* ≡ Q l → V*.Nth j q* b → VO.Nth j q b
  nth-at {j} {q} {l} {b = b} i refl n* with nth-back n*
  ... | l′ , eq , _ , q′ , i′ , n = subst (λ z → VO.Nth j z b) (img-inj (subst (S.Img q′) (sym (Q-inj eq)) i′) i) n
