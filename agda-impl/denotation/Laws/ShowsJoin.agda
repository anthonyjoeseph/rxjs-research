{-# OPTIONS --guardedness #-}

-- A JOINER SHOWS ITS HANGS: a fan of the outer's rows, each moved at most
-- one step down, and a lane for each value it runs, past the value.  A
-- lane keeps its rows until it is cut, a cut being past a later bad
-- position, and its pins past the cut whose connect it made before it.
module denotation.Laws.ShowsJoin where

open import Data.Bool using (T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Nullary using (¬_)

open import denotation.Position using (Pos; ix; inside; _⊕_)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; EmissionSet; _≺_; _≼_; Few; Reach; Den; enter; Ended; LaneOf;
  module Joining; module Merge; module Switch; module Exhaust; module Bounded; module Op)
open import Tree using (mergeᶠ; switchᶠ; exhaustᶠ)
open import Data.Maybe using (nothing; just)
open import denotation.Laws.Modulus using (≺-trans; ≺-ext; entered-reach; entered-few)
open import denotation.Laws.Worlds using (Ok; InvAt; InvD; world-after; ok-step; ok-in; full; _⊑_; ⊑-refl; inside-⊑; conv)
open import denotation.Laws.Worlds.Leaves using (out-inj)
open import denotation.Laws.BoundedInv using (module BoundedI)
open import denotation.Laws.Count using (em)
open import denotation.Laws.Shows using (ShowsK; _⊆ᵖ_; Step; sk-same; sk-down; sk-∪; sk-left; sk-fan; sk-step; sk-trunc)

------------------------------------------------------------------------
-- A joiner, by its parts

module Fanned {A B : Set} {n : ℕ} (Lane : Pos → A → EmissionSet B) (o : EmissionSet A)
              (Runs : Pos → Set) (Cut : Pos → Pos → Set) (Hand : Pos → Set) (Bad : Pos → Pos → Set)
              (cut-bad : ∀ {q k} → Cut q k → Σ Pos λ c → Bad q c × c ≺ k)
              (bad-cut : ∀ {q c k} → Bad q c → c ≺ k → Cut q k)
              (few-bad : ∀ {q c} → Bad q c → Σ (List Pos) λ L → ∀ {c′} → Bad q c′ → c′ ≺ c → c′ ∈ L)
              (o-func : ∀ {q a a′} → o q (out a) → o q (out a′) → a ≡ a′)
              (past : ∀ {q a k e} → o q (out a) → Runs q → Lane q a k e → q ≺ k)
              (reach : ∀ {q a k e} → o q (out a) → Runs q → Lane q a k e → Reach (Lane q a) k e)
              (sk-o : ShowsK n o)
              (sk-l : ∀ {q a} → o q (out a) → Runs q → ShowsK n (Lane q a)) where
  open Joining Lane o (λ _ _ → ⊥) (Ended o) Runs Cut Hand

  -- The outer's rows.
  IsOut : ∀ {q e} → JoinT q e → Set
  IsOut (val _)     = ⊤
  IsOut (step _)    = ⊤
  IsOut (opin _)    = ⊤
  IsOut (oend _ _)  = ⊤
  IsOut (opass _ _) = ⊤
  IsOut _           = ⊥

  -- The rows of the lane for the value at `s`.
  IsLn : Pos → ∀ {q e} → JoinT q e → Set
  IsLn s (lane {q} _ _ _ _ _)    = q ≡ s
  IsLn s (lend {q} _ _ _ _ _ _)  = q ≡ s
  IsLn s (lpass {q} _ _ _ _ _ _) = q ≡ s
  IsLn s (hand {q} _ _ _ _ _)    = q ≡ s
  IsLn s (left {q} _ _ _ _ _)    = q ≡ s
  IsLn s _                       = ⊥

  Out : EmissionSet B
  Out q e = Σ (JoinT q e) IsOut

  Br : Pos → EmissionSet B
  Br s q e = Σ (JoinT q e) (IsLn s)

  split : ∀ {q e} (x : JoinT q e) → IsOut x ⊎ Σ Pos λ s → IsLn s x
  split (val _)                 = inj₁ tt
  split (step _)                = inj₁ tt
  split (opin _)                = inj₁ tt
  split (oend _ _)              = inj₁ tt
  split (opass _ _)             = inj₁ tt
  split (lane {q} _ _ _ _ _)    = inj₂ (q , refl)
  split (lend {q} _ _ _ _ _ _)  = inj₂ (q , refl)
  split (lpass {q} _ _ _ _ _ _) = inj₂ (q , refl)
  split (hand {q} _ _ _ _ _)    = inj₂ (q , refl)
  split (left {q} _ _ _ _ _)    = inj₂ (q , refl)
  split (run () _)
  split (rend () _ _)
  split (rpass () _ _)
  split (rhand () _)

  -- The outer, each row moved at most one step down.
  sk-out : ShowsK n Out
  sk-out = sk-step pre img sk-o
    where
      pre : ∀ {y e} → Out y e → ¬ ¬ Σ Pos λ z → Σ (Ev A) (o z) × Step z y
      pre (val x , _)     ¬p = ¬p (_ , (_ , x) , inj₂ refl)
      pre (step x , _)    ¬p = ¬p (_ , (_ , x) , inj₁ refl)
      pre (opin x , _)    ¬p = ¬p (_ , (_ , x) , inj₁ refl)
      pre (oend x _ , _)  ¬p = ¬p (_ , (_ , x) , inj₁ refl)
      pre (opass x _ , _) ¬p = ¬p (_ , (_ , x) , inj₁ refl)
      pre (lane _ _ _ _ _ , ())
      pre (lend _ _ _ _ _ _ , ())
      pre (lpass _ _ _ _ _ _ , ())
      pre (hand _ _ _ _ _ , ())
      pre (left _ _ _ _ _ , ())
      pre (run () _ , _)
      pre (rend () _ _ , _)
      pre (rpass () _ _ , _)
      pre (rhand () _ , _)

      img : ∀ {z e} → o z e → ¬ ¬ Σ Pos λ y → Σ (Ev B) (Out y) × Step z y
      img {e = out _} x ¬i = ¬i (_ , (_ , val x , tt) , inj₂ refl)
      img {e = skip}  x ¬i = ¬i (_ , (_ , step x , tt) , inj₁ refl)
      img {e = pin _} x ¬i = ¬i (_ , (_ , opin x , tt) , inj₁ refl)
      img {e = end}   x    = em (λ d ¬i → ¬i (_ , (_ , oend x d , tt) , inj₁ refl)) (λ nd ¬i → ¬i (_ , (_ , opass x nd , tt) , inj₁ refl))

  -- The value at `s` and its run, from any row of its lane.
  src : ∀ {s q e} → Br s q e → Σ A λ a → o s (out a) × Runs s
  src (lane x r _ _ _ , refl)    = _ , x , r
  src (lend x r _ _ _ _ , refl)  = _ , x , r
  src (lpass x r _ _ _ _ , refl) = _ , x , r
  src (hand x r _ _ _ , refl)    = _ , x , r
  src (left x r _ _ _ , refl)    = _ , x , r
  src (val _ , ())
  src (step _ , ())
  src (opin _ , ())
  src (oend _ _ , ())
  src (opass _ _ , ())
  src (run () _ , _)
  src (rend () _ _ , _)
  src (rpass () _ _ , _)
  src (rhand () _ , _)

  root : ∀ {s y e} → Br s y e → s ≺ y × Σ (Ev B) (Out (s ⊕ [ ix 0 ]))
  root (lane x r l _ _ , refl)        = past x r l , _ , val x , tt
  root (lend x r l _ _ _ , refl)      = past x r l , _ , val x , tt
  root (lpass x r l _ _ _ , refl)     = past x r l , _ , val x , tt
  root {s} (hand {c = c} x r l _ _ , refl) = ≺-trans {s} {c} {c ⊕ [ ix 0 ]} (past x r l) (≺-ext c []) , _ , val x , tt
  root (left x r l _ _ , refl)        = past x r l , _ , val x , tt
  root (val _ , ())
  root (step _ , ())
  root (opin _ , ())
  root (oend _ _ , ())
  root (opass _ _ , ())
  root (run () _ , _)
  root (rend () _ _ , _)
  root (rpass () _ _ , _)
  root (rhand () _ , _)

  -- One lane: kept before its cut, and its pins past it.
  module One {s a} (xs : o s (out a)) (rs : Runs s) where
    Kept : EmissionSet B
    Kept k e = Lane s a k e × (¬ Cut s k ⊎ Σ Pos λ r → e ≡ pin r × ¬ Cut s r × T (inside r k))

    Before : EmissionSet B
    Before k e = Lane s a k e × ¬ Cut s k

    Past : EmissionSet B
    Past k e = Lane s a k e × (Σ Pos λ r → e ≡ pin r × ¬ Cut s r × T (inside r k)) × Cut s k

    cut-up : ∀ {j k} → Cut s j → j ≺ k → Cut s k
    cut-up {j} {k} cj jk with cut-bad cj
    ... | c , b , cj′ = bad-cut b (≺-trans {c} {j} {k} cj′ jk)

    sk-before : ShowsK n Before
    sk-before = sk-down (λ x ¬l → ¬l (_ , proj₁ x)) (λ { (_ , nc) l kq ¬b → ¬b (_ , l , λ ck → nc (cut-up ck kq)) }) (sk-l xs rs)

    sk-past : ShowsK n Past
    sk-past = sk-left (Bad s) few-bad proj₁ tgt
      where
        tgt : ∀ {k e} → Past k e → Σ Pos λ r → e ≡ pin r × Reach (Lane s a) k (pin r) × (∀ {c} → Bad s c → r ≼ c) × ¬ ¬ (Σ Pos λ c → Bad s c × r ⊑ c)
        tgt {k} (l , (r , refl , nr , ins) , ck) = r , refl , reach xs rs l , early , led
          where
            early : ∀ {c} → Bad s c → r ≼ c
            early b cr = nr (bad-cut b cr)

            led : ¬ ¬ (Σ Pos λ c → Bad s c × r ⊑ c)
            led ¬l with cut-bad ck
            ... | c , b , ck′ = ¬l (c , b , conv (⊑-refl r) (early b) ck′ (inside-⊑ r k ins))

    sk-kept : ShowsK n Kept
    sk-kept = sk-∪ (λ { (l , nc) ¬k → ¬k (_ , l , inj₁ nc) }) (λ { (l , r , _) ¬k → ¬k (_ , l , inj₂ r) })
                   (λ { (l , inj₁ nc) ¬p → ¬p (inj₁ (_ , l , nc))
                      ; {k} (l , inj₂ r) → em (λ ck ¬p → ¬p (inj₂ (_ , l , r , ck))) (λ nc ¬p → ¬p (inj₁ (_ , l , nc))) })
                   sk-before sk-past

    fix : ∀ {a′ k e} → o s (out a′) → Lane s a′ k e → Lane s a k e
    fix {k = k} {e} x l = subst (λ b → Lane s b k e) (o-func x xs) l

    sk-lane : ShowsK n (Br s)
    sk-lane = sk-step pre img sk-kept
      where
        pre : ∀ {y e} → Br s y e → ¬ ¬ Σ Pos λ z → Σ (Ev B) (Kept z) × Step z y
        pre (lane x _ l nc _ , refl)    ¬p = ¬p (_ , (_ , fix x l , inj₁ nc) , inj₁ refl)
        pre (lend x _ l nc _ _ , refl)  ¬p = ¬p (_ , (_ , fix x l , inj₁ nc) , inj₁ refl)
        pre (lpass x _ l nc _ _ , refl) ¬p = ¬p (_ , (_ , fix x l , inj₁ nc) , inj₁ refl)
        pre (hand x _ l nc _ , refl)    ¬p = ¬p (_ , (_ , fix x l , inj₁ nc) , inj₂ refl)
        pre (left x _ l nr i , refl)    ¬p = ¬p (_ , (_ , fix x l , inj₂ (_ , refl , nr , i)) , inj₁ refl)
        pre (val _ , ())
        pre (step _ , ())
        pre (opin _ , ())
        pre (oend _ _ , ())
        pre (opass _ _ , ())
        pre (run () _ , _)
        pre (rend () _ _ , _)
        pre (rpass () _ _ , _)
        pre (rhand () _ , _)

        img : ∀ {z e} → Kept z e → ¬ ¬ Σ Pos λ y → Σ (Ev B) (Br s y) × Step z y
        img {e = end} (l , inj₁ nc) = em (λ h ¬i → ¬i (_ , (_ , hand xs rs l nc h , refl) , inj₂ refl))
          λ nh → em (λ d ¬i → ¬i (_ , (_ , lend xs rs l nc nh d , refl) , inj₁ refl)) (λ nd ¬i → ¬i (_ , (_ , lpass xs rs l nc nh nd , refl) , inj₁ refl))
        img {e = end}   (l , inj₂ (_ , () , _))
        img {e = out _} (l , inj₁ nc) ¬i = ¬i (_ , (_ , lane xs rs l nc tt , refl) , inj₁ refl)
        img {e = out _} (l , inj₂ (_ , () , _))
        img {e = skip}  (l , inj₁ nc) ¬i = ¬i (_ , (_ , lane xs rs l nc tt , refl) , inj₁ refl)
        img {e = skip}  (l , inj₂ (_ , () , _))
        img {e = pin _} (l , inj₁ nc) ¬i = ¬i (_ , (_ , lane xs rs l nc tt , refl) , inj₁ refl)
        img {e = pin _} (l , inj₂ (_ , refl , nr , i)) ¬i = ¬i (_ , (_ , left xs rs l nr i , refl) , inj₁ refl)

  sk-br : ∀ s → ShowsK n (Br s)
  sk-br s {v} fc = em {G = Few (Br s) v} (λ { (_ , xs , rs) → One.sk-lane xs rs fc }) (λ none ¬f → ¬f ([] , λ x _ → ⊥-elim (none (src x))))

  sk-join : ShowsK n JoinT
  sk-join = sk-fan Br (λ x ¬y → ¬y (_ , proj₁ x)) (λ x ¬y → ¬y (_ , proj₁ x)) parts root sk-out sk-br
    where
      parts : ∀ {q e} → JoinT q e → ¬ ¬ (Σ (Ev B) (Out q) ⊎ Σ Pos λ s → Σ (Ev B) (Br s q))
      parts x ¬c with split x
      ... | inj₁ i       = ¬c (inj₁ (_ , x , i))
      ... | inj₂ (s , i) = ¬c (inj₂ (s , _ , x , i))

------------------------------------------------------------------------
-- Each joiner

module Flat {A B H n} (d : Den A) (f : A → Den B) (Id : InvD H d) (If : ∀ a → InvD H (f a)) (p : Pos) (ok : Ok H p)
            (sk-o : ShowsK n (enter d p)) (sk-f : ∀ a s → Ok H s → ShowsK n (enter (f a) s)) where
  o : EmissionSet A
  o = enter d p

  Io : InvAt H p o
  Io = Id p ok

  o-func : ∀ {q a a′} → o q (out a) → o q (out a′) → a ≡ a′
  o-func x x′ = out-inj (InvAt.func Io x x′)

  few-out : ∀ {c a} → o c (out a) → Few o c
  few-out {c} {a} x = entered-few d p {e = out a} (λ {k} {e′} → full {q = c} {e = out a} tt {k} {e′}) x

  val-ok : ∀ {q a} → o q (out a) → Ok H (q ⊕ [ ix 1 ])
  val-ok {q} x = ok-step q (ok-in ok (InvAt.world Io x) (InvAt.real Io x))

  -- A lane at its value's second child.
  module Plain {Runs : Pos → Set} where
    past : ∀ {q a k e} → o q (out a) → Runs q → LaneOf f q a k e → q ≺ k
    past {q} {k = k} _ _ (_ , lt) = ≺-trans {q} {q ⊕ [ ix 1 ]} {k} (≺-ext q []) lt

    reach : ∀ {q a k e} → o q (out a) → Runs q → LaneOf f q a k e → Reach (LaneOf f q a) k e
    reach {q} {a} _ _ (y , _) with entered-reach (f a) (q ⊕ [ ix 1 ]) y
    ... | ks , h = ks , λ y′ lt dp → h (proj₁ y′) lt dp

    sk-lane : ∀ {q a} → o q (out a) → Runs q → ShowsK n (LaneOf f q a)
    sk-lane {q} {a} x _ = sk-same (λ y ¬e → ¬e (_ , proj₁ y)) (λ y ¬l → ¬l (_ , y , after y)) (sk-f a (q ⊕ [ ix 1 ]) (val-ok x))
      where
        after : ∀ {k e} → enter (f a) (q ⊕ [ ix 1 ]) k e → (q ⊕ [ ix 1 ]) ≺ k
        after y = world-after (InvAt.world I y) (InvAt.real I y) where I = If a (q ⊕ [ ix 1 ]) (val-ok x)

  sk-merge : ShowsK n (Merge.JoinT f o)
  sk-merge = Fanned.sk-join (LaneOf f) o (λ _ → ⊤) (λ _ _ → ⊥) (λ _ → ⊥) (λ _ _ → ⊥) (λ ()) (λ ()) (λ ())
                            o-func past reach sk-o sk-lane
    where open Plain {λ _ → ⊤}

  sk-switch : ShowsK n (Switch.JoinT f o)
  sk-switch = Fanned.sk-join (LaneOf f) o (λ _ → ⊤) (Switch.Cut f o) (λ _ → ⊥) Bad
                             cut-bad bad-cut few-bad o-func past reach sk-o sk-lane
    where
      open Plain {λ _ → ⊤}

      data Bad (q c : Pos) : Set where
        bad : ∀ {a′} → o c (out a′) → q ≺ c → Bad q c

      cut-bad : ∀ {q k} → Switch.Cut f o q k → Σ Pos λ c → Bad q c × c ≺ k
      cut-bad (q′ , a′ , x , qq′ , q′k) = q′ , bad x qq′ , q′k

      bad-cut : ∀ {q c k} → Bad q c → c ≺ k → Switch.Cut f o q k
      bad-cut {c = c} (bad x qc) ck = c , _ , x , qc , ck

      few-bad : ∀ {q c} → Bad q c → Σ (List Pos) λ L → ∀ {c′} → Bad q c′ → c′ ≺ c → c′ ∈ L
      few-bad (bad x _) with few-out x
      ... | ks , h = ks , λ { (bad x′ _) lt → h x′ lt }

  sk-exhaust : ShowsK n (Exhaust.JoinT f o)
  sk-exhaust = Fanned.sk-join (LaneOf f) o (Exhaust.Run f o) (λ _ _ → ⊥) (λ _ → ⊥) (λ _ _ → ⊥) (λ ()) (λ ()) (λ ())
                              o-func past reach sk-o sk-lane
    where open Plain {Exhaust.Run f o}

  module Bnd (m : ℕ) where
    open Bounded m f o using (Lane; Indexed; Queued; Starts; room; freed; queued; Sub; JoinT)
    open BoundedI ok m f If Io using (okS) renaming (sub-same to uniq)

    starts-past : ∀ {i q ls s} → Starts i q ls s → q ≺ s
    starts-past {q = q} (room _)    = ≺-ext q []
    starts-past {q = q} (freed _ _) = ≺-ext q []
    starts-past {q = q} (queued {c} _ qc _ _ _) = ≺-trans {q} {c} {c ⊕ [ ix 1 ]} qc (≺-ext c [])


    past : ∀ {q a k e} → o q (out a) → Indexed q → Lane q a k e → q ≺ k
    past {q} {k = k} _ _ (_ , s , (_ , st) , (_ , lt)) = ≺-trans {q} {s} {k} (starts-past st) lt

    reach : ∀ {q a k e} → o q (out a) → Indexed q → Lane q a k e → Reach (Lane q a) k e
    reach {q} {a} _ _ (_ , s , sb , (y , _)) with entered-reach (f a) s y
    ... | ks , h = ks , λ { (_ , s′ , sb′ , (y′ , _)) lt dp → h (back sb′ y′) lt dp }
      where
        back : ∀ {i′ s′ k′ e′} → Sub i′ q s′ a → enter (f a) s′ k′ e′ → enter (f a) s k′ e′
        back sb′ y′ with uniq sb sb′
        ... | refl = y′

    sk-lane : ∀ {q a} → o q (out a) → Indexed q → ShowsK n (Lane q a)
    sk-lane {q} {a} _ _ {v} fc = em {G = Few (Lane q a) v} one (λ none ¬f → ¬f ([] , λ { (i , s , sb , _) _ → ⊥-elim (none (i , s , sb)) }))
      where
        one : (Σ ℕ λ i → Σ Pos λ s → Sub i q s a) → ¬ ¬ Few (Lane q a) v
        one (i , s , sb) = sk-same to back (sk-f a s (okS sb)) fc
          where
            to : Lane q a ⊆ᵖ enter (f a) s
            to (_ , s′ , sb′ , (y , _)) ¬e with uniq sb sb′
            ... | refl = ¬e (_ , y)

            back : enter (f a) s ⊆ᵖ Lane q a
            back y ¬l = ¬l (_ , i , s , sb , y , world-after (InvAt.world I y) (InvAt.real I y))
              where I = If a s (okS sb)

    sk-bounded : ShowsK n JoinT
    sk-bounded = Fanned.sk-join Lane o Indexed (λ _ _ → ⊥) Queued (λ _ _ → ⊥) (λ ()) (λ ()) (λ ())
                                o-func past reach sk-o sk-lane

  sk-flat : ∀ op → ShowsK n (enter (Op.flatMap op f d) p)
  sk-flat (mergeᶠ nothing)  = sk-trunc sk-merge
  sk-flat (mergeᶠ (just m)) = sk-trunc (Bnd.sk-bounded m)
  sk-flat switchᶠ           = sk-trunc sk-switch
  sk-flat exhaustᶠ          = sk-trunc sk-exhaust
