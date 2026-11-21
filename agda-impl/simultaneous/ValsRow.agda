{-# OPTIONS --guardedness #-}

-- THE OUTER'S VALUES, READ THROUGH A HOT: a value row of the hot past the
-- reader's subscription, with few rows before it, shows its value a value
-- step below the hot's reading of it (`vals-at`).  Every row of the reading
-- before that lies under a hot row no later than it, at one of four steps,
-- or is the reading's own late end.
module simultaneous.ValsRow where

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-map⁺)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Maybe using (nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import Tree using (mergeᶠ)
open import denotation.Position using (Pos; ix; sub; last; _⊕_)
open import denotation.Events using (ofᴱ)
open import denotation.EmissionSet using (EmissionSet; Den; hot; enter; module Op; module Merge; Rejoin; shown; heard; ended; late;
  out; end; Ev; InE; at-out; on-out; at-end; Few; Ended; LaneOf; _≺_; _≼_)
open import simultaneous.DenRows using (merge-out; hot-out)
open import denotation.Laws.Modulus using (≺-ext; ≺-irrefl; ≺-trans; ≼-or-≻; ≼-split; ≺-≼-≺; ≺→≼; ≼-refl)
open import denotation.Laws.Worlds using (Lawful; _⊑_; ⊑-≼; ⊑-snoc⁺; ⊑-trans; ⊕-assoc; ⊕-identityʳ)
open import denotation.Laws.Worlds.Leaves using (of-reach)
open import denotation.Laws.Count using (child)
open import simultaneous.InstEmit using (InstEmit; instEmit; value; mark; valuesOf)

-- Past `v`, a position it does not lead lies past all of `v`'s extensions.
child* : ∀ {v q} ys → v ≺ q → v ⊑ q ⊎ (v ⊕ ys) ≺ q
child* {v} {q} []       vq = inj₂ (subst (_≺ q) (sym (⊕-identityʳ v)) vq)
child* {v} {q} (l ∷ ys) vq with child l vq
... | inj₁ vq′ = inj₁ vq′
... | inj₂ lt with child* {v ⊕ [ l ]} ys lt
...   | inj₁ lq  = inj₁ (⊑-trans (⊑-snoc⁺ v) lq)
...   | inj₂ lt′ = inj₂ (subst (_≺ q) (⊕-assoc v [ l ] ys) lt′)

module _ {N A : Set} (t : EmissionSet (InstEmit N A)) (Lt : Lawful t) (p : Pos) where

  private
    f : InstEmit N A → Den A
    f x = Op.of (valuesOf x)

    O : EmissionSet (InstEmit N A)
    O = enter (hot t) p

    module MJ = Merge f O

    deep : ∀ {k z} l → k ⊑ z → k ⊑ (z ⊕ [ l ])
    deep {z = z} l kz = ⊑-trans kz (⊑-snoc⁺ z)

    -- The four steps below a hot row its reading shows rows at.
    shapes : Pos → List Pos
    shapes k = (k ⊕ [ sub p ]) ∷ ((k ⊕ [ sub p ]) ⊕ [ ix 0 ]) ∷ (((k ⊕ [ sub p ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ])
             ∷ (((k ⊕ [ sub p ]) ⊕ [ ix 1 ]) ⊕ [ last ]) ∷ []

    rows : List Pos → List Pos
    rows []       = (p ⊕ [ last ]) ∷ []
    rows (k ∷ ks) = shapes k ++ rows ks

    rows-mem : ∀ {k ks z} → k ∈ ks → z ∈ shapes k → z ∈ rows ks
    rows-mem {ks = k′ ∷ ks} (here refl) i = ∈-++⁺ˡ i
    rows-mem {ks = k′ ∷ ks} (there j)   i = ∈-++⁺ʳ (shapes k′) (rows-mem j i)

    late-mem : ∀ ks → (p ⊕ [ last ]) ∈ rows ks
    late-mem []       = here refl
    late-mem (k ∷ ks) = ∈-++⁺ʳ (shapes k) (late-mem ks)

    -- A row of the reading lies one `sub` below a hot row, or is its late end.
    orow : ∀ {q e} → O q e → (Σ Pos λ k → Σ (Ev (InstEmit N A)) λ e′ → t k e′ × q ≡ k ⊕ [ sub p ]) ⊎ q ≡ p ⊕ [ last ]
    orow (shown tq _ _ , _) = inj₁ (_ , _ , tq , refl)
    orow (heard tq _ , _)   = inj₁ (_ , _ , tq , refl)
    orow (ended tc _ , _)   = inj₁ (_ , _ , tc , refl)
    orow (late _ _ , _)     = inj₂ refl

    orow-out : ∀ {q x} → O q (out x) → Σ Pos λ k → Σ (Ev (InstEmit N A)) λ e′ → t k e′ × q ≡ k ⊕ [ sub p ]
    orow-out (shown tq _ _ , _) = _ , _ , tq , refl

    -- A lane's rows: its value, then its end.
    of1 : ∀ (x : InstEmit N A) s {k e} → InE (ofᴱ s 0 (valuesOf x)) k e → k ≡ s ⊕ [ ix 0 ] ⊎ k ≡ s ⊕ [ last ]
    of1 (instEmit (value _) _) s at-out          = inj₁ refl
    of1 (instEmit (value _) _) s (on-out at-end) = inj₂ refl
    of1 (instEmit (mark _) _)  s at-end          = inj₂ refl

  -- A VALUE THE READING SHOWS PRECEDES ITS END, where every hot value row
  -- precedes every hot end.
  vals-before : (∀ {r x k} → t r (out x) → t k end → r ≺ k)
              → ∀ {q a c′} → enter (Op.flatMap (mergeᶠ nothing) f (hot t)) p q (out a) → enter (Op.flatMap (mergeᶠ nothing) f (hot t)) p c′ end → q ≺ c′
  vals-before pe {q} {a} {c′} xq xc with merge-out f (hot t) p xq
  ... | _ , x , hk , (l , _) , _ with hot-out hk
  ...   | k₀ , tk₀ , pk₀ , refl = from-end (oend-of (proj₁ xc))
    where
      k₀q : k₀ ⊑ q
      k₀q with of1 x ((k₀ ⊕ [ sub p ]) ⊕ [ ix 1 ]) l
      ... | inj₁ eq = sub p ∷ ix 1 ∷ ix 0 ∷ [] , trans eq (trans (⊕-assoc (k₀ ⊕ [ sub p ]) [ ix 1 ] [ ix 0 ]) (⊕-assoc k₀ [ sub p ] (ix 1 ∷ ix 0 ∷ [])))
      ... | inj₂ eq = sub p ∷ ix 1 ∷ last ∷ [] , trans eq (trans (⊕-assoc (k₀ ⊕ [ sub p ]) [ ix 1 ] [ last ]) (⊕-assoc k₀ [ sub p ] (ix 1 ∷ last ∷ [])))

      oend-of : MJ.JoinT c′ end → Σ Pos λ c₀ → O c₀ end × c₀ ≼ c′
      oend-of (MJ.oend oc _)                = c′ , oc , ≼-refl {c′}
      oend-of (MJ.lend _ _ _ _ _ (ov , _))  = ov
      oend-of (MJ.lane _ _ _ _ ())
      oend-of (MJ.run () _)
      oend-of (MJ.rend () _ _)

      before-k : ∀ {k} → t k end → q ≺ k
      before-k {k} tk with child* (proj₁ k₀q) (pe tk₀ tk)
      ... | inj₁ ([] , eq)      = ⊥-elim (≺-irrefl {k₀} (subst (k₀ ≺_) (trans eq (⊕-identityʳ k₀)) (pe tk₀ tk)))
      ... | inj₁ (_ ∷ _ , refl) = ⊥-elim (Lawful.flat Lt tk₀ tk)
      ... | inj₂ lt = subst (_≺ k) (sym (proj₂ k₀q)) lt

      from-end : (Σ Pos λ c₀ → O c₀ end × c₀ ≼ c′) → q ≺ c′
      from-end (_ , (ended {k} tk _ , _) , le) = ≺-≼-≺ {q} {k ⊕ [ sub p ]} {c′} (≺-trans {q} {k} {k ⊕ [ sub p ]} (before-k tk) (≺-ext k [])) le
      from-end (_ , (late {k} tk kp , _) , _)  = ⊥-elim (≺-irrefl {p} (≺-≼-≺ {p} {k} {p} (≺-trans {p} {k₀} {k} pk₀ (pe tk₀ tk)) kp))

  module _ {c e₀} (tc : t c e₀) (pc : p ≺ c) (fc : Few t c) where

    -- WHERE THE READING SHOWS `c`'s VALUE.
    W : Pos
    W = ((c ⊕ [ sub p ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ]

    private
      ks : List Pos
      ks = proj₁ fc

      K S : Pos
      K = c ⊕ [ sub p ]
      S = K ⊕ [ ix 1 ]

      cW : c ⊑ W
      cW = sub p ∷ ix 1 ∷ ix 0 ∷ [] , trans (⊕-assoc K [ ix 1 ] [ ix 0 ]) (⊕-assoc c [ sub p ] (ix 1 ∷ ix 0 ∷ []))

      -- A hot row leading a row before one under `c` is `c` or before it.
      cmp : ∀ {k e z w} → t k e → k ⊑ z → c ⊑ w → z ≺ w → k ∈ c ∷ ks
      cmp {k} {e} {z} {w} tk kz (zw , refl) lt with ≼-or-≻ k c
      ... | inj₁ kc with ≼-split {k} {c} kc
      ...   | inj₁ k<c = there (proj₂ fc tk k<c)
      ...   | inj₂ refl = here refl
      cmp {k} {e} {z} {w} tk kz (zw , refl) lt | inj₂ ck with child* zw ck
      ... | inj₁ ([] , eq)      = here (trans eq (⊕-identityʳ c))
      ... | inj₁ (_ ∷ _ , refl) = ⊥-elim (Lawful.flat Lt tc tk)
      ... | inj₂ wk = ⊥-elim (≺-irrefl {z} (≺-≼-≺ {z} {k} {z} (≺-trans {z} {c ⊕ zw} {k} lt wk) (⊑-≼ {k} {z} kz)))

      Hs : List Pos
      Hs = L.map (_⊕ [ sub p ]) ks ++ [ p ⊕ [ last ] ]

      one : ∀ {k e} → t k e → (k ⊕ [ sub p ]) ≺ K → (k ⊕ [ sub p ]) ∈ Hs
      one {k} tk lt with cmp tk (⊑-snoc⁺ k) (⊑-snoc⁺ c) lt
      ... | here refl = ⊥-elim (≺-irrefl {K} lt)
      ... | there i   = ∈-++⁺ˡ (∈-map⁺ (_⊕ [ sub p ]) i)

      hbefore : ∀ {k e′} → Rejoin p t k e′ → k ≺ K → k ∈ Hs
      hbefore (shown tq _ _) lt = one tq lt
      hbefore (heard tq _)   lt = one tq lt
      hbefore (ended tq _)   lt = one tq lt
      hbefore (late _ _)     lt = ∈-++⁺ʳ (L.map (_⊕ [ sub p ]) ks) (here refl)

      -- The hot row of `c` the reading shows, with few rows before it.
      hrow : ∀ {x} → e₀ ≡ out x → O K (out x)
      hrow eq = shown (subst (t c) eq tc) tt pc , Hs , λ r lt _ → hbefore r lt

      hend : e₀ ≡ end → O K end
      hend eq = ended (subst (t c) eq tc) pc , Hs , λ r lt _ → hbefore r lt

      at-hot : ∀ {k e z w} → c ⊑ w → t k e → k ⊑ z → z ≺ w → z ∈ shapes k → z ∈ rows (c ∷ ks)
      at-hot cw tk kz lt i = rows-mem (cmp tk kz cw lt) i

      at-o : ∀ {q e w} → c ⊑ w → O q e → q ≺ w → q ∈ rows (c ∷ ks)
      at-o cw oq lt with orow oq
      ... | inj₁ (k , _ , tk , refl) = at-hot cw tk (⊑-snoc⁺ k) lt (here refl)
      ... | inj₂ refl = late-mem (c ∷ ks)

      in-lane : ∀ {q x′ k e w} → c ⊑ w → O q (out x′) → InE (ofᴱ (q ⊕ [ ix 1 ]) 0 (valuesOf x′)) k e → k ≺ w → k ∈ rows (c ∷ ks)
      in-lane {x′ = x′} cw oq r lt with orow-out oq
      ... | k , _ , tk , refl with of1 x′ ((k ⊕ [ sub p ]) ⊕ [ ix 1 ]) r
      ...   | inj₁ refl = at-hot cw tk (deep (ix 0) (deep (ix 1) (⊑-snoc⁺ k))) lt (there (there (here refl)))
      ...   | inj₂ refl = at-hot cw tk (deep last (deep (ix 1) (⊑-snoc⁺ k))) lt (there (there (there (here refl))))

      -- Every row of the reading before one under `c` is one the hot rows up
      -- to `c` show.
      jbefore : ∀ {w k e′} → c ⊑ w → MJ.JoinT k e′ → k ≺ w → k ∈ rows (c ∷ ks)
      jbefore cw (MJ.val oq) lt with orow-out oq
      ... | k , _ , tk , refl = at-hot cw tk (deep (ix 0) (⊑-snoc⁺ k)) lt (there (here refl))
      jbefore cw (MJ.step oq)     lt = at-o cw oq lt
      jbefore cw (MJ.opin oq)     lt = at-o cw oq lt
      jbefore cw (MJ.oend oc _)   lt = at-o cw oc lt
      jbefore cw (MJ.opass oc _)  lt = at-o cw oc lt
      jbefore cw (MJ.lane oq _ ((r , _) , _) _ _)    lt = in-lane cw oq r lt
      jbefore cw (MJ.lend oq _ ((r , _) , _) _ _ _)  lt = in-lane cw oq r lt
      jbefore cw (MJ.lpass oq _ ((r , _) , _) _ _ _) lt = in-lane cw oq r lt
      jbefore cw (MJ.hand _ _ _ _ ())
      jbefore cw (MJ.left oq _ ((r , _) , _) _ _)    lt = in-lane cw oq r lt
      jbefore cw (MJ.run () _)
      jbefore cw (MJ.rend () _ _)
      jbefore cw (MJ.rpass () _ _)
      jbefore cw (MJ.rhand () _)

      -- A hot row read before `c`'s lies wholly before `c`.
      before-c : ∀ {k e} → t k e → (k ⊕ [ sub p ]) ≺ K → ∀ zs → (k ⊕ zs) ≺ c
      before-c {k} tk lt zs with ≼-or-≻ k c
      ... | inj₂ ck with child* [ sub p ] ck
      ...   | inj₁ ([] , eq)      = ⊥-elim (≺-irrefl {K} (subst (λ z → (z ⊕ [ sub p ]) ≺ K) (trans eq (⊕-identityʳ c)) lt))
      ...   | inj₁ (_ ∷ _ , refl) = ⊥-elim (Lawful.flat Lt tc tk)
      ...   | inj₂ Kk = ⊥-elim (≺-irrefl {K} (≺-trans {K} {k} {K} Kk (≺-trans {k} {k ⊕ [ sub p ]} {K} (≺-ext k []) lt)))
      before-c {k} tk lt zs | inj₁ kc with ≼-split {k} {c} kc
      ...   | inj₂ refl = ⊥-elim (≺-irrefl {K} lt)
      ...   | inj₁ k<c with child* zs k<c
      ...     | inj₁ ([] , eq)      = ⊥-elim (≺-irrefl {k} (subst (k ≺_) (trans eq (⊕-identityʳ k)) k<c))
      ...     | inj₁ (_ ∷ _ , eq)   = ⊥-elim (Lawful.flat Lt tk (subst (λ z → t z e₀) eq tc))
      ...     | inj₂ lt′ = lt′

      -- Each lane of a value read before `c`'s has ended by `c`'s reading.
      lane-end : ∀ (x′ : InstEmit N A) s → InE (ofᴱ s 0 (valuesOf x′)) (s ⊕ [ last ]) end
      lane-end (instEmit (value _) _) s = on-out at-end
      lane-end (instEmit (mark _) _)  s = at-end

      lanes-ended : ∀ {q x′} → O q (out x′) → q ≺ K → Ended (LaneOf f q x′) K
      lanes-ended {x′ = x′} oq lt with orow-out oq
      ... | k , _ , tk , refl =
        ((k ⊕ [ sub p ]) ⊕ [ ix 1 ]) ⊕ [ last ]
        , ((lane-end x′ ((k ⊕ [ sub p ]) ⊕ [ ix 1 ]) , of-reach ((k ⊕ [ sub p ]) ⊕ [ ix 1 ]) 0 (valuesOf x′) {((k ⊕ [ sub p ]) ⊕ [ ix 1 ]) ⊕ [ last ]} {end})
          , ≺-ext ((k ⊕ [ sub p ]) ⊕ [ ix 1 ]) [])
        , ≺→≼ {((k ⊕ [ sub p ]) ⊕ [ ix 1 ]) ⊕ [ last ]} {K}
            (≺-trans {((k ⊕ [ sub p ]) ⊕ [ ix 1 ]) ⊕ [ last ]} {c} {K}
              (subst (_≺ c) (sym (trans (⊕-assoc (k ⊕ [ sub p ]) [ ix 1 ] [ last ]) (⊕-assoc k [ sub p ] (ix 1 ∷ last ∷ [])))) (before-c tk lt (sub p ∷ ix 1 ∷ last ∷ [])))
              (≺-ext c []))

    -- THE READING SHOWS `c`'s VALUE AT `W`.
    vals-at : ∀ {a n} → e₀ ≡ out (instEmit (value a) n) → enter (Op.flatMap (mergeᶠ nothing) f (hot t)) p W (out a)
    vals-at {a} eq = MJ.lane (hrow eq) tt ((at-out , of-reach S 0 (a ∷ []) {S ⊕ [ ix 0 ]} {out a}) , ≺-ext S []) (λ ()) tt
                   , rows (c ∷ ks) , λ r lt _ → jbefore cW r lt

    -- THE READING ENDS WHERE IT READS `c`'s END.
    vals-end : e₀ ≡ end → enter (Op.flatMap (mergeᶠ nothing) f (hot t)) p (c ⊕ [ sub p ]) end
    vals-end eq = MJ.oend (hend eq) ((K , hend eq , ≼-refl {K}) , λ oq _ lt _ → lanes-ended oq lt)
                , rows (c ∷ ks) , λ r lt _ → jbefore (⊑-snoc⁺ c) r lt
