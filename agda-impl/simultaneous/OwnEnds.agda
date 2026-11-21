{-# OPTIONS --guardedness #-}

-- THE FLATMAP'S OWN BRANCHES, ALL ENDED, FAIL THE SOURCE'S TAKE: their
-- merge ends at the last branch end, the concat's closing `nothing`
-- starts there, and the trackers' merge passes it on in that instant.
module simultaneous.OwnEnds where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (s≤s; z≤n)
open import Data.List using ([]; _∷_; [_]; _++_)
open import Relation.Nullary using (¬_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans)

open import Tree using (mergeᶠ)
open import denotation.Position using (Pos; Path; ix; last; root; _≟ᵖ_; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (out; end; EmissionSet; Den; enter; Few; LaneOf; _≺_; _≼_; at-out; module Op;
  module TakeWhile; module Merge; module Bounded)
open import denotation.Laws.Modulus using (≺-trans; ≺-ext; ≺→≼; ≺-≼-≺; ≼-refl; ≼-trans; ≼-or-≻; ≺-irrefl)
open import denotation.Laws.Worlds using (⊕-assoc; Shows)
open import denotation.Laws.Worlds.Leaves using (of-reach; of-end-row)
open import denotation.Laws.Lift using (few-lift)
open import simultaneous.SObs using (lone; module Elaborate; Branch; outerB; laneB; closeB)
open import simultaneous.BranchSplit using (OwnOf; idx; of-at; of-own; module Spots)
open import simultaneous.HeldTrigger using (module Two)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Instants using (_≺ⁱ_; instant-≺)
open import simultaneous.TakeCut using (inst-⊕)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (Input; going)

module OwnEnds {B : Set} (F C : Bool → Den (Maybe (Input B))) (G : Branch → Den (Maybe (Input B))) (P : Pos)
               (eqF : F false ≡ Op.flatMap (mergeᶠ (just 1)) C (Op.of (true ∷ false ∷ [])))
               (eqC : C true ≡ Op.flatMap (mergeᶠ nothing) G (Op.of OwnOf))
               (eqN : C false ≡ Op.of (nothing ∷ [])) where
  open Spots P 0 using (q₁; S₂; s₃)

  module M4 = Merge G (enter (Op.of OwnOf) s₃)
  module B3 = Bounded 1 C (enter (Op.of (true ∷ false ∷ [])) S₂)
  module M2 = Merge F (enter (Op.of (true ∷ false ∷ [])) P)
  module TW = TakeWhile false going (enter (Op.flatMap (mergeᶠ nothing) F (Op.of (true ∷ false ∷ []))) P)

  private
    module O2 = Two S₂
    module O1 = Two P

  Own′ Cat′ Fed′ : EmissionSet (Maybe (Input B))
  Own′ = enter (Op.flatMap (mergeᶠ nothing) G (Op.of OwnOf)) s₃
  Cat′ = enter (Op.flatMap (mergeᶠ (just 1)) C (Op.of (true ∷ false ∷ []))) S₂
  Fed′ = enter (Op.flatMap (mergeᶠ nothing) F (Op.of (true ∷ false ∷ []))) P

  -- Positions under the subscription, and past all of it.
  Under : Pos → Set
  Under x = Σ Path λ ys → x ≡ P ⊕ ys

  Past : Pos → Set
  Past c = ∀ zs → (P ⊕ zs) ≺ c

  ext-u : ∀ {x} → Under x → ∀ zs → Under (x ⊕ zs)
  ext-u (ys , refl) zs = ys ++ zs , ⊕-assoc P ys zs

  past-u : ∀ {x c} → Under x → Past c → ∀ zs → (x ⊕ zs) ≺ c
  past-u {x} {c} u pc zs = subst (_≺ c) (sym (proj₂ (ext-u u zs))) (pc (proj₁ (ext-u u zs)))

  before : ∀ {x c} → Under x → Past c → x ≺ c
  before {x} {c} u pc = ≺-trans {x} {x ⊕ [ ix 0 ]} {c} (≺-ext x []) (past-u u pc [ ix 0 ])

  S₂-u : Under S₂
  S₂-u = ext-u ([ ix 1 ] , refl) [ ix 1 ]

  s₃-u : Under s₃
  s₃-u = ext-u (ext-u S₂-u [ ix 0 ]) [ ix 1 ]

  -- A branch's end at its lane of the merge, past the subscription.
  BEnd : Branch → Pos → Set
  BEnd b c = LaneOf G (s₃ ⊕ [ ix (idx b) ]) b c end × Past c

  -- Every branch ended by `c`: the merge is done there.
  done-at : ∀ {c₀ c₁ c₂ c} → BEnd outerB c₀ → BEnd laneB c₁ → BEnd closeB c₂ → c₀ ≼ c → c₁ ≼ c → c₂ ≼ c → M4.Done c
  done-at {c₀} {c₁} {c₂} {c} (l₀ , p₀) (l₁ , _) (l₂ , _) h₀ h₁ h₂ =
    (s₃ ⊕ [ last ] , (of-end-row s₃ 0 OwnOf , of-reach s₃ 0 OwnOf {s₃ ⊕ [ last ]} {end}) ,
     ≺→≼ {s₃ ⊕ [ last ]} {c} (≺-≼-≺ {s₃ ⊕ [ last ]} {c₀} {c} (past-u s₃-u p₀ [ last ]) h₀)) , lanes
    where
      lanes : ∀ {q a} → enter (Op.of OwnOf) s₃ q (out a) → _ → q ≺ c → _ → Σ Pos λ c′ → LaneOf G q a c′ end × c′ ≼ c
      lanes {a = outerB} o _ _ _ with of-at outerB o
      ... | refl = c₀ , l₀ , h₀
      lanes {a = laneB} o _ _ _ with of-at laneB o
      ... | refl = c₁ , l₁ , h₁
      lanes {a = closeB} o _ _ _ with of-at closeB o
      ... | refl = c₂ , l₂ , h₂

  lend-at : ∀ b {c} → BEnd b c → M4.Done c → M4.JoinT c end
  lend-at b (l , _) d = M4.lend (of-own b s₃) tt l (λ ()) (λ ()) d

  -- THE MERGE ENDS AT THE LAST BRANCH END.
  merge-end : ∀ {c₀ c₁ c₂} → BEnd outerB c₀ → BEnd laneB c₁ → BEnd closeB c₂
            → Σ Pos λ c → M4.JoinT c end × (c ≡ c₀ ⊎ c ≡ c₁ ⊎ c ≡ c₂)
  merge-end {c₀} {c₁} {c₂} e₀ e₁ e₂ with ≼-or-≻ c₀ c₁
  ... | inj₁ h₀₁ with ≼-or-≻ c₁ c₂
  ...   | inj₁ h₁₂ = c₂ , lend-at closeB e₂ (done-at e₀ e₁ e₂ (≼-trans {c₀} {c₁} {c₂} h₀₁ h₁₂) h₁₂ (≼-refl {c₂})) , inj₂ (inj₂ refl)
  ...   | inj₂ h₂₁ = c₁ , lend-at laneB e₁ (done-at e₀ e₁ e₂ h₀₁ (≼-refl {c₁}) (≺→≼ {c₂} {c₁} h₂₁)) , inj₂ (inj₁ refl)
  merge-end {c₀} {c₁} {c₂} e₀ e₁ e₂ | inj₂ h₁₀ with ≼-or-≻ c₀ c₂
  ...   | inj₁ h₀₂ = c₂ , lend-at closeB e₂ (done-at e₀ e₁ e₂ h₀₂ (≼-trans {c₁} {c₀} {c₂} (≺→≼ {c₁} {c₀} h₁₀) h₀₂) (≼-refl {c₂})) , inj₂ (inj₂ refl)
  ...   | inj₂ h₂₀ = c₀ , lend-at outerB e₀ (done-at e₀ e₁ e₂ (≼-refl {c₀}) (≺→≼ {c₁} {c₀} h₁₀) (≺→≼ {c₂} {c₀} h₂₀)) , inj₁ refl

  -- Where the source's reader shows its levels' hangs, and has few rows
  -- of each before a row `q` that no failure precedes.
  module Fails (shM4 : Shows M4.JoinT) (shB3 : Shows B3.JoinT) (shM2 : Shows M2.JoinT)
               (uniq : ∀ {c c′} → Own′ c end → Own′ c′ end → c ≡ c′)
               {q} (f2 : Few Own′ q) (f3 : Few Cat′ q) (f4 : Few Fed′ q) (nfq : ¬ TW.Failed q) where

    -- THE MERGE'S END IN AN INSTANT BEFORE `q`'s FAILS THE TAKE BEFORE IT:
    -- the closing `nothing` starts at once, one step down.
    own-fails : ∀ {c₀} → M4.JoinT c₀ end → Past c₀ → instantOf c₀ ≺ⁱ instantOf q → ⊥
    own-fails {c₀} x pc iq =
      few-lift shM4 f2 x (≺→≼ {c₀} {q} c₀q) λ own →
      few-lift shB3 f3 (raw3 own) (≺→≼ {z₀} {q} z₀q) λ cat →
      few-lift shM2 f4 (raw2 cat) (≺→≼ {z₀} {q} z₀q) λ fed →
      nfq (z₀ , nothing , fed , tt , z₀q)
      where
        c₀q : c₀ ≺ q
        c₀q = instant-≺ c₀ q iq

        c₂ z₀ : Pos
        c₂ = c₀ ⊕ [ ix 1 ]
        z₀ = c₂ ⊕ [ ix 0 ]

        z₀q : z₀ ≺ q
        z₀q = instant-≺ z₀ q (subst (_≺ⁱ instantOf q) (sym (trans (inst-⊕ c₂ [ ix 0 ]) (inst-⊕ c₀ [ ix 1 ]))) iq)

        ends₀ : Own′ c₀ end → B3.Ends 0 [] c₀
        ends₀ own = O2.q₀ , true , s₃ , O2.nth₀ , B3.room (s≤s z≤n) , subst (λ d → enter d s₃ c₀ end) (sym eqC) own , before s₃-u pc

        k-not : Own′ c₀ end → ¬ B3.Kth (_≺ c₀) (B3.Sched 1) 0
        k-not own (inj₁ (c , (_ , _ , _ , nth , B3.room _ , en , _) , lt)) with O2.nth-0 nth
        ... | refl , refl = ≺-irrefl {c₀} (subst (_≺ c₀) (uniq (subst (λ d → enter d s₃ c end) eqC en) own) lt)
        k-not own (inj₁ (_ , (_ , _ , _ , _ , B3.freed () _ , _) , _))
        k-not own (inj₁ (_ , (_ , _ , _ , _ , B3.queued () _ _ _ _ , _) , _))
        k-not own (inj₂ ())

        st₁ : Own′ c₀ end → B3.Starts 1 O2.q₁ (B3.Sched 1) c₂
        st₁ own = B3.queued (s≤s z≤n) (past-u S₂-u pc [ ix 1 ]) (inj₁ (c₀ , ends₀ own , refl)) (inj₁ (c₀ , ends₀ own , ≼-refl {c₀})) (k-not own)

        raw3 : Own′ c₀ end → B3.JoinT z₀ (out nothing)
        raw3 own = B3.lane O2.o₁ (1 , false , O2.nth₁)
          (1 , c₂ , (O2.nth₁ , st₁ own) ,
           subst (λ d → enter d c₂ z₀ (out nothing)) (sym eqN) (at-out , of-reach c₂ 0 (nothing ∷ []) {z₀} {out nothing}) ,
           ≺-ext c₂ [])
          (λ ()) tt

        S₂z₀ : S₂ ≺ z₀
        S₂z₀ = ≺-trans {S₂} {c₀} {z₀} (before S₂-u pc) (≺-trans {c₀} {c₂} {z₀} (≺-ext c₀ []) (≺-ext c₂ []))

        raw2 : Cat′ z₀ (out nothing) → M2.JoinT z₀ (out nothing)
        raw2 cat = M2.lane O1.o₁ tt (subst (λ d → enter d S₂ z₀ (out nothing)) (sym eqF) cat , S₂z₀) (λ ()) tt
