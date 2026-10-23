module port.Placed.Keyed where

open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import denotation.MonotonicList.Events using (Pos; sub)
import denotation.Unfold as U

-- WHERE A NODE CAN STEP, AS A KEY ON THE CONFIGURATION.  `Keyed Q`
-- holds of a node when every position it holds, to step at or to
-- subscribe under, satisfies `Q`.
module _ (Q : Pos → Set) where
  Qᴹ : Maybe Pos → Set
  Qᴹ nothing  = ⊤
  Qᴹ (just c) = Q c

  -- A source's step at `q` lands, fed or told, where `Q` holds.
  Fit : Pos → Set
  Fit q = ∀ j → Q j → Q (q ++ [ sub j ])

  Noted : ∀ {Γ} → List (U.Notice Γ) → Set
  Noted []                    = ⊤
  Noted (U.notice i q a ∷ ns) = Fit q × Noted ns

  mutual
    Keyed : ∀ {Γ A} → U.Node Γ A → Set
    Keyed (U.framesᶜ τ e m)            = Q e
    Keyed (U.burstᶜ τ r i b)           = Q r
    Keyed (U.ofᶜ p i xs)               = Q p
    Keyed (U.mapᶜ f c)                 = Keyed c
    Keyed (U.scanᶜ f z c)              = Keyed c
    Keyed (U.takeWhileᶜ i f c)         = Keyed c
    Keyed (U.flatMapᶜ op g o ls qs pl) = (∀ a q → Q q → Keyed (g a q)) × Keyedᴹ o × Keyedᴸ ls × Keyed pl
    Keyed (U.joinᶜ i p xs e)           = Q p × All (λ x → Q (proj₁ x)) xs × Qᴹ e
    Keyed (U.connectᶜ r b s)           = Keyed b × Keyedˢ s
    Keyed (U.deferᶜ l p ns)            = Q p × Noted ns
    Keyed (U.endingᶜ p n)              = Q p × Keyed n
    Keyed (U.restᶜ n)                  = Keyed n
    Keyed U.idleᶜ                      = ⊤
    Keyed (U.unionᶜ x y)               = Keyed x × Keyed y
    Keyed (U.burstingᶜ r t)            = Keyed t
    Keyed (U.underᶜ s b)               = Keyedˢ s × Keyed b

    Keyedᴹ : ∀ {Γ A} → Maybe (U.Node Γ A) → Set
    Keyedᴹ nothing  = ⊤
    Keyedᴹ (just c) = Keyed c

    Keyedᴸ : ∀ {Γ A} → List (U.Node Γ A) → Set
    Keyedᴸ []       = ⊤
    Keyedᴸ (c ∷ cs) = Keyed c × Keyedᴸ cs

    Keyedˢ : ∀ {Γ A} → U.Source Γ A → Set
    Keyedˢ (U.live s)    = Keyed s
    Keyedˢ (U.ended c t) = Q c × Keyed t

  KeyedStep : ∀ {Γ A} → U.Step Γ A → Set
  KeyedStep (U.outˢ k a c) = Q k × Keyed c
  KeyedStep (U.skipˢ k c)  = Q k × Keyed c
  KeyedStep (U.endˢ k)     = Q k
  KeyedStep U.hushˢ        = ⊤

  KeyedOuter : ∀ {Γ A} → U.Outer Γ A → Set
  KeyedOuter U.doneᵒ       = ⊤
  KeyedOuter (U.runᵒ o so) = Keyed o × KeyedStep so

  KeyedEarliest : ∀ {Γ B} → U.Earliest Γ B → Set
  KeyedEarliest U.none                = ⊤
  KeyedEarliest (U.found k bs l s as) = Keyedᴸ bs × Keyed l × KeyedStep s × Keyedᴸ as

  Admitted : ∀ {Γ} {A B : Set} → List (U.Node Γ B) × List A × U.Node Γ B → Set
  Admitted (ls , qs , d) = Keyedᴸ ls × Keyed d

  keyed-head : ∀ {Γ A} (t : U.Step Γ A) → KeyedStep t → ∀ k → U.headˢ t ≡ just k → Q k
  keyed-head (U.outˢ k a c) (qk , _) _ refl = qk
  keyed-head (U.skipˢ k c)  (qk , _) _ refl = qk
  keyed-head (U.endˢ k)     qk       _ refl = qk
  keyed-head U.hushˢ        _        _ ()
