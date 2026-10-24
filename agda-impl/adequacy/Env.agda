{-# OPTIONS --guardedness #-}

-- A NODE READS ITS ENVIRONMENT NO FURTHER THAN IT HAS RUN: each source
-- in scope alike for m steps leaves a node's meaning and cut alike for
-- as many, each operator's own non-expansiveness carried through the
-- node; and sources alike at every depth leave a node in order alike,
-- every order predicate being read off the steps alone.
module adequacy.Env where

open import Data.List using (List; []; _∷_; [_])
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (lookup; updateAt) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (refl)

open import Tree using (Later)
open import denotation.MonotonicList.Events using (Events; Events∞; Tail∞; Pos; out; skip; end; idle)
open import denotation.MonotonicList using (MonotonicList; Agree; Agreeᵀ; stop; out⁼; skip⁼; end⁼; hush⁼; pin⁼; idle⁼;
  agree-refl; agree-sym; agree-pred; agreeᵀ-refl; _≈[_]_; agrees; agree; ≈ₖ-pred) renaming (cold to coldᴹ)
open import denotation.NonExpansive using (Agreeˢ; _,ˢ_; mapᴱ-ne; scanᴱ-ne; takeWhileᴱ-ne; tailᴱ-ne; ∪-ne; burstOn-ne; beside-ne;
  rejoin-ne; hot-ne; go-ne; whole-ne; mapᴱ-neᴹ; Lanes; []ᴸ; _∷ᴸ_; Queue; []ᑫ; _∷ᑫ_; Outerᴿ; doneᴼ; liveᴼ)
open import denotation.Compositional using (EnvAgree; []ᵉ; _∷ᵉ_; deferᴰ-contractive)
open import denotation.Denote using (flatOp)
import denotation.Unfold as U
open import denotation.Unfold using (NEnv)
open import adequacy.Placed.Order using (Reaches; out-here; skip-here; out-there; skip-there)

open Events∞
open Tail∞

------------------------------------------------------------------------
-- Environments alike for m steps

-- Two environments alike for m steps, source by source.
NAgree : ∀ {Γ} → ℕ → NEnv Γ → NEnv Γ → Set
NAgree m []ᴬ       []ᴬ         = ⊤
NAgree m (e ∷ᴬ ρ) (e′ ∷ᴬ ρ′) = Agree m e e′ × NAgree m ρ ρ′

nagree-refl : ∀ {Γ} m (ρ : NEnv Γ) → NAgree m ρ ρ
nagree-refl m []ᴬ      = tt
nagree-refl m (e ∷ᴬ ρ) = agree-refl m e , nagree-refl m ρ

lookup-ne : ∀ {Γ A m} {ρ ρ′ : NEnv Γ} → NAgree m ρ ρ′ → (i : A ∈ Γ) → Agree m (lookup ρ i) (lookup ρ′ i)
lookup-ne {ρ = _ ∷ᴬ _} {_ ∷ᴬ _} (a , _) (here refl) = a
lookup-ne {ρ = _ ∷ᴬ _} {_ ∷ᴬ _} (_ , E) (there i)   = lookup-ne E i

-- A source's step put back, alike.
put-ne : ∀ {A m} q (a : Maybe A) {e e′ : Events A} → Agree m e e′ → Agree m (U.put q a e) (U.put q a e′)
put-ne {m = zero}  q a        _  = stop
put-ne {m = suc m} q (just _) ag = out⁼ (agreeᵀ-refl m idle) (agree-pred ag)
put-ne {m = suc m} q nothing  ag = skip⁼ (agreeᵀ-refl m idle) (agree-pred ag)

update-ne : ∀ {Γ A m} (i : A ∈ Γ) (f : Events A → Events A) → (∀ {e e′} → Agree m e e′ → Agree m (f e) (f e′))
          → {ρ ρ′ : NEnv Γ} → NAgree m ρ ρ′ → NAgree m (updateAt i f ρ) (updateAt i f ρ′)
update-ne (here refl) f F {_ ∷ᴬ _} {_ ∷ᴬ _} (a , E) = F a , E
update-ne (there i)   f F {_ ∷ᴬ _} {_ ∷ᴬ _} (a , E) = a , update-ne i f F E

replay-ne : ∀ {Γ m} (ns : List (U.Notice Γ)) {ρ ρ′ : NEnv Γ} → NAgree m ρ ρ′ → NAgree m (U.replay ns ρ) (U.replay ns ρ′)
replay-ne []                    E = E
replay-ne (U.notice i q a ∷ ns) E = update-ne i (U.put q a) (put-ne q a) (replay-ne ns E)

hots-ne : ∀ {Γ m} {ρ ρ′ : NEnv Γ} → NAgree m ρ ρ′ → EnvAgree m (U.hots ρ) (U.hots ρ′)
hots-ne {ρ = []ᴬ}    {[]ᴬ}      _       = []ᵉ
hots-ne {ρ = _ ∷ᴬ _} {_ ∷ᴬ _} (a , E) = hot-ne a ∷ᵉ hots-ne E

fed-ne : ∀ {A m} (xs : List (Pos × Maybe A)) {e e′ : Events A} → Agree m e e′ → Agree m (U.fedᴺ xs e) (U.fedᴺ xs e′)
fed-ne []             ag = ag
fed-ne ((q , a) ∷ xs) ag = put-ne q a (fed-ne xs ag)

joined-ne : ∀ {Γ A m} (i : A ∈ Γ) p (c : Maybe Pos) {ρ ρ′ : NEnv Γ} → NAgree m ρ ρ′ → Agree m (U.joined i p c ρ) (U.joined i p c ρ′)
joined-ne i p (just c) E = agree-refl _ _
joined-ne i p nothing  E = rejoin-ne p (lookup-ne E i)

queue-ne : ∀ {A B : Set} {m} (qs : List A) {h h′ : A → MonotonicList B} → (∀ a → h a ≈[ m ] h′ a) → Queue m (L.map h qs) (L.map h′ qs)
queue-ne []       F = []ᑫ
queue-ne (a ∷ qs) F = F a ∷ᑫ queue-ne qs F

------------------------------------------------------------------------
-- A node's meaning and cut, alike

mutual
  meaning-ne : ∀ {Γ A m} (n : U.Node Γ A) {ρ ρ′ : NEnv Γ} → NAgree m ρ ρ′ → Agree m (U.meaning n ρ) (U.meaning n ρ′)
  meaning-ne (U.framesᶜ _ _ _)    E = agree-refl _ _
  meaning-ne (U.burstᶜ _ _ _ _)   E = agree-refl _ _
  meaning-ne (U.ofᶜ _ _ _)        E = agree-refl _ _
  meaning-ne (U.mapᶜ f c)         E = mapᴱ-ne f (meaning-ne c E)
  meaning-ne (U.scanᶜ f z c)      E = scanᴱ-ne f z (meaning-ne c E)
  meaning-ne (U.takeWhileᶜ i p c) E = takeWhileᴱ-ne i p (meaning-ne c E)
  meaning-ne (U.flatMapᶜ op g o ls qs pl) {ρ} {ρ′} E =
    go-ne (flatOp op) (outer-ne g o F E) (states-ne ls E) (queue-ne qs F) (cut-ne pl E)
    where
      F : ∀ a → coldᴹ (λ q → U.stateᴺ (g a q) ρ) ≈[ _ ] coldᴹ (λ q → U.stateᴺ (g a q) ρ′)
      F a = agrees (λ q → cut-ne (g a q) E) (λ q → meaning-ne (g a q) E)
  meaning-ne (U.joinᶜ i p xs c)   E = fed-ne xs (joined-ne i p c E)
  meaning-ne (U.connectᶜ r b (U.live s))    E = beside-ne r (state-ne b (meaning-ne s E , E)) (state-ne s E)
  meaning-ne (U.connectᶜ r b (U.ended c t)) E = beside-ne r (state-ne b (agree-refl _ (end c) , E)) (state-ne t E)
  meaning-ne (U.deferᶜ l p ns)    E = agree (≈ₖ-pred (deferᴰ-contractive (U.⟦⟧-ne (Later.force l) (hots-ne (replay-ne ns E))))) p
  meaning-ne (U.endingᶜ p n)      E = agree-refl _ _
  meaning-ne (U.restᶜ n)          E = tailᴱ-ne (cut-ne n E)
  meaning-ne U.idleᶜ              E = agree-refl _ _
  meaning-ne (U.unionᶜ x y)       E = tailᴱ-ne (∪-ne (cut-ne x E) (cut-ne y E))
  meaning-ne (U.burstingᶜ r t)    E = tailᴱ-ne (burstOn-ne r (state-ne t E))
  meaning-ne (U.underᶜ (U.live s) b)    E = tailᴱ-ne (cut-ne b (meaning-ne s E , E))
  meaning-ne (U.underᶜ (U.ended c t) b) E = tailᴱ-ne (cut-ne b (agree-refl _ (end c) , E))

  cut-ne : ∀ {Γ A m} (n : U.Node Γ A) {ρ ρ′ : NEnv Γ} → NAgree m ρ ρ′ → Agreeᵀ m (U.cutᴺ n ρ) (U.cutᴺ n ρ′)
  cut-ne (U.framesᶜ _ _ _)    E = agreeᵀ-refl _ _
  cut-ne (U.burstᶜ _ _ _ _)   E = agreeᵀ-refl _ _
  cut-ne (U.ofᶜ _ _ _)        E = agreeᵀ-refl _ _
  cut-ne (U.mapᶜ f c)         E = cut-ne c E
  cut-ne (U.scanᶜ f z c)      E = cut-ne c E
  cut-ne (U.takeWhileᶜ i p c) E = cut-ne c E
  cut-ne (U.flatMapᶜ op g o ls qs pl) {ρ} {ρ′} E =
    whole-ne (outer-ne g o F E) (states-ne ls E) (cut-ne pl E)
    where
      F : ∀ a → coldᴹ (λ q → U.stateᴺ (g a q) ρ) ≈[ _ ] coldᴹ (λ q → U.stateᴺ (g a q) ρ′)
      F a = agrees (λ q → cut-ne (g a q) E) (λ q → meaning-ne (g a q) E)
  cut-ne (U.joinᶜ _ _ _ _)    E = agreeᵀ-refl _ _
  cut-ne (U.connectᶜ r b (U.live s))    E = ∪-ne (burstOn-ne r (state-ne s E)) (cut-ne b (meaning-ne s E , E))
  cut-ne (U.connectᶜ r b (U.ended c t)) E = ∪-ne (burstOn-ne r (state-ne t E)) (cut-ne b (agree-refl _ (end c) , E))
  cut-ne (U.deferᶜ _ _ _)     E = agreeᵀ-refl _ _
  cut-ne (U.endingᶜ p n)      E = cut-ne n E
  cut-ne (U.restᶜ n)          E = cut-ne n E
  cut-ne U.idleᶜ              E = agreeᵀ-refl _ _
  cut-ne (U.unionᶜ x y)       E = ∪-ne (cut-ne x E) (cut-ne y E)
  cut-ne (U.burstingᶜ r t)    E = burstOn-ne r (state-ne t E)
  cut-ne (U.underᶜ (U.live s) b)    E = cut-ne b (meaning-ne s E , E)
  cut-ne (U.underᶜ (U.ended c t) b) E = cut-ne b (agree-refl _ (end c) , E)

  state-ne : ∀ {Γ A m} (n : U.Node Γ A) {ρ ρ′ : NEnv Γ} → NAgree m ρ ρ′ → Agreeˢ m (U.stateᴺ n ρ) (U.stateᴺ n ρ′)
  state-ne n E = cut-ne n E ,ˢ meaning-ne n E

  states-ne : ∀ {Γ A m} (ls : List (U.Node Γ A)) {ρ ρ′ : NEnv Γ} → NAgree m ρ ρ′ → Lanes m (U.states ls ρ) (U.states ls ρ′)
  states-ne []       E = []ᴸ
  states-ne (c ∷ cs) E = state-ne c E ∷ᴸ states-ne cs E

  -- The outer, its elements alike by `F`.
  outer-ne : ∀ {Γ A B m} (g : A → Pos → U.Node Γ B) (o : Maybe (U.Node Γ A)) {ρ ρ′ : NEnv Γ}
           → (∀ a → coldᴹ (λ q → U.stateᴺ (g a q) ρ) ≈[ m ] coldᴹ (λ q → U.stateᴺ (g a q) ρ′))
           → NAgree m ρ ρ′ → Outerᴿ m (U.outerᴺ g o ρ) (U.outerᴺ g o ρ′)
  outer-ne g nothing  F E = doneᴼ
  outer-ne g (just o) F E = liveᴼ (cut-ne o E) (mapᴱ-neᴹ F (meaning-ne o E))

------------------------------------------------------------------------
-- Runs alike at every depth: a position reached alike

out-next : ∀ {A k x} {l r : Events∞ A} → (∀ m → Agree m (out k x l) (out k x r)) → ∀ m → Agree m (force l) (force r)
out-next ag m with ag (suc m)
... | out⁼ _ a = a

skip-next : ∀ {A k} {l r : Events∞ A} → (∀ m → Agree m (skip k l) (skip k r)) → ∀ m → Agree m (force l) (force r)
skip-next ag m with ag (suc m)
... | skip⁼ _ a = a

reaches-agree : ∀ {A k} {e e′ : Events A} → (∀ m → Agree m e e′) → Reaches k e → Reaches k e′
reaches-agree ag out-here with ag 1
... | out⁼ _ _ = out-here
reaches-agree ag skip-here with ag 1
... | skip⁼ _ _ = skip-here
reaches-agree ag (out-there h) with ag 1
... | out⁼ _ _ = out-there (reaches-agree (out-next ag) h)
reaches-agree ag (skip-there h) with ag 1
... | skip⁼ _ _ = skip-there (reaches-agree (skip-next ag) h)

------------------------------------------------------------------------
-- Environments alike at every depth

Same : ∀ {Γ} → NEnv Γ → NEnv Γ → Set
Same ρ ρ′ = ∀ m → NAgree m ρ ρ′

same-cons : ∀ {Γ A} {e e′ : Events A} {ρ ρ′ : NEnv Γ} → (∀ m → Agree m e e′) → Same ρ ρ′ → Same (e ∷ᴬ ρ) (e′ ∷ᴬ ρ′)
same-cons a S m = a m , S m

-- A node in order to every depth stays so under an environment alike
-- at every depth.

