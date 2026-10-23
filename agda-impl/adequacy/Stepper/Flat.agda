{-# OPTIONS --guardedness #-}

-- A FLATMAP STARTS AS ITS PARTS DO: its step and its meaning each run
-- the part showing first of its pool, its outer and its lanes, by the same
-- rule.  A part whose meaning starts with its step's event heads alike on
-- both sides; one starting past a source lends that source to the whole.
-- Of two parts, the step and the meaning pick the same one where both are
-- alike, and otherwise the whole starts past a source of either (`combine`).
-- Three levels: the lanes' earliest, the outer against it, the pool
-- against the outer and the lanes.
module adequacy.Stepper.Flat where

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_]; null; map)
open import Data.Bool.Properties using (∧-identityʳ)
import Tree as T
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.List.Relation.Unary.All using (All)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; subst₂; cong)

open import denotation.MonotonicList.Events using (Events; Events∞; out; skip; end; hush; Pos; idle; pin; ix; _<ᵖ_; Tail; <ᵖ-trans; <ᵖ-asym;
  <ᵖ-below)
open import denotation.MonotonicList using (Agree; stop; stopᵀ; out⁼; skip⁼; end⁼; hush⁼; tailᴱ; MonotonicList)
import denotation.MonotonicList as M′
import denotation.Unfold as U
open import denotation.Unfold using (NEnv)
open import denotation.Denote using (flatOp)
open import adequacy.Placed.Order using (still)
open import adequacy.Sane using (Mode; Rested; RestedS; step-rested)
open import adequacy.Stepper.Past using (Past; First; Firsts; Firstᴹ; Firstᴸ; Underᵐ; afterᴱ)
open import adequacy.Stepper.Parts using (posᴱ; pastᴱ-pos; pos-pastᴱ; move; pick; under-or; Overᵐ)

open Events∞

------------------------------------------------------------------------
-- Heads, and rules picking the first of two.

-- `m` shows no later than `n`; nothing shows latest.
_≼_ : Maybe Pos → Maybe Pos → Set
m      ≼ nothing = ⊤
nothing ≼ just _ = ⊥
just a ≼ just b  = b <ᵖ a ≡ false

-- A rule picking the first of two heads, the one it picks no later.
Fair : (Maybe Pos → Maybe Pos → Bool) → Set
Fair r = ∀ a b → (r a b ≡ true → a ≼ b) × (r a b ≡ false → b ≼ a)

under-≼ : ∀ m n a → m ≼ n → Underᵐ m a → Underᵐ n a
under-≼ m        nothing  a _  _ = tt
under-≼ nothing  (just b) a () _
under-≼ (just c) (just b) a cb u = still a c b u cb

under-over : ∀ m h a → Underᵐ m a → Overᵐ m h → a <ᵖ h ≡ true
under-over nothing  h a u ()
under-over (just j) h a u o = <ᵖ-trans a j h u o

-- A lane earlier than the rest's earliest, ties going on.
first? : Maybe Pos → Maybe Pos → Bool
first? nothing  m        = false
first? (just k) nothing  = true
first? (just k) (just j) = k <ᵖ j

fair-first : Fair first?
fair-first nothing  m        = (λ ()) , (λ _ → tt)
fair-first (just k) nothing  = (λ _ → tt) , (λ ())
fair-first (just k) (just j) = (λ e → <ᵖ-asym k j e) , (λ e → e)

-- The outer, when it shows strictly before the lanes, or they show nothing.
race? : Maybe Pos → Maybe Pos → Bool
race? h        nothing  = true
race? nothing  (just k) = false
race? (just j) (just k) = j <ᵖ k

fair-race : Fair race?
fair-race h        nothing  = (λ _ → tt) , (λ ())
fair-race nothing  (just k) = (λ ()) , (λ _ → tt)
fair-race (just j) (just k) = (λ e → <ᵖ-asym j k e) , (λ e → e)

-- The pool, when it shows strictly before every other part.
pool? : Maybe Pos → Maybe Pos → Bool
pool? nothing  r = false
pool? (just k) r = M′.clear k r

fair-pool : Fair pool?
fair-pool nothing  r        = (λ ()) , (λ _ → tt)
fair-pool (just k) nothing  = (λ _ → tt) , (λ ())
fair-pool (just k) (just j) = (λ e → <ᵖ-asym k j e) , (λ e → e)

-- Strictly before both, strictly before the one a fair rule picks.
clear-min : ∀ r → Fair r → ∀ k a b → M′.clear k a ∧ M′.clear k b ≡ M′.clear k (if r a b then a else b)
clear-min r f k a b with r a b in e
... | true  = up a b (proj₁ (f a b) e)
  where
    up : ∀ a b → a ≼ b → M′.clear k a ∧ M′.clear k b ≡ M′.clear k a
    up nothing  nothing  _  = refl
    up nothing  (just j) ()
    up (just i) nothing  _  with k <ᵖ i
    ... | true  = refl
    ... | false = refl
    up (just i) (just j) ji with k <ᵖ i in ki
    ... | true  = still k i j ki ji
    ... | false = refl
... | false = down a b (proj₂ (f a b) e)
  where
    down : ∀ a b → b ≼ a → M′.clear k a ∧ M′.clear k b ≡ M′.clear k b
    down nothing  nothing  _ = refl
    down (just i) nothing  ()
    down nothing  (just j) _ = refl
    down (just i) (just j) ij with k <ᵖ j in kj
    ... | true  rewrite still k j i kj ij = refl
    ... | false with k <ᵖ i
    ...   | true  = refl
    ...   | false = refl

clearˢ-clear : ∀ k m → U.clearˢ k m ≡ M′.clear k m
clearˢ-clear k nothing  = refl
clearˢ-clear k (just j) = refl

------------------------------------------------------------------------
-- A part as the step and the meaning see it: alike, by `P`, at one
-- head; else the meaning starts past a source shown before the step's
-- head.

Lead : ∀ {Γ} → All (λ _ → Mode) Γ → NEnv Γ → Maybe Pos → Maybe Pos → Set
Lead ν ρ s m = Σ Pos λ h → m ≡ just h × Past ν h s ρ

Cand : ∀ {Γ} → All (λ _ → Mode) Γ → NEnv Γ → Set → Maybe Pos → Maybe Pos → Set
Cand ν ρ P s m = (P × s ≡ m) ⊎ Lead ν ρ s m

Pick : Bool → Set → Set → Set
Pick true  P Q = P
Pick false P Q = Q

recand : ∀ {Γ} {ν : All (λ _ → Mode) Γ} {ρ : NEnv Γ} {P Q : Set} {s s′ m m′} → s ≡ s′ → m ≡ m′ → (P → Q) → Cand ν ρ P s m → Cand ν ρ Q s′ m′
recand refl refl f (inj₁ (p , e)) = inj₁ (f p , e)
recand refl refl f (inj₂ l)       = inj₂ l

-- Under the step's head, or that head before `h`.
either : ∀ m a h → a <ᵖ h ≡ true → (a <ᵖ h ≡ true × Underᵐ m a) ⊎ Overᵐ m h
either m a h ah with under-or m a h ah
... | inj₁ u = inj₁ (ah , u)
... | inj₂ o = inj₂ o

-- OF TWO PARTS, the step and the meaning pick alike, or the whole starts
-- past a source: the picked part's own, or, where the two sides pick
-- apart, whichever of the two sources shows first.
combine : ∀ {Γ} (ν : All (λ _ → Mode) Γ) (ρ : NEnv Γ) {P₁ P₂ : Set} r → Fair r → ∀ s₁ m₁ s₂ m₂
        → Cand ν ρ P₁ s₁ m₁ → Cand ν ρ P₂ s₂ m₂
        → Cand ν ρ (r s₁ s₂ ≡ r m₁ m₂ × Pick (r m₁ m₂) P₁ P₂) (if r s₁ s₂ then s₁ else s₂) (if r m₁ m₂ then m₁ else m₂)
combine ν ρ r f s₁ m₁ s₂ m₂ c₁ c₂ with r s₁ s₂ in eU | r m₁ m₂ in eM
combine ν ρ r f s₁ m₁ s₂ m₂ (inj₁ (p₁ , e₁)) c₂ | true | true = inj₁ ((refl , p₁) , e₁)
combine ν ρ r f s₁ m₁ s₂ m₂ (inj₂ l₁) c₂ | true | true = inj₂ l₁
combine ν ρ r f s₁ m₁ s₂ m₂ c₁ (inj₁ (p₂ , e₂)) | false | false = inj₁ ((refl , p₂) , e₂)
combine ν ρ r f s₁ m₁ s₂ m₂ c₁ (inj₂ l₂) | false | false = inj₂ l₂
combine ν ρ r f s₁ m₁ s₂ m₂ (inj₁ (p₁ , refl)) (inj₁ (p₂ , refl)) | true | false = ⊥-elim (bool (trans (sym eU) eM))
  where bool : true ≡ false → ⊥
        bool ()
combine ν ρ r f s₁ m₁ s₂ m₂ (inj₁ (p₁ , refl)) (inj₁ (p₂ , refl)) | false | true = ⊥-elim (bool (trans (sym eM) eU))
  where bool : true ≡ false → ⊥
        bool ()
-- The step picks the first, alike; the meaning the second, past.
combine ν ρ r f s₁ m₁ s₂ m₂ (inj₁ (p₁ , refl)) (inj₂ (h₂ , refl , q₂)) | true | false =
  inj₂ (h₂ , refl , move ν ρ h₂ s₂ h₂ s₁ (λ a ah _ → ah , under-≼ (just h₂) s₁ a (proj₂ (f s₁ (just h₂)) eM) ah) q₂)
-- The step picks the second, past; the meaning the first, alike.
combine ν ρ r f s₁ m₁ s₂ m₂ (inj₁ (p₁ , refl)) (inj₂ (h₂ , refl , q₂)) | false | true = inj₂ (lend s₁ (proj₁ (f s₁ (just h₂)) eM) (proj₂ (f s₁ s₂) eU))
  where
    lend : ∀ m₁ → m₁ ≼ just h₂ → s₂ ≼ m₁ → Lead ν ρ s₂ m₁
    lend nothing   () _
    lend (just h₁) _  o = h₁ , refl , move ν ρ h₂ s₂ h₁ s₂ (λ a _ u → under-≼ s₂ (just h₁) a o u , u) q₂
-- The step picks the first, past; the meaning the second, alike.
combine ν ρ r f s₁ m₁ s₂ m₂ (inj₂ (h₁ , refl , q₁)) (inj₁ (p₂ , refl)) | true | false = inj₂ (lend s₂ (proj₂ (f (just h₁) s₂) eM) (proj₁ (f s₁ s₂) eU))
  where
    lend : ∀ m₂ → m₂ ≼ just h₁ → s₁ ≼ m₂ → Lead ν ρ s₁ m₂
    lend nothing   () _
    lend (just h₂) _  o = h₂ , refl , move ν ρ h₁ s₁ h₂ s₁ (λ a _ u → under-≼ s₁ (just h₂) a o u , u) q₁
-- The step picks the second, alike; the meaning the first, past.
combine ν ρ r f s₁ m₁ s₂ m₂ (inj₂ (h₁ , refl , q₁)) (inj₁ (p₂ , refl)) | false | true =
  inj₂ (h₁ , refl , move ν ρ h₁ s₁ h₁ s₂ (λ a ah _ → ah , under-≼ (just h₁) s₂ a (proj₁ (f (just h₁) s₂) eM) ah) q₁)
-- Both past, picked apart: the source shown first.
combine ν ρ r f s₁ m₁ s₂ m₂ (inj₂ (h₁ , refl , q₁)) (inj₂ (h₂ , refl , q₂)) | true | false
  with pick ν ρ h₂ s₂ h₂ s₁ (λ a ah _ → either s₁ a h₂ ah) q₂
... | inj₁ q = inj₂ (h₂ , refl , q)
... | inj₂ o = inj₂ (h₂ , refl , move ν ρ h₁ s₁ h₂ s₁ (λ a _ u → under-over s₁ h₂ a u o , u) q₁)
combine ν ρ r f s₁ m₁ s₂ m₂ (inj₂ (h₁ , refl , q₁)) (inj₂ (h₂ , refl , q₂)) | false | true
  with pick ν ρ h₁ s₁ h₁ s₂ (λ a ah _ → either s₂ a h₁ ah) q₁
... | inj₁ q = inj₂ (h₁ , refl , q)
... | inj₂ o = inj₂ (h₁ , refl , move ν ρ h₂ s₂ h₁ s₂ (λ a _ u → under-over s₂ h₁ a u o , u) q₂)

------------------------------------------------------------------------
-- One part.

agree-head : ∀ {Γ A} (ρ : NEnv Γ) (t : U.Step Γ A) (x : Events A) → Agree 1 x (afterᴱ ρ t) → U.headˢ t ≡ M′.head x
agree-head ρ (U.outˢ k a c) _ (out⁼ _ _)  = refl
agree-head ρ (U.skipˢ k c)  _ (skip⁼ _ _) = refl
agree-head ρ (U.endˢ k)     _ end⁼        = refl
agree-head ρ U.hushˢ        _ hush⁼       = refl

head-pos : ∀ {A} (x : Events A) → x ≢ hush → M′.head x ≡ just (posᴱ x)
head-pos (out q a r) _  = refl
head-pos (skip q r)  _  = refl
head-pos (end c)     _  = refl
head-pos hush        nh = ⊥-elim (nh refl)

cand : ∀ {Γ A} (ν : All (λ _ → Mode) Γ) (ρ : NEnv Γ) (t : U.Step Γ A) (x : Events A) → First ν ρ t x
     → Cand ν ρ (Agree 1 x (afterᴱ ρ t)) (U.headˢ t) (M′.head x)
cand ν ρ t x (inj₁ a) = inj₁ (a , agree-head ρ t x a)
cand ν ρ t x (inj₂ p) = inj₂ (posᴱ x , head-pos x (proj₁ (pastᴱ-pos ν ρ t x p)) , proj₂ (pastᴱ-pos ν ρ t x p))

------------------------------------------------------------------------
-- The lanes' earliest.

headEˢ : ∀ {Γ B} → U.Earliest Γ B → Maybe Pos
headEˢ U.none                = nothing
headEˢ (U.found k _ _ _ _)   = just k

headE : ∀ {B} → M′.Earliest B → Maybe Pos
headE M′.none            = nothing
headE (M′.found k _ _ _) = just k

hereˢ : ∀ {Γ B} → U.Node Γ B → U.Step Γ B → List (U.Node Γ B) → Maybe Pos → U.Earliest Γ B
hereˢ l s ls nothing  = U.none
hereˢ l s ls (just k) = U.found k [] l s ls

onˢ : ∀ {Γ B} → U.Node Γ B → U.Earliest Γ B → U.Earliest Γ B
onˢ l U.none                  = U.none
onˢ l (U.found k bs c sc as)  = U.found k (l ∷ bs) c sc as

hereᴹ : ∀ {B} → Events∞ B → List (Events∞ B) → Maybe Pos → M′.Earliest B
hereᴹ l ls nothing  = M′.none
hereᴹ l ls (just k) = M′.found k [] l ls

onᴹ : ∀ {B} → Events∞ B → M′.Earliest B → M′.Earliest B
onᴹ l M′.none              = M′.none
onᴹ l (M′.found k bs c as) = M′.found k (l ∷ bs) c as

pick-view : ∀ {Γ B} (l : U.Node Γ B) s ls h e → U.pick l s ls h e ≡ (if first? h (headEˢ e) then hereˢ l s ls h else onˢ l e)
pick-view l s ls nothing  U.none              = refl
pick-view l s ls nothing  (U.found _ _ _ _ _) = refl
pick-view l s ls (just k) U.none              = refl
pick-view l s ls (just k) (U.found _ _ _ _ _) = refl

earliest-view : ∀ {B} (l : Events∞ B) ls
              → M′.earliest (l ∷ ls) ≡ (if first? (M′.head (force l)) (headE (M′.earliest ls)) then hereᴹ l ls (M′.head (force l)) else onᴹ l (M′.earliest ls))
earliest-view l ls with M′.head (force l) | M′.earliest ls
... | nothing | M′.none              = refl
... | nothing | M′.found _ _ _ _     = refl
... | just k  | M′.none              = refl
... | just k  | M′.found _ _ _ _     = refl

head-hereˢ : ∀ {Γ B} d (l : U.Node Γ B) s ls h e → headEˢ (if d then hereˢ l s ls h else onˢ l e) ≡ (if d then h else headEˢ e)
head-hereˢ true  l s ls nothing  e                    = refl
head-hereˢ true  l s ls (just k) e                    = refl
head-hereˢ false l s ls h        U.none               = refl
head-hereˢ false l s ls h        (U.found _ _ _ _ _)  = refl

head-hereᴹ : ∀ {B} d (l : Events∞ B) ls h e → headE (if d then hereᴹ l ls h else onᴹ l e) ≡ (if d then h else headE e)
head-hereᴹ true  l ls nothing  e                  = refl
head-hereᴹ true  l ls (just k) e                  = refl
head-hereᴹ false l ls h        M′.none            = refl
head-hereᴹ false l ls h        (M′.found _ _ _ _) = refl

-- The same lane earliest on both sides, its meaning its step's.
Mirrorᴱ : ∀ {Γ B} → NEnv Γ → U.Earliest Γ B → M′.Earliest B → Set
Mirrorᴱ ρ U.none                M′.none                  = ⊤
Mirrorᴱ ρ (U.found k bs l s as) (M′.found k′ bs′ l′ as′) =
  bs′ ≡ U.states bs ρ × l′ ≡ U.stateᴺ l ρ × as′ ≡ U.states as ρ × Agree 1 (U.meaning l ρ) (afterᴱ ρ s)
Mirrorᴱ ρ _                     _                        = ⊥

mirror-here : ∀ {Γ B} (ρ : NEnv Γ) (l : U.Node Γ B) ls h → Agree 1 (U.meaning l ρ) (afterᴱ ρ (U.step l)) → U.headˢ (U.step l) ≡ h
            → Mirrorᴱ ρ (hereˢ l (U.step l) ls (U.headˢ (U.step l))) (hereᴹ (U.stateᴺ l ρ) (U.states ls ρ) h)
mirror-here ρ l ls h a refl with U.headˢ (U.step l)
... | nothing = tt
... | just k  = refl , refl , refl , a

mirror-on : ∀ {Γ B} (ρ : NEnv Γ) (l : U.Node Γ B) e eᴹ → Mirrorᴱ ρ e eᴹ → Mirrorᴱ ρ (onˢ l e) (onᴹ (U.stateᴺ l ρ) eᴹ)
mirror-on ρ l U.none                M′.none                  _                 = tt
mirror-on ρ l (U.found k bs c sc as) (M′.found k′ bs′ c′ as′) (refl , m) = refl , m
mirror-on ρ l U.none                (M′.found _ _ _ _)       ()
mirror-on ρ l (U.found _ _ _ _ _)   M′.none                  ()

lanes : ∀ {Γ B} (ν : All (λ _ → Mode) Γ) (ρ : NEnv Γ) (ls : List (U.Node Γ B)) → Firstᴸ ν ls ρ
      → Cand ν ρ (Mirrorᴱ ρ (U.earliest ls) (M′.earliest (U.states ls ρ))) (headEˢ (U.earliest ls)) (headE (M′.earliest (U.states ls ρ)))
lanes ν ρ []       _        = inj₁ (tt , refl)
lanes ν ρ (l ∷ ls) (fl , fs) =
  recand {ν = ν} {ρ = ρ} (sym (trans (cong headEˢ (pick-view l s ls s₁ E)) (head-hereˢ (first? s₁ s₂) l s ls s₁ E)))
         (sym (trans (cong headE (earliest-view (U.stateᴺ l ρ) (U.states ls ρ))) (head-hereᴹ (first? m₁ m₂) (U.stateᴺ l ρ) (U.states ls ρ) m₁ Eᴹ)))
         conv
         (combine ν ρ first? fair-first s₁ m₁ s₂ m₂ (cand ν ρ s (U.meaning l ρ) fl) (lanes ν ρ ls fs))
  where
    s  = U.step l
    s₁ = U.headˢ s
    m₁ = M′.head (U.meaning l ρ)
    E  = U.earliest ls
    Eᴹ = M′.earliest (U.states ls ρ)
    s₂ = headEˢ E
    m₂ = headE Eᴹ
    conv′ : ∀ dU dM → dU ≡ dM → Pick dM (Agree 1 (U.meaning l ρ) (afterᴱ ρ s)) (Mirrorᴱ ρ E Eᴹ)
          → Mirrorᴱ ρ (if dU then hereˢ l s ls s₁ else onˢ l E) (if dM then hereᴹ (U.stateᴺ l ρ) (U.states ls ρ) m₁ else onᴹ (U.stateᴺ l ρ) Eᴹ)
    conv′ true  true  _ a = mirror-here ρ l ls m₁ a (agree-head ρ s (U.meaning l ρ) a)
    conv′ false false _ m = mirror-on ρ l E Eᴹ m
    conv′ true  false () _
    conv′ false true  () _
    conv : (first? s₁ s₂ ≡ first? m₁ m₂ × Pick (first? m₁ m₂) (Agree 1 (U.meaning l ρ) (afterᴱ ρ s)) (Mirrorᴱ ρ E Eᴹ))
         → Mirrorᴱ ρ (U.earliest (l ∷ ls)) (M′.earliest (U.states (l ∷ ls) ρ))
    conv (e , p) = subst₂ (Mirrorᴱ ρ) (sym (pick-view l s ls s₁ E)) (sym (earliest-view (U.stateᴺ l ρ) (U.states ls ρ))) (conv′ (first? s₁ s₂) (first? m₁ m₂) e p)

earliest-found : ∀ {B} (ls : List (Events∞ B)) {k bs l as} → M′.earliest ls ≡ M′.found k bs l as → M′.head (force l) ≡ just k
earliest-found []        ()
earliest-found (l₀ ∷ ls) with M′.head (force l₀) in hl | M′.earliest ls in el
... | nothing | M′.none            = λ ()
... | nothing | M′.found k bs c as = λ { refl → earliest-found ls el }
... | just k  | M′.none            = λ { refl → hl }
... | just k  | M′.found k′ bs c as with k <ᵖ k′
...   | true  = λ { refl → hl }
...   | false = λ { refl → earliest-found ls el }

earliest-foundˢ : ∀ {Γ B} (ls : List (U.Node Γ B)) {k bs l s as} → U.earliest ls ≡ U.found k bs l s as → U.headˢ s ≡ just k
earliest-foundˢ []        ()
earliest-foundˢ (l₀ ∷ ls) with U.headˢ (U.step l₀) in hl | U.earliest ls in el
... | nothing | U.none               = λ ()
... | nothing | U.found k bs c sc as = λ { refl → earliest-foundˢ ls el }
... | just k  | U.none               = λ { refl → hl }
... | just k  | U.found k′ bs c sc as with k <ᵖ k′
...   | true  = λ { refl → hl }
...   | false = λ { refl → earliest-foundˢ ls el }

------------------------------------------------------------------------
-- The outer against the lanes.

headOˢ : ∀ {Γ A} → U.Outer Γ A → Maybe Pos
headOˢ U.doneᵒ      = nothing
headOˢ (U.runᵒ _ s) = U.headˢ s

soonestˢ : ∀ {Γ A B} → U.Outer Γ A → U.Earliest Γ B → Maybe Pos
soonestˢ O E = if race? (headOˢ O) (headEˢ E) then headOˢ O else headEˢ E

soonestᴹ : ∀ {B} → Maybe (Events∞ (MonotonicList B)) → M′.Earliest B → Maybe Pos
soonestᴹ o E = if race? (M′.headᴼ o) (headE E) then M′.headᴼ o else headE E

-- Each lane opened at its element: the queue, as the meaning holds it.
Fᴹ : ∀ {Γ} {A B : Set} → (A → Pos → U.Node Γ B) → NEnv Γ → A → MonotonicList B
Fᴹ g ρ a = M′.cold λ q → U.stateᴺ (g a q) ρ

lanesˢ : ∀ {Γ B} → U.Earliest Γ B → List (U.Node Γ B) → List (U.Node Γ B)
lanesˢ U.none                ls = ls
lanesˢ (U.found k bs l s as) ls = bs ++ l ∷ as

lanesᴹ : ∀ {B} → M′.Earliest B → List (Events∞ B) → List (Events∞ B)
lanesᴹ M′.none              ls = ls
lanesᴹ (M′.found k bs l as) ls = bs ++ l ∷ as

outStepˢ : ∀ {Γ A B} → T.FlatOp → (A → Pos → U.Node Γ B) → U.Outer Γ A → List (U.Node Γ B) → List A → U.Node Γ B → U.Step Γ B
outStepˢ op g U.doneᵒ       L qs p = U.hushˢ
outStepˢ op g (U.runᵒ c so) L qs p = U.outerˢ op g c so L qs p

laneStepˢ : ∀ {Γ A B} → T.FlatOp → (A → Pos → U.Node Γ B) → U.Outer Γ A → U.Earliest Γ B → List A → U.Node Γ B → U.Step Γ B
laneStepˢ op g O U.none                qs p = U.hushˢ
laneStepˢ op g O (U.found k bs l s as) qs p = U.laneˢ op g (U.nodeᵒ O) bs l s as qs p

outEv : ∀ {B} → M′.FlatOp → Maybe (Events∞ (MonotonicList B)) → List (Events∞ B) → List (MonotonicList B) → Tail → Events B
outEv op nothing  L qs t = hush
outEv op (just e) L qs t = M′.outer op e L qs t (force e)

laneEv : ∀ {B} → M′.FlatOp → Maybe (Events∞ (MonotonicList B)) → M′.Earliest B → List (MonotonicList B) → Tail → Events B
laneEv op o M′.none              qs t = hush
laneEv op o (M′.found k bs l as) qs t = M′.lane op o bs l as qs t (force l)

go-viewˢ : ∀ {Γ A B} op (g : A → Pos → U.Node Γ B) (O : U.Outer Γ A) ls qs p E
         → U.goˢ op g O ls qs p E ≡ (if race? (headOˢ O) (headEˢ E) then outStepˢ op g O (lanesˢ E ls) qs p else laneStepˢ op g O E qs p)
go-viewˢ op g U.doneᵒ       ls qs p U.none                = refl
go-viewˢ op g (U.runᵒ c so) ls qs p U.none                = refl
go-viewˢ op g U.doneᵒ       ls qs p (U.found k bs l s as) = refl
go-viewˢ op g (U.runᵒ c so) ls qs p (U.found k bs l s as) with U.headˢ so
... | nothing = refl
... | just j  = refl

parts-view : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t
           → M′.parts op o ls qs t ≡ (if race? (M′.headᴼ o) (headE (M′.earliest ls)) then outEv op o (lanesᴹ (M′.earliest ls) ls) qs t else laneEv op o (M′.earliest ls) qs t)
parts-view op o ls qs t with M′.earliest ls | o
... | M′.none            | nothing = refl
... | M′.none            | just e  = refl
... | M′.found k bs l as | nothing = refl
... | M′.found k bs l as | just e with M′.head (force e)
...   | nothing = refl
...   | just j with j <ᵖ k
...     | true  = refl
...     | false = refl

-- An outer event and a step alike in kind and place.
data Shape {Γ X Y} : Events X → U.Step Γ Y → Set₁ where
  out⁼ˢ  : ∀ {q m r a c} → Shape (out q m r) (U.outˢ q a c)
  skip⁼ˢ : ∀ {q r c} → Shape (skip q r) (U.skipˢ q c)
  end⁼ˢ  : ∀ {c} → Shape (end c) (U.endˢ c)
  hush⁼ˢ : Shape hush U.hushˢ

shape-map : ∀ {Γ A X} (ρ : NEnv Γ) (f : A → X) (t : U.Step Γ A) (x : Events A) → Agree 1 x (afterᴱ ρ t) → Shape (M′.mapᴱ f x) t
shape-map ρ f (U.outˢ k a c) _ (out⁼ _ _)  = out⁼ˢ
shape-map ρ f (U.skipˢ k c)  _ (skip⁼ _ _) = skip⁼ˢ
shape-map ρ f (U.endˢ k)     _ end⁼        = end⁼ˢ
shape-map ρ f U.hushˢ        _ hush⁼       = hush⁼ˢ

head-mapᴱ : ∀ {A X} (f : A → X) (x : Events A) → M′.head (M′.mapᴱ f x) ≡ M′.head x
head-mapᴱ f (out k a r) = refl
head-mapᴱ f (skip k r)  = refl
head-mapᴱ f (end k)     = refl
head-mapᴱ f hush        = refl

outer-mirror : ∀ {Γ A B} op (g : A → Pos → U.Node Γ B) (c : U.Node Γ A) (ρ : NEnv Γ) (e : Events∞ (MonotonicList B)) so (y : Events (MonotonicList B)) L qs p Lᴹ t
             → null Lᴹ ≡ null L → Shape y so
             → Agree 1 (M′.outer (flatOp op) e Lᴹ (map (Fᴹ g ρ) qs) t y) (afterᴱ ρ (U.outerˢ op g c so L qs p))
outer-mirror op g c ρ e _ _ L qs p Lᴹ t _ (out⁼ˢ {q = q} {m = m} {a = a})
  with M′.admit (flatOp op) (q ++ [ ix 1 ]) m Lᴹ (map (Fᴹ g ρ) qs) | U.admit op g (q ++ [ ix 1 ]) a L qs (U.restsᶜ L)
... | _ , _ , _ | _ , _ , _ = skip⁼ stopᵀ stop
outer-mirror op g c ρ e _ _ L        qs       p Lᴹ       t _  skip⁼ˢ = skip⁼ stopᵀ stop
outer-mirror op g c ρ e _ _ []       []       p []       t _  end⁼ˢ  = end⁼
outer-mirror op g c ρ e _ _ []       (x ∷ qs) p []       t _  end⁼ˢ  = skip⁼ stopᵀ stop
outer-mirror op g c ρ e _ _ (l ∷ L)  qs       p (m ∷ Lᴹ) t _  end⁼ˢ  = skip⁼ stopᵀ stop
outer-mirror op g c ρ e _ _ []       qs       p (m ∷ Lᴹ) t () end⁼ˢ
outer-mirror op g c ρ e _ _ (l ∷ L)  qs       p []       t () end⁼ˢ
outer-mirror op g c ρ e _ _ L        qs       p Lᴹ       t _  hush⁼ˢ = hush⁼

lane-mirror : ∀ {Γ A B} op (g : A → Pos → U.Node Γ B) (o : Maybe (U.Node Γ A)) (ρ : NEnv Γ) bs l s as qs p t (x : Events B)
            → Agree 1 x (afterᴱ ρ s)
            → Agree 1 (M′.lane (flatOp op) (U.outerᴺ g o ρ) (U.states bs ρ) (U.stateᴺ l ρ) (U.states as ρ) (map (Fᴹ g ρ) qs) t x)
                      (afterᴱ ρ (U.laneˢ op g o bs l s as qs p))
lane-mirror op g o        ρ bs       l (U.outˢ k b c) as       qs       p t _ (out⁼ _ _)  = out⁼ stopᵀ stop
lane-mirror op g o        ρ bs       l (U.skipˢ k c)  as       qs       p t _ (skip⁼ _ _) = skip⁼ stopᵀ stop
lane-mirror op g o        ρ bs       l (U.endˢ c)     as       (y ∷ qs) p t _ end⁼        = skip⁼ stopᵀ stop
lane-mirror op g nothing  ρ []       l (U.endˢ c)     []       []       p t _ end⁼        = end⁼
lane-mirror op g nothing  ρ []       l (U.endˢ c)     (a ∷ as) []       p t _ end⁼        = skip⁼ stopᵀ stop
lane-mirror op g nothing  ρ (b ∷ bs) l (U.endˢ c)     as       []       p t _ end⁼        = skip⁼ stopᵀ stop
lane-mirror op g (just o) ρ bs       l (U.endˢ c)     as       []       p t _ end⁼        = skip⁼ stopᵀ stop
lane-mirror op g o        ρ bs       l U.hushˢ        as       qs       p t _ hush⁼       = hush⁼

-- What a picked part shows, the whole shows at or past it.
outer-up : ∀ {B} op (e : Events∞ (MonotonicList B)) L qs t (y : Events (MonotonicList B)) h → M′.head y ≡ just h
         → M′.outer op e L qs t y ≢ hush × (∀ a → a <ᵖ h ≡ true → a <ᵖ posᴱ (M′.outer op e L qs t y) ≡ true)
outer-up op e L qs t (out q m r) h refl with M′.admit op (q ++ [ ix 1 ]) m L qs
... | _ , _ , _ = (λ ()) , λ a ah → <ᵖ-trans a q (q ++ [ ix 0 ]) ah (<ᵖ-below q [])
outer-up op e L       qs       t (skip q r) h refl = (λ ()) , λ a ah → ah
outer-up op e []      []       t (end c)    h refl = (λ ()) , λ a ah → ah
outer-up op e []      (m ∷ qs) t (end c)    h refl = (λ ()) , λ a ah → ah
outer-up op e (l ∷ L) qs       t (end c)    h refl = (λ ()) , λ a ah → ah
outer-up op e L       qs       t hush       h ()

lane-up : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) bs l as qs t (x : Events B) h → M′.head x ≡ just h
        → M′.lane op o bs l as qs t x ≢ hush × (∀ a → a <ᵖ h ≡ true → a <ᵖ posᴱ (M′.lane op o bs l as qs t x) ≡ true)
lane-up op o        bs       l as       qs       t (out k b r) h refl = (λ ()) , λ a ah → ah
lane-up op o        bs       l as       qs       t (skip k r)  h refl = (λ ()) , λ a ah → ah
lane-up op o        bs       l as       (m ∷ qs) t (end c)     h refl = (λ ()) , λ a ah → <ᵖ-trans a c (c ++ [ ix 0 ]) ah (<ᵖ-below c [])
lane-up op nothing  []       l []       []       t (end c)     h refl = (λ ()) , λ a ah → ah
lane-up op nothing  []       l (y ∷ as) []       t (end c)     h refl = (λ ()) , λ a ah → ah
lane-up op nothing  (b ∷ bs) l as       []       t (end c)     h refl = (λ ()) , λ a ah → ah
lane-up op (just e) bs       l as       []       t (end c)     h refl = (λ ()) , λ a ah → ah
lane-up op o        bs       l as       qs       t hush        h ()

outer-upˢ : ∀ {Γ A B} op (g : A → Pos → U.Node Γ B) (c : U.Node Γ A) so L qs p a → Underᵐ (U.headˢ so) a → Underᵐ (U.headˢ (U.outerˢ op g c so L qs p)) a
outer-upˢ op g c (U.outˢ q x o′) L qs p a u with U.admit op g (q ++ [ ix 1 ]) x L qs (U.restsᶜ L)
... | _ , _ , _ = <ᵖ-trans a q (q ++ [ ix 0 ]) u (<ᵖ-below q [])
outer-upˢ op g c (U.skipˢ q o′) L       qs       p a u = u
outer-upˢ op g c (U.endˢ e)     []      []       p a u = u
outer-upˢ op g c (U.endˢ e)     []      (x ∷ qs) p a u = u
outer-upˢ op g c (U.endˢ e)     (l ∷ L) qs       p a u = u
outer-upˢ op g c U.hushˢ        L       qs       p a u = tt

lane-upˢ : ∀ {Γ A B} op (g : A → Pos → U.Node Γ B) o bs l s as qs p a → Underᵐ (U.headˢ s) a → Underᵐ (U.headˢ (U.laneˢ op g o bs l s as qs p)) a
lane-upˢ op g o        bs       l (U.outˢ k b c) as       qs       p a u = u
lane-upˢ op g o        bs       l (U.skipˢ k c)  as       qs       p a u = u
lane-upˢ op g o        bs       l (U.endˢ c)     as       (x ∷ qs) p a u = <ᵖ-trans a c (c ++ [ ix 0 ]) u (<ᵖ-below c [])
lane-upˢ op g nothing  []       l (U.endˢ c)     []       []       p a u = u
lane-upˢ op g nothing  []       l (U.endˢ c)     (y ∷ as) []       p a u = u
lane-upˢ op g nothing  (b ∷ bs) l (U.endˢ c)     as       []       p a u = u
lane-upˢ op g (just o) bs       l (U.endˢ c)     as       []       p a u = u
lane-upˢ op g o        bs       l U.hushˢ        as       qs       p a u = tt

parts-up : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t h → soonestᴹ o (M′.earliest ls) ≡ just h
         → M′.parts op o ls qs t ≢ hush × (∀ a → a <ᵖ h ≡ true → a <ᵖ posᴱ (M′.parts op o ls qs t) ≡ true)
parts-up op o ls qs t h with M′.earliest ls in el | o
... | M′.none            | nothing = λ ()
... | M′.none            | just e  = λ eq → outer-up op e ls qs t (force e) h eq
... | M′.found k bs l as | nothing = λ eq → lane-up op nothing bs l as qs t (force l) h (trans (earliest-found ls el) eq)
... | M′.found k bs l as | just e with M′.head (force e) in he
...   | nothing = λ eq → lane-up op (just e) bs l as qs t (force l) h (trans (earliest-found ls el) eq)
...   | just j with j <ᵖ k
...     | true  = λ eq → outer-up op e (bs ++ l ∷ as) qs t (force e) h (trans he eq)
...     | false = λ eq → lane-up op (just e) bs l as qs t (force l) h (trans (earliest-found ls el) eq)

go-upˢ : ∀ {Γ A B} op (g : A → Pos → U.Node Γ B) (O : U.Outer Γ A) ls qs p a → Underᵐ (soonestˢ O (U.earliest ls)) a
       → Underᵐ (U.headˢ (U.goˢ op g O ls qs p (U.earliest ls))) a
go-upˢ op g O ls qs p a with U.earliest ls in el | O
... | U.none                | U.doneᵒ     = λ _ → tt
... | U.none                | U.runᵒ c so = outer-upˢ op g c so ls qs p a
... | U.found k bs l s as   | U.doneᵒ     = λ u → lane-upˢ op g nothing bs l s as qs p a (subst (λ m → Underᵐ m a) (sym (earliest-foundˢ ls el)) u)
... | U.found k bs l s as   | U.runᵒ c so with U.headˢ so in hs
...   | nothing = λ u → lane-upˢ op g (just c) bs l s as qs p a (subst (λ m → Underᵐ m a) (sym (earliest-foundˢ ls el)) u)
...   | just j with j <ᵖ k
...     | true  = λ u → outer-upˢ op g c so (bs ++ l ∷ as) qs p a (subst (λ m → Underᵐ m a) (sym hs) u)
...     | false = λ u → lane-upˢ op g (just c) bs l s as qs p a (subst (λ m → Underᵐ m a) (sym (earliest-foundˢ ls el)) u)

-- The outer as both sides see it.
OuterP : ∀ {Γ A} → NEnv Γ → Maybe (U.Node Γ A) → Set
OuterP ρ nothing  = ⊤
OuterP ρ (just c) = Agree 1 (U.meaning c ρ) (afterᴱ ρ (U.step c))

outer-cand : ∀ {Γ A B} (ν : All (λ _ → Mode) Γ) (ρ : NEnv Γ) (g : A → Pos → U.Node Γ B) o → Firstᴹ ν o ρ
           → Cand ν ρ (OuterP ρ o) (headOˢ (U.outerOf o)) (M′.headᴼ (U.outerᴺ g o ρ))
outer-cand ν ρ g nothing  _  = inj₁ (tt , refl)
outer-cand ν ρ g (just c) fc = recand {ν = ν} {ρ = ρ} refl (sym (head-mapᴱ (Fᴹ g ρ) (U.meaning c ρ))) (λ a → a) (cand ν ρ (U.step c) (U.meaning c ρ) fc)

node-outer : ∀ {Γ A} (o : Maybe (U.Node Γ A)) → U.nodeᵒ (U.outerOf o) ≡ o
node-outer nothing  = refl
node-outer (just c) = refl

null-++ : ∀ {ℓ} {X : Set ℓ} (bs : List X) c as → null (bs ++ c ∷ as) ≡ false
null-++ []       c as = refl
null-++ (b ∷ bs) c as = refl

null-lanesˢ : ∀ {Γ B} (ls : List (U.Node Γ B)) → null (lanesˢ (U.earliest ls) ls) ≡ null ls
null-lanesˢ []       = refl
null-lanesˢ (l ∷ ls) = loud (U.earliest (l ∷ ls))
  where
    loud : ∀ E → null (lanesˢ E (l ∷ ls)) ≡ false
    loud U.none                = refl
    loud (U.found k bs c s as) = null-++ bs c as

null-lanesᴹ : ∀ {B} (ls : List (Events∞ B)) → null (lanesᴹ (M′.earliest ls) ls) ≡ null ls
null-lanesᴹ []       = refl
null-lanesᴹ (l ∷ ls) = loud (M′.earliest (l ∷ ls))
  where
    loud : ∀ E → null (lanesᴹ E (l ∷ ls)) ≡ false
    loud M′.none              = refl
    loud (M′.found k bs c as) = null-++ bs c as

null-states : ∀ {Γ B} (ls : List (U.Node Γ B)) (ρ : NEnv Γ) → null (U.states ls ρ) ≡ null ls
null-states []       ρ = refl
null-states (l ∷ ls) ρ = refl

-- THE OUTER AGAINST THE LANES: alike where both sides pick alike, the
-- picked part's own head otherwise.
rest : ∀ {Γ A B} (ν : All (λ _ → Mode) Γ) (ρ : NEnv Γ) op (g : A → Pos → U.Node Γ B) o ls qs p t → Firstᴹ ν o ρ → Firstᴸ ν ls ρ
     → Cand ν ρ (Agree 1 (M′.parts (flatOp op) (U.outerᴺ g o ρ) (U.states ls ρ) (map (Fᴹ g ρ) qs) t) (afterᴱ ρ (U.goˢ op g (U.outerOf o) ls qs p (U.earliest ls))))
                (soonestˢ (U.outerOf o) (U.earliest ls)) (soonestᴹ (U.outerᴺ g o ρ) (M′.earliest (U.states ls ρ)))
rest ν ρ op g o ls qs p t fo fl =
  recand {ν = ν} {ρ = ρ} refl refl conv (combine ν ρ race? fair-race sO mO sE mE (outer-cand ν ρ g o fo) (lanes ν ρ ls fl))
  where
    O  = U.outerOf o
    E  = U.earliest ls
    Oᴹ = U.outerᴺ g o ρ
    Ls = U.states ls ρ
    Eᴹ = M′.earliest Ls
    Qs = map (Fᴹ g ρ) qs
    sO = headOˢ O
    mO = M′.headᴼ Oᴹ
    sE = headEˢ E
    mE = headE Eᴹ
    lanes-null : null (lanesᴹ Eᴹ Ls) ≡ null (lanesˢ E ls)
    lanes-null = trans (null-lanesᴹ Ls) (trans (null-states ls ρ) (sym (null-lanesˢ ls)))
    outer-agree : ∀ o → OuterP ρ o → Agree 1 (outEv (flatOp op) (U.outerᴺ g o ρ) (lanesᴹ Eᴹ Ls) Qs t) (afterᴱ ρ (outStepˢ op g (U.outerOf o) (lanesˢ E ls) qs p))
    outer-agree nothing  _ = hush⁼
    outer-agree (just c) a = outer-mirror op g c ρ (U.outer∞ g c ρ) (U.step c) _ (lanesˢ E ls) qs p (lanesᴹ Eᴹ Ls) t lanes-null
                               (shape-map ρ (Fᴹ g ρ) (U.step c) (U.meaning c ρ) a)
    lane-agree : ∀ E′ Eᴹ′ → Mirrorᴱ ρ E′ Eᴹ′ → Agree 1 (laneEv (flatOp op) Oᴹ Eᴹ′ Qs t) (afterᴱ ρ (laneStepˢ op g O E′ qs p))
    lane-agree U.none                M′.none            _                    = hush⁼
    lane-agree (U.found k bs l s as) (M′.found _ _ _ _) (refl , refl , refl , a) =
      subst (λ o′ → Agree 1 (M′.lane (flatOp op) Oᴹ (U.states bs ρ) (U.stateᴺ l ρ) (U.states as ρ) Qs t (U.meaning l ρ)) (afterᴱ ρ (U.laneˢ op g o′ bs l s as qs p)))
            (sym (node-outer o)) (lane-mirror op g o ρ bs l s as qs p t (U.meaning l ρ) a)
    lane-agree U.none                (M′.found _ _ _ _) ()
    lane-agree (U.found _ _ _ _ _)   M′.none            ()
    conv′ : ∀ dU dM → dU ≡ dM → Pick dM (OuterP ρ o) (Mirrorᴱ ρ E Eᴹ)
          → Agree 1 (if dM then outEv (flatOp op) Oᴹ (lanesᴹ Eᴹ Ls) Qs t else laneEv (flatOp op) Oᴹ Eᴹ Qs t)
                    (afterᴱ ρ (if dU then outStepˢ op g O (lanesˢ E ls) qs p else laneStepˢ op g O E qs p))
    conv′ true  true  _  q = outer-agree o q
    conv′ false false _  q = lane-agree E Eᴹ q
    conv′ true  false () _
    conv′ false true  () _
    conv : (race? sO sE ≡ race? mO mE × Pick (race? mO mE) (OuterP ρ o) (Mirrorᴱ ρ E Eᴹ))
         → Agree 1 (M′.parts (flatOp op) Oᴹ Ls Qs t) (afterᴱ ρ (U.goˢ op g O ls qs p E))
    conv (e , q) = subst₂ (λ X S → Agree 1 X (afterᴱ ρ S)) (sym (parts-view (flatOp op) Oᴹ Ls Qs t)) (sym (go-viewˢ op g O ls qs p E))
                     (conv′ (race? sO sE) (race? mO mE) e q)

------------------------------------------------------------------------
-- The pool against the rest.

poolHeadˢ : ∀ {Γ B} → U.Step Γ B → Maybe Pos
poolHeadˢ (U.skipˢ k _) = just k
poolHeadˢ _             = nothing

pool-head : ∀ {Γ B} (t : U.Step Γ B) → RestedS t → U.headˢ t ≡ poolHeadˢ t
pool-head (U.skipˢ k c)  _ = refl
pool-head U.hushˢ        _ = refl
pool-head (U.outˢ k a c) ()
pool-head (U.endˢ k)     ()

rested-meaning : ∀ {Γ A} (t : U.Node Γ A) (ρ : NEnv Γ) → Rested t → U.meaning t ρ ≡ tailᴱ (U.cutᴺ t ρ)
rested-meaning (U.restᶜ n)                ρ _ = refl
rested-meaning U.idleᶜ                    ρ _ = refl
rested-meaning (U.unionᶜ x y)             ρ _ = refl
rested-meaning (U.burstingᶜ r t)          ρ _ = refl
rested-meaning (U.underᶜ (U.live s) b)    ρ _ = refl
rested-meaning (U.underᶜ (U.ended c t) b) ρ _ = refl
rested-meaning (U.framesᶜ τ e m)            ρ ()
rested-meaning (U.burstᶜ τ r k f)           ρ ()
rested-meaning (U.ofᶜ p k xs)               ρ ()
rested-meaning (U.mapᶜ f c)                 ρ ()
rested-meaning (U.scanᶜ f z c)              ρ ()
rested-meaning (U.takeWhileᶜ k p c)         ρ ()
rested-meaning (U.flatMapᶜ op g o ls qs pl) ρ ()
rested-meaning (U.joinᶜ j p xs e)           ρ ()
rested-meaning (U.connectᶜ r b s)           ρ ()
rested-meaning (U.deferᶜ l p ns)            ρ ()
rested-meaning (U.endingᶜ p n)              ρ ()

pool-cand : ∀ {Γ B} (ν : All (λ _ → Mode) Γ) (ρ : NEnv Γ) (pl : U.Node Γ B) → Rested pl → Firsts ν pl ρ
          → Cand ν ρ (Agree 1 (tailᴱ (U.cutᴺ pl ρ)) (afterᴱ ρ (U.step pl))) (poolHeadˢ (U.step pl)) (M′.head (tailᴱ {B} (U.cutᴺ pl ρ)))
pool-cand ν ρ pl rp fp = recand {ν = ν} {ρ = ρ} (pool-head (U.step pl) (step-rested pl rp)) refl (λ a → a)
  (cand ν ρ (U.step pl) (tailᴱ (U.cutᴺ pl ρ)) (subst (First ν ρ (U.step pl)) (rested-meaning pl ρ rp) fp))

poolStepˢ : ∀ {Γ A B} → T.FlatOp → (A → Pos → U.Node Γ B) → U.Outer Γ A → List (U.Node Γ B) → List A → U.Step Γ B → U.Step Γ B
poolStepˢ op g O ls qs (U.skipˢ k p′) = U.skipˢ k (U.flatMapᶜ op g (U.nodeᵒ O) ls qs p′)
poolStepˢ op g O ls qs _              = U.hushˢ

poolEv : ∀ {B} → M′.FlatOp → Maybe (Events∞ (MonotonicList B)) → List (Events∞ B) → List (MonotonicList B) → Tail → Events B
poolEv op o ls qs (pin k u) = M′.left op o ls qs k u true
poolEv op o ls qs idle      = hush

ahead-clears : ∀ {Γ A B} k (O : U.Outer Γ A) (E : U.Earliest Γ B) → U.aheadˢ k O E ≡ M′.clear k (headOˢ O) ∧ M′.clear k (headEˢ E)
ahead-clears k U.doneᵒ       U.none              = refl
ahead-clears k U.doneᵒ       (U.found _ _ _ _ _) = refl
ahead-clears k (U.runᵒ _ so) U.none              = trans (clearˢ-clear k (U.headˢ so)) (sym (∧-identityʳ _))
ahead-clears k (U.runᵒ _ so) (U.found j _ _ _ _) = cong (_∧ (k <ᵖ j)) (clearˢ-clear k (U.headˢ so))

flat-view : ∀ {Γ A B} op (g : A → Pos → U.Node Γ B) (O : U.Outer Γ A) ls qs p t E
          → U.flatˢ op g O ls qs p t E ≡ (if pool? (poolHeadˢ t) (soonestˢ O E) then poolStepˢ op g O ls qs t else U.goˢ op g O ls qs p E)
flat-view op g O ls qs p (U.skipˢ k p′) E = cong (λ b → if b then U.skipˢ k (U.flatMapᶜ op g (U.nodeᵒ O) ls qs p′) else U.goˢ op g O ls qs p E)
  (trans (ahead-clears k O E) (clear-min race? fair-race k (headOˢ O) (headEˢ E)))
flat-view op g O ls qs p (U.outˢ k a c) E = refl
flat-view op g O ls qs p (U.endˢ k)     E = refl
flat-view op g O ls qs p U.hushˢ        E = refl

clears-earliest : ∀ {B} k (ls : List (Events∞ B)) → M′.clears k ls ≡ M′.clear k (headE (M′.earliest ls))
clears-earliest k []       = refl
clears-earliest k (l ∷ ls) =
  trans (cong (M′.clear k h₁ ∧_) (clears-earliest k ls))
        (trans (clear-min first? fair-first k h₁ (headE (M′.earliest ls)))
               (cong (M′.clear k) (sym (trans (cong headE (earliest-view l ls)) (head-hereᴹ (first? h₁ (headE (M′.earliest ls))) l ls h₁ (M′.earliest ls))))))
  where h₁ = M′.head (force l)

go-viewᴹ : ∀ {B} op (o : Maybe (Events∞ (MonotonicList B))) ls qs t
         → M′.go op o ls qs t ≡ (if pool? (M′.head (tailᴱ {B} t)) (soonestᴹ o (M′.earliest ls)) then poolEv op o ls qs t else M′.parts op o ls qs t)
go-viewᴹ op o ls qs idle      = refl
go-viewᴹ op o ls qs (pin k u) =
  trans (left-if (M′.ahead-of k o ls))
        (cong (λ b → if b then M′.left op o ls qs k u true else M′.parts op o ls qs (pin k u))
              (trans (cong (M′.clear k (M′.headᴼ o) ∧_) (clears-earliest k ls)) (clear-min race? fair-race k (M′.headᴼ o) (headE (M′.earliest ls)))))
  where
    left-if : ∀ b → M′.left op o ls qs k u b ≡ (if b then M′.left op o ls qs k u true else M′.parts op o ls qs (pin k u))
    left-if true  = refl
    left-if false = refl

-- A FLATMAP STARTS AS ITS PARTS DO.
flat-first : ∀ {Γ A B} {ν : All (λ _ → Mode) Γ} op (g : A → Pos → U.Node Γ B) o ls qs pl (ρ : NEnv Γ)
           → Firstᴹ ν o ρ → Firstᴸ ν ls ρ → Rested pl → Firsts ν pl ρ → Firsts ν (U.flatMapᶜ op g o ls qs pl) ρ
flat-first {B = B} {ν = ν} op g o ls qs pl ρ fo fl rp fp =
  subst₂ (First ν ρ) (sym (flat-view op g O ls qs pl (U.step pl) E)) (sym (go-viewᴹ {B = B} (flatOp op) Oᴹ Ls Qs Tl))
    (finish (pool? sP sR) (pool? mP mR) (combine ν ρ pool? fair-pool sP mP sR mR (pool-cand ν ρ pl rp fp) (rest ν ρ op g o ls qs pl Tl fo fl)))
  where
    O  = U.outerOf o
    E  = U.earliest ls
    Oᴹ = U.outerᴺ g o ρ
    Ls = U.states ls ρ
    Qs = map (Fᴹ g ρ) qs
    Tl = U.cutᴺ pl ρ
    sP = poolHeadˢ (U.step pl)
    mP = M′.head (tailᴱ {B} Tl)
    sR = soonestˢ O E
    mR = soonestᴹ Oᴹ (M′.earliest Ls)
    PS = poolStepˢ op g O ls qs (U.step pl)
    GS = U.goˢ op g O ls qs pl E
    PE = poolEv (flatOp op) Oᴹ Ls Qs Tl
    GE = M′.parts (flatOp op) Oᴹ Ls Qs Tl
    pool-agree : ∀ T t → Agree 1 (tailᴱ T) (afterᴱ ρ t) → Agree 1 (poolEv (flatOp op) Oᴹ Ls Qs T) (afterᴱ ρ (poolStepˢ op g O ls qs t))
    pool-agree idle      U.hushˢ        hush⁼       = hush⁼
    pool-agree (pin k u) (U.skipˢ k c)  (skip⁼ _ _) = skip⁼ stopᵀ stop
    pool-agree idle      (U.outˢ _ _ _) ()
    pool-agree idle      (U.skipˢ _ _)  ()
    pool-agree idle      (U.endˢ _)     ()
    pool-agree (pin k u) (U.outˢ _ _ _) ()
    pool-agree (pin k u) (U.endˢ _)     ()
    pool-agree (pin k u) U.hushˢ        ()
    pool-up : ∀ T h → M′.head (tailᴱ {B} T) ≡ just h
            → poolEv (flatOp op) Oᴹ Ls Qs T ≢ hush × (∀ a → a <ᵖ h ≡ true → a <ᵖ posᴱ (poolEv (flatOp op) Oᴹ Ls Qs T) ≡ true)
    pool-up idle      h ()
    pool-up (pin k u) h refl = (λ ()) , λ a ah → ah
    pool-upˢ : ∀ t a → Underᵐ (poolHeadˢ t) a → Underᵐ (U.headˢ (poolStepˢ op g O ls qs t)) a
    pool-upˢ (U.skipˢ k c)  a u = u
    pool-upˢ (U.outˢ _ _ _) a u = tt
    pool-upˢ (U.endˢ _)     a u = tt
    pool-upˢ U.hushˢ        a u = tt
    up : ∀ dM h → (if dM then mP else mR) ≡ just h
       → (if dM then PE else GE) ≢ hush × (∀ a → a <ᵖ h ≡ true → a <ᵖ posᴱ (if dM then PE else GE) ≡ true)
    up true  h mh = pool-up Tl h mh
    up false h mh = parts-up (flatOp op) Oᴹ Ls Qs Tl h mh
    upˢ : ∀ dU a → Underᵐ (if dU then sP else sR) a → Underᵐ (U.headˢ (if dU then PS else GS)) a
    upˢ true  a u = pool-upˢ (U.step pl) a u
    upˢ false a u = go-upˢ op g O ls qs pl a u
    finish : ∀ dU dM → Cand ν ρ (dU ≡ dM × Pick dM (Agree 1 (tailᴱ Tl) (afterᴱ ρ (U.step pl))) (Agree 1 GE (afterᴱ ρ GS))) (if dU then sP else sR) (if dM then mP else mR)
           → First ν ρ (if dU then PS else GS) (if dM then PE else GE)
    finish true  true  (inj₁ ((_ , a) , _))  = inj₁ (pool-agree Tl (U.step pl) a)
    finish false false (inj₁ ((_ , a) , _))  = inj₁ a
    finish true  false (inj₁ ((() , _) , _))
    finish false true  (inj₁ ((() , _) , _))
    finish dU    dM    (inj₂ (h , mh , q))   =
      inj₂ (pos-pastᴱ ν ρ (if dU then PS else GS) (if dM then PE else GE) (proj₁ (up dM h mh))
              (move ν ρ h (if dU then sP else sR) (posᴱ (if dM then PE else GE)) (U.headˢ (if dU then PS else GS))
                    (λ a ah u → proj₂ (up dM h mh) a ah , upˢ dU a u) q))
