-- ══════════════════════════════════════════════════════════════════
-- ONE LEVEL DOES NOT PAY FOR A REBUILD, which is the second thing
-- this frame law got wrong and the one its own size sibling already
-- knew.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree may not import the statement it refutes: the proposition is
-- written out again here, so `src` may move its own copy freely and
-- this file goes red the day the two stop agreeing.
--
-- WHAT THE STATEMENT SAID.  Values arriving at a `map-f` carry a
-- closure reading at the level the caller is at; the values the frame
-- passes on carry the reading ONE level up -- and the caller's other
-- premises now price the frame's own function (`pathSz?`) and the
-- arriving payload (`valsCaps?`) at that same level, which is what the
-- flat form was missing.
--
-- WHY IT LOOKED RIGHT.  With the function priced, the output is the
-- function's body with the argument substituted in, so its closure is
-- bounded by a PRODUCT of two quantities both under the cap -- and a
-- level multiplies the cap by roughly `2 * cSize`.  The step looks
-- like it dominates because the cap reads as the bigger of the two
-- factors.
--
-- WHERE IT BREAKS.  It is not the bigger factor: both factors ARE the
-- cap.  A template holding `w` copies of its argument has size `w + 3`
-- and an argument of closure `V` has size `V + 2`, so the caller's
-- premises admit `w` and `V` each within one of the level's own cap
-- `X`, while the output's closure is `w * V`, which is `X²`.  One
-- level buys `X ↦ S * (1 + 2X)`, linear in `X`, and a linear step
-- cannot pay a square.  The witness takes `w = V = S²` at level one,
-- where the output exceeds `S⁴` and the level-two cap is
-- `S + 2S² + 4S³`, under `S⁴` by the base supply `8 ≤ S`.
--
-- WHAT IT COSTS.  The repair is not a bigger constant: the frame has
-- to be charged the levels its SIZE sibling already charges, one per
-- unit of `sizeᵗ` of the frame's own function, which is where the size
-- face puts its own map arm's `face-charge1`.
--
-- THE WITNESS IS SYMBOLIC, WHICH IS STRONGER THAN A ROW HERE.  `S` is
-- never computed: every quantity is built FROM the cap, so no
-- enlargement of the cap escapes it.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Step-Frame-Clos-Level where

open import Data.Bool using (Bool; true; false; T)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _≤ᵇ_; _+_; _*_; _^_; _⊔_;
  s≤s; z≤n)
open import Data.Nat.Properties using (≤ᵇ⇒≤; ≤-trans; ≤-refl; 1+n≰n; n≤1+n; <⇒≤; +-mono-≤; *-monoˡ-≤; *-monoʳ-≤; *-identityʳ;
  ⊔-identityʳ; +-monoʳ-≤; +-monoˡ-≤; +-comm; m≤m+n)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Data.Fin using (Fin) renaming (zero to fzero)
open import Data.Product using (proj₁)
open import Data.Unit using (tt)
open import Data.Bool.ListAction using (all)
open import Data.List.Relation.Unary.Any using (here)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong;
  subst; trans; cong₂)

open import Decide using (∧-intro; ∧-trueˡ; ≤ᵇ-true)
open import Rx.Prim using (Gas; g0; hot; Tick; Id)
open import Rx.Exp using (Ctx; Closed; Val; Tm; Fn; Ren∈; natᵗ; obs; input; ofᵉ; nat̂; strmᵗ; varᵗ; renTms; sizeᵗ;
  sizeᵗˢ; sizeᵉ; sizeᵛ; subΘTm; subΘTms)
open import Rx.Clos-Size using (closSizeᵉ; closSizeᵗ; closSizeᵗˢ)
open import Rx.Frame-Width using (dWᵗˢⱽ; pWᵛ)
open import Rx.Slots using (Slots; scripted)
open import Rx.Slot-Clos using (slotClos)
open import Rx.Evaluator using (Sched; EvalSt; Path; root; _↠_; map-f; stepFrame; sched-init; st-init)
open import Verify-Budget-Sufficient.Caps using (Caps; capsAt; frameStep;
  8≤capsAt-size; capsAt-base-wid)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (capsOK?;
  nestClosOK?ᵛ; pathSz?)
open import Verify-Budget-Sufficient.Caps-Face.Part4 using (valsCaps?)

------------------------------------------------------------------
-- the statement, restated at the level the migration proposes
------------------------------------------------------------------

StepFrameClosMap : Set
StepFrameClosMap = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (sl : Slots Γ) (id : ℕ) (L : ℕ) (sf : Gas) (nid : Id) (now : Tick)
  (fn : Fn Γ [] [] [] s u)
  (p : Path Γ u t) (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (frameStep L (capsAt e sl id)) sched st ≡ true →
  pathSz? (Caps.cSize (frameStep L (capsAt e sl id))) ((map-f fn) ↠ p) ≡ true →
  valsCaps? (frameStep L (capsAt e sl id)) sl vals ≡ true →
  all (nestClosOK?ᵛ (frameStep L (capsAt e sl id)) sl s) vals ≡ true →
  all (nestClosOK?ᵛ (frameStep (suc L) (capsAt e sl id)) sl u)
      (proj₁ (stepFrame sf nid now (map-f fn) p vals fin sched st)) ≡ true

------------------------------------------------------------------
-- the program, and the two quantities built out of its own cap
------------------------------------------------------------------

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

sl₁ : Slots Γ₁
sl₁ fzero = scripted (hot [])

σ₁ : Fin 1 → ℕ
σ₁ = slotClos sl₁

e₁ : Closed Γ₁ (obs (obs natᵗ))
e₁ = ofᵉ (strmᵗ (ofᵉ (strmᵗ (input fzero) ∷ [])) ∷ [])

c₀ : Caps
c₀ = capsAt e₁ sl₁ 0

S : ℕ
S = Caps.cSize c₀

W : ℕ
W = Caps.cWid c₀

K : ℕ
K = S * S

nats : ∀ {Δᵍ Δ Θ} → ℕ → List (Tm Γ₁ Δᵍ Δ Θ natᵗ)
nats zero    = []
nats (suc k) = nat̂ 0 ∷ nats k

v : Val Γ₁ (obs natᵗ)
v = ofᵉ (nats K)

vars : ℕ → List (Tm Γ₁ [] [] (obs natᵗ ∷ []) (obs natᵗ))
vars zero    = []
vars (suc k) = varᵗ (here refl) ∷ vars k

fnW : Fn Γ₁ [] [] [] (obs natᵗ) (obs (obs natᵗ))
fnW = strmᵗ (ofᵉ (vars K))

------------------------------------------------------------------
-- what the pieces measure
------------------------------------------------------------------

nats-clos : ∀ {Δᵍ Δ Θ} (k : ℕ) → closSizeᵗˢ σ₁ (nats {Δᵍ} {Δ} {Θ} k) ≡ suc k
nats-clos zero    = refl
nats-clos (suc k) = cong suc (nats-clos k)

nats-size : ∀ {Δᵍ Δ Θ} (k : ℕ) → sizeᵗˢ (nats {Δᵍ} {Δ} {Θ} k) ≡ suc k
nats-size zero    = refl
nats-size (suc k) = cong suc (nats-size k)

nats-len : ∀ {Δᵍ Δ Θ} (k : ℕ) → length (nats {Δᵍ} {Δ} {Θ} k) ≡ k
nats-len zero    = refl
nats-len (suc k) = cong suc (nats-len k)

nats-dW : ∀ {Δᵍ Δ Θ} (j : ℕ) (k : ℕ) →
  dWᵗˢⱽ {Γ = Γ₁} {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} j [] sl₁ (nats k) ≡ 0
nats-dW j zero    = refl
nats-dW j (suc k) = nats-dW j k

nats-ren-clos : ∀ {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′}
  (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′) (k : ℕ) →
  closSizeᵗˢ σ₁ (renTms {t = natᵗ} ρg ρd ρt (nats k)) ≡ suc k
nats-ren-clos ρg ρd ρt zero    = refl
nats-ren-clos ρg ρd ρt (suc k) = cong suc (nats-ren-clos ρg ρd ρt k)

vars-size : ∀ (k : ℕ) → sizeᵗˢ (vars k) ≡ suc k
vars-size zero    = refl
vars-size (suc k) = cong suc (vars-size k)

-- the weakened copy of the argument the substitution plants at every
-- variable position, and the only quantity the output is made of
one : Tm Γ₁ [] [] [] (obs natᵗ)
one = subΘTm {Θsub = obs natᵗ ∷ []} [] (v ∷ᵃ []ᵃ) (varᵗ (here refl))

one-clos : closSizeᵗ σ₁ one ≡ suc (suc (suc K))
one-clos = cong (λ x → suc (suc x)) (nats-ren-clos _ _ _ K)

vars-mul : ∀ (k : ℕ) →
  k * closSizeᵗ σ₁ one ≤
  closSizeᵗˢ σ₁ (subΘTms {Θsub = obs natᵗ ∷ []} [] (v ∷ᵃ []ᵃ) (vars k))
vars-mul zero    = z≤n
vars-mul (suc k) = +-mono-≤ ≤-refl (vars-mul k)

------------------------------------------------------------------
-- the arithmetic: a linear step against a square
------------------------------------------------------------------

1≤pow : ∀ (b w : ℕ) → 1 ≤ b → 1 ≤ b ^ w
1≤pow b zero    hb = ≤-refl
1≤pow b (suc w) hb =
  ≤-trans hb (subst (λ x → x ≤ b * b ^ w) (*-identityʳ b)
                    (*-monoʳ-≤ b (1≤pow b w hb)))

b≤pow : ∀ (b w : ℕ) → 1 ≤ b → 1 ≤ w → b ≤ b ^ w
b≤pow b (suc w) hb _ =
  subst (λ x → x ≤ b * b ^ w) (*-identityʳ b) (*-monoʳ-≤ b (1≤pow b w hb))

8≤S : 8 ≤ S
8≤S = 8≤capsAt-size e₁ sl₁ 0

1≤S : 1 ≤ S
1≤S = ≤-trans (s≤s z≤n) 8≤S

3≤S : 3 ≤ S
3≤S = ≤-trans (s≤s (s≤s (s≤s z≤n))) 8≤S

1≤W : 1 ≤ W
1≤W = ≤-trans (s≤s z≤n) (capsAt-base-wid e₁ sl₁ 0)

A B : ℕ
A = S * S
B = S * (S * S)

X≡ : S * suc (2 * S) ≡ S + (A + A)
X≡ = solve 1 (λ s → s :* (con 1 :+ con 2 :* s) := s :+ (s :* s :+ s :* s)) refl S

Y≡ : S * suc (2 * (S * suc (2 * S))) ≡ S + (A + A) + (B + B + B + B)
Y≡ = solve 1 (λ s →
       s :* (con 1 :+ con 2 :* (s :* (con 1 :+ con 2 :* s)))
       := s :+ (s :* s :+ s :* s)
          :+ (s :* (s :* s) :+ s :* (s :* s) :+ s :* (s :* s) :+ s :* (s :* s)))
     refl S

KK≡ : K * K ≡ S * B
KK≡ = solve 1 (λ s → (s :* s) :* (s :* s) := s :* (s :* (s :* s))) refl S

1≤A : 1 ≤ A
1≤A = ≤-trans 1≤S (subst (λ x → x ≤ S * S) (*-identityʳ S) (*-monoʳ-≤ S 1≤S))

1≤B : 1 ≤ B
1≤B = ≤-trans 1≤S (subst (λ x → x ≤ S * (S * S)) (*-identityʳ S) (*-monoʳ-≤ S 1≤A))

S≤B : S ≤ B
S≤B = subst (λ x → x ≤ S * (S * S)) (*-identityʳ S) (*-monoʳ-≤ S 1≤A)

A≤B : A ≤ B
A≤B = *-monoʳ-≤ S (subst (λ x → x ≤ S * S) (*-identityʳ S) (*-monoʳ-≤ S 1≤S))

-- the level-two cap, against the square the map produced
sevenB : ℕ
sevenB = (B + (B + B)) + (B + B + B + B)

Y≤7B : S * suc (2 * (S * suc (2 * S))) ≤ sevenB
Y≤7B = subst (λ x → x ≤ sevenB) (sym Y≡)
  (+-mono-≤ (+-mono-≤ S≤B (+-mono-≤ A≤B A≤B)) ≤-refl)

7B≡ : sevenB ≡ 7 * B
7B≡ = solve 1 (λ b → (b :+ (b :+ b)) :+ (b :+ b :+ b :+ b) := con 7 :* b) refl B

8B≡ : 7 * B + B ≡ 8 * B
8B≡ = solve 1 (λ b → con 7 :* b :+ b := con 8 :* b) refl B

7B<KK : sevenB < K * K
7B<KK = subst (λ x → sevenB < x) (sym KK≡)
  (subst (λ x → x < S * B) (sym 7B≡)
    (≤-trans (subst (λ x → x ≤ 7 * B + B) (+-comm (7 * B) 1)
                    (+-monoʳ-≤ (7 * B) 1≤B))
             (subst (λ x → x ≤ S * B) (sym 8B≡) (*-monoˡ-≤ B 8≤S))))

------------------------------------------------------------------
-- the premises the caller does supply
------------------------------------------------------------------

fn≤X : suc (suc (suc K)) ≤ S * suc (2 * S)
fn≤X = subst (λ x → suc (suc (suc K)) ≤ x) (sym X≡)
  (≤-trans (+-monoˡ-≤ K 3≤S) (+-monoʳ-≤ S (m≤m+n A A)))

K≤pow : K ≤ S ^ suc W
K≤pow = *-monoʳ-≤ S (b≤pow S W 1≤S 1≤W)

K2≤X : suc (suc K) ≤ S * suc (2 * S)
K2≤X = ≤-trans (n≤1+n (suc (suc K))) fn≤X

S≤X : S ≤ S * suc (2 * S)
S≤X = subst (λ x → x ≤ S * suc (2 * S)) (*-identityʳ S) (*-monoʳ-≤ S (s≤s z≤n))

1≤X : 1 ≤ S * suc (2 * S)
1≤X = ≤-trans 1≤S S≤X

fnsz : sizeᵗ fnW ≡ suc (suc (suc K))
fnsz = cong (λ x → suc (suc x)) (vars-size K)

vsz : sizeᵉ v ≡ suc (suc K)
vsz = cong suc (nats-size K)

vclos : closSizeᵉ σ₁ v ≡ suc (suc K)
vclos = cong suc (nats-clos K)

vpW : pWᵛ 1 sl₁ (obs natᵗ) v ≡ K
vpW = trans (cong₂ _⊔_ (nats-len K) (nats-dW 1 K)) (⊔-identityʳ K)

------------------------------------------------------------------
-- the premises the caller does supply, at level one
------------------------------------------------------------------

hp : pathSz? (Caps.cSize (frameStep 1 c₀)) ((map-f fnW) ↠ root) ≡ true
hp = ∧-intro (≤ᵇ-true (sizeᵗ fnW) _
               (subst (λ x → x ≤ S * suc (2 * S)) (sym fnsz) fn≤X))
             (∧-intro (≤ᵇ-true 1 _ 1≤X) refl)

hvc : valsCaps? (frameStep 1 c₀) sl₁ (v ∷ []) ≡ true
hvc = ∧-intro
        (∧-intro (∧-intro (≤ᵇ-true (sizeᵛ (obs natᵗ) v) _
                            (subst (λ x → x ≤ S * suc (2 * S)) (sym vsz) K2≤X))
                          (≤ᵇ-true (pWᵛ 1 sl₁ (obs natᵗ) v) _
                            (subst (λ x → x ≤ S ^ suc W) (sym vpW) K≤pow)))
                 refl)
        (≤ᵇ-true 1 (suc (Caps.cWid (frameStep 1 c₀))) (s≤s z≤n))

hcl : all (nestClosOK?ᵛ (frameStep 1 c₀) sl₁ (obs natᵗ)) (v ∷ []) ≡ true
hcl = ∧-intro (≤ᵇ-true (closSizeᵉ σ₁ v) _
                (subst (λ x → x ≤ S * suc (2 * S)) (sym vclos) K2≤X))
              refl

h : StepFrameClosMap →
  all (nestClosOK?ᵛ (frameStep 2 c₀) sl₁ (obs (obs natᵗ)))
    (proj₁ (stepFrame {e = e₁} g0 0 0 (map-f fnW) root (v ∷ []) false
              (sched-init e₁ sl₁) (st-init e₁))) ≡ true
h pr = pr sl₁ 0 1 g0 0 0 fnW root (v ∷ []) false
          (sched-init e₁ sl₁) (st-init e₁) refl refl hp hvc hcl

subs : List (Tm Γ₁ [] [] [] (obs natᵗ))
subs = subΘTms {Θsub = obs natᵗ ∷ []} [] (v ∷ᵃ []ᵃ) (vars K)

big : K * K ≤ closSizeᵗˢ σ₁ subs
big = ≤-trans (*-monoʳ-≤ K (subst (λ x → K ≤ x) (sym one-clos)
                             (≤-trans (n≤1+n K) (≤-trans (n≤1+n _) (n≤1+n _)))))
              (vars-mul K)

conj : StepFrameClosMap →
  (suc (closSizeᵗˢ σ₁ subs) ≤ᵇ Caps.cSize (frameStep 2 c₀)) ≡ true
conj pr = ∧-trueˡ (h pr)

------------------------------------------------------------------
-- the refutation
------------------------------------------------------------------

step-frame-clos-map-absurd : StepFrameClosMap → ⊥
step-frame-clos-map-absurd pr = 1+n≰n lt
  where
  lt : K * K < K * K
  lt = ≤-trans (s≤s big)
        (≤-trans (≤ᵇ⇒≤ _ _ (subst T (sym (conj pr)) tt))
          (≤-trans Y≤7B (<⇒≤ 7B<KK)))
