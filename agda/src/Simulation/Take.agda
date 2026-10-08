------------------------------------------------------------------
-- A TEST'S ARM: the plain takeWhile steps once where the impl runs its
-- cut cell's scan, the cell's test, the projection and the one-lane
-- merge.  The cell spends where the test does, so an open group leaves
-- both sides open at a budget of one; the group that ends, and the
-- spent test, are leaves.
------------------------------------------------------------------
module Simulation.Take where

open import Data.Bool    using (Bool; true; false; _∧_)
open import Data.Empty   using (⊥; ⊥-elim)
open import Data.List    using (List; []; _∷_; _++_; map)
open import Data.Maybe   using (Maybe; just)
open import Data.Nat     using (ℕ; zero; suc; _≤_; _<ᵇ_)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Unit    using (tt)
open import Data.List.Properties using (++-identityʳ)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst; subst₂)

open import Rx.Exp       using (Ctx; Closed; Val; Env; FnClo; boolᵗ; unitᵗ; _×ᵗ_; applyClo; _≟ᵗ_)
open import Rx.Evaluator using (EvalSt; Sched; NodeId; NodeState; Path; _↠[_]_; scan-f; take-f; map-f; lookupNode; setNode;
  cell-st; take-st; takeVals; scanVals; spends; takeDispatch; cutThrough)
open import Rx.Evaluator.Domain using (stepFrame⇓; foldPath⇓; fold-step; step-scan; step-take; step-map; injectRoot)
open import Rx.Evaluator.Freshness using (lookup-set; set-above)
open import Rx.Evaluator.Reducible.Support using (Sound; drop-ot; head-on; self-node)
open import Rx.Evaluator.Reducible.Rule-Kept using (step-kept)
open import SExp.Syntax  using (Kinds; plainᵏ; emitᵗ)
open import SExp.Elaborate using (CutS; cutOpenᵛ; cutOutᵛ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Binary.Pointwise using () renaming ([] to []ᵖ)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Simulation.Stores using (EmitRel; CutLifts; PathRel; takeWhile~; spentWhile~; Store; guardOf)
open import Simulation.Sweep using (t≢f; sweepL; sweep-eq)
open import Simulation.Cut using (cut-go; cut-keeps; cut-persists)
open import Simulation.Write using (apart)
open import Simulation.After using (module Kept)
open import Simulation.Arm using (module Arms; Clear; fold-unmoved; on-drop; step-clear; Out; out-quiet)

-- A CELL'S SCAN AND A TEST'S TAKE, AT THE STATE THE NODE HOLDS: the
-- one step each derivation can be
scan-at : ∀ {m} {Δ : Ctx m} {t} {e : Closed Δ t} {s u lo} {fn : FnClo Δ (u ×ᵗ s) u} {k} {κ′ : Path Δ lo u t}
            {now vals fin sc} {st : EvalSt e} {a r}
        → lookupNode k (EvalSt.nodes st) ≡ just (cell-st {t = u} a)
        → stepFrame⇓ now (scan-f fn k) κ′ vals fin sc st r
        → r ≡ ([] , proj₁ (scanVals fn a vals) , fin , sc
              , record st { nodes = setNode k (cell-st (proj₂ (scanVals fn a vals))) (EvalSt.nodes st) })
scan-at {u = u} e step-scan rewrite e with u ≟ᵗ u
... | yes refl = refl
... | no ne    = ⊥-elim (ne refl)

take-at : ∀ {m} {Δ : Ctx m} {t} {e : Closed Δ t} {s lo w k} {κ′ : Path Δ lo s t}
            {now vals fin sc} {st : EvalSt e} {b r}
        → lookupNode k (EvalSt.nodes st) ≡ just (take-st b)
        → stepFrame⇓ now (take-f w k) κ′ vals fin sc st r
        → r ≡ injectRoot (takeDispatch w k vals fin sc st (just (take-st b)))
take-at e step-take rewrite e = refl

-- a test that does not cut writes what it leaves and passes the end on
take-open-at : ∀ {m} {Δ : Ctx m} {t} {e : Closed Δ t} {s lo w k} {κ′ : Path Δ lo s t}
                 {now vals fin sc} {st : EvalSt e} {b r}
             → lookupNode k (EvalSt.nodes st) ≡ just (take-st b)
             → proj₂ (proj₂ (takeVals w b vals)) ≡ false
             → stepFrame⇓ now (take-f w k) κ′ vals fin sc st r
             → r ≡ ([] , proj₁ (takeVals w b vals) , fin ∧ (0 <ᵇ b) , sc
                   , record st { nodes = setNode k (take-st (proj₁ (proj₂ (takeVals w b vals)))) (EvalSt.nodes st) })
take-open-at e h d rewrite take-at e d | h = refl

-- and one that cuts severs the rows through its node, writes zero and ends
take-cut-at : ∀ {m} {Δ : Ctx m} {t} {e : Closed Δ t} {s lo w k} {κ′ : Path Δ lo s t}
                {now vals fin sc} {st : EvalSt e} {b r}
            → lookupNode k (EvalSt.nodes st) ≡ just (take-st b)
            → proj₂ (proj₂ (takeVals w b vals)) ≡ true
            → stepFrame⇓ now (take-f w k) κ′ vals fin sc st r
            → r ≡ ([] , proj₁ (takeVals w b vals) , true
                  , record sc { live = sweepL (guardOf (proj₁ (cutThrough k (EvalSt.registry st)))) (Sched.live sc) }
                  , record st { registry = proj₁ (cutThrough k (EvalSt.registry st))
                              ; cancelled = proj₂ (cutThrough k (EvalSt.registry st)) ++ EvalSt.cancelled st
                              ; nodes = setNode k (take-st 0) (EvalSt.nodes st) })
take-cut-at {k = k} {sc = sc} {st = st} e h d
  rewrite take-at e d | h | sweep-eq (proj₁ (cutThrough k (EvalSt.registry st))) (Sched.live sc) = refl

cut-cons : ∀ {m} {Δ : Ctx m} {s} (w : Maybe (FnClo Δ s boolᵗ)) b (vs : List (Val Δ s))
         → proj₂ (proj₂ (takeVals w b vs)) ≡ true → proj₁ (takeVals w b vs) ≢ []
cut-cons w zero          _        ()
cut-cons w (suc b)       []       ()
cut-cons w (suc zero)    (v ∷ vs) _ with spends w v
... | true  = λ ()
... | false = λ ()
cut-cons w (suc (suc b)) (v ∷ vs) _ with spends w v
... | true  = λ ()
... | false = λ ()

map-cons : ∀ {A B : Set} (f : A → B) xs → xs ≢ [] → map f xs ≢ []
map-cons f []       ne = ⊥-elim (ne refl)
map-cons f (x ∷ xs) ne = λ ()

-- a cell and a count never share a node
cell-take : ∀ {m} {Δ : Ctx m} {N : List (NodeId × NodeState Δ)} {k k′ u b} {a : Val Δ u}
          → lookupNode k N ≡ just (cell-st a) → lookupNode k′ N ≡ just (take-st b) → k′ ≡ k → ⊥
cell-take l l′ refl with trans (sym l) l′
... | ()

module Takes {n} {Γ : Ctx n} (κ : Kinds n) where

  open Arms {Γ = Γ} κ

  -- A COUNT'S PLAIN STEP, A VALUE AT A TIME: an empty group passes
  -- nothing and keeps the count, a head that does not cut hands the
  -- rest the count it leaves, and one that cuts ends the group
  take-nil : ∀ {s} (P : Maybe (FnClo Γ s boolᵗ)) b → takeVals P b [] ≡ ([] , b , false)
  take-nil P zero    = refl
  take-nil P (suc b) = refl

  take-go : ∀ {s} (P : Maybe (FnClo Γ s boolᵗ)) b w vs → proj₂ (proj₂ (takeVals P b (w ∷ []))) ≡ false
          → takeVals P b (w ∷ vs) ≡ ( proj₁ (takeVals P b (w ∷ [])) ++ proj₁ (takeVals P (proj₁ (proj₂ (takeVals P b (w ∷ [])))) vs)
                                    , proj₂ (takeVals P (proj₁ (proj₂ (takeVals P b (w ∷ [])))) vs))
  take-go P zero          w vs _ = refl
  take-go P (suc zero)    w vs h with spends P w
  ... | true  = ⊥-elim (t≢f h)
  ... | false = refl
  take-go P (suc (suc b)) w vs h with spends P w
  ... | true  = refl
  ... | false = refl

  take-stop : ∀ {s} (P : Maybe (FnClo Γ s boolᵗ)) b w vs → proj₂ (proj₂ (takeVals P b (w ∷ []))) ≡ true
            → takeVals P b (w ∷ vs) ≡ takeVals P b (w ∷ [])
  take-stop P zero          w vs h = ⊥-elim (t≢f (sym h))
  take-stop P (suc zero)    w vs h with spends P w
  ... | true  = refl
  ... | false = ⊥-elim (t≢f (sym h))
  take-stop P (suc (suc b)) w vs h with spends P w
  ... | true  = ⊥-elim (t≢f (sym h))
  ... | false = ⊥-elim (t≢f (sym h))

  -- one value passes or not
  take-one : ∀ {s} (P : Maybe (FnClo Γ s boolᵗ)) b w → proj₁ (takeVals P b (w ∷ [])) ≡ [] ⊎ proj₁ (takeVals P b (w ∷ [])) ≡ w ∷ []
  take-one P zero          w = inj₁ refl
  take-one P (suc zero)    w with spends P w
  ... | true  = inj₂ refl
  ... | false = inj₂ refl
  take-one P (suc (suc b)) w with spends P w
  ... | true  = inj₂ refl
  ... | false = inj₂ refl

  carry-cons : ∀ {s} (e′ : Val (plainᵏ Γ κ) (emitᵗ s)) {xs es′ vs} → EmitRel κ s e′ xs → (xs ≡ [] ⊎ Σ (Val Γ s) λ w → xs ≡ w ∷ [])
             → Carries es′ vs → Carries (e′ ∷ es′) (xs ++ vs)
  carry-cons e′ r (inj₁ refl)       b = quiet e′ r b
  carry-cons e′ r (inj₂ (_ , refl)) b = one e′ r b

  -- THE IMPL'S CUT CELL PASSES ITSELF WHILE OPEN, AND ONCE CLOSED
  module _ {B s} {Θ ρ} where

    open-step : ∀ (c : Val (plainᵏ Γ κ) (CutS B s)) cs → proj₁ (proj₂ c) ≡ false
              → takeVals (just (Θ , cutOpenᵛ , ρ)) 1 (c ∷ cs) ≡ (c ∷ proj₁ (takeVals (just (Θ , cutOpenᵛ , ρ)) 1 cs) , proj₂ (takeVals (just (Θ , cutOpenᵛ , ρ)) 1 cs))
    open-step (_ , _ , _) cs refl = refl

    closed-step : ∀ (c : Val (plainᵏ Γ κ) (CutS B s)) cs → proj₁ (proj₂ c) ≡ true
                → takeVals (just (Θ , cutOpenᵛ , ρ)) 1 (c ∷ cs) ≡ (c ∷ [] , 0 , true)
    closed-step (_ , _ , _) cs refl = refl

  -- THE IMPL'S CUT CELL OVER A GROUP SPENDS WHERE THE PLAIN COUNT DOES:
  -- an open cell scanned over the emits and passed while open carries
  -- what the count passes of the values, cuts exactly when it does, and
  -- when neither cuts is left open over the count's budget
  module _ {B s} {Bud : Val (plainᵏ Γ κ) B → ℕ → Set} {F′ : FnClo (plainᵏ Γ κ) (CutS B s ×ᵗ emitᵗ s) (CutS B s)}
           {P : Maybe (FnClo Γ s boolᵗ)} {Θ₂ ρ₂ Θ₃ ρ₃} (L : CutLifts κ B s Bud F′ P) where

    Res : List (Val (plainᵏ Γ κ) (emitᵗ s)) → List (Val (plainᵏ Γ κ) (CutS B s)) × ℕ × Bool → List (Val Γ s) × ℕ × Bool
        → Val (plainᵏ Γ κ) (CutS B s) → Set
    Res es T W fc =
        Carries (map (applyClo (Θ₃ , cutOutᵛ , ρ₃)) (proj₁ T)) (proj₁ W)
      × proj₂ (proj₂ T) ≡ proj₂ (proj₂ W)
      × (proj₂ (proj₂ W) ≡ false → proj₁ (proj₂ T) ≡ 1 × proj₁ (proj₂ fc) ≡ false × Bud (proj₁ fc) (proj₁ (proj₂ W)))
      × (∀ {I} → All (DelAt I) es → All (DelAt I) (map (applyClo (Θ₃ , cutOutᵛ , ρ₃)) (proj₁ T)))

    Spent : Val (plainᵏ Γ κ) (CutS B s) → List (Val (plainᵏ Γ κ) (emitᵗ s)) → ℕ → List (Val Γ s) → Set
    Spent c es b vs = Res es (takeVals (just (Θ₂ , cutOpenᵛ , ρ₂)) 1 (proj₁ (scanVals F′ c es))) (takeVals P b vs) (proj₂ (scanVals F′ c es))

    cut-group : ∀ {es vs} → Carries es vs → ∀ c b → proj₁ (proj₂ c) ≡ false → Bud (proj₁ c) b → Spent c es b vs
    cut-group [] c b h bud rewrite take-nil P b = [] , refl , (λ _ → refl , h , bud) , λ _ → []
    cut-group (quiet e′ {es′} {vs} r bs) (b′ , .false , os , em) b refl bud =
      subst (λ T → Res (e′ ∷ es′) T (takeVals P b vs) (proj₂ (scanVals F′ c₁ es′))) (sym (open-step {Θ = Θ₂} {ρ = ρ₂} c₁ (proj₁ (scanVals F′ c₁ es′)) h₁))
            ( quiet _ bare₁ (proj₁ IH) , proj₁ (proj₂ IH) , proj₁ (proj₂ (proj₂ IH))
            , λ { (d ∷ ds) → del-keep (applyClo (Θ₃ , cutOutᵛ , ρ₃) c₁) e′ (proj₂ (proj₂ (proj₂ CL))) d ∷ proj₂ (proj₂ (proj₂ IH)) ds })
      where
        c₁   = applyClo F′ ((b′ , false , os , em) , e′)
        CL   = L b′ b os em e′ [] bud r
        nil  = take-nil P b
        h₁   : proj₁ (proj₂ c₁) ≡ false
        h₁   = trans (proj₁ (proj₂ CL)) (cong (λ T → proj₂ (proj₂ T)) nil)
        bud₁ : Bud (proj₁ c₁) b
        bud₁ = subst (λ T → Bud (proj₁ c₁) (proj₁ (proj₂ T))) nil (proj₁ CL (cong (λ T → proj₂ (proj₂ T)) nil))
        bare₁ : Bare (applyClo (Θ₃ , cutOutᵛ , ρ₃) c₁)
        bare₁ = subst (λ T → EmitRel κ s (applyClo (Θ₃ , cutOutᵛ , ρ₃) c₁) (proj₁ T)) nil (proj₁ (proj₂ (proj₂ CL)))
        IH   = cut-group bs c₁ b h₁ bud₁
    cut-group (one e′ {es′} {w} {vs} r bs) (b′ , .false , os , em) b refl bud = go _ refl
      where
        c₁ = applyClo F′ ((b′ , false , os , em) , e′)
        CL = L b′ b os em e′ (w ∷ []) bud r
        W₀ = takeVals P b (w ∷ [])
        once : proj₁ W₀ ≡ [] ⊎ Σ (Val Γ s) λ x → proj₁ W₀ ≡ x ∷ []
        once with take-one P b w
        ... | inj₁ e = inj₁ e
        ... | inj₂ e = inj₂ (w , e)
        go : ∀ x → proj₂ (proj₂ W₀) ≡ x → Spent (b′ , false , os , em) (e′ ∷ es′) b (w ∷ vs)
        go false eq =
          subst₂ (λ T W → Res (e′ ∷ es′) T W (proj₂ (scanVals F′ c₁ es′))) (sym (open-step {Θ = Θ₂} {ρ = ρ₂} c₁ (proj₁ (scanVals F′ c₁ es′)) h₁)) (sym (take-go P b w vs eq))
                 ( carry-cons _ (proj₁ (proj₂ (proj₂ CL))) once (proj₁ IH) , proj₁ (proj₂ IH) , proj₁ (proj₂ (proj₂ IH))
                 , λ { (d ∷ ds) → del-keep (applyClo (Θ₃ , cutOutᵛ , ρ₃) c₁) e′ (proj₂ (proj₂ (proj₂ CL))) d ∷ proj₂ (proj₂ (proj₂ IH)) ds })
          where
            h₁ = trans (proj₁ (proj₂ CL)) eq
            IH = cut-group bs c₁ (proj₁ (proj₂ W₀)) h₁ (proj₁ CL eq)
        go true eq =
          subst₂ (λ T W → Res (e′ ∷ es′) T W (proj₂ (scanVals F′ c₁ es′))) (sym (closed-step {Θ = Θ₂} {ρ = ρ₂} c₁ (proj₁ (scanVals F′ c₁ es′)) (trans (proj₁ (proj₂ CL)) eq))) (sym (take-stop P b w vs eq))
                 ( subst (Carries (applyClo (Θ₃ , cutOutᵛ , ρ₃) c₁ ∷ [])) (++-identityʳ (proj₁ W₀))
                         (carry-cons _ (proj₁ (proj₂ (proj₂ CL))) once [])
                 , sym eq , (λ f → ⊥-elim (t≢f (trans (sym eq) f)))
                 , λ { (d ∷ _) → del-keep (applyClo (Θ₃ , cutOutᵛ , ρ₃) c₁) e′ (proj₂ (proj₂ (proj₂ CL))) d ∷ [] } )

  module While {t} {ep : Closed Γ t} {ei : Closed (plainᵏ Γ κ) (emitᵗ t)} where

    open Kept {Γ = Γ} κ {t} {ep} {ei}
    open Run {t} {ep} {ei}

    -- the impl's run for a test: the cut cell's scan, its test and the
    -- projection, with no merge
    Wh : ∀ {lo′ ℓ₁ ℓ₂ ℓ₃ s} → FnClo (plainᵏ Γ κ) (CutS unitᵗ s ×ᵗ emitᵗ s) (CutS unitᵗ s) → NodeId → NodeId
       → ∀ {Θ₂ Θ₃} → Env (plainᵏ Γ κ) Θ₂ → Env (plainᵏ Γ κ) Θ₃
       → lo′ ≤ ℓ₁ → ℓ₁ ≤ ℓ₂ → ℓ₂ ≤ ℓ₃ → Path (plainᵏ Γ κ) ℓ₃ (emitᵗ s) (emitᵗ t) → Path (plainᵏ Γ κ) lo′ (emitᵗ s) (emitᵗ t)
    Wh F₁ k₁ k₂ {Θ₂} {Θ₃} ρ₂ ρ₃ h₁ h₂ h₃ q =
      scan-f F₁ k₁ ↠[ h₁ ] (take-f (just (Θ₂ , cutOpenᵛ , ρ₂)) k₂ ↠[ h₂ ] (map-f (Θ₃ , cutOutᵛ , ρ₃) ↠[ h₃ ] q))

    postulate
      -- A TEST'S NODES WRITTEN OPEN ON BOTH SIDES: the plain test to
      -- one, the cell to an open state and its test to one, keep the
      -- stores and the tails related
      -- PROBED: make qc-store QC='50 150 2' QC_BUDGET=500 QC_DRAW='{"exp":[0,0,0,0,0,0,0,0,0,0,0,1,1],"leaf":[1,0,0],"fan":[2,0,0,2,1,2,2,0,0,0],"script":[0,1,0,0,0,0],"reach":["takeWhile","flatten"]}'
      --   decided by `CLI.Store-Check`'s `store?`: 150 agree, 0 fail.
      --   Case 2 passes two values of the hot input through an open test
      --   under a merge.
      while-write : ∀ {sP stP sI stI} (S : St sP stP sI stI) {lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ s k k₁ k₂ Θ₂ Θ₃}
                      {ρ₂ : Env (plainᵏ Γ κ) Θ₂} {ρ₃ : Env (plainᵏ Γ κ) Θ₃}
                      {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                      {P : FnClo Γ s boolᵗ} {F₁ : FnClo (plainᵏ Γ κ) (CutS unitᵗ s ×ᵗ emitᵗ s) (CutS unitᵗ s)}
                      {p : Path Γ ℓ s t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ s) (emitᵗ t)}
                  → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (take-f (just P) k ↠[ h ] p) (Wh F₁ k₁ k₂ ρ₂ ρ₃ h₁ h₂ h₃ q)
                  → Sound (take-f (just P) k ↠[ h ] p) sP stP → Sound (Wh F₁ k₁ k₂ ρ₂ ρ₃ h₁ h₂ h₃ q) sI stI
                  → ∀ b c r → proj₁ (proj₂ c) ≡ false → b ≡ 1 → r ≡ 1
                  → Σ (After S ([] , sP , record stP { nodes = setNode k (take-st b) (EvalSt.nodes stP) })
                               ([] , sI , record stI { nodes = setNode k₂ (take-st r) (setNode k₁ (cell-st {t = CutS unitᵗ s} c) (EvalSt.nodes stI)) })) λ A
                      → PathRel κ (Store.π (After.store A)) (setNode k (take-st b) (EvalSt.nodes stP))
                          (setNode k₂ (take-st r) (setNode k₁ (cell-st {t = CutS unitᵗ s} c) (EvalSt.nodes stI))) p q

      -- A TEST'S NODES WRITTEN SPENT ONCE BOTH SIDES HAVE CUT: the plain
      -- test and the cell's test to zero, the cell to what the scan
      -- left, keep the stores the cut left and the tails related
      -- PROBED: make qc-store QC='50 150 2' QC_BUDGET=500 QC_DRAW='{"exp":[0,0,0,0,0,0,0,0,0,0,0,1,1],"leaf":[1,0,0],"fan":[2,0,0,2,1,2,2,0,0,0],"script":[0,1,0,0,0,0],"reach":["takeWhile","flatten"]}'
      --   decided by `CLI.Store-Check`'s `store?`: 150 agree, 0 fail.
      --   Cases 13 and 22 cut at the hot input's first arrival, under a
      --   merge and a bounded merge of limit one; case 4 cuts at a value
      --   an exhaust's lane carries.
      while-zero : ∀ {sP stP sI stI} (S : St sP stP sI stI) {lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ s k k₁ k₂ Θ₂ Θ₃}
                     {ρ₂ : Env (plainᵏ Γ κ) Θ₂} {ρ₃ : Env (plainᵏ Γ κ) Θ₃}
                     {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                     {P : FnClo Γ s boolᵗ} {F₁ : FnClo (plainᵏ Γ κ) (CutS unitᵗ s ×ᵗ emitᵗ s) (CutS unitᵗ s)}
                     {p : Path Γ ℓ s t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ s) (emitᵗ t)}
                     (e : (k , k₁ ∷ k₂ ∷ []) ∈ Store.π S)
                 → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (take-f (just P) k ↠[ h ] p) (Wh F₁ k₁ k₂ ρ₂ ρ₃ h₁ h₂ h₃ q)
                 → Sound (take-f (just P) k ↠[ h ] p) sP stP → Sound (Wh F₁ k₁ k₂ ρ₂ ρ₃ h₁ h₂ h₃ q) sI stI
                 → ∀ c
                 → Σ (After (cut-go κ S e (there (here refl)))
                        ([] , record sP { live = sweepL (guardOf (proj₁ (cutThrough k (EvalSt.registry stP)))) (Sched.live sP) }
                            , record stP { registry = proj₁ (cutThrough k (EvalSt.registry stP))
                                         ; cancelled = proj₂ (cutThrough k (EvalSt.registry stP)) ++ EvalSt.cancelled stP
                                         ; nodes = setNode k (take-st 0) (EvalSt.nodes stP) })
                        ([] , record sI { live = sweepL (guardOf (proj₁ (cutThrough k₂ (EvalSt.registry stI)))) (Sched.live sI) }
                            , record stI { registry = proj₁ (cutThrough k₂ (EvalSt.registry stI))
                                         ; cancelled = proj₂ (cutThrough k₂ (EvalSt.registry stI)) ++ EvalSt.cancelled stI
                                         ; nodes = setNode k₂ (take-st 0) (setNode k₁ (cell-st {t = CutS unitᵗ s} c) (EvalSt.nodes stI)) })) λ A
                     → PathRel κ (Store.π (After.store A)) (setNode k (take-st 0) (EvalSt.nodes stP))
                         (setNode k₂ (take-st 0) (setNode k₁ (cell-st {t = CutS unitᵗ s} c) (EvalSt.nodes stI))) p q

      -- A SPENT TEST ON BOTH SIDES passes nothing, its end included,
      -- and stays spent
      -- PROBED: make qc-store QC='50 150 2' QC_BUDGET=500 QC_DRAW='{"exp":[0,0,0,0,0,0,0,0,0,0,0,1,1],"leaf":[1,0,0],"fan":[2,0,0,2,1,2,2,0,0,0],"script":[0,1,0,0,0,0],"reach":["takeWhile","flatten"]}'
      --   decided by `CLI.Store-Check`'s `store?`: 150 agree, 0 fail.
      --   Case 22's second arrival comes after its first spent the test,
      --   on both sides.
      while-spent : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ s k k₁ k₂ Θ₂ Θ₃}
                      {ρ₂ : Env (plainᵏ Γ κ) Θ₂} {ρ₃ : Env (plainᵏ Γ κ) Θ₃}
                      {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                      {P : FnClo Γ s boolᵗ} {F₁ : FnClo (plainᵏ Γ κ) (CutS unitᵗ s ×ᵗ emitᵗ s) (CutS unitᵗ s)}
                      {p : Path Γ ℓ s t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ s) (emitᵗ t)}
                      {vs es fin oP vs₁ fin₁ sP₁ stP₁ rI}
                  → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (take-f (just P) k ↠[ h ] p) (Wh F₁ k₁ k₂ ρ₂ ρ₃ h₁ h₂ h₃ q)
                  → lookupNode k (EvalSt.nodes stP) ≡ just (take-st 0)
                  → Carries es vs
                  → Sound (take-f (just P) k ↠[ h ] p) sP stP → Sound (Wh F₁ k₁ k₂ ρ₂ ρ₃ h₁ h₂ h₃ q) sI stI
                  → stepFrame⇓ now (take-f (just P) k) p vs fin sP stP (oP , vs₁ , fin₁ , sP₁ , stP₁)
                  → foldPath⇓ now (Wh F₁ k₁ k₂ ρ₂ ρ₃ h₁ h₂ h₃ q) es fin sI stI rI
                  → Arm S now oP sP₁ stP₁ p vs₁ fin₁
                      (λ π NP NI → PathRel κ π NP NI (take-f (just P) k ↠[ h ] p) (Wh F₁ k₁ k₂ ρ₂ ρ₃ h₁ h₂ h₃ q)) (λ I → Dlv I fin es) rI

      -- A TAIL HANDED A DELIVERED GROUP AND THE END SENDS AT THAT
      -- INSTANT: what a cut hands on is never empty, so whatever the
      -- end subscribes is restamped to the group's own instant
      --
      -- PROBED: make qc-same-clock QC='44 150 3' QC_BUDGET=900 QC_DRAW='{"exp":[2,2,1,0,4,2,3,2,0,0,0,4,3],"obs":[4,2,1,0],"fan":[0,3,2,1,1,0,1,2,2,0],"script":[0,3,0,0,2,0],"reach":["flatten"]}'
      --   decided by `CLI.QuickCheck`'s `sameClockᵇ`, over budget at 24 agree,
      --   0 fail, 37 undecided.  Case 41 cuts an exhaust's first inner at
      --   the second of two hot arrivals.
      -- PROBED: make qc-same-clock QC='46 80 3' QC_DRAW='{"exp":[4,4,1,0,1,5,1,1,0,0,0,5,0],"obs":[0,3,1,0],"fan":[0,3,2,1,1,0,1,2,2,0],"script":[0,4,0,0,0,0],"reach":["flatten","takeWhile"]}'
      --   decided by `CLI.QuickCheck`'s `sameClockᵇ`: 54 agree, 0 fail, 26
      --   undecided.  Case 6 cuts a bounded merge's first inner, limit one,
      --   at the hot input's first arrival, and its end subscribes the
      --   queued inners at that instant.
      cut-out : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now ℓ ℓ′ s I} {p : Path Γ ℓ s t} {q : Path (plainᵏ Γ κ) ℓ′ (emitᵗ s) (emitᵗ t)}
                  {es rI}
              → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) p q → Sound q sI stI
              → foldPath⇓ now q es true sI stI rI → All (DelAt I) es → es ≢ [] → Out I (proj₁ rI)

    -- A TEST THAT CUTS ON BOTH SIDES: the plain test and the cell's
    -- test each sever the registrations through their node and write
    -- zero, and pass the same prefix and the end
    while-cut : ∀ {sP stP sI stI} (S : St sP stP sI stI) {now lo lo′ ℓ ℓ₁ ℓ₂ ℓ₃ s k k₁ k₂ Θ₂ Θ₃}
                  {ρ₂ : Env (plainᵏ Γ κ) Θ₂} {ρ₃ : Env (plainᵏ Γ κ) Θ₃}
                  {h : lo ≤ ℓ} {h₁ : lo′ ≤ ℓ₁} {h₂ : ℓ₁ ≤ ℓ₂} {h₃ : ℓ₂ ≤ ℓ₃}
                  {P : FnClo Γ s boolᵗ} {F₁ : FnClo (plainᵏ Γ κ) (CutS unitᵗ s ×ᵗ emitᵗ s) (CutS unitᵗ s)}
                  {p : Path Γ ℓ s t} {q : Path (plainᵏ Γ κ) ℓ₃ (emitᵗ s) (emitᵗ t)}
                  {vs es fin oP vs₁ fin₁ sP₁ stP₁ rI}
              → PathRel κ (Store.π S) (EvalSt.nodes stP) (EvalSt.nodes stI) (take-f (just P) k ↠[ h ] p) (Wh F₁ k₁ k₂ ρ₂ ρ₃ h₁ h₂ h₃ q)
              → proj₂ (proj₂ (takeVals (just P) 1 vs)) ≡ true
              → Carries es vs
              → Sound (take-f (just P) k ↠[ h ] p) sP stP → Sound (Wh F₁ k₁ k₂ ρ₂ ρ₃ h₁ h₂ h₃ q) sI stI
              → stepFrame⇓ now (take-f (just P) k) p vs fin sP stP (oP , vs₁ , fin₁ , sP₁ , stP₁)
              → foldPath⇓ now (Wh F₁ k₁ k₂ ρ₂ ρ₃ h₁ h₂ h₃ q) es fin sI stI rI
              → Arm S now oP sP₁ stP₁ p vs₁ fin₁
                  (λ π NP NI → PathRel κ π NP NI (take-f (just P) k ↠[ h ] p) (Wh F₁ k₁ k₂ ρ₂ ρ₃ h₁ h₂ h₃ q)) (λ I → Dlv I fin es) rI
    while-cut S R@(spentWhile~ _ lk _ _) _ bs sp si d dI = while-spent S R lk bs sp si d dI
    while-cut {stP = stP} {sI = sI} {stI = stI} S {es = es}
              R@(takeWhile~ {s = s} {k = k} {k₁ = k₁} {k₂ = k₂} {os = os} {em = em} {Θ₂ = Θ₂} {ρ₂ = ρ₂} {Θ₃ = Θ₃} {ρ₃ = ρ₃}
                            {h = h} {h₁ = h₁} {h₂ = h₂} {h₃ = h₃} {P = P} {F₁ = F₁} {p = p} {q = q} e lk lk₁ lk₂ CL r)
              eqW bs sp si d dI@(fold-step d₁ (fold-step d₂ (fold-step step-map dq)))
      with cut-group {Bud = λ _ b → b ≡ 1} {F′ = F₁} {P = just P} {Θ₂ = Θ₂} {ρ₂ = ρ₂} {Θ₃ = Θ₃} {ρ₃ = ρ₃} CL bs (tt , false , os , em) 1 refl refl
         | scan-at lk₁ d₁ | take-cut-at lk eqW d
    ... | cs , fe , _ , dl | refl | refl
      with take-cut-at (trans (set-above k₁ k₂ (cell-st {t = CutS unitᵗ s} (proj₂ (scanVals F₁ (tt , false , os , em) es))) (EvalSt.nodes stI)
                                        (apart k₁ k₂ (cell-take {N = EvalSt.nodes stI} {k = k₁} {k′ = k₂} lk₁ lk₂))) lk₂)
                       (trans fe eqW) d₂
    ... | refl =
      arm A (proj₂ ZW) cs soq dq (λ {rP} dP B rel′ →
        spentWhile~ (After.grows B (After.grows A e)) (trans (fold-unmoved dP cP) lkP) (trans (fold-unmoved dq c₂) lk₂′) rel′)
        λ { (_ , ds) → out-quiet [] refl
                     , inj₁ (cut-out (After.store A) (proj₂ ZW) soq dq (dl ds)
                              (map-cons (applyClo (Θ₃ , cutOutᵛ , ρ₃)) _ (cut-cons (just (Θ₂ , cutOpenᵛ , ρ₂)) 1 (proj₁ (scanVals F₁ (tt , false , os , em) es)) (trans fe eqW)))) }
      where
      fc : Val (plainᵏ Γ κ) (CutS unitᵗ s)
      fc = proj₂ (scanVals F₁ (tt , false , os , em) es)
      N₂ = setNode k₂ (take-st 0) (setNode k₁ (cell-st {t = CutS unitᵗ s} fc) (EvalSt.nodes stI))
      -- the cut on both sides, then its nodes written
      ZW = while-zero S e R sp si fc
      A = after (cut-go κ S e (there (here refl))) (cut-keeps κ S e (there (here refl))) (cut-persists κ S e (there (here refl))) []ᵖ (λ x → x)
          ⨾∅ proj₁ ZW
      lkP : lookupNode k (setNode k (take-st 0) (EvalSt.nodes stP)) ≡ just (take-st 0)
      lkP = lookup-set k (take-st 0) (EvalSt.nodes stP)
      lk₂′ : lookupNode k₂ N₂ ≡ just (take-st 0)
      lk₂′ = lookup-set k₂ (take-st 0) (setNode k₁ (cell-st {t = CutS unitᵗ s} fc) (EvalSt.nodes stI))
      spK = step-kept h d sp
      cP : Clear k p _ _
      cP = head-on (take-f (just P) k) h p k (self-node k []) spK , drop-ot (take-f (just P) k) h p spK
      so₁ = step-kept h₁ d₁ si
      so₂ = step-kept h₂ d₂ (drop-ot _ _ _ so₁)
      soq = drop-ot _ _ _ (drop-ot _ _ _ so₂)
      c₂ : Clear k₂ q _ _
      c₂ = on-drop (head-on _ h₂ _ k₂ (self-node k₂ []) so₂) , soq

    -- A TEST STEPS ALIKE ON BOTH SIDES.  A group that does not cut,
    -- whether or not it ends, leaves the cell open and both tests at
    -- one, and the three impl frames write nothing the tails' folds read
    takeWhile-arm : ∀ {lo lo′ ℓ s} {P k} {h : lo ≤ ℓ} {p : Path Γ ℓ s t} {Q : Path (plainᵏ Γ κ) lo′ _ _}
                  → Steps (take-f (just P) k) h p Q
    takeWhile-arm S R@(spentWhile~ _ lk _ _) bs sp si d dI = while-spent S R lk bs sp si d dI
    takeWhile-arm {vs = vs} {es = es} {fin = fin} {sP = sP} {stP = stP} {sI = sI} {stI = stI} S
                  R@(takeWhile~ {s = s} {k = k} {k₁ = k₁} {k₂ = k₂} {os = os} {em = em} {Θ₂ = Θ₂} {ρ₂ = ρ₂} {Θ₃ = Θ₃} {ρ₃ = ρ₃}
                                {h = h} {h₁ = h₁} {h₂ = h₂} {h₃ = h₃} {P = P} {F₁ = F₁} {p = p} {q = q} e lk lk₁ lk₂ CL r)
                  bs sp si d dI@(fold-step d₁ (fold-step d₂ (fold-step step-map dq)))
      with proj₂ (proj₂ (takeVals (just P) 1 vs)) in eqW
    ... | true = while-cut S R eqW bs sp si d dI
    ... | false
      with cut-group {Bud = λ _ b → b ≡ 1} {F′ = F₁} {P = just P} {Θ₂ = Θ₂} {ρ₂ = ρ₂} {Θ₃ = Θ₃} {ρ₃ = ρ₃} CL bs (tt , false , os , em) 1 refl refl
         | scan-at lk₁ d₁ | take-open-at lk eqW d
    ... | cs , fe , rest , dl | refl | refl
      with rest eqW
         | take-open-at (trans (set-above k₁ k₂ (cell-st {t = CutS unitᵗ s} (proj₂ (scanVals F₁ (tt , false , os , em) es))) (EvalSt.nodes stI)
                                          (apart k₁ k₂ (cell-take {N = EvalSt.nodes stI} {k = k₁} {k′ = k₂} lk₁ lk₂))) lk₂)
                        (trans fe eqW) d₂
    ... | r1 , fl , bud | refl =
      arm (proj₁ TW) (proj₂ TW) cs soq dq (λ {rP} dP B rel′ →
        takeWhile~ (After.grows B (After.grows (proj₁ TW) e))
          (trans (fold-unmoved dP cP) lkP) (trans (fold-unmoved dq c₁) lk₁′) (trans (fold-unmoved dq c₂) lk₂′) CL rel′)
        λ { (f , ds) → out-quiet [] refl , inj₂ (cong (λ x → x ∧ true) f , dl ds) }
      where
      remP = proj₁ (proj₂ (takeVals (just P) 1 vs))
      fc : Val (plainᵏ Γ κ) (CutS unitᵗ s)
      fc = proj₂ (scanVals F₁ (tt , false , os , em) es)
      r₂ = proj₁ (proj₂ (takeVals {s = CutS unitᵗ s} (just (Θ₂ , cutOpenᵛ , ρ₂)) 1 (proj₁ (scanVals F₁ (tt , false , os , em) es))))
      N₁ = setNode k₁ (cell-st {t = CutS unitᵗ s} fc) (EvalSt.nodes stI)
      N₂ = setNode k₂ (take-st r₂) N₁
      TW = while-write S R sp si remP fc r₂ fl bud r1
      lkP : lookupNode k (setNode k (take-st remP) (EvalSt.nodes stP)) ≡ just (take-st 1)
      lkP = subst (λ x → lookupNode k (setNode k (take-st remP) (EvalSt.nodes stP)) ≡ just (take-st x)) bud
                  (lookup-set k (take-st remP) (EvalSt.nodes stP))
      lk₁′ : lookupNode k₁ N₂ ≡ just (cell-st {t = CutS unitᵗ s} (tt , false , proj₂ (proj₂ fc)))
      lk₁′ = trans (set-above k₂ k₁ (take-st r₂) N₁ (apart k₂ k₁ (λ x → cell-take {N = EvalSt.nodes stI} {k = k₁} {k′ = k₂} lk₁ lk₂ (sym x))))
                   (subst (λ f → lookupNode k₁ N₁ ≡ just (cell-st {t = CutS unitᵗ s} (tt , f , proj₂ (proj₂ fc))))
                          fl (lookup-set k₁ (cell-st {t = CutS unitᵗ s} fc) (EvalSt.nodes stI)))
      lk₂′ : lookupNode k₂ N₂ ≡ just (take-st 1)
      lk₂′ = subst (λ x → lookupNode k₂ N₂ ≡ just (take-st x)) r1 (lookup-set k₂ (take-st r₂) N₁)
      -- the plain test off its tail, once stepped
      spK = step-kept h d sp
      cP : Clear k p sP _
      cP = head-on (take-f (just P) k) h p k (self-node k []) spK , drop-ot (take-f (just P) k) h p spK
      -- the impl's nodes off its tail, once stepped
      so₁ = step-kept h₁ d₁ si
      so₂ = step-kept h₂ d₂ (drop-ot _ _ _ so₁)
      soq = drop-ot _ _ _ (drop-ot _ _ _ so₂)
      c₁ : Clear k₁ q sI _
      c₁ = on-drop (on-drop (proj₁ (step-clear d₂ (head-on (scan-f F₁ k₁) h₁ _ k₁ (self-node k₁ []) so₁ , drop-ot _ _ _ so₁)))) , soq
      c₂ : Clear k₂ q sI _
      c₂ = on-drop (head-on _ h₂ _ k₂ (self-node k₂ []) so₂) , soq
