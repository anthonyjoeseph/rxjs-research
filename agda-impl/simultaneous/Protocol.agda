{-# OPTIONS --guardedness #-}

-- THE RUN'S PROTOCOL, READ OFF ITS POSITIONS: what the batcher needs of
-- the elaborated run, one emit at a time, from where the emits sit.
-- An instant is an interval of positions (`between`), each emit is named
-- for its instant, the subscribe mark sits once, at the end of the
-- subscribe frame, an instant's values come before its overs and every
-- value before the completion.  The run meets the visible rows in
-- position order, so each of these is a fact of the run.
module simultaneous.Protocol where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_])
import Data.List as L
open import Data.List.Properties using (foldl-++; ∷-injectiveʳ; ∷-injectiveˡ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ʳ; ∈-++⁺ˡ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂; sym; trans; subst)

open import denotation.Events using (Pos; Timeline; Label; ix; sub; last; root; fresh; _≟ᵖ_; <ᵖ-between; <ᵖ-below)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; _≺_; enter; ⟦_⟧)
open import denotation.Laws using (inv-⟦⟧)
open import denotation.Laws.Worlds using (W; InvAt; TimerRoot; Plain; plain-ix; plain-last; step; timer; join; here; inW)
open import denotation.Read using (Run; _∷_)
open import denotation.Laws.Modulus using (≺-trans; ≺-irrefl; ≺-absurd)
open import simultaneous.InstEmit using (InstEmit; instEmit; value; mark)
import simultaneous.InstEmit as Marks
open import simultaneous.SObs using (SObs; module Elaborate)
open import simultaneous.Readings using (Rooted; NotSub; in-frame; in-cascade; ix-ns; last-ns; instantOf; stamped)
open import simultaneous.Relations using (Met; values; elaborated)
open import simultaneous.Layers using (at-func; run-tail; run-after; run-row; run-has; to≺; from≺)

open Elaborate {C = Timeline} _≟ᵖ_ root fresh using (IE; elaborate)

------------------------------------------------------------------------
-- The run as the batcher reads it

nameStep : ∀ {A : Set} → Pos → IE A → Pos
nameStep a (instEmit (mark Marks.begin) n) = n
nameStep a (instEmit _ _)                  = a

-- The name of the last begin, `a` if none.
lastBegin : ∀ {A : Set} → Pos → List (IE A) → Pos
lastBegin a xs = L.foldl nameStep a xs

subStep : ∀ {A : Set} → Bool → IE A → Bool
subStep b (instEmit (mark Marks.subscribed) _) = true
subStep b (instEmit _ _)                       = b

-- The subscribe burst is over.
seenSub : ∀ {A : Set} → List (IE A) → Bool
seenSub xs = L.foldl subStep false xs

-- The next value, if any, is of another instant.
Fresh : ∀ {A : Set} → Pos → List (Pos × A) → Set
Fresh i []            = ⊤
Fresh i ((j , _) ∷ _) = i ≢ j

lb-snoc : ∀ {A : Set} (xs : List (IE A)) w → lastBegin root (xs ++ [ w ]) ≡ nameStep (lastBegin root xs) w
lb-snoc xs w = foldl-++ nameStep root xs [ w ]

ss-snoc : ∀ {A : Set} (xs : List (IE A)) w → seenSub (xs ++ [ w ]) ≡ subStep (seenSub xs) w
ss-snoc xs w = foldl-++ subStep false xs [ w ]

------------------------------------------------------------------------
-- Emits, one kind at a time

-- An emit is a subscribe mark, or leaves the burst flag alone.
sub-view : ∀ {A : Set} (x : IE A) → (Σ Pos λ m → x ≡ instEmit (mark Marks.subscribed) m) ⊎ (∀ b → subStep b x ≡ b)
sub-view (instEmit (value _) _)             = inj₂ λ _ → refl
sub-view (instEmit (mark Marks.subscribed) m) = inj₁ (m , refl)
sub-view (instEmit (mark Marks.begin) _)      = inj₂ λ _ → refl
sub-view (instEmit (mark Marks.over) _)       = inj₂ λ _ → refl
sub-view (instEmit (mark Marks.stop) _)       = inj₂ λ _ → refl
sub-view (instEmit (mark Marks.outerOpen) _)  = inj₂ λ _ → refl
sub-view (instEmit (mark Marks.outerClose) _) = inj₂ λ _ → refl
sub-view (instEmit (mark Marks.laneStart) _)  = inj₂ λ _ → refl
sub-view (instEmit (mark Marks.laneDone) _)   = inj₂ λ _ → refl
sub-view (instEmit (mark Marks.burstEnd) _)   = inj₂ λ _ → refl
sub-view (instEmit (mark Marks.outerDone) _)  = inj₂ λ _ → refl
sub-view (instEmit (mark Marks.carry) _)      = inj₂ λ _ → refl
sub-view (instEmit (mark Marks.completed) _)  = inj₂ λ _ → refl

-- An emit is a begin, or leaves the name alone.
begin-view : ∀ {A : Set} (x : IE A) → (Σ Pos λ n → x ≡ instEmit (mark Marks.begin) n) ⊎ (∀ a → nameStep a x ≡ a)
begin-view (instEmit (value _) _)             = inj₂ λ _ → refl
begin-view (instEmit (mark Marks.begin) n)      = inj₁ (n , refl)
begin-view (instEmit (mark Marks.subscribed) _) = inj₂ λ _ → refl
begin-view (instEmit (mark Marks.over) _)       = inj₂ λ _ → refl
begin-view (instEmit (mark Marks.stop) _)       = inj₂ λ _ → refl
begin-view (instEmit (mark Marks.outerOpen) _)  = inj₂ λ _ → refl
begin-view (instEmit (mark Marks.outerClose) _) = inj₂ λ _ → refl
begin-view (instEmit (mark Marks.laneStart) _)  = inj₂ λ _ → refl
begin-view (instEmit (mark Marks.laneDone) _)   = inj₂ λ _ → refl
begin-view (instEmit (mark Marks.burstEnd) _)   = inj₂ λ _ → refl
begin-view (instEmit (mark Marks.outerDone) _)  = inj₂ λ _ → refl
begin-view (instEmit (mark Marks.carry) _)      = inj₂ λ _ → refl
begin-view (instEmit (mark Marks.completed) _)  = inj₂ λ _ → refl

stays-seen : ∀ {A : Set} (xs : List (IE A)) → L.foldl subStep true xs ≡ true
stays-seen []       = refl
stays-seen (x ∷ xs) with sub-view x
... | inj₁ (_ , refl) = stays-seen xs
... | inj₂ k          = trans (cong (λ b → L.foldl subStep b xs) (k true)) (stays-seen xs)

-- A subscribe mark met, the burst is over.
sub-seen : ∀ {A : Set} b {m} (xs : List (IE A)) → instEmit (mark Marks.subscribed) m ∈ xs → L.foldl subStep b xs ≡ true
sub-seen b (_ ∷ xs) (here refl) = stays-seen xs
sub-seen b (x ∷ xs) (there h)   = sub-seen (subStep b x) xs h

-- The burst is over only past a subscribe mark.
seen-sub : ∀ {A : Set} b (xs : List (IE A)) → L.foldl subStep b xs ≡ true → b ≡ true ⊎ Σ Pos λ m → instEmit (mark Marks.subscribed) m ∈ xs
seen-sub b []       e = inj₁ e
seen-sub b (x ∷ xs) e with seen-sub (subStep b x) xs e
... | inj₂ (m , h) = inj₂ (m , there h)
... | inj₁ e′ with sub-view x
...   | inj₁ (m , refl) = inj₂ (m , here refl)
...   | inj₂ k          = inj₁ (trans (sym (k b)) e′)

-- The last begin's name, or the start.
lb-view : ∀ {A : Set} a (xs : List (IE A)) → L.foldl nameStep a xs ≡ a ⊎ instEmit (mark Marks.begin) (L.foldl nameStep a xs) ∈ xs
lb-view a []       = inj₁ refl
lb-view a (x ∷ xs) with lb-view (nameStep a x) xs
... | inj₂ h = inj₂ (there h)
... | inj₁ e with begin-view x
...   | inj₁ (n , refl) = inj₂ (subst (λ m → instEmit (mark Marks.begin) m ∈ (instEmit (mark Marks.begin) n ∷ xs)) (sym e) (here refl))
...   | inj₂ k          = inj₁ (trans e (k a))

-- No value of instant `i` next.
fresh-all : ∀ {A : Set} i (ys : List (IE A)) → (∀ {a j} → instEmit (value a) j ∈ ys → i ≢ j) → Fresh i (stamped ys)
fresh-all i []                          h = tt
fresh-all i (instEmit (value a) j ∷ ys) h = h (here refl)
fresh-all i (instEmit (mark _) _ ∷ ys)  h = fresh-all i ys (λ m → h (there m))

-- No value at all.
none-stamped : ∀ {A : Set} (ys : List (IE A)) → (∀ {a j} → instEmit (value a) j ∈ ys → ⊥) → stamped ys ≡ []
none-stamped []                          h = refl
none-stamped (instEmit (value a) j ∷ ys) h = ⊥-elim (h (here refl))
none-stamped (instEmit (mark _) _ ∷ ys)  h = none-stamped ys (λ m → h (there m))

------------------------------------------------------------------------
-- An instant is an interval of positions

private
  cascade-form : ∀ {t e l} c → instantOf c ≡ (ix t ∷ sub e ∷ l ∷ []) → Σ Pos λ ys → c ≡ (ix t ∷ sub e ∷ l ∷ []) ++ ys
  cascade-form (ix _ ∷ sub _ ∷ _ ∷ ys) refl = ys , refl
  cascade-form []                    ()
  cascade-form (ix _ ∷ [])           ()
  cascade-form (ix _ ∷ ix _ ∷ _)     ()
  cascade-form (ix _ ∷ last ∷ _)     ()
  cascade-form (ix _ ∷ sub _ ∷ [])   ()
  cascade-form (sub _ ∷ _)           ()
  cascade-form (last ∷ _)            ()

  frame-form : ∀ {c} → Rooted c → instantOf c ≡ root → Σ Label λ l → Σ Pos λ ys → c ≡ (ix 0 ∷ []) ++ l ∷ ys
  frame-form (in-frame {l} {p} _) _ = l , p , refl
  frame-form in-cascade           ()

  frame-root : ∀ {zs} → Rooted (ix 0 ∷ zs) → instantOf (ix 0 ∷ zs) ≡ root
  frame-root (in-frame ix-ns)   = refl
  frame-root (in-frame last-ns) = refl

  cascade-prefix : ∀ t e l p → (ix t ∷ sub e ∷ l ∷ []) ≺ (ix t ∷ sub e ∷ l ∷ p) ⊎ _≡_ {A = Pos} (ix t ∷ sub e ∷ l ∷ []) (ix t ∷ sub e ∷ l ∷ p)
  cascade-prefix t e l []      = inj₂ refl
  cascade-prefix t e l (x ∷ q) = inj₁ (to≺ (ix t ∷ sub e ∷ l ∷ []) (ix t ∷ sub e ∷ l ∷ x ∷ q) (<ᵖ-below (ix t ∷ sub e ∷ l ∷ []) {x} q))

  -- What lies between two positions under `p` lies under `p`.
  under : ∀ p {a b c ys zs} → a ≡ p ++ ys → p ≺ a ⊎ p ≡ a → a ≺ b → b ≺ c → c ≡ p ++ zs → Σ Pos λ ws → b ≡ p ++ ws
  under p {a} {b} {c} {zs = zs} _ pa ab bc refl =
    <ᵖ-between p b zs (from≺ p b (pb pa)) (from≺ b (p ++ zs) bc)
    where
      pb : p ≺ a ⊎ p ≡ a → p ≺ b
      pb (inj₁ lt)   = ≺-trans {p} {a} {b} lt ab
      pb (inj₂ refl) = ab

-- An instant is an interval: a position between two of one instant is of it.
between : ∀ {a b c} → Rooted a → Rooted b → Rooted c → a ≺ b → b ≺ c → instantOf a ≡ instantOf c → instantOf b ≡ instantOf a
between {a} {b} {c} ra@(in-frame {l} {p} _) rb rc ab bc e with frame-form rc (trans (sym e) (frame-root ra))
... | l′ , p′ , ec with under (ix 0 ∷ []) {a} {b} {c} {l ∷ p} refl (inj₁ (to≺ (ix 0 ∷ []) a (<ᵖ-below (ix 0 ∷ []) {l} p))) ab bc ec
...   | ws , refl = trans (frame-root rb) (sym (frame-root ra))
between {a} {b} {c} (in-cascade {t} {e₀} {l} {p}) rb rc ab bc e with cascade-form c (sym e)
... | zs , ec with under (ix (suc t) ∷ sub e₀ ∷ l ∷ []) {_} {b} {c} {p} refl (cascade-prefix (suc t) e₀ l p) ab bc ec
...   | ws , refl = refl

------------------------------------------------------------------------
-- A run, split at an emit

-- An async position: past the subscribe frame.
Async : Pos → Set
Async k = instantOf k ≢ root

module Split {A : Set} where

  -- A value met, at its row.
  val-in : ∀ {x} (rs : List (Pos × Ev A)) → x ∈ values rs → Σ Pos λ k → (k , out x) ∈ rs
  val-in ((k , out a) ∷ rs) (here refl) = k , here refl
  val-in ((k , out a) ∷ rs) (there h)   with val-in rs h
  ... | q , m = q , there m
  val-in ((k , skip) ∷ rs)  h with val-in rs h
  ... | q , m = q , there m
  val-in ((k , end) ∷ rs)   h with val-in rs h
  ... | q , m = q , there m
  val-in ((k , pin _) ∷ rs) h with val-in rs h
  ... | q , m = q , there m

  -- A row met, as a value.
  in-val : ∀ {k x} (rs : List (Pos × Ev A)) → (k , out x) ∈ rs → x ∈ values rs
  in-val ((k , out a) ∷ rs) (here refl) = here refl
  in-val ((k , out a) ∷ rs) (there h)   = there (in-val rs h)
  in-val ((k , skip) ∷ rs)  (there h)   = in-val rs h
  in-val ((k , end) ∷ rs)   (there h)   = in-val rs h
  in-val ((k , pin _) ∷ rs) (there h)   = in-val rs h

  nonempty : ∀ {X : Set} (xs : List X) {w : X} {ys} → [] ≡ xs ++ w ∷ ys → ⊥
  nonempty []      ()
  nonempty (_ ∷ _) ()

  -- The run around one of its values.
  split : ∀ (rs : List (Pos × Ev A)) xs w ys → values rs ≡ xs ++ w ∷ ys
        → Σ _ λ r₁ → Σ _ λ r₂ → Σ Pos λ k → rs ≡ r₁ ++ (k , out w) ∷ r₂ × values r₁ ≡ xs × values r₂ ≡ ys
  split [] xs w ys e = ⊥-elim (nonempty xs e)
  split ((k , out a) ∷ rs) [] w ys refl = [] , rs , k , refl , refl , refl
  split ((k , out a) ∷ rs) (x ∷ xs) w ys e with split rs xs w ys (∷-injectiveʳ e)
  ... | r₁ , r₂ , q , refl , e₁ , e₂ = (k , out a) ∷ r₁ , r₂ , q , refl , cong₂ _∷_ (∷-injectiveˡ e) e₁ , e₂
  split ((k , skip) ∷ rs) xs w ys e with split rs xs w ys e
  ... | r₁ , r₂ , q , refl , e₁ , e₂ = (k , skip) ∷ r₁ , r₂ , q , refl , e₁ , e₂
  split ((k , end) ∷ rs) xs w ys e with split rs xs w ys e
  ... | r₁ , r₂ , q , refl , e₁ , e₂ = (k , end) ∷ r₁ , r₂ , q , refl , e₁ , e₂
  split ((k , pin p) ∷ rs) xs w ys e with split rs xs w ys e
  ... | r₁ , r₂ , q , refl , e₁ , e₂ = (k , pin p) ∷ r₁ , r₂ , q , refl , e₁ , e₂

  module _ {t : Pos → Ev A → Set} where

    -- What a run meets before a row lies before it.
    run-before : ∀ {c} r₁ {k e r₂ q e′} → Run t c (r₁ ++ (k , e) ∷ r₂) → (q , e′) ∈ r₁ → q ≺ k
    run-before ((q , _) ∷ r₁) {k} (_ ∷ run) (here refl) = run-after run (∈-++⁺ʳ r₁ (here refl))
    run-before (_ ∷ r₁)           (_ ∷ run) (there h)   = run-before r₁ run h

    -- What a run meets after a row lies after it.
    run-past : ∀ {c} r₁ {k e r₂ q e′} → Run t c (r₁ ++ (k , e) ∷ r₂) → (q , e′) ∈ r₂ → k ≺ q
    run-past r₁ run h with run-tail r₁ run
    ... | _ ∷ rest = run-after rest h

    -- A row met before `k` was met before it.
    locate : ∀ {c} r₁ {k e r₂ q e′} → Run t c (r₁ ++ (k , e) ∷ r₂) → (q , e′) ∈ (r₁ ++ (k , e) ∷ r₂) → q ≺ k → (q , e′) ∈ r₁
    locate r₁ {k} {q = q} run h qk with ∈-++⁻ r₁ h
    ... | inj₁ h₁         = h₁
    ... | inj₂ (here refl) = ⊥-elim (≺-irrefl {k} qk)
    ... | inj₂ (there h₂)  = ⊥-elim (≺-absurd {q} {k} qk (run-past r₁ run h₂))

------------------------------------------------------------------------
-- The positions of an elaborated program's emits

-- Every row of a program run from the root lies under the subscribe
-- frame or one step of a timer cascade: in the root's world, a timer
-- fires past tick 0, and no row sits at a timer's root.
private
  Cascade : Pos → Set
  Cascade x = Σ ℕ λ t → Σ Pos λ e → x ≡ ix (suc t) ∷ sub e ∷ []

  rooted-ext : ∀ {x} l ys → Rooted x ⊎ Cascade x → Rooted (x ++ l ∷ ys)
  rooted-ext l ys (inj₁ (in-frame ns))  = in-frame ns
  rooted-ext l ys (inj₁ in-cascade)     = in-cascade
  rooted-ext l ys (inj₂ (_ , _ , refl)) = in-cascade

  plain-ns : ∀ {l} → Plain l → NotSub l
  plain-ns plain-ix   = ix-ns
  plain-ns plain-last = last-ns

  world-rooted : ∀ {x} → W (λ _ → ⊥) root x → Rooted x ⊎ Cascade x
  world-rooted (step here pl)                = inj₁ (in-frame (plain-ns pl))
  world-rooted (step {l = l} (inW w) _)      = inj₁ (rooted-ext l [] (world-rooted w))
  world-rooted (timer zero _ ())
  world-rooted (timer (suc t) _ _)           = inj₂ (t , _ , refl)
  world-rooted (join (inj₁ ()) _ _)
  world-rooted (join {e = e} (inj₂ u) _ _)   = inj₁ (rooted-ext (sub e) [] (world-rooted u))

row-rooted : ∀ {A} (o : SObs [] A) {k e} → enter (⟦ o ⟧ []ᴬ) root k e → Rooted k
row-rooted o x = go (InvAt.world I x) (InvAt.untimed I x)
  where
    I = inv-⟦⟧ o []ᴬ (λ ()) root (tt , λ ())

    go : ∀ {k} → W (λ _ → ⊥) root k → (TimerRoot k → ⊥) → Rooted k
    go w nt with world-rooted w
    ... | inj₁ r              = r
    ... | inj₂ (_ , _ , refl) = ⊥-elim (nt tt)

rooted : ∀ {A} (o : SObs [] A) {k e} → elaborated o k e → Rooted k
rooted o = row-rooted (elaborate o)

-- THE INSTANT STRUCTURE: every emit is named for its instant, and the
-- begins of one instant name it alike; the subscribe mark sits once, before every
-- begin, every value past it async; an instant's values precede its overs,
-- and every value precedes the completion.
postulate
  named     : ∀ {A} (o : SObs [] A) {k x} → elaborated o k (out x) → instantOf (InstEmit.instant x) ≡ instantOf k
  one-name  : ∀ {A} (o : SObs [] A) {k k′ n n′} → elaborated o k (out (instEmit (mark Marks.begin) n))
            → elaborated o k′ (out (instEmit (mark Marks.begin) n′)) → instantOf k ≡ instantOf k′ → n ≡ n′
  sub-first : ∀ {A} (o : SObs [] A) {k n} → elaborated o k (out (instEmit (mark Marks.begin) n))
            → Σ Pos λ ks → Σ Pos λ m → elaborated o ks (out (instEmit (mark Marks.subscribed) m)) × ks ≺ k
  sub-one   : ∀ {A} (o : SObs [] A) {k k′ m m′} → elaborated o k (out (instEmit (mark Marks.subscribed) m))
            → elaborated o k′ (out (instEmit (mark Marks.subscribed) m′)) → k ≡ k′
  sub-async : ∀ {A} (o : SObs [] A) {ks m k a j} → elaborated o ks (out (instEmit (mark Marks.subscribed) m))
            → elaborated o k (out (instEmit (value a) j)) → ks ≺ k → Async k
  over-last : ∀ {A} (o : SObs [] A) {kv a n ko m} → elaborated o kv (out (instEmit (value a) n))
            → elaborated o ko (out (instEmit (mark Marks.over) m)) → instantOf kv ≡ instantOf ko → kv ≺ ko
  done-last : ∀ {A} (o : SObs [] A) {kv a n kc m} → elaborated o kv (out (instEmit (value a) n))
            → elaborated o kc (out (instEmit (mark Marks.completed) m)) → kv ≺ kc

------------------------------------------------------------------------
-- The protocol, one mark at a time

module Leaves {A : Set} (o : SObs [] A) {rx} (mx : Met (elaborated o) rx) where
  open Split {IE A}

  X = elaborated o
  fu = at-func (elaborate o)

  -- The run around the emit `w`, past `xs`, before `ys`.
  record Around (xs : List (IE A)) (w : IE A) (ys : List (IE A)) : Set where
    field
      r₁ r₂ : List (Pos × Ev (IE A))
      k     : Pos
      run   : Run X nothing (r₁ ++ (k , out w) ∷ r₂)
      vs₁   : values r₁ ≡ xs
      vs₂   : values r₂ ≡ ys

    row : X k (out w)
    row = proj₁ (run-row run (∈-++⁺ʳ r₁ (here refl)))

    -- A value next lies past `k`, at a row of its own.
    next : ∀ {a j} → instEmit (value a) j ∈ ys → Σ Pos λ q → X q (out (instEmit (value a) j)) × k ≺ q
    next h with val-in r₂ (subst (λ zs → _ ∈ zs) (sym vs₂) h)
    ... | q , m = q , proj₁ (run-row run (∈-++⁺ʳ r₁ (there m))) , run-past r₁ run m

    -- An emit past `xs`, at a row before `k`.
    prev : ∀ {x} → x ∈ xs → Σ Pos λ q → X q (out x) × q ≺ k
    prev h with val-in r₁ (subst (λ zs → _ ∈ zs) (sym vs₁) h)
    ... | q , m = q , proj₁ (run-row run (∈-++⁺ˡ m)) , run-before r₁ run m

    -- A visible row before `k` was met past `xs`.
    met : ∀ {q x} → X q (out x) → q ≺ k → x ∈ xs
    met {q} {x} y qk = subst (λ zs → x ∈ zs) vs₁
      (in-val r₁ (locate r₁ run (run-has fu run y tt tt (λ kq → ≺-absurd {q} {k} qk kq) (∈-++⁺ʳ r₁ (here refl))) qk))

  around : ∀ xs w ys → values rx ≡ xs ++ w ∷ ys → Around xs w ys
  around xs w ys e with split rx xs w ys e
  ... | r₁ , r₂ , k , eq , e₁ , e₂ = record { r₁ = r₁ ; r₂ = r₂ ; k = k ; run = subst (Run X nothing) eq mx ; vs₁ = e₁ ; vs₂ = e₂ }

  -- An async value is named for no frame.
  async-name : ∀ {q a j} → X q (out (instEmit (value a) j)) → Async q → j ≢ root
  async-name y as refl = as (sym (named o y))

  -- Past the subscribe mark, a value is named for no frame.
  past-sub : ∀ xs {w ys} → (h : Around xs w ys) → seenSub xs ≡ true → ∀ {a j} → instEmit (value a) j ∈ ys → j ≢ root
  past-sub xs h s v with seen-sub false xs s
  ... | inj₁ ()
  ... | inj₂ (m , hm) with Around.prev h hm | Around.next h v
  ...   | ks , yk , ksk | q , y , kq = async-name y (sub-async o yk y (≺-trans {ks} {Around.k h} {q} ksk kq))

  -- Begins only past the subscribe burst.
  begin-late : ∀ xs n ys → values rx ≡ xs ++ instEmit (mark Marks.begin) n ∷ ys → seenSub xs ≡ true
  begin-late xs n ys e with around xs _ ys e
  ... | h with sub-first o (Around.row h)
  ...   | ks , m , y , kk = sub-seen false xs (Around.met h y kk)

  -- The subscribe burst ends once.
  sub-once : ∀ xs n ys → values rx ≡ xs ++ instEmit (mark Marks.subscribed) n ∷ ys → seenSub xs ≡ false
  sub-once xs n ys e with around xs _ ys e
  ... | h with seenSub xs in s
  ...   | false = refl
  ...   | true with seen-sub false xs s
  ...     | inj₁ ()
  ...     | inj₂ (m , hm) with Around.prev h hm
  ...       | q , y , qk with sub-one o y (Around.row h)
  ...         | refl = ⊥-elim (≺-irrefl {q} qk)

  -- Past the subscribe mark, the next value is of no frame.
  sub-fresh : ∀ xs n ys → values rx ≡ xs ++ instEmit (mark Marks.subscribed) n ∷ ys → Fresh root (stamped ys)
  sub-fresh xs n ys e with around xs _ ys e
  ... | h = fresh-all root ys λ v eq → case v eq
    where
      case : ∀ {a j} → instEmit (value a) j ∈ ys → root ≡ j → ⊥
      case v refl with Around.next h v
      ... | q , y , kq = async-name y (sub-async o (Around.row h) y kq) refl

  -- A value past `k` is of an instant other than one met before `k`.
  apart : ∀ {ka k q} → ka ≺ k → k ≺ q → instantOf q ≡ instantOf ka → (Rooted ka → Rooted k → Rooted q → instantOf k ≡ instantOf ka → ⊥)
        → Rooted ka → Rooted k → Rooted q → ⊥
  apart {ka} {k} {q} ak kq e no ra rk rq = no ra rk rq (between ra rk rq ak kq (sym e))

  -- Past a begin of a new name, the next value is of another instant.
  begin-fresh : ∀ xs n ys → values rx ≡ xs ++ instEmit (mark Marks.begin) n ∷ ys → n ≢ lastBegin root xs → Fresh (lastBegin root xs) (stamped ys)
  begin-fresh xs n ys e ne with around xs _ ys e
  ... | h = fresh-all (lastBegin root xs) ys λ v eq → case v eq
    where
      kb = Around.k h
      case : ∀ {a j} → instEmit (value a) j ∈ ys → lastBegin root xs ≡ j → ⊥
      case {a} {j} v eq with Around.next h v | lb-view root xs
      ... | q , y , kq | inj₁ e₀ =
        past-sub xs h (begin-late xs n ys e) v (trans (sym eq) e₀)
      ... | q , y , kq | inj₂ hb with Around.prev h hb
      ...   | ka , yb , ak =
        apart ak kq (trans (sym (named o y)) (trans (cong instantOf (sym eq)) (named o yb)))
          (λ _ _ _ eb → ne (one-name o (Around.row h) yb eb))
          (rooted o yb) (rooted o (Around.row h)) (rooted o y)

  -- Past an over, the next value is of another instant.
  over-fresh : ∀ xs n ys → values rx ≡ xs ++ instEmit (mark Marks.over) n ∷ ys → seenSub xs ≡ true → Fresh (lastBegin root xs) (stamped ys)
  over-fresh xs n ys e s with around xs _ ys e
  ... | h = fresh-all (lastBegin root xs) ys λ v eq → case v eq
    where
      ko = Around.k h
      case : ∀ {a j} → instEmit (value a) j ∈ ys → lastBegin root xs ≡ j → ⊥
      case {a} {j} v eq with Around.next h v | lb-view root xs
      ... | q , y , kq | inj₁ e₀ = past-sub xs h s v (trans (sym eq) e₀)
      ... | q , y , kq | inj₂ hb with Around.prev h hb
      ...   | ka , yb , ak =
        let eA = trans (sym (named o y)) (trans (cong instantOf (sym eq)) (named o yb)) in
        apart ak kq eA (λ _ _ _ eo → ≺-absurd {ko} {q} kq (over-last o y (Around.row h) (trans eA (sym eo))))
          (rooted o yb) (rooted o (Around.row h)) (rooted o y)

  -- Nothing past the completion.
  completed-end : ∀ xs n ys → values rx ≡ xs ++ instEmit (mark Marks.completed) n ∷ ys → stamped ys ≡ []
  completed-end xs n ys e with around xs _ ys e
  ... | h = none-stamped ys λ v → case v
    where
      case : ∀ {a j} → instEmit (value a) j ∈ ys → ⊥
      case v with Around.next h v
      ... | q , y , kq = ≺-absurd {Around.k h} {q} kq (done-last o y (Around.row h))
