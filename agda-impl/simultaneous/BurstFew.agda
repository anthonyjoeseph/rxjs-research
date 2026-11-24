{-# OPTIONS --guardedness #-}

-- THE BURST PART'S LANE HAS FINITELY MANY ROWS (`burst-few`).  Its
-- share's first lane is an `each` of nothing over the blocker, whose
-- only row is the empty's end; its second lane is empty; and its frame's
-- lanes are a one-value `of`, the share rejoined, and an empty.  Each
-- lane starts where its value arrives or at an earlier lane's end, so
-- every lane's rows lie among finitely many places, and the connects,
-- the count and the scan above them add none of their own but the first
-- children of their sources' rows.
module simultaneous.BurstFew where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; [_]; _++_; concatMap)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-map⁺; ∈-concat⁺′)
open import Data.List.Relation.Unary.All using (_∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; s≤s)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (refl)

open import Tree using (Obs; mergeᶠ)
open import denotation.Position using (Pos; ix; sub; last; root; _≟ᵖ_; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (EmissionSet; Den; DenEnv; hot; enter; out; Proper; at-out; on-out; at-end; _≺_; Few; Truncate; Rejoin; shown;
  heard; ended; late; LaneOf; MapT; map-out; module Op; module Joining; module Bounded;
  module Connecting; module Scan; module Merge)
open import denotation.Laws.Modulus using (≺-ext; ≺-trans)
open import denotation.Laws.Truth using (Finite)
open import denotation.Laws.Worlds.Leaves using (of-reach)
open import simultaneous.HeldComb using (ev)
open import simultaneous.SObs using (lone; lanePart; burstPart; module Elaborate)
open import simultaneous.InstEmit using (burstEnd)
open import simultaneous.LaneLayers using (Under; few-row; few-tr; map-few; scan-few; under-ext; under-refl; under-trans; under-⊕)
open import simultaneous.LaneStart using (module C; Sh; z₀)
open import simultaneous.ConcatTwo using (module Two; starts₀)
open import simultaneous.ConcatThree using (module Of3; o1; e1; r1)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; laneStep; marked; piece; laneSrc)

-- A connect's rows before `v`: its body's, and the first children of its
-- source's.
conn-few-src : ∀ {A B} p (σ : EmissionSet A) (β : EmissionSet B) {v} → Few σ v → Few β v → Few (Connecting.ConnT p σ β) v
conn-few-src p σ β {v} (ks , hs) (kb , hb) = kb ++ L.map (_⊕ [ ix 0 ]) ks , go
  where
    src : ∀ {k e} → σ k e → (k ⊕ [ ix 0 ]) ≺ v → (k ⊕ [ ix 0 ]) ∈ (kb ++ L.map (_⊕ [ ix 0 ]) ks)
    src {k} x lt = ∈-++⁺ʳ kb (∈-map⁺ (_⊕ [ ix 0 ]) (hs x (≺-trans {k} {k ⊕ [ ix 0 ]} {v} (≺-ext k []) lt)))

    go : ∀ {k e} → Connecting.ConnT p σ β k e → k ≺ v → k ∈ (kb ++ L.map (_⊕ [ ix 0 ]) ks)
    go (Connecting.body b) lt       = ∈-++⁺ˡ (hb b lt)
    go (Connecting.burst x _) lt    = src x lt
    go (Connecting.echo x _ _ _) lt = src x lt
    go (Connecting.kept x _ _ _) lt = src x lt

fin-few : ∀ {A} {t : EmissionSet A} → Finite t → ∀ {v} → Few t v
fin-few (ks , h) = ks , λ x _ → h x

fin-tr : ∀ {A} {t : EmissionSet A} → Finite t → Finite (Truncate t)
fin-tr (ks , h) = ks , λ x → h (proj₁ x)

-- A hot's rows, rejoined: one sub label under each, or a last child.
fin-rejoin : ∀ {A} p (t : EmissionSet A) → Finite t → Finite (Rejoin p t)
fin-rejoin p t (ks , h) = (p ⊕ [ last ]) ∷ L.map (_⊕ [ sub p ]) ks , go
  where
    go : ∀ {k e} → Rejoin p t k e → k ∈ ((p ⊕ [ last ]) ∷ L.map (_⊕ [ sub p ]) ks)
    go (shown x _ _) = there (∈-map⁺ (_⊕ [ sub p ]) (h x))
    go (heard x _)   = there (∈-map⁺ (_⊕ [ sub p ]) (h x))
    go (ended x _)   = there (∈-map⁺ (_⊕ [ sub p ]) (h x))
    go (late _ _)    = here refl

fin-empty : ∀ {A} p → Finite (enter (Op.empty {A}) p)
fin-empty p = [ p ⊕ [ last ] ] , λ { (at-end , _) → here refl }

-- A joiner's rows: its outer's, its lanes', its background's, and the
-- first child of each.
fin-join : ∀ {A B} {Lane : Pos → A → EmissionSet B} {o : EmissionSet A} {Bg : EmissionSet B} {Over Runs : Pos → Set} {Cut : Pos → Pos → Set} {Hand : Pos → Set}
         → Finite o → (Σ (List Pos) λ kl → ∀ {q a k e} → o q (out a) → Lane q a k e → k ∈ kl) → Finite Bg
         → Finite (Joining.JoinT Lane o Bg Over Runs Cut Hand)
fin-join {Lane = Lane} {o} {Bg} {Over} {Runs} {Cut} {Hand} (ko , ho) (kl , hl) (kb , hb) = Ks , go
  where
    ix₀ : Pos → Pos
    ix₀ k = k ⊕ [ ix 0 ]

    Ks : List Pos
    Ks = ko ++ (L.map ix₀ ko ++ (kl ++ (L.map ix₀ kl ++ (kb ++ L.map ix₀ kb))))

    i₂ : ∀ {k} → k ∈ L.map ix₀ ko → k ∈ Ks
    i₃ : ∀ {k} → k ∈ kl → k ∈ Ks
    i₄ : ∀ {k} → k ∈ L.map ix₀ kl → k ∈ Ks
    i₅ : ∀ {k} → k ∈ kb → k ∈ Ks
    i₆ : ∀ {k} → k ∈ L.map ix₀ kb → k ∈ Ks
    i₂ i = ∈-++⁺ʳ ko (∈-++⁺ˡ i)
    i₃ i = ∈-++⁺ʳ ko (∈-++⁺ʳ (L.map ix₀ ko) (∈-++⁺ˡ i))
    i₄ i = ∈-++⁺ʳ ko (∈-++⁺ʳ (L.map ix₀ ko) (∈-++⁺ʳ kl (∈-++⁺ˡ i)))
    i₅ i = ∈-++⁺ʳ ko (∈-++⁺ʳ (L.map ix₀ ko) (∈-++⁺ʳ kl (∈-++⁺ʳ (L.map ix₀ kl) (∈-++⁺ˡ i))))
    i₆ i = ∈-++⁺ʳ ko (∈-++⁺ʳ (L.map ix₀ ko) (∈-++⁺ʳ kl (∈-++⁺ʳ (L.map ix₀ kl) (∈-++⁺ʳ kb i))))

    go : ∀ {k e} → Joining.JoinT Lane o Bg Over Runs Cut Hand k e → k ∈ Ks
    go (Joining.val x)             = i₂ (∈-map⁺ ix₀ (ho x))
    go (Joining.step x)            = ∈-++⁺ˡ (ho x)
    go (Joining.opin x)            = ∈-++⁺ˡ (ho x)
    go (Joining.oend x _)          = ∈-++⁺ˡ (ho x)
    go (Joining.opass x _)         = ∈-++⁺ˡ (ho x)
    go (Joining.lane x _ l _ _)    = i₃ (hl x l)
    go (Joining.lend x _ l _ _ _)  = i₃ (hl x l)
    go (Joining.lpass x _ l _ _ _) = i₃ (hl x l)
    go (Joining.hand x _ l _ _)    = i₄ (∈-map⁺ ix₀ (hl x l))
    go (Joining.left x _ l _ _)    = i₃ (hl x l)
    go (Joining.run b _)           = i₅ (hb b)
    go (Joining.rend b _ _)        = i₅ (hb b)
    go (Joining.rpass b _ _)       = i₅ (hb b)
    go (Joining.rhand b _)         = i₆ (∈-map⁺ ix₀ (hb b))

-- An `each` of nothing over a finite hot: its outer's rows, and each
-- lane's end.
fin-each : ∀ {A X} (t : EmissionSet A) → Finite t → ∀ s → Finite (enter (Op.flatMap (mergeᶠ nothing) (λ _ → Op.of {X} []) (hot t)) s)
fin-each {X = X} t ft s = fin-tr (fin-join fo (L.map lend (proj₁ fo) , lanes) ([] , λ ()))
  where
    fo : Finite (enter (hot t) s)
    fo = fin-tr (fin-rejoin s t ft)

    lend : Pos → Pos
    lend q = (q ⊕ [ ix 1 ]) ⊕ [ last ]

    lanes : ∀ {q a k e} → enter (hot t) s q (out a) → LaneOf (λ _ → Op.of {X} []) q a k e → k ∈ L.map lend (proj₁ fo)
    lanes x ((at-end , _) , _) = ∈-map⁺ lend (proj₂ fo x)

module _ {Θ B Γ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ′ → X ∈ ⊤ ∷ Θ) (o : Obs Timeline Γ′ B) (ρ : DenEnv Θ) where

  -- The burst part's share and pieces, read through the elaboration.
  sh→ : ∀ m (h : Den ⊤) p {y e} → enter (ev m (Sh ρ′ o ρ burstPart) (h ∷ ρ)) p y e
      → enter (Op.flatMap (mergeᶠ (just 1)) (λ c → ev m (laneSrc ρ′ o burstPart c) (h ∷ ρ)) (Op.of (true ∷ false ∷ []))) p y e
  sh→ nothing  h p r = r
  sh→ (just _) h p r = r

  blk→ : ∀ m (h : Den ⊤) s {y e} → enter (ev m (laneSrc ρ′ o burstPart true) (h ∷ ρ)) s y e
       → enter (Op.flatMap (mergeᶠ nothing) (λ _ → Op.of {IE B} []) h) s y e
  blk→ nothing  h s r = r
  blk→ (just _) h s r = r

  emp→ : ∀ m (h : Den ⊤) s {y e} → enter (ev m (laneSrc ρ′ o burstPart false) (h ∷ ρ)) s y e → enter (Op.empty {IE B}) s y e
  emp→ nothing  h s r = r
  emp→ (just _) h s r = r

  pb0→ : ∀ m (h : Den ⊤) (h′ : Den (IE B)) s {y e} → enter (ev m (piece {B = B} burstPart 0) (h′ ∷ h ∷ ρ)) s y e → enter (Op.of (marked burstEnd ∷ [])) s y e
  pb0→ nothing  h h′ s r = r
  pb0→ (just _) h h′ s r = r

  pb1→ : ∀ m (h : Den ⊤) (h′ : Den (IE B)) s {y e} → enter (ev m (piece {B = B} burstPart 1) (h′ ∷ h ∷ ρ)) s y e → enter h′ s y e
  pb1→ nothing  h h′ s r = r
  pb1→ (just _) h h′ s r = r

  pb2→ : ∀ m (h : Den ⊤) (h′ : Den (IE B)) s {y e} → enter (ev m (piece {B = B} burstPart 2) (h′ ∷ h ∷ ρ)) s y e → enter (Op.empty {IE B}) s y e
  pb2→ nothing  h h′ s r = r
  pb2→ (just _) h h′ s r = r

  pcb : ∀ m (h : Den ⊤) (h′ : Den (IE B)) s → enter (ev m (piece {B = B} burstPart 0) (h′ ∷ h ∷ ρ)) s (s ⊕ [ ix 0 ]) (out (marked burstEnd))
  pcb nothing  h h′ s = at-out , of-reach s 0 (marked burstEnd ∷ []) {s ⊕ [ ix 0 ]} {out (marked burstEnd)}
  pcb (just _) h h′ s = at-out , of-reach s 0 (marked burstEnd ∷ []) {s ⊕ [ ix 0 ]} {out (marked burstEnd)}

  module _ (m : Maybe ℕ) where
    open C ρ′ o ρ m using (Sv; Ct; Sc; Fr; H₁; H₂; Bp; module Frame)

    -- The burst part's share, over a finite hot: its blocker's rows, and
    -- the empty's end wherever it starts.
    module ShareFin (t : EmissionSet ⊤) (ft : Finite t) (Qs : Pos) where
      gb : Bool → Den (IE B)
      gb c = ev m (laneSrc ρ′ o burstPart c) (hot t ∷ ρ)

      O2 : EmissionSet Bool
      O2 = enter (Op.of (true ∷ false ∷ [])) Qs

      module T2 = Two gb O2 Qs true false (λ x → x) (λ x → x)
      open Bounded 1 gb O2 using (Starts; Ends; Sched; Lane; JoinT; room; freed; queued)

      S₀ : Pos
      S₀ = T2.q₀ ⊕ [ ix 1 ]

      FE = fin-each {X = IE B} t ft S₀

      fb0 : Finite (enter (gb true) S₀)
      fb0 = proj₁ FE , λ x → proj₂ FE (blk→ m (hot t) S₀ x)

      ends-in : ∀ {c} → Ends 0 [] c → c ∈ proj₁ fb0
      ends-in ec = proj₂ fb0 (proj₁ (T2.end-of ec))

      lend : Pos → Pos
      lend c = (c ⊕ [ ix 1 ]) ⊕ [ last ]

      kl : List Pos
      kl = proj₁ fb0 ++ (lend T2.q₁ ∷ L.map lend (proj₁ fb0))

      lane1 : ∀ {s y e} → Starts 1 T2.q₁ (Sched 1) s → enter (gb false) s y e → y ∈ kl
      lane1 (room (s≤s ())) _
      lane1 (freed _ _) r with emp→ m (hot t) _ r
      ... | (at-end , _) = ∈-++⁺ʳ (proj₁ fb0) (here refl)
      lane1 (queued _ _ (inj₁ (_ , ec , refl)) _ _) r with emp→ m (hot t) _ r
      ... | (at-end , _) = ∈-++⁺ʳ (proj₁ fb0) (there (∈-map⁺ lend (ends-in ec)))
      lane1 (queued _ _ (inj₂ ()) _ _) _

      lanes : ∀ {q a y e} → Lane q a y e → y ∈ kl
      lanes (_ , _ , (n , st) , (r , _)) with T2.nth-c n
      ... | T2.n₀ with starts₀ st
      ...   | refl = ∈-++⁺ˡ (proj₂ fb0 r)
      lanes (_ , _ , (n , st) , (r , _)) | T2.n₁ = lane1 st r

      fo : Finite O2
      fo = T2.q₀ ∷ T2.q₁ ∷ T2.qL ∷ [] , go
        where
          go : ∀ {k e} → O2 k e → k ∈ (T2.q₀ ∷ T2.q₁ ∷ T2.qL ∷ [])
          go x with T2.o-row x
          ... | T2.r₀ = here refl
          ... | T2.r₁ = there (here refl)
          ... | T2.rL = there (there (here refl))

      fin-sh : Finite (enter (ev m (Sh ρ′ o ρ burstPart) (hot t ∷ ρ)) Qs)
      fin-sh = proj₁ F , λ x → proj₂ F (sh→ m (hot t) Qs x)
        where F = fin-tr (fin-join fo (kl , λ _ l → lanes l) ([] , λ ()))

    -- The burst part's frame: its first lane's mark and end, its second's
    -- rejoined rows wherever it starts, and its third's end wherever it
    -- starts.
    module FrameFin (h₁ : Den ⊤) (h₂ : Den (IE B)) (KS : List Pos)
                    (fh : ∀ {s y e} → enter h₂ s y e → y ∈ ((s ⊕ [ last ]) ∷ L.map (_⊕ [ sub s ]) KS)) (F : Pos) where
      fb : ℕ → Den (IE B)
      fb j = ev m (piece {B = B} burstPart j) (h₂ ∷ h₁ ∷ ρ)

      open Of3 F using (O; q₀; q₁; q₂; qL; nth-c; n₀; n₁; n₂; ofin)
      open Bounded 1 fb O using (Starts; Ends; Sched; Lane; JoinT; room; freed; queued)

      S₀ : Pos
      S₀ = q₀ ⊕ [ ix 1 ]

      L0 : List Pos
      L0 = (S₀ ⊕ [ ix 0 ]) ∷ (S₀ ⊕ [ last ]) ∷ []

      RL : Pos → List Pos
      RL s = (s ⊕ [ last ]) ∷ L.map (_⊕ [ sub s ]) KS

      St1 : List Pos
      St1 = (q₁ ⊕ [ ix 1 ]) ∷ L.map (_⊕ [ ix 1 ]) L0

      L1 : List Pos
      L1 = concatMap RL St1

      St2 : List Pos
      St2 = (q₂ ⊕ [ ix 1 ]) ∷ L.map (_⊕ [ ix 1 ]) (L1 ++ L0)

      L2 : List Pos
      L2 = L.map (_⊕ [ last ]) St2

      lane0 : ∀ {s y e} → Starts 0 q₀ [] s → enter (fb 0) s y e → y ∈ L0
      lane0 st r with starts₀ st
      ... | refl with r1 (marked burstEnd) S₀ (pb0→ m h₁ h₂ S₀ r)
      ...   | o1 = here refl
      ...   | e1 = there (here refl)

      end0-in : ∀ {c} → Ends 0 [] c → c ∈ L0
      end0-in (_ , _ , _ , n , st , (r , _)) with nth-c n
      ... | n₀ = lane0 st r

      st1-in : ∀ {s} → Starts 1 q₁ (Sched 1) s → s ∈ St1
      st1-in (room (s≤s ()))
      st1-in (freed _ _) = here refl
      st1-in (queued _ _ (inj₁ (_ , ec , refl)) _ _) = there (∈-map⁺ (_⊕ [ ix 1 ]) (end0-in ec))
      st1-in (queued _ _ (inj₂ ()) _ _)

      lane1 : ∀ {s y e} → Starts 1 q₁ (Sched 1) s → enter (fb 1) s y e → y ∈ L1
      lane1 {s} st r = ∈-concat⁺′ (fh (pb1→ m h₁ h₂ s r)) (∈-map⁺ RL (st1-in st))

      end1-in : ∀ {c} → Ends 1 (Sched 1) c → c ∈ L1
      end1-in (_ , _ , _ , n , st , (r , _)) with nth-c n
      ... | n₁ = lane1 st r

      st2-in : ∀ {s} → Starts 2 q₂ (Sched 2) s → s ∈ St2
      st2-in (room (s≤s ()))
      st2-in (freed _ _) = here refl
      st2-in (queued _ _ (inj₁ (_ , ec , refl)) _ _)        = there (∈-map⁺ (_⊕ [ ix 1 ]) (∈-++⁺ˡ (end1-in ec)))
      st2-in (queued _ _ (inj₂ (inj₁ (_ , ec , refl))) _ _) = there (∈-map⁺ (_⊕ [ ix 1 ]) (∈-++⁺ʳ L1 (end0-in ec)))
      st2-in (queued _ _ (inj₂ (inj₂ ())) _ _)

      lane2 : ∀ {s y e} → Starts 2 q₂ (Sched 2) s → enter (fb 2) s y e → y ∈ L2
      lane2 {s} st r with pb2→ m h₁ h₂ s r
      ... | (at-end , _) = ∈-map⁺ (_⊕ [ last ]) (st2-in st)

      kl : List Pos
      kl = L0 ++ (L1 ++ L2)

      lanes : ∀ {q a y e} → Lane q a y e → y ∈ kl
      lanes (_ , _ , (n , st) , (r , _)) with nth-c n
      ... | n₀ = ∈-++⁺ˡ (lane0 st r)
      ... | n₁ = ∈-++⁺ʳ L0 (∈-++⁺ˡ (lane1 st r))
      ... | n₂ = ∈-++⁺ʳ L0 (∈-++⁺ʳ L1 (lane2 st r))

      fin : Finite JoinT
      fin = fin-join (q₀ ∷ q₁ ∷ q₂ ∷ qL ∷ [] , ofin) (kl , λ _ l → lanes l) ([] , λ ())

    -- The burst part's lane at `s`, its layers' rows few before anywhere.
    module BurstAt (s : Pos) where
      R R′ : Pos
      R = (s ⊕ [ ix 1 ]) ⊕ [ ix 1 ]
      R′ = R ⊕ [ ix 0 ]

      h₁ = H₁ R
      h₂ = H₂ R burstPart

      Pe : Finite (Proper (enter (Op.empty {⊤}) (R ⊕ [ ix 1 ])))
      Pe = [ (R ⊕ [ ix 1 ]) ⊕ [ last ] ] , λ { ((at-end , _) , _) → here refl }

      module SF = ShareFin (Proper (enter (Op.empty {⊤}) (R ⊕ [ ix 1 ]))) Pe (R′ ⊕ [ ix 1 ])

      SHb : EmissionSet (IE B)
      SHb = enter (ev m (Sh ρ′ o ρ burstPart) (h₁ ∷ ρ)) (R′ ⊕ [ ix 1 ])

      fP : Finite (Proper SHb)
      fP = proj₁ SF.fin-sh , λ x → proj₂ SF.fin-sh (proj₁ x)

      module FF = FrameFin h₁ h₂ (proj₁ fP) (λ {s′} x → proj₂ (fin-rejoin s′ (Proper SHb) fP) (proj₁ x)) (Bp R)

      FrbE : EmissionSet (IE B)
      FrbE = enter (Fr burstPart h₁ h₂) (Bp R)

      ScE = enter (Sc burstPart h₁ h₂) (Bp R)

      scf : ∀ v → Few (Scan.ScanT laneStep z₀ FrbE) v
      scf v = scan-few laneStep z₀ FrbE (fin-few (fin-tr FF.fin))

      ctf : ∀ v → Few (MapT proj₂ ScE) v
      ctf v = map-few proj₂ ScE (few-tr (scf v))

      inf : ∀ v → Few (Connecting.ConnT R′ SHb (enter (Ct burstPart h₁ h₂) (Bp R))) v
      inf v = conn-few-src R′ SHb (enter (Ct burstPart h₁ h₂) (Bp R)) (fin-few SF.fin-sh) (few-tr (ctf v))

      svf : ∀ v → Few (Connecting.ConnT R (enter (Op.empty {⊤}) (R ⊕ [ ix 1 ])) (enter (Op.connect (ev m (Sh ρ′ o ρ burstPart) (h₁ ∷ ρ)) (λ h′ → Ct burstPart h₁ h′)) R′)) v
      svf v = conn-few-src R (enter (Op.empty {⊤}) (R ⊕ [ ix 1 ])) (enter (Op.connect (ev m (Sh ρ′ o ρ burstPart) (h₁ ∷ ρ)) (λ h′ → Ct burstPart h₁ h′)) R′)
                (fin-few (fin-empty {⊤} (R ⊕ [ ix 1 ]))) (few-tr (inf v))

      -- The frame's first piece's mark, its `burstEnd`, a row of every
      -- layer up to the parts' merge.
      open Frame burstPart h₁ h₂ (Bp R) using (V₀; u-V₀; ob₀; nth₀; S₀; sb₀; fr-min) renaming (module Bd to FB)

      be : IE B
      be = marked burstEnd

      Eb : Pos
      Eb = V₀

      fr-row : FB.JoinT V₀ (out be)
      fr-row = Joining.lane ob₀ (0 , 0 , nth₀) (0 , S₀ , sb₀ , (pcb m h₁ h₂ S₀ , ≺-ext S₀ [])) (λ ()) tt

      sc-row : ScE V₀ (out (laneStep z₀ be))
      sc-row = few-row (Scan.sval (Scan.acc₀ (few-row fr-row (fin-few FF.fin)) fr-min)) (scf V₀)

      sv-row : enter (Sv burstPart) R Eb (out be)
      sv-row = few-row (Connecting.body (few-row (Connecting.body (few-row (map-out sc-row) (ctf V₀))) (inf V₀))) (svf V₀)

      u-R′ : Under R′ V₀
      u-R′ = under-trans (under-⊕ (under-⊕ (under-refl R′) (ix 0)) (ix 0)) u-V₀

      u-R : Under R V₀
      u-R = under-trans (under-⊕ (under-refl R) (ix 0)) u-R′

      -- It lies below the burst part's subscription.
      u-s : Under (s ⊕ [ ix 1 ]) Eb
      u-s = under-trans (under-⊕ (under-refl (s ⊕ [ ix 1 ])) (ix 1)) u-R

      mm-row : Merge.JoinT Sv (enter (Op.of (lanePart ∷ burstPart ∷ [])) s) Eb (out be)
      mm-row = Joining.lane (on-out at-out , of-reach s 0 (lanePart ∷ burstPart ∷ []) {s ⊕ [ ix 1 ]} {out burstPart}) tt
                 (sv-row , under-ext R u-R′) (λ ()) tt

    -- Where the burst part's lane shows its `burstEnd`.
    burstAt : Pos → Pos
    burstAt s = BurstAt.Eb s

    -- THE BURST PART'S LANE HAS FEW ROWS BEFORE ANYWHERE.
    burst-few : ∀ s v → Few (enter (Sv burstPart) ((s ⊕ [ ix 1 ]) ⊕ [ ix 1 ])) v
    burst-few s v = few-tr (BurstAt.svf s v)
